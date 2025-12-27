# LeanYjs Technical Documentation

This document provides an in-depth technical explanation of the LeanYjs formalization, complementing the high-level overview in the README.

## Table of Contents

1. [Data Structures](#data-structures)
2. [Integrate Implementation](#integrate-implementation)
3. [Ordering Relations](#ordering-relations)
4. [ItemSet Invariants](#itemset-invariants)
5. [Total Order Proofs](#total-order-proofs)
6. [Integrate Correctness](#integrate-correctness)
7. [Network Model and Convergence](#network-model-and-convergence)

## Data Structures

The core data structures in LeanYjs are defined in `LeanYjs/Item.lean`.

```lean
structure YjsId where
  clientId : ClientId
  clock : Nat

mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr

inductive YjsItem : Type where
| item (origin : YjsPtr) (rightOrigin : YjsPtr) : YjsId -> A -> YjsItem
end
```

`YjsId` orders events primarily by `clientId` and secondarily by a descending `clock` (local Lamport clock), matching the Yjs tie-breaking rule. `YjsPtr.first/last` are sentinels that bound the editable sequence.

Helper accessors:

```lean
def YjsItem.origin {A} : YjsItem A -> YjsPtr A
def YjsItem.rightOrigin {A} : YjsItem A -> YjsPtr A
def YjsItem.id {A} : YjsItem A -> YjsId
```

## Integrate Implementation

The executable algorithm lives in `LeanYjs/Algorithm/Integrate.lean` and follows the reference CRDT implementation.

```lean
def findIntegratedIndex (leftIdx rightIdx : Int) (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError Nat := do
  let mut scanning := false
  let mut destIdx := leftIdx + 1
  for offset in [1:(rightIdx-leftIdx).toNat] do
    let i := (leftIdx + offset).toNat
    let other <- getElemExcept arr i
    let oLeftIdx <- findPtrIdx other.origin arr
    let oRightIdx <- findPtrIdx other.rightOrigin arr
    if oLeftIdx < leftIdx then
      break
    else if oLeftIdx == leftIdx then
      if newItem.id.clientId > other.id.clientId then
        scanning := false
      else if oRightIdx == rightIdx then
        break
      else
        scanning := true
    if !scanning then destIdx := i + 1
  return (Int.toNat destIdx)

def integrate (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findPtrIdx (YjsItem.origin newItem) arr
  let rightIdx <- findPtrIdx (YjsItem.rightOrigin newItem) arr
  let destIdx <- findIntegratedIndex leftIdx rightIdx newItem arr
  return (arr.insertIdxIfInBounds (Int.toNat destIdx) newItem)

def integrateSafe (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  if isClockSafe newItem arr then integrate newItem arr else Except.error IntegrateError.error
```

### Algorithm Logic

1. **Find boundaries**: Locate the indices of `origin` and `rightOrigin` in the array
2. **Scan between boundaries**: Examine each item between the insertion boundaries
3. **Conflict resolution**:
   - If `oLeftIdx < leftIdx`: Current item should come before newItem (break)
   - If `oLeftIdx == leftIdx`: Items share an origin; prefer smaller `clientId`, breaking ties with `rightOrigin`
   - If `oRightIdx == rightIdx`: Items have same rightOrigin, determines final position
4. **Position tracking**: `destIdx` tracks where to insert, `scanning` controls when to advance it
5. **Clock safety**: `integrateSafe` enforces per-client clock monotonicity to rule out duplicate IDs

The algorithm ensures that the resulting array maintains the total order defined by the ordering relations.

## Ordering Relations

The ordering relations are defined in `LeanYjs/Order/ItemOrder.lean`. They establish a total order over `YjsPtr` elements once paired with the invariants below.

### OriginLt

```lean
inductive OriginLt {A} : YjsPtr A -> YjsPtr A -> Prop where
  | lt_first : forall item, OriginLt YjsPtr.first (YjsPtr.itemPtr item)
  | lt_last : forall item, OriginLt (YjsPtr.itemPtr item) YjsPtr.last
  | lt_first_last : OriginLt YjsPtr.first YjsPtr.last
```

This defines the basic ordering between boundary elements and items. Intuitively:

- `first` comes before any item
- Any item comes before `last`
- `first` comes before `last`
- Transitivity/comparability for arbitrary items is supplied by the mutually defined relations below.

### YjsLt, ConflictLt, and YjsLeq

The core ordering relations are mutually defined and no longer carry an explicit `ItemSet` parameter (the invariants supply well-formedness separately):

```lean
mutual
  inductive YjsLt {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltConflict h i1 i2 : ConflictLt h i1 i2 -> YjsLt (h + 1) i1 i2
    | ltOriginOrder i1 i2 : OriginLt i1 i2 -> YjsLt 0 i1 i2
    | ltOrigin h x o r id c : YjsLeq h x o -> YjsLt (h + 1) x (YjsItem.mk o r id c)
    | ltRightOrigin h o r id c x : YjsLeq h r x -> YjsLt (h + 1) (YjsItem.mk o r id c) x

  inductive YjsLeq {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | leqSame x : YjsLeq h x x
    | leqLt h x y : YjsLt h x y -> YjsLeq (h + 1) x y

  inductive ConflictLt {A : Type} : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 :
      YjsLt h1 l2 l1
      -> YjsLt h2 (YjsItem.mk l1 r1 id1 c1) r2
      -> YjsLt h3 l1 (YjsItem.mk l2 r2 id2 c2)
      -> YjsLt h4 (YjsItem.mk l2 r2 id2 c2) r1
      -> ConflictLt (max4 h1 h2 h3 h4 + 1) (YjsItem.mk l1 r1 id1 c1) (YjsItem.mk l2 r2 id2 c2)
    | ltOriginSame h1 h2 l r1 r2 id1 id2 (c1 c2 : A) :
      YjsLt h1 (YjsItem.mk l r1 id1 c1) r2
      -> YjsLt h2 (YjsItem.mk l r2 id2 c2) r1
      -> id1 < id2
      -> ConflictLt (max h1 h2 + 1) (YjsItem.mk l r1 id1 c1) (YjsItem.mk l r2 id2 c2)
end
```

These definitions capture the intuitive ordering rules:

1. **ltOriginOrder**: Direct ordering from `OriginLt` for boundary cases
2. **ltOrigin**: `x < item` if `x ≤ item.origin`
3. **ltRightOrigin**: `item < x` if `item.rightOrigin ≤ x`
4. **ltConflict**: Handle conflicts between items with complex positioning rules

The conflict resolution rules ensure that when two items have overlapping insertion positions, they are ordered deterministically based on their origins and actor IDs.

`YjsLt'`/`YjsLeq'` abbreviations existentially quantify the height parameter, hiding proof bookkeeping when reasoning in tactics.

## ItemSet Invariants

`ItemSet` is a predicate over `YjsPtr` (`LeanYjs/ItemSet.lean`). `LeanYjs/Order/ItemSetInvariant.lean` packages the structural requirements used to rule out pathological graphs.

### ItemSet Definition

```lean
def ItemSet := Set (YjsPtr A)

structure IsClosedItemSet {A} (P : YjsPtr A -> Prop) : Prop where
  baseFirst : P YjsPtr.first
  baseLast : P YjsPtr.last
  closedLeft : (∀ (o : YjsPtr A) r id c, P (YjsItem.mk o r id c) -> P o)
  closedRight : (∀ o (r : YjsPtr A) id c, P (YjsItem.mk o r id c) -> P r)
```

### ItemSetInvariant

```lean
structure ItemSetInvariant where
  origin_not_leq : ∀ (o r : YjsPtr A) c id, P (YjsItem.mk o r id c) ->
    YjsLt' o r
  origin_nearest_reachable : ∀ (o r : YjsPtr A) c id x,
    P (YjsItem.mk o r id c) ->
    OriginReachable (A := A) (YjsItem.mk o r id c) x ->
    (YjsLeq' x o) ∨ (YjsLeq' r x)
  id_unique : ∀ (x y : YjsItem A), x.id = y.id -> P x -> P y -> x = y
```

These invariants are crucial because **without them, the ordering would not be a total order**. For example:

- Without `origin_not_leq`: An item could have `origin = rightOrigin`, violating asymmetry
- Without `origin_nearest_reachable`: Reachability along origins could skip over nearer elements, breaking comparability
- Without `id_unique`: Two equal IDs could form incomparable duplicates

The invariants eliminate pathological cases that would break the mathematical properties needed for a total order.

## Total Order Proofs

The proofs that the ordering relations form a total order are split across three files under `LeanYjs/Order/`.

### Totality (`LeanYjs/Order/Totality.lean`)

```lean
theorem yjs_lt_total {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y : YjsPtr A), P x -> P y ->
    (∃ h, @YjsLeq A P h x y) ∨ (∃ h, @YjsLt A P h y x)
```

Proves that for any two elements `x` and `y` in a valid ItemSet, either `x ≤ y` or `y < x`.

### Transitivity (`LeanYjs/Order/Transitivity.lean`)

```lean
theorem yjs_lt_trans {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y z : YjsPtr A), P x -> P y -> P z ->
  YjsLt' P x y -> YjsLt' P y z -> YjsLt' P x z
```

Proves that if `x < y` and `y < z`, then `x < z`.

### Asymmetry (`LeanYjs/Order/Asymmetry.lean`)

```lean
theorem yjs_lt_asymm {A} [DecidableEq A] {P : ItemSet A} :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), YjsLt' P x y -> YjsLt' P y x -> False
```

Proves that if `x < y`, then `¬(y < x)`, establishing asymmetry.

These three properties together establish that the ordering is a strict total order.

## Integrate Correctness

The main correctness results are in `LeanYjs/Algorithm/IntegrateSpec.lean` and `LeanYjs/Algorithm/IntegrateCommutative.lean`.

### Main Theorem

```lean
theorem YjsArrInvariant_integrate (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  → newItem.isValid
  -> UniqueId newItem arr
  -> integrate newItem arr = Except.ok newArr
  -> ∃ i ≤ arr.size, newArr = arr.insertIdxIfInBounds i newItem ∧ YjsArrInvariant newArr.toList
```

This theorem states that if:

1. The input array satisfies the Yjs array invariants
2. The new item satisfies the insertion preconditions (`isValid` plus `UniqueId`, which encapsulates `InsertOk`)
3. The integrate function succeeds

Then the result is equivalent to inserting the item at some valid position that preserves all invariants.

### Loop Invariant

The proof uses a complex loop invariant (`loopInv`) in `IntegrateSpec.lean` that tracks:

```lean
def loopInv (arr : Array (YjsItem A)) (newItem : YjsItem A) (leftIdx : ℤ) (rightIdx : ℤ) (x : Option ℕ) (state : ForInStep (MProd ℤ Bool)) :=
  let current := offsetToIndex leftIdx rightIdx x (isBreak state)
  let ⟨ dest, scanning ⟩ := state.value
  let done := isDone state x
  -- Properties that must hold at each iteration:
  (match x with
    | none => True
    | some x => 0 < x ∧ x < rightIdx - leftIdx) ∧
  (dest ≤ current) ∧
  (!scanning → !done -> dest = current) ∧
  let dest := dest.toNat;
  (∀ i : ℕ, i < dest -> (h_i_lt : i < arr.size)-> YjsLt' (ArrSet $ newItem :: arr.toList) arr[i] newItem) ∧
  (∀ i, (h_dest_i : dest ≤ i) -> (h_i_c : i < current) ->
    ∃ (i_lt_size : i < arr.size) (h_dest_lt : dest < arr.size),
      (arr[i].origin = newItem.origin ∧ newItem.id < arr[i].id ∨
        YjsLeq' (ArrSet $ newItem :: arr.toList) arr[dest] arr[i].origin)) ∧
  (scanning -> ∃ h_dest_lt : dest < arr.size, arr[dest].origin = newItem.origin) ∧
  (done -> ∀item : YjsPtr A, extGetElemExcept arr current = Except.ok item -> YjsLt' (ArrSet $ newItem :: arr.toList) newItem item)
```

This invariant ensures that:

1. All items before `dest` are ordered before `newItem`
2. All items in the "to be determined" region have specific ordering properties
3. When scanning mode is active, we're looking at items with the same origin
4. When the loop is done, `newItem` should be ordered before the item at the current position

### Commutativity

`LeanYjs/Algorithm/IntegrateCommutative.lean` proves that integration is commutative when items are unique and not in each other's origin chain:

```lean
theorem integrate_commutative (a b : YjsItem A) (arr1 : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> a.id.clientId ≠ b.id.clientId
  → ¬OriginReachable a (YjsPtr.itemPtr b)
  → ¬OriginReachable b (YjsPtr.itemPtr a)
  → a.isValid
  → b.isValid
  -> (do
    let arr2 <- integrateSafe a arr1;
    integrateSafe b arr2) =
  (do
    let arr2' <- integrateSafe b arr1;
    integrateSafe a arr2')
```

This shows that the order in which operations are integrated doesn't affect the final result, which is crucial for CRDTs.

## Network Model and Convergence

`LeanYjs/Network` provides a causal delivery model and an instantiation for Yjs operations.

- `LeanYjs/Network/CausalNetwork.lean` defines histories of `Event.Broadcast/Deliver`, a happens-before relation, and assumes causal delivery plus per-node local ordering of broadcasts.
- `LeanYjs/Network/OperationNetwork.lean` lifts an `Operation` (state, effect, error) into the network, requiring that nodes broadcast only valid messages.
- `LeanYjs/Network/YjsNetwork.lean` instantiates the model with `YjsValidItem` and `YjsArray`, tying `histories` back to `UniqueId`/`isValid`.

The central convergence statement is:

```lean
theorem YjsOperationNetwork_converge' :
  ∀ {A} [DecidableEq A] (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : YjsArray A),
    interpDeliveredOps (network.toDeliverMessages i) = Except.ok res₀ →
    interpDeliveredOps (network.toDeliverMessages j) = Except.ok res₁ →
    (∀ item, item ∈ network.toDeliverMessages i ↔ item ∈ network.toDeliverMessages j) →
    res₀ = res₁
```

Under the causal network assumptions and the commutativity proof above, any two replicas that deliver the same set of operations compute identical array states—establishing convergence (strong eventual consistency) for `integrate` on this network model.
