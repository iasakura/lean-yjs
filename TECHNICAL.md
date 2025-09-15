# LeanYjs Technical Documentation

This document provides an in-depth technical explanation of the LeanYjs formalization, complementing the high-level overview in the README.

## Table of Contents

1. [Data Structures](#data-structures)
2. [Integrate Implementation](#integrate-implementation)
3. [Ordering Relations](#ordering-relations)
4. [ItemSet Invariants](#itemset-invariants)
5. [Total Order Proofs](#total-order-proofs)
6. [Integrate Correctness](#integrate-correctness)

## Data Structures

The core data structures in LeanYjs are defined in [`LeanYjs/Item.lean`](LeanYjs/Item.lean).

### YjsPtr and YjsItem

```lean
mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr

inductive YjsItem : Type where
| item (origin : YjsPtr) (rightOrigin : YjsPtr) : ClientId -> A -> YjsItem
end
```

- **YjsPtr**: Represents pointers in the Yjs structure. Can point to actual items (`itemPtr`), or special boundary markers (`first`, `last`)
- **YjsItem**: Represents actual content items with:
  - `origin`: Pointer to the item this was inserted after
  - `rightOrigin`: Pointer to the item this was inserted before
  - `ClientId`: Unique identifier for the actor/client that created this item
  - `A`: The actual content/data of the item

The `first` and `last` pointers serve as sentinel values representing the beginning and end of the document structure.

## Integrate Implementation

The integrate algorithm is implemented in [`LeanYjs/Integrate.lean`](LeanYjs/Integrate.lean). This implementation is a port of the reference implementation from [josephg/reference-crdts](https://github.com/josephg/reference-crdts/blob/c539474087701c778c52b2974019f07c5bce8e23/crdts.ts#L405).

The original Yjs implementation uses a doubly-linked list structure, which makes formal verification significantly more challenging due to the complex pointer manipulations and mutation required. By using an array-based representation, we can focus on the algorithmic correctness without getting bogged down in low-level memory management details.

```lean
def integrate (newItem : YjsItem A) (arr : Array (YjsItem A)) : Except IntegrateError (Array (YjsItem A)) := do
  let leftIdx <- findPtrIdx (YjsItem.origin newItem) arr
  let rightIdx <- findPtrIdx (YjsItem.rightOrigin newItem) arr

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
      if newItem.id > other.id then
        scanning := false
      else if oRightIdx == rightIdx then
        break
      else
        scanning := true

    if !scanning then
      destIdx := i + 1

  return (Array.insertIdxIfInBounds arr (Int.toNat destIdx) newItem)
```

### Algorithm Logic

1. **Find boundaries**: Locate the indices of `origin` and `rightOrigin` in the array
2. **Scan between boundaries**: Examine each item between the insertion boundaries
3. **Conflict resolution**:
   - If `oLeftIdx < leftIdx`: Current item should come before newItem (break)
   - If `oLeftIdx == leftIdx`: Items have same origin, use actor ID for ordering
   - If `oRightIdx == rightIdx`: Items have same rightOrigin, determines final position
4. **Position tracking**: `destIdx` tracks where to insert, `scanning` controls when to advance it

The algorithm ensures that the resulting array maintains the total order defined by the ordering relations.

## Ordering Relations

The ordering relations are defined in [`LeanYjs/ItemOrder.lean`](LeanYjs/ItemOrder.lean). These relations establish a total order over YjsPtr elements.

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

### YjsLt, ConflictLt, and YjsLeq

The core ordering relations are mutually defined:

```lean
mutual
  inductive YjsLt {A : Type} (P : ItemSet A) : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltConflict h i1 i2 : ConflictLt P h i1 i2 -> YjsLt P (h + 1) i1 i2
    | ltOriginOrder i1 i2 : P i1 -> P i2 -> OriginLt i1 i2 -> YjsLt P 0 i1 i2
    | ltOrigin h x o r id c : P (YjsItem.item o r id c) -> YjsLeq P h x o -> YjsLt P (h + 1) x (YjsItem.item o r id c)
    | ltRightOrigin h o r id c x : P (YjsItem.item o r id c) -> YjsLeq P h r x -> YjsLt P (h + 1) (YjsItem.item o r id c) x

  inductive ConflictLt {A : Type} (P : ItemSet A) : Nat -> YjsPtr A -> YjsPtr A -> Prop where
    | ltOriginDiff h1 h2 h3 h4 l1 l2 r1 r2 id1 id2 c1 c2 :
      YjsLt P h1 l2 l1
      -> YjsLt P h2 (YjsItem.item l1 r1 id1 c1) r2
      -> YjsLt P h3 l1 (YjsItem.item l2 r2 id2 c2)
      -> YjsLt P h4 (YjsItem.item l2 r2 id2 c2) r1
      -> ConflictLt P (max4 h1 h2 h3 h4 + 1) (YjsItem.item l1 r1 id1 c1) (YjsItem.item l2 r2 id2 c2)
    | ltOriginSame h1 h2 l r1 r2 id1 id2 (c1 c2 : A) :
      YjsLt P h1 (YjsItem.item l r1 id1 c1) r2
      -> YjsLt P h2 (YjsItem.item l r2 id2 c2) r1
      -> id1 < id2
      -> ConflictLt P (max h1 h2 + 1) (YjsItem.item l r1 id1 c1) (YjsItem.item l r2 id2 c2)
end
```

These definitions capture the intuitive ordering rules:

1. **ltOriginOrder**: Direct ordering from `OriginLt` for boundary cases
2. **ltOrigin**: `x < item` if `x ≤ item.origin`
3. **ltRightOrigin**: `item < x` if `item.rightOrigin ≤ x`
4. **ltConflict**: Handle conflicts between items with complex positioning rules

The conflict resolution rules ensure that when two items have overlapping insertion positions, they are ordered deterministically based on their origins and actor IDs.

**Key insight**: These rules only cover intuitively obvious cases. The complexity comes from handling concurrent insertions where multiple items claim to be inserted at the same position.

## ItemSet Invariants

The file [`LeanYjs/ItemSet.lean`](LeanYjs/ItemSet.lean) defines `ItemSet` as a set of YjsPtr, and [`LeanYjs/ItemSetInvariant.lean`](LeanYjs/ItemSetInvariant.lean) defines the invariants that valid item sets must satisfy.

### ItemSet Definition

```lean
def ItemSet := Set (YjsPtr A)

structure IsClosedItemSet {A} (P : YjsPtr A -> Prop) : Prop where
  baseFirst : P YjsPtr.first
  baseLast : P YjsPtr.last
  closedLeft : (∀ (o : YjsPtr A) r id c, P (YjsItem.item o r id c) -> P o)
  closedRight : (∀ o (r : YjsPtr A) id c, P (YjsItem.item o r id c) -> P r)
```

### ItemSetInvariant

```lean
structure ItemSetInvariant where
  origin_not_leq : ∀ (o r c id), P (YjsItem.item o r id c) ->
    YjsLt' P o r
  origin_nearest_reachable : ∀ (o r c id x),
    P (YjsItem.item o r id c) ->
    OriginReachable (YjsItem.item o r id c) x ->
    (YjsLeq' P x o) ∨ (YjsLeq' P r x)
  same_id_ordered : ∀ (x y : YjsItem A),
    P x -> P y ->
    x ≠ y ->
    x.id = y.id ->
    YjsLeq' P x y.origin ∨
    YjsLeq' P y x.origin ∨
    YjsLeq' P x.rightOrigin y ∨
    YjsLeq' P y.rightOrigin x
```

These invariants are crucial because **without them, the ordering would not be a total order**. For example:

- Without `origin_not_leq`: An item could have `origin = rightOrigin`, violating asymmetry
- Without `same_id_ordered`: Two items with the same ID could be incomparable, violating totality

The invariants eliminate pathological cases that would break the mathematical properties needed for a total order.

## Total Order Proofs

The proofs that the ordering relations form a total order are split across three files:

### Totality ([`LeanYjs/Totality.lean`](LeanYjs/Totality.lean))

```lean
theorem yjs_lt_total {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y : YjsPtr A), P x -> P y ->
    (∃ h, @YjsLeq A P h x y) ∨ (∃ h, @YjsLt A P h y x)
```

Proves that for any two elements `x` and `y` in a valid ItemSet, either `x ≤ y` or `y < x`.

### Transitivity ([`LeanYjs/Transitivity.lean`](LeanYjs/Transitivity.lean))

```lean
theorem yjs_lt_trans {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y z : YjsPtr A), P x -> P y -> P z ->
  YjsLt' P x y -> YjsLt' P y z -> YjsLt' P x z
```

Proves that if `x < y` and `y < z`, then `x < z`.

### Asymmetry ([`LeanYjs/Asymmetry.lean`](LeanYjs/Asymmetry.lean))

```lean
theorem yjs_lt_asymm {A} [DecidableEq A] {P : ItemSet A} :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), YjsLt' P x y -> YjsLt' P y x -> False
```

Proves that if `x < y`, then `¬(y < x)`, establishing asymmetry.

These three properties together establish that the ordering is a strict total order.

## Integrate Correctness

The main correctness theorem is in [`LeanYjs/IntegrateProof.lean`](LeanYjs/IntegrateProof.lean). This file contains over 2000 lines of proof establishing that the integrate algorithm is correct.

### Main Theorem

```lean
theorem YjsArrInvariant_integrate (newItem : YjsItem A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  -> InsertOk arr newItem
  -> integrate newItem arr = Except.ok newArr
  -> ∃ i ≤ arr.size, newArr = arr.insertIdxIfInBounds i newItem ∧ YjsArrInvariant newArr.toList
```

This theorem states that if:

1. The input array satisfies the Yjs array invariants
2. The new item satisfies the insertion preconditions (`InsertOk`)
3. The integrate function succeeds

Then the result is equivalent to inserting the item at some valid position that preserves all invariants.

### Loop Invariant

The proof uses a complex loop invariant (`loopInv`) that tracks:

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

The file also proves that integration is commutative:

```lean
theorem integrate_commutative (a b : YjsItem A) (arr1 arr2 arr3 arr2' arr3' : Array (YjsItem A)) :
  YjsArrInvariant arr1.toList
  -> a.id ≠ b.id
  -> InsertOk arr1 a
  -> InsertOk arr1 b
  -> integrate a arr1 = Except.ok arr2
  -> integrate b arr2 = Except.ok arr3
  -> integrate b arr1 = Except.ok arr2'
  -> integrate a arr2' = Except.ok arr3'
  -> arr3 = arr3'
```

This shows that the order in which operations are integrated doesn't affect the final result, which is crucial for CRDTs.

---

This technical documentation provides the detailed mathematical foundations underlying the LeanYjs formalization. The key insight is that by carefully restricting the allowed item configurations through invariants, we can ensure that the naturally complex conflict resolution rules result in a well-defined total order that supports commutative operations.
