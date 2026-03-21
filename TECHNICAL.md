# LeanYjs Technical Documentation

## Goal Theorem

The project goal is the convergence theorem in `LeanYjs/Network/Yjs/YjsNetwork.lean`:

```lean
theorem YjsOperationNetwork_converge' {A} [DecidableEq A]
  (network : YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : YjsState A) :
  let hist_i := network.toDeliverMessages i
  let hist_j := network.toDeliverMessages j
  interpOps hist_i Operation.init = Except.ok res₀ →
  interpOps hist_j Operation.init = Except.ok res₁ →
  (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
  res₀ = res₁
```

This theorem is the SEC-style endpoint of the project. It compares two clients `i` and `j`, takes their delivered-operation histories `hist_i` and `hist_j`, and assumes both histories execute successfully from `Operation.init`, producing `res₀` and `res₁`. The key premise is set equality of delivered operations (`∀ item, item ∈ hist_i ↔ item ∈ hist_j`), not equality of list order. Under the causal and validity assumptions packaged in `YjsOperationNetwork`, the theorem concludes `res₀ = res₁`: delivery order may vary, but equal delivered operation sets yield the same final Yjs state.

## 1. Basic Data Structure

Yjs state is an ordered list of items. Each item (`YjsItem`) stores the `origin` and `rightOrigin` chosen when that item was generated (the insertion operation metadata), plus its `id`. The list is sorted by item order, and that order is determined by `origin`, `rightOrigin`, and `id`. Deletion is represented by tombstones: deleted item ids are recorded in `deletedIds` rather than physically removing items from `items`.

File: `LeanYjs/Item.lean`

```lean
structure YjsId where
  clientId : ClientId
  clock : Nat

mutual
inductive YjsPtr : Type where
  | itemPtr : YjsItem -> YjsPtr
  | first : YjsPtr
  | last : YjsPtr

structure YjsItem : Type where
  origin : YjsPtr
  rightOrigin : YjsPtr
  id : YjsId
  content : A
end
```

The development assumes that `YjsId` is globally unique per item (no two distinct `YjsItem`s share the same id). This expectation appears later as `ItemSetInvariant.id_unique` and array-level `uniqueId` constraints.

The algorithm state stores this sequence as an array:

```lean
structure YjsState (A : Type) where
  items : Array (YjsItem A)
  deletedIds : DeletedIdSet
```

## 2. YjsItem Validity Preconditions: `ItemSet`, `ItemSetInvariant`

- `LeanYjs/ItemSet.lean`
- `LeanYjs/Order/ItemSetInvariant.lean`

Core assumptions:

- closure of origins/right-origins in the item set
- no pathological origin/right-origin shape (`origin_not_leq`)
- nearest-reachable side condition (`origin_nearest_reachable`)
- id uniqueness (`id_unique`)

These conditions capture the structural validity expected of `YjsItem`s in this model, and they are used by later order and algorithm proofs.

## 3. Total Order

Files:

- `LeanYjs/Order/ItemOrder.lean`
- `LeanYjs/Order/Totality.lean`
- `LeanYjs/Order/Transitivity.lean`
- `LeanYjs/Order/Asymmetry.lean`

This project’s order is defined as an inductive relation tuned to the Yjs integration behavior (not a direct copy of the YATA paper relation).

Core inductive relations are:

- `YjsLt`, `YjsLeq`, `ConflictLt`
- shorthand predicates `YjsLt'`, `YjsLeq'`

Constructors used by this relation:

- `OriginLt`: sentinel/base order (`first < item < last`)

- `YjsLt.ltOrigin`: if `x ≤ item.origin` then `x < item`
- `YjsLt.ltRightOrigin`: if `item.rightOrigin ≤ x` then `item < x`
- `ConflictLt.ltOriginDiff`: overlap case with different origins and four side-conditions
- `ConflictLt.ltOriginSame`: overlap case with same origin; `id1 < id2` is used under its side-conditions

`yjs_lt_total` is proved mainly by exhaustive case analysis following these constructors (implemented with strong induction on `x.size + y.size`). `yjs_lt_trans` and `yjs_lt_asymm` are proved by strong induction on pointer/item size measures.

Main theorem statements:

```lean
theorem yjs_lt_total {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y : YjsPtr A), P x -> P y ->
    (∃ h, @YjsLeq A h x y) ∨ (∃ h, @YjsLt A h y x)
```

```lean
theorem yjs_lt_trans {A : Type} [DecidableEq A] {P : ItemSet A} {inv : ItemSetInvariant P} :
  IsClosedItemSet P ->
  ∀ (x y z : YjsPtr A), P x -> P y -> P z ->
  YjsLt' x y -> YjsLt' y z -> YjsLt' x z
```

```lean
theorem yjs_lt_asymm {A} [DecidableEq A] {P : ItemSet A} :
  IsClosedItemSet P ->
  ItemSetInvariant P ->
  ∀ (x y : YjsPtr A), P x -> P y -> YjsLt' x y -> YjsLt' y x -> False
```

## 4. Algorithm Invariants

File: `LeanYjs/Algorithm/Invariant/YjsArray.lean`

```lean
structure YjsArrInvariant (arr : List (YjsItem A)) : Prop where
  closed : IsClosedItemSet (ArrSet arr)
  item_set_inv : ItemSetInvariant (ArrSet arr)
  sorted : List.Pairwise (fun x y => YjsLt' x y) arr
  unique : uniqueId arr

def YjsStateInvariant (state : YjsState A) : Prop :=
  YjsArrInvariant state.items.toList
```

Field meanings:

- `closed`: every item's `origin`/`rightOrigin` stays inside the same array-set (plus sentinels).
- `item_set_inv`: order-side structural conditions on the same set (`origin_not_leq`, `id_unique`, etc.).
- `sorted`: array order is pairwise consistent with `YjsLt'`.
- `unique`: no duplicate `YjsId` in the array.

`YjsStateInvariant` simply lifts the same condition to `YjsState.items`. These invariants are what insert/delete proofs preserve at the algorithm level.

## 5. Preservation Proofs

Insert implementation and proofs:

- implementation: `LeanYjs/Algorithm/Insert/Basic.lean`
- proofs: `LeanYjs/Algorithm/Insert/Spec.lean`

Main preservation theorems:

- `YjsArrInvariant_integrate`
- `YjsArrInvariant_integrateSafe`
- `YjsStateInvariant_insert`

`YjsStateInvariant_insert` statement:

```lean
theorem YjsStateInvariant_insert (arr newArr : YjsState A) (input : IntegrateInput A) :
  YjsStateInvariant arr
  → input.toItem arr.items = Except.ok newItem
  → newItem.isValid
  → arr.insert input = Except.ok newArr
  → YjsStateInvariant newArr
```

This theorem captures preservation of `YjsStateInvariant` across an insert step. More concretely, it assumes that the pre-state `arr` already satisfies `YjsStateInvariant`, that resolving `input` against `arr.items` succeeds and produces a concrete `newItem`, and that this item satisfies `newItem.isValid`. Under these assumptions, if the executable insert step `arr.insert input` returns `newArr`, then `newArr` also satisfies `YjsStateInvariant`.

The predicate `newItem.isValid` is defined in `LeanYjs/Algorithm/Insert/Spec.lean` as:

```lean
structure IsItemValid (item : YjsItem A) where
  origin_lt_rightOrigin : YjsLt' item.origin item.rightOrigin
  reachable_YjsLeq' : (∀ (x : YjsPtr A),
      OriginReachable (YjsPtr.itemPtr item) x →
      YjsLeq' x item.origin ∨ YjsLeq' item.rightOrigin x)

abbrev YjsItem.isValid : YjsItem A → Prop := IsItemValid
```

Delete side:

- implementation: `LeanYjs/Algorithm/Delete/Basic.lean`
- proof: `LeanYjs/Algorithm/Delete/Spec.lean`
- theorem: `YjsStateInvariant_deleteById`

`YjsStateInvariant_deleteById` statement:

```lean
theorem YjsStateInvariant_deleteById (state : YjsState A) (id : YjsId) :
  YjsStateInvariant state →
  YjsStateInvariant (deleteById state id)
```

## 6. Commutativity Proofs

Files:

- `LeanYjs/Algorithm/Commutativity/InsertInsert.lean`
- `LeanYjs/Algorithm/Commutativity/InsertDelete.lean`
- `LeanYjs/Algorithm/Commutativity/DeleteDelete.lean`

Main results:

- `insert_commutative`
- `insert_deleteById_commutative` (insert-delete)
- `deleteById_commutative`

## 7. Network Layering to `YjsNetwork`

The stack is built in this order:

1. `CausalNetwork` (`LeanYjs/Network/CausalNetwork.lean`)
2. `StrongCausalOrder` (`LeanYjs/Network/StrongCausalOrder.lean`)
3. `OperationNetwork` (`LeanYjs/Network/OperationNetwork.lean`)
4. `YjsOperationNetwork` (`LeanYjs/Network/Yjs/YjsNetwork.lean`)

Role of each layer:

1. `CausalNetwork` provides concrete event histories (`Broadcast`/`Deliver`) and assumptions that connect local histories to happens-before.
2. `StrongCausalOrder` provides the hb-consistency/concurrency framework used by the final convergence pipeline (including `hb_consistent_effect_convergent`).
3. `OperationNetwork` connects network events to an executable operation model (`Operation.effect`, `isValidState`, invariant preservation).
4. `YjsOperationNetwork` is the Yjs-specific instantiation with insert/delete messages, Yjs state invariants, and Yjs-specific validity assumptions.

Why the strong framework is needed:

`LeanYjs/Algorithm/Insert/Basic.lean` (section `InconsistencyExample`) records a counterexample showing why an unconditional commutativity law is too strong for Yjs insert. Intuitively, if a state violates the nearest-reachable side condition (for example the `a/b/o/n` scenario in that section), different integration orders can produce different outcomes.

Therefore this project uses `StrongCausalOrder`, where commutativity is stated with explicit premises: state invariant, per-operation validity in that state, and successful execution. In that sense, the framework is "stronger" in assumptions but the commutativity claim itself is logically weaker than an unconditional one, which is exactly what Yjs needs.

From these layers, `YjsNetwork` proves:

- local concurrent commutativity: `YjsOperationNetwork_concurrentCommutative`
- final convergence goal: `YjsOperationNetwork_converge'`

How the final step works:

- `YjsOperationNetwork_concurrentCommutative` is proved by case analysis on concurrent operation pairs (insert/insert, insert/delete, delete/delete), using the commutativity theorems from Section 6.
- `YjsOperationNetwork_converge'` then applies the generic convergence machinery for hb-consistent executions (from the network/order layer) together with the Yjs commutativity and validity/invariant lemmas, yielding equal final states when delivered operation sets are equal.

## 8. Indirect Reference Variant

Files:

- `LeanYjs/Indirect/Item.lean`
- `LeanYjs/Indirect/Algorithm/Basic.lean`
- `LeanYjs/Indirect/Algorithm/Delete/Basic.lean`
- `LeanYjs/Indirect/Algorithm/Insert/Basic.lean`
- `LeanYjs/Indirect/Algorithm/Equivalence.lean`
- `LeanYjs/Indirect/Network/Yjs/YjsNetwork.lean`

The direct model stores `origin` and `rightOrigin` as recursive pointers (`YjsPtr`). For the indirect variant, the project keeps the original direct-reference development unchanged and adds a separate `Indirect` namespace. The purpose is to replace direct recursive pointers with id-based references while preserving the same executable behavior and convergence theorem.

### 8.1 Indirect Item Representation

`LeanYjs/Indirect/Item.lean` introduces:

```lean
inductive YjsRef where
  | itemId (id : YjsId)
  | first
  | last

structure YjsItem (A : Type) where
  origin : YjsRef
  rightOrigin : YjsRef
  id : YjsId
  content : A
```

So the indirect state removes recursive pointer structure from `YjsItem`. Instead of storing `YjsPtr.itemPtr item`, the item stores only `YjsId`, plus sentinels `first` and `last`.

The bridge from the direct model is:

- `YjsRef.ofDirectPtr`
- `ofDirectItem`
- `ofDirectState`

These collapse direct pointers to ids without changing item order, item ids, or payloads.

### 8.2 Indirect Algorithms

`LeanYjs/Indirect/Algorithm/Insert/Basic.lean` re-implements the integration algorithm using `YjsRef` lookup:

- `findRefIdx`
- `findLeftIdx`
- `findRightIdx`
- `findIntegratedIndex`
- `mkItem`
- `integrate`
- `integrateSafe`
- `YjsState.insert`

`LeanYjs/Indirect/Algorithm/Delete/Basic.lean` keeps deletion behavior the same as the direct model: delete only inserts into `deletedIds`.

The key point is that the indirect algorithm is not a wrapper around the direct algorithm. It is a separate executable implementation that works on indirect states.

### 8.3 State Equivalence

The relation between direct and indirect states is intentionally simple:

```lean
def StateEquivalent (direct : _root_.YjsState A) (indirect : YjsState A) : Prop :=
  ofDirectState direct = indirect
```

This means equivalence is extensional: the indirect state must literally be the direct state after erasing recursive pointers down to ids. Concretely, this implies:

- the arrays have the same length
- corresponding items have the same `id` and `content`
- corresponding `origin`/`rightOrigin` point to the same logical positions, but encoded as `YjsId`/sentinels rather than recursive pointers
- `deletedIds` are equal

### 8.4 Direct/Indirect Algorithm Correspondence

`LeanYjs/Indirect/Algorithm/Equivalence.lean` proves that the indirect executable algorithm matches the direct executable algorithm after applying `ofDirectState`.

Important bridge lemmas:

- `findLeftIdx_ofDirect`
- `findRightIdx_ofDirect`
- `findIntegratedIndex_ofDirect`
- `ofDirectItem_mkItemByIndex`
- `integrate_ofDirect`
- `integrateSafe_ofDirect`
- `insert_ofDirectState`
- `deleteById_ofDirectState`

The main preservation results are:

- `insert_preserves_stateEquivalent`
- `delete_preserves_stateEquivalent`

These are the formal version of the intended statement:

- if a direct state `s₁` and an indirect state `s₂` are equivalent
- and we perform corresponding direct/indirect operations successfully
- then the resulting states are again equivalent

So the indirect algorithm is proved behaviorally identical to the direct algorithm under the erasure map `ofDirectState`.

### 8.5 Indirect Network-Level Convergence

`LeanYjs/Indirect/Network/Yjs/YjsNetwork.lean` lifts the one-step correspondence to network executions.

It defines:

- `effect` for indirect `YjsOperation`
- `interpOps` for indirect states

Then it proves:

- `effect_ofDirectState`
- `effect_preserves_stateEquivalent`

To reach a convergence theorem, the file reconstructs a successful direct execution from a successful indirect execution:

- `stateInv_of_prefix` recovers the direct state invariant for every direct prefix execution
- `direct_of_indirect_suffix` lifts one-step equivalence to suffix executions
- `direct_of_indirect_from_source` reconstructs an entire successful direct run from an indirect run

Finally, the indirect network theorem is:

```lean
theorem YjsOperationNetwork_converge {A} [DecidableEq A]
  (network : _root_.YjsOperationNetwork A) (i j : ClientId) (res₀ res₁ : YjsState A) :
  let hist_i := network.toCausalNetwork.toDeliverMessages i
  let hist_j := network.toCausalNetwork.toDeliverMessages j
  interpOps hist_i YjsEmptyState = Except.ok res₀ →
  interpOps hist_j YjsEmptyState = Except.ok res₁ →
  (∀ item, item ∈ hist_i ↔ item ∈ hist_j) →
  res₀ = res₁
```

This theorem is proved by:

1. converting each successful indirect execution into a successful direct execution with an equivalent final state
2. applying the existing direct convergence theorem `YjsOperationNetwork_converge'`
3. transporting the resulting direct-state equality back through `ofDirectState`

So the indirect variant reuses the original network proof architecture, but only after proving that indirect execution is a faithful implementation of the direct algorithm.

## Appendix: Executable Differential Testing

- Lean runner: `DiffTestRunner.lean`
- JS harness: `diff-test/src/*.ts`

Run:

```bash
lake build diff-test-runner
cd diff-test
pnpm install
pnpm test
```
