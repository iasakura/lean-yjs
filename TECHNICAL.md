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
