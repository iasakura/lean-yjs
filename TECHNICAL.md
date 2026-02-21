# LeanYjs Technical Documentation

This document describes the current LeanYjs formalization and points to the
actual implementation and proof files in this repository.

## Table of Contents

1. [Core Data Model](#core-data-model)
2. [Insert Algorithm](#insert-algorithm)
3. [Ordering Relations](#ordering-relations)
4. [Array and State Invariants](#array-and-state-invariants)
5. [Preservation Proofs](#preservation-proofs)
6. [Commutativity Proofs](#commutativity-proofs)
7. [Network Model and Convergence](#network-model-and-convergence)
8. [Executable Differential Testing](#executable-differential-testing)

## Core Data Model

### Items and pointers

Defined in `LeanYjs/Item.lean`:

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

`YjsId` comparison (`LT YjsId`) is:

- primary key: `clientId` ascending
- tie-breaker (same client): `clock` descending

That matches Yjs-style client-based tie-breaking with newer local clocks treated
as smaller in the local chain.

### State

Defined in `LeanYjs/Algorithm/Basic.lean`:

```lean
structure YjsState (A : Type) where
  items : Array (YjsItem A)
  deletedIds : DeletedIdSet
```

`deletedIds` stores tombstones for delete operations (`ExtTreeSet` keyed by `YjsId`).

## Insert Algorithm

Main executable logic is in `LeanYjs/Algorithm/Insert/Basic.lean`.

### Input form

```lean
structure IntegrateInput (A : Type) where
  originId : Option YjsId
  rightOriginId : Option YjsId
  content : A
  id : YjsId
```

`IntegrateInput.toItem` resolves optional origin ids against the current array
and builds a concrete `YjsItem`.

### Key functions

- `findLeftIdx`
- `findRightIdx`
- `findIntegratedIndex`
- `mkItemByIndex`
- `integrate`
- `isClockSafe`
- `integrateSafe`
- `YjsState.insert`

Core definitions:

```lean
def integrate (newItem : IntegrateInput A) (arr : Array (YjsItem A)) :
  Except IntegrateError (Array (YjsItem A))

def integrateSafe (newItem : IntegrateInput A) (arr : Array (YjsItem A)) :
  Except IntegrateError (Array (YjsItem A))
```

`integrateSafe` gates integration with `isClockSafe`, enforcing per-client
clock monotonicity.

### Delete side

Defined in `LeanYjs/Algorithm/Delete/Basic.lean`:

```lean
def deleteById (state : YjsState A) (id : YjsId) : YjsState A
```

This updates only `deletedIds`.

## Ordering Relations

The order theory is in `LeanYjs/Order/*.lean`, centered on
`LeanYjs/Order/ItemOrder.lean`.

### Primitive relation

```lean
inductive OriginLt : YjsPtr A -> YjsPtr A -> Prop
```

With constructors for sentinel ordering (`first < item < last`).

### Main mutually-recursive relations

```lean
mutual
  inductive YjsLt : Nat -> YjsPtr A -> YjsPtr A -> Prop
  inductive YjsLeq : Nat -> YjsPtr A -> YjsPtr A -> Prop
  inductive ConflictLt : Nat -> YjsPtr A -> YjsPtr A -> Prop
end
```

Abbreviations:

```lean
def YjsLt'  (x y : YjsPtr A) : Prop := ∃ h, YjsLt h x y
def YjsLeq' (x y : YjsPtr A) : Prop := ∃ h, YjsLeq h x y
```

### Item-set assumptions

`LeanYjs/Order/ItemSetInvariant.lean`:

```lean
structure ItemSetInvariant (P : ItemSet A) where
  origin_not_leq : ...
  origin_nearest_reachable : ...
  id_unique : ...
```

These constraints rule out pathological graphs and are required for total-order
results.

### Total-order results

- `yjs_lt_total` (`LeanYjs/Order/Totality.lean`)
- `yjs_lt_trans` (`LeanYjs/Order/Transitivity.lean`)
- `yjs_lt_asymm` (`LeanYjs/Order/Asymmetry.lean`)

## Array and State Invariants

`LeanYjs/Algorithm/Invariant/YjsArray.lean` defines:

```lean
structure YjsArrInvariant (arr : List (YjsItem A)) : Prop where
  closed : IsClosedItemSet (ArrSet arr)
  item_set_inv : ItemSetInvariant (ArrSet arr)
  sorted : List.Pairwise (fun x y => YjsLt' x y) arr
  unique : uniqueId arr

def YjsStateInvariant (state : YjsState A) : Prop := YjsArrInvariant state.items.toList
```

Insert proof-side validity helpers in `LeanYjs/Algorithm/Insert/Spec.lean`:

```lean
structure IsItemValid (item : YjsItem A) where
  origin_lt_rightOrigin : YjsLt' item.origin item.rightOrigin
  reachable_YjsLeq' : ...

abbrev YjsItem.isValid : YjsItem A → Prop := IsItemValid

def maximalId (newItem : YjsItem A) (arr : Array (YjsItem A)) := ...
```

## Preservation Proofs

Main file: `LeanYjs/Algorithm/Insert/Spec.lean`.

### Integration preserves array invariant

```lean
theorem YjsArrInvariant_integrate (input : IntegrateInput A) (arr newArr : Array (YjsItem A)) :
  YjsArrInvariant arr.toList
  → input.toItem arr = Except.ok newItem
  → newItem.isValid
  → maximalId newItem arr
  → integrate input arr = Except.ok newArr
  → ∃ i ≤ arr.size, newArr = arr.insertIdxIfInBounds i newItem ∧ YjsArrInvariant newArr.toList
```

### Safe integration preserves invariant

```lean
theorem YjsArrInvariant_integrateSafe ...
```

### State-level preservation

```lean
theorem YjsStateInvariant_insert (arr newArr : YjsState A) (input : IntegrateInput A) :
  YjsStateInvariant arr
  → input.toItem arr.items = Except.ok newItem
  → newItem.isValid
  → arr.insert input = Except.ok newArr
  → YjsStateInvariant newArr
```

Delete preservation is in `LeanYjs/Algorithm/Delete/Spec.lean`:

```lean
theorem YjsStateInvariant_deleteById ...
```

## Commutativity Proofs

### Insert/Insert

`LeanYjs/Algorithm/Commutativity/InsertInsert.lean`:

- `integrate_commutative`
- `insert_commutative`

These establish equivalence of the two integration orders for concurrent
inserts under the theorem preconditions (distinct client ids, no origin
reachability cycles, validity assumptions).

### Insert/Delete

`LeanYjs/Algorithm/Commutativity/InsertDelete.lean`:

```lean
theorem integrateSafe_deleteById_commutative ...
```

### Delete/Delete

`LeanYjs/Algorithm/Commutativity/DeleteDelete.lean`:

```lean
theorem deleteById_commutative ...
```

## Network Model and Convergence

### Generic model

- `LeanYjs/Network/CausalNetwork.lean`
- `LeanYjs/Network/OperationNetwork.lean`
- `LeanYjs/Network/StrongCausalOrder.lean`

The framework defines histories of broadcast/deliver events, happens-before
consistency, and operation interpretation over local histories.

### Yjs instantiation

`LeanYjs/Network/Yjs/YjsNetwork.lean` defines:

- `YjsOperation` (`insert` / `delete`)
- `YjsOperationNetwork` (extends generic `OperationNetwork`)
- validity and invariant preservation for Yjs operations

Key results:

- `YjsOperationNetwork_concurrentCommutative`
- `YjsOperationNetwork_converge'`

`YjsOperationNetwork_converge'` is the convergence theorem used here: if two
clients deliver the same set of operations (possibly in different
happens-before-consistent orders), they reach equal final states.

## Executable Differential Testing

### Lean runner

`DiffTestRunner.lean` provides an executable (`diff-test-runner`) that:

- accepts NDJSON commands from stdin
- applies `insert` and `sync` transitions to per-client `YString` states
- outputs final per-client strings as JSON

Command forms:

- `{"type":"insert","clientId":...,"index":...,"char":"..."}`
- `{"type":"sync","from":...,"to":...}`

### JS differential harness

`diff-test/` compares Lean output with upstream `yjs`:

- deterministic scenario test: `diff-test/src/insert.test.ts`
- property-based test (`fast-check`): `diff-test/src/pbt.test.ts`
- helper bridge for building/running Lean binary: `diff-test/src/testUtils.ts`

Run:

```bash
lake build diff-test-runner
cd diff-test
pnpm install
pnpm test
```
