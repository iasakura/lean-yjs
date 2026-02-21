# Lean-Yjs: Formal Verification of Yjs Integration

This repository formalizes core parts of the Yjs integration algorithm in Lean 4.
It focuses on insertion ordering, state invariants, operation commutativity, and
convergence under a causal network model.

## Overview

The formalization is organized into the following modules:

- `LeanYjs/Item.lean`: `YjsId`, `YjsPtr`, `YjsItem`
- `LeanYjs/Order/*.lean`: ordering relations and total-order properties
- `LeanYjs/Algorithm/Insert/*.lean`: executable insert logic and preservation proofs
- `LeanYjs/Algorithm/Delete/*.lean`: delete operation and invariance
- `LeanYjs/Algorithm/Commutativity/*.lean`: insert/insert, insert/delete, delete/delete commutativity
- `LeanYjs/Algorithm/Invariant/*.lean`: array/state invariants and supporting lemmas
- `LeanYjs/Network/*.lean`: generic causal/operation network framework
- `LeanYjs/Network/Yjs/YjsNetwork.lean`: Yjs-specific network instantiation and convergence theorem
- `DiffTestRunner.lean`, `diff-test/`: differential tests against upstream `yjs`

## Main Proven Results

- **Preservation**
  - `YjsArrInvariant_integrate` (`LeanYjs/Algorithm/Insert/Spec.lean`)
  - `YjsArrInvariant_integrateSafe` (`LeanYjs/Algorithm/Insert/Spec.lean`)
  - `YjsStateInvariant_insert` (`LeanYjs/Algorithm/Insert/Spec.lean`)
- **Commutativity**
  - `integrate_commutative` and `insert_commutative` (`LeanYjs/Algorithm/Commutativity/InsertInsert.lean`)
  - `integrateSafe_deleteById_commutative` (`LeanYjs/Algorithm/Commutativity/InsertDelete.lean`)
  - `deleteById_commutative` (`LeanYjs/Algorithm/Commutativity/DeleteDelete.lean`)
- **Convergence / SEC-style statement**
  - `YjsOperationNetwork_converge'` (`LeanYjs/Network/Yjs/YjsNetwork.lean`)

## Build

```bash
lake build
lake env lean LeanYjs.lean
```

## Differential Tests (Lean vs yjs)

Build the Lean executable and run JS-based differential tests:

```bash
lake build diff-test-runner
cd diff-test
pnpm install
pnpm test
```

## Documentation

For a detailed technical walkthrough, see [TECHNICAL.md](TECHNICAL.md).

## References

- [Yjs Documentation](https://docs.yjs.dev/)
- [YATA Paper](https://www.researchgate.net/publication/310212186_Near_Real-Time_Peer-to-Peer_Shared_Editing_on_Extensible_Data_Types)
- [reference-crdts](https://github.com/josephg/reference-crdts)
- [Lean 4 Documentation](https://leanprover.github.io/lean4/doc/)
