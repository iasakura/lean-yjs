# Lean-Yjs: Formal Verification of Yjs Integration Algorithm

This project provides a formal verification of the Yjs integration algorithm using the Lean 4 theorem prover. Yjs is a high-performance CRDT (Conflict-free Replicated Data Type) library for building collaborative applications.

## Overview

This work focuses on the formal verification of Yjs's `integrate` operation, which is the core algorithm responsible for maintaining consistency when integrating new operations into a shared document state. The Lean sources are organized under:

- `LeanYjs/Algorithm`: the executable algorithm and its specifications
- `LeanYjs/Order`: ordering relations and invariants
- `LeanYjs/Network`: a causal network model used to reason about convergence

## Goal

While Yjs is closely related to the YATA (Yet Another Transformation Approach) algorithm, it employs a sophisticated tie-breaking mechanism that cleverly uses `rightOrigin`. To verify this algorithm, we need to establish an ordering relationship that differs from the one presented in the YATA paper.

Although the YATA paper presents the algorithm in a simplified manner, the correctness of Yjs's `integrate` operation is not trivial and requires dedicated loop invariants for verification. Additionally, while not explicitly clarified in the YATA paper, newly inserted items must satisfy certain conditions (guaranteed by the fact that insert operations use two adjacent elements as origins).

This work aims to clarify these aspects and formally verify the correctness of the Yjs integration algorithm. Specifically, we prove:

- **Preservation**: The integration maintains the invariants of the data structure (see `LeanYjs/Algorithm/IntegrateSpec.lean`)
- **Commutativity**: Operations can be integrated in any order and produce the same result (see `LeanYjs/Algorithm/IntegrateCommutative.lean`)
- **Convergence (aka Strong Eventual Consistency)**: On the causal delivery model in `LeanYjs/Network`, replicas that deliver the same set of operations reach the same state (`YjsOperationNetwork_converge'` in `LeanYjs/Network/YjsNetwork.lean`)

## Documentation

For detailed technical information about the formalization, see [TECHNICAL.md](TECHNICAL.md).

## References

- [Yjs Documentation](https://docs.yjs.dev/)
- [YATA Algorithm Paper](https://www.researchgate.net/publication/310212186_Near_Real-Time_Peer-to-Peer_Shared_Editing_on_Extensible_Data_Types)
- [Reference CRDT Implementations](https://github.com/josephg/reference-crdts)
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)
