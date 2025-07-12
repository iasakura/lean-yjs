# Lean-Yjs: Formal Verification of Yjs Integration Algorithm

This project provides a formal verification of the Yjs integration algorithm using the Lean 4 theorem prover. Yjs is a high-performance CRDT (Conflict-free Replicated Data Type) library for building collaborative applications.

## Overview

This work focuses on the formal verification of Yjs's `integrate` operation, which is the core algorithm responsible for maintaining consistency when integrating new operations into a shared document state. The project is currently **under development**.

## Goal

While Yjs is closely related to the YATA (Yet Another Transformation Approach) algorithm, it employs a sophisticated tie-breaking mechanism that cleverly uses `rightOrigin`. To verify this algorithm, we need to establish an ordering relationship that differs from the one presented in the YATA paper.

Although the YATA paper presents the algorithm in a simplified manner, the correctness of Yjs's `integrate` operation is not trivial and requires dedicated loop invariants for verification. Additionally, while not explicitly clarified in the YATA paper, newly inserted items must satisfy certain conditions (guaranteed by the fact that insert operations use two adjacent elements as origins).

This work aims to clarify these aspects and formally verify the correctness of the Yjs integration algorithm. Specifically, we prove:

- **Preservation**: The integration maintains the invariants of the data structure
- **Commutativity**: Operations can be integrated in any order and produce the same result

Note: Convergence (strong eventual consistency) follows from these properties but is not explicitly proven in this work.

## Current Status

🚧 **Under Development** 🚧

- ✅ Core data structures and operations defined
- ✅ Integration algorithm implemented
- ✅ Item ordering definition and total ordering proof
- 🔄 Preservation proof (work in progress)
- 🔄 Commutativity proof (work in progress)

## References

- [Yjs Documentation](https://docs.yjs.dev/)
- [YATA Algorithm Paper](https://www.researchgate.net/publication/310212186_Near_Real-Time_Peer-to-Peer_Shared_Editing_on_Extensible_Data_Types)
- [Reference CRDT Implementations](https://github.com/josephg/reference-crdts)
- [Lean 4 Manual](https://leanprover.github.io/lean4/doc/)

## License

MIT
