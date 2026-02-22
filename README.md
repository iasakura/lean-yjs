# Lean-Yjs: Formal Verification of Yjs Integration Algorithm

Lean-Yjs is a Lean 4 formalization of the Yjs sequence-integration algorithm. The project models how replicated clients apply insert and delete operations, and proves that replicas converge when they process the same operations under causal delivery.

## Motivation

The Yjs integration algorithm was proposed in the YATA line of work, where proofs were given only for selected lemmas and not for full algorithmic correctness. Correctness of CRDT algorithms is subtle in practice, and the algorithm as presented in the YATA paper was later found to contain a mistake (see <https://discuss.yjs.dev/t/lean-yjs-formally-proving-the-yjs-conflict-resolution-algorithms/3875>). This project uses Lean 4 to provide a rigorous proof for the Yjs algorithm, including properties that were not proved in the YATA paper such as commutativity and convergence, while also formalizing side conditions that are easy to miss in prose descriptions.

## Main Theorem and Structure

The central result is `YjsOperationNetwork_converge'` in `LeanYjs/Network/Yjs/YjsNetwork.lean`. Intuitively, it says that if two replicas deliver the same set of Yjs operations under causal delivery, then they end in the same state even when delivery order differs.

The formalization is organized in three layers. `LeanYjs/Order` proves that the item ordering forms a total order (totality, asymmetry, transitivity). `LeanYjs/Algorithm` formalizes the executable insert/delete procedures and proves their correctness properties. `LeanYjs/Network` formalizes a Yjs network model on top of causal delivery (`CausalNetwork`) and proves convergence in that model. In addition to the proofs, `diff-test` runs randomized differential tests against Yjs to check implementation-level agreement.

More detailed definitions and proof flow are documented in [TECHNICAL.md](TECHNICAL.md).

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

## Acknowledgments

The algorithm formalization was informed by `integrateYjs` in `reference-crdts`.


## References

- [YATA Paper](https://www.researchgate.net/publication/310212186_Near_Real-Time_Peer-to-Peer_Shared_Editing_on_Extensible_Data_Types)
- [reference-crdts](https://github.com/josephg/reference-crdts)
