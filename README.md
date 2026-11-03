# SpqrBridge

Bridge between the SPQR code proofs (SparsePostQuantumRatchet-verify) and the SPQR correctness
bound of secure-messaging (`SPQR.correctness_error_le`). Local proof of concept.

Dependencies, by path:

- `../spqr`: SparsePostQuantumRatchet-verify, branch `la/poc-aeneas-bump` (Aeneas
  `nightly-2026.11.03-ab34bd2`, with `Global` renamed by hand in `SrcTranslated/`).
- `../sm`: secure-messaging, from `a3e953ee` (`ada/spqr-correctness`).

Build with `lake build`.
