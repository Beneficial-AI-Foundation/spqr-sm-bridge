# SpqrBridge

Bridge between the SPQR code proofs (SparsePostQuantumRatchet-verify) and the SPQR correctness
bound of secure-messaging (`SPQR.correctness_error_le`). Local proof of concept.

Dependencies, by path:

- `../spqr`: SparsePostQuantumRatchet-verify, branch `la/poc-aeneas-bump` (Aeneas
  `nightly-2026.11.03-ab34bd2`, with `Global` renamed by hand in `SrcTranslated/`).
- `../sm`: secure-messaging, branch `la/generic-decoder` (`c16e287c`), one commit on top of
  `a3e953ee` (`ada/spqr-correctness`). It makes the ML-KEM Braid and SPQR machines generic in
  their stream decoder, so the Rust decoder can be used in them directly.

Build with `lake build`.
