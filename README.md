# SpqrBridge

A Lean 4 proof that transfers the SCKA correctness bound of
[secure-messaging](https://github.com/Beneficial-AI-Foundation/secure-messaging) from its model of
SPQR to the chunked `States` machine of
[SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet) v1.6.0, presented
as an SCKA scheme by an adapter. The machine is the Aeneas extraction verified in
[SparsePostQuantumRatchet-verify](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify).
The result does not cover the rest of the library, such as serialization or the public API.

This is a proof of concept. The theorem is conditional on four facts about the code that are not
proved yet, listed below.

## Result

Let `sampleInitKey` sample initial keys that the code accepts. Let `adv` be an SCKA correctness
adversary that makes at most `q` send queries across both parties, with `q + 2 < 2^64`. Let `codeScheme`
be the code's chunked `States` machine, presented as an SCKA scheme. Each send draws 64 uniform
random bytes, independent of earlier sends, and the code reads at most 64 of them. Then

```text
1 - Pr[ correctnessExp (codeScheme sampleInitKey) adv = true ]  ≤  q · ε
```

where `ε` is the correctness error of `codeKem`, the KEM that the code's ML-KEM-768 models define.

```lean
theorem code_correctness_error_le (hB : BridgeObligations) (sampleInitKey : ProbComp InitKey)
    (adv : SCKACorrectnessAdversary Message) (q : ℕ)
    (hq : SendQueryBound adv q) (hq64 : q + 2 < 2 ^ 64) :
    1 - Pr{let x ← correctnessExp (codeScheme sampleInitKey) adv}[x = true] ≤
      (q : ℝ≥0∞) * codeKem.correctnessError ProbCompRuntime.probComp
```

The correctness experiment is Def. 3.1 of [ADJKS25]: monotonic, matching and unique epochs,
consistent keys, and a known prefix. The adversary delivers unmodified recorded messages, in any
order and with replay. It does not inject messages.

## Method

The proof composes three relations:

1. **Code to `Braid`.** SparsePostQuantumRatchet-verify relates the extracted `States` machine to an
   abstract machine `Braid` that follows ML-KEM Braid [MLKEMBraid], with the code's deviations.
2. **`Braid` to `SPQR.Chunked`.** This repository relates `Braid` to secure-messaging's model
   `SPQR.Chunked`, arm by arm (`send_chunked`, `receive_chunked`). The transfer in step 3 compares
   the code's game with secure-messaging's, so it uses the composition: a code state and a
   secure-messaging state are related when some `Braid` state lies between them (`RA`). Messages
   are related by `Braid`'s message map followed by the chunk map (`RM`).
3. **The bound.** secure-messaging proves `SPQR.correctness_error_le` with one lemma,
   `correctness_error_le_of_potential`, over an invariant and a function on its game states (its
   potential). This repository reuses that invariant and its one-step bounds for the code's game
   (`correctness_error_le_of_budgeted_transfer`). The code-side function is the infimum of the
   secure-messaging one over the related game states that satisfy the invariant, capped at 1. Two
   game states are related when both party states are related by `RA`, the recorded messages by
   `RM`, and the key tables, counters and flag are equal. The step obligations keep the game states
   related. The
   code's epochs are `u64`, but an epoch never exceeds the number of sends plus one. So the
   obligations are needed only in runs with fewer than `2^64 - 2` sends, and the code never
   overflows there.

Two facts make the second relation possible:

- **Generic stream decoders.** The Rust erasure decoder skips points as they arrive, so its
  state depends on the arrival order. The secure-messaging branch below makes `MLKEMBraid` and
  `SPQR.Chunked` generic in their stream decoder, with one safety law, `StreamDecoder.Lawful`.
  Its own set-based decoder is an instance. The generic theorems take the law as a premise in
  place of erasure-code correctness, and the concrete v1 bound keeps its statement.
- **The Rust decoder is lawful.** `polyStreamDecoder_lawful`: from an honest state, adding an
  honest chunk keeps the state honest, and the decoder returns nothing or the payload.

## Assumptions

`BridgeObligations` has four fields. Each is a statement about the code, owned by an issue of
SparsePostQuantumRatchet-verify:

| Field | Statement | Issue |
|---|---|---|
| `mlkem_sizes` | libcrux reports the ML-KEM-768 sizes 960 (`ct1`), 128 (`ct2`) and 1152 (encapsulation key) | [#786](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/786) |
| `send_total` | on a reachable state whose epoch plus one fits in a `u64`, `send` with at least 64 bytes of randomness succeeds | [#785](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/785) |
| `recv_complete` | on a reachable state that refines a `Braid` state, where `Braid` accepts a message whose epoch plus one fits in a `u64`, `recv` succeeds with a state that refines `Braid`'s next state and with the same key | [#785](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/785) |
| `send_refines_tape` | a successful `send` takes the `Braid` step whose randomness is the prefix of the bytes that the code read: the next states are related, and the message and key are the same | [#787](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/787) |

The exact statements are the fields of `BridgeObligations` in `SpqrBridge/CodeBound.lean`.

Beyond Lean's three axioms, `#print axioms code_correctness_error_le` lists three axioms of the
trusted base of SparsePostQuantumRatchet-verify: `spqr.kdf.hkdf_to_slice_spec`,
`libcrux_hmac.hmac_sha256_tag32_spec` and
`incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec`.

## Limits

- The theorem is conditional on the four fields above.
- `ε` is not yet identified with the correctness error of ML-KEM-768, so the result gives no
  numerical bound. The code's `encaps2` first calls an opaque workaround whose axiom only fixes
  the length of its result ([#788](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/788)).
- It covers the correctness game only: no injected messages, no liveness, no state rollback.
- The SparsePostQuantumRatchet-verify branch moves to Aeneas `nightly-2026.11.03-ab34bd2` by
  renaming one identifier in the extracted files by hand, without a new extraction.

## Dependencies and build

| Package | Repository | Branch | Commit |
|---|---|---|---|
| `Spqr` | SparsePostQuantumRatchet-verify | `la/bridge-aeneas-bump` | `1017e52` |
| `SecureMessaging` | secure-messaging | `la/generic-decoder` | `c16e287` |

`lakefile.toml` pins both commits. Both packages use Lean `v4.35.0` and Mathlib `56a00585`. The
first build compiles both dependencies and takes a while. `lake exe cache get` fetches Mathlib
only.

Install Lean through [elan](https://github.com/leanprover/elan), which reads `lean-toolchain`.
Then, from the repository root:

```bash
lake exe cache get
lake build
```

## Files

| File | Content |
|---|---|
| `CodeCorrectness.lean` | the theorem |
| `CodeBound.lean` | `BridgeObligations`, the code-side game invariant, the budgeted transfer statement |
| `Adapter.lean`, `EpochBound.lean` | the code as an SCKA scheme, and its epoch bound |
| `CodePrims.lean`, `CodeParams.lean` | the code's primitives, and secure-messaging parameters built from them |
| `ChunkedRel.lean`, `ChunkedSend*.lean`, `ChunkedRecv*.lean` | the relation between `Braid` and `SPQR.Chunked`, with every arm |
| `PolyDecoderLawful.lean`, `PolyEncoderChunk.lean`, `NextChunkWrap.lean` | the Rust erasure code against secure-messaging's interface |
| `PotentialTransfer.lean`, `BudgetedPotential.lean` | the transfer of the bound |

## References

- [MLKEMBraid] Signal. *The ML-KEM Braid Protocol*, Revision 1.
  https://signal.org/docs/specifications/mlkembraid/
- [ADJKS25] Auerbach, Dodis, Jost, Katsumata, Schmidt. *How to Compare Bandwidth Constrained
  Two-Party Secure Messaging Protocols: A Quest for A More Efficient and Secure Post-Quantum
  Protocol.* USENIX Security 2025, https://eprint.iacr.org/2025/2267.pdf

## License

MIT. See `LICENSE`.
