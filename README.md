# SpqrBridge

A Lean 4 proof that transfers the SCKA correctness bound of
[secure-messaging](https://github.com/Beneficial-AI-Foundation/secure-messaging) from its model of
SPQR to the chunked `States` machine of
[SparsePostQuantumRatchet](https://github.com/signalapp/SparsePostQuantumRatchet) v1.6.0, presented
as an SCKA scheme by an adapter. The machine is the Aeneas extraction verified in
[SparsePostQuantumRatchet-verify](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify).
The result does not cover the rest of the library, such as serialization or the public API.

This is a proof of concept. The theorem is conditional on four facts about the code that are not
proved yet. It also depends on a trusted base: three axioms, and Lean models of the external
functions that the code calls. Both lists are in [Assumptions](#assumptions).

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
   Its proved theorems, `send_refines` and `recv_refines`, cover one direction: a step of the code
   that succeeds refines a `Braid` step, for some randomness. The bound needs more: `send` does not
   fail, its randomness is the prefix of the bytes it read, and the code accepts every message that
   `Braid` accepts. These are the fields `send_total`, `send_refines_tape` and `recv_complete` of
   `BridgeObligations`. So the part of step 1 that the theorem uses is assumed, not proved, and
   `code_correctness_error_le` does not use `send_refines` or `recv_refines`.
2. **`Braid` to `SPQR.Chunked`.** This repository relates `Braid` to secure-messaging's model
   `SPQR.Chunked`, arm by arm (`send_chunked`, `receive_chunked`). The transfer in step 3 compares
   the code's game with secure-messaging's, so it uses the composition `RA`. If some `Braid` state
   lies between a code state and a secure-messaging state, `RA` relates them. Messages
   are related by `Braid`'s message map followed by the chunk map (`RM`).
3. **The bound.** secure-messaging proves `SPQR.correctness_error_le` with one lemma,
   `correctness_error_le_of_potential`, over an invariant and a function on its game states (its
   potential). This repository reuses that invariant and its one-step bounds for the code's game
   (`correctness_error_le_of_budgeted_transfer`). The code-side function is the infimum of the
   secure-messaging one over the related game states that satisfy the invariant, capped at 1. The
   relation of game states (`GameRel`) relates both party states by `RA` and the recorded messages
   by `RM`. The key tables, counters and flag are equal. After each step, the game states are
   related again, or the secure-messaging game failed. A failed secure-messaging game has potential
   at least 1. The code-side function is at most 1, so a failure pays for any behavior of the code.
   If secure-messaging refuses a recorded message, `RecvRel` puts no requirement on the code. That
   refusal already loses the correctness game. The code's epochs
   are `u64`, but an epoch never exceeds the number of sends plus one. So the obligations are
   needed only in runs with fewer than `2^64 - 2` sends, and the code never overflows there.

Two facts make the second relation possible:

- **Generic stream decoders.** The Rust erasure decoder skips points as they arrive, so its
  state depends on the arrival order. The secure-messaging branch below makes `MLKEMBraid` and
  `SPQR.Chunked` generic in their stream decoder, with one safety law, `StreamDecoder.Lawful`.
  Its own set-based decoder is an instance. The generic theorems take the law as a premise in
  place of erasure-code correctness, and the concrete v1 bound keeps its statement.
- **The Rust decoder is lawful.** `polyStreamDecoder_lawful`: from an honest state, adding an
  honest chunk keeps the state honest, and the decoder returns nothing or the payload. The law is
  a safety property only. A decoder that never returns a payload also satisfies it, so the law
  says nothing about progress.

## Assumptions

The theorem rests on three groups of assumptions. The first two are visible in Lean: the premise
`BridgeObligations` and the output of `#print axioms`. The third group is in definitions, so Lean
does not list it.

### Premises

`BridgeObligations` has four fields. Each is a statement about the code, owned by an issue of
SparsePostQuantumRatchet-verify:

| Field | Statement | Issue |
|---|---|---|
| `mlkem_sizes` | libcrux reports the ML-KEM-768 sizes 960 (`ct1`), 128 (`ct2`) and 1152 (encapsulation key) | [#786](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/786) |
| `send_total` | on a reachable state whose epoch plus one fits in a `u64`, `send` with at least 64 bytes of randomness succeeds | [#785](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/785) |
| `recv_complete` | on a reachable state that refines a `Braid` state, where `Braid` accepts a message whose epoch plus one fits in a `u64`, `recv` succeeds with a state that refines `Braid`'s next state and with the same key | [#785](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/785) |
| `send_refines_tape` | a successful `send` takes the `Braid` step whose randomness is the prefix of the bytes that the code read: the next states are related, and the message and key are the same | [#787](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/787) |

The exact statements are the fields of `BridgeObligations` in `SpqrBridge/CodeBound.lean`.

Nobody has shown yet that the four fields hold together. If one is false, the theorem says
nothing. Two fields claim more than the correctness game needs: `send_refines_tape` has no
reachability premise, and `recv_complete` covers every message that `Braid` accepts, not only
recorded ones. If a proof of a field fails at this generality, the field can be narrowed to the
states and messages of `CodeGameInv`.

### Axioms

Beyond Lean's three axioms, `#print axioms code_correctness_error_le` lists three axioms of the
trusted base of SparsePostQuantumRatchet-verify: `spqr.kdf.hkdf_to_slice_spec`,
`libcrux_hmac.hmac_sha256_tag32_spec` and
`incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec`.

### Models and other trusted parts

The theorem is about the Lean model of the code. The steps from the Rust code to that model are
trusted, and Lean does not list them:

- **Lean models of libcrux ML-KEM.** In `SrcTranslated/FunsExternal.lean` of
  SparsePostQuantumRatchet-verify, `from_seed`, `encapsulate1`, `encapsulate2` and
  `decapsulate_compressed_key` are Lean definitions that follow FIPS 203, not extractions of
  libcrux. The theorem holds for these definitions. That they agree with libcrux is trusted.
  Theorems such as `from_seed_eq_mlkemKeyGen` hold by `rfl`, so they relate two Lean definitions
  and say nothing about libcrux code. Two known differences from libcrux are listed in [Limits](#limits).
  FIPS 203 does not standardize the incremental API (`encapsulate1`, `encapsulate2` and the
  2080-byte state between them). The model ties it to FIPS 203 only through a composition law:
  the two rounds together give ML-KEM.Encaps (`Spqr/Crypto/Fips203/KEM/EncapsIncremental.lean`).
- **Opaque functions.** These constants have no definition. So the theorem holds for every
  function of their type that meets the axioms above. The constants are `Fips203.stdPrimitives`
  (SHA3 and SHAKE), `crypto.HMAC_SHA256`, `libcrux_hmac.hmac` and the libcrux #1275 workaround.
  They also include the libcrux length functions `Ciphertext1.len`, `Ciphertext2.len` and
  `pk2_len`, whose values are the premise `mlkem_sizes`.
- **Total wrappers.** `pick` and `fit` (`SpqrBridge/CodePrims.lean`) make the code's primitives
  total. Outside the inputs on which the code succeeds, they return an arbitrary value or zeros.
  `SpqrBridge/CodeContracts.lean` proves that the code's results match them on those inputs.
- **The adapter.** `codeScheme` (`SpqrBridge/Adapter.lean`) gives each send 64 fresh uniform bytes,
  not the output of a real random number generator. It maps an Aeneas panic, a divergence and a
  Rust `Err` to a refused call. A refused send leaves the game unchanged. So `send_total` is
  necessary: without it, a code that refuses every send also meets the bound.
- **The extraction and the tools.** Charon, Aeneas and its library, VCVio and Lean. The extraction
  was edited by hand (see [Limits](#limits)).

## Limits

- The theorem is conditional on the four fields above.
- `ε` is the correctness error of `codeKem`, a KEM built from the Lean models of libcrux. It is
  not yet bounded, so the result gives no number. If `q · ε ≥ 1`, the bound says nothing. See
  [Toward a numerical bound](#toward-a-numerical-bound).
- It covers the correctness game only: no injected messages, no liveness, no state rollback.
- It covers runs in which the current code produces every state. States that libcrux versions
  before the fix of [cryspen/libcrux#1275](https://github.com/cryspen/libcrux/issues/1275)
  persisted are outside its scope. On AVX2, those versions wrote the encapsulation state with
  byte-swapped words. SPQR's workaround repairs such a state unless every word of `e₂` is 0 or
  -1. For an honestly sampled `e₂`, that case has probability `(10/16)^256 ≈ 2^-173.6`.
- The SparsePostQuantumRatchet-verify branch moves to Aeneas `nightly-2026.11.03-ab34bd2` by
  renaming one identifier in the extracted files by hand, without a new extraction.
- The source references in `SrcTranslated/FunsExternal.lean` name libcrux-ml-kem 0.0.7 and
  libcrux-hmac 0.0.6, but `Cargo.lock` pins 0.0.10 and 0.0.8. For ML-KEM, the incremental API,
  the state layout, sampling and serialization are the same in 0.0.7 and 0.0.10, so only the
  references are stale.
- The model of the 2080-byte encapsulation state writes each coefficient as its value in
  `[0, q)`. libcrux writes signed 16-bit values, which are often negative
  (`Spqr/Crypto/Fips203/Refinement/EncapsBytes.lean`). The model reads back what it writes, so
  `codeKem` and the theorem are not affected. Statements about the bytes that libcrux writes do not
  hold, for example about a persisted state. See [#800](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/800).

## Toward a numerical bound

secure-messaging proves a number for its own ML-KEM-768, `MLKEM.mlkem768Scheme`:
`deltaCorrect_mlkem768` bounds its correctness error by `2^(-164.8)`, under the hypothesis
`CoefficientFailureBound`. Its concrete SPQR bound is `q` times this error. The bridge bounds
`q · ε` with `ε` the error of `codeKem`. The two KEMs are different Lean models, and neither is
libcrux. To get a number, relate them:

1. **The samplers.** Both models cap `SampleNTT`, as FIPS 203 Appendix B permits, and return the
   zero polynomial on exhaustion. VCVio's concrete instance stops after 280 byte triples
   (`Extern/MLKEM/Instance.lean`), and SparsePostQuantumRatchet-verify after 1024
   (`Spqr/Crypto/Fips203/Sampling/SampleNTT.lean`). See [#799](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/issues/799). A run that succeeds within 280 triples also
   succeeds within 1024, with the same polynomial. So the two samplers agree outside the event
   that a 280-triple run fails.
2. **The primitives.** Both use opaque hash functions: `Fips203.stdPrimitives` and VCVio's FFI
   SHA3 and SHAKE. A hypothesis that they compute the same functions is necessary.
3. **The rest of ML-KEM.** Prove that the two FIPS 203 models agree on key generation,
   encapsulation and decapsulation, given 1 and 2.
4. **The #788 workaround.** `codeKem` applies it only to states that the model wrote. There, the
   words of `e₂` are 0, 1, 2, 3327 and 3328, and the Rust body returns `None`. The Lean
   workaround is opaque, so this needs a specification of the workaround, which is SPQR's own
   Rust code. The bridge needs only the corollary for these states. The axiom for arbitrary
   2080-byte inputs stays.

Then `ε ≤ ε_SM + δ`, where `ε_SM` is the error of `mlkem768Scheme` and `δ` bounds the
probability that a 280-triple run fails. A bound on `δ` needs a hypothesis on SHAKE128, because
it is opaque in both models.

The step from these models to libcrux stays trusted. libcrux has no cap, so it agrees with each
model outside its exhaustion event. Its incremental API has no standard. The evidence for both is
testing, not proof.

## Transfer of other properties

The method transfers a bound proved with `correctness_error_le_of_potential`. A new theorem of
secure-messaging, for example key secrecy, authentication or security against injected messages,
needs more than this repository gives.

These parts can be reused:

- The relations `ChunkedRel`, `RA` and `RM`, with the proofs for every arm.
- The facts about the Rust erasure code: `polyStreamDecoder_lawful`, `PolyEncoderChunk` and
  `next_chunk_wrap`.
- The adapter `codeScheme`, the epoch bound and the four obligations, once they are proved.

These parts hold only for correctness:

- If secure-messaging refuses, `RecvRel` lets the code do anything. For authentication, a refusal
  of a forged message is the wanted behavior, so it cannot pay for an acceptance by the code.
- The obligation `init` compares supports only, not distributions.
- The code-side invariant `CodeGameInv` and the epoch bound assume that every delivered message
  was sent by the other party.
- `GameRel` relates the fields of the correctness game only.

A security property needs a transfer theorem of the form
`Adv_code(A) ≤ Adv_SM(A') + δ`, where `A'` is an adversary against secure-messaging built from `A`.
Its premises must show:

- The adversary sees the same outputs in both games, at every query, and in both worlds of a
  distinguishing game.
- The distributions of the initial states are related, not only their supports.
- On an injected message, the code and secure-messaging both accept or both refuse. The parsers
  and serializers agree.
- The exposure oracles correspond: corrupted states, leaked randomness and challenge keys. The
  current send coupling ignores the leaked randomness. This includes the tape bytes that the code
  does not read.
- The assumptions on the primitives, for example that HMAC is a PRF, hold for the code's
  primitives. Today these primitives are opaque.

The relation does not need to be a bijection. The information that it drops must not be visible
to the adversary. Liveness needs progress laws for the decoder and delivery assumptions.

## Dependencies and build

| Package | Repository | Branch | Commit |
|---|---|---|---|
| `Spqr` | SparsePostQuantumRatchet-verify | `la/bridge-aeneas-bump-main` | `c950d94` |
| `SecureMessaging` | secure-messaging | `la/generic-decoder` | `c16e287` |

The `Spqr` branch is `main` at `15bf667`, which includes
[#781](https://github.com/Beneficial-AI-Foundation/SparsePostQuantumRatchet-verify/pull/781), plus
one commit that moves to Aeneas `nightly-2026.11.03-ab34bd2` and Lean `v4.35.0` (see
[Limits](#limits)). `lakefile.toml` pins both commits. Both packages use Lean `v4.35.0` and Mathlib
`56a00585`. The first build compiles both dependencies and takes a while. `lake exe cache get`
fetches Mathlib only.

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
