# W5 report: the conditional code-level bound

`code_correctness_error_le` is proved. Its statement is unchanged, except that
`BridgeObligations` lost three fields. No `sorryAx` is in its closure. `lake build` passes.
Branch `poc/w5`, local only, on `main` at `7c0d873`.

## Changes

- `BridgeObligations` (`CodeBound.lean`) has no `send_key_length`, `recv_key_length` or
  `next_chunk_wrap`. The users call the theorems `codeSend_key_length`, `codeRecv_key_length`
  (`KeyLength.lean`) and `next_chunk_wrap` (`NextChunkWrap.lean`). `ChunkedRecv` and
  `ChunkedSend` import those files. `encStep`, `braid_send_pure`, `keysUnsampled_agree` and
  `headerReceived_agree` no longer take `hB`, because they used only `next_chunk_wrap`.
- `code_correctness_error_le` moved from `CodeBound.lean` to the new file
  `CodeCorrectness.lean`. The move is necessary because `send_chunked` and `receive_chunked`
  are in files that import `CodeBound`.
- `PotentialTransferSPQR.lean`: the two `S₂` premises that `spqr_correctness_error_le_of_transfer`
  proved inline are now the lemmas `spqr_potential_ge_one` and `spqr_potential_init`. Both
  theorems use them. The statement of `spqr_correctness_error_le_of_transfer` did not change.
- `Adapter.lean`: the `sorry` theorems `send_key_length`, `recv_key_length` and the structure
  `AdapterObligations` are deleted. Nothing used them.
- `ChunkedFacts.lean`: `codePrims_mac_length` is deleted. Its users call W1's
  `mac_length_u32`. `codePrims_encaps2_length` stays: its proof already uses the W1 contracts
  `encaps2_ok` and `encaps2_agree`, which use `encaps2_ok_length`. It is a statement over
  `codePrims.encaps2`, not a second copy of the proof.

## Proof

`codeBudgetedObligations` gives `BudgetedTransferObligations (codeScheme k) (smScheme k) smInv
CodeGameInv RA RA RM (2^64 - 2)`:

- `init`: `codeGameInv_init`, `ra_initA`, `ra_initB`.
- `pres`: `codeGameInv_pres`.
- `sendA`, `sendB`: `send_chunked`. `ReachParty` comes from `CodeGameInv`. The epoch premise
  comes from `codeGameInv_epochs` and `nA + nB < 2^64 - 2`.
- `recvA`, `recvB`: `receive_chunked`. The message epoch premise comes from
  `codeGameInv_epochs` and `nA + nB ≤ 2^64 - 2`.

`code_correctness_error_le` applies `correctness_error_le_of_budgeted_transfer`. `Inv₂`, `V₂`
and the four `S₂` premises are those of `spqr_correctness_error_le_of_transfer`, with the four
decoders lawful by `L2.polyStreamDecoder_lawful`. `ε` is
`codeKem.correctnessError ProbCompRuntime.probComp`. `q + 2 < 2^64` gives `q < 2^64 - 2`.
The recursion-depth workaround of W4 was not needed.

## Audit

`lake build`: no `declaration uses 'sorry'` warning in `SpqrBridge/`, and none in the
dependencies. The remaining warnings existed before W5 (`ImportProbe` header,
`PolyDecoderLawful` deprecation and module hint, three in `spqr` and `sm`).

`#print axioms code_correctness_error_le`:

- `propext`, `Classical.choice`, `Quot.sound`
- `spqr.kdf.hkdf_to_slice_spec`
- `libcrux_hmac.hmac_sha256_tag32_spec`
- `incremental_mlkem768.potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec`

No other `spqr` axiom is reached. `recv_refines` is not in the closure. Only
`reachParty_refines` uses it, and nothing uses `reachParty_refines`. Through `recv_refines`,
`reachParty_refines` also has the `bv_decide` certificate `spqr.util.inz_spec._native.bv_decide.ax_1_13`,
which the top theorem therefore does not have. No `sorryAx`.

Definitions:

| Definition | Axioms |
|---|---|
| `codeScheme` | Lean's three, `spqr.kdf.hkdf_to_slice_spec` |
| `codeParams`, `codeKem`, `smScheme`, `codeAuth`, `codeIrl` | Lean's three |
| `RA`, `RM` | Lean's three |
| `CodeGameInv`, `BridgeObligations` | Lean's three, `spqr.kdf.hkdf_to_slice_spec` |

None depends on `sorryAx`.

## Dependencies

- `../spqr`: `b5973cc5673d474972b669a85a0b32cca1231054`, branch `la/poc-aeneas-bump`. Dirty:
  17 modified tracked files, among them `SrcTranslated/{Funs,FunsExternal,Types}.lean`,
  `lakefile.toml`, `lean-toolchain` and `lake-manifest.json`. These are the Aeneas bump.
- `../sm`: `c16e287c897b4f99bea7f9879abad338a2bf0618`, branch `la/generic-decoder`, clean.
- `lake-manifest.json`: not changed since `7c0d873`. `Spqr` and `SecureMessaging` are path
  dependencies. `aeneas` is at `ab34bd28`.

## Remaining fields of `BridgeObligations`

| Field | Removed by |
|---|---|
| `mlkem_sizes` | #786 |
| `send_total` | #785 |
| `recv_complete` | #785 |
| `send_refines_tape` | #787 |

## Limits

- The theorem is conditional on the four fields above.
- `ε` is the correctness error of `codeKem`. It is not yet tied to ML-KEM's small error,
  because of the opaque workaround in `encaps2` (#788).
- It covers the SCKA correctness game only: honest delivery, no injected bytes, no liveness and
  no rollback.
- The bump of `SrcTranslated/` in `../spqr` was a hand rename, not a new extraction.
