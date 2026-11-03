# W1 report: primitive and tape obligations

Result: 12 of the 13 W1 theorems are proved. `mac_length` is open, because it needs a fact
about the opaque `libcrux_hmac.hmac` that no axiom gives. No statement, definition or other
theorem changed. `lake build` passes. Branch `poc/w1`, local only.

## Status

| Theorem | File | Status |
|---|---|---|
| `codePrims_agreesSeeded` | `CodePrims.lean` | proved |
| `keyGen_valid` | `CodeParams.lean` | proved |
| `bytesOfChunks_chunkOf` | `CodeParams.lean` | proved |
| `keyGen_lengths` | `CodeContracts.lean` | proved |
| `encaps1_lengths` | `CodeContracts.lean` | proved |
| `encaps2_agree` | `CodeContracts.lean` | proved |
| `encaps2_ok` | `CodeContracts.lean` | proved |
| `decaps_agree` | `CodeContracts.lean` | proved |
| `kdfOK_agree` | `CodeContracts.lean` | proved |
| `mac_length` | `CodeContracts.lean` | open, `sorry` (see below) |
| `codeSend_tape_irrel` | `CodeContracts.lean` | proved |
| `codeSend_prefix` | `CodeContracts.lean` | proved |
| `relTriple_sampleTape_pure` | `CodeContracts.lean` | proved |

## Why `mac_length` is open

The premises bound the key and the data by `usize::MAX`. The only HMAC fact is the axiom
`hmac_sha256_tag32_spec`, which needs both lengths at most `u32::MAX`. `Usize.max` is
`2^System.Platform.numBits - 1`, and Lean cannot prove `numBits = 32`. For a key of
`2^32` bytes, no axiom says that `hmac` succeeds, so `codePrims.mac` is the `pick` default,
whose length is unknown. The Rust glue panics there (`try_into().unwrap()`), so an axiom
that says `hmac` succeeds is false for the code. The statement is not shown false, but it
cannot be proved without a new axiom.

`mac_length_u32` in `CodePrimsFacts.lean` proves the same claim with `u32::MAX` premises. If
the contract changes to `u32::MAX`, its proof is `mac_length_u32 k d hk hd`. Whether the
callers meet that bound is for W4 to check. The authenticator MACs short inputs.

## Helper files

| File | Content |
|---|---|
| `SpqrBridge/SeededSpecs.lean` | `generate_ok_seed`, `encaps1_ok_hdr`, `encaps1_ok_msg`: FIPS 203 values of a successful `generate` or `encaps1` with any RNG. The proof swaps in an RNG whose `fill_bytes` returns the observed result, so `generate_spec` and `encaps1_spec` apply. Imported by `CodePrims.lean`. |
| `SpqrBridge/CodePrimsFacts.lean` | lengths of `seededKeyGen` and `seededEncaps1`, `codePrims_ekMatches_generated`, `encaps2_ok_length`, `decaps_ok_length`, `flatten_ofFn_blocks`, `mac_length_u32`. |
| `SpqrBridge/TapeFacts.lean` | `relTriple_bind_pure_right`, `dropRng` (a result without its RNG), `codeSend_congr`, `dropRng_send_irrel`, `tapeFill_take`, `generate_tape`, `encaps1_tape`, `dropRng_send_prefix`. |

`CodeParams.lean` imports `CodePrimsFacts` and `TapeFacts`, so `CodeContracts.lean` needs no
new import line. This keeps the merge with W4 to proof bodies.

`relTriple_sampleTape_pure` calls the generic `relTriple_bind_pure_right`. The same proof
written inline over `sampleTape` makes the `constructorNameAsVariable` linter hit the
recursion limit.

## Axioms

`#print axioms` gives `propext`, `Classical.choice` and `Quot.sound` for `codeParams`,
`codeKem`, `smScheme` and every proved theorem, with two additions:

* `encaps2_ok` also uses `potentially_fix_state_incorrectly_encoded_by_libcrux_issue_1275_spec`,
  through `encaps2_spec`. It gives success only, as the plan expects for #788.
* `mac_length` has `sorryAx`. `mac_length_u32` uses `hmac_sha256_tag32_spec`.

No `sorryAx` reaches `codeParams`, `codeKem` or `smScheme`. No new axiom.

## Lemmas that belong in `spqr`

* `generate_ok_seed`, `encaps1_ok_hdr`, `encaps1_ok_msg`: the "if it returns `Ok`" forms of
  `generate_spec` and `encaps1_spec`, without the `fill_bytes` premise.
* `encaps2_ok_length`, `decaps_ok_length`: a successful `encaps2` returns 128 bytes and a
  successful `decaps` returns 32, with no length premise.
* `generate_tape`, `encaps1_tape`, `dropRng_send_prefix`: these state that a `send` reads at
  most 64 bytes of its RNG. They fit the single infinite tape of #787 once the tape RNG is
  in `spqr`.
