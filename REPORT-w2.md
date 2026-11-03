# W2 report: `Braid` → `SPQR.Chunked`

Result: the feasibility test is proved, and so is every arm. `send_chunked` and
`receive_chunked` hold for all eleven states. The proofs use only fields of `BridgeObligations`
and W1 contracts. `lake build` passes. Branch `poc/w2`, local only, on `main` at `a577957`.
The dependencies are `../spqr` at `b5973cc` and `../sm` at `c16e287c`. `lake-manifest.json`
did not change.

## Definitions (`SpqrBridge/ChunkedRel.lean`)

- `DecWF K d`: the decoder needs `16 K` points and its slots are sorted.
- `EncRel K cd enc es`: `es.ecp` is `L2.ecp K cd`, `L2.EncInv (cd.ser es.payload) enc` holds,
  and `enc.idx.val = es.nextIndex % 2^32`. This is the form of `next_chunk_wrap`.
- `SameState σ st`: the same constructor, equal epochs and authenticators, and each `Braid`
  byte field is the value of the typed field. Decoders are equal and satisfy `DecWF`, and
  encoders satisfy `EncRel`. In `keysSampled` and `ekReceivedCt1Sampled`, the `Braid` header
  is the SM header.
- `ChunkedRel σ st := (authOf σ).macKey.length = 32 ∧ SameState σ st`.
- `RA s st := ∃ σ, Refines s σ ∧ ChunkedRel σ st`.
- `RM m m'`: equal epochs, and payloads correspond by constructor, with each chunk
  `c ↦ (c.index.val, c.data)`. `Ct1Ack true` maps to `ct1Ack`. `Ct1Ack false` maps to SM's
  `none` payload, as in `absMsg`.

Three choices differ from the plan:

1. `ChunkedRel` carries `DecWF`, so no decoder-honesty premise is needed. With `DecWF`,
   `add_chunk` and `decoded_message` succeed on any chunk (`decStep`). That is enough because
   the arms are one-sided, and the decoded value comes from SM's acceptance. The
   honesty-from-`Inv₂` lemma of the plan is therefore not needed and was not written.
2. `ChunkedRel` carries the 32-byte MAC key. Without it, `fit 32` hides a MAC of the wrong
   length, and then SM can accept where `Braid` refuses. Every transition sets the key with
   `Auth.update`, so the fact is established where each state is built.
3. `RM` maps `Ct1Ack false` to `none`, not to nothing. The send side recovers `RM` from
   `absMsg out.msg`, which cannot tell `None` from `Ct1Ack false`. The receive proofs are
   unchanged.

## Status

| Theorem | File | Status |
|---|---|---|
| `recvRel_ekSentCt1Received_ct2` (feasibility test) | `ChunkedRecv.lean` | proved |
| `receive_chunked` (every recv arm, `RecvRel RA`) | `ChunkedRecvAll.lean` | proved |
| `send_chunked` (every send arm, `SendRel RA RM`) | `ChunkedSendAll.lean` | proved |
| `ra_initA`, `ra_initB` (initial states) | `ChunkedSendAll.lean` | proved |
| `reachParty_refines` | `CodeContracts.lean` | proved |
| `polyStreamDecoder_addChunk_code` | `CodeContracts.lean` | proved |
| `polyStreamDecoder_decoded_code` | `CodeContracts.lean` | proved |

The receive arms are the `recv_*` theorems in `ChunkedRecv.lean`, one per state and payload that
`Chunked.recv` acts on (eight theorems for eleven state and payload pairs). `chunked_recv_braid` adds the stale epoch, the
successor epoch in `ct2Sampled`, the future-epoch error and all ignored messages. The send arms
are `braid_send_pure` (nine states, `ChunkedSend.lean`), `keysUnsampled_agree` and
`headerReceived_agree`.

## What each proof uses

| Theorem | `BridgeObligations` fields | W1 contracts (still `sorry` here) |
|---|---|---|
| `receive_chunked` | `recv_complete`, `recv_key_length`, `mlkem_sizes` | `encaps2_ok`, `encaps2_agree` |
| `send_chunked` | `send_total`, `send_refines_tape`, `send_key_length`, `next_chunk_wrap` | `keyGen_lengths`, `encaps1_lengths`, `relTriple_sampleTape_pure` |
| `ra_initA`, `ra_initB` | none | `codePrims_agreesSeeded` |
| `reachParty_refines` | none (`hsz` premise) | none |

All the theorems also reach `keyGen_valid` and `bytesOfChunks_chunkOf` through `codeParams`.
W1 proved every contract in this table on `poc/w1`. `mac_length` is not used: the MAC length
comes from `codePrims_mac_length` (`ChunkedFacts.lean`), which needs `u32::MAX` bounds and the
HMAC axiom, as in W1's `mac_length_u32`.

`receive_chunked` takes `ReachParty s n` and `msg.epoch.val + 1 < 2^64` as premises. W5 gets
both from `CodeGameInv` and `codeGameInv_epochs` at `nA + nB ≤ Bud`. `send_chunked` takes
`s.epochOf.val + 1 < 2^64`, which follows from `codeGameInv_epochs` at `nA + nB < Bud`.

## Axioms

`#print axioms` gives the same list for `send_chunked`, `receive_chunked` and
`recvRel_ekSentCt1Received_ct2`: `propext`, `Classical.choice`, `Quot.sound`, `sorryAx`,
`libcrux_hmac.hmac_sha256_tag32_spec` and `spqr.kdf.hkdf_to_slice_spec`. For `ra_initA` and
`ra_initB`, the list is the same without the HMAC axiom. A scan of the dependency closure
shows that `sorryAx` comes only from W1 theorems. These are `keyGen_valid`,
`bytesOfChunks_chunkOf`, `keyGen_lengths`, `encaps1_lengths`, `relTriple_sampleTape_pure`,
`encaps2_ok`, `encaps2_agree` and `codePrims_agreesSeeded`. `reachParty_refines` and both decoder
contracts have no `sorryAx`. `reachParty_refines` inherits `spqr`'s axioms through
`recv_refines`. No new axiom.

## Changes outside new files

- `SpqrBridge/CodeContracts.lean`: only the three `sorry` bodies of the task.
- `SpqrBridge.lean`: six import lines for the new files.

## For W5 and the interface

- The `BudgetedTransferObligations` need `RB = RA`. Both parties use the same `RA`.
- The plan's decoder-honesty lemma is not needed with this `ChunkedRel`. `Inv₂` is not used.
- `codePrims_encaps2_length` and `codePrims_mac_length` duplicate W1 helpers
  (`encaps2_ok_length`, `mac_length_u32`). Keep one copy after the merge.
- No interface change is needed. Arms were committed in groups, not one commit per arm.
