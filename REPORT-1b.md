# Probe 1b report: the SCKA adapter `codeScheme`

Result: no stop condition fires. `init_a` and `init_b` succeed on `InitKey`, and `codeScheme`
type-checks with no default state and no `sorry` in any definition. `#print axioms codeScheme`
gives `propext`, `Classical.choice`, `Quot.sound` and `spqr.kdf.hkdf_to_slice_spec`, with no
`sorryAx`. The `hkdf_to_slice_spec` axiom enters through the `new_spec` lemmas that prove
`init_a_ok` and `init_b_ok`.

Files: `SpqrBridge/Adapter.lean`, `SpqrBridge/EpochBound.lean`. Build with `lake build`.

## Definitions

| Name | What it is |
|---|---|
| `InitKey` | `{k : Slice Std.U8 // k.length + 32 ≤ Std.Usize.max}` |
| `okOf`, `initAState`, `initBState` | the state that `init_a` or `init_b` returns, from a proof that the call succeeds |
| `tapeFill`, `tapeCore`, `tapeRng`, `tapeCrypto` | the tape RNG. `fill_bytes` takes the first bytes of a `List Std.U8`. If the tape is too short, it fails. `next_u32` and `next_u64` fail, and `States::send` does not call them. |
| `B n` | `{b : List Std.U8 // b.length = n}` |
| `sampleTape` | a uniform `Vector (Fin 256) 64`, mapped to `B 64` |
| `codeSend`, `codeRecv` | `States::send` and `States::recv`. If the call returns `Ok`, the result is `some`, else `none`. |
| `keyOf` | `EpochSecret` to `(epoch, B 32)`. If the secret is not 32 bytes long, the result is an outer `none`. |
| `sendStep`, `recvStep` | one call in SCKA's output form |
| `codeSendA`, `codeSendRleak` | sample a tape, then `sendStep`. The leaking form also returns the tape. |
| `codeScheme` | `SCKAScheme ProbComp InitKey States States (B 32) Message (B 64)` |
| `CodeReach` | the code configurations that a correctness game reaches, with the number of successful sends |

## Obligations

| Theorem | Status |
|---|---|
| `init_a_ok`, `init_b_ok`: `init_a` and `init_b` succeed on `InitKey` | proved |
| `init_a_ok_imp`, `init_b_ok_imp`: success implies `k.length + 32 ≤ Usize.max` | proved |
| `send_epoch`: a successful `send` stamps the message with the state epoch and keeps the state epoch | proved |
| `recv_epoch_le`: after a successful `recv`, the state epoch is at most `max old (msg.epoch + 1)` | proved |
| `epoch_bound`: over `CodeReach`, state and message epochs are at most sends plus one | proved |
| `epoch_budget`: with `n ≤ q` and `q + 2 < 2^64`, every epoch plus one fits in a `u64` | proved |
| `send_key_length`: a key from a successful `send` is 32 bytes long | `sorry` |
| `recv_key_length`: a key from a successful `recv` is 32 bytes long | `sorry` |

`AdapterObligations` bundles the two open obligations.

The initial relation to SM's state is not in this probe. `ChunkedRel` does not exist yet.
`init_refines` already relates `init_a` and `init_b` to `InitAlice` and `InitBob` of the
abstract Braid machine.

## Design choices

Initial key. The `+ 32` bound is the exact condition. `init_a` and `init_b` both call
`Authenticator::new`, which concatenates the 32-byte zero root key and the key. If
`k.length + 32 > Usize.max`, the concatenation fails, and only then. Both directions are proved, so
the subtype is unchanged.

No default state. `initAState` uses `Classical.choose` on the proof that `init_a` succeeds.
The value of a successful `Result` is unique, so the choice is the code's own state. `init_a_eq`
states `init_a k = ok (initAState k)`.

Errors. An Aeneas failure, a divergence and a Rust `Err` all give `none`. This matches SM's
oracles:

- A send that gives `none` leaves the game state unchanged and does not record a message. A
  failed Rust `send` likewise returns no new state, and `lib.rs` keeps the old one. A send that
  always fails meets the bound, so send success (#785) stays a separate requirement.
- A receive that gives `none` sets `correct` to false and keeps the state. An `Err` on an honest
  delivery is a correctness failure. The code returns `Err` for a message from a future epoch
  (`recv_of_gt`). It returns `Ok` and keeps its state for a stale message (`recv_of_lt`).
- A key that is not 32 bytes long also gives `none`. `send_key_length` and `recv_key_length`
  say that this does not happen, so this branch does not change either game.

Epoch reports. `send` reports `out.msg.epoch - 1` and `recv` reports `msg.epoch - 1`, also for
stale messages, as `lib.rs:298` and `lib.rs:425` do. A key is reported at `es.epoch`. The
coupling (1c) must check that this scale matches SM's key epochs.

Randomness. `Rand` is `B 64`, the tape of the send. `sendArleak` returns it. The frozen
statement has `Unit` (see below).

Tape length. `States::send` calls `fill_bytes` once at most: 64 bytes in `generate`, 32 bytes in
`encaps1`. A 64-byte tape is long enough, but this is not proved. It belongs to the sampling
obligations (deliverable 3), together with the unused tape bytes.

Epoch budget: the relation carries the send count. Capped oracles change the scheme to
`States × ℕ` and add `q` as a parameter of `codeScheme`. They also need a proof that the cap
changes neither game. The game already counts successful sends (`nA + nB`). Each successful send
is a send query, so `SendQueryBound adv q` gives `nA + nB ≤ q`. `epoch_bound` and `epoch_budget`
then give `u64` epochs that never overflow and equal SM's natural-number epochs, so the relation
can hold up to `q` sends. The proof that `nA + nB` stays at most `q` along the game belongs to
the coupling (1c).

Epoch bound after a failure. The bound holds after a failure. A failed call leaves both states
and both message lists unchanged in SM's oracles, so `CodeReach` has no step for it. After
`correct` becomes false, the game continues from the same states. `CodeReach` uses the code's
own successful calls. So a send whose key the adapter refuses is still a step, and the bound
covers it. The proof shows a stronger fact: message epochs are at most the number of sends.

## Lemmas that belong in `spqr`

- `send_key_length`, `recv_key_length` (open). If a lemma over all states is too hard, a form
  over reachable states is enough for the bridge. The existing component specs
  (`send_ct1_chunk_spec`, `recv_ct2_spec_shape`) give 32 bytes, but under state invariants.
- `auth_new_ok_imp`, `init_a_ok_imp`, `init_b_ok_imp`, `send_epoch`, `recv_epoch_le`,
  `epochOf_le_keyFloor`, `keyFloor_le_epochOf_succ` (proved here). They fit next to
  `Authenticator/New.lean` and `Braid/Scka/EpochUniqueness/KeyFloor.lean`.

## Changes to `docs/statements/code-correctness-bound.md`

1. The type of `codeScheme sampleInitKey` in the commentary has `Unit` as the randomness type.
   With a leaking send that returns its tape, it is `B 64`. The correctness game does not use
   `Rand`, so the theorem statement does not change. Only the commentary changes.
2. The commentary asks probe 1b to make sure that `+ 32` is the exact condition. It is, in
   both directions (`init_a_ok_imp`, `init_b_ok_imp`). The commentary can say so.
3. `hq64 : q + 2 < 2 ^ 64` is enough for the epoch budget (`epoch_budget`). No change is needed.
