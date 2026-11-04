# Bridge fields: key lengths and counter wrap

All three bridge-owned fields of `BridgeObligations` are proved. Each theorem has exactly the
field's type: `by with_reducible rfl` closes the type equality against the field of
`BridgeObligations` (`SpqrBridge/CodeBound.lean`). `CodeBound.lean` is not changed.

| Field | Theorem | File |
|-------|---------|------|
| `send_key_length` | `SpqrBridge.codeSend_key_length` | `SpqrBridge/KeyLength.lean` |
| `recv_key_length` | `SpqrBridge.codeRecv_key_length` | `SpqrBridge/KeyLength.lean` |
| `next_chunk_wrap` | `SpqrBridge.next_chunk_wrap` | `SpqrBridge/NextChunkWrap.lean` |

The names differ from the field names for the keys because `Adapter.lean` already has
`send_key_length` and `recv_key_length` as `sorry` theorems. W5 can close those two with the new
theorems, or delete them.

## Axioms

`#print axioms`:

- `codeSend_key_length`, `codeRecv_key_length`: `propext`, `Classical.choice`, `Quot.sound`,
  `spqr.kdf.hkdf_to_slice_spec`. The last is the documented HKDF axiom of the trusted base,
  reached through `hkdf_to_vec_spec`.
- `next_chunk_wrap`: `propext`, `Classical.choice`, `Quot.sound`.

No `sorryAx`. No new axioms.

## How

Keys: `send_key_epoch` and `recv_key_epoch` (spqr, `KeyFloor.lean`) show that only `send` from
`HeaderReceived` and `recv` of a `Ct2` chunk in `EkSentCt1Received` emit a key. Both secrets
come from `hkdf_to_vec … 32`. No state invariant is needed, so the fields hold for every state,
tape and message.

Wrap: `next_chunk_inv_wrap` calls `chunk_at_spec` with `idx as u16` directly, instead of
`next_chunk_spec`, which needs `idx ≤ u16::MAX`. It gives index `idx % 2^16`, the chunk of that
index, `EncInv` kept, and stored counter `(idx + 1) % 2^32` from `wrapping_add_val_eq`.

## Lemmas that belong in `spqr`

- `send_ct1_secret_length`, `send_ct1_chunk_secret_length`, `recv_ct2_secret_length`,
  `recv_ct2_chunk_secret_length`, and the two key-length statements restated over
  `States.send` / `States.recv` without the `codeSend` / `codeRecv` wrappers.
- A `next_chunk_spec` without the `idx ≤ u16::MAX` premise, with `chunk.index.val = idx % 2^16`
  and the words at `idx % 2^16` (issue #783). `next_chunk_inv_wrap` does this at the level of
  `EncInv`; the spqr version would state it with `NextChunkPostCond` at the truncated index.
