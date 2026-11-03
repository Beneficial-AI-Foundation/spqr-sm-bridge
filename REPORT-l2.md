# L2 for the code's PolyDecoder

Result: L2 holds. `SpqrBridge.L2.polyStreamDecoder_lawful` proves that the extracted
`PolyDecoder` is a `Lawful` stream decoder of secure-messaging (`la/generic-decoder`,
`c16e287c`). The proof has no `sorry`. There is no counterexample.

```
'SpqrBridge.L2.polyStreamDecoder_lawful' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpqrBridge.L2.encode_bytes_inv' depends on axioms: [propext, Classical.choice, Quot.sound]
'SpqrBridge.L2.next_chunk_eq_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Branch `poc/l2`. Files: `SpqrBridge/PolyDecoderLawful.lean` (decoder, L2) and
`SpqrBridge/PolyEncoderChunk.lean` (encoder agreement). Build: `lake build` in this worktree.

## What is proved

The proof is generic in `K`, the number of points per polynomial slot. The payload has `32 K`
bytes and the decoder is `PolyDecoder::new(32 K)`. Every stream has `pts_needed = 16 K`, so each
of the 16 slots needs exactly `K` points. The four streams are `K = 3` (header and MAC, 96
bytes), `K = 36` (ek, 1152 bytes), `K = 30` (ct1, 960 bytes) and `K = 5` (ct2 and MAC, 160
bytes). One theorem covers all four streams. Only the `Codec` (see below) differs per stream.

- `polyStreamDecoder_lawful`: L2 for `polyStreamDecoder K hKN cd` against `ecp K hK hKN cd`,
  for every `0 < K ≤ 2^16`.
- `honest_empty` (inside `polyStreamDecoder`), and `new_eq_emptyDecoder`: `PolyDecoder::new(32 K)`
  returns the decoder's `empty`.
- `add_chunk_inv`: an honest chunk keeps the decoder state honest. This covers the point skipping
  at `src/encoding/polynomial.rs:907-914` and the replace-or-insert of `SortedSet::push`. Either
  way, every stored point is a point of an honest chunk.
- `decoded_unflatten`: if `decoded_message` returns `Some v` from an honest state, then `v` is the
  serialized payload. If a slot has the point at `x = k/16`, the decoder reads it. Otherwise it
  interpolates through the first `K` stored points. Those points are on the slot polynomial, so
  the interpolant is that polynomial (`lagrangeInterpolantSum_eq_of_on`).
- `add_chunk_ok`, `decoded_message_ok`: from honest states neither function panics, so the error
  cases of the wrapper are not reached.
- `next_chunk_eq_encode` with `encode_bytes_inv`: `PolyEncoder::encode_bytes` over the payload
  bytes, then `next_chunk`, emits `(ecp K _ _ cd).encode p i` at counter `i < 2^16`.

The arrival order does not matter for L2. The decoder keeps only points of the one codeword
polynomial. Any `K` of them with distinct abscissae determine the polynomial, and the abscissae
are distinct because the slots are sorted sets of 16-bit values.

## Design choices

- `Sym` is the chunk payload `Std.Array U8 32#usize`. A code chunk maps to `(index.val, data)`.
- `ErasureCode`: `N = 2^16`, `nchunk = K`. `encode msg j` is `codeChunk msg j`: word `s` of the
  chunk is the slot-`s` polynomial at `j`. That polynomial is the Mathlib Lagrange interpolant
  through `(k, word s of chunk k)` for `k < K` (`codePoly`). `decode` is the constant `none`,
  because L2 does not use it and the bridge uses the code's decoder instead.
- `ErasureCodePayload`: `M` is generic. A `Codec M K` gives `ser : M → Fin K → Sym`, `parse`
  and `parse ∘ ser = some`. The adapter (`bridge-1b`) supplies one codec per stream, for example
  header ‖ MAC as 3 chunks of 32 bytes.
- `StreamDecoder`: `D = PolyDecoder`. `addChunk d (n, data)` runs `add_chunk` on the chunk with
  index `n mod 2^16`. If the call fails, the state stays the same. `decodedPayload d` is `parse`
  of the bytes from `decoded_message`, and `none` on `None` or on a failure.
- `Honest d p` is `Inv (cd.ser p) d`: `pts_needed = 16 K`, every slot is a sorted set
  (`PointsValid`), and every stored point of slot `s` lies on `codePoly (cd.ser p) s`. This
  invariant does not mention `is_complete`. When `is_complete` is true, `decoded_message`
  returns `None`, and L2 allows that.

## Remaining `sorry` and missing lemmas

There is no `sorry`. No lemma has to move to `spqr` or `sm` for L2. These lemmas are general,
and they belong in `spqr`:

- `natToGF216_inj` and `gfToNat` (`Nat.toGF216` is a bijection on `[0, 2^16)`).
- `lagrangeInterpolantSum_eq_interpolate` and `scaledLagrangeBasis_eq`. These show that the
  decoder's and the encoder's Lagrange formulas equal Mathlib's `Lagrange.interpolate`.
- `decodedValue_eq`, which states that `decoded_message` is correct on points of one
  polynomial. This is the reconstruction fact that issue #791 asks for.

## Limits and open points

- The encoder agreement covers counters `i < 2^16` only, because `next_chunk_spec` in `spqr`
  requires `idx ≤ U16.max`. The code truncates with `idx as u16`, which matches
  `counterIndex i = i % 2^16`. A spec of `next_chunk` without that precondition closes this gap.
- L2 is a safety law. A decoder that always returns `none` also satisfies it. Liveness (the
  decoder decodes after `K` distinct honest chunks) is not proved here. The SM bound does not
  need liveness, as the task brief says.
- The wrapper's error branches are faithful only on honest states (`add_chunk_ok`,
  `decoded_message_ok`). To relate the wrapper to the code's `Result` semantics, the coupling
  argument (`bridge-1c`) must use those two lemmas.

## Estimate for the rest

- Per-stream instances: about one hour each, for a `Codec` from the adapter's payload types
  and `K ∈ {3, 36, 30, 5}`. The theorems need no other change.
- Encoder for counters `≥ 2^16`: about half a day, for a `next_chunk` spec without the `u16`
  precondition in `spqr`.
- Liveness: if a later step needs it, about one day. It reuses `decodedValue_eq` and adds a
  counting argument over the stored points.
