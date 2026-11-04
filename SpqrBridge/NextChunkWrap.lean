/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.PolyEncoderChunk
import SpqrBridge.Adapter

/-!
# `next_chunk` at every `u32` counter

`next_chunk_eq_encode` covers counters below `2^16` and says the stored counter grows by one.
Here the counter is any `u32`. `next_chunk` emits index `idx as u16`, that is `idx % 2^16`,
with the chunk of that index, and stores `idx.wrapping_add(1)`, that is `(idx + 1) % 2^32`.
`next_chunk_inv_wrap` states this for the encoder, and `next_chunk_wrap` proves the
`next_chunk_wrap` field of `BridgeObligations`. The proof calls `chunk_at_spec` with the
truncated index, so it does not need the `idx ≤ u16::MAX` premise of `next_chunk_spec`.
-/

open Aeneas Aeneas.Std Polynomial spqr.encoding.polynomial spqr.encoding.gf

namespace SpqrBridge.L2

open spqr.encoding.polynomial.PolyEncoder spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder in
/-- From an encoder holding `msg` at any counter `idx`, `next_chunk` succeeds, emits the chunk
`(idx % 2^16, codeChunk msg (idx % 2^16))`, stores `(idx + 1) % 2^32` and still holds `msg`. -/
theorem next_chunk_inv_wrap {K : ℕ} (hKN : K ≤ 2 ^ 16)
    (hKadm : K = 1 ∨ K = 3 ∨ K = 5 ∨ K = 30 ∨ K = 34 ∨ K = 36)
    (msg : Fin K → Sym) (enc : PolyEncoder) (hinv : EncInv msg enc) :
    ∃ c enc', next_chunk enc = .ok (c, enc') ∧
      c.index.val = enc.idx.val % 2 ^ 16 ∧ c.data = codeChunk msg (enc.idx.val % 2 ^ 16) ∧
      enc'.idx.val = (enc.idx.val + 1) % 2 ^ 32 ∧ EncInv msg enc' := by
  have hmax := usize_max_ge
  have hadm : ∀ pts, enc.s = .Points pts → ∀ (j : Nat), j < 16 →
      let len := (pts[j]!).value.length
      len = 0 ∨ len = 1 ∨ len = 3 ∨ len = 5 ∨ len = 30 ∨ len = 34 ∨ len = 36 := by
    intro pts hs j hj
    rcases hinv with ⟨pts', hs', hpts⟩ | ⟨polys, hs', _⟩
    · rw [hs] at hs'
      cases hs'
      simp only [(hpts j hj).1]
      omega
    · rw [hs] at hs'; cases hs'
  have hcb : ∀ polys, enc.s = .Polys polys → ∀ (j : Nat), j < 16 →
      (polys[j]!).coefficients.length + 1 ≤ Usize.max := by
    intro polys hs j hj
    rcases hinv with ⟨pts, hs', _⟩ | ⟨polys', hs', hpolys⟩
    · rw [hs] at hs'; cases hs'
    · rw [hs] at hs'
      cases hs'
      exact (hpolys j hj).2
  set i := UScalar.cast .U16 enc.idx with hi_def
  have hi : i.val = enc.idx.val % 2 ^ 16 := by
    rw [hi_def, UScalar.cast_val_eq]; rfl
  have hspec := PolyEncoder.chunk_at_spec enc i
    (by have := i.hBounds; simp only [UScalarTy.numBits] at this; omega) hadm hcb
  obtain ⟨⟨out, enc1⟩, hca⟩ := exists_ok_of_spec hspec
  have hpost := WP.post_of_ok hspec hca
  obtain ⟨hcidx, -, hidx1, hmatch⟩ := hpost
  have hnode : ∀ j, i.val < K → (codePoly msg j).eval i.val.toGF216 =
      (wordAt msg i.val j).toGF216 := by
    intro j hk
    have := codePoly_eval_node hKN msg j ⟨i.val, hk⟩
    rw [this, wordAt, dite_eq_left hk]
  have hwords : (∀ j < 16, chunkWord out.data.val j = (codeWord msg i.val j).toGF216) ∧
      EncInv msg enc1 := by
    simp only [codeWord, toGF216_gfToNat, chunkWord]
    rcases hinv with ⟨pts, hs, hpts⟩ | ⟨polys, hs, hpolys⟩
    · rw [hs] at hmatch
      simp only at hmatch
      rcases hmatch with ⟨rfl, hcache⟩ | ⟨polys', hs', hlag, hcoef, htrans⟩
      · refine ⟨fun j hj => ?_, Or.inl ⟨pts, hs, hpts⟩⟩
        obtain ⟨hlt, hw⟩ := hcache j hj
        rw [hw, (hpts j hj).2 _ (by rw [← (hpts j hj).1]; exact hlt),
          hnode j (by rw [← (hpts j hj).1]; exact hlt)]
      · have hpoly : ∀ j < 16, (polys'[j]!).toGF216Poly = codePoly msg j := by
          intro j hj
          rw [hlag j hj]
          have hlen : (alloc.vec.Vec.len (pts[j]!).value).val = K := by
            simp only [alloc.vec.Vec.len_val]; exact (hpts j hj).1
          rw [(hpts j hj).1]
          calc ∑ k ∈ Finset.range K, C ((pts[j]!).value[k]!).toGF216 *
                scaledLagrangeBasis (alloc.vec.Vec.len (pts[j]!).value) k
              = ∑ k ∈ Finset.range (alloc.vec.Vec.len (pts[j]!).value).val,
                  C (wordAt msg k j).toGF216 *
                    scaledLagrangeBasis (alloc.vec.Vec.len (pts[j]!).value) k := by
                rw [hlen]
                exact Finset.sum_congr rfl (fun k hk => by
                  rw [(hpts j hj).2 k (Finset.mem_range.mp hk)])
            _ = _ := sum_scaledLagrangeBasis_eq _ (by rw [hlen]; exact hKN) _
            _ = codePoly msg j := by rw [hlen]; rfl
        refine ⟨fun j hj => ?_, Or.inr ⟨polys', hs', fun j hj => ⟨hpoly j hj, hcoef j hj⟩⟩⟩
        rcases htrans j hj with ⟨hlt, hw⟩ | hw
        · rw [hw,
            (hpts j hj).2 _ (by rw [← (hpts j hj).1]; exact hlt),
            hnode j (by rw [← (hpts j hj).1]; exact hlt)]
        · rw [hw, hpoly j hj]
    · rw [hs] at hmatch
      simp only at hmatch
      obtain ⟨rfl, hw⟩ := hmatch
      refine ⟨fun j hj => ?_, Or.inr ⟨polys, hs, hpolys⟩⟩
      rw [hw j hj, (hpolys j hj).1]
  refine ⟨out, { enc1 with idx := core.num.U32.wrapping_add enc1.idx 1#u32 }, ?_, ?_, ?_, ?_,
    hwords.2⟩
  · simp only [next_chunk, lift, Std.bind_ok, ← hi_def, hca, uncurry_apply_pair]
  · rw [hcidx, hi]
  · rw [← hi]
    exact data_eq_chunkOfWords out.data _ (fun j _ => gfToNat_lt _) hwords.1
  · simp only [core.num.U32.wrapping_add_val_eq, hidx1, UScalar.size, UScalarTy.numBits]; rfl

end SpqrBridge.L2

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr

/-- For `K ∈ {3, 5, 30, 36}`, from an encoder holding `cd.ser p` at counter `n % 2^32`,
`next_chunk` emits `(ecp K _ _ cd).encode p n`, still holds `cd.ser p` and stores
`(n + 1) % 2^32`. -/
theorem next_chunk_wrap : ∀ {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16)
    (cd : L2.Codec M K) (p : M) (n : ℕ) (enc : encoding.polynomial.PolyEncoder),
    (K = 3 ∨ K = 5 ∨ K = 30 ∨ K = 36) → L2.EncInv (cd.ser p) enc → enc.idx.val = n % 2 ^ 32 →
      ∃ c enc', encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk enc =
          ok (c, enc') ∧
        (c.index.val, c.data) = (L2.ecp K hK hKN cd).encode p n ∧
        L2.EncInv (cd.ser p) enc' ∧ enc'.idx.val = (n + 1) % 2 ^ 32 := by
  intro M K hK hKN cd p n enc hKs hinv hn
  obtain ⟨c, enc', h, hidx, hdata, hidx', hinv'⟩ :=
    L2.next_chunk_inv_wrap hKN (by omega) (cd.ser p) enc hinv
  have h16 : enc.idx.val % 2 ^ 16 = n % 2 ^ 16 := by
    rw [hn, Nat.mod_mod_of_dvd _ (by norm_num)]
  refine ⟨c, enc', h, ?_, hinv', ?_⟩
  · simp only [ErasureCodePayload.encode, ErasureCodePayload.counterIndex, L2.ecp, L2.ec]
    rw [hidx, hdata, h16]
  · rw [hidx', hn, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

end SpqrBridge
