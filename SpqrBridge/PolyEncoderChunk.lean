/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.PolyDecoderLawful
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.EncodeBytes
import Spqr.Specs.Encoding.Polynomial.PolyEncoder.NextChunk
import Spqr.Specs.Encoding.Gf.GF16.ONE
import Spqr.Math.Poly.Coeff.Basic

/-!
# The code's polynomial encoder emits the chunks of `ecp`

`PolyEncoder::encode_bytes` over the `32 K` payload bytes, followed by `next_chunk`, emits at
counter `i < 2^16` the chunk `(i, codeChunk msg i)`, which is `(ecp K _ _ cd).encode p i` for
`msg = cd.ser p`. The spec of `next_chunk` in `Spqr` assumes the counter fits in `u16`, so the
counters `i ≥ 2^16` (where the code truncates `idx as u16`) are not covered.
-/

open Aeneas Aeneas.Std Polynomial spqr.encoding.polynomial spqr.encoding.gf
open spqr.encoding.polynomial.PolyConst.lagrange_interpolate_pt_loop

namespace SpqrBridge.L2

/-! ## The encoder's scaled Lagrange basis is Mathlib's Lagrange basis -/

theorem condProdLinearFactors_eq (px : GF16) (pts : List Pt) (a : ℕ) :
    condProdLinearFactors px pts a = ∏ j ∈ Finset.Ico a pts.length,
      (if px.value = (pts[j]!).x.value then 1 else X - C (xv pts j)) := by
  induction h : pts.length - a generalizing a with
  | zero =>
    rw [condProdLinearFactors_ge _ _ _ (by omega)]
    rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]
  | succ k ih =>
    have ha : a < pts.length := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot ha, ← ih (a + 1) (by omega)]
    by_cases heq : px.value = pts[a].x.value
    · rw [condProdLinearFactors_skip _ _ _ ha heq]
      rw [← getElem!_pos pts a ha] at heq
      rw [ite_eq_left heq, one_mul]
    · rw [condProdLinearFactors_accum _ _ _ ha heq]
      rw [← getElem!_pos pts a ha] at heq
      rw [ite_eq_right heq, xv, getElem!_pos pts a ha]

/-- For points with distinct abscissae, the conditional product is the basis polynomial. -/
theorem condProdLinearFactors_eq_basis (pts : List Pt) (hs : PolyDecoder.SlotSorted pts)
    (i : ℕ) (hi : i < pts.length) :
    condProdLinearFactors (pts[i]!).x pts 0 = lagrangeBasisPoly pts i := by
  have hinj := xv_injOn pts hs
  have hmem : i ∈ Finset.range pts.length := Finset.mem_range.mpr hi
  rw [condProdLinearFactors_eq, ← Finset.range_eq_Ico, ← Finset.mul_prod_erase _ _ hmem,
    ite_eq_left rfl, one_mul, lagrangeBasisPoly, ite_eq_left hi,
    prodLinearFactors_eq _ _ _ (by omega), prodLinearFactors_eq _ _ _ le_rfl,
    ← Finset.prod_union (Finset.disjoint_left.mpr (by
        intro j h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega)), ← range_erase_eq _ _ hi]
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := Finset.ne_of_mem_erase hj
  have hne : (pts[i]!).x.value ≠ (pts[j]!).x.value := by
    intro h
    apply hji
    apply hinj (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hj)) (Finset.mem_coe.mpr hmem)
    simp only [xv, GF16.toGF216, h]
  rw [ite_eq_right hne]

theorem completePoints_getElem! (N : Usize) (j : ℕ) (hj : j < N.val) :
    (completePoints N).val[j]! = ⟨⟨⟨BitVec.ofNat 16 j⟩⟩, GF16.ONE⟩ := by
  rw [completePoints, Array.from_val, getElem!_pos _ _ (by simp; omega)]
  simp

theorem completePoints_length (N : Usize) : (completePoints N).val.length = N.val := by
  simp

theorem bv16_toNat (j : ℕ) (hj : j < 2 ^ 16) : (BitVec.ofNat 16 j).toNat = j := by
  rw [BitVec.toNat_ofNat]; omega

theorem xv_completePoints (N : Usize) (hN : N.val ≤ 2 ^ 16) (j : ℕ) (hj : j < N.val) :
    xv (completePoints N).val j = j.toGF216 := by
  rw [xv, completePoints_getElem! N j hj, GF16.toGF216]
  simp only [UScalar.val]
  rw [bv16_toNat j (by omega)]

theorem completePoints_sorted (N : Usize) (hN : N.val ≤ 2 ^ 16) :
    PolyDecoder.SlotSorted (completePoints N).val := by
  rw [PolyDecoder.SlotSorted, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [completePoints_length] at hi hj
  rw [← getElem!_pos _ i (by rw [completePoints_length]; exact hi),
    ← getElem!_pos _ j (by rw [completePoints_length]; exact hj),
    completePoints_getElem! N i hi, completePoints_getElem! N j hj]
  simp only [UScalar.val]
  rw [bv16_toNat i (by omega), bv16_toNat j (by omega)]
  exact hij

/-- The encoder's scaled Lagrange basis over the nodes `0, …, N-1` is Mathlib's. -/
theorem scaledLagrangeBasis_eq (N : Usize) (hN : N.val ≤ 2 ^ 16) (k : ℕ) (hk : k < N.val) :
    scaledLagrangeBasis N k =
      Lagrange.basis (Finset.range N.val) (fun j : ℕ => j.toGF216) k := by
  set cp := (completePoints N).val with hcp
  have hlen : cp.length = N.val := completePoints_length N
  have htake : cp.take N.val = cp := List.take_of_length_le (by omega)
  have hs : PolyDecoder.SlotSorted cp := completePoints_sorted N hN
  have hterm := lagrange_term_eq cp hs k (by omega)
  rw [get_eq_getElem!, ← condProdLinearFactors_eq_basis cp hs k (by omega)] at hterm
  rw [scaledLagrangeBasis, Array.getElem!_Nat_eq, ← hcp, htake]
  have hy : (cp[k]!).y.toGF216 = 1 := by
    rw [hcp, completePoints_getElem! N k hk]; exact GF16.ONE_toGF216
  have hyv : yv cp k = 1 := hy
  rw [lagrangeScaleGF216] at hterm
  rw [hterm, hyv, map_one, one_mul, hlen]
  unfold Lagrange.basis
  apply Finset.prod_congr rfl
  intro j hj
  rw [xv_completePoints N hN k hk,
    xv_completePoints N hN j (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))]

/-- The encoder's interpolant through `(k, y k)` for `k < N` is Mathlib's interpolant. -/
theorem sum_scaledLagrangeBasis_eq (N : Usize) (hN : N.val ≤ 2 ^ 16) (y : ℕ → GF216) :
    ∑ k ∈ Finset.range N.val, C (y k) * scaledLagrangeBasis N k =
      Lagrange.interpolate (Finset.range N.val) (fun j : ℕ => j.toGF216) y := by
  rw [Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [scaledLagrangeBasis_eq N hN k (Finset.mem_range.mp hk)]

/-! ## Chunk payloads from their words -/

open spqr.encoding.polynomial.PolyEncoder in
/-- A 32-byte chunk is determined by its 16 words. -/
theorem data_eq_chunkOfWords (data : Sym) (w : ℕ → ℕ) (hw : ∀ j < 16, w j < 2 ^ 16)
    (h : ∀ j < 16, chunkWord data.val j = (w j).toGF216) : data = chunkOfWords w := by
  apply Aeneas.Std.Array.ext
  simp only [chunkOfWords, Array.make_val]
  apply List.ext_getElem (by simp)
  intro b hb1 hb2
  simp only [List.length_ofFn] at hb2
  rw [List.getElem_ofFn]
  have hj : b / 2 < 16 := by omega
  have hb := (data.val[2 * (b / 2)]!).hBounds
  have hb' := (data.val[2 * (b / 2) + 1]!).hBounds
  simp only [UScalarTy.numBits] at hb hb'
  have hwj := hw _ hj
  have heq := natToGF216_inj (by omega) hwj (h _ hj)
  rw [← getElem!_pos data.val b hb1]
  apply UScalar.eq_of_val_eq
  dsimp only
  by_cases hbe : b % 2 = 0
  · have e : 2 * (b / 2) = b := by omega
    rw [e] at heq hb hb'
    rw [ite_eq_left hbe, byteOf_val]; omega
  · have e : 2 * (b / 2) + 1 = b := by omega
    rw [e] at heq hb'
    rw [ite_eq_right hbe, byteOf_val]; omega

/-! ## The encoder invariant -/

/-- The `32 K` bytes of a payload of `K` chunks. -/
def flatten {K : ℕ} (msg : Fin K → Sym) : List U8 :=
  List.ofFn (fun t : Fin (32 * K) => (msg ⟨t.val / 32, by omega⟩).val[t.val % 32]!)

theorem flatten_length {K : ℕ} (msg : Fin K → Sym) : (flatten msg).length = 32 * K := by
  simp [flatten]

/-- The encoder holds the payload `msg`: either the `K` points of each slot are the payload
words (before the first interpolation), or each slot's polynomial is the slot polynomial. -/
def EncInv {K : ℕ} (msg : Fin K → Sym) (enc : PolyEncoder) : Prop :=
  (∃ pts, enc.s = .Points pts ∧ ∀ j, j < 16 → (pts[j]!).value.length = K ∧
      ∀ k, k < K → ((pts[j]!).value[k]!).toGF216 = (wordAt msg k j).toGF216) ∨
  (∃ polys, enc.s = .Polys polys ∧ ∀ j, j < 16 → (polys[j]!).toGF216Poly = codePoly msg j ∧
      (polys[j]!).coefficients.length + 1 ≤ Usize.max)

open spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder in
/-- `encode_bytes` over the payload bytes gives an encoder at counter `0` holding the payload. -/
theorem encode_bytes_inv {K : ℕ} (hK : K ≤ 2 ^ 15) (msg : Fin K → Sym)
    (hlen : (flatten msg).length ≤ Usize.max) (enc : PolyEncoder)
    (h : encode_bytes (Slice.from (flatten msg) hlen) = .ok (.Ok enc)) :
    enc.idx.val = 0 ∧ EncInv msg enc := by
  have hfl := flatten_length msg
  have hspec := WP.post_of_ok (encode_bytes_spec (Slice.from (flatten msg) hlen)
    (by simp [Slice.from_val, hfl]; omega) (by simp [Slice.from_val, hfl]; omega)) h
  obtain ⟨idx, st⟩ := enc
  rcases st with pts | polys
  · simp only [Slice.length, Slice.from_val, hfl] at hspec
    obtain ⟨hidx, hlens, hcoeff⟩ := hspec
    refine ⟨by rw [hidx]; rfl, Or.inl ⟨pts, rfl, fun j hj => ?_⟩⟩
    have hl : (pts[j]!).value.length = K := by
      rw [hlens j hj]; split <;> omega
    refine ⟨hl, fun k hk => ?_⟩
    obtain ⟨_, hc⟩ := hcoeff j hj k (by omega)
    rw [listToGF216Poly_coeff, dite_eq_left (by simp only [alloc.vec.Vec.length] at hl; omega)]
      at hc
    rw [List.get_eq_getElem, ← getElem!_pos _ k (by simp only [alloc.vec.Vec.length] at hl; omega)] at hc
    rw [alloc.vec.Vec.getElem!_Nat_eq, hc, wordAt, dite_eq_left hk, word]
    simp only [Slice.getElem!_Nat_eq, Slice.from_val, flatten]
    rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)]
    simp only [List.getElem_ofFn]
    have e1 : 2 * (j + 16 * k) / 32 = k := by omega
    have e2 : 2 * (j + 16 * k) % 32 = 2 * j := by omega
    have e3 : (2 * (j + 16 * k) + 1) / 32 = k := by omega
    have e4 : (2 * (j + 16 * k) + 1) % 32 = 2 * j + 1 := by omega
    simp only [e1, e2, e3, e4]
  · simp at hspec

open spqr.encoding.polynomial.PolyEncoder spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder in
/-- From an encoder holding `msg` at counter `idx < 2^16`, `next_chunk` emits the chunk
`(idx, codeChunk msg idx)`, advances the counter and still holds `msg`. -/
theorem next_chunk_inv {K : ℕ} (hKN : K ≤ 2 ^ 16)
    (hKadm : K = 1 ∨ K = 3 ∨ K = 5 ∨ K = 30 ∨ K = 34 ∨ K = 36)
    (msg : Fin K → Sym) (enc : PolyEncoder) (hinv : EncInv msg enc)
    (hidx : enc.idx.val < 2 ^ 16) (c : spqr.encoding.Chunk) (enc' : PolyEncoder)
    (h : next_chunk enc = .ok (c, enc')) :
    c.index.val = enc.idx.val ∧ c.data = codeChunk msg enc.idx.val ∧
      enc'.idx.val = enc.idx.val + 1 ∧ EncInv msg enc' := by
  have hmax := usize_max_ge
  have hfits : enc.idx.val ≤ U16.max := by
    simp only [U16.max, U16.numBits, UScalarTy.numBits]; omega
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
  have hpost := WP.post_of_ok (next_chunk_spec enc hfits hadm hcb) h
  obtain ⟨hcidx, _, hidx', hmatch⟩ := hpost
  have hidx'' : enc'.idx.val = enc.idx.val + 1 := by
    rw [hidx']; exact Nat.mod_eq_of_lt (by simp only [U32.size, U32.numBits, UScalarTy.numBits]; omega)
  -- each chunk word is the slot polynomial at `idx`
  suffices hwords : (∀ j < 16, chunkWord c.data.val j =
      (codeWord msg enc.idx.val j).toGF216) ∧ EncInv msg enc' by
    refine ⟨hcidx, ?_, hidx'', hwords.2⟩
    exact data_eq_chunkOfWords c.data _ (fun j _ => gfToNat_lt _) hwords.1
  have hnode : ∀ j, enc.idx.val < K → (codePoly msg j).eval enc.idx.val.toGF216 =
      (wordAt msg enc.idx.val j).toGF216 := by
    intro j hk
    have := codePoly_eval_node hKN msg j ⟨enc.idx.val, hk⟩
    rw [this, wordAt, dite_eq_left hk]
  simp only [codeWord, toGF216_gfToNat]
  rcases hinv with ⟨pts, hs, hpts⟩ | ⟨polys, hs, hpolys⟩
  · rw [hs] at hmatch
    simp only at hmatch
    rcases hmatch with ⟨hs', hcache⟩ | ⟨polys', hs', hlag, hcoef, htrans⟩
    · refine ⟨fun j hj => ?_, Or.inl ⟨pts, hs', hpts⟩⟩
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
    obtain ⟨hs', hw⟩ := hmatch
    refine ⟨fun j hj => ?_, Or.inr ⟨polys, hs', hpolys⟩⟩
    rw [hw j hj, (hpolys j hj).1]

open spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder in
/-- **The code's encoder emits the chunks of `ecp`.** From an encoder holding `cd.ser p` at
counter `i < 2^16`, `next_chunk` emits `(ecp K _ _ cd).encode p i` (as `(index, data)`). -/
theorem next_chunk_eq_encode {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16)
    (hKadm : K = 1 ∨ K = 3 ∨ K = 5 ∨ K = 30 ∨ K = 34 ∨ K = 36) (cd : Codec M K) (p : M)
    (enc : PolyEncoder) (hinv : EncInv (cd.ser p) enc) (hidx : enc.idx.val < 2 ^ 16)
    (c : spqr.encoding.Chunk) (enc' : PolyEncoder) (h : next_chunk enc = .ok (c, enc')) :
    (c.index.val, c.data) = (ecp K hK hKN cd).encode p enc.idx.val ∧
      enc'.idx.val = enc.idx.val + 1 ∧ EncInv (cd.ser p) enc' := by
  obtain ⟨h1, h2, h3, h4⟩ := next_chunk_inv hKN hKadm (cd.ser p) enc hinv hidx c enc' h
  refine ⟨?_, h3, h4⟩
  simp only [ErasureCodePayload.encode, ErasureCodePayload.counterIndex, ecp, ec]
  rw [h1, h2, Nat.mod_eq_of_lt hidx]

end SpqrBridge.L2

#print axioms SpqrBridge.L2.encode_bytes_inv
#print axioms SpqrBridge.L2.next_chunk_eq_encode
