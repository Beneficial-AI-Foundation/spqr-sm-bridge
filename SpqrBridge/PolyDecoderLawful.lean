/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.DecodedMessage.DecodedMessage
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.AddChunk
import Spqr.Specs.Encoding.Polynomial.PolyDecoder.New
import SecureMessaging.ErasureCode.Streaming
import Mathlib.LinearAlgebra.Lagrange
import Spqr.Auxiliary.Aeneas.SpecImpExists

/-!
# The code's polynomial decoder meets secure-messaging's stream-decoder law

`PolyDecoder` (`src/encoding/polynomial.rs`, extracted by Aeneas) is wrapped as a
`StreamDecoder` of secure-messaging, and `Lawful` (law L2) is proved for it: adding an honestly
encoded chunk to an honest decoder keeps it honest, and the decoder then decodes nothing or the
payload.

The result is generic in the number `K` of points per polynomial slot. The payload has `32 K`
bytes and the decoder is `PolyDecoder::new(32 K)`. The four streams of ML-KEM Braid use
`K = 3` (header and MAC, 96 bytes), `36` (encapsulation key, 1152 bytes), `30` (ct1, 960 bytes)
and `5` (ct2 and MAC, 160 bytes).
-/

open Aeneas Aeneas.Std Polynomial spqr.encoding.polynomial spqr.encoding.gf

namespace SpqrBridge.L2

/-- `Nat.toGF216` is injective on `[0, 2^16)`. -/
theorem natToGF216_inj {a b : ℕ} (ha : a < 2 ^ 16) (hb : b < 2 ^ 16)
    (h : a.toGF216 = b.toGF216) : a = b := by
  open spqr.math.gf in
  unfold Nat.toGF216 at h
  by_contra hab
  set d := natToBinaryPoly a - natToBinaryPoly b with hd
  have hne : d ≠ 0 := fun h0 => hab (natToBinaryPoly_inj (sub_eq_zero.mp h0))
  have hcoeff_zero : ∀ m, 16 ≤ m → d.coeff m = 0 := by
    intro m hm
    have hpow : 2 ^ 16 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    rw [hd, Polynomial.coeff_sub, natToBinaryPoly_coeff, natToBinaryPoly_coeff,
      Nat.testBit_eq_false_of_lt (by omega), Nat.testBit_eq_false_of_lt (by omega)]
    simp
  have hnd : d.natDegree < 16 := by
    by_contra h_not
    push Not at h_not
    exact (Polynomial.leadingCoeff_ne_zero.mpr hne) (hcoeff_zero _ h_not)
  have hprime : Prime polyGF2 :=
    (UniqueFactorizationMonoid.irreducible_iff_prime).mp polyGF2_irreducible
  have hprime_ideal : (Ideal.span {polyGF2}).IsPrime :=
    (Ideal.span_singleton_prime polyGF2_monic.ne_zero).mpr hprime
  have hne_bot : Ideal.span ({polyGF2} : Set BinaryPoly) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact polyGF2_monic.ne_zero
  have hmax : (Ideal.span {polyGF2}).IsMaximal :=
    Ideal.IsPrime.isMaximal hprime_ideal hne_bot
  have hle : Ideal.span {polyGF2} ≤ RingHom.ker BinaryPoly.toGF216 :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr
      (RingHom.mem_ker.mpr BinaryPoly.toGF216_polyGF2))
  have hker_eq : RingHom.ker BinaryPoly.toGF216 = Ideal.span {polyGF2} := by
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact heq.symm
    · exact absurd (hmax.out.2 _ hlt) (RingHom.ker_ne_top BinaryPoly.toGF216)
  have hmem : polyGF2 ∣ d := by
    rw [← Ideal.mem_span_singleton, ← hker_eq, RingHom.mem_ker, hd, map_sub, h, sub_self]
  have := Polynomial.natDegree_le_of_dvd hmem hne
  rw [polyGF2_natDegree] at this
  omega

noncomputable instance : Fintype GF216 := Fintype.ofFinite _

theorem card_GF216 : Fintype.card GF216 = 2 ^ 16 := by
  rw [← Nat.card_eq_fintype_card]; exact GaloisField.card 2 16 (by norm_num)

/-- `Nat.toGF216` is a bijection from `Fin (2^16)` onto `GF216`. -/
theorem natToGF216_bij : Function.Bijective (fun n : Fin (2 ^ 16) => n.val.toGF216) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun a b h => Fin.ext (natToGF216_inj a.2 b.2 h), by simp [card_GF216]⟩

/-- The 16-bit word whose image in `GF216` is `g`. -/
noncomputable def gfToNat (g : GF216) : ℕ := ((Function.surjInv natToGF216_bij.2) g).val

theorem gfToNat_lt (g : GF216) : gfToNat g < 2 ^ 16 := ((Function.surjInv natToGF216_bij.2) g).2

theorem toGF216_gfToNat (g : GF216) : (gfToNat g).toGF216 = g :=
  Function.surjInv_eq natToGF216_bij.2 g

theorem pow_card_sub_two_eq_inv (a : GF216) : a ^ (2 ^ 16 - 2) = a⁻¹ := by
  by_cases ha : a = 0
  · subst ha; simp
  · have h1 := FiniteField.pow_card_sub_one_eq_one a ha
    rw [card_GF216] at h1
    refine (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ]
    exact h1


/-! ## The decoder's Lagrange interpolant -/

/-- Abscissa of the `j`-th point of `pts` in `GF216`. -/
noncomputable def xv (pts : List Pt) (j : ℕ) : GF216 := (pts[j]!).x.toGF216

/-- Ordinate of the `j`-th point of `pts` in `GF216`. -/
noncomputable def yv (pts : List Pt) (j : ℕ) : GF216 := (pts[j]!).y.toGF216

theorem get_eq_getElem! (pts : List Pt) (j : ℕ) (h : j < pts.length) :
    pts.get ⟨j, h⟩ = pts[j]! := by
  rw [List.get_eq_getElem, getElem!_pos pts j h]

theorem prodLinearFactors_eq (pts : List Pt) (a b : ℕ) (hb : b ≤ pts.length) :
    prodLinearFactors pts a b = ∏ j ∈ Finset.Ico a b, (X - C (xv pts j)) := by
  induction h : b - a generalizing a with
  | zero =>
    rw [prodLinearFactors_eq_one_of_not_lt _ _ _ (by omega)]
    rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]
  | succ k ih =>
    rw [prodLinearFactors, dite_eq_left ⟨by omega, by omega⟩,
      Finset.prod_eq_prod_Ico_succ_bot (by omega), ih (a + 1) (by omega),
      get_eq_getElem!, xv]

theorem lagrangeDenomProd_eq (px : GF16) (pts : List Pt) (a : ℕ) :
    lagrangeDenomProd px pts a = ∏ j ∈ Finset.Ico a pts.length,
      (if px.value = (pts[j]!).x.value then 1 else px.toGF216 - xv pts j) := by
  induction h : pts.length - a generalizing a with
  | zero =>
    rw [lagrangeDenomProd_eq_one_of_le _ _ _ (by omega)]
    rw [Finset.Ico_eq_empty (by omega), Finset.prod_empty]
  | succ k ih =>
    have ha : a < pts.length := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot ha, ← ih (a + 1) (by omega)]
    by_cases heq : px.value = (pts.get ⟨a, ha⟩).x.value
    · rw [lagrangeDenomProd_skip _ _ _ ha heq]
      rw [get_eq_getElem!] at heq
      rw [ite_eq_left heq, one_mul]
    · rw [lagrangeDenomProd_accum _ _ _ ha heq]
      rw [get_eq_getElem!] at heq
      rw [ite_eq_right heq, get_eq_getElem!, xv]

/-- Points with strictly increasing abscissae have pairwise distinct abscissae in `GF216`. -/
theorem xv_injOn (pts : List Pt) (hs : PolyDecoder.SlotSorted pts) :
    Set.InjOn (xv pts) ↑(Finset.range pts.length) := by
  intro i hi j hj hij
  simp only [Finset.coe_range, Set.mem_Iio] at hi hj
  have hval : (pts[i]!).x.value.val = (pts[j]!).x.value.val :=
    natToGF216_inj (by have := (pts[i]!).x.value.hBounds; scalar_tac)
      (by have := (pts[j]!).x.value.hBounds; scalar_tac) hij
  rw [PolyDecoder.SlotSorted, List.pairwise_iff_getElem] at hs
  rw [getElem!_pos pts i hi, getElem!_pos pts j hj] at hval
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd hval (Nat.ne_of_lt (hs i j hi hj hlt))
  · exact absurd hval (Nat.ne_of_gt (hs j i hj hi hlt))

theorem range_erase_eq (n i : ℕ) (hi : i < n) :
    (Finset.range n).erase i = Finset.Ico 0 i ∪ Finset.Ico (i + 1) n := by
  ext j; simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega

/-- One term of the decoder's interpolant is the Mathlib Lagrange term. -/
theorem lagrange_term_eq (pts : List Pt) (hs : PolyDecoder.SlotSorted pts) (i : ℕ)
    (hi : i < pts.length) :
    C (lagrangeScaleGF216 (pts.get ⟨i, hi⟩) pts) * lagrangeBasisPoly pts i =
      C (yv pts i) * Lagrange.basis (Finset.range pts.length) (xv pts) i := by
  have hinj := xv_injOn pts hs
  have hmem : i ∈ Finset.range pts.length := Finset.mem_range.mpr hi
  -- the basis polynomial
  have hB : lagrangeBasisPoly pts i =
      ∏ j ∈ (Finset.range pts.length).erase i, (X - C (xv pts j)) := by
    rw [lagrangeBasisPoly, ite_eq_left hi, prodLinearFactors_eq _ _ _ (by omega),
      prodLinearFactors_eq _ _ _ le_rfl, range_erase_eq _ _ hi,
      Finset.prod_union (Finset.disjoint_left.mpr (by
        intro j h1 h2; simp only [Finset.mem_Ico] at h1 h2; omega))]
  -- the denominator
  have hD : lagrangeDenomProd (pts.get ⟨i, hi⟩).x pts 0 =
      ∏ j ∈ (Finset.range pts.length).erase i, (xv pts i - xv pts j) := by
    rw [lagrangeDenomProd_eq, ← Finset.range_eq_Ico, ← Finset.mul_prod_erase _ _ hmem,
      get_eq_getElem!, ite_eq_left rfl, one_mul]
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hne : (pts[i]!).x.value ≠ (pts[j]!).x.value := by
      intro h
      apply hji
      apply hinj (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hj)) (Finset.mem_coe.mpr hmem)
      simp only [xv, GF16.toGF216, h]
    rw [ite_eq_right hne]; rfl
  rw [lagrangeScaleGF216, hD, hB, pow_card_sub_two_eq_inv, Lagrange.basis]
  simp only [Lagrange.basisDivisor, Finset.prod_mul_distrib, ← map_prod, Finset.prod_inv_distrib,
    map_mul, get_eq_getElem!, yv]
  ring

/-- The decoder's interpolant through all points of `pts` is Mathlib's Lagrange interpolant. -/
theorem lagrangeInterpolantSum_eq_interpolate (pts : List Pt) (hs : PolyDecoder.SlotSorted pts) :
    lagrangeInterpolantSum pts pts.length =
      Lagrange.interpolate (Finset.range pts.length) (xv pts) (yv pts) := by
  rw [lagrangeInterpolantSum_eq_finset_sum _ _ le_rfl, Lagrange.interpolate_apply]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [dite_eq_left hi', lagrange_term_eq pts hs i hi']

/-- If `pts` has strictly increasing abscissae and every point lies on `Q`, with
`deg Q < |pts|`, the decoder's interpolant through `pts` is `Q`. -/
theorem lagrangeInterpolantSum_eq_of_on (pts : List Pt) (hs : PolyDecoder.SlotSorted pts)
    (Q : GF216[X]) (hdeg : Q.degree < pts.length)
    (hon : ∀ pt ∈ pts, pt.y.toGF216 = Q.eval pt.x.toGF216) :
    lagrangeInterpolantSum pts pts.length = Q := by
  rw [lagrangeInterpolantSum_eq_interpolate pts hs]
  symm
  apply Lagrange.eq_interpolate_of_eval_eq _ (xv_injOn pts hs) (by simpa using hdeg)
  intro i hi
  have hi' := Finset.mem_range.mp hi
  rw [xv, yv, hon _ (by rw [getElem!_pos pts i hi']; exact List.getElem_mem hi')]

/-! ## The codeword and the erasure code

`K` is the number of points per polynomial slot: the payload has `32 * K` bytes, cut into `K`
chunks of 32 bytes. Word `j` of chunk `k` (bytes `2j`, `2j+1`) is the value at `x = k` of the
polynomial of slot `j`. -/

/-- The chunk payload of the code: 32 bytes. -/
abbrev Sym := Std.Array U8 32#usize

/-- Word `j` (big-endian bytes `2j`, `2j+1`) of a 32-byte chunk, as a natural number. -/
def word (c : Sym) (j : ℕ) : ℕ := 256 * (c.val[2 * j]!).val + (c.val[2 * j + 1]!).val

/-- The polynomial of slot `j` for a payload of `K` chunks: the interpolant of degree `< K`
through `(k, word j of chunk k)` for `k < K`. -/
noncomputable def codePoly {K : ℕ} (msg : Fin K → Sym) (j : ℕ) : GF216[X] :=
  Lagrange.interpolate Finset.univ (fun k : Fin K => k.val.toGF216)
    (fun k => (word (msg k) j).toGF216)

/-- The byte with value `n % 256`. -/
def byteOf (n : ℕ) : U8 := ⟨BitVec.ofNat 8 n⟩

theorem byteOf_val (n : ℕ) : (byteOf n).val = n % 256 := by
  simp [byteOf, UScalar.val]

/-- The 32-byte chunk whose word `j` is `w j` (taken modulo `2^16`). -/
def chunkOfWords (w : ℕ → ℕ) : Sym :=
  Array.make 32#usize (List.ofFn (fun b : Fin 32 =>
      if b.val % 2 = 0 then byteOf (w (b.val / 2) / 256) else byteOf (w (b.val / 2))))

theorem word_chunkOfWords (w : ℕ → ℕ) (j : ℕ) (hj : j < 16) (hw : w j < 2 ^ 16) :
    word (chunkOfWords w) j = w j := by
  simp only [word, chunkOfWords, Array.make_val]
  rw [getElem!_pos _ _ (by simp; omega), getElem!_pos _ _ (by simp; omega)]
  simp only [List.getElem_ofFn]
  rw [ite_eq_left (by omega), ite_eq_right (by omega), byteOf_val, byteOf_val]
  have h1 : (2 * j) / 2 = j := by omega
  have h2 : (2 * j + 1) / 2 = j := by omega
  rw [h1, h2]
  omega

/-- The 16-bit word encoding of a `GF216` value at index `idx` of slot `j`. -/
noncomputable def codeWord {K : ℕ} (msg : Fin K → Sym) (idx : ℕ) (j : ℕ) : ℕ :=
  gfToNat ((codePoly msg j).eval idx.toGF216)

/-- The chunk payload emitted at index `idx`: word `j` is slot `j`'s polynomial at `idx`. -/
noncomputable def codeChunk {K : ℕ} (msg : Fin K → Sym) (idx : ℕ) : Sym :=
  chunkOfWords (codeWord msg idx)

/-- The polynomial erasure code with `K` points per slot and `2^16` chunk indices. Its
set-based `decode` is unused here (the stream decoder is the code's `PolyDecoder`), so it is
the constant `none`. -/
noncomputable def ec (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16) : ErasureCode Sym where
  N := 2 ^ 16
  N_pos := by norm_num
  nchunk := K
  nchunk_pos := hK
  nchunk_le_N := hKN
  encode msg i := codeChunk msg i.val
  decode _ := none

/-- A payload type with a serialization to `K` chunks of 32 bytes. -/
structure Codec (M : Type) (K : ℕ) where
  /-- The serialized payload, as `K` chunks of 32 bytes. -/
  ser : M → Fin K → Sym
  /-- Parse `K` chunks of 32 bytes. -/
  parse : (Fin K → Sym) → Option M
  parse_ser : ∀ p, parse (ser p) = some p

/-- The erasure-coded payload scheme of one stream of the code. -/
noncomputable def ecp {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16) (cd : Codec M K) :
    ErasureCodePayload M Sym where
  ec := ec K hK hKN
  serialize := cd.ser
  parse := cd.parse
  parse_serialize := cd.parse_ser

/-! ## The code's decoder as a stream decoder -/

open spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder in
/-- The code chunk with index `n mod 2^16` and payload `data`. -/
def toChunk (n : ℕ) (data : Sym) : spqr.encoding.Chunk := ⟨⟨BitVec.ofNat 16 n⟩, data⟩

theorem usize_max_ge : 2 ^ 32 - 1 ≤ Usize.max := by
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp [U32.max, U64.max, U32.numBits, U64.numBits]

/-- The decoder state right after `PolyDecoder::new(32 * K)`. -/
def emptyDecoder (K : ℕ) (hK : 16 * K ≤ Usize.max) : PolyDecoder :=
  { pts_needed := UScalar.ofNatCore (16 * K) (by have := hK; have := Nat.two_pow_pos System.Platform.numBits; simp only [Usize.max, UScalarTy.numBits, Usize.numBits] at *; omega)
    pts := Array.make 16#usize (List.replicate 16 default)
    is_complete := false }

/-- Cut `32 * K` bytes into `K` chunks of 32 bytes. -/
def unflatten (K : ℕ) (v : List U8) : Fin K → Sym :=
  fun c => Array.make 32#usize (List.ofFn (fun b : Fin 32 => v[32 * c.val + b.val]!))

/-- The decoder invariant for payload chunks `msg`: it needs `16 K` points, its slots are
sorted sets, and every stored point of slot `s` lies on the polynomial of slot `s`. -/
def Inv {K : ℕ} (msg : Fin K → Sym) (d : PolyDecoder) : Prop :=
  d.pts_needed.val = 16 * K ∧ PolyDecoder.PointsValid d.pts ∧
    ∀ s < 16, ∀ pt ∈ (d.pts.val[s]!).val, pt.y.toGF216 = (codePoly msg s).eval pt.x.toGF216

open spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder in
/-- The code's `PolyDecoder` as a stream decoder. A failing `add_chunk` (a panic in Rust)
leaves the state unchanged and a failing or empty `decoded_message` gives `none`; neither
happens from honest states. -/
noncomputable def polyStreamDecoder {M : Type} (K : ℕ) (hKN : K ≤ 2 ^ 16)
    (cd : Codec M K) : ErasureCodePayload.Streaming.StreamDecoder M Sym where
  D := PolyDecoder
  empty := emptyDecoder K (by have := usize_max_ge; omega)
  addChunk d c := match (add_chunk d (toChunk c.1 c.2)).match with
    | .ok d' => d'
    | _ => d
  decodedPayload d := match (decoded_message d).match with
    | .ok (some v) => cd.parse (unflatten K v.val)
    | _ => none
  Honest d p := Inv (cd.ser p) d
  honest_empty p := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [emptyDecoder, UScalar.ofNatCore_val_eq]
    · apply PolyDecoder.PointsValid_of_forall_nil
      intro s hs
      simp only [emptyDecoder, Array.make_val, List.mem_replicate] at hs
      rw [hs.2]; rfl
    · intro s hs pt hpt
      simp only [emptyDecoder, Array.make_val] at hpt
      rw [getElem!_pos _ _ (by simp; omega), List.getElem_replicate] at hpt
      cases hpt

/-! ## `decoded_message` from an honest state returns the payload -/

open spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

theorem lookupY_some (l : List Pt) (x : ℕ) (y : GF16) (h : lookupY l x = some y) :
    ∃ pt ∈ l, pt.x.value.val = x ∧ pt.y = y := by
  induction l with
  | nil => simp [lookupY] at h
  | cons p rest ih =>
    simp only [lookupY] at h
    split at h
    · obtain ⟨pt, hpt, h1, h2⟩ := ih h
      exact ⟨pt, List.mem_cons_of_mem _ hpt, h1, h2⟩
    · split at h
      · simp only [Option.some.injEq] at h
        exact ⟨p, List.mem_cons_self, by omega, h⟩
      · cases h

theorem nodes_injOn (K : ℕ) (hKN : K ≤ 2 ^ 16) :
    Set.InjOn (fun k : Fin K => k.val.toGF216) ↑(Finset.univ : Finset (Fin K)) := by
  intro a _ b _ h
  exact Fin.ext (natToGF216_inj (by omega) (by omega) h)

/-- At node `k < K`, the polynomial of slot `j` is word `j` of chunk `k`. -/
theorem codePoly_eval_node {K : ℕ} (hKN : K ≤ 2 ^ 16) (msg : Fin K → Sym) (j : ℕ) (k : Fin K) :
    (codePoly msg j).eval k.val.toGF216 = (word (msg k) j).toGF216 := by
  rw [codePoly]
  exact Lagrange.eval_interpolate_at_node _ (nodes_injOn K hKN) (Finset.mem_univ k)

theorem codePoly_degree_lt {K : ℕ} (hKN : K ≤ 2 ^ 16) (msg : Fin K → Sym) (j : ℕ) :
    (codePoly msg j).degree < K := by
  have := Lagrange.degree_interpolate_lt (r := fun k : Fin K => (word (msg k) j).toGF216)
    (nodes_injOn K hKN)
  simpa [codePoly] using this

/-- In an honest state with enough points in every slot, `decoded_message` reconstructs word
`k % 16` of chunk `k / 16` at index `k`. -/
theorem decodedValue_eq {K : ℕ} (hKN : K ≤ 2 ^ 16) (msg : Fin K → Sym) (d : PolyDecoder)
    (hinv : Inv msg d) (hfull : ¬someIncomplete d.pts d.pts_needed 0 16) (k : ℕ)
    (hk : k < 16 * K) :
    decodedValue d.pts d.pts_needed k =
      (word (msg ⟨k / 16, by omega⟩) (k % 16)).toGF216 := by
  obtain ⟨hneed, hvalid, hon⟩ := hinv
  have hs16 : k % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have hx : k / 16 % 2 ^ 16 = k / 16 := Nat.mod_eq_of_lt (by omega)
  have h0 : 16 * K % 16 = 0 := by omega
  have h1 : 16 * K / 16 = K := by omega
  have hnode := codePoly_eval_node hKN msg (k % 16) ⟨k / 16, by omega⟩
  simp only at hnode
  have hslot : ∀ pt ∈ (d.pts.val[k % 16]'(by simp; omega)).val,
      pt.y.toGF216 = (codePoly msg (k % 16)).eval pt.x.toGF216 := by
    intro pt hpt
    apply hon _ hs16
    rwa [getElem!_pos _ _ (by simp; omega)]
  unfold decodedValue
  simp only [hx]
  split
  · rename_i y hy
    obtain ⟨pt, hpt, hptx, hpty⟩ := lookupY_some _ _ _ hy
    rw [← hpty, hslot pt hpt, GF16.toGF216, hptx, hnode]
  · have hnp : necessaryPoints d.pts_needed (k % 16) = K := by
      simp only [necessaryPoints, hneed, h0, h1, Nat.not_lt_zero, ite_false, add_zero]
    rw [hnp]
    set l := (d.pts.val[k % 16]'(by simp; omega)).val with hl
    have hlen : K ≤ l.length := by
      by_contra hlt
      apply hfull
      refine ⟨k % 16, hs16, Nat.zero_le _, hs16, ?_⟩
      simp only [hneed, h0, h1, Nat.not_lt_zero, ite_false, add_zero, alloc.vec.Vec.length]
      exact Nat.lt_of_not_le hlt
    have hsorted : PolyDecoder.SlotSorted (l.take K) :=
      List.Pairwise.sublist (List.take_sublist _ _) (hvalid.slot (k % 16) hs16)
    have htake_len : (l.take K).length = K := by simp; omega
    have heq := lagrangeInterpolantSum_eq_of_on (l.take K) hsorted (codePoly msg (k % 16))
      (by rw [htake_len]; exact codePoly_degree_lt hKN msg _)
      (fun pt hpt => hslot pt (List.mem_of_mem_take hpt))
    rw [htake_len] at heq
    rw [heq, hnode]

/-- If `decoded_message` returns bytes from an honest state, they are the payload. -/
theorem decoded_unflatten {K : ℕ} (hKN : K ≤ 2 ^ 16) (msg : Fin K → Sym) (d : PolyDecoder)
    (hinv : Inv msg d) (v : alloc.vec.Vec U8) (hd : decoded_message d = .ok (some v)) :
    unflatten K v.val = msg := by
  have hmax := usize_max_ge
  have hspec := WP.post_of_ok (decoded_message_spec d hinv.2.1 (by rw [hinv.1]; omega)) hd
  simp only at hspec
  obtain ⟨_, hfull, hlen, hbytes⟩ := hspec
  rw [hinv.1] at hlen
  simp only [alloc.vec.Vec.length] at hlen
  funext c
  apply Aeneas.Std.Array.ext
  simp only [unflatten, Array.make_val]
  apply List.ext_getElem (by simp)
  intro b hb1 hb2
  simp only [List.length_ofFn] at hb1
  rw [List.getElem_ofFn, ← getElem!_pos (msg c).val b hb2]
  simp only
  -- the word index of byte `32 c + b`
  have hc := c.2
  set k := 16 * c.val + b / 2 with hk
  have hk0 : 2 * k < v.val.length := by omega
  have hk1 : 2 * k + 1 < v.val.length := by omega
  have hw := hbytes k (v.val[2 * k]!) (v.val[2 * k + 1]!)
    (by rw [getElem!_pos v.val _ hk0]; exact List.getElem?_eq_getElem hk0)
    (by rw [getElem!_pos v.val _ hk1]; exact List.getElem?_eq_getElem hk1)
  rw [zero_add, decodedValue_eq hKN msg d hinv hfull k (by omega)] at hw
  have hkc : (⟨k / 16, by omega⟩ : Fin K) = c := Fin.ext (by simp only; omega)
  have hkm : k % 16 = b / 2 := by omega
  rw [hkc, hkm] at hw
  have hb := (v.val[2 * k]!).hBounds
  have hb' := (v.val[2 * k + 1]!).hBounds
  have hm1 := ((msg c).val[2 * (b / 2)]!).hBounds
  have hm2 := ((msg c).val[2 * (b / 2) + 1]!).hBounds
  simp only [UScalarTy.numBits] at hb hb' hm1 hm2
  have hw' := natToGF216_inj (by omega) (by simp only [word]; omega) hw
  simp only [word] at hw'
  have hd1 : (v.val[2 * k]!).val = ((msg c).val[2 * (b / 2)]!).val := by omega
  have hd2 : (v.val[2 * k + 1]!).val = ((msg c).val[2 * (b / 2) + 1]!).val := by omega
  rcases Nat.even_or_odd b with ⟨r, hr⟩ | ⟨r, hr⟩
  · have e1 : 32 * c.val + b = 2 * k := by omega
    have e2 : 2 * (b / 2) = b := by omega
    rw [e1]
    rw [e2] at hd1
    exact UScalar.eq_of_val_eq hd1
  · have e1 : 32 * c.val + b = 2 * k + 1 := by omega
    have e2 : 2 * (b / 2) + 1 = b := by omega
    rw [e1]
    rw [e2] at hd2
    exact UScalar.eq_of_val_eq hd2

/-! ## `add_chunk` of an honest chunk keeps the state honest -/

/-- A slot with strictly increasing 16-bit abscissae has at most `2^16` points. -/
theorem slotSorted_length_le (l : List Pt) (hs : PolyDecoder.SlotSorted l) :
    l.length ≤ 2 ^ 16 := by
  let f : Pt → Fin (2 ^ 16) := fun p =>
    ⟨p.x.value.val, by have := p.x.value.hBounds; simp only [UScalarTy.numBits] at this; omega⟩
  have hnd : (l.map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine hs.imp (fun {a b} h e => ?_)
    have := congrArg Fin.val e
    simp only [f] at this
    omega
  have := hnd.length_le_card
  simpa using this

theorem mem_of_isSortedPushResult {old new_ : List Pt} {p x : Pt}
    (h : IsSortedPushResult old new_ p) (hx : x ∈ new_) : x ∈ old ∨ x = p := by
  obtain ⟨j, _, h | ⟨_, h⟩⟩ := h <;> subst h <;>
    simp only [List.mem_append, List.mem_singleton] at hx <;>
    rcases hx with (hx | hx) | hx
  · exact Or.inl (List.mem_of_mem_take hx)
  · exact Or.inr hx
  · exact Or.inl (List.mem_of_mem_drop hx)
  · exact Or.inl (List.mem_of_mem_take hx)
  · exact Or.inr hx
  · exact Or.inl (List.mem_of_mem_drop hx)

theorem ite_imp_or {c : Prop} [Decidable c] {A B : Prop} (h : if c then A else B) : A ∨ B := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h; exact Or.inl h
  · rw [ite_eq_right hc] at h; exact Or.inr h

theorem toChunk_index_val (n : ℕ) (hn : n < 2 ^ 16) (data : Sym) :
    (toChunk n data).index.val = n := by
  simp only [toChunk, UScalar.val]
  exact Nat.mod_eq_of_lt hn

/-- Adding the chunk of `msg` at index `n < 2^16` to an honest state gives an honest state. -/
theorem add_chunk_inv {K : ℕ} (msg : Fin K → Sym) (d : PolyDecoder) (hinv : Inv msg d)
    (n : ℕ) (hn : n < 2 ^ 16) (d' : PolyDecoder)
    (h : add_chunk d (toChunk n (codeChunk msg n)) = .ok d') : Inv msg d' := by
  have hmax := usize_max_ge
  obtain ⟨hneed, hvalid, hon⟩ := hinv
  have hidx := toChunk_index_val n hn (codeChunk msg n)
  have hcap : ∀ k, k < 16 → (d.pts[k]!).length + 17 ≤ Usize.max := by
    intro k hk
    have := slotSorted_length_le _ (hvalid.slot! k hk)
    simp only [Array.getElem!_Nat_eq, alloc.vec.Vec.length]
    omega
  have hover : (toChunk n (codeChunk msg n)).index * 16 + 16 ≤ Usize.max := by
    rw [hidx]; omega
  have hspec := WP.post_of_ok (add_chunk_spec d _ hover hcap) h
  have hvalid' := WP.post_of_ok (add_chunk_spec_valid d _ hover hcap hvalid) h
  obtain ⟨hneed', _, selfs, h0, h16, hstep⟩ := hspec
  refine ⟨by rw [hneed', hneed], hvalid', ?_⟩
  -- every intermediate state stores only points on the slot polynomials
  have hall : ∀ m, m ≤ 16 → ∀ s < 16, ∀ pt ∈ ((selfs m).pts.val[s]!).val,
      pt.y.toGF216 = (codePoly msg s).eval pt.x.toGF216 := by
    intro m
    induction m with
    | zero => intro _; rw [h0]; exact hon
    | succ m ih =>
      intro hm s hs pt hpt
      obtain ⟨_, _, _, hpidx, p, hpx, hpy, hpush⟩ := hstep m (by omega)
      simp only [hidx] at hpidx hpx hpush
      have hpoly : (n * 16 + m) % 16 = m := by omega
      simp only [hpoly] at hpush
      -- the pushed point lies on the polynomial of slot `m`
      have hp : p.y.toGF216 = (codePoly msg m).eval p.x.toGF216 := by
        have hw := word_chunkOfWords (codeWord msg n) m (by omega) (gfToNat_lt _)
        simp only [word, toChunk, codeChunk, Array.getElem!_Nat_eq] at hpy hw
        rw [GF16.toGF216, GF16.toGF216, hpy, hpx, hpidx, show m * 2 = 2 * m by ring]
        rw [show (chunkOfWords (codeWord msg n)).val[2 * m]!.val * 256 +
            (chunkOfWords (codeWord msg n)).val[2 * m + 1]!.val = codeWord msg n m by omega]
        exact toGF216_gfToNat _
      rcases ite_imp_or hpush with ⟨hother, hres⟩ | hpush
      · by_cases hsm : s = m
        · subst hsm
          rcases mem_of_isSortedPushResult hres hpt with hold | rfl
          · exact ih (by omega) s hs pt hold
          · exact hp
        · have := hother s hsm
          rw [Array.getElem!_Nat_eq] at this
          rw [this] at hpt
          exact ih (by omega) s hs pt hpt
      · rw [hpush] at hpt
        exact ih (by omega) s hs pt hpt
  rw [← h16]
  exact hall 16 le_rfl

/-! ## Law L2 -/

/-- From an honest state the wrapped decoder decodes nothing or the payload. -/
theorem decodedPayload_honest {M : Type} (K : ℕ) (hKN : K ≤ 2 ^ 16) (cd : Codec M K)
    (d : PolyDecoder) (p : M) (hd : Inv (cd.ser p) d) :
    (polyStreamDecoder K hKN cd).decodedPayload d = none ∨
      (polyStreamDecoder K hKN cd).decodedPayload d = some p := by
  simp only [polyStreamDecoder]
  rcases hm : (decoded_message d).match with v | _ | _
  · rcases v with _ | v
    · exact Or.inl rfl
    · right
      show cd.parse (unflatten K v.val) = some p
      rw [decoded_unflatten hKN (cd.ser p) d hd v (Result.match.isOk.mp hm), cd.parse_ser]
  · exact Or.inl rfl
  · exact Or.inl rfl

/-- **Law L2 for the code's decoder.** Adding a chunk that the polynomial code emits for `p` at
any counter to a `PolyDecoder` that holds only points of `p` keeps it so, and the decoder then
decodes nothing or `p`. -/
theorem polyStreamDecoder_lawful {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16)
    (cd : Codec M K) :
    (polyStreamDecoder K hKN cd).Lawful (ecp K hK hKN cd) where
  honest_addChunk d p i hd := by
    have hhon : (polyStreamDecoder K hKN cd).Honest
        ((polyStreamDecoder K hKN cd).addChunk d ((ecp K hK hKN cd).encode p i)) p := by
      simp only [polyStreamDecoder, ErasureCodePayload.encode, ErasureCodePayload.counterIndex,
        ecp, ec]
      rcases hm : (add_chunk d (toChunk (i % 2 ^ 16) (codeChunk (cd.ser p) (i % 2 ^ 16)))).match
        with d' | _ | _
      · exact add_chunk_inv (cd.ser p) d hd (i % 2 ^ 16) (Nat.mod_lt _ (by norm_num)) d'
          (Result.match.isOk.mp hm)
      · exact hd
      · exact hd
    exact ⟨hhon, decodedPayload_honest K hKN cd _ p hhon⟩

end SpqrBridge.L2

#print axioms SpqrBridge.L2.polyStreamDecoder_lawful
