/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.ChunkedRel
import Spqr.Specs.IncrementalMlkem768.Decaps

/-!
# Facts about `codePrims` for the `Braid` → `Chunked` relation

`codePrims` reads each primitive with `pick`, so its value is the code's own wherever the code
succeeds. This file proves the instances that the arms of W2 use: the sizes, the lengths of
`KDF_OK`, `KDF_AUTH`, `ToBytes`, `MAC` and `Decaps`, and one decoder step (`decStep`), which runs
`add_chunk` and `decoded_message` on a well-formed decoder and relates the result to
`polyStreamDecoder`.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming
open spqr.encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder

/-! ## `pick` -/

/-- `pick p` satisfies `p` when some value does. -/
theorem pick_spec {β : Type} [Nonempty β] {p : β → Prop} (h : ∃ b, p b) : p (pick p) := by
  simp only [pick, h, _root_.dite_true]
  exact Classical.choose_spec h

/-- `pick p` is the only value that satisfies `p`. -/
theorem pick_eq_of {β : Type} [Nonempty β] {p : β → Prop} {b : β} (hb : p b)
    (hu : ∀ b', p b' → b' = b) : pick p = b :=
  hu _ (pick_spec ⟨b, hb⟩)

theorem ok_inj {α : Type} {m : Result α} {a b : α} (ha : m = ok a) (hb : m = ok b) : a = b := by
  rw [ha, Result.ok.injEq] at hb; exact hb

/-! ## Decoders -/

theorem codePrims_addChunk {d d' : encoding.polynomial.PolyDecoder} {c : encoding.Chunk}
    (h : add_chunk d c = ok d') : codePrims.addChunk d c = d' :=
  pick_eq_of h fun _ h' => ok_inj h' h

theorem codePrims_message {d : encoding.polynomial.PolyDecoder}
    {m : Option (alloc.vec.Vec Std.U8)} (h : decoded_message d = ok m) :
    codePrims.message d = m.map (·.val) :=
  pick_eq_of ⟨m, h, rfl⟩ fun _ ⟨m', h', e⟩ => by rw [e, ok_inj h' h]

/-- The code chunk of a secure-messaging chunk read from a code chunk is that chunk. -/
theorem toChunk_chunkOfCode (c : encoding.Chunk) :
    L2.toChunk (chunkOfCode c).1 (chunkOfCode c).2 = c := by
  obtain ⟨i, data⟩ := c
  simp only [L2.toChunk, chunkOfCode, encoding.Chunk.mk.injEq, and_true]
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val]
  exact Nat.mod_eq_of_lt i.hBounds

/-- One decoder step on a well-formed decoder: `add_chunk` succeeds, the result is
well-formed, and `decoded_message` succeeds on it. Both `codePrims` and `polyStreamDecoder`
then return the code's values. -/
theorem decStep {M : Type} (K : ℕ) (hKN : K ≤ 2 ^ 16) (cd : L2.Codec M K)
    (d : encoding.polynomial.PolyDecoder) (hwf : DecWF K d) (c : encoding.Chunk) :
    ∃ d', add_chunk d c = ok d' ∧ codePrims.addChunk d c = d' ∧
      (L2.polyStreamDecoder K hKN cd).addChunk d (chunkOfCode c) = d' ∧ DecWF K d' ∧
      ∃ r, decoded_message d' = ok r ∧ codePrims.message d' = r.map (·.val) ∧
        (L2.polyStreamDecoder K hKN cd).decodedPayload d' =
          r.bind (fun v => cd.parse (L2.unflatten K v.val)) ∧
        ∀ v ∈ r, v.val.length = 32 * K := by
  have hmax := L2.usize_max_ge
  have hcap : ∀ k, k < 16 → (d.pts[k]!).length + 17 ≤ Usize.max := by
    intro k hk
    have := L2.slotSorted_length_le _ (hwf.2.slot! k hk)
    simp only [Array.getElem!_Nat_eq, alloc.vec.Vec.length]
    omega
  have hidx : c.index.val < 2 ^ 16 := c.index.hBounds
  have hover : c.index * 16 + 16 ≤ Usize.max := by omega
  obtain ⟨d', hd', hpost⟩ := WP.spec_imp_exists (add_chunk_spec d c hover hcap)
  have hvalid' := WP.post_of_ok (add_chunk_spec_valid d c hover hcap hwf.2) hd'
  have hneed' : d'.pts_needed.val = 16 * K := by rw [hpost.1, hwf.1]
  obtain ⟨r, hr, hrpost⟩ := WP.spec_imp_exists
    (decoded_message_spec d' hvalid' (by rw [hneed']; omega))
  refine ⟨d', hd', codePrims_addChunk hd', ?_, ⟨hneed', hvalid'⟩, r, hr, codePrims_message hr,
    ?_, ?_⟩
  · simp only [L2.polyStreamDecoder, toChunk_chunkOfCode, hd']
    rfl
  · simp only [L2.polyStreamDecoder, hr]
    rcases r with _ | v <;> rfl
  · intro v hv
    cases hv
    have h2 := hrpost.2.2.1
    simp only [alloc.vec.Vec.length] at h2
    rw [h2, hneed']
    ring

/-- The empty decoder of `polyStreamDecoder` is well-formed. -/
theorem decWF_empty {M : Type} (K : ℕ) (hKN : K ≤ 2 ^ 16) (cd : L2.Codec M K) :
    DecWF K (L2.polyStreamDecoder K hKN cd).empty := by
  refine ⟨?_, ?_⟩
  · simp only [L2.polyStreamDecoder, L2.emptyDecoder, UScalar.ofNatCore_val_eq]
  · apply encoding.polynomial.PolyDecoder.PointsValid_of_forall_nil
    intro s hs
    simp only [L2.polyStreamDecoder, L2.emptyDecoder, Array.make_val, List.mem_replicate] at hs
    rw [hs.2]; rfl

/-! ## Sizes -/

theorem codePrims_headerSize : codePrims.headerSize = 64 :=
  pick_eq_of ⟨_, incremental_mlkem768.HEADER_SIZE_eq, rfl⟩ fun _ ⟨n, hn, e⟩ => by
    rw [e, ok_inj hn incremental_mlkem768.HEADER_SIZE_eq]; rfl

theorem codePrims_macSize : codePrims.macSize = 32 := by
  simp only [codePrims, authenticator.Authenticator.MACSIZE]; rfl

theorem codePrims_ct1Size (hsz : MlkemSizes) : codePrims.ct1Size = 960 :=
  pick_eq_of ⟨_, hsz.1, rfl⟩ fun _ ⟨n, hn, e⟩ => by rw [e, ok_inj hn hsz.1]; rfl

theorem codePrims_ct2Size (hsz : MlkemSizes) : codePrims.ct2Size = 128 :=
  pick_eq_of ⟨_, hsz.2.1, rfl⟩ fun _ ⟨n, hn, e⟩ => by rw [e, ok_inj hn hsz.2.1]; rfl

theorem codePrims_ekSize (hsz : MlkemSizes) : codePrims.ekSize = 1152 :=
  pick_eq_of ⟨_, hsz.2.2, rfl⟩ fun _ ⟨n, hn, e⟩ => by rw [e, ok_inj hn hsz.2.2]; rfl

/-! ## Lengths -/

theorem u64_of_lt {n : ℕ} (h : n < 2 ^ 64) : ∃ ep : Std.U64, ep.val = n :=
  ⟨UScalar.ofNatCore n (by simpa [UScalarTy.numBits] using h), UScalar.ofNatCore_val_eq _⟩

theorem codePrims_toBytes_length {n : ℕ} (h : n < 2 ^ 64) : (codePrims.toBytes n).length = 8 := by
  obtain ⟨ep, hep⟩ := u64_of_lt h
  obtain ⟨_, _, e⟩ := pick_spec (p := fun l => ∃ ep : Std.U64, ep.val = n ∧
    l = (core.num.U64.to_be_bytes ep).val) ⟨_, ep, hep, rfl⟩
  show (pick (β := Bytes) _).length = 8
  rw [e]
  exact (core.num.U64.to_be_bytes _).property

theorem codePrims_kdfOk_length (ss : Bytes) {n : ℕ} (h : n < 2 ^ 64) :
    (codePrims.kdfOk ss n).length = 32 := by
  obtain ⟨ep, hep⟩ := u64_of_lt h
  obtain ⟨_, _, e⟩ := pick_spec (p := fun out => ∃ ep : Std.U64, ep.val = n ∧
    out = crypto.hkdf (List.replicate 32 0#u8) ss
      (Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++ (core.num.U64.to_be_bytes ep).val) 32)
    ⟨_, ep, hep, rfl⟩
  show (pick (β := Bytes) _).length = 32
  rw [e, crypto.hkdf_length]

theorem codePrims_kdfAuth_length (rk k : Bytes) {n : ℕ} (h : n < 2 ^ 64) :
    (codePrims.kdfAuth rk k n).length = 64 := by
  obtain ⟨ep, hep⟩ := u64_of_lt h
  obtain ⟨_, _, e⟩ := pick_spec (p := fun out => ∃ ep : Std.U64, ep.val = n ∧
    out = crypto.hkdf (List.replicate 32 0#u8) (rk ++ k)
      (authenticator.Authenticator.updateLabel ++ (core.num.U64.to_be_bytes ep).val) 64)
    ⟨_, ep, hep, rfl⟩
  show (pick (β := Bytes) _).length = 64
  rw [e, crypto.hkdf_length]

/-- `Decaps` on inputs of 2400, 960 and 128 bytes returns 32 bytes. -/
theorem codePrims_decaps_length (dk ct1 ct2 : Bytes) (h1 : dk.length = 2400)
    (h2 : ct1.length = 960) (h3 : ct2.length = 128) :
    (codePrims.decaps dk ct1 ct2).length = 32 := by
  have hmax := L2.usize_max_ge
  let dkv : alloc.vec.Vec Std.U8 := alloc.vec.Vec.from dk (by omega)
  let c1v : alloc.vec.Vec Std.U8 := alloc.vec.Vec.from ct1 (by omega)
  let c2v : alloc.vec.Vec Std.U8 := alloc.vec.Vec.from ct2 (by omega)
  obtain ⟨ss, hss, -⟩ := WP.spec_imp_exists (incremental_mlkem768.decaps_spec dkv c1v c2v
    (by simp [dkv, alloc.vec.Vec.length, alloc.vec.Vec.from_val, h1])
    (by simp [c1v, alloc.vec.Vec.length, alloc.vec.Vec.from_val, h2])
    (by simp [c2v, alloc.vec.Vec.length, alloc.vec.Vec.from_val, h3]))
  obtain ⟨dkv', c1v', c2v', ssv, e1, e2, e3, hssv, e⟩ := pick_spec (p := fun ss =>
    ∃ dkv ct1v ct2v ssv : alloc.vec.Vec Std.U8, dkv.val = dk ∧ ct1v.val = ct1 ∧ ct2v.val = ct2 ∧
      incremental_mlkem768.decaps dkv ct1v ct2v = ok ssv ∧ ss = ssv.val)
    ⟨_, dkv, c1v, c2v, ss, alloc.vec.Vec.from_val .., alloc.vec.Vec.from_val ..,
      alloc.vec.Vec.from_val .., hss, rfl⟩
  show (pick (β := Bytes) _).length = 32
  rw [e]
  exact (WP.post_of_ok (incremental_mlkem768.decaps_spec dkv' c1v' c2v'
    (by simp only [alloc.vec.Vec.length, e1, h1]) (by simp only [alloc.vec.Vec.length, e2, h2])
    (by simp only [alloc.vec.Vec.length, e3, h3])) hssv).2

/-- `Decoder.new(32 K)` is the empty decoder of `polyStreamDecoder`. -/
theorem codePrims_decoderNew {M : Type} (K : ℕ) (hKN : K ≤ 2 ^ 16) (cd : L2.Codec M K) :
    codePrims.decoderNew (32 * K) = (L2.polyStreamDecoder K hKN cd).empty := by
  have hmax := L2.usize_max_ge
  have hK : 16 * K ≤ Usize.max := by omega
  have h32 : 32 * K ≤ Usize.max := by omega
  have hnew := L2.new_eq_emptyDecoder K hK h32
  refine pick_eq_of ⟨_, UScalar.ofNatCore_val_eq _, hnew⟩ fun d ⟨u, hu, hd⟩ => ?_
  have : u = UScalar.ofNatCore (32 * K) (by
      have := Nat.two_pow_pos System.Platform.numBits
      simp only [Usize.max, UScalarTy.numBits, Usize.numBits] at *; omega) := by
    apply UScalar.eq_of_val_eq; rw [hu, UScalar.ofNatCore_val_eq]
  rw [this] at hd
  have := ok_inj hd hnew
  cases this
  rfl

/-- `K` chunks cut from `32 K` bytes, flattened, are the bytes. -/
theorem flatten_blocks (K : ℕ) (v : List Std.U8) (hv : v.length = 32 * K) :
    (List.ofFn fun i : Fin K => List.ofFn fun b : Fin 32 => v[32 * i.val + b.val]!).flatten =
      v := by
  induction K generalizing v with
  | zero => simp_all
  | succ K ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    have h1 : (List.ofFn fun b : Fin 32 => v[32 * (0 : Fin (K + 1)).val + b.val]!) =
        v.take 32 := by
      apply List.ext_getElem (by simp; omega)
      intro j hj _
      simp only [List.getElem_ofFn, List.getElem_take, Fin.val_zero, mul_zero, zero_add]
      simp only [List.length_ofFn] at hj
      exact getElem!_pos v j (by omega)
    have h2 := ih (v.drop 32) (by simp; omega)
    have h3 : (List.ofFn fun i : Fin K => List.ofFn fun b : Fin 32 =>
        v[32 * (Fin.succ i).val + b.val]!) =
        List.ofFn fun i : Fin K => List.ofFn fun b : Fin 32 => (v.drop 32)[32 * i.val + b.val]! := by
      congr 1; funext i; congr 1; funext b
      simp only [Fin.val_succ]
      rw [getElem!_pos (v.drop 32) _ (by simp; omega), getElem!_pos v _ (by omega),
        List.getElem_drop]
      congr 1; ring
    rw [h1, h3, h2, List.take_append_drop]

/-- Parsing the chunks of a decoded message reads back its bytes. -/
theorem bytesOfChunks_unflatten (K : ℕ) (v : List Std.U8) (hv : v.length = 32 * K) :
    (bytesOfChunks K (L2.unflatten K v)).1 = v := by
  simp only [bytesOfChunks, L2.unflatten, Array.make_val]
  exact flatten_blocks K v hv

/-! ## The authenticator -/

/-- Two lists of length `n` are equal as `n` bytes exactly when they are equal. -/
theorem fit_eq_fit_iff {n : ℕ} {l m : List Std.U8} (hl : l.length = n) (hm : m.length = n) :
    fit n l = fit n m ↔ l = m := by
  constructor
  · intro h
    have := congrArg Subtype.val h
    rwa [fit_of_length hl, fit_of_length hm] at this
  · rintro rfl; rfl

theorem auth_update_macKey_length (a : Auth) {e : ℕ} (he : e < 2 ^ 64) (k : Bytes) :
    (Auth.update codePrims a e k).macKey.length = 32 := by
  simp only [Auth.update, List.length_drop, codePrims_kdfAuth_length _ _ he]

theorem protocolInfo_length : codePrims.protocolInfo.length = 24 := by
  simp only [codePrims, ascii, List.length_map]; decide

theorem macCt_length (a : Auth) {e : ℕ} (he : e < 2 ^ 64) (ct : Bytes)
    (hk : a.macKey.length = 32) (hct : ct.length ≤ 2 ^ 20) :
    (Auth.macCt codePrims a e ct).length = 32 := by
  have hu : U32.max = 2 ^ 32 - 1 := by simp [U32.max, U32.numBits, UScalarTy.numBits]
  have ha : (ascii ":ciphertext").length = 11 := by simp only [ascii, List.length_map]; decide
  apply mac_length_u32
  · rw [hk, hu]; omega
  · simp only [List.length_append, protocolInfo_length, ha, codePrims_toBytes_length he, hu]
    omega

theorem macHdr_length (a : Auth) {e : ℕ} (he : e < 2 ^ 64) (hdr : Bytes)
    (hk : a.macKey.length = 32) (hh : hdr.length ≤ 2 ^ 20) :
    (Auth.macHdr codePrims a e hdr).length = 32 := by
  have hu : U32.max = 2 ^ 32 - 1 := by simp [U32.max, U32.numBits, UScalarTy.numBits]
  have ha : (ascii ":ekheader").length = 9 := by simp only [ascii, List.length_map]; decide
  apply mac_length_u32
  · rw [hk, hu]; omega
  · simp only [List.length_append, protocolInfo_length, ha, codePrims_toBytes_length he, hu]
    omega

/-! ## Codecs -/

/-- Parsing the chunks of `32 K` bytes in a pair form splits the bytes. -/
theorem pairForm_parse (a b K : ℕ) (h : a + b = 32 * K) (v : List Std.U8)
    (hv : v.length = 32 * K) :
    (codecOf (pairForm a b K h)).parse (L2.unflatten K v) =
      some (fit a (v.take a), fit b (v.drop a)) := by
  simp only [codecOf, pairForm, bytesOfChunks_unflatten K v hv]

/-- Parsing the chunks of `32 K` bytes in the byte form gives the bytes. -/
theorem bytesForm_parse (K : ℕ) (v : List Std.U8) (hv : v.length = 32 * K) :
    (codecOf (bytesForm K)).parse (L2.unflatten K v) = some ⟨v, hv⟩ := by
  simp only [codecOf, bytesForm, Option.some.injEq]
  exact Subtype.ext (bytesOfChunks_unflatten K v hv)

/-! ## Encoders -/

/-- The chunks of `32 K` bytes, flattened, are the bytes. -/
theorem flatten_chunkOf (K : ℕ) (b : B (32 * K)) : L2.flatten (chunkOf K b) = b.1 := by
  apply List.ext_getElem (by rw [L2.flatten_length, b.2])
  intro t ht _
  rw [L2.flatten_length] at ht
  have hb := b.2
  simp only [L2.flatten, List.getElem_ofFn, chunkOf, Array.make_val]
  have h32 : ((b.1.drop (32 * (t / 32))).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, hb]; omega
  rw [fit_of_length h32, getElem!_pos _ _ (by rw [h32]; omega), List.getElem_take,
    List.getElem_drop]
  congr 1
  omega

open spqr.encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder in
/-- `Encode` of the bytes of a payload in a byte form gives an encoder at counter `0` that holds
the payload's chunks. -/
theorem codePrims_encode {M : Type} {K : ℕ} (f : ByteForm M K) (hK : K ≤ 2 ^ 15) (p : M) :
    L2.EncInv ((codecOf f).ser p) (codePrims.encode (f.toBytes p).1) ∧
      (codePrims.encode (f.toBytes p).1).idx.val = 0 := by
  have hmax := L2.usize_max_ge
  have hl := (f.toBytes p).2
  have hfl : L2.flatten ((codecOf f).ser p) = (f.toBytes p).1 := flatten_chunkOf K _
  let sl : Slice Std.U8 := Slice.from (f.toBytes p).1 (by omega)
  obtain ⟨res, hres, hpost⟩ := WP.spec_imp_exists (encode_bytes_spec sl
    (by simp only [sl, Slice.length, Slice.from_val, hl]; omega)
    (by simp only [sl, Slice.length, Slice.from_val, hl]; omega))
  obtain ⟨e, rfl⟩ : ∃ e, res = .Ok e := by
    rcases res with e | _
    · exact ⟨e, rfl⟩
    · exact hpost.elim
  obtain ⟨s', hs', henc⟩ := pick_spec (p := fun e => ∃ s : Slice Std.U8,
    s.val = (f.toBytes p).1 ∧ encode_bytes s = ok (.Ok e)) ⟨e, sl, Slice.from_val .., hres⟩
  have hs'' : s' = Slice.from (L2.flatten ((codecOf f).ser p)) (by rw [hfl]; omega) :=
    Slice.ext _ _ (by rw [hs', Slice.from_val, hfl])
  rw [hs''] at henc
  obtain ⟨h0, hinv⟩ := L2.encode_bytes_inv hK _ _ _ henc
  exact ⟨hinv, h0⟩

end SpqrBridge
