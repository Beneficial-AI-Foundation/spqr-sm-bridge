/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Spqr.Specs.Braid.StateMachine.Refinement
import Spqr.Crypto.Fips203.Refinement.EncapsBytes
import Spqr.Crypto.Fips203.Refinement.KeyPairBytes
import SpqrBridge.SeededSpecs

/-!
# The fixed primitive instance of the bridge

`codePrims` is one named `CodePrims`. Key generation is the FIPS 203 model of `from_seed` on
the first 64 bytes of its randomness. `Encaps1` is the FIPS 203 model of `encapsulate1` on the
first 32 bytes. Every other primitive is the code's own function where that function succeeds.

`CodeAgreesSeeded P` is `CodeAgrees P` with key generation and `Encaps1` pinned to these models.
`codePrims_agreesSeeded` proves that `codePrims` satisfies it.

`fit n l` is the total way to read a byte list as `n` bytes: `l` itself when it has length
`n`, and `n` zero bytes otherwise. The bridge uses it wherever a secure-messaging field must
be total and the code gives a length only on its own domain.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid

/-! ## Total byte strings -/

/-- `n` bytes read from a list: the list itself when its length is `n`, and zeros otherwise. -/
def fit (n : ℕ) (l : List Std.U8) : {b : List Std.U8 // b.length = n} :=
  if h : l.length = n then ⟨l, h⟩ else ⟨List.replicate n 0#u8, List.length_replicate⟩

/-- On a list of the right length, `fit` is the list. -/
theorem fit_of_length {n : ℕ} {l : List Std.U8} (h : l.length = n) : (fit n l).1 = l := by
  simp only [fit, h, ↓reduceDIte]

/-! ## Seeds and messages from randomness -/

/-- The 64-byte FIPS 203 seed read from the first bytes of `r`, zero-padded. -/
def seedOfBytes (r : Bytes) : Fin 64 → UInt8 := fun i => (r.getD i.val 0#u8).toUInt8

/-- The 32-byte FIPS 203 message read from the first bytes of `r`, zero-padded. -/
def msgOfBytes (r : Bytes) : Fin 32 → UInt8 := fun i => (r.getD i.val 0#u8).toUInt8

/-- Key generation on randomness `r`: `(dk, ek_header, ek_vector)` of the FIPS 203 model of
`from_seed`. -/
noncomputable def seededKeyGen (r : Bytes) : Bytes × Bytes × Bytes :=
  (Fips203.Refinement.keyPairList (seedOfBytes r),
    Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes (seedOfBytes r)),
    Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes (seedOfBytes r)))

/-- `Encaps1` on a header and randomness `r`: `(encaps_secret, ct1, shared_secret)` of the
FIPS 203 model of `encapsulate1`. A header shorter than 64 bytes gives empty outputs; the code
rejects such headers. -/
noncomputable def seededEncaps1 (hdr r : Bytes) : Bytes × Bytes × Bytes :=
  if h : 64 ≤ hdr.length then
    (Fips203.Refinement.toU8List (Fips203.Refinement.stateOut hdr h (msgOfBytes r)),
      Fips203.Refinement.ct1List hdr h (msgOfBytes r),
      Fips203.Refinement.toU8List (Fips203.Refinement.ssOut hdr h (msgOfBytes r)))
  else ([], [], [])

/-! ## The instance -/

/-- `CodeAgrees P`, with key generation and `Encaps1` fixed to the FIPS 203 models of the code's
seeded calls. -/
structure CodeAgreesSeeded (P : CodePrims) : Prop extends CodeAgrees P where
  /-- Key generation is `from_seed` on the first 64 bytes. -/
  keyGenSeed : ∀ r, P.keyGen r = seededKeyGen r
  /-- `Encaps1` is `encapsulate1` on the first 32 bytes. -/
  encaps1Seed : ∀ hdr r, P.encaps1 hdr r = seededEncaps1 hdr r

/-- `pick p` is a value that satisfies `p` when there is one. -/
noncomputable def pick {β : Type} [Nonempty β] (p : β → Prop) : β :=
  open Classical in if h : ∃ b, p b then Classical.choose h else Classical.choice inferInstance

instance : Nonempty encoding.polynomial.PolyEncoder :=
  ⟨⟨0#u32, .Polys (Array.repeat 16#usize
    ⟨alloc.vec.Vec.from [] (by simp only [List.length_nil, zero_le])⟩)⟩⟩

instance : Nonempty encoding.polynomial.PolyDecoder :=
  ⟨⟨0#usize, Array.repeat 16#usize ⟨Slice.from [] (by simp only [List.length_nil, zero_le])⟩,
    false⟩⟩

instance : Nonempty encoding.Chunk := ⟨⟨0#u16, Array.repeat 32#usize 0#u8⟩⟩

/-- The fixed primitive instance. It is `codeAgrees_exists`'s construction, except that key
generation and `Encaps1` are the seeded FIPS 203 models. -/
noncomputable def codePrims : CodePrims where
  encode msg := pick fun e => ∃ s : Slice Std.U8, s.val = msg ∧
    encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.encode_bytes s = ok (.Ok e)
  nextChunk e := pick fun ce =>
    encoding.polynomial.PolyEncoder.Insts.SpqrEncodingEncoder.next_chunk e = ok ce
  decoderNew n := pick fun d => ∃ u : Std.Usize, u.val = n ∧
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.new u = ok (.Ok d)
  addChunk d c := pick fun d' =>
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d c = ok d'
  message d := pick fun o => ∃ m,
    encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d = ok m ∧
      o = m.map (·.val)
  keyGen := seededKeyGen
  encaps1 := seededEncaps1
  encaps2 es _ ek := pick fun ct2 => ∃ ekv esv ct2v : alloc.vec.Vec Std.U8,
    ekv.val = ek ∧ esv.val = es ∧ incremental_mlkem768.encaps2 ekv esv = ok ct2v ∧
      ct2 = ct2v.val
  decaps dk ct1 ct2 := pick fun ss => ∃ dkv ct1v ct2v ssv : alloc.vec.Vec Std.U8,
    dkv.val = dk ∧ ct1v.val = ct1 ∧ ct2v.val = ct2 ∧
      incremental_mlkem768.decaps dkv ct1v ct2v = ok ssv ∧ ss = ssv.val
  ekMatches hdr ek := pick fun b => ∃ ekv hdrv : alloc.vec.Vec Std.U8,
    ekv.val = ek ∧ hdrv.val = hdr ∧ incremental_mlkem768.ek_matches_header ekv hdrv = ok b
  headerSize := pick fun m => ∃ n, incremental_mlkem768.HEADER_SIZE = ok n ∧ m = n.val
  ekSize := pick fun m => ∃ n, incremental_mlkem768.ENCAPSULATION_KEY_SIZE = ok n ∧ m = n.val
  ct1Size := pick fun m => ∃ n, incremental_mlkem768.CIPHERTEXT1_SIZE = ok n ∧ m = n.val
  ct2Size := pick fun m => ∃ n, incremental_mlkem768.CIPHERTEXT2_SIZE = ok n ∧ m = n.val
  macSize := authenticator.Authenticator.MACSIZE.val
  mac k d := pick fun t => ∃ (ks ds : Slice Std.U8) (tv : alloc.vec.Vec Std.U8),
    ks.val = k ∧ ds.val = d ∧ libcrux_hmac.hmac .Sha256 ks ds (some 32#usize) = ok tv ∧
      t = tv.val
  protocolInfo := ascii "Signal_PQCKA_V1_MLKEM768"
  toBytes n := pick fun l => ∃ ep : Std.U64, ep.val = n ∧ l = (core.num.U64.to_be_bytes ep).val
  kdfAuth rk k n := pick fun out => ∃ ep : Std.U64, ep.val = n ∧
    out = crypto.hkdf (List.replicate 32 0#u8) (rk ++ k)
      (authenticator.Authenticator.updateLabel ++ (core.num.U64.to_be_bytes ep).val) 64
  kdfOk ss n := pick fun out => ∃ ep : Std.U64, ep.val = n ∧
    out = crypto.hkdf (List.replicate 32 0#u8) ss
      (Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++ (core.num.U64.to_be_bytes ep).val) 32

/-- `codePrims` agrees with the code on its seeded calls. The fields other than `keyGen` and
`encaps1` follow `codeAgrees_exists`. `keyGen` and `encaps1` follow `generate_spec` and the
`encaps1` spec of #661, with the seed and the message read back from the bytes that
`fill_bytes` wrote. -/
theorem codePrims_agreesSeeded : CodeAgreesSeeded codePrims := by
  have pick_eq : ∀ {β : Type} [Nonempty β] {p : β → Prop} {b : β}, p b →
      (∀ b', p b' → b' = b) → pick p = b := by
    intro β _ p b hb hu
    have h : ∃ b, p b := ⟨b, hb⟩
    simp only [pick, h, _root_.dite_true]
    exact hu _ (Classical.choose_spec h)
  have ok_unique : ∀ {α : Type} {m : Result α} {a b : α}, m = ok a → m = ok b → b = a := by
    intro α m a b ha hb
    rw [ha, Result.ok.injEq] at hb; exact hb.symm
  have hU64 : ∀ a b : Std.U64, a.val = b.val → a = b := fun _ _ h => UScalar.eq_of_val_eq h
  have hUs : ∀ a b : Std.Usize, a.val = b.val → a = b := fun _ _ h => UScalar.eq_of_val_eq h
  have hV : ∀ a b : alloc.vec.Vec Std.U8, a.val = b.val → a = b :=
    fun a b h => (alloc.vec.Vec.eq_iff a b).mpr h
  have hS : ∀ a b : Slice Std.U8, a.val = b.val → a = b := fun a b h => (Slice.eq_iff a b).mpr h
  refine { toCodeAgrees := ?_, keyGenSeed := fun _ => rfl, encaps1Seed := fun _ _ => rfl }
  constructor
  · intro msg e h
    refine pick_eq ⟨msg, rfl, h⟩ ?_
    rintro e' ⟨s', hs', h'⟩
    rw [hS s' msg hs'] at h'
    simpa only [core.result.Result.Ok.injEq] using ok_unique h h'
  · intro e e' c h
    exact pick_eq h fun _ h' => ok_unique h h'
  · intro n d h
    refine pick_eq ⟨n, rfl, h⟩ ?_
    rintro d' ⟨u, hu, h'⟩
    rw [hUs u n hu] at h'
    simpa only [core.result.Result.Ok.injEq] using ok_unique h h'
  · intro d d' c h
    exact pick_eq h fun _ h' => ok_unique h h'
  · intro d m h
    refine pick_eq ⟨m, h, rfl⟩ ?_
    rintro o ⟨m', h', rfl⟩
    rw [ok_unique h h']
  · intro R i₁ i₂ rng rng' k h
    obtain ⟨seed, hdk, hhdr, hek⟩ := generate_ok_seed i₁ i₂ rng rng' k h
    have hs : seedOfBytes (Fips203.Refinement.toU8List seed) = seed :=
      funext (toU8List_getD seed)
    exact ⟨Fips203.Refinement.toU8List seed, by
      simp only [codePrims, seededKeyGen, hs, hdk, hhdr, hek]⟩
  · intro R i₁ i₂ rng rng' hdr ct1 es ss h
    obtain ⟨h64, m, h1, h2, h3⟩ := encaps1_ok_msg i₁ i₂ hdr rng rng' ct1 es ss h
    have hm : msgOfBytes (Fips203.Refinement.toU8List m) = m := funext (toU8List_getD m)
    exact ⟨Fips203.Refinement.toU8List m, by
      simp only [codePrims, seededEncaps1, h64, _root_.dite_true, hm, h1, h2, h3]⟩
  · intro ek es ct2 hdr h
    refine pick_eq ⟨ek, es, ct2, rfl, rfl, h, rfl⟩ ?_
    rintro _ ⟨ekv, esv, ct2v, h1, h2, h', rfl⟩
    rw [hV ekv ek h1, hV esv es h2] at h'
    rw [ok_unique h h']
  · intro dk ct1 ct2 ss h
    refine pick_eq ⟨dk, ct1, ct2, ss, rfl, rfl, rfl, h, rfl⟩ ?_
    rintro _ ⟨dkv, ct1v, ct2v, ssv, h1, h2, h3, h', rfl⟩
    rw [hV dkv dk h1, hV ct1v ct1 h2, hV ct2v ct2 h3] at h'
    rw [ok_unique h h']
  · intro ek hdr b h
    refine pick_eq ⟨ek, hdr, rfl, rfl, h⟩ ?_
    rintro _ ⟨ekv, hdrv, h1, h2, h'⟩
    rw [hV ekv ek h1, hV hdrv hdr h2] at h'
    exact ok_unique h h'
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · intro n h
    exact pick_eq ⟨n, h, rfl⟩ fun _ ⟨n', h', e⟩ => by rw [e, ok_unique h h']
  · rfl
  · intro key data t h
    refine pick_eq ⟨key, data, t, rfl, rfl, h, rfl⟩ ?_
    rintro _ ⟨ks, ds, tv, h1, h2, h', rfl⟩
    rw [hS ks key h1, hS ds data h2] at h'
    rw [ok_unique h h']
  · rfl
  · intro ep
    exact pick_eq ⟨ep, rfl, rfl⟩ fun _ ⟨ep', h1, e⟩ => by rw [e, hU64 ep' ep h1]
  · intro rk k ep
    exact pick_eq ⟨ep, rfl, rfl⟩ fun _ ⟨ep', h1, e⟩ => by rw [e, hU64 ep' ep h1]
  · intro ss ep
    exact pick_eq ⟨ep, rfl, rfl⟩ fun _ ⟨ep', h1, e⟩ => by rw [e, hU64 ep' ep h1]

end SpqrBridge
