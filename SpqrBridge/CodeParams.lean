/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.CodePrims
import SpqrBridge.CodePrimsFacts
import SpqrBridge.SendFacts
import SpqrBridge.Adapter
import SpqrBridge.PolyDecoderLawful
import SecureMessaging.SCKA.SPQR.Construction

/-!
# Secure-messaging parameters from the code's primitives

`codeParams` is the `MLKEMBraid.Parameters ProbComp` record that the bridge transfers the
secure-messaging bound to. Every field is total. Byte strings are read with `fit n`. Such a result agrees
with `codePrims` wherever the code gives `n` bytes, and is `n` zero bytes elsewhere. The decoder
fields use the total wrapper `L2.polyStreamDecoder`.

Sampling uses `sampleB`, as the uniform `fill_bytes` oracle of `codeScheme` does. Key generation
samples 64 bytes and `Encaps1` samples 32 bytes, as the code does.

`codeKem` is the KEM of `codeParams`. Its correctness error is the `ε` of the code-level bound.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming

/-! ## Codecs: payloads as chunks of 32 bytes -/

/-- Chunk `i` of a `32 K`-byte string: its bytes `32 i` to `32 i + 31`. -/
def chunkOf (K : ℕ) (b : B (32 * K)) (i : Fin K) : L2.Sym :=
  Aeneas.Std.Array.make 32#usize (fit 32 ((b.1.drop (32 * i.val)).take 32)).1
    (fit 32 ((b.1.drop (32 * i.val)).take 32)).2

/-- The `32 K` bytes of `K` chunks, in order. -/
def bytesOfChunks (K : ℕ) (c : Fin K → L2.Sym) : B (32 * K) :=
  ⟨(List.ofFn fun i => (c i).val).flatten, by
    simp [List.length_flatten, List.map_ofFn, Function.comp_def]
    ring⟩

/-- `bytesOfChunks` inverts `chunkOf`. -/
theorem bytesOfChunks_chunkOf (K : ℕ) (b : B (32 * K)) : bytesOfChunks K (chunkOf K b) = b := by
  apply Subtype.ext
  have hc : ∀ i : Fin K, (chunkOf K b i).val = (b.1.drop (32 * i.val)).take 32 := by
    intro i
    simp only [chunkOf, Aeneas.Std.Array.make_val]
    apply fit_of_length
    simp only [List.length_take, List.length_drop, b.2]
    have := i.isLt
    omega
  simp only [bytesOfChunks, hc]
  exact flatten_ofFn_blocks K b.1 b.2

/-- A payload type with an injection into `32 K` bytes and its partial inverse. -/
structure ByteForm (M : Type) (K : ℕ) where
  /-- The serialized payload. -/
  toBytes : M → B (32 * K)
  /-- Parse the serialized payload. -/
  ofBytes : B (32 * K) → Option M
  /-- Parsing inverts serialization. -/
  ofBytes_toBytes : ∀ p, ofBytes (toBytes p) = some p

/-- The codec of a payload type with a byte form. -/
def codecOf {M : Type} {K : ℕ} (f : ByteForm M K) : L2.Codec M K where
  ser p := chunkOf K (f.toBytes p)
  parse c := f.ofBytes (bytesOfChunks K c)
  parse_ser p := by rw [bytesOfChunks_chunkOf, f.ofBytes_toBytes]

/-- `bytesForm K` is the byte form on `B (32 * K)` with `toBytes = id` and `ofBytes = some`. -/
def bytesForm (K : ℕ) : ByteForm (B (32 * K)) K := ⟨id, some, fun _ => rfl⟩

/-- A pair of byte strings as their concatenation. -/
def pairForm (a b K : ℕ) (h : a + b = 32 * K) : ByteForm (B a × B b) K where
  toBytes p := ⟨p.1.1 ++ p.2.1, by simp only [List.length_append, p.1.2, p.2.2, h]⟩
  ofBytes x := some (fit a (x.1.take a), fit b (x.1.drop a))
  ofBytes_toBytes p := by
    obtain ⟨⟨l1, h1⟩, ⟨l2, h2⟩⟩ := p
    simp only [Option.some.injEq, Prod.mk.injEq]
    constructor <;> apply Subtype.ext
    · rw [fit_of_length (by simp [h1])]; simp [← h1]
    · rw [fit_of_length (by simp [h1, h2])]; simp [← h1]

/-- The header stream: `hdr ‖ mac`, 96 bytes in 3 chunks. -/
def hdrCodec : L2.Codec (B 64 × B 32) 3 := codecOf (pairForm 64 32 3 rfl)
/-- The `ek` stream: 1152 bytes in 36 chunks. -/
def ekCodec : L2.Codec (B (32 * 36)) 36 := codecOf (bytesForm 36)
/-- The `ct1` stream: 960 bytes in 30 chunks. -/
def ct1Codec : L2.Codec (B (32 * 30)) 30 := codecOf (bytesForm 30)
/-- The `ct2` stream: `ct2 ‖ mac`, 160 bytes in 5 chunks. -/
def ct2Codec : L2.Codec (B 128 × B 32) 5 := codecOf (pairForm 128 32 5 rfl)

/-! ## The KEM -/

/-- A public key: a header and a vector that `ek_matches_header` accepts. -/
abbrev PK : Type := {p : B 64 × B 1152 // codePrims.ekMatches p.1.1 p.2.1 = true}

/-- Generated keys are valid. With `CodeAgreesSeeded`, this is `pk1HashValid_pk1Bytes` and
`pk2Valid_pk2Bytes` of #661. -/
theorem keyGen_valid (r : Bytes) :
    codePrims.ekMatches (fit 64 (codePrims.keyGen r).2.1).1
      (fit 1152 (codePrims.keyGen r).2.2).1 = true := by
  have h := seededKeyGen_lengths r
  rw [show codePrims.keyGen r = seededKeyGen r from rfl, fit_of_length h.2.1,
    fit_of_length h.2.2]
  simp only [seededKeyGen]
  exact codePrims_ekMatches_generated (seedOfBytes r)

/-- Let `t : B 64` and `o := codePrims.keyGen t.1`. Then `keyGenOf t` is the pair of the public
key with header `fit 64 o.2.1` and vector `fit 1152 o.2.2`, valid by `keyGen_valid t.1`, and the
secret key `fit 2400 o.1`. -/
noncomputable def keyGenOf (t : B 64) : PK × B 2400 :=
  (⟨(fit 64 (codePrims.keyGen t.1).2.1, fit 1152 (codePrims.keyGen t.1).2.2), keyGen_valid t.1⟩,
    fit 2400 (codePrims.keyGen t.1).1)

/-- Let `h : B 64`, `t : B 32` and `o := codePrims.encaps1 h.1 t.1`. Then
`encaps1Of h t = (fit 2080 o.1, fit 960 o.2.1, fit 32 o.2.2)`. -/
noncomputable def encaps1Of (h : B 64) (t : B 32) : B 2080 × B 960 × B 32 :=
  let o := codePrims.encaps1 h.1 t.1
  (fit 2080 o.1, fit 960 o.2.1, fit 32 o.2.2)

/-- The pure second stage. -/
noncomputable def encaps2Det (st : B 2080) (h : B 64) (v : B 1152) : B 128 :=
  fit 128 (codePrims.encaps2 st.1 h.1 v.1)

/-- The pure decapsulation. It never refuses. -/
noncomputable def decapsDet (sk : B 2400) (c : B 960 × B 128) : Option (B 32) :=
  some (fit 32 (codePrims.decaps sk.1 c.1.1 c.2.1))

/-- `encaps1Fn h` samples `t` with `sampleB 32` and returns `encaps1Of h t`. -/
noncomputable def encaps1Fn (h : B 64) : ProbComp (B 2080 × B 960 × B 32) := do
  let t ← sampleB 32
  pure (encaps1Of h t)

/-- `codeKem` is the KEM with these three algorithms.

* Key generation samples `t` with `sampleB 64` and returns `keyGenOf t`.
* Let `pk.1 = (hdr, vec)`. Encapsulation samples `(st, c1, k)` with `encaps1Fn hdr`, lets
  `c2 := encaps2Det st hdr vec`, and returns `((c1, c2), k)`.
* Decapsulation of `c` with `sk` is `pure (decapsDet sk c)`. -/
noncomputable def codeKem : KEMScheme ProbComp (B 32) PK (B 2400) (B 960 × B 128) where
  keygen := do
    let t ← sampleB 64
    pure (keyGenOf t)
  encaps pk := do
    let (hdr, vec) := pk.1
    let (st, c1, k) ← encaps1Fn hdr
    let c2 ← (pure (encaps2Det st hdr vec) : ProbComp (B 128))
    pure ((c1, c2), k)
  decaps sk c := pure (decapsDet sk c)

/-- The incremental structure of the code's KEM. -/
noncomputable def codeInc : codeKem.IncrementalStructure where
  PKheader := B 64
  PKvector := B 1152
  C₁ := B 960
  C₂ := B 128
  St := B 2080
  validPK h v := codePrims.ekMatches h.1 v.1
  splitPK := Equiv.refl _
  splitC := Equiv.refl _
  encaps1 := encaps1Fn
  encaps2 st h v := pure (encaps2Det st h v)
  factor _ := rfl

/-! ## The parameter record -/

/-- `kdfOKTotal k n = fit 32 (codePrims.kdfOk k.1 n)`, for every natural number `n`. For an
epoch `ep : u64`, `kdfOK_agree` (`SpqrBridge.CodeContracts`) relates it to the code's HKDF call. -/
noncomputable def kdfOKTotal (k : B 32) (n : ℕ) : B 32 := fit 32 (codePrims.kdfOk k.1 n)

/-- The secure-messaging parameters of the code. -/
noncomputable def codeParams : MLKEMBraid.Parameters ProbComp where
  K := B 32
  PK := PK
  SK := B 2400
  C := B 960 × B 128
  kem := codeKem
  inc := codeInc
  hDet := ⟨decapsDet, fun _ _ => rfl⟩
  hEnc2 := ⟨encaps2Det, fun _ _ _ => rfl⟩
  EpochKey := B 32
  Mac := B 32
  Sym := L2.Sym
  kdfOK := kdfOKTotal
  ecpHdr := L2.ecp 3 (by decide) (by decide) hdrCodec
  ecpEk := L2.ecp 36 (by decide) (by decide) ekCodec
  ecpCt1 := L2.ecp 30 (by decide) (by decide) ct1Codec
  ecpCt2 := L2.ecp 5 (by decide) (by decide) ct2Codec
  decHdr := L2.polyStreamDecoder 3 (by decide) hdrCodec
  decEk := L2.polyStreamDecoder 36 (by decide) ekCodec
  decCt1 := L2.polyStreamDecoder 30 (by decide) ct1Codec
  decCt2 := L2.polyStreamDecoder 5 (by decide) ct2Codec

instance : DecidableEq codeParams.K := inferInstanceAs (DecidableEq (B 32))
instance : DecidableEq codeParams.EpochKey := inferInstanceAs (DecidableEq (B 32))
instance : DecidableEq codeParams.Sym := inferInstanceAs (DecidableEq L2.Sym)

/-! ## The authenticator and the randomness leak -/

/-- The code's ratcheted authenticator, from `Braid.Auth`. MACs are read as 32 bytes, and
verification compares with the recomputed MAC. -/
noncomputable def codeAuth :
    RatchetedAuthenticator InitKey (B 32) Auth (B 64) (B 960 × B 128) (B 32) where
  init ik ep := Auth.init codePrims ep ik.1.val
  update a ep k := Auth.update codePrims a ep k.1
  macHeader a ep h := fit 32 (Auth.macHdr codePrims a ep h.1)
  verifyHeader a ep h t := decide (t = fit 32 (Auth.macHdr codePrims a ep h.1))
  macCiphertext a ep c := fit 32 (Auth.macCt codePrims a ep (c.1.1 ++ c.2.1))
  verifyCiphertext a ep c t := decide (t = fit 32 (Auth.macCt codePrims a ep (c.1.1 ++ c.2.1)))
  verifyHeader_correct _ _ _ := by simp only [decide_true]
  verifyCiphertext_correct _ _ _ := by simp only [decide_true]

/-- `codeIrl` is the randomness leak of `codeInc` with randomness types `B 64`, `B 32` and
`Unit`. Its key generation leak samples `t` with `sampleB 64` and returns `(keyGenOf t, t)`. Its
first encapsulation leak samples `t` with `sampleB 32` and returns `(encaps1Of h t, t)`. Its second
encapsulation leak is `pure (encaps2Det st h v, ())`. -/
noncomputable def codeIrl : codeKem.IncrementalRandLeak codeInc where
  KeygenRand := B 64
  Encaps1Rand := B 32
  Encaps2Rand := Unit
  keygenRleak := do
    let t ← sampleB 64
    pure (keyGenOf t, t)
  encaps1Rleak h := do
    let t ← sampleB 32
    pure (encaps1Of h t, t)
  encaps2Rleak st h v := pure (encaps2Det st h v, ())
  keygen_fst := by simp only [bind_assoc, pure_bind]; rfl
  encaps1_fst _ := by simp only [bind_assoc, pure_bind]; rfl
  encaps2_fst _ _ _ := by simp only [pure_bind]; rfl

/-- The secure-messaging SPQR scheme over the code's parameters. -/
noncomputable def smScheme (sampleInitKey : ProbComp InitKey) :=
  SPQR.scheme codeParams codeAuth codeIrl sampleInitKey

end SpqrBridge
