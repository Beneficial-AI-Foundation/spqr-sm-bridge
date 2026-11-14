/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.ChunkedSend

/-!
# `send_chunked`: every send arm

The bytes that a send asks for (`sendLen_of_refines`), the two sampling arms (`keysUnsampled`,
`headerReceived`), the coupling of the code's send with
`Chunked.send` (`send_chunked`), and the relation of the initial states (`ra_initA`,
`ra_initB`).
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming
open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational

/-- Let `0 < K ≤ 2 ^ 15`, let `f : ByteForm M K`, and let `l = (f.toBytes p).1`. Then `EncRel`
relates `codePrims.encode l` and the secure-messaging encoder that `EncoderState.init` builds
from `p`. -/
theorem encRel_init {M : Type} {K : ℕ} (hK : 0 < K) (hKN : K ≤ 2 ^ 16) (hK15 : K ≤ 2 ^ 15)
    (f : ByteForm M K) (p : M) (l : Bytes) (hl : (f.toBytes p).1 = l) :
    EncRel K hK hKN (codecOf f) (codePrims.encode l)
      (EncoderState.init (L2.ecp K hK hKN (codecOf f)) p) := by
  subst hl
  have h := codePrims_encode f hK15 p
  exact ⟨rfl, h.1, by rw [h.2]; rfl⟩

/-- `seedLen σ` is 64 for `keysUnsampled`, 32 for `headerReceived`, and 0 for each other
state. -/
def seedLen : BState → ℕ
  | .keysUnsampled .. => 64
  | .headerReceived .. => 32
  | _ => 0

/-- Let `Refines s σ`. Then `sendLen s = seedLen σ`. -/
theorem sendLen_of_refines (s : States) (σ : BState) (h : Refines s σ) : sendLen s = seedLen σ := by
  cases s <;> cases σ <;> first | rfl | exact absurd h (by simp [Refines])

/-- Let `ChunkedRel σ st`. Then `seedLen σ` is 64 if `st` is `keysUnsampled`, 32 if `st` is
`headerReceived`, and 0 for each other `st`. -/
theorem seedLen_of_chunkedRel (σ : BState) (st : SMState) (h : ChunkedRel σ st) :
    seedLen σ = match st with
      | .keysUnsampled .. => 64
      | .headerReceived .. => 32
      | _ => 0 := by
  obtain ⟨-, hst⟩ := h
  cases σ <;> cases st <;> first | rfl | exact absurd hst (by simp [SameState])

/-- Let `pk := (keyGenOf t).1`, `hdr := pk.1.1`, `tag := codeAuth.macHeader a ep hdr` and
`ch := (EncoderState.init codeParams.ecpHdr (hdr, tag)).nextChunk`. Then `keysUnsampledOut ep a t`
is `⟨⟨ep, .hdr ch.1⟩, ep - 1, none, .keysSampled ⟨ep, a, pk, (keyGenOf t).2⟩ ch.2⟩`. This is the
value of `Chunked.send` in `keysUnsampled ⟨ep, a⟩` when key generation samples `t`
(`send_keysUnsampled_eq`). -/
noncomputable def keysUnsampledOut (ep : ℕ) (a : Auth) (t : B 64) :
    SPQR.Chunked.SendResult codeParams Braid.Auth :=
  let pk := (keyGenOf t).1
  let hdr : B 64 := pk.1.1
  let tag := codeAuth.macHeader a ep hdr
  let ch := (EncoderState.init codeParams.ecpHdr (hdr, tag)).nextChunk
  ⟨⟨ep, .hdr ch.1⟩, ep - 1, none, .keysSampled ⟨ep, a, pk, (keyGenOf t).2⟩ ch.2⟩

/-- `Chunked.send` in `keysUnsampled ⟨ep, a⟩` samples `t` with `sampleB 64` and returns
`keysUnsampledOut ep a t`. -/
theorem send_keysUnsampled_eq (ep : ℕ) (a : Auth) :
    SPQR.Chunked.send codeParams codeAuth (.keysUnsampled ⟨ep, a⟩) =
      (do let t ← sampleB 64; pure (keysUnsampledOut ep a t)) := by
  simp only [SPQR.Chunked.send, SPQR.EkSender.sendHeader, codeParams, codeKem, keysUnsampledOut,
    bind_assoc, pure_bind]
  rfl

/-- Let `ChunkedRel σ (.keysUnsampled ⟨ep, a⟩)` and `ep < 2 ^ 64`. Then, for every `t : B 64`,
`SendAgree (Braid.send codePrims σ t.1) (keysUnsampledOut ep a t)`. This is transition (1). -/
theorem keysUnsampled_agree (ep : ℕ) (a : Auth) (σ : BState)
    (hrel : ChunkedRel σ (.keysUnsampled ⟨ep, a⟩)) (h64 : ep < 2 ^ 64) (t : B 64) :
    SendAgree (Braid.send codePrims σ t.1) (keysUnsampledOut ep a t) := by
  obtain ⟨hmk, hst⟩ := hrel
  rcases σ with ⟨e, a'⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp only [SameState] at hst
  obtain ⟨rfl, rfl⟩ := hst
  simp only [authOf] at hmk
  obtain ⟨h1, h2, h3⟩ := keyGen_lengths t.1
  have hM := macHdr_length a' h64 (codePrims.keyGen t.1).2.1 hmk (by rw [h2]; omega)
  have henc := encRel_init (by decide) (by decide) (by decide) (pairForm 64 32 3 rfl)
    (fit 64 (codePrims.keyGen t.1).2.1,
      fit 32 (Auth.macHdr codePrims a' e (fit 64 (codePrims.keyGen t.1).2.1).1))
    ((codePrims.keyGen t.1).2.1 ++ Auth.macHdr codePrims a' e (codePrims.keyGen t.1).2.1)
    (by simp only [pairForm, fit_of_length h2, fit_of_length hM])
  obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 3 _ _ hdrCodec (by decide) _ _ henc
  simp only [Braid.send, hnc]
  exact ⟨⟨hmk, rfl, rfl, (fit_of_length h1).symm, (fit_of_length h2).symm,
    (fit_of_length h3).symm, hrel'⟩, rfl, hc, rfl, rfl⟩

/-- Let `o := encaps1Of hdr t`, `ik := codeParams.kdfOK o.2.2 ep` and
`ch := (EncoderState.init codeParams.ecpCt1 o.2.1).nextChunk`, and let
`st := ⟨ep, codeAuth.update a ep ik, hdr, o.1, o.2.1⟩`. Then `headerReceivedOut ep a hdr dec t`
is `⟨⟨ep, .ct1 ch.1⟩, ep - 1, some (ep, ik), .ct1Sampled st ch.2 dec⟩`. This is the value of
`Chunked.send` in `headerReceived ⟨ep, a, hdr⟩ dec` when `Encaps1` samples `t`
(`send_headerReceived_eq`). -/
noncomputable def headerReceivedOut (ep : ℕ) (a : Auth) (hdr : B 64)
    (dec : encoding.polynomial.PolyDecoder) (t : B 32) :
    SPQR.Chunked.SendResult codeParams Braid.Auth :=
  let o := encaps1Of hdr t
  let ik := codeParams.kdfOK o.2.2 ep
  let ch := (EncoderState.init codeParams.ecpCt1 o.2.1).nextChunk
  ⟨⟨ep, .ct1 ch.1⟩, ep - 1, some (ep, ik),
    .ct1Sampled ⟨ep, codeAuth.update a ep ik, hdr, o.1, o.2.1⟩ ch.2 dec⟩

/-- `Chunked.send` in `headerReceived ⟨ep, a, hdr⟩ dec` samples `t` with `sampleB 32` and returns
`headerReceivedOut ep a hdr dec t`. -/
theorem send_headerReceived_eq (ep : ℕ) (a : Auth) (hdr : B 64)
    (dec : encoding.polynomial.PolyDecoder) :
    SPQR.Chunked.send codeParams codeAuth (.headerReceived ⟨ep, a, hdr⟩ dec) =
      (do let t ← sampleB 32; pure (headerReceivedOut ep a hdr dec t)) := by
  simp only [SPQR.Chunked.send, SPQR.CtSender.sendCt1, codeParams, codeInc, encaps1Fn,
    headerReceivedOut, bind_assoc, pure_bind]

/-- Let `ChunkedRel σ (.headerReceived ⟨ep, a, hdr⟩ dec)` and `ep < 2 ^ 64`. Then, for every
`t : B 32`, `SendAgree (Braid.send codePrims σ t.1) (headerReceivedOut ep a hdr dec t)`. This is
transition (7). -/
theorem headerReceived_agree (ep : ℕ) (a : Auth) (hdr : B 64)
    (dec : encoding.polynomial.PolyDecoder) (σ : BState)
    (hrel : ChunkedRel σ (.headerReceived ⟨ep, a, hdr⟩ dec)) (h64 : ep < 2 ^ 64) (t : B 32) :
    SendAgree (Braid.send codePrims σ t.1) (headerReceivedOut ep a hdr dec t) := by
  obtain ⟨hmk, hst⟩ := hrel
  rcases σ with _ | _ | _ | _ | _ | _ | ⟨e, a', hdr', d⟩ | _ | _ | _ | _ <;>
    simp only [SameState] at hst
  obtain ⟨rfl, rfl, rfl, rfl, hwf⟩ := hst
  obtain ⟨h1, h2, h3⟩ := encaps1_lengths hdr.1 t.1 hdr.2
  have hkdf := codePrims_kdfOk_length (codePrims.encaps1 hdr.1 t.1).2.2 h64
  have hik : (codeParams.kdfOK (encaps1Of hdr t).2.2 e).1 =
      codePrims.kdfOk (codePrims.encaps1 hdr.1 t.1).2.2 e := by
    show (fit 32 (codePrims.kdfOk (fit 32 (codePrims.encaps1 hdr.1 t.1).2.2).1 e)).1 = _
    rw [fit_of_length h3, fit_of_length hkdf]
  have henc := encRel_init (by decide) (by decide) (by decide) (bytesForm 30)
    (fit 960 (codePrims.encaps1 hdr.1 t.1).2.1) (codePrims.encaps1 hdr.1 t.1).2.1
    (fit_of_length h2)
  obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 30 _ _ ct1Codec (by decide) _ _ henc
  simp only [Braid.send, hnc]
  refine ⟨⟨auth_update_macKey_length _ h64 _, rfl, ?_, rfl, (fit_of_length h1).symm,
    (fit_of_length h2).symm, hrel', rfl, hwf⟩, rfl, hc, ?_, rfl⟩
  · show _ = Auth.update codePrims a' e (codeParams.kdfOK (encaps1Of hdr t).2.2 e).1
    rw [hik]
  · show _ = some (e, (codeParams.kdfOK (encaps1Of hdr t).2.2 e).1)
    rw [hik]

/-- Assume `BridgeObligations`. Let `ReachParty s n`, `s.epochOf.val + 1 < 2 ^ 64` and
`RA s st`.
Then `RelTriple (codeSendA s) ((smScheme sampleInitKey).sendA st) (SendRel RA RM)`.

If `sendLen s` is 64 or 32, both computations sample with `sampleB (sendLen s)`, and the coupling
is the identity on the sample. If `sendLen s = 0`, both computations are pure. -/
theorem send_chunked (hB : BridgeObligations) (sampleInitKey : ProbComp InitKey) (s : States)
    (n : ℕ) (st : SMState) (hreach : ReachParty s n) (hep : s.epochOf.val + 1 < 2 ^ 64)
    (hRA : RA s st) :
    RelTriple (codeSendA s) ((smScheme sampleInitKey).sendA st) (SendRel RA RM) := by
  obtain ⟨σ, hσ, hrel⟩ := hRA
  have h64 : st.epoch < 2 ^ 64 := by rw [← hrel.2.epoch, hσ.epoch]; omega
  have hlen := (sendLen_of_refines s σ hσ).trans (seedLen_of_chunkedRel σ st hrel)
  change RelTriple (codeSendA s)
    (do let r ← SPQR.Chunked.send codeParams codeAuth st
        pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))) _
  rw [codeSendA_eq]
  by_cases hs : (∃ c, st = .keysUnsampled c) ∨ ∃ c d, st = .headerReceived c d
  · rcases hs with ⟨⟨ep, a⟩, rfl⟩ | ⟨⟨ep, a, hdr⟩, dec, rfl⟩
    · rw [send_keysUnsampled_eq, sampleBuf_of_sendLen_64 s hlen, bind_assoc, bind_assoc]
      refine relTriple_bind (relTriple_refl _) fun t t' (h : t = t') => ?_
      subst h
      rw [pure_bind, pure_bind]
      refine relTriple_pure_pure (sendRel_of_braid hB s n σ hreach hσ hep _
        ((sliceOf_length t _).trans hlen.symm) _ ?_)
      rw [sliceOf_val]
      exact keysUnsampled_agree ep a σ hrel h64 t
    · rw [send_headerReceived_eq ep a hdr dec, sampleBuf_of_sendLen_32 s hlen, bind_assoc,
        bind_assoc]
      refine relTriple_bind (relTriple_refl _) fun t t' (h : t = t') => ?_
      subst h
      rw [pure_bind, pure_bind]
      refine relTriple_pure_pure (sendRel_of_braid hB s n σ hreach hσ hep _
        ((sliceOf_length t _).trans hlen.symm) _ ?_)
      rw [sliceOf_val]
      exact headerReceived_agree ep a hdr dec σ hrel h64 t
  · have h0 : sendLen s = 0 := by
      rw [hlen]
      cases st <;> first | rfl | exact absurd ⟨_, rfl⟩ (not_or.mp hs).1 |
        exact absurd ⟨_, _, rfl⟩ (not_or.mp hs).2
    obtain ⟨res, hres, hagree⟩ := braid_send_pure σ st hrel (not_or.mp hs)
    rw [hres, sampleBuf_of_sendLen_zero s h0, pure_bind, pure_bind]
    exact relTriple_pure_pure (sendRel_of_braid hB s n σ hreach hσ hep noBuf h0.symm res
      (hagree _))

/-! ## Initial states -/

/-- For every `k : InitKey`, `RA (initAState k) (SPQR.Chunked.initA codeParams codeAuth k)`. -/
theorem ra_initA (k : InitKey) :
    RA (initAState k) (SPQR.Chunked.initA codeParams codeAuth k) :=
  ⟨_, (init_refines codePrims codePrims_agreesSeeded.toCodeAgrees k.1).1 _ (init_a_eq k),
    auth_update_macKey_length _ (by norm_num) _, rfl, rfl⟩

/-- For every `k : InitKey`, `RA (initBState k) (SPQR.Chunked.initB codeParams codeAuth k)`. -/
theorem ra_initB (k : InitKey) :
    RA (initBState k) (SPQR.Chunked.initB codeParams codeAuth k) := by
  refine ⟨_, (init_refines codePrims codePrims_agreesSeeded.toCodeAgrees k.1).2 _ (init_b_eq k),
    auth_update_macKey_length _ (by norm_num) _, rfl, rfl, ?_, ?_⟩
  · rw [codePrims_headerSize, codePrims_macSize]
    exact codePrims_decoderNew 3 (by decide) hdrCodec
  · rw [codePrims_headerSize, codePrims_macSize, show 64 + 32 = 32 * 3 from rfl,
      codePrims_decoderNew 3 (by decide) hdrCodec]
    exact decWF_empty 3 (by decide) hdrCodec

end SpqrBridge
