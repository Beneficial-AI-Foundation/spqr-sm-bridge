/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.ChunkedSend

/-!
# `send_chunked`: every send arm

The two sampling arms (`keysUnsampled`, `headerReceived`), the coupling of the code's send with
`Chunked.send` (`send_chunked`), and the relation of the initial states (`ra_initA`,
`ra_initB`).
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming
open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational

/-- A fresh encoder of the bytes of a payload is related to the secure-messaging encoder at
counter `0`. -/
theorem encRel_init {M : Type} {K : ℕ} (hK : 0 < K) (hKN : K ≤ 2 ^ 16) (hK15 : K ≤ 2 ^ 15)
    (f : ByteForm M K) (p : M) (l : Bytes) (hl : (f.toBytes p).1 = l) :
    EncRel K hK hKN (codecOf f) (codePrims.encode l)
      (EncoderState.init (L2.ecp K hK hKN (codecOf f)) p) := by
  subst hl
  have h := codePrims_encode f hK15 p
  exact ⟨rfl, h.1, by rw [h.2]; rfl⟩

/-- The result of `Chunked.send` in `keysUnsampled` for the tape `t`. -/
noncomputable def keysUnsampledOut (ep : ℕ) (a : Auth) (t : B 64) :
    SPQR.Chunked.SendResult codeParams Braid.Auth :=
  let pk := (keyGenOf t).1
  let hdr : B 64 := pk.1.1
  let tag := codeAuth.macHeader a ep hdr
  let ch := (EncoderState.init codeParams.ecpHdr (hdr, tag)).nextChunk
  ⟨⟨ep, .hdr ch.1⟩, ep - 1, none, .keysSampled ⟨ep, a, pk, (keyGenOf t).2⟩ ch.2⟩

/-- `Chunked.send` in `keysUnsampled` samples a tape and is otherwise pure. -/
theorem send_keysUnsampled_eq (ep : ℕ) (a : Auth) :
    SPQR.Chunked.send codeParams codeAuth (.keysUnsampled ⟨ep, a⟩) =
      (do let t ← sampleTape; pure (keysUnsampledOut ep a t)) := by
  simp only [SPQR.Chunked.send, SPQR.EkSender.sendHeader, bind_assoc, pure_bind]
  have hk : codeParams.kem.keygen = (do let t ← sampleTape; pure (keyGenOf t)) := rfl
  rw [hk, bind_assoc]
  refine congrArg (sampleTape >>= ·) (funext fun t => ?_)
  exact pure_bind _ _

/-- The `keysUnsampled` send arm (transition (1)): `Braid.send` on the 64-byte tape agrees with
`Chunked.send` on the same tape. -/
theorem keysUnsampled_agree (ep : ℕ) (a : Auth) (σ : BState)
    (hrel : ChunkedRel σ (.keysUnsampled ⟨ep, a⟩)) (h64 : ep < 2 ^ 64) (t : B 64) :
    SendAgree (Braid.send codePrims σ (t.1.take (seedLen σ))) (keysUnsampledOut ep a t) := by
  obtain ⟨hmk, hst⟩ := hrel
  rcases σ with ⟨e, a'⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp only [SameState] at hst
  obtain ⟨rfl, rfl⟩ := hst
  simp only [authOf] at hmk
  have ht : t.1.take (seedLen (.keysUnsampled e a' : BState)) = t.1 :=
    List.take_of_length_le (by rw [t.2]; rfl)
  rw [ht]
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

/-- The result of `Chunked.send` in `headerReceived` for the tape `t`. -/
noncomputable def headerReceivedOut (ep : ℕ) (a : Auth) (hdr : B 64)
    (dec : encoding.polynomial.PolyDecoder) (t : B 64) :
    SPQR.Chunked.SendResult codeParams Braid.Auth :=
  let o := encaps1Of hdr t
  let ik := codeParams.kdfOK o.2.2 ep
  let ch := (EncoderState.init codeParams.ecpCt1 o.2.1).nextChunk
  ⟨⟨ep, .ct1 ch.1⟩, ep - 1, some (ep, ik),
    .ct1Sampled ⟨ep, codeAuth.update a ep ik, hdr, o.1, o.2.1⟩ ch.2 dec⟩

/-- `Chunked.send` in `headerReceived` samples a tape and is otherwise pure. -/
theorem send_headerReceived_eq (ep : ℕ) (a : Auth) (hdr : B 64)
    (dec : encoding.polynomial.PolyDecoder) :
    SPQR.Chunked.send codeParams codeAuth (.headerReceived ⟨ep, a, hdr⟩ dec) =
      (do let t ← sampleTape; pure (headerReceivedOut ep a hdr dec t)) := by
  simp only [SPQR.Chunked.send, SPQR.CtSender.sendCt1, bind_assoc, pure_bind]
  have hk : codeParams.inc.encaps1 hdr = (do let t ← sampleTape; pure (encaps1Of hdr t)) := rfl
  rw [hk, bind_assoc]
  refine congrArg (sampleTape >>= ·) (funext fun t => ?_)
  exact pure_bind _ _

/-- `Encaps1` reads only the first 32 bytes of its randomness. -/
theorem msgOfBytes_take (r : Bytes) : msgOfBytes (r.take 32) = msgOfBytes r := by
  funext i
  simp only [msgOfBytes, List.getD_eq_getElem?_getD, List.getElem?_take, i.2, ↓reduceIte]

/-- The `headerReceived` send arm (transition (7)): `Braid.send` on the first 32 bytes of the tape
agrees with `Chunked.send` on the tape. -/
theorem headerReceived_agree (ep : ℕ) (a : Auth) (hdr : B 64)
    (dec : encoding.polynomial.PolyDecoder) (σ : BState)
    (hrel : ChunkedRel σ (.headerReceived ⟨ep, a, hdr⟩ dec)) (h64 : ep < 2 ^ 64) (t : B 64) :
    SendAgree (Braid.send codePrims σ (t.1.take (seedLen σ)))
      (headerReceivedOut ep a hdr dec t) := by
  obtain ⟨hmk, hst⟩ := hrel
  rcases σ with _ | _ | _ | _ | _ | _ | ⟨e, a', hdr', d⟩ | _ | _ | _ | _ <;>
    simp only [SameState] at hst
  obtain ⟨rfl, rfl, rfl, rfl, hwf⟩ := hst
  have he1 : codePrims.encaps1 hdr.1 (t.1.take 32) = codePrims.encaps1 hdr.1 t.1 := by
    show seededEncaps1 hdr.1 (t.1.take 32) = seededEncaps1 hdr.1 t.1
    simp only [seededEncaps1, msgOfBytes_take]
  simp only [seedLen]
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
  simp only [Braid.send, he1, hnc]
  refine ⟨⟨auth_update_macKey_length _ h64 _, rfl, ?_, rfl, (fit_of_length h1).symm,
    (fit_of_length h2).symm, hrel', rfl, hwf⟩, rfl, hc, ?_, rfl⟩
  · show _ = Auth.update codePrims a' e (codeParams.kdfOK (encaps1Of hdr t).2.2 e).1
    rw [hik]
  · show _ = some (e, (codeParams.kdfOK (encaps1Of hdr t).2.2 e).1)
    rw [hik]

/-- `send_chunked`, the send obligation of the transfer: for a reachable code state with epoch
headroom related to a secure-messaging state, the code's send with a fresh tape and
`Chunked.send` are coupled on `SendRel RA RM`. In the two sampling states the coupling is the
identity on the tape; elsewhere `Chunked.send` is pure and the code ignores its tape
(`relTriple_sampleTape_pure`). It uses the `BridgeObligations` fields `send_total` and
`send_refines_tape`, and the theorems `codeSend_key_length` and `next_chunk_wrap`. -/
theorem send_chunked (hB : BridgeObligations) (sampleInitKey : ProbComp InitKey) (s : States)
    (n : ℕ) (st : SMState) (hreach : ReachParty s n) (hep : s.epochOf.val + 1 < 2 ^ 64)
    (hRA : RA s st) :
    RelTriple (codeSendA s) ((smScheme sampleInitKey).sendA st) (SendRel RA RM) := by
  obtain ⟨σ, hσ, hrel⟩ := hRA
  have h64 : st.epoch < 2 ^ 64 := by rw [← hrel.2.epoch, hσ.epoch]; omega
  change RelTriple (do let t ← sampleTape; pure (sendStep s t.1))
    (do let r ← SPQR.Chunked.send codeParams codeAuth st
        pure (some (r.outputKey, r.msg, r.sendingEpoch, r.state))) _
  by_cases hs : (∃ c, st = .keysUnsampled c) ∨ ∃ c d, st = .headerReceived c d
  · rcases hs with ⟨⟨ep, a⟩, rfl⟩ | ⟨⟨ep, a, hdr⟩, dec, rfl⟩
    · rw [send_keysUnsampled_eq, bind_assoc]
      refine relTriple_bind (relTriple_refl _) fun t t' (h : t = t') => ?_
      subst h
      rw [pure_bind]
      exact relTriple_pure_pure (sendRel_of_braid hB s n σ hreach hσ hep t _
        (keysUnsampled_agree ep a σ hrel h64 t))
    · rw [send_headerReceived_eq ep a hdr dec, bind_assoc]
      refine relTriple_bind (relTriple_refl _) fun t t' (h : t = t') => ?_
      subst h
      rw [pure_bind]
      exact relTriple_pure_pure (sendRel_of_braid hB s n σ hreach hσ hep t _
        (headerReceived_agree ep a hdr dec σ hrel h64 t))
  · obtain ⟨res, hres, hagree⟩ := braid_send_pure σ st hrel (not_or.mp hs)
    rw [hres, pure_bind]
    exact relTriple_sampleTape_pure (fun t => sendStep s t.1) _ _ fun t =>
      sendRel_of_braid hB s n σ hreach hσ hep t res (hagree _)

/-! ## Initial states -/

/-- The initial states are related: A's. -/
theorem ra_initA (k : InitKey) :
    RA (initAState k) (SPQR.Chunked.initA codeParams codeAuth k) :=
  ⟨_, (init_refines codePrims codePrims_agreesSeeded.toCodeAgrees k.1).1 _ (init_a_eq k),
    auth_update_macKey_length _ (by norm_num) _, rfl, rfl⟩

/-- The initial states are related: B's. -/
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
