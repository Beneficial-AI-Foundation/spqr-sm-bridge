/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.ChunkedFacts

/-!
# The receive arms of `Braid` → `Chunked`

`recvRel_of_braid` reduces the one-sided receive obligation `RecvRel RA` to a step of the
abstract machine: when `Chunked.recv` accepts, `Braid.receive` accepts with a related state and
the same key. The code side then follows from the `BridgeObligations` fields `recv_complete` and
`recv_key_length`.

Each `recv_*` theorem proves that machine step for one arm of `Chunked.recv`.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming

/-- Let `s` be reachable and refine `σ`, with message epoch headroom, and let the messages be
related. Assume that whenever `Chunked.recv` accepts, `Braid.receive` accepts with a related
state, the same key and the report `msg'.epoch - 1`. Then the code's receive and
secure-messaging's receive are related by `RecvRel RA`. -/
theorem recvRel_of_braid (hB : BridgeObligations) (s : States) (n : ℕ) (σ : BState)
    (st : SMState) (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym)
    (hreach : ReachParty s n) (hσ : Refines s σ) (hep : msg.epoch.val + 1 < 2 ^ 64)
    (hRM : RM msg msg')
    (h : ∀ r, SPQR.Chunked.recv codeParams codeAuth st msg' = .ok r →
      ∃ σ', Braid.receive codePrims σ (absMsg msg) =
          some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
        ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1) :
    RecvRel RA (recvStep s msg) (SPQR.recvSCKA codeParams codeAuth st msg') := by
  unfold SPQR.recvSCKA
  split
  · exact trivial
  · rename_i r hr
    obtain ⟨σ', hrecv, hrel, hepr⟩ := h r hr
    obtain ⟨out, hout, hσ', hkey⟩ := hB.recv_complete s n σ σ' msg _ hreach hσ hep hrecv
    have hlen := hB.recv_key_length s msg out hout
    simp only [recvStep, hout, Option.bind_eq_bind, Option.bind_some]
    rcases hk : out.key with _ | es
    · rw [hk] at hkey
      simp only [Option.map_none] at hkey
      simp only [keyOf, Option.bind_some, Option.pure_def, RecvRel]
      refine ⟨?_, ?_, ⟨σ', hσ', hrel⟩⟩
      · rcases hrk : r.outputKey with _ | ⟨e, x⟩
        · rfl
        · rw [hrk] at hkey; simp at hkey
      · rw [hepr, hRM.1]
    · have h32 := hlen es (by rw [hk]; rfl)
      rw [hk] at hkey
      simp only [keyOf, h32, ↓reduceDIte, Option.bind_some, Option.pure_def, RecvRel]
      refine ⟨?_, ?_, ⟨σ', hσ', hrel⟩⟩
      · rcases hrk : r.outputKey with _ | ⟨e, x⟩
        · rw [hrk] at hkey; simp at hkey
        · rw [hrk] at hkey
          simp only [Option.map_some, Option.some.injEq, absKey, Prod.mk.injEq] at hkey
          congr 2
          · exact hkey.1.symm
          · exact Subtype.ext hkey.2.symm
      · rw [hepr, hRM.1]

/-- `EkSender.recvCt2` over the code's parameters: decapsulate, derive the epoch key, update the
authenticator and compare the tag with the recomputed MAC. -/
theorem recvCt2_code (ep : ℕ) (a : Auth) (sk : B 2400) (c1 : B 960) (c2 : B 128) (tag : B 32) :
    SPQR.EkSender.recvCt2 codeParams.inc codeAuth codeParams.kdfOK codeParams.hDet
      (⟨ep, a, sk, c1⟩ : SPQR.EkSender.EkSentCt1Received codeParams.inc Auth) c2 tag =
    if tag = fit 32 (Auth.macCt codePrims (Auth.update codePrims a ep
        (kdfOKTotal (fit 32 (codePrims.decaps sk.1 c1.1 c2.1)) ep).1) ep (c1.1 ++ c2.1)) then
      some (⟨ep + 1, Auth.update codePrims a ep
        (kdfOKTotal (fit 32 (codePrims.decaps sk.1 c1.1 c2.1)) ep).1⟩,
        (ep, kdfOKTotal (fit 32 (codePrims.decaps sk.1 c1.1 c2.1)) ep))
    else none := by
  have hd : codeParams.hDet.decapsDet sk (codeParams.inc.splitC.symm (c1, c2)) =
      some (fit 32 (codePrims.decaps sk.1 c1.1 c2.1)) := rfl
  simp only [SPQR.EkSender.recvCt2, hd]
  exact if_congr (by simp only [codeAuth, decide_eq_true_eq]; rfl) rfl rfl

/-- The `ct2` arm in `ekSentCt1Received` (transitions (4)–(5) of §2.5): when `Chunked.recv`
accepts a `ct2` chunk at the state's epoch, `Braid.receive` accepts with a related state, the same
key and the report `epoch - 1`. This covers the decoder that completes, with its key output, its
epoch advance and its MAC check, and the decoder that does not. -/
theorem recv_ekSentCt1Received_ct2 (hsz : MlkemSizes) (σ : BState) (ep : ℕ) (a : Auth)
    (sk : B 2400) (c1 : B 960) (dec : encoding.polynomial.PolyDecoder)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.ekSentCt1Received ⟨ep, a, sk, c1⟩ dec)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ct2 c) (hep : msg'.epoch = ep) (h64 : ep < 2 ^ 64)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.ekSentCt1Received ⟨ep, a, sk, c1⟩ dec) msg' =
      .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  rcases σ with _ | _ | _ | _ | ⟨e, a', dk, ct1, d⟩ | _ | _ | _ | _ | _ | _ <;>
    simp only [ChunkedRel] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, rfl, hwf⟩ := hrel
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  rw [hpay] at hpr
  cases pay' <;> simp only [PayloadRel] at hpr
  subst hpr
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', res, hres, hcm, hsd, hlen⟩ :=
    decStep 5 (by decide) ct2Codec d hwf c
  simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false] at hr
  simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl, ite_false,
    Braid.receiveEq]
  rw [show codeParams.decCt2.addChunk _ (chunkOfCode c) = d' from hsa,
    show codeParams.decCt2.decodedPayload d' = _ from hsd] at hr
  rw [hca, hcm]
  rcases res with _ | v
  · simp only [Option.bind_none, Except.ok.injEq] at hr
    subst hr
    exact ⟨_, rfl, ⟨rfl, rfl, rfl, rfl, rfl, hwf'⟩, rfl⟩
  · have hv : v.val.length = 32 * 5 := hlen v rfl
    have ht : (v.val.take 128).length = 128 := by simp [hv]
    have hd : (v.val.drop 128).length = 32 := by simp [hv]
    simp only [Option.bind_some, ct2Codec, pairForm_parse 128 32 5 rfl v.val hv] at hr
    erw [recvCt2_code] at hr
    have hdec := codePrims_decaps_length _ _ _ sk.2 c1.2 ht
    have hkdf := codePrims_kdfOk_length (codePrims.decaps sk.1 c1.1 (v.val.take 128)) h64
    have hk : (kdfOKTotal (fit 32 (codePrims.decaps sk.1 c1.1 (v.val.take 128))) ep').1 =
        codePrims.kdfOk (codePrims.decaps sk.1 c1.1 (v.val.take 128)) ep' := by
      rw [kdfOKTotal, fit_of_length hdec, fit_of_length hkdf]
    have hmac := macCt_length (Auth.update codePrims a' ep'
      (codePrims.kdfOk (codePrims.decaps sk.1 c1.1 (v.val.take 128)) ep')) h64 (c1.1 ++ v.val.take 128)
      (auth_update_macKey_length _ h64 _) (by simp only [List.length_append, c1.2, ht]; omega)
    simp only [fit_of_length ht, hk, fit_eq_fit_iff hd hmac] at hr
    simp only [Option.map_some, codePrims_ct2Size hsz]
    by_cases hm : v.val.drop 128 = Auth.macCt codePrims (Auth.update codePrims a' ep'
      (codePrims.kdfOk (codePrims.decaps sk.1 c1.1 (v.val.take 128)) ep')) ep' (c1.1 ++ v.val.take 128)
    · simp only [hm, ↓reduceIte, Except.ok.injEq] at hr ⊢
      subst hr
      refine ⟨.noHeaderReceived (ep' + 1) (Auth.update codePrims a' ep'
        (codePrims.kdfOk (codePrims.decaps sk.1 c1.1 (v.val.take 128)) ep')) (codePrims.decoderNew (codePrims.headerSize +
        codePrims.macSize)), ?_, ?_, rfl⟩
      · rw [← hk]; rfl
      refine ⟨rfl, rfl, ?_, ?_⟩
      · rw [codePrims_headerSize, codePrims_macSize]
        exact codePrims_decoderNew 3 (by decide) hdrCodec
      · rw [codePrims_headerSize, codePrims_macSize, codePrims_decoderNew 3 (by decide) hdrCodec]
        exact decWF_empty 3 (by decide) hdrCodec
    · simp only [hm, ↓reduceIte] at hr
      cases hr

/-- The feasibility test of W2: the one-sided receive relation for a `ct2` chunk in
`ekSentCt1Received`. -/
theorem recvRel_ekSentCt1Received_ct2 (hB : BridgeObligations) (s : States) (n : ℕ) (ep : ℕ)
    (a : Auth) (sk : B 2400) (c1 : B 960) (dec : encoding.polynomial.PolyDecoder)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hreach : ReachParty s n) (hep : msg.epoch.val + 1 < 2 ^ 64)
    (hRA : RA s (.ekSentCt1Received ⟨ep, a, sk, c1⟩ dec)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ct2 c) (hepoch : msg'.epoch = ep) :
    RecvRel RA (recvStep s msg)
      (SPQR.recvSCKA codeParams codeAuth (.ekSentCt1Received ⟨ep, a, sk, c1⟩ dec) msg') := by
  obtain ⟨σ, hσ, hrel⟩ := hRA
  have h64 : ep < 2 ^ 64 := by rw [← hepoch, ← hRM.1]; omega
  exact recvRel_of_braid hB s n σ _ msg msg' hreach hσ hep hRM fun r hr =>
    recv_ekSentCt1Received_ct2 hB.mlkem_sizes σ ep a sk c1 dec msg msg' c hrel hRM hpay hepoch h64
      r hr

end SpqrBridge
