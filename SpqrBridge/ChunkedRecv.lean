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
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | _ | _ | ⟨e, a', dk, ct1, d⟩ | _ | _ | _ | _ | _ | _ <;>
    simp only [SameState] at hrel
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
    exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, rfl, hwf'⟩, rfl⟩
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
      refine ⟨auth_update_macKey_length _ h64 _, rfl, rfl, ?_, ?_⟩
      · rw [codePrims_headerSize, codePrims_macSize]
        exact codePrims_decoderNew 3 (by decide) hdrCodec
      · rw [codePrims_headerSize, codePrims_macSize, codePrims_decoderNew 3 (by decide) hdrCodec]
        exact decWF_empty 3 (by decide) hdrCodec
    · simp only [hm, ↓reduceIte] at hr
      cases hr

/-- The `ct1` arm in `keysSampled` (transition (2)): the first `ct1` chunk starts the `ct1`
decoder and the `ek` encoder. -/
theorem recv_keysSampled_ct1 (hsz : MlkemSizes) (σ : BState) (ep : ℕ) (a : Auth) (pk : PK)
    (sk : B 2400) (es : EncoderState (B 64 × B 32) L2.Sym)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.keysSampled ⟨ep, a, pk, sk⟩ es)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ct1 c) (hep : msg'.epoch = ep)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.keysSampled ⟨ep, a, pk, sk⟩ es) msg' = .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | ⟨e, a', dk, hdr, ek, enc⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -⟩ := hrel
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  rw [hpay] at hpr
  cases pay' <;> simp only [PayloadRel] at hpr
  subst hpr
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', -⟩ :=
    decStep 30 (by decide) ct1Codec _ (decWF_empty 30 (by decide) ct1Codec) c
  simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false,
    Except.ok.injEq] at hr
  subst hr
  simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl, ite_false,
    Braid.receiveEq]
  rw [codePrims_ct1Size hsz, show 960 = 32 * 30 from rfl, codePrims_decoderNew 30 (by decide) ct1Codec, hca]
  have henc := codePrims_encode (bytesForm 36) (by decide) pk.1.2
  exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, hsa.symm, hwf', rfl, henc.1, henc.2⟩, trivial⟩

/-- The `ct1` arm in `headerSent` (transition (3)): a `ct1` chunk that completes or does not
complete the decoder. -/
theorem recv_headerSent_ct1 (σ : BState) (ep : ℕ) (a : Auth) (sk : B 2400)
    (es : EncoderState (B (32 * 36)) L2.Sym) (dec : encoding.polynomial.PolyDecoder)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.headerSent ⟨ep, a, sk⟩ es dec)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ct1 c) (hep : msg'.epoch = ep)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.headerSent ⟨ep, a, sk⟩ es dec) msg' = .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | ⟨e, a', dk, d, enc⟩ | _ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, hwf, henc⟩ := hrel
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  rw [hpay] at hpr
  cases pay' <;> simp only [PayloadRel] at hpr
  subst hpr
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', res, hres, hcm, hsd, hlen⟩ :=
    decStep 30 (by decide) ct1Codec d hwf c
  simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false] at hr
  simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl, ite_false,
    Braid.receiveEq]
  rw [show codeParams.decCt1.addChunk _ (chunkOfCode c) = d' from hsa,
    show codeParams.decCt1.decodedPayload d' = _ from hsd] at hr
  rw [hca, hcm]
  rcases res with _ | v
  · simp only [Option.bind_none, Except.ok.injEq] at hr
    subst hr
    exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, hwf', henc⟩, rfl⟩
  · have hv : v.val.length = 32 * 30 := hlen v rfl
    simp only [Option.bind_some, ct1Codec, bytesForm_parse 30 v.val hv, Except.ok.injEq] at hr
    subst hr
    exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, henc⟩, rfl⟩

/-- The `ct2` arm in `ct1Received` (transition (4)): the first `ct2` chunk starts the `ct2`
decoder. -/
theorem recv_ct1Received_ct2 (hsz : MlkemSizes) (σ : BState) (ep : ℕ) (a : Auth) (sk : B 2400)
    (c1 : B 960) (es : EncoderState (B (32 * 36)) L2.Sym)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.ct1Received ⟨ep, a, sk, c1⟩ es)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ct2 c) (hep : msg'.epoch = ep)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.ct1Received ⟨ep, a, sk, c1⟩ es) msg' = .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | _ | ⟨e, a', dk, ct1, enc⟩ | _ | _ | _ | _ | _ | _ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hrel
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  rw [hpay] at hpr
  cases pay' <;> simp only [PayloadRel] at hpr
  subst hpr
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', -⟩ :=
    decStep 5 (by decide) ct2Codec _ (decWF_empty 5 (by decide) ct2Codec) c
  simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false,
    Except.ok.injEq] at hr
  subst hr
  simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl, ite_false,
    Braid.receiveEq]
  rw [codePrims_ct2Size hsz, codePrims_macSize, show 128 + 32 = 32 * 5 from rfl,
    codePrims_decoderNew 5 (by decide) ct2Codec, hca]
  exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, hsa.symm, hwf'⟩, trivial⟩

/-- `CtSender.recvHeader` over the code's parameters: compare the tag with the recomputed MAC. -/
theorem recvHeader_code (ep : ℕ) (a : Auth) (hdr : B 64) (tag : B 32) :
    SPQR.CtSender.recvHeader codeParams.inc codeAuth
      (⟨ep, a⟩ : SPQR.CtSender.NoHeaderReceived Auth) hdr tag =
    if tag = fit 32 (Auth.macHdr codePrims a ep hdr.1) then some ⟨ep, a, hdr⟩ else none := by
  simp only [SPQR.CtSender.recvHeader]
  exact if_congr (by simp only [codeAuth, decide_eq_true_eq]) rfl rfl

/-- The `hdr` arm in `noHeaderReceived` (transition (6)): a header chunk that completes or does
not complete the decoder, with the header MAC check. -/
theorem recv_noHeaderReceived_hdr (hsz : MlkemSizes) (σ : BState) (ep : ℕ) (a : Auth)
    (dec : encoding.polynomial.PolyDecoder)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.noHeaderReceived ⟨ep, a⟩ dec)) (hRM : RM msg msg')
    (hpay : msg.payload = .Hdr c) (hep : msg'.epoch = ep) (h64 : ep < 2 ^ 64)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.noHeaderReceived ⟨ep, a⟩ dec) msg' = .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | _ | _ | _ | ⟨e, a', d⟩ | _ | _ | _ | _ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, hwf⟩ := hrel
  simp only [authOf] at hmk
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  rw [hpay] at hpr
  cases pay' <;> simp only [PayloadRel] at hpr
  subst hpr
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', res, hres, hcm, hsd, hlen⟩ :=
    decStep 3 (by decide) hdrCodec d hwf c
  simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false] at hr
  simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl, ite_false,
    Braid.receiveEq]
  rw [show codeParams.decHdr.addChunk _ (chunkOfCode c) = d' from hsa,
    show codeParams.decHdr.decodedPayload d' = _ from hsd] at hr
  rw [hca, hcm]
  rcases res with _ | v
  · simp only [Option.bind_none, Except.ok.injEq] at hr
    subst hr
    exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, hwf'⟩, rfl⟩
  · have hv : v.val.length = 32 * 3 := hlen v rfl
    have ht : (v.val.take 64).length = 64 := by simp [hv]
    have hd : (v.val.drop 64).length = 32 := by simp [hv]
    simp only [Option.bind_some, hdrCodec, pairForm_parse 64 32 3 rfl v.val hv] at hr
    erw [recvHeader_code] at hr
    have hmac := macHdr_length a' h64 (v.val.take 64) hmk (by rw [ht]; omega)
    simp only [fit_of_length ht, fit_eq_fit_iff hd hmac] at hr
    simp only [Option.map_some, codePrims_headerSize]
    by_cases hm : v.val.drop 64 = Auth.macHdr codePrims a' ep' (v.val.take 64)
    · simp only [hm, ↓reduceIte, Except.ok.injEq] at hr ⊢
      subst hr
      refine ⟨.headerReceived ep' a' (v.val.take 64) (codePrims.decoderNew codePrims.ekSize),
        rfl, ⟨hmk, rfl, rfl, ?_, ?_⟩, rfl⟩
      · rw [fit_of_length ht]
      · rw [codePrims_ekSize hsz, show 1152 = 32 * 36 from rfl,
          codePrims_decoderNew 36 (by decide) ekCodec]
        exact ⟨rfl, decWF_empty 36 (by decide) ekCodec⟩
    · simp only [hm, ↓reduceIte] at hr
      cases hr

/-- `Encaps2` on a 2080-byte state and a 1152-byte vector returns 128 bytes. (From the W1
contracts `encaps2_ok` and `encaps2_agree`.) -/
theorem codePrims_encaps2_length (es hdr ek : Bytes) (hes : es.length = 2080)
    (hek : ek.length = 1152) : (codePrims.encaps2 es hdr ek).length = 128 := by
  have hmax := L2.usize_max_ge
  let ekv : alloc.vec.Vec Std.U8 := alloc.vec.Vec.from ek (by omega)
  let esv : alloc.vec.Vec Std.U8 := alloc.vec.Vec.from es (by omega)
  obtain ⟨ct2, h⟩ := encaps2_ok ekv esv
    (by simp [ekv, alloc.vec.Vec.length, alloc.vec.Vec.from_val, hek])
    (by simp [esv, alloc.vec.Vec.length, alloc.vec.Vec.from_val, hes])
  have := encaps2_agree ekv esv ct2 hdr h
  simp only [ekv, esv, alloc.vec.Vec.from_val] at this
  rw [this.1]
  exact this.2

/-- The state that completes stage two (transitions (9), (11), (12)) is related to the `Braid`
state with the `ct2` encoder. -/
theorem completeCt2_rel (ep : ℕ) (a : Auth) (hdr : B 64) (es : B 2080) (c1 : B 960)
    (vec : B 1152) (h64 : ep < 2 ^ 64) (hmk : a.macKey.length = 32) :
    ChunkedRel (.ct2Sampled ep a (ct2Encoder codePrims ep a es.1 c1.1 hdr.1 vec.1))
      (SPQR.Chunked.completeCt2 codeParams codeAuth ⟨ep, a, hdr, es, c1, vec⟩) := by
  have hX := codePrims_encaps2_length es.1 hdr.1 vec.1 es.2 vec.2
  have hM := macCt_length a h64 (c1.1 ++ codePrims.encaps2 es.1 hdr.1 vec.1) hmk
    (by simp only [List.length_append, c1.2, hX]; omega)
  have henc := codePrims_encode (pairForm 128 32 5 rfl) (by decide)
    (fit 128 (codePrims.encaps2 es.1 hdr.1 vec.1),
      fit 32 (Auth.macCt codePrims a ep (c1.1 ++ (fit 128 (codePrims.encaps2 es.1 hdr.1 vec.1)).1)))
  have e1 : codePrims.encode ((pairForm 128 32 5 rfl).toBytes
      (fit 128 (codePrims.encaps2 es.1 hdr.1 vec.1),
        fit 32 (Auth.macCt codePrims a ep (c1.1 ++ (fit 128 (codePrims.encaps2 es.1 hdr.1 vec.1)).1)))).1 =
      ct2Encoder codePrims ep a es.1 c1.1 hdr.1 vec.1 := by
    simp only [pairForm, ct2Encoder, fit_of_length hX, fit_of_length hM]
  rw [e1] at henc
  exact ⟨hmk, rfl, rfl, rfl, henc.1, henc.2⟩

/-- `CtSender.recvVector` over the code's parameters: the code's `ek` check. -/
theorem recvVector_code (ep : ℕ) (a : Auth) (hdr : B 64) (es : B 2080) (c1 : B 960)
    (vec : B 1152) :
    SPQR.CtSender.recvVector codeParams.inc
      (⟨ep, a, hdr, es, c1⟩ : SPQR.CtSender.Ct1Sent codeParams.inc Auth) vec =
    if codePrims.ekMatches hdr.1 vec.1 then some ⟨ep, a, hdr, es, c1, vec⟩ else none := rfl

/-- The `ek` arm in `ct1Sampled` (transition (10)), with the `ek` check. -/
theorem recv_ct1Sampled_ek (σ : BState) (ep : ℕ) (a : Auth) (hdr : B 64)
    (es : B 2080) (c1 : B 960) (ecs : EncoderState (B (32 * 30)) L2.Sym)
    (dec : encoding.polynomial.PolyDecoder)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.ct1Sampled ⟨ep, a, hdr, es, c1⟩ ecs dec)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ek c) (hep : msg'.epoch = ep)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.ct1Sampled ⟨ep, a, hdr, es, c1⟩ ecs dec) msg' =
      .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | _ | _ | _ | _ | _ | ⟨e, a', hdr', es', ct1, enc, d⟩ | _ | _ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, rfl, henc, rfl, hwf⟩ := hrel
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  rw [hpay] at hpr
  cases pay' <;> simp only [PayloadRel] at hpr
  subst hpr
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', res, hres, hcm, hsd, hlen⟩ :=
    decStep 36 (by decide) ekCodec d hwf c
  simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false] at hr
  simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl, ite_false,
    Braid.receiveEq]
  rw [show codeParams.decEk.addChunk _ (chunkOfCode c) = d' from hsa,
    show codeParams.decEk.decodedPayload d' = _ from hsd] at hr
  rw [hca, hcm]
  rcases res with _ | v
  · simp only [Option.bind_none, Except.ok.injEq] at hr
    subst hr
    exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, rfl, henc, rfl, hwf'⟩, rfl⟩
  · have hv : v.val.length = 32 * 36 := hlen v rfl
    simp only [Option.bind_some, ekCodec, bytesForm_parse 36 v.val hv] at hr
    erw [recvVector_code] at hr
    simp only [Option.map_some]
    by_cases hm : codePrims.ekMatches hdr.1 v.val = true
    · simp only [hm, ↓reduceIte, Except.ok.injEq] at hr ⊢
      subst hr
      exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, rfl, rfl, henc⟩, rfl⟩
    · simp only [hm, ↓reduceIte, Bool.false_eq_true] at hr
      cases hr

/-- The `ekCt1Ack` arm in `ct1Sampled` (transitions (8), (9)). -/
theorem recv_ct1Sampled_ekCt1Ack (σ : BState) (ep : ℕ) (a : Auth) (hdr : B 64)
    (es : B 2080) (c1 : B 960) (ecs : EncoderState (B (32 * 30)) L2.Sym)
    (dec : encoding.polynomial.PolyDecoder)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.ct1Sampled ⟨ep, a, hdr, es, c1⟩ ecs dec)) (hRM : RM msg msg')
    (hpay : msg.payload = .EkCt1Ack c) (hep : msg'.epoch = ep) (h64 : ep < 2 ^ 64)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.ct1Sampled ⟨ep, a, hdr, es, c1⟩ ecs dec) msg' =
      .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | _ | _ | _ | _ | _ | ⟨e, a', hdr', es', ct1, enc, d⟩ | _ | _ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, rfl, -, rfl, hwf⟩ := hrel
  simp only [authOf] at hmk
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  rw [hpay] at hpr
  cases pay' <;> simp only [PayloadRel] at hpr
  subst hpr
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', res, hres, hcm, hsd, hlen⟩ :=
    decStep 36 (by decide) ekCodec d hwf c
  simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false] at hr
  simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl, ite_false,
    Braid.receiveEq]
  rw [show codeParams.decEk.addChunk _ (chunkOfCode c) = d' from hsa,
    show codeParams.decEk.decodedPayload d' = _ from hsd] at hr
  rw [hca, hcm]
  rcases res with _ | v
  · simp only [Option.bind_none, Except.ok.injEq] at hr
    subst hr
    exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, rfl, rfl, hwf'⟩, rfl⟩
  · have hv : v.val.length = 32 * 36 := hlen v rfl
    simp only [Option.bind_some, ekCodec, bytesForm_parse 36 v.val hv] at hr
    erw [recvVector_code] at hr
    simp only [Option.map_some]
    by_cases hm : codePrims.ekMatches hdr.1 v.val = true
    · simp only [hm, ↓reduceIte, Except.ok.injEq] at hr ⊢
      subst hr
      exact ⟨_, rfl, completeCt2_rel ep' a' hdr es c1 ⟨v.val, hv⟩ h64 hmk, rfl⟩
    · simp only [hm, ↓reduceIte, Bool.false_eq_true] at hr
      cases hr

/-- The `ek` and `ekCt1Ack` arms in `ct1Acknowledged` (transition (11) and
`Deviation.lateEkChunk`). -/
theorem recv_ct1Acknowledged_ek (σ : BState) (ep : ℕ) (a : Auth) (hdr : B 64)
    (es : B 2080) (c1 : B 960) (dec : encoding.polynomial.PolyDecoder)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (c : encoding.Chunk)
    (hrel : ChunkedRel σ (.ct1Acknowledged ⟨ep, a, hdr, es, c1⟩ dec)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ek c ∨ msg.payload = .EkCt1Ack c) (hep : msg'.epoch = ep)
    (h64 : ep < 2 ^ 64)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth (.ct1Acknowledged ⟨ep, a, hdr, es, c1⟩ dec) msg' =
      .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨e, a', hdr', es', ct1, d⟩ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hwf⟩ := hrel
  simp only [authOf] at hmk
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  simp only at hep
  subst hep
  obtain ⟨d', had, hca, hsa, hwf', res, hres, hcm, hsd, hlen⟩ :=
    decStep 36 (by decide) ekCodec d hwf c
  rcases hpay with hpay | hpay <;> rw [hpay] at hpr <;>
    cases pay' <;> simp only [PayloadRel] at hpr <;> subst hpr <;>
    simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false] at hr <;>
    simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl,
      ite_false, Braid.receiveEq] <;>
    rw [show codeParams.decEk.addChunk _ (chunkOfCode c) = d' from hsa,
      show codeParams.decEk.decodedPayload d' = _ from hsd] at hr <;>
    rw [hca, hcm] <;>
    rcases res with _ | v
  all_goals first
    | (simp only [Option.bind_none, Except.ok.injEq] at hr
       subst hr
       exact ⟨_, rfl, ⟨hmk, rfl, rfl, rfl, rfl, rfl, rfl, hwf'⟩, rfl⟩)
    | (have hv : v.val.length = 32 * 36 := hlen v rfl
       simp only [Option.bind_some, ekCodec, bytesForm_parse 36 v.val hv] at hr
       erw [recvVector_code] at hr
       simp only [Option.map_some]
       by_cases hm : codePrims.ekMatches hdr.1 v.val = true
       · simp only [hm, ↓reduceIte, Except.ok.injEq] at hr ⊢
         subst hr
         exact ⟨_, rfl, completeCt2_rel ep' a' hdr es c1 ⟨v.val, hv⟩ h64 hmk, rfl⟩
       · simp only [hm, ↓reduceIte, Bool.false_eq_true] at hr
         cases hr)

/-- The `ct1Ack` and `ekCt1Ack` arms in `ekReceivedCt1Sampled` (transition (12) and
`Deviation.ct1AckAccepted`). -/
theorem recv_ekReceivedCt1Sampled_ack (σ : BState) (ep : ℕ) (a : Auth) (hdr : B 64)
    (es : B 2080) (c1 : B 960) (vec : B 1152) (ecs : EncoderState (B (32 * 30)) L2.Sym)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym)
    (hrel : ChunkedRel σ (.ekReceivedCt1Sampled ⟨ep, a, hdr, es, c1, vec⟩ ecs)) (hRM : RM msg msg')
    (hpay : msg.payload = .Ct1Ack true ∨ ∃ c, msg.payload = .EkCt1Ack c) (hep : msg'.epoch = ep)
    (h64 : ep < 2 ^ 64)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth
      (.ekReceivedCt1Sampled ⟨ep, a, hdr, es, c1, vec⟩ ecs) msg' = .ok r) :
    ∃ σ', Braid.receive codePrims σ (absMsg msg) =
        some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
      ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1 := by
  obtain ⟨hmk, hrel⟩ := hrel
  rcases σ with _ | _ | _ | _ | _ | _ | _ | _ | ⟨e, a', es', ct1, hdr', ek, enc⟩ | _ | _ <;>
    simp only [SameState] at hrel
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hrel
  simp only [authOf] at hmk
  obtain ⟨hme, hpr⟩ := hRM
  obtain ⟨ep', pay'⟩ := msg'
  simp only at hep
  subst hep
  rcases hpay with hpay | ⟨c, hpay⟩ <;> rw [hpay] at hpr <;>
    cases pay' <;> simp only [PayloadRel] at hpr <;>
    simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false,
      Except.ok.injEq] at hr <;> subst hr <;>
    simp only [Braid.receive, Braid.State.epoch, absMsg, hpay, hme, gt_iff_lt, lt_irrefl,
      ite_false, Braid.receiveEq] <;>
    exact ⟨_, rfl, completeCt2_rel ep' a' hdr es c1 vec h64 hmk, trivial⟩

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
