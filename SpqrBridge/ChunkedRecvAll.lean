/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.ChunkedRecv

/-!
# `receive_chunked`: every receive arm

`chunked_recv_braid` covers every arm of `Chunked.recv`: stale messages, the successor epoch in
`ct2Sampled`, the arms of `ChunkedRecv.lean`, and the messages that both machines ignore.
`receive_chunked` is the one-sided obligation `RecvRel RA` of the transfer.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming

/-- Related states have the same epoch. -/
theorem SameState.epoch {σ : BState} {st : SMState} (h : SameState σ st) :
    σ.epoch = st.epoch := by
  cases σ <;> cases st <;> simp only [SameState] at h <;>
    simp only [State.epoch, SPQR.Chunked.PartyState.epoch, h.1]

/-- The goal of every receive arm: `Braid.receive` accepts with a related state, the same key and
the report `msg'.epoch - 1`. -/
def BraidAccepts (σ : BState) (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth) : Prop :=
  ∃ σ', Braid.receive codePrims σ (absMsg msg) =
      some (σ', r.outputKey.map fun k => (k.1, k.2.1)) ∧
    ChunkedRel σ' r.state ∧ r.receivingEpoch = msg'.epoch - 1

/-- A message that both machines ignore. -/
theorem ignore_case {σ : BState} {st : SMState} {msg : Message}
    {msg' : SPQR.Chunked.Message L2.Sym} {r : SPQR.Chunked.RecvResult codeParams Braid.Auth}
    (hrel : ChunkedRel σ st) (hbr : Braid.receive codePrims σ (absMsg msg) = some (σ, none))
    (hr : r = ⟨msg'.epoch - 1, none, st⟩) : BraidAccepts σ msg msg' r :=
  ⟨σ, by rw [hbr, hr]; rfl, by rw [hr]; exact hrel, by rw [hr]⟩

/-- `Braid.receive` ignores a message from an earlier epoch. -/
theorem receive_of_lt' (P : CodePrims) {σ : BState} {m : Msg encoding.Chunk}
    (h : m.epoch < σ.epoch) : Braid.receive P σ m = some (σ, none) := by
  cases σ <;> simp only [State.epoch] at h <;>
    simp only [Braid.receive, State.epoch, gt_iff_lt, h, Nat.lt_asymm h, ↓reduceIte,
      Nat.ne_of_lt (Nat.lt_succ_of_lt h)]

set_option hygiene false in
/-- Close an arm that both machines ignore at the state's epoch. Needs `hrel`, `hRM`, `hr`,
`hep : msg'.epoch = _`, `hme : (absMsg msg).epoch = σ.epoch` and `hm : msg.payload = _`. -/
local macro "recv_ignore" : tactic => `(tactic| (
  obtain ⟨ep', pay'⟩ := msg'
  have hpr := hRM.2
  rw [hm] at hpr
  simp only at hep
  subst hep
  rcases pay' with _ | x | x | x | _ | x | x <;> simp only [PayloadRel] at hpr
  all_goals
    simp only [SPQR.Chunked.recv, SPQR.Chunked.PartyState.epoch, lt_irrefl, ite_false,
      Except.ok.injEq] at hr
    refine ignore_case hrel ?_ hr.symm
    rw [receive_of_eq codePrims hme]
    obtain ⟨-, hs⟩ := hrel
    rcases σ with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp only [SameState] at hs
    simp only [absMsg, hm, Braid.receiveEq]))

/-- Every arm of `Chunked.recv` at the state's epoch. -/
theorem chunked_recv_braid_eq (hsz : MlkemSizes) (σ : BState) (st : SMState) (msg : Message)
    (msg' : SPQR.Chunked.Message L2.Sym) (hrel : ChunkedRel σ st) (hRM : RM msg msg')
    (hep : msg'.epoch = st.epoch) (h64 : st.epoch < 2 ^ 64)
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth st msg' = .ok r) :
    BraidAccepts σ msg msg' r := by
  have hme : (absMsg msg).epoch = σ.epoch := by
    rw [hrel.2.epoch, ← hep, ← hRM.1]; rfl
  rcases hm : msg.payload with _ | c | c | c | (_ | _) | c | c <;>
    rcases st with ⟨ep, a⟩ | ⟨⟨ep, a, pk, sk⟩, es⟩ | ⟨⟨ep, a, sk⟩, es, dec⟩ |
      ⟨⟨ep, a, sk, c1⟩, es⟩ | ⟨⟨ep, a, sk, c1⟩, dec⟩ | ⟨⟨ep, a⟩, dec⟩ | ⟨⟨ep, a, hdr⟩, dec⟩ |
      ⟨⟨ep, a, hdr, es, c1⟩, ecs, dec⟩ | ⟨⟨ep, a, hdr, es, c1, vec⟩, ecs⟩ |
      ⟨⟨ep, a, hdr, es, c1⟩, dec⟩ | ⟨⟨ep, a⟩, es⟩ <;>
    simp only [SPQR.Chunked.PartyState.epoch] at hep h64
  case Ct1.keysSampled =>
    exact recv_keysSampled_ct1 hsz σ ep a pk sk es msg msg' c hrel hRM hm hep r hr
  case Ct1.headerSent =>
    exact recv_headerSent_ct1 σ ep a sk es dec msg msg' c hrel hRM hm hep r hr
  case Ct2.ct1Received =>
    exact recv_ct1Received_ct2 hsz σ ep a sk c1 es msg msg' c hrel hRM hm hep r hr
  case Ct2.ekSentCt1Received =>
    exact recv_ekSentCt1Received_ct2 hsz σ ep a sk c1 dec msg msg' c hrel hRM hm hep h64 r hr
  case Hdr.noHeaderReceived =>
    exact recv_noHeaderReceived_hdr hsz σ ep a dec msg msg' c hrel hRM hm hep h64 r hr
  case Ek.ct1Sampled =>
    exact recv_ct1Sampled_ek σ ep a hdr es c1 ecs dec msg msg' c hrel hRM hm hep r hr
  case EkCt1Ack.ct1Sampled =>
    exact recv_ct1Sampled_ekCt1Ack σ ep a hdr es c1 ecs dec msg msg' c hrel hRM hm hep h64 r hr
  case Ek.ct1Acknowledged =>
    exact recv_ct1Acknowledged_ek σ ep a hdr es c1 dec msg msg' c hrel hRM (.inl hm) hep h64 r hr
  case EkCt1Ack.ct1Acknowledged =>
    exact recv_ct1Acknowledged_ek σ ep a hdr es c1 dec msg msg' c hrel hRM (.inr hm) hep h64 r hr
  case Ct1Ack.true.ekReceivedCt1Sampled =>
    exact recv_ekReceivedCt1Sampled_ack σ ep a hdr es c1 vec ecs msg msg' hrel hRM (.inl hm) hep
      h64 r hr
  case EkCt1Ack.ekReceivedCt1Sampled =>
    exact recv_ekReceivedCt1Sampled_ack σ ep a hdr es c1 vec ecs msg msg' hrel hRM (.inr ⟨c, hm⟩)
      hep h64 r hr
  all_goals recv_ignore

/-- Every arm of `Chunked.recv`: when it accepts, `Braid.receive` accepts with a related state, the
same key and the report `msg'.epoch - 1`. -/
theorem chunked_recv_braid (hsz : MlkemSizes) (s : States) (σ : BState) (st : SMState)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (hσ : Refines s σ)
    (hrel : ChunkedRel σ st) (hRM : RM msg msg')
    (r : SPQR.Chunked.RecvResult codeParams Braid.Auth)
    (hr : SPQR.Chunked.recv codeParams codeAuth st msg' = .ok r) :
    BraidAccepts σ msg msg' r := by
  have hst : σ.epoch = st.epoch := hrel.2.epoch
  have h64 : st.epoch < 2 ^ 64 := by
    rw [← hst, hσ.epoch]; exact s.epochOf.hBounds
  have hme : (absMsg msg).epoch = msg'.epoch := hRM.1
  rcases Nat.lt_trichotomy msg'.epoch st.epoch with hlt | heq | hgt
  · simp only [SPQR.Chunked.recv, hlt, ↓reduceIte, Except.ok.injEq] at hr
    exact ignore_case hrel (receive_of_lt' codePrims (by rw [hme, hst]; exact hlt)) hr.symm
  · exact chunked_recv_braid_eq hsz σ st msg msg' hrel hRM heq h64 r hr
  · simp only [SPQR.Chunked.recv, Nat.lt_asymm hgt, hgt, ↓reduceIte] at hr
    obtain ⟨hmk, hs⟩ := hrel
    rcases st with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨⟨ep, a⟩, es⟩ <;>
      simp only [reduceCtorEq] at hr
    rcases σ with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨e, a', enc⟩ <;>
      simp only [SameState] at hs
    obtain ⟨rfl, rfl, -⟩ := hs
    simp only [SPQR.CtSender.recvNextEpoch] at hr
    by_cases hn : msg'.epoch = e + 1
    · simp only [hn, ↓reduceIte, Except.ok.injEq] at hr
      subst hr
      refine ⟨.keysUnsampled (e + 1) a', ?_, ⟨hmk, rfl, rfl⟩, by rw [hn]⟩
      simp only [Braid.receive, hme, hn, ↓reduceIte, Option.map_none]
    · simp only [hn, ↓reduceIte, reduceCtorEq] at hr

/-- `receive_chunked`, the one-sided receive obligation of the transfer: for a reachable code
state related to a secure-messaging state, and related messages with epoch headroom, the code's
receive and secure-messaging's receive are related by `RecvRel RA`. It uses the
`BridgeObligations` fields `recv_complete`, `recv_key_length` and `mlkem_sizes`. -/
theorem receive_chunked (hB : BridgeObligations) (s : States) (n : ℕ) (st : SMState)
    (msg : Message) (msg' : SPQR.Chunked.Message L2.Sym) (hreach : ReachParty s n)
    (hep : msg.epoch.val + 1 < 2 ^ 64) (hRA : RA s st) (hRM : RM msg msg') :
    RecvRel RA (recvStep s msg) (SPQR.recvSCKA codeParams codeAuth st msg') := by
  obtain ⟨σ, hσ, hrel⟩ := hRA
  exact recvRel_of_braid hB s n σ st msg msg' hreach hσ hep hRM fun r hr =>
    chunked_recv_braid hB.mlkem_sizes s σ st msg msg' hσ hrel hRM r hr

end SpqrBridge
