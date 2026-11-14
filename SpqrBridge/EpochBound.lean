/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.SendFacts
import Spqr.Specs.Braid.Scka.EpochUniqueness.KeyFloor
import Spqr.Specs.Braid.StateMachine.EpochDispatch

/-!
# Epoch bound for the adapter

`epoch_bound_strong`: in every configuration that a correctness game on `codeScheme` reaches,
both state epochs are at most the number of successful sends plus one, and every recorded message
epoch is at most the number of successful sends. `epoch_bound` is the weaker form with the bound
`n + 1` for the messages too. Deliveries, replays and stale messages do not
count. A failed call leaves both states and both message lists unchanged, so the bound also
holds after a failure.

The proof uses two step facts. A successful `send` keeps the state epoch and stamps the
message with it (`send_epoch`). After a successful `recv`, the state epoch is at most the
larger of the old state epoch and the incoming message epoch plus one (`recv_epoch_le`).
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states
open spqr.v1.chunked spqr.v1.chunked.states.epoch_uniqueness

/-- A successful `send` stamps the message with the state epoch and keeps the state epoch. -/
theorem send_epoch {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (s : States) (rng rng' : R) (r : v1.chunked.states.Send)
    (h : States.send i₁ i₂ s rng = ok (.Ok r, rng')) :
    r.msg.epoch = s.epochOf ∧ r.state.epochOf = s.epochOf := by
  cases s <;> simp only [States.send, send_ek.KeysUnsampled.epoch, send_ek.KeysSampled.epoch,
    send_ek.HeaderSent.epoch,
    send_ek.Ct1Received.epoch, send_ek.EkSentCt1Received.epoch, send_ct.NoHeaderReceived.epoch,
    send_ct.HeaderReceived.epoch, send_ct.Ct1Sampled.epoch, send_ct.EkReceivedCt1Sampled.epoch,
    send_ct.Ct1Acknowledged.epoch, send_ct.Ct2Sampled.epoch, bind_ok, bind_eq_ok,
    Prod.exists, uncurry_apply_pair, ok.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq,
    exists_eq_right_right] at h
  case EkSentCt1Received | NoHeaderReceived | Ct1Acknowledged =>
    obtain ⟨rfl, -⟩ := h
    exact ⟨rfl, rfl⟩
  case KeysUnsampled =>
    obtain ⟨_, _, hc, rfl⟩ := h
    exact ⟨rfl, KeysUnsampled_send_hdr_chunk_epoch i₁ i₂ _ rng hc⟩
  case KeysSampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact ⟨rfl, KeysSampled_send_hdr_chunk_epoch _ hc⟩
  case HeaderSent =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact ⟨rfl, HeaderSent_send_ek_chunk_epoch _ hc⟩
  case Ct1Received =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact ⟨rfl, Ct1Received_send_ek_chunk_epoch _ hc⟩
  case HeaderReceived st =>
    obtain ⟨st', _, _, hc, rfl⟩ := h
    exact ⟨rfl, (HeaderReceived_send_ct1_chunk_epoch i₁ i₂ st rng hc).1⟩
  case Ct1Sampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact ⟨rfl, Ct1Sampled_send_ct1_chunk_epoch _ hc⟩
  case EkReceivedCt1Sampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact ⟨rfl, EkReceivedCt1Sampled_send_ct1_chunk_epoch _ hc⟩
  case Ct2Sampled =>
    obtain ⟨_, _, hc, rfl, -⟩ := h
    exact ⟨rfl, Ct2Sampled_send_ct2_chunk_epoch _ hc⟩

theorem epochOf_le_keyFloor (s : States) : s.epochOf.val ≤ keyFloor s := by
  cases s <;> simp only [States.epochOf, keyFloor] <;> omega

theorem keyFloor_le_epochOf_succ (s : States) : keyFloor s ≤ s.epochOf.val + 1 := by
  cases s <;> simp only [States.epochOf, keyFloor] <;> omega

/-- Let `States.recv s msg = ok (.Ok r)`. Then
`r.state.epochOf.val ≤ max s.epochOf.val (msg.epoch.val + 1)`. -/
theorem recv_epoch_le (s : States) (msg : Message) (r : v1.chunked.states.Recv)
    (h : States.recv s msg = ok (.Ok r)) :
    r.state.epochOf.val ≤ max s.epochOf.val (msg.epoch.val + 1) := by
  by_cases hlt : msg.epoch.val < s.epochOf.val
  · rw [recv_of_lt s msg hlt, ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    exact le_max_left _ _
  · have hs := recv_step s msg r h
    cases hk : r.key with
    | none =>
      rw [hk] at hs
      have h1 := epochOf_le_keyFloor r.state
      have h2 := keyFloor_le_epochOf_succ s
      omega
    | some k =>
      rw [hk] at hs
      obtain ⟨st, st', _, -, hst', hme, -, -, hep⟩ := hs
      rw [hst']
      simp only [States.epochOf]
      rw [hme] at hlt ⊢
      omega

/-- Let `codeSend s buf = some out`. Then
`States.send (fixedRng buf) (fixedCrypto buf) s () = ok (.Ok out, rng')` for some `rng'`. -/
theorem codeSend_some {s : States} {buf : Slice Std.U8} {out : v1.chunked.states.Send}
    (h : codeSend s buf = some out) :
    ∃ rng', States.send (fixedRng buf) (fixedCrypto buf) s () = ok (.Ok out, rng') :=
  (codeSend_eq_some_iff s buf out).mp h

/-- Let `codeRecv s msg = some out`. Then `States.recv s msg = ok (.Ok out)`. -/
theorem codeRecv_some {s : States} {msg : Message} {out : v1.chunked.states.Recv}
    (h : codeRecv s msg = some out) : States.recv s msg = ok (.Ok out) := by
  unfold codeRecv at h
  generalize States.recv s msg = x at h
  cases x with
  | ret r =>
    cases r <;> simp_all [Result.match.ok]
  | vis i k => simp [Result.match.vis] at h
  | div => simp [Result.match.div] at h

theorem initAState_epoch (k : InitKey) : (initAState k).epochOf.val ≤ 1 := by
  have := keyFloor_init_a (init_a_eq k)
  have := epochOf_le_keyFloor (initAState k)
  omega

theorem initBState_epoch (k : InitKey) : (initBState k).epochOf.val ≤ 1 := by
  have := keyFloor_init_b (init_b_eq k)
  have := epochOf_le_keyFloor (initBState k)
  omega

/-- Let `CodeReach sA sB mA mB n`. Then `sA.epochOf.val ≤ n + 1`, `sB.epochOf.val ≤ n + 1`, and
`m.epoch.val ≤ n` for every `m` in `mA ++ mB`. -/
theorem epoch_bound_strong {sA sB : States} {mA mB : List Message} {n : ℕ}
    (h : CodeReach sA sB mA mB n) :
    sA.epochOf.val ≤ n + 1 ∧ sB.epochOf.val ≤ n + 1 ∧
      ∀ m ∈ mA ++ mB, m.epoch.val ≤ n := by
  induction h with
  | init k =>
    exact ⟨initAState_epoch k, initBState_epoch k, by simp⟩
  | sendA buf out _ _ hs ih =>
    obtain ⟨hA, hB, hm⟩ := ih
    obtain ⟨_, hc⟩ := codeSend_some hs
    obtain ⟨he, hst⟩ := send_epoch _ _ _ _ _ _ hc
    refine ⟨by rw [hst]; omega, by omega, fun m hmem => ?_⟩
    simp only [List.append_assoc, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | rfl | hmem
    · have := hm m (List.mem_append_left _ hmem); omega
    · rw [he]; omega
    · have := hm m (List.mem_append_right _ hmem); omega
  | sendB buf out _ _ hs ih =>
    obtain ⟨hA, hB, hm⟩ := ih
    obtain ⟨_, hc⟩ := codeSend_some hs
    obtain ⟨he, hst⟩ := send_epoch _ _ _ _ _ _ hc
    refine ⟨by omega, by rw [hst]; omega, fun m hmem => ?_⟩
    simp only [List.mem_append, List.mem_singleton] at hmem
    rcases hmem with hmem | hmem | rfl
    · have := hm m (List.mem_append_left _ hmem); omega
    · have := hm m (List.mem_append_right _ hmem); omega
    · rw [he]; omega
  | recvA m out _ hmem hr ih =>
    obtain ⟨hA, hB, hm⟩ := ih
    have hle := recv_epoch_le _ _ _ (codeRecv_some hr)
    have := hm m (List.mem_append_right _ hmem)
    exact ⟨by omega, hB, hm⟩
  | recvB m out _ hmem hr ih =>
    obtain ⟨hA, hB, hm⟩ := ih
    have hle := recv_epoch_le _ _ _ (codeRecv_some hr)
    have := hm m (List.mem_append_left _ hmem)
    exact ⟨hA, by omega, hm⟩

/-- Let `CodeReach sA sB mA mB n`. Then `sA.epochOf.val ≤ n + 1`, `sB.epochOf.val ≤ n + 1`, and
`m.epoch.val ≤ n + 1` for every `m` in `mA ++ mB`. -/
theorem epoch_bound {sA sB : States} {mA mB : List Message} {n : ℕ}
    (h : CodeReach sA sB mA mB n) :
    sA.epochOf.val ≤ n + 1 ∧ sB.epochOf.val ≤ n + 1 ∧
      ∀ m ∈ mA ++ mB, m.epoch.val ≤ n + 1 := by
  obtain ⟨hA, hB, hm⟩ := epoch_bound_strong h
  exact ⟨hA, hB, fun m hmem => Nat.le_succ_of_le (hm m hmem)⟩

/-- Let `CodeReach sA sB mA mB n`, `n ≤ q` and `q + 2 < 2 ^ 64`. Then
`sA.epochOf.val + 1 < 2 ^ 64`, `sB.epochOf.val + 1 < 2 ^ 64`, and `m.epoch.val + 1 < 2 ^ 64`
for every `m` in `mA ++ mB`. -/
theorem epoch_budget {sA sB : States} {mA mB : List Message} {n q : ℕ}
    (h : CodeReach sA sB mA mB n) (hn : n ≤ q) (hq64 : q + 2 < 2 ^ 64) :
    sA.epochOf.val + 1 < 2 ^ 64 ∧ sB.epochOf.val + 1 < 2 ^ 64 ∧
      ∀ m ∈ mA ++ mB, m.epoch.val + 1 < 2 ^ 64 := by
  obtain ⟨hA, hB, hm⟩ := epoch_bound h
  exact ⟨by omega, by omega, fun m hmem => by have := hm m hmem; omega⟩

end SpqrBridge
