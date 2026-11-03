/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.EpochBound
import SecureMessaging.SCKA.Correctness

/-!
# Step facts for the code-side game invariant

Facts that `codeGameInv_pres` and `codeGameInv_epochs` use: what a successful send or receive
step of `codeScheme` is in terms of `codeSend` and `codeRecv`, how the game's send
and receive updates change the fields that `CodeGameInv` reads, and how a recorded message array
grows by one send. `CodeBound` imports this file, so the invariant appears here unfolded, as
`RecordedRaw` and `CodeGameInvRaw`. They are `RecordedAs` and `CodeGameInv` by definition.

The linter `constructorNameAsVariable` reaches its recursion limit on binders whose type mentions
the support of `sampleTape`, so `codeGameInvRaw_pres` turns it off. For the same reason, the proofs rewrite
a hypothesis `_ ∈ support (codeSendA s)` in place and never pass it to a lemma: passing it as
an argument also reaches the recursion limit.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std spqr spqr.v1.chunked.states
open OracleSpec OracleComp SCKAScheme

/-! ## Code steps -/

/-- A successful `sendStep` is a successful `codeSend` with the same message and next state. -/
theorem sendStep_some {s : States} {tape : List Std.U8} {k : Option (ℕ × B 32)} {m : Message}
    {e : ℕ} {s' : States} (h : sendStep s tape = some (k, m, e, s')) :
    ∃ out, codeSend s tape = some out ∧ m = out.msg ∧ s' = out.state := by
  simp only [sendStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨out, hout, k', -, hk⟩ := h
  simp only [Prod.mk.injEq] at hk
  exact ⟨out, hout, hk.2.1.symm, hk.2.2.2.symm⟩

/-- A successful `recvStep` is a successful `codeRecv` with the same next state. -/
theorem recvStep_some {s : States} {msg : Message} {k : Option (ℕ × B 32)} {e : ℕ} {s' : States}
    (h : recvStep s msg = some (k, e, s')) :
    ∃ out, codeRecv s msg = some out ∧ s' = out.state := by
  simp only [recvStep, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨out, hout, k', -, hk⟩ := h
  simp only [Prod.mk.injEq] at hk
  exact ⟨out, hout, hk.2.2.symm⟩

/-! ## Fields of the game updates -/

section Fields

variable {StA StB I Rho : Type} [DecidableEq I] (s : GameState StA StB I Rho)
  (keyOpt : Option (ℕ × I)) (ρ : Rho) (tsnd : ℕ)

theorem sendAUpdate_msgA (st : StA) :
    (sendAUpdate s keyOpt ρ tsnd st).msgA = Function.update s.msgA (s.nA + 1) (some (ρ, tsnd)) := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

theorem sendAUpdate_msgB (st : StA) : (sendAUpdate s keyOpt ρ tsnd st).msgB = s.msgB := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

theorem sendAUpdate_nA (st : StA) : (sendAUpdate s keyOpt ρ tsnd st).nA = s.nA + 1 := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

theorem sendAUpdate_nB (st : StA) : (sendAUpdate s keyOpt ρ tsnd st).nB = s.nB := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

theorem sendBUpdate_msgB (st : StB) :
    (sendBUpdate s keyOpt ρ tsnd st).msgB = Function.update s.msgB (s.nB + 1) (some (ρ, tsnd)) := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

theorem sendBUpdate_msgA (st : StB) : (sendBUpdate s keyOpt ρ tsnd st).msgA = s.msgA := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

theorem sendBUpdate_nB (st : StB) : (sendBUpdate s keyOpt ρ tsnd st).nB = s.nB + 1 := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

theorem sendBUpdate_nA (st : StB) : (sendBUpdate s keyOpt ρ tsnd st).nA = s.nA := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> rfl

/-- A's receive update changes A's state and nothing that `CodeGameInv` reads. -/
theorem recvAUpdate_fields (trcv : ℕ) (st : StA) :
    (recvAUpdate s tsnd keyOpt trcv st).stA = st ∧ (recvAUpdate s tsnd keyOpt trcv st).stB = s.stB ∧
      (recvAUpdate s tsnd keyOpt trcv st).msgA = s.msgA ∧
      (recvAUpdate s tsnd keyOpt trcv st).msgB = s.msgB ∧
      (recvAUpdate s tsnd keyOpt trcv st).nA = s.nA ∧ (recvAUpdate s tsnd keyOpt trcv st).nB = s.nB := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- B's receive update changes B's state and nothing that `CodeGameInv` reads. -/
theorem recvBUpdate_fields (trcv : ℕ) (st : StB) :
    (recvBUpdate s tsnd keyOpt trcv st).stB = st ∧ (recvBUpdate s tsnd keyOpt trcv st).stA = s.stA ∧
      (recvBUpdate s tsnd keyOpt trcv st).msgA = s.msgA ∧
      (recvBUpdate s tsnd keyOpt trcv st).msgB = s.msgB ∧
      (recvBUpdate s tsnd keyOpt trcv st).nA = s.nA ∧ (recvBUpdate s tsnd keyOpt trcv st).nB = s.nB := by
  rcases keyOpt with _ | ⟨_, _⟩ <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Fields

/-! ## Recorded message arrays -/

section Record

variable {α β : Type}

/-- Recording one more message at index `count + 1` extends the recorded list by it. The
premise and conclusion are `RecordedAs` unfolded. -/
theorem recorded_update {msg : ℕ → Option (α × β)} {count : ℕ} {ms : List α}
    (h : count = ms.length ∧ msg 0 = none ∧ ∀ k, (msg (k + 1)).map Prod.fst = ms[k]?)
    (m : α) (t : β) :
    count + 1 = (ms ++ [m]).length ∧ Function.update msg (count + 1) (some (m, t)) 0 = none ∧
      ∀ k, (Function.update msg (count + 1) (some (m, t)) (k + 1)).map Prod.fst =
        (ms ++ [m])[k]? := by
  obtain ⟨hc, h0, hk⟩ := h
  refine ⟨by simp [hc], by rw [Function.update_of_ne (by omega)]; exact h0, fun k => ?_⟩
  by_cases hkc : k = count
  · subst hkc
    simp [hc]
  · rw [Function.update_of_ne (by omega), hk k]
    rcases Nat.lt_or_gt_of_ne hkc with hlt | hgt
    · rw [List.getElem?_append_left (by omega)]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-- A recorded message is in the recorded list. The premise is `RecordedAs` unfolded. -/
theorem mem_of_recorded {msg : ℕ → Option (α × β)} {count : ℕ} {ms : List α}
    (h : count = ms.length ∧ msg 0 = none ∧ ∀ k, (msg (k + 1)).map Prod.fst = ms[k]?)
    {n : ℕ} {m : α} {t : β} (hn : msg n = some (m, t)) : m ∈ ms := by
  obtain ⟨-, h0, hk⟩ := h
  rcases n with _ | k
  · rw [h0] at hn; cases hn
  · have := hk k
    rw [hn] at this
    exact List.mem_of_getElem? this.symm

end Record

/-! ## The invariant, unfolded -/

/-- `RecordedAs`, unfolded. -/
def RecordedRaw {α β : Type} (msg : ℕ → Option (α × β)) (count : ℕ) (ms : List α) : Prop :=
  count = ms.length ∧ msg 0 = none ∧ ∀ k, (msg (k + 1)).map Prod.fst = ms[k]?

/-- `CodeGameInv`, unfolded. -/
def CodeGameInvRaw (s : GameState States States (B 32) Message) : Prop :=
  ∃ mA mB, CodeReach s.stA s.stB mA mB (s.nA + s.nB) ∧
    RecordedRaw s.msgA s.nA mA ∧ RecordedRaw s.msgB s.nB mB

theorem codeGameInvRaw_init (k : InitKey) :
    CodeGameInvRaw (initGameState (initAState k) (initBState k)) :=
  ⟨[], [], CodeReach.init k, ⟨rfl, rfl, fun _ => rfl⟩, ⟨rfl, rfl, fun _ => rfl⟩⟩

set_option linter.constructorNameAsVariable false in
theorem codeGameInvRaw_pres (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv (sckaCorrectnessImpl (codeScheme sampleInitKey)) CodeGameInvRaw := by
  refine sckaCorrectnessImpl_preservesInv _ ?_ ?_ ?_ ?_
  · intro u s hs z hz
    cases u
    rw [mem_support_oracleSendA_run_iff] at hz
    obtain ⟨out, hout, rfl⟩ := hz
    rcases out with _ | ⟨keyOpt, ρ, tsnd, st'⟩
    · exact hs
    · change _ ∈ support (codeSendA _) at hout
      unfold codeSendA at hout
      rw [mem_support_bind_iff] at hout
      obtain ⟨t, -, ht⟩ := hout
      rw [mem_support_pure_iff] at ht
      obtain ⟨o, hco, rfl, rfl⟩ := sendStep_some ht.symm
      obtain ⟨mA, mB, hR, hA, hB⟩ := hs
      refine ⟨mA ++ [o.msg], mB, ?_, ?_, ?_⟩
      · rw [sendAUpdate_stA, sendAUpdate_stB, sendAUpdate_nA, sendAUpdate_nB,
          Nat.add_right_comm]
        exact CodeReach.sendA _ o hR hco
      · rw [sendAUpdate_msgA, sendAUpdate_nA]
        exact recorded_update hA _ _
      · rw [sendAUpdate_msgB, sendAUpdate_nB]
        exact hB
  · intro u s hs z hz
    cases u
    rw [mem_support_oracleSendB_run_iff] at hz
    obtain ⟨out, hout, rfl⟩ := hz
    rcases out with _ | ⟨keyOpt, ρ, tsnd, st'⟩
    · exact hs
    · change _ ∈ support (codeSendA _) at hout
      unfold codeSendA at hout
      rw [mem_support_bind_iff] at hout
      obtain ⟨t, -, ht⟩ := hout
      rw [mem_support_pure_iff] at ht
      obtain ⟨o, hco, rfl, rfl⟩ := sendStep_some ht.symm
      obtain ⟨mA, mB, hR, hA, hB⟩ := hs
      refine ⟨mA, mB ++ [o.msg], ?_, ?_, ?_⟩
      · rw [sendBUpdate_stA, sendBUpdate_stB, sendBUpdate_nA, sendBUpdate_nB, ← Nat.add_assoc]
        exact CodeReach.sendB _ o hR hco
      · rw [sendBUpdate_msgA, sendBUpdate_nA]
        exact hA
      · rw [sendBUpdate_msgB, sendBUpdate_nB]
        exact recorded_update hB _ _
  · intro n s hs z hz
    rcases (mem_support_oracleRecvA_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, st', hm, hr, rfl⟩
    · exact hs
    · exact hs
    · obtain ⟨o, hco, rfl⟩ := recvStep_some hr
      obtain ⟨mA, mB, hR, hA, hB⟩ := hs
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := recvAUpdate_fields s keyOpt tsnd trcv o.state
      refine ⟨mA, mB, ?_, ?_, ?_⟩
      · rw [h1, h2, h5, h6]
        exact CodeReach.recvA ρ o hR (mem_of_recorded hB hm) hco
      · rw [h3, h5]; exact hA
      · rw [h4, h6]; exact hB
  · intro n s hs z hz
    rcases (mem_support_oracleRecvB_run_iff _ s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨ρ, tsnd, keyOpt, trcv, st', hm, hr, rfl⟩
    · exact hs
    · exact hs
    · obtain ⟨o, hco, rfl⟩ := recvStep_some hr
      obtain ⟨mA, mB, hR, hA, hB⟩ := hs
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := recvBUpdate_fields s keyOpt tsnd trcv o.state
      refine ⟨mA, mB, ?_, ?_, ?_⟩
      · rw [h1, h2, h5, h6]
        exact CodeReach.recvB ρ o hR (mem_of_recorded hA hm) hco
      · rw [h3, h5]; exact hA
      · rw [h4, h6]; exact hB

theorem codeGameInvRaw_epochs (s : GameState States States (B 32) Message)
    (h : CodeGameInvRaw s) :
    s.stA.epochOf.val ≤ s.nA + s.nB + 1 ∧ s.stB.epochOf.val ≤ s.nA + s.nB + 1 ∧
      ∀ n m t, (s.msgA n = some (m, t) ∨ s.msgB n = some (m, t)) →
        m.epoch.val ≤ s.nA + s.nB := by
  obtain ⟨mA, mB, hR, hA, hB⟩ := h
  obtain ⟨hsA, hsB, hm⟩ := epoch_bound_strong hR
  refine ⟨hsA, hsB, fun n m t hn => ?_⟩
  rcases hn with hn | hn
  · exact hm m (List.mem_append_left _ (mem_of_recorded hA hn))
  · exact hm m (List.mem_append_right _ (mem_of_recorded hB hn))

end SpqrBridge
