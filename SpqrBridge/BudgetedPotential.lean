/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.PotentialTransfer

/-!
# The potential transfer with a send budget

`correctness_error_le_of_transfer` needs the step obligations on every related state. This file
weakens that: the obligations need to hold only on states of `S₁` that meet an invariant `Inv₁`,
and a send only below a budget `Bud` of successful sends, a receive up to it.

The potential method of SM (`wp_simulateQ_run_le`) has a fixed invariant. Here the invariant is
indexed by the number `k` of send queries that the adversary has left
(`wp_simulateQ_run_le_budget`). On the correctness game, the index is `Inv₁ s ∧ nA + nB + k ≤ q`:
every send query raises `nA + nB` by at most one and uses one unit of `k`, and every other query
keeps `nA + nB` (`nA_add_nB_le`). So a send query sees `nA + nB < q`, and every query sees
`nA + nB ≤ q`.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open SCKAScheme

namespace SpqrBridge

/-! ### A potential bound with a budgeted invariant -/

section Generic

variable {ι : Type} {spec : OracleSpec ι} {σ α : Type}

/-- Let `Inv k` be an invariant indexed by the number `k` of `p`-queries left. A `p`-query with
`0 < k` moves `Inv k` to `Inv (k - 1)`, and another query keeps `Inv k`. A query from a state of
`Inv k` that is allowed (`0 < k` for a `p`-query) raises the expected score by at most `ε` for a
`p`-query and `0` otherwise. Then a computation with at most `q` `p`-queries, run from a state
of `Inv q`, raises the expected score by at most `q · ε`. -/
theorem wp_simulateQ_run_le_budget
    (impl : QueryImpl spec (StateT σ ProbComp))
    (Inv : ℕ → σ → Prop) (score : σ → ℝ≥0∞)
    (p : ι → Prop) [DecidablePred p] (ε : ℝ≥0∞)
    (hpres : ∀ t k s, Inv k s → (p t → 0 < k) →
      ∀ z ∈ support ((impl t).run s), Inv (if p t then k - 1 else k) z.2)
    (hstep : ∀ t k s, Inv k s → (p t → 0 < k) →
      wp ((impl t).run s) (fun z => score z.2) ≤ score s + if p t then ε else 0)
    (oa : OracleComp spec α) (q : ℕ) (hq : oa.IsQueryBoundP p q) :
    ∀ s, Inv q s →
      wp ((simulateQ impl oa).run s) (fun z => score z.2) ≤ score s + (q : ℝ≥0∞) * ε := by
  induction oa using OracleComp.inductionOn generalizing q with
  | pure x =>
      intro s _
      simp only [simulateQ_pure, StateT.run_pure, ExactWPMonad.wp_pure, self_le_add_right]
  | @query_bind t cont ih =>
      intro s hs
      rw [OracleComp.isQueryBoundP_query_bind_iff] at hq
      obtain ⟨hcan, hcont⟩ := hq
      have hallow : p t → 0 < q := fun ht => hcan.resolve_left (not_not_intro ht)
      rw [simulateQ_query_bind, StateT.run_bind, wp_bind]
      have hK : ∀ K : ℝ≥0∞, (∀ z ∈ support ((impl t).run s),
          wp ((simulateQ impl (cont z.1)).run z.2) (fun w => score w.2) ≤ score z.2 + K) →
          wp ((impl t).run s)
              (fun z => wp ((simulateQ impl (cont z.1)).run z.2) (fun w => score w.2)) ≤
            wp ((impl t).run s) (fun z => score z.2) + K := fun K h =>
        (wp_mono_of_support _ h).trans_eq (by rw [wp_add, wp_const])
      by_cases ht : p t
      · have hqpos : 0 < q := hallow ht
        refine (hK _ fun z hz => ih z.1 (q - 1) (by simpa [ht] using hcont z.1) z.2
          (by simpa [ht] using hpres t q s hs hallow z hz)).trans ?_
        calc
          wp ((impl t).run s) (fun z => score z.2) + (((q - 1 : ℕ) : ℝ≥0∞) * ε)
              ≤ (score s + ε) + (((q - 1 : ℕ) : ℝ≥0∞) * ε) :=
            add_le_add (by simpa [ht] using hstep t q s hs hallow) le_rfl
          _ = score s + (q : ℝ≥0∞) * ε := by
            have hcast : (((q - 1 : ℕ) : ℝ≥0∞) + 1) = (q : ℝ≥0∞) := by
              exact_mod_cast Nat.sub_add_cancel hqpos
            rw [← hcast, add_mul, one_mul]
            ac_rfl
      · refine (hK _ fun z hz => ih z.1 q (by simpa [ht] using hcont z.1) z.2
          (by simpa [ht] using hpres t q s hs hallow z hz)).trans ?_
        simpa [ht] using add_le_add (hstep t q s hs hallow) (le_refl ((q : ℝ≥0∞) * ε))

end Generic

variable {IK₁ StA₁ StB₁ Rho₁ Rand₁ IK₂ StA₂ StB₂ Rho₂ Rand₂ I : Type}

/-! ### Send counters of the correctness game -/

section Counters

variable [DecidableEq I]

/-- A query of the correctness game raises `nA + nB` by at most one if it is a send, and keeps
it otherwise. -/
theorem nA_add_nB_le (S : SCKAScheme ProbComp IK₁ StA₁ StB₁ I Rho₁ Rand₁)
    (t : (sckaCorrectnessSpec Rho₁).Domain) (s : GameState StA₁ StB₁ I Rho₁)
    (z) (hz : z ∈ support ((sckaCorrectnessImpl S t).run s)) :
    z.2.nA + z.2.nB ≤ s.nA + s.nB + if isSendQuery (Rho := Rho₁) t then 1 else 0 := by
  rcases t with ((((n | u) | u) | n) | n)
  · have := oracleUnif_preservesInv (fun z : GameState StA₁ StB₁ I Rho₁ => z = s) n s rfl z hz
    simp only at this
    simp [this, isSendQuery]
  · change z ∈ support ((oracleSendA S ()).run s) at hz
    obtain ⟨out, -, rfl⟩ := (mem_support_oracleSendA_run_iff S s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, st⟩ <;>
      simp [sendAUpdate, isSendQuery] <;> omega
  · change z ∈ support ((oracleSendB S ()).run s) at hz
    obtain ⟨out, -, rfl⟩ := (mem_support_oracleSendB_run_iff S s z).1 hz
    rcases out with _ | ⟨_ | ⟨tI, key⟩, ρ, tsnd, st⟩ <;>
      simp [sendBUpdate, isSendQuery] <;> omega
  · change z ∈ support ((oracleRecvA S n).run s) at hz
    rcases (mem_support_oracleRecvA_run_iff S s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, keyOpt, -, -, -, -, rfl⟩
    · simp [isSendQuery]
    · simp [isSendQuery]
    · rcases keyOpt with _ | ⟨tI, key⟩ <;> simp [recvAUpdate, isSendQuery]
  · change z ∈ support ((oracleRecvB S n).run s) at hz
    rcases (mem_support_oracleRecvB_run_iff S s n z).1 hz with
      ⟨-, rfl⟩ | ⟨-, -, -, -, rfl⟩ | ⟨-, -, keyOpt, -, -, -, -, rfl⟩
    · simp [isSendQuery]
    · simp [isSendQuery]
    · rcases keyOpt with _ | ⟨tI, key⟩ <;> simp [recvBUpdate, isSendQuery]

end Counters

/-! ### One step of the two games, with obligations at one state -/

section Step

variable [DecidableEq I] {S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ I Rho₁ Rand₁}
  {S₂ : SCKAScheme ProbComp IK₂ StA₂ StB₂ I Rho₂ Rand₂}
  {RA : StA₁ → StA₂ → Prop} {RB : StB₁ → StB₂ → Prop} {RM : Rho₁ → Rho₂ → Prop}

/-- The version of `step_relTriple` that needs the step obligations only at the given pair of
states: the send obligations only if the query is a send. -/
theorem step_relTriple_of (t : (sckaCorrectnessSpec Rho₁).Domain)
    (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
    (h : GameRel RA RB RM s₁ s₂)
    (hsA : isSendQuery (Rho := Rho₁) t = true →
      RelTriple (S₁.sendA s₁.stA) (S₂.sendA s₂.stA) (SendRel RA RM))
    (hsB : isSendQuery (Rho := Rho₁) t = true →
      RelTriple (S₁.sendB s₁.stB) (S₂.sendB s₂.stB) (SendRel RB RM))
    (hrA : ∀ n tsnd ρ₁ ρ₂, s₁.msgB n = some (ρ₁, tsnd) → s₂.msgB n = some (ρ₂, tsnd) →
      RM ρ₁ ρ₂ → RecvRel RA (S₁.recvA s₁.stA ρ₁) (S₂.recvA s₂.stA ρ₂))
    (hrB : ∀ n tsnd ρ₁ ρ₂, s₁.msgA n = some (ρ₁, tsnd) → s₂.msgA n = some (ρ₂, tsnd) →
      RM ρ₁ ρ₂ → RecvRel RB (S₁.recvB s₁.stB ρ₁) (S₂.recvB s₂.stB ρ₂)) :
    RelTriple ((sckaCorrectnessImpl S₁ t).run s₁)
      ((sckaCorrectnessImpl S₂ (castQuery t)).run s₂)
      (fun z₁ z₂ => GameRel RA RB RM z₁.2 z₂.2 ∨ z₂.2.correct = false) := by
  rcases t with ((((n | u) | u) | n) | n)
  · refine relTriple_post_mono
      (relTriple_prod (P := fun z => z.2 = s₁) (Q := fun z => z.2 = s₂) ?_ ?_) ?_
    · exact fun z hz => oracleUnif_preservesInv (· = s₁) n s₁ rfl z hz
    · exact fun z hz => oracleUnif_preservesInv (· = s₂) n s₂ rfl z hz
    · rintro z₁ z₂ ⟨h1, h2⟩
      exact Or.inl (h1 ▸ h2 ▸ h)
  · change RelTriple ((oracleSendA S₁ ()).run s₁) ((oracleSendA S₂ ()).run s₂) _
    rw [oracleSendA_run_eq, oracleSendA_run_eq]
    refine relTriple_map (relTriple_post_mono (hsA rfl) ?_)
    rintro (_ | ⟨k₁, ρ₁, t₁, st₁⟩) (_ | ⟨k₂, ρ₂, t₂, st₂⟩) hr <;> simp only [SendRel] at hr
    · exact Or.inl h
    · obtain ⟨rfl, hρ, rfl, hst⟩ := hr
      exact Or.inl (h.sendAUpdate _ hρ _ hst)
  · change RelTriple ((oracleSendB S₁ ()).run s₁) ((oracleSendB S₂ ()).run s₂) _
    rw [oracleSendB_run_eq, oracleSendB_run_eq]
    refine relTriple_map (relTriple_post_mono (hsB rfl) ?_)
    rintro (_ | ⟨k₁, ρ₁, t₁, st₁⟩) (_ | ⟨k₂, ρ₂, t₂, st₂⟩) hr <;> simp only [SendRel] at hr
    · exact Or.inl h
    · obtain ⟨rfl, hρ, rfl, hst⟩ := hr
      exact Or.inl (h.sendBUpdate _ hρ _ hst)
  · change RelTriple ((oracleRecvA S₁ n).run s₁) ((oracleRecvA S₂ n).run s₂) _
    have hm := h.msgB n
    rcases h₁ : s₁.msgB n with _ | ⟨ρ₁, tsnd⟩ <;> rcases h₂ : s₂.msgB n with _ | ⟨ρ₂, tsnd₂⟩ <;>
      rw [h₁, h₂] at hm <;> cases hm
    · rw [oracleRecvA_run_eq_of_none S₁ s₁ h₁, oracleRecvA_run_eq_of_none S₂ s₂ h₂]
      exact relTriple_pure_pure (Or.inl h)
    · rename_i hm
      obtain ⟨hρ, rfl⟩ := hm
      have hr := hrA n _ ρ₁ ρ₂ h₁ h₂ hρ
      rcases hr₂ : S₂.recvA s₂.stA ρ₂ with _ | ⟨k₂, t₂, st₂⟩
      · rw [oracleRecvA_run_eq_of_refuse S₂ s₂ h₂ hr₂]
        refine relTriple_post_mono (relTriple_prod (P := fun _ => True)
          (Q := fun z => z.2.correct = false) (fun _ _ => trivial) ?_) fun _ _ hz => Or.inr hz.2
        intro z hz
        rw [mem_support_pure_iff] at hz
        subst hz
        rfl
      · rcases hr₁ : S₁.recvA s₁.stA ρ₁ with _ | ⟨k₁, t₁, st₁⟩ <;>
          rw [hr₁, hr₂] at hr <;> simp only [RecvRel] at hr
        obtain ⟨rfl, rfl, hst⟩ := hr
        rw [oracleRecvA_run_eq_of_accept S₁ s₁ h₁ hr₁, oracleRecvA_run_eq_of_accept S₂ s₂ h₂ hr₂]
        exact relTriple_pure_pure (Or.inl (h.recvAUpdate _ _ _ hst))
  · change RelTriple ((oracleRecvB S₁ n).run s₁) ((oracleRecvB S₂ n).run s₂) _
    have hm := h.msgA n
    rcases h₁ : s₁.msgA n with _ | ⟨ρ₁, tsnd⟩ <;> rcases h₂ : s₂.msgA n with _ | ⟨ρ₂, tsnd₂⟩ <;>
      rw [h₁, h₂] at hm <;> cases hm
    · rw [oracleRecvB_run_eq_of_none S₁ s₁ h₁, oracleRecvB_run_eq_of_none S₂ s₂ h₂]
      exact relTriple_pure_pure (Or.inl h)
    · rename_i hm
      obtain ⟨hρ, rfl⟩ := hm
      have hr := hrB n _ ρ₁ ρ₂ h₁ h₂ hρ
      rcases hr₂ : S₂.recvB s₂.stB ρ₂ with _ | ⟨k₂, t₂, st₂⟩
      · rw [oracleRecvB_run_eq_of_refuse S₂ s₂ h₂ hr₂]
        refine relTriple_post_mono (relTriple_prod (P := fun _ => True)
          (Q := fun z => z.2.correct = false) (fun _ _ => trivial) ?_) fun _ _ hz => Or.inr hz.2
        intro z hz
        rw [mem_support_pure_iff] at hz
        subst hz
        rfl
      · rcases hr₁ : S₁.recvB s₁.stB ρ₁ with _ | ⟨k₁, t₁, st₁⟩ <;>
          rw [hr₁, hr₂] at hr <;> simp only [RecvRel] at hr
        obtain ⟨rfl, rfl, hst⟩ := hr
        rw [oracleRecvB_run_eq_of_accept S₁ s₁ h₁ hr₁, oracleRecvB_run_eq_of_accept S₂ s₂ h₂ hr₂]
        exact relTriple_pure_pure (Or.inl (h.recvBUpdate _ _ _ hst))

end Step

/-! ### The budgeted transfer theorem -/

/-- Let `S₂` satisfy the premises of `SCKAScheme.correctness_error_le_of_potential` with invariant
`Inv₂`, potential `V₂` and error `ε`. Let `S₁` have an invariant `Inv₁` that holds initially and
that every query keeps. Assume the step obligations of `TransferObligations` on states that meet
`Inv₁`, for a send only if `nA + nB < Bud`, for a receive only if `nA + nB ≤ Bud`. Then every
adversary against `S₁` with at most `q < Bud` send queries causes a false correctness flag with
probability at most `q · ε`. -/
theorem correctness_error_le_of_budgeted_steps [DecidableEq I]
    (S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ I Rho₁ Rand₁)
    (S₂ : SCKAScheme ProbComp IK₂ StA₂ StB₂ I Rho₂ Rand₂)
    (Inv₂ : IK₂ → GameState StA₂ StB₂ I Rho₂ → Prop) (V₂ : GameState StA₂ StB₂ I Rho₂ → ℝ≥0∞)
    (ε : ℝ≥0∞)
    (hV₂ : ∀ s, s.correct = false → 1 ≤ V₂ s)
    (hinit₂ : ∀ ik ∈ support S₂.initKeyGen, ∀ stA ∈ support (S₂.initA ik),
      ∀ stB ∈ support (S₂.initB ik), Inv₂ ik (initGameState stA stB) ∧ V₂ (initGameState stA stB) = 0)
    (hpres₂ : ∀ ik, QueryImpl.PreservesInv (sckaCorrectnessImpl S₂) (Inv₂ ik))
    (hstep₂ : ∀ ik (t : (sckaCorrectnessSpec Rho₂).Domain) s, Inv₂ ik s →
      wp ((sckaCorrectnessImpl S₂ t).run s) (fun z => V₂ z.2) ≤
        V₂ s + if isSendQuery (Rho := Rho₂) t then ε else 0)
    (Inv₁ : GameState StA₁ StB₁ I Rho₁ → Prop)
    (RA : StA₁ → StA₂ → Prop) (RB : StB₁ → StB₂ → Prop) (RM : Rho₁ → Rho₂ → Prop) (Bud : ℕ)
    (init : ∀ ik₁ ∈ support S₁.initKeyGen, ∀ stA₁ ∈ support (S₁.initA ik₁),
      ∀ stB₁ ∈ support (S₁.initB ik₁),
        Inv₁ (initGameState stA₁ stB₁) ∧
        ∃ ik₂ ∈ support S₂.initKeyGen, ∃ stA₂ ∈ support (S₂.initA ik₂),
          ∃ stB₂ ∈ support (S₂.initB ik₂), RA stA₁ stA₂ ∧ RB stB₁ stB₂)
    (pres : QueryImpl.PreservesInv (sckaCorrectnessImpl S₁) Inv₁)
    (sendA : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂),
      s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB < Bud → GameRel RA RB RM s₁ s₂ →
        Inv₂ ik₂ s₂ → RelTriple (S₁.sendA s₁.stA) (S₂.sendA s₂.stA) (SendRel RA RM))
    (sendB : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂),
      s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB < Bud → GameRel RA RB RM s₁ s₂ →
        Inv₂ ik₂ s₂ → RelTriple (S₁.sendB s₁.stB) (S₂.sendB s₂.stB) (SendRel RB RM))
    (recvA : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
      (n tsnd : ℕ) (ρ₁ : Rho₁) (ρ₂ : Rho₂),
      s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB ≤ Bud → GameRel RA RB RM s₁ s₂ →
        Inv₂ ik₂ s₂ → s₁.msgB n = some (ρ₁, tsnd) → s₂.msgB n = some (ρ₂, tsnd) → RM ρ₁ ρ₂ →
          RecvRel RA (S₁.recvA s₁.stA ρ₁) (S₂.recvA s₂.stA ρ₂))
    (recvB : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
      (n tsnd : ℕ) (ρ₁ : Rho₁) (ρ₂ : Rho₂),
      s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB ≤ Bud → GameRel RA RB RM s₁ s₂ →
        Inv₂ ik₂ s₂ → s₁.msgA n = some (ρ₁, tsnd) → s₂.msgA n = some (ρ₂, tsnd) → RM ρ₁ ρ₂ →
          RecvRel RB (S₁.recvB s₁.stB ρ₁) (S₂.recvB s₂.stB ρ₂))
    (adv : SCKACorrectnessAdversary Rho₁) (q : ℕ) (hq : SendQueryBound adv q) (hqB : q < Bud) :
    1 - Pr{let x ← correctnessExp S₁ adv}[x = true] ≤ q * ε := by
  -- The invariant with `k` send queries left.
  let Inv : ℕ → GameState StA₁ StB₁ I Rho₁ → Prop := fun k s => Inv₁ s ∧ s.nA + s.nB + k ≤ q
  let V := transferPotential RA RB RM Inv₂ V₂
  have hpresB : ∀ (t : (sckaCorrectnessSpec Rho₁).Domain) k s, Inv k s →
      (isSendQuery (Rho := Rho₁) t = true → 0 < k) →
      ∀ z ∈ support ((sckaCorrectnessImpl S₁ t).run s),
        Inv (if isSendQuery (Rho := Rho₁) t = true then k - 1 else k) z.2 := by
    intro t k s ⟨hI, hk⟩ hallow z hz
    refine ⟨pres t s hI z hz, ?_⟩
    have hle := nA_add_nB_le S₁ t s z hz
    by_cases ht : isSendQuery (Rho := Rho₁) t = true
    · have := hallow ht
      simp only [ht, ↓reduceIte] at hle ⊢
      omega
    · simp only [ht, Bool.false_eq_true, ↓reduceIte] at hle ⊢
      omega
  have hstepB : ∀ (t : (sckaCorrectnessSpec Rho₁).Domain) k s, Inv k s →
      (isSendQuery (Rho := Rho₁) t = true → 0 < k) →
      wp ((sckaCorrectnessImpl S₁ t).run s) (fun z => V z.2) ≤
        V s + if isSendQuery (Rho := Rho₁) t = true then ε else 0 := by
    intro t k s₁ ⟨hI, hk⟩ hallow
    have hle1 : wp ((sckaCorrectnessImpl S₁ t).run s₁) (fun z => V z.2) ≤ 1 :=
      wp_le_const_of_support _ fun z _ => transferPotential_le_one z.2
    by_cases hc : s₁.correct = true
    · have key : ∀ s₂ ik₂, GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
          wp ((sckaCorrectnessImpl S₁ t).run s₁) (fun z => V z.2) ≤
            V₂ s₂ + if isSendQuery (Rho := Rho₁) t = true then ε else 0 := by
        intro s₂ ik₂ h hinv
        have hbud : s₁.nA + s₁.nB ≤ Bud := by omega
        have hst := step_relTriple_of (S₁ := S₁) (S₂ := S₂) t s₁ s₂ h
          (fun ht => sendA ik₂ s₁ s₂ hc hI (by have := hallow ht; omega) h hinv)
          (fun ht => sendB ik₂ s₁ s₂ hc hI (by have := hallow ht; omega) h hinv)
          (fun n tsnd ρ₁ ρ₂ => recvA ik₂ s₁ s₂ n tsnd ρ₁ ρ₂ hc hI hbud h hinv)
          (fun n tsnd ρ₁ ρ₂ => recvB ik₂ s₁ s₂ n tsnd ρ₁ ρ₂ hc hI hbud h hinv)
        calc _ ≤ wp ((sckaCorrectnessImpl S₂ (castQuery t)).run s₂) (fun z => V₂ z.2) :=
              wp_le_of_relTriple hst fun z₁ _ z₂ hz₂ hr => transferPotential_le hV₂
                (hpres₂ ik₂ (castQuery t) s₂ hinv z₂ hz₂) hr
          _ ≤ V₂ s₂ + if isSendQuery (Rho := Rho₂) (castQuery t) then ε else 0 :=
              hstep₂ ik₂ _ s₂ hinv
          _ = _ := by rw [isSendQuery_castQuery]
      have hV : V s₁ = min 1 (⨅ (s₂ : GameState StA₂ StB₂ I Rho₂)
            (_ : GameRel RA RB RM s₁ s₂ ∧ ∃ ik₂, Inv₂ ik₂ s₂), V₂ s₂) := by
        simp [V, transferPotential, hc]
      rw [hV, ← min_add_add_right]
      refine le_min (hle1.trans le_self_add) ?_
      rw [ENNReal.iInf_add]
      refine le_iInf fun s₂ => ?_
      rw [ENNReal.iInf_add]
      exact le_iInf fun ⟨h, ik₂, hinv⟩ => key s₂ ik₂ h hinv
    · have hV : V s₁ = 1 := by
        simp [V, transferPotential, hc]
      rw [hV]
      exact hle1.trans le_self_add
  -- The expected potential of a complete run from any initial state is at most `q · ε`.
  have hrun : ∀ ik ∈ support S₁.initKeyGen, ∀ stA ∈ support (S₁.initA ik),
      ∀ stB ∈ support (S₁.initB ik),
        wp ((simulateQ (sckaCorrectnessImpl S₁) adv).run (initGameState stA stB))
          (fun z => if z.2.correct then 0 else 1) ≤ q * ε := by
    intro ik₁ hik₁ stA₁ hA₁ stB₁ hB₁
    obtain ⟨hI, ik₂, hik₂, stA₂, hA₂, stB₂, hB₂, hRA, hRB⟩ := init ik₁ hik₁ stA₁ hA₁ stB₁ hB₁
    obtain ⟨hinv, hV0⟩ := hinit₂ ik₂ hik₂ stA₂ hA₂ stB₂ hB₂
    have hrel : GameRel RA RB RM (initGameState stA₁ stB₁ : GameState StA₁ StB₁ I Rho₁)
        (initGameState stA₂ stB₂) :=
      { stA := hRA, stB := hRB, msgA := fun _ => .none, msgB := fun _ => .none,
        keyA := rfl, keyB := rfl, nA := rfl, nB := rfl, tcurA := rfl, tcurB := rfl,
        correct := rfl }
    have h0 : V (initGameState stA₁ stB₁) = 0 :=
      le_antisymm ((transferPotential_le hV₂ hinv (Or.inl hrel)).trans_eq hV0) zero_le
    have h := wp_simulateQ_run_le_budget (sckaCorrectnessImpl S₁) Inv V
      (fun t => isSendQuery (Rho := Rho₁) t = true) ε hpresB hstepB adv q hq _
      ⟨hI, by simp [initGameState]⟩
    rw [h0, zero_add] at h
    refine le_trans (wp_mono _ fun z => ?_) h
    split_ifs with hz
    · exact zero_le
    · simp [V, transferPotential, hz]
  -- The failure probability is at most the expected indicator of a false flag.
  have hexp : correctnessExp S₁ adv =
      S₁.initKeyGen >>= fun ik => S₁.initA ik >>= fun stA => S₁.initB ik >>= fun stB =>
        (fun z => z.2.correct) <$>
          (simulateQ (sckaCorrectnessImpl S₁) adv).run (initGameState stA stB) := by
    simp [correctnessExp, map_eq_bind_pure_comp]
  have hle : Pr{let x ← correctnessExp S₁ adv}[x = false] ≤
      wp (correctnessExp S₁ adv) (fun b => if b then 0 else 1) :=
    prEvent_le_wp _ _ _ fun b hb => by simp [hb]
  have hfalse : Pr{let x ← correctnessExp S₁ adv}[x = false] =
      1 - Pr{let x ← correctnessExp S₁ adv}[x = true] :=
    OracleComp.prEvent_eq_false_eq_one_sub _
  rw [← hfalse]
  refine hle.trans ?_
  rw [hexp, wp_bind]
  refine wp_le_const_of_support _ fun ik hik => ?_
  rw [wp_bind]
  refine wp_le_const_of_support _ fun stA hA => ?_
  rw [wp_bind]
  refine wp_le_const_of_support _ fun stB hB => ?_
  rw [wp_map, Function.comp_def]
  exact hrun ik hik stA hA stB hB

end SpqrBridge
