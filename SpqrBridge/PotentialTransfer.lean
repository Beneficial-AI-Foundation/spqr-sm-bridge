/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SecureMessaging.SCKA.Correctness
import VCVio.ProgramLogic.Relational.Basic

/-!
# Transfer of the SCKA correctness bound between related schemes

Let `S₂` be an SCKA scheme whose correctness bound is proved with
`SCKAScheme.correctness_error_le_of_potential`, from an invariant `Inv₂` and a potential `V₂`.
Let `S₁` be a second scheme, related to `S₂` by relations `RA`, `RB` on party states and `RM` on
messages. If the two schemes correspond query by query (`TransferObligations`), then `S₁` has the
same bound `q · ε` (`correctness_error_le_of_transfer`).

The proof applies `correctness_error_le_of_potential` to `S₁` with the trivial invariant and the
potential `transferPotential`: `1` once the flag of `S₁` is false, and otherwise the least `V₂` of a
related `S₂` game state that meets `Inv₂`, capped at `1`. The cap makes every state without a
related state cost nothing, so `S₁` needs no invariant of its own, and no relation is needed after
the flag becomes false. Each query is handled by a coupling of one step of the two games
(`step_relTriple`), not by a coupling of the whole runs, so the adversary is never shared between
the games.
-/

open OracleSpec OracleComp ENNReal MeasureTheory
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open SCKAScheme

namespace SpqrBridge

/-- If two computations are coupled on `R`, and `f a ≤ g b` for supported `a`, `b` related by `R`,
then the expectation of `f` is at most the expectation of `g`. -/
theorem wp_le_of_relTriple {α β : Type} {oa : ProbComp α} {ob : ProbComp β}
    {R : RelPost α β} (h : RelTriple oa ob R) {f : α → ℝ≥0∞} {g : β → ℝ≥0∞}
    (hfg : ∀ a ∈ support oa, ∀ b ∈ support ob, R a b → f a ≤ g b) :
    wp oa f ≤ wp ob g := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace β := ⊤
  obtain ⟨c, hc⟩ := relTriple_iff_relWP.1 h
  have h1 : ∫⁻ a, f a ∂𝒟[oa] = ∫⁻ z, f z.1 ∂c.joint := by
    have e : 𝒟[oa] = c.joint.map Prod.fst := c.isCoupling.fst_eq.symm
    calc ∫⁻ a, f a ∂𝒟[oa] = ∫⁻ a, f a ∂(c.joint.map Prod.fst) := by rw [← e]
      _ = _ := lintegral_map Measurable.of_discrete measurable_fst
  have h2 : ∫⁻ b, g b ∂𝒟[ob] = ∫⁻ z, g z.2 ∂c.joint := by
    have e : 𝒟[ob] = c.joint.map Prod.snd := c.isCoupling.snd_eq.symm
    calc ∫⁻ b, g b ∂𝒟[ob] = ∫⁻ b, g b ∂(c.joint.map Prod.snd) := by rw [← e]
      _ = _ := lintegral_map Measurable.of_discrete measurable_snd
  rw [wp_eq_lintegral _ _ Measurable.of_discrete, wp_eq_lintegral _ _ Measurable.of_discrete,
    h1, h2]
  refine lintegral_mono_ae ?_
  filter_upwards [hc, ae_mem_support_prod c] with z hR hs
  exact hfg _ hs.1 _ hs.2 hR

variable {IK₁ StA₁ StB₁ Rho₁ Rand₁ IK₂ StA₂ StB₂ Rho₂ Rand₂ I : Type}

/-! ### Related game states -/

/-- Two game states are related when their party states are related by `RA` and `RB`, their
transit arrays hold messages related by `RM` with equal epochs, and all other bookkeeping of the
correctness game (key tables, counters, current epochs, correctness flag) is equal. -/
structure GameRel (RA : StA₁ → StA₂ → Prop) (RB : StB₁ → StB₂ → Prop)
    (RM : Rho₁ → Rho₂ → Prop)
    (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂) : Prop where
  stA : RA s₁.stA s₂.stA
  stB : RB s₁.stB s₂.stB
  keyA : s₂.keyA = s₁.keyA
  keyB : s₂.keyB = s₁.keyB
  msgA : ∀ n, Option.Rel (fun p q => RM p.1 q.1 ∧ q.2 = p.2) (s₁.msgA n) (s₂.msgA n)
  msgB : ∀ n, Option.Rel (fun p q => RM p.1 q.1 ∧ q.2 = p.2) (s₁.msgB n) (s₂.msgB n)
  nA : s₂.nA = s₁.nA
  nB : s₂.nB = s₁.nB
  tcurA : s₂.tcurA = s₁.tcurA
  tcurB : s₂.tcurB = s₁.tcurB
  correct : s₂.correct = s₁.correct

/-- Correspondence of two send results: both refuse, or both succeed with the same key and epoch,
related messages and related next states. -/
def SendRel {St₁ St₂ : Type} (R : St₁ → St₂ → Prop) (RM : Rho₁ → Rho₂ → Prop) :
    Option (Option (ℕ × I) × Rho₁ × ℕ × St₁) → Option (Option (ℕ × I) × Rho₂ × ℕ × St₂) → Prop
  | none, none => True
  | some (k₁, ρ₁, t₁, st₁), some (k₂, ρ₂, t₂, st₂) =>
      k₂ = k₁ ∧ RM ρ₁ ρ₂ ∧ t₂ = t₁ ∧ R st₁ st₂
  | _, _ => False

/-- Correspondence of two receive results: the second scheme refuses, or both accept with the
same key and epoch and related next states. A refusal of the second scheme is compatible with any
result of the first, because it clears the second game's correctness flag. -/
def RecvRel {St₁ St₂ : Type} (R : St₁ → St₂ → Prop) :
    Option (Option (ℕ × I) × ℕ × St₁) → Option (Option (ℕ × I) × ℕ × St₂) → Prop
  | _, none => True
  | some (k₁, t₁, st₁), some (k₂, t₂, st₂) => k₂ = k₁ ∧ t₂ = t₁ ∧ R st₁ st₂
  | none, some _ => False

/-- The per-query obligations that relate `S₁` to `S₂`. In each obligation the two game states
are related, the flag of the first is true, and the second meets `S₂`'s invariant `Inv₂`.

* `init`: every initial pair of party states of `S₁` has a related initial pair of `S₂`, from a
  supported initial key. This is a statement about supports only.
* `sendA`, `sendB`: the sends of the two schemes are coupled on `SendRel`.
* `recvA`, `recvB`: on a delivered message and its related message, the receives agree in the
  sense of `RecvRel`. -/
structure TransferObligations [DecidableEq I]
    (S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ I Rho₁ Rand₁)
    (S₂ : SCKAScheme ProbComp IK₂ StA₂ StB₂ I Rho₂ Rand₂)
    (Inv₂ : IK₂ → GameState StA₂ StB₂ I Rho₂ → Prop)
    (RA : StA₁ → StA₂ → Prop) (RB : StB₁ → StB₂ → Prop) (RM : Rho₁ → Rho₂ → Prop) : Prop where
  init : ∀ ik₁ ∈ support S₁.initKeyGen, ∀ stA₁ ∈ support (S₁.initA ik₁),
    ∀ stB₁ ∈ support (S₁.initB ik₁),
      ∃ ik₂ ∈ support S₂.initKeyGen, ∃ stA₂ ∈ support (S₂.initA ik₂),
        ∃ stB₂ ∈ support (S₂.initB ik₂), RA stA₁ stA₂ ∧ RB stB₁ stB₂
  sendA : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂),
    s₁.correct = true → GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
      RelTriple (S₁.sendA s₁.stA) (S₂.sendA s₂.stA) (SendRel RA RM)
  sendB : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂),
    s₁.correct = true → GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
      RelTriple (S₁.sendB s₁.stB) (S₂.sendB s₂.stB) (SendRel RB RM)
  recvA : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
    (n tsnd : ℕ) (ρ₁ : Rho₁) (ρ₂ : Rho₂),
    s₁.correct = true → GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
      s₁.msgB n = some (ρ₁, tsnd) → s₂.msgB n = some (ρ₂, tsnd) → RM ρ₁ ρ₂ →
        RecvRel RA (S₁.recvA s₁.stA ρ₁) (S₂.recvA s₂.stA ρ₂)
  recvB : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
    (n tsnd : ℕ) (ρ₁ : Rho₁) (ρ₂ : Rho₂),
    s₁.correct = true → GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
      s₁.msgA n = some (ρ₁, tsnd) → s₂.msgA n = some (ρ₂, tsnd) → RM ρ₁ ρ₂ →
        RecvRel RB (S₁.recvB s₁.stB ρ₁) (S₂.recvB s₂.stB ρ₂)

/-! ### Game updates preserve the relation -/

section Updates

variable [DecidableEq I] {RA : StA₁ → StA₂ → Prop} {RB : StB₁ → StB₂ → Prop}
  {RM : Rho₁ → Rho₂ → Prop} {s₁ : GameState StA₁ StB₁ I Rho₁} {s₂ : GameState StA₂ StB₂ I Rho₂}

theorem GameRel.sendAUpdate (h : GameRel RA RB RM s₁ s₂) (keyOpt : Option (ℕ × I))
    {ρ₁ : Rho₁} {ρ₂ : Rho₂} (hρ : RM ρ₁ ρ₂) (tsnd : ℕ) {st₁ : StA₁} {st₂ : StA₂}
    (hst : RA st₁ st₂) :
    GameRel RA RB RM (SCKAScheme.sendAUpdate s₁ keyOpt ρ₁ tsnd st₁)
      (SCKAScheme.sendAUpdate s₂ keyOpt ρ₂ tsnd st₂) := by
  have hmsg : ∀ n, Option.Rel (fun p q => RM p.1 q.1 ∧ q.2 = p.2)
      (Function.update s₁.msgA (s₁.nA + 1) (some (ρ₁, tsnd)) n)
      (Function.update s₂.msgA (s₂.nA + 1) (some (ρ₂, tsnd)) n) := by
    intro n
    rw [h.nA]
    by_cases hn : n = s₁.nA + 1
    · subst hn; simp only [Function.update_self]; exact .some ⟨hρ, rfl⟩
    · simp only [Function.update_of_ne hn]; exact h.msgA n
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    exact { stA := hst, stB := h.stB, msgA := hmsg, msgB := h.msgB,
            keyA := by simp [SCKAScheme.sendAUpdate, h.keyA],
            keyB := by simp [SCKAScheme.sendAUpdate, h.keyB],
            nA := by simp [SCKAScheme.sendAUpdate, h.nA],
            nB := by simp [SCKAScheme.sendAUpdate, h.nB],
            tcurA := by simp [SCKAScheme.sendAUpdate],
            tcurB := by simp [SCKAScheme.sendAUpdate, h.tcurB],
            correct := by simp [SCKAScheme.sendAUpdate, h.correct, h.tcurA, h.keyA, h.keyB] }

theorem GameRel.sendBUpdate (h : GameRel RA RB RM s₁ s₂) (keyOpt : Option (ℕ × I))
    {ρ₁ : Rho₁} {ρ₂ : Rho₂} (hρ : RM ρ₁ ρ₂) (tsnd : ℕ) {st₁ : StB₁} {st₂ : StB₂}
    (hst : RB st₁ st₂) :
    GameRel RA RB RM (SCKAScheme.sendBUpdate s₁ keyOpt ρ₁ tsnd st₁)
      (SCKAScheme.sendBUpdate s₂ keyOpt ρ₂ tsnd st₂) := by
  have hmsg : ∀ n, Option.Rel (fun p q => RM p.1 q.1 ∧ q.2 = p.2)
      (Function.update s₁.msgB (s₁.nB + 1) (some (ρ₁, tsnd)) n)
      (Function.update s₂.msgB (s₂.nB + 1) (some (ρ₂, tsnd)) n) := by
    intro n
    rw [h.nB]
    by_cases hn : n = s₁.nB + 1
    · subst hn; simp only [Function.update_self]; exact .some ⟨hρ, rfl⟩
    · simp only [Function.update_of_ne hn]; exact h.msgB n
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    exact { stA := h.stA, stB := hst, msgA := h.msgA, msgB := hmsg,
            keyA := by simp [SCKAScheme.sendBUpdate, h.keyA],
            keyB := by simp [SCKAScheme.sendBUpdate, h.keyB],
            nA := by simp [SCKAScheme.sendBUpdate, h.nA],
            nB := by simp [SCKAScheme.sendBUpdate, h.nB],
            tcurA := by simp [SCKAScheme.sendBUpdate, h.tcurA],
            tcurB := by simp [SCKAScheme.sendBUpdate],
            correct := by simp [SCKAScheme.sendBUpdate, h.correct, h.tcurB, h.keyA, h.keyB] }

theorem GameRel.recvAUpdate (h : GameRel RA RB RM s₁ s₂) (tsnd : ℕ) (keyOpt : Option (ℕ × I))
    (trcv : ℕ) {st₁ : StA₁} {st₂ : StA₂} (hst : RA st₁ st₂) :
    GameRel RA RB RM (SCKAScheme.recvAUpdate s₁ tsnd keyOpt trcv st₁)
      (SCKAScheme.recvAUpdate s₂ tsnd keyOpt trcv st₂) := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    exact { stA := hst, stB := h.stB, msgA := h.msgA, msgB := h.msgB,
            keyA := by simp [SCKAScheme.recvAUpdate, h.keyA],
            keyB := by simp [SCKAScheme.recvAUpdate, h.keyB],
            nA := by simp [SCKAScheme.recvAUpdate, h.nA],
            nB := by simp [SCKAScheme.recvAUpdate, h.nB],
            tcurA := by simp [SCKAScheme.recvAUpdate, h.tcurA],
            tcurB := by simp [SCKAScheme.recvAUpdate, h.tcurB],
            correct := by simp [SCKAScheme.recvAUpdate, h.correct, h.tcurA, h.keyA, h.keyB] }

theorem GameRel.recvBUpdate (h : GameRel RA RB RM s₁ s₂) (tsnd : ℕ) (keyOpt : Option (ℕ × I))
    (trcv : ℕ) {st₁ : StB₁} {st₂ : StB₂} (hst : RB st₁ st₂) :
    GameRel RA RB RM (SCKAScheme.recvBUpdate s₁ tsnd keyOpt trcv st₁)
      (SCKAScheme.recvBUpdate s₂ tsnd keyOpt trcv st₂) := by
  rcases keyOpt with _ | ⟨tI, key⟩ <;>
    exact { stA := h.stA, stB := hst, msgA := h.msgA, msgB := h.msgB,
            keyA := by simp [SCKAScheme.recvBUpdate, h.keyA],
            keyB := by simp [SCKAScheme.recvBUpdate, h.keyB],
            nA := by simp [SCKAScheme.recvBUpdate, h.nA],
            nB := by simp [SCKAScheme.recvBUpdate, h.nB],
            tcurA := by simp [SCKAScheme.recvBUpdate, h.tcurA],
            tcurB := by simp [SCKAScheme.recvBUpdate, h.tcurB],
            correct := by simp [SCKAScheme.recvBUpdate, h.correct, h.tcurB, h.keyA, h.keyB] }

end Updates

/-! ### The transferred potential -/

section Potential

variable (RA : StA₁ → StA₂ → Prop) (RB : StB₁ → StB₂ → Prop) (RM : Rho₁ → Rho₂ → Prop)
  (Inv₂ : IK₂ → GameState StA₂ StB₂ I Rho₂ → Prop) (V₂ : GameState StA₂ StB₂ I Rho₂ → ℝ≥0∞)

/-- The potential of a game state of `S₁`: `1` if its flag is false, and otherwise the least
potential `V₂` of a related game state of `S₂` that meets `Inv₂` for some initial key, capped at
`1`. -/
noncomputable def transferPotential (s₁ : GameState StA₁ StB₁ I Rho₁) : ℝ≥0∞ :=
  if s₁.correct then
    min 1 (⨅ (s₂ : GameState StA₂ StB₂ I Rho₂)
      (_ : GameRel RA RB RM s₁ s₂ ∧ ∃ ik₂, Inv₂ ik₂ s₂), V₂ s₂)
  else 1

variable {RA RB RM Inv₂ V₂}

theorem transferPotential_le_one (s₁ : GameState StA₁ StB₁ I Rho₁) :
    transferPotential RA RB RM Inv₂ V₂ s₁ ≤ 1 := by
  unfold transferPotential
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- If `V₂` is at least `1` on false flags, the potential of a game state of `S₁` is at most
`V₂` of any `S₂` state that meets `Inv₂` and is related to it or has a false flag. -/
theorem transferPotential_le (hV₂ : ∀ s : GameState StA₂ StB₂ I Rho₂, s.correct = false → 1 ≤ V₂ s)
    {s₁ : GameState StA₁ StB₁ I Rho₁} {s₂ : GameState StA₂ StB₂ I Rho₂} {ik₂ : IK₂}
    (hinv : Inv₂ ik₂ s₂) (h : GameRel RA RB RM s₁ s₂ ∨ s₂.correct = false) :
    transferPotential RA RB RM Inv₂ V₂ s₁ ≤ V₂ s₂ := by
  rcases h with h | h
  · by_cases hc : s₁.correct = true
    · unfold transferPotential
      simp only [hc, ↓reduceIte]
      exact (min_le_right _ _).trans (iInf₂_le s₂ ⟨h, ik₂, hinv⟩)
    · exact (transferPotential_le_one s₁).trans
        (hV₂ s₂ (by rw [h.correct]; simpa using hc))
  · exact (transferPotential_le_one s₁).trans (hV₂ s₂ h)

end Potential

/-! ### One step of the two games -/

/-- The same query index of the correctness game, read for the second message type. -/
def castQuery : (sckaCorrectnessSpec Rho₁).Domain → (sckaCorrectnessSpec Rho₂).Domain
  | sckaCorrectnessSpec.OUnif n => sckaCorrectnessSpec.OUnif n
  | sckaCorrectnessSpec.OSendA => sckaCorrectnessSpec.OSendA
  | sckaCorrectnessSpec.OSendB => sckaCorrectnessSpec.OSendB
  | sckaCorrectnessSpec.ORecvA n => sckaCorrectnessSpec.ORecvA n
  | sckaCorrectnessSpec.ORecvB n => sckaCorrectnessSpec.ORecvB n

theorem isSendQuery_castQuery (t : (sckaCorrectnessSpec Rho₁).Domain) :
    isSendQuery (Rho := Rho₂) (castQuery t) = isSendQuery (Rho := Rho₁) t := by
  rcases t with ((((n | u) | u) | n) | n) <;> rfl

section Step

variable [DecidableEq I] {S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ I Rho₁ Rand₁}
  {S₂ : SCKAScheme ProbComp IK₂ StA₂ StB₂ I Rho₂ Rand₂}
  {Inv₂ : IK₂ → GameState StA₂ StB₂ I Rho₂ → Prop}
  {RA : StA₁ → StA₂ → Prop} {RB : StB₁ → StB₂ → Prop} {RM : Rho₁ → Rho₂ → Prop}

/-- One query of the two correctness games, from related states where the first flag is true and
the second state meets `Inv₂`, is coupled so that the successor states are related or the second
flag is false. -/
theorem step_relTriple (hob : TransferObligations S₁ S₂ Inv₂ RA RB RM) (ik₂ : IK₂)
    (t : (sckaCorrectnessSpec Rho₁).Domain)
    (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
    (hc : s₁.correct = true) (h : GameRel RA RB RM s₁ s₂) (hinv : Inv₂ ik₂ s₂) :
    RelTriple ((sckaCorrectnessImpl S₁ t).run s₁)
      ((sckaCorrectnessImpl S₂ (castQuery t)).run s₂)
      (fun z₁ z₂ => GameRel RA RB RM z₁.2 z₂.2 ∨ z₂.2.correct = false) := by
  rcases t with ((((n | u) | u) | n) | n)
  · -- Uniform randomness leaves both states unchanged.
    refine relTriple_post_mono
      (relTriple_prod (P := fun z => z.2 = s₁) (Q := fun z => z.2 = s₂) ?_ ?_) ?_
    · exact fun z hz => oracleUnif_preservesInv (· = s₁) n s₁ rfl z hz
    · exact fun z hz => oracleUnif_preservesInv (· = s₂) n s₂ rfl z hz
    · rintro z₁ z₂ ⟨h1, h2⟩
      exact Or.inl (h1 ▸ h2 ▸ h)
  · change RelTriple ((oracleSendA S₁ ()).run s₁) ((oracleSendA S₂ ()).run s₂) _
    rw [oracleSendA_run_eq, oracleSendA_run_eq]
    refine relTriple_map (relTriple_post_mono (hob.sendA ik₂ s₁ s₂ hc h hinv) ?_)
    rintro (_ | ⟨k₁, ρ₁, t₁, st₁⟩) (_ | ⟨k₂, ρ₂, t₂, st₂⟩) hr <;> simp only [SendRel] at hr
    · exact Or.inl h
    · obtain ⟨rfl, hρ, rfl, hst⟩ := hr
      exact Or.inl (h.sendAUpdate _ hρ _ hst)
  · change RelTriple ((oracleSendB S₁ ()).run s₁) ((oracleSendB S₂ ()).run s₂) _
    rw [oracleSendB_run_eq, oracleSendB_run_eq]
    refine relTriple_map (relTriple_post_mono (hob.sendB ik₂ s₁ s₂ hc h hinv) ?_)
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
      have hr := hob.recvA ik₂ s₁ s₂ n _ ρ₁ ρ₂ hc h hinv h₁ h₂ hρ
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
      have hr := hob.recvB ik₂ s₁ s₂ n _ ρ₁ ρ₂ hc h hinv h₁ h₂ hρ
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

/-! ### The transfer theorem -/

/-- Let `S₂` satisfy the premises of `SCKAScheme.correctness_error_le_of_potential` with invariant
`Inv₂`, potential `V₂` and error `ε`, and let `S₁` be related to `S₂` by `RA`, `RB`, `RM` through
`TransferObligations`. Then every adversary against `S₁` making at most `q` send queries causes a
false correctness flag with probability at most `q · ε`. -/
theorem correctness_error_le_of_transfer [DecidableEq I]
    (S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ I Rho₁ Rand₁)
    (S₂ : SCKAScheme ProbComp IK₂ StA₂ StB₂ I Rho₂ Rand₂)
    (Inv₂ : IK₂ → GameState StA₂ StB₂ I Rho₂ → Prop) (V₂ : GameState StA₂ StB₂ I Rho₂ → ℝ≥0∞)
    (ε : ℝ≥0∞)
    (hV₂ : ∀ s : GameState StA₂ StB₂ I Rho₂, s.correct = false → 1 ≤ V₂ s)
    (hinit₂ : ∀ ik ∈ support S₂.initKeyGen, ∀ stA ∈ support (S₂.initA ik),
      ∀ stB ∈ support (S₂.initB ik),
        Inv₂ ik (initGameState stA stB) ∧ V₂ (initGameState stA stB) = 0)
    (hpres₂ : ∀ ik, QueryImpl.PreservesInv (sckaCorrectnessImpl S₂) (Inv₂ ik))
    (hstep₂ : ∀ ik (t : (sckaCorrectnessSpec Rho₂).Domain) s, Inv₂ ik s →
      wp ((sckaCorrectnessImpl S₂ t).run s) (fun z => V₂ z.2) ≤
        V₂ s + if isSendQuery (Rho := Rho₂) t then ε else 0)
    (RA : StA₁ → StA₂ → Prop) (RB : StB₁ → StB₂ → Prop) (RM : Rho₁ → Rho₂ → Prop)
    (hob : TransferObligations S₁ S₂ Inv₂ RA RB RM)
    (adv : SCKACorrectnessAdversary Rho₁) (q : ℕ) (hq : SendQueryBound adv q) :
    1 - Pr{let x ← correctnessExp S₁ adv}[x = true] ≤ q * ε := by
  refine correctness_error_le_of_potential S₁ (fun _ _ => True)
    (transferPotential RA RB RM Inv₂ V₂) ε ?_ ?_ (fun _ _ _ _ _ _ => trivial) ?_ adv q hq
  · intro s hs
    simp [transferPotential, hs]
  · intro ik₁ hik₁ stA₁ hA₁ stB₁ hB₁
    refine ⟨trivial, ?_⟩
    obtain ⟨ik₂, hik₂, stA₂, hA₂, stB₂, hB₂, hRA, hRB⟩ := hob.init ik₁ hik₁ stA₁ hA₁ stB₁ hB₁
    obtain ⟨hinv, hV0⟩ := hinit₂ ik₂ hik₂ stA₂ hA₂ stB₂ hB₂
    have hrel : GameRel RA RB RM (initGameState stA₁ stB₁ : GameState StA₁ StB₁ I Rho₁)
        (initGameState stA₂ stB₂) :=
      { stA := hRA, stB := hRB, msgA := fun _ => .none, msgB := fun _ => .none,
        keyA := rfl, keyB := rfl, nA := rfl, nB := rfl, tcurA := rfl, tcurB := rfl,
        correct := rfl }
    exact le_antisymm ((transferPotential_le hV₂ hinv (Or.inl hrel)).trans_eq hV0) zero_le
  · intro _ t s₁ _
    have hle1 : wp ((sckaCorrectnessImpl S₁ t).run s₁)
        (fun z => transferPotential RA RB RM Inv₂ V₂ z.2) ≤ 1 :=
      wp_le_const_of_support _ fun z _ => transferPotential_le_one z.2
    by_cases hc : s₁.correct = true
    · have key : ∀ s₂ ik₂, GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
          wp ((sckaCorrectnessImpl S₁ t).run s₁)
            (fun z => transferPotential RA RB RM Inv₂ V₂ z.2) ≤
            V₂ s₂ + if isSendQuery (Rho := Rho₁) t then ε else 0 := by
        intro s₂ ik₂ h hinv
        calc _ ≤ wp ((sckaCorrectnessImpl S₂ (castQuery t)).run s₂) (fun z => V₂ z.2) :=
              wp_le_of_relTriple (step_relTriple hob ik₂ t s₁ s₂ hc h hinv)
                fun z₁ _ z₂ hz₂ hr => transferPotential_le hV₂
                  (hpres₂ ik₂ (castQuery t) s₂ hinv z₂ hz₂) hr
          _ ≤ V₂ s₂ + if isSendQuery (Rho := Rho₂) (castQuery t) then ε else 0 :=
              hstep₂ ik₂ _ s₂ hinv
          _ = _ := by rw [isSendQuery_castQuery]
      have hV : transferPotential RA RB RM Inv₂ V₂ s₁ =
          min 1 (⨅ (s₂ : GameState StA₂ StB₂ I Rho₂)
            (_ : GameRel RA RB RM s₁ s₂ ∧ ∃ ik₂, Inv₂ ik₂ s₂), V₂ s₂) := by
        simp [transferPotential, hc]
      rw [hV, ← min_add_add_right]
      refine le_min (hle1.trans le_self_add) ?_
      rw [ENNReal.iInf_add]
      refine le_iInf fun s₂ => ?_
      rw [ENNReal.iInf_add]
      exact le_iInf fun ⟨h, ik₂, hinv⟩ => key s₂ ik₂ h hinv
    · have hV : transferPotential RA RB RM Inv₂ V₂ s₁ = 1 := by
        simp [transferPotential, hc]
      rw [hV]
      exact hle1.trans le_self_add

end SpqrBridge
