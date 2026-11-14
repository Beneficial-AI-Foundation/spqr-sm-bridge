/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.IdealRng
import SpqrBridge.CodeCorrectness
import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# The correctness bound for the extracted `send` with a generator

`realScheme sampleInitKey i₁ i₂ seed` is `codeScheme sampleInitKey` with `realSendA i₁ i₂ seed`
as the send of both parties. Each send samples a generator state from `seed` and runs the
extracted `States.send` with the instances `i₁` and `i₂`.

`real_correctness_error_le`: assume `BridgeObligations` and `IdealRng i₁ seed 64`. Then the bound
of `code_correctness_error_le` holds for `realScheme`. The proof shows that the correctness
experiments of `realScheme` and `codeScheme` have the same distribution
(`realScheme_correctnessExp`), from `send_bridge` for each send.

That each send starts from a new state, independent of the earlier sends, is a modeling
assumption. Lean does not connect `IdealRng` to `OsRng`. The leaking sends of `realScheme` are
those of `codeScheme`. The correctness experiment does not use them.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states
open OracleSpec OracleComp ENNReal
open SCKAScheme

section Generic

variable {IK StA StB I Rho Rand : Type} [DecidableEq I]

/-- Let `IK`, `StA`, `StB`, `I`, `Rho` and `Rand` be types with `[DecidableEq I]`, and let `S₁` and
`S₂` be SCKA schemes over them. Let `S₁.sendA x =ᵈ S₂.sendA x` for every `x`. Then, for
every game state `st`,
`(oracleSendA S₁ ()).run st =ᵈ (oracleSendA S₂ ()).run st`. -/
theorem oracleSendA_run_evalDistEq (S₁ S₂ : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (h : ∀ x, S₁.sendA x =ᵈ S₂.sendA x) (st : GameState StA StB I Rho) :
    (oracleSendA S₁ ()).run st =ᵈ (oracleSendA S₂ ()).run st := by
  simp only [oracleSendA, StateT.run_bind, StateT.run_get, pure_bind]
  refine EvalDistEq.bind ?_ fun _ => EvalDistEq.rfl
  simpa using (h st.stA).map (fun r => (r, st))

/-- Let `IK`, `StA`, `StB`, `I`, `Rho` and `Rand` be types with `[DecidableEq I]`, and let `S₁` and
`S₂` be SCKA schemes over them. Let `S₁.sendB x =ᵈ S₂.sendB x` for every `x`. Then, for
every game state `st`,
`(oracleSendB S₁ ()).run st =ᵈ (oracleSendB S₂ ()).run st`. -/
theorem oracleSendB_run_evalDistEq (S₁ S₂ : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (h : ∀ x, S₁.sendB x =ᵈ S₂.sendB x) (st : GameState StA StB I Rho) :
    (oracleSendB S₁ ()).run st =ᵈ (oracleSendB S₂ ()).run st := by
  simp only [oracleSendB, StateT.run_bind, StateT.run_get, pure_bind]
  refine EvalDistEq.bind ?_ fun _ => EvalDistEq.rfl
  simpa using (h st.stB).map (fun r => (r, st))

/-- Let `IK`, `StA`, `StB`, `I`, `Rho` and `Rand` be types with `[DecidableEq I]`, and let `S` be
an SCKA scheme over them. Let `fA x =ᵈ S.sendA x` and `fB x =ᵈ S.sendB x` for every `x`. Then, for
every query `t` and
every game state `st`, the oracle of `sckaCorrectnessImpl { S with sendA := fA, sendB := fB }` and
the oracle of `sckaCorrectnessImpl S` give equal distributions on `t` from `st`. -/
theorem correctnessImpl_run_evalDistEq (S : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (fA : StA → ProbComp (Option (Option (ℕ × I) × Rho × ℕ × StA)))
    (fB : StB → ProbComp (Option (Option (ℕ × I) × Rho × ℕ × StB)))
    (hA : ∀ x, fA x =ᵈ S.sendA x) (hB : ∀ x, fB x =ᵈ S.sendB x)
    (t : (sckaCorrectnessSpec Rho).Domain) (st : GameState StA StB I Rho) :
    ((sckaCorrectnessImpl { S with sendA := fA, sendB := fB }) t).run st =ᵈ
      ((sckaCorrectnessImpl S) t).run st := by
  rcases t with (((t | t) | t) | t) | t
  · exact EvalDistEq.rfl
  · exact oracleSendA_run_evalDistEq { S with sendA := fA, sendB := fB } S hA st
  · exact oracleSendB_run_evalDistEq { S with sendA := fA, sendB := fB } S hB st
  · exact EvalDistEq.rfl
  · exact EvalDistEq.rfl

/-- Let `IK`, `StA`, `StB`, `I`, `Rho` and `Rand` be types with `[DecidableEq I]`, and let `S` be
an SCKA scheme over them. Let `fA x =ᵈ S.sendA x` and `fB x =ᵈ S.sendB x` for every `x`. Then, for
every correctness adversary `adv`,
`correctnessExp { S with sendA := fA, sendB := fB } adv =ᵈ correctnessExp S adv`. -/
theorem correctnessExp_evalDistEq (S : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (fA : StA → ProbComp (Option (Option (ℕ × I) × Rho × ℕ × StA)))
    (fB : StB → ProbComp (Option (Option (ℕ × I) × Rho × ℕ × StB)))
    (hA : ∀ x, fA x =ᵈ S.sendA x) (hB : ∀ x, fB x =ᵈ S.sendB x)
    (adv : SCKACorrectnessAdversary Rho) :
    correctnessExp { S with sendA := fA, sendB := fB } adv =ᵈ correctnessExp S adv := by
  simp only [correctnessExp]
  refine EvalDistEq.bind_right _ fun ik => EvalDistEq.bind_right _ fun stA =>
    EvalDistEq.bind_right _ fun stB => ?_
  exact EvalDistEq.bind (evalDistEq_simulateQ_run _ _
    (correctnessImpl_run_evalDistEq S fA fB hA hB) adv _) fun _ => EvalDistEq.rfl

end Generic

/-- `realScheme sampleInitKey i₁ i₂ seed` is `codeScheme sampleInitKey` with
`sendA := realSendA i₁ i₂ seed` and `sendB := realSendA i₁ i₂ seed`. All other fields, including
the leaking sends, are those of `codeScheme sampleInitKey`. Each send samples a new state from
`seed` and drops the final state. -/
noncomputable def realScheme (sampleInitKey : ProbComp InitKey) {R : Type}
    (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (seed : ProbComp R) :
    SCKAScheme ProbComp InitKey States States (B 32) Message (Slice Std.U8) :=
  { codeScheme sampleInitKey with
    sendA := realSendA i₁ i₂ seed
    sendB := realSendA i₁ i₂ seed }

/-- Let `IdealRng i₁ seed 64`. Then, for every correctness adversary `adv`,
`correctnessExp (realScheme sampleInitKey i₁ i₂ seed) adv =ᵈ
correctnessExp (codeScheme sampleInitKey) adv`. -/
theorem realScheme_correctnessExp (sampleInitKey : ProbComp InitKey) {R : Type}
    (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (seed : ProbComp R)
    (h : IdealRng i₁ seed 64) (adv : SCKACorrectnessAdversary Message) :
    correctnessExp (realScheme sampleInitKey i₁ i₂ seed) adv =ᵈ
      correctnessExp (codeScheme sampleInitKey) adv :=
  correctnessExp_evalDistEq (codeScheme sampleInitKey) _ _
    (send_bridge i₁ i₂ seed h) (send_bridge i₁ i₂ seed h) adv

/-- Assume `BridgeObligations` and `IdealRng i₁ seed 64`. Let `sampleInitKey` be a sampler of
`InitKey`, let `adv` be an SCKA correctness adversary with `SendQueryBound adv q`, and let
`q + 2 < 2 ^ 64`. Then the probability that
`correctnessExp (realScheme sampleInitKey i₁ i₂ seed) adv` does not return `true` is at most
`(q : ℝ≥0∞) * codeKem.correctnessError ProbCompRuntime.probComp`. -/
theorem real_correctness_error_le (hB : BridgeObligations) (sampleInitKey : ProbComp InitKey)
    {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R) (seed : ProbComp R)
    (hI : IdealRng i₁ seed 64) (adv : SCKACorrectnessAdversary Message) (q : ℕ)
    (hq : SendQueryBound adv q) (hq64 : q + 2 < 2 ^ 64) :
    1 - Pr{let x ← correctnessExp (realScheme sampleInitKey i₁ i₂ seed) adv}[x = true] ≤
      (q : ℝ≥0∞) * codeKem.correctnessError ProbCompRuntime.probComp := by
  rw [(realScheme_correctnessExp sampleInitKey i₁ i₂ seed hI adv).prEvent_eq]
  exact code_correctness_error_le hB sampleInitKey adv q hq hq64

end SpqrBridge
