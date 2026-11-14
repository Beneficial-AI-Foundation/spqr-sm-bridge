/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.PotentialTransfer
import SecureMessaging.SCKA.SPQR.Correctness

/-!
# Transfer of the SPQR correctness bound

Two uses of `correctness_error_le_of_transfer`. `transferObligations_self` relates every scheme to
itself, so the obligations can be met. `spqr_correctness_error_le_of_transfer` takes `S₂` to be
secure-messaging's SPQR scheme, with the invariant and potential of `SPQR.correctness_error_le`:
a scheme that meets the obligations against it inherits the bound `q` times the KEM correctness
error.
-/

open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open SCKAScheme

namespace SpqrBridge

variable {IK StA StB I Rho Rand : Type}

/-- Every scheme meets the obligations against itself, with equality as all three relations and
any invariant. -/
theorem transferObligations_self [DecidableEq I] (S : SCKAScheme ProbComp IK StA StB I Rho Rand)
    (Inv : IK → GameState StA StB I Rho → Prop) :
    TransferObligations S S Inv Eq Eq Eq where
  init := fun ik hik stA hA stB hB => ⟨ik, hik, stA, hA, stB, hB, rfl, rfl⟩
  sendA := fun _ s₁ s₂ _ h _ => by
    rw [← h.stA]
    refine relTriple_refl_of_mem_support _ fun o _ => ?_
    rcases o with _ | ⟨k, ρ, t, st⟩ <;> simp [SendRel]
  sendB := fun _ s₁ s₂ _ h _ => by
    rw [← h.stB]
    refine relTriple_refl_of_mem_support _ fun o _ => ?_
    rcases o with _ | ⟨k, ρ, t, st⟩ <;> simp [SendRel]
  recvA := fun _ s₁ s₂ _ _ _ _ _ h _ _ _ hρ => by
    subst hρ
    rw [← h.stA]
    rcases S.recvA s₁.stA _ with _ | ⟨k, t, st⟩ <;> simp [RecvRel]
  recvB := fun _ s₁ s₂ _ _ _ _ _ h _ _ _ hρ => by
    subst hρ
    rw [← h.stB]
    rcases S.recvB s₁.stB _ with _ | ⟨k, t, st⟩ <;> simp [RecvRel]

/-- The potential of `SPQR.correctness_error_le` is at least one on a game state whose
correctness flag is false. -/
theorem spqr_potential_ge_one (P : SPQR.Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] {AuthState : Type}
    (s : SPQR.GameState P AuthState) (hs : s.correct = false) :
    1 ≤ Braid.failurePotential s.toBraid := by
  simp [Braid.failurePotential, SPQR.GameState.toBraid, hs]

/-- The initial game states of secure-messaging's SPQR scheme satisfy the invariant of
`SPQR.correctness_error_le` and have potential zero. -/
theorem spqr_potential_init (P : SPQR.Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (sampleInitKey : ProbComp InitKey) :
    ∀ ik ∈ support (SPQR.scheme P auth sampleInitKey).initKeyGen,
      ∀ stA ∈ support ((SPQR.scheme P auth sampleInitKey).initA ik),
      ∀ stB ∈ support ((SPQR.scheme P auth sampleInitKey).initB ik),
        (Braid.CorrectnessInv auth ik (SPQR.GameState.toBraid (initGameState stA stB)) ∧
          SPQR.Ct1AckInv (initGameState stA stB)) ∧
        Braid.failurePotential (SPQR.GameState.toBraid (initGameState stA stB)) = 0 := by
  intro ik _ stA hA stB hB
  simp only [SPQR.scheme, mem_support_pure_iff] at hA hB
  subst hA hB
  refine ⟨⟨Or.inr ⟨_, Braid.transcriptConsistent_initGameState (P := P.toBraid) auth ik⟩,
    ?_⟩, ?_⟩
  · intro party n msg tsnd h
    cases party <;> simp [SCKAScheme.initGameState, SPQR.GameState.messagesAt] at h
  · change Braid.failurePotential
      (SCKAScheme.initGameState (Braid.initA P.toBraid auth ik)
        (Braid.initB P.toBraid auth ik)) = 0
    simp [Braid.failurePotential, Braid.currentEpochFailure,
      Braid.pairFailure, SCKAScheme.initGameState, Braid.initA, Braid.initB,
      Braid.State.controlPosition, Braid.State.epoch]

/-- Let `S₁` be an SCKA scheme with the epoch keys of secure-messaging's SPQR scheme, related to
that scheme through `TransferObligations` with the invariant of `SPQR.correctness_error_le`. With
sound stream decoders, every adversary against `S₁` making at most `q` send queries causes a false
correctness flag with probability at most `q` times the KEM correctness error. -/
theorem spqr_correctness_error_le_of_transfer
    (P : SPQR.Parameters ProbComp) [DecidableEq P.K] [DecidableEq P.EpochKey]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.det.PKheader (P.det.C₁ × P.det.C₂) P.Mac)
    (sampleInitKey : ProbComp InitKey)
    (hHdrSound : P.decHdr.Sound P.ecpHdr)
    (hEkSound : P.decEk.Sound P.ecpEk)
    (hCt1Sound : P.decCt1.Sound P.ecpCt1)
    (hCt2Sound : P.decCt2.Sound P.ecpCt2)
    {IK₁ StA₁ StB₁ Rho₁ Rand₁ : Type}
    (S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ P.EpochKey Rho₁ Rand₁)
    (RA : StA₁ → SPQR.Chunked.PartyState P AuthState → Prop)
    (RB : StB₁ → SPQR.Chunked.PartyState P AuthState → Prop)
    (RM : Rho₁ → SPQR.Chunked.Message P.Sym → Prop)
    (hob : TransferObligations S₁ (SPQR.scheme P auth sampleInitKey)
      (fun ik s => Braid.CorrectnessInv auth ik (SPQR.GameState.toBraid s) ∧
        SPQR.Ct1AckInv s) RA RB RM)
    (adv : SCKACorrectnessAdversary Rho₁) (q : ℕ) (hq : SendQueryBound adv q) :
    1 - Pr{let x ← correctnessExp S₁ adv}[x = true] ≤
      (q : ℝ≥0∞) * P.det.toKEM.correctnessError ProbCompRuntime.probComp := by
  refine correctness_error_le_of_transfer S₁ (SPQR.scheme P auth sampleInitKey) _
    (fun s => Braid.failurePotential (SPQR.GameState.toBraid s)) _
    (spqr_potential_ge_one P) (spqr_potential_init P auth sampleInitKey)
    (SPQR.correctnessImpl_preserves_correctnessInv auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound)
    (fun ik t s hs => SPQR.wp_failurePotential_query_le auth sampleInitKey
      hHdrSound hEkSound hCt1Sound hCt2Sound ik t s hs.1 hs.2) RA RB RM hob adv q hq

end SpqrBridge
