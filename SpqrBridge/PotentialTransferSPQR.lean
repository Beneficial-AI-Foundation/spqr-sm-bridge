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
theorem spqr_potential_ge_one (P : MLKEMBraid.Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] {AuthState : Type}
    (s : SCKAScheme.GameState (SPQR.Chunked.PartyState P AuthState)
      (SPQR.Chunked.PartyState P AuthState) P.EpochKey (SPQR.Chunked.Message P.Sym))
    (hs : s.correct = false) :
    1 ≤ MLKEMBraid.failurePotential (SPQR.GameState.toMLKEMBraid s) := by
  simp [MLKEMBraid.failurePotential, SPQR.GameState.toMLKEMBraid, hs]

/-- The initial game states of secure-messaging's SPQR scheme satisfy the invariant of
`SPQR.correctness_error_le` and have potential zero. -/
theorem spqr_potential_init (P : MLKEMBraid.Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc) (sampleInitKey : ProbComp InitKey) :
    ∀ ik ∈ support (SPQR.scheme P auth irl sampleInitKey).initKeyGen,
      ∀ stA ∈ support ((SPQR.scheme P auth irl sampleInitKey).initA ik),
      ∀ stB ∈ support ((SPQR.scheme P auth irl sampleInitKey).initB ik),
        (MLKEMBraid.CorrectnessInv auth ik
            (SPQR.GameState.toMLKEMBraid (initGameState stA stB)) ∧
          SPQR.Ct1AckInv (initGameState stA stB)) ∧
        MLKEMBraid.failurePotential (SPQR.GameState.toMLKEMBraid (initGameState stA stB)) = 0 := by
  intro ik _ stA hA stB hB
  simp only [SPQR.scheme, mem_support_pure_iff] at hA hB
  subst hA hB
  refine ⟨⟨Or.inr ⟨_, MLKEMBraid.transcriptConsistent_initGameState auth ik⟩, ?_⟩, ?_⟩
  · intro party n msg tsnd h
    cases party <;> simp [SCKAScheme.initGameState] at h
  · change MLKEMBraid.failurePotential
      (SCKAScheme.initGameState (MLKEMBraid.initA P auth ik) (MLKEMBraid.initB P auth ik)) = 0
    simp [MLKEMBraid.failurePotential, MLKEMBraid.currentEpochFailure,
      MLKEMBraid.pairFailure, SCKAScheme.initGameState, MLKEMBraid.initA, MLKEMBraid.initB,
      MLKEMBraid.State.controlPosition, MLKEMBraid.State.epoch]

/-- Let `S₁` be an SCKA scheme with the epoch keys of secure-messaging's SPQR scheme, related to
that scheme through `TransferObligations` with the invariant of `SPQR.correctness_error_le`. With
lawful stream decoders, every adversary against `S₁` making at most `q` send queries causes a false
correctness flag with probability at most `q` times the KEM correctness error. -/
theorem spqr_correctness_error_le_of_transfer
    (P : MLKEMBraid.Parameters ProbComp) [DecidableEq P.K]
    [DecidableEq P.EpochKey] [DecidableEq P.Sym]
    {InitKey AuthState : Type}
    (auth : RatchetedAuthenticator InitKey P.EpochKey AuthState
      P.inc.PKheader (P.inc.C₁ × P.inc.C₂) P.Mac)
    (irl : P.kem.IncrementalRandLeak P.inc)
    (sampleInitKey : ProbComp InitKey)
    (hHdrLawful : P.decHdr.Lawful P.ecpHdr)
    (hEkLawful : P.decEk.Lawful P.ecpEk)
    (hCt1Lawful : P.decCt1.Lawful P.ecpCt1)
    (hCt2Lawful : P.decCt2.Lawful P.ecpCt2)
    {IK₁ StA₁ StB₁ Rho₁ Rand₁ : Type}
    (S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ P.EpochKey Rho₁ Rand₁)
    (RA : StA₁ → SPQR.Chunked.PartyState P AuthState → Prop)
    (RB : StB₁ → SPQR.Chunked.PartyState P AuthState → Prop)
    (RM : Rho₁ → SPQR.Chunked.Message P.Sym → Prop)
    (hob : TransferObligations S₁ (SPQR.scheme P auth irl sampleInitKey)
      (fun ik s => MLKEMBraid.CorrectnessInv auth ik (SPQR.GameState.toMLKEMBraid s) ∧
        SPQR.Ct1AckInv s) RA RB RM)
    (adv : SCKACorrectnessAdversary Rho₁) (q : ℕ) (hq : SendQueryBound adv q) :
    1 - Pr{let x ← correctnessExp S₁ adv}[x = true] ≤
      (q : ℝ≥0∞) * P.kem.correctnessError ProbCompRuntime.probComp := by
  refine correctness_error_le_of_transfer S₁ (SPQR.scheme P auth irl sampleInitKey) _
    (fun s => MLKEMBraid.failurePotential (SPQR.GameState.toMLKEMBraid s)) _
    (spqr_potential_ge_one P) (spqr_potential_init P auth irl sampleInitKey)
    (SPQR.correctnessImpl_preserves_correctnessInv auth irl sampleInitKey
      hHdrLawful hEkLawful hCt1Lawful hCt2Lawful)
    (fun ik t s hs => SPQR.wp_failurePotential_query_le auth irl sampleInitKey
      hHdrLawful hEkLawful hCt1Lawful hCt2Lawful ik t s hs.1 hs.2) RA RB RM hob adv q hq

end SpqrBridge
