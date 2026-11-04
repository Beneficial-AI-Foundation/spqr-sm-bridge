/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.ChunkedSendAll

/-!
# The conditional code-level bound

`code_correctness_error_le` applies the budgeted transfer (`correctness_error_le_of_budgeted_transfer`)
with `S₁` the code's scheme and `S₂` secure-messaging's SPQR scheme over `codeParams`:

* `S₂` meets the premises of the potential argument with the invariant and potential of
  `SPQR.correctness_error_le`, as in `spqr_correctness_error_le_of_transfer`. Its decoders are
  lawful by `L2.polyStreamDecoder_lawful`.
* The code-side invariant is `CodeGameInv`, with budget `2^64 - 2`. Below it, the invariant gives
  the reachability and epoch headroom that `send_chunked` and `receive_chunked` need.
* Both parties use the relation `RA`, and messages use `RM`.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open SCKAScheme

/-- The invariant of `SPQR.correctness_error_le` over `codeParams`. -/
abbrev smInv (ik : InitKey) (s : GameState SMState SMState (B 32) (SPQR.Chunked.Message L2.Sym)) :
    Prop :=
  MLKEMBraid.CorrectnessInv codeAuth ik (SPQR.GameState.toMLKEMBraid s) ∧ SPQR.Ct1AckInv s

/-- A party of a game state with `CodeGameInv` is reachable with the game's send count. -/
theorem reachParty_of_codeGameInv {s : GameState States States (B 32) Message}
    (h : CodeGameInv s) : ReachParty s.stA (s.nA + s.nB) ∧ ReachParty s.stB (s.nA + s.nB) := by
  obtain ⟨mA, mB, hr, -, -⟩ := h
  exact ⟨⟨_, _, mA, mB, hr, Or.inl rfl⟩, ⟨_, _, mA, mB, hr, Or.inr rfl⟩⟩

/-- The code meets the budgeted obligations against secure-messaging's SPQR scheme, with budget
`2^64 - 2`. -/
theorem codeBudgetedObligations (hB : BridgeObligations) (sampleInitKey : ProbComp InitKey) :
    BudgetedTransferObligations (codeScheme sampleInitKey) (smScheme sampleInitKey) smInv
      CodeGameInv RA RA RM (2 ^ 64 - 2) where
  init ik hik stA hA stB hB' := by
    simp only [codeScheme, mem_support_pure_iff] at hA hB'
    subst hA hB'
    exact ⟨codeGameInv_init ik, ik, hik, _, (mem_support_pure_iff _ _).mpr rfl, _,
      (mem_support_pure_iff _ _).mpr rfl, ra_initA ik, ra_initB ik⟩
  pres := codeGameInv_pres sampleInitKey
  sendA _ s₁ s₂ _ hinv hbud hrel _ := by
    have he := (codeGameInv_epochs s₁ hinv).1
    exact send_chunked hB sampleInitKey s₁.stA _ s₂.stA (reachParty_of_codeGameInv hinv).1
      (by omega) hrel.stA
  sendB _ s₁ s₂ _ hinv hbud hrel _ := by
    have he := (codeGameInv_epochs s₁ hinv).2.1
    exact send_chunked hB sampleInitKey s₁.stB _ s₂.stB (reachParty_of_codeGameInv hinv).2
      (by omega) hrel.stB
  recvA _ s₁ s₂ n tsnd ρ₁ ρ₂ _ hinv hbud hrel _ h₁ _ hρ := by
    have he := (codeGameInv_epochs s₁ hinv).2.2 n ρ₁ tsnd (Or.inr h₁)
    exact receive_chunked hB s₁.stA _ s₂.stA ρ₁ ρ₂ (reachParty_of_codeGameInv hinv).1
      (by omega) hrel.stA hρ
  recvB _ s₁ s₂ n tsnd ρ₁ ρ₂ _ hinv hbud hrel _ h₁ _ hρ := by
    have he := (codeGameInv_epochs s₁ hinv).2.2 n ρ₁ tsnd (Or.inl h₁)
    exact receive_chunked hB s₁.stB _ s₂.stB ρ₁ ρ₂ (reachParty_of_codeGameInv hinv).2
      (by omega) hrel.stB hρ

/-- Assume the allowed assumptions. Let `sampleInitKey` sample initial keys that the code
accepts. Then every SCKA correctness adversary with at most `q` sends, across both parties,
breaks some correctness assert on the code's chunked `States` machine with probability at most
`q` times the correctness error of the code's KEM. The premise `BridgeObligations` is what makes
this conditional: its fields go away once #782 is done. -/
theorem code_correctness_error_le (hB : BridgeObligations) (sampleInitKey : ProbComp InitKey)
    (adv : SCKACorrectnessAdversary Message) (q : ℕ)
    (hq : SendQueryBound adv q) (hq64 : q + 2 < 2 ^ 64) :
    1 - Pr{let x ← correctnessExp (codeScheme sampleInitKey) adv}[x = true] ≤
      (q : ℝ≥0∞) * codeKem.correctnessError ProbCompRuntime.probComp := by
  have hHdr := L2.polyStreamDecoder_lawful 3 (by decide) (by decide) hdrCodec
  have hEk := L2.polyStreamDecoder_lawful 36 (by decide) (by decide) ekCodec
  have hCt1 := L2.polyStreamDecoder_lawful 30 (by decide) (by decide) ct1Codec
  have hCt2 := L2.polyStreamDecoder_lawful 5 (by decide) (by decide) ct2Codec
  refine correctness_error_le_of_budgeted_transfer (codeScheme sampleInitKey)
    (smScheme sampleInitKey) smInv
    (fun s => MLKEMBraid.failurePotential (SPQR.GameState.toMLKEMBraid s)) _
    (spqr_potential_ge_one codeParams) (spqr_potential_init codeParams codeAuth codeIrl sampleInitKey)
    (SPQR.correctnessImpl_preserves_correctnessInv (P := codeParams) codeAuth codeIrl
      sampleInitKey hHdr hEk hCt1 hCt2)
    (fun ik t s hs => SPQR.wp_failurePotential_query_le (P := codeParams) codeAuth codeIrl
      sampleInitKey hHdr hEk hCt1 hCt2 ik t s hs.1 hs.2)
    CodeGameInv RA RA RM (2 ^ 64 - 2) (codeBudgetedObligations hB sampleInitKey) adv q hq
    (by omega)

end SpqrBridge
