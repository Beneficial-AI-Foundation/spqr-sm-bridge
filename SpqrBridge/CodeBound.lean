/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.BudgetedPotential
import SpqrBridge.CodeParams
import SpqrBridge.EpochBound
import SpqrBridge.PolyEncoderChunk
import SpqrBridge.PotentialTransferSPQR
import SpqrBridge.GameInvSteps

/-!
# The invariant, the transfer statement and the assumptions

This file states the pieces from which `code_correctness_error_le` is proved:

* `CodeGameInv`: the code game state is reachable, its recorded messages are the messages of
  that run, and its send counters count the successful sends.
* `BudgetedTransferObligations` and `correctness_error_le_of_budgeted_transfer`: the transfer of
  `correctness_error_le_of_transfer` (`PotentialTransfer.lean`), with a code-side invariant and a
  send budget.
* `BridgeObligations`: the facts about the code that the theorem assumes. Each field names the
  issue of SparsePostQuantumRatchet-verify that proves it.

The conditional code-level bound `code_correctness_error_le` is in `SpqrBridge.CodeCorrectness`,
because its proof uses the files that import this one.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open SCKAScheme

/-! ## The code-side game invariant -/

/-- `s` is the state of one party in a reachable run of the code, with `n` successful sends. -/
def ReachParty (s : States) (n : ℕ) : Prop :=
  ∃ sA sB mA mB, CodeReach sA sB mA mB n ∧ (s = sA ∨ s = sB)

/-- The recorded messages of one party: entry `k + 1` of the transit array is message `k` of the
run, for `k` below the send count, and every other entry is empty. -/
def RecordedAs (msg : ℕ → Option (Message × ℕ)) (count : ℕ) (ms : List Message) : Prop :=
  count = ms.length ∧ msg 0 = none ∧ ∀ k, (msg (k + 1)).map Prod.fst = ms[k]?

/-- The code game state is a reachable run: its party states, recorded messages and send
counters are those of one `CodeReach` run. -/
def CodeGameInv (s : GameState States States (B 32) Message) : Prop :=
  ∃ mA mB, CodeReach s.stA s.stB mA mB (s.nA + s.nB) ∧
    RecordedAs s.msgA s.nA mA ∧ RecordedAs s.msgB s.nB mB

/-! ## The budgeted transfer -/

section Budgeted

variable {IK₁ StA₁ StB₁ Rho₁ Rand₁ IK₂ StA₂ StB₂ Rho₂ Rand₂ I : Type} [DecidableEq I]

/-- The obligations of `TransferObligations`, with a code-side invariant `Inv₁` and a send
budget `Bud`. A
send query needs the step obligation only below the budget. A receive query needs it up to the
budget, which covers the deliveries after the last send. -/
structure BudgetedTransferObligations
    (S₁ : SCKAScheme ProbComp IK₁ StA₁ StB₁ I Rho₁ Rand₁)
    (S₂ : SCKAScheme ProbComp IK₂ StA₂ StB₂ I Rho₂ Rand₂)
    (Inv₂ : IK₂ → GameState StA₂ StB₂ I Rho₂ → Prop)
    (Inv₁ : GameState StA₁ StB₁ I Rho₁ → Prop)
    (RA : StA₁ → StA₂ → Prop) (RB : StB₁ → StB₂ → Prop) (RM : Rho₁ → Rho₂ → Prop)
    (Bud : ℕ) : Prop where
  init : ∀ ik₁ ∈ support S₁.initKeyGen, ∀ stA₁ ∈ support (S₁.initA ik₁),
    ∀ stB₁ ∈ support (S₁.initB ik₁),
      Inv₁ (initGameState stA₁ stB₁) ∧
      ∃ ik₂ ∈ support S₂.initKeyGen, ∃ stA₂ ∈ support (S₂.initA ik₂),
        ∃ stB₂ ∈ support (S₂.initB ik₂), RA stA₁ stA₂ ∧ RB stB₁ stB₂
  pres : QueryImpl.PreservesInv (sckaCorrectnessImpl S₁) Inv₁
  sendA : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂),
    s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB < Bud → GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
      RelTriple (S₁.sendA s₁.stA) (S₂.sendA s₂.stA) (SendRel RA RM)
  sendB : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂),
    s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB < Bud → GameRel RA RB RM s₁ s₂ → Inv₂ ik₂ s₂ →
      RelTriple (S₁.sendB s₁.stB) (S₂.sendB s₂.stB) (SendRel RB RM)
  recvA : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
    (n tsnd : ℕ) (ρ₁ : Rho₁) (ρ₂ : Rho₂),
    s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB ≤ Bud → GameRel RA RB RM s₁ s₂ →
      Inv₂ ik₂ s₂ → s₁.msgB n = some (ρ₁, tsnd) → s₂.msgB n = some (ρ₂, tsnd) → RM ρ₁ ρ₂ →
        RecvRel RA (S₁.recvA s₁.stA ρ₁) (S₂.recvA s₂.stA ρ₂)
  recvB : ∀ ik₂ (s₁ : GameState StA₁ StB₁ I Rho₁) (s₂ : GameState StA₂ StB₂ I Rho₂)
    (n tsnd : ℕ) (ρ₁ : Rho₁) (ρ₂ : Rho₂),
    s₁.correct = true → Inv₁ s₁ → s₁.nA + s₁.nB ≤ Bud → GameRel RA RB RM s₁ s₂ →
      Inv₂ ik₂ s₂ → s₁.msgA n = some (ρ₁, tsnd) → s₂.msgA n = some (ρ₂, tsnd) → RM ρ₁ ρ₂ →
        RecvRel RB (S₁.recvB s₁.stB ρ₁) (S₂.recvB s₂.stB ρ₂)

/-- Let `S₂` meet the premises of `correctness_error_le_of_potential` with invariant `Inv₂`,
potential `V₂` and error `ε`. Let `S₁` meet the budgeted obligations against `S₂` with budget
`Bud`. Then every adversary against `S₁` with at most `q < Bud` sends breaks correctness with
probability at most `q · ε`. -/
theorem correctness_error_le_of_budgeted_transfer
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
    (hobl : BudgetedTransferObligations S₁ S₂ Inv₂ Inv₁ RA RB RM Bud)
    (adv : SCKACorrectnessAdversary Rho₁) (q : ℕ) (hq : SendQueryBound adv q) (hqB : q < Bud) :
    1 - Pr{let x ← correctnessExp S₁ adv}[x = true] ≤ q * ε :=
  correctness_error_le_of_budgeted_steps S₁ S₂ Inv₂ V₂ ε hV₂ hinit₂ hpres₂ hstep₂ Inv₁ RA RB RM
    Bud hobl.init hobl.pres hobl.sendA hobl.sendB hobl.recvA hobl.recvB adv q hq hqB

end Budgeted

/-! ## The allowed assumptions -/

/-- The bytes of randomness that a `Braid` send step reads: 64 for key generation, 32 for
`Encaps1`, and none otherwise. -/
def seedLen : State encoding.polynomial.PolyEncoder encoding.polynomial.PolyDecoder → ℕ
  | .keysUnsampled .. => 64
  | .headerReceived .. => 32
  | _ => 0

/-- The facts about the code that `code_correctness_error_le` assumes. Each field names the issue
of SparsePostQuantumRatchet-verify that proves it. The bridge's own facts are theorems: `codeSend_key_length`, `codeRecv_key_length`
(`SpqrBridge.KeyLength`) and `next_chunk_wrap` (`SpqrBridge.NextChunkWrap`). -/
structure BridgeObligations : Prop where
  /-- Imported fact, #786. -/
  mlkem_sizes : MlkemSizes
  /-- Open upstream, #785 statement 1: `send` succeeds on a reachable state below the epoch
  limit, with a 64-byte tape. -/
  send_total : ∀ (s : States) (n : ℕ) (tape : List Std.U8), ReachParty s n →
    s.epochOf.val + 1 < 2 ^ 64 → 64 ≤ tape.length →
      ∃ out, codeSend s tape = some out
  /-- Open upstream, #785 statement 2: where the machine accepts, `recv` returns `Ok` with a
  related state and the same key. -/
  recv_complete : ∀ (s : States) (n : ℕ) (σ σ' : Braid.State encoding.polynomial.PolyEncoder
      encoding.polynomial.PolyDecoder) (msg : Message) (k : Option Key),
    ReachParty s n → Refines s σ → msg.epoch.val + 1 < 2 ^ 64 →
      Braid.receive codePrims σ (absMsg msg) = some (σ', k) →
        ∃ out, codeRecv s msg = some out ∧ Refines out.state σ' ∧ out.key.map absKey = k
  /-- Open upstream, #787 statement 5: the machine's randomness is the tape prefix that the
  code read. -/
  send_refines_tape : ∀ (s : States) (σ : Braid.State encoding.polynomial.PolyEncoder
      encoding.polynomial.PolyDecoder) (tape : List Std.U8) (out : v1.chunked.states.Send),
    Refines s σ → codeSend s tape = some out →
      Refines out.state (Braid.send codePrims σ (tape.take (seedLen σ))).1 ∧
        absMsg out.msg = (Braid.send codePrims σ (tape.take (seedLen σ))).2.1 ∧
        out.key.map absKey = (Braid.send codePrims σ (tape.take (seedLen σ))).2.2

end SpqrBridge
