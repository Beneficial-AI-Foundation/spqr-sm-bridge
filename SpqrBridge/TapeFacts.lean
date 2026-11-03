/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.Adapter
import VCVio.ProgramLogic.Relational.Basic

/-!
# Facts about the tape of a send

`relTriple_bind_pure_right`: a sampled computation whose every outcome is related to `b` couples
with `pure b`.
-/

namespace SpqrBridge

open OracleSpec OracleComp
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational

/-- If `R (f t) b` holds for every `t`, then sampling `t` and returning `f t` couples with
`pure b` on `R`. -/
theorem relTriple_bind_pure_right {γ α β : Type} (oa : ProbComp γ) (f : γ → α) (b : β)
    (R : α → β → Prop) (h : ∀ t, R (f t) b) :
    RelTriple (do let t ← oa; pure (f t)) (pure b : ProbComp β) R := by
  refine relTriple_post_mono (relTriple_prod (P := fun a => R a b) (Q := fun y => y = b) ?_ ?_)
    (fun _ _ ⟨hp, hq⟩ => hq ▸ hp)
  · intro a ha
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at ha
    obtain ⟨t, -, ht⟩ := ha
    rw [ht]
    exact h t
  · intro y hy
    simpa only [support_pure, Set.mem_singleton_iff] using hy

end SpqrBridge
