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

namespace SpqrBridge
open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states

/-- A computation's result without its RNG. -/
def dropRng {α R : Type} (x : Result (α × R)) : Result α := Std.bind x fun p => ok p.1

theorem dropRng_eq_ok {α R : Type} (x : Result (α × R)) (a : α) :
    dropRng x = ok a ↔ ∃ r, x = ok (a, r) := by
  simp only [dropRng, Result.bind_eq_ok, Result.ok.injEq]
  constructor
  · rintro ⟨⟨a', r⟩, hx, h⟩; exact ⟨r, h ▸ hx⟩
  · rintro ⟨r, hx⟩; exact ⟨(a, r), hx, rfl⟩

theorem uncurry_bind {α β γ δ : Type} (f : α → β → Result γ) (k : γ → Result δ) (q : α × β) :
    Std.bind (uncurry f q) k = uncurry (fun a b => Std.bind (f a b) k) q := by
  obtain ⟨a, b⟩ := q
  simp only [uncurry_apply_pair]

theorem codeSend_eq_some_iff (s : States) (t : List Std.U8) (out : v1.chunked.states.Send) :
    codeSend s t = some out ↔ ∃ r, States.send tapeRng tapeCrypto s t = ok (.Ok out, r) := by
  unfold codeSend
  generalize States.send tapeRng tapeCrypto s t = x
  cases x with
  | ret v =>
    obtain ⟨o, r⟩ := v
    cases o with
    | Ok o =>
      simp only [Result.match.ok, Option.some.injEq, Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq, exists_and_left, exists_eq', and_true]
    | Err e =>
      simp only [Result.match.ok, Result.ok.injEq, Prod.mk.injEq, reduceCtorEq, false_and,
        exists_false]
  | vis i k =>
    simp only [Result.match.vis, reduceCtorEq, false_iff, not_exists]
    exact fun _ h => vis_not_ok h
  | div =>
    simp only [Result.match.div, reduceCtorEq, false_iff, not_exists]
    exact fun _ h => div_not_ok h

/-- `codeSend` depends only on the result of `send` without its RNG. -/
theorem codeSend_congr (s s' : States) (t t' : List Std.U8)
    (h : dropRng (States.send tapeRng tapeCrypto s t) =
      dropRng (States.send tapeRng tapeCrypto s' t')) :
    codeSend s t = codeSend s' t' := by
  apply Option.ext
  intro out
  rw [codeSend_eq_some_iff, codeSend_eq_some_iff, ← dropRng_eq_ok, ← dropRng_eq_ok, h]

/-- A `send` from a state other than `KeysUnsampled` and `HeaderReceived` does not read the
tape: without its RNG, its result is the same for every tape. -/
theorem dropRng_send_irrel (s : States) (h1 : ∀ st, s ≠ .KeysUnsampled st)
    (h2 : ∀ st, s ≠ .HeaderReceived st) (t t' : List Std.U8) :
    dropRng (States.send tapeRng tapeCrypto s t) =
      dropRng (States.send tapeRng tapeCrypto s t') := by
  cases s with
  | KeysUnsampled st => exact absurd rfl (h1 st)
  | HeaderReceived st => exact absurd rfl (h2 st)
  | _ => simp only [dropRng, States.send, Std.bind_assoc, uncurry_bind, bind_ok]

end SpqrBridge
