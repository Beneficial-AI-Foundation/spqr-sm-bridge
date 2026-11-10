/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.Adapter

/-!
# Facts about `codeSend`

`codeSend_eq_some_iff` restates `codeSend s buf = some out` on the extracted `States.send`, run
with the RNG whose `fill_bytes` returns `buf`.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states

/-- Let `f : α → β → Result γ`, `k : γ → Result δ` and `q : α × β`. Then
`Std.bind (uncurry f q) k = uncurry (fun a b => Std.bind (f a b) k) q`. -/
theorem uncurry_bind {α β γ δ : Type} (f : α → β → Result γ) (k : γ → Result δ) (q : α × β) :
    Std.bind (uncurry f q) k = uncurry (fun a b => Std.bind (f a b) k) q := rfl

/-- Let `f : α → β → γ`. Then `uncurry f = fun q => f q.1 q.2`. -/
theorem uncurry_eq {α β γ : Type} (f : α → β → γ) : uncurry f = fun q => f q.1 q.2 := rfl

/-- `codeSend s buf = some out` if and only if
`States.send (fixedRng buf) (fixedCrypto buf) s () = ok (.Ok out, r)` for some `r`. -/
theorem codeSend_eq_some_iff (s : States) (buf : Slice Std.U8) (out : v1.chunked.states.Send) :
    codeSend s buf = some out ↔
      ∃ r, States.send (fixedRng buf) (fixedCrypto buf) s () = ok (.Ok out, r) := by
  unfold codeSend sendRest outOf
  generalize States.send (fixedRng buf) (fixedCrypto buf) s () = x
  cases x with
  | ret v =>
    obtain ⟨o, r⟩ := v
    cases o with
    | Ok o =>
      simp only [bind_ok, Result.match.ok, Option.some.injEq, Result.ok.injEq, Prod.mk.injEq,
        core.result.Result.Ok.injEq, and_true, exists_const]
    | Err e =>
      simp only [bind_ok, Result.match.ok, Result.ok.injEq, Prod.mk.injEq, reduceCtorEq,
        false_and, exists_false]
  | vis i k =>
    simp only [bind_vis, Result.match.vis, reduceCtorEq, false_iff, not_exists]
    exact fun _ h => vis_not_ok h
  | div =>
    simp only [bind_div, Result.match.div, reduceCtorEq, false_iff, not_exists]
    exact fun _ h => div_not_ok h

end SpqrBridge
