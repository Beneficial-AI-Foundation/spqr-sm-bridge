/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.SendFacts

/-!
# The send program is the extracted code

`sendProg s` (`SpqrBridge.Adapter`) is one `OracleComp` program for a send. Its only oracle is
`fill_bytes`: a buffer goes in and the filled buffer comes out. The games interpret the oracle
with uniform bytes (`unifImpl`).

`send_eq_prog` shows that the extracted `States.send` is equal to `runProg i₁ (sendResult s) rng`.
This is the second component of the same program, interpreted with the `fill_bytes` of any RNG of
any type `R` (`fillImpl`). The proof uses no property of
`fill_bytes`.

`send_eq_rest` splits the extracted `send` into the sampling `sendBuf s` and `sendRest`. Its
consequences are conditional on the sampling:

* `sample_ok_of_send_ok`: if the extracted `send` returns `ok`, the sampling returned `ok`. So a
  failure of `fill_bytes` is a failure of `send`. `send_total` does not exclude it.
* `send_ok_of_codeSend`: if the sampling returns `ok (buf, rng')` and `codeSend s buf = some out`,
  the extracted `send` returns `ok (.Ok out, rng')`.

These statements do not give the length of `buf`. The premise `buf.length = sendLen s` of
`send_total` and `send_refines_bytes` is a separate assumption on the RNG.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states
open OracleSpec OracleComp

/-- `sendResult s` runs `sendProg s` and returns the second component of its value. -/
noncomputable def sendResult (s : States) :
    OracleComp fillSpec (Result (core.result.Result v1.chunked.states.Send spqr.Error)) := do
  let p ← sendProg s
  return p.2

/-- Let `i : rand_1.rng.Rng R`, `b : Slice Std.U8`, `f : Slice Std.U8 → Result α` and `rng : R`.
Let `prog` be the program that queries `b` and returns `f` of the answer. Then
`runProg i prog rng = Std.bind (i.rand_core_1RngCoreInst.fill_bytes rng b) g`, where
`g p = Std.bind (f p.2) (fun a => ok (a, p.1))`. -/
theorem runProg_query {R α : Type} (i : rand_1.rng.Rng R) (b : Slice Std.U8)
    (f : Slice Std.U8 → Result α) (rng : R) :
    runProg i (do
        let x ← (liftM (fillSpec.query b) : OracleComp fillSpec _)
        return f x) rng =
      Std.bind (i.rand_core_1RngCoreInst.fill_bytes rng b) fun p =>
        Std.bind (f p.2) fun a => ok (a, p.1) := by
  simp only [runProg, simulateQ_bind, simulateQ_spec_query, simulateQ_pure]
  show Std.bind (Std.bind (Std.bind (i.rand_core_1RngCoreInst.fill_bytes rng b)
      fun p => ok (p.2, p.1)) fun q => ok (f q.1, q.2)) (fun q => Std.bind q.1 fun a => ok (a, q.2)) = _
  simp only [Std.bind_assoc, bind_ok]

/-- Let `i : rand_1.rng.Rng R`, `r : Result α` and `rng : R`. Then
`runProg i (pure r) rng = Std.bind r (fun a => ok (a, rng))`. -/
theorem runProg_pure {R α : Type} (i : rand_1.rng.Rng R) (r : Result α) (rng : R) :
    runProg i (pure r) rng = Std.bind r fun a => ok (a, rng) := by
  simp only [runProg, simulateQ_pure, StateT.run_pure, pure_tc_eq, bind_ok]
  rfl

/-- Let `R` be a type, and let `i₁` and `i₂` be the RNG instances of `R`. Then, for every state
`s` and every `rng : R`, `States.send i₁ i₂ s rng = runProg i₁ (sendResult s) rng`. -/
theorem send_eq_prog {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (s : States) (rng : R) :
    States.send i₁ i₂ s rng = runProg i₁ (sendResult s) rng := by
  cases s with
  | KeysUnsampled st =>
    simp only [sendResult, sendProg, sendBuf, bind_assoc, pure_bind, runProg_query, sendRest,
      States.send, v1.chunked.send_ek.KeysUnsampled.send_hdr_chunk,
      v1.unchunked.send_ek.KeysUnsampled.send_header, incremental_mlkem768.generate, lift,
      Array.to_slice_mut, fixedRng, fixedCore, buf64, Std.bind_assoc, bind_ok, uncurry_eq,
      v1.chunked.send_ek.KeysUnsampled.epoch]
  | HeaderReceived st =>
    simp only [sendResult, sendProg, sendBuf, bind_assoc, pure_bind, runProg_query, sendRest,
      States.send, v1.chunked.send_ct.HeaderReceived.send_ct1_chunk,
      v1.unchunked.send_ct.HeaderReceived.send_ct1, incremental_mlkem768.encaps1, lift,
      Array.to_slice_mut, fixedRng, fixedCore, buf32, Std.bind_assoc, bind_ok, uncurry_eq,
      alloc.vec.Vec.deref_mut, v1.chunked.send_ct.HeaderReceived.epoch]
  | _ =>
    simp only [sendResult, sendProg, sendBuf, pure_bind, runProg_pure, sendRest, States.send,
      Std.bind_assoc, uncurry_bind, bind_ok]

/-- `States.send i₁ i₂ s rng` is equal to this computation: interpret `sendBuf s` with
`fillImpl i₁` from the state `rng`, and, on `ok (buf, rng')`, run `sendRest s buf` and pair its
value with `rng'`. If the interpretation does not return `ok`, neither does `States.send`. -/
theorem send_eq_rest {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (s : States) (rng : R) :
    States.send i₁ i₂ s rng =
      Std.bind ((simulateQ (fillImpl i₁) (sendBuf s)).run rng) fun p =>
        Std.bind (sendRest s p.1) fun a => ok (a, p.2) := by
  rw [send_eq_prog]
  simp only [sendResult, sendProg, runProg, bind_assoc, pure_bind, simulateQ_bind,
    simulateQ_pure, StateT.run_bind, StateT.run_pure]
  show Std.bind (Std.bind ((simulateQ (fillImpl i₁) (sendBuf s)).run rng)
      fun q => ok (sendRest s q.1, q.2)) (fun q => Std.bind q.1 fun a => ok (a, q.2)) = _
  simp only [Std.bind_assoc, bind_ok]

/-- Let `States.send i₁ i₂ s rng = ok x`. Then the interpretation of `sendBuf s` with
`fillImpl i₁` from the state `rng` returns `ok (buf, rng')` for some `buf` and `rng'`. -/
theorem sample_ok_of_send_ok {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (s : States) (rng : R)
    (x : core.result.Result v1.chunked.states.Send spqr.Error × R)
    (h : States.send i₁ i₂ s rng = ok x) :
    ∃ buf rng', (simulateQ (fillImpl i₁) (sendBuf s)).run rng = ok (buf, rng') := by
  rw [send_eq_rest] at h
  generalize (simulateQ (fillImpl i₁) (sendBuf s)).run rng = y at h
  cases y with
  | ret p => exact ⟨p.1, p.2, rfl⟩
  | vis i k => exact absurd h (by simp only [bind_vis]; exact vis_not_ok)
  | div => exact absurd h (by simp only [bind_div]; exact div_not_ok)

/-- Let the interpretation of `sendBuf s` with `fillImpl i₁` from the state `rng` return
`ok (buf, rng')`, and let `codeSend s buf = some out`. Then
`States.send i₁ i₂ s rng = ok (.Ok out, rng')`. -/
theorem send_ok_of_codeSend {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (s : States) (rng rng' : R) (buf : Slice Std.U8) (out : v1.chunked.states.Send)
    (hs : (simulateQ (fillImpl i₁) (sendBuf s)).run rng = ok (buf, rng'))
    (h : codeSend s buf = some out) :
    States.send i₁ i₂ s rng = ok (.Ok out, rng') := by
  obtain ⟨r, hr⟩ := (codeSend_eq_some_iff s buf out).mp h
  rw [send_eq_rest, hs, bind_ok]
  simp only [sendRest, hr, bind_ok]

end SpqrBridge
