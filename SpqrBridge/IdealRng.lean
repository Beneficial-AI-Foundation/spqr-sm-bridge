/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.RngMonad
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.EvalDist.EvalDistEq

/-!
# The assumption on the generator, as a Lean statement

`IdealRng i seed n` is the assumption on the generator, ported from bridging-examples
(`BridgingExamples/ByteMask/Bridge.lean`, commit `a95e0a6`). It says: for every oracle program
`p` whose queries ask for at most `n` bytes in total (`ByteBound p n`), the two computations below
have the same distribution.

* Sample a state `rng` from `seed`, interpret `p` with the `fill_bytes` of `i` from `rng`
  (`runProg`), and drop the final state.
* Interpret `p` with `unifImpl`.

`send_bridge`: let `IdealRng i₁ seed 64`. Then `realSendA i₁ i₂ seed s`, which samples a state
from `seed` and runs the extracted `States.send` on it, has the distribution of `codeSendA s`.

`idealRng_tape`: the generator `tapeRng`, from a tape that `sampleB n` samples, meets
`IdealRng tapeRng (tapeSeed n) n`. So the hypothesis of `send_bridge` is not empty.

The statement is about one send from one sampled state. That each send of a run starts from a new
state, independent of the earlier sends, is a modeling assumption. Lean does not connect
`IdealRng` to `OsRng`.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states
open OracleSpec OracleComp

/-- `ByteBound p n` is `p.IsQueryBound n (fun s b => s.length ≤ b) (fun s b => b - s.length)`.
So, on every path of `p`, the sum of `s.length` over the queries `s` is at most `n`. -/
def ByteBound {α : Type} (p : OracleComp fillSpec α) (n : ℕ) : Prop :=
  p.IsQueryBound n (fun s b => s.length ≤ b) (fun s b => b - s.length)

/-- Let `i` be an RNG of type `R`, `seed` a distribution on `R`, and `n` a natural number.
`IdealRng i seed n` holds if, for every type `α` and every `p : OracleComp fillSpec (Result α)`
with `ByteBound p n`,
`(do let rng ← seed; pure (Prod.fst <$> runProg i p rng)) =ᵈ simulateQ unifImpl p`.

The state is sampled once and passed through all the queries of `p`. So the statement is about
the joint distribution of the answers to `p`. `p` has no access to the state. A failure of
`fill_bytes` within the budget, from a state in the support of `seed`, is an observable result,
and `unifImpl` never fails.

Remark, not proved in Lean. Let `n ≥ 1`, and let the support of `seed` have fewer than `256 ^ n`
elements. Then no `i` meets `IdealRng i seed n`. For `n ≤ Usize.max`, take the program that asks
for one buffer of `n` bytes and returns it. For a larger `n`, take `n` queries of one byte each.
Under `unifImpl`, each program has `256 ^ n` results. From `seed`, it has fewer. -/
def IdealRng {R : Type} (i : rand_1.rng.Rng R) (seed : ProbComp R) (n : ℕ) : Prop :=
  ∀ {α : Type} (p : OracleComp fillSpec (Result α)), ByteBound p n →
    (do let rng ← seed
        pure (Prod.fst <$> runProg i p rng)) =ᵈ
    simulateQ unifImpl p

/-- For every state `s`, `ByteBound (sendResult s) 64`. -/
theorem sendResult_byteBound (s : States) : ByteBound (sendResult s) 64 := by
  cases s <;> simp [ByteBound, sendResult, sendProg, sendBuf, buf64_length, buf32_length]

/-- `realSendA i₁ i₂ seed s` samples `rng` from `seed`, runs `States.send i₁ i₂ s rng`, drops the
final state, and returns `stepOf` of the result. -/
noncomputable def realSendA {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (seed : ProbComp R) (s : States) :
    ProbComp (Option (Option (ℕ × B 32) × Message × ℕ × States)) := do
  let rng ← seed
  pure (stepOf (Prod.fst <$> States.send i₁ i₂ s rng))

/-- For every state `s`,
`simulateQ unifImpl (sendResult s) = Prod.snd <$> simulateQ unifImpl (sendProg s)`. -/
theorem simulateQ_sendResult (s : States) :
    simulateQ unifImpl (sendResult s) = (·.2) <$> simulateQ unifImpl (sendProg s) := by
  simp [sendResult, map_eq_bind_pure_comp]

/-- Let `IdealRng i₁ seed 64`. Then, for every state `s`,
`realSendA i₁ i₂ seed s =ᵈ codeSendA s`. -/
theorem send_bridge {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (seed : ProbComp R) (h : IdealRng i₁ seed 64) (s : States) :
    realSendA i₁ i₂ seed s =ᵈ codeSendA s := by
  have hp := (h (sendResult s) (sendResult_byteBound s)).map stepOf
  rw [simulateQ_sendResult] at hp
  simpa [realSendA, codeSendA, send_eq_prog, map_eq_bind_pure_comp] using hp

/-! ## A generator that meets the assumption -/

/-- Let `α` and `γ` be types with `[SampleableType α]`, let `m ≤ n`, and let
`g : List α → ProbComp γ`. Then `(do let v ← $ᵗ (List.Vector α n); g v.val) =ᵈ
(do let a ← $ᵗ (List.Vector α m); let b ← $ᵗ (List.Vector α (n - m)); g (a.val ++ b.val))`. -/
theorem uniformVector_split {α γ : Type} [SampleableType α] :
    ∀ (m n : ℕ), m ≤ n → ∀ g : List α → ProbComp γ,
      (do let v ← $ᵗ (List.Vector α n); g v.val) =ᵈ
      (do let a ← $ᵗ (List.Vector α m)
          let b ← $ᵗ (List.Vector α (n - m))
          g (a.val ++ b.val)) := by
  intro m
  induction m with
  | zero =>
    intro n _ g
    have : (fun a : List.Vector α 0 => (do
        let b ← $ᵗ (List.Vector α (n - 0)); g (a.val ++ b.val))) =
        fun _ => (do let v ← $ᵗ (List.Vector α n); g v.val) := by
      funext a
      rw [List.Vector.eq_nil a]
      rfl
    rw [this]
    exact (OracleComp.EvalDistEq.bind_const _ _).symm
  | succ m ih =>
    intro n hn g
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_add_right]
    refine ((SampleableType.evalDistEq_uniformSample_vector_succ n).bind_left _).trans ?_
    refine EvalDistEq.trans ?_
      ((SampleableType.evalDistEq_uniformSample_vector_succ m).bind_left _).symm
    simp only [bind_assoc, pure_bind]
    refine EvalDistEq.bind_right _ fun x => ?_
    exact ih n (by omega) (fun l => g (x :: l))

/-- `listVectorOf v` is the element of `List.Vector (Fin 256) n` whose list is `v.toList`. -/
def listVectorOf {n : ℕ} (v : Vector (Fin 256) n) : List.Vector (Fin 256) n :=
  ⟨v.toList, by simp⟩

/-- For every `n`, `listVectorOf (n := n)` is bijective. -/
theorem listVectorOf_bijective (n : ℕ) : Function.Bijective (listVectorOf (n := n)) := by
  refine ⟨fun a b h => Vector.toList_inj.mp (congrArg Subtype.val h),
    fun w => ⟨⟨w.val.toArray, by simp [w.property]⟩, Subtype.ext (by simp [listVectorOf])⟩⟩

/-- Let `g : List Std.U8 → ProbComp γ`. Then `(do let t ← sampleB n; g t.1) =ᵈ
(do let v ← $ᵗ (List.Vector (Fin 256) n); g (v.val.map byteOfFin))`. -/
theorem sampleB_bind_eq {γ : Type} (n : ℕ) (g : List Std.U8 → ProbComp γ) :
    (do let t ← sampleB n; g t.1) =ᵈ
    (do let v ← $ᵗ (List.Vector (Fin 256) n); g (v.val.map byteOfFin)) := by
  have h := (SampleableType.map_uniformSample_evalDistEq_of_bijective
    (listVectorOf_bijective n)).bind_left (fun v => g (v.val.map byteOfFin))
  convert h using 1
  simp only [sampleB, bind_assoc, pure_bind, map_eq_bind_pure_comp, Function.comp]
  rfl

/-- Let `m ≤ n`, and let `g : List Std.U8 → ProbComp γ`. Then
`(do let t ← sampleB n; g t.1) =ᵈ
(do let a ← sampleB m; let b ← sampleB (n - m); g (a.1 ++ b.1))`. -/
theorem sampleB_split {γ : Type} (m n : ℕ) (hmn : m ≤ n) (g : List Std.U8 → ProbComp γ) :
    (do let t ← sampleB n; g t.1) =ᵈ
    (do let a ← sampleB m
        let b ← sampleB (n - m)
        g (a.1 ++ b.1)) := by
  let G : List Std.U8 → ProbComp γ := fun la => do let b ← sampleB (n - m); g (la ++ b.1)
  have hR : (do let a ← sampleB m; G a.1) =ᵈ
      (do let va ← $ᵗ (List.Vector (Fin 256) m)
          let vb ← $ᵗ (List.Vector (Fin 256) (n - m))
          g (va.val.map byteOfFin ++ vb.val.map byteOfFin)) :=
    (sampleB_bind_eq m G).trans
      (EvalDistEq.bind_right _ fun va =>
        sampleB_bind_eq (n - m) (fun lb => g (va.val.map byteOfFin ++ lb)))
  refine (sampleB_bind_eq n g).trans ?_
  refine (uniformVector_split m n hmn (fun l => g (l.map byteOfFin))).trans ?_
  refine EvalDistEq.trans ?_ hR.symm
  simp only [List.map_append]
  exact EvalDistEq.rfl

/-- `tapePrefix s tape` is the slice with contents `tape.take s.length`. -/
def tapePrefix (s : Slice Std.U8) (tape : List Std.U8) : Slice Std.U8 :=
  Slice.from (tape.take s.length) (le_trans (List.length_take_le _ _) s.property)

/-- `tapeCore` is the RNG core on `List Std.U8` with these functions. If
`s.length ≤ tape.length`, then `fill_bytes tape s = ok (tape.drop s.length, tapePrefix s tape)`.
Otherwise, `fill_bytes tape s = fail .panic`. `next_u32` and `next_u64` return `fail .panic`. -/
def tapeCore : rand_core_1.RngCore (List Std.U8) where
  next_u32 _ := fail .panic
  next_u64 _ := fail .panic
  fill_bytes tape s :=
    if s.length ≤ tape.length then ok (tape.drop s.length, tapePrefix s tape) else fail .panic

/-- `tapeRng` is the `rand_1.rng.Rng (List Std.U8)` instance `⟨tapeCore⟩`. -/
def tapeRng : rand_1.rng.Rng (List Std.U8) := ⟨tapeCore⟩

/-- `tapeSeed n` is `(fun t => t.1) <$> sampleB n`. -/
def tapeSeed (n : ℕ) : ProbComp (List Std.U8) := (fun t => t.1) <$> sampleB n

/-- Let `s.length ≤ tape.length`. Then the query `s` followed by `k`, interpreted with
`fillImpl tapeRng` from `tape`, is `k (tapePrefix s tape)` interpreted from
`tape.drop s.length`. -/
theorem run_tape_query_bind {β : Type} (s : Slice Std.U8) (k : Slice Std.U8 → OracleComp fillSpec β)
    (tape : List Std.U8) (h : s.length ≤ tape.length) :
    (simulateQ (fillImpl tapeRng) ((liftM (fillSpec.query s) : OracleComp fillSpec _) >>= k)).run
        tape =
      (simulateQ (fillImpl tapeRng) (k (tapePrefix s tape))).run (tape.drop s.length) := by
  have hq : (fillImpl tapeRng s).run tape = ok (tapePrefix s tape, tape.drop s.length) := by
    simp only [fillImpl, tapeRng, tapeCore, StateT.run, h, ↓reduceIte]
    exact bind_ok _ _
  simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, hq]
  exact bind_ok _ _

/-- Let `ByteBound p n`. Then
`(do let t ← sampleB n; pure (Prod.fst <$> (simulateQ (fillImpl tapeRng) p).run t.1)) =ᵈ
(ok <$> simulateQ unifImpl p)`. -/
theorem tape_sim {β : Type} (p : OracleComp fillSpec β) :
    ∀ n, ByteBound p n →
      (do let t ← sampleB n
          pure (Prod.fst <$> (simulateQ (fillImpl tapeRng) p).run t.1)) =ᵈ
      (ok <$> simulateQ unifImpl p) := by
  induction p using OracleComp.inductionOn with
  | pure x =>
    intro n _
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    exact OracleComp.EvalDistEq.bind_const _ _
  | query_bind s k ih =>
    intro n hb
    rw [ByteBound, isQueryBound_query_bind_iff] at hb
    obtain ⟨hs, hk⟩ := hb
    have e : ∀ t : B n,
        Prod.fst <$> (simulateQ (fillImpl tapeRng)
            ((liftM (fillSpec.query s) : OracleComp fillSpec _) >>= k)).run t.1 =
          Prod.fst <$> (simulateQ (fillImpl tapeRng) (k (tapePrefix s t.1))).run
            (t.1.drop s.length) := fun t =>
      congrArg _ (run_tape_query_bind s k t.1 (by rw [t.2]; exact hs))
    simp only [e]
    refine (sampleB_split s.length n hs (fun l => pure (Prod.fst <$>
      (simulateQ (fillImpl tapeRng) (k (tapePrefix s l))).run (l.drop s.length)))).trans ?_
    have e2 : ∀ (a : B s.length) (b : List Std.U8),
        tapePrefix s (a.1 ++ b) = sliceOf a s.property ∧ (a.1 ++ b).drop s.length = b := by
      intro a b
      refine ⟨(Slice.eq_iff _ _).mpr ?_, List.drop_left' a.2⟩
      rw [tapePrefix, Slice.from_val, sliceOf_val]
      exact List.take_left' a.2
    simp only [e2, simulateQ_bind, simulateQ_spec_query, unifImpl, bind_assoc, pure_bind,
      map_bind]
    exact EvalDistEq.bind_right _ fun a => ih _ _ (hk _)

/-- Let `i : rand_1.rng.Rng R`, `p : OracleComp fillSpec (Result α)` and `rng : R`. Then
`Prod.fst <$> runProg i p rng = (Prod.fst <$> (simulateQ (fillImpl i) p).run rng) >>= id`. -/
theorem fst_runProg {R α : Type} (i : rand_1.rng.Rng R) (p : OracleComp fillSpec (Result α))
    (rng : R) :
    Prod.fst <$> runProg i p rng = (Prod.fst <$> (simulateQ (fillImpl i) p).run rng) >>= id := by
  have hok : ∀ {γ : Type} (x : γ), ok x = pure x := fun _ => rfl
  have hbind : ∀ {γ δ : Type} (x : Result γ) (f : γ → Result δ),
      Std.bind x f = x >>= f := fun _ _ => rfl
  simp only [runProg, hok, hbind, map_bind, bind_map_left, map_pure, bind_pure, uncurry, id]

/-- For every `n`, `IdealRng tapeRng (tapeSeed n) n`. So `IdealRng` is not empty. -/
theorem idealRng_tape (n : ℕ) : IdealRng tapeRng (tapeSeed n) n := by
  intro α p hp
  have h := (tape_sim p n hp).map (fun r => r >>= id)
  simp only [tapeSeed, fst_runProg, bind_map_left]
  simpa [map_bind] using h

end SpqrBridge
