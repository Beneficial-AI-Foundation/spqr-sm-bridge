/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Spqr.Specs.Braid.StateMachine.Refinement
import Spqr.Specs.V1.Chunked.SendEk.KeysUnsampled.New
import Spqr.Specs.V1.Chunked.SendCt.NoHeaderReceived.New
import SecureMessaging.SCKA.Defs

/-!
# The code's chunked `States` machine as an SCKA scheme

`codeScheme` presents the extracted `spqr::v1::chunked::states::States` machine as a
secure-messaging `SCKAScheme`:

* the initial key is `InitKey`, a byte slice on which `init_a` and `init_b` succeed
  (`init_a_ok`, `init_b_ok`), so `initA` and `initB` are total without a default state;
* a send is one program over a `fill_bytes` oracle (`sendProg`). The game interprets the oracle
  with uniform bytes (`unifImpl`). `send_eq_prog` (`SpqrBridge.RngMonad`) shows that the extracted
  `States::send` is equal to the second component of the same program, interpreted with the
  `fill_bytes` of any RNG (`fillImpl`) and run with `runProg`;
* an Aeneas failure, a Rust `Err` and a key that is not 32 bytes long all give `none`;
* `send` reports the outgoing message's epoch minus 1, and `recv` reports the incoming
  message's epoch minus 1, as `chain.send_key(msg.epoch - 1)` and
  `chain.recv_key(msg.epoch - 1, _)` in `lib.rs` select chain keys.

`CodeReach` is the set of code configurations that a correctness game reaches;
`SpqrBridge.EpochBound` bounds their epochs.

`sendProg` queries the oracle before all other steps. The extracted `send` reads the epoch
before it calls `fill_bytes`. The epoch accessors return `ok` and do not use the RNG, so the two
orders give equal results (`send_eq_prog`).
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states

/-- Let `x ⦃ v => P v ⦄`. Then `x = ok a` for some `a`. -/
theorem exists_ok_of_spec {α : Type} {x : Result α} {P : α → Prop} (h : x ⦃ v => P v ⦄) :
    ∃ a, x = ok a := by
  cases x with
  | ret r => exact ⟨r, rfl⟩
  | vis i k => exact absurd h (by simp only [WP.spec_vis, not_false_eq_true])
  | div => exact absurd h (by simp only [WP.spec_div, not_false_eq_true])

/-! ## Initial key -/

/-- `InitKey` is `{k : Slice Std.U8 // k.length + 32 ≤ Std.Usize.max}`. `init_a` and `init_b`
succeed on `k` if and only if `k` satisfies this bound (`init_a_ok`, `init_a_ok_imp`, `init_b_ok`,
`init_b_ok_imp`). -/
def InitKey : Type := {k : Slice Std.U8 // k.length + 32 ≤ Std.Usize.max}

/-- For every `k : InitKey`, `States.init_a k.1 = ok s` for some `s`. -/
theorem init_a_ok (k : InitKey) : ∃ s, States.init_a k.1 = ok s := by
  have h := v1.chunked.send_ek.KeysUnsampled.new_spec k.1 k.2
  obtain ⟨ku, hku⟩ := exists_ok_of_spec h
  exact ⟨.KeysUnsampled ku, by simp only [States.init_a, hku, bind_ok]⟩

/-- For every `k : InitKey`, `States.init_b k.1 = ok s` for some `s`. -/
theorem init_b_ok (k : InitKey) : ∃ s, States.init_b k.1 = ok s := by
  have h := v1.chunked.send_ct.NoHeaderReceived.new_spec k.1 k.2
  obtain ⟨n, hn⟩ := exists_ok_of_spec h
  exact ⟨.NoHeaderReceived n, by simp only [States.init_b, hn, bind_ok]⟩

/-- Let `to_vec key = ok v` and `Authenticator.new v ep = ok a`. Then
`key.length + 32 ≤ usize::MAX`. -/
theorem auth_new_ok_imp {key : Slice Std.U8} {v : alloc.vec.Vec Std.U8} {ep : Std.U64}
    {a : authenticator.Authenticator}
    (hv : alloc.slice.Slice.to_vec core.clone.CloneU8 key = ok v)
    (h : authenticator.Authenticator.new v ep = ok a) : key.length + 32 ≤ Std.Usize.max := by
  simp only [authenticator.Authenticator.new, Result.bind_eq_ok] at h
  obtain ⟨z, hz, hu⟩ := h
  have hb := authenticator.Authenticator.length_le_of_update_ok hu
  have hz' : z.length = 32 := (WP.post_of_ok (alloc.vec.from_elem_spec _ _ _ rfl) hz).2
  have hd : v.deref.length = key.length := by
    simp only [alloc.vec.Vec.deref, Slice.length, Slice.from_val, Slice.to_vec_U8_ok_val hv]
  have hb' : z.length + key.length ≤ Usize.max := hd ▸ hb
  omega

/-- Let `States.init_a key = ok s`. Then `key.length + 32 ≤ usize::MAX`. -/
theorem init_a_ok_imp (key : Slice Std.U8) (s : States) (h : States.init_a key = ok s) :
    key.length + 32 ≤ Std.Usize.max := by
  simp only [States.init_a, v1.chunked.send_ek.KeysUnsampled.new,
    v1.unchunked.send_ek.KeysUnsampled.new, Result.bind_eq_ok] at h
  obtain ⟨_, ⟨_, ⟨v, hv, a, ha, -⟩, -⟩, -⟩ := h
  exact auth_new_ok_imp hv ha

/-- Let `States.init_b key = ok s`. Then `key.length + 32 ≤ usize::MAX`. -/
theorem init_b_ok_imp (key : Slice Std.U8) (s : States) (h : States.init_b key = ok s) :
    key.length + 32 ≤ Std.Usize.max := by
  simp only [States.init_b, v1.chunked.send_ct.NoHeaderReceived.new,
    v1.unchunked.send_ct.NoHeaderReceived.new, Result.bind_eq_ok] at h
  obtain ⟨_, ⟨_, -, _, -, _, -, _, ⟨v, hv, a, ha, -⟩, -⟩, -⟩ := h
  exact auth_new_ok_imp hv ha

/-- Let `r = ok a` for some `a`. Then `okOf r h` is this `a` (`okOf_eq`). The value `a` is
unique, because `ok` is injective. -/
noncomputable def okOf {α : Type} (r : Result α) (h : ∃ a, r = ok a) : α := Classical.choose h

/-- Let `r = ok a` for some `a`. Then `r = ok (okOf r h)`. -/
theorem okOf_eq {α : Type} (r : Result α) (h : ∃ a, r = ok a) : r = ok (okOf r h) :=
  Classical.choose_spec h

/-- Let `k : InitKey`. Then `initAState k` is the unique state `s` with `States.init_a k.1 = ok s`
(`init_a_eq`). -/
noncomputable def initAState (k : InitKey) : States := okOf _ (init_a_ok k)

/-- Let `k : InitKey`. Then `initBState k` is the unique state `s` with `States.init_b k.1 = ok s`
(`init_b_eq`). -/
noncomputable def initBState (k : InitKey) : States := okOf _ (init_b_ok k)

theorem init_a_eq (k : InitKey) : States.init_a k.1 = ok (initAState k) := okOf_eq _ _

theorem init_b_eq (k : InitKey) : States.init_b k.1 = ok (initBState k) := okOf_eq _ _

/-! ## Byte strings of fixed length -/

/-- `B n` is `{b : List Std.U8 // b.length = n}`, the type of byte lists of length `n`. -/
abbrev B (n : ℕ) : Type := {b : List Std.U8 // b.length = n}

/-- `byteOfFin x` is the `Std.U8` value with bit vector `BitVec.ofFin x`. -/
def byteOfFin (x : Fin 256) : Std.U8 := ⟨BitVec.ofFin x⟩

/-- `sampleB n` samples `v` uniformly from `Vector (Fin 256) n` and returns the element of `B n`
with list `v.toList.map byteOfFin`. -/
def sampleB (n : ℕ) : ProbComp (B n) := do
  let v ← $ᵗ (Vector (Fin 256) n)
  return ⟨v.toList.map byteOfFin, by simp⟩

/-- Let `t : B n` and `h : n ≤ Std.Usize.max`. Then `sliceOf t h` is the slice with contents `t.1`
(`sliceOf_val`). -/
def sliceOf {n : ℕ} (t : B n) (h : n ≤ Std.Usize.max) : Slice Std.U8 :=
  Slice.from t.1 (by rw [t.2]; exact h)

theorem sliceOf_val {n : ℕ} (t : B n) (h : n ≤ Std.Usize.max) : (sliceOf t h).val = t.1 :=
  Slice.from_val _ _

theorem sliceOf_length {n : ℕ} (t : B n) (h : n ≤ Std.Usize.max) : (sliceOf t h).length = n := by
  simp only [Slice.length, sliceOf_val]; exact t.2

/-! ## The RNG as an oracle

The code takes its RNG as an argument of any type `R`. Here the RNG is an oracle, and the two
handlers below interpret it. -/

/-- `fillSpec` is the oracle specification `Slice Std.U8 →ₒ Slice Std.U8` of `fill_bytes`. It
does not relate the lengths of a query and its answer. In Rust, `fill_bytes` writes into its
argument, so the length cannot change. The Aeneas model returns a new slice. -/
abbrev fillSpec : OracleSpec (Slice Std.U8) := Slice Std.U8 →ₒ Slice Std.U8

/-- Let `i : rand_1.rng.Rng R`, `s : Slice Std.U8` and `rng : R`. Then `(fillImpl i s).run rng`
is `Std.bind (i.rand_core_1RngCoreInst.fill_bytes rng s) (fun p => ok (p.2, p.1))`. So the
answer is the slice that `fill_bytes` returns, and the new state is its new RNG state. An error
or divergence of `fill_bytes` is the result of the handler. -/
def fillImpl {R : Type} (i : rand_1.rng.Rng R) : QueryImpl fillSpec (StateT R Result) :=
  fun s rng => do
    let (rng1, s1) ← i.rand_core_1RngCoreInst.fill_bytes rng s
    ok (s1, rng1)

/-- `unifImpl` answers the query `s` with `sliceOf t`, where `sampleB s.length` samples `t`. The
answer has length `s.length` and does not depend on the content of `s`. -/
def unifImpl : QueryImpl fillSpec ProbComp := fun s => do
  let t ← sampleB s.length
  return sliceOf t s.property

/-- `fixedCore buf` is the `RngCore Unit` whose `fill_bytes` returns `ok ((), buf)` on every
input, and whose `next_u32` and `next_u64` return `fail .panic`. -/
def fixedCore (buf : Slice Std.U8) : rand_core_1.RngCore Unit where
  next_u32 _ := fail .panic
  next_u64 _ := fail .panic
  fill_bytes _ _ := ok ((), buf)

/-- `fixedRng buf` is `⟨fixedCore buf⟩ : rand_1.rng.Rng Unit`. -/
def fixedRng (buf : Slice Std.U8) : rand_1.rng.Rng Unit := ⟨fixedCore buf⟩

/-- `fixedCrypto buf` is `⟨fixedCore buf⟩ : rand_core_1.CryptoRng Unit`. This structure states no
property of the generated bytes. -/
def fixedCrypto (buf : Slice Std.U8) : rand_core_1.CryptoRng Unit := ⟨fixedCore buf⟩

/-! ## One send as a program over the oracle -/

/-- `sendRest s buf` is `Prod.fst <$> States.send (fixedRng buf) (fixedCrypto buf) s ()`. This is
the result of the extracted `send` when each `fill_bytes` call returns `buf`. -/
noncomputable def sendRest (s : States) (buf : Slice Std.U8) :
    Result (core.result.Result v1.chunked.states.Send spqr.Error) := do
  let p ← States.send (fixedRng buf) (fixedCrypto buf) s ()
  ok p.1

/-- `buf64` is `(Array.repeat 64#usize 0#u8).to_slice`, the buffer of 64 zero bytes that
`generate` passes to `fill_bytes`. -/
def buf64 : Slice Std.U8 := (Array.repeat 64#usize 0#u8).to_slice

/-- `buf32` is `(Array.repeat 32#usize 0#u8).to_slice`, the buffer of 32 zero bytes that
`encaps1` passes to `fill_bytes`. -/
def buf32 : Slice Std.U8 := (Array.repeat 32#usize 0#u8).to_slice

/-- `noBuf` is the slice with contents `[]`. It is the value of `sendBuf s` in the states `s`
where `send` does not call `fill_bytes`. -/
def noBuf : Slice Std.U8 := Slice.from [] (Nat.zero_le _)

/-- `sendLen s` is 64 for `KeysUnsampled`, 32 for `HeaderReceived`, and 0 for each other state.
It is the length of the slice that `sendBuf s` queries (`buf64_length`, `buf32_length`), and 0
if `sendBuf s` makes no query. -/
def sendLen : States → ℕ
  | .KeysUnsampled _ => 64
  | .HeaderReceived _ => 32
  | _ => 0

/-- `sendBuf s` is the query `buf64` for `KeysUnsampled`, the query `buf32` for `HeaderReceived`,
and `pure noBuf` for each other state. By `send_eq_prog` (`SpqrBridge.RngMonad`), these are the
`fill_bytes` calls of the extracted `send`. -/
def sendBuf : States → OracleComp fillSpec (Slice Std.U8)
  | .KeysUnsampled _ => liftM (fillSpec.query buf64)
  | .HeaderReceived _ => liftM (fillSpec.query buf32)
  | _ => pure noBuf

/-- `sendProg s` runs `sendBuf s` and, for its value `b`, returns `(b, sendRest s b)`. -/
noncomputable def sendProg (s : States) :
    OracleComp fillSpec
      (Slice Std.U8 × Result (core.result.Result v1.chunked.states.Send spqr.Error)) := do
  let b ← sendBuf s
  return (b, sendRest s b)

/-- `runProg i p rng` is
`Std.bind ((simulateQ (fillImpl i) p).run rng) (fun q => Std.bind q.1 (fun a => ok (a, q.2)))`.
So it interprets `p` with `fillImpl i` from the state `rng`. If the interpretation returns
`ok (r, rng')` and `r = ok a`, then `runProg i p rng = ok (a, rng')`. An error or divergence of
the interpretation or of `r` is the result of `runProg i p rng`. -/
def runProg {R α : Type} (i : rand_1.rng.Rng R) (p : OracleComp fillSpec (Result α)) (rng : R) :
    Result (α × R) := do
  let (r, rng1) ← (simulateQ (fillImpl i) p).run rng
  let a ← r
  ok (a, rng1)

/-! ## One step of the code -/

/-- `outOf r = some out` if `r = ok (.Ok out)`. In each other case, `outOf r = none`. -/
noncomputable def outOf (r : Result (core.result.Result v1.chunked.states.Send spqr.Error)) :
    Option v1.chunked.states.Send :=
  match r.match with
  | .ok (.Ok out) => some out
  | _ => none

/-- `codeSend s buf = outOf (sendRest s buf)`. It is `some out` if and only if
`States.send (fixedRng buf) (fixedCrypto buf) s ()` returns `ok (.Ok out, r)` for some `r`
(`codeSend_eq_some_iff`, `SpqrBridge.SendFacts`). -/
noncomputable def codeSend (s : States) (buf : Slice Std.U8) : Option v1.chunked.states.Send :=
  outOf (sendRest s buf)

/-- `codeRecv s msg = some out` if `States.recv s msg = ok (.Ok out)`. In each other case,
`codeRecv s msg = none`. -/
noncomputable def codeRecv (s : States) (msg : Message) : Option v1.chunked.states.Recv :=
  match (States.recv s msg).match with
  | .ok (.Ok out) => some out
  | _ => none

/-- `keyOf none = some none`. If `h : es.secret.val.length = 32`, then
`keyOf (some es) = some (some (es.epoch.val, ⟨es.secret.val, h⟩))`. If not,
`keyOf (some es) = none`. By
`codeSend_key_length` and `codeRecv_key_length` (`SpqrBridge.KeyLength`), the last case does not
occur on a key that `codeSend` or `codeRecv` returns. -/
def keyOf : Option EpochSecret → Option (Option (ℕ × B 32))
  | none => some none
  | some es =>
    if h : es.secret.val.length = 32 then some (some (es.epoch.val, ⟨es.secret.val, h⟩))
    else none

/-- If `outOf r = some out` and `keyOf out.key = some k`, then
`stepOf r = some (k, out.msg, out.msg.epoch.val - 1, out.state)`. In each other case,
`stepOf r = none`. The subtraction is on natural numbers. -/
noncomputable def stepOf (r : Result (core.result.Result v1.chunked.states.Send spqr.Error)) :
    Option (Option (ℕ × B 32) × Message × ℕ × States) := do
  let out ← outOf r
  let k ← keyOf out.key
  return (k, out.msg, out.msg.epoch.val - 1, out.state)

/-- `sendStep s buf = stepOf (sendRest s buf)`. -/
noncomputable def sendStep (s : States) (buf : Slice Std.U8) :
    Option (Option (ℕ × B 32) × Message × ℕ × States) :=
  stepOf (sendRest s buf)

/-- If `codeRecv s msg = some out` and `keyOf out.key = some k`, then
`recvStep s msg = some (k, msg.epoch.val - 1, out.state)`. In each other case,
`recvStep s msg = none`. The subtraction is on natural numbers. -/
noncomputable def recvStep (s : States) (msg : Message) : Option (Option (ℕ × B 32) × ℕ × States) := do
  let out ← codeRecv s msg
  let k ← keyOf out.key
  return (k, msg.epoch.val - 1, out.state)

/-- `codeSendA s` interprets `sendProg s` with `unifImpl` and returns `stepOf` of the second
component of the value. -/
noncomputable def codeSendA (s : States) :
    ProbComp (Option (Option (ℕ × B 32) × Message × ℕ × States)) := do
  let p ← simulateQ unifImpl (sendProg s)
  return stepOf p.2

/-- `codeSendRleak s` interprets `sendProg s` with `unifImpl`. Let `(b, r)` be the value. If
`stepOf r = some (k, m, e, s')`, the result is `some (k, m, e, s', b)`. If not, it is `none`. -/
noncomputable def codeSendRleak (s : States) :
    ProbComp (Option (Option (ℕ × B 32) × Message × ℕ × States × Slice Std.U8)) := do
  let p ← simulateQ unifImpl (sendProg s)
  return (stepOf p.2).map fun (k, m, e, s') => (k, m, e, s', p.1)

/-- `sampleBuf s` is `sendBuf s`, interpreted with `unifImpl`. -/
def sampleBuf (s : States) : ProbComp (Slice Std.U8) := simulateQ unifImpl (sendBuf s)

/-- `codeSendA s` samples `b` with `sampleBuf s` and returns `sendStep s b`. -/
theorem codeSendA_eq (s : States) :
    codeSendA s = (do let b ← sampleBuf s; pure (sendStep s b)) := by
  simp only [codeSendA, sendProg, sampleBuf, sendStep, simulateQ_bind, simulateQ_pure,
    bind_assoc, pure_bind]

/-- Let `b.length = n`. Then `unifImpl b` samples `t` with `sampleB n` and returns `sliceOf t`. -/
theorem unifImpl_of_length (b : Slice Std.U8) (n : ℕ) (h : b.length = n) :
    unifImpl b = (do let t ← sampleB n; pure (sliceOf t (h ▸ b.property))) := by
  subst h
  rfl

theorem buf64_length : buf64.length = 64 := by
  simp only [buf64, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

theorem buf32_length : buf32.length = 32 := by
  simp only [buf32, Slice.length, Array.val_to_slice, Aeneas.Std.Array.length_eq]; rfl

/-- `sampleBuf (.KeysUnsampled st)` samples `t` with `sampleB 64` and returns `sliceOf t`. -/
theorem sampleBuf_keysUnsampled (st : v1.chunked.send_ek.KeysUnsampled) :
    sampleBuf (.KeysUnsampled st) =
      (do let t ← sampleB 64; pure (sliceOf t (by scalar_tac))) := by
  simp only [sampleBuf, sendBuf, simulateQ_spec_query]
  exact unifImpl_of_length buf64 64 buf64_length

/-- `sampleBuf (.HeaderReceived st)` samples `t` with `sampleB 32` and returns `sliceOf t`. -/
theorem sampleBuf_headerReceived (st : v1.chunked.send_ct.HeaderReceived) :
    sampleBuf (.HeaderReceived st) =
      (do let t ← sampleB 32; pure (sliceOf t (by scalar_tac))) := by
  simp only [sampleBuf, sendBuf, simulateQ_spec_query]
  exact unifImpl_of_length buf32 32 buf32_length

/-- Let `sendLen s = 64`. Then `sampleBuf s` samples `t` with `sampleB 64` and returns
`sliceOf t`. -/
theorem sampleBuf_of_sendLen_64 (s : States) (h : sendLen s = 64) :
    sampleBuf s = (do let t ← sampleB 64; pure (sliceOf t (by scalar_tac))) := by
  cases s with
  | KeysUnsampled st => exact sampleBuf_keysUnsampled st
  | _ => simp [sendLen] at h

/-- Let `sendLen s = 32`. Then `sampleBuf s` samples `t` with `sampleB 32` and returns
`sliceOf t`. -/
theorem sampleBuf_of_sendLen_32 (s : States) (h : sendLen s = 32) :
    sampleBuf s = (do let t ← sampleB 32; pure (sliceOf t (by scalar_tac))) := by
  cases s with
  | HeaderReceived st => exact sampleBuf_headerReceived st
  | _ => simp [sendLen] at h

/-- Let `sendLen s = 0`. Then `sampleBuf s = pure noBuf`. -/
theorem sampleBuf_of_sendLen_zero (s : States) (h : sendLen s = 0) : sampleBuf s = pure noBuf := by
  cases s <;> first | (simp only [sendLen] at h; omega) | simp only [sampleBuf, sendBuf, simulateQ_pure]

/-- Let `b` be in the support of `sampleBuf s`. Then `b.length = sendLen s`. -/
theorem sampleBuf_length (s : States) (b : Slice Std.U8) (h : b ∈ support (sampleBuf s)) :
    b.length = sendLen s := by
  cases s with
  | KeysUnsampled st =>
    rw [sampleBuf_keysUnsampled, mem_support_bind_iff] at h
    obtain ⟨t, -, ht⟩ := h
    rw [mem_support_pure_iff] at ht
    rw [ht]; exact sliceOf_length t _
  | HeaderReceived st =>
    rw [sampleBuf_headerReceived, mem_support_bind_iff] at h
    obtain ⟨t, -, ht⟩ := h
    rw [mem_support_pure_iff] at ht
    rw [ht]; exact sliceOf_length t _
  | _ =>
    rw [sampleBuf_of_sendLen_zero _ rfl, mem_support_pure_iff] at h
    rw [h]; rfl

/-! ## The scheme -/

/-- `codeScheme sampleInitKey` is the SCKA scheme with `initKeyGen = sampleInitKey`,
`initA k = pure (initAState k)` and `initB k = pure (initBState k)`. For both parties, the send is
`codeSendA`, the receive is `recvStep`, and the send that leaks its randomness is
`codeSendRleak`. The randomness type is `Slice Std.U8`. -/
noncomputable def codeScheme (sampleInitKey : ProbComp InitKey) :
    SCKAScheme ProbComp InitKey States States (B 32) Message (Slice Std.U8) where
  initKeyGen := sampleInitKey
  initA k := pure (initAState k)
  initB k := pure (initBState k)
  sendA := codeSendA
  sendArleak := codeSendRleak
  recvA := recvStep
  sendB := codeSendA
  sendBrleak := codeSendRleak
  recvB := recvStep

/-- `CodeReach sA sB mA mB n` is the least predicate with these rules:

* it holds for `initAState k`, `initBState k`, `[]`, `[]` and `0`, for every `k : InitKey`;
* a party in state `s` sends: if `buf.length = sendLen s` and `codeSend s buf = some out`, the
  state of the party becomes `out.state`, `out.msg` is appended to the list of the party, and
  `n` increases by 1;
* a party in state `s` receives: if `m` is in the list of the other party and
  `codeRecv s m = some out`, the state of the party becomes `out.state`.

So `mA` and `mB` are the messages that A and B sent, and `n` is the number of successful sends.
A call that returns `none` is not a step. A party can receive a message more than once, and in
any order. The rules do not use `keyOf`. -/
inductive CodeReach : States → States → List Message → List Message → ℕ → Prop
  | init (k : InitKey) : CodeReach (initAState k) (initBState k) [] [] 0
  | sendA {sA sB mA mB n} (buf : Slice Std.U8) (out : v1.chunked.states.Send) :
      CodeReach sA sB mA mB n → buf.length = sendLen sA → codeSend sA buf = some out →
      CodeReach out.state sB (mA ++ [out.msg]) mB (n + 1)
  | sendB {sA sB mA mB n} (buf : Slice Std.U8) (out : v1.chunked.states.Send) :
      CodeReach sA sB mA mB n → buf.length = sendLen sB → codeSend sB buf = some out →
      CodeReach sA out.state mA (mB ++ [out.msg]) (n + 1)
  | recvA {sA sB mA mB n} (m : Message) (out : v1.chunked.states.Recv) :
      CodeReach sA sB mA mB n → m ∈ mB → codeRecv sA m = some out →
      CodeReach out.state sB mA mB n
  | recvB {sA sB mA mB n} (m : Message) (out : v1.chunked.states.Recv) :
      CodeReach sA sB mA mB n → m ∈ mA → codeRecv sB m = some out →
      CodeReach sA out.state mA mB n

end SpqrBridge
