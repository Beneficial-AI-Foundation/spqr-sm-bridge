/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
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
* each send samples a uniform 64-byte tape and runs `States::send` with `tapeRng`, an RNG whose
  `fill_bytes` reads the first bytes of the tape;
* an Aeneas failure, a Rust `Err` and a key that is not 32 bytes long all give `none`;
* `send` reports the outgoing message's epoch minus 1, and `recv` reports the incoming
  message's epoch minus 1, as `lib.rs:298` and `lib.rs:425` select chain keys.

The open obligations are `send_key_length` and `recv_key_length`. `CodeReach` is the set of
code configurations that a correctness game reaches; `SpqrBridge.EpochBound` bounds their epochs.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states

/-- A computation that meets some spec returns `ok`. -/
theorem exists_ok_of_spec {α : Type} {x : Result α} {P : α → Prop} (h : x ⦃ v => P v ⦄) :
    ∃ a, x = ok a := by
  cases x with
  | ret r => exact ⟨r, rfl⟩
  | vis i k => exact absurd h (by simp only [WP.spec_vis, not_false_eq_true])
  | div => exact absurd h (by simp only [WP.spec_div, not_false_eq_true])

/-! ## Initial key -/

/-- An initial key that the code's `init_a` and `init_b` accept: the authenticator appends 32
bytes to it, so its length plus 32 fits in a `usize`. -/
def InitKey : Type := {k : Slice Std.U8 // k.length + 32 ≤ Std.Usize.max}

/-- `init_a` succeeds on every `InitKey`. -/
theorem init_a_ok (k : InitKey) : ∃ s, States.init_a k.1 = ok s := by
  have h := v1.chunked.send_ek.KeysUnsampled.new_spec k.1 k.2
  obtain ⟨ku, hku⟩ := exists_ok_of_spec h
  exact ⟨.KeysUnsampled ku, by simp only [States.init_a, hku, bind_ok]⟩

/-- `init_b` succeeds on every `InitKey`. -/
theorem init_b_ok (k : InitKey) : ∃ s, States.init_b k.1 = ok s := by
  have h := v1.chunked.send_ct.NoHeaderReceived.new_spec k.1 k.2
  obtain ⟨n, hn⟩ := exists_ok_of_spec h
  exact ⟨.NoHeaderReceived n, by simp only [States.init_b, hn, bind_ok]⟩

/-- `Authenticator::new` succeeds only if the key length plus 32 fits in a `usize`. -/
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

/-- The bound of `InitKey` is exact for `init_a`: if `init_a` succeeds, the key length plus 32
fits in a `usize`. -/
theorem init_a_ok_imp (key : Slice Std.U8) (s : States) (h : States.init_a key = ok s) :
    key.length + 32 ≤ Std.Usize.max := by
  simp only [States.init_a, v1.chunked.send_ek.KeysUnsampled.new,
    v1.unchunked.send_ek.KeysUnsampled.new, Result.bind_eq_ok] at h
  obtain ⟨_, ⟨_, ⟨v, hv, a, ha, -⟩, -⟩, -⟩ := h
  exact auth_new_ok_imp hv ha

/-- The bound of `InitKey` is exact for `init_b`. -/
theorem init_b_ok_imp (key : Slice Std.U8) (s : States) (h : States.init_b key = ok s) :
    key.length + 32 ≤ Std.Usize.max := by
  simp only [States.init_b, v1.chunked.send_ct.NoHeaderReceived.new,
    v1.unchunked.send_ct.NoHeaderReceived.new, Result.bind_eq_ok] at h
  obtain ⟨_, ⟨_, -, _, -, _, -, _, ⟨v, hv, a, ha, -⟩, -⟩, -⟩ := h
  exact auth_new_ok_imp hv ha

/-- The value of a `Result` that is known to succeed. It is unique, so the choice picks the
code's own value, not a default. -/
noncomputable def okOf {α : Type} (r : Result α) (h : ∃ a, r = ok a) : α := Classical.choose h

theorem okOf_eq {α : Type} (r : Result α) (h : ∃ a, r = ok a) : r = ok (okOf r h) :=
  Classical.choose_spec h

/-- A's initial state: the state that `init_a` returns. -/
noncomputable def initAState (k : InitKey) : States := okOf _ (init_a_ok k)

/-- B's initial state: the state that `init_b` returns. -/
noncomputable def initBState (k : InitKey) : States := okOf _ (init_b_ok k)

theorem init_a_eq (k : InitKey) : States.init_a k.1 = ok (initAState k) := okOf_eq _ _

theorem init_b_eq (k : InitKey) : States.init_b k.1 = ok (initBState k) := okOf_eq _ _

/-! ## Tape RNG -/

/-- `fill_bytes` of the tape RNG: fill the slice with the first bytes of the tape and keep the
rest. It fails if the tape is too short. -/
def tapeFill (t : List Std.U8) (s : Slice Std.U8) : Result (List Std.U8 × Slice Std.U8) :=
  if h : s.length ≤ t.length then
    ok (t.drop s.length, Slice.from (t.take s.length) (by
      simp only [List.length_take]; exact Nat.le_trans (Nat.min_le_left _ _) s.property))
  else fail .panic

/-- The tape as a `RngCore`. `States::send` calls only `fill_bytes`. -/
def tapeCore : rand_core_1.RngCore (List Std.U8) where
  next_u32 _ := fail .panic
  next_u64 _ := fail .panic
  fill_bytes := tapeFill

/-- The tape as a `rand::Rng`. -/
def tapeRng : rand_1.rng.Rng (List Std.U8) := ⟨tapeCore⟩

/-- The tape as a `CryptoRng`. -/
def tapeCrypto : rand_core_1.CryptoRng (List Std.U8) := ⟨tapeCore⟩

/-! ## Byte strings of fixed length -/

/-- Byte strings of length `n`. -/
abbrev B (n : ℕ) : Type := {b : List Std.U8 // b.length = n}

/-- A uniform byte. -/
def byteOfFin (x : Fin 256) : Std.U8 := ⟨BitVec.ofFin x⟩

/-- A uniform 64-byte tape. -/
def sampleTape : ProbComp (B 64) := do
  let v ← $ᵗ (Vector (Fin 256) 64)
  return ⟨v.toList.map byteOfFin, by simp⟩

/-! ## One step of the code -/

/-- `States::send` with the tape RNG, when it returns `Ok`. -/
noncomputable def codeSend (s : States) (tape : List Std.U8) : Option v1.chunked.states.Send :=
  match (States.send tapeRng tapeCrypto s tape).match with
  | .ok (.Ok out, _) => some out
  | _ => none

/-- `States::recv`, when it returns `Ok`. -/
noncomputable def codeRecv (s : States) (msg : Message) : Option v1.chunked.states.Recv :=
  match (States.recv s msg).match with
  | .ok (.Ok out) => some out
  | _ => none

/-- The key output as an SCKA key: the epoch and the 32-byte secret. The outer `none` means
that the secret is not 32 bytes long; `send_key_length` and `recv_key_length` say that this
does not happen. -/
def keyOf : Option EpochSecret → Option (Option (ℕ × B 32))
  | none => some none
  | some es =>
    if h : es.secret.val.length = 32 then some (some (es.epoch.val, ⟨es.secret.val, h⟩))
    else none

/-- One send with a given tape, as SCKA's `send` returns it. The sending epoch is the message
epoch minus 1. -/
noncomputable def sendStep (s : States) (tape : List Std.U8) :
    Option (Option (ℕ × B 32) × Message × ℕ × States) := do
  let out ← codeSend s tape
  let k ← keyOf out.key
  return (k, out.msg, out.msg.epoch.val - 1, out.state)

/-- One receive, as SCKA's `recv` returns it. The receiving epoch is the incoming message's
epoch minus 1, also for a stale message. -/
noncomputable def recvStep (s : States) (msg : Message) : Option (Option (ℕ × B 32) × ℕ × States) := do
  let out ← codeRecv s msg
  let k ← keyOf out.key
  return (k, msg.epoch.val - 1, out.state)

/-- A send that samples a fresh tape. -/
noncomputable def codeSendA (s : States) : ProbComp (Option (Option (ℕ × B 32) × Message × ℕ × States)) := do
  let t ← sampleTape
  return sendStep s t.1

/-- A send that samples a fresh tape and also returns it. -/
noncomputable def codeSendRleak (s : States) :
    ProbComp (Option (Option (ℕ × B 32) × Message × ℕ × States × B 64)) := do
  let t ← sampleTape
  return (sendStep s t.1).map fun (k, m, e, s') => (k, m, e, s', t)

/-! ## The scheme -/

/-- The code's chunked `States` machine as an SCKA scheme. Both parties run the same `send` and
`recv`; only the initial state differs. The randomness of a send is its 64-byte tape. -/
noncomputable def codeScheme (sampleInitKey : ProbComp InitKey) :
    SCKAScheme ProbComp InitKey States States (B 32) Message (B 64) where
  initKeyGen := sampleInitKey
  initA k := pure (initAState k)
  initB k := pure (initBState k)
  sendA := codeSendA
  sendArleak := codeSendRleak
  recvA := recvStep
  sendB := codeSendA
  sendBrleak := codeSendRleak
  recvB := recvStep

/-! ## Obligations -/

/-- Every key that a successful `States::send` returns is 32 bytes long. Belongs in `spqr`. -/
theorem send_key_length (s : States) (tape : List Std.U8) (out : v1.chunked.states.Send)
    (h : codeSend s tape = some out) : ∀ es ∈ out.key, es.secret.val.length = 32 := by
  sorry

/-- Every key that a successful `States::recv` returns is 32 bytes long. Belongs in `spqr`. -/
theorem recv_key_length (s : States) (msg : Message) (out : v1.chunked.states.Recv)
    (h : codeRecv s msg = some out) : ∀ es ∈ out.key, es.secret.val.length = 32 := by
  sorry

/-- The open obligations of the adapter, as one structure. -/
structure AdapterObligations : Prop where
  send_key_length : ∀ (s : States) (tape : List Std.U8) (out : v1.chunked.states.Send),
    codeSend s tape = some out → ∀ es ∈ out.key, es.secret.val.length = 32
  recv_key_length : ∀ (s : States) (msg : Message) (out : v1.chunked.states.Recv),
    codeRecv s msg = some out → ∀ es ∈ out.key, es.secret.val.length = 32

theorem adapterObligations : AdapterObligations :=
  ⟨send_key_length, recv_key_length⟩

/-- The code states and messages that a correctness game can reach, with the number of
successful sends. A failed call leaves both states unchanged in SM's oracles, so it is not a
step here. A delivery may pick any message the other party sent: replays and stale messages
are allowed. Sends and receives are the code's own, so a send whose key the adapter refuses
is still a step. -/
inductive CodeReach : States → States → List Message → List Message → ℕ → Prop
  | init (k : InitKey) : CodeReach (initAState k) (initBState k) [] [] 0
  | sendA {sA sB mA mB n} (tape : List Std.U8) (out : v1.chunked.states.Send) :
      CodeReach sA sB mA mB n → codeSend sA tape = some out →
      CodeReach out.state sB (mA ++ [out.msg]) mB (n + 1)
  | sendB {sA sB mA mB n} (tape : List Std.U8) (out : v1.chunked.states.Send) :
      CodeReach sA sB mA mB n → codeSend sB tape = some out →
      CodeReach sA out.state mA (mB ++ [out.msg]) (n + 1)
  | recvA {sA sB mA mB n} (m : Message) (out : v1.chunked.states.Recv) :
      CodeReach sA sB mA mB n → m ∈ mB → codeRecv sA m = some out →
      CodeReach out.state sB mA mB n
  | recvB {sA sB mA mB n} (m : Message) (out : v1.chunked.states.Recv) :
      CodeReach sA sB mA mB n → m ∈ mA → codeRecv sB m = some out →
      CodeReach sA out.state mA mB n

end SpqrBridge
