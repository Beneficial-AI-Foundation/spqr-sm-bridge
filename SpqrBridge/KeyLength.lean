/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.EpochBound

/-!
# Keys from `send` and `recv` have 32 bytes

`codeSend_key_length` and `codeRecv_key_length` prove the `send_key_length` and
`recv_key_length` fields of `BridgeObligations`, for every state, tape and message.

Only two transitions emit a key (`send_key_epoch`, `recv_key_epoch`): `send` from
`HeaderReceived` (`send_ct1`) and `recv` of the last `Ct2` chunk in `EkSentCt1Received`
(`recv_ct2`). Both take the secret from `hkdf_to_vec` with output length 32, so the length
comes from `hkdf_to_vec_spec`, which rests on the HKDF axiom `hkdf_to_slice_spec`.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states
open core.result.Result.Insts.CoreOpsTry (branch_eq_continue)
open core.result.Result.Insts.CoreOpsTry_traitFromResidualResult (from_residual_ne_ok)

/-- The epoch secret that `send_ct1` returns has 32 bytes. -/
theorem send_ct1_secret_length {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (self : v1.unchunked.send_ct.HeaderReceived) (rng : R) {r}
    (h : v1.unchunked.send_ct.HeaderReceived.send_ct1 i₁ i₂ self rng = ok r) :
    r.1.2.2.secret.length = 32 := by
  simp only [v1.unchunked.send_ct.HeaderReceived.send_ct1, Result.bind_eq_ok] at h
  obtain ⟨⟨⟨_, _, _⟩, _⟩, -, h⟩ := h
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, hk, _, -, _, -, h⟩ := h
  simp only [Result.ok.injEq] at h
  subst h
  exact (WP.post_of_ok (kdf.hkdf_to_vec_spec _ _ _ _ (by simp only [UScalar.ofNatCore_val_eq,
    Nat.reduceMul, Nat.reduceLeDiff])) hk).2

/-- The epoch secret that `send_ct1_chunk` returns has 32 bytes. -/
theorem send_ct1_chunk_secret_length {R : Type} (i₁ : rand_1.rng.Rng R)
    (i₂ : rand_core_1.CryptoRng R) (self : v1.chunked.send_ct.HeaderReceived) (rng : R) {r}
    (h : v1.chunked.send_ct.HeaderReceived.send_ct1_chunk i₁ i₂ self rng = ok r) :
    r.1.2.2.secret.length = 32 := by
  simp only [v1.chunked.send_ct.HeaderReceived.send_ct1_chunk, Result.bind_eq_ok] at h
  obtain ⟨⟨⟨_, _, _⟩, _⟩, hsc, h⟩ := h
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
  obtain ⟨_, -, _, -, ⟨_, _⟩, -, h⟩ := h
  simp only [uncurry_apply_pair, Result.ok.injEq] at h
  subst h
  exact send_ct1_secret_length i₁ i₂ _ _ hsc

/-- The epoch secret that a successful `recv_ct2` returns has 32 bytes. -/
theorem recv_ct2_secret_length (self : v1.unchunked.send_ek.EkSentCt1Received)
    (ct2 mac : alloc.vec.Vec Std.U8) {p}
    (h : v1.unchunked.send_ek.EkSentCt1Received.recv_ct2 self ct2 mac = ok (.Ok p)) :
    p.2.secret.length = 32 := by
  simp only [v1.unchunked.send_ek.EkSentCt1Received.recv_ct2, Result.bind_eq_ok] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, ss1, hk, _, -, _, -, _, -, cf, -, h⟩ := h
  cases cf with
  | Break _ => exact (from_residual_ne_ok h).elim
  | Continue _ =>
    simp only [Result.bind_eq_ok] at h
    obtain ⟨_, -, v, hv, h⟩ := h
    simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at h
    subst h
    have h32 := (WP.post_of_ok (kdf.hkdf_to_vec_spec _ _ _ _ (by simp only [UScalar.ofNatCore_val_eq,
      Nat.reduceMul, Nat.reduceLeDiff])) hk).2
    simp only [alloc.vec.Vec.length, alloc.vec.Vec.deref, Slice.from_val,
      Slice.to_vec_U8_ok_val hv, UScalar.ofNatCore_val_eq] at h32 ⊢
    exact h32

/-- The epoch secret that `recv_ct2_chunk` returns when it completes has 32 bytes. -/
theorem recv_ct2_chunk_secret_length (self : v1.chunked.send_ek.EkSentCt1Received)
    (epoch : Std.U64) (chunk : encoding.Chunk) {st sec}
    (h : v1.chunked.send_ek.EkSentCt1Received.recv_ct2_chunk self epoch chunk =
      ok (.Ok (.Done (st, sec)))) :
    sec.secret.length = 32 := by
  simp only [v1.chunked.send_ek.EkSentCt1Received.recv_ct2_chunk, Result.bind_eq_ok] at h
  obtain ⟨_, -, _, -, o, -, h⟩ := h
  cases o with
  | none => simp only [Result.ok.injEq, core.result.Result.Ok.injEq, reduceCtorEq] at h
  | some _ =>
    simp only [Result.bind_eq_ok] at h
    obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, hr, cf, hcf, h⟩ := h
    cases cf with
    | Break _ => exact (from_residual_ne_ok h).elim
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      obtain ⟨_, _⟩ := val
      simp only [uncurry_apply_pair, Result.bind_eq_ok] at h
      obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h
      simp only [Result.ok.injEq, core.result.Result.Ok.injEq,
        v1.chunked.send_ek.EkSentCt1ReceivedRecvChunk.Done.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact recv_ct2_secret_length _ _ _ hr

/-- Every key that a successful `codeSend` returns has a 32-byte secret. -/
theorem codeSend_key_length : ∀ (s : States) (tape : List Std.U8) (out : v1.chunked.states.Send),
    codeSend s tape = some out → ∀ es ∈ out.key, es.secret.val.length = 32 := by
  intro s tape out h es hes
  obtain ⟨rng', hs⟩ := codeSend_some h
  have hk : out.key = some es := hes
  obtain ⟨st, -, rfl, -⟩ := send_key_epoch _ _ _ _ _ _ _ hs hk
  simp only [States.send, Result.bind_eq_ok, Prod.exists, uncurry_apply_pair, Result.ok.injEq,
    Prod.mk.injEq, core.result.Result.Ok.injEq, exists_eq_right_right] at hs
  obtain ⟨_, -, _, _, _, hc, rfl⟩ := hs
  simp only [Option.some.injEq] at hk
  subst hk
  exact send_ct1_chunk_secret_length _ _ _ _ hc

/-- Every key that a successful `codeRecv` returns has a 32-byte secret. -/
theorem codeRecv_key_length : ∀ (s : States) (msg : Message) (out : v1.chunked.states.Recv),
    codeRecv s msg = some out → ∀ es ∈ out.key, es.secret.val.length = 32 := by
  intro s msg out h es hes
  have hs := codeRecv_some h
  have hk : out.key = some es := hes
  obtain ⟨st, -, chunk, rfl, -, -, hp, -, -⟩ := recv_key_epoch _ _ _ _ hs hk
  simp only [States.recv, v1.chunked.send_ek.EkSentCt1Received.epoch, lift,
    core.cmp.impls.OrdU64.cmp, bind_ok, hp] at hs
  split at hs
  · simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs
    subst hs
    simp only [reduceCtorEq] at hk
  · simp only [Result.bind_eq_ok] at hs
    obtain ⟨_, hr, cf, hcf, hs⟩ := hs
    cases cf with
    | Break _ => exact (from_residual_ne_ok hs).elim
    | Continue val =>
      obtain rfl := branch_eq_continue hcf
      cases val with
      | StillReceiving _ =>
        simp only [Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        subst hs
        simp only [reduceCtorEq] at hk
      | Done p =>
        obtain ⟨_, _⟩ := p
        simp only [uncurry_apply_pair, Result.ok.injEq, core.result.Result.Ok.injEq] at hs
        subst hs
        simp only [Option.some.injEq] at hk
        subst hk
        exact recv_ct2_chunk_secret_length _ _ _ hr
  · simp only [Result.ok.injEq, reduceCtorEq] at hs

end SpqrBridge
