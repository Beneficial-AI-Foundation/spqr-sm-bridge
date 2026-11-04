/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import Spqr.Specs.IncrementalMlkem768.Generate
import Spqr.Specs.IncrementalMlkem768.Encaps1
import Spqr.Auxiliary.Aeneas.Result
import Spqr.Auxiliary.Aeneas.Scalar

/-!
# Seeded key generation and `Encaps1`, for any RNG

`generate_spec` and `encaps1_spec` assume that `fill_bytes` never fails. A successful call
needs less: it already shows that the one `fill_bytes` call succeeded. `generate_ok_seed` and
`encaps1_ok_msg` give the FIPS 203 values of a successful call with any RNG. The proofs replace
the RNG with one whose `fill_bytes` returns the observed result, so the specs apply.

`toU8List_getD` reads a FIPS 203 byte vector back from its list.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr

/-- An RNG whose `fill_bytes` always returns `(r, s)`. -/
def constRng {R : Type} (i : rand_1.rng.Rng R) (r : R) (s : Slice Std.U8) : rand_1.rng.Rng R :=
  ⟨{ i.rand_core_1RngCoreInst with fill_bytes := fun _ _ => ok (r, s) }⟩

/-- Reading byte `j` of a FIPS 203 byte vector from its list. -/
theorem toU8List_getD {N : ℕ} (b : Fin N → UInt8) (j : Fin N) :
    ((Fips203.Refinement.toU8List b).getD j.val 0#u8).toUInt8 = b j := by
  rw [List.getD_eq_getElem _ _ (by simp only [Fips203.Refinement.toU8List_length, j.isLt]),
    Fips203.Refinement.toU8List_getElem, U8.toUInt8_ofUInt8]

/-- A successful `generate`, with any RNG, returns the FIPS 203 key pair of some seed. -/
theorem generate_ok_seed {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (rng rng' : R) (k : incremental_mlkem768.Keys)
    (h : incremental_mlkem768.generate i₁ i₂ rng = ok (k, rng')) :
    ∃ seed : Fin 64 → UInt8,
      k.dk.val = Fips203.Refinement.keyPairList seed ∧
      k.hdr.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes seed) ∧
      k.ek.val = Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes seed) := by
  have h0 := h
  simp only [incremental_mlkem768.generate, lift, Array.to_slice_mut, bind_ok,
    uncurry_apply_pair, Result.bind_eq_ok] at h0
  obtain ⟨⟨r1, s1⟩, hf, -⟩ := h0
  have h' : incremental_mlkem768.generate (constRng i₁ r1 s1) i₂ rng = ok (k, rng') := by
    rw [← h]
    simp only [incremental_mlkem768.generate, lift, Array.to_slice_mut, uncurry_apply_pair,
      bind_ok, constRng, hf]
  obtain ⟨⟨seed, hdk, hek, hhdr⟩, -⟩ :=
    WP.post_of_ok (incremental_mlkem768.generate_spec (constRng i₁ r1 s1) i₂ rng
      (fun _ _ => by simp only [constRng, WP.spec_ok])) h'
  exact ⟨seed, hdk, hhdr, hek⟩

/-- A successful `encaps1` had a header of at least 64 bytes: `encapsulate1` rejects shorter
ones, and `encaps1` panics on the rejection. -/
theorem encaps1_ok_hdr {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (hdr : alloc.vec.Vec Std.U8) (rng rng' : R) (ct1 es ss : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng')) :
    64 ≤ hdr.val.length := by
  have h0 := h
  simp only [incremental_mlkem768.encaps1, lift, Array.to_slice_mut, bind_ok,
    uncurry_apply_pair, Result.bind_eq_ok] at h0
  obtain ⟨⟨r1, s1⟩, -, h1⟩ := h0
  simp only [uncurry_apply_pair, alloc.vec.Vec.deref_mut, Result.bind_eq_ok] at h1
  obtain ⟨_, -, _, -, _, -, _, -, s2, hs2, ⟨c1, s5, s6⟩, he, h2⟩ := h1
  simp only [uncurry_apply_pair, Result.bind_eq_ok] at h2
  obtain ⟨c, hc, -⟩ := h2
  simp only [alloc.vec.Vec.as_slice, Result.ok.injEq] at hs2
  subst hs2
  by_contra hlt
  rw [Fips203.Refinement.encapsulate1_short_header _ _ _ _ (by
    simp only [Slice.length, Slice.from_val]; omega)] at he
  simp only [Result.ok.injEq, Prod.mk.injEq] at he
  obtain ⟨rfl, -, -⟩ := he
  simp only [core.result.Result.expect] at hc
  exact fail_not_ok hc

/-- A successful `encaps1`, with any RNG, returns the FIPS 203 round 1 values of some message. -/
theorem encaps1_ok_msg {R : Type} (i₁ : rand_1.rng.Rng R) (i₂ : rand_core_1.CryptoRng R)
    (hdr : alloc.vec.Vec Std.U8) (rng rng' : R) (ct1 es ss : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.encaps1 i₁ i₂ hdr rng = ok ((ct1, es, ss), rng')) :
    ∃ (h64 : 64 ≤ hdr.val.length) (m : Fin 32 → UInt8),
      ct1.val = Fips203.Refinement.ct1List hdr.val h64 m ∧
      es.val = Fips203.Refinement.toU8List (Fips203.Refinement.stateOut hdr.val h64 m) ∧
      ss.val = Fips203.Refinement.toU8List (Fips203.Refinement.ssOut hdr.val h64 m) := by
  have h64 := encaps1_ok_hdr i₁ i₂ hdr rng rng' ct1 es ss h
  have h0 := h
  simp only [incremental_mlkem768.encaps1, lift, Array.to_slice_mut, bind_ok,
    uncurry_apply_pair, Result.bind_eq_ok] at h0
  obtain ⟨⟨r1, s1⟩, hf, -⟩ := h0
  have h' : incremental_mlkem768.encaps1 (constRng i₁ r1 s1) i₂ hdr rng =
      ok ((ct1, es, ss), rng') := by
    rw [← h]
    simp only [incremental_mlkem768.encaps1, lift, Array.to_slice_mut, uncurry_apply_pair,
      bind_ok, constRng, hf]
  obtain ⟨⟨m, h1, h2, h3⟩, -⟩ :=
    WP.post_of_ok (incremental_mlkem768.encaps1_spec (constRng i₁ r1 s1) i₂ hdr rng h64
      (fun _ _ => by simp only [constRng, WP.spec_ok])) h'
  exact ⟨h64, m, h1, h2, h3⟩

end SpqrBridge
