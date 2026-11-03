/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE-APACHE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.CodePrims
import SpqrBridge.Adapter
import Spqr.Specs.IncrementalMlkem768.EkMatchesHeader
import Spqr.Auxiliary.Aeneas.Slice
import Spqr.Specs.IncrementalMlkem768.Encaps2

/-!
# Facts about `codePrims`

Lengths of the seeded key generation and `Encaps1`, and the code's `ek` check on generated keys.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr Braid

/-- `fit` on a list of the right length, as a subtype equation. -/
theorem fit_eq {n : ℕ} {l : List Std.U8} (h : l.length = n) : fit n l = ⟨l, h⟩ :=
  Subtype.ext (fit_of_length h)

/-- The seeded key generation has the code's lengths: 2400, 64 and 1152 bytes. -/
theorem seededKeyGen_lengths (r : Bytes) :
    (seededKeyGen r).1.length = 2400 ∧ (seededKeyGen r).2.1.length = 64 ∧
      (seededKeyGen r).2.2.length = 1152 := by
  simp only [seededKeyGen, Fips203.Refinement.keyPairList_length,
    Fips203.Refinement.toU8List_length, and_self]

/-- On a header of at least 64 bytes, the seeded `Encaps1` has the code's lengths. -/
theorem seededEncaps1_lengths (hdr r : Bytes) (h : 64 ≤ hdr.length) :
    (seededEncaps1 hdr r).1.length = 2080 ∧ (seededEncaps1 hdr r).2.1.length = 960 ∧
      (seededEncaps1 hdr r).2.2.length = 32 := by
  simp only [seededEncaps1, h, _root_.dite_true, Fips203.Refinement.toU8List_length,
    Fips203.Refinement.ct1List_length]
  exact ⟨rfl, trivial, trivial⟩

/-- `codePrims.ekMatches` accepts a generated key: the code's `ek_matches_header` does. -/
theorem codePrims_ekMatches_generated (seed : Fin 64 → UInt8) :
    codePrims.ekMatches (Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes seed))
      (Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes seed)) = true := by
  let ek : alloc.vec.Vec Std.U8 :=
    alloc.vec.Vec.from (Fips203.Refinement.toU8List (Fips203.Refinement.pk2Bytes seed))
      (by simp only [Fips203.Refinement.toU8List_length]; scalar_tac)
  let hdr : alloc.vec.Vec Std.U8 :=
    alloc.vec.Vec.from (Fips203.Refinement.toU8List (Fips203.Refinement.pk1Bytes seed))
      (by simp only [Fips203.Refinement.toU8List_length]; scalar_tac)
  have hs := incremental_mlkem768.ek_matches_header_generated seed ek hdr
    (alloc.vec.Vec.from_val _ _) (alloc.vec.Vec.from_val _ _)
  obtain ⟨b, hb⟩ := exists_ok_of_spec hs
  have hb' := WP.post_of_ok hs hb
  have := codePrims_agreesSeeded.ekMatches ek hdr b hb
  rw [hb', alloc.vec.Vec.from_val, alloc.vec.Vec.from_val] at this
  exact this

/-- Cutting a list of `32 K` elements into `K` blocks of 32 and joining them gives the list. -/
theorem flatten_ofFn_blocks {α : Type} (K : ℕ) (l : List α) (h : l.length = 32 * K) :
    (List.ofFn fun i : Fin K => (l.drop (32 * i.val)).take 32).flatten = l := by
  induction K generalizing l with
  | zero => simp_all only [Nat.mul_zero, List.length_eq_zero_iff, List.ofFn_zero,
      List.flatten_nil]
  | succ K ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    have hd : (List.ofFn fun i : Fin K => (l.drop (32 * (i.val + 1))).take 32) =
        List.ofFn fun i : Fin K => ((l.drop 32).drop (32 * i.val)).take 32 := by
      congr 1; funext i; rw [List.drop_drop]; congr 2; ring
    simp only [Fin.val_zero, Nat.mul_zero, List.drop_zero, Fin.val_succ]
    rw [hd, ih (l.drop 32) (by rw [List.length_drop, h]; ring_nf; omega), List.take_append_drop]

/-- A successful `encaps2` returns 128 bytes: the `Ciphertext2` array. -/
theorem encaps2_ok_length (ek es ct2 : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.encaps2 ek es = ok ct2) : ct2.length = 128 := by
  simp only [incremental_mlkem768.encaps2, lift, bind_ok, Result.bind_eq_ok] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, c, -, hv⟩ := h
  rw [alloc.vec.Vec.length, Slice.to_vec_U8_ok_val hv, Array.val_to_slice,
    Aeneas.Std.Array.length_eq]
  rfl

/-- A successful `decaps` returns 32 bytes: the shared-secret array. -/
theorem decaps_ok_length (dk ct1 ct2 ss : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.decaps dk ct1 ct2 = ok ss) : ss.length = 32 := by
  simp only [incremental_mlkem768.decaps, lift, bind_ok, Result.bind_eq_ok] at h
  obtain ⟨_, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, _, -, c, -, hv⟩ := h
  rw [alloc.vec.Vec.length, Slice.to_vec_U8_ok_val hv, Array.val_to_slice,
    Aeneas.Std.Array.length_eq]
  rfl

/-- On inputs of at most `u32::MAX` bytes, the MAC has 32 bytes. This is the bound of the HMAC
axiom `hmac_sha256_tag32_spec`; the contract `mac_length` states `usize::MAX`, which no axiom
covers. -/
theorem mac_length_u32 (k d : Bytes) (hk : k.length ≤ Std.U32.max) (hd : d.length ≤ Std.U32.max) :
    (codePrims.mac k d).length = 32 := by
  have hu : Std.U32.max ≤ Std.Usize.max := by scalar_tac
  let ks : Slice Std.U8 := Slice.from k (le_trans hk hu)
  let ds : Slice Std.U8 := Slice.from d (le_trans hd hu)
  have hs := libcrux_hmac.hmac_sha256_tag32_spec ks ds
    (by simp only [ks, Slice.length, Slice.from_val]; exact hk)
    (by simp only [ds, Slice.length, Slice.from_val]; exact hd)
  obtain ⟨t, ht⟩ := exists_ok_of_spec hs
  have := codePrims_agreesSeeded.mac ks ds t ht
  simp only [ks, ds, Slice.from_val] at this
  have hl := WP.post_of_ok hs ht
  rw [this]
  exact hl

end SpqrBridge
