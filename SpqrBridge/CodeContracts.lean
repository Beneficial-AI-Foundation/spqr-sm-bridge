/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.CodeBound

/-!
# Contracts between the total definitions and the code

These statements make sure that `fit` and `pick` hide no mismatch with the code.

* Primitives: where `fit` is the identity, and where each total field agrees with the
  code.
* Game invariant: `CodeGameInv` holds initially, every query keeps it, and it bounds the
  epochs. At the receive boundary `nA + nB = Bud`, the epoch argument uses
  `epoch_bound_strong`, not `epoch_budget`.
* Upstream adapters: the facts that connect the issues of SparsePostQuantumRatchet-verify to the
  fields of `BridgeObligations`.
* Decoder: on honest states, the decoder wrapper runs the code's own calls.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open SCKAScheme

/-! ## Primitives -/

/-- Key generation returns a 2400-byte `dk`, a 64-byte header and a 1152-byte vector, for any
randomness. So `fit` is the identity on all three. -/
theorem keyGen_lengths (r : Bytes) :
    (codePrims.keyGen r).1.length = 2400 ∧ (codePrims.keyGen r).2.1.length = 64 ∧
      (codePrims.keyGen r).2.2.length = 1152 := by
  exact seededKeyGen_lengths r

/-- On a 64-byte header, `Encaps1` returns a 2080-byte state, a 960-byte `ct1` and a 32-byte
shared secret. -/
theorem encaps1_lengths (hdr r : Bytes) (h : hdr.length = 64) :
    (codePrims.encaps1 hdr r).1.length = 2080 ∧ (codePrims.encaps1 hdr r).2.1.length = 960 ∧
      (codePrims.encaps1 hdr r).2.2.length = 32 := by
  exact seededEncaps1_lengths hdr r (by omega)

/-- Where the code's `encaps2` succeeds, `codePrims.encaps2` is its result, of 128 bytes. The
header argument is ignored, as in the code. -/
theorem encaps2_agree (ek es ct2 : alloc.vec.Vec Std.U8) (hdr : Bytes)
    (h : incremental_mlkem768.encaps2 ek es = ok ct2) :
    codePrims.encaps2 es.val hdr ek.val = ct2.val ∧ ct2.length = 128 := by
  exact ⟨codePrims_agreesSeeded.encaps2 ek es ct2 hdr h, encaps2_ok_length ek es ct2 h⟩

/-- Let `ek.length = 1152` and `es.length = 2080`. Then `incremental_mlkem768.encaps2 ek es = ok ct2`
for some `ct2`. The statement gives no property of `ct2`. This is the success part of #788. -/
theorem encaps2_ok (ek es : alloc.vec.Vec Std.U8) (hek : ek.length = 1152)
    (hes : es.length = 2080) : ∃ ct2, incremental_mlkem768.encaps2 ek es = ok ct2 := by
  exact exists_ok_of_spec (incremental_mlkem768.encaps2_spec ek es hek hes)

/-- Where the code's `decaps` succeeds, `codePrims.decaps` is its result, of 32 bytes. -/
theorem decaps_agree (dk ct1 ct2 ss : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.decaps dk ct1 ct2 = ok ss) :
    codePrims.decaps dk.val ct1.val ct2.val = ss.val ∧ ss.length = 32 := by
  exact ⟨codePrims_agreesSeeded.decaps dk ct1 ct2 ss h, decaps_ok_length dk ct1 ct2 ss h⟩

/-- On `u64` epochs, the total `KDF_OK` is the code's HKDF call. -/
theorem kdfOK_agree (k : B 32) (ep : Std.U64) :
    (kdfOKTotal k ep.val).1 = crypto.hkdf (List.replicate 32 0#u8) k.1
      (Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++ (core.num.U64.to_be_bytes ep).val) 32 := by
  rw [kdfOKTotal, codePrims_agreesSeeded.kdfOk k.1 ep]
  exact fit_of_length (crypto.hkdf_length _ _ _ _)

/-- Let `k.length ≤ u32::MAX` and `d.length ≤ u32::MAX`. Then `codePrims.mac k d` has 32 bytes.
The two bounds are the premises of the HMAC axiom `hmac_sha256_tag32_spec`. -/
theorem mac_length (k d : Bytes) (hk : k.length ≤ Std.U32.max) (hd : d.length ≤ Std.U32.max) :
    (codePrims.mac k d).length = 32 :=
  mac_length_u32 k d hk hd

/-! ## Game invariant -/

/-- The initial game state of the code satisfies `CodeGameInv`. -/
theorem codeGameInv_init (k : InitKey) :
    CodeGameInv (initGameState (initAState k) (initBState k)) :=
  codeGameInvRaw_init k

/-- Every correctness query keeps `CodeGameInv`, including failed sends, key-length refusals
and stale deliveries. -/
theorem codeGameInv_pres (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv (sckaCorrectnessImpl (codeScheme sampleInitKey)) CodeGameInv :=
  codeGameInvRaw_pres sampleInitKey

/-- Let `s : GameState States States (B 32) Message` satisfy `CodeGameInv s`. Then
`s.stA.epochOf.val ≤ s.nA + s.nB + 1` and `s.stB.epochOf.val ≤ s.nA + s.nB + 1`. For every `n`,
`m` and `t`, if `s.msgA n = some (m, t)` or `s.msgB n = some (m, t)`, then
`m.epoch.val ≤ s.nA + s.nB`.

Consequence: if `s.nA + s.nB ≤ 2^64 - 2`, then `m.epoch.val + 1 < 2^64` for every recorded
message `m`. -/
theorem codeGameInv_epochs (s : GameState States States (B 32) Message) (h : CodeGameInv s) :
    s.stA.epochOf.val ≤ s.nA + s.nB + 1 ∧ s.stB.epochOf.val ≤ s.nA + s.nB + 1 ∧
      ∀ n m t, (s.msgA n = some (m, t) ∨ s.msgB n = some (m, t)) →
        m.epoch.val ≤ s.nA + s.nB :=
  codeGameInvRaw_epochs s h

/-! ## Upstream adapters -/

/-- Assume `MlkemSizes`. Let `ReachParty s n`. Then `Refines s σ` for some `σ`. -/
theorem reachParty_refines (hsz : MlkemSizes) (s : States) (n : ℕ) (h : ReachParty s n) :
    ∃ σ, Refines s σ := by
  obtain ⟨P, hP⟩ := codeAgrees_exists
  obtain ⟨sA, sB, mA, mB, hr, hs⟩ := h
  suffices hAB : (∃ σ, Refines sA σ) ∧ ∃ σ, Refines sB σ by
    rcases hs with rfl | rfl
    exacts [hAB.1, hAB.2]
  have hsend : ∀ (s : States) (buf : Slice Std.U8) (out : v1.chunked.states.Send),
      codeSend s buf = some out → (∃ σ, Refines s σ) → ∃ σ, Refines out.state σ := by
    rintro s buf out hout ⟨σ, hσ⟩
    obtain ⟨rng', hs'⟩ := codeSend_some hout
    obtain ⟨r, hr', -⟩ :=
      send_refines P hP (fixedRng buf) (fixedCrypto buf) s σ hσ () rng' out hs'
    exact ⟨_, hr'⟩
  have hrecv : ∀ (s : States) (msg : Message) (out : v1.chunked.states.Recv),
      codeRecv s msg = some out → (∃ σ, Refines s σ) → ∃ σ, Refines out.state σ := by
    rintro s msg out hout ⟨σ, hσ⟩
    obtain ⟨σ', -, hσ'⟩ := recv_refines P hP hsz s σ hσ msg out (codeRecv_some hout)
    exact ⟨σ', hσ'⟩
  clear hs
  induction hr with
  | init k =>
    exact ⟨⟨_, (init_refines P hP k.1).1 _ (init_a_eq k)⟩,
      ⟨_, (init_refines P hP k.1).2 _ (init_b_eq k)⟩⟩
  | sendA buf out _ _ hout ih => exact ⟨hsend _ buf out hout ih.1, ih.2⟩
  | sendB buf out _ _ hout ih => exact ⟨ih.1, hsend _ buf out hout ih.2⟩
  | recvA m out _ _ hout ih => exact ⟨hrecv _ m out hout ih.1, ih.2⟩
  | recvB m out _ _ hout ih => exact ⟨ih.1, hrecv _ m out hout ih.2⟩

/-- Let `msg.epoch < s.epochOf`. Then `codeRecv s msg = some { key := none, state := s }`. The
statement has no bound on the epochs. -/
theorem codeRecv_stale (s : States) (msg : Message) (h : msg.epoch.val < s.epochOf.val) :
    codeRecv s msg = some { key := none, state := s } := by
  simp only [codeRecv, recv_of_lt s msg h]
  rfl

/-! ## Decoder -/

/-- Let `hK : 0 < K`, `hKN : K ≤ 2 ^ 16` and `cd : L2.Codec M K`. Let `d` be honest for `p` in
`L2.polyStreamDecoder K hKN cd`, and let `c = (L2.ecp K hK hKN cd).encode p i`. Then the code's
`add_chunk d (L2.toChunk c.1 c.2)` returns `ok d'` for some `d'`, and `addChunk d c = d'` in
`L2.polyStreamDecoder`. -/
theorem polyStreamDecoder_addChunk_code {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16)
    (cd : L2.Codec M K) (d : (L2.polyStreamDecoder K hKN cd).D) (p : M) (i : ℕ)
    (hd : (L2.polyStreamDecoder K hKN cd).Honest d p) :
    ∃ d', encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d
        (L2.toChunk ((L2.ecp K hK hKN cd).encode p i).1 ((L2.ecp K hK hKN cd).encode p i).2) =
          ok d' ∧
      (L2.polyStreamDecoder K hKN cd).addChunk d ((L2.ecp K hK hKN cd).encode p i) = d' := by
  have hidx : ((L2.ecp K hK hKN cd).encode p i).1 < 2 ^ 16 := by
    simp only [ErasureCodePayload.encode, ErasureCodePayload.counterIndex, L2.ecp, L2.ec]
    exact Nat.mod_lt _ (by norm_num)
  obtain ⟨d', hd'⟩ := L2.add_chunk_ok (cd.ser p) d hd _ hidx ((L2.ecp K hK hKN cd).encode p i).2
  refine ⟨d', hd', ?_⟩
  simp only [L2.polyStreamDecoder, hd']
  rfl

/-- Let `hKN : K ≤ 2 ^ 16` and `cd : L2.Codec M K`. Let `d` be honest for `p` in
`L2.polyStreamDecoder K hKN cd`. Then the code's `decoded_message d` returns `ok r` for some `r`,
and `decodedPayload d = r.bind fun v => cd.parse (L2.unflatten K v.val)` in
`L2.polyStreamDecoder`. -/
theorem polyStreamDecoder_decoded_code {M : Type} (K : ℕ) (hKN : K ≤ 2 ^ 16)
    (cd : L2.Codec M K) (d : (L2.polyStreamDecoder K hKN cd).D) (p : M)
    (hd : (L2.polyStreamDecoder K hKN cd).Honest d p) :
    ∃ r, encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d = ok r ∧
      (L2.polyStreamDecoder K hKN cd).decodedPayload d =
        r.bind fun v => cd.parse (L2.unflatten K v.val) := by
  obtain ⟨r, hr⟩ := L2.decoded_message_ok hKN (cd.ser p) d hd
  refine ⟨r, hr, ?_⟩
  simp only [L2.polyStreamDecoder, hr]
  rcases r with _ | v <;> rfl

end SpqrBridge
