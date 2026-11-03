/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.CodeBound

/-!
# The contracts of step 2

The second review of W0 asked for these statements before W1 and W4 start. They fix what each
workstream proves, so that `fit` and `pick` cannot hide a mismatch with the code.

* Primitives (W1): where `fit` is the identity, and where each total field agrees with the
  code.
* Tape (W1): which bytes a `send` reads, and the elimination of unused sampling.
* Game invariant (W4): `CodeGameInv` holds initially, every query keeps it, and it bounds the
  epochs. At the receive boundary `nA + nB = Bud`, the epoch argument uses
  `epoch_bound_strong`, not `epoch_budget`.
* Upstream adapters (W2, W5): the facts that turn a closed issue of #782 into a field of
  `BridgeObligations`.
* Decoder (W2): on honest states, the decoder wrapper runs the code's own calls.

Every `sorry` in this file is a proof obligation of the workstream that the docstring names.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open OracleSpec OracleComp ENNReal
open OracleComp.ProgramLogic OracleComp.ProgramLogic.Relational
open SCKAScheme

/-! ## Primitives (W1) -/

/-- Key generation returns a 2400-byte `dk`, a 64-byte header and a 1152-byte vector, for any
randomness. So `fit` is the identity on all three. (W1.) -/
theorem keyGen_lengths (r : Bytes) :
    (codePrims.keyGen r).1.length = 2400 ∧ (codePrims.keyGen r).2.1.length = 64 ∧
      (codePrims.keyGen r).2.2.length = 1152 := by
  exact seededKeyGen_lengths r

/-- On a 64-byte header, `Encaps1` returns a 2080-byte state, a 960-byte `ct1` and a 32-byte
shared secret. (W1.) -/
theorem encaps1_lengths (hdr r : Bytes) (h : hdr.length = 64) :
    (codePrims.encaps1 hdr r).1.length = 2080 ∧ (codePrims.encaps1 hdr r).2.1.length = 960 ∧
      (codePrims.encaps1 hdr r).2.2.length = 32 := by
  exact seededEncaps1_lengths hdr r (by omega)

/-- Where the code's `encaps2` succeeds, `codePrims.encaps2` is its result, of 128 bytes. The
header argument is ignored, as in the code. (W1.) -/
theorem encaps2_agree (ek es ct2 : alloc.vec.Vec Std.U8) (hdr : Bytes)
    (h : incremental_mlkem768.encaps2 ek es = ok ct2) :
    codePrims.encaps2 es.val hdr ek.val = ct2.val ∧ ct2.length = 128 := by
  exact ⟨codePrims_agreesSeeded.encaps2 ek es ct2 hdr h, encaps2_ok_length ek es ct2 h⟩

/-- On a 2080-byte state and a 1152-byte vector, the code's `encaps2` succeeds. This is the
success part of #788. It says nothing about the value: see `docs/bridge-step2-plan.md`, "#788".
(W1, or a field if #788 is not done.) -/
theorem encaps2_ok (ek es : alloc.vec.Vec Std.U8) (hek : ek.length = 1152)
    (hes : es.length = 2080) : ∃ ct2, incremental_mlkem768.encaps2 ek es = ok ct2 := by
  exact exists_ok_of_spec (incremental_mlkem768.encaps2_spec ek es hek hes)

/-- Where the code's `decaps` succeeds, `codePrims.decaps` is its result, of 32 bytes. (W1.) -/
theorem decaps_agree (dk ct1 ct2 ss : alloc.vec.Vec Std.U8)
    (h : incremental_mlkem768.decaps dk ct1 ct2 = ok ss) :
    codePrims.decaps dk.val ct1.val ct2.val = ss.val ∧ ss.length = 32 := by
  exact ⟨codePrims_agreesSeeded.decaps dk ct1 ct2 ss h, decaps_ok_length dk ct1 ct2 ss h⟩

/-- On `u64` epochs, the total `KDF_OK` is the code's HKDF call. (W1.) -/
theorem kdfOK_agree (k : B 32) (ep : Std.U64) :
    (kdfOKTotal k ep.val).1 = crypto.hkdf (List.replicate 32 0#u8) k.1
      (Spqr.V1.Unchunked.SendCt.sckaKeyLabel ++ (core.num.U64.to_be_bytes ep).val) 32 := by
  rw [kdfOKTotal, codePrims_agreesSeeded.kdfOk k.1 ep]
  exact fit_of_length (crypto.hkdf_length _ _ _ _)

/-- On inputs that fit in a slice, the MAC has 32 bytes. So `fit 32` is the identity on the
MACs of `codeAuth`. (W1.) -/
theorem mac_length (k d : Bytes) (hk : k.length ≤ Std.Usize.max) (hd : d.length ≤ Std.Usize.max) :
    (codePrims.mac k d).length = 32 := by
  sorry

/-! ## Tape (W1) -/

/-- The states whose `send` samples: key generation and `Encaps1`. -/
def Samples : States → Prop
  | .KeysUnsampled _ | .HeaderReceived _ => True
  | _ => False

/-- A `send` that does not sample ignores the tape. (W1.) -/
theorem codeSend_tape_irrel (s : States) (hs : ¬ Samples s) (t t' : List Std.U8) :
    codeSend s t = codeSend s t' := by
  refine codeSend_congr s s t t' (dropRng_send_irrel s ?_ ?_ t t')
  · rintro st rfl; exact hs trivial
  · rintro st rfl; exact hs trivial

/-- A `send` reads at most the first 64 bytes of a tape of at least 64 bytes. This is the
adapter between the fresh 64-byte tape of `codeScheme` and the single infinite tape of #787:
the result does not change when bytes are appended. (W1.) -/
theorem codeSend_prefix (s : States) (t t' : List Std.U8) (ht : 64 ≤ t.length)
    (ht' : 64 ≤ t'.length) (h : t.take 64 = t'.take 64) : codeSend s t = codeSend s t' := by
  exact codeSend_congr s s t t' (dropRng_send_prefix s t t' ht ht' h)

/-- Sampling a tape and ignoring it couples with a pure value. Used in the branches of
`Chunked.send` that do not sample. (W1.) -/
theorem relTriple_sampleTape_pure {α β : Type} (f : B 64 → α) (b : β) (R : α → β → Prop)
    (h : ∀ t, R (f t) b) :
    RelTriple (do let t ← sampleTape; pure (f t)) (pure b : ProbComp β) R := by
  exact relTriple_bind_pure_right sampleTape f b R h

/-! ## Game invariant (W4) -/

/-- The initial game state of the code satisfies `CodeGameInv`. (W4.) -/
theorem codeGameInv_init (k : InitKey) :
    CodeGameInv (initGameState (initAState k) (initBState k)) :=
  codeGameInvRaw_init k

/-- Every correctness query keeps `CodeGameInv`, including failed sends, key-length refusals
and stale deliveries. (W4.) -/
theorem codeGameInv_pres (sampleInitKey : ProbComp InitKey) :
    QueryImpl.PreservesInv (sckaCorrectnessImpl (codeScheme sampleInitKey)) CodeGameInv :=
  codeGameInvRaw_pres sampleInitKey

/-- `CodeGameInv` bounds the epochs by the send count: a party epoch by `nA + nB + 1`, and a
recorded message's epoch by `nA + nB`. At `nA + nB ≤ 2^64 - 2`, the second bound gives every
recorded message epoch plus one below `2^64`. (W4, from `epoch_bound_strong`.) -/
theorem codeGameInv_epochs (s : GameState States States (B 32) Message) (h : CodeGameInv s) :
    s.stA.epochOf.val ≤ s.nA + s.nB + 1 ∧ s.stB.epochOf.val ≤ s.nA + s.nB + 1 ∧
      ∀ n m t, (s.msgA n = some (m, t) ∨ s.msgB n = some (m, t)) →
        m.epoch.val ≤ s.nA + s.nB :=
  codeGameInvRaw_epochs s h

/-! ## Upstream adapters (W2, W5) -/

/-- A reachable code state refines some machine state. This adapts #784's invariant to
`ReachParty`. It follows from `init_refines` and `run_refines`. (W2.) -/
theorem reachParty_refines (hsz : MlkemSizes) (s : States) (n : ℕ) (h : ReachParty s n) :
    ∃ σ, Refines s σ := by
  sorry

/-- A stale message leaves the state unchanged and outputs no key. This is the stale half of
the split that `recv_complete` needs: #785 bounds the state epoch, the bridge bounds the
message epoch, and a stale message needs no headroom. -/
theorem codeRecv_stale (s : States) (msg : Message) (h : msg.epoch.val < s.epochOf.val) :
    codeRecv s msg = some { key := none, state := s } := by
  simp only [codeRecv, recv_of_lt s msg h]
  rfl

/-! ## Decoder (W2) -/

/-- On an honest decoder state, the wrapper's `addChunk` of an honest chunk is the code's
`add_chunk`, which succeeds. (W2, from `add_chunk_ok`.) -/
theorem polyStreamDecoder_addChunk_code {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16)
    (cd : L2.Codec M K) (d : (L2.polyStreamDecoder K hKN cd).D) (p : M) (i : ℕ)
    (hd : (L2.polyStreamDecoder K hKN cd).Honest d p) :
    ∃ d', encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.add_chunk d
        (L2.toChunk ((L2.ecp K hK hKN cd).encode p i).1 ((L2.ecp K hK hKN cd).encode p i).2) =
          ok d' ∧
      (L2.polyStreamDecoder K hKN cd).addChunk d ((L2.ecp K hK hKN cd).encode p i) = d' := by
  sorry

/-- On an honest decoder state, the code's `decoded_message` succeeds, and the wrapper's
`decodedPayload` is its parsed result. (W2, from `decoded_message_ok`.) -/
theorem polyStreamDecoder_decoded_code {M : Type} (K : ℕ) (hKN : K ≤ 2 ^ 16)
    (cd : L2.Codec M K) (d : (L2.polyStreamDecoder K hKN cd).D) (p : M)
    (hd : (L2.polyStreamDecoder K hKN cd).Honest d p) :
    ∃ r, encoding.polynomial.PolyDecoder.Insts.SpqrEncodingDecoder.decoded_message d = ok r ∧
      (L2.polyStreamDecoder K hKN cd).decodedPayload d =
        r.bind fun v => cd.parse (L2.unflatten K v.val) := by
  sorry

end SpqrBridge
