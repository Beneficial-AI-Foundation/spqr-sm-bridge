/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.ChunkedRecvAll
import SpqrBridge.NextChunkWrap

/-!
# The send arms of `Braid` → `Chunked`

`sendRel_of_braid` reduces the send obligation `SendRel RA RM` for one buffer to a step of the
abstract machine: `Braid.send` on the bytes that `fill_bytes` returned agrees with the result of
`Chunked.send` (`SendAgree`). The code side follows from the `BridgeObligations` fields
`send_total` and `send_refines_bytes`, and from the theorem `codeSend_key_length`. The encoder
steps use the theorem `next_chunk_wrap`.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming

/-- `Braid` payloads and secure-messaging payloads correspond by constructor. -/
def BPayloadRel : Braid.Payload encoding.Chunk → SPQR.Chunked.Payload L2.Sym → Prop
  | .none, .none => True
  | .hdr c, .hdr x => x = chunkOfCode c
  | .ek c, .ek x => x = chunkOfCode c
  | .ekCt1Ack c, .ekCt1Ack x => x = chunkOfCode c
  | .ct1Ack, .ct1Ack => True
  | .ct1 c, .ct1 x => x = chunkOfCode c
  | .ct2 c, .ct2 x => x = chunkOfCode c
  | _, _ => False

/-- A code message whose `Braid` image corresponds to a secure-messaging message is related to
it by `RM`. -/
theorem RM_of_absMsg (m : Message) (m' : SPQR.Chunked.Message L2.Sym)
    (he : (absMsg m).epoch = m'.epoch) (hp : BPayloadRel (absMsg m).payload m'.payload) :
    RM m m' := by
  refine ⟨he, ?_⟩
  obtain ⟨ep, p⟩ := m
  obtain ⟨ep', p'⟩ := m'
  rcases p with _ | _ | _ | _ | (_ | _) | _ | _ <;> rcases p' with _ | _ | _ | _ | _ | _ | _ <;>
    simp only [absMsg, BPayloadRel] at hp <;> simp only [PayloadRel, hp]

/-- `Braid.send` agrees with a result of `Chunked.send`: related states, corresponding messages,
the same key, and the report `epoch - 1`. -/
def SendAgree (b : BState × Msg encoding.Chunk × Option Key)
    (res : SPQR.Chunked.SendResult codeParams Braid.Auth) : Prop :=
  ChunkedRel b.1 res.state ∧ b.2.1.epoch = res.msg.epoch ∧
    BPayloadRel b.2.1.payload res.msg.payload ∧
    b.2.2 = res.outputKey.map (fun k => (k.1, k.2.1)) ∧ res.sendingEpoch = b.2.1.epoch - 1

/-- Assume `BridgeObligations`. Let `ReachParty s n`, `Refines s σ`, `s.epochOf.val + 1 < 2 ^ 64`
and `buf.length = sendLen s`. If `SendAgree (Braid.send codePrims σ buf.val) res`, then
`SendRel RA RM` relates `sendStep s buf` and
`some (res.outputKey, res.msg, res.sendingEpoch, res.state)`. -/
theorem sendRel_of_braid (hB : BridgeObligations) (s : States) (n : ℕ) (σ : BState)
    (hreach : ReachParty s n) (hσ : Refines s σ) (hep : s.epochOf.val + 1 < 2 ^ 64)
    (buf : Slice Std.U8) (hbuf : buf.length = sendLen s)
    (res : SPQR.Chunked.SendResult codeParams Braid.Auth)
    (h : SendAgree (Braid.send codePrims σ buf.val) res) :
    SendRel RA RM (sendStep s buf) (some (res.outputKey, res.msg, res.sendingEpoch, res.state)) := by
  obtain ⟨out, hout⟩ := hB.send_total s n buf hreach hep hbuf
  obtain ⟨hst, hmsg, hkey⟩ := hB.send_refines_bytes s n σ buf out hreach hep hbuf hσ hout
  have hlen := codeSend_key_length s buf out hout
  replace hout : outOf (sendRest s buf) = some out := hout
  obtain ⟨hrel, he, hp, hk, hse⟩ := h
  rw [← hmsg] at he hp hse
  rw [← hkey] at hk
  have hRM := RM_of_absMsg out.msg res.msg he hp
  simp only [sendStep, stepOf, hout, Option.bind_eq_bind, Option.bind_some]
  rcases hko : out.key with _ | es
  · rw [hko] at hk
    simp only [keyOf, Option.bind_some, Option.pure_def, SendRel]
    refine ⟨?_, hRM, ?_, ⟨_, hst, hrel⟩⟩
    · rcases hrk : res.outputKey with _ | ⟨e, x⟩
      · rfl
      · rw [hrk] at hk; simp at hk
    · rw [hse]; rfl
  · have h32 := hlen es (by rw [hko]; rfl)
    rw [hko] at hk
    simp only [keyOf, h32, ↓reduceDIte, Option.bind_some, Option.pure_def, SendRel]
    refine ⟨?_, hRM, ?_, ⟨_, hst, hrel⟩⟩
    · rcases hrk : res.outputKey with _ | ⟨e, x⟩
      · rw [hrk] at hk; simp at hk
      · rw [hrk] at hk
        simp only [Option.map_some, Option.some.injEq, absKey, Prod.mk.injEq] at hk
        congr 2
        · exact hk.1.symm
        · exact Subtype.ext hk.2.symm
    · rw [hse]; rfl

/-- Let `K` be 3, 5, 30 or 36, and let `EncRel K hK hKN cd enc es`. Then
`codePrims.nextChunk enc = (c, enc')` for some `c` and `enc'` with
`es.nextChunk.1 = chunkOfCode c` and `EncRel K hK hKN cd enc' es.nextChunk.2`. -/
theorem encStep {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16)
    (cd : L2.Codec M K) (hKadm : K = 3 ∨ K = 5 ∨ K = 30 ∨ K = 36)
    (enc : encoding.polynomial.PolyEncoder) (es : EncoderState M L2.Sym)
    (h : EncRel K hK hKN cd enc es) :
    ∃ c enc', codePrims.nextChunk enc = (c, enc') ∧ es.nextChunk.1 = chunkOfCode c ∧
      EncRel K hK hKN cd enc' es.nextChunk.2 := by
  obtain ⟨hecp, hinv, hidx⟩ := h
  obtain ⟨c, enc', hnc, hc, hinv', hidx'⟩ :=
    next_chunk_wrap K hK hKN cd es.payload es.nextIndex enc hKadm hinv hidx
  refine ⟨c, enc', pick_eq_of hnc fun _ h' => ok_inj h' hnc, ?_, hecp, hinv', hidx'⟩
  simp only [EncoderState.nextChunk, hecp]
  exact hc.symm

/-- Let `ChunkedRel σ st`, and let `st` be neither `keysUnsampled` nor `headerReceived`. Then
`Chunked.send` on `st` is `pure res` for some `res`, and `SendAgree (Braid.send codePrims σ r) res`
for every `r`. -/
theorem braid_send_pure (σ : BState) (st : SMState)
    (hrel : ChunkedRel σ st) (hs : ¬ (∃ c, st = .keysUnsampled c) ∧ ¬ ∃ c d, st = .headerReceived c d) :
    ∃ res, SPQR.Chunked.send codeParams codeAuth st = pure res ∧
      ∀ r, SendAgree (Braid.send codePrims σ r) res := by
  obtain ⟨hmk, hst⟩ := hrel
  rcases st with ⟨ep, a⟩ | ⟨⟨ep, a, pk, sk⟩, es⟩ | ⟨⟨ep, a, sk⟩, es, dec⟩ |
      ⟨⟨ep, a, sk, c1⟩, es⟩ | ⟨⟨ep, a, sk, c1⟩, dec⟩ | ⟨⟨ep, a⟩, dec⟩ | ⟨⟨ep, a, hdr⟩, dec⟩ |
      ⟨⟨ep, a, hdr, es', c1⟩, ecs, dec⟩ | ⟨⟨ep, a, hdr, es', c1, vec⟩, ecs⟩ |
      ⟨⟨ep, a, hdr, es', c1⟩, dec⟩ | ⟨⟨ep, a⟩, es⟩
  · exact absurd ⟨_, rfl⟩ hs.1
  · rcases σ with _ | ⟨e, a', dk, hdr', ek, enc⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, rfl, rfl, henc⟩ := hst
    obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 3 _ _ hdrCodec (by decide) enc es henc
    refine ⟨_, rfl, fun r => ?_⟩
    simp only [Braid.send, hnc]
    exact ⟨⟨hmk, rfl, rfl, rfl, rfl, rfl, hrel'⟩, rfl, hc, rfl, rfl⟩
  · rcases σ with _ | _ | ⟨e, a', dk, d, enc⟩ | _ | _ | _ | _ | _ | _ | _ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, rfl, hwf, henc⟩ := hst
    obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 36 _ _ ekCodec (by decide) enc es henc
    refine ⟨_, rfl, fun r => ?_⟩
    simp only [Braid.send, hnc]
    exact ⟨⟨hmk, rfl, rfl, rfl, rfl, hwf, hrel'⟩, rfl, hc, rfl, rfl⟩
  · rcases σ with _ | _ | _ | ⟨e, a', dk, ct1, enc⟩ | _ | _ | _ | _ | _ | _ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, rfl, henc⟩ := hst
    obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 36 _ _ ekCodec (by decide) enc es henc
    refine ⟨_, rfl, fun r => ?_⟩
    simp only [Braid.send, hnc]
    exact ⟨⟨hmk, rfl, rfl, rfl, rfl, hrel'⟩, rfl, hc, rfl, rfl⟩
  · rcases σ with _ | _ | _ | _ | ⟨e, a', dk, ct1, d⟩ | _ | _ | _ | _ | _ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, rfl, rfl, hwf⟩ := hst
    exact ⟨_, rfl, fun _ => ⟨⟨hmk, rfl, rfl, rfl, rfl, rfl, hwf⟩, rfl, trivial, rfl, rfl⟩⟩
  · rcases σ with _ | _ | _ | _ | _ | ⟨e, a', d⟩ | _ | _ | _ | _ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, hwf⟩ := hst
    exact ⟨_, rfl, fun _ => ⟨⟨hmk, rfl, rfl, rfl, hwf⟩, rfl, trivial, rfl, rfl⟩⟩
  · exact absurd ⟨_, _, rfl⟩ hs.2
  · rcases σ with _ | _ | _ | _ | _ | _ | _ | ⟨e, a', hdr', es, ct1, enc, d⟩ | _ | _ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, rfl, rfl, henc, rfl, hwf⟩ := hst
    obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 30 _ _ ct1Codec (by decide) enc ecs henc
    refine ⟨_, rfl, fun r => ?_⟩
    simp only [Braid.send, hnc]
    exact ⟨⟨hmk, rfl, rfl, rfl, rfl, rfl, hrel', rfl, hwf⟩, rfl, hc, rfl, rfl⟩
  · rcases σ with _ | _ | _ | _ | _ | _ | _ | _ | ⟨e, a', es, ct1, hdr', ek, enc⟩ | _ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, henc⟩ := hst
    obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 30 _ _ ct1Codec (by decide) enc ecs henc
    refine ⟨_, rfl, fun r => ?_⟩
    simp only [Braid.send, hnc]
    exact ⟨⟨hmk, rfl, rfl, rfl, rfl, rfl, rfl, hrel'⟩, rfl, hc, rfl, rfl⟩
  · rcases σ with _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨e, a', hdr', es, ct1, d⟩ | _ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, hwf⟩ := hst
    exact ⟨_, rfl, fun _ => ⟨⟨hmk, rfl, rfl, rfl, rfl, rfl, rfl, hwf⟩, rfl, trivial, rfl, rfl⟩⟩
  · rcases σ with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | ⟨e, a', enc⟩ <;>
      simp only [SameState] at hst
    obtain ⟨rfl, rfl, henc⟩ := hst
    obtain ⟨c, enc', hnc, hc, hrel'⟩ := encStep 5 _ _ ct2Codec (by decide) enc es henc
    refine ⟨_, rfl, fun r => ?_⟩
    simp only [Braid.send, hnc]
    exact ⟨⟨hmk, rfl, rfl, hrel'⟩, rfl, hc, rfl, rfl⟩

end SpqrBridge
