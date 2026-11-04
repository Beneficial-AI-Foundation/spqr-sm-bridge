/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Beneficial AI Foundation
-/
import SpqrBridge.CodeContracts

/-!
# The relation between `Braid` and secure-messaging's `SPQR.Chunked`

`ChunkedRel σ st` relates a state of the abstract machine `Braid` (over `codePrims`) to a state
of `SPQR.Chunked` over `codeParams`:

* the same constructor, equal epochs and equal authenticators;
* each byte field of `Braid` is the value of the typed field of `codeParams`;
* the decoders are equal (both are `PolyDecoder`), and each needs `16 K` points and has sorted
  slots (`DecWF`);
* each code encoder holds the payload of the secure-messaging encoder at the counter
  `nextIndex mod 2^32`, the form of `next_chunk_wrap` (`EncRel`);
* the `Braid` authenticator has a 32-byte MAC key, so that `fit 32` is the identity on its MACs.

`RA s st` composes `Refines` with `ChunkedRel`. `RM` relates the code's messages to
secure-messaging's.
-/

namespace SpqrBridge

open Aeneas Aeneas.Std Result spqr spqr.v1.chunked.states Braid
open ErasureCodePayload.Streaming

/-- The `Braid` states over the code's encoders and decoders. -/
abbrev BState := Braid.State encoding.polynomial.PolyEncoder encoding.polynomial.PolyDecoder

/-- The secure-messaging states over the code's parameters. -/
abbrev SMState := SPQR.Chunked.PartyState codeParams Braid.Auth

/-- A code decoder for `K` chunks that `add_chunk` and `decoded_message` accept: it needs
`16 K` points, and its slots are sorted. -/
def DecWF (K : ℕ) (d : encoding.polynomial.PolyDecoder) : Prop :=
  d.pts_needed.val = 16 * K ∧ encoding.polynomial.PolyDecoder.PointsValid d.pts

/-- The code encoder `enc` holds the payload of the secure-messaging encoder `es`, with stored
counter `es.nextIndex mod 2^32`. -/
def EncRel {M : Type} (K : ℕ) (hK : 0 < K) (hKN : K ≤ 2 ^ 16) (cd : L2.Codec M K)
    (enc : encoding.polynomial.PolyEncoder) (es : EncoderState M L2.Sym) : Prop :=
  es.ecp = L2.ecp K hK hKN cd ∧ L2.EncInv (cd.ser es.payload) enc ∧
    enc.idx.val = es.nextIndex % 2 ^ 32

/-- The authenticator that every `Braid` state holds. -/
def authOf : BState → Auth
  | .keysUnsampled _ a | .keysSampled _ a .. | .headerSent _ a .. | .ct1Received _ a ..
  | .ekSentCt1Received _ a .. | .noHeaderReceived _ a .. | .headerReceived _ a ..
  | .ct1Sampled _ a .. | .ekReceivedCt1Sampled _ a .. | .ct1Acknowledged _ a ..
  | .ct2Sampled _ a .. => a

/-- `SameState σ st`: the same state of §2.5 with equal values. The `Braid` header in
`keysSampled` and `ekReceivedCt1Sampled`, which `Refines` leaves free, is the header of `st`. -/
def SameState : BState → SMState → Prop
  | .keysUnsampled e a, .keysUnsampled core => e = core.ep ∧ a = core.authSt
  | .keysSampled e a dk hdr ek enc, .keysSampled core es =>
    e = core.ep ∧ a = core.authSt ∧ dk = core.sk.1 ∧ hdr = core.pk.1.1.1 ∧
      ek = core.pk.1.2.1 ∧ EncRel 3 (by decide) (by decide) hdrCodec enc es
  | .headerSent e a dk d enc, .headerSent core es dec =>
    e = core.ep ∧ a = core.authSt ∧ dk = core.sk.1 ∧ d = dec ∧ DecWF 30 d ∧
      EncRel 36 (by decide) (by decide) ekCodec enc es
  | .ct1Received e a dk ct1 enc, .ct1Received core es =>
    e = core.ep ∧ a = core.authSt ∧ dk = core.sk.1 ∧ ct1 = core.c1.1 ∧
      EncRel 36 (by decide) (by decide) ekCodec enc es
  | .ekSentCt1Received e a dk ct1 d, .ekSentCt1Received core dec =>
    e = core.ep ∧ a = core.authSt ∧ dk = core.sk.1 ∧ ct1 = core.c1.1 ∧ d = dec ∧ DecWF 5 d
  | .noHeaderReceived e a d, .noHeaderReceived core dec =>
    e = core.ep ∧ a = core.authSt ∧ d = dec ∧ DecWF 3 d
  | .headerReceived e a hdr d, .headerReceived core dec =>
    e = core.ep ∧ a = core.authSt ∧ hdr = core.hdr.1 ∧ d = dec ∧ DecWF 36 d
  | .ct1Sampled e a hdr es ct1 enc d, .ct1Sampled core ecs dec =>
    e = core.ep ∧ a = core.authSt ∧ hdr = core.hdr.1 ∧ es = core.encapsSt.1 ∧
      ct1 = core.c1.1 ∧ EncRel 30 (by decide) (by decide) ct1Codec enc ecs ∧ d = dec ∧ DecWF 36 d
  | .ekReceivedCt1Sampled e a es ct1 hdr ek enc, .ekReceivedCt1Sampled core ecs =>
    e = core.ep ∧ a = core.authSt ∧ es = core.encapsSt.1 ∧ ct1 = core.c1.1 ∧
      hdr = core.hdr.1 ∧ ek = core.vec.1 ∧ EncRel 30 (by decide) (by decide) ct1Codec enc ecs
  | .ct1Acknowledged e a hdr es ct1 d, .ct1Acknowledged core dec =>
    e = core.ep ∧ a = core.authSt ∧ hdr = core.hdr.1 ∧ es = core.encapsSt.1 ∧
      ct1 = core.c1.1 ∧ d = dec ∧ DecWF 36 d
  | .ct2Sampled e a enc, .ct2Sampled core es =>
    e = core.ep ∧ a = core.authSt ∧ EncRel 5 (by decide) (by decide) ct2Codec enc es
  | _, _ => False

/-- `ChunkedRel σ st`: `σ` and `st` are the same state with equal values, and the MAC key of
`σ` has 32 bytes. -/
def ChunkedRel (σ : BState) (st : SMState) : Prop :=
  (authOf σ).macKey.length = 32 ∧ SameState σ st

/-- The relation of party states: the code state refines a `Braid` state that is related to the
secure-messaging state. -/
def RA (s : States) (st : SMState) : Prop := ∃ σ, Refines s σ ∧ ChunkedRel σ st

/-- A code chunk as a secure-messaging chunk. -/
def chunkOfCode (c : encoding.Chunk) : ℕ × L2.Sym := (c.index.val, c.data)

/-- The payloads correspond by constructor. `Ct1Ack false`, which the code never sends, carries
nothing: like `absMsg`, it corresponds to the `none` payload. -/
def PayloadRel : MessagePayload → SPQR.Chunked.Payload L2.Sym → Prop
  | .None, .none => True
  | .Ct1Ack false, .none => True
  | .Hdr c, .hdr x => x = chunkOfCode c
  | .Ek c, .ek x => x = chunkOfCode c
  | .EkCt1Ack c, .ekCt1Ack x => x = chunkOfCode c
  | .Ct1Ack true, .ct1Ack => True
  | .Ct1 c, .ct1 x => x = chunkOfCode c
  | .Ct2 c, .ct2 x => x = chunkOfCode c
  | _, _ => False

/-- The relation of messages: equal epochs and corresponding payloads. -/
def RM (m : Message) (m' : SPQR.Chunked.Message L2.Sym) : Prop :=
  m.epoch.val = m'.epoch ∧ PayloadRel m.payload m'.payload

end SpqrBridge
