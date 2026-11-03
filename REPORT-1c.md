# Probe 1c: transfer of the correctness bound

Result: route 1 (potential transport) closes on the abstract model. Routes 2 and 3 were not
needed and were not tried.

## Theorems

All in `SpqrBridge/`, commit `26d5582` on `poc/1c`. No `sorry`. `#print axioms` on each theorem
gives only `[propext, Classical.choice, Quot.sound]`, the same set as `SPQR.correctness_error_le`.

- `correctness_error_le_of_transfer` (`PotentialTransfer.lean`). Assume that a scheme `S₂` meets
  the four premises of `SCKAScheme.correctness_error_le_of_potential` with invariant `Inv₂`,
  potential `V₂` and error `ε`. Assume that a scheme `S₁` meets `TransferObligations S₁ S₂ Inv₂ RA
  RB RM`. Then every adversary against `S₁` with at most `q` sends has
  `1 - Pr[correctnessExp S₁ adv = true] ≤ q · ε`.
- `spqr_correctness_error_le_of_transfer` (`PotentialTransferSPQR.lean`). The same theorem with
  `S₂ := SPQR.scheme` and the invariant and potential of `SPQR.correctness_error_le`. The four
  premises of `S₂` are discharged from SM's own lemmas. The only remaining premises are the four
  lawful decoders (as in SM) and `TransferObligations`.
- `transferObligations_self`: every scheme meets the obligations against itself, with equality as
  the three relations. This shows that the obligations can be met.

## How route 1 works

The proof applies `correctness_error_le_of_potential` to `S₁` with the invariant `True` and this
potential:

```text
V₁ s₁ = 1                                                    if s₁.correct = false
V₁ s₁ = min 1 (inf { V₂ s₂ | GameRel s₁ s₂, ∃ ik₂, Inv₂ ik₂ s₂ })   otherwise
```

The infimum removes the risk named in the plan. The relation is not a function, but no related
state must be chosen. The cap at `1` removes the need for an invariant on `S₁`. A state with no
related `S₂` state, or with a false flag, has potential `1`. Its expected successor potential is
also at most `1`, so the step condition holds there without any relation. Thus nothing about the
two games is needed after the flag becomes false.

For a related pair `(s₁, s₂)`, one query is coupled for one step only (`step_relTriple`). The
coupling relates the successor states by `GameRel`, or the `S₂` successor has a false flag. Then
`wp_le_of_relTriple` gives `E[V₁ s₁'] ≤ E[V₂ s₂'] ≤ V₂ s₂ + ε`, and the infimum over `s₂` gives the
step condition. The two runs are never coupled as a whole, and the adversary is never shared. So
the problem of the VCVio coupling lemma (answers after a failure) does not arise. The answers of
the two oracles need not be equal at all.

## Obligations for a concrete bridge

These are the fields of `TransferObligations`. They become fields of the bridge's obligations
structure.

Relations: `RA : StA₁ → StA₂ → Prop`, `RB : StB₁ → StB₂ → Prop`, `RM : Rho₁ → Rho₂ → Prop`. The
message relation can be any relation. Injectivity and a message function are not needed.
`GameRel RA RB RM s₁ s₂` asks for related party states and for transit arrays related entry by
entry by `RM`, with equal epochs. It also asks for equal key tables, counters, current epochs and
flag. Both schemes
must use the same epoch-key type `I`. For SPQR, this means that the code's `I` is `P.EpochKey`.

Context of the step obligations: `s₁.correct = true`, `GameRel RA RB RM s₁ s₂`, and
`Inv₂ ik₂ s₂`. For SPQR, `Inv₂` is `CorrectnessInv (toMLKEMBraid s₂) ∧ Ct1AckInv s₂`, which gives
a consistent transcript, so honest messages, to the obligation. The obligations must hold for
every such `s₂`, not for one chosen `s₂`.

1. `init` (supports only). For `ik₁`, `stA₁`, `stB₁` in the supports of `S₁`'s initialization,
   some `ik₂`, `stA₂`, `stB₂` in the supports of `S₂`'s initialization satisfy `RA stA₁ stA₂`
   and `RB stB₁ stB₂`.
2. `sendA`, `sendB` (a coupling). `RelTriple (S₁.sendA s₁.stA) (S₂.sendA s₂.stA) (SendRel RA RM)`.
   `SendRel` holds in two cases. Both sends refuse. Or both succeed with equal key output, equal
   epoch, messages related by `RM` and next states related by `RA`.
3. `recvA`, `recvB` (deterministic). If `s₁.msgB n = some (ρ₁, t)`, `s₂.msgB n = some (ρ₂, t)` and
   `RM ρ₁ ρ₂`, then `RecvRel RA (S₁.recvA s₁.stA ρ₁) (S₂.recvA s₂.stA ρ₂)`. `RecvRel` holds in
   three cases. `S₂` refuses, and then any result of `S₁` is allowed. Or both accept with equal
   key output, equal epoch and next states related by `RA`. A refusal of `S₁` with an acceptance
   of `S₂` is not allowed. In words, a code failure must be an SM failure.

Equality of distributions or only of supports: `init` needs supports only. `recv` is pointwise.
`send` needs a coupling, which is more than equal supports, because the potential is an
expectation. A coupling is weaker than equality of distributions: the two output distributions
need not be equal, and they are on different types. To discharge it, run the same sampler on
both sides (`relTriple_refl`), then relate the deterministic remainder (`relTriple_bind`,
`relTriple_pure_pure`). Then the only equality of
distributions needed is that the two schemes sample their randomness from the same distribution.

## Routes not tried

Route 2 is absorbing failure. Route 3 is an honest-chunk invariant without the flag. We did not
try them, because route 1 closed with a smaller set of obligations. Both routes couple the complete
runs, so they also need equal oracle answers. Route 1 does not need equal answers.

## What a concrete bridge must still check

The obligations assume that `RA` and `RB` relate the code's states to every SM state that the
infimum ranges over. The decoder relation comes from L2 (session `bridge-l2`). If it relates one
code decoder state to several SM decoder states, `send` and `recv` must agree for each of them. The
`Inv₂`-context in the obligations is there to help with this. The adapter `codeScheme` (session
`bridge-1b`) must report the same key, epoch and refusal as SM, because `GameRel` requires equal
key tables, epochs and flags.
