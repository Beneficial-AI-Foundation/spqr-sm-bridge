# W4 report: budgeted transfer and code-side game invariant

All four W4 theorems are proved. No statement or definition changed. `lake build` passes.

## Status

| Theorem | File | Status | Axioms |
|---------|------|--------|--------|
| `correctness_error_le_of_budgeted_transfer` | `CodeBound.lean` | proved | Lean's three |
| `codeGameInv_init` | `CodeContracts.lean` | proved | Lean's three, `spqr.kdf.hkdf_to_slice_spec` |
| `codeGameInv_pres` | `CodeContracts.lean` | proved | Lean's three, `spqr.kdf.hkdf_to_slice_spec` |
| `codeGameInv_epochs` | `CodeContracts.lean` | proved | Lean's three, `spqr.kdf.hkdf_to_slice_spec` |

Lean's three are `propext`, `Classical.choice` and `Quot.sound`. No W1 theorem is in any
closure, so there is no `sorryAx`.

## Proof route

Budgeted transfer (`SpqrBridge/BudgetedPotential.lean`):

- `wp_simulateQ_run_le_budget` is SM's `wp_simulateQ_run_le` with an invariant `Inv k` indexed
  by the number `k` of send queries left. A send query needs `0 < k` and moves to `Inv (k - 1)`.
  The induction on the adversary is the same as SM's.
- The index on the game is `Inv₁ s ∧ nA + nB + k ≤ q`. `nA_add_nB_le` shows that a send
  query raises `nA + nB` by at most one and that every other query keeps it. So a send query
  sees `nA + nB < q < Bud`, and every query sees `nA + nB ≤ q ≤ Bud`.
- `step_relTriple_of` is probe 1c's `step_relTriple`, with the obligations taken at the one
  state pair. The potential is probe 1c's `transferPotential`, unchanged.
- `correctness_error_le_of_budgeted_steps` takes the obligation fields as separate premises,
  because this file must not import `CodeBound`. The theorem in `CodeBound.lean` applies it to
  the fields of `hobl`.

The theorem needs only `Inv₁` and the send count. It needs no other state.

Game invariant (`SpqrBridge/GameInvSteps.lean`):

- `CodeGameInvRaw` and `RecordedRaw` are `CodeGameInv` and `RecordedAs` unfolded, because
  `CodeBound` imports this file. Each W4 theorem in `CodeContracts.lean` is one `exact` of the
  matching `Raw` theorem.
- Preservation goes through `sckaCorrectnessImpl_preservesInv`. A failed send, a key-length
  refusal (`keyOf` gives `none`) and a missing message leave the state unchanged. A refused
  delivery only clears `correct`. A successful send is a `CodeReach.sendA` step, and the new
  message lands at index `nA + 1` (`recorded_update`). An accepted delivery is a
  `CodeReach.recvA` step, and the delivered message is in the other party's list
  (`mem_of_recorded`). Stale deliveries are accepted deliveries, so this case covers them.
- The epoch bound is `epoch_bound_strong` plus `mem_of_recorded`.

## Helper files

- `SpqrBridge/BudgetedPotential.lean`: generic. It imports only `PotentialTransfer`.
- `SpqrBridge/GameInvSteps.lean`: imports `EpochBound` and SM's `Correctness`.

`CodeBound.lean` imports both. `SpqrBridge.lean` lists both.

## Note for W1 and W5

A proof term that passes a hypothesis `_ ∈ support (codeSendA s)` (or the same for
`(codeScheme k).sendA s`) as an argument fails with "maximum recursion depth". The linter
`constructorNameAsVariable` fails in the same way on such binders. The cause is the support of
`sampleTape`, a uniform 64-element vector. The workaround is to rewrite the hypothesis in place
(`change`, `unfold codeSendA`, `rw [mem_support_bind_iff]`) and to turn the linter off for that
declaration only. `codeGameInvRaw_pres` does both. There is no `maxRecDepth` or `maxHeartbeats`
change.
