# HOL Light C2 Report

Generated: 2026-04-24 20:42:06 -03:00

This report summarizes the current HOL Light formalization state for the C2/Rota K material.
The runner status below means: HOL Light loaded the module, accepted the stated theorems through its kernel, emitted the expected marker, and the log contains no `Exception:` or `Error in included file`.

## Summary

- Status: 12/12 HOL runners passing.
- Current inventory: 161 named `C2_*` theorem/lemma bindings and 40 `c2_*` definitions.
- Newest completed layer: `c2_full_chain.ml`.
- Scope of the HOL formalization so far: branch barrier, sigma-only/t-blind operator behavior, bridge to the genuine detector, cutoff residuals, finite/canonical residuals, exact `Z_X` transfer, abstract lower-bound-to-transfer chains, concrete real `c0` normalization/off-axis profile, the genuine complex `c0` profile realization in polar form, the multiplicity-safe Thm 8 transversality layer at jet level, the exact `Z_spec`/continuation interface, and an endpoint-facing Taylor-dominance/full-chain layer that propagates off-axis nonvanishing and exclusion-radius data to `zeta` and `Z_spec`.
- Important boundary: the full-chain layer is still conditional on explicit Taylor-dominance witnesses and the abstract continuation identity. It does not yet prove the analytic Taylor witness, the meromorphic identity step establishing `c2_continuation_identity`, or the downstream finite-strip/Rouche closure inside HOL Light.

## Runner Status

| Runner | Status | Latest log |
| --- | --- | --- |
| `run_c2_branch_barrier.sh` | PASS | `/tmp/hol_c2_branch_barrier.2536926.log` |
| `run_c2_branch_sigma.sh` | PASS | `/tmp/hol_c2_branch_sigma.2538008.log` |
| `run_c2_genuine_bridge.sh` | PASS | `/tmp/hol_c2_genuine_bridge.2539463.log` |
| `run_c2_cutoff_transfer.sh` | PASS | `/tmp/hol_c2_cutoff_transfer.2540759.log` |
| `run_c2_finite_residual.sh` | PASS | `/tmp/hol_c2_finite_residual.2542064.log` |
| `run_c2_zx_transfer.sh` | PASS | `/tmp/hol_c2_zx_transfer.2543878.log` |
| `run_c2_transfer_chains.sh` | PASS | `/tmp/hol_c2_transfer_chains.2545553.log` |
| `run_c2_c0_normalization.sh` | PASS | `/tmp/hol_c2_c0_normalization.2547081.log` |
| `run_c2_c0_complex_profile.sh` | PASS | `/tmp/hol_c2_c0_complex_profile.2548771.log` |
| `run_c2_transversal_multiplicity.sh` | PASS | `/tmp/hol_c2_transversal_multiplicity.3154357.log` |
| `run_c2_identity_continuation.sh` | PASS | `/tmp/hol_c2_identity_continuation.3258589.log` |
| `run_c2_full_chain.sh` | PASS | `/tmp/hol_c2_full_chain.3928442.log` |

## Module Inventory

| Module | `C2_*` theorems/lemmas | `c2_*` definitions | Main content |
| --- | ---: | ---: | --- |
| `c2_branch_barrier.ml` | 14 | 2 | Abstract branch mass barrier in `q`, trichotomy around `q = 1/2`, and `t`-blindness. |
| `c2_branch_sigma.ml` | 15 | 2 | Sigma parametrization `q(sigma)`, barrier equivalences around `sigma = 1/2`, and independence from `t`. |
| `c2_genuine_bridge.ml` | 10 | 3 | Branch norm bridge to a genuine detector error model under a lower bound for `c0`. |
| `c2_cutoff_transfer.ml` | 9 | 2 | `O(1/X)` cutoff residual bounds and transfer to the genuine error ratio. |
| `c2_finite_residual.ml` | 11 | 4 | Finite residual with phase/control vector, canonical residual, and residual-to-genuine transfer. |
| `c2_zx_transfer.ml` | 11 | 1 | Exact map `c2_zx zeta R c0 = zeta + R/c0` and norm transfer bounds. |
| `c2_transfer_chains.ml` | 14 | 0 | Abstract chains from `c0` lower-bound profiles and finite-band lower bounds to uniform `Z_X` transfer estimates. |
| `c2_c0_normalization.ml` | 17 | 6 | Concrete real `2^sigma`, `c0_real`, off-axis/critical lower profiles, positivity/nonzero lemmas, and profile-instantiated `Z_X` transfer theorems. |
| `c2_c0_complex_profile.ml` | 13 | 4 | Genuine complex `c0` coefficient in polar form, denominator nonzero/positive, numerator and denominator norm estimates, uniform off-axis lower profile, critical profile, and concrete `Z_X` transfer theorems. |
| `c2_transversal_multiplicity.ml` | 12 | 2 | Multiplicity-safe Leibniz collapse, abstract and critical Thm 8 nondegeneracy, plus the exact jet identity `Fjet = c2_c0_complex sigma t * zJet m` and its nonvanishing conclusion. |
| `c2_identity_continuation.ml` | 15 | 4 | Exact `Z_spec = (Dinf - Binf)/c0` interface, off-axis/critical ratio lemmas, abstract continuation identity wrapper, zero/nonzero equivalences for `Z_spec` and the numerator, and global off-axis zero exclusion reductions from `Z_spec`, the continued product, or the continued numerator. |
| `c2_full_chain.ml` | 20 | 10 | Endpoint-facing Taylor-dominance interface, gap/radius extraction, envelope/parametric/log-square `M2` variants, and full-chain nonvanishing/exclusion-radius consequences for the numerator, `zeta`, and `Z_spec`. |

## What Is Formalized Now

- The branch operator barrier is formalized both in the raw `q` variable and in the sigma-parametrized form.
- The operator layer is formally `t`-blind: the branch mass/norm statements depend on `sigma`, not on `t`.
- The critical threshold is formalized as `sigma = 1/2`: one side is contractive, the critical line is neutral, and the other side is expansive.
- The cutoff residual layer proves the expected `C/X` behavior and bounds it by coefficient hypotheses of the form `abs(C) <= B * L * X`.
- The finite residual layer proves the same transfer for phase-controlled and canonical finite residuals.
- The `Z_X` layer proves the exact algebraic transfer identity and the finite/canonical bounds from a lower bound `L <= norm(c0)`.
- The transfer-chain layer now proves that abstract global/profile/band lower bounds for `c0` imply the corresponding uniform `Z_X` transfer estimates.
- The concrete real `c0` normalization layer now proves positivity and nonzero facts for the real/off-axis/critical lower profiles, including `c2_c0_offaxis_lower sigma <= c2_c0_real sigma` for `0 < sigma`, and connects realized profiles directly to the existing `Z_X` transfer bounds.
- The genuine complex `c0` profile layer now proves, uniformly in `t`, that `c2_c0_offaxis_lower sigma <= norm(c2_c0_complex sigma t)` for `0 < sigma`, plus the corresponding off-axis/critical profile-realization and concrete transfer theorems.
- The multiplicity-safe transversality layer now proves the arbitrary-order Leibniz collapse used in Rota K Thm 8, the abstract and critical nondegeneracy statements, and the exact product-jet identity `Fjet = c2_c0_complex sigma t * zJet m` together with `Fjet <> 0`.
- The identity/continuation layer now formalizes the exact quotient object `c2_zspec`, the abstract half-plane continuation wrapper `c2_continuation_identity`, off-axis and critical Thm 13 ratio consequences, and the exact zero/nonzero equivalences between `Z_spec`, the continued numerator, and `zeta` on `sigma > 0`.
- That same layer now reduces off-axis zero exclusion for `zeta` to any of three endpoint inputs: direct nonvanishing of `Z_spec`, a transversal product-jet witness for `Z_spec`, or a transversal product-jet witness for either the continued product `c2_c0_complex sigma t * zeta sigma t` or the continued numerator `Dinf sigma t - Binf sigma t`.
- The full-chain layer now packages the Lean-style Taylor-dominance endpoint: an explicit positive gap witness implies numerator nonvanishing, extracts `deltaStar = 2 * mu / M2`, and transfers the resulting off-axis nonvanishing/radius conclusions to `zeta` and `Z_spec`.
- The same full-chain layer provides envelope, parametric, and height-log-square variants for the `M2` bound, matching the endpoint-facing shape used by the Lean report and Rota K notes.

## What Still Needs Porting Into HOL Light

- Optional syntactic identification between the polar HOL coefficient `c2_c0_complex` and any alternate `cpow`/`cexp` analytic presentation used in the paper, if that exact presentation is needed downstream.
- The analytic theorem establishing `c2_continuation_identity` from the meromorphic continuation / identity-principle argument, not just the abstract continuation interface and its algebraic consequences.
- The analytic proof that supplies the Taylor-dominance witnesses (`mu`, `M2`, residual `R`, and `delta`) for the concrete continued numerator.
- Optional transport of the jet-level transversality theorem to a literal iterated-`sigma`-derivative wrapper, if the downstream endpoint needs the theorem stated with actual derivatives rather than jet data.
- The paper-level finite-strip/Rouche/Hurwitz closure, after the analytic continuation step and the concrete Taylor/lower-bound witnesses are available in HOL.

These are pending HOL formalization items, not statements about gaps in the Rota K documents.

## Reproduction Commands

Run individual modules:

```bash
bash formal/hol_c2/run_c2_branch_barrier.sh
bash formal/hol_c2/run_c2_branch_sigma.sh
bash formal/hol_c2/run_c2_genuine_bridge.sh
bash formal/hol_c2/run_c2_cutoff_transfer.sh
bash formal/hol_c2/run_c2_finite_residual.sh
bash formal/hol_c2/run_c2_zx_transfer.sh
bash formal/hol_c2/run_c2_transfer_chains.sh
bash formal/hol_c2/run_c2_c0_normalization.sh
bash formal/hol_c2/run_c2_c0_complex_profile.sh
bash formal/hol_c2/run_c2_transversal_multiplicity.sh
bash formal/hol_c2/run_c2_identity_continuation.sh
bash formal/hol_c2/run_c2_full_chain.sh
```

The runners are verification wrappers. The mathematical acceptance is the HOL Light kernel accepting each `prove` block; the shell scripts only make that kernel check reproducible.

## Recommended Next Step

Port the analytic proof of the continuation identity and the concrete Taylor-dominance witness next. The endpoint algebra is now in HOL Light, so the remaining high-value work is replacing the abstract hypotheses by analytic estimates and then closing the finite-strip/Rouche/Hurwitz step.
