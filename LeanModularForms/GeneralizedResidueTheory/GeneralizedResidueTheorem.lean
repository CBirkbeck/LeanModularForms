/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer

/-!
# Generalized Residue Theorem -- Public API

Clean top-level names for the generalized residue theorem and its corollaries.
All proofs delegate to the machinery in `HomologicalCauchy.lean` and
`Residue/FlatnessTransfer.lean`; this file contains no new proof work.

## Main results

* `generalizedResidueTheorem` -- the most general version: null-homologous
  curve, higher-order poles, conditions (A')+(B).
* `generalizedResidueTheorem_convex` -- corollary for convex domains (closedness
  replaces null-homologous hypothesis).
* `generalizedResidueTheorem_simplePoles` -- corollary for simple poles in
  null-homologous setting (conditions A+B drop out; uses `HasSimplePoleAt`).

## References

* Hungerbuhler-Wasem, *The generalized residue theorem*, arXiv:1808.00997v2,
  Theorem 3.3.
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

/-! ### Master theorem (null-homologous, higher-order poles, conditions A'+B) -/

/-- **Generalized Residue Theorem** (Hungerbuhler-Wasem, Theorem 3.3).

For a meromorphic function `f` with finitely many poles `S0` on a
null-homologous piecewise C^1 immersion `gamma` in an open set `U`,
the Cauchy principal value integral converges to
`2 pi i * sum_{s in S0} n(gamma, s) * Res(f, s)`,
provided conditions (A') (flatness) and (B) (angle/Laurent compatibility)
hold at every crossing point.

This is the most general form. See `generalizedResidueTheorem_convex` for
the convex-domain specialization and `generalizedResidueTheorem_simplePoles`
for the simple-pole case where conditions A'+B are not needed. -/
theorem generalizedResidueTheorem (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) :=
  generalizedResidueTheorem_3_3_nullHomologous U hU S hS_in_U hS_discrete
    hS_closed S0 hS0_subset f hf γ h_null hS_on_curve hMero hCondA hCondB
    hγ_meas h_no_endpt_cross h_unique_cross

/-! ### Convex-domain corollary -/

/-- **Generalized Residue Theorem** (convex domain).

Specialization of `generalizedResidueTheorem` to convex open sets, where
null-homologousness is automatic for any closed curve contained in `U`.
Requires the curve to be closed and contained in `U`. -/
theorem generalizedResidueTheorem_convex (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) :=
  GeneralizedResidueTheory.generalizedResidueTheorem_3_3
    U hU hU_convex S hS_in_U hS_discrete hS_closed S0 hS0_subset f hf γ
    hγ_closed hγ_in_U hS_on_curve hMero hCondA hCondB hγ_meas
    h_no_endpt_cross h_unique_cross

/-! ### Simple-pole corollary -/

/-- **Generalized Residue Theorem for simple poles** (null-homologous).

When every singularity in `S0` is a simple pole, conditions (A') and (B) are
not needed: condition (A') is automatic because every piecewise C^1 immersion
is flat of order 1 (`isFlatOfOrder_one`), and the Laurent compatibility in
condition (B) is vacuously satisfied (no higher-order terms). The conclusion
is an equality (CPV exists), not just `Tendsto`, and uses `residueAt` in place
of `residueSimplePole`.

**Hypotheses compared to `generalizedResidueTheorem`:**
- Replaces `hCondA`, `hCondB` with `hSimplePoles` (simple pole at each `s`)
  and `hf_ext` (continuity of the regular part `f(z) - Res/(z-s)`).
- Requires `DifferentiableOn` of `f` on `U \ S0`. -/
theorem generalizedResidueTheorem_simplePoles (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0,
      ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s :=
  generalizedResidueTheorem_higher_order_simple_nullHomologous U hU S hS_in_U
    hS_discrete hS_closed S0 hS0_subset f hf γ h_null hS_on_curve
    hSimplePoles hf_ext hγ_meas h_no_endpt_cross h_unique_cross
