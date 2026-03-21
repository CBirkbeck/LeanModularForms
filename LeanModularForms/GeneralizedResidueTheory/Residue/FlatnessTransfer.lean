/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy

/-!
# Generalized Residue Theorem (Theorem 3.3) -- Convex Domain Corollaries

Convex-domain specializations of the null-homologous residue theorems from
`HomologicalCauchy.lean`. Each convex theorem is a thin wrapper that constructs
the `IsNullHomologous` witness via `isNullHomologous_of_convex` and delegates
to the corresponding `_nullHomologous` version.

## Main results

* `pv_res_tendsto_of_immersion`: PV residue convergence (convex)
* `generalizedResidueTheorem_3_3`: the generalized residue theorem with conditions (A')+(B) (convex)
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

/-- Convex-domain corollary of `higherOrderCancel_assembly_nh`. -/
theorem higherOrderCancel_assembly (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0)) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0) (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) :=
  have h_null : IsNullHomologous γ U :=
    isNullHomologous_of_convex U hU hU_convex
      ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr γ.hab.le)⟩
      γ hγ_closed hγ_in_U
  higherOrderCancel_assembly_abstract U hU S0 f hf γ
    h_null.closed h_null.image_subset hMero hCondA hCondB _hγ_meas h_no_endpt
    h_unique_cross hS0_in_U
    (fun _ hg => contourIntegral_eq_zero_of_nullHomologous hU hg γ h_null)
    (fun T g hg_mero hg_res hg_diff _hT_in_U hg_avoids =>
      contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh T g
        hg_mero hg_res U hU hg_diff γ h_null hg_avoids)

/-- **Bridge Lemma (convex domain):** Conditions (A') (flatness of pole order) and (B)
(angle/Laurent compatibility) imply the higher-order cancellation hypothesis.

Convex-domain corollary of `conditionsAB_imply_higherOrderCancel_nh`. -/
theorem conditionsAB_imply_higherOrderCancel (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0)) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0) (hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0) :=
  have h_null : IsNullHomologous γ U :=
    isNullHomologous_of_convex U hU hU_convex
      ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr γ.hab.le)⟩
      γ hγ_closed hγ_in_U
  conditionsAB_imply_higherOrderCancel_nh U hU S0 f hf γ
    h_null hMero hCondA hCondB hγ_meas h_no_endpt h_unique_cross hS0_in_U

/-- PV convergence of the pure residue function for closed PiecewiseC1Immersion curves.

Convex-domain corollary of `pv_res_tendsto_of_immersion_nullHomologous`. -/
lemma pv_res_tendsto_of_immersion
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (_hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) :=
  have h_null : IsNullHomologous γ U :=
    isNullHomologous_of_convex U hU hU_convex
      ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr γ.hab.le)⟩
      γ hγ_closed hγ_in_U
  pv_res_tendsto_of_immersion_nullHomologous U S hS_discrete hS_closed
    S0 hS0_subset f γ h_null hS_on_curve _hγ_meas h_no_endpt_cross h_unique_cross

/-- **Theorem 3.3 (Hungerbühler-Wasem)**: Generalized residue theorem with the paper's
actual conditions (A') and (B), matching arXiv:1808.00997v2 Theorem 3.3.

Uses `Tendsto` formulation and does not require C² regularity at crossings.

- **Condition (A')**: At each crossing point where `f` has a pole of order `n`,
  the curve is flat of order `n` (Definition 3.2). Uses `SatisfiesConditionA'`
  with `poleOrderAt f` to capture the variable-order flatness requirement.
- **Condition (B)**: At each crossing point, the angle `α` is a rational multiple
  of `π`, and each nonzero Laurent coefficient `a_{-k}` with `k ≥ 2` satisfies
  `(k-1)·α ∈ 2πℤ`.

These conditions ensure that the PV contributions from higher-order polar terms
vanish, so the full PV integral reduces to the simple-pole case.

For simple poles, `poleOrderAt f s = 1` and `IsFlatOfOrder γ t₀ 1` is automatic
(see `isFlatOfOrder_one`), so condition (A') reduces to condition (A). -/
theorem generalizedResidueTheorem_3_3
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
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
  have h_null : IsNullHomologous γ U :=
    isNullHomologous_of_convex U hU hU_convex
      ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr γ.hab.le)⟩
      γ hγ_closed hγ_in_U
  generalizedResidueTheorem_3_3_nullHomologous U hU S hS_in_U hS_discrete hS_closed
    S0 hS0_subset f hf γ h_null hS_on_curve hMero hCondA hCondB hγ_meas
    h_no_endpt_cross h_unique_cross

end GeneralizedResidueTheory
