/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase
import LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy

/-!
# Generalized Residue Theorem -- Convex-Domain Corollaries

Convex-domain versions of the generalized residue theorem, proved as
corollaries of the null-homologous versions via `isNullHomologous_of_convex`.

## Main Results

* `generalizedResidueTheorem` -- simple poles, no explicit PV hypothesis
* `generalizedResidueTheorem_higher_order` -- higher-order poles with
  cancellation hypothesis
* `generalizedResidueTheorem_higher_order_simple` -- higher-order theorem
  specialised to simple poles
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-- **Generalized Residue Theorem** (Hungerbuhler-Wasem, Theorem 3.3).

CPV of `f` along a piecewise C1 immersion equals `2 pi i . Sigma winding . residue`,
even when the curve passes through simple poles. Unlike `generalizedResidueTheorem'`,
this version does NOT require `CauchyPrincipalValueExists'` as a hypothesis --
PV existence is proved from the immersion structure + C2 regularity at crossings.

Proved via `generalizedResidueTheorem'` on a convex domain, deriving PV
existence from C2 regularity at crossings. -/
theorem generalizedResidueTheorem (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (hC2_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueSimplePole f s := by
  have hPV_singular : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f s / (z - s)) γ.toFun γ.a γ.b s := by
    intro s hs
    have h_inv := cpv_exists_inv_sub γ s hγ_meas
      (h_no_endpt_cross s hs) (hC2_cross s hs) (h_cont_deriv_cross s hs)
    have h_eq : (fun z => residueSimplePole f s / (z - s)) =
        (fun z => residueSimplePole f s * (fun z => (z - s)⁻¹) z) := by
      ext z; simp [div_eq_mul_inv]
    rw [h_eq]; exact h_inv.const_mul (residueSimplePole f s)
  exact (generalizedResidueTheorem' U hU hU_convex S hS_in_U hS_discrete hS_closed
    S0 hS0_subset f hf γ hγ_closed hγ_in_U hS_on_curve hSimplePoles hf_ext hPV_singular).2

/-- **Generalized Residue Theorem for higher-order poles**
(Hungerbuhler-Wasem, Theorem 3.3, full generality).

For a meromorphic function `f` with poles of arbitrary order on a closed
piecewise C1 immersion, the Cauchy principal value equals
`2 pi i . Sigma n(gamma, z_l) . Res(f, z_l)`, provided the higher-order cancellation
hypothesis holds.

Proved via `generalizedResidueTheorem` on a convex domain, with the
higher-order cancellation hypothesis as input. -/
theorem generalizedResidueTheorem_higher_order (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (_hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hHigherOrderCancel : Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0))
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (hC2_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
  set f_res := fun z => ∑ s ∈ S0, residueAt f s / (z - s) with hf_res_def
  have hSimple_res : ∀ s ∈ S0, HasSimplePoleAt f_res s :=
    fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueAt f) s hs
  have hf_res_diff : DifferentiableOn ℂ f_res (U \ ↑S0) :=
    differentiableOn_sum_div_sub S0 (residueAt f) U
  have hf_ext_res : ∀ s ∈ S0, ContinuousAt
      (fun z => f_res z - residueSimplePole f_res s / (z - s)) s :=
    fun s hs => continuousAt_sum_remainder S0 (residueAt f) s hs
  have h_res_eq : ∀ s ∈ S0,
      residueSimplePole f_res s = residueAt f s :=
    fun s hs => residueSimplePole_sum_div_sub S0 (residueAt f) s hs
  have h_simple_thm := generalizedResidueTheorem U hU hU_convex S hS_in_U hS_discrete
    hS_closed S0 hS0_subset f_res hf_res_diff γ hγ_closed hγ_in_U hS_on_curve
    hSimple_res hf_ext_res hγ_meas h_no_endpt_cross hC2_cross h_cont_deriv_cross
  have h_res_formula : cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
    rw [h_simple_thm]; congr 1; apply Finset.sum_congr rfl
    intro s hs; rw [h_res_eq s hs]
  have hPV_singular_res : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f_res s / (z - s)) γ.toFun γ.a γ.b s := by
    intro s hs
    have h_inv := cpv_exists_inv_sub γ s hγ_meas
      (h_no_endpt_cross s hs) (hC2_cross s hs) (h_cont_deriv_cross s hs)
    have h_eq : (fun z => residueSimplePole f_res s / (z - s)) =
        (fun z => residueSimplePole f_res s * (fun z => (z - s)⁻¹) z) := by
      ext z; simp [div_eq_mul_inv]
    rw [h_eq]; exact h_inv.const_mul (residueSimplePole f_res s)
  have h_res_exists : CauchyPrincipalValueExistsOn S0 f_res γ.toFun γ.a γ.b :=
    (generalizedResidueTheorem' U hU hU_convex S hS_in_U hS_discrete
      hS_closed S0 hS0_subset f_res hf_res_diff γ hγ_closed hγ_in_U hS_on_curve
      hSimple_res hf_ext_res hPV_singular_res).1
  have h_cpv_eq : cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b :=
    cpv_eq_of_cancel_and_exists S0 f f_res γ hHigherOrderCancel h_res_exists
  rw [h_cpv_eq, h_res_formula]

/-- **Corollary**: The simple-pole theorem is a special case of the higher-order theorem.
When all singularities are simple poles, `generalizedResidueTheorem_higher_order`
reduces to `generalizedResidueTheorem` (conditions A and B are automatic,
and `residueAt = residueSimplePole`). -/
theorem generalizedResidueTheorem_higher_order_simple (U : Set ℂ)
    (hU : IsOpen U) (hU_convex : Convex ℝ U) (S : Set ℂ)
    (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (hC2_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ContDiffAt ℝ 2 γ.toFun t)
    (h_cont_deriv_cross : ∀ s ∈ S0, ∀ t ∈ Ioo γ.a γ.b, γ.toFun t = s →
      ∃ a' b', t ∈ Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
        ContinuousOn (deriv γ.toFun) (Icc a' b')) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
  have h_base := generalizedResidueTheorem U hU hU_convex S hS_in_U hS_discrete hS_closed
    S0 hS0_subset f hf γ hγ_closed hγ_in_U hS_on_curve hSimplePoles hf_ext
    hγ_meas h_no_endpt_cross hC2_cross h_cont_deriv_cross
  rw [h_base]
  congr 1; apply Finset.sum_congr rfl
  intro s hs
  rw [residueAt_eq_residueSimplePole f s (hSimplePoles s hs)]

end
