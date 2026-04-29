/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheorem
import LeanModularForms.ForMathlib.CurveMeasureZero

/-!
# Higher-Order Cancellation Assembly

This file provides the assembly layer connecting conditions (A')+(B) from
Hungerbuhler-Wasem to the `hCancel` hypothesis required by the generalized
residue theorem (Theorem 3.3).

## Main results

### Simple pole cancellation (fully proved)

* `hCancel_of_simplePoles_convex` -- for simple poles in convex domains, the
  remainder `f - principalPartSum` has vanishing CPV: it is holomorphic, so its
  contour integral vanishes by Cauchy, and the CPV equals the contour integral
  since `gamma` avoids all poles.

### Composition and assembly

* `generalizedResidueTheorem_composed` -- given a cancellation result for the
  remainder and a CPV result for the singular part, assembles the full residue
  formula. A direct application of `hasCauchyPVOn_of_tendsto_sub`.

* `hasCauchyPVOn_simplePoles_convex` -- the fully assembled CPV residue theorem
  for simple poles in convex domains: no `hCancel` or `hPV_sing` hypotheses.

### Avoidance infrastructure

* `cpvIntegrandOn_eq_of_avoids` -- when `gamma` avoids `S` and `epsilon` is small,
  the CPV integrand equals the full contour integrand.

* `cpvIntegrandOn_integrableOn_of_avoids` -- integrability of the CPV integrand
  for small epsilon, derived from contour integrand integrability.

* `hPV_sing_of_avoids` -- the singular part CPV equals the winding number formula
  when `gamma` avoids all poles.

## Design notes

The full proof that conditions (A')+(B) imply higher-order cancellation is deep
(sector curve analysis + dominated convergence). This file provides the
*composition layer* that shows how to combine such a result with the generalized
residue theorem to obtain the unconditional HW Theorem 3.3.

For simple poles, the cancellation is elementary (the remainder is holomorphic),
and we prove everything from scratch with no sorry.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2, Theorem 3.3.
-/

open Complex Set Filter Topology MeasureTheory Finset
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-! ## Avoidance infrastructure -/

/-- When `gamma` avoids all points of `S` with margin `delta` and `epsilon < delta`,
the CPV integrand equals the full contour integrand at every point of `[0,1]`. -/
theorem cpvIntegrandOn_eq_of_avoids
    {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {δ : ℝ} (hδ_bound : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    {ε : ℝ} (hε : ε < δ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    cpvIntegrandOn S f γ.toPath.extend ε t =
      f (γ.toPath.extend t) * deriv γ.toPath.extend t := by
  apply cpvIntegrandOn_of_forall_gt
  intro s hs
  exact lt_of_lt_of_le hε (hδ_bound s hs t ht)

/-- The CPV integrand is interval-integrable on `[0,1]` when `gamma` avoids `S`
and `epsilon` is small, provided the contour integrand is integrable. -/
theorem cpvIntegrandOn_integrableOn_of_avoids
    {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {δ : ℝ} (_hδ_pos : 0 < δ)
    (hδ_bound : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    {ε : ℝ} (_hε_pos : 0 < ε) (hε_lt : ε < δ)
    (hint : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand f γ) volume 0 1) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1 := by
  apply hint.congr
  intro t ht
  rw [uIoc_of_le (zero_le_one' ℝ)] at ht
  simp only [PiecewiseC1Path.contourIntegrand, PiecewiseC1Path.extendedPath_eq]
  rw [cpvIntegrandOn_eq_of_avoids hδ_bound hε_lt t (Ioc_subset_Icc_self ht)]

/-! ## Simple pole cancellation -/

/-- **Simple pole cancellation in convex domains.**

For simple poles in a convex domain where `gamma` avoids all poles, the CPV
of `f - principalPartSum` converges to zero.

Proof:
1. The remainder admits a holomorphic extension `g` to all of `U`.
2. `g` agrees with the remainder on the curve (which avoids `S`).
3. The contour integral of `g` vanishes by Cauchy for convex domains.
4. The contour integral of the remainder equals that of `g`, hence vanishes.
5. The CPV equals the contour integral (by avoidance), hence vanishes. -/
private theorem contourIntegral_remainder_eq_zero_of_simplePoles
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1) :
    γ.contourIntegral
      (fun z => f z - principalPartSum S (fun s => residue f s) z) = 0 := by
  obtain ⟨g, hg_diff, hg_agree⟩ := remainder_differentiableOn_of_simplePoles
    hU_open S hS_in_U f hf hSimplePoles
  have h_g_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S (fun s => residue f s) (γ t) :=
    fun t ht => hg_agree (γ t) ⟨hγ_in_U t ht, fun hmem =>
      hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
  have h_g_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand g γ) volume 0 1 := by
    apply h_rem_int.congr
    intro t ht
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.contourIntegrand]
    rw [h_g_on_curve t (Ioc_subset_Icc_self ht)]
  have hg_zero : γ.contourIntegral g = 0 :=
    γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU_convex hU_open hU_ne
      hg_diff hγ_in_U h_g_int
  have h_integrals_eq : γ.contourIntegral g =
      γ.contourIntegral (fun z => f z - principalPartSum S (fun s => residue f s) z) := by
    simp only [PiecewiseC1Path.contourIntegral, PiecewiseC1Path.extendedPath_eq]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.extendedPath_eq] at h_g_on_curve
    show g (γ.toPath.extend t) * _ = (f (γ.toPath.extend t) - _) * _
    rw [h_g_on_curve t ht]
  rw [← h_integrals_eq]; exact hg_zero

theorem hCancel_of_simplePoles_convex
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 := by
  rw [← contourIntegral_remainder_eq_zero_of_simplePoles hU_convex hU_open hU_ne S hS_in_U
    f hf γ hSimplePoles hγ_in_U hγ_avoids h_rem_int]
  exact hasCauchyPVOn_of_avoids hδ

/-- **Pointwise variant of `hCancel_of_simplePoles_nullHomologous`**:
requires only `dixonFunction ((z-w₀)·(f-pp)) U γ w₀ = 0` at `w₀`. Used when
`h_dixon_zero` comes from B-5 applied to a corrected remainder that agrees
with `f - pp` only on `U \ S`. Null-homologous analog of
`hCancel_of_simplePoles_convex`. -/
theorem hCancel_of_simplePoles_nullHomologous_at
    {U : Set ℂ} (_hU_open : IsOpen U)
    (S : Finset ℂ) (_hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (_hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (_hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (_hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (w₀ : ℂ) (hw₀_in_U : w₀ ∈ U)
    (hw₀_off : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀)
    (h_dixon_zero_at : dixonFunction
      (fun z => (z - w₀) *
        (f z - principalPartSum S (fun s => residue f s) z)) U γ w₀ = 0)
    (h_cauchy_int : IntervalIntegrable
      (fun t => (γ t - w₀) *
        (f (γ t) - principalPartSum S (fun s => residue f s) (γ t))
        / (γ t - w₀) * deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t => (γ t - w₀)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 := by
  have h_zero : γ.contourIntegral
      (fun z => f z - principalPartSum S (fun s => residue f s) z) = 0 :=
    contourIntegral_eq_zero_of_nullHomologous_at w₀ hw₀_in_U hw₀_off
      h_dixon_zero_at h_cauchy_int h_base_int
  rw [← h_zero]
  exact hasCauchyPVOn_of_avoids hδ

theorem hCancel_of_simplePoles_nullHomologous
    {U : Set ℂ} (hU_open : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (w₀ : ℂ) (hw₀_in_U : w₀ ∈ U)
    (hw₀_off : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀)
    -- Dixon-zero for the twisted remainder g(z) = (z - w₀) · (f - pp)(z)
    (h_dixon_zero : ∀ w, dixonFunction
      (fun z => (z - w₀) *
        (f z - principalPartSum S (fun s => residue f s) z)) U γ w = 0)
    (h_cauchy_int : IntervalIntegrable
      (fun t => (γ t - w₀) *
        (f (γ t) - principalPartSum S (fun s => residue f s) (γ t))
        / (γ t - w₀) * deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t => (γ t - w₀)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_simplePoles_nullHomologous_at hU_open S hS_in_U f hf γ hSimplePoles
    hγ_in_U hγ_avoids hδ w₀ hw₀_in_U hw₀_off (h_dixon_zero w₀)
    h_cauchy_int h_base_int

/-- The CPV of the singular part equals the winding number formula when `gamma`
avoids all poles. -/
theorem hPV_sing_of_avoids
    (S : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s)) γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) := by
  rw [← contourIntegral_principalPartSum_eq hδ hI]
  exact hasCauchyPVOn_of_avoids hδ

/-! ## Composition layer -/

/-- **Composition theorem.** Given:
- A cancellation result: `HasCauchyPVOn S (f - pp) gamma 0`
- A singular CPV result: `HasCauchyPVOn S pp gamma (formula)`
- Integrability of both CPV integrands

the CPV of `f` equals the winding-residue formula.

This decomposes `f = (f - pp) + pp` and applies `hasCauchyPVOn_of_tendsto_sub`.

TODO (legacy-port-plan Phase 1): derive the four oracle hypotheses from
Condition A'/B hypotheses. See
`docs/superpowers/plans/2026-04-20-legacy-port-plan.md`. -/
theorem generalizedResidueTheorem_composed
    (S : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Path x x)
    (hCancel : HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z)
      γ 0)
    (hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s)) γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s))
    (hI_rem : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z)
        γ.toPath.extend ε t) volume 0 1)
    (hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) :=
  hasCauchyPVOn_of_tendsto_sub hCancel hPV_sing hI_rem hI_sing

/-! ## Fully assembled simple-pole CPV theorem -/

/-- **Fully assembled CPV residue theorem for simple poles in convex domains.**

This composes:
1. `hCancel_of_simplePoles_convex` -- remainder CPV tends to 0
2. `hPV_sing_of_avoids` -- singular CPV = formula
3. `generalizedResidueTheorem_composed` -- assembly

The CPV-integrand integrability hypotheses are passed through from the caller.
In the avoidance case these can be derived from contour-integrand integrability
via `cpvIntegrandOn_integrableOn_of_avoids`. -/
theorem hasCauchyPVOn_simplePoles_convex
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (_h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1)
    (hI_cpv_rem : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z)
        γ.toPath.extend ε t) volume 0 1)
    (hI_cpv_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) :=
  generalizedResidueTheorem_composed S f γ
    (hCancel_of_simplePoles_convex hU_convex hU_open hU_ne S hS_in_U f hf γ
      hSimplePoles hγ_in_U hγ_avoids hδ h_rem_int)
    (hPV_sing_of_avoids S f γ hδ hI)
    hI_cpv_rem hI_cpv_sing

/-! ## Discharging CPV integrability from contour integrability -/

/-- In the avoidance case, CPV-integrand integrability can be derived from contour
integrand integrability for any `epsilon` in `(0, delta)`. This helper shows
that the `hI_cpv_rem` and `hI_cpv_sing` hypotheses in the fully assembled
theorem are automatically satisfiable in the avoidance case. -/
theorem cpvIntegrandOn_integrableOn_eventually_of_avoids
    {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bound : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (hint : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand f γ) volume 0 1) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1 := by
  filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
  exact cpvIntegrandOn_integrableOn_of_avoids hδ_pos hδ_bound hε.1 hε.2 hint

/-- **Version with automatic CPV integrability derivation.**

When `gamma` avoids `S` with margin `delta`, the CPV integrand integrability
hypotheses can be derived from the contour integrand integrability. This
removes the `hI_cpv_rem` and `hI_cpv_sing` hypotheses. -/
private theorem cpvIntegrandOn_sum_eq_of_avoids
    {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bound : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1) :
    (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) =ᶠ[𝓝[>] 0]
    (fun ε =>
      (∫ t in (0 : ℝ)..1,
        cpvIntegrandOn S (fun z => f z -
          principalPartSum S (fun s => residue f s) z) γ.toPath.extend ε t) +
      (∫ t in (0 : ℝ)..1,
        cpvIntegrandOn S (principalPartSum S (fun s => residue f s))
          γ.toPath.extend ε t)) := by
  filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
  have hε_pos : 0 < ε := hε.1
  have hε_lt : ε < δ := hε.2
  have h_f_eq : (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) =
      (fun t => cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z) γ.toPath.extend ε t +
      cpvIntegrandOn S (principalPartSum S (fun s => residue f s))
        γ.toPath.extend ε t) := by
    ext t; rw [← cpvIntegrandOn_add]; congr 1; ext z; ring
  rw [h_f_eq]
  exact intervalIntegral.integral_add
    (cpvIntegrandOn_integrableOn_of_avoids hδ_pos hδ_bound hε_pos hε_lt h_rem_int)
    (cpvIntegrandOn_integrableOn_of_avoids hδ_pos hδ_bound hε_pos hε_lt h_pp_int)

theorem hasCauchyPVOn_simplePoles_convex_auto
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  have h_cancel := hCancel_of_simplePoles_convex hU_convex hU_open hU_ne S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids ⟨δ, hδ_pos, hδ_bound⟩ h_rem_int
  have h_sing := hPV_sing_of_avoids S f γ ⟨δ, hδ_pos, hδ_bound⟩ hI
  simp only [HasCauchyPVOn] at h_cancel h_sing ⊢
  have h_lim := h_cancel.add h_sing
  simp only [zero_add] at h_lim
  exact h_lim.congr' (cpvIntegrandOn_sum_eq_of_avoids hδ_pos hδ_bound h_rem_int h_pp_int).symm

/-! ## Bridge to the full generalized residue theorem -/

/-- **Bridge to `generalizedResidueTheorem`.**

Given conditions (A')+(B), a cancellation oracle, and the structural hypotheses
of `generalizedResidueTheorem`, this constructs all required inputs and applies
the main theorem. The cancellation oracle is the only piece that requires
analytic work; the rest is pure assembly. -/
theorem generalizedResidueTheorem_of_cancel_oracle
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S)
    (h_no_endpt_cross : ∀ s ∈ S,
      γ.toPiecewiseC1Path 0 ≠ s ∧ γ.toPiecewiseC1Path 1 ≠ s)
    (h_unique_cross : ∀ s ∈ S,
      ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ t₂ ∈ Icc (0 : ℝ) 1,
        γ.toPiecewiseC1Path t₁ = s → γ.toPiecewiseC1Path t₂ = s → t₁ = t₂)
    -- Cancellation oracle: the single analytic hypothesis
    (hCancel : HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z)
      γ.toPiecewiseC1Path 0)
    -- Singular part CPV
    (hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s))
    -- Integrability
    (hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (principalPartSum S (fun s => residue f s))
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_rem : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z)
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) :=
  generalizedResidueTheorem hU S hS_in_U f hf γ h_null hMero hCondA hCondB
    h_no_endpt_cross h_unique_cross hCancel hPV_sing hI_sing hI_rem

/-! ## Equivalence: ordinary contour integral vs CPV for avoidance -/

/-- When `gamma` avoids `S`, the ordinary contour integral of `f` and the CPV of `f`
are equal. This bridges between the ordinary-integral formulation of the simple-pole
theorem and the CPV formulation. -/
theorem contourIntegral_eq_of_hasCauchyPVOn_avoids
    {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} {L : ℂ}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_pvon : HasCauchyPVOn S f γ L) :
    γ.contourIntegral f = L := by
  have h_avoids : HasCauchyPVOn S f γ (γ.contourIntegral f) :=
    hasCauchyPVOn_of_avoids hδ
  exact HasCauchyPVOn.unique h_avoids h_pvon

/-! ## Fully-closed form: only minimal hypotheses (item 1 of HW 3.3 closure) -/

/-- **Item 1 — Fully-closed HW 3.3 for simple poles in convex domains.**

This theorem takes ONLY the minimal geometric/analytic hypotheses — no oracle
hypotheses (`hCancel`, `hPV_sing`, `hI_sing`, `hI_rem`) and no integrability
hypotheses on `f ∘ γ * γ'`. The integrability is derived from continuity of `f`
on `U \ S` (from differentiability) via `contourIntegrand_intervalIntegrable_of_continuousOn`,
and the four oracle hypotheses are discharged via
`hasCauchyPVOn_simplePoles_convex_auto`.

This is the cleanest form of HW 3.3 for the simple-pole convex-domain case:
only convexity, openness, simple poles, avoidance, and integrable derivative. -/
theorem hasCauchyPVOn_simplePoles_convex_closed
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_deriv_int : IntervalIntegrable (deriv γ.toPath.extend) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) := by
  -- γ's image lies in U \ S
  have h_img : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U \ (↑S : Set ℂ) := fun t ht =>
    ⟨hγ_in_U t ht, fun hmem => hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
  -- f is continuous on U \ S (from differentiability)
  have hf_cont : ContinuousOn f (U \ ↑S) := hf.continuousOn
  -- Principal part sum is differentiable on (↑S)ᶜ, hence continuous
  have h_pp_cont : ContinuousOn (principalPartSum S (fun s => residue f s))
      (↑S : Set ℂ)ᶜ := (principalPartSum_differentiableOn S _).continuousOn
  have h_img_off_S : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (↑S : Set ℂ)ᶜ := fun t ht =>
    fun hmem => hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl
  -- Derive integrability of principal-part-sum integrand
  have h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1 :=
    PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn γ h_pp_cont h_img_off_S h_deriv_int
  -- Derive integrability of the remainder integrand on U \ S
  have h_rem_cont : ContinuousOn (fun z => f z -
      principalPartSum S (fun s => residue f s) z) (U \ ↑S) := by
    apply hf_cont.sub
    exact h_pp_cont.mono (fun z hz hmem =>
      hz.2 (Finset.mem_coe.mpr (Finset.mem_coe.mp hmem)))
  have h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1 :=
    PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn γ h_rem_cont h_img h_deriv_int
  -- Per-pole integrability: each simple-pole term c/(z-s) is continuous on (s)ᶜ
  have hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1 := by
    intro s hs
    have h_single_cont : ContinuousOn
        (fun z => residue f s / (z - s)) ({s} : Set ℂ)ᶜ :=
      (differentiableOn_div_sub s (residue f s)).continuousOn
    have h_img_off_s : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t ∈ ({s} : Set ℂ)ᶜ :=
      fun t ht hmem => hγ_avoids s hs t ht (mem_singleton_iff.mp hmem)
    have := PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn
      (f := fun z => residue f s / (z - s)) γ h_single_cont h_img_off_s h_deriv_int
    show IntervalIntegrable
      (fun t => residue f s / (γ.toPath.extend t - s) * deriv γ.toPath.extend t) volume 0 1
    exact this
  exact hasCauchyPVOn_simplePoles_convex_auto hU_convex hU_open hU_ne S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids hδ h_rem_int h_pp_int hI

/-- **Item 1 + 4 combined**: contour-integral-form HW 3.3 for simple poles in convex
domains with only minimal hypotheses. -/
theorem contourIntegral_simplePoles_convex_closed
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_deriv_int : IntervalIntegrable (deriv γ.toPath.extend) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s *
        residue f s :=
  contourIntegral_eq_of_hasCauchyPVOn_avoids hδ
    (hasCauchyPVOn_simplePoles_convex_closed hU_convex hU_open hU_ne S hS_in_U
      f hf γ hSimplePoles hγ_in_U hγ_avoids hδ h_deriv_int)

/-! ## Null-homologous closed form (Dixon-zero supplied as one oracle) -/

/-- **HW 3.3 closed form for simple poles in null-homologous null-homologous domains.**

Counterpart of `hasCauchyPVOn_simplePoles_convex_closed` for general
null-homologous curves (not just convex domains). The only remaining input
beyond the null-hom geometric data is the Dixon-zero oracle for the twisted
function `g(z) = (z − w₀) · (f(z) − pp(z))`; callers discharge it via
`dixonFunction_eq_zero_of_bounds` applied to `g`. -/
theorem hasCauchyPVOn_simplePoles_nullHomologous_closed
    {U : Set ℂ} (hU_open : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    -- Existence of w₀ off the curve
    (w₀ : ℂ) (hw₀_in_U : w₀ ∈ U)
    (hw₀_off : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀)
    -- Dixon-zero oracle for the twisted holomorphic remainder
    (h_dixon_zero : ∀ w, dixonFunction
      (fun z => (z - w₀) *
        (f z - principalPartSum S (fun s => residue f s) z)) U γ w = 0)
    -- Integrability hypotheses (can be derived from continuity via
    -- contourIntegrand_intervalIntegrable_of_continuousOn)
    (h_cauchy_int : IntervalIntegrable
      (fun t => (γ t - w₀) *
        (f (γ t) - principalPartSum S (fun s => residue f s) (γ t))
        / (γ t - w₀) * deriv γ.toPath.extend t) volume 0 1)
    (h_base_int : IntervalIntegrable
      (fun t => (γ t - w₀)⁻¹ * deriv γ.toPath.extend t) volume 0 1)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  have h_cancel := hCancel_of_simplePoles_nullHomologous hU_open S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids ⟨δ, hδ_pos, hδ_bound⟩
    w₀ hw₀_in_U hw₀_off h_dixon_zero h_cauchy_int h_base_int
  have h_sing := hPV_sing_of_avoids S f γ ⟨δ, hδ_pos, hδ_bound⟩ hI
  simp only [HasCauchyPVOn] at h_cancel h_sing ⊢
  have h_lim := h_cancel.add h_sing
  simp only [zero_add] at h_lim
  exact h_lim.congr' (cpvIntegrandOn_sum_eq_of_avoids hδ_pos hδ_bound h_rem_int h_pp_int).symm

/-! ## Null-homologous closed form with automatic w₀ from Lipschitz -/

/-- **Variant of `hasCauchyPVOn_simplePoles_nullHomologous_closed` auto-deriving w₀.**

If `γ.toPath.extend` is Lipschitz, the w₀ hypothesis is automatic via A-2's
`exists_mem_not_mem_image_of_isOpen_of_lipschitz`. The existence is packaged
as a classical choice so the returned theorem uses only the same Lipschitz
hypothesis plus the Dixon-zero oracle (plus integrability). -/
theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_of_lipschitz
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    -- Lipschitz hypothesis — supplied by caller for the specific curve
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend)
    -- For each valid w₀, the caller supplies Dixon-zero + integrability
    (dixon_zero_for :
      ∀ w₀ ∈ U, (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ w₀) →
        (∀ w, dixonFunction
          (fun z => (z - w₀) *
            (f z - principalPartSum S (fun s => residue f s) z)) U γ w = 0) ∧
        IntervalIntegrable
          (fun t => (γ t - w₀) *
            (f (γ t) - principalPartSum S (fun s => residue f s) (γ t))
            / (γ t - w₀) * deriv γ.toPath.extend t) volume 0 1 ∧
        IntervalIntegrable
          (fun t => (γ t - w₀)⁻¹ * deriv γ.toPath.extend t) volume 0 1)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) := by
  -- Derive w₀ from A-2
  obtain ⟨w₀, hw₀_in_U, hw₀_off⟩ :=
    ForMathlib.exists_mem_not_mem_path_image_of_isOpen γ hU_open hU_ne hLip
  -- Unpack Dixon-zero + integrability
  obtain ⟨h_dixon_zero, h_cauchy_int, h_base_int⟩ :=
    dixon_zero_for w₀ hw₀_in_U hw₀_off
  exact hasCauchyPVOn_simplePoles_nullHomologous_closed hU_open S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids hδ w₀ hw₀_in_U hw₀_off h_dixon_zero
    h_cauchy_int h_base_int h_rem_int h_pp_int hI

/-! ## B-6: fully-closed null-homologous simple-pole HW 3.3

Combines the W-stream closure (W-5) with the convex-domain B-5 closure
(`dixonFunction_eq_zero_of_nullHomologous_convex_full`) and A-2's automatic
choice of `w₀` to discharge **both** oracle hypotheses of
`hasCauchyPVOn_simplePoles_nullHomologous_closed`. Lipschitz `γ` is the only
non-geometric input. -/

/-- **B-6 (full closure for general open `U`).** For a closed Lipschitz piecewise C¹
immersion `γ` null-homologous in a bounded open set `U`, with simple poles at
`S ⊆ U` avoided by `γ`, the CPV residue formula holds with no oracle hypotheses.
**Non-convex variant** — built on `dixonFunction_eq_zero_of_nullHomologous_open_full`. -/
theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_full
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPiecewiseC1Path t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  have hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U :=
    h_null.image_subset
  -- Lipschitz ⇒ deriv γ ∈ IntervalIntegrable
  have h_deriv_int : IntervalIntegrable (deriv γ.toPath.extend)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  -- A-2: pick w₀ ∈ U off the curve
  obtain ⟨w₀, hw₀_in_U, hw₀_off⟩ :=
    ForMathlib.exists_mem_not_mem_path_image_of_isOpen
      γ.toPiecewiseC1Path hU_open hU_ne hLip
  -- Holomorphic extension `g` of `f - pp` on `U`
  obtain ⟨g, hg_diff, hg_agree⟩ :=
    remainder_differentiableOn_of_simplePoles hU_open S hS_in_U f hf hSimplePoles
  -- B-5 + W-5: dixonFunction (z↦(z-w₀)·g(z)) U γ w = 0 for all w
  have hG_diff : DifferentiableOn ℂ (fun z => (z - w₀) * g z) U := fun z hz =>
    ((differentiableAt_id.sub_const w₀).differentiableWithinAt).mul (hg_diff z hz)
  have h_dixon_G : ∀ w,
      dixonFunction (fun z => (z - w₀) * g z) U γ.toPiecewiseC1Path w = 0 :=
    dixonFunction_eq_zero_of_nullHomologous_open_full hU_open hU_bounded
      hG_diff γ h_null hLip
      (fun w hw_notin h_avoid_local =>
        h_null.winding_zero_nhds_of_not_mem_of_closed hw_notin h_avoid_local hLip)
  -- Pointwise dslope equality on the curve
  have h_dslope_eq : ∀ t ∈ Icc (0 : ℝ) 1,
      dslope (fun z => (z - w₀) *
        (f z - principalPartSum S (fun s => residue f s) z)) w₀
        (γ.toPiecewiseC1Path t) =
      dslope (fun z => (z - w₀) * g z) w₀ (γ.toPiecewiseC1Path t) := by
    intro t ht
    have ht_off_w₀ : γ.toPiecewiseC1Path t ≠ w₀ := hw₀_off t ht
    have ht_off_S : γ.toPiecewiseC1Path t ∉ (↑S : Set ℂ) := fun hmem =>
      hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl
    have ht_in_USmS : γ.toPiecewiseC1Path t ∈ U \ (↑S : Set ℂ) :=
      ⟨hγ_in_U t ht, ht_off_S⟩
    rw [dslope_of_ne _ ht_off_w₀, dslope_of_ne _ ht_off_w₀,
        slope_def_field, slope_def_field, sub_self, zero_mul, zero_mul,
        sub_zero, sub_zero, hg_agree _ ht_in_USmS]
  -- Transfer dixonFunction = 0 at w₀ from h_dixon_G
  have h_dixon_zero_at : dixonFunction
      (fun z => (z - w₀) *
        (f z - principalPartSum S (fun s => residue f s) z))
      U γ.toPiecewiseC1Path w₀ = 0 := by
    have h_eq : dixonFunction
        (fun z => (z - w₀) *
          (f z - principalPartSum S (fun s => residue f s) z))
        U γ.toPiecewiseC1Path w₀ =
        dixonFunction (fun z => (z - w₀) * g z) U γ.toPiecewiseC1Path w₀ := by
      simp only [dixonFunction, hw₀_in_U, if_true, dixonH1]
      refine intervalIntegral.integral_congr (fun t ht => ?_)
      rw [uIcc_of_le (zero_le_one' ℝ)] at ht
      rw [h_dslope_eq t ht]
    rw [h_eq, h_dixon_G w₀]
  -- Avoidance: γ stays away from w₀ with a positive distance δ'
  obtain ⟨δ', hδ'_pos, hδ'_bound⟩ := avoids_delta_bound γ.toPiecewiseC1Path w₀ hw₀_off
  -- Continuity / integrability bookkeeping
  have hf_cont : ContinuousOn f (U \ ↑S) := hf.continuousOn
  have h_pp_cont : ContinuousOn (principalPartSum S (fun s => residue f s))
      (↑S : Set ℂ)ᶜ := (principalPartSum_differentiableOn S _).continuousOn
  have h_img_off_S : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPiecewiseC1Path t ∈ (↑S : Set ℂ)ᶜ := fun t ht hmem =>
    hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl
  have h_img_off_S' : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPiecewiseC1Path t ∈ U \ (↑S : Set ℂ) :=
    fun t ht => ⟨hγ_in_U t ht, h_img_off_S t ht⟩
  have h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ.toPiecewiseC1Path)
      MeasureTheory.volume 0 1 :=
    PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn _
      h_pp_cont h_img_off_S h_deriv_int
  have h_rem_cont : ContinuousOn (fun z => f z -
      principalPartSum S (fun s => residue f s) z) (U \ ↑S) := by
    refine hf_cont.sub (h_pp_cont.mono fun z hz hmem => ?_)
    exact hz.2 (Finset.mem_coe.mpr (Finset.mem_coe.mp hmem))
  have h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z)
        γ.toPiecewiseC1Path) MeasureTheory.volume 0 1 :=
    PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn _
      h_rem_cont h_img_off_S' h_deriv_int
  have hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPiecewiseC1Path.toPath.extend t - s)) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) MeasureTheory.volume 0 1 := by
    intro s hs
    have h_single_cont : ContinuousOn
        (fun z => residue f s / (z - s)) ({s} : Set ℂ)ᶜ :=
      (differentiableOn_div_sub s (residue f s)).continuousOn
    have h_img_off_s : ∀ t ∈ Icc (0 : ℝ) 1,
        γ.toPiecewiseC1Path.toPath.extend t ∈ ({s} : Set ℂ)ᶜ :=
      fun t ht hmem => hγ_avoids s hs t ht (mem_singleton_iff.mp hmem)
    have := PiecewiseC1Path.contourIntegrand_intervalIntegrable_of_continuousOn
      (f := fun z => residue f s / (z - s)) γ.toPiecewiseC1Path h_single_cont
      h_img_off_s h_deriv_int
    show IntervalIntegrable
      (fun t => residue f s / (γ.toPiecewiseC1Path.toPath.extend t - s) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) MeasureTheory.volume 0 1
    exact this
  -- Continuous (γ - w₀)⁻¹ on uIcc 0 1
  have h_inv_cont : ContinuousOn
      (fun t => (γ.toPiecewiseC1Path t - w₀)⁻¹) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    refine ContinuousOn.inv₀
      (γ.toPiecewiseC1Path.toPath.continuous_extend.continuousOn.sub continuousOn_const) ?_
    intro t ht heq
    have := hδ'_bound t ht
    rw [heq, norm_zero] at this; linarith
  -- h_base_int: continuous (γ-w₀)⁻¹ × integrable deriv ⇒ integrable
  have h_base_int : IntervalIntegrable
      (fun t => (γ.toPiecewiseC1Path t - w₀)⁻¹ *
        deriv γ.toPiecewiseC1Path.toPath.extend t)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_inv_cont
  -- h_cauchy_int: simplifies (γ-w₀)·(f-pp)·γ'/(γ-w₀) = (f-pp)·γ' = contourIntegrand (f - pp)
  have h_cauchy_int : IntervalIntegrable
      (fun t => (γ.toPiecewiseC1Path t - w₀) *
        (f (γ.toPiecewiseC1Path t) -
          principalPartSum S (fun s => residue f s) (γ.toPiecewiseC1Path t))
        / (γ.toPiecewiseC1Path t - w₀) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) MeasureTheory.volume 0 1 := by
    refine h_rem_int.congr (fun t ht => ?_)
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have ht_off_w₀ : γ.toPiecewiseC1Path t ≠ w₀ := hw₀_off t ht_Icc
    have h_ne : γ.toPiecewiseC1Path t - w₀ ≠ 0 := sub_ne_zero.mpr ht_off_w₀
    simp only [PiecewiseC1Path.contourIntegrand]
    rw [mul_div_cancel_left₀ _ h_ne]
  -- Finally: assemble via hCancel_at + hPV_sing + composition
  have h_cancel := hCancel_of_simplePoles_nullHomologous_at hU_open S hS_in_U f hf
    γ.toPiecewiseC1Path hSimplePoles hγ_in_U hγ_avoids ⟨δ, hδ_pos, hδ_bound⟩ w₀
    hw₀_in_U hw₀_off h_dixon_zero_at h_cauchy_int h_base_int
  have h_sing := hPV_sing_of_avoids S f γ.toPiecewiseC1Path
    ⟨δ, hδ_pos, hδ_bound⟩ hI
  simp only [HasCauchyPVOn] at h_cancel h_sing ⊢
  have h_lim := h_cancel.add h_sing
  simp only [zero_add] at h_lim
  exact h_lim.congr'
    (cpvIntegrandOn_sum_eq_of_avoids hδ_pos hδ_bound h_rem_int h_pp_int).symm

/-- **Contour integral form of B-6.** Same hypotheses as
`hasCauchyPVOn_simplePoles_nullHomologous_closed_full`, but states the
ordinary contour integral equals the winding-residue formula. The CPV
predicate collapses to the contour integral via avoidance
(`contourIntegral_eq_of_hasCauchyPVOn_avoids`). -/
theorem contourIntegral_simplePoles_nullHomologous_closed_full
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPiecewiseC1Path t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    γ.toPiecewiseC1Path.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s :=
  contourIntegral_eq_of_hasCauchyPVOn_avoids hδ
    (hasCauchyPVOn_simplePoles_nullHomologous_closed_full hU_open hU_ne
      hU_bounded S hS_in_U f hf γ h_null hSimplePoles hγ_avoids hδ hLip)

/-- **Closed null-homologous form of `generalizedResidueTheorem` for simple poles.**

Discharges every oracle of the abstract `generalizedResidueTheorem` (`hCancel`,
`hPV_sing`, `hI_sing`, `hI_rem`, plus the higher-order condition hypotheses
which are automatic for simple poles) and returns the value with `2πi`
factored to the front of the sum, matching the abstract theorem's signature. -/
theorem generalizedResidueTheorem_simplePoles_nullHomologous_closed
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPiecewiseC1Path t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) := by
  have h_target_eq : 2 * ↑Real.pi * I * ∑ s ∈ S,
      generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s =
    ∑ s ∈ S, 2 * ↑Real.pi * I *
      generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h_target_eq]
  exact hasCauchyPVOn_simplePoles_nullHomologous_closed_full hU_open
    hU_ne hU_bounded S hS_in_U f hf γ h_null hSimplePoles hγ_avoids hδ hLip

/-! ## δ-free wrappers (deriving the distance bound from pointwise avoidance) -/

/-- δ-free variant of `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`:
the positive-distance hypothesis `hδ` is auto-derived from pointwise avoidance
and finite `S` via `avoids_finset_delta_bound`. -/
theorem hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) :=
  hasCauchyPVOn_simplePoles_nullHomologous_closed_full hU_open hU_ne
    hU_bounded S hS_in_U f hf γ h_null hSimplePoles hγ_avoids
    (avoids_finset_delta_bound γ.toPiecewiseC1Path S hγ_avoids) hLip

/-- δ-free variant of `contourIntegral_simplePoles_nullHomologous_closed_full`. -/
theorem contourIntegral_simplePoles_nullHomologous_closed_full_avoids
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    γ.toPiecewiseC1Path.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s :=
  contourIntegral_simplePoles_nullHomologous_closed_full hU_open hU_ne
    hU_bounded S hS_in_U f hf γ h_null hSimplePoles hγ_avoids
    (avoids_finset_delta_bound γ.toPiecewiseC1Path S hγ_avoids) hLip

/-- δ-free variant of `generalizedResidueTheorem_simplePoles_nullHomologous_closed`. -/
theorem generalizedResidueTheorem_simplePoles_nullHomologous_closed_avoids
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) :=
  generalizedResidueTheorem_simplePoles_nullHomologous_closed hU_open hU_ne
    hU_bounded S hS_in_U f hf γ h_null hSimplePoles hγ_avoids
    (avoids_finset_delta_bound γ.toPiecewiseC1Path S hγ_avoids) hLip

/-! ## Convex corollary derived as specialization of the general theorem -/

/-- **Generalized Residue Theorem for simple poles in convex domains (via general
theorem).**

Same statement as `generalizedResidueTheorem_simplePoles_convex` but derived as a
specialization of the CPV-form generalized residue theorem
(`hasCauchyPVOn_simplePoles_convex_auto`) + avoidance equivalence
(`contourIntegral_eq_of_hasCauchyPVOn_avoids`). This makes the convex corollary
a bona-fide corollary of the general HW 3.3 machinery rather than a parallel proof. -/
theorem generalizedResidueTheorem_simplePoles_convex_fromGeneral
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s *
        residue f s :=
  contourIntegral_eq_of_hasCauchyPVOn_avoids hδ
    (hasCauchyPVOn_simplePoles_convex_auto hU_convex hU_open hU_ne S hS_in_U
      f hf γ hSimplePoles hγ_in_U hγ_avoids hδ h_rem_int h_pp_int hI)

end
