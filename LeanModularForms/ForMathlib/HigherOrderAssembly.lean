/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheorem

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

This decomposes `f = (f - pp) + pp` and applies `hasCauchyPVOn_of_tendsto_sub`. -/
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

end
