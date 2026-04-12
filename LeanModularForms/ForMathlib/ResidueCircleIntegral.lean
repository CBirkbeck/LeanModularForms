/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.Residue
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Residue via Circle Integral

Properties of the residue `residue f z₀`, defined as the circle-integral limit
`lim_{r→0⁺} (2πi)⁻¹ ∮_{|z-z₀|=r} f(z) dz`.

## Main results

* `residue_eq_zero_of_analyticAt` — analytic functions have zero residue.
* `residue_eq_zero_of_eventually_differentiableAt` — functions differentiable on a
  neighborhood have zero residue.
* `circleIntegral_simple_pole_eq` — for small `r`, the normalized circle integral of
  a function with a simple pole equals its pole coefficient `c`.
* `residue_eq_of_simple_pole_decomp` — for simple poles, the residue equals the pole
  coefficient.
* `residue_eq_coeff` — `residue f z₀ = h.coeff` when `h : HasSimplePoleAt f z₀`.
* `residue_congr` — residue depends only on local behavior in a punctured neighborhood.
* `norm_two_pi_i_inv_circleIntegral_tendsto_zero` — the normalized circle integral of a
  continuous function tends to zero as the radius tends to zero.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory Metric
open scoped Interval Real

noncomputable section

/-! ### Helpers -/

/-- Two `limUnder`s agree when the functions are eventually equal. -/
private lemma limUnder_eq_of_eventuallyEq {α β : Type*}
    [TopologicalSpace β] [Nonempty β]
    {l : Filter α} {f g : α → β} (h : f =ᶠ[l] g) :
    l.limUnder f = l.limUnder g := by
  unfold Filter.limUnder
  congr 1; ext s
  change f ⁻¹' s ∈ l ↔ g ⁻¹' s ∈ l
  constructor
  · exact fun hs => mem_of_superset (inter_mem hs h) fun x hx => by
      show g x ∈ s; rw [← hx.2]; exact hx.1
  · exact fun hs => mem_of_superset (inter_mem hs h.symm) fun x hx => by
      show f x ∈ s; rw [← hx.2]; exact hx.1

/-- The circle integral of `f` vanishes when `f` is analytic on an open ball strictly
containing the circle. -/
private lemma circleIntegral_eq_zero_of_analyticOnNhd_ball {f : ℂ → ℂ} {z₀ : ℂ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hf : AnalyticOnNhd ℂ f (ball z₀ R)) :
    ∮ z in C(z₀, r), f z = 0 :=
  circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le countable_empty
    (hf.continuousOn.mono (closedBall_subset_ball hrR))
    (fun z ⟨hz, _⟩ => (hf z (ball_subset_ball hrR.le hz)).differentiableAt)

/-! ### Holomorphic / analytic functions have zero residue -/

/-- A function that is analytic at `z₀` has residue zero. -/
theorem residue_eq_zero_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) : residue f z₀ = 0 := by
  unfold residue
  apply Filter.Tendsto.limUnder_eq
  obtain ⟨R, hR_pos, hR_an⟩ := hf.exists_ball_analyticOnNhd
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hR_pos] with r hr_lt hr_pos
  simp only [mem_Ioi] at hr_pos
  simp only [mem_Iio] at hr_lt
  rw [circleIntegral_eq_zero_of_analyticOnNhd_ball hr_pos hr_lt hR_an, mul_zero]

/-- A function that is differentiable on a neighborhood of `z₀` has residue zero. -/
theorem residue_eq_zero_of_eventually_differentiableAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ f z) : residue f z₀ = 0 :=
  residue_eq_zero_of_analyticAt
    (Complex.analyticAt_iff_eventually_differentiableAt.mpr hf)

/-! ### Circle integral for simple poles -/

/-- For small enough `r > 0`, the normalized circle integral of `f` around a simple pole
`z₀` equals the pole coefficient `c`. The `c/(z-z₀)` term contributes `c` via
`circleIntegral.integral_sub_center_inv`, while the analytic remainder integrates
to zero. -/
theorem circleIntegral_simple_pole_eq {f : ℂ → ℂ} {z₀ c : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g z₀)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ),
      (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, r), f z = c := by
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg.exists_ball_analyticOnNhd
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq
  obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq
  have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hr₀_pos] with r hr_lt hr_pos
  simp only [mem_Ioi] at hr_pos
  simp only [mem_Iio] at hr_lt
  have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  -- f agrees with c * (z-z₀)⁻¹ + g on sphere z₀ r
  have h_eq_on : EqOn f (fun z => c * (z - z₀)⁻¹ + g z) (sphere z₀ r) := by
    intro z hz
    have h_ne : z ≠ z₀ := by
      intro heq; rw [heq, mem_sphere, dist_self] at hz; linarith
    have h_in : dist z z₀ < rf := by rw [mem_sphere.mp hz]; exact hr_lt_rf
    have h_mem : z ∈ ball z₀ rf ∩ {z₀}ᶜ :=
      ⟨mem_ball.mpr h_in, mem_compl_singleton_iff.mpr h_ne⟩
    have := hrf_eq h_mem
    simp only [mem_setOf_eq] at this
    rw [this, div_eq_mul_inv]
  -- g is continuous on closedBall z₀ r and circle-integrable
  have h_g_cont : ContinuousOn g (closedBall z₀ r) :=
    hg_ball.continuousOn.mono (closedBall_subset_ball hr_lt_rg)
  have h_ci_g : CircleIntegrable g z₀ r :=
    (h_g_cont.mono sphere_subset_closedBall).circleIntegrable hr_pos.le
  -- (z-z₀)⁻¹ is circle-integrable (z₀ not on sphere when r > 0)
  have h_ci_inv : CircleIntegrable (fun z => (z - z₀)⁻¹) z₀ r :=
    circleIntegrable_sub_inv_iff.mpr (Or.inr (by
      rw [mem_sphere, dist_self, abs_of_pos hr_pos]; exact hr_ne.symm))
  -- c * (z-z₀)⁻¹ is circle-integrable
  have h_ci_cinv : CircleIntegrable (fun z => c * (z - z₀)⁻¹) z₀ r :=
    h_ci_inv.const_fun_smul
  -- Split the integral: ∮ f = c * ∮ (z-z₀)⁻¹ + ∮ g
  have h_int_eq : (∮ z in C(z₀, r), f z) =
      c * (∮ z in C(z₀, r), (z - z₀)⁻¹) + (∮ z in C(z₀, r), g z) := by
    rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
      circleIntegral.integral_add h_ci_cinv h_ci_g,
      circleIntegral.integral_const_mul]
  -- ∮ (z-z₀)⁻¹ = 2πi, ∮ g = 0
  rw [h_int_eq,
    circleIntegral.integral_sub_center_inv z₀ hr_ne,
    circleIntegral_eq_zero_of_analyticOnNhd_ball hr_pos hr_lt_rg hg_ball,
    add_zero]
  -- Algebra: (2πi)⁻¹ * (c * 2πi) = c
  have h2pi_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  field_simp

/-! ### Residue of simple poles -/

/-- For a function with a simple pole decomposition `f(z) = c/(z-z₀) + g(z)`, the
residue equals the pole coefficient `c`. For small `r`, the normalized integral
equals `c` exactly by `circleIntegral_simple_pole_eq`, so the `limUnder` is `c`. -/
theorem residue_eq_of_simple_pole_decomp {f : ℂ → ℂ} {z₀ c : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g z₀)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    residue f z₀ = c := by
  unfold residue
  exact (tendsto_nhds_of_eventually_eq
    (circleIntegral_simple_pole_eq hg hf_eq)).limUnder_eq

/-- For a function with a simple pole at `z₀`, the residue equals `h.coeff`. -/
theorem residue_eq_coeff {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) : residue f z₀ = h.coeff :=
  residue_eq_of_simple_pole_decomp h.regularPart_analyticAt h.eventually_eq

/-! ### Residue is determined by local behavior -/

/-- If `f` and `g` agree in a punctured neighborhood of `z₀`, they have the same
residue. The proof shows that the circle integrals agree for all sufficiently small
radii, so the `limUnder`s coincide. -/
theorem residue_congr {f g : ℂ → ℂ} {z₀ : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] z₀, f z = g z) : residue f z₀ = residue g z₀ := by
  unfold residue
  apply limUnder_eq_of_eventuallyEq
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at h
  obtain ⟨ε, hε_pos, hε⟩ := h
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hε_pos] with r hr_lt hr_pos
  simp only [mem_Ioi] at hr_pos
  simp only [mem_Iio] at hr_lt
  congr 1
  apply circleIntegral.integral_congr hr_pos.le
  intro z hz
  have h_ne : z ≠ z₀ := by
    intro heq; rw [heq, mem_sphere, dist_self] at hz; linarith
  have h_dist : dist z z₀ < ε := by rw [mem_sphere.mp hz]; linarith
  exact hε ⟨mem_ball.mpr h_dist, mem_compl_singleton_iff.mpr h_ne⟩

/-! ### Circle integral norm bound -/

/-- The normalized circle integral of a continuous function tends to zero as `r → 0⁺`.
Uses the bound `‖(2πi)⁻¹ · ∮ g‖ ≤ r · C` from
`circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const`. -/
theorem norm_two_pi_i_inv_circleIntegral_tendsto_zero {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : ContinuousAt g z₀) :
    Tendsto (fun r => (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, r), g z)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  rw [Metric.continuousAt_iff] at hg
  obtain ⟨R, hR_pos, hR_bound⟩ := hg 1 one_pos
  set M := ‖g z₀‖ + 1 with hM_def
  have hM_pos : 0 < M := by positivity
  have hδM : 0 < δ / M := div_pos hδ hM_pos
  refine ⟨min R (δ / M), lt_min hR_pos hδM, fun r hr_pos hr_lt => ?_⟩
  simp only [mem_Ioi] at hr_pos
  simp only [Real.dist_eq, sub_zero] at hr_lt
  have hr_abs : |r| = r := abs_of_pos hr_pos
  have hr_lt_R : r < R := by
    linarith [hr_abs.symm.trans_lt (hr_lt.trans_le (min_le_left R (δ / M)))]
  have hr_lt_δM : r < δ / M := by
    linarith [hr_abs.symm.trans_lt (hr_lt.trans_le (min_le_right R (δ / M)))]
  have h_bound : ∀ z ∈ sphere z₀ r, ‖g z‖ ≤ M := by
    intro z hz
    have h_dist : dist z z₀ < R := by rw [mem_sphere.mp hz]; linarith
    have h_near := hR_bound h_dist
    rw [dist_eq_norm] at h_near
    calc ‖g z‖ = ‖g z₀ + (g z - g z₀)‖ := by ring_nf
    _ ≤ ‖g z₀‖ + ‖g z - g z₀‖ := norm_add_le _ _
    _ ≤ ‖g z₀‖ + 1 := by linarith
  have h_smul_eq : (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, r), g z =
      (2 * ↑Real.pi * I)⁻¹ • ∮ z in C(z₀, r), g z := (smul_eq_mul ..).symm
  rw [dist_eq_norm, sub_zero, h_smul_eq]
  calc ‖(2 * ↑Real.pi * I)⁻¹ • ∮ z in C(z₀, r), g z‖
      ≤ r * M := circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const
        hr_pos.le h_bound
    _ < (δ / M) * M := mul_lt_mul_of_pos_right hr_lt_δM hM_pos
    _ = δ := div_mul_cancel₀ δ (ne_of_gt hM_pos)

end
