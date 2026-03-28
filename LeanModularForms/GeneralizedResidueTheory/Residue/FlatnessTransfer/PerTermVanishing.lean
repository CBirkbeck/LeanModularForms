/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.BoundaryVanishing
import LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase

/-!
# Per-Term PV Vanishing and CPV Helpers

Per-term PV vanishing for higher-order polar terms (L4), Laurent circle
integrals, multi-point CPV, holomorphic CPV vanishing, and assembly helpers.

## Main results

* `pv_higher_order_term_tendsto_zero`: single-crossing higher-order PV → 0
* `multipoint_pv_zpow_tendsto_zero`: multi-point CPV of zpow → 0
* `holomorphic_cpv_tendsto_zero_on_convex`: holomorphic CPV → 0 on convex domains
* `tendsto_cpv_of_continuousOn_zero_integral`: CPV → 0 for continuous functions with zero integral
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

/-! ## L4: Per-term PV vanishing for higher-order polar terms

The cutoff integral of `a/(γ(t)-s)^{m}·γ'(t)` (with m ≥ 2) tends to 0 under
the angle condition + flatness, using FTC + boundary vanishing (L3).

The FTC reduces the cutoff integral to boundary terms `(γ(t_exit)-s)^{1-m}/(1-m)`
at the exit points of the ε-ball. These boundary terms are exactly the `w^k`
from L3 with `k = 1-m ≤ -1`, and flatness of order `m` gives
`n + k = m + (1-m) = 1 ≥ 1`. -/

/-- For a single crossing at `t₀` with angle `α`, exponent `m ≥ 2`, and
flatness of order `m`: if `(m-1) · α ∈ 2πℤ`, then the PV cutoff integral
of `(γ-s)^{-m} · γ'` tends to 0.

This combines FTC telescoping (L1) with boundary vanishing (L3). The flatness
hypothesis is essential: without it, the boundary terms `(γ-s)^{1-m}` at the
ε-cutoff points grow as `ε^{1-m} → ∞` and the angle condition alone cannot
compensate. With flatness of order `m`, the direction convergence rate is
`o(ε^{m-1})`, which exactly cancels the `ε^{1-m}` divergence. -/
theorem pv_higher_order_term_tendsto_zero
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (h_angle : ∃ k : ℤ, ((m - 1 : ℕ) : ℝ) * _root_.angleAtCrossing γ t₀ ht₀ =
      ↑k * (2 * Real.pi)) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε
         then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0))
    (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨wR, wL, uR, uL, h_nR, h_nL, h_neR, h_neL, huR, huL,
    h_arg, h_rate_R, h_rate_L, h_eq⟩ :=
    cutoff_zpow_infrastructure γ s m hm t₀ ht₀ hcross h_unique hγ_closed h_flat
  have h_zpow : uR ^ (1 - (m : ℤ)) = uL ^ (1 - (m : ℤ)) := by
    apply unit_zpow_eq_of_angle_multiple _ _ _ huR huL
    obtain ⟨n_a, h_n_a⟩ := h_arg
    obtain ⟨j, hj⟩ := h_angle
    have h1m : 1 ≤ m := by omega
    refine ⟨-j + (1 - (m : ℤ)) * n_a, ?_⟩
    push_cast [Nat.cast_sub h1m] at hj h_n_a ⊢
    have h_expand : (1 - (m : ℝ)) * (arg uR - arg uL) =
        (1 - (m : ℝ)) * _root_.angleAtCrossing γ t₀ ht₀ +
        (1 - (m : ℝ)) * ((n_a : ℝ) * (2 * Real.pi)) := by
      rw [h_n_a]; ring
    linarith
  have h_L3 : Tendsto (fun ε => wR ε ^ (1 - (m : ℤ)) - wL ε ^ (1 - (m : ℤ)))
      (𝓝[>] 0) (𝓝 0) :=
    zpow_boundary_diff_tendsto_zero (1 - (m : ℤ)) (by omega) wR wL
      h_nR h_nL h_neR h_neL uR uL huR huL h_zpow m (by omega) h_rate_R h_rate_L
  have h_bdy : Tendsto
      (fun ε => (wL ε ^ (1 - (m : ℤ)) - wR ε ^ (1 - (m : ℤ))) /
        ((1 : ℂ) - ↑(m : ℤ)))
      (𝓝[>] 0) (𝓝 0) := by
    have h1 := h_L3.neg.div_const ((1 : ℂ) - ↑(m : ℤ))
    simp only [neg_zero, zero_div] at h1
    exact Tendsto.congr (fun ε => by ring) h1
  exact Tendsto.congr' (h_eq.mono fun ε h => h.symm) h_bdy

/-- The CPV integrand of any function is pointwise bounded by
`‖g(γ(t))‖ * ‖γ'(t)‖` (since it's either 0 or `g(γ(t)) * γ'(t)`). -/
private lemma norm_cpvIntegrandOn_le (S0 : Finset ℂ) (g : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    ‖cauchyPrincipalValueIntegrandOn S0 g γ ε t‖ ≤
      ‖g (γ t)‖ * ‖deriv γ t‖ := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs with h
  · simp only [norm_zero]; positivity
  · exact norm_mul_le _ _

/-- CPV integrand of `f` minus CPV integrand of `g` equals CPV integrand of `f - g`,
pointwise, because both use the same indicator set `{t : ∃ s ∈ S0, ‖γ t - s‖ ≤ ε}`. -/
lemma cpvIntegrandOn_sub (S0 : Finset ℂ) (f g : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 f γ ε t -
    cauchyPrincipalValueIntegrandOn S0 g γ ε t =
    cauchyPrincipalValueIntegrandOn S0 (fun z => f z - g z) γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs <;> ring

/-! ### Sublemma 1: Residue equals leading Laurent coefficient -/

/-- Helper: circle integral of a single Laurent term `a / (z - s)^{k+1}`. -/
private theorem circleIntegral_laurent_term
    (s : ℂ) (r : ℝ) (hr_pos : 0 < r) (c : ℂ) (k : ℕ) :
    (∮ z in C(s, r), c / (z - s) ^ (k + 1)) =
      if k = 0 then c * (2 * ↑Real.pi * I) else 0 := by
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_not : s ∉ Metric.sphere s r := by
    simp [hr_ne.symm]
  have h_eq : Set.EqOn (fun z => c / (z - s) ^ (k + 1))
      (fun z => c * (z - s) ^ (-(↑(k + 1) : ℤ))) (Metric.sphere s r) := by
    intro z _
    simp only [div_eq_mul_inv, zpow_neg, zpow_natCast]
  rw [circleIntegral.integral_congr hr_pos.le h_eq,
    circleIntegral.integral_const_mul]
  by_cases hk : k = 0
  · simp only [hk, zero_add, Nat.cast_one, if_true]
    congr 1
    have h_eq' : Set.EqOn (fun z => (z - s) ^ (-(1 : ℤ)))
        (fun z => (z - s)⁻¹) (Metric.sphere s r) := by
      intro z _; simp only [zpow_neg_one]
    rw [circleIntegral.integral_congr hr_pos.le h_eq',
      circleIntegral.integral_sub_center_inv s hr_ne]
  · simp only [hk, if_false]
    rw [circleIntegral.integral_sub_zpow_of_ne, mul_zero]
    intro h_neg_eq
    apply hk
    omega

/-- Helper: circle integral of the Laurent sum equals `a₀ * 2πi`. -/
private theorem circleIntegral_laurent_sum (s : ℂ) (r : ℝ) (hr_pos : 0 < r)
    (N : ℕ) (hN : 0 < N) (a : Fin N → ℂ) :
    (∮ z in C(s, r), ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      a ⟨0, hN⟩ * (2 * ↑Real.pi * I) := by
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_not : s ∉ Metric.sphere s r := by
    simp [hr_ne.symm]
  have h_ci_term : ∀ k : Fin N,
      CircleIntegrable (fun z => a k / (z - s) ^ (k.val + 1)) s r := by
    intro k
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.sub continuousOn_const).pow _
    · intro z hz
      exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))
  have h_push : (∮ z in C(s, r), ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      ∑ k : Fin N, (∮ z in C(s, r), a k / (z - s) ^ (k.val + 1)) := by
    unfold circleIntegral
    have h_smul : ∀ θ : ℝ,
        deriv (circleMap s r) θ •
          (∑ k : Fin N, a k / (circleMap s r θ - s) ^ (k.val + 1)) =
        ∑ k : Fin N,
          deriv (circleMap s r) θ • (a k / (circleMap s r θ - s) ^ (k.val + 1)) :=
      fun θ => Finset.smul_sum
    rw [show (fun θ => deriv (circleMap s r) θ •
          (∑ k : Fin N, a k / (circleMap s r θ - s) ^ (k.val + 1))) =
          fun θ => ∑ k : Fin N,
            deriv (circleMap s r) θ • (a k / (circleMap s r θ - s) ^ (k.val + 1))
      from funext h_smul]
    rw [intervalIntegral.integral_finset_sum]
    intro i _
    exact (h_ci_term i).out
  rw [h_push]
  rw [show (∑ k : Fin N, (∮ z in C(s, r), a k / (z - s) ^ (k.val + 1))) =
      ∑ k : Fin N, if k.val = 0 then a k * (2 * ↑Real.pi * I) else 0
    from Finset.sum_congr rfl (fun k _ => circleIntegral_laurent_term s r hr_pos (a k) k.val)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have h_filter : Finset.filter (fun k : Fin N => k.val = 0) Finset.univ = {⟨0, hN⟩} := by
    ext ⟨j, hj⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => Fin.ext h, fun h => congr_arg Fin.val h⟩
  rw [h_filter, Finset.sum_singleton]

/-- **Sublemma 1**: The residue of `f` at `s` equals the leading Laurent coefficient `a₀`.

Given the Laurent expansion `f(z) = g(z) + Σ_{k=0}^{N-1} aₖ/(z-s)^{k+1}` near `s`,
with `g` analytic at `s`, the circle integral definition of `residueAt` gives
`residueAt f s = a₀`.

Proof strategy: On a small circle of radius `r` around `s`:
- `∮ g = 0` by Cauchy (g analytic → differentiable on disk)
- `∮ (z-s)^{-(k+1)} = 0` for `k ≥ 1` (by `integral_sub_zpow_of_ne`, exponent ≠ -1)
- `∮ (z-s)⁻¹ = 2πi` (by `integral_sub_center_inv`)
- So `∮ f = a₀ · 2πi`, hence `residueAt f s = (2πi)⁻¹ · a₀ · 2πi = a₀`. -/
theorem residueAt_eq_laurent_head_coeff (f : ℂ → ℂ) (s : ℂ) (N : ℕ)
    (hN : 0 < N) (a : Fin N → ℂ) (g : ℂ → ℂ) (hg : AnalyticAt ℂ g s)
    (hf_eq : ∀ᶠ z in 𝓝[≠] s,
      f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) :
    residueAt f s = a ⟨0, hN⟩ := by
  unfold residueAt
  apply Filter.Tendsto.limUnder_eq
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg.exists_ball_analyticOnNhd
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq
  obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq
  have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hr₀_pos] with r hr_lt hr_pos
  simp only [Set.mem_Ioi] at hr_pos
  simp only [Set.mem_Iio] at hr_lt
  have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have h_eq_on : Set.EqOn f
      (fun z => g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) (Metric.sphere s r) := by
    intro z hz
    have h_ne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    have h_in : dist z s < rf := by
      rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf
    exact hrf_eq ⟨Metric.mem_ball.mpr h_in, Set.mem_compl_singleton_iff.mpr h_ne⟩
  have h_g_cont : ContinuousOn g (Metric.closedBall s r) :=
    hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
  have h_ci_g : CircleIntegrable g s r :=
    (h_g_cont.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
  have hs_not : s ∉ Metric.sphere s r := by simp [hr_ne.symm]
  have h_ci_sum : CircleIntegrable
      (fun z => ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) s r := by
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply continuousOn_finset_sum
    intro k _
    apply ContinuousOn.div continuousOn_const
    · exact (continuousOn_id.sub continuousOn_const).pow _
    · intro z hz
      exact pow_ne_zero _ (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))
  have h_int_eq : (∮ z in C(s, r), f z) =
      (∮ z in C(s, r), g z) +
      (∮ z in C(s, r), ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) := by
    rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
      circleIntegral.integral_add h_ci_g h_ci_sum]
  have h_g_zero : (∮ z in C(s, r), g z) = 0 :=
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
      Set.countable_empty h_g_cont
      (fun z ⟨hz, _⟩ => (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)).differentiableAt)
  rw [h_int_eq, h_g_zero, zero_add, circleIntegral_laurent_sum s r hr_pos N hN a]
  have h2pi_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [mul_comm (a ⟨0, hN⟩) _, ← mul_assoc, inv_mul_cancel₀ h2pi_ne, one_mul]

/-- Helper 1: The difference between single-point and multi-point CPV integrands
equals an indicator function a.e. on `Ι γ.a γ.b`. -/
private lemma ae_eq_indicator_diff_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hs : s ∈ S0)
    (f_zpow : ℂ → ℂ) (hf_zpow : f_zpow = fun z => (z - s) ^ (-(m : ℤ)))
    (ε : ℝ) :
    (fun t => (if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0) -
      cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t) =ᵐ[volume.restrict (Ι γ.a γ.b)]
      (({t | ε < ‖γ.toFun t - s‖} \ {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
        Icc γ.a γ.b).indicator
        (fun t => f_zpow (γ.toFun t) * deriv γ.toFun t) := by
  have hIoc_sub : Ι γ.a γ.b ⊆ Icc γ.a γ.b := by
    rw [Set.uIoc_of_le (le_of_lt γ.hab)]; exact Set.Ioc_subset_Icc_self
  filter_upwards [ae_restrict_mem (measurableSet_uIoc)] with t ht
  have ht_Icc : t ∈ Icc γ.a γ.b := hIoc_sub ht
  simp only [cauchyPrincipalValueIntegrandOn, Set.indicator, hf_zpow]
  by_cases h1 : ε < ‖γ.toFun t - s‖ <;>
    by_cases h2 : ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖
  · have h_not_mem :
        ¬(t ∈ ({t | ε < ‖γ.toFun t - s‖} \
          {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
          Icc γ.a γ.b) :=
      fun ⟨⟨_, h_nG⟩, _⟩ => h_nG h2
    simp only [h_not_mem, ite_false, if_pos h1,
      if_neg (show ¬∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε from by push_neg; exact h2)]
    ring
  · push_neg at h2
    obtain ⟨s', hs', hs'_le⟩ := h2
    have h_mem : t ∈ ({t | ε < ‖γ.toFun t - s‖} \
        {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
        Icc γ.a γ.b :=
      ⟨⟨h1, fun h_all =>
        absurd (h_all s' hs') (not_lt.mpr hs'_le)⟩, ht_Icc⟩
    simp only [h_mem, ite_true, if_pos h1,
      if_pos (show ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε from ⟨s', hs', hs'_le⟩)]
    ring
  · push_neg at h1
    have h_not_mem :
        ¬(t ∈ ({t | ε < ‖γ.toFun t - s‖} \
          {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
          Icc γ.a γ.b) :=
      fun ⟨⟨h_far, _⟩, _⟩ => absurd h_far (not_lt.mpr h1)
    simp only [h_not_mem, ite_false,
      if_neg (show ¬‖γ.toFun t - s‖ > ε from not_lt.mpr h1),
      if_pos (show ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε
        from ⟨s, hs, h1⟩)]
    ring
  · push_neg at h1 h2
    have h_not_mem :
        ¬(t ∈ ({t | ε < ‖γ.toFun t - s‖} \
          {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
          Icc γ.a γ.b) :=
      fun ⟨⟨h_far, _⟩, _⟩ => absurd h_far (not_lt.mpr h1)
    obtain ⟨s', hs', hs'_le⟩ := h2
    simp only [h_not_mem, ite_false,
      if_neg (show ¬‖γ.toFun t - s‖ > ε from not_lt.mpr h1),
      if_pos (show ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε
        from ⟨s', hs', hs'_le⟩)]
    ring

/-- Helper 2a: The multi-point "good set"
`{t | ∀ s' ∈ S0, ε < ‖γ(t)-s'‖} ∩ Icc` is measurable. -/
private lemma measurableSet_goodSet_Icc
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (ε : ℝ) :
    MeasurableSet ({t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b) := by
  have h_eq : {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b =
      Icc γ.a γ.b \ ({t | ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b) := by
    ext t; constructor
    · intro ⟨h_good, ht⟩; exact ⟨ht, fun ⟨⟨s', hs', h_le⟩, _⟩ =>
        absurd (h_good s' hs') (not_lt.mpr h_le)⟩
    · intro ⟨ht, h_not⟩; exact ⟨fun s' hs' => by
        by_contra h_le; push_neg at h_le; exact h_not ⟨⟨s', hs', h_le⟩, ht⟩, ht⟩
  rw [h_eq]; apply MeasurableSet.diff isClosed_Icc.measurableSet
  have h_eq2 : {t | ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b =
      ⋃ s' ∈ S0, ({t | ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b) := by
    ext t; simp only [mem_inter_iff, mem_setOf_eq, mem_iUnion, exists_prop]
    exact ⟨fun ⟨⟨s', hs', h⟩, ht⟩ => ⟨s', hs', h, ht⟩,
           fun ⟨s', hs', h, ht⟩ => ⟨⟨s', hs', h⟩, ht⟩⟩
  rw [h_eq2]; apply Finset.measurableSet_biUnion; intro s' _
  have : {t | ‖γ.toFun t - s'‖ ≤ ε} ∩ Icc γ.a γ.b =
      Icc γ.a γ.b \ ({t | ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b) := by
    ext t; simp only [mem_inter_iff, mem_setOf_eq, mem_diff, not_and]; constructor
    · intro ⟨h_le, ht⟩; exact ⟨ht, fun h_gt => absurd h_gt (not_lt.mpr h_le)⟩
    · intro ⟨ht, h_not⟩; exact ⟨le_of_not_gt (fun h => (h_not h) ht), ht⟩
  rw [this]; exact isClosed_Icc.measurableSet.diff
    (measurableSet_norm_gt_Icc ε
      (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const))

/-- The derivative `deriv γ.toFun` is AEStronglyMeasurable on `Icc γ.a γ.b` for
any `PiecewiseC1Immersion γ`, because it is continuous off the finite partition set. -/
private lemma aesm_deriv_on_Icc (γ : PiecewiseC1Immersion) :
    AEStronglyMeasurable (deriv γ.toFun) (volume.restrict (Icc γ.a γ.b)) :=
  aEStronglyMeasurable_of_continuousOn_off_finite (P := γ.partition) (by
    intro t ⟨ht_Icc, ht_nP⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b :=
      ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm fun h =>
        ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.1)),
       lt_of_le_of_ne ht_Icc.2 fun h =>
        ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.2)⟩
    exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
      t ht_Ioo ht_nP).continuousWithinAt)

/-- Helper 2b: `(z-s)^{-m} ∘ γ · γ'` is AEStronglyMeasurable on the "single far" set. -/
private lemma aesm_zpow_on_singleFar
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    AEStronglyMeasurable
      (fun t => (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t)
      (volume.restrict ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b)) := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  have hSF_meas : MeasurableSet ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) :=
    measurableSet_norm_gt_Icc ε (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const)
  have hf_cont : ContinuousOn (fun t => f_zpow (γ.toFun t))
      ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) := by
    have hf_zpow_cont : ContinuousOn f_zpow {z : ℂ | z - s ≠ 0} :=
      ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const) (-(m : ℤ))
        (fun z hz => Or.inl hz)
    have h_maps : Set.MapsTo γ.toFun
        ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) {z | z - s ≠ 0} := by
      intro t ⟨ht_far, _⟩
      change γ.toFun t - s ≠ 0
      exact sub_ne_zero.mpr (fun heq => by
        have : ε < ‖γ.toFun t - s‖ := ht_far
        rw [heq, sub_self, norm_zero] at this; linarith)
    exact hf_zpow_cont.comp
      (γ.toPiecewiseC1Curve.continuous_toFun.mono Set.inter_subset_right) h_maps
  exact (hf_cont.aestronglyMeasurable hSF_meas).mul
    ((aesm_deriv_on_Icc γ).mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))

/-- Helper 2: The difference between single-point and multi-point CPV integrands
of `(z-s)^{-m}` is AEStronglyMeasurable on `Ι γ.a γ.b`. Assembled from
`ae_eq_indicator_diff_cpv_zpow`, `aesm_zpow_on_singleFar`, and
`measurableSet_goodSet_Icc`. -/
private lemma aesm_diff_single_multi_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0)
    (ε : ℝ) (hε : 0 < ε) :
    AEStronglyMeasurable
      (fun t => (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
        cauchyPrincipalValueIntegrandOn S0 (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
      (volume.restrict (Ι γ.a γ.b)) := by
  have h_diff_ae := ae_eq_indicator_diff_cpv_zpow S0 γ s m hs
    (fun z => (z - s) ^ (-(m : ℤ))) rfl ε
  apply AEStronglyMeasurable.congr _ h_diff_ae.symm
  have hSF_meas : MeasurableSet ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) :=
    measurableSet_norm_gt_Icc ε (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const)
  have hSG_sub :
      ({t | ε < ‖γ.toFun t - s‖} \
        {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩
        Icc γ.a γ.b ⊆
      {t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b :=
    Set.inter_subset_inter_left _ Set.diff_subset
  have hSG_meas : MeasurableSet (({t | ε < ‖γ.toFun t - s‖} \
      {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩ Icc γ.a γ.b) := by
    rw [show ({t | ε < ‖γ.toFun t - s‖} \
        {t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}) ∩ Icc γ.a γ.b =
      ({t | ε < ‖γ.toFun t - s‖} ∩ Icc γ.a γ.b) \
        ({t | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖} ∩ Icc γ.a γ.b) from by
        ext x; simp only [mem_inter_iff, mem_diff]; tauto]
    exact hSF_meas.diff (measurableSet_goodSet_Icc S0 γ ε)
  apply ((AEStronglyMeasurable.piecewise hSG_meas
    ((aesm_zpow_on_singleFar γ s m ε hε).mono_measure (Measure.restrict_mono hSG_sub le_rfl))
    (aestronglyMeasurable_const (α := ℝ) (β := ℂ))).mono_measure
      Measure.restrict_le_self).congr
  filter_upwards with t
  simp only [Set.piecewise, Set.indicator]

/-- A.e. `t` in the integration interval `Ι γ.a γ.b` does not land on any
point of `S0` under `γ`, because each crossing set is finite (hence null). -/
private lemma ae_forall_ne_of_finite_crossings
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b → ∀ s ∈ S0, γ.toFun t ≠ s := by
  have h_preimage_finite : (⋃ s ∈ S0, {t ∈ Icc γ.a γ.b | γ.toFun t = s}).Finite :=
    Set.Finite.biUnion S0.finite_toSet (fun s _ => finite_crossings γ s)
  rw [Filter.eventually_iff, mem_ae_iff]
  refine le_antisymm ?_ (zero_le _)
  calc volume {t | ¬(t ∈ Ι γ.a γ.b → ∀ s ∈ S0, γ.toFun t ≠ s)}
      ≤ volume (⋃ s ∈ S0, {t ∈ Icc γ.a γ.b | γ.toFun t = s}) := by
        apply measure_mono; intro t ht; push_neg at ht
        obtain ⟨ht_in, s, hs, hts⟩ := ht
        exact Set.mem_biUnion hs
          ⟨Ioc_subset_Icc_self (Set.uIoc_of_le γ.hab.le ▸ ht_in), hts⟩
    _ = 0 := h_preimage_finite.measure_zero _

/-! ### Sublemma 2: Multi-point CPV of higher-order pole term → 0 -/

/-- Norm bound for the zpow integrand: if `‖γ(t) - s‖ > ε` then
`‖(γ(t)-s)^{-m} · γ'(t)‖ ≤ ε⁻¹^m · (|Mγ'| + 1)`. -/
private lemma zpow_deriv_norm_bound
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Icc γ.a γ.b)
    (h_far : ‖γ.toFun t - s‖ > ε) :
    ‖(fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t‖ ≤
      ε⁻¹ ^ m * (|Mγ'| + 1) := by
  calc ‖(fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t‖
      ≤ ‖(fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t)‖ * ‖deriv γ.toFun t‖ :=
        norm_mul_le _ _
    _ ≤ ε⁻¹ ^ m * (|Mγ'| + 1) := by
        apply mul_le_mul
        · simp only []
          rw [norm_zpow, zpow_neg, zpow_natCast, inv_pow]
          exact inv_anti₀ (by positivity)
            (pow_le_pow_left₀ hε.le h_far.le m)
        · exact le_trans
            ((hMγ' t ht).trans (le_abs_self _))
            (le_add_of_nonneg_right one_pos.le)
        · exact norm_nonneg _
        · positivity

/-- The single-point cutoff integrand of `(z-s)^{-m} · γ'` is interval integrable. -/
private lemma single_cutoff_zpow_intervalIntegrable
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε then
        (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0)
      volume γ.a γ.b := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  rw [show (fun t => if ‖γ.toFun t - s‖ > ε then
      f_zpow (γ.toFun t) * deriv γ.toFun t else 0) =
    (fun t =>
      cauchyPrincipalValueIntegrandOn {s} f_zpow γ.toFun ε t) from
    funext fun t => by rw [cauchyPrincipalValueIntegrandOn_singleton]]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt γ.hab)]
  refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
  refine integrableOn_of_bounded_aeMeasurable (M := ε⁻¹ ^ m * (|Mγ'| + 1)) ?_ ?_
  · have h_aesm_if : AEStronglyMeasurable
        (fun t => if ε < ‖γ.toFun t - s‖ then f_zpow (γ.toFun t) * deriv γ.toFun t else 0)
        (volume.restrict (Icc γ.a γ.b)) := by
      apply aEStronglyMeasurable_pv_integrand_piecewiseC1
        (P := γ.partition) (z₀ := s)
      · intro z ⟨_, hz_not_ball⟩
        have hz_ne : z ≠ s := by
          intro heq; exact hz_not_ball (by rw [Metric.mem_ball, heq, dist_self]; exact hε)
        exact ((continuousAt_id.sub continuousAt_const).zpow₀ (-(m : ℤ))
          (Or.inl (sub_ne_zero.mpr hz_ne))).continuousWithinAt
      · exact γ.toPiecewiseC1Curve.continuous_toFun
      · intro t ⟨ht_Icc, ht_nP⟩
        have ht_Ioo : t ∈ Ioo γ.a γ.b := by
          refine ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm fun h =>
            ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.1)), ?_⟩
          exact lt_of_le_of_ne ht_Icc.2 fun h =>
            ht_nP (h ▸ γ.toPiecewiseC1Curve.endpoints_in_partition.2)
        exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
          t ht_Ioo ht_nP).continuousWithinAt
    exact h_aesm_if.congr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t _
      exact (cauchyPrincipalValueIntegrandOn_singleton f_zpow γ.toFun s ε t).symm)
  · intro t ht
    rw [cauchyPrincipalValueIntegrandOn_singleton]
    split_ifs with h
    · exact zpow_deriv_norm_bound γ s m Mγ' hMγ' ε hε t ht h
    · simp only [norm_zero]; positivity

/-- The multi-point cutoff integrand of `(z-s)^{-m} · γ'` is interval integrable. -/
private lemma multi_cutoff_zpow_intervalIntegrable
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
      volume γ.a γ.b := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt γ.hab)]
  refine IntegrableOn.mono_set ?_ Ioc_subset_Icc_self
  refine integrableOn_of_bounded_aeMeasurable (M := ε⁻¹ ^ m * (|Mγ'| + 1)) ?_ ?_
  · let GoodSet := {t : ℝ | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}
    have hGoodSet_meas : MeasurableSet (GoodSet ∩ Icc γ.a γ.b) :=
      measurableSet_goodSet_Icc S0 γ ε
    have hfγ_cont_good : ContinuousOn (fun t => f_zpow (γ.toFun t))
        (GoodSet ∩ Icc γ.a γ.b) := by
      have hf_cont : ContinuousOn f_zpow {z : ℂ | z - s ≠ 0} :=
        ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const) (-(m : ℤ))
          (fun z hz => Or.inl hz)
      have h_maps : Set.MapsTo γ.toFun (GoodSet ∩ Icc γ.a γ.b) {z | z - s ≠ 0} := by
        intro t ⟨ht_good, _⟩
        exact sub_ne_zero.mpr (fun heq => by
          have := ht_good s hs; rw [heq, sub_self, norm_zero] at this; linarith)
      exact hf_cont.comp
        (γ.toPiecewiseC1Curve.continuous_toFun.mono Set.inter_subset_right) h_maps
    have hγ'_meas := aesm_deriv_on_Icc γ
    have h_prod_meas : AEStronglyMeasurable (fun t => f_zpow (γ.toFun t) * deriv γ.toFun t)
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)) :=
      (hfγ_cont_good.aestronglyMeasurable hGoodSet_meas).mul
        (hγ'_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
    have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)ᶜ) := aestronglyMeasurable_const
    have h_pw := AEStronglyMeasurable.piecewise hGoodSet_meas h_prod_meas h_zero_meas
    exact (h_pw.mono_measure Measure.restrict_le_self).congr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [cauchyPrincipalValueIntegrandOn]
      by_cases ht_good : t ∈ GoodSet ∩ Icc γ.a γ.b
      · rw [Set.piecewise_eq_of_mem _ _ _ ht_good]
        have : ¬∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε := by push_neg; exact ht_good.1
        rw [if_neg this]
      · rw [Set.piecewise_eq_of_notMem _ _ _ ht_good]
        have : ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε := by
          by_contra h; push_neg at h; exact ht_good ⟨h, ht⟩
        rw [if_pos this])
  · intro t ht
    simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h
    · simp only [norm_zero]; positivity
    · push_neg at h; exact zpow_deriv_norm_bound γ s m Mγ' hMγ' ε hε t ht (h s hs)

/-- DCT bound for the difference between single-point and multi-point CPV
integrands: when `ε < δ_sep / 2`, the difference is bounded by
`(δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1)`. -/
private lemma dct_bound_diff_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0) (_hS0_single : S0 ≠ {s})
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (δ_sep : ℝ) (hδ_pos : 0 < δ_sep)
    (hδ_sep_le : ∀ s' ∈ S0.erase s, δ_sep ≤ ‖s - s'‖)
    (ε : ℝ) (hε : ε ∈ Ioo 0 (δ_sep / 2)) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      ‖(if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
        cauchyPrincipalValueIntegrandOn S0
          (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t‖ ≤
      (δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1) := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  apply ae_of_all; intro t ht
  simp only [cauchyPrincipalValueIntegrandOn]
  by_cases h_multi_cut : ∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε
  · rw [if_pos h_multi_cut]
    by_cases h_single_cut : ‖γ.toFun t - s‖ > ε
    · rw [if_pos h_single_cut]; simp only [sub_zero]
      obtain ⟨s', hs', hs'_close⟩ := h_multi_cut
      have hs'_ne : s' ≠ s := by intro heq; rw [heq] at hs'_close; linarith
      have h_sep_s' : δ_sep ≤ ‖s - s'‖ :=
        hδ_sep_le s' (Finset.mem_erase.mpr ⟨hs'_ne, hs'⟩)
      have h_far : ‖γ.toFun t - s‖ ≥ δ_sep / 2 := by
        have h1 : ‖s - s'‖ ≤ ‖γ.toFun t - s‖ + ‖γ.toFun t - s'‖ := by
          calc ‖s - s'‖ = ‖(s - γ.toFun t) + (γ.toFun t - s')‖ := by ring_nf
            _ ≤ ‖s - γ.toFun t‖ + ‖γ.toFun t - s'‖ := norm_add_le _ _
            _ = ‖γ.toFun t - s‖ + ‖γ.toFun t - s'‖ := by rw [norm_sub_rev]
        linarith [hε.2]
      have ht_Icc : t ∈ Icc γ.a γ.b :=
        Ioc_subset_Icc_self (Set.uIoc_of_le γ.hab.le ▸ ht)
      calc ‖f_zpow (γ.toFun t) * deriv γ.toFun t‖
          ≤ ‖f_zpow (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul_le _ _
        _ ≤ (δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1) := by
            apply mul_le_mul
            · change ‖f_zpow (γ.toFun t)‖ ≤ (δ_sep / 2)⁻¹ ^ m
              simp only [f_zpow]
              rw [norm_zpow, zpow_neg, zpow_natCast, inv_pow]
              exact inv_anti₀ (by positivity)
                (pow_le_pow_left₀ (by linarith) h_far m)
            · exact le_trans ((hMγ' t ht_Icc).trans (le_abs_self _))
                (le_add_of_nonneg_right one_pos.le)
            · exact norm_nonneg _
            · positivity
    · push_neg at h_single_cut; rw [if_neg (not_lt.mpr h_single_cut)]
      norm_num; positivity
  · rw [if_neg h_multi_cut]
    by_cases h_single_cut : ‖γ.toFun t - s‖ > ε
    · rw [if_pos h_single_cut]; norm_num; positivity
    · push_neg at h_single_cut h_multi_cut
      exact absurd (h_multi_cut s hs) (not_lt.mpr h_single_cut)

/-- A.e. pointwise limit of the single-multi CPV difference is 0 when `t` does
not land on any point of `S0`. -/
private lemma ae_limit_diff_cpv_zpow
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0) (hS0_ne : S0.Nonempty) :
    ∀ᵐ t ∂volume, t ∈ Ι γ.a γ.b →
      Tendsto (fun ε =>
        (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
        cauchyPrincipalValueIntegrandOn S0
          (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_forall_ne_of_finite_crossings S0 γ] with t h_not_cross ht_in
  have h_nc := h_not_cross ht_in
  apply tendsto_const_nhds.congr'
  let δ_t := S0.inf' hS0_ne (fun s' => ‖γ.toFun t - s'‖)
  have hδ_t_pos : 0 < δ_t := by
    apply (Finset.lt_inf'_iff _).mpr
    intro s' hs'; exact norm_pos_iff.mpr (sub_ne_zero.mpr (h_nc s' hs'))
  filter_upwards [Ioo_mem_nhdsGT hδ_t_pos] with ε hε
  simp only [cauchyPrincipalValueIntegrandOn]
  have h_no_near : ¬∃ s' ∈ S0, ‖γ.toFun t - s'‖ ≤ ε := by
    push_neg; intro s' hs'
    exact lt_of_lt_of_le hε.2 (Finset.inf'_le _ hs')
  rw [if_neg h_no_near]
  have h_far_s : ‖γ.toFun t - s‖ > ε :=
    lt_of_lt_of_le hε.2 (Finset.inf'_le _ hs)
  rw [if_pos h_far_s]; ring

/-- Reduce the multi-point CPV goal to showing the single-multi difference
tends to 0, using `Tendsto.sub` and `integral_sub`. -/
private lemma reduce_to_diff_tendsto_zero
    (S0 : Finset ℂ) (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (hs : s ∈ S0)
    (Mγ' : ℝ) (hMγ' : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ Mγ')
    (h_single : Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0))
      (𝓝[>] 0) (𝓝 0))
    (h_diff : Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        ((if ‖γ.toFun t - s‖ > ε then
            (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
         cauchyPrincipalValueIntegrandOn S0
           (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  set f_zpow := fun z => (z - s) ^ (-(m : ℤ)) with hf_zpow_def
  have h_single_int : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable
        (fun t => if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0)
        volume γ.a γ.b :=
    fun ε hε => single_cutoff_zpow_intervalIntegrable γ s m Mγ' hMγ' ε hε
  have h_multi_int : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable
        (fun t => cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t)
        volume γ.a γ.b :=
    fun ε hε => multi_cutoff_zpow_intervalIntegrable S0 γ s m hs Mγ' hMγ' ε hε
  have h_eventually_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t =
      (∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0)) -
      ∫ t in γ.a..γ.b,
        ((if ‖γ.toFun t - s‖ > ε then f_zpow (γ.toFun t) * deriv γ.toFun t else 0) -
         cauchyPrincipalValueIntegrandOn S0 f_zpow γ.toFun ε t) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    rw [← intervalIntegral.integral_sub (h_single_int ε hε)
      ((h_single_int ε hε).sub (h_multi_int ε hε))]
    congr 1; ext t; ring
  have h_sub := h_single.sub h_diff
  simp only [sub_self] at h_sub
  exact h_sub.congr' (h_eventually_eq.mono fun ε h => h.symm)

/-- **Sublemma 2**: The multi-point CPV integral of `(z-s)^{-m}` tends to 0
for `m ≥ 2`, given flatness of order `m` and the angle condition.

This extends `pv_higher_order_term_tendsto_zero` from single-point to
multi-point cutoff. The difference between multi-point and single-point
cutoffs is supported on a set where `(z-s)^{-m}` is bounded (far from `s`,
near some other `s' ∈ S0`) and whose measure tends to 0. -/
theorem multipoint_pv_zpow_tendsto_zero (S0 : Finset ℂ)
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m) (hs : s ∈ S0)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (h_angle : ∃ k : ℤ, ((m - 1 : ℕ) : ℝ) * _root_.angleAtCrossing γ t₀ ht₀ =
      ↑k * (2 * Real.pi)) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  have h_single : Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε then
          (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0))
      (𝓝[>] 0) (𝓝 0) :=
    pv_higher_order_term_tendsto_zero γ s m hm t₀ ht₀ hcross h_unique
      hγ_closed h_flat h_angle
  apply reduce_to_diff_tendsto_zero S0 γ s m hs Mγ' hMγ' h_single
  by_cases hS0_single : S0 = {s}
  · apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    show 0 = _
    rw [show (∫ t in γ.a..γ.b,
          ((if ‖γ.toFun t - s‖ > ε then
              (fun z => (z - s) ^ (-(m : ℤ))) (γ.toFun t) * deriv γ.toFun t else 0) -
           cauchyPrincipalValueIntegrandOn S0
             (fun z => (z - s) ^ (-(m : ℤ))) γ.toFun ε t)) =
        ∫ t in γ.a..γ.b, (0 : ℂ) from by
      congr 1; ext t
      rw [hS0_single, cauchyPrincipalValueIntegrandOn_singleton]; ring_nf]
    simp only [intervalIntegral.integral_zero]
  · have hS0_ne : S0.Nonempty := ⟨s, hs⟩
    let δ_sep := (S0.erase s).inf' (by
      exact (Finset.erase_nonempty hs).mpr
        ((Finset.nontrivial_iff_ne_singleton hs).mpr hS0_single))
      (fun s' => ‖s - s'‖)
    have hδ_pos : 0 < δ_sep := by
      apply (Finset.lt_inf'_iff _).mpr
      intro s' hs'
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (ne_of_mem_erase hs').symm)
    have hδ_sep_le : ∀ s' ∈ S0.erase s, δ_sep ≤ ‖s - s'‖ :=
      fun s' hs' => Finset.inf'_le _ hs'
    have h_dct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (δ_sep / 2)⁻¹ ^ m * (|Mγ'| + 1))
      (by filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
          exact aesm_diff_single_multi_cpv_zpow S0 γ s m hs ε hε)
      (by filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < δ_sep / 2 by linarith)]
            with ε hε
          exact dct_bound_diff_cpv_zpow S0 γ s m hs hS0_single Mγ' hMγ'
            δ_sep hδ_pos hδ_sep_le ε hε)
      intervalIntegrable_const
      (ae_limit_diff_cpv_zpow S0 γ s m hs hS0_ne)
    simp only [intervalIntegral.integral_zero] at h_dct
    exact h_dct
/-! ### Helper: CPV of a function continuous along γ with zero contour integral

If g is continuous on γ's image and ∮_γ g dz = 0, then cpv(S0, g, ε) → 0.
The CPV integrand converges a.e. to g(γ(t)) * γ'(t) as ε → 0 (the crossing
set has measure zero), and is dominated by ‖g(γ(t))‖ * ‖γ'(t)‖. By DCT, the
limit equals ∮_γ g dz = 0. -/

/-- CPV integral of a function continuous along γ with zero ordinary contour
integral tends to 0. This is the DCT core of the assembly proof, abstracting
the zero-integral condition. -/
theorem tendsto_cpv_of_continuousOn_zero_integral
    (S0 : Finset ℂ) (g : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hg_cont : ContinuousOn g (γ.toFun '' Icc γ.a γ.b))
    (h_integral_zero : ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hγ'_bdd := piecewiseC1Immersion_deriv_bounded γ
  have hgγ_cont : ContinuousOn (fun t => g (γ.toFun t)) (Set.uIcc γ.a γ.b) := by
    rw [Set.uIcc_of_le (le_of_lt γ.hab)]
    exact hg_cont.comp hγ_cont (fun t ht => Set.mem_image_of_mem _ ht)
  have h_ord_int : IntervalIntegrable (fun t => g (γ.toFun t) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ'_bdd).continuousOn_mul
      hgγ_cont
  rw [← h_integral_zero]
  have h_ae_not_in_S0 := ae_forall_ne_of_finite_crossings S0 γ
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖g (γ.toFun t) * deriv γ.toFun t‖)
    (by filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
        have h_int := intervalIntegrable_cauchyPrincipalValueIntegrandOn (S0 := S0) hε hg_cont
        rw [intervalIntegrable_iff] at h_int
        exact h_int.aestronglyMeasurable)
    (by filter_upwards [self_mem_nhdsWithin] with ε (_hε : (0 : ℝ) < ε)
        apply ae_of_all; intro t ht
        simp only [cauchyPrincipalValueIntegrandOn]
        split_ifs
        · simp only [norm_zero]; exact norm_nonneg _
        · exact le_refl _)
    h_ord_int.norm
    (by filter_upwards [h_ae_not_in_S0] with t h_not_in ht_in
        simp only [cauchyPrincipalValueIntegrandOn]
        have h_not_in' := h_not_in ht_in
        by_cases hS0_empty : S0 = ∅
        · have : ∀ ε, ¬∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε := by
            intro ε h_ex; obtain ⟨s, hs, _⟩ := h_ex
            exact absurd hs (hS0_empty ▸ Finset.notMem_empty s)
          apply tendsto_const_nhds.congr'
          filter_upwards with ε; rw [if_neg (this ε)]
        · have hS0_ne : S0.Nonempty := Finset.nonempty_of_ne_empty hS0_empty
          let δ := S0.inf' hS0_ne (fun s => ‖γ.toFun t - s‖)
          have hδ_pos : 0 < δ :=
            (Finset.lt_inf'_iff hS0_ne).mpr (fun s hs =>
              norm_pos_iff.mpr (sub_ne_zero.mpr (h_not_in' s hs)))
          apply tendsto_const_nhds.congr'
          filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
          have h_no_near : ¬∃ s ∈ S0, ‖γ.toFun t - s‖ ≤ ε := by
            push_neg; intro s hs
            exact lt_of_lt_of_le hε.2 (Finset.inf'_le _ hs)
          rw [if_neg h_no_near])

/-! ### Sublemma 3: Holomorphic CPV integral → 0 on closed curve -/

/-- **Sublemma 3**: For a function holomorphic on a convex open `U` containing the
closed curve `γ`, the multi-point CPV integral tends to 0.

The CPV integrand `1_{∀s∈S0, ‖γ(t)-s‖>ε} · g(γ(t)) · γ'(t)` converges a.e.
to `g(γ(t)) · γ'(t)` as `ε → 0` (the cutout set shrinks to a null set), and
is dominated by `‖g(γ(t))‖ · ‖γ'(t)‖` (bounded since `g` is continuous on
the compact image of `γ`). By DCT, the CPV integral converges to the ordinary
integral `∮_γ g dz`, which is 0 by Cauchy's integral theorem on convex `U`. -/
theorem holomorphic_cpv_tendsto_zero_on_convex (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U) (S0 : Finset ℂ) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g U) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    Tendsto (fun ε =>
      ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hg_cont_U : ContinuousOn g U := hg.continuousOn
  have hg_cont_image : ContinuousOn g (γ.toFun '' Icc γ.a γ.b) :=
    hg_cont_U.mono (Set.image_subset_iff.mpr (fun t ht => hγ_in_U t ht))
  have hgγ_cont : ContinuousOn (fun t => g (γ.toFun t)) (Set.uIcc γ.a γ.b) := by
    rw [Set.uIcc_of_le (le_of_lt γ.hab)]
    exact hg_cont_U.comp hγ_cont (fun t ht => hγ_in_U t ht)
  have hγ'_bdd := piecewiseC1Immersion_deriv_bounded γ
  have h_ord_int : IntervalIntegrable (fun t => g (γ.toFun t) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ'_bdd).continuousOn_mul
      hgγ_cont
  have hU_ne : U.Nonempty :=
    ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr (le_of_lt γ.hab))⟩
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU hU_ne hg
  have h_Fγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) := by
    intro t ht
    exact ((hF (γ.toFun t) (hγ_in_U t ht)).continuousAt).continuousWithinAt.comp
      (hγ_cont t ht) (mapsTo_image γ.toFun _)
  have h_countable : (↑γ.partition ∩ Ioo γ.a γ.b : Set ℝ).Countable :=
    (γ.partition.finite_toSet.inter_of_left _).countable
  have h_deriv' : ∀ t ∈ Ioo γ.a γ.b \ (↑γ.partition ∩ Ioo γ.a γ.b),
      HasDerivAt (F ∘ γ.toFun) (g (γ.toFun t) * deriv γ.toFun t) t := by
    intro t ⟨ht, hp⟩
    exact (hF (γ.toFun t) (hγ_in_U t (Ioo_subset_Icc_self ht))).comp_of_eq t
      ((γ.smooth_off_partition t (Ioo_subset_Icc_self ht)
        (fun h => hp ⟨h, ht⟩)).hasDerivAt) rfl
  have h_ord_zero : ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0 := by
    have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      (F ∘ γ.toFun) (fun t => g (γ.toFun t) * deriv γ.toFun t) (le_of_lt γ.hab)
      h_countable h_Fγ_cont h_deriv' h_ord_int
    rw [h_ftc, Function.comp_apply, Function.comp_apply,
      (hγ_closed : γ.toFun γ.a = γ.toFun γ.b), sub_self]
  exact tendsto_cpv_of_continuousOn_zero_integral S0 g γ hg_cont_image h_ord_zero

/-! ### Helper: CPV integral of scalar multiple -/

/-- CPV integrand of `c • f` equals `c • cpv(f)` pointwise (the indicator set is the same). -/
lemma cpvIntegrandOn_const_smul (S0 : Finset ℂ) (c : ℂ) (f : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 (fun z => c * f z) γ ε t =
    c * cauchyPrincipalValueIntegrandOn S0 f γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs <;> ring

/-- CPV integrand of `f + g` equals `cpv(f) + cpv(g)` pointwise (same indicator). -/
lemma cpvIntegrandOn_add (S0 : Finset ℂ) (f g : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 (fun z => f z + g z) γ ε t =
    cauchyPrincipalValueIntegrandOn S0 f γ ε t +
    cauchyPrincipalValueIntegrandOn S0 g γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs <;> ring

/-- CPV integrand of a finset sum decomposes. -/
lemma cpvIntegrandOn_finset_sum {ι : Type*} (S0 : Finset ℂ) (T : Finset ι)
    (f : ι → ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrandOn S0 (fun z => ∑ i ∈ T, f i z) γ ε t =
    ∑ i ∈ T, cauchyPrincipalValueIntegrandOn S0 (f i) γ ε t := by
  simp only [cauchyPrincipalValueIntegrandOn]
  split_ifs with h
  · simp only [Finset.sum_const_zero]
  · simp only [Finset.sum_mul]

/-- Integrability of CPV integrand for functions continuous on U \ S0.
For any g continuous on U \ S0 with γ mapping into U, the multi-point CPV
integrand is interval integrable on [a,b] for fixed ε > 0. The key insight
is that the CPV integrand is bounded (it's either 0 or g(γ(t)) * γ'(t) where
γ(t) is far from all poles) and ae strongly measurable (continuous off a finite
set within [a,b]). -/
lemma intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
    (U : Set ℂ) (S0 : Finset ℂ) (g : ℂ → ℂ)
    (hg_cont : ContinuousOn g (U \ ↑S0)) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε) volume γ.a γ.b := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  obtain ⟨Mγ', hMγ'⟩ := piecewiseC1Immersion_deriv_bounded γ
  have h_compact_image : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn hγ_cont
  have h_safe_closed : IsClosed ({z : ℂ | ∀ s ∈ S0, ε ≤ ‖z - s‖}) := by
    have : {z : ℂ | ∀ s ∈ S0, ε ≤ ‖z - s‖} =
        ⋂ s ∈ (↑S0 : Set ℂ), {z | ε ≤ ‖z - s‖} := by
      ext z; simp [Set.mem_iInter]
    rw [this]; exact isClosed_biInter fun s _ =>
      isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))
  have h_safe_compact : IsCompact
      ((γ.toFun '' Icc γ.a γ.b) ∩ {z | ∀ s ∈ S0, ε ≤ ‖z - s‖}) :=
    h_compact_image.inter_right h_safe_closed
  have h_safe_sub :
      (γ.toFun '' Icc γ.a γ.b) ∩
        {z | ∀ s ∈ S0, ε ≤ ‖z - s‖} ⊆ U \ ↑S0 := by
    intro z hz
    obtain ⟨⟨t, ht, rfl⟩, hz_safe⟩ := hz
    exact ⟨hγ_in_U t ht, fun hzS0 => by
      have h1 := hz_safe (γ.toFun t) (Finset.mem_coe.mp hzS0)
      simp only [sub_self, norm_zero] at h1; linarith⟩
  obtain ⟨Mg, hMg⟩ := h_safe_compact.exists_bound_of_continuousOn (hg_cont.mono h_safe_sub)
  have h_bound : ∀ t ∈ Icc γ.a γ.b,
      ‖cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t‖ ≤ |Mg| * |Mγ'| + 1 := by
    intro t ht
    simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h
    · simp only [norm_zero]; positivity
    · push_neg at h
      calc ‖g (γ.toFun t) * deriv γ.toFun t‖
          = ‖g (γ.toFun t)‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
        _ ≤ |Mg| * |Mγ'| := by
            apply mul_le_mul
            · exact (hMg _
                ⟨⟨t, ht, rfl⟩,
                  fun s hs => le_of_lt (h s hs)⟩).trans
                (le_abs_self _)
            · exact (hMγ' t ht).trans (le_abs_self _)
            · exact norm_nonneg _
            · positivity
        _ ≤ |Mg| * |Mγ'| + 1 := le_add_of_nonneg_right one_pos.le
  set cpv_fn := cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε
  have h_cpv_aesm : AEStronglyMeasurable cpv_fn (volume.restrict (Icc γ.a γ.b)) := by
    let GoodSet := {t : ℝ | ∀ s' ∈ S0, ε < ‖γ.toFun t - s'‖}
    have hGoodSet_meas : MeasurableSet (GoodSet ∩ Icc γ.a γ.b) :=
      measurableSet_goodSet_Icc S0 γ ε
    have hgγ_cont_good : ContinuousOn (fun t => g (γ.toFun t))
        (GoodSet ∩ Icc γ.a γ.b) := by
      apply ContinuousOn.comp (hg_cont.mono h_safe_sub) (hγ_cont.mono inter_subset_right)
      intro t ⟨ht_good, ht_Icc⟩
      exact ⟨mem_image_of_mem _ ht_Icc, fun s' hs' => le_of_lt (ht_good s' hs')⟩
    have hγ'_meas := aesm_deriv_on_Icc γ
    have h_prod_meas : AEStronglyMeasurable (fun t => g (γ.toFun t) * deriv γ.toFun t)
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)) :=
      (hgγ_cont_good.aestronglyMeasurable hGoodSet_meas).mul
        (hγ'_meas.mono_measure (Measure.restrict_mono Set.inter_subset_right le_rfl))
    have h_zero_meas : AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
        (volume.restrict (GoodSet ∩ Icc γ.a γ.b)ᶜ) := aestronglyMeasurable_const
    have h_pw := AEStronglyMeasurable.piecewise hGoodSet_meas h_prod_meas h_zero_meas
    have h_ae_eq : cpv_fn =ᵐ[volume.restrict (Icc γ.a γ.b)]
        (GoodSet ∩ Icc γ.a γ.b).piecewise
          (fun t => g (γ.toFun t) * deriv γ.toFun t) (fun _ => (0 : ℂ)) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      change cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t = _
      simp only [cauchyPrincipalValueIntegrandOn]
      by_cases ht_good : t ∈ GoodSet ∩ Icc γ.a γ.b
      · rw [Set.piecewise_eq_of_mem _ _ _ ht_good, if_neg]
        push_neg; exact ht_good.1
      · rw [Set.piecewise_eq_of_notMem _ _ _ ht_good, if_pos]
        exact by_contra (fun h => by push_neg at h; exact ht_good ⟨h, ht⟩)
    exact (h_pw.mono_measure Measure.restrict_le_self).congr h_ae_eq.symm
  have h_int : IntegrableOn cpv_fn (Icc γ.a γ.b) volume :=
    IntegrableOn.of_bound
      (show volume (Icc γ.a γ.b) < ⊤ by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
      h_cpv_aesm (|Mg| * |Mγ'| + 1)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; exact h_bound t ht)
  exact (Set.uIcc_of_le (le_of_lt γ.hab) ▸ h_int).intervalIntegrable

/-! ### Assembly helper: CPV of h = f - f_res tends to 0

This helper packages the assembly of Sublemmas 1-3 into the main bridge lemma.
It shows that `∫ cpv(S0, h, ε) → 0` where `h z = f z - Σ res(f,s)/(z-s)`.

The proof decomposes h into:
- **Polar terms** at each crossed point: `a_k/(z-s)^{k+1}` for `k ≥ 1`,
  each tending to 0 by `multipoint_pv_zpow_tendsto_zero` (Sublemma 2).
- **Holomorphic remainder**: continuous along γ with zero contour integral,
  tending to 0 by `tendsto_cpv_of_continuousOn_zero_integral`.

The identification `a_0 = residueAt f s` uses `residueAt_eq_laurent_head_coeff`
(Sublemma 1). -/

/-- If two functions agree eventually on `𝓝[≠] s`, they have the same `residueAt`.
This is because `residueAt` is defined via circle integrals, and two functions that
agree on a punctured neighborhood have the same circle integrals for small radii. -/
private lemma residueAt_congr {f g : ℂ → ℂ} {s : ℂ}
    (h : f =ᶠ[𝓝[≠] s] g) : residueAt f s = residueAt g s := by
  have h_mem : {z | f z = g z} ∈ 𝓝[≠] s := h
  rw [Metric.mem_nhdsWithin_iff] at h_mem
  obtain ⟨δ, hδ_pos, hδ_eq⟩ := h_mem
  have h_ci_eq : ∀ r, 0 < r → r < δ →
      (∮ z in C(s, r), f z) = (∮ z in C(s, r), g z) := by
    intro r hr_pos hr_lt
    apply circleIntegral.integral_congr hr_pos.le
    intro z hz
    have hne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    exact hδ_eq ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; exact hr_lt),
      Set.mem_compl_singleton_iff.mpr hne⟩
  exact limUnder_eventually_eq (by
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with r ⟨hr_pos, hr_lt⟩
    simp only; congr 1; exact h_ci_eq r hr_pos hr_lt)

/-- Circle integrals of a meromorphic `f` are constant for small radii: if `f` is
analytic on `ball s rf \ {s}`, then `∮_{C(s,r)} f = ∮_{C(s,R₀)} f` for `r ≤ R₀ < rf`.
The proof multiplies by `(z-s)` to get a holomorphic `F` on the annulus, applies
the annulus integral identity, then divides back by `(z-s)⁻¹`. -/
private lemma circleIntegral_const_of_meromorphicAt_aux (f : ℂ → ℂ) (s : ℂ) (rf R₀ : ℝ)
    (hR₀_pos : 0 < R₀) (hR₀_lt_rf : R₀ < rf)
    (hf_analytic_at : ∀ z, z ∈ Metric.ball s rf → z ≠ s → AnalyticAt ℂ f z)
    (r : ℝ) (hr_pos : 0 < r) (hr_le : r ≤ R₀) :
    (∮ z in C(s, r), f z) = (∮ z in C(s, R₀), f z) := by
  have hR₀_ne : R₀ ≠ 0 := ne_of_gt hR₀_pos
  have h_inv_smul : ∀ ρ (hρ_ne : ρ ≠ 0),
      Set.EqOn (fun z => (z - s)⁻¹ • ((z - s) * f z)) f (Metric.sphere s ρ) := by
    intro ρ hρ_ne z hz
    have h_ne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz
      exact hρ_ne hz.symm
    simp only [smul_eq_mul, inv_mul_cancel_left₀ (sub_ne_zero.mpr h_ne)]
  set F : ℂ → ℂ := fun z => (z - s) * f z with hF_def
  have hF_analytic : ∀ z, z ∈ Metric.ball s rf → z ≠ s → AnalyticAt ℂ F z := by
    intro z hz hne
    exact (analyticAt_id.sub analyticAt_const).mul (hf_analytic_at z hz hne)
  have hF_cont : ContinuousOn F (Metric.closedBall s R₀ \ Metric.ball s r) := by
    intro z ⟨hz_cb, hz_not_ball⟩
    have h_ne : z ≠ s := by
      intro heq; rw [heq, Metric.mem_ball, dist_self, not_lt] at hz_not_ball; linarith
    exact (hF_analytic z (Metric.mem_ball.mpr (lt_of_le_of_lt
      (Metric.mem_closedBall.mp hz_cb) hR₀_lt_rf)) h_ne).continuousAt.continuousWithinAt
  have hF_diff : ∀ z ∈ (Metric.ball s R₀ \ Metric.closedBall s r) \ (∅ : Set ℂ),
      DifferentiableAt ℂ F z := by
    intro z ⟨⟨hz_ball, hz_not_cb⟩, _⟩
    have h_ne : z ≠ s := by
      intro heq; subst heq
      exact hz_not_cb (Metric.mem_closedBall_self hr_pos.le)
    have hz_rf : z ∈ Metric.ball s rf :=
      Metric.mem_ball.mpr (lt_trans (Metric.mem_ball.mp hz_ball) hR₀_lt_rf)
    exact (hF_analytic z hz_rf h_ne).differentiableAt
  have h_annulus :=
    Complex.circleIntegral_sub_center_inv_smul_eq_of_differentiable_on_annulus_off_countable
      hr_pos hr_le Set.countable_empty hF_cont hF_diff
  rw [circleIntegral.integral_congr hr_pos.le (h_inv_smul r (ne_of_gt hr_pos)),
    circleIntegral.integral_congr hR₀_pos.le (h_inv_smul R₀ hR₀_ne)] at h_annulus
  exact h_annulus.symm

/-- Circle integral of `∑ s' ∈ S0, c(s') / (z - s')` around `s ∈ S0` at radius
`r < dist(s, S0 \ {s})` equals `c(s) * 2πi`. The poles `s' ≠ s` are outside
the circle (by the separation hypothesis), so their contributions vanish. -/
private lemma circleIntegral_simple_pole_sum
    (S0 : Finset ℂ) (c : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0) (r : ℝ) (hr_pos : 0 < r)
    (h_no_pole : ∀ p ∈ S0, ∀ z ∈ Metric.sphere s r, z - p ≠ 0)
    (h_no_pole_cb : ∀ p ∈ S0.erase s, ∀ z ∈ Metric.closedBall s r, z - p ≠ 0) :
    (∮ z in C(s, r), ∑ s' ∈ S0, c s' / (z - s')) =
      c s * (2 * ↑Real.pi * I) := by
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_not : s ∉ Metric.sphere s r := by simp [hr_ne.symm]
  rw [show (fun z => ∑ s' ∈ S0, c s' / (z - s')) =
      (fun z => c s / (z - s) +
        ∑ s' ∈ S0.erase s, c s' / (z - s'))
    from funext (fun z => (Finset.add_sum_erase S0
      (fun s' => c s' / (z - s')) hs).symm)]
  have hci_s : CircleIntegrable (fun z => c s / (z - s)) s r :=
    (ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))).circleIntegrable hr_pos.le
  have hci_rest : CircleIntegrable
      (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s')) s r := by
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply continuousOn_finset_sum; intro p hp
    exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => h_no_pole p (Finset.mem_of_mem_erase hp) z hz)
  rw [circleIntegral.integral_add hci_s hci_rest,
    show (fun z => c s / (z - s)) = (fun z => c s * (z - s)⁻¹)
      from funext (fun z => div_eq_mul_inv _ _),
    circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv s hr_ne]
  suffices h_rest : (∮ z in C(s, r), ∑ s' ∈ S0.erase s, c s' / (z - s')) = 0 by
    rw [h_rest, add_zero]
  have h_rest_cont : ContinuousOn
      (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s')) (Metric.closedBall s r) := by
    apply continuousOn_finset_sum; intro p hp
    exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => h_no_pole_cb p hp z hz)
  have h_rest_diff : ∀ z ∈ (Metric.ball s r) \ (∅ : Set ℂ), DifferentiableAt ℂ
      (fun z => ∑ s' ∈ S0.erase s, c s' / (z - s')) z := by
    intro z ⟨hz, _⟩
    apply DifferentiableAt.fun_sum; intro p hp
    exact (differentiableAt_const (c p)).div
      (differentiableAt_id.sub (differentiableAt_const p))
      (h_no_pole_cb p hp z (Metric.ball_subset_closedBall hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
    Set.countable_empty h_rest_cont h_rest_diff

/-- Helper: `residueAt (f - Σ res(f,s')/(z-s')) s = 0` for `s ∈ S0`.
The function `h z = f z - Σ_{s' ∈ S0} residueAt f s' / (z - s')` has the same
higher-order poles as `f` at `s` but no simple pole (the `s' = s` term in the
sum cancels the residue). Hence `residueAt h s = 0`.

The proof uses circle integral decomposition: for small `r`,
`∮_{C(s,r)} h = ∮ f - Σ residueAt f s' * ∮ 1/(z-s')`. For `s' ≠ s` with
`|s'-s| > r`, `∮ 1/(z-s') = 0` (Cauchy); for `s' = s`, `∮ 1/(z-s) = 2πi`.
So `(2πi)⁻¹ ∮ h = (2πi)⁻¹ ∮ f - residueAt f s`. Taking `r → 0`:
`residueAt h s = residueAt f s - residueAt f s = 0`. -/
lemma residueAt_sub_residueSum_eq_zero
    (S0 : Finset ℂ) (f : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0)
    (hMero : MeromorphicAt f s) :
    residueAt (fun z => f z - ∑ s' ∈ S0, residueAt f s' / (z - s')) s = 0 := by
  unfold residueAt
  apply Filter.Tendsto.limUnder_eq
  have h_min_dist : ∃ δ > 0, ∀ s' ∈ S0, s' ≠ s → δ ≤ dist s' s := by
    by_cases h_other : ∃ s' ∈ S0, s' ≠ s
    · obtain ⟨s', hs', hne⟩ := h_other
      have h_nonempty : (S0.filter (· ≠ s)).Nonempty :=
        ⟨s', Finset.mem_filter.mpr ⟨hs', hne⟩⟩
      exact ⟨(S0.filter (· ≠ s)).inf' h_nonempty (fun s' => dist s' s),
        (Finset.lt_inf'_iff h_nonempty).mpr (fun b hb => dist_pos.mpr (Finset.mem_filter.mp hb).2),
        fun s' hs' hne' => Finset.inf'_le _ (Finset.mem_filter.mpr ⟨hs', hne'⟩)⟩
    · push_neg at h_other
      exact ⟨1, one_pos, fun s' hs' hne' => absurd (h_other s' hs') hne'⟩
  obtain ⟨δ, hδ_pos, hδ_sep⟩ := h_min_dist
  have hf_ev_analytic := hMero.eventually_analyticAt
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_ev_analytic
  obtain ⟨rf, hrf_pos, hrf_analytic⟩ := hf_ev_analytic
  set ρ := min δ rf with hρ_def
  have hρ_pos : 0 < ρ := lt_min hδ_pos hrf_pos
  have h2piI_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  set R₀ := ρ / 2 with hR₀_def
  have hR₀_pos : 0 < R₀ := by positivity
  have hR₀_lt_ρ : R₀ < ρ := by linarith
  have hR₀_lt_δ : R₀ < δ := lt_of_lt_of_le hR₀_lt_ρ (min_le_left _ _)
  have hR₀_lt_rf : R₀ < rf := lt_of_lt_of_le hR₀_lt_ρ (min_le_right _ _)
  have hR₀_ne : R₀ ≠ 0 := ne_of_gt hR₀_pos
  have hf_analytic_at : ∀ z, z ∈ Metric.ball s rf → z ≠ s → AnalyticAt ℂ f z := by
    intro z hz hne
    exact hrf_analytic ⟨hz, Set.mem_compl_singleton_iff.mpr hne⟩
  have hf_cont_sphere : ∀ r, 0 < r → r < rf → ContinuousOn f (Metric.sphere s r) := by
    intro r hr_pos hr_lt z hz
    exact (hf_analytic_at z
      (by rwa [Metric.mem_ball, Metric.mem_sphere.mp hz])
      (by intro heq
          rw [heq, Metric.mem_sphere, dist_self] at hz
          linarith)).continuousAt.continuousWithinAt
  have h_const_integral : ∀ r, 0 < r → r ≤ R₀ →
      (∮ z in C(s, r), f z) = (∮ z in C(s, R₀), f z) := fun r hr hr_le =>
    circleIntegral_const_of_meromorphicAt_aux f s rf R₀ hR₀_pos hR₀_lt_rf
      hf_analytic_at r hr hr_le
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds hR₀_pos] with r hr_lt hr_pos
  simp only [Set.mem_Ioi] at hr_pos; simp only [Set.mem_Iio] at hr_lt
  have hr_lt_δ : r < δ := lt_trans hr_lt hR₀_lt_δ
  have hr_lt_rf : r < rf := lt_trans hr_lt hR₀_lt_rf
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hs_not : s ∉ Metric.sphere s r := by simp [hr_ne.symm]
  have hf_ci : CircleIntegrable f s r :=
    (hf_cont_sphere r hr_pos hr_lt_rf).circleIntegrable hr_pos.le
  have h_no_pole_on_sphere : ∀ p ∈ S0, ∀ z ∈ Metric.sphere s r, z - ↑p ≠ 0 := by
    intro p hp z hz
    apply sub_ne_zero.mpr; intro heq
    rw [heq] at hz
    by_cases h_eq : p = s
    · exact hs_not (h_eq ▸ hz)
    · have h_dist := hδ_sep p hp h_eq
      rw [Metric.mem_sphere] at hz; linarith
  have hsum_ci : CircleIntegrable (fun z => ∑ s' ∈ S0, residueAt f s' / (z - s')) s r := by
    apply ContinuousOn.circleIntegrable hr_pos.le
    apply continuousOn_finset_sum; intro p hp
    exact ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      (fun z hz => h_no_pole_on_sphere p hp z hz)
  have h_int_sub := circleIntegral.integral_sub hf_ci hsum_ci
  have h_no_pole_in_cb : ∀ p ∈ S0.erase s,
      ∀ z ∈ Metric.closedBall s r, z - ↑p ≠ 0 := by
    intro p hp z hz
    apply sub_ne_zero.mpr; intro heq
    rw [heq] at hz
    have h_dist := hδ_sep p (Finset.mem_of_mem_erase hp) (Finset.ne_of_mem_erase hp)
    rw [Metric.mem_closedBall] at hz; linarith
  have h_int_sum : (∮ z in C(s, r), ∑ s' ∈ S0, residueAt f s' / (z - s')) =
      residueAt f s * (2 * ↑Real.pi * I) :=
    circleIntegral_simple_pole_sum S0 (residueAt f) s hs r hr_pos
      h_no_pole_on_sphere h_no_pole_in_cb
  rw [h_int_sub, h_int_sum, mul_sub, mul_comm (residueAt f s) _, ← mul_assoc,
    inv_mul_cancel₀ h2piI_ne, one_mul]
  rw [h_const_integral r hr_pos hr_lt.le]
  have h_res_eq : residueAt f s = (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(s, R₀), f z := by
    unfold residueAt
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_nhds_of_eventually_eq
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hR₀_pos] with r' hr'_lt hr'_pos
    simp only [Set.mem_Ioi] at hr'_pos; simp only [Set.mem_Iio] at hr'_lt
    rw [h_const_integral r' hr'_pos hr'_lt.le]
  rw [h_res_eq, sub_self]

/-- Helper: If `g` decomposes as `g = g_reg + g_pol` where:
- `g_reg` is continuous on `γ`'s image with `∮ g_reg = 0`, and
- `g_pol` is ContinuousOn `U \ S0` with `CPV(S0, g_pol, ε) → 0`,
then `CPV(S0, g, ε) → 0`.

The proof splits `CPV(g) = CPV(g_reg) + CPV(g_pol)` using CPV linearity
(both are interval integrable for fixed ε > 0), then combines the limits. -/
private theorem cpv_tendsto_zero_of_add_decomposition
    (U : Set ℂ) (S0 : Finset ℂ) (g g_reg g_pol : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hg_eq : ∀ z, g z = g_reg z + g_pol z)
    (hg_reg_cont : ContinuousOn g_reg (γ.toFun '' Icc γ.a γ.b))
    (hg_reg_int_zero : ∫ t in γ.a..γ.b, g_reg (γ.toFun t) * deriv γ.toFun t = 0)
    (hg_pol_cont : ContinuousOn g_pol (U \ ↑S0))
    (hg_pol_tendsto : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g_pol γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  have hg_eq_fun : g = fun z => g_reg z + g_pol z := funext hg_eq
  have h_integrand_eq : ∀ ε t,
      cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t =
      cauchyPrincipalValueIntegrandOn S0 g_reg γ.toFun ε t +
      cauchyPrincipalValueIntegrandOn S0 g_pol γ.toFun ε t := by
    intro ε t; rw [hg_eq_fun]; exact cpvIntegrandOn_add S0 g_reg g_pol γ.toFun ε t
  have h_reg_tendsto := tendsto_cpv_of_continuousOn_zero_integral S0 g_reg γ
    hg_reg_cont hg_reg_int_zero
  have h_zero_eq : (0 : ℂ) = 0 + 0 := (add_zero 0).symm
  rw [h_zero_eq]
  apply Filter.Tendsto.congr' _ (h_reg_tendsto.add hg_pol_tendsto)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  rw [show (fun t => cauchyPrincipalValueIntegrandOn S0 g γ.toFun ε t) =
      (fun t => cauchyPrincipalValueIntegrandOn S0 g_reg γ.toFun ε t +
       cauchyPrincipalValueIntegrandOn S0 g_pol γ.toFun ε t) from
    funext (fun t => h_integrand_eq ε t)]
  exact (intervalIntegral.integral_add
    (intervalIntegrable_cauchyPrincipalValueIntegrandOn (S0 := S0) hε hg_reg_cont)
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 g_pol
      hg_pol_cont γ hγ_in_U ε hε)).symm

end GeneralizedResidueTheory
