/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.SectorCancellation
import LeanModularForms.ForMathlib.HungerbuhlerWasem.CrossingDataBuilder
import LeanModularForms.ForMathlib.ExitTime
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Higher-order CPV discharger from immersion data (T-BR-03)

This file wraps `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
(in `SectorCancellation.lean`) into a paper-faithful form. The original
theorem takes ~30 hypotheses describing the analytic and geometric data
of the crossing; this wrapper derives all of them from a much smaller set
of inputs:

* `γ : ClosedPwC1Immersion x` — the closed piecewise-`C¹` immersion;
* `t₀ ∈ Ioo 0 1` — interior crossing time;
* `h_at`, `h_unique` — the curve crosses `s` only at `t₀`;
* `h_flat : IsFlatOfOrder γ.extend t₀ n` for `2 ≤ k ≤ n`;
* `h_B` (corner form) or `h_angle` (smooth form) — the angle compatibility
  expressing Condition (B) for the integrand `c/(z-s)^k`.

## Main results

* `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner` —
  general (corner-friendly) form, takes explicit left/right derivative
  limits and the unit-circle equation `h_B`.
* `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB` —
  smooth specialisation at off-partition points, deriving `L_- = L_+` and
  the even-power `h_B` from the simpler `(k-1)·π ∈ 2π·ℤ` form of (B).
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- Build `h_close` from a closed piecewise-`C¹` curve: the extended path takes
the same value at `0` and `1` (both equal the basepoint `x`). -/
theorem closed_immersion_extend_zero_eq_one (γ : ClosedPwC1Immersion x) :
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 =
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1 := by
  simp

private theorem neg_pow_eq_self_of_even_sub_one
    {k : ℕ} (z : ℂ) (m : ℤ) (hm : ((k - 1 : ℕ) : ℝ) = 2 * (m : ℝ)) :
    (-z) ^ (k - 1) = z ^ (k - 1) := by
  refine Even.neg_pow ?_ z
  have h_eq : ((k - 1 : ℕ) : ℤ) = 2 * m := by exact_mod_cast hm
  exact ⟨m.toNat, by omega⟩

/-- At an off-partition interior point, the right and left derivative limits both
equal `deriv γ t₀` and are nonzero. -/
theorem deriv_limit_eq_at_off_partition
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    let f := γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend
    deriv f t₀ ≠ 0 ∧
    Tendsto (deriv f) (𝓝[>] t₀) (𝓝 (deriv f t₀)) ∧
    Tendsto (deriv f) (𝓝[<] t₀) (𝓝 (deriv f t₀)) := by
  have h_cont :=
    γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off_extend t₀ ht₀ h_off
  exact ⟨γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_off,
    h_cont.tendsto.mono_left nhdsWithin_le_nhds,
    h_cont.tendsto.mono_left nhdsWithin_le_nhds⟩

/-- The angle equation `h_B` from condition-(B) angle compatibility, in the
off-partition (smooth) case where `L_- = L_+ = L`.

If `(k-1) · π = m · 2π` for some integer `m`, then
`(L/‖L‖)^(k-1) = ((-L)/‖L‖)^(k-1)`. -/
theorem h_B_of_angle_compat_smooth
    (L : ℂ) (_hL : L ≠ 0) (k : ℕ) (_hk : 2 ≤ k)
    (h_angle : ∃ m : ℤ, ((k - 1 : ℕ) : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi)) :
    (L / (↑‖L‖ : ℂ)) ^ (k - 1) =
    ((-L) / (↑‖L‖ : ℂ)) ^ (k - 1) := by
  obtain ⟨m, hm⟩ := h_angle
  have hkm : ((k - 1 : ℕ) : ℝ) = 2 * (m : ℝ) :=
    mul_right_cancel₀ Real.pi_ne_zero (by linarith [hm] :
      ((k - 1 : ℕ) : ℝ) * Real.pi = (2 * m) * Real.pi)
  rw [neg_div, neg_pow_eq_self_of_even_sub_one (L / ↑‖L‖) m hkm]

/-- For a function `γ` with `Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)` and eventual
differentiability on `(t₀, ∞)`, plus continuity at `t₀`, we have
`HasDerivWithinAt γ L (Ioi t₀) t₀`. -/
theorem hasDerivWithinAt_Ioi_of_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Ioi t₀) t₀ := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact hasDerivWithinAt_Ioi_iff_Ici.mpr
    (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hL_right)

/-- For a function `γ` with `Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)` and eventual
differentiability on `(-∞, t₀)`, plus continuity at `t₀`, we have
`HasDerivWithinAt γ L (Iio t₀) t₀`. -/
theorem hasDerivWithinAt_Iio_of_tendsto
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) :
    HasDerivWithinAt γ L (Iio t₀) t₀ := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact hasDerivWithinAt_Iio_iff_Iic.mpr
    (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hL_left)

/-- A cutoff-integrability lemma for `c / (z - s)^k`, mirroring
`cpvIntegrandOn_polarPart_intervalIntegrable` but specialised to a single
Laurent monomial. -/
theorem cpvIntegrandOn_singleMonomial_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {S : Finset ℂ} (hs : s ∈ S)
    (c : ℂ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => c / (z - s) ^ k)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      MeasureTheory.volume 0 1 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set badSet : Set ℝ := {t | ∃ s' ∈ S, ‖γP.toPath.extend t - s'‖ ≤ ε} with badSet_def
  set monomial : ℂ → ℂ := fun z => c / (z - s) ^ k
  set h_curve : ℝ → ℂ := fun t =>
    monomial (γP.toPath.extend t) * deriv γP.toPath.extend t
  have h_indicator_eq :
      (fun t => cpvIntegrandOn S monomial γP.toPath.extend ε t) =
      badSetᶜ.indicator h_curve := by
    funext t
    by_cases ht_in : t ∈ badSet
    · rw [cpvIntegrandOn_of_exists_le ht_in,
        Set.indicator_of_notMem (Set.notMem_compl_iff.mpr ht_in)]
    · have h_forall : ∀ s' ∈ S, ε < ‖γP.toPath.extend t - s'‖ := by
        simp only [Set.mem_setOf_eq, not_exists, not_and, not_le, badSet_def] at ht_in
        exact ht_in
      rw [cpvIntegrandOn_of_forall_gt h_forall, Set.indicator_of_mem ht_in]
  set M_polar : ℝ := ‖c‖ / ε ^ k
  set M : ℝ := M_polar * K
  have h_M_polar_nonneg : 0 ≤ M_polar :=
    div_nonneg (norm_nonneg _) (pow_nonneg hε.le _)
  have h_M_nonneg : 0 ≤ M := mul_nonneg h_M_polar_nonneg (NNReal.coe_nonneg K)
  have h_bound_on_compl : ∀ t ∈ badSetᶜ, ‖h_curve t‖ ≤ M := by
    intro t ht_in
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and,
      not_le, badSet_def] at ht_in
    have h_far_s : ε < ‖γP.toPath.extend t - s‖ := ht_in s hs
    have h_mono_bound : ‖monomial (γP.toPath.extend t)‖ ≤ M_polar := by
      change ‖c / (γP.toPath.extend t - s) ^ k‖ ≤ M_polar
      rw [norm_div, norm_pow]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hε _)
        (pow_le_pow_left₀ hε.le h_far_s.le _)
    calc ‖h_curve t‖ = ‖monomial (γP.toPath.extend t)‖ *
          ‖deriv γP.toPath.extend t‖ := norm_mul _ _
      _ ≤ M_polar * K :=
          mul_le_mul h_mono_bound (norm_deriv_le_of_lipschitz hLip)
            (norm_nonneg _) h_M_polar_nonneg
  have h_bound_indicator : ∀ t, ‖badSetᶜ.indicator h_curve t‖ ≤ M := by
    intro t
    by_cases ht_in : t ∈ badSetᶜ
    · rw [Set.indicator_of_mem ht_in]
      exact h_bound_on_compl t ht_in
    · rw [Set.indicator_of_notMem ht_in, norm_zero]
      exact h_M_nonneg
  have h_γ_meas : Measurable γP.toPath.extend :=
    γP.toPath.continuous_extend.measurable
  have h_curve_meas : Measurable h_curve :=
    (((h_γ_meas.sub_const s).pow_const _).const_div _).mul (measurable_deriv _)
  have h_badSet_meas : MeasurableSet badSet := by
    have h_eq : badSet = ⋃ s' ∈ (S : Set ℂ),
        {t : ℝ | ‖γP.toPath.extend t - s'‖ ≤ ε} := by
      ext t
      simp only [badSet_def, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_coe,
        exists_prop]
    rw [h_eq]
    refine MeasurableSet.biUnion S.countable_toSet fun s' _ =>
      measurableSet_le ?_ measurable_const
    exact (h_γ_meas.sub_const s').norm
  rw [intervalIntegrable_iff, h_indicator_eq]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
    (h_curve_meas.aestronglyMeasurable.indicator h_badSet_meas.compl) M ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
  exact h_bound_indicator t

private theorem integral_pow_inv_eq_FTC_of_le
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {s : ℂ} {k : ℕ} {a b : ℝ}
    {exc : Set ℝ} (hexc : exc.Countable)
    (hk : 2 ≤ k) (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b \ exc, HasDerivAt γ (γ' t) t)
    (h_avoids : ∀ t ∈ Icc a b, γ t ≠ s)
    (h_int : IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume a b) :
    ∫ t in a..b, γ' t / (γ t - s) ^ k =
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ b - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ a - s) ^ (k - 1))⁻¹) := by
  set F : ℂ → ℂ := fun z => -(↑(k - 1) : ℂ)⁻¹ * ((z - s) ^ (k - 1))⁻¹
  have h_F_diff_at : ∀ t ∈ Ioo a b \ exc,
      HasDerivAt (fun u => F (γ u)) (γ' t / (γ t - s) ^ k) t := by
    intro t ht
    have h_chain := (hasDerivAt_antiderivative_pow_inv_complex hk
      (h_avoids t (Ioo_subset_Icc_self ht.1))).comp t (hγ_diff t ht)
    convert h_chain using 1
    simp [div_eq_mul_inv]; ring
  have h_Fγ_cont : ContinuousOn (fun u => F (γ u)) (Icc a b) := fun t ht =>
    (hasDerivAt_antiderivative_pow_inv_complex hk (h_avoids t ht)).continuousAt
      |>.comp_continuousWithinAt (hγ_cont t ht)
  exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (fun u => F (γ u)) (fun t => γ' t / (γ t - s) ^ k) hab hexc h_Fγ_cont
    h_F_diff_at h_int

private theorem closed_excised_integral_eq_antideriv_diff_of_continuous
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {s : ℂ} {k : ℕ} {a t_minus t_plus b : ℝ}
    {exc : Set ℝ} (hexc : exc.Countable)
    (hk : 2 ≤ k) (hat_minus : a ≤ t_minus) (htplus_b : t_plus ≤ b)
    (h_close : γ a = γ b)
    (hγ_cont_left : ContinuousOn γ (Icc a t_minus))
    (hγ_cont_right : ContinuousOn γ (Icc t_plus b))
    (hγ_diff_left : ∀ t ∈ Ioo a t_minus \ exc, HasDerivAt γ (γ' t) t)
    (hγ_diff_right : ∀ t ∈ Ioo t_plus b \ exc, HasDerivAt γ (γ' t) t)
    (h_avoids_left : ∀ t ∈ Icc a t_minus, γ t ≠ s)
    (h_avoids_right : ∀ t ∈ Icc t_plus b, γ t ≠ s)
    (h_int_left : IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume a t_minus)
    (h_int_right : IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume t_plus b) :
    (∫ t in a..t_minus, γ' t / (γ t - s) ^ k) +
      (∫ t in t_plus..b, γ' t / (γ t - s) ^ k) =
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ t_minus - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ t_plus - s) ^ (k - 1))⁻¹) := by
  rw [integral_pow_inv_eq_FTC_of_le hexc hk hat_minus hγ_cont_left hγ_diff_left
        h_avoids_left h_int_left,
    integral_pow_inv_eq_FTC_of_le hexc hk htplus_b hγ_cont_right hγ_diff_right
        h_avoids_right h_int_right, h_close]
  ring

private theorem hw_theorem_3_3_parametric_relaxed
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {a b t₀ : ℝ}
    (_hab_t : a ≤ t₀) (_htb : t₀ ≤ b)
    {s L_minus L_plus : ℂ} {n k : ℕ}
    {exc : Set ℝ} (hexc : exc.Countable)
    (h_close : γ a = γ b)
    (h_flat : IsFlatOfOrder γ t₀ n)
    (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L_plus (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L_minus (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_plus))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_minus))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    (t_eps_plus t_eps_minus : ℝ → ℝ)
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] (0 : ℝ)) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] (0 : ℝ)) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ (t_eps_minus ε) - s‖ = ε)
    (h_a_le_t_minus : ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ≤ t_eps_minus ε)
    (h_t_plus_le_b : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t_eps_plus ε ≤ b)
    (h_minus_cont : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn γ (Icc a (t_eps_minus ε)))
    (h_plus_cont : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn γ (Icc (t_eps_plus ε) b))
    (h_minus_diff : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Ioo a (t_eps_minus ε) \ exc, HasDerivAt γ (γ' t) t)
    (h_plus_diff : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Ioo (t_eps_plus ε) b \ exc, HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc a (t_eps_minus ε), γ t ≠ s)
    (h_plus_avoids : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (t_eps_plus ε) b, γ t ≠ s)
    (h_minus_int : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume a (t_eps_minus ε))
    (h_plus_int : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume
        (t_eps_plus ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(t_eps_minus ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (t_eps_plus ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h_F_diff_to_zero :=
    F_curve_diff_tendsto_zero_under_conditionB h_flat hL_minus hL_plus
      h_deriv_right h_deriv_left hL_right hL_left h_s hk hkn hn1 h_B
      t_eps_plus t_eps_minus h_plus_to h_plus_radius h_minus_to h_minus_radius
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine h_F_diff_to_zero.congr' ?_
  filter_upwards [h_a_le_t_minus, h_t_plus_le_b, h_minus_cont, h_plus_cont,
    h_minus_diff, h_plus_diff, h_minus_avoids, h_plus_avoids, h_minus_int,
    h_plus_int] with ε ha_le_tm htp_le_b hcl hcr hdl hdr hal har hil hir
  rw [closed_excised_integral_eq_antideriv_diff_of_continuous hexc hk ha_le_tm
    htp_le_b h_close hcl hcr hdl hdr hal har hil hir]

private theorem div_norm_eq_exp_arg {z : ℂ} (hz : z ≠ 0) :
    z / (↑‖z‖ : ℂ) = Complex.exp (↑(Complex.arg z) * Complex.I) := by
  rw [div_eq_iff (by exact_mod_cast (norm_pos_iff.mpr hz).ne'), mul_comm]
  exact (Complex.norm_mul_exp_arg_mul_I z).symm

/-- **From corner angle equation to `h_B`.** Given nonzero `L_-, L_+`, and the
integer angle equation `(k - 1 : ℕ) · (arg L_+ - arg (-L_-)) = m · 2π`, the
unit-circle powers `(L_+/‖L_+‖)^(k-1)` and `((-L_-)/‖L_-‖)^(k-1)` agree.

This is the general-angle analog of `h_B_of_angle_compat_smooth`: where the
smooth case forces `L_+ = -(-L_-)` (so the angle is `π` and the equation
reduces to even-power), the corner case uses the general angle
`α = arg(L_+) - arg(-L_-)`. -/
theorem h_B_of_angle_compat_corner
    {L_minus L_plus : ℂ} (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0)
    {k : ℕ} (_hk : 2 ≤ k)
    (h_angle : ∃ m : ℤ,
      ((k - 1 : ℕ) : ℝ) * (Complex.arg L_plus - Complex.arg (-L_minus)) =
        (m : ℝ) * (2 * Real.pi)) :
    (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
    ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1) := by
  obtain ⟨m, hm⟩ := h_angle
  rw [show (↑‖L_minus‖ : ℂ) = ↑‖-L_minus‖ by rw [norm_neg],
    div_norm_eq_exp_arg hL_plus, div_norm_eq_exp_arg (neg_ne_zero.mpr hL_minus),
    ← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨m, ?_⟩
  have hm_complex : ((k - 1 : ℕ) : ℂ) * (↑(Complex.arg L_plus) -
      ↑(Complex.arg (-L_minus))) = ((m : ℤ) : ℂ) * (2 * (↑Real.pi : ℂ)) := by
    have h := congrArg ((↑·) : ℝ → ℂ) hm
    push_cast at h ⊢
    linear_combination h
  linear_combination congr_arg (· * Complex.I) hm_complex

/-- **Higher-order CPV vanishing under condition (B) — corner-friendly form
(T-BR-Y10).**

For a closed piecewise-`C¹` immersion `γ` that crosses `s` only at parameter
`t₀ ∈ Ioo 0 1` (POSSIBLY a corner point), with `γ` flat of order `n ≥ k` at
`t₀`, separate one-sided derivative limits `L_-, L_+ ≠ 0`, and condition (B)
in the form `h_B : (L_+/‖L_+‖)^(k-1) = ((-L_-)/‖L_-‖)^(k-1)` (provided by
condition (B)'s Laurent compatibility), the CPV of `c / (z - s)^k` along
`γ.toPiecewiseC1Path` at the singleton `{s}` vanishes.

This is the general form. The smooth specialisation at off-partition points
is `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`. -/
theorem hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {L_minus L_plus : ℂ} (hL_minus_ne : L_minus ≠ 0) (hL_plus_ne : L_plus ≠ 0)
    (hL_right : Tendsto
      (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
      (𝓝[>] t₀) (𝓝 L_plus))
    (hL_left : Tendsto
      (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
      (𝓝[<] t₀) (𝓝 L_minus))
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ n)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    (c : ℂ) :
    HasCauchyPVOn {s} (fun z => c / (z - s) ^ k)
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  classical
  set f : ℝ → ℂ := fun t =>
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_continuous : Continuous f := γ.toPwC1Immersion.toPiecewiseC1Path.continuous
  have hγ_cont_t₀ : ContinuousAt f t₀ := hγ_continuous.continuousAt
  have hγ_diff_right : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ f t :=
    eventually_differentiable_right γ ht₀
  have hγ_diff_left : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ f t :=
    eventually_differentiable_left γ ht₀
  obtain ⟨r_R, hr_R_pos, hγ_mono_at_radius⟩ :=
    norm_sub_strictMonoOn_right h_at hL_plus_ne hL_right hγ_cont_t₀ hγ_diff_right
  obtain ⟨r_L, hr_L_pos, hγ_anti_at_radius⟩ :=
    norm_sub_strictAntiOn_left h_at hL_minus_ne hL_left hγ_cont_t₀ hγ_diff_left
  set δPlus : ℝ := min r_R (1 - t₀) / 2
  set δMinus : ℝ := min r_L t₀ / 2
  have hδPlus_pos : 0 < δPlus := half_pos (lt_min hr_R_pos (sub_pos.mpr ht₀.2))
  have hδMinus_pos : 0 < δMinus := half_pos (lt_min hr_L_pos ht₀.1)
  have hδPlus_le_1mt₀ : δPlus ≤ 1 - t₀ :=
    (half_le_self (lt_min hr_R_pos (sub_pos.mpr ht₀.2)).le).trans (min_le_right _ _)
  have hδMinus_le_t₀ : δMinus ≤ t₀ :=
    (half_le_self (lt_min hr_L_pos ht₀.1).le).trans (min_le_right _ _)
  have hδPlus_in_one : t₀ + δPlus ≤ 1 := by linarith
  have hδMinus_in_zero : 0 ≤ t₀ - δMinus := by linarith
  have hγ_mono : StrictMonoOn (fun t => ‖f t - s‖) (Icc t₀ (t₀ + δPlus)) :=
    hγ_mono_at_radius.mono (Icc_subset_Icc le_rfl (by
      have : δPlus ≤ r_R :=
        (half_le_self (lt_min hr_R_pos (sub_pos.mpr ht₀.2)).le).trans (min_le_left _ _)
      linarith))
  have hγ_anti : StrictAntiOn (fun t => ‖f t - s‖) (Icc (t₀ - δMinus) t₀) :=
    hγ_anti_at_radius.mono (Icc_subset_Icc (by
      have : δMinus ≤ r_L :=
        (half_le_self (lt_min hr_L_pos ht₀.1).le).trans (min_le_left _ _)
      linarith) le_rfl)
  have hγ_cont_right_delta : ContinuousOn f (Icc t₀ (t₀ + δPlus)) :=
    hγ_continuous.continuousOn
  have hγ_cont_left_delta : ContinuousOn f (Icc (t₀ - δMinus) t₀) :=
    hγ_continuous.continuousOn
  have h_leave_right : ∀ t ∈ Ioc t₀ (t₀ + δPlus), f t ≠ s := by
    intro t ht heq
    have h_strict := hγ_mono ⟨le_rfl, by linarith [hδPlus_pos]⟩
      ⟨ht.1.le, ht.2⟩ ht.1
    simp only [show f t₀ = s from h_at, heq] at h_strict
    exact lt_irrefl _ h_strict
  have h_leave_left : ∀ t ∈ Ico (t₀ - δMinus) t₀, f t ≠ s := by
    intro t ht heq
    have h_strict := hγ_anti ⟨ht.1, ht.2.le⟩
      ⟨by linarith [hδMinus_pos], le_rfl⟩ ht.2
    simp only [show f t₀ = s from h_at, heq] at h_strict
    exact lt_irrefl _ h_strict
  obtain ⟨δ_avoid, h_avoid_pos, h_avoid_left_raw, h_avoid_right_raw⟩ :=
    exists_far_bound_compact f hγ_continuous s t₀ h_unique
      (lt_min hδMinus_pos hδPlus_pos) ((min_le_left _ _).trans hδMinus_le_t₀)
      ((min_le_right _ _).trans hδPlus_le_1mt₀)
  have h_avoid_left : ∀ t ∈ Set.Icc (0 : ℝ) (t₀ - δMinus), δ_avoid ≤ ‖f t - s‖ :=
    fun t ht => h_avoid_left_raw t ⟨ht.1, by
      have := min_le_left δMinus δPlus; linarith [ht.2]⟩
  have h_avoid_right : ∀ t ∈ Set.Icc (t₀ + δPlus) (1 : ℝ), δ_avoid ≤ ‖f t - s‖ :=
    fun t ht => h_avoid_right_raw t ⟨by
      have := min_le_right δMinus δPlus; linarith [ht.1], ht.2⟩
  have h_deriv_right : HasDerivWithinAt f L_plus (Set.Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_of_tendsto hγ_cont_t₀ hγ_diff_right hL_right
  have h_deriv_left : HasDerivWithinAt f L_minus (Set.Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_of_tendsto hγ_cont_t₀ hγ_diff_left hL_left
  set t_eps_plus := LeanModularForms.firstExitTimeRight f t₀ δPlus s
  set t_eps_minus := LeanModularForms.firstExitTimeLeft f t₀ δMinus s
  have h_plus_to : Tendsto t_eps_plus (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) :=
    LeanModularForms.firstExitTimeRight_tendsto_t₀ hδPlus_pos
      hγ_cont_right_delta h_at h_leave_right
  have h_plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖f (t_eps_plus ε) - s‖ = ε :=
    LeanModularForms.firstExitTimeRight_radius_eventually hδPlus_pos
      hγ_cont_right_delta h_at h_leave_right
  have h_minus_to : Tendsto t_eps_minus (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) :=
    LeanModularForms.firstExitTimeLeft_tendsto_t₀ hδMinus_pos
      hγ_cont_left_delta h_at h_leave_left
  have h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖f (t_eps_minus ε) - s‖ = ε :=
    LeanModularForms.firstExitTimeLeft_radius_eventually hδMinus_pos
      hγ_cont_left_delta h_at h_leave_left
  have h_t_minus_in_Ioo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      t_eps_minus ε ∈ Ioo (t₀ - δMinus) t₀ :=
    h_minus_to (Ioo_mem_nhdsLT (by linarith [hδMinus_pos]))
  have h_t_plus_in_Ioo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      t_eps_plus ε ∈ Ioo t₀ (t₀ + δPlus) :=
    h_plus_to (Ioo_mem_nhdsGT (by linarith [hδPlus_pos]))
  have h_zero_le_t_minus : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (0 : ℝ) ≤ t_eps_minus ε :=
    h_t_minus_in_Ioo.mono fun _ hε => by linarith [hε.1, hδMinus_in_zero]
  have h_t_plus_le_one : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t_eps_plus ε ≤ (1 : ℝ) :=
    h_t_plus_in_Ioo.mono fun _ hε => by linarith [hε.2, hδPlus_in_one]
  have h_minus_cont : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn f (Icc (0 : ℝ) (t_eps_minus ε)) :=
    Filter.Eventually.of_forall fun _ => hγ_continuous.continuousOn
  have h_plus_cont : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ContinuousOn f (Icc (t_eps_plus ε) (1 : ℝ)) :=
    Filter.Eventually.of_forall fun _ => hγ_continuous.continuousOn
  set partSet : Set ℝ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ)
  have h_partSet_countable : partSet.Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have h_minus_diff : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Ioo (0 : ℝ) (t_eps_minus ε) \ partSet,
        HasDerivAt f (deriv f t) t := by
    filter_upwards [h_t_minus_in_Ioo] with ε htme t ⟨ht_in, ht_off⟩
    exact (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t
      ⟨ht_in.1, by linarith [ht_in.2, htme.2, ht₀.2]⟩ ht_off).hasDerivAt
  have h_plus_diff : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Ioo (t_eps_plus ε) (1 : ℝ) \ partSet,
        HasDerivAt f (deriv f t) t := by
    filter_upwards [h_t_plus_in_Ioo] with ε htpe t ⟨ht_in, ht_off⟩
    exact (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend t
      ⟨by linarith [htpe.1, ht_in.1, ht₀.1], ht_in.2⟩ ht_off).hasDerivAt
  have h_minus_avoids : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (0 : ℝ) (t_eps_minus ε), f t ≠ s := by
    filter_upwards [h_t_minus_in_Ioo] with ε htme t ht heq
    have h_t_lt_t₀ : t < t₀ := lt_of_le_of_lt ht.2 htme.2
    exact h_t_lt_t₀.ne (h_unique t ⟨ht.1, by linarith [ht.2, htme.2, ht₀.2]⟩ heq)
  have h_plus_avoids : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ t ∈ Icc (t_eps_plus ε) (1 : ℝ), f t ≠ s := by
    filter_upwards [h_t_plus_in_Ioo] with ε htpe t ht heq
    have h_t₀_lt_t : t₀ < t := lt_of_lt_of_le htpe.1 ht.1
    exact h_t₀_lt_t.ne' (h_unique t ⟨by linarith [ht.1, htpe.1, ht₀.1], ht.2⟩ heq)
  have h_deriv_int_full : IntervalIntegrable (deriv f) volume 0 1 :=
    γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable
  have h_eq_int : (fun t => deriv f t / (f t - s) ^ k) =
      fun t => deriv f t * ((1 : ℂ) / (f t - s) ^ k) := by
    funext t; rw [mul_one_div]
  -- Build `IntervalIntegrable (deriv f t / (f t - s)^k)` on a sub-interval of `[0,1]`
  -- on which `f` avoids `s` (witnessed by a `t ↦ f t ≠ s` hypothesis).
  have integrable_of_avoids : ∀ {a b : ℝ}, 0 ≤ a → b ≤ 1 → a ≤ b →
      (∀ t ∈ Icc a b, f t ≠ s) →
      IntervalIntegrable (fun t => deriv f t / (f t - s) ^ k) volume a b := by
    intro a b ha_nn hb_le hab h_avoid
    rw [h_eq_int]
    refine (h_deriv_int_full.mono (by
        rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]
        exact Icc_subset_Icc ha_nn hb_le) le_rfl).mul_continuousOn ?_
    rw [Set.uIcc_of_le hab]
    exact fun t ht => ContinuousAt.continuousWithinAt (ContinuousAt.div continuousAt_const
      ((hγ_continuous.continuousAt.sub continuousAt_const).pow k)
      (pow_ne_zero _ (sub_ne_zero.mpr (h_avoid t ht))))
  have h_minus_int : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (fun t => deriv f t / (f t - s) ^ k) volume 0
        (t_eps_minus ε) := by
    filter_upwards [h_t_minus_in_Ioo, h_minus_avoids] with ε htme havoid
    exact integrable_of_avoids le_rfl (htme.2.le.trans ht₀.2.le)
      (by linarith [htme.1, hδMinus_in_zero]) havoid
  have h_plus_int : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IntervalIntegrable (fun t => deriv f t / (f t - s) ^ k) volume
        (t_eps_plus ε) (1 : ℝ) := by
    filter_upwards [h_t_plus_in_Ioo, h_plus_avoids] with ε htpe havoid
    exact integrable_of_avoids (by linarith [htpe.1, ht₀.1])
      le_rfl (htpe.2.le.trans hδPlus_in_one) havoid
  have h_F_diff_tendsto :
      Tendsto (fun ε =>
        (∫ t in (0 : ℝ)..(t_eps_minus ε), deriv f t / (f t - s) ^ k) +
          (∫ t in (t_eps_plus ε)..(1 : ℝ), deriv f t / (f t - s) ^ k))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hw_theorem_3_3_parametric_relaxed (γ := f) (γ' := deriv f)
      (a := 0) (b := 1) (t₀ := t₀) (s := s) (L_minus := L_minus) (L_plus := L_plus)
      (n := n) (k := k) (exc := partSet) ht₀.1.le ht₀.2.le h_partSet_countable
      ?_ h_flat
      hL_minus_ne hL_plus_ne h_deriv_right h_deriv_left hL_right hL_left
      h_at hk hkn hn1 h_B
      t_eps_plus t_eps_minus h_plus_to h_plus_radius h_minus_to h_minus_radius
      h_zero_le_t_minus h_t_plus_le_one
      h_minus_cont h_plus_cont h_minus_diff h_plus_diff
      h_minus_avoids h_plus_avoids h_minus_int h_plus_int
    exact closed_immersion_extend_zero_eq_one γ
  have h_shape : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ t_eps_minus ε ∧
      t_eps_plus ε ≤ 1 ∧
      t_eps_minus ε ≤ t_eps_plus ε ∧
      (∀ t ∈ Ioo (0 : ℝ) (t_eps_minus ε), ε < ‖f t - s‖) ∧
      (∀ t ∈ Ioo (t_eps_plus ε) (1 : ℝ), ε < ‖f t - s‖) ∧
      (∀ t ∈ Ioo (t_eps_minus ε) (t_eps_plus ε), ‖f t - s‖ ≤ ε) :=
    shape_eventually_of_strict_mono hδMinus_in_zero hδPlus_in_one
      hδMinus_pos hδPlus_pos hγ_cont_left_delta hγ_cont_right_delta
      hγ_anti hγ_mono h_at h_avoid_pos h_avoid_pos h_avoid_left h_avoid_right
  have h_int_full_singleton : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn {s} (fun z => (1 : ℂ) / (z - s) ^ k)
        f ε t) volume 0 1 := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε_pos : 0 < ε)
    exact cpvIntegrandOn_singleMonomial_intervalIntegrable γ
      (Finset.mem_singleton.mpr rfl : s ∈ ({s} : Finset ℂ)) 1 k hε_pos
  have h_singleton :
      HasCauchyPVOn ({s} : Finset ℂ) (fun z => (1 : ℂ) / (z - s) ^ k)
        γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
    refine hasCauchyPVOn_singleton_of_exitTime_excision
      γ.toPwC1Immersion.toPiecewiseC1Path s
      (fun z => (1 : ℂ) / (z - s) ^ k) h_shape h_int_full_singleton ?_
    refine h_F_diff_tendsto.congr fun ε => ?_
    congr 1 <;>
    · refine intervalIntegral.integral_congr fun t _ => ?_
      change deriv f t / (f t - s) ^ k = (1 / (f t - s) ^ k) * deriv f t
      ring
  have h_smul := h_singleton.smul c
  rw [mul_zero] at h_smul
  convert h_smul using 1
  funext z; rw [mul_one_div]

/-- **Higher-order CPV vanishing under condition (B) — paper-faithful form.**

For a closed piecewise-`C¹` immersion `γ` that crosses `s` only at parameter
`t₀ ∈ Ioo 0 1` (off the legacy partition), with `γ` flat of order `n ≥ k` at
`t₀` and condition (B) expressed as `(k-1) · π ∈ 2π·ℤ` (`h_angle`), the CPV of
`c / (z - s)^k` along `γ.toPiecewiseC1Path` at the singleton `{s}` vanishes.

This is the smooth-crossing specialisation of
`hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`: at an
off-partition point, the left/right derivative limits agree, and condition (B)
reduces to the even-power form via `h_B_of_angle_compat_smooth`. -/
theorem hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB
    (γ : ClosedPwC1Immersion x) {s : ℂ}
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (h_t₀_off_partition : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ n)
    (h_angle : ∃ m : ℤ,
      ((k - 1 : ℕ) : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi))
    (c : ℂ) :
    HasCauchyPVOn {s} (fun z => c / (z - s) ^ k)
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  obtain ⟨h_L_ne, h_L_right, h_L_left⟩ :=
    deriv_limit_eq_at_off_partition γ ht₀ h_t₀_off_partition
  exact hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner
    γ ht₀ h_at h_unique h_L_ne h_L_ne h_L_right h_L_left hk hkn hn1 h_flat
    (h_B_of_angle_compat_smooth _ h_L_ne k hk h_angle) c

end HungerbuhlerWasem

end
