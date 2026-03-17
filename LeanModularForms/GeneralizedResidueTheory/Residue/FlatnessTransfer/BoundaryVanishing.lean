/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.Flatness

/-!
# Boundary Vanishing for Higher-Order Polar Terms

Chain rules for zpow compositions (L0), FTC for negative powers (L1),
exit-time direction convergence (L2), and boundary term vanishing under
angle conditions with flatness rate (L3).

## Main results

* `zpow_boundary_diff_tendsto_zero`: boundary zpow difference → 0 under angle + flatness
* `cutoff_zpow_infrastructure`: full infrastructure for cutoff zpow integrals
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

/-! ## L0: Chain rule for zpow compositions

The derivative of `t ↦ (γ(t) - s)^n` where `n : ℤ` and `γ(t) ≠ s`. -/

/-- HasDerivAt for `(γ(t) - s)^n` when `γ` is differentiable and `γ(t) ≠ s`.
This is the chain rule applied to `z ↦ z^n` composed with `t ↦ γ(t) - s`. -/
theorem hasDerivAt_zpow_comp_sub
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {t : ℝ} {L : ℂ}
    (hγ : HasDerivAt γ L t) (hne : γ t ≠ s) :
    HasDerivAt (fun t => (γ t - s) ^ n)
      (↑n * (γ t - s) ^ (n - 1) * L) t := by
  have hγ_sub : HasDerivAt (fun t => γ t - s) L t :=
    hγ.sub_const s
  have h_base : HasDerivAt (· ^ n) (↑n * (γ t - s) ^ (n - 1)) (γ t - s) :=
    hasDerivAt_zpow n (γ t - s) (Or.inl (sub_ne_zero.mpr hne))
  have h_comp := h_base.comp t hγ_sub
  -- comp gives derivative (n * (γ t - s) ^ (n-1)) • L, need to convert smul to mul
  refine h_comp.congr_deriv ?_
  simp

/-- ContinuousOn for `t ↦ (γ(t) - s)^n` on a set where `γ(t) ≠ s`. -/
theorem continuousOn_zpow_comp_sub
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {A : Set ℝ}
    (hγ : ContinuousOn γ A)
    (hne : ∀ t ∈ A, γ t ≠ s) :
    ContinuousOn (fun t => (γ t - s) ^ n) A := by
  apply ContinuousOn.zpow₀ (hγ.sub continuousOn_const)
  intro t ht
  exact Or.inl (sub_ne_zero.mpr (hne t ht))

/-! ## L1: FTC for negative powers on parameterized curves

When `γ` is differentiable and avoids `s` on `[a, b]`, the integral of
`(γ(t) - s)^{-m} · γ'(t)` equals the boundary difference of the primitive
`(γ(t) - s)^{1-m} / (1-m)`. -/

/-- FTC for the integral of `(γ(t) - s)^n · γ'(t)` on `[a, b]` when `γ(t) ≠ s`
on `[a, b]` and `n ≠ -1`. The primitive is `(γ(t) - s)^{n+1} / (n+1)`. -/
theorem integral_zpow_comp_sub_mul_deriv
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} (hn : n ≠ -1)
    {a b : ℝ} (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ s)
    -- Piecewise differentiability: differentiable off a countable set
    (E : Set ℝ) (hE : E.Countable) (_hE_sub : E ∩ Ioo a b ⊆ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ E → DifferentiableAt ℝ γ t)
    -- Integrability of the integrand
    (h_int : IntervalIntegrable
      (fun t => (γ t - s) ^ n * (deriv γ t : ℂ)) MeasureTheory.volume a b) :
    ∫ t in a..b, (γ t - s) ^ n * (deriv γ t : ℂ) =
      ((γ b - s) ^ (n + 1) - (γ a - s) ^ (n + 1)) / (↑(n + 1) : ℂ) := by
  -- Key fact: n + 1 ≠ 0 since n ≠ -1
  have hn1 : (n : ℤ) + 1 ≠ 0 := by omega
  have hn1_cast : (↑(n + 1) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn1
  -- Primitive: F(t) = (γ(t) - s)^{n+1} / (n+1)
  set F : ℝ → ℂ := fun t => (γ t - s) ^ (n + 1) / (↑(n + 1) : ℂ) with hF_def
  -- Integrand
  set f : ℝ → ℂ := fun t => (γ t - s) ^ n * (deriv γ t : ℂ) with hf_def
  -- F is continuous on [a, b]
  have hF_cont : ContinuousOn F (Icc a b) :=
    (continuousOn_zpow_comp_sub hγ_cont hγ_ne (n := n + 1)).div_const _
  -- Countable exceptional set for FTC: use E ∩ Ioo a b
  have hE_count : (E ∩ Ioo a b).Countable := hE.mono Set.inter_subset_left
  -- HasDerivAt F f on (a, b) \ (E ∩ Ioo a b)
  have hF_deriv : ∀ t ∈ Ioo a b \ (E ∩ Ioo a b),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not_E : t ∉ E := fun hE_mem => ht_not ⟨hE_mem, ht⟩
    have hγ_da := (hγ_diff t ht ht_not_E).hasDerivAt
    have hne : γ t ≠ s := hγ_ne t (Ioo_subset_Icc_self ht)
    -- Chain rule: d/dt[(γ(t)-s)^{n+1}] = (n+1) * (γ(t)-s)^n * γ'(t)
    have h_zpow := hasDerivAt_zpow_comp_sub (n := n + 1) hγ_da hne
    -- Divide by (n+1)
    have h_div := h_zpow.div_const (↑(n + 1) : ℂ)
    -- Need to show: (n+1) * (γ t - s)^((n+1)-1) * deriv γ t / (n+1)
    --             = (γ t - s)^n * deriv γ t
    show HasDerivAt F ((γ t - s) ^ n * ↑(deriv γ t)) t
    have : (↑(n + 1) : ℂ) * (γ t - s) ^ (n + 1 - 1) * ↑(deriv γ t) / (↑(n + 1) : ℂ)
        = (γ t - s) ^ n * ↑(deriv γ t) := by
      rw [show (n + 1 : ℤ) - 1 = n from by ring]
      rw [mul_assoc, mul_div_cancel_left₀ _ hn1_cast]
    rw [← this]
    exact h_div
  -- Apply FTC
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f hab hE_count hF_cont hF_deriv h_int
  rw [h_ftc]
  -- F(b) - F(a) = ((γ b - s)^{n+1} - (γ a - s)^{n+1}) / (n+1)
  simp only [F]
  rw [← sub_div]

/-! ## L2: Exit times and direction convergence

For a piecewise C¹ immersion passing through `s` at parameter `t₀`, the curve
enters and exits the ε-ball around `s` at unique parameters near `t₀`. The
directions `(γ(t±) - s) / ‖γ(t±) - s‖` converge to the tangent directions. -/

/-- Near a crossing point of an immersion, there exists a neighborhood such that
the curve only crosses the singularity at that one point. -/
theorem exists_unique_crossing_neighborhood
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s) :
    ∃ a' b', t₀ ∈ Set.Ioo a' b' ∧ Icc a' b' ⊆ Icc γ.a γ.b ∧
      ∀ t ∈ Icc a' b', γ.toFun t = s → t = t₀ := by
  obtain ⟨a', b', ha'_lt, ht₀_lt_b', h_sub, h_unique, _⟩ :=
    _root_.exists_isolated_crossing_interval γ s t₀ ht₀ hcross
  exact ⟨a', b', ⟨ha'_lt, ht₀_lt_b'⟩, h_sub, h_unique⟩

/-- As `ε → 0⁺`, the direction from `s` to the first right exit point of the
ε-ball converges to the right tangent direction (normalized). Specifically,
`(γ(t₊(ε)) - s) / ‖γ(t₊(ε)) - s‖ → L_right / ‖L_right‖`.

This follows from the first-order Taylor approximation
`γ(t) - s ≈ (t - t₀) · L_right` and `‖γ(t) - s‖ ≈ |t - t₀| · ‖L_right‖`. -/
theorem crossing_direction_right_tendsto
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_right : ℂ) (hL : L_right ≠ 0)
    (hL_lim : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_right)) :
    Tendsto (fun ε => (γ.toFun (t₀ + ε) - s) / ‖γ.toFun (t₀ + ε) - s‖)
      (𝓝[>] 0) (𝓝 (L_right / ‖L_right‖)) := by
  -- Step 1: Obtain HasDerivWithinAt γ.toFun L_right (Ici t₀) t₀.
  -- Find (t₀, δ) ⊆ Icc γ.a γ.b with no partition points.
  have ht₀_Icc : t₀ ∈ Icc γ.a γ.b := Ioo_subset_Icc_self ht₀
  -- Filter partition points above t₀ and find the nearest one.
  let P := γ.toPiecewiseC1Curve.partition.filter (t₀ < ·)
  have hP_ne : P.Nonempty :=
    ⟨γ.b, Finset.mem_filter.mpr
      ⟨γ.toPiecewiseC1Curve.endpoints_in_partition.2, ht₀.2⟩⟩
  let δ := P.min' hP_ne
  have hδ_in : δ ∈ P := Finset.min'_mem _ hP_ne
  have hδ_in_part : δ ∈ γ.toPiecewiseC1Curve.partition :=
    (Finset.mem_filter.mp hδ_in).1
  have hδ_gt : t₀ < δ := (Finset.mem_filter.mp hδ_in).2
  have hδ_le_b : δ ≤ γ.b := (γ.toPiecewiseC1Curve.partition_subset hδ_in_part).2
  -- No partition points in (t₀, δ).
  have h_no_part : ∀ t ∈ Ioo t₀ δ, t ∉ γ.toPiecewiseC1Curve.partition := by
    intro t ht htp
    have ht_in : t ∈ P := Finset.mem_filter.mpr ⟨htp, ht.1⟩
    linarith [Finset.min'_le P t ht_in, ht.2]
  have h_sub : Ioo t₀ δ ⊆ Icc γ.a γ.b :=
    fun t ht => ⟨le_of_lt (lt_trans ht₀.1 ht.1), le_trans (le_of_lt ht.2) hδ_le_b⟩
  have h_diff : DifferentiableOn ℝ γ.toFun (Ioo t₀ δ) := fun t ht =>
    (γ.toPiecewiseC1Curve.smooth_off_partition t (h_sub ht)
      (h_no_part t ht)).differentiableWithinAt
  have h_cont : ContinuousWithinAt γ.toFun (Ioo t₀ δ) t₀ :=
    (γ.toPiecewiseC1Curve.continuous_toFun.continuousWithinAt ht₀_Icc).mono h_sub
  have h_deriv : HasDerivWithinAt γ.toFun L_right (Ici t₀) t₀ :=
    hasDerivWithinAt_Ici_of_tendsto_deriv h_diff h_cont (Ioo_mem_nhdsGT hδ_gt) hL_lim
  -- Step 2: Extract the slope convergence from the right and transfer to 𝓝[>] 0.
  have h_slope : Tendsto (fun ε : ℝ => ε⁻¹ • (γ.toFun (t₀ + ε) - s))
      (𝓝[>] 0) (𝓝 L_right) := by
    rw [hasDerivWithinAt_iff_tendsto_slope] at h_deriv
    -- Ici t₀ \ {t₀} = Ioi t₀
    rw [show (Ici t₀ \ {t₀} : Set ℝ) = Ioi t₀ from Ici_diff_left] at h_deriv
    -- Map ε ↦ t₀ + ε sends 𝓝[>] 0 → 𝓝[>] t₀
    have h_map : Tendsto (fun ε : ℝ => t₀ + ε) (𝓝[>] (0 : ℝ)) (𝓝[>] t₀) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun ε : ℝ => t₀ + ε) (𝓝 (0 : ℝ)) (𝓝 t₀) := by
          have := (continuous_add_left t₀).tendsto (0 : ℝ)
          simpa using this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
        exact lt_add_of_pos_right t₀ hε
    exact (h_deriv.comp h_map).congr (fun ε => by
      simp only [Function.comp, slope, vsub_eq_sub, hcross, add_sub_cancel_left])
  -- Step 3: Compose with normalization w ↦ w / ‖w‖.
  -- For ε > 0, w / ‖w‖ = (ε⁻¹ • w) / ‖ε⁻¹ • w‖ (scale invariance).
  suffices h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (γ.toFun (t₀ + ε) - s) / ↑‖γ.toFun (t₀ + ε) - s‖ =
      (ε⁻¹ • (γ.toFun (t₀ + ε) - s)) / ↑‖ε⁻¹ • (γ.toFun (t₀ + ε) - s)‖ by
    have h_norm_cont : Tendsto (fun w : ℂ => w / ↑‖w‖) (𝓝 L_right)
        (𝓝 (L_right / ↑‖L_right‖)) := by
      apply Tendsto.div tendsto_id
        (Complex.continuous_ofReal.continuousAt.tendsto.comp
          continuous_norm.continuousAt.tendsto)
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hL)
    exact (h_norm_cont.comp h_slope).congr' (h_eq.mono fun ε h => h.symm)
  -- Prove the eventual equality: w/‖w‖ = (ε⁻¹•w)/‖ε⁻¹•w‖ for ε > 0
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with ε (hε : (0 : ℝ) < ε)
  show (γ.toFun (t₀ + ε) - s) / ↑‖γ.toFun (t₀ + ε) - s‖ =
    (ε⁻¹ • (γ.toFun (t₀ + ε) - s)) / ↑‖ε⁻¹ • (γ.toFun (t₀ + ε) - s)‖
  set w := γ.toFun (t₀ + ε) - s
  show w / ↑‖w‖ = (ε⁻¹ • w) / ↑‖ε⁻¹ • w‖
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw]
  · -- Positive real scaling preserves normalization: c*w/‖c*w‖ = w/‖w‖ for c > 0
    have h_inv_pos : (0 : ℝ) < ε⁻¹ := inv_pos_of_pos hε
    have h_inv_ne : (↑(ε⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt h_inv_pos)
    rw [Complex.real_smul]
    have h_norm : (↑‖↑(ε⁻¹ : ℝ) * w‖ : ℂ) = ↑(ε⁻¹ : ℝ) * ↑‖w‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos h_inv_pos, Complex.ofReal_mul]
    rw [h_norm, mul_div_mul_left _ _ h_inv_ne]

/-- Left-side analogue of `crossing_direction_right_tendsto`:
`(γ(t₋(ε)) - s) / ‖γ(t₋(ε)) - s‖ → -L_left / ‖L_left‖`. -/
theorem crossing_direction_left_tendsto
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_left : ℂ) (hL : L_left ≠ 0)
    (hL_lim : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_left)) :
    Tendsto (fun ε => (γ.toFun (t₀ - ε) - s) / ‖γ.toFun (t₀ - ε) - s‖)
      (𝓝[>] 0) (𝓝 (-L_left / ‖L_left‖)) := by
  -- Step 1: Find partition-free interval (δ, t₀) and get left-sided derivative.
  have ht₀_Icc : t₀ ∈ Icc γ.a γ.b := Ioo_subset_Icc_self ht₀
  -- Filter partition points below t₀ and find the nearest one.
  let P := γ.toPiecewiseC1Curve.partition.filter (· < t₀)
  have hP_ne : P.Nonempty :=
    ⟨γ.a, Finset.mem_filter.mpr
      ⟨γ.toPiecewiseC1Curve.endpoints_in_partition.1, ht₀.1⟩⟩
  let δ := P.max' hP_ne
  have hδ_in : δ ∈ P := Finset.max'_mem _ hP_ne
  have hδ_in_part : δ ∈ γ.toPiecewiseC1Curve.partition :=
    (Finset.mem_filter.mp hδ_in).1
  have hδ_lt : δ < t₀ := (Finset.mem_filter.mp hδ_in).2
  have ha_le_δ : γ.a ≤ δ := (γ.toPiecewiseC1Curve.partition_subset hδ_in_part).1
  -- No partition points in (δ, t₀).
  have h_no_part : ∀ t ∈ Ioo δ t₀, t ∉ γ.toPiecewiseC1Curve.partition := by
    intro t ht htp
    have ht_in : t ∈ P := Finset.mem_filter.mpr ⟨htp, ht.2⟩
    linarith [Finset.le_max' P t ht_in, ht.1]
  have h_sub : Ioo δ t₀ ⊆ Icc γ.a γ.b :=
    fun t ht => ⟨le_of_lt (lt_of_le_of_lt ha_le_δ ht.1), le_of_lt (lt_trans ht.2 ht₀.2)⟩
  have h_diff : DifferentiableOn ℝ γ.toFun (Ioo δ t₀) := fun t ht =>
    (γ.toPiecewiseC1Curve.smooth_off_partition t (h_sub ht)
      (h_no_part t ht)).differentiableWithinAt
  have h_cont : ContinuousWithinAt γ.toFun (Ioo δ t₀) t₀ :=
    (γ.toPiecewiseC1Curve.continuous_toFun.continuousWithinAt ht₀_Icc).mono h_sub
  have h_deriv : HasDerivWithinAt γ.toFun L_left (Iic t₀) t₀ :=
    hasDerivWithinAt_Iic_of_tendsto_deriv h_diff h_cont (Ioo_mem_nhdsLT hδ_lt) hL_lim
  -- Step 2: Extract slope convergence and transfer to 𝓝[>] 0.
  -- slope γ.toFun t₀ t → L_left as t → t₀ from left (in 𝓝[<] t₀).
  -- With ε = t₀ - t > 0: slope = (-ε)⁻¹ • (γ(t₀-ε) - s) = -(ε⁻¹ • (γ(t₀-ε) - s))
  -- So ε⁻¹ • (γ(t₀-ε) - s) → -L_left.
  have h_slope : Tendsto (fun ε : ℝ => ε⁻¹ • (γ.toFun (t₀ - ε) - s))
      (𝓝[>] 0) (𝓝 (-L_left)) := by
    rw [hasDerivWithinAt_iff_tendsto_slope] at h_deriv
    rw [show (Iic t₀ \ {t₀} : Set ℝ) = Iio t₀ from Iic_diff_right] at h_deriv
    -- Map ε ↦ t₀ - ε sends 𝓝[>] 0 → 𝓝[<] t₀
    have h_map : Tendsto (fun ε : ℝ => t₀ - ε) (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Tendsto (fun ε : ℝ => t₀ - ε) (𝓝 (0 : ℝ)) (𝓝 t₀) := by
          have := (continuous_sub_left t₀).tendsto (0 : ℝ)
          simpa using this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
        exact sub_lt_self t₀ hε
    -- Compose: slope γ.toFun t₀ (t₀ - ε) → L_left.
    -- slope γ.toFun t₀ (t₀ - ε) = (-ε)⁻¹ • (γ(t₀-ε) - s) = -(ε⁻¹ • (γ(t₀-ε) - s))
    -- So ε⁻¹ • (γ(t₀-ε) - s) → -L_left.
    have h_comp := h_deriv.comp h_map
    have h_neg : Tendsto (fun ε : ℝ => -((-ε)⁻¹ • (γ.toFun (t₀ - ε) - s)))
        (𝓝[>] 0) (𝓝 (-L_left)) := h_comp.neg.congr (fun ε => by
      simp only [Function.comp, slope, vsub_eq_sub]
      rw [hcross]; ring_nf)
    convert h_neg using 1
    ext ε
    rw [inv_neg, neg_smul, neg_neg]
  -- Step 3: Compose with normalization w ↦ w / ‖w‖.
  -- Need to show: -L_left / ‖L_left‖ = -L_left / ‖-L_left‖ (since ‖-L_left‖ = ‖L_left‖).
  have h_norm_neg : ‖-L_left‖ = ‖L_left‖ := norm_neg L_left
  suffices h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (γ.toFun (t₀ - ε) - s) / ↑‖γ.toFun (t₀ - ε) - s‖ =
      (ε⁻¹ • (γ.toFun (t₀ - ε) - s)) / ↑‖ε⁻¹ • (γ.toFun (t₀ - ε) - s)‖ by
    have hL_neg : -L_left ≠ 0 := neg_ne_zero.mpr hL
    have h_norm_cont : Tendsto (fun w : ℂ => w / ↑‖w‖) (𝓝 (-L_left))
        (𝓝 (-L_left / ↑‖-L_left‖)) := by
      apply Tendsto.div tendsto_id
        (Complex.continuous_ofReal.continuousAt.tendsto.comp
          continuous_norm.continuousAt.tendsto)
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hL_neg)
    rw [h_norm_neg] at h_norm_cont
    exact (h_norm_cont.comp h_slope).congr' (h_eq.mono fun ε h => h.symm)
  -- Prove the eventual equality: w/‖w‖ = (ε⁻¹•w)/‖ε⁻¹•w‖ for ε > 0
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with ε (hε : (0 : ℝ) < ε)
  show (γ.toFun (t₀ - ε) - s) / ↑‖γ.toFun (t₀ - ε) - s‖ =
    (ε⁻¹ • (γ.toFun (t₀ - ε) - s)) / ↑‖ε⁻¹ • (γ.toFun (t₀ - ε) - s)‖
  set w := γ.toFun (t₀ - ε) - s
  show w / ↑‖w‖ = (ε⁻¹ • w) / ↑‖ε⁻¹ • w‖
  rcases eq_or_ne w 0 with hw | hw
  · simp [hw]
  · have h_inv_pos : (0 : ℝ) < ε⁻¹ := inv_pos_of_pos hε
    have h_inv_ne : (↑(ε⁻¹ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt h_inv_pos)
    rw [Complex.real_smul]
    have h_norm : (↑‖↑(ε⁻¹ : ℝ) * w‖ : ℂ) = ↑(ε⁻¹ : ℝ) * ↑‖w‖ := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos h_inv_pos, Complex.ofReal_mul]
    rw [h_norm, mul_div_mul_left _ _ h_inv_ne]

/-! ## L3: Boundary term vanishing under angle condition (with flatness rate)

The FTC boundary terms at the ε-cutoff points have the form `w₊^k - w₋^k` where
`w₊, w₋` lie on the ε-sphere (`‖w‖ = ε`) and `k ≤ -1`. Writing `w = ε · u`
with `‖u‖ = 1`, the difference is `ε^k · (u₊^k - u₋^k)`.

Since `k ≤ -1`, `ε^k → ∞` while the angle condition gives `u₊^k - u₋^k → 0`.
Whether the product tends to 0 depends on the **rate** of direction convergence:

- With flatness of order `n`: direction error is `o(ε^{n-1})`, giving
  `u₊^k - u₋^k = o(ε^{n-1})` and the product is `o(ε^{k+n-1})`.
- For this to tend to 0, we need `k + n - 1 ≥ 0`, i.e., `n + k ≥ 1`.
- At a pole of order `m` with Laurent term `(z-s)^{-(k_L+1)}`, the FTC boundary
  exponent is `k = -k_L`. Flatness of order `n = m ≥ k_L + 1` gives
  `k + n - 1 = m - k_L - 1 ≥ 0`. ✓

Reference: Hungerbühler-Wasem, proof of Theorem 3.3, equation (3.4). -/

/-- `v^k - u^k = O(v - u)` near `u ≠ 0`, from differentiability of zpow. -/
private lemma zpow_sub_isBigO (k : ℤ) (u : ℂ) (hu : u ≠ 0) :
    (fun v => v ^ k - u ^ k) =O[𝓝 u] (fun v => v - u) :=
  (hasDerivAt_zpow k u (Or.inl hu)).differentiableAt.isBigO_sub

open Asymptotics in
/-- Direction convergence from isLittleO rate: `‖d(ε) - u‖ = o(ε^{n-1})` implies `d → u`. -/
private lemma direction_tendsto_of_rate
    (w : ℝ → ℂ) (u : ℂ) (n : ℕ) (hn : 2 ≤ n)
    (h_rate : (fun ε => ‖w ε / (↑‖w ε‖ : ℂ) - u‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ)) :
    Tendsto (fun ε => w ε / (↑‖w ε‖ : ℂ)) (𝓝[>] 0) (𝓝 u) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff ℝ]
  calc (fun ε => w ε / ↑‖w ε‖ - u)
      =o[𝓝[>] 0] (fun ε => (ε : ℝ) ^ (n - 1 : ℕ)) := isLittleO_norm_left.mp h_rate
    _ =o[𝓝[>] 0] (fun _ => (1 : ℝ)) := by
        rw [isLittleO_one_iff]
        have := ((continuous_pow (n - 1)).continuousAt (x := (0 : ℝ))).tendsto
        simp only [zero_pow (by omega : n - 1 ≠ 0)] at this
        exact this.mono_left nhdsWithin_le_nhds

open Asymptotics in
/-- Compose IsBigO of zpow diff with direction convergence rate:
`(d(ε)^k - u^k) = O(d(ε) - u)` and `(d(ε) - u) = o(ε^{n-1})` gives `(d(ε)^k - u^k) = o(ε^{n-1})`. -/
private lemma direction_zpow_diff_isLittleO
    (k : ℤ) (u : ℂ) (hu : u ≠ 0) (w : ℝ → ℂ) (n : ℕ) (hn : 2 ≤ n)
    (h_rate : (fun ε => ‖w ε / (↑‖w ε‖ : ℂ) - u‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ)) :
    (fun ε => (w ε / (↑‖w ε‖ : ℂ)) ^ k - u ^ k) =o[𝓝[>] (0 : ℝ)]
      (fun ε => (ε : ℝ) ^ (n - 1 : ℕ)) :=
  ((zpow_sub_isBigO k u hu).comp_tendsto
    (direction_tendsto_of_rate w u n hn h_rate)).trans_isLittleO
    (Asymptotics.isLittleO_norm_left.mp h_rate)

/-- Boundary term vanishing for zpow under angle condition with flatness rate.

When `w_R, w_L` lie on the ε-sphere (`‖w‖ = ε`), directions converge to unit
vectors `uR, uL` at rate `o(ε^{n-1})` (from flatness of order `n`), and the
angle condition ensures `uR^k = uL^k`, the zpow boundary difference tends to 0
provided `n + k ≥ 1`.

**Proof sketch**: `wR^k - wL^k = ε^k · (uR(ε)^k - uL(ε)^k)` where `u(ε) = w(ε)/ε`.
The map `u ↦ u^k` is `O`-Lipschitz near each limit (from differentiability),
so `uR(ε)^k - uR_∞^k = O(uR(ε) - uR_∞) = o(ε^{n-1})`. Under the angle condition,
`uR_∞^k = uL_∞^k`, so `uR(ε)^k - uL(ε)^k = o(ε^{n-1})`. The product
`ε^k · o(ε^{n-1})` tends to 0 since `ε^k · ε^{n-1} = ε^{k+n-1} ≤ 1` for small `ε`. -/
theorem zpow_boundary_diff_tendsto_zero
    (k : ℤ) (hk : k ≤ -1)
    (wR wL : ℝ → ℂ)
    -- On the ε-sphere
    (h_norm_R : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wR ε‖ = ε)
    (h_norm_L : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wL ε‖ = ε)
    (h_neR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), wR ε ≠ 0)
    (h_neL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), wL ε ≠ 0)
    -- Direction limits on the unit circle
    (uR uL : ℂ) (huR : ‖uR‖ = 1) (huL : ‖uL‖ = 1)
    -- Angle condition on zpow: limiting zpow values agree
    (h_angle : uR ^ k = uL ^ k)
    -- Flatness rate: direction convergence is o(ε^{n-1}) for flatness order n
    (n : ℕ) (hn : (n : ℤ) + k ≥ 1)
    (h_rate_R : (fun ε => ‖wR ε / (↑‖wR ε‖ : ℂ) - uR‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ))
    (h_rate_L : (fun ε => ‖wL ε / (↑‖wL ε‖ : ℂ) - uL‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (n - 1 : ℕ)) :
    Tendsto (fun ε => wR ε ^ k - wL ε ^ k)
      (𝓝[>] 0) (𝓝 0) := by
  have hn2 : 2 ≤ n := by omega
  have huR_ne : uR ≠ 0 := norm_ne_zero_iff.mp (by rw [huR]; exact one_ne_zero)
  have huL_ne : uL ≠ 0 := norm_ne_zero_iff.mp (by rw [huL]; exact one_ne_zero)
  -- Direction zpow diffs are o(ε^{n-1})
  have h_oR := direction_zpow_diff_isLittleO k uR huR_ne wR n hn2 h_rate_R
  have h_oL := direction_zpow_diff_isLittleO k uL huL_ne wL n hn2 h_rate_L
  -- Combined direction diff is o(ε^{n-1}) using angle condition
  have h_diff : (fun ε => (wR ε / (↑‖wR ε‖ : ℂ)) ^ k - (wL ε / (↑‖wL ε‖ : ℂ)) ^ k)
      =o[𝓝[>] 0] (fun ε => (ε : ℝ) ^ (n - 1 : ℕ)) := by
    have h_eq : (fun ε => (wR ε / ↑‖wR ε‖) ^ k - (wL ε / ↑‖wL ε‖) ^ k) =
        fun ε => ((wR ε / ↑‖wR ε‖) ^ k - uR ^ k) -
          ((wL ε / ↑‖wL ε‖) ^ k - uL ^ k) := by
      ext ε; rw [h_angle]; ring
    rw [h_eq]; exact h_oR.sub h_oL
  -- ε-δ proof: factor wR^k - wL^k = (↑ε)^k * (direction diff), bound by η
  rw [Metric.tendsto_nhds]
  intro η hη
  -- Get quantitative bound from isLittleO (unfold IsBigOWith to ∀ᶠ)
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(wR ε / (↑‖wR ε‖ : ℂ)) ^ k - (wL ε / (↑‖wL ε‖ : ℂ)) ^ k‖ ≤
      η / 2 * ‖(ε : ℝ) ^ (n - 1 : ℕ)‖ := (h_diff.def' (half_pos hη)).bound
  filter_upwards [h_bound, h_norm_R, h_norm_L, h_neR, h_neL,
    Ioo_mem_nhdsGT one_pos] with ε h_bnd h_nR h_nL h_ne_R h_ne_L hε_mem
  obtain ⟨hε_pos, hε_lt⟩ := hε_mem
  rw [dist_eq_norm, sub_zero]
  -- Factor: wR^k = (↑ε)^k * (wR/↑‖wR‖)^k using mul_zpow
  have h_factR : wR ε ^ k = (↑ε : ℂ) ^ k * (wR ε / (↑‖wR ε‖ : ℂ)) ^ k := by
    have h_ne : (↑‖wR ε‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h_ne_R)
    have : wR ε = (↑‖wR ε‖ : ℂ) * (wR ε / (↑‖wR ε‖ : ℂ)) := by field_simp
    conv_lhs => rw [this]
    rw [mul_zpow, h_nR]
  have h_factL : wL ε ^ k = (↑ε : ℂ) ^ k * (wL ε / (↑‖wL ε‖ : ℂ)) ^ k := by
    have h_ne : (↑‖wL ε‖ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h_ne_L)
    have : wL ε = (↑‖wL ε‖ : ℂ) * (wL ε / (↑‖wL ε‖ : ℂ)) := by field_simp
    conv_lhs => rw [this]
    rw [mul_zpow, h_nL]
  rw [h_factR, h_factL, ← mul_sub, norm_mul, Complex.norm_zpow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε_pos]
  -- Simplify ‖ε^{n-1}‖ in the bound
  have h_norm_pow : ‖(ε : ℝ) ^ (n - 1 : ℕ)‖ = ε ^ (n - 1 : ℕ) :=
    (Real.norm_eq_abs _).trans (abs_of_pos (pow_pos hε_pos _))
  rw [h_norm_pow] at h_bnd
  -- ε^k * ε^{n-1} ≤ 1 for 0 < ε < 1 and k + n - 1 ≥ 0
  have h_pow_le : (ε : ℝ) ^ k * (ε : ℝ) ^ (n - 1 : ℕ) ≤ 1 := by
    rw [← zpow_natCast ε (n - 1), ← zpow_add₀ (ne_of_gt hε_pos)]
    exact zpow_le_one₀ hε_pos hε_lt.le (by omega)
  -- Assemble: ε^k * ‖direction diff‖ ≤ (η/2) * (ε^k * ε^{n-1}) ≤ η/2 < η
  calc ε ^ k * ‖(wR ε / ↑‖wR ε‖) ^ k - (wL ε / ↑‖wL ε‖) ^ k‖
      ≤ ε ^ k * (η / 2 * ε ^ (n - 1 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left h_bnd (zpow_nonneg hε_pos.le k)
    _ = η / 2 * (ε ^ k * ε ^ (n - 1 : ℕ)) := by ring
    _ ≤ η / 2 * 1 := by exact mul_le_mul_of_nonneg_left h_pow_le (half_pos hη).le
    _ = η / 2 := mul_one _
    _ < η := half_lt_self hη

/-! ## Bridge: tangent deviation → direction norm difference

For unit vectors `u, v` with `‖u - v‖ ≤ 1`:
`‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖`.

This bridges `IsFlatOfOrder` (stated in terms of tangent deviation) to the
direction rate condition in `zpow_boundary_diff_tendsto_zero` (L3). -/

/-- Simplification: for unit `v`, the normSq divisor in orthogonal projection
drops out. -/
private lemma orthogonalProjectionComplex_of_norm_one (u v : ℂ) (hv : ‖v‖ = 1) :
    orthogonalProjectionComplex u v = (u * starRingEnd ℂ v).re • v := by
  unfold orthogonalProjectionComplex
  rw [Complex.normSq_eq_norm_sq, hv, one_pow, div_one]

/-- For unit `v`: `tangentDeviation u v = u - Re(u * conj v) • v`. -/
private lemma tangentDeviation_of_norm_one (u v : ℂ) (hv : ‖v‖ = 1) :
    tangentDeviation u v = u - (u * starRingEnd ℂ v).re • v := by
  rw [tangentDeviation, orthogonalProjectionComplex_of_norm_one u v hv]

/-- For unit vectors `u, v` with `‖u - v‖ ≤ 1`:
`‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖`.

Proof sketch: `u - v = tangentDeviation(u,v) + (Re(u·v̄) - 1)·v`. Since
`‖u-v‖² = 2 - 2·Re(u·v̄)`, we get `|Re(u·v̄) - 1| = ‖u-v‖²/2 ≤ ‖u-v‖/2`
for `‖u-v‖ ≤ 1`, giving `‖u-v‖ ≤ ‖tangentDeviation‖ + ‖u-v‖/2`. -/
theorem norm_sub_le_tangentDeviation_of_unit (u v : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h_close : ‖u - v‖ ≤ 1) :
    ‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖ := by
  -- Decompose: u - v = tangentDeviation(u,v) + (Re(u·v̄) - 1) • v
  have h_decomp : u - v = tangentDeviation u v + ((u * starRingEnd ℂ v).re - 1) • v := by
    rw [tangentDeviation_of_norm_one u v hv]
    simp only [Complex.real_smul]; push_cast; ring
  -- Bound the projection residual: |Re(u·v̄) - 1| = ‖u - v‖²/2
  have h_normSq : ‖u - v‖ ^ 2 = 2 - 2 * (u * starRingEnd ℂ v).re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, hu, hv, one_pow, starRingEnd_apply]
    ring
  have h_re_le : (u * starRingEnd ℂ v).re ≤ 1 := by
    have h1 : |(u * starRingEnd ℂ v).re| ≤ 1 := by
      calc |(u * starRingEnd ℂ v).re| ≤ ‖u * starRingEnd ℂ v‖ :=
            Complex.abs_re_le_norm _
        _ = 1 := by rw [norm_mul, hu, starRingEnd_apply, norm_star, hv, mul_one]
    exact le_of_abs_le h1
  have h_re_bound : 1 - (u * starRingEnd ℂ v).re = ‖u - v‖ ^ 2 / 2 := by linarith
  -- Triangle inequality on the decomposition
  have h_tri := norm_add_le (tangentDeviation u v) (((u * starRingEnd ℂ v).re - 1) • v)
  rw [← h_decomp] at h_tri
  have h_smul_norm : ‖((u * starRingEnd ℂ v).re - 1) • v‖ = ‖u - v‖ ^ 2 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_nonpos (by linarith), neg_sub,
      h_re_bound]
  -- ‖u - v‖ ≤ ‖tangentDeviation‖ + ‖u - v‖²/2 ≤ ‖tangentDeviation‖ + ‖u - v‖/2
  have h_sq_le : ‖u - v‖ ^ 2 / 2 ≤ ‖u - v‖ / 2 := by
    rw [div_le_div_iff_of_pos_right two_pos]
    calc ‖u - v‖ ^ 2 = ‖u - v‖ * ‖u - v‖ := sq _
      _ ≤ ‖u - v‖ * 1 := by exact mul_le_mul_of_nonneg_left h_close (norm_nonneg _)
      _ = ‖u - v‖ := mul_one _
  linarith [h_smul_norm, h_sq_le, h_tri]

/-- For unit vectors `z₁, z₂` and integer exponent `k`, if
`k · (arg z₁ - arg z₂) ∈ 2πℤ`, then `z₁^k = z₂^k`.

Proof: write unit `z = exp(i · arg z)` via `norm_mul_exp_arg_mul_I`, then
reduce to `exp_eq_exp_iff_exists_int`. -/
lemma unit_zpow_eq_of_angle_multiple
    (z₁ z₂ : ℂ) (k : ℤ)
    (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (h : ∃ n : ℤ, (↑k : ℝ) * (arg z₁ - arg z₂) = ↑n * (2 * Real.pi)) :
    z₁ ^ k = z₂ ^ k := by
  have h₁ : z₁ = exp (↑(arg z₁) * I) := by
    have := norm_mul_exp_arg_mul_I z₁
    rw [hz₁, ofReal_one, one_mul] at this
    exact this.symm
  have h₂ : z₂ = exp (↑(arg z₂) * I) := by
    have := norm_mul_exp_arg_mul_I z₂
    rw [hz₂, ofReal_one, one_mul] at this
    exact this.symm
  rw [h₁, h₂, ← exp_int_mul, ← exp_int_mul]
  rw [exp_eq_exp_iff_exists_int]
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  rw [← sub_eq_zero]
  have h_eq : ↑k * (↑(arg z₁) * I) - (↑k * (↑(arg z₂) * I) + ↑n * (2 * ↑Real.pi * I)) =
      ↑((↑k : ℝ) * (arg z₁ - arg z₂) - (↑n : ℝ) * (2 * Real.pi)) * I := by
    push_cast; ring
  rw [h_eq, mul_eq_zero]
  left
  rw [ofReal_eq_zero]
  linarith

/-- Orthogonal projection scales linearly in the first argument:
`orthogonalProjectionComplex (c • w) L = c • orthogonalProjectionComplex w L` for real `c`. -/
private lemma orthogonalProjectionComplex_real_smul_left (c : ℝ) (w L : ℂ) :
    orthogonalProjectionComplex (c • w) L = c • orthogonalProjectionComplex w L := by
  simp only [orthogonalProjectionComplex, Complex.real_smul]
  rw [show ↑c * w * (starRingEnd ℂ) L = ↑c * (w * (starRingEnd ℂ) L) from mul_assoc _ _ _,
    Complex.re_ofReal_mul]
  push_cast; ring

/-- Tangent deviation scales linearly in the first argument:
`tangentDeviation (c • w) L = c • tangentDeviation w L` for real `c`. -/
private lemma tangentDeviation_real_smul_left (c : ℝ) (w L : ℂ) :
    tangentDeviation (c • w) L = c • tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex_real_smul_left, smul_sub]

/-- Orthogonal projection is invariant under nonzero real scaling of the direction:
`orthogonalProjectionComplex w (c • L) = orthogonalProjectionComplex w L` for `c ≠ 0` real. -/
private lemma orthogonalProjectionComplex_real_smul_right (c : ℝ) (hc : c ≠ 0) (w L : ℂ) :
    orthogonalProjectionComplex w (c • L) = orthogonalProjectionComplex w L := by
  unfold orthogonalProjectionComplex
  simp only [Complex.real_smul]
  conv_lhs =>
    rw [show starRingEnd ℂ (↑c * L) = star (↑c * L) from rfl,
      star_mul', show star (↑c : ℂ) = ↑c from by
        rw [Complex.star_def]; exact Complex.conj_ofReal c,
      show star L = starRingEnd ℂ L from rfl]
  rw [show Complex.normSq ((↑c : ℂ) * L) = c ^ 2 * Complex.normSq L from by
    rw [Complex.normSq_mul, Complex.normSq_ofReal, sq],
    show w * (↑c * starRingEnd ℂ L) = ↑c * (w * starRingEnd ℂ L) from by ring,
    Complex.re_ofReal_mul]
  set r := (w * starRingEnd ℂ L).re
  set nS := Complex.normSq L
  rw [show (↑(c * r / (c ^ 2 * nS)) : ℂ) * ((↑c : ℂ) * L) =
    ↑(c * r / (c ^ 2 * nS) * c) * L from by push_cast; ring,
    show c * r / (c ^ 2 * nS) * c = r / nS from by rw [sq]; field_simp]

/-- Tangent deviation is invariant under nonzero real scaling of the direction:
`tangentDeviation w (c • L) = tangentDeviation w L` for `c ≠ 0` real. -/
private lemma tangentDeviation_real_smul_right (c : ℝ) (hc : c ≠ 0) (w L : ℂ) :
    tangentDeviation w (c • L) = tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex_real_smul_right c hc]

/-- Direction convergence rate from flatness: if `IsFlatOfOrder γ t₀ m` and
`ε ↦ σ(ε)` are exit times with `σ(ε) → t₀⁺` and `‖γ(σ(ε)) - s‖ = ε`,
then the normalized direction converges to the tangent direction at rate `o(ε^{m-1})`.

This bridges the parameter-space flatness (stated in terms of `t → t₀`) to
the ε-space rate (stated in terms of `ε → 0`). -/
private lemma direction_rate_from_flatness_right
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_R : ℂ) (hL_R_ne : L_R ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R))
    -- Exit time function and its properties
    (σ : ℝ → ℝ) (_hσ_gt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), t₀ < σ ε)
    (_hσ_le_b : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ ε ≤ γ.b)
    (hσ_norm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ.toFun (σ ε) - s‖ = ε)
    (hσ_tendsto : Tendsto σ (𝓝[>] 0) (𝓝[>] t₀)) :
    (fun ε => ‖(γ.toFun (σ ε) - s) / (↑‖γ.toFun (σ ε) - s‖ : ℂ) -
      L_R / ↑‖L_R‖‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (m - 1 : ℕ) := by
  set v₀ := L_R / (↑‖L_R‖ : ℂ) with hv₀_def
  have hL_pos : (0 : ℝ) < ‖L_R‖ := norm_pos_iff.mpr hL_R_ne
  have hL_ne : ‖L_R‖ ≠ 0 := ne_of_gt hL_pos
  have hv₀_norm : ‖v₀‖ = 1 := by
    rw [hv₀_def]
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL_pos, div_self hL_ne]
  -- Step 1: Flatness bound in ε-space
  have h_flat_eps : (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) L_R‖) =o[𝓝[>] 0]
      (fun ε => ε ^ m) := by
    have h1 := (h_flat.right_flat L_R hL_R_ne htend_R).congr
      (fun t => by rw [hcross]) (fun t => by rw [hcross])
    exact ((h1.comp_tendsto hσ_tendsto).congr (fun _ => rfl) (fun _ => rfl)).trans_eventuallyEq
      (by filter_upwards [hσ_norm] with ε hε; simp only [Function.comp_def]; rw [hε])
  -- Step 2: Re(w * conj L_R) > 0 eventually
  -- Proof: the derivative tends to L_R from the right, so (γ(t)-s)/(t-t₀) → L_R.
  -- Taking Re(· * conj L_R): the ratio's re part → ‖L_R‖² > 0.
  -- Since t - t₀ > 0 from the right, Re(w * conj L_R) > 0.
  have hcont : ContinuousAt γ.toFun t₀ :=
    γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hdiff_right : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ.toFun t := by
    have hcl : IsClosed ((↑γ.partition : Set ℝ) \ {t₀}) :=
      (γ.partition.finite_toSet.subset Set.diff_subset).isClosed
    filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (Set.mem_compl (by simp))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2), self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂ fun hm => ht₁ ⟨hm, ne_of_gt (Set.mem_Ioi.mp ht₃)⟩
  obtain ⟨s_set, hs_mem, hs_diff⟩ := hdiff_right.exists_mem
  have hderiv : HasDerivWithinAt γ.toFun L_R (Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_iff_Ici.mpr (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hcont.continuousWithinAt hs_mem htend_R)
  -- Re(w(t) * conj L_R) > 0 for t near t₀ from the right
  -- From HasDerivWithinAt: γ(t)-s = (t-t₀)•L_R + r(t) with r = o(t-t₀),
  -- so Re(w*conj L_R) = (t-t₀)*‖L_R‖² + Re(r*conj L_R) > 0 for small t-t₀ > 0.
  -- Re(L_R * conj L_R) = ‖L_R‖² > 0
  have hReLR : 0 < (L_R * starRingEnd ℂ L_R).re := by
    rw [Complex.mul_conj]
    simp only [Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hL_R_ne
  -- slope(t) := (γ(t)-s)/(t-t₀) → L_R as t → t₀ from the right
  have h_slope : Tendsto (slope γ.toFun t₀) (𝓝[>] t₀) (𝓝 L_R) :=
    (hasDerivWithinAt_iff_tendsto_slope' Set.notMem_Ioi_self).mp hderiv
  -- Re(slope(t) * conj L_R) → Re(L_R * conj L_R) > 0 from the right
  -- Since slope(t) = (γ(t)-s)/(t-t₀) = (γ(t)-s) * (1/(t-t₀)) and t - t₀ > 0:
  -- Re((γ(t)-s) * conj L_R) = (t-t₀) * Re(slope(t) * conj L_R) > 0
  have h_re_pos_t : ∀ᶠ t in 𝓝[>] t₀,
      0 < ((γ.toFun t - s) * starRingEnd ℂ L_R).re := by
    -- Re(slope * conj L_R) → Re(L_R * conj L_R) > 0
    have h_slope_re : Tendsto (fun t => (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re)
        (𝓝[>] t₀) (𝓝 (L_R * starRingEnd ℂ L_R).re) :=
      (continuous_re.comp (continuous_mul_right _)).continuousAt.tendsto.comp h_slope
    -- Eventually Re(slope * conj L_R) > 0
    have h_ev := h_slope_re (Ioi_mem_nhds hReLR)
    filter_upwards [h_ev, self_mem_nhdsWithin] with t ht ht_pos
    have ht_gt : t₀ < t := Set.mem_Ioi.mp ht_pos
    have h_pos_factor : (0 : ℝ) < t - t₀ := sub_pos.mpr ht_gt
    -- Extract: 0 < Re(slope γ t₀ t * conj L_R)
    have h_slope_pos : 0 < (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re :=
      Set.mem_Ioi.mp (Set.mem_preimage.mp ht)
    -- (t-t₀) • slope = γ(t) - γ(t₀) = γ(t) - s
    -- So Re((γ(t)-s) * conj L_R) = (t-t₀) * Re(slope * conj L_R) > 0
    have h_key : (t - t₀) * (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re =
        ((γ.toFun t - s) * starRingEnd ℂ L_R).re := by
      have hsub : (t - t₀) • slope γ.toFun t₀ t = γ.toFun t -ᵥ γ.toFun t₀ :=
        sub_smul_slope _ _ _
      rw [vsub_eq_sub, hcross] at hsub
      have hmul : (↑(t - t₀) : ℂ) * (slope γ.toFun t₀ t * starRingEnd ℂ L_R) =
          (γ.toFun t - s) * starRingEnd ℂ L_R := by
        rw [← mul_assoc, ← Complex.real_smul, hsub]
      simp only [← hmul, mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith [mul_pos h_pos_factor h_slope_pos]
  have h_re_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ((γ.toFun (σ ε) - s) * starRingEnd ℂ L_R).re :=
    hσ_tendsto.eventually h_re_pos_t
  -- Step 3: Pointwise bound
  rw [Asymptotics.isLittleO_iff]; intro c hc_pos
  have hcsq : (0 : ℝ) < c / Real.sqrt 2 := div_pos hc_pos (Real.sqrt_pos.mpr two_pos)
  filter_upwards [(Asymptotics.isLittleO_iff.mp h_flat_eps) hcsq, hσ_norm, h_re_pos] with
    ε h_td_bound hε_norm h_re
  set w := γ.toFun (σ ε) - s
  have hw_ne : w ≠ 0 := by intro h; simp [h] at h_re
  have hw_ne' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw_ne
  have hε_pos : 0 < ε := by rw [← hε_norm]; exact norm_pos_iff.mpr hw_ne
  set u := w / (↑‖w‖ : ℂ)
  have hu_norm : ‖u‖ = 1 := by
    show ‖w / (↑‖w‖ : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hw_ne']
  -- td(u,v₀) scaling: ‖td(u,v₀)‖ = ‖td(w,L_R)‖ / ‖w‖
  have h_td_scale : ‖tangentDeviation u v₀‖ = ‖tangentDeviation w L_R‖ / ‖w‖ := by
    show ‖tangentDeviation (w / (↑‖w‖ : ℂ)) (L_R / (↑‖L_R‖ : ℂ))‖ = _
    have h1 : (w / (↑‖w‖ : ℂ) : ℂ) = (‖w‖⁻¹ : ℝ) • w := by
      simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]
    have h2 : (L_R / (↑‖L_R‖ : ℂ) : ℂ) = (‖L_R‖⁻¹ : ℝ) • L_R := by
      simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]
    rw [h1, h2, tangentDeviation_real_smul_right _ (inv_ne_zero hL_ne),
      tangentDeviation_real_smul_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_eq_div]
  -- Re(u * conj v₀) > 0
  set R := (u * starRingEnd ℂ v₀).re
  have hR_pos : 0 < R := by
    show 0 < (w / (↑‖w‖ : ℂ) * starRingEnd ℂ (L_R / (↑‖L_R‖ : ℂ))).re
    rw [map_div₀ (starRingEnd ℂ), Complex.conj_ofReal,
      div_mul_div_comm, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    exact div_pos h_re (mul_pos (by rw [hε_norm]; exact hε_pos) hL_pos)
  -- Geometric bound: ‖u-v₀‖² ≤ 2*‖td(u,v₀)‖² when Re(u·v̄₀) > 0
  have h_sq : ‖u - v₀‖ ^ 2 ≤ 2 * ‖tangentDeviation u v₀‖ ^ 2 := by
    -- ‖u-v₀‖² = 2 - 2R
    have h_lhs : ‖u - v₀‖ ^ 2 = 2 - 2 * R := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp only [Complex.normSq_eq_norm_sq, hu_norm, hv₀_norm, one_pow]; ring
    -- ‖td(u,v₀)‖² = 1 - R²
    have h_rhs : ‖tangentDeviation u v₀‖ ^ 2 = 1 - R ^ 2 := by
      rw [tangentDeviation_of_norm_one u v₀ hv₀_norm,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp only [Complex.normSq_eq_norm_sq, hu_norm, one_pow,
        norm_smul, Real.norm_eq_abs, hv₀_norm, mul_one, sq_abs]
      -- Simplify starRingEnd ℂ (R • v₀) = ↑R * starRingEnd ℂ v₀
      have hstar : (starRingEnd ℂ) (R • v₀) = (↑R : ℂ) * (starRingEnd ℂ) v₀ := by
        rw [Complex.real_smul, map_mul (starRingEnd ℂ), Complex.conj_ofReal]
      rw [hstar]
      -- Simplify (u * (↑R * starRingEnd ℂ v₀)).re = R²
      have hre : (u * ((↑R : ℂ) * starRingEnd ℂ v₀)).re = R * R := by
        rw [← mul_assoc, mul_comm u (↑R : ℂ), mul_assoc,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hre]
      ring
    have hR_le : R ≤ 1 := by nlinarith [sq_nonneg (‖tangentDeviation u v₀‖)]
    rw [h_lhs, h_rhs]; nlinarith [hR_pos.le, hR_le]
  -- ‖u-v₀‖ ≤ √2 * ‖td(u,v₀)‖
  have h_bound : ‖u - v₀‖ ≤ Real.sqrt 2 * ‖tangentDeviation u v₀‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (u - v₀)),
      ← Real.sqrt_sq (norm_nonneg (tangentDeviation u v₀)),
      ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt h_sq
  -- Assemble: ‖u-v₀‖ ≤ √2 * ‖td(w,L_R)‖/ε ≤ c * ε^{m-1}
  rw [h_td_scale, hε_norm] at h_bound
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  -- Strip double norm from h_td_bound
  have h_td_bound' : ‖tangentDeviation w L_R‖ ≤ c / Real.sqrt 2 * ε ^ m := by
    rwa [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (pow_nonneg hε_pos.le _)] at h_td_bound
  calc ‖u - v₀‖
      ≤ Real.sqrt 2 * (‖tangentDeviation w L_R‖ / ε) := h_bound
    _ ≤ Real.sqrt 2 * (c / Real.sqrt 2 * ε ^ m / ε) := by gcongr
    _ = c * (ε ^ m / ε) := by field_simp
    _ = c * ε ^ (m - 1) := by
        congr 1
        have hpow : ε ^ m = ε ^ (m - 1) * ε := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
        rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hε_pos)]
    _ = c * ‖ε ^ (m - 1 : ℕ)‖ := by rw [Real.norm_of_nonneg (pow_nonneg hε_pos.le _)]

/-- Left-side analogue of `direction_rate_from_flatness_right`. -/
private lemma direction_rate_from_flatness_left
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_L : ℂ) (hL_L_ne : L_L ≠ 0)
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L))
    -- Exit time function and its properties
    (σ : ℝ → ℝ) (_hσ_lt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), σ ε < t₀)
    (_hσ_ge_a : ∀ᶠ ε in 𝓝[>] (0 : ℝ), γ.a ≤ σ ε)
    (hσ_norm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖γ.toFun (σ ε) - s‖ = ε)
    (hσ_tendsto : Tendsto σ (𝓝[>] 0) (𝓝[<] t₀)) :
    (fun ε => ‖(γ.toFun (σ ε) - s) / (↑‖γ.toFun (σ ε) - s‖ : ℂ) -
      (-L_L / ↑‖L_L‖)‖) =o[𝓝[>] (0 : ℝ)]
      fun ε => ε ^ (m - 1 : ℕ) := by
  set v₀ := -L_L / (↑‖L_L‖ : ℂ) with hv₀_def
  have hL_pos : (0 : ℝ) < ‖L_L‖ := norm_pos_iff.mpr hL_L_ne
  have hL_ne : ‖L_L‖ ≠ 0 := ne_of_gt hL_pos
  have hv₀_norm : ‖v₀‖ = 1 := by
    rw [hv₀_def]
    simp only [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL_pos,
      div_self hL_ne]
  -- Step 1: Flatness bound in ε-space
  -- left_flat gives td(w, L_L), but we need td(w, -L_L) = td(w, L_L) by scale invariance
  have h_td_eq : ∀ w : ℂ, tangentDeviation w (-L_L) = tangentDeviation w L_L := by
    intro w
    have : -L_L = (-1 : ℝ) • L_L := by simp
    rw [this, tangentDeviation_real_smul_right _ (by norm_num : (-1 : ℝ) ≠ 0)]
  have h_flat_eps : (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) (-L_L)‖) =o[𝓝[>] 0]
      (fun ε => ε ^ m) := by
    have h1 := (h_flat.left_flat L_L hL_L_ne htend_L).congr
      (fun t => by rw [hcross]) (fun t => by rw [hcross])
    have h2 : (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) (-L_L)‖) =
        (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) L_L‖) :=
      funext fun ε => by rw [h_td_eq]
    rw [h2]
    exact ((h1.comp_tendsto hσ_tendsto).congr (fun _ => rfl) (fun _ => rfl)).trans_eventuallyEq
      (by filter_upwards [hσ_norm] with ε hε; simp only [Function.comp_def]; rw [hε])
  -- Step 2: Re(w * conj(-L_L)) > 0 eventually
  -- Proof: the derivative tends to L_L from the left, so (γ(t)-s)/(t-t₀) → L_L.
  -- Taking Re(· * conj(-L_L)): the ratio's re part → Re(L_L * conj(-L_L)) = -‖L_L‖² < 0.
  -- Since t - t₀ < 0 from the left, Re(w * conj(-L_L)) = (t-t₀) * Re(slope * conj(-L_L)) > 0.
  have hcont : ContinuousAt γ.toFun t₀ :=
    γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hdiff_left : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ.toFun t := by
    have hcl : IsClosed ((↑γ.partition : Set ℝ) \ {t₀}) :=
      (γ.partition.finite_toSet.subset Set.diff_subset).isClosed
    filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (Set.mem_compl (by simp))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2), self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂ fun hm => ht₁ ⟨hm, ne_of_lt (Set.mem_Iio.mp ht₃)⟩
  obtain ⟨s_set, hs_mem, hs_diff⟩ := hdiff_left.exists_mem
  have hderiv : HasDerivWithinAt γ.toFun L_L (Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_iff_Iic.mpr (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hcont.continuousWithinAt hs_mem htend_L)
  -- Re(L_L * conj(-L_L)) = -‖L_L‖² < 0
  have hReLLneg : (L_L * starRingEnd ℂ (-L_L)).re < 0 := by
    rw [map_neg, mul_neg, Complex.neg_re, neg_neg_iff_pos, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hL_L_ne
  -- slope(t) := (γ(t)-s)/(t-t₀) → L_L as t → t₀ from the left
  have h_slope : Tendsto (slope γ.toFun t₀) (𝓝[<] t₀) (𝓝 L_L) :=
    (hasDerivWithinAt_iff_tendsto_slope' Set.notMem_Iio_self).mp hderiv
  -- Re(slope(t) * conj(-L_L)) → Re(L_L * conj(-L_L)) < 0 from the left
  -- Since t - t₀ < 0:
  -- Re((γ(t)-s) * conj(-L_L)) = (t-t₀) * Re(slope(t) * conj(-L_L))
  -- = (negative) * (eventually negative) > 0
  have h_re_pos_t : ∀ᶠ t in 𝓝[<] t₀,
      0 < ((γ.toFun t - s) * starRingEnd ℂ (-L_L)).re := by
    -- Re(slope * conj(-L_L)) → Re(L_L * conj(-L_L)) < 0
    have h_slope_re : Tendsto (fun t => (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re)
        (𝓝[<] t₀) (𝓝 (L_L * starRingEnd ℂ (-L_L)).re) :=
      (continuous_re.comp (continuous_mul_right _)).continuousAt.tendsto.comp h_slope
    -- Eventually Re(slope * conj(-L_L)) < 0
    have h_ev := h_slope_re (Iio_mem_nhds hReLLneg)
    filter_upwards [h_ev, self_mem_nhdsWithin] with t ht ht_neg
    have ht_lt : t < t₀ := Set.mem_Iio.mp ht_neg
    have h_neg_factor : t - t₀ < 0 := sub_neg.mpr ht_lt
    -- Extract: Re(slope γ t₀ t * conj(-L_L)) < 0
    have h_slope_neg : (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re < 0 :=
      Set.mem_Iio.mp (Set.mem_preimage.mp ht)
    -- (t-t₀) • slope = γ(t) - γ(t₀) = γ(t) - s
    -- So Re((γ(t)-s) * conj(-L_L)) = (t-t₀) * Re(slope * conj(-L_L)) > 0
    have h_key : (t - t₀) * (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re =
        ((γ.toFun t - s) * starRingEnd ℂ (-L_L)).re := by
      have hsub : (t - t₀) • slope γ.toFun t₀ t = γ.toFun t -ᵥ γ.toFun t₀ :=
        sub_smul_slope _ _ _
      rw [vsub_eq_sub, hcross] at hsub
      have hmul : (↑(t - t₀) : ℂ) * (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)) =
          (γ.toFun t - s) * starRingEnd ℂ (-L_L) := by
        rw [← mul_assoc, ← Complex.real_smul, hsub]
      simp only [← hmul, mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    linarith [mul_pos_of_neg_of_neg h_neg_factor h_slope_neg]
  have h_re_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ((γ.toFun (σ ε) - s) * starRingEnd ℂ (-L_L)).re :=
    hσ_tendsto.eventually h_re_pos_t
  -- Step 3: Pointwise bound
  rw [Asymptotics.isLittleO_iff]; intro c hc_pos
  have hcsq : (0 : ℝ) < c / Real.sqrt 2 := div_pos hc_pos (Real.sqrt_pos.mpr two_pos)
  filter_upwards [(Asymptotics.isLittleO_iff.mp h_flat_eps) hcsq, hσ_norm, h_re_pos] with
    ε h_td_bound hε_norm h_re
  set w := γ.toFun (σ ε) - s
  have hw_ne : w ≠ 0 := by intro h; simp [h] at h_re
  have hw_ne' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw_ne
  have hε_pos : 0 < ε := by rw [← hε_norm]; exact norm_pos_iff.mpr hw_ne
  set u := w / (↑‖w‖ : ℂ)
  have hu_norm : ‖u‖ = 1 := by
    show ‖w / (↑‖w‖ : ℂ)‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hw_ne']
  -- td(u,v₀) scaling: ‖td(u,v₀)‖ = ‖td(w,-L_L)‖ / ‖w‖
  have h_td_scale : ‖tangentDeviation u v₀‖ = ‖tangentDeviation w (-L_L)‖ / ‖w‖ := by
    show ‖tangentDeviation (w / (↑‖w‖ : ℂ)) (-L_L / (↑‖L_L‖ : ℂ))‖ = _
    have h1 : (w / (↑‖w‖ : ℂ) : ℂ) = (‖w‖⁻¹ : ℝ) • w := by
      simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]
    have h_negL : -L_L / (↑‖L_L‖ : ℂ) = (‖L_L‖⁻¹ : ℝ) • (-L_L) := by
      rw [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div, neg_div]
    rw [h1, h_negL, tangentDeviation_real_smul_right _ (inv_ne_zero hL_ne),
      tangentDeviation_real_smul_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_eq_div]
  -- Re(u * conj v₀) > 0
  set R := (u * starRingEnd ℂ v₀).re
  have hR_pos : 0 < R := by
    show 0 < (w / (↑‖w‖ : ℂ) * starRingEnd ℂ (-L_L / (↑‖L_L‖ : ℂ))).re
    rw [map_div₀ (starRingEnd ℂ), map_neg, Complex.conj_ofReal,
      div_mul_div_comm, show w * -(starRingEnd ℂ L_L) = w * starRingEnd ℂ (-L_L) from by
        rw [map_neg], ← Complex.ofReal_mul, Complex.div_ofReal_re]
    exact div_pos h_re (mul_pos (by rw [hε_norm]; exact hε_pos) hL_pos)
  -- Geometric bound: ‖u-v₀‖² ≤ 2*‖td(u,v₀)‖² when Re(u·v̄₀) > 0
  have h_sq : ‖u - v₀‖ ^ 2 ≤ 2 * ‖tangentDeviation u v₀‖ ^ 2 := by
    -- ‖u-v₀‖² = 2 - 2R
    have h_lhs : ‖u - v₀‖ ^ 2 = 2 - 2 * R := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp only [Complex.normSq_eq_norm_sq, hu_norm, hv₀_norm, one_pow]; ring
    -- ‖td(u,v₀)‖² = 1 - R²
    have h_rhs : ‖tangentDeviation u v₀‖ ^ 2 = 1 - R ^ 2 := by
      rw [tangentDeviation_of_norm_one u v₀ hv₀_norm,
        ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
      simp only [Complex.normSq_eq_norm_sq, hu_norm, one_pow,
        norm_smul, Real.norm_eq_abs, hv₀_norm, mul_one, sq_abs]
      -- Simplify starRingEnd ℂ (R • v₀) = ↑R * starRingEnd ℂ v₀
      have hstar : (starRingEnd ℂ) (R • v₀) = (↑R : ℂ) * (starRingEnd ℂ) v₀ := by
        rw [Complex.real_smul, map_mul (starRingEnd ℂ), Complex.conj_ofReal]
      rw [hstar]
      -- Simplify (u * (↑R * starRingEnd ℂ v₀)).re = R²
      have hre : (u * ((↑R : ℂ) * starRingEnd ℂ v₀)).re = R * R := by
        rw [← mul_assoc, mul_comm u (↑R : ℂ), mul_assoc,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [hre]
      ring
    have hR_le : R ≤ 1 := by nlinarith [sq_nonneg (‖tangentDeviation u v₀‖)]
    rw [h_lhs, h_rhs]; nlinarith [hR_pos.le, hR_le]
  -- ‖u-v₀‖ ≤ √2 * ‖td(u,v₀)‖
  have h_bound : ‖u - v₀‖ ≤ Real.sqrt 2 * ‖tangentDeviation u v₀‖ := by
    rw [← Real.sqrt_sq (norm_nonneg (u - v₀)),
      ← Real.sqrt_sq (norm_nonneg (tangentDeviation u v₀)),
      ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt h_sq
  -- Assemble: ‖u-v₀‖ ≤ √2 * ‖td(w,-L_L)‖/ε ≤ c * ε^{m-1}
  -- Note: ‖td(w,-L_L)‖ = ‖td(w,L_L)‖ by h_td_eq
  rw [h_td_scale, hε_norm] at h_bound
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  -- Strip double norm from h_td_bound
  have h_td_bound' : ‖tangentDeviation w (-L_L)‖ ≤ c / Real.sqrt 2 * ε ^ m := by
    rwa [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (pow_nonneg hε_pos.le _)] at h_td_bound
  calc ‖u - v₀‖
      ≤ Real.sqrt 2 * (‖tangentDeviation w (-L_L)‖ / ε) := h_bound
    _ ≤ Real.sqrt 2 * (c / Real.sqrt 2 * ε ^ m / ε) := by gcongr
    _ = c * (ε ^ m / ε) := by field_simp
    _ = c * ε ^ (m - 1) := by
        congr 1
        have hpow : ε ^ m = ε ^ (m - 1) * ε := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
        rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hε_pos)]
    _ = c * ‖ε ^ (m - 1 : ℕ)‖ := by rw [Real.norm_of_nonneg (pow_nonneg hε_pos.le _)]

/-- FTC reduction for zpow cutoff integrals: for a closed curve with a unique crossing
at `t₀`, the cutoff integral of `(γ-s)^{-m} · γ'` reduces to boundary values at the
exit points of the ε-ball.

The proof splits the integral at the exit times σ₁, σ₂, uses that the integrand
vanishes on (σ₁, σ₂), applies FTC on [a, σ₁] and [σ₂, b], and uses γ(a)=γ(b)
to cancel the outer boundary terms. -/
private lemma cutoff_zpow_integral_eq_boundary
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (σ₁ σ₂ ε : ℝ)
    (hσ₁_ge : γ.a ≤ σ₁) (hσ₁_lt : σ₁ < σ₂) (hσ₂_le : σ₂ ≤ γ.b)
    (hε_pos : 0 < ε)
    (hσ₁_val : ‖γ.toFun σ₁ - s‖ = ε) (hσ₂_val : ‖γ.toFun σ₂ - s‖ = ε)
    (h_left : ∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - s‖)
    (h_right : ∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - s‖)
    (h_middle : ∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - s‖ ≤ ε)
    -- Integrability conditions (needed for interval integral)
    (h_int_l : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume γ.a σ₁)
    (h_int_r : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume σ₂ γ.b) :
    ∫ t in γ.a..γ.b,
      (if ‖γ.toFun t - s‖ > ε
       then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
      ((γ.toFun σ₁ - s) ^ (1 - (m : ℤ)) - (γ.toFun σ₂ - s) ^ (1 - (m : ℤ))) /
        ((1 : ℂ) - ↑(m : ℤ)) := by
  -- Key facts
  have hab := γ.toPiecewiseC1Curve.hab
  have hn_ne : (-(m : ℤ) : ℤ) ≠ -1 := by omega
  -- γ(t) ≠ s on [a, σ₁]
  have hne_left : ∀ t ∈ Icc γ.a σ₁, γ.toFun t ≠ s := by
    intro t ht habs
    rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
    · rw [habs, sub_self, norm_zero] at hσ₁_val; linarith
    · have := h_left t ⟨ht.1, ht_lt⟩; rw [habs, sub_self, norm_zero] at this; linarith
  -- γ(t) ≠ s on [σ₂, b]
  have hne_right : ∀ t ∈ Icc σ₂ γ.b, γ.toFun t ≠ s := by
    intro t ht habs
    rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
    · rw [habs, sub_self, norm_zero] at hσ₂_val; linarith
    · have := h_right t ⟨ht_gt, ht.2⟩; rw [habs, sub_self, norm_zero] at this; linarith
  -- Abbreviation for the bare integrand
  set F : ℝ → ℂ := fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t with hF_def
  -- ae-equality: on Ioo a σ₁, condition is true (since Ioo a σ₁ ⊆ Ico a σ₁)
  -- Since restrict_Ioo = restrict_Ioc for NoAtoms measures, ae on Ioo = ae on Ι.
  have hae_left : ∀ᵐ t ∂(volume.restrict (Ι γ.a σ₁)),
      (if ‖γ.toFun t - s‖ > ε then F t else 0) = F t := by
    rw [Set.uIoc_of_le hσ₁_ge, ← restrict_Ioo_eq_restrict_Ioc]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact MeasureTheory.ae_of_all _ fun t ht => by
      have hε_lt : ε < ‖γ.toFun t - s‖ :=
        h_left t ⟨ht.1.le, ht.2⟩
      simp [show ‖γ.toFun t - s‖ > ε from hε_lt]
  -- ae-equality: on Ι σ₂ b, condition is true
  have hae_right : ∀ᵐ t ∂(volume.restrict (Ι σ₂ γ.b)),
      (if ‖γ.toFun t - s‖ > ε then F t else 0) = F t := by
    rw [Set.uIoc_of_le hσ₂_le, ← restrict_Ioo_eq_restrict_Ioc]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact MeasureTheory.ae_of_all _ fun t ht => by
      have hε_lt : ε < ‖γ.toFun t - s‖ :=
        h_right t ⟨ht.1, ht.2.le⟩
      simp [show ‖γ.toFun t - s‖ > ε from hε_lt]
  -- Equality: on [[σ₁, σ₂]], condition is false, so if-then-else = 0
  have heq_mid : EqOn (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      (fun _ => (0 : ℂ)) [[σ₁, σ₂]] := by
    intro t ht
    rw [Set.uIcc_of_le hσ₁_lt.le] at ht
    simp [show ¬(‖γ.toFun t - s‖ > ε) from not_lt.mpr (h_middle t ht)]
  -- Integrability of the if-then-else on subintervals
  -- Use congr_ae: F is integrable on [a,σ₁], and (if...) =ᵃᵉ F there.
  have hae_left_eq : (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) =ᶠ[ae (volume.restrict (Ι γ.a σ₁))] F :=
    hae_left
  have hae_right_eq : (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) =ᶠ[ae (volume.restrict (Ι σ₂ γ.b))] F :=
    hae_right
  have hint_l : IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      volume γ.a σ₁ :=
    h_int_l.congr_ae hae_left_eq.symm
  have hint_m : IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      volume σ₁ σ₂ :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr
      (heq_mid.symm.mono Set.uIoc_subset_uIcc)
  have hint_r : IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      volume σ₂ γ.b :=
    h_int_r.congr_ae hae_right_eq.symm
  -- Step 1: Split ∫_a^b = ∫_a^σ₁ + ∫_σ₁^σ₂ + ∫_σ₂^b
  set G := fun t => if ‖γ.toFun t - s‖ > ε then F t else (0 : ℂ) with hG_def
  have hsplit : ∫ t in γ.a..γ.b, G t =
      (∫ t in γ.a..σ₁, G t) + (∫ t in σ₁..σ₂, G t) + (∫ t in σ₂..γ.b, G t) := by
    have h_σ₁_b := intervalIntegral.integral_add_adjacent_intervals hint_m hint_r
    have h_a_b := intervalIntegral.integral_add_adjacent_intervals hint_l (hint_m.trans hint_r)
    rw [← h_σ₁_b] at h_a_b
    rw [← h_a_b, add_assoc]
  rw [hsplit]
  -- Step 2: Middle integral = 0
  have h_mid_zero : ∫ t in σ₁..σ₂, G t = 0 := by
    have : ∫ t in σ₁..σ₂, G t = ∫ t in σ₁..σ₂, (fun _ => (0 : ℂ)) t :=
      intervalIntegral.integral_congr heq_mid
    rw [this, intervalIntegral.integral_zero]
  rw [h_mid_zero, add_zero]
  -- Step 3: Left integral = ∫_a^σ₁ F, right integral = ∫_σ₂^b F
  have hleft_eq : ∫ t in γ.a..σ₁, G t = ∫ t in γ.a..σ₁, F t :=
    intervalIntegral.integral_congr_ae_restrict hae_left_eq
  have hright_eq : ∫ t in σ₂..γ.b, G t = ∫ t in σ₂..γ.b, F t :=
    intervalIntegral.integral_congr_ae_restrict hae_right_eq
  rw [hleft_eq, hright_eq]
  -- Step 4: Apply FTC on [a, σ₁] and [σ₂, b]
  -- Need: ContinuousOn γ on [a,σ₁] and [σ₂,b], γ ≠ s, piecewise differentiable
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hγ_cont_l : ContinuousOn γ.toFun (Icc γ.a σ₁) :=
    hγ_cont.mono (Icc_subset_Icc le_rfl (hσ₁_lt.le.trans hσ₂_le))
  have hγ_cont_r : ContinuousOn γ.toFun (Icc σ₂ γ.b) :=
    hγ_cont.mono (Icc_subset_Icc (hσ₁_ge.trans hσ₁_lt.le) le_rfl)
  -- Piecewise differentiability from the immersion
  set E := (γ.toPiecewiseC1Curve.partition : Set ℝ) with hE_def
  have hE_count : E.Countable := γ.toPiecewiseC1Curve.partition.countable_toSet
  have hγ_diff : ∀ t ∈ Icc γ.a γ.b, t ∉ E → DifferentiableAt ℝ γ.toFun t :=
    fun t ht hne => γ.toPiecewiseC1Curve.smooth_off_partition t ht hne
  -- FTC on [a, σ₁]
  have hftc_l : ∫ t in γ.a..σ₁, F t =
      ((γ.toFun σ₁ - s) ^ (-(m : ℤ) + 1) - (γ.toFun γ.a - s) ^ (-(m : ℤ) + 1)) /
        (↑(-(m : ℤ) + 1) : ℂ) := by
    exact integral_zpow_comp_sub_mul_deriv hn_ne hσ₁_ge hγ_cont_l hne_left
      E hE_count (Set.inter_subset_right) (fun t ht hne =>
        hγ_diff t ⟨ht.1.le, ht.2.le.trans (hσ₁_lt.le.trans hσ₂_le)⟩ hne) h_int_l
  -- FTC on [σ₂, b]
  have hftc_r : ∫ t in σ₂..γ.b, F t =
      ((γ.toFun γ.b - s) ^ (-(m : ℤ) + 1) - (γ.toFun σ₂ - s) ^ (-(m : ℤ) + 1)) /
        (↑(-(m : ℤ) + 1) : ℂ) := by
    exact integral_zpow_comp_sub_mul_deriv hn_ne hσ₂_le hγ_cont_r hne_right
      E hE_count (Set.inter_subset_right) (fun t ht hne =>
        hγ_diff t ⟨(hσ₁_ge.trans hσ₁_lt.le).trans ht.1.le, ht.2.le⟩ hne) h_int_r
  rw [hftc_l, hftc_r]
  -- Step 5: Use closedness γ(a) = γ(b) to cancel boundary terms
  -- LHS: (A - B)/K + (C - D)/K where A = (γ σ₁-s)^{1-m}, B = (γ a-s)^{1-m},
  --   C = (γ b-s)^{1-m}, D = (γ σ₂-s)^{1-m}, K = ↑(1-↑m)
  -- RHS: (A - D) / (1 - ↑↑m)
  -- Since γ(a) = γ(b), B = C, so (A-B)/K + (C-D)/K = (A-D)/K.
  -- Also ↑(1-↑m) = 1 - ↑↑m by push_cast.
  rw [hγ_closed]
  -- Now LHS = (A-B)/K + (B-D)/K = (A-D)/K since γ(a) = γ(b), so B = C → terms match.
  -- Need to normalize casts: ↑(1 - ↑m : ℤ) vs (1 - ↑↑m : ℂ)
  have hint_eq : (-(m : ℤ) + 1 : ℤ) = 1 - (m : ℤ) := by omega
  simp only [hint_eq]
  have hcast : (↑(1 - (m : ℤ)) : ℂ) = 1 - ↑↑m := by push_cast; ring
  simp only [hcast, Int.cast_natCast]
  ring

/-- Exit times σ₁(ε), σ₂(ε) converge to t₀ from below and above respectively
as ε → 0⁺, using the strict monotonicity of ‖γ - s‖ near t₀. -/
private lemma exit_time_tendsto_right
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (_h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (σ₂ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hσ₂_props : ∀ ε ∈ Ioo 0 δ, t₀ < σ₂ ε ∧ σ₂ ε ≤ γ.b ∧
      ‖γ.toFun (σ₂ ε) - s‖ = ε ∧
      ∀ t ∈ Icc t₀ (σ₂ ε), ‖γ.toFun t - s‖ ≤ ε) :
    Tendsto σ₂ (𝓝[>] 0) (𝓝[>] t₀) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · -- σ₂(ε) → t₀ in 𝓝 t₀: for any η > 0, eventually σ₂(ε) ∈ B(t₀, η)
    rw [Metric.tendsto_nhds]
    intro η hη
    -- Get strict monotonicity near t₀
    obtain ⟨l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, _, hg_mono⟩ :=
      _root_.piecewiseC1Immersion_norm_strictMono_near_crossing γ s t₀ ht₀ hcross
    -- Pick a point between t₀ and min(t₀+η, r) to get an upper bound on ε
    have hη_r : 0 < min η (r - t₀) := lt_min hη (by linarith)
    set t₁ := t₀ + min η (r - t₀) / 2 with ht₁_def
    have ht₁_gt : t₀ < t₁ := by simp only [ht₁_def]; linarith
    have ht₁_lt_r : t₁ < r := by simp only [ht₁_def]; linarith [min_le_right η (r - t₀)]
    have ht₁_mem : t₁ ∈ Icc t₀ r := ⟨ht₁_gt.le, ht₁_lt_r.le⟩
    -- ‖γ(t₁) - s‖ > 0 by strict monotonicity (since t₁ > t₀ and g(t₀) = 0)
    have hg_t₁ : 0 < ‖γ.toFun t₁ - s‖ := by
      have h_lt := hg_mono ⟨le_rfl, hr_gt.le⟩ ht₁_mem ht₁_gt
      have : ‖γ.toFun t₀ - s‖ = 0 := by rw [hcross, sub_self, norm_zero]
      linarith
    set ε₀ := min ‖γ.toFun t₁ - s‖ δ
    have hε₀_pos : 0 < ε₀ := lt_min hg_t₁ hδ
    filter_upwards [Ioo_mem_nhdsGT hε₀_pos] with ε ⟨hε_pos, hε_lt⟩
    have hε_Ioo : ε ∈ Ioo 0 δ := ⟨hε_pos, lt_of_lt_of_le hε_lt (min_le_right _ _)⟩
    obtain ⟨hσ₂_gt, hσ₂_le, hσ₂_norm, hσ₂_mid⟩ := hσ₂_props ε hε_Ioo
    -- dist(σ₂(ε), t₀) = σ₂(ε) - t₀ since σ₂(ε) > t₀
    rw [dist_eq_norm, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ₂_gt)]
    -- We need σ₂(ε) - t₀ < η. It suffices to show σ₂(ε) < t₁ ≤ t₀ + η.
    -- If σ₂(ε) ≤ r, then by monotonicity: ‖γ(σ₂(ε)) - s‖ < ‖γ(t₁) - s‖
    --   would follow from σ₂(ε) < t₁, and we need σ₂(ε) < t₁.
    -- Actually the argument is: if σ₂(ε) ≥ t₁ then ‖γ(σ₂(ε)) - s‖ ≥ ‖γ(t₁) - s‖ > ε,
    -- contradicting ‖γ(σ₂(ε)) - s‖ = ε.
    have hε_lt_t₁ : ε < ‖γ.toFun t₁ - s‖ := lt_of_lt_of_le hε_lt (min_le_left _ _)
    -- Show σ₂(ε) < t₁
    by_contra h_not_lt
    push_neg at h_not_lt -- h_not_lt : η ≤ σ₂ ε - t₀, i.e., σ₂(ε) ≥ t₀ + η
    -- t₁ ≤ t₀ + η ≤ σ₂(ε), so t₁ ∈ [t₀, σ₂(ε)]
    have ht₁_le_σ₂ : t₁ ≤ σ₂ ε := by
      simp only [ht₁_def]; linarith [min_le_left η (r - t₀)]
    -- Therefore ‖γ(t₁) - s‖ ≤ ε by the middle bound
    have := hσ₂_mid t₁ ⟨ht₁_gt.le, ht₁_le_σ₂⟩
    linarith
  · -- σ₂(ε) ∈ Ioi t₀ eventually
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (hσ₂_props ε hε).1

/-- Left-side analogue: exit time σ₁(ε) → t₀ from below. -/
private lemma exit_time_tendsto_left
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (_h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (σ₁ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hσ₁_props : ∀ ε ∈ Ioo 0 δ, σ₁ ε < t₀ ∧ γ.a ≤ σ₁ ε ∧
      ‖γ.toFun (σ₁ ε) - s‖ = ε ∧
      ∀ t ∈ Icc (σ₁ ε) t₀, ‖γ.toFun t - s‖ ≤ ε) :
    Tendsto σ₁ (𝓝[>] 0) (𝓝[<] t₀) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, hg_anti, _⟩ :=
      _root_.piecewiseC1Immersion_norm_strictMono_near_crossing γ s t₀ ht₀ hcross
    have hη_l : 0 < min η (t₀ - l) := lt_min hη (by linarith)
    set t₁ := t₀ - min η (t₀ - l) / 2 with ht₁_def
    have ht₁_lt : t₁ < t₀ := by simp only [ht₁_def]; linarith
    have ht₁_gt_l : l < t₁ := by simp only [ht₁_def]; linarith [min_le_right η (t₀ - l)]
    have ht₁_mem : t₁ ∈ Icc l t₀ := ⟨ht₁_gt_l.le, ht₁_lt.le⟩
    have hg_t₁ : 0 < ‖γ.toFun t₁ - s‖ := by
      have h1 := hg_anti ht₁_mem ⟨hl_lt.le, le_rfl⟩ ht₁_lt
      simp only [hcross, sub_self, norm_zero] at h1; exact h1
    set ε₀ := min ‖γ.toFun t₁ - s‖ δ
    have hε₀_pos : 0 < ε₀ := lt_min hg_t₁ hδ
    filter_upwards [Ioo_mem_nhdsGT hε₀_pos] with ε ⟨hε_pos, hε_lt⟩
    have hε_Ioo : ε ∈ Ioo 0 δ := ⟨hε_pos, lt_of_lt_of_le hε_lt (min_le_right _ _)⟩
    obtain ⟨hσ₁_lt, hσ₁_ge, hσ₁_norm, hσ₁_mid⟩ := hσ₁_props ε hε_Ioo
    rw [dist_comm, dist_eq_norm, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ₁_lt)]
    have hε_lt_t₁ : ε < ‖γ.toFun t₁ - s‖ := lt_of_lt_of_le hε_lt (min_le_left _ _)
    -- Show t₀ - σ₁(ε) < η. If σ₁(ε) ≤ t₁ then t₁ ∈ [σ₁(ε), t₀] and ‖γ(t₁)-s‖ ≤ ε, contradiction.
    by_contra h_not_lt
    push_neg at h_not_lt -- t₀ - σ₁(ε) ≥ η
    have hσ₁_le_t₁ : σ₁ ε ≤ t₁ := by
      simp only [ht₁_def]; linarith [min_le_left η (t₀ - l)]
    have := hσ₁_mid t₁ ⟨hσ₁_le_t₁, ht₁_lt.le⟩
    linarith
  · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (hσ₁_props ε hε).1

/-- The integrand `(γ(t) - s)^{-m} · γ'(t)` is interval integrable on any
sub-interval `[c, d] ⊆ [a, b]` where `γ(t) ≠ s`.

The zpow part is continuous on `[[c, d]]` (since `γ(t) ≠ s`), and the derivative is
integrable on `[c, d]` (bounded and measurable from the piecewise C1 structure). Their
product is integrable by `IntervalIntegrable.continuousOn_mul`. -/
private lemma zpow_mul_deriv_intervalIntegrable
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (c d : ℝ) (hcd : c ≤ d)
    (hc_ge : γ.a ≤ c) (hd_le : d ≤ γ.b)
    (hne : ∀ t ∈ Icc c d, γ.toFun t ≠ s) :
    IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume c d := by
  -- The zpow part is continuous on [[c, d]]
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hcont_zpow : ContinuousOn (fun t => (γ.toFun t - s) ^ (-(m : ℤ)))
      (Set.uIcc c d) := by
    rw [Set.uIcc_of_le hcd]
    exact continuousOn_zpow_comp_sub
      (hγ_cont.mono (Icc_subset_Icc hc_ge hd_le)) hne
  -- The derivative is integrable on [c, d] (restriction of integrability on [a, b])
  have hderiv_int : IntervalIntegrable (deriv γ.toFun) MeasureTheory.volume c d :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
      (piecewiseC1Immersion_deriv_bounded γ)).mono_set
      ((Set.uIcc_of_le hcd ▸ Set.uIcc_of_le (le_of_lt γ.hab) ▸
        Icc_subset_Icc hc_ge hd_le) : [[c, d]] ⊆ [[γ.a, γ.b]])
  -- Product of integrable and continuous is integrable
  exact hderiv_int.continuousOn_mul hcont_zpow

/-- Infrastructure for the FTC-based proof of L4. Given a piecewise C¹ immersion
crossing `s` at `t₀` with flatness of order `m`, this provides:
- Exit time functions `wR, wL` with `‖w(ε)‖ = ε` on the ε-sphere
- Direction limits `uR, uL` on the unit circle related to `angleAtCrossing`
- Direction convergence rates `o(ε^{m-1})` from flatness
- FTC reduction: the cutoff integral equals `(wL^{1-m} - wR^{1-m}) / (1-m)` -/
lemma cutoff_zpow_infrastructure
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m) :
    ∃ (wR wL : ℝ → ℂ) (uR uL : ℂ),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wR ε‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wL ε‖ = ε) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), wR ε ≠ 0) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), wL ε ≠ 0) ∧
      (‖uR‖ = 1) ∧ (‖uL‖ = 1) ∧
      (∃ n_angle : ℤ, arg uR - arg uL =
        _root_.angleAtCrossing γ t₀ ht₀ + ↑n_angle * (2 * Real.pi)) ∧
      ((fun ε => ‖wR ε / (↑‖wR ε‖ : ℂ) - uR‖) =o[𝓝[>] (0 : ℝ)]
        fun ε => ε ^ (m - 1 : ℕ)) ∧
      ((fun ε => ‖wL ε / (↑‖wL ε‖ : ℂ) - uL‖) =o[𝓝[>] (0 : ℝ)]
        fun ε => ε ^ (m - 1 : ℕ)) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ∫ t in γ.a..γ.b,
          (if ‖γ.toFun t - s‖ > ε
           then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
          (wL ε ^ (1 - (m : ℤ)) - wR ε ^ (1 - (m : ℤ))) /
            ((1 : ℂ) - ↑(m : ℤ))) := by
  -- ========================================================================
  -- Step 1: Extract one-sided derivative limits (nonzero) at t₀
  -- ========================================================================
  obtain ⟨L_R, hL_R_ne, htend_R⟩ :
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L) := by
    by_cases h : t₀ ∈ γ.toPiecewiseC1Curve.partition
    · exact γ.right_deriv_limit t₀ h ht₀.2
    · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
        (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
          nhdsWithin_le_nhds⟩
  obtain ⟨L_L, hL_L_ne, htend_L⟩ :
      ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L) := by
    by_cases h : t₀ ∈ γ.toPiecewiseC1Curve.partition
    · exact γ.left_deriv_limit t₀ h ht₀.1
    · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
        (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
          nhdsWithin_le_nhds⟩
  -- ========================================================================
  -- Step 2: Get exit times from _root_.exists_cutoff_boundary_times
  -- ========================================================================
  obtain ⟨δ, hδ_pos, h_exit⟩ :=
    _root_.exists_cutoff_boundary_times γ s t₀ ht₀ hcross h_unique
  -- Define σ₁(ε), σ₂(ε) via Classical.choose
  let σ₁ : ℝ → ℝ := fun ε =>
    if h : ε ∈ Ioo 0 δ then (h_exit ε h).choose else t₀
  let σ₂ : ℝ → ℝ := fun ε =>
    if h : ε ∈ Ioo 0 δ then (h_exit ε h).choose_spec.choose else t₀
  -- Extract all properties for ε ∈ (0,δ)
  have hprops : ∀ ε (hε : ε ∈ Ioo 0 δ),
      γ.a ≤ σ₁ ε ∧ σ₁ ε < t₀ ∧ t₀ < σ₂ ε ∧ σ₂ ε ≤ γ.b ∧
      ‖γ.toFun (σ₁ ε) - s‖ = ε ∧ ‖γ.toFun (σ₂ ε) - s‖ = ε ∧
      (∀ t ∈ Ico γ.a (σ₁ ε), ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Ioc (σ₂ ε) γ.b, ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Icc (σ₁ ε) (σ₂ ε), ‖γ.toFun t - s‖ ≤ ε) := by
    intro ε hε
    simp only [σ₁, σ₂, hε, dif_pos]
    exact (h_exit ε hε).choose_spec.choose_spec
  have hIoo_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 δ := Ioo_mem_nhdsGT hδ_pos
  -- ========================================================================
  -- Step 3: Define wR, wL, uR, uL
  -- ========================================================================
  let wR : ℝ → ℂ := fun ε => γ.toFun (σ₂ ε) - s
  let wL : ℝ → ℂ := fun ε => γ.toFun (σ₁ ε) - s
  let uR : ℂ := L_R / ↑‖L_R‖
  let uL : ℂ := -L_L / ↑‖L_L‖
  refine ⟨wR, wL, uR, uL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ========================================================================
  -- Property 1: ‖wR ε‖ = ε eventually
  -- ========================================================================
  · exact hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.2.1
  -- ========================================================================
  -- Property 2: ‖wL ε‖ = ε eventually
  -- ========================================================================
  · exact hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.1
  -- ========================================================================
  -- Property 3: wR ε ≠ 0 eventually
  -- ========================================================================
  · filter_upwards [hIoo_ev] with ε hε
    show γ.toFun (σ₂ ε) - s ≠ 0
    have h_norm := (hprops ε hε).2.2.2.2.2.1
    exact sub_ne_zero.mpr (fun h => by rw [h, sub_self, norm_zero] at h_norm; linarith [hε.1])
  -- ========================================================================
  -- Property 4: wL ε ≠ 0 eventually
  -- ========================================================================
  · filter_upwards [hIoo_ev] with ε hε
    show γ.toFun (σ₁ ε) - s ≠ 0
    have h_norm := (hprops ε hε).2.2.2.2.1
    exact sub_ne_zero.mpr (fun h => by rw [h, sub_self, norm_zero] at h_norm; linarith [hε.1])
  -- ========================================================================
  -- Property 5: ‖uR‖ = 1
  -- ========================================================================
  · show ‖L_R / ↑‖L_R‖‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hL_R_ne),
      div_self (norm_ne_zero_iff.mpr hL_R_ne)]
  -- ========================================================================
  -- Property 6: ‖uL‖ = 1
  -- ========================================================================
  · show ‖-L_L / ↑‖L_L‖‖ = 1
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.mpr hL_L_ne), div_self (norm_ne_zero_iff.mpr hL_L_ne)]
  -- ========================================================================
  -- Property 7: angle relation arg uR - arg uL = angleAtCrossing + n*2π
  -- ========================================================================
  · -- Angle relation: arg(L_R/‖L_R‖) - arg(-L_L/‖L_L‖) = angleAtCrossing + n*2π
    -- Key identity: arg(z / ‖z‖) = arg(z) for z ≠ 0 (dividing by positive real)
    have h_arg_uR : uR.arg = L_R.arg := by
      show (L_R / ↑‖L_R‖).arg = L_R.arg
      rw [div_eq_inv_mul, ← Complex.ofReal_inv,
        Complex.arg_real_mul L_R (inv_pos.mpr (norm_pos_iff.mpr hL_R_ne))]
    have h_arg_uL : uL.arg = (-L_L).arg := by
      show (-L_L / ↑‖L_L‖).arg = (-L_L).arg
      rw [div_eq_inv_mul, ← Complex.ofReal_inv,
        Complex.arg_real_mul (-L_L) (inv_pos.mpr (norm_pos_iff.mpr hL_L_ne))]
    rw [h_arg_uR, h_arg_uL]
    by_cases hp : t₀ ∈ γ.toPiecewiseC1Curve.partition
    · -- Partition case: angleAtCrossing = arg L_right - arg (-L_left)
      refine ⟨0, ?_⟩
      simp only [Int.cast_zero, zero_mul, add_zero]
      unfold angleAtCrossing
      rw [dif_pos hp]
      have hL_R_eq := tendsto_nhds_unique htend_R
        (Classical.choose_spec (γ.right_deriv_limit t₀ hp ht₀.2)).2
      have hL_L_eq := tendsto_nhds_unique htend_L
        (Classical.choose_spec (γ.left_deriv_limit t₀ hp ht₀.1)).2
      rw [hL_R_eq, hL_L_eq]
    · -- Smooth case: angleAtCrossing = π, and L_R = L_L
      rw [angleAtCrossing_smooth γ t₀ ht₀ hp]
      have hL_eq : L_R = L_L := by
        have hcont := γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ hp
        exact (tendsto_nhds_unique htend_R
          (hcont.tendsto.mono_left nhdsWithin_le_nhds)).trans
          (tendsto_nhds_unique htend_L
            (hcont.tendsto.mono_left nhdsWithin_le_nhds)).symm
      rw [hL_eq]
      -- arg(z) - arg(-z) = ±π, both ≡ π mod 2π
      by_cases him : 0 < L_L.im
      · exact ⟨0, by rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos him]; push_cast; ring⟩
      · by_cases him' : L_L.im < 0
        · exact ⟨-1, by rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg him']; push_cast; ring⟩
        · have him_eq : L_L.im = 0 := le_antisymm (not_lt.mp him) (not_lt.mp him')
          have hre_ne : L_L.re ≠ 0 := fun h => hL_L_ne (Complex.ext h him_eq)
          rcases lt_or_gt_of_ne hre_ne with hre | hre
          · exact ⟨0, by rw [Complex.arg_neg_eq_arg_sub_pi_iff.mpr (Or.inr ⟨him_eq, hre⟩)]
                         push_cast; ring⟩
          · exact ⟨-1, by rw [Complex.arg_neg_eq_arg_add_pi_iff.mpr (Or.inr ⟨him_eq, hre⟩)]
                          push_cast; ring⟩
  -- ========================================================================
  -- Property 8: direction convergence rate for wR (right exit)
  -- ========================================================================
  · -- Need: ‖wR(ε)/‖wR(ε)‖ - uR‖ = o(ε^{m-1})
    -- Strategy: use direction_rate_from_flatness_right with σ₂ as the exit time
    -- First show σ₂(ε) → t₀⁺
    have hσ₂_tendsto : Tendsto σ₂ (𝓝[>] 0) (𝓝[>] t₀) :=
      exit_time_tendsto_right γ s t₀ ht₀ hcross h_unique σ₂ δ hδ_pos
        (fun ε hε => ⟨(hprops ε hε).2.2.1, (hprops ε hε).2.2.2.1,
          (hprops ε hε).2.2.2.2.2.1,
          fun t ht => (hprops ε hε).2.2.2.2.2.2.2.2
            t ⟨le_trans (le_of_lt (hprops ε hε).2.1) ht.1, ht.2⟩⟩)
    exact direction_rate_from_flatness_right γ s m hm t₀ ht₀ hcross h_flat
      L_R hL_R_ne htend_R σ₂
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.2.1)
      hσ₂_tendsto
  -- ========================================================================
  -- Property 9: direction convergence rate for wL (left exit)
  -- ========================================================================
  · -- Need: ‖wL(ε)/‖wL(ε)‖ - uL‖ = o(ε^{m-1})
    have hσ₁_tendsto : Tendsto σ₁ (𝓝[>] 0) (𝓝[<] t₀) :=
      exit_time_tendsto_left γ s t₀ ht₀ hcross h_unique σ₁ δ hδ_pos
        (fun ε hε => ⟨(hprops ε hε).2.1, (hprops ε hε).1,
          (hprops ε hε).2.2.2.2.1,
          fun t ht => (hprops ε hε).2.2.2.2.2.2.2.2
            t ⟨ht.1, le_trans ht.2 (le_of_lt (hprops ε hε).2.2.1)⟩⟩)
    exact direction_rate_from_flatness_left γ s m hm t₀ ht₀ hcross h_flat
      L_L hL_L_ne htend_L σ₁
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.1)
      hσ₁_tendsto
  -- ========================================================================
  -- Property 10: FTC reduction
  -- ========================================================================
  · -- Eventually: ∫ = (wL^{1-m} - wR^{1-m}) / (1-m)
    filter_upwards [hIoo_ev] with ε hε
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hprops ε hε
    -- Apply cutoff_zpow_integral_eq_boundary
    show ∫ t in γ.a..γ.b,
      (if ‖γ.toFun t - s‖ > ε
       then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
      ((γ.toFun (σ₁ ε) - s) ^ (1 - (m : ℤ)) - (γ.toFun (σ₂ ε) - s) ^ (1 - (m : ℤ))) /
        ((1 : ℂ) - ↑(m : ℤ))
    -- Integrability on [a, σ₁]: γ(t) ≠ s on Icc γ.a (σ₁ ε)
    have hne_left : ∀ t ∈ Icc γ.a (σ₁ ε), γ.toFun t ≠ s := by
      intro t ht habs
      rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
      · rw [habs, sub_self, norm_zero] at h5; linarith [hε.1]
      · have := h7 t ⟨ht.1, ht_lt⟩; rw [habs, sub_self, norm_zero] at this; linarith [hε.1]
    -- Integrability on [σ₂, b]: γ(t) ≠ s on Icc (σ₂ ε) γ.b
    have hne_right : ∀ t ∈ Icc (σ₂ ε) γ.b, γ.toFun t ≠ s := by
      intro t ht habs
      rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
      · rw [habs, sub_self, norm_zero] at h6; linarith [hε.1]
      · have := h8 t ⟨ht_gt, ht.2⟩; rw [habs, sub_self, norm_zero] at this; linarith [hε.1]
    exact cutoff_zpow_integral_eq_boundary γ s m hm hγ_closed
      (σ₁ ε) (σ₂ ε) ε h1 (lt_trans h2 h3) h4 hε.1 h5 h6 h7 h8 h9
      (zpow_mul_deriv_intervalIntegrable γ s m γ.a (σ₁ ε) h1 le_rfl
        ((lt_trans h2 h3).le.trans h4) hne_left)
      (zpow_mul_deriv_intervalIntegrable γ s m (σ₂ ε) γ.b h4
        (h1.trans (lt_trans h2 h3).le) le_rfl hne_right)


end GeneralizedResidueTheory
