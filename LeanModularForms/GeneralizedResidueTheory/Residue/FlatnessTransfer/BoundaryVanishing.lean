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
    (E : Set ℝ) (hE : E.Countable) (_hE_sub : E ∩ Ioo a b ⊆ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ E → DifferentiableAt ℝ γ t)
    (h_int : IntervalIntegrable
      (fun t => (γ t - s) ^ n * (deriv γ t : ℂ)) MeasureTheory.volume a b) :
    ∫ t in a..b, (γ t - s) ^ n * (deriv γ t : ℂ) =
      ((γ b - s) ^ (n + 1) - (γ a - s) ^ (n + 1)) / (↑(n + 1) : ℂ) := by
  have hn1 : (n : ℤ) + 1 ≠ 0 := by omega
  have hn1_cast : (↑(n + 1) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn1
  set F : ℝ → ℂ := fun t => (γ t - s) ^ (n + 1) / (↑(n + 1) : ℂ) with hF_def
  set f : ℝ → ℂ := fun t => (γ t - s) ^ n * (deriv γ t : ℂ) with hf_def
  have hF_cont : ContinuousOn F (Icc a b) :=
    (continuousOn_zpow_comp_sub hγ_cont hγ_ne (n := n + 1)).div_const _
  have hE_count : (E ∩ Ioo a b).Countable := hE.mono Set.inter_subset_left
  have hF_deriv : ∀ t ∈ Ioo a b \ (E ∩ Ioo a b),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not_E : t ∉ E := fun hE_mem => ht_not ⟨hE_mem, ht⟩
    have hγ_da := (hγ_diff t ht ht_not_E).hasDerivAt
    have hne : γ t ≠ s := hγ_ne t (Ioo_subset_Icc_self ht)
    have h_zpow := hasDerivAt_zpow_comp_sub (n := n + 1) hγ_da hne
    have h_div := h_zpow.div_const (↑(n + 1) : ℂ)
    change HasDerivAt F ((γ t - s) ^ n * ↑(deriv γ t)) t
    have : (↑(n + 1) : ℂ) * (γ t - s) ^ (n + 1 - 1) * ↑(deriv γ t) / (↑(n + 1) : ℂ)
        = (γ t - s) ^ n * ↑(deriv γ t) := by
      rw [show (n + 1 : ℤ) - 1 = n from by ring]
      rw [mul_assoc, mul_div_cancel_left₀ _ hn1_cast]
    rw [← this]
    exact h_div
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f hab hE_count hF_cont hF_deriv h_int
  rw [h_ftc]
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

private lemma slope_tendsto_right_of_deriv
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L : ℂ) (hL_lim : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (γ.toFun (t₀ + ε) - s)) (𝓝[>] 0) (𝓝 L) := by
  have ht₀_Icc : t₀ ∈ Icc γ.a γ.b := Ioo_subset_Icc_self ht₀
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
  have h_deriv : HasDerivWithinAt γ.toFun L (Ici t₀) t₀ :=
    hasDerivWithinAt_Ici_of_tendsto_deriv h_diff h_cont (Ioo_mem_nhdsGT hδ_gt) hL_lim
  rw [hasDerivWithinAt_iff_tendsto_slope] at h_deriv
  rw [show (Ici t₀ \ {t₀} : Set ℝ) = Ioi t₀ from Ici_diff_left] at h_deriv
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

private lemma direction_of_slope_tendsto
    (f : ℝ → ℂ) (L : ℂ) (hL : L ≠ 0)
    (h_slope : Tendsto (fun ε : ℝ => ε⁻¹ • (f ε)) (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε => f ε / ↑‖f ε‖) (𝓝[>] 0) (𝓝 (L / ↑‖L‖)) := by
  suffices h_eq : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f ε / ↑‖f ε‖ = (ε⁻¹ • f ε) / ↑‖ε⁻¹ • f ε‖ by
    have h_norm_cont : Tendsto (fun w : ℂ => w / ↑‖w‖) (𝓝 L)
        (𝓝 (L / ↑‖L‖)) := by
      apply Tendsto.div tendsto_id
        (Complex.continuous_ofReal.continuousAt.tendsto.comp
          continuous_norm.continuousAt.tendsto)
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hL)
    exact (h_norm_cont.comp h_slope).congr' (h_eq.mono fun ε h => h.symm)
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with ε (hε : (0 : ℝ) < ε)
  set w := f ε
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
      (𝓝[>] 0) (𝓝 (L_right / ‖L_right‖)) :=
  direction_of_slope_tendsto _ L_right hL
    (slope_tendsto_right_of_deriv γ s t₀ ht₀ hcross L_right hL_lim)

private lemma slope_tendsto_left_of_deriv
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L : ℂ) (hL_lim : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (γ.toFun (t₀ - ε) - s)) (𝓝[>] 0) (𝓝 (-L)) := by
  have ht₀_Icc : t₀ ∈ Icc γ.a γ.b := Ioo_subset_Icc_self ht₀
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
  have h_deriv : HasDerivWithinAt γ.toFun L (Iic t₀) t₀ :=
    hasDerivWithinAt_Iic_of_tendsto_deriv h_diff h_cont (Ioo_mem_nhdsLT hδ_lt) hL_lim
  rw [hasDerivWithinAt_iff_tendsto_slope] at h_deriv
  rw [show (Iic t₀ \ {t₀} : Set ℝ) = Iio t₀ from Iic_diff_right] at h_deriv
  have h_map : Tendsto (fun ε : ℝ => t₀ - ε) (𝓝[>] (0 : ℝ)) (𝓝[<] t₀) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun ε : ℝ => t₀ - ε) (𝓝 (0 : ℝ)) (𝓝 t₀) := by
        have := (continuous_sub_left t₀).tendsto (0 : ℝ)
        simpa using this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
      exact sub_lt_self t₀ hε
  have h_comp := h_deriv.comp h_map
  have h_neg : Tendsto (fun ε : ℝ => -((-ε)⁻¹ • (γ.toFun (t₀ - ε) - s)))
      (𝓝[>] 0) (𝓝 (-L)) := h_comp.neg.congr (fun ε => by
    simp only [Function.comp, slope, vsub_eq_sub]
    rw [hcross]; ring_nf)
  convert h_neg using 1
  ext ε
  rw [inv_neg, neg_smul, neg_neg]

/-- Left-side analogue of `crossing_direction_right_tendsto`:
`(γ(t₋(ε)) - s) / ‖γ(t₋(ε)) - s‖ → -L_left / ‖L_left‖`. -/
theorem crossing_direction_left_tendsto
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_left : ℂ) (hL : L_left ≠ 0)
    (hL_lim : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_left)) :
    Tendsto (fun ε => (γ.toFun (t₀ - ε) - s) / ‖γ.toFun (t₀ - ε) - s‖)
      (𝓝[>] 0) (𝓝 (-L_left / ‖L_left‖)) := by
  have h_slope := slope_tendsto_left_of_deriv γ s t₀ ht₀ hcross L_left hL_lim
  have h_norm_neg : ‖-L_left‖ = ‖L_left‖ := norm_neg L_left
  have hL_neg : -L_left ≠ 0 := neg_ne_zero.mpr hL
  have h_dir := direction_of_slope_tendsto _ (-L_left) hL_neg h_slope
  have h_eq : -L_left / ↑‖-L_left‖ = -L_left / ↑‖L_left‖ := by rw [h_norm_neg]
  rwa [h_eq] at h_dir

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
  `k + n - 1 = m - k_L - 1 ≥ 0`. -/

private lemma zpow_sub_isBigO (k : ℤ) (u : ℂ) (hu : u ≠ 0) :
    (fun v => v ^ k - u ^ k) =O[𝓝 u] (fun v => v - u) :=
  (hasDerivAt_zpow k u (Or.inl hu)).differentiableAt.isBigO_sub

open Asymptotics in
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
provided `n + k ≥ 1`. -/
theorem zpow_boundary_diff_tendsto_zero
    (k : ℤ) (hk : k ≤ -1)
    (wR wL : ℝ → ℂ)
    (h_norm_R : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wR ε‖ = ε)
    (h_norm_L : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖wL ε‖ = ε)
    (h_neR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), wR ε ≠ 0)
    (h_neL : ∀ᶠ ε in 𝓝[>] (0 : ℝ), wL ε ≠ 0)
    (uR uL : ℂ) (huR : ‖uR‖ = 1) (huL : ‖uL‖ = 1)
    (h_angle : uR ^ k = uL ^ k)
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
  have h_oR := direction_zpow_diff_isLittleO k uR huR_ne wR n hn2 h_rate_R
  have h_oL := direction_zpow_diff_isLittleO k uL huL_ne wL n hn2 h_rate_L
  have h_diff : (fun ε =>
      (wR ε / (↑‖wR ε‖ : ℂ)) ^ k - (wL ε / (↑‖wL ε‖ : ℂ)) ^ k)
      =o[𝓝[>] 0] (fun ε => (ε : ℝ) ^ (n - 1 : ℕ)) := by
    have h_eq : (fun ε => (wR ε / ↑‖wR ε‖) ^ k - (wL ε / ↑‖wL ε‖) ^ k) =
        fun ε => ((wR ε / ↑‖wR ε‖) ^ k - uR ^ k) -
          ((wL ε / ↑‖wL ε‖) ^ k - uL ^ k) := by
      ext ε; rw [h_angle]; ring
    rw [h_eq]; exact h_oR.sub h_oL
  rw [Metric.tendsto_nhds]
  intro η hη
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖(wR ε / (↑‖wR ε‖ : ℂ)) ^ k - (wL ε / (↑‖wL ε‖ : ℂ)) ^ k‖ ≤
      η / 2 * ‖(ε : ℝ) ^ (n - 1 : ℕ)‖ := (h_diff.def' (half_pos hη)).bound
  filter_upwards [h_bound, h_norm_R, h_norm_L, h_neR, h_neL,
    Ioo_mem_nhdsGT one_pos] with ε h_bnd h_nR h_nL h_ne_R h_ne_L hε_mem
  obtain ⟨hε_pos, hε_lt⟩ := hε_mem
  rw [dist_eq_norm, sub_zero]
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
  have h_norm_pow : ‖(ε : ℝ) ^ (n - 1 : ℕ)‖ = ε ^ (n - 1 : ℕ) :=
    (Real.norm_eq_abs _).trans (abs_of_pos (pow_pos hε_pos _))
  rw [h_norm_pow] at h_bnd
  have h_pow_le : (ε : ℝ) ^ k * (ε : ℝ) ^ (n - 1 : ℕ) ≤ 1 := by
    rw [← zpow_natCast ε (n - 1), ← zpow_add₀ (ne_of_gt hε_pos)]
    exact zpow_le_one₀ hε_pos hε_lt.le (by omega)
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

private lemma orthogonalProjectionComplex_of_norm_one (u v : ℂ) (hv : ‖v‖ = 1) :
    orthogonalProjectionComplex u v = (u * starRingEnd ℂ v).re • v := by
  unfold orthogonalProjectionComplex
  rw [Complex.normSq_eq_norm_sq, hv, one_pow, div_one]

private lemma tangentDeviation_of_norm_one (u v : ℂ) (hv : ‖v‖ = 1) :
    tangentDeviation u v = u - (u * starRingEnd ℂ v).re • v := by
  rw [tangentDeviation, orthogonalProjectionComplex_of_norm_one u v hv]

/-- For unit vectors `u, v` with `‖u - v‖ ≤ 1`:
`‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖`. -/
theorem norm_sub_le_tangentDeviation_of_unit (u v : ℂ)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (h_close : ‖u - v‖ ≤ 1) :
    ‖u - v‖ ≤ 2 * ‖tangentDeviation u v‖ := by
  have h_decomp : u - v = tangentDeviation u v + ((u * starRingEnd ℂ v).re - 1) • v := by
    rw [tangentDeviation_of_norm_one u v hv]
    simp only [Complex.real_smul]; push_cast; ring
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
  have h_tri := norm_add_le (tangentDeviation u v) (((u * starRingEnd ℂ v).re - 1) • v)
  rw [← h_decomp] at h_tri
  have h_smul_norm : ‖((u * starRingEnd ℂ v).re - 1) • v‖ = ‖u - v‖ ^ 2 / 2 := by
    rw [norm_smul, Real.norm_eq_abs, hv, mul_one, abs_of_nonpos (by linarith), neg_sub,
      h_re_bound]
  have h_sq_le : ‖u - v‖ ^ 2 / 2 ≤ ‖u - v‖ / 2 := by
    rw [div_le_div_iff_of_pos_right two_pos]
    calc ‖u - v‖ ^ 2 = ‖u - v‖ * ‖u - v‖ := sq _
      _ ≤ ‖u - v‖ * 1 := by exact mul_le_mul_of_nonneg_left h_close (norm_nonneg _)
      _ = ‖u - v‖ := mul_one _
  linarith [h_smul_norm, h_sq_le, h_tri]

/-- For unit vectors `z₁, z₂` and integer exponent `k`, if
`k · (arg z₁ - arg z₂) ∈ 2πℤ`, then `z₁^k = z₂^k`. -/
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
  have h_eq : ↑k * (↑(arg z₁) * I) -
      (↑k * (↑(arg z₂) * I) + ↑n * (2 * ↑Real.pi * I)) =
      ↑((↑k : ℝ) * (arg z₁ - arg z₂) -
        (↑n : ℝ) * (2 * Real.pi)) * I := by
    push_cast; ring
  rw [h_eq, mul_eq_zero]
  left
  rw [ofReal_eq_zero]
  linarith

private lemma orthogonalProjectionComplex_real_smul_left (c : ℝ) (w L : ℂ) :
    orthogonalProjectionComplex (c • w) L = c • orthogonalProjectionComplex w L := by
  simp only [orthogonalProjectionComplex, Complex.real_smul]
  rw [show ↑c * w * (starRingEnd ℂ) L = ↑c * (w * (starRingEnd ℂ) L) from mul_assoc _ _ _,
    Complex.re_ofReal_mul]
  push_cast; ring

private lemma tangentDeviation_real_smul_left (c : ℝ) (w L : ℂ) :
    tangentDeviation (c • w) L = c • tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex_real_smul_left, smul_sub]

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

private lemma tangentDeviation_real_smul_right (c : ℝ) (hc : c ≠ 0) (w L : ℂ) :
    tangentDeviation w (c • L) = tangentDeviation w L := by
  simp only [tangentDeviation, orthogonalProjectionComplex_real_smul_right c hc]

private lemma unit_sq_le_two_mul_tangentDeviation_sq
    (u v₀ : ℂ) (hu : ‖u‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hR_pos : 0 < (u * starRingEnd ℂ v₀).re) :
    ‖u - v₀‖ ^ 2 ≤ 2 * ‖tangentDeviation u v₀‖ ^ 2 := by
  set R := (u * starRingEnd ℂ v₀).re
  have h_lhs : ‖u - v₀‖ ^ 2 = 2 - 2 * R := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, hu, hv₀, one_pow]; ring
  have h_rhs : ‖tangentDeviation u v₀‖ ^ 2 = 1 - R ^ 2 := by
    rw [tangentDeviation_of_norm_one u v₀ hv₀,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp only [Complex.normSq_eq_norm_sq, hu, one_pow,
      norm_smul, Real.norm_eq_abs, hv₀, mul_one, sq_abs]
    have hstar : (starRingEnd ℂ) (R • v₀) = (↑R : ℂ) * (starRingEnd ℂ) v₀ := by
      rw [Complex.real_smul, map_mul (starRingEnd ℂ), Complex.conj_ofReal]
    rw [hstar]
    have hre : (u * ((↑R : ℂ) * starRingEnd ℂ v₀)).re = R * R := by
      rw [← mul_assoc, mul_comm u (↑R : ℂ), mul_assoc,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [hre]; ring
  have hR_le : R ≤ 1 := by nlinarith [sq_nonneg (‖tangentDeviation u v₀‖)]
  rw [h_lhs, h_rhs]; nlinarith [hR_pos.le, hR_le]

private lemma norm_sub_le_sqrt2_tangentDeviation
    (u v₀ : ℂ) (hu : ‖u‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hR_pos : 0 < (u * starRingEnd ℂ v₀).re) :
    ‖u - v₀‖ ≤ Real.sqrt 2 * ‖tangentDeviation u v₀‖ := by
  have h_sq := unit_sq_le_two_mul_tangentDeviation_sq u v₀ hu hv₀ hR_pos
  rw [← Real.sqrt_sq (norm_nonneg (u - v₀)),
    ← Real.sqrt_sq (norm_nonneg (tangentDeviation u v₀)),
    ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  exact Real.sqrt_le_sqrt h_sq

private lemma direction_rate_final_calc
    (m : ℕ) (c ε : ℝ) (hε_pos : 0 < ε) (hm : 2 ≤ m)
    (w : ℂ) (L : ℂ) (u v₀ : ℂ)
    (hu : ‖u‖ = 1) (hv₀ : ‖v₀‖ = 1)
    (hR_pos : 0 < (u * starRingEnd ℂ v₀).re)
    (h_td_scale : ‖tangentDeviation u v₀‖ = ‖tangentDeviation w L‖ / ‖w‖)
    (hε_norm : ‖w‖ = ε)
    (h_td_bound' : ‖tangentDeviation w L‖ ≤ c / Real.sqrt 2 * ε ^ m) :
    ‖u - v₀‖ ≤ c * ‖ε ^ (m - 1 : ℕ)‖ := by
  have h_bound := norm_sub_le_sqrt2_tangentDeviation u v₀ hu hv₀ hR_pos
  rw [h_td_scale, hε_norm] at h_bound
  rw [Real.norm_of_nonneg (pow_nonneg hε_pos.le _)]
  calc ‖u - v₀‖
      ≤ Real.sqrt 2 * (‖tangentDeviation w L‖ / ε) := h_bound
    _ ≤ Real.sqrt 2 * (c / Real.sqrt 2 * ε ^ m / ε) := by gcongr
    _ = c * (ε ^ m / ε) := by field_simp
    _ = c * ε ^ (m - 1) := by
        congr 1
        have hpow : ε ^ m = ε ^ (m - 1) * ε := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]
        rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hε_pos)]

private lemma re_pos_right_of_slope
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_R : ℂ) (hL_R_ne : L_R ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R)) :
    ∀ᶠ t in 𝓝[>] t₀, 0 < ((γ.toFun t - s) * starRingEnd ℂ L_R).re := by
  have hcont : ContinuousAt γ.toFun t₀ :=
    γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hdiff_right : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ.toFun t := by
    have hcl : IsClosed ((↑γ.partition : Set ℝ) \ {t₀}) :=
      (γ.partition.finite_toSet.subset Set.diff_subset).isClosed
    filter_upwards [nhdsWithin_le_nhds
        (hcl.isOpen_compl.mem_nhds (Set.mem_compl (by simp))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2),
      self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂
      fun hm => ht₁ ⟨hm, ne_of_gt (Set.mem_Ioi.mp ht₃)⟩
  obtain ⟨s_set, hs_mem, hs_diff⟩ := hdiff_right.exists_mem
  have hderiv : HasDerivWithinAt γ.toFun L_R (Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_iff_Ici.mpr (hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hcont.continuousWithinAt hs_mem htend_R)
  have hReLR : 0 < (L_R * starRingEnd ℂ L_R).re := by
    rw [Complex.mul_conj]; simp only [Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hL_R_ne
  have h_slope : Tendsto (slope γ.toFun t₀) (𝓝[>] t₀) (𝓝 L_R) :=
    (hasDerivWithinAt_iff_tendsto_slope' Set.notMem_Ioi_self).mp hderiv
  have h_slope_re : Tendsto (fun t => (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re)
      (𝓝[>] t₀) (𝓝 (L_R * starRingEnd ℂ L_R).re) :=
    (continuous_re.comp (continuous_mul_right _)).continuousAt.tendsto.comp h_slope
  have h_ev := h_slope_re (Ioi_mem_nhds hReLR)
  filter_upwards [h_ev, self_mem_nhdsWithin] with t ht ht_pos
  have ht_gt : t₀ < t := Set.mem_Ioi.mp ht_pos
  have h_pos_factor : (0 : ℝ) < t - t₀ := sub_pos.mpr ht_gt
  have h_slope_pos : 0 < (slope γ.toFun t₀ t * starRingEnd ℂ L_R).re :=
    Set.mem_Ioi.mp (Set.mem_preimage.mp ht)
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

private lemma re_pos_left_of_slope
    (γ : PiecewiseC1Immersion) (s : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (L_L : ℂ) (hL_L_ne : L_L ≠ 0)
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L)) :
    ∀ᶠ t in 𝓝[<] t₀, 0 < ((γ.toFun t - s) * starRingEnd ℂ (-L_L)).re := by
  have hcont : ContinuousAt γ.toFun t₀ :=
    γ.continuous_toFun.continuousAt (Icc_mem_nhds ht₀.1 ht₀.2)
  have hdiff_left : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ.toFun t := by
    have hcl : IsClosed ((↑γ.partition : Set ℝ) \ {t₀}) :=
      (γ.partition.finite_toSet.subset Set.diff_subset).isClosed
    filter_upwards [nhdsWithin_le_nhds
        (hcl.isOpen_compl.mem_nhds (Set.mem_compl (by simp))),
      nhdsWithin_le_nhds (Icc_mem_nhds ht₀.1 ht₀.2),
      self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.smooth_off_partition t ht₂
      fun hm => ht₁ ⟨hm, ne_of_lt (Set.mem_Iio.mp ht₃)⟩
  obtain ⟨s_set, hs_mem, hs_diff⟩ := hdiff_left.exists_mem
  have hderiv : HasDerivWithinAt γ.toFun L_L (Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_iff_Iic.mpr (hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hcont.continuousWithinAt hs_mem htend_L)
  have hReLLneg : (L_L * starRingEnd ℂ (-L_L)).re < 0 := by
    rw [map_neg, mul_neg, Complex.neg_re, neg_neg_iff_pos, Complex.mul_conj]
    simp only [Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hL_L_ne
  have h_slope : Tendsto (slope γ.toFun t₀) (𝓝[<] t₀) (𝓝 L_L) :=
    (hasDerivWithinAt_iff_tendsto_slope' Set.notMem_Iio_self).mp hderiv
  have h_slope_re : Tendsto (fun t => (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re)
      (𝓝[<] t₀) (𝓝 (L_L * starRingEnd ℂ (-L_L)).re) :=
    (continuous_re.comp (continuous_mul_right _)).continuousAt.tendsto.comp h_slope
  have h_ev := h_slope_re (Iio_mem_nhds hReLLneg)
  filter_upwards [h_ev, self_mem_nhdsWithin] with t ht ht_neg
  have ht_lt : t < t₀ := Set.mem_Iio.mp ht_neg
  have h_neg_factor : t - t₀ < 0 := sub_neg.mpr ht_lt
  have h_slope_neg : (slope γ.toFun t₀ t * starRingEnd ℂ (-L_L)).re < 0 :=
    Set.mem_Iio.mp (Set.mem_preimage.mp ht)
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

private lemma tangentDeviation_scale_eq
    (w L : ℂ) (_hw_ne : ‖w‖ ≠ 0) (hL_ne : ‖L‖ ≠ 0) :
    ‖tangentDeviation (w / (↑‖w‖ : ℂ)) (L / (↑‖L‖ : ℂ))‖ =
      ‖tangentDeviation w L‖ / ‖w‖ := by
  have h1 : (w / (↑‖w‖ : ℂ) : ℂ) = (‖w‖⁻¹ : ℝ) • w := by
    simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]
  have h2 : (L / (↑‖L‖ : ℂ) : ℂ) = (‖L‖⁻¹ : ℝ) • L := by
    simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]
  rw [h1, h2, tangentDeviation_real_smul_right _ (inv_ne_zero hL_ne),
    tangentDeviation_real_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_eq_div]

private lemma direction_rate_from_flatness_right
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_R : ℂ) (hL_R_ne : L_R ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R))
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
  have h_flat_eps : (fun ε => ‖tangentDeviation (γ.toFun (σ ε) - s) L_R‖) =o[𝓝[>] 0]
      (fun ε => ε ^ m) := by
    have h1 := (h_flat.right_flat L_R hL_R_ne htend_R).congr
      (fun t => by rw [hcross]) (fun t => by rw [hcross])
    exact ((h1.comp_tendsto hσ_tendsto).congr (fun _ => rfl) (fun _ => rfl)).trans_eventuallyEq
      (by filter_upwards [hσ_norm] with ε hε; simp only [Function.comp_def]; rw [hε])
  have h_re_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ((γ.toFun (σ ε) - s) * starRingEnd ℂ L_R).re :=
    hσ_tendsto.eventually (re_pos_right_of_slope γ s t₀ ht₀ hcross L_R hL_R_ne htend_R)
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
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hw_ne']
  have hR_pos : 0 < (u * starRingEnd ℂ v₀).re := by
    change 0 < (w / (↑‖w‖ : ℂ) * starRingEnd ℂ (L_R / (↑‖L_R‖ : ℂ))).re
    rw [map_div₀ (starRingEnd ℂ), Complex.conj_ofReal,
      div_mul_div_comm, ← Complex.ofReal_mul, Complex.div_ofReal_re]
    exact div_pos h_re (mul_pos (by rw [hε_norm]; exact hε_pos) hL_pos)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have h_td_bound' : ‖tangentDeviation w L_R‖ ≤ c / Real.sqrt 2 * ε ^ m := by
    rwa [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (pow_nonneg hε_pos.le _)] at h_td_bound
  exact direction_rate_final_calc m c ε hε_pos hm w L_R u v₀ hu_norm hv₀_norm hR_pos
    (tangentDeviation_scale_eq w L_R hw_ne' hL_ne) hε_norm h_td_bound'

private lemma tangentDeviation_scale_neg_eq
    (w L : ℂ) (_hw_ne : ‖w‖ ≠ 0) (hL_ne : ‖L‖ ≠ 0) :
    ‖tangentDeviation (w / (↑‖w‖ : ℂ)) (-L / (↑‖L‖ : ℂ))‖ =
      ‖tangentDeviation w (-L)‖ / ‖w‖ := by
  have h1 : (w / (↑‖w‖ : ℂ) : ℂ) = (‖w‖⁻¹ : ℝ) • w := by
    simp [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div]
  have h_negL : -L / (↑‖L‖ : ℂ) = (‖L‖⁻¹ : ℝ) • (-L) := by
    rw [Complex.real_smul, Complex.ofReal_inv, inv_mul_eq_div, neg_div]
  rw [h1, h_negL, tangentDeviation_real_smul_right _ (inv_ne_zero hL_ne),
    tangentDeviation_real_smul_left, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_eq_div]

private lemma direction_rate_from_flatness_left
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_L : ℂ) (hL_L_ne : L_L ≠ 0)
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L))
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
  have h_re_pos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < ((γ.toFun (σ ε) - s) * starRingEnd ℂ (-L_L)).re :=
    hσ_tendsto.eventually (re_pos_left_of_slope γ s t₀ ht₀ hcross L_L hL_L_ne htend_L)
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
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      div_self hw_ne']
  have hR_pos : 0 < (u * starRingEnd ℂ v₀).re := by
    change 0 < (w / (↑‖w‖ : ℂ) * starRingEnd ℂ (-L_L / (↑‖L_L‖ : ℂ))).re
    rw [map_div₀ (starRingEnd ℂ), map_neg, Complex.conj_ofReal,
      div_mul_div_comm, show w * -(starRingEnd ℂ L_L) = w * starRingEnd ℂ (-L_L) from by
        rw [map_neg], ← Complex.ofReal_mul, Complex.div_ofReal_re]
    exact div_pos h_re (mul_pos (by rw [hε_norm]; exact hε_pos) hL_pos)
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have h_td_bound' : ‖tangentDeviation w (-L_L)‖ ≤ c / Real.sqrt 2 * ε ^ m := by
    rwa [Real.norm_of_nonneg (norm_nonneg _),
      Real.norm_of_nonneg (pow_nonneg hε_pos.le _)] at h_td_bound
  exact direction_rate_final_calc m c ε hε_pos hm w (-L_L) u v₀ hu_norm hv₀_norm hR_pos
    (tangentDeviation_scale_neg_eq w L_L hw_ne' hL_ne) hε_norm h_td_bound'

private lemma cutoff_integral_split_to_sides
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (σ₁ σ₂ ε : ℝ)
    (hσ₁_ge : γ.a ≤ σ₁) (hσ₁_lt : σ₁ < σ₂) (hσ₂_le : σ₂ ≤ γ.b)
    (h_left : ∀ t ∈ Ico γ.a σ₁, ε < ‖γ.toFun t - s‖)
    (h_right : ∀ t ∈ Ioc σ₂ γ.b, ε < ‖γ.toFun t - s‖)
    (h_middle : ∀ t ∈ Icc σ₁ σ₂, ‖γ.toFun t - s‖ ≤ ε)
    (h_int_l : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume γ.a σ₁)
    (h_int_r : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume σ₂ γ.b) :
    ∫ t in γ.a..γ.b,
      (if ‖γ.toFun t - s‖ > ε
       then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
      (∫ t in γ.a..σ₁, (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t) +
      (∫ t in σ₂..γ.b, (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t) := by
  set F : ℝ → ℂ := fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t with hF_def
  have hae_left_raw : ∀ᵐ t ∂(volume.restrict (Ι γ.a σ₁)),
      (if ‖γ.toFun t - s‖ > ε then F t else 0) = F t := by
    rw [Set.uIoc_of_le hσ₁_ge, ← restrict_Ioo_eq_restrict_Ioc]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact MeasureTheory.ae_of_all _ fun t ht => by
      simp [show ‖γ.toFun t - s‖ > ε from h_left t ⟨ht.1.le, ht.2⟩]
  have hae_left : (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      =ᶠ[ae (volume.restrict (Ι γ.a σ₁))] F := hae_left_raw
  have hae_right_raw : ∀ᵐ t ∂(volume.restrict (Ι σ₂ γ.b)),
      (if ‖γ.toFun t - s‖ > ε then F t else 0) = F t := by
    rw [Set.uIoc_of_le hσ₂_le, ← restrict_Ioo_eq_restrict_Ioc]
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact MeasureTheory.ae_of_all _ fun t ht => by
      simp [show ‖γ.toFun t - s‖ > ε from h_right t ⟨ht.1, ht.2.le⟩]
  have hae_right : (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      =ᶠ[ae (volume.restrict (Ι σ₂ γ.b))] F := hae_right_raw
  have heq_mid : EqOn (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      (fun _ => (0 : ℂ)) [[σ₁, σ₂]] := by
    intro t ht
    rw [Set.uIcc_of_le hσ₁_lt.le] at ht
    simp [show ¬(‖γ.toFun t - s‖ > ε) from not_lt.mpr (h_middle t ht)]
  have hint_l := h_int_l.congr_ae hae_left.symm
  have hint_m : IntervalIntegrable
      (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0)
      volume σ₁ σ₂ :=
    (intervalIntegrable_const (c := (0 : ℂ))).congr
      (heq_mid.symm.mono Set.uIoc_subset_uIcc)
  have hint_r := h_int_r.congr_ae hae_right.symm
  have hsplit : ∫ t in γ.a..γ.b, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t =
      (∫ t in γ.a..σ₁, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t) +
      (∫ t in σ₁..σ₂, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t) +
      (∫ t in σ₂..γ.b, (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t) := by
    have h_σ₁_b := intervalIntegral.integral_add_adjacent_intervals hint_m hint_r
    have h_a_b := intervalIntegral.integral_add_adjacent_intervals hint_l (hint_m.trans hint_r)
    rw [← h_σ₁_b] at h_a_b; rw [← h_a_b, add_assoc]
  rw [hsplit]
  have h_mid_zero : ∫ t in σ₁..σ₂,
      (fun t => if ‖γ.toFun t - s‖ > ε then F t else 0) t = 0 := by
    rw [intervalIntegral.integral_congr heq_mid, intervalIntegral.integral_zero]
  rw [h_mid_zero, add_zero,
    intervalIntegral.integral_congr_ae_restrict hae_left,
    intervalIntegral.integral_congr_ae_restrict hae_right]

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
  have hn_ne : (-(m : ℤ) : ℤ) ≠ -1 := by omega
  have hne_left : ∀ t ∈ Icc γ.a σ₁, γ.toFun t ≠ s := by
    intro t ht habs
    rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
    · rw [habs, sub_self, norm_zero] at hσ₁_val; linarith
    · have := h_left t ⟨ht.1, ht_lt⟩; rw [habs, sub_self, norm_zero] at this; linarith
  have hne_right : ∀ t ∈ Icc σ₂ γ.b, γ.toFun t ≠ s := by
    intro t ht habs
    rcases eq_or_lt_of_le ht.1 with rfl | ht_gt
    · rw [habs, sub_self, norm_zero] at hσ₂_val; linarith
    · have := h_right t ⟨ht_gt, ht.2⟩; rw [habs, sub_self, norm_zero] at this; linarith
  set F : ℝ → ℂ := fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t
  have hsplit := cutoff_integral_split_to_sides γ s m σ₁ σ₂ ε
    hσ₁_ge hσ₁_lt hσ₂_le h_left h_right h_middle h_int_l h_int_r
  rw [hsplit]
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  set E := (γ.toPiecewiseC1Curve.partition : Set ℝ)
  have hE_count : E.Countable := γ.toPiecewiseC1Curve.partition.countable_toSet
  have hγ_diff : ∀ t ∈ Icc γ.a γ.b, t ∉ E → DifferentiableAt ℝ γ.toFun t :=
    fun t ht hne => γ.toPiecewiseC1Curve.smooth_off_partition t ht hne
  have hftc_l := integral_zpow_comp_sub_mul_deriv hn_ne hσ₁_ge
    (hγ_cont.mono (Icc_subset_Icc le_rfl (hσ₁_lt.le.trans hσ₂_le))) hne_left
    E hE_count (Set.inter_subset_right) (fun t ht hne =>
      hγ_diff t ⟨ht.1.le, ht.2.le.trans (hσ₁_lt.le.trans hσ₂_le)⟩ hne) h_int_l
  have hftc_r := integral_zpow_comp_sub_mul_deriv hn_ne hσ₂_le
    (hγ_cont.mono (Icc_subset_Icc (hσ₁_ge.trans hσ₁_lt.le) le_rfl)) hne_right
    E hE_count (Set.inter_subset_right) (fun t ht hne =>
      hγ_diff t ⟨(hσ₁_ge.trans hσ₁_lt.le).trans ht.1.le, ht.2.le⟩ hne) h_int_r
  rw [hftc_l, hftc_r, hγ_closed]
  have hint_eq : (-(m : ℤ) + 1 : ℤ) = 1 - (m : ℤ) := by omega
  simp only [hint_eq]
  have hcast : (↑(1 - (m : ℤ)) : ℂ) = 1 - ↑↑m := by push_cast; ring
  simp only [hcast, Int.cast_natCast]; ring

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
  · rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨l, r, hl_lt, hr_gt, hl_ge_a, hr_le_b, _, hg_mono⟩ :=
      _root_.piecewiseC1Immersion_norm_strictMono_near_crossing γ s t₀ ht₀ hcross
    have hη_r : 0 < min η (r - t₀) := lt_min hη (by linarith)
    set t₁ := t₀ + min η (r - t₀) / 2 with ht₁_def
    have ht₁_gt : t₀ < t₁ := by simp only [ht₁_def]; linarith
    have ht₁_lt_r : t₁ < r := by simp only [ht₁_def]; linarith [min_le_right η (r - t₀)]
    have ht₁_mem : t₁ ∈ Icc t₀ r := ⟨ht₁_gt.le, ht₁_lt_r.le⟩
    have hg_t₁ : 0 < ‖γ.toFun t₁ - s‖ := by
      have h_lt := hg_mono ⟨le_rfl, hr_gt.le⟩ ht₁_mem ht₁_gt
      have : ‖γ.toFun t₀ - s‖ = 0 := by rw [hcross, sub_self, norm_zero]
      linarith
    set ε₀ := min ‖γ.toFun t₁ - s‖ δ
    have hε₀_pos : 0 < ε₀ := lt_min hg_t₁ hδ
    filter_upwards [Ioo_mem_nhdsGT hε₀_pos] with ε ⟨hε_pos, hε_lt⟩
    have hε_Ioo : ε ∈ Ioo 0 δ := ⟨hε_pos, lt_of_lt_of_le hε_lt (min_le_right _ _)⟩
    obtain ⟨hσ₂_gt, hσ₂_le, hσ₂_norm, hσ₂_mid⟩ := hσ₂_props ε hε_Ioo
    rw [dist_eq_norm, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ₂_gt)]
    have hε_lt_t₁ : ε < ‖γ.toFun t₁ - s‖ := lt_of_lt_of_le hε_lt (min_le_left _ _)
    by_contra h_not_lt
    push_neg at h_not_lt
    have ht₁_le_σ₂ : t₁ ≤ σ₂ ε := by
      simp only [ht₁_def]; linarith [min_le_left η (r - t₀)]
    have := hσ₂_mid t₁ ⟨ht₁_gt.le, ht₁_le_σ₂⟩
    linarith
  · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (hσ₂_props ε hε).1

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
    by_contra h_not_lt
    push_neg at h_not_lt
    have hσ₁_le_t₁ : σ₁ ε ≤ t₁ := by
      simp only [ht₁_def]; linarith [min_le_left η (t₀ - l)]
    have := hσ₁_mid t₁ ⟨hσ₁_le_t₁, ht₁_lt.le⟩
    linarith
  · filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (hσ₁_props ε hε).1

private lemma zpow_mul_deriv_intervalIntegrable
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ)
    (c d : ℝ) (hcd : c ≤ d)
    (hc_ge : γ.a ≤ c) (hd_le : d ≤ γ.b)
    (hne : ∀ t ∈ Icc c d, γ.toFun t ≠ s) :
    IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t)
      MeasureTheory.volume c d := by
  have hγ_cont := γ.toPiecewiseC1Curve.continuous_toFun
  have hcont_zpow : ContinuousOn (fun t => (γ.toFun t - s) ^ (-(m : ℤ)))
      (Set.uIcc c d) := by
    rw [Set.uIcc_of_le hcd]
    exact continuousOn_zpow_comp_sub
      (hγ_cont.mono (Icc_subset_Icc hc_ge hd_le)) hne
  have hderiv_int : IntervalIntegrable (deriv γ.toFun) MeasureTheory.volume c d :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
      (piecewiseC1Immersion_deriv_bounded γ)).mono_set
      ((Set.uIcc_of_le hcd ▸ Set.uIcc_of_le (le_of_lt γ.hab) ▸
        Icc_subset_Icc hc_ge hd_le) : [[c, d]] ⊆ [[γ.a, γ.b]])
  exact hderiv_int.continuousOn_mul hcont_zpow

private lemma immersion_right_deriv_limit
    (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L) := by
  by_cases h : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · exact γ.right_deriv_limit t₀ h ht₀.2
  · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
      (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
        nhdsWithin_le_nhds⟩

private lemma immersion_left_deriv_limit
    (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L) := by
  by_cases h : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · exact γ.left_deriv_limit t₀ h ht₀.1
  · exact ⟨_, γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) h,
      (γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ h).tendsto.mono_left
        nhdsWithin_le_nhds⟩

private lemma angle_at_crossing_arg_relation
    (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
    (L_R L_L : ℂ) (_hL_R_ne : L_R ≠ 0) (hL_L_ne : L_L ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R))
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L)) :
    ∃ n_angle : ℤ, L_R.arg - (-L_L).arg =
      _root_.angleAtCrossing γ t₀ ht₀ + ↑n_angle * (2 * Real.pi) := by
  by_cases hp : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · refine ⟨0, ?_⟩
    simp only [Int.cast_zero, zero_mul, add_zero]
    unfold angleAtCrossing
    rw [dif_pos hp]
    have hL_R_eq := tendsto_nhds_unique htend_R
      (Classical.choose_spec (γ.right_deriv_limit t₀ hp ht₀.2)).2
    have hL_L_eq := tendsto_nhds_unique htend_L
      (Classical.choose_spec (γ.left_deriv_limit t₀ hp ht₀.1)).2
    rw [hL_R_eq, hL_L_eq]
  · rw [angleAtCrossing_smooth γ t₀ ht₀ hp]
    have hL_eq : L_R = L_L := by
      have hcont := γ.toPiecewiseC1Curve.deriv_continuous_off_partition t₀ ht₀ hp
      exact (tendsto_nhds_unique htend_R
        (hcont.tendsto.mono_left nhdsWithin_le_nhds)).trans
        (tendsto_nhds_unique htend_L
          (hcont.tendsto.mono_left nhdsWithin_le_nhds)).symm
    rw [hL_eq]
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

private lemma cutoff_zpow_direction_and_ftc
    (γ : PiecewiseC1Immersion) (s : ℂ) (m : ℕ) (hm : 2 ≤ m)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = s)
    (h_unique : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₀)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (h_flat : IsFlatOfOrder γ.toFun t₀ m)
    (L_R L_L : ℂ) (hL_R_ne : L_R ≠ 0) (hL_L_ne : L_L ≠ 0)
    (htend_R : Tendsto (deriv γ.toFun) (𝓝[>] t₀) (𝓝 L_R))
    (htend_L : Tendsto (deriv γ.toFun) (𝓝[<] t₀) (𝓝 L_L))
    (σ₁ σ₂ : ℝ → ℝ) (δ : ℝ) (hδ_pos : 0 < δ)
    (hprops : ∀ ε, ε ∈ Ioo 0 δ →
      γ.a ≤ σ₁ ε ∧ σ₁ ε < t₀ ∧ t₀ < σ₂ ε ∧ σ₂ ε ≤ γ.b ∧
      ‖γ.toFun (σ₁ ε) - s‖ = ε ∧ ‖γ.toFun (σ₂ ε) - s‖ = ε ∧
      (∀ t ∈ Ico γ.a (σ₁ ε), ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Ioc (σ₂ ε) γ.b, ε < ‖γ.toFun t - s‖) ∧
      (∀ t ∈ Icc (σ₁ ε) (σ₂ ε), ‖γ.toFun t - s‖ ≤ ε))
    (hIoo_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo 0 δ) :
    ((fun ε => ‖(γ.toFun (σ₂ ε) - s) / (↑‖γ.toFun (σ₂ ε) - s‖ : ℂ) -
        L_R / ↑‖L_R‖‖) =o[𝓝[>] (0 : ℝ)] fun ε => ε ^ (m - 1 : ℕ)) ∧
    ((fun ε => ‖(γ.toFun (σ₁ ε) - s) / (↑‖γ.toFun (σ₁ ε) - s‖ : ℂ) -
        (-L_L / ↑‖L_L‖)‖) =o[𝓝[>] (0 : ℝ)] fun ε => ε ^ (m - 1 : ℕ)) ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∫ t in γ.a..γ.b,
        (if ‖γ.toFun t - s‖ > ε
         then (γ.toFun t - s) ^ (-(m : ℤ)) * deriv γ.toFun t else 0) =
        ((γ.toFun (σ₁ ε) - s) ^ (1 - (m : ℤ)) -
          (γ.toFun (σ₂ ε) - s) ^ (1 - (m : ℤ))) /
          ((1 : ℂ) - ↑(m : ℤ))) := by
  have hσ₂_tendsto : Tendsto σ₂ (𝓝[>] 0) (𝓝[>] t₀) :=
    exit_time_tendsto_right γ s t₀ ht₀ hcross h_unique σ₂ δ hδ_pos
      (fun ε hε => ⟨(hprops ε hε).2.2.1, (hprops ε hε).2.2.2.1,
        (hprops ε hε).2.2.2.2.2.1,
        fun t ht => (hprops ε hε).2.2.2.2.2.2.2.2
          t ⟨le_trans (le_of_lt (hprops ε hε).2.1) ht.1, ht.2⟩⟩)
  have hσ₁_tendsto : Tendsto σ₁ (𝓝[>] 0) (𝓝[<] t₀) :=
    exit_time_tendsto_left γ s t₀ ht₀ hcross h_unique σ₁ δ hδ_pos
      (fun ε hε => ⟨(hprops ε hε).2.1, (hprops ε hε).1,
        (hprops ε hε).2.2.2.2.1,
        fun t ht => (hprops ε hε).2.2.2.2.2.2.2.2
          t ⟨ht.1, le_trans ht.2 (le_of_lt (hprops ε hε).2.2.1)⟩⟩)
  refine ⟨?_, ?_, ?_⟩
  · exact direction_rate_from_flatness_right γ s m hm t₀ ht₀ hcross h_flat
      L_R hL_R_ne htend_R σ₂
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.2.1)
      hσ₂_tendsto
  · exact direction_rate_from_flatness_left γ s m hm t₀ ht₀ hcross h_flat
      L_L hL_L_ne htend_L σ₁
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).1)
      (hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.1)
      hσ₁_tendsto
  · filter_upwards [hIoo_ev] with ε hε
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hprops ε hε
    have hne_left : ∀ t ∈ Icc γ.a (σ₁ ε), γ.toFun t ≠ s := by
      intro t ht habs
      rcases eq_or_lt_of_le ht.2 with rfl | ht_lt
      · rw [habs, sub_self, norm_zero] at h5; linarith [hε.1]
      · have := h7 t ⟨ht.1, ht_lt⟩; rw [habs, sub_self, norm_zero] at this; linarith [hε.1]
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
  obtain ⟨L_R, hL_R_ne, htend_R⟩ := immersion_right_deriv_limit γ t₀ ht₀
  obtain ⟨L_L, hL_L_ne, htend_L⟩ := immersion_left_deriv_limit γ t₀ ht₀
  obtain ⟨δ, hδ_pos, h_exit⟩ :=
    _root_.exists_cutoff_boundary_times γ s t₀ ht₀ hcross h_unique
  let σ₁ := fun ε => if h : ε ∈ Ioo 0 δ then (h_exit ε h).choose else t₀
  let σ₂ := fun ε => if h : ε ∈ Ioo 0 δ then (h_exit ε h).choose_spec.choose else t₀
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
  let wR : ℝ → ℂ := fun ε => γ.toFun (σ₂ ε) - s
  let wL : ℝ → ℂ := fun ε => γ.toFun (σ₁ ε) - s
  let uR : ℂ := L_R / ↑‖L_R‖
  let uL : ℂ := -L_L / ↑‖L_L‖
  obtain ⟨h_rate_R, h_rate_L, h_ftc⟩ :=
    cutoff_zpow_direction_and_ftc γ s m hm t₀ ht₀ hcross
    h_unique hγ_closed h_flat L_R L_L hL_R_ne hL_L_ne htend_R htend_L σ₁ σ₂ δ hδ_pos
    hprops hIoo_ev
  refine ⟨wR, wL, uR, uL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_rate_R, h_rate_L, h_ftc⟩
  · exact hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.2.1
  · exact hIoo_ev.mono fun ε hε => (hprops ε hε).2.2.2.2.1
  · filter_upwards [hIoo_ev] with ε hε
    change γ.toFun (σ₂ ε) - s ≠ 0
    have h_norm := (hprops ε hε).2.2.2.2.2.1
    exact sub_ne_zero.mpr (fun h => by rw [h, sub_self, norm_zero] at h_norm; linarith [hε.1])
  · filter_upwards [hIoo_ev] with ε hε
    change γ.toFun (σ₁ ε) - s ≠ 0
    have h_norm := (hprops ε hε).2.2.2.2.1
    exact sub_ne_zero.mpr (fun h => by rw [h, sub_self, norm_zero] at h_norm; linarith [hε.1])
  · change ‖L_R / ↑‖L_R‖‖ = 1
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (norm_pos_iff.mpr hL_R_ne),
      div_self (norm_ne_zero_iff.mpr hL_R_ne)]
  · change ‖-L_L / ↑‖L_L‖‖ = 1
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (norm_pos_iff.mpr hL_L_ne), div_self (norm_ne_zero_iff.mpr hL_L_ne)]
  · have h_arg_uR : uR.arg = L_R.arg := by
      change (L_R / ↑‖L_R‖).arg = L_R.arg
      rw [div_eq_inv_mul, ← Complex.ofReal_inv,
        Complex.arg_real_mul L_R (inv_pos.mpr (norm_pos_iff.mpr hL_R_ne))]
    have h_arg_uL : uL.arg = (-L_L).arg := by
      change (-L_L / ↑‖L_L‖).arg = (-L_L).arg
      rw [div_eq_inv_mul, ← Complex.ofReal_inv,
        Complex.arg_real_mul (-L_L) (inv_pos.mpr (norm_pos_iff.mpr hL_L_ne))]
    rw [h_arg_uR, h_arg_uL]
    exact angle_at_crossing_arg_relation γ t₀ ht₀ L_R L_L hL_R_ne hL_L_ne htend_R htend_L

end GeneralizedResidueTheory
