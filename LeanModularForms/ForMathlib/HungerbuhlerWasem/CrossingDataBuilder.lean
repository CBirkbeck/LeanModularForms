/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import LeanModularForms.ForMathlib.BoundaryWinding
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.AsymmetricSingleCrossing
import LeanModularForms.ForMathlib.HungerbuhlerWasem.HigherOrderAsymptotics

/-!
# Generic `SingleCrossingData` builder from `IsFlatOfOrder _ _ 1`

This file provides infrastructure to build `SingleCrossingData` for any closed
piecewise-`C¹` immersion `γ` crossing a point `s` at parameter `t₀ ∈ Ioo 0 1`
transversely (`IsFlatOfOrder γ t₀ 1`) and uniquely.

## Components delivered

1. **`SingleCrossingData.ofClosedImmersion_flat_one`** — the headline generic
   builder. Takes `(γ : ClosedPwC1Immersion x, t₀, h_at, h_unique, h_flat,
   L, δ, threshold, hthresh, hδ_pos, hδ_small, h_far, h_near, ftcHyp)` and
   packages into `SingleCrossingData γ.toPiecewiseC1Path s`. Mirrors
   `mkSingleCrossingData_smooth` but for arbitrary `ClosedPwC1Immersion`.

2. **Far bound from uniqueness** (`exists_far_bound_compact`): if `γ` crosses
   `s` only at `t₀` on `[0, 1]`, then `‖γ(t) - s‖` has a positive minimum on
   any compact set `[0, t₀ - r] ∪ [t₀ + r, 1]`.

3. **One-sided derivative limits** (`exists_left_deriv_limit`,
   `exists_right_deriv_limit`): at any interior `t₀`, the immersion has nonzero
   one-sided derivative limits.

4. **Chord-to-tangent eventual bounds** (`exists_chord_lower_bound_right`,
   etc.): for some `r > 0`, on `(t₀, t₀ + r)`, `(‖L_+‖/2)·(t-t₀) ≤
   ‖γ(t) - s‖ ≤ (3‖L_+‖/2)·(t-t₀)`. Symmetric on the left.

5. **Eventual differentiability on each side** (`eventually_differentiable_*`).

These pieces are the geometric ingredients needed by the downstream T-BR-04
ticket (per-pole CPV witness assembly).

## Design note

The strict-monotonicity infrastructure is now in place:

* **`norm_sub_strictMonoOn_right`** — `‖γ(t) - s‖` is strictly increasing on
  `[t₀, t₀ + r]` for some `r > 0`.
* **`norm_sub_strictAntiOn_left`** — `‖γ(t) - s‖` is strictly decreasing on
  `[t₀ - r, t₀]` for some `r > 0`.

These follow from `HasDerivAt.norm_sq` and a careful chord-to-tangent
positivity argument: `(d/dt)‖γ(t) - s‖² = 2 · ⟪γ(t) - s, γ'(t)⟫_ℝ`, whose
leading term `(t - t₀) · ‖L‖²` dominates the `o(t - t₀)` corrections.

### Asymmetric crossings

The `SingleCrossingData` scheme uses a SINGLE cutoff `δ(ε)` controlling both
sides simultaneously: `‖γ(t) - s‖ ≤ ε` for `|t - t₀| ≤ δ(ε)` and
`‖γ(t) - s‖ > ε` for `|t - t₀| > δ(ε)`. For this to hold, the LEFT and RIGHT
exit times `δ_R(ε)`, `δ_L(ε)` (where `‖γ(t₀ ± δ_•(ε)) - s‖ = ε`) must be EQUAL
— i.e., the curve's distance-to-`s` function must be SYMMETRIC about `t₀`.

Even at off-partition (smooth) interior points, this symmetry does not hold
generically: for asymmetric `γ`, the level set `{t : ‖γ(t) - s‖ = ε}` consists
of two distinct points `t₀ + δ_R(ε)` and `t₀ - δ_L(ε)` with `δ_R ≠ δ_L`. Then
no choice of `δ(ε)` simultaneously satisfies h_near and h_far (h_near requires
`δ ≤ min(δ_R, δ_L)`, h_far requires `δ ≥ max(δ_R, δ_L)`).

Therefore the headline constructor `SingleCrossingData.ofClosedImmersion_flat_one`
continues to take `(δ, threshold, h_far, h_near)` as parameters: callers supply
curve-specific cutoffs (using either symmetry of the curve, or stronger flatness
input). The strict-monotonicity lemmas exposed in this file allow callers to
*build* such cutoffs via IVT inversion when they have additional symmetry
information.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-! ### Compact-set far bound from uniqueness

When `γ` crosses `s` only at `t₀` on `[0, 1]`, the function `t ↦ ‖γ(t) - s‖`
has a positive minimum on the compact set `[0, t₀ - r] ∪ [t₀ + r, 1]` for any
`r > 0`. -/

/-- **Far bound from uniqueness**: if `γ` is continuous and crosses `s` only at
`t₀ ∈ [0, 1]`, then on any compact set `Icc 0 (t₀ - r) ∪ Icc (t₀ + r) 1` (with
`r > 0`), the distance `‖γ(t) - s‖` has a positive minimum. -/
theorem exists_far_bound_compact
    (γ : ℝ → ℂ) (hγ : Continuous γ) (s : ℂ) (t₀ : ℝ)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1, γ t = s → t = t₀)
    {r : ℝ} (hr_pos : 0 < r) (hr_lt₀ : r ≤ t₀) (hr_lt₁ : r ≤ 1 - t₀) :
    ∃ m : ℝ, 0 < m ∧
      (∀ t ∈ Icc (0 : ℝ) (t₀ - r), m ≤ ‖γ t - s‖) ∧
      (∀ t ∈ Icc (t₀ + r) (1 : ℝ), m ≤ ‖γ t - s‖) := by
  have h_norm_cont : ContinuousOn (fun t => ‖γ t - s‖) (univ : Set ℝ) :=
    (hγ.continuousOn.sub continuousOn_const).norm
  obtain ⟨t_l, ht_l_mem, ht_l_min⟩ :=
    (isCompact_Icc (a := (0 : ℝ)) (b := t₀ - r)).exists_isMinOn
      ⟨0, le_rfl, by linarith⟩ (h_norm_cont.mono (subset_univ _))
  have h_t_l_in_Icc01 : t_l ∈ Icc (0 : ℝ) 1 :=
    ⟨ht_l_mem.1, by linarith [ht_l_mem.2]⟩
  have hm_l_pos : 0 < ‖γ t_l - s‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
    have h_ne : t_l ≠ t₀ := fun h => by linarith [h ▸ ht_l_mem.2]
    exact h_ne (h_unique t_l h_t_l_in_Icc01 h_eq)
  obtain ⟨t_r, ht_r_mem, ht_r_min⟩ :=
    (isCompact_Icc (a := t₀ + r) (b := (1 : ℝ))).exists_isMinOn
      ⟨1, by linarith, le_rfl⟩ (h_norm_cont.mono (subset_univ _))
  have h_t_r_in_Icc01 : t_r ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht_r_mem.1], ht_r_mem.2⟩
  have hm_r_pos : 0 < ‖γ t_r - s‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
    have h_ne : t_r ≠ t₀ := fun h => by linarith [h ▸ ht_r_mem.1]
    exact h_ne (h_unique t_r h_t_r_in_Icc01 h_eq)
  exact ⟨_, lt_min hm_l_pos hm_r_pos,
    fun _ ht => (min_le_left _ _).trans (ht_l_min ht),
    fun _ ht => (min_le_right _ _).trans (ht_r_min ht)⟩

/-! ### One-sided derivative limits at interior points -/

/-- At any `t₀ ∈ Ioo 0 1`, the right derivative limit `L_+` exists and is nonzero. -/
theorem exists_right_deriv_limit
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] t₀) (𝓝 L) := by
  by_cases h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  · exact γ.toPwC1Immersion.right_deriv_limit t₀ h_part
  · refine ⟨deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀,
      γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_part,
      (γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off t₀ ht₀
        h_part).tendsto.mono_left nhdsWithin_le_nhds⟩

/-- At any `t₀ ∈ Ioo 0 1`, the left derivative limit `L_-` exists and is nonzero. -/
theorem exists_left_deriv_limit
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] t₀) (𝓝 L) := by
  by_cases h_part : t₀ ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
  · exact γ.toPwC1Immersion.left_deriv_limit t₀ h_part
  · refine ⟨deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀,
      γ.toPwC1Immersion.deriv_ne_zero t₀ ht₀ h_part,
      (γ.toPwC1Immersion.toPiecewiseC1Path.deriv_continuous_off t₀ ht₀
        h_part).tendsto.mono_left nhdsWithin_le_nhds⟩

/-! ### Eventual differentiability on each side -/

/-- Differentiability is eventual on `𝓝[>] t₀` for an immersion at interior `t₀`. -/
theorem eventually_differentiable_right
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝[>] t₀,
      DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t := by
  have hcl : IsClosed
      ((↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) \ {t₀}) :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.subset
      diff_subset).isClosed
  filter_upwards [
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (mem_compl fun h => h.2 rfl)),
    nhdsWithin_le_nhds (Ioo_mem_nhds ht₀.1 ht₀.2),
    self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
  exact γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off t ht₂
    fun hm => ht₁ ⟨hm, ne_of_gt (mem_Ioi.mp ht₃)⟩

/-- Differentiability is eventual on `𝓝[<] t₀` for an immersion at interior `t₀`. -/
theorem eventually_differentiable_left
    (γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    ∀ᶠ t in 𝓝[<] t₀,
      DifferentiableAt ℝ γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t := by
  have hcl : IsClosed
      ((↑γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) \ {t₀}) :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.subset
      diff_subset).isClosed
  filter_upwards [
    nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (mem_compl fun h => h.2 rfl)),
    nhdsWithin_le_nhds (Ioo_mem_nhds ht₀.1 ht₀.2),
    self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
  exact γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off t ht₂
    fun hm => ht₁ ⟨hm, ne_of_lt (mem_Iio.mp ht₃)⟩

/-! ### Chord-to-tangent eventual inequalities

From the right derivative limit `L_+` at `t₀`, we get the eventual two-sided
bound `(‖L_+‖/2)·(t - t₀) ≤ ‖γ(t) - s‖ ≤ (3‖L_+‖/2)·(t - t₀)` for `t > t₀`
close to `t₀`. Symmetric on the left.

These follow from the differentiability `o(t - t₀)` bound and the triangle
inequality. -/

/-- **Right-side chord-to-tangent eventual lower bound**: eventually on
`𝓝[>] t₀`, `(‖L_+‖/2) · (t - t₀) ≤ ‖γ(t) - s‖`. -/
theorem chord_lower_bound_right_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[>] t₀, (‖L‖/2) * (t - t₀) ≤ ‖γ t - s‖ := by
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hr := hasDerivWithinAt_iff_isLittleO.mp <| hasDerivWithinAt_Ioi_iff_Ici.mpr <|
    hasDerivWithinAt_Ici_of_tendsto_deriv (fun t ht => (hS_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hS_mem hL_right
  filter_upwards [hr.def (by positivity : (0 : ℝ) < ‖L‖/2), self_mem_nhdsWithin]
    with t h_bound h_t_gt
  have h_t_pos : 0 < t - t₀ := sub_pos.mpr h_t_gt
  rw [Real.norm_eq_abs, abs_of_pos h_t_pos] at h_bound
  have h_eq : γ t - s = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) := by rw [h_at]; ring
  have h_norm_smul : ‖((t - t₀) : ℝ) • L‖ = (t - t₀) * ‖L‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_t_pos]
  have h_tri : ‖((t - t₀) : ℝ) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
      ‖((t - t₀) : ℝ) • L + (γ t - γ t₀ - (t - t₀) • L)‖ := by
    have h1 := norm_sub_norm_le (((t - t₀) : ℝ) • L) (-(γ t - γ t₀ - (t - t₀) • L))
    rwa [norm_neg, sub_neg_eq_add] at h1
  rw [h_eq]
  rw [h_norm_smul] at h_tri
  have h_alg : (t - t₀) * ‖L‖ - ‖L‖ / 2 * (t - t₀) = ‖L‖ / 2 * (t - t₀) := by ring
  have h_bound' : (t - t₀) * ‖L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ ≥
      (t - t₀) * ‖L‖ - ‖L‖ / 2 * (t - t₀) := by gcongr; exact h_bound
  linarith [h_tri, h_bound', h_alg]

/-- **Right-side chord-to-tangent eventual upper bound**: eventually on
`𝓝[>] t₀`, `‖γ(t) - s‖ ≤ (3‖L_+‖/2) · (t - t₀)`. -/
theorem chord_upper_bound_right_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[>] t₀, ‖γ t - s‖ ≤ (3 * ‖L‖/2) * (t - t₀) := by
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hr := hasDerivWithinAt_iff_isLittleO.mp <| hasDerivWithinAt_Ioi_iff_Ici.mpr <|
    hasDerivWithinAt_Ici_of_tendsto_deriv (fun t ht => (hS_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hS_mem hL_right
  filter_upwards [hr.def (by positivity : (0 : ℝ) < ‖L‖/2), self_mem_nhdsWithin]
    with t h_bound h_t_gt
  have h_t_pos : 0 < t - t₀ := sub_pos.mpr h_t_gt
  rw [Real.norm_eq_abs, abs_of_pos h_t_pos] at h_bound
  have h_eq : γ t - s = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) := by rw [h_at]; ring
  have h_norm_smul : ‖((t - t₀) : ℝ) • L‖ = (t - t₀) * ‖L‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos h_t_pos]
  rw [h_eq]
  calc ‖((t - t₀) : ℝ) • L + (γ t - γ t₀ - (t - t₀) • L)‖
      ≤ ‖((t - t₀) : ℝ) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := norm_add_le _ _
    _ ≤ (t - t₀) * ‖L‖ + ‖L‖/2 * (t - t₀) := by gcongr <;> [exact h_norm_smul.le; exact h_bound]
    _ = (3 * ‖L‖/2) * (t - t₀) := by ring

/-- **Left-side chord-to-tangent eventual lower bound**: eventually on
`𝓝[<] t₀`, `(‖L_-‖/2) · (t₀ - t) ≤ ‖γ(t) - s‖`. -/
theorem chord_lower_bound_left_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[<] t₀, (‖L‖/2) * (t₀ - t) ≤ ‖γ t - s‖ := by
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hr := hasDerivWithinAt_iff_isLittleO.mp <| hasDerivWithinAt_Iio_iff_Iic.mpr <|
    hasDerivWithinAt_Iic_of_tendsto_deriv (fun t ht => (hS_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hS_mem hL_left
  filter_upwards [hr.def (by positivity : (0 : ℝ) < ‖L‖/2), self_mem_nhdsWithin]
    with t h_bound h_t_lt
  have h_t_pos : 0 < t₀ - t := sub_pos.mpr h_t_lt
  have h_norm_real : ‖t - t₀‖ = t₀ - t := by
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos h_t_pos]
  rw [h_norm_real] at h_bound
  have h_eq : γ t - s = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) := by rw [h_at]; ring
  have h_norm_smul : ‖((t - t₀) : ℝ) • L‖ = (t₀ - t) * ‖L‖ := by rw [norm_smul, h_norm_real]
  have h_tri : ‖((t - t₀) : ℝ) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ ≤
      ‖((t - t₀) : ℝ) • L + (γ t - γ t₀ - (t - t₀) • L)‖ := by
    have h1 := norm_sub_norm_le (((t - t₀) : ℝ) • L) (-(γ t - γ t₀ - (t - t₀) • L))
    rwa [norm_neg, sub_neg_eq_add] at h1
  rw [h_eq]
  rw [h_norm_smul] at h_tri
  have h_alg : (t₀ - t) * ‖L‖ - ‖L‖ / 2 * (t₀ - t) = ‖L‖ / 2 * (t₀ - t) := by ring
  have h_bound' : (t₀ - t) * ‖L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ ≥
      (t₀ - t) * ‖L‖ - ‖L‖ / 2 * (t₀ - t) := by gcongr; exact h_bound
  linarith [h_tri, h_bound', h_alg]

/-- **Left-side chord-to-tangent eventual upper bound**: eventually on
`𝓝[<] t₀`, `‖γ(t) - s‖ ≤ (3‖L_-‖/2) · (t₀ - t)`. -/
theorem chord_upper_bound_left_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[<] t₀, ‖γ t - s‖ ≤ (3 * ‖L‖/2) * (t₀ - t) := by
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hr := hasDerivWithinAt_iff_isLittleO.mp <| hasDerivWithinAt_Iio_iff_Iic.mpr <|
    hasDerivWithinAt_Iic_of_tendsto_deriv (fun t ht => (hS_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hS_mem hL_left
  filter_upwards [hr.def (by positivity : (0 : ℝ) < ‖L‖/2), self_mem_nhdsWithin]
    with t h_bound h_t_lt
  have h_t_pos : 0 < t₀ - t := sub_pos.mpr h_t_lt
  have h_norm_real : ‖t - t₀‖ = t₀ - t := by
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos h_t_pos]
  rw [h_norm_real] at h_bound
  have h_eq : γ t - s = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) := by rw [h_at]; ring
  have h_norm_smul : ‖((t - t₀) : ℝ) • L‖ = (t₀ - t) * ‖L‖ := by rw [norm_smul, h_norm_real]
  rw [h_eq]
  calc ‖((t - t₀) : ℝ) • L + (γ t - γ t₀ - (t - t₀) • L)‖
      ≤ ‖((t - t₀) : ℝ) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := norm_add_le _ _
    _ ≤ (t₀ - t) * ‖L‖ + ‖L‖/2 * (t₀ - t) := by gcongr <;> [exact h_norm_smul.le; exact h_bound]
    _ = (3 * ‖L‖/2) * (t₀ - t) := by ring

/-! ### Strict monotonicity of `‖γ(t) - s‖` on a one-sided neighborhood

From the differentiability `o(t-t₀)` bound at `t₀`, the squared-norm function
`t ↦ ‖γ(t) - s‖²` has positive derivative on `(t₀, t₀+r)` for some `r > 0`.
This gives strict monotonicity of `‖γ(t) - s‖` itself on the one-sided
neighborhood, which is the key ingredient for inverting the norm via IVT
to define the exit-time cutoff `δ(ε)`. -/

/-- The real "inner product" of two complex numbers viewed as ℝ²:
`reInner z w := z.re * w.re + z.im * w.im`. This equals `Re(z * conj w)`. -/
private def reInner (z w : ℂ) : ℝ := z.re * w.re + z.im * w.im

private lemma reInner_le_norm_mul_norm (z w : ℂ) :
    |reInner z w| ≤ ‖z‖ * ‖w‖ := by
  have h_id : reInner z w = (z * (starRingEnd ℂ) w).re := by
    unfold reInner
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have h_norm_eq : ‖z‖ * ‖w‖ = ‖z * (starRingEnd ℂ) w‖ := by
    rw [norm_mul, Complex.norm_conj]
  rw [h_id, h_norm_eq]
  exact Complex.abs_re_le_norm _

private lemma reInner_add_left (a b c : ℂ) :
    reInner (a + b) c = reInner a c + reInner b c := by
  unfold reInner
  simp only [Complex.add_re, Complex.add_im]; ring

private lemma reInner_add_right (a b c : ℂ) :
    reInner a (b + c) = reInner a b + reInner a c := by
  unfold reInner
  simp only [Complex.add_re, Complex.add_im]; ring

private lemma reInner_smul_left (r : ℝ) (a c : ℂ) :
    reInner ((r : ℝ) • a) c = r * reInner a c := by
  unfold reInner
  simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

private lemma reInner_self (z : ℂ) : reInner z z = ‖z‖^2 := by
  rw [reInner, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]

/-- **Inner-product positivity, right side**: for `t > t₀` close to `t₀`, with
right derivative limit `L ≠ 0`, the real inner product
`reInner (γ(t)-s) (γ'(t))` (which equals `(γ(t)-s).re·γ'(t).re + (γ(t)-s).im·γ'(t).im`)
is bounded below by `(t - t₀) · ‖L‖² / 2 > 0`.

This is the key positive-derivative bound: the derivative of `t ↦ ‖γ(t)-s‖²` is
`2·reInner(γ(t)-s, γ'(t))`, and the leading-order term is `(t-t₀)·‖L‖²`, which
dominates the `o(t-t₀)` corrections eventually. -/
private theorem reInner_lower_bound_right_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[>] t₀,
      (t - t₀) * ‖L‖^2 / 2 ≤ reInner (γ t - s) (deriv γ t) := by
  -- Build chord-tangent and deriv-tangent eventual bounds.
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hderiv : HasDerivWithinAt γ L (Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_iff_Ici.mpr
      (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hS_diff t ht).differentiableWithinAt)
        hγ_cont.continuousWithinAt hS_mem hL_right)
  have hr := hasDerivWithinAt_iff_isLittleO.mp hderiv
  -- Choose tolerance η = ‖L‖/8 so 2η‖L‖ + η² = ‖L‖²/4 + ‖L‖²/64 < ‖L‖²/2.
  set η : ℝ := ‖L‖ / 8 with hη_def
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  -- Eventually `‖γ(t) - γ(t₀) - (t - t₀) • L‖ ≤ η · |t - t₀|`.
  have h_chord := hr.def hη_pos
  -- Eventually `deriv γ t` is η-close to L.
  have h_deriv_close : ∀ᶠ t in 𝓝[>] t₀, ‖deriv γ t - L‖ < η := by
    have := (Metric.tendsto_nhds.mp hL_right) η hη_pos
    filter_upwards [this] with t ht
    rw [dist_eq_norm] at ht; exact ht
  filter_upwards [h_chord, h_deriv_close, self_mem_nhdsWithin] with
    t h_chord_t h_dclose_t h_t_gt
  have h_t_pos : 0 < t - t₀ := sub_pos.mpr h_t_gt
  -- Decompose: γ(t) - s = (t-t₀) • L + R, deriv γ t = L + D.
  set R : ℂ := γ t - γ t₀ - (t - t₀) • L with hR_def
  set D : ℂ := deriv γ t - L with hD_def
  have hR_norm : ‖R‖ ≤ η * (t - t₀) := by
    rw [Real.norm_eq_abs, abs_of_pos h_t_pos] at h_chord_t
    exact h_chord_t
  have hD_norm : ‖D‖ ≤ η := le_of_lt h_dclose_t
  have h_gamma_decomp : γ t - s = (t - t₀) • L + R := by
    rw [hR_def, h_at]; ring
  have h_deriv_decomp : deriv γ t = L + D := by
    rw [hD_def]; ring
  -- Expand reInner via bilinearity:
  -- reInner (γ t - s) (deriv γ t) = reInner ((t-t₀)•L + R) (L + D)
  --   = reInner ((t-t₀)•L) L + reInner ((t-t₀)•L) D + reInner R L + reInner R D
  --   = (t-t₀)·‖L‖² + (t-t₀)·reInner L D + reInner R L + reInner R D.
  rw [h_gamma_decomp, h_deriv_decomp]
  rw [reInner_add_left, reInner_add_right, reInner_add_right]
  rw [reInner_smul_left, reInner_smul_left, reInner_self]
  -- Goal: (t-t₀)*‖L‖²/2 ≤ (t-t₀)*‖L‖² + ((t-t₀)*reInner L D + (reInner R L + reInner R D))
  -- Bound errors:
  have h_err_LD : |reInner L D| ≤ ‖L‖ * η := by
    refine le_trans (reInner_le_norm_mul_norm L D) ?_
    exact mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _)
  have h_err_RL : |reInner R L| ≤ η * (t - t₀) * ‖L‖ := by
    refine le_trans (reInner_le_norm_mul_norm R L) ?_
    exact mul_le_mul_of_nonneg_right hR_norm (norm_nonneg _)
  have h_err_RD : |reInner R D| ≤ η * (t - t₀) * η := by
    refine le_trans (reInner_le_norm_mul_norm R D) ?_
    exact mul_le_mul hR_norm hD_norm (norm_nonneg _) (by positivity)
  -- Sign-flipped versions for linarith:
  have h_LD_lower : -(‖L‖ * η) ≤ reInner L D := neg_le_of_abs_le h_err_LD
  have h_RL_lower : -(η * (t - t₀) * ‖L‖) ≤ reInner R L := neg_le_of_abs_le h_err_RL
  have h_RD_lower : -(η * (t - t₀) * η) ≤ reInner R D := neg_le_of_abs_le h_err_RD
  -- For η = ‖L‖/8: 2η‖L‖ + η² = ‖L‖²/4 + ‖L‖²/64 < ‖L‖²/2.
  have h_eta_bound : 2 * η * ‖L‖ + η^2 ≤ ‖L‖^2 / 2 := by
    rw [hη_def]; nlinarith [hL_pos]
  -- Multiply h_LD_lower by (t-t₀) ≥ 0:
  have h_t_LD : -((t - t₀) * (‖L‖ * η)) ≤ (t - t₀) * reInner L D := by
    have := mul_le_mul_of_nonneg_left h_LD_lower h_t_pos.le
    linarith [this, show (t - t₀) * -(‖L‖ * η) = -((t - t₀) * (‖L‖ * η)) from by ring]
  -- Combine bounds. Total error lower bound:
  -- (t-t₀)*reInner L D + reInner R L + reInner R D
  --   ≥ -(t-t₀)*‖L‖*η - η*(t-t₀)*‖L‖ - η*(t-t₀)*η = -(t-t₀)*(2η‖L‖ + η²).
  -- Need this ≥ -(t-t₀)*‖L‖²/2.
  have h_combined :
      -((t - t₀) * (2 * η * ‖L‖ + η^2))
        ≤ (t - t₀) * reInner L D + (reInner R L + reInner R D) := by
    have h1 : -((t - t₀) * (2 * η * ‖L‖ + η^2)) =
        -((t - t₀) * (‖L‖ * η)) + (-(η * (t - t₀) * ‖L‖) + -(η * (t - t₀) * η)) := by
      ring
    rw [h1]
    linarith
  have h_err_le : -((t - t₀) * (‖L‖^2 / 2))
      ≤ (t - t₀) * reInner L D + (reInner R L + reInner R D) := by
    refine le_trans ?_ h_combined
    have h_le : (t - t₀) * (2 * η * ‖L‖ + η^2) ≤ (t - t₀) * (‖L‖^2 / 2) :=
      mul_le_mul_of_nonneg_left h_eta_bound h_t_pos.le
    linarith
  linarith

/-- **Equivalence of `reInner` with the real-valued inner product on `ℂ`**:
the bare `reInner z w = z.re * w.re + z.im * w.im` equals `⟪w, z⟫_ℝ` when `ℂ`
is viewed as a real inner-product space via `RCLike.toInnerProductSpaceReal`. -/
private lemma reInner_eq_inner_real (z w : ℂ) :
    reInner z w = inner ℝ w z := by
  change z.re * w.re + z.im * w.im = (Inner.rclikeToReal ℂ ℂ).inner w z
  rw [Inner.rclikeToReal]
  change z.re * w.re + z.im * w.im = (z * (starRingEnd ℂ) w).re
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

/-- **Strict monotonicity right side**: for some `r > 0`, the function
`t ↦ ‖γ(t) - s‖` is strictly monotone-increasing on `[t₀, t₀+r]`.

This is the key one-sided strict-monotonicity property used to define the
exit-time cutoff `δ(ε)` via IVT. -/
theorem norm_sub_strictMonoOn_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + r)) := by
  -- Get a right interval where positive-deriv bound and differentiability hold.
  have h_pos := reInner_lower_bound_right_eventually h_at hL hL_right hγ_cont hγ_diff
  have h_combined : ∀ᶠ t in 𝓝[>] t₀,
      DifferentiableAt ℝ γ t ∧
      (t - t₀) * ‖L‖^2 / 2 ≤ reInner (γ t - s) (deriv γ t) := by
    filter_upwards [hγ_diff, h_pos] with t h1 h2
    exact ⟨h1, h2⟩
  -- Extract `r > 0` with the bounds holding on `(t₀, t₀+r)`.
  rw [eventually_nhdsWithin_iff] at h_combined
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.eventually_nhds_iff_ball.mp h_combined
  -- We use `r := r₀ / 2` so endpoint `t₀ + r` is also strictly inside the open ball.
  set r := r₀ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_lt : r < r₀ := by rw [hr_def]; linarith
  have hr_data : ∀ t ∈ Ioc t₀ (t₀ + r),
      DifferentiableAt ℝ γ t ∧
      (t - t₀) * ‖L‖^2 / 2 ≤ reInner (γ t - s) (deriv γ t) := by
    intro t ht
    have h_t_in_ball : t ∈ Metric.ball t₀ r₀ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2]
    exact hr₀_sub t h_t_in_ball ht.1
  refine ⟨r, hr_pos, ?_⟩
  -- Squared-norm strict mono ⟹ norm strict mono.
  set f : ℝ → ℝ := fun t => ‖γ t - s‖^2 with hf_def
  -- Continuity of γ on Icc.
  have h_γ_continuousOn : ContinuousOn γ (Icc t₀ (t₀ + r)) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h_eq | h_gt
    · rw [← h_eq]; exact hγ_cont.continuousWithinAt
    · -- t > t₀, so t ∈ Ioc t₀ (t₀+r), giving differentiability and continuity.
      have h_in_Ioc : t ∈ Ioc t₀ (t₀ + r) := ⟨h_gt, ht.2⟩
      exact (hr_data t h_in_Ioc).1.continuousAt.continuousWithinAt
  -- f continuous on Icc
  have h_f_cont : ContinuousOn f (Icc t₀ (t₀ + r)) := by
    intro t ht
    have hγt := h_γ_continuousOn t ht
    exact ((hγt.sub continuousWithinAt_const).norm).pow 2
  -- Interior of Icc t₀ (t₀+r) is Ioo t₀ (t₀+r) (since t₀ < t₀+r).
  have h_int : interior (Icc t₀ (t₀ + r)) = Ioo t₀ (t₀ + r) := by
    rw [interior_Icc]
  have h_f_strictMono : StrictMonoOn f (Icc t₀ (t₀ + r)) := by
    apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _)
      (f' := fun t => 2 * reInner (γ t - s) (deriv γ t))
      h_f_cont
    · intro t ht
      rw [h_int] at ht
      have h_in_Ioc : t ∈ Ioc t₀ (t₀ + r) := ⟨ht.1, le_of_lt ht.2⟩
      have h_diff : DifferentiableAt ℝ γ t := (hr_data t h_in_Ioc).1
      -- HasDerivAt for ‖γ(·) - s‖² with derivative 2 * ⟪γ(t) - s, γ'(t)⟫_ℝ.
      have h_d_sub : HasDerivAt (fun u => γ u - s) (deriv γ t) t :=
        h_diff.hasDerivAt.sub_const s
      have h_d_normSq := h_d_sub.norm_sq
      have h_re_eq : (2 : ℝ) * inner ℝ (γ t - s) (deriv γ t) =
          2 * reInner (γ t - s) (deriv γ t) := by
        rw [reInner_eq_inner_real, real_inner_comm]
      rw [h_re_eq] at h_d_normSq
      exact h_d_normSq.hasDerivWithinAt
    · intro t ht
      rw [h_int] at ht
      have h_in_Ioc : t ∈ Ioc t₀ (t₀ + r) := ⟨ht.1, le_of_lt ht.2⟩
      have h_pos_inner : 0 < (t - t₀) * ‖L‖^2 / 2 := by
        have h_t_pos : 0 < t - t₀ := sub_pos.mpr ht.1
        have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
        positivity
      linarith [(hr_data t h_in_Ioc).2]
  -- Reduce: ‖γ(·) - s‖² strict mono ⟹ ‖γ(·) - s‖ strict mono (both nonneg).
  intro a ha b hb hab
  have h_sq_lt : ‖γ a - s‖^2 < ‖γ b - s‖^2 := h_f_strictMono ha hb hab
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h_sq_lt

/-- **Inner-product upper bound, left side**: for `t < t₀` close to `t₀`, with
left derivative limit `L ≠ 0`, `reInner (γ(t) - s) (γ'(t)) ≤ (t - t₀) · ‖L‖² / 2 < 0`.

The leading-order term is `(t - t₀) · ‖L‖²` which is negative since `t < t₀`. -/
private theorem reInner_upper_bound_left_eventually
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∀ᶠ t in 𝓝[<] t₀,
      reInner (γ t - s) (deriv γ t) ≤ (t - t₀) * ‖L‖^2 / 2 := by
  obtain ⟨S, hS_mem, hS_diff⟩ := hγ_diff.exists_mem
  have hderiv : HasDerivWithinAt γ L (Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_iff_Iic.mpr
      (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hS_diff t ht).differentiableWithinAt)
        hγ_cont.continuousWithinAt hS_mem hL_left)
  have hr := hasDerivWithinAt_iff_isLittleO.mp hderiv
  set η : ℝ := ‖L‖ / 8 with hη_def
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have h_chord := hr.def hη_pos
  have h_deriv_close : ∀ᶠ t in 𝓝[<] t₀, ‖deriv γ t - L‖ < η := by
    have := (Metric.tendsto_nhds.mp hL_left) η hη_pos
    filter_upwards [this] with t ht
    rw [dist_eq_norm] at ht; exact ht
  filter_upwards [h_chord, h_deriv_close, self_mem_nhdsWithin] with
    t h_chord_t h_dclose_t h_t_lt
  have h_t_neg : t - t₀ < 0 := sub_neg_of_lt h_t_lt
  have h_t₀t_pos : 0 < t₀ - t := sub_pos.mpr h_t_lt
  set R : ℂ := γ t - γ t₀ - (t - t₀) • L with hR_def
  set D : ℂ := deriv γ t - L with hD_def
  have hR_norm : ‖R‖ ≤ η * (t₀ - t) := by
    rw [Real.norm_eq_abs, abs_sub_comm, abs_of_pos h_t₀t_pos] at h_chord_t
    exact h_chord_t
  have hD_norm : ‖D‖ ≤ η := le_of_lt h_dclose_t
  have h_gamma_decomp : γ t - s = (t - t₀) • L + R := by
    rw [hR_def, h_at]; ring
  have h_deriv_decomp : deriv γ t = L + D := by rw [hD_def]; ring
  rw [h_gamma_decomp, h_deriv_decomp]
  rw [reInner_add_left, reInner_add_right, reInner_add_right]
  rw [reInner_smul_left, reInner_smul_left, reInner_self]
  -- Goal: (t-t₀)*‖L‖² + ((t-t₀)*reInner L D + (reInner R L + reInner R D)) ≤ (t-t₀)*‖L‖²/2.
  -- Equivalent: (t-t₀)*reInner L D + reInner R L + reInner R D ≤ (t₀-t)*‖L‖²/2.
  -- Strategy: sum of |error terms| ≤ (t₀-t)·(2η‖L‖ + η²) ≤ (t₀-t)·‖L‖²/2.
  have h_err_LD : |reInner L D| ≤ ‖L‖ * η := by
    refine le_trans (reInner_le_norm_mul_norm L D) ?_
    exact mul_le_mul_of_nonneg_left hD_norm (norm_nonneg _)
  have h_err_RL : |reInner R L| ≤ η * (t₀ - t) * ‖L‖ := by
    refine le_trans (reInner_le_norm_mul_norm R L) ?_
    exact mul_le_mul_of_nonneg_right hR_norm (norm_nonneg _)
  have h_err_RD : |reInner R D| ≤ η * (t₀ - t) * η := by
    refine le_trans (reInner_le_norm_mul_norm R D) ?_
    exact mul_le_mul hR_norm hD_norm (norm_nonneg _) (by positivity)
  -- Bound (t-t₀)*reInner L D in absolute value: |(t-t₀)| = t₀-t.
  have h_t_LD_abs : |(t - t₀) * reInner L D| ≤ (t₀ - t) * (‖L‖ * η) := by
    rw [abs_mul, abs_sub_comm, abs_of_pos h_t₀t_pos]
    exact mul_le_mul_of_nonneg_left h_err_LD h_t₀t_pos.le
  have h_RL_upper : reInner R L ≤ η * (t₀ - t) * ‖L‖ := le_of_abs_le h_err_RL
  have h_RD_upper : reInner R D ≤ η * (t₀ - t) * η := le_of_abs_le h_err_RD
  have h_t_LD_upper : (t - t₀) * reInner L D ≤ (t₀ - t) * (‖L‖ * η) :=
    le_of_abs_le h_t_LD_abs
  have h_eta_bound : 2 * η * ‖L‖ + η^2 ≤ ‖L‖^2 / 2 := by
    rw [hη_def]; nlinarith [hL_pos]
  -- Sum of upper bounds: (t₀-t)·(‖L‖·η + η·‖L‖ + η·η) = (t₀-t)·(2η‖L‖ + η²)
  --                   ≤ (t₀-t)·‖L‖²/2.
  have h_sum_le : (t - t₀) * reInner L D + (reInner R L + reInner R D)
        ≤ (t₀ - t) * (2 * η * ‖L‖ + η^2) := by
    have h1 : (t₀ - t) * (‖L‖ * η) + (η * (t₀ - t) * ‖L‖ + η * (t₀ - t) * η)
        = (t₀ - t) * (2 * η * ‖L‖ + η^2) := by ring
    linarith
  have h_le_main : (t₀ - t) * (2 * η * ‖L‖ + η^2) ≤ (t₀ - t) * (‖L‖^2 / 2) :=
    mul_le_mul_of_nonneg_left h_eta_bound h_t₀t_pos.le
  have h_neg_eq : (t₀ - t) * (‖L‖^2 / 2) = -((t - t₀) * (‖L‖^2 / 2)) := by ring
  linarith

/-- **Strict ANTI-monotonicity left side**: for some `r > 0`, the function
`t ↦ ‖γ(t) - s‖` is strictly anti-monotone (decreasing) on `[t₀ - r, t₀]`.

Symmetric to `norm_sub_strictMonoOn_right`. -/
theorem norm_sub_strictAntiOn_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} (h_at : γ t₀ = s)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    ∃ r > 0, StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - r) t₀) := by
  have h_neg := reInner_upper_bound_left_eventually h_at hL hL_left hγ_cont hγ_diff
  have h_combined : ∀ᶠ t in 𝓝[<] t₀,
      DifferentiableAt ℝ γ t ∧
      reInner (γ t - s) (deriv γ t) ≤ (t - t₀) * ‖L‖^2 / 2 := by
    filter_upwards [hγ_diff, h_neg] with t h1 h2
    exact ⟨h1, h2⟩
  rw [eventually_nhdsWithin_iff] at h_combined
  obtain ⟨r₀, hr₀_pos, hr₀_sub⟩ := Metric.eventually_nhds_iff_ball.mp h_combined
  set r := r₀ / 2 with hr_def
  have hr_pos : 0 < r := by rw [hr_def]; linarith
  have hr_lt : r < r₀ := by rw [hr_def]; linarith
  have hr_data : ∀ t ∈ Ico (t₀ - r) t₀,
      DifferentiableAt ℝ γ t ∧
      reInner (γ t - s) (deriv γ t) ≤ (t - t₀) * ‖L‖^2 / 2 := by
    intro t ht
    have h_t_in_ball : t ∈ Metric.ball t₀ r₀ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm,
        abs_of_pos (sub_pos.mpr ht.2)]
      linarith [ht.1]
    exact hr₀_sub t h_t_in_ball ht.2
  refine ⟨r, hr_pos, ?_⟩
  set f : ℝ → ℝ := fun t => ‖γ t - s‖^2 with hf_def
  have h_γ_continuousOn : ContinuousOn γ (Icc (t₀ - r) t₀) := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with h_eq | h_lt
    · rw [h_eq]; exact hγ_cont.continuousWithinAt
    · have h_in_Ico : t ∈ Ico (t₀ - r) t₀ := ⟨ht.1, h_lt⟩
      exact (hr_data t h_in_Ico).1.continuousAt.continuousWithinAt
  have h_f_cont : ContinuousOn f (Icc (t₀ - r) t₀) := by
    intro t ht
    have hγt := h_γ_continuousOn t ht
    exact ((hγt.sub continuousWithinAt_const).norm).pow 2
  have h_int : interior (Icc (t₀ - r) t₀) = Ioo (t₀ - r) t₀ := by
    rw [interior_Icc]
  have h_f_strictAnti : StrictAntiOn f (Icc (t₀ - r) t₀) := by
    apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc _ _)
      (f' := fun t => 2 * reInner (γ t - s) (deriv γ t))
      h_f_cont
    · intro t ht
      rw [h_int] at ht
      have h_in_Ico : t ∈ Ico (t₀ - r) t₀ := ⟨le_of_lt ht.1, ht.2⟩
      have h_diff : DifferentiableAt ℝ γ t := (hr_data t h_in_Ico).1
      have h_d_sub : HasDerivAt (fun u => γ u - s) (deriv γ t) t :=
        h_diff.hasDerivAt.sub_const s
      have h_d_normSq := h_d_sub.norm_sq
      have h_re_eq : (2 : ℝ) * inner ℝ (γ t - s) (deriv γ t) =
          2 * reInner (γ t - s) (deriv γ t) := by
        rw [reInner_eq_inner_real, real_inner_comm]
      rw [h_re_eq] at h_d_normSq
      exact h_d_normSq.hasDerivWithinAt
    · intro t ht
      rw [h_int] at ht
      have h_in_Ico : t ∈ Ico (t₀ - r) t₀ := ⟨le_of_lt ht.1, ht.2⟩
      have h_neg_inner : (t - t₀) * ‖L‖^2 / 2 < 0 := by
        have h_t_neg : t - t₀ < 0 := sub_neg_of_lt ht.2
        have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
        have : ‖L‖^2 > 0 := by positivity
        nlinarith
      linarith [(hr_data t h_in_Ico).2]
  -- Reduce: ‖γ(·) - s‖² strict anti ⟹ ‖γ(·) - s‖ strict anti.
  intro a ha b hb hab
  have h_sq_lt : ‖γ b - s‖^2 < ‖γ a - s‖^2 := h_f_strictAnti ha hb hab
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h_sq_lt

/-! ### IVT exit-time inversion (T-BR-Y3b)

Given strict monotonicity of `f` on `[0, r]` with `f 0 = 0` and continuity, the
intermediate value theorem produces, for each `ε ∈ (0, f r)`, a unique
`τ ∈ (0, r)` with `f τ = ε`. This is the inverse function defining the
exit-time cutoff `δ(ε)` from the level set `‖γ(t) - s‖ = ε`. -/

/-- **IVT exit-time inversion**: a strictly monotone continuous function with
`f 0 = 0` admits a unique preimage `τ ∈ (0, r)` for every `ε ∈ (0, f r)`. -/
private theorem strict_mono_inverse_exists
    (f : ℝ → ℝ) {r : ℝ} (hr : 0 < r) (hf₀ : f 0 = 0)
    (hf_strict : StrictMonoOn f (Icc 0 r))
    (hf_cont : ContinuousOn f (Icc 0 r)) :
    ∀ ε ∈ Ioo (0 : ℝ) (f r),
      ∃! τ : ℝ, τ ∈ Ioo (0 : ℝ) r ∧ f τ = ε := by
  intro ε hε
  -- Existence: IVT gives τ ∈ Ioo 0 r with f τ = ε.
  have h_image : Ioo (f 0) (f r) ⊆ f '' Ioo 0 r :=
    intermediate_value_Ioo hr.le hf_cont
  have hε_in : ε ∈ Ioo (f 0) (f r) := by
    rw [hf₀]; exact hε
  obtain ⟨τ, hτ_mem, hfτ⟩ := h_image hε_in
  refine ⟨τ, ⟨hτ_mem, hfτ⟩, ?_⟩
  rintro τ' ⟨hτ'_mem, hfτ'⟩
  -- Uniqueness: StrictMonoOn implies InjOn.
  exact hf_strict.injOn (Ioo_subset_Icc_self hτ'_mem)
    (Ioo_subset_Icc_self hτ_mem) (hfτ'.trans hfτ.symm)

/-! ### Geometric scaffolding bundle (T-BR-Y3b)

This bundles the derived geometric output `(δ_left, δ_right, threshold, ...,
h_far_*, h_near_*)` from immersion data into a single structure. The user of
the asymmetric framework can extract individual fields if they need to
construct the analytic content (`AsymmetricArcFTCHyp`) themselves; alternatively
the `AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived` constructor
below packages everything (including the user-supplied analytic content) into
the full structure. -/

/-- Bundled geometric scaffolding: cutoffs and far/near bounds derived from
immersion data (`γ, t₀, h_at, h_unique, h_flat`). -/
structure DerivedAsymmetricCutoffs {x : ℂ} (γ : ClosedPwC1Immersion x) (s : ℂ)
    (t₀ : ℝ) where
  /-- Left cutoff function. -/
  δ_left : ℝ → ℝ
  /-- Right cutoff function. -/
  δ_right : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  hδ_left_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε
  hδ_right_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε
  hδ_left_small : ∀ ε, 0 < ε → ε < threshold → δ_left ε < t₀
  hδ_right_small : ∀ ε, 0 < ε → ε < threshold → δ_right ε < 1 - t₀
  h_far_left : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc (0 : ℝ) 1, t ≤ t₀ → δ_left ε < t₀ - t →
      ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_far_right : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc (0 : ℝ) 1, t₀ ≤ t → δ_right ε < t - t₀ →
      ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖
  h_near_left : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, t ≤ t₀ → t₀ - t ≤ δ_left ε →
      ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε
  h_near_right : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, t₀ ≤ t → t - t₀ ≤ δ_right ε →
      ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε

/-- **Derive geometric scaffolding (right side).** From the strict monotonicity
of `‖γ(t) - s‖` on a right neighborhood and the compact far bound from
uniqueness, produce a right cutoff function `δ_right : ℝ → ℝ` with positive
threshold satisfying the `h_far_right` and `h_near_right` axioms. -/
private theorem exists_right_cutoff
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_right : ℝ → ℝ) (threshold : ℝ), 0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_right ε < 1 - t₀) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ∀ t ∈ Icc (0 : ℝ) 1, t₀ ≤ t → δ_right ε < t - t₀ →
          ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ∀ t, t₀ ≤ t → t - t₀ ≤ δ_right ε →
          ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  -- Establish smoothness ingredients at t₀: continuity, differentiability,
  -- and a nonzero right derivative limit.
  obtain ⟨L, hL_ne, hL_right⟩ := exists_right_deriv_limit γ ht₀_Ioo
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  have hγf_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_right γ ht₀_Ioo
  -- Strict monotonicity on `[t₀, t₀ + r₀]`.
  obtain ⟨r₀, hr₀_pos, hmono⟩ :=
    norm_sub_strictMonoOn_right h_at hL_ne hL_right hγf_cont hγf_diff
  -- Shrink r so r ≤ min t₀ (1 - t₀) (so [t₀+r, 1] and [0, t₀-r] both fit).
  set r : ℝ := min r₀ (min ((1 - t₀) / 2) (t₀ / 2)) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    refine lt_min hr₀_pos (lt_min ?_ ?_)
    · linarith [ht₀_Ioo.2]
    · linarith [ht₀_Ioo.1]
  have hr_le_r₀ : r ≤ r₀ := by rw [hr_def]; exact min_le_left _ _
  have hr_le_half : r ≤ (1 - t₀) / 2 := by
    rw [hr_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hr_le_t₀_half : r ≤ t₀ / 2 := by
    rw [hr_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hr_lt_one_sub : r < 1 - t₀ := by linarith [ht₀_Ioo.2]
  have hr_le_t₀ : r ≤ t₀ := by linarith [ht₀_Ioo.1]
  have hmono_r : StrictMonoOn (fun t => ‖γf t - s‖) (Icc t₀ (t₀ + r)) :=
    hmono.mono (Icc_subset_Icc le_rfl (by linarith))
  -- Define f(τ) := ‖γf (t₀ + τ) - s‖ on [0, r].
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ + τ) - s‖ with hf_def
  have hγ_cont_all : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have hf₀ : f 0 = 0 := by
    change ‖γf (t₀ + 0) - s‖ = 0
    rw [add_zero, show γf t₀ = s from h_at, sub_self, norm_zero]
  have hf_cont : ContinuousOn f (Icc 0 r) :=
    (((hγ_cont_all.comp (continuous_const.add continuous_id)).sub
      continuous_const).norm).continuousOn
  have hf_strict : StrictMonoOn f (Icc 0 r) := fun a ha b hb hab =>
    hmono_r ⟨by linarith [ha.1], by linarith [ha.2]⟩
      ⟨by linarith [hb.1], by linarith [hb.2]⟩ (by linarith)
  have hf_r_pos : 0 < f r :=
    hf₀ ▸ hf_strict (left_mem_Icc.mpr hr_pos.le) (right_mem_Icc.mpr hr_pos.le) hr_pos
  -- Compact far bound on the right portion [t₀ + r, 1].
  obtain ⟨m, hm_pos, _, h_right_far⟩ := exists_far_bound_compact γf hγ_cont_all s t₀
    h_unique hr_pos hr_le_t₀ (le_of_lt hr_lt_one_sub)
  set threshold : ℝ := min (f r) m with hthresh_def
  have hthresh_pos : 0 < threshold := lt_min hf_r_pos hm_pos
  have hthresh_le_fr : threshold ≤ f r := by rw [hthresh_def]; exact min_le_left _ _
  have hthresh_le_m : threshold ≤ m := by rw [hthresh_def]; exact min_le_right _ _
  -- Define δ_right via Classical.choose on strict_mono_inverse_exists.
  set δ_right : ℝ → ℝ := fun ε =>
    if h : ε ∈ Ioo (0 : ℝ) (f r) then
      (strict_mono_inverse_exists f hr_pos hf₀ hf_strict hf_cont ε h).choose
    else r / 2 with hδ_def
  -- Properties of δ_right when ε ∈ Ioo 0 (f r).
  have hδ_spec : ∀ ε, 0 < ε → ε < f r →
      δ_right ε ∈ Ioo (0 : ℝ) r ∧ f (δ_right ε) = ε := by
    intro ε hε_pos hε_lt
    have hε_in : ε ∈ Ioo (0 : ℝ) (f r) := ⟨hε_pos, hε_lt⟩
    simp only [hδ_def, dif_pos hε_in]
    exact
      (strict_mono_inverse_exists f hr_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
  refine ⟨δ_right, threshold, hthresh_pos, ?_, ?_, ?_, ?_⟩
  · -- hδ_right_pos
    intro ε hε_pos hε_lt
    exact (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1.1
  · -- hδ_right_small : δ_right ε < 1 - t₀
    intro ε hε_pos hε_lt
    have h_in_Ioo := (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1
    linarith [h_in_Ioo.2]
  · -- h_far_right
    intro ε hε_pos hε_lt t ht_Icc ht_ge hgap
    have hε_lt_fr : ε < f r := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    by_cases ht_le_r : t ≤ t₀ + r
    · -- Use strict monotonicity: t - t₀ > δ_right ε ⟹ f (t - t₀) > f (δ_right ε) = ε.
      have ht_τ_mem : t - t₀ ∈ Icc (0 : ℝ) r := ⟨by linarith, by linarith⟩
      have hδ_τ_mem : δ_right ε ∈ Icc (0 : ℝ) r :=
        ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
      have h_lt : f (δ_right ε) < f (t - t₀) := hf_strict hδ_τ_mem ht_τ_mem hgap
      rw [hfδ] at h_lt
      have h_eq : f (t - t₀) = ‖γf t - s‖ := by
        change ‖γf (t₀ + (t - t₀)) - s‖ = ‖γf t - s‖
        rw [show t₀ + (t - t₀) = t from by ring]
      rwa [h_eq] at h_lt
    · -- t > t₀ + r: use the compact far bound.
      push Not at ht_le_r
      have hε_lt_m : ε < m := lt_of_lt_of_le hε_lt hthresh_le_m
      have h_ge_m : m ≤ ‖γf t - s‖ := h_right_far t ⟨le_of_lt ht_le_r, ht_Icc.2⟩
      linarith
  · -- h_near_right
    intro ε hε_pos hε_lt t ht_ge hgap
    have hε_lt_fr : ε < f r := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    have ht_τ_mem : t - t₀ ∈ Icc (0 : ℝ) r := by
      refine ⟨by linarith, ?_⟩
      linarith [hδ_in.2]
    have hδ_τ_mem : δ_right ε ∈ Icc (0 : ℝ) r :=
      ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
    by_cases h_t_eq : t = t₀
    · rw [h_t_eq, h_at, sub_self, norm_zero]
      exact le_of_lt hε_pos
    · have ht_τ_pos : (0 : ℝ) < t - t₀ := by
        cases lt_or_eq_of_le ht_ge with
        | inl h => linarith
        | inr h => exact absurd h.symm h_t_eq
      have h_le : f (t - t₀) ≤ f (δ_right ε) := by
        cases lt_or_eq_of_le hgap with
        | inl h_lt =>
          exact le_of_lt (hf_strict ht_τ_mem hδ_τ_mem h_lt)
        | inr h_eq =>
          have : t - t₀ = δ_right ε := h_eq
          rw [this]
      rw [hfδ] at h_le
      have h_eq : f (t - t₀) = ‖γf t - s‖ := by
        change ‖γf (t₀ + (t - t₀)) - s‖ = ‖γf t - s‖
        rw [show t₀ + (t - t₀) = t from by ring]
      rwa [h_eq] at h_le

/-- **Derive geometric scaffolding (left side).** Symmetric to
`exists_right_cutoff`. -/
private theorem exists_left_cutoff
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    ∃ (δ_left : ℝ → ℝ) (threshold : ℝ), 0 < threshold ∧
      (∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε) ∧
      (∀ ε, 0 < ε → ε < threshold → δ_left ε < t₀) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ∀ t ∈ Icc (0 : ℝ) 1, t ≤ t₀ → δ_left ε < t₀ - t →
          ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖) ∧
      (∀ ε, 0 < ε → ε < threshold →
        ∀ t, t ≤ t₀ → t₀ - t ≤ δ_left ε →
          ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  obtain ⟨L, hL_ne, hL_left⟩ := exists_left_deriv_limit γ ht₀_Ioo
  have hγf_cont : ContinuousAt γf t₀ :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousAt
  have hγf_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γf t :=
    eventually_differentiable_left γ ht₀_Ioo
  obtain ⟨r₀, hr₀_pos, hanti⟩ :=
    norm_sub_strictAntiOn_left h_at hL_ne hL_left hγf_cont hγf_diff
  set r : ℝ := min r₀ (min (t₀ / 2) ((1 - t₀) / 2)) with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    refine lt_min hr₀_pos (lt_min ?_ ?_)
    · linarith [ht₀_Ioo.1]
    · linarith [ht₀_Ioo.2]
  have hr_le_r₀ : r ≤ r₀ := by rw [hr_def]; exact min_le_left _ _
  have hr_le_t₀_half : r ≤ t₀ / 2 := by
    rw [hr_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hr_le_one_sub_half : r ≤ (1 - t₀) / 2 := by
    rw [hr_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hr_lt_t₀ : r < t₀ := by linarith [ht₀_Ioo.1]
  have hr_le_one_sub : r ≤ 1 - t₀ := by linarith [ht₀_Ioo.2]
  -- Anti-mono on `[t₀ - r, t₀]`.
  have hanti_r : StrictAntiOn (fun t => ‖γf t - s‖) (Icc (t₀ - r) t₀) :=
    hanti.mono (Icc_subset_Icc (by linarith) le_rfl)
  -- Define f(τ) := ‖γf (t₀ - τ) - s‖ on [0, r]; this is STRICTLY MONOTONE (incr).
  set f : ℝ → ℝ := fun τ => ‖γf (t₀ - τ) - s‖ with hf_def
  have hγ_cont_all : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have hf₀ : f 0 = 0 := by
    change ‖γf (t₀ - 0) - s‖ = 0
    rw [sub_zero, show γf t₀ = s from h_at, sub_self, norm_zero]
  have hf_cont : ContinuousOn f (Icc 0 r) :=
    (((hγ_cont_all.comp (continuous_const.sub continuous_id)).sub
      continuous_const).norm).continuousOn
  have hf_strict : StrictMonoOn f (Icc 0 r) := fun a ha b hb hab =>
    hanti_r ⟨by linarith [hb.2], by linarith [hb.1]⟩
      ⟨by linarith [ha.2], by linarith [ha.1]⟩ (by linarith)
  have hf_r_pos : 0 < f r :=
    hf₀ ▸ hf_strict (left_mem_Icc.mpr hr_pos.le) (right_mem_Icc.mpr hr_pos.le) hr_pos
  -- Compact far bound on the left portion [0, t₀ - r].
  obtain ⟨m, hm_pos, h_left_far, _⟩ := exists_far_bound_compact γf hγ_cont_all s t₀
    h_unique hr_pos (le_of_lt hr_lt_t₀) hr_le_one_sub
  set threshold : ℝ := min (f r) m with hthresh_def
  have hthresh_pos : 0 < threshold := lt_min hf_r_pos hm_pos
  have hthresh_le_fr : threshold ≤ f r := by rw [hthresh_def]; exact min_le_left _ _
  have hthresh_le_m : threshold ≤ m := by rw [hthresh_def]; exact min_le_right _ _
  -- Define δ_left via Classical.choose.
  set δ_left : ℝ → ℝ := fun ε =>
    if h : ε ∈ Ioo (0 : ℝ) (f r) then
      (strict_mono_inverse_exists f hr_pos hf₀ hf_strict hf_cont ε h).choose
    else r / 2 with hδ_def
  have hδ_spec : ∀ ε, 0 < ε → ε < f r →
      δ_left ε ∈ Ioo (0 : ℝ) r ∧ f (δ_left ε) = ε := by
    intro ε hε_pos hε_lt
    have hε_in : ε ∈ Ioo (0 : ℝ) (f r) := ⟨hε_pos, hε_lt⟩
    simp only [hδ_def, dif_pos hε_in]
    exact
      (strict_mono_inverse_exists f hr_pos hf₀ hf_strict hf_cont ε hε_in).choose_spec.1
  refine ⟨δ_left, threshold, hthresh_pos, ?_, ?_, ?_, ?_⟩
  · intro ε hε_pos hε_lt
    exact (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1.1
  · intro ε hε_pos hε_lt
    have h_in_Ioo := (hδ_spec ε hε_pos (lt_of_lt_of_le hε_lt hthresh_le_fr)).1
    linarith [h_in_Ioo.2]
  · -- h_far_left
    intro ε hε_pos hε_lt t ht_Icc ht_le hgap
    have hε_lt_fr : ε < f r := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    by_cases ht_ge_neg : t₀ - r ≤ t
    · have ht_τ_mem : t₀ - t ∈ Icc (0 : ℝ) r := ⟨by linarith, by linarith⟩
      have hδ_τ_mem : δ_left ε ∈ Icc (0 : ℝ) r :=
        ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
      have h_lt : f (δ_left ε) < f (t₀ - t) := hf_strict hδ_τ_mem ht_τ_mem hgap
      rw [hfδ] at h_lt
      have h_eq : f (t₀ - t) = ‖γf t - s‖ := by
        change ‖γf (t₀ - (t₀ - t)) - s‖ = ‖γf t - s‖
        rw [show t₀ - (t₀ - t) = t from by ring]
      rwa [h_eq] at h_lt
    · push Not at ht_ge_neg
      have hε_lt_m : ε < m := lt_of_lt_of_le hε_lt hthresh_le_m
      have h_ge_m : m ≤ ‖γf t - s‖ := h_left_far t ⟨ht_Icc.1, le_of_lt ht_ge_neg⟩
      linarith
  · -- h_near_left
    intro ε hε_pos hε_lt t ht_le hgap
    have hε_lt_fr : ε < f r := lt_of_lt_of_le hε_lt hthresh_le_fr
    obtain ⟨hδ_in, hfδ⟩ := hδ_spec ε hε_pos hε_lt_fr
    have ht_τ_mem : t₀ - t ∈ Icc (0 : ℝ) r := by
      refine ⟨by linarith, ?_⟩
      linarith [hδ_in.2]
    have hδ_τ_mem : δ_left ε ∈ Icc (0 : ℝ) r :=
      ⟨le_of_lt hδ_in.1, le_of_lt hδ_in.2⟩
    by_cases h_t_eq : t = t₀
    · rw [h_t_eq, h_at, sub_self, norm_zero]
      exact le_of_lt hε_pos
    · have ht_τ_pos : (0 : ℝ) < t₀ - t := by
        cases lt_or_eq_of_le ht_le with
        | inl h => linarith
        | inr h => exact absurd h h_t_eq
      have h_le : f (t₀ - t) ≤ f (δ_left ε) := by
        cases lt_or_eq_of_le hgap with
        | inl h_lt =>
          exact le_of_lt (hf_strict ht_τ_mem hδ_τ_mem h_lt)
        | inr h_eq =>
          have : t₀ - t = δ_left ε := h_eq
          rw [this]
      rw [hfδ] at h_le
      have h_eq : f (t₀ - t) = ‖γf t - s‖ := by
        change ‖γf (t₀ - (t₀ - t)) - s‖ = ‖γf t - s‖
        rw [show t₀ - (t₀ - t) = t from by ring]
      rwa [h_eq] at h_le

/-- **Derive the full geometric scaffolding bundle** from immersion data —
**corner-friendly form**. This is the same as `deriveAsymmetricCutoffs` but
without the `h_part_off` hypothesis: the underlying `exists_right_cutoff` and
`exists_left_cutoff` lemmas only require one-sided derivative limits (which
exist for `PwC1Immersion` at any interior point, smooth OR corner). -/
noncomputable def deriveAsymmetricCutoffs_anywhere
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    DerivedAsymmetricCutoffs γ s t₀ :=
  let dR := exists_right_cutoff γ ht₀_Ioo h_at h_unique
  let dL := exists_left_cutoff γ ht₀_Ioo h_at h_unique
  let δR := dR.choose
  let dR' := dR.choose_spec
  let threshR := dR'.choose
  let dR_props := dR'.choose_spec
  let δL := dL.choose
  let dL' := dL.choose_spec
  let threshL := dL'.choose
  let dL_props := dL'.choose_spec
  { δ_left := δL
    δ_right := δR
    threshold := min threshR threshL
    hthresh := lt_min dR_props.1 dL_props.1
    hδ_left_pos := fun ε hε hεt =>
      dL_props.2.1 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    hδ_right_pos := fun ε hε hεt =>
      dR_props.2.1 ε hε (lt_of_lt_of_le hεt (min_le_left _ _))
    hδ_left_small := fun ε hε hεt =>
      dL_props.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    hδ_right_small := fun ε hε hεt =>
      dR_props.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_left _ _))
    h_far_left := fun ε hε hεt =>
      dL_props.2.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    h_far_right := fun ε hε hεt =>
      dR_props.2.2.2.1 ε hε (lt_of_lt_of_le hεt (min_le_left _ _))
    h_near_left := fun ε hε hεt =>
      dL_props.2.2.2.2 ε hε (lt_of_lt_of_le hεt (min_le_right _ _))
    h_near_right := fun ε hε hεt =>
      dR_props.2.2.2.2 ε hε (lt_of_lt_of_le hεt (min_le_left _ _)) }

/-- **Derive the full geometric scaffolding bundle** from immersion data. This
combines `exists_right_cutoff` and `exists_left_cutoff`, taking the minimum
threshold and packaging everything into the `DerivedAsymmetricCutoffs` bundle. -/
noncomputable def deriveAsymmetricCutoffs
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (_h_part_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) :
    DerivedAsymmetricCutoffs γ s t₀ :=
  deriveAsymmetricCutoffs_anywhere γ ht₀_Ioo h_at h_unique

/-- **Combine derived geometric cutoffs with analytic FTC content** to produce a
full `AsymmetricSingleCrossingData`. The geometric scaffolding
(`δ_left, δ_right, threshold`, far/near bounds, positivity, smallness) is taken
from the supplied `DerivedAsymmetricCutoffs` bundle; the analytic content
(`L, E, h_ftc, h_limit, hint_left, hint_right`) is supplied via the
`AsymmetricArcFTCHyp` referencing the same `δ_left, δ_right`. -/
def AsymmetricSingleCrossingData.ofDerivedCutoffs
    {x : ℂ} {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ : ℝ}
    (D : DerivedAsymmetricCutoffs γ s t₀)
    {L : ℂ}
    (ftcHyp : AsymmetricArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s t₀
      D.δ_left D.δ_right D.threshold L) :
    AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s where
  L := L
  t₀ := t₀
  ht₀ := by
    -- t₀ ∈ Ioo 0 1: derivable from hδ_left_small, hδ_right_small at ε = threshold/2.
    -- We don't have direct access to ht₀_Ioo here, but it's encoded in the bundle.
    -- Provide it via: pick any ε in (0, threshold), get δ_left ε < t₀ and δ_right ε < 1 - t₀.
    -- We need a concrete ε. Use threshold/2.
    have hε_pos : 0 < D.threshold / 2 := by linarith [D.hthresh]
    have hε_lt : D.threshold / 2 < D.threshold := by linarith [D.hthresh]
    have hδL_pos := D.hδ_left_pos (D.threshold / 2) hε_pos hε_lt
    have hδR_pos := D.hδ_right_pos (D.threshold / 2) hε_pos hε_lt
    have hδL_small := D.hδ_left_small (D.threshold / 2) hε_pos hε_lt
    have hδR_small := D.hδ_right_small (D.threshold / 2) hε_pos hε_lt
    refine ⟨?_, ?_⟩ <;> linarith
  δ_left := D.δ_left
  δ_right := D.δ_right
  threshold := D.threshold
  hthresh := D.hthresh
  hδ_left_pos := D.hδ_left_pos
  hδ_right_pos := D.hδ_right_pos
  hδ_left_small := D.hδ_left_small
  hδ_right_small := D.hδ_right_small
  h_far_left := D.h_far_left
  h_far_right := D.h_far_right
  h_near_left := D.h_near_left
  h_near_right := D.h_near_right
  E := ftcHyp.E
  h_ftc := ftcHyp.h_ftc
  hint_left := ftcHyp.hint_left
  hint_right := ftcHyp.hint_right
  h_limit := ftcHyp.h_limit

/-- **Generic asymmetric builder with derived geometric scaffolding** — Option α.

Takes a closed piecewise-`C¹` immersion `γ` crossing `s` at `t₀ ∈ Ioo 0 1`
uniquely, off-partition, plus the **analytic content** (`L, E, h_ftc, h_limit,
hint_left, hint_right`) expressed via `AsymmetricArcFTCHyp`. The geometric
scaffolding (`δ_left, δ_right`, threshold, far/near bounds) is **derived
automatically** from the immersion data via `deriveAsymmetricCutoffs`.

The user does not specify `δ_left, δ_right` explicitly; they are extracted from
the `DerivedAsymmetricCutoffs` bundle and accessible via the `D` argument when
constructing the FTC hypothesis. This is the residual oracle pattern: the
geometric content is fully discharged, but the user must still supply the
analytic FTC convergence (a single `HasCauchyPV`-equivalent statement).

This is the strongest constructor available without proving the full
analytic-content theorem (`Tendsto E (𝓝[>] 0) (𝓝 L)`), which requires a
substantial analysis chain (FTC for `Complex.log`, chord-to-tangent limits of
`arg`, and branch-cut analysis). Pending that work, this constructor reduces
the `h_geometry` oracle from a 14-field structure to a 5-field
`AsymmetricArcFTCHyp`. -/
noncomputable def AsymmetricSingleCrossingData.ofClosedImmersion_flat_one_derived
    {x : ℂ} (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (h_part_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    {L : ℂ}
    (mkFTCHyp : (D : DerivedAsymmetricCutoffs γ s t₀) →
      AsymmetricArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s t₀
        D.δ_left D.δ_right D.threshold L) :
    AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s :=
  let D := deriveAsymmetricCutoffs γ ht₀_Ioo h_at h_unique h_part_off
  AsymmetricSingleCrossingData.ofDerivedCutoffs D (mkFTCHyp D)

/-- **Generic `SingleCrossingData` builder from immersion + flatness + uniqueness.**

Given a closed piecewise-`C¹` immersion `γ` crossing the pole `s` at parameter
`t₀ ∈ Ioo 0 1` with `IsFlatOfOrder _ _ 1` and uniquely on `[0, 1]`, together
with a parameter-space cutoff `δ`, threshold, geometric bounds (h_far, h_near),
and the analytic FTC component `(L, ftcHyp)`, build the full
`SingleCrossingData`. Mirrors the FD-curve constructors `mkSingleCrossingData_atI`,
etc., for arbitrary closed pw-`C¹` immersions.

The supporting lemmas in this file (`exists_far_bound_compact`,
`chord_lower_bound_*_eventually`, `chord_upper_bound_*_eventually`,
`exists_*_deriv_limit`, `eventually_differentiable_*`) provide the
mathematical content needed to construct the geometric scaffold from the
immersion data. -/
def SingleCrossingData.ofClosedImmersion_flat_one
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (_h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (_h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1)
    (L : ℂ)
    (δ : ℝ → ℝ)
    (threshold : ℝ) (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, δ ε < |t - t₀| →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, |t - t₀| ≤ δ ε →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε)
    (ftcHyp : ArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s t₀ δ threshold L) :
    SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s where
  L := L
  t₀ := t₀
  ht₀ := ht₀_Ioo
  δ := δ
  threshold := threshold
  hthresh := hthresh
  hδ_pos := hδ_pos
  hδ_small := hδ_small
  h_far := h_far
  h_near := h_near
  E := ftcHyp.E
  h_ftc := ftcHyp.h_ftc
  hint_left := ftcHyp.hint_left
  hint_right := ftcHyp.hint_right
  h_limit := ftcHyp.h_limit

/-! ## T-BR-Y3 — generic asymmetric `AsymmetricSingleCrossingData` builder

The asymmetric form of `SingleCrossingData.ofClosedImmersion_flat_one`: takes the
same geometric inputs (immersion, crossing parameter, uniqueness, flatness)
but with **independent left/right cutoffs** `δ_left, δ_right : ℝ → ℝ` and
corresponding asymmetric far/near bounds. Each side is controlled independently,
admitting crossings where the chord-to-tangent constants `‖L_-‖, ‖L_+‖` on the
two sides differ — which the symmetric form cannot express. -/

/-- **Generic asymmetric builder.** Given a closed piecewise-`C¹` immersion `γ`
crossing the pole `s` at parameter `t₀ ∈ Ioo 0 1` with `IsFlatOfOrder _ _ 1`
and uniquely on `[0, 1]`, together with **independent left/right cutoffs**
`δ_left, δ_right`, asymmetric geometric bounds (`h_far_left, h_far_right,
h_near_left, h_near_right`) and the analytic FTC component
`AsymmetricArcFTCHyp`, build the full `AsymmetricSingleCrossingData`.

This is the asymmetric counterpart of
`SingleCrossingData.ofClosedImmersion_flat_one`: the immersion data
(`γ, ht₀_Ioo, h_at, h_unique, h_flat`) is recorded for the moral content but
not used in the proof body (the existing far/near bounds already encode the
geometric content). It is supplied for downstream use in `residueTheorem_crossing`,
which expects the asymmetric crossing data and uses the immersion data to
verify flatness and uniqueness independently. -/
def AsymmetricSingleCrossingData.ofClosedImmersion_flat_one
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (_h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (_h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (_h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1)
    (L : ℂ)
    (δ_left δ_right : ℝ → ℝ)
    (threshold : ℝ) (hthresh : 0 < threshold)
    (hδ_left_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_left ε)
    (hδ_right_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ_right ε)
    (hδ_left_small : ∀ ε, 0 < ε → ε < threshold → δ_left ε < t₀)
    (hδ_right_small : ∀ ε, 0 < ε → ε < threshold → δ_right ε < 1 - t₀)
    (h_far_left : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≤ t₀ → δ_left ε < t₀ - t →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖)
    (h_far_right : ∀ ε, 0 < ε → ε < threshold →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, t₀ ≤ t → δ_right ε < t - t₀ →
        ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖)
    (h_near_left : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, t ≤ t₀ → t₀ - t ≤ δ_left ε →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε)
    (h_near_right : ∀ ε, 0 < ε → ε < threshold →
      ∀ t, t₀ ≤ t → t - t₀ ≤ δ_right ε →
        ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s‖ ≤ ε)
    (ftcHyp : AsymmetricArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s t₀
      δ_left δ_right threshold L) :
    AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s :=
  AsymmetricSingleCrossingData.mk_from_bounds ht₀_Ioo hthresh
    hδ_left_pos hδ_right_pos hδ_left_small hδ_right_small
    h_far_left h_far_right h_near_left h_near_right ftcHyp

/-! ## T-BR-Y3c — `AsymmetricArcFTCHyp` from `HasCauchyPV`

The `AsymmetricArcFTCHyp` analytic oracle packs `(L, E, h_ftc, h_limit,
hint_left, hint_right)`. T-BR-Y3c shows this bundle can be derived from a
single `HasCauchyPV` hypothesis (plus the auto-derived geometric scaffolding
from T-BR-Y3b), eliminating the 5-field FTC oracle in favour of a single
CPV-existence statement.

The strategy:
* `E(ε) := outer-integral sum`. Then `h_ftc` is definitional (`rfl`).
* `hint_left, hint_right`: integrability of `(γ - s)⁻¹ * γ'` on segments away
  from the singularity follows from `(γ - s)⁻¹` being bounded/continuous
  (norm bounded below by some `m > 0`) and `γ'` being interval-integrable.
* `h_limit`: the cutoff integral equals `E(ε)` plus a vanishing middle piece.
  Since `HasCauchyPV` gives `cutoff_integral → L`, we get `E(ε) → L`. -/

/-- **Integrability of `(γ - s)⁻¹ * γ'` on segments away from the
singularity**. If `γ(t) ≠ s` on the closed interval `[a, b] ⊆ [0, 1]`, then
the integrand `(γ(t) - s)⁻¹ * γ'(t)` is interval-integrable on `[a, b]`.

The proof: `γ'` is interval-integrable on `[0, 1]` (hence on `[a, b]` by
restriction), and `(γ - s)⁻¹` is continuous on `[a, b]` (since `γ - s ≠ 0`
on the compact interval). Their product is interval-integrable. -/
theorem inv_sub_mul_deriv_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ}
    (hab : a ≤ b) (h_in_Icc : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1)
    (h_ne : ∀ t ∈ Set.Icc a b,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s) :
    IntervalIntegrable
      (fun t => (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
      MeasureTheory.volume a b := by
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  have hγ_int : IntervalIntegrable (deriv γf) MeasureTheory.volume a b :=
    γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable.mono_set <| by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]; exact h_in_Icc
  have h_cont : ContinuousOn (fun t => (γf t - s)⁻¹) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    refine (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.continuousOn.sub
      continuousOn_const).inv₀ fun t ht h_eq => h_ne t ht ?_
    linear_combination h_eq
  exact (hγ_int.mul_continuousOn h_cont).congr (fun t _ => by ring)

/-- **The integrand `(γ - s)⁻¹ * γ'` is interval-integrable on `[a, b]` when
`γ(t) ≠ s` on the closed interval and `0 ≤ a, b ≤ 1`.** Specialisation of
`inv_sub_mul_deriv_intervalIntegrable` for the typical case. -/
theorem inv_sub_mul_deriv_intervalIntegrable_left
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    {δ_left_ε : ℝ} (hδL_pos : 0 < δ_left_ε) (hδL_small : δ_left_ε < t₀)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    IntervalIntegrable
      (fun t => (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
      MeasureTheory.volume 0 (t₀ - δ_left_ε) := by
  have hab : (0 : ℝ) ≤ t₀ - δ_left_ε := by linarith
  have h_in_Icc : Set.Icc (0 : ℝ) (t₀ - δ_left_ε) ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.Icc_subset_Icc le_rfl (by linarith [ht₀_Ioo.2])
  refine inv_sub_mul_deriv_intervalIntegrable γ hab h_in_Icc fun t ht h_eq => ?_
  have h_t_eq : t = t₀ := h_unique t (h_in_Icc ht) h_eq
  linarith [ht.2, h_t_eq.symm ▸ ht.2]

/-- Symmetric to `inv_sub_mul_deriv_intervalIntegrable_left`. -/
theorem inv_sub_mul_deriv_intervalIntegrable_right
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    {δ_right_ε : ℝ} (hδR_pos : 0 < δ_right_ε) (hδR_small : δ_right_ε < 1 - t₀)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀) :
    IntervalIntegrable
      (fun t => (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
      MeasureTheory.volume (t₀ + δ_right_ε) 1 := by
  have hab : t₀ + δ_right_ε ≤ 1 := by linarith
  have h_in_Icc : Set.Icc (t₀ + δ_right_ε) (1 : ℝ) ⊆ Set.Icc (0 : ℝ) 1 :=
    Set.Icc_subset_Icc (by linarith [ht₀_Ioo.1]) le_rfl
  refine inv_sub_mul_deriv_intervalIntegrable γ hab h_in_Icc fun t ht h_eq => ?_
  have h_t_eq : t = t₀ := h_unique t (h_in_Icc ht) h_eq
  linarith [ht.1, h_t_eq.symm ▸ ht.1]

/-- **The cutoff integral equals the outer-integral sum** when the geometric
scaffolding holds and the integrand is integrable on the outer pieces. This
mirrors `AsymmetricSingleCrossingData.cutoff_integral_eq_E` but is stated for
the derived geometric scaffolding directly. -/
theorem cutoff_integral_eq_outer_sum
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (D : DerivedAsymmetricCutoffs γ s t₀)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) :
    ∫ t in (0 : ℝ)..1,
      cpvIntegrand (fun z => (z - s)⁻¹)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t =
    (∫ t in (0 : ℝ)..(t₀ - D.δ_left ε),
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
          deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) +
    (∫ t in (t₀ + D.δ_right ε)..1,
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
          deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) := by
  classical
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  have hδL_pos := D.hδ_left_pos ε hε_pos hε_lt
  have hδR_pos := D.hδ_right_pos ε hε_pos hε_lt
  have hδL_small := D.hδ_left_small ε hε_pos hε_lt
  have hδR_small := D.hδ_right_small ε hε_pos hε_lt
  have h_left_lt : (0 : ℝ) < t₀ - D.δ_left ε := by linarith
  have h_mid_lt : t₀ - D.δ_left ε < t₀ + D.δ_right ε := by linarith
  have h_right_lt : t₀ + D.δ_right ε < 1 := by linarith
  -- Define F := cpvIntegrand restricted to [0, 1].
  set F : ℝ → ℂ := fun t =>
    cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t with hF_def
  -- Helper: the integrand on each piece.
  set integrand : ℝ → ℂ := fun t => (γf t - s)⁻¹ * deriv γf t with hI_def
  -- Step 1: F = integrand a.e. on [0, t₀ - δ_left ε].
  have hF_left_ae : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc 0 (t₀ - D.δ_left ε) → F t = integrand t := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      ((Set.finite_singleton (t₀ - D.δ_left ε)).measure_zero MeasureTheory.volume)]
      with t ht_ne ht_mem
    rw [Set.uIoc_of_le h_left_lt.le] at ht_mem
    have ht_lt : t < t₀ - D.δ_left ε :=
      lt_of_le_of_ne ht_mem.2 fun h => ht_ne (Set.mem_singleton_iff.mpr h)
    simp only [hF_def, hI_def, cpvIntegrand]
    rw [if_pos]
    refine D.h_far_left ε hε_pos hε_lt t
      ⟨ht_mem.1.le, (by linarith [ht₀_Ioo.2] : t ≤ 1)⟩ (by linarith) (by linarith)
  -- Step 2: F = 0 on [t₀ - δ_left ε, t₀ + δ_right ε].
  have hF_mid : ∀ t ∈ Set.uIoc (t₀ - D.δ_left ε) (t₀ + D.δ_right ε), F t = 0 := by
    intro t ht
    rw [Set.uIoc_of_le (le_of_lt h_mid_lt)] at ht
    simp only [hF_def, cpvIntegrand]
    rw [if_neg (not_lt.mpr _)]
    by_cases h_t_le : t ≤ t₀
    · refine D.h_near_left ε hε_pos hε_lt t h_t_le ?_
      linarith [ht.1]
    · push Not at h_t_le
      refine D.h_near_right ε hε_pos hε_lt t (le_of_lt h_t_le) ?_
      linarith [ht.2]
  -- Step 3: F = integrand a.e. on [t₀ + δ_right ε, 1].
  have hF_right_ae : ∀ᵐ t ∂MeasureTheory.volume,
      t ∈ Set.uIoc (t₀ + D.δ_right ε) 1 → F t = integrand t := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr
      ((Set.finite_singleton (t₀ + D.δ_right ε)).measure_zero MeasureTheory.volume)]
      with t _ ht_mem
    rw [Set.uIoc_of_le h_right_lt.le] at ht_mem
    have ht_gt_t₀ : t₀ < t := by linarith [ht_mem.1]
    simp only [hF_def, hI_def, cpvIntegrand]
    rw [if_pos]
    refine D.h_far_right ε hε_pos hε_lt t
      ⟨by linarith [ht₀_Ioo.1], ht_mem.2⟩ (by linarith) (by linarith [ht_mem.1])
  -- Step 4: Integrability of integrand on outer pieces (from uniqueness).
  have h_int_left :
      IntervalIntegrable integrand MeasureTheory.volume 0 (t₀ - D.δ_left ε) :=
    inv_sub_mul_deriv_intervalIntegrable_left γ ht₀_Ioo hδL_pos hδL_small h_unique
  have h_int_right :
      IntervalIntegrable integrand MeasureTheory.volume (t₀ + D.δ_right ε) 1 :=
    inv_sub_mul_deriv_intervalIntegrable_right γ ht₀_Ioo hδR_pos hδR_small h_unique
  -- Step 5: Integrability of F on each piece via congr_ae.
  have hF_int_left : IntervalIntegrable F MeasureTheory.volume 0 (t₀ - D.δ_left ε) :=
    h_int_left.congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
        (hF_left_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_int_mid :
      IntervalIntegrable F MeasureTheory.volume (t₀ - D.δ_left ε) (t₀ + D.δ_right ε) :=
    (IntervalIntegrable.zero (μ := MeasureTheory.volume)
      (a := t₀ - D.δ_left ε) (b := t₀ + D.δ_right ε)).congr
      (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F MeasureTheory.volume (t₀ + D.δ_right ε) 1 :=
    h_int_right.congr_ae
      ((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr
        (hF_right_ae.mono (fun t ht hm => (ht hm).symm)))
  -- Step 6: Split, simplify pieces.
  have h_split : ∫ t in (0 : ℝ)..1, F t =
      (∫ t in (0 : ℝ)..(t₀ - D.δ_left ε), F t) +
      (∫ t in (t₀ - D.δ_left ε)..(t₀ + D.δ_right ε), F t) +
      (∫ t in (t₀ + D.δ_right ε)..1, F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int_left.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
  rw [h_split,
      intervalIntegral.integral_zero_ae (MeasureTheory.ae_of_all _ (fun t ht => hF_mid t ht)),
      intervalIntegral.integral_congr_ae hF_left_ae,
      intervalIntegral.integral_congr_ae hF_right_ae, add_zero]

/-- **Construct `AsymmetricArcFTCHyp` from a `HasCauchyPV` hypothesis** and
the derived geometric scaffolding. This packages the analytic content
`(E, h_ftc, h_limit, hint_left, hint_right)` from the existence of the
Cauchy principal value at `s` along `γ`.

This is the heart of T-BR-Y3c: it shows that the 5-field FTC oracle is
derivable from a single CPV-existence hypothesis. -/
noncomputable def AsymmetricArcFTCHyp.ofHasCauchyPV
    {γ : ClosedPwC1Immersion x} {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (D : DerivedAsymmetricCutoffs γ s t₀)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {L : ℂ}
    (hCPV : HasCauchyPV (fun z => (z - s)⁻¹)
      γ.toPwC1Immersion.toPiecewiseC1Path s L) :
    AsymmetricArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s t₀
      D.δ_left D.δ_right D.threshold L := by
  classical
  refine
    { E := fun ε =>
        (∫ t in (0 : ℝ)..(t₀ - D.δ_left ε),
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
            deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) +
        (∫ t in (t₀ + D.δ_right ε)..1,
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
            deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t)
      h_ftc := fun ε _ _ => rfl
      hint_left := fun ε hε_pos hε_lt => ?_
      hint_right := fun ε hε_pos hε_lt => ?_
      h_limit := ?_ }
  · exact inv_sub_mul_deriv_intervalIntegrable_left γ ht₀_Ioo
      (D.hδ_left_pos ε hε_pos hε_lt) (D.hδ_left_small ε hε_pos hε_lt) h_unique
  · exact inv_sub_mul_deriv_intervalIntegrable_right γ ht₀_Ioo
      (D.hδ_right_pos ε hε_pos hε_lt) (D.hδ_right_small ε hε_pos hε_lt) h_unique
  · -- h_limit: E(ε) → L from HasCauchyPV via cutoff_integral_eq_outer_sum.
    have h_ev :
        (fun ε => ∫ t in (0 : ℝ)..1,
          cpvIntegrand (fun z => (z - s)⁻¹)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
        =ᶠ[𝓝[>] (0 : ℝ)] fun ε =>
          (∫ t in (0 : ℝ)..(t₀ - D.δ_left ε),
            (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
              deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) +
          (∫ t in (t₀ + D.δ_right ε)..1,
            (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s)⁻¹ *
              deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) := by
      filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
      exact cutoff_integral_eq_outer_sum γ ht₀_Ioo D h_unique hε.1 hε.2
    exact hCPV.congr' h_ev

/-- **Generic `AsymmetricSingleCrossingData` builder from
`HasCauchyPV`** (T-BR-Y3c).

Given a closed piecewise-`C¹` immersion `γ` crossing `s` at `t₀ ∈ Ioo 0 1`
uniquely and off-partition, together with the **existence of the Cauchy
principal value of `(z - s)⁻¹` along `γ`**, build the full
`AsymmetricSingleCrossingData γ.toPiecewiseC1Path s`.

This is the strongest form available: the geometric scaffolding is derived
automatically (T-BR-Y3b), and the analytic FTC content is reduced to a
single `HasCauchyPV` hypothesis (T-BR-Y3c). Compared with
`ofClosedImmersion_flat_one_derived` (which requires a 5-field
`AsymmetricArcFTCHyp`), this constructor exposes only `HasCauchyPV`. -/
noncomputable def AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    (h_part_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition)
    {L : ℂ}
    (hCPV : HasCauchyPV (fun z => (z - s)⁻¹)
      γ.toPwC1Immersion.toPiecewiseC1Path s L) :
    AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s :=
  let D := deriveAsymmetricCutoffs γ ht₀_Ioo h_at h_unique h_part_off
  AsymmetricSingleCrossingData.ofDerivedCutoffs D
    (AsymmetricArcFTCHyp.ofHasCauchyPV ht₀_Ioo D h_unique hCPV)

/-- **Corner-friendly variant** of `AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV`
that does **not** require `h_part_off`. The underlying geometric machinery
(`deriveAsymmetricCutoffs_anywhere`) only needs one-sided derivative limits,
which exist at every interior point of a `ClosedPwC1Immersion` (smooth or
corner). (T-BR-Y10b) -/
noncomputable def AsymmetricSingleCrossingData.ofClosedImmersion_hasCauchyPV_anywhere
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀_Ioo : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s)
    (h_unique : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t₀)
    {L : ℂ}
    (hCPV : HasCauchyPV (fun z => (z - s)⁻¹)
      γ.toPwC1Immersion.toPiecewiseC1Path s L) :
    AsymmetricSingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s :=
  let D := deriveAsymmetricCutoffs_anywhere γ ht₀_Ioo h_at h_unique
  AsymmetricSingleCrossingData.ofDerivedCutoffs D
    (AsymmetricArcFTCHyp.ofHasCauchyPV ht₀_Ioo D h_unique hCPV)

end HungerbuhlerWasem

end
