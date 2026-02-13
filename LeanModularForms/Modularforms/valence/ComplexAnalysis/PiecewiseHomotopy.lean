/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.HomotopyBridge
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Infrastructure.PiecewiseHomotopyHelpers

/-!
# Homotopy Theory for Piecewise C¹ Curves

This file extends the homotopy theory to piecewise C¹ curves, which is needed for
the valence formula where the fundamental domain boundary is piecewise smooth.

## Main Results

* `PiecewiseCurvesHomotopicAvoiding` - Homotopy definition for piecewise C¹ curves
* `windingNumber_eq_of_piecewise_homotopic` - Homotopy invariance for piecewise curves
* `linearHomotopy` - Standard linear interpolation between curves

## Mathematical Background

### Key Observation from Isabelle's HOL-Complex_Analysis

Isabelle's `valid_path` is defined as piecewise C¹ differentiable on [0,1], meaning there
exists a finite set of points where differentiability may fail. The key properties:

1. **Winding number well-defined**: The integral ∮ dz/(z-z₀) exists as a proper integral
   for piecewise C¹ curves avoiding z₀, since the integrand is continuous and the
   derivative exists almost everywhere.

2. **Integer-valued**: For closed curves avoiding z₀, the winding number is always an
   integer. This follows from the fact that exp(-∫₀ᵗ γ'(s)/(γ(s)-z₀) ds) = (γ(t)-z₀)/(γ(0)-z₀),
   and for closed curves γ(b) = γ(a), so the total integral is 2πi × integer.

3. **Homotopy invariance**: If two closed piecewise C¹ curves are homotopic avoiding z₀,
   they have the same winding number. The proof uses:
   - The winding number varies continuously with the homotopy parameter s
   - The winding number is always an integer
   - A continuous integer-valued function on [0,1] is constant

### Difference from Smooth Case

The smooth case (`ClosedCurvesHomotopicAvoiding`) requires:
- `∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun t' => H(t',s)) t`

For piecewise C¹ curves, we relax this to:
- `∀ t ∈ Ioo a b, t ∉ P, DifferentiableAt ℝ (fun t' => H(t',s)) t`

where P is a finite set of partition points.

### References

* Isabelle: `Winding_Numbers.thy` - `winding_number_homotopy_paths`
* Isabelle: `Contour_Integration.thy` - `valid_path`, `contour_integral_join`
* Ahlfors, "Complex Analysis" - Chapter 4 on winding numbers
* Rudin, "Real and Complex Analysis" - Chapter 10 on complex integration
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-! ## Piecewise Homotopy Definition -/

/-- Two closed piecewise C¹ curves are homotopic avoiding z₀ if there exists a
    continuous deformation that:
    - Is continuous overall
    - Restricts to γ₀ at s=0 and γ₁ at s=1
    - Keeps all intermediate curves closed
    - Avoids z₀ throughout
    - Is differentiable in t except at finitely many partition points

    This relaxes `ClosedCurvesHomotopicAvoiding` to handle piecewise smooth curves.
-/
def PiecewiseCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (P : Finset ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    -- H is jointly continuous
    Continuous H ∧
    -- H(·, 0) = γ₀
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    -- H(·, 1) = γ₁
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    -- Closed at each stage: H(a, s) = H(b, s)
    (∀ s ∈ Icc (0:ℝ) 1, H (a, s) = H (b, s)) ∧
    -- Avoids z₀ throughout
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀) ∧
    -- Differentiable in t away from partition points
    (∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    -- The t-derivative is continuous on each piece (between partition points)
    -- This is the key regularity condition for dominated convergence
    -- NOTE: We require Ioo p₁ p₂ ⊆ Ioo a b because for clamped homotopies,
    -- the derivative is discontinuous at clamp boundaries when extending beyond [a,b].
    -- This constraint is satisfied by all natural partition pieces.
    (∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1) (Ioo p₁ p₂ ×ˢ Icc 0 1)) ∧
    -- Derivative bound: required for dominated convergence in continuity proof
    (∃ M : ℝ, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, ‖deriv (fun t' => H (t', s)) t‖ ≤ M)

/-- Simplified version: homotopic avoiding with empty partition (smooth case).
    This is equivalent to `ClosedCurvesHomotopicAvoiding`. -/
def SmoothCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ ∅

/-! ## Winding Number for Piecewise C¹ Curves -/

/-- The generalized winding number is well-defined for piecewise C¹ curves.

    For a piecewise C¹ curve γ that avoids z₀, the integral
      (1/2πi) ∫ₐᵇ γ'(t)/(γ(t)-z₀) dt
    exists as a proper integral because:
    1. The integrand is continuous except at finitely many points (partition)
    2. At partition points, the limits exist from both sides
    3. The integral splits into finitely many pieces, each well-defined

    This uses `generalizedWindingNumber'` from WindingNumber.lean which handles
    the PV case, but for curves avoiding z₀ it equals the classical integral.
-/
theorem generalizedWindingNumber_welldefined_piecewiseC1
    (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (_hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    ∃! n : ℂ, n = generalizedWindingNumber' γ.toFun γ.a γ.b z₀ := by
  -- The hypothesis _hγ_avoids ensures the integral is well-defined (no singularities),
  -- but the uniqueness statement is trivial: X is the unique value equal to X.
  exact ⟨generalizedWindingNumber' γ.toFun γ.a γ.b z₀, rfl, fun _ h => h⟩

/-! ## Helper Lemmas for Piecewise Smooth Integer-Valuedness -/

/-- A finite set has measure zero.

    This is used to show that integrals over [a,b] are not affected by
    changing values at finitely many partition points.
-/
lemma finset_measure_zero (P : Finset ℝ) : volume (P : Set ℝ) = 0 := by
  apply Set.Finite.measure_zero
  exact Finset.finite_toSet P

/-- A continuous function on [a, b] with derivative 0 on (a, b) minus a finite set
    has right derivative 0 everywhere on [a, b).

    This allows using `constant_of_has_deriv_right_zero` for piecewise smooth functions.
-/
lemma hasDerivWithinAt_zero_of_deriv_zero_off_finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (a b : ℝ) (P : Finset ℝ) (hab : a < b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ f t)
    (hf_deriv_zero : ∀ t ∈ Ioo a b, t ∉ P → deriv f t = 0) :
    ∀ t ∈ Ico a b, HasDerivWithinAt f 0 (Ici t) t := by
  intro t ht
  -- Key insight: for any t ∈ [a, b), the RIGHT derivative of f at t is 0.
  -- This is because there exists ε > 0 such that (t, t + ε) ⊆ (a, b) and avoids P.
  -- On (t, t + ε), f' = 0, so f is constant, so the right derivative at t is 0.
  have ht_lt_b : t < b := ht.2
  -- The set {b} ∪ P is finite
  let S : Set ℝ := {b} ∪ (P : Set ℝ)
  have hS_finite : S.Finite := (Set.finite_singleton b).union (Finset.finite_toSet P)
  -- Find s_min = min {s ∈ S | t < s}. This exists because b ∈ S and t < b.
  let S_above : Set ℝ := {s ∈ S | t < s}
  have hS_above_nonempty : S_above.Nonempty := ⟨b, by simp only [S_above, S, Set.mem_setOf_eq,
    Set.mem_union, Set.mem_singleton_iff, true_or, ht_lt_b, and_self]⟩
  have hS_above_finite : S_above.Finite := hS_finite.subset (fun s hs => hs.1)
  -- Convert to Finset to find minimum
  have hS_above_finset := hS_above_finite.toFinset
  have hS_above_finset_nonempty : hS_above_finite.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hS_above_nonempty
  -- Get the minimum element
  set s_min := hS_above_finite.toFinset.min' hS_above_finset_nonempty with hs_min_def
  have hs_min_in : s_min ∈ S_above := by
    have := Finset.min'_mem hS_above_finite.toFinset hS_above_finset_nonempty
    rw [Set.Finite.mem_toFinset] at this
    exact this
  have hs_min_le : ∀ s ∈ S_above, s_min ≤ s := by
    intro s hs
    have hs_finset : s ∈ hS_above_finite.toFinset := by rw [Set.Finite.mem_toFinset]; exact hs
    exact Finset.min'_le hS_above_finite.toFinset s hs_finset
  have ht_lt_smin : t < s_min := hs_min_in.2
  -- For any x ∈ (t, s_min), x ∉ S (by minimality)
  have h_avoid : ∀ x ∈ Ioo t s_min, x ∉ S := by
    intro x hx hxS
    have hx_above : x ∈ S_above := ⟨hxS, hx.1⟩
    have := hs_min_le x hx_above
    linarith [hx.2]
  -- Therefore (t, s_min) ⊆ (a, b) \ P, and f' = 0 on (t, s_min)
  have h_Ioo_sub : Ioo t s_min ⊆ Ioo a b := by
    intro x hx
    constructor
    · calc a ≤ t := ht.1
        _ < x := hx.1
    · have : s_min ≤ b := by
        have hb_in : b ∈ S_above := ⟨by simp [S], ht_lt_b⟩
        exact hs_min_le b hb_in
      linarith [hx.2]
  have h_deriv_zero_piece : ∀ x ∈ Ioo t s_min, deriv f x = 0 := by
    intro x hx
    have hx_Ioo : x ∈ Ioo a b := h_Ioo_sub hx
    have hx_not_P : x ∉ P := by
      have hx_not_S : x ∉ S := h_avoid x hx
      simp only [S, Set.mem_union, Set.mem_singleton_iff] at hx_not_S
      push_neg at hx_not_S
      exact hx_not_S.2
    exact hf_deriv_zero x hx_Ioo hx_not_P
  -- f is differentiable on (t, s_min) with derivative 0
  have h_diff_piece : DifferentiableOn ℝ f (Ioo t s_min) := by
    intro x hx
    have hx_Ioo : x ∈ Ioo a b := h_Ioo_sub hx
    have hx_not_P : x ∉ P := by
      have hx_not_S : x ∉ S := h_avoid x hx
      simp only [S, Set.mem_union, Set.mem_singleton_iff] at hx_not_S
      push_neg at hx_not_S
      exact hx_not_S.2
    exact (hf_diff x hx_Ioo hx_not_P).differentiableWithinAt
  -- By IsOpen.is_const_of_deriv_eq_zero, f is constant on (t, s_min)
  have h_const_piece : ∀ x ∈ Ioo t s_min, ∀ y ∈ Ioo t s_min, f x = f y := by
    have h_eq_on : Set.EqOn (deriv f) 0 (Ioo t s_min) := fun x hx => h_deriv_zero_piece x hx
    exact fun x hx y hy => IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo h_diff_piece h_eq_on hx hy
  -- Now prove HasDerivWithinAt f 0 (Ici t) t
  -- Strategy: f is constant on (t, s_min) and continuous at t, so f(x) = f(t) for x near t
  -- Hence slope f t x = 0 for x ∈ (t, s_min), so slope f t → 0
  --
  -- This follows from: constant function has right derivative 0
  -- We apply this to (t, s_min) where f is constant and then extend to t by continuity.
  --
  -- The formal proof uses that:
  -- 1. f is continuous at t
  -- 2. f is constant on (t, s_min)
  -- 3. By continuity, f(t) = lim_{x→t+} f(x) = f(x₀) for any x₀ ∈ (t, s_min)
  -- 4. So for x ∈ (t, s_min), f(x) = f(t), hence (f(x) - f(t))/(x-t) = 0
  -- 5. Thus slope f t → 0 as we approach t from the right
  have h_mid : (t + s_min) / 2 ∈ Ioo t s_min := ⟨by linarith, by linarith⟩
  set x₀ := (t + s_min) / 2
  have h_cont_at_t : ContinuousWithinAt f (Icc a b) t := hf_cont.continuousWithinAt (Ico_subset_Icc_self ht)
  -- f is constant on (t, s_min), so f(x) = f(x₀) for all x ∈ (t, s_min)
  have h_f_eq_x₀ : ∀ x ∈ Ioo t s_min, f x = f x₀ := fun x hx => h_const_piece x hx x₀ h_mid
  -- f(t) = f(x₀) by right continuity
  have h_f_t_eq : f t = f x₀ := by
    -- Use that f is continuous at t and equals f(x₀) on (t, s_min)
    have h_Ioo_sub_Icc : Ioo t s_min ⊆ Icc a b := fun x hx =>
      ⟨le_of_lt (lt_of_le_of_lt ht.1 hx.1), le_of_lt (lt_of_lt_of_le hx.2 (hs_min_le b ⟨by simp [S], ht_lt_b⟩))⟩
    -- By continuity of f at t from the right in (t, s_min)
    -- lim_{x→t+} f(x) = f(t) and also = f(x₀)
    have h_cont_Ioo : ContinuousWithinAt f (Ioo t s_min) t := by
      apply h_cont_at_t.mono h_Ioo_sub_Icc
    -- The nhds of t within (t, s_min) from the right gives f → f(t)
    -- But f ≡ f(x₀) on (t, s_min), so f(t) = f(x₀)
    have h_eq_near : ∀ᶠ x in 𝓝[Ioo t s_min] t, f x = f x₀ := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact h_f_eq_x₀ x hx
    have h_tendsto : Tendsto f (𝓝[Ioo t s_min] t) (𝓝 (f t)) := h_cont_Ioo.tendsto
    have h_tendsto' : Tendsto (fun _ => f x₀) (𝓝[Ioo t s_min] t) (𝓝 (f t)) := by
      apply h_tendsto.congr'
      exact h_eq_near
    -- f x₀ is the unique limit; first show filter is NeBot
    have h_ne : (𝓝[Ioo t s_min] t).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot]
      have h_ne' : t ≠ s_min := ne_of_lt ht_lt_smin
      rw [closure_Ioo h_ne']
      exact ⟨le_refl t, le_of_lt ht_lt_smin⟩
    haveI : (𝓝[Ioo t s_min] t).NeBot := h_ne
    have : f t = f x₀ := tendsto_nhds_unique h_tendsto' tendsto_const_nhds
    exact this
  -- Now show the right derivative is 0
  rw [hasDerivWithinAt_iff_tendsto_slope]
  -- slope f t x = (x - t)⁻¹ • (f x - f t) = 0 for x ∈ (t, s_min)
  have h_Ioi_sub : Ioo t s_min ⊆ Ici t \ {t} := fun x hx => ⟨le_of_lt hx.1, ne_of_gt hx.1⟩
  have h_Ioo_mem : Ioo t s_min ∈ 𝓝[Ici t \ {t}] t := by
    rw [mem_nhdsWithin]
    refine ⟨Iio s_min, isOpen_Iio, ht_lt_smin, ?_⟩
    intro x ⟨hx_Iio, hx_Ici_diff⟩
    constructor
    · exact lt_of_le_of_ne hx_Ici_diff.1 (Ne.symm hx_Ici_diff.2)
    · exact hx_Iio
  have h_slope_zero : ∀ᶠ x in 𝓝[Ici t \ {t}] t, slope f t x = 0 := by
    filter_upwards [h_Ioo_mem] with x hx
    simp only [slope, h_f_eq_x₀ x hx, ← h_f_t_eq, vsub_self, smul_zero]
  exact tendsto_nhds_of_eventually_eq h_slope_zero

/-- For piecewise C¹ curves with explicit derivative bound, the winding number is an integer.

    **This is the practical version with explicit bounds** - use this in applications where
    you have concrete curves with known derivative bounds.

    **Mathematical Argument**:
    For a closed curve γ avoiding z₀, the winding number equals the integral
      (1/2πi) ∫ₐᵇ γ'(t)/(γ(t)-z₀) dt

    With an explicit bound M on ‖γ'‖ and δ > 0 bounding ‖γ - z₀‖ away from 0,
    the integrand is bounded by M/δ, making it integrable.
-/
lemma windingNumber_integer_of_piecewise_closed_avoiding_with_bound
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (M : ℝ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_deriv_bound : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M)
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  -- WITH EXPLICIT BOUNDS, we can prove integrability and apply the exp trick.
  --
  -- Step 1: Get uniform avoidance bound δ > 0
  have h_bound_away : ∃ δ > 0, ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖ := by
    have h_compact : IsCompact (γ '' Icc a b) := isCompact_Icc.image_of_continuousOn hγ_cont
    have h_nonempty : (γ '' Icc a b).Nonempty := Set.image_nonempty.mpr (nonempty_Icc.mpr (le_of_lt hab))
    have hz₀_notin : z₀ ∉ γ '' Icc a b := fun ⟨t, ht, heq⟩ => hγ_avoids t ht heq
    have hδ : 0 < Metric.infDist z₀ (γ '' Icc a b) :=
      (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp hz₀_notin
    use Metric.infDist z₀ (γ '' Icc a b), hδ
    intro t ht
    have hmem : γ t ∈ γ '' Icc a b := mem_image_of_mem γ ht
    calc Metric.infDist z₀ (γ '' Icc a b) ≤ dist z₀ (γ t) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖γ t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := h_bound_away
  -- Step 2: Define the integrand and show it's bounded by M/δ
  let integrand : ℝ → ℂ := fun t => deriv γ t / (γ t - z₀)
  have h_integrand_bound : ∀ t ∈ Icc a b, ‖integrand t‖ ≤ M / δ := by
    intro t ht
    simp only [integrand, norm_div]
    calc ‖deriv γ t‖ / ‖γ t - z₀‖ ≤ ‖deriv γ t‖ / δ :=
            div_le_div_of_nonneg_left (norm_nonneg _) hδ_pos (hδ_bound t ht)
         _ ≤ M / δ := div_le_div_of_nonneg_right (hγ_deriv_bound t ht) (le_of_lt hδ_pos)
  -- Step 3: Show integrand is continuous off P ∪ {a, b}
  let P' : Finset ℝ := P ∪ {a, b}
  have h_integrand_cont : ContinuousOn integrand ((Icc a b) \ P') := by
    intro t ⟨ht_Icc, ht_notP'⟩
    simp only [P', Finset.coe_union, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_notP'
    have ht_Ioo : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_notP'.2.1),
                                   lt_of_le_of_ne ht_Icc.2 ht_notP'.2.2⟩
    have ht_notP : t ∉ P := ht_notP'.1
    have hne : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids t ht_Icc)
    apply ContinuousWithinAt.div
    · -- deriv γ is continuous at t: find an interval around t that avoids P
      -- Since t ∉ P and P is finite, there exists ε > 0 such that (t-ε, t+ε) avoids P
      have h_away : ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P := by
        by_cases hP_empty : P = ∅
        · use 1, one_pos; intro x _; simp [hP_empty]
        · have hP_ne : P.Nonempty := Finset.nonempty_of_ne_empty hP_empty
          have h_ne_mem : ∀ p ∈ P, p ≠ t := fun p hp => ne_of_mem_of_not_mem hp ht_notP
          let d := Finset.inf' P hP_ne (fun p => |p - t|)
          have hd_pos : 0 < d := by
            have h_all_pos : ∀ p ∈ P, 0 < |p - t| :=
              fun p hp => abs_pos.mpr (sub_ne_zero.mpr (h_ne_mem p hp))
            rw [Finset.lt_inf'_iff]; exact h_all_pos
          use d / 2, by linarith
          intro x hx hxP
          have h_dist : d ≤ |x - t| := Finset.inf'_le (fun p => |p - t|) hxP
          have hx_dist : |x - t| < d := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
          linarith
      obtain ⟨ε, hε_pos, hε_avoid⟩ := h_away
      -- Build interval [p₁, p₂] around t that avoids P
      let p₁ := max a (t - ε / 2)
      let p₂ := min b (t + ε / 2)
      have ht_between : t - ε / 2 < t + ε / 2 := by linarith
      have hp₁p₂ : p₁ < p₂ := by
        simp only [p₁, p₂, lt_min_iff, max_lt_iff]
        -- After simp: (a < b ∧ t - ε/2 < b) ∧ (a < t + ε/2 ∧ t - ε/2 < t + ε/2)
        have ha_lt_b : a < b := lt_trans ht_Ioo.1 ht_Ioo.2
        have ha_lt_t_eps : a < t + ε / 2 := by linarith [ht_Ioo.1, hε_pos]
        have ht_eps_lt_b : t - ε / 2 < b := by linarith [ht_Ioo.2, hε_pos]
        exact ⟨⟨ha_lt_b, ht_eps_lt_b⟩, ⟨ha_lt_t_eps, ht_between⟩⟩
      have h_piece_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := by
        intro s hs; apply hε_avoid
        simp only [p₁, p₂, mem_Ioo] at hs
        constructor
        · calc t - ε < t - ε / 2 := by linarith
            _ ≤ max a (t - ε / 2) := le_max_right _ _
            _ < s := hs.1
        · calc s < min b (t + ε / 2) := hs.2
            _ ≤ t + ε / 2 := min_le_right _ _
            _ < t + ε := by linarith
      -- Prove that Ioo p₁ p₂ ⊆ Ioo a b (follows from p₁ = max a ..., p₂ = min b ...)
      have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
        simp only [p₁, p₂, mem_Ioo] at hx ⊢
        exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1, lt_of_lt_of_le hx.2 (min_le_left b _)⟩
      have h_deriv_cont := hγ_deriv_cont p₁ p₂ hp₁p₂ h_piece_avoid h_sub
      have ht_in : t ∈ Ioo p₁ p₂ := by
        simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
        -- After simp: (a < t ∧ t - ε/2 < t) ∧ (t < b ∧ t < t + ε/2)
        have ht_lt_t_eps : t < t + ε / 2 := by linarith [hε_pos]
        have ht_eps_lt_t : t - ε / 2 < t := by linarith [hε_pos]
        exact ⟨⟨ht_Ioo.1, ht_eps_lt_t⟩, ⟨ht_Ioo.2, ht_lt_t_eps⟩⟩
      exact (h_deriv_cont.continuousAt (Ioo_mem_nhds ht_in.1 ht_in.2)).continuousWithinAt
    · -- γ - z₀ is continuous on Icc a b \ P', hence continuous at t
      have h_sub_cont : ContinuousOn (fun t => γ t - z₀) (Icc a b) := hγ_cont.sub continuousOn_const
      exact h_sub_cont.continuousWithinAt ht_Icc |>.mono diff_subset
    · exact hne
  -- Step 4: Integrand is IntervalIntegrable (using the bound!)
  have h_int : IntervalIntegrable integrand MeasureTheory.volume a b :=
    intervalIntegrable_of_piecewise_continuousOn_bounded (M / δ) (le_of_lt hab)
      h_integrand_cont h_integrand_bound
  -- Step 5: Define F and G for the exp trick
  let F : ℝ → ℂ := fun t => ∫ s in a..t, integrand s
  let G : ℝ → ℂ := fun t => (γ t - z₀) * Complex.exp (-F t)
  have hFa : F a = 0 := intervalIntegral.integral_same
  have hGa : G a = γ a - z₀ := by simp only [G, hFa, neg_zero, Complex.exp_zero, mul_one]
  -- Step 6: G is constant on [a, b] by exp trick
  have hG_const : ∀ t ∈ Icc a b, G t = G a := by
    -- G continuous + G' = 0 on (a,b) \ P ⇒ G constant
    have hG_cont : ContinuousOn G (Icc a b) := by
      apply ContinuousOn.mul
      · exact hγ_cont.sub continuousOn_const
      · apply Continuous.comp_continuousOn Complex.continuous_exp
        apply ContinuousOn.neg
        -- F continuous because integrand is IntervalIntegrable
        -- Use continuousOn_primitive_interval' which takes IntervalIntegrable directly
        have h_prim := intervalIntegral.continuousOn_primitive_interval' h_int
          (left_mem_uIcc (a := a) (b := b))
        -- h_prim : ContinuousOn (... ) (uIcc a b), need ContinuousOn ... (Icc a b)
        -- Since a ≤ b, uIcc a b = Icc a b
        rw [Set.uIcc_of_le (le_of_lt hab)] at h_prim
        exact h_prim
    have hG_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ G t := by
      intro t ht ht_not_P
      have hγ_diff_t := hγ_diff t ht ht_not_P
      apply DifferentiableAt.mul
      · exact hγ_diff_t.sub (differentiableAt_const z₀)
      · -- F is differentiable at t by FTC
        apply DifferentiableAt.cexp; apply DifferentiableAt.neg
        -- F'(t) = integrand(t) by FTC (integrand continuous at t)
        -- Build avoiding neighborhood
        have h_away : ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P := by
          by_cases hP_empty : P = ∅
          · use 1, one_pos; intro x _; simp [hP_empty]
          · have hP_ne : P.Nonempty := Finset.nonempty_of_ne_empty hP_empty
            have h_ne_mem : ∀ p ∈ P, p ≠ t := fun p hp => ne_of_mem_of_not_mem hp ht_not_P
            let d := Finset.inf' P hP_ne (fun p => |p - t|)
            have hd_pos : 0 < d := by
              have h_all_pos : ∀ p ∈ P, 0 < |p - t| :=
                fun p hp => abs_pos.mpr (sub_ne_zero.mpr (h_ne_mem p hp))
              rw [Finset.lt_inf'_iff]; exact h_all_pos
            use d / 2, by linarith
            intro x hx hxP
            have h_dist : d ≤ |x - t| := Finset.inf'_le (fun p => |p - t|) hxP
            have hx_dist : |x - t| < d := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
            linarith
        obtain ⟨ε, hε_pos, hε_avoid⟩ := h_away
        let p₁ := max a (t - ε / 2)
        let p₂ := min b (t + ε / 2)
        have ht_between : t - ε / 2 < t + ε / 2 := by linarith
        have hp₁p₂ : p₁ < p₂ := by
          simp only [p₁, p₂, lt_min_iff, max_lt_iff]
          have ha_lt_b : a < b := lt_trans ht.1 ht.2
          have ha_lt_t_eps : a < t + ε / 2 := by linarith [ht.1, hε_pos]
          have ht_eps_lt_b : t - ε / 2 < b := by linarith [ht.2, hε_pos]
          exact ⟨⟨ha_lt_b, ht_eps_lt_b⟩, ⟨ha_lt_t_eps, ht_between⟩⟩
        have h_piece_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := by
          intro s hs; apply hε_avoid
          simp only [p₁, p₂, mem_Ioo] at hs
          constructor
          · calc t - ε < t - ε / 2 := by linarith
              _ ≤ max a (t - ε / 2) := le_max_right _ _
              _ < s := hs.1
          · calc s < min b (t + ε / 2) := hs.2
              _ ≤ t + ε / 2 := min_le_right _ _
              _ < t + ε := by linarith
        -- Prove that Ioo p₁ p₂ ⊆ Ioo a b (follows from p₁ = max a ..., p₂ = min b ...)
        have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
          simp only [p₁, p₂, mem_Ioo] at hx ⊢
          exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1, lt_of_lt_of_le hx.2 (min_le_left b _)⟩
        have h_deriv_cont := hγ_deriv_cont p₁ p₂ hp₁p₂ h_piece_avoid h_sub
        have ht_in : t ∈ Ioo p₁ p₂ := by
          simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
          have ht_lt_t_eps : t < t + ε / 2 := by linarith [hε_pos]
          have ht_eps_lt_t : t - ε / 2 < t := by linarith [hε_pos]
          exact ⟨⟨ht.1, ht_eps_lt_t⟩, ⟨ht.2, ht_lt_t_eps⟩⟩
        have hne : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids t (Ioo_subset_Icc_self ht))
        have h_cont_at : ContinuousAt integrand t := by
          apply ContinuousAt.div
          · exact h_deriv_cont.continuousAt (Ioo_mem_nhds ht_in.1 ht_in.2)
          · exact hγ_cont.continuousAt (Icc_mem_nhds ht.1 ht.2) |>.sub continuousAt_const
          · exact hne
        -- Apply FTC: F differentiable where integrand continuous
        have ht_Icc := Ioo_subset_Icc_self ht
        have ht_in_uIcc : t ∈ Set.uIcc a b := by
          rw [Set.uIcc_of_le (le_of_lt hab)]; exact ht_Icc
        have h_int_at : IntervalIntegrable integrand volume a t :=
          h_int.mono_set (Set.uIcc_subset_uIcc_left ht_in_uIcc)
        -- For StronglyMeasurableAtFilter, use that integrand is continuous on Ioo p₁ p₂
        have h_integrand_cont_ioo : ContinuousOn integrand (Ioo p₁ p₂) := by
          intro x hx
          have hx_notP := h_piece_avoid x hx
          have hx_Ioo_ab : x ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hx.1,
            lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
          have hx_ne : γ x - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids x (Ioo_subset_Icc_self hx_Ioo_ab))
          apply ContinuousWithinAt.div
          · exact h_deriv_cont.continuousWithinAt hx
          · exact ((hγ_cont.sub continuousOn_const).continuousWithinAt
              (Ioo_subset_Icc_self hx_Ioo_ab)).mono
              ((Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)).trans Ioo_subset_Icc_self)
          · exact hx_ne
        have h_meas : StronglyMeasurableAtFilter integrand (𝓝 t) volume :=
          ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
            (fun x hx => h_integrand_cont_ioo.continuousAt (Ioo_mem_nhds hx.1 hx.2)) t ht_in
        exact (intervalIntegral.integral_hasDerivAt_right h_int_at h_meas h_cont_at).differentiableAt
    have hG_deriv : ∀ t ∈ Ioo a b, t ∉ P → deriv G t = 0 := by
      intro t ht ht_not_P
      have hγ_diff_t := hγ_diff t ht ht_not_P
      have hne : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids t (Ioo_subset_Icc_self ht))
      -- G' = γ' * exp(-F) + (γ-z₀) * (-F') * exp(-F)
      --    = γ' * exp(-F) - (γ-z₀) * (γ'/(γ-z₀)) * exp(-F)
      --    = γ' * exp(-F) - γ' * exp(-F) = 0
      -- Build avoiding neighborhood (outside h_cont_at for reuse)
      have h_away : ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P := by
        by_cases hP_empty : P = ∅
        · use 1, one_pos; intro x _; simp [hP_empty]
        · have hP_ne : P.Nonempty := Finset.nonempty_of_ne_empty hP_empty
          have h_ne_mem : ∀ p ∈ P, p ≠ t := fun p hp => ne_of_mem_of_not_mem hp ht_not_P
          let d := Finset.inf' P hP_ne (fun p => |p - t|)
          have hd_pos : 0 < d := by
            have h_all_pos : ∀ p ∈ P, 0 < |p - t| :=
              fun p hp => abs_pos.mpr (sub_ne_zero.mpr (h_ne_mem p hp))
            rw [Finset.lt_inf'_iff]; exact h_all_pos
          use d / 2, by linarith
          intro x hx hxP
          have h_dist : d ≤ |x - t| := Finset.inf'_le (fun p => |p - t|) hxP
          have hx_dist : |x - t| < d := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
          linarith
      obtain ⟨ε, hε_pos, hε_avoid⟩ := h_away
      let p₁ := max a (t - ε / 2)
      let p₂ := min b (t + ε / 2)
      have ht_between : t - ε / 2 < t + ε / 2 := by linarith
      have hp₁p₂ : p₁ < p₂ := by
        simp only [p₁, p₂, lt_min_iff, max_lt_iff]
        have ha_lt_b : a < b := lt_trans ht.1 ht.2
        have ha_lt_t_eps : a < t + ε / 2 := by linarith [ht.1, hε_pos]
        have ht_eps_lt_b : t - ε / 2 < b := by linarith [ht.2, hε_pos]
        exact ⟨⟨ha_lt_b, ht_eps_lt_b⟩, ⟨ha_lt_t_eps, ht_between⟩⟩
      have h_piece_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := by
        intro s hs; apply hε_avoid
        simp only [p₁, p₂, mem_Ioo] at hs
        constructor
        · calc t - ε < t - ε / 2 := by linarith
            _ ≤ max a (t - ε / 2) := le_max_right _ _
            _ < s := hs.1
        · calc s < min b (t + ε / 2) := hs.2
            _ ≤ t + ε / 2 := min_le_right _ _
            _ < t + ε := by linarith
      -- Prove that Ioo p₁ p₂ ⊆ Ioo a b (follows from p₁ = max a ..., p₂ = min b ...)
      have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
        simp only [p₁, p₂, mem_Ioo] at hx ⊢
        exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1, lt_of_lt_of_le hx.2 (min_le_left b _)⟩
      have h_deriv_cont := hγ_deriv_cont p₁ p₂ hp₁p₂ h_piece_avoid h_sub
      have ht_in : t ∈ Ioo p₁ p₂ := by
        simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
        have ht_lt_t_eps : t < t + ε / 2 := by linarith [hε_pos]
        have ht_eps_lt_t : t - ε / 2 < t := by linarith [hε_pos]
        exact ⟨⟨ht.1, ht_eps_lt_t⟩, ⟨ht.2, ht_lt_t_eps⟩⟩
      have h_cont_at : ContinuousAt integrand t := by
        apply ContinuousAt.div
        · exact h_deriv_cont.continuousAt (Ioo_mem_nhds ht_in.1 ht_in.2)
        · exact hγ_cont.continuousAt (Icc_mem_nhds ht.1 ht.2) |>.sub continuousAt_const
        · exact hne
      have ht_Icc := Ioo_subset_Icc_self ht
      have ht_in_uIcc : t ∈ Set.uIcc a b := by
        rw [Set.uIcc_of_le (le_of_lt hab)]; exact ht_Icc
      have h_int_at : IntervalIntegrable integrand volume a t :=
        h_int.mono_set (Set.uIcc_subset_uIcc_left ht_in_uIcc)
      -- For StronglyMeasurableAtFilter, use that integrand is continuous on open interval Ioo p₁ p₂
      have h_integrand_cont_ioo : ContinuousOn integrand (Ioo p₁ p₂) := by
        intro x hx
        have hx_notP := h_piece_avoid x hx
        have hx_Ioo_ab : x ∈ Ioo a b := ⟨lt_of_le_of_lt (le_max_left _ _) hx.1,
          lt_of_lt_of_le hx.2 (min_le_left _ _)⟩
        have hx_ne : γ x - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids x (Ioo_subset_Icc_self hx_Ioo_ab))
        apply ContinuousWithinAt.div
        · exact h_deriv_cont.continuousWithinAt hx
        · exact ((hγ_cont.sub continuousOn_const).continuousWithinAt
            (Ioo_subset_Icc_self hx_Ioo_ab)).mono
            ((Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)).trans Ioo_subset_Icc_self)
        · exact hx_ne
      have h_meas : StronglyMeasurableAtFilter integrand (𝓝 t) volume :=
        ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
          (fun x hx => h_integrand_cont_ioo.continuousAt (Ioo_mem_nhds hx.1 hx.2)) t ht_in
      have hF_deriv : HasDerivAt F (integrand t) t :=
        intervalIntegral.integral_hasDerivAt_right h_int_at h_meas h_cont_at
      -- G' = γ' * exp(-F) + (γ-z₀) * (-integrand) * exp(-F) = 0
      have hc : HasDerivAt (fun t => γ t - z₀) (deriv γ t) t := hγ_diff_t.hasDerivAt.sub_const z₀
      have hd : HasDerivAt (fun t => Complex.exp (-F t)) (Complex.exp (-F t) * (-integrand t)) t := by
        apply HasDerivAt.cexp; exact hF_deriv.neg
      have hG_at : HasDerivAt G (deriv γ t * Complex.exp (-F t) +
          (γ t - z₀) * (Complex.exp (-F t) * (-integrand t))) t := hc.mul hd
      have h_zero : deriv γ t * Complex.exp (-F t) +
          (γ t - z₀) * (Complex.exp (-F t) * (-integrand t)) = 0 := by
        simp only [integrand]; field_simp [hne]; ring
      rw [hG_at.deriv]; exact h_zero
    exact constant_of_has_deriv_right_zero hG_cont
      (hasDerivWithinAt_zero_of_deriv_zero_off_finite G a b P hab hG_cont hG_diff hG_deriv)
  -- Step 7: From G constant, derive exp(-F(b)) = 1
  have hGeq : G b = G a := hG_const b (right_mem_Icc.mpr (le_of_lt hab))
  have hne_a : γ a - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids a (left_mem_Icc.mpr (le_of_lt hab)))
  have h_exp_neg : Complex.exp (-F b) = 1 := by
    have h1 : (γ a - z₀) * Complex.exp (-F b) = γ a - z₀ := by
      calc (γ a - z₀) * Complex.exp (-F b)
          = (γ b - z₀) * Complex.exp (-F b) := by rw [hγ_closed]
        _ = G b := rfl
        _ = G a := hGeq
        _ = γ a - z₀ := hGa
    have h2 : (γ a - z₀) * Complex.exp (-F b) = (γ a - z₀) * 1 := by rw [h1, mul_one]
    exact mul_left_cancel₀ hne_a h2
  -- Step 8: exp(-F(b)) = 1 ⇒ F(b) = 2πin
  rw [Complex.exp_eq_one_iff] at h_exp_neg
  obtain ⟨n, hn⟩ := h_exp_neg
  use -n
  unfold generalizedWindingNumber'
  -- PV integral = ordinary integral when curve avoids z₀
  have h_pv_eq : cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0 =
      ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t := by
    unfold cauchyPrincipalValue'
    apply limUnder_eventually_eq_const
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    simp only [sub_zero]
    have ht' : t ∈ Icc a b := Ioc_subset_Icc_self (Set.uIoc_of_le (le_of_lt hab) ▸ ht)
    simp only [(mem_Ioo.mp hε).2.trans_le (hδ_bound t ht'), ↓reduceIte, deriv_sub_const]
  rw [h_pv_eq]
  have h_int_eq : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t = F b := by
    simp only [F, integrand]; congr 1; ext t; rw [mul_comm, div_eq_mul_inv]
  rw [h_int_eq]
  have hFb : F b = -(↑n * (2 * Real.pi * I)) := by calc F b = -(-F b) := by ring
      _ = -(↑n * (2 * Real.pi * I)) := by rw [hn]
  calc (2 * Real.pi * I)⁻¹ * F b = (2 * Real.pi * I)⁻¹ * (-(↑n * (2 * Real.pi * I))) := by rw [hFb]
    _ = -(↑n : ℂ) := by
        have hne : (2 : ℂ) * Real.pi * I ≠ 0 := by
          simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
            Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
        field_simp
    _ = ↑(-n) := by simp only [Int.cast_neg]

/-- For piecewise C¹ curves, the winding number is an integer.

    **Mathematical Argument**:
    For a closed curve γ avoiding z₀, the winding number equals the integral
      (1/2πi) ∫ₐᵇ γ'(t)/(γ(t)-z₀) dt

    For piecewise C¹ curves, we split at partition points P = {p₁,...,pₙ}:
      ∫ₐᵇ = ∫ₐ^{p₁} + ∫_{p₁}^{p₂} + ... + ∫_{pₙ}^b

    On each smooth piece [pᵢ, pᵢ₊₁], the fundamental theorem of calculus gives:
      ∫_{pᵢ}^{pᵢ₊₁} γ'/(γ-z₀) dt = log(γ(pᵢ₊₁) - z₀) - log(γ(pᵢ) - z₀)

    The sum telescopes to log(γ(b) - z₀) - log(γ(a) - z₀).
    Since γ(b) = γ(a) for closed curves, this is 2πi·n for some integer n.

    **Proof approach**: Use `windingNumber_integer_of_closed_avoiding` from HomotopyBridge.lean
    which already handles the exp trick. For piecewise curves, we use that:
    1. The integrand is continuous except on a null set (finite partition)
    2. The integral is the same whether we use piecewise or smooth derivatives
    3. The exp trick argument works because G = (γ-z₀)·exp(-F) is continuous
       and has zero derivative except at finitely many points
-/
lemma windingNumber_integer_of_piecewise_closed_avoiding
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  obtain ⟨M, hM⟩ := hγ_deriv_bound_ex
  exact windingNumber_integer_of_piecewise_closed_avoiding_with_bound
    γ a b z₀ P M hab hγ_closed hγ_cont hγ_diff hγ_deriv_cont hM hγ_avoids

/-! ## Winding Number Continuity for Piecewise Homotopies -/

/-- Winding number is continuous in the homotopy parameter for piecewise C¹ homotopies
    when we have an explicit derivative bound.

    This is the version with an explicit bound M that can be applied directly.
-/
lemma windingNumber_continuous_in_param_piecewise_with_bound
    (H : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (M : ℝ) (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1) (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1) :=
  windingNumber_continuousOn_param_piecewise_with_bound hab hH_cont hH_avoid hH_diff hH_deriv_cont hM_bound

/-- Winding number is continuous in the homotopy parameter for piecewise C¹ homotopies.

    **Mathematical Argument**:
    If H : [a,b] × [0,1] → ℂ is a homotopy that is:
    - Jointly continuous
    - Avoids z₀ throughout
    - Has derivatives continuous on each piece (between partition points)

    Then the winding number s ↦ n(H(·,s)) is continuous on [0,1].

    **Proof Strategy**:
    1. The integrand ∂ₜH(t,s)/(H(t,s)-z₀) is bounded (uniform distance from z₀)
    2. The integrand is continuous except on the measure-zero partition set
    3. By dominated convergence, the integral is continuous in s

    **Technical Gap**: The smooth version `windingNumber_continuous_in_param` requires
    globally continuous derivatives. For piecewise homotopies, we need to extend
    the dominated convergence argument to handle discontinuities on null sets.
-/
lemma windingNumber_continuous_in_param_piecewise
    (H : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t)
    (hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1) (Ioo p₁ p₂ ×ˢ Icc 0 1))
    (hH_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1) :=
  windingNumber_continuousOn_param_piecewise hab hH_cont hH_avoid hH_diff hH_deriv_cont
    hH_deriv_bound_ex

/-! ## Homotopy Invariance for Piecewise Curves -/

/-- **Key Theorem**: Homotopy invariance of winding numbers for piecewise C¹ curves.

    If two closed piecewise C¹ curves are homotopic avoiding z₀, they have the
    same winding number around z₀.

    **Proof strategy** (following Isabelle's `winding_number_homotopy_paths`):
    1. The winding number varies continuously with the homotopy parameter s
    2. For each s, the winding number is an integer (by windingNumber_integer_of_piecewise_closed_avoiding)
    3. A continuous integer-valued function on [0,1] is constant
    4. Therefore n(γ₀) = n(0) = n(1) = n(γ₁)

    **Reference**: Isabelle `Winding_Numbers.thy`, theorem `winding_number_homotopy_paths`
-/
theorem windingNumber_eq_of_piecewise_homotopic
    (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ P) :
    generalizedWindingNumber' γ₀ a b z₀ = generalizedWindingNumber' γ₁ a b z₀ := by
  -- Step 1: Extract the homotopy H (with the derivative bound)
  obtain ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid, hH_diff, hH_deriv_cont, M, hM_bound⟩ := hhom
  -- Step 2: Define the winding number function n(s)
  let n : ℝ → ℂ := fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀
  -- Step 3: Show n is continuous on [0,1] (using the _with_bound version)
  have hn_cont : ContinuousOn n (Icc 0 1) :=
    windingNumber_continuous_in_param_piecewise_with_bound H a b z₀ P M hab hH_cont hH_avoid
      hH_diff hH_deriv_cont hM_bound
  -- Step 4: Show n(s) is an integer for all s ∈ [0,1]
  have hn_int : ∀ s ∈ Icc (0:ℝ) 1, ∃ m : ℤ, n s = m := by
    intro s hs
    -- H(·, s) is a closed piecewise C¹ curve avoiding z₀
    -- Apply the piecewise version of integer-valuedness
    apply windingNumber_integer_of_piecewise_closed_avoiding (fun t => H (t, s)) a b z₀ P hab
    · -- Closedness: H(a, s) = H(b, s)
      exact hH_closed s hs
    · -- Continuity on [a, b]
      exact hH_cont.comp (continuous_id.prodMk continuous_const) |>.continuousOn
    · -- Differentiability at non-partition points
      intro t ht h_not_P
      exact hH_diff t ht h_not_P s hs
    · -- Derivative continuity on pieces between partition points
      -- hH_deriv_cont gives continuity on (Ioo p₁ p₂) ×ˢ (Icc 0 1)
      -- We need to extract the slice at s
      intro p₁ p₂ hp₁p₂ hpiece h_sub
      -- The derivative of H(·, s) is continuous on Ioo p₁ p₂
      -- because the full derivative is continuous on (Ioo p₁ p₂) ×ˢ (Icc 0 1)
      have h_full := hH_deriv_cont p₁ p₂ hp₁p₂ hpiece h_sub
      -- The function (fun p => deriv (H(·, p.2)) p.1) restricted to Ioo p₁ p₂ × {s}
      -- is (fun t => deriv (H(·, s)) t) which is what we need
      -- Use ContinuousOn.comp with the embedding t ↦ (t, s)
      have h_embed : ContinuousOn (fun t => (t, s)) (Ioo p₁ p₂) :=
        (continuous_id.prodMk continuous_const).continuousOn
      have h_range : MapsTo (fun t => (t, s)) (Ioo p₁ p₂) (Ioo p₁ p₂ ×ˢ Icc 0 1) :=
        fun t ht => ⟨ht, hs⟩
      -- The composition gives us the slice
      have h_comp := h_full.comp h_embed h_range
      -- Now we need to show the functions are equal
      convert h_comp using 1
    · -- Avoids z₀
      exact fun t ht => hH_avoid t ht s hs
    · -- Derivative bound existence (from homotopy field hM_bound)
      exact ⟨M, fun t ht => hM_bound t ht s hs⟩
  -- Step 5: Apply continuous_integer_valued_constant
  have heq : n 0 = n 1 := continuous_integer_valued_constant n hn_cont hn_int
  -- Step 6: Relate n(0) and n(1) to the original winding numbers
  have hn0_eq : n 0 = generalizedWindingNumber' γ₀ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 0)) γ₀ a b z₀ hab hH0
    -- Derivatives agree a.e.: use pattern from HomotopyBridge.lean
    rw [Set.uIoc_of_le (le_of_lt hab)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 0)) γ₀ (Ioo a b) :=
      fun t' ht' => hH0 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 0))) (deriv γ₀) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    -- Convert: property on Ioo implies ae on Ioc using Ioo_ae_eq_Ioc
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  have hn1_eq : n 1 = generalizedWindingNumber' γ₁ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 1)) γ₁ a b z₀ hab hH1
    rw [Set.uIoc_of_le (le_of_lt hab)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 1)) γ₁ (Ioo a b) :=
      fun t' ht' => hH1 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 1))) (deriv γ₁) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    -- Convert: property on Ioo implies ae on Ioc using Ioo_ae_eq_Ioc
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  rw [← hn0_eq, ← hn1_eq, heq]

/-! ## Linear Homotopy for Piecewise Curves -/

/-- The linear homotopy H(t,s) = (1-s)γ₀(t) + sγ₁(t) between two curves.

    This is piecewise smooth when both γ₀ and γ₁ are piecewise smooth,
    with partition points being the union of their partitions.
-/
def linearHomotopy (γ₀ γ₁ : ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun ⟨t, s⟩ => (1 - s) • γ₀ t + s • γ₁ t

theorem linearHomotopy_continuous (γ₀ γ₁ : ℝ → ℂ)
    (hγ₀ : Continuous γ₀) (hγ₁ : Continuous γ₁) :
    Continuous (linearHomotopy γ₀ γ₁) := by
  unfold linearHomotopy
  apply Continuous.add
  · apply Continuous.smul
    · exact continuous_const.sub continuous_snd
    · exact hγ₀.comp continuous_fst
  · apply Continuous.smul
    · exact continuous_snd
    · exact hγ₁.comp continuous_fst

theorem linearHomotopy_at_zero (γ₀ γ₁ : ℝ → ℂ) (t : ℝ) :
    linearHomotopy γ₀ γ₁ (t, 0) = γ₀ t := by
  simp only [linearHomotopy, sub_zero, one_smul, zero_smul, add_zero]

theorem linearHomotopy_at_one (γ₀ γ₁ : ℝ → ℂ) (t : ℝ) :
    linearHomotopy γ₀ γ₁ (t, 1) = γ₁ t := by
  simp only [linearHomotopy, sub_self, zero_smul, one_smul, zero_add]

theorem linearHomotopy_closed (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ)
    (hγ₀_closed : γ₀ a = γ₀ b) (hγ₁_closed : γ₁ a = γ₁ b) (s : ℝ) :
    linearHomotopy γ₀ γ₁ (a, s) = linearHomotopy γ₀ γ₁ (b, s) := by
  simp only [linearHomotopy, hγ₀_closed, hγ₁_closed]

/-- The linear homotopy is differentiable in t when both curves are. -/
theorem linearHomotopy_differentiableAt_t (γ₀ γ₁ : ℝ → ℂ) (t s : ℝ)
    (hγ₀ : DifferentiableAt ℝ γ₀ t) (hγ₁ : DifferentiableAt ℝ γ₁ t) :
    DifferentiableAt ℝ (fun t' => linearHomotopy γ₀ γ₁ (t', s)) t := by
  simp only [linearHomotopy]
  apply DifferentiableAt.add
  · exact hγ₀.const_smul (1 - s)
  · exact hγ₁.const_smul s

/-- The derivative of the linear homotopy in t. -/
theorem linearHomotopy_deriv_t (γ₀ γ₁ : ℝ → ℂ) (t s : ℝ)
    (hγ₀ : DifferentiableAt ℝ γ₀ t) (hγ₁ : DifferentiableAt ℝ γ₁ t) :
    deriv (fun t' => linearHomotopy γ₀ γ₁ (t', s)) t =
    (1 - s) • deriv γ₀ t + s • deriv γ₁ t := by
  simp only [linearHomotopy]
  have hd₀ : DifferentiableAt ℝ (fun t' => (1 - s) • γ₀ t') t := hγ₀.const_smul (1 - s)
  have hd₁ : DifferentiableAt ℝ (fun t' => s • γ₁ t') t := hγ₁.const_smul s
  have h1 : deriv (fun t' => (1 - s) • γ₀ t') t = (1 - s) • deriv γ₀ t :=
    deriv_const_smul (1 - s) hγ₀
  have h2 : deriv (fun t' => s • γ₁ t') t = s • deriv γ₁ t :=
    deriv_const_smul s hγ₁
  have h_add : deriv (fun t' => (1 - s) • γ₀ t' + s • γ₁ t') t =
      deriv (fun t' => (1 - s) • γ₀ t') t + deriv (fun t' => s • γ₁ t') t :=
    deriv_add hd₀ hd₁
  rw [h_add, h1, h2]

end
