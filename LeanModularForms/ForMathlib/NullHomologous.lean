/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.PoincareBridge
import LeanModularForms.ForMathlib.CurveUtilities

/-!
# Null-Homologous Curves

A closed piecewise C^1 immersion is **null-homologous** in an open set `U` when its image
lies in `U` and its winding number around every point outside `U` is zero. This is the
topological condition required by the generalized residue theorem of Hungerbuhler-Wasem.

## Main definitions

* `IsNullHomologous` -- null-homologous closed piecewise C^1 immersion in an open set.
  Closedness is encoded by `PwC1Immersion x x` (same start and end point).

## Main results

* `isNullHomologous_of_convex` -- every closed piecewise C^1 immersion in a convex open
  set is null-homologous.
* `IsNullHomologous.mono` -- monotonicity: null-homologous in `U` implies null-homologous
  in any superset `V ⊇ U`.
* `IsNullHomologous.closed` -- extract that the underlying path is closed (trivial since
  `x = x`).

## Design notes

We use `PwC1Immersion x x` to encode closedness: since the start and end points
are the same, the path is automatically closed. The `winding_zero` field uses the value
`generalizedWindingNumber` (not the `HasGeneralizedWindingNumber` predicate) because
downstream applications need the actual numerical value `0`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

variable {x : ℂ}

/-- A closed piecewise C^1 immersion `gamma` is null-homologous in an open set `U` if:
1. Its image lies in `U`.
2. Its winding number around every point outside `U` is zero.

Closedness is encoded by the type: `PwC1Immersion x x` has the same start and
end point. -/
structure IsNullHomologous (γ : PwC1Immersion x x) (U : Set ℂ) : Prop where
  /-- The image of `gamma` lies in `U`. -/
  image_subset : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U
  /-- The generalized winding number around every point outside `U` is zero. -/
  winding_zero : ∀ z, z ∉ U →
    generalizedWindingNumber γ.toPiecewiseC1Path z = 0

/-! ### Basic properties -/

/-- The underlying path of a null-homologous immersion is closed. -/
theorem IsNullHomologous.closed {γ : PwC1Immersion x x} {U : Set ℂ}
    (_h : IsNullHomologous γ U) : γ.toPiecewiseC1Path.IsClosed :=
  rfl

/-- Monotonicity: if `gamma` is null-homologous in `U` and `U ⊆ V`, then `gamma` is
null-homologous in `V`. -/
theorem IsNullHomologous.mono {γ : PwC1Immersion x x} {U V : Set ℂ}
    (h : IsNullHomologous γ U) (hUV : U ⊆ V) : IsNullHomologous γ V where
  image_subset := fun t ht => hUV (h.image_subset t ht)
  winding_zero := fun z hz => h.winding_zero z (fun hmem => hz (hUV hmem))

/-! ### Auxiliary lemmas -/

/-- If a piecewise C^1 path avoids a point, there is a positive distance lower bound. -/
private theorem avoids_delta_bound (γ : PiecewiseC1Path x x) (z₀ : ℂ)
    (h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z₀‖ := by
  have h_compact : IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    isCompact_Icc.image γ.toPath.continuous_extend
  have h_nonempty : (γ.toPath.extend '' Icc (0 : ℝ) 1).Nonempty :=
    ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
  have h_not_mem : z₀ ∉ γ.toPath.extend '' Icc (0 : ℝ) 1 :=
    fun ⟨t, ht, heq⟩ => h_avoids t ht heq
  have h_pos : 0 < Metric.infDist z₀ (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
    (h_compact.isClosed.notMem_iff_infDist_pos h_nonempty).mp h_not_mem
  exact ⟨_, h_pos, fun t ht => by
    calc Metric.infDist z₀ _ ≤ dist z₀ (γ.toPath.extend t) :=
          Metric.infDist_le_dist_of_mem (mem_image_of_mem _ ht)
      _ = ‖γ.toPath.extend t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]⟩

/-- The contour integral of `(w - z)⁻¹` along a closed piecewise C^1 path in a convex
set not containing `z` is zero.

The proof handles two cases:
- If the contour integrand is interval integrable, the FTC telescope gives
  `F(x) - F(x) = 0` using the primitive `F` from the convex domain theorem.
- If not integrable, the integral is `0` by mathlib's `integral_undef` convention. -/
private theorem contourIntegral_inv_eq_zero_of_convex {U : Set ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (γ : PiecewiseC1Path x x)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) (z : ℂ) (hz : z ∉ U) :
    γ.contourIntegral (fun w => (w - z)⁻¹) = 0 := by
  by_cases h_int : IntervalIntegrable
      (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume 0 1
  · -- Case 1: integrand is integrable → use FTC
    have h_ne : ∀ w ∈ U, w - z ≠ 0 :=
      fun w hw h => hz (sub_eq_zero.mp h ▸ hw)
    have h_holo : DifferentiableOn ℂ (fun w => (w - z)⁻¹) U := fun w hw =>
      ((differentiableAt_id.sub (differentiableAt_const z)).inv
        (h_ne w hw)).differentiableWithinAt
    obtain ⟨F, hF⟩ := h_holo.hasPrimitive_of_convex hU hUo hUne
    exact γ.contourIntegral_eq_zero_of_hasDerivAt_of_closed rfl hγ
      (fun w hw => hF w hw) h_int
  · -- Case 2: integrand not integrable → integral is 0 by convention
    exact intervalIntegral.integral_undef h_int

/-! ### Winding vanishes in neighborhoods of exterior points -/

/-- **B-1 (weaker form)**: For `γ` null-homologous in `U` and `w` strictly outside
the closure of `U`, there exists `ε > 0` such that the generalized winding number
vanishes throughout the ball `ball w ε`.

This is the easy case of `h_winding_zero_near` used in `dixonFunction_differentiable`:
when `w ∉ closure U`, a small ball around `w` stays in the complement of `U`, and
null-hom gives winding 0 at every point of that ball.

The stronger statement (for `w ∉ U`, possibly on the boundary) requires the
additional fact that the winding number is locally constant on connected components
of `ℂ \ γ.image`, which is deferred. -/
theorem IsNullHomologous.winding_zero_nhds_of_not_mem_closure
    {γ : PwC1Immersion x x} {U : Set ℂ} (h_null : IsNullHomologous γ U)
    {w : ℂ} (hw : w ∉ closure U) :
    ∃ ε > 0, ∀ w' ∈ Metric.ball w ε,
      generalizedWindingNumber γ.toPiecewiseC1Path w' = 0 := by
  have h_compl_open : IsOpen (closure U)ᶜ := isClosed_closure.isOpen_compl
  obtain ⟨ε, hε_pos, hball_sub⟩ := Metric.isOpen_iff.mp h_compl_open w hw
  refine ⟨ε, hε_pos, fun w' hw' => ?_⟩
  exact h_null.winding_zero w' (fun hmem =>
    hball_sub hw' (subset_closure hmem))

/-- **B-1 cocompact form**: For `γ` null-homologous in a bounded `U`, winding vanishes
(and γ avoids the point) eventually in `cocompact ℂ`.

Proof: for bounded `U`, `Uᶜ` is cobounded = cocompact. For `w ∉ U`, γ.image ⊆ U gives
γ avoids `w`, and null-hom gives `winding γ w = 0`. -/
theorem IsNullHomologous.winding_eventually_zero_cocompact_of_bounded
    {γ : PwC1Immersion x x} {U : Set ℂ} (h_null : IsNullHomologous γ U)
    (hU_bounded : Bornology.IsBounded U) :
    ∀ᶠ w in Filter.cocompact ℂ,
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ w) ∧
        generalizedWindingNumber γ.toPiecewiseC1Path w = 0 := by
  have h_compl : Uᶜ ∈ Filter.cocompact ℂ := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Bornology.isBounded_def.mp hU_bounded
  filter_upwards [h_compl] with w hw_notin
  refine ⟨fun t ht heq => hw_notin (heq ▸ h_null.image_subset t ht),
    h_null.winding_zero w hw_notin⟩

/-! ### Convex domains -/

/-- Every closed piecewise C^1 immersion in a convex open set is null-homologous.

The proof: for `z ∉ U`, the path avoids `z` (since image ⊆ U). The generalized winding
number reduces to `(2πi)⁻¹ · ∮_γ (w-z)⁻¹ dw` by `hasGeneralizedWindingNumber_of_avoids`.
The contour integral vanishes: either by the FTC telescope (if the integrand is integrable),
or by mathlib's convention that the integral of a non-integrable function is zero. -/
theorem isNullHomologous_of_convex {U : Set ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (γ : PwC1Immersion x x)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ∈ U) :
    IsNullHomologous γ U where
  image_subset := hγ
  winding_zero := by
    intro z hz
    have h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ z :=
      fun t ht heq => hz (heq ▸ hγ t ht)
    obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
      avoids_delta_bound γ.toPiecewiseC1Path z h_avoids
    rw [(hasGeneralizedWindingNumber_of_avoids ⟨δ, hδ_pos, hδ_bound⟩).eq,
      contourIntegral_inv_eq_zero_of_convex hU hUo hUne γ.toPiecewiseC1Path hγ z hz,
      mul_zero]

end
