/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.PoincareBridge

/-!
# Null-Homologous Closed Paths

A closed piecewise C¹ path is **null-homologous** in an open set `U` when its
generalized winding number vanishes for every point outside `U`. This is the
topological condition required by the generalized residue theorem of
Hungerbuhler--Wasem.

## Main definitions

* `IsNullHomologous γ U` -- a closed piecewise C¹ path `γ` is null-homologous in `U`
  when it lies in `U` and its generalized winding number is zero for all `z ∉ U`.

## Main results

* `isNullHomologous_of_convex` -- every closed path in a convex open set is
  null-homologous, provided the contour integrand is integrable for each
  exterior point. The proof constructs a holomorphic primitive of `(w - z)⁻¹`
  on the convex set and applies the fundamental theorem of calculus.

* `IsNullHomologous.mono` -- null-homologicity is monotone in the open set.

* `IsNullHomologous.winding_eq_zero` -- the generalized winding number value is
  zero for points outside the ambient set.

* `IsNullHomologous.contourIntegral_eq_zero` -- Cauchy's theorem: the contour
  integral of a holomorphic function along a null-homologous path in a convex
  domain vanishes.

## Design notes

The definition uses `HasGeneralizedWindingNumber` (Tendsto-based predicate) to state
that the winding number is zero. This matches the CPV-first design from
`GeneralizedWindingNumber.lean` and allows the winding number to be well-defined
even when the curve passes through the point.

The integrability hypotheses are explicit because `PiecewiseC1Path` does not carry
enough structure to automatically derive integrability of all contour integrands.
The `PiecewiseC1Immersion`-based integrability lemma lives in the
`GeneralizedResidueTheory` folder and may be promoted to ForMathlib in the future.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

variable {x : ℂ}

/-! ### Definition -/

/-- A closed piecewise C¹ path `γ` is **null-homologous** in a set `U` when:
1. The image of `γ` lies entirely in `U`.
2. The generalized winding number of `γ` around every point `z ∉ U` is zero.

This uses the `HasGeneralizedWindingNumber` predicate (Tendsto-based), which allows
the winding number to be defined even when the curve passes through `z`. For points
not on the curve, this reduces to the classical winding number being zero. -/
structure IsNullHomologous (γ : PiecewiseC1Path x x) (U : Set ℂ) : Prop where
  /-- The image of the path lies in `U`. -/
  image_subset : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U
  /-- The generalized winding number around every point outside `U` is zero. -/
  winding_zero : ∀ z, z ∉ U → HasGeneralizedWindingNumber γ z 0

/-! ### Basic properties -/

/-- Null-homologicity is monotone in the ambient set: if `γ` is null-homologous in `U`
and `U ⊆ V`, then `γ` is null-homologous in `V`. -/
theorem IsNullHomologous.mono {γ : PiecewiseC1Path x x} {U V : Set ℂ}
    (h : IsNullHomologous γ U) (hUV : U ⊆ V) : IsNullHomologous γ V where
  image_subset t ht := hUV (h.image_subset t ht)
  winding_zero z hz := h.winding_zero z (fun hzU => hz (hUV hzU))

/-- If `γ` is null-homologous in `U` and `z ∉ U`, then the generalized winding number
computed via `generalizedWindingNumber` equals zero. -/
theorem IsNullHomologous.winding_eq_zero {γ : PiecewiseC1Path x x} {U : Set ℂ}
    (h : IsNullHomologous γ U) {z : ℂ} (hz : z ∉ U) :
    generalizedWindingNumber γ z = 0 :=
  (h.winding_zero z hz).eq

/-- If `γ` is null-homologous in `U`, the CPV of `(w - z)⁻¹` vanishes for `z ∉ U`. -/
theorem IsNullHomologous.cauchyPV_eq_zero {γ : PiecewiseC1Path x x} {U : Set ℂ}
    (h : IsNullHomologous γ U) {z : ℂ} (hz : z ∉ U) :
    cauchyPV (fun w => (w - z)⁻¹) γ z = 0 := by
  have hwn := h.winding_zero z hz
  rw [hwn.cauchyPV_eq_two_pi_I_mul, mul_zero]

/-! ### Cauchy's theorem for null-homologous paths -/

/-- **Cauchy's theorem for null-homologous paths in convex domains.**

If `f` is holomorphic on a convex open set `U` and `γ` is a null-homologous closed
piecewise C¹ path, then the contour integral of `f` along `γ` vanishes. -/
theorem IsNullHomologous.contourIntegral_eq_zero {γ : PiecewiseC1Path x x}
    {U : Set ℂ} (h : IsNullHomologous γ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 :=
  γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU hUo hUne hf
    h.image_subset h_int

/-! ### Convexity implies null-homologous -/

/-- **Every closed path in a convex open set is null-homologous.**

Given a closed piecewise C¹ path `γ` in a convex open set `U`, for any `z ∉ U`:
1. The path avoids `z` (since `γ` lies in `U` and `z ∉ U`).
2. By compactness of `[0,1]`, the minimum distance from `γ` to `z` is positive.
3. `hasGeneralizedWindingNumber_of_avoids` reduces the PV-based winding number to
   `(2πi)⁻¹` times the contour integral of `(w - z)⁻¹`.
4. The contour integral vanishes by Cauchy's theorem for convex domains (primitive
   via `DifferentiableOn.hasPrimitive_of_convex` + FTC for closed paths).

The integrability hypothesis is needed for the FTC computation. It holds automatically
for `PiecewiseC1Immersion`s (see `integrand_intervalIntegrable_of_avoids` in the
`GeneralizedResidueTheory` folder) and will be discharged by the caller. -/
theorem isNullHomologous_of_convex (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (hU_ne : U.Nonempty) (γ : PiecewiseC1Path x x)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (h_int : ∀ z, z ∉ U → IntervalIntegrable
      (fun t => (γ t - z)⁻¹ * deriv γ.toPath.extend t) volume 0 1) :
    IsNullHomologous γ U where
  image_subset := hγ_in_U
  winding_zero z hz := by
    -- Step 1: The path avoids z since z ∉ U but γ lies in U
    have h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z :=
      fun t ht heq => hz (heq ▸ hγ_in_U t ht)
    -- Step 2: Compactness gives a positive minimum distance
    have h_norm_cont : ContinuousOn (fun t => ‖γ t - z‖) (Icc 0 1) :=
      (γ.continuous.continuousOn.sub continuousOn_const).norm
    obtain ⟨t₀, ht₀, hmin⟩ :=
      isCompact_Icc.exists_isMinOn ⟨0, left_mem_Icc.mpr zero_le_one⟩ h_norm_cont
    have hδ_pos : 0 < ‖γ t₀ - z‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoids t₀ ht₀))
    -- Step 3: hasGeneralizedWindingNumber_of_avoids gives the winding number value
    have h_gwn := hasGeneralizedWindingNumber_of_avoids
      (γ := γ) (z₀ := z) ⟨‖γ t₀ - z‖, hδ_pos, fun t ht => hmin ht⟩
    -- Step 4: The contour integral of (w - z)⁻¹ vanishes by Cauchy's theorem
    have h_holo : DifferentiableOn ℂ (fun w => (w - z)⁻¹) U := by
      intro w hw
      have : w - z ≠ 0 := sub_ne_zero.mpr (fun heq => hz (heq ▸ hw))
      exact ((differentiableAt_id.sub (differentiableAt_const z)).inv
        this).differentiableWithinAt
    have h_zero : γ.contourIntegral (fun w => (w - z)⁻¹) = 0 :=
      γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl
        hU_convex hU hU_ne h_holo hγ_in_U (h_int z hz)
    -- Step 5: The winding number is (2πi)⁻¹ * 0 = 0
    rwa [h_zero, mul_zero] at h_gwn

/-! ### Direct construction from HasGeneralizedWindingNumber -/

/-- Construct `IsNullHomologous` directly from pointwise winding number witnesses and
an image containment proof. This is useful when the winding number is computed by
other means (e.g., homotopy invariance, direct calculation). -/
theorem isNullHomologous_of_forall_winding_zero
    (γ : PiecewiseC1Path x x) (U : Set ℂ)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hwn : ∀ z, z ∉ U → HasGeneralizedWindingNumber γ z 0) :
    IsNullHomologous γ U where
  image_subset := hγ
  winding_zero := hwn

/-! ### Intersection with open sets -/

/-- If `γ` is null-homologous in both `U` and `V`, then it is null-homologous in `U ∩ V`. -/
theorem IsNullHomologous.inter {γ : PiecewiseC1Path x x} {U V : Set ℂ}
    (hU : IsNullHomologous γ U) (hV : IsNullHomologous γ V) :
    IsNullHomologous γ (U ∩ V) where
  image_subset t ht := ⟨hU.image_subset t ht, hV.image_subset t ht⟩
  winding_zero z hz := by
    simp only [mem_inter_iff, not_and_or] at hz
    cases hz with
    | inl h => exact hU.winding_zero z h
    | inr h => exact hV.winding_zero z h

/-! ### Null-homologous in the whole space -/

/-- Every closed path is null-homologous in `Set.univ`. The winding number condition
is vacuously true since there are no points outside `univ`. -/
theorem isNullHomologous_univ (γ : PiecewiseC1Path x x) :
    IsNullHomologous γ Set.univ where
  image_subset _ _ := mem_univ _
  winding_zero z hz := absurd (mem_univ z) hz

end
