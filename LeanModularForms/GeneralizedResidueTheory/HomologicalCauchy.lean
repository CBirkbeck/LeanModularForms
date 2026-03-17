/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
import LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import LeanModularForms.GeneralizedResidueTheory.Homotopy.Invariance

/-!
# Null-Homologous Curves and the Cauchy Integral Theorem

A closed piecewise C^1 immersion is **null-homologous** in an open set U when its
winding number around every point outside U is zero. This is the topological
condition required by the generalized residue theorem of Hungerbuhler-Wasem.

## Main definitions

* `IsNullHomologous` -- null-homologous curve in an open set

## Main results

* `isNullHomologous_of_convex` -- every closed curve in a convex open set
  is null-homologous (bridge lemma)
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

/-- A closed piecewise C^1 immersion gamma is null-homologous in an open set U if:
1. gamma is a closed curve
2. gamma lies entirely in U
3. The winding number of gamma around every point outside U is zero.

This matches the definition in Hungerbuhler-Wasem (arXiv:1808.00997v2). -/
structure IsNullHomologous (γ : PiecewiseC1Immersion) (U : Set ℂ) : Prop where
  closed : γ.toPiecewiseC1Curve.IsClosed
  image_subset : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U
  winding_zero : ∀ z, z ∉ U →
    generalizedWindingNumber' γ.toFun γ.a γ.b z = 0

/-- The contour integral of a derivative of a composition F circ gamma over a
piecewise C^1 curve equals F(gamma(b)) - F(gamma(a)), when F is holomorphic
on a set containing the image of gamma.

Proof strategy: split the integral along partition points and apply the
standard FTC (`integral_eq_sub_of_hasDerivAt_of_le`) on each smooth subinterval.
On each subinterval [p_i, p_{i+1}], gamma is C^1 hence differentiable, so
F circ gamma has derivative f(gamma(t)) * gamma'(t) by the chain rule, and
the sum telescopes to F(gamma(b)) - F(gamma(a)). -/
private theorem ftc_piecewise_contour
    {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (U : Set ℂ) (_hU : IsOpen U)
    (_hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (_hF_prim : ∀ z ∈ U, HasDerivAt F (f z) z)
    (_h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun γ.b) - F (γ.toFun γ.a) := by
  sorry

/-- The integrand (gamma(t) - z)^{-1} * gamma'(t) is interval integrable when z
is bounded away from the image of gamma.

Proof strategy: gamma is continuous on [a,b] and avoids z, so
|gamma(t) - z|^{-1} is bounded by compactness. The derivative deriv gamma
is bounded on [a,b] off the finite partition (piecewise continuous and
bounded on the compact interval). The product is therefore bounded and
piecewise continuous, hence integrable. -/
private theorem integrand_intervalIntegrable_of_avoids
    (γ : PiecewiseC1Curve) (z : ℂ)
    (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z) :
    IntervalIntegrable
      (fun t => (γ.toFun t - z)⁻¹ * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  -- The inverse factor is continuous on all of [a,b] since gamma avoids z
  have h_inv_cont : ContinuousOn (fun t => (γ.toFun t - z)⁻¹) (Icc γ.a γ.b) :=
    ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
      (fun t ht => sub_ne_zero.mpr (h_avoids t ht))
  -- Get bound for the inverse factor by compactness of image
  obtain ⟨M_inv, hM_inv⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (h_inv_cont.norm)
  -- Get a bound for deriv gamma on [a,b].
  -- deriv gamma t is always a well-defined value (0 by convention if not differentiable).
  -- It is continuous off the finite partition, and takes finitely many values at
  -- partition points, so it is bounded on [a,b].
  have h_deriv_bounded : ∃ M_d : ℝ, ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d := by
    sorry
  obtain ⟨M_d, hM_d⟩ := h_deriv_bounded
  -- Now bound the product
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_inv * M_d) hab
  · -- ContinuousOn off partition
    intro t ⟨ht_Icc, ht_not_part⟩
    apply ContinuousWithinAt.mul
    · exact (h_inv_cont t ht_Icc).mono diff_subset
    · have ht_Ioo : t ∈ Ioo γ.a γ.b := by
        refine ⟨?_, ?_⟩
        · by_contra h_not_lt
          push_neg at h_not_lt
          have : t = γ.a := le_antisymm h_not_lt ht_Icc.1
          rw [this] at ht_not_part
          exact ht_not_part (γ.endpoints_in_partition.1)
        · by_contra h_not_lt
          push_neg at h_not_lt
          have : t = γ.b := le_antisymm ht_Icc.2 h_not_lt
          rw [this] at ht_not_part
          exact ht_not_part (γ.endpoints_in_partition.2)
      exact (γ.deriv_continuous_off_partition t ht_Ioo ht_not_part).continuousWithinAt
  · -- Bound
    intro t ht
    have h1 : ‖(γ.toFun t - z)⁻¹‖ ≤ M_inv := by
      have := hM_inv t ht
      simp only [Real.norm_eq_abs, abs_norm] at this
      exact this
    calc ‖(γ.toFun t - z)⁻¹ * deriv γ.toFun t‖
        = ‖(γ.toFun t - z)⁻¹‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
      _ ≤ M_inv * M_d := by
          exact mul_le_mul h1 (hM_d t ht) (norm_nonneg _)
            (le_trans (norm_nonneg _) h1)

/-- Every closed curve in a convex open set is null-homologous.

The proof uses:
1. `generalizedWindingNumber_eq_classical_away` to reduce the PV winding
   number to a classical contour integral (since z is not on the curve).
2. `holomorphic_convex_primitive` to obtain a primitive F of w |-> (w - z)^{-1}
   on the convex set U.
3. The fundamental theorem of calculus to evaluate the integral as
   F(gamma(b)) - F(gamma(a)) = 0 (since gamma is closed). -/
theorem isNullHomologous_of_convex
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (hU_ne : U.Nonempty)
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    IsNullHomologous γ U where
  closed := hγ_closed
  image_subset := hγ_in_U
  winding_zero := by
    intro z hz
    -- Step 1: z is not on the curve (since the curve is in U and z is not in U)
    have h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z :=
      fun t ht heq => hz (heq ▸ hγ_in_U t ht)
    -- Step 2: Reduce PV winding number to classical integral
    have h_classical := generalizedWindingNumber_eq_classical_away
      γ.toPiecewiseC1Curve z h_avoids
    rw [h_classical]
    -- Step 3: The function w -> (w - z)^{-1} is holomorphic on U
    have h_ne_z : ∀ w ∈ U, w - z ≠ 0 :=
      fun w hw => sub_ne_zero.mpr (fun heq => hz (heq ▸ hw))
    have h_holo : DifferentiableOn ℂ (fun w => (w - z)⁻¹) U := by
      intro w hw
      exact ((differentiableAt_id.sub (differentiableAt_const z)).inv
        (h_ne_z w hw)).differentiableWithinAt
    -- Step 4: Get a primitive F on U via convexity
    obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU hU_ne h_holo
    -- Step 5: Integrability (the integrand is bounded piecewise continuous)
    have h_int := integrand_intervalIntegrable_of_avoids
      γ.toPiecewiseC1Curve z h_avoids
    -- Step 6: By FTC, integral = F(gamma(b)) - F(gamma(a))
    have h_ftc := ftc_piecewise_contour γ.toPiecewiseC1Curve U hU
      hγ_in_U hF h_int
    -- Step 7: gamma is closed, so F(gamma(b)) = F(gamma(a))
    have h_closed_val : F (γ.toFun γ.b) = F (γ.toFun γ.a) :=
      congrArg F hγ_closed.symm
    rw [h_ftc, h_closed_val, sub_self, mul_zero]

end
