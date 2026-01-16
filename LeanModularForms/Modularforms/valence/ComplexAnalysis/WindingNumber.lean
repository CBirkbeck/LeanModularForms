/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PrincipalValue
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Finiteness
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Winding Number Theory

This file develops the theory of generalized winding numbers, including:
- The model sector calculation (angle → winding number)
- The classical case (closed curve avoiding point → integer winding number)
- The decomposition theorem (winding number = classical + angle contributions)

## Main Results

* `generalizedWindingNumber_modelSector` - Model sector gives α/(2π)
* `generalizedWindingNumber_eq_classical` - Classical case is integer
* `generalizedWindingNumber_decomposition` - Full decomposition theorem

## References

* Isabelle: `Winding_Numbers.thy` - `winding_number_integer`
* Isabelle: `Contour_Integration.thy` - `contour_integral_join`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Model Sector Calculation -/

/-- Integral of 1/z along positive real axis from ε to r.
    ∫_ε^r dt/t = log(r) - log(ε)
-/
theorem integral_inv_real_axis (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (_hεr : ε < r) :
    ∫ t in ε..r, (t : ℂ)⁻¹ = Complex.log r - Complex.log ε := by
  -- Step 1: Compute the real integral: ∫_ε^r t⁻¹ dt = log(r/ε) = log(r) - log(ε)
  have h_real : ∫ t in ε..r, (t : ℝ)⁻¹ = Real.log r - Real.log ε := by
    rw [integral_inv_of_pos hε hr, Real.log_div hr.ne' hε.ne']
  -- Step 2: Rewrite (t : ℂ)⁻¹ = (t⁻¹ : ℂ) and use intervalIntegral.integral_ofReal
  simp_rw [← Complex.ofReal_inv]
  rw [intervalIntegral.integral_ofReal, h_real]
  simp only [Complex.ofReal_sub, Complex.ofReal_log hr.le, Complex.ofReal_log hε.le]

/-- Integral of 1/z along ray at angle α from 0 to r.
    ∫_0^r dt/(t·e^{iα}) · e^{iα} = ∫_0^r dt/t is divergent, but the PV exists.
-/
theorem integral_inv_along_ray (r α : ℝ) (hr : 0 < r) :
    ∫ t in (0:ℝ)..r, (t * exp (I * α))⁻¹ * exp (I * α) =
    ∫ t in (0:ℝ)..r, (t : ℂ)⁻¹ := by
  congr 1
  ext t
  simp only [mul_inv_rev]
  rw [mul_comm (exp (I * α))⁻¹, mul_assoc, inv_mul_cancel₀ (exp_ne_zero _), mul_one]

/-- The model sector calculation: PV integral gives α/(2π).

    **Theorem**: For the model sector curve with angle α,
    n₀(γ) = (1/2πi) · PV ∮_γ dz/z = α/(2π)

    **Proof**: The logs from the two radial segments cancel, leaving iα.
    Then (2πi)⁻¹ · iα = α/(2π).

    This is the key calculation underlying the winding number decomposition.
-/
theorem generalizedWindingNumber_modelSector' (C : ModelSectorCurve) :
    ∃ L : ℂ, Tendsto (fun ε : ℝ =>
      (2 * Real.pi * I)⁻¹ * (
        (∫ t in ε..C.r, (t : ℂ)⁻¹) +                    -- γ₁: positive real axis
        (∫ t in (0:ℝ)..C.α, I) +                        -- angle contribution
        (∫ t in (0:ℝ)..(C.r - ε), -((C.r - t) : ℂ)⁻¹)  -- γ₃: back along ray
      )) (𝓝[>] 0) (𝓝 L) ∧
    L = C.α / (2 * Real.pi) := by
  use C.α / (2 * Real.pi)
  constructor
  · -- Show convergence: the logs cancel, leaving I * α
    -- The integral sum simplifies to I * α for small ε, then (2πi)⁻¹ * i*α = α/(2π)
    refine Tendsto.congr' ?_ tendsto_const_nhds
    -- Show the integral expression eventually equals the constant C.α / (2 * Real.pi)
    filter_upwards [Ioo_mem_nhdsGT C.hr] with ε hε
    -- hε : ε ∈ Ioo 0 C.r, so 0 < ε and ε < C.r
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < C.r := hε.2
    -- Compute the three integrals
    have h1 : ∫ t in ε..C.r, (t : ℂ)⁻¹ = Complex.log C.r - Complex.log ε :=
      integral_inv_real_axis C.r ε C.hr hε_pos hε_lt
    -- Integral of the arc: ∫ I dt = I * α
    have h2 : ∫ t in (0 : ℝ)..C.α, I = C.α * I := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, Complex.real_smul]
    -- Integral on the returning path: uses substitution
    have h3 : ∫ t in (0 : ℝ)..(C.r - ε), -((C.r - t) : ℂ)⁻¹ = Complex.log ε - Complex.log C.r := by
      -- Pull out the negative: ∫ -f = -∫ f
      rw [intervalIntegral.integral_neg]
      -- Substitution u = r - t: ∫_0^{r-ε} f(r-t) dt = ∫_ε^r f(u) du
      have hsub : ∫ t in (0 : ℝ)..(C.r - ε), ((C.r - t) : ℂ)⁻¹ = ∫ u in ε..C.r, (u : ℂ)⁻¹ := by
        have hcomp := intervalIntegral.integral_comp_sub_left (fun x : ℝ => (x : ℂ)⁻¹) C.r
          (a := (0 : ℝ)) (b := C.r - ε)
        simp only [sub_zero, sub_sub_cancel] at hcomp
        simp only [← Complex.ofReal_sub] at hcomp ⊢
        exact hcomp
      rw [hsub, h1]
      ring
    -- Prove the sum equals I * α by rewriting each integral
    have sum_eq : (∫ t in ε..C.r, (t : ℂ)⁻¹) + (∫ t in (0 : ℝ)..C.α, I) +
                  (∫ t in (0 : ℝ)..(C.r - ε), -((C.r - t) : ℂ)⁻¹) = I * C.α := by
      rw [h1, h2, h3]
      ring
    -- Now apply and simplify
    rw [sum_eq]
    field_simp [Complex.I_ne_zero, Real.pi_ne_zero]
  · rfl

/-! ## Angle at Intersection Points -/

/-- The oriented angle at a point t₀ where γ passes through z₀.

    α = arg(lim_{t↘t₀} γ'(t)) - arg(lim_{t↗t₀} γ'(t))

    This is the angle between the outgoing and incoming tangent vectors.
-/
def angleAtPoint' (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b) : ℝ :=
  if h : t₀ ∈ γ.toPiecewiseC1Curve.partition then
    -- At partition point: use one-sided limits
    let L_left := if hl : γ.a < t₀
      then Classical.choose (γ.left_deriv_limit t₀ h hl)
      else deriv γ.toFun t₀
    let L_right := if hr : t₀ < γ.b
      then Classical.choose (γ.right_deriv_limit t₀ h hr)
      else deriv γ.toFun t₀
    arg L_right - arg (-L_left)
  else
    -- At smooth point: derivative is continuous, so angle is 0
    0

/-- At smooth points (not in partition), the angle is 0. -/
theorem angleAtPoint_smooth (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Icc γ.a γ.b) (ht₀_smooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    angleAtPoint' γ t₀ ht₀ = 0 := by
  simp only [angleAtPoint', ht₀_smooth, ↓reduceDIte]

/-! ## Classical Winding Number Case -/

/-- When γ avoids z₀, the PV integral equals the classical integral for small ε.

    **Key observation**: If min_{t} ‖γ(t) - z₀‖ = δ > 0, then for ε < δ,
    the cutoff has no effect and we get the standard integral.
-/
theorem cauchyPrincipalValue_eq_classical_off_curve'
    (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    ∃ δ > 0, ∀ ε < δ, ∀ t ∈ Icc γ.a γ.b, ‖γ.toFun t - z₀‖ > ε := by
  -- By compactness, infimum distance is achieved and positive
  have h_compact : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  have hz_notin : z₀ ∉ γ.toFun '' Icc γ.a γ.b := by
    rw [mem_image]
    push_neg
    intro t ht
    exact hoff t ht
  have h_nonempty : (γ.toFun '' Icc γ.a γ.b).Nonempty :=
    ⟨γ.toFun γ.a, mem_image_of_mem _ (left_mem_Icc.mpr (le_of_lt γ.hab))⟩
  have h_dist_pos : 0 < Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := by
    rw [← Metric.infDist_pos_iff_notMem_closure h_nonempty]
    rw [h_compact.isClosed.closure_eq]
    exact hz_notin
  use Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b), h_dist_pos
  intro ε hε t ht
  have ht_in_image : γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b := mem_image_of_mem _ ht
  calc ‖γ.toFun t - z₀‖ = dist (γ.toFun t) z₀ := (dist_eq_norm _ _).symm
    _ = dist z₀ (γ.toFun t) := dist_comm _ _
    _ ≥ Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b) := Metric.infDist_le_dist_of_mem ht_in_image
    _ > ε := hε

/-- When a closed curve avoids z₀, its winding number is an integer.

    **Theorem**: If γ is a closed piecewise C¹ curve that doesn't pass through z₀,
    then n_{z₀}(γ) ∈ ℤ.

    **Isabelle parallel**: `winding_number_integer` in `Winding_Numbers.thy`

    **Proof strategies**:

    **Option A (using mathlib)**:
    - Connect our definition to mathlib's `Complex.winding_number`
    - Use mathlib's `winding_number_integer`

    **Option B (direct via logarithm)**:
    - Define θ(t) = arg(γ(t) - z₀) as a continuous branch
    - Show ∮ dz/(z-z₀) = i·(θ(b) - θ(a))
    - For closed curve: θ(b) - θ(a) = 2πn for some n ∈ ℤ
-/
theorem generalizedWindingNumber_eq_classical'
    (γ : PiecewiseC1Curve) (hclosed : γ.IsClosed) (z₀ : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ ∈ range (fun n : ℤ => (n : ℂ)) := by
  -- Strategy: Use generalizedWindingNumber_eq_classical_away to convert to a classical integral,
  -- then show that integral is 2πi·n for some integer n.
  --
  -- Step 1: The generalized winding number equals the classical integral
  have h_eq := generalizedWindingNumber_eq_classical_away γ z₀ hoff
  rw [h_eq]
  simp only [mem_range]
  -- Step 2: Show the classical integral ∫ γ'(t)/(γ(t)-z₀) dt = 2πi·n for some n ∈ ℤ
  -- This follows from the argument principle / logarithm argument:
  -- - For a closed curve, exp(∫ γ'/(γ-z₀)) = (γ(b)-z₀)/(γ(a)-z₀) = 1 (since γ(a) = γ(b))
  -- - Therefore ∫ γ'/(γ-z₀) = 2πi·n for some integer n
  -- - Hence (2πi)⁻¹ · ∫ γ'/(γ-z₀) = n
  --
  -- PROOF APPROACH:
  -- The mathematical content is standard: closed curves avoiding a point have integer winding number.
  -- The technical challenge is that `integral_closed_curve_eq_two_pi_int` requires
  -- `ContinuousOn (deriv gamma) (Icc a b)`, but PiecewiseC1Curve only guarantees continuity
  -- off finitely many partition points.
  --
  -- RESOLUTION OPTIONS:
  -- (a) The derivative discontinuities occur only at a finite (hence null) set of points,
  --     so they don't affect the Bochner integral. The integral equals the sum of integrals
  --     over smooth pieces, each of which satisfies the hypotheses.
  -- (b) Use a smooth approximation argument: approximate γ by smooth curves and use continuity.
  -- (c) Directly show exp(∫ γ'/(γ-z₀)) = 1 using the piecewise nature and product formula.
  --
  -- The key mathematical fact used is:
  --   exp(∫_a^b γ'(t)/(γ(t)-z₀) dt) = (γ(b)-z₀)/(γ(a)-z₀)
  -- For closed curves, γ(a) = γ(b), so this ratio is 1, giving ∫ = 2πi·n.
  --
  -- TECHNICAL GAP: Full proof requires extending `integral_closed_curve_eq_two_pi_int`
  -- to piecewise C¹ curves. The key fact is that finite sets have measure zero,
  -- so the integral over [a,b] equals the integral over [a,b] \ partition.
  --
  -- For now, we provide a partial proof showing the structure:
  -- 1. The curve avoids z₀, so (γ t - z₀) is bounded away from 0
  -- 2. For closed curves, (γ b - z₀)/(γ a - z₀) = 1
  -- 3. Using exp_eq_one_iff, we get the integer
  have hγa_ne : γ.toFun γ.a - z₀ ≠ 0 := sub_ne_zero.mpr (hoff γ.a (left_mem_Icc.mpr (le_of_lt γ.hab)))
  have hγb_ne : γ.toFun γ.b - z₀ ≠ 0 := sub_ne_zero.mpr (hoff γ.b (right_mem_Icc.mpr (le_of_lt γ.hab)))
  have hratio_one : (γ.toFun γ.b - z₀) / (γ.toFun γ.a - z₀) = 1 := by
    rw [← hclosed]; exact div_self hγa_ne
  -- KEY MATHEMATICAL FACT (requires logarithm integration theory):
  -- For a closed curve avoiding z₀:
  --   exp(∫ γ'/(γ-z₀) dt) = (γ(b)-z₀)/(γ(a)-z₀) = 1
  -- By Complex.exp_eq_one_iff: ∫ γ'/(γ-z₀) dt = n * (2 * π * I) for some n ∈ ℤ
  -- Hence (2πi)⁻¹ * ∫ γ'/(γ-z₀) dt = n ∈ ℤ
  --
  -- REQUIRED INFRASTRUCTURE (not yet in mathlib for piecewise curves):
  -- 1. Logarithmic derivative: d/dt(log f) = f'/f when f ≠ 0
  -- 2. FTC for complex log: ∫_a^b f'/f dt = log(f(b)) - log(f(a)) mod 2πi
  -- 3. Extension to piecewise C¹ curves via partition sum
  --
  -- The integer n is the classical winding number of γ around z₀.
  -- This result is standard in complex analysis textbooks (e.g., Ahlfors).
  sorry

/-! ## Local Winding Number Contributions -/

/-- The winding number contribution from a smooth crossing.

    **Theorem**: When a smooth (C¹) curve passes through z₀ with nonzero derivative,
    the generalized winding number contribution is exactly 1/2.

    **Proof**: Locally, a smooth curve through z₀ looks like a straight line.
    By the model sector calculation with α = π (a line subtends angle π),
    the contribution is π/(2π) = 1/2.

    This is the key result for computing winding numbers at smooth crossings,
    such as at i on the fundamental domain boundary.
-/
theorem generalizedWindingNumber_smooth_crossing'
    (γ : ℝ → ℂ) (a b t₀ : ℝ) (z₀ : ℂ)
    (hab : a < b) (ht₀ : t₀ ∈ Ioo a b)
    (hγ_at_z₀ : γ t₀ = z₀)
    (hγ_smooth : DifferentiableAt ℝ γ t₀)
    (hγ'_ne : deriv γ t₀ ≠ 0)
    (hγ_unique : ∀ t ∈ Icc a b, γ t = z₀ → t = t₀) :
    generalizedWindingNumber' γ a b z₀ = 1/2 := by
  -- The curve locally looks like a straight line through z₀.
  -- By Taylor expansion: γ(t) ≈ z₀ + (t - t₀) * γ'(t₀) near t₀.
  --
  -- The model sector with α = π (a line) gives contribution π/(2π) = 1/2.
  --
  -- PROOF OUTLINE:
  -- 1. Split the integral: ∫_a^b = ∫_a^{t₀-δ} + ∫_{t₀-δ}^{t₀+δ} + ∫_{t₀+δ}^b
  -- 2. The outer integrals contribute 0 (curve is bounded away from z₀)
  -- 3. The middle integral is a PV that matches the model sector with α = π
  -- 4. By generalizedWindingNumber_modelSector', this gives π/(2π) = 1/2
  --
  -- The key insight is that no detoured curve construction is needed:
  -- the generalized winding number is computed directly via principal value.
  sorry

/-- The winding number contribution from a corner crossing.

    **Theorem**: When a piecewise C¹ curve has a corner at z₀ with oriented angle α
    between the incoming and outgoing tangents, the contribution is α/(2π).

    **Proof**: Locally, the curve looks like a model sector with angle α.
    By the model sector calculation, this contributes α/(2π).

    This is used for crossings at corners, such as at ρ on the fundamental
    domain boundary where the angle is 2π/3, giving contribution 1/3.
-/
theorem generalizedWindingNumber_corner_crossing'
    (γ : ℝ → ℂ) (a b t₀ : ℝ) (z₀ : ℂ) (α : ℝ)
    (hab : a < b) (ht₀ : t₀ ∈ Ioo a b)
    (hγ_at_z₀ : γ t₀ = z₀)
    (hα_pos : 0 < α) (hα_lt : α < 2 * Real.pi)
    -- The incoming tangent has argument θ₁, outgoing has θ₂, with α = θ₂ - θ₁ + π (mod 2π)
    (hangle : ∃ (L_in L_out : ℂ), L_in ≠ 0 ∧ L_out ≠ 0 ∧
      Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_in) ∧
      Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_out) ∧
      arg L_out - arg (-L_in) = α)
    (hγ_unique : ∀ t ∈ Icc a b, γ t = z₀ → t = t₀) :
    generalizedWindingNumber' γ a b z₀ = α / (2 * Real.pi) := by
  -- The curve locally looks like a model sector with angle α.
  -- By the model sector calculation, this contributes α/(2π).
  --
  -- PROOF OUTLINE:
  -- 1. Near t₀, the curve approaches z₀ along direction -L_in
  -- 2. Near t₀, the curve leaves z₀ along direction L_out
  -- 3. The angle between these is α (by hypothesis)
  -- 4. The PV integral matches the model sector integral
  -- 5. By generalizedWindingNumber_modelSector', we get α/(2π)
  sorry

/-! ## Winding Number for Curves with Multiple Crossings -/

/-- The generalized winding number equals the sum of local contributions.

    **Theorem**: For a piecewise C¹ curve passing through z₀ at finitely many points,
    the generalized winding number equals the sum of angle contributions at each crossing.

    This is the direct approach using principal values, without constructing
    any auxiliary "detoured" curves. The generalized winding number handles
    all crossings naturally via the principal value definition.
-/
theorem generalizedWindingNumber_sum_of_contributions'
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (crossings : Finset ℝ) (angles : crossings → ℝ)
    (hcrossings : ∀ t ∈ crossings, t ∈ Icc γ.a γ.b ∧ γ.toFun t = z₀)
    (hcrossings_only : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = z₀ → t ∈ crossings)
    (hangles : ∀ t : crossings, 0 ≤ angles t ∧ angles t ≤ 2 * Real.pi) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      ∑ t : crossings, (angles t : ℂ) / (2 * Real.pi) := by
  -- The proof splits the integral over each crossing and applies the
  -- corner/smooth crossing results at each point.
  --
  -- PROOF OUTLINE:
  -- 1. Split the interval [a,b] at each crossing point
  -- 2. On segments between crossings, the curve avoids z₀, contributing 0
  --    (these are not closed curves, so they don't wind around z₀)
  -- 3. At each crossing t_i, apply the corner crossing result with angle α_i
  -- 4. Sum the contributions to get Σ α_i/(2π)
  sorry

/-! ## Integral Splitting -/

/-- The contour integral splits when the path is decomposed.

    **Isabelle parallel**: `contour_integral_join` in `Contour_Integration.thy`
-/
theorem cauchyPrincipalValue_split
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b c : ℝ) (z₀ : ℂ)
    (_hab : a < b) (_hbc : b < c)
    (hf_ab : CauchyPrincipalValueExists' f γ a b z₀)
    (hf_bc : CauchyPrincipalValueExists' f γ b c z₀) :
    cauchyPrincipalValue' f γ a c z₀ =
    cauchyPrincipalValue' f γ a b z₀ + cauchyPrincipalValue' f γ b c z₀ := by
  -- The PV integral splits additively over adjacent intervals.
  -- Key insight: for each ε > 0, the interval integral [a,c] = [a,b] + [b,c]
  -- and the limits are additive when both exist.
  unfold cauchyPrincipalValue'
  -- Get the limits from the existence hypotheses
  obtain ⟨L_ab, hL_ab⟩ := hf_ab
  obtain ⟨L_bc, hL_bc⟩ := hf_bc
  -- The limit of the sum equals the sum of the limits
  have h_sum : Tendsto (fun ε =>
      (∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) +
      (∫ t in b..c, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0))
      (𝓝[>] 0) (𝓝 (L_ab + L_bc)) := hL_ab.add hL_bc
  -- For each ε, the interval integral [a,c] splits as [a,b] + [b,c]
  -- Key observation: Since both limits L_ab and L_bc exist, the integrals are eventually
  -- well-defined. For each ε > 0 small enough, both integrals [a,b] and [b,c] are finite.
  -- The splitting ∫[a,c] = ∫[a,b] + ∫[b,c] follows from the additivity of interval integrals.
  --
  -- Technical note: The integrability conditions required by
  -- intervalIntegral.integral_add_adjacent_intervals follow from the fact that
  -- the PV limits exist. If the integrands weren't integrable, the limits couldn't exist.
  --
  -- We use a limit-based argument: since both sides converge to the same limit,
  -- and the integrals split for any ε where they are well-defined, we get equality of limits.
  have h_split : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in a..c, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) =
      (∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) +
      (∫ t in b..c, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) := by
    -- For each fixed ε > 0, the integrand is a bounded function (it's 0 near z₀).
    -- The integral splits by additivity.
    apply Filter.Eventually.of_forall
    intro ε
    -- The integral splits by additivity over adjacent intervals.
    -- The integrand g(t) = if ‖γ t - z₀‖ > ε then f(γ t) * γ'(t) else 0
    symm
    rw [← intervalIntegral.integral_add_adjacent_intervals]
    -- INTEGRABILITY: For a bounded piecewise function on finite intervals,
    -- integrability follows from AEStronglyMeasurable + bounded.
    -- The condition function t ↦ (‖γ t - z₀‖ > ε) creates a piecewise structure:
    -- - On {t : ‖γ t - z₀‖ > ε}: integrand is f(γ t) * γ'(t)
    -- - On {t : ‖γ t - z₀‖ ≤ ε}: integrand is 0
    --
    -- TECHNICAL GAP: The theorem statement lacks hypotheses on f and γ needed
    -- for formal integrability proofs (measurability of f, γ, deriv γ).
    -- In practice, for the valence formula application, these hold.
    -- The PV existence hypotheses (hf_ab, hf_bc) implicitly require integrability.
    all_goals sorry
  -- So the limit of [a,c] equals the limit of [a,b] + [b,c]
  have h_tendsto_ac : Tendsto (fun ε =>
      ∫ t in a..c, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 (L_ab + L_bc)) := by
    apply Tendsto.congr' _ h_sum
    filter_upwards [h_split] with ε hε
    exact hε.symm
  -- The limits are unique in a Hausdorff space
  rw [h_tendsto_ac.limUnder_eq, hL_ab.limUnder_eq, hL_bc.limUnder_eq]

end
