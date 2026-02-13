/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PiecewiseHomotopy

/-!
# Fundamental Domain Boundary

This file contains the canonical definitions of the fundamental domain boundary curve
and its segments for the valence formula.

## Contents

- `H_height`: The height cutoff for the finite-height approximation
- `fdBoundary`: The closed boundary curve parameterized over [0, 5]
- `fdPolygon`: The polygon approximation (replacing arcs with chords)
- Segment definitions and geometric lemmas
- Continuity and closedness proofs

## Parameterization

The boundary is parameterized CLOCKWISE (negative orientation, winding = -1) over [0, 5]:
- t ∈ [0, 1]: right vertical from (1/2 + Hi) DOWN to ρ' (interior to the LEFT → clockwise)
- t ∈ [1, 2]: arc from ρ' to i (on unit circle, angle π/3 → π/2)
- t ∈ [2, 3]: arc from i to ρ (on unit circle, angle π/2 → 2π/3)
- t ∈ [3, 4]: left vertical from ρ UP to (-1/2 + Hi)
- t ∈ [4, 5]: horizontal from (-1/2 + Hi) RIGHT to (1/2 + Hi)

Note: The FD interior (points with |Re| < 1/2, Im > 0, |z| > 1) lies to the RIGHT
of the curve as we traverse it, making this a CLOCKWISE orientation.

where H = √3/2 + 1.

## Imports

This file imports `ValenceFormulaDefinitions` for the elliptic points and fundamental
domain definition. All other valence files should import this file for boundary
definitions rather than defining their own.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval UpperHalfPlane

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Height Cutoff -/

/-- The height cutoff for the finite-height boundary approximation.
    H = √3/2 + 1 ≈ 1.866, which is well above the elliptic points. -/
def H_height : ℝ := Real.sqrt 3 / 2 + 1

/-- H > 1 -/
theorem H_height_gt_one : H_height > 1 := by
  unfold H_height
  have h : Real.sqrt 3 / 2 > 0 := by positivity
  linarith

/-- H > √3/2 (height of ρ and ρ') -/
theorem H_height_gt_rho_height : H_height > Real.sqrt 3 / 2 := by
  unfold H_height; linarith

/-! ## Boundary Curve Definition -/

/-- The closed boundary curve of the fundamental domain, parameterized over [0, 5].
    Traversed CLOCKWISE (negative orientation, winding number = -1 for interior points). -/
def fdBoundary : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    -- Segment 1: vertical from (1/2 + Hi) down to ρ' = (1/2 + √3/2·i)
    1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    -- Segment 2: arc from ρ' to i (counterclockwise, angle π/3 → π/2)
    Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    -- Segment 3: arc from i to ρ (counterclockwise, angle π/2 → 2π/3)
    Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -- Segment 4: vertical from ρ up to (-1/2 + Hi)
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I
  else
    -- Segment 5: horizontal from (-1/2 + Hi) to (1/2 + Hi)
    (t - 9/2) + H_height * I

/-- The polygon approximation of the boundary (replacing arcs with chords). -/
def fdPolygon : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    -- Segment 1: vertical from (1/2 + Hi) down to ρ'
    1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    -- Segment 2: chord from ρ' to i
    ellipticPoint_rho_plus_one + (t - 1) * (I - ellipticPoint_rho_plus_one)
  else if t ≤ 3 then
    -- Segment 3: chord from i to ρ
    I + (t - 2) * (ellipticPoint_rho - I)
  else if t ≤ 4 then
    -- Segment 4: vertical from ρ up to (-1/2 + Hi)
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I
  else
    -- Segment 5: horizontal from (-1/2 + Hi) to (1/2 + Hi)
    (t - 9/2) + H_height * I

/-! ## Boundary Values at Key Points -/

theorem fdBoundary_at_zero : fdBoundary 0 = (1/2 : ℂ) + H_height * I := by
  simp only [fdBoundary]
  -- 0 ≤ 1, so we're in segment 1
  have h : (0 : ℝ) ≤ 1 := by norm_num
  simp only [h, ↓reduceIte]
  -- seg1(0) = 1/2 + (H - 0*(H - √3/2))*I = 1/2 + H*I
  -- Simplify the complex expression
  congr 1
  -- Goal: (↑H_height - ↑0 * (↑H_height - ↑√3 / 2)) * I = ↑H_height * I
  congr 1
  -- Goal: ↑H_height - ↑0 * (↑H_height - ↑√3 / 2) = ↑H_height
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]

theorem fdBoundary_at_one : fdBoundary 1 = ellipticPoint_rho_plus_one := by
  simp only [fdBoundary, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  -- 1 ≤ 1, so we're in segment 1
  have h : (1 : ℝ) ≤ 1 := le_refl 1
  simp only [h, ↓reduceIte]
  -- seg1(1) = 1/2 + (H - 1*(H - √3/2))*I = 1/2 + √3/2*I
  congr 1
  -- Goal: (↑H_height - ↑1 * (↑H_height - ↑√3 / 2)) * I = ↑√3 / 2 * I
  congr 1
  -- Goal: ↑H_height - ↑1 * (↑H_height - ↑√3 / 2) = ↑√3 / 2
  simp only [Complex.ofReal_one, one_mul]
  ring

theorem fdBoundary_at_two : fdBoundary 2 = I := by
  simp only [fdBoundary]
  -- 2 > 1 and 2 ≤ 2, so we're in segment 2
  have h1 : ¬((2 : ℝ) ≤ 1) := by norm_num
  have h2 : (2 : ℝ) ≤ 2 := le_refl 2
  simp only [h1, ↓reduceIte, h2]
  -- seg2(2) = exp((π/3 + (2-1)*(π/2 - π/3))*I) = exp((π/3 + π/6)*I) = exp(π/2*I) = i
  -- First show the angle simplifies to π/2
  have h_angle : (↑Real.pi / 3 + (↑(2:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) =
      ↑Real.pi / 2 := by
    push_cast; ring
  rw [h_angle]
  -- exp((π/2) * I) = i
  -- Note: the goal is cexp (↑π/2 * I) = I
  rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  simp

theorem fdBoundary_at_three : fdBoundary 3 = ellipticPoint_rho := by
  simp only [fdBoundary, ellipticPoint_rho, ellipticPoint_rho']
  -- 3 > 1, 3 > 2, 3 ≤ 3, so we're in segment 3
  have h1 : ¬((3 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((3 : ℝ) ≤ 2) := by norm_num
  have h3 : (3 : ℝ) ≤ 3 := le_refl 3
  simp only [h1, ↓reduceIte, h2, h3]
  -- seg3(3) = exp((π/2 + (3-2)*(2π/3 - π/2))*I) = exp(2π/3 * I) = ρ
  -- First show the angle simplifies to 2π/3
  have h_angle : (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) =
      2 * ↑Real.pi / 3 := by push_cast; ring
  rw [h_angle]
  -- exp(2πi/3) = cos(2π/3) + i*sin(2π/3) = -1/2 + (√3/2)*i
  rw [Complex.exp_mul_I]
  -- Prove cos(2π/3) = -1/2 using cos(π - x) = -cos(x)
  have h_cos : Real.cos (2 * Real.pi / 3) = -1/2 := by
    have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
  -- Prove sin(2π/3) = √3/2 using sin(π - x) = sin(x)
  have h_sin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]
  -- Convert Complex cos/sin to Real cos/sin
  have h2π3 : (2 * ↑Real.pi / 3 : ℂ) = ↑(2 * Real.pi / 3 : ℝ) := by push_cast; ring
  rw [h2π3, ← Complex.ofReal_cos, ← Complex.ofReal_sin, h_cos, h_sin]
  -- Now goal is: ↑(-1/2) + ↑(√3/2) * I = ↑⟨-1/2 + ↑√3/2 * I, proof⟩
  -- The RHS is a subtype coercion which extracts the underlying complex value
  simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  -- Goal: -1/2 + ↑√3/2 * I = ↑⟨-1/2 + ↑√3/2 * I, _⟩ - this is rfl
  rfl

theorem fdBoundary_at_four : fdBoundary 4 = -1/2 + H_height * I := by
  simp only [fdBoundary]
  -- 4 > 1, 4 > 2, 4 > 3, 4 ≤ 4, so we're in segment 4
  have h1 : ¬((4 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((4 : ℝ) ≤ 2) := by norm_num
  have h3 : ¬((4 : ℝ) ≤ 3) := by norm_num
  have h4 : (4 : ℝ) ≤ 4 := le_refl 4
  simp only [h1, ↓reduceIte, h2, h3, h4]
  -- seg4(4) = -1/2 + (√3/2 + (4-3)*(H - √3/2))*I = -1/2 + H*I
  congr 1
  -- Goal: (↑√3/2 + (↑4 - 3) * (↑H - ↑√3/2)) * I = ↑H * I
  congr 1
  -- Goal: ↑√3/2 + (↑4 - 3) * (↑H - ↑√3/2) = ↑H
  have h_real : (Real.sqrt 3 / 2 : ℂ) + ((4 : ℂ) - 3) * ((H_height : ℂ) - Real.sqrt 3 / 2) =
      (H_height : ℂ) := by
    ring
  exact h_real

theorem fdBoundary_at_five : fdBoundary 5 = (1/2 : ℂ) + H_height * I := by
  simp only [fdBoundary]
  -- 5 > 1, 5 > 2, 5 > 3, 5 > 4, so we're in segment 5
  have h1 : ¬((5 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((5 : ℝ) ≤ 2) := by norm_num
  have h3 : ¬((5 : ℝ) ≤ 3) := by norm_num
  have h4 : ¬((5 : ℝ) ≤ 4) := by norm_num
  simp only [h1, ↓reduceIte, h2, h3, h4]
  -- seg5(5) = (5 - 9/2) + H*I = 1/2 + H*I
  congr 1
  -- Goal: ↑5 - 9/2 = 1/2
  norm_cast
  norm_num

/-- The boundary curve is closed. -/
theorem fdBoundary_closed : fdBoundary 0 = fdBoundary 5 := by
  rw [fdBoundary_at_zero, fdBoundary_at_five]

/-! ## Polygon Values at Key Points -/

theorem fdPolygon_at_zero : fdPolygon 0 = (1/2 : ℂ) + H_height * I := by
  simp only [fdPolygon]
  have h : (0 : ℝ) ≤ 1 := by norm_num
  simp only [h, ↓reduceIte, Complex.ofReal_zero, zero_mul, sub_zero]

theorem fdPolygon_at_one : fdPolygon 1 = ellipticPoint_rho_plus_one := by
  simp only [fdPolygon, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  have h : (1 : ℝ) ≤ 1 := le_refl 1
  simp only [h, ↓reduceIte, Complex.ofReal_one, one_mul]
  congr 1
  simp only [H_height]
  ring

theorem fdPolygon_at_two : fdPolygon 2 = I := by
  -- Direct computation: ellipticPoint_rho_plus_one + 1 * (I - ellipticPoint_rho_plus_one) = I
  simp only [fdPolygon]
  have h1 : ¬((2 : ℝ) ≤ 1) := by norm_num
  have h2 : (2 : ℝ) ≤ 2 := le_refl 2
  simp only [h1, ↓reduceIte, h2]
  -- Goal: ellipticPoint_rho_plus_one + (↑2 - 1) * (I - ellipticPoint_rho_plus_one) = I
  -- Simplify: (2:ℝ) - 1 = 1
  have h : (↑(2 : ℝ) : ℂ) - 1 = 1 := by norm_num
  rw [h]; ring

theorem fdPolygon_at_three : fdPolygon 3 = ellipticPoint_rho := by
  -- Direct computation: I + 1 * (ellipticPoint_rho - I) = ellipticPoint_rho
  simp only [fdPolygon]
  have h1 : ¬((3 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((3 : ℝ) ≤ 2) := by norm_num
  have h3 : (3 : ℝ) ≤ 3 := le_refl 3
  simp only [h1, ↓reduceIte, h2, h3]
  -- Goal: I + (↑3 - 2) * (ellipticPoint_rho - I) = ellipticPoint_rho
  -- Simplify: (3:ℝ) - 2 = 1
  have h : (↑(3 : ℝ) : ℂ) - 2 = 1 := by norm_num
  rw [h]; ring

theorem fdPolygon_at_four : fdPolygon 4 = -1/2 + H_height * I := by
  -- Direct computation: √3/2 + 1*(H - √3/2) = H
  simp only [fdPolygon]
  have h1 : ¬((4 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((4 : ℝ) ≤ 2) := by norm_num
  have h3 : ¬((4 : ℝ) ≤ 3) := by norm_num
  have h4 : (4 : ℝ) ≤ 4 := le_refl 4
  simp only [h1, ↓reduceIte, h2, h3, h4]
  -- seg4(4) = -1/2 + (√3/2 + (4-3)*(H - √3/2))*I = -1/2 + H*I
  congr 1
  -- Goal: (√3/2 + (↑4 - 3)*(H - √3/2)) * I = H * I
  -- Simplify: (4:ℝ) - 3 = 1
  have h : (↑(4 : ℝ) : ℂ) - 3 = 1 := by norm_num
  rw [h]; ring

theorem fdPolygon_at_five : fdPolygon 5 = (1/2 : ℂ) + H_height * I := by
  simp only [fdPolygon]
  have h1 : ¬((5 : ℝ) ≤ 1) := by norm_num
  have h2 : ¬((5 : ℝ) ≤ 2) := by norm_num
  have h3 : ¬((5 : ℝ) ≤ 3) := by norm_num
  have h4 : ¬((5 : ℝ) ≤ 4) := by norm_num
  simp only [h1, ↓reduceIte, h2, h3, h4]
  -- (5 - 9/2) + H*I = 1/2 + H*I
  congr 1
  norm_cast; norm_num

/-- The polygon is closed. -/
theorem fdPolygon_closed : fdPolygon 0 = fdPolygon 5 := by
  rw [fdPolygon_at_zero, fdPolygon_at_five]

/-! ## Continuity -/

theorem fdBoundary_continuous : Continuous fdBoundary := by
  -- Apply Continuous.if recursively for each segment
  apply Continuous.if
  -- Case 1: Matching at t = 1
  · intro t ht
    rw [show {t : ℝ | t ≤ 1} = Set.Iic 1 from rfl, frontier_Iic] at ht
    simp only [mem_singleton_iff] at ht
    subst ht
    -- At t = 1: need to show seg1(1) = seg2(1)
    -- After reduceIte on both branches at t=1
    simp only [show (1:ℝ) ≤ 2 from by norm_num, ↓reduceIte]
    -- LHS: 1/2 + (H_height - 1*(H_height - √3/2))*I
    -- RHS: exp((π/3 + (1-1)*(π/2 - π/3))*I)
    -- Simplify and convert to canonical form
    have h_angle : (↑Real.pi / 3 + (↑(1:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) = ↑Real.pi / 3 := by push_cast; ring
    rw [h_angle, Complex.exp_mul_I]
    have h_cos : Complex.cos (↑Real.pi / 3 : ℂ) = 1/2 := by
      have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [heq, ← Complex.ofReal_cos, Real.cos_pi_div_three]; norm_num
    have h_sin : Complex.sin (↑Real.pi / 3 : ℂ) = ↑(Real.sqrt 3) / 2 := by
      have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      rw [heq, ← Complex.ofReal_sin, Real.sin_pi_div_three]; push_cast; ring
    rw [h_cos, h_sin]
    -- Now prove LHS = 1/2 + √3/2*I: H - 1*(H - √3/2) = √3/2
    simp only [Complex.ofReal_one, one_mul, sub_sub_cancel]
  -- Continuity of segment 1
  · exact Continuous.add continuous_const (Continuous.mul (Continuous.sub continuous_const
      (Continuous.mul continuous_ofReal continuous_const)) continuous_const)
  -- Nested if for remaining segments
  · apply Continuous.if
    -- Case 2: Matching at t = 2
    · intro t ht
      rw [show {t : ℝ | t ≤ 2} = Set.Iic 2 from rfl, frontier_Iic] at ht
      simp only [mem_singleton_iff] at ht
      subst ht
      simp only [show (2:ℝ) ≤ 3 from by norm_num, ↓reduceIte]
      -- Both sides should equal exp(π/2·i) = i
      congr 1
      have lhs_simp : (↑Real.pi / 3 + (↑(2:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ)
                    = ↑Real.pi / 2 := by push_cast; field_simp; ring
      have rhs_simp : (↑Real.pi / 2 + (↑(2:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ)
                    = ↑Real.pi / 2 := by push_cast; field_simp; ring
      rw [lhs_simp, rhs_simp]
    -- Continuity of segment 2
    · apply Continuous.cexp
      apply Continuous.mul _ continuous_const
      apply Continuous.add continuous_const
      exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
    -- Nested if for remaining segments
    · apply Continuous.if
      -- Case 3: Matching at t = 3
      · intro t ht
        rw [show {t : ℝ | t ≤ 3} = Set.Iic 3 from rfl, frontier_Iic] at ht
        simp only [mem_singleton_iff] at ht
        subst ht
        -- At t = 3: seg3(3) = exp(2π/3·i) = seg4(3) = -1/2 + √3/2·i
        have lhs_simp : (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ)
                      = 2 * ↑Real.pi / 3 := by push_cast; field_simp; ring
        have rhs_simp : (↑(Real.sqrt 3) / 2 + (↑(3:ℝ) - 3) * (H_height - ↑(Real.sqrt 3) / 2) : ℂ)
                      = ↑(Real.sqrt 3) / 2 := by push_cast; ring
        conv_lhs => rw [lhs_simp]
        conv_rhs => rw [rhs_simp]
        rw [Complex.exp_mul_I]
        have h_cos : Complex.cos (2 * ↑Real.pi / 3 : ℂ) = -1/2 := by
          have h1 : (2 * ↑Real.pi / 3 : ℂ) = ↑Real.pi - ↑Real.pi / 3 := by push_cast; ring
          rw [h1, Complex.cos_sub, Complex.cos_pi, Complex.sin_pi]
          have h2 : Complex.cos (↑Real.pi / 3 : ℂ) = (1 / 2 : ℂ) := by
            have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
            rw [heq, ← Complex.ofReal_cos, Real.cos_pi_div_three]; norm_num
          rw [h2]; ring
        have h_sin : Complex.sin (2 * ↑Real.pi / 3 : ℂ) = ↑(Real.sqrt 3) / 2 := by
          have h1 : (2 * ↑Real.pi / 3 : ℂ) = ↑Real.pi - ↑Real.pi / 3 := by push_cast; ring
          rw [h1, Complex.sin_sub, Complex.sin_pi, Complex.cos_pi]
          have h2 : Complex.sin (↑Real.pi / 3 : ℂ) = ↑(Real.sqrt 3) / 2 := by
            have heq : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
            rw [heq, ← Complex.ofReal_sin, Real.sin_pi_div_three]; push_cast; ring
          rw [h2]; ring
        rw [h_cos, h_sin]
        simp only [show (3:ℝ) ≤ 4 from by norm_num, ↓reduceIte]
      -- Continuity of segment 3
      · apply Continuous.cexp
        apply Continuous.mul _ continuous_const
        apply Continuous.add continuous_const
        exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
      -- Nested if for final segments
      · apply Continuous.if
        -- Case 4: Matching at t = 4
        · intro t ht
          rw [show {t : ℝ | t ≤ 4} = Set.Iic 4 from rfl, frontier_Iic] at ht
          simp only [mem_singleton_iff] at ht
          subst ht
          -- At t = 4: seg4(4) = -1/2 + H·i = seg5(4)
          have lhs_simp : (↑(Real.sqrt 3) / 2 + (↑(4:ℝ) - 3) * (H_height - ↑(Real.sqrt 3) / 2) : ℂ)
                        = ↑H_height := by push_cast; ring
          have rhs_simp : ((↑(4:ℝ) : ℂ) - 9/2 : ℂ) = -1/2 := by push_cast; ring
          conv_lhs => rw [lhs_simp]
          conv_rhs => rw [rhs_simp]
        -- Continuity of segment 4
        · apply Continuous.add continuous_const
          apply Continuous.mul _ continuous_const
          apply Continuous.add continuous_const
          exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
        -- Continuity of segment 5 (final segment)
        · apply Continuous.add _ continuous_const
          exact continuous_ofReal.sub continuous_const

theorem fdPolygon_continuous : Continuous fdPolygon := by
  -- Apply Continuous.if recursively for each segment
  apply Continuous.if
  -- Case 1: Matching at t = 1
  · intro t ht
    rw [show {t : ℝ | t ≤ 1} = Set.Iic 1 from rfl, frontier_Iic] at ht
    simp only [mem_singleton_iff] at ht
    subst ht
    -- At t = 1: both pieces equal ellipticPoint_rho_plus_one
    simp only [show (1:ℝ) ≤ 2 from by norm_num, ↓reduceIte]
    simp only [Complex.ofReal_one, one_mul, sub_self, zero_mul, add_zero, sub_sub_cancel]
    simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']; rfl
  -- Continuity of segment 1: linear function
  · exact Continuous.add continuous_const (Continuous.mul (Continuous.sub continuous_const
      (Continuous.mul continuous_ofReal continuous_const)) continuous_const)
  -- Nested if for remaining segments
  · apply Continuous.if
    -- Case 2: Matching at t = 2
    · intro t ht
      rw [show {t : ℝ | t ≤ 2} = Set.Iic 2 from rfl, frontier_Iic] at ht
      simp only [mem_singleton_iff] at ht
      subst ht
      simp only [show (2:ℝ) ≤ 3 from by norm_num, ↓reduceIte]
      -- Both pieces equal I at t = 2
      simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
        ellipticPoint_rho, ellipticPoint_rho']; push_cast; ring
    -- Continuity of segment 2: linear interpolation
    · apply Continuous.add continuous_const
      exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
    -- Nested if for remaining segments
    · apply Continuous.if
      -- Case 3: Matching at t = 3
      · intro t ht
        rw [show {t : ℝ | t ≤ 3} = Set.Iic 3 from rfl, frontier_Iic] at ht
        simp only [mem_singleton_iff] at ht
        subst ht
        -- Both pieces equal ellipticPoint_rho at t = 3
        simp only [show (3:ℝ) ≤ 4 from by norm_num, ↓reduceIte]
        have hrho : (ellipticPoint_rho : ℂ) = -1/2 + ↑(Real.sqrt 3)/2 * I := by
          simp only [ellipticPoint_rho, ellipticPoint_rho']; rfl
        rw [hrho]; push_cast; ring
      -- Continuity of segment 3: linear interpolation
      · apply Continuous.add continuous_const
        exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
      -- Nested if for final segments
      · apply Continuous.if
        -- Case 4: Matching at t = 4
        · intro t ht
          rw [show {t : ℝ | t ≤ 4} = Set.Iic 4 from rfl, frontier_Iic] at ht
          simp only [mem_singleton_iff] at ht
          subst ht
          -- Both pieces equal -1/2 + H·i at t = 4
          push_cast; ring
        -- Continuity of segment 4: linear function
        · apply Continuous.add continuous_const
          apply Continuous.mul _ continuous_const
          apply Continuous.add continuous_const
          exact Continuous.mul (continuous_ofReal.sub continuous_const) continuous_const
        -- Continuity of segment 5 (final segment): linear function
        · apply Continuous.add _ continuous_const
          exact continuous_ofReal.sub continuous_const

/-! ## Segment Definitions (for decomposition) -/

/-- Segment 1: right vertical from (1/2 + Hi) down to ρ' -/
def fdBoundary_seg1 : ℝ → ℂ := fun t =>
  1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I

/-- Segment 2: arc from ρ' to i -/
def fdBoundary_seg2 : ℝ → ℂ := fun t =>
  Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)

/-- Segment 3: arc from i to ρ -/
def fdBoundary_seg3 : ℝ → ℂ := fun t =>
  Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)

/-- Segment 4: left vertical from ρ up to (-1/2 + Hi) -/
def fdBoundary_seg4 : ℝ → ℂ := fun t =>
  -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I

/-- Segment 5: horizontal from (-1/2 + Hi) to (1/2 + Hi) -/
def fdBoundary_seg5 : ℝ → ℂ := fun t =>
  (t - 9/2) + H_height * I

/-! ## Partition Points -/

/-- The partition points where the boundary changes segments. -/
def fdPartition : Finset ℝ := {1, 2, 3, 4}

/-- The corner partition points where the curve is NOT differentiable.
    Note: t=2 is NOT a corner because segments 2 and 3 (both arcs on unit circle)
    meet smoothly at i with the same angular speed (π/6 per unit t). -/
def fdCornerPartition : Finset ℝ := {1, 3, 4}

/-- At corner partition points {1, 3, 4}, the curve has corners (non-differentiable).
    These are the points where adjacent segments have different derivatives. -/
theorem fdBoundary_corner_at_cornerPartition (t : ℝ) (ht : t ∈ fdCornerPartition) :
    ¬DifferentiableAt ℝ fdBoundary t := by
  simp only [fdCornerPartition, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl
  · -- Case t = 1: seg1 (affine) meets seg2 (exp). Left deriv ∝ I, right deriv ∝ exp * I
    intro hd
    -- Left derivative from seg1: d/dt [1/2 + (H - t*(H-√3/2))*I] = -(H-√3/2)*I
    have h_left : HasDerivWithinAt fdBoundary (↑(-(H_height - Real.sqrt 3 / 2)) * I) (Iic 1) 1 := by
      have hda : HasDerivAt (fun t : ℝ => (1:ℂ)/2 + (↑(H_height - t * (H_height - Real.sqrt 3 / 2))) * I)
          (↑(-(H_height - Real.sqrt 3 / 2)) * I) 1 := by
        have hg : HasDerivAt (fun t : ℝ => H_height - t * (H_height - Real.sqrt 3 / 2))
            (-(H_height - Real.sqrt 3 / 2)) 1 := by
          rw [show (fun t : ℝ => H_height - t * (H_height - Real.sqrt 3 / 2))
            = (fun t => -(H_height - Real.sqrt 3 / 2) * t + H_height) from by ext t; ring]
          simpa using ((hasDerivAt_id (1:ℝ)).const_mul
            (-(H_height - Real.sqrt 3 / 2))).add_const H_height
        exact (hg.ofReal_comp.mul_const I).const_add _
      exact hda.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        (by filter_upwards [self_mem_nhdsWithin] with s hs
            simp only [fdBoundary, if_pos (mem_Iic.mp hs)]
            congr 1; congr 1; push_cast; ring)
        right_mem_Iic
    -- Right derivative from seg2: d/dt [exp((π/3 + (t-1)*(π/2-π/3))*I)] at t=1
    -- = exp(π/3*I) * (π/2-π/3)*I = exp(π/3*I) * (π/6)*I
    have h_right : HasDerivWithinAt fdBoundary
        (Complex.exp ((↑(Real.pi / 3) : ℂ) * I) * (↑(Real.pi / 2 - Real.pi / 3) * I))
        (Ici 1) 1 := by
      have h_inner : HasDerivAt
          (fun t : ℝ => (↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I)
          (↑(Real.pi / 2 - Real.pi / 3) * I) 1 := by
        have h1 := ((hasDerivAt_id (1:ℝ)).sub_const 1).mul_const (Real.pi / 2 - Real.pi / 3)
        simp only [one_mul] at h1
        exact ((h1.const_add _).ofReal_comp.mul_const I)
      have hda := h_inner.cexp

      have h_val : Real.pi / 3 + ((1:ℝ) - 1) * (Real.pi / 2 - Real.pi / 3) = Real.pi / 3 := by ring
      rw [h_val] at hda
      exact hda.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        (by filter_upwards [Ico_mem_nhdsGE (show (1:ℝ) < 2 by norm_num)] with s hs
            have hsm := mem_Ico.mp hs
            simp only [fdBoundary]
            by_cases h1 : s ≤ 1
            · have heq : s = 1 := le_antisymm h1 hsm.1; subst heq
              simp only [le_refl, ↓reduceIte, sub_self, zero_mul, add_zero]
              rw [show (↑(Real.pi / 3) : ℂ) * I = ↑(Real.pi / 3) * I from rfl]
              rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
                Real.cos_pi_div_three, Real.sin_pi_div_three]
              push_cast; ring
            · push_neg at h1
              simp only [show ¬(s ≤ 1) from not_le.mpr h1, ↓reduceIte, if_pos hsm.2.le]
              congr 1; congr 1; push_cast; ring)
        left_mem_Ici
    -- Now derive contradiction: both equal deriv fdBoundary 1
    have eq_L := (uniqueDiffWithinAt_Iic (1:ℝ)).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h_left
    have eq_R := (uniqueDiffWithinAt_Ici (1:ℝ)).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h_right
    -- So -(H-√3/2)*I = exp(π/3*I) * (π/2-π/3)*I
    have h_eq : (↑(-(H_height - Real.sqrt 3 / 2)) : ℂ) * I =
        Complex.exp ((↑(Real.pi / 3) : ℂ) * I) * (↑(Real.pi / 2 - Real.pi / 3) * I) := by
      rw [← eq_L, ← eq_R]
    -- Compare norms: LHS norm = |-(H-√3/2)| = 1, RHS norm = |π/6|
    have h_norm_L : ‖(↑(-(H_height - Real.sqrt 3 / 2)) : ℂ) * I‖ =
        |-(H_height - Real.sqrt 3 / 2)| := by
      rw [norm_mul, norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have h_norm_R : ‖Complex.exp ((↑(Real.pi / 3) : ℂ) * I) *
        (↑(Real.pi / 2 - Real.pi / 3) * I)‖ = |Real.pi / 2 - Real.pi / 3| := by
      rw [norm_mul, norm_mul,
        show (↑(Real.pi / 3) : ℂ) * I = ↑(Real.pi / 3) * I from rfl,
        Complex.norm_exp_ofReal_mul_I, one_mul, norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
    have h_norm : |-(H_height - Real.sqrt 3 / 2)| = |Real.pi / 2 - Real.pi / 3| := by
      rw [← h_norm_L, ← h_norm_R, h_eq]
    have hcoeff : H_height - Real.sqrt 3 / 2 = 1 := by unfold H_height; ring
    have hpi : Real.pi / 2 - Real.pi / 3 = Real.pi / 6 := by ring
    rw [abs_neg, abs_of_pos (by rw [hcoeff]; norm_num), hcoeff, hpi,
      abs_of_pos (by positivity)] at h_norm
    -- h_norm : 1 = π / 6, contradicts π ≤ 4
    linarith [Real.pi_le_four]
  · -- Case t = 3: seg3 (exp) meets seg4 (affine). Same norm argument.
    intro hd
    -- Left derivative from seg3: d/dt [exp((π/2 + (t-2)*(2π/3-π/2))*I)] at t=3
    -- = exp(2π/3*I) * (2π/3-π/2)*I
    have h_left : HasDerivWithinAt fdBoundary
        (Complex.exp ((↑(2 * Real.pi / 3) : ℂ) * I) * (↑(2 * Real.pi / 3 - Real.pi / 2) * I))
        (Iic 3) 3 := by
      have h_inner : HasDerivAt
          (fun t : ℝ => (↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I)
          (↑(2 * Real.pi / 3 - Real.pi / 2) * I) 3 := by
        have h1 := ((hasDerivAt_id (3:ℝ)).sub_const 2).mul_const (2 * Real.pi / 3 - Real.pi / 2)
        simp only [one_mul] at h1
        exact ((h1.const_add _).ofReal_comp.mul_const I)
      have hda := h_inner.cexp

      have h_val : Real.pi / 2 + ((3:ℝ) - 2) * (2 * Real.pi / 3 - Real.pi / 2) =
          2 * Real.pi / 3 := by ring
      rw [h_val] at hda
      exact hda.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        (by filter_upwards [Ioc_mem_nhdsLE (show (2:ℝ) < 3 by norm_num)] with s hs
            have hsm := mem_Ioc.mp hs
            simp only [fdBoundary, if_neg (show ¬(s ≤ 1) from by linarith),
              if_neg (show ¬(s ≤ 2) from by linarith), if_pos hsm.2]
            congr 1; congr 1; push_cast; ring)
        right_mem_Iic
    -- Right derivative from seg4: d/dt [-1/2 + (√3/2 + (t-3)*(H-√3/2))*I] = (H-√3/2)*I
    have h_right : HasDerivWithinAt fdBoundary (↑(H_height - Real.sqrt 3 / 2) * I) (Ici 3) 3 := by
      have hda : HasDerivAt (fun t : ℝ => (-1:ℂ)/2 +
          (↑(Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2))) * I)
          (↑(H_height - Real.sqrt 3 / 2) * I) 3 := by
        have hg : HasDerivAt (fun t : ℝ => Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2))
            (H_height - Real.sqrt 3 / 2) 3 := by
          have h1 := ((hasDerivAt_id (3:ℝ)).sub_const 3).mul_const (H_height - Real.sqrt 3 / 2)
          simp only [one_mul] at h1
          exact h1.const_add _
        exact (hg.ofReal_comp.mul_const I).const_add _
      exact hda.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        (by filter_upwards [Ico_mem_nhdsGE (show (3:ℝ) < 4 by norm_num)] with s hs
            have hsm := mem_Ico.mp hs
            simp only [fdBoundary]
            by_cases h3 : s ≤ 3
            · have heq : s = 3 := le_antisymm h3 hsm.1; subst heq
              simp only [show ¬((3:ℝ) ≤ 1) from by norm_num, ↓reduceIte,
                show ¬((3:ℝ) ≤ 2) from by norm_num, le_refl, sub_self, zero_mul, add_zero]
              -- Need: exp(2π/3*I) = -1/2 + (√3/2)*I
              -- Collapse casts in exp argument, then evaluate via cos/sin
              suffices h : Complex.exp (↑(2 * Real.pi / 3) * I) = -1/2 + ↑(Real.sqrt 3 / 2) * I by
                convert h using 2; push_cast; ring
              rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
                show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
                Real.cos_pi_sub, Real.sin_pi_sub,
                Real.cos_pi_div_three, Real.sin_pi_div_three]
              push_cast; ring
            · push_neg at h3
              simp only [show ¬(s ≤ 1) from by linarith, ↓reduceIte,
                show ¬(s ≤ 2) from by linarith, show ¬(s ≤ 3) from not_le.mpr h3,
                if_pos hsm.2.le]
              congr 1; congr 1; push_cast; ring)
        left_mem_Ici
    -- Derive contradiction via norms
    have eq_L := (uniqueDiffWithinAt_Iic (3:ℝ)).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h_left
    have eq_R := (uniqueDiffWithinAt_Ici (3:ℝ)).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h_right
    have h_eq : Complex.exp ((↑(2 * Real.pi / 3) : ℂ) * I) *
        (↑(2 * Real.pi / 3 - Real.pi / 2) * I) =
        (↑(H_height - Real.sqrt 3 / 2) : ℂ) * I := by
      rw [← eq_L, ← eq_R]
    -- Compare norms: LHS norm = |π/6|, RHS norm = |1| = 1
    have h_norm_L : ‖Complex.exp ((↑(2 * Real.pi / 3) : ℂ) * I) *
        (↑(2 * Real.pi / 3 - Real.pi / 2) * I)‖ = |2 * Real.pi / 3 - Real.pi / 2| := by
      rw [norm_mul, norm_mul,
        show (↑(2 * Real.pi / 3) : ℂ) * I = ↑(2 * Real.pi / 3) * I from rfl,
        Complex.norm_exp_ofReal_mul_I, one_mul, norm_real, Complex.norm_I, mul_one,
        Real.norm_eq_abs]
    have h_norm_R : ‖(↑(H_height - Real.sqrt 3 / 2) : ℂ) * I‖ = |H_height - Real.sqrt 3 / 2| := by
      rw [norm_mul, norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    have h_norm : |2 * Real.pi / 3 - Real.pi / 2| = |H_height - Real.sqrt 3 / 2| := by
      rw [← h_norm_L, ← h_norm_R, h_eq]
    have hcoeff : H_height - Real.sqrt 3 / 2 = 1 := by unfold H_height; ring
    have hpi : 2 * Real.pi / 3 - Real.pi / 2 = Real.pi / 6 := by ring
    rw [hcoeff, abs_of_pos (by norm_num : (0:ℝ) < 1), hpi,
      abs_of_pos (by positivity)] at h_norm
    linarith [Real.pi_le_four]
  · -- Case t = 4: seg4 (affine, deriv ∝ I) meets seg5 (affine, deriv = 1).
    -- Contradiction via imaginary parts.
    intro hd
    -- Left derivative from seg4: (H-√3/2)*I
    have h_left : HasDerivWithinAt fdBoundary (↑(H_height - Real.sqrt 3 / 2) * I) (Iic 4) 4 := by
      have hda : HasDerivAt (fun t : ℝ => (-1:ℂ)/2 +
          ↑(Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I)
          (↑(H_height - Real.sqrt 3 / 2) * I) 4 := by
        have hg : HasDerivAt (fun t : ℝ => Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2))
            (H_height - Real.sqrt 3 / 2) 4 := by
          have h1 := ((hasDerivAt_id (4:ℝ)).sub_const 3).mul_const (H_height - Real.sqrt 3 / 2)
          simp only [one_mul] at h1
          exact h1.const_add _
        exact (hg.ofReal_comp.mul_const I).const_add _
      exact hda.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        (by filter_upwards [Ioc_mem_nhdsLE (show (3:ℝ) < 4 by norm_num)] with s hs
            have hsm := mem_Ioc.mp hs
            simp only [fdBoundary, if_neg (show ¬(s ≤ 1) from by linarith),
              if_neg (show ¬(s ≤ 2) from by linarith),
              if_neg (show ¬(s ≤ 3) from by linarith), if_pos hsm.2]
            congr 1; congr 1; push_cast; ring)
        right_mem_Iic
    -- Right derivative from seg5: 1
    have h_right : HasDerivWithinAt fdBoundary 1 (Ici 4) 4 := by
      have hda : HasDerivAt (fun t : ℝ => (↑(t - 9/2) : ℂ) + ↑H_height * I) (1 : ℂ) 4 := by
        have := ((hasDerivAt_id (4:ℝ)).sub_const (9/2)).ofReal_comp
        simp only [Complex.ofReal_one] at this
        exact this.add_const _
      exact hda.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
        (by filter_upwards [self_mem_nhdsWithin] with s hs
            have hsm := mem_Ici.mp hs
            simp only [fdBoundary]
            by_cases h4 : s ≤ 4
            · have heq : s = 4 := le_antisymm h4 hsm; subst heq
              simp only [show ¬((4:ℝ) ≤ 1) from by norm_num, ↓reduceIte,
                show ¬((4:ℝ) ≤ 2) from by norm_num,
                show ¬((4:ℝ) ≤ 3) from by norm_num, le_refl]
              unfold H_height; push_cast; ring
            · push_neg at h4
              simp [show ¬(s ≤ 1) from by linarith, show ¬(s ≤ 2) from by linarith,
                show ¬(s ≤ 3) from by linarith, show ¬(s ≤ 4) from not_le.mpr h4])
        left_mem_Ici
    have eq_L := (uniqueDiffWithinAt_Iic (4:ℝ)).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h_left
    have eq_R := (uniqueDiffWithinAt_Ici (4:ℝ)).eq_deriv _
      hd.hasDerivAt.hasDerivWithinAt h_right
    have h_absurd : (↑(H_height - Real.sqrt 3 / 2) : ℂ) * I = 1 := by
      rw [← eq_L, ← eq_R]
    have := congr_arg Complex.im h_absurd
    simp [H_height] at this

/-- At t=2, the boundary IS differentiable: segments 2 and 3 (both arcs on the unit circle)
    meet smoothly at i with the same derivative.
    Left: d/dt exp((π/3 + (t-1)*(π/6))*I)|_{t=2⁻} = (π/6)*I * I = -π/6
    Right: d/dt exp((π/2 + (t-2)*(π/6))*I)|_{t=2⁺} = (π/6)*I * I = -π/6 -/
theorem fdBoundary_differentiableAt_two : DifferentiableAt ℝ fdBoundary 2 := by
  -- Key: seg2 and seg3 are the SAME function (both = exp(π/6*(t+1)*I)),
  -- so fdBoundary agrees with a single differentiable function on (1, 3) ∋ 2
  have h_agree : fdBoundary =ᶠ[𝓝 2] fun s =>
      Complex.exp ((Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * I) := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3)] with s hs
    have hsm := mem_Ioo.mp hs
    simp only [fdBoundary, if_neg (not_le.mpr hsm.1)]
    by_cases h : s ≤ 2
    · simp only [if_pos h]
    · push_neg at h
      simp only [if_neg (not_le.mpr h), if_pos hsm.2.le]
      congr 1; congr 1; ring
  exact h_agree.differentiableAt_iff.mpr
    (DifferentiableAt.cexp (((differentiableAt_const _).add
      ((Complex.ofRealCLM.differentiableAt.sub (differentiableAt_const _)).mul
        (differentiableAt_const _))).mul_const _))

/-- Away from partition points, the boundary is differentiable. -/
theorem fdBoundary_differentiableAt_off_partition (t : ℝ)
    (ht : t ∈ Ioo 0 5) (ht_not_P : t ∉ fdPartition) :
    DifferentiableAt ℝ fdBoundary t := by
  simp only [fdPartition, Finset.mem_insert, Finset.mem_singleton, not_or] at ht_not_P
  obtain ⟨hne1, hne2, hne3, hne4⟩ := ht_not_P
  -- Differentiability tactic for affine ℝ → ℂ branches
  have hd_ofReal := Complex.ofRealCLM.differentiable
  by_cases h1 : t < 1
  · -- t ∈ (0, 1): seg1
    have : fdBoundary =ᶠ[𝓝 t] fun s =>
        1/2 + (H_height - s * (H_height - Real.sqrt 3 / 2)) * I := by
      filter_upwards [Iio_mem_nhds h1] with s hs
      simp only [fdBoundary, if_pos (mem_Iio.mp hs).le]
    exact this.differentiableAt_iff.mpr
      ((differentiableAt_const _).add (((differentiableAt_const _).sub
        (hd_ofReal.differentiableAt.mul (differentiableAt_const _))).mul_const _))
  · push_neg at h1
    have h1' : 1 < t := h1.lt_of_ne (Ne.symm hne1)
    by_cases h2 : t < 2
    · -- t ∈ (1, 2): seg2
      have : fdBoundary =ᶠ[𝓝 t] fun s =>
          Complex.exp ((Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) * I) := by
        filter_upwards [Ioo_mem_nhds h1' h2] with s hs
        simp only [fdBoundary, if_neg (not_le.mpr (mem_Ioo.mp hs).1),
          if_pos (mem_Ioo.mp hs).2.le]
      exact this.differentiableAt_iff.mpr
        (DifferentiableAt.cexp (((differentiableAt_const _).add
          ((hd_ofReal.differentiableAt.sub (differentiableAt_const _)).mul
            (differentiableAt_const _))).mul_const _))
    · push_neg at h2
      have h2' : 2 < t := h2.lt_of_ne (Ne.symm hne2)
      by_cases h3 : t < 3
      · -- t ∈ (2, 3): seg3
        have : fdBoundary =ᶠ[𝓝 t] fun s =>
            Complex.exp ((Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I) := by
          filter_upwards [Ioo_mem_nhds h2' h3] with s hs
          have hsm := mem_Ioo.mp hs
          simp only [fdBoundary, if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 2) hsm.1)),
            if_neg (not_le.mpr hsm.1), if_pos hsm.2.le]
        exact this.differentiableAt_iff.mpr
          (DifferentiableAt.cexp (((differentiableAt_const _).add
            ((hd_ofReal.differentiableAt.sub (differentiableAt_const _)).mul
              (differentiableAt_const _))).mul_const _))
      · push_neg at h3
        have h3' : 3 < t := h3.lt_of_ne (Ne.symm hne3)
        by_cases h4 : t < 4
        · -- t ∈ (3, 4): seg4
          have : fdBoundary =ᶠ[𝓝 t] fun s =>
              -1/2 + (Real.sqrt 3 / 2 + (s - 3) * (H_height - Real.sqrt 3 / 2)) * I := by
            filter_upwards [Ioo_mem_nhds h3' h4] with s hs
            have hsm := mem_Ioo.mp hs
            simp only [fdBoundary,
              if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) hsm.1)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) hsm.1)),
              if_neg (not_le.mpr hsm.1), if_pos hsm.2.le]
          exact this.differentiableAt_iff.mpr
            ((differentiableAt_const _).add (((differentiableAt_const _).add
              ((hd_ofReal.differentiableAt.sub (differentiableAt_const _)).mul
                (differentiableAt_const _))).mul_const _))
        · -- t ∈ (4, 5): seg5
          push_neg at h4
          have h4' : 4 < t := h4.lt_of_ne (Ne.symm hne4)
          have : fdBoundary =ᶠ[𝓝 t] fun s =>
              (s - 9/2) + H_height * I := by
            filter_upwards [Ioi_mem_nhds h4'] with s hs
            have hsm := mem_Ioi.mp hs
            simp only [fdBoundary,
              if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) hsm)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) hsm)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) hsm)),
              if_neg (not_le.mpr hsm)]
          exact this.differentiableAt_iff.mpr
            ((hd_ofReal.differentiableAt.sub (differentiableAt_const _)).add
              (differentiableAt_const _))

end

/-! ## PiecewiseC1Immersion Adapter -/

section PiecewiseC1Adapter

/-- The full partition including endpoints for the PiecewiseC1Curve structure. -/
noncomputable def fdBoundaryFullPartition : Finset ℝ := {0, 1, 2, 3, 4, 5}

/-- Helper: H_height - √3/2 = 1 -/
private theorem H_height_sub_sqrt3_div2 : H_height - Real.sqrt 3 / 2 = 1 := by
  unfold H_height; ring

set_option maxHeartbeats 400000 in
/-- The derivative of fdBoundary is continuous away from partition points. -/
private theorem fdBoundary_deriv_continuousAt_off_partition (t : ℝ)
    (ht : t ∈ Ioo 0 5) (ht_not_P : t ∉ fdBoundaryFullPartition) :
    ContinuousAt (deriv fdBoundary) t := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton, not_or]
    at ht_not_P
  obtain ⟨hne0, hne1, hne2, hne3, hne4, hne5⟩ := ht_not_P
  have hd_ofReal := Complex.ofRealCLM.differentiable
  by_cases h1 : t < 1
  · -- seg1: deriv fdBoundary = const near t
    have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
        (1:ℂ)/2 + ↑(H_height - s * (H_height - Real.sqrt 3 / 2)) * I := by
      filter_upwards [Ioo_mem_nhds (lt_of_le_of_ne ht.1.le (Ne.symm hne0)) h1] with s hs
      simp only [fdBoundary, if_pos (mem_Ioo.mp hs).2.le]
      congr 1; congr 1; push_cast; ring
    have h_deriv_const : deriv fdBoundary =ᶠ[𝓝 t]
        fun _ => (↑(-(H_height - Real.sqrt 3 / 2)) : ℂ) * I := by
      have h_eq2 := eventually_eventually_nhds.mpr h_eq
      filter_upwards [h_eq2] with s hs
      rw [Filter.EventuallyEq.deriv_eq hs]
      have : HasDerivAt (fun u : ℝ => (1:ℂ)/2 + ↑(H_height - u * (H_height - Real.sqrt 3 / 2)) * I)
          (↑(-(H_height - Real.sqrt 3 / 2)) * I) s := by
        have hg : HasDerivAt (fun u : ℝ => H_height - u * (H_height - Real.sqrt 3 / 2))
            (-(H_height - Real.sqrt 3 / 2)) s := by
          rw [show (fun u : ℝ => H_height - u * (H_height - Real.sqrt 3 / 2)) =
            (fun u => -(H_height - Real.sqrt 3 / 2) * u + H_height) from by ext u; ring]
          simpa using ((hasDerivAt_id s).const_mul (-(H_height - Real.sqrt 3 / 2))).add_const H_height
        exact (hg.ofReal_comp.mul_const I).const_add _
      exact this.deriv
    exact continuousAt_const.congr h_deriv_const.symm
  · push_neg at h1
    have h1' : 1 < t := h1.lt_of_ne (Ne.symm hne1)
    by_cases h2 : t < 2
    · -- seg2: deriv = exp(angle*I) * (π/6*I), which is continuous
      have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
          Complex.exp ((↑(Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I) := by
        filter_upwards [Ioo_mem_nhds h1' h2] with s hs
        simp only [fdBoundary, if_neg (not_le.mpr (mem_Ioo.mp hs).1),
          if_pos (mem_Ioo.mp hs).2.le]
        congr 1; congr 1; push_cast; ring
      have h_deriv_eq : deriv fdBoundary =ᶠ[𝓝 t] fun s =>
          Complex.exp ((↑(Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I) *
            (↑(Real.pi / 2 - Real.pi / 3) * I) := by
        have h_eq2 := eventually_eventually_nhds.mpr h_eq
        filter_upwards [h_eq2] with s hs
        rw [Filter.EventuallyEq.deriv_eq hs]
        have h_inner : HasDerivAt (fun u : ℝ =>
            (↑(Real.pi / 3 + (u - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I)
            (↑(Real.pi / 2 - Real.pi / 3) * I) s := by
          have h1 := ((hasDerivAt_id s).sub_const 1).mul_const (Real.pi / 2 - Real.pi / 3)
          simp only [one_mul] at h1
          exact (h1.const_add _).ofReal_comp.mul_const I
        exact h_inner.cexp.deriv
      have h_ca : ContinuousAt (fun s : ℝ => Complex.exp
          ((↑(Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I) *
            (↑(Real.pi / 2 - Real.pi / 3) * I)) t :=
        ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.add
          ((continuousAt_id.sub continuousAt_const).mul continuousAt_const))).mul
            continuousAt_const).cexp.mul continuousAt_const
      exact h_ca.congr h_deriv_eq.symm
    · push_neg at h2
      have h2' : 2 < t := h2.lt_of_ne (Ne.symm hne2)
      by_cases h3 : t < 3
      · -- seg3: same as seg2 with different offsets
        have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
            Complex.exp ((↑(Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I) := by
          filter_upwards [Ioo_mem_nhds h2' h3] with s hs
          have hsm := mem_Ioo.mp hs
          simp only [fdBoundary, if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 2) hsm.1)),
            if_neg (not_le.mpr hsm.1), if_pos hsm.2.le]
          congr 1; congr 1; push_cast; ring
        have h_deriv_eq : deriv fdBoundary =ᶠ[𝓝 t] fun s =>
            Complex.exp ((↑(Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I) *
              (↑(2 * Real.pi / 3 - Real.pi / 2) * I) := by
          have h_eq2 := eventually_eventually_nhds.mpr h_eq
          filter_upwards [h_eq2] with s hs
          rw [Filter.EventuallyEq.deriv_eq hs]
          have h_inner : HasDerivAt (fun u : ℝ =>
              (↑(Real.pi / 2 + (u - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I)
              (↑(2 * Real.pi / 3 - Real.pi / 2) * I) s := by
            have h1 := ((hasDerivAt_id s).sub_const 2).mul_const (2 * Real.pi / 3 - Real.pi / 2)
            simp only [one_mul] at h1
            exact (h1.const_add _).ofReal_comp.mul_const I
          exact h_inner.cexp.deriv
        have h_ca : ContinuousAt (fun s : ℝ => Complex.exp
            ((↑(Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I) *
              (↑(2 * Real.pi / 3 - Real.pi / 2) * I)) t :=
          ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.add
            ((continuousAt_id.sub continuousAt_const).mul continuousAt_const))).mul
              continuousAt_const).cexp.mul continuousAt_const
        exact h_ca.congr h_deriv_eq.symm
      · push_neg at h3
        have h3' : 3 < t := h3.lt_of_ne (Ne.symm hne3)
        by_cases h4 : t < 4
        · -- seg4: constant derivative
          have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
              (-1:ℂ)/2 + ↑(Real.sqrt 3 / 2 + (s - 3) * (H_height - Real.sqrt 3 / 2)) * I := by
            filter_upwards [Ioo_mem_nhds h3' h4] with s hs
            have hsm := mem_Ioo.mp hs
            simp only [fdBoundary,
              if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) hsm.1)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) hsm.1)),
              if_neg (not_le.mpr hsm.1), if_pos hsm.2.le]
            congr 1; congr 1; push_cast; ring
          have h_deriv_const : deriv fdBoundary =ᶠ[𝓝 t]
              fun _ => (↑(H_height - Real.sqrt 3 / 2) : ℂ) * I := by
            have h_eq2 := eventually_eventually_nhds.mpr h_eq
            filter_upwards [h_eq2] with s hs
            rw [Filter.EventuallyEq.deriv_eq hs]
            have hg : HasDerivAt (fun u : ℝ => Real.sqrt 3 / 2 + (u - 3) * (H_height - Real.sqrt 3 / 2))
                (H_height - Real.sqrt 3 / 2) s := by
              have h1 := ((hasDerivAt_id s).sub_const 3).mul_const (H_height - Real.sqrt 3 / 2)
              simp only [one_mul] at h1
              exact h1.const_add _
            exact ((hg.ofReal_comp.mul_const I).const_add _).deriv
          exact continuousAt_const.congr h_deriv_const.symm
        · -- seg5: constant derivative
          push_neg at h4
          have h4' : 4 < t := h4.lt_of_ne (Ne.symm hne4)
          have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
              (↑(s - 9/2) : ℂ) + ↑H_height * I := by
            filter_upwards [Ioi_mem_nhds h4'] with s hs
            have hsm := mem_Ioi.mp hs
            simp only [fdBoundary,
              if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) hsm)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) hsm)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) hsm)),
              if_neg (not_le.mpr hsm)]
            push_cast; ring
          have h_deriv_const : deriv fdBoundary =ᶠ[𝓝 t] fun _ => (1 : ℂ) := by
            have h_eq2 := eventually_eventually_nhds.mpr h_eq
            filter_upwards [h_eq2] with s hs
            rw [Filter.EventuallyEq.deriv_eq hs]
            have h1 : HasDerivAt (fun u : ℝ => (u - 9/2 : ℝ)) 1 s := by
              simpa using (hasDerivAt_id s).sub_const (9/2 : ℝ)
            exact (h1.ofReal_comp.add_const (↑H_height * I)).deriv
          exact continuousAt_const.congr h_deriv_const.symm

/-- The boundary curve as a PiecewiseC1Curve. -/
noncomputable def fdBoundaryCurve : PiecewiseC1Curve where
  toFun := fdBoundary
  a := 0
  b := 5
  hab := by norm_num
  partition := fdBoundaryFullPartition
  partition_subset := by
    intro x hx
    have : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
      simp only [fdBoundaryFullPartition, Finset.mem_coe,
        Finset.mem_insert, Finset.mem_singleton] at hx
      exact hx
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by norm_num, by norm_num⟩
  endpoints_in_partition := by
    constructor <;> simp [fdBoundaryFullPartition]
  continuous_toFun := fdBoundary_continuous.continuousOn
  smooth_off_partition := by
    intro t ht htp
    have ht_ioo : t ∈ Ioo 0 5 := by
      refine ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩
      · intro h; exact htp (by rw [← h]; simp [fdBoundaryFullPartition])
      · intro h; exact htp (by rw [h]; simp [fdBoundaryFullPartition])
    have htp' : t ∉ fdPartition := by
      simp only [fdBoundaryFullPartition, fdPartition, Finset.mem_insert,
        Finset.mem_singleton, not_or] at htp ⊢
      exact ⟨htp.2.1, htp.2.2.1, htp.2.2.2.1, htp.2.2.2.2.1⟩
    exact fdBoundary_differentiableAt_off_partition t ht_ioo htp'
  deriv_continuous_off_partition := by
    intro t ht htp
    exact fdBoundary_deriv_continuousAt_off_partition t ht htp

set_option maxHeartbeats 400000 in
/-- Helper for computing the derivative on each segment and proving it's nonzero.
    Returns the derivative formula and proof it's nonzero for the 5-way case split. -/
private theorem fdBoundary_deriv_ne_zero_off_partition (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 5) (ht_not_P : t ∉ fdBoundaryFullPartition) :
    deriv fdBoundary t ≠ 0 := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton, not_or]
    at ht_not_P
  obtain ⟨hne0, hne1, hne2, hne3, hne4, hne5⟩ := ht_not_P
  have ht_ioo : t ∈ Ioo 0 5 :=
    ⟨lt_of_le_of_ne ht.1 (Ne.symm hne0), lt_of_le_of_ne ht.2 hne5⟩
  have hd_ofReal := Complex.ofRealCLM.differentiable
  by_cases h1 : t < 1
  · -- seg1: deriv = -(H-√3/2)*I = -I
    have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
        (1:ℂ)/2 + ↑(H_height - s * (H_height - Real.sqrt 3 / 2)) * I := by
      filter_upwards [Ioo_mem_nhds ht_ioo.1 h1] with s hs
      simp only [fdBoundary, if_pos (mem_Ioo.mp hs).2.le]
      congr 1; congr 1; push_cast; ring
    rw [Filter.EventuallyEq.deriv_eq h_eq]
    have hg : HasDerivAt (fun u : ℝ => H_height - u * (H_height - Real.sqrt 3 / 2))
        (-(H_height - Real.sqrt 3 / 2)) t := by
      rw [show (fun u : ℝ => H_height - u * (H_height - Real.sqrt 3 / 2)) =
        (fun u => -(H_height - Real.sqrt 3 / 2) * u + H_height) from by ext u; ring]
      simpa using ((hasDerivAt_id t).const_mul (-(H_height - Real.sqrt 3 / 2))).add_const H_height
    rw [(hg.ofReal_comp.mul_const I).const_add _ |>.deriv]
    simp only [H_height_sub_sqrt3_div2, Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul]
    exact neg_ne_zero.mpr Complex.I_ne_zero
  · push_neg at h1
    have h1' : 1 < t := h1.lt_of_ne (Ne.symm hne1)
    by_cases h2 : t < 2
    · -- seg2: deriv = exp(...) * (π/6)*I, nonzero
      have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
          Complex.exp ((↑(Real.pi / 3 + (s - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I) := by
        filter_upwards [Ioo_mem_nhds h1' h2] with s hs
        simp only [fdBoundary, if_neg (not_le.mpr (mem_Ioo.mp hs).1),
          if_pos (mem_Ioo.mp hs).2.le]
        congr 1; congr 1; push_cast; ring
      rw [Filter.EventuallyEq.deriv_eq h_eq]
      have h_inner : HasDerivAt (fun u : ℝ =>
          (↑(Real.pi / 3 + (u - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I)
          (↑(Real.pi / 2 - Real.pi / 3) * I) t := by
        have h1 := ((hasDerivAt_id t).sub_const 1).mul_const (Real.pi / 2 - Real.pi / 3)
        simp only [one_mul] at h1
        exact (h1.const_add _).ofReal_comp.mul_const I
      rw [h_inner.cexp.deriv]
      apply mul_ne_zero (exp_ne_zero _)
      apply mul_ne_zero _ Complex.I_ne_zero
      rw [Complex.ofReal_ne_zero]
      have : Real.pi / 2 - Real.pi / 3 = Real.pi / 6 := by ring
      rw [this]; positivity
    · push_neg at h2
      have h2' : 2 < t := h2.lt_of_ne (Ne.symm hne2)
      by_cases h3 : t < 3
      · -- seg3: deriv = exp(...) * (π/6)*I, nonzero
        have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
            Complex.exp ((↑(Real.pi / 2 + (s - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I) := by
          filter_upwards [Ioo_mem_nhds h2' h3] with s hs
          have hsm := mem_Ioo.mp hs
          simp only [fdBoundary, if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 2) hsm.1)),
            if_neg (not_le.mpr hsm.1), if_pos hsm.2.le]
          congr 1; congr 1; push_cast; ring
        rw [Filter.EventuallyEq.deriv_eq h_eq]
        have h_inner : HasDerivAt (fun u : ℝ =>
            (↑(Real.pi / 2 + (u - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I)
            (↑(2 * Real.pi / 3 - Real.pi / 2) * I) t := by
          have h1 := ((hasDerivAt_id t).sub_const 2).mul_const (2 * Real.pi / 3 - Real.pi / 2)
          simp only [one_mul] at h1
          exact (h1.const_add _).ofReal_comp.mul_const I
        rw [h_inner.cexp.deriv]
        apply mul_ne_zero (exp_ne_zero _)
        apply mul_ne_zero _ Complex.I_ne_zero
        rw [Complex.ofReal_ne_zero]
        have : 2 * Real.pi / 3 - Real.pi / 2 = Real.pi / 6 := by ring
        rw [this]; positivity
      · push_neg at h3
        have h3' : 3 < t := h3.lt_of_ne (Ne.symm hne3)
        by_cases h4 : t < 4
        · -- seg4: deriv = (H-√3/2)*I = I
          have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
              (-1:ℂ)/2 + ↑(Real.sqrt 3 / 2 + (s - 3) * (H_height - Real.sqrt 3 / 2)) * I := by
            filter_upwards [Ioo_mem_nhds h3' h4] with s hs
            have hsm := mem_Ioo.mp hs
            simp only [fdBoundary,
              if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) hsm.1)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) hsm.1)),
              if_neg (not_le.mpr hsm.1), if_pos hsm.2.le]
            congr 1; congr 1; push_cast; ring
          rw [Filter.EventuallyEq.deriv_eq h_eq]
          have hg : HasDerivAt (fun u : ℝ => Real.sqrt 3 / 2 + (u - 3) * (H_height - Real.sqrt 3 / 2))
              (H_height - Real.sqrt 3 / 2) t := by
            have h1 := ((hasDerivAt_id t).sub_const 3).mul_const (H_height - Real.sqrt 3 / 2)
            simp only [one_mul] at h1
            exact h1.const_add _
          rw [(hg.ofReal_comp.mul_const I).const_add _ |>.deriv]
          simp only [H_height_sub_sqrt3_div2, Complex.ofReal_one, one_mul]
          exact Complex.I_ne_zero
        · -- seg5: deriv = 1
          push_neg at h4
          have h4' : 4 < t := h4.lt_of_ne (Ne.symm hne4)
          have h_eq : fdBoundary =ᶠ[𝓝 t] fun s =>
              (↑(s - 9/2) : ℂ) + ↑H_height * I := by
            filter_upwards [Ioi_mem_nhds h4'] with s hs
            have hsm := mem_Ioi.mp hs
            simp only [fdBoundary,
              if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) hsm)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) hsm)),
              if_neg (not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) hsm)),
              if_neg (not_le.mpr hsm)]
            push_cast; ring
          rw [Filter.EventuallyEq.deriv_eq h_eq]
          have h1 : HasDerivAt (fun u : ℝ => (u - 9/2 : ℝ)) 1 t := by
            simpa using (hasDerivAt_id t).sub_const (9/2 : ℝ)
          rw [(h1.ofReal_comp.add_const (↑H_height * I)).deriv]
          exact one_ne_zero

/-- Compute the derivative of seg1 at any point near s. -/
private theorem deriv_seg1_eq (s : ℝ) (hs : s < 1)
    (h_eq : fdBoundary =ᶠ[𝓝 s] fun u =>
      (1:ℂ)/2 + ↑(H_height - u * (H_height - Real.sqrt 3 / 2)) * I) :
    deriv fdBoundary s = -(1 : ℂ) * I := by
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have hg : HasDerivAt (fun u : ℝ => H_height - u * (H_height - Real.sqrt 3 / 2))
      (-(H_height - Real.sqrt 3 / 2)) s := by
    rw [show (fun u : ℝ => H_height - u * (H_height - Real.sqrt 3 / 2)) =
      (fun u => -(H_height - Real.sqrt 3 / 2) * u + H_height) from by ext u; ring]
    simpa using ((hasDerivAt_id s).const_mul (-(H_height - Real.sqrt 3 / 2))).add_const H_height
  rw [(hg.ofReal_comp.mul_const I).const_add _ |>.deriv, H_height_sub_sqrt3_div2]; simp

/-- Compute the derivative of seg2 at any point s in (1,2). -/
private theorem deriv_seg2_eq (s : ℝ) (h1 : 1 < s) (h2 : s < 2)
    (h_eq : fdBoundary =ᶠ[𝓝 s] fun u =>
      Complex.exp ((↑(Real.pi / 3 + (u - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I)) :
    deriv fdBoundary s = Complex.exp
      ((↑(Real.pi / 3 + (s - 1) * (Real.pi / 6)) : ℂ) * I) * (↑(Real.pi / 6) * I) := by
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun u : ℝ =>
      (↑(Real.pi / 3 + (u - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I)
      (↑(Real.pi / 2 - Real.pi / 3) * I) s := by
    have h1 := ((hasDerivAt_id s).sub_const 1).mul_const (Real.pi / 2 - Real.pi / 3)
    simp only [one_mul] at h1
    exact (h1.const_add _).ofReal_comp.mul_const I
  rw [h_inner.cexp.deriv]
  have h_pi_eq : Real.pi / 2 - Real.pi / 3 = Real.pi / 6 := by ring
  congr 1
  · congr 1; congr 1; rw [h_pi_eq]
  · rw [h_pi_eq]

/-- Compute the derivative of seg3 at any point s in (2,3). -/
private theorem deriv_seg3_eq (s : ℝ) (h2 : 2 < s) (h3 : s < 3)
    (h_eq : fdBoundary =ᶠ[𝓝 s] fun u =>
      Complex.exp ((↑(Real.pi / 2 + (u - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I)) :
    deriv fdBoundary s = Complex.exp
      ((↑(Real.pi / 2 + (s - 2) * (Real.pi / 6)) : ℂ) * I) * (↑(Real.pi / 6) * I) := by
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have h_inner : HasDerivAt (fun u : ℝ =>
      (↑(Real.pi / 2 + (u - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I)
      (↑(2 * Real.pi / 3 - Real.pi / 2) * I) s := by
    have h1 := ((hasDerivAt_id s).sub_const 2).mul_const (2 * Real.pi / 3 - Real.pi / 2)
    simp only [one_mul] at h1
    exact (h1.const_add _).ofReal_comp.mul_const I
  rw [h_inner.cexp.deriv]
  have h_pi_eq : 2 * Real.pi / 3 - Real.pi / 2 = Real.pi / 6 := by ring
  congr 1
  · congr 1; congr 1; rw [h_pi_eq]
  · rw [h_pi_eq]

/-- Compute the derivative of seg4 at any point s in (3,4). -/
private theorem deriv_seg4_eq (s : ℝ) (h3 : 3 < s) (h4 : s < 4)
    (h_eq : fdBoundary =ᶠ[𝓝 s] fun u =>
      (-1:ℂ)/2 + ↑(Real.sqrt 3 / 2 + (u - 3) * (H_height - Real.sqrt 3 / 2)) * I) :
    deriv fdBoundary s = I := by
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have hg : HasDerivAt (fun u : ℝ => Real.sqrt 3 / 2 + (u - 3) * (H_height - Real.sqrt 3 / 2))
      (H_height - Real.sqrt 3 / 2) s := by
    have h1 := ((hasDerivAt_id s).sub_const 3).mul_const (H_height - Real.sqrt 3 / 2)
    simp only [one_mul] at h1
    exact h1.const_add _
  rw [(hg.ofReal_comp.mul_const I).const_add _ |>.deriv, H_height_sub_sqrt3_div2]; simp

/-- Compute the derivative of seg5 at any point s > 4. -/
private theorem deriv_seg5_eq (s : ℝ) (h4 : 4 < s)
    (h_eq : fdBoundary =ᶠ[𝓝 s] fun u => (↑(u - 9/2) : ℂ) + ↑H_height * I) :
    deriv fdBoundary s = 1 := by
  rw [Filter.EventuallyEq.deriv_eq h_eq]
  have hda : HasDerivAt (fun u : ℝ => (↑(u - 9/2) : ℂ) + ↑H_height * I) (1 : ℂ) s := by
    have h1 : HasDerivAt (fun u : ℝ => (u - 9/2 : ℝ)) 1 s := by
      simpa using (hasDerivAt_id s).sub_const (9/2 : ℝ)
    exact (h1.ofReal_comp.add_const (↑H_height * I))
  exact hda.deriv

/-- ContinuousAt for the exp-arc derivative pattern: s ↦ exp((a + (s-c)*d)*I) * (d*I). -/
private theorem continuousAt_exp_arc_deriv (a c d : ℝ) (p : ℝ) :
    ContinuousAt (fun s : ℝ => Complex.exp
      ((↑(a + (s - c) * d) : ℂ) * I) * (↑d * I)) p := by
  apply ContinuousAt.mul
  · apply Complex.continuous_exp.continuousAt.comp
    apply ContinuousAt.mul _ continuousAt_const
    exact Complex.continuous_ofReal.continuousAt.comp
      (continuousAt_const.add ((continuousAt_id.sub continuousAt_const).mul continuousAt_const))
  · exact continuousAt_const

/-- EventuallyEq for seg1: near any s < 1 -/
private theorem fdBoundary_eventuallyEq_seg1 (s : ℝ) (hs1 : s < 1) :
    fdBoundary =ᶠ[𝓝 s] fun u =>
      (1:ℂ)/2 + ↑(H_height - u * (H_height - Real.sqrt 3 / 2)) * I := by
  filter_upwards [Iio_mem_nhds hs1] with u hu
  simp only [fdBoundary, if_pos (mem_Iio.mp hu).le]
  congr 1; congr 1; push_cast; ring

/-- EventuallyEq for seg2: near any s ∈ (1,2) -/
private theorem fdBoundary_eventuallyEq_seg2 (s : ℝ) (hs1 : 1 < s) (hs2 : s < 2) :
    fdBoundary =ᶠ[𝓝 s] fun u =>
      Complex.exp ((↑(Real.pi / 3 + (u - 1) * (Real.pi / 2 - Real.pi / 3)) : ℂ) * I) := by
  filter_upwards [Ioo_mem_nhds hs1 hs2] with u hu
  have hum := mem_Ioo.mp hu
  simp only [fdBoundary, if_neg (not_le.mpr hum.1), if_pos hum.2.le]
  congr 1; congr 1; push_cast; ring

/-- EventuallyEq for seg3: near any s ∈ (2,3) -/
private theorem fdBoundary_eventuallyEq_seg3 (s : ℝ) (hs2 : 2 < s) (hs3 : s < 3) :
    fdBoundary =ᶠ[𝓝 s] fun u =>
      Complex.exp ((↑(Real.pi / 2 + (u - 2) * (2 * Real.pi / 3 - Real.pi / 2)) : ℂ) * I) := by
  filter_upwards [Ioo_mem_nhds hs2 hs3] with u hu
  have hum := mem_Ioo.mp hu
  simp only [fdBoundary, if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 2) hum.1)),
    if_neg (not_le.mpr hum.1), if_pos hum.2.le]
  congr 1; congr 1; push_cast; ring

/-- EventuallyEq for seg4: near any s ∈ (3,4) -/
private theorem fdBoundary_eventuallyEq_seg4 (s : ℝ) (hs3 : 3 < s) (hs4 : s < 4) :
    fdBoundary =ᶠ[𝓝 s] fun u =>
      (-1:ℂ)/2 + ↑(Real.sqrt 3 / 2 + (u - 3) * (H_height - Real.sqrt 3 / 2)) * I := by
  filter_upwards [Ioo_mem_nhds hs3 hs4] with u hu
  have hum := mem_Ioo.mp hu
  simp only [fdBoundary,
    if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) hum.1)),
    if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) hum.1)),
    if_neg (not_le.mpr hum.1), if_pos hum.2.le]
  congr 1; congr 1; push_cast; ring

/-- EventuallyEq for seg5: near any s > 4 -/
private theorem fdBoundary_eventuallyEq_seg5 (s : ℝ) (hs4 : 4 < s) :
    fdBoundary =ᶠ[𝓝 s] fun u => (↑(u - 9/2) : ℂ) + ↑H_height * I := by
  filter_upwards [Ioi_mem_nhds hs4] with u hu
  have hum := mem_Ioi.mp hu
  simp only [fdBoundary,
    if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) hum)),
    if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) hum)),
    if_neg (not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) hum)),
    if_neg (not_le.mpr hum)]
  push_cast; ring

set_option maxHeartbeats 400000 in
/-- Helper for left derivative limits at each partition point. -/
private theorem fdBoundary_left_deriv_limit (p : ℝ) (hp : p ∈ fdBoundaryFullPartition)
    (hap : (0 : ℝ) < p) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv fdBoundary) (𝓝[<] p) (𝓝 L) := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · -- p = 0, but 0 < 0 is false
    exact absurd hap (lt_irrefl _)
  · -- p = 1, left from seg1: constant deriv = -I
    refine ⟨-(1 : ℂ) * I, by simp [Complex.I_ne_zero], ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with s hs
      have hsm := mem_Ioo.mp hs
      exact (deriv_seg1_eq s hsm.2 (fdBoundary_eventuallyEq_seg1 s hsm.2)).symm)
  · -- p = 2, left from seg2: deriv = exp(π/2*I) * (π/6)*I
    refine ⟨Complex.exp ((↑(Real.pi / 2) : ℂ) * I) * (↑(Real.pi / 6) * I), ?_, ?_⟩
    · apply mul_ne_zero (exp_ne_zero _)
      exact mul_ne_zero (by rw [Complex.ofReal_ne_zero]; positivity) Complex.I_ne_zero
    · -- Show deriv fdBoundary = g eventually, then Tendsto g from continuity
      have h_ee : (fun s => Complex.exp ((↑(Real.pi / 3 + (s - 1) * (Real.pi / 6)) : ℂ) * I) *
            (↑(Real.pi / 6) * I)) =ᶠ[𝓝[<] 2] deriv fdBoundary := by
        filter_upwards [Ioo_mem_nhdsLT (show (1:ℝ) < 2 by norm_num)] with s hs
        have hsm := mem_Ioo.mp hs
        exact (deriv_seg2_eq s hsm.1 hsm.2 (fdBoundary_eventuallyEq_seg2 s hsm.1 hsm.2)).symm
      have h_cont := continuousAt_exp_arc_deriv (Real.pi / 3) 1 (Real.pi / 6) 2
      simp only [ContinuousAt] at h_cont
      rw [show Real.pi / 3 + ((2:ℝ) - 1) * (Real.pi / 6) = Real.pi / 2 from by ring] at h_cont
      exact (h_cont.mono_left nhdsWithin_le_nhds).congr' h_ee
  · -- p = 3, left from seg3: deriv = exp(2π/3*I) * (π/6)*I
    refine ⟨Complex.exp ((↑(2 * Real.pi / 3) : ℂ) * I) * (↑(Real.pi / 6) * I), ?_, ?_⟩
    · apply mul_ne_zero (exp_ne_zero _)
      exact mul_ne_zero (by rw [Complex.ofReal_ne_zero]; positivity) Complex.I_ne_zero
    · have h_ee : (fun s => Complex.exp ((↑(Real.pi / 2 + (s - 2) * (Real.pi / 6)) : ℂ) * I) *
            (↑(Real.pi / 6) * I)) =ᶠ[𝓝[<] 3] deriv fdBoundary := by
        filter_upwards [Ioo_mem_nhdsLT (show (2:ℝ) < 3 by norm_num)] with s hs
        have hsm := mem_Ioo.mp hs
        exact (deriv_seg3_eq s hsm.1 hsm.2 (fdBoundary_eventuallyEq_seg3 s hsm.1 hsm.2)).symm
      have h_cont := continuousAt_exp_arc_deriv (Real.pi / 2) 2 (Real.pi / 6) 3
      simp only [ContinuousAt] at h_cont
      rw [show Real.pi / 2 + ((3:ℝ) - 2) * (Real.pi / 6) = 2 * Real.pi / 3 from by ring] at h_cont
      exact (h_cont.mono_left nhdsWithin_le_nhds).congr' h_ee
  · -- p = 4, left from seg4: constant deriv = I
    refine ⟨I, Complex.I_ne_zero, ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsLT (show (3:ℝ) < 4 by norm_num)] with s hs
      have hsm := mem_Ioo.mp hs
      exact (deriv_seg4_eq s hsm.1 hsm.2 (fdBoundary_eventuallyEq_seg4 s hsm.1 hsm.2)).symm)
  · -- p = 5, left from seg5: constant deriv = 1
    refine ⟨1, one_ne_zero, ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsLT (show (4:ℝ) < 5 by norm_num)] with s hs
      have hsm := mem_Ioo.mp hs
      exact (deriv_seg5_eq s hsm.1 (fdBoundary_eventuallyEq_seg5 s hsm.1)).symm)

set_option maxHeartbeats 400000 in
/-- Helper for right derivative limits at each partition point. -/
private theorem fdBoundary_right_deriv_limit (p : ℝ) (hp : p ∈ fdBoundaryFullPartition)
    (hpb : p < (5 : ℝ)) :
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv fdBoundary) (𝓝[>] p) (𝓝 L) := by
  simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · -- p = 0, right from seg1: constant deriv = -I
    refine ⟨-(1 : ℂ) * I, by simp [Complex.I_ne_zero], ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
      have hsm := mem_Ioo.mp hs
      exact (deriv_seg1_eq s hsm.2 (fdBoundary_eventuallyEq_seg1 s hsm.2)).symm)
  · -- p = 1, right from seg2: deriv = exp(π/3*I) * (π/6)*I
    refine ⟨Complex.exp ((↑(Real.pi / 3) : ℂ) * I) * (↑(Real.pi / 6) * I), ?_, ?_⟩
    · apply mul_ne_zero (exp_ne_zero _)
      exact mul_ne_zero (by rw [Complex.ofReal_ne_zero]; positivity) Complex.I_ne_zero
    · have h_ee : (fun s => Complex.exp ((↑(Real.pi / 3 + (s - 1) * (Real.pi / 6)) : ℂ) * I) *
            (↑(Real.pi / 6) * I)) =ᶠ[𝓝[>] 1] deriv fdBoundary := by
        filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 2 by norm_num)] with s hs
        have hsm := mem_Ioo.mp hs
        exact (deriv_seg2_eq s hsm.1 hsm.2 (fdBoundary_eventuallyEq_seg2 s hsm.1 hsm.2)).symm
      have h_cont := continuousAt_exp_arc_deriv (Real.pi / 3) 1 (Real.pi / 6) 1
      simp only [ContinuousAt] at h_cont
      rw [show Real.pi / 3 + ((1:ℝ) - 1) * (Real.pi / 6) = Real.pi / 3 from by ring] at h_cont
      exact (h_cont.mono_left nhdsWithin_le_nhds).congr' h_ee
  · -- p = 2, right from seg3: deriv = exp(π/2*I) * (π/6)*I
    refine ⟨Complex.exp ((↑(Real.pi / 2) : ℂ) * I) * (↑(Real.pi / 6) * I), ?_, ?_⟩
    · apply mul_ne_zero (exp_ne_zero _)
      exact mul_ne_zero (by rw [Complex.ofReal_ne_zero]; positivity) Complex.I_ne_zero
    · have h_ee : (fun s => Complex.exp ((↑(Real.pi / 2 + (s - 2) * (Real.pi / 6)) : ℂ) * I) *
            (↑(Real.pi / 6) * I)) =ᶠ[𝓝[>] 2] deriv fdBoundary := by
        filter_upwards [Ioo_mem_nhdsGT (show (2:ℝ) < 3 by norm_num)] with s hs
        have hsm := mem_Ioo.mp hs
        exact (deriv_seg3_eq s hsm.1 hsm.2 (fdBoundary_eventuallyEq_seg3 s hsm.1 hsm.2)).symm
      have h_cont := continuousAt_exp_arc_deriv (Real.pi / 2) 2 (Real.pi / 6) 2
      simp only [ContinuousAt] at h_cont
      rw [show Real.pi / 2 + ((2:ℝ) - 2) * (Real.pi / 6) = Real.pi / 2 from by ring] at h_cont
      exact (h_cont.mono_left nhdsWithin_le_nhds).congr' h_ee
  · -- p = 3, right from seg4: constant deriv = I
    refine ⟨I, Complex.I_ne_zero, ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (show (3:ℝ) < 4 by norm_num)] with s hs
      have hsm := mem_Ioo.mp hs
      exact (deriv_seg4_eq s hsm.1 hsm.2 (fdBoundary_eventuallyEq_seg4 s hsm.1 hsm.2)).symm)
  · -- p = 4, right from seg5: constant deriv = 1
    refine ⟨1, one_ne_zero, ?_⟩
    exact tendsto_const_nhds.congr' (by
      filter_upwards [Ioo_mem_nhdsGT (show (4:ℝ) < 5 by norm_num)] with s hs
      have hsm := mem_Ioo.mp hs
      exact (deriv_seg5_eq s hsm.1 (fdBoundary_eventuallyEq_seg5 s hsm.1)).symm)
  · -- p = 5, but 5 < 5 is false
    exact absurd hpb (lt_irrefl _)

/-- The boundary curve as a PiecewiseC1Immersion. -/
noncomputable def fdBoundaryImmersion : PiecewiseC1Immersion where
  toPiecewiseC1Curve := fdBoundaryCurve
  deriv_ne_zero := fdBoundary_deriv_ne_zero_off_partition
  left_deriv_limit := fdBoundary_left_deriv_limit
  right_deriv_limit := fdBoundary_right_deriv_limit

/-- The boundary immersion is a closed curve. -/
theorem fdBoundaryImmersion_closed : fdBoundaryImmersion.toPiecewiseC1Curve.IsClosed := by
  show fdBoundary 0 = fdBoundary 5
  exact fdBoundary_closed

end PiecewiseC1Adapter
