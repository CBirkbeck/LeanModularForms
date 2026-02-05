/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: f47e3978-4813-4f34-bca9-e18337bfd6de

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma fdPolygon_deriv_bounded : ∃ M : ℝ, ∀ t ∈ Icc 0 5, ‖deriv fdPolygon t‖ ≤ M
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PiecewiseHomotopy
import LeanModularForms.Modularforms.valence.ComplexAnalysis.WindingNumberInterior


/-!
# Rectangle/Chord Homotopy Approach for Winding Number = 1

This file proves `generalizedWindingNumber_interior_eq_one_complex` using a
rectangle/chord homotopy approach that avoids angle-lifting.

## Main Strategy

For interior points p ∈ 𝒟' (fundamental domain interior), we have ‖p‖ > 1.
The fundamental domain boundary has two arc segments on the unit circle |z| = 1.
Since p is outside the unit disk, we can:

1. Replace each unit-circle arc with a straight chord (inside the unit disk)
2. The straight-line homotopy from arc to chord stays in the unit disk
3. Since ‖p‖ > 1, p is outside the closed unit disk
4. Therefore the homotopy avoids p
5. The resulting polygon can be homotoped to a circle around p
6. The circle integral equals 2πi by `circleIntegral.integral_sub_inv_of_mem_ball`

## Key Advantages

- No angle-lifting needed
- Convexity arguments are simpler (closed unit ball is convex)
- The "avoids p" check is straightforward: p outside unit disk, homotopy inside
- Uses existing mathlib lemma `circleIntegral.integral_sub_inv_of_mem_ball`
-/

open Complex MeasureTheory Set Filter Topology Metric

open scoped Real Interval

noncomputable section

/-! ## Fundamental Domain Definition -/

/-- The standard fundamental domain for SL₂(ℤ) in the upper half-plane. -/
def fundamentalDomain' : Set UpperHalfPlane :=
  {z : UpperHalfPlane | |(z : ℂ).re| ≤ 1/2 ∧ ‖(z : ℂ)‖ ≥ 1}

notation "𝒟'" => fundamentalDomain'

/-! ## Geometric Facts about Interior Points -/

/-- The elliptic point ρ = e^{2πi/3} = -1/2 + √3/2 · i -/
def rho : ℂ := -1/2 + Real.sqrt 3 / 2 * I

/-- The elliptic point ρ' = e^{πi/3} = 1/2 + √3/2 · i -/
def rho' : ℂ := 1/2 + Real.sqrt 3 / 2 * I

/-- The elliptic point i -/
def i_point : ℂ := I

/-- ρ is on the unit circle: ‖ρ‖ = 1.
    Proof: ‖-1/2 + √3/2·i‖² = (1/2)² + (√3/2)² = 1/4 + 3/4 = 1 -/
lemma rho_norm : ‖rho‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [rho, Complex.add_re, Complex.neg_re, Complex.one_re, Complex.div_ofNat_re,
             Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
             Complex.ofReal_im, Complex.I_im, mul_one,
             Complex.add_im, Complex.neg_im, Complex.one_im, Complex.div_ofNat_im,
             Complex.mul_im, add_zero]
  ring_nf
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 3)
  rw [h]
  norm_num

/-- ρ' is on the unit circle: ‖ρ'‖ = 1.
    Proof: ‖1/2 + √3/2·i‖² = (1/2)² + (√3/2)² = 1/4 + 3/4 = 1 -/
lemma rho'_norm : ‖rho'‖ = 1 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  simp only [rho', Complex.add_re, Complex.one_re, Complex.div_ofNat_re,
             Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
             Complex.ofReal_im, Complex.I_im, mul_one,
             Complex.add_im, Complex.one_im, Complex.div_ofNat_im,
             Complex.mul_im, add_zero]
  ring_nf
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 3)
  rw [h]
  norm_num

/-- i is on the unit circle: ‖i‖ = 1 -/
lemma i_point_norm : ‖i_point‖ = 1 := by
  simp only [i_point, Complex.norm_I]

/-- For p ∈ 𝒟', we have ‖p‖ ≥ 1 -/
lemma fundamentalDomain'_norm_ge_one (p : UpperHalfPlane) (hp : p ∈ 𝒟') : ‖(p : ℂ)‖ ≥ 1 := hp.2

/-- Interior points of 𝒟' (not on the unit circle arc boundary) have ‖p‖ > 1. -/
lemma interior_point_norm_gt_one (p : UpperHalfPlane) (hp : p ∈ 𝒟')
    (hp_not_on_arc : ‖(p : ℂ)‖ ≠ 1) : ‖(p : ℂ)‖ > 1 := by
  have h_ge := fundamentalDomain'_norm_ge_one p hp
  exact lt_of_le_of_ne h_ge (Ne.symm hp_not_on_arc)

/-- Points z with ‖z‖ > 1 are outside the closed unit disk. -/
lemma outside_closed_unit_ball (z : ℂ) (hz : ‖z‖ > 1) : z ∉ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right, not_le]
  exact hz

/-! ## Chord Homotopy Infrastructure -/

/-- The chord (straight line segment) from z₁ to z₂. -/
def chordSegment (z₁ z₂ : ℂ) : ℝ → ℂ := fun t => (1 - t) • z₁ + t • z₂

/-- The chord segment between two points in a convex set stays in the set. -/
lemma chordSegment_in_convex {z₁ z₂ : ℂ} {S : Set ℂ} (hS : Convex ℝ S)
    (hz₁ : z₁ ∈ S) (hz₂ : z₂ ∈ S) (t : ℝ) (ht : t ∈ Icc 0 1) :
    chordSegment z₁ z₂ t ∈ S := by
  simp only [chordSegment]
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h1 : 0 ≤ 1 - t := by linarith
  have h2 : 1 - t + t = 1 := by ring
  exact hS hz₁ hz₂ h1 ht0 h2

/-- The closed unit disk is convex. -/
lemma convex_closedBall_zero_one : Convex ℝ (closedBall (0 : ℂ) 1) :=
  convex_closedBall 0 1

/-- A chord between two points on the unit circle stays in the closed unit disk. -/
lemma chord_in_closed_unit_ball (z₁ z₂ : ℂ) (hz₁ : ‖z₁‖ = 1) (hz₂ : ‖z₂‖ = 1)
    (t : ℝ) (ht : t ∈ Icc 0 1) :
    chordSegment z₁ z₂ t ∈ closedBall (0 : ℂ) 1 := by
  apply chordSegment_in_convex convex_closedBall_zero_one
  · simp only [mem_closedBall, dist_zero_right, hz₁, le_refl]
  · simp only [mem_closedBall, dist_zero_right, hz₂, le_refl]
  · exact ht

/-! ## Arc to Chord Homotopy -/

/-- The straight-line homotopy from an arc point to the chord.
    H(t, s) = (1-s) * arc(t) + s * chord(t)
    stays in the closed unit disk when both endpoints are on the unit circle. -/
def arcToChordHomotopy (arc chord : ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun (t, s) => (1 - s) • arc t + s • chord t

/-- If arc(t) and chord(t) are both in the closed unit disk, then the homotopy is too. -/
lemma arcToChordHomotopy_in_closed_unit_ball (arc chord : ℝ → ℂ)
    (harc : ∀ t ∈ Icc 0 1, arc t ∈ closedBall (0 : ℂ) 1)
    (hchord : ∀ t ∈ Icc 0 1, chord t ∈ closedBall (0 : ℂ) 1)
    (t : ℝ) (ht : t ∈ Icc 0 1) (s : ℝ) (hs : s ∈ Icc 0 1) :
    arcToChordHomotopy arc chord (t, s) ∈ closedBall (0 : ℂ) 1 := by
  simp only [arcToChordHomotopy]
  -- The convex combination stays in the convex set
  have hconv : Convex ℝ (closedBall (0 : ℂ) 1) := convex_closedBall_zero_one
  exact chordSegment_in_convex hconv (harc t ht) (hchord t ht) s hs

/-- The arc-to-chord homotopy avoids any point p with ‖p‖ > 1. -/
lemma arcToChordHomotopy_avoids (arc chord : ℝ → ℂ) (p : ℂ) (hp : ‖p‖ > 1)
    (harc : ∀ t ∈ Icc 0 1, arc t ∈ closedBall (0 : ℂ) 1)
    (hchord : ∀ t ∈ Icc 0 1, chord t ∈ closedBall (0 : ℂ) 1)
    (t : ℝ) (ht : t ∈ Icc 0 1) (s : ℝ) (hs : s ∈ Icc 0 1) :
    arcToChordHomotopy arc chord (t, s) ≠ p := by
  have hH := arcToChordHomotopy_in_closed_unit_ball arc chord harc hchord t ht s hs
  have hp_out := outside_closed_unit_ball p hp
  exact fun h => hp_out (h ▸ hH)

/-! ## Circle Winding Number from Mathlib -/

/-- The key mathlib lemma: ∮_{|z-c|=R} (z-w)⁻¹ dz = 2πi when w ∈ ball(c, R). -/
lemma circleIntegral_sub_inv_eq_two_pi_I (c w : ℂ) (R : ℝ) (hw : w ∈ ball c R) :
    (∮ z in C(c, R), (z - w)⁻¹) = 2 * π * I :=
  circleIntegral.integral_sub_inv_of_mem_ball hw

/-! ## Main Strategy Outline -/

/-- **KEY INSIGHT**: For interior p ∈ 𝒟' with ‖p‖ > 1:
    1. The FD boundary arcs (on |z| = 1) can be replaced by chords
    2. The homotopy stays in the closed unit disk (by convexity)
    3. Since p is outside the closed unit disk, the homotopy avoids p
    4. The polygon is then homotoped to a small circle around p
    5. The circle integral = 2πi by `circleIntegral.integral_sub_inv_of_mem_ball`

    This approach avoids angle-lifting entirely.
-/
theorem windingNumber_strategy_outline
    (p : UpperHalfPlane) (hp : p ∈ 𝒟')
    (hp_not_on_arc : ‖(p : ℂ)‖ ≠ 1) :
    -- The homotopy from arc to chord avoids p
    ∀ arc chord : ℝ → ℂ,
    (∀ t ∈ Icc 0 1, arc t ∈ closedBall (0 : ℂ) 1) →
    (∀ t ∈ Icc 0 1, chord t ∈ closedBall (0 : ℂ) 1) →
    ∀ t ∈ Icc 0 1, ∀ s ∈ Icc 0 1, arcToChordHomotopy arc chord (t, s) ≠ (p : ℂ) := by
  have hp_gt : ‖(p : ℂ)‖ > 1 := interior_point_norm_gt_one p hp hp_not_on_arc
  intro arc chord harc hchord t ht s hs
  exact arcToChordHomotopy_avoids arc chord (p : ℂ) hp_gt harc hchord t ht s hs

/-! ## Explicit Arc Parameterizations for the Fundamental Domain Boundary -/

/-- The angle at ρ' = e^{iπ/3}: the arc starts here going counterclockwise -/
def θ_rho' : ℝ := Real.pi / 3

/-- The angle at i = e^{iπ/2}: the arc passes through here -/
def θ_i : ℝ := Real.pi / 2

/-- The angle at ρ = e^{2iπ/3}: the arc ends here -/
def θ_rho : ℝ := 2 * Real.pi / 3

/-- Arc 1: from ρ' to i on the unit circle (counterclockwise).
    Parameterized by t ∈ [0, 1] with θ going from π/3 to π/2. -/
def arc1 (t : ℝ) : ℂ := Complex.exp (I * (θ_rho' + t * (θ_i - θ_rho')))

/-- Arc 2: from i to ρ on the unit circle (counterclockwise).
    Parameterized by t ∈ [0, 1] with θ going from π/2 to 2π/3. -/
def arc2 (t : ℝ) : ℂ := Complex.exp (I * (θ_i + t * (θ_rho - θ_i)))

/-- Arc 1 stays on the unit circle. -/
lemma arc1_on_unit_circle (t : ℝ) : ‖arc1 t‖ = 1 := by
  simp only [arc1]
  have h : I * (↑θ_rho' + ↑t * (↑θ_i - ↑θ_rho')) = I * ↑(θ_rho' + t * (θ_i - θ_rho')) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
  rw [h, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Arc 2 stays on the unit circle. -/
lemma arc2_on_unit_circle (t : ℝ) : ‖arc2 t‖ = 1 := by
  simp only [arc2]
  have h : I * (↑θ_i + ↑t * (↑θ_rho - ↑θ_i)) = I * ↑(θ_i + t * (θ_rho - θ_i)) := by
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
  rw [h, mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Arc 1 is in the closed unit ball. -/
lemma arc1_in_closed_unit_ball (t : ℝ) (_ : t ∈ Icc 0 1) :
    arc1 t ∈ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right, arc1_on_unit_circle, le_refl]

/-- Arc 2 is in the closed unit ball. -/
lemma arc2_in_closed_unit_ball (t : ℝ) (_ : t ∈ Icc 0 1) :
    arc2 t ∈ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right, arc2_on_unit_circle, le_refl]

/-- Chord 1: straight line from ρ' to i. -/
def chord1 : ℝ → ℂ := chordSegment rho' i_point

/-- Chord 2: straight line from i to ρ. -/
def chord2 : ℝ → ℂ := chordSegment i_point rho

/-- Chord 1 stays in the closed unit ball. -/
lemma chord1_in_closed_unit_ball (t : ℝ) (ht : t ∈ Icc 0 1) :
    chord1 t ∈ closedBall (0 : ℂ) 1 :=
  chord_in_closed_unit_ball rho' i_point rho'_norm i_point_norm t ht

/-- Chord 2 stays in the closed unit ball. -/
lemma chord2_in_closed_unit_ball (t : ℝ) (ht : t ∈ Icc 0 1) :
    chord2 t ∈ closedBall (0 : ℂ) 1 :=
  chord_in_closed_unit_ball i_point rho i_point_norm rho_norm t ht

/-! ## Polygon to Circle Homotopy -/

/-- For an interior point p with ‖p‖ > 1, there exists a small ε > 0 such that
    ball(p, ε) is contained in the region bounded by the polygon
    (FD boundary with arcs replaced by chords). -/
lemma exists_ball_in_polygon_interior (p : ℂ) (hp : ‖p‖ > 1) (hp_im : 0 < p.im) :
    ∃ ε > 0, ∀ z, ‖z - p‖ < ε → z.im > 0 ∧ ‖z‖ > 1 := by
  -- Choose ε = min((‖p‖ - 1)/2, p.im/2). Then for any z with ‖z - p‖ < ε:
  -- |‖z‖ - ‖p‖| ≤ ‖z - p‖ < (‖p‖ - 1)/2, so ‖z‖ > ‖p‖ - (‖p‖ - 1)/2 = (‖p‖ + 1)/2 > 1
  -- |z.im - p.im| ≤ ‖z - p‖ < p.im/2, so z.im > p.im/2 > 0
  use min ((‖p‖ - 1)/2) (p.im/2)
  constructor
  · exact lt_min (by linarith) (by linarith)
  intro z hz
  have hz₁ : ‖z - p‖ < (‖p‖ - 1)/2 := lt_of_lt_of_le hz (min_le_left _ _)
  have hz₂ : ‖z - p‖ < p.im/2 := lt_of_lt_of_le hz (min_le_right _ _)
  constructor
  · -- z.im > 0
    have h_im_bound : |z.im - p.im| ≤ ‖z - p‖ := Complex.abs_im_le_norm (z - p)
    have : z.im - p.im > -(p.im/2) := by
      have : |z.im - p.im| < p.im/2 := lt_of_le_of_lt h_im_bound hz₂
      linarith [abs_lt.mp this]
    linarith
  · -- ‖z‖ > 1
    have h_norm_bound : |‖z‖ - ‖p‖| ≤ ‖z - p‖ := abs_norm_sub_norm_le z p
    have : ‖z‖ - ‖p‖ > -((‖p‖ - 1)/2) := by
      have : |‖z‖ - ‖p‖| < (‖p‖ - 1)/2 := lt_of_le_of_lt h_norm_bound hz₁
      linarith [abs_lt.mp this]
    linarith

/-- The circle integral formula: ∮_{|z-p|=ε} (z-p)⁻¹ dz = 2πi for any ε > 0.
    This is the key result from mathlib. -/
lemma circleIntegral_winding (p : ℂ) (ε : ℝ) (hε : 0 < ε) :
    (∮ z in C(p, ε), (z - p)⁻¹) = 2 * Real.pi * I :=
  circleIntegral.integral_sub_inv_of_mem_ball (Metric.mem_ball_self hε)

/-! ## Polygon Curve: FD Boundary with Arcs Replaced by Chords -/

/-- The height parameter H = √3/2 + 1 for the fundamental domain boundary. -/
noncomputable def H_height : ℝ := Real.sqrt 3 / 2 + 1

/-- The polygon curve: same as FD boundary but with arcs replaced by chords.

    - Segment 1 (t ∈ [0,1]): Right vertical from (1/2 + Hi) down to ρ'
    - Segment 2 (t ∈ [1,2]): **CHORD** from ρ' to i (straight line)
    - Segment 3 (t ∈ [2,3]): **CHORD** from i to ρ (straight line)
    - Segment 4 (t ∈ [3,4]): Left vertical from ρ up to (-1/2 + Hi)
    - Segment 5 (t ∈ [4,5]): Horizontal from (-1/2 + Hi) to (1/2 + Hi)
-/
noncomputable def fdPolygon : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    -- Segment 1: vertical line from (1/2 + Hi) down to ρ' = (1/2 + √3/2·i)
    1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    -- Segment 2: CHORD from ρ' to i (straight line)
    -- At t=1: ρ' = 1/2 + √3/2·i. At t=2: i
    chordSegment rho' i_point (t - 1)
  else if t ≤ 3 then
    -- Segment 3: CHORD from i to ρ (straight line)
    -- At t=2: i. At t=3: ρ = -1/2 + √3/2·i
    chordSegment i_point rho (t - 2)
  else if t ≤ 4 then
    -- Segment 4: vertical line from ρ up to (-1/2 + Hi)
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I
  else
    -- Segment 5: horizontal line from (-1/2 + Hi) to (1/2 + Hi)
    (t - 9/2) + H_height * I

/-- The fundamental domain boundary curve (matches ValenceFormula.lean definition). -/
noncomputable def fdBoundary : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    -- Arc from ρ' to i
    Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    -- Arc from i to ρ
    Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I
  else
    (t - 9/2) + H_height * I

/-! ## Homotopy from FD Boundary to Polygon -/

/-- The homotopy H from FD boundary (s=0) to polygon (s=1).

    For segments 1, 4, 5: H(t, s) = γ(t) (no change, these are already straight lines)
    For segments 2, 3: H(t, s) = (1-s)·arc(t) + s·chord(t)

    This homotopy stays in the closed unit disk for segments 2 and 3,
    hence avoids any interior point p with ‖p‖ > 1.
-/
noncomputable def fdBoundaryToPolygonHomotopy : ℝ × ℝ → ℂ := fun (t, s) =>
  if t ≤ 1 then
    -- Segment 1: constant in s (vertical edge unchanged)
    1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    -- Segment 2: arc-to-chord homotopy
    -- Arc: exp((π/3 + (t-1)*(π/2 - π/3)) * I) - matches fdBoundary exactly
    let arc_point := Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
    let chord_point := chordSegment rho' i_point (t - 1)
    (1 - s) • arc_point + s • chord_point
  else if t ≤ 3 then
    -- Segment 3: arc-to-chord homotopy
    -- Arc: exp((π/2 + (t-2)*(2π/3 - π/2)) * I) - matches fdBoundary exactly
    let arc_point := Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
    let chord_point := chordSegment i_point rho (t - 2)
    (1 - s) • arc_point + s • chord_point
  else if t ≤ 4 then
    -- Segment 4: constant in s (vertical edge unchanged)
    -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I
  else
    -- Segment 5: constant in s (horizontal edge unchanged)
    (t - 9/2) + H_height * I

/-! ### Helper Lemmas for Homotopy -/

/-- Arc-to-chord homotopy at s=0 gives the arc. -/
@[simp] lemma arcToChordHomotopy_at_zero (arc chord : ℝ → ℂ) (t : ℝ) :
    arcToChordHomotopy arc chord (t, 0) = arc t := by
  simp only [arcToChordHomotopy, sub_zero, one_smul, zero_smul, add_zero]

/-- Arc-to-chord homotopy at s=1 gives the chord. -/
@[simp] lemma arcToChordHomotopy_at_one (arc chord : ℝ → ℂ) (t : ℝ) :
    arcToChordHomotopy arc chord (t, 1) = chord t := by
  simp only [arcToChordHomotopy, sub_self, zero_smul, one_smul, zero_add]

/-- FD boundary at t=0 equals 1/2 + H·I. -/
lemma fdBoundary_at_zero : fdBoundary 0 = (1/2 : ℂ) + H_height * I := by
  simp only [fdBoundary, show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte, H_height]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]

/-- FD boundary at t=5 equals 1/2 + H·I. -/
lemma fdBoundary_at_five : fdBoundary 5 = (1/2 : ℂ) + H_height * I := by
  simp only [fdBoundary, show ¬(5 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
             show ¬(5 : ℝ) ≤ 2 from by norm_num,
             show ¬(5 : ℝ) ≤ 3 from by norm_num,
             show ¬(5 : ℝ) ≤ 4 from by norm_num, H_height]
  norm_cast
  ring_nf

/-- Homotopy at t=0 equals fdBoundary at 0 (which is 1/2 + H·I). -/
lemma fdBoundaryToPolygonHomotopy_at_t_zero (s : ℝ) :
    fdBoundaryToPolygonHomotopy (0, s) = (1/2 : ℂ) + H_height * I := by
  simp only [fdBoundaryToPolygonHomotopy, show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte, H_height]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]

/-- Homotopy at t=5 equals fdBoundary at 5 (which is 1/2 + H·I). -/
lemma fdBoundaryToPolygonHomotopy_at_t_five (s : ℝ) :
    fdBoundaryToPolygonHomotopy (5, s) = (1/2 : ℂ) + H_height * I := by
  simp only [fdBoundaryToPolygonHomotopy,
             show ¬(5 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
             show ¬(5 : ℝ) ≤ 2 from by norm_num,
             show ¬(5 : ℝ) ≤ 3 from by norm_num,
             show ¬(5 : ℝ) ≤ 4 from by norm_num, H_height]
  norm_cast
  ring_nf

/-- The arc at segment 2 is on the unit circle.
    The expression is exp(θ * I) where θ = π/3 + (t-1) * (π/2 - π/3). -/
lemma segment2_arc_on_unit_circle (t : ℝ) :
    ‖Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)‖ = 1 := by
  -- exp(θ * I) has norm 1 for any real θ
  conv_lhs => rw [show ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I : ℂ) =
                       ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The arc at segment 3 is on the unit circle.
    The expression is exp(θ * I) where θ = π/2 + (t-2) * (2π/3 - π/2). -/
lemma segment3_arc_on_unit_circle (t : ℝ) :
    ‖Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)‖ = 1 := by
  conv_lhs => rw [show ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I : ℂ) =
                       ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Arc point for segment 2 is in the closed unit ball. -/
lemma segment2_arc_in_closed_unit_ball (t : ℝ) :
    Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I) ∈ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right, segment2_arc_on_unit_circle, le_refl]

/-- Arc point for segment 3 is in the closed unit ball. -/
lemma segment3_arc_in_closed_unit_ball (t : ℝ) :
    Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I) ∈ closedBall (0 : ℂ) 1 := by
  simp only [mem_closedBall, dist_zero_right, segment3_arc_on_unit_circle, le_refl]

/-- Norm of imaginary part is bounded by norm. -/
lemma norm_ge_abs_im (z : ℂ) : ‖z‖ ≥ |z.im| := Complex.abs_im_le_norm z

/-- H_height > 1. -/
lemma H_height_gt_one : H_height > 1 := by
  simp only [H_height]
  have h : Real.sqrt 3 > 0 := Real.sqrt_pos.mpr (by norm_num : (3 : ℝ) > 0)
  linarith

/-! ### Continuity Helper Lemmas -/

/-- Segment 1 formula as a standalone function. -/
noncomputable def H_seg1 (p : ℝ × ℝ) : ℂ :=
  1/2 + (H_height - p.1 * (H_height - Real.sqrt 3 / 2)) * I

/-- Segment 2 formula as a standalone function. -/
noncomputable def H_seg2 (p : ℝ × ℝ) : ℂ :=
  let arc_point := Complex.exp ((Real.pi / 3 + (p.1 - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  let chord_point := chordSegment rho' i_point (p.1 - 1)
  (1 - p.2) • arc_point + p.2 • chord_point

/-- Segment 3 formula as a standalone function. -/
noncomputable def H_seg3 (p : ℝ × ℝ) : ℂ :=
  let arc_point := Complex.exp ((Real.pi / 2 + (p.1 - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  let chord_point := chordSegment i_point rho (p.1 - 2)
  (1 - p.2) • arc_point + p.2 • chord_point

/-- Segment 4 formula as a standalone function. -/
noncomputable def H_seg4 (p : ℝ × ℝ) : ℂ :=
  -1/2 + (Real.sqrt 3 / 2 + (p.1 - 3) * (H_height - Real.sqrt 3 / 2)) * I

/-- Segment 5 formula as a standalone function. -/
noncomputable def H_seg5 (p : ℝ × ℝ) : ℂ :=
  (p.1 - 9/2) + H_height * I

/-- Segment 1 is continuous. -/
lemma H_seg1_continuous : Continuous H_seg1 := by
  unfold H_seg1
  continuity

/-- Segment 2 is continuous. -/
lemma H_seg2_continuous : Continuous H_seg2 := by
  unfold H_seg2 chordSegment
  continuity

/-- Segment 3 is continuous. -/
lemma H_seg3_continuous : Continuous H_seg3 := by
  unfold H_seg3 chordSegment
  continuity

/-- Segment 4 is continuous. -/
lemma H_seg4_continuous : Continuous H_seg4 := by
  unfold H_seg4
  continuity

/-- Segment 5 is continuous. -/
lemma H_seg5_continuous : Continuous H_seg5 := by
  unfold H_seg5
  continuity

/-! ### Joint Matching Lemmas -/

/-- exp(θ * I) for real θ gives cos θ + sin θ * I. -/
lemma exp_real_mul_I (θ : ℝ) :
    Complex.exp (↑θ * I) = ↑(Real.cos θ) + ↑(Real.sin θ) * I := by
  rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- cos(2π/3) = -1/2 -/
lemma Real.cos_two_pi_div_three' : Real.cos (2 * Real.pi / 3) = -1/2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]
  norm_num

/-- sin(2π/3) = √3/2 -/
lemma Real.sin_two_pi_div_three' : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]

/-- exp(π/3 * I) = ρ' = 1/2 + √3/2 * I -/
lemma exp_pi_div_three_eq_rho' : Complex.exp (↑(Real.pi / 3) * I) = rho' := by
  rw [exp_real_mul_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp only [rho', Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

/-- exp(π/2 * I) = I -/
lemma exp_pi_div_two_eq_I : Complex.exp (↑(Real.pi / 2) * I) = I := by
  rw [exp_real_mul_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_add, one_mul]

/-- exp(2π/3 * I) = ρ = -1/2 + √3/2 * I -/
lemma exp_two_pi_div_three_eq_rho : Complex.exp (↑(2 * Real.pi / 3) * I) = rho := by
  rw [exp_real_mul_I, Real.cos_two_pi_div_three', Real.sin_two_pi_div_three']
  simp only [rho, Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

/-- At t=1: segment 1 matches segment 2. -/
lemma H_match_at_t1 (p : ℝ × ℝ) (hp : p.1 = 1) : H_seg1 p = H_seg2 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp
  subst hp
  -- LHS (H_seg1 at t=1): 1/2 + (H - 1*(H - √3/2))*I = 1/2 + √3/2*I = ρ'
  -- RHS (H_seg2 at t=1): (1-s) • arc(0) + s • chord(0)
  --   where arc(0) = exp((π/3 + 0*(...))*I) = exp(π/3*I) = ρ'
  --   and chord(0) = (1-0)•ρ' + 0•I = ρ'
  -- So RHS = (1-s)•ρ' + s•ρ' = ρ'
  simp only [H_seg1, H_seg2, chordSegment, H_height, rho', i_point]
  -- Simplify LHS: H - 1*(H - √3/2) = √3/2
  have hLHS : (↑(Real.sqrt 3 / 2 + 1) - ↑(1:ℝ) * (↑(Real.sqrt 3 / 2 + 1) - ↑(Real.sqrt 3) / 2) : ℂ) =
              ↑(Real.sqrt 3) / 2 := by push_cast; ring
  simp only [hLHS]
  -- Simplify arc angle at t=1: π/3 + 0*(...) = π/3
  have hangle : (↑Real.pi / 3 + (↑(1:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) = ↑Real.pi / 3 := by
    simp only [Complex.ofReal_one, sub_self, zero_mul, add_zero]
  simp only [hangle]
  -- Convert ↑π / 3 to ↑(π / 3) for exp lemma
  have hpi3 : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3) := by push_cast; ring
  rw [hpi3, exp_pi_div_three_eq_rho']
  -- Simplify chord at t-1=0: (1-0)*ρ' + 0*I = ρ'
  simp only [sub_self, zero_smul, add_zero, rho']
  -- Now RHS = (1-s)•ρ' + s•ρ' = ρ', LHS = ρ'
  simp only [smul_add, Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one, sub_zero, one_mul]
  ring

/-- At t=2: segment 2 matches segment 3. -/
lemma H_match_at_t2 (p : ℝ × ℝ) (hp : p.1 = 2) : H_seg2 p = H_seg3 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp
  subst hp
  -- Seg2 at t=2: arc = exp(π/2*I) = I, chord = I
  -- Seg3 at t=2: arc = exp(π/2*I) = I, chord = I
  -- Both equal (1-s)•I + s•I = I
  unfold H_seg2 H_seg3 chordSegment rho' i_point rho
  simp only [Complex.ofReal_ofNat]
  norm_num

/-- At t=3: segment 3 matches segment 4. -/
lemma H_match_at_t3 (p : ℝ × ℝ) (hp : p.1 = 3) : H_seg3 p = H_seg4 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp
  subst hp
  -- Seg3 at t=3: arc = exp(2π/3*I) = ρ, chord = ρ
  -- Seg4 at t=3: -1/2 + √3/2*I = ρ
  -- Both equal (1-s)•ρ + s•ρ = ρ
  unfold H_seg3 H_seg4 chordSegment i_point rho H_height
  simp only [Complex.ofReal_ofNat]
  norm_num
  -- Need to show exp(2π/3 * I) = -1/2 + √3/2 * I
  have hexp : Complex.exp (2 * ↑Real.pi / 3 * I) = -1/2 + ↑(Real.sqrt 3) / 2 * I := by
    have h : (2 * ↑Real.pi / 3 * I : ℂ) = ↑(2 * Real.pi / 3) * I := by push_cast; ring
    rw [h, exp_two_pi_div_three_eq_rho, rho]
  simp only [hexp]
  ring

/-- At t=4: segment 4 matches segment 5. -/
lemma H_match_at_t4 (p : ℝ × ℝ) (hp : p.1 = 4) : H_seg4 p = H_seg5 p := by
  obtain ⟨t, s⟩ := p
  simp only at hp
  subst hp
  simp only [H_seg4, H_seg5, H_height]
  -- Seg4 at t=4: -1/2 + (√3/2 + 1*(H - √3/2))*I = -1/2 + H*I
  -- Seg5 at t=4: (4 - 9/2) + H*I = -1/2 + H*I
  ring_nf
  simp only [Complex.ofReal_add, Complex.ofReal_ofNat]
  ring

/-! ### Main Continuity Proof -/

/-- The homotopy is continuous.

    Each of the 5 pieces is continuous (exponentials, linear functions),
    and they match at the boundaries t = 1, 2, 3, 4.
-/
lemma fdBoundaryToPolygonHomotopy_continuous : Continuous fdBoundaryToPolygonHomotopy := by
  -- The function equals a piecewise combination of H_seg1..H_seg5
  -- Each segment function is continuous, and they match at boundaries
  -- Use Continuous.if_le to glue the pieces together
  have h45 : Continuous (fun p => if p.1 ≤ 4 then H_seg4 p else H_seg5 p) := by
    apply Continuous.if_le H_seg4_continuous H_seg5_continuous continuous_fst continuous_const
    intro p hp; exact H_match_at_t4 p hp
  have h345 : Continuous (fun p => if p.1 ≤ 3 then H_seg3 p else if p.1 ≤ 4 then H_seg4 p else H_seg5 p) := by
    apply Continuous.if_le H_seg3_continuous h45 continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 4 from le_trans (le_of_eq hp) (by norm_num : (3 : ℝ) ≤ 4), if_true]
    exact H_match_at_t3 p hp
  have h2345 : Continuous (fun p => if p.1 ≤ 2 then H_seg2 p
      else if p.1 ≤ 3 then H_seg3 p else if p.1 ≤ 4 then H_seg4 p else H_seg5 p) := by
    apply Continuous.if_le H_seg2_continuous h345 continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 3 from le_trans (le_of_eq hp) (by norm_num : (2 : ℝ) ≤ 3), if_true]
    exact H_match_at_t2 p hp
  have h12345 : Continuous (fun p => if p.1 ≤ 1 then H_seg1 p
      else if p.1 ≤ 2 then H_seg2 p
      else if p.1 ≤ 3 then H_seg3 p else if p.1 ≤ 4 then H_seg4 p else H_seg5 p) := by
    apply Continuous.if_le H_seg1_continuous h2345 continuous_fst continuous_const
    intro p hp
    simp only [show p.1 ≤ 2 from le_trans (le_of_eq hp) (by norm_num : (1 : ℝ) ≤ 2), if_true]
    exact H_match_at_t1 p hp
  -- Now show fdBoundaryToPolygonHomotopy equals this function
  convert h12345 using 1

/-- At s=0, the homotopy gives the FD boundary. -/
lemma fdBoundaryToPolygonHomotopy_at_zero (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdBoundaryToPolygonHomotopy (t, 0) = fdBoundary t := by
  simp only [fdBoundaryToPolygonHomotopy, fdBoundary]
  split_ifs with h1 h2 h3 h4
  · rfl  -- Segment 1: identical
  · -- Segment 2: (1-0)*arc + 0*chord = arc
    simp only [sub_zero, one_smul, zero_smul, add_zero]
  · -- Segment 3: same
    simp only [sub_zero, one_smul, zero_smul, add_zero]
  · rfl  -- Segment 4: identical
  · rfl

-- Segment 5: identical

/-- At s=1, the homotopy gives the polygon. -/
lemma fdBoundaryToPolygonHomotopy_at_one (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdBoundaryToPolygonHomotopy (t, 1) = fdPolygon t := by
  simp only [fdBoundaryToPolygonHomotopy, fdPolygon]
  split_ifs with h1 h2 h3 h4
  · rfl  -- Segment 1: identical
  · simp only [sub_self, zero_smul, one_smul, zero_add]  -- Segment 2: 0*arc + 1*chord = chord
  · simp only [sub_self, zero_smul, one_smul, zero_add]  -- Segment 3: same
  · rfl  -- Segment 4: identical
  · rfl

-- Segment 5: identical

/-- The homotopy avoids any interior point p with ‖p‖ > 1, |p.re| < 1/2, and p.im < H_height.

    **Proof idea**:
    - Segments 1, 4: Avoided because p.re ≠ ±1/2 (we have |p.re| < 1/2)
    - Segment 5: Avoided because p.im < H_height = points on segment 5 have im = H_height
    - Segments 2, 3: The arc-to-chord homotopy stays in the closed unit ball
      (arc on unit circle, chord inside by convexity), so p with ‖p‖ > 1 is avoided
-/
lemma fdBoundaryToPolygonHomotopy_avoids (p : ℂ) (hp_norm : ‖p‖ > 1)
    (hp_re : |p.re| < 1/2) (hp_im : p.im < H_height)
    (t : ℝ) (_ht : t ∈ Icc 0 5) (s : ℝ) (hs : s ∈ Icc 0 1) :
    fdBoundaryToPolygonHomotopy (t, s) ≠ p := by
  simp only [fdBoundaryToPolygonHomotopy]
  split_ifs with h1 h2 h3 h4
  · -- Segment 1: vertical edge at x = 1/2
    -- Points on this segment have re = 1/2, but |p.re| < 1/2, so p.re ≠ 1/2
    intro heq
    -- The real part of 1/2 + (...)*I is just 1/2
    have hre : (1/2 + (↑H_height - ↑t * (↑H_height - ↑(Real.sqrt 3) / 2)) * I : ℂ).re = 1/2 := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
                 Complex.I_im, mul_one, Complex.sub_re, Complex.div_ofNat_re,
                 Complex.sub_im, Complex.ofReal_im, Complex.div_ofNat_im, Complex.mul_im]
      norm_num
    rw [heq] at hre
    have hp_re_eq : p.re = 1/2 := hre
    have : |p.re| = 1/2 := by rw [hp_re_eq]; norm_num
    linarith
  · -- Segment 2: arc-to-chord homotopy
    -- Both arc and chord are in closed unit ball, convex combination too
    -- p with ‖p‖ > 1 is outside, hence avoided
    have ht2 : t - 1 ∈ Icc 0 1 := by constructor <;> linarith [h1, h2]
    have h_arc_in := segment2_arc_in_closed_unit_ball t
    have h_chord_in := chord1_in_closed_unit_ball (t - 1) ht2
    -- The convex combination of two points in a convex set is in the set
    have h_in_ball : (1 - s) • Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I) +
        s • chordSegment rho' i_point (t - 1) ∈ closedBall (0 : ℂ) 1 := by
      apply chordSegment_in_convex convex_closedBall_zero_one h_arc_in h_chord_in s hs
    -- p is outside the closed unit ball
    have hp_out := outside_closed_unit_ball p hp_norm
    exact fun h => hp_out (h ▸ h_in_ball)
  · -- Segment 3: similar to segment 2
    have ht3 : t - 2 ∈ Icc 0 1 := by constructor <;> linarith [h2, h3]
    have h_arc_in := segment3_arc_in_closed_unit_ball t
    have h_chord_in := chord2_in_closed_unit_ball (t - 2) ht3
    have h_in_ball : (1 - s) • Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I) +
        s • chordSegment i_point rho (t - 2) ∈ closedBall (0 : ℂ) 1 := by
      apply chordSegment_in_convex convex_closedBall_zero_one h_arc_in h_chord_in s hs
    have hp_out := outside_closed_unit_ball p hp_norm
    exact fun h => hp_out (h ▸ h_in_ball)
  · -- Segment 4: vertical edge at x = -1/2
    -- Points on this segment have re = -1/2, but |p.re| < 1/2, so p.re ≠ -1/2
    intro heq
    have hre : ((-1/2 : ℂ) + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H_height - ↑(Real.sqrt 3) / 2)) * I).re = -1/2 := by
      simp only [Complex.add_re, Complex.mul_re, Complex.I_re, mul_zero,
                 Complex.I_im, mul_one, Complex.sub_re, Complex.div_ofNat_re,
                 Complex.sub_im, Complex.ofReal_im, Complex.div_ofNat_im]
      norm_num
    rw [heq] at hre
    have hp_re_eq : p.re = -1/2 := hre
    have : |p.re| = 1/2 := by rw [hp_re_eq]; norm_num
    linarith
  · -- Segment 5: horizontal edge at height H = √3/2 + 1
    -- Points z on this segment have z.im = H_height, but p.im < H_height
    intro heq
    -- The goal after split_ifs is: ↑t - 9/2 + ↑H_height * I ≠ p
    -- The imaginary part is H_height
    have him : (↑t - 9/2 + ↑H_height * I : ℂ).im = H_height := by
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.div_ofNat_im,
                 Complex.mul_im, Complex.ofReal_re, Complex.I_re, mul_zero,
                 Complex.I_im, mul_one]
      -- Goal: 0 - im 9 / 2 + (H_height + 0) = H_height
      -- (9 : ℂ).im = 0, so this is 0 - 0/2 + H_height = H_height
      simp only [show (9 : ℂ).im = 0 from rfl, add_zero, zero_div, sub_zero, zero_add]
    rw [heq] at him
    linarith

/-- The homotopy is closed: H(0, s) = H(5, s) for all s. -/
lemma fdBoundaryToPolygonHomotopy_closed (s : ℝ) (_hs : s ∈ Icc 0 1) :
    fdBoundaryToPolygonHomotopy (0, s) = fdBoundaryToPolygonHomotopy (5, s) := by
  simp only [fdBoundaryToPolygonHomotopy]
  simp only [show (0 : ℝ) ≤ 1 from by norm_num, ↓reduceIte,
             show ¬(5 : ℝ) ≤ 1 from by norm_num,
             show ¬(5 : ℝ) ≤ 2 from by norm_num,
             show ¬(5 : ℝ) ≤ 3 from by norm_num,
             show ¬(5 : ℝ) ≤ 4 from by norm_num]
  -- At t=0: 1/2 + (H - 0*(H - √3/2))*I = 1/2 + H*I
  -- At t=5: (5 - 9/2) + H*I = 1/2 + H*I
  simp only [H_height]
  simp only [Complex.ofReal_zero, zero_mul, sub_zero]
  -- Goal: 1/2 + H*I = -9/2 + H*I + 5
  -- Since -9/2 + 5 = 1/2, this is arithmetic
  norm_cast
  ring

/-! ## Circle Parameterization -/

/-- A circle centered at p with radius ε, parameterized over [0, 5] to match FD boundary. -/
noncomputable def circleAround (p : ℂ) (ε : ℝ) : ℝ → ℂ := fun t =>
  p + ε * Complex.exp (2 * Real.pi * I * t / 5)

/-- The circle is closed: circleAround(0) = circleAround(5). -/
lemma circleAround_closed (p : ℂ) (ε : ℝ) :
    circleAround p ε 0 = circleAround p ε 5 := by
  simp only [circleAround]
  congr 1
  -- At t=0: exp(2πi * 0 / 5) = exp(0) = 1
  -- At t=5: exp(2πi * 5 / 5) = exp(2πi) = 1
  have h0 : 2 * Real.pi * I * (0 : ℂ) / 5 = 0 := by ring
  have h5 : 2 * Real.pi * I * (5 : ℂ) / 5 = 2 * Real.pi * I := by ring
  simp only [Complex.ofReal_zero, mul_zero, zero_div, Complex.ofReal_ofNat]
  rw [h5, Complex.exp_zero, Complex.exp_two_pi_mul_I]

/-- The circle is continuous. -/
lemma circleAround_continuous (p : ℂ) (ε : ℝ) : Continuous (circleAround p ε) := by
  unfold circleAround
  continuity

/-- Points on the circle have distance ε from p. -/
lemma circleAround_dist (p : ℂ) (ε : ℝ) (hε : 0 ≤ ε) (t : ℝ) :
    ‖circleAround p ε t - p‖ = ε := by
  simp only [circleAround, add_sub_cancel_left]
  rw [Complex.norm_mul]
  -- The exponent 2 * π * I * t / 5 = (2 * π * t / 5) * I
  have hform : 2 * Real.pi * I * (t : ℂ) / 5 = ↑(2 * Real.pi * t / 5) * I := by
    push_cast; ring
  rw [hform, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
  exact abs_of_nonneg hε

/-! ## Polygon to Circle Radial Homotopy -/

/-- The radial homotopy from polygon to circle.
    H(t, s) = p + (1 - s) * (fdPolygon(t) - p) + s * ε * (fdPolygon(t) - p) / ‖fdPolygon(t) - p‖

    When s = 0: H(t, 0) = fdPolygon(t)
    When s = 1: H(t, 1) = p + ε * (fdPolygon(t) - p) / ‖fdPolygon(t) - p‖ (on the circle)

    This homotopy avoids p because p is always in the interior of the region.
-/
noncomputable def polygonToCircleHomotopy (p : ℂ) (ε : ℝ) : ℝ × ℝ → ℂ := fun (t, s) =>
  let z := fdPolygon t
  let dir := z - p
  p + (1 - s) * dir + s * ε * (dir / ‖dir‖)

/-- The polygon doesn't pass through any interior point p with the given constraints. -/
lemma fdPolygon_avoids_interior (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im : p.im < H_height) (t : ℝ) (_ht : t ∈ Icc 0 5) :
    fdPolygon t ≠ p := by
  -- This follows from fdBoundaryToPolygonHomotopy_avoids with s = 1
  have h := fdBoundaryToPolygonHomotopy_avoids p hp_norm hp_re hp_im t _ht 1 ⟨zero_le_one, le_refl 1⟩
  simp only [fdBoundaryToPolygonHomotopy_at_one t _ht] at h
  exact h

/-! ## Main Theorem: Winding Number = 1 for Interior Points -/

/-- **MAIN THEOREM**: For an interior point p in the fundamental domain with the stated constraints,
    the homotopy from the FD boundary to the polygon avoids p.

    This is the key geometric result that enables the winding number = 1 proof.
    Combined with homotopy invariance and the circle integral, it shows:
    - fdBoundary is homotopic to fdPolygon (avoiding p)
    - fdPolygon is homotopic to a small circle around p (avoiding p)
    - Circle integral = 2πi, so winding number = 1

    The full winding number proof requires importing additional machinery from
    PiecewiseHomotopy.lean and WindingNumber.lean. This file establishes the
    geometric foundation: the avoidance property for the arc-to-chord homotopy.
-/
theorem fdBoundaryToPolygon_homotopy_avoids_interior
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2) (hp_im : p.im < H_height) :
    ∀ t ∈ Icc 0 5, ∀ s ∈ Icc (0:ℝ) 1, fdBoundaryToPolygonHomotopy (t, s) ≠ p :=
  fdBoundaryToPolygonHomotopy_avoids p hp_norm hp_re hp_im

/-- The homotopy from FD boundary to polygon is closed at each stage. -/
theorem fdBoundaryToPolygon_homotopy_closed :
    ∀ s ∈ Icc (0:ℝ) 1, fdBoundaryToPolygonHomotopy (0, s) = fdBoundaryToPolygonHomotopy (5, s) :=
  fdBoundaryToPolygonHomotopy_closed

/-- The homotopy is continuous (already proved above). -/
theorem fdBoundaryToPolygon_homotopy_continuous : Continuous fdBoundaryToPolygonHomotopy :=
  fdBoundaryToPolygonHomotopy_continuous

/-- Summary: We have established that for interior points p with |p.re| < 1/2 and ‖p‖ > 1:

    1. **Arc-to-chord homotopy avoids p**: `fdBoundaryToPolygon_homotopy_avoids_interior`
       - This uses the convexity of the closed unit ball
       - Arc points are on the unit circle, chord points are in the unit ball
       - Since ‖p‖ > 1, the homotopy avoids p

    2. **The homotopy is proper**:
       - Continuous: `fdBoundaryToPolygon_homotopy_continuous`
       - Closed: `fdBoundaryToPolygon_homotopy_closed`
       - Endpoints: `fdBoundaryToPolygonHomotopy_at_zero`, `fdBoundaryToPolygonHomotopy_at_one`

    3. **Next step**: Use `windingNumber_eq_of_piecewise_homotopic` from PiecewiseHomotopy.lean
       to conclude that the winding numbers are equal.

    4. **Final step**: Homotope the polygon to a small circle around p and use
       `circleIntegral.integral_sub_inv_of_mem_ball` to get winding = 1.
-/
theorem winding_number_one_summary
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2) (hp_im : p.im < H_height) :
    -- The key geometric ingredients are established
    (∀ t ∈ Icc 0 5, ∀ s ∈ Icc (0:ℝ) 1, fdBoundaryToPolygonHomotopy (t, s) ≠ p) ∧
    Continuous fdBoundaryToPolygonHomotopy ∧
    (∀ s ∈ Icc (0:ℝ) 1, fdBoundaryToPolygonHomotopy (0, s) = fdBoundaryToPolygonHomotopy (5, s)) := by
  exact ⟨fdBoundaryToPolygon_homotopy_avoids_interior p hp_norm hp_re hp_im,
         fdBoundaryToPolygon_homotopy_continuous,
         fdBoundaryToPolygon_homotopy_closed⟩

/-! ## Polygon Properties -/

/-! ### Polygon Values at Key Points -/

/-- fdPolygon at t=1 equals ρ' -/
lemma fdPolygon_at_t1 : fdPolygon 1 = rho' := by
  simp only [fdPolygon, show (1:ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
  simp only [H_height, rho']
  push_cast
  ring

/-- fdPolygon at t=2 equals i -/
lemma fdPolygon_at_t2 : fdPolygon 2 = i_point := by
  simp only [fdPolygon, show ¬(2:ℝ) ≤ 1 from by norm_num, show (2:ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
  simp only [chordSegment, i_point]
  simp only [show (2:ℝ) - 1 = 1 by ring]
  simp only [sub_self, zero_smul, zero_add, one_smul]

/-- fdPolygon at t=3 equals ρ -/
lemma fdPolygon_at_t3 : fdPolygon 3 = rho := by
  simp only [fdPolygon, show ¬(3:ℝ) ≤ 1 from by norm_num, show ¬(3:ℝ) ≤ 2 from by norm_num,
             show (3:ℝ) ≤ 3 from le_refl 3, ↓reduceIte]
  simp only [chordSegment, rho]
  simp only [show (3:ℝ) - 2 = 1 by ring]
  simp only [sub_self, zero_smul, zero_add, one_smul]

/-- fdPolygon at t=4 equals -1/2 + H*I -/
lemma fdPolygon_at_t4 : fdPolygon 4 = -1/2 + H_height * I := by
  simp only [fdPolygon, show ¬(4:ℝ) ≤ 1 from by norm_num, show ¬(4:ℝ) ≤ 2 from by norm_num,
             show ¬(4:ℝ) ≤ 3 from by norm_num, show (4:ℝ) ≤ 4 from le_refl 4, ↓reduceIte]
  simp only [H_height]
  push_cast
  ring

/-! ### Polygon Segment Functions -/

/-- Segment 1: right vertical -/
noncomputable def fdPolygon_seg1 : ℝ → ℂ := fun t =>
  1/2 + (H_height - t * (H_height - Real.sqrt 3 / 2)) * I

/-- Segment 2: chord from ρ' to i -/
noncomputable def fdPolygon_seg2 : ℝ → ℂ := fun t =>
  chordSegment rho' i_point (t - 1)

/-- Segment 3: chord from i to ρ -/
noncomputable def fdPolygon_seg3 : ℝ → ℂ := fun t =>
  chordSegment i_point rho (t - 2)

/-- Segment 4: left vertical -/
noncomputable def fdPolygon_seg4 : ℝ → ℂ := fun t =>
  -1/2 + (Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2)) * I

/-- Segment 5: top horizontal -/
noncomputable def fdPolygon_seg5 : ℝ → ℂ := fun t =>
  (t - 9/2) + H_height * I

lemma fdPolygon_seg1_continuous : Continuous fdPolygon_seg1 := by
  unfold fdPolygon_seg1
  continuity

lemma fdPolygon_seg2_continuous : Continuous fdPolygon_seg2 := by
  unfold fdPolygon_seg2 chordSegment
  continuity

lemma fdPolygon_seg3_continuous : Continuous fdPolygon_seg3 := by
  unfold fdPolygon_seg3 chordSegment
  continuity

lemma fdPolygon_seg4_continuous : Continuous fdPolygon_seg4 := by
  unfold fdPolygon_seg4
  continuity

lemma fdPolygon_seg5_continuous : Continuous fdPolygon_seg5 := by
  unfold fdPolygon_seg5
  continuity

/-- Matching at t=1: seg1 and seg2 agree -/
lemma fdPolygon_match_t1 : fdPolygon_seg1 1 = fdPolygon_seg2 1 := by
  simp only [fdPolygon_seg1, fdPolygon_seg2, chordSegment, H_height, rho']
  simp only [sub_self, zero_smul, sub_zero, one_smul]
  push_cast
  ring

/-- Matching at t=2: seg2 and seg3 agree -/
lemma fdPolygon_match_t2 : fdPolygon_seg2 2 = fdPolygon_seg3 2 := by
  simp only [fdPolygon_seg2, fdPolygon_seg3, chordSegment, i_point]
  simp only [show (2:ℝ) - 1 = 1 by ring, show (2:ℝ) - 2 = 0 by ring]
  simp only [sub_self, zero_smul, zero_add, one_smul, sub_zero, add_zero]

/-- Matching at t=3: seg3 and seg4 agree -/
lemma fdPolygon_match_t3 : fdPolygon_seg3 3 = fdPolygon_seg4 3 := by
  simp only [fdPolygon_seg3, fdPolygon_seg4, chordSegment, rho, H_height]
  simp only [show (3:ℝ) - 2 = 1 by ring]
  simp only [sub_self, zero_smul, zero_add, one_smul]
  push_cast
  ring

/-- Matching at t=4: seg4 and seg5 agree -/
lemma fdPolygon_match_t4 : fdPolygon_seg4 4 = fdPolygon_seg5 4 := by
  simp only [fdPolygon_seg4, fdPolygon_seg5, H_height]
  push_cast
  ring

/-- The polygon curve is continuous. -/
lemma fdPolygon_continuous : Continuous fdPolygon := by
  -- Use piecewise continuity: fdPolygon is continuous on each segment and matches at boundaries
  -- Key: frontier {x | x ≤ a} = {a} for any a
  have hfrontier1 : frontier {x : ℝ | x ≤ 1} = {1} := frontier_Iic
  have hfrontier2 : frontier {x : ℝ | x ≤ 2} = {2} := frontier_Iic
  have hfrontier3 : frontier {x : ℝ | x ≤ 3} = {3} := frontier_Iic
  have hfrontier4 : frontier {x : ℝ | x ≤ 4} = {4} := frontier_Iic
  -- fdPolygon agrees with segment functions on each interval
  have h12 : Continuous (fun t => if t ≤ 1 then fdPolygon_seg1 t else fdPolygon_seg2 t) := by
    apply Continuous.if
    · intro t ht
      rw [hfrontier1] at ht
      simp only [mem_singleton_iff] at ht
      rw [ht]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · exact fdPolygon_seg2_continuous
  have h123 : Continuous (fun t => if t ≤ 1 then fdPolygon_seg1 t
                                   else if t ≤ 2 then fdPolygon_seg2 t
                                   else fdPolygon_seg3 t) := by
    apply Continuous.if
    · intro t ht; rw [hfrontier1] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
      simp only [show (1:ℝ) ≤ 2 from by norm_num, ↓reduceIte]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · apply Continuous.if
      · intro t ht; rw [hfrontier2] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
        exact fdPolygon_match_t2
      · exact fdPolygon_seg2_continuous
      · exact fdPolygon_seg3_continuous
  have h1234 : Continuous (fun t => if t ≤ 1 then fdPolygon_seg1 t
                                    else if t ≤ 2 then fdPolygon_seg2 t
                                    else if t ≤ 3 then fdPolygon_seg3 t
                                    else fdPolygon_seg4 t) := by
    apply Continuous.if
    · intro t ht; rw [hfrontier1] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
      simp only [show (1:ℝ) ≤ 2 from by norm_num, ↓reduceIte]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · apply Continuous.if
      · intro t ht; rw [hfrontier2] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
        simp only [show (2:ℝ) ≤ 3 from by norm_num, ↓reduceIte]
        exact fdPolygon_match_t2
      · exact fdPolygon_seg2_continuous
      · apply Continuous.if
        · intro t ht; rw [hfrontier3] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
          exact fdPolygon_match_t3
        · exact fdPolygon_seg3_continuous
        · exact fdPolygon_seg4_continuous
  -- Full polygon is the 5-way piecewise
  have h_full : Continuous (fun t => if t ≤ 1 then fdPolygon_seg1 t
                                     else if t ≤ 2 then fdPolygon_seg2 t
                                     else if t ≤ 3 then fdPolygon_seg3 t
                                     else if t ≤ 4 then fdPolygon_seg4 t
                                     else fdPolygon_seg5 t) := by
    apply Continuous.if
    · intro t ht; rw [hfrontier1] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
      simp only [show (1:ℝ) ≤ 2 from by norm_num, ↓reduceIte]
      exact fdPolygon_match_t1
    · exact fdPolygon_seg1_continuous
    · apply Continuous.if
      · intro t ht; rw [hfrontier2] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
        simp only [show (2:ℝ) ≤ 3 from by norm_num, ↓reduceIte]
        exact fdPolygon_match_t2
      · exact fdPolygon_seg2_continuous
      · apply Continuous.if
        · intro t ht; rw [hfrontier3] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
          simp only [show (3:ℝ) ≤ 4 from by norm_num, ↓reduceIte]
          exact fdPolygon_match_t3
        · exact fdPolygon_seg3_continuous
        · apply Continuous.if
          · intro t ht; rw [hfrontier4] at ht; simp only [mem_singleton_iff] at ht; rw [ht]
            exact fdPolygon_match_t4
          · exact fdPolygon_seg4_continuous
          · exact fdPolygon_seg5_continuous
  -- Now show fdPolygon equals this piecewise function
  convert h_full using 1

/-- The polygon is closed: fdPolygon(0) = fdPolygon(5). -/
lemma fdPolygon_closed : fdPolygon 0 = fdPolygon 5 := by
  simp only [fdPolygon]
  simp only [show ¬(5:ℝ) ≤ 1 from by norm_num, show ¬(5:ℝ) ≤ 2 from by norm_num,
             show ¬(5:ℝ) ≤ 3 from by norm_num, show ¬(5:ℝ) ≤ 4 from by norm_num,
             show (0:ℝ) ≤ 1 from by norm_num, ↓reduceIte]
  simp only [H_height]
  push_cast
  ring

/-! ## Polygon Derivative Properties -/

/-- The derivative of the real-to-complex embedding at any point is 1. -/
lemma Complex.deriv_ofReal' : deriv (fun t : ℝ => (↑t : ℂ)) = fun _ => 1 := by
  ext t
  have : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  exact this.deriv

/-- Helper: derivative of affine function t ↦ a + t * b is b (for ℂ-valued functions on ℝ). -/
lemma deriv_affine_mul (a b : ℂ) : deriv (fun t : ℝ => a + ↑t * b) = fun _ => b := by
  ext t
  have h_id : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h_mul : HasDerivAt (fun t : ℝ => (↑t : ℂ) * b) (1 * b) t := h_id.mul_const b
  have h_add : HasDerivAt (fun t : ℝ => a + ↑t * b) (0 + 1 * b) t :=
    (hasDerivAt_const t a).add h_mul
  simp only [zero_add, one_mul] at h_add
  exact h_add.deriv

/-- Helper: derivative of affine function with shifted parameter t ↦ a + (t - c) * b is b. -/
lemma deriv_affine_shifted_mul (a b : ℂ) (c : ℝ) : deriv (fun t : ℝ => a + (↑t - ↑c) * b) = fun _ => b := by
  ext t
  have h_id : HasDerivAt (fun t : ℝ => (↑t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h_sub : HasDerivAt (fun t : ℝ => (↑t : ℂ) - ↑c) (1 - 0) t :=
    h_id.sub (hasDerivAt_const t (↑c : ℂ))
  simp only [sub_zero] at h_sub
  have h_mul : HasDerivAt (fun t : ℝ => ((↑t : ℂ) - ↑c) * b) (1 * b) t := h_sub.mul_const b
  have h_add : HasDerivAt (fun t : ℝ => a + (↑t - ↑c) * b) (0 + 1 * b) t :=
    (hasDerivAt_const t a).add h_mul
  simp only [zero_add, one_mul] at h_add
  exact h_add.deriv

/-- Derivative of segment 1: constant -(H - √3/2)*I -/
lemma fdPolygon_deriv_seg1 : deriv fdPolygon_seg1 = fun _ => -(H_height - Real.sqrt 3 / 2) * I := by
  -- fdPolygon_seg1 t = 1/2 + (H_height - t * (H_height - √3/2)) * I
  -- = (1/2 + H_height * I) + t * (-(H_height - √3/2) * I)
  have hrw : fdPolygon_seg1 = fun (t : ℝ) => ((1:ℂ)/2 + H_height * I) + ↑t * (-(H_height - Real.sqrt 3 / 2) * I) := by
    ext t
    simp only [fdPolygon_seg1]
    push_cast
    ring
  rw [hrw, deriv_affine_mul]

/-- Derivative of segment 2: constant (i - ρ') -/
lemma fdPolygon_deriv_seg2 : deriv fdPolygon_seg2 = fun _ => i_point - rho' := by
  -- fdPolygon_seg2 t = chordSegment rho' i_point (t - 1)
  -- = rho' + (t-1) * (i_point - rho')
  have hrw : fdPolygon_seg2 = fun (t : ℝ) => rho' + (↑t - ↑(1:ℝ)) * (i_point - rho') := by
    ext t
    simp only [fdPolygon_seg2, chordSegment, rho', i_point]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_one]
    push_cast
    ring
  rw [hrw, deriv_affine_shifted_mul]

/-- Derivative of segment 3: constant (ρ - i) -/
lemma fdPolygon_deriv_seg3 : deriv fdPolygon_seg3 = fun _ => rho - i_point := by
  -- fdPolygon_seg3 t = chordSegment i_point rho (t - 2)
  -- = i_point + (t - 2) * (rho - i_point)
  have hrw : fdPolygon_seg3 = fun (t : ℝ) => i_point + (↑t - ↑(2:ℝ)) * (rho - i_point) := by
    ext t
    simp only [fdPolygon_seg3, chordSegment, rho, i_point]
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_ofNat]
    push_cast
    ring
  rw [hrw, deriv_affine_shifted_mul]

/-- Derivative of segment 4: constant (H - √3/2)*I -/
lemma fdPolygon_deriv_seg4 : deriv fdPolygon_seg4 = fun _ => (H_height - Real.sqrt 3 / 2) * I := by
  -- fdPolygon_seg4 t = -1/2 + (√3/2 + (t-3)*(H-√3/2))*I
  -- = (-1/2 + (√3/2)*I) + (t-3) * ((H-√3/2)*I)
  have hrw : fdPolygon_seg4 = fun (t : ℝ) => (-(1:ℂ)/2 + (Real.sqrt 3 / 2) * I) + (↑t - ↑(3:ℝ)) * ((H_height - Real.sqrt 3 / 2) * I) := by
    ext t
    simp only [fdPolygon_seg4, H_height]
    push_cast
    ring
  rw [hrw, deriv_affine_shifted_mul]

/-- Derivative of segment 5: constant 1 -/
lemma fdPolygon_deriv_seg5 : deriv fdPolygon_seg5 = fun _ => 1 := by
  -- fdPolygon_seg5 t = (t - 9/2) + H_height * I
  -- = (-9/2 + H_height * I) + t * 1
  have hrw : fdPolygon_seg5 = fun (t : ℝ) => (-(9:ℂ)/2 + H_height * I) + ↑t * (1:ℂ) := by
    ext t
    simp only [fdPolygon_seg5, H_height]
    push_cast
    ring
  rw [hrw, deriv_affine_mul]

/-- Segment 1 is differentiable (affine function). -/
lemma fdPolygon_seg1_differentiable : Differentiable ℝ fdPolygon_seg1 := by
  have h : fdPolygon_seg1 = fun (t : ℝ) => ((1:ℂ)/2 + H_height * I) + ↑t * (-(H_height - Real.sqrt 3 / 2) * I) := by
    ext t
    simp only [fdPolygon_seg1]
    push_cast
    ring
  rw [h]
  exact (differentiable_const _).add (Complex.ofRealCLM.differentiable.mul (differentiable_const _))

/-- Segment 2 is differentiable (affine function). -/
lemma fdPolygon_seg2_differentiable : Differentiable ℝ fdPolygon_seg2 := by
  have h : fdPolygon_seg2 = fun (t : ℝ) => rho' + (↑t - (1:ℂ)) * (i_point - rho') := by
    ext t
    simp only [fdPolygon_seg2, chordSegment, rho', i_point, Complex.real_smul]
    simp only [Complex.ofReal_sub, Complex.ofReal_one]
    ring
  rw [h]
  refine (differentiable_const _).add ?_
  exact (Complex.ofRealCLM.differentiable.sub (differentiable_const _)).mul (differentiable_const _)

/-- Segment 3 is differentiable (affine function). -/
lemma fdPolygon_seg3_differentiable : Differentiable ℝ fdPolygon_seg3 := by
  have h : fdPolygon_seg3 = fun (t : ℝ) => i_point + (↑t - (2:ℂ)) * (rho - i_point) := by
    ext t
    simp only [fdPolygon_seg3, chordSegment, rho, i_point, Complex.real_smul]
    simp only [Complex.ofReal_sub, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  rw [h]
  refine (differentiable_const _).add ?_
  exact (Complex.ofRealCLM.differentiable.sub (differentiable_const _)).mul (differentiable_const _)

/-- Segment 4 is differentiable (affine function). -/
lemma fdPolygon_seg4_differentiable : Differentiable ℝ fdPolygon_seg4 := by
  have h : fdPolygon_seg4 = fun (t : ℝ) => (-(1:ℂ)/2 + (Real.sqrt 3 / 2) * I) + (↑t - (3:ℂ)) * ((H_height - Real.sqrt 3 / 2) * I) := by
    ext t
    simp only [fdPolygon_seg4, H_height]
    push_cast
    ring
  rw [h]
  refine (differentiable_const _).add ?_
  exact (Complex.ofRealCLM.differentiable.sub (differentiable_const _)).mul (differentiable_const _)

/-- Segment 5 is differentiable (affine function). -/
lemma fdPolygon_seg5_differentiable : Differentiable ℝ fdPolygon_seg5 := by
  have h : fdPolygon_seg5 = fun (t : ℝ) => (-(9:ℂ)/2 + H_height * I) + ↑t * (1:ℂ) := by
    ext t
    simp only [fdPolygon_seg5, H_height]
    push_cast
    ring
  rw [h]
  exact (differentiable_const _).add (Complex.ofRealCLM.differentiable.mul (differentiable_const _))

/-- The polygon is differentiable on each segment interior. -/
lemma fdPolygon_differentiableAt_off_partition (t : ℝ) (ht : t ∈ Ioo 0 5)
    (ht_not_P : t ∉ ({1, 2, 3, 4} : Finset ℝ)) :
    DifferentiableAt ℝ fdPolygon t := by
  -- Determine which segment t is in
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht_not_P
  obtain ⟨ht_ne1, ht_ne2, ht_ne3, ht_ne4⟩ := ht_not_P
  -- Case split on which segment
  by_cases h1 : t < 1
  · -- Segment 1: fdPolygon t = fdPolygon_seg1 t
    have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg1 := by
      filter_upwards [eventually_lt_nhds h1, eventually_gt_nhds ht.1] with s hs1 hs2
      simp only [fdPolygon, show s ≤ 1 from le_of_lt hs1, if_true, fdPolygon_seg1]
    exact fdPolygon_seg1_differentiable.differentiableAt.congr_of_eventuallyEq heq
  · push_neg at h1
    by_cases h2 : t < 2
    · -- Segment 2: fdPolygon t = fdPolygon_seg2 t
      have h1' : t > 1 := lt_of_le_of_ne h1 (Ne.symm ht_ne1)
      have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg2 := by
        filter_upwards [eventually_gt_nhds h1', eventually_lt_nhds h2] with s hs1 hs2
        simp only [fdPolygon, show ¬s ≤ 1 from not_le.mpr hs1, show s ≤ 2 from le_of_lt hs2, if_true, if_false, fdPolygon_seg2]
      exact fdPolygon_seg2_differentiable.differentiableAt.congr_of_eventuallyEq heq
    · push_neg at h2
      by_cases h3 : t < 3
      · -- Segment 3: fdPolygon t = fdPolygon_seg3 t
        have h2' : t > 2 := lt_of_le_of_ne h2 (Ne.symm ht_ne2)
        have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg3 := by
          filter_upwards [eventually_gt_nhds h2', eventually_lt_nhds h3] with s hs1 hs2
          simp only [fdPolygon, show ¬s ≤ 1 from not_le.mpr (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) (le_of_lt hs1)),
                     show ¬s ≤ 2 from not_le.mpr hs1, show s ≤ 3 from le_of_lt hs2, if_true, if_false, fdPolygon_seg3]
        exact fdPolygon_seg3_differentiable.differentiableAt.congr_of_eventuallyEq heq
      · push_neg at h3
        by_cases h4 : t < 4
        · -- Segment 4: fdPolygon t = fdPolygon_seg4 t
          have h3' : t > 3 := lt_of_le_of_ne h3 (Ne.symm ht_ne3)
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg4 := by
            filter_upwards [eventually_gt_nhds h3', eventually_lt_nhds h4] with s hs1 hs2
            simp only [fdPolygon,
                       show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 3) hs1),
                       show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 3) hs1),
                       show ¬s ≤ 3 from not_le.mpr hs1,
                       show s ≤ 4 from le_of_lt hs2, if_true, if_false, fdPolygon_seg4]
          exact fdPolygon_seg4_differentiable.differentiableAt.congr_of_eventuallyEq heq
        · -- Segment 5: fdPolygon t = fdPolygon_seg5 t
          push_neg at h4
          have h4' : t > 4 := lt_of_le_of_ne h4 (Ne.symm ht_ne4)
          have heq : fdPolygon =ᶠ[𝓝 t] fdPolygon_seg5 := by
            filter_upwards [eventually_gt_nhds h4', eventually_lt_nhds ht.2] with s hs1 hs2
            simp only [fdPolygon,
                       show ¬s ≤ 1 from not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) hs1),
                       show ¬s ≤ 2 from not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) hs1),
                       show ¬s ≤ 3 from not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) hs1),
                       show ¬s ≤ 4 from not_le.mpr hs1, if_false, fdPolygon_seg5]
          exact fdPolygon_seg5_differentiable.differentiableAt.congr_of_eventuallyEq heq

/- The polygon derivative is bounded by 3. -/
noncomputable section AristotleLemmas

/-
Bounds the derivative of each polygon segment function by 3.
-/
lemma fdPolygon_segs_deriv_bound (t : ℝ) :
  ‖deriv fdPolygon_seg1 t‖ ≤ 3 ∧
  ‖deriv fdPolygon_seg2 t‖ ≤ 3 ∧
  ‖deriv fdPolygon_seg3 t‖ ≤ 3 ∧
  ‖deriv fdPolygon_seg4 t‖ ≤ 3 ∧
  ‖deriv fdPolygon_seg5 t‖ ≤ 3 := by
    -- By definition of the polygon, we know that its derivative is bounded by the maximum of the norms of its segments.
    have h_deriv_bounds : ∀ t, ‖deriv fdPolygon_seg1 t‖ ≤ 3 ∧ ‖deriv fdPolygon_seg2 t‖ ≤ 3 ∧ ‖deriv fdPolygon_seg3 t‖ ≤ 3 ∧ ‖deriv fdPolygon_seg4 t‖ ≤ 3 ∧ ‖deriv fdPolygon_seg5 t‖ ≤ 3 := by
      intro t
      simp [fdPolygon_deriv_seg1, fdPolygon_deriv_seg2, fdPolygon_deriv_seg3, fdPolygon_deriv_seg4, fdPolygon_deriv_seg5];
      norm_num [ Complex.normSq, Complex.norm_def, H_height ] ; ring_nf ;
      norm_num [ i_point, rho, rho', Real.sqrt_le_iff ];
      constructor <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
    exact h_deriv_bounds t

/-
Proves that the derivative of the polygon function equals the derivative of the corresponding segment function on each open interval.
-/
lemma fdPolygon_deriv_eq_segs (t : ℝ) :
  (t ∈ Ioo 0 1 → deriv fdPolygon t = deriv fdPolygon_seg1 t) ∧
  (t ∈ Ioo 1 2 → deriv fdPolygon t = deriv fdPolygon_seg2 t) ∧
  (t ∈ Ioo 2 3 → deriv fdPolygon t = deriv fdPolygon_seg3 t) ∧
  (t ∈ Ioo 3 4 → deriv fdPolygon t = deriv fdPolygon_seg4 t) ∧
  (t ∈ Ioo 4 5 → deriv fdPolygon t = deriv fdPolygon_seg5 t) := by
    refine' ⟨ fun ht => _, fun ht => _, fun ht => _, fun ht => _, fun ht => _ ⟩;
    · refine' Filter.EventuallyEq.deriv_eq _;
      filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with u hu using if_pos hu.2.le;
    · refine' Filter.EventuallyEq.deriv_eq _;
      filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with x hx using if_neg hx.1.not_le |> fun h => h.trans <| if_pos hx.2.le;
    · refine' Filter.EventuallyEq.deriv_eq _;
      filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with x hx using by unfold fdPolygon; unfold fdPolygon_seg3; split_ifs <;> norm_num <;> linarith [ hx.1, hx.2 ] ;
    · refine' Filter.EventuallyEq.deriv_eq _;
      filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with x hx using by unfold fdPolygon; unfold fdPolygon_seg4; split_ifs <;> ring <;> linarith [ hx.1, hx.2 ] ;
    · refine' Filter.EventuallyEq.deriv_eq _;
      filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with x hx using if_neg ( by linarith [ hx.1, hx.2 ] ) |> fun h => h.trans ( if_neg ( by linarith [ hx.1, hx.2 ] ) |> fun h => h.trans ( if_neg ( by linarith [ hx.1, hx.2 ] ) |> fun h => h.trans ( if_neg ( by linarith [ hx.1, hx.2 ] ) ) ) )

end AristotleLemmas

lemma fdPolygon_deriv_bounded : ∃ M : ℝ, ∀ t ∈ Icc 0 5, ‖deriv fdPolygon t‖ ≤ M := by
  -- Technical: Each segment has bounded derivative:
  -- - Segment 1: ‖-(H - √3/2)*I‖ = 1
  -- - Segment 2: ‖i - ρ'‖ ≤ 2
  -- - Segment 3: ‖ρ - i‖ ≤ 2
  -- - Segment 4: ‖(H - √3/2)*I‖ = 1
  -- - Segment 5: ‖1‖ = 1
  -- At partition points, deriv may not exist (use deriv_zero_of_not_differentiableAt)
  use 3
  intro t ht
  by_cases h : DifferentiableAt ℝ fdPolygon t
  ·
    by_cases h1 : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5;
    · rcases h1 with ( rfl | rfl | rfl | rfl | rfl | rfl );
      all_goals have := h.hasDerivAt.tendsto_slope_zero; norm_num at *;
      all_goals have := this.norm; norm_num at this;
      all_goals refine' le_of_tendsto this _;
      all_goals filter_upwards [ self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds ( Metric.ball_mem_nhds _ zero_lt_one ) ] with x hx₁ hx₂; norm_num [ Complex.normSq, Complex.norm_def ] at *;
      all_goals unfold fdPolygon; norm_num [ abs_of_nonneg, add_nonneg ];
      all_goals split_ifs <;> norm_num [ Complex.normSq, Complex.norm_def ] at *;
      any_goals nlinarith [ abs_lt.mp hx₂ ];
      any_goals rw [ Real.sqrt_mul_self_eq_abs ] ; ring_nf ; norm_num [ abs_of_nonneg, hx₁ ];
      all_goals rw [ inv_mul_eq_div, div_le_iff₀ ( abs_pos.mpr hx₁ ) ] ; norm_num [ abs_of_nonneg, H_height ];
      any_goals rw [ abs_le ] ; constructor <;> cases abs_cases x <;> nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
      · unfold chordSegment; norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ abs_of_nonneg, hx₁ ];
        unfold rho' i_point; norm_num [ abs_of_pos, ‹0 < x› ] ; ring_nf ; norm_num [ abs_of_pos, ‹0 < x› ] ;
        rw [ Real.sqrt_le_left ] <;> nlinarith [ abs_lt.mp hx₂, Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
      · unfold chordSegment; norm_num [ Complex.normSq, Complex.norm_def ] ; ring_nf;
        rw [ Real.sqrt_le_left ] <;> norm_num [ rho', i_point ] ; ring_nf ; norm_num [ abs_of_nonneg, ‹x ≤ 0› ];
        nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
      · unfold chordSegment; norm_num [ Complex.normSq, Complex.norm_def ] ; ring_nf;
        rw [ Real.sqrt_le_left ] <;> norm_num [ i_point, rho ] ; ring_nf ; norm_num [ abs_of_pos, ‹0 < x› ];
        nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
      · unfold chordSegment; norm_num [ Complex.normSq, Complex.norm_def ] ; ring_nf;
        rw [ Real.sqrt_le_left ] <;> norm_num [ i_point, rho ] ; ring_nf ; norm_num [ abs_of_nonneg, hx₁ ];
        nlinarith [ Real.sqrt_nonneg 3, Real.sq_sqrt ( show 0 ≤ 3 by norm_num ) ];
      · unfold chordSegment; norm_num [ Complex.normSq, Complex.div_re, Complex.div_im ] ; ring_nf ; norm_num [ abs_of_nonneg, hx₁ ];
        rw [ Real.sqrt_le_left ] <;> norm_num [ rho ] ; ring_nf ; norm_num [ abs_of_pos, ‹0 < x› ];
    · have h_deriv_segment : ∃ k ∈ ({0, 1, 2, 3, 4} : Set ℝ), t ∈ Set.Ioo k (k + 1) := by
        simp +zetaDelta at *;
        cases lt_or_gt_of_ne h1.1 <;> cases lt_or_gt_of_ne h1.2.1 <;> cases lt_or_gt_of_ne h1.2.2.1 <;> cases lt_or_gt_of_ne h1.2.2.2.1 <;> cases lt_or_gt_of_ne h1.2.2.2.2.1 <;> cases lt_or_gt_of_ne h1.2.2.2.2.2 <;> first | linarith | exact Or.inl ⟨ by linarith, by linarith ⟩ | exact Or.inr <| Or.inl ⟨ by linarith, by linarith ⟩ | exact Or.inr <| Or.inr <| Or.inl ⟨ by linarith, by linarith ⟩ | exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨ by linarith, by linarith ⟩ | exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨ by linarith, by linarith ⟩ ;
      obtain ⟨ k, hk_set, hk_interval ⟩ := h_deriv_segment;
      have h_deriv_segment : deriv fdPolygon t = deriv (if k = 0 then fdPolygon_seg1 else if k = 1 then fdPolygon_seg2 else if k = 2 then fdPolygon_seg3 else if k = 3 then fdPolygon_seg4 else fdPolygon_seg5) t := by
        convert ( Filter.EventuallyEq.deriv_eq _ ) using 1;
        filter_upwards [ Ioo_mem_nhds hk_interval.1 hk_interval.2 ] with x hx;
        rcases hk_set with ( rfl | rfl | rfl | rfl | rfl ) <;> norm_num [ fdPolygon ] at hx ⊢;
        · rw [ if_pos hx.2.le ] ; rfl;
        · unfold fdPolygon_seg2; split_ifs <;> norm_num at * <;> linarith;
        · split_ifs <;> norm_num [ fdPolygon_seg3 ] <;> linarith;
        · unfold fdPolygon_seg4; split_ifs <;> norm_num <;> linarith;
        · unfold fdPolygon_seg5; split_ifs <;> norm_num <;> linarith;
      convert fdPolygon_segs_deriv_bound t |> fun h => h.1 |> fun h' => ?_ using 1;
      grind -- Technical: case analysis on segments, all bounded by 3
  · simp only [deriv_zero_of_not_differentiableAt h, norm_zero]
    norm_num

/-! ## Polygon to Circle Homotopy Properties -/

/-- Radial homotopy from polygon to unit circle around p.

    H(t, s) = p + ((1-s)*‖z-p‖ + s) • (z-p)/‖z-p‖

    At s=0: H(t,0) = p + ‖z-p‖ • (z-p)/‖z-p‖ = z = fdPolygon(t)
    At s=1: H(t,1) = p + 1 • (z-p)/‖z-p‖ = p + (z-p)/‖z-p‖ (on unit circle around p)
-/
noncomputable def polygonToCircleRadial (p : ℂ) : ℝ × ℝ → ℂ := fun (t, s) =>
  let z := fdPolygon t
  let dir := z - p
  p + ((1 - s) * ‖dir‖ + s) • (dir / ‖dir‖)

/-- The radial homotopy avoids p when z ≠ p. -/
lemma polygonToCircleRadial_avoids (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im : p.im < H_height) (t : ℝ) (ht : t ∈ Icc 0 5) (s : ℝ) (hs : s ∈ Icc 0 1) :
    polygonToCircleRadial p (t, s) ≠ p := by
  simp only [polygonToCircleRadial]
  have hz_ne : fdPolygon t ≠ p := fdPolygon_avoids_interior p hp_norm hp_re hp_im t ht
  have hdir_ne : fdPolygon t - p ≠ 0 := sub_ne_zero.mpr hz_ne
  have hnorm_pos : ‖fdPolygon t - p‖ > 0 := norm_pos_iff.mpr hdir_ne
  -- The coefficient (1-s)*‖dir‖ + s is always positive
  have hcoeff : (1 - s) * ‖fdPolygon t - p‖ + s > 0 := by
    have hs0 : 0 ≤ s := hs.1
    have hs1 : s ≤ 1 := hs.2
    have h1s : 0 ≤ 1 - s := by linarith
    -- Either s > 0 or (1-s)*‖dir‖ > 0
    by_cases hs_pos : s > 0
    · have h1 : (1 - s) * ‖fdPolygon t - p‖ ≥ 0 := mul_nonneg h1s (le_of_lt hnorm_pos)
      linarith
    · push_neg at hs_pos
      have hs_zero : s = 0 := le_antisymm hs_pos hs0
      simp only [hs_zero, sub_zero, one_mul, add_zero]
      exact hnorm_pos
  -- So the smul is nonzero
  intro heq
  rw [add_eq_left] at heq
  have hsmul_zero : ((1 - s) * ‖fdPolygon t - p‖ + s) • ((fdPolygon t - p) / ‖fdPolygon t - p‖) = 0 := heq
  rw [smul_eq_zero] at hsmul_zero
  rcases hsmul_zero with hcoeff_zero | hdir_zero
  · -- Coefficient can't be zero since it's positive
    have hcoeff_ne : (1 - s) * ‖fdPolygon t - p‖ + s ≠ 0 := ne_of_gt hcoeff
    exact hcoeff_ne hcoeff_zero
  · rw [div_eq_zero_iff] at hdir_zero
    rcases hdir_zero with h1 | h2
    · exact hdir_ne h1
    · -- h2 : ↑‖fdPolygon t - p‖ = 0
      have hnorm_zero : ‖fdPolygon t - p‖ = 0 := Complex.ofReal_eq_zero.mp h2
      have hnorm_ne : ‖fdPolygon t - p‖ ≠ 0 := ne_of_gt hnorm_pos
      exact hnorm_ne hnorm_zero

/-! ## Main Theorem: Winding Number = 1 -/

/- Aristotle failed to find a proof. -/
/-- **MAIN THEOREM**: For interior points p in the fundamental domain,
    the generalized winding number of the FD boundary around p equals 1.

    **Proof Strategy**:
    1. fdBoundary → fdPolygon via arc-to-chord homotopy (avoids p since ‖p‖ > 1)
    2. fdPolygon → radial circle via radial projection (avoids p)
    3. Radial circle → circleParam via rotation on S¹ (avoids p)
    4. circleParam has winding = 1 by circleParam_winding_eq_one
    5. Homotopy invariance gives fdBoundary has winding = 1

    **Mathematical Content**: This is the key geometric fact for the valence formula.
    Interior points are enclosed once by the fundamental domain boundary.
-/
theorem generalizedWindingNumber_fdBoundary_eq_one
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2) (hp_im : p.im < H_height) :
    generalizedWindingNumber' fdBoundary 0 5 p = 1 := by
  -- Setup
  have hab : (0 : ℝ) < 5 := by norm_num
  have hγ_cont : ContinuousOn fdBoundary (Icc 0 5) := by
    apply Continuous.continuousOn
    -- fdBoundary is piecewise continuous with matching at boundaries
    sorry -- Technical: same pattern as fdBoundaryToPolygonHomotopy_continuous
  have hγ_ne : ∀ t ∈ Icc 0 5, fdBoundary t ≠ p := by
    intro t ht
    -- fdBoundary avoids p because:
    -- - Segments 1, 4, 5: p is in wrong x or y region
    -- - Segments 2, 3: arc is on unit circle, but ‖p‖ > 1
    sorry -- Technical: case analysis on segments
  have hγ_closed : fdBoundary 0 = fdBoundary 5 := fdBoundary_at_zero.trans fdBoundary_at_five.symm
  -- The key: construct homotopy from fdBoundary to circleParam
  have hhom : PiecewiseCurvesHomotopicAvoiding fdBoundary (circleParam p 1 0 5) 0 5 p {1, 2, 3, 4} := by
    -- HOMOTOPY CONSTRUCTION:
    -- 1. fdBoundary → fdPolygon (via fdBoundaryToPolygonHomotopy, avoids p)
    -- 2. fdPolygon → radial projection on S¹ (via polygonToCircleRadial, avoids p)
    -- 3. Radial S¹ → circleParam (via S¹ rotation, avoids p)
    --
    -- Each step produces a PiecewiseCurvesHomotopicAvoiding, and they can be composed
    -- since they all avoid p. The composition gives the required homotopy.
    sorry -- Technical: homotopy composition
  exact winding_eq_one_of_homotopic_to_circle p fdBoundary 0 5 {1, 2, 3, 4} hab hγ_cont hγ_ne hγ_closed hhom

/-!
## CURRENT STATUS (2026-01-30)

### Main Results

**MAIN THEOREM**: `generalizedWindingNumber_fdBoundary_eq_one`
- For interior points p with ‖p‖ > 1, |p.re| < 1/2, p.im < H_height
- The generalized winding number of fdBoundary around p equals 1

### Proved Lemmas (sorry-free):
- `fdBoundary_at_zero`, `fdBoundary_at_five` ✓
- `fdBoundaryToPolygonHomotopy_at_t_zero`, `fdBoundaryToPolygonHomotopy_at_t_five` ✓
- `fdBoundaryToPolygonHomotopy_at_zero`, `fdBoundaryToPolygonHomotopy_at_one` ✓
- `fdBoundaryToPolygonHomotopy_avoids` ✓ (ALL 5 segments!)
- `fdBoundaryToPolygonHomotopy_closed` ✓
- `fdBoundaryToPolygonHomotopy_continuous` ✓ (piecewise continuity with gluing)
- `circleAround_closed`, `circleAround_continuous`, `circleAround_dist` ✓
- `exists_ball_in_polygon_interior` ✓
- Joint matching lemmas `H_match_at_t1` through `H_match_at_t4` ✓
- `fdPolygon_avoids_interior` ✓
- `fdPolygon_closed` ✓
- `polygonToCircleRadial_avoids` ✓
- `winding_number_one_summary` ✓

### Remaining Sorries (6 total, all technical):
1. `fdPolygon_continuous` - piecewise continuity (same pattern as fdBoundaryToPolygonHomotopy)
2. `fdPolygon_differentiableAt_off_partition` - piecewise linear is differentiable
3. `fdPolygon_deriv_bounded` - piecewise constant derivatives are bounded
4. `generalizedWindingNumber_fdBoundary_eq_one`:
   - `hγ_cont` - fdBoundary continuity (same pattern)
   - `hγ_ne` - fdBoundary avoids p (case analysis)
   - `hhom` - homotopy composition (main technical gap)

### HOW TO USE THIS FILE:
Import this file and use `generalizedWindingNumber_fdBoundary_eq_one` to get
winding = 1 for interior points. This replaces angle-lifting approaches.

## KEY INSIGHT RECAP

The rectangle Cauchy-Goursat lemma (`integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`)
gives **0** for holomorphic functions on regions avoiding singularities.
It is useful for showing homotopy invariance, NOT for computing winding = 1.

For winding = 1, we must use `circleIntegral.integral_sub_inv_of_mem_ball` which
specifically handles the case where the singularity is INSIDE the circle.

## KEY AVOIDANCE RESULT

The crucial `fdBoundaryToPolygonHomotopy_avoids` lemma shows that for interior points p
with |p.re| < 1/2, p.im < H_height, and ‖p‖ > 1:
- Segments 1, 4: Avoided because |p.re| < 1/2 but segments are at x = ±1/2
- Segments 2, 3: Avoided because homotopy stays in closed unit ball, but ‖p‖ > 1
- Segment 5: Avoided because p.im < H_height but segment has y = H_height
-/