/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ValenceFormula.Definitions

/-!
# Fundamental Domain Boundary

The 5-segment closed contour around the standard fundamental domain for SL₂(ℤ),
parameterized on `[0, 1]` with breakpoints at `1/5, 2/5, 3/5, 4/5`.

## Segments (clockwise)

* Seg 1: `[0, 1/5]` — right vertical from `1/2 + Hi` down to `ρ+1`
* Seg 2: `[1/5, 2/5]` — unit-circle arc from `ρ+1` to `i`
* Seg 3: `[2/5, 3/5]` — unit-circle arc from `i` to `ρ`
* Seg 4: `[3/5, 4/5]` — left vertical from `ρ` up to `-1/2 + Hi`
* Seg 5: `[4/5, 1]` — horizontal from `-1/2 + Hi` to `1/2 + Hi`

## Main definitions

* `fdStart H` — the starting/ending point `1/2 + Hi`
* `fdBoundaryFun H` — the boundary function `ℝ → ℂ`
* `FDWindingData H` — structure bundling winding weight data for the valence formula

## Main results

* `fdBoundaryFun_continuous` — continuity of the boundary
* `fdBoundaryFun_closed` — the contour is closed
* `fdBoundaryFun_at_*` — values at the five junction points
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ### Starting point -/

/-- The starting (and ending) point of the FD boundary contour. -/
def fdStart (H : ℝ) : ℂ := 1 / 2 + ↑H * I

/-! ### The 5-segment boundary function -/

/-- Boundary of the standard fundamental domain for SL₂(ℤ) at height `H`,
parameterized on `[0, 1]` with breakpoints at `1/5, 2/5, 3/5, 4/5`.

The contour is clockwise: right-vertical, arc, arc, left-vertical, horizontal. -/
def fdBoundaryFun (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1/5 then
    -- Seg 1: right vertical from (1/2 + Hi) down to ρ+1
    1/2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else if t ≤ 2/5 then
    -- Seg 2: unit-circle arc from ρ+1 to i (angle π/3 → π/2)
    exp ((↑Real.pi / 3 + (5 * ↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)
  else if t ≤ 3/5 then
    -- Seg 3: unit-circle arc from i to ρ (angle π/2 → 2π/3)
    exp ((↑Real.pi / 2 + (5 * ↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
  else if t ≤ 4/5 then
    -- Seg 4: left vertical from ρ up to (-1/2 + Hi)
    -1/2 + (↑(Real.sqrt 3) / 2 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else
    -- Seg 5: horizontal from (-1/2 + Hi) to (1/2 + Hi)
    (5 * ↑t - 9/2) + ↑H * I

/-! ### Junction values -/

theorem fdBoundaryFun_at_zero (H : ℝ) :
    fdBoundaryFun H 0 = fdStart H := by
  simp only [fdBoundaryFun, fdStart, show (0 : ℝ) ≤ 1/5 from by norm_num, ite_true]
  push_cast; ring

theorem fdBoundaryFun_at_one_fifth (H : ℝ) :
    fdBoundaryFun H (1/5) = ellipticPointRhoPlusOne := by
  simp only [fdBoundaryFun, show (1/5 : ℝ) ≤ 1/5 from le_refl _, ite_true,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast; ring

theorem fdBoundaryFun_at_two_fifths (H : ℝ) :
    fdBoundaryFun H (2/5) = ellipticPointI := by
  simp only [fdBoundaryFun, show ¬(2/5 : ℝ) ≤ 1/5 from by norm_num,
    show (2/5 : ℝ) ≤ 2/5 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 3 + (5 * (↑(2/5 : ℝ)) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp only [ellipticPointI, ellipticPointI']; norm_num

theorem fdBoundaryFun_at_three_fifths (H : ℝ) :
    fdBoundaryFun H (3/5) = ellipticPointRho := by
  simp only [fdBoundaryFun, show ¬(3/5 : ℝ) ≤ 1/5 from by norm_num,
    show ¬(3/5 : ℝ) ≤ 2/5 from by norm_num,
    show (3/5 : ℝ) ≤ 3/5 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 2 + (5 * (↑(3/5 : ℝ)) - 2) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]; norm_num

theorem fdBoundaryFun_at_four_fifths (H : ℝ) :
    fdBoundaryFun H (4/5) = -1/2 + ↑H * I := by
  simp only [fdBoundaryFun, show ¬(4/5 : ℝ) ≤ 1/5 from by norm_num,
    show ¬(4/5 : ℝ) ≤ 2/5 from by norm_num,
    show ¬(4/5 : ℝ) ≤ 3/5 from by norm_num,
    show (4/5 : ℝ) ≤ 4/5 from le_refl _, ite_true, ite_false]
  push_cast; ring

theorem fdBoundaryFun_at_one (H : ℝ) :
    fdBoundaryFun H 1 = fdStart H := by
  simp only [fdBoundaryFun, show ¬(1 : ℝ) ≤ 1/5 from by norm_num,
    show ¬(1 : ℝ) ≤ 2/5 from by norm_num,
    show ¬(1 : ℝ) ≤ 3/5 from by norm_num,
    show ¬(1 : ℝ) ≤ 4/5 from by norm_num, ite_false, fdStart]
  push_cast; ring

/-- The FD boundary contour is closed. -/
theorem fdBoundaryFun_closed (H : ℝ) :
    fdBoundaryFun H 0 = fdBoundaryFun H 1 := by
  rw [fdBoundaryFun_at_zero, fdBoundaryFun_at_one]

/-! ### Continuity -/

/-- Continuity of segment 1: right vertical. -/
private lemma fdBoundaryFun_seg1_cont (H : ℝ) :
    Continuous (fun t : ℝ => (1 : ℂ) / 2 +
      (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I) :=
  continuous_const.add
    ((continuous_const.sub
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).mul
      continuous_const)

/-- Continuity of segment 2: unit-circle arc ρ+1 to i. -/
private lemma fdBoundaryFun_seg2_cont :
    Continuous (fun t : ℝ => exp
      ((↑Real.pi / 3 + (5 * ↑t - 1) *
        (↑Real.pi / 2 - ↑Real.pi / 3)) * I)) :=
  Complex.continuous_exp.comp
    ((continuous_const.add
      (((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).mul
        continuous_const)).mul continuous_const)

/-- Continuity of segment 3: unit-circle arc i to ρ. -/
private lemma fdBoundaryFun_seg3_cont :
    Continuous (fun t : ℝ => exp
      ((↑Real.pi / 2 + (5 * ↑t - 2) *
        (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)) :=
  Complex.continuous_exp.comp
    ((continuous_const.add
      (((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).mul
        continuous_const)).mul continuous_const)

/-- Continuity of segment 4: left vertical. -/
private lemma fdBoundaryFun_seg4_cont (H : ℝ) :
    Continuous (fun t : ℝ =>
      (-1 : ℂ) / 2 + (↑(Real.sqrt 3) / 2 +
        (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I) :=
  continuous_const.add
    ((continuous_const.add
      (((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).mul
        continuous_const)).mul continuous_const)

/-- Continuity of segment 5: horizontal. -/
private lemma fdBoundaryFun_seg5_cont (H : ℝ) :
    Continuous (fun t : ℝ => (5 * ↑t - 9 / 2 : ℂ) + ↑H * I) :=
  ((continuous_const.mul Complex.continuous_ofReal).sub continuous_const).add continuous_const

/-- Inner layering for continuity proof: segments 4-5. -/
private def fdBoundaryFun_inner45 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 4/5 then
    -1/2 + (↑(Real.sqrt 3) / 2 + (5 * ↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else (5 * ↑t - 9/2) + ↑H * I

private lemma fdBoundaryFun_inner45_cont (H : ℝ) :
    Continuous (fdBoundaryFun_inner45 H) :=
  Continuous.if_le (fdBoundaryFun_seg4_cont H) (fdBoundaryFun_seg5_cont H)
    continuous_id continuous_const (fun t (ht : t = 4/5) => by
      subst ht; push_cast; ring)

/-- Inner layering: segments 3-4-5. -/
private def fdBoundaryFun_inner345 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 3/5 then
    exp ((↑Real.pi / 2 + (5 * ↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
  else fdBoundaryFun_inner45 H t

private lemma fdBoundaryFun_inner345_cont (H : ℝ) :
    Continuous (fdBoundaryFun_inner345 H) := by
  apply Continuous.if_le fdBoundaryFun_seg3_cont
    (fdBoundaryFun_inner45_cont H) continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 3/5 := by linarith
  subst this; unfold fdBoundaryFun_inner45
  simp only [show (3/5 : ℝ) ≤ 4/5 from by norm_num, ite_true]
  have h : (↑Real.pi / 2 + (5 * (↑(3/5 : ℝ)) - 2) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast; ring

/-- Inner layering: segments 2-3-4-5. -/
private def fdBoundaryFun_inner2345 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 2/5 then
    exp ((↑Real.pi / 3 + (5 * ↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)
  else fdBoundaryFun_inner345 H t

private lemma fdBoundaryFun_inner2345_cont (H : ℝ) :
    Continuous (fdBoundaryFun_inner2345 H) := by
  apply Continuous.if_le fdBoundaryFun_seg2_cont
    (fdBoundaryFun_inner345_cont H) continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 2/5 := by linarith
  subst this; unfold fdBoundaryFun_inner345
  simp only [show (2/5 : ℝ) ≤ 3/5 from by norm_num, ite_true]
  have h1 : (↑Real.pi / 3 + (5 * (↑(2/5 : ℝ)) - 1) *
      (↑Real.pi / 2 - ↑Real.pi / 3)) * I = ↑(Real.pi / 2) * I := by
    push_cast; ring
  have h2 : (↑Real.pi / 2 + (5 * (↑(2/5 : ℝ)) - 2) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I = ↑(Real.pi / 2) * I := by
    push_cast; ring
  rw [h1, h2]

private lemma fdBoundaryFun_eq_layered (H : ℝ) (t : ℝ) :
    fdBoundaryFun H t =
      (if t ≤ 1/5 then
        1/2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
       else fdBoundaryFun_inner2345 H t) := by
  unfold fdBoundaryFun fdBoundaryFun_inner2345 fdBoundaryFun_inner345
    fdBoundaryFun_inner45
  split_ifs <;> rfl

/-- The FD boundary is continuous as a function `ℝ → ℂ`. -/
theorem fdBoundaryFun_continuous (H : ℝ) :
    Continuous (fdBoundaryFun H) := by
  have : (fdBoundaryFun H) = (fun t => if t ≤ 1/5 then
      1/2 + (↑H - 5 * ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
      else fdBoundaryFun_inner2345 H t) := by
    ext t; exact fdBoundaryFun_eq_layered H t
  rw [this]
  apply Continuous.if_le (fdBoundaryFun_seg1_cont H) (fdBoundaryFun_inner2345_cont H)
    continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 1/5 := by linarith
  subst this; unfold fdBoundaryFun_inner2345
  simp only [show (1/5 : ℝ) ≤ 2/5 from by norm_num, ite_true]
  have h : (↑Real.pi / 3 + (5 * (↑(1/5 : ℝ)) - 1) *
      (↑Real.pi / 2 - ↑Real.pi / 3)) * I = ↑(Real.pi / 3) * I := by
    push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

/-! ### Path construction -/

/-- The FD boundary as a `Path` from `fdStart H` to `fdStart H`. -/
def fdBoundaryPath (H : ℝ) : Path (fdStart H) (fdStart H) where
  toFun := fun t => fdBoundaryFun H t
  continuous_toFun := (fdBoundaryFun_continuous H).continuousOn.restrict
  source' := by show fdBoundaryFun H 0 = _; exact fdBoundaryFun_at_zero H
  target' := by show fdBoundaryFun H 1 = _; exact fdBoundaryFun_at_one H

/-! ### FD boundary partition -/

/-- The partition points (segment junctions) for the FD boundary on `[0, 1]`. -/
def fdBoundaryPartition : Finset ℝ := {1/5, 2/5, 3/5, 4/5}

theorem fdBoundaryPartition_subset_Ioo :
    (fdBoundaryPartition : Set ℝ) ⊆ Ioo 0 1 := by
  intro x hx
  simp only [fdBoundaryPartition, Finset.coe_insert, Finset.coe_singleton,
    mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with h | h | h | h <;> (subst h; constructor <;> norm_num)

/-! ### Winding weight specification structure -/

/-- Winding weight data for the valence formula at height `H`.

This structure bundles the FD boundary contour as a `PiecewiseC1Path` together
with the generalized winding number values at each relevant point. These are
the coefficients that appear in the valence formula:
- `-1` at strict interior points (full winding)
- `-1/2` at the edge point `i` (half winding, on-curve)
- `-1/6` at the elliptic points `ρ` and `ρ+1` (sixth winding, corner) -/
structure FDWindingData (H : ℝ) where
  /-- The FD boundary as a piecewise C1 closed path. -/
  boundary : PiecewiseC1Path (fdStart H) (fdStart H)
  /-- The boundary function agrees with `fdBoundaryFun` on `[0, 1]`. -/
  boundary_eq : ∀ t ∈ Icc (0 : ℝ) 1, boundary.toPath.extend t = fdBoundaryFun H t
  /-- Winding number = -1 for strict interior points of the fundamental domain. -/
  interior_winding : ∀ z : ℂ, ‖z‖ > 1 → |z.re| < 1/2 → z.im > 0 → z.im < H →
    HasGeneralizedWindingNumber boundary z (-1)
  /-- Winding number = -1/2 at `i` (on-curve, edge crossing). -/
  winding_at_i : HasGeneralizedWindingNumber boundary I (-1/2)
  /-- Winding number = -1/6 at `ρ` (on-curve, elliptic corner). -/
  winding_at_rho : HasGeneralizedWindingNumber boundary ellipticPointRho (-1/6)
  /-- Winding number = -1/6 at `ρ+1` (on-curve, elliptic corner). -/
  winding_at_rho_plus_one :
    HasGeneralizedWindingNumber boundary ellipticPointRhoPlusOne (-1/6)

/-! ### Geometric facts about the boundary -/

/-- The right vertical segment stays at `re = 1/2`. -/
theorem fdBoundaryFun_seg1_re (H : ℝ) (t : ℝ) (ht : t ≤ 1/5) :
    (fdBoundaryFun H t).re = 1/2 := by
  simp only [fdBoundaryFun, ht, ite_true]
  simp [add_re, sub_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_ofNat]

/-- The left vertical segment stays at `re = -1/2`. -/
theorem fdBoundaryFun_seg4_re (H : ℝ) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t ≤ 4/5) :
    (fdBoundaryFun H t).re = -1/2 := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    ht4, ite_true, ite_false]
  simp [add_re, sub_re, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    neg_re, div_ofNat]

/-- The horizontal segment stays at `im = H`. -/
theorem fdBoundaryFun_seg5_im (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    (fdBoundaryFun H t).im = H := by
  simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
    show ¬t ≤ 2/5 from by linarith, show ¬t ≤ 3/5 from by linarith,
    show ¬t ≤ 4/5 from by linarith, ite_false]
  simp [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_ofNat]

/-- Arc segments (2 and 3) lie on the unit circle. -/
theorem fdBoundaryFun_arc_norm (H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t ≤ 3/5) :
    ‖fdBoundaryFun H t‖ = 1 := by
  by_cases ht : t ≤ 2/5
  · -- Seg 2
    simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith, ht, ite_true, ite_false]
    have h : (↑Real.pi / 3 + (5 * ↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
        ↑(Real.pi / 3 + (5 * t - 1) * (Real.pi / 2 - Real.pi / 3)) * I := by
      push_cast; ring
    rw [h]; exact Complex.norm_exp_ofReal_mul_I _
  · -- Seg 3
    push_neg at ht
    simp only [fdBoundaryFun, show ¬t ≤ 1/5 from by linarith,
      show ¬t ≤ 2/5 from by linarith, ht2, ite_true, ite_false]
    have h : (↑Real.pi / 2 + (5 * ↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
        ↑(Real.pi / 2 + (5 * t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I := by
      push_cast; ring
    rw [h]; exact Complex.norm_exp_ofReal_mul_I _

/-- The right vertical imaginary part interpolates linearly. -/
theorem fdBoundaryFun_seg1_im (H : ℝ) (t : ℝ) (ht : t ≤ 1/5) :
    (fdBoundaryFun H t).im = H - 5 * t * (H - Real.sqrt 3 / 2) := by
  simp only [fdBoundaryFun, ht, ite_true]
  simp [add_im, sub_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, div_ofNat]

/-- Height hypothesis: we need `H > √3/2` for the boundary to be well-formed. -/
def fdHeightValid (H : ℝ) : Prop := Real.sqrt 3 / 2 < H

theorem fdHeightValid_of_one_lt (H : ℝ) (hH : 1 < H) : fdHeightValid H := by
  unfold fdHeightValid
  have h1 : Real.sqrt 3 < 2 := by
    have : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    rwa [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (2 : ℝ) ≥ 0)] at this
  linarith

/-! ### Relationship to [0,5]-parameterized boundary

The `[0,1]`-parameterized boundary `fdBoundaryFun H t` equals the `[0,5]`-parameterized
boundary `fdBoundary_H H (5 * t)` from `ValenceFormula/Boundary/Basic.lean`. This is a
simple rescaling: each segment `[k/5, (k+1)/5]` maps to `[k, k+1]` under `t ↦ 5t`.
-/

/-! ### Construction of FDWindingData from SingleCrossingData -/

/-- Build `FDWindingData` from individual `SingleCrossingData` instances.

This constructor shows how the winding weight specifications follow from
the single-crossing framework. Each winding weight (at `i`, `ρ`, `ρ+1`)
is obtained by providing:
1. A `SingleCrossingData` instance with the correct limit `L`
2. The proof that `L / (2πi)` equals the target weight

For interior points, the winding number follows from the contour integral
(standard Cauchy winding number for a closed curve avoiding the point). -/
private lemma pi_third_div_two_pi : -(↑Real.pi / 3 * I) / (2 * ↑Real.pi * I) = (-1 : ℂ) / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp; ring

def FDWindingData.mk_of_crossing {H : ℝ}
    (boundary : PiecewiseC1Path (fdStart H) (fdStart H))
    (hbdy : ∀ t ∈ Icc (0 : ℝ) 1, boundary.toPath.extend t = fdBoundaryFun H t)
    (h_int : ∀ z : ℂ, ‖z‖ > 1 → |z.re| < 1/2 → z.im > 0 → z.im < H →
      HasGeneralizedWindingNumber boundary z (-1))
    (D_i : SingleCrossingData boundary I)
    (hL_i : D_i.L = -(↑Real.pi * I))
    (D_rho : SingleCrossingData boundary ellipticPointRho)
    (hL_rho : D_rho.L = -(↑Real.pi / 3 * I))
    (D_rho1 : SingleCrossingData boundary ellipticPointRhoPlusOne)
    (hL_rho1 : D_rho1.L = -(↑Real.pi / 3 * I)) :
    FDWindingData H where
  boundary := boundary
  boundary_eq := hbdy
  interior_winding := h_int
  winding_at_i := by
    have := D_i.hasWindingNumber
    rwa [hL_i, show -(↑Real.pi * I) / (2 * ↑Real.pi * I) = (-1 : ℂ) / 2 from by
      have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hI : (I : ℂ) ≠ 0 := I_ne_zero
      field_simp] at this
  winding_at_rho := by
    have := D_rho.hasWindingNumber
    rwa [hL_rho, pi_third_div_two_pi] at this
  winding_at_rho_plus_one := by
    have := D_rho1.hasWindingNumber
    rwa [hL_rho1, pi_third_div_two_pi] at this

end
