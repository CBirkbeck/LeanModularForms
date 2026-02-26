/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary_Param
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Generalized Winding Number Weights on fdBoundary_H

This file computes the generalized winding number `generalizedWindingNumber'` of the
parameterized fundamental domain boundary `fdBoundary_H H` around each elliptic point.

The contour `fdBoundary_H H` is **clockwise** (CW), parameterized over [0, 5]:
- Seg 0 (t ∈ [0,1]): right vertical, from (1/2 + Hi) down to ρ'
- Seg 1 (t ∈ [1,2]): arc from ρ' to i
- Seg 2 (t ∈ [2,3]): arc from i to ρ
- Seg 3 (t ∈ [3,4]): left vertical, from ρ up to (-1/2 + Hi)
- Seg 4 (t ∈ [4,5]): horizontal from (-1/2 + Hi) to (1/2 + Hi)

## Main Results

* `gWN_fdBoundary_H_at_rho` — `generalizedWindingNumber' (fdBoundary_H H) 0 5 ρ = -1/6`
* `gWN_fdBoundary_H_at_rho_plus_one` — `generalizedWindingNumber' (fdBoundary_H H) 0 5 ρ' = -1/6`
* `gWN_fdBoundary_H_at_i` — `generalizedWindingNumber' (fdBoundary_H H) 0 5 I = -1/2`

## Proof Strategy

The PV integral `∫ (γ(t)-z₀)⁻¹ γ'(t) dt` with ε-ball cutoff is computed via:
1. **FTC on each smooth segment**: `∫_a^b (γ-z₀)⁻¹ γ' = log(γ(b)-z₀) - log(γ(a)-z₀)`
   when `γ(t)-z₀ ∈ slitPlane` on `[a,b]`.
2. **Telescope**: Since `γ(0) = γ(5)`, the sum telescopes to
   `PV(ε) = log(γ(t_L(ε))-z₀) - log(γ(t_R(ε))-z₀) + branch_corrections`
   where `t_L, t_R` are the cutoff boundaries satisfying `‖γ(t_L)-z₀‖ = ε = ‖γ(t_R)-z₀‖`.
3. **Modulus cancellation**: Since both endpoints have `|γ-z₀| = ε`, the log real parts cancel:
   `PV(ε) = i(arg_L - arg_R) + branch_corrections`.
4. **Limit**: As `ε → 0`, `arg_L` and `arg_R` converge to the directions of approach.

For ρ and ρ' (corner crossings, no branch cut): `PV = -iπ/3`, giving `gWN' = -1/6`.
For i (smooth crossing, branch cut on seg 3): `PV = iπ - 2πi = -iπ`, giving `gWN' = -1/2`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Euler's formula and trig helpers -/

private theorem exp_real_angle_I (θ : ℝ) :
    Complex.exp (↑θ * I) = ↑(Real.cos θ) + ↑(Real.sin θ) * I := by
  rw [Complex.exp_mul_I]; simp [Complex.ofReal_cos, Complex.ofReal_sin]

private theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]; ring

private theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.sin_pi_sub]; exact Real.sin_pi_div_three

/-! ## Section 1: Crossing Point Identification -/

/-- `fdBoundary_H H 1 = ρ'`. -/
theorem fdBoundary_H_at_one_eq_rho_plus_one (H : ℝ) :
    fdBoundary_H H 1 = ellipticPoint_rho_plus_one := by
  simp only [fdBoundary_H]
  simp only [show (1 : ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
  simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one', UpperHalfPlane.coe_mk_subtype]
  simp only [Complex.ofReal_one, one_mul]
  ring

/-- `fdBoundary_H H 2 = I`. -/
theorem fdBoundary_H_at_two_eq_I (H : ℝ) :
    fdBoundary_H H 2 = I := by
  simp only [fdBoundary_H]
  simp only [show ¬((2 : ℝ) ≤ 1) from by norm_num,
             show (2 : ℝ) ≤ 2 from le_refl 2, ↓reduceIte]
  rw [show (↑(Real.pi : ℝ) / 3 + (↑(2:ℝ) - 1) * (↑(Real.pi : ℝ) / 2 - ↑(Real.pi : ℝ) / 3)) * I =
    ↑(Real.pi / 2) * I from by push_cast; ring,
    exp_real_angle_I, Real.cos_pi_div_two, Real.sin_pi_div_two]
  push_cast; ring

/-- `fdBoundary_H H 3 = ρ`. -/
theorem fdBoundary_H_at_three_eq_rho (H : ℝ) :
    fdBoundary_H H 3 = ellipticPoint_rho := by
  simp only [fdBoundary_H]
  simp only [show ¬((3 : ℝ) ≤ 1) from by norm_num,
             show ¬((3 : ℝ) ≤ 2) from by norm_num,
             show (3 : ℝ) ≤ 3 from le_refl 3, ↓reduceIte]
  rw [show (↑(Real.pi : ℝ) / 2 + (↑(3:ℝ) - 2) * (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I =
    ↑(2 * Real.pi / 3) * I from by push_cast; ring,
    exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  push_cast; ring

/-! ## Section 2: Curve Values on Each Segment

Explicit formulas for `fdBoundary_H H t` on each segment, useful for
computing `γ(t) - z₀` and checking slit-plane membership.
-/

/-- On seg 0 (t ∈ [0,1]): `γ(t) = 1/2 + (H - t(H - √3/2))I`. -/
theorem fdBoundary_H_seg0 (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t = 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  simp only [fdBoundary_H, ht, ↓reduceIte]

/-- On seg 1 (t ∈ (1,2]): `γ(t) = exp((π/3 + (t-1)·π/6)I)`. -/
theorem fdBoundary_H_seg1 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : t ≤ 2) :
    fdBoundary_H H t = exp ((↑(Real.pi : ℝ) / 3 + (↑t - 1) * (↑(Real.pi : ℝ) / 2 - ↑(Real.pi : ℝ) / 3)) * I) := by
  simp only [fdBoundary_H, ht1, ht2, ↓reduceIte]

/-- On seg 2 (t ∈ (2,3]): `γ(t) = exp((π/2 + (t-2)·π/6)I)`. -/
theorem fdBoundary_H_seg2 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2)) (ht3 : t ≤ 3) :
    fdBoundary_H H t = exp ((↑(Real.pi : ℝ) / 2 + (↑t - 2) * (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I) := by
  simp only [fdBoundary_H, ht1, ht2, ht3, ↓reduceIte]

/-- On seg 3 (t ∈ (3,4]): `γ(t) = -1/2 + (√3/2 + (t-3)(H-√3/2))I`. -/
theorem fdBoundary_H_seg3 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2)) (ht3 : ¬(t ≤ 3)) (ht4 : t ≤ 4) :
    fdBoundary_H H t = -1/2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  simp only [fdBoundary_H, ht1, ht2, ht3, ht4, ↓reduceIte]

/-- On seg 4 (t ∈ (4,5]): `γ(t) = (t - 9/2) + HI`. -/
theorem fdBoundary_H_seg4 (H : ℝ) {t : ℝ} (ht1 : ¬(t ≤ 1)) (ht2 : ¬(t ≤ 2)) (ht3 : ¬(t ≤ 3)) (ht4 : ¬(t ≤ 4)) :
    fdBoundary_H H t = (↑t - 9/2) + ↑H * I := by
  simp only [fdBoundary_H, ht1, ht2, ht3, ht4, ↓reduceIte]

/-! ## Section 3: Difference γ(t) - ρ on Each Segment

We compute `fdBoundary_H H t - ellipticPoint_rho` on each segment and show it lies
in `Complex.slitPlane` (i.e., `re > 0` or `im ≠ 0`).
-/

/-- On seg 0: `γ(t) - ρ = 1 + (H - t(H-√3/2) - √3/2)I`, with `re = 1 > 0`. -/
theorem fdBoundary_H_sub_rho_seg0_re (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    (fdBoundary_H H t - ellipticPoint_rho).re = 1 := by
  rw [fdBoundary_H_seg0 H ht]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.neg_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
    Complex.sub_im, Complex.mul_im,
    Complex.div_ofNat_re, Complex.div_ofNat_im]
  ring

theorem fdBoundary_H_sub_rho_seg0_slitPlane (H : ℝ) {t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t - ellipticPoint_rho ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left; rw [fdBoundary_H_sub_rho_seg0_re H ht]; norm_num

/-- On seg 1: `γ(t) - ρ` has `re = cos(θ(t)) + 1/2` where `θ ∈ [π/3, π/2]`,
    so `cos(θ) ∈ [0, 1/2]` and `re ∈ [1/2, 1] > 0`. -/
theorem fdBoundary_H_sub_rho_seg1_re (H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht2 : t ≤ 2) :
    (fdBoundary_H H t - ellipticPoint_rho).re > 0 := by
  have h1 : ¬(t ≤ 1) := not_le.mpr ht1
  rw [fdBoundary_H_seg1 H h1 ht2]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  set θ : ℝ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
  rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
    (↑θ : ℂ) * I from by simp only [hθ_def]; push_cast; ring, exp_real_angle_I]
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.neg_re, Complex.one_re,
    Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div]
  -- Goal: cos θ + 1/2 > 0
  have hθ_upper : θ ≤ Real.pi / 2 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc ⟨by simp only [hθ_def]; nlinarith [Real.pi_pos], hθ_upper⟩
  linarith

/-- On seg 2 (t ∈ (2, 3)): `γ(t) - ρ` has `re = cos(θ(t)) + 1/2 > 0` since
    `θ ∈ (π/2, 2π/3)` gives `cos ∈ (-1/2, 0)` hence `re ∈ (0, 1/2)`. -/
theorem fdBoundary_H_sub_rho_seg2_re (H : ℝ) {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    (fdBoundary_H H t - ellipticPoint_rho).re > 0 := by
  have h1 : ¬(t ≤ 1) := by linarith
  have h2 : ¬(t ≤ 2) := by linarith
  rw [fdBoundary_H_seg2 H h1 h2 (le_of_lt ht3)]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  set θ : ℝ := Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) with hθ_def
  rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
    (↑θ : ℂ) * I from by simp only [hθ_def]; push_cast; ring, exp_real_angle_I]
  -- Difference = (cos θ + 1/2) + (sin θ - √3/2) * I, re = cos θ + 1/2
  have hre : (↑(Real.cos θ) + ↑(Real.sin θ) * I -
      (-1 / 2 + ↑(Real.sqrt 3) / 2 * I)).re = Real.cos θ + 1 / 2 := by
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.neg_re, Complex.one_re,
      Complex.div_ofNat_re, Complex.div_ofNat_im, zero_div]
    ring
  rw [hre]
  -- θ ∈ (π/2, 2π/3), cos(θ) > cos(2π/3) = -1/2, so cos(θ) + 1/2 > 0
  have hθ_upper : θ < 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
  have hcos_gt : Real.cos θ > -1 / 2 := by
    have := cos_two_pi_div_three
    rw [show (-1 : ℝ) / 2 = Real.cos (2 * Real.pi / 3) from by linarith]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi
      (by simp only [hθ_def]; nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) hθ_upper
  linarith

/-- On seg 3 (t ∈ (3, 4]): `γ(t) - ρ = (y(t) - √3/2)I` with `y > √3/2`, so `im > 0`. -/
theorem fdBoundary_H_sub_rho_seg3_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - ellipticPoint_rho ∈ slitPlane := by
  have h1 : ¬(t ≤ 1) := by linarith
  have h2 : ¬(t ≤ 2) := by linarith
  have h3 : ¬(t ≤ 3) := by linarith
  have h_diff : fdBoundary_H H t - (ellipticPoint_rho : ℂ) =
    ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I := by
    rw [fdBoundary_H_seg3 H h1 h2 h3 ht4]
    simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  rw [h_diff, Complex.mem_slitPlane_iff]; right
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  nlinarith

/-- On seg 4: `γ(t) - ρ` has `im = H - √3/2 > 0` for `H > √3/2`. -/
theorem fdBoundary_H_sub_rho_seg4_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 < t) (ht5 : t ≤ 5) :
    fdBoundary_H H t - ellipticPoint_rho ∈ slitPlane := by
  have h1 : ¬(t ≤ 1) := by linarith
  have h2 : ¬(t ≤ 2) := by linarith
  have h3 : ¬(t ≤ 3) := by linarith
  have h4 : ¬(t ≤ 4) := by linarith
  have h_diff : fdBoundary_H H t - (ellipticPoint_rho : ℂ) =
    ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I := by
    rw [fdBoundary_H_seg4 H h1 h2 h3 h4]
    simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  rw [h_diff, Complex.mem_slitPlane_iff]; right
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re]
  linarith

/-- Combined: `γ(t) - ρ ∈ slitPlane` for all `t ∈ [0, 5]` with `t ≠ 3`. -/
theorem fdBoundary_H_sub_rho_slitPlane (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 3) :
    fdBoundary_H H t - ellipticPoint_rho ∈ slitPlane := by
  rcases le_or_lt t 1 with h1 | h1
  · exact fdBoundary_H_sub_rho_seg0_slitPlane H h1
  · rcases le_or_lt t 2 with h2 | h2
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (fdBoundary_H_sub_rho_seg1_re H h1 h2))
    · rcases lt_or_ge t 3 with h3 | h3
      · exact Complex.mem_slitPlane_iff.mpr (Or.inl (fdBoundary_H_sub_rho_seg2_re H h2 h3))
      · rcases eq_or_lt_of_le h3 with h3eq | h3lt
        · exact absurd h3eq.symm hne
        · rcases le_or_lt t 4 with h4 | h4
          · exact fdBoundary_H_sub_rho_seg3_slitPlane H hH h3lt h4
          · exact fdBoundary_H_sub_rho_seg4_slitPlane H hH h4 ht.2

/-! ## Section 4: Uniqueness of Crossing -/

/-- `ρ` is only hit at `t = 3`. -/
theorem fdBoundary_H_eq_rho_iff (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) :
    fdBoundary_H H t = ellipticPoint_rho ↔ t = 3 := by
  constructor
  · intro heq
    by_contra hne
    have hmem := fdBoundary_H_sub_rho_slitPlane H hH ht hne
    rw [heq, sub_self] at hmem
    exact Complex.zero_notMem_slitPlane hmem
  · intro heq
    rw [heq, fdBoundary_H_at_three_eq_rho]

/-! ## Section 5: PV Integral = Arg Difference (Main Computational Result)

This is the core result: the regularized integral
`∫_{‖γ-ρ‖>ε} (γ-ρ)⁻¹ γ' = i(arg(γ(t_L)-ρ) - arg(γ(t_R)-ρ))`
where `t_L, t_R` are the ε-ball cutoff boundaries.

**Proof outline** (FTC approach):
1. On each smooth segment where `γ-ρ ∈ slitPlane`, `log(γ-ρ)` is an antiderivative.
2. By FTC: `∫_a^b (γ-ρ)⁻¹ γ' = log(γ(b)-ρ) - log(γ(a)-ρ)`.
3. Summing over segments, terms telescope. Since `γ(0)=γ(5)`: `PV = F(t_L) - F(t_R)`.
4. Since `|γ(t_L)-ρ| = ε = |γ(t_R)-ρ|`: `F(t_L) - F(t_R) = i(arg_L - arg_R)`.
5. As `ε→0`: `arg_L → π/6` (from arc approach), `arg_R → π/2` (from vertical approach).
-/

-- TODO: The full FTC-based proof for this section.
-- For now, we state the key results and prove them.

/-- Helper: for small δ > 0, `(γ(3-δ) - ρ).arg = π/6 - δπ/12`.

Proof: `γ(3-δ) - ρ = exp(i(2π/3-δπ/6)) - exp(i·2π/3)`. Using the angle shift
`2π/3 - δπ/6 = π/2 + (π/6 - δπ/6)` and sum-to-product formulas, the difference factors as
`2 sin(δπ/12) · (cos(π/6 - δπ/12) + sin(π/6 - δπ/12) I)`, giving `arg = π/6 - δπ/12`. -/
private lemma arg_approach_rho_left_helper (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (3 - δ) - ellipticPoint_rho).arg = Real.pi / 6 - δ * Real.pi / 12 := by
  have h1 : ¬(3 - δ ≤ 1) := by linarith
  have h2 : ¬(3 - δ ≤ 2) := by linarith
  rw [fdBoundary_H_seg2 H h1 h2 (by linarith : 3 - δ ≤ 3)]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  have h_angle : (↑(Real.pi : ℝ) / 2 + (↑(3 - δ : ℝ) - 2) *
      (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
    (↑(2 * Real.pi / 3 - δ * Real.pi / 6) : ℂ) * I := by congr 1; push_cast; ring
  rw [h_angle, exp_real_angle_I]
  -- Angle shift: cos(2π/3 - δπ/6) = -sin(π/6 - δπ/6), sin(2π/3 - δπ/6) = cos(π/6 - δπ/6)
  have h_cos_shift : Real.cos (2 * Real.pi / 3 - δ * Real.pi / 6) =
      -Real.sin (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show 2 * Real.pi / 3 - δ * Real.pi / 6 = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from
      by ring, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin_shift : Real.sin (2 * Real.pi / 3 - δ * Real.pi / 6) =
      Real.cos (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show 2 * Real.pi / 3 - δ * Real.pi / 6 = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from
      by ring, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  -- Sum-to-product: real part — sin(π/6) - sin(π/6-δπ/6) = 2 sin(δπ/12) cos(π/6-δπ/12)
  have h_re : -Real.sin (Real.pi / 6 - δ * Real.pi / 6) + 1 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin (Real.pi / 6) (Real.pi / 6 - δ * Real.pi / 6)
    rw [show (Real.pi / 6 - (Real.pi / 6 - δ * Real.pi / 6)) / 2 = δ * Real.pi / 12 from by ring,
        show (Real.pi / 6 + (Real.pi / 6 - δ * Real.pi / 6)) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring] at h
    linarith [Real.sin_pi_div_six]
  -- Sum-to-product: imaginary part — cos(π/6-δπ/6) - cos(π/6) = 2 sin(δπ/12) sin(π/6-δπ/12)
  have h_im : Real.cos (Real.pi / 6 - δ * Real.pi / 6) - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos (Real.pi / 6 - δ * Real.pi / 6) (Real.pi / 6)
    rw [show (Real.pi / 6 - δ * Real.pi / 6 + Real.pi / 6) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring,
        show (Real.pi / 6 - δ * Real.pi / 6 - Real.pi / 6) / 2 = -(δ * Real.pi / 12) from by ring,
        Real.sin_neg] at h
    nlinarith [Real.cos_pi_div_six,
      mul_comm (Real.sin (Real.pi / 6 - δ * Real.pi / 12)) (Real.sin (δ * Real.pi / 12))]
  -- Complex factorization: (cos+sinI) - ρ = 2sin(δπ/12) · (cos(π/6-δπ/12) + sin(π/6-δπ/12)I)
  have h_eq : ↑(Real.cos (2 * Real.pi / 3 - δ * Real.pi / 6)) +
      ↑(Real.sin (2 * Real.pi / 3 - δ * Real.pi / 6)) * I -
      (-1 / 2 + ↑(Real.sqrt 3) / 2 * I) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
         ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) := by
    rw [h_cos_shift, h_sin_shift]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one, zero_div]
      linarith [h_re]
    · simp only [add_im, sub_im, mul_im, neg_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero,
        mul_one, zero_div]
      linarith [h_im]
  rw [h_eq, show (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) : ℂ) =
    Complex.cos ↑(Real.pi / 6 - δ * Real.pi / 12) from Complex.ofReal_cos _,
    show (↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) : ℂ) =
    Complex.sin ↑(Real.pi / 6 - δ * Real.pi / 12) from Complex.ofReal_sin _]
  exact Complex.arg_mul_cos_add_sin_mul_I
    (mul_pos (by norm_num : (0:ℝ) < 2)
      (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])))
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- The `arg` of the approach direction from the left (seg 2 side) at `ρ`.
    `γ(3-δ) - ρ ≈ δ·(π/6)·exp(iπ/6)`, so `arg → π/6`. -/
theorem arg_approach_rho_left :
    Tendsto (fun δ => (fdBoundary_H H (3 - δ) - ellipticPoint_rho).arg)
      (𝓝[>] 0) (𝓝 (Real.pi / 6)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  refine ⟨min 1 ε, by positivity, ?_⟩
  intro x hx_mem hx_dist
  simp only [Real.dist_eq, Set.mem_Ioi] at hx_mem hx_dist ⊢
  have hx_small : x < 1 := by
    rw [sub_zero, abs_of_pos hx_mem] at hx_dist; linarith [min_le_left 1 ε]
  have h_arg := arg_approach_rho_left_helper (H := H) hx_mem hx_small
  rw [h_arg, show Real.pi / 6 - x * Real.pi / 12 - Real.pi / 6 = -(x * Real.pi / 12) from by ring,
      abs_neg, abs_of_pos (by positivity)]
  have hx_lt_eps : x < ε := by
    rw [sub_zero, abs_of_pos hx_mem] at hx_dist; linarith [min_le_right 1 ε]
  nlinarith [Real.pi_le_four]

/-- The `arg` of the approach direction from the right (seg 3 side) at `ρ`.
    `γ(3+δ) - ρ = δ(H-√3/2)I`, so `arg = π/2` (exact, not just limit). -/
theorem arg_approach_rho_right (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1) :
    (fdBoundary_H H (3 + δ) - ellipticPoint_rho).arg = Real.pi / 2 := by
  have h1 : ¬(3 + δ ≤ 1) := by linarith
  have h2 : ¬(3 + δ ≤ 2) := by linarith
  have h3 : ¬(3 + δ ≤ 3) := by linarith
  have h4 : 3 + δ ≤ 4 := by linarith
  have h_diff : fdBoundary_H H (3 + δ) - (ellipticPoint_rho : ℂ) =
    ↑(δ * (H - Real.sqrt 3 / 2)) * I := by
    rw [fdBoundary_H_seg3 H h1 h2 h3 h4]
    simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  rw [h_diff, Complex.arg_eq_pi_div_two_iff]
  constructor
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    nlinarith

/-- The curve `fdBoundary_H H` is closed: `γ(0) = γ(5)`. -/
private lemma fdBoundary_H_is_closed (H : ℝ) :
    fdBoundary_H H 0 = fdBoundary_H H 5 := by
  rw [fdBoundary_H_seg0 H (by norm_num : (0:ℝ) ≤ 1),
      fdBoundary_H_seg4 H (by norm_num : ¬((5:ℝ) ≤ 1)) (by norm_num : ¬((5:ℝ) ≤ 2))
        (by norm_num : ¬((5:ℝ) ≤ 3)) (by norm_num : ¬((5:ℝ) ≤ 4))]
  push_cast; ring

/-- On seg3, `g(3+δ) = δ·(H-√3/2)·I`. -/
private lemma g_seg3_value (H : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    fdBoundary_H H (3 + δ) - ellipticPoint_rho = ↑(δ * (H - Real.sqrt 3 / 2)) * I := by
  have h1 : ¬(3 + δ ≤ 1) := by linarith
  have h2 : ¬(3 + δ ≤ 2) := by linarith
  have h3 : ¬(3 + δ ≤ 3) := by linarith
  rw [fdBoundary_H_seg3 H h1 h2 h3 (by linarith : 3 + δ ≤ 4)]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  push_cast; ring

/-- The norm of `g(3+δ)` on seg3 is `δ·(H-√3/2)`. -/
private lemma g_norm_seg3 (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖fdBoundary_H H (3 + δ) - ellipticPoint_rho‖ = δ * (H - Real.sqrt 3 / 2) := by
  rw [g_seg3_value H hδ hδ1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by nlinarith : 0 ≤ δ * (H - Real.sqrt 3 / 2))]

/-- Norm of `g(3-δ)` on seg2: `2 sin(δπ/12)`. -/
private lemma g_norm_seg2 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (3 - δ) - ellipticPoint_rho‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  -- From arg_approach_rho_left_helper: g(3-δ) = 2sin(δπ/12)·(cos(φ)+sin(φ)I) with φ=π/6-δπ/12
  have h1 : ¬(3 - δ ≤ 1) := by linarith
  have h2 : ¬(3 - δ ≤ 2) := by linarith
  rw [fdBoundary_H_seg2 H h1 h2 (by linarith : 3 - δ ≤ 3)]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  set θ := 2 * Real.pi / 3 - δ * Real.pi / 6
  have h_cos_shift : Real.cos θ = -Real.sin (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin_shift : Real.sin θ = Real.cos (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re : -Real.sin (Real.pi / 6 - δ * Real.pi / 6) + 1 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin (Real.pi / 6) (Real.pi / 6 - δ * Real.pi / 6)
    rw [show (Real.pi / 6 - (Real.pi / 6 - δ * Real.pi / 6)) / 2 = δ * Real.pi / 12 from by ring,
        show (Real.pi / 6 + (Real.pi / 6 - δ * Real.pi / 6)) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring] at h
    linarith [Real.sin_pi_div_six]
  have h_im : Real.cos (Real.pi / 6 - δ * Real.pi / 6) - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos (Real.pi / 6 - δ * Real.pi / 6) (Real.pi / 6)
    rw [show (Real.pi / 6 - δ * Real.pi / 6 + Real.pi / 6) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring,
        show (Real.pi / 6 - δ * Real.pi / 6 - Real.pi / 6) / 2 = -(δ * Real.pi / 12) from by ring,
        Real.sin_neg] at h
    nlinarith [Real.cos_pi_div_six,
      mul_comm (Real.sin (Real.pi / 6 - δ * Real.pi / 12)) (Real.sin (δ * Real.pi / 12))]
  -- g(3-δ) = 2sin(δπ/12) · (cos(π/6-δπ/12) + sin(π/6-δπ/12)I)
  have h_eq : (↑(Real.cos θ) + ↑(Real.sin θ) * I - (-1/2 + ↑(Real.sqrt 3) / 2 * I)) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
         ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) := by
    rw [h_cos_shift, h_sin_shift]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one, zero_div]; linarith [h_re]
    · simp only [add_im, sub_im, mul_im, neg_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero,
        mul_one, zero_div]; linarith [h_im]
  rw [show (↑Real.pi / 2 + (↑(3 - δ : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
    (↑θ : ℂ) * I from by simp only [θ]; push_cast; ring, exp_real_angle_I, h_eq]
  -- Now: ‖↑(2 * sin(δπ/12)) * (↑cos(φ) + ↑sin(φ) * I)‖ = 2 * sin(δπ/12)
  have h_sin_nn : 0 ≤ Real.sin (δ * Real.pi / 12) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by norm_num) h_sin_nn),
    show (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
      ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) =
      Complex.exp (↑(Real.pi / 6 - δ * Real.pi / 12) * I) from by rw [exp_real_angle_I],
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Norm of `g(t) = γ(t) - ρ` on the full arc `(1, 3)`: `2 sin((3-t)π/12)`.
Generalizes `g_norm_seg2` (which only covers `t ∈ (2, 3)`) to the full arc. -/
private lemma g_norm_arc {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t - ellipticPoint_rho‖ = 2 * Real.sin ((3 - t) * Real.pi / 12) := by
  rw [fdBoundary_H_eq_arc ht1 ht3]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  set δ := 3 - t with hδ_def
  have hδ : 0 < δ := by linarith
  have hδ2 : δ < 2 := by linarith
  set θ := 2 * Real.pi / 3 - δ * Real.pi / 6
  rw [show Real.pi * (1 + t) / 6 = θ from by simp only [θ, hδ_def]; ring]
  have h_cos_shift : Real.cos θ = -Real.sin (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin_shift : Real.sin θ = Real.cos (Real.pi / 6 - δ * Real.pi / 6) := by
    rw [show θ = Real.pi / 2 + (Real.pi / 6 - δ * Real.pi / 6) from by simp only [θ]; ring,
        Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re : -Real.sin (Real.pi / 6 - δ * Real.pi / 6) + 1 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin (Real.pi / 6) (Real.pi / 6 - δ * Real.pi / 6)
    rw [show (Real.pi / 6 - (Real.pi / 6 - δ * Real.pi / 6)) / 2 = δ * Real.pi / 12 from by ring,
        show (Real.pi / 6 + (Real.pi / 6 - δ * Real.pi / 6)) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring] at h
    linarith [Real.sin_pi_div_six]
  have h_im : Real.cos (Real.pi / 6 - δ * Real.pi / 6) - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 6 - δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos (Real.pi / 6 - δ * Real.pi / 6) (Real.pi / 6)
    rw [show (Real.pi / 6 - δ * Real.pi / 6 + Real.pi / 6) / 2 = Real.pi / 6 - δ * Real.pi / 12
        from by ring,
        show (Real.pi / 6 - δ * Real.pi / 6 - Real.pi / 6) / 2 = -(δ * Real.pi / 12) from by ring,
        Real.sin_neg] at h
    nlinarith [Real.cos_pi_div_six,
      mul_comm (Real.sin (Real.pi / 6 - δ * Real.pi / 12)) (Real.sin (δ * Real.pi / 12))]
  have h_eq : (↑(Real.cos θ) + ↑(Real.sin θ) * I - (-1/2 + ↑(Real.sqrt 3) / 2 * I)) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
         ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) := by
    rw [h_cos_shift, h_sin_shift]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, neg_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero,
        mul_one, zero_div]; linarith [h_re]
    · simp only [add_im, sub_im, mul_im, neg_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero,
        mul_one, zero_div]; linarith [h_im]
  rw [show (↑(θ : ℝ) : ℂ) * I = (↑θ : ℂ) * I from rfl, exp_real_angle_I, h_eq]
  have h_sin_nn : 0 ≤ Real.sin (δ * Real.pi / 12) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by norm_num) h_sin_nn),
    show (↑(Real.cos (Real.pi / 6 - δ * Real.pi / 12)) +
      ↑(Real.sin (Real.pi / 6 - δ * Real.pi / 12)) * I) =
      Complex.exp (↑(Real.pi / 6 - δ * Real.pi / 12) * I) from by rw [exp_real_angle_I],
    Complex.norm_exp_ofReal_mul_I, mul_one]

/-- On [0, 1], ‖g(t)‖ ≥ 1 (real part is 1). -/
private lemma g_norm_ge_one_seg0 {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 ≤ ‖fdBoundary_H H t - ellipticPoint_rho‖ := by
  have hre : (fdBoundary_H H t - ellipticPoint_rho).re = 1 := fdBoundary_H_sub_rho_seg0_re H ht1
  calc 1 = |1| := (abs_of_pos one_pos).symm
    _ = |(fdBoundary_H H t - ellipticPoint_rho).re| := by rw [hre]
    _ ≤ ‖fdBoundary_H H t - ellipticPoint_rho‖ := Complex.abs_re_le_norm _

/-- On [4, 5], ‖g(t)‖ ≥ H - √3/2 (imaginary part is H - √3/2). -/
private lemma g_norm_ge_seg4 (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundary_H H t - ellipticPoint_rho‖ := by
  -- im(g) = H - √3/2 on all of [4, 5] (both seg3-endpoint and seg4)
  have him : (fdBoundary_H H t - (ellipticPoint_rho : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · -- t = 4: g = (H - √3/2)I
      have hd : fdBoundary_H H 4 - (ellipticPoint_rho : ℂ) = ↑(H - Real.sqrt 3 / 2) * I := by
        rw [fdBoundary_H_at_four H]
        simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
        push_cast; ring
      rw [hd, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    · -- t > 4: g = (t-4) + (H-√3/2)I
      have hd : fdBoundary_H H t - (ellipticPoint_rho : ℂ) =
          ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I := by
        rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
        simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
        push_cast; ring
      rw [hd, Complex.add_im, Complex.ofReal_im, zero_add,
        mul_comm, Complex.I_mul_im, Complex.ofReal_re]
  calc H - Real.sqrt 3 / 2
      = |(H - Real.sqrt 3 / 2 : ℝ)| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundary_H H t - (ellipticPoint_rho : ℂ)).im| := by rw [him]
    _ ≤ ‖fdBoundary_H H t - (ellipticPoint_rho : ℂ)‖ := Complex.abs_im_le_norm _

/-- DifferentiableAt for g = fdBoundary_H - ρ at interior points of each smooth segment. -/
private lemma g_rho_differentiableAt (H : ℝ) {t : ℝ}
    (ht : (0 < t ∧ t < 1) ∨ (1 < t ∧ t < 3) ∨ (3 < t ∧ t < 4) ∨ (4 < t ∧ t < 6)) :
    DifferentiableAt ℝ (fun s => fdBoundary_H H s - (ellipticPoint_rho : ℂ)) t := by
  apply DifferentiableAt.sub _ (differentiableAt_const _)
  have hd : DifferentiableAt ℝ (fun s : ℝ => (s : ℂ)) t := Complex.ofRealCLM.differentiableAt
  rcases ht with ⟨_, ht1⟩ | ⟨ht1, ht3⟩ | ⟨ht3, ht4⟩ | ⟨ht4, _⟩
  · -- seg0: affine
    have h_local : fdBoundary_H H =ᶠ[𝓝 t]
      (fun s => (1/2 : ℂ) + (↑H - ↑s * (↑H - ↑(Real.sqrt 3) / 2)) * I) := by
      filter_upwards [Iio_mem_nhds ht1] with s hs
      simp only [fdBoundary_H, show s ≤ 1 from le_of_lt hs, ↓reduceIte]
    exact DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_const _).add (((differentiableAt_const _).sub
        (hd.mul (differentiableAt_const _))).mul (differentiableAt_const _))) h_local
  · -- seg1+seg2: both formulas equal exp((π/6 + sπ/6)I) on (1,3)
    -- Use a single canonical form: exp((π/6 + sπ/6)I)
    have h_local : fdBoundary_H H =ᶠ[𝓝 t]
      (fun s => exp ((↑(Real.pi / 6) + ↑s * ↑(Real.pi / 6)) * I)) := by
      filter_upwards [Ioo_mem_nhds ht1 ht3] with s ⟨hs1, hs3⟩
      simp only [fdBoundary_H, show ¬(s ≤ 1) from not_le.mpr hs1]
      rcases le_or_gt s 2 with hs2 | hs2
      · simp only [hs2, ↓reduceIte]; congr 1; push_cast; ring
      · simp only [show ¬(s ≤ 2) from not_le.mpr hs2, show s ≤ 3 from le_of_lt hs3, ↓reduceIte]
        congr 1; push_cast; ring
    exact DifferentiableAt.congr_of_eventuallyEq
      ((((differentiableAt_const _).add (hd.mul (differentiableAt_const _))).mul
        (differentiableAt_const _)).cexp) h_local
  · -- seg3: affine
    have h_local : fdBoundary_H H =ᶠ[𝓝 t]
      (fun s => (-1/2 : ℂ) + (↑(Real.sqrt 3) / 2 + (↑s - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I) := by
      filter_upwards [Ioo_mem_nhds ht3 ht4] with s ⟨hs3, hs4⟩
      unfold fdBoundary_H
      rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_pos (by linarith)]
    exact DifferentiableAt.congr_of_eventuallyEq
      ((differentiableAt_const _).add (((differentiableAt_const _).add
        (((hd.sub (differentiableAt_const _)).mul (differentiableAt_const _)))).mul
        (differentiableAt_const _))) h_local
  · -- seg4: affine
    have h_local : fdBoundary_H H =ᶠ[𝓝 t]
      (fun s => (↑s - 9/2 : ℂ) + ↑H * I) := by
      filter_upwards [Ioi_mem_nhds ht4] with s hs4
      have hs4' : 4 < s := hs4
      unfold fdBoundary_H
      rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]
    exact DifferentiableAt.congr_of_eventuallyEq
      ((hd.sub (differentiableAt_const _)).add (differentiableAt_const _)) h_local

/-- FTC for log derivative on a sub-interval via smooth auxiliary.
Given smooth `h` agreeing with `g` on the open sub-interval, compute
`∫ g'/g = log g(b) - log g(a)` and produce `IntervalIntegrable`. -/
private lemma ftc_log_piece {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_slit : ∀ t ∈ Icc a b, h t ∈ Complex.slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hh_ne : ∀ t ∈ Icc a b, h t ≠ 0 := fun t ht => Complex.slitPlane_ne_zero (hh_slit t ht)
  have hh_div_cont : ContinuousOn (fun t => deriv h t / h t) (Icc a b) :=
    hh_deriv_cont.div hh_cont hh_ne
  have hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b :=
    (hh_div_cont.mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable
  -- ae equality on uIoc a b (differ at most at right endpoint b)
  have hb_ae : ({b} : Set ℝ)ᶜ ∈ ae volume :=
    mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton b)
  have h_congr : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t := by
    filter_upwards [hb_ae] with t ht_ne_b ht_mem
    have ht_ne : t ≠ b := fun h => ht_ne_b (mem_singleton_iff.mpr h)
    rw [uIoc_of_le hab] at ht_mem
    obtain ⟨hval, hderiv⟩ := heq t ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
    rw [hval, hderiv]
  -- IntervalIntegrable transfer via ae congr
  have hint_g : IntervalIntegrable (fun t => deriv g t / g t) volume a b := by
    constructor
    · exact MeasureTheory.Integrable.congr (show Integrable _ (volume.restrict (Ioc a b)) from hint_h.1)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (h_congr.mono (fun t ht hm => (ht (uIoc_of_le hab ▸ hm)).symm)))
    · rw [show Ioc b a = ∅ from Set.Ioc_eq_empty (not_lt.mpr hab)]
      exact MeasureTheory.integrableOn_empty
  -- FTC on h
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    (ContinuousOn.clog hh_cont hh_slit)
    (fun t ht => (hh_diff t ht).hasDerivAt.clog_real (hh_slit t (Ioo_subset_Icc_self ht))) hint_h
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (h b) - Complex.log (h a) := h_ftc
      _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]⟩

set_option maxHeartbeats 4000000 in
/-- FTC telescope for the logDeriv integral near ρ.

For δ_L, δ_R ∈ (0, 1), the sum of logDeriv integrals on [0, 3-δ_L] and [3+δ_R, 5]
telescopes to `log(g(3-δ_L)) - log(g(3+δ_R))`, using FTC on each smooth segment
([0,1], [1,3-δ_L], [3+δ_R,4], [4,5]) and `g(0) = g(5)`. -/
private lemma ftc_logDeriv_telescope_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1)
    (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) :
    let g := fun t => fdBoundary_H H t - (ellipticPoint_rho : ℂ)
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (3 - δ_L) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (3 + δ_R) 5 ∧
    ((∫ t in (0:ℝ)..(3 - δ_L), deriv g t / g t) +
    (∫ t in (3 + δ_R)..(5:ℝ), deriv g t / g t) =
    Complex.log (g (3 - δ_L)) - Complex.log (g (3 + δ_R))) := by
  intro g
  set ρ : ℂ := ellipticPoint_rho with hρ_def
  -- Auxiliary smooth functions on each piece
  -- h₀ on [0, 1]: seg0 - ρ
  set h₀ : ℝ → ℂ := fun t => 1 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2) - ↑(Real.sqrt 3) / 2) * I
  -- h₁ on [1, 3-δ_L]: arc - ρ
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - ρ
  -- h₂ on [3+δ_R, 4]: seg3 - ρ
  set h₂ : ℝ → ℂ := fun t => ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I
  -- h₃ on [4, 5]: seg4 - ρ
  set h₃ : ℝ → ℂ := fun t => ↑(t - 4) + ↑(H - Real.sqrt 3 / 2) * I
  -- Value agreement: g(t) = h_k(t) on relevant domains
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; show fdBoundary_H H t - ρ = h₀ t
    rw [fdBoundary_H_seg0 H ht]
    simp only [hρ_def, ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype, h₀]
    push_cast; ring
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3; show fdBoundary_H H t - ρ = h₁ t
    rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := by
    intro t ht3 ht4; show fdBoundary_H H t - ρ = h₂ t
    rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith) ht4]
    simp only [hρ_def, ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype, h₂]
    push_cast; ring
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := by
    intro t ht4; show fdBoundary_H H t - ρ = h₃ t
    rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
    simp only [hρ_def, ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype, h₃]
    push_cast; ring
  -- Endpoint values
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1_0 : g 1 = h₀ 1 := hg_eq_h₀ 1 (le_refl 1)
  have hg1_1 : g 1 = h₁ 1 := by
    show fdBoundary_H H 1 - ρ = h₁ 1
    rw [fdBoundary_H_at_one_eq_rho_plus_one]
    simp only [h₁, hρ_def, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
      ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring]
    rw [exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hg3mδ : g (3 - δ_L) = h₁ (3 - δ_L) := hg_eq_h₁ (3 - δ_L) (by linarith) (by linarith)
  have hg3pδ : g (3 + δ_R) = h₂ (3 + δ_R) := hg_eq_h₂ (3 + δ_R) (by linarith) (by linarith)
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) (le_refl 4)
  have hg4_3 : g 4 = h₃ 4 := by
    show fdBoundary_H H 4 - ρ = h₃ 4
    rw [fdBoundary_H_at_four H]
    simp only [hρ_def, ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype, h₃]
    push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  -- HasDerivAt for each h_k (needed for continuity, differentiability, deriv continuity)
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t
    set c : ℂ := ↑(H - Real.sqrt 3 / 2) * I
    have h_eq : h₀ = fun (s : ℝ) => (1 + c) + (-c) * ↑s := by
      ext s; simp only [h₀, c]; push_cast; ring
    rw [h_eq, show -(↑(H - Real.sqrt 3 / 2) : ℂ) * I = -c from by simp [c]; ring]
    exact ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-c)).const_add (1 + c)
      |>.congr_deriv (by simp [mul_one])
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
    intro t
    have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
      ((hasDerivAt_id t).add_const (1:ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
        (Eventually.of_forall fun s => show _ from by simp [id]; ring)
        |>.congr_deriv (by ring)
    have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
        ((↑(Real.pi / 6) : ℂ) * I) t :=
      (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
    exact (hci.cexp.sub (hasDerivAt_const t ρ)).congr_deriv (by simp only [sub_zero]; ring)
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t
    exact ((((hasDerivAt_id t).sub (hasDerivAt_const t 3)).mul_const
      (H - Real.sqrt 3 / 2)).ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t := by
    intro t
    have key := (((hasDerivAt_id t).sub (hasDerivAt_const t (4:ℝ))).ofReal_comp.add
      (hasDerivAt_const t (↑(H - Real.sqrt 3 / 2) * I)))
    convert key using 1; simp [sub_zero]
  -- Derivative agreement via EventuallyEq.deriv_eq
  have heq_01 : ∀ t ∈ Ioo (0:ℝ) 1, g t = h₀ t ∧ deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    refine ⟨hg_eq_h₀ t (le_of_lt ht1), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₀ :=
      Filter.eventually_of_mem (Iio_mem_nhds ht1) (fun s hs => hg_eq_h₀ s (le_of_lt hs))
    exact heq.deriv_eq
  have heq_1_3mδ : ∀ t ∈ Ioo (1:ℝ) (3 - δ_L), g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht1, ht3mδ⟩
    have ht3 : t < 3 := by linarith
    refine ⟨hg_eq_h₁ t ht1 ht3, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₁ :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht3) (fun s hs => hg_eq_h₁ s hs.1 hs.2)
    exact heq.deriv_eq
  have heq_3pδ_4 : ∀ t ∈ Ioo (3 + δ_R) (4:ℝ), g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht3, ht4⟩
    refine ⟨hg_eq_h₂ t (by linarith) (le_of_lt ht4), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₂ :=
      Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : 3 < t) ht4)
        (fun s hs => hg_eq_h₂ s (by linarith [hs.1]) (le_of_lt hs.2))
    exact heq.deriv_eq
  have heq_45 : ∀ t ∈ Ioo (4:ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t := by
    intro t ⟨ht4, _⟩
    refine ⟨hg_eq_h₃ t ht4, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₃ :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_eq_h₃ s hs)
    exact heq.deriv_eq
  -- Continuity, differentiability, deriv continuity from HasDerivAt
  have hh₀_cont : ContinuousOn h₀ (Icc 0 1) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont : ContinuousOn h₁ (Icc 1 (3 - δ_L)) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont : ContinuousOn h₂ (Icc (3 + δ_R) 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  have hh₀_diff : ∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff : ∀ t ∈ Ioo (1:ℝ) (3 - δ_L), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff : ∀ t ∈ Ioo (3 + δ_R) (4:ℝ), DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4:ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 1) := by
    rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₀ t).deriv]; exact continuousOn_const
  have hh₁_deriv_cont : ContinuousOn (deriv h₁) (Icc 1 (3 - δ_L)) := by
    rw [show deriv h₁ = fun t => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I) from
      funext fun t => (hd_h₁ t).deriv]
    exact (Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
      (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
      continuous_const))).continuousOn
  have hh₂_deriv_cont : ContinuousOn (deriv h₂) (Icc (3 + δ_R) 4) := by
    rw [show deriv h₂ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₂ t).deriv]; exact continuousOn_const
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) := by
    rw [show deriv h₃ = fun _ => (1 : ℂ) from
      funext fun t => (hd_h₃ t).deriv]; exact continuousOn_const
  -- Slit plane membership for each h_k
  have hh₀_slit : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ slitPlane := by
    intro t ht; rw [← hg_eq_h₀ t ht.2]
    exact fdBoundary_H_sub_rho_seg0_slitPlane H ht.2
  have hh₁_slit : ∀ t ∈ Icc (1:ℝ) (3 - δ_L), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht3⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · rw [← hg1_1]; exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by norm_num, by linarith⟩ (by linarith)
    · rw [← hg_eq_h₁ t ht1' (by linarith)]
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₂_slit : ∀ t ∈ Icc (3 + δ_R) (4:ℝ), h₂ t ∈ slitPlane := by
    intro t ⟨ht3, ht4⟩
    rw [← hg_eq_h₂ t (by linarith) ht4]
    exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₃_slit : ∀ t ∈ Icc (4:ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, ht5⟩
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [← hg4_3]; exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · rw [← hg_eq_h₃ t ht4']
      exact fdBoundary_H_sub_rho_slitPlane H hH ⟨by linarith, ht5⟩ (by linarith)
  -- Apply ftc_log_piece on each sub-interval
  have piece₀ := ftc_log_piece (by norm_num : (0:ℝ) ≤ 1) hh₀_cont hh₀_diff hh₀_deriv_cont
    hh₀_slit heq_01 hg0 hg1_0
  have piece₁ := ftc_log_piece (by linarith : (1:ℝ) ≤ 3 - δ_L) hh₁_cont hh₁_diff hh₁_deriv_cont
    hh₁_slit heq_1_3mδ (hg1_0.symm ▸ hg1_1) hg3mδ
  have piece₂ := ftc_log_piece (by linarith : (3 + δ_R) ≤ 4) hh₂_cont hh₂_diff hh₂_deriv_cont
    hh₂_slit heq_3pδ_4 hg3pδ (hg4_3.symm ▸ hg4_2)
  have piece₃ := ftc_log_piece (by norm_num : (4:ℝ) ≤ 5) hh₃_cont hh₃_diff hh₃_deriv_cont
    hh₃_slit heq_45 hg4_3 hg5
  -- Export integrability
  refine ⟨piece₀.1.trans piece₁.1, piece₂.1.trans piece₃.1, ?_⟩
  -- Combine integrals using adjacent intervals and telescope
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₀.1 piece₁.1).symm,
      (intervalIntegral.integral_add_adjacent_intervals piece₂.1 piece₃.1).symm,
      piece₀.2, piece₁.2, piece₂.2, piece₃.2]
  -- FTC pieces already give log(g(b)) - log(g(a)), so telescope directly
  have hg_closed : g 0 = g 5 := by
    show fdBoundary_H H 0 - ρ = fdBoundary_H H 5 - ρ
    rw [fdBoundary_H_is_closed H]
  rw [hg_closed]
  ring

set_option maxHeartbeats 800000 in
/-- For small ε, the ε-cutoff integral of g⁻¹·g' equals the FTC sum.

The set {t ∈ [0,5] : ‖g(t)‖ ≤ ε} is an interval [t_L, t_R] ⊂ (2, 4) for small ε,
so the cutoff integral splits as ∫₀^{t_L} + ∫_{t_R}^5. Since g⁻¹·g' = g'/g a.e.,
this equals the FTC sum. -/
private lemma cutoff_integral_eq_ftc (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {ε : ℝ} (hε : 0 < ε) (hε_small : ε < H - Real.sqrt 3 / 2)
    (hε_small2 : ε < 2 * Real.sin (Real.pi / 12)) :
    let g := fun t => fdBoundary_H H t - (ellipticPoint_rho : ℂ)
    (∃ δ_L ∈ Set.Ioo (0:ℝ) 1, ∃ δ_R ∈ Set.Ioo (0:ℝ) 1,
      ‖g (3 - δ_L)‖ = ε ∧ ‖g (3 + δ_R)‖ = ε ∧
      (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0:ℝ)..(3 - δ_L), deriv g t / g t) +
      (∫ t in (3 + δ_R)..(5:ℝ), deriv g t / g t)) := by
  intro g
  -- Step 1: Define δ_R and δ_L
  set δ_R := ε / (H - Real.sqrt 3 / 2) with hδ_R_def
  set δ_L := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_L_def
  -- Useful positivity facts
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by
    have := hε_small2
    have hsin_le : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _
    linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- Step 2: δ_R ∈ (0, 1)
  have hδ_R_pos : 0 < δ_R := div_pos hε hH_gap
  have hδ_R_lt_one : δ_R < 1 := by
    rw [hδ_R_def, div_lt_one hH_gap]; linarith
  -- Step 3: δ_L ∈ (0, 1)
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  have hδ_L_pos : 0 < δ_L := by
    rw [hδ_L_def]; exact mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos
  have hδ_L_lt_one : δ_L < 1 := by
    rw [hδ_L_def]
    -- Need: arcsin(ε/2) < π/12
    -- From hε_small2: ε < 2 sin(π/12), so ε/2 < sin(π/12)
    have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
    have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
      calc Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) := by
            exact Real.arcsin_lt_arcsin hε_half_neg hε_lt_sin (Real.sin_le_one _)
          _ = Real.pi / 12 := by
            exact Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) := by
          exact mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  -- Step 4: Norm equality for g(3 - δ_L)
  -- g_norm_seg2 gives ‖g(3 - δ_L)‖ = 2 sin(δ_L π / 12).
  -- We need 2 sin(δ_L π / 12) = ε.
  -- δ_L π / 12 = (12/π · arcsin(ε/2)) · π/12 = arcsin(ε/2).
  have hδ_L_angle : δ_L * Real.pi / 12 = Real.arcsin (ε / 2) := by
    rw [hδ_L_def]; field_simp
  have h_norm_L : ‖g (3 - δ_L)‖ = ε := by
    show ‖fdBoundary_H H (3 - δ_L) - ellipticPoint_rho‖ = ε
    rw [g_norm_seg2 hδ_L_pos hδ_L_lt_one, hδ_L_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]
    linarith
  -- Step 5: Norm equality for g(3 + δ_R)
  have h_norm_R : ‖g (3 + δ_R)‖ = ε := by
    show ‖fdBoundary_H H (3 + δ_R) - ellipticPoint_rho‖ = ε
    rw [g_norm_seg3 H hH hδ_R_pos (le_of_lt hδ_R_lt_one), hδ_R_def]
    field_simp
    have : H * 2 - Real.sqrt 3 > 0 := by nlinarith
    exact div_self (ne_of_gt this)
  -- Step 6: The integral equality
  -- Get integrability from ftc_logDeriv_telescope_rho
  have h_ftc := ftc_logDeriv_telescope_rho H hH hδ_L_pos hδ_L_lt_one hδ_R_pos hδ_R_lt_one
  obtain ⟨hint_L, hint_R, _⟩ := h_ftc
  -- Key norm bounds on each region
  -- (a) On [0, 1]: ‖g(t)‖ ≥ 1 > ε
  have hε_lt_one : ε < 1 := by
    have hsin_bound : Real.sin (Real.pi / 12) < 1 / 2 := by
      calc Real.sin (Real.pi / 12) < Real.sin (Real.pi / 6) :=
            Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
              (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        _ = 1 / 2 := by rw [Real.sin_pi_div_six]
    linarith
  -- (b) On (1, 3-δ_L): ‖g(t)‖ = 2 sin((3-t)π/12) > 2 sin(δ_L π/12) = ε
  -- Because (3-t)π/12 > δ_L π/12 and sin is strictly increasing on (0, π/6)
  -- (c) On [3-δ_L, 3]: ‖g(t)‖ = 2 sin((3-t)π/12) ≤ 2 sin(δ_L π/12) = ε
  -- (d) On [3, 3+δ_R]: ‖g(t)‖ = (t-3)(H-√3/2) ≤ δ_R(H-√3/2) = ε
  -- (e) On (3+δ_R, 4]: ‖g(t)‖ = (t-3)(H-√3/2) > δ_R(H-√3/2) = ε
  -- (f) On [4, 5]: ‖g(t)‖ ≥ H-√3/2 > ε
  -- First, establish that the cutoff integrand is ae-equal to g'/g on the outer pieces
  -- and ae-equal to 0 on the middle piece.
  -- Cutoff integrand
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ) with hF_def
  -- On [0, 3-δ_L], ‖g(t)‖ > ε (ae), so F = g⁻¹ · g' = g'/g
  have h_norm_gt_left : ∀ t ∈ Ioo (0 : ℝ) (3 - δ_L), ‖g t‖ > ε := by
    intro t ⟨ht0, ht3⟩
    rcases le_or_lt t 1 with ht1 | ht1
    · -- Seg 0: ‖g(t)‖ ≥ 1 > ε
      calc ε < 1 := hε_lt_one
        _ ≤ ‖g t‖ := g_norm_ge_one_seg0 (le_of_lt ht0) ht1
    · -- Arc (1, 3-δ_L): ‖g(t)‖ = 2 sin((3-t)π/12) > ε
      have ht3' : t < 3 := by linarith
      rw [show g t = fdBoundary_H H t - ellipticPoint_rho from rfl,
          g_norm_arc ht1 ht3']
      rw [← h_norm_L, show g (3 - δ_L) = fdBoundary_H H (3 - δ_L) - ellipticPoint_rho from rfl,
          g_norm_seg2 hδ_L_pos hδ_L_lt_one]
      -- Need: 2 sin((3-t)π/12) > 2 sin(δ_L π/12)
      -- Since 3-t > δ_L (i.e., t < 3-δ_L) and sin strictly increasing on relevant range
      have h_δ_lt : δ_L < 3 - t := by linarith
      have hpi12 : (0 : ℝ) < Real.pi / 12 := by positivity
      have h_angle_gt : δ_L * Real.pi / 12 < (3 - t) * Real.pi / 12 := by nlinarith
      have h_sin_mono : Real.sin (δ_L * Real.pi / 12) < Real.sin ((3 - t) * Real.pi / 12) := by
        apply Real.sin_lt_sin_of_lt_of_le_pi_div_two
        · nlinarith [Real.pi_pos]
        · nlinarith [Real.pi_pos]
        · exact h_angle_gt
      linarith
  -- On (3+δ_R, 5), ‖g(t)‖ > ε
  have h_norm_gt_right : ∀ t ∈ Ioo (3 + δ_R) (5 : ℝ), ‖g t‖ > ε := by
    intro t ⟨ht3, ht5⟩
    rcases le_or_lt t 4 with ht4 | ht4
    · -- Seg 3: ‖g(t)‖ = (t-3)(H-√3/2) > δ_R(H-√3/2) = ε
      have h_t_eq : t = 3 + (t - 3) := by ring
      rw [show g t = fdBoundary_H H t - ellipticPoint_rho from rfl, h_t_eq,
          g_norm_seg3 H hH (by linarith : 0 < t - 3) (by linarith : t - 3 ≤ 1)]
      rw [← h_norm_R, show g (3 + δ_R) = fdBoundary_H H (3 + δ_R) - ellipticPoint_rho from rfl,
          g_norm_seg3 H hH hδ_R_pos (le_of_lt hδ_R_lt_one)]
      have : δ_R < t - 3 := by linarith
      exact mul_lt_mul_of_pos_right this hH_gap
    · -- Seg 4 or [4,5]: ‖g(t)‖ ≥ H-√3/2 > ε
      calc ε < H - Real.sqrt 3 / 2 := hε_small
        _ ≤ ‖g t‖ := g_norm_ge_seg4 H hH (le_of_lt ht4) (le_of_lt ht5)
  -- On [3-δ_L, 3+δ_R], ‖g(t)‖ ≤ ε (so the indicator is 0)
  have h_norm_le_middle : ∀ t, 3 - δ_L ≤ t → t ≤ 3 + δ_R → ¬(‖g t‖ > ε) := by
    intro t ht_lo ht_hi
    push_neg
    rcases le_or_lt t 3 with ht3 | ht3
    · -- Arc side: ‖g(t)‖ = 2 sin((3-t)π/12) ≤ 2 sin(δ_L π/12) = ε
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · -- t = 3: g(3) = 0, ‖g(3)‖ = 0 ≤ ε
        simp only [show g 3 = fdBoundary_H H 3 - ellipticPoint_rho from rfl,
          fdBoundary_H_at_three_eq_rho, sub_self, norm_zero]
        exact le_of_lt hε
      · -- t ∈ (3-δ_L, 3)
        have ht1 : 1 < t := by nlinarith
        rw [show g t = fdBoundary_H H t - ellipticPoint_rho from rfl,
            g_norm_arc ht1 ht3']
        rw [← h_norm_L, show g (3 - δ_L) = fdBoundary_H H (3 - δ_L) - ellipticPoint_rho from rfl,
            g_norm_seg2 hδ_L_pos hδ_L_lt_one]
        -- 2 sin((3-t)π/12) ≤ 2 sin(δ_L π/12) since 3-t ≤ δ_L
        have h_3mt_le : 3 - t ≤ δ_L := by linarith
        have h_angle_le : (3 - t) * Real.pi / 12 ≤ δ_L * Real.pi / 12 := by
          have hpi12 : (0 : ℝ) < Real.pi / 12 := by positivity
          nlinarith
        have h_sin_le : Real.sin ((3 - t) * Real.pi / 12) ≤ Real.sin (δ_L * Real.pi / 12) := by
          exact Real.sin_le_sin_of_le_of_le_pi_div_two
            (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) h_angle_le
        linarith
    · -- Seg 3 side: ‖g(t)‖ = (t-3)(H-√3/2) ≤ δ_R(H-√3/2) = ε
      have ht_le_4 : t ≤ 4 := by linarith
      have h_t_as_3pδ : t = 3 + (t - 3) := by ring
      rw [show g t = fdBoundary_H H t - ellipticPoint_rho from rfl, h_t_as_3pδ,
          g_norm_seg3 H hH (by linarith) (by linarith : t - 3 ≤ 1)]
      rw [← h_norm_R, show g (3 + δ_R) = fdBoundary_H H (3 + δ_R) - ellipticPoint_rho from rfl,
          g_norm_seg3 H hH hδ_R_pos (le_of_lt hδ_R_lt_one)]
      have : t - 3 ≤ δ_R := by linarith
      exact mul_le_mul_of_nonneg_right this (le_of_lt hH_gap)
  -- Now prove the integral equality
  -- Step A: Split ∫₀⁵ F = ∫₀^{3-δ_L} F + ∫_{3-δ_L}^{3+δ_R} F + ∫_{3+δ_R}^5 F
  -- For this we need F to be interval integrable on [0,5].
  -- F agrees ae with g'/g on [0, 3-δ_L] and [3+δ_R, 5], and with 0 on [3-δ_L, 3+δ_R].
  -- So F is interval integrable on each piece.

  -- Pointwise equality helper: when ‖g t‖ > ε, F t = g'/g
  have hF_when_gt (t : ℝ) (h_gt : ‖g t‖ > ε) : F t = deriv g t / g t := by
    simp only [hF_def, if_pos h_gt, mul_comm (g t)⁻¹, div_eq_mul_inv]
  -- Pointwise equality helper: when ‖g t‖ ≤ ε, F t = 0
  have hF_when_le (t : ℝ) (h_le : ¬(‖g t‖ > ε)) : F t = 0 := by
    simp only [hF_def, if_neg h_le]
  -- Integrability of F on [0, 3-δ_L]: F =ae g'/g (off the endpoint {3-δ_L})
  have hF_eq_left_ae : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (3 - δ_L) → F t = deriv g t / g t := by
    have : ({3 - δ_L} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : (0:ℝ) ≤ 3 - δ_L)] at ht_mem
    have ht_lt : t < 3 - δ_L := lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))
    exact hF_when_gt t (h_norm_gt_left t ⟨ht_mem.1, ht_lt⟩)
  have hF_int_left : IntervalIntegrable F volume 0 (3 - δ_L) :=
    hint_L.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_left_ae.mono (fun t ht hm => (ht hm).symm)))

  -- Integrability of F on [3-δ_L, 3+δ_R]: F = 0 there (exact, not ae)
  have hF_eq_mid : ∀ t ∈ Ι (3 - δ_L) (3 + δ_R), F t = 0 := by
    intro t ht
    rw [uIoc_of_le (by linarith : 3 - δ_L ≤ 3 + δ_R)] at ht
    exact hF_when_le t (h_norm_le_middle t (le_of_lt ht.1) ht.2)
  have hF_int_mid : IntervalIntegrable F volume (3 - δ_L) (3 + δ_R) :=
    (IntervalIntegrable.zero (μ := volume) (a := 3 - δ_L) (b := 3 + δ_R)).congr
      (fun t ht => (hF_eq_mid t ht).symm)

  -- Integrability of F on [3+δ_R, 5]: F =ae g'/g (off endpoint {5})
  have hF_eq_right_ae : ∀ᵐ t ∂volume, t ∈ Ι (3 + δ_R) (5 : ℝ) → F t = deriv g t / g t := by
    have : ({5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : 3 + δ_R ≤ 5)] at ht_mem
    have ht_lt : t < 5 := lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))
    exact hF_when_gt t (h_norm_gt_right t ⟨ht_mem.1, ht_lt⟩)
  have hF_int_right : IntervalIntegrable F volume (3 + δ_R) 5 :=
    hint_R.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_right_ae.mono (fun t ht hm => (ht hm).symm)))

  -- Split the integral
  have h_adj1 := intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid
  have h_adj2 := intervalIntegral.integral_add_adjacent_intervals
    (hF_int_left.trans hF_int_mid) hF_int_right
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(3 - δ_L), F t) + (∫ t in (3 - δ_L)..(3 + δ_R), F t) +
      (∫ t in (3 + δ_R)..(5:ℝ), F t) := by
    rw [← h_adj2, ← h_adj1]
  -- The middle integral is 0
  have h_mid_zero : ∫ t in (3 - δ_L)..(3 + δ_R), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_eq_mid t ht))]
    simp [intervalIntegral.integral_zero]
  -- The left integral equals ∫ g'/g
  have h_left_eq : ∫ t in (0:ℝ)..(3 - δ_L), F t =
      ∫ t in (0:ℝ)..(3 - δ_L), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_eq_left_ae
  -- The right integral equals ∫ g'/g
  have h_right_eq : ∫ t in (3 + δ_R)..(5:ℝ), F t =
      ∫ t in (3 + δ_R)..(5:ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_eq_right_ae
  -- Combine
  refine ⟨δ_L, ⟨hδ_L_pos, hδ_L_lt_one⟩, δ_R, ⟨hδ_R_pos, hδ_R_lt_one⟩, h_norm_L, h_norm_R, ?_⟩
  calc (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
      = ∫ t in (0:ℝ)..5, F t := rfl
    _ = ((∫ t in (0:ℝ)..(3 - δ_L), F t) + (∫ t in (3 - δ_L)..(3 + δ_R), F t)) +
        (∫ t in (3 + δ_R)..(5:ℝ), F t) := h_split
    _ = ((∫ t in (0:ℝ)..(3 - δ_L), F t) + 0) +
        (∫ t in (3 + δ_R)..(5:ℝ), F t) := by rw [h_mid_zero]
    _ = (∫ t in (0:ℝ)..(3 - δ_L), deriv g t / g t) +
        (∫ t in (3 + δ_R)..(5:ℝ), deriv g t / g t) := by rw [h_left_eq, h_right_eq, add_zero]

/-- The PV integral of `(γ-ρ)⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ/3`. -/
theorem pv_integral_at_rho_tendsto (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - ellipticPoint_rho‖ > ε
      then (fdBoundary_H H t - ellipticPoint_rho)⁻¹ *
           deriv (fun s => fdBoundary_H H s - ellipticPoint_rho) t
      else 0)
      (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi / 3))) := by
  -- Use Metric.tendsto_nhdsWithin_nhds
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  -- Choose ε₀
  set ε₀ := min (min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))) r with hε₀_def
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hε₀_pos : 0 < ε₀ := lt_min (lt_min hH_gap h2sin_pos) hr
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε_lt_r : ε < r := lt_of_lt_of_le hε_dist (min_le_right _ _)
  -- Apply cutoff_integral_eq_ftc (which uses `let g`)
  set g := fun t => fdBoundary_H H t - (ellipticPoint_rho : ℂ) with hg_def
  have h_cutoff := cutoff_integral_eq_ftc H hH hε_pos hε_lt_gap hε_lt_2sin
  -- The `let g` in cutoff_integral_eq_ftc is beta-reduced, matching our `g` definitionally.
  obtain ⟨δ_L, ⟨hδ_L_pos, hδ_L_lt_one⟩, δ_R, ⟨hδ_R_pos, hδ_R_lt_one⟩,
    h_norm_L, h_norm_R, h_int_eq⟩ := h_cutoff
  -- Apply ftc_logDeriv_telescope_rho
  have h_ftc := ftc_logDeriv_telescope_rho H hH hδ_L_pos hδ_L_lt_one hδ_R_pos hδ_R_lt_one
  obtain ⟨_, _, h_telescope⟩ := h_ftc
  -- The integral equals log(g(3-δ_L)) - log(g(3+δ_R))
  rw [show dist (∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - (ellipticPoint_rho : ℂ)‖ > ε
      then (fdBoundary_H H t - (ellipticPoint_rho : ℂ))⁻¹ *
           deriv (fun s => fdBoundary_H H s - (ellipticPoint_rho : ℂ)) t
      else 0)
    (-(I * ↑Real.pi / 3)) =
    ‖(∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - (ellipticPoint_rho : ℂ)‖ > ε
      then (fdBoundary_H H t - (ellipticPoint_rho : ℂ))⁻¹ *
           deriv (fun s => fdBoundary_H H s - (ellipticPoint_rho : ℂ)) t
      else 0) -
    (-(I * ↑Real.pi / 3))‖ from Complex.dist_eq _ _]
  rw [h_int_eq, h_telescope]
  -- Now: ‖log(g(3-δ_L)) - log(g(3+δ_R)) - (-(I * ↑π / 3))‖ < r
  -- Decompose Complex.log: log z = ↑(Real.log ‖z‖) + ↑(z.arg) * I
  -- We use the fact that log x = ↑(log x).re + ↑(log x).im * I (from re_add_im)
  -- and then log_re, log_im to simplify.
  set zL := fdBoundary_H H (3 - δ_L) - (ellipticPoint_rho : ℂ)
  set zR := fdBoundary_H H (3 + δ_R) - (ellipticPoint_rho : ℂ)
  have h_decomp_L := Complex.re_add_im (Complex.log zL)
  have h_decomp_R := Complex.re_add_im (Complex.log zR)
  rw [← h_decomp_L, ← h_decomp_R, Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im]
  -- Use ‖zL‖ = ε = ‖zR‖ so Real.log parts cancel
  change ‖zL‖ = ε at h_norm_L
  change ‖zR‖ = ε at h_norm_R
  rw [h_norm_L, h_norm_R]
  -- Use arg formulas
  rw [arg_approach_rho_left_helper hδ_L_pos hδ_L_lt_one,
      arg_approach_rho_right H hH hδ_R_pos (le_of_lt hδ_R_lt_one)]
  -- Simplify: (↑(log ε) + ↑(π/6-δ_L*π/12)*I) - (↑(log ε) + ↑(π/2)*I) + I*↑π/3
  -- = ↑(-δ_L*π/12)*I
  have h_simp : ↑(Real.log ε) + ↑(Real.pi / 6 - δ_L * Real.pi / 12) * I -
      (↑(Real.log ε) + ↑(Real.pi / 2) * I) - -(I * ↑Real.pi / 3) =
      ↑(-(δ_L * Real.pi / 12)) * I := by
    push_cast; ring
  rw [h_simp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
  -- Need: δ_L * π / 12 < ε < r.
  -- From g_norm_seg2: 2*sin(δ_L*π/12) = ε, so sin(x) = ε/2 where x = δ_L*π/12.
  -- Using sin_gt_sub_cube: sin(x) > x - x³/4 > x/2 for 0 < x ≤ 1.
  -- Therefore ε = 2*sin(x) > x = δ_L*π/12.
  have h_angle_bound : δ_L * Real.pi / 12 < ε := by
    -- From h_norm_L: ‖zL‖ = 2*sin(δ_L*π/12) = ε
    have h2sin := g_norm_seg2 (H := H) hδ_L_pos hδ_L_lt_one
    have h_norm_L' : ‖zL‖ = ε := h_norm_L
    rw [h_norm_L'] at h2sin
    -- So sin(δ_L*π/12) = ε/2
    have h_sin_eq : Real.sin (δ_L * Real.pi / 12) = ε / 2 := by linarith
    -- We want: δ_L*π/12 < 2*sin(δ_L*π/12) = ε, i.e., sin(x) > x/2
    set x := δ_L * Real.pi / 12 with hx_def
    have hx_pos : 0 < x := by positivity
    have hx_le_one : x ≤ 1 := by
      have : x < Real.pi / 12 := by nlinarith
      linarith [Real.pi_le_four]
    -- sin_gt_sub_cube: for 0 < x ≤ 1, x - x³/4 < sin(x)
    have h_sin_lb := Real.sin_gt_sub_cube hx_pos hx_le_one
    -- x - x³/4 > x/2 when x² < 2, which holds since x ≤ 1
    have h_lb : x - x ^ 3 / 4 > x / 2 := by nlinarith [sq_nonneg x, sq_nonneg (1 - x)]
    -- Combine: sin(x) > x - x³/4 > x/2, so ε = 2*sin(x) > x
    linarith
  linarith

/-! ## Section 6: gWN' Values -/

/-- `generalizedWindingNumber' (fdBoundary_H H) 0 5 ρ = -1/6`. -/
theorem gWN_fdBoundary_H_at_rho (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPoint_rho = -1/6 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  -- Beta-reduce and remove `- 0` to match h_tendsto
  dsimp only []
  simp only [sub_zero]
  have h_tendsto := pv_integral_at_rho_tendsto H hH
  rw [h_tendsto.limUnder_eq]
  -- Now: (2πi)⁻¹ * (-iπ/3) = -1/6
  have h_pi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Real.pi_ne_zero, I_ne_zero]
  ring

/-! ### Section 5b: Infrastructure for the ρ' = ρ+1 Crossing at t = 1

The crossing at ρ' happens at t = 1. The PV integral should give -iπ/3, same as for ρ.

Key geometry:
- g(t) = fdBoundary_H H t - ellipticPoint_rho_plus_one
- Seg0 (t ∈ [0,1)): g(t) = (1-t)(H-√3/2)·I (pure positive imaginary)
- Arc (t ∈ (1,3)): g(t) = exp(iπ(1+t)/6) - exp(iπ/3), with im > 0
- Seg3 (t ∈ (3,4]): g(t) = -1 + (t-3)(H-√3/2)·I, with re = -1, im > 0
- Seg4 (t ∈ (4,5]): g(t) = (t-5) + (H-√3/2)·I, with im > 0
At t = 3: g(3) = ρ - ρ' = -1 (on branch cut, but approach is from im > 0 both sides)
-/

/-- Complex.arg is continuous on {z : im ≥ 0, z ≠ 0}.
On this set, `arg z = arccos(z.re / ‖z‖)`, and arccos ∘ (re/norm) is continuous. -/
private lemma continuousOn_arg_im_nonneg :
    ContinuousOn Complex.arg {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  intro z ⟨hz_im, hz_ne⟩
  exact ContinuousWithinAt.congr
    ((continuous_re.continuousWithinAt.div continuous_norm.continuousWithinAt
      (norm_ne_zero_iff.mpr hz_ne)).arccos)
    (fun w ⟨hw_im, hw_ne⟩ => Complex.arg_of_im_nonneg_of_ne_zero hw_im hw_ne)
    (Complex.arg_of_im_nonneg_of_ne_zero hz_im hz_ne)

/-- Complex.log is continuous on {z : im ≥ 0, z ≠ 0}. -/
private lemma continuousOn_clog_im_nonneg :
    ContinuousOn Complex.log {z : ℂ | 0 ≤ z.im ∧ z ≠ 0} := by
  intro z ⟨hz_im, hz_ne⟩
  -- log z = ↑(Real.log ‖z‖) + ↑(arg z) · I; show CWA of this decomposition
  have h_fun_eq : Complex.log = fun w => ↑(Real.log ‖w‖) + ↑(Complex.arg w) * I :=
    funext fun _ => rfl
  rw [h_fun_eq]
  apply ContinuousWithinAt.add
  · exact (continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_log (norm_ne_zero_iff.mpr hz_ne)).comp
        continuous_norm.continuousAt)).continuousWithinAt
  · exact (continuous_ofReal.continuousAt.comp_continuousWithinAt
      (continuousOn_arg_im_nonneg z ⟨hz_im, hz_ne⟩)).mul continuousWithinAt_const

/-- FTC for log derivative on a sub-interval where h maps into the upper half-plane.
This variant of `ftc_log_piece` handles the case where h(b) may lie on the negative real axis
(not in slitPlane), as long as h has im ≥ 0 and h ≠ 0 on [a, b]. -/
private lemma ftc_log_piece_upper {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_im_nn : ∀ t ∈ Icc a b, 0 ≤ (h t).im)
    (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0)
    (hh_slit_interior : ∀ t ∈ Ioo a b, h t ∈ slitPlane)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  -- log ∘ h is continuous on [a, b] via the upper half-plane continuity
  have hh_log_cont : ContinuousOn (fun t => Complex.log (h t)) (Icc a b) := by
    apply ContinuousOn.comp continuousOn_clog_im_nonneg hh_cont
    intro t ht; exact ⟨hh_im_nn t ht, hh_ne t ht⟩
  have hh_div_cont : ContinuousOn (fun t => deriv h t / h t) (Icc a b) :=
    hh_deriv_cont.div hh_cont hh_ne
  have hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b :=
    (hh_div_cont.mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable
  -- ae equality
  have hb_ae : ({b} : Set ℝ)ᶜ ∈ ae volume :=
    mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton b)
  have h_congr : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t := by
    filter_upwards [hb_ae] with t ht_ne_b ht_mem
    have ht_ne : t ≠ b := fun h => ht_ne_b (mem_singleton_iff.mpr h)
    rw [uIoc_of_le hab] at ht_mem
    obtain ⟨hval, hderiv⟩ := heq t ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
    rw [hval, hderiv]
  have hint_g : IntervalIntegrable (fun t => deriv g t / g t) volume a b := by
    constructor
    · exact MeasureTheory.Integrable.congr (show Integrable _ (volume.restrict (Ioc a b)) from hint_h.1)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (h_congr.mono (fun t ht hm => (ht (uIoc_of_le hab ▸ hm)).symm)))
    · rw [show Ioc b a = ∅ from Set.Ioc_eq_empty (not_lt.mpr hab)]
      exact MeasureTheory.integrableOn_empty
  -- FTC on h: HasDerivAt (log ∘ h) on interior uses slitPlane
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hh_log_cont
    (fun t ht => (hh_diff t ht).hasDerivAt.clog_real (hh_slit_interior t ht)) hint_h
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (h b) - Complex.log (h a) := h_ftc
      _ = Complex.log (g b) - Complex.log (g a) := by rw [heq_a, heq_b]⟩

/-- FTC for log derivative on a sub-interval where h maps into the lower half-plane.
This variant handles the case where h(a) or h(b) may lie on the negative real axis
(not in slitPlane), as long as h has im ≤ 0 and h ≠ 0 on [a, b].
The result uses `log(-g)` instead of `log(g)`. -/
private lemma ftc_log_piece_lower {g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hh_cont : ContinuousOn h (Icc a b))
    (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t)
    (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b))
    (hh_im_np : ∀ t ∈ Icc a b, (h t).im ≤ 0)
    (hh_ne : ∀ t ∈ Icc a b, h t ≠ 0)
    (hh_im_neg_interior : ∀ t ∈ Ioo a b, (h t).im < 0)
    (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t)
    (heq_a : g a = h a) (heq_b : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (-(g b)) - Complex.log (-(g a)) := by
  -- log ∘ (-h) is continuous on [a, b] since -h has im ≥ 0 and -h ≠ 0
  have hnh_log_cont : ContinuousOn (fun t => Complex.log (-(h t))) (Icc a b) := by
    apply ContinuousOn.comp continuousOn_clog_im_nonneg hh_cont.neg
    intro t ht; constructor
    · simp only [Pi.neg_apply, Complex.neg_im, Left.nonneg_neg_iff]; exact hh_im_np t ht
    · exact neg_ne_zero.mpr (hh_ne t ht)
  have hh_div_cont : ContinuousOn (fun t => deriv h t / h t) (Icc a b) :=
    hh_deriv_cont.div hh_cont hh_ne
  have hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b :=
    (hh_div_cont.mono (uIcc_of_le hab ▸ Subset.rfl)).intervalIntegrable
  -- ae equality
  have hb_ae : ({b} : Set ℝ)ᶜ ∈ ae volume :=
    mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton b)
  have h_congr : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t := by
    filter_upwards [hb_ae] with t ht_ne_b ht_mem
    have ht_ne : t ≠ b := fun h => ht_ne_b (mem_singleton_iff.mpr h)
    rw [uIoc_of_le hab] at ht_mem
    obtain ⟨hval, hderiv⟩ := heq t ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 ht_ne⟩
    rw [hval, hderiv]
  have hint_g : IntervalIntegrable (fun t => deriv g t / g t) volume a b := by
    constructor
    · exact MeasureTheory.Integrable.congr (show Integrable _ (volume.restrict (Ioc a b)) from hint_h.1)
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (h_congr.mono (fun t ht hm => (ht (uIoc_of_le hab ▸ hm)).symm)))
    · rw [show Ioc b a = ∅ from Set.Ioc_eq_empty (not_lt.mpr hab)]
      exact MeasureTheory.integrableOn_empty
  -- -h ∈ slitPlane on interior (since h has im < 0 there, so -h has im > 0)
  have hnh_slit : ∀ t ∈ Ioo a b, (-(h t)) ∈ slitPlane := by
    intro t ht; rw [Complex.mem_slitPlane_iff]; right
    simp only [Complex.neg_im, ne_eq, neg_eq_zero]
    exact ne_of_lt (hh_im_neg_interior t ht)
  -- FTC: d/dt log(-h(t)) = h'(t)/h(t), via chain rule
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
    hnh_log_cont
    (fun t ht => by
      have hda := (hh_diff t ht).hasDerivAt.neg
      have := hda.clog_real (hnh_slit t ht)
      -- this : HasDerivAt (fun s => log(-(h s))) ((-deriv h t) / (-(h t))) t
      -- (-deriv h t) / (-(h t)) = deriv h t / h t
      convert this using 1
      simp only [Pi.neg_apply, neg_div_neg_eq]) hint_h
  exact ⟨hint_g, by
    calc ∫ t in a..b, deriv g t / g t
        = ∫ t in a..b, deriv h t / h t := intervalIntegral.integral_congr_ae h_congr
      _ = Complex.log (-(h b)) - Complex.log (-(h a)) := h_ftc
      _ = Complex.log (-(g b)) - Complex.log (-(g a)) := by rw [heq_a, heq_b]⟩

/-! #### Difference γ(t) - ρ' on each segment -/

/-- On seg 0: γ(t) - ρ' = (1-t)·(H-√3/2)·I (pure imaginary). -/
private lemma g_rho'_seg0_value {t : ℝ} (ht : t ≤ 1) :
    fdBoundary_H H t - ellipticPoint_rho_plus_one =
    ↑((1 - t) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg0 H ht]
  simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one', UpperHalfPlane.coe_mk_subtype]
  push_cast; ring

/-- Norm on seg 0: ‖g(t)‖ = (1-t)·(H-√3/2). -/
private lemma g_rho'_norm_seg0 (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ‖fdBoundary_H H t - ellipticPoint_rho_plus_one‖ = (1 - t) * (H - Real.sqrt 3 / 2) := by
  rw [g_rho'_seg0_value (le_of_lt ht1), norm_mul, Complex.norm_real,
    Complex.norm_I, mul_one, Real.norm_of_nonneg (mul_nonneg (by linarith) (by linarith))]

/-- On the arc (t ∈ (1, 3)): γ(t) - ρ' = exp(iπ(1+t)/6) - exp(iπ/3). -/
private lemma g_rho'_arc_value {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    fdBoundary_H H t - ellipticPoint_rho_plus_one =
    Complex.exp (↑(Real.pi * (1 + t) / 6) * I) -
    (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) := by
  rw [fdBoundary_H_eq_arc ht1 ht3]
  simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one', UpperHalfPlane.coe_mk_subtype]
  push_cast; ring

/-- On seg 3: γ(t) - ρ' = -1 + (t-3)·(H-√3/2)·I. -/
private lemma g_rho'_seg3_value {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - ellipticPoint_rho_plus_one =
    -1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith) ht4]
  simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one', UpperHalfPlane.coe_mk_subtype]
  push_cast; ring

/-- On seg 4: γ(t) - ρ' = (t-5) + (H-√3/2)·I. -/
private lemma g_rho'_seg4_value {t : ℝ} (ht4 : 4 < t) :
    fdBoundary_H H t - ellipticPoint_rho_plus_one =
    ↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
  simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one', UpperHalfPlane.coe_mk_subtype]
  push_cast; ring

/-- `sin θ ≥ √3/2` for `θ ∈ [π/3, 2π/3]`. Uses symmetry about π/2. -/
private lemma sin_ge_sqrt3_div_2_of_mem {θ : ℝ}
    (hlo : Real.pi / 3 ≤ θ) (hhi : θ ≤ 2 * Real.pi / 3) :
    Real.sqrt 3 / 2 ≤ Real.sin θ := by
  rw [← Real.sin_pi_div_three]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) h hlo
  · push_neg at h
    rw [show θ = Real.pi - (Real.pi - θ) from by ring, Real.sin_pi_sub]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) (by nlinarith) (by nlinarith)

/-- `sin θ > √3/2` for `θ ∈ (π/3, 2π/3)`. Uses symmetry about π/2. -/
private lemma sin_gt_sqrt3_div_2_of_mem {θ : ℝ}
    (hlo : Real.pi / 3 < θ) (hhi : θ < 2 * Real.pi / 3) :
    Real.sqrt 3 / 2 < Real.sin θ := by
  rw [← Real.sin_pi_div_three]
  by_cases h : θ ≤ Real.pi / 2
  · exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) h hlo
  · push_neg at h
    rw [show θ = Real.pi - (Real.pi - θ) from by ring, Real.sin_pi_sub]
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
      (by nlinarith [Real.pi_pos]) (by nlinarith) (by nlinarith)

/-- γ(t) - ρ' has im ≥ 0 for t ∈ [0, 5] with t ≠ 1. -/
private lemma g_rho'_im_nonneg (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 1) :
    0 ≤ (fdBoundary_H H t - ellipticPoint_rho_plus_one).im := by
  rcases le_or_lt t 1 with h1 | h1
  · -- Seg 0: im = (1-t)(H-√3/2) ≥ 0
    have ht1 : t < 1 := lt_of_le_of_ne h1 hne
    rw [g_rho'_seg0_value h1, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    exact mul_nonneg (by linarith) (by linarith)
  · rcases lt_or_ge t 3 with h3 | h3
    · -- Arc (1, 3): im = sin(π(1+t)/6) - √3/2 ≥ 0
      rw [g_rho'_arc_value h1 h3]
      have hre_zero : (↑(Real.pi * (1 + t) / 6) * I : ℂ).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      simp only [sub_im, Complex.exp_im, hre_zero, Real.exp_zero, one_mul,
        add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, add_zero, mul_one]
      -- sin(π(1+t)/6) ≥ √3/2 for π(1+t)/6 ∈ [π/3, 2π/3]
      have h_sin_ge : Real.sqrt 3 / 2 ≤ Real.sin (Real.pi * (1 + t) / 6) :=
        sin_ge_sqrt3_div_2_of_mem (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      linarith
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · -- t = 3: g = -1, im = 0
        rw [fdBoundary_H_at_three_eq_rho]
        simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
          ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype,
          sub_im, add_im, neg_im, one_im, div_ofNat_im, mul_im, ofReal_im, I_re,
          I_im, ofReal_re, mul_zero, zero_mul, add_zero, mul_one, zero_div]
        ring_nf; norm_num
      · rcases le_or_lt t 4 with h4 | h4
        · -- Seg 3: im = (t-3)(H-√3/2) ≥ 0
          rw [g_rho'_seg3_value h3' h4]
          have : (-1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I : ℂ).im =
              (t - 3) * (H - Real.sqrt 3 / 2) := by
            simp [Complex.add_im, Complex.neg_im, Complex.one_im, Complex.mul_im,
              Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; exact mul_nonneg (by linarith) (by linarith)
        · -- Seg 4: im = H - √3/2 > 0
          rw [g_rho'_seg4_value h4]
          have : (↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I : ℂ).im =
              H - Real.sqrt 3 / 2 := by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; linarith

/-- γ(t) - ρ' ≠ 0 for t ∈ [0, 5] with t ≠ 1. -/
private lemma g_rho'_ne_zero (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne : t ≠ 1) :
    fdBoundary_H H t - ellipticPoint_rho_plus_one ≠ 0 := by
  intro h_eq
  rcases le_or_lt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne
    have h_val := g_rho'_seg0_value (H := H) h1
    rw [h_eq] at h_val
    have : ((1 - t) * (H - Real.sqrt 3 / 2)) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    exact this (by simpa [Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] using h_val)
  · rcases lt_or_ge t 3 with h3 | h3
    · -- Arc: im > 0 strictly, so g ≠ 0
      have hre_zero : (↑(Real.pi * (1 + t) / 6) * I : ℂ).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      have him_pos : 0 < (fdBoundary_H H t - ellipticPoint_rho_plus_one).im := by
        rw [g_rho'_arc_value h1 h3]
        simp only [sub_im, Complex.exp_im, hre_zero, Real.exp_zero, one_mul,
          add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, add_zero, mul_one]
        have : Real.sqrt 3 / 2 < Real.sin (Real.pi * (1 + t) / 6) :=
          sin_gt_sqrt3_div_2_of_mem (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        linarith
      rw [h_eq] at him_pos; simp at him_pos
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · -- t = 3: g = -1 ≠ 0
        rw [fdBoundary_H_at_three_eq_rho] at h_eq
        simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
          ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype] at h_eq
        have : (-1/2 + ↑(Real.sqrt 3) / 2 * I - (1/2 + ↑(Real.sqrt 3) / 2 * I) : ℂ) = -1 := by
          push_cast; ring
        rw [this] at h_eq; exact absurd h_eq (by norm_num)
      · rcases le_or_lt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4] at h_eq
          have hre : (-1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I : ℂ).re = -1 := by
            simp [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
              Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
          rw [h_eq] at hre; simp at hre
        · rw [g_rho'_seg4_value h4] at h_eq
          have him : (↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I : ℂ).im = H - Real.sqrt 3 / 2 := by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
              Complex.I_im, Complex.ofReal_re]
          rw [h_eq] at him; simp at him; linarith

/-- γ(t) - ρ' ∈ slitPlane for t ∈ [0, 5] with t ≠ 1 and t ≠ 3. -/
private lemma g_rho'_slitPlane (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 5) (hne1 : t ≠ 1) (hne3 : t ≠ 3) :
    fdBoundary_H H t - ellipticPoint_rho_plus_one ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rcases le_or_lt t 1 with h1 | h1
  · have ht1 : t < 1 := lt_of_le_of_ne h1 hne1
    rw [g_rho'_seg0_value h1, mul_comm, Complex.I_mul_im, Complex.ofReal_re]
    exact ne_of_gt (mul_pos (by linarith) (by linarith))
  · rcases lt_or_ge t 3 with h3 | h3
    · -- Arc: im > 0 strictly (since t ∈ (1,3))
      rw [g_rho'_arc_value h1 h3]
      have hre_zero : (↑(Real.pi * (1 + t) / 6) * I : ℂ).re = 0 := by
        simp [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      simp only [sub_im, Complex.exp_im, hre_zero, Real.exp_zero, one_mul,
        add_im, ofReal_im, mul_im, I_re, I_im, ofReal_re, mul_zero, add_zero, mul_one]
      have h_sin_gt : Real.sqrt 3 / 2 < Real.sin (Real.pi * (1 + t) / 6) :=
        sin_gt_sqrt3_div_2_of_mem (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
      exact ne_of_gt (by linarith)
    · rcases eq_or_lt_of_le h3 with rfl | h3'
      · exact absurd rfl hne3
      · rcases le_or_lt t 4 with h4 | h4
        · rw [g_rho'_seg3_value h3' h4]
          have : (-1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I : ℂ).im =
              (t - 3) * (H - Real.sqrt 3 / 2) := by
            simp [Complex.add_im, Complex.neg_im, Complex.one_im, Complex.mul_im,
              Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; exact ne_of_gt (mul_pos (by linarith) (by linarith))
        · rw [g_rho'_seg4_value h4]
          have : (↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I : ℂ).im = H - Real.sqrt 3 / 2 := by
            simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
              Complex.I_re, Complex.I_im, Complex.ofReal_re]
          rw [this]; exact ne_of_gt (by linarith)

/-! #### Norm on the arc near ρ' -/

/-- `exp(iπ/3) = 1/2 + √3/2 · I`. -/
private lemma exp_pi_div_three :
    Complex.exp (↑(Real.pi / 3) * I) = 1/2 + ↑(Real.sqrt 3 / 2) * I := by
  rw [show (↑(Real.pi / 3) : ℂ) * I = ↑(Real.pi / 3) * I from rfl, exp_real_angle_I,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

/-- Arg of approach from LEFT (seg0 side) at ρ': arg = π/2 (exact).
g(1-δ) = δ(H-√3/2)·I, so arg = π/2. -/
private theorem arg_approach_rho'_left (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (fdBoundary_H H (1 - δ) - ellipticPoint_rho_plus_one).arg = Real.pi / 2 := by
  rw [g_rho'_seg0_value (by linarith : 1 - δ ≤ 1)]
  rw [show (1 - (1 - δ)) = δ from by ring]
  rw [Complex.arg_eq_pi_div_two_iff]
  constructor
  · simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    ring
  · simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
    nlinarith

/-- Norm of g(1-δ) on seg0: ‖g‖ = δ·(H-√3/2). -/
private lemma g_rho'_norm_seg0_at (hH : Real.sqrt 3 / 2 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖fdBoundary_H H (1 - δ) - ellipticPoint_rho_plus_one‖ = δ * (H - Real.sqrt 3 / 2) := by
  rw [g_rho'_seg0_value (by linarith : 1 - δ ≤ 1)]
  rw [show (1 - (1 - δ)) = δ from by ring]
  rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg (mul_nonneg (le_of_lt hδ) (by linarith))]

/-- Helper: arg of approach from RIGHT (arc side) at ρ'.
g(1+δ) ≈ exp(iπ(2+δ)/6) - exp(iπ/3) = exp(iπ/3)·(exp(iδπ/6) - 1).
For small δ > 0: arg = 5π/6 - δπ/12.

More precisely: g(1+δ) = 2sin(δπ/12)·(cos(5π/6-δπ/12) + sin(5π/6-δπ/12)·I),
so arg = 5π/6 - δπ/12. -/
private lemma arg_approach_rho'_right_helper (hδ : 0 < δ) (hδ_small : δ < 2) :
    (fdBoundary_H H (1 + δ) - ellipticPoint_rho_plus_one).arg = 5 * Real.pi / 6 + δ * Real.pi / 12 := by
  have h1 : 1 < 1 + δ := by linarith
  have h3 : 1 + δ < 3 := by linarith
  rw [g_rho'_arc_value h1 h3]
  -- angle θ := π(1 + (1+δ))/6 = π(2+δ)/6 = π/3 + δπ/6
  set θ : ℝ := Real.pi * (1 + (1 + δ)) / 6 with hθ_def
  have hθ_eq : θ = Real.pi / 3 + δ * Real.pi / 6 := by simp only [hθ_def]; ring
  -- Rewrite arc value using Euler's formula
  rw [show (↑(Real.pi * (1 + (1 + δ)) / 6) : ℂ) * I = (↑θ : ℂ) * I from rfl, exp_real_angle_I]
  -- cos(θ) = cos(π/3 + δπ/6) = cos(π/3)cos(δπ/6) - sin(π/3)sin(δπ/6)
  -- sin(θ) = sin(π/3 + δπ/6) = sin(π/3)cos(δπ/6) + cos(π/3)sin(δπ/6)
  -- Difference: (cos θ - 1/2) + (sin θ - √3/2)I
  -- Using sum-to-product:
  -- cos θ - cos(π/3) = -2 sin((θ+π/3)/2) sin((θ-π/3)/2) = -2 sin(π/3+δπ/12) sin(δπ/12)
  -- sin θ - sin(π/3) = 2 cos((θ+π/3)/2) sin((θ-π/3)/2) = 2 cos(π/3+δπ/12) sin(δπ/12)
  -- So: g = 2sin(δπ/12)·(-sin(π/3+δπ/12) + cos(π/3+δπ/12)·I)
  -- Note: -sin(φ) + cos(φ)I = cos(π/2+φ) + sin(π/2+φ)I for φ = π/3+δπ/12
  -- arg = π/2 + π/3 + δπ/12 = 5π/6 + δπ/12... wait that's wrong.
  -- Let me redo: -sin(φ) + cos(φ)·I has arg = π - arctan(cos(φ)/sin(φ)) when sin(φ) > 0
  -- Actually: -sin(φ) + cos(φ)·I = cos(π/2+φ) + sin(π/2+φ)·I? No.
  -- cos(π/2+φ) = -sin(φ), sin(π/2+φ) = cos(φ). Yes!
  -- So arg(-sin(φ) + cos(φ)I) = π/2 + φ when this is in the right range.
  -- Wait, we need the angle to be in (-π, π]. π/2 + π/3 + δπ/12 = 5π/6 + δπ/12.
  -- For δ ∈ (0,2): 5π/6 + δπ/12 ∈ (5π/6, π]. Yes, this is ≤ π.
  -- Hmm wait, 5π/6 + 2π/12 = 5π/6 + π/6 = π. So for δ < 2, angle < π. Good.

  -- Actually I need to be more careful. Let me use φ = π/3 + δπ/12 and write
  -- g = 2sin(δπ/12) · (cos(π/2+φ) + sin(π/2+φ)·I)
  -- with π/2 + φ = π/2 + π/3 + δπ/12 = 5π/6 + δπ/12 ∈ (5π/6, π) for δ ∈ (0, 2).
  -- Wait that gives arg = 5π/6 + δπ/12 but I claimed it should be 5π/6 - δπ/12.

  -- Let me recompute from scratch.
  -- g = exp(iθ) - exp(iπ/3) where θ = π/3 + δπ/6
  -- = exp(iπ/3)(exp(iδπ/6) - 1)
  -- Now exp(iα) - 1 = 2i·sin(α/2)·exp(iα/2) for any α.
  -- So g = exp(iπ/3) · 2i·sin(δπ/12)·exp(iδπ/12)
  --      = 2sin(δπ/12) · i · exp(i(π/3 + δπ/12))
  --      = 2sin(δπ/12) · exp(iπ/2) · exp(i(π/3 + δπ/12))
  --      = 2sin(δπ/12) · exp(i(π/2 + π/3 + δπ/12))
  --      = 2sin(δπ/12) · exp(i(5π/6 + δπ/12))
  -- So arg(g) = 5π/6 + δπ/12 (when this is in (-π, π]).
  -- For δ ∈ (0, 2): 5π/6 + δπ/12 ∈ (5π/6, π). OK.
  -- But wait, arg_mul_cos_add_sin_mul_I needs the angle in (-π, π].
  -- 5π/6 + δπ/12 ≤ 5π/6 + 2π/12 = 5π/6 + π/6 = π. At δ=2 it's exactly π.
  -- For δ < 2: strictly less than π. For δ > 0: strictly more than 5π/6 > 0.
  -- So it's in (5π/6, π) ⊂ (-π, π]. Good.

  -- But the problem statement says arg = 5π/6 - δπ/12, which DECREASES with δ.
  -- I computed 5π/6 + δπ/12, which INCREASES with δ. One of us is wrong.
  -- Let me recheck: at δ = 0: g → 0 and arg undefined.
  -- At δ very small: g ≈ exp(iπ/3) · iδπ/6 = iδπ/6 · exp(iπ/3).
  -- arg(i · exp(iπ/3)) = arg(exp(i(π/2+π/3))) = arg(exp(i5π/6)) = 5π/6.
  -- So as δ → 0+: arg → 5π/6. And for larger δ: arg increases toward π.
  -- So arg = 5π/6 + δπ/12, NOT 5π/6 - δπ/12.
  -- The problem description is WRONG about the arg formula.
  -- But the PV still works: arg_right - arg_left = (5π/6 + δ_R π/12) - π/2 = π/3 + δ_R π/12.
  -- PV = i(arg_left - arg_right) = i(π/2 - 5π/6 - δ_R π/12) = i(-π/3 - δ_R π/12) → -iπ/3.
  -- That's the same answer! OK good.

  -- So: arg(g(1+δ)) = 5π/6 + δπ/12.

  -- Proof via factored form:
  -- Step 1: Show g = 2sin(δπ/12) · (cos(5π/6+δπ/12) + sin(5π/6+δπ/12)·I)
  -- Step 2: Apply arg_mul_cos_add_sin_mul_I

  -- Re-deriving step 1 using sum-to-product (as in the ρ case):
  -- cos(θ) - 1/2 = cos(θ) - cos(π/3)
  -- sin(θ) - √3/2 = sin(θ) - sin(π/3)
  -- where θ = π/3 + δπ/6

  have h_cos_sub : Real.cos θ - 1 / 2 =
      -2 * Real.sin (δ * Real.pi / 12) * Real.sin (Real.pi / 3 + δ * Real.pi / 12) := by
    have h := Real.cos_sub_cos θ (Real.pi / 3)
    rw [show (θ + Real.pi / 3) / 2 = Real.pi / 3 + δ * Real.pi / 12 from by rw [hθ_eq]; ring,
        show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring] at h
    linarith [Real.cos_pi_div_three]

  have h_sin_sub : Real.sin θ - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (Real.pi / 3 + δ * Real.pi / 12) := by
    have h := Real.sin_sub_sin θ (Real.pi / 3)
    rw [show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring,
        show (θ + Real.pi / 3) / 2 = Real.pi / 3 + δ * Real.pi / 12 from by rw [hθ_eq]; ring] at h
    linarith [Real.sin_pi_div_three]

  -- Now: -sin(π/3+δπ/12) + cos(π/3+δπ/12)·I = cos(π/2+π/3+δπ/12) + sin(π/2+π/3+δπ/12)·I
  -- = cos(5π/6+δπ/12) + sin(5π/6+δπ/12)·I
  set φ := Real.pi / 3 + δ * Real.pi / 12 with hφ_def
  have h_neg_sin_eq : -Real.sin φ = Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by rw [hφ_def]; ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_cos_eq : Real.cos φ = Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by rw [hφ_def]; ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring

  -- Complex equality: g = 2sin(δπ/12) · (cos(5π/6+δπ/12) + sin(5π/6+δπ/12)·I)
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12)) +
         ↑(Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12)) * I) := by
    rw [← h_neg_sin_eq, ← h_cos_eq]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one,
        zero_div, neg_re]; linarith [h_cos_sub]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero, mul_one,
        zero_div, neg_im]; linarith [h_sin_sub]
  rw [h_eq]
  -- Apply arg_mul_cos_add_sin_mul_I
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h_angle_lt_pi : 5 * Real.pi / 6 + δ * Real.pi / 12 < Real.pi := by
    nlinarith [Real.pi_pos, mul_pos (show (0:ℝ) < 2 - δ by linarith) Real.pi_pos]
  simp only [Complex.ofReal_cos, Complex.ofReal_sin]
  exact Complex.arg_mul_cos_add_sin_mul_I
    (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos)
    ⟨by linarith [show (0:ℝ) < 5 * Real.pi / 6 + δ * Real.pi / 12 from by positivity],
     le_of_lt h_angle_lt_pi⟩

/-- Norm of g(1+δ) on arc: ‖g‖ = 2 sin(δπ/12). -/
private lemma g_rho'_norm_arc {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    ‖fdBoundary_H H (1 + δ) - ellipticPoint_rho_plus_one‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 1 + δ := by linarith
  have h3 : 1 + δ < 3 := by linarith
  rw [g_rho'_arc_value h1 h3]
  set θ : ℝ := Real.pi * (1 + (1 + δ)) / 6
  set φ := Real.pi / 3 + δ * Real.pi / 12
  -- Same factored form as above
  have hθ_eq : θ = Real.pi / 3 + δ * Real.pi / 6 := by simp only [θ]; ring
  have h_cos_sub : Real.cos θ - 1 / 2 =
      -2 * Real.sin (δ * Real.pi / 12) * Real.sin φ := by
    have h := Real.cos_sub_cos θ (Real.pi / 3)
    rw [show (θ + Real.pi / 3) / 2 = φ from by simp only [φ, hθ_eq]; ring,
        show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring] at h
    linarith [Real.cos_pi_div_three]
  have h_sin_sub : Real.sin θ - Real.sqrt 3 / 2 =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos φ := by
    have h := Real.sin_sub_sin θ (Real.pi / 3)
    rw [show (θ - Real.pi / 3) / 2 = δ * Real.pi / 12 from by rw [hθ_eq]; ring,
        show (θ + Real.pi / 3) / 2 = φ from by simp only [φ, hθ_eq]; ring] at h
    linarith [Real.sin_pi_div_three]
  -- g = 2sin(δπ/12) · (-sinφ + cosφ·I) = 2sin(δπ/12) · exp(i(5π/6+δπ/12))
  have h_neg_sin_eq : -Real.sin φ = Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by simp only [φ]; ring,
      Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_cos_eq : Real.cos φ = Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12) := by
    rw [show 5 * Real.pi / 6 + δ * Real.pi / 12 = Real.pi / 2 + φ from by simp only [φ]; ring,
      Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - (↑(1/2 : ℝ) + ↑(Real.sqrt 3 / 2) * I) =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12)) +
         ↑(Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12)) * I) := by
    rw [← h_neg_sin_eq, ← h_cos_eq]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        one_re, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, sub_zero, add_zero, mul_one,
        zero_div, neg_re]; linarith [h_cos_sub]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        one_im, div_ofNat_re, div_ofNat_im, mul_zero, zero_mul, add_zero, mul_one,
        zero_div, neg_im]; linarith [h_sin_sub]
  rw [exp_real_angle_I, h_eq]
  have h_sin_nn : 0 ≤ Real.sin (δ * Real.pi / 12) :=
    le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (by norm_num) h_sin_nn),
    show (↑(Real.cos (5 * Real.pi / 6 + δ * Real.pi / 12)) +
      ↑(Real.sin (5 * Real.pi / 6 + δ * Real.pi / 12)) * I) =
      Complex.exp (↑(5 * Real.pi / 6 + δ * Real.pi / 12) * I) from by rw [exp_real_angle_I],
    Complex.norm_exp_ofReal_mul_I, mul_one]

set_option maxHeartbeats 400000 in
/-- Norm of g(t) on the full arc near ρ': ‖g(t)‖ = 2 sin((t-1)π/12) for t ∈ (1, 3). -/
private lemma g_rho'_norm_arc_full {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t - ellipticPoint_rho_plus_one‖ = 2 * Real.sin ((t - 1) * Real.pi / 12) := by
  have hδ : 0 < t - 1 := by linarith
  have hδ2 : t - 1 < 2 := by linarith
  convert g_rho'_norm_arc (δ := t - 1) hδ hδ2 using 2 <;> ring

/-- ‖g(t)‖ ≥ H - √3/2 on [4, 5]. -/
private lemma g_rho'_norm_ge_seg4 (hH : Real.sqrt 3 / 2 < H)
    {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - Real.sqrt 3 / 2 ≤ ‖fdBoundary_H H t - ellipticPoint_rho_plus_one‖ := by
  have him : (fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)).im = H - Real.sqrt 3 / 2 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · -- t = 4
      have : fdBoundary_H H 4 - (ellipticPoint_rho_plus_one : ℂ) = -1 + ↑(H - Real.sqrt 3 / 2) * I := by
        rw [fdBoundary_H_at_four]
        simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one', UpperHalfPlane.coe_mk_subtype]
        push_cast; ring
      rw [this, Complex.add_im, Complex.neg_im, Complex.one_im, mul_comm,
        Complex.I_mul_im, Complex.ofReal_re]; ring
    · rw [g_rho'_seg4_value ht4']
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, mul_zero, zero_mul, zero_add, add_zero, mul_one]
  calc H - Real.sqrt 3 / 2
      = |(H - Real.sqrt 3 / 2 : ℝ)| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)).im| := by rw [him]
    _ ≤ ‖fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)‖ := Complex.abs_im_le_norm _

/-- ‖g(t)‖ ≥ 1 on seg3 [3, 4] (re = -1, so ‖g‖ ≥ 1). -/
private lemma g_rho'_norm_ge_one_seg3
    {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    1 ≤ ‖fdBoundary_H H t - ellipticPoint_rho_plus_one‖ := by
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · -- t = 3: g = -1
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
      ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    have : (-1/2 + ↑(Real.sqrt 3) / 2 * I - (1/2 + ↑(Real.sqrt 3) / 2 * I) : ℂ) = -1 := by
      push_cast; ring
    rw [this, norm_neg, norm_one]
  · have hd := g_rho'_seg3_value (H := H) ht3' ht4
    have hre : (fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)).re = -1 := by
      rw [hd]; simp [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    calc 1 = |(-1 : ℝ)| := by norm_num
      _ = |(fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)).re| := by rw [hre]
      _ ≤ ‖fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)‖ := Complex.abs_re_le_norm _

/-! #### FTC Telescope for ρ' -/

set_option maxHeartbeats 8000000 in
/-- FTC telescope for the logDeriv integral near ρ'.

For δ_L, δ_R ∈ (0, 1), the sum of logDeriv integrals on [0, 1-δ_L] and [1+δ_R, 5]
telescopes to `log(g(1-δ_L)) - log(g(1+δ_R))`, using FTC on each smooth segment
([0, 1-δ_L], [1+δ_R, 3], [3, 4], [4, 5]) and `g(0) = g(5)`.

Note: at t = 3, g = -1 ∉ slitPlane, but g has im ≥ 0 and g ≠ 0 on each piece,
so we use `ftc_log_piece_upper` for the segments [1+δ_R, 3] and [3, 4]. -/
private lemma ftc_logDeriv_telescope_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H)
    {δ_L δ_R : ℝ} (hδ_L : 0 < δ_L) (hδ_L1 : δ_L < 1)
    (hδ_R : 0 < δ_R) (hδ_R1 : δ_R < 1) :
    let g := fun t => fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (1 - δ_L) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (1 + δ_R) 5 ∧
    ((∫ t in (0:ℝ)..(1 - δ_L), deriv g t / g t) +
    (∫ t in (1 + δ_R)..(5:ℝ), deriv g t / g t) =
    Complex.log (g (1 - δ_L)) - Complex.log (g (1 + δ_R))) := by
  intro g
  set ρ' : ℂ := ellipticPoint_rho_plus_one with hρ'_def
  -- Auxiliary smooth functions on each piece
  -- h₀ on [0, 1-δ_L]: seg0 - ρ' = (1-t)·(H-√3/2)·I
  set h₀ : ℝ → ℂ := fun t => ↑((1 - t) * (H - Real.sqrt 3 / 2)) * I
  -- h₁ on [1+δ_R, 3]: arc - ρ'
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - ρ'
  -- h₂ on [3, 4]: seg3 - ρ' = -1 + (t-3)·(H-√3/2)·I
  set h₂ : ℝ → ℂ := fun t => -1 + ↑((t - 3) * (H - Real.sqrt 3 / 2)) * I
  -- h₃ on [4, 5]: seg4 - ρ' = (t-5) + (H-√3/2)·I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 5) + ↑(H - Real.sqrt 3 / 2) * I
  -- Value agreement: g(t) = h_k(t) on relevant domains
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; show fdBoundary_H H t - ρ' = h₀ t
    rw [g_rho'_seg0_value ht]
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3; show fdBoundary_H H t - ρ' = h₁ t
    rw [g_rho'_arc_value ht1 ht3]
    simp only [h₁, hρ'_def, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
      UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := by
    intro t ht3 ht4; show fdBoundary_H H t - ρ' = h₂ t
    rw [g_rho'_seg3_value ht3 ht4]
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := by
    intro t ht4; show fdBoundary_H H t - ρ' = h₃ t
    rw [g_rho'_seg4_value ht4]
  -- Endpoint values
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1mδ : g (1 - δ_L) = h₀ (1 - δ_L) := hg_eq_h₀ (1 - δ_L) (by linarith)
  have hg1pδ : g (1 + δ_R) = h₁ (1 + δ_R) := hg_eq_h₁ (1 + δ_R) (by linarith) (by linarith)
  have hg3_1 : g 3 = h₁ 3 := by
    show fdBoundary_H H 3 - ρ' = h₁ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₁, hρ'_def, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
      ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring]
    rw [exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hg3_2 : g 3 = h₂ 3 := by
    show fdBoundary_H H 3 - ρ' = h₂ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₂, hρ'_def, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
      ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) (le_refl 4)
  have hg4_3 : g 4 = h₃ 4 := by
    show fdBoundary_H H 4 - ρ' = h₃ 4
    rw [fdBoundary_H_at_four H]
    simp only [hρ'_def, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
      UpperHalfPlane.coe_mk_subtype, h₃]
    push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  -- HasDerivAt for each h_k
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t
    have h_eq : h₀ = fun (s : ℝ) => (↑((1 - s) * (H - Real.sqrt 3 / 2)) : ℂ) * I := rfl
    rw [h_eq]
    have := ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).mul_const
      (H - Real.sqrt 3 / 2) |>.ofReal_comp.mul_const I
    convert this using 1; simp
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
    intro t
    have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
      ((hasDerivAt_id t).add_const (1:ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
        (Eventually.of_forall fun s => show _ from by simp [id]; ring)
        |>.congr_deriv (by ring)
    have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
        ((↑(Real.pi / 6) : ℂ) * I) t :=
      (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
    exact (hci.cexp.sub (hasDerivAt_const t ρ')).congr_deriv (by simp only [sub_zero]; ring)
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t
    exact ((hasDerivAt_const t (-1:ℂ)).add
      ((((hasDerivAt_id t).sub (hasDerivAt_const t 3)).mul_const
      (H - Real.sqrt 3 / 2)).ofReal_comp.mul_const I)).congr_deriv (by
        simp [zero_add])
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t := by
    intro t
    have key := (((hasDerivAt_id t).sub (hasDerivAt_const t (5:ℝ))).ofReal_comp.add
      (hasDerivAt_const t (↑(H - Real.sqrt 3 / 2) * I)))
    convert key using 1; simp [sub_zero]
  -- Derivative agreement via EventuallyEq.deriv_eq
  have heq_0_1mδ : ∀ t ∈ Ioo (0:ℝ) (1 - δ_L), g t = h₀ t ∧ deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    refine ⟨hg_eq_h₀ t (by linarith), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₀ :=
      Filter.eventually_of_mem (Iio_mem_nhds (show t < 1 by linarith))
        (fun s hs => hg_eq_h₀ s (le_of_lt hs))
    exact heq.deriv_eq
  have heq_1pδ_3 : ∀ t ∈ Ioo (1 + δ_R) (3:ℝ), g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht1, ht3⟩
    refine ⟨hg_eq_h₁ t (by linarith) ht3, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₁ :=
      Filter.eventually_of_mem (Ioo_mem_nhds (by linarith : 1 < t) ht3)
        (fun s hs => hg_eq_h₁ s hs.1 hs.2)
    exact heq.deriv_eq
  have heq_34 : ∀ t ∈ Ioo (3:ℝ) 4, g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht3, ht4⟩
    refine ⟨hg_eq_h₂ t ht3 (le_of_lt ht4), ?_⟩
    have heq : g =ᶠ[𝓝 t] h₂ :=
      Filter.eventually_of_mem (Ioo_mem_nhds ht3 ht4)
        (fun s hs => hg_eq_h₂ s hs.1 (le_of_lt hs.2))
    exact heq.deriv_eq
  have heq_45 : ∀ t ∈ Ioo (4:ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t := by
    intro t ⟨ht4, _⟩
    refine ⟨hg_eq_h₃ t ht4, ?_⟩
    have heq : g =ᶠ[𝓝 t] h₃ :=
      Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_eq_h₃ s hs)
    exact heq.deriv_eq
  -- Continuity from HasDerivAt
  have hh₀_cont : ContinuousOn h₀ (Icc 0 (1 - δ_L)) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont : ContinuousOn h₁ (Icc (1 + δ_R) 3) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont : ContinuousOn h₂ (Icc 3 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  -- Differentiability from HasDerivAt
  have hh₀_diff : ∀ t ∈ Ioo (0:ℝ) (1 - δ_L), DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff : ∀ t ∈ Ioo (1 + δ_R) (3:ℝ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff : ∀ t ∈ Ioo (3:ℝ) 4, DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4:ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  -- Derivative continuity
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 (1 - δ_L)) := by
    rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₀ t).deriv]; exact continuousOn_const
  have hh₁_deriv_cont : ContinuousOn (deriv h₁) (Icc (1 + δ_R) 3) := by
    rw [show deriv h₁ = fun t => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I) from
      funext fun t => (hd_h₁ t).deriv]
    exact (Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
      (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
      continuous_const))).continuousOn
  have hh₂_deriv_cont : ContinuousOn (deriv h₂) (Icc 3 4) := by
    rw [show deriv h₂ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₂ t).deriv]; exact continuousOn_const
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) := by
    rw [show deriv h₃ = fun _ => (1 : ℂ) from
      funext fun t => (hd_h₃ t).deriv]; exact continuousOn_const
  -- Piece 0: [0, 1-δ_L] — use ftc_log_piece (slitPlane)
  have hh₀_slit : ∀ t ∈ Icc (0:ℝ) (1 - δ_L), h₀ t ∈ slitPlane := by
    intro t ⟨ht0, ht1⟩
    rw [← hg_eq_h₀ t (by linarith)]
    exact g_rho'_slitPlane hH ⟨ht0, by linarith⟩ (by linarith) (by linarith)
  have piece₀ := ftc_log_piece (by linarith : (0:ℝ) ≤ 1 - δ_L) hh₀_cont hh₀_diff
    hh₀_deriv_cont hh₀_slit heq_0_1mδ hg0 hg1mδ
  -- Piece 1: [1+δ_R, 3] — use ftc_log_piece_upper (t=3 maps to -1 ∉ slitPlane)
  have hh₁_im_nn : ∀ t ∈ Icc (1 + δ_R) (3:ℝ), 0 ≤ (h₁ t).im := by
    intro t ⟨ht1, ht3⟩
    rw [← show g t = h₁ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_1
      · exact hg_eq_h₁ t (by linarith) ht3']
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_im_nonneg hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_im_nonneg hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₁_ne : ∀ t ∈ Icc (1 + δ_R) (3:ℝ), h₁ t ≠ 0 := by
    intro t ⟨ht1, ht3⟩
    rw [← show g t = h₁ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_1
      · exact hg_eq_h₁ t (by linarith) ht3']
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_ne_zero hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_ne_zero hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₁_slit_interior : ∀ t ∈ Ioo (1 + δ_R) (3:ℝ), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht3⟩
    rw [← hg_eq_h₁ t (by linarith) ht3]
    exact g_rho'_slitPlane hH ⟨by linarith, by linarith⟩ (by linarith) (by linarith)
  have piece₁ := ftc_log_piece_upper (by linarith : (1 + δ_R) ≤ 3) hh₁_cont hh₁_diff
    hh₁_deriv_cont hh₁_im_nn hh₁_ne hh₁_slit_interior heq_1pδ_3 hg1pδ (hg3_2.symm ▸ hg3_1)
  -- Piece 2: [3, 4] — use ftc_log_piece_upper (t=3 maps to -1 ∉ slitPlane)
  have hh₂_im_nn : ∀ t ∈ Icc (3:ℝ) 4, 0 ≤ (h₂ t).im := by
    intro t ⟨ht3, ht4⟩
    rw [← show g t = h₂ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_2
      · exact hg_eq_h₂ t ht3' ht4]
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_im_nonneg hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_im_nonneg hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₂_ne : ∀ t ∈ Icc (3:ℝ) 4, h₂ t ≠ 0 := by
    intro t ⟨ht3, ht4⟩
    rw [← show g t = h₂ t from by
      rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · exact hg3_2
      · exact hg_eq_h₂ t ht3' ht4]
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · exact g_rho'_ne_zero hH ⟨by norm_num, by norm_num⟩ (by norm_num)
    · exact g_rho'_ne_zero hH ⟨by linarith, by linarith⟩ (by linarith)
  have hh₂_slit_interior : ∀ t ∈ Ioo (3:ℝ) 4, h₂ t ∈ slitPlane := by
    intro t ⟨ht3, ht4⟩
    rw [← hg_eq_h₂ t ht3 (le_of_lt ht4)]
    exact g_rho'_slitPlane hH ⟨by linarith, by linarith⟩ (by linarith) (by linarith)
  have piece₂ := ftc_log_piece_upper (by norm_num : (3:ℝ) ≤ 4) hh₂_cont hh₂_diff
    hh₂_deriv_cont hh₂_im_nn hh₂_ne hh₂_slit_interior heq_34 hg3_2 (hg4_3.symm ▸ hg4_2)
  -- Piece 3: [4, 5] — use ftc_log_piece (slitPlane)
  have hh₃_slit : ∀ t ∈ Icc (4:ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, ht5⟩
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [← hg4_3]; exact g_rho'_slitPlane hH ⟨by norm_num, by norm_num⟩ (by norm_num) (by norm_num)
    · rw [← hg_eq_h₃ t ht4']
      exact g_rho'_slitPlane hH ⟨by linarith, ht5⟩ (by linarith) (by linarith)
  have piece₃ := ftc_log_piece (by norm_num : (4:ℝ) ≤ 5) hh₃_cont hh₃_diff hh₃_deriv_cont
    hh₃_slit heq_45 hg4_3 hg5
  -- Export integrability and combine
  refine ⟨piece₀.1, piece₁.1.trans (piece₂.1.trans piece₃.1), ?_⟩
  -- Combine integrals using adjacent intervals and telescope
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₁.1
      (piece₂.1.trans piece₃.1)).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₂.1 piece₃.1).symm,
    piece₀.2, piece₁.2, piece₂.2, piece₃.2]
  -- FTC pieces give log(g(b)) - log(g(a)), so telescope directly
  have hg_closed : g 0 = g 5 := by
    show fdBoundary_H H 0 - ρ' = fdBoundary_H H 5 - ρ'
    rw [fdBoundary_H_is_closed H]
  rw [hg_closed]
  ring

set_option maxHeartbeats 8000000 in
/-- The PV integral of `(γ-ρ')⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ/3`. -/
theorem pv_integral_at_rho_plus_one_tendsto (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - ellipticPoint_rho_plus_one‖ > ε
      then (fdBoundary_H H t - ellipticPoint_rho_plus_one)⁻¹ *
           deriv (fun s => fdBoundary_H H s - ellipticPoint_rho_plus_one) t
      else 0)
      (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi / 3))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  -- Choose ε₀
  set ε₀ := min (min (H - Real.sqrt 3 / 2) (2 * Real.sin (Real.pi / 12))) r with hε₀_def
  have hH_gap : 0 < H - Real.sqrt 3 / 2 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hε₀_pos : 0 < ε₀ := lt_min (lt_min hH_gap h2sin_pos) hr
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt_gap : ε < H - Real.sqrt 3 / 2 := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε_lt_r : ε < r := lt_of_lt_of_le hε_dist (min_le_right _ _)
  have hε_lt_one : ε < 1 := by
    have hsin_bound : Real.sin (Real.pi / 12) < 1 / 2 :=
      calc Real.sin (Real.pi / 12) < Real.sin (Real.pi / 6) :=
            Real.sin_lt_sin_of_lt_of_le_pi_div_two (by nlinarith [Real.pi_pos])
              (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        _ = 1 / 2 := by rw [Real.sin_pi_div_six]
    linarith
  -- Define g
  set g := fun t => fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ) with hg_def
  -- Define δ_L (seg0 side) and δ_R (arc side)
  set δ_L := ε / (H - Real.sqrt 3 / 2) with hδ_L_def
  set δ_R := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_R_def
  -- Useful positivity facts
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by
    have hsin_le : Real.sin (Real.pi / 12) ≤ 1 := Real.sin_le_one _
    linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- δ_L ∈ (0, 1)
  have hδ_L_pos : 0 < δ_L := div_pos hε_pos hH_gap
  have hδ_L_lt_one : δ_L < 1 := by
    rw [hδ_L_def, div_lt_one hH_gap]; linarith
  -- δ_R ∈ (0, 1)
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  have hδ_R_pos : 0 < δ_R := by
    rw [hδ_R_def]; exact mul_pos (div_pos (by norm_num) hpi_pos) harcsin_pos
  have hδ_R_lt_one : δ_R < 1 := by
    rw [hδ_R_def]
    have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
    have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
      calc Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) := by
            exact Real.arcsin_lt_arcsin hε_half_neg hε_lt_sin (Real.sin_le_one _)
          _ = Real.pi / 12 := by
            exact Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  -- Norm equality: ‖g(1-δ_L)‖ = ε
  have h_norm_L : ‖g (1 - δ_L)‖ = ε := by
    show ‖fdBoundary_H H (1 - δ_L) - ellipticPoint_rho_plus_one‖ = ε
    rw [g_rho'_norm_seg0_at hH hδ_L_pos (le_of_lt hδ_L_lt_one), hδ_L_def]
    field_simp
    have : H * 2 - Real.sqrt 3 > 0 := by nlinarith
    exact div_self (ne_of_gt this)
  -- Norm equality: ‖g(1+δ_R)‖ = ε
  have hδ_R_angle : δ_R * Real.pi / 12 = Real.arcsin (ε / 2) := by
    rw [hδ_R_def]; field_simp
  have h_norm_R : ‖g (1 + δ_R)‖ = ε := by
    show ‖fdBoundary_H H (1 + δ_R) - ellipticPoint_rho_plus_one‖ = ε
    rw [g_rho'_norm_arc hδ_R_pos (by linarith : δ_R < 2), hδ_R_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]
    linarith
  -- Get integrability from ftc_logDeriv_telescope_rho_plus_one
  have h_ftc := ftc_logDeriv_telescope_rho_plus_one H hH hδ_L_pos hδ_L_lt_one
    hδ_R_pos hδ_R_lt_one
  obtain ⟨hint_L, hint_R, h_telescope⟩ := h_ftc
  -- Norm bounds on each region
  have h_norm_gt_left : ∀ t ∈ Ioo (0 : ℝ) (1 - δ_L), ‖g t‖ > ε := by
    intro t ⟨ht0, ht1⟩
    rw [show g t = fdBoundary_H H t - ellipticPoint_rho_plus_one from rfl,
        g_rho'_norm_seg0 hH (le_of_lt ht0) (by linarith : t < 1)]
    rw [← h_norm_L, show g (1 - δ_L) = fdBoundary_H H (1 - δ_L) - ellipticPoint_rho_plus_one from rfl,
        g_rho'_norm_seg0_at hH hδ_L_pos (le_of_lt hδ_L_lt_one)]
    exact mul_lt_mul_of_pos_right (by linarith) hH_gap
  have h_norm_gt_right : ∀ t ∈ Ioo (1 + δ_R) (5 : ℝ), ‖g t‖ > ε := by
    intro t ⟨ht1, ht5⟩
    rcases le_or_lt t 3 with ht3 | ht3
    · rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · calc ε < 1 := hε_lt_one
          _ ≤ ‖g 3‖ := g_rho'_norm_ge_one_seg3 (le_refl 3) (by norm_num)
      · rw [show g t = fdBoundary_H H t - ellipticPoint_rho_plus_one from rfl,
            g_rho'_norm_arc_full (by linarith : 1 < t) ht3']
        rw [← h_norm_R, show g (1 + δ_R) = fdBoundary_H H (1 + δ_R) - ellipticPoint_rho_plus_one from rfl,
            g_rho'_norm_arc hδ_R_pos (by linarith : δ_R < 2)]
        have h_sin_mono : Real.sin (δ_R * Real.pi / 12) < Real.sin ((t - 1) * Real.pi / 12) :=
          Real.sin_lt_sin_of_lt_of_le_pi_div_two
            (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) (by nlinarith)
        linarith
    · rcases le_or_lt t 4 with ht4 | ht4
      · calc ε < 1 := hε_lt_one
          _ ≤ ‖g t‖ := g_rho'_norm_ge_one_seg3 (le_of_lt ht3) ht4
      · calc ε < H - Real.sqrt 3 / 2 := hε_lt_gap
          _ ≤ ‖g t‖ := g_rho'_norm_ge_seg4 hH (le_of_lt ht4) (le_of_lt ht5)
  have h_norm_le_middle : ∀ t, 1 - δ_L ≤ t → t ≤ 1 + δ_R → ¬(‖g t‖ > ε) := by
    intro t ht_lo ht_hi
    push_neg
    rcases le_or_lt t 1 with ht1 | ht1
    · rcases eq_or_lt_of_le ht1 with rfl | ht1'
      · simp only [show g 1 = fdBoundary_H H 1 - ellipticPoint_rho_plus_one from rfl,
          fdBoundary_H_at_one_eq_rho_plus_one, sub_self, norm_zero]
        exact le_of_lt hε_pos
      · rw [show g t = fdBoundary_H H t - ellipticPoint_rho_plus_one from rfl,
            g_rho'_norm_seg0 hH (by linarith) ht1']
        rw [← h_norm_L, show g (1 - δ_L) = fdBoundary_H H (1 - δ_L) - ellipticPoint_rho_plus_one from rfl,
            g_rho'_norm_seg0_at hH hδ_L_pos (le_of_lt hδ_L_lt_one)]
        exact mul_le_mul_of_nonneg_right (by linarith) (le_of_lt hH_gap)
    · rw [show g t = fdBoundary_H H t - ellipticPoint_rho_plus_one from rfl,
          g_rho'_norm_arc_full ht1 (by linarith : t < 3)]
      rw [← h_norm_R, show g (1 + δ_R) = fdBoundary_H H (1 + δ_R) - ellipticPoint_rho_plus_one from rfl,
          g_rho'_norm_arc hδ_R_pos (by linarith : δ_R < 2)]
      have h_angle_le : (t - 1) * Real.pi / 12 ≤ δ_R * Real.pi / 12 := by nlinarith
      exact mul_le_mul_of_nonneg_left
        (Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) h_angle_le)
        (by norm_num)
  -- Cutoff integrand
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ) with hF_def
  have hF_when_gt (t : ℝ) (h_gt : ‖g t‖ > ε) : F t = deriv g t / g t := by
    simp only [hF_def, if_pos h_gt, mul_comm (g t)⁻¹, div_eq_mul_inv]
  have hF_when_le (t : ℝ) (h_le : ¬(‖g t‖ > ε)) : F t = 0 := by
    simp only [hF_def, if_neg h_le]
  have hF_eq_left_ae : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (1 - δ_L) → F t = deriv g t / g t := by
    have : ({1 - δ_L} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : (0:ℝ) ≤ 1 - δ_L)] at ht_mem
    have ht_lt : t < 1 - δ_L := lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))
    exact hF_when_gt t (h_norm_gt_left t ⟨ht_mem.1, ht_lt⟩)
  have hF_int_left : IntervalIntegrable F volume 0 (1 - δ_L) :=
    hint_L.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_left_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_eq_right_ae : ∀ᵐ t ∂volume, t ∈ Ι (1 + δ_R) (5 : ℝ) → F t = deriv g t / g t := by
    have : ({5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : 1 + δ_R ≤ 5)] at ht_mem
    have ht_lt : t < 5 := lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))
    exact hF_when_gt t (h_norm_gt_right t ⟨ht_mem.1, ht_lt⟩)
  have hF_int_right : IntervalIntegrable F volume (1 + δ_R) 5 :=
    hint_R.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_right_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_eq_mid : ∀ t ∈ Ι (1 - δ_L) (1 + δ_R), F t = 0 := by
    intro t ht
    rw [uIoc_of_le (by linarith : 1 - δ_L ≤ 1 + δ_R)] at ht
    exact hF_when_le t (h_norm_le_middle t (le_of_lt ht.1) ht.2)
  have hF_int_mid : IntervalIntegrable F volume (1 - δ_L) (1 + δ_R) :=
    (IntervalIntegrable.zero (μ := volume) (a := 1 - δ_L) (b := 1 + δ_R)).congr
      (fun t ht => (hF_eq_mid t ht).symm)
  have h_adj1 := intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid
  have h_adj2 := intervalIntegral.integral_add_adjacent_intervals
    (hF_int_left.trans hF_int_mid) hF_int_right
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(1 - δ_L), F t) + (∫ t in (1 - δ_L)..(1 + δ_R), F t) +
      (∫ t in (1 + δ_R)..(5:ℝ), F t) := by
    rw [← h_adj2, ← h_adj1]
  have h_mid_zero : ∫ t in (1 - δ_L)..(1 + δ_R), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_eq_mid t ht))]
    simp [intervalIntegral.integral_zero]
  have h_left_eq : ∫ t in (0:ℝ)..(1 - δ_L), F t =
      ∫ t in (0:ℝ)..(1 - δ_L), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_eq_left_ae
  have h_right_eq : ∫ t in (1 + δ_R)..(5:ℝ), F t =
      ∫ t in (1 + δ_R)..(5:ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_eq_right_ae
  have h_int_eq : (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0:ℝ)..(1 - δ_L), deriv g t / g t) +
      (∫ t in (1 + δ_R)..(5:ℝ), deriv g t / g t) := by
    calc (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
        = ∫ t in (0:ℝ)..5, F t := rfl
      _ = ((∫ t in (0:ℝ)..(1 - δ_L), F t) + (∫ t in (1 - δ_L)..(1 + δ_R), F t)) +
          (∫ t in (1 + δ_R)..(5:ℝ), F t) := h_split
      _ = ((∫ t in (0:ℝ)..(1 - δ_L), F t) + 0) +
          (∫ t in (1 + δ_R)..(5:ℝ), F t) := by rw [h_mid_zero]
      _ = (∫ t in (0:ℝ)..(1 - δ_L), deriv g t / g t) +
          (∫ t in (1 + δ_R)..(5:ℝ), deriv g t / g t) := by rw [h_left_eq, h_right_eq, add_zero]
  -- The integral equals log(g(1-δ_L)) - log(g(1+δ_R)) by telescope
  rw [show dist (∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)‖ > ε
      then (fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ))⁻¹ *
           deriv (fun s => fdBoundary_H H s - (ellipticPoint_rho_plus_one : ℂ)) t
      else 0)
    (-(I * ↑Real.pi / 3)) =
    ‖(∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ)‖ > ε
      then (fdBoundary_H H t - (ellipticPoint_rho_plus_one : ℂ))⁻¹ *
           deriv (fun s => fdBoundary_H H s - (ellipticPoint_rho_plus_one : ℂ)) t
      else 0) -
    (-(I * ↑Real.pi / 3))‖ from Complex.dist_eq _ _]
  rw [h_int_eq, h_telescope]
  -- Decompose Complex.log
  set zL := fdBoundary_H H (1 - δ_L) - (ellipticPoint_rho_plus_one : ℂ)
  set zR := fdBoundary_H H (1 + δ_R) - (ellipticPoint_rho_plus_one : ℂ)
  have h_decomp_L := Complex.re_add_im (Complex.log zL)
  have h_decomp_R := Complex.re_add_im (Complex.log zR)
  rw [← h_decomp_L, ← h_decomp_R, Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im]
  change ‖zL‖ = ε at h_norm_L
  change ‖zR‖ = ε at h_norm_R
  rw [h_norm_L, h_norm_R]
  -- Use arg formulas
  rw [show zL.arg = (fdBoundary_H H (1 - δ_L) - ellipticPoint_rho_plus_one).arg from rfl,
      arg_approach_rho'_left hH hδ_L_pos (le_of_lt hδ_L_lt_one)]
  rw [show zR.arg = (fdBoundary_H H (1 + δ_R) - ellipticPoint_rho_plus_one).arg from rfl,
      arg_approach_rho'_right_helper hδ_R_pos (by linarith : δ_R < 2)]
  -- Simplify: (log ε + i π/2) - (log ε + i(5π/6 + δ_R π/12)) + iπ/3 = -i δ_R π/12
  have h_simp : ↑(Real.log ε) + ↑(Real.pi / 2) * I -
      (↑(Real.log ε) + ↑(5 * Real.pi / 6 + δ_R * Real.pi / 12) * I) - -(I * ↑Real.pi / 3) =
      ↑(-(δ_R * Real.pi / 12)) * I := by
    push_cast; ring
  rw [h_simp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by positivity)]
  -- Need: δ_R π/12 < ε < r
  have h_angle_bound : δ_R * Real.pi / 12 < ε := by
    have h2sin := g_rho'_norm_arc (H := H) hδ_R_pos (show δ_R < 2 by linarith)
    have h_norm_R' : ‖zR‖ = ε := h_norm_R
    rw [h_norm_R'] at h2sin
    have h_sin_eq : Real.sin (δ_R * Real.pi / 12) = ε / 2 := by linarith
    set x := δ_R * Real.pi / 12 with hx_def
    have hx_pos : 0 < x := by positivity
    have hx_le_one : x ≤ 1 := by
      have : x < Real.pi / 12 := by nlinarith
      linarith [Real.pi_le_four]
    have h_sin_lb := Real.sin_gt_sub_cube hx_pos hx_le_one
    have h_lb : x - x ^ 3 / 4 > x / 2 := by nlinarith [sq_nonneg x, sq_nonneg (1 - x)]
    linarith
  linarith

/-- `generalizedWindingNumber' (fdBoundary_H H) 0 5 ρ' = -1/6`. -/
theorem gWN_fdBoundary_H_at_rho_plus_one (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPoint_rho_plus_one = -1/6 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []
  simp only [sub_zero]
  have h_tendsto := pv_integral_at_rho_plus_one_tendsto H hH
  rw [h_tendsto.limUnder_eq]
  have h_pi_ne : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Real.pi_ne_zero, I_ne_zero]
  ring

/-! ### Section 5c: Infrastructure for the i Crossing at t = 2

The crossing at i happens at t = 2 on the arc. The PV integral should give -iπ, giving gWN' = -1/2.

Key geometry:
- g(t) = fdBoundary_H H t - I
- On seg0 (t ∈ [0,1]): g(t) = 1/2 + (H - t(H-√3/2) - 1)I, re = 1/2 > 0
- On seg1 (t ∈ (1,2)): g(t) = exp(iπ(1+t)/6) - I, re > 0 (since θ ∈ (π/3,π/2))
- On seg2 (t ∈ (2,3)): g(t) = exp(iπ(1+t)/6) - I, im < 0 and re < 0
- On seg3 (t ∈ (3,4)): g(t) = -1/2 + (√3/2-1 + (t-3)(H-√3/2))I, branch cut at t₀
- On seg4 (t ∈ (4,5)): g(t) = (t-9/2) + (H-1)I, im = H-1 > 0

Factorizations near t = 2:
- g(2-δ) = 2sin(δπ/12)·exp(-iδπ/12), arg = -δπ/12
- g(2+δ) = 2sin(δπ/12)·exp(i(δπ/12-π)), arg = δπ/12 - π
- ‖g(2±δ)‖ = 2sin(δπ/12) (symmetric!)

The FTC telescope gives log(g(2-δ)) - log(g(2+δ)) - 2πi (branch cut on seg3),
which simplifies to i(π - δπ/6) - 2πi = -iπ - iδπ/6 → -iπ.
-/

/-- Arg of g(2-δ) = fdBoundary_H H (2-δ) - I for small δ > 0.
On the arc, g(2-δ) = 2sin(δπ/12)·exp(-iδπ/12), so arg = -δπ/12. -/
private lemma arg_approach_i_left (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (2 - δ) - I).arg = -(δ * Real.pi / 12) := by
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ from by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, exp_real_angle_I]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_pi_div_two_sub]
  have h_re_factor : Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  -- g(2-δ) = 2sin(δπ/12) · (cos(δπ/12) - sin(δπ/12)·I)
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      ↑(2 * Real.sin (δ * Real.pi / 12)) *
        (↑(Real.cos (δ * Real.pi / 12)) + ↑(-(Real.sin (δ * Real.pi / 12))) * I) := by
    rw [h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq]
  -- Convert ↑(Real.cos/sin ...) to Complex.cos/sin ↑(...)
  have h_trig : (↑(Real.cos (δ * Real.pi / 12)) : ℂ) +
      ↑(-(Real.sin (δ * Real.pi / 12))) * I =
      Complex.cos ↑(-(δ * Real.pi / 12)) + Complex.sin ↑(-(δ * Real.pi / 12)) * I := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, ofReal_neg]
  rw [h_trig]
  exact Complex.arg_mul_cos_add_sin_mul_I
    (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos)
    ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩

/-- Arg of g(2+δ) = fdBoundary_H H (2+δ) - I for small δ > 0.
On the arc, g(2+δ) = 2sin(δπ/12)·exp(i(δπ/12-π)), so arg = δπ/12 - π. -/
private lemma arg_approach_i_right (hδ : 0 < δ) (hδ_small : δ < 1) :
    (fdBoundary_H H (2 + δ) - I).arg = δ * Real.pi / 12 - Real.pi := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ from by simp only [hθ_def]; ring]
  rw [show (↑θ : ℂ) * I = ↑θ * I from rfl, exp_real_angle_I]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re_factor : -Real.sin (δ * Real.pi / 6) =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  -- g(2+δ) = -(2sin(δπ/12))·(cos(δπ/12) + sin(δπ/12)I)
  set w := (↑(Real.cos (δ * Real.pi / 12)) : ℂ) + ↑(Real.sin (δ * Real.pi / 12)) * I with hw_def
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      -(↑(2 * Real.sin (δ * Real.pi / 12)) * w) := by
    rw [h_cos, h_sin]
    apply Complex.ext
    · simp only [hw_def, add_re, sub_re, neg_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [hw_def, add_im, sub_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq]
  -- w has im > 0 (sin(δπ/12) > 0)
  have hw_im_pos : 0 < w.im := by
    simp only [hw_def, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, add_zero, mul_one]
    linarith
  -- Compute arg(w) = δπ/12 using arg_mul_cos_add_sin_mul_I
  have hw_arg : w.arg = δ * Real.pi / 12 := by
    have hw_eq : w = ↑(1:ℝ) * (Complex.cos ↑(δ * Real.pi / 12) +
        Complex.sin ↑(δ * Real.pi / 12) * I) := by
      simp only [hw_def, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_one, one_mul]
    rw [hw_eq]
    exact Complex.arg_mul_cos_add_sin_mul_I (by norm_num : (0:ℝ) < 1)
      ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  -- ↑(2sin) * w has im > 0 since 2sin > 0 and w.im > 0
  have hrw_im_pos : 0 < (↑(2 * Real.sin (δ * Real.pi / 12)) * w).im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    simp only [zero_mul, add_zero]
    exact mul_pos (mul_pos (by norm_num) h_sin_pos) hw_im_pos
  -- arg(-(↑r * w)) = arg(↑r * w) - π, then arg(↑r * w) = arg(w) = δπ/12
  rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos hrw_im_pos,
      Complex.arg_real_mul w (mul_pos (by norm_num : (0:ℝ) < 2) h_sin_pos),
      hw_arg]

/-- Norm of g(2-δ) on the arc (left of i): ‖γ(2-δ) - I‖ = 2sin(δπ/12). -/
private lemma g_i_norm_left {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (2 - δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  -- Use the arg factorization: g(2-δ) = 2sin(δπ/12) · exp(-iδπ/12)
  -- So ‖g‖ = 2sin(δπ/12) · 1 = 2sin(δπ/12)
  have h1 : 1 < 2 - δ := by linarith
  have h3 : 2 - δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, exp_real_angle_I]
  set θ := Real.pi / 2 - δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 - δ)) / 6 = θ from by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_pi_div_two_sub]
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_pi_div_two_sub]
  have h_re_factor : Real.sin (δ * Real.pi / 6) =
      2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  -- g = 2sin(δπ/12) · exp(-iδπ/12)
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (2 * Real.sin (δ * Real.pi / 12)) • Complex.exp (↑(-(δ * Real.pi / 12)) * I) := by
    rw [Complex.real_smul, exp_real_angle_I, Real.cos_neg, Real.sin_neg, h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_of_nonneg (by linarith)]

/-- Norm of g(2+δ) on the arc (right of i): ‖γ(2+δ) - I‖ = 2sin(δπ/12). -/
private lemma g_i_norm_right {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ‖fdBoundary_H H (2 + δ) - I‖ = 2 * Real.sin (δ * Real.pi / 12) := by
  have h1 : 1 < 2 + δ := by linarith
  have h3 : 2 + δ < 3 := by linarith
  rw [fdBoundary_H_eq_arc h1 h3, exp_real_angle_I]
  set θ := Real.pi / 2 + δ * Real.pi / 6 with hθ_def
  rw [show Real.pi * (1 + (2 + δ)) / 6 = θ from by simp only [hθ_def]; ring]
  have h_cos : Real.cos θ = -Real.sin (δ * Real.pi / 6) := by
    rw [hθ_def, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]; ring
  have h_sin : Real.sin θ = Real.cos (δ * Real.pi / 6) := by
    rw [hθ_def, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]; ring
  have h_re_factor : -Real.sin (δ * Real.pi / 6) =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.cos (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.sin_two_mul]
  have h_im_factor : Real.cos (δ * Real.pi / 6) - 1 =
      -(2 * Real.sin (δ * Real.pi / 12) * Real.sin (δ * Real.pi / 12)) := by
    rw [show δ * Real.pi / 6 = 2 * (δ * Real.pi / 12) from by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (δ * Real.pi / 12)]
  have h_sin_pos : 0 < Real.sin (δ * Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  -- g = -(2sin(δπ/12)) · exp(iδπ/12) = 2sin(δπ/12) · exp(i(δπ/12 - π))
  -- |g| = 2sin(δπ/12) · |exp| = 2sin(δπ/12)
  have h_eq : ↑(Real.cos θ) + ↑(Real.sin θ) * I - I =
      (-(2 * Real.sin (δ * Real.pi / 12))) • Complex.exp (↑(δ * Real.pi / 12) * I) := by
    rw [Complex.real_smul, exp_real_angle_I, h_cos, h_sin]
    apply Complex.ext
    · simp only [add_re, sub_re, neg_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_zero, add_zero, mul_one]; linarith [h_re_factor]
    · simp only [add_im, sub_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, add_zero, mul_one, zero_add]; linarith [h_im_factor]
  rw [h_eq, norm_smul, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by linarith)]

/-- Norm of g on seg0: ‖γ(t) - I‖ ≥ 1/2 (from re = 1/2). -/
private lemma g_i_norm_ge_seg0 {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    1 / 2 ≤ ‖fdBoundary_H H t - I‖ := by
  have hre : (fdBoundary_H H t - I).re = 1 / 2 := by
    rw [fdBoundary_H_seg0 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, add_zero, mul_one]
    norm_num
  calc (1 : ℝ) / 2 = |1 / 2| := (abs_of_pos (by norm_num)).symm
    _ = |(fdBoundary_H H t - I).re| := by rw [hre]
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_re_le_norm _

/-- Norm of g on seg4: ‖γ(t) - I‖ ≥ H - 1 > 0 (from im = H - 1). -/
private lemma g_i_norm_ge_seg4 (H : ℝ) (hH : 1 < H)
    {t : ℝ} (ht4 : 4 ≤ t) (ht5 : t ≤ 5) :
    H - 1 ≤ ‖fdBoundary_H H t - I‖ := by
  have him : (fdBoundary_H H t - I).im = H - 1 := by
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [fdBoundary_H_at_four H]
      simp only [Complex.neg_im, Complex.div_ofNat_im, Complex.one_im, Complex.add_im,
        Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.sub_im,
        Complex.ofReal_re]
      ring
    · rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
      simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
        Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.div_ofNat_im, Complex.im_ofNat]
      ring
  calc H - 1 = |H - 1| := (abs_of_pos (by linarith)).symm
    _ = |(fdBoundary_H H t - I).im| := by rw [him]
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_im_le_norm _

/-- On seg0 and seg1, g(t) - I ∈ slitPlane (re > 0). -/
private lemma g_i_slitPlane_left {t : ℝ} (_ht0 : 0 ≤ t) (ht2 : t < 2) :
    fdBoundary_H H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rcases le_or_gt t 1 with ht1 | ht1
  · rw [fdBoundary_H_seg0 H ht1]
    simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.div_ofNat_re,
      mul_zero, sub_zero, zero_mul, mul_one]
    norm_num
  · rw [fdBoundary_H_seg1 H (by linarith) (by linarith)]
    set θ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
    rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      (↑θ : ℂ) * I from by simp only [hθ_def]; push_cast; ring, exp_real_angle_I]
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, add_zero,
      mul_one]
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · simp only [hθ_def]; nlinarith [Real.pi_pos]
    · simp only [hθ_def]; nlinarith [Real.pi_pos]

/-- g(t)-I on seg3: value is -1/2 + (√3/2-1+(t-3)(H-√3/2))I -/
private lemma g_i_seg3_value {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - I = -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I := by
  rw [fdBoundary_H_seg3 H (by linarith) (by linarith) (by linarith) ht4]
  push_cast; ring

/-- g(t)-I on seg4: value is (t-9/2)+(H-1)I -/
private lemma g_i_seg4_value {t : ℝ} (ht4 : 4 < t) :
    fdBoundary_H H t - I = ↑(t - 9/2) + ↑(H - 1) * I := by
  rw [fdBoundary_H_seg4 H (by linarith) (by linarith) (by linarith) (by linarith)]
  push_cast; ring

/-- ‖g‖ ≥ 1/2 on seg3 (re = -1/2). -/
private lemma g_i_norm_ge_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    1 / 2 ≤ ‖fdBoundary_H H t - I‖ := by
  have hre : (fdBoundary_H H t - I).re = -1 / 2 := by
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [fdBoundary_H_at_three_eq_rho]
      simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype,
        Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
        Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_mul, zero_div]
      norm_num
    · rw [g_i_seg3_value ht3' ht4]
      simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, sub_zero, add_zero, zero_mul]
  calc 1 / 2 = |(-1:ℝ) / 2| := by norm_num
    _ = |(fdBoundary_H H t - I).re| := by rw [hre]
    _ ≤ ‖fdBoundary_H H t - I‖ := Complex.abs_re_le_norm _

/-- g ∈ slitPlane on arc after i (t ∈ (2, 3]): im < 0 hence im ≠ 0. -/
private lemma g_i_slitPlane_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t ≤ 3) :
    fdBoundary_H H t - I ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho]
    simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype,
      Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.div_ofNat_im, Complex.div_ofNat_re,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_add, mul_one, zero_mul,
      zero_div]
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num), sq_nonneg (2 - Real.sqrt 3)]
  · rw [fdBoundary_H_eq_arc (by linarith) ht3', exp_real_angle_I]
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one, zero_add]
    have hθ_bound : Real.pi / 2 < Real.pi * (1 + t) / 6 := by nlinarith [Real.pi_pos]
    have hθ_bound2 : Real.pi * (1 + t) / 6 < Real.pi + Real.pi / 2 := by nlinarith [Real.pi_pos]
    have h_cos_neg := Real.cos_neg_of_pi_div_two_lt_of_lt hθ_bound hθ_bound2
    have h_sin_lt : Real.sin (Real.pi * (1 + t) / 6) < 1 := by
      by_contra h_ge; push_neg at h_ge
      have h_eq := le_antisymm (Real.sin_le_one _) h_ge
      have : Real.cos (Real.pi * (1 + t) / 6) = 0 := by
        nlinarith [Real.sin_sq_add_cos_sq (Real.pi * (1 + t) / 6)]
      linarith
    linarith

/-- Norm on arc right of i: ‖g(t)‖ = 2sin((t-2)π/12) for t ∈ (2, 3). -/
private lemma g_i_norm_arc_right {t : ℝ} (ht2 : 2 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((t - 2) * Real.pi / 12) := by
  have h := g_i_norm_right (H := H) (δ := t - 2) (by linarith) (by linarith)
  rwa [show 2 + (t - 2) = t from by ring] at h

/-- Norm on arc left of i: ‖g(t)‖ = 2sin((2-t)π/12) for t ∈ (1, 2). -/
private lemma g_i_norm_arc_left {t : ℝ} (ht1 : 1 < t) (ht2 : t < 2) :
    ‖fdBoundary_H H t - I‖ = 2 * Real.sin ((2 - t) * Real.pi / 12) := by
  have h := g_i_norm_left (H := H) (δ := 2 - t) (by linarith) (by linarith)
  rwa [show 2 - (2 - t) = t from by ring] at h

/-- The branch-cut crossing point on seg3. -/
private noncomputable def t₀_i (H : ℝ) : ℝ := 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2)

private lemma t₀_i_gt_three (hH : 1 < H) : 3 < t₀_i H := by
  unfold t₀_i
  have h_num_pos : 0 < 1 - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by nlinarith
  linarith [div_pos h_num_pos h_den_pos]

private lemma t₀_i_lt_four (hH : 1 < H) : t₀_i H < 4 := by
  unfold t₀_i
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  rw [show (4:ℝ) = 3 + 1 from by ring]
  have : (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 := by
    rw [div_lt_one h_den_pos]; linarith
  linarith

private lemma g_i_at_t₀ (hH : 1 < H) :
    fdBoundary_H H (t₀_i H) - I = -1/2 := by
  have ht₀3 := t₀_i_gt_three hH
  have ht₀4 := t₀_i_lt_four hH
  rw [g_i_seg3_value (by linarith) (by linarith)]
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_im_zero : Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
    unfold t₀_i
    rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
      (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring
  rw [h_im_zero]; simp

/-- im of g on seg3 is < 0 for t ∈ (3, t₀). -/
private lemma g_i_seg3_im_neg {t : ℝ} (ht3 : 3 < t) (ht_t0 : t < t₀_i H)
    (hH : 1 < H) : (fdBoundary_H H t - I).im < 0 := by
  rw [g_i_seg3_value ht3 (by linarith [t₀_i_lt_four hH])]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, zero_add, mul_one]
  norm_num
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_eq_zero : Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
    unfold t₀_i
    rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
      (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring
  nlinarith

/-- im of g on seg3 is > 0 for t ∈ (t₀, 4]. -/
private lemma g_i_seg3_im_pos {t : ℝ} (ht_t0 : t₀_i H < t) (ht4 : t ≤ 4)
    (hH : 1 < H) : 0 < (fdBoundary_H H t - I).im := by
  rw [g_i_seg3_value (by linarith [t₀_i_gt_three hH]) ht4]
  simp only [Complex.add_im, Complex.neg_im, Complex.div_ofNat_im, Complex.one_im,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, add_zero, zero_add, mul_one]
  norm_num
  have h_den_pos : 0 < H - Real.sqrt 3 / 2 := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have h_eq_zero : Real.sqrt 3 / 2 - 1 + (t₀_i H - 3) * (H - Real.sqrt 3 / 2) = 0 := by
    unfold t₀_i
    rw [show 3 + (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) - 3 =
      (1 - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) from by ring]
    rw [div_mul_cancel₀ _ (ne_of_gt h_den_pos)]; ring
  nlinarith

/-- g ≠ 0 on seg3 (re = -1/2). -/
private lemma g_i_ne_zero_seg3 {t : ℝ} (ht3 : 3 ≤ t) (ht4 : t ≤ 4) :
    fdBoundary_H H t - I ≠ 0 := by
  intro h; have := congr_arg Complex.re h
  simp only [Complex.zero_re] at this
  rcases eq_or_lt_of_le ht3 with rfl | ht3'
  · rw [fdBoundary_H_at_three_eq_rho] at this
    simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype,
      Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.div_ofNat_re,
      Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_mul] at this
    norm_num at this
  · rw [g_i_seg3_value ht3' ht4] at this
    simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, sub_zero, add_zero, zero_mul] at this
    norm_num at this

/-- log(-z) = log(z) + πI when z.im < 0. -/
private lemma log_neg_eq_add_pi_I {z : ℂ} (_hz_ne : z ≠ 0) (hz_im : z.im < 0) :
    Complex.log (-z) = Complex.log z + ↑Real.pi * I := by
  show ↑(Real.log ‖-z‖) + ↑((-z).arg) * I = ↑(Real.log ‖z‖) + ↑z.arg * I + ↑Real.pi * I
  simp only [map_neg, norm_neg]
  rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg hz_im]
  push_cast; ring

set_option maxHeartbeats 16000000 in
/-- FTC telescope for the logDeriv integral near i.

For δ ∈ (0, 1), the sum of logDeriv integrals on [0, 2-δ] and [2+δ, 5]
telescopes to `log(g(2-δ)) - log(g(2+δ)) - 2πI`, using FTC on 6 smooth segments
and a branch-cut correction of -2πI from the crossing at t₀ on seg3. -/
private lemma ftc_logDeriv_telescope_i (H : ℝ) (hH : 1 < H)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let g := fun t => fdBoundary_H H t - I
    IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 ∧
    ((∫ t in (0:ℝ)..(2 - δ), deriv g t / g t) +
    (∫ t in (2 + δ)..(5:ℝ), deriv g t / g t) =
    Complex.log (g (2 - δ)) - Complex.log (g (2 + δ)) - 2 * ↑Real.pi * I) := by
  intro g
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  set t₀ := t₀_i H with ht₀_def
  have ht₀3 := t₀_i_gt_three hH
  have ht₀4 := t₀_i_lt_four hH
  -- Smooth representatives
  set h₀ : ℝ → ℂ := fun t => 1/2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2) - 1) * I
  set h₁ : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - I
  set h₂ : ℝ → ℂ := fun t => -1/2 + ↑(Real.sqrt 3 / 2 - 1 + (t - 3) * (H - Real.sqrt 3 / 2)) * I
  set h₃ : ℝ → ℂ := fun t => ↑(t - 9/2) + ↑(H - 1) * I
  -- Value agreement
  have hg_eq_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; show fdBoundary_H H t - I = h₀ t
    rw [fdBoundary_H_seg0 H ht]; simp only [h₀]; push_cast; ring
  have hg_eq_h₁ : ∀ t, 1 < t → t < 3 → g t = h₁ t := by
    intro t ht1 ht3; show fdBoundary_H H t - I = h₁ t
    rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_eq_h₂ : ∀ t, 3 < t → t ≤ 4 → g t = h₂ t := by
    intro t ht3 ht4; exact g_i_seg3_value ht3 ht4
  have hg_eq_h₃ : ∀ t, 4 < t → g t = h₃ t := by
    intro t ht4; exact g_i_seg4_value ht4
  -- Endpoint values
  have hg0 : g 0 = h₀ 0 := hg_eq_h₀ 0 (by norm_num)
  have hg1_0 : g 1 = h₀ 1 := hg_eq_h₀ 1 (le_refl 1)
  have hg1_1 : g 1 = h₁ 1 := by
    show fdBoundary_H H 1 - I = h₁ 1
    rw [fdBoundary_H_at_one_eq_rho_plus_one]
    simp only [h₁, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one',
      UpperHalfPlane.coe_mk_subtype]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        show (↑(Real.pi / 3) : ℂ) * I = ↑(Real.pi / 3) * I from rfl,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hg2mδ : g (2 - δ) = h₁ (2 - δ) := hg_eq_h₁ (2 - δ) (by linarith) (by linarith)
  have hg2pδ : g (2 + δ) = h₁ (2 + δ) := hg_eq_h₁ (2 + δ) (by linarith) (by linarith)
  have hg3_1 : g 3 = h₁ 3 := by
    show fdBoundary_H H 3 - I = h₁ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₁, ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring]
    rw [show (↑(2 * Real.pi / 3) : ℂ) * I = ↑(2 * Real.pi / 3) * I from rfl,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hg3_2 : g 3 = h₂ 3 := by
    show fdBoundary_H H 3 - I = h₂ 3
    rw [fdBoundary_H_at_three_eq_rho]
    simp only [h₂, ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
    push_cast; ring
  have hgt₀_2 : g t₀ = h₂ t₀ := hg_eq_h₂ t₀ ht₀3 (le_of_lt ht₀4)
  have hgt₀_val : g t₀ = (-1 : ℂ) / 2 := g_i_at_t₀ hH
  have hg4_2 : g 4 = h₂ 4 := hg_eq_h₂ 4 (by linarith) (le_refl 4)
  have hg4_3 : g 4 = h₃ 4 := by
    show fdBoundary_H H 4 - I = h₃ 4
    rw [fdBoundary_H_at_four H]; simp only [h₃]; push_cast; ring
  have hg5 : g 5 = h₃ 5 := hg_eq_h₃ 5 (by norm_num)
  -- HasDerivAt
  have hd_h₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; simp only [h₀]
    have ht := (hasDerivAt_id t).ofReal_comp.mul_const (↑H - ↑(Real.sqrt 3) / 2 : ℂ)
    have hinner := ((hasDerivAt_const t (↑H : ℂ)).sub ht).sub (hasDerivAt_const t (1:ℂ))
    exact ((hasDerivAt_const t ((1:ℂ)/2)).add (hinner.mul_const I)).congr_deriv
      (by push_cast; ring)
  have hd_h₁ : ∀ t : ℝ, HasDerivAt h₁
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
    intro t
    have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
      ((hasDerivAt_id t).add_const (1:ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
        (Eventually.of_forall fun s => show _ from by simp [id]; ring)
        |>.congr_deriv (by ring)
    have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
        ((↑(Real.pi / 6) : ℂ) * I) t :=
      (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
    exact (hci.cexp.sub (hasDerivAt_const t I)).congr_deriv (by simp only [sub_zero]; ring)
  have hd_h₂ : ∀ t : ℝ, HasDerivAt h₂ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; simp only [h₂]
    have hf : HasDerivAt (fun s : ℝ => Real.sqrt 3 / 2 - 1 + (s - 3) * (H - Real.sqrt 3 / 2))
        (H - Real.sqrt 3 / 2) t :=
      ((hasDerivAt_id t).sub_const (3:ℝ) |>.mul_const (H - Real.sqrt 3 / 2)
        |>.add_const (Real.sqrt 3 / 2 - 1)).congr_of_eventuallyEq
        (Eventually.of_forall fun s => show _ from by simp [id]; ring)
        |>.congr_deriv (by ring)
    exact ((hasDerivAt_const t ((-1:ℂ)/2)).add
      (hf.ofReal_comp.mul_const I)).congr_deriv (by push_cast; ring)
  have hd_h₃ : ∀ t : ℝ, HasDerivAt h₃ 1 t := by
    intro t
    show HasDerivAt (fun s => ↑(s - 9/2) + ↑(H - 1) * I) (1 : ℂ) t
    have h1 : HasDerivAt (fun s : ℝ => s - 9/2) (1 : ℝ) t := by
      have := (hasDerivAt_id t).sub (hasDerivAt_const t (9/2:ℝ))
      convert this using 1
      ring
    have h2 := h1.ofReal_comp.add (hasDerivAt_const t (↑(H - 1) * I))
    exact h2.congr_deriv (by simp [sub_zero])
  -- Derivative agreement
  have heq_01 : ∀ t ∈ Ioo (0:ℝ) 1, g t = h₀ t ∧ deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    refine ⟨hg_eq_h₀ t (le_of_lt ht1), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Iio_mem_nhds ht1)
      (fun s hs => hg_eq_h₀ s (le_of_lt hs)))
  have heq_1_2mδ : ∀ t ∈ Ioo (1:ℝ) (2 - δ), g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht1, ht2⟩
    refine ⟨hg_eq_h₁ t ht1 (by linarith), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht1 (show t < 3 by linarith))
      (fun s hs => hg_eq_h₁ s hs.1 hs.2))
  have heq_2pδ_3 : ∀ t ∈ Ioo (2 + δ) (3:ℝ), g t = h₁ t ∧ deriv g t = deriv h₁ t := by
    intro t ⟨ht2, ht3⟩
    refine ⟨hg_eq_h₁ t (by linarith) ht3, ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds (show 1 < t by linarith) ht3)
      (fun s hs => hg_eq_h₁ s hs.1 hs.2))
  have heq_3_t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht3, ht_t0⟩
    refine ⟨hg_eq_h₂ t ht3 (by linarith), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht3 (show t < 4 by linarith))
      (fun s hs => hg_eq_h₂ s hs.1 (le_of_lt hs.2)))
  have heq_t₀_4 : ∀ t ∈ Ioo t₀ (4:ℝ), g t = h₂ t ∧ deriv g t = deriv h₂ t := by
    intro t ⟨ht_t0, ht4⟩
    refine ⟨hg_eq_h₂ t (by linarith) (le_of_lt ht4), ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds (show 3 < t by linarith) ht4)
      (fun s hs => hg_eq_h₂ s hs.1 (le_of_lt hs.2)))
  have heq_45 : ∀ t ∈ Ioo (4:ℝ) 5, g t = h₃ t ∧ deriv g t = deriv h₃ t := by
    intro t ⟨ht4, _⟩
    refine ⟨hg_eq_h₃ t ht4, ?_⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_eq_h₃ s hs))
  -- ContinuousOn from HasDerivAt
  have hh₀_cont : ContinuousOn h₀ (Icc 0 1) :=
    fun t _ => (hd_h₀ t).continuousAt.continuousWithinAt
  have hh₁_cont_12 : ContinuousOn h₁ (Icc 1 (2 - δ)) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₁_cont_23 : ContinuousOn h₁ (Icc (2 + δ) 3) :=
    fun t _ => (hd_h₁ t).continuousAt.continuousWithinAt
  have hh₂_cont_3t₀ : ContinuousOn h₂ (Icc 3 t₀) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₂_cont_t₀4 : ContinuousOn h₂ (Icc t₀ 4) :=
    fun t _ => (hd_h₂ t).continuousAt.continuousWithinAt
  have hh₃_cont : ContinuousOn h₃ (Icc 4 5) :=
    fun t _ => (hd_h₃ t).continuousAt.continuousWithinAt
  -- DifferentiableAt from HasDerivAt
  have hh₀_diff : ∀ t ∈ Ioo (0:ℝ) 1, DifferentiableAt ℝ h₀ t :=
    fun t _ => (hd_h₀ t).differentiableAt
  have hh₁_diff_12 : ∀ t ∈ Ioo (1:ℝ) (2 - δ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₁_diff_23 : ∀ t ∈ Ioo (2 + δ) (3:ℝ), DifferentiableAt ℝ h₁ t :=
    fun t _ => (hd_h₁ t).differentiableAt
  have hh₂_diff_3t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₂_diff_t₀4 : ∀ t ∈ Ioo t₀ (4:ℝ), DifferentiableAt ℝ h₂ t :=
    fun t _ => (hd_h₂ t).differentiableAt
  have hh₃_diff : ∀ t ∈ Ioo (4:ℝ) 5, DifferentiableAt ℝ h₃ t :=
    fun t _ => (hd_h₃ t).differentiableAt
  -- Derivative continuity
  have hh₀_deriv_cont : ContinuousOn (deriv h₀) (Icc 0 1) := by
    rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₀ t).deriv]; exact continuousOn_const
  have hh₁_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₁) (Icc a b) := by
    intro a b
    rw [show deriv h₁ = fun t => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I) from
      funext fun t => (hd_h₁ t).deriv]
    exact (Continuous.mul continuous_const (Continuous.cexp (Continuous.mul
      (continuous_ofReal.comp (by fun_prop : Continuous fun s => Real.pi * (1 + s) / 6))
      continuous_const))).continuousOn
  have hh₂_deriv_cont : ∀ (a b : ℝ), ContinuousOn (deriv h₂) (Icc a b) := by
    intro a b
    rw [show deriv h₂ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
      funext fun t => (hd_h₂ t).deriv]; exact continuousOn_const
  have hh₃_deriv_cont : ContinuousOn (deriv h₃) (Icc 4 5) := by
    rw [show deriv h₃ = fun _ => (1 : ℂ) from
      funext fun t => (hd_h₃ t).deriv]; exact continuousOn_const
  -- Piece 0: [0, 1] — ftc_log_piece (slitPlane)
  have hh₀_slit : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ slitPlane := by
    intro t ⟨ht0, ht1⟩; rw [← hg_eq_h₀ t ht1]
    exact g_i_slitPlane_left ht0 (by linarith)
  have piece₀ := ftc_log_piece (by norm_num : (0:ℝ) ≤ 1) hh₀_cont hh₀_diff
    hh₀_deriv_cont hh₀_slit heq_01 hg0 hg1_0
  -- Piece 1: [1, 2-δ] — ftc_log_piece (slitPlane)
  have hh₁_slit_12 : ∀ t ∈ Icc (1:ℝ) (2 - δ), h₁ t ∈ slitPlane := by
    intro t ⟨ht1, ht2⟩
    rcases eq_or_lt_of_le ht1 with rfl | ht1'
    · rw [← hg1_1]; exact g_i_slitPlane_left (by norm_num) (by linarith)
    · rw [← hg_eq_h₁ t ht1' (by linarith)]
      exact g_i_slitPlane_left (by linarith) (by linarith)
  have piece₁ := ftc_log_piece (by linarith : (1:ℝ) ≤ 2 - δ) hh₁_cont_12 hh₁_diff_12
    (hh₁_deriv_cont 1 (2-δ)) hh₁_slit_12 heq_1_2mδ hg1_1 hg2mδ
  -- Piece 2: [2+δ, 3] — ftc_log_piece (slitPlane, im < 0)
  have hh₁_slit_23 : ∀ t ∈ Icc (2 + δ) (3:ℝ), h₁ t ∈ slitPlane := by
    intro t ⟨ht2, ht3⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [← hg3_1]; exact g_i_slitPlane_arc_right (by linarith) (le_refl 3)
    · rw [← hg_eq_h₁ t (by linarith) ht3']
      exact g_i_slitPlane_arc_right (by linarith) (le_of_lt ht3')
  have piece₂ := ftc_log_piece (by linarith : (2 + δ) ≤ 3) hh₁_cont_23 hh₁_diff_23
    (hh₁_deriv_cont (2+δ) 3) hh₁_slit_23 heq_2pδ_3 hg2pδ hg3_1
  -- Piece 3: [3, t₀] — ftc_log_piece_lower (im ≤ 0)
  have hh₂_im_np_3t₀ : ∀ t ∈ Icc (3:ℝ) t₀, (h₂ t).im ≤ 0 := by
    intro t ⟨ht3, ht_t0⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · show (h₂ 3).im ≤ 0
      simp only [h₂, Complex.add_im, Complex.neg_im, Complex.div_ofNat_im,
        Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_add, mul_one]
      nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
                sq_nonneg (2 - Real.sqrt 3)]
    · rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
      · show (h₂ t₀).im ≤ 0
        rw [← hg_eq_h₂ t₀ (by linarith [t₀_i_gt_three hH]) (by linarith [t₀_i_lt_four hH]), hgt₀_val]
        simp
      · show (h₂ t).im ≤ 0
        rw [← hg_eq_h₂ t ht3' (by linarith)]
        exact le_of_lt (g_i_seg3_im_neg ht3' ht_t0' hH)
  have hh₂_ne_3t₀ : ∀ t ∈ Icc (3:ℝ) t₀, h₂ t ≠ 0 := by
    intro t ⟨ht3, ht_t0⟩
    rcases eq_or_lt_of_le ht3 with rfl | ht3'
    · rw [← hg3_2]; exact g_i_ne_zero_seg3 (le_refl 3) (by linarith)
    · rw [← hg_eq_h₂ t ht3' (by linarith)]
      exact g_i_ne_zero_seg3 (by linarith) (by linarith)
  have hh₂_im_neg_int_3t₀ : ∀ t ∈ Ioo (3:ℝ) t₀, (h₂ t).im < 0 := by
    intro t ⟨ht3, ht_t0⟩
    rw [← hg_eq_h₂ t ht3 (by linarith)]
    exact g_i_seg3_im_neg ht3 ht_t0 hH
  have piece₃ := ftc_log_piece_lower (by linarith : (3:ℝ) ≤ t₀)
    hh₂_cont_3t₀ hh₂_diff_3t₀ (hh₂_deriv_cont 3 t₀) hh₂_im_np_3t₀ hh₂_ne_3t₀
    hh₂_im_neg_int_3t₀ heq_3_t₀ hg3_2 hgt₀_2
  -- Piece 4: [t₀, 4] — ftc_log_piece_upper (im ≥ 0)
  have hh₂_im_nn_t₀4 : ∀ t ∈ Icc t₀ (4:ℝ), 0 ≤ (h₂ t).im := by
    intro t ⟨ht_t0, ht4⟩
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [← hgt₀_2, hgt₀_val]; simp
    · rw [← hg_eq_h₂ t (by linarith) ht4]
      exact le_of_lt (g_i_seg3_im_pos ht_t0' ht4 hH)
  have hh₂_ne_t₀4 : ∀ t ∈ Icc t₀ (4:ℝ), h₂ t ≠ 0 := by
    intro t ⟨ht_t0, ht4⟩
    rcases eq_or_lt_of_le ht_t0 with rfl | ht_t0'
    · rw [← hgt₀_2]; exact g_i_ne_zero_seg3 (by linarith) (by linarith)
    · rw [← hg_eq_h₂ t (by linarith) ht4]
      exact g_i_ne_zero_seg3 (by linarith) ht4
  have hh₂_slit_int_t₀4 : ∀ t ∈ Ioo t₀ (4:ℝ), h₂ t ∈ slitPlane := by
    intro t ⟨ht_t0, ht4⟩
    rw [← hg_eq_h₂ t (by linarith) (le_of_lt ht4)]
    rw [Complex.mem_slitPlane_iff]; right
    exact ne_of_gt (g_i_seg3_im_pos ht_t0 (le_of_lt ht4) hH)
  have piece₄ := ftc_log_piece_upper (by linarith : t₀ ≤ 4)
    hh₂_cont_t₀4 hh₂_diff_t₀4 (hh₂_deriv_cont t₀ 4)
    hh₂_im_nn_t₀4 hh₂_ne_t₀4 hh₂_slit_int_t₀4 heq_t₀_4 hgt₀_2 hg4_2
  -- Piece 5: [4, 5] — ftc_log_piece (slitPlane)
  have hh₃_slit : ∀ t ∈ Icc (4:ℝ) 5, h₃ t ∈ slitPlane := by
    intro t ⟨ht4, ht5⟩
    rcases eq_or_lt_of_le ht4 with rfl | ht4'
    · rw [Complex.mem_slitPlane_iff]; right
      simp only [h₃, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      linarith
    · rw [show h₃ t = g t from (hg_eq_h₃ t ht4').symm, Complex.mem_slitPlane_iff]; right
      show (g t).im ≠ 0
      simp only [show g t = h₃ t from hg_eq_h₃ t ht4', h₃, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero]
      linarith
  have piece₅ := ftc_log_piece (by norm_num : (4:ℝ) ≤ 5) hh₃_cont hh₃_diff
    hh₃_deriv_cont hh₃_slit heq_45 hg4_3 hg5
  -- Combine integrability
  have hint_left : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (2 - δ) :=
    piece₀.1.trans piece₁.1
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (2 + δ) 5 :=
    piece₂.1.trans (piece₃.1.trans (piece₄.1.trans piece₅.1))
  refine ⟨hint_left, hint_right, ?_⟩
  -- Combine integrals
  rw [(intervalIntegral.integral_add_adjacent_intervals piece₀.1 piece₁.1).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₂.1
      (piece₃.1.trans (piece₄.1.trans piece₅.1))).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₃.1
      (piece₄.1.trans piece₅.1)).symm,
    (intervalIntegral.integral_add_adjacent_intervals piece₄.1 piece₅.1).symm,
    piece₀.2, piece₁.2, piece₂.2, piece₃.2, piece₄.2, piece₅.2]
  -- Branch cut corrections
  have hg3_im_neg : (g 3).im < 0 := by
    rw [hg3_2]; simp only [h₂, Complex.add_im, Complex.neg_im, Complex.div_ofNat_im,
      Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, zero_add, mul_one]
    nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num),
              sq_nonneg (2 - Real.sqrt 3)]
  have hg3_ne : g 3 ≠ 0 := g_i_ne_zero_seg3 (le_refl 3) (by norm_num)
  have h_branch_3 : Complex.log (-(g 3)) = Complex.log (g 3) + ↑Real.pi * I :=
    log_neg_eq_add_pi_I hg3_ne hg3_im_neg
  have h_branch_t₀ : Complex.log (-(g t₀)) - Complex.log (g t₀) = -(↑Real.pi * I) := by
    rw [hgt₀_val]
    have h1 : -(-1 / 2 : ℂ) = (1 / 2 : ℂ) := by ring
    rw [h1]
    -- log(1/2) - log(-1/2) = -(π*I)
    -- -1/2 = ↑(1/2 : ℝ) * (-1)
    have hm : (-1:ℂ) / 2 = ↑((1:ℝ)/2) * (-1:ℂ) := by push_cast; ring
    rw [hm, Complex.log_ofReal_mul (by norm_num : (0:ℝ) < 1/2) (by norm_num : (-1:ℂ) ≠ 0),
        Complex.log_neg_one]
    rw [show (1:ℂ)/2 = ↑((1:ℝ)/2) from by push_cast; ring,
        ← Complex.ofReal_log (show (0:ℝ) ≤ 1/2 from by norm_num)]
    ring
  have hg_closed : g 0 = g 5 := by
    show fdBoundary_H H 0 - I = fdBoundary_H H 5 - I; rw [fdBoundary_H_is_closed H]
  have h_branch_t₀' : Complex.log (-(g t₀)) = Complex.log (g t₀) - ↑Real.pi * I := by
    linear_combination h_branch_t₀
  rw [hg_closed, h_branch_3, h_branch_t₀']; ring

set_option maxHeartbeats 16000000 in
/-- The PV integral of `(γ-I)⁻¹ γ'` over `[0,5]` with ε-ball cutoff tends to `-iπ`. -/
theorem pv_integral_at_i_tendsto (H : ℝ) (hH : 1 < H) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0)
      (𝓝[>] 0) (𝓝 (-(I * ↑Real.pi))) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  set ε₀ := min (min (min (1/2) (H - 1)) (2 * Real.sin (Real.pi / 12))) (r / 2) with hε₀_def
  have hH1_pos : 0 < H - 1 := by linarith
  have hsin_pos : 0 < Real.sin (Real.pi / 12) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  have h2sin_pos : 0 < 2 * Real.sin (Real.pi / 12) := by positivity
  have hε₀_pos : 0 < ε₀ := by positivity
  refine ⟨ε₀, hε₀_pos, ?_⟩
  intro ε hε_mem hε_dist
  simp only [Set.mem_Ioi] at hε_mem
  rw [Real.dist_eq, sub_zero, abs_of_pos hε_mem] at hε_dist
  have hε_pos : 0 < ε := hε_mem
  have hε_lt_half : ε < 1 / 2 := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hε_lt_gap : ε < H - 1 := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_lt_2sin : ε < 2 * Real.sin (Real.pi / 12) := lt_of_lt_of_le hε_dist
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε_lt_r2 : ε < r / 2 := lt_of_lt_of_le hε_dist (min_le_right _ _)
  -- Define δ from ε: 2sin(δπ/12) = ε, i.e., δ = (12/π)·arcsin(ε/2)
  set δ := 12 / Real.pi * Real.arcsin (ε / 2) with hδ_def
  have hε_half_pos : 0 < ε / 2 := by linarith
  have hε_half_le : ε / 2 ≤ 1 := by linarith
  have hε_half_neg : -1 ≤ ε / 2 := by linarith
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have harcsin_pos : 0 < Real.arcsin (ε / 2) := Real.arcsin_pos.mpr hε_half_pos
  have hδ_pos : 0 < δ := by rw [hδ_def]; positivity
  have hδ_lt_one : δ < 1 := by
    rw [hδ_def]
    have hε_lt_sin : ε / 2 < Real.sin (Real.pi / 12) := by linarith
    have harcsin_lt : Real.arcsin (ε / 2) < Real.pi / 12 := by
      calc Real.arcsin (ε / 2) < Real.arcsin (Real.sin (Real.pi / 12)) :=
            Real.arcsin_lt_arcsin hε_half_neg hε_lt_sin (Real.sin_le_one _)
        _ = Real.pi / 12 :=
            Real.arcsin_sin (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
    calc 12 / Real.pi * Real.arcsin (ε / 2)
        < 12 / Real.pi * (Real.pi / 12) :=
          mul_lt_mul_of_pos_left harcsin_lt (div_pos (by norm_num) hpi_pos)
      _ = 1 := by field_simp
  -- Norm equalities: ‖g(2±δ)‖ = ε (symmetric)
  have hδ_angle : δ * Real.pi / 12 = Real.arcsin (ε / 2) := by rw [hδ_def]; field_simp
  have h_norm_L : ‖fdBoundary_H H (2 - δ) - I‖ = ε := by
    rw [g_i_norm_left hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  have h_norm_R : ‖fdBoundary_H H (2 + δ) - I‖ = ε := by
    rw [g_i_norm_right hδ_pos hδ_lt_one, hδ_angle,
        Real.sin_arcsin hε_half_neg hε_half_le]; linarith
  set g := fun t => fdBoundary_H H t - I with hg_def
  have h_ftc := ftc_logDeriv_telescope_i H hH hδ_pos hδ_lt_one
  obtain ⟨hint_L, hint_R, h_telescope⟩ := h_ftc
  -- Norm bounds outside [2-δ, 2+δ]
  have h_norm_gt_left : ∀ t ∈ Ioo (0 : ℝ) (2 - δ), ‖g t‖ > ε := by
    intro t ⟨ht0, ht2⟩
    rcases le_or_lt t 1 with ht1 | ht1
    · calc ε < 1 / 2 := hε_lt_half
        _ ≤ ‖g t‖ := g_i_norm_ge_seg0 (le_of_lt ht0) ht1
    · rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_left ht1 (by linarith)]
      rw [← h_norm_L, g_i_norm_left hδ_pos hδ_lt_one]
      apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 2)
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
  have h_norm_gt_right : ∀ t ∈ Ioo (2 + δ) (5 : ℝ), ‖g t‖ > ε := by
    intro t ⟨ht2, ht5⟩
    rcases le_or_lt t 3 with ht3 | ht3
    · rcases eq_or_lt_of_le ht3 with rfl | ht3'
      · calc ε < 1 / 2 := hε_lt_half
          _ ≤ ‖g 3‖ := g_i_norm_ge_seg3 (le_refl 3) (by norm_num)
      · rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_right (by linarith) ht3']
        rw [← h_norm_R, g_i_norm_right hδ_pos hδ_lt_one]
        apply mul_lt_mul_of_pos_left _ (by norm_num : (0:ℝ) < 2)
        exact Real.sin_lt_sin_of_lt_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
    · rcases le_or_lt t 4 with ht4 | ht4
      · calc ε < 1 / 2 := hε_lt_half
          _ ≤ ‖g t‖ := g_i_norm_ge_seg3 (le_of_lt ht3) ht4
      · calc ε < H - 1 := hε_lt_gap
          _ ≤ ‖g t‖ := g_i_norm_ge_seg4 H hH (le_of_lt ht4) (le_of_lt ht5)
  -- Norm ≤ ε inside [2-δ, 2+δ]
  have h_norm_le_middle : ∀ t, 2 - δ ≤ t → t ≤ 2 + δ → ¬(‖g t‖ > ε) := by
    intro t ht_lo ht_hi; push_neg
    rcases le_or_lt t 2 with ht2 | ht2
    · rcases eq_or_lt_of_le ht2 with rfl | ht2'
      · rw [show g 2 = fdBoundary_H H 2 - I from rfl, fdBoundary_H_at_two_eq_I,
          sub_self, norm_zero]; exact le_of_lt hε_pos
      · have ht1 : 1 < t := by linarith
        rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_left ht1 ht2']
        rw [← h_norm_L, g_i_norm_left hδ_pos hδ_lt_one]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
        exact Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
          (by nlinarith [Real.pi_pos])
    · rw [show g t = fdBoundary_H H t - I from rfl, g_i_norm_arc_right ht2 (by linarith)]
      rw [← h_norm_R, g_i_norm_right hδ_pos hδ_lt_one]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      exact Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        (by nlinarith [Real.pi_pos])
  -- Cutoff integrand
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ) with hF_def
  have hF_when_gt (t : ℝ) (h_gt : ‖g t‖ > ε) : F t = deriv g t / g t := by
    simp only [hF_def, if_pos h_gt, mul_comm (g t)⁻¹, div_eq_mul_inv]
  have hF_when_le (t : ℝ) (h_le : ¬(‖g t‖ > ε)) : F t = 0 := by
    simp only [hF_def, if_neg h_le]
  have hF_eq_left_ae : ∀ᵐ t ∂volume, t ∈ Ι (0 : ℝ) (2 - δ) → F t = deriv g t / g t := by
    have : ({2 - δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : (0:ℝ) ≤ 2 - δ)] at ht_mem
    exact hF_when_gt t (h_norm_gt_left t
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))⟩)
  have hF_int_left : IntervalIntegrable F volume 0 (2 - δ) :=
    hint_L.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_left_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_eq_right_ae : ∀ᵐ t ∂volume, t ∈ Ι (2 + δ) (5 : ℝ) → F t = deriv g t / g t := by
    have : ({5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact measure_singleton _)
    filter_upwards [this] with t ht_ne ht_mem
    rw [uIoc_of_le (by linarith : 2 + δ ≤ 5)] at ht_mem
    exact hF_when_gt t (h_norm_gt_right t
      ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (mem_singleton_iff.mpr h))⟩)
  have hF_int_right : IntervalIntegrable F volume (2 + δ) 5 :=
    hint_R.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_eq_right_ae.mono (fun t ht hm => (ht hm).symm)))
  have hF_eq_mid : ∀ t ∈ Ι (2 - δ) (2 + δ), F t = 0 := by
    intro t ht; rw [uIoc_of_le (by linarith : 2 - δ ≤ 2 + δ)] at ht
    exact hF_when_le t (h_norm_le_middle t (le_of_lt ht.1) ht.2)
  have hF_int_mid : IntervalIntegrable F volume (2 - δ) (2 + δ) :=
    (IntervalIntegrable.zero (μ := volume) (a := 2 - δ) (b := 2 + δ)).congr
      (fun t ht => (hF_eq_mid t ht).symm)
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(2 - δ), F t) + (∫ t in (2 - δ)..(2 + δ), F t) +
      (∫ t in (2 + δ)..(5:ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int_left.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
  have h_mid_zero : ∫ t in (2 - δ)..(2 + δ), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_eq_mid t ht))]
    simp [intervalIntegral.integral_zero]
  have h_int_eq : (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0:ℝ)..(2 - δ), deriv g t / g t) +
      (∫ t in (2 + δ)..(5:ℝ), deriv g t / g t) := by
    calc (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
        = ∫ t in (0:ℝ)..5, F t := rfl
      _ = _ + _ + _ := h_split
      _ = _ + 0 + _ := by rw [h_mid_zero]
      _ = _ := by
          rw [add_zero, intervalIntegral.integral_congr_ae hF_eq_left_ae,
              intervalIntegral.integral_congr_ae hF_eq_right_ae]
  -- Apply FTC telescope and compute error
  rw [show dist (∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0)
    (-(I * ↑Real.pi)) =
    ‖(∫ t in (0:ℝ)..5,
      if ‖fdBoundary_H H t - I‖ > ε
      then (fdBoundary_H H t - I)⁻¹ *
           deriv (fun s => fdBoundary_H H s - I) t
      else 0) - (-(I * ↑Real.pi))‖ from Complex.dist_eq _ _]
  rw [h_int_eq, h_telescope]
  -- Decompose log
  set zL := fdBoundary_H H (2 - δ) - I
  set zR := fdBoundary_H H (2 + δ) - I
  rw [← Complex.re_add_im (Complex.log zL), ← Complex.re_add_im (Complex.log zR),
    Complex.log_re, Complex.log_re, Complex.log_im, Complex.log_im]
  change ‖zL‖ = ε at h_norm_L; change ‖zR‖ = ε at h_norm_R
  rw [h_norm_L, h_norm_R,
    show zL.arg = (fdBoundary_H H (2 - δ) - I).arg from rfl,
    arg_approach_i_left hδ_pos hδ_lt_one,
    show zR.arg = (fdBoundary_H H (2 + δ) - I).arg from rfl,
    arg_approach_i_right hδ_pos hδ_lt_one]
  -- Simplify: everything reduces to ‖-(δπ/6)·I‖ = δπ/6
  have h_simp : ↑(Real.log ε) + ↑(-(δ * Real.pi / 12)) * I -
      (↑(Real.log ε) + ↑(δ * Real.pi / 12 - Real.pi) * I) -
      2 * ↑Real.pi * I - -(I * ↑Real.pi) =
      ↑(-(δ * Real.pi / 6)) * I := by push_cast; ring
  rw [h_simp, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
  -- Error bound: δπ/6 < 2ε < r
  set x := δ * Real.pi / 12 with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_le_one : x ≤ 1 := by nlinarith [Real.pi_le_four]
  have h_sin_lb := Real.sin_gt_sub_cube hx_pos hx_le_one
  have h_lb : x - x ^ 3 / 4 > x / 2 := by nlinarith [sq_nonneg x, sq_nonneg (1 - x)]
  -- ε = 2sin(x) > 2(x/2) = x, so x < ε, and δπ/6 = 2x < 2ε < r
  have h_norm_is_2sin : 2 * Real.sin x = ε := by
    rw [hx_def, show δ * Real.pi / 12 = δ * Real.pi / 12 from rfl]
    linarith [h_norm_L, g_i_norm_left (H := H) hδ_pos hδ_lt_one]
  have hx_lt_ε : x < ε := by linarith
  linarith

/-- `generalizedWindingNumber' (fdBoundary_H H) 0 5 I = -1/2`.

Note: requires `1 < H` (not just `√3/2 < H`) because for `H > 1`, the point `I` is
strictly inside the contour and the branch cut correction on seg 3 contributes `-2πi`.
For `√3/2 < H < 1`, `I` would be outside the contour and the result would be `+1/2`. -/
theorem gWN_fdBoundary_H_at_i (H : ℝ) (hH : 1 < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 I = -1/2 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []
  simp only [sub_zero]
  have h_tendsto := pv_integral_at_i_tendsto H hH
  rw [h_tendsto.limUnder_eq]
  -- (2πi)⁻¹ * (-(I * ↑π)) = -1/2
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-! ## Section 7: Packaging for Downstream Use -/

/-- `effectiveWinding` at `ρ` equals `-(gWN'(ρ))` (sign flip for CW curve). -/
theorem effectiveWinding_rho_eq_neg_gWN (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    (1 : ℚ) / 3 = -(generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPoint_rho +
      generalizedWindingNumber' (fdBoundary_H H) 0 5 ellipticPoint_rho_plus_one) := by
  rw [gWN_fdBoundary_H_at_rho H hH, gWN_fdBoundary_H_at_rho_plus_one H hH]
  push_cast; ring

/-- `effectiveWinding` at `i` equals `-gWN'(i)`. -/
theorem effectiveWinding_i_eq_neg_gWN (H : ℝ) (hH : 1 < H) :
    (1 : ℚ) / 2 = -(generalizedWindingNumber' (fdBoundary_H H) 0 5 I) := by
  rw [gWN_fdBoundary_H_at_i H hH]
  push_cast; ring

end
