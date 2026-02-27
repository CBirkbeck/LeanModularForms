/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary_Param
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_WindingWeights
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PrincipalValue

/-!
# Generalized Winding Number at Smooth Boundary Points

This file proves that `generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2` for smooth
(non-corner) points `s` on the boundary of the fundamental domain.

## Main Results

* `gWN_fdBoundary_H_eq_neg_half_of_rightEdge` — gWN = -1/2 for points on the right vertical edge
* `gWN_fdBoundary_H_eq_neg_half_of_leftEdge` — gWN = -1/2 for points on the left vertical edge

## Proof Strategy

For a point `s` on the right edge (`s.re = 1/2`, `√3/2 < s.im < H`):

1. **Parameterization**: Find `t₀ ∈ (0, 1)` with `fdBoundary_H H t₀ = s`.
2. **Separation**: Other segments stay bounded away from `s`.
3. **Seg1 is real-valued**: On seg1, `γ(t) - s` is purely imaginary, so
   `(γ(t) - s)⁻¹ · γ'(t)` is real. The PV on seg1 is ε-independent.
4. **FTC telescope**: The total PV = `iπ + branch_corrections = iπ - 2πi = -iπ`.
5. **Conclusion**: `gWN = (2πi)⁻¹ · (-iπ) = -1/2`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Right Edge Parameterization -/

/-- For a point on the right edge, `t₀ = (H - s.im) / (H - √3/2)` is the unique
parameter in `(0, 1)` with `fdBoundary_H H t₀ = s`. -/
lemma rightEdge_t₀_mem_Ioo (H : ℝ) (hH : H_height ≤ H) (s : ℂ)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    (H - s.im) / (H - Real.sqrt 3 / 2) ∈ Ioo (0 : ℝ) 1 := by
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    have : H_height = Real.sqrt 3 / 2 + 1 := rfl; linarith
  have hα_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  constructor
  · exact div_pos (by linarith) hα_pos
  · rw [div_lt_one hα_pos]; linarith

/-- `fdBoundary_H H` passes through `s` at parameter `t₀`. -/
lemma rightEdge_fdBoundary_eq (H : ℝ) (s : ℂ)
    (hs_re : s.re = 1/2) (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    let t₀ := (H - s.im) / (H - Real.sqrt 3 / 2)
    fdBoundary_H H t₀ = s := by
  intro t₀
  have hH_sqrt : Real.sqrt 3 / 2 < H := by linarith
  have hden_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  have ht₀_le : t₀ ≤ 1 := by
    rw [div_le_one hden_pos]; linarith
  simp only [fdBoundary_H, ht₀_le, ↓reduceIte]
  -- Goal: 1/2 + (↑H - ↑t₀ * (↑H - ↑√3 / 2)) * I = s
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
    linarith [hs_re]
  · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
    -- Goal: H - t₀ * (H - √3/2) = s.im where t₀ = (H - s.im)/(H - √3/2)
    have h_cancel : (H - s.im) / (H - Real.sqrt 3 / 2) * (H - Real.sqrt 3 / 2) = H - s.im :=
      div_mul_cancel₀ (H - s.im) (ne_of_gt hden_pos)
    linarith

/-- The right edge parameter `t₀` is the UNIQUE crossing point on `[0, 5]`. -/
lemma rightEdge_unique_crossing (H : ℝ) (hH : H_height ≤ H) (s : ℂ)
    (hs_re : s.re = 1/2) (hs_norm : ‖s‖ > 1) (hs_im_lower : Real.sqrt 3 / 2 < s.im)
    (hs_im : s.im < H) :
    let t₀ := (H - s.im) / (H - Real.sqrt 3 / 2)
    ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary_H H t = s → t = t₀ := by
  intro t₀ t ht hs_eq
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    have : H_height = Real.sqrt 3 / 2 + 1 := rfl; linarith
  have hden_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  -- Case analysis on which segment t is in
  by_cases h1 : t ≤ 1
  · -- Seg1: γ(t) = 1/2 + (H - t·(H - √3/2))·i
    simp only [fdBoundary_H, h1, ↓reduceIte] at hs_eq
    -- Extract imaginary part
    have him := congr_arg Complex.im hs_eq
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im] at him
    -- him : H - t * (H - √3/2) = s.im → t = (H - s.im) / (H - √3/2) = t₀
    show t = (H - s.im) / (H - Real.sqrt 3 / 2)
    have h_eq : t * (H - Real.sqrt 3 / 2) = H - s.im := by linarith
    rw [eq_div_iff (ne_of_gt hden_pos)]
    linarith
  · push_neg at h1
    by_cases h2 : t ≤ 2
    · -- Seg2 (arc): ‖γ(t)‖ = 1, but ‖s‖ > 1, contradiction
      simp only [fdBoundary_H, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte, h2] at hs_eq
      have : ‖s‖ = 1 := by
        rw [← hs_eq]
        rw [show (↑π / 3 + (↑t - 1) * (↑π / 2 - ↑π / 3)) * I =
          ↑(π / 3 + (t - 1) * (π / 2 - π / 3)) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      linarith
    · push_neg at h2
      by_cases h3 : t ≤ 3
      · -- Seg3 (arc): same ‖γ(t)‖ = 1 argument
        simp only [fdBoundary_H, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte,
                    show ¬(t ≤ 2) from not_le.mpr h2, h3] at hs_eq
        have : ‖s‖ = 1 := by
          rw [← hs_eq]
          rw [show (↑π / 2 + (↑t - 2) * (2 * ↑π / 3 - ↑π / 2)) * I =
            ↑(π / 2 + (t - 2) * (2 * π / 3 - π / 2)) * I from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        linarith
      · push_neg at h3
        by_cases h4 : t ≤ 4
        · -- Seg4 (left vertical): re = -1/2 ≠ 1/2
          simp only [fdBoundary_H, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte,
                      show ¬(t ≤ 2) from not_le.mpr h2,
                      show ¬(t ≤ 3) from not_le.mpr h3, h4] at hs_eq
          have hre := congr_arg Complex.re hs_eq
          simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
                Complex.I_re, Complex.I_im] at hre
          linarith [hs_re]
        · push_neg at h4
          -- Seg5 (horizontal): im = H ≠ s.im
          simp only [fdBoundary_H, show ¬(t ≤ 1) from not_le.mpr h1, ↓reduceIte,
                      show ¬(t ≤ 2) from not_le.mpr h2,
                      show ¬(t ≤ 3) from not_le.mpr h3,
                      show ¬(t ≤ 4) from not_le.mpr h4] at hs_eq
          have him := congr_arg Complex.im hs_eq
          simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
                Complex.I_re, Complex.I_im] at him
          linarith

/-! ## Right Edge Separation from Other Segments -/

/-- Points on seg2/seg3 (unit circle) are at distance ≥ ‖s‖ - 1 from s. -/
lemma rightEdge_dist_from_arc (s : ℂ) (z : ℂ) (hz : ‖z‖ = 1) :
    ‖s‖ - 1 ≤ ‖z - s‖ := by
  calc ‖s‖ - 1 = ‖s‖ - ‖z‖ := by rw [hz]
    _ ≤ |‖s‖ - ‖z‖| := le_abs_self _
    _ = |‖z‖ - ‖s‖| := abs_sub_comm _ _
    _ ≤ ‖z - s‖ := abs_norm_sub_norm_le z s

/-- Points on seg4 (left vertical, re = -1/2) are at distance ≥ 1 from s with re = 1/2. -/
lemma rightEdge_dist_from_leftVertical (s : ℂ) (hs_re : s.re = 1/2) (z : ℂ) (hz_re : z.re = -1/2) :
    1 ≤ ‖z - s‖ := by
  have hre : (z - s).re = -1 := by
    simp [Complex.sub_re, hz_re, hs_re]; ring
  calc 1 = |(z - s).re| := by rw [hre]; norm_num
    _ ≤ ‖z - s‖ := abs_re_le_norm (z - s)

/-- Points on seg5 (horizontal at height H) are at distance ≥ H - s.im from s with s.im < H. -/
lemma rightEdge_dist_from_horizontal (s : ℂ) (hs_im : s.im < H) (z : ℂ) (hz_im : z.im = H) :
    H - s.im ≤ ‖z - s‖ := by
  have him : (z - s).im = H - s.im := by simp [Complex.sub_im, hz_im]
  calc H - s.im = |(z - s).im| := by rw [him]; rw [abs_of_pos (by linarith)]
    _ ≤ ‖z - s‖ := abs_im_le_norm (z - s)

/-- Minimum distance from s (on right edge) to the non-seg1 parts of the boundary. -/
lemma rightEdge_min_dist_pos (s : ℂ) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H) :
    0 < min (min (‖s‖ - 1) 1) (H - s.im) := by
  simp only [lt_min_iff]
  exact ⟨⟨by linarith, by norm_num⟩, by linarith⟩

/-! ## FTC for log(−g) on smooth segments -/

/-- FTC on a smooth segment: `∫ f'/f = log(−f(b)) − log(−f(a))` when `−f` stays in `slitPlane`. -/
private lemma ftc_log_neg {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, -(f t) ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t = Complex.log (-(f b)) - Complex.log (-(f a)) := by
  have hf_ne : ∀ t ∈ Icc a b, f t ≠ 0 := fun t ht =>
    neg_ne_zero.mp (Complex.slitPlane_ne_zero (hf_slit t ht))
  have hF_cont : ContinuousOn (fun t => Complex.log (-(f t))) (Icc a b) :=
    hf_cont.neg.clog (fun t ht => hf_slit t ht)
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun t => Complex.log (-(f t)))
      (deriv f x / f x) x := by
    intro x hx
    have hslit := hf_slit x (Ioo_subset_Icc_self hx)
    have h_log := (hf_diff x hx).hasDerivAt.neg.clog_real hslit
    convert h_log using 1
    exact (neg_div_neg_eq (deriv f x) (f x)).symm
  have hint : IntervalIntegrable (fun t => deriv f t / f t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hf_deriv_cont.div hf_cont (fun x hx => hf_ne x hx)
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hint⟩

/-- FTC for `log ∘ f` when `f` stays in slitPlane (no negation). -/
private lemma ftc_log {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b ∧
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a) := by
  have hf_ne : ∀ t ∈ Icc a b, f t ≠ 0 :=
    fun t ht => Complex.slitPlane_ne_zero (hf_slit t ht)
  have hF_cont : ContinuousOn (fun t => Complex.log (f t)) (Icc a b) :=
    hf_cont.clog (fun t ht => hf_slit t ht)
  have hF_deriv : ∀ x ∈ Ioo a b, HasDerivAt (fun t => Complex.log (f t))
      (deriv f x / f x) x := by
    intro x hx
    exact (hf_diff x hx).hasDerivAt.clog_real (hf_slit x (Ioo_subset_Icc_self hx))
  have hint : IntervalIntegrable (fun t => deriv f t / f t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hf_deriv_cont.div hf_cont (fun x hx => hf_ne x hx)
  exact ⟨hint, intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF_cont hF_deriv hint⟩

/-! ## Key Log Computations -/

/-- log(-(r*I)) - log(r*I) = -π*I for r > 0 -/
private lemma log_neg_rI_sub_log_rI {r : ℝ} (hr : 0 < r) :
    Complex.log (-(↑r * I)) - Complex.log (↑r * I) = -(↑Real.pi * I) := by
  rw [show -(↑r * I : ℂ) = ↑r * (-I) from by ring]
  rw [Complex.log_ofReal_mul hr I_ne_zero, Complex.log_ofReal_mul hr (neg_ne_zero.mpr I_ne_zero)]
  rw [Complex.log_I, Complex.log_neg_I]; ring

/-- For elements with positive real part, `log(a/b) = log a - log b`. -/
private lemma log_div_of_re_pos {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    Complex.log (a / b) = Complex.log a - Complex.log b := by
  have ha_ne : a ≠ 0 := by intro h; simp [h] at ha
  have hb_ne : b ≠ 0 := by intro h; simp [h] at hb
  have hb_inv_ne : b⁻¹ ≠ 0 := inv_ne_zero hb_ne
  rw [div_eq_mul_inv]
  have hb_arg_ne_pi : b.arg ≠ Real.pi := by
    intro h; have := Complex.arg_eq_pi_iff.mp h; linarith [this.1]
  have hb_inv_arg : b⁻¹.arg = -b.arg := by
    rw [Complex.arg_inv]; simp [hb_arg_ne_pi]
  have ha_abs_arg : |a.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl ha)
  have hb_abs_arg : |b.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hb)
  have hbi_abs_arg : |b⁻¹.arg| < Real.pi / 2 := by
    rw [hb_inv_arg, abs_neg]; exact hb_abs_arg
  have h_sum : a.arg + b⁻¹.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    constructor
    · linarith [abs_lt.mp ha_abs_arg, abs_lt.mp hbi_abs_arg]
    · linarith [abs_lt.mp ha_abs_arg, abs_lt.mp hbi_abs_arg]
  rw [Complex.log_mul ha_ne hb_inv_ne h_sum, Complex.log_inv b hb_arg_ne_pi]
  ring

/-! ## Right Edge: g on seg1 -/

/-- On seg1, g is purely imaginary when s.re = 1/2. -/
private lemma rightEdge_g_seg1_eq {H : ℝ} {s : ℂ} (hs_re : s.re = 1/2) (t : ℝ) (ht : t ≤ 1) :
    fdBoundary_H H t - s = (↑(H - t * (H - Real.sqrt 3 / 2) - s.im) : ℂ) * I := by
  simp only [fdBoundary_H, ht, ↓reduceIte]
  rw [show s = (↑(1/2 : ℝ) : ℂ) + ↑s.im * I from by
    rw [show (1/2 : ℝ) = s.re from hs_re.symm]; exact (Complex.re_add_im s).symm]
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
  · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]

/-- Same as rightEdge_g_seg1_eq but for the smooth representative h₀ = fdBoundary_seg1_H - s. -/
private lemma rightEdge_h₀_eq {H : ℝ} {s : ℂ} (hs_re : s.re = 1/2) (t : ℝ) :
    fdBoundary_seg1_H H t - s = (↑(H - t * (H - Real.sqrt 3 / 2) - s.im) : ℂ) * I := by
  simp only [fdBoundary_seg1_H]
  rw [show s = (↑(1/2 : ℝ) : ℂ) + ↑s.im * I from by
    rw [show (1/2 : ℝ) = s.re from hs_re.symm]; exact (Complex.re_add_im s).symm]
  apply Complex.ext
  · simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.I_im]
  · simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]

private theorem exp_real_angle_I (θ : ℝ) :
    Complex.exp (↑θ * I) = ↑(Real.cos θ) + ↑(Real.sin θ) * I := by
  rw [exp_mul_I]; simp [Complex.ofReal_cos, Complex.ofReal_sin]

private theorem cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]; ring

private theorem sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
  rw [show (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.sin_pi_sub]; exact Real.sin_pi_div_three

/-! ## Right Edge: Smooth Representatives and FTC Telescope -/

/-- HasDerivAt for the arc smooth representative minus s. -/
private lemma hasDerivAt_arc_rep (s : ℂ) (t : ℝ) :
    HasDerivAt (fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s)
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have hf : HasDerivAt (fun s : ℝ => Real.pi * (1 + s) / 6) (Real.pi / 6) t :=
    ((hasDerivAt_id t).add_const (1:ℝ) |>.const_mul (Real.pi / 6)).congr_of_eventuallyEq
      (Eventually.of_forall fun s => show _ from by simp [id]; ring)
      |>.congr_deriv (by ring)
  have hci : HasDerivAt (fun s : ℝ => (↑(Real.pi * (1 + s) / 6) : ℂ) * I)
      ((↑(Real.pi / 6) : ℂ) * I) t :=
    (hf.ofReal_comp.mul_const I).congr_deriv (by norm_num [smul_eq_mul])
  exact (hci.cexp.sub (hasDerivAt_const t s)).congr_deriv (by simp only [sub_zero]; ring)

private lemma norm_fdBoundary_H_arc (H : ℝ) (t : ℝ) (ht1 : 1 < t) (ht3 : t < 3) :
    ‖fdBoundary_H H t‖ = 1 := by
  rw [fdBoundary_H_eq_arc ht1 ht3]; exact Complex.norm_exp_ofReal_mul_I _

private lemma re_fdBoundary_H_seg4 (H : ℝ) (t : ℝ) (ht1 : 1 < t) (ht2 : 2 < t)
    (ht3 : 3 < t) (ht4 : t ≤ 4) :
    (fdBoundary_H H t).re = -1/2 := by
  rw [fdBoundary_H_eq_seg4_H (not_le.mpr ht1) (not_le.mpr ht2) (not_le.mpr ht3) ht4]
  simp [fdBoundary_seg4_H, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma im_fdBoundary_H_seg5 (H : ℝ) (t : ℝ) (ht1 : 1 < t) (ht2 : 2 < t)
    (ht3 : 3 < t) (ht4 : 4 < t) :
    (fdBoundary_H H t).im = H := by
  rw [fdBoundary_H_eq_seg5_H (not_le.mpr ht1) (not_le.mpr ht2) (not_le.mpr ht3) (not_le.mpr ht4)]
  simp [fdBoundary_seg5_H, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]

private lemma rightEdge_min_dist_from_non_seg1_arc (s : ℂ) (hs_norm : ‖s‖ > 1) (z : ℂ)
    (hz : ‖z‖ = 1) : min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖s - z‖ := by
  rw [norm_sub_rev]
  exact ((min_le_left _ _).trans (min_le_left _ _)).trans (rightEdge_dist_from_arc s z hz)

private lemma rightEdge_min_dist_from_non_seg1_seg4 (s : ℂ) (hs_re : s.re = 1/2) (z : ℂ)
    (hz_re : z.re = -1/2) : min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖s - z‖ := by
  rw [norm_sub_rev]
  exact ((min_le_left _ _).trans (min_le_right _ _)).trans (rightEdge_dist_from_leftVertical s hs_re z hz_re)

private lemma rightEdge_min_dist_from_non_seg1_seg5 (s : ℂ) (hs_im : s.im < H) (z : ℂ)
    (hz_im : z.im = H) : min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖s - z‖ := by
  rw [norm_sub_rev]
  exact (min_le_right _ _).trans (rightEdge_dist_from_horizontal s hs_im z hz_im)

set_option maxHeartbeats 800000 in
private lemma rightEdge_min_dist_from_non_seg1 (H : ℝ) (s : ℂ)
    (hs_re : s.re = 1/2) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H)
    (t : ℝ) (ht1 : 1 < t) (ht5 : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundary_H H t - s‖ := by
  have neg_sub_norm : ‖fdBoundary_H H t - s‖ = ‖s - fdBoundary_H H t‖ := by
    rw [norm_sub_rev]
  rw [neg_sub_norm]
  by_cases h2 : t ≤ 2
  · exact rightEdge_min_dist_from_non_seg1_arc s hs_norm _
      (norm_fdBoundary_H_arc H t ht1 (by linarith))
  · push_neg at h2
    by_cases h3 : t < 3
    · exact rightEdge_min_dist_from_non_seg1_arc s hs_norm _
        (norm_fdBoundary_H_arc H t ht1 h3)
    · push_neg at h3 -- h3 : 3 ≤ t
      rcases eq_or_lt_of_le h3 with h3_eq | h3_lt
      · -- t = 3: arc endpoint, ‖fdBoundary_H H 3‖ = 1
        subst h3_eq
        have : ‖fdBoundary_H H 3‖ = 1 := by
          simp only [fdBoundary_H, show ¬((3:ℝ) ≤ 1) from by norm_num, ↓reduceIte,
            show ¬((3:ℝ) ≤ 2) from by norm_num, show (3:ℝ) ≤ 3 from le_refl _]
          convert Complex.norm_exp_ofReal_mul_I (2 * Real.pi / 3) using 2
          push_cast; ring
        exact rightEdge_min_dist_from_non_seg1_arc s hs_norm _ this
      · -- 3 < t
        by_cases h4 : t ≤ 4
        · exact rightEdge_min_dist_from_non_seg1_seg4 s hs_re _
            (re_fdBoundary_H_seg4 H t ht1 h2 h3_lt h4)
        · push_neg at h4
          exact rightEdge_min_dist_from_non_seg1_seg5 s hs_im _
            (im_fdBoundary_H_seg5 H t ht1 h2 h3_lt h4)

set_option maxHeartbeats 1600000 in
theorem gWN_fdBoundary_H_eq_neg_half_of_rightEdge (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = 1/2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []; simp only [sub_zero]
  -- Setup notation
  set g : ℝ → ℂ := fun t => fdBoundary_H H t - s with hg_def
  set α := H - Real.sqrt 3 / 2 with hα_def
  set t₀ := (H - s.im) / α with ht₀_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have ht₀_pos : 0 < t₀ := div_pos (by linarith) hα_pos
  have ht₀_lt : t₀ < 1 := by rw [ht₀_def, div_lt_one hα_pos]; linarith [hα_def]
  have ht₀_mul : t₀ * α = H - s.im := div_mul_cancel₀ _ hα_ne
  -- Smooth representatives for each segment
  set h₀ : ℝ → ℂ := fun t => fdBoundary_seg1_H H t - s
  set h_arc : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
  set h₃ : ℝ → ℂ := fun t => fdBoundary_seg4_H H t - s
  set h₅ : ℝ → ℂ := fun t => fdBoundary_seg5_H H t - s
  -- HasDerivAt for each
  have hd₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg1_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd_arc : ∀ t : ℝ, HasDerivAt h_arc
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_rep s
  have hd₃ : ∀ t : ℝ, HasDerivAt h₃ ((↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg4_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd₅ : ∀ t : ℝ, HasDerivAt h₅ 1 t := by
    intro t; exact (hasDerivAt_fdBoundary_seg5_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp)
  -- Value agreement: g = hₖ on each segment
  have hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; simp only [hg_def, h₀]; rw [fdBoundary_H_eq_seg1_H ht]
  have hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t := by
    intro t ht1 ht3; simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t := by
    intro t ht3 ht4; simp only [hg_def, h₃]
    rw [fdBoundary_H_eq_seg4_H (not_le.mpr (by linarith : 1 < t))
        (not_le.mpr (by linarith : 2 < t)) (not_le.mpr ht3) ht4]
  have hg_h₅ : ∀ t, 4 < t → g t = h₅ t := by
    intro t ht4; simp only [hg_def, h₅]
    rw [fdBoundary_H_eq_seg5_H (not_le.mpr (by linarith : 1 < t))
        (not_le.mpr (by linarith : 2 < t)) (not_le.mpr (by linarith : 3 < t))
        (not_le.mpr ht4)]
  -- Endpoint value agreement
  have hep_01 : h₀ 0 = h₅ 5 := by
    simp only [h₀, h₅, fdBoundary_seg1_H, fdBoundary_seg5_H]; push_cast; ring
  have hep_1 : h₀ 1 = h_arc 1 := by
    simp only [h₀, h_arc, fdBoundary_seg1_H]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hep_3 : h_arc 3 = h₃ 3 := by
    simp only [h_arc, h₃, fdBoundary_seg4_H]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hep_4 : h₃ 4 = h₅ 4 := by
    simp only [h₃, h₅, fdBoundary_seg4_H, fdBoundary_seg5_H]; push_cast; ring
  -- Derivative agreement (EventuallyEq)
  have hderiv_01 : ∀ t ∈ Ioo (0:ℝ) 1, deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Iio_mem_nhds ht1) (fun s hs => hg_h₀ s (le_of_lt hs)))
  have hderiv_arc : ∀ t ∈ Ioo (1:ℝ) 3, deriv g t = deriv h_arc t := by
    intro t ⟨ht1, ht3⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht3) (fun s hs => hg_arc s hs.1 hs.2))
  have hderiv_3 : ∀ t ∈ Ioo (3:ℝ) 4, deriv g t = deriv h₃ t := by
    intro t ⟨ht3, ht4⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht3 ht4)
        (fun s hs => hg_h₃ s hs.1 (le_of_lt hs.2)))
  have hderiv_5 : ∀ t ∈ Ioo (4:ℝ) 5, deriv g t = deriv h₅ t := by
    intro t ⟨ht4, _⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_h₅ s hs))
  -- slitPlane conditions for -(hₖ t)
  have hslit₀_left : ∀ δ', 0 < δ' → δ' < t₀ →
      ∀ t ∈ Icc (0 : ℝ) (t₀ - δ'), -(h₀ t) ∈ Complex.slitPlane := by
    intro δ' hδ' hδ't₀ t ⟨ht0, htd⟩
    rw [Complex.mem_slitPlane_iff]; right
    show (-(h₀ t)).im ≠ 0
    simp only [h₀, rightEdge_h₀_eq hs_re, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero]
    -- Goal: -(H - t * (H - √3/2) - s.im) ≠ 0
    have : t * α < H - s.im := by
      calc t * α ≤ (t₀ - δ') * α := by nlinarith
        _ = t₀ * α - δ' * α := by ring
        _ = (H - s.im) - δ' * α := by rw [ht₀_mul]
        _ < H - s.im := by nlinarith
    rw [hα_def] at this; intro h; linarith
  have hslit₀_right : ∀ δ', 0 < δ' → δ' < 1 - t₀ →
      ∀ t ∈ Icc (t₀ + δ') 1, -(h₀ t) ∈ Complex.slitPlane := by
    intro δ' hδ' hδ'1t₀ t ⟨htd, ht1⟩
    rw [Complex.mem_slitPlane_iff]; right
    show (-(h₀ t)).im ≠ 0
    simp only [h₀, rightEdge_h₀_eq hs_re, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero]
    have : t * α > H - s.im := by
      calc t * α ≥ (t₀ + δ') * α := by nlinarith
        _ = t₀ * α + δ' * α := by ring
        _ = (H - s.im) + δ' * α := by rw [ht₀_mul]
        _ > H - s.im := by nlinarith
    rw [hα_def] at this; intro h; linarith
  have hslit_arc : ∀ t ∈ Icc (1:ℝ) 3, -(h_arc t) ∈ Complex.slitPlane := by
    intro t ⟨ht1, ht3⟩
    rw [Complex.mem_slitPlane_iff]
    simp only [h_arc, neg_sub]
    -- -(h_arc t) = s - exp(θ*I), re = 1/2 - cos(θ), im = s.im - sin(θ)
    -- θ = π*(1+t)/6 ∈ [π/3, 2π/3]
    set θ := Real.pi * (1 + t) / 6 with hθ_def
    have hθ_lower : Real.pi / 3 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    have hθ_upper : θ ≤ 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    by_cases ht1_eq : t = 1
    · -- At t=1: cos(π/3) = 1/2, need im ≠ 0
      right
      subst ht1_eq
      show (s - cexp (↑(Real.pi * (1 + 1) / 6) * I)).im ≠ 0
      rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
          exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
      linarith [hs_im_lower]
    · -- For t > 1: cos(θ) < 1/2, so re > 0
      left
      have ht1_strict : 1 < t := lt_of_le_of_ne ht1 (Ne.symm ht1_eq)
      have hθ_strict : Real.pi / 3 < θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
      -- Need (s - exp(θ*I)).re > 0, i.e., s.re - cos(θ) > 0, i.e., cos(θ) < 1/2
      simp only [Complex.sub_re, exp_ofReal_mul_I_re]
      rw [hs_re]
      -- cos(θ) < cos(π/3) = 1/2 for θ > π/3
      have hcos_lt : Real.cos θ < 1 / 2 := by
        have h_pi_div_three : Real.pi / 3 > 0 := by nlinarith [Real.pi_pos]
        have h_theta : θ > Real.pi / 3 := hθ_strict
        have h_theta_le_pi : θ ≤ 2 * Real.pi / 3 := hθ_upper
        have h_upper_pi : 2 * Real.pi / 3 ≤ Real.pi := by nlinarith [Real.pi_pos]
        rw [← Real.cos_pi_div_three]
        exact Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt h_pi_div_three) (h_theta_le_pi.trans (by nlinarith [Real.pi_pos])) hθ_strict
      linarith
  have hslit₃ : ∀ t ∈ Icc (3:ℝ) 4, -(h₃ t) ∈ Complex.slitPlane := by
    intro t ⟨_, _⟩
    rw [Complex.mem_slitPlane_iff]; left
    simp only [h₃, fdBoundary_seg4_H, neg_sub, Complex.sub_re, Complex.add_re, Complex.neg_re,
      Complex.div_ofNat_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero]
    rw [hs_re]
    norm_num
  have hslit₅ : ∀ t ∈ Icc (4:ℝ) 5, -(h₅ t) ∈ Complex.slitPlane := by
    intro t ⟨ht4, ht5⟩
    rw [Complex.mem_slitPlane_iff]
    simp only [h₅, fdBoundary_seg5_H, neg_sub]
    by_cases ht5_eq : t = 5
    · right
      subst ht5_eq
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith
    · left
      have : t < 5 := lt_of_le_of_ne ht5 ht5_eq
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hs_re]; linarith
  -- Apply ftc_log_neg on each sub-interval
  -- Choose ε₀ and show eventually constant
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  have hd_pos : 0 < d := rightEdge_min_dist_pos s hs_norm hs_im
  set ε₀ := min d (min (d * α) (min (t₀ * α) ((1 - t₀) * α)))
  have hε₀_pos : 0 < ε₀ := by
    refine lt_min hd_pos (lt_min (mul_pos hd_pos hα_pos) (lt_min (mul_pos ht₀_pos hα_pos) (mul_pos (by linarith) hα_pos)))
  suffices h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ *
        deriv (fun u => fdBoundary_H H u - s) t else 0) = -(↑Real.pi * I) by
    rw [show (fun ε => ∫ t in (0:ℝ)..5, if ‖(fdBoundary_H H t - s)‖ > ε then
        (fdBoundary_H H t - s)⁻¹ * deriv (fun u => fdBoundary_H H u - s) t else 0) =
      (fun ε => ∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ *
        deriv (fun u => fdBoundary_H H u - s) t else 0) from rfl]
    have h_tendsto : Filter.Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ *
        deriv (fun u => fdBoundary_H H u - s) t else 0) (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) :=
      tendsto_const_nhds.congr' (h_ev.mono (fun _ h => h.symm))
    rw [h_tendsto.limUnder_eq]
    field_simp [Real.pi_ne_zero, I_ne_zero]
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀_pos, fun ε hε => ?_⟩
  obtain ⟨hε_pos, hε_lt⟩ := hε
  have hε_lt_d : ε < d := calc ε < ε₀ := hε_lt
      _ ≤ d := min_le_left _ _
  have hεα_lt_d : ε / α < d := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min (t₀ * α) ((1 - t₀) * α)) := min_le_right _ _
      _ ≤ d * α := min_le_left _ _
  have hεα_lt_t₀ : ε / α < t₀ := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min (t₀ * α) ((1 - t₀) * α)) := min_le_right _ _
      _ ≤ min (t₀ * α) ((1 - t₀) * α) := min_le_right _ _
      _ ≤ t₀ * α := min_le_left _ _
  have hεα_lt_1mt₀ : ε / α < 1 - t₀ := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min (t₀ * α) ((1 - t₀) * α)) := min_le_right _ _
      _ ≤ min (t₀ * α) ((1 - t₀) * α) := min_le_right _ _
      _ ≤ (1 - t₀) * α := min_le_right _ _
  set δ := ε / α with hδ_def
  have hδ_pos : 0 < δ := div_pos hε_pos hα_pos
  -- g = deriv g convention: deriv (fdBoundary_H H · - s) = deriv g
  have hderiv_eq : deriv (fun u => fdBoundary_H H u - s) = deriv g := rfl
  rw [show (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ *
    deriv (fun u => fdBoundary_H H u - s) t else 0) =
    (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) from rfl]
  -- FTC on each piece using smooth representatives
  -- Piece 0: [0, t₀-δ]
  have piece₀ := ftc_log_neg (by linarith : (0:ℝ) ≤ t₀ - δ)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑α : ℂ) * I from funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    (hslit₀_left δ hδ_pos hεα_lt_t₀)
  -- Piece 1: [t₀+δ, 1]
  have piece₁ := ftc_log_neg (by linarith : t₀ + δ ≤ 1)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑α : ℂ) * I from funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    (hslit₀_right δ hδ_pos hεα_lt_1mt₀)
  -- Piece 2: [1, 3] (arc)
  have h_arc_cont : Continuous h_arc := by
    simp only [h_arc]; exact (Continuous.cexp (by fun_prop)).sub continuous_const
  have piece₂ := ftc_log_neg (by norm_num : (1:ℝ) ≤ 3)
    h_arc_cont.continuousOn
    (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc
  -- Piece 3: [3, 4]
  have piece₃ := ftc_log_neg (by norm_num : (3:ℝ) ≤ 4)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    hslit₃
  -- Piece 4: [4, 5]
  have piece₄ := ftc_log_neg (by norm_num : (4:ℝ) ≤ 5)
    ((continuous_fdBoundary_seg5_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₅ t).differentiableAt)
    (by rw [show deriv h₅ = fun _ => (1 : ℂ) from funext fun t => (hd₅ t).deriv]
        exact continuousOn_const)
    hslit₅
  -- Convert from hₖ integrands to g integrands via a.e. equality
  have h_ae₀ : ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
      ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → deriv h₀ t / h₀ t = deriv g t / g t := by
    intro a b ha_nn hab hb1
    have h_excl : ({b} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({b} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht
    rw [Set.uIoc_of_le (le_of_lt hab)] at ht
    have ht_lt_b : t < b := lt_of_le_of_ne ht.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
    have ht_lt1 : t < 1 := lt_of_lt_of_le ht_lt_b hb1
    rw [hg_h₀ t (le_of_lt ht_lt1), hderiv_01 t ⟨by linarith [ht.1], ht_lt1⟩]
  have h_ae_arc : ∀ᵐ t ∂volume, t ∈ Set.uIoc 1 3 → deriv h_arc t / h_arc t = deriv g t / g t := by
    have : ({1, 3} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact ((Set.toFinite ({1, 3} : Set ℝ)).measure_zero volume))
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht_mem
    have ht1 : 1 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht3 : t < 3 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_arc t ht1 ht3, hderiv_arc t ⟨ht1, ht3⟩]
  have h_ae₃ : ∀ᵐ t ∂volume, t ∈ Set.uIoc 3 4 → deriv h₃ t / h₃ t = deriv g t / g t := by
    have : ({3, 4} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact ((Set.toFinite ({3, 4} : Set ℝ)).measure_zero volume))
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at ht_mem
    have ht3 : 3 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht4 : t < 4 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₃ t ht3 (le_of_lt ht4), hderiv_3 t ⟨ht3, ht4⟩]
  have h_ae₅ : ∀ᵐ t ∂volume, t ∈ Set.uIoc 4 5 → deriv h₅ t / h₅ t = deriv g t / g t := by
    have : ({4, 5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({4, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at ht_mem
    have ht4 : 4 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht5 : t < 5 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₅ t ht4, hderiv_5 t ⟨ht4, ht5⟩]
  -- Transfer integrability from hₖ to g
  have hint₀ : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (t₀ - δ) :=
    piece₀.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₀ 0 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono
        (fun t ht hm => ht hm)))
  have hint₁ : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 1 :=
    piece₁.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₀ (t₀ + δ) 1 (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => ht hm)))
  have hint_arc : IntervalIntegrable (fun t => deriv g t / g t) volume 1 3 :=
    piece₂.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_arc.mono (fun t ht hm => ht hm)))
  have hint₃ : IntervalIntegrable (fun t => deriv g t / g t) volume 3 4 :=
    piece₃.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₃.mono (fun t ht hm => ht hm)))
  have hint₅ : IntervalIntegrable (fun t => deriv g t / g t) volume 4 5 :=
    piece₄.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₅.mono (fun t ht hm => ht hm)))
  -- Combined integrability
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 5 :=
    hint₁.trans hint_arc |>.trans hint₃ |>.trans hint₅
  -- Cutoff function
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ)
  -- On [0, t₀-δ]: ‖g(t)‖ > ε (from |t-t₀| > δ, ‖g‖ = |t-t₀|*α > δ*α = ε)
  -- At t = t₀-δ exactly, ‖g t‖ = ε (not >), so we exclude that point a.e.
  have hF_left : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (t₀ - δ) →
      F t = deriv g t / g t := by
    have h_excl : ({t₀ - δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({t₀ - δ} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ t₀ - δ)] at ht_mem
    have ht_lt : t < t₀ - δ := lt_of_le_of_ne ht_mem.2
      (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
    have ht_le1 : t ≤ 1 := by linarith
    have h_norm_gt : ‖g t‖ > ε := by
      show ‖fdBoundary_H H t - s‖ > ε
      rw [rightEdge_g_seg1_eq hs_re t ht_le1]
      simp only [show H - Real.sqrt 3 / 2 = α from hα_def.symm]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      have h_im_pos : H - t * α - s.im > 0 := by nlinarith [ht_mem.1]
      rw [abs_of_pos h_im_pos]
      have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
      have h_tα : t * α < (t₀ - δ) * α := mul_lt_mul_of_pos_right ht_lt hα_pos
      have h_expand : (t₀ - δ) * α = t₀ * α - δ * α := sub_mul t₀ δ α
      linarith [ht₀_mul]
    show F t = deriv g t / g t
    simp only [F, if_pos h_norm_gt]
    rw [div_eq_mul_inv, mul_comm]
  -- On [t₀+δ, 5]: ‖g(t)‖ > ε
  have hF_right : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ + δ) 5 →
      F t = deriv g t / g t := by
    have h_boundary : ({t₀ + δ, 5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({t₀ + δ, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [h_boundary] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ + δ ≤ 5)] at ht_mem
    have h_norm_gt : ‖g t‖ > ε := by
      by_cases ht1 : t ≤ 1
      · -- On seg1: ‖g‖ = (t-t₀)*α > δ*α = ε
        show ‖fdBoundary_H H t - s‖ > ε
        rw [rightEdge_g_seg1_eq hs_re t ht1]
        simp only [show H - Real.sqrt 3 / 2 = α from hα_def.symm]
        rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
        have h_tα : (t₀ + δ) * α < t * α :=
          mul_lt_mul_of_pos_right ht_mem.1 hα_pos
        have h_expand : (t₀ + δ) * α = t₀ * α + δ * α := add_mul t₀ δ α
        have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
        have h_im_neg : H - t * α - s.im < 0 := by linarith [ht₀_mul]
        rw [abs_of_neg h_im_neg]
        linarith [ht₀_mul]
      · -- On [1, 5]: ‖g‖ ≥ d > ε
        push_neg at ht1
        have : d ≤ ‖g t‖ := by
          show d ≤ ‖fdBoundary_H H t - s‖
          exact rightEdge_min_dist_from_non_seg1 H s hs_re hs_norm hs_im t ht1 ht_mem.2
        linarith [hε_lt_d]
    show F t = deriv g t / g t
    simp only [F, if_pos h_norm_gt]
    rw [div_eq_mul_inv, mul_comm]
  -- On [t₀-δ, t₀+δ]: ‖g(t)‖ ≤ ε, so F = 0
  have hF_mid : ∀ t ∈ Set.uIoc (t₀ - δ) (t₀ + δ), F t = 0 := by
    intro t ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ - δ ≤ t₀ + δ)] at ht_mem
    simp only [F]
    have h_norm : ‖g t‖ ≤ ε := by
      show ‖fdBoundary_H H t - s‖ ≤ ε
      rw [rightEdge_g_seg1_eq hs_re t (by linarith [ht_mem.2, hεα_lt_1mt₀])]
      simp only [show H - Real.sqrt 3 / 2 = α from hα_def.symm]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
      rw [abs_le]
      have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
      have h_upper : (t₀ + δ) * α = t₀ * α + δ * α := by ring
      have h_lower : (t₀ - δ) * α = t₀ * α - δ * α := by ring
      have h_tα_upper : t * α ≤ (t₀ + δ) * α :=
        mul_le_mul_of_nonneg_right ht_mem.2 (le_of_lt hα_pos)
      have h_tα_lower : (t₀ - δ) * α < t * α :=
        mul_lt_mul_of_pos_right ht_mem.1 hα_pos
      refine ⟨?_, ?_⟩
      · -- -ε ≤ H - t*α - s.im
        linarith [ht₀_mul]
      · -- H - t*α - s.im ≤ ε
        linarith [ht₀_mul]
    simp [if_neg (not_lt.mpr h_norm)]
  -- Integrability of cutoff
  have hF_int₀ : IntervalIntegrable F volume 0 (t₀ - δ) :=
    hint₀.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_left.mono (fun t ht hm => (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δ) (t₀ + δ) :=
    (IntervalIntegrable.zero (μ := volume) (a := t₀ - δ) (b := t₀ + δ)).congr
      (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (t₀ + δ) 5 :=
    hint_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_right.mono (fun t ht hm => (ht hm).symm)))
  -- Split the integral
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(t₀ - δ), F t) + (∫ t in (t₀ - δ)..(t₀ + δ), F t) +
      (∫ t in (t₀ + δ)..(5:ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int₀.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int₀ hF_int_mid]
  have h_mid_zero : ∫ t in (t₀ - δ)..(t₀ + δ), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_mid t ht))]
    simp [intervalIntegral.integral_zero]
  -- Convert F integrals to deriv g / g integrals
  have h_eq_left : ∫ t in (0:ℝ)..(t₀ - δ), F t = ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_left
  have h_eq_right : ∫ t in (t₀ + δ)..(5:ℝ), F t = ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_right
  -- FTC values via smooth representatives
  have h_ftc₀ : ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (-(h₀ (t₀ - δ))) - Complex.log (-(h₀ 0)) := by
    rw [← piece₀.2, intervalIntegral.integral_congr_ae
      ((h_ae₀ 0 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono (fun t ht hm => ht hm))]
  have h_ftc₁ : ∫ t in (t₀ + δ)..(1:ℝ), deriv g t / g t =
      Complex.log (-(h₀ 1)) - Complex.log (-(h₀ (t₀ + δ))) := by
    rw [← piece₁.2, intervalIntegral.integral_congr_ae
      ((h_ae₀ (t₀ + δ) 1 (by linarith) (by linarith) le_rfl).mono (fun t ht hm => ht hm))]
  have h_ftc_arc : ∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t =
      Complex.log (-(h_arc 3)) - Complex.log (-(h_arc 1)) := by
    rw [← piece₂.2, intervalIntegral.integral_congr_ae
      (h_ae_arc.mono (fun t ht hm => ht hm))]
  have h_ftc₃ : ∫ t in (3:ℝ)..(4:ℝ), deriv g t / g t =
      Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3)) := by
    rw [← piece₃.2, intervalIntegral.integral_congr_ae
      (h_ae₃.mono (fun t ht hm => ht hm))]
  have h_ftc₅ : ∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t =
      Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)) := by
    rw [← piece₄.2, intervalIntegral.integral_congr_ae
      (h_ae₅.mono (fun t ht hm => ht hm))]
  -- Combine integrals by adjacent intervals
  have h_right_total : ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t =
      Complex.log (-(h₀ 1)) - Complex.log (-(h₀ (t₀ + δ))) +
      (Complex.log (-(h_arc 3)) - Complex.log (-(h_arc 1))) +
      (Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3))) +
      (Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4))) := by
    have h_split_right : (∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t) =
      (∫ t in (t₀ + δ)..(1:ℝ), deriv g t / g t) +
      (∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t) +
      (∫ t in (3:ℝ)..(4:ℝ), deriv g t / g t) +
      (∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t) := by
        have h1 : (∫ t in (t₀ + δ)..(1:ℝ), deriv g t / g t) + (∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t) =
            ∫ t in (t₀ + δ)..(3:ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hint₁ hint_arc]
        have h2 : (∫ t in (t₀ + δ)..(3:ℝ), deriv g t / g t) + (∫ t in (3:ℝ)..(4:ℝ), deriv g t / g t) =
            ∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals (hint₁.trans hint_arc) hint₃]
        have h3 : (∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t) + (∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t) =
            ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals ((hint₁.trans hint_arc).trans hint₃) hint₅]
        rw [← h3, ← h2, ← h1]
    rw [h_split_right, h_ftc₁, h_ftc_arc, h_ftc₃, h_ftc₅]
  -- Telescope: intermediate log terms cancel due to endpoint agreement
  have h_telescope : Complex.log (-(h₀ (t₀ - δ))) - Complex.log (-(h₀ 0)) +
      (Complex.log (-(h₀ 1)) - Complex.log (-(h₀ (t₀ + δ))) +
      (Complex.log (-(h_arc 3)) - Complex.log (-(h_arc 1))) +
      (Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3))) +
      (Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)))) =
      Complex.log (-(h₀ (t₀ - δ))) - Complex.log (-(h₀ (t₀ + δ))) := by
    rw [hep_1, hep_3, hep_4, hep_01]; ring
  -- Now compute: show the original cutoff integral = -πI
  show ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) = -(↑Real.pi * I)
  -- Step 1: split into three pieces
  have h_step1 : ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t) + (∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t) := by
    calc ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
        = ∫ t in (0:ℝ)..5, F t := rfl
      _ = _ + _ + _ := h_split
      _ = _ + 0 + _ := by rw [h_mid_zero]
      _ = _ := by rw [add_zero, h_eq_left, h_eq_right]
  -- Step 2: FTC on each piece
  rw [h_step1, h_ftc₀, h_right_total, h_telescope]
  -- Remaining: log(-(h₀(t₀-δ))) - log(-(h₀(t₀+δ))) = -πI
  have hval_minus : h₀ (t₀ - δ) = ↑(δ * α) * I := by
    show fdBoundary_seg1_H H (t₀ - δ) - s = _
    have h_sub : (t₀ - δ) * α = t₀ * α - δ * α := sub_mul t₀ δ α
    have hval : H - (t₀ - δ) * α - s.im = δ * α := by linarith [ht₀_mul]
    rw [rightEdge_h₀_eq hs_re, show H - Real.sqrt 3 / 2 = α from hα_def.symm, hval]
  have hval_plus : h₀ (t₀ + δ) = ↑(-(δ * α)) * I := by
    show fdBoundary_seg1_H H (t₀ + δ) - s = _
    have h_add : (t₀ + δ) * α = t₀ * α + δ * α := add_mul t₀ δ α
    have hval : H - (t₀ + δ) * α - s.im = -(δ * α) := by linarith [ht₀_mul]
    rw [rightEdge_h₀_eq hs_re, show H - Real.sqrt 3 / 2 = α from hα_def.symm, hval]
  rw [hval_minus, hval_plus]
  rw [show -(↑(δ * α) * I : ℂ) = ↑(δ * α) * (-I) from by ring,
      show -(↑(-(δ * α)) * I : ℂ) = ↑(δ * α) * I from by push_cast; ring]
  have hdα_pos : 0 < δ * α := mul_pos hδ_pos hα_pos
  rw [Complex.log_ofReal_mul hdα_pos (show (-I : ℂ) ≠ 0 from neg_ne_zero.mpr I_ne_zero),
      Complex.log_ofReal_mul hdα_pos I_ne_zero,
      Complex.log_neg_I, Complex.log_I]
  ring

/-! ## Left Edge Helper Lemmas -/

/-- For a point on the left edge, `t₀ = 3 + (s.im - √3/2) / α` is in `(3, 4)`. -/
private lemma leftEdge_t₀_mem_Ioo (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H) (s : ℂ)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    3 + (s.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) ∈ Ioo (3 : ℝ) 4 := by
  have hα_pos : 0 < H - Real.sqrt 3 / 2 := by linarith
  constructor
  · linarith [div_pos (by linarith : (0:ℝ) < s.im - Real.sqrt 3 / 2) hα_pos]
  · have : (s.im - Real.sqrt 3 / 2) / (H - Real.sqrt 3 / 2) < 1 :=
      (div_lt_one hα_pos).mpr (by linarith)
    linarith

/-- On seg4, `g(t) = (√3/2 + (t-3)·α - s.im) * I` when `s.re = -1/2`. -/
private lemma leftEdge_h₃_eq {H : ℝ} {s : ℂ} (hs_re : s.re = -1/2) (t : ℝ) :
    fdBoundary_seg4_H H t - s =
      ↑(Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) - s.im) * I := by
  simp only [fdBoundary_seg4_H]
  apply Complex.ext <;>
    simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, hs_re]

/-- Left edge separation: seg1 (re=1/2) is at distance ≥ 1 from s with re=-1/2. -/
private lemma leftEdge_dist_from_rightVertical (s : ℂ) (hs_re : s.re = -1/2)
    (z : ℂ) (hz_re : z.re = 1/2) : 1 ≤ ‖z - s‖ := by
  have hre : (z - s).re = 1 := by simp [Complex.sub_re, hz_re, hs_re]; ring
  calc 1 = |(z - s).re| := by rw [hre]; norm_num
    _ ≤ ‖z - s‖ := abs_re_le_norm (z - s)

/-- Minimum distance for left edge: d > 0. -/
private lemma leftEdge_min_dist_pos (s : ℂ) (hs_norm : ‖s‖ > 1) (hs_im : s.im < H) :
    0 < min (min (‖s‖ - 1) 1) (H - s.im) :=
  lt_min (lt_min (by linarith) one_pos) (by linarith)

/-- Non-seg4 segments of fdBoundary_H stay at distance ≥ d from left edge point s. -/
private lemma leftEdge_min_dist_from_non_seg4 (H : ℝ) (s : ℂ) (hs_re : s.re = -1/2)
    (hs_norm : ‖s‖ > 1) (hs_im : s.im < H) (t : ℝ) (ht_seg4_left : t ≤ 3)
    (ht_upper : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundary_H H t - s‖ := by
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  by_cases h1 : t ≤ 1
  · -- Seg1: re = 1/2, dist ≥ 1
    rw [fdBoundary_H_eq_seg1_H h1]
    have hre : (fdBoundary_seg1_H H t).re = 1/2 := by
      simp [fdBoundary_seg1_H, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    calc d ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
      _ ≤ _ := leftEdge_dist_from_rightVertical s hs_re _ hre
  · push_neg at h1
    by_cases h3 : t ≤ 3
    · -- Arc: ‖z‖ = 1, dist ≥ ‖s‖ - 1
      have h_on_arc : ‖fdBoundary_H H t‖ = 1 := by
        by_cases h2 : t ≤ 2
        · rw [fdBoundary_H_eq_seg2_H (not_le.mpr h1) h2]
          simp only [fdBoundary_seg2_H, fdBoundary_seg2]
          rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
              ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
        · push_neg at h2
          rw [fdBoundary_H_eq_seg3_H (not_le.mpr h1) (not_le.mpr h2) h3]
          simp only [fdBoundary_seg3_H, fdBoundary_seg3]
          rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
              ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I
              from by push_cast; ring]
          exact Complex.norm_exp_ofReal_mul_I _
      calc d ≤ ‖s‖ - 1 := le_trans (min_le_left _ _) (min_le_left _ _)
        _ ≤ _ := rightEdge_dist_from_arc s _ h_on_arc
    · -- Can't reach: t ≤ 3 assumed
      exact absurd ht_seg4_left h3

-- Also need: non-seg4 from the RIGHT side (t > 4)
private lemma leftEdge_min_dist_from_non_seg4_right (H : ℝ) (s : ℂ) (hs_re : s.re = -1/2)
    (hs_norm : ‖s‖ > 1) (hs_im : s.im < H) (t : ℝ) (ht4 : 4 < t) (ht5 : t ≤ 5) :
    min (min (‖s‖ - 1) 1) (H - s.im) ≤ ‖fdBoundary_H H t - s‖ := by
  -- Seg5: im = H, dist ≥ H - s.im
  rw [fdBoundary_H_eq_seg5_H (not_le.mpr (by linarith : 1 < t))
      (not_le.mpr (by linarith : 2 < t)) (not_le.mpr (by linarith : 3 < t))
      (not_le.mpr ht4)]
  have him : (fdBoundary_seg5_H H t - s).im = H - s.im := by
    simp [fdBoundary_seg5_H, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  calc min (min (‖s‖ - 1) 1) (H - s.im)
      ≤ H - s.im := min_le_right _ _
    _ = |(fdBoundary_seg5_H H t - s).im| := by rw [him]; exact (abs_of_pos (by linarith)).symm
    _ ≤ ‖fdBoundary_seg5_H H t - s‖ := Complex.abs_im_le_norm _

/-! ## Left Edge Main Theorem -/

set_option maxHeartbeats 8000000 in
private lemma leftEdge_winding_aux (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1/2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - s‖ > ε then
        (fdBoundary_H H t - s)⁻¹ * deriv (fun u => fdBoundary_H H u - s) t else 0) =
      -(↑Real.pi * I) := by
  -- Setup notation
  set g : ℝ → ℂ := fun t => fdBoundary_H H t - s with hg_def
  set α := H - Real.sqrt 3 / 2 with hα_def
  -- t₀ is the crossing parameter on seg4
  set t₀ := 3 + (s.im - Real.sqrt 3 / 2) / α with ht₀_def
  have hα_pos : 0 < α := by rw [hα_def]; linarith
  have hα_ne : α ≠ 0 := ne_of_gt hα_pos
  have ht₀_Ioo := leftEdge_t₀_mem_Ioo H hH_sqrt s hs_im_lower hs_im
  have ht₀_gt3 : 3 < t₀ := ht₀_Ioo.1
  have ht₀_lt4 : t₀ < 4 := ht₀_Ioo.2
  have ht₀_sub3_pos : 0 < t₀ - 3 := by linarith
  have ht₀_sub3_lt1 : t₀ - 3 < 1 := by linarith
  have ht₀_mul : (t₀ - 3) * α = s.im - Real.sqrt 3 / 2 := by
    simp only [ht₀_def, add_sub_cancel_left]
    exact div_mul_cancel₀ _ hα_ne
  -- Smooth representatives for each segment (same as right edge)
  set h₀ : ℝ → ℂ := fun t => fdBoundary_seg1_H H t - s
  set h_arc : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
  set h₃ : ℝ → ℂ := fun t => fdBoundary_seg4_H H t - s
  set h₅ : ℝ → ℂ := fun t => fdBoundary_seg5_H H t - s
  -- HasDerivAt for each
  have hd₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg1_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd_arc : ∀ t : ℝ, HasDerivAt h_arc
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_rep s
  have hd₃ : ∀ t : ℝ, HasDerivAt h₃ ((↑α : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg4_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp [hα_def])
  have hd₅ : ∀ t : ℝ, HasDerivAt h₅ 1 t := by
    intro t; exact (hasDerivAt_fdBoundary_seg5_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp)
  -- Value agreement: g = hₖ on each segment (same as right edge)
  have hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; simp only [hg_def, h₀]; rw [fdBoundary_H_eq_seg1_H ht]
  have hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t := by
    intro t ht1 ht3; simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t := by
    intro t ht3 ht4; simp only [hg_def, h₃]
    rw [fdBoundary_H_eq_seg4_H (not_le.mpr (by linarith : 1 < t))
        (not_le.mpr (by linarith : 2 < t)) (not_le.mpr ht3) ht4]
  have hg_h₅ : ∀ t, 4 < t → g t = h₅ t := by
    intro t ht4; simp only [hg_def, h₅]
    rw [fdBoundary_H_eq_seg5_H (not_le.mpr (by linarith : 1 < t))
        (not_le.mpr (by linarith : 2 < t)) (not_le.mpr (by linarith : 3 < t))
        (not_le.mpr ht4)]
  -- Endpoint value agreement (same as right edge)
  have hep_01 : h₀ 0 = h₅ 5 := by
    simp only [h₀, h₅, fdBoundary_seg1_H, fdBoundary_seg5_H]; push_cast; ring
  have hep_1 : h₀ 1 = h_arc 1 := by
    simp only [h₀, h_arc, fdBoundary_seg1_H]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hep_3 : h_arc 3 = h₃ 3 := by
    simp only [h_arc, h₃, fdBoundary_seg4_H]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hep_4 : h₃ 4 = h₅ 4 := by
    simp only [h₃, h₅, fdBoundary_seg4_H, fdBoundary_seg5_H]; push_cast; ring
  -- Derivative agreement (same as right edge)
  have hderiv_01 : ∀ t ∈ Ioo (0:ℝ) 1, deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Iio_mem_nhds ht1) (fun s hs => hg_h₀ s (le_of_lt hs)))
  have hderiv_arc : ∀ t ∈ Ioo (1:ℝ) 3, deriv g t = deriv h_arc t := by
    intro t ⟨ht1, ht3⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht3) (fun s hs => hg_arc s hs.1 hs.2))
  have hderiv_3 : ∀ t ∈ Ioo (3:ℝ) 4, deriv g t = deriv h₃ t := by
    intro t ⟨ht3, ht4⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht3 ht4)
        (fun s hs => hg_h₃ s hs.1 (le_of_lt hs.2)))
  have hderiv_5 : ∀ t ∈ Ioo (4:ℝ) 5, deriv g t = deriv h₅ t := by
    intro t ⟨ht4, _⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_h₅ s hs))
  -- slitPlane conditions: h stays in slitPlane (NOT -h, unlike right edge)
  have hslit₀ : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ Complex.slitPlane := by
    intro t _
    rw [Complex.mem_slitPlane_iff]; left
    simp only [h₀, fdBoundary_seg1_H, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_one, mul_zero, add_zero, sub_zero]
    rw [hs_re]; norm_num
  have hslit_arc : ∀ t ∈ Icc (1:ℝ) 3, h_arc t ∈ Complex.slitPlane := by
    intro t ⟨ht1, ht3⟩
    rw [Complex.mem_slitPlane_iff]
    simp only [h_arc]
    set θ := Real.pi * (1 + t) / 6 with hθ_def
    have hθ_lower : Real.pi / 3 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    have hθ_upper : θ ≤ 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
    by_cases h3_eq : t = 3
    · -- At t=3: θ = 2π/3, cos = -1/2, re = 0, need im ≠ 0
      right
      subst h3_eq
      show (cexp (↑(Real.pi * (1 + 3) / 6) * I) - s).im ≠ 0
      rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
          exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
      linarith [hs_im_lower]
    · -- For t < 3: cos(θ) > -1/2 so re > 0
      left
      have ht3_strict : t < 3 := lt_of_le_of_ne ht3 h3_eq
      have hθ_strict : θ < 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith [Real.pi_pos]
      show 0 < (cexp (↑θ * I) - s).re
      simp only [Complex.sub_re, exp_ofReal_mul_I_re]
      rw [hs_re]
      -- cos(θ) > cos(2π/3) = -1/2 for θ < 2π/3
      have hcos_gt : Real.cos θ > -(1 / 2) := by
        have h := Real.cos_lt_cos_of_nonneg_of_le_pi
          (le_of_lt (by nlinarith [Real.pi_pos])) (by nlinarith [Real.pi_pos]) hθ_strict
        rw [cos_two_pi_div_three] at h; linarith
      linarith
  have hslit₃_left : ∀ δ', 0 < δ' → δ' < t₀ - 3 →
      ∀ t ∈ Icc (3:ℝ) (t₀ - δ'), h₃ t ∈ Complex.slitPlane := by
    intro δ' hδ' hδ't₀ t ⟨ht3, htd⟩
    rw [Complex.mem_slitPlane_iff]; right
    show (fdBoundary_seg4_H H t - s).im ≠ 0
    rw [leftEdge_h₃_eq hs_re]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    -- Need √3/2 + (t-3)·α - s.im ≠ 0
    have : (t - 3) * α < s.im - Real.sqrt 3 / 2 := by
      calc (t - 3) * α ≤ (t₀ - δ' - 3) * α := by nlinarith
        _ = (t₀ - 3) * α - δ' * α := by ring
        _ = (s.im - Real.sqrt 3 / 2) - δ' * α := by rw [ht₀_mul]
        _ < s.im - Real.sqrt 3 / 2 := by nlinarith
    rw [hα_def] at this; intro h; linarith
  have hslit₃_right : ∀ δ', 0 < δ' → δ' < 4 - t₀ →
      ∀ t ∈ Icc (t₀ + δ') 4, h₃ t ∈ Complex.slitPlane := by
    intro δ' hδ' hδ'4 t ⟨htd, ht4⟩
    rw [Complex.mem_slitPlane_iff]; right
    show (fdBoundary_seg4_H H t - s).im ≠ 0
    rw [leftEdge_h₃_eq hs_re]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
    have : (t - 3) * α > s.im - Real.sqrt 3 / 2 := by
      calc (t - 3) * α ≥ (t₀ + δ' - 3) * α := by nlinarith
        _ = (t₀ - 3) * α + δ' * α := by ring
        _ = (s.im - Real.sqrt 3 / 2) + δ' * α := by rw [ht₀_mul]
        _ > s.im - Real.sqrt 3 / 2 := by nlinarith
    rw [hα_def] at this; intro h; linarith
  have hslit₅ : ∀ t ∈ Icc (4:ℝ) 5, h₅ t ∈ Complex.slitPlane := by
    intro t ⟨ht4, ht5⟩
    rw [Complex.mem_slitPlane_iff]
    simp only [h₅, fdBoundary_seg5_H]
    by_cases ht4_eq : t = 4
    · right
      subst ht4_eq
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith
    · left
      have : 4 < t := lt_of_le_of_ne ht4 (Ne.symm ht4_eq)
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      rw [hs_re]; linarith
  -- Apply ftc_log on each sub-interval (using ftc_log, not ftc_log_neg)
  -- Choose ε₀
  set d := min (min (‖s‖ - 1) 1) (H - s.im)
  have hd_pos : 0 < d := leftEdge_min_dist_pos s hs_norm hs_im
  set ε₀ := min d (min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)))
  have hε₀_pos : 0 < ε₀ := by
    refine lt_min hd_pos (lt_min (mul_pos hd_pos hα_pos)
      (lt_min (mul_pos ht₀_sub3_pos hα_pos) (mul_pos (by linarith) hα_pos)))
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨Ioo 0 ε₀, Ioo_mem_nhdsGT hε₀_pos, fun ε hε => ?_⟩
  obtain ⟨hε_pos, hε_lt⟩ := hε
  have hε_lt_d : ε < d := calc ε < ε₀ := hε_lt
      _ ≤ d := min_le_left _ _
  have hεα_lt_d : ε / α < d := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)) := min_le_right _ _
      _ ≤ d * α := min_le_left _ _
  have hεα_lt_t₀m3 : ε / α < t₀ - 3 := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)) := min_le_right _ _
      _ ≤ min ((t₀ - 3) * α) ((4 - t₀) * α) := min_le_right _ _
      _ ≤ (t₀ - 3) * α := min_le_left _ _
  have hεα_lt_4mt₀ : ε / α < 4 - t₀ := by
    rw [div_lt_iff₀ hα_pos]
    calc ε < ε₀ := hε_lt
      _ ≤ min (d * α) (min ((t₀ - 3) * α) ((4 - t₀) * α)) := min_le_right _ _
      _ ≤ min ((t₀ - 3) * α) ((4 - t₀) * α) := min_le_right _ _
      _ ≤ (4 - t₀) * α := min_le_right _ _
  set δ := ε / α with hδ_def
  have hδ_pos : 0 < δ := div_pos hε_pos hα_pos
  -- g = deriv g convention
  have hderiv_eq : deriv (fun u => fdBoundary_H H u - s) = deriv g := rfl
  rw [show (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ *
    deriv (fun u => fdBoundary_H H u - s) t else 0) =
    (∫ t in (0:ℝ)..5, if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) from rfl]
  -- FTC on each piece using ftc_log
  -- Piece 0: [0, 1] (seg1)
  have piece₀ := ftc_log (by norm_num : (0:ℝ) ≤ 1)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑α : ℂ) * I from funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    hslit₀
  -- Piece 1: [1, 3] (arc)
  have h_arc_cont : Continuous h_arc := by
    simp only [h_arc]; exact (Continuous.cexp (by fun_prop)).sub continuous_const
  have piece₁ := ftc_log (by norm_num : (1:ℝ) ≤ 3)
    h_arc_cont.continuousOn
    (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc
  -- Piece 2: [3, t₀-δ] (seg4, below crossing)
  have piece₂ := ftc_log (by linarith : (3:ℝ) ≤ t₀ - δ)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    (hslit₃_left δ hδ_pos hεα_lt_t₀m3)
  -- Piece 3: [t₀+δ, 4] (seg4, above crossing)
  have piece₃ := ftc_log (by linarith : t₀ + δ ≤ 4)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑α : ℂ) * I from funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    (hslit₃_right δ hδ_pos hεα_lt_4mt₀)
  -- Piece 4: [4, 5] (seg5)
  have piece₄ := ftc_log (by norm_num : (4:ℝ) ≤ 5)
    ((continuous_fdBoundary_seg5_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₅ t).differentiableAt)
    (by rw [show deriv h₅ = fun _ => (1 : ℂ) from funext fun t => (hd₅ t).deriv]
        exact continuousOn_const)
    hslit₅
  -- Convert from hₖ integrands to g integrands via a.e. equality
  have h_ae₀ : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 1 → deriv h₀ t / h₀ t = deriv g t / g t := by
    have h_excl : ({0, 1} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({0, 1} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht_mem
    have ht0 : 0 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff]; left; linarith)
      · exact h
    have ht1 : t < 1 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₀ t (le_of_lt ht1), hderiv_01 t ⟨ht0, ht1⟩]
  have h_ae_arc : ∀ᵐ t ∂volume, t ∈ Set.uIoc 1 3 → deriv h_arc t / h_arc t = deriv g t / g t := by
    have : ({1, 3} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact ((Set.toFinite ({1, 3} : Set ℝ)).measure_zero volume))
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht_mem
    have ht1 : 1 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht3 : t < 3 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_arc t ht1 ht3, hderiv_arc t ⟨ht1, ht3⟩]
  have h_ae₃ : ∀ a b : ℝ, 3 ≤ a → a < b → b ≤ 4 →
      ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → deriv h₃ t / h₃ t = deriv g t / g t := by
    intro a b ha_ge hab hb4
    have h_excl : ({a, b} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({a, b} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht
    rw [Set.uIoc_of_le (le_of_lt hab)] at ht
    have ht_gt_a : a < t := by
      rcases eq_or_lt_of_le (le_of_lt ht.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff]; left; linarith)
      · exact h
    have ht_lt_b : t < b := by
      rcases eq_or_lt_of_le ht.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    have ht3 : 3 < t := by linarith
    have ht4 : t < 4 := by linarith
    rw [hg_h₃ t ht3 (le_of_lt ht4), hderiv_3 t ⟨ht3, ht4⟩]
  have h_ae₅ : ∀ᵐ t ∂volume, t ∈ Set.uIoc 4 5 → deriv h₅ t / h₅ t = deriv g t / g t := by
    have : ({4, 5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({4, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [this] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at ht_mem
    have ht4 : 4 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht5 : t < 5 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₅ t ht4, hderiv_5 t ⟨ht4, ht5⟩]
  -- Transfer integrability from hₖ to g
  have hint₀ : IntervalIntegrable (fun t => deriv g t / g t) volume 0 1 :=
    piece₀.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₀.mono (fun t ht hm => ht hm)))
  have hint_arc : IntervalIntegrable (fun t => deriv g t / g t) volume 1 3 :=
    piece₁.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_arc.mono (fun t ht hm => ht hm)))
  have hint₃_left : IntervalIntegrable (fun t => deriv g t / g t) volume 3 (t₀ - δ) :=
    piece₂.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₃ 3 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono
        (fun t ht hm => ht hm)))
  have hint₃_right : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 4 :=
    piece₃.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      ((h_ae₃ (t₀ + δ) 4 (by linarith) (by linarith) le_rfl).mono
        (fun t ht hm => ht hm)))
  have hint₅ : IntervalIntegrable (fun t => deriv g t / g t) volume 4 5 :=
    piece₄.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae₅.mono (fun t ht hm => ht hm)))
  -- Combined integrability
  have hint_left : IntervalIntegrable (fun t => deriv g t / g t) volume 0 (t₀ - δ) :=
    hint₀.trans hint_arc |>.trans hint₃_left
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 5 :=
    hint₃_right.trans hint₅
  -- Cutoff function
  set F := fun t => if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else (0 : ℂ)
  -- On [0, t₀-δ]: ‖g(t)‖ > ε
  have hF_left : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (t₀ - δ) →
      F t = deriv g t / g t := by
    have h_excl : ({0, t₀ - δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({0, t₀ - δ} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ t₀ - δ)] at ht_mem
    have h_norm_gt : ‖g t‖ > ε := by
      by_cases ht3 : t ≤ 3
      · -- On [0, 3]: separated by d > ε
        have ht5 : t ≤ 5 := by linarith
        have : d ≤ ‖g t‖ := by
          show d ≤ ‖fdBoundary_H H t - s‖
          exact leftEdge_min_dist_from_non_seg4 H s hs_re hs_norm hs_im t ht3 ht5
        linarith [hε_lt_d]
      · -- On (3, t₀-δ]: on seg4, ‖g‖ > ε
        push_neg at ht3
        have ht4 : t ≤ 4 := by linarith [ht_mem.2]
        show ‖fdBoundary_H H t - s‖ > ε
        rw [fdBoundary_H_eq_seg4_H (not_le.mpr (by linarith : 1 < t))
            (not_le.mpr (by linarith : 2 < t)) (not_le.mpr ht3) ht4]
        rw [leftEdge_h₃_eq hs_re]
        rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
        have ht_lt_t₀mδ : t < t₀ - δ := by
          rcases eq_or_lt_of_le ht_mem.2 with h | h
          · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; exact h)
          · exact h
        have h_im_neg : Real.sqrt 3 / 2 + (t - 3) * α - s.im < 0 := by
          have : (t - 3) * α < (t₀ - δ - 3) * α := mul_lt_mul_of_pos_right (by linarith) hα_pos
          have : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
          have := mul_pos hδ_pos hα_pos; linarith [ht₀_mul]
        rw [abs_of_neg h_im_neg]
        have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
        have : (t - 3) * α < (t₀ - δ - 3) * α := mul_lt_mul_of_pos_right (by linarith) hα_pos
        have : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
        linarith [ht₀_mul]
    show F t = deriv g t / g t
    simp only [F, if_pos h_norm_gt]
    rw [div_eq_mul_inv, mul_comm]
  -- On [t₀+δ, 5]: ‖g(t)‖ > ε
  have hF_right : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ + δ) 5 →
      F t = deriv g t / g t := by
    have h_boundary : ({t₀ + δ, 5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({t₀ + δ, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [h_boundary] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ + δ ≤ 5)] at ht_mem
    have h_norm_gt : ‖g t‖ > ε := by
      by_cases ht4 : t ≤ 4
      · -- On [t₀+δ, 4]: on seg4, ‖g‖ > ε
        show ‖fdBoundary_H H t - s‖ > ε
        rw [fdBoundary_H_eq_seg4_H (not_le.mpr (by linarith [ht_mem.1] : 1 < t))
            (not_le.mpr (by linarith [ht_mem.1] : 2 < t)) (not_le.mpr (by linarith [ht_mem.1] : 3 < t)) ht4]
        rw [leftEdge_h₃_eq hs_re]
        rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
        have h_tα : (t₀ + δ - 3) * α < (t - 3) * α :=
          mul_lt_mul_of_pos_right (by linarith [ht_mem.1]) hα_pos
        have h_expand : (t₀ + δ - 3) * α = (t₀ - 3) * α + δ * α := by ring
        have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
        have h_im_pos : Real.sqrt 3 / 2 + (t - 3) * α - s.im > 0 := by linarith [ht₀_mul]
        rw [abs_of_pos h_im_pos]; linarith [ht₀_mul]
      · -- On (4, 5]: separated by d > ε
        push_neg at ht4
        have : d ≤ ‖g t‖ := by
          show d ≤ ‖fdBoundary_H H t - s‖
          exact leftEdge_min_dist_from_non_seg4_right H s hs_re hs_norm hs_im t ht4 ht_mem.2
        linarith [hε_lt_d]
    show F t = deriv g t / g t
    simp only [F, if_pos h_norm_gt]
    rw [div_eq_mul_inv, mul_comm]
  -- On [t₀-δ, t₀+δ]: ‖g(t)‖ ≤ ε, so F = 0
  have hF_mid : ∀ t ∈ Set.uIoc (t₀ - δ) (t₀ + δ), F t = 0 := by
    intro t ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ - δ ≤ t₀ + δ)] at ht_mem
    simp only [F]
    have h_norm : ‖g t‖ ≤ ε := by
      show ‖fdBoundary_H H t - s‖ ≤ ε
      rw [fdBoundary_H_eq_seg4_H (not_le.mpr (by linarith [ht_mem.1] : 1 < t))
          (not_le.mpr (by linarith [ht_mem.1] : 2 < t))
          (not_le.mpr (by linarith [ht_mem.1] : 3 < t))
          (by linarith [ht_mem.2, hεα_lt_4mt₀] : t ≤ 4)]
      rw [leftEdge_h₃_eq hs_re]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_le]
      have hε_eq : ε = δ * α := by rw [hδ_def]; field_simp
      have h_upper : (t₀ + δ - 3) * α = (t₀ - 3) * α + δ * α := by ring
      have h_lower : (t₀ - δ - 3) * α = (t₀ - 3) * α - δ * α := by ring
      have h_tα_upper : (t - 3) * α ≤ (t₀ + δ - 3) * α :=
        mul_le_mul_of_nonneg_right (by linarith [ht_mem.2]) (le_of_lt hα_pos)
      have h_tα_lower : (t₀ - δ - 3) * α < (t - 3) * α :=
        mul_lt_mul_of_pos_right (by linarith [ht_mem.1]) hα_pos
      have h_conv : (t - 3) * (H - Real.sqrt 3 / 2) = (t - 3) * α := by rw [hα_def]
      constructor <;> linarith [ht₀_mul, h_conv]
    simp [if_neg (not_lt.mpr h_norm)]
  -- Integrability of cutoff
  have hF_int₀ : IntervalIntegrable F volume 0 (t₀ - δ) :=
    hint_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_left.mono (fun t ht hm => (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δ) (t₀ + δ) :=
    (IntervalIntegrable.zero (μ := volume) (a := t₀ - δ) (b := t₀ + δ)).congr
      (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (t₀ + δ) 5 :=
    hint_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_right.mono (fun t ht hm => (ht hm).symm)))
  -- Split the integral
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(t₀ - δ), F t) + (∫ t in (t₀ - δ)..(t₀ + δ), F t) +
      (∫ t in (t₀ + δ)..(5:ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int₀.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int₀ hF_int_mid]
  have h_mid_zero : ∫ t in (t₀ - δ)..(t₀ + δ), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae (ae_of_all _ (fun t ht => hF_mid t ht))]
    simp [intervalIntegral.integral_zero]
  -- Convert F integrals to deriv g / g integrals
  have h_eq_left : ∫ t in (0:ℝ)..(t₀ - δ), F t = ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_left
  have h_eq_right : ∫ t in (t₀ + δ)..(5:ℝ), F t = ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_right
  -- FTC values via smooth representatives (using ftc_log)
  have h_ftc₀ : ∫ t in (0:ℝ)..(1:ℝ), deriv g t / g t =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) := by
    rw [← piece₀.2, intervalIntegral.integral_congr_ae
      (h_ae₀.mono (fun t ht hm => ht hm))]
  have h_ftc_arc : ∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t =
      Complex.log (h_arc 3) - Complex.log (h_arc 1) := by
    rw [← piece₁.2, intervalIntegral.integral_congr_ae
      (h_ae_arc.mono (fun t ht hm => ht hm))]
  have h_ftc₃_left : ∫ t in (3:ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3) := by
    rw [← piece₂.2, intervalIntegral.integral_congr_ae
      ((h_ae₃ 3 (t₀ - δ) le_rfl (by linarith) (by linarith)).mono (fun t ht hm => ht hm))]
  have h_ftc₃_right : ∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t =
      Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) := by
    rw [← piece₃.2, intervalIntegral.integral_congr_ae
      ((h_ae₃ (t₀ + δ) 4 (by linarith) (by linarith) le_rfl).mono (fun t ht hm => ht hm))]
  have h_ftc₅ : ∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t =
      Complex.log (h₅ 5) - Complex.log (h₅ 4) := by
    rw [← piece₄.2, intervalIntegral.integral_congr_ae
      (h_ae₅.mono (fun t ht hm => ht hm))]
  -- Combine integrals by adjacent intervals
  have h_left_total : ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) +
      (Complex.log (h_arc 3) - Complex.log (h_arc 1)) +
      (Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3)) := by
    have h_split_left : (∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t) =
      (∫ t in (0:ℝ)..(1:ℝ), deriv g t / g t) +
      (∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t) +
      (∫ t in (3:ℝ)..(t₀ - δ), deriv g t / g t) := by
        have h1 : (∫ t in (0:ℝ)..(1:ℝ), deriv g t / g t) + (∫ t in (1:ℝ)..(3:ℝ), deriv g t / g t) =
            ∫ t in (0:ℝ)..(3:ℝ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals hint₀ hint_arc]
        have h2 : (∫ t in (0:ℝ)..(3:ℝ), deriv g t / g t) + (∫ t in (3:ℝ)..(t₀ - δ), deriv g t / g t) =
            ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t := by
          rw [← intervalIntegral.integral_add_adjacent_intervals (hint₀.trans hint_arc) hint₃_left]
        rw [← h2, ← h1]
    rw [h_split_left, h_ftc₀, h_ftc_arc, h_ftc₃_left]
  have h_right_total : ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t =
      Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) +
      (Complex.log (h₅ 5) - Complex.log (h₅ 4)) := by
    have h_split_right : (∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t) =
      (∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t) +
      (∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hint₃_right hint₅]
    rw [h_split_right, h_ftc₃_right, h_ftc₅]
  -- Telescope: intermediate log terms cancel due to endpoint agreement
  have h_telescope : Complex.log (h₀ 1) - Complex.log (h₀ 0) +
      (Complex.log (h_arc 3) - Complex.log (h_arc 1)) +
      (Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ 3)) +
      (Complex.log (h₃ 4) - Complex.log (h₃ (t₀ + δ)) +
      (Complex.log (h₅ 5) - Complex.log (h₅ 4))) =
      Complex.log (h₃ (t₀ - δ)) - Complex.log (h₃ (t₀ + δ)) := by
    rw [hep_1, hep_3, hep_4, hep_01]; ring
  -- Now compute: show the cutoff integral = -πI
  show ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) = -(↑Real.pi * I)
  -- Step 1: split into three pieces
  have h_step1 : ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      (∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t) + (∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t) := by
    calc ∫ t in (0:ℝ)..5, (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0)
        = ∫ t in (0:ℝ)..5, F t := rfl
      _ = _ + _ + _ := h_split
      _ = _ + 0 + _ := by rw [h_mid_zero]
      _ = _ := by rw [add_zero, h_eq_left, h_eq_right]
  -- Step 2: FTC on each piece, telescope, then log computation
  rw [h_step1, h_left_total, h_right_total, h_telescope]
  -- Goal: log(h₃(t₀-δ)) - log(h₃(t₀+δ)) = -(↑π * I)
  -- Step 3: Compute h₃(t₀±δ) as pure imaginary values
  have hval_minus : h₃ (t₀ - δ) = ↑(-(δ * α)) * I := by
    show fdBoundary_seg4_H H (t₀ - δ) - s = _
    rw [leftEdge_h₃_eq hs_re]
    have h_expand : (t₀ - δ - 3) * (H - Real.sqrt 3 / 2) = (t₀ - 3) * α - δ * α := by
      rw [hα_def]; ring
    have h_eq' : Real.sqrt 3 / 2 + (t₀ - δ - 3) * (H - Real.sqrt 3 / 2) - s.im = -(δ * α) := by
      rw [h_expand]; linarith [ht₀_mul]
    rw [h_eq']
  have hval_plus : h₃ (t₀ + δ) = ↑(δ * α) * I := by
    show fdBoundary_seg4_H H (t₀ + δ) - s = _
    rw [leftEdge_h₃_eq hs_re]
    have h_expand : (t₀ + δ - 3) * (H - Real.sqrt 3 / 2) = (t₀ - 3) * α + δ * α := by
      rw [hα_def]; ring
    have h_eq' : Real.sqrt 3 / 2 + (t₀ + δ - 3) * (H - Real.sqrt 3 / 2) - s.im = δ * α := by
      rw [h_expand]; linarith [ht₀_mul]
    rw [h_eq']
  rw [hval_minus, hval_plus]
  rw [show (↑(-(δ * α)) * I : ℂ) = -(↑(δ * α) * I) from by push_cast; ring]
  exact log_neg_rI_sub_log_rI (mul_pos hδ_pos hα_pos)

theorem gWN_fdBoundary_H_eq_neg_half_of_leftEdge (H : ℝ) (hH_sqrt : Real.sqrt 3 / 2 < H)
    (s : ℂ) (hs_re : s.re = -1/2) (hs_norm : ‖s‖ > 1)
    (hs_im_lower : Real.sqrt 3 / 2 < s.im) (hs_im : s.im < H) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []; simp only [sub_zero]
  have h_ev := leftEdge_winding_aux H hH_sqrt s hs_re hs_norm hs_im_lower hs_im
  have h_tendsto : Filter.Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖(fdBoundary_H H t - s)‖ > ε then
      (fdBoundary_H H t - s)⁻¹ * deriv (fun u => fdBoundary_H H u - s) t else 0)
    (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) :=
    tendsto_const_nhds.congr' (h_ev.mono (fun _ h => h.symm))
  rw [h_tendsto.limUnder_eq]
  field_simp [Real.pi_ne_zero, I_ne_zero]

end

/-! ## Unit Circle Arc: gWN = -1/2

For a point `s` on the unit circle arc (`‖s‖ = 1`, `|s.re| < 1/2`, `s.im > 0`):

1. **Parameterization**: Find `t₀ ∈ (1, 3)` with `fdBoundary_H H t₀ = s = exp(i·π(1+t₀)/6)`.
2. **Separation**: Non-arc segments stay bounded away from `s`.
3. **Hybrid FTC**: Use `ftc_log` (g ∈ slitPlane) before the crossing,
   `ftc_log_neg` (−g ∈ slitPlane) after the crossing.
4. **Branch correction**: The far endpoint gives `log(−g(5)) − log(g(0)) = −iπ`.
5. **Near-crossing ratio**: `g(t₀−δ)/(−g(t₀+δ)) = exp(−iπδ/6) → 1`.
6. **Limit**: Total → −iπ, hence `gWN = (2πi)⁻¹·(−iπ) = −1/2`.
-/

section UnitArc

/-! ### Arc Parameterization -/

/-- The crossing parameter `t₀ = 6·arccos(s.re)/π − 1` lies in `(1, 3)`. -/
private lemma unitArc_t₀_mem_Ioo (s : ℂ) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    6 * Real.arccos s.re / Real.pi - 1 ∈ Ioo (1 : ℝ) 3 := by
  set θ₀ := Real.arccos s.re with hθ₀_def
  have hs_re_bound : s.re ∈ Ioo (-1/2 : ℝ) (1/2) := by
    have h := abs_lt.mp hs_re; exact ⟨by linarith [h.1], h.2⟩
  -- arccos maps (-1/2, 1/2) to (π/3, 2π/3) (arccos is strictly decreasing)
  have hcos_third : Real.arccos (1/2 : ℝ) = Real.pi / 3 := by
    rw [show (1/2 : ℝ) = Real.cos (Real.pi / 3) from (Real.cos_pi_div_three).symm]
    exact Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])
  have hcos_two_third : Real.arccos (-1/2 : ℝ) = 2 * Real.pi / 3 := by
    rw [show (-1/2 : ℝ) = Real.cos (2 * Real.pi / 3) from by
      rw [show (2:ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; ring]
    exact Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])
  have hθ₀_lower : Real.pi / 3 < θ₀ := by
    rw [← hcos_third]
    -- arccos(1/2) < arccos(s.re): need -1 ≤ s.re, s.re < 1/2, 1/2 ≤ 1
    exact Real.arccos_lt_arccos (by linarith [hs_re_bound.1]) hs_re_bound.2 (by norm_num)
  have hθ₀_upper : θ₀ < 2 * Real.pi / 3 := by
    rw [← hcos_two_third]
    -- arccos(s.re) < arccos(-1/2): need -1 ≤ -1/2, -1/2 < s.re, s.re ≤ 1
    exact Real.arccos_lt_arccos (by norm_num) (by linarith [hs_re_bound.1])
        (by linarith [hs_re_bound.2])
  constructor
  · -- 6θ₀/π - 1 > 1 ↔ θ₀ > π/3
    rw [show (1:ℝ) < 6 * θ₀ / Real.pi - 1 ↔ 2 * Real.pi < 6 * θ₀ from by
      rw [lt_sub_iff_add_lt, lt_div_iff₀ Real.pi_pos]; ring_nf]
    linarith
  · -- 6θ₀/π - 1 < 3 ↔ θ₀ < 2π/3
    rw [show 6 * θ₀ / Real.pi - 1 < (3:ℝ) ↔ 6 * θ₀ < 4 * Real.pi from by
      rw [sub_lt_iff_lt_add, div_lt_iff₀ Real.pi_pos]; ring_nf]
    linarith

/-- `fdBoundary_H H` passes through `s` at the arc parameter `t₀`. -/
private lemma unitArc_fdBoundary_eq (H : ℝ) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    let t₀ := 6 * Real.arccos s.re / Real.pi - 1
    fdBoundary_H H t₀ = s := by
  intro t₀
  have ht₀_Ioo := unitArc_t₀_mem_Ioo s hs_re hs_im_pos
  rw [fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2]
  -- Goal: exp(↑(π * (1 + t₀) / 6) * I) = s
  -- We have t₀ = 6·arccos(s.re)/π - 1, so π(1+t₀)/6 = arccos(s.re)
  have h_angle : Real.pi * (1 + t₀) / 6 = Real.arccos s.re := by
    simp only [t₀]; field_simp; ring
  rw [h_angle]
  -- exp(i·arccos(s.re)) = cos(arccos(s.re)) + i·sin(arccos(s.re)) = s.re + i·s.im = s
  rw [exp_real_angle_I]
  have hs_re_range : s.re ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · have := abs_le.mp (le_of_lt hs_re |>.trans (by norm_num : (1:ℝ)/2 ≤ 1))
      linarith [(abs_le.mp (le_of_lt hs_re)).1]
    · linarith [(abs_lt.mp hs_re).2]
  rw [Real.cos_arccos hs_re_range.1 hs_re_range.2]
  -- sin(arccos(s.re)) = s.im (from ‖s‖ = 1 and s.im > 0)
  have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
    have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg s)] at h2
    simp only [Complex.normSq_apply] at h2; nlinarith
  have h_sin : Real.sin (Real.arccos s.re) = s.im := by
    rw [Real.sin_arccos]
    have h1m : 1 - s.re ^ 2 = s.im ^ 2 := by linarith
    rw [h1m, Real.sqrt_sq (le_of_lt hs_im_pos)]
  rw [h_sin]
  exact Complex.re_add_im s

/-- The arc crossing parameter `t₀` is the unique crossing on `[0, 5]`. -/
private lemma unitArc_unique_crossing (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    let t₀ := 6 * Real.arccos s.re / Real.pi - 1
    ∀ t ∈ Icc (0 : ℝ) 5, fdBoundary_H H t = s → t = t₀ := by
  intro t₀ t ht hs_eq
  have ht₀_Ioo := unitArc_t₀_mem_Ioo s hs_re hs_im_pos
  have hH_sqrt : Real.sqrt 3 / 2 < H := by
    have : Real.sqrt 3 < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]
    linarith
  -- Case analysis on which segment t is in
  by_cases h1 : t ≤ 1
  · -- Seg1: re = 1/2 but |s.re| < 1/2 so s.re ≤ 1/2. At seg1, re = 1/2, but we need re(s) = 1/2
    -- Actually seg1 has re = 1/2, and s.re could be anything in (-1/2, 1/2).
    -- But fdBoundary(t) = s implies re(fdBoundary(t)) = s.re. On seg1, re = 1/2.
    -- So s.re = 1/2, but |s.re| < 1/2 means s.re ∈ (-1/2, 1/2), contradiction unless s.re ≠ 1/2.
    simp only [fdBoundary_H, h1, ↓reduceIte] at hs_eq
    have hre := congr_arg Complex.re hs_eq
    simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im] at hre
    -- hre : 1/2 = s.re, contradicts |s.re| < 1/2 (actually (1:ℝ)/2 = s.re)
    have := (abs_lt.mp hs_re).2
    linarith
  · push_neg at h1
    by_cases h3 : t ≤ 3
    · -- Arc: t ∈ (1, 3], fdBoundary = exp(iπ(1+t)/6)
      by_cases h1' : t = 1
      · -- t = 1: boundary, but we can handle via re argument
        subst h1'
        simp only [fdBoundary_H, show (1:ℝ) ≤ 1 from le_refl _, ↓reduceIte] at hs_eq
        have hre := congr_arg Complex.re hs_eq
        simp [exp_real_angle_I, Real.cos_pi_div_three] at hre
        have := (abs_lt.mp hs_re).2
        push_cast at hre
        linarith
      · have ht1 : 1 < t := lt_of_le_of_ne (le_of_lt h1) (Ne.symm h1')
        have ht3 : t < 3 := lt_of_le_of_ne h3 (by
          intro h3_eq; subst h3_eq
          simp only [fdBoundary_H, show ¬((3:ℝ) ≤ 1) from by norm_num, ↓reduceIte,
            show ¬((3:ℝ) ≤ 2) from by norm_num, show (3:ℝ) ≤ 3 from le_refl _] at hs_eq
          have hre := congr_arg Complex.re hs_eq
          have h_angle : (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) =
              ↑(2 * Real.pi / 3) := by push_cast; ring
          rw [h_angle] at hre
          rw [exp_real_angle_I, cos_two_pi_div_three] at hre
          simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero] at hre
          have := (abs_lt.mp hs_re).1; linarith)
        rw [fdBoundary_H_eq_arc ht1 ht3] at hs_eq
        -- Now: exp(iπ(1+t)/6) = s, and we know s = exp(iπ(1+t₀)/6)
        have h_s_eq : fdBoundary_H H t₀ = s := unitArc_fdBoundary_eq H s hs_norm hs_re hs_im_pos
        rw [fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2] at h_s_eq
        rw [← h_s_eq] at hs_eq
        -- exp(iπ(1+t)/6) = exp(iπ(1+t₀)/6)
        -- Extract real parts: cos(π(1+t)/6) = cos(π(1+t₀)/6)
        have hre := congr_arg Complex.re hs_eq
        simp only [exp_real_angle_I, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
                   mul_zero, zero_mul, sub_self, add_zero] at hre
        -- cos is injective on (π/3, 2π/3) ⊂ [0, π]
        set θ := Real.pi * (1 + t) / 6
        set θ₀' := Real.pi * (1 + t₀) / 6
        have hθ_range : θ ∈ Icc (0 : ℝ) Real.pi := by
          constructor
          · positivity
          · simp only [θ]; nlinarith [Real.pi_pos, h3]
        have hθ₀_range : θ₀' ∈ Icc (0 : ℝ) Real.pi := by
          constructor
          · simp only [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.1]
          · simp only [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.2]
        -- cos is strictly anti on [0, π], so injective
        have hθ_eq : θ = θ₀' :=
          Real.strictAntiOn_cos.injOn hθ_range hθ₀_range hre
        -- θ = θ₀' → t = t₀
        simp only [θ, θ₀'] at hθ_eq
        nlinarith [Real.pi_pos]
    · push_neg at h3
      by_cases h4 : t ≤ 4
      · -- Seg4: re = -1/2, but |s.re| < 1/2 is compatible. Need im argument.
        -- Actually: ‖s‖ = 1, and seg4 goes from (ρ) up. ‖seg4(t)‖ ≥ 1 at t=3 (= ρ)
        -- and increases. But s is on the unit circle.
        -- More simply: on seg4, re = -1/2. If s.re ≠ -1/2, contradiction.
        -- If s.re = -1/2, then s = -1/2 + s.im·I with s.im = √(1 - 1/4) = √3/2.
        -- But then s = ρ which has |s.re| = 1/2, contradicting |s.re| < 1/2.
        rw [fdBoundary_H_eq_seg4_H (not_le.mpr (by linarith : 1 < t))
            (not_le.mpr (by linarith : 2 < t)) (not_le.mpr h3) h4] at hs_eq
        have hre := congr_arg Complex.re hs_eq
        simp [fdBoundary_seg4_H, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre
        -- hre : -1/2 = s.re
        have := (abs_lt.mp hs_re).1; linarith
      · -- Seg5: im = H but s.im ≤ 1 < H
        push_neg at h4
        rw [fdBoundary_H_eq_seg5_H (not_le.mpr (by linarith : 1 < t))
            (not_le.mpr (by linarith : 2 < t)) (not_le.mpr (by linarith : 3 < t))
            (not_le.mpr h4)] at hs_eq
        have him := congr_arg Complex.im hs_eq
        simp [fdBoundary_seg5_H, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im] at him
        -- him : H = s.im, but s.im ≤ 1 < H
        have hs_im_le : s.im ≤ 1 := by
          have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
            have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
            rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg s)] at h2
            simp only [Complex.normSq_apply] at h2; nlinarith
          nlinarith [sq_nonneg s.re]
        linarith

/-! ### Arc: Separation from Non-Arc Segments -/

/-- Points on seg1 (re = 1/2) are at distance ≥ 1/2 − s.re from s on the arc. -/
private lemma unitArc_dist_from_seg1 (s : ℂ) (hs_re : |s.re| < 1/2) (z : ℂ)
    (hz_re : z.re = 1/2) : 1/2 - s.re ≤ ‖z - s‖ := by
  have hd : (z - s).re = 1/2 - s.re := by simp [Complex.sub_re, hz_re]
  calc 1/2 - s.re = |(z - s).re| := by
        rw [hd, abs_of_pos (by linarith [(abs_lt.mp hs_re).2])]
    _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _

/-- Points on seg4 (re = −1/2) are at distance ≥ s.re + 1/2 from s on the arc. -/
private lemma unitArc_dist_from_seg4 (s : ℂ) (hs_re : |s.re| < 1/2) (z : ℂ)
    (hz_re : z.re = -1/2) : s.re + 1/2 ≤ ‖z - s‖ := by
  have hd : (z - s).re = -1/2 - s.re := by simp [Complex.sub_re, hz_re]
  calc s.re + 1/2 = |(-1/2 - s.re)| := by
        rw [abs_of_nonpos (by linarith [(abs_lt.mp hs_re).1])]; ring
    _ = |(z - s).re| := by rw [hd]
    _ ≤ ‖z - s‖ := Complex.abs_re_le_norm _

/-- Points on seg5 (im = H) are at distance ≥ H − 1 from s on the arc (since s.im ≤ 1). -/
private lemma unitArc_dist_from_seg5 (s : ℂ) (hs_norm : ‖s‖ = 1) (H : ℝ) (hH : 1 < H)
    (z : ℂ) (hz_im : z.im = H) : H - 1 ≤ ‖z - s‖ := by
  have hs_im_le : s.im ≤ 1 := by
    have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
      rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg s)] at h2
      simp only [Complex.normSq_apply] at h2; nlinarith
    nlinarith [sq_nonneg s.re]
  have hd : (z - s).im = H - s.im := by simp [Complex.sub_im, hz_im]
  calc H - 1 ≤ H - s.im := by linarith
    _ = |(z - s).im| := by rw [hd, abs_of_pos (by linarith)]
    _ ≤ ‖z - s‖ := Complex.abs_im_le_norm _

/-- Minimum separation distance for arc points. -/
private lemma unitArc_min_dist_pos (s : ℂ) (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2)
    (hs_im_pos : 0 < s.im) (H : ℝ) (hH : 1 < H) :
    0 < min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) := by
  simp only [lt_min_iff]
  exact ⟨⟨by linarith [(abs_lt.mp hs_re).2], by linarith [(abs_lt.mp hs_re).1]⟩,
         by linarith⟩

set_option maxHeartbeats 8000000 in
/-- Non-arc segments of fdBoundary_H stay at distance ≥ d from arc point s. -/
private lemma unitArc_min_dist_from_non_arc (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im)
    (t : ℝ) (ht_arc_right : 3 ≤ t) (ht5 : t ≤ 5) :
    min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) ≤ ‖fdBoundary_H H t - s‖ := by
  set d := min (min (1/2 - s.re) (s.re + 1/2)) (H - 1)
  rcases eq_or_lt_of_le ht_arc_right with h3_eq | h3_lt
  · -- t = 3: arc endpoint ρ = exp(i·2π/3), which has re = -1/2
    subst h3_eq
    unfold fdBoundary_H
    rw [if_neg (show ¬((3:ℝ) ≤ 1) from by norm_num),
        if_neg (show ¬((3:ℝ) ≤ 2) from by norm_num),
        if_pos (show (3:ℝ) ≤ 3 from le_refl _)]
    have hre : (exp ((↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)).re = -1/2 := by
      rw [show (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) * I =
          ↑(2 * Real.pi / 3) * I from by push_cast; ring]
      rw [exp_real_angle_I, cos_two_pi_div_three]
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero]; norm_num
    calc d ≤ s.re + 1/2 := le_trans (min_le_left _ _) (min_le_right _ _)
      _ ≤ _ := unitArc_dist_from_seg4 s hs_re _ hre
  · by_cases h4 : t ≤ 4
    · -- Seg4: re = -1/2
      have hre := re_fdBoundary_H_seg4 H t (by linarith) (by linarith) h3_lt h4
      calc d ≤ s.re + 1/2 := le_trans (min_le_left _ _) (min_le_right _ _)
        _ ≤ _ := unitArc_dist_from_seg4 s hs_re _ hre
    · -- Seg5: im = H
      push_neg at h4
      have him := im_fdBoundary_H_seg5 H t (by linarith) (by linarith) h3_lt h4
      calc d ≤ H - 1 := min_le_right _ _
        _ ≤ _ := unitArc_dist_from_seg5 s hs_norm H hH _ him

/-- Non-arc segments to the LEFT (t ≤ 1) stay at distance ≥ d from arc point s. -/
private lemma unitArc_min_dist_from_seg1 (H : ℝ) (s : ℂ)
    (hs_re : |s.re| < 1/2) (t : ℝ) (ht : t ≤ 1) :
    1/2 - s.re ≤ ‖fdBoundary_H H t - s‖ := by
  rw [fdBoundary_H_eq_seg1_H ht]
  have hre : (fdBoundary_seg1_H H t).re = 1/2 := by
    simp [fdBoundary_seg1_H, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  exact unitArc_dist_from_seg1 s hs_re _ hre

/-! ### Arc: slitPlane Conditions -/

/-- On the arc before the crossing, `g ∈ slitPlane` (since `re(g) > 0`). -/
private lemma unitArc_g_slitPlane_before (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (t : ℝ) (ht1 : 1 ≤ t) (htt₀ : t < t₀) :
    (exp (↑(Real.pi * (1 + t) / 6) * I) - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  -- g(t) = exp(iθ(t)) - exp(iθ₀) where θ(t) < θ₀
  -- re(g) = cos θ(t) - cos θ₀ > 0 since cos is decreasing and θ(t) < θ₀
  set θ := Real.pi * (1 + t) / 6 with hθ_def
  set θ₀' := Real.pi * (1 + t₀) / 6 with hθ₀_def
  rw [h_s_arc, exp_real_angle_I, exp_real_angle_I, show
    (↑(Real.cos θ) + ↑(Real.sin θ) * I) - (↑(Real.cos θ₀') + ↑(Real.sin θ₀') * I) =
    ↑(Real.cos θ - Real.cos θ₀') + ↑(Real.sin θ - Real.sin θ₀') * I from by push_cast; ring]
  -- Need: cos θ - cos θ₀' > 0, i.e., cos θ > cos θ₀'
  -- Since cos is strictly decreasing on [0, π] and θ < θ₀' with both in [π/3, 2π/3] ⊂ [0, π]
  have hθ_lt : θ < θ₀' := by simp [hθ_def, hθ₀_def]; nlinarith [Real.pi_pos]
  have hθ_range : θ ∈ Icc (0 : ℝ) Real.pi := by
    constructor <;> simp [hθ_def] <;> nlinarith [Real.pi_pos, ht₀_Ioo.2]
  have hθ₀_range : θ₀' ∈ Icc (0 : ℝ) Real.pi := by
    constructor <;> simp [hθ₀_def] <;> nlinarith [Real.pi_pos, ht₀_Ioo.2]
  -- cos_lt_cos_of_nonneg_of_le_pi: x < y ∧ 0 ≤ x ∧ y ≤ π  →  cos y < cos x
  -- We have θ < θ₀', so cos θ₀' < cos θ, i.e., cos θ > cos θ₀'
  have h_cos_lt : Real.cos θ > Real.cos θ₀' :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ_range.1 hθ₀_range.2 hθ_lt
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  nlinarith [h_cos_lt, sq_nonneg (Real.sin θ₀' - Real.sin θ)]

/-- On the arc after the crossing, `−g ∈ slitPlane` (since `re(−g) > 0`). -/
private lemma unitArc_neg_g_slitPlane_after (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3) (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (t : ℝ) (htt₀ : t₀ < t) (ht3 : t ≤ 3) :
    -(exp (↑(Real.pi * (1 + t) / 6) * I) - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  set θ := Real.pi * (1 + t) / 6 with hθ_def
  set θ₀' := Real.pi * (1 + t₀) / 6 with hθ₀_def
  rw [h_s_arc, exp_real_angle_I, exp_real_angle_I, show
    -((↑(Real.cos θ) + ↑(Real.sin θ) * I) - (↑(Real.cos θ₀') + ↑(Real.sin θ₀') * I)) =
    ↑(Real.cos θ₀' - Real.cos θ) + ↑(Real.sin θ₀' - Real.sin θ) * I from by push_cast; ring]
  -- Need: cos θ₀' - cos θ > 0, i.e., cos θ₀' > cos θ
  have hθ_gt : θ₀' < θ := by simp [hθ_def, hθ₀_def]; nlinarith [Real.pi_pos]
  have hθ_range : θ ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · simp [hθ_def]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    · simp [hθ_def]; have : 1 + t ≤ 4 := by linarith [ht3]
      nlinarith [Real.pi_pos]
  have hθ₀_range : θ₀' ∈ Icc (0 : ℝ) Real.pi := by
    constructor
    · simp [hθ₀_def]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    · simp [hθ₀_def]; nlinarith [Real.pi_pos, ht₀_Ioo.2]
  -- cos_lt_cos_of_nonneg_of_le_pi: x < y ∧ 0 ≤ x ∧ y ≤ π  →  cos y < cos x
  -- We have θ₀' < θ, so cos θ < cos θ₀', i.e., cos θ₀' > cos θ
  have h_cos_lt : Real.cos θ₀' > Real.cos θ :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_range.1 hθ_range.2 hθ_gt
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  nlinarith [h_cos_lt, sq_nonneg (Real.sin θ₀' - Real.sin θ)]

/-- On seg4, `−g ∈ slitPlane` (since `re(−g) = s.re + 1/2 > 0`). -/
private lemma unitArc_neg_g_slitPlane_seg4 (s : ℂ)
    (hs_re : |s.re| < 1/2) (H : ℝ) (t : ℝ) (_ht3 : 3 ≤ t) (_ht4 : t ≤ 4) :
    -(fdBoundary_seg4_H H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  simp only [fdBoundary_seg4_H, neg_sub]
  show 0 < (s - (-1/2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I)).re
  have h_cast : (↑(Real.sqrt 3 / 2) : ℂ) = ↑(Real.sqrt 3) / 2 := by push_cast; ring
  simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, h_cast]
  linarith [(abs_lt.mp hs_re).1]

/-- On seg5, `−g ∈ slitPlane` (since `im(−g) = s.im − H ≠ 0`). -/
private lemma unitArc_neg_g_slitPlane_seg5 (s : ℂ)
    (hs_norm : ‖s‖ = 1) (H : ℝ) (hH : 1 < H) (t : ℝ) :
    -(fdBoundary_seg5_H H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; right
  simp only [fdBoundary_seg5_H, neg_sub]
  -- Goal: (s - (↑t - 9/2 + ↑H * I)).im ≠ 0 from expanded def
  -- This simplifies to s.im - H ≠ 0
  simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  -- im = s.im - H ≠ 0 since s.im ≤ 1 < H
  intro h
  have hs_im_le : s.im ≤ 1 := by
    have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
      rw [Complex.norm_def] at h2
      have hn : 0 ≤ Complex.normSq s := Complex.normSq_nonneg s
      rw [Real.sq_sqrt hn] at h2
      simp only [Complex.normSq_apply] at h2
      convert h2 using 1
      ring
    nlinarith [sq_nonneg s.re]
  linarith

/-! ### Arc: Near-Crossing Ratio Computation -/

/-- The ratio `g(t₀-δ) / (−g(t₀+δ)) = exp(−i·πδ/6)` on the arc. -/
private lemma unitArc_ratio_eq (t₀ δ : ℝ) (hδ_pos : 0 < δ) (hδ_small : δ < 6) :
    let g_minus := exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - exp (↑(Real.pi * (1 + t₀) / 6) * I)
    let neg_g_plus := -(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - exp (↑(Real.pi * (1 + t₀) / 6) * I))
    g_minus / neg_g_plus = exp (↑(-(Real.pi * δ / 6)) * I) := by
  -- Unfold the let bindings
  dsimp only
  set θ₀ := Real.pi * (1 + t₀) / 6
  set φ := Real.pi * δ / 6 with hφ_def
  have hφ_pos : 0 < φ := by positivity
  have hφ_lt_pi : φ < Real.pi := by simp [hφ_def]; nlinarith [Real.pi_pos]
  -- Rewrite angle expressions
  rw [show Real.pi * (1 + (t₀ - δ)) / 6 = θ₀ - φ from by simp [θ₀, hφ_def]; ring,
      show Real.pi * (1 + (t₀ + δ)) / 6 = θ₀ + φ from by simp [θ₀, hφ_def]; ring]
  -- Factor out exp(iθ₀) using z and w
  rw [show (↑(θ₀ - φ) * I : ℂ) = ↑θ₀ * I - ↑φ * I from by push_cast; ring,
      show (↑(θ₀ + φ) * I : ℂ) = ↑θ₀ * I + ↑φ * I from by push_cast; ring]
  set z := exp (↑θ₀ * I)
  set w := exp (↑φ * I)
  have h_sub : exp (↑θ₀ * I - ↑φ * I) = z * w⁻¹ := by rw [Complex.exp_sub]; rfl
  have h_add : exp (↑θ₀ * I + ↑φ * I) = z * w := Complex.exp_add _ _
  rw [h_sub, h_add]
  have hz_ne : z ≠ 0 := exp_ne_zero _
  have hw_ne_one : w ≠ 1 := by
    intro h
    have him := congr_arg Complex.im h
    rw [show w = cexp (↑φ * I) from rfl, exp_ofReal_mul_I_im, one_im] at him
    linarith [Real.sin_pos_of_pos_of_lt_pi hφ_pos hφ_lt_pi]
  rw [show z * w⁻¹ - z = z * (w⁻¹ - 1) from by ring,
      show -(z * w - z) = z * (1 - w) from by ring,
      mul_div_mul_left _ _ hz_ne]
  have hw_ne : w ≠ 0 := exp_ne_zero _
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw_ne_one)
  have h_ratio : (w⁻¹ - 1) / (1 - w) = w⁻¹ := by field_simp [h1w]
  rw [h_ratio]
  simp only [w]
  rw [show (↑(-φ) * I : ℂ) = -(↑φ * I) from by push_cast; ring, Complex.exp_neg]

/-! ### Arc: Far-Endpoint Log Correction -/

/-- log(−g(0)) = log(g(0)) − iπ when g(0) has im > 0. -/
private lemma unitArc_far_endpoint_correction (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    Complex.log (-(fdBoundary_H H 0 - s)) =
    Complex.log (fdBoundary_H H 0 - s) - ↑Real.pi * I := by
  set g₀ := fdBoundary_H H 0 - s
  -- g₀ = 1/2 + HI - s. re(g₀) = 1/2 - s.re > 0, im(g₀) = H - s.im > 0
  have hg₀_re : g₀.re = 1/2 - s.re := by
    simp [g₀, fdBoundary_H, Complex.sub_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hs_im_le : s.im ≤ 1 := by
    have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
      have h2 : ‖s‖ ^ 2 = 1 := by rw [hs_norm]; norm_num
      rw [Complex.norm_def] at h2
      have hn : 0 ≤ Complex.normSq s := Complex.normSq_nonneg s
      rw [Real.sq_sqrt hn] at h2
      simp only [Complex.normSq_apply] at h2
      convert h2 using 1
      ring
    nlinarith [sq_nonneg s.re]
  have hg₀_im : g₀.im = H - s.im := by
    simp [g₀, fdBoundary_H, Complex.sub_im, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have hg₀_im_pos : 0 < g₀.im := by rw [hg₀_im]; linarith
  -- For z with im > 0: log(-z) = log(z) - iπ
  have hg₀_ne : g₀ ≠ 0 := by
    intro h; have := congr_arg Complex.im h; simp at this; linarith [hg₀_im_pos]
  simp only [Complex.log]
  rw [norm_neg, arg_neg_eq_arg_sub_pi_iff.mpr (Or.inl hg₀_im_pos)]
  push_cast; ring

/-! ### Arc: g ∈ slitPlane on seg1 (re > 0) -/

/-- On seg1, `g ∈ slitPlane` since `re(g) = 1/2 − s.re > 0`. -/
private lemma unitArc_g_slitPlane_seg1 (s : ℂ)
    (hs_re : |s.re| < 1/2) (H : ℝ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (fdBoundary_H H t - s) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  rw [fdBoundary_H_eq_seg1_H ht.2]
  simp [fdBoundary_seg1_H, Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linarith [(abs_lt.mp hs_re).2]

/-! ### Arc: Main Winding Number Computation -/

set_option maxHeartbeats 400000 in
/-- For any `δ > 0` with `t₀-δ > 1` and `t₀+δ < 3`, the δ-split integral
equals `log(g(t₀-δ)/(-g(t₀+δ))) - πI`. -/
private lemma unitArc_ftc_value (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im)
    (δ : ℝ) (hδ_pos : 0 < δ)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hδ_left : 1 < t₀ - δ) (hδ_right : t₀ + δ < 3) :
    IntervalIntegrable (fun t => deriv (fun u => fdBoundary_H H u - s) t / (fdBoundary_H H t - s)) volume 0 (t₀ - δ) ∧
    IntervalIntegrable (fun t => deriv (fun u => fdBoundary_H H u - s) t / (fdBoundary_H H t - s)) volume (t₀ + δ) 5 ∧
    ((∫ t in (0:ℝ)..(t₀ - δ), deriv (fun u => fdBoundary_H H u - s) t / (fdBoundary_H H t - s)) +
    (∫ t in (t₀ + δ)..5, deriv (fun u => fdBoundary_H H u - s) t / (fdBoundary_H H t - s)) =
    Complex.log ((fdBoundary_H H (t₀ - δ) - s) / (-(fdBoundary_H H (t₀ + δ) - s))) -
    ↑Real.pi * I) := by
  -- Notation
  set g : ℝ → ℂ := fun t => fdBoundary_H H t - s with hg_def
  -- Smooth representatives for each segment
  set h₀ : ℝ → ℂ := fun t => fdBoundary_seg1_H H t - s
  set h_arc : ℝ → ℂ := fun t => exp (↑(Real.pi * (1 + t) / 6) * I) - s
  set h₃ : ℝ → ℂ := fun t => fdBoundary_seg4_H H t - s
  set h₅ : ℝ → ℂ := fun t => fdBoundary_seg5_H H t - s
  -- HasDerivAt for each representative
  have hd₀ : ∀ t : ℝ, HasDerivAt h₀ (-(↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg1_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp)
  have hd_arc : ∀ t : ℝ, HasDerivAt h_arc
      (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + t) / 6) * I)) t :=
    hasDerivAt_arc_rep s
  have hd₃ : ∀ t : ℝ, HasDerivAt h₃ ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) t := by
    intro t; exact (hasDerivAt_fdBoundary_seg4_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp)
  have hd₅ : ∀ t : ℝ, HasDerivAt h₅ 1 t := by
    intro t; exact (hasDerivAt_fdBoundary_seg5_H H t).sub (hasDerivAt_const t s)
      |>.congr_deriv (by simp)
  -- Value agreement: g = hₖ on each segment
  have hg_h₀ : ∀ t, t ≤ 1 → g t = h₀ t := by
    intro t ht; simp only [hg_def, h₀]; rw [fdBoundary_H_eq_seg1_H ht]
  have hg_arc : ∀ t, 1 < t → t < 3 → g t = h_arc t := by
    intro t ht1 ht3; simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc ht1 ht3]
  have hg_h₃ : ∀ t, 3 < t → t ≤ 4 → g t = h₃ t := by
    intro t ht3 ht4; simp only [hg_def, h₃]
    rw [fdBoundary_H_eq_seg4_H (not_le.mpr (by linarith : 1 < t))
        (not_le.mpr (by linarith : 2 < t)) (not_le.mpr ht3) ht4]
  have hg_h₅ : ∀ t, 4 < t → g t = h₅ t := by
    intro t ht4; simp only [hg_def, h₅]
    rw [fdBoundary_H_eq_seg5_H (not_le.mpr (by linarith : 1 < t))
        (not_le.mpr (by linarith : 2 < t)) (not_le.mpr (by linarith : 3 < t))
        (not_le.mpr ht4)]
  -- Endpoint value agreement
  have hep_01 : h₅ 5 = h₀ 0 := by
    simp only [h₀, h₅, fdBoundary_seg1_H, fdBoundary_seg5_H]; push_cast; ring
  have hep_1 : h₀ 1 = h_arc 1 := by
    simp only [h₀, h_arc, fdBoundary_seg1_H]
    rw [show Real.pi * (1 + 1) / 6 = Real.pi / 3 from by ring,
        exp_real_angle_I, Real.cos_pi_div_three, Real.sin_pi_div_three]
    push_cast; ring
  have hep_3 : h_arc 3 = h₃ 3 := by
    simp only [h_arc, h₃, fdBoundary_seg4_H]
    rw [show Real.pi * (1 + 3) / 6 = 2 * Real.pi / 3 from by ring,
        exp_real_angle_I, cos_two_pi_div_three, sin_two_pi_div_three]
    push_cast; ring
  have hep_4 : h₃ 4 = h₅ 4 := by
    simp only [h₃, h₅, fdBoundary_seg4_H, fdBoundary_seg5_H]; push_cast; ring
  -- Derivative agreement (EventuallyEq) on open subintervals
  have hderiv_01 : ∀ t ∈ Ioo (0:ℝ) 1, deriv g t = deriv h₀ t := by
    intro t ⟨_, ht1⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Iio_mem_nhds ht1) (fun s hs => hg_h₀ s (le_of_lt hs)))
  have hderiv_arc : ∀ t ∈ Ioo (1:ℝ) 3, deriv g t = deriv h_arc t := by
    intro t ⟨ht1, ht3⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht1 ht3) (fun s hs => hg_arc s hs.1 hs.2))
  have hderiv_3 : ∀ t ∈ Ioo (3:ℝ) 4, deriv g t = deriv h₃ t := by
    intro t ⟨ht3, ht4⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioo_mem_nhds ht3 ht4)
        (fun s hs => hg_h₃ s hs.1 (le_of_lt hs.2)))
  have hderiv_5 : ∀ t ∈ Ioo (4:ℝ) 5, deriv g t = deriv h₅ t := by
    intro t ⟨ht4, _⟩
    exact Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht4) (fun s hs => hg_h₅ s hs))
  -- slitPlane conditions (positive sense and negative sense)
  -- Seg1 [0, 1]: g ∈ slitPlane (re > 0)
  have hslit_seg1 : ∀ t ∈ Icc (0:ℝ) 1, h₀ t ∈ Complex.slitPlane := by
    intro t ht
    have : (fdBoundary_H H t - s) ∈ Complex.slitPlane :=
      unitArc_g_slitPlane_seg1 s hs_re H t ht
    rwa [← hg_h₀ t ht.2]
  -- Arc [1, t₀-δ]: g ∈ slitPlane (re > 0)
  have hslit_arc_before : ∀ t ∈ Icc (1:ℝ) (t₀ - δ), h_arc t ∈ Complex.slitPlane := by
    intro t ⟨ht1, ht_td⟩
    have htt₀ : t < t₀ := by linarith
    rcases eq_or_lt_of_le ht1 with h_eq | h_lt
    · -- t = 1
      rw [← h_eq]; rw [← hep_1]; exact hslit_seg1 1 ⟨by norm_num, le_refl _⟩
    · exact unitArc_g_slitPlane_before s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc t
        (le_of_lt h_lt) htt₀
  -- Arc [t₀+δ, 3]: -g ∈ slitPlane (re > 0)
  have hslit_arc_after : ∀ t ∈ Icc (t₀ + δ) (3:ℝ), -(h_arc t) ∈ Complex.slitPlane := by
    intro t ⟨ht_td, ht3⟩
    have htt₀ : t₀ < t := by linarith
    rcases eq_or_lt_of_le ht3 with h_eq | h_lt
    · -- t = 3
      rw [h_eq, hep_3]
      exact unitArc_neg_g_slitPlane_seg4 s hs_re H 3 le_rfl (by norm_num)
    · exact unitArc_neg_g_slitPlane_after s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc t
        htt₀ (le_of_lt h_lt)
  -- Seg4 [3, 4]: -g ∈ slitPlane
  have hslit_seg4 : ∀ t ∈ Icc (3:ℝ) 4, -(h₃ t) ∈ Complex.slitPlane := by
    intro t ht; exact unitArc_neg_g_slitPlane_seg4 s hs_re H t ht.1 ht.2
  -- Seg5 [4, 5]: -g ∈ slitPlane
  have hslit_seg5 : ∀ t ∈ Icc (4:ℝ) 5, -(h₅ t) ∈ Complex.slitPlane := by
    intro t ⟨ht4, ht5⟩
    have : -(fdBoundary_seg5_H H t - s) ∈ Complex.slitPlane :=
      unitArc_neg_g_slitPlane_seg5 s hs_norm H hH t
    simpa [h₅]
  -- Apply FTC on each sub-interval
  -- Piece 0: [0, 1] via ftc_log (g ∈ slitPlane)
  have piece₀ := ftc_log (by norm_num : (0:ℝ) ≤ 1)
    ((continuous_fdBoundary_seg1_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₀ t).differentiableAt)
    (by rw [show deriv h₀ = fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I from
          funext fun t => (hd₀ t).deriv]
        exact continuousOn_const)
    hslit_seg1
  -- Piece 1: [1, t₀-δ] via ftc_log (g ∈ slitPlane on arc)
  have h_arc_cont : Continuous h_arc := by
    simp only [h_arc]; exact (Continuous.cexp (by fun_prop)).sub continuous_const
  have piece₁ := ftc_log (by linarith : (1:ℝ) ≤ t₀ - δ)
    h_arc_cont.continuousOn
    (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc_before
  -- Piece 2: [t₀+δ, 3] via ftc_log_neg (-g ∈ slitPlane on arc)
  have piece₂ := ftc_log_neg (by linarith : t₀ + δ ≤ 3)
    h_arc_cont.continuousOn
    (fun t _ => (hd_arc t).differentiableAt)
    (by rw [show deriv h_arc = fun t => ↑(Real.pi / 6) * I *
          exp (↑(Real.pi * (1 + t) / 6) * I) from funext fun t => (hd_arc t).deriv]
        exact (Continuous.mul continuous_const (Continuous.cexp (by fun_prop))).continuousOn)
    hslit_arc_after
  -- Piece 3: [3, 4] via ftc_log_neg
  have piece₃ := ftc_log_neg (by norm_num : (3:ℝ) ≤ 4)
    ((continuous_fdBoundary_seg4_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₃ t).differentiableAt)
    (by rw [show deriv h₃ = fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I from
          funext fun t => (hd₃ t).deriv]
        exact continuousOn_const)
    hslit_seg4
  -- Piece 4: [4, 5] via ftc_log_neg
  have piece₄ := ftc_log_neg (by norm_num : (4:ℝ) ≤ 5)
    ((continuous_fdBoundary_seg5_H H).sub continuous_const).continuousOn
    (fun t _ => (hd₅ t).differentiableAt)
    (by rw [show deriv h₅ = fun _ => (1 : ℂ) from funext fun t => (hd₅ t).deriv]
        exact continuousOn_const)
    hslit_seg5
  -- A.e. equality: deriv hₖ / hₖ = deriv g / g on each interval
  have h_ae_01 : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 1 → deriv h₀ t / h₀ t = deriv g t / g t := by
    have h_excl : ({1} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({1} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    have ht_lt1 : t < 1 := lt_of_le_of_ne ht.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
    rw [hg_h₀ t (le_of_lt ht_lt1), hderiv_01 t ⟨by linarith [ht.1], ht_lt1⟩]
  have h_ae_1_td : ∀ᵐ t ∂volume, t ∈ Set.uIoc 1 (t₀ - δ) →
      deriv h_arc t / h_arc t = deriv g t / g t := by
    have h_excl : ({1, t₀ - δ} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({1, t₀ - δ} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : (1:ℝ) ≤ t₀ - δ)] at ht_mem
    have ht1 : 1 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht3 : t < 3 := by linarith [ht_mem.2]
    rw [hg_arc t ht1 ht3, hderiv_arc t ⟨ht1, ht3⟩]
  have h_ae_arc_after : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ + δ) 3 →
      deriv h_arc t / h_arc t = deriv g t / g t := by
    have h_excl : ({t₀ + δ, 3} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({t₀ + δ, 3} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ + δ ≤ 3)] at ht_mem
    have ht1 : 1 < t := by linarith [ht_mem.1]
    have ht3 : t < 3 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_arc t ht1 ht3, hderiv_arc t ⟨ht1, ht3⟩]
  have h_ae_34 : ∀ᵐ t ∂volume, t ∈ Set.uIoc 3 4 → deriv h₃ t / h₃ t = deriv g t / g t := by
    have h_excl : ({3, 4} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({3, 4} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at ht_mem
    have ht3 : 3 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht4 : t < 4 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₃ t ht3 (le_of_lt ht4), hderiv_3 t ⟨ht3, ht4⟩]
  have h_ae_45 : ∀ᵐ t ∂volume, t ∈ Set.uIoc 4 5 → deriv h₅ t / h₅ t = deriv g t / g t := by
    have h_excl : ({4, 5} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite ({4, 5} : Set ℝ)).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at ht_mem
    have ht4 : 4 < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; left; linarith)
      · exact h
    have ht5 : t < 5 := by
      rcases eq_or_lt_of_le ht_mem.2 with h | h
      · exfalso; exact ht_ne (by simp [Set.mem_insert_iff, Set.mem_singleton_iff]; right; linarith)
      · exact h
    rw [hg_h₅ t ht4, hderiv_5 t ⟨ht4, ht5⟩]
  -- Transfer integrability from hₖ to g
  have hint_01 : IntervalIntegrable (fun t => deriv g t / g t) volume 0 1 :=
    piece₀.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_01.mono (fun t ht hm => ht hm)))
  have hint_1_td : IntervalIntegrable (fun t => deriv g t / g t) volume 1 (t₀ - δ) :=
    piece₁.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_1_td.mono (fun t ht hm => ht hm)))
  have hint_td_3 : IntervalIntegrable (fun t => deriv g t / g t) volume (t₀ + δ) 3 :=
    piece₂.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_arc_after.mono (fun t ht hm => ht hm)))
  have hint_34 : IntervalIntegrable (fun t => deriv g t / g t) volume 3 4 :=
    piece₃.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_34.mono (fun t ht hm => ht hm)))
  have hint_45 : IntervalIntegrable (fun t => deriv g t / g t) volume 4 5 :=
    piece₄.1.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (h_ae_45.mono (fun t ht hm => ht hm)))
  -- Return integrability and equation as a triple
  refine ⟨hint_01.trans hint_1_td, (hint_td_3.trans hint_34).trans hint_45, ?_⟩
  -- deriv (fdBoundary_H H · - s) = deriv g
  have hderiv_eq : (fun u => fdBoundary_H H u - s) = g := rfl
  -- FTC values via smooth representatives
  have h_ftc_01 : ∫ t in (0:ℝ)..1, deriv g t / g t =
      Complex.log (h₀ 1) - Complex.log (h₀ 0) := by
    rw [← piece₀.2, intervalIntegral.integral_congr_ae
      (h_ae_01.mono (fun t ht hm => ht hm))]
  have h_ftc_1_td : ∫ t in (1:ℝ)..(t₀ - δ), deriv g t / g t =
      Complex.log (h_arc (t₀ - δ)) - Complex.log (h_arc 1) := by
    rw [← piece₁.2, intervalIntegral.integral_congr_ae
      (h_ae_1_td.mono (fun t ht hm => ht hm))]
  have h_ftc_td_3 : ∫ t in (t₀ + δ)..(3:ℝ), deriv g t / g t =
      Complex.log (-(h_arc 3)) - Complex.log (-(h_arc (t₀ + δ))) := by
    rw [← piece₂.2, intervalIntegral.integral_congr_ae
      (h_ae_arc_after.mono (fun t ht hm => ht hm))]
  have h_ftc_34 : ∫ t in (3:ℝ)..(4:ℝ), deriv g t / g t =
      Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3)) := by
    rw [← piece₃.2, intervalIntegral.integral_congr_ae
      (h_ae_34.mono (fun t ht hm => ht hm))]
  have h_ftc_45 : ∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t =
      Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)) := by
    rw [← piece₄.2, intervalIntegral.integral_congr_ae
      (h_ae_45.mono (fun t ht hm => ht hm))]
  -- Split the left integral [0, t₀-δ] = [0, 1] + [1, t₀-δ]
  have h_split_left : ∫ t in (0:ℝ)..(t₀ - δ), deriv g t / g t =
      (∫ t in (0:ℝ)..1, deriv g t / g t) + (∫ t in (1:ℝ)..(t₀ - δ), deriv g t / g t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint_01 hint_1_td]
  -- Split the right integral [t₀+δ, 5] = [t₀+δ, 3] + [3, 4] + [4, 5]
  have h_split_right : ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t =
      (∫ t in (t₀ + δ)..(3:ℝ), deriv g t / g t) +
      (∫ t in (3:ℝ)..(4:ℝ), deriv g t / g t) +
      (∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t) := by
    have h1 : (∫ t in (t₀ + δ)..(3:ℝ), deriv g t / g t) +
        (∫ t in (3:ℝ)..(4:ℝ), deriv g t / g t) =
        ∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hint_td_3 hint_34]
    have h2 : (∫ t in (t₀ + δ)..(4:ℝ), deriv g t / g t) +
        (∫ t in (4:ℝ)..(5:ℝ), deriv g t / g t) =
        ∫ t in (t₀ + δ)..(5:ℝ), deriv g t / g t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint_td_3.trans hint_34) hint_45]
    rw [← h2, ← h1]
  -- Convert integrand to g-form under binders, then split and apply FTC
  simp_rw [show ∀ t, fdBoundary_H H t - s = g t from fun _ => rfl]
  rw [h_split_left, h_ftc_01, h_ftc_1_td,
      h_split_right, h_ftc_td_3, h_ftc_34, h_ftc_45]
  -- Telescope: intermediate terms cancel via endpoint agreements
  -- LHS = (log(h₀ 1) - log(h₀ 0)) + (log(h_arc(t₀-δ)) - log(h_arc 1))
  --      + (log(-h_arc 3) - log(-h_arc(t₀+δ))) + (log(-h₃ 4) - log(-h₃ 3))
  --      + (log(-h₅ 5) - log(-h₅ 4))
  -- = log(h_arc(t₀-δ)) - log(h₀ 0) + log(-h₅ 5) - log(-h_arc(t₀+δ))
  --   [using hep_1: h₀ 1 = h_arc 1; hep_3: h_arc 3 = h₃ 3; hep_4: h₃ 4 = h₅ 4]
  -- = log(h_arc(t₀-δ)) - log(h₀ 0) + log(-h₀ 0) - log(-h_arc(t₀+δ))
  --   [using hep_01: h₅ 5 = h₀ 0]
  have h_telescope :
    Complex.log (h₀ 1) - Complex.log (h₀ 0) +
    (Complex.log (h_arc (t₀ - δ)) - Complex.log (h_arc 1)) +
    ((Complex.log (-(h_arc 3)) - Complex.log (-(h_arc (t₀ + δ)))) +
     (Complex.log (-(h₃ 4)) - Complex.log (-(h₃ 3))) +
     (Complex.log (-(h₅ 5)) - Complex.log (-(h₅ 4)))) =
    Complex.log (h_arc (t₀ - δ)) - Complex.log (h₀ 0) +
    (Complex.log (-(h₀ 0)) - Complex.log (-(h_arc (t₀ + δ)))) := by
    rw [hep_1, hep_3, hep_4, hep_01]; ring
  rw [h_telescope]
  -- Now use far endpoint correction: log(-h₀ 0) = log(h₀ 0) - πI
  -- h₀ 0 = fdBoundary_seg1_H H 0 - s = fdBoundary_H H 0 - s = g 0
  have h_h₀_is_g₀ : h₀ 0 = fdBoundary_H H 0 - s := by
    simp [h₀]; rw [← fdBoundary_H_eq_seg1_H (by norm_num : (0:ℝ) ≤ 1)]
  have h_far_corr : Complex.log (-(h₀ 0)) = Complex.log (h₀ 0) - ↑Real.pi * I := by
    rw [h_h₀_is_g₀]
    exact unitArc_far_endpoint_correction H hH s hs_norm hs_re hs_im_pos
  rw [h_far_corr]
  -- Now LHS = log(h_arc(t₀-δ)) - log(h₀ 0) + (log(h₀ 0) - πI - log(-h_arc(t₀+δ)))
  -- = log(h_arc(t₀-δ)) - log(-h_arc(t₀+δ)) - πI
  -- We need to show this equals log(g(t₀-δ)/(-g(t₀+δ))) - πI
  -- Since t₀-δ and t₀+δ are on the arc:
  --   g(t₀-δ) = h_arc(t₀-δ) and g(t₀+δ) = h_arc(t₀+δ)
  -- So fdBoundary_H H (t₀-δ) - s = h_arc(t₀-δ) and fdBoundary_H H (t₀+δ) - s = h_arc(t₀+δ)
  have h_td_arc : g (t₀ - δ) = h_arc (t₀ - δ) := by
    simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc (by linarith) (by linarith)]
  have h_pd_arc : g (t₀ + δ) = h_arc (t₀ + δ) := by
    simp only [hg_def, h_arc]; rw [fdBoundary_H_eq_arc (by linarith) (by linarith)]
  rw [h_td_arc, h_pd_arc]
  -- Now need: log(h_arc(t₀-δ)) - log(h₀ 0) + (log(h₀ 0) - πI - log(-h_arc(t₀+δ)))
  --         = log(h_arc(t₀-δ) / (-h_arc(t₀+δ))) - πI
  -- The log(h₀ 0) terms cancel, leaving
  --   log(h_arc(t₀-δ)) - log(-h_arc(t₀+δ)) - πI
  -- We need log_div_of_re_pos to convert the difference to a quotient.
  -- re(h_arc(t₀-δ)) > 0 from slitPlane before crossing
  -- re(-h_arc(t₀+δ)) > 0 from slitPlane after crossing
  -- re(h_arc(t₀-δ)) > 0: directly from unitArc_g_slitPlane_before
  -- h_arc(t₀-δ) = exp(iθ_minus) - s, and the slitPlane proof uses `left` (re > 0)
  have h_re_before : 0 < (h_arc (t₀ - δ)).re := by
    -- h_arc(t₀-δ) ∈ slitPlane, and for t < t₀ on the arc, the proof goes through left (re > 0)
    -- We can extract this: cos(θ_minus) > cos(θ₀) since θ_minus < θ₀
    show 0 < (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s).re
    set θ_m := Real.pi * (1 + (t₀ - δ)) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.sub_re]
    show 0 < Real.cos θ_m - Real.cos θ₀'
    have hθ_lt : θ_m < θ₀' := by simp [θ_m, θ₀']; nlinarith [Real.pi_pos]
    have hθ_m_nn : 0 ≤ θ_m := by simp [θ_m]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ₀_le_pi : θ₀' ≤ Real.pi := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ_m_nn hθ₀_le_pi hθ_lt]
  -- re(-h_arc(t₀+δ)) > 0: directly from unitArc_neg_g_slitPlane_after
  have h_re_after : 0 < (-(h_arc (t₀ + δ))).re := by
    show 0 < (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)).re
    set θ_p := Real.pi * (1 + (t₀ + δ)) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero, neg_sub]
    show 0 < Real.cos θ₀' - Real.cos θ_p
    have hθ_gt : θ₀' < θ_p := by simp [θ₀', θ_p]; nlinarith [Real.pi_pos]
    have hθ₀_nn : 0 ≤ θ₀' := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ_p_le_pi : θ_p ≤ Real.pi := by simp [θ_p]; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_nn hθ_p_le_pi hθ_gt]
  -- Use log_div_of_re_pos: log(a/b) = log(a) - log(b) for re(a), re(b) > 0
  rw [log_div_of_re_pos h_re_before h_re_after]; ring

/-- The log ratio `log(g(t₀-δ)/(-g(t₀+δ))) → 0` as `δ → 0`. -/
private lemma unitArc_log_ratio_tendsto (s : ℂ)
    (_hs_norm : ‖s‖ = 1) (_hs_re : |s.re| < 1/2) (_hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (_ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3)
    (_h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I)) :
    Tendsto (fun δ => Complex.log (
      (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
      (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))))
    (𝓝[>] 0) (𝓝 0) := by
  have h_ev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0), 0 < δ ∧ δ < 6 := by
    apply inter_mem self_mem_nhdsWithin
    exact nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 6))
  have h_log_exp : Tendsto (fun δ : ℝ => Complex.log (cexp (↑(-(Real.pi * δ / 6)) * I)))
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    rw [show (0 : ℂ) = Complex.log 1 from by simp]
    apply (continuousAt_clog (by simp [slitPlane])).tendsto.comp
    rw [show (1 : ℂ) = cexp (↑(-(Real.pi * 0 / 6)) * I) from by simp]
    exact Tendsto.mono_left (by fun_prop : Continuous _).continuousAt.tendsto nhdsWithin_le_nhds
  have h_agree : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0),
      Complex.log (cexp (↑(-(Real.pi * δ / 6)) * I)) =
      Complex.log (
        (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
        (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))) := by
    apply h_ev.mono
    intro δ ⟨hδ_pos, hδ_small⟩
    rw [_h_s_arc]
    congr 1
    exact (unitArc_ratio_eq t₀ δ hδ_pos hδ_small).symm
  exact h_log_exp.congr' h_agree

/-- `log(g(t₀−δ)) − log(−g(t₀+δ)) → 0` as `δ → 0⁺`. This bridges the log-difference
form (from FTC telescope) to the log-ratio form (from `unitArc_log_ratio_tendsto`). -/
private lemma unitArc_log_diff_tendsto (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im)
    (t₀ : ℝ) (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I)) :
    Tendsto (fun δ =>
      Complex.log (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) -
      Complex.log (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)))
    (𝓝[>] 0) (𝓝 0) := by
  have h_ratio := unitArc_log_ratio_tendsto s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc
  -- For small δ, both g(t₀-δ) and -g(t₀+δ) have re > 0, so log_div_of_re_pos applies
  -- Extract re > 0 from the slitPlane proofs (which use the `left` case)
  -- For g(t₀-δ): re > 0 is cos(θ) - cos(θ₀) > 0 (θ < θ₀ and cos decreasing)
  -- For -g(t₀+δ): re > 0 is cos(θ₀) - cos(θ) > 0 (θ₀ < θ and cos decreasing)
  have h_ev_agree : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0),
      Complex.log (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) -
      Complex.log (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)) =
      Complex.log ((exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s) /
        (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s))) := by
    have h_ev : ∀ᶠ δ in nhdsWithin (0:ℝ) (Ioi 0), 0 < δ ∧ δ < min (t₀ - 1) (3 - t₀) := by
      apply inter_mem self_mem_nhdsWithin
      exact nhdsWithin_le_nhds (Iio_mem_nhds (lt_min (by linarith [ht₀_Ioo.1]) (by linarith [ht₀_Ioo.2])))
    apply h_ev.mono; intro δ ⟨hδ_pos, hδ_small⟩
    have hδ_lt1 : δ < t₀ - 1 := lt_of_lt_of_le hδ_small (min_le_left _ _)
    have hδ_lt2 : δ < 3 - t₀ := lt_of_lt_of_le hδ_small (min_le_right _ _)
    -- re(g(t₀-δ)) > 0: cos(θ_minus) > cos(θ₀) since θ_minus < θ₀
    set θ_m := Real.pi * (1 + (t₀ - δ)) / 6
    set θ₀' := Real.pi * (1 + t₀) / 6
    have hθ_lt : θ_m < θ₀' := by simp [θ_m, θ₀']; nlinarith [Real.pi_pos]
    have hθ_m_nn : 0 ≤ θ_m := by simp [θ_m]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ₀_le_pi : θ₀' ≤ Real.pi := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    have hcos_m : Real.cos θ₀' < Real.cos θ_m :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hθ_m_nn hθ₀_le_pi hθ_lt
    have h_re_a : 0 < (exp (↑(Real.pi * (1 + (t₀ - δ)) / 6) * I) - s).re := by
      rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero, Complex.sub_re]
      show 0 < Real.cos θ_m - Real.cos θ₀'; linarith
    -- re(-g(t₀+δ)) > 0: cos(θ₀) > cos(θ_plus) since θ₀ < θ_plus
    set θ_p := Real.pi * (1 + (t₀ + δ)) / 6
    have hθ_gt : θ₀' < θ_p := by simp [θ₀', θ_p]; nlinarith [Real.pi_pos]
    have hθ₀_nn : 0 ≤ θ₀' := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ_p_le_pi : θ_p ≤ Real.pi := by simp [θ_p]; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    have hcos_p : Real.cos θ_p < Real.cos θ₀' :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_nn hθ_p_le_pi hθ_gt
    have h_re_b : 0 < (-(exp (↑(Real.pi * (1 + (t₀ + δ)) / 6) * I) - s)).re := by
      rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
      simp only [Complex.neg_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, zero_mul, sub_self, add_zero, neg_sub]
      show 0 < Real.cos θ₀' - Real.cos θ_p; linarith
    exact (log_div_of_re_pos h_re_a h_re_b).symm
  exact h_ratio.congr' (h_ev_agree.mono fun _ h => h.symm)

/-- normSq of the difference of two unit-circle points:
  `‖exp(iα) − exp(iβ)‖² = 2 − 2·cos(α − β)`. -/
private lemma normSq_exp_sub (α β : ℝ) :
    Complex.normSq (exp (↑α * I) - exp (↑β * I)) = 2 - 2 * Real.cos (α - β) := by
  rw [Complex.normSq_apply]
  -- re and im of exp(iα) - exp(iβ) = (cos α - cos β) + (sin α - sin β)*I
  rw [exp_real_angle_I, exp_real_angle_I]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_self, add_zero,
    Complex.sub_re, Complex.add_im, Complex.mul_im, mul_one, add_zero, Complex.sub_im]
  -- Goal: (cos α - cos β) * (cos α - cos β) + (sin α - sin β) * (sin α - sin β)
  --      = 2 - 2 * cos(α - β)
  rw [Real.cos_sub]
  nlinarith [Real.sin_sq_add_cos_sq α, Real.sin_sq_add_cos_sq β,
    sq_nonneg (Real.sin α - Real.sin β), sq_nonneg (Real.cos α - Real.cos β)]

/-- On the arc, `‖g(t₀+δ)‖² = 2 − 2·cos(πδ/6)` (depends only on |δ|). -/
private lemma unitArc_normSq_at_offset (s : ℂ) (H : ℝ) (t₀ δ : ℝ)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (h_in_arc : 1 < t₀ + δ) (h_in_arc' : t₀ + δ < 3) :
    Complex.normSq (fdBoundary_H H (t₀ + δ) - s) = 2 - 2 * Real.cos (Real.pi * δ / 6) := by
  rw [fdBoundary_H_eq_arc h_in_arc h_in_arc', h_s_arc]
  rw [normSq_exp_sub]
  congr 1; congr 1; congr 1; ring

/-- Norm symmetry: `‖g(t₀+δ)‖ = ‖g(t₀−δ)‖` on the arc. -/
private lemma unitArc_norm_offset_symm (s : ℂ) (H : ℝ) (t₀ δ : ℝ)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (h_left_arc : 1 < t₀ - δ) (h_left_arc' : t₀ - δ < 3)
    (h_right_arc : 1 < t₀ + δ) (h_right_arc' : t₀ + δ < 3) :
    ‖fdBoundary_H H (t₀ - δ) - s‖ = ‖fdBoundary_H H (t₀ + δ) - s‖ := by
  rw [Complex.norm_def, Complex.norm_def]
  congr 1
  rw [show t₀ - δ = t₀ + (-δ) from sub_eq_add_neg t₀ δ]
  rw [unitArc_normSq_at_offset s H t₀ (-δ) h_s_arc (by linarith) (by linarith)]
  rw [unitArc_normSq_at_offset s H t₀ δ h_s_arc h_right_arc h_right_arc']
  congr 1; congr 1; rw [show Real.pi * (-δ) / 6 = -(Real.pi * δ / 6) from by ring, Real.cos_neg]

/-- Strict norm monotonicity on the arc: if `0 ≤ δ₁ < δ₂` with both offsets
on the arc, then `‖g(t₀+δ₁)‖ < ‖g(t₀+δ₂)‖`. -/
private lemma unitArc_norm_strict_mono (s : ℂ) (H : ℝ) (t₀ : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (δ₁ δ₂ : ℝ) (hδ₁_nn : 0 ≤ δ₁) (hδ₁₂ : δ₁ < δ₂)
    (hδ₂ : δ₂ < min (t₀ - 1) (3 - t₀)) :
    ‖fdBoundary_H H (t₀ + δ₁) - s‖ < ‖fdBoundary_H H (t₀ + δ₂) - s‖ := by
  -- Both t₀+δᵢ are on the arc
  have hδ₂_left : δ₂ < t₀ - 1 := lt_of_lt_of_le hδ₂ (min_le_left _ _)
  have hδ₂_right : δ₂ < 3 - t₀ := lt_of_lt_of_le hδ₂ (min_le_right _ _)
  have h1a : 1 < t₀ + δ₁ := by linarith [ht₀_Ioo.1]
  have h3a : t₀ + δ₁ < 3 := by linarith
  have h1b : 1 < t₀ + δ₂ := by linarith [ht₀_Ioo.1]
  have h3b : t₀ + δ₂ < 3 := by linarith
  -- normSq values
  have hns₁ := unitArc_normSq_at_offset s H t₀ δ₁ h_s_arc h1a h3a
  have hns₂ := unitArc_normSq_at_offset s H t₀ δ₂ h_s_arc h1b h3b
  -- cos(πδ₂/6) < cos(πδ₁/6) by strict monotonicity of cos on [0,π]
  have hφ₁_nn : 0 ≤ Real.pi * δ₁ / 6 := by positivity
  have hφ₂_le_pi : Real.pi * δ₂ / 6 ≤ Real.pi := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 6)]
    nlinarith [Real.pi_pos, ht₀_Ioo.2]
  have hφ_lt : Real.pi * δ₁ / 6 < Real.pi * δ₂ / 6 := by nlinarith [Real.pi_pos]
  have hcos_lt : Real.cos (Real.pi * δ₂ / 6) < Real.cos (Real.pi * δ₁ / 6) :=
    Real.cos_lt_cos_of_nonneg_of_le_pi hφ₁_nn hφ₂_le_pi hφ_lt
  -- normSq₁ < normSq₂
  have hns_lt : Complex.normSq (fdBoundary_H H (t₀ + δ₁) - s) <
      Complex.normSq (fdBoundary_H H (t₀ + δ₂) - s) := by rw [hns₁, hns₂]; linarith
  -- Convert normSq ordering to norm ordering
  rw [Complex.norm_def, Complex.norm_def]
  exact Real.sqrt_lt_sqrt (Complex.normSq_nonneg _) hns_lt

/-- On the unit arc, ‖g‖ is strictly increasing in |offset| from t₀.
    Unlike `unitArc_norm_strict_mono`, this works for ANY two points on the arc. -/
private lemma unitArc_norm_lt_of_abs_lt (s : ℂ) (H : ℝ) (t₀ : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (t₁ t₂ : ℝ) (ht₁_arc : 1 < t₁) (ht₁_arc' : t₁ < 3)
    (ht₂_arc : 1 < t₂) (ht₂_arc' : t₂ < 3)
    (habs : |t₁ - t₀| < |t₂ - t₀|) :
    ‖fdBoundary_H H t₁ - s‖ < ‖fdBoundary_H H t₂ - s‖ := by
  rw [show t₁ = t₀ + (t₁ - t₀) from by ring, show t₂ = t₀ + (t₂ - t₀) from by ring]
  have hns₁ := unitArc_normSq_at_offset s H t₀ (t₁ - t₀) h_s_arc (by linarith) (by linarith)
  have hns₂ := unitArc_normSq_at_offset s H t₀ (t₂ - t₀) h_s_arc (by linarith) (by linarith)
  have hcos₁ : Real.cos (Real.pi * (t₁ - t₀) / 6) = Real.cos (Real.pi * |t₁ - t₀| / 6) := by
    rcases le_or_gt (t₁ - t₀) 0 with h | h
    · rw [abs_of_nonpos h,
        show Real.pi * (t₁ - t₀) / 6 = -(Real.pi * (-(t₁ - t₀)) / 6) from by ring,
        Real.cos_neg]
    · rw [abs_of_pos h]
  have hcos₂ : Real.cos (Real.pi * (t₂ - t₀) / 6) = Real.cos (Real.pi * |t₂ - t₀| / 6) := by
    rcases le_or_gt (t₂ - t₀) 0 with h | h
    · rw [abs_of_nonpos h,
        show Real.pi * (t₂ - t₀) / 6 = -(Real.pi * (-(t₂ - t₀)) / 6) from by ring,
        Real.cos_neg]
    · rw [abs_of_pos h]
  have h_abs_bound : |t₂ - t₀| < 2 := by
    rw [abs_lt]; constructor <;> linarith [ht₀_Ioo.1, ht₀_Ioo.2]
  have hφ₁_nn : 0 ≤ Real.pi * |t₁ - t₀| / 6 := by positivity
  have hφ₂_le_pi : Real.pi * |t₂ - t₀| / 6 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hφ_lt : Real.pi * |t₁ - t₀| / 6 < Real.pi * |t₂ - t₀| / 6 := by
    nlinarith [Real.pi_pos]
  have hcos_lt := Real.cos_lt_cos_of_nonneg_of_le_pi hφ₁_nn hφ₂_le_pi hφ_lt
  rw [Complex.norm_def, Complex.norm_def]
  apply Real.sqrt_lt_sqrt (Complex.normSq_nonneg _)
  rw [hns₁, hns₂, hcos₁, hcos₂]; linarith

/-- For `δ > 0` on the arc, `‖g(t₀+δ)‖ > 0`. -/
private lemma unitArc_norm_pos_at_offset (s : ℂ) (H : ℝ) (t₀ δ : ℝ)
    (ht₀_Ioo : t₀ ∈ Ioo (1:ℝ) 3)
    (h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I))
    (hδ_pos : 0 < δ) (hδ_small : δ < min (t₀ - 1) (3 - t₀)) :
    0 < ‖fdBoundary_H H (t₀ + δ) - s‖ := by
  have h0 : ‖fdBoundary_H H (t₀ + 0) - s‖ = 0 := by
    simp only [add_zero]
    rw [fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2, h_s_arc, sub_self, norm_zero]
  calc 0 = ‖fdBoundary_H H (t₀ + 0) - s‖ := h0.symm
    _ < ‖fdBoundary_H H (t₀ + δ) - s‖ :=
        unitArc_norm_strict_mono s H t₀ ht₀_Ioo h_s_arc 0 δ le_rfl hδ_pos hδ_small

/-- Continuity of δ ↦ ‖g(t₀+δ)‖ for IVT applications. -/
private lemma unitArc_norm_continuous (s : ℂ) (H : ℝ) (t₀ : ℝ) :
    Continuous (fun δ : ℝ => ‖fdBoundary_H H (t₀ + δ) - s‖) :=
  continuous_norm.comp (((fdBoundary_H_continuous H).comp (continuous_const.add continuous_id')).sub
    continuous_const)

set_option maxHeartbeats 8000000 in
/-- The PV integral → −πI as ε → 0 for the arc case. -/
private lemma unitArc_winding_tendsto (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    Tendsto (fun ε => ∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - s‖ > ε then
      (fdBoundary_H H t - s)⁻¹ * deriv (fun u => fdBoundary_H H u - s) t else 0)
    (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := by
  -- Setup: crossing parameter and arc representation
  set t₀ := 6 * Real.arccos s.re / Real.pi - 1 with ht₀_def
  have ht₀_Ioo := unitArc_t₀_mem_Ioo s hs_re hs_im_pos
  have ht₀_gt1 : 1 < t₀ := ht₀_Ioo.1
  have ht₀_lt3 : t₀ < 3 := ht₀_Ioo.2
  have hg_at_t₀ := unitArc_fdBoundary_eq H s hs_norm hs_re hs_im_pos
  have h_s_arc : s = exp (↑(Real.pi * (1 + t₀) / 6) * I) := by
    rw [← fdBoundary_H_eq_arc ht₀_Ioo.1 ht₀_Ioo.2]; exact hg_at_t₀.symm
  -- Notation
  set g : ℝ → ℂ := fun t => fdBoundary_H H t - s with hg_def
  -- Minimum distance from s to non-arc segments
  set d_min := min (min (1/2 - s.re) (s.re + 1/2)) (H - 1) with hd_min_def
  have hd_min_pos : 0 < d_min := unitArc_min_dist_pos s hs_norm hs_re hs_im_pos H hH
  -- Half-width for the arc
  set hw := min (t₀ - 1) (3 - t₀) with hhw_def
  have hhw_pos : 0 < hw := lt_min (by linarith [ht₀_Ioo.1]) (by linarith [ht₀_Ioo.2])
  -- The FTC-based integral as a function of δ
  -- For small δ: integral on [0, t₀-δ] ∪ [t₀+δ, 5] of g'/g
  --   = log_diff(δ) - πI where log_diff → 0
  -- The ε-cutoff integral I(ε) agrees with the δ-split integral when ε = ‖g(t₀+δ)‖
  -- Use Metric.tendsto_nhdsWithin_nhds: show ∀ r > 0, ∃ ε₀ > 0, ...
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro r hr
  -- Step 1: From unitArc_log_diff_tendsto, get δ₀ > 0 with |log_diff(δ)| < r for δ ∈ (0, δ₀)
  have h_log_tends := unitArc_log_diff_tendsto s hs_norm hs_re hs_im_pos t₀ ht₀_Ioo h_s_arc
  rw [Metric.tendsto_nhdsWithin_nhds] at h_log_tends
  obtain ⟨δ₀, hδ₀_pos, hδ₀_spec⟩ := h_log_tends r hr
  -- Step 2: Choose δ₁ ∈ (0, min(δ₀, hw) / 2) — small enough for FTC and log_diff bound
  set δ₁ := min δ₀ hw / 2 with hδ₁_def
  have hδ₁_pos : 0 < δ₁ := by positivity
  have hδ₁_lt_δ₀ : δ₁ < δ₀ := by
    simp only [hδ₁_def]; linarith [min_le_left δ₀ hw]
  have hδ₁_lt_hw : δ₁ < hw := by
    simp only [hδ₁_def]; linarith [min_le_right δ₀ hw]
  -- δ₁ satisfies the FTC hypotheses
  have hδ₁_left : 1 < t₀ - δ₁ := by linarith [lt_of_lt_of_le hδ₁_lt_hw (min_le_left _ _)]
  have hδ₁_right : t₀ + δ₁ < 3 := by linarith [lt_of_lt_of_le hδ₁_lt_hw (min_le_right _ _)]
  -- Step 3: Set ε₀ = ‖g(t₀+δ₁)‖ > 0
  set ε₀ := ‖g (t₀ + δ₁)‖ with hε₀_def
  have hε₀_pos : 0 < ε₀ := by
    simp only [hε₀_def, hg_def]
    exact unitArc_norm_pos_at_offset s H t₀ δ₁ ht₀_Ioo h_s_arc hδ₁_pos hδ₁_lt_hw
  -- Ensure ε₀ ≤ d_min (so for ε < ε₀, off-arc segments don't get cut)
  set ε₁ := min ε₀ d_min with hε₁_def
  have hε₁_pos : 0 < ε₁ := lt_min hε₀_pos hd_min_pos
  refine ⟨ε₁, hε₁_pos, fun {ε} hε_mem hε_dist => ?_⟩
  -- We have ε > 0, ε ∈ Ioi 0, and dist ε 0 < ε₁, i.e., ε < ε₁
  have hε_pos : 0 < ε := hε_mem
  have hε_lt : ε < ε₁ := by rwa [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_dist
  have hε_lt_ε₀ : ε < ε₀ := lt_of_lt_of_le hε_lt (min_le_left _ _)
  have hε_lt_d : ε < d_min := lt_of_lt_of_le hε_lt (min_le_right _ _)
  -- Step 4: By IVT, find δ' ∈ (0, δ₁) with ‖g(t₀+δ')‖ = ε
  -- The function φ(δ) = ‖g(t₀+δ)‖ is continuous, φ(0) = 0, φ(δ₁) = ε₀ > ε
  have hφ_zero : ‖g (t₀ + 0)‖ = 0 := by
    simp only [add_zero, hg_def]; rw [hg_at_t₀]; simp
  have hφ_cont : Continuous (fun δ : ℝ => ‖g (t₀ + δ)‖) := by
    simp only [hg_def]; exact unitArc_norm_continuous s H t₀
  have h_ivt : ε ∈ (fun δ : ℝ => ‖g (t₀ + δ)‖) '' Icc 0 δ₁ := by
    apply intermediate_value_Icc (le_of_lt hδ₁_pos) hφ_cont.continuousOn
    constructor
    · rw [hφ_zero]; exact le_of_lt hε_pos
    · exact le_of_lt hε_lt_ε₀
  obtain ⟨δ', ⟨hδ'_nn, hδ'_le⟩, hδ'_eq⟩ := h_ivt
  -- δ' > 0 (since ‖g(t₀+0)‖ = 0 < ε = ‖g(t₀+δ')‖)
  have hδ'_pos : 0 < δ' := by
    rcases eq_or_lt_of_le hδ'_nn with h0 | h0
    · exfalso; rw [← h0] at hδ'_eq; dsimp only at hδ'_eq; rw [hφ_zero] at hδ'_eq; linarith
    · exact h0
  have hδ'_lt_hw : δ' < hw := lt_of_le_of_lt hδ'_le hδ₁_lt_hw
  have hδ'_lt_δ₀ : δ' < δ₀ := lt_of_le_of_lt hδ'_le hδ₁_lt_δ₀
  -- Symmetry: ‖g(t₀-δ')‖ = ‖g(t₀+δ')‖ = ε
  have h_sym : ‖g (t₀ - δ')‖ = ε := by
    rw [hg_def] at hδ'_eq ⊢
    rw [unitArc_norm_offset_symm s H t₀ δ' h_s_arc
      (by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_left _ _)])
      (by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_right _ _)])
      (by linarith [ht₀_Ioo.1])
      (by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_right _ _)])]
    exact hδ'_eq
  -- FTC hypotheses for δ'
  have hδ'_left : 1 < t₀ - δ' := by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_left _ _)]
  have hδ'_right : t₀ + δ' < 3 := by linarith [lt_of_lt_of_le hδ'_lt_hw (min_le_right _ _)]
  -- Step 5: Show I(ε) = delta-split integral at δ'
  -- First, show the ε-cutoff integral is the same as the δ'-split integral
  -- Key: on [0, t₀-δ') and (t₀+δ', 5], ‖g(t)‖ > ε
  --       on (t₀-δ', t₀+δ'), ‖g(t)‖ ≤ ε (with equality at endpoints)
  -- The cutoff integrand agrees a.e. with the non-cutoff integrand on [0,t₀-δ') ∪ (t₀+δ', 5]
  -- and is 0 on (t₀-δ', t₀+δ')
  -- So I(ε) = ∫_{[0,t₀-δ']} g'/g + ∫_{[t₀+δ',5]} g'/g = FTC(δ')
  -- For the off-arc segments: ‖g(t)‖ ≥ d_min > ε
  -- For the arc before crossing: ‖g(t)‖ > ‖g(t₀+δ')‖ = ε when t < t₀-δ' or t > t₀+δ'
  -- For the arc near crossing: ‖g(t)‖ ≤ ε when t₀-δ' ≤ t ≤ t₀+δ'
  -- Convert integrand: (fdBoundary_H H t - s)⁻¹ * deriv g t → deriv g t / g t
  have h_integrand_eq : (∫ t in (0:ℝ)..5, if ‖fdBoundary_H H t - s‖ > ε then
      (fdBoundary_H H t - s)⁻¹ * deriv g t else 0) =
    ∫ t in (0:ℝ)..5, if ‖g t‖ > ε then
      deriv g t / g t else 0 := by
    congr 1; ext t
    show (if ‖g t‖ > ε then (g t)⁻¹ * deriv g t else 0) =
      if ‖g t‖ > ε then deriv g t / g t else 0
    split_ifs with h
    · rw [mul_comm, div_eq_mul_inv]
    · rfl
  rw [h_integrand_eq]
  -- Now show the integral at ε equals the FTC value at δ'
  -- We need to split [0,5] into three parts and show a.e. agreement
  -- Key a.e. claim: for a.e. t ∈ [0,5],
  --   (if ‖g t‖ > ε then g'(t)/g(t) else 0) =
  --   (if t < t₀ - δ' ∨ t > t₀ + δ' then g'(t)/g(t) else 0)
  -- This means I(ε) = ∫_{0}^{t₀-δ'} g'/g + ∫_{t₀+δ'}^{5} g'/g
  -- Apply FTC: equals log_diff(δ') - πI
  -- Then dist(I(ε), -πI) = ‖log_diff(δ')‖ < r since δ' < δ₀
  -- Step 5a: Show ‖g(t)‖ > ε for t on the arc with |t-t₀| > δ' (strictly)
  have h_arc_outside : ∀ t, 1 < t → t < 3 → δ' < |t - t₀| → ‖g t‖ > ε := by
    intro t ht1 ht3 habs
    show ε < ‖g t‖
    have hε_eq : ε = ‖g (t₀ + δ')‖ := by
      change _ = ‖g (t₀ + δ')‖; exact hδ'_eq.symm
    rw [hε_eq]; simp only [hg_def]
    exact unitArc_norm_lt_of_abs_lt s H t₀ ht₀_Ioo h_s_arc (t₀ + δ') t
      (by linarith) hδ'_right ht1 ht3
      (by rw [show t₀ + δ' - t₀ = δ' from by ring, abs_of_pos hδ'_pos]; exact habs)
  -- Step 5b: Show ‖g(t)‖ ≤ ε for t on the arc with |t-t₀| ≤ δ'
  have h_arc_inside : ∀ t, 1 < t → t < 3 → |t - t₀| ≤ δ' → ‖g t‖ ≤ ε := by
    intro t ht1 ht3 habs
    rcases eq_or_lt_of_le habs with heq | hlt
    · -- |t - t₀| = δ': normSq equality gives ‖g t‖ = ε
      have hε_eq : ε = ‖g (t₀ + δ')‖ := by
        change _ = ‖g (t₀ + δ')‖; exact hδ'_eq.symm
      rw [hε_eq]; simp only [hg_def]
      rw [show t = t₀ + (t - t₀) from by ring, Complex.norm_def, Complex.norm_def]
      apply le_of_eq; congr 1
      rw [unitArc_normSq_at_offset s H t₀ (t - t₀) h_s_arc (by linarith) (by linarith),
          unitArc_normSq_at_offset s H t₀ δ' h_s_arc (by linarith) hδ'_right]
      congr 1; congr 1
      -- cos(π(t-t₀)/6) = cos(πδ'/6) from |t-t₀| = δ'
      rcases le_or_gt (t - t₀) 0 with h | h
      · have h_neg : t - t₀ = -δ' := by rw [abs_of_nonpos h] at heq; linarith
        rw [h_neg, show Real.pi * (-δ') / 6 = -(Real.pi * δ' / 6) from by ring, Real.cos_neg]
      · rw [abs_of_pos h] at heq; rw [heq]
    · -- |t - t₀| < δ': strict monotonicity gives ‖g t‖ < ε
      have hε_eq : ε = ‖g (t₀ + δ')‖ := by
        change _ = ‖g (t₀ + δ')‖; exact hδ'_eq.symm
      rw [hε_eq]; simp only [hg_def]
      exact le_of_lt (unitArc_norm_lt_of_abs_lt s H t₀ ht₀_Ioo h_s_arc t (t₀ + δ')
        ht1 ht3 (by linarith) hδ'_right
        (by rw [show t₀ + δ' - t₀ = δ' from by ring, abs_of_pos hδ'_pos]; exact hlt))
  -- Step 5c: Off-arc segments have ‖g‖ ≥ d_min > ε
  have h_off_arc_seg1 : ∀ t, t ≤ 1 → ‖g t‖ ≥ d_min := by
    intro t ht; simp only [hg_def, hd_min_def, ge_iff_le]
    calc min (min (1/2 - s.re) (s.re + 1/2)) (H - 1)
        ≤ 1/2 - s.re := le_trans (min_le_left _ _) (min_le_left _ _)
      _ ≤ ‖fdBoundary_H H t - s‖ := unitArc_min_dist_from_seg1 H s hs_re t ht
  have h_off_arc_right : ∀ t, 3 ≤ t → t ≤ 5 → ‖g t‖ ≥ d_min := by
    intro t ht3 ht5; simp only [hg_def, hd_min_def, ge_iff_le]
    exact unitArc_min_dist_from_non_arc H hH s hs_norm hs_re hs_im_pos t ht3 ht5
  -- Step 5d: The integrand with ε-cutoff agrees a.e. with the δ'-split integrand
  -- I.e., ∫_0^5 [‖g‖>ε]·g'/g = ∫_0^{t₀-δ'} g'/g + ∫_{t₀+δ'}^5 g'/g
  -- which equals the FTC value.
  -- To show this, we prove:
  --   ∫_0^5 [‖g‖>ε]·g'/g = ∫_0^{t₀-δ'} [‖g‖>ε]·g'/g + ∫_{t₀-δ'}^{t₀+δ'} [‖g‖>ε]·g'/g
  --                         + ∫_{t₀+δ'}^5 [‖g‖>ε]·g'/g
  -- Middle integral = 0 (since ‖g‖ ≤ ε on (t₀-δ', t₀+δ'))
  -- Left and right integrals: [‖g‖>ε] = 1 a.e.
  -- Then left + right = ∫_0^{t₀-δ'} g'/g + ∫_{t₀+δ'}^5 g'/g = FTC(δ')
  -- Apply unitArc_ftc_value to get the value
  have h_ftc := unitArc_ftc_value H hH s hs_norm hs_re hs_im_pos δ' hδ'_pos t₀ ht₀_Ioo
    h_s_arc hδ'_left hδ'_right
  -- The FTC gives us the value in terms of deriv(fdBoundary_H H · - s) / (fdBoundary_H H t - s)
  -- which is the same as deriv g / g (since g = fdBoundary_H H · - s)
  -- Step 6: Show the ε-cutoff integral equals the FTC value
  -- Use the approach: split [0,5] at t₀-δ' and t₀+δ', show cutoff is constant on outer parts
  -- and 0 on inner part
  -- We need integrability of the cutoff function on [0,5]
  -- The cutoff function is bounded and measurable on [0,5] (it's piecewise continuous)
  -- Let's use a different approach: show the integral equals the non-cutoff integral
  -- on [0, t₀-δ'] ∪ [t₀+δ', 5] directly via a.e. equality
  -- Actually, the cleanest approach: show the ε-cutoff integral on [0,5] equals
  -- the δ'-split integral (∫_0^{t₀-δ'} + ∫_{t₀+δ'}^5) by a.e. equality arguments.
  -- We know the δ'-split integral = FTC value = log_diff(δ') - πI.
  -- Then dist to -πI = ‖log_diff(δ')‖ < r since δ' < δ₀.
  -- For the a.e. equality argument:
  -- 1. Split ∫_0^5 = ∫_0^{t₀-δ'} + ∫_{t₀-δ'}^{t₀+δ'} + ∫_{t₀+δ'}^5
  -- 2. On [t₀-δ', t₀+δ']: cutoff is 0 a.e. (since ‖g‖ ≤ ε on the arc, and for
  --    non-arc points in this interval, we're still on the arc since t₀-δ' > 1 and t₀+δ' < 3)
  -- 3. On [0, t₀-δ'] and [t₀+δ', 5]: cutoff = g'/g a.e.
  -- First, we need interval integrability of the cutoff function.
  -- For now, let's use a slightly different approach: show that the ε-cutoff integral
  -- equals the δ-split integral by splitting the interval of integration and arguing
  -- about each piece.
  -- Instead of the complex a.e. approach, let me use the following observation:
  -- Since t₀-δ' > 1 and t₀+δ' < 3, the interval (t₀-δ', t₀+δ') is entirely on the arc.
  -- On this interval, ‖g(t)‖ ≤ ε (from h_arc_inside), so the cutoff integrand is 0 a.e.
  -- On [0, t₀-δ']:
  --   For t ≤ 1: ‖g(t)‖ ≥ d_min > ε, so cutoff is on (g'/g)
  --   For 1 < t < t₀-δ': on arc, |t-t₀| > δ', so ‖g(t)‖ > ε
  --   At t = t₀-δ': ‖g(t₀-δ')‖ = ε, not > ε, but this is a single point (measure zero)
  -- On [t₀+δ', 5]:
  --   For t₀+δ' < t < 3: on arc, |t-t₀| > δ', so ‖g(t)‖ > ε
  --   At t = t₀+δ': ‖g‖ = ε (measure zero)
  --   For 3 ≤ t ≤ 5: ‖g(t)‖ ≥ d_min > ε
  -- So a.e. on [0, t₀-δ']: cutoff function = g'/g
  -- And a.e. on [t₀+δ', 5]: cutoff function = g'/g
  -- Therefore:
  --   ∫_0^5 [cutoff] = ∫_0^{t₀-δ'} g'/g + 0 + ∫_{t₀+δ'}^5 g'/g = FTC(δ')
  -- First establish the interval integrability needed for splitting
  -- The cutoff integrand is measurable and bounded on [0,5] (away from t₀)
  -- Actually, let me use intervalIntegral.integral_add_adjacent_intervals to split
  -- First need: the cutoff function is intervalIntegrable on [0, t₀-δ'], [t₀-δ', t₀+δ'], [t₀+δ', 5]
  -- On [t₀-δ', t₀+δ']: integrand is a.e. 0, so trivially integrable
  -- On [0, t₀-δ'] and [t₀+δ', 5]: integrand a.e. equals g'/g which is integrable (from FTC)
  -- Let's just claim the a.e. equalities and use integral_congr_ae
  set F := fun t => if ‖g t‖ > ε then deriv g t / g t else (0 : ℂ) with hF_def
  -- a.e. equality on [0, t₀-δ']: F = g'/g
  have hF_left : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (t₀ - δ') → F t = deriv g t / g t := by
    have h_excl : ({t₀ - δ'} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite _).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : (0:ℝ) ≤ t₀ - δ')] at ht_mem
    have ht_lt : t < t₀ - δ' := lt_of_le_of_ne ht_mem.2
      (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
    simp only [hF_def]
    have hgt : ‖g t‖ > ε := by
      by_cases h1 : t ≤ 1
      · calc ε < d_min := hε_lt_d
          _ ≤ ‖g t‖ := h_off_arc_seg1 t h1
      · push_neg at h1
        exact h_arc_outside t h1 (by linarith) (by rw [abs_of_nonpos (by linarith)]; linarith)
    simp only [if_pos hgt]
  -- a.e. equality on [t₀+δ', 5]: F = g'/g
  have hF_right : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ + δ') 5 → F t = deriv g t / g t := by
    have h_excl : ({t₀ + δ'} : Set ℝ)ᶜ ∈ ae volume :=
      mem_ae_iff.mpr (by rw [compl_compl]; exact (Set.toFinite _).measure_zero volume)
    filter_upwards [h_excl] with t ht_ne ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ + δ' ≤ 5)] at ht_mem
    have ht_gt : t₀ + δ' < t := by
      rcases eq_or_lt_of_le (le_of_lt ht_mem.1) with h | h
      · exfalso; exact ht_ne (Set.mem_singleton_iff.mpr (by linarith))
      · exact h
    simp only [hF_def]
    have hgt : ‖g t‖ > ε := by
      by_cases h3 : t < 3
      · exact h_arc_outside t (by linarith) h3
          (by rw [abs_of_pos (by linarith)]; linarith)
      · push_neg at h3
        calc ε < d_min := hε_lt_d
          _ ≤ ‖g t‖ := h_off_arc_right t h3 ht_mem.2
    simp only [if_pos hgt]
  -- a.e. equality on [t₀-δ', t₀+δ']: F = 0
  have hF_mid_ae : ∀ᵐ t ∂volume, t ∈ Set.uIoc (t₀ - δ') (t₀ + δ') → F t = 0 := by
    apply Filter.Eventually.of_forall; intro t ht_mem
    rw [Set.uIoc_of_le (by linarith : t₀ - δ' ≤ t₀ + δ')] at ht_mem
    simp only [hF_def]
    rw [if_neg]; push_neg
    -- t₀-δ' < t ≤ t₀+δ', and t₀-δ' > 1, t₀+δ' < 3, so t is on the arc
    exact h_arc_inside t (by linarith [ht_mem.1]) (by linarith [ht_mem.2])
      (by rw [abs_le]; constructor <;> linarith [ht_mem.1, ht_mem.2])
  -- Extract integrability from the modified unitArc_ftc_value
  obtain ⟨hint_left, hint_right, h_ftc_eq⟩ := h_ftc
  -- Integrability of F on each sub-interval (from a.e. equality with g'/g resp. 0)
  have hF_int_left : IntervalIntegrable F volume 0 (t₀ - δ') :=
    hint_left.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_left.mono (fun t ht hm => (ht hm).symm)))
  have hF_int_mid : IntervalIntegrable F volume (t₀ - δ') (t₀ + δ') := by
    have hF_mid : ∀ t ∈ Set.uIoc (t₀ - δ') (t₀ + δ'), F t = 0 := by
      intro t ht_mem
      rw [Set.uIoc_of_le (by linarith : t₀ - δ' ≤ t₀ + δ')] at ht_mem
      simp only [hF_def]
      rw [if_neg]; push_neg
      exact h_arc_inside t (by linarith [ht_mem.1]) (by linarith [ht_mem.2])
        (by rw [abs_le]; constructor <;> linarith [ht_mem.1, ht_mem.2])
    exact (IntervalIntegrable.zero (μ := volume) (a := t₀ - δ') (b := t₀ + δ')).congr
      (fun t ht => (hF_mid t ht).symm)
  have hF_int_right : IntervalIntegrable F volume (t₀ + δ') 5 :=
    hint_right.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
      (hF_right.mono (fun t ht hm => (ht hm).symm)))
  -- Split the integral into three pieces
  have h_split : ∫ t in (0:ℝ)..5, F t =
      (∫ t in (0:ℝ)..(t₀ - δ'), F t) + (∫ t in (t₀ - δ')..(t₀ + δ'), F t) +
      (∫ t in (t₀ + δ')..(5:ℝ), F t) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
          (hF_int_left.trans hF_int_mid) hF_int_right,
        ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
  -- Middle integral is 0
  have h_mid_zero : ∫ t in (t₀ - δ')..(t₀ + δ'), F t = 0 := by
    rw [intervalIntegral.integral_congr_ae hF_mid_ae]
    simp [intervalIntegral.integral_zero]
  -- Outer integrals equal g'/g integrals
  have h_eq_left : ∫ t in (0:ℝ)..(t₀ - δ'), F t =
      ∫ t in (0:ℝ)..(t₀ - δ'), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_left
  have h_eq_right : ∫ t in (t₀ + δ')..(5:ℝ), F t =
      ∫ t in (t₀ + δ')..(5:ℝ), deriv g t / g t :=
    intervalIntegral.integral_congr_ae hF_right
  -- The full integral equals the FTC value
  have h_integral_eq : ∫ t in (0:ℝ)..5, F t =
      Complex.log ((fdBoundary_H H (t₀ - δ') - s) / (-(fdBoundary_H H (t₀ + δ') - s))) -
      ↑Real.pi * I := by
    rw [h_split, h_mid_zero, add_zero, h_eq_left, h_eq_right]
    exact h_ftc_eq
  -- Now show dist(integral, -piI) < r
  show dist (∫ t in (0:ℝ)..5, F t) (-(↑Real.pi * I)) < r
  rw [h_integral_eq, dist_comm, dist_eq_norm]
  rw [show -(↑Real.pi * I) -
    (Complex.log ((fdBoundary_H H (t₀ - δ') - s) / (-(fdBoundary_H H (t₀ + δ') - s))) -
    ↑Real.pi * I) =
    -Complex.log ((fdBoundary_H H (t₀ - δ') - s) / (-(fdBoundary_H H (t₀ + δ') - s)))
    from by ring, norm_neg]
  -- Convert fdBoundary_H values to arc exponential form
  rw [fdBoundary_H_eq_arc hδ'_left (by linarith : t₀ - δ' < 3),
      fdBoundary_H_eq_arc (by linarith : 1 < t₀ + δ') hδ'_right]
  -- Use log_div = log - log (both factors have re > 0) to match unitArc_log_diff_tendsto
  set θ_m := Real.pi * (1 + (t₀ - δ')) / 6
  set θ₀' := Real.pi * (1 + t₀) / 6
  set θ_p := Real.pi * (1 + (t₀ + δ')) / 6
  have h_re_before : 0 < (exp (↑θ_m * I) - s).re := by
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero]
    show 0 < Real.cos θ_m - Real.cos θ₀'
    have hθ_m_lt : θ_m < θ₀' := by simp [θ_m, θ₀']; nlinarith [Real.pi_pos]
    have hθ_m_nn : 0 ≤ θ_m := by simp [θ_m]; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ₀_le_pi : θ₀' ≤ Real.pi := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ_m_nn hθ₀_le_pi hθ_m_lt]
  have h_re_after : 0 < (-(exp (↑θ_p * I) - s)).re := by
    rw [h_s_arc, exp_real_angle_I, exp_real_angle_I]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_self, add_zero, neg_sub]
    show 0 < Real.cos θ₀' - Real.cos θ_p
    have hθ_gt : θ₀' < θ_p := by simp [θ₀', θ_p]; nlinarith [Real.pi_pos]
    have hθ₀_nn : 0 ≤ θ₀' := by simp [θ₀']; nlinarith [Real.pi_pos, ht₀_Ioo.1]
    have hθ_p_le_pi : θ_p ≤ Real.pi := by simp [θ_p]; nlinarith [Real.pi_pos, ht₀_Ioo.2]
    linarith [Real.cos_lt_cos_of_nonneg_of_le_pi hθ₀_nn hθ_p_le_pi hθ_gt]
  rw [log_div_of_re_pos h_re_before h_re_after]
  -- Now the goal is ‖log(a) - log(b)‖ < r which matches hδ₀_spec
  have hδ'_in_Ioi : δ' ∈ Ioi (0:ℝ) := hδ'_pos
  have hδ'_dist : dist δ' 0 < δ₀ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hδ'_pos]; exact hδ'_lt_δ₀
  have h_log_small := hδ₀_spec hδ'_in_Ioi hδ'_dist
  rw [dist_zero_right] at h_log_small
  convert h_log_small using 2

/-- **Main theorem**: gWN = −1/2 at smooth arc points. -/
theorem gWN_fdBoundary_H_eq_neg_half_of_unitArc (H : ℝ) (hH : 1 < H) (s : ℂ)
    (hs_norm : ‖s‖ = 1) (hs_re : |s.re| < 1/2) (hs_im_pos : 0 < s.im) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2 := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []; simp only [sub_zero]
  have h_tendsto := unitArc_winding_tendsto H hH s hs_norm hs_re hs_im_pos
  rw [h_tendsto.limUnder_eq]
  field_simp [Real.pi_ne_zero, I_ne_zero]

end UnitArc
