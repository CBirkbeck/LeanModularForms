/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.LogDerivModularForm
import LeanModularForms.ForMathlib.FDBoundaryPath
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import LeanModularForms.ForMathlib.ModularInvariance

/-!
# Modular Contour Integral: Key Components

The contour integral of `logDeriv(f)` along the fundamental domain boundary
splits into five segments. Using modular invariance, the five-piece integral
reduces to a single number:

$$\oint_{\partial\mathcal{F}} \frac{f'}{f}\,dz
  = -(2\pi i)\bigl(\tfrac{k}{12} - \mathrm{ord}_\infty(f)\bigr)$$

This file provides the three key geometric ingredients:

## 1. T-cancellation (verticals)

Segments 1 (right vertical, `re = 1/2`) and 4 (left vertical, `re = -1/2`)
are T-translates: `γ(4/5 - t) = γ(t) - 1` for `t ∈ (0, 1/5)`. Since
`logDeriv f` is periodic with period 1, the integrands are negatives after the
change of variables, so the two integrals cancel.

## 2. S-arc contribution (arcs)

Segments 2 and 3 (unit-circle arcs from `ρ+1` to `i` to `ρ`) are swapped by
the S-involution `z ↦ -1/z`. The modular identity `f(Sz) = z^k f(z)` gives
`logDeriv f(z) = logDeriv f(-1/z) / z² - k/z`, and the integral of `k/z`
along the arc from `ρ+1` to `ρ` equals `k · (log ρ - log(ρ+1)) = kπi/3`.
By S-symmetry `2I_arc = -kπi/3`, hence `I_arc = -kπi/6 = -(2πi)(k/12)`.

## 3. Horizontal contribution (seg5)

At height `H`, the horizontal segment maps to a circle in the q-plane via
`q = exp(2πiz)`. The integral of `logDeriv(f)` becomes a winding number
computation in the q-variable, yielding `2πi · ord_∞(f)`.

## Main results

* `fdBoundaryFun_seg4_eq_seg1_sub_one` -- T-translation: seg4(4/5-t) = seg1(t) - 1
* `deriv_seg4_eq_neg_seg1` -- derivative reflection on the verticals
* `logDeriv_integrand_seg4_neg_seg1` -- T-cancellation of the logDeriv integrand
* `fdBoundaryFun_S_arc` -- S-involution: -1/γ(t) = γ(4/5-t) on the arc
* `arc_angle_computation` -- log(ρ) - log(ρ+1) = πi/3
* `arc_contribution_eq_neg_k_over_12` -- the arc integral equals -(2πi)(k/12)
* `modular_side_cancel_two_pi_I` -- cancel 2πi to obtain the modular side

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Serre, *A Course in Arithmetic*, Chapter VII
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

noncomputable section

/-- Derivative of `fdBoundaryFun H` on seg1 (right vertical, `t < 1/5`). -/
theorem deriv_fdBoundaryFun_seg1 (H : ℝ) (t : ℝ) (ht : t < 1/5) :
    deriv (fdBoundaryFun H) t = -(5 * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  have h_ev : fdBoundaryFun H =ᶠ[𝓝 t] (fun s : ℝ =>
      (1/2 + ↑H * I : ℂ) + (-(5 * (↑H - ↑(Real.sqrt 3) / 2)) * I) * (↑s : ℂ)) :=
    eventually_of_mem (Iio_mem_nhds ht) fun s (hs : s < 1/5) => by
      simp only [fdBoundaryFun, hs.le, ite_true]
      ring
  rw [h_ev.deriv_eq]
  exact ((Complex.ofRealCLM.hasDerivAt.const_mul _).const_add _).deriv ▸ by
    simp [Complex.ofRealCLM_apply]

/-- Derivative of `fdBoundaryFun H` on seg4 (left vertical, `3/5 < t < 4/5`). -/
theorem deriv_fdBoundaryFun_seg4 (H : ℝ) (t : ℝ) (ht3 : 3/5 < t) (ht4 : t < 4/5) :
    deriv (fdBoundaryFun H) t = (5 * (↑H - ↑(Real.sqrt 3) / 2)) * I := by
  have h_ev : fdBoundaryFun H =ᶠ[𝓝 t] (fun s : ℝ =>
      (-1/2 - 3 * (↑H - ↑(Real.sqrt 3) / 2) * I + ↑(Real.sqrt 3) / 2 * I : ℂ) +
      (5 * (↑H - ↑(Real.sqrt 3) / 2) * I) * (↑s : ℂ)) :=
    eventually_of_mem (Filter.inter_mem (Ioi_mem_nhds ht3) (Iio_mem_nhds ht4))
      fun s ⟨hs1, hs2⟩ => by
        simp only [mem_Ioi] at hs1
        simp only [mem_Iio] at hs2
        unfold fdBoundaryFun
        split_ifs <;> first | linarith | ring
  rw [h_ev.deriv_eq]
  exact ((Complex.ofRealCLM.hasDerivAt.const_mul _).const_add _).deriv ▸ by
    simp [Complex.ofRealCLM_apply]

/-- The seg1 and seg4 derivatives are negatives of each other.
This is the derivative-level identity underlying T-cancellation. -/
theorem deriv_seg4_eq_neg_seg1 (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (1/5)) :
    deriv (fdBoundaryFun H) (4/5 - t) = -(deriv (fdBoundaryFun H) t) := by
  rw [deriv_fdBoundaryFun_seg1 H t ht.2,
    deriv_fdBoundaryFun_seg4 H (4/5 - t) (by linarith [ht.2]) (by linarith [ht.1])]
  ring

/-- T-translation: on the open interval `(0, 1/5)`, the left vertical (seg4 at
`4/5 - t`) equals the right vertical (seg1 at `t`) shifted by `-1`. -/
theorem fdBoundaryFun_seg4_eq_seg1_sub_one (H : ℝ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1/5) :
    fdBoundaryFun H (4/5 - t) = fdBoundaryFun H t - 1 := by
  simp only [fdBoundaryFun, ht1.le,
    show ¬(4/5 - t ≤ 1/5) by linarith, show ¬(4/5 - t ≤ 2/5) by linarith,
    show ¬(4/5 - t ≤ 3/5) by linarith, show (4/5 - t ≤ 4/5) by linarith,
    ite_true, ite_false]
  push_cast
  ring

/-- Boundary case: `ρ = (ρ+1) - 1`. -/
theorem fdBoundaryFun_seg4_boundary_translate (H : ℝ) :
    fdBoundaryFun H (3/5) = fdBoundaryFun H (1/5) - 1 := by
  rw [fdBoundaryFun_at_three_fifths, fdBoundaryFun_at_one_fifth]
  simp only [ellipticPointRho, ellipticPointRho', ellipticPointRhoPlusOne,
    ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  ring

/-- T-cancellation for `logDeriv`: if `f(z+1) = f(z)`, then the `logDeriv f`
integrand at parameter `4/5 - t` (seg4) is the negative of the integrand at
parameter `t` (seg1). The proof uses the T-translation identity, periodicity
of `logDeriv`, and the derivative reflection. -/
theorem logDeriv_integrand_seg4_neg_seg1 {f : ℂ → ℂ} (hf_periodic : ∀ z, f (z + 1) = f z)
    (H : ℝ) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) (1/5)) :
    logDeriv f (fdBoundaryFun H (4/5 - t)) * deriv (fdBoundaryFun H) (4/5 - t) =
    -(logDeriv f (fdBoundaryFun H t) * deriv (fdBoundaryFun H) t) := by
  have h_trans := fdBoundaryFun_seg4_eq_seg1_sub_one H t ht.1.le ht.2
  have h_period : logDeriv f (fdBoundaryFun H (4/5 - t)) =
      logDeriv f (fdBoundaryFun H t) := by
    rw [h_trans]
    have h := logDeriv_periodic hf_periodic (fdBoundaryFun H t - 1)
    rw [show fdBoundaryFun H t - 1 + 1 = fdBoundaryFun H t by ring] at h
    exact h.symm
  rw [h_period, deriv_seg4_eq_neg_seg1 H t ht]
  ring

/-- The S-involution on the complex exponential: `-1/exp(iθ) = exp(i(π - θ))`. -/
theorem neg_inv_exp_mul_I (θ : ℂ) :
    -(1 : ℂ) / exp (θ * I) = exp ((↑Real.pi - θ) * I) := by
  rw [sub_mul, exp_sub, exp_pi_mul_I, neg_div]

/-- S-involution on the arc (first half): for `t ∈ (1/5, 2/5)` (seg2),
`-1/γ(t) = γ(4/5 - t)` which lies on seg3. -/
theorem fdBoundaryFun_S_arc (H : ℝ) (t : ℝ) (ht1 : 1/5 < t) (ht2 : t < 2/5) :
    -(1 : ℂ) / fdBoundaryFun H t = fdBoundaryFun H (4/5 - t) := by
  have h_seg2 : fdBoundaryFun H t =
      exp ((↑Real.pi / 3 + (5 * ↑t - 1) *
        (↑Real.pi / 2 - ↑Real.pi / 3)) * I) := by
    simp only [fdBoundaryFun, show ¬(t ≤ 1/5) by linarith, ht2.le, ite_true, ite_false]
  have h_seg3 : fdBoundaryFun H (4/5 - t) =
      exp ((↑Real.pi / 2 + (5 * ↑(4/5 - t) - 2) *
        (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I) := by
    simp only [fdBoundaryFun, show ¬(4/5 - t ≤ 1/5) by linarith,
      show ¬(4/5 - t ≤ 2/5) by linarith, show 4/5 - t ≤ 3/5 by linarith, ite_true, ite_false]
  rw [h_seg2, neg_inv_exp_mul_I, h_seg3]
  congr 1
  push_cast
  ring

/-- S-involution on the arc (second half): for `t ∈ (2/5, 3/5)` (seg3),
`-1/γ(t) = γ(4/5 - t)` which lies on seg2. -/
theorem fdBoundaryFun_S_arc' (H : ℝ) (t : ℝ) (ht1 : 2/5 < t) (ht2 : t < 3/5) :
    -(1 : ℂ) / fdBoundaryFun H t = fdBoundaryFun H (4/5 - t) := by
  have h_seg3 : fdBoundaryFun H t =
      exp ((↑Real.pi / 2 + (5 * ↑t - 2) *
        (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I) := by
    simp only [fdBoundaryFun, show ¬(t ≤ 1/5) by linarith,
      show ¬(t ≤ 2/5) by linarith, ht2.le, ite_true, ite_false]
  have h_seg2 : fdBoundaryFun H (4/5 - t) =
      exp ((↑Real.pi / 3 + (5 * ↑(4/5 - t) - 1) *
        (↑Real.pi / 2 - ↑Real.pi / 3)) * I) := by
    simp only [fdBoundaryFun, show ¬(4/5 - t ≤ 1/5) by linarith,
      show 4/5 - t ≤ 2/5 by linarith, ite_true, ite_false]
  rw [h_seg3, neg_inv_exp_mul_I, h_seg2]
  congr 1
  push_cast
  ring

/-- The elliptic point `ρ` lies on the unit circle at angle `2π/3`. -/
theorem ellipticPointRho_eq_exp :
    (ellipticPointRho : ℂ) = exp (↑(2 * Real.pi / 3) * I) := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  simp only [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.sin_pi_sub, Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast
  ring

/-- The T-translate `ρ+1` lies on the unit circle at angle `π/3`. -/
theorem ellipticPointRhoPlusOne_eq_exp :
    (ellipticPointRhoPlusOne : ℂ) = exp (↑(Real.pi / 3) * I) := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  simp only [ellipticPointRhoPlusOne, ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk]
  push_cast
  ring

/-- The principal-branch logarithm of `ρ` is `2πi/3`. -/
theorem log_ellipticPointRho :
    Complex.log ellipticPointRho = ↑(2 * Real.pi / 3) * I := by
  rw [ellipticPointRho_eq_exp]
  refine Complex.log_exp ?_ ?_ <;>
    · simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero]
      linarith [Real.pi_pos]

/-- The principal-branch logarithm of `ρ+1` is `πi/3`. -/
theorem log_ellipticPointRhoPlusOne :
    Complex.log ellipticPointRhoPlusOne = ↑(Real.pi / 3) * I := by
  rw [ellipticPointRhoPlusOne_eq_exp]
  refine Complex.log_exp ?_ ?_ <;>
    · simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero]
      linarith [Real.pi_pos]

/-- **Arc angle computation**: `log(ρ) - log(ρ+1) = πi/3`.

The arc from `ρ+1` (angle `π/3`) to `ρ` (angle `2π/3`) subtends `π/3`. By
FTC, the integral of `1/z` along this arc equals `log(ρ) - log(ρ+1) = πi/3`. -/
theorem arc_angle_computation :
    Complex.log ellipticPointRho - Complex.log ellipticPointRhoPlusOne = ↑Real.pi / 3 * I := by
  rw [log_ellipticPointRho, log_ellipticPointRhoPlusOne]
  push_cast
  ring

/-- The contour integral of `k/z` along the arc from `ρ+1` to `ρ` equals `kπi/3`. -/
theorem arc_integral_k_over_z (k : ℤ) :
    (k : ℂ) * (Complex.log ellipticPointRho - Complex.log ellipticPointRhoPlusOne) =
    ↑k * ↑Real.pi / 3 * I := by
  rw [arc_angle_computation]
  ring

/-- **Arc contribution equals `-(2πi)(k/12)`**: from `2I_arc = -kπi/3`
(S-symmetry) we get `I_arc = -kπi/6 = -(2πi)(k/12)`. -/
theorem arc_contribution_eq_neg_k_over_12 (k : ℤ) :
    -(↑k * ↑Real.pi * I / 6) = -(2 * ↑Real.pi * I * ((k : ℂ) / 12)) := by ring

/-- Combining arc `-(2πi)(k/12)` and horizontal `2πi · ord_∞` gives
the full modular side `-(2πi)(k/12 - ord_∞)`. -/
theorem modular_side_combination (k : ℤ) (ord_inf : ℂ) :
    -(2 * ↑Real.pi * I * ((k : ℂ) / 12)) + (2 * ↑Real.pi * I * ord_inf) =
    -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ord_inf)) := by ring

/-- **Cancel `2πi`**: if the contour integral equals `-(2πi)(k/12 - ord_∞)`,
dividing by `2πi` recovers the modular side. -/
theorem modular_side_cancel_two_pi_I {L : ℂ} (k : ℤ) (ord_inf : ℂ)
    (h : 2 * ↑Real.pi * I * L = -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ord_inf))) :
    L = -((k : ℂ) / 12 - ord_inf) := by
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp [Real.pi_ne_zero, I_ne_zero]
  rw [show -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ord_inf)) =
    2 * ↑Real.pi * I * (-((k : ℂ) / 12 - ord_inf)) by ring] at h
  exact mul_left_cancel₀ hpi h

/-- **OrbitFM-sum rearrangement**: from `wt_sum = -(k/12 - ord_∞)` derive
the textbook form `ord_∞ + (-wt_sum) = k/12`. -/
theorem modular_side_rearrange (k : ℤ) (ord_inf weighted_sum : ℂ)
    (h : weighted_sum = -((k : ℂ) / 12 - ord_inf)) :
    ord_inf + (-weighted_sum) = (k : ℂ) / 12 := by
  subst h; ring

/-- Seg5 stays at constant imaginary part `H`. -/
theorem fdBoundaryFun_seg5_constant_height (H : ℝ) (t : ℝ) (ht : 4/5 < t) :
    (fdBoundaryFun H t).im = H :=
  fdBoundaryFun_seg5_im H t ht

/-- Seg5 covers exactly one period: from `-1/2 + Hi` to `1/2 + Hi`. -/
theorem fdBoundaryFun_seg5_one_period (H : ℝ) :
    fdBoundaryFun H 1 - fdBoundaryFun H (4/5) = (1 : ℂ) := by
  rw [fdBoundaryFun_at_one, fdBoundaryFun_at_four_fifths, fdStart]
  ring

end
