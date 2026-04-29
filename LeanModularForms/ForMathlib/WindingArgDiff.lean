/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.WindingInteger

/-!
# Winding number via continuous arg lift

For a closed piecewise C¹ path `γ` avoiding a point `w` (with positive distance), the
generalized winding number of `γ` around `w` equals `(θ(1) - θ(0)) / (2π)`, where
`θ : ℝ → ℝ` is the continuous arg lift along `γ - w` from
`Complex.exists_continuous_arg_lift_of_avoids` (W-1).

## Strategy

Choose a partition `s_j = j/N` of `[0, 1]` fine enough that on each `[s_j, s_{j+1}]`,
the ratio `(γ(t) - w) / (γ(s_j) - w)` lies in `Complex.slitPlane`. On each segment,
`Complex.log((γ(t) - w) / (γ(s_j) - w))` is a continuously differentiable primitive of
`γ'(t)/(γ(t) - w)` (chain rule + `HasDerivAt.clog_real`). Apply the FTC variant with
countable exception set (`MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`)
on each segment, and sum via `intervalIntegral.sum_integral_adjacent_intervals`.

## Main results

* `Complex.contourIntegral_inv_eq_sum_log_segRatio` — the contour integral of
  `(z - w)⁻¹` along `γ` equals a sum of complex logs of segment ratios.
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

namespace Complex

variable {x y : ℂ}

/-- **Contour integral as a sum of segment logs.** For γ : PiecewiseC1Path with γ avoiding
w (positive distance), choose any monotone partition `s : ℕ → ℝ` of `[0, 1]` such that
each segment ratio lies in `slitPlane`. Then the contour integral telescopes through
`Complex.log`. -/
theorem contourIntegral_inv_eq_sum_log_segRatio
    (γ : PiecewiseC1Path x y) {w : ℂ}
    {N : ℕ} (_hN : 0 < N) {s : ℕ → ℝ}
    (hs_zero : s 0 = 0) (hs_N : s N = 1) (hs_mono : Monotone s)
    (hs_in : ∀ j ≤ N, s j ∈ Icc (0 : ℝ) 1)
    (h_avoid : ∀ j ≤ N, γ.toPath.extend (s j) - w ≠ 0)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ.toPath.extend t - w) / (γ.toPath.extend (s j) - w) ∈ Complex.slitPlane)
    (h_int : IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1) :
    γ.contourIntegral (fun z => (z - w)⁻¹) =
      ∑ j ∈ Finset.range N,
        Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
          (γ.toPath.extend (s j) - w)) := by
  -- Step 1: contourIntegral = ∫₀¹ γ'(t) / (γ(t) - w) dt
  have h_eq_int : γ.contourIntegral (fun z => (z - w)⁻¹) =
      ∫ t in (0 : ℝ)..1, deriv γ.toPath.extend t / (γ.toPath.extend t - w) := by
    rw [PiecewiseC1Path.contourIntegral]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    show (γ.toPath.extend t - w)⁻¹ * deriv γ.toPath.extend t =
         deriv γ.toPath.extend t / (γ.toPath.extend t - w)
    rw [div_eq_mul_inv, mul_comm]
  rw [h_eq_int]
  -- Step 2: split into adjacent intervals via s
  have h_int_seg : ∀ k < N, IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume (s k) (s (k + 1)) := by
    intro k hk
    refine h_int.mono_set ?_
    rw [uIcc_of_le (zero_le_one' ℝ),
      uIcc_of_le (hs_mono (Nat.le_succ k))]
    exact Icc_subset_Icc (hs_in k hk.le).1 (hs_in (k + 1) hk).2
  rw [show (0 : ℝ) = s 0 from hs_zero.symm, show (1 : ℝ) = s N from hs_N.symm,
      ← intervalIntegral.sum_integral_adjacent_intervals h_int_seg]
  -- Step 3: each segment integral = log(segment ratio) via segment_log_FTC
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range] at hj
  -- Apply segment_log_FTC over [s j, s (j+1)]
  have hab : s j ≤ s (j + 1) := hs_mono (Nat.le_succ j)
  have hP_count : (γ.partition : Set ℝ).Countable := γ.partition.countable_toSet
  have hγ_cont : ContinuousOn γ.toPath.extend (Icc (s j) (s (j + 1))) :=
    γ.toPath.continuous_extend.continuousOn
  have hγ_diff : ∀ t ∈ Ioo (s j) (s (j + 1)) \ (γ.partition : Set ℝ),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t := by
    intro t ht
    have ht_open : t ∈ Ioo (0 : ℝ) 1 := by
      have h_lo : (0 : ℝ) < t := lt_of_le_of_lt (hs_in j hj.le).1 ht.1.1
      have h_hi : t < 1 := lt_of_lt_of_le ht.1.2 (hs_in (j + 1) hj).2
      exact ⟨h_lo, h_hi⟩
    exact (γ.differentiable_off t ht_open ht.2).hasDerivAt
  have h_a_ne : γ.toPath.extend (s j) - w ≠ 0 := h_avoid j hj.le
  have h_slit_seg : ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ.toPath.extend t - w) / (γ.toPath.extend (s j) - w) ∈ Complex.slitPlane :=
    h_slit j hj
  have h_int_seg_j := h_int_seg j hj
  exact segment_log_FTC hab hP_count hγ_cont hγ_diff h_a_ne h_slit_seg h_int_seg_j

/-- **Real-imaginary decomposition of contour integral.** Under the same fine-partition
hypotheses, the contour integral splits as `↑(log‖γ 1 - w‖ - log‖γ 0 - w‖) + I · ↑(sum
of imaginary parts of segment logs)`. -/
theorem contourIntegral_inv_decomp
    (γ : PiecewiseC1Path x y) {w : ℂ}
    {N : ℕ} (hN : 0 < N) {s : ℕ → ℝ}
    (hs_zero : s 0 = 0) (hs_N : s N = 1) (hs_mono : Monotone s)
    (hs_in : ∀ j ≤ N, s j ∈ Icc (0 : ℝ) 1)
    (h_avoid : ∀ j ≤ N, γ.toPath.extend (s j) - w ≠ 0)
    (h_slit : ∀ j, j < N → ∀ t ∈ Icc (s j) (s (j + 1)),
      (γ.toPath.extend t - w) / (γ.toPath.extend (s j) - w) ∈ Complex.slitPlane)
    (h_int : IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1) :
    γ.contourIntegral (fun z => (z - w)⁻¹) =
      ((Real.log ‖γ.toPath.extend 1 - w‖ - Real.log ‖γ.toPath.extend 0 - w‖ : ℝ) : ℂ) +
      Complex.I *
        ((∑ j ∈ Finset.range N,
            (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                          (γ.toPath.extend (s j) - w))).im : ℝ) : ℂ) := by
  rw [contourIntegral_inv_eq_sum_log_segRatio γ hN hs_zero hs_N hs_mono hs_in h_avoid h_slit h_int]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
    rw [Complex.re_sum]
    calc ∑ j ∈ Finset.range N,
            (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                          (γ.toPath.extend (s j) - w))).re
        = ∑ j ∈ Finset.range N,
            (Real.log ‖γ.toPath.extend (s (j + 1)) - w‖ -
             Real.log ‖γ.toPath.extend (s j) - w‖) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [Finset.mem_range] at hj
          rw [Complex.log_re, norm_div,
              Real.log_div (norm_ne_zero_iff.mpr (h_avoid (j + 1) hj))
                (norm_ne_zero_iff.mpr (h_avoid j hj.le))]
      _ = Real.log ‖γ.toPath.extend (s N) - w‖ -
            Real.log ‖γ.toPath.extend (s 0) - w‖ :=
          Finset.sum_range_sub (fun j => Real.log ‖γ.toPath.extend (s j) - w‖) N
      _ = _ := by rw [hs_N, hs_zero]
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, zero_add, one_mul]
    exact Complex.im_sum _ _

/-! ### Main theorem: closed-curve winding via arg lift -/

/-- **W-2 (Winding via arg difference).** For a closed piecewise C¹ path `γ` avoiding `w`
with positive distance, there exists a continuous arg lift `θ` of `γ - w` such that
the generalized winding number of `γ` around `w` equals `(θ(1) - θ(0)) / (2π)`. -/
theorem hasGeneralizedWindingNumber_eq_arg_diff_W1_closed
    (γ : PiecewiseC1Path x x) {w : ℂ}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - w‖)
    (h_int : IntervalIntegrable
      (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - w))
      MeasureTheory.volume 0 1) :
    ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t - w =
        (‖γ.toPath.extend t - w‖ : ℂ) * Complex.exp (Complex.I * (θ t : ℂ))) ∧
      HasGeneralizedWindingNumber γ w (((θ 1 - θ 0 : ℝ) : ℂ) / (2 * Real.pi)) := by
  obtain ⟨d, hd_pos, hd_bd⟩ := hδ
  have h_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t ≠ w := fun t ht heq => by
    have := hd_bd t ht
    rw [heq, sub_self, norm_zero] at this; linarith
  have hγ_cont : ContinuousOn γ.toPath.extend (Icc (0 : ℝ) 1) :=
    γ.toPath.continuous_extend.continuousOn
  obtain ⟨N, s, hN_pos, hs_zero, hs_N, hs_mono, hs_in, hs_avoid, h_slit, hθ_cont, h_lift⟩ :=
    Complex.exists_continuous_arg_lift_with_partition hγ_cont h_avoid
  -- θ has the explicit W-1 form
  set θ : ℝ → ℝ := fun t =>
    Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log (Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) t)).im with hθ_def
  refine ⟨θ, hθ_cont, h_lift, ?_⟩
  -- contourIntegral = ↑(log ‖γ 1‖ - log ‖γ 0‖) + I · ↑(sum Im)
  have h_contour := contourIntegral_inv_decomp γ hN_pos hs_zero hs_N hs_mono hs_in
    hs_avoid h_slit h_int
  -- θ(0) = arg(γ 0 - w)
  have h_θ_zero : θ 0 = Complex.arg (γ.toPath.extend 0 - w) := by
    show Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log (Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) 0)).im =
      Complex.arg (γ.toPath.extend 0 - w)
    have h_each : ∀ j ∈ Finset.range N,
        (Complex.log (Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) 0)).im = 0 := by
      intro j hj
      rw [Finset.mem_range] at hj
      have h_le : (0 : ℝ) ≤ s j := (hs_in j hj.le).1
      have h_eq_one : Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) 0 = 1 :=
        Complex.segRatio_eq_one_of_le (hs_mono (Nat.le_succ _)) h_le (hs_avoid j hj.le)
      rw [h_eq_one, Complex.log_one]; rfl
    rw [Finset.sum_eq_zero h_each, add_zero]
  -- θ(1) = arg(γ 0 - w) + sum
  have h_θ_one : θ 1 = Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                      (γ.toPath.extend (s j) - w))).im := by
    show Complex.arg (γ.toPath.extend 0 - w) +
      ∑ j ∈ Finset.range N,
        (Complex.log (Complex.segRatio γ.toPath.extend w (s j) (s (j + 1)) 1)).im = _
    apply congrArg (Complex.arg (γ.toPath.extend 0 - w) + ·)
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    have h_le : s (j + 1) ≤ 1 := by
      have : s (j + 1) ≤ s N := hs_mono hj
      rwa [hs_N] at this
    rw [Complex.segRatio_eq_full (hs_mono (Nat.le_succ _)) h_le]
  -- θ(1) - θ(0) = sum
  have h_θ_diff : (θ 1 - θ 0 : ℝ) =
      ∑ j ∈ Finset.range N,
        (Complex.log ((γ.toPath.extend (s (j + 1)) - w) /
                      (γ.toPath.extend (s j) - w))).im := by
    rw [h_θ_one, h_θ_zero]; ring
  -- For closed γ: real part of contour integral = 0
  have h_closed_eq : γ.toPath.extend 1 = γ.toPath.extend 0 := by
    rw [γ.toPath.extend_one, γ.toPath.extend_zero]
  have h_re_zero : Real.log ‖γ.toPath.extend 1 - w‖ -
      Real.log ‖γ.toPath.extend 0 - w‖ = 0 := by
    rw [h_closed_eq]; ring
  -- Apply hasGeneralizedWindingNumber_of_avoids
  have hδ' : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - w‖ :=
    ⟨d, hd_pos, hd_bd⟩
  have h_w := hasGeneralizedWindingNumber_of_avoids (γ := γ) (z₀ := w) hδ'
  rw [h_contour, h_re_zero, Complex.ofReal_zero, zero_add, ← h_θ_diff] at h_w
  -- h_w : HasGeneralizedWindingNumber γ w ((2 π I)⁻¹ * (I * ↑(θ 1 - θ 0)))
  -- We want : HasGeneralizedWindingNumber γ w (↑(θ 1 - θ 0) / (2 π))
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h_value_eq : ((θ 1 - θ 0 : ℝ) : ℂ) / (2 * Real.pi) =
      (2 * ↑Real.pi * Complex.I)⁻¹ * (Complex.I * ((θ 1 - θ 0 : ℝ) : ℂ)) := by
    field_simp
  rw [h_value_eq]
  exact h_w

end Complex

end
