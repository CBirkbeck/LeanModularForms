/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.Modularforms.tendstolems
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Logarithmic derivative lemmas

Auxiliary lemmas on logarithmic derivatives of infinite products, used in the analysis of
the eta and related modular functions.

## Main results

* `logDeriv_tprod_eq_tsum2`: the logarithmic derivative of a locally uniformly convergent
  infinite product is the sum of the logarithmic derivatives.
* `logDeriv_one_sub_exp`: closed form for the logarithmic derivative of `1 - r * exp`.
* `logDeriv_q_expo_summable`: summability of the series `n * r^n / (1 - r^n)`.
* `logDeriv_eqOn_iff2`: two nonvanishing holomorphic functions with equal logarithmic
  derivative on a connected open convex set differ by a nonzero constant.
-/

open TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

theorem logDeriv_tprod_eq_tsum2 {s : Set ℂ} (hs : IsOpen s) (x : s) (f : ℕ → ℂ → ℂ)
    (hf : ∀ i, f i x ≠ 0)
    (hd : ∀ i : ℕ, DifferentiableOn ℂ (f i) s) (hm : Summable fun i ↦ logDeriv (f i) ↑x)
    (htend : MultipliableLocallyUniformlyOn f s) (hnez : ∏' (i : ℕ), f i ↑x ≠ 0) :
    logDeriv (∏' i : ℕ, f i ·) x = ∑' i : ℕ, logDeriv (f i) x := by
  have h2 := Summable.hasSum hm
  rw [Summable.hasSum_iff_tendsto_nat hm] at h2
  apply symm
  rw [← Summable.hasSum_iff hm, Summable.hasSum_iff_tendsto_nat hm]
  let g := (∏' i : ℕ, f i ·)
  have h_tlu : TendstoLocallyUniformlyOn (fun n z ↦ ∏ i ∈ Finset.range n, f i z) g atTop s := by
    have := htend.hasProdLocallyUniformlyOn.tendstoLocallyUniformlyOn_finsetRange
    exact this.congr (fun n => by intro z _; rfl)
  have h_diff : ∀ᶠ (n : ℕ) in atTop,
      DifferentiableOn ℂ (fun z => ∏ i ∈ Finset.range n, f i z) s := by
    simp only [eventually_atTop, ge_iff_le]
    use 0
    intro b _ z hz
    have := DifferentiableAt.finset_prod (fun i (_ : i ∈ Finset.range b) =>
      (hd i z hz).differentiableAt (IsOpen.mem_nhds hs hz))
    exact this.differentiableWithinAt.congr (fun w hw => (Finset.prod_apply ..).symm)
      (Finset.prod_apply ..).symm
  have HT := logDeriv_tendsto (f := fun (n : ℕ) z ↦ ∏ i ∈ Finset.range n, f i z) (g := g)
    (s := s) hs (x.2) (p := atTop) h_tlu h_diff hnez
  conv =>
    enter [1]
    ext n
    rw [← logDeriv_prod (by intro i hi; apply hf i)
      (by intro i hi; apply (hd i x x.2).differentiableAt; exact IsOpen.mem_nhds hs x.2)]
  exact HT

lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z => 1 - r * cexp (z)) =
    fun z => -r * cexp z / (1 - r * cexp (z)) := by
  ext z
  rw [logDeriv]
  simp only [Pi.div_apply, differentiableAt_const, differentiableAt_exp, DifferentiableAt.fun_mul,
    deriv_fun_sub, deriv_const', deriv_fun_mul, zero_mul, Complex.deriv_exp, zero_add, zero_sub,
    neg_mul]

lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) :
    Summable fun n : ℕ => (n * r^n / (1 - r^n)) := by
  have := aux47 r hr
  have h1 : Tendsto (fun n : ℕ => (1 : ℂ)) atTop (𝓝 1) := by simp
  have h2 := Filter.Tendsto.div h1 this (by simp)
  rw [Metric.tendsto_atTop] at h2
  simp only [gt_iff_lt, ge_iff_le, Pi.div_apply, one_div, ne_eq, one_ne_zero, not_false_eq_true,
    div_self, dist_eq_norm] at h2
  have h3 := h2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat (g := fun n => 2 * ‖n * r^n‖)
  · apply Summable.mul_left
    simp
    have := (summable_norm_pow_mul_geometric_of_norm_lt_one 1 hr)
    simp at this
    apply this
  · simp
    obtain ⟨N, hN⟩ := h3
    use N
    intro n hn
    have h4 := hN n hn
    have hdist : dist ((1 - r ^ n)⁻¹) 1 < 1 := by rwa [dist_eq_norm]
    have := norm_lt_of_mem_ball (Metric.mem_ball.mpr hdist) (E := ℂ)
    simp at *
    rw [div_eq_mul_inv, mul_comm]
    gcongr
    apply le_trans this.le
    norm_cast
