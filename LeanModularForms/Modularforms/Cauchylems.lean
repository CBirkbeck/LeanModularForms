/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.Modularforms.Icc_Ico_lems
public import LeanModularForms.Modularforms.riemannZetalems
public import LeanModularForms.Modularforms.summable_lems

/-!
# Cauchy sequence lemma for `G_2` partial sums

This file proves that the symmetric partial sums on `Finset.Icc (-N) N` of the
term-by-term `tsum` defining the weight-two Eisenstein series `G_2` form a Cauchy
sequence, via an equality with `2 * riemannZeta 2` plus a convergent
exponential `q`-expansion-style series.

## Main results

* `G2_cauchy`: the partial sums of `G_2` on `Finset.Icc (-N) N` are Cauchy.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat ArithmeticFunction.sigma

private noncomputable def summable_term (z : ℍ) : ℤ → ℂ :=
  fun m : ℤ ↦ ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2

private lemma summable_term_neg (z : ℍ) (m : ℤ) : summable_term z m = summable_term z (-m) := by
  simp only [summable_term]
  nth_rw 1 [int_sum_neg]
  congr 1
  funext n
  push_cast
  ring

private lemma sum_Icc_tsum_eq_two_zeta_two_add_range (z : ℍ) :
    (fun N : ℕ ↦ ∑ m ∈ Finset.Icc (-N : ℤ) N, ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2) =
      (fun _ : ℕ ↦ 2 * riemannZeta 2) +
        fun N : ℕ ↦ ∑ m ∈ Finset.range N, 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
          ∑' n : ℕ+, n ^ (2 - 1) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n) := by
  funext m
  simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
    Nat.cast_one, div_one, pow_one, Pi.add_apply]
  rw [Icc_sum_even]
  · simp only [Int.cast_natCast, Int.cast_zero, zero_mul, zero_add]
    rw [zeta_two_eqn]
    nth_rw 2 [add_comm]
    have hsr := sum_range_zero (fun m ↦ ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2) m
    simp only [Int.cast_natCast, one_div, Int.cast_zero, zero_mul, zero_add, Int.cast_add,
      Int.cast_one] at hsr
    rw [hsr, zeta_two_eqn, add_comm, mul_add, ← mul_assoc, show
      ∀ a c : ℂ, a + 2 * 2 * c - 2 * c = a + 2 * c from fun _ _ ↦ by ring]
    congr
    rw [Finset.mul_sum]
    congr
    ext d
    let Z : ℍ := ⟨(d + 1) * z, by simpa using mul_pos (by linarith : (0 : ℝ) < d + 1) z.2⟩
    have hq := q_exp_iden 2 (by norm_num) (z := Z)
    simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one,
      Nat.factorial_one, Nat.cast_one, div_one, pow_one, Z] at *
    rw [hq]
    ring_nf
    congr
    ext r
    congr 1
    ring_nf
  · intro n
    simpa [summable_term] using summable_term_neg z n

private theorem G2_c_tendsto (z : ℍ) :
    Tendsto (fun N ↦ ∑ x ∈ Finset.range N, 2 * (2 * ↑π * Complex.I) ^ 2 *
        ∑' n : ℕ+, ↑↑n * cexp (2 * ↑π * Complex.I * (↑x + 1) * ↑z * ↑↑n)) atTop
      (𝓝 (-8 * ↑π ^ 2 * ∑' n : ℕ+, ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) := by
  rw [← t9]
  have hf : Summable fun m : ℕ ↦ 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ (2 - 1) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n) := by
    conv =>
      enter [1]
      ext m
      rw [show (m : ℂ) + 1 = (((m + 1) : ℕ) : ℂ) by simp]
    rw [← nat_pos_tsum2' (f := fun m : ℕ ↦ 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ (2 - 1) * Complex.exp (2 * ↑π * Complex.I * m * z * n))]
    refine Summable.mul_left _ <| (a4 2 z).prod_symm.prod.congr fun b ↦ ?_
    congr
  have V := hf.hasSum.comp tendsto_finset_range
  simp at *
  apply V

/-- The partial sums on `Finset.Icc (-N) N` of the term-by-term tsum defining `G_2`
form a Cauchy sequence. -/
lemma G2_cauchy (z : ℍ) :
    CauchySeq fun N : ℕ ↦ ∑ m ∈ Finset.Icc (-N : ℤ) N, ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2 := by
  rw [sum_Icc_tsum_eq_two_zeta_two_add_range]
  simp
  exact CauchySeq.const_add <| Filter.Tendsto.cauchySeq <| G2_c_tendsto z
