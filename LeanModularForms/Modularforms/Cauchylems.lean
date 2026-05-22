/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.Modularforms.Icc_Ico_lems
public import LeanModularForms.Modularforms.riemannZetalems
public import LeanModularForms.Modularforms.summable_lems

@[expose] public section

/-!
# Cauchy sequence lemmas for `G₂`

This file collects Cauchy-sequence and tendsto lemmas used in the construction of
the weight-`2` Eisenstein series `G₂`. The main result is `G2_cauchy`, which shows
that the partial sums of `G₂` over symmetric intervals form a Cauchy sequence.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

private lemma auxer (a c : ℂ) : a + 2 * 2 * c - 2 * c = a + 2 * c := by ring

private noncomputable def summable_term (z : ℍ) : ℤ → ℂ :=
  fun m : ℤ => ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2

private lemma term_even (z : ℍ) (m : ℤ) : summable_term z m = summable_term z (-m) := by
  simp [summable_term]
  nth_rw 1 [int_sum_neg]
  congr
  funext m
  simp
  ring

private lemma t8 (z : ℍ) :
    (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2) =
    (fun _ : ℕ => 2 * riemannZeta 2) +
    fun N : ℕ => ∑ m ∈ Finset.range N, 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ (2 - 1) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n) := by
  funext m
  simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one, Nat.factorial_one,
    Nat.cast_one, div_one, pow_one, Pi.add_apply]
  rw [Icc_sum_even]
  · simp only [Int.cast_natCast, Int.cast_zero, zero_mul, zero_add]
    rw [zeta_two_eqn]
    nth_rw 2 [add_comm]
    have := sum_range_zero (fun m => ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2) m
    simp only [Int.cast_natCast, one_div, Int.cast_zero, zero_mul, zero_add, Int.cast_add,
      Int.cast_one] at this
    rw [this, zeta_two_eqn, add_comm, mul_add, ← mul_assoc, auxer]
    congr
    rw [Finset.mul_sum]
    congr
    ext d
    let Z : ℍ := ⟨(d + 1) * z, by simp; exact mul_pos (by linarith) z.2⟩
    have := q_exp_iden 2 (by norm_num) (z := Z)
    simp only [one_div, neg_mul, even_two, Even.neg_pow, Nat.add_one_sub_one,
      Nat.factorial_one, Nat.cast_one, div_one, pow_one, Z] at *
    rw [this]
    ring_nf
    congr
    ext r
    congr 1
    ring_nf
  · intro n
    have := term_even z n
    simp [summable_term] at *
    exact this

private theorem G2_c_tendsto (z : ℍ) :
    Tendsto
      (fun N ↦ ∑ x ∈ Finset.range N,
        2 * (2 * ↑π * Complex.I) ^ 2 *
          ∑' (n : ℕ+), ↑↑n * cexp (2 * ↑π * Complex.I * (↑x + 1) * ↑z * ↑↑n))
      atTop (𝓝 (-8 * ↑π ^ 2 *
        ∑' (n : ℕ+), ↑((σ 1) ↑n) * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) := by
  rw [← t9]
  have hf : Summable fun m : ℕ => 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ (2 - 1) * Complex.exp (2 * ↑π * Complex.I * (m + 1) * z * n) := by
    conv =>
      enter [1]
      ext m
      rw [show (m : ℂ) + 1 = (((m + 1) : ℕ) : ℂ) by simp]
    have := nat_pos_tsum2' (f := fun m : ℕ => 2 * (-2 * ↑π * Complex.I) ^ 2 / (2 - 1)! *
      ∑' n : ℕ+, n ^ (2 - 1) * Complex.exp (2 * ↑π * Complex.I * m * z * n))
    rw [← this]
    apply Summable.mul_left
    refine (a4 2 z).prod_symm.prod.congr fun b => ?_
    congr
  have V := hf.hasSum.comp tendsto_finset_range
  simp at *
  apply V

lemma G2_cauchy (z : ℍ) :
    CauchySeq fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N,
      ∑' n : ℤ, 1 / ((m : ℂ) * z + n) ^ 2 := by
  rw [t8]
  simp
  apply CauchySeq.const_add
  apply Filter.Tendsto.cauchySeq
    (x := -8 * π ^ 2 * ∑' n : ℕ+, (σ 1 n) * cexp (2 * π * Complex.I * n * z))
  apply G2_c_tendsto z
