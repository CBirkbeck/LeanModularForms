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

private lemma cc (f : ℤ → ℂ) (hc : CauchySeq fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, f m)
    (hs : ∀ n, f n = f (-n)) :
    Tendsto f atTop (𝓝 0) := by
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨g, hg, H, Hg⟩ := hc
  rw [Metric.tendsto_atTop] at *
  simp at *
  intro ε hε
  obtain ⟨N, hN⟩ := Hg (2 * ε) (by linarith)
  refine ⟨N + 1, fun n hn => ?_⟩
  have H3 := H n.natAbs (n - 1).natAbs N ?_ ?_
  · rw [trex f n.natAbs] at H3
    · simp [dist_eq_norm] at *
      have h1 : |n| = n := by simp; linarith
      simp_rw [h1] at H3
      have h2 : |n - 1| = n - 1 := by simp; linarith
      simp_rw [h2] at H3
      simp at H3
      rw [← hs n, show f n + f n = 2 * f n by ring] at H3
      simp at H3
      have HN := hN N (by rfl)
      have := le_trans H3 (le_abs_self (g N))
      nlinarith [lt_of_le_of_lt this HN]
    omega
  · omega
  omega

private lemma sum_Icc_eq_sum_Ico_succ {α : Type*} [AddCommMonoid α] (f : ℤ → α)
    {l u : ℤ} (h : l ≤ u) :
    ∑ m ∈ Finset.Icc l u, f m = (∑ m ∈ Finset.Ico l u, f m) + f u := by
  rw [Finset.Icc_eq_cons_Ico h]
  simp only [Finset.cons_eq_insert, Finset.mem_Ico, lt_self_iff_false, and_false, not_false_eq_true,
    Finset.sum_insert, add_comm]

private lemma cauchySeq_Icc_iff_cauchySeq_Ico (f : ℤ → ℂ) (hs : ∀ n, f n = f (-n))
    (hc : CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Icc (-N : ℤ) N, f m)) :
    CauchySeq (fun N : ℕ => ∑ m ∈ Finset.Ico (-N : ℤ) N, f m) := by
  have h0 := cc f hc hs
  have hcs : CauchySeq fun n : ℕ => f n := by
    apply Filter.Tendsto.cauchySeq (x := 0)
    rw [Metric.tendsto_atTop] at *
    intro ε hε
    obtain ⟨N, hN⟩ := h0 ε hε
    refine ⟨N.natAbs, fun n hn => ?_⟩
    simp at *
    exact hN n (by omega)
  simp_rw [cauchySeq_iff_le_tendsto_0] at *
  obtain ⟨b, hb, H, hbb⟩ := hc
  obtain ⟨a, ha, H2, haa⟩ := hcs
  refine ⟨b + a, fun n => ?_, fun n m N hn hm => ?_, ?_⟩
  · simp
    exact add_nonneg (hb n) (ha n)
  · have H3 := H n m N hn hm
    simp [dist_eq_norm] at *
    rw [sum_Icc_eq_sum_Ico_succ _, sum_Icc_eq_sum_Ico_succ _] at H3
    · refine le_trans (norm_le_add_norm_add _ (f n - f m)) ?_
      gcongr
      · refine le_trans (le_of_eq ?_) H3
        congr 1
        ring
      exact H2 n m N hn hm
    · omega
    omega
  · simpa using Filter.Tendsto.add hbb haa

private theorem extracted_2 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, 1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
    ((b : ℂ) * ↑z + ↑x + 1)⁻¹ * (((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹)
  have ht := (G2_prod_summable1 z b).hasSum.comp verga
  simp at *
  apply ht

private theorem extracted_2_δ (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / (((b : ℂ) * ↑z + ↑n) ^ 2 * (↑b * ↑z + ↑n + 1)) + δ b n) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ),
    (((b : ℂ) * ↑z + ↑x + 1)⁻¹ * (((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹ + δ b x))
  have ht := (G2_prod_summable1_δ z b).hasSum.comp verga
  simp at *
  apply ht

private theorem telescope_aux (z : ℍ) (m : ℤ) (b : ℕ) :
    ∑ n ∈ Finset.Ico (-b : ℤ) b, (1 / ((m : ℂ) * ↑z + ↑n) - 1 / (↑m * ↑z + ↑n + 1)) =
      1 / (↑m * ↑z - ↑b) - 1 / (↑m * ↑z + ↑b) := by
  induction b with
  | zero => aesop
  | succ b ihb =>
    simp only [Nat.cast_add, Nat.cast_one, one_div, Finset.sum_sub_distrib] at *
    rw [fsb, Finset.sum_union, Finset.sum_union, Finset.sum_pair, Finset.sum_pair,
      add_sub_add_comm, ihb]
    · simp only [neg_add_rev, Int.reduceNeg, Int.cast_add, Int.cast_neg, Int.cast_one,
        Int.cast_natCast]
      ring
    · omega
    · omega
    all_goals simp [Finset.disjoint_insert_right, Finset.disjoint_singleton_right]

private theorem extracted_3 (z : ℍ) (b : ℤ) : CauchySeq fun N : ℕ ↦
    ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) - 1 / (↑b * ↑z + ↑n + 1)) := by
  conv =>
    enter [1]
    intro d
    rw [telescope_aux]
  apply Filter.Tendsto.cauchySeq (x := 0)
  have h1 : Tendsto (fun d : ℕ ↦ 1 / ((b : ℂ) * ↑z - ↑d)) atTop (𝓝 0) := by
    have := tendsto_zero_inv_linear z (-b)
    rw [← tendsto_const_smul_iff₀ (c := (-1 : ℂ))] at this
    · simp at *
      refine this.congr fun x => ?_
      rw [neg_inv]
      congr 1
      ring
    · norm_cast
  simpa using h1.sub (tendsto_zero_inv_linear z b)

private theorem extracted_4 (z : ℍ) (b : ℤ) :
    CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z + ↑n) ^ 2) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * ↑z + ↑x) ^ 2)⁻¹))
  have ht := (G2_summable_aux b z 2 (by norm_num)).hasSum.comp verga
  simp at *
  apply ht

private theorem extracted_5 (z : ℍ) (b : ℤ) :
    CauchySeq fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N, (1 / ((b : ℂ) * ↑z - ↑n) ^ 2) := by
  apply Filter.Tendsto.cauchySeq (x := ∑' (x : ℤ), ((((b : ℂ) * ↑z - ↑x) ^ 2)⁻¹))
  have ht := (summable_neg _ (G2_summable_aux b z 2 (by norm_num))).hasSum.comp verga
  simp at *
  have := ht.congr' (f₂ := fun N : ℕ ↦ ∑ n ∈ Finset.Ico (-↑N : ℤ) ↑N,
    (1 / ((b : ℂ) * ↑z - ↑n) ^ 2)) ?_
  · simp at this
    apply this
  refine Filter.Eventually.of_forall fun N => ?_
  simp
  congr

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
