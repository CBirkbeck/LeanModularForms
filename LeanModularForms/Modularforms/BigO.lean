/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence

@[expose] public section

/-!
# Big-O bounds for linear combinations on the upper half plane

Big-O bounds along `cofinite` for `(m z + n)⁻¹` and related expressions, used to deduce
summability of Eisenstein-style series.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

lemma linear_bigO (m : ℤ) (z : ℍ) : (fun n : ℤ ↦ ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n ↦ (|(n : ℝ)|⁻¹) := by
  have h1 : (fun (n : ℤ) ↦ ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    (fun n : ℤ ↦ ((r z * ‖![n, m]‖))⁻¹) := by
    rw [Asymptotics.isBigO_iff']
    use 1
    simp
    constructor
    repeat{
    use 0
    intro n hn
    have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![m, n]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ge_iff_le] at *
    nth_rw 2 [mul_comm]
    simp_rw [Real.rpow_neg_one] at this
    have hr : (r z)⁻¹ = |r z|⁻¹ := by rw [abs_of_pos (r_pos z)]
    rw [← hr, EisensteinSeries.norm_symm]
    exact this}
  apply Asymptotics.IsBigO.trans h1
  rw [Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp; exact r_pos z, ?_⟩
  simp
  constructor
  · use min (-1) m
    intro n hn
    rw [mul_comm]
    gcongr
    · simp [(r_pos z).le]
    · exact r_pos z
    · exact le_abs_self (r z)
    · simp; omega
    · rw [EisensteinSeries.norm_eq_max_natAbs]
      simp
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp only [abs_pos, ne_eq, Int.cast_eq_zero]; omega
  · simp

lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) :
    (fun n : ℤ ↦ (((m : ℂ) * z + n) ^ k)⁻¹) =O[cofinite] fun n ↦ (|(n : ℝ)| ^ k)⁻¹ := by
  simp_rw [← inv_pow]
  exact (linear_bigO m z).pow k

private lemma Asymptotics.IsBigO.zify {α β : Type*} [Norm α] [Norm β] {f : ℤ → α} {g : ℤ → β}
    (hf : f =O[cofinite] g) : (fun n : ℕ ↦ f n) =O[cofinite] fun n ↦ g n := by
  rw [isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  rw [Int.cofinite_eq] at hC
  rw [Nat.cofinite_eq_atTop]
  apply Filter.Eventually.natCast_atTop (p := fun n ↦ ‖f n‖ ≤ C * ‖g n‖)
  simp_all only [eventually_sup, eventually_atBot, eventually_atTop, ge_iff_le]

lemma linear_bigO_nat (m : ℤ) (z : ℍ) : (fun n : ℕ ↦ ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n ↦ (|(n : ℝ)|⁻¹) :=
  (linear_bigO m z).zify

lemma linear_bigO' (m : ℤ) (z : ℍ) : (fun (n : ℤ) ↦ ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    fun n ↦ (|(n : ℝ)|⁻¹) := by
  have h1 : (fun (n : ℤ) ↦ ((n : ℂ) * z + m)⁻¹) =O[cofinite]
    (fun n : ℤ ↦ ((r z * ‖![m, n]‖))⁻¹) := by
    rw [Asymptotics.isBigO_iff']
    use 1
    simp
    constructor
    repeat{
      use 0
      intro n hn
      have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![n, m]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, ge_iff_le] at *
      nth_rw 2 [mul_comm]
      simp_rw [Real.rpow_neg_one] at this
      have hr : (r z)⁻¹ = |r z|⁻¹ := by rw [abs_of_pos (r_pos z)]
      rw [← hr, EisensteinSeries.norm_symm]
      exact this}
  apply Asymptotics.IsBigO.trans h1
  rw [Asymptotics.isBigO_iff']
  use (r z)⁻¹
  refine ⟨by simp; exact r_pos z, ?_⟩
  simp
  constructor
  · use min (-1) m
    intro n hn
    rw [mul_comm]
    gcongr
    · simp [(r_pos z).le]
    · exact r_pos z
    · exact le_abs_self (r z)
    · simp; omega
    · simp [EisensteinSeries.norm_eq_max_natAbs]
  use max 1 m
  intro b hb
  rw [EisensteinSeries.norm_eq_max_natAbs]
  simp
  rw [mul_comm]
  gcongr
  · simp [(r_pos z).le]
  · exact r_pos z
  · exact le_abs_self (r z)
  · simp; omega
  · simp
