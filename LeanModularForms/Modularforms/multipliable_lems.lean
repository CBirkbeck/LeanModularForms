/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.Modularforms.summable_lems

@[expose] public section

/-!
# Multipliability lemmas

Auxiliary lemmas about `Multipliable` and `tprod` used in the eta and Delta product
expansions.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

/-- Summable `f` gives multipliable `1 + f` (being PRd to mathlib). -/
lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f) :
    Multipliable (fun n : ℕ ↦ 1 + f n) :=
  Complex.multipliable_of_summable_log (Complex.summable_log_one_add_of_summable hf)

theorem term_ne_zero (z : ℍ) (n : ℕ) : 1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑z) ≠ 0 := by
  rw [sub_ne_zero]
  intro h
  have := exp_upperHalfPlane_lt_one_nat z n
  rw [← h] at this
  simp at this

theorem multipliable_lt_one (x : ℂ) (hx : x ∈ ball 0 1) :
    Multipliable fun i ↦ 1 - x ^ (i + 1) := by
  have h := Complex.summable_nat_multipliable_one_add (fun n : ℕ ↦ -x ^ (n + 1)) ?_
  · simpa [sub_eq_add_neg] using h
  rw [summable_neg_iff, summable_nat_add_iff, summable_geometric_iff_norm_lt_one]
  simpa using hx

lemma MultipliableEtaProductExpansion (z : ℍ) :
    Multipliable fun n : ℕ ↦ 1 - cexp (2 * π * Complex.I * (n + 1) * z) := by
  have h := Complex.summable_nat_multipliable_one_add
    (fun n : ℕ ↦ -cexp (2 * π * Complex.I * (n + 1) * z)) ?_
  · simpa [sub_eq_add_neg] using h
  rw [← summable_norm_iff]
  simpa using summable_exp_pow z

lemma Multipliable_pow {ι : Type*} (f : ι → ℂ) (hf : Multipliable f) (n : ℕ) :
    Multipliable fun i ↦ f i ^ n := by
  induction n with
  | zero => simp
  | succ n hn => simpa [pow_succ] using hn.mul hf

lemma tprod_pow (f : ℕ → ℂ) (hf : Multipliable f) (n : ℕ) :
    (∏' i : ℕ, f i) ^ n = ∏' i : ℕ, f i ^ n := by
  induction n with
  | zero => simp
  | succ n hn =>
    rw [pow_succ, hn, ← Multipliable.tprod_mul (Multipliable_pow f hf n) hf]
    simp [pow_succ]
