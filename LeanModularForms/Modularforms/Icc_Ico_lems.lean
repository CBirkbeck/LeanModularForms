module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Cases

/-!
# Auxiliary lemmas on symmetric integer intervals

Small utility lemmas relating `Finset.Icc (-N) N` and `Finset.Ico (-N) N` to smaller
intervals, used in the modular forms development for manipulating symmetric sums.
-/

@[expose] public section

open TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

lemma Icc_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
  {(-(n+1) : ℤ), (n + 1 : ℤ)} := by
  refine Finset.ext_iff.mpr ?_
  intro a
  simp only [neg_add_rev, Int.reduceNeg, Finset.mem_Icc, add_neg_le_iff_le_add, Finset.union_insert,
    Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
  omega


lemma Icc_sum_even (f : ℤ → ℂ) (hf : ∀ n, f n = f (-n)) (N : ℕ) :
    ∑ m ∈ Finset.Icc (-N : ℤ) N, f m = 2 * ∑ m ∈ Finset.range (N + 1), f m - f 0 := by
  induction N with
  | zero =>
    simp only [CharP.cast_eq_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton,
      zero_add, Finset.range_one]
    ring
  | succ N ih =>
    have := Icc_succ N
    simp only [neg_add_rev, Int.reduceNeg, Nat.cast_add, Nat.cast_one] at *
    rw [this, Finset.sum_union, Finset.sum_pair, ih]
    · nth_rw 2 [Finset.sum_range_succ]
      have HF:= hf (N + 1)
      simp only [neg_add_rev, Int.reduceNeg] at HF
      rw [← HF]
      ring_nf
      norm_cast
    · omega
    simp only [Int.reduceNeg, Finset.disjoint_insert_right, Finset.mem_Icc, le_add_iff_nonneg_left,
      Left.nonneg_neg_iff, Int.reduceLE, add_neg_le_iff_le_add, false_and, not_false_eq_true,
      Finset.disjoint_singleton_right, add_le_iff_nonpos_right, and_false, and_self]

