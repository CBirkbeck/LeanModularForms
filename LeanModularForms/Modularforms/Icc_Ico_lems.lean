/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Int.Star
public import Mathlib.Tactic.Cases

/-!
# Auxiliary lemmas on `Finset.Icc` and `Finset.Ico` over `ℤ`

This file collects small structural and tendsto lemmas about symmetric integer
intervals `Finset.Icc (-N) N` and `Finset.Ico (-N) N`, used in the convergence
arguments for `G_2` and related series.
-/

@[expose] public section

open TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

lemma Icc_succ (n : ℕ) : Finset.Icc (-(n + 1) : ℤ) (n + 1) = Finset.Icc (-n : ℤ) n ∪
    {(-(n+1) : ℤ), (n + 1 : ℤ)} := by
  ext a
  simp
  omega

lemma Icc_sum_split_endpoints (f : ℤ → ℂ) (N : ℕ) (hn : 1 ≤ N) :
    ∑ m ∈ Finset.Icc (-N : ℤ) N, f m =
    f N + f (-N : ℤ) + ∑ m ∈ Finset.Icc (-(N - 1) : ℤ) (N - 1), f m := by
  induction N with
  | zero => omega
  | succ N _ =>
    zify
    rw [Icc_succ, Finset.sum_union]
    · ring_nf
      rw [add_assoc]
      congr
      rw [Finset.sum_pair (by omega)]
      ring
    · simp

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
      have HF := hf (N + 1)
      simp only [neg_add_rev, Int.reduceNeg] at HF
      rw [← HF]
      ring_nf
      norm_cast
    · omega
    · simp [Finset.disjoint_insert_right, Finset.disjoint_singleton_right, Finset.mem_Icc]

lemma tendsto_Icc_symm_atTop : Tendsto (fun N : ℕ ↦ Finset.Icc (-N : ℤ) N) atTop atTop :=
  tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Icc_subset_Icc (by gcongr) (by gcongr))
  (fun x ↦ ⟨x.natAbs, by simp [le_abs, neg_le]⟩)

lemma tendsto_Ico_symm_atTop : Tendsto (fun N : ℕ ↦ Finset.Ico (-N : ℤ) N) atTop atTop := by
  apply tendsto_atTop_finset_of_monotone (fun _ _ _ ↦ Finset.Ico_subset_Ico (by omega) (by gcongr))
  intro x
  refine ⟨x.natAbs + 1, ?_⟩
  simp only [Nat.cast_add, Int.natCast_natAbs, Nat.cast_one, neg_add_rev, Int.reduceNeg,
    Finset.mem_Ico, add_neg_le_iff_le_add]
  refine ⟨?_, Int.lt_add_one_iff.mpr (le_abs_self x)⟩
  have := neg_abs_le x
  omega

lemma Ico_succ_neg_split (b : ℕ) : Finset.Ico (-(b+1) : ℤ) (b+1) = Finset.Ico (-(b : ℤ)) (b) ∪
    {-((b+1) : ℤ), (b : ℤ)} := by
  ext n
  simp
  omega
