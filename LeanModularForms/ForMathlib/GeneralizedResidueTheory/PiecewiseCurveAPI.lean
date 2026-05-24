/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ClassicalCPV
import Mathlib

/-!
# Piecewise C¹ Curve API

General-purpose API for proving properties of piecewise C¹ curves by checking each
consecutive segment defined by the partition.

## Main results

* `PiecewiseC1Curve.sortedPartition` - the partition points as a sorted list
* `PiecewiseC1Curve.consecutivePairs` - consecutive pairs (pᵢ, pᵢ₊₁) from the sorted partition
* `PiecewiseC1Curve.sortedPartition_head` - the first element of the sorted partition is `γ.a`
* `PiecewiseC1Curve.sortedPartition_last` - the last element of the sorted partition is `γ.b`
* `PiecewiseC1Curve.consecutivePairs_cover` - union of [pᵢ, pᵢ₊₁] covers [a,b]
* `PiecewiseC1Curve.forall_Icc_of_forall_consecutive` - prove a property on [a,b] from
  each consecutive interval [pᵢ, pᵢ₊₁]
-/

open Set MeasureTheory Complex

namespace PiecewiseC1Curve

/-- The sorted partition points as a list. -/
noncomputable def sortedPartition (γ : PiecewiseC1Curve) : List ℝ :=
  γ.partition.sort (· ≤ ·)

/-- Consecutive pairs of partition points: [(p₀,p₁), (p₁,p₂), ...]. -/
noncomputable def consecutivePairs (γ : PiecewiseC1Curve) : List (ℝ × ℝ) :=
  let pts := γ.sortedPartition
  pts.zip pts.tail

/-- Membership in `sortedPartition` is equivalent to membership in the original partition. -/
@[simp]
theorem mem_sortedPartition (γ : PiecewiseC1Curve) (x : ℝ) :
    x ∈ γ.sortedPartition ↔ x ∈ γ.partition :=
  Finset.mem_sort (· ≤ ·)

/-- The `sortedPartition` is sorted with respect to `≤`. -/
theorem sortedPartition_sorted (γ : PiecewiseC1Curve) :
    γ.sortedPartition.Pairwise (· ≤ ·) :=
  Finset.pairwise_sort γ.partition (· ≤ ·)

/-- The `sortedPartition` is nonempty (contains at least `a` and `b`). -/
theorem sortedPartition_nonempty (γ : PiecewiseC1Curve) :
    γ.sortedPartition ≠ [] := fun h => by
  simpa [h] using (mem_sortedPartition γ γ.a).mpr γ.endpoints_in_partition.1

/-- Every element of the `sortedPartition` lies in `[a, b]`. -/
theorem sortedPartition_mem_Icc (γ : PiecewiseC1Curve) (x : ℝ)
    (hx : x ∈ γ.sortedPartition) : x ∈ Icc γ.a γ.b :=
  γ.partition_subset ((mem_sortedPartition γ x).mp hx)

/-- The first element of the sorted partition equals `γ.a`. -/
theorem sortedPartition_head (γ : PiecewiseC1Curve) :
    γ.sortedPartition.head (sortedPartition_nonempty γ) = γ.a := by
  set hne := sortedPartition_nonempty γ
  refine le_antisymm ?_ (sortedPartition_mem_Icc γ _ (List.head_mem hne)).1
  exact (sortedPartition_sorted γ).rel_head
    ((mem_sortedPartition γ γ.a).mpr γ.endpoints_in_partition.1)

/-- The last element of the sorted partition equals `γ.b`. -/
theorem sortedPartition_last (γ : PiecewiseC1Curve) :
    γ.sortedPartition.getLast (sortedPartition_nonempty γ) = γ.b := by
  set hne := sortedPartition_nonempty γ
  refine le_antisymm (sortedPartition_mem_Icc γ _ (List.getLast_mem hne)).2 ?_
  exact (sortedPartition_sorted γ).rel_getLast
    ((mem_sortedPartition γ γ.b).mpr γ.endpoints_in_partition.2)

private theorem sorted_consecutive_union :
    ∀ (pts : List ℝ) (_hsorted : pts.Pairwise (· ≤ ·)) (hne : pts ≠ [])
      (_htail_ne : pts.tail ≠ []) (lo hi : ℝ)
      (_hhead : pts.head hne = lo) (_hlast : pts.getLast hne = hi),
    Icc lo hi ⊆ ⋃ p ∈ pts.zip pts.tail, Icc p.1 p.2 := by
  intro pts
  induction pts with
  | nil => intro _ hne _ _ _ _ _; exact absurd rfl hne
  | cons x xs ih =>
    intro hsorted _ htail_ne lo hi hhead hlast
    obtain rfl : x = lo := hhead
    cases xs with
    | nil => exact absurd rfl htail_ne
    | cons y ys =>
      simp only [List.zip_cons_cons, List.tail_cons]
      have hys_sorted := (List.pairwise_cons.mp hsorted).2
      rw [List.getLast_cons_cons] at hlast
      cases ys with
      | nil =>
        simp only [List.getLast_singleton] at hlast
        subst hlast
        intro t ht
        exact Set.mem_iUnion₂.mpr ⟨(x, y), List.mem_singleton.mpr rfl, ht⟩
      | cons z zs =>
        intro t ht
        simp only [List.mem_cons, Set.mem_iUnion]
        by_cases htxy : t ≤ y
        · exact ⟨(x, y), Or.inl rfl, ht.1, htxy⟩
        · push Not at htxy
          obtain ⟨p, hp_mem, hp_t⟩ := Set.mem_iUnion₂.mp <|
            ih hys_sorted (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
              y hi rfl hlast ⟨htxy.le, ht.2⟩
          exact ⟨p, Or.inr hp_mem, hp_t⟩

/-- The sorted partition has at least two elements (since `a ≠ b` are both in the partition). -/
theorem sortedPartition_tail_nonempty (γ : PiecewiseC1Curve) :
    γ.sortedPartition.tail ≠ [] := by
  have hcard : 1 < γ.partition.card := Finset.one_lt_card.mpr
    ⟨γ.a, γ.endpoints_in_partition.1, γ.b, γ.endpoints_in_partition.2, ne_of_lt γ.hab⟩
  have hlen : 2 ≤ γ.sortedPartition.length := by
    simp only [sortedPartition, Finset.length_sort]; omega
  intro h
  have hlen' := congr_arg List.length h
  simp [List.length_tail] at hlen'
  omega

/-- The union of `Icc p.1 p.2` over all `p ∈ consecutivePairs γ` covers `[a, b]`. -/
theorem consecutivePairs_cover (γ : PiecewiseC1Curve) :
    Icc γ.a γ.b ⊆ ⋃ p ∈ γ.consecutivePairs, Icc p.1 p.2 :=
  sorted_consecutive_union γ.sortedPartition
    (sortedPartition_sorted γ) (sortedPartition_nonempty γ)
    (sortedPartition_tail_nonempty γ)
    γ.a γ.b (sortedPartition_head γ) (sortedPartition_last γ)

end PiecewiseC1Curve
