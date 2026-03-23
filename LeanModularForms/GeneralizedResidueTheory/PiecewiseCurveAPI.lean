/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
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

/-! ### Definitions -/

/-- The sorted partition points as a list. -/
noncomputable def sortedPartition (γ : PiecewiseC1Curve) : List ℝ :=
  γ.partition.sort (· ≤ ·)

/-- Consecutive pairs of partition points: [(p₀,p₁), (p₁,p₂), ...]. -/
noncomputable def consecutivePairs (γ : PiecewiseC1Curve) : List (ℝ × ℝ) :=
  let pts := γ.sortedPartition
  pts.zip pts.tail

/-! ### Basic properties of `sortedPartition` -/

/-- Membership in `sortedPartition` is equivalent to membership in the original partition. -/
@[simp]
theorem mem_sortedPartition (γ : PiecewiseC1Curve) (x : ℝ) :
    x ∈ γ.sortedPartition ↔ x ∈ γ.partition :=
  Finset.mem_sort (· ≤ ·)

/-- The `sortedPartition` is sorted with respect to `≤`. -/
theorem sortedPartition_sorted (γ : PiecewiseC1Curve) :
    γ.sortedPartition.Sorted (· ≤ ·) :=
  Finset.sort_sorted (· ≤ ·) γ.partition

/-- The `sortedPartition` has no duplicates. -/
theorem sortedPartition_nodup (γ : PiecewiseC1Curve) :
    γ.sortedPartition.Nodup :=
  Finset.sort_nodup (· ≤ ·) γ.partition

/-- The `sortedPartition` is nonempty (contains at least `a` and `b`). -/
theorem sortedPartition_nonempty (γ : PiecewiseC1Curve) :
    γ.sortedPartition ≠ [] := by
  intro h
  have ha := γ.endpoints_in_partition.1
  rw [← mem_sortedPartition] at ha
  simp [h] at ha

/-- Every element of the `sortedPartition` lies in `[a, b]`. -/
theorem sortedPartition_mem_Icc (γ : PiecewiseC1Curve) (x : ℝ)
    (hx : x ∈ γ.sortedPartition) : x ∈ Icc γ.a γ.b :=
  γ.partition_subset ((mem_sortedPartition γ x).mp hx)

/-- The partition is nonempty. -/
private theorem partition_nonempty (γ : PiecewiseC1Curve) : γ.partition.Nonempty :=
  ⟨γ.a, γ.endpoints_in_partition.1⟩

/-! ### Head and last of `sortedPartition` -/

/-- The first element of the sorted partition equals `γ.a`.

  Proof sketch: `head ∈ [a,b]` so `a ≤ head`; all elements ≥ head from sorted, and
  `a ∈ sortedPartition`, so `head ≤ a`. Together: `head = a`. -/
theorem sortedPartition_head (γ : PiecewiseC1Curve) :
    γ.sortedPartition.head (sortedPartition_nonempty γ) = γ.a := by
  have hne := sortedPartition_nonempty γ
  have h_head_mem : γ.sortedPartition.head hne ∈ γ.sortedPartition :=
    List.head_mem hne
  have h_head_Icc := sortedPartition_mem_Icc γ _ h_head_mem
  -- a ≤ head from head ∈ [a,b]
  have ha_le : γ.a ≤ γ.sortedPartition.head hne := h_head_Icc.1
  -- head ≤ a: use that list is sorted and a ∈ list
  -- head of a sorted list is ≤ all other elements
  have h_a_mem : γ.a ∈ γ.sortedPartition := (mem_sortedPartition γ γ.a).mpr
    γ.endpoints_in_partition.1
  have hsorted := sortedPartition_sorted γ
  -- Either a = head or a ∈ tail; in either case head ≤ a from sorted
  obtain (rfl | h_a_tail) : γ.sortedPartition.head hne = γ.a ∨
      γ.a ∈ γ.sortedPartition.tail := by
    cases γ.sortedPartition with
    | nil => exact absurd rfl hne
    | cons h t =>
      simp only [List.head_cons, List.tail_cons]
      rcases List.mem_cons.mp h_a_mem with rfl | ht
      · exact Or.inl rfl
      · exact Or.inr ht
  · rfl
  · have h_head_le : γ.sortedPartition.head hne ≤ γ.a := by
      cases γ.sortedPartition with
      | nil => exact absurd rfl hne
      | cons h t =>
        simp only [List.head_cons, List.tail_cons] at *
        exact List.rel_of_sorted_cons hsorted γ.a h_a_tail
    linarith

/-- The last element of the sorted partition equals `γ.b`.

  Proof sketch: `getLast ∈ [a,b]` so `getLast ≤ b`; all elements ≤ getLast from sorted,
  and `b ∈ sortedPartition`, so `b ≤ getLast`. Together: `getLast = b`. -/
theorem sortedPartition_last (γ : PiecewiseC1Curve) :
    γ.sortedPartition.getLast (sortedPartition_nonempty γ) = γ.b := by
  have hne := sortedPartition_nonempty γ
  have h_last_mem : γ.sortedPartition.getLast hne ∈ γ.sortedPartition :=
    List.getLast_mem hne
  have h_last_Icc := sortedPartition_mem_Icc γ _ h_last_mem
  -- getLast ≤ b from getLast ∈ [a,b]
  have h_le_b : γ.sortedPartition.getLast hne ≤ γ.b := h_last_Icc.2
  -- b ≤ getLast: use that list is sorted and b ∈ list
  -- For a sorted list, all elements ≤ getLast.
  -- We prove this by showing getLast is an upper bound.
  have h_b_mem : γ.b ∈ γ.sortedPartition := (mem_sortedPartition γ γ.b).mpr
    γ.endpoints_in_partition.2
  have hsorted := sortedPartition_sorted γ
  -- Use Sorted.rel_of_mem_take_of_mem_drop or direct induction
  -- b ≤ getLast because in sorted list, elements increase, and getLast is last
  have h_b_le : γ.b ≤ γ.sortedPartition.getLast hne := by
    -- Induction: prove ∀ x ∈ l, x ≤ getLast l for sorted l
    suffices ∀ (l : List ℝ), l.Sorted (· ≤ ·) → l ≠ [] →
        ∀ x ∈ l, x ≤ l.getLast (by assumption) by
      exact this _ hsorted hne _ h_b_mem
    intro l hl hne' x hx
    induction l with
    | nil => exact absurd rfl hne'
    | cons a as ih =>
      cases as with
      | nil =>
        simp only [List.getLast_singleton]
        exact List.eq_of_mem_singleton hx ▸ le_refl _
      | cons b bs =>
        simp only [List.getLast_cons (List.cons_ne_nil b bs)]
        rcases List.mem_cons.mp hx with rfl | hx'
        · -- x = a, need a ≤ getLast (b :: bs)
          have h_a_le_b : a ≤ b := (List.sorted_cons.mp hl).1 b (List.mem_cons_self b bs)
          have h_b_le_last : b ≤ (b :: bs).getLast (List.cons_ne_nil b bs) :=
            ih ((List.sorted_cons.mp hl).2) (List.cons_ne_nil b bs) b
              (List.mem_cons_self b bs)
          linarith
        · exact ih ((List.sorted_cons.mp hl).2) (List.cons_ne_nil b bs) x hx'
  linarith

/-! ### Consecutive pairs cover `[a, b]` -/

/-- A sorted list whose head is `lo` and last is `hi` has consecutive Icc's covering `[lo, hi]`. -/
private theorem sorted_consecutive_union (pts : List ℝ)
    (hsorted : pts.Sorted (· ≤ ·))
    (hne : pts ≠ [])
    (lo hi : ℝ)
    (hhead : pts.head hne = lo)
    (hlast : pts.getLast hne = hi) :
    Icc lo hi ⊆ ⋃ p ∈ pts.zip pts.tail, Icc p.1 p.2 := by
  induction pts with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    simp only [List.head_cons] at hhead
    subst hhead
    cases xs with
    | nil =>
      simp only [List.getLast_singleton] at hlast
      subst hlast
      simp [List.zip_nil_right]
    | cons y ys =>
      simp only [List.zip_cons_cons, List.tail_cons]
      simp only [List.getLast_cons_cons] at hlast
      have hlo_le_y : lo ≤ y :=
        (List.sorted_cons.mp hsorted).1 y (List.mem_cons_self y ys)
      have hys_sorted : (y :: ys).Sorted (· ≤ ·) :=
        (List.sorted_cons.mp hsorted).2
      have hys_ne : y :: ys ≠ [] := List.cons_ne_nil y ys
      have ih_ys := ih hys_sorted hys_ne y hi (List.head_cons y ys) hlast
      intro t ht
      simp only [List.mem_cons, Set.mem_iUnion]
      by_cases htxy : t ≤ y
      · exact ⟨(lo, y), Or.inl rfl, ht.1, htxy⟩
      · push_neg at htxy
        have ht_sub : t ∈ Icc y hi := ⟨le_of_lt htxy, ht.2⟩
        obtain ⟨p, hp_mem, hp_t⟩ := Set.mem_iUnion₂.mp (ih_ys ht_sub)
        exact ⟨p, Or.inr hp_mem, hp_t⟩

/-- The union of `Icc p.1 p.2` over all `p ∈ consecutivePairs γ` covers `[a, b]`. -/
theorem consecutivePairs_cover (γ : PiecewiseC1Curve) :
    Icc γ.a γ.b ⊆ ⋃ p ∈ γ.consecutivePairs, Icc p.1 p.2 :=
  sorted_consecutive_union γ.sortedPartition
    (sortedPartition_sorted γ) (sortedPartition_nonempty γ)
    γ.a γ.b (sortedPartition_head γ) (sortedPartition_last γ)

/-! ### Properties of consecutive pairs -/

/-- For any sorted list, consecutive pairs in `l.zip l.tail` satisfy `p.1 ≤ p.2`. -/
private theorem sorted_zip_tail_le {l : List ℝ} (hl : l.Sorted (· ≤ ·))
    {p : ℝ × ℝ} (hp : p ∈ l.zip l.tail) : p.1 ≤ p.2 := by
  induction l with
  | nil => simp at hp
  | cons x xs ih =>
    cases xs with
    | nil => simp at hp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.tail_cons, List.mem_cons] at hp
      cases hp with
      | inl h =>
        rw [← h]
        exact (List.sorted_cons.mp hl).1 y (List.mem_cons_self y ys)
      | inr h =>
        exact ih ((List.sorted_cons.mp hl).2) h

/-- For each consecutive pair `(p, q)`, we have `p ≤ q`. -/
theorem consecutivePairs_le (γ : PiecewiseC1Curve) (p : ℝ × ℝ)
    (hp : p ∈ γ.consecutivePairs) : p.1 ≤ p.2 :=
  sorted_zip_tail_le (sortedPartition_sorted γ) hp

/-- Both components of a consecutive pair lie in `[a, b]`. -/
theorem consecutivePairs_subset (γ : PiecewiseC1Curve) (p : ℝ × ℝ)
    (hp : p ∈ γ.consecutivePairs) :
    p.1 ∈ Icc γ.a γ.b ∧ p.2 ∈ Icc γ.a γ.b := by
  simp only [consecutivePairs] at hp
  have h12 := List.of_mem_zip hp
  exact ⟨sortedPartition_mem_Icc γ _ h12.1,
         sortedPartition_mem_Icc γ _ (List.mem_of_mem_tail h12.2)⟩

/-! ### Main theorems -/

/-- **Main theorem**: to prove a property `P` on `[a, b]`, it suffices to prove `P` on each
    consecutive segment `[pᵢ, pᵢ₊₁]` of the partition. -/
theorem forall_Icc_of_forall_consecutive {P : ℝ → Prop}
    (γ : PiecewiseC1Curve)
    (h : ∀ p ∈ γ.consecutivePairs, ∀ t ∈ Icc p.1 p.2, P t) :
    ∀ t ∈ Icc γ.a γ.b, P t := fun t ht => by
  obtain ⟨p, hp_mem, hp_t⟩ := Set.mem_iUnion₂.mp (consecutivePairs_cover γ ht)
  exact h p hp_mem t hp_t

/-- **Image variant**: if the image of each consecutive segment lies in `S`,
    then the image of `[a, b]` lies in `S`. -/
theorem image_subset_of_consecutive_images {S : Set ℂ}
    (γ : PiecewiseC1Curve)
    (h : ∀ p ∈ γ.consecutivePairs, γ.toFun '' Icc p.1 p.2 ⊆ S) :
    γ.toFun '' Icc γ.a γ.b ⊆ S := fun z ⟨t, ht, hz⟩ => by
  obtain ⟨p, hp_mem, hp_t⟩ := Set.mem_iUnion₂.mp (consecutivePairs_cover γ ht)
  exact h p hp_mem ⟨t, hp_t, hz⟩

end PiecewiseC1Curve
