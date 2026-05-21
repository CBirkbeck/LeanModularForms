/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.Analysis.Complex.Basic

/-!
# Curve Utilities and Avoidance

Utility lemmas for working with `PiecewiseC1Path` partition structure and curve avoidance.

## Main definitions

* `PiecewiseC1Path.Avoids` -- a piecewise C^1 path avoids a point z_0
* `PiecewiseC1Path.infDist` -- infimum distance from z_0 to the path image on [0,1]
* `PiecewiseC1Path.fullPartition` -- sorted partition including endpoints 0 and 1

## Main results

* `PiecewiseC1Path.image_compact` -- the image of [0,1] under gamma is compact
* `PiecewiseC1Path.infDist_pos_of_avoids` -- positive inf distance when path avoids z_0
* `PiecewiseC1Path.avoids_of_im_lt` -- imaginary part criterion for avoidance
* `PiecewiseC1Path.avoids_of_re_ne` -- real part criterion for avoidance
* `PiecewiseC1Path.avoids_of_norm_ne` -- norm criterion for avoidance
* `PiecewiseC1Path.fullPartition_sorted` -- the full partition is sorted
* `PiecewiseC1Path.fullPartition_head_eq_zero` -- first element is 0
* `PiecewiseC1Path.fullPartition_last_eq_one` -- last element is 1
-/

open Set Complex Metric

noncomputable section

variable {x y : ℂ}

namespace PiecewiseC1Path

/-! ### Avoidance -/

/-- A piecewise C^1 path avoids a point `z_0`. -/
def Avoids (γ : PiecewiseC1Path x y) (z₀ : ℂ) : Prop :=
  ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z₀

/-- Infimum distance from `z_0` to the path image on `[0, 1]`. -/
noncomputable def infDist (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℝ :=
  Metric.infDist z₀ (γ.toPath.extend '' Icc 0 1)

/-! ### Compactness of the image -/

/-- The image of `[0, 1]` under a piecewise C^1 path is compact. -/
theorem image_compact (γ : PiecewiseC1Path x y) :
    IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1) :=
  isCompact_Icc.image γ.toPath.continuous_extend

/-! ### Positive inf-distance -/

/-- If a piecewise C^1 path avoids `z_0`, then the infimum distance from `z_0` to the
path image is positive. -/
theorem infDist_pos_of_avoids (γ : PiecewiseC1Path x y) (z₀ : ℂ)
    (hav : γ.Avoids z₀) : 0 < γ.infDist z₀ := by
  rw [infDist, ← γ.image_compact.isClosed.notMem_iff_infDist_pos
    ⟨γ.toPath.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩]
  rintro ⟨t, ht, heq⟩
  exact hav t ht heq

/-! ### Avoidance criteria -/

/-- If every point on the path has imaginary part strictly greater than `z_0.im`,
then the path avoids `z_0`. -/
theorem avoids_of_im_lt (γ : PiecewiseC1Path x y) (z₀ : ℂ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, z₀.im < (γ t).im) : γ.Avoids z₀ :=
  fun t ht heq => (h t ht).ne' (by rw [heq])

/-- If every point on the path has real part different from `z_0.re`,
then the path avoids `z_0`. -/
theorem avoids_of_re_ne (γ : PiecewiseC1Path x y) (z₀ : ℂ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, (γ t).re ≠ z₀.re) : γ.Avoids z₀ :=
  fun t ht heq => h t ht (by rw [heq])

/-- If every point on the path has norm different from `‖z_0‖`,
then the path avoids `z_0`. Useful for curves on circles. -/
theorem avoids_of_norm_ne (γ : PiecewiseC1Path x y) (z₀ : ℂ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≠ ‖z₀‖) : γ.Avoids z₀ :=
  fun t ht heq => h t ht (by rw [heq])

/-! ### Full partition -/

/-- The underlying finset for the full partition: `{0, 1} ∪ partition`. -/
private def fullPartitionFinset (γ : PiecewiseC1Path x y) : Finset ℝ :=
  ({0, 1} : Finset ℝ) ∪ γ.partition

/-- The full sorted partition including endpoints 0 and 1. The partition of a
`PiecewiseC1Path` contains breakpoints in `(0, 1)`; the full partition adds the
endpoints `{0, 1}`. -/
noncomputable def fullPartition (γ : PiecewiseC1Path x y) : List ℝ :=
  γ.fullPartitionFinset.sort (· ≤ ·)

private theorem zero_mem_fullPartitionFinset (γ : PiecewiseC1Path x y) :
    (0 : ℝ) ∈ γ.fullPartitionFinset := by
  simp [fullPartitionFinset]

private theorem one_mem_fullPartitionFinset (γ : PiecewiseC1Path x y) :
    (1 : ℝ) ∈ γ.fullPartitionFinset := by
  simp [fullPartitionFinset]

private theorem fullPartitionFinset_nonempty (γ : PiecewiseC1Path x y) :
    γ.fullPartitionFinset.Nonempty :=
  ⟨0, γ.zero_mem_fullPartitionFinset⟩

/-- The full partition list is nonempty. -/
theorem fullPartition_ne_nil (γ : PiecewiseC1Path x y) :
    γ.fullPartition ≠ [] :=
  List.ne_nil_of_mem ((Finset.mem_sort _).mpr γ.zero_mem_fullPartitionFinset)

/-- The full partition is sorted with respect to `≤`. -/
theorem fullPartition_sorted (γ : PiecewiseC1Path x y) :
    γ.fullPartition.Pairwise (· ≤ ·) :=
  Finset.pairwise_sort _ (· ≤ ·)

/-- Membership in `fullPartition` is equivalent to being `0`, `1`, or a partition point. -/
theorem mem_fullPartition (γ : PiecewiseC1Path x y) (t : ℝ) :
    t ∈ γ.fullPartition ↔ t = 0 ∨ t = 1 ∨ t ∈ γ.partition := by
  change t ∈ γ.fullPartitionFinset.sort (· ≤ ·) ↔ _
  rw [Finset.mem_sort]
  simp [fullPartitionFinset]

/-- `0` is in the full partition. -/
theorem zero_mem_fullPartition (γ : PiecewiseC1Path x y) :
    (0 : ℝ) ∈ γ.fullPartition := by
  simp [mem_fullPartition]

/-- `1` is in the full partition. -/
theorem one_mem_fullPartition (γ : PiecewiseC1Path x y) :
    (1 : ℝ) ∈ γ.fullPartition := by
  simp [mem_fullPartition]

/-- Every element of the full partition lies in `[0, 1]`. -/
theorem fullPartition_mem_Icc (γ : PiecewiseC1Path x y) (t : ℝ)
    (ht : t ∈ γ.fullPartition) : t ∈ Icc (0 : ℝ) 1 := by
  rw [mem_fullPartition] at ht
  rcases ht with rfl | rfl | hpart
  · exact ⟨le_refl _, zero_le_one⟩
  · exact ⟨zero_le_one, le_refl _⟩
  · exact ⟨(γ.partition_subset hpart).1.le, (γ.partition_subset hpart).2.le⟩

/-- The first element of the full partition is `0`. -/
theorem fullPartition_head_eq_zero (γ : PiecewiseC1Path x y) :
    γ.fullPartition.head γ.fullPartition_ne_nil = 0 := by
  have h_mem := List.head_mem γ.fullPartition_ne_nil
  have h_le := γ.fullPartition_sorted.rel_head γ.zero_mem_fullPartition
  linarith [(γ.fullPartition_mem_Icc _ h_mem).1]

/-- The last element of the full partition is `1`. -/
theorem fullPartition_last_eq_one (γ : PiecewiseC1Path x y) :
    γ.fullPartition.getLast γ.fullPartition_ne_nil = 1 := by
  have h_mem := List.getLast_mem γ.fullPartition_ne_nil
  have h_ge := γ.fullPartition_sorted.rel_getLast γ.one_mem_fullPartition
  linarith [(γ.fullPartition_mem_Icc _ h_mem).2]

/-- The full partition has at least two elements (it contains both 0 and 1). -/
theorem fullPartition_length_ge_two (γ : PiecewiseC1Path x y) :
    2 ≤ γ.fullPartition.length := by
  simp only [fullPartition, Finset.length_sort]
  exact Finset.one_lt_card.mpr
    ⟨0, γ.zero_mem_fullPartitionFinset, 1, γ.one_mem_fullPartitionFinset, zero_ne_one⟩

/-- The full partition has no duplicate elements. -/
theorem fullPartition_nodup (γ : PiecewiseC1Path x y) :
    γ.fullPartition.Nodup :=
  Finset.sort_nodup _ _

end PiecewiseC1Path

end
