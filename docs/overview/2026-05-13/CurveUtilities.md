# CurveUtilities.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/CurveUtilities.lean`

---

### def `PiecewiseC1Path.Avoids`
- Type: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) : Prop`
- What: Proposition stating `γ` avoids the point `z₀` on `[0,1]`.
- How: `∀ t ∈ Icc 0 1, γ t ≠ z₀`.
- Hypotheses: none (definition).
- Uses-from-project: `PiecewiseC1Path`.
- Used by: every theorem in this file.
- Visibility: public.
- Lines: 42-43.

### def `PiecewiseC1Path.infDist`
- Type: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℝ`
- What: Infimum distance from `z₀` to the path image on `[0,1]`.
- How: `Metric.infDist z₀ (γ.toPath.extend '' Icc 0 1)`.
- Hypotheses: none.
- Uses-from-project: `PiecewiseC1Path`, `Path.extend`.
- Used by: `infDist_pos_of_avoids`.
- Visibility: public, `noncomputable`.
- Lines: 46-47.

### theorem `PiecewiseC1Path.image_compact`
- Type: `(γ : PiecewiseC1Path x y) → IsCompact (γ.toPath.extend '' Icc (0 : ℝ) 1)`
- What: The image of `[0,1]` under a piecewise C¹ path is compact.
- How: `isCompact_Icc.image γ.toPath.continuous_extend`.
- Hypotheses: none.
- Uses-from-project: `PiecewiseC1Path`, `Path.continuous_extend`.
- Used by: `infDist_pos_of_avoids`.
- Visibility: public.
- Lines: 52-54.

### theorem `PiecewiseC1Path.infDist_pos_of_avoids`
- Type: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) (hav : γ.Avoids z₀) → 0 < γ.infDist z₀`
- What: Positive infimum distance when the path avoids `z₀`.
- How: Rewrites using `IsClosed.notMem_iff_infDist_pos` of the compact (hence closed) image with witness `γ.toPath.extend 0`; uses `mem_image_of_mem` and `left_mem_Icc.mpr zero_le_one`; closes via the assumption that `γ` does not equal `z₀` anywhere.
- Hypotheses: `γ.Avoids z₀`.
- Uses-from-project: `Avoids`, `infDist`, `image_compact`.
- Used by: external callers (homotopy/avoidance).
- Visibility: public.
- Lines: 60-65.

### theorem `PiecewiseC1Path.avoids_of_im_lt`
- Type: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) (h : ∀ t ∈ Icc 0 1, z₀.im < (γ t).im) → γ.Avoids z₀`
- What: Strict imaginary part inequality on `[0,1]` implies avoidance.
- How: `fun t ht heq => (h t ht).ne' (by rw [heq])`.
- Hypotheses: pointwise strict inequality on imaginary parts.
- Uses-from-project: `Avoids`.
- Used by: avoidance constructors.
- Visibility: public.
- Lines: 71-73.

### theorem `PiecewiseC1Path.avoids_of_re_ne`
- Type: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) (h : ∀ t ∈ Icc 0 1, (γ t).re ≠ z₀.re) → γ.Avoids z₀`
- What: Real parts pairwise distinct from `z₀.re` imply avoidance.
- How: `fun t ht heq => h t ht (by rw [heq])`.
- Hypotheses: pointwise real-part inequality.
- Uses-from-project: `Avoids`.
- Used by: avoidance constructors.
- Visibility: public.
- Lines: 77-79.

### theorem `PiecewiseC1Path.avoids_of_norm_ne`
- Type: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) (h : ∀ t ∈ Icc 0 1, ‖γ t‖ ≠ ‖z₀‖) → γ.Avoids z₀`
- What: Norm inequality criterion for avoidance (useful for circular curves).
- How: `fun t ht heq => h t ht (by rw [heq])`.
- Hypotheses: pointwise norm inequality.
- Uses-from-project: `Avoids`.
- Used by: circle-based avoidance.
- Visibility: public.
- Lines: 83-85.

### private def `PiecewiseC1Path.fullPartitionFinset`
- Type: `(γ : PiecewiseC1Path x y) : Finset ℝ`
- What: Underlying finset for the full partition: `{0,1} ∪ γ.partition`.
- How: Definition.
- Hypotheses: none.
- Uses-from-project: `PiecewiseC1Path.partition`.
- Used by: `fullPartition`, `*_mem_fullPartitionFinset`, `fullPartition_length_ge_two`.
- Visibility: private.
- Lines: 90-91.

### def `PiecewiseC1Path.fullPartition`
- Type: `(γ : PiecewiseC1Path x y) : List ℝ`
- What: Sorted partition list including endpoints `0` and `1`.
- How: `γ.fullPartitionFinset.sort (· ≤ ·)`.
- Hypotheses: none.
- Uses-from-project: `fullPartitionFinset`.
- Used by: `fullPartition_*` theorems.
- Visibility: public, `noncomputable`.
- Lines: 96-97.

### private theorem `PiecewiseC1Path.zero_mem_fullPartitionFinset`
- Type: `(0 : ℝ) ∈ γ.fullPartitionFinset`
- What: `0` belongs to the underlying finset.
- How: `simp [fullPartitionFinset]`.
- Hypotheses: none.
- Uses-from-project: `fullPartitionFinset`.
- Used by: `fullPartitionFinset_nonempty`, `fullPartition_ne_nil`, `fullPartition_head_eq_zero`, `fullPartition_length_ge_two`.
- Visibility: private.
- Lines: 99-101.

### private theorem `PiecewiseC1Path.one_mem_fullPartitionFinset`
- Type: `(1 : ℝ) ∈ γ.fullPartitionFinset`
- What: `1` belongs to the underlying finset.
- How: `simp [fullPartitionFinset]`.
- Hypotheses: none.
- Uses-from-project: `fullPartitionFinset`.
- Used by: `fullPartition_last_eq_one`, `fullPartition_length_ge_two`.
- Visibility: private.
- Lines: 103-105.

### private theorem `PiecewiseC1Path.fullPartitionFinset_nonempty`
- Type: `γ.fullPartitionFinset.Nonempty`
- What: The underlying finset is nonempty.
- How: `⟨0, γ.zero_mem_fullPartitionFinset⟩`.
- Hypotheses: none.
- Uses-from-project: `zero_mem_fullPartitionFinset`.
- Used by: not used directly in this file.
- Visibility: private.
- Lines: 107-109.

### theorem `PiecewiseC1Path.fullPartition_ne_nil`
- Type: `γ.fullPartition ≠ []`
- What: The full partition list is nonempty.
- How: Membership of `0` transported via `Finset.mem_sort` and a contradiction with `List.not_mem_nil`.
- Hypotheses: none.
- Uses-from-project: `zero_mem_fullPartitionFinset`, `fullPartition`.
- Used by: `fullPartition_head_eq_zero`, `fullPartition_last_eq_one`.
- Visibility: public.
- Lines: 112-119.

### theorem `PiecewiseC1Path.fullPartition_sorted`
- Type: `γ.fullPartition.Pairwise (· ≤ ·)`
- What: The full partition list is sorted.
- How: `Finset.pairwise_sort _ (· ≤ ·)`.
- Hypotheses: none.
- Uses-from-project: `fullPartition`.
- Used by: `fullPartition_head_eq_zero`, `fullPartition_last_eq_one`.
- Visibility: public.
- Lines: 122-124.

### theorem `PiecewiseC1Path.mem_fullPartition`
- Type: `(t : ℝ) → t ∈ γ.fullPartition ↔ t = 0 ∨ t = 1 ∨ t ∈ γ.partition`
- What: Membership characterisation.
- How: `change`; `Finset.mem_sort`; `simp [fullPartitionFinset]`.
- Hypotheses: none.
- Uses-from-project: `fullPartition`, `fullPartitionFinset`, `PiecewiseC1Path.partition`.
- Used by: `zero_mem_fullPartition`, `one_mem_fullPartition`, `fullPartition_mem_Icc`.
- Visibility: public.
- Lines: 127-131.

### theorem `PiecewiseC1Path.zero_mem_fullPartition`
- Type: `(0 : ℝ) ∈ γ.fullPartition`
- What: `0` is in the full partition.
- How: `rw [mem_fullPartition]; left; rfl`.
- Hypotheses: none.
- Uses-from-project: `mem_fullPartition`.
- Used by: `fullPartition_head_eq_zero`.
- Visibility: public.
- Lines: 134-138.

### theorem `PiecewiseC1Path.one_mem_fullPartition`
- Type: `(1 : ℝ) ∈ γ.fullPartition`
- What: `1` is in the full partition.
- How: `rw [mem_fullPartition]; right; left; rfl`.
- Hypotheses: none.
- Uses-from-project: `mem_fullPartition`.
- Used by: `fullPartition_last_eq_one`.
- Visibility: public.
- Lines: 141-146.

### theorem `PiecewiseC1Path.fullPartition_mem_Icc`
- Type: `(t : ℝ) (ht : t ∈ γ.fullPartition) → t ∈ Icc (0 : ℝ) 1`
- What: Every full-partition point lies in `[0,1]`.
- How: `rw [mem_fullPartition] at ht; rcases ht with rfl | rfl | hpart`; on partition branch uses `(γ.partition_subset hpart).1.le` and `.2.le`.
- Hypotheses: none.
- Uses-from-project: `mem_fullPartition`, `PiecewiseC1Path.partition_subset`.
- Used by: `fullPartition_head_eq_zero`, `fullPartition_last_eq_one`.
- Visibility: public.
- Lines: 149-155.

### theorem `PiecewiseC1Path.fullPartition_head_eq_zero`
- Type: `γ.fullPartition.head γ.fullPartition_ne_nil = 0`
- What: First element of `fullPartition` is `0`.
- How: `List.head_mem`; `Sorted.rel_head` against `0`; `linarith` from `fullPartition_mem_Icc`.
- Hypotheses: none.
- Uses-from-project: `fullPartition_ne_nil`, `fullPartition_sorted`, `zero_mem_fullPartition`, `fullPartition_mem_Icc`.
- Used by: external (FD boundary callers).
- Visibility: public.
- Lines: 158-162.

### theorem `PiecewiseC1Path.fullPartition_last_eq_one`
- Type: `γ.fullPartition.getLast γ.fullPartition_ne_nil = 1`
- What: Last element of `fullPartition` is `1`.
- How: `List.getLast_mem`; `Sorted.rel_getLast` against `1`; `linarith` from `fullPartition_mem_Icc`.
- Hypotheses: none.
- Uses-from-project: `fullPartition_ne_nil`, `fullPartition_sorted`, `one_mem_fullPartition`, `fullPartition_mem_Icc`.
- Used by: external (FD boundary callers).
- Visibility: public.
- Lines: 165-169.

### theorem `PiecewiseC1Path.fullPartition_length_ge_two`
- Type: `2 ≤ γ.fullPartition.length`
- What: The full partition list has at least two elements.
- How: `simp [fullPartition, Finset.length_sort]`; `Finset.one_lt_card.mpr ⟨0, zero_mem_fullPartitionFinset, 1, one_mem_fullPartitionFinset, zero_ne_one⟩`.
- Hypotheses: none.
- Uses-from-project: `fullPartition`, `zero_mem_fullPartitionFinset`, `one_mem_fullPartitionFinset`.
- Used by: external.
- Visibility: public.
- Lines: 172-176.

### theorem `PiecewiseC1Path.fullPartition_nodup`
- Type: `γ.fullPartition.Nodup`
- What: Full partition list has no duplicates.
- How: `Finset.sort_nodup _ _`.
- Hypotheses: none.
- Uses-from-project: `fullPartition`.
- Used by: external (relies on uniqueness).
- Visibility: public.
- Lines: 179-181.

---

## File Summary
- Total declarations: 21 (2 definitions, 1 noncomputable derived definition, 1 private finset def, 17 theorems including 4 private helpers).
- Key API: `Avoids` predicate + three avoidance constructors (`im`, `re`, `norm` criteria); `infDist_pos_of_avoids`; sorted `fullPartition` with head/last/length/nodup theorems.
- Unused declarations within file: `fullPartitionFinset_nonempty` (private, currently not called) — others are used downstream.
- Sorries: none.
- `set_option`: none.
- Long proofs (>10 lines): none — all proofs are ≤7 lines.
- Purpose: Utility lemmas for `PiecewiseC1Path` paths: an avoidance predicate with criteria from imaginary/real/norm comparisons, a positive infimum-distance theorem against a point, and a fully-extended sorted partition list (with endpoints `0` and `1`) characterised by head/last/length/nodup theorems. Provides the basic glue for higher-level CPV/homotopy theorems that work with the path's piecewise structure.
