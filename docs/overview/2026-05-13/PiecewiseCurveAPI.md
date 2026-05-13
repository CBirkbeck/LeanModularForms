# PiecewiseCurveAPI.lean Inventory

**Path**: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/PiecewiseCurveAPI.lean`
**Namespace**: `PiecewiseC1Curve`
**Imports**: `LeanModularForms.ForMathlib.ClassicalCPV`, `Mathlib`

---

### noncomputable def `sortedPartition`
- **Type**: `PiecewiseC1Curve → List ℝ`
- **What**: Partition points returned as a `≤`-sorted list.
- **How**: `γ.partition.sort (· ≤ ·)`.
- **Hypotheses**: none.
- **Uses-from-project**: `PiecewiseC1Curve.partition` (from `ClassicalCPV`).
- **Used by**: all downstream lemmas in this file.
- **Visibility**: public, `noncomputable`
- **Lines**: 32–33
- **Notes**: Underlying datatype is a Mathlib `Finset.sort`.

### noncomputable def `consecutivePairs`
- **Type**: `PiecewiseC1Curve → List (ℝ × ℝ)`
- **What**: List of consecutive partition pairs `[(p₀,p₁), (p₁,p₂), …]`.
- **How**: `let pts := γ.sortedPartition; pts.zip pts.tail`.
- **Hypotheses**: none.
- **Uses-from-project**: `sortedPartition`.
- **Used by**: `consecutivePairs_cover`, `consecutivePairs_le`, `consecutivePairs_subset`, `forall_Icc_of_forall_consecutive`, `image_subset_of_consecutive_images`.
- **Visibility**: public, `noncomputable`
- **Lines**: 36–38
- **Notes**: Built by `List.zip` with tail (drops the last pair correctly).

### theorem `mem_sortedPartition` (`@[simp]`)
- **Type**: `x ∈ γ.sortedPartition ↔ x ∈ γ.partition`.
- **What**: Sorting preserves membership.
- **How**: `Finset.mem_sort`.
- **Hypotheses**: none.
- **Uses-from-project**: `sortedPartition`.
- **Used by**: `sortedPartition_nonempty`, `sortedPartition_head`, `sortedPartition_last`, `sortedPartition_mem_Icc`.
- **Visibility**: public, `@[simp]`
- **Lines**: 43–46
- **Notes**: 1-line proof.

### theorem `sortedPartition_sorted`
- **Type**: `γ.sortedPartition.Pairwise (· ≤ ·)`.
- **What**: The sorted-partition list is non-strictly sorted.
- **How**: `Finset.pairwise_sort`.
- **Hypotheses**: none.
- **Uses-from-project**: `sortedPartition`.
- **Used by**: `sortedPartition_head`, `sortedPartition_last`, `consecutivePairs_cover`, `consecutivePairs_le`.
- **Visibility**: public
- **Lines**: 49–51
- **Notes**: 1-line proof.

### theorem `sortedPartition_nodup`
- **Type**: `γ.sortedPartition.Nodup`.
- **What**: No duplicates in the sorted partition list.
- **How**: `Finset.sort_nodup _ _`.
- **Hypotheses**: none.
- **Uses-from-project**: `sortedPartition`.
- **Used by**: not used elsewhere in this file (auxiliary fact).
- **Visibility**: public
- **Lines**: 54–56
- **Notes**: 1-line proof.

### theorem `sortedPartition_nonempty`
- **Type**: `γ.sortedPartition ≠ []`.
- **What**: Sorted partition contains at least `γ.a` and `γ.b`, so it is nonempty.
- **How**: Contradiction: from `γ.endpoints_in_partition.1`, `γ.a ∈ sortedPartition`; rewriting via `mem_sortedPartition` and `simp [h]` produces a false membership claim.
- **Hypotheses**: none (uses `endpoints_in_partition` field).
- **Uses-from-project**: `mem_sortedPartition`, `endpoints_in_partition`.
- **Used by**: `sortedPartition_head`, `sortedPartition_last`, `consecutivePairs_cover`, `sortedPartition_tail_nonempty`.
- **Visibility**: public
- **Lines**: 59–64
- **Notes**: 3-line proof.

### theorem `sortedPartition_mem_Icc`
- **Type**: `x ∈ γ.sortedPartition → x ∈ Icc γ.a γ.b`.
- **What**: Every sorted-partition point lies in `[a, b]`.
- **How**: `γ.partition_subset ((mem_sortedPartition γ x).mp hx)`.
- **Hypotheses**: membership in the sorted partition.
- **Uses-from-project**: `mem_sortedPartition`, `partition_subset`.
- **Used by**: `sortedPartition_head`, `sortedPartition_last`, `consecutivePairs_subset`.
- **Visibility**: public
- **Lines**: 67–69
- **Notes**: 1-line proof.

### theorem `sortedPartition_head`
- **Type**: `γ.sortedPartition.head sortedPartition_nonempty = γ.a`.
- **What**: The first element of the sorted partition is `γ.a`.
- **How**: Antisymmetry: `ha_le : γ.a ≤ head` from `sortedPartition_mem_Icc` on `List.head_mem`; `h_head_le : head ≤ γ.a` from `(sortedPartition_sorted γ).rel_head h_a_mem`; finish with `le_antisymm` (8-line proof; main lemmas `sortedPartition_sorted.rel_head` and `sortedPartition_mem_Icc`).
- **Hypotheses**: none (uses field `endpoints_in_partition`).
- **Uses-from-project**: `sortedPartition_nonempty`, `sortedPartition_sorted`, `sortedPartition_mem_Icc`, `mem_sortedPartition`, `endpoints_in_partition`.
- **Used by**: `consecutivePairs_cover`.
- **Visibility**: public
- **Lines**: 77–86
- **Notes**: Two-sided sandwich.

### theorem `sortedPartition_last`
- **Type**: `γ.sortedPartition.getLast sortedPartition_nonempty = γ.b`.
- **What**: The last element of the sorted partition is `γ.b`.
- **How**: Antisymmetric argument mirroring `sortedPartition_head`, but using `rel_getLast` and `List.getLast_mem` (8-line proof; main lemmas `sortedPartition_sorted.rel_getLast` and `sortedPartition_mem_Icc`).
- **Hypotheses**: none.
- **Uses-from-project**: same as `sortedPartition_head`.
- **Used by**: `consecutivePairs_cover`.
- **Visibility**: public
- **Lines**: 92–101
- **Notes**: Dual of `sortedPartition_head`.

### private theorem `sorted_consecutive_union`
- **Type**: for any pairwise `≤`-sorted list `pts` (with non-empty tail) whose head/last are `lo`/`hi`, `Icc lo hi ⊆ ⋃ p ∈ pts.zip pts.tail, Icc p.1 p.2`.
- **What**: Structural induction on a sorted list: consecutive segments cover the full `[head, last]` interval.
- **How**: Induction on `pts`: nil case from `absurd rfl hne`; cons case strips the head equality `x = lo`, then nested `cases xs`. The base `[x, y]` reduces to `⟨(x, y), List.mem_singleton.mpr rfl, ht⟩`; the inductive case `[x, y, z, zs]` splits `t ≤ y` (left segment) versus `y < t` (recurses on the tail using `ih hys_sorted hys_ne htail_ne' y hi rfl hlast`) (proof spans lines 108–152; >10 lines; key lemmas `List.zip_cons_cons`, `List.getLast_cons_cons`, `Set.mem_iUnion`/`Set.mem_iUnion₂`).
- **Hypotheses**: `pts.Pairwise (· ≤ ·)`; non-empty list and tail; head = `lo`, last = `hi`.
- **Uses-from-project**: none beyond Mathlib list/Set primitives.
- **Used by**: `consecutivePairs_cover`.
- **Visibility**: private
- **Lines**: 108–152
- **Notes**: Uses `push Not` to flip negated inequality in the recursive case.

### theorem `sortedPartition_tail_nonempty`
- **Type**: `γ.sortedPartition.tail ≠ []`.
- **What**: At least two distinct partition points (`a ≠ b`), so `tail` is non-empty.
- **How**: From `γ.hab : a < b`, derive `1 < γ.partition.card` via `Finset.one_lt_card`; convert to `2 ≤ length` using `Finset.length_sort`; assume `tail = []`, derive `length ≤ 1` by destructuring `sortedPartition` as `hd :: tl`; contradict via `linarith` (proof spans lines 155–171; >10 lines; key lemmas `Finset.one_lt_card`, `Finset.length_sort`).
- **Hypotheses**: none (uses `γ.hab` and `endpoints_in_partition`).
- **Uses-from-project**: `sortedPartition_nonempty`, `endpoints_in_partition`, `hab`.
- **Used by**: `consecutivePairs_cover`.
- **Visibility**: public
- **Lines**: 155–171
- **Notes**: Length-based argument.

### theorem `consecutivePairs_cover`
- **Type**: `Icc γ.a γ.b ⊆ ⋃ p ∈ γ.consecutivePairs, Icc p.1 p.2`.
- **What**: Consecutive-pair `Icc`s cover the parameter interval.
- **How**: Apply `sorted_consecutive_union` with the witnesses `sortedPartition_sorted`, `sortedPartition_nonempty`, `sortedPartition_tail_nonempty`, `sortedPartition_head`, `sortedPartition_last`.
- **Hypotheses**: none.
- **Uses-from-project**: all of the above.
- **Used by**: `forall_Icc_of_forall_consecutive`, `image_subset_of_consecutive_images`.
- **Visibility**: public
- **Lines**: 174–179
- **Notes**: Wraps the private induction lemma.

### private theorem `sorted_zip_tail_le`
- **Type**: for `l.Pairwise (· ≤ ·)` and `p ∈ l.zip l.tail`, `p.1 ≤ p.2`.
- **What**: Each pair from `zip` with tail satisfies the sorted relation.
- **How**: Induction on `l`; in the `cons x (cons y ys)` branch, the head pair `(x, y)` is handled by `List.pairwise_cons.mp hl).1 y List.mem_cons_self`, the recursive case by `ih ((List.pairwise_cons.mp hl).2) h` (12-line proof; key lemma `List.pairwise_cons`).
- **Hypotheses**: `l.Pairwise (· ≤ ·)`; `p ∈ l.zip l.tail`.
- **Uses-from-project**: none beyond Mathlib.
- **Used by**: `consecutivePairs_le`.
- **Visibility**: private
- **Lines**: 184–198
- **Notes**: Returns the pairwise relation pointwise on zip pairs.

### theorem `consecutivePairs_le`
- **Type**: `p ∈ γ.consecutivePairs → p.1 ≤ p.2`.
- **What**: Consecutive pairs are ordered.
- **How**: `sorted_zip_tail_le (sortedPartition_sorted γ) hp`.
- **Hypotheses**: `p ∈ γ.consecutivePairs`.
- **Uses-from-project**: `sorted_zip_tail_le`, `sortedPartition_sorted`.
- **Used by**: downstream segment lemmas requiring `p.1 ≤ p.2`.
- **Visibility**: public
- **Lines**: 201–203
- **Notes**: 1-line proof.

### theorem `consecutivePairs_subset`
- **Type**: each pair's components lie in `Icc γ.a γ.b`.
- **What**: Both endpoints of every consecutive pair are in the parameter interval.
- **How**: `List.of_mem_zip hp` gives membership of the two components in `sortedPartition` and its `tail`; then `sortedPartition_mem_Icc` on the head component, and `List.mem_of_mem_tail` + `sortedPartition_mem_Icc` on the tail component.
- **Hypotheses**: `p ∈ γ.consecutivePairs`.
- **Uses-from-project**: `sortedPartition_mem_Icc`.
- **Used by**: downstream segment analyses.
- **Visibility**: public
- **Lines**: 206–211
- **Notes**: 4-line proof.

### theorem `forall_Icc_of_forall_consecutive`
- **Type**: `(∀ p ∈ γ.consecutivePairs, ∀ t ∈ Icc p.1 p.2, P t) → ∀ t ∈ Icc γ.a γ.b, P t`.
- **What**: Reduces an interval property on `[a, b]` to consecutive segments.
- **How**: From `consecutivePairs_cover γ ht` extract `p, hp_mem, hp_t` via `Set.mem_iUnion₂.mp`; conclude `h p hp_mem t hp_t`.
- **Hypotheses**: piecewise property `P` holds on each consecutive segment.
- **Uses-from-project**: `consecutivePairs_cover`.
- **Used by**: downstream proofs that lift segment-by-segment claims to the global parameter interval.
- **Visibility**: public
- **Lines**: 217–222
- **Notes**: 4-line proof.

### theorem `image_subset_of_consecutive_images`
- **Type**: `(∀ p ∈ γ.consecutivePairs, γ.toFun '' Icc p.1 p.2 ⊆ S) → γ.toFun '' Icc γ.a γ.b ⊆ S`.
- **What**: Image variant: a curve whose every consecutive-segment image lies in `S` has full image in `S`.
- **How**: Pick `(t, ht, hz)` and a covering pair `p, hp_mem, hp_t`; apply `h p hp_mem ⟨t, hp_t, hz⟩`.
- **Hypotheses**: per-segment image inclusion.
- **Uses-from-project**: `consecutivePairs_cover`.
- **Used by**: downstream image-based segment-to-curve arguments.
- **Visibility**: public
- **Lines**: 226–231
- **Notes**: 4-line proof.

---

## File Summary

PiecewiseCurveAPI.lean develops a small list-based API for `PiecewiseC1Curve`, providing a sorted-partition view (`sortedPartition`) and consecutive-pair list (`consecutivePairs`). It proves: basic structural facts (sorted, no-duplicates, non-empty, members in `[a, b]`), identifies the head/last as `γ.a`/`γ.b`, shows the tail is non-empty, and — using a private induction lemma `sorted_consecutive_union` — concludes that the union of `Icc p.1 p.2` over consecutive pairs covers `[a, b]`. Auxiliary lemmas `consecutivePairs_le` and `consecutivePairs_subset` document the relational and inclusion properties of pairs (the relational lemma uses a second private induction `sorted_zip_tail_le`). The user-facing payoff is the pair `forall_Icc_of_forall_consecutive` and `image_subset_of_consecutive_images`, which reduce proofs of pointwise and image properties on `[a, b]` to per-segment statements.
