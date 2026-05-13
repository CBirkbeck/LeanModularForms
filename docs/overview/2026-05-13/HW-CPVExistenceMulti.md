# Inventory: HungerbuhlerWasem/CPVExistenceMulti.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/CPVExistenceMulti.lean`
Lines: 391

Namespace: `HungerbuhlerWasem`

### `private theorem min_pairwise_distance_pos`
- **Type**: `{crossings : Finset ℝ} (h_card_ge_two : 2 ≤ crossings.card) : ∃ d > 0, ∀ t₁ ∈ crossings, ∀ t₂ ∈ crossings, t₁ ≠ t₂ → d ≤ |t₁ - t₂|`
- **What**: For a finset of reals of cardinality ≥ 2, the minimum pairwise distance between distinct elements is a positive lower bound.
- **How**: Form the filtered pair-finset `(crossings ×ˢ crossings).filter (fun p => p.1 ≠ p.2)`; nonempty by `Finset.one_lt_card`. Use `Finset.exists_min_image` to obtain a minimizing pair `p_min`; positivity of `|p_min.1 - p_min.2|` follows from `abs_pos` + `sub_ne_zero` on the filter membership; the universal bound comes from the minimum property applied to `(t₁, t₂)`.
- **Hypotheses**: cardinality ≥ 2.
- **Uses from project**: [].
- **Used by**: `multi_pole_common_radius`.
- **Visibility**: private
- **Lines**: 76-98
- **Notes**: classical; uses `Finset.exists_min_image`

### `private theorem crossings_bounded_from_endpoints_finset`
- **Type**: `{crossings : Finset ℝ} (h_nonempty : crossings.Nonempty) (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo 0 1) : ∃ a > 0, ∀ t ∈ crossings, a ≤ t ∧ t ≤ 1 - a`
- **What**: For a nonempty finset of reals all in `Ioo 0 1`, there is `a > 0` bounding every element away from both endpoints.
- **How**: Use `Finset.exists_min_image` with key `fun t => min t (1 - t)`; the minimum at `t_min` is positive by `lt_min` from `t_min ∈ Ioo 0 1`. Then `a = min t_min (1 - t_min)`; the bound `a ≤ t` follows from `min_le_left`, and `t ≤ 1 - a` from `min_le_right` after a `linarith`.
- **Hypotheses**: crossings nonempty; all in `Ioo 0 1`.
- **Uses from project**: [].
- **Used by**: `multi_pole_common_radius`.
- **Visibility**: private
- **Lines**: 103-117

### `private theorem crossings_bounded_from_partition_finset`
- **Type**: `{crossings partition : Finset ℝ} (h_nonempty : crossings.Nonempty) (h_off : ∀ t ∈ crossings, t ∉ partition) : ∃ b > 0, ∀ t ∈ crossings, ∀ p ∈ partition, b ≤ |t - p|`
- **What**: For a nonempty finset `crossings` whose elements are all disjoint from `partition`, there is `b > 0` bounding `|t - p|` from below for every `t ∈ crossings, p ∈ partition`.
- **How**: Case-split on `partition = ∅` (take `b = 1`, vacuous bound). Otherwise pick `p₀`, `t₀`; form `pairs = crossings ×ˢ partition` (nonempty); use `Finset.exists_min_image` on `|q.1 - q.2|`. Positivity from `abs_pos` + `sub_eq_zero` (would equate a crossing with a partition point, contradicting `h_off`).
- **Hypotheses**: crossings nonempty; each crossing is off partition.
- **Uses from project**: [].
- **Used by**: `multi_pole_common_radius`.
- **Visibility**: private
- **Lines**: 122-154
- **Notes**: ~33 lines

### `theorem multi_pole_common_radius`
- **Type**: `{crossings partition : Finset ℝ} (h_nonempty : crossings.Nonempty) (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo 0 1) (h_off : ∀ t ∈ crossings, t ∉ partition) : ∃ r > 0, (∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r) ∧ (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|) ∧ (∀ t ∈ crossings, ∀ p ∈ partition, r < |t - p|)`
- **What**: Extracts a common positive radius `r` such that every crossing window `[t_i - r, t_i + r]` is interior to `[0,1]`, pairwise disjoint between distinct crossings (distance > 2r), and disjoint from the partition (distance > r).
- **How**: Use `crossings_bounded_from_endpoints_finset` to get `a > 0` bounding crossings away from `{0, 1}`; `crossings_bounded_from_partition_finset` to get `b > 0` bounding away from partition. Case-split `crossings.card = 1` (take `r = min a (b/2)`, pairwise vacuous since only one crossing) vs. `card ≥ 2` (use `min_pairwise_distance_pos` to get `d > 0`; take `r = min a (min (b/2) (d/4))`). The 1/4 factor on d gives `2r < d ≤ |t - t'|`; the 1/2 on b gives `r < b/2 ≤ |t - p|`. Discharges via `linarith` on each branch.
- **Hypotheses**: crossings nonempty in Ioo 0 1, off partition.
- **Uses from project**: `crossings_bounded_from_endpoints_finset`, `crossings_bounded_from_partition_finset`, `min_pairwise_distance_pos`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 165-221
- **Notes**: ~57 line proof; key geometric scaffolding for multi-crossing CPV

### `theorem multi_pole_local_uniqueness`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {crossings : Finset ℝ} {r : ℝ} (hr_pos : 0 < r) (h_endpts : ∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r) (h_pairwise : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|) (h_complete : ∀ t ∈ Icc 0 1, γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings) {t_i : ℝ} (ht_i_mem : t_i ∈ crossings) {t : ℝ} (ht_in : t ∈ Icc (t_i - r) (t_i + r)) (h_eq : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s) : t = t_i`
- **What**: Per-crossing local uniqueness — on the window `[t_i - r, t_i + r]`, the only parameter mapping to `s` is `t_i` itself, given the global completeness and pairwise-disjointness data.
- **How**: From `h_endpts` get `t ∈ Icc 0 1` (via `linarith` on `ht_in`); from `h_complete` deduce `t ∈ crossings`. Contradiction: if `t ≠ t_i`, then `h_pairwise t_i t` gives `2r < |t_i - t|`, but `ht_in` gives `|t_i - t| ≤ r` (via `abs_sub_comm` + `abs_le`), contradicting `r > 0`.
- **Hypotheses**: r positive, crossings interior to [r, 1-r], pairwise distant > 2r, `γ⁻¹(s) ⊆ crossings`, t_i ∈ crossings, t in window, `γ(t) = s`.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.toPwC1Immersion`, `PwC1Immersion.toPiecewiseC1Path`, `PiecewiseC1Path.toPath`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 231-256

### `theorem multi_pole_local_far_bound`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t_i : ℝ} {r : ℝ} (hr_pos : 0 < r) (h_local_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t_i) {r' : ℝ} (hr'_pos : 0 < r') (hr'_le : r' ≤ r) : ∃ m > 0, (∀ t ∈ Icc (t_i - r) (t_i - r'), m ≤ ‖γ.toPath.extend t - s‖) ∧ (∀ t ∈ Icc (t_i + r') (t_i + r), m ≤ ‖γ.toPath.extend t - s‖)`
- **What**: Local far-bound — on each closed half-window `[t_i - r, t_i - r']` and `[t_i + r', t_i + r]` (for any `0 < r' < r`), `‖γ(t) - s‖` has a positive lower bound.
- **How**: Use continuity of `γ` (`PiecewiseC1Path.toPath.continuous_extend`), so `t ↦ ‖γ(t) - s‖` is continuous; left and right half-windows are compact and nonempty; apply `IsCompact.exists_isMinOn`. The minimizers `t_l, t_r` are not equal to `t_i` (would force `t_i ≤ t_i - r'` or `t_i + r' ≤ t_i`, contradicting `r' > 0`); by local uniqueness `γ(t_l) ≠ s` and `γ(t_r) ≠ s`, hence positivity via `norm_pos_iff` + `sub_ne_zero`. Take `m = min m_l m_r`.
- **Hypotheses**: r positive, local uniqueness on the window, 0 < r' ≤ r.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.toPwC1Immersion`, `PwC1Immersion.toPiecewiseC1Path`, `PiecewiseC1Path.toPath`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 264-319
- **Notes**: ~56 line proof; uses `IsCompact.exists_isMinOn`

### `theorem multi_pole_crossing_mem_window`
- **Type**: `{t_i : ℝ} {r : ℝ} (hr_pos : 0 < r) : t_i ∈ Set.Ioo (t_i - r) (t_i + r)`
- **What**: A crossing lies strictly in its own window `(t_i - r, t_i + r)` — trivial interiority fact.
- **How**: One-line `⟨by linarith, by linarith⟩` using `0 < r`.
- **Hypotheses**: r positive.
- **Uses from project**: [].
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 338-341

### `theorem multi_pole_crossing_in_Ioo`
- **Type**: `{t_i : ℝ} {r : ℝ} (hr_pos : 0 < r) (h_ge : r ≤ t_i) (h_le : t_i ≤ 1 - r) : t_i ∈ Set.Ioo 0 1`
- **What**: From the window-interiority bounds `r ≤ t_i ≤ 1 - r`, the crossing lies strictly in `(0, 1)`.
- **How**: One-line `⟨by linarith, by linarith⟩`.
- **Hypotheses**: r positive, t_i in [r, 1-r].
- **Uses from project**: [].
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 344-347

## File Summary

Geometric scaffolding for the multi-crossing CPV existence problem in the Hungerbühler-Wasem framework. Three private finset helpers (`min_pairwise_distance_pos`, `crossings_bounded_from_endpoints_finset`, `crossings_bounded_from_partition_finset`) feed `multi_pole_common_radius`, which extracts a common positive radius `r` ensuring pairwise-disjoint crossing windows interior to `[0,1]` and avoiding the partition. `multi_pole_local_uniqueness` and `multi_pole_local_far_bound` provide the per-window local data needed by per-crossing single-crossing CPV machinery. Two trivial helpers (`multi_pole_crossing_mem_window`, `multi_pole_crossing_in_Ioo`) complete the file. Long comment sections sketch the remaining path forward (cutoff integral decomposition, per-crossing convergence, polar-part lift) needed to discharge the oracle `h_multi_cpv` in `residueTheorem_crossing_asymmetric_multiPole`. No `sorry`/`axiom`/heartbeat overrides; the file delivers geometric foundations only, not the full multi-crossing CPV theorem.
