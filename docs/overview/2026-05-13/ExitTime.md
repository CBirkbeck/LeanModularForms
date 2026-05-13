# Inventory: ExitTime.lean

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ExitTime.lean`

Namespace: `LeanModularForms`. Imports `Mathlib.Topology.Order.IntermediateValue`, `Mathlib.Analysis.SpecialFunctions.Complex.Analytic`.

### `theorem exit_time_right_exists`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (h_s : γ t₀ = s) {ε : ℝ} (hε_pos : 0 ≤ ε) (hε_le : ε ≤ ‖γ (t₀ + δ) − s‖) : ∃ t_ε ∈ Icc t₀ (t₀ + δ), ‖γ t_ε − s‖ = ε`
- **What**: Existence (via IVT) of a right-side exit time `t_ε ∈ [t₀, t₀ + δ]` where `γ` is at distance exactly ε from s.
- **How**: Apply `intermediate_value_Icc` to the continuous function `t ↦ ‖γ t − s‖`, using `(hγ_cont.sub continuousOn_const).norm` for continuity and `simp [h_s, hε_pos, hε_le]` to package ε in the image interval.
- **Hypotheses**: δ > 0; γ continuous on `[t₀, t₀+δ]`; γ(t₀) = s; 0 ≤ ε ≤ ‖γ(t₀+δ) − s‖.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 44–55.
- **Notes**: none.

### `theorem exit_time_left_exists`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ − δ) t₀)) (h_s : γ t₀ = s) {ε : ℝ} (hε_pos : 0 ≤ ε) (hε_le : ε ≤ ‖γ (t₀ − δ) − s‖) : ∃ t_ε ∈ Icc (t₀ − δ) t₀, ‖γ t_ε − s‖ = ε`
- **What**: Existence of a left-side exit time `t_ε ∈ [t₀ − δ, t₀]` at distance exactly ε from s.
- **How**: Apply `intermediate_value_Icc'` (reverse-orientation IVT) to `t ↦ ‖γ t − s‖`.
- **Hypotheses**: δ > 0; γ continuous on `[t₀−δ, t₀]`; γ(t₀) = s; 0 ≤ ε ≤ ‖γ(t₀−δ) − s‖.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 60–71.
- **Notes**: none.

### `noncomputable def firstExitTimeRight`
- **Type**: `(γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) (ε : ℝ) : ℝ`
- **What**: The first exit time at radius ε on the right side: `sInf {t ∈ [t₀, t₀+δ] | ε ≤ ‖γ t − s‖}`. Returns junk (`sInf ∅`) when the set is empty.
- **How**: Direct `sInf` definition.
- **Hypotheses**: None (definition).
- **Uses from project**: [].
- **Used by**: `firstExitTimeRight_set_nonempty`, `firstExitTimeRight_set_lb`, `firstExitTimeRight_mem_Icc`, `ε_le_norm_at_firstExitTimeRight`, `t₀_lt_firstExitTimeRight`, `norm_at_firstExitTimeRight_eq`, `firstExitTimeRight_le_of_mem`, `firstExitTimeRight_mono_of_witness`, `firstExitTimeRight_tendsto_t₀`, `firstExitTimeRight_radius_eventually`, `HW33ExitData.ofExitTimes`.
- **Visibility**: public.
- **Lines**: 90–91.
- **Notes**: noncomputable.

### `theorem firstExitTimeRight_set_nonempty`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ + δ) − s‖) : (t₀ + δ) ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t − s‖}`
- **What**: The defining set of `firstExitTimeRight` is nonempty when `γ(t₀+δ)` is at least ε from s — explicitly `t₀+δ` is a witness.
- **How**: Combine `⟨by linarith, le_rfl⟩` for the Icc membership with `h_far`.
- **Hypotheses**: 0 ≤ δ; ε ≤ ‖γ(t₀+δ) − s‖.
- **Uses from project**: [].
- **Used by**: `firstExitTimeRight_mem_Icc`, `ε_le_norm_at_firstExitTimeRight`, `t₀_lt_firstExitTimeRight`, `firstExitTimeRight_tendsto_t₀` (indirectly via `firstExitTimeRight_le_of_mem`).
- **Visibility**: public.
- **Lines**: 94–98.
- **Notes**: none.

### `theorem firstExitTimeRight_set_lb`
- **Type**: `(γ : ℝ → ℂ) (t₀ δ ε : ℝ) (s : ℂ) : ∀ t ∈ {t ∈ Icc t₀ (t₀ + δ) | ε ≤ ‖γ t − s‖}, t₀ ≤ t`
- **What**: Every element of the defining set is at least `t₀` (i.e. the set is bounded below by t₀).
- **How**: Membership pattern-match `⟨hmem, _⟩` extracts `hmem.1 : t₀ ≤ t`.
- **Hypotheses**: none (universal).
- **Uses from project**: [].
- **Used by**: `firstExitTimeRight_mem_Icc`, `ε_le_norm_at_firstExitTimeRight`, `t₀_lt_firstExitTimeRight`, `firstExitTimeRight_le_of_mem`, `firstExitTimeRight_mono_of_witness`, `firstExitTimeRight_tendsto_t₀`, `norm_at_firstExitTimeRight_eq`.
- **Visibility**: public.
- **Lines**: 101–104.
- **Notes**: none.

### `theorem firstExitTimeRight_mem_Icc`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 ≤ δ) (hε_le : ε ≤ ‖γ (t₀ + δ) − s‖) : t₀ ≤ firstExitTimeRight γ t₀ δ s ε ∧ firstExitTimeRight γ t₀ δ s ε ≤ t₀ + δ`
- **What**: The first exit time lies in `[t₀, t₀+δ]`.
- **How**: Combine `le_csInf` (using `firstExitTimeRight_set_lb`) with `csInf_le` (using nonemptiness via `firstExitTimeRight_set_nonempty` and bounded-below via `firstExitTimeRight_set_lb`).
- **Hypotheses**: 0 ≤ δ; the defining set is nonempty (witness `t₀+δ`).
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_set_nonempty`, `firstExitTimeRight_set_lb`.
- **Used by**: `norm_at_firstExitTimeRight_eq`.
- **Visibility**: public.
- **Lines**: 107–115.
- **Notes**: none.

### `theorem ε_le_norm_at_firstExitTimeRight`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (hε_le : ε ≤ ‖γ (t₀ + δ) − s‖) : ε ≤ ‖γ (firstExitTimeRight γ t₀ δ s ε) − s‖`
- **What**: The first exit time itself is at least ε from s (closed-and-bounded ⇒ infimum is in the set).
- **How**: >10 lines, key lemma: write `S = Icc t₀ (t₀+δ) ∩ (‖γ t − s‖) ⁻¹' Ici ε`; show closed via `(hγ_cont.sub continuousOn_const).norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici`; show nonempty (`firstExitTimeRight_set_nonempty`) and bounded below (`firstExitTimeRight_set_lb`); apply `IsClosed.csInf_mem` and extract second component.
- **Hypotheses**: δ > 0; γ continuous; ε ≤ ‖γ(t₀+δ) − s‖.
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_set_nonempty`, `firstExitTimeRight_set_lb`.
- **Used by**: `norm_at_firstExitTimeRight_eq`.
- **Visibility**: public.
- **Lines**: 123–136.
- **Notes**: >10 lines.

### `theorem t₀_lt_firstExitTimeRight`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ + δ) − s‖) : t₀ < firstExitTimeRight γ t₀ δ s ε`
- **What**: For ε > 0 and γ(t₀) = s, the first exit time is strictly greater than t₀: continuity rules out a neighborhood of t₀.
- **How**: >10 lines, key lemmas: `(hγ_cont t₀ …).sub continuousWithinAt_const).norm` for continuity at t₀; `tendsto.eventually_lt_const` to get a ball around t₀ with `‖γ t − s‖ < ε`; extract `η` via `Metric.nhdsWithin_basis_ball.eventually_iff`; lift to `t₀ + min η δ / 2 ≤ firstExitTimeRight …` via `le_csInf` and a contradiction with `not_le.mpr (hη …)`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; ε > 0; ε ≤ ‖γ(t₀+δ) − s‖.
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_set_nonempty`, `firstExitTimeRight_set_lb`.
- **Used by**: `norm_at_firstExitTimeRight_eq`, `firstExitTimeRight_tendsto_t₀`.
- **Visibility**: public.
- **Lines**: 143–164.
- **Notes**: >10 lines.

### `theorem norm_at_firstExitTimeRight_eq`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ + δ) − s‖) : ‖γ (firstExitTimeRight γ t₀ δ s ε) − s‖ = ε`
- **What**: Exact-radius equality at the right first exit time: the function value at the inf is exactly ε.
- **How**: >30 lines, key lemma: `le_antisymm` against `ε_le_norm_at_firstExitTimeRight`; assume by contradiction `ε < ‖γ t_ε − s‖`; continuity gives a ball where `ε < ‖γ t − s‖`; choose `r = min(η/2, (t_ε − t₀)/2)`, get `t_ε − r ∈ Icc t₀ (t₀+δ)` and `dist(t_ε − r, t_ε) < η`; conclude `t_ε ≤ t_ε − r` via `csInf_le` (using `firstExitTimeRight_set_lb`), contradicting `r > 0`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; ε > 0; ε ≤ ‖γ(t₀+δ) − s‖.
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_mem_Icc`, `firstExitTimeRight_set_lb`, `ε_le_norm_at_firstExitTimeRight`, `t₀_lt_firstExitTimeRight`.
- **Used by**: `firstExitTimeRight_radius_eventually`.
- **Visibility**: public.
- **Lines**: 171–202.
- **Notes**: >30 lines.

### `noncomputable def firstExitTimeLeft`
- **Type**: `(γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) (ε : ℝ) : ℝ`
- **What**: Left-side first exit time `sSup {t ∈ [t₀−δ, t₀] | ε ≤ ‖γ t − s‖}`. Mirror of `firstExitTimeRight` using `sSup` since the curve approaches s from the left as t ↑ t₀.
- **How**: Direct `sSup` definition.
- **Hypotheses**: None (definition).
- **Uses from project**: [].
- **Used by**: `firstExitTimeLeft_set_nonempty`, `firstExitTimeLeft_set_ub`, `firstExitTimeLeft_mem_Icc`, `ε_le_norm_at_firstExitTimeLeft`, `firstExitTimeLeft_lt_t₀`, `norm_at_firstExitTimeLeft_eq`, `firstExitTimeLeft_ge_of_mem`, `firstExitTimeLeft_anti_of_witness`, `firstExitTimeLeft_tendsto_t₀`, `firstExitTimeLeft_radius_eventually`, `HW33ExitData.ofExitTimes`.
- **Visibility**: public.
- **Lines**: 214–215.
- **Notes**: noncomputable.

### `theorem firstExitTimeLeft_set_nonempty`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 ≤ δ) (h_far : ε ≤ ‖γ (t₀ − δ) − s‖) : (t₀ − δ) ∈ {t ∈ Icc (t₀ − δ) t₀ | ε ≤ ‖γ t − s‖}`
- **What**: Nonemptiness of the defining set via the witness `t₀ − δ`.
- **How**: `⟨⟨le_rfl, by linarith⟩, h_far⟩`.
- **Hypotheses**: 0 ≤ δ; ε ≤ ‖γ(t₀−δ) − s‖.
- **Uses from project**: [].
- **Used by**: `firstExitTimeLeft_mem_Icc`, `ε_le_norm_at_firstExitTimeLeft`, `firstExitTimeLeft_lt_t₀`.
- **Visibility**: public.
- **Lines**: 218–222.
- **Notes**: none.

### `theorem firstExitTimeLeft_set_ub`
- **Type**: `(γ : ℝ → ℂ) (t₀ δ ε : ℝ) (s : ℂ) : ∀ t ∈ {t ∈ Icc (t₀ − δ) t₀ | ε ≤ ‖γ t − s‖}, t ≤ t₀`
- **What**: The defining set is bounded above by `t₀`.
- **How**: Pattern-match `⟨hmem, _⟩` and extract `hmem.2`.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `firstExitTimeLeft_mem_Icc`, `ε_le_norm_at_firstExitTimeLeft`, `firstExitTimeLeft_lt_t₀`, `norm_at_firstExitTimeLeft_eq`, `firstExitTimeLeft_ge_of_mem`, `firstExitTimeLeft_anti_of_witness`, `firstExitTimeLeft_tendsto_t₀`.
- **Visibility**: public.
- **Lines**: 225–228.
- **Notes**: none.

### `theorem firstExitTimeLeft_mem_Icc`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 ≤ δ) (hε_le : ε ≤ ‖γ (t₀ − δ) − s‖) : t₀ − δ ≤ firstExitTimeLeft γ t₀ δ s ε ∧ firstExitTimeLeft γ t₀ δ s ε ≤ t₀`
- **What**: `firstExitTimeLeft ∈ [t₀ − δ, t₀]`.
- **How**: `le_csSup` with the upper-bound witness `t₀` (from `firstExitTimeLeft_set_ub`) combined with `csSup_le` and the nonemptiness witness from `firstExitTimeLeft_set_nonempty`.
- **Hypotheses**: 0 ≤ δ; set nonempty.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_set_nonempty`, `firstExitTimeLeft_set_ub`.
- **Used by**: `norm_at_firstExitTimeLeft_eq`.
- **Visibility**: public.
- **Lines**: 231–239.
- **Notes**: none.

### `theorem ε_le_norm_at_firstExitTimeLeft`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ − δ) t₀)) (hε_le : ε ≤ ‖γ (t₀ − δ) − s‖) : ε ≤ ‖γ (firstExitTimeLeft γ t₀ δ s ε) − s‖`
- **What**: At the supremum, γ is still at distance ≥ ε from s (closed set ⇒ sup ∈ set).
- **How**: >10 lines, key lemma: form the closed set `S = Icc (t₀−δ) t₀ ∩ (‖γ t − s‖) ⁻¹' Ici ε`; check closedness via `…norm.preimage_isClosed_of_isClosed`; check nonempty / bounded-above via `firstExitTimeLeft_set_nonempty/ub`; apply `IsClosed.csSup_mem` and take the second component.
- **Hypotheses**: δ > 0; γ continuous; ε ≤ ‖γ(t₀−δ) − s‖.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_set_nonempty`, `firstExitTimeLeft_set_ub`.
- **Used by**: `norm_at_firstExitTimeLeft_eq`.
- **Visibility**: public.
- **Lines**: 247–260.
- **Notes**: >10 lines.

### `theorem firstExitTimeLeft_lt_t₀`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ − δ) t₀)) (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ − δ) − s‖) : firstExitTimeLeft γ t₀ δ s ε < t₀`
- **What**: The left first exit time is strictly less than `t₀`: continuity rules out a left-neighborhood of t₀.
- **How**: >10 lines, key lemmas: continuity at t₀ via `.sub continuousWithinAt_const).norm`; `tendsto.eventually_lt_const` produces a ball; extract `η` from `Metric.nhdsWithin_basis_ball`; use `lt_of_le_of_lt` with `t₀ − min(η,δ)/2` as upper-bound witness; close via `csSup_le` and a contradiction.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; ε > 0; ε ≤ ‖γ(t₀−δ) − s‖.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_set_nonempty`, `firstExitTimeLeft_set_ub`.
- **Used by**: `norm_at_firstExitTimeLeft_eq`, `firstExitTimeLeft_tendsto_t₀`.
- **Visibility**: public.
- **Lines**: 267–288.
- **Notes**: >10 lines.

### `theorem norm_at_firstExitTimeLeft_eq`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ − δ) t₀)) (h_s : γ t₀ = s) (hε_pos : 0 < ε) (hε_le : ε ≤ ‖γ (t₀ − δ) − s‖) : ‖γ (firstExitTimeLeft γ t₀ δ s ε) − s‖ = ε`
- **What**: Exact-radius equality at the left first exit time.
- **How**: >30 lines, key lemma: `le_antisymm` against `ε_le_norm_at_firstExitTimeLeft`; assume by contradiction `ε < ‖γ t_ε − s‖`; use continuity at t_ε to find a neighborhood; choose `r = min(η/2, (t₀−t_ε)/2)`, show `t_ε + r ∈ Icc (t₀−δ) t₀` and `dist(t_ε+r, t_ε) < η`; conclude `t_ε + r ≤ t_ε` via `le_csSup`, contradicting `r > 0`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; ε > 0; ε ≤ ‖γ(t₀−δ) − s‖.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_mem_Icc`, `firstExitTimeLeft_set_ub`, `ε_le_norm_at_firstExitTimeLeft`, `firstExitTimeLeft_lt_t₀`.
- **Used by**: `firstExitTimeLeft_radius_eventually`.
- **Visibility**: public.
- **Lines**: 293–324.
- **Notes**: >30 lines.

### `theorem exists_right_modulus`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (h_s : γ t₀ = s) {ε : ℝ} (hε_pos : 0 < ε) : ∃ η ∈ Ioc 0 δ, ∀ t ∈ Icc t₀ (t₀ + η), ‖γ t − s‖ < ε`
- **What**: Right-side `(ε, δ)`-modulus of continuity: there is η ∈ (0, δ] such that on `[t₀, t₀+η]`, γ stays within ε of s.
- **How**: >10 lines, key lemmas: continuity at t₀ via `.sub continuousWithinAt_const).norm`; `tendsto.eventually_lt_const` yields a ball, extract `η₀` via `Metric.nhdsWithin_basis_ball.eventually_iff`; pick η = min(η₀/2, δ/2); check `Ioc` membership; for t ∈ [t₀, t₀+η] verify the ball condition with `Real.dist_eq` and `abs_of_nonneg`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; ε > 0.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 332–348.
- **Notes**: >10 lines.

### `theorem exists_left_modulus`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ − δ) t₀)) (h_s : γ t₀ = s) {ε : ℝ} (hε_pos : 0 < ε) : ∃ η ∈ Ioc 0 δ, ∀ t ∈ Icc (t₀ − η) t₀, ‖γ t − s‖ < ε`
- **What**: Symmetric left-side modulus of continuity.
- **How**: >10 lines, key lemmas: the symmetric construction of `exists_right_modulus`, replacing `abs_of_nonneg` with `abs_of_nonpos` after computing `t − t₀ ≤ 0`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; ε > 0.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 351–367.
- **Notes**: >10 lines.

### `theorem firstExitTimeRight_le_of_mem`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} {t₁ : ℝ} (ht₁ : t₁ ∈ Icc t₀ (t₀ + δ)) (h_far : ε ≤ ‖γ t₁ − s‖) : firstExitTimeRight γ t₀ δ s ε ≤ t₁`
- **What**: If `t₁` is in the Icc and far enough from s, then the first exit time on the right is at most `t₁`.
- **How**: Direct `csInf_le` with the bounded-below witness `⟨t₀, firstExitTimeRight_set_lb …⟩` and membership data `⟨ht₁, h_far⟩`.
- **Hypotheses**: `t₁ ∈ Icc t₀ (t₀+δ)`; ε ≤ ‖γ t₁ − s‖.
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_set_lb`.
- **Used by**: `firstExitTimeRight_tendsto_t₀`.
- **Visibility**: public.
- **Lines**: 373–378.
- **Notes**: none.

### `theorem firstExitTimeLeft_ge_of_mem`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ ε : ℝ} {s : ℂ} {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (t₀ − δ) t₀) (h_far : ε ≤ ‖γ t₁ − s‖) : t₁ ≤ firstExitTimeLeft γ t₀ δ s ε`
- **What**: Symmetric lower-bound by witness for the left first exit time.
- **How**: `le_csSup` with the upper-bound witness `⟨t₀, firstExitTimeLeft_set_ub …⟩` and `⟨ht₁, h_far⟩`.
- **Hypotheses**: `t₁ ∈ Icc (t₀ − δ) t₀`; ε ≤ ‖γ t₁ − s‖.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_set_ub`.
- **Used by**: `firstExitTimeLeft_tendsto_t₀`.
- **Visibility**: public.
- **Lines**: 382–387.
- **Notes**: none.

### `theorem firstExitTimeRight_mono_of_witness`
- **Type**: `(γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) {ε₁ ε₂ : ℝ} (h_le : ε₁ ≤ ε₂) (h_witness : ∃ t ∈ Icc t₀ (t₀ + δ), ε₂ ≤ ‖γ t − s‖) : firstExitTimeRight γ t₀ δ s ε₁ ≤ firstExitTimeRight γ t₀ δ s ε₂`
- **What**: For ε₁ ≤ ε₂ with ε₂ achievable in the Icc, the first exit time on the right is monotone in ε.
- **How**: Use `csInf_le_csInf` with the lower-bound witness `⟨t₀, firstExitTimeRight_set_lb…⟩`, the nonemptiness witness `⟨t₂, …⟩`, and the set inclusion `{ε₂ ≤ ‖…‖} ⊆ {ε₁ ≤ ‖…‖}` (via `h_le.trans`).
- **Hypotheses**: ε₁ ≤ ε₂; ε₂ is achievable.
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_set_lb`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 398–405.
- **Notes**: none.

### `theorem firstExitTimeLeft_anti_of_witness`
- **Type**: `(γ : ℝ → ℂ) (t₀ δ : ℝ) (s : ℂ) {ε₁ ε₂ : ℝ} (h_le : ε₁ ≤ ε₂) (h_witness : ∃ t ∈ Icc (t₀ − δ) t₀, ε₂ ≤ ‖γ t − s‖) : firstExitTimeLeft γ t₀ δ s ε₂ ≤ firstExitTimeLeft γ t₀ δ s ε₁`
- **What**: Symmetric anti-monotonicity for the left first exit time.
- **How**: `csSup_le_csSup` with the upper-bound witness, the nonemptiness witness, and the same set-inclusion proof.
- **Hypotheses**: ε₁ ≤ ε₂; ε₂ is achievable.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_set_ub`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 409–416.
- **Notes**: none.

### `theorem firstExitTimeRight_tendsto_t₀`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ioc t₀ (t₀ + δ), γ t ≠ s) : Tendsto (fun ε => firstExitTimeRight γ t₀ δ s ε) (𝓝[>] 0) (𝓝[>] t₀)`
- **What**: The right first exit time tends to `t₀` from above as ε → 0⁺.
- **How**: >30 lines, key lemmas: split via `tendsto_nhdsWithin_iff`; metric direction: pick `t₁ = t₀ + min(η,δ)/2`, show `‖γ t₁ − s‖ > 0`, use `firstExitTimeRight_le_of_mem` for the upper bound and `le_csInf` (via `firstExitTimeRight_set_lb`) for the lower bound; eventual-membership direction: `Ioo_mem_nhdsGT h_far_pos` plus `t₀_lt_firstExitTimeRight`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; γ avoids s on (t₀, t₀+δ].
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_set_lb`, `firstExitTimeRight_le_of_mem`, `t₀_lt_firstExitTimeRight`.
- **Used by**: `HW33ExitData.ofExitTimes`.
- **Visibility**: public.
- **Lines**: 426–461.
- **Notes**: >30 lines.

### `theorem firstExitTimeLeft_tendsto_t₀`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ − δ) t₀)) (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ico (t₀ − δ) t₀, γ t ≠ s) : Tendsto (fun ε => firstExitTimeLeft γ t₀ δ s ε) (𝓝[>] 0) (𝓝[<] t₀)`
- **What**: The left first exit time tends to `t₀` from below as ε → 0⁺.
- **How**: >30 lines, key lemmas: symmetric to `firstExitTimeRight_tendsto_t₀`, picking `t₁ = t₀ − min(η,δ)/2`, using `firstExitTimeLeft_ge_of_mem` and `csSup_le` (via `firstExitTimeLeft_set_ub`); eventual-membership via `firstExitTimeLeft_lt_t₀`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; γ avoids s on [t₀−δ, t₀).
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_set_ub`, `firstExitTimeLeft_ge_of_mem`, `firstExitTimeLeft_lt_t₀`.
- **Used by**: `HW33ExitData.ofExitTimes`.
- **Visibility**: public.
- **Lines**: 466–502.
- **Notes**: >30 lines.

### `theorem firstExitTimeRight_radius_eventually`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δ))) (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ioc t₀ (t₀ + δ), γ t ≠ s) : ∀ᶠ ε in 𝓝[>] 0, ‖γ (firstExitTimeRight γ t₀ δ s ε) − s‖ = ε`
- **What**: For all sufficiently small ε > 0, the right first exit time hits radius exactly ε.
- **How**: Extract `h_far_pos : 0 < ‖γ(t₀+δ) − s‖` via `h_leave _ ⟨…⟩`; `filter_upwards` with `Ioo_mem_nhdsGT h_far_pos`; close via `norm_at_firstExitTimeRight_eq`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; γ avoids s on (t₀, t₀+δ].
- **Uses from project**: `firstExitTimeRight`, `norm_at_firstExitTimeRight_eq`.
- **Used by**: `HW33ExitData.ofExitTimes`.
- **Visibility**: public.
- **Lines**: 510–520.
- **Notes**: none.

### `theorem firstExitTimeLeft_radius_eventually`
- **Type**: `{γ : ℝ → ℂ} {t₀ δ : ℝ} {s : ℂ} (hδ : 0 < δ) (hγ_cont : ContinuousOn γ (Icc (t₀ − δ) t₀)) (h_s : γ t₀ = s) (h_leave : ∀ t ∈ Ico (t₀ − δ) t₀, γ t ≠ s) : ∀ᶠ ε in 𝓝[>] 0, ‖γ (firstExitTimeLeft γ t₀ δ s ε) − s‖ = ε`
- **What**: Symmetric eventual exact-radius statement for the left.
- **How**: `filter_upwards [Ioo_mem_nhdsGT h_far_pos]` closes via `norm_at_firstExitTimeLeft_eq`.
- **Hypotheses**: δ > 0; γ continuous; γ(t₀) = s; γ avoids s on [t₀−δ, t₀).
- **Uses from project**: `firstExitTimeLeft`, `norm_at_firstExitTimeLeft_eq`.
- **Used by**: `HW33ExitData.ofExitTimes`.
- **Visibility**: public.
- **Lines**: 523–533.
- **Notes**: none.

### `structure HW33ExitData`
- **Type**: `(γ : ℝ → ℂ) (t₀ : ℝ) (s : ℂ)`
- **What**: Bundle of the four asymptotic exit-time hypotheses required by HW Theorem 3.3 (`hw_theorem_3_3_odd_transverse_parametric`): two exit-time functions `tPlus`, `tMinus`, their convergence to t₀ from above / below, and eventual exact-radius properties.
- **How**: Inductive record with six fields: `tPlus`, `tMinus`, `plus_to`, `plus_radius`, `minus_to`, `minus_radius`.
- **Hypotheses**: None (structure).
- **Uses from project**: [].
- **Used by**: `HW33ExitData.ofExitTimes`.
- **Visibility**: public.
- **Lines**: 540–552.
- **Notes**: none.

### `noncomputable def HW33ExitData.ofExitTimes`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {s : ℂ} {δPlus δMinus : ℝ} (hδPlus : 0 < δPlus) (hδMinus : 0 < δMinus) (hγ_cont_right : ContinuousOn γ (Icc t₀ (t₀ + δPlus))) (hγ_cont_left : ContinuousOn γ (Icc (t₀ − δMinus) t₀)) (h_s : γ t₀ = s) (h_leave_right : ∀ t ∈ Ioc t₀ (t₀ + δPlus), γ t ≠ s) (h_leave_left : ∀ t ∈ Ico (t₀ − δMinus) t₀, γ t ≠ s) : HW33ExitData γ t₀ s`
- **What**: Canonical construction of `HW33ExitData` using `firstExitTimeRight` / `firstExitTimeLeft` and their tendsto + eventual-radius lemmas.
- **How**: Anonymous-constructor record build: `tPlus := firstExitTimeRight γ t₀ δPlus s`, `tMinus := firstExitTimeLeft γ t₀ δMinus s`, with `plus_to`, `plus_radius`, `minus_to`, `minus_radius` filled by `firstExitTimeRight_tendsto_t₀`, `firstExitTimeRight_radius_eventually`, `firstExitTimeLeft_tendsto_t₀`, `firstExitTimeLeft_radius_eventually` respectively.
- **Hypotheses**: positive radii on both sides; continuity on both sides; γ(t₀) = s; γ avoids s away from t₀ on each side.
- **Uses from project**: `HW33ExitData`, `firstExitTimeRight`, `firstExitTimeLeft`, `firstExitTimeRight_tendsto_t₀`, `firstExitTimeRight_radius_eventually`, `firstExitTimeLeft_tendsto_t₀`, `firstExitTimeLeft_radius_eventually`.
- **Used by**: unused in file.
- **Visibility**: public.
- **Lines**: 558–576.
- **Notes**: noncomputable.

## File Summary

- 22 declarations: 2 `noncomputable def`s (`firstExitTimeRight`, `firstExitTimeLeft`), 2 `structure`s (`HW33ExitData`), 1 `noncomputable def` for the structure builder (`HW33ExitData.ofExitTimes`), and 17 theorems.
- 0 private/scoped declarations, 0 `set_option`, no sorry / TODO / axiom.
- Builds the exit-time apparatus on both sides of a crossing time `t₀`, in three layers: (1) IVT-based existence (`exit_time_right/left_exists`); (2) `sInf`/`sSup`-based canonical definitions (`firstExitTimeRight`, `firstExitTimeLeft`) with their basic properties (membership in Icc, strict positivity, eventual radius equality, tendsto t₀); (3) the bundling `HW33ExitData` and its canonical constructor `ofExitTimes`. The file's only mathlib dependencies are `Topology.Order.IntermediateValue` and `Analysis.SpecialFunctions.Complex.Analytic`; no project dependencies outside the namespace.
- Total declarations: 22. (N3 = 22.)
