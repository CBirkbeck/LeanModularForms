# HomotopyDefs.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HomotopyDefs.lean`

## Imports
- `LeanModularForms.ForMathlib.PiecewiseC1Path`
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle`

## Declarations

### `def PiecewiseCurvesHomotopicAvoiding`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) (P : Finset ℝ) : Prop`
- **What**: Piecewise C¹ homotopy on `[0,1]` between two closed curves `γ₀, γ₁ : ℝ → ℂ`, avoiding `z₀`, with breakpoint set `P : Finset ℝ`. Asserts existence of `H : ℝ × ℝ → ℂ` that is continuous, has the right boundary values (`H(·,0)=γ₀`, `H(·,1)=γ₁`), is closed (`H(0,s)=H(1,s)`), never hits `z₀`, is differentiable in `t` away from `P` for every `s`, has continuous `t`-derivative on each `Ioo p₁ p₂ ×ˢ Icc 0 1` for partition-free sub-intervals, and admits a global uniform `t`-derivative bound `M`.
- **How**: Direct definitional `∃ H, ... ∧ ...` packaging eight conjuncts. Not a theorem — no proof body.
- **Hypotheses**: None (it is a definition / `Prop`).
- **Uses from project**: [] (only `Continuous`, `Set.Icc`, `Set.Ioo`, `DifferentiableAt`, `deriv`, `ContinuousOn`, `Finset`, `Set.prod` from mathlib).
- **Used by**: `ClosedCurvesHomotopicAvoiding.toPiecewise`, `PiecewiseCurvesHomotopicAvoiding.refl`, `PiecewiseCurvesHomotopicAvoiding.symm`.
- **Visibility**: public (def).
- **Lines**: 45–69.
- **Notes**: 9-tuple existential.

### `def ClosedCurvesHomotopicAvoiding`
- **Type**: `(γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) : Prop`
- **What**: Smooth (no partition) version of the homotopy. Asserts existence of `H : ℝ × ℝ → ℂ` satisfying continuity, boundary conditions `H(·,0)=γ₀`, `H(·,1)=γ₁`, closure `H(0,s)=H(1,s)`, avoidance of `z₀`, differentiability in `t` on all of `Ioo 0 1` for every `s`, continuity of the `t`-derivative on the full open product `Ioo 0 1 ×ˢ Icc 0 1`, and a global uniform `t`-derivative bound `M`.
- **How**: Direct definitional `∃ H, ... ∧ ...` packaging eight conjuncts. No proof body.
- **Hypotheses**: None (definition).
- **Uses from project**: [].
- **Used by**: `ClosedCurvesHomotopicAvoiding.toPiecewise`.
- **Visibility**: public (def).
- **Lines**: 71–88.
- **Notes**: Strictly stronger than `PiecewiseCurvesHomotopicAvoiding` — equivalent to the latter with `P = ∅`.

### `theorem ClosedCurvesHomotopicAvoiding.toPiecewise`
- **Type**: `{γ₀ γ₁ : ℝ → ℂ} {z₀ : ℂ} (h : ClosedCurvesHomotopicAvoiding γ₀ γ₁ z₀) : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ ∅`
- **What**: Conversion: a smooth closed homotopy is a piecewise C¹ closed homotopy with empty partition.
- **How**: Destructures the smooth homotopy data, then `refine`s the 9-tuple of the piecewise version reusing each component verbatim, except (i) the partition-free differentiability is supplied by ignoring the (vacuous) `t ∉ ∅` hypothesis and applying `hdiff`, and (ii) the per-subinterval derivative continuity is obtained via `hderiv_cont.mono (prod_mono hI Subset.rfl)` to restrict from `Ioo 0 1 ×ˢ Icc 0 1` to `Ioo p₁ p₂ ×ˢ Icc 0 1`.
- **Hypotheses**: One smooth closed homotopy hypothesis `h`.
- **Uses from project**: `ClosedCurvesHomotopicAvoiding`, `PiecewiseCurvesHomotopicAvoiding`.
- **Used by**: unused in file.
- **Visibility**: public (theorem).
- **Lines**: 96–105.
- **Notes**: Short proof.

### `theorem PiecewiseCurvesHomotopicAvoiding.refl`
- **Type**: `{γ : ℝ → ℂ} {z₀ : ℂ} {P : Finset ℝ} (hγ_cont : Continuous γ) (hγ_closed : γ 0 = γ 1) (hγ_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z₀) (hγ_diff : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ P → DifferentiableAt ℝ γ t) (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo (0 : ℝ) 1 → ContinuousOn (deriv γ) (Ioo p₁ p₂)) (hγ_bound : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ M) : PiecewiseCurvesHomotopicAvoiding γ γ z₀ P`
- **What**: Reflexivity: every piecewise C¹ closed curve avoiding `z₀` is homotopic (with breakpoints `P`) to itself.
- **How**: Builds the constant-in-`s` homotopy `H(t,s) = γ t`. Continuity from `hγ_cont.comp continuous_fst`. Boundary identities by `rfl`. Avoidance, differentiability, and bound conditions delegate to the corresponding hypotheses applied at `(t, _)`. The derivative-continuity case uses `ContinuousOn.congr` to identify `deriv (fun t' => γ t') q.1` with `deriv γ q.1` after composing with `continuousOn_fst`.
- **Hypotheses**: γ continuous; γ closed (`γ 0 = γ 1`); γ avoids `z₀` on `[0,1]`; γ differentiable in `Ioo 0 1 \ P`; piecewise derivative continuity on each partition-free sub-interval `Ioo p₁ p₂ ⊆ Ioo 0 1`; uniform bound on `‖deriv γ‖` over `[0,1]`.
- **Uses from project**: `PiecewiseCurvesHomotopicAvoiding`.
- **Used by**: unused in file.
- **Visibility**: public (theorem).
- **Lines**: 112–134.
- **Notes**: 23-line proof; the only nontrivial step is the `ContinuousOn.congr` for the `deriv` clause.

### `lemma one_sub_mem_Icc`
- **Type**: `{s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 - s ∈ Icc (0 : ℝ) 1`
- **What**: If `s ∈ [0,1]` then `1 - s ∈ [0,1]` — the reflection in the midpoint preserves the interval.
- **How**: Anonymous-constructor `⟨linarith [hs.2], linarith [hs.1]⟩` for the two inequalities `0 ≤ 1-s` and `1-s ≤ 1`.
- **Hypotheses**: `s ∈ Icc 0 1`.
- **Uses from project**: [].
- **Used by**: `PiecewiseCurvesHomotopicAvoiding.symm` (four call sites).
- **Visibility**: `private`.
- **Lines**: 138–139.
- **Notes**: Helper for symmetry; could be replaced by `Set.symm_mem_Icc_iff` style lemma but kept local.

### `theorem PiecewiseCurvesHomotopicAvoiding.symm`
- **Type**: `{γ₀ γ₁ : ℝ → ℂ} {z₀ : ℂ} {P : Finset ℝ} (h : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ P) : PiecewiseCurvesHomotopicAvoiding γ₁ γ₀ z₀ P`
- **What**: Symmetry: if `γ₀` is piecewise homotopic to `γ₁` (avoiding `z₀`, partition `P`), then `γ₁` is piecewise homotopic to `γ₀`.
- **How**: Reverses the homotopy parameter: define `H'(t,s) = H(t, 1-s)`. Continuity from `continuous_fst.prodMk (continuous_const.sub continuous_snd)`. Boundary at `s=0` gives `H(·,1)=γ₁` after `sub_zero`; boundary at `s=1` gives `H(·,0)=γ₀` after `sub_self`. Closure, avoidance, differentiability, and uniform bound all transfer via `one_sub_mem_Icc`. The derivative continuity clause is the only delicate part: introduces `φ : ℝ × ℝ → ℝ × ℝ, (t,s) ↦ (t, 1-s)`, shows `φ` maps `Ioo p₁ p₂ ×ˢ Icc 0 1` into itself via `one_sub_mem_Icc`, observes `deriv (fun t' => H (t', 1-q.2)) q.1 = (deriv-component-of-original) ∘ φ` pointwise (by `rfl`), and concludes via `ContinuousOn.congr` and `hderiv_cont.comp hφ_cont.continuousOn hφ_maps`.
- **Hypotheses**: One piecewise homotopy hypothesis `h`.
- **Uses from project**: `PiecewiseCurvesHomotopicAvoiding`, `one_sub_mem_Icc`.
- **Used by**: unused in file.
- **Visibility**: public (theorem).
- **Lines**: 143–176.
- **Notes**: ~34-line proof. Uses `let φ` for the reflection map. No `sorry`.

### `theorem homotopy_uniform_avoidance`
- **Type**: `(H : ℝ × ℝ → ℂ) (z₀ : ℂ) (hH_cont : Continuous H) (hH_avoid : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀) : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, δ ≤ ‖H (t, s) - z₀‖`
- **What**: Compactness gives a uniform positive distance: if `H` is continuous on `[0,1]²` and never equals `z₀`, then there exists `δ > 0` with `‖H(t,s) - z₀‖ ≥ δ` for all `(t,s) ∈ [0,1]²`.
- **How**: Forms the image `H '' ([0,1] ×ˢ [0,1])`. Image is compact via `(isCompact_Icc.prod isCompact_Icc).image hH_cont`, nonempty (contains `H(0,0)`), and `z₀ ∉ image` from the avoidance hypothesis. Applies `IsCompact.isClosed.notMem_iff_infDist_pos` to extract `δ := Metric.infDist z₀ (image) > 0`. Then for each `(t,s)`, `H(t,s) ∈ image`, so `Metric.infDist_le_dist_of_mem` gives `δ ≤ dist z₀ (H(t,s)) = ‖H(t,s) - z₀‖` (via `Complex.dist_eq` and `norm_sub_rev`).
- **Hypotheses**: `H` continuous on `ℝ × ℝ`; `H` avoids `z₀` on `[0,1] × [0,1]`.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public (theorem).
- **Lines**: 185–202.
- **Notes**: 18-line proof. Uses `Metric.infDist`, `IsCompact.isClosed.notMem_iff_infDist_pos`, `Complex.dist_eq`, `norm_sub_rev`. No `sorry`, no `axiom`.

## File Summary

HomotopyDefs.lean introduces the `[0,1]`-specialised homotopy infrastructure used by the modular-forms project: two `Prop`-valued definitions `PiecewiseCurvesHomotopicAvoiding` (piecewise C¹ with finite breakpoint set `P`) and `ClosedCurvesHomotopicAvoiding` (smooth, no partition), each packaging continuity, boundary conditions, closure, avoidance of a marked point `z₀`, differentiability in the curve parameter, continuity of that derivative on partition-free sub-rectangles, and a uniform derivative bound. The four supporting theorems are: `ClosedCurvesHomotopicAvoiding.toPiecewise` (smooth ⇒ piecewise with `P = ∅`), `PiecewiseCurvesHomotopicAvoiding.refl` (constant homotopy for self-homotopy), `PiecewiseCurvesHomotopicAvoiding.symm` (reflect `s ↦ 1-s`), and `homotopy_uniform_avoidance` (compactness gives `δ > 0` with `‖H - z₀‖ ≥ δ` on `[0,1]²`). One private helper `one_sub_mem_Icc` services the symmetry proof. The design note in the header explicitly contrasts these `[0,1]` versions with the earlier `Homotopy/Integrality.lean` versions over arbitrary `[a,b]`. The whole file is `noncomputable section`. No `sorry`, no `axiom`, no `set_option`, no `native_decide`. Total: 2 definitions, 4 theorems, 1 private lemma.
