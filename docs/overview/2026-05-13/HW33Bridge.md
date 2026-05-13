# HW33Bridge.lean Inventory

### `theorem cpvIntegrandOn_singleton_eq_contour_of_far`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ} {t : ℝ} (h_far : ε < ‖γ.toPath.extend t - s‖) : cpvIntegrandOn {s} f γ.toPath.extend ε t = f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: When γ(t) is far from a single pole `s` (distance > ε), the CPV integrand reduces to the ordinary contour integrand `f(γ(t)) · γ'(t)`.
- **How**: Apply `cpvIntegrandOn_of_forall_gt` with the singleton membership specialization `Finset.mem_singleton`.
- **Hypotheses**: `ε < ‖γ(t) - s‖`.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_of_forall_gt`, `PiecewiseC1Path`
- **Used by**: `cpvIntegrandOn_singleton_eq_indicator`, `integral_cpvIntegrandOn_singleton_eq_contour_left`, `integral_cpvIntegrandOn_singleton_eq_contour_right`
- **Visibility**: public (in namespace `LeanModularForms`)
- **Lines**: 56-63
- **Notes**: none

### `theorem cpvIntegrandOn_singleton_eq_zero_of_close`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ} {t : ℝ} (h_close : ‖γ.toPath.extend t - s‖ ≤ ε) : cpvIntegrandOn {s} f γ.toPath.extend ε t = 0`
- **What**: When γ(t) is within ε of `s`, the CPV integrand is zero (excision region).
- **How**: Apply `cpvIntegrandOn_of_exists_le` with the singleton witness `⟨s, Finset.mem_singleton_self s, h_close⟩`.
- **Hypotheses**: `‖γ(t) - s‖ ≤ ε`.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_of_exists_le`, `PiecewiseC1Path`
- **Used by**: `cpvIntegrandOn_singleton_eq_indicator`, `integral_cpvIntegrandOn_singleton_eq_zero_middle`
- **Visibility**: public
- **Lines**: 66-70
- **Notes**: none

### `theorem cpvIntegrandOn_singleton_eq_indicator`
- **Type**: `(γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) (ε : ℝ) (t : ℝ) : cpvIntegrandOn {s} f γ.toPath.extend ε t = ({t | ε < ‖γ.toPath.extend t - s‖}.indicator (fun t => f (γ.toPath.extend t) * deriv γ.toPath.extend t)) t`
- **What**: Pointwise identification: the singleton-CPV integrand equals the indicator of the "far from `s`" set times the contour integrand.
- **How**: `by_cases` on `ε < ‖γ(t) - s‖`; in the positive branch apply `Set.indicator_of_mem` and `cpvIntegrandOn_singleton_eq_contour_of_far`; otherwise use `Set.indicator_of_notMem`, `push Not`, and `cpvIntegrandOn_singleton_eq_zero_of_close`.
- **Hypotheses**: none.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_contour_of_far`, `cpvIntegrandOn_singleton_eq_zero_of_close`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 77-89
- **Notes**: none

### `theorem integral_cpvIntegrandOn_singleton_eq_contour_left`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α : ℝ} (hα : 0 ≤ α) (h_outside : ∀ t ∈ Ioo (0 : ℝ) α, ε < ‖γ.toPath.extend t - s‖) : ∫ t in (0 : ℝ)..α, cpvIntegrandOn {s} f γ.toPath.extend ε t = ∫ t in (0 : ℝ)..α, f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: The integral on `[0, α]` of the CPV integrand equals the ordinary contour integral, given γ is far from `s` on `(0, α)`.
- **How**: `intervalIntegral.integral_of_le hα` on both sides, convert `Ioc → Ioo` via `MeasureTheory.integral_Ioc_eq_integral_Ioo`, then `MeasureTheory.setIntegral_congr_fun` on `measurableSet_Ioo` using `cpvIntegrandOn_singleton_eq_contour_of_far` pointwise.
- **Hypotheses**: `0 ≤ α`; far-from-pole on `Ioo 0 α`.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_contour_of_far`, `PiecewiseC1Path`
- **Used by**: `cpvIntegrandOn_singleton_integral_eq_excision`
- **Visibility**: public
- **Lines**: 96-107
- **Notes**: none

### `theorem integral_cpvIntegrandOn_singleton_eq_contour_right`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε β : ℝ} (hβ : β ≤ 1) (h_outside : ∀ t ∈ Ioo β (1 : ℝ), ε < ‖γ.toPath.extend t - s‖) : ∫ t in β..(1 : ℝ), cpvIntegrandOn {s} f γ.toPath.extend ε t = ∫ t in β..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: Symmetric of the left version: integral on `[β, 1]` matches contour integral when far from `s` on `(β, 1)`.
- **How**: Same template as `_contour_left` (interval_of_le, Ioc→Ioo, setIntegral_congr_fun, far-from-pole).
- **Hypotheses**: `β ≤ 1`; far-from-pole on `Ioo β 1`.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_contour_of_far`, `PiecewiseC1Path`
- **Used by**: `cpvIntegrandOn_singleton_integral_eq_excision`
- **Visibility**: public
- **Lines**: 111-122
- **Notes**: none

### `theorem integral_cpvIntegrandOn_singleton_eq_zero_middle`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε α β : ℝ} (h_le : α ≤ β) (h_inside : ∀ t ∈ Ioo α β, ‖γ.toPath.extend t - s‖ ≤ ε) : ∫ t in α..β, cpvIntegrandOn {s} f γ.toPath.extend ε t = 0`
- **What**: Integral on the excision interval `[α, β]` vanishes when γ stays within ε of `s`.
- **How**: `intervalIntegral.integral_of_le`, convert to `Ioo`, use `setIntegral_congr_fun` rewriting the integrand to `0` via `cpvIntegrandOn_singleton_eq_zero_of_close`, then `simp` integral of zero.
- **Hypotheses**: `α ≤ β`; close-to-pole on `Ioo α β`.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_singleton_eq_zero_of_close`, `PiecewiseC1Path`
- **Used by**: `cpvIntegrandOn_singleton_integral_eq_excision`
- **Visibility**: public
- **Lines**: 126-134
- **Notes**: none

### `theorem cpvIntegrandOn_singleton_integral_eq_excision`
- **Type**: `(γ : PiecewiseC1Path x x) {s : ℂ} {f : ℂ → ℂ} {ε : ℝ} {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (h_le : α ≤ β) (h_outside_left : ...) (h_outside_right : ...) (h_inside : ...) (h_int_full : IntervalIntegrable ...) : ∫ t in (0 : ℝ)..1, cpvIntegrandOn {s} f γ.toPath.extend ε t = (∫ t in (0 : ℝ)..α, f (γ.toPath.extend t) * deriv γ.toPath.extend t) + ∫ t in β..(1 : ℝ), f (γ.toPath.extend t) * deriv γ.toPath.extend t`
- **What**: Full splitting: under the shape hypothesis (γ-far on `(0,α)`, γ-close on `(α,β)`, γ-far on `(β,1)`), the CPV integral on `[0,1]` equals the symmetric-excision sum of contour integrals on `[0,α] ∪ [β,1]`.
- **How**: 30-line proof. Build a triple split using `intervalIntegral.integral_add_adjacent_intervals` twice (after sub-integrability via `h_int_full.mono_set` and `Set.Icc_subset_Icc` on `α, β, 0, 1`). Then rewrite each piece: left via `integral_cpvIntegrandOn_singleton_eq_contour_left`, middle via `integral_cpvIntegrandOn_singleton_eq_zero_middle`, right via `integral_cpvIntegrandOn_singleton_eq_contour_right`; finish with `add_zero`. Specific lemma: `intervalIntegral.integral_add_adjacent_intervals`.
- **Hypotheses**: `0 ≤ α ≤ β ≤ 1`; far on `(0,α)`, close on `(α,β)`, far on `(β,1)`; CPV integrand interval-integrable on `[0,1]`.
- **Uses from project**: `cpvIntegrandOn`, `integral_cpvIntegrandOn_singleton_eq_contour_left`, `integral_cpvIntegrandOn_singleton_eq_zero_middle`, `integral_cpvIntegrandOn_singleton_eq_contour_right`, `PiecewiseC1Path`
- **Used by**: `hasCauchyPVOn_singleton_of_excision_tendsto`
- **Visibility**: public
- **Lines**: 139-179
- **Notes**: >30 lines proof.

### `theorem hasCauchyPVOn_singleton_of_excision_tendsto`
- **Type**: `(γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) (α β : ℝ → ℝ) (h_shape : ∀ᶠ ε in 𝓝[>] 0, ...shape...) (h_int_full : ∀ᶠ ε, IntervalIntegrable ...) (h_excision : Tendsto (fun ε => ...excision integral...) (𝓝[>] 0) (𝓝 0)) : HasCauchyPVOn {s} f γ 0`
- **What**: Bridge from "parametric symmetric-excision integral tends to 0" to `HasCauchyPVOn`. Given exit-time functions `α, β : ℝ → ℝ` and the shape/integrability/excision hypotheses, the singleton CPV integral exists and equals 0.
- **How**: `refine h_excision.congr' ?_; filter_upwards [h_shape, h_int_full] with ε ...`; apply `(cpvIntegrandOn_singleton_integral_eq_excision γ ha hb hc hd he hf h_int).symm`.
- **Hypotheses**: shape hypothesis (six conjuncts), full integrability, excision integral tendsto 0.
- **Uses from project**: `cpvIntegrandOn`, `cpvIntegrandOn_singleton_integral_eq_excision`, `HasCauchyPVOn`, `PiecewiseC1Path`
- **Used by**: `hasCauchyPVOn_singleton_of_exitTime_excision`
- **Visibility**: public
- **Lines**: 194-212
- **Notes**: none

### `theorem hasCauchyPVOn_singleton_of_exitTime_excision`
- **Type**: `(γ : PiecewiseC1Path x x) (s : ℂ) (f : ℂ → ℂ) {t₀ δMinus δPlus : ℝ} (h_shape : ∀ᶠ ε ...) (h_int_full : ∀ᶠ ε, IntervalIntegrable ...) (h_excision : Tendsto (fun ε => ...) (𝓝[>] 0) (𝓝 0)) : HasCauchyPVOn {s} f γ 0`
- **What**: Specialization of the previous bridge to `α = firstExitTimeLeft` and `β = firstExitTimeRight`.
- **How**: Forwards directly to `hasCauchyPVOn_singleton_of_excision_tendsto` with `α := firstExitTimeLeft γ t₀ δMinus s`, `β := firstExitTimeRight γ t₀ δPlus s`.
- **Hypotheses**: same shape/integrability/excision package, parametrized by exit times.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeRight`, `hasCauchyPVOn_singleton_of_excision_tendsto`, `cpvIntegrandOn`, `HasCauchyPVOn`, `PiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 219-246
- **Notes**: none

### `theorem shape_left_of_strictAntiOn`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δMinus : ℝ} (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (hδMinus : 0 < δMinus) (hγ_cont : ContinuousOn γ (Icc (t₀ - δMinus) t₀)) (hγ_anti : StrictAntiOn (fun t => ‖γ t - s‖) (Icc (t₀ - δMinus) t₀)) {δ_avoid : ℝ} (h_avoid : ∀ t ∈ Icc (0 : ℝ) (t₀ - δMinus), δ_avoid ≤ ‖γ t - s‖) {ε : ℝ} (hε_lt_avoid : ε < δ_avoid) (hε_le_max : ε ≤ ‖γ (t₀ - δMinus) - s‖) : 0 ≤ firstExitTimeLeft γ t₀ δMinus s ε ∧ ∀ t ∈ Ioo (0 : ℝ) (firstExitTimeLeft γ t₀ δMinus s ε), ε < ‖γ t - s‖`
- **What**: From local strict anti-monotonicity of `‖γ - s‖` on `[t₀ - δMinus, t₀]` plus avoidance margin on `[0, t₀ - δMinus]`, derive the left-side shape hypothesis used by the bridge: the exit time is ≥ 0 and γ stays far on `(0, exit-time)`.
- **How**: `firstExitTimeLeft_mem_Icc` gives the Icc bound; case-split `t ≤ t₀ - δMinus`: outer case uses `h_avoid` + `linarith`; inner case uses `ε_le_norm_at_firstExitTimeLeft` and `hγ_anti` + `linarith`.
- **Hypotheses**: nonneg `t₀ - δMinus`; `0 < δMinus`; continuity, strict anti-monotonicity; avoidance margin; `ε < δ_avoid`; `ε ≤ ‖γ(t₀ - δMinus) - s‖`.
- **Uses from project**: `firstExitTimeLeft`, `firstExitTimeLeft_mem_Icc`, `ε_le_norm_at_firstExitTimeLeft`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 257-276
- **Notes**: none

### `theorem shape_right_of_strictMonoOn`
- **Type**: `{γ : ℝ → ℂ} {s : ℂ} {t₀ δPlus : ℝ} (h_t₀_plus_le : t₀ + δPlus ≤ 1) (hδPlus : 0 < δPlus) (hγ_cont : ContinuousOn γ (Icc t₀ (t₀ + δPlus))) (hγ_mono : StrictMonoOn (fun t => ‖γ t - s‖) (Icc t₀ (t₀ + δPlus))) {δ_avoid : ℝ} (h_avoid : ∀ t ∈ Icc (t₀ + δPlus) (1 : ℝ), δ_avoid ≤ ‖γ t - s‖) {ε : ℝ} (hε_lt_avoid : ε < δ_avoid) (hε_le_max : ε ≤ ‖γ (t₀ + δPlus) - s‖) : firstExitTimeRight γ t₀ δPlus s ε ≤ 1 ∧ ∀ t ∈ Ioo (firstExitTimeRight γ t₀ δPlus s ε) (1 : ℝ), ε < ‖γ t - s‖`
- **What**: Symmetric of `shape_left_of_strictAntiOn`: strict monotonicity of `‖γ - s‖` on `[t₀, t₀+δPlus]` plus right avoidance margin yields the right-side shape: exit time ≤ 1, γ far on `(exit-time, 1)`.
- **How**: `firstExitTimeRight_mem_Icc` for membership; case-split `t₀ + δPlus ≤ t`: outer via `h_avoid` + `linarith`; inner via `ε_le_norm_at_firstExitTimeRight` and `hγ_mono`.
- **Hypotheses**: `t₀ + δPlus ≤ 1`; `0 < δPlus`; continuity, strict mono; avoidance; `ε < δ_avoid`; `ε ≤ ‖γ(t₀ + δPlus) - s‖`.
- **Uses from project**: `firstExitTimeRight`, `firstExitTimeRight_mem_Icc`, `ε_le_norm_at_firstExitTimeRight`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 282-301
- **Notes**: none

## File Summary

**File**: `LeanModularForms/ForMathlib/HW33Bridge.lean` (305 lines, namespace `LeanModularForms`)

Bridge between the parametric symmetric-excision Cauchy principal value form (used by `hw_theorem_3_3_odd_transverse_parametric`) and the `HasCauchyPVOn` form used elsewhere. Imports `HW33ExitTimeWrapper`. Structure:
1. **Pointwise CPV-integrand identification** for a singleton pole: far-from-pole reduces to contour integrand; close-to-pole gives zero; combined as indicator.
2. **Integral splitting**: `[0, α]` and `[β, 1]` CPV integrals equal contour integrals (under far-from-pole on `(0,α)`/`(β,1)`); middle `[α, β]` integral vanishes (under close-to-pole on `(α,β)`).
3. **Full excision identity** `cpvIntegrandOn_singleton_integral_eq_excision` combining all three.
4. **Bridge to `HasCauchyPVOn`** in generic form `hasCauchyPVOn_singleton_of_excision_tendsto` and exit-time specialization `hasCauchyPVOn_singleton_of_exitTime_excision`.
5. **Shape derivations from monotonicity**: `shape_left_of_strictAntiOn` and `shape_right_of_strictMonoOn` build the shape hypothesis from continuity + strict (anti)monotonicity of `‖γ - s‖` plus avoidance margins.

All theorems are public (in namespace `LeanModularForms`). No `sorry`, no axioms, no `set_option`.
