# ClassicalCPV.lean Inventory

### `structure PiecewiseC1Curve`
- **Type**: `structure PiecewiseC1Curve where toFun : ℝ → ℂ; a : ℝ; b : ℝ; hab : a < b; partition : Finset ℝ; partition_subset : ↑partition ⊆ Icc a b; endpoints_in_partition : a ∈ partition ∧ b ∈ partition; continuous_toFun : ContinuousOn toFun (Icc a b); smooth_off_partition : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ toFun t; deriv_continuous_off_partition : ∀ t ∈ Ioo a b, t ∉ partition → ContinuousAt (deriv toFun) t`
- **What**: A piecewise C¹ curve `γ : [a, b] → ℂ`: a continuous function with a finite partition (including endpoints) such that `γ` is C¹ on each subinterval between adjacent partition points.
- **How**: Structure declaration with seven fields.
- **Hypotheses**: implicit in the structure.
- **Uses from project**: []
- **Used by**: `instance : CoeFun PiecewiseC1Curve _`, `PiecewiseC1Curve.IsClosed`, `PiecewiseC1Immersion`.
- **Visibility**: public (`structure`).
- **Lines**: 30-41.
- **Notes**: Mirrors the Hungerbühler–Wasem definition; explicitly forces `a, b ∈ partition`.

### `instance : CoeFun PiecewiseC1Curve fun _ => ℝ → ℂ`
- **Type**: `CoeFun PiecewiseC1Curve fun _ => ℝ → ℂ`
- **What**: Function coercion: `(γ : ℝ → ℂ)` returns `γ.toFun`.
- **How**: `where coe := PiecewiseC1Curve.toFun`.
- **Hypotheses**: none.
- **Uses from project**: `PiecewiseC1Curve` (this file).
- **Used by**: (implicit through coercion in downstream definitions).
- **Visibility**: public (`instance`).
- **Lines**: 43-44.
- **Notes**: Enables `γ t` syntax.

### `def PiecewiseC1Curve.IsClosed`
- **Type**: `(γ : PiecewiseC1Curve) : Prop`
- **What**: `γ` is a closed curve, i.e. `γ.toFun γ.a = γ.toFun γ.b`.
- **How**: Direct equality definition.
- **Hypotheses**: none (a property).
- **Uses from project**: `PiecewiseC1Curve` (this file).
- **Used by**: (none in this file; intended for downstream).
- **Visibility**: public (`def`).
- **Lines**: 47-48.
- **Notes**: Distinct from `_root_.IsClosed` (set-theoretic closedness); namespaced via `PiecewiseC1Curve`.

### `structure PiecewiseC1Immersion`
- **Type**: `structure PiecewiseC1Immersion extends PiecewiseC1Curve where deriv_ne_zero : ∀ t ∈ Icc a b, t ∉ partition → deriv toFun t ≠ 0; left_deriv_limit : ∀ p ∈ partition, a < p → ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toFun) (𝓝[<] p) (𝓝 L); right_deriv_limit : ∀ p ∈ partition, p < b → ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv toFun) (𝓝[>] p) (𝓝 L)`
- **What**: A piecewise C¹ curve which is additionally an immersion: nonzero derivative on smooth intervals, and the derivative has nonzero one-sided limits at every interior partition point.
- **How**: Structure extending `PiecewiseC1Curve` with three additional fields.
- **Hypotheses**: implicit in the structure.
- **Uses from project**: `PiecewiseC1Curve` (this file).
- **Used by**: (no in-file user; intended downstream).
- **Visibility**: public (`structure`).
- **Lines**: 51-56.
- **Notes**: Generalises a smooth immersion to the piecewise setting.

### `def cauchyPrincipalValueIntegrand'`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ`
- **What**: The Cauchy principal value integrand at cutoff `ε`: `f(γ t) · γ'(t)` if `‖γ t - z₀‖ > ε`, else `0`.
- **How**: `if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `cauchyPrincipalValueIntegrand'_of_gt`, `cauchyPrincipalValueIntegrand'_of_le`.
- **Visibility**: public.
- **Lines**: 59-61.
- **Notes**: Helper integrand for the principal value.

### `theorem cauchyPrincipalValueIntegrand'_of_gt`
- **Type**: `{f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ} (h : ε < ‖γ t - z₀‖) : cauchyPrincipalValueIntegrand' f γ z₀ ε t = f (γ t) * deriv γ t`
- **What**: Evaluation rule for the integrand when the cutoff is satisfied.
- **How**: `simp only [cauchyPrincipalValueIntegrand', if_pos h]`.
- **Hypotheses**: `ε < ‖γ t - z₀‖`.
- **Uses from project**: `cauchyPrincipalValueIntegrand'` (this file).
- **Used by**: (no in-file user).
- **Visibility**: public, `@[simp]`.
- **Lines**: 64-67.
- **Notes**: Tagged `@[simp]` for downstream automation.

### `theorem cauchyPrincipalValueIntegrand'_of_le`
- **Type**: `{f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ} (h : ‖γ t - z₀‖ ≤ ε) : cauchyPrincipalValueIntegrand' f γ z₀ ε t = 0`
- **What**: Evaluation rule for the integrand when the cutoff is not satisfied.
- **How**: `simp only [cauchyPrincipalValueIntegrand', if_neg (not_lt.mpr h)]`.
- **Hypotheses**: `‖γ t - z₀‖ ≤ ε`.
- **Uses from project**: `cauchyPrincipalValueIntegrand'` (this file).
- **Used by**: (no in-file user).
- **Visibility**: public, `@[simp]`.
- **Lines**: 70-73.
- **Notes**: Companion `@[simp]` rule for the `else` branch.

### `def cauchyPrincipalValue'`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ`
- **What**: Cauchy principal value `PV ∮_γ f(z) dz`, defined as the `limUnder` of the integral over `[a, b]` of the cutoff integrand as `ε → 0⁺`.
- **How**: `limUnder (𝓝[>] 0) fun ε => ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `generalizedWindingNumber'`, `CauchyPrincipalValueExists'`.
- **Visibility**: public.
- **Lines**: 76-78.
- **Notes**: The signature inlines the conditional rather than reusing `cauchyPrincipalValueIntegrand'`.

### `def CauchyPrincipalValueExists'`
- **Type**: `(f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop`
- **What**: Asserts that the principal value limit actually converges, i.e. there exists `L : ℂ` with the cutoff integrals tending to `L` as `ε → 0⁺`.
- **How**: `∃ L : ℂ, Tendsto (fun ε => ∫ t in a..b, ...) (𝓝[>] 0) (𝓝 L)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: (none in this file; consumer-side predicate).
- **Visibility**: public.
- **Lines**: 81-85.
- **Notes**: Useful for upgrading `limUnder` to genuine `Tendsto`.

### `def generalizedWindingNumber'`
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℂ`
- **What**: The generalized winding number `(2πi)⁻¹ · PV ∮_γ dz/(z - z₀)`.
- **How**: `(2 * Real.pi * I)⁻¹ * cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0`.
- **Hypotheses**: none.
- **Uses from project**: `cauchyPrincipalValue'` (this file).
- **Used by**: External (downstream).
- **Visibility**: public.
- **Lines**: 88-90.
- **Notes**: General `[a, b]`-version (cf. the `[0,1]`-specialisation `generalizedWindingNumber01` in `WindingHomotopy.lean`).

### `def CurvesHomotopic`
- **Type**: `(Γ γ : ℝ → ℂ) (a b : ℝ) : Prop`
- **What**: Two curves `Γ, γ : [a,b] → ℂ` are continuously homotopic with shared endpoint behavior (`H(a, s)` and `H(b, s)` constant in `s`).
- **How**: `∃ H : ℝ × ℝ → ℂ, Continuous H ∧ (slice at 0 equals Γ) ∧ (slice at 1 equals γ) ∧ (endpoints constant in s)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: (none in this file).
- **Visibility**: public.
- **Lines**: 93-98.
- **Notes**: Endpoints fixed to `H(a,0)` and `H(b,0)` respectively.

### `def CurvesHomotopicAvoiding`
- **Type**: `(Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop`
- **What**: Homotopy of `Γ, γ` avoiding `z₀`: endpoints pinned to `z₀` (degenerate case for closed curves) and interior of every slice avoids `z₀`.
- **How**: `∃ H, Continuous H ∧ slice at 0 = Γ ∧ slice at 1 = γ ∧ (∀ s, H(a,s) = z₀ ∧ H(b,s) = z₀) ∧ (∀ t ∈ Ioo a b, ∀ s, H(t,s) ≠ z₀)`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: (none in this file).
- **Visibility**: public.
- **Lines**: 101-107.
- **Notes**: Specialised variant for winding-number purposes; the "endpoints at `z₀`" branch corresponds to a closed curve degenerated to a base point of integration.

### `private theorem aestronglyMeasurable_of_continuousOn_off_finite`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (hf_cont : ContinuousOn f ((Icc a b) \ P)) : AEStronglyMeasurable f (volume.restrict (Icc a b))`
- **What**: A function continuous on `[a, b]` minus a finite set is a.e. strongly measurable on `[a, b]`.
- **How**: Decomposes `Icc a b = (Icc a b \ P) ∪ (P ∩ Icc a b)` via `Set.inter_comm` and `Set.diff_union_inter`. Applies `aestronglyMeasurable_union_iff`; the first piece is measurable via `hf_cont.aestronglyMeasurable (measurableSet_Icc.diff (Finset.measurableSet P))`, the second has measure zero (finite intersection), reduced to `aestronglyMeasurable_zero_measure f` after `Measure.restrict_zero_set`.
- **Hypotheses**: continuity off a finite set.
- **Uses from project**: []
- **Used by**: `intervalIntegrable_of_piecewise_continuousOn_bounded`.
- **Visibility**: `private`.
- **Lines**: 109-122.
- **Notes**: Foundational measurability bridge.

### `theorem intervalIntegrable_of_piecewise_continuousOn_bounded`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} {P : Finset ℝ} (M : ℝ) (hab : a ≤ b) (hf_cont : ContinuousOn f ((Icc a b) \ P)) (hf_bound : ∀ t ∈ Icc a b, ‖f t‖ ≤ M) : IntervalIntegrable f volume a b`
- **What**: A bounded piecewise-continuous function is interval integrable.
- **How**: Constructs `IntegrableOn f (Icc a b) volume` from `aestronglyMeasurable_of_continuousOn_off_finite hf_cont` and `MeasureTheory.HasFiniteIntegral.restrict_of_bounded M` (with `Real.volume_Icc` giving `< ⊤`, and `filter_upwards [ae_restrict_mem measurableSet_Icc]` providing the pointwise bound). Then `rw [← uIcc_of_le hab]` converts to `uIcc` and concludes with `.intervalIntegrable`.
- **Hypotheses**: `a ≤ b`, piecewise continuity, uniform bound.
- **Uses from project**: `aestronglyMeasurable_of_continuousOn_off_finite` (this file).
- **Used by**: (none in this file; intended for downstream use).
- **Visibility**: public.
- **Lines**: 125-139.
- **Notes**: Standard bounded-measurable ⇒ integrable.

### `private theorem exists_min_above_in_finite_union`
- **Type**: `(P : Finset ℝ) (t b : ℝ) (ht_lt_b : t < b) : ∃ s_min : ℝ, t < s_min ∧ s_min ≤ b ∧ (∀ x ∈ Ioo t s_min, x ∉ ({b} ∪ (P : Set ℝ)))`
- **What**: Given a finite "bad" set `{b} ∪ P` and a point `t < b`, finds the smallest element of the bad set strictly above `t` (so `(t, s_min)` is bad-free) and bounds it by `b`.
- **How**: Let `S := {b} ∪ ↑P`, finite via `(Set.finite_singleton b).union (Finset.finite_toSet P)`. Restrict to `S_above := {s ∈ S | t < s}`, which is nonempty (contains `b`). Take `s_min := hS_above_finite.toFinset.min' hne`. Membership and lower-bound properties come from `Finset.min'_mem` and `Finset.min'_le` (with `Set.Finite.mem_toFinset`). The exclusion `x ∉ S` follows by `linarith [hs_min_le x ⟨hxS, hx.1⟩, hx.2]`.
- **Hypotheses**: `t < b`.
- **Uses from project**: []
- **Used by**: `hasDerivWithinAt_zero_of_deriv_zero_off_finite`.
- **Visibility**: `private`.
- **Lines**: 143-165.
- **Notes**: Finds a maximal "good" window above `t`.

### `private theorem eq_on_Ioo_of_deriv_zero`
- **Type**: `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} {a b t s_min : ℝ} (ht : t ∈ Ico a b) (ht_lt_s : t < s_min) (hf_cont : ContinuousOn f (Icc a b)) (h_diff : DifferentiableOn ℝ f (Ioo t s_min)) (h_dz : ∀ x ∈ Ioo t s_min, deriv f x = 0) (h_smin_le_b : s_min ≤ b) : ∀ x ∈ Ioo t s_min, f x = f t`
- **What**: If `f` is continuous on `[a, b]`, differentiable on `(t, s_min)`, has zero derivative there, then `f x = f t` for all `x ∈ (t, s_min)`.
- **How**: Step 1: `IsOpen.is_const_of_deriv_eq_zero isOpen_Ioo isPreconnected_Ioo h_diff h_dz` gives `f x = f y` for all `x, y ∈ (t, s_min)`. Step 2: `f x = f ((t + s_min) / 2)` (midpoint as pivot). Step 3: Promotes to `f t = f ((t + s_min) / 2)` via `ContinuousWithinAt f (Ioo t s_min) t` (from `hf_cont.continuousWithinAt` on `Ico_subset_Icc_self`) and `tendsto_nhds_unique` against the constant tendsto; the `(𝓝[Ioo t s_min] t).NeBot` instance comes from `closure_Ioo (ne_of_lt ht_lt_s)` and `mem_closure_iff_nhdsWithin_neBot`.
- **Hypotheses**: continuity, differentiability, zero derivative, geometry.
- **Uses from project**: []
- **Used by**: `hasDerivWithinAt_zero_of_deriv_zero_off_finite`.
- **Visibility**: `private`.
- **Lines**: 167-199.
- **Notes**: Proof >30 lines (~33). General `NormedAddCommGroup`/`NormedSpace ℝ` setting (more general than `ℂ`).

### `theorem hasDerivWithinAt_zero_of_deriv_zero_off_finite`
- **Type**: `{E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : ℝ → E) (a b : ℝ) (P : Finset ℝ) (_hab : a < b) (hf_cont : ContinuousOn f (Icc a b)) (hf_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ f t) (hf_deriv_zero : ∀ t ∈ Ioo a b, t ∉ P → deriv f t = 0) : ∀ t ∈ Ico a b, HasDerivWithinAt f 0 (Ici t) t`
- **What**: If `f` is continuous on `[a, b]`, differentiable off finite `P` on `(a, b)`, with zero derivative there, then `f` has zero right derivative at every point of `[a, b)`.
- **How**: For each `t ∈ Ico a b`, applies `exists_min_above_in_finite_union P t b ht.2` to get `s_min ∈ (t, b]` with `(t, s_min)` avoiding `{b} ∪ P`. Applies `eq_on_Ioo_of_deriv_zero` to conclude `f x = f t` on `(t, s_min)`. Then uses `hasDerivWithinAt_iff_tendsto_slope` and `tendsto_nhds_of_eventually_eq` against the slope `(f x - f t) / (x - t) = 0` (justified by `slope`, `h_eq x hx`, `vsub_self`, `smul_zero`); the neighborhood membership `Ioo t s_min ∈ 𝓝[Ici t \ {t}] t` is from `mem_nhdsWithin` with witness `Iio s_min`.
- **Hypotheses**: continuity, off-`P` differentiability, off-`P` zero derivative.
- **Uses from project**: `exists_min_above_in_finite_union`, `eq_on_Ioo_of_deriv_zero` (this file).
- **Used by**: (none in this file; intended for downstream).
- **Visibility**: public.
- **Lines**: 203-234.
- **Notes**: Proof ≈32 lines (just over the 30-line threshold). General `NormedAddCommGroup`/`NormedSpace ℝ` setting.

### `theorem continuousWithinAt_integral_of_dominated_piecewise`
- **Type**: `{X : Type*} [TopologicalSpace X] [FirstCountableTopology X] {F : X → ℝ → ℂ} {x₀ : X} {a b : ℝ} {S : Set X} {M : ℝ} (hab : a ≤ b) (hF_meas : ∀ x ∈ S, AEStronglyMeasurable (F x) (volume.restrict (Icc a b))) (hF_bound : ∀ x ∈ S, ∀ t ∈ Icc a b, ‖F x t‖ ≤ M) (hF_cont : ∀ᵐ t ∂volume.restrict (Icc a b), ContinuousWithinAt (fun x => F x t) S x₀) : ContinuousWithinAt (fun x => ∫ t in a..b, F x t) S x₀`
- **What**: Parametric integral continuity (dominated convergence flavor): if `F x` is a.e.-measurable, uniformly bounded by `M`, and continuous in `x` a.e.-`t`, then `∫ F x t dt` is continuous at `x₀` within `S`.
- **How**: Computes `h_uIoc_sub : Set.uIoc a b ⊆ Icc a b` from `uIoc_of_le hab` and `Ioc_subset_Icc_self`. Applies `intervalIntegral.continuousWithinAt_of_dominated_interval (bound := fun _ => M)` with four subgoals: (1) measurability (`filter_upwards [self_mem_nhdsWithin (s := S)]` + `hF_meas` + `.mono_set h_uIoc_sub`); (2) pointwise bound (same self-mem filter + `.of_forall fun t ht => hF_bound x hx t (h_uIoc_sub ht)`); (3) `intervalIntegrable_const` for the bound; (4) a.e. continuity (`MeasureTheory.ae_imp_of_ae_restrict (MeasureTheory.ae_restrict_of_ae_restrict_of_subset h_uIoc_sub hF_cont)`).
- **Hypotheses**: `a ≤ b`, measurability, uniform bound, a.e.-continuity.
- **Uses from project**: []
- **Used by**: (none in this file; intended downstream for parametric continuity of CPV-style integrals).
- **Visibility**: public.
- **Lines**: 236-254.
- **Notes**: Wraps mathlib's `intervalIntegral.continuousWithinAt_of_dominated_interval`.

## File Summary

- **Total decls**: 17 (4 structures/definitions for curve types + coercion, 4 CPV/winding definitions, 2 homotopy predicates, 2 `@[simp]` evaluation rules, 5 theorems/lemmas).
- **Key API** (used 3+ in this file): `PiecewiseC1Curve` (used by coercion instance, `IsClosed`, `PiecewiseC1Immersion` — 3 uses).
- **Unused in file**: `PiecewiseC1Curve.IsClosed`, `PiecewiseC1Immersion`, `CurvesHomotopic`, `CurvesHomotopicAvoiding`, `CauchyPrincipalValueExists'`, `cauchyPrincipalValueIntegrand'_of_gt`, `cauchyPrincipalValueIntegrand'_of_le`, `intervalIntegrable_of_piecewise_continuousOn_bounded`, `hasDerivWithinAt_zero_of_deriv_zero_off_finite`, `continuousWithinAt_integral_of_dominated_piecewise`, `generalizedWindingNumber'` — all terminal public API, expected to have only downstream consumers.
- **Sorries**: 0.
- **set_options**: none.
- **Proofs >30 lines**: `eq_on_Ioo_of_deriv_zero` (~33 lines), `hasDerivWithinAt_zero_of_deriv_zero_off_finite` (~32 lines).
- **One-paragraph file purpose**: Provides the core definitional layer for Cauchy principal value integrals and generalized winding numbers in the classical Hungerbühler–Wasem setting. Declares the `PiecewiseC1Curve` and `PiecewiseC1Immersion` structures (with explicit `partition : Finset ℝ` containing the endpoints, off-partition smoothness, continuous one-sided derivatives, and nonzero-derivative immersion conditions), the CPV integrand `cauchyPrincipalValueIntegrand'` with its `@[simp]` evaluation rules, the principal value `cauchyPrincipalValue'` (as `limUnder` of cutoff integrals), the existence predicate `CauchyPrincipalValueExists'`, and the generalized winding number `generalizedWindingNumber' := (2πi)⁻¹ · PV ∮ dz/(z - z₀)`. Adds two homotopy predicates (`CurvesHomotopic`, `CurvesHomotopicAvoiding`) and a small toolbox of integrability/derivative-vanishing lemmas (`aestronglyMeasurable_of_continuousOn_off_finite`, `intervalIntegrable_of_piecewise_continuousOn_bounded`, `eq_on_Ioo_of_deriv_zero`, `hasDerivWithinAt_zero_of_deriv_zero_off_finite`, `continuousWithinAt_integral_of_dominated_piecewise`) — the constant-on-an-interval lemma promotes pointwise zero-derivative-off-finite to a `HasDerivWithinAt 0` result on `Ici t`. All declarations are general (over `ℂ` for the CPV ones, over `NormedAddCommGroup`/`NormedSpace ℝ` for the derivative-zero results) and serve as the foundation imported by downstream homotopy-invariance and crossing-analysis files.
