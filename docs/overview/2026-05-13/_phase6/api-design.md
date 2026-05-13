# Phase 6: API Design Review

Scan of ~180 ForMathlib inventory files for missing helper lemmas, simp/ext/fun_prop tags, instances, and ergonomic combinators. Findings are grounded in repeated "How"-field patterns and explicit `Uses-from-project` cross-references.

## A. Missing helper lemmas (would simplify multiple proofs)

### A1. `cpvIntegrandOn_eq_singleton_of_far` — singleton form already exists; missing `_subset_smaller` variant
- **Locations using the pattern manually**: HW33Bridge (`cpvIntegrandOn_singleton_eq_contour_of_far`), MultipointPV (`cpvIntegrandOn_subset_eq`), HW-ExitTimeExcision (multiple ε-cases), HungerbuhlerWasem (`cpvIntegrandOn_eq_indicator_compl`).
- **Count**: ≥ 5 distinct "rewrite cpvIntegrandOn on a subset of S to a smaller subset" call sites.
- **Proposal**: `cpvIntegrandOn_anti : S ⊆ T → (∀ s ∈ T \ S, ε < ‖γ t - s‖) → cpvIntegrandOn T f γ ε t = cpvIntegrandOn S f γ ε t`. (Generalizes both subset and singleton/empty special cases now duplicated.)
- **Impact**: Eliminates duplicated `split_ifs ; push_neg ; ring`/`norm_num` reasoning in `Crossing.lean`, `MultipointPV.lean`, `HW33Bridge.lean`.

### A2. `Finset.IsConsecutive`-API completeness (missing partition-iteration lemmas)
- **Locations**: `PaperPwC1Immersion.lean` has `intervalIntegrable_of_consecutive_pieces` and `lipschitzOnWith_of_consecutive_pieces`, each ≥30 lines, both implementing the *same* strong-induction-on-consecutive-pairs schema.
- **Proposal**:
  - `Finset.IsConsecutive.left_mem`, `_right_mem`, `_lt` (projection lemmas — currently re-destructed via `obtain` in every callsite).
  - `Finset.consecutive_induction : ∀ {motive : ℝ → Prop} (s : Finset ℝ), {a b : ℝ} → a ∈ s → b ∈ s → a ≤ b → (P a) → (∀ p q, s.IsConsecutive p q → P p → P q) → P b` — would replace both ≥30-line strong-inductions with a 5-line call. Universal pattern: every "lift a piece-wise property to global property" lemma re-implements this.
- **Impact**: Two long proofs in `PaperPwC1Immersion.lean` collapse; future similar lemmas (e.g. `contDiffOn_global_of_consecutive_pieces`) become one-liners.

### A3. `eventually_off_partition` / `partition_isolated` consolidation
- **Locations**: PVChain-Helpers, ResidueSide, WN-Proposition2_2 (3 separate `Finset.toFinite ↑P |>.isClosed.compl` + `IsOpen.mem_nhds` arguments).
- **Proposal**: `Finset.compl_eventually_at_of_not_mem (P : Finset ℝ) (t : ℝ) (ht : t ∉ P) : ∀ᶠ s in 𝓝 t, s ∉ P` (and `nhdsWithin` variants for `𝓝[>] t`, `𝓝[<] t`).
- **Count**: ≥ 4 separate ad-hoc constructions of this filter membership.
- **Impact**: Removes a 3-line idiom in every off-partition argument.

### A4. `Tendsto.const_add_const_compose` (filter shifts)
- **Locations**: `PaperPwC1ImmersionInvariance.lean` defines **four** private lemmas (`tendsto_add_const_nhdsGT/_nhdsLT`, `tendsto_sub_const_nhdsGT/_nhdsLT`) that all establish `Tendsto (·+c) (𝓝[>] x) (𝓝[>] (x+c))` and variants. These should be mathlib API or at least file-local single lemmas, not four copies.
- **Proposal**: `Filter.tendsto_const_add_nhdsLT/GT`, or generalize via existing `nhdsWithin_*` shift lemmas.
- **Impact**: 4 lemmas → 1 lemma (or use existing mathlib).

### A5. `principalPartSum_rest_analyticAt_at_s` cross-file duplication
- **Locations**: `HW33LaurentPolarPart.lean` (`principalPartSum_rest_analyticAt_at_s`, private), `PrincipalPart.lean` (`principalPartSum_rest_analyticAt`, private), `HungerbuhlerWasem.lean` (inline). Same proof: filter the `s`-pole out, sum is analytic at `s` because each `(z - t)⁻¹` is.
- **Proposal**: Make `PrincipalPart.principalPartSum_rest_analyticAt` `public`, drop the two duplicates.
- **Impact**: -2 lemmas, no proof obligations.

### A6. `Path.cyclicShift` deriv-eventually-eq lemmas
- **Locations**: `PaperPwC1ImmersionInvariance.lean` has **four** private lemmas `deriv_cyclicShift_eventuallyEq_left/right_no_wrap/wrap`, each ≥ 15 lines, each handling one of the 4 cases (left/right × wrap/no-wrap).
- **Proposal**: Unify via one lemma `Path.cyclicShift_deriv_eventuallyEq : ∀ᶠ t in 𝓝 t₀, deriv γ.cyclicShift t = deriv γ (...)` using the periodic extension API. (Currently the case split is replicated.)
- **Impact**: 4 lemmas → 1, ~60 lines saved.

### A7. `HasCauchyPV`-`HasCauchyPVOn` singleton bridge already exists; missing `cauchyPV_eq_cauchyPVOn_singleton`
- **Locations**: `MultipointPV.hasCauchyPVOn_singleton_of_hasCauchyPV` and `hasCauchyPV_of_hasCauchyPVOn_singleton`. The `cauchyPV f γ z₀ = cauchyPVOn {z₀} f γ` value equality is not stated.
- **Proposal**: `cauchyPV_eq_cauchyPVOn_singleton : cauchyPV f γ z₀ = cauchyPVOn {z₀} f γ` and `Tendsto`-flavoured variant.
- **Impact**: Cleaner unification across HW33-* files that switch back and forth.

### A8. `IsFlatOfOrder` weakening lemmas (missing `_succ`, `_add`)
- **Status now**: `IsFlatOfOrder.of_le` exists; no `_zero`, `_one` constructors are part of the API; `isFlatOfOrder_zero` and `isFlatOfOrder_one` are standalone theorems but not exposed as `IsFlatOfOrder.zero`/`.one` dot-notation.
- **Proposal**: rename `isFlatOfOrder_zero` to `IsFlatOfOrder.zero`, `isFlatOfOrder_one` to `IsFlatOfOrder.one` for dot-notation accessibility; consider `IsFlatOfOrder.succ_of_*` and `IsFlatOfOrder.congr` (replace γ by an eventually-equal function — the manual one-sided argument in `ClosedPwC1Immersion.isFlatOfOrder_of_eventuallyEq_shift` shows this gap).
- **Impact**: Caller code becomes `(hcont.continuousAt).isFlatOfOrder_zero` instead of `isFlatOfOrder_zero _ _ hcont.continuousAt`.

### A9. `SatisfiesConditionA'.weaken_subset` / `SatisfiesConditionB.weaken_subset`
- **Status**: Currently only `SatisfiesConditionA'.of_le_poleOrder` exists. There is no `SatisfiesConditionA' (γ : PwC1Immersion x y) f S₁ p → S₂ ⊆ S₁ → SatisfiesConditionA' γ f S₂ p`.
- **Locations**: Implicit in `hw_3_3_*_paper` variants — they all assume the conditions over the same `S`. Future generalizations (e.g. excising a known-uncrossed subset) would need this.
- **Proposal**: `SatisfiesConditionA'.mono` and `SatisfiesConditionB.mono` (in the `S` parameter).

### A10. `IsNullHomologous`-style monotonicity in the open set
- **Status**: `IsNullHomologous.mono` exists per inventory (NullHomologous.md line 2). Good. But its dual — *image-only* invariance under reparametrization — is missing.
- **Locations**: `PaperPwC1ImmersionInvariance.isNullHomologous_cyclicShift` re-establishes it manually using `image_subset`. Generalizing to "any reparametrization with same image" would unify several similar cyclicShift bookkeeping lemmas (`cyclicShift_image_subset`, etc.).
- **Proposal**: `IsNullHomologous.of_image_eq` (replace γ with any closed PwC1Immersion sharing image and winding behavior).

## B. Missing @[simp] lemmas

### B1. `cpvIntegrand_zero_fun` / `cpvIntegrandOn_zero_fun`
- **Pattern**: `cpvIntegrand (fun _ => 0) γ z₀ ε t = 0` — required in `HasCauchyPV.zero_fun` (Crossing.lean) and induction bases; proven inline by `split_ifs <;> simp`.
- **Locations**: ≥ 3 (Crossing, MultipointPV, MultiCrossingCPV).

### B2. `PolarPartDecomposition` field projections lack `@[simp]`
- `polarPart_eq`, `residue_eq`, `decomp` are stated but not tagged. Many callers do `simp only [decomp.polarPart_eq]` to unfold the polar part.
- **Locations**: HW33Closed, HW33HigherOrderC3/C4, HW-SectorCancellation, MultiPoleDCT (all do this unfold step manually).

### B3. `laurentPolarPartAt_uncrossed` / `_eq_data` simp tags
- File `LaurentExtraction.md` lists `laurentPolarPartAt_uncrossed` and `laurentPolarOrderAt_uncrossed` as private lemmas. Both are pure `if_neg` rewrites; they should be public `@[simp]` rules. Currently every caller does `simp [laurentPolarPartAt, h_not_cross]`.
- **Locations**: ≥ 4 occurrences across HW33LaurentPolarPart.

### B4. `extendedPath_eq` / `apply_zero` / `apply_one` are already `@[simp]` — good. But:
- `Path.cyclicShift_apply` (in PaperPwC1Immersion) is *not* tagged `@[simp]`; should be.
- `cyclicShiftFun_zero` / `_one` are tagged with `omit` annotations but unclear if `@[simp]` — should be promoted to simp lemmas (zero/one endpoint values are canonical simp targets).

### B5. `PwC1Immersion.deriv_ne_zero` projection lacks simp
- Used heavily as `γ.deriv_ne_zero t ht hnp` in raw form. A `@[simp]` rewriting `γ.toPiecewiseC1Path.deriv_ne_zero` directly would help.

### B6. `cpvIntegrandOn_empty` is **not** `@[simp]`-tagged though it has the perfect simp form (`cpvIntegrandOn ∅ f γ ε t = f (γ t) * deriv γ t`).

### B7. `Finset.IsConsecutive` projections
- `IsConsecutive` is a 4-conjunction. Callers repeatedly destructure via `obtain ⟨_, _, _, _⟩`. Should expose `IsConsecutive.mem_left`, `IsConsecutive.mem_right`, `IsConsecutive.lt`, `IsConsecutive.not_mem_Ioo` as `@[simp]` and use dot notation.

### B8. `IsCrossed` `if_pos` / `if_neg` reduction
- `crossingParam`, `laurentPolarPartAt`, `laurentAnalyticPartAt` are all defined as `if h : IsCrossed γ s then ... else 0`. The `_uncrossed` simp lemma exists in only one form. We need all `_uncrossed` and `_of_crossed` variants tagged consistently.

## C. Missing instances

### C1. `FunLike (PiecewiseC1Path x y) ℝ E` (currently only `CoeFun`)
- **Now**: Two separate `CoeFun` instances on `PiecewiseC1Path` and `PwC1Immersion` (both via `extendedPath`/`toPath.extend`). 
- **Benefit**: A `FunLike` instance would provide `DFunLike.ext`, `coe_inj`, and auto-elaboration of `γ` against function-expecting Mathlib lemmas (`ContinuousMap.coe_..` style). Currently 295+ occurrences of `γ.toPath.extend`/`γ.toPiecewiseC1Path.toPath.extend` show this gap.

### C2. `Path.cyclicShift` as `Path` constructor
- **Now**: `Path.cyclicShift` returns a `Path` but `mk_apply` / extend lemmas need to be re-derived for it.
- **Benefit**: An instance/simp set making the extend-of-cyclicShift = cyclicShiftFun automatic at term level.

### C3. `PolarPartDecomposition`: no `Inhabited` / `Zero` / `Subsingleton` instances
- For the trivial `f = 0` case or empty `S`, no canonical instance exists; callers build manually.

### C4. `ClosedPwC1Curve` / `ClosedPwC1Immersion` coercion to `PiecewiseC1Path`
- Currently mediated by `.toPiecewiseC1Path` (built via `ClosedPwC1Curve.toPiecewiseC1Path`). Should be a `Coe` instance so `γ : PiecewiseC1Path 0 0` works directly without explicit projection.
- **Evidence**: Every HW33Paper, HW33Tight, HW33-related call passes `γ.toPwC1Immersion.toPiecewiseC1Path` explicitly — 50+ occurrences.

### C5. `ContinuousMapClass (PiecewiseC1Path x y) ℝ E`
- Every callsite re-derives continuity via `γ.continuous`. A `ContinuousMapClass` instance + `Continuous.foo` lemmas would integrate with `fun_prop`.

## D. Missing @[fun_prop] tags

Every `Continuous`/`Differentiable` lemma in the project is callable but not `fun_prop`-discoverable. None of the inventory files mention `@[fun_prop]` (grep returned zero).

Candidates that should be tagged `@[fun_prop]`:
- `PiecewiseC1Path.continuous`
- `PwC1Immersion.continuous`
- `ClosedPwC1Curve.continuous`
- `ClosedPwC1Curve.lipschitzWith_extend` (via `Continuous.lipschitzWith_extend` corollary)
- `Path.cyclicShift_apply` / `Continuous.cyclicShiftFun`
- `principalPartSum_differentiableOn`, `principalPartSum_differentiableAt`
- `principalPartSum_analyticAt`, `principalPartSum_meromorphicAt`
- `laurentPolarPartAt_differentiableAt` (and the `higherOrder` variant)
- `laurentHigherOrderPolar_differentiableAt`, `laurentHolomorphicRemainder_differentiableOn`
- `PolarPartDecomposition.analyticRemainder_diff`
- `cpvIntegrandOn` integrability lemmas (`cpvIntegrandOn_diff_intervalIntegrable`, `cpvIntegrandOn_polarPart_intervalIntegrable`).

This would replace lots of explicit `Differentiable.fun_sum`/`differentiableAt_const.div` reasoning with a single `fun_prop`.

## E. Missing @[ext] lemmas

Structures that look extension-worthy:
- **`PolarPartDecomposition`** — bundles 7 fields. Should have `@[ext]` so two decompositions with same `polarPart`, `order`, `coeff`, `analyticRemainder` (and matching axioms) are equal. Currently zero callers can rewrite "we have two decompositions, they agree on data ⟹ equal."
- **`SingleCrossingData`** — 13 fields, no ext. (Inventory `SingleCrossing.md`.)
- **`PerPoleCrossData`** / **`MultiPoleCrossData`** — both bundled records, no ext.
- **`AsymmetricSingleCrossingData`** / **`DerivedAsymmetricCutoffs`** — same.
- **`IsNullHomologous`** — Prop-valued, but two fields; `@[ext]` for *propositional* equality (irrelevant since Prop, but useful for `IsNullHomologous` *structure* matching).
- **`ClosedPwC1Curve`** / **`ClosedPwC1Immersion`** — partition+contDiffOn fields. `@[ext]` would let two curves with same partition + `toPath` be identified.
- **`PiecewiseC1Path`** / **`PwC1Immersion`** — same situation.

## F. Top 15 API additions by impact

| # | Name | Signature | Simplifies |
|---|------|-----------|------------|
| 1 | `Finset.consecutive_induction` | `{P : ℝ → Prop} → ∀ s : Finset ℝ, ∀ a b ∈ s, a ≤ b → P a → (∀ p q, s.IsConsecutive p q → P p → P q) → P b` | **2 large proofs** (`intervalIntegrable_of_consecutive_pieces`, `lipschitzOnWith_of_consecutive_pieces`) both >30 lines, plus future similar lemmas; foundational |
| 2 | `@[ext] structure PolarPartDecomposition` + `Coe ClosedPwC1Immersion PiecewiseC1Path` | structural | All HW33-* files pass `γ.toPwC1Immersion.toPiecewiseC1Path` >50 times |
| 3 | `cpvIntegrandOn_anti` | `S ⊆ T → (∀ s ∈ T \ S, ε < ‖γ t - s‖) → cpvIntegrandOn T = cpvIntegrandOn S` (pointwise) | Crossing, MultipointPV, HW33Bridge, HW-ExitTimeExcision, HungerbuhlerWasem ≥ 5 callers |
| 4 | `@[fun_prop]` annotations across all CPV/Diff/Cont lemmas | none (annotation only) | Replaces explicit Continuous/Differentiable proof scripts in 50+ proofs |
| 5 | `IsFlatOfOrder.congr` | `IsFlatOfOrder γ₁ t₀ n → γ₁ =ᶠ[𝓝 t₀] γ₂ → IsFlatOfOrder γ₂ t₀ n` | `isFlatOfOrder_of_eventuallyEq_shift` (PaperPwC1ImmersionInvariance.lean) and likely 2+ more |
| 6 | `Filter.tendsto_const_add_nhdsLT/GT` (mathlib-style) | `Tendsto (· + c) (𝓝[<] x) (𝓝[<] (x+c))` | Replaces 4 private lemmas in PaperPwC1ImmersionInvariance |
| 7 | `Finset.IsConsecutive.{mem_left,mem_right,lt,not_mem_Ioo}` projections + dot notation | trivial | Every consecutive-pair use destructures manually (~15+ sites) |
| 8 | `cpvIntegrandOn_empty` / `cpvIntegrandOn_zero_fun` tagged `@[simp]` | trivial | HasCauchyPVOn.zero_fun, finset_sum induction bases (~5 sites) |
| 9 | `Path.cyclicShift_deriv_eventuallyEq` unified lemma | `Tendsto`/`EventuallyEq` joint statement | Collapses 4 private case-split lemmas in PaperPwC1ImmersionInvariance |
| 10 | `principalPartSum_rest_analyticAt` made public | promotion | Removes 2 duplicate private copies (HW33LaurentPolarPart, HungerbuhlerWasem) |
| 11 | `SatisfiesConditionA'.mono`, `SatisfiesConditionB.mono` (in `S`) | `S₂ ⊆ S₁ → Sat… γ f S₁ p → Sat… γ f S₂ p` | Enables excision-style HW33 proofs (currently inaccessible) |
| 12 | `IsFlatOfOrder.zero`, `.one` (dot-notation aliases) | rename + alias | Slight ergonomic gain across ~10 call sites |
| 13 | `FunLike (PiecewiseC1Path x y) ℝ E` instance | instance | 295+ occurrences of `γ.toPath.extend` could shrink to `γ t` (currently mediated via `CoeFun` only on direct `γ`) |
| 14 | `@[simp]` lemmas for `laurentPolarPartAt_uncrossed`, `laurentPolarOrderAt_uncrossed`, `laurentAnalyticPartAt_uncrossed` (public + tagged) | promotion + tagging | LaurentExtraction has 5+ inline `simp [laurentX, h_not_cross]` calls |
| 15 | `cauchyPV_eq_cauchyPVOn_singleton` value-level bridge | `cauchyPV f γ z₀ = cauchyPVOn {z₀} f γ` | Cleans HW33-* files that convert between forms repeatedly |

## Notes on what's already well-designed

- `CauchyPrincipalValue.lean` API: `_of_gt`/`_of_le`/`_empty` simp set is good, mirrors `MultipointPV` API; main gap is the `_anti`/`_zero_fun` simp lemmas.
- `HasSimplePoleAt` has `.add/.sub/.const_mul/.finset_sum` — well-rounded combinators.
- `residue_*` linearity is well-developed in `ResidueLinearity.lean`.
- `PiecewiseC1Path.contourIntegral_{neg,add,smul,zero,sub,finset_sum}` is fully linearized.
- `HasCauchyPVOn.{neg,smul,add,sub,zero_fun,finset_sum}` similarly complete.

The biggest gaps are: (i) **partition iteration** (no `Finset.consecutive_induction`), (ii) **coercion ergonomics** (`ClosedPwC1Curve` → `PiecewiseC1Path` chain requires 2-3 manual projections), and (iii) **`fun_prop` integration** (project has zero `@[fun_prop]` annotations despite many fact-shaped Differentiable/Continuous lemmas).
