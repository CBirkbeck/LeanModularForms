# Project Overview — LeanModularForms/ForMathlib

**Generated**: 2026-05-13 via `/mathlib-quality:overview`
**Scope**: `LeanModularForms/ForMathlib/` (183 `.lean` files, ~132k lines)
**Method**: per-file inventory by 47 worker subagents, then 5 cross-cutting analysis phases (mathlib API audit, duplication detection, generalization analysis, API design review, junk identification).
**Supersedes**: previous PROJECT_OVERVIEW.md from 2026-03-31.

---

## Executive Summary

`ForMathlib/` is the project's "candidates-for-mathlib" library. It contains three large independently-developed threads with substantial mutual duplication: the **Hungerbühler–Wasem Theorem 3.3** formalization (split between top-level `HW33*` files and the `HungerbuhlerWasem/` subdirectory, ~30 files, ~50k lines), the **valence-formula** apparatus (`ValenceFormula/` subtree + top-level FD / boundary / winding files, ~50 files, ~25k lines), and an older **GeneralizedResidueTheory** chain (28 files, 15k lines, partly superseded but still active). A small "for-mathlib" shim layer (7 files: `UpperHalfPlane`, `SlashActions`, `AtImInfty`, `Instances`, `TrigLemmas`, `CongruenceSubgrps`, `FunctionsBoundedAtInfty`) is PR-ready and should be moved upstream.

The project compiles cleanly with **no `sorry`s in source**, only **4 files** using `set_option maxHeartbeats`, and axiom-clean main theorems (`[propext, Classical.choice, Quot.sound]`). The cross-cutting health issues are not correctness, but **structure** — there is significant duplication and missing automation that adds friction to every downstream proof.

### The seven headline findings

1. **~1620 lines of source code are entirely inert.** Seven files (`hassumunifon.lean` 1023 lines, `Bounds.lean` 340, `IsBoundedAtImInfty.lean` 78, `LevelOne.lean` 55, `Identities.lean` 40, `Petersson.lean` 136, `QExpansion.lean` 264) have their **entire body wrapped in a `/- ... -/` block comment** — the Lean parser sees them as empty. Add `CongruenceSubgroupsCopy.lean` (15-line explicit placeholder stub) and Tier-1 deletion is **8 files** for essentially no risk.

2. **Massive cross-tree duplication.** Phase 4 found **105 unify candidates** including byte-equal duplicates differing only in namespace:
   - `HW33SectorEven.lean` ≡ `HungerbuhlerWasem/SectorCancellation.lean` (one line differs: the `namespace` line; 558 vs 562 lines)
   - `FlatnessConditions.lean` ≡ `GeneralizedResidueTheory/Residue/Flatness.lean` (17 byte-equal declarations)
   - `HW33LaurentPolarPart.lean` is a **strict subset** of `HungerbuhlerWasem/LaurentExtraction.lean`
   - `HigherOrderCancel.lean` shares 17 verbatim theorems with `HungerbuhlerWasem/HigherOrderAsymptotics.lean`
   - `HW33Bridge.lean` ⊆ `HungerbuhlerWasem/ExitTimeExcision.lean` (10+ theorems)
   - `HungerbuhlerWasem.lean` redeclares ~6 things from `HW33HigherOrderAvoidance.lean`
   - **Estimated deletable: 5–6 files ≈ 2500–3000 lines.**

3. **Two parallel piecewise-C¹ chains.** `PiecewiseC1Path`/`PwC1Immersion` (on `[0,1]`) and `PiecewiseC1Curve`/`PiecewiseC1Immersion` (on `[a,b]`, in `ClassicalCPV.lean`) duplicate ~960 lines. The `'`-suffix `cauchyPrincipalValue'` / `generalizedWindingNumber'` are precomposed copies, eliminable by routing through the `[0,1]` chain via `Path.extend`.

4. **Three parallel CPV definition families.** `Residue.lean` (`cauchyPrincipalValueOn`), `CauchyPrincipalValue.lean` (`cauchyPVOn`, primary), and `ClassicalCPV.lean` (`cauchyPrincipalValue'`) — same content, three names per concept. Plus `cauchyPV`/`cauchyPVOn` are `limUnder`-defined and dead weight; project memory and downstream callers all use the `HasCauchyPV*` `Tendsto` predicates instead.

5. **Two parallel `HasSimplePoleAt` libraries** (`Residue.lean` 97 lines vs `GeneralizedResidueTheory/Residue.lean` 760 lines). The `HungerbuhlerWasem.lean` docstring explicitly flags this. **Mathlib's `meromorphicTrailingCoeffAt` + `MeromorphicAt` subsume both** and carry `@[fun_prop]`.

6. **Zero `@[fun_prop]` annotations** project-wide despite ~50+ project lemmas about `Continuous`/`Differentiable`/`MeromorphicAt` of `PiecewiseC1Path`, `principalPartSum`, `laurentPolarPartAt`, `laurentHigherOrderPolar`, `laurentHolomorphicRemainder`, `PolarPartDecomposition.analyticRemainder`. Tagging these unlocks `fun_prop` automation across the project.

7. **No structural `@[ext]` lemmas** for `PolarPartDecomposition`, `SingleCrossingData`, `PerPoleCrossData`, `AsymmetricSingleCrossingData`, `ClosedPwC1Curve`, etc. Many of these are heavily bundled records (7–13 fields); ext lets decomposition-uniqueness reasoning short-circuit.

### Top 10 concrete actions

1. **Delete 8 commented-out / placeholder files** (~1951 lines, mechanical, zero downstream impact).
2. **Delete `FlatnessConditions.lean`** (~441 lines, byte-equal duplicate).
3. **Delete `HW33SectorEven.lean`** (~558 lines, one-line-different duplicate).
4. **Delete `HW33LaurentPolarPart.lean`** (~519 lines, strict subset of `LaurentExtraction.lean`).
5. **Delete `HW33Bridge.lean`** (~305 lines, duplicates 10+ theorems of `ExitTimeExcision.lean`).
6. **Dedupe `HigherOrderCancel.lean` ↔ `HigherOrderAsymptotics.lean`** (~300 lines, 17 shared theorems).
7. **Replace `residueSimplePole`/`HasSimplePoleAt`/`poleOrderAt`** with mathlib's `meromorphicTrailingCoeffAt`/`MeromorphicAt`/`meromorphicOrderAt`.
8. **Collapse `PiecewiseC1Curve`/`PiecewiseC1Immersion`** onto `PiecewiseC1Path` (~960 lines saved).
9. **Tag project `Continuous`/`Differentiable`/`MeromorphicAt` lemmas with `@[fun_prop]`**.
10. **Move 7 PR-ready shims to upstream mathlib PRs** (`UpperHalfPlane`, `AtImInfty`, `SlashActions`, `FunctionsBoundedAtInfty`, `TrigLemmas`, `CongruenceSubgrps`, `Instances`).

**Total potential deletion: ~5000+ lines of project code through items 1–6 alone**, with proof reuse unchanged.

---

## Statistics

| Metric | Value |
|---|---|
| Total `.lean` files (ForMathlib) | 183 |
| Total lines | ~132,000 |
| Total declarations | 2,757 |
| &nbsp;&nbsp;`def` + `abbrev` | 219 |
| &nbsp;&nbsp;`structure`/`class`/`inductive` | 32 |
| &nbsp;&nbsp;`instance` | 9 |
| &nbsp;&nbsp;`theorem`/`lemma` | 1,706 |
| `sorry` in source | 0 |
| Files using `set_option maxHeartbeats` | 4 |
| Files fully commented out (`/- ... -/` wrapping body) | 7 |
| Dead orphan files (no importer, not headline/PR-ready) | 4 |
| Dead private declarations | ~24 |
| Unify candidates (Phase 4) | **105** |

### Subdirectory breakdown

| Subdir | Files | Lines |
|---|---|---|
| Top-level `ForMathlib/` | 121 | ~44k |
| `HungerbuhlerWasem/` | 13 | 39k |
| `GeneralizedResidueTheory/` | 28 | 15k |
| `ValenceFormula/` | 17 | 11k |
| `ContourIntegral/` | 4 | 1k |

### Top-imported files (project centrality)

| Rank | File | Importers |
|---|---|---|
| 1 | `ClassicalCPV` | 14 |
| 2 | `SegmentFTC` | 11 |
| 3 | `SingleCrossing` | 9 |
| 3 | `FlatnessConditions` | 9 |
| 5 | `ModularInvariance` | 8 |
| 5 | `GeneralizedWindingNumber` | 8 |
| 7 | `WindingWeightProofs` | 7 |
| 7 | `PiecewiseContourIntegral` | 7 |
| 7 | `PaperPwC1Immersion` | 7 |

The top-imported files are the **structural pinch points**: any refactor of `ClassicalCPV` (rec'd in this report) or `FlatnessConditions` (rec'd for deletion) ripples through 9–14 dependents.

---

## Part 1: Declaration Inventory

Full per-file inventories are at `/tmp/overview-inventory/*.md` (~180 files, 2.7MB, 3029 declaration entries). Each entry has:

- `Type` (full signature)
- `What` (plain math English description)
- `How` (key proof technique / mathlib lemma used)
- `Hypotheses` (key mathematical assumptions)
- `Uses from project` (every project decl referenced in proof body)
- `Used by` (other decls in same file)
- `Visibility` / `Lines` / `Notes`

Each inventory ends with a File Summary (total decls, key API, unused decls, sorries, set_options, long proofs, one-paragraph purpose).

The inventories are the source-of-truth for Phases 3–7.

---

## Part 2: Cross-File Dependencies

**Forward import graph**: 163 project-internal edges across 174 files with ≥1 project import.
**Reverse import map**: 168 files have ≥1 importer; 15 files have NO IMPORTERS.

NO-IMPORTERS files split as:
- **Headline / root theorems** (KEEP) — `HW33Clean`, `ValenceFormulaFinal`, `HungerbuhlerWasem`, `WindingWeightsUnconditional`, etc.
- **PR-ready shims** (KEEP, target upstream) — `UpperHalfPlane`, `SlashActions`, `AtImInfty`, `Instances`, `TrigLemmas`, `CongruenceSubgrps`, `FunctionsBoundedAtInfty`.
- **Orphaned content** (DELETE) — `WindingHomotopy` (superseded by GRT.Homotopy), `ResidueSideProof` (covered by ValenceFormulaBridged), `Cycles`, `HorizontalContribution`.

Raw graphs: `/tmp/overview-inventory/_phase2/{imports,reverse-imports}.txt`.

### Key dependency observations

- `ClassicalCPV` is the top-imported file (14 importers) and is also the file that contains the duplicate `PiecewiseC1Curve`/`PiecewiseC1Immersion` chain. **Refactor target: route 14 importers through `PiecewiseC1Path` instead.**
- `PaperPwC1Immersion.lean` (1755 lines) and its `Invariance` companion (1260 lines) are foundational for the HW33 subtree; restructuring here ripples through ~21 files.
- The `HungerbuhlerWasem/` subtree is a **deeply layered internal-dependency graph** (`MultiCrossingCPV` ← `Crossing` ← `CPVExistence` ← `LocalCutoffs` ← …). Phase 7 confirms this is genuine layering, not proliferation.

---

## Part 3: Mathlib API Audit (most important)

Full audit at `/tmp/overview-inventory/_phase3/mathlib-api-audit.md` (583 lines).

### A. Project definitions catalog (high-impact subset)

| # | Declaration | File | What | Used by | Mathlib status |
|---|---|---|---|---|---|
| 1 | `PwC1Immersion` | `PiecewiseC1Path.lean` | piecewise-C¹ path w/ nonzero deriv | 104 | KEEP |
| 2 | `ClosedPwC1Curve`/`ClosedPwC1Immersion` | `PaperPwC1Immersion.lean` | endpoints-in-partition variant | 81 | KEEP (consolidate) |
| 3 | `firstExitTime*` + `HW33ExitData` | `ExitTime.lean` | exit time `inf {t : ε ≤ ‖γt−s‖}` | 54 | KEEP |
| 4 | `cpvIntegrandOn` | `CauchyPrincipalValue.lean` | ε-cutoff CPV integrand | 54 | KEEP |
| 5 | `tangentDeviation`/`orthogonalProjectionComplex` | `FlatnessConditions.lean` | ℝ-orthogonal projection on `ℝ·L ⊂ ℂ` | 46 | **GENERALIZE → `orthogonalProjection`** |
| 6 | `generalizedWindingNumber'`/`generalizedWindingNumber01` | `ClassicalCPV.lean` | `(2πi)⁻¹·PV ∫ dz/(z−z₀)` | 39 | KEEP (PV variant novel) |
| 7 | `cauchyPV`/`cauchyPVOn` | `CauchyPrincipalValue.lean` | `limUnder` of cutoff integrals | 36 | **REPLACE: delete, use `Tendsto` only** |
| 8 | `HasCauchyPV`/`HasCauchyPVOn` | same | `Tendsto` predicate | 32 | KEEP (the good one) |
| 9 | `principalPartSum` | `PrincipalPart.lean` | `∑ s ∈ S, c s / (z − s)` | 28 | KEEP |
| 10 | `cauchyPrincipalValue'` | `ClassicalCPV.lean` | duplicate of (7) | 28 | **REPLACE: delete primed pair** |
| 11 | `PiecewiseC1Path` | `PiecewiseC1Path.lean` | abstract `[0,1]` piecewise-C¹ | 26 | KEEP (already extends mathlib's `Path`) |
| 14 | `cpvIntegrand` (single-pole) | `CauchyPrincipalValue.lean` | special case of (4) | 15 | **REPLACE: delete (proof of `= cpvIntegrandOn {z₀}` exists)** |
| 15 | `PiecewiseC1Curve`/`PiecewiseC1Immersion` | `ClassicalCPV.lean` | open-interior-partition variant on `[a,b]` | 10+2 | **REPLACE: collapse onto `PiecewiseC1Path`** |
| 17 | `residueSimplePole`/`HasSimplePoleAt` | `Residue.lean` | simple-pole limit & decomp | 8+8 | **GENERALIZE → `meromorphicTrailingCoeffAt` + `MeromorphicAt`** |
| 19 | `poleOrderAt` | `PrincipalPart.lean` | `WithTop ℤ → ℕ` pole order | 6 | **REPLACE → `(-meromorphicOrderAt _ _).untop₀.toNat`** |
| 23 | `Finset.IsConsecutive` | `PaperPwC1Immersion.lean` | `a,b ∈ s`, nothing strictly between | 10+ | **REPLACE / upstream: `Finset.Ioo a b ∩ s = ∅`** |

### B. Top REPLACE / GENERALIZE actions

- **B-1. Two parallel piecewise-C¹ chains.** Collapse `PiecewiseC1Curve`/`PiecewiseC1Immersion` onto `PiecewiseC1Path` via `Path.extend`. **~960 lines deletable.**
- **B-2. Delete `cauchyPV` / `cauchyPVOn` / `cauchyPrincipalValue'`** (`limUnder`-defined). Every caller wants the `HasCauchyPV*` `Tendsto` predicates anyway. Project memory already designates these as primary.
- **B-3. Replace `residueSimplePole` + `HasSimplePoleAt`** with mathlib's `meromorphicTrailingCoeffAt` + `MeromorphicAt`. Unlocks `@[fun_prop]` and the full mathlib `MeromorphicAt` combinator API. ~50 lines deletable in `Residue.lean`.
- **B-4. Replace `orthogonalProjectionComplex`/`tangentDeviation`** with mathlib's `orthogonalProjection (ℝ ∙ L)` over `Complex.instInnerProductSpaceReal`. ~60 lines saved.
- **B-5. Drop the `IsFlatOfOrder` structure wrapper** — switch to a `def` alias over raw `Asymptotics.IsLittleO`. Lets `fun_prop` see through.

### C. API-poor → API-rich

- `limUnder` (in `cauchyPV`, `cauchyPVOn`, `generalizedWindingNumber01`) → `Tendsto`. Mathlib has ~200 lemmas for `Tendsto`; ~20 for `limUnder`.
- `∃ ε > 0, ∀ x, ‖x−x₀‖ < ε → ‖f x − f x₀‖ < ε` (manual ε-δ) → `ContinuousAt`.
- Custom finite-set predicates → `Finset` / `Fintype`.

### D. Hand-rolled patterns to refactor

- 66-line `intervalIntegrable_of_consecutive_pieces` + 55-line `lipschitzOnWith_of_consecutive_pieces` (`PaperPwC1Immersion.lean`) share a `Finset.strongInductionOn`-with-consecutive-pair template. Should be one shared `Finset.consecutive_induction` lemma.
- ε-δ scaffolding in `ExitTime.lean` (≥40 lines) replicable in 3 lines via mathlib's `IsClosed.csInf_mem` + `Tendsto.eventually_lt_const`.
- `PiecewiseContourIntegral.contourIntegral` (329 lines) — long-term target: mathlib's `curveIntegral` (in `Mathlib.MeasureTheory.Integral.CurveIntegral.Basic`).

### E. Missing automation hooks

**Zero `@[fun_prop]` annotations in the entire `ForMathlib/` tree.** 14 most-impactful candidates: `PiecewiseC1Path.continuous`, `PwC1Immersion.continuous`, `ClosedPwC1Curve.continuous`, `principalPartSum_differentiableOn/AnalyticAt/MeromorphicAt`, `laurentPolarPartAt_differentiableAt`, `laurentHigherOrderPolar_differentiableAt`, `laurentHolomorphicRemainder_differentiableOn`, `PolarPartDecomposition.analyticRemainder_diff`, `HasSimplePoleAt.meromorphicAt`. Tagging collapses ~80 hand-written proof chains.

---

## Part 4: Moral Duplication

Full pairwise table (105 candidates) at `/tmp/overview-inventory/_phase4/duplication.md`.

### A. Byte-equal / namespace-different duplicates (DELETE one side)

| # | Pair | Verdict |
|---|---|---|
| 1 | `FlatnessConditions.lean` vs `GeneralizedResidueTheory/Residue/Flatness.lean` | DELETE FlatnessConditions (~441 lines, ~17 byte-equal decls) |
| 2 | `HW33SectorEven.lean` vs `HungerbuhlerWasem/SectorCancellation.lean` | DELETE HW33SectorEven (~558 lines, only `namespace` line differs) |
| 3 | `HW33LaurentPolarPart.lean` vs `HungerbuhlerWasem/LaurentExtraction.lean` | DELETE HW33LaurentPolarPart (~519 lines, strict subset of LaurentExtraction's 1130) |
| 4 | `HW33Bridge.lean` vs `HungerbuhlerWasem/ExitTimeExcision.lean` | DELETE HW33Bridge (~305 lines, 10+ verbatim theorems) |
| 5 | `HigherOrderCancel.lean` vs `HungerbuhlerWasem/HigherOrderAsymptotics.lean` | DEDUPE (17 verbatim theorems = ~300 lines) |
| 6 | `HungerbuhlerWasem.lean` vs `HW33HigherOrderAvoidance.lean` | DEDUPE (~150 lines: `PolarPartDecomposition`, `polarPart_eq_simplePole_add_higherOrder`, `contourIntegral_higherOrder*_eq_zero_of_avoids`) |
| 7 | `ClassicalCPV.lean` (`cauchyPrincipalValue'`, etc.) vs `CauchyPrincipalValue.lean` | DELETE the `'`-suffix definitions |
| 8 | `Residue.lean` CPV defs vs `CauchyPrincipalValue.lean` | DEDUPE / merge |

**Estimated total deletion: 5–6 files ≈ 2500–3000 lines.**

### B. Parametrization opportunities (`_at_i` / `_at_rho` / `_at_rho_plus_one` triples)

10 triples found, each ~120 lines = **~1200 lines** of mechanical parametric duplication:

1. `arc_near_at_{I,rho,rhoPlusOne}_arcsin` (arc near-distance bound)
2. `arc_far_at_{I,rho,rhoPlusOne}_arcsin` (arc far-distance bound)
3. `vert_{near,far}_at_{rho,rhoPlusOne}` (vert pair)
4. `mkSingleCrossingData_at{I,Rho,RhoPlusOne}` (constructor triple)
5. `gWN_fdBoundary_H_at_{i,rho,rho_plus_one}` (winding number triple)
6. `pv_integral_at_{i,rho,rhoPlusOne}_tendsto` (PV integral tendsto triple)
7. `rho_{far,near}_{left,right}` + `rhoPlusOne_{far,near}_{left,right}` (six-lemma pattern)
8. `norm_trig_sub_{I,rho,rhoPlusOne}` (arc-distance lemmas)
9. `fdBoundary_crosses_{I,rho,rhoPlusOne}_at` (boundary crossing)
10. `fdBoundaryFun_arc_dist_{I,rho,rhoPlusOne}` (boundary distance)

A single `(P : EllipticPoint)` parameter would collapse each triple.

### C. Segment-index parametrization

- `Seg1FTCProvider.lean` / `Seg4FTCProvider.lean` / `ArcGenericFTCProvider.lean` — ~40 declarations each, structurally isomorphic, name-suffixed by segment index. Parametrizing on `segIdx : Fin 5` collapses ~2700 lines.
- Inside `WindingWeights/Rho.lean`: `fdBoundary_H_sub_rho_seg{0,1,2,3,4}_re/_slitPlane` (5-segment family) — same pattern.
- Inside `InteriorContourIntegral.lean`: `seg1F` / `seg5F` / `seg4F` (3-fold), `ref1` / `ref5` / `ref4n` / `arcRef` (4-fold).

### D. Within-file derivable wrappers (KEEP-DERIVE)

- `hw_3_3_clean` vs `_avoids` vs `_with_scd` vs `_full` vs `_truly_full` vs `_multi` vs `_full_mero` in `HW33Clean.lean`: pick one primary; the rest are auto-derivable.
- `residueTheorem_crossing` vs `_asymmetric` vs `_singleton` vs `_singleton_asymmetric` in `Crossing.lean`: same pattern.
- `hPV_sing_of_conditionB` vs `_avoids` vs `_singleCrossing` vs `_pointwise_winding` in `HW33PVSing.lean`.

### E. Parallel infrastructure analysis

There are **two parallel "residue / HW3.3" infrastructures** plus the legacy top-level HW33* sequence:

1. **`HungerbuhlerWasem/` subdir** — 13 files, clean modular HW Theorem 3.3 development.
2. **`HW33*.lean` top-level** — 18 files (HW33Clean, HW33Closed, HW33Paper, HW33Tight, HW33Final, etc.). Several are **direct copies of subdir files** (e.g. HW33SectorEven = SectorCancellation).
3. **`GeneralizedResidueTheory/` subdir** — older, partly superseded.

**Strategy**: keep subdirs + only the bridging top-level HW33 files (HW33Tight, HW33Paper, HW33Closed, HW33Final, HW33Clean — wrappers with non-trivial conversion). Delete: `HW33SectorEven`, `HW33LaurentPolarPart`, `HW33Bridge`, `FlatnessConditions`, `ClassicalCPV`.

---

## Part 5: Generalization Opportunities

Full analysis at `/tmp/overview-inventory/_phase5/generalization.md`.

### LOW-difficulty (just retype the type parameters)

- **`Avoids` / Lipschitz / homotopy avoidance** (`NullHomologous`, `CurveUtilities`, `HomotopyDefs`): pure metric facts about paths in `[0,1]`; lift to any `[NormedAddCommGroup E] [NormedSpace ℝ E]`. Proofs work as-is. **Mathlib-upstreamable.**
- **`PiecewiseC1Path` / `PwC1Immersion` / `ClosedPwC1Immersion`**: already generic in target `E`; just audit `Avoids`/`infDist`/`image_compact` to thread `E` through. No proof changes needed.

### MEDIUM-difficulty

- **`hausdorffMeasure_two_lipschitz_image_zero`**: replace ℂ-specific `finrank` with generic `finrank ℝ E`. Mathlib-upstream candidate.
- **`IsFlatOfOrder` / `tangentDeviation` to any `[InnerProductSpace ℝ E]`**: replace ad-hoc `orthogonalProjectionComplex` with mathlib's `Submodule.orthogonalProjection (ℝ ∙ L)`.
- **`HasSimplePoleAt` / `residue` / `HasCauchyPV` over Banach-valued targets `f : 𝕜 → E`**: align with mathlib's `MeromorphicAt` (already supports `f : 𝕜 → E`).

### HIGH-difficulty (correctly ℂ-specific — KEEP)

- `generalizedWindingNumber` value (Cauchy integral of `1/z`), `PolarPartDecomposition`, `angleAtCrossing`, Dixon–Liouville chain, FD geometry for the valence formula — all genuinely use ℂ-specific residue calculus / holomorphicity.
- Hungerbühler–Wasem 3.3 is ℂ-only by design.

### Universe polymorphism / typeclass weakening

- Audit `Finset ℂ S → (S : Set ℂ) [S.Finite]` use sites.
- `Convex ℝ U → StarConvex ℝ z₀ U` (mild secondary win).
- `[NormedSpace ℝ E]` → `[NormedAddCommGroup E]` where smul not used (exemplified by `translatePath`'s `omit` pattern).

---

## Part 6: API Design Review

Full review at `/tmp/overview-inventory/_phase6/api-design.md`.

### Top 15 API additions by impact

| # | Name | Signature | Simplifies |
|---|---|---|---|
| 1 | `Finset.consecutive_induction` | strong-induction on consecutive pairs | 2 >30-line proofs in `PaperPwC1Immersion.lean` plus future similar; **foundational** |
| 2 | `@[ext] PolarPartDecomposition` + `Coe ClosedPwC1Immersion PiecewiseC1Path` | structural | 50+ explicit `γ.toPwC1Immersion.toPiecewiseC1Path` projections in HW33-* |
| 3 | `cpvIntegrandOn_anti` | `S ⊆ T → far → eq` (pointwise) | ≥5 callers manually `split_ifs` |
| 4 | `@[fun_prop]` across all CPV/Diff/Cont lemmas | annotation only | 50+ proofs simplify |
| 5 | `IsFlatOfOrder.congr` | `IsFlatOfOrder γ₁ → γ₁ =ᶠ γ₂ → IsFlatOfOrder γ₂` | `isFlatOfOrder_of_eventuallyEq_shift` + ≥2 more |
| 6 | `Filter.tendsto_const_add_nhdsLT/GT` | shift-of-filter | 4 private copies in `PaperPwC1ImmersionInvariance` |
| 7 | `Finset.IsConsecutive.{mem_left,mem_right,lt,not_mem_Ioo}` + dot notation | trivial | ~15+ manual destructures |
| 8 | `cpvIntegrandOn_empty/zero_fun` tagged `@[simp]` | trivial | `HasCauchyPVOn.zero_fun`, induction bases |
| 9 | `Path.cyclicShift_deriv_eventuallyEq` unified | `Tendsto`/`EventuallyEq` joint | 4 private cases in `PaperPwC1ImmersionInvariance` |
| 10 | `principalPartSum_rest_analyticAt` made public | promotion | 2 duplicate private copies (HW33LaurentPolarPart, HungerbuhlerWasem) |
| 11 | `SatisfiesConditionA'.mono`, `SatisfiesConditionB.mono` | `S₂ ⊆ S₁ → Sat γ f S₁ p → Sat γ f S₂ p` | excision-style HW33 proofs |
| 12 | `IsFlatOfOrder.zero`/`.one` (dot notation) | rename + alias | ~10 call sites |
| 13 | `FunLike (PiecewiseC1Path x y) ℝ E` | instance | 295+ `γ.toPath.extend` uses |
| 14 | `@[simp]` on `laurentPolarPartAt_uncrossed` etc. | promotion + tagging | 5+ inline `simp [laurentX, h_not_cross]` |
| 15 | `cauchyPV_eq_cauchyPVOn_singleton` value-level bridge | `cauchyPV f γ z₀ = cauchyPVOn {z₀} f γ` | HW33-* form-switching |

### Missing `@[ext]` on structures

- `PolarPartDecomposition` (7 fields) — high-impact: enables decomposition-uniqueness.
- `SingleCrossingData` (13 fields)
- `PerPoleCrossData` / `MultiPoleCrossData`
- `AsymmetricSingleCrossingData` / `DerivedAsymmetricCutoffs`
- `ClosedPwC1Curve` / `ClosedPwC1Immersion`
- `PiecewiseC1Path` / `PwC1Immersion`

### Missing `Coe` / `FunLike`

- `ClosedPwC1Curve` / `ClosedPwC1Immersion` → `PiecewiseC1Path` coercion (currently 2–3 manual `.toPwC1Immersion.toPiecewiseC1Path` projections, 50+ occurrences).
- `FunLike (PiecewiseC1Path x y) ℝ E` to replace `CoeFun` (would shrink 295+ `γ.toPath.extend` sites).
- `ContinuousMapClass` instance to integrate with `fun_prop`.

---

## Part 7: Junk / Removable

Full report at `/tmp/overview-inventory/_phase7/junk.md`.

### Tier 1 — Immediate deletion (~1951 lines, zero downstream impact)

Files compiling to **nothing** (entire body wrapped in `/- ... -/`):

| File | Lines | Status |
|---|---|---|
| `hassumunifon.lean` | 1023 | block-commented |
| `Bounds.lean` | 340 | block-commented |
| `QExpansion.lean` | 264 | block-commented |
| `Petersson.lean` | 136 | block-commented |
| `IsBoundedAtImInfty.lean` | 78 | block-commented |
| `LevelOne.lean` | 55 | block-commented |
| `Identities.lean` | 40 | block-commented |
| `CongruenceSubgroupsCopy.lean` | 15 | explicit placeholder stub |

### Tier 2 — Orphan files with real content

| File | Lines | Status |
|---|---|---|
| `WindingHomotopy.lean` | 266 | superseded by `GeneralizedResidueTheory.Homotopy.*` |
| `ResidueSideProof.lean` | 454 | old chain artifact; covered by `ValenceFormulaBridged` |
| `Cycles.lean` | 284 | orphan `ContourCycle` API; no callers |
| `HorizontalContribution.lean` | 131 | orphan seg5 horizontal-line; integrate or delete |

### Tier 3 — Dead private declarations (~24 across ~16 files)

`fdBoundary_sub_I_at_35_im_neg` (ArcFTCAtI); `NormSMulClass ℝ ℂ` × 3 instances (Boundary-Smooth); `unit_circle_re_*_eq_*` (CoreIdentityProof); `volume_ball_preimage_tendsto_zero` (Crossing); `norm_sub_pos_on_farSet` (GammaAnalysis); `pv_piecewise_*` × 3, `pv_simple_pole_*` × 2 (GRT-PrincipalValue); `laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed` (HW33LaurentPolarPart); `two_pi_I_ne_zero_ms` (ModularSideProof); `ge_one_sub_tau_of_*`, `le_one_sub_tau_of_*` (PaperPwC1Immersion); `pvIntegral_vertical_cancel` (PVChain-Assembly); `modularFormCompOfComplex_periodic` (PVChain-Helpers); duplicate `IsScalarTower ℝ ℂ ℂ` (PVChain-ResidueSideInfra); `A_int_eq_greg_mul_deriv` (Residue-MultipointPV-DominatedConvergence); `ref_seg4_I_neg_slitPlane` (SegmentAnalysis); `limUnder_eventually_eq_const` (WindingHomotopy); `cutoff_integral_eq_ftc` (WindingWeights-Rho).

### Tier 4 — Structural consolidation (defer, but track)

- **Unify the two Residue libraries** (Residue.lean vs GRT/Residue.lean). HungerbuhlerWasem.lean docstring already flags this.
- **HW33 chain consolidation** — 21 files, ~3500+ lines connected for one theorem. Target for split-file restructure once HW33 stable.
- **ForMathlib PR pipeline** — files ready for mathlib PR: `UpperHalfPlane`, `FunctionsBoundedAtInfty`, `AtImInfty`, `SlashActions`, `TrigLemmas`, `Instances`, `CongruenceSubgrps`.

### "Headline" files (NO IMPORTERS by design — KEEP)

`HW33Clean.lean`, `ValenceFormulaFinal.lean`, `WindingWeightsUnconditional.lean`, `WindingWeightProofs.lean`, `HungerbuhlerWasem.lean`, the 7 PR-ready shims.

---

## Recommended Action Plan

### Priority 1 — Quick wins (mechanical, ~2 days)

1. **Delete 8 commented-out / placeholder files** (Tier 1, ~1951 lines).
2. **Delete 4 orphan-with-content files** (Tier 2, ~1135 lines, after verifying no callers via `grep`).
3. **Remove 24 dead private declarations** (Tier 3).
4. **Delete `FlatnessConditions.lean`** (441 lines, byte-equal duplicate of `GeneralizedResidueTheory/Residue/Flatness.lean`).
5. **Delete `HW33SectorEven.lean`** (558 lines, one-line-different copy of `HungerbuhlerWasem/SectorCancellation.lean`).
6. **Tag project's `Continuous`/`Differentiable`/`MeromorphicAt` lemmas with `@[fun_prop]`** (zero-risk annotation pass).
7. **Add `@[ext]` to bundled structures** (`PolarPartDecomposition`, `SingleCrossingData`, `AsymmetricSingleCrossingData`, `ClosedPwC1Curve`, etc.).
8. **Add `@[simp]` to `_uncrossed` / `_empty` / `_zero_fun` lemmas** where the form is canonical.

**Subtotal**: ~5000 lines removed, ~50 annotation additions, zero proof rewrites.

### Priority 2 — API improvements (~1 week)

9. **Delete `HW33LaurentPolarPart.lean`** (519 lines, strict subset of `LaurentExtraction.lean`).
10. **Delete `HW33Bridge.lean`** (305 lines, duplicates 10+ theorems of `ExitTimeExcision.lean`).
11. **Dedupe `HigherOrderCancel.lean` ↔ `HigherOrderAsymptotics.lean`** (17 verbatim theorems, ~300 lines).
12. **Extract `Finset.consecutive_induction`** — collapses 2 >30-line proofs.
13. **Unify the 4 `tendsto_*_const_nhds{GT,LT}` private lemmas** and the 4 `deriv_cyclicShift_*` private lemmas in `PaperPwC1ImmersionInvariance.lean`.
14. **Make `principalPartSum_rest_analyticAt` public**, delete the 2 duplicate private copies.
15. **Add `cpvIntegrandOn_anti`** to subsume the 5+ ad-hoc subset rewrites.
16. **Add `SatisfiesConditionA'.mono` / `SatisfiesConditionB.mono`** in `S` — enables excision-style HW33 proofs.

### Priority 3 — Generalizations (~2 weeks)

17. **Generalize `Avoids` / Lipschitz / homotopy avoidance** to `[NormedAddCommGroup E] [NormedSpace ℝ E]`. Mathlib-upstreamable.
18. **Generalize `hausdorffMeasure_two_lipschitz_image_zero`** to arbitrary `[FiniteDimensional ℝ E]`. Mathlib-upstreamable.
19. **Replace `orthogonalProjectionComplex` / `tangentDeviation`** with mathlib's `orthogonalProjection (ℝ ∙ L)`. ~60 lines saved.
20. **Move 7 PR-ready shims to upstream mathlib PRs** (`UpperHalfPlane`, `AtImInfty`, `SlashActions`, `FunctionsBoundedAtInfty`, `TrigLemmas`, `CongruenceSubgrps`, `Instances`).

### Priority 4 — Structural refactors (~1 month)

21. **Collapse `PiecewiseC1Curve`/`PiecewiseC1Immersion` onto `PiecewiseC1Path`** via `Path.extend` (~960 lines deletable; breaks 14 importers, mostly in `Residue.lean`/`ClassicalCPV.lean`).
22. **Delete `cauchyPV`/`cauchyPVOn`/`cauchyPrincipalValue'`** (`limUnder`-defined), keep only `HasCauchyPV*` predicates.
23. **Replace `residueSimplePole` + `HasSimplePoleAt` + `poleOrderAt`** with mathlib's `meromorphicTrailingCoeffAt` + `MeromorphicAt` + `meromorphicOrderAt`. Unlocks `@[fun_prop]` + full mathlib `MeromorphicAt` API.
24. **Unify the two `HasSimplePoleAt` chains** (`Residue.lean` vs `GeneralizedResidueTheory/Residue.lean`). Pick one, migrate downstream.
25. **Parametrize the `_at_i` / `_at_rho` / `_at_rho_plus_one` triples** (10 families, ~1200 lines of duplication) on `(P : EllipticPoint)`.
26. **Parametrize the `Seg1/Seg4/ArcGeneric FTCProvider` triple** on `segIdx : Fin 5` (~2700 lines).
27. **Long-term: route `PiecewiseContourIntegral.contourIntegral` (329 lines) onto mathlib's `curveIntegral`** when that API stabilizes.

### Cumulative line-count impact

| Priority | Lines deletable | Lines simplified |
|---|---|---|
| P1 (mechanical) | ~5000 | (annotations only) |
| P2 (API) | ~1200 | + ~100 |
| P3 (generalization) | ~60 | + 7 files upstreamed |
| P4 (structural) | ~6500 | major |
| **Total** | **~12,700** | major |

---

## Appendix A: Raw Outputs

Persisted analysis artifacts:

- **Per-file inventory**: `/tmp/overview-inventory/*.md` (~180 files, 2.7MB, 3029 declarations)
- **Forward import graph**: `/tmp/overview-inventory/_phase2/imports.txt`
- **Reverse import map**: `/tmp/overview-inventory/_phase2/reverse-imports.txt`
- **Phase 3 Mathlib API audit**: `/tmp/overview-inventory/_phase3/mathlib-api-audit.md` (583 lines)
- **Phase 4 duplication analysis**: `/tmp/overview-inventory/_phase4/duplication.md` (319 lines, 105 unify candidates)
- **Phase 5 generalization**: `/tmp/overview-inventory/_phase5/generalization.md` (138 lines)
- **Phase 6 API design**: `/tmp/overview-inventory/_phase6/api-design.md` (168 lines)
- **Phase 7 junk identification**: `/tmp/overview-inventory/_phase7/junk.md` (221 lines)

These are in `/tmp/` and will be wiped on reboot. Move to `docs/overview/` for persistence:

```bash
mkdir -p docs/overview
cp -r /tmp/overview-inventory docs/overview/2026-05-13
```
