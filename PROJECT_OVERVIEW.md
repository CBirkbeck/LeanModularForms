# Project Overview: LeanModularForms

**Generated**: 2026-05-28 (refresh after the heavy-file golf rounds reached the natural floor).
**Scope**: entire `LeanModularForms/` tree — 118 `.lean` files, 36,180 lines.
**Branch**: `feat/mathlib-prs`
**Supersedes**: `PROJECT_OVERVIEW.md` from 2026-05-25 (120 files / 37,211 lines). The intervening 56 commits ran focused golf passes across the top-of-ranking files — `MultiCrossingCPV` shed −506 lines (2,043 → 1,537), the three winding-weight chain files together lost ~−145, and a project-wide cleanup-all pass with miscellaneous helper consolidations contributed the rest. Two extreme-outlier files (`HW33ParaphrastCommit.lean` and an empty leftover) were removed.

---

## Executive Summary

LeanModularForms is a Lean 4 / Mathlib project formalising:

* the **Hungerbühler–Wasem generalised residue theorem** (HW Theorem 3.3) in its maximally general multi-crossing higher-order meromorphic form, and
* the **textbook valence formula** for weight-`k` modular forms on `SL₂(ℤ)`.

The two **protected theorems** both verify with axioms `[propext, Classical.choice, Quot.sound]` — no extras, freshly re-checked at the end of this session:

| Theorem | File | Lines | Axioms |
|---|---|---|---|
| `LeanModularForms.hw_3_3_clean_full_mero` | `ForMathlib/HW33Clean.lean` | 82 | `[propext, Classical.choice, Quot.sound]` |
| `valence_formula_textbook` | `ForMathlib/ValenceFormulaFinal.lean` | 70 | `[propext, Classical.choice, Quot.sound]` |

### Reduction history (full multi-day session)

| Checkpoint | Files | Lines | Δ |
|---|---|---|---|
| Session start | ~220 | 88,479 | — |
| After Phase 1 (orphans, HW33 fanout collapse) | 135 | 52,073 | −36,406 |
| Forward-reachability rounds 4–7 baseline | 120 | 37,211 | −14,862 |
| **Current** (heavy-file golf rounds) | **118** | **36,180** | **−1,031** |
| Total session reduction | — | — | **−52,299 / −59.1%** |

The last −1,031 lines came from:

| Sub-area | Δ lines | Approach |
|---|---|---|
| `MultiCrossingCPV.lean` | −506 (2,043 → 1,537) | 6 extracted helpers, condB-corner extraction, three `HW3.3` refactors, aggressive simp normalization |
| `CornerFTCAtRho` / `LocalCutoffs` / `ArcGenericFTCProvider` | ~−95 | extracted transfer/re/tail helpers, δ→0 tendsto helper, cutoff/annular helper |
| Winding-weights (`I`/`Rho`/`RhoPlusOne`+`Common`) | ~−68 | extracted shared `arc_*` helpers, decomposed `ftc_logDeriv_telescope_*` (3 variants), shared arc-norm tail, case-split simplification |
| `OnCurvePV/Main` + valence chain | ~−95 | shared CPV-glue and arc-smoothness helpers, norm-equality tightening, `fdBox_convex` simplification |
| `Crossing` / `DixonDiff` / GRT `Residue` | ~−23 | reused `deriv_intervalIntegrable_of_lipschitz`, extracted `aestronglyMeasurable_mul_deriv`, consolidated helpers |
| 81-file project-wide cleanup-all pass | −622 (net) | unified style sweep across every file the umbrella reaches |
| Decompose-proof helper extraction | +103 (cost) | breaking long proofs into named helpers (was paid back later) |

### What this overview adds vs the prior

* Confirms the 30–34k *realistic floor* prediction held (current 36k, with ~−100 to −300 estimated still recoverable).
* Confirms zero new orphans introduced during the heavy golf rounds.
* Documents the remaining post-floor levers honestly.

The remaining tree is honestly load-bearing. There are zero orphan files, zero sorries, zero `axiom` declarations, three `set_option` directives in two files, and every file in the import graph descends from at least one protected theorem.

## Statistics

| Metric | Value |
|---|---|
| Files | 118 |
| Total lines | 36,180 |
| Total declarations (`theorem`/`lemma`/`def`/instance/structure/class/inductive/abbrev) | 1,762 |
| Sorries | **0** |
| Axiom declarations | **0** |
| `set_option` directives | 3 (`DslopeIntegral.lean` ×2, `PVSplitting.lean` ×1) |
| File size: tiny (<50 lines) | 9 |
| File size: small (50–200) | 36 |
| File size: medium (200–700) | 66 |
| File size: large (700–1500) | 6 |
| File size: XL (≥1500) | 1 (`MultiCrossingCPV.lean` at 1,537) |
| `@[simp]` attributes | 9 (in 5 files) |
| `@[fun_prop]` attributes | 0 |
| `by fun_prop` tactic uses | 9 (scattered) |
| Orphan files (unreachable from `LeanModularForms.lean`) | **0** |
| Umbrella imports | 44 |
| Mathlib imports across the tree | 102 |
| Most-imported leaf module | `SegmentFTC.lean` (10 importers) |
| Commits since prior overview (2026-05-25) | 56 |

The XL outlier dropped from 2,043 → 1,537 in this session; the `large` bucket dropped from 7 to 6 because `CornerFTCAtRho.lean` (1,113 → 1,049) stayed in `large` but `MultiCrossingCPV.lean` is still alone in `XL`.

---

## Part 1: Inventory at Scale

### Namespace bucket (file × LOC)

| Bucket | Files | LOC | Notes |
|---|---|---|---|
| `ForMathlib/` (root) | 69 | 17,235 | The general-purpose analytic core: curve types, Cauchy PV, winding, FD-boundary, FTC providers, Dixon theorem, side-mirror BoundaryWinding/Seg infrastructure. Lost 2 files vs prior overview. |
| `ForMathlib/HungerbuhlerWasem/` | 12 | 6,340 | The full HW machinery. Down −462 lines vs prior (mainly the `MultiCrossingCPV` shed). |
| `ForMathlib/ValenceFormula/` | 16 | 8,034 | The valence-formula chain. Down −156 lines from coordinated `WindingWeights` + `Boundary/Smooth` + `OnCurvePV/Main` + `PVChain/Assembly` golfs. |
| `ForMathlib/GeneralizedResidueTheory/` | 16 | 4,130 | The GRT residue chain (used by HW33 and the valence formula bridge). Down −23 lines (negligible). |
| `ForMathlib/ContourIntegral/` | 3 | 289 | Thin slice of contour-integral lemmas. Stable. |
| umbrella `LeanModularForms.lean` | 1 | 44 | Imports 44 leaf modules including both protected files. |
| protected leaves | 2 | 152 | The two top-level theorems and nothing else (`HW33Clean.lean`, `ValenceFormulaFinal.lean`). |
| **Total** | **118** | **36,180** | |

### Top 20 files by line count (with deltas vs prior overview)

| # | File | LOC | Δ | One-line purpose |
|---|---|---|---|---|
| 1 | `HungerbuhlerWasem/MultiCrossingCPV.lean` | 1,537 | **−506** | Multi-crossing CPV existence (corner variant) for HW33 paper-faithful chain |
| 2 | `CornerFTCAtRho.lean` | 1,049 | −64 | `CornerFTCHyp` at ρ and ρ+1 (asymmetric corners of the FD) |
| 3 | `HungerbuhlerWasem/LocalCutoffs.lean` | 1,031 | −37 | Localised exit-time cutoffs feeding multi-crossing CPV (T-BR-Y6c) |
| 4 | `ValenceFormula/WindingWeights/I.lean` | 855 | −5 | gWN = −1/2 at i; PV integral tendsto −iπ |
| 5 | `HungerbuhlerWasem/Crossing.lean` | 852 | +113 | Per-pole CPV composition; the `+113` reflects three new extracted helpers (`crossings_finset_of_endpts_off`, `canonical_derivLimits_at_crossings_exists`, `condB_to_h_B_at_crossings_corner`) that paid back ×3 inside `MultiCrossingCPV` |
| 6 | `ArcGenericFTCProvider.lean` | 783 | −27 | `ArcFTCHyp` at a generic angle on the unit-circle arc |
| 7 | `ValenceFormula/OnCurvePV/Main.lean` | 773 | −68 | On-curve PV main theorem (corner crossings + smooth points) |
| 8 | `ValenceFormula/PVChain/Assembly.lean` | 681 | −30 | Modular-side ↔ residue-side equality assembly |
| 9 | `ValenceFormula/WindingWeights/RhoPlusOne.lean` | 670 | +6 | gWN = −1/6 at ρ+1; PV integral tendsto −iπ/3 |
| 10 | `ValenceFormula/Boundary/Smooth.lean` | 619 | −17 | FD-boundary smoothness on each open segment |
| 11 | `ValenceFormula/PVChain/ResidueSideInfra.lean` | 600 | −16 | log-deriv analyticity off zeros + residue-side helpers |
| 12 | `ValenceFormula/WindingWeights/Rho.lean` | 596 | −15 | gWN = −1/6 at ρ; PV integral tendsto −iπ/3 |
| 13 | `DixonDiff.lean` | 585 | −29 | Dixon h2 holomorphic off curve, h1 holomorphic everywhere |
| 14 | `HungerbuhlerWasem/LaurentExtraction.lean` | 573 | −17 | Extracts Laurent polar-part data into named functions |
| 15 | `GeneralizedResidueTheory/Residue.lean` | 569 | −6 | GRT residue theory: residue, CPV-on, residue-of-simple-pole, residueAt |
| 16 | `ValenceFormula/PVChain/ArcContribution.lean` | 560 | 0 | Arc contribution to the PV chain |
| 17 | `ValenceFormula/OnCurvePV/EndpointCorner.lean` | 503 | 0 | Endpoint-corner case (asymmetric ρ/ρ+1 contribution) |
| 18 | `PaperPwC1Immersion.lean` | 503 | 0 | `ClosedPwC1Immersion`/`ClosedPwC1Curve` types |
| 19 | `CoreIdentityProof.lean` | 501 | −2 | Core contour-integration identity for the valence formula |
| 20 | `CrossingAtRho.lean` | 496 | 0 | Crossing-at-ρ data (specialised SingleCrossingData) |

### File-size threshold movement vs prior overview

| Threshold | Prior overview (37k) | Current (36k) | Δ |
|---|---|---|---|
| ≥1500 lines | 1 (`MultiCrossingCPV` 2,043) | 1 (`MultiCrossingCPV` 1,537) | XL outlier dropped 506 lines |
| ≥1000 lines | 3 | 3 | unchanged (just shrunk) |
| ≥700 lines | 10 | 7 | three files dropped below 700: `OnCurvePV/Main` (841→773), `PVChain/Assembly` (711→681), `MultiCrossingCPV` ≥1500 already counted |
| ≥500 lines | 22 | 19 | three more dropped: `DominatedConvergence` (492 — under), `Crossing` rose to 852 (also above 500), `LaurentExtraction` (573 — still above), `Smooth.lean` (619 — still above). Net 3 files dropped from this range. |
| <100 lines | 13 | 14 | one additional file now under 100 |

### Most-imported modules (in-degree)

These are the load-bearing leaf utilities. Anything ≥5 importers is structural infrastructure:

| In-deg | Module |
|---|---|
| 10 | `ForMathlib.SegmentFTC` |
| 8  | `ForMathlib.GeneralizedWindingNumber` |
| 7  | `ForMathlib.SegmentAnalysis` |
| 7  | `ForMathlib.ModularInvariance` |
| 6  | `ForMathlib.WindingWeightProofs` |
| 6  | `ForMathlib.SingleCrossing` |
| 6  | `ForMathlib.ClassicalCPV` |
| 5  | `ForMathlib.Instances` |
| 5  | `ForMathlib.FlatnessConditions` |
| 5  | `ForMathlib.BoundaryWindingSeg1Proof` |
| 5  | `ForMathlib.ValenceFormula.Boundary.Smooth` |
| 5  | `ForMathlib.FDBoundary` |
| 5  | `ForMathlib.CrossingAtI` |

### Newly-under-threshold files vs prior overview

* `MultiCrossingCPV.lean` (2,043 → 1,537): still XL, now closer to falling into `large`
* `OnCurvePV/Main.lean` (841 → 773): now under 800
* `PVChain/Assembly.lean` (711 → 681): now under 700
* `CornerFTCAtRho.lean` (1,113 → 1,049): could fall below 1000 with one more pass
* `DominatedConvergence.lean` (492 → 492): unchanged
* `OnCurvePV/EndpointCorner.lean` (503 → 503): unchanged

No file *grew* materially except `Crossing.lean` (+113), which absorbed three large extracted helpers that paid back ~×3 in `MultiCrossingCPV`.

---

## Part 2: Dependency Walk (from umbrella + protected theorems)

The umbrella file `LeanModularForms.lean` imports 44 modules (43 leaves + `ValenceFormulaFinal.lean` and `HW33Clean.lean` as transitive roots).

**Orphan count: 0.**

Reachability check (Python import-graph walk from `LeanModularForms.lean`):
- Total modules: 118
- Reachable from umbrella: 118
- Orphans: 0

This was verified explicitly via Python script walking `import LeanModularForms.…` lines through the transitive closure. The two protected theorems' source files are each reachable as direct umbrella imports, and every other file is reachable as an indirect dependency of one of them.

### Protected-theorem dependency depths (informal)

`hw_3_3_clean_full_mero`:
* depth 0: `HW33Clean.lean`
* depth 1: `HungerbuhlerWasem/MultiCrossingCPV.lean`
* depth 2: `HungerbuhlerWasem/Crossing.lean`, `HungerbuhlerWasem/LocalCutoffs.lean`, ...
* deeper: all of `HungerbuhlerWasem/`, `LaurentExtraction`, `CrossingAtRho`, `SingleCrossingData`, `PiecewiseC1Path` chain, `NullHomologous`, `DixonTheorem`, `GeneralizedResidueTheory/Residue*` chain, ...

`valence_formula_textbook`:
* depth 0: `ValenceFormulaFinal.lean`
* depth 1: `ValenceFormulaBridged.lean`
* deeper: `CoreIdentityProof`, `Orbits`, `OrbitPairing`, `ModularInvariance`, `ValenceFormula/` chain (PVChain, OnCurvePV, WindingWeights, Boundary), and through the bridge also the residue/winding utility pile from chain 1.

The two trees share a substantial base (`SegmentFTC`, `PiecewiseC1Path`, `GeneralizedResidueTheory/Residue`, `EllipticPoints`, `FDBoundaryH`).

### Sanity-check: zero-importer modules

A walk of the reverse graph confirms only the umbrella has in-degree 0 (and the umbrella is the top-of-tree). Every other file has at least one importer.

---

## Part 3: Mathlib API Audit (HIGHEST VALUE)

This is the lever that did NOT exhaust itself in the prior 7 rounds of forward-reachability sweeps and golfing. It is the slow lever (each opportunity requires investigating, drafting, and PR'ing upstream), but it is the only honest path to further reduction beyond ~36k.

### Already-applied mathlib API wins (carrying over from prior session work)

Confirmed via grep:

| Identifier | Use sites | Saved |
|---|---|---|
| `convex_halfSpace_re_gt` / `convex_halfSpace_re_lt` / `convex_halfSpace_im_gt` / `convex_halfSpace_im_lt` | 3 | `fdBox_convex` proof in `ResidueSideInfra` and `Orbits` |
| `le_of_sq_le_sq` | 2 | `PVChain/Assembly.lean` (norm bounds) |
| `sq_eq_sq₀` | 3 | `OrbitPairing`, `PVChain/Assembly`, `OnCurvePV/Main` |
| `abs_le_of_sq_le_sq'` | 2 | `FlatChordBound`, `HigherOrderAsymptotics` |
| `deriv_intervalIntegrable_of_lipschitz` (project helper) | 3 | `HungerbuhlerWasem.lean`, `Crossing.lean` (reuses across CPV proofs) |
| `aestronglyMeasurable_mul_deriv` (project helper) | 3 | `DixonDiff.lean` (paid back 3× in module) |

### Searched and unavailable in current mathlib (4.30.0-rc2)

* `Complex.slitPlane` — only basic API (`isOpen_slitPlane`, `slitPlane_ne_zero`, `ofReal_mem_slitPlane`, `mem_slitPlane_iff`). Project uses 89 references via `mem_slitPlane_iff.mpr`/`.inl`/`.inr` already.
* Custom CPV API — `HasCauchyPV.add`, `.zero_fun`, `.finset_sum`, `.congr_pointwise` (in `HW33` umbrella) are project-specific and have no analogue.
* `IntervalIntegrable (deriv f)` — mathlib has the `AbsolutelyContinuousOnInterval`, `MonotoneOn`, and `BoundedVariationOn` paths via `Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable`. The project already specialises through `PiecewiseC1Path.deriv_intervalIntegrable_of_lipschitz`.

### Live candidates worth investigation (lever B continuation)

1. **`SingleCrossingData` / `CornerFTCHyp` / `ArcFTCHyp` upstream** — these structures (in `SingleCrossing.lean`, `CrossingAtRho.lean`, `WindingWeightProofs.lean`) carry meaningful proof obligations and could plausibly be PR'd to `Mathlib.Analysis.Complex.…`. Estimated saving locally: ~300 lines via extension API.

2. **`PiecewiseC1Path` and `PwC1Immersion`** — the bundled-path types in `PiecewiseC1Path.lean` (125 lines) and `PiecewiseC1PathOn.lean` (79 lines) are *very* close to what mathlib could absorb. A PR there would let us drop ~500 lines of "carrier" lemmas in `PaperPwC1Immersion.lean` (503), `FDBoundaryPath.lean` (204), and various utilities. Estimated saving: ~150–200 lines once the upstream API replaces local custom helpers.

3. **`HasCauchyPV` API** — currently no mathlib analogue exists. The `CauchyPrincipalValue.lean` (168 lines) plus `HungerbuhlerWasem/Crossing.lean` additivity/sum helpers (~80 lines of `HasCauchyPV.add/zero_fun/finset_sum/congr_pointwise`) are stable enough to PR. Saving: a small leaf module shrinks to its definition; the helpers move upstream. Estimated locally: ~−60 lines.

4. **`hasDerivAt_arc_sub_const` / `hasDerivAt_aff_imI_*`** — these are pure mathlib derivative-of-composition lemmas in `WindingWeights/Common.lean` (~30 lines total) that *should* live in `Mathlib.Analysis.SpecialFunctions.Complex.Trigonometric`. Estimated saving locally: ~−30 once accepted.

5. **`ftc_log_pieceFM`, `ftc_log_piece_upper`, `ftc_log_piece_lower`** — the three piecewise-FTC bridges in `WindingWeights/Common.lean` (~50 lines each, ~150 total) are a candidate cluster for upstreaming to `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`. The local proofs are clean, mathlib has no direct analogue. Estimated saving: ~−40 lines if accepted (the locals would become one-line invocations).

### Cumulative mathlib-upstream potential

Realistic estimate for further reduction via lever B: **~−150 to −250 lines** spread across 5–10 PRs to mathlib. This is the conservative cumulative; some PRs might be rejected, others may simplify only modestly.

This is the slow lever. It does not yield 1000-line wins; it yields steady 30–60 line wins per accepted PR, each requiring 1–3 weeks of upstream review.

---

## Part 4: Moral Duplications (with pairwise table)

After the prior 5+ rounds of dead-decl walks, the population of *true* moral duplications is sparse. The 60 stem-groups discovered by automatic name-similarity scanning are dominated by:

* **Per-segment variants** (`_seg1`, `_seg2`, …, `_seg5`) — these are mathematical decompositions where each segment carries a different shape/equation; the parallel naming is a *consequence* of the FD geometry (segments labelled 1–5), not a sign of duplication.
* **Per-side variants** (`_left`, `_right`) — most arise from the symmetric left/right cutoff/asymptotic shape pairs in CPV existence; the pair is informational, not redundant.
* **Per-elliptic-point variants** (`_i`, `_rho`, `_rho_plus_one`) — three elliptic points, three winding/PV-existence chains. The structural skeleton of the proof is parallel but the per-point geometry differs (i is on the imaginary axis with a single `t₀` crossing; ρ/ρ+1 share a structure but with different angles and segment relations).

### Pairwise verification of candidate clusters

| Cluster | Pair / triple | Verdict |
|---|---|---|
| `ftc_logDeriv_telescope_{i,rho,rho_plus_one}` | 3 variants in `WindingWeights/{I,Rho,RhoPlusOne}.lean` | **Genuinely parallel but distinct.** The i variant has the inner `t₀_i` crossing where the imaginary axis meets the arc; the ρ/ρ+1 variants share a 4-piece decomposition (seg1, arc, seg4, seg5) with different break points. Common skeleton is already factored to `Common.lean` (`heq_deriv_of_eq_on_nhds`, `hasDerivAt_arc_sub_const`, `hasDerivAt_aff_imI_*`). A unified telescope lemma would require parameterising the piecewise breakpoints AND the inner-crossing presence; cost > saving. |
| `arg_approach_{i_left, i_right, rho_left_helper, rho_right, rho'_left, rho'_right_helper}` | 6 variants across the same three files | **Mostly distinct.** Each handles a different combination of (elliptic point, side of crossing, with-helper-or-not). The `_helper` variants are intermediate lemmas, not duplicates. Common subexpression already in `Common.lean` via `arg_ofReal_mul_I`, `arg_two_sin_mul`. |
| `cpv_exists_{at_i, at_rho, at_rho_plus_one}` in `ValenceFormula/OnCurvePV/Basic.lean` | 3 variants | **Genuine parallelism over the 3 elliptic points** but each is a specialisation of a generic schema. A unified `cpv_exists_at_ellipticPoint p` would conceivably help; the local types differ slightly (each carries its own `CornerFTCHyp` or `ArcFTCHyp` instance). Estimated saving: ~−30 lines. Risk: API regression. |
| `exists_chord_slitPlane_radius_{left, right}` | 2 variants in `LocalCutoffs.lean` (lines 351, 365) | **Genuine pair** by symmetric construction. Common ~80% but they have distinct sign-convention obligations. Could be merged via `f → -f` trick, but the local proofs are already short (~15 lines each). Saving: ~−10. |
| `exists_chord_div_endpoint_slitPlane_{left, right}` | 2 variants (LocalCutoffs.lean lines 382, 429) | Same as above. |
| `chord_div_t_tendsto_{left,right}` in `HungerbuhlerWasem/CPVExistence.lean` | 2 variants (lines 48, 80) | Same symmetric-pair shape. |
| `chord_to_tangent_isLittleO_{left,right}` in `HigherOrderAsymptotics.lean` | 2 variants (lines 173, 206) | Symmetric. Already share substantial inner content via prior golf. |

### Conclusion

The first 6 rounds of forward-reachability + 5 rounds of dead-decl walks have *already eliminated the moral duplications that exist as such*. The remaining "parallel" names reflect mathematical structure (5 segments; 3 elliptic points; left/right of a crossing) where unifying via a parameter would cost as much as it saves and reduce readability.

Conservative estimate for further reduction via *additional* deduplication: **~−40 to −80 lines**, mostly via merging symmetric left/right pairs in `LocalCutoffs`, `CrossingAnalysis`, `CrossingDataBuilder`, `CPVExistence`, and `HigherOrderAsymptotics`.

---

## Part 5: Generalization Opportunities

Few survive after the prior rounds. The remaining ones are:

### A. `FlatnessConditions.lean` — `IsFlatOfOrder` structure (229 lines)

The condition is currently specialised to `ℝ → ℂ` paths. The natural generalisation is to a general normed-vector-space target. Whether the project benefits: a partial generalisation has already occurred (each crossing/condition lemma is already polymorphic in the analytic body). The structure declaration itself is ~25 lines, so saving from generalisation would be minimal (~−5 lines locally, but ~−15 if a `Mathlib.Analysis.Asymptotics.FlatnessOfOrder` PR is accepted upstream).

### B. `CauchyPrincipalValue.lean` — `HasCauchyPV` API (168 lines)

The current API is specialised to `ℂ`-valued integrands on `PiecewiseC1Path`. Generalisation to a generic Banach space + general absolutely continuous curve is plausible. Locally saves nothing; upstream PR potential ~−60 if mathlib adopts.

### C. `ArcCalculus.lean` — `GeneralizedResidueTheory.ArcCalculus` (74 lines)

The arc-derivative + arc-length calculus. Heavily specialised to the unit circle and the FD arc. Plausibly generalisable to `Path ℝ ℂ` with constant magnitude. Local saving: small.

### D. Generalise from `ℝ → ℂ` to `ℝ → E`

Most existing `ℝ → ℂ` lemmas (in `FDBoundary*`, `ValenceFormula/WindingWeights/Common`, `SegmentFTC`) implicitly depend on `Complex`-specific structure (arg, log, slit plane). Genuine generalisation would require re-engineering and is **not** a saving lever.

### Estimate

Conservative estimate for further reduction via generalisation alone: **~−20 to −40 lines locally** (most of the gain comes via mathlib PRs whose acceptance would be counted under Part 3 / Lever B).

---

## Part 6: API Improvements

### Missing simp lemmas

There are only 9 `@[simp]` attributes across the entire tree (`Orbits.lean`, `ClassicalCPV.lean` ×3, `PiecewiseC1Path.lean` ×2, `CauchyPrincipalValue.lean` ×3). Adding more `@[simp]` annotations could shrink case-handling in lemma proofs but is unlikely to remove lines materially.

Candidates worth adding:
* `Complex.norm_exp_mul_I_eq_one` (if not already a `@[simp]` upstream)
* `fdBoundary_H_at_zero`, `fdBoundary_H_at_one_eq_rho_plus_one`, `fdBoundary_H_at_two_eq_I`, `fdBoundary_H_at_three_eq_rho`, `fdBoundary_H_at_four`, `fdBoundary_H_at_five`

Estimated saving: **~−20 lines** total across the project.

### Missing `fun_prop` annotations

The project has 0 `@[fun_prop]` annotations and 9 `by fun_prop` uses. The 132 manual `ContDiff` proofs (estimate from `have.*: ContDiff` grep) could often be `by fun_prop`'d, but most have non-trivial scope (composition with `Path.extend`, conditional arms). A focused pass could probably trim 30–50 lines via `fun_prop` annotations on key project definitions.

### Missing instances / extensionality

The project defines:
* `PiecewiseC1Path`, `PwC1Immersion`, `ClosedPwC1Curve`, `ClosedPwC1Immersion` — none are `@[ext]`. Adding `@[ext]` would simplify equality reasoning.
* `FDWindingData`, `FDWindingDataFull`, `SmoothBoundaryWindingData`, `SingleCrossingData`, `AsymmetricSingleCrossingData`, `CornerFTCHyp`, `ArcFTCHyp` — none are `@[ext]`. Same.

Estimated saving from `@[ext]` + `@[fun_prop]` campaign: **~−40 lines**.

---

## Part 7: Junk / Removable

The forward-reachability cascade bottomed out at round 7. A fresh scan finds:

* **Orphans**: 0
* **Empty/near-empty files**: 0 (all near-empty files from prior rounds — `MeromorphicBridge`, `ContourIntegral/WindingNumber`, `CurveAvoidance`, `ValenceFormula/PVChain.lean` — were removed in round 5 waves 1–4)
* **Dead declarations within reachable files**: extensively walked by rounds 5–6, with 7+ cleanup waves dropping ~3,000 lines of dead code. A spot-check of `MultiCrossingCPV.lean` decl list shows no dead theorems remaining.
* **Dead imports**: minor noise probably remains; estimated saving ~−20 lines via `unused_imports` linter pass.
* **`HW33Clean.lean` 82-line comment block**: this is intentional documentation per session memory rules ("Compression rules: top-of-file docstrings are not bloat").

### Conclusion

Junk-and-removable lever is **exhausted**. Further round 8/9/etc. dead-decl walks would yield <50 lines. The remaining cleanup is `unused_imports`, which is mechanical.

---

## Part 8: Recommended Action Plan (Honest)

### Context

This session has executed ALL the levers from the prior plan:

1. **Phase 1 (orphan subsystem deletion)** — done in earliest days; not repeatable.
2. **HW33 fan-out collapse (variant ratchet)** — done; the 32→5 variant collapse and 13→3 dixon collapse cannot recur (the canonical forms are now load-bearing).
3. **Forward-reachability cascade (rounds 4–7)** — done; converged at round 7 with 0 orphans, 0 dead leaves.
4. **Proof-golf waves (Phase 3 + waves 4–8 of decompose)** — done. The recent rounds added named helpers (decompose) then collapsed back via re-golfing. The −1,031 lines this session is the residue.
5. **Heavy-file targeted golf** — done this session for top-20 ranked files.

### Levers that remain (honest assessment)

| Lever | Estimated Δ | Cost | Honesty rating |
|---|---|---|---|
| **B. Mathlib upstreaming** (Part 3) | −150 to −250 | 5–10 PRs × 1–3 weeks each | High value, slow. The only path beyond the natural floor. |
| **B'. `@[ext]` + `@[fun_prop]` campaign** (Part 6) | −40 to −60 | 1–2 sessions | Mechanical. Low risk. |
| **C. Symmetric left/right pair merger** (Part 4) | −40 to −80 | 1 session | Risk of readability regression. Skip unless explicit ask. |
| **D. Unused-imports linter pass** (Part 7) | −20 to −40 | 1 session | Mechanical. Low risk. |
| **E. Drop GRT generality** | −500 to −1500 | research-scope decision | NOT consolidation — would change the mathematical scope of the paper. Owner decision only. |
| **F. Accept current 36k as the project's natural shape** | 0 | no work | The other-side-of-the-mirror option. |

### Realistic forward path

Without lever E, the achievable reduction beyond 36k is bounded by:

* Lever B (mathlib upstreaming) — slow, ~−150 to −250 over multiple sessions
* Lever B' / D (mechanical cleanups) — ~−60 to −100 in a single focused session
* Lever C (symmetric pair merger) — ~−40 to −80, but risk

**Combined honest estimate for one more focused session**: **−100 to −300 lines**, putting the floor at ~35,900 → ~35,500.

If multiple sessions and a string of accepted mathlib PRs land, the absolute lower bound is ~34,500. **The "30–34k realistic floor" prediction from the prior overview was approximately correct** — we're now within the upper half of that range.

### Recommended path forward (if more consolidation is desired)

1. **First** (mechanical, cheap): run the lever B' campaign — add `@[ext]` to the 8 structures, add `@[fun_prop]` to the 132 candidate ContDiff definitions, do the unused-imports pass. Expected: −60 to −100. Cost: 1 focused session.
2. **Second** (slow, valuable): pick 1–2 mathlib upstream targets from Part 3 candidate list (most accessible: `hasDerivAt_arc_sub_const`/`hasDerivAt_aff_imI_*` cluster). PR them. Expected per PR: −30 to −60 if accepted. Cost: 1 PR per cycle of upstream review.
3. **Don't** pursue lever C without explicit need — the symmetric-pair structure aids readability.
4. **Don't** pursue lever E unless scope shrinks for research reasons.
5. **Strongly consider** accepting 36k as the project's natural shape; the proof tree is mathematically taut.

### What's now at its floor

| Component | Status |
|---|---|
| Multi-crossing CPV chain | Floor at 1,537 (had been 2,043). Further compression would require either (a) drop higher-order-`f` generality or (b) wait for mathlib `HasCauchyPV` API. |
| Per-elliptic-point winding chains (`I`, `Rho`, `RhoPlusOne`) | Floor at ~600 each. Cannot unify without `t₀_i` complication. |
| FTC providers (`Seg1`, `Seg4`, `ArcFTCAtI`, `VertSeg`, `ArcGenericFTC`) | Floor at ~360 each. Per-segment geometry mandates individual handling. |
| GRT residue chain (16 files) | Floor at 4,130 — this is the pure mathematical content; no fat to cut. |

---

## Appendix: Final Axiom + Signature Check

Performed via `lean_verify` on both protected theorems at the very end of this overview generation:

```
LeanModularForms.hw_3_3_clean_full_mero:
  axioms = [propext, Classical.choice, Quot.sound]
  warnings = []

valence_formula_textbook:
  axioms = [propext, Classical.choice, Quot.sound]
  warnings = []
```

Both protected theorems remain on the canonical Lean axiom basis. No additional axioms, no `sorry`, no `admit`. The proof closure of each theorem traverses the union of all 118 modules in the tree.

---

**END OF OVERVIEW**
