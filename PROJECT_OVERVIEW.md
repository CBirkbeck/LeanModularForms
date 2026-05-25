# Project Overview: LeanModularForms

**Generated**: 2026-05-25 (refresh after the 7-round forward-reachability sweep).
**Scope**: entire `LeanModularForms/` tree — 120 `.lean` files, 37,211 lines.
**Branch**: `feat/mathlib-prs`
**Supersedes**: previous `PROJECT_OVERVIEW.md` from 2026-05-24 (135 files / 52,073 lines). The intervening sweep removed roughly 14,900 lines via *forward-reachability from the two protected theorems*, which exposed entire pipelines that the umbrella import detector had ratified but that neither protected theorem actually traversed.

---

## Executive Summary

LeanModularForms is a Lean 4 / Mathlib project formalising:

* the **Hungerbühler–Wasem generalised residue theorem** (HW Theorem 3.3) in its maximally general multi-crossing higher-order meromorphic form, and
* the **textbook valence formula** for weight-`k` modular forms on `SL₂(ℤ)`.

The two **protected theorems** (both verifying with axioms `[propext, Classical.choice, Quot.sound]` — no extras):

| Theorem | File | Lines |
|---|---|---|
| `LeanModularForms.hw_3_3_clean_full_mero` | `ForMathlib/HW33Clean.lean` | 82 |
| `valence_formula_textbook` | `ForMathlib/ValenceFormulaFinal.lean` | 70 |

The codebase began this multi-day session at 88,479 lines (~220 files) and currently sits at 37,211 lines (120 files) — a **−51,268 / −58.0% reduction**. The major reductions, in chronological order, came from:

1. **Phase 1 (orphan subsystems)** dropped `Modularforms/`, `SpherePacking/`, and a 51-file orphan ring (−14,340 lines).
2. **HW33 fan-out collapse** consolidated 16 HW33 variant files into one canonical `HW33Clean.lean` (−3,784 lines).
3. **Variant ratchet collapse** trimmed `residueTheorem_crossing_*` from 32 to 5 visible variants and `dixonFunction_eq_zero*` from 13 to 3.
4. **Proof golf** waves (Phase 3, then waves 4–8 of decompose-and-shrink) ran across the long-proof corpus.
5. **Forward-reachability rounds 4–7** were the late discovery: traversing the import graph from the two protected theorems and the umbrella file showed that several long pipelines (most prominently the non-`_corner` arm of `MultiCrossingCPV.lean`, the speculative `ExitTimeExcision.lean`, the `Proposition2_2.lean` chain, and the `cyclicShift` invariance development in `PaperPwC1ImmersionInvariance.lean`) were reachable as orphans, not as actual dependencies. Six waves of dead-decl removal cut another ~6,700 lines from inside files whose names looked load-bearing.

The remaining tree is honestly load-bearing. There are zero orphan files, zero sorries, zero `axiom` declarations, and a single `set_option backward.isDefEq.respectTransparency false` directive in two files. Every entry in the top-50 file ranking sits on the transitive dependency closure of at least one protected theorem.

## Statistics

| Metric | Value |
|---|---|
| Files | 120 |
| Total lines | 37,211 |
| Total declarations (`theorem`/`lemma`/`def`/instance/structure/...) | ~1,732 |
| Sorries | **0** |
| Axiom declarations | **0** |
| `set_option` directives | 3 (`DslopeIntegral.lean` ×2, `PVSplitting.lean` ×1) |
| File size: tiny (<50 lines) | 8 |
| File size: small (50–200) | 39 |
| File size: medium (200–700) | 65 |
| File size: large (700–1500) | 7 |
| File size: XL (≥1500) | 1 (`MultiCrossingCPV.lean` at 2,043) |
| `@[simp]` attributes | 10 (in 5 files) |
| `@[fun_prop]` attributes | 0 |
| Orphan files (unreachable from `LeanModularForms.lean`) | **0** |
| Umbrella imports | 44 |
| Commits this session (April + May 2026) | ~470 |

---

## Part 1: Inventory at Scale

### Namespace bucket (file × LOC)

| Bucket | Files | LOC | Notes |
|---|---|---|---|
| `ForMathlib/` (root) | 71 | 17,699 | The general-purpose analytic core: curve types, Cauchy PV, winding, FD-boundary, FTC providers, Dixon theorem, side-mirror BoundaryWinding/Seg infrastructure. |
| `ForMathlib/HungerbuhlerWasem/` | 12 | 6,802 | The full HW machinery: per-pole CPV composition, multi-crossing CPV existence, Laurent extraction, higher-order asymptotics, sector cancellation, multi-pole DCT, local cutoffs. |
| `ForMathlib/ValenceFormula/` | 16 | 8,190 | The valence-formula chain: PV chain assembly (with `Assembly/ResidueSide.lean`), boundary smoothness/bounds, winding weights at i / ρ / ρ+1, on-curve PV decomposition, segment 5 cusp integral. |
| `ForMathlib/GeneralizedResidueTheory/` | 16 | 4,153 | The GRT residue chain (used by HW33 and the valence formula bridge): residue+CPV definitions, generalized theorem base, multi-point PV decomposition, homotopy invariance/integrality, PV infrastructure (annulus bounds, singular annulus, gamma analysis, remainder analysis, step bounds, uniform step bound), Cauchy primitive. |
| `ForMathlib/ContourIntegral/` | 3 | 307 | Thin slice of contour-integral lemmas (`CrossingLimit`, `PVSplit`, `SegmentFTC`). |
| umbrella `LeanModularForms.lean` | 1 | 44 | Imports 44 leaf modules including both protected files. |
| protected leaves (`HW33Clean.lean`, `ValenceFormulaFinal.lean`) | 2 | 152 | The two top-level theorems and nothing else. |

### Top 30 files by line count

| # | File | LOC | One-line purpose | Class |
|---|---|---|---|---|
| 1 | `HungerbuhlerWasem/MultiCrossingCPV.lean` | 2,043 | Multi-crossing CPV existence (corner variant) for the HW33 paper-faithful chain | LOAD-BEARING |
| 2 | `CornerFTCAtRho.lean` | 1,113 | `CornerFTCHyp` at ρ and ρ+1 (asymmetric corners of the FD) | LOAD-BEARING |
| 3 | `HungerbuhlerWasem/LocalCutoffs.lean` | 1,068 | Localised exit-time cutoffs feeding multi-crossing CPV (T-BR-Y6c) | LOAD-BEARING |
| 4 | `ValenceFormula/WindingWeights/I.lean` | 860 | gWN = −1/2 at i; PV integral tendsto −iπ | LOAD-BEARING |
| 5 | `ValenceFormula/OnCurvePV/Main.lean` | 841 | On-curve PV main theorem (corner crossings + smooth points) | LOAD-BEARING |
| 6 | `ArcGenericFTCProvider.lean` | 810 | `ArcFTCHyp` at a generic angle on the unit-circle arc | LOAD-BEARING |
| 7 | `HungerbuhlerWasem/Crossing.lean` | 739 | Per-pole CPV composition (T-GL-01) culminating in the paper-faithful clean spec | LOAD-BEARING |
| 8 | `ValenceFormula/PVChain/Assembly.lean` | 711 | Modular-side ↔ residue-side equality assembly | LOAD-BEARING |
| 9 | `ValenceFormula/WindingWeights/RhoPlusOne.lean` | 664 | gWN = −1/6 at ρ+1; PV integral tendsto −iπ/3 | LOAD-BEARING |
| 10 | `ValenceFormula/Boundary/Smooth.lean` | 636 | FD-boundary smoothness on each open segment | LOAD-BEARING |
| 11 | `ValenceFormula/PVChain/ResidueSideInfra.lean` | 616 | log-deriv analyticity off zeros + residue-side helpers | LOAD-BEARING |
| 12 | `DixonDiff.lean` | 614 | Dixon h2 holomorphic off curve, h1 holomorphic everywhere | LOAD-BEARING |
| 13 | `ValenceFormula/WindingWeights/Rho.lean` | 611 | gWN = −1/6 at ρ; PV integral tendsto −iπ/3 | LOAD-BEARING |
| 14 | `HungerbuhlerWasem/LaurentExtraction.lean` | 590 | Extracts Laurent polar-part data into named functions | LOAD-BEARING |
| 15 | `GeneralizedResidueTheory/Residue.lean` | 575 | GRT residue theory: residue, CPV-on, residue-of-simple-pole, residueAt | LOAD-BEARING |
| 16 | `ValenceFormula/PVChain/ArcContribution.lean` | 560 | Arc contribution to the PV chain | LOAD-BEARING |
| 17 | `ValenceFormula/OnCurvePV/EndpointCorner.lean` | 503 | Endpoint-corner case of on-curve PV (the asymmetric ρ/ρ+1 contribution) | LOAD-BEARING |
| 18 | `PaperPwC1Immersion.lean` | 503 | `ClosedPwC1Immersion`/`ClosedPwC1Curve` types (post-`cyclicShift`-prune) | LOAD-BEARING |
| 19 | `CoreIdentityProof.lean` | 503 | Core contour-integration identity for the valence formula | LOAD-BEARING |
| 20 | `WindingInteger.lean` | 496 | Continuous argument lift + integer-valued winding number | LOAD-BEARING |
| 21 | `CrossingAtRho.lean` | 496 | Crossing-at-ρ data (specialised SingleCrossingData) | LOAD-BEARING |
| 22 | `GeneralizedResidueTheory/Residue/MultipointPV/DominatedConvergence.lean` | 492 | Dominated-convergence backbone for the GRT MultipointPV chain | LOAD-BEARING |
| 23 | `InteriorContourIntegral.lean` | 487 | Interior contour-integral lemmas for Dixon's theorem | LOAD-BEARING |
| 24 | `GeneralizedResidueTheory/PVInfrastructure/SingularAnnulus.lean` | 482 | Singular-annulus PV infrastructure | LOAD-BEARING |
| 25 | `HungerbuhlerWasem/HigherOrderAsymptotics.lean` | 477 | F-diff asymptotic chain (T-SC-00a) | LOAD-BEARING |
| 26 | `DixonTheorem.lean` | 476 | Dixon theorem: null-homologous + bounded ⇒ Dixon function ≡ 0 | LOAD-BEARING |
| 27 | `HungerbuhlerWasem.lean` | 446 | "Central B" `residueTheorem_simplePoles_convex` + corollaries | LOAD-BEARING |
| 28 | `HungerbuhlerWasem/CPVExistence.lean` | 431 | Single transverse-crossing CPV existence | LOAD-BEARING |
| 29 | `ValenceFormula/PVChain/Assembly/ResidueSide.lean` | 407 | The residue-side leaf of the modular ↔ residue equality | LOAD-BEARING |
| 30 | `HungerbuhlerWasem/CrossingDataBuilder.lean` | 407 | Generic `SingleCrossingData` builder from `IsFlatOfOrder _ _ 1` | LOAD-BEARING |

All top-30 are load-bearing on at least one of the two protected theorems. The biggest difference vs the 2026-05-24 ranking is that **`MultiCrossingCPV.lean` dropped from 4,059 → 2,043 (−50%)** thanks to the round-5-wave-5 removal of the non-`_corner` pipeline; `PaperPwC1Immersion.lean` dropped from 1,341 → 503 (−63%) once the `cyclicShift` cluster and `ofClosedPartition` were proven dead; and `HungerbuhlerWasem/Crossing.lean` dropped from 1,583 → 739 (−53%) after the asymmetric/multi-pole helper dead-code waves.

### Top 31–50 files

| # | File | LOC |
|---|---|---|
| 31 | `ValenceFormula/PVChain/Seg5CuspIntegral.lean` | 406 |
| 32 | `CanonicalReps.lean` | 399 |
| 33 | `Seg4FTCProvider.lean` | 389 |
| 34 | `GeneralizedResidueTheory/PVInfrastructure/AnnulusBounds.lean` | 371 |
| 35 | `HungerbuhlerWasem/MultiPoleDCT.lean` | 368 |
| 36 | `SegmentAnalysis.lean` | 367 |
| 37 | `Seg1FTCProvider.lean` | 367 |
| 38 | `VertSegFTCProvider.lean` | 359 |
| 39 | `ArcFTCAtI.lean` | 357 |
| 40 | `GeneralizedResidueTheory/CauchyPrimitive.lean` | 346 |
| 41 | `GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean` | 345 |
| 42 | `ValenceFormula/PVChain/Helpers.lean` | 344 |
| 43 | `ExitTime.lean` | 342 |
| 44 | `ValenceFormula/WindingWeights/Common.lean` | 331 |
| 45 | `ModularInvariance.lean` | 331 |
| 46 | `WindingArgDiff.lean` | 314 |
| 47 | `ValenceFormula.lean` | 307 |
| 48 | `FDBoundary.lean` | 303 |
| 49 | `WindingWeightProofs.lean` | 300 |
| 50 | `GeneralizedResidueTheory/OnCurvePV/Basic.lean` | 299 |

The size distribution flattens sharply after the top 5: the top file (`MultiCrossingCPV.lean`) is 2,043 lines but #6 is already at 810, and #20 sits at 496. There is no longer a small cluster of "giants" dominating the codebase; the long tail of medium files (200–700) holds 65 files and ~22,000 lines.

### Size distribution

| Bucket | File count | Mean LOC | Aggregate LOC | % of project |
|---|---|---|---|---|
| XL (≥1,500) | 1 | 2,043 | 2,043 | 5.5% |
| Large (700–1,499) | 7 | 882 | 6,177 | 16.6% |
| Medium-Large (500–699) | 16 | 591 | 9,452 | 25.4% |
| Medium (300–499) | 28 | 391 | 10,953 | 29.4% |
| Small-Medium (200–299) | 21 | 240 | 5,030 | 13.5% |
| Small (100–199) | 22 | 152 | 3,355 | 9.0% |
| Tiny (<100) | 25 | 60 | 1,500 | 4.0% |

Half the LOC sits in 24 files (XL + Large + Medium-Large together). Aggressive consolidation of the long tail beyond these 24 files yields diminishing returns; the median yield-per-file is at most ~10-15 LOC.

---

## Part 2: Dependency walk

`LeanModularForms.lean` imports 44 leaf modules. A transitive-import walk from the umbrella reaches all 120 files. **Zero orphans** remain.

* Protected theorem `valence_formula_textbook` chain (depth-first names):
  `ValenceFormulaFinal → ValenceFormulaBridged → ResidueSideBridge → FDBoundaryReparametrization → (FDBoundary + FDBoundaryH + FDBoundaryPath + CauchyPrincipalValue + ClassicalCPV + GeneralizedWindingNumber) → … → ValenceFormula/PVChain/Assembly{,.ResidueSide,.Helpers,.OnCurveCapture,.Seg5CuspIntegral,.ArcContribution} + ValenceFormula/WindingWeights/{Common,I,Rho,RhoPlusOne} + ValenceFormula/OnCurvePV/{Basic,EndpointCorner,Main} + ValenceFormula/Boundary/{Bounds,Smooth} + ModularInvariance + EllipticPoints + Orbits + OrbitPairing + CanonicalReps + CoreIdentityProof + …`
* Protected theorem `hw_3_3_clean_full_mero` chain (depth-first names):
  `HW33Clean → HungerbuhlerWasem/MultiCrossingCPV → HungerbuhlerWasem/{Crossing, CPVExistence, CPVExistenceMulti, CrossingCPV, CrossingDataBuilder, CrossingHigherOrder, HigherOrderAsymptotics, LaurentExtraction, LocalCutoffs, MultiPoleDCT, SectorCancellation} → HungerbuhlerWasem.lean + PaperPwC1Immersion + AsymmetricSingleCrossing + GeneralizedResidueTheory/{Residue, Residue/GeneralizedTheoremBase, Residue/MultipointPV, Residue/MultipointPV/DominatedConvergence, …} + DixonTheorem + DixonDiff + …`

The two chains share the `GeneralizedResidueTheory/Residue` family, the now-deduplicated `MultipointPV` pair (`ForMathlib/MultipointPV.lean` at 157 lines plus `GeneralizedResidueTheory/Residue/MultipointPV.lean` at 283 — both load-bearing), the `PiecewiseC1Path`/`PwC1Immersion` curve types, and the `CauchyPrincipalValue` core.

A useful refinement from the round 4–7 sweep: the previous overview asserted "all 135 files are reachable", which was correct as a transitive-closure statement *but* it understated the reality that many of those files participated in pipelines whose endpoints were dead. The forward-reachability filter caught these by asking "which named declarations are actually used to type-check `hw_3_3_clean_full_mero` or `valence_formula_textbook`?", then sweeping out the rest. Result: ~6,700 lines of long pipelines (most notably the entire `WindingNumber/Proposition2_2.lean` chain, the non-corner arm of `MultiCrossingCPV.lean`, and `ExitTimeExcision.lean`) were proven dead despite being reachable from the umbrella.

### Shared infrastructure between the two protected chains

Approximately 60% of the dependency closure is shared between `hw_3_3_clean_full_mero` and `valence_formula_textbook`. The shared core includes:

* **Curve types** (`PiecewiseC1Path`, `PwC1Immersion`, `ClosedPwC1Immersion`, `PiecewiseC1PathOn`, `PiecewiseC1Curve`).
* **Cauchy PV core** (`CauchyPrincipalValue.lean`, `ClassicalCPV.lean`).
* **Winding number machinery** (`GeneralizedWindingNumber.lean`, `WindingInteger.lean`, `WindingArgDiff.lean`).
* **GRT residue family** (`Residue.lean`, `Residue/MeasureHelpers.lean`, `Residue/MultipointPV.lean`).
* **MultipointPV pair** (`ForMathlib/MultipointPV.lean` 157 + `GeneralizedResidueTheory/Residue/MultipointPV.lean` 283).
* **PV infrastructure** (`PVInfrastructure/AnnulusBounds.lean`, `SingularAnnulus.lean`, `StepBounds.lean`, `UniformStepBound.lean`, `GammaAnalysis.lean`, `RemainderAnalysis.lean`).
* **Contour integral** (`ContourIntegral/CrossingLimit.lean`, `PVSplit.lean`, `SegmentFTC.lean`).

The HW33-exclusive part is the `HungerbuhlerWasem/` subtree (6,802 LOC, 12 files) plus `PaperPwC1Immersion.lean`, `AsymmetricSingleCrossing.lean`, `DixonTheorem.lean`, `DixonDiff.lean`, `HungerbuhlerWasem.lean`.

The valence-exclusive part is the `ValenceFormula/` subtree (8,190 LOC, 16 files) plus `ValenceFormula.lean`, `CanonicalReps.lean`, `Orbits.lean`, `OrbitPairing.lean`, `EllipticPoints.lean`, `CoreIdentityProof.lean`, `ModularInvariance.lean`, FD-boundary triple (303+265+218 = 786), `ResidueSideBridge.lean`, `ValenceFormulaBridged.lean`, `Seg{1,4}FTCProvider.lean`, `VertSegFTCProvider.lean`, `ArcGenericFTCProvider.lean`, `ArcFTCAtI.lean`, `CornerFTCAtRho.lean`, `BoundaryWinding*` files.

---

## Part 3: Mathlib API audit

### 3.1 `HasSimplePoleAt` — unified (single canonical definition)

Resolved in an earlier commit. Single canonical definition lives in `ForMathlib/Residue.lean:35`. The GRT file `ForMathlib/GeneralizedResidueTheory/Residue.lean` references the canonical definition. No further action required for in-project use; long-term, redefining as `abbrev` over `MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ = -1` would let the bridge file collapse. Note `MeromorphicBridge.lean` was removed entirely (commit `75c7265` in round 5).

### 3.2 `HasCauchyPV` / `HasCauchyPVOn` — no mathlib equivalent (KEEP, upstream candidate)

* Project: `ForMathlib/CauchyPrincipalValue.lean:85` and `:165`.
* Mathlib has no integral-PV API.
* Action: **NOT in mathlib but should be**. Definition is clean (tendsto-first) and used universally throughout HW machinery and valence chain. Keep canonical, upstream once API is settled. The competing `cauchyPrincipalValueOn` re-definition in `GeneralizedResidueTheory/Residue.lean` was removed in Phase 6.

### 3.3 `HasGeneralizedWindingNumber` — no mathlib equivalent (KEEP, upstream candidate)

* Project: `ForMathlib/GeneralizedWindingNumber.lean:62`.
* Mathlib has only `circleIntegral` and Cauchy-formula winding for holomorphic discs; no piecewise-C¹ general curve API.
* Action: **NOT in mathlib but should be**. Foundational, used in both protected chains. Upstream candidate after stabilisation.

### 3.4 Curve types — narrowed but not flat

Project still carries:

* `PiecewiseC1Path x y` (`PiecewiseC1Path.lean:54`).
* `PwC1Immersion x y` (`PiecewiseC1Path.lean:115`).
* `PiecewiseC1Curve` (`ClassicalCPV.lean:52`, no-endpoints — used by 8 GRT/ValenceFormula files).
* `ClosedPwC1Curve x` + `ClosedPwC1Immersion x` (`PaperPwC1Immersion.lean:77`, post-prune).
* `PiecewiseC1PathOn a b hab x y` (`PiecewiseC1PathOn.lean:51`, free-interval form).

The `cyclicShift` invariance suite that previously bridged `ClosedPwC1Immersion` to the other forms was removed (round 5 wave 11, −520 lines). The basepoint structural residual `hx_notin_S` in `hw_3_3_clean_full_mero` is now satisfied at the call site by every practical caller (see the docstring); the formal `cyclicShift`-based bridge survives only in `PaperPwC1Immersion.lean`.

Action: **PARTIAL match**. Keep `PiecewiseC1Path` canonical; long-term, express `PiecewiseC1Curve` as `Σ x, PiecewiseC1Path x x` and let the bridge between the legacy and GRT chains collapse. Estimated harvest after this refactor: ~200 LOC, mostly in `ClassicalCPV.lean` and `CauchyPrincipalValue.lean`.

### 3.5 FD-boundary triple — still alive

`FDBoundary.lean` 303, `FDBoundaryH.lean` 265, `FDBoundaryReparametrization.lean` 218, `FDBoundaryPath.lean` 204. The legacy `[0,1]` parametrisation (`FDBoundary`) and the `[0,5]` parametrisation (`FDBoundaryH`) coexist; `FDBoundaryReparametrization` is the bridge. The 5-fold concat machinery (`concat₅`) that was once present was deleted as orphan during round 4. Re-adding it inside the chosen canonical FD parametrisation, then deleting the legacy chain, is still the cleanest path forward.

Estimated harvest: ~400 LOC across `FDBoundary.lean` + `FDBoundaryReparametrization.lean` + `ResidueSideBridge.lean` + a fraction of `ValenceFormulaBridged.lean`. Risk: medium — both chains touch `valence_formula_textbook` indirectly via `WindingWeights`.

### 3.6 Trig + small upstreamables

`TrigLemmas.lean` (30 lines, three trig facts) and `Instances.lean` (31 lines, `IsScalarTower ℝ ℂ ℂ`) remain upstream candidates. Their removal awaits the upstream PRs landing.

---

## Part 4: Remaining structural duplications

The 2026-05-24 overview listed 17 numbered duplication clusters. Many are now resolved. The current short-list:

| # | Cluster | Loc A | Loc B | Status / harvest |
|---|---|---|---|---|
| 1 | `BoundaryWindingSeg{1,4}Proof.lean` | 256 | 224 | **near-mirror**, *still open*; factor over `side : ℂ ∈ {1/2, -1/2}` (~80 LOC) |
| 2 | `Seg{1,4}FTCProvider.lean` + `VertSegFTCProvider.lean` | 367 | 389 | partly shared via `VertSegFTCProvider.lean` (359); collapse fully into side-parametrised file (~150 LOC) |
| 3 | FD-boundary triple | `FDBoundary.lean` 303 | `FDBoundaryH.lean` 265 + `FDBoundaryReparametrization.lean` 218 | **still open**; pick `[0,5]`; delete the other two (~400 LOC) |
| 4 | `WindingWeights/{I,Rho,RhoPlusOne}` | 860 + 611 + 664 = 2,135 | share Common.lean (331) | **still open**; parametrise over elliptic point (~400 LOC, medium risk) |
| 5 | `BoundaryWindingArcProof` + `Seg{1,4}Proof` | 288 + 256 + 224 | three-way parallel | extract a `*Of_data*` builder (~120 LOC) |
| 6 | `MultipointPV.lean` (157) vs `GeneralizedResidueTheory/Residue/MultipointPV.lean` (283) + `DominatedConvergence.lean` (492) | legacy chain vs GRT chain | overlapping API surfaces | merge possible only after the curve-type unification (§3.4) |
| 7 | `ResidueSide.lean` (103) vs `ResidueSideBridge.lean` (67) | both load-bearing | structural — `ResidueSideBridge` exists only because the FD triple isn't collapsed | absorbs into canonical residue-side once §3.5 is done |
| 8 | `ResidueCircleIntegral.lean` (82) vs `SimplePoleIntegral.lean` (60) | both compute simple-pole contour integrals | near-duplicate API; could share a common lemma (~30 LOC) |

### Top duplication action items (concrete)

* **F4 (still open)** — `BoundaryWindingSeg{1,4}Proof` → single side-parametrised file. ~80 LOC saving.
* **F5 (partly done)** — `Seg{1,4}FTCProvider` → single `VertSegFTCProvider`. ~150 LOC saving (shared scaffold already exists at 359 LOC; collapse the per-side specialisations).
* **F6 (still open)** — FD-boundary triple → single `[0,5]` parametrisation. ~400 LOC saving including cascade. Highest-risk item on the list because both protected theorems pass through this chain.
* **F11 (still open)** — `BoundaryWindingArcProof` + `Seg{1,4}Proof` extract a single `SmoothBoundaryWindingData.ofPiece` builder. ~120 LOC.
* **F12 (still open)** — `WindingWeights/{I,Rho,RhoPlusOne}` share the 5-step elliptic-point scaffold. Parametrising over the crossing point and per-point cutoff would save ~400 LOC. Higher risk because the geometric proofs differ per point.

---

## Part 5: Generalization opportunities

The project surface that's not already maximally general is small. The 2026-05-24 list (G1–G6) remains essentially valid; nothing has been generalised since then but nothing has been *un*generalised either:

* G1: `PiecewiseC1Path` already takes general normed `E`.
* G2: `HasGeneralizedWindingNumber` takes general curve endpoints; the target point is ℂ-specific.
* G3: `meromorphicOrderAt` adaptation is upstream-already-general.
* G4: HW machinery is fundamentally ℂ-specific.
* G5: `principalPartSum` over `Finset ℂ` could be `Fintype ι` — 1-line definitional change.
* G6: FD-boundary geometry is SL₂(ℤ)-specific — do **NOT** generalise.

---

## Part 6: API improvements

### A1: `@[simp]` count is 10 across 120 files (down from 25/135)

The simp surface is small. The remaining tags concentrate in `Orbits.lean`, `ClassicalCPV.lean`, `CauchyPrincipalValue.lean`, `PiecewiseC1Path.lean`, and `PiecewiseC1PathOn.lean`. The earlier 25-tag count included tags on now-dead declarations; the in-flight 10 are the load-bearing ones.

### A2: `@[fun_prop]` count is 0 across 120 files

`fun_prop` discharges `Continuous`, `Differentiable`, `MeasurableSet`, `AEStronglyMeasurable`. The project does a lot of `Continuous`/`DifferentiableAt` plumbing by hand. Adding a handful of tags (notably on `principalPartSum_differentiableOn`, `HasCauchyPVOn.continuousOn_integrand`, `fdBoundaryFun_continuous`, `fdBoundary_H_continuous`) would shorten downstream callers measurably.

### A3: Missing companion lemmas

| Concept | Missing | Estimated saving |
|---|---|---|
| `HasCauchyPVOn` | `_const_mul`, `_smul`, `_neg` | ~15 LOC |
| `HasGeneralizedWindingNumber` | `_const_mul`, `_neg`, `_add` | ~20 LOC |
| `PiecewiseC1Path` | `_trans` (5-fold), `_symm`, `_extend_unique` | ~50 LOC (currently scattered ad-hoc) |

`principalPartSum_*` companions vanished from the urgency list once `PrincipalPart.lean` was deleted as orphan (round 4 wave 6); the remaining callers in the live tree are few.

### A4: Missing `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_order_pos`

Used implicitly in `WindingWeights/I.lean`, `Rho.lean`, `RhoPlusOne.lean` and in `Assembly/ResidueSide.lean` — proved ad-hoc each time. Direct upstream candidate.

---

## Part 7: What's load-bearing vs. untouchable

The "untouchable" set is small. Modifying any of these without thorough axiom-checking risks regressing the protected theorems:

1. **`HungerbuhlerWasem/MultiCrossingCPV.lean` (2,043 lines)** — the heart of the HW33 paper-faithful chain. The corner-only pipeline that survives is the *minimal* one needed by `residueTheorem_crossing_paper_faithful_clean`. Five `theorem`s extend each other in a delicate chain.
2. **`HW33Clean.lean` (82 lines) + `ValenceFormulaFinal.lean` (70 lines)** — the protected theorem files. Both verify with `[propext, Classical.choice, Quot.sound]`. Treat as read-only.
3. **`PaperPwC1Immersion.lean` (503 lines)** — post-prune; the surviving content is the `ClosedPwC1Immersion`/`ClosedPwC1Curve` types and the residual `cyclicShift`-via-`τ ∈ Ioo 0 1` infrastructure mentioned in the `hw_3_3_clean_full_mero` docstring. Previously co-existed with a 767-line `PaperPwC1ImmersionInvariance.lean` which was deleted entirely (round 3, commit `573f29f`).
4. **`ValenceFormula/PVChain/Assembly.lean` (711 lines) + `Assembly/ResidueSide.lean` (407 lines)** — the modular ↔ residue equality. Touching either requires a careful axiom check on `valence_formula_textbook`.
5. **`GeneralizedResidueTheory/Residue/MultipointPV/DominatedConvergence.lean` (492 lines)** — the DCT backbone of the GRT chain.
6. **`HungerbuhlerWasem/LocalCutoffs.lean` (1,068 lines)** — the exit-time cutoff infrastructure. Subtle.

### What's load-bearing but golf-able

Everything below the top-10 is fair game for proof golf and structural refactoring, with the usual `axiom_check_clean` gate after each batch. The recent waves 4–8 of "decompose long proofs" show the pattern is sustainable: each wave was ~10 helpers extracted per commit, ~50–100 LOC reduction per wave.

### Files most likely to yield further savings

The candidates for the next `/cleanup-all` orchestrator pass, prioritised by current LOC and expected yield:

| File | Current LOC | Estimated yield | Risk |
|---|---|---|---|
| `ArcGenericFTCProvider.lean` | 810 | 80–120 LOC golf | Low (stable post-F5) |
| `ValenceFormula/PVChain/ResidueSideInfra.lean` | 616 | 60–100 LOC golf | Low |
| `DixonDiff.lean` | 614 | 60–90 LOC golf | Low |
| `HungerbuhlerWasem/LaurentExtraction.lean` | 590 | 50–80 LOC golf | Medium (touches HW33 chain) |
| `ValenceFormula/PVChain/ArcContribution.lean` | 560 | 50–80 LOC golf | Low |
| `CoreIdentityProof.lean` | 503 | 40–80 LOC golf | Low |
| `CrossingAtRho.lean` | 496 | 40–70 LOC golf | Low |
| `WindingInteger.lean` | 496 | 40–60 LOC golf | Low |
| `InteriorContourIntegral.lean` | 487 | 40–60 LOC golf | Low |
| `HungerbuhlerWasem/HigherOrderAsymptotics.lean` | 477 | 30–60 LOC golf | Medium (touches HW33 chain) |
| `DixonTheorem.lean` | 476 | 30–60 LOC golf | Low |
| `HungerbuhlerWasem.lean` | 446 | 30–50 LOC golf | Low (only the barrel layer) |

Aggregate: 12 files, ~6,500 combined LOC, expected yield ~600–900 LOC at the optimistic end.

---

## Part 8: Honest forward outlook

This section deliberately replaces the optimistic phased plan in earlier overviews. The realistic-next-phase savings, *given that the project is already at 58% reduction*, are modest.

### Tier A — clean, low-risk savings (~−800 to −1,200 LOC)

* **F4 + F5 + F11** (side-mirror unification): ~−350 LOC.
* **F12** (WindingWeights elliptic-point parametrisation): ~−400 LOC, *medium* risk.
* **Small-tail dead-decl sweeps** of files in the 200–500 LOC range that haven't yet been touched: empirically ~5–10% savings per file, so ~50 files × ~15 LOC each = ~−500 LOC over a long calendar.

### Tier B — structural, medium-risk (~−500 to −800 LOC)

* **F6** (FD-boundary triple collapse): ~−400 LOC, but high risk because both protected theorems pass through. Requires re-adding `PiecewiseC1PathOn.concat` infrastructure.
* **§3.4 curve-type unification**: ~−200 LOC after the long-tail follow-on, but the prerequisite for **J7** (MultipointPV merge).

### Tier C — long-horizon (calendar weeks, not days) (~−200 to −400 LOC locally)

* **Mathlib upstream PRs** for `HasGeneralizedWindingNumber`, `HasCauchyPV{On}`, `MeromorphicAt.logDeriv_*`, and trig lemmas. Each is roughly 2 weeks calendar end-to-end; the local saving on landing is small but the *qualitative* benefit (downstream proofs collapse on mathlib idioms) is large.

### What's NOT achievable

The 2026-05-22 `CONSOLIDATION_PLAN.md` hoped for a 20k floor; that's now confirmed mathematically out of reach. The dependency closure of the two protected theorems contains:

* The full HW33 multi-crossing CPV machinery: ~6,000 LOC even after maximum golf (HungerbuhlerWasem/ subtree).
* The full valence-formula chain including the three WindingWeights files and the FD-boundary integration: ~8,000 LOC even after F6 + F12.
* The GRT residue chain with multipoint PV decomposition and DCT: ~3,500 LOC.
* Curve types + winding number + Cauchy PV core: ~2,000 LOC after upstream.
* Dixon theorem + Cauchy infrastructure: ~1,000 LOC.
* Modular-side / orbit-pairing / canonical-reps: ~1,500 LOC.

That's a ~22,000-line lower bound on the dependency closure of the two protected theorems with realistic generality preserved. The realistic floor is therefore **30k–34k**, not 20k. (The detailed accounting is in `CONSOLIDATION_PLAN.md` §6.)

The 37,211-line current state is ~3k–7k above that floor. Further savings beyond Tier A+B compound slowly and require either substantial calendar time (Tier C) or *scope-down decisions* (removing generality the project chose to formalise).

### Calendar-time projections

| Milestone | LOC | Calendar from 2026-05-25 | Confidence |
|---|---|---|---|
| Tier A complete (long-tail golf) | ~35,000 | 4 weeks active | High |
| Tier A + F12 done | ~34,500 | 6 weeks active | Medium-high |
| Tier A + F4+F5+F11+F12 done | ~34,000 | 8 weeks active | Medium |
| Tier A + B + F6 done | ~33,500 | 12 weeks active | Medium |
| Plus 2-3 mathlib PRs landed | ~33,000 | 16 weeks calendar | Medium |
| Plus all 6 mathlib PRs landed | ~32,300 | 20 weeks calendar | Low-medium |
| Plus aggressive long-tail golf (50% yield) | ~31,000 | 30+ weeks calendar | Low |
| Realistic floor (preserving generality) | ~30,500 | indefinite | reasoning-based |

The reasoning-based floor of ~30.5k is the line below which further reduction requires *scope decisions*, not consolidation. Identifying which decision to make (drop GRT generality? specialise HW33 to single-pole? specialise valence formula to weight 12?) is a mathematical question, not an engineering one.

---

## DO NOT TOUCH list

Load-bearing for at least one protected theorem, currently in clean working order, and high-risk-to-edit. Any "improvement" that destabilises these is net-negative:

1. **`HungerbuhlerWasem/MultiCrossingCPV.lean` (2,043 lines)** — the heart of the HW33 proof. The corner-only pipeline is delicate.
2. **`HW33Clean.lean` (82 lines) + `ValenceFormulaFinal.lean` (70 lines)** — read-only.
3. **`PaperPwC1Immersion.lean` (503 lines)** — `ClosedPwC1Immersion`/`ClosedPwC1Curve` types + residual cyclicShift bridge.
4. **`ValenceFormula/PVChain/Assembly.lean` (711) + `Assembly/ResidueSide.lean` (407)** — modular-side ↔ residue-side equality.
5. **`HungerbuhlerWasem/LocalCutoffs.lean` (1,068)** — exit-time cutoff infrastructure.
6. **`CornerFTCAtRho.lean` (1,113)** — the asymmetric-corners machinery the valence formula uses for ρ and ρ+1.
7. **`GeneralizedResidueTheory/Residue/MultipointPV/DominatedConvergence.lean` (492)** — DCT backbone for the GRT chain.

The two protected theorems can survive small local edits to all of the above, but each requires a fresh `lean_verify` axiom check before pushing.

---

## Verification

| Check | Result |
|---|---|
| `LeanModularForms.hw_3_3_clean_full_mero` axioms | `[propext, Classical.choice, Quot.sound]` |
| `valence_formula_textbook` axioms | `[propext, Classical.choice, Quot.sound]` |
| `sorry` / `admit` count in `LeanModularForms/**/*.lean` | **0** |
| `axiom` declarations | **0** |
| `set_option` directives | 3 (in 2 files: `DslopeIntegral.lean` ×2, `PVSplitting.lean` ×1) |
| Orphan files unreachable from `LeanModularForms.lean` | **0** of 120 |
| Build state | green (umbrella + both protected theorems verify) |

---

## Appendix A: Notable historical drops since 2026-05-21

| Wave / commit | LOC delta | Files / decls removed | Lever |
|---|---|---|---|
| Phase 1 orphan-subsystem drop | −14,340 | 40 Modularforms/, 3 SpherePacking/, 4 GRT/WindingNumber orphans, 4 small ForMathlib helpers | A |
| HW33 fan-out collapse | −3,784 | 16 HW33*.lean files → `HW33Clean.lean` only | D |
| `residueTheorem_crossing_*` collapse | included in Phase 2 | 32 → 5 visible variants | D |
| `dixonFunction_eq_zero*` collapse | included in Phase 2 | 13 → 3 variants | D |
| Phase 3 proof-golf | −1,291 | Top 150 long proofs golfed | C |
| Round 5 wave 5 (MultiCrossingCPV non-corner) | −1,470 | 6 non-corner multi-crossing CPV lemmas | dead-decl (new) |
| Round 5 wave 11 (PaperPwC1Immersion cyclicShift) | −520 | `cyclicShift` cluster + `ofClosedPartition` | dead-decl (new) |
| Round 5 wave 10 (CrossingDataBuilder) | −532 | 12 dead CrossingDataBuilder helpers | dead-decl (new) |
| Round 5 wave 9 (CPVExistence) | −514 | 8 dead CPVExistence helpers | dead-decl (new) |
| Round 5 wave 6 (Crossing asymmetric) | −472 | 12 dead asymmetric/multi-pole helpers in Crossing.lean | dead-decl (new) |
| Round 3 wave (PaperPwC1ImmersionInvariance) | −413 | Entire file (767 LOC originally) | dead-decl (new) |
| Round 5 wave 8 (ExitTimeExcision) | −364 | Entire file | dead-decl (new) |
| Round 5 wave 7 (higher-order CPV) | −364 | 5 dead higher-order CPV helpers | dead-decl (new) |
| Round 6 wave 1 (Proposition2_2) | −241 | Proposition2_2.lean | dead-decl (new) |
| Round 5 wave 13 (residueTheorem_avoidance) | −201 | residueTheorem_avoidance + simple-pole CI helpers | dead-decl (new) |
| Round 4 wave 11 (scattered leafs) | −190 | Scattered leaf decls + duplicate ftc_telescope | dead-decl (new) |

The dead-decl harvest dominated the late session in both volume and surprise factor. The pattern: a single round (which is sequenced waves of removals) often unblocks ~3-5× its direct removal in cascaded follow-ons. The 161-candidate harvest single-handedly cut 2,966 lines across 58 files.

---

## Appendix B: Top contributors to current line count, by file ownership

The five subsystems and their share of the project:

* `ForMathlib/` root (curve types + winding + Cauchy PV + FD-boundary + side mirrors + Dixon): 47.6% (17,699 LOC).
* `ForMathlib/ValenceFormula/`: 22.0% (8,190 LOC).
* `ForMathlib/HungerbuhlerWasem/`: 18.3% (6,802 LOC).
* `ForMathlib/GeneralizedResidueTheory/`: 11.2% (4,153 LOC).
* `ForMathlib/ContourIntegral/` + umbrella + protected leaves: 0.8% (503 LOC).

The HW33 chain is now the *smaller* of the two protected chains by file count. This is the reverse of the original 75k-line project, where HW33 dominated. The reason: HW33's dead-code surface was much larger (multi-crossing CPV had ~50% dead branches), whereas the valence formula chain was tighter to begin with because its development was more recent and more constrained by an explicit textbook reference.

---

## Appendix C: Files at risk in the next consolidation pass

These files have grown since the last touch but remain candidates for golf:

| File | LOC | Last touched | Notes |
|---|---|---|---|
| `HungerbuhlerWasem/MultiCrossingCPV.lean` | 2,043 | 2026-05-25 | Several long proofs remain (>200 LOC each) |
| `CornerFTCAtRho.lean` | 1,113 | 2026-05-24 | Untouched in recent golf waves; likely contains 100-200 LOC of golf yield |
| `HungerbuhlerWasem/LocalCutoffs.lean` | 1,068 | 2026-05-24 | Sensitive to dead-decl checks — exit-time cutoff machinery |
| `ValenceFormula/WindingWeights/I.lean` | 860 | 2026-05-23 | The F12 candidate (parametrise over elliptic point) |
| `ValenceFormula/OnCurvePV/Main.lean` | 841 | 2026-05-23 | Long-proof corpus — needs `/cleanup` per-file |
| `ArcGenericFTCProvider.lean` | 810 | 2026-05-22 | Stable post-F5; candidate for golf only |
| `ValenceFormula/PVChain/Assembly.lean` | 711 | 2026-05-23 | High-risk; touches both protected chains |
| `ValenceFormula/WindingWeights/RhoPlusOne.lean` | 664 | 2026-05-23 | F12 candidate |
| `ValenceFormula/Boundary/Smooth.lean` | 636 | 2026-05-23 | Smooth-boundary proofs; some golf yield available |
| `DixonDiff.lean` | 614 | 2026-05-22 | Differentiability infra for Dixon; ~10-15% golf likely |
| `ValenceFormula/WindingWeights/Rho.lean` | 611 | 2026-05-23 | F12 candidate |

For the latest cleanup pacing rules (per the user's memory), each file should be a separate batch with a pause for review between batches. Auto-dispatch is disabled.

---

## Appendix D: Per-namespace contents (current)

### `ForMathlib/HungerbuhlerWasem/` (12 files, 6,802 LOC)

| File | LOC | Role |
|---|---|---|
| `MultiCrossingCPV.lean` | 2,043 | Multi-crossing CPV (corner pipeline) — the heart of HW33 |
| `LocalCutoffs.lean` | 1,068 | Localised exit-time cutoffs (T-BR-Y6c) |
| `Crossing.lean` | 739 | Per-pole CPV composition (T-GL-01) |
| `LaurentExtraction.lean` | 590 | Laurent polar-part extraction |
| `HigherOrderAsymptotics.lean` | 477 | F-diff asymptotic chain (T-SC-00a) |
| `CPVExistence.lean` | 431 | Single transverse-crossing CPV existence |
| `CrossingDataBuilder.lean` | 407 | Generic `SingleCrossingData` builder |
| `MultiPoleDCT.lean` | 368 | Multi-pole dominated convergence |
| `CPVExistenceMulti.lean` | 224 | Multi-crossing CPV existence |
| `CrossingHigherOrder.lean` | 214 | Higher-order CPV discharger (T-BR-03) |
| `SectorCancellation.lean` | 165 | Sector-even cancellation under cond (B) (T-SC-01) |
| `CrossingCPV.lean` | 76 | Crossing-CPV typeclass facade |

### `ForMathlib/ValenceFormula/` (16 files, 8,190 LOC)

| Subdir / File | LOC | Role |
|---|---|---|
| `WindingWeights/I.lean` | 860 | gWN = −1/2 at i |
| `OnCurvePV/Main.lean` | 841 | On-curve PV main theorem |
| `PVChain/Assembly.lean` | 711 | Modular ↔ residue equality assembly |
| `WindingWeights/RhoPlusOne.lean` | 664 | gWN = −1/6 at ρ+1 |
| `Boundary/Smooth.lean` | 636 | FD-boundary smoothness on each segment |
| `PVChain/ResidueSideInfra.lean` | 616 | log-deriv analyticity off zeros + residue-side helpers |
| `WindingWeights/Rho.lean` | 611 | gWN = −1/6 at ρ |
| `PVChain/ArcContribution.lean` | 560 | Arc contribution to the PV chain |
| `OnCurvePV/EndpointCorner.lean` | 503 | Endpoint-corner case of on-curve PV |
| `PVChain/Assembly/ResidueSide.lean` | 407 | Residue-side leaf of the equality |
| `PVChain/Seg5CuspIntegral.lean` | 406 | Segment 5 cusp integral contribution |
| `PVChain/Helpers.lean` | 344 | PV-chain support lemmas |
| `WindingWeights/Common.lean` | 331 | Shared scaffolding for the WindingWeights triple |
| `PVChain/OnCurveCapture.lean` | 269 | On-curve PV capture lemmas |
| `Boundary/Bounds.lean` | 241 | FD-boundary bounds |
| `OnCurvePV/Basic.lean` | 190 | On-curve PV basics |

### `ForMathlib/GeneralizedResidueTheory/` (16 files, 4,153 LOC)

| Subdir / File | LOC | Role |
|---|---|---|
| `Residue.lean` | 575 | GRT residue theory definitions |
| `Residue/MultipointPV/DominatedConvergence.lean` | 492 | DCT backbone for MultipointPV |
| `PVInfrastructure/SingularAnnulus.lean` | 482 | Singular-annulus PV infrastructure |
| `PVInfrastructure/AnnulusBounds.lean` | 371 | Annulus bounds for PV chain |
| `CauchyPrimitive.lean` | 346 | Cauchy primitive on annular regions |
| `Residue/GeneralizedTheoremBase.lean` | 345 | Base theorem statement |
| `OnCurvePV/Basic.lean` | 299 | OnCurvePV basics for GRT |
| `Residue/MultipointPV.lean` | 283 | MultipointPV main decomposition |
| `PVInfrastructure/StepBounds.lean` | 210 | Step bound infrastructure |
| `PVInfrastructure/RemainderAnalysis.lean` | 187 | Remainder analysis |
| `PVInfrastructure/UniformStepBound.lean` | 186 | Uniform step bound |
| `PVInfrastructure/GammaAnalysis.lean` | 119 | Gamma analysis |
| `Residue/MeasureHelpers.lean` | 94 | Measure-theoretic helpers |
| `ArcCalculus.lean` | 76 | Arc-specific calculus helpers |
| `Homotopy/Invariance.lean` | 56 | Homotopy invariance |
| `Homotopy/Integrality.lean` | 32 | Homotopy integrality |

### `ForMathlib/ContourIntegral/` (3 files, 307 LOC)

| File | LOC | Role |
|---|---|---|
| `CrossingLimit.lean` | 151 | Crossing-limit contour-integral lemmas |
| `PVSplit.lean` | 104 | PV-split contour-integral lemmas |
| `SegmentFTC.lean` | 52 | Segment FTC support |

The `ContourIntegral/` namespace is the thinnest — three small files providing precisely the bridge lemmas needed by the umbrella's full chain.
