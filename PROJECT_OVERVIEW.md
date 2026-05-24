# Project Overview: LeanModularForms

**Generated**: 2026-05-24 (refresh after 39-commit cleanup wave; previous version was 2026-05-21 at 75 727 lines).
**Scope**: entire `LeanModularForms/` tree — 135 `.lean` files, 52 073 lines.
**Branch**: `feat/mathlib-prs`
**Supersedes**: previous `PROJECT_OVERVIEW.md` from 2026-05-21 (now stale; `Modularforms/`, `SpherePacking/` and the 51-file Phase-1 orphan ring have since been dropped, and the `HW33*` / `residueTheorem_crossing_*` / `dixonFunction_eq_zero` variant ratchets have been collapsed to their canonical statements).

---

## Executive Summary

LeanModularForms is a Lean 4 / Mathlib project formalising:

* the **Hungerbühler–Wasem generalised residue theorem** (HW Theorem 3.3) in its maximally general multi-crossing higher-order meromorphic form, and
* the **textbook valence formula** for weight-`k` modular forms on `SL₂(ℤ)`.

The two **protected theorems** (both verifying with axioms `[propext, Classical.choice, Quot.sound]` — no extras):

| Theorem | File | Lines |
|---|---|---|
| `LeanModularForms.hw_3_3_clean_full_mero` | `ForMathlib/HW33Clean.lean` | 84 |
| `valence_formula_textbook` | `ForMathlib/ValenceFormulaFinal.lean` | 70 |

The codebase used to fan out to ~220 files / ~88 000 lines but has been compressed by ~41 % since then. The biggest savings came from (a) dropping the `Modularforms/` and `SpherePacking/` subtrees that were not on the dep chain of either protected theorem, (b) collapsing the `HW33*` variant fan-out (16 files → 1, −3 784 lines), (c) merging the `residueTheorem_crossing_*` cluster (32 → 5 variants), (d) a 5-wave golf-and-decompose pass on the remaining proofs (−1 291 lines), and (e) a Phase-6 sweep of unreferenced decls and orphan files (−2 851 lines combined).

The remaining structure is **lean but not flat**. Three concrete patterns dominate the surface:

1. **Side-mirror twins still mostly intact** — `BoundaryWindingSeg{1,4}Proof`, `Seg{1,4}FTCProvider`, `WindingWeights/{I,Rho,RhoPlusOne}`. A partial `VertSegFTCProvider.lean` extraction exists (207 lines) but neither provider has been collapsed into a single side-parametrised file. Estimated harvest: ~600 lines if executed properly.
2. **FD-boundary triple still alive** — `FDBoundary.lean` (`[0,1]`), `FDBoundaryH.lean` (`[0,5]`) and `FDBoundaryReparametrization.lean` (the glue) coexist. Bridge files `ResidueSideBridge.lean` and `ValenceFormulaBridged.lean` are downstream consequences. Estimated harvest: ~500 lines if the `[0,5]` chain wins.
3. **Two HungerbuhlerWasem giants** — `MultiCrossingCPV.lean` (4 059 lines) and `Crossing.lean` (1 583 lines) carry the heavy proof work. Both are load-bearing for `hw_3_3_clean_full_mero`. Further savings here require generalisation / shared infrastructure, not duplication removal.

A pleasant finding: with `Modularforms/` and `SpherePacking/` gone there are **zero sorries** in the project, **zero `axiom` declarations**, and only **three `set_option` directives** (two `respectTransparency false` in `DslopeIntegral.lean` and one `linter.unusedVariables false` in `PVSplitting.lean`).

## Statistics

| Metric | Value |
|---|---|
| Files | 135 |
| Total lines | 52 073 |
| Total declarations (`theorem`/`lemma`/`def`/…) | 2 277 |
| Sorries | **0** |
| Axiom declarations | **0** |
| `set_option` directives | 3 (in 2 files) |
| File size: tiny (<50 lines) | 2 |
| File size: small (50–200) | 41 |
| File size: medium (200–700) | 78 |
| File size: large (700–1500) | 12 |
| File size: XL (≥1500) | 2 (`MultiCrossingCPV` 4 059, `Crossing` 1 583) |
| `@[simp]` attributes | 25 |
| `@[fun_prop]` attributes | 0 |
| Orphan files (unreachable from `LeanModularForms.lean`) | **0** |

---

## Part 1: Inventory at Scale

### Namespace bucket (file × LOC)

| Bucket | Files | LOC | Notes |
|---|---|---|---|
| `ForMathlib/` (root) | 79 | 22 886 | The general-purpose analytic infrastructure: curve types, Cauchy PV, winding, principal parts, Dixon theorem, FD-boundary, FTC providers, side-mirror data. |
| `ForMathlib/HungerbuhlerWasem/` | 14 | 12 539 | The full HW machinery: per-pole CPV composition, multi-crossing CPV existence, exit-time excision, Laurent extraction, higher-order asymptotics, sector cancellation, multi-pole DCT, local cutoffs. |
| `ForMathlib/ValenceFormula/` | 13 | 8 363 | The valence-formula chain proper: PV chain assembly, modular-side residue-side equality, boundary smoothness/bounds, winding weights at i / ρ / ρ+1, on-curve PV decomposition. |
| `ForMathlib/GeneralizedResidueTheory/` | 21 | 7 835 | The "second" residue chain (used by HW33 and indirectly by the valence formula via the GRT bridge): residue+CPV definitions, sector-curve PV lemma, multi-point PV decomposition, homotopy invariance, winding-number Proposition 2.2, principal-value infrastructure (annulus bounds, singular annulus, gamma analysis, remainder analysis, step bounds, uniform step bound). |
| `ForMathlib/ContourIntegral/` | 4 | 450 | Thin slice of contour-integral lemmas used by the winding chain. |
| umbrella `LeanModularForms.lean` | 1 | 53 | Imports all 53 leaf modules including both protected files. |
| protected leaves (`HW33Clean.lean`, `ValenceFormulaFinal.lean`) | 2 | 154 | The two top-level theorems and nothing else. |

### Top 30 files by line count

| # | File | LOC | One-line purpose | Class |
|---|---|---|---|---|
| 1 | `HungerbuhlerWasem/MultiCrossingCPV.lean` | 4 059 | Multi-crossing CPV existence (T-BR-Y9d, Y9e) for arbitrary cardinality singularity sets | LOAD-BEARING |
| 2 | `HungerbuhlerWasem/Crossing.lean` | 1 583 | Per-pole CPV composition (T-GL-01) culminating in `residueTheorem_crossing_truly_full_spec` | LOAD-BEARING |
| 3 | `PaperPwC1Immersion.lean` | 1 341 | Paper-faithful `ClosedPwC1Immersion`/`ClosedPwC1Curve` types + `cyclicShift` invariance core | LOAD-BEARING |
| 4 | `HungerbuhlerWasem/LocalCutoffs.lean` | 1 249 | Localised exit-time cutoffs feeding the multi-crossing CPV (T-BR-Y6c) | LOAD-BEARING |
| 5 | `HungerbuhlerWasem/CPVExistence.lean` | 1 169 | Single transverse-crossing CPV existence | LOAD-BEARING |
| 6 | `HungerbuhlerWasem/CrossingDataBuilder.lean` | 1 120 | Generic `SingleCrossingData` builder from `IsFlatOfOrder _ _ 1` | LOAD-BEARING |
| 7 | `CornerFTCAtRho.lean` | 1 113 | `CornerFTCHyp` at ρ and ρ+1 (the asymmetric corners of the FD) | LOAD-BEARING |
| 8 | `ValenceFormula/WindingWeights/I.lean` | 941 | gWN = −1/2 at i; PV integral tendsto −iπ | LOAD-BEARING |
| 9 | `ValenceFormula/OnCurvePV/Main.lean` | 841 | On-curve PV main theorem (corner crossings + smooth points) | LOAD-BEARING |
| 10 | `GeneralizedResidueTheory/Residue/SectorCurveLemma.lean` | 812 | Sector-curve PV Lemma 3.1 from HW | LOAD-BEARING |
| 11 | `ArcGenericFTCProvider.lean` | 810 | `ArcFTCHyp` at a generic angle on the unit-circle arc | LOAD-BEARING |
| 12 | `PaperPwC1ImmersionInvariance.lean` | 767 | Cyclic-shift invariance for HasCauchyPVOn / gWN / IsNullHomologous / CondA' / CondB | LOAD-BEARING |
| 13 | `ValenceFormula/WindingWeights/RhoPlusOne.lean` | 718 | gWN = −1/6 at ρ+1; PV integral tendsto −iπ/3 | LOAD-BEARING |
| 14 | `ValenceFormula/PVChain/Assembly.lean` | 711 | Modular-side ↔ residue-side equality assembly | LOAD-BEARING |
| 15 | `ValenceFormula/Boundary/Smooth.lean` | 693 | FD-boundary smoothness on each open segment | LOAD-BEARING |
| 16 | `HungerbuhlerWasem.lean` | 688 | "Central B" `residueTheorem_simplePoles_convex` + four corollaries | LOAD-BEARING |
| 17 | `ValenceFormula/WindingWeights/Rho.lean` | 657 | gWN = −1/6 at ρ; PV integral tendsto −iπ/3 | LOAD-BEARING |
| 18 | `DixonDiff.lean` | 653 | Dixon h2 holomorphic off curve, h1 holomorphic everywhere | LOAD-BEARING |
| 19 | `DixonTheorem.lean` | 650 | Dixon theorem: null-homologous + bounded ⇒ Dixon function ≡ 0 | LOAD-BEARING |
| 20 | `ValenceFormula/PVChain/ResidueSideInfra.lean` | 616 | log-deriv analyticity off zeros + residue-side helpers | LOAD-BEARING |
| 21 | `HungerbuhlerWasem/LaurentExtraction.lean` | 607 | Extracts Laurent polar-part data into named functions | LOAD-BEARING |
| 22 | `WindingInteger.lean` | 594 | Continuous argument lift + integer-valued winding number | LOAD-BEARING |
| 23 | `HungerbuhlerWasem/CrossingHigherOrder.lean` | 578 | Higher-order CPV discharger (T-BR-03) | LOAD-BEARING |
| 24 | `GeneralizedResidueTheory/Residue.lean` | 575 | GRT residue theory: residue, CPV-on, residue-of-simple-pole, residueAt | LOAD-BEARING |
| 25 | `HungerbuhlerWasem/HigherOrderAsymptotics.lean` | 565 | F-diff asymptotic chain (T-SC-00a) | LOAD-BEARING |
| 25 | `GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean` | 565 | HW Proposition 2.2: finite crossings + isolated crossing intervals | LOAD-BEARING |
| 27 | `ValenceFormula/PVChain/ArcContribution.lean` | 560 | Arc contribution to the PV chain | LOAD-BEARING |
| 28 | `GeneralizedResidueTheory/Residue/SectorCurve.lean` | 534 | Sector-curve PV Lemma 3.1 (statement-level companions) | LOAD-BEARING |
| 29 | `HungerbuhlerWasem/SectorCancellation.lean` | 524 | Sector-even cancellation under condition (B) (T-SC-01) | LOAD-BEARING |
| 30 | `Seg4FTCProvider.lean` | 520 | `ArcFTCHyp` for the left vertical FD edge at a generic point | LOAD-BEARING (side-mirror of #34) |

All top-30 are load-bearing on at least one of the two protected theorems — there are no large "general but unused" files left in the tree.

---

## Part 2: Dependency walk

`LeanModularForms.lean` imports 53 leaf modules. A transitive-import walk from the umbrella reaches all 135 files. **Zero orphans** remain.

* Protected theorem `valence_formula_textbook` chain (depth-first names):
  `ValenceFormulaFinal → ValenceFormulaBridged → ResidueSideBridge → FDBoundaryReparametrization → (FDBoundary + FDBoundaryH + FDBoundaryPath + CauchyPrincipalValue + ClassicalCPV + GeneralizedWindingNumber) → … → ValenceFormula/PVChain/Assembly{,.ResidueSide,.Helpers,.OnCurveCapture,.Seg5CuspIntegral,.ArcContribution} + ValenceFormula/WindingWeights/{Common,I,Rho,RhoPlusOne} + ValenceFormula/OnCurvePV/{Basic,EndpointCorner,Main} + ValenceFormula/Boundary/{Bounds,Smooth} + ModularInvariance + EllipticPoints + Orbits + OrbitPairing + CanonicalReps + …`
* Protected theorem `hw_3_3_clean_full_mero` chain (depth-first names):
  `HW33Clean → HungerbuhlerWasem/MultiCrossingCPV → HungerbuhlerWasem/{Crossing, CPVExistence, CPVExistenceMulti, CrossingCPV, CrossingDataBuilder, CrossingHigherOrder, ExitTimeExcision, HigherOrderAsymptotics, LaurentExtraction, LocalCutoffs, MultiPoleDCT, SectorCancellation} → HungerbuhlerWasem.lean + PaperPwC1Immersion + PaperPwC1ImmersionInvariance + AsymmetricSingleCrossing + GeneralizedResidueTheory/{Residue, WindingNumber/Proposition2_2, …} + DixonTheorem + DixonDiff + …`

Both chains share the `GeneralizedResidueTheory/Residue` family, the `MultipointPV` duplicate pair (now harmless — both files survive but `disjoint_balls_of_small_epsilon` / `finset_discrete_min_sep` were deduplicated in commit `d4ff8fb`), the `PiecewiseC1Path` / `PwC1Immersion` curve types, and the `CauchyPrincipalValue` core.

---

## Part 3: Mathlib API audit (HIGHEST VALUE)

### 3.1 `HasSimplePoleAt` — **now unified** (post-`ea0ac58`)

Status: **resolved** in commit `ea0ac58`. Single canonical definition lives in `ForMathlib/Residue.lean:35`. The GRT file `ForMathlib/GeneralizedResidueTheory/Residue.lean` only references the canonical definition via its `MeasureHelpers` ancestor.

Action: **none** — the in-project unification is complete. Long-term, redefine as `abbrev` over `MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ = -1` so `MeromorphicBridge.lean` collapses to one-or-two `simp` lemmas. That's an upstream/redesign step (5 % of the file's lemmas would survive).

### 3.2 `poleOrderAt` — duplicates `meromorphicOrderAt` (still open)

* Project: `ForMathlib/PrincipalPart.lean:49` defines `poleOrderAt f z₀ : ℕ` via an ad-hoc recursion.
* Mathlib: `meromorphicOrderAt f z₀ : WithTop ℤ` lives in `Mathlib.Analysis.Meromorphic.Order` and is much more general (negative pole orders, holomorphic zeros, undefined).
* Action: **EXISTS in mathlib (partial)** — redefine as `poleOrderAt f z₀ := (-(meromorphicOrderAt f z₀)).untop₀.toNat` or, better, switch downstream callers to a single `meromorphicOrderAt`-based predicate. Bridge into `MeromorphicBridge.lean`.
* Estimate: small (~40 LOC if downstream callers are sparse — `principalPartSum.residue` is the main client).

### 3.3 `HasCauchyPV` / `HasCauchyPVOn` — no mathlib equivalent (KEEP, upstream candidate)

* Project: `ForMathlib/CauchyPrincipalValue.lean:85` and `:165`.
* Mathlib has no integral-PV API.
* Action: **NOT in mathlib but should be**. Definition is clean (tendsto-first), used universally throughout HW machinery and valence chain. Keep canonical, upstream once API is settled. The Phase-6 work already removed the competing `cauchyPrincipalValueOn` re-definition in `GeneralizedResidueTheory/Residue.lean`.

### 3.4 `HasGeneralizedWindingNumber` — no mathlib equivalent (KEEP, upstream candidate)

* Project: `ForMathlib/GeneralizedWindingNumber.lean:62`.
* Mathlib has only `circleIntegral` and Cauchy-formula winding for holomorphic discs; no piecewise-C¹ general curve API.
* Action: **NOT in mathlib but should be**. Foundational, used in both protected chains. Upstream candidate after stabilisation.

### 3.5 `principalPartSum` — locally useful, no direct mathlib (KEEP)

* Project: `ForMathlib/PrincipalPart.lean:65` defines `principalPartSum S c z := ∑ s ∈ S, c s / (z - s)`.
* Mathlib has `Polynomial.partialFractions` (only rational) and `MeromorphicAt.laurent` (asymptotic, not finite sum). Neither replaces the finite-Finset simple-pole sum needed by `HungerbuhlerWasem.lean:618` and `MeromorphicCauchy.lean:64`.
* Action: **GENUINELY local** for now. The companion algebra (`_add`, `_sub`, `_const_mul`, `_const_smul`) is partially missing and would shorten downstream proofs by ~30 LOC.

### 3.6 Four parallel curve types (HIGH PRIORITY — partly addressed)

Project still carries:

* `PiecewiseC1Path x y` (`PiecewiseC1Path.lean:54`, extends `PiecewiseC1PathOn 0 1 _ x y`).
* `PwC1Immersion x y` (`PiecewiseC1Path.lean:115`, adds non-vanishing derivative).
* `PiecewiseC1Curve` (`ClassicalCPV.lean:52`, the "old" no-endpoints version).
* `ClosedPwC1Curve x` + `ClosedPwC1Immersion x` (`PaperPwC1Immersion.lean:77` / `:98`).
* `PiecewiseC1PathOn a b hab x y` (`PiecewiseC1PathOn.lean:51`, free-interval form).

Usage counts (string-grep): `PiecewiseC1Curve` 108 hits, `PwC1Immersion` 1 114 hits, `ClosedPwC1Immersion`/`ClosedPwC1Curve` 256 hits. The `PiecewiseC1Curve` (no-endpoints) usage is concentrated in `ClassicalCPV.lean`, `CauchyPrincipalValue.lean`, and the older `MultipointPV.lean` plumbing — it's the legacy chain that the bridge files `FDBoundaryReparametrization` and `ResidueSideBridge` were created to span.

Action: **PARTIAL match (parallel locally; no mathlib equivalent for the wider notion)**. Keep `PiecewiseC1Path` canonical; express `PiecewiseC1Curve` as `Σ x, PiecewiseC1Path x x`; refactor `ClosedPwC1Curve` to a structural property. This unblocks the bridge-file collapse in §4 and reduces the `cyclicShift` development in `PaperPwC1Immersion{,Invariance}.lean` (currently 1 341 + 767 = 2 108 lines) by an estimated 200 LOC.

### 3.7 `PoincareBridge.lean` — keep (right kind of narrow bridge)

92 lines (was 140 pre-cleanup). Bridge from mathlib `IsExactOn` / convex-set primitive to project `PiecewiseC1Path` contour integration. Keep.

### 3.8 FD-boundary triple — could collapse via `Path.trans` (still open)

`FDBoundary.lean` 340, `FDBoundaryH.lean` 297, `FDBoundaryReparametrization.lean` 218. Mathlib has `Path.trans` (2-fold) and `Path.cast_trans`; the project added a private `PiecewiseC1PathOn.concat` (still alive; see `PiecewiseC1PathOn.lean:129`) but a 5-fold variant (`concat₅`) was added in Phase 4 and then **dropped** in Phase 6 along with its only consumer `FDBoundaryPathOn.lean`. Verifying via `git show`: the `concat₅` API survived as orphan and was deleted.

Action: **partly NOT in mathlib but should be**. Re-add the 5-fold concat (or use 4 nested 2-folds) inside the chosen canonical FD parametrisation, then delete the legacy `[0,1]` chain. Same harvest as in the prior overview (~500 LOC).

---

## Part 4: Moral Duplications (pairwise)

Many old duplicates have been resolved. The remaining picture is much narrower than at 75k. Pairs that **still exist** (status as of 2026-05-24):

| # | Cluster (or pair) | Loc A | Loc B | Status | Action |
|---|---|---|---|---|---|
| 1 | `HasSimplePoleAt` (definition) | `ForMathlib/Residue.lean:35` | (formerly: GRT/Residue.lean:67) | **RESOLVED** (commit `ea0ac58`) | none |
| 2 | `HW33*` flat fan-out | `HW33Clean.lean` only (single canonical) | — | **RESOLVED** (commit `8205c4d`, 16 → 1) | none |
| 3 | `residueTheorem_crossing_*` (was 32) | `Crossing.lean` (3 variants) | `MultiCrossingCPV.lean` (2 variants) | **RESOLVED** (commit `4f3959c`, 32 → 5) | none |
| 4 | `dixonFunction_eq_zero` (was 13) | `DixonTheorem.lean` (3 variants) | — | **RESOLVED** (3 of 13 survive: `_of_nullHomologous_convex_full`, `_of_nullHomologous_open_full`, `_of_nullHomologous_open_full_unbounded`) | none |
| 5 | `BoundaryWindingSeg{1,4}Proof.lean` | 256 lines | 224 lines | **near-mirror**, *still open* | factor over `side : ℂ ∈ {1/2, -1/2}` |
| 6 | `Seg{1,4}FTCProvider.lean` | 500 lines | 520 lines | **near-mirror**, *partly shared via* `VertSegFTCProvider.lean` (207 lines) | finish extraction; collapse both into single side-parametrised file (~+250 LOC moved) |
| 7 | FD-boundary triple | `FDBoundary.lean` (340) | `FDBoundaryH.lean` (297) + `FDBoundaryReparametrization.lean` (218) | **still open** | pick `[0,5]`; delete the other two (~ −500 LOC; cascades through `FDBoundaryPath.lean` 204 LOC and `ResidueSideBridge.lean` 67 LOC) |
| 8 | `eta.lean` / `eta_cleanup.lean` | — | — | **RESOLVED** (Modularforms tree dropped) | none |
| 9 | seg naming clash (was `seg0..4` vs `seg1..5`) | both use `seg1..5` | — | **RESOLVED** (both `WindingWeights/Common.lean` and `Boundary/Bounds.lean` use `seg1..seg5`) | none |
| 10 | `analyticAt_logDeriv_off_zeros{,'}` private duplicate | `ResidueSideInfra.lean:84` | — | **RESOLVED** (only one definition remains; the `'` variant is the public one) | none |
| 11 | `IsScalarTower ℝ ℂ ℂ` quadruplicate | `Instances.lean:31` (only) | — | **RESOLVED** (single instance now) | none |
| 12 | `exists_height_bound_S` vs `exists_height_above_sqrt3_and_S` | `Helpers.lean:201` | `Assembly/ResidueSide.lean:54` (private) | **still open**, near-duplicate | inline one into the other (~20 LOC) |
| 13 | 4 parallel curve types | `PiecewiseC1Path` + `PwC1Immersion` | `PiecewiseC1Curve` + `ClosedPwC1Curve`/`ClosedPwC1Immersion` + `PiecewiseC1PathOn` | **still open** (see §3.6) | unify on `PiecewiseC1Path`; express `Curve` as `Σ x, Path x x`; refactor `Closed` to a structural property |
| 14 | `MultipointPV.lean` vs `GeneralizedResidueTheory/Residue/MultipointPV.lean` | 253 lines | 316 lines + sub-file `DominatedConvergence.lean` (492 lines) | **partially resolved** — internally-duplicated `finset_discrete_min_sep` / `disjoint_balls_of_small_epsilon` were removed in `d4ff8fb`, but the two files still cover overlapping API surfaces (legacy chain vs GRT chain) | merge eventually; both chains are load-bearing today |
| 15 | `ResidueSide.lean` vs `ResidueSideBridge.lean` | 120 lines | 67 lines | structural — the second exists only because the FD-triple isn't yet collapsed | absorbs into the canonical residue-side once §3.8/F7 is done |
| 16 | `ResidueCircleIntegral.lean` (177) vs `SimplePoleIntegral.lean` (130) | both compute the simple-pole contour integral | — | **near-duplicate API** | one is "circle path" the other "single point CPV residue"; could share a common lemma |
| 17 | `BoundaryWindingArcProof.lean` (288) vs `BoundaryWindingSeg{1,4}Proof.lean` | arc / left-vertical / right-vertical variants of `SmoothBoundaryWindingData` | — | three-way parallel | extract a `*Of_data*` builder; saves ~150 LOC |

### Top duplication action items (concrete)

F-items numbered to mirror the prior overview's plan; new estimates after the 41 % shrink.

**F4 (still open)** — `BoundaryWindingSeg{1,4}Proof` → single side-parametrised file. ~80 LOC saving (was ~150 pre-cleanup; smaller now because both files were golfed in Phase 3).

**F5 (still open)** — `Seg{1,4}FTCProvider` → single `VertSegFTCProvider`. ~250 LOC saving. The shared scaffold already exists at 207 LOC; what's left is the *side-specific slitPlane membership and the linear-cutoff orientation*.

**F6 (still open)** — FD-boundary triple → single `[0,5]` parametrisation. ~500 LOC saving including cascade (`FDBoundary`, `FDBoundaryReparametrization`, `ResidueSideBridge`, `FDBoundaryPath` rewrite).

**F11 (new)** — `BoundaryWindingArcProof` + `Seg1Proof` + `Seg4Proof` extract a single `SmoothBoundaryWindingData.ofPiece` builder. ~150 LOC.

**F12 (new)** — `WindingWeights/{I,Rho,RhoPlusOne}` share the same 5-step structure (PV setup → norm bounds → log telescope → log limit → gWN). Parametrising over the crossing point (i, ρ, ρ+1) and the per-point cutoff (`arcsinDelta`, `vertDelta`, asymmetric mix) would save ~400 LOC across the three files. Higher risk because the geometric proofs differ per point (sin/cos identities specialise differently).

---

## Part 5: Generalization opportunities

The project surface that's not already maximally general is small.

### G1: `PiecewiseC1Path` over general normed `E` — already general
Stated for arbitrary `[NormedAddCommGroup E] [NormedSpace ℝ E]`. The bespoke `PiecewiseC1Curve` (no-endpoints) is `ℂ`-specific but only via downstream contour-integral lemmas; the structural definition is `E`-generic.

### G2: `HasGeneralizedWindingNumber` — already general for the curve, ℂ-specific for the target
The definition takes any `PiecewiseC1Path x y` (general endpoints) but the point `z₀` is `ℂ`. Could be generalised to any space where `1/(z - z₀)` makes sense (no value — only ℂ is used).

### G3: `meromorphicOrderAt` adaptation — mathlib is already ℝ/ℂ-agnostic
The shift of §3.2 to `meromorphicOrderAt` automatically generalises the project's `poleOrderAt` from ℂ-functions to `NontriviallyNormedField`-functions. Low yield since the project's poles are ℂ-only, but improves "what's the right level of abstraction" for upstream.

### G4: HW machinery — fundamentally ℂ-specific
The Hungerbühler–Wasem theorem and its CPV / Laurent / sector machinery are ℂ-specific. No generalisation surface.

### G5: `principalPartSum` over a finite Finset — could be over Fintype
Replacing `Finset ℂ` with `Fintype ι` indexing would let the sum range over `ι → ℂ`. Likely a 1-line change in the definition and zero changes downstream. Worth doing if upstreaming.

### G6: FD-boundary geometry is SL₂(ℤ)-specific — do NOT generalise
The seg1..seg5 layout is geometric and tied to the standard fundamental domain. Generalising to `Γ₀(N)`/`Γ(N)` is research-level and outside scope.

---

## Part 6: API improvements

### A1: `@[simp]` count is 25 across 135 files

Very low density. The reluctance is rational (this is heavy real-analysis content with delicate hypotheses) but the lack of simp tags makes `MeromorphicBridge.lean` and `Residue.lean` longer than they need to be at the call site.

### A2: `@[fun_prop]` count is 0 across 135 files

`fun_prop` discharges `Continuous`, `Differentiable`, `MeasurableSet`, `AEStronglyMeasurable`, etc. The project does **a lot** of `Continuous`/`DifferentiableAt` plumbing by hand. Even a single `@[fun_prop]` tag on, say, `principalPartSum_differentiableOn` (`PrincipalPart.lean:76`) would shorten downstream callers in `MeromorphicCauchy.lean` and `HungerbuhlerWasem.lean` measurably.

### A3: Missing companion lemmas

| Concept | Missing | Estimated saving |
|---|---|---|
| `principalPartSum` | `_add`, `_sub`, `_const_mul`, `_const_smul`, `_zero` | ~30 LOC |
| `HasCauchyPVOn` | `_const_mul`, `_smul`, `_neg` (the `.add` and `.sub` exist) | ~15 LOC |
| `HasGeneralizedWindingNumber` | `_const_mul`, `_neg`, `_add` (the curve-side operations are absent) | ~20 LOC |
| `PiecewiseC1Path` | `_trans` (5-fold), `_symm`, `_extend_unique` | ~50 LOC (currently scattered ad-hoc) |
| `ClosedPwC1Immersion` | `_cyclicShift_compose` (the proofs duplicate by hand in `PaperPwC1ImmersionInvariance.lean`) | ~60 LOC |

### A4: Missing `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_order_pos`

Used implicitly in `WindingWeights/I.lean`, `Rho.lean`, `RhoPlusOne.lean` and in `Assembly/ResidueSide.lean` but proved ad-hoc each time. Direct upstream candidate.

### A5: Missing `ClosedPwC1Immersion.cyclicShift_compose` and `_cyclicShift_assoc`

The `cyclicShift` development in `PaperPwC1ImmersionInvariance.lean` re-proves invariance for each of `HasCauchyPVOn`, `generalizedWindingNumber`, `IsNullHomologous`, `SatisfiesConditionA'`, `SatisfiesConditionB`. A single lemma `cyclicShift_compose : (γ.cyclicShift s).cyclicShift t = γ.cyclicShift (s + t mod 1)` would reduce all five invariance proofs to one-line corollaries.

### A6: Missing `IsBoundedAtImInfty.neg` and `zero_at_cusps_of_zero_at_infty`

(These were `J7` in the prior overview, in the now-dropped `Modularforms/` tree. They are upstream candidates that should still be PR'd to mathlib for the benefit of *other* projects, but they're no longer urgent for LeanModularForms.)

---

## Part 7: Junk / removable

The Phase-6 sweep harvested most of the obvious junk. What's left is structural.

### J1: `FDBoundaryReparametrization.lean` (218 lines) — DELETE after F6

Exists solely to bridge the legacy `[0,1]` and the new `[0,5]` parametrisations.

### J2: `ResidueSideBridge.lean` (67 lines) — DELETE after F6

Downstream of `FDBoundaryReparametrization`. Vanishes once F6 is executed.

### J3: `ValenceFormulaBridged.lean` (170 lines) — SHRINK after F6

Most of this file is the *combination* of (a) `valence_formula_unconditional_mkD` + (b) the bridged residue/modular sides. After F6 the bridging vanishes and this file becomes the thin top-level theorem application that `ValenceFormulaFinal.lean` already is. Likely reduces to ~50 LOC.

### J4: `Instances.lean` (31 lines) — UPSTREAM

Single `IsScalarTower ℝ ℂ ℂ := inferInstance` instance. Upstream to mathlib; the `inferInstance` itself works without the manual declaration on most mathlib versions; this file exists as a "guard" against synthesisation gaps that have closed.

### J5: `TrigLemmas.lean` (30 lines) — UPSTREAM

Three trig facts (`exp_real_angle_I`, `cos_two_pi_div_three`, `sin_two_pi_div_three`). Pure mathlib material.

### J6: `MeromorphicBridge.lean` (162 lines) — SHRINK after §3.1 long-term move

Drops to a handful of `simp` lemmas once `HasSimplePoleAt` becomes an abbreviation over `meromorphicOrderAt = -1`. ~140 LOC savable.

### J7: `MultipointPV.lean` (253) + `GeneralizedResidueTheory/Residue/MultipointPV.lean` (316) + `…/MultipointPV/DominatedConvergence.lean` (492) — POTENTIAL MERGE

Two parallel chains (legacy and GRT). Internally-duplicate decls were already removed; what's left is two ~250-line statements of "PV decomposes into sum of single-pole PVs", one using the legacy `PiecewiseC1Path` chain and one using the GRT `cauchyPrincipalValueOn`. Merging requires unifying the curve-type chain first (§3.6) — until then, both stay.

### J8: `ClassicalCPV.lean` (342) — KEEP, but watch

The original `PiecewiseC1Curve` (no-endpoints) home. Load-bearing for `HungerbuhlerWasem.lean` (the central B theorem). Once curve unification (§3.6) is done, this drops to ~150 LOC (just the integration definitions) or vanishes entirely.

---

## Part 8: Recommended action plan

### P1: Quick wins (1–3 days each, low risk) — estimated **−200 to −300 LOC**

* **P1a** Inline `exists_height_above_sqrt3_and_S` into `exists_height_bound_S` (or vice-versa). −20 LOC.
* **P1b** Add the missing `principalPartSum_{add, sub, const_mul, const_smul, zero}` companion lemmas; refactor 4 ad-hoc downstream proofs to use them. Net −30 LOC.
* **P1c** Add `@[fun_prop]` to `principalPartSum_differentiableOn`, `HasCauchyPVOn.continuousOn_integrand`, `fdBoundary_H_continuous`, `fdBoundaryFun_continuous` (4 tags). Refactor downstream proofs that hand-roll the same facts. Estimated −50 LOC.
* **P1d** Add `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_order_pos` (A4). Reuse in 3 places. Net −40 LOC.
* **P1e** Clear the 3 `set_option` directives — investigate whether the underlying definitional-equality / unused-variable issues can be fixed at the source. ~+0 LOC but removes config noise.

### P2: API improvements + extracting `WindingWeights` core (4–6 days, low/medium risk) — estimated **−300 to −400 LOC**

* **P2a** F12: extract a shared 5-step scaffold from `WindingWeights/{I,Rho,RhoPlusOne}.lean`, parametrise over the crossing point and the cutoff function. The geometric trig identities still specialise per point but the chain assembly becomes one helper. Estimated −400 LOC.
* **P2b** Add the `ClosedPwC1Immersion.cyclicShift_compose` lemma (A5) and refactor the 5 invariance proofs in `PaperPwC1ImmersionInvariance.lean`. Estimated −60 LOC.

### P3: Side-mirror unification + FD-triple collapse (1–2 weeks, medium risk) — estimated **−800 LOC**

* **P3a** F4 + F5: complete the `VertSegFTCProvider.lean` extraction; collapse `Seg1FTCProvider`/`Seg4FTCProvider` into a single side-parametrised file (~−250 LOC); collapse `BoundaryWindingSeg{1,4}Proof.lean` similarly (~−80 LOC). Sub-total ~−330 LOC.
* **P3b** F11: extract `SmoothBoundaryWindingData.ofPiece` builder shared by `BoundaryWindingArcProof.lean` and the two side-mirror files. Estimated −150 LOC.
* **P3c** F6: pick `[0,5]` as canonical FD parametrisation; delete `FDBoundary.lean`, `FDBoundaryReparametrization.lean`, `ResidueSideBridge.lean`, shrink `ValenceFormulaBridged.lean`. Sub-total ~−500 LOC.

### P4: Structural — unify curve types (1–2 weeks, higher risk) — estimated **−400 LOC**

* **P4a** §3.6: express `PiecewiseC1Curve = Σ x, PiecewiseC1Path x x`; refactor `ClassicalCPV.lean` and `CauchyPrincipalValue.lean` accordingly. Drops `ClassicalCPV.lean` from 342 to ~150 and lets the bridge between the legacy and GRT MultipointPV chains begin (J7 merge becomes possible).
* **P4b** §3.6: refactor `ClosedPwC1Curve x` / `ClosedPwC1Immersion x` to use a structural `IsClosed`/`IsImmersion` property on `PiecewiseC1Path x x` rather than a new struct. Estimated −150 LOC in `PaperPwC1Immersion{,Invariance}.lean`.

### P5: Mathlib upstream PRs (carryover from prior plan; some now urgent) — estimated **−150 LOC** after merge

* **Up1** `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_order_pos` (A4).
* **Up2** `principalPartSum_{add, sub, const_mul, _const_smul}` + the `Finset → Fintype` generalisation (G5) — clean-room rewrite, suitable for a small first-time-contributor PR.
* **Up3** `Path.trans₅` or `Path.concat₅` — the project already had this code and dropped it as orphan; resurrect for mathlib.
* **Up4** Trig facts `exp_real_angle_I`, `cos_two_pi_div_three`, `sin_two_pi_div_three` (J5).
* **Up5** Long-term: `HasCauchyPV{On}` and `HasGeneralizedWindingNumber` API once stabilised. Large PR; would require design review.

**Honest aggregate**: ~−1 700 LOC achievable across P1–P4 if all priorities land cleanly, putting the project around **50 400 LOC**. The prior overview's −10 000 Phase-3 forecast turned out to be −1 300 actual, so I'm applying a similar 6× realism multiplier here: the *realistic* outcome is ~−800 to −1 200 LOC. Anything beyond P3 has diminishing returns relative to the value of stability for the protected theorems.

---

## DO NOT TOUCH list

These items are load-bearing for `hw_3_3_clean_full_mero` and/or `valence_formula_textbook` AND are currently in clean working order. Any "improvement" that destabilises them is net-negative.

1. **`HungerbuhlerWasem/MultiCrossingCPV.lean` (4 059 lines)** — the heart of the HW33 proof. Five `theorem`s extend each other in a delicate chain (`hasCauchyPVOn_multiCrossing_higherOrder`, `cpv_polarPart_at_multiCrossed_pole_under_condB`, `residueTheorem_crossing_full_spec`, `residueTheorem_crossing_paper_faithful_clean`). The two `admit`-mentions in the docstrings are not actual `admit`s.
2. **`HW33Clean.lean` (84 lines) + `ValenceFormulaFinal.lean` (70 lines)** — the protected theorem files. Both verify with `[propext, Classical.choice, Quot.sound]`. Treat as read-only.
3. **`PaperPwC1Immersion.lean` (1 341 lines) + `PaperPwC1ImmersionInvariance.lean` (767 lines)** — the `ClosedPwC1Immersion` definition and `cyclicShift` invariance. The basepoint structural residual `hx_notin_S` in `hw_3_3_clean_full_mero` is bridged via these files. Carefully golfed in Phase 3.
4. **`ValenceFormula/PVChain/Assembly.lean` (711 lines) + `Assembly/ResidueSide.lean` (407 lines)** — the modular-side ↔ residue-side equality. The valence formula's modular side and residue side are assembled here.
5. **`GeneralizedResidueTheory/Residue/SectorCurveLemma.lean` (812 lines) + `SectorCurve.lean` (534 lines)** — the sector-curve PV Lemma 3.1 from HW. Used by both `MultiCrossingCPV.lean` and the valence chain via `Proposition2_2.lean`.

---

## Verification

| Check | Result |
|---|---|
| `LeanModularForms.hw_3_3_clean_full_mero` axioms | `["propext", "Classical.choice", "Quot.sound"]` |
| `valence_formula_textbook` axioms | `["propext", "Classical.choice", "Quot.sound"]` |
| `sorry` / `admit` count in `LeanModularForms/**/*.lean` | **0** (the 2 `admit` matches in `MultiCrossingCPV.lean` are docstring English, not tactics) |
| `axiom` declarations | **0** |
| `set_option` directives | 3 (in 2 files: `DslopeIntegral.lean` ×2, `PVSplitting.lean` ×1) |
| Orphan files unreachable from `LeanModularForms.lean` | **0** of 135 |
| Build state | green (umbrella + both protected theorems verify) |
