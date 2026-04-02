# Project Overview: LeanModularForms

Generated: 2026-03-31

## 1. Executive Summary

This project formalizes the **generalized residue theorem** of Hungerbuhler-Wasem
(arXiv:1808.00997v2, Theorem 3.3) and applies it to prove the **valence formula for
modular forms** on SL_2(Z). The two main components total **46,586 lines of Lean 4**
across **81 files** with approximately **1,614 top-level declarations**, **zero sorries**,
and **no non-standard axioms** (only `propext`, `Classical.choice`, `Quot.sound`).

The **GeneralizedResidueTheory** component (37 files, 23,427 lines, ~669 declarations)
builds a complete framework for Cauchy principal value integrals on piecewise C^1 curves
that pass through poles. It includes a Dixon-style proof of the Cauchy integral formula
for null-homologous curves, generalized winding numbers with the Hungerbuhler-Wasem
crossing-angle decomposition (Proposition 2.2), higher-order pole support via flatness
conditions (A') and (B), and an extension to formal Z-linear combinations of curves
(contour cycles). The public API exposes two main theorems:
`generalizedResidueTheorem` (full conditions) and
`generalizedResidueTheorem_simplePoles` (simple pole corollary).

The **ValenceFormula** component (44 files, 23,159 lines, ~945 declarations) applies this
machinery to the standard fundamental domain of SL_2(Z), proving:
`ord_cusp(f) + (1/2) ord_i(f) + (1/3) ord_rho(f) + sum_q ord_q(f) = k/12`.
This requires: explicit construction of the fundamental domain boundary as a piecewise
C^1 immersion; computation of generalized winding numbers at the three elliptic points
(i, rho, rho+1) and at boundary edges; a homotopy argument showing interior winding
number equals -1; modular invariance of the vanishing order under T and S; orbit-pairing
to collapse left/right edge and arc contributions; and assembly into textbook form with
`finsum` over non-elliptic orbits.

## 2. Statistics

| Metric | GeneralizedResidueTheory | ValenceFormula | Total |
|---|---|---|---|
| Files | 37 | 44 | 81 |
| Lines of code | 23,427 | 23,159 | 46,586 |
| Top-level declarations | ~669 | ~945 | ~1,614 |
| `private` declarations | ~290 | ~388 | ~678 |
| Sorries | 0 | 0 | 0 |
| Non-standard axioms | 0 | 0 | 0 |
| Files > 1,000 lines | 8 | 3 | 11 |
| Files > 500 lines | 19 | 21 | 40 |
| `set_option maxHeartbeats` overrides | 0 | 0 | 0 |

### Subdirectory Breakdown

**GeneralizedResidueTheory** (23,427 lines):

| Subdirectory/File | Files | Lines | Purpose |
|---|---|---|---|
| Root-level files | 12 | 6,381 | Core definitions (Basic), CPV, winding numbers, residues, cycle theory, curve avoidance, etc. |
| `Homotopy/` | 4 | 2,845 | Parametric differentiation, homotopy invariance, integrality, circle parameterization |
| `PVInfrastructure/` | 5 | 3,450 | Annulus bounds, step bounds, gamma/remainder analysis, uniform step bounds |
| `Residue/` | 6 | 3,830 | Meromorphic principal parts, sector curves, generalized theorem base, measure helpers |
| `Residue/FlatnessTransfer/` | 4 | 3,649 | Higher-order cancellation: boundary vanishing, per-term vanishing, CPV existence, assembly |
| `OnCurvePV/` | 1 | 339 | On-curve principal value basics |
| `WindingNumber/` | 1 | 747 | Proposition 2.2 (angle decomposition) |

**ValenceFormula** (23,159 lines):

| Subdirectory/File | Files | Lines | Purpose |
|---|---|---|---|
| Root-level files | 10 | 2,878 | Definitions, core identity, orbit sum/pairing, modular invariance, textbook forms |
| `Boundary/` | 3 | 1,584 | FD boundary definition (Basic), bounds, smoothness/immersion construction |
| `Boundary/Winding/` | 4 | 2,975 | Edge/arc winding numbers: RightEdge, LeftEdge, UnitArc, UnitArcHelpers |
| `RectHomotopy/` | 14 | 7,122 | Homotopy from curved FD boundary to rectilinear polygon, proving winding = -1 |
| `PVChain/` | 6 | 3,921 | Assembly of residue/modular sides, arc contribution, cusp integral, helpers |
| `OnCurvePV/` | 3 | 1,768 | CPV existence at on-curve singularities: endpoint, corner, main theorem |
| `WindingWeights/` | 4 | 3,301 | Winding number weights at i, rho, rho+1, plus common infrastructure |

## 3. Structural Issues

### 3.1 Extremely Long Proofs

The project contains monolithic proofs that are the single biggest barrier to
maintainability. Most follow a pattern: they case-split on the 5 segments of
`fdBoundary_H` or partition points {1, 2, 3, 4}, then repeat similar subgoal work per
case. This is the classic symptom of missing extraction of a parametric helper lemma.

**Over 800 lines (single proof):**

| Proof | File | ~Lines | Description |
|---|---|---|---|
| `dominated_convergence_multipoint_helper` | `Residue/MultipointPV.lean:643` | 1,010 | Dominated convergence for multipoint PV integrals |
| `singular_annulus_bound_explicit` | `PVInfrastructure/AnnulusBounds.lean:888` | 836 | Annulus integration bounds for singular terms |

**500-700 lines:**

| Proof | File | ~Lines | Description |
|---|---|---|---|
| `fdBoundaryToPolygonHomotopy_deriv_bound` | `RectHomotopy/MainTheoremBound.lean:16` | 686 | Derivative bound for homotopy (5-segment case split) |
| `fdBoundaryToPolygonHomotopy_deriv_continuousOn_pieces` | `RectHomotopy/MainTheoremDerivCont.lean:15` | 637 | Continuity of homotopy derivative on each piece |
| `fdBoundaryToPolygonHomotopy_not_diffAt_134` | `RectHomotopy/BoundaryHomotopySmooth.lean:20` | 630 | Non-differentiability at partition corners (1, 3, 4) |

**200-500 lines:**

| Proof | File | ~Lines |
|---|---|---|
| `hasDerivAt_homotopy_param` | `Homotopy/ParametricDiff.lean:273` | 460 |
| `hasDerivAt_homotopy_integral_zero` | `Homotopy/ParametricDiff.lean:738` | 360 |
| `rightEdge_ftc_telescope` | `Boundary/Winding/RightEdge.lean` | ~298 |
| `cpv_at_corner` | `OnCurvePV/EndpointCorner.lean` | ~297 |
| `cpv_at_endpoint` | `OnCurvePV/EndpointCorner.lean` | ~296 |
| `ftc_logDeriv_telescope_i` | `WindingWeights/I.lean` | ~293 |

### 3.2 Large Files

Eleven files exceed 1,000 lines.

**GeneralizedResidueTheory (8 files over 1,000 lines):**
- `PVInfrastructure/AnnulusBounds.lean` -- 1,724 lines
- `HomologicalCauchy.lean` -- 1,710 lines
- `Residue/MultipointPV.lean` -- 1,653 lines
- `WindingNumber.lean` -- 1,553 lines
- `Residue/FlatnessTransfer/PerTermVanishing.lean` -- 1,260 lines
- `Residue/FlatnessTransfer/BoundaryVanishing.lean` -- 1,206 lines
- `Homotopy/ParametricDiff.lean` -- 1,103 lines
- `Residue/FlatnessTransfer/HigherOrderAssembly.lean` -- 1,084 lines

**ValenceFormula (3 files over 1,000 lines):**
- `PVChain/Assembly.lean` -- 1,255 lines
- `WindingWeights/Rho.lean` -- 1,098 lines
- `WindingWeights/I.lean` -- 1,061 lines

### 3.3 High Private-to-Public Ratio

Across both components, ~678 of ~1,614 declarations (42%) are `private`. Many are
utility lemmas about complex arithmetic, norm bounds, and trigonometry that could serve
other projects. The files with the highest private counts:

| File | Private Count |
|---|---|
| `HomologicalCauchy.lean` | 38 |
| `Residue/SectorCurveLemma.lean` | 33 |
| `Residue/FlatnessTransfer/HigherOrderAssembly.lean` | 32 |
| `Residue/FlatnessTransfer/BoundaryVanishing.lean` | 30 |
| `TextbookForm.lean` | 37 |
| `PVChain/Assembly.lean` | 34 |
| `WindingWeights/I.lean` | 28 |
| `WindingWeights/RhoPlusOne.lean` | 24 |

### 3.4 ContinuousSMul Instance Duplication

The instance chain `NormSMulClass R C -> IsBoundedSMul R C -> ContinuousSMul R C` is
manually declared in 6 files:
- `GeneralizedResidueTheory/LogDerivFTC.lean`
- `GeneralizedResidueTheory/Homotopy/CircleParam.lean`
- `GeneralizedResidueTheory/Homotopy/ParametricDiff.lean`
- `GeneralizedResidueTheory/CauchyPrimitive.lean`
- `ValenceFormula/Boundary/Smooth.lean`
- `ValenceFormula/RectHomotopy/HomotopyDef.lean`

This should be a single file or import providing the instance.

## 4. Missing API / Generalization Opportunities

### 4.1 PiecewiseC1Curve vs Mathlib's Path / ContinuousMap

`PiecewiseC1Curve` and `PiecewiseC1Immersion` (defined in `Basic.lean`) are bespoke
structures: a function `R -> C` on `[a, b]` with a `Finset R` partition and piecewise
differentiability. Mathlib provides `Path x y` (continuous map from `[0,1]`) and
`ContinuousMap.Homotopy`.

**Gap:** No `toPath` or `toContinuousMap` coercions exist. The project builds its own
homotopy invariance from scratch (the entire `Homotopy/` subdirectory: 2,845 lines in
GenRes, plus the 7,122-line `RectHomotopy/` in ValenceFormula).

**Recommendation:** Add `PiecewiseC1Curve.toPath` and `toContinuousMap` (rescaling
`[a,b]` to `[0,1]`). This does not require rewriting proofs but enables future
interoperability with mathlib's homotopy theory.

### 4.2 CurveAvoids / curveInfDist vs Mathlib's Metric.infDist

`CurveAvoids gamma a b z0` is defined as `forall t in Icc a b, gamma t /= z0` and
`curveInfDist` is literally `Metric.infDist z0 (gamma '' Icc a b)`. The 98-line
`CurveAvoidance.lean` is a thin wrapper around standard mathlib API.

**Gap:** These wrappers add a naming layer without adding functionality. The key theorem
`curveInfDist_pos_of_avoids` restates `IsClosed.notMem_iff_infDist_pos` for curve images.

**Recommendation:** Consider deprecating `CurveAvoids` in favor of
`z0 not-in gamma '' Icc a b` and using `Metric.infDist` directly. Keep only genuinely
useful convenience lemmas (e.g., `curveAvoids_of_im_lt`).

### 4.3 Winding Number and circleIntegral

The generalized winding number is defined as a CPV integral. For curves avoiding `z0` it
reduces to the classical contour integral `(1/(2*pi*I)) integral_gamma dz/(z - z0)`.
Mathlib's `Complex.windingNumber` uses `circleIntegral`.

**Gap:** No bridge lemma equating `generalizedWindingNumber'` on a circle to
`Complex.windingNumber`. The project does use `circleIntegral` internally
(in `HigherOrderAssembly.lean` and `PerTermVanishing.lean`) but never connects its
winding number to mathlib's.

**Recommendation:** Add `generalizedWindingNumber_eq_windingNumber_of_circle`.

### 4.4 IsNullHomologous vs Mathlib's Homology

`IsNullHomologous gamma U` is a three-field structure (closedness, image in U, vanishing
winding around complement). This is the correct definition for Hungerbuhler-Wasem but
is disconnected from mathlib's algebraic topology.

**Gap:** No bridge to `FundamentalGroup` or singular homology.

**Recommendation:** Long-term. A connecting lemma would require homology infrastructure
for open subsets of C that may not yet exist in mathlib.

### 4.5 Concreteness of fdBoundary_H

The fundamental domain boundary `fdBoundary_H H` is a piecewise function with 5 explicit
segments parameterized on `[0, 5]`. Every property is proved with a 5-way case split.
At least 20 proofs across the ValenceFormula component contain:

```
by_cases h1 : t <= 1  -- right vertical
by_cases h2 : t <= 2  -- first arc half
by_cases h3 : t <= 3  -- second arc half
by_cases h4 : t <= 4  -- left vertical
                       -- top horizontal
```

**Gap:** No abstract segment-builder combinator exists.

**Recommendation:** Introduce a combinator that builds `PiecewiseC1Curve` from a list of
segments, each carrying differentiability/derivative data. Prove properties by induction
over the segment list. This is the highest-impact structural refactoring for the
ValenceFormula component.

### 4.6 Residue Definitions

The project defines both `residueSimplePole f z0` (limit of `(z - z0) * f z`) and
`residueAt f s` (via `meromorphicOrderAt`). Mathlib now has `MeromorphicAt.residue`.

**Gap:** No lemma connects `residueAt` to `MeromorphicAt.residue`.

**Recommendation:** Add `residueAt_eq_meromorphicAt_residue` and consider deprecating
`residueSimplePole`.

## 5. Duplication Patterns

### 5.1 Edge/Arc Winding Number Proofs (High Impact)

`Boundary/Winding/RightEdge.lean` (939 lines), `LeftEdge.lean` (788 lines),
`UnitArc.lean` (559 lines), and `UnitArcHelpers.lean` (689 lines) all follow the same
proof pattern:

1. Identify the unique crossing parameter `t0` on `[0, 5]`
2. Prove `fdBoundary_H H t0 = s` and uniqueness of crossing
3. Compute the FTC telescope: `log(gamma(t0-delta) - s) - log(gamma(t0+delta) - s) -> L`
4. Show the PV integral converges (from step 3 plus non-crossing bounds)
5. Extract `generalizedWindingNumber' = PV / (-2*pi*I)`

A unified `singleCrossingWindingNumber` framework parameterized by the crossing data
could reduce this by 30-40%.

### 5.2 WindingWeights at i / rho / rho+1 (High Impact)

`WindingWeights/I.lean` (1,061 lines), `Rho.lean` (1,098 lines), and `RhoPlusOne.lean`
(915 lines) share extensive structural overlap. Each file:

- Computes `fdBoundary_H H t - s` for each of the 5 segments
- Establishes `slitPlane` membership for `gamma(t) - s` away from crossing
- Performs FTC telescoping with `Complex.log`
- Extracts `pv_integral_at_*_tendsto` and `gWN_fdBoundary_H_at_*`

The common infrastructure (`Common.lean`, 227 lines) captures shared definitions but
not the proof pattern. Factoring out a `windingWeight_at_elliptic_point` parameterized
by the crossing geometry would eliminate most of the repetition.

### 5.3 FTC Log Telescoping (Medium Impact)

The `ftc_log` pattern (applying the fundamental theorem of calculus to `Complex.log(gamma(t) - s)`)
appears in at least 7 files with references to `ftc_log`-named lemmas in:
- `WindingWeights/{I, Rho, RhoPlusOne}.lean`
- `Boundary/Winding/{LeftEdge, RightEdge}.lean`
- `Boundary/Winding/UnitArcHelpers.lean`
- `WindingWeights/Common.lean`

Each instance reproves: (a) `gamma(t) - s` lies in `slitPlane`, (b) `Complex.log` is
differentiable there, (c) the chain rule gives the log-derivative, and (d) the integral
telescopes to a log difference. A single lemma:

```
theorem ftc_log_on_segment {gamma : R -> C} {a b : R} {s : C}
    (h_slit : forall t in Icc a b, gamma t - s in slitPlane)
    (h_diff : ...) (h_deriv_cont : ...) :
    integral t in a..b, deriv gamma t / (gamma t - s) =
      Complex.log (gamma b - s) - Complex.log (gamma a - s)
```

could replace all of these instances.

### 5.4 Five-Segment Case Analysis (Pervasive)

Beyond individual proof lengths, the 5-segment structure of `fdBoundary_H` generates
recurring case-analysis boilerplate throughout the ValenceFormula component. At least 20
proofs perform some variant of the `by_cases` chain over segment boundaries. Each case
typically involves: rewriting with the segment's definition (`fdBoundary_H_seg*`),
simplifying complex arithmetic, and applying segment-specific bounds. The fix is the
abstract segment builder described in Section 4.5.

### 5.5 Instance and Attribute Boilerplate (Low Impact, Easy Fix)

- `ContinuousSMul R C` instance: duplicated in 6 files (see Section 3.4)
- `attribute [local instance] Classical.propDecidable`: appears in nearly every file
- `open Complex MeasureTheory Set Filter Topology` / `open scoped Real Interval`: the
  same `open` block is repeated verbatim in most files

A shared prelude file (`Imports.lean`) could consolidate all three.

## 6. Recommended Action Plan

### Priority 1: Quick Wins (1-2 days each)

**P1.1 -- Consolidate ContinuousSMul instance.**
Create a shared file with the `NormSMulClass -> IsBoundedSMul -> ContinuousSMul` chain
for `R` and `C`. Replace the 6 duplicated instance declarations with a single import.

**P1.2 -- Audit private declarations.**
Review the ~678 private declarations, focusing on files with highest counts
(HomologicalCauchy: 38, SectorCurveLemma: 33, HigherOrderAssembly: 32, TextbookForm: 37).
Promote general-purpose complex arithmetic/trig/norm lemmas to public. Zero proof risk.

**P1.3 -- Clean up CurveAvoidance API.**
Either deprecate `CurveAvoids`/`curveInfDist` in favor of direct `Metric.infDist` usage,
or add `@[simp]` lemmas making the equivalence transparent. Naming cleanup, not a refactor.

**P1.4 -- Previously identified quick wins (from prior audit).**
- Delete `ftc_log_piece` wrapper in `ValenceFormula/WindingWeights/Common.lean`
- Unify `H_height` and `heightCutoff` constants
- Delete `cos/sin_two_pi_div_three'` primed copies in `RectHomotopy/HomotopyDef.lean`
- Unify `exp_real_angle_I` and `exp_real_mul_I`
- Make `fd_im_gt_half` public (currently private in both `OrbitSum.lean` and `TextbookForm.lean`)

### Priority 2: API Improvements (1-2 weeks each)

**P2.1 -- Extract ftc_log_on_segment.**
A single lemma for FTC applied to `Complex.log (gamma(t) - s)` on a segment where
`gamma(t) - s` stays in the slit plane. Would be used in 7+ files.

**P2.2 -- Add PiecewiseC1Curve.toPath and toContinuousMap.**
Bridge coercions to mathlib types. No existing proofs change; enables future
interoperability.

**P2.3 -- Connect residueAt to MeromorphicAt.residue.**
A bridge lemma `residueAt_eq_meromorphicAt_residue` connecting to mathlib's evolving
meromorphic function library.

**P2.4 -- Connect generalizedWindingNumber to Complex.windingNumber.**
For the special case of circular contours, equate the project's CPV-based winding number
with mathlib's `circleIntegral`-based definition.

### Priority 3: Structural Refactoring (1-3 months)

**P3.1 -- Decompose the longest proofs.**
Break each proof exceeding 500 lines into per-case helper lemmas. Targets in priority
order:

1. `dominated_convergence_multipoint_helper` (~1,010 lines): Extract per-point dominated
   convergence, then combine with a summation step.
2. `singular_annulus_bound_explicit` (~836 lines): Factor annulus geometry into separate
   lemmas for the inner/outer/boundary regions.
3. `fdBoundaryToPolygonHomotopy_deriv_bound` (~686 lines): One helper per segment.
4. `fdBoundaryToPolygonHomotopy_deriv_continuousOn_pieces` (~637 lines): Same strategy.
5. `fdBoundaryToPolygonHomotopy_not_diffAt_134` (~630 lines): One helper per corner.

**P3.2 -- Unify edge/arc winding number proofs.**
Create a `singleCrossingWindingNumber` framework taking the crossing parameter,
uniqueness proof, and log-ratio limit as inputs. Apply it in `RightEdge.lean`,
`LeftEdge.lean`, and `UnitArc.lean`.

**P3.3 -- Unify WindingWeights/I, Rho, RhoPlusOne.**
Factor out a `windingWeight_at_point` parameterized by the elliptic point's geometric
properties (crossing time, segment membership, angle).

**P3.4 -- Abstract fdBoundary_H segment builder.**
A combinator that builds `PiecewiseC1Curve` from a list of segments and lifts
per-segment properties to the full curve. This would tame the 5-way case splits
throughout the 14-file `RectHomotopy/` subdirectory.

**P3.5 -- Split the 8 GenRes files over 1,000 lines.**
Most urgent: `HomologicalCauchy.lean` (1,710 lines) contains the Dixon proof,
null-homologous bridge lemmas, FTC machinery, and the Cauchy integral formula --
logically distinct components. `MultipointPV.lean` (1,653 lines) and
`AnnulusBounds.lean` (1,724 lines) similarly contain independent proof chains.

### Priority 4: Mathlib Contributions (Long-term)

**P4.1 -- PiecewiseC1Curve and PiecewiseCurveAPI.**
After adding `toPath`/`toContinuousMap` (P2.2), the core structures plus the sorted
partition / consecutive-pairs API would fit in mathlib's
`Analysis.Calculus.PiecewiseC1` or `Topology.ContinuousOn.Piecewise`.

**P4.2 -- Generalized winding number.**
The CPV-based winding number and angle decomposition (Proposition 2.2) are of
independent interest. After connecting to `Complex.windingNumber` (P2.4), this could
join mathlib's complex analysis library.

**P4.3 -- Generalized residue theorem.**
The theorems `generalizedResidueTheorem` and `generalizedResidueTheorem_simplePoles`,
together with `ContourCycle` extensions, formalize Theorem 3.3 of Hungerbuhler-Wasem.
After refactoring (P3.1-P3.5), the dependency chain would be clean enough for a
mathlib PR.

**P4.4 -- ContinuousSMul instance upstream.**
If `ContinuousSMul R C` is not already derivable in mathlib from `NormedSpace`, file
an issue or contribute the missing instance.

## 7. Dependency Graph (Simplified)

```
GeneralizedResidueTheory/
  Basic.lean  <----  PiecewiseCurveAPI.lean
    |                CurveAvoidance.lean
    |                ArcCalculus.lean
    v
  CauchyPrimitive.lean
  PrincipalValue.lean
  LogDerivFTC.lean
    |
    v
  Residue.lean  <----  Residue/{MultipointPV, SectorCurve, MeromorphicPrincipalPart, ...}
    |                   Residue/FlatnessTransfer/{PerTermVanishing, BoundaryVanishing, ...}
    v
  HomologicalCauchy.lean  (Dixon proof, null-homologous Cauchy integral)
    |
    v
  WindingNumber.lean  <----  WindingNumber/Proposition2_2.lean
  Homotopy/{ParametricDiff, Invariance, Integrality, CircleParam}
    |
    v
  GeneralizedResidueTheorem.lean  (public API: Theorem 3.3)
  Cycle.lean  (contour cycles: Z-linear combinations)

ValenceFormula/
  Definitions.lean  (elliptic points i/rho/rho+1, order of vanishing, FD)
  ModularInvariance.lean  (T/S invariance of vanishing order)
    |
    v
  Boundary/{Basic, Bounds, Smooth}  (fdBoundary_H curve construction + PiecewiseC1Immersion)
  Boundary/Winding/{RightEdge, LeftEdge, UnitArc, UnitArcHelpers}
    |
    v
  RectHomotopy/{HomotopyDef, Geometry, ..., MainTheorem}  (winding = -1 via homotopy)
  InteriorWinding.lean
    |
    v
  OnCurvePV/{Basic, EndpointCorner, Main}  (CPV existence at on-curve singularities)
  WindingWeights/{Common, I, Rho, RhoPlusOne}  (gWN at elliptic points)
    |
    v
  PVChain/{Helpers, Assembly, ArcContribution, ...}  (residue side + modular side assembly)
  OrbitPairing.lean  (T/S orbit cancellation)
  OrbitSum.lean
    |
    v
  CoreIdentity.lean  (orbit-sum form of valence formula)
  TextbookExistence.lean  (canonical representative finsets)
  TextbookForm.lean  (final textbook statement with finsum)
```

### Cross-Component Dependencies

The ValenceFormula imports from GeneralizedResidueTheory at 14 points:
- **Basic.lean** -- `PiecewiseC1Curve` structure
- **PiecewiseCurveAPI.lean**, **CurveAvoidance.lean**, **ArcCalculus.lean** -- curve utilities
- **PrincipalValue.lean** -- CPV definitions
- **LogDerivFTC.lean** -- FTC for log-derivative
- **Residue.lean** -- residue definitions and classical theorem
- **Residue/GeneralizedTheoremBase.lean** -- base theorem machinery
- **PVInfrastructure/UniformStepBound.lean** -- step bound infrastructure
- **OnCurvePV/Basic.lean** -- on-curve PV foundations
- **Homotopy/{Invariance, CircleParam}** -- homotopy invariance tools
