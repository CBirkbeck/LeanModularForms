# Cleanup Ticket Plan

All tickets from PROJECT_OVERVIEW.md, organized into parallelizable stages.

## Dependency Graph

```
Stage 1 (all independent, fully parallel)
  |
Stage 2 (depends on Stage 1 completions where noted)
  |
Stage 3 (depends on Stage 2)
  |
Stage 4 (long-term, depends on Stage 3)
```

---

## Stage 1: Quick Wins (all independent, run in parallel)

### T1.1 — Consolidate ContinuousSMul instances
- **Files**: Create `ForMathlib/Instances.lean`, modify 6+ files
- **Work**: Move `NormSMulClass/IsBoundedSMul/ContinuousSMul ℝ ℂ` to shared file, replace all duplicates and `haveI` calls
- **Risk**: Low (mechanical replacement)
- **Blocked by**: Nothing
- **Blocks**: Nothing

### T1.2 — Clean up CurveAvoidance API
- **Files**: `GeneralizedResidueTheory/CurveAvoidance.lean` (98 lines)
- **Work**: Add `@[simp]` lemmas connecting `CurveAvoids` to `Metric.infDist`, deprecate thin wrappers
- **Risk**: Low
- **Blocked by**: Nothing
- **Blocks**: Nothing

### T1.3 — Delete duplicate constants/lemmas
- **Files**: Multiple (see below)
- **Work**:
  - Delete `cos/sin_two_pi_div_three'` primed copies in `RectHomotopy/HomotopyDef.lean`
  - Unify `exp_real_angle_I` and `exp_real_mul_I`
  - Unify `H_height` and `heightCutoff`
  - Make `fd_im_gt_half` public (private in both `OrbitSum.lean` and `TextbookForm.lean`)
- **Risk**: Low
- **Blocked by**: Nothing
- **Blocks**: Nothing

### T1.4 — Private declaration audit (GenResTheory)
- **Files**: All 37 GenRes files, focus on top-4: HomologicalCauchy (38 private), SectorCurveLemma (33), HigherOrderAssembly (32), BoundaryVanishing (30)
- **Work**: Review each private decl. Promote general-purpose complex/trig/norm lemmas to public. Remove unused ones.
- **Risk**: Low (visibility change only)
- **Blocked by**: Nothing
- **Blocks**: Nothing

### T1.5 — Private declaration audit (ValenceFormula)
- **Files**: All 44 ValenceFormula files, focus on: TextbookForm (37 private), Assembly (34), I (28), RhoPlusOne (24)
- **Work**: Same as T1.4
- **Risk**: Low
- **Blocked by**: Nothing
- **Blocks**: Nothing

---

## Stage 2: API Improvements (some independent, some sequential)

### T2.1 — Extract `ftc_log_on_segment` lemma
- **Files**: Create in `GeneralizedResidueTheory/LogDerivFTC.lean` or new file; refactor 7+ consumer files
- **Work**: Single lemma for FTC applied to `Complex.log(gamma(t) - s)` on slit-plane segment. Replace 7+ inline reproofs.
- **Risk**: Medium (must match all use sites)
- **Blocked by**: Nothing
- **Blocks**: T3.2, T3.3

### T2.2 — Add `PiecewiseC1Curve.toPath` bridge
- **Files**: `GeneralizedResidueTheory/Basic.lean`
- **Work**: Add coercion to mathlib's `Path` (rescale `[a,b]` to `[0,1]`). Add `toContinuousMap`.
- **Risk**: Low (additive, no existing proofs change)
- **Blocked by**: Nothing
- **Blocks**: T4.1, T4.2

### T2.3 — Connect `residueAt` to `MeromorphicAt.residue`
- **Files**: `GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean`
- **Work**: Bridge lemma `residueAt_eq_meromorphicAt_residue`. Consider deprecating `residueSimplePole`.
- **Risk**: Medium
- **Blocked by**: Nothing
- **Blocks**: T4.3

### T2.4 — Connect `generalizedWindingNumber'` to `Complex.windingNumber`
- **Files**: `GeneralizedResidueTheory/WindingNumber.lean` or new file
- **Work**: For circular contours, equate CPV-based winding number with mathlib's definition.
- **Risk**: Medium
- **Blocked by**: Nothing
- **Blocks**: T4.2

---

## Stage 3: Structural Refactoring (dependencies noted)

### T3.1a — Decompose `dominated_convergence_multipoint_helper` (840 lines)
- **File**: `GeneralizedResidueTheory/Residue/MultipointPV.lean`
- **Work**: Extract per-point dominated convergence, measurability infrastructure, bound computation as separate lemmas. Target: main proof <50 lines.
- **Risk**: High (mathematically complex)
- **Blocked by**: Nothing (but benefits from T2.1)
- **Blocks**: T3.5 (file split)

### T3.1b — Decompose `singular_annulus_bound_explicit` (830 lines)
- **File**: `GeneralizedResidueTheory/PVInfrastructure/AnnulusBounds.lean`
- **Work**: Factor annulus geometry into inner/outer/boundary region lemmas. Target: <50 lines.
- **Risk**: High
- **Blocked by**: Nothing
- **Blocks**: T3.5

### T3.1c — Decompose `fdBoundaryToPolygonHomotopy_deriv_bound` (686 lines)
- **File**: `ValenceFormula/RectHomotopy/MainTheoremBound.lean`
- **Work**: One helper per homotopy segment (5 segments). Target: <50 lines.
- **Risk**: Medium (repetitive structure, 5 parallel sub-tasks)
- **Blocked by**: Nothing
- **Blocks**: Nothing

### T3.1d — Decompose `fdBoundaryToPolygonHomotopy_deriv_continuousOn_pieces` (637 lines)
- **File**: `ValenceFormula/RectHomotopy/MainTheoremDerivCont.lean`
- **Work**: Same 5-segment strategy as T3.1c.
- **Risk**: Medium
- **Blocked by**: Nothing
- **Blocks**: Nothing

### T3.1e — Decompose `fdBoundaryToPolygonHomotopy_not_diffAt_134` (573 lines)
- **File**: `ValenceFormula/RectHomotopy/BoundaryHomotopySmooth.lean`
- **Work**: One helper per corner (3 corners). Target: <50 lines.
- **Risk**: Medium
- **Blocked by**: Nothing
- **Blocks**: Nothing

### T3.1f — Decompose `hasDerivAt_homotopy_param` + `hasDerivAt_homotopy_integral_zero` (460+360 lines)
- **File**: `GeneralizedResidueTheory/Homotopy/ParametricDiff.lean`
- **Work**: Extract uniform bound, pointwise convergence, measurability, and parameter differentiation as separate lemmas.
- **Risk**: High (the core of homotopy invariance theory)
- **Blocked by**: Nothing
- **Blocks**: T3.5

### T3.2 — Unify edge/arc winding number proofs
- **Files**: `Boundary/Winding/{RightEdge, LeftEdge, UnitArc, UnitArcHelpers}.lean` (~2,975 lines total)
- **Work**: Create `singleCrossingWindingNumber` framework. Each edge/arc file provides crossing data, framework produces the gWN value.
- **Risk**: High (must unify 3 different geometric cases)
- **Blocked by**: T2.1 (ftc_log_on_segment)
- **Blocks**: Nothing

### T3.3 — Unify WindingWeights at i/rho/rho+1
- **Files**: `WindingWeights/{I, Rho, RhoPlusOne}.lean` (~3,174 lines total)
- **Work**: Factor out `windingWeight_at_point` parameterized by crossing geometry. Each file provides elliptic-point-specific data.
- **Risk**: High
- **Blocked by**: T2.1
- **Blocks**: Nothing

### T3.4 — Abstract fdBoundary_H segment builder
- **Files**: New combinator in `Boundary/Basic.lean`, refactor ~20 proofs across ValenceFormula
- **Work**: Build `PiecewiseC1Curve` from segment list with per-segment properties. Prove properties by induction over segments instead of 5-way case splits.
- **Risk**: Very high (touches ~20 proofs, architectural change)
- **Blocked by**: T3.1c, T3.1d, T3.1e (decompose first, then abstract)
- **Blocks**: Nothing

### T3.5 — Split large files (>1000 lines)
- **Files**: 11 files
- **Work**: Split each into focused submodules:
  - `HomologicalCauchy.lean` (1710) → Dixon proof + null-homologous bridge + FTC
  - `MultipointPV.lean` (1653) → measurability + dominated convergence + PV assembly
  - `AnnulusBounds.lean` (1724) → measure bounds + singular bounds
  - `WindingNumber.lean` (1553) → angle defs + crossing analysis + main decomposition
  - `PerTermVanishing.lean` (1260) → zpow infrastructure + vanishing + CPV
  - `BoundaryVanishing.lean` (1206) → direction analysis + FTC + cutoff
  - `ParametricDiff.lean` (1103) → Schwarz + param diff + homotopy integral
  - `HigherOrderAssembly.lean` (1084) → per-term dispatch + assembly
  - `Assembly.lean` (1255) → modular side + residue side + vertical cancel
  - `Rho.lean` (1098) → segment analysis + FTC + PV
  - `I.lean` (1061) → segment analysis + FTC + PV
- **Risk**: Medium (mechanical but many files)
- **Blocked by**: T3.1a-f (decompose proofs first to reduce individual proof sizes)
- **Blocks**: T4.3

---

## Stage 4: Mathlib Contributions (long-term)

### T4.1 — Contribute PiecewiseC1Curve to mathlib
- **Blocked by**: T2.2 (toPath bridge)
- **Work**: Clean up `Basic.lean` + `PiecewiseCurveAPI.lean` for mathlib standards

### T4.2 — Contribute generalized winding number to mathlib
- **Blocked by**: T2.4 (windingNumber bridge)
- **Work**: CPV-based winding number + angle decomposition (Prop 2.2)

### T4.3 — Contribute generalized residue theorem to mathlib
- **Blocked by**: T3.5 (clean file structure), T2.3 (residue bridge)
- **Work**: Theorem 3.3 of Hungerbuhler-Wasem

### T4.4 — Fix ContinuousSMul ℝ ℂ upstream
- **Blocked by**: T1.1 (consolidation identifies the exact missing instance)
- **Work**: File mathlib issue or contribute `NormedSpace → ContinuousSMul` instance

---

## Parallelization Map

```
            T1.1  T1.2  T1.3  T1.4  T1.5     ← Stage 1: all parallel
              |                  |     |
              v                  v     v
            T2.1  T2.2  T2.3  T2.4            ← Stage 2: all parallel
              |     |     |     |
              v     |     |     |
     T3.1a  T3.1b  |   T3.1c  T3.1d  T3.1e  T3.1f   ← Stage 3 decompositions: all parallel
       |      |     |     |      |      |      |
       v      v     |     v      v      v      v
     T3.5   T3.2  T3.3  T3.4                  ← Stage 3 unification: after decompositions
       |      |     |     |
       v      v     v     v
     T4.1  T4.2  T4.3  T4.4                   ← Stage 4: after refactoring
```

**Maximum parallelism:**
- Stage 1: 5 workers simultaneously
- Stage 2: 4 workers simultaneously
- Stage 3 decompositions: 6 workers simultaneously (T3.1a-f)
- Stage 3 unification: 4 workers (T3.2-T3.5, after decompositions complete)
- Stage 4: 4 workers (after refactoring)

## Effort Estimates

| Stage | Tickets | Est. Total Effort | Parallelizable? |
|-------|---------|-------------------|-----------------|
| 1 | 5 | 1-2 days | Fully |
| 2 | 4 | 1-2 weeks | Fully |
| 3 decomp | 6 | 2-4 weeks | Fully |
| 3 unify | 4 | 2-4 weeks | Mostly |
| 4 | 4 | 2-3 months | Mostly |

**Critical path**: T1.1 → T2.1 → T3.2/T3.3 (for edge/winding unification)
**Highest impact**: T3.1a-f (decompose monster proofs) + T3.5 (split large files)
