# Project Overview: LeanModularForms (Valence Formula + Generalized Residue Theory)

Generated: 2026-03-23

## Summary

| Metric | GeneralizedResidueTheory | ValenceFormula (new) | valence/ComplexAnalysis (old) | **Total** |
|--------|--------------------------|----------------------|-------------------------------|-----------|
| Files  | 33                       | 44                   | 52                            | **129**   |
| Lines  | ~25,000                  | ~22,000              | ~106,000                      | **~153k** |
| Sorries| **0**                    | **0**                | ~150 (90 in Work files)       | ~150      |

### Key Results (sorry-free)

| Theorem | File | What |
|---------|------|------|
| `generalizedResidueTheorem` | GRT/GeneralizedResidueTheorem | Hungerbühler-Wasem Thm 3.3 for null-homologous curves |
| `generalizedResidueTheorem_cycle` | GRT/Cycle | Residue theorem for formal ℤ-cycles |
| `windingNumberCycle_isInt` | GRT/Cycle | Winding number of cycles is integer |
| `valence_formula_orbit_sum` | VF/CoreIdentity | Main orbit-sum valence formula |
| `valence_formula_textbook_orbit_finsum` | VF/TextbookForm | Textbook form with finprod over orbits |
| `gWN_fdBoundary_H_eq_neg_one_of_strictInterior` | VF/InteriorWinding | Winding = -1 for interior points |
| `gWN_fdBoundary_H_at_i` | VF/WindingWeights/I | gWN at i = -1/2 |
| `gWN_fdBoundary_H_at_rho` | VF/WindingWeights/Rho | gWN at ρ = -1/6 |
| `gWN_fdBoundary_H_at_rho_plus_one` | VF/WindingWeights/RhoPlusOne | gWN at ρ+1 = -1/6 |

---

## Table of Contents

1. [GeneralizedResidueTheory/](#1-generalizedresiduetheory) — Hungerbühler-Wasem PV theory
2. [ValenceFormula/](#2-valenceformula-new) — Clean split-file valence formula proof
3. [Modularforms/valence/ComplexAnalysis/](#3-modularformsvalencecomplexanalysis-old) — Original monolithic files

---

## 1. GeneralizedResidueTheory/

**33 files, ~25,000 lines, 0 sorries**

### Import Graph

```
Basic ──────────────────────────────────────────────────────────────┐
  ├── PrincipalValue                                                │
  ├── Residue ──────────────────────────────────┐                   │
  │     ├── Residue/Flatness                    │                   │
  │     ├── Residue/SectorCurve                 │                   │
  │     ├── Residue/SectorCurveLemma            │                   │
  │     ├── Residue/MeasureHelpers              │                   │
  │     ├── Residue/MeromorphicLaurent          │                   │
  │     ├── Residue/MeromorphicPrincipalPart    │                   │
  │     ├── Residue/MultipointPV                │                   │
  │     ├── Residue/GeneralizedTheoremBase      │                   │
  │     ├── Residue/GeneralizedTheorem          │                   │
  │     └── Residue/FlatnessTransfer/           │                   │
  │           ├── BoundaryVanishing             │                   │
  │           ├── CPVExistence                  │                   │
  │           ├── PerTermVanishing              │                   │
  │           └── HigherOrderAssembly           │                   │
  ├── WindingNumber ────────────────────────────┤                   │
  │     └── WindingNumber/Proposition2_2        │                   │
  ├── OnCurvePV/Basic                           │                   │
  ├── PVInfrastructure/                         │                   │
  │     ├── GammaAnalysis                       │                   │
  │     ├── RemainderAnalysis                   │                   │
  │     ├── StepBounds                          │                   │
  │     ├── AnnulusBounds                       │                   │
  │     └── UniformStepBound                    │                   │
  ├── CauchyPrimitive                           │                   │
  ├── Homotopy/                                 │                   │
  │     ├── CircleParam                         │                   │
  │     ├── Integrality                         │                   │
  │     ├── ParametricDiff                      │                   │
  │     └── Invariance                          │                   │
  ├── HomologicalCauchy ────────────────────────┘                   │
  ├── Cycle                                                         │
  └── GeneralizedResidueTheorem ────────────────────────────────────┘
```

### Key Files

| File | Decls | Purpose |
|------|-------|---------|
| **Basic.lean** | 22 | Core structures: `PiecewiseC1Curve`, `PiecewiseC1Immersion`, `cauchyPrincipalValue'`, `generalizedWindingNumber'` |
| **CauchyPrimitive.lean** | 12 | `holomorphic_convex_primitive` — primitives on convex sets |
| **HomologicalCauchy.lean** | ~50 | Dixon function proof: `contourIntegral_eq_zero_of_nullHomologous`, `cauchyIntegralFormula_nullHomologous`, `conditionsAB_imply_higherOrderCancel_nh` |
| **Cycle.lean** | 16 | `ContourCycle`, `generalizedResidueTheorem_cycle`, `windingNumberCycle_isInt` |
| **GeneralizedResidueTheorem.lean** | ~5 | Master theorem re-export: `generalizedResidueTheorem` |
| **Residue.lean** | ~35 | Multi-point CPV: `cauchyPrincipalValueOn`, `HasSimplePoleAt`, `integral_eq_sum_residues_of_avoids` |
| **WindingNumber.lean** | ~20 | Angle-based winding: `angleAtCrossing`, `windingNumberWithAngles'`, `exp_cutoff_integral_eq_ratio` |
| **Proposition2_2.lean** | ~15 | `finite_crossings` — crossing set is finite |
| **Homotopy/Invariance.lean** | 16 | `windingNumber_eq_of_homotopic_closed`, `generalizedWindingNumber_eq_classical_away`, `contourIntegral_eq_of_homotopic` |
| **Homotopy/ParametricDiff.lean** | 7 | `schwarz_partialDeriv_comm`, `hasDerivAt_homotopy_integral_zero` |
| **Homotopy/Integrality.lean** | 24 | `windingNumber_integer_of_piecewise_closed_avoiding`, `exp_integral_eq_endpoint_ratio_piecewise` |
| **Homotopy/CircleParam.lean** | 19 | `circleParam_winding_eq_one`, `circleParamCW_winding_eq_neg_one`, `winding_of_S1_curve_eq_degree` |
| **PVInfrastructure/UniformStepBound.lean** | 1 | `pv_step_bound_ratio_two_uniform` — the uniform PV convergence bound |
| **Residue/Flatness.lean** | 22 | `IsFlatOfOrder`, `tangentDeviation`, `SatisfiesConditionA/A'/B`, `conditions_automatic_simple_poles` |
| **Residue/GeneralizedTheoremBase.lean** | 20 | `residueAt`, `generalizedResidueTheorem'`, `generalizedResidueTheorem_higher_order_tendsto` |
| **Residue/GeneralizedTheorem.lean** | 3 | `generalizedResidueTheorem` (convex), `generalizedResidueTheorem_higher_order` |
| **Residue/FlatnessTransfer.lean** | 1 | `generalizedResidueTheorem_3_3` — Thm 3.3 with (A')+(B) on convex domain |
| **Residue/FlatnessTransfer/BoundaryVanishing.lean** | 39 | `integral_zpow_comp_sub_mul_deriv`, `zpow_boundary_diff_tendsto_zero`, `cutoff_zpow_infrastructure` |
| **Residue/FlatnessTransfer/CPVExistence.lean** | 2 | `cpv_exists_inv_sub_of_closed_unique` — CPV existence for 1/(z-z₀) |
| **Residue/FlatnessTransfer/PerTermVanishing.lean** | 24 | `pv_higher_order_term_tendsto_zero`, `holomorphic_cpv_tendsto_zero_on_convex`, `residueAt_sub_residueSum_eq_zero` |
| **Residue/FlatnessTransfer/HigherOrderAssembly.lean** | 34 | `higherOrderCancel_assembly_abstract` — main assembly theorem |
| **Residue/MeromorphicPrincipalPart.lean** | 13 | `meromorphicPrincipalPart`, `contourIntegral_principalPart_eq_zero_of_residue_zero` |
| **Residue/MultipointPV.lean** | 23 | `multipointPV_eq_sum_of_integral_zero`, `dominated_convergence_multipoint_helper` |
| **Residue/SectorCurve.lean** | ~35 | `sectorCurve`, `pv_sector_dz_over_z` — Lemma 3.1 PV = iα |
| **Residue/SectorCurveLemma.lean** | ~30 | `cauchyPV_sectorCurve_simplePole`, `generalizedWindingNumber_sectorCurve` = α/(2π) |
| **Residue/MeasureHelpers.lean** | 2 | `preimage_singleton_measure_zero_of_deriv_ne_zero` |

### Key Structures

```
PiecewiseC1Curve
  ├── toFun : ℝ → ℂ
  ├── a, b : ℝ           -- domain [a,b]
  ├── partition : Finset ℝ
  ├── continuous_toFun : Continuous toFun
  ├── differentiableOn_off_partition
  └── continuousOn_deriv_off_partition

PiecewiseC1Immersion extends PiecewiseC1Curve
  ├── deriv_ne_zero       -- off partition
  ├── left_deriv_limit    -- at partition points
  └── right_deriv_limit   -- at partition points

IsNullHomologous (in HomologicalCauchy.lean)
  ├── isClosed
  ├── image_subset_U
  └── winding_zero_outside_U

ContourCycle := Finsupp PiecewiseC1Immersion ℤ  (in Cycle.lean)
```

---

## 2. ValenceFormula/ (new)

**44 files, ~22,000 lines, 0 sorries**

### Import Graph

```
Definitions
  ├── Boundary/Basic ──── Boundary/Bounds ──── Boundary/Smooth
  │     │                                         │
  │     │    ┌────────────────────────────────────┘
  │     │    │
  │     ├── Boundary/Winding/RightEdge
  │     ├── Boundary/Winding/LeftEdge
  │     ├── Boundary/Winding/UnitArcHelpers ── UnitArc
  │     │
  │     ├── WindingWeights/Common
  │     │     ├── WindingWeights/I
  │     │     ├── WindingWeights/Rho
  │     │     └── WindingWeights/RhoPlusOne
  │     │
  │     ├── RectHomotopy/* (14 files) ──── InteriorWinding
  │     │
  │     ├── OnCurvePV/Basic ── EndpointCorner ── Main
  │     │
  │     ├── ModularInvariance
  │     │     └── OrbitPairing ── OrbitSum
  │     │
  │     └── PVChain/*
  │           ├── Helpers
  │           ├── ResidueSideInfra
  │           ├── OnCurveCapture
  │           ├── ArcContribution
  │           ├── Seg5CuspIntegral
  │           └── Assembly
  │
  ├── CoreIdentity
  ├── TextbookExistence ── TextbookForm
  └── WindingWeights
```

### Key Files

| File | Decls | Purpose |
|------|-------|---------|
| **Definitions.lean** | 22 | `ellipticPointI'`, `ellipticPointRho'`, `orderOfVanishingAt'`, `windingNumberCoeff'` |
| **Boundary/Basic.lean** | 33 | `fdBoundary`, `fdBoundary_H`, 5 segment defs, boundary value lemmas |
| **Boundary/Bounds.lean** | 33 | `fdBoundary_H_im_pos`, `fdBoundary_H_re_abs_le_half`, segment selectors |
| **Boundary/Smooth.lean** | ~45 | `fdBoundary_HImmersion`, derivatives, corner proofs |
| **InteriorWinding.lean** | ~14 | `gWN_fdBoundary_H_eq_neg_one_of_strictInterior` |
| **WindingWeights/I.lean** | ~25 | `gWN_fdBoundary_H_at_i` (= -1/2) |
| **WindingWeights/Rho.lean** | ~25 | `gWN_fdBoundary_H_at_rho` (= -1/6) |
| **WindingWeights/RhoPlusOne.lean** | ~25 | `gWN_fdBoundary_H_at_rho_plus_one` (= -1/6) |
| **ModularInvariance.lean** | ~20 | `ord_add_one_eq` (T), `ord_S_eq` (S), `exists_height_cusp_nonvanishing` |
| **OrbitPairing.lean** | ~35 | T/S pairing: `sum_ord_rightVert_eq_sum_ord_leftVert`, `sum_ord_rightArc_eq_sum_ord_leftArc` |
| **OrbitSum.lean** | ~20 | `Orbit`, `ordOrbit`, `finite_zeros_in_fd` |
| **CoreIdentity.lean** | ~18 | **`valence_formula_orbit_sum`** — the main theorem |
| **TextbookForm.lean** | ~30 | **`valence_formula_textbook_orbit_finsum`** — textbook packaging |
| **PVChain/Assembly.lean** | ~35 | `cpv_modular_side_tendsto`, `cpv_residue_side_tendsto` |
| **RectHomotopy/MainTheorem.lean** | large | Rectangular homotopy winding = -1 |

### Dependency Chain (top-level)

```
Winding weights (I, ρ, ρ+1)  ─┐
Interior winding (= -1)       ├─► CoreIdentity ─► TextbookExistence ─► TextbookForm
Boundary smooth winding (= -1/2) ─┤
Orbit pairing (T, S)          ─┤
PV chain assembly              ─┘
```

---

## 3. Modularforms/valence/ComplexAnalysis/ (old)

**52 files, ~106,000 lines, ~150 sorries (90 in *_Work.lean dev copies)**

This is the original monolithic development. The new `ValenceFormula/` directory is a clean split-file reorganization. Key legacy files:

| File | Lines | Sorries | Purpose |
|------|-------|---------|---------|
| ValenceFormula_PV.lean | 7,168 | 3 | Modular-side PV infrastructure |
| ValenceFormula_Rect_Homotopy.lean | 6,323 | 1 | Rectangular homotopy proof |
| ValenceFormula.lean | 8,124 | 17 | Original monolithic file |
| ValenceFormula_Core.lean | 1,998 | 5 | Core identity assembly |
| ValenceFormula_ResidueSide.lean | 4,604 | 4 | Residue-side assembly |
| ResidueTheory.lean | 6,222 | 0 | Standalone residue theory |
| WindingNumber.lean | 3,255 | 5 | Winding number theory |
| WindingNumberInterior.lean | 2,970 | 8 | Interior winding proofs |
| HomotopyBridge.lean | 2,635 | 0 | Homotopy invariance bridge |
| ValenceFormula_FD_Boundary.lean | 1,449 | 0 | Boundary curve definition |
| ValenceFormula_FD_Boundary_Param.lean | 1,053 | 0 | H-parameterized boundary |
| ValenceFormula_CPV_ModularSide.lean | 3,891 | 0 | CPV modular-side computation |
| ValenceFormula_FD_WindingWeights.lean | 3,269 | 0 | Winding weight FTC computations |
| ValenceFormula_FD_SmoothBoundaryWeights.lean | 2,921 | 0 | Smooth boundary winding |
| ValenceFormula_FD_OnCurvePVProvider.lean | 1,921 | 0 | CPV existence at on-curve points |
| **Work files** (3 files) | ~30,155 | 90 | Development copies — NOT canonical |

### Key Infrastructure (sorry-free, shared by both old and new)

| File | Key API |
|------|---------|
| Basic.lean | `PiecewiseC1Curve`, `PiecewiseC1Immersion`, `generalizedWindingNumber'` |
| Finiteness.lean | `piecewiseC1Immersion_finite_zeros` |
| HalfResidueTheorem.lean | `semicircle_integral_eq_pi_I`, `smooth_crossing_opposite_values` |
| BranchCutTracking.lean | `integral_logDeriv_slitPlane`, `liftedLogDiff` |
| PiecewiseHomotopy.lean | `windingNumber_eq_of_piecewise_homotopic` |
| HomotopyBridge.lean | `windingNumber_eq_of_homotopic_closed`, `contourIntegral_eq_of_homotopic` |
| ResidueTheory.lean | `generalizedResidueTheorem'`, `argumentPrinciple` |
| Infrastructure/CauchyTheorem.lean | `cauchyTheorem_convex`, `residue_simple_pole` |

---

## Cross-File Dependencies

### Import Graph (directories)

```
GeneralizedResidueTheory/
  └── (self-contained, imports only mathlib)

ValenceFormula/
  └── imports GeneralizedResidueTheory/

Modularforms/valence/ComplexAnalysis/
  └── (self-contained, parallel to GRT — some declarations duplicated)
```

### Key Declarations Used Across Files

| Declaration | Defined in | Used across |
|-------------|-----------|-------------|
| `PiecewiseC1Curve` | GRT/Basic | All of GRT, VF/Boundary |
| `PiecewiseC1Immersion` | GRT/Basic | All of GRT, VF/Boundary |
| `generalizedWindingNumber'` | GRT/Basic | GRT/*, VF/InteriorWinding, VF/WindingWeights |
| `cauchyPrincipalValueOn` | GRT/Residue | GRT/Cycle, GRT/HomologicalCauchy |
| `IsNullHomologous` | GRT/HomologicalCauchy | GRT/Cycle, GRT/GeneralizedResidueTheorem |
| `fdBoundary_H` | VF/Boundary/Basic | ~30 files in VF/ |
| `fdBoundary_HImmersion` | VF/Boundary/Smooth | VF/InteriorWinding, VF/WindingWeights, VF/PVChain |
| `ellipticPointI'` | VF/Definitions | ~15 files in VF/ |
| `windingNumberCoeff'` | VF/Definitions | VF/CoreIdentity, VF/TextbookForm |
| `ordOrbit` | VF/OrbitSum | VF/CoreIdentity, VF/TextbookForm |

---

## Consolidation Analysis

### A. Duplication Between Old and New ValenceFormula

The **biggest consolidation opportunity**: `Modularforms/valence/ComplexAnalysis/` (106k lines) contains the original monolithic development. `ValenceFormula/` (22k lines) is the clean split-file version. Many declarations exist in both.

**Recommendation**: The old directory can likely be reduced to:
1. **Infrastructure files** that are still imported (Basic, Finiteness, HalfResidueTheorem, BranchCutTracking, PiecewiseHomotopy, HomotopyBridge, Infrastructure/*)
2. **ResidueTheory.lean** (standalone, no duplication)
3. **Delete Work files** (*_Work.lean, ~30k lines) — these are development copies with sorries

**Estimated savings**: ~60-70k lines by removing duplicated and Work files.

### B. Duplication Between Old valence/ and GeneralizedResidueTheory/

Several core concepts are defined in both:

| Concept | Old location | New location |
|---------|-------------|-------------|
| `PiecewiseC1Curve` | valence/ComplexAnalysis/Basic | GRT/Basic |
| `PiecewiseC1Immersion` | valence/ComplexAnalysis/Basic | GRT/Basic |
| `generalizedWindingNumber'` | valence/ComplexAnalysis/Basic | GRT/Basic |
| `cauchyPrincipalValue'` | valence/ComplexAnalysis/Basic | GRT/Basic |
| `ModelSectorCurve` | valence/ComplexAnalysis/Basic | GRT/Basic |
| Homotopy invariance | valence/ComplexAnalysis/HomotopyBridge | GRT/Homotopy/Invariance |
| Circle param winding | valence/ComplexAnalysis/WindingNumberInterior | GRT/Homotopy/CircleParam |
| PV integrability | valence/ComplexAnalysis/PrincipalValue | GRT/PrincipalValue |
| Cauchy theorem (convex) | valence/ComplexAnalysis/Infrastructure/CauchyTheorem | GRT/CauchyPrimitive |

**Recommendation**: Migrate the old `valence/ComplexAnalysis/` infrastructure files to import from `GeneralizedResidueTheory/` rather than defining their own copies, or delete them if the new `ValenceFormula/` already imports GRT.

### C. Work Files (Candidates for Deletion)

| File | Lines | Sorries | Status |
|------|-------|---------|--------|
| ValenceFormula_Core_Work.lean | 9,422 | 31 | Dev copy of Core — delete |
| ValenceFormula_Homotopy_Work.lean | 9,423 | 32 | Dev copy of Homotopy — delete |
| ValenceFormula_PV_Work.lean | 11,310 | 27 | Dev copy of PV — delete |

**Total**: 30,155 lines removable immediately.

### D. Potentially Removable Files

| File | Lines | Reason |
|------|-------|--------|
| polygonToCircleRadial.lean | 29 | Single sorry, unused |
| ValenceFormula.lean (monolithic) | 8,124 | Superseded by split files |
| ValenceFormula_Final_Split.lean | 1,036 | Forwarding wrappers only |
| ValenceFormula_Final_WithData.lean | 193 | Forwarding wrappers only |

### E. Sorries Remaining (non-Work files)

| File | Count | Declarations |
|------|-------|-------------|
| Infrastructure/CauchyTheorem.lean | 4 | generalizedResidueTheorem, residueTheorem_classical, pv_exists_simple_pole, modelSector_windingNumber |
| Infrastructure/LHopital.lean | 5 | lhopital helpers |
| WindingNumber.lean | 5 | generalizedWindingNumber_eq_angleContribution_single area |
| WindingNumberInterior.lean | 8 | piecewise_deriv_bounded_ae/bounded + homotopy helpers |
| ValenceFormula_Core.lean | 5 | Assembly glue |
| ValenceFormula_PV.lean | 3 | PV existence/cancellation |
| ValenceFormula_ResidueSide.lean | 4 | Residue-side assembly |
| ValenceFormula_Final.lean | 1 | valenceFormula forwarding |
| ValenceFormula_Final_AxiomClean.lean | 2 | Axiom-clean variants |
| ValenceFormula_Final_Split.lean | 3 | Split forwarding |
| ValenceFormula_InteriorWinding.lean | 1 | Interior winding bridge |
| ValenceFormula_Rect_Homotopy.lean | 1 | Rect homotopy lemma |

**Note**: These are in the **old** `valence/ComplexAnalysis/` directory. The **new** `GeneralizedResidueTheory/` and `ValenceFormula/` directories are **sorry-free**.

### F. maxHeartbeats Usage

Files with elevated heartbeat limits (potential performance concerns):

| File | Max Setting |
|------|------------|
| GRT/HomologicalCauchy.lean | 1,600,000 |
| GRT/Homotopy/ParametricDiff.lean | 2,000,000 |
| VF/Boundary/Smooth.lean | 1,600,000 |
| VF/Boundary/Winding/RightEdge.lean | 1,600,000 |
| VF/InteriorWinding.lean | 1,600,000 |
| VF/WindingWeights/I.lean | 800,000 |
| VF/WindingWeights/Rho.lean | 800,000 |
| VF/WindingWeights/RhoPlusOne.lean | 800,000 |
| old/ValenceFormula_FD_OnCurvePVProvider.lean | **32,000,000** |
| old/ValenceFormula_FD_SmoothBoundaryWeights.lean | **8,000,000** |
| old/ValenceFormula_FD_WindingWeights.lean | **16,000,000** |
| old/ValenceFormula_TextbookOrbitFinsum.lean | 3,200,000 |

---

## Top Priorities

1. **Delete Work files** — 30k lines of sorry-bearing dev copies (`*_Work.lean`)
2. **Consolidate old/new duplication** — migrate old `valence/ComplexAnalysis/` infrastructure to import from `GeneralizedResidueTheory/` rather than duplicating definitions
3. **Performance** — the old `FD_OnCurvePVProvider.lean` (32M heartbeats) and `FD_WindingWeights.lean` (16M heartbeats) are the worst offenders; the new `ValenceFormula/` equivalents use at most 1.6M
