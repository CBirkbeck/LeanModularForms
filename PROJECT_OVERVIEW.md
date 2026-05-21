# Project Overview: LeanModularForms

**Generated**: 2026-05-21 via `/mathlib-quality:overview`
**Scope**: entire `LeanModularForms/` project (220 files, 79,727 lines)
**Method**: 3 parallel Phase-1 inventory workers (by directory) + 1 Phase-2 deep-analysis worker (mathlib audit, duplications, generalizations, API gaps, junk identification)
**Branch**: `feat/mathlib-prs`
**Supersedes**: previous PROJECT_OVERVIEW.md from 2026-05-13.

---

## Executive Summary

LeanModularForms is a substantial Lean 4 / Mathlib project formalizing modular-form analysis, the Hungerbühler–Wasem generalised residue theorem (HW Theorem 3.3), the textbook valence formula for weight-`k` modular forms on `SL₂(ℤ)`, and Viazovska's E₈ sphere-packing magic function. After a recent project-wide `/cleanup-all` pass (~13,500 lines removed; protected theorems verified throughout), the codebase is **79,727 lines across 220 `.lean` files** organised under three top namespaces: `ForMathlib/` (analytic foundations, 119 files), `Modularforms/` (modular-form definitions, 47 files), and `SpherePacking/` (Viazovska function, 3 files).

The two **headline theorems** are:
- `valence_formula_textbook` in `ForMathlib/ValenceFormulaFinal.lean` — the unconditional textbook valence formula
- The `hw_3_3_clean*` family (8 variants) in `ForMathlib/HW33Clean.lean` — the clean general HW Theorem 3.3

Both depend only on `[propext, Classical.choice, Quot.sound]`.

The deep review identifies four major themes that drive the recommended action plan:

1. **Variant ratchets** — `residueTheorem_crossing_*` (32 variants across 2 files), `hw_3_3_*` (8 variants in one file), `dixonFunction_eq_zero` (13 variants). Each cluster has an unambiguously strongest member; the others are scar tissue from incremental generalisation.
2. **Side-mirrored pairs** — `BoundaryWindingSeg{1,4}Proof`, `Seg{1,4}FTCProvider`, etc. are line-for-line mirrors that differ only by which vertical side of the FD they describe. Saved: ~600 lines after parametrising over side.
3. **Triple FD-boundary parametrisation** — `FDBoundary.lean` (`[0,1]`) + `FDBoundaryH.lean` (`[0,5]`) + `FDBoundaryReparametrization.lean` (the glue). Picking `[0,5]` as canonical removes ~600 lines.
4. **Mathlib-bridge surface** — `HasSimplePoleAt`, `poleOrderAt`, `principalPartSum`, `HasCauchyPV{On}`, `HasGeneralizedWindingNumber`, the bespoke piecewise-C¹ path types. Three of these have direct mathlib counterparts; two should be upstreamed to mathlib.

## Statistics

| Metric | Value |
|---|---|
| Files | 220 |
| Total lines | 79,727 |
| Sorries | 10 (8 in `Modularforms/FG.lean`, 1 in `Derivative.lean`, 1 in `DimensionFormulas.lean`) |
| `set_option` directives | 3 (in 2 files) |
| File size: tiny (<50 lines) | 21 files |
| File size: small (50–200) | 68 files |
| File size: medium (200–700) | 105 files |
| File size: large (700–1500) | 24 files |
| File size: XL (>1500) | 2 files (`MultiCrossingCPV.lean` 5035, `Crossing.lean` 2911) |
| Moral duplication clusters | 15 (10+ confirmed in code) |
| Variant-ratchet clusters | 3 (HW33, residueTheorem_crossing, dixonFunction_eq_zero) |
| Definitions to replace with mathlib | 2 (HasSimplePoleAt, poleOrderAt) |
| Mathlib upstream candidates | 6 |
| Junk / merge-candidates | 12 files |
| Estimated lines savable if all actions executed | ~3,500 |

---

## Part 1: Project Inventory

Per-directory inventories (full detail) live in `/tmp/lmf_overview/phase1_*.md` on the machine where this was generated. Headline points:

### ForMathlib root (106 files, ~33,500 lines)
- **HW33 family** (16 files, 3,706 lines): `HW33Clean.lean` exports 8 `hw_3_3_clean*` variants. `HW33Tight.lean` (89 lines) is the paper-faithful canonical form.
- **HungerbuhlerWasem subdirectory** (13 files, ~16,000 lines): two giants `MultiCrossingCPV.lean` (5035) and `Crossing.lean` (2911) account for ~half.
- **FD-boundary trio**: `FDBoundary.lean` (350), `FDBoundaryH.lean` (335), `FDBoundaryReparametrization.lean` (302) — three parallel parametrisations of the same curve.
- **Side-mirror pairs**: `BoundaryWindingSeg{1,4}Proof.lean` (240/237 lines), `Seg{1,4}FTCProvider.lean` (629/659), `CrossingAt{I,Rho}.lean`, `ArcFTC{AtI,Generic}.lean`.
- **Bridge files**: `MeromorphicBridge.lean` (187), `PoincareBridge.lean` (140), `ResidueSideBridge.lean` (67). Two will shrink/vanish after the duplications below are unified; `PoincareBridge` is the right kind of narrow bridge.

### ValenceFormula subtree (17 files, ~7,700 lines)
- Apex `PVChain.lean` (51 lines) — the modular-side vs residue-side equality that feeds `valence_formula_textbook`.
- Per-singular-point files `WindingWeights/{I,Rho,RhoPlusOne}.lean` (1003/693/721 lines after cleanup).
- Largest: `OnCurvePV/Main.lean` (855), `WindingWeights/I.lean` (954).
- **Naming clash**: `Boundary/Bounds.lean` uses `seg1..seg5`; `WindingWeights/Common.lean` uses `seg0..seg4` for the same five pieces.

### GeneralizedResidueTheory subtree (27 files, ~10,143 lines)
- Zero sorries, well-organised into `Homotopy/`, `OnCurvePV/`, `PVInfrastructure/`, `Residue/`, `WindingNumber/`.
- Main public API: `Residue.lean` + `Residue/GeneralizedTheoremBase.lean` (`generalizedResidueTheorem'`, `residueAt`, `cauchyPrincipalValueOn`).
- Largest: `WindingNumber/CrossingAnalysis.lean` (937), `Residue/SectorCurveLemma.lean` (812), `PVInfrastructure/StepBounds.lean` (659).

### Modularforms (47 files, ~11,606 lines)
- All 10 project sorries are here: 8 in `FG.lean`, 1 each in `Derivative.lean` (`antiSerreDerPos`) and `DimensionFormulas.lean` (`FiniteDimensional` for arbitrary finite-index Γ).
- **Stub files**: `cotangent.lean` (15 lines, upstreamed), `test.lean` (6 lines scratch), `Generators.lean` (5 lines barrel).
- **Modular-form definitions**: `Delta.lean` (Δ), `Eisenstein.lean` (E₄,E₆), `Eisensteinqexpansions.lean` (general E_k), `E2.lean` (G₂, quasi-modular E₂), `JacobiTheta.lean` (Θ₂/₃/₄, H₂/₃/₄), `ThetaDerivIdentities.lean`, `IsCuspForm.lean`.
- **Co-existing duplicates**: `eta.lean` (175) and `eta_cleanup.lean` (324).
- Largest: `summable_lems.lean` (1467), `FG.lean` (1037), `Eisenstein.lean` (904).

### SpherePacking (3 files, 1287 lines)
- `ViazovskaMagicFunction.lean` (860) builds `a(r) = I12 + I34 + I5 + I6` using the original triangular Viazovska contours. Per the docstring + `SpherePacking/README.md`, the endgame is to use `Residue/GeneralizedTheoremBase.lean` to handle cusps at `z ∈ {-1, 0, 1}` via CPV — competing with the alternative rectangular-contour deformation in the sister Sphere-Packing-Lean repo.
- `CuspDecay.lean` (373) holomorphic decay bounds.
- `PhiHolomorphic.lean` (54) thin glue.

---

## Part 2: Cross-File Dependencies

Two top-level barrel files:
- `LeanModularForms.lean` — root umbrella (does **not** import `ValenceFormulaFinal` or `HW33Clean`; axiom checks must `import` those files directly).
- `LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber.lean` — sub-barrel re-exporting `Defs`/`CrossingAnalysis`/`Decomposition`.

**Pathological imports**:
- Importing both `LeanModularForms.ForMathlib.MultipointPV` and `LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MultipointPV` in the same script fails: duplicate `finset_discrete_min_sep._simp_1_3`. Two files independently define `finset_discrete_min_sep`. Use separate axiom-check scripts.

**Chain leading to `valence_formula_textbook`**: ValenceFormulaFinal → ValenceFormulaBridged → ValenceFormula (orbits/canonical reps) → PVChain → {Assembly (modular side), Assembly/ResidueSide (residue side)} → {WindingWeights/{I,Rho,RhoPlusOne}, OnCurvePV/{Main,EndpointCorner}, Boundary/{Smooth,Bounds}, PVChain/{ArcContribution,Helpers,Seg5CuspIntegral,ResidueSideInfra,OnCurveCapture}}.

**Chain leading to `hw_3_3_clean`**: HW33Clean → {HW33SimpleClean (single-crossing avoidance), MultiCrossingCPV} → HungerbuhlerWasem/{Crossing, CPVExistence, LaurentExtraction, MultiPoleDCT, LocalCutoffs, CrossingDataBuilder, …} → GeneralizedResidueTheory/{Residue, WindingNumber, …}.

---

## Part 3: Mathlib API Audit

### 3.1 `HasSimplePoleAt` — duplicated in-project, has mathlib equivalent (CRITICAL)

- Defined **twice**: `ForMathlib/Residue.lean:39` and `ForMathlib/GeneralizedResidueTheory/Residue.lean:67` (identical bodies).
- Mathlib equivalent: `MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ = -1`.
- Existing bridge: `ForMathlib/MeromorphicBridge.lean` proves both directions.
- **Action**: delete the GRT copy and import the canonical one; long-term, redefine the project predicate as an `abbrev` over the mathlib statement so the bridge file collapses to a few `simp` lemmas.

### 3.2 `poleOrderAt` — duplicates `meromorphicOrderAt`

- Project: `ForMathlib/PrincipalPart.lean` defines `poleOrderAt` as a `ℕ`-valued helper.
- Mathlib: `meromorphicOrderAt f z₀ : WithTop ℤ` (`Mathlib.Analysis.Meromorphic.Order`).
- **Action**: redefine `poleOrderAt f z₀ := (-(meromorphicOrderAt f z₀)).untop₀.toNat`; the bespoke recursion goes away. Bridge lemmas collapse to one line each.

### 3.3 `HasCauchyPV` / `HasCauchyPVOn` — no mathlib equivalent yet (KEEP, upstream candidate)

- Project: `ForMathlib/CauchyPrincipalValue.lean` (242 lines).
- Mathlib has no integral PV API.
- **Action**: keep. Re-organise so the single-pole and multi-pole forms are defined in one place; currently `cauchyPrincipalValueOn` is re-introduced in `GeneralizedResidueTheory/Residue.lean:~80-170`, competing with `HasCauchyPVOn`. Strong upstream-PR candidate once API stabilises.

### 3.4 `HasGeneralizedWindingNumber` — no mathlib equivalent (KEEP, upstream candidate)

- Project: `ForMathlib/GeneralizedWindingNumber.lean`.
- Mathlib only has holomorphic `circleIntegral` / Cauchy-formula winding for the standard ball case.
- **Action**: keep; foundational lemmas (`.eq`, `.unique`, `.neg`) are clean — upstream to mathlib once the design has settled.

### 3.5 `principalPartSum` — locally useful, no direct mathlib

- Project: `ForMathlib/PrincipalPart.lean` defines `principalPartSum S c z := ∑ s ∈ S, c s / (z - s)`.
- Mathlib has `Polynomial.partialFractions` / `MeromorphicAt.laurent` but no finite-Finset simple-pole sum helper.
- **Action**: keep; rename to `Finset.principalPartSum` and add missing algebra lemmas (`_add`, `_sub`, `_const_mul`).

### 3.6 Four parallel curve types (HIGH PRIORITY)

Project has FOUR coexisting piecewise-C¹ curve abstractions:
- `PiecewiseC1Path x y` (in `PiecewiseC1Path.lean:52`, open-interval, extends mathlib `Path`).
- `PwC1Immersion x y` (in `PiecewiseC1Path.lean:122`, adds non-vanishing derivative).
- `PiecewiseC1Curve` (in `ClassicalCPV.lean:53`, no endpoints).
- `ClosedPwC1Curve x` / `ClosedPwC1Immersion x` (in `PaperPwC1Immersion.lean`, closed-interval / paper-faithful).

Mathlib has only `Path x y`.
- **Action**: keep `PiecewiseC1Path` canonical, express `PiecewiseC1Curve` as `Σ x, PiecewiseC1Path x x`, and refactor `ClosedPwC1Curve` to be a structural property rather than a new type. The pairwise conversion theorems in `PaperPwC1Immersion.lean:~600` collapse into definitional equalities.

### 3.7 `PoincareBridge.lean` — keep (right kind of narrow bridge)

- Mathlib has `Complex.IsExactOn` / `DifferentiableOn` primitives on convex sets.
- Project bridge (140 lines) is a thin glue file from mathlib to project `PiecewiseC1Path` contour integrals.
- **Action**: keep; this is exactly the right level of indirection.

### 3.8 Custom FD segments — could use mathlib `Path.trans`

- `FDBoundary.lean` / `FDBoundaryH.lean` hard-code five segments + arc with per-piece `re`/`im`/`at_t` parametrisation.
- Could be assembled via `Path.trans` and `Set.Icc.affineHomeomorph` from five named pieces.
- **Action**: re-architect as `Path.trans₅` (or an explicit indexed assembly lemma); eliminates 5× per-segment parametrisation boilerplate.

---

## Part 4: Moral Duplications

This is the **highest-priority axis** for this project: a large amount of "same lemma, slightly different hypothesis" code has accreted over ~9 months of development. Pairwise table follows; top-10 concrete UNIFY actions below.

### Pairwise table

| # | Pair (or cluster) | Loc A | Loc B | Status | Action |
|---|---|---|---|---|---|
| 1 | `HasSimplePoleAt` (the def) | `ForMathlib/Residue.lean:39` | `ForMathlib/GeneralizedResidueTheory/Residue.lean:67` | **identical** | delete GRT copy; long-term redefine via mathlib |
| 2 | `HW33*` flat fan-out (16 files) | `ForMathlib/HW33*.lean` | — | naming ratchet | merge into 3 thematic files; 8→1+5 corollaries |
| 3 | `residueTheorem_crossing_*` (32 variants) | `Crossing.lean` (21) | `MultiCrossingCPV.lean` (11) | naming ratchet | promote strongest spec; private the rest |
| 4 | `dixonFunction_eq_zero` (13 variants) | `DixonTheorem.lean` | (intra-file) | naming ratchet | keep `_of_nullHomologous_convex_full`; alias others |
| 5 | `BoundaryWindingSeg{1,4}Proof.lean` | 240 lines | 237 lines | **near-mirror** | factor common helper over side |
| 6 | `Seg{1,4}FTCProvider.lean` | 629 lines | 659 lines | **near-mirror** | extract `VertSegFTCProvider` over side |
| 7 | `FDBoundary` triple | `FDBoundary.lean` (350) | `FDBoundaryH.lean` (335) + `FDBoundaryReparametrization.lean` (302) | parallel API | pick `[0,5]`; delete `[0,1]` and reparam (-600) |
| 8 | `eta.lean` vs `eta_cleanup.lean` | 175 lines | 324 lines | live duplicate | unify on the mathlib-eta version; delete primed copy (-324) |
| 9 | Seg naming `seg1..5` vs `seg0..4` | `Boundary/Bounds.lean` | `WindingWeights/Common.lean` | naming clash | rename `Common.lean` to match |
| 10 | `analyticAt_logDeriv_off_zeros` and `_off_zeros'` | `PVChain/ArcContribution.lean:45` (`private`) | `PVChain/ResidueSideInfra.lean:84` (public) | **identical** | delete private copy |
| 11 | `IsScalarTower ℝ ℂ ℂ` / `NormSMulClass ℝ ℂ` (4 copies) | `ForMathlib/Instances.lean` | `WindingWeights/Common.lean`, `Boundary/Smooth.lean`, `SpherePacking/ViazovskaMagicFunction.lean` | **4× copies** | keep `Instances.lean` only |
| 12 | `exists_height_bound_S` vs `exists_height_above_sqrt3_and_S` | `PVChain/Helpers.lean:205` | `PVChain/Assembly/ResidueSide.lean:54` | near-duplicate | inline into one helper |
| 13 | 4 parallel curve types | `PiecewiseC1Path` | `PiecewiseC1Curve` + `ClosedPwC1Curve/Immersion` | parallel types | unify on `PiecewiseC1Path` |
| 14 | `UpperHalfPlane.lean` (one fact `S²=-1`) | `ForMathlib/UpperHalfPlane.lean` (12 lines) | `Modularforms/ForMathlib_UpperHalfPlane.lean` (13 lines) | **identical** | delete one; upstream to mathlib |
| 15 | `FunctionsBoundedAtInfty` (one fact `IsBoundedAtImInfty.neg`) | `ForMathlib/FunctionsBoundedAtInfty.lean` (9 lines) | `Modularforms/ForMathlib_FunctionsBoundedAtInfty.lean` (13 lines) | **identical** | delete one; upstream to mathlib |
| 16 | `SlashActions.lean` | `ForMathlib/SlashActions.lean` (44 lines) | `Modularforms/ForMathlib_SlashActions.lean` (43 lines) | **identical** | delete one; redirect imports |

### Top duplication action items (concrete)

#### F1: HW33* fan-out (16 files → ~6 files; saves ~700 lines)
- Pick `hw_3_3_tight` (in `HW33Tight.lean`) as canonical statement.
- Move `hw_3_3_paper` into the same file as a `ClosedPwC1Immersion` corollary.
- Promote `hw_3_3_clean_full_mero` (strongest variant in `HW33Clean.lean`) as one further corollary; delete the other 7 `hw_3_3_clean_*`.
- Inline `HW33ExitTimeWrapper.lean`, `HW33Final.lean`, `HW33Closed.lean` into `HW33Tight.lean` as a final section.
- Collapse the 4-file `HW33HigherOrder{Auto,C3,C4}.lean` chain into a single `HW33HigherOrder.lean`.
- Merge `HW33Laurent{PolarPart,Simple}.lean` → `HW33Laurent.lean`.

#### F2: `residueTheorem_crossing_*` (32 → ~5 variants; saves ~600 lines)
- Promote `residueTheorem_crossing_truly_full_spec` (`Crossing.lean:2769`) as canonical multi-pole result.
- Promote `residueTheorem_crossing_paper_faithful_clean` (`MultiCrossingCPV.lean:4812`) as canonical `ClosedPwC1Immersion` form.
- Mark all intermediates `_card_le_one_full_spec_*`, `_asymmetric_*`, `_singleton_*`, `_compositional`, `_full_spec_no_basepoint_*` as `private`.
- After private-marking, walk the import graph and delete the ~20 of 32 variants that have no remaining callers.

#### F3: `dixonFunction_eq_zero` (13 → 4 variants; saves ~300 lines)
- Promote `dixonFunction_eq_zero_of_nullHomologous_convex_full` as canonical.
- Express `_of_bounds`, `_autoH1`, `_autoH2`, `_autoBounds`, `_open_full`, `_unbounded` as thin wrappers.

#### F4: `BoundaryWindingSeg{1,4}Proof.lean` (2 files → 1; saves ~150 lines)
- Replace both with single `BoundaryWindingVertSegProof.lean` parametrised over `side : ℂ ∈ {1/2, -1/2}` and `t_start : ℝ ∈ {0, 3/5}`.
- Re-export the two `smoothBoundaryData_seg{1,4}_of_ftcHyp` as one-line wrappers.

#### F5: `Seg{1,4}FTCProvider.lean` (2 files → 1; saves ~600 lines)
- Same pattern as F4 but larger: create `VertSegFTCProvider.lean` parametrised over side.
- `arcFTCHyp_seg1` / `arcFTCHyp_seg4` become one-line wrappers.

#### F6: FD-boundary triple (3 files → 1; saves ~600 lines)
- Pick `fdBoundary_H` (the `[0,5]` parametrisation) as canonical — every downstream file in `ValenceFormula/` already uses it.
- Delete `fdBoundaryFun` and derived lemmas in `FDBoundary.lean`.
- Move FD-membership lemmas (e.g. `fdHeightValid`) into `FDBoundaryH.lean`.
- Delete `FDBoundaryReparametrization.lean` outright (302 lines).

#### F7: `eta.lean` vs `eta_cleanup.lean` (2 → 1 file; saves ~325 lines)
- Prove `dedekindEtaFun' = ModularForm.eta ∘ (· : ℍ → ℂ)` (one-line `rfl` after rewriting).
- Migrate `SpherePacking/PhiHolomorphic.lean` to use the mathlib-eta primitives from `eta.lean`.
- Delete `eta_cleanup.lean`.

#### F8: Seg naming conflict — pure textual rename
- Rename `WindingWeights/Common.lean` lemmas from `seg0..seg4` to `seg1..seg5` to match `Boundary/Bounds.lean`. No proof changes.

#### F9: `analyticAt_logDeriv_off_zeros{,'}` — delete private copy
- Replace its single use at `ArcContribution.lean:194` with the public version from `ResidueSideInfra.lean`.

#### F10: 4-way duplicate `IsScalarTower`/`NormSMulClass` instances
- Delete the three non-canonical copies; ensure `ForMathlib/Instances.lean` is imported transitively.

---

## Part 5: Generalization Opportunities

The project is domain-specific to `ModularForm Γ(1) k` and SL₂(ℤ) fundamental-domain analysis, so the generalisation surface is small. Findings:

### G1: `ResToImagAxis.lean` predicates → general ray restriction
- `Modularforms/ResToImagAxis.lean` (443 lines) defines `ResToImagAxis.Real`/`.Pos`/`.EventuallyPos` only for the positive imaginary axis. The proofs use only that the imaginary axis is a ℝ-vector subspace.
- **Action**: generalise to any straight ray `t ↦ z₀ + t·d`; restrict at the use site in `FG.lean`.
- **Difficulty**: Low.

### G2: `CongruenceSubgrps.lean::width` → all congruence subgroups
- The 71-line file only handles `Gamma N` width but proofs work for any subgroup containing a power of `T`.
- **Action**: relax `Γ = Gamma N` hypothesis to "`Γ` contains some `T^n`".
- **Difficulty**: Low.

### G3: `PiecewiseC1Path` over `ℝ → ℂ` — already general
- Stated for general normed space `E`. No action.

### G4: FD-specific segments — do NOT generalise
- The seg1..seg5 parametrisation is deeply tied to SL₂(ℤ) FD geometry. Generalising to `Γ₀(N)` etc. is research-level.

### G5: `HasGeneralizedWindingNumber` — already general
- Stated for arbitrary curves `[0,1] → ℂ`. No action.

---

## Part 6: API Improvements

### A1: Missing `MeromorphicAt` ↔ `HasSimplePoleAt` bidirectional `@[simp]`
- Adding `@[simp] theorem hasSimplePoleAt_iff_meromorphicAt_order_neg_one` would let users `simp` away the bridge entirely.

### A2: Missing `Finset.principalPartSum` algebra
- `principalPartSum_add`, `_sub`, `_const_mul` are easy to add and would shorten downstream proofs.

### A3: Missing `PiecewiseC1Path.trans` (and 5-fold variant)
- The five FD segments are hand-assembled via `Function.piecewise` cascade in `FDBoundaryH.lean:65`. A `trans` operation would shrink the file ~150 lines.

### A4: Missing `MeromorphicAt.logDeriv_hasSimplePoleAt`
- `LogDerivModularForm.lean::logDeriv_hasSimplePoleAt_of_order` says "log-deriv of a function with finite order has a simple pole with residue = order". Mathlib has all ingredients but not the named lemma.
- **Action**: clean-room rewrite, upstream to mathlib.

### A5: `ClosedPwC1Curve.trans` and `_cyclicShift_eq_of_…`
- `PaperPwC1Immersion.lean` has a 250-line `cyclicShift` development that would be much cleaner if the curve type were `PiecewiseC1Path` (see Part 3.6).

### A6: Missing `IsBoundedAtImInfty.neg` in mathlib
- The 9-line `ForMathlib/FunctionsBoundedAtInfty.lean` exists only because mathlib lacks this one fact.
- **Action**: upstream.

---

## Part 7: Junk / Removable

### J1: `Modularforms/cotangent.lean` (15 lines) — DELETE
Entire content is a docstring saying "upstreamed to mathlib". Zero declarations.

### J2: `Modularforms/test.lean` (6 lines) — DELETE
Scratch file with `import Mathlib`, a comment, and a `#find_home`.

### J3: `Modularforms/Generators.lean` (5 lines) — INLINE
Pure barrel of three Generators sub-imports. Inline into `LeanModularForms.lean`.

### J4: `ForMathlib/GeneralizedResidueTheory/WindingNumber.lean` (18 lines) — INLINE
Pure barrel of WindingNumber sub-modules. Inline at use sites.

### J5: `ForMathlib/UpperHalfPlane.lean` (12 lines) — DUPLICATE
Identical to `Modularforms/ForMathlib_UpperHalfPlane.lean`. Delete one; upstream the single fact `ModularGroup.modular_S_sq`.

### J6: `ForMathlib/FunctionsBoundedAtInfty.lean` (9 lines) — DUPLICATE
Identical to `Modularforms/ForMathlib_FunctionsBoundedAtInfty.lean`. Delete one; upstream `isBoundedAtImInfty_neg_iff`.

### J7: `Modularforms/ForMathlib_Cusps.lean` (21 lines) — UPSTREAM
Two facts `zero_at_cusps_of_zero_at_infty`, `bounded_at_cusps_of_bounded_at_infty`. Upstream to mathlib; locally merge into `Modularforms/AtImInfty.lean` (27 lines) until upstreamed.

### J8: `Modularforms/ForMathlib_SlashActions.lean` (43 lines) ≡ `ForMathlib/SlashActions.lean` (44 lines) — DUPLICATE
Keep `ForMathlib/SlashActions.lean`; delete the Modularforms copy; redirect imports.

### J9: Tiny utility files in Modularforms — MERGE into `FilterUtils.lean`
- `Modularforms/upperhalfplane.lean` (21) — `pnat_div_upper`, `pos_nat_div_upper`
- `Modularforms/tendstolems.lean` (41) — five `tendsto_*` lemmas
- `Modularforms/exp_lems.lean` (36) — three exp-on-UHP lemmas → into `qExpansion_lems.lean`
- `Modularforms/riemannZetalems.lean` (37) — single `zeta_two_eqn` lemma → into `Eisenstein.lean`
- `Modularforms/equivs.lean` (46) — six small `Equiv` helpers, inline at use sites
- `Modularforms/AtImInfty.lean` (27), `Modularforms/limunder_lems.lean` (60) — consider unified `FilterUtils.lean`

### J10: `ForMathlib/TrigLemmas.lean` (30), `ForMathlib/Instances.lean` (31) — KEEP / UPSTREAM
Both load-bearing. Upstream `TrigLemmas` (`exp_real_angle_I`, `cos_two_pi_div_three`, `sin_two_pi_div_three`). `Instances.lean` should disappear once the mathlib instance-synthesis gap is fixed.

### J11: Bridge files that should die after their target is unified
- `ForMathlib/ResidueSideBridge.lean` (67 lines) — vanishes after F6 (FD parametrisation unification).
- `ForMathlib/FDBoundaryReparametrization.lean` (302 lines) — see F6.
- `ForMathlib/MeromorphicBridge.lean` (187 lines) — shrinks to 2 `simp` lemmas after F1/A1.
- `ForMathlib/PoincareBridge.lean` (140 lines) — **keep**; legitimate narrow bridge.

### J12: `ForMathlib/CongruenceSubgrps.lean` (71 lines) — UPSTREAM
Pure mathlib material (`Gamma N` width). Upstream and delete locally.

---

## Part 8: Recommended Action Plan

### Priority 1: Quick wins (1–2 days each, low risk)
- **P1a** (F8): Rename `WindingWeights/Common.lean` `seg0..seg4` → `seg1..seg5`. Pure textual.
- **P1b** (F9, F10): Delete private `analyticAt_logDeriv_off_zeros` and the three duplicate `IsScalarTower` instances. Pure deletions.
- **P1c** (J1, J2, J3, J5, J6, J8): Delete the 6 stub/duplicate files (`cotangent`, `test`, the two `ForMathlib_*Plane`/`*BoundedAtInfty`, `ForMathlib_SlashActions`, the two barrels).
- **P1d** (3.1, 3.2): Delete the duplicate `HasSimplePoleAt` def; redefine `poleOrderAt` via `meromorphicOrderAt`.

**Expected**: ~9 files deleted, ~250–400 lines removed.

### Priority 2: Side-mirror unification (4–6 days, medium risk)
- **P2a** (F4): Replace `BoundaryWindingSeg{1,4}Proof.lean` with single side-parametrised file.
- **P2b** (F5): Replace `Seg{1,4}FTCProvider.lean` with single `VertSegFTCProvider.lean`. Largest single saving (~600 lines).
- **P2c** (F6): Unify FD-boundary trio onto `[0,5]`; delete `FDBoundary.lean` and `FDBoundaryReparametrization.lean`.

**Expected**: ~1,350 lines removed.

### Priority 3: Variant-ratchet cleanup (3–5 days, medium risk)
- **P3a** (F2): `residueTheorem_crossing_*` — promote two canonical statements, private-mark all intermediates, walk import graph and delete unreferenced (-600 lines).
- **P3b** (F3): `dixonFunction_eq_zero` — promote canonical, alias others (-300 lines).
- **P3c** (F1): HW33 fan-out — merge 16 files into ~6 (-700 lines).

**Expected**: ~1,600 lines removed; clearer public API.

### Priority 4: Structural / curve-type unification (1–2 weeks, higher risk)
- **P4a** (3.6, A5): Unify the 4 piecewise-C¹ curve types onto `PiecewiseC1Path`. `cyclicShift` development becomes simpler.
- **P4b** (F7): Migrate `eta_cleanup.lean` to mathlib `ModularForm.eta`; delete primed copy.
- **P4c** (3.8, A3): Re-architect FD segments via `Path.trans`.

**Expected**: ~600+ lines removed; major API cleanup.

### Priority 5: Mathlib upstream PRs (3–5 PRs)
- **Up1**: `MeromorphicAt.logDeriv_meromorphicOrderAt_eq_neg_one_of_…` (A4).
- **Up2**: `IsBoundedAtImInfty.neg` and friends (A6, J6, J7).
- **Up3**: `ModularGroup.modular_S_sq` (J5).
- **Up4**: `Gamma N` width API (G2, J12).
- **Up5**: Trig identities (`exp_real_angle_I`, `cos/sin_two_pi_div_three`) (J10).
- **Up6**: Long-term: `HasCauchyPV{On}` and `HasGeneralizedWindingNumber` once stabilised.

**Expected**: 6 upstream PRs; ~150 lines removed locally after they merge.

---

## Summary metric

If all proposed actions are executed:
- **Files deleted**: ~16
- **Lines saved**: ~3,500 (best case)
- **Naming clarifications**: ~35 lemmas
- **Mathlib upstream candidates**: 6
- **Public API simplifications**: ~50 `_full_spec_*` / `_truly_*` / `_paper_faithful_*` variants collapsed into ~10 canonical statements

---

## Top 5 Action Items (printed at end of /overview run)

1. **Delete the duplicate `HasSimplePoleAt` definition** in `GeneralizedResidueTheory/Residue.lean:67` — straight redundancy, identical body.
2. **Promote `residueTheorem_crossing_truly_full_spec` and `paper_faithful_clean` as canonical**; mark the other 30 variants `private`; delete those without callers (~600 lines).
3. **Unify `Seg{1,4}FTCProvider.lean` into `VertSegFTCProvider.lean`** parametrised over side — largest single side-mirror saving (~600 lines).
4. **Pick `[0,5]` as canonical FD-boundary parametrisation**; delete `FDBoundary.lean` and `FDBoundaryReparametrization.lean` (~600 lines).
5. **Delete the 6 stub/duplicate files**: `cotangent.lean`, `test.lean`, `ForMathlib_SlashActions.lean`, the two `ForMathlib_*UpperHalfPlane`/`*FunctionsBoundedAtInfty` pairs.

---

## Verification

| Check | Result |
|---|---|
| `lake build` | ✅ 8428 jobs |
| `valence_formula_textbook` axioms | `[propext, Classical.choice, Quot.sound]` |
| 8 × `hw_3_3_clean*` axioms | `[propext, Classical.choice, Quot.sound]` |
| Sorries | 10 (all in `Modularforms/`) |
| Build green throughout 187-batch `/cleanup-all` | ✅ |
