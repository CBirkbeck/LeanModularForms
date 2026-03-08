# Separate GeneralizedResidueTheory from ValenceFormula

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Move general complex analysis results (curves, PV, winding numbers, residue theory, homotopy, dyadic convergence) into `LeanModularForms/GeneralizedResidueTheory/`, keeping valence-formula-specific results in `LeanModularForms/ValenceFormula/`.

**Architecture:** 17 files move as-is via `git mv`. One file (`OnCurvePV/Basic.lean`) is split: general declarations extracted to new location, FD-specific declarations stay. All import paths updated from `LeanModularForms.ValenceFormula.*` to `LeanModularForms.GeneralizedResidueTheory.*` where appropriate. No namespace changes needed (files use `open` only, no module-path namespaces). No lakefile changes needed (`lean_lib` recurses automatically).

**Tech Stack:** Lean 4, git

---

### Task 1: Create directory structure

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/` (and subdirectories)

**Step 1: Create directories**

```bash
mkdir -p LeanModularForms/GeneralizedResidueTheory/Homotopy
mkdir -p LeanModularForms/GeneralizedResidueTheory/PVInfrastructure
mkdir -p LeanModularForms/GeneralizedResidueTheory/Residue
mkdir -p LeanModularForms/GeneralizedResidueTheory/OnCurvePV
```

**Step 2: Commit**

```bash
# No commit needed — empty directories aren't tracked by git.
# Files will be committed after the moves.
```

---

### Task 2: Move core files with `git mv`

**Files to move (17 files):**

**Step 1: Move root-level general files**

```bash
git mv LeanModularForms/ValenceFormula/Basic.lean LeanModularForms/GeneralizedResidueTheory/Basic.lean
git mv LeanModularForms/ValenceFormula/PrincipalValue.lean LeanModularForms/GeneralizedResidueTheory/PrincipalValue.lean
git mv LeanModularForms/ValenceFormula/CauchyPrimitive.lean LeanModularForms/GeneralizedResidueTheory/CauchyPrimitive.lean
git mv LeanModularForms/ValenceFormula/WindingNumber.lean LeanModularForms/GeneralizedResidueTheory/WindingNumber.lean
git mv LeanModularForms/ValenceFormula/Residue.lean LeanModularForms/GeneralizedResidueTheory/Residue.lean
```

**Step 2: Move Homotopy/ files**

```bash
git mv LeanModularForms/ValenceFormula/Homotopy/ParametricDiff.lean LeanModularForms/GeneralizedResidueTheory/Homotopy/ParametricDiff.lean
git mv LeanModularForms/ValenceFormula/Homotopy/Integrality.lean LeanModularForms/GeneralizedResidueTheory/Homotopy/Integrality.lean
git mv LeanModularForms/ValenceFormula/Homotopy/Invariance.lean LeanModularForms/GeneralizedResidueTheory/Homotopy/Invariance.lean
git mv LeanModularForms/ValenceFormula/Homotopy/CircleParam.lean LeanModularForms/GeneralizedResidueTheory/Homotopy/CircleParam.lean
```

**Step 3: Move PVInfrastructure/ files**

```bash
git mv LeanModularForms/ValenceFormula/PVInfrastructure/GammaAnalysis.lean LeanModularForms/GeneralizedResidueTheory/PVInfrastructure/GammaAnalysis.lean
git mv LeanModularForms/ValenceFormula/PVInfrastructure/RemainderAnalysis.lean LeanModularForms/GeneralizedResidueTheory/PVInfrastructure/RemainderAnalysis.lean
git mv LeanModularForms/ValenceFormula/PVInfrastructure/StepBounds.lean LeanModularForms/GeneralizedResidueTheory/PVInfrastructure/StepBounds.lean
git mv LeanModularForms/ValenceFormula/PVInfrastructure/AnnulusBounds.lean LeanModularForms/GeneralizedResidueTheory/PVInfrastructure/AnnulusBounds.lean
git mv LeanModularForms/ValenceFormula/PVInfrastructure/UniformStepBound.lean LeanModularForms/GeneralizedResidueTheory/PVInfrastructure/UniformStepBound.lean
```

**Step 4: Move Residue/ subfolder files**

```bash
git mv LeanModularForms/ValenceFormula/Residue/MeasureHelpers.lean LeanModularForms/GeneralizedResidueTheory/Residue/MeasureHelpers.lean
git mv LeanModularForms/ValenceFormula/Residue/MultipointPV.lean LeanModularForms/GeneralizedResidueTheory/Residue/MultipointPV.lean
git mv LeanModularForms/ValenceFormula/Residue/GeneralizedTheorem.lean LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean
```

**Step 5: Remove empty directories**

```bash
rmdir LeanModularForms/ValenceFormula/Homotopy 2>/dev/null || true
rmdir LeanModularForms/ValenceFormula/PVInfrastructure 2>/dev/null || true
rmdir LeanModularForms/ValenceFormula/Residue 2>/dev/null || true
```

---

### Task 3: Update imports in moved files

For each moved file, replace `LeanModularForms.ValenceFormula.` with `LeanModularForms.GeneralizedResidueTheory.` in import statements that reference OTHER moved modules. Only change imports — no other edits.

**Files with no import changes needed (Mathlib-only imports):**
- `Basic.lean` — no changes
- `CauchyPrimitive.lean` — no changes
- `Homotopy/ParametricDiff.lean` — no changes
- `PVInfrastructure/GammaAnalysis.lean` — no changes

**Files needing import updates (13 files):**

| File | Old Import | New Import |
|------|-----------|------------|
| `PrincipalValue.lean` | `.ValenceFormula.Basic` | `.GeneralizedResidueTheory.Basic` |
| `WindingNumber.lean` | `.ValenceFormula.Basic` | `.GeneralizedResidueTheory.Basic` |
| `WindingNumber.lean` | `.ValenceFormula.PrincipalValue` | `.GeneralizedResidueTheory.PrincipalValue` |
| `Residue.lean` | `.ValenceFormula.Basic` | `.GeneralizedResidueTheory.Basic` |
| `Residue.lean` | `.ValenceFormula.CauchyPrimitive` | `.GeneralizedResidueTheory.CauchyPrimitive` |
| `Residue.lean` | `.ValenceFormula.Homotopy.Invariance` | `.GeneralizedResidueTheory.Homotopy.Invariance` |
| `Homotopy/Integrality.lean` | `.ValenceFormula.Basic` | `.GeneralizedResidueTheory.Basic` |
| `Homotopy/Invariance.lean` | `.ValenceFormula.Homotopy.Integrality` | `.GeneralizedResidueTheory.Homotopy.Integrality` |
| `Homotopy/Invariance.lean` | `.ValenceFormula.Homotopy.ParametricDiff` | `.GeneralizedResidueTheory.Homotopy.ParametricDiff` |
| `Homotopy/CircleParam.lean` | `.ValenceFormula.Homotopy.Integrality` | `.GeneralizedResidueTheory.Homotopy.Integrality` |
| `Residue/MeasureHelpers.lean` | `.ValenceFormula.Basic` | `.GeneralizedResidueTheory.Basic` |
| `Residue/MultipointPV.lean` | `.ValenceFormula.Residue.MeasureHelpers` | `.GeneralizedResidueTheory.Residue.MeasureHelpers` |
| `Residue/MultipointPV.lean` | `.ValenceFormula.Residue` | `.GeneralizedResidueTheory.Residue` |
| `Residue/GeneralizedTheorem.lean` | `.ValenceFormula.Residue.MultipointPV` | `.GeneralizedResidueTheory.Residue.MultipointPV` |
| `PVInfrastructure/RemainderAnalysis.lean` | `.ValenceFormula.PVInfrastructure.GammaAnalysis` | `.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis` |
| `PVInfrastructure/StepBounds.lean` | `.ValenceFormula.PVInfrastructure.GammaAnalysis` | `.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis` |
| `PVInfrastructure/StepBounds.lean` | `.ValenceFormula.PVInfrastructure.RemainderAnalysis` | `.GeneralizedResidueTheory.PVInfrastructure.RemainderAnalysis` |
| `PVInfrastructure/AnnulusBounds.lean` | `.ValenceFormula.PVInfrastructure.GammaAnalysis` | `.GeneralizedResidueTheory.PVInfrastructure.GammaAnalysis` |
| `PVInfrastructure/AnnulusBounds.lean` | `.ValenceFormula.PVInfrastructure.RemainderAnalysis` | `.GeneralizedResidueTheory.PVInfrastructure.RemainderAnalysis` |
| `PVInfrastructure/AnnulusBounds.lean` | `.ValenceFormula.PVInfrastructure.StepBounds` | `.GeneralizedResidueTheory.PVInfrastructure.StepBounds` |
| `PVInfrastructure/UniformStepBound.lean` | `.ValenceFormula.PVInfrastructure.AnnulusBounds` | `.GeneralizedResidueTheory.PVInfrastructure.AnnulusBounds` |

**Method:** For each file, run find-and-replace on import lines:
```
s/LeanModularForms.ValenceFormula./LeanModularForms.GeneralizedResidueTheory./g
```
This is safe because ALL imports in these files reference other moved modules (verified by dependency analysis).

---

### Task 4: Split OnCurvePV/Basic.lean

**Context:** `ValenceFormula/OnCurvePV/Basic.lean` contains both general and FD-specific declarations. General declarations move to `GeneralizedResidueTheory/OnCurvePV/Basic.lean`. FD-specific declarations stay.

**Step 1: Create `GeneralizedResidueTheory/OnCurvePV/Basic.lean`**

Extract these declarations (in order) into the new file:
- `pv_limit_via_dyadic` (private, lines ~27-158)
- `measurableSet_norm_gt_of_continuousOn` (private, lines ~160-181)
- `measurableSet_norm_gt_Icc` (private, lines ~183-186)
- `aEStronglyMeasurable_pv_integrand_piecewiseC1` (private, lines ~188-253)
- `indicator_integrand_deriv_eq` (private, lines ~256-261)
- `cpv_exists_from_shifted_tendsto` (private, lines ~263-268)
- `arc_angle_injective` (public, lines ~321-349)
- `cpv_exists_on_smooth_subinterval` (public, lines ~351-367)
- `cpv_avoidance` (public, lines ~370-388)
- `cpv_concat` (public, lines ~391-412)

The new file's imports should be:
```lean
import LeanModularForms.GeneralizedResidueTheory.PVInfrastructure.UniformStepBound
```
Plus any Mathlib imports the extracted declarations need.

**Step 2: Update `ValenceFormula/OnCurvePV/Basic.lean`**

- Remove the extracted declarations
- Add import: `import LeanModularForms.GeneralizedResidueTheory.OnCurvePV.Basic`
- Update existing import: `ValenceFormula.PVInfrastructure.UniformStepBound` → `GeneralizedResidueTheory.PVInfrastructure.UniformStepBound`
- Keep imports for `Boundary.Smooth`, `WindingWeights.*` (these stay in ValenceFormula)
- Verify that FD-specific declarations still compile (they reference the general ones via the new import)

**Important:** Some private declarations in the general file are used by FD-specific ones. These must be made non-private (or the FD-specific code adjusted to not need them). Check:
- `pv_limit_via_dyadic` — used by `cpv_exists_at_rho`, `cpv_exists_at_rho_plus_one`, `cpv_exists_at_i` indirectly via `cpv_exists_on_smooth_subinterval`
- `cpv_exists_on_smooth_subinterval` is already public, so this chain works

---

### Task 5: Update imports in valence-specific files

These files remain in `ValenceFormula/` but import moved modules. Update their import paths.

| File | Old Import | New Import |
|------|-----------|------------|
| `Boundary/Basic.lean` | `.ValenceFormula.Basic` | `.GeneralizedResidueTheory.Basic` |
| `Boundary/Winding/RightEdge.lean` | `.ValenceFormula.PrincipalValue` | `.GeneralizedResidueTheory.PrincipalValue` |
| `InteriorWinding.lean` | `.ValenceFormula.Residue` | `.GeneralizedResidueTheory.Residue` |
| `InteriorWinding.lean` | `.ValenceFormula.Homotopy.Invariance` | `.GeneralizedResidueTheory.Homotopy.Invariance` |
| `PVChain/Helpers.lean` | `.ValenceFormula.Residue` | `.GeneralizedResidueTheory.Residue` |
| `PVChain/ResidueSideInfra.lean` | `.ValenceFormula.Residue.MultipointPV` | `.GeneralizedResidueTheory.Residue.MultipointPV` |
| `PVChain/ResidueSideInfra.lean` | `.ValenceFormula.Residue.GeneralizedTheorem` | `.GeneralizedResidueTheory.Residue.GeneralizedTheorem` |
| `RectHomotopy/Geometry.lean` | `.ValenceFormula.Homotopy.CircleParam` | `.GeneralizedResidueTheory.Homotopy.CircleParam` |
| `RectHomotopy/WindingProof.lean` | `.ValenceFormula.Homotopy.CircleParam` | `.GeneralizedResidueTheory.Homotopy.CircleParam` |
| `RectHomotopy/MainTheorem.lean` | `.ValenceFormula.Homotopy.CircleParam` | `.GeneralizedResidueTheory.Homotopy.CircleParam` |
| `RectHomotopy/RadialHomotopy.lean` | `.ValenceFormula.Homotopy.Invariance` | `.GeneralizedResidueTheory.Homotopy.Invariance` |
| `OnCurvePV/Basic.lean` | `.ValenceFormula.PVInfrastructure.UniformStepBound` | `.GeneralizedResidueTheory.PVInfrastructure.UniformStepBound` |

**Method:** For each file, edit only the specific import lines listed above. Do NOT blanket-replace — some files import both moved and non-moved `ValenceFormula` modules.

---

### Task 6: Build and verify

**Step 1: Run `lake build`**

```bash
lake build
```

Expected: 0 errors. All 56+ files compile successfully.

**Step 2: Verify axiom cleanliness of main theorem**

```
lean_verify valence_formula_textbook_orbit_finsum
```

Expected: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

**Step 3: Commit**

```bash
git add -A
git commit -m "refactor: separate GeneralizedResidueTheory from ValenceFormula

Move 17 general complex analysis files (curves, PV, winding numbers,
residue theory, homotopy invariance, dyadic convergence) into
LeanModularForms/GeneralizedResidueTheory/.

Split OnCurvePV/Basic.lean: general PV convergence machinery goes to
GeneralizedResidueTheory/OnCurvePV/Basic.lean, FD-specific helpers stay
in ValenceFormula/OnCurvePV/Basic.lean.

All import paths updated. No functional changes."
```

---

## File inventory

### Files moving to `GeneralizedResidueTheory/` (17 + 1 new)

| # | Source | Destination |
|---|--------|-------------|
| 1 | `ValenceFormula/Basic.lean` | `GeneralizedResidueTheory/Basic.lean` |
| 2 | `ValenceFormula/PrincipalValue.lean` | `GeneralizedResidueTheory/PrincipalValue.lean` |
| 3 | `ValenceFormula/CauchyPrimitive.lean` | `GeneralizedResidueTheory/CauchyPrimitive.lean` |
| 4 | `ValenceFormula/WindingNumber.lean` | `GeneralizedResidueTheory/WindingNumber.lean` |
| 5 | `ValenceFormula/Residue.lean` | `GeneralizedResidueTheory/Residue.lean` |
| 6 | `ValenceFormula/Homotopy/ParametricDiff.lean` | `GeneralizedResidueTheory/Homotopy/ParametricDiff.lean` |
| 7 | `ValenceFormula/Homotopy/Integrality.lean` | `GeneralizedResidueTheory/Homotopy/Integrality.lean` |
| 8 | `ValenceFormula/Homotopy/Invariance.lean` | `GeneralizedResidueTheory/Homotopy/Invariance.lean` |
| 9 | `ValenceFormula/Homotopy/CircleParam.lean` | `GeneralizedResidueTheory/Homotopy/CircleParam.lean` |
| 10 | `ValenceFormula/PVInfrastructure/GammaAnalysis.lean` | `GeneralizedResidueTheory/PVInfrastructure/GammaAnalysis.lean` |
| 11 | `ValenceFormula/PVInfrastructure/RemainderAnalysis.lean` | `GeneralizedResidueTheory/PVInfrastructure/RemainderAnalysis.lean` |
| 12 | `ValenceFormula/PVInfrastructure/StepBounds.lean` | `GeneralizedResidueTheory/PVInfrastructure/StepBounds.lean` |
| 13 | `ValenceFormula/PVInfrastructure/AnnulusBounds.lean` | `GeneralizedResidueTheory/PVInfrastructure/AnnulusBounds.lean` |
| 14 | `ValenceFormula/PVInfrastructure/UniformStepBound.lean` | `GeneralizedResidueTheory/PVInfrastructure/UniformStepBound.lean` |
| 15 | `ValenceFormula/Residue/MeasureHelpers.lean` | `GeneralizedResidueTheory/Residue/MeasureHelpers.lean` |
| 16 | `ValenceFormula/Residue/MultipointPV.lean` | `GeneralizedResidueTheory/Residue/MultipointPV.lean` |
| 17 | `ValenceFormula/Residue/GeneralizedTheorem.lean` | `GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean` |
| 18 | *(new)* | `GeneralizedResidueTheory/OnCurvePV/Basic.lean` (extracted from ValenceFormula/OnCurvePV/Basic.lean) |

### Files staying in `ValenceFormula/` with import updates (12 files)

1. `Boundary/Basic.lean`
2. `Boundary/Winding/RightEdge.lean`
3. `InteriorWinding.lean`
4. `PVChain/Helpers.lean`
5. `PVChain/ResidueSideInfra.lean`
6. `RectHomotopy/Geometry.lean`
7. `RectHomotopy/WindingProof.lean`
8. `RectHomotopy/MainTheorem.lean`
9. `RectHomotopy/RadialHomotopy.lean`
10. `OnCurvePV/Basic.lean` (also loses extracted declarations)
11. `OnCurvePV/EndpointCorner.lean` (no import changes — imports `ValenceFormula.OnCurvePV.Basic` which stays)
12. `OnCurvePV/Main.lean` (no import changes)

### Files staying in `ValenceFormula/` with NO changes (~24 files)

All other valence-specific files that don't import any moved module.
