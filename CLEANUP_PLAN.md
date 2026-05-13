# ForMathlib Cleanup Plan

**Source**: findings from `/mathlib-quality:overview` (see `PROJECT_OVERVIEW.md`, 2026-05-13)
**Branch**: `feat/mathlib-prs`
**Strategy**: Phase A = structural changes (file deletion, deduplication) done manually with `lake build` after each step. Phase B = `/cleanup-all` for mathlib-style per-file cleanup on the resulting tree.

`/cleanup-all` cannot drive the structural part: it dispatches per-file style audits, not cross-file refactors. Order matters — running `/cleanup-all` first would clean 5000+ lines of soon-to-be-deleted code.

---

## Phase A — Structural cleanup (manual, ~2 sessions)

Each step is one commit. After each step: `lake build LeanModularForms` must pass, axioms must remain clean.

**Status (2026-05-13 — Phase A fully complete)**: A1, A2, A3, A4, A5, A6, A7, A8, A9 all done.

* 17 ForMathlib files deleted (8 commented-out + 4 orphans + 5 duplicates)
* 14 dead private declarations removed
* 1 file (`HigherOrderCancel.lean`) deduped via import + open, 833 lines saved
* **Total ≈ 6,714 lines removed**
* **ForMathlib: 183 → 166 files**, ~88k → ~81.8k lines
* All `lake build`s green throughout
* Headline theorems verified axiom-clean after each major change:
  - `hw_3_3_clean_full_mero` (most general HW3.3): `[propext, Classical.choice, Quot.sound]`
  - `hw_3_3_clean_multi`, `hw_3_3_clean`, `hw_3_3_clean_truly_full`: same
  - `valence_formula_textbook` (ValenceFormulaFinal): same

**A2 notes**: Phase 4's verdict was inverted — `FlatnessConditions.lean` (8 importers, the modern PwC1Immersion variant) is canonical; `Residue/Flatness.lean` (1 importer with no direct name uses) is legacy. Deleted `Residue/Flatness.lean` (467 lines) instead. The single importer `GeneralizedTheoremBase.lean` had a dead transitive import; just removed it.

**A6 notes**: The two files declare 20 byte-equivalent theorems but in DIFFERENT namespaces (HigherOrderCancel at root, HigherOrderAsymptotics in `HungerbuhlerWasem`), so they were technically distinct decls. Made HigherOrderCancel `import` HigherOrderAsymptotics and `open HungerbuhlerWasem`, then removed the 20 duplicates. The 5 remaining unique theorems in HigherOrderCancel resolve their references via the new `open`.

### A1. Delete fully-commented-out files (~1951 lines, zero risk)

Files whose entire body is `/- ... -/`-wrapped:

```
LeanModularForms/ForMathlib/hassumunifon.lean             # 1023 lines
LeanModularForms/ForMathlib/Bounds.lean                   #  340
LeanModularForms/ForMathlib/QExpansion.lean               #  264
LeanModularForms/ForMathlib/Petersson.lean                #  136
LeanModularForms/ForMathlib/IsBoundedAtImInfty.lean       #   78
LeanModularForms/ForMathlib/LevelOne.lean                 #   55
LeanModularForms/ForMathlib/Identities.lean               #   40
LeanModularForms/ForMathlib/CongruenceSubgroupsCopy.lean  #   15 (placeholder stub)
```

**Procedure**:
1. For each file, confirm body is fully commented: `grep -E "^[^-/]" <file>` should return only header/imports/the closing `-/`.
2. `git rm <file>`.
3. Check if anything `imports` the file: `grep -rE "^import LeanModularForms.ForMathlib.<basename>$" LeanModularForms/`. Update or remove dead imports.
4. `lake build` → must pass.

**Estimated time**: 30 minutes (one commit per ~3 files).

### A2. Delete duplicate `FlatnessConditions.lean` (~441 lines)

`FlatnessConditions.lean` and `GeneralizedResidueTheory/Residue/Flatness.lean` share 17 byte-equal declarations modulo the curve type (`PwC1Immersion x y` vs `PiecewiseC1Immersion`).

**Procedure**:
1. Identify the 9 `FlatnessConditions.lean` importers (reverse-imports.txt centrality #3, 9 importers).
2. For each importer: replace `import ...FlatnessConditions` with `import ...GeneralizedResidueTheory.Residue.Flatness`.
3. Where the curve type matters, add a thin bridge lemma:
   ```
   theorem FlatnessConditions.IsFlatOfOrder_iff_GRT
     {γ : PwC1Immersion x y} ... : IsFlatOfOrder γ ↔ IsFlatOfOrder γ.toPiecewiseC1Immersion
   ```
   (only if the bridge is needed; many usages may pass through as-is).
4. `git rm LeanModularForms/ForMathlib/FlatnessConditions.lean`.
5. `lake build` → must pass.

**Risk**: medium — 9 importers, type-bridging may be needed.

### A3. Delete `HW33SectorEven.lean` (~558 lines)

Differs from `HungerbuhlerWasem/SectorCancellation.lean` only in the `namespace` declaration.

**Procedure**:
1. Identify importers of `HW33SectorEven` (Phase 4 found 2: `HW33Closed.lean`, `HW33LaurentPolarPart.lean`).
2. For each importer: replace `import ...HW33SectorEven` with `import ...HungerbuhlerWasem.SectorCancellation` and open the `HungerbuhlerWasem` namespace where needed.
3. `git rm LeanModularForms/ForMathlib/HW33SectorEven.lean`.
4. `lake build` → must pass.

**Risk**: low — minimal name-resolution work.

### A4. Delete `HW33LaurentPolarPart.lean` (~519 lines)

Strict subset of `HungerbuhlerWasem/LaurentExtraction.lean`.

**Procedure**:
1. Identify importers (`HW33LaurentSimple`, `HW33PVSing`, `HW33Tight`).
2. Replace imports with `HungerbuhlerWasem.LaurentExtraction`.
3. Open the right namespace where consumers use `LeanModularForms.…` qualifiers.
4. `git rm`.
5. `lake build` → must pass.

**Risk**: low-medium — 3 importers in HW33 stack.

### A5. Delete `HW33Bridge.lean` (~305 lines)

10+ theorems duplicate `HungerbuhlerWasem/ExitTimeExcision.lean`.

**Procedure**:
1. Identify importers (`HW33Final` uses it).
2. Replace imports with `HungerbuhlerWasem.ExitTimeExcision`.
3. `git rm`.
4. `lake build` → must pass.

**Risk**: low.

### A6. Dedupe `HigherOrderCancel.lean` ↔ `HungerbuhlerWasem/HigherOrderAsymptotics.lean` (~300 lines)

17 theorems verbatim in both files. The lower-level file (`HigherOrderAsymptotics`) should own them.

**Procedure**:
1. Move the 17 shared theorems out of `HigherOrderCancel.lean` (they already exist in `HigherOrderAsymptotics`).
2. In `HigherOrderCancel.lean`, add `import HungerbuhlerWasem.HigherOrderAsymptotics` and add `export HungerbuhlerWasem (...)` for the 17 names (if downstream uses `LeanModularForms.…` qualifiers).
3. `lake build` → must pass.

**Risk**: medium — both files are heavily used (HigherOrderCancel: 1515 lines, central to HW33 stack).

### A7. Delete orphan files with real content (~1135 lines)

```
LeanModularForms/ForMathlib/WindingHomotopy.lean        # 266 lines, superseded by GRT.Homotopy.*
LeanModularForms/ForMathlib/ResidueSideProof.lean       # 454 lines, covered by ValenceFormulaBridged
LeanModularForms/ForMathlib/Cycles.lean                 # 284 lines, orphan ContourCycle API
LeanModularForms/ForMathlib/HorizontalContribution.lean # 131 lines, orphan seg5 contribution
```

**Procedure**:
1. For each: `grep -rE "^import LeanModularForms.ForMathlib.<basename>$" LeanModularForms/` to confirm zero importers.
2. `git rm`.
3. `lake build` → must pass (should be no-op since no importers).

**Risk**: low.

### A8. Remove 24 dead private declarations

Mechanical removal — each declaration listed in `PROJECT_OVERVIEW.md` § Tier 3.

**Procedure**: one PR per file containing dead decls. Build check after each.

**Risk**: low — definition of "dead" is "private + unused in file".

### A9. Dedupe `HungerbuhlerWasem.lean` ↔ `HW33HigherOrderAvoidance.lean` (~150 lines)

`HungerbuhlerWasem.lean` redeclares `PolarPartDecomposition`, `higherOrderPart`, `simplePolePart`, `polarPart_eq_simplePole_add_higherOrder`, and 2 `contourIntegral_higherOrder*_eq_zero_of_avoids` theorems that live in `HW33HigherOrderAvoidance.lean`.

**Procedure**:
1. Have `HungerbuhlerWasem.lean` `import HW33HigherOrderAvoidance` and re-export rather than re-declare.
2. `lake build` → must pass.

**Risk**: medium — `HungerbuhlerWasem.lean` is the top-level API entry; downstream callers expect declarations there. Use `export` for namespace stability.

---

## Phase B — Per-file style cleanup (`/cleanup-all`)

After Phase A, the file count drops from 183 to ~170, and ~5000 lines of duplicate / inert code are gone. Now run mathlib-style per-file cleanup.

### B1. Run `/cleanup-all LeanModularForms/ForMathlib`

This orchestrates one cleanup agent per file. Each agent runs the 15-item style audit (header, simp squeezing, line packing, `by` placement, format, line packing, comments, docstrings, visibility, structure, mathlib API).

Expected outputs per file:
- Mechanical replacements: `show → change`, `λ → fun`, `$ → <|`
- Squeeze bare `simp`, unsqueeze terminal `simp only`
- `erw → rw`, `omega → lia`, `continuity → fun_prop`, `measurability → fun_prop`
- Remove `set_option maxHeartbeats` (4 files affected)
- Apply golf rules (`by exact e → e`, `rw [h]; exact e → rwa [h]`, `simp [...]; exact h → simpa [...] using h`, etc.)
- Promote `_uncrossed`/`_empty`/`_zero_fun` lemmas to `@[simp]` where canonical

### B2. Add `@[fun_prop]` annotation pass (separate from /cleanup-all, mechanical)

The 14 most-impactful `Continuous`/`Differentiable`/`MeromorphicAt` lemmas identified in Phase 3:
- `PiecewiseC1Path.continuous`, `PwC1Immersion.continuous`, `ClosedPwC1Curve.continuous`
- `principalPartSum_differentiableOn`, `principalPartSum_analyticAt`, `principalPartSum_meromorphicAt`
- `laurentPolarPartAt_differentiableAt`, `laurentHigherOrderPolar_differentiableAt`
- `laurentHolomorphicRemainder_differentiableOn`
- `PolarPartDecomposition.analyticRemainder_diff`
- `HasSimplePoleAt.meromorphicAt`
- `cpvIntegrandOn_diff_intervalIntegrable`, `cpvIntegrandOn_polarPart_intervalIntegrable`

### B3. Add `@[ext]` to bundled structures

Add `attribute [ext]` (or rebuild with `@[ext] structure`) for:
- `PolarPartDecomposition`
- `SingleCrossingData`
- `PerPoleCrossData`, `MultiPoleCrossData`
- `AsymmetricSingleCrossingData`, `DerivedAsymmetricCutoffs`
- `ClosedPwC1Curve`, `ClosedPwC1Immersion`
- `PiecewiseC1Path`, `PwC1Immersion`

Verify with `#check @PolarPartDecomposition.ext` etc.

---

## Phase C — Future structural refactors (out of scope for this plan, but noted)

Tracked items not in Phase A/B:
- Collapse `PiecewiseC1Curve`/`PiecewiseC1Immersion` onto `PiecewiseC1Path` (~960 lines, breaks 14 importers)
- Delete `cauchyPV`/`cauchyPVOn`/`cauchyPrincipalValue'` (`limUnder`-defined)
- Replace `residueSimplePole` + `HasSimplePoleAt` + `poleOrderAt` with `meromorphicTrailingCoeffAt` + `MeromorphicAt` + `meromorphicOrderAt`
- Parametrize 10 `_at_i` / `_at_rho` / `_at_rho_plus_one` triples on `(P : EllipticPoint)`
- Parametrize `Seg1/Seg4/ArcGeneric FTCProvider` triple on `segIdx : Fin 5`
- Move PR-ready shims to upstream mathlib PRs (7 files)

These need standalone planning/PR work; defer until Phase A+B settle.

---

## Suggested execution order

1. Start with **A1** (commented-out files): mechanical, immediate ~1951-line win, zero risk.
2. **A7** (orphan files): zero-risk, ~1135 lines.
3. **A8** (dead privates): file-by-file, mechanical, ~24 declarations.
4. **A3** (HW33SectorEven): low-risk, ~558 lines, mostly import edits.
5. **A5** (HW33Bridge): low-risk, ~305 lines.
6. **A4** (HW33LaurentPolarPart): low-medium risk, ~519 lines.
7. **A9** (HungerbuhlerWasem dedupe): medium risk, ~150 lines.
8. **A6** (HigherOrderCancel ↔ Asymptotics): medium risk, ~300 lines.
9. **A2** (FlatnessConditions): medium risk, ~441 lines.
10. After all of A: **B1** (`/cleanup-all`).
11. After B1: **B2** (fun_prop annotations) + **B3** (ext annotations).

**Total Phase A line reduction**: ~5,335 lines (1951 + 441 + 558 + 519 + 305 + 300 + 1135 + 150 + 24 decls × ~5 lines = ~5,479).

Each step gets its own commit so we can revert cleanly.

---

## Build / verification protocol per step

```bash
# Before each step
git status                                       # confirm clean working tree
lake build LeanModularForms 2>&1 | tail -3       # confirm green baseline

# Make change

# After
lake build LeanModularForms 2>&1 | tail -10      # must be ✔
grep -rE "(sorry|sorryAx)" LeanModularForms/ForMathlib | grep -v "//" | grep -v "/-"   # must be empty

# Commit
git add -A
git commit -m "..."
```
