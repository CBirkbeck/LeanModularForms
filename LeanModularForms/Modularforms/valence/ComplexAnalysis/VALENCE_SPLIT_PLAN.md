# Valence Formula File Split Plan

**Goal:** de‑duplicate the current `ValenceFormula*.lean` files and split the proof into clean, ordered modules: **Definitions → Geometry → Homotopy (interior winding) → Angle contributions (elliptic points) → PV infrastructure → Residue side → Modular side → Core identity → Final valence formula**.

This plan is designed so that each file is self‑contained, imports only earlier files, and can be worked on independently by agents. It also fixes the long‑standing **PV vs angle** mismatch by keeping **angle‑based contributions** for elliptic points and **PV winding** for interior points only.

---

## 0) Current Files & Key Duplication Sources

You currently have:
- `ValenceFormula.lean` (main, large, contains everything)
- `ValenceFormula_Core_Work.lean` (core assembly copy)
- `ValenceFormula_PV_Work.lean` (PV infrastructure copy)
- `ValenceFormula_Homotopy_Work.lean` (older homotopy approach)
- `ValenceFormula_Rect_Homotopy.lean` (new chord/rectangle homotopy)
- `ValenceFormulaDefinitions.lean` (already the right “definitions only” file)
- `polygonToCircleRadial.lean` (stub, duplicates Rect_Homotopy)

**Duplication hotspots:**
- Fundamental domain + elliptic points appear in multiple files.
- FD boundary curve & its segments appear in both `ValenceFormula.lean` and `ValenceFormula_Rect_Homotopy.lean`.
- “PV vs angle” logic is inconsistently encoded in several places.

We should keep the work files for now as scratch, but **do not import them** in the final pipeline. Instead, move cleaned proofs into the new split modules below.

---

## 1) Target Module Graph (Linear Import Chain)

**A → B → C → D → E → F → G → H → I**

### **A. `ValenceFormulaDefinitions.lean` (already exists)**
**Contents:**
- `fundamentalDomain` (𝒟′), elliptic points `i, ρ, ρ+1`
- Orbifold coefficients
- `orderOfVanishingAt'` definition

**Imports:** Mathlib modular form basics only.

**Notes:**
- Add `ellipticPoint_rho_plus_one` here (currently defined in Core Work).
- Keep all basic *numerical facts* about ρ, ρ′, i here (norms etc.).

---

### **B. `ValenceFormula_FD_Boundary.lean` (new)**
**Purpose:** canonical definitions of the fundamental domain boundary curve and segments.

**Contents to move here (from `ValenceFormula.lean` + `ValenceFormula_Rect_Homotopy.lean`):**
- boundary parameterization (fdBoundary curve) and partition `{1,2,3,4}`
- segment definitions (verticals, arcs, chord versions if needed)
- `fdBoundary` closedness and continuity
- key geometric lemmas: points on arc, vertical edges, etc.

**Imports:** `ValenceFormulaDefinitions`, `Basic`, `PiecewiseHomotopy`.

**Notes:**
- Remove duplicate local definitions of `rho`, `rho'`, `i_point` in Rect_Homotopy; use `ValenceFormulaDefinitions` instead.
- Export a `PiecewiseC1Curve` or `PiecewiseC1Immersion` instance if needed by PV/angle lemmas.

---

### **C. `ValenceFormula_InteriorWinding.lean` (new)**
**Purpose:** prove **interior** winding = 1 for FD boundary, using **Rect/Chord homotopy**.

**Contents to move here:**
- Everything from `ValenceFormula_Rect_Homotopy.lean` (once cleaned)
- Main theorem: `generalizedWindingNumber_interior_eq_one_complex` (or the fdBoundary version)

**Imports:** B + `WindingNumberInterior` + `PiecewiseHomotopy`.

**Notes:**
- Retire the older angle‑lift approach in `ValenceFormula_Homotopy_Work.lean`.
- Remove the stub `polygonToCircleRadial.lean` (or merge its final lemmas here).

---

### **D. `ValenceFormula_EllipticContrib.lean` (new)**
**Purpose:** compute **angle‑based** winding contributions at **i, ρ, ρ′**.

**Contents to move here (from `ValenceFormula.lean` / Core Work):**
- `windingContribution_at_i_eq_half`
- `windingContribution_rho_total_eq_third` (ρ + ρ′)
- local crossing angle lemmas using `windingNumberWithAngles'`

**Imports:** B + `WindingNumber`.

**Important:**
- **Do NOT use PV‐based generalizedWindingNumber' at crossings.**
- These are angle sums from `windingNumberWithAngles'`.

---

### **E. `ValenceFormula_PV.lean` (new)**
**Purpose:** all PV existence + modular side integral computations.

**Contents to move here (from `ValenceFormula_PV_Work.lean`):**
- `cauchy_cutoff_of_linear_approx`
- `immersion_crossing_cauchy`
- `pv_integral_exists_f'_over_f`
- `pv_integral_decompose_segments`
- `pv_integral_vertical_cancel`
- `arc_contribution_is_k_div_12`
- `pv_integral_eq_modular_transformation`
- `cusp_contribution` (q‑expansion) if this is the chosen place

**Imports:** A + B + `PrincipalValue` + `ResidueTheory` + `WindingNumber`.

**Notes:**
- All PV work lives here. The rest of the proof assumes these lemmas.

---

### **F. `ValenceFormula_ResidueSide.lean` (new)**
**Purpose:** assemble the **residue side** of the valence formula.

**Contents:**
- `effectiveWinding` (or equivalent) definition: 
  - interior → generalizedWindingNumber' 
  - elliptic points → angle‑based coefficients (1/2, 1/6, 1/6)
- Lemma: `effectiveWinding_eq_windingNumberCoeff'` (match orbifold coefficients)
- `pv_equals_residue_sum` (generalized residue theorem applied to FD boundary)

**Imports:** A + B + C + D + `ResidueTheory` + `WindingNumber`.

**Notes:**
- This is where the PV/angle split is enforced.

---

### **G. `ValenceFormula_ModularSide.lean` (new)**
**Purpose:** assemble the **modular side** (k/12 − ord∞).

**Contents:**
- `modular_side_equals_pv_integral`
- Uses `pv_integral_eq_modular_transformation` from E

**Imports:** A + B + E + modular forms basics.

---

### **H. `ValenceFormula_Core.lean` (new)**
**Purpose:** core identity
```
2πi * Σ (coeff × order) = 2πi * (k/12 − ord∞)
```

**Contents:**
- `residue_side_equals_pv_integral` from F
- `modular_side_equals_pv_integral` from G
- `valence_formula_base_identity`

**Imports:** F + G + A.

---

### **I. `ValenceFormula_Final.lean` (new)**
**Purpose:** final theorems:
- `valenceFormula`
- `valenceFormula_classical`
- corollaries

**Imports:** H + A + modular forms basics.

**Note:** This should become the new `ValenceFormula.lean` (or replace it).

---

## 2) Migration Steps (Detailed)

### Step 1: Create new files & copy code
1. Create the new files B–I listed above (empty skeletons).
2. Move definitions & lemmas (copy‑paste) into their target files.
3. Leave `ValenceFormula_*_Work.lean` files untouched (for now) so we don’t lose work.

### Step 2: Remove duplicates and fix imports
1. Remove re‑definitions of `fundamentalDomain`, `rho`, `rho'`, `i_point` etc. from:
   - `ValenceFormula_Rect_Homotopy.lean`
   - `ValenceFormula.lean`
2. Replace with imports of `ValenceFormulaDefinitions` + notations.
3. Update `open`/`notation` if needed.

### Step 3: Resolve forward‑reference problems
- Any lemma currently used before definition (e.g., `logDeriv_residue_eq_order`) should live in a **lower‑level file** that is imported earlier (ideally in `ResidueTheory` or `ValenceFormula_ResidueSide`).

### Step 4: Eliminate deprecated PV=angle attempts
- Delete or quarantine the old lemmas that try to prove
  `generalizedWindingNumber' = 1/2 or 1/3 at crossings`.
- Keep `windingNumberWithAngles'` for elliptic points only.

### Step 5: Replace main `ValenceFormula.lean`
- Once A–I compile, rename `ValenceFormula_Final.lean` to `ValenceFormula.lean`.
- Alternatively, keep `ValenceFormula.lean` and make it a short “import file”:
  ```
  import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Final
  ```

---

## 3) Known Issues & Fixes During Splitting

### Issue: `polygonToCircleRadial.lean` stub
- This file imports `ValenceFormula_Rect_Homotopy` and has a `sorry`.
- **Plan:** delete this file OR merge its contents into `ValenceFormula_InteriorWinding.lean`.

### Issue: `effectiveWinding` vs angle contributions
- Keep `effectiveWinding` in the **ResidueSide** file (F).
- Define it explicitly in terms of:
  - interior: `generalizedWindingNumber'`
  - boundary: angle contributions from D

### Issue: ρ vs ρ+1 canonical representative
- Standardize the convention in A (definitions) so **ρ+1 is explicitly named**.
- Use T‑invariance to move any ρ+1 terms to ρ in core sums if needed.

### Issue: PV infrastructure is still incomplete
- The PV file E can still have sorries while C/D/F/H compile.
- The core identity (H) should only depend on E once the PV lemmas are ready.

---

## 4) Recommended Build Order for Agents

1. **Interior homotopy agent:** work only in C (Rect/Chord homotopy)
2. **Elliptic/angles agent:** work in D (angle contributions)
3. **PV agent:** work in E (PV existence, decomposition, modular side)
4. **Residue‑side agent:** work in F (effectiveWinding, residue sum)
5. **Core assembly agent:** work in H (connect residue + modular)
6. **Final agent:** work in I (public theorems)

---

## 5) Quick Checklist for the Split

- [ ] All geometry/FD boundary definitions live in B
- [ ] All interior winding proofs live in C
- [ ] All elliptic contributions live in D
- [ ] All PV lemmas live in E
- [ ] Residue side (effectiveWinding + sum) lives in F
- [ ] Modular side lives in G
- [ ] Core identity lives in H
- [ ] Final theorem statements live in I
- [ ] `ValenceFormula.lean` becomes a thin import of I

---

## 6) Notes for AI Workers (include in task headers)

- **Do not introduce new axioms.**
- **Do not use Jordan curve theorem.**
- **Do not try to prove PV=angle at crossings.** Use `windingNumberWithAngles'`.
- When a proof is large, split into helper lemmas; aim for ≤30 lines each.
- If a lemma depends on a later file, move it earlier (no forward refs).

---

If you want, I can pre‑generate the skeleton files B–I with minimal headers and imports to speed up the split.
