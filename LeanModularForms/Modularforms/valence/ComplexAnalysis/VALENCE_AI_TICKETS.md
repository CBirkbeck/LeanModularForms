# Valence Formula – AI Worker Tickets (Post‑Split)

These tickets assume the **split file layout** from `VALENCE_SPLIT_PLAN.md`.
Each worker should **only** edit their target file(s) and import earlier modules.
When reporting back, **always include the main blockers you still face**.

---

## Migration Order (do this once before any ticket work)

Follow this exact order to avoid forward‑reference/import issues. Do **not** delete the old
`ValenceFormula_*_Work.lean` files until the split files compile.

1) **Create split skeletons** (empty files if they don’t exist yet):
   - `ValenceFormula_FD_Boundary.lean`
   - `ValenceFormula_InteriorWinding.lean`
   - `ValenceFormula_EllipticContrib.lean`
   - `ValenceFormula_PV.lean`
   - `ValenceFormula_ResidueSide.lean`
   - `ValenceFormula_ModularSide.lean`
   - `ValenceFormula_Core.lean`
   - `ValenceFormula_Final.lean` (or make `ValenceFormula.lean` an import‑only file)

2) **Move definitions first** (no proofs yet):
   - From `ValenceFormulaDefinitions.lean`: keep all defs there; add missing constants
     (e.g., `ellipticPoint_rho_plus_one`) so later files can import them.
   - From `ValenceFormula.lean` / `ValenceFormula_Rect_Homotopy.lean`:
     move the *FD boundary curve* and *segment definitions* into
     `ValenceFormula_FD_Boundary.lean`.

3) **Migrate Homotopy proof** (Rect‑homotopy):
   - Copy everything from `ValenceFormula_Rect_Homotopy.lean` into
     `ValenceFormula_InteriorWinding.lean`.
   - Fix imports to use `ValenceFormulaDefinitions` + `ValenceFormula_FD_Boundary`.
   - Leave any sorries intact; the Homotopy AI will finish them.

4) **Migrate Elliptic contributions**:
   - Move `windingContribution_at_i_eq_half` and
     `windingContribution_rho_total_eq_third` (and local angle lemmas)
     into `ValenceFormula_EllipticContrib.lean`.

5) **Migrate PV infrastructure**:
   - Move PV lemmas from `ValenceFormula_PV_Work.lean` into
     `ValenceFormula_PV.lean` (keep sorries as‑is).
   - Update imports to pull FD boundary + definitions only.

6) **Migrate core assembly**:
   - Move `effectiveWinding`, `pv_equals_residue_sum`,
     `effectiveWinding_eq_windingNumberCoeff'` into
     `ValenceFormula_ResidueSide.lean`.
   - Move `pv_equals_modular_total` into `ValenceFormula_ModularSide.lean`.
   - Move `valence_formula_base_identity` into `ValenceFormula_Core.lean`.

7) **Final wrapper**:
   - Make `ValenceFormula_Final.lean` import Core and restate the main theorems.
   - Optionally replace `ValenceFormula.lean` with a thin import of `ValenceFormula_Final`.

**After step 7**, run a compile to ensure the split files build. Then start the tickets.

---

## Recommended Execution Order + Parallelization

**Phase 0 (must be done once):** Migration Order above.  

**Phase 1 (parallel):**
- Ticket A (Homotopy / Interior Winding)
- Ticket B (PV Infrastructure)

These can run **in parallel** because they work in different files and do not
depend on each other.

**Phase 2 (partial parallel):**
- Ticket C (Core) can start on **boundary classification lemmas** (B1–B3) and
  effectiveWinding logic **while** A/B are running, but it cannot finish
  `pv_equals_residue_sum` until A and B are done.

**Phase 3 (sequential):**
- After A and B are complete, finish Ticket C fully.
- Then do Integration / Final Assembly (import‑only file).

**Progress protocol:** every AI **must** update `VALENCE_AI_PROGRESS.md`
before handing off, including blockers.

---

## Ticket A – Homotopy / Interior Winding

**Owner:** Homotopy AI  
**Target file:** `ValenceFormula_InteriorWinding.lean`  
**Imports (must be present):**  
`ValenceFormulaDefinitions`, `ValenceFormula_FD_Boundary`, `WindingNumberInterior`, `PiecewiseHomotopy`

**Goal:** prove
```
theorem generalizedWindingNumber_fdBoundary_eq_one
  (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2) (hp_im : p.im < H_height) :
  generalizedWindingNumber' fdBoundary 0 5 p = 1
```

**Detailed plan:** follow `VALENCE_AI_PLAN_HOMOTOPY.md` exactly.  
Do not attempt large proofs; break into helper lemmas first.

**Deliverables:**
- All sorries removed in `ValenceFormula_InteriorWinding.lean`.
- A short summary of new helper lemmas introduced.

**Reporting requirement:** include completed lemmas + **main blockers**.

---

## Ticket B – PV Infrastructure

**Owner:** PV AI  
**Target file:** `ValenceFormula_PV.lean`  
**Imports (must be present):**  
`ValenceFormulaDefinitions`, `ValenceFormula_FD_Boundary`, `PrincipalValue`, `ResidueTheory`

**Goal:** prove
```
lemma pv_integral_eq_modular_transformation ...
```
and all prerequisite PV lemmas (Cauchy criteria, decomposition, etc.).

**Detailed plan:** follow `VALENCE_AI_PLAN_PV.md` exactly.  
Do not rewrite math; assemble from A1–A5 helper lemmas.

**Deliverables:**
- All `⚡ TARGET` sorries removed in `ValenceFormula_PV.lean`.
- A short list of helper lemmas added.

**Reporting requirement:** include completed lemmas + **main blockers**.

---

## Ticket C – Core / Residue + Modular Side

**Owner:** Core AI  
**Target files:**  
`ValenceFormula_ResidueSide.lean`, `ValenceFormula_ModularSide.lean`, `ValenceFormula_Core.lean`

**Imports (must be present):**
- Residue side: `ValenceFormulaDefinitions`, `ValenceFormula_FD_Boundary`,
  `ValenceFormula_InteriorWinding`, `ValenceFormula_EllipticContrib`, `ResidueTheory`
- Modular side: `ValenceFormulaDefinitions`, `ValenceFormula_FD_Boundary`, `ValenceFormula_PV`
- Core: `ValenceFormula_ResidueSide`, `ValenceFormula_ModularSide`

**Goals:**
1) **Residue side:** finish  
   `effectiveWinding_eq_windingNumberCoeff'`, `pv_equals_residue_sum`.
2) **Modular side:** finish  
   `pv_equals_modular_total` (wrapper around PV lemma).
3) **Core identity:** finish  
   `valence_formula_base_identity` (likely already structured).

**Detailed plan:** follow `VALENCE_AI_PLAN_CORE.md` exactly.  
Focus on boundary classification lemmas B1–B3 and effectiveWinding logic.

**Deliverables:**
- All core sorries removed in the three target files.
- Any new helper lemmas (with names).

**Reporting requirement:** include completed lemmas + **main blockers**.
