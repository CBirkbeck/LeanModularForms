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

## Ticket A – Homotopy / Interior Winding — **COMPLETE** ✓ (Session 92)

**Owner:** Homotopy AI → Claude Opus 4.6
**Target file:** `ValenceFormula_InteriorWinding.lean`
**Imports:** `ValenceFormulaDefinitions`, `ValenceFormula_FD_Boundary`, `ValenceFormula_Rect_Homotopy`

**Canonical result (sorry-free, no `sorryAx`):**
```
theorem generalizedWindingNumber_fdBoundary_eq_neg_one
  (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
  (hp_im_pos : 0 < p.im) (hp_im : p.im < H_height) :
  generalizedWindingNumber' fdBoundary 0 5 p = -1
```

Sign is **-1** (clockwise orientation of `fdBoundary`).

**Convenience variants:**
- `generalizedWindingNumber_fdBoundary_eq_neg_one_uhp` — for `s : ℍ`
- `generalizedWindingNumber_fdBoundary_eq_neg_windingCoeff_interior` — gives `-(windingNumberCoeff' s : ℂ)`

**Proof strategy:** bridge lemmas (`fdBoundary_eq_rect`, `H_height_eq_rect`) verify
definitional equality, then forward to `RectHomotopyProof.generalizedWindingNumber_fdBoundary_eq_neg_one`.

**Axioms:** `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.

**Do-not-pursue:** Pointwise `generalizedWindingNumber' = -(effectiveWinding)` at
elliptic crossing points (i, ρ) is **not a valid goal** — PV-based `generalizedWindingNumber'`
gives 0 at crossings. The current architecture uses `effectiveWinding` decomposition
in Core/ResidueSide instead, which is correct.

**A parked:** Ticket A is fully done (Session 92). Worker is waiting for reassignment.
No further changes to InteriorWinding or Rect_Homotopy are needed.

---

## Ticket B – PV Infrastructure — CRITICAL PATH (5 dead-code sorries remain)

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

## Ticket C – Core / Residue + Modular Side — **DONE** ✓ (0 sorry)

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

---

## Ticket A2 – Remove `sorryAx` from Piecewise Homotopy Chain — **DONE** ✓

**Owner:** Claude Opus 4.6
**Detailed handoff file:** `TICKET_A2_SORRYAX_CLEANUP.md`
**Target files (strict):**
- `PiecewiseHomotopy.lean`
- `Infrastructure/PiecewiseHomotopyHelpers.lean`
- `VALENCE_AI_PROGRESS.md`

**Status: DONE (2026-02-10)**

### Result

**Signatures changed (4 total):**
1. `windingNumber_integer_of_piecewise_closed_avoiding` — added `hγ_deriv_bound_ex`, forwards to `_with_bound` (3 sorries eliminated)
2. `windingNumber_continuousOn_param_piecewise` (helpers) — added `hH_deriv_bound_ex`, forwards to `_with_bound` (1 sorry eliminated)
3. `windingNumber_continuous_in_param_piecewise` — added `hH_deriv_bound_ex`, forwards to helpers
4. `windingNumber_eq_of_piecewise_homotopic` — passes `⟨M, fun t ht => hM_bound t ht s hs⟩`

**Sorry delta: -4** (3 in PiecewiseHomotopy.lean, 1 in PiecewiseHomotopyHelpers.lean)

**Axiom results (no sorryAx):**
- `windingNumber_eq_of_piecewise_homotopic` → `[propext, Classical.choice, Quot.sound]`
- `generalizedWindingNumber_fdBoundary_eq_neg_one` → `[propext, Classical.choice, Quot.sound]`

**Build results:** both `lake build` targets pass (2832 and 2873 jobs respectively).

---

## Ticket D + D2 – Final Public API — **DONE** ✓

**Owner:** Claude Opus 4.6
**Target files:**
- `ValenceFormula_Final.lean` — canonical public API (imports legacy `ValenceFormula.lean`)
- `ValenceFormula_Final_WithData.lean` — internal `_with_data` wrappers (imports Core)
- `ValenceFormula_Final_Discharge.lean` — ℚ bridge lemmas (imports Core)

**Status: DONE (2026-02-10)** — canonical signatures exposed, 0 local sorry in all files.

### Final Public Signatures (in `ValenceFormula_Final.lean`)

```lean
theorem valenceFormula {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' f p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℚ) +
    ∑ p ∈ S, windingNumberCoeff' p * (orderOfVanishingAt' f p : ℚ) = k / 12
-- forwards to valenceFormula' in ValenceFormula.lean

theorem valenceFormula_classical {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟' ∧ p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho')
    (hS_complete : ∀ p, p ∈ 𝒟' → p ≠ ellipticPoint_i' → p ≠ ellipticPoint_rho' →
                    orderOfVanishingAt' f p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℚ) +
    (1/2 : ℚ) * orderOfVanishingAt' f ellipticPoint_i' +
    (1/3 : ℚ) * orderOfVanishingAt' f ellipticPoint_rho' +
    ∑ p ∈ S, (orderOfVanishingAt' f p : ℚ) = k / 12
-- forwards to valenceFormula_classical' in ValenceFormula.lean
```

**Inputs**: `k f hf S hS hS_complete` only — **no** `zeros/hzeros/hint/hcusp_nonvan`.

### Build Output

```
$ lake build ...ValenceFormula_Final → Build completed successfully (2953 jobs).
$ lake build ...ValenceFormula_Final_WithData → Build completed successfully (2973 jobs).
$ lake build ...ValenceFormula_Final_Discharge → Build completed successfully (2973 jobs).
```

### Axiom Output

```
#print axioms valenceFormula: [propext, sorryAx, Classical.choice, Quot.sound]
#print axioms valenceFormula_classical: [propext, sorryAx, Classical.choice, Quot.sound]
```

`sorryAx` traces to upstream legacy `ValenceFormula.lean` sorries (infrastructure proofs).

---

## Ticket H-WITHDATA-RADIUS-SYNC — Larger-radius WithData + windingCoeff — **DONE** ✓

**Owner:** Claude Opus 4.6 (Worker H)
**Target files:**
- `ValenceFormula_Final_WithData.lean` — ℂ-typed `_of_larger_radius` wrappers
- `ValenceFormula_Final_Discharge.lean` — ℚ-typed `windingCoeff_of_larger_radius_rat`

**Status: DONE (2026-02-11)**

### New Signatures

```lean
-- WithData (ℂ-typed, forward to Core)
theorem valenceFormula_with_data_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset ℍ) (hzeros hzeros_fd hzeros_complete hint)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ closedBall(0,r), q ≠ 0 → cuspFunction 1 f q ≠ 0) :
    ∑ s ∈ zeros, ew(s) * ord(s) = k/12 - ord_∞

theorem valenceFormula_classical_with_data_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset ℍ) (hzeros hzeros_fd hzeros_complete hint)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ closedBall(0,r), q ≠ 0 → cuspFunction 1 f q ≠ 0) :
    ord_∞ + ½·ord_i + ⅓·ord_ρ + Σ_interior ord = k/12

-- Discharge (ℚ-typed, requires hclass)
theorem valence_formula_windingCoeff_of_larger_radius_rat (hf : f ≠ 0)
    (zeros : Finset ℍ) (hzeros hzeros_fd hzeros_complete)
    (hclass : ∀ s ∈ zeros, interior ∨ i ∨ ρ)
    (hint) {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ closedBall(0,r), q ≠ 0 → cuspFunction 1 f q ≠ 0) :
    ord_∞ + Σ wc(s)·ord(s) = k/12
```

### Axioms (all clean)

```
valenceFormula_with_data_of_larger_radius: [propext, Classical.choice, Quot.sound]
valenceFormula_classical_with_data_of_larger_radius: [propext, Classical.choice, Quot.sound]
valence_formula_windingCoeff_of_larger_radius_rat: [propext, Classical.choice, Quot.sound]
```

---

## Worker H — Support Track Tickets (all DONE) ✓

All Worker-H tickets are conflict-free micro-lemma additions. No existing
signatures modified. All theorems: 0 sorry, `[propext, Classical.choice, Quot.sound]`.

### H-PARAM-PREP (Session 84) — **DONE** ✓
- **Files:** `ValenceFormula_CuspHeight.lean`, `ValenceFormula_ModularSide.lean`
- **Added:** `cusp_nonvanishing_closedBall_mono`, `cusp_nonvanishing_height_mono`,
  `exists_height_cusp_nonvanishing_above`, `modular_side_of_larger_radius`

### H-PARAM-SYNC (Session 85) — **DONE** ✓
- **Files:** `ValenceFormula_Final_Discharge.lean`
- **Changed:** Removed `hclass`, `h_winding`, `h_integral_residue` from
  `valence_formula_base_identity_rat`, `valence_formula_rearranged_rat`.
  Added `valence_formula_classical_form_rat` (no `hclass`).
  Kept `hclass` in bridge lemmas (algebraically required).

### H-RADIUS-BRIDGE (Session 86) — **DONE** ✓
- **Files:** `ValenceFormula_Core.lean`, `ValenceFormula_Final_Discharge.lean`
- **Added:** `valence_formula_base_identity_of_larger_radius`,
  `valence_formula_classical_form_of_larger_radius` (ℂ);
  `valence_formula_base_identity_of_larger_radius_rat`,
  `valence_formula_classical_form_of_larger_radius_rat` (ℚ)

### H-WITHDATA-RADIUS-SYNC (Session 87) — **DONE** ✓
- **Files:** `ValenceFormula_Final_WithData.lean`, `ValenceFormula_Final_Discharge.lean`
- **Added:** `valenceFormula_with_data_of_larger_radius`,
  `valenceFormula_classical_with_data_of_larger_radius` (ℂ);
  `valence_formula_windingCoeff_of_larger_radius_rat` (ℚ, requires `hclass`)
