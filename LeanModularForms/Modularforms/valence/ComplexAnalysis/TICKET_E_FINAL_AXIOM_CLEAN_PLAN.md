# Ticket E — Final Axiom-Clean Public API

**Goal:** Remove `sorryAx` from the public `valenceFormula` / `valenceFormula_classical`
theorems AND eliminate the extra hypotheses (`hint`, `hcusp_nonvan`) from the split chain.

**Do NOT attempt:**
- Pointwise elliptic `generalizedWindingNumber' = -(effectiveWinding)` at i or ρ.
  PV-based gWN gives 0 at crossings. This is a dead end.
- Contour indentation route. Prefer the PV/effective-winding plan already adopted
  in Core/ResidueSide.

---

## Track E1: Remove `sorryAx` from public `ValenceFormula_Final.lean`

**Current state:** `ValenceFormula_Final.lean` imports legacy `ValenceFormula.lean` and
forwards to `valenceFormula'` / `valenceFormula_classical'`. These carry `sorryAx` from
infrastructure proofs in the monolithic file.

The split-chain path (Core → Discharge → WithData) is fully axiom-clean, but
`ValenceFormula_Final.lean` does NOT yet use it.

### E1-1: Choose hypothesis treatment

**Decision required before proceeding.** Two options:

**Option A — Retain `hint` + `hcusp_nonvan` as hypotheses:**
- Fastest path. Switch import from `ValenceFormula` to split-chain `ValenceFormula_Core`.
- Public signatures keep `hint` + `hcusp_nonvan` (or use `_of_larger_radius` variants).
- Already have: `valenceFormula_with_data_of_larger_radius` (axiom-clean).
- Blocker: none (all infrastructure exists).

**Option B — Remove extra hypotheses (requires E2):**
- Cleanest API. Public signatures become `(hf : f ≠ 0) (S : Finset ℍ) (hS ...) (hS_complete ...)`.
- Requires E2 to derive `hint` and `hcusp_nonvan` internally.
- Blocker: E2 must be completed first.

### E1-2: Rewire `ValenceFormula_Final.lean` (micro-tasks)

| Task | Description | Blocker |
|------|-------------|---------|
| E1-2a | Change import: `ValenceFormula` → `ValenceFormula_Core` (or `_Discharge` / `_WithData`) | None |
| E1-2b | Replace `valenceFormula` body: forward to split-chain `valence_formula_base_identity` (Option A) or auto-derived version (Option B) | E1-1 decision |
| E1-2c | Replace `valenceFormula_classical` body: forward to `valence_formula_classical_form` | E1-1 decision |
| E1-2d | Verify: `#print axioms valenceFormula` → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`) | E1-2b, E1-2c |

### E1-3: Verify downstream

| Task | Description |
|------|-------------|
| E1-3a | `lake build ValenceFormula_Final` passes |
| E1-3b | Full `lake build` passes (7457 jobs) |
| E1-3c | No other files import `ValenceFormula.lean` directly (or if they do, they still build) |

---

### E1.9: Re-export axiom-clean theorems — DONE (via Final_AxiomClean.lean)

**E1.9 (original):** BLOCKED — import conflict prevents adding split-chain import to
`ValenceFormula_Final.lean`. Both chains define `orbifoldCoeff_at_i` etc.

**E1.9B (pivot):** DONE — Created `ValenceFormula_Final_AxiomClean.lean` as a separate
axiom-clean entrypoint. Imports only `ValenceFormula_Final_Split`. Contains 4 theorems:

| Name | Status |
|------|--------|
| `valenceFormula_axiomClean_from_S` | DONE, axiom-clean |
| `valenceFormula_classical_axiomClean_from_S` | DONE, axiom-clean |
| `valenceFormula_axiomClean_from_S_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_classical_axiomClean_from_S_of_larger_radius` | DONE, axiom-clean |

### E1.8: Larger-radius superset wrappers — DONE (Session 95)

| Name | Status |
|------|--------|
| `valenceFormula_split_from_S_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_classical_split_from_S_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_split_from_S` (refactored) | DONE, 1-line forward |
| `valenceFormula_classical_split_from_S` (refactored) | DONE, 1-line forward |

---

## Track E2: Remove `hint` and `hcusp_nonvan` from split chain

**Current state:** The split-chain `valence_formula_base_identity` requires:
- `hint : IntervalIntegrable (fun t => logDeriv(f∘ofComplex)(fdBoundary t) * deriv fdBoundary t) volume 0 5`
- `hcusp_nonvan : ∀ q ∈ closedBall(0, seg5_q_radius), q ≠ 0 → cuspFunction 1 f q ≠ 0`

These cannot be stated in the public API without exposing internal constants.
Goal: derive them from `(hf : f ≠ 0)` alone.

### E2-1: Derive `hcusp_nonvan` from `hf`

**Mathematical argument:** For a nonzero modular form f, the cuspFunction `g(q) = f(log(q)/(2πi))`
is holomorphic on a punctured disk and extends meromorphically to 0. Since f ≠ 0, g is not
identically zero. By the identity theorem, g has only finitely many zeros in any closed ball.
Choose radius r small enough to avoid all zeros except possibly q = 0.

| Micro-task | Description | Blocker |
|------------|-------------|---------|
| E2-1a | Prove `cuspFunction_meromorphicAt_zero` | Needs mathlib `MeromorphicAt` for q-expansion |
| E2-1b | Prove `cuspFunction_not_identically_zero` from `hf : f ≠ 0` | E2-1a |
| E2-1c | Prove `exists_radius_cusp_nonvanishing (hf : f ≠ 0) : ∃ r > 0, ∀ q ∈ closedBall(0,r), q ≠ 0 → cuspFunction 1 f q ≠ 0` | E2-1b |
| E2-1d | Show `seg5_q_radius ≤ r` for the radius from E2-1c (or use `_of_larger_radius` variant) | E2-1c |

**Existing infrastructure:** `ValenceFormula_CuspHeight.lean` has `cusp_nonvanishing_closedBall_mono`
and `exists_height_cusp_nonvanishing_above`. May partially address this.

### E2-2: Derive `hint` from `hf` + curve structure

**Mathematical argument:** `logDeriv(f∘ofComplex)` is meromorphic on ℍ. Since f ≠ 0 has only
finitely many zeros in the compact region bounded by fdBoundary, and fdBoundary avoids all
zeros (by choosing H large enough), the integrand is continuous on [0,5] and hence integrable.

| Micro-task | Description | Blocker |
|------------|-------------|---------|
| E2-2a | Reuse `finite_zeros_in_fdBox` from `ValenceFormula_ResidueSide.lean:1604` (DO NOT re-prove finiteness from scratch) | Exposure: `fdBox` is private — use existing public API or add thin wrapper |
| E2-2b | Prove `exists_H_fdBoundary_avoids_zeros (hf : f ≠ 0) : ∃ H, ∀ t ∈ [0,5], f(fdBoundary_H t) ≠ 0` | E2-2a |
| E2-2c | Prove `logDeriv_continuous_on_fdBoundary` from avoidance | E2-2b |
| E2-2d | Prove `logDeriv_integrable_on_fdBoundary` from continuity | E2-2c |

**Parameterized boundary:** RESOLVED. `fdBoundary_H` and `seg5_q_radius_H` are in
`ValenceFormula_FD_Boundary_Param.lean` with bridge, endpoint, closure, monotonicity,
continuity, HasDerivAt, deriv, nonvanishing derivative, and norm lemmas.

**E2.2 full-curve regularity (DONE):**
- `fdBoundary_H_continuous` — full 5-piece curve continuity via nested `Continuous.if`
- `fdBoundary_H_eq_seg{1,4,5}_H` — segment agreement lemmas
- `fdBoundary_H_height_eq` — pointwise equality at canonical height

**Existing infrastructure:**
- `ValenceFormula_CuspHeight.lean` has height monotonicity lemmas
- `_of_larger_radius` variants in Core/Discharge/WithData handle variable radius

### E2.4: HINT DECOUPLING LAYER — DONE (Session 97)

Added `_of_nonvanishing` theorem variants at every level of the chain:

| File | Theorem | Status |
|------|---------|--------|
| ResidueSide | `pv_equals_residue_sum_of_nonvanishing` | DONE, 0 sorry |
| Core | `valence_formula_base_identity_of_nonvanishing` | DONE |
| Core | `valence_formula_classical_form_of_nonvanishing` | DONE |
| Discharge | `valence_formula_base_identity_of_nonvanishing_rat` | DONE |
| Discharge | `valence_formula_classical_form_of_nonvanishing_rat` | DONE |

Also refactored `pv_equals_residue_sum` to route through `_of_nonvanishing` in the f≠0 case.

Integrability derived from nonvanishing via `intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing`.

### E2.5: FILL CORE NONVANISHING SORRY — DONE (Session 97)

Eliminated the single executable `sorry` in `valence_formula_base_identity_of_nonvanishing`
(Core.lean line 349). Replaced with:
```lean
have hint := intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing f h_nv
```

New lemmas in ResidueSide.lean:
- `logDeriv_continuousOn_fdBoundary_image_of_nonvanishing` (private)
- `intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing` (public)

All three `_of_nonvanishing` theorems now axiom-clean: `[propext, Classical.choice, Quot.sound]`.

### E2.6: Nonvanishing public split wrappers — DONE (Session 97/97b)

Both theorems already present in `ValenceFormula_Final_Split.lean` (added during E2.4):

| Name | Status |
|------|--------|
| `valenceFormula_split_from_S_of_nonvanishing` | DONE, axiom-clean |
| `valenceFormula_classical_split_from_S_of_nonvanishing` | DONE, axiom-clean |

### E2.7: WithData nonvanishing wrappers — DONE (Session 98)

4 theorems added to `ValenceFormula_Final_WithData.lean`:

| Name | Status |
|------|--------|
| `valenceFormula_with_data_of_nonvanishing` | DONE, axiom-clean |
| `valenceFormula_classical_with_data_of_nonvanishing` | DONE, axiom-clean |
| `valenceFormula_with_data_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_classical_with_data_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |

### E1.12: Nonvanishing-from-S AxiomClean wrappers — DONE (Session 100)

4 theorems added to `ValenceFormula_Final_AxiomClean.lean`:

| Name | Status |
|------|--------|
| `valenceFormula_axiomClean_from_S_of_nonvanishing` | DONE, axiom-clean |
| `valenceFormula_classical_axiomClean_from_S_of_nonvanishing` | DONE, axiom-clean |
| `valenceFormula_axiomClean_from_S_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_classical_axiomClean_from_S_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |

### E2.8: Larger-radius nonvanishing split wrappers — DONE (Session 99)

2 new theorems + 2 refactored in `ValenceFormula_Final_Split.lean`:

| Name | Status |
|------|--------|
| `valenceFormula_split_from_S_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_classical_split_from_S_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_split_from_S_of_nonvanishing` | REFACTORED → 1-line forward with `le_rfl` |
| `valenceFormula_classical_split_from_S_of_nonvanishing` | REFACTORED → 1-line forward with `le_rfl` |

### E2-3: Combine into auto-deriving wrapper

| Micro-task | Description | Blocker |
|------------|-------------|---------|
| E2-3a | Create `valence_formula_auto (hf : f ≠ 0) (S ...) : Σ wc·ord = k/12` that internally derives hint + hcusp_nonvan | E2-1, E2-2 |
| E2-3b | Wire into `ValenceFormula_Final.lean` | E2-3a, E1-2 |

---

## Dependency Graph

```
E2-1a → E2-1b → E2-1c → E2-1d ─┐
                                  ├─→ E2-3a → E2-3b → E1-2b (Option B)
E2-2a → E2-2b → E2-2c → E2-2d ─┘

E1-1 (decision) → E1-2a → E1-2b → E1-2c → E1-2d → E1-3
```

**E1 (Option A) can proceed immediately** — no blockers.
**E1 (Option B) requires E2** — substantial new infrastructure.

---

### E1.10: Explicit-zeros nonvanishing wrappers — DONE (Session 97c)

| Name | Status |
|------|--------|
| `valenceFormula_axiomClean_with_data_of_nonvanishing` | DONE, axiom-clean |
| `valenceFormula_classical_axiomClean_with_data_of_nonvanishing` | DONE, axiom-clean |

### E1.11: Larger-radius nonvanishing with-data wrappers — DONE (Session 99)

| Name | Status |
|------|--------|
| `valenceFormula_axiomClean_with_data_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |
| `valenceFormula_classical_axiomClean_with_data_of_nonvanishing_of_larger_radius` | DONE, axiom-clean |

---

## PV Non-Critical Sorries — CONFIRMED ALL DEAD CODE (Session 98 audit)

These 12 sorry in `ValenceFormula_PV.lean` are NOT on the critical path
(`pv_integral_eq_modular_transformation` is axiom-clean). ALL are in dead code chains
not referenced by any axiom-clean theorem. Cleanup is optional.

| Sorry Line | Enclosing Declaration | Type | Dead Code? |
|------------|----------------------|------|------------|
| 1924, 1936 | `cauchy_on_subseq` (line 1722) | PV Cauchy bound | Yes (no callers) |
| 3759 | `singular_annulus_bound` (line 3725) | Annulus integral bound | Yes (superseded by `_explicit`) |
| 4436, 4442 | `pv_limit_exists` (line 4352) | PV convergence | Yes (superseded by `pv_limit_via_dyadic`) |
| 4740 | `near_part_cauchy` (line 4582) | Near-part Cauchy bound | Yes (no callers) |
| 4810, 4883 | `smooth_crossing_cauchy` (line 4766) | Smooth crossing Cauchy | Yes (only in sorry chain) |
| 4983, 5032 | `immersion_crossing_cauchy` (line 4935) | Corner crossing Cauchy | Yes (only in sorry chain) |
| 5213 | `pv_integral_exists_f'_over_f` (line 5142) | PV existence | Yes (blocked + no callers) |
| 6426 | `horizontal_contribution_is_cusp` (line 6421) | Dead code (parameterized H) | Yes (no callers) |

---

## Completed Track Summary

| Track | Status | Sessions |
|-------|--------|----------|
| E1.6-E1.7 | DONE — superset-form theorems | 93 |
| E1.8 | DONE — larger-radius wrappers | 95a |
| E1.9 | BLOCKED → E1.9B DONE — AxiomClean.lean | 95b |
| E1.10 | DONE — explicit-zeros nonvanishing wrappers | 97c |
| E2.4 | DONE — `_of_nonvanishing` chain | 97 |
| E2.5 | DONE — core sorry filled | 97 |
| E2.6 | DONE — split wrappers (already present) | 97b |
| Session 98 | DONE — comprehensive dead code audit | 98 |
| E1.11 | DONE — larger-radius nonvanishing with-data wrappers | 99 |
| E1.12 | DONE — nonvanishing-from-S AxiomClean wrappers (4 theorems) | 100 |
| E2.8 | DONE — larger-radius nonvanishing split wrappers | 99 |

### E2.9: PV Dead-Code Cleanup — DONE (Session 101)

Deleted ~2000 lines of dead code from `ValenceFormula_PV.lean`. 0 sorry remaining.
Restored `cutoff_integrand_intervalIntegrable` (incorrectly deleted, used by living code).

### E2-UNCONDITIONAL: BLOCKED — Mathematically False (Session 101)

**Goal was:** Remove `h_nv`/`hint`/`hcusp_nonvan` entirely, exposing `(f hf S hS hS_complete)`.

**Status:** HARD STOP. The theorem is **false** under current `effectiveWinding` definitions.
Boundary-arc zeros get `effectiveWinding = 0` but represent orbifold-interior points needing
contribution 1. Holomorphic modular forms CAN have such zeros (e.g., `E₄³ - c·Δ` for suitable `c`).

**Bridge theorems added:** `hint_iff_nonvanishing_fdBoundary` (public iff, both directions proven).

This is a **definition-level mathematical obstruction**, not a Lean plumbing issue.
Fixing would require redefining `effectiveWinding` to handle orbifold identification
on the arc boundary, which is out of scope.

**Conclusion:** `_of_nonvanishing` theorems are the mathematically correct primary API.

---

### F3-PV-HEIGHT-PARAM — DONE (Session 107)

Height-parameterized PV infrastructure: `pv_integral_eq_modular_transformation_H` and wrappers.

| Name | File | Status |
|------|------|--------|
| `circleIntegral_logDeriv_cuspFunction_of_radius` | PV | DONE, axiom-clean |
| `seg5_integral_eq_circleIntegral_H` | PV | DONE, axiom-clean |
| `seg5_logDeriv_integral_eq_H` | PV | DONE, axiom-clean |
| `seg5_integral_eq_cusp_order_H` | PV | DONE, axiom-clean |
| `pv_integral_vertical_cancel_H` | PV | DONE, axiom-clean |
| `pv_integral_decompose_segments_H` | PV | DONE, axiom-clean |
| `nonvanishing_on_seg2_of_integrable_H` | PV | DONE, axiom-clean |
| `nonvanishing_on_seg3_of_integrable_H` | PV | DONE, axiom-clean |
| `pv_integral_eq_modular_transformation_H` | PV | DONE, axiom-clean |
| `modular_side_of_height` | ModularSide_Param | DONE, axiom-clean |

---

## Remaining Work

1. ~~**E2 auto-derive**: Remove `h_nv`/`hcusp_nonvan` from public API~~ — **BLOCKED** by
   definition-level mathematics (see E2-UNCONDITIONAL above). Not a Lean plumbing issue.

2. ~~**PV dead code cleanup**~~ — **DONE** (Session 101). 0 sorry in PV.lean.

3. ~~**F3-PV-HEIGHT-PARAM**~~ — **DONE** (Session 107). Height-parameterized PV/modular-side.
