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

## PV Non-Critical Sorries (for reference)

These 12 sorry in `ValenceFormula_PV.lean` are NOT on the critical path
(`pv_integral_eq_modular_transformation` is axiom-clean). Cleanup is optional.

| Sorry Line | Enclosing Declaration | Type |
|------------|----------------------|------|
| 1924, 1936 | `cauchy_on_subseq` (line 1722) | PV Cauchy bound |
| 3759 | `singular_annulus_bound` (line 3725) | Annulus integral bound |
| 4436, 4442 | `pv_limit_exists` (line 4352) | PV convergence |
| 4740 | `near_part_cauchy` (line 4582) | Near-part Cauchy bound |
| 4810, 4883 | `smooth_crossing_cauchy` (line 4766) | Smooth crossing Cauchy |
| 4983, 5032 | `immersion_crossing_cauchy` (line 4935) | Corner crossing Cauchy |
| 5213 | `pv_integral_exists_f'_over_f` (line 5142) | PV existence |
| 6426 | `horizontal_contribution_is_cusp` (line 6421) | Dead code (parameterized H) |

---

## Recommended Execution Order

1. **E1 Option A** (immediate, ~1 session): Rewire Final.lean to split chain, retain hypotheses.
   This gives `sorryAx`-free public API right away.

2. **E2** (medium effort, ~3-5 sessions): Derive `hint` + `hcusp_nonvan` from `hf`.
   Major new infrastructure needed (parameterized H, cuspFunction meromorphicity).

3. **E1 Option B** (after E2): Switch Final.lean to auto-deriving wrapper.

4. **PV sorry cleanup** (optional, low priority): Fill the 12 non-critical sorries.
