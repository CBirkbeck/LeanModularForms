# Ticket D3 — No-Extra-Hypothesis Final Valence Formula

**Owner:** Claude Opus 4.6
**Status:** Phase A DONE, Phase D DONE (stubs), Phases B/C/E BLOCKED
**Created:** 2026-02-10

## Goal

Remove `hint : IntervalIntegrable` and `hcusp_nonvan` from the public signatures
of `valenceFormula` and `valenceFormula_classical` in `ValenceFormula_Final.lean`.

**Current public signature** (correct, but depends on sorry stubs):
```lean
theorem valenceFormula {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℚ) +
    ∑ p ∈ S, windingNumberCoeff' p * (orderOfVanishingAt' (⇑f) p : ℚ) = k / 12
```

**Target:** Same signature, but `#print axioms` must not show `sorryAx` from
`logDeriv_fdBoundary_intervalIntegrable` or `cuspFunction_nonvanishing_on_ball`.

## Ground-Truth Constraints

1. `hint : IntervalIntegrable (logDeriv f' ∘ fdBoundary * deriv fdBoundary)` is
   **NOT derivable** in general — `f'/f` has poles at elliptic points on `∂𝒟`.
2. `hcusp_nonvan` with fixed `seg5_q_radius` is **NOT derivable** from `hf : f ≠ 0`
   uniformly in `f` — the first q-expansion zero varies with f.
3. Therefore the final no-extra-hyp theorem requires **API refactor**, not
   discharge-by-force.

## Architecture: Existential Height

The fix is to **choose the FD boundary height `H` existentially** for each `f`:
- Choose `H` large enough that the cusp function is nonvanishing on the q-circle.
- The boundary `∂𝒟_H` avoids all zeros of `f` (finitely many in any compact region).
- The `IntervalIntegrable` issue vanishes when the boundary doesn't pass through poles.

## Phases

### Phase A — Cusp Height Infrastructure — COMPLETE
**File:** `ValenceFormula_CuspHeight.lean` (144 lines, 0 sorry)
**Axioms:** `[propext, Classical.choice, Quot.sound]` — no sorryAx

1. `cuspFunction_not_eventually_zero` — identity principle (analytic → isolated zeros → f ≡ 0)
2. `cuspFunction_eventually_ne_zero` — cusp function eventually nonzero in 𝓝[≠] 0
3. `exists_radius_cusp_nonvanishing`:
   `∃ r > 0, ∀ q ∈ closedBall(0, r), q ≠ 0 → cuspFunction 1 f q ≠ 0`
4. `heightOfRadius (r : ℝ) : ℝ := -Real.log r / (2 * Real.pi)`
5. `heightOfRadius_pos_of_lt_one`
6. `exists_height_cusp_nonvanishing`:
   `∃ H > √3/2, ∀ q ∈ closedBall(0, exp(-2πH)), q ≠ 0 → cuspFunction 1 f q ≠ 0`

### Phase B — Parameterized FD Boundary
**File:** `ValenceFormula_FD_Boundary_H.lean`

1. `fdBoundaryH (H : ℝ)` — FD boundary with height parameter
2. `fdBoundary_seg{1..5}_H` — segment definitions
3. `fdPartition_H`
4. `fdBoundaryH_eq_fdBoundary_at_defaultHeight`
5. `seg5_q_radius_H_def`
6. `fdBoundaryH_closed` / `fdBoundaryH_piecewiseC1`

### Phase C — Modular Side with Existential Height
**File:** `ValenceFormula_ModularSide_H.lean`

1. `pv_integral_eq_modular_transformation_H` — with `fdBoundaryH H`
2. `pv_integral_eq_modular_transformation_auto (hf : f ≠ 0)` — selects H from Phase A

### Phase D — Core Auto Bridge (Interface Prep)
**File:** `ValenceFormula_Core_AutoBridge.lean`

1. `valence_formula_base_identity_auto_signature` — statement only
2. `valence_formula_classical_auto_signature` — statement only

### Phase E — Final Integration (After Ticket C)
**File:** `ValenceFormula_Final.lean` (edit)

Replace sorry stubs with existential-height proofs.

## Scope Boundary with Ticket C

- **DO NOT edit:** `ValenceFormula_Core.lean`, `ValenceFormula_ResidueSide.lean`
- **DO edit:** new files (Phases A-D) and `ValenceFormula_Final.lean` (Phase E)

## Current Blockers in ValenceFormula_Final.lean

| Blocker | Type | Fix |
|---------|------|-----|
| `logDeriv_fdBoundary_intervalIntegrable` | sorry | Phase B+C: existential H avoids poles |
| `cuspFunction_nonvanishing_on_ball` | sorry | Phase A: existential radius/height |
| `zeros_in_fd_are_classified` | Ticket C B6 | Upstream — wait for Ticket C |

## Acceptance Criteria

1. New infrastructure files compile (`lake build` passes).
2. No `hint` or `hcusp_nonvan` in public signatures of `valenceFormula`/`valenceFormula_classical`.
3. `#print axioms valenceFormula` contains no new local `sorryAx` from Final-side files.
4. Progress log updated with commands run, files touched, unresolved blockers.
