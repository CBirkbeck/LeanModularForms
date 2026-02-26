# TICKET F4-B: Remove Crossing SorryAx + h_nv Dependency

## Status: B2/B3 DONE (auto_interior chain), B1 deferred

## Completed: Auto-Interior Chain (B2/B3)

### New Theorems Added (all axiom-clean, sorry-free)

**ResidueSide** (`ValenceFormula_ResidueSide.lean`):
- `nonvanishing_fdBoundary_of_interior_zeros` — h_interior → h_nv

**Core** (`ValenceFormula_Core.lean`):
- `valence_formula_base_identity_auto_interior` — base identity, no h_nv/hint/h_pv_eq_residue
- `valence_formula_classical_form_auto_interior` — classical form variant

**Split** (`ValenceFormula_Final_Split.lean`):
- `valenceFormula_split_from_S_auto_interior` — orbifold S-superset form
- `valenceFormula_classical_split_from_S_auto_interior` — classical S-superset form

**AxiomClean** (`ValenceFormula_Final_AxiomClean.lean`):
- `valenceFormula_axiomClean_from_S_auto_interior` — public API, orbifold form
- `valenceFormula_classical_axiomClean_from_S_auto_interior` — public API, classical form

### Axiom Check: All `[propext, Classical.choice, Quot.sound]`

### Design

Under `h_interior` (all zeros satisfy `classifyPoint = .interior`), boundary
nonvanishing is derived automatically because:
- Arc points: `‖z‖ = 1` (interior requires `> 1`)
- Vertical points: `|Re| = 1/2` (interior requires `< 1/2`)
- Top edge: `Im = H_height` (interior requires `< H_height`)

This gives `h_nv → hint → h_pv_eq_residue` for free. Only `hcusp_nonvan`
remains as infrastructure.

**Applicability**: Modular forms with interior-only zeros (e.g., Δ).
Not applicable to E₄ (zero at ρ) or E₆ (zero at i).

### Remaining Hypothesis: `hcusp_nonvan`

Under `h_interior + hzeros_complete`, no zeros exist with `Im ≥ H_height`.
This should imply `hcusp_nonvan` via T-periodicity + q-expansion correspondence,
but formalizing this requires additional infrastructure (~50-100 lines).

To fully eliminate `hcusp_nonvan`, one could either:
1. Formalize the "no high zeros → cusp function nonzero" correspondence
2. Build a parameterized residue theorem (`pv_equals_residue_sum` at `fdBoundary_H H`)
   and compose with `modular_side_auto_cusp`

## Milestones

### B1: Fill crossing-chain sorries in WindingNumber.lean
**Status: DEFERRED** (both sorries remain, NOT blocking downstream)

These theorems are NOT used by ResidueSide/Core/Final.
The axiom-clean `_direct` and `_slitPlane` variants handle the valence formula.

Target theorems (currently have `sorryAx`):
1. `generalizedWindingNumber_eq_angleContribution_single` (line ~3055)
2. `generalizedWindingNumber_eq_half_smooth_crossing` (line ~3186)
3. `generalizedWindingNumber_eq_corner_contribution` (line ~3207)

#### Sorry 1 (line 2525): `L_pv = I * pi`
- **Difficulty**: HIGH (~200 lines). Core challenge: H-W Proposition 2.3

#### Sorry 2 (line 2980): Corner crossing PV convergence
- **Difficulty**: HIGH (similar to sorry 1)

### B2: Boundary nonvanishing from h_interior
**Status: DONE**

`nonvanishing_fdBoundary_of_interior_zeros` proves h_nv from h_interior.

### B3: Core/Split/AxiomClean auto_interior chain
**Status: DONE**

8 new theorems across 4 files, all axiom-clean and sorry-free.

## Key Files

| File | Role | Changes |
|------|------|---------|
| `ValenceFormula_ResidueSide.lean` | h_nv derivation | +1 theorem |
| `ValenceFormula_Core.lean` | Core auto_interior | +2 theorems |
| `ValenceFormula_Final_Split.lean` | S-superset forms | +2 theorems |
| `ValenceFormula_Final_AxiomClean.lean` | Public API | +2 theorems |
| `ValenceFormula_Core_AutoBridge.lean` | Documentation | Updated |
| `WindingNumber.lean` | B1 target | 2 sorries (deferred) |

## Public API Summary (AxiomClean)

### Best available (auto_interior, for Δ-like forms):
```
valenceFormula_axiomClean_from_S_auto_interior
  (f hf S hS hS_complete h_interior hcusp_nonvan) :
  ord_∞ + Σ ew·ord = k/12
```
Hypotheses: f ≠ 0, S superset of zeros in 𝒟', all zeros interior, cusp nonvanishing.

### Most general (auto_cusp, for all forms):
```
valenceFormula_axiomClean_from_S_auto_cusp
  (f hf S hS hS_complete) :
  ∃ H₀ > √3/2, ∀ H ≥ H₀, hint_H → h_pv_eq_residue → ord_∞ + Σ ew·ord = k/12
```
Hypotheses: f ≠ 0, S superset of zeros in 𝒟'. Returns existential over height.
