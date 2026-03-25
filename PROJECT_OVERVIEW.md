# Project Overview: ContourIntegral API + Winding Number Files

Generated: 2026-03-25

## Summary
- Files: 12 (4 API + 4 Winding + 4 WindingWeights)
- Total lines: 7,209
- Sorries: 0
- Total declarations: ~170

## ContourIntegral API (598 lines, 14 declarations)

| File | Lines | Decls | Key API |
|------|-------|-------|---------|
| PVSplit.lean | 127 | 1 | `pv_split_at_crossing` |
| SegmentFTC.lean | 223 | 8 | `ftc_telescope_closed_split_five`, `ftc_telescope_integrability` |
| CrossingLimit.lean | 188 | 2 | `pv_tendsto_of_crossing_limit`, `pv_tendsto_of_crossing_limit_asymmetric` |
| WindingNumber.lean | 60 | 3 | `gWN_eq_neg_half_of_pv_tendsto`, `gWN_eq_neg_sixth_of_pv_tendsto` |

## Winding Files (2,998 lines, 87 declarations)

| File | Lines | Decls | Main Result | Uses API |
|------|-------|-------|-------------|----------|
| RightEdge.lean | 935 | 27 | `gWN = -1/2` (right vertical) | symmetric |
| LeftEdge.lean | 782 | 23 | `gWN = -1/2` (left vertical) | symmetric |
| UnitArc.lean | 591 | 19 | `gWN = -1/2` (smooth arc) | symmetric |
| UnitArcHelpers.lean | 690 | 18 | helpers for UnitArc | N/A |

## WindingWeights Files (3,613 lines, 91 declarations)

| File | Lines | Decls | Main Result | Uses API |
|------|-------|-------|-------------|----------|
| Common.lean | 222 | 16 | shared helpers | N/A |
| I.lean | 1,161 | 27 | `gWN = -1/2` (at i) | symmetric |
| Rho.lean | 1,092 | 23 | `gWN = -1/6` (at ρ) | asymmetric |
| RhoPlusOne.lean | 1,138 | 25 | `gWN = -1/6` (at ρ+1) | asymmetric |

---

## Dead Code (candidates for deletion)

### Confirmed unused within project:

| Declaration | File | Lines | Reason |
|-------------|------|-------|--------|
| `unitArc_norm_offset_symm` | UnitArc:120 | 11 | 0 references |
| `unitArc_norm_pos_at_offset` | UnitArc:189 | 10 | 0 references |
| `unitArc_norm_continuous` | UnitArc:200 | 4 | 0 references |
| `unitArc_final_dist_bound` | UnitArc:340 | 12 | 0 references |
| `cutoff_integral_eq_ftc_rho_plus_one` | RhoPlusOne:644 | 132 | superseded by `pv_tendsto_of_crossing_limit_asymmetric` |
| `i_norm_gt_right_helper` | I:831 | 23 | 0 references |
| `i_norm_le_middle_helper` | I:855 | 21 | 0 references |
| `fdBoundary_H_eq_rho_iff` | Rho:139 | 11 | 0 references in winding files |
| `arg_approach_rho_left` | Rho:210 | 16 | superseded by `_helper` version |
| `g_rho_differentiableAt` | Rho:392 | 41 | 0 references |

**Total deletable: ~280 lines**

### SegmentFTC unused theorems (API available but not yet adopted):

| Declaration | Lines | Status |
|-------------|-------|--------|
| `ftc_telescope_closed_split` | 12 | Available but unused — `ftc_telescope_closed_split_five` used instead |
| `ftc_telescope_transfer` | 12 | Available but unused |
| `ftc_telescope_piecewise_two` | 21 | Available but unused |
| `ftc_telescope_piecewise_three` | 28 | Available but unused |

These are general API — keep for future use.

---

## Shared Helpers in Wrong Location

These helpers are defined in RightEdge.lean but used across multiple files:

| Declaration | Defined in | Used by |
|-------------|-----------|---------|
| `ftc_log_neg` | RightEdge:147 | RightEdge (5x), LeftEdge (indirectly), UnitArcHelpers (5x) |
| `ftc_log` | RightEdge:171 | LeftEdge (5x), UnitArcHelpers (2x) |
| `log_neg_rI_sub_log_rI` | RightEdge:192 | RightEdge, LeftEdge |
| `log_div_of_re_pos` | RightEdge:199 | UnitArc, UnitArcHelpers |
| `hasDerivAt_arc_rep` | RightEdge:244 | LeftEdge, UnitArcHelpers |
| `re_fdBoundary_H_seg4` | RightEdge:261 | UnitArcHelpers |
| `im_fdBoundary_H_seg5` | RightEdge:267 | UnitArcHelpers |
| `rightEdge_dist_from_arc` | RightEdge:115 | LeftEdge |

**Recommendation**: Move these 8 helpers to `Common.lean` or a new `SharedHelpers.lean`.

---

## Consolidation Opportunities

### A. Parallel Structure: Rho ↔ RhoPlusOne

These files have nearly identical structure with different crossing parameters:

| Pattern | Rho | RhoPlusOne |
|---------|-----|------------|
| Crossing point | t₀ = 3 | t₀ = 1 |
| Left side | arc (seg2) | vertical (seg0) |
| Right side | vertical (seg3) | arc (seg1-2) |
| δ_left | arcsin-based | linear |
| δ_right | linear | arcsin-based |
| Limit | -πi/3 | -πi/3 |

The geometry is **mirror-symmetric** (left↔right swap). A parametric version could save ~400 lines.

### B. FTC Telescope Pattern

Each file has a ~150-250 line `_ftc_telescope` helper. All follow the same pattern:
1. Define segment functions (~15 lines)
2. Apply `ftc_log_piece` on each segment (~35 lines)
3. Establish ae-equality (~20 lines)
4. Transfer integrability (~25 lines)
5. Combine and telescope (~15 lines)

`ftc_telescope_closed_split_five` was designed to replace steps 2-5, but type mismatches (negated log, different segment counts) prevent direct use. A more flexible variant accepting per-segment FTC results as a `List` or `Fin n →` would work.

### C. Missing: `ftc_log` / `ftc_log_neg` in GRT

`ftc_log` and `ftc_log_neg` (RightEdge:147-190) are general FTC lemmas that should live in `GeneralizedResidueTheory/LogDerivFTC.lean` alongside the existing `integral_logDeriv_eq_log_sub`. The negated variant handles curves where `-f` stays in slitPlane.

---

## Top Priorities

1. **Delete ~280 lines of dead code** across UnitArc, I, Rho, RhoPlusOne
2. **Move 8 shared helpers** from RightEdge to Common.lean
3. **Add `ftc_log_neg` to LogDerivFTC.lean** (general API, not FD-specific)
