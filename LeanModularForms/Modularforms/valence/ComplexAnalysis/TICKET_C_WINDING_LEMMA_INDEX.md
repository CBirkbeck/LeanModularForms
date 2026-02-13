# Ticket C — Winding Lemma Index

Quick reference for Ticket C worker: exact theorem names and locations for
winding number, crossing contribution, and fdBoundary immersion facts.

---

## 1. Interior Winding = -1 Bridge

**File:** `ValenceFormula_InteriorWinding.lean`

| Theorem | Line | Signature |
|---------|------|-----------|
| `generalizedWindingNumber_fdBoundary_eq_neg_one` | 60 | `(p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : \|p.re\| < 1/2) (hp_im_pos : 0 < p.im) (hp_im : p.im < H_height) : gWN = -1` |
| `generalizedWindingNumber_fdBoundary_eq_neg_one_uhp` | 72 | `(s : ℍ) ... : gWN = -1` (derives `hp_im_pos` from `s.im_pos`) |
| `generalizedWindingNumber_fdBoundary_eq_neg_windingCoeff_interior` | 83 | `(s : ℍ) ... (hs_not_i) (hs_not_rho) : gWN = -(windingNumberCoeff' s : ℂ)` |

**File:** `ValenceFormula_ResidueSide.lean` (already-wired bridges)

| Theorem | Line | Signature |
|---------|------|-----------|
| `winding_number_interior_bridge` (private) | 179 | Forwards to `RectHomotopyProof.generalizedWindingNumber_fdBoundary_eq_neg_one` |
| `gWN_interior_eq_neg_one` | 186 | `(p : ℍ) (hp : isInteriorPoint p) : gWN = -1` |
| `gWN_interior_eq_neg_ew` | 191 | `(p : ℍ) (hp : isInteriorPoint p) : gWN = -(effectiveWinding p : ℂ)` |
| `gWN_eq_zero_of_boundary_zero` (private) | 2528 | Boundary/exterior points: gWN cancels with effectiveWinding = 0 |

---

## 2. Smooth / Corner Crossing Contributions

**File:** `WindingNumber.lean`

### Core definitions

| Name | Line | Description |
|------|------|-------------|
| `angleAtCrossing` | ~792 | Angle contribution at a crossing point |
| `windingNumberWithAngles` | 828 | Explicit angle-tracking winding number |
| `windingNumberWithAngles'` | 836 | Variant with explicit crossings finset |

### Smooth crossing (angle = π → contribution = 1/2)

| Theorem | Line | Description |
|---------|------|-------------|
| `windingNumber_smooth_crossing` | 863 | Single smooth crossing contributes 1/2 (angle-based) |
| `generalizedWindingNumber_eq_half_smooth_crossing` | 3101 | PV-based gWN = 1/2 at smooth crossing |
| `generalizedWindingNumber_eq_half_smooth_crossing_direct` | 3198 | Direct computation variant |
| `pv_smooth_crossing_eq_ipi` | 2641 | PV integral of 1/γ at smooth crossing = iπ |

### Corner crossing (angle α → contribution = α/(2π))

| Theorem | Line | Description |
|---------|------|-------------|
| `windingNumber_corner_crossing` | 886 | Corner crossing contributes α/(2π) (angle-based) |
| `generalizedWindingNumber_eq_corner_contribution` | 3122 | PV-based gWN = α/(2π) at corner |
| `generalizedWindingNumber_eq_corner_contribution_slitPlane` | 3164 | Via slitPlane hypothesis |

### Winding number decomposition

| Theorem | Line | Description |
|---------|------|-------------|
| `windingNumber_decomposition` | 1037 | Full decomposition: n + Σ angle contributions |
| `windingNumber_decomposition_sub` | 1004 | Subtract version |
| `generalizedWindingNumber_eq_angleContribution_single` | 2970 | Single crossing: gWN = angle/(2π) |
| `pv_integral_single_crossing_eq_angle` | 2720 | PV ∮ 1/z = i · crossing angle |

---

## 3. Elliptic Winding Coefficients

**File:** `ValenceFormula_EllipticContrib.lean`

| Theorem | Line | Description |
|---------|------|-------------|
| `windingContribution_at_i_eq_half` | 79 | `windingNumberCoeff' ellipticPoint_i' = 1/2` |
| `windingContribution_at_rho_eq_sixth` | 102 | Individual ρ corner = 1/6 |
| `windingContribution_at_rho'_eq_sixth` | 127 | Individual ρ' corner = 1/6 |
| `windingContribution_rho_total_eq_third` | 141 | `windingNumberCoeff' ellipticPoint_rho' = 1/3` |

**File:** `ValenceFormulaDefinitions.lean`

| Theorem | Line | Description |
|---------|------|-------------|
| `windingNumberCoeff_interior` | 220 | `p ≠ i → p ≠ ρ → windingNumberCoeff' p = 1` |
| `windingNumberCoeff_at_i` | 226 | `windingNumberCoeff' ellipticPoint_i' = 1/2` |
| `windingNumberCoeff_at_rho` | 237 | `windingNumberCoeff' ellipticPoint_rho' = 1/3` |
| `windingNumberCoeff_trichotomy` | 241 | Three-case split for coefficients |

---

## 4. effectiveWinding (in ResidueSide)

**File:** `ValenceFormula_ResidueSide.lean`

| Name | Line | Description |
|------|------|-------------|
| `isInteriorPoint` | 66 | `‖p‖ > 1 ∧ \|p.re\| < 1/2 ∧ p.im < H_height` |
| `classifyPoint` | 84 | Interior / i / ρ / boundary classification |
| `effectiveWinding` | 99 | 1 (interior), 1/2 (i), 1/3 (ρ), 0 (else) |
| `effectiveWinding_eq_one_of_interior` | 122 | Interior → effectiveWinding = 1 |
| `effectiveWinding_eq_half_at_i` | 130 | effectiveWinding at i = 1/2 |
| `effectiveWinding_eq_third_at_rho` | 133 | effectiveWinding at ρ = 1/3 |
| `effectiveWinding_rho_plus_one_eq_zero` | 153 | effectiveWinding at ρ+1 = 0 |
| `effectiveWinding_eq_windingCoeff_of_classified` | 137 | With classification → equals windingNumberCoeff' |

---

## 5. fdBoundary as PiecewiseC1Immersion

**File:** `ValenceFormula_FD_Boundary.lean`

| Name | Line | Description |
|------|------|-------------|
| `fdBoundaryCurve` | 956 | `PiecewiseC1Curve` wrapping `fdBoundary` on [0,5] |
| `fdBoundaryImmersion` | 1350 | `PiecewiseC1Immersion` (deriv_ne_zero + limit lemmas) |
| `fdBoundaryImmersion_closed` | 1357 | `fdBoundaryImmersion.toPiecewiseC1Curve.IsClosed` |
| `fdBoundaryFullPartition` | 810 | `{0, 1, 2, 3, 4, 5} : Finset ℝ` |

---

## Important: PV limitation at crossings

`generalizedWindingNumber'` (PV-based) gives **0** at crossing/elliptic points.
Do NOT attempt to prove `generalizedWindingNumber' = -(effectiveWinding)` at i or ρ.
The architecture uses `effectiveWinding` directly for orbifold coefficients.
