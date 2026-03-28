# Project Overview: LeanModularForms

Generated: 2026-03-28

## Executive Summary

This project formalizes the **generalized residue theorem** of Hungerbühler–Wasem
(arXiv:1808.00997v2, Theorem 3.3) and applies it to the **valence formula for modular
forms** and **Viazovska's sphere packing** contour integrals. The codebase spans 84 files
and ~48,600 lines across three main directories:

- **GeneralizedResidueTheory/** (37 files): The core complex analysis framework including
  piecewise C¹ curves, Cauchy principal values, generalized winding numbers, Dixon's proof
  of the Cauchy integral formula for null-homologous curves, and the full Theorem 3.3 with
  conditions (A') and (B).

- **ValenceFormula/** (44 files): The valence formula for weight-k modular forms on SL₂(ℤ),
  building on the generalized residue theorem. Includes fundamental domain geometry,
  boundary winding numbers, orbit pairing, and the textbook-form result.

- **SpherePacking/** (3 files): Application to Viazovska's magic function, proving the
  contour equivalence I₁₂ = I₁₂_vert + I₁₂_horiz using original triangular contours.

**Key metrics:** 0 sorries, 0 `set_option maxHeartbeats`, 1754 declarations (1017 lemmas,
547 theorems, 171 definitions).

## Statistics

| Metric | Count |
|--------|-------|
| Files | 84 |
| Total lines | 48,590 |
| Declarations | 1,754 |
| - lemmas | 1,017 |
| - theorems | 547 |
| - definitions | 171 |
| - structures | 7 |
| - classes | 3 |
| Sorries | 0 |
| `set_option maxHeartbeats` | 0 |

---

## Part 1: Moral Duplications

### HIGH Priority (should fix)

1. **`ftc_log_piece` wrapper** — `ValenceFormula/WindingWeights/Common.lean:100` wraps
   `GeneralizedResidueTheory/LogDerivFTC.lean:78` with zero added value.
   **Action:** Delete wrapper, import LogDerivFTC directly.

2. **`fdBoundary` local copy** — `RectHomotopy/Geometry.lean:224` is an acknowledged copy of
   `Boundary/Basic.lean:64` (same 5-segment curve with renamed height constant).
   **Action:** Delete copy, import from Boundary/Basic.

3. **`H_height` vs `heightCutoff`** — Both equal `√3/2 + 1`, defined independently in
   `RectHomotopy/Geometry.lean:207` and `Boundary/Basic.lean:32`.
   **Action:** Unify to `heightCutoff`.

### MEDIUM Priority

4. **`cos/sin_two_pi_div_three'`** — Primed copies in `RectHomotopy/HomotopyDef.lean`
   duplicate `WindingWeights/Common.lean` versions.
   **Action:** Delete primed copies.

5. **`exp_real_angle_I` vs `exp_real_mul_I`** — Same Euler formula identity in two files.
   **Action:** Unify name.

6. **`fd_im_gt_half` private duplicates** — Same fact proved privately in `OrbitSum.lean`
   and `TextbookForm.lean`.
   **Action:** Make one public, delete other.

### KEEP (intentional API layering)

- Convex vs null-homologous wrappers (thin corollaries, good API design)
- `rho`/`i_point` (ℂ) vs `ellipticPointRho'` (ℍ) — different types
- `cpv_exists_inv_sub*` variants — genuinely different hypotheses
- Single-curve vs cycle theorems — different input types

---

## Part 2: Recommended Action Plan

### Priority 1: Quick Wins (can do now)
- Delete `ftc_log_piece` wrapper in ValenceFormula
- Delete `fdBoundary` copy in RectHomotopy/Geometry
- Unify `H_height` → `heightCutoff`
- Delete `cos/sin_two_pi_div_three'` primed copies
- Delete `exp_real_mul_I` duplicate

### Priority 2: API Improvements
- Rename `generalizedResidueTheorem` in Residue/ to avoid name collision
- Make `fd_im_gt_half` public and shared
- Add connecting lemmas between ℂ and ℍ point definitions

### Priority 3: Unused Declaration Cleanup (~52 declarations)

**Basic.lean (9):** Remove `ModelSectorCurve` (struct + 6 methods), `residue'`, `residueIntegral'`
**PrincipalValue.lean (11):** Remove `cauchyPrincipalValueIntegrand_add'/_smul'/_eq_indicator/_integrable`,
  `cauchyPrincipalValue_add'/_smul'`, `windingNumber_homotopy_invariant'`,
  `cauchyPrincipalValueExists_of_singular_pole/_continuous_piecewise/_simple_pole`,
  `limUnder_eventually_eq'`, `epsilon_cutoff_trivial_on_compact`
**HomologicalCauchy.lean (1):** Remove `integral_eq_sum_residues_of_nullHomologous`
**Residue.lean (3):** Remove `cauchyPrincipalValueIntegrandOn_eq_zero_of_near`,
  `cauchyPrincipalValueExistsOn_empty/_singleton`
**GeneralizedResidueTheorem.lean (2):** Remove `generalizedResidueTheorem_convex`,
  `HasSimplePoleAt.meromorphicAt`
**Cycle.lean (15):** Entire file unused — keep as future API or remove
**Definitions.lean (11):** Remove `fundamentalDomainCanonical` + 4 related,
  `orderOfVanishingAt_nonneg`, `windingNumberCoeff'` + 4 related

### Priority 4: Mathlib API audit (pending)
- Check all 171 definitions against mathlib
- Key candidates: `PiecewiseC1Curve` (no mathlib equivalent),
  `cauchyPrincipalValue'` (custom CPV), `IsNullHomologous` (custom)
