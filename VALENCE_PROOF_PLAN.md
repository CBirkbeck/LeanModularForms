# Comprehensive Plan: Proving the Valence Formula

## Executive Summary

The valence formula states that for a nonzero modular form f of weight k for SL₂(ℤ):

```
ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{p ∈ 𝒟°} ord_p(f) = k/12
```

**Current Status**: The proof infrastructure is mostly complete. There is ONE critical sorry that blocks the entire proof chain, plus several auxiliary sorries.

---

## Dependency Chain Analysis

The valence formula proof has a single critical dependency chain:

```
valenceFormula' (line 5619) - FINAL THEOREM
    ↓ uses
valenceFormula_core_equality (line 5249)
    ↓ uses
contour_integral_two_ways (line 5231)
    ↓ uses
generalizedResidueTheorem_modularFormApplication (line 4851)
    ↓ uses
modularTransformation_valenceIdentity (line 4722)
    ↓ uses
contour_integral_equality (line 4661)
    ↓ uses
valence_core_identity (line 4484)
    ↓ uses
valenceFormula_fundamental (line 4252)
    ↓ uses
contour_integral_agreement (line 4070)
    ↓ uses
valenceFormula_identity_base (line 3989) ← **CRITICAL SORRY at line 4014**
```

**Key Insight**: ALL valence formula theorems depend on `valenceFormula_identity_base`. Filling this one sorry completes the entire chain.

---

## Infrastructure Status by File

### ✅ ResidueTheory.lean - COMPLETE (0 sorries)

| Theorem | Line | Status |
|---------|------|--------|
| `generalizedResidueTheorem'` | 5573 | ✅ Complete |
| `integral_eq_sum_residues_of_avoids` | 2745 | ✅ Complete |
| `classicalResidueTheorem` | 6180 | ✅ Complete |
| `argumentPrinciple` | 6205 | ✅ Complete |

**This provides**: PV ∮_γ f = 2πi × Σ (n_s × res_s) for curves passing through simple poles.

### 🔶 ValenceFormula.lean - 4 sorries (per LSP diagnostics)

| Line | Lemma | Description | Priority |
|------|-------|-------------|----------|
| **~4040** | `valenceFormula_identity_base` | **CRITICAL** - Main theorem (after `apply valence_formula_from_contour_equality`) | **HIGHEST** |
| 3635 | `generalizedWindingNumber_at_rho_eq_sixth` | Orientation at ρ | HIGH |
| 3704 | `generalizedWindingNumber_at_rho'_eq_sixth` | Orientation at ρ' | HIGH |
| 1861 | `fundamentalDomainBoundary_homotopic_to_circle` | Homotopy for interior points | LOW |

**Note**: `generalizedWindingNumber_at_i_eq_half` uses `orientation_at_i_strict` which is **FULLY PROVED** (line 3352). No sorry there!

### 🔶 WindingNumber.lean - 2 sorries

| Line | Lemma | Description | Priority |
|------|-------|-------------|----------|
| 2355 | `pv_smooth_crossing_pv_integral_agrees` | H-W 2.3 PV equivalence | MEDIUM |
| 2720 | Corner case | Non-smooth crossings | LOW |

### 🔶 PiecewiseHomotopy.lean - 2 sorries

| Line | Description | Priority |
|------|-------------|----------|
| 622 | Continuity at partition boundary | LOW |
| 643 | Slice continuity for deriv | LOW |

### 🔶 PiecewiseHomotopyHelpers.lean - 3 sorries

| Line | Description | Priority |
|------|-------------|----------|
| 247 | Endpoint derivative continuity | LOW |
| 311 | Derivative bound constant | LOW |
| 367 | Dominated convergence integrand | LOW |

---

## What's Available (Sorry-Free Infrastructure)

### In ValenceFormula.lean:

| Lemma | Line | Description |
|-------|------|-------------|
| `orientation_at_i_strict` | 3352 | ✅ **Proves** Im(ratio) > 0 at i |
| `valence_formula_from_contour_equality` | 3926 | ✅ Cancels 2πi from both sides |
| `vertical_edges_cancel` | 5446 | ✅ T-invariance cancellation |
| `arc_contribution_is_k_div_12` | 5554 | ✅ S-transformation gives k/12 |
| `logDeriv_residue_eq_order` | 5265 | ✅ Residue of f'/f = order |
| `contour_decomposition` | 5037 | ✅ Decomposes ∮ into arc + cusp |
| `windingNumberCoeff'` | (defined) | ✅ Orbifold coefficients 1, 1/2, 1/3 |

### In WindingNumber.lean:

| Lemma | Line | Description |
|-------|------|-------------|
| `generalizedWindingNumber_eq_corner_contribution` | 2946 | ✅ angle α → contribution α/(2π) |
| `generalizedWindingNumber_eq_angleContribution_single` | ~2900 | ✅ Single crossing formula |
| `angleAtCrossing_at_i_eq_pi` | (defined) | ✅ Angle at i = π |
| `angleAtCrossing_at_rho_eq_pi_div_three` | (defined) | ✅ Angle at ρ = π/3 |
| `angleAtCrossing_at_rho'_eq_pi_div_three` | (defined) | ✅ Angle at ρ' = π/3 |

---

## Proof Strategy

### Phase 1: Fill Orientation Sorries (Lines 3547, 3608, 3677)

**Goal**: Prove `h_orientation : ∀ᶠ δ in 𝓝[>] 0, Im(ratio) > 0`

**At i (line 3547)**:
- **Helper exists**: `orientation_at_i_strict` (line 3352) is FULLY PROVED!
- **Fix**: Simply use `exact orientation_at_i_strict`

**At ρ (line 3608)**:
- Need to prove similar to i, but for the corner at t=3
- The ratio involves:
  - γ(3-δ) on the arc segment
  - γ(3+δ) on the vertical segment
- Mathematical content: counterclockwise turn gives Im > 0

**At ρ' (line 3677)**:
- Similar to ρ, but at t=1
- The ratio involves:
  - γ(1-δ) on the vertical segment
  - γ(1+δ) on the arc segment

### Phase 2: Fill Main Theorem (Line 4014)

**Current state after `apply valence_formula_from_contour_equality`**:
```lean
⊢ 2 * π * I * Σ (coeff × order) = 2 * π * I * (k/12 - ord_∞)
```

**Strategy**: Show both sides equal the same contour integral ∮_{∂𝒟} f'/f

**LHS (Residue Side)**:
1. Apply `generalizedResidueTheorem'` to f'/f
2. Use `logDeriv_residue_eq_order`: residue = order
3. Use winding number results:
   - Interior: winding = 1 (classical, needs homotopy)
   - At i: winding = 1/2 (from Phase 1)
   - At ρ: winding = 1/6 (from Phase 1)
   - At ρ': winding = 1/6 (from Phase 1)
4. Total at ρ-class: 1/6 + 1/6 = 1/3 = windingNumberCoeff'

**RHS (Modular Side)**:
1. Use `vertical_edges_cancel`: T-invariance → 0
2. Use `arc_contribution_is_k_div_12`: S-transformation → k/12
3. Use q-expansion → cusp contribution = ord_∞

**Equality**: Both = ∮_{∂𝒟} f'/f, so LHS = RHS

### Phase 3 (Optional): Fill Remaining Sorries

The homotopy sorries (1879, 1938, 1945, 1949) are only needed for:
- Proving interior points have winding number = 1
- This requires showing the boundary is homotopic to a circle around the point

These can be deferred since:
- The orbifold points (i, ρ) are the critical cases
- Interior points can use a direct argument if needed

---

## Detailed Proof for valenceFormula_identity_base

The main theorem needs to prove:
```lean
∑ p ∈ S, (windingNumberCoeff' p : ℂ) * (orderOfVanishingAt' f p : ℂ) =
(k : ℂ) / 12 - (orderAtCusp' f : ℂ)
```

### Required Results and Their Status:

| Result | Status | Where |
|--------|--------|-------|
| `generalizedResidueTheorem'` | ✅ | ResidueTheory.lean:5573 |
| `logDeriv_residue_eq_order` | ✅ | ValenceFormula.lean:5265 |
| `vertical_edges_cancel` | ✅ | ValenceFormula.lean:5446 |
| `arc_contribution_is_k_div_12` | ✅ | ValenceFormula.lean:5554 |
| `contour_decomposition` | ✅ | ValenceFormula.lean:5037 |
| Winding at i = 1/2 | 🔶 needs orientation sorry | line 3547 |
| Winding at ρ = 1/6 | 🔶 needs orientation sorry | line 3608 |
| Winding at ρ' = 1/6 | 🔶 needs orientation sorry | line 3677 |
| Cusp Tendsto | 🔶 commented out | line 5593 |

### Proof Outline:

```lean
theorem valenceFormula_identity_base ... := by
  apply valence_formula_from_contour_equality
  -- Goal: 2πi × Σ(coeff × order) = 2πi × (k/12 - ord_∞)

  -- Step 1: The LHS equals the PV contour integral by residue theorem
  have h_residue := generalizedResidueTheorem' ...
  -- PV ∮ f'/f = 2πi × Σ (winding × residue)

  -- Step 2: residue of f'/f = order
  have h_res_order := logDeriv_residue_eq_order ...

  -- Step 3: winding = orbifold coefficient
  have h_wind_i := generalizedWindingNumber_at_i_eq_half -- needs orientation
  have h_wind_rho := generalizedWindingNumber_at_rho_eq_sixth -- needs orientation
  have h_wind_rho' := generalizedWindingNumber_at_rho'_eq_sixth -- needs orientation
  -- Total at ρ-class: 1/6 + 1/6 = 1/3

  -- Step 4: The RHS equals the same contour integral by modular transformation
  have h_vert := vertical_edges_cancel f
  have h_arc := arc_contribution_is_k_div_12 f
  have h_cusp := cusp_contribution f -- or use contour_decomposition

  -- Step 5: Equate
  -- LHS = PV ∮ f'/f = 2πi × Σ(coeff × order)
  -- RHS = PV ∮ f'/f = 2πi × (k/12 - ord_∞)
  -- Therefore LHS = RHS
  ...
```

---

## Action Items (Prioritized)

### Immediate (Unblocks Main Theorem):

1. **Fill line 3547**: Use `exact orientation_at_i_strict` (already proved!)

2. **Fill line 3608**: Prove `orientation_at_rho_strict`
   - Similar calculation to `orientation_at_i_strict`
   - For corner at t=3 between arc and vertical segments

3. **Fill line 3677**: Prove `orientation_at_rho'_strict`
   - Similar to ρ, for corner at t=1

4. **Fill line 4014**: Connect the infrastructure
   - Use `generalizedResidueTheorem'` for LHS
   - Use modular transformation results for RHS
   - Show equality via same contour integral

### Secondary (Complete the formalization):

5. Fill homotopy sorries (1879, 1938, 1945, 1949) for interior winding = 1

6. Fill WindingNumber.lean sorries (2355, 2720) for H-W 2.3

7. Fill PiecewiseHomotopy sorries (622, 643) for continuity

---

## Mathematical Summary

The valence formula proof combines two computations of ∮_{∂𝒟} f'/f:

**Residue Theorem**:
∮ f'/f = 2πi × Σ (winding × residue) = 2πi × Σ (orbifold_coeff × order)

**Modular Transformation**:
∮ f'/f = 0 (vertical) + 2πi×k/12 (arc) - 2πi×ord_∞ (cusp)

**Equality**: Both = same integral ⟹ Σ (coeff × order) = k/12 - ord_∞

The orbifold coefficients 1, 1/2, 1/3 arise from stabilizer orders and equal the H-W winding number sums at each point.

---

## Files to Modify

1. `ValenceFormula.lean`:
   - Line 3547: exact orientation_at_i_strict
   - Lines 3608, 3677: Add orientation helpers for ρ, ρ'
   - Line 4014: Main proof connecting infrastructure

2. Optionally:
   - `WindingNumber.lean`: H-W 2.3 sorries
   - `PiecewiseHomotopy.lean`: Homotopy continuity
   - `PiecewiseHomotopyHelpers.lean`: Derivative bounds
