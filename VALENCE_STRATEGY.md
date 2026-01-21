# Strategy for Proving the Valence Formula in Lean

## Overview

This document outlines the strategy for completing the proof of the valence formula
for modular forms. The approach uses **orbifold coefficients** from the quotient
structure of ℍ/PSL₂(ℤ), combined with contour integration via Cauchy principal values.

**IMPORTANT CORRECTION**: The valence formula coefficients 1/2 at i and 1/3 at ρ
are ORBIFOLD coefficients (= 1/stabilizer order), NOT geometric winding numbers.

| Point    | Stabilizer                   | Order | Coefficient |
|----------|------------------------------|-------|-------------|
| Interior | {±I}                         | 1     | 1           |
| i        | ⟨S⟩ where S: z ↦ -1/z        | 2     | 1/2         |
| ρ        | ⟨ST⟩ where ST: z ↦ -1/(z+1)  | 3     | 1/3         |

The Hungerbühler-Wasem paper's geometric winding numbers happen to coincide at i
(smooth crossing → angle π → 1/2) but NOT at ρ (corner angle π/3 → 1/6 ≠ 1/3).

## Current State Summary

### Completed Components (No Sorries)
1. **Basic Definitions** (`ComplexAnalysis/Basic.lean`) - Core data structures for:
   - `PiecewiseC1Curve` and `PiecewiseC1Immersion`
   - Cauchy principal value definitions
   - Generalized winding number definition
   - Model sector curve structure

2. **Finiteness Results** (`ComplexAnalysis/Finiteness.lean`) - Proven:
   - Zeros of immersions are isolated and finite on compact intervals
   - `piecewiseC1Immersion_finite_zeros`

### Components with Sorries (Updated 2026-01-21)

| File | Sorries | Category | Notes |
|------|---------|----------|-------|
| `PrincipalValue.lean` | 5 | Core PV theory | |
| `HomotopyBridge.lean` | 1 | Homotopy invariance | |
| `AsymptoticEstimates.lean` | 2 | Boundedness proofs | |
| `WindingNumber.lean` | 3 | Winding number properties | |
| `ResidueTheory.lean` | 4 | Residue computation | **Reduced from 10** - Case 2 structured |
| `ValenceFormula.lean` | 10 | Main application | |
| `Infrastructure/CauchyTheorem.lean` | 4 | FTC/Cauchy infrastructure | |

## Mathematical Strategy

### Key Insight

The valence formula coefficients come from the **orbifold structure** of the modular
curve, not from geometric winding numbers:

- **w_i = 1/2** = 1/(stabilizer order at i) = 1/2
- **w_ρ = 1/3** = 1/(stabilizer order at ρ) = 1/3

The proof uses contour integration of f'/f along ∂𝒟, where the transformation
formula for modular forms determines the total contribution, and the orbifold
structure determines how that contribution is distributed among points.

### Critical Path Analysis

```
1. Model Sector Calculation [DONE]
   └── generalizedWindingNumber_modelSector' proves α/(2π) contribution

2. Finiteness of Zeros [DONE]
   └── piecewiseC1Immersion_finite_zeros

3. PV Integral Existence [5 sorries]
   ├── cauchyPrincipalValueIntegrand_integrable (line 164)
   ├── cauchyPrincipalValueExists_of_simple_pole (line 214)
   ├── cauchyPrincipalValue_add' (line 248) - needs integrability
   ├── homotopy_pv_integral_eq' (line 376) - KEY
   └── cauchyPrincipalValue_of_dominated (line 507)

4. Homotopy Invariance [1 sorry]
   └── HomotopyBridge.lean line ~1845
       Uses constant_of_hasDerivAt_zero for parametric Cauchy

5. Asymptotic Estimates [2 sorries]
   ├── numerator_big_O_squared (line 136) - Taylor expansion
   └── windingNumberIntegrand_limit_at_zero (line 629) - C² limit

6. Winding Number Properties [3 sorries]
   ├── generalizedWindingNumber_eq_classical' (line 235)
   ├── generalizedWindingNumber_decomposition' (line 307)
   └── cauchyPrincipalValue_split (line 379) - integrability gap

7. Residue Theory [10 sorries]
   ├── residue_eq_contour_integral (line 137)
   ├── residue_smul edge case (line 217)
   ├── pv_integral_simple_pole (line 333)
   ├── residue_of_simple_pole (line 350)
   └── generalizedResidueTheorem' (lines 396, 405, 415)

8. Valence Formula [8 sorries] (updated - removed deprecated winding number theorems)
   ├── Boundary curve continuity/smoothness
   ├── orbifoldCoeff_at_i, orbifoldCoeff_at_rho - defined via stabilizer orders (DONE)
   ├── windingNumber_boundary_interior (line 293)
   ├── orderOfVanishingAt_nonneg (line 324)
   ├── valenceFormula' (line 375)
   ├── valenceFormula_classical' (line 402)
   └── valenceFormula_weight_zero_constant' (line 578)
```

## Recommended Approach

### Phase 1: Foundation Solidification (Priority: HIGH)

**Goal**: Establish integrability and PV existence for simple poles

1. **`cauchyPrincipalValueIntegrand_integrable`** (PrincipalValue.lean:164)
   - Bound is already proven in `cauchyPrincipalValueIntegrand_bounded`
   - Need AEStronglyMeasurable for piecewise indicator function
   - Use `MeasureTheory.Integrable.mono'` with uniform bound

2. **`cauchyPrincipalValueExists_of_simple_pole`** (PrincipalValue.lean:214)
   - Split into regular (continuous) and singular (1/(z-z₀)) parts
   - Regular part: standard integral exists
   - Singular part: use model sector calculation

3. **`cauchyPrincipalValue_add'`** (PrincipalValue.lean:248)
   - Needs `intervalIntegral.integral_add`
   - Gap is showing integrability of piecewise indicator functions

### Phase 2: Homotopy Bridge (Priority: HIGH)

**Goal**: Connect to mathlib's Cauchy integral theory

1. **`homotopy_pv_integral_eq'`** (PrincipalValue.lean:376)
   - Define F(s) = PV integral along H(·, s)
   - Show F continuous via dominated convergence
   - Show F locally constant via Cauchy's theorem
   - Conclude F(0) = F(1) on connected [0,1]

2. **HomotopyBridge.lean line ~1845**
   - The sorry is documented as "standard mathematical argument"
   - Uses parametric differentiation under integral sign
   - Bounded uniform convergence + FTC

### Phase 3: Asymptotic Estimates (Priority: MEDIUM)

1. **`numerator_big_O_squared`** (AsymptoticEstimates.lean:136)
   - Taylor expansion with Lipschitz derivative
   - Key: x*y' - y*x' has O(h²) via cancellation of vx*vy - vy*vx = 0
   - Most of proof already done, just needs FTC integration

2. **`windingNumberIntegrand_limit_at_zero`** (AsymptoticEstimates.lean:629)
   - C² Taylor expansion to second order
   - Limit involves signed curvature
   - Standard calculus, needs Taylor remainder bounds

### Phase 4: Winding Number Theory (Priority: MEDIUM)

1. **`generalizedWindingNumber_eq_classical'`** (WindingNumber.lean:235)
   - For closed curve avoiding z₀, show winding number ∈ ℤ
   - Use `integral_closed_curve_eq_two_pi_int` from HomotopyBridge
   - Gap: extend to piecewise C¹ curves (split at partition points)

2. **`generalizedWindingNumber_decomposition'`** (WindingNumber.lean:307)
   - Main decomposition: n_{z₀}(γ) = n_{z₀}(γ̃) + Σᵢ αᵢ/(2π)
   - Construct γ̃ by detouring around z₀ at each intersection
   - Use homotopy invariance + model sector calculation

### Phase 5: Residue Theory (Priority: MEDIUM)

1. **`pv_integral_simple_pole`** (ResidueTheory.lean:333)
   - PV ∮ c/(z-z₀) = 2πi · n_{z₀}(γ) · c
   - Follows from `pv_integral_inverse` with scalar multiplication

2. **`generalizedResidueTheorem'`** (ResidueTheory.lean:396-415)
   - Decompose f = Σ (singular parts) + holomorphic
   - Apply PV linearity and Cauchy's theorem for regular part
   - Sum residue contributions

### Phase 6: Valence Formula (Priority: HIGH but DEPENDENT)

1. **Boundary curve properties** (ValenceFormula.lean:165-183)
   - Show `fundamentalDomainBoundary` is continuous/smooth
   - Each piece is polynomial or exp of linear function
   - Standard continuity arguments

2. **Orbifold coefficients at special points** (ValenceFormula.lean)
   - Use stabilizer structure of PSL₂(ℤ)
   - At i: stabilizer ⟨S⟩ has order 2 → coefficient = 1/2
   - At ρ: stabilizer ⟨ST⟩ has order 3 → coefficient = 1/3
   - Interior: trivial stabilizer → coefficient = 1

3. **Main valence formula** (ValenceFormula.lean:375-402)
   - Apply generalized residue theorem to f'/f
   - Handle cusp contribution via q-expansion
   - Use modular transformation formula

## Weakening Assumptions

Since the final goal is the valence formula, we can simplify:

1. **Regularity**: We only need piecewise C¹ curves for the fundamental domain boundary (which is piecewise smooth anyway)

2. **Homotopy**: We only need homotopy invariance for curves in the upper half-plane avoiding specific singularities

3. **Residue theory**: We only need simple poles (which is what f'/f has at zeros/poles of f)

4. **Winding numbers**: We only need integer winding numbers away from the boundary, and the specific values 1/2, 1/3 at elliptic points

## Axiom Safety

The project currently avoids nonstandard axioms. All sorries should be filled using:
- Standard mathlib tactics (`simp`, `ring`, `norm_num`, `linarith`, `nlinarith`)
- Mathlib's integration theory (`MeasureTheory`)
- Mathlib's complex analysis (`Complex`, `circleIntegral`)
- Mathlib's differential topology (`ContDiff`, `HasDerivAt`)

**Do NOT introduce**:
- `Classical.axiomOfChoice` beyond what mathlib uses
- Custom axioms for integration or limits
- `sorry` replacements that use `Decidable` instances incorrectly

## Implementation Order

1. **Immediate**: PrincipalValue integrability (foundation for everything)
2. **Next**: Homotopy bridge (enables winding number decomposition)
3. **Then**: Winding number decomposition (enables valence formula)
4. **Finally**: Valence formula application

## Files to Focus On

1. `ComplexAnalysis/PrincipalValue.lean` - 5 sorries, foundational
2. `ComplexAnalysis/HomotopyBridge.lean` - 1 sorry, critical
3. `ComplexAnalysis/WindingNumber.lean` - 3 sorries, bridges to valence
4. `ComplexAnalysis/ValenceFormula.lean` - 8 sorries (reduced), final goal

## Testing Strategy

After each sorry is filled:
1. Run `lake build` to check compilation
2. Check for unused variables or suspicious patterns
3. Verify no new axioms introduced with `/check-axioms`
4. Run profile on complex theorems if elaboration is slow

## Notes on Specific Sorries

### Most Tractable (Quick Wins)
- `cauchyPrincipalValueIntegrand_integrable`: Just needs measurability + bounded
- `cauchyPrincipalValue_add'`: Limit algebra, gap is integrability
- Boundary curve continuity: Standard if-then-else continuity

### Most Difficult
- `homotopy_pv_integral_eq'`: Core Cauchy-Goursat argument
- `generalizedWindingNumber_decomposition'`: Substantial construction
- `generalizedResidueTheorem'`: Combines everything

### Potentially Droppable
- `residue_smul` edge case: Only matters when limit doesn't exist (not our case)
- `windingNumberIntegrand_limit_at_zero`: Only needed for C² curves (not critical path)

## Changelog

### 2026-01-21: Case 2 Proof Structure for generalizedResidueTheorem'

**MAJOR PROGRESS**: Completed the proof structure for Case 2 of `generalizedResidueTheorem'`
(curve passes through singularities).

**Filled completely**:
- `hg_integral_zero`: Cauchy theorem for piecewise C1 curves
  - Uses `holomorphic_convex_primitive` to get primitive F of g on convex U
  - Applies FTC with countable exceptions via `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`
  - Uses closedness of γ to conclude F(γ(b)) - F(γ(a)) = 0

**Restructured with documentation**:
- `h_single_pole_formula`: Case split on residue = 0
  - Case 1 (c_s = 0): Both sides are 0, proved directly
  - Case 2 (c_s ≠ 0): Uses scalar factor extraction from hPV_singular

**Remaining sorries (well-documented)**:
1. **Line 1804**: Piecewise measurability for AEStronglyMeasurable
2. **Line 2243**: Multi-point PV existence (`cauchyPrincipalValueOn_singular_sum`)
3. **Line 2595**: Scalar factor extraction: if `c * f → L` and `c ≠ 0`, then `f → L/c`
4. **Line 2650**: Multi-point PV decomposition for separated singularities

**Key insight**: All remaining sorries are infrastructure for standard limit/integral arithmetic:
- Tendsto and scalar multiplication (limit algebra)
- PV decomposition for disjoint balls (separated singularities)
- Piecewise measurability (standard measure theory)

**Tomorrow's plan**:
1. Fill scalar factor extraction (use `Tendsto.const_mul` with c⁻¹)
2. Fill multi-point PV decomposition (use Finset.sum + disjoint ball analysis)
3. Attack `cauchyPrincipalValueOn_singular_sum` existence
4. Consider weakening assumptions if proofs get stuck

### 2026-01-20: Orbifold Coefficient Correction

**CRITICAL FIX**: The valence formula coefficients at elliptic points are NOT
geometric winding numbers from Hungerbühler-Wasem theory. They are **orbifold
coefficients** from the stabilizer structure:

- **At i**: Coefficient = 1/2 = 1/(stabilizer order). The H-W winding number
  happens to also be 1/2 (smooth crossing, angle π → π/(2π) = 1/2), but this
  is a coincidence.

- **At ρ**: Coefficient = 1/3 = 1/(stabilizer order). The H-W winding number
  is 1/6 (corner angle π/3 → π/3/(2π) = 1/6), which is DIFFERENT.

The incorrect claim that "angle 2π/3 at ρ gives 1/3" was based on a misunderstanding.
The geometric angle at ρ is π/3, not 2π/3.

**Changes made**:
1. Removed deprecated theorems `windingNumber_boundary_at_i`, `windingNumber_boundary_at_rho`
2. Added `orbifoldCoeff_at_i`, `orbifoldCoeff_at_rho` definitions
3. Updated all docstrings to clarify orbifold vs geometric distinction
4. Updated `CLAUDE.md` with correct mathematical explanation
