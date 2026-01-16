# Plan for Proving Complex Analysis Results

## Overview

Our approach uses **generalized winding numbers via Cauchy principal values**, which allows contours to pass through singularities. This is simpler than the Isabelle approach which requires:
- Paths to avoid singularities
- Homotopy/wiggle relations to handle paths near singularities
- Careful construction of modified paths

**Key advantage**: Our principal value definition automatically handles the cancellation of singular terms, giving well-defined values even when the contour passes through a singularity.

## Phase 1: Core Principal Value Theory (No external dependencies)

### 1.1 Principal Value Existence for Simple Poles
**Goal**: Show `CauchyPrincipalValueExists f γ a b z₀` when f has a simple pole at z₀

**Approach**:
- For f(z) = c/(z - z₀) + g(z) where g is holomorphic:
- The PV integral splits: PV∮f = PV∮(c/(z-z₀)) + ∮g
- The second integral is standard (g is integrable)
- The first is handled by the model sector computation

**Key Lemma** (to prove):
```lean
lemma pv_exists_simple_pole (γ : PiecewiseC1Immersion') (z₀ : ℂ) (c : ℂ)
    (hγ : γ.toFun passes_through z₀ at_times T) :
    CauchyPrincipalValueExists (fun z => c / (z - z₀)) γ.toFun γ.a γ.b z₀
```

### 1.2 Model Sector Computation (Already partially done)
**Status**: `generalizedWindingNumber_modelSector` is proven

**What's needed**: Extract the computation to work for general curves approaching a point

### 1.3 Linearity of Principal Values
**Goal**: Show PV is linear in f when both limits exist

```lean
lemma cauchyPrincipalValue_add (h1 : CauchyPrincipalValueExists f γ a b z₀)
    (h2 : CauchyPrincipalValueExists g γ a b z₀) :
    cauchyPrincipalValue (f + g) γ a b z₀ =
    cauchyPrincipalValue f γ a b z₀ + cauchyPrincipalValue g γ a b z₀
```

## Phase 2: Winding Number Properties

### 2.1 Winding Number Decomposition
**Goal**: When a curve is split at points, winding numbers add

The key result `generalizedWindingNumber_decomposition` shows:
```
n_z(γ) = n_z(γ̃) + Σ_i α_i/(2π)
```
where γ̃ avoids z and α_i are the angles at intersection points.

**Approach**:
- This follows from additivity of integrals
- The model sector calculation gives the α/(2π) terms
- No homotopy theory needed!

### 2.2 Winding Number for Curves Avoiding a Point
**Goal**: When γ avoids z₀, the generalized winding number equals the classical one

```lean
lemma generalizedWindingNumber_eq_classical (γ : PiecewiseC1Curve')
    (hz : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    generalizedWindingNumber γ.toFun γ.a γ.b z₀ ∈ ℤ
```

**Approach**:
- When z₀ is not on γ, the ε-exclusion has no effect for small ε
- The integral is just the standard contour integral
- Use mathlib's `Complex.winding_number` or derive from first principles

## Phase 3: Residue Theory

### 3.1 Residue Definition (Already done)
We define residue via Laurent series coefficient:
```lean
def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  (laurentExpansionAt f z₀).coeff (-1)
```

### 3.2 Residue Integral Formula
**Goal**: For a simple pole, PV∮f = 2πi · n_z(γ) · res_z(f)

**Key Computation**:
For f(z) = c/(z - z₀) near z₀:
- res_z(f) = c
- PV∮(c/(z-z₀)) = c · PV∮(1/(z-z₀)) = c · 2πi · n_z(γ)

This is essentially the model sector calculation applied to general curves.

### 3.3 Holomorphic Function Contribution
**Goal**: If f is holomorphic at z₀ and z₀ is on γ, then PV∮f near z₀ contributes 0 to the residue sum

**Approach**: The singular part is 0, so no principal value issues arise.

## Phase 4: The Generalized Residue Theorem

### 4.1 Theorem Statement
```lean
theorem generalizedResidueTheorem
    (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_discrete : S.Countable ∧ ∀ s ∈ S, ¬ AccPt s S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S))
    (γ : PiecewiseC1Curve') (hγ_closed : γ.IsClosed)
    (hγ_in_U : ∀ t, γ.toFun t ∈ U)
    (hSimplePoles : ∀ s ∈ S ∩ γ.image, is_simple_pole f s) :
    PV (1/2πi) ∮_γ f = Σ_{s ∈ S} n_s(γ) · res_s(f)
```

### 4.2 Proof Strategy (Simplified by PV approach)

**Step 1**: Identify singularities on γ
- S ∩ γ([a,b]) is finite (discrete set intersecting compact set)
- Let {s₁, ..., sₙ} be these points

**Step 2**: Decompose the integral
- Split [a,b] into subintervals around each sᵢ
- On each subinterval, f = (singular part) + (holomorphic part)

**Step 3**: Handle holomorphic parts
- Away from singularities, use standard integration
- Mathlib's `DifferentiableOn.contourIntegral` handles this

**Step 4**: Handle singular parts
- Each (c/(z - sᵢ)) contributes PV∮(c/(z-sᵢ)) = 2πi · n_{sᵢ}(γ) · c
- This is the model sector calculation

**Step 5**: Combine
- Sum over all singularities
- The winding number decomposition ensures correct counting

## Phase 5: Infrastructure Lemmas Needed

### 5.1 Finiteness Results (Partially done)
- ✅ `zeros_uniformly_separated` - proven
- ✅ `zeros_finite_on_interval` - proven
- ❌ `piecewiseC1Immersion_finite_zeros` - has gaps (see below)

**Gap Analysis**: The finiteness proof has issues when γ' → 0 at partition points.

**Solution**: Add assumption that one-sided limits of γ' at partition points are nonzero:
```lean
structure PiecewiseC1Immersion' extends PiecewiseC1Curve' where
  deriv_ne_zero : ∀ t ∈ Icc a b, t ∉ partition → deriv toFun t ≠ 0
  -- NEW: One-sided limits at partition points are nonzero
  left_deriv_ne_zero : ∀ p ∈ partition, p > a →
    ∃ L ≠ 0, Tendsto (deriv toFun) (𝓝[<] p) (𝓝 L)
  right_deriv_ne_zero : ∀ p ∈ partition, p < b →
    ∃ L ≠ 0, Tendsto (deriv toFun) (𝓝[>] p) (𝓝 L)
```

### 5.2 Integral Manipulations
Need from mathlib:
- `intervalIntegral.integral_add` - additivity
- `intervalIntegral.integral_sub` - subtraction
- `intervalIntegral.integral_comp_mul_right` - substitution
- `Complex.integral_boundary_rect_eq_zero_of_differentiableOn` - Cauchy for rectangles

### 5.3 Limit Theorems
Need:
- Dominated convergence for PV limits
- Interchanging limits and integrals

## Phase 6: Avoiding Isabelle's Complexity

### What we DON'T need (thanks to PV approach):

1. **Homotopy Theory**: Isabelle uses `homotopic_loops` extensively. We don't need this because:
   - Our PV definition handles singularities on the contour directly
   - The model sector computation gives the contribution without path deformation

2. **Wiggle Relations**: Isabelle needs careful arguments about paths "almost" avoiding points. We don't need this because:
   - PV automatically excludes ε-neighborhoods
   - The limit as ε → 0 handles the "wiggling"

3. **Path Avoidance Constructions**: Isabelle constructs modified paths avoiding singularities. We only need this conceptually (for understanding), not formally.

4. **Index Theory**: The classical winding number ∈ ℤ requirement is relaxed to ∈ ℂ in our framework.

### What we DO need:

1. **Model Sector Computation**: The core calculation that α/(2π) emerges from the PV integral (✅ done)

2. **Integral Splitting**: Ability to split integrals at points where γ passes through singularities

3. **Dominated Convergence**: To interchange limits and integrals in PV definition

4. **Basic Complex Analysis**:
   - Cauchy's integral formula (from mathlib)
   - Laurent series (from mathlib)
   - Residue basics (partially from mathlib)

## Recommended Implementation Order

### Immediate (can do now):
1. Strengthen `PiecewiseC1Immersion'` with one-sided derivative limits
2. Fix `piecewiseC1Immersion_finite_zeros` with the new structure
3. Prove `cauchyPrincipalValue_add` (linearity)

### Short term:
4. Prove `pv_exists_simple_pole`
5. Prove `generalizedWindingNumber_decomposition`
6. Prove `generalizedWindingNumber_eq_classical`

### Medium term:
7. Prove the generalized residue theorem for simple poles
8. Handle the special cases (flatness conditions) for higher order poles

### Final:
9. Apply to valence formula
10. Derive classical corollaries (zeppelin curve example, etc.)

## Dependencies on Mathlib

**Required** (should be available):
- `Mathlib.Analysis.Complex.CauchyIntegral` - basic Cauchy theory
- `Mathlib.Analysis.Calculus.ContDiff` - smooth functions
- `Mathlib.MeasureTheory.Integral.IntervalIntegral` - interval integrals
- `Mathlib.Analysis.SpecialFunctions.Complex.Log` - complex logarithm
- `Mathlib.RingTheory.LaurentSeries` - Laurent series

**Might need to develop**:
- Principal value limit theorems (dominated convergence for PV)
- Specific angle calculations for model sectors
