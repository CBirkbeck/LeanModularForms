# Viazovska Contour Equivalence Plan

## Goal
Prove: `∫_{-1→i} F(z) dz = ∫_{-1→-1+i} F(z) dz + ∫_{-1+i→i} F(z) dz`

where `F(z) = φ₀''(-1/(z+1)) · (z+1)² · e^{πirz}`.

## The Real-Axis Issue

The contour from -1 to i starts at z = -1 on the real line where:
- Im(z) = 0, so z ∉ ℍ (upper half-plane)
- φ₀ is only defined on ℍ (Δ = 0 at cusps)
- But (z+1)² = 0 cancels the cusp singularity → F(-1) = 0

## Strategy: Limit Approach (Phase A)

### Step 1: Truncated contour equivalence
For δ > 0, let z_δ = -1 + δ(1+i) (point on the diagonal, Im = δ > 0).
Prove the equivalence for truncated contours starting at z_δ instead of -1:
```
∫_{z_δ → i} F dz = ∫_{z_δ → -1+i} F dz + ∫_{-1+i → i} F dz
```
This holds by Cauchy on the convex set {Im(z) > δ/2} where F is holomorphic.

### Step 2: Take δ → 0
Show all three integrals converge as δ → 0:
- |F(z)| → 0 as z → -1 (cusp cancellation)
- The truncated integrals approach the full integrals
- Use dominated convergence or direct continuity

### Step 3: Conclude
The identity passes to the limit.

## Key Lemmas Needed

### From modular forms (Eisenstein.lean, Delta.lean):
1. `Δ_ne_zero`: Δ(z) ≠ 0 for z ∈ ℍ (already proven)
2. `φ₀_holomorphic`: DifferentiableOn ℂ φ₀'' {z | 0 < z.im} (needs proof)
3. `φ₀_cusp_decay`: φ₀(w) = O(e^{-2π·Im(w)}) as Im(w) → ∞ (needs proof)
4. Cusp cancellation: φ₀(-1/(z+1))·(z+1)² → 0 as z → -1 (from 3)

### From GeneralizedResidueTheory:
5. `holomorphic_convex_primitive` (CauchyPrimitive.lean) — primitive on convex domain
6. Standard FTC for line-segment integrals

## Implementation Order

1. Prove φ₀'' is DifferentiableOn the upper half-plane
2. Prove the cusp cancellation (F → 0 at z = -1)
3. Define truncated contours
4. Prove truncated equivalence via FTC on convex domain
5. Take limit δ → 0
6. Repeat for 1→i and 0→i contours

## Files
- `SpherePacking/ViazovskaMagicFunction.lean` — definitions (done)
- `SpherePacking/ContourEquivalence.lean` — the proof (to create)
- May need `SpherePacking/PhiHolomorphic.lean` — holomorphicity of φ₀
