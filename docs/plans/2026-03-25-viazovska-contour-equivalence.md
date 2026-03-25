# Viazovska Contour Equivalence Plan

## Goal
Prove: `∫_{-1→i} F(z) dz = ∫_{-1→-1+i} F(z) dz + ∫_{-1+i→i} F(z) dz`

where `F(z) = φ₀''(-1/(z+1)) · (z+1)² · e^{πirz}`.

## The Real-Axis Issue

The contour from -1 to i starts at z = -1 on the real line where:
- Im(z) = 0, so z ∉ ℍ (upper half-plane)
- φ₀ is only defined on ℍ (Δ = 0 at cusps)
- But (z+1)² = 0 cancels the cusp singularity → F(-1) = 0

## Key Prerequisite: Holomorphicity of φ₀

### The E₂ problem
E₂ is quasi-modular (not a modular form), so `ModularFormClass` doesn't give
holomorphicity. But we don't need E₂ alone — only the combination E₂·E₄ - E₆.

### Ramanujan's formula (THE KEY)
```
E₂·E₄ - E₆ = 3·D(E₄)
```
where D is the Serre derivative. Since E₄ is a modular form (holomorphic on ℍ),
D(E₄) is holomorphic. Therefore E₂·E₄ - E₆ is holomorphic, and
φ₀ = (E₂·E₄ - E₆)² / Δ is holomorphic on ℍ (since Δ ≠ 0 on ℍ).

### Status
- `E₂_mul_E₄_sub_E₆` (q-expansion) — STATED but sorry'd in Eisenstein.lean:733
- `ramanujan_E₄` (E₂·E₄ - E₆ = 3·D(E₄)) — NOT in our codebase
- Serre derivative `D` — NOT in our codebase
- Sphere-Packing-Lean has all of this (different Lean version, can't import)

### Options
A. Port Ramanujan formula from sphere packing (needs Serre derivative D)
B. Prove holomorphicity of E₂·E₄ - E₆ directly from q-expansion convergence
C. Axiomatize: assume φ₀ is holomorphic on ℍ as a hypothesis

## Strategy: Limit Approach (Phase A)

### Step 0: Prove/assume holomorphicity of φ₀ on ℍ
Either prove via Ramanujan or take as hypothesis.

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

## Implementation Order

1. **Port Serre derivative D and Ramanujan formula** (or axiomatize φ₀ holomorphicity)
2. Prove φ₀'' is DifferentiableOn the upper half-plane
3. Prove the cusp cancellation (F → 0 at z = -1)
4. Define truncated contours
5. Prove truncated equivalence via FTC on convex domain
6. Take limit δ → 0
7. Repeat for 1→i and 0→i contours

## Files
- `SpherePacking/ViazovskaMagicFunction.lean` — definitions (done)
- `SpherePacking/ContourEquivalence.lean` — the proof (to create)
- `SpherePacking/PhiHolomorphic.lean` — holomorphicity of φ₀ (to create)
- `Modularforms/SerreDeriv.lean` — Serre derivative D (to create, or port)
