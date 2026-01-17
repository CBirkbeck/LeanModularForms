# Claude Code Instructions for LeanModularForms

## Lean 4 Proof Guidelines

### Forbidden Tactics
- **NEVER use `native_decide`** - This tactic uses kernel computation which can be slow, may fail unexpectedly, and produces non-portable proofs. Use `decide`, `simp`, `norm_num`, or explicit proofs instead.
- **NEVER use `sorry` to replace working code** - Only use `sorry` as a placeholder for incomplete proofs.

### Preferred Tactics
- Use `simp`, `ring`, `norm_num`, `linarith`, `nlinarith`, `omega` for automation
- Use `exact`, `apply`, `refine` for explicit proof steps
- Use `decide` (not `native_decide`) for decidable propositions when needed

### Code Style
- Use proper Lean 4 syntax (not Lean 3):
  - `∀ t ∈ S` not `forall t in S`
  - `∃ x, P x` not `exists x, P x`
  - `∧` not `and`, `∨` not `or`
  - `→` not `->`
  - `fun x => ...` not `λ x, ...`

### Axiom Safety
- Do not introduce custom axioms
- All proofs should use only standard mathlib axioms
- Run `/check-axioms` after filling sorries to verify

### Testing
- Always run `lake build` after making changes
- Check for errors, not just warnings
- Verify sorry count hasn't increased unexpectedly

## Project Structure

The valence formula proof is in `LeanModularForms/Modularforms/valence/`:
- `ComplexAnalysis/Basic.lean` - Core definitions (no sorries)
- `ComplexAnalysis/Finiteness.lean` - Finiteness results (no sorries)
- `ComplexAnalysis/PrincipalValue.lean` - Cauchy principal value theory
- `ComplexAnalysis/WindingNumber.lean` - Generalized winding numbers
- `ComplexAnalysis/AsymptoticEstimates.lean` - Big-O estimates
- `ComplexAnalysis/HomotopyBridge.lean` - Homotopy invariance
- `ComplexAnalysis/ResidueTheory.lean` - Residue computations
- `ComplexAnalysis/ValenceFormula.lean` - Main valence formula
- `GeneralizedResidueTheorem.lean` - Core theorem infrastructure

## Key Mathematical Concepts

The project uses **generalized winding numbers** via Cauchy principal values:
- Contours can pass through singularities
- At elliptic point i: winding number = 1/2 (smooth crossing)
- At elliptic point ρ: winding number = 1/3 (corner with angle 2π/3)

## Our Approach: Direct Winding Numbers (No Detoured Curves)

**IMPORTANT**: We use a direct approach that differs from Isabelle and some textbooks.

### The Direct Approach

Instead of constructing "detoured curves" that go around singularities, we compute
winding numbers directly using principal value integrals:

1. **Smooth crossing** (`generalizedWindingNumber_smooth_crossing'`):
   - When a C¹ curve passes through z₀ with nonzero derivative
   - Contribution: **1/2**
   - Used at: elliptic point i (t = 2 on boundary)

2. **Corner crossing** (`generalizedWindingNumber_corner_crossing'`):
   - When a piecewise C¹ curve has a corner at z₀ with angle α
   - Contribution: **α/(2π)**
   - Used at: elliptic point ρ (t = 3 on boundary, angle = 2π/3 → contribution 1/3)

3. **Classical case** (`generalizedWindingNumber_eq_classical_away`):
   - When curve avoids z₀, generalized = classical winding number
   - Used at: interior points (winding number = 1)

### Why Not Detoured Curves?

The traditional approach constructs an auxiliary curve γ̃ that:
- Coincides with γ away from singularities
- Detours around each singularity via small semicircular arcs

Then: `W(γ, z₀) = W(γ̃, z₀) + Σ angle_contributions`

**We skip this construction entirely.** The principal value definition already
captures the correct local contributions at each crossing point. This is:
- Simpler to formalize (no complex curve construction)
- More direct (compute contributions locally)
- Equivalent mathematically (same final answer)

### Fundamental Domain Boundary

The boundary is parameterized **counterclockwise** (positive orientation):
- t ∈ [0,1]: right vertical from (1/2 + Hi) down to ρ'
- t ∈ [1,2]: arc from ρ' to i (counterclockwise, angle π/3 → π/2)
- t ∈ [2,3]: arc from i to ρ (counterclockwise, angle π/2 → 2π/3)
- t ∈ [3,4]: left vertical from ρ up to (-1/2 + Hi)

This gives **positive** winding numbers: +1 interior, +1/2 at i, +1/3 at ρ.

## Comparing with Isabelle HOL-Complex_Analysis

When checking our approach against Isabelle's `HOL-Complex_Analysis` library:

### IGNORE These Parts in Isabelle
- **Detoured curve constructions** - Isabelle builds curves that avoid singularities
  by detouring around them. We handle singularities directly via principal values.
- **Wiggle relations** - Isabelle's `wiggle_rel` for paths near singularities
- **Homotopy arguments to avoid points** - We don't need curves to avoid points

### USE These Parts from Isabelle
- **Contour integral definitions** - Basic definitions are compatible
- **Residue calculations** - Core residue theory applies
- **Winding number properties** - Integer winding for closed curves avoiding point
- **Argument principle** - Standard form applies
- **Cauchy's theorem** - For regions where function is holomorphic

### Key Isabelle Files for Reference
- `Winding_Numbers.thy` - Winding number theory (adapt for our PV approach)
- `Contour_Integration.thy` - Contour integral properties
- `Complex_Residues.thy` - Residue definitions
- `Residue_Theorem.thy` - Classical residue theorem (we generalize this)

### Translation Notes
When translating Isabelle proofs:
1. If Isabelle requires curve to avoid a point, check if we can use PV instead
2. Replace detour constructions with direct local contribution calculations
3. Use `generalizedWindingNumber_smooth_crossing'` for smooth crossings
4. Use `generalizedWindingNumber_corner_crossing'` for corners
