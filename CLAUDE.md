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

### The Valence Formula

For a nonzero modular form f of weight k for SL₂(ℤ):

```
ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{p ∈ 𝒟°} ord_p(f) = k/12
```

### Orbifold Coefficients (NOT Winding Numbers!)

**CRITICAL**: The coefficients 1/2 at i and 1/3 at ρ come from the **orbifold structure**
of the modular curve ℍ/SL₂(ℤ), NOT from geometric winding numbers.

#### Why Winding Numbers Don't Work

The Hungerbühler-Wasem paper defines generalized winding numbers via Cauchy PV:
```
n_{z₀}(γ) = PV (1/2πi) ∮_γ dz/(z-z₀) = α/(2π)
```
where α is the angle from outgoing tangent to -incoming tangent.

However, at ρ on ∂𝒟:
- The geometric angle is **π/3** (or 5π/3 depending on convention)
- This gives **1/6** or **5/6**, NOT 1/3!
- The valence formula requires **1/3**

At i, the H-W formula happens to give 1/2 (smooth crossing, angle = π), but this
is a **coincidence** — the orbifold coefficient would still be 1/2 regardless of
the curve geometry.

#### The Orbifold Structure

The quotient ℍ/SL₂(ℤ) is an orbifold with:

| Point | Stabilizer | Order | Valence Coefficient |
|-------|------------|-------|---------------------|
| Interior | {±I} | 1 | 1 |
| i | ⟨S⟩ where S: z ↦ -1/z | 2 | 1/2 |
| ρ | ⟨ST⟩ where ST: z ↦ -1/(z+1) | 3 | 1/3 |

The coefficient at p is **1/(order of stabilizer at p)**.

### What the PV/Winding Number Approach IS Good For

The Hungerbühler-Wasem PV approach is still useful for:
- **Interior points**: winding number = 1 (classical case, curve avoids point)
- **Residue calculations**: PV integrals of meromorphic functions
- **General complex analysis**: curves passing through singularities

But for the **valence formula coefficients at elliptic points**, use:
- `orbifoldCoeff_at_i = 1/2` (stabilizer order 2)
- `orbifoldCoeff_at_rho = 1/3` (stabilizer order 3)

### Fundamental Domain Boundary

The boundary is parameterized **counterclockwise** (positive orientation):
- t ∈ [0,1]: right vertical from (1/2 + Hi) down to ρ'
- t ∈ [1,2]: arc from ρ' to i (counterclockwise, angle π/3 → π/2)
- t ∈ [2,3]: arc from i to ρ (counterclockwise, angle π/2 → 2π/3)
- t ∈ [3,4]: left vertical from ρ up to (-1/2 + Hi)

For interior points: classical winding number = +1.
For elliptic points: use **orbifold coefficients** (1/2 at i, 1/3 at ρ).

## Comparing with Isabelle HOL-Complex_Analysis

When checking our approach against Isabelle's `HOL-Complex_Analysis` library:

### USE These Parts from Isabelle
- **Contour integral definitions** - Basic definitions are compatible
- **Residue calculations** - Core residue theory applies
- **Winding number properties** - Integer winding for closed curves avoiding point
- **Argument principle** - Standard form applies
- **Cauchy's theorem** - For regions where function is holomorphic
- **Detoured curve constructions** - For computing residue contributions

### Key Isabelle Files for Reference
- `Winding_Numbers.thy` - Winding number theory
- `Contour_Integration.thy` - Contour integral properties
- `Complex_Residues.thy` - Residue definitions
- `Residue_Theorem.thy` - Classical residue theorem

### Translation Notes
When translating Isabelle proofs:
1. For **interior points**: use classical winding number theory
2. For **elliptic points**: use orbifold coefficients directly (don't try to derive from geometry)
3. The detoured curve approach IS mathematically valid, but the orbifold coefficient approach
   is more direct for the valence formula

## Working on Sorry Elimination

### Persistence Rule
When the user approves work on a file or sorry, **continue working until that file/theorem is completely sorry-free**. Do not stop after partial progress. Keep iterating until:
- All sorries in the approved scope are eliminated
- Or you encounter a fundamental obstacle that requires user input

### Breaking Down Complex Proofs
When a lemma is too complex to prove directly:
1. **Identify the key sub-goals** - What are the main mathematical steps?
2. **Create helper lemmas** - Break the proof into smaller, provable pieces
3. **Prove the helpers first** - Start with the simplest/most foundational
4. **Combine helpers** - Use the proven helpers to complete the main result
5. **Keep helpers sorry-free** - Don't just move sorries to helper lemmas

### Verifying Theorem Statements
Before filling a sorry, **always verify the theorem statement is correct**:
1. Check that hypotheses are sufficient for the conclusion
2. Check that the statement matches the mathematical intent
3. Look for missing hypotheses that would make the proof possible
4. If a statement is wrong or missing hypotheses:
   - **Fix it** if the fix is straightforward
   - **Add hypotheses** if needed (ensuring we can still prove the valence formula)
   - **Document the change** in comments

### Common Issues to Check
- Missing boundedness/continuity hypotheses
- Wrong direction of inequalities
- Missing non-degeneracy conditions (e.g., `a < b`, `L ≠ 0`)
- Incorrect filter directions (e.g., `𝓝[>] 0` vs `𝓝[<] 0`)
- Type mismatches between `PiecewiseC1Curve` and `PiecewiseC1Immersion`

### Workflow for Each Sorry
1. **Read the context** - Understand what the theorem is trying to prove
2. **Check the statement** - Verify it's correct and has sufficient hypotheses
3. **Plan the proof** - Identify the mathematical strategy
4. **Attempt direct proof** - Try standard tactics first
5. **Break down if needed** - Create helper lemmas for complex steps
6. **Iterate** - Keep working until sorry-free or blocked
7. **Document gaps** - If truly stuck, document what's needed clearly
