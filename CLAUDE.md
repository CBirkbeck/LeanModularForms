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

### Current Status: HalfResidueTheorem.lean and WindingNumber.lean

#### Current Sorries (as of 2026-01-27, updated after session):

**HalfResidueTheorem.lean** (2 declarations with sorry):
- `symmetric_second_diff_tendsto` (line 432): Symmetric second difference → second derivative
  - **Statement**: (γ(t₀+δ) + γ(t₀-δ) - 2γ(t₀))/δ² → γ''(t₀) as δ → 0
  - **Gap**: Standard Taylor expansion result, requires taylor_isLittleO from mathlib
  - **Mathematically trivial**: Well-known characterization of second derivative

- `pv_smooth_crossing_contribution_eq_pi_I'` (line 792): Version without curvature hypothesis
  - **Gap**: Orientation condition requires curvature info
  - **For valence formula**: Use `pv_smooth_crossing_contribution_eq_pi_I_C2` instead with h_ccw > 0
  - **Note**: This theorem is intentionally incomplete - it documents that the orientation
    condition cannot be proven without curvature (C²) hypothesis

**WindingNumber.lean** (2 declarations with sorry):
- `pv_equals_log_ratio_limit` (line 2116): PV = lim log(ratio)
  - **Gap**: Connect ε-cutoff PV definition to δ-parameterized log ratio
  - **Requires**: Asymptotic analysis showing ε-cutoff ≈ δ = ε/‖L‖
  - **Mathematical reference**: H-W Proposition 2.3

- `pv_integral_single_crossing_eq_angle` (line 2420): Corner crossing case
  - **Gap**: PV integral = I * angle for non-smooth crossings (t₀ ∈ partition)
  - **Note**: Smooth case (t₀ ∉ partition) is fully proven!
  - **For valence formula**: All elliptic point crossings are smooth, so this is not needed

**Key infrastructure now proven (no sorries):**
- `deriv_limit_plus` - γ(t₀+δ)/δ → γ'(t₀)
- `deriv_limit_minus` - γ(t₀-δ)/δ → -γ'(t₀)
- `im_ratio_over_delta_tendsto` - Im(ratio)/δ → Im(H·conj(L))/|L|² (key Taylor asymptotic!)
- `semicircle_integral_eq_pi_I` - The integral of 1/z over a semicircle = πi
- `smooth_crossing_opposite_values` - For smooth crossings, γ(t₀-δ)/γ(t₀+δ) → -1
- `log_ratio_smooth_crossing_tendsto_pi_I` - With orientation hypothesis, log(ratio) → πI
- `orientation_condition_from_C2_curvature` - With h_ccw > 0, Im(ratio) ≥ 0 for small δ
- `pv_smooth_crossing_contribution_eq_pi_I_C2` - C² version with strict curvature hypothesis
- `pv_smooth_crossing_eq_ipi` - Smooth crossing PV = iπ (used in main theorem)
- `regularized_integral_eq_log_diff_for_closed` - FTC for closed curves (fixed with partition hyp)

**What remains to fill:**
1. **Taylor expansion result**: `symmetric_second_diff_tendsto` - standard calculus
2. **Asymptotic analysis**: `pv_equals_log_ratio_limit` - ε ↔ δ reparameterization
3. **Corner case**: `pv_integral_single_crossing_eq_angle` - not needed for valence formula

#### Key Mathematical Insight:
The half-residue theorem states ∫_{semicircle} dz/z = πi. This is INDEPENDENT of the radius,
so the limit exists trivially. The challenge is connecting the PV definition to this result.

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

### Orbifold Coefficients and Winding Numbers

The coefficients 1/2 at i and 1/3 at ρ in the valence formula arise from the
**orbifold structure** of ℍ/SL₂(ℤ) and are consistent with the H-W winding numbers.

#### The Orbifold Structure

The quotient ℍ/SL₂(ℤ) is an orbifold with:

| Point | Stabilizer | Order | Valence Coefficient |
|-------|------------|-------|---------------------|
| Interior | {±I} | 1 | 1 |
| i | ⟨S⟩ where S: z ↦ -1/z | 2 | 1/2 |
| ρ | ⟨ST⟩ where ST: z ↦ -1/(z+1) | 3 | 1/3 |

The coefficient at p is **1/(order of stabilizer at p)**.

#### How H-W Winding Numbers Give the Correct Coefficients

The Hungerbühler-Wasem paper defines generalized winding numbers via Cauchy PV:
```
n_{z₀}(γ) = PV (1/2πi) ∮_γ dz/(z-z₀) = α/(2π)
```
where α is the angle from outgoing tangent to -incoming tangent.

**At i**: The arc passes smoothly through i with angle π, giving 1/2. ✓

**At ρ**: The boundary ∂𝒟 passes through TWO T-equivalent points:
- **ρ = e^{2πi/3}** at x = -1/2 (left corner): angle π/3 → contribution 1/6
- **ρ' = e^{πi/3} = ρ + 1** at x = 1/2 (right corner): angle π/3 → contribution 1/6
- By T-invariance f(z+1) = f(z), the order at ρ' equals the order at ρ
- **Total: 1/6 + 1/6 = 1/3** ✓

This shows the H-W winding number approach IS consistent with the orbifold coefficients
when we properly account for all T-equivalent points on ∂𝒟.

### What the PV/Winding Number Approach IS Good For

The Hungerbühler-Wasem PV approach is useful for:
- **Interior points**: winding number = 1 (classical case, curve avoids point)
- **Elliptic points**: sum over T-equivalent occurrences on ∂𝒟
- **Residue calculations**: PV integrals of meromorphic functions
- **General complex analysis**: curves passing through singularities

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

### Important: No Jordan Curve Theorem Needed
**DO NOT use Jordan curve theorem** for winding number proofs. Instead use:
- `generalizedWindingNumber_eq_classical'` - when curve avoids point, generalized = classical
- Homotopy invariance from HomotopyBridge.lean
- Residue theorem infrastructure from ResidueTheory.lean
- The winding number results from WindingNumber.lean (even if they have sorries - use them!)

The fundamental domain boundary winding number = 1 for interior points follows from:
1. The curve is closed and avoids the interior point
2. By `generalizedWindingNumber_eq_classical'`, the generalized winding = classical winding
3. Classical winding number for a simple closed curve around a point is ±1 (use the explicit
   parameterization and homotopy to a circle)

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
