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
- **NEVER introduce custom `axiom` declarations** - This is CRITICAL. Custom axioms can introduce logical inconsistencies and make proofs mathematically invalid. If a statement seems to require an axiom, it often means:
  1. The statement is FALSE (most common case)
  2. Missing hypotheses are needed
  3. A different approach is required
- All proofs should use only standard mathlib axioms (propext, funext, Quot.sound, Choice)
- Run `/check-axioms` after filling sorries to verify
- If you find yourself wanting to add an axiom, STOP and reconsider the mathematical validity of the approach

### Testing
- Always run `lake build` after making changes
- Check for errors, not just warnings
- Verify sorry count hasn't increased unexpectedly

### Current Status: HalfResidueTheorem.lean and WindingNumber.lean

#### IMPORTANT: PV-based Winding Numbers vs Angle-based Winding Numbers

**FUNDAMENTAL ISSUE** (see WindingNumber.lean lines 726-766):
The PV-based `generalizedWindingNumber'` definition gives **0** at crossing points, NOT angle/(2π)!
This is because the symmetric ε-cutoff loses direction information (the integrand 1/t is odd).

**DO NOT claim `generalizedWindingNumber' = angle/(2π)` at crossings - this is FALSE!**

**CORRECT APPROACH for boundary points:**
- Use `windingNumberWithAngles'` which computes from angles directly (sorry-free!)
- Key theorems (all proven):
  - `windingNumber_smooth_crossing`: single smooth crossing → 1/2
  - `windingNumber_corner_crossing`: single corner crossing → α/(2π)

**For interior points (curve avoids point):**
- Use `generalizedWindingNumber_eq_classical_away`: gives classical winding = 1

#### Current Sorries (as of 2026-01-27, UPDATED):

**HalfResidueTheorem.lean** - **SORRY-FREE!** ✓

**WindingNumber.lean** (2 sorries, NOT in critical path for valence formula):
- `pv_equals_log_ratio_limit`: Would prove PV = log(ratio), but this is UNUSED
- `pv_integral_single_crossing_eq_angle` corner case: UNUSED for valence formula

**ValenceFormula.lean** (4 declarations with sorries, UPDATED 2026-01-27):

1. **`fundamentalDomainBoundary_homotopic_to_circle`** (line 1880) - OLD smooth homotopy (DEPRECATED)
   - Returns `ClosedCurvesHomotopicAvoiding` which requires differentiability at ALL points
   - **CANNOT be proven** due to corners at t = 1, 2, 3, 4
   - Kept for reference only - use piecewise version below

2. **`fundamentalDomainBoundary_homotopic_to_circle_piecewise`** (line 2159) - NEW piecewise version
   - Returns `PiecewiseCurvesHomotopicAvoiding` with partition {1, 2, 3, 4}
   - **CAN be proven** because we only need differentiability OUTSIDE partition
   - Used by `generalizedWindingNumber_interior_eq_one_complex`
   - Sorries remaining: continuity, differentiability on pieces, derivative bounds
   - Anti-parallel sorry: same issue as smooth version (geometric argument needed)

3. **`valence_formula_base_identity`** (line ~4180) - **CORE FORMULA SORRY**
   - This is the BASE valence formula identity: Σ(coeff × order) = k/12 - ord_∞
   - Well-documented with full mathematical justification in docstring
   - All component theorems are proven (residue theorem, modular transformation)
   - The sorry captures the formal connection between H-W winding numbers and orbifold coefficients
   - `contour_computation_equality` now derives from this (no longer has sorry!)

4. **`pv_integral_eq_modular_transformation`** (line ~6758) - Bridge lemma
   - Connects PV integral to modular transformation result
   - Needed for the formal proof of valence formula

**PV Helper Lemmas (UPDATED 2026-01-28):**

1. **`pv_integral_vertical_cancel`** (line ~6626) - **COMPLETE!** ✓
   - Proves vertical edge integrals cancel by T-invariance
   - Uses `SlashInvariantFormClass.periodic_comp_ofComplex`
   - Key result: ∫_right + ∫_left = 0 for the log derivative

2. **`hasSimplePoleAt_logDeriv_of_zero`** (line ~6379) - IMPROVED (2 sorries)
   - Shows f'/f has simple pole at zeros of f
   - Added proper hypotheses: `hs_im : 0 < s.im`, `hf_nonzero : f ≠ 0`
   - Structured proof using `AnalyticAt.analyticOrderAt_ne_top`
   - Remaining: (a) order ≠ ⊤ for non-zero modular form, (b) algebraic calculation

3. **`immersion_crossing_cauchy`** (line ~6437) - Has sorry (H-W theorem content)
   - Proves Cauchy criterion for PV when curve crosses singularity
   - Mathematical content: symmetric cancellation of log divergence

4. **`continuousOn_logDeriv_regular_part`** (line ~6454) - Has sorry
   - Proves regular part of f'/f (minus singular terms) is continuous
   - Mathematical content: holomorphic away from poles → continuous

5. **`pv_integral_decompose_segments`** (line ~6618) - Has sorry
   - PV additivity over path concatenation
   - Needs analogue of `intervalIntegral_pathJoin` for PV integrals

**Proof structure improvement (2026-01-27):**
- Added `valence_formula_base_identity` as the clean base theorem
- `contour_computation_equality` now uses `valence_formula_base_identity` (no sorry!)
- Eliminated circular dependency between valence formula theorems
- All downstream theorems now derive cleanly from the base identity

**Key elliptic point theorems - ALL PROVEN!** ✓
- `windingContribution_at_i_eq_half` - uses `windingNumber_corner_crossing` (angle = π)
- `windingContribution_at_rho_eq_sixth` - uses `windingNumber_corner_crossing` (angle = π/3)
- `windingContribution_at_rho'_eq_sixth` - uses `windingNumber_corner_crossing` (angle = π/3)
- `windingContribution_rho_total_eq_third` - sum of ρ and ρ' = 1/3

**Key infrastructure proven (in HalfResidueTheorem.lean):**
- `pv_smooth_crossing_contribution_eq_pi_I'` - log(ratio) → πI for smooth crossings with orientation
- Various Taylor asymptotics for curve analysis

**Key infrastructure proven (in WindingNumber.lean):**
- `angleAtCrossing` - computes angle contribution at a crossing point
- `windingNumberWithAngles'` - sums angle contributions for all crossings
- `windingNumber_smooth_crossing` - proves 1/2 for smooth crossings
- `windingNumber_corner_crossing` - proves α/(2π) for corner crossings

#### Key Mathematical Insight:
For curves passing through a point, we CANNOT use the PV integral approach (it gives 0).
Instead, we must use the angle-based approach from the H-W paper, which tracks the
argument change as the curve passes through the point.

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

### ValenceFormula.lean Internal Organization

Due to circular dependencies between definitions and lemmas, ValenceFormula.lean is organized
into logical sections rather than separate files. When working on sorries, identify which
group they belong to:

#### **GROUP 1: PV Infrastructure** (lines ~6370-7050)
Handle these sorries TOGETHER (they depend on each other):
- `hasSimplePoleAt_logDeriv_of_zero` (line ~6388) - f'/f has simple pole at zeros
- `immersion_crossing_cauchy` (line ~6587) - Cauchy criterion for PV
- `continuousOn_logDeriv_regular_part` (line ~6646) - Regular part continuity
- `pv_integral_exists_f'_over_f` (line ~6684) - PV existence
- `pv_integral_decompose_segments` (line ~6798) - PV splits over segments
- `pv_integral_vertical_cancel` (line ~6842) - **PROVED** ✓
- `pv_integral_eq_modular_transformation` (line ~6958) - Bridge lemma

**Strategy**: Start with `immersion_crossing_cauchy` using Taylor expansion + model sector
analysis. Then `continuousOn_logDeriv_regular_part` follows. Finally assemble for
`pv_integral_eq_modular_transformation`.

#### **GROUP 2: Residue Side** (lines ~4873-4967)
- `residue_eq_order_at` (line ~4873) - residue of f'/f = order
- `residue_side_eq` (line ~4895) - **TRIVIAL** (just existence)
- `winding_equals_orbifold_coeff` (line ~4950) - **TRIVIAL** (just existence)

**Strategy**: These are mostly trivial existence statements. The real work is in the
`windingNumberCoeff'` definition which is already sorry-free.

#### **GROUP 3: Core Assembly** (lines ~4977-5200)
- `valence_formula_from_contour_equality` (line ~4977) - Bridge lemma (divide by 2πi)
- `valence_formula_base_identity` (line ~5042) - **CORE SORRY** ✓ documented
- `contour_computation_equality` (line ~5154) - **DERIVES from base** (no direct sorry)

**Strategy**: `valence_formula_base_identity` is the key sorry. It needs:
1. `pv_integral_eq_modular_transformation` (Group 1)
2. Winding coefficient = orbifold coefficient correspondence

#### **GROUP 4: Homotopy Leftovers** (lines ~2200-3100) - **NOT ON CRITICAL PATH**
- `fundamentalDomainBoundary_homotopic_to_circle` (line ~2271) - DEPRECATED
- `fundamentalDomainBoundary_homotopic_to_circle_piecewise` (line ~2598) - Used indirectly
- `generalizedWindingNumber_interior_eq_one_complex` (line ~2991) - Has sorry

**Strategy**: These are NOT needed for the valence formula. The orbifold approach is used instead.
Ignore these sorries unless specifically asked to work on homotopy.

#### **GROUP 5: Final Theorems** (lines ~7500-8200)
- `valenceFormula'` (line ~7522) - Main theorem with rationals
- `valenceFormula_classical'` (line ~7930) - Classical form
- Plus corollaries

**Strategy**: These all derive from `valence_formula_base_identity`. Once Groups 1-3 are done,
these will be automatic.

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
