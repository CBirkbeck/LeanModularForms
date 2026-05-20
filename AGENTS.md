# Codex Instructions for LeanModularForms

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

## Current Architecture: Split File Layout

The valence formula proof has been **split into separate files** for parallel AI work.
See `VALENCE_AI_TICKETS.md` for the ticket-based workflow.

### Split File Structure (in `ComplexAnalysis/`)

| File | Purpose | Dependencies |
|------|---------|--------------|
| `ValenceFormulaDefinitions.lean` | Core definitions (elliptic points, orders, etc.) | Base imports |
| `ValenceFormula_FD_Boundary.lean` | FD boundary curve and segments | Definitions |
| `ValenceFormula_InteriorWinding.lean` | Homotopy proof for interior winding = 1 | FD_Boundary |
| `ValenceFormula_EllipticContrib.lean` | Elliptic point angle contributions | FD_Boundary |
| `ValenceFormula_PV.lean` | PV infrastructure (logDeriv integrals) | FD_Boundary, ResidueTheory |
| `ValenceFormula_ResidueSide.lean` | Residue side assembly | InteriorWinding, EllipticContrib, PV |
| `ValenceFormula_ModularSide.lean` | Modular transformation side | PV |
| `ValenceFormula_Core.lean` | Core identity equating both sides | ResidueSide, ModularSide |
| `ValenceFormula_Final.lean` | Final theorem statements | Core |

### AI Ticket System

Work is organized into **three parallel tickets**. See `VALENCE_AI_TICKETS.md` for details.

| Ticket | Target File | Main Goal | Status |
|--------|-------------|-----------|--------|
| **A** - Homotopy | `ValenceFormula_InteriorWinding.lean` | `generalizedWindingNumber_fdBoundary_eq_one` | In progress |
| **B** - PV | `ValenceFormula_PV.lean` | `pv_integral_eq_modular_transformation` | In progress (10 sorries) |
| **C** - Core | `ValenceFormula_ResidueSide/ModularSide/Core.lean` | `valence_formula_base_identity` | Waiting on A, B |

**Progress tracking**: Update `VALENCE_AI_PROGRESS.md` after each session.

### Ticket B - PV Infrastructure (Current Focus)

**File**: `ValenceFormula_PV.lean`
**Goal**: Prove `pv_integral_eq_modular_transformation`

**Proven helper lemmas (2026-02-02):**
- `seg4_eq_seg1_minus_one` - geometric relationship between vertical edges ✓
- `deriv_fdBoundary_seg1` - derivative of seg1 ✓
- `deriv_fdBoundary_seg4` - derivative of seg4 ✓
- `deriv_seg4_at_complement_eq_neg_deriv_seg1` - key derivative relation ✓
- `logDeriv_periodic_of_periodic` - periodicity of logDeriv ✓

**Remaining sorries (10):**
1. `hasSimplePoleAt_logDeriv_of_zero` - f'/f has simple pole at zeros
2. `hasSimplePoleAt_logDeriv_of_zero'` - same, using `HasSimplePoleAt`
3. `immersion_crossing_cauchy` - Cauchy criterion for PV crossings
4. `continuousOn_logDeriv_regular_part` - regular part continuity
5. `pv_integral_exists_f'_over_f` - PV existence
6. `pv_integral_decompose_segments` - additivity over segments
7. `pv_integral_vertical_cancel` - T-invariance (has full proof structure!)
8. `arc_contribution_is_k_div_12` - S-transformation
9. `horizontal_contribution_is_cusp` - q-expansion
10. `pv_integral_eq_modular_transformation` - main result

**Key insight for `pv_integral_vertical_cancel`**:
```
1. Change variables t → 4-t in seg4 integral
2. Use seg4(4-s) = seg1(s) - 1 (proven)
3. Use logDeriv periodicity (proven)
4. Use deriv_seg4_at_complement_eq_neg_deriv_seg1 (proven)
5. Conclude ∫_{seg4} = -∫_{seg1}, so they cancel
```

### IMPORTANT: PV-based vs Angle-based Winding Numbers

**FUNDAMENTAL ISSUE**: The PV-based `generalizedWindingNumber'` gives **0** at crossing points!
This is because the symmetric ε-cutoff loses direction information.

**DO NOT claim `generalizedWindingNumber' = angle/(2π)` at crossings - this is FALSE!**

**CORRECT APPROACH:**
- **Interior points**: Use `generalizedWindingNumber_eq_classical_away` → winding = 1
- **Boundary points**: Use angle-based `windingNumberWithAngles'` or orbifold coefficients directly

**Key proven theorems:**
- `windingNumber_smooth_crossing`: single smooth crossing → 1/2
- `windingNumber_corner_crossing`: single corner crossing → α/(2π)
- `windingContribution_at_i_eq_half` ✓
- `windingContribution_rho_total_eq_third` ✓

## Project Structure

The valence formula proof is in `LeanModularForms/Modularforms/valence/`:

### Core Infrastructure (sorry-free)
- `ComplexAnalysis/Basic.lean` - Core definitions
- `ComplexAnalysis/Finiteness.lean` - Finiteness results
- `ComplexAnalysis/PrincipalValue.lean` - Cauchy principal value theory
- `ComplexAnalysis/WindingNumber.lean` - Generalized winding numbers
- `ComplexAnalysis/ResidueTheory.lean` - Residue computations
- `ComplexAnalysis/HomotopyBridge.lean` - Homotopy invariance

### Split Valence Files (active work)
- `ComplexAnalysis/ValenceFormulaDefinitions.lean` - Definitions
- `ComplexAnalysis/ValenceFormula_FD_Boundary.lean` - Boundary curve
- `ComplexAnalysis/ValenceFormula_InteriorWinding.lean` - Ticket A
- `ComplexAnalysis/ValenceFormula_PV.lean` - Ticket B
- `ComplexAnalysis/ValenceFormula_ResidueSide.lean` - Ticket C
- `ComplexAnalysis/ValenceFormula_ModularSide.lean` - Ticket C
- `ComplexAnalysis/ValenceFormula_Core.lean` - Ticket C

### Legacy (reference only)
- `ComplexAnalysis/ValenceFormula.lean` - Original monolithic file

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

## Working with AI Tickets

### Ticket Workflow

Each AI working on the valence formula should:

1. **Read the ticket file**: `VALENCE_AI_TICKETS.md` for overall plan
2. **Read the plan file**: `VALENCE_AI_PLAN_*.md` for detailed instructions
3. **Check progress**: `VALENCE_AI_PROGRESS.md` for current state
4. **Work on assigned file(s)**: Only edit target files listed in your ticket
5. **Update progress**: Update `VALENCE_AI_PROGRESS.md` before handing off

### Dependency Chain

```
Ticket A (Homotopy)  ──┐
                       ├──► Ticket C (Core) ──► Final Assembly
Ticket B (PV)        ──┘
```

**A and B can run in parallel.** C depends on both A and B.

### Progress Protocol

**ALWAYS update `VALENCE_AI_PROGRESS.md`** when finishing work. Include:
- Completed lemmas (by name)
- New helper lemmas introduced
- **Main blockers still remaining** (critical!)

### File Boundaries

- **DO NOT** edit files outside your ticket's target files
- **DO NOT** create new files without user approval
- **DO** import from earlier modules in the chain
- **DO** use existing definitions from `ValenceFormulaDefinitions.lean`

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

## Plan Files Reference

Detailed proof strategies are in:
- `VALENCE_AI_PLAN_HOMOTOPY.md` - Ticket A: Homotopy proofs
- `VALENCE_AI_PLAN_PV.md` - Ticket B: PV infrastructure
- `VALENCE_AI_PLAN_CORE.md` - Ticket C: Core assembly

**Read these before starting work on a ticket.**
