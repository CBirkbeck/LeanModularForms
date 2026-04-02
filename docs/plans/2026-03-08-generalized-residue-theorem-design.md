# Generalized Residue Theorem (H-W Paper) — Design

## Goal

Prove the generalized residue theorem (Thm 3.3) and Proposition 2.2 from the Hungerbuhler-Wasem paper (arXiv 1808.00997v2), replacing the current `generalizedResidueTheorem'` which takes `CauchyPrincipalValueExists` as a hypothesis. The new theorem proves PV existence from the immersion + pole conditions.

## Architecture

Six phases, each building on the previous:

1. **Prop 2.2** — PV of `1/(z-z₀)` exists for closed piecewise C¹ immersions
2. **Lemma 3.1** — PV on model sector-curve for Laurent series
3. **Def 3.2 + higher-order PV** — Flatness condition, PV invariance under flatness
4. **Thm 3.3** — Clean generalized residue theorem (replaces existing)
5. **ValenceFormula update** — Downstream files use new theorem
6. **Cycles** — Formal sums `Σ mₗ γₗ`, lift theorem to cycles

## Phase Details

### Phase 1: Proposition 2.2

**File:** `GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean`

Prove that for a closed piecewise C¹ immersion `γ` and a point `z₀` on the curve, the Cauchy PV of `1/(z-z₀)` exists. The result decomposes as `n(Λ̃) + Σ αₗ/(2π)` where `αₗ` are oriented angles at crossings and `Λ̃` is the lifted curve in the log-Riemann surface.

**Key ingredients:**
- Existing `pv_limit_via_dyadic` (PV at single crossing)
- `cpv_avoidance` + `cpv_concat` (gluing PV over sub-intervals)
- New: assemble PV over all crossings via induction on crossing count

### Phase 2: Lemma 3.1

**File:** `GeneralizedResidueTheory/Residue/SectorCurve.lean`

Define the model sector-curve `γ₁ + γ₂ + γ₃` (radial-out, arc of angle `α`, radial-back) and prove `PV ∮_γ z^n dz/z = { iα if n=0; 0 if n≥1 }` under the angle condition `α = (p/q)π` with `gcd(p,q)=1`, `q ∤ (n+1)`.

### Phase 3: Definition 3.2 + Higher-Order PV

**File:** `GeneralizedResidueTheory/Residue/Flatness.lean`

Define flatness of order `n` at a crossing point (curve stays close to tangent with error `o(|Γ(x)-z₁|ⁿ)`). Prove that PV of `f` exists at a pole on the curve when the flatness condition (A) and angle condition (B) are satisfied.

### Phase 4: Theorem 3.3

**File:** Rewrite `GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean`

Replace `generalizedResidueTheorem'` with the clean version:
- No `CauchyPrincipalValueExists` hypothesis
- Simple poles: only need immersion + `HasSimplePoleAt` (conditions A+B automatic)
- Higher-order poles: conditions A+B as hypotheses
- Statement: `PV 1/(2πi) ∮_C f(z)dz = Σ n_{zₗ}(C) · res_{zₗ} f`

### Phase 5: ValenceFormula Update

Update downstream files to use the new theorem (drop `hPV_singular` hypotheses).

### Phase 6: Cycles

Define `Cycle` as formal integer-weighted sum of curves. Lift Thm 3.3 to cycles.

## Key Design Decisions

- **Replace, don't duplicate**: The existing `generalizedResidueTheorem'` is replaced, not kept alongside
- **Single curves first**: Cycles (Phase 6) come after single-curve theorem is solid
- **Leverage existing work**: `pv_limit_via_dyadic`, `cpv_avoidance`, `cpv_concat` are reused
- **Full generality**: Support higher-order poles via conditions A+B from the paper
