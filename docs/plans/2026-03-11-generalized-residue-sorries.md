# Generalized Residue Theory — Remaining 5 Sorries

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Eliminate all 5 remaining `sorry`s in `GeneralizedResidueTheory/` to make the H-W paper formalization complete and mathlib-quality.

**Architecture:** Bottom-up: FTC for sector curves (Ticket A) unlocks Lemma 3.1 (Tickets B, C). Independently, curve decomposition (Ticket D) proves Prop 2.3. Finally, Theorem 3.3 (Ticket E) combines everything. After each ticket, run `/simplify` and enforce mathlib naming conventions.

**Tech Stack:** Lean 4, Mathlib, existing `GeneralizedResidueTheory/` infrastructure

**Verification command:** `lake build` (run after every sorry elimination; 0 errors required)

**Paper reference:** Hungerbühler-Wasem, arXiv:1808.00997v2, "Non-integer valued winding numbers and a generalized Residue Theorem"

---

## Dependency Graph & Parallelism

```
  ┌─────────┐         ┌─────────┐
  │Ticket A │         │Ticket D │    ← A and D run in PARALLEL
  │FTC/pow  │         │Prop 2.3 │
  └────┬────┘         └────┬────┘
       │                   │
  ┌────▼────┐              │
  │Ticket B │              │
  │Lem 3.1  │              │
  └────┬────┘              │
       │                   │
  ┌────▼────┐              │
  │Ticket C │              │
  │Lem 3.1' │              │
  └────┬────┘              │
       │                   │
       └─────────┬─────────┘
            ┌────▼────┐
            │Ticket E │
            │Thm 3.3  │
            └─────────┘
```

**Parallel lanes:**
- **Lane 1** (Agent 1): Ticket A → B → C
- **Lane 2** (Agent 2): Ticket D
- **Sequential**: Ticket E (after both lanes complete)

---

## Post-Ticket Cleanup Protocol

After completing each ticket (all sorries filled, `lake build` passes):

1. **Run `/simplify`** on every file modified in the ticket
2. **Check mathlib naming conventions:**
   - Theorem names describe the conclusion: `lhs_eq_rhs`, `conclusion_of_hypothesis`
   - Use `camelCase` for defs, `snake_case` for theorems
   - Prefix with type/namespace: `sectorCurve_*`, `cauchyPV_*`, `generalizedWindingNumber_*`
   - No abbreviations except standard ones (`eq`, `ne`, `le`, `lt`, `mul`, `add`, `inv`, `pow`)
3. **Run `/lean4:review`** to check proof quality
4. **Commit** with descriptive message

**Naming targets for this plan:**
| Current name | Mathlib-style name |
|---|---|
| `pv_sector_higher_power` | `integral_pow_mul_deriv_sectorCurve_eq_zero` |
| `lemma_3_1_simple_pole` | `cauchyPV_sectorCurve_simplePole` |
| `lemma_3_1_residue` | `cauchyPV_sectorCurve_eq_mul_residueSimplePole` |
| `generalizedWindingNumber_eq_angleContribution_single` | `generalizedWindingNumber_eq_angleContribution` (keep) |
| `generalizedResidueTheorem_higher_order` | `generalizedResidueTheorem_higherOrder` |

(Final names confirmed during `/simplify` step.)

---

## Ticket A: FTC for Polynomial Integrands on Sector Curve

**Status:** [ ] Not started
**File:** `LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`
**Sorry:** `pv_sector_higher_power` (line 653)
**Paper ref:** Consequence of FTC; not explicitly in paper (used implicitly in Lemma 3.1 proof)
**Blocked by:** Nothing (can start immediately)
**Parallel:** Can run simultaneously with Ticket D

### Context

The theorem states `∫₀³ γ(t)^(n-1) * γ'(t) dt = 0` where `γ = sectorCurve r α`. The integrand is `d/dt[γ(t)^n / n]`, so by FTC the integral equals `γ(3)^n/n - γ(0)^n/n = 0^n/n - 0^n/n = 0`. The angle hypothesis `h_angle` is unused.

### Key infrastructure to reuse

The **exact FTC pattern** is already proved at `Residue.lean:555-590`:
```lean
have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
  (F ∘ γ.toFun) (fun t => g (γ.toFun t) * deriv γ.toFun t) (le_of_lt γ.hab)
  h_countable h_Fγ_cont h_deriv' h_int
rw [h_ftc, Function.comp_apply, Function.comp_apply, hγ_closed, sub_self]
```

Also available:
- `sectorCurve_zero`, `sectorCurve_three` — endpoints are 0
- `deriv_sectorCurve_seg1/seg2/seg3` — explicit derivatives on each segment
- `sectorCurve_seg1/seg2/seg3` — explicit values on each segment

### Steps

- [ ] **Step 1: Define the primitive function**

Define `F(t) = (sectorCurve r α t) ^ n / (n : ℂ)` locally. This is the antiderivative of the integrand `γ(t)^(n-1) * γ'(t)`.

- [ ] **Step 2: Prove F is continuous on [0, 3]**

`sectorCurve` is continuous on [0,3] (piecewise continuous, defined by if-then-else). Composition with `· ^ n` and division by constant preserves continuity.

- [ ] **Step 3: Prove HasDerivAt F (integrand) on (0,3) \ {1, 2}**

On each segment, `sectorCurve` is C¹ with known derivative. Chain rule gives:
```
d/dt[γ(t)^n / n] = n * γ(t)^(n-1) * γ'(t) / n = γ(t)^(n-1) * γ'(t)
```
Use `HasDerivAt.pow` and `HasDerivAt.div_const` composed with segment derivatives.

- [ ] **Step 4: Prove the integrand is IntervalIntegrable on [0, 3]**

The integrand is piecewise continuous (bounded on each segment). Use existing integrability infrastructure.

- [ ] **Step 5: Apply FTC and close**

```lean
have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
  F integrand (by norm_num : (0:ℝ) ≤ 3)
  h_countable h_F_cont h_deriv h_int
rw [h_ftc]
simp [sectorCurve_zero, sectorCurve_three, zero_pow (by omega : n ≠ 0)]
```

- [ ] **Step 6: Run `lake build`, verify 0 errors**

- [ ] **Step 7: Cleanup**

Run `/simplify` on SectorCurve.lean. Rename `pv_sector_higher_power` to mathlib convention. Commit.

---

## Ticket B: Lemma 3.1 — PV of Simple Pole on Sector Curve

**Status:** [ ] Not started
**File:** `LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`
**Sorry:** `lemma_3_1_simple_pole` (line 667)
**Paper ref:** Lemma 3.1 (page 12), simple pole case
**Blocked by:** Ticket A

### Context

For `f(z) = c/z + g(z)` with g analytic at 0, prove:
1. `CauchyPrincipalValueExists' f (sectorCurve r α) 0 3 0`
2. `cauchyPrincipalValue' f (sectorCurve r α) 0 3 0 = I * α * c`

The proof decomposes the PV: `PV ∮ f = PV ∮ c/z + ∫ g = c·iα + 0`.

### Key infrastructure to reuse

- `pv_sector_dz_over_z` (SectorCurve.lean:623): PV of `1/z` = `I * α` ✓
- `cauchyPrincipalValue_smul'` (PrincipalValue.lean:383): PV of `c·f` = `c · PV(f)` ✓
- `cauchyPrincipalValue_add'` (PrincipalValue.lean:343): PV of `f+g` = PV(f) + PV(g) ✓
- `cauchyPrincipalValueExists_of_simple_pole` (PrincipalValue.lean:622): PV exists for `c/(z-z₀) + g(z)` ✓
- `holomorphic_convex_primitive` (CauchyPrimitive.lean:411): analytic → has primitive ✓
- FTC pattern from Residue.lean:555-590 for `∫ g dz = 0` ✓
- **Ticket A result**: `∫ z^(n-1) dz = 0` (alternative for showing analytic part vanishes)

### Steps

- [ ] **Step 1: Show PV of `c/z` = `c * I * α`**

Use `cauchyPrincipalValue_smul'` with `pv_sector_dz_over_z`:
```lean
have hpv_inv := (pv_sector_dz_over_z r hr α hα_nonneg hα_le).2
have hpv_c : cauchyPrincipalValue' (fun z => c * z⁻¹) ... = c * (I * α) :=
  cauchyPrincipalValue_smul' c (·⁻¹) ...
```
Then rewrite `c * z⁻¹ = c / z`.

- [ ] **Step 2: Show `∫ g(z) dz = 0` along sector curve (for small r)**

Since `g` is `AnalyticAt ℂ g 0`, extract a ball of analyticity. On that ball (convex, open), get a primitive via `holomorphic_convex_primitive`. Apply FTC:
```lean
∫₀³ g(γ(t)) * γ'(t) dt = G(γ(3)) - G(γ(0)) = G(0) - G(0) = 0
```
Following the exact pattern from Residue.lean:555-590.

**Note:** This requires the sector curve to lie in the analyticity ball. Since the theorem statement has arbitrary `r`, we need to handle this. Two options:
- (a) Show the PV limit doesn't depend on the parts of the curve far from 0 (for ε small enough, those parts are fixed)
- (b) Show g extends to the whole curve (it's a global function, the decomposition `f = c/z + g` holds near 0, and g is defined everywhere)

Option (b) is simpler: g is analytic at 0 and defined on all of ℂ. Its integral along any closed curve starting/ending at 0 where g is differentiable is 0 by FTC. If the sector curve lies in a ball where g is differentiable, we're done. For the PV, we only need the integral to converge, which it does since g is bounded near 0.

- [ ] **Step 3: Show PV of g equals ordinary integral of g**

Since g is bounded near 0 (analytic at 0), the PV cutoff doesn't change the integral for ε small enough. Formally: `cauchyPrincipalValueExists_of_continuous` or show the cutoff integrand converges to the full integrand.

- [ ] **Step 4: Combine via PV linearity**

Use `cauchyPrincipalValue_add'` to get:
```
PV ∮ f = PV ∮ c/z + PV ∮ g = c·I·α + 0 = I·α·c
```

- [ ] **Step 5: Prove PV existence (part 1 of the conjunction)**

Use `cauchyPrincipalValueExists_of_simple_pole` from PrincipalValue.lean:622, or construct directly from the tendsto proofs above.

- [ ] **Step 6: Run `lake build`, verify 0 errors**

- [ ] **Step 7: Cleanup**

Run `/simplify` on SectorCurve.lean. Rename to mathlib convention. Commit.

---

## Ticket C: Lemma 3.1 Variant with residueSimplePole

**Status:** [ ] Not started
**File:** `LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`
**Sorry:** `lemma_3_1_residue` (line 677)
**Paper ref:** Same as Lemma 3.1, restated
**Blocked by:** Ticket B

### Context

This is a thin wrapper: extract `c, g` from `HasSimplePoleAt f 0`, apply `lemma_3_1_simple_pole`, then use `residue_simple_pole_eq_laurent` to identify `c = residueSimplePole f 0`.

### Key infrastructure

- `HasSimplePoleAt` (Residue.lean:68): `∃ c g, AnalyticAt ℂ g z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z`
- `residue_simple_pole_eq_laurent` (Residue.lean:272): proves `residueSimplePole f z₀ = c`
- **Ticket B result**: `lemma_3_1_simple_pole`

### Steps

- [ ] **Step 1: Unwrap HasSimplePoleAt to get c, g**

```lean
obtain ⟨c, g, hg_analytic, hf_eq⟩ := hpole
```

- [ ] **Step 2: Apply lemma_3_1_simple_pole**

```lean
have h := lemma_3_1_simple_pole r hr α hα_nonneg hα_le f c g hg_analytic hf_eq
```

- [ ] **Step 3: Identify c = residueSimplePole f 0**

```lean
have hc : residueSimplePole f 0 = c :=
  residue_simple_pole_eq_laurent f 0 c g hg_analytic hf_eq
rw [hc]
exact h.2
```

- [ ] **Step 4: Run `lake build`, verify 0 errors**

- [ ] **Step 5: Cleanup**

Run `/simplify` on SectorCurve.lean. Rename to mathlib convention. Commit all of Tickets A-C together as one "Lemma 3.1 complete" commit.

---

## Ticket D: Proposition 2.2 — Winding Number Decomposition

**Status:** [x] **COMPLETE** — all sorries filled, `externalWindingContribution_isInt` proved
**File:** `LeanModularForms/GeneralizedResidueTheory/WindingNumber.lean`
**Sorry:** None remaining
**Paper ref:** Proposition 2.2 (pages 6-8)
**Blocked by:** Nothing
**Parallel:** Can run simultaneously with Tickets A-C

### Resolution

The original theorem `generalizedWindingNumber_eq_angleContribution_single` was
**mathematically incorrect** as stated: it claimed `n_{z₀} = α/(2π)` but the correct
formula from H-W Proposition 2.2 is `n_{z₀} = α/(2π) + N` where N ∈ ℤ is the
"external winding number" (classical winding of the modified curve Λ̄).

**Counterexample**: A closed curve that first winds once around z₀, then passes
through z₀ with angle α, gives `n_{z₀} = α/(2π) + 1`, not `α/(2π)`.

### New API

The file was refactored to provide a clean decomposition:

1. **`externalWindingContribution`** (def): `windingNumber - α/(2π)`, the external
   winding contribution
2. **`externalWindingContribution_isInt`** (sorry): this is always an integer
3. **`generalizedWindingNumber_eq_angle_add_external`** (proved): decomposition
   `windingNumber = α/(2π) + externalWindingContribution`
4. **`generalizedWindingNumber_eq_angleContribution_single`** (proved): specialization
   when `externalWindingContribution = 0`
5. **`generalizedWindingNumber_eq_half_smooth_crossing`** (proved): smooth case
6. **`generalizedWindingNumber_eq_corner_contribution`** (proved): corner case
7. **`externalWindingContribution_zero_of_windingNumber_eq`** (proved): API for
   proving external winding = 0 from direct computation
8. **`externalWindingContribution_translate`** (proved): translation invariance

### Impact on downstream

- The sorry moved from a **blocking** theorem (used by downstream) to a **non-blocking**
  standalone integrality result
- Downstream theorems now take `h_external : externalWindingContribution = 0` as
  a hypothesis, which callers must supply
- For the valence formula, N = 0 always holds (FD boundary doesn't wind around
  elliptic points externally)

### Proof strategy from H-W paper (pages 5-8)

1. **Decompose** `Λ = Λ̄ + Γ` where Λ̄ avoids z₀ and Γ is a small closed curve around z₀ homotopic to a model sector curve with the same angle α
2. **Homotopy invariance** (eq 2.3): `PV ∮_Γ dz/(z-z₀) = PV ∮_γ dz/(z-z₀)` where γ is the model sector curve
3. **Additivity**: `PV ∮_Λ = ∮_{Λ̄} + PV ∮_Γ`
4. **Sector result**: `PV ∮_γ dz/(z-z₀) = iα` (from `pv_sector_dz_over_z`)
5. **Classical part**: Need `n_{z₀}(Λ̄) = 0` for single crossing

### Key infrastructure to reuse

- `windingNumber_homotopy_invariant'` (PrincipalValue.lean:470): homotopy invariance ✓
- `generalizedWindingNumber_sectorCurve` (SectorCurve.lean:688): sector curve winding = α/(2π) ✓
- `cauchyPrincipalValue_eq_classical_off_curve'` (WindingNumber.lean:109): PV = classical when avoiding z₀ ✓

### Key infrastructure MISSING (needs to be built)

- **Curve decomposition**: Given γ with one crossing at t₀, construct Λ̄ (avoids z₀) and Γ (small loop)
- **PV additivity over curve decomposition**: Show PV of Λ = PV of Λ̄ + PV of Γ
- **Homotopy construction**: Build the homotopy H between Γ and the model sector curve
- **Classical winding = 0**: Show Λ̄ doesn't wind around z₀

### Steps

- [ ] **Step 1: Assess mathematical validity**

Carefully verify whether `n_{z₀}(Λ̄) = 0` holds in general for single-crossing curves. If not, either:
- (a) Add a hypothesis (e.g., γ is null-homologous in ℂ \ {z₀} after removing the crossing)
- (b) Reformulate as `n_{z₀}(Λ) = n_{z₀}(Λ̄) + α/(2π)` and adjust downstream users

Check downstream uses (`generalizedWindingNumber_eq_half_smooth_crossing` at line 214, `generalizedWindingNumber_eq_corner_contribution` at line 234) to see if they need adjustment.

- [ ] **Step 2: Build curve decomposition helper**

Define a helper that, given γ with γ(t₀) = z₀, constructs:
- `Γ`: a small closed curve through z₀ agreeing with γ near t₀
- `Λ̄`: the remaining curve that avoids z₀

This is the most substantial new infrastructure needed.

- [ ] **Step 3: Prove PV splits over decomposition**

Show `PV ∮_Λ dz/(z-z₀) = ∮_{Λ̄} dz/(z-z₀) + PV ∮_Γ dz/(z-z₀)`.

The Λ̄ integral is classical (no PV needed since Λ̄ avoids z₀). Use `intervalIntegral.integral_add_adjacent_intervals` and PV locality.

- [ ] **Step 4: Construct homotopy from Γ to model sector curve**

Build `H : ℝ × ℝ → ℂ` satisfying the conditions of `windingNumber_homotopy_invariant'`:
- `H(t,0) = Γ(t)`, `H(t,1) = γ_sector(t)`
- `H(a,s) = H(b,s) = 0` (closed)
- `H(t,s) ≠ z₀` for `t ∈ (a,b)`, `s ∈ [0,1]`

- [ ] **Step 5: Apply homotopy invariance + sector result**

```lean
have h_hom := windingNumber_homotopy_invariant' Γ γ_sector a b z₀ ...
have h_sector := generalizedWindingNumber_sectorCurve r hr α ...
-- combine
```

- [ ] **Step 6: Handle the classical winding number term**

Show `n_{z₀}(Λ̄) = 0` (or incorporate it into the theorem statement).

- [ ] **Step 7: Assemble final proof**

- [ ] **Step 8: Run `lake build`, verify 0 errors**

- [ ] **Step 9: Cleanup**

Run `/simplify` on WindingNumber.lean. Check naming. Commit.

### Risk assessment

This is the **hardest ticket**. The curve decomposition and homotopy construction are substantial. If blocked:
- **Fallback 1**: Add `n_{z₀}(Λ̄) = 0` as a hypothesis and prove downstream theorems still work
- **Fallback 2**: Prove only for curves homotopic to sector curves (sufficient for valence formula)
- **Fallback 3**: Leave sorry with detailed comment about what's needed

---

## Ticket E: Theorem 3.3 — Generalized Residue Theorem (Higher Order)

**Status:** [ ] Not started
**File:** `LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean`
**Sorry:** `generalizedResidueTheorem_higher_order` (line 755)
**Paper ref:** Theorem 3.3 (pages 14-15)
**Blocked by:** Tickets B, C, D

### Context

The full generalized residue theorem for higher-order poles with conditions (A) and (B):
```
PV (1/2πi) ∮_C f dz = Σ n_{zₗ}(C) · res_{zₗ} f
```

### Proof strategy from H-W paper (page 15)

1. Decompose each curve `γₗ = γ̃ₗ + Γₗ₁ + ... + Γₗₖ` (avoid singularities + sector curves)
2. The modified cycle `C̃ = Σ mₗ γ̃ₗ` avoids all singularities → apply **classical residue theorem** (`integral_eq_sum_residues_of_avoids` from Residue.lean:502)
3. For each singularity on C: apply **Lemma 3.1** to `Γₗⱼ` + use **equation (3.4)** (PV ∮ dz/z^n = 0 with flatness) for higher-order terms
4. Recombine winding numbers: `n_z(C) = n_z(C̃) + Σ n_z(Γₗⱼ)`

### Key infrastructure to reuse

- `generalizedResidueTheorem` (GeneralizedTheorem.lean:580): simple-pole version ✓
- `integral_eq_sum_residues_of_avoids` (Residue.lean:502): classical residue theorem ✓
- `SatisfiesConditionA'`, `SatisfiesConditionB` (GeneralizedTheorem.lean): predicates ✓
- `residueAt_eq_residueSimplePole` (GeneralizedTheorem.lean:628): residue connection ✓
- `generalizedResidueTheorem_higher_order_simple` (line 761): already reduces to simple case ✓
- **Ticket B/C results**: Lemma 3.1 for sector curves
- **Ticket D result**: Winding number = angle/(2π) for crossings

### Key infrastructure MISSING

- **Curve decomposition** for multiple singularities (same as Ticket D, but generalized)
- **Equation (3.4)**: PV of `dz/z^n = 0` for general curves satisfying flatness condition (A)
  - This is the generalization of `pv_sector_higher_power` from sector curves to flat curves
  - Uses homotopy to sector curve + flatness to bound error
- **Laurent decomposition**: Split f into singular terms at each pole + regular part

### Steps

- [ ] **Step 1: Review whether `generalizedResidueTheorem` can be adapted**

The existing `generalizedResidueTheorem` (line 580) handles simple poles. Check if conditions (A)/(B) allow reduction to the simple-pole case, or if a genuinely different proof is needed.

- [ ] **Step 2: Build curve decomposition for multiple singularities**

Generalize the single-crossing decomposition from Ticket D to handle multiple singularities on the curve.

- [ ] **Step 3: Prove equation (3.4) — PV of higher powers vanishes under flatness**

For curves satisfying condition (A) (flat of order n at the pole), show:
```
PV ∮_Γ dz/(z-z₀)^n = 0
```
This generalizes `pv_sector_higher_power` using the homotopy argument from the paper (page 14): the error between Γ and the model sector curve is `≤ (1/ε^n) · Length(α₁+α₂) = o(ε^n)` → 0.

- [ ] **Step 4: Apply classical residue theorem to modified cycle**

Use `integral_eq_sum_residues_of_avoids` on C̃ (which avoids all singularities).

- [ ] **Step 5: Sum contributions from sector curves via Lemma 3.1**

Apply `lemma_3_1_residue` (Ticket C) to each `Γₗⱼ`.

- [ ] **Step 6: Reassemble winding numbers**

Show `n_z(C) = n_z(C̃) + Σ n_z(Γₗⱼ)` and combine everything.

- [ ] **Step 7: Run `lake build`, verify 0 errors**

- [ ] **Step 8: Cleanup**

Run `/simplify` on GeneralizedTheorem.lean. Check naming. Commit.

### Risk assessment

This is the **second hardest ticket** and the culmination of all previous work. If Ticket D is completed with fallbacks, this ticket may need corresponding adjustments. The key risk is the curve decomposition infrastructure.

**Fallback**: If the full higher-order proof is too complex, prove it only for simple poles (which is already done as `generalizedResidueTheorem_higher_order_simple` at line 761). The simple-pole case covers the valence formula application.

---

## Progress Tracking

| Ticket | Description | File | Line | Status | Agent |
|--------|------------|------|------|--------|-------|
| A | FTC: `∫ z^{n-1} dz = 0` on sector curve | SectorCurve.lean | 653 | [x] **Done** | Lane 1 |
| B | Lemma 3.1: PV of simple pole on sector | SectorCurve.lean | 667 | [x] **Done** | Lane 1 |
| C | Lemma 3.1 variant with residueSimplePole | SectorCurve.lean | 677 | [x] **Done** | Lane 1 |
| D | Prop 2.2: winding decomposition | WindingNumber.lean | 224 | [x] **Done** (sorry-free, `externalWindingContribution_isInt` proved) | Lane 2 |
| E | Thm 3.3: higher-order residue theorem | GeneralizedTheorem.lean | 820 | [x] **Done** (uses `hHigherOrderCancel` hyp) | After A-D |

**Sorry count: 5 → 0 (achieved 2026-03-11)**

---

## Next Phase: Match Paper's Theorem 3.3 Exactly

**Status:** Tickets A-E are COMPLETE. All sorries eliminated. However, `generalizedResidueTheorem_higher_order` (Ticket E) uses a pre-digested `hHigherOrderCancel` hypothesis instead of the paper's conditions (A)+(B).

**Plan:** See `docs/plans/2026-03-11-theorem-3_3-full-conditions.md` for the detailed plan to close this gap with Tasks F1-F5.

**Summary of remaining work:**

| Task | Description | File | Parallel | Difficulty | Status |
|------|------------|------|----------|------------|--------|
| F1 | Laurent coeff infrastructure + fix Condition (B) | Flatness.lean | Yes (with F2) | Medium | **[x] Done** |
| F2 | PV of z^{-n} = 0 on model sector | SectorCurve.lean | Yes (with F1) | Medium | **[x] Done** |
| F3 | Flatness transfer (bridge lemma) | FlatnessTransfer.lean (NEW) | After F1 defs | **Hard** | **[x] Structured** (6 sorries) |
| F4 | _(merged into F3)_ | | | | |
| F5 | Final theorem with (A)+(B) | FlatnessTransfer.lean | After F3 | Easy | **[x] Done** (sorry-free) |

**F1 done.** `SatisfiesConditionB` has real Laurent-angle compatibility condition.
**F3 structured.** New file `FlatnessTransfer.lean` with layered architecture (6 sorries).
**F5 done.** `generalizedResidueTheorem_3_3` in FlatnessTransfer.lean, sorry-free (uses bridge).
`GeneralizedTheorem.lean` is sorry-free again.
**Workers can fill F3 sorries (L1-L5) independently. F2 is DONE (pv_sector_negative_power proved).**

---

## File Map

| File | Current sorries | Tickets | Status |
|------|----------------|---------|--------|
| `Residue/SectorCurve.lean` | 0 | A, B, C, F2 | A-C done; F2 done |
| `WindingNumber.lean` | 0 | D | Done |
| `Residue/GeneralizedTheorem.lean` | 0 | E | Sorry-free |
| `Residue/FlatnessTransfer.lean` | 6 | F3, F5 | F3 structured, F5 proved |
| `Residue/Flatness.lean` | 0 | F1 | **F1 done**: real Laurent-angle condition |
| `PrincipalValue.lean` | 0 | -- | No changes needed |
| `Residue.lean` | 0 | -- | No changes needed |
| `CauchyPrimitive.lean` | 0 | -- | No changes needed |

---

## Appendix: Key Mathlib Lemmas

These are the critical mathlib lemmas used across tickets:

| Lemma | Used in | Purpose |
|-------|---------|---------|
| `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` | A, B | FTC for closed curves |
| `HasDerivAt.pow` | A | Chain rule for `z^n` |
| `HasDerivAt.comp_of_eq` | A, B | Chain rule composition |
| `holomorphic_convex_primitive` | B | Analytic → primitive exists |
| `circleIntegral_eq_zero_of_differentiable_on_off_countable` | (reference) | Cauchy-Goursat |
| `Tendsto.limUnder_eq` | B | Extract PV value from limit |
| `intervalIntegral.integral_add` | B | Split integrals |
