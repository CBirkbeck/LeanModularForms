# Ticket B Handoff - PV Infrastructure

**Last Updated:** 2026-02-05 (Session 45)
**File:** `ValenceFormula_PV.lean`
**Goal:** Prove `pv_integral_eq_modular_transformation`

---

## Major Achievement This Session

**`annulus_symmDiff_measure_bound` is now SORRY-FREE** (lines 2630-2871)

This was the key structural lemma blocking progress. The proof is complete.

---

## Current State

### Build Status
- **Compiles:** Yes, no errors
- **Sorries in file:** 34

### Key Completed Lemmas
| Lemma | Lines | Status |
|-------|-------|--------|
| `norm_linear_approx_bound` | ~2389 | ✅ DONE |
| `symmDiff_subset_boundaryLayers` | ~2428 | ✅ DONE |
| `tAnnLin_implies_r_le` | ~2491 | ✅ DONE |
| `near_threshold_implies_r_in_shell` | ~2497 | ✅ DONE |
| `volume_shell_le` | ~2399 | ✅ DONE |
| `shell_volume_bound` | ~2521 | ✅ DONE |
| `annulus_symmDiff_measure_bound` | 2630-2871 | ✅ DONE |

### Remaining Sorries (Priority Order)
1. `singular_annulus_bound` (line 2892) - uses `annulus_symmDiff_measure_bound`
2. `pv_step_bound_ratio_two_uniform` (line 2939) - uses above
3. `immersion_crossing_cauchy` (line ~1697) - Cauchy criterion
4. `pv_limit_via_dyadic` (line 3150) - dyadic PV limit
5. Various downstream lemmas

---

## Key Technical Details

### The `annulus_symmDiff_measure_bound` Signature

```lean
lemma annulus_symmDiff_measure_bound {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hab : a < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0) :
    ∃ K > 0, ∃ δ₀' > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ < δ →
      let γAnn := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
      let tAnnLin := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁}
      volume (symmDiff γAnn tAnnLin) ≤ ENNReal.ofReal (K * ε₁^2 / ‖L‖^3)
```

### Key Design Decisions (Option A + δ-shrinking)

1. **Sets have 4 components:** `(Icc_mem, local_bound, lower_bound, upper_bound)`
   - `t ∈ Set.Icc a b`
   - `|t - t₀| < δ₀'` (LOCAL ZONE - eliminates far-field issues)
   - `ε₂ < ‖γ t - γ t₀‖` (or linear version)
   - `‖γ t - γ t₀‖ ≤ ε₁` (or linear version)

2. **Output `δ₁` as `δ₀'` (not `δ₀`):**
   - `δ₁ = min(δ₀, ‖L‖/(4K₀))` where K₀ is C² constant
   - Makes localization trivial: from `t ∈ γAnn` get `|t - t₀| < δ₁` directly
   - C² still applies since `δ₁ ≤ δ₀`

3. **Existential outputs:**
   - `K = 32 * K₀`
   - `δ₀' = δ₁ = min(δ₀, ‖L‖/(4K₀))`
   - `δ = ‖L‖ * δ₁ / 2`

### Call Site Updates Needed

The call sites at lines 2912-2913 and 3219 use:
```lean
obtain ⟨Kmeas, hKmeas_pos, δmeas, hδmeas_pos, h_meas_bound⟩ :=
    annulus_symmDiff_measure_bound hab _hat₀ hγ_C2 hγ_deriv hL
```

This is a **5-tuple** but the lemma now outputs a **6-tuple** (with `δ₀'`). Need to update to:
```lean
obtain ⟨Kmeas, hKmeas_pos, δ₀', hδ₀'_pos, δmeas, hδmeas_pos, h_meas_bound⟩ := ...
```

Also, the local set definitions in callers don't include the `|t - t₀| < δ₀'` restriction. Either:
- Update callers to use localized sets, OR
- Show non-localized sets are subsets when `ε₁ < δ`

---

## Proof Strategy for Remaining Lemmas

### `singular_annulus_bound` (line 2892)

**Goal:** Show ∫_{annulus} (t-t₀)⁻¹ = O(ε₁/‖L‖²)

**Strategy:**
1. Symmetric integral over tAnnLin cancels (odd function)
2. γAnn differs from tAnnLin by set of measure O(ε₁²/‖L‖³) [from `annulus_symmDiff_measure_bound`]
3. |∫_{symmDiff}| ≤ measure × sup|(t-t₀)⁻¹| ≤ O(ε₁²/‖L‖³) × O(‖L‖/ε₁) = O(ε₁/‖L‖²)

**Needs:**
- Update destructuring for 6-tuple
- Use localized sets or show equivalence

### `pv_step_bound_ratio_two_uniform` (line 2939)

**Goal:** For cutoffs with ratio ≤ 2, integral difference is O(ε₁/‖L‖²)

**Depends on:** `singular_annulus_bound`

### `pv_limit_via_dyadic` (line 3150)

**Goal:** PV limit exists via dyadic approximation

**Strategy:** Telescoping sum with geometric decay from step bounds

---

## Important Context

### Why Option A Was Needed
The old approach had "far-field" sorries - couldn't prove localization when `|t - t₀| ≥ δ₀`. By baking `|t - t₀| < δ₀'` into the set definition, far-field cases are impossible by definition.

### Why δ-shrinking Was Needed
With `δ₁ = min(δ₀, ‖L‖/(4K₀))`:
- Quadratic error term `K₀|t - t₀|` ≤ ‖L‖/4 in local zone
- Factor `‖L‖ - K₀|t - t₀|` ≥ 3‖L‖/4 (always positive and bounded below)
- Eliminates tricky "quadratic case" where factor could be small

### Destructuring Pattern
Old (3 components): `⟨_, _, ht_upper⟩`
New (4 components): `⟨_, ht_local, _, ht_upper⟩`

When reconstructing membership proofs, include `ht_localized`:
```lean
exact ht_not_tAnn ⟨ht_Icc, ht_localized, ht_lo', ht_hi'⟩
```

---

## Files to Read

1. **Main file:** `ValenceFormula_PV.lean`
2. **Progress log:** `VALENCE_AI_PROGRESS.md` (end of file for recent sessions)
3. **Overall plan:** `VALENCE_AI_PLAN_PV.md`
4. **Instructions:** `CLAUDE.md` in project root

---

## Quick Start for Next Session

1. Read this file
2. Check `annulus_symmDiff_measure_bound` is still sorry-free (lines 2630-2871)
3. Work on `singular_annulus_bound` (line 2892):
   - Update destructuring to 6-tuple
   - Adapt proof to use localized sets
4. Then `pv_step_bound_ratio_two_uniform` (line 2939)
5. Update `VALENCE_AI_PROGRESS.md` with session notes

---

## Commands

```bash
# Build the file
lake build LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_PV

# Count sorries
grep -c "sorry" LeanModularForms/Modularforms/valence/ComplexAnalysis/ValenceFormula_PV.lean

# Check errors at specific lines
# Use mcp__lean-lsp__lean_diagnostic_messages tool
```
