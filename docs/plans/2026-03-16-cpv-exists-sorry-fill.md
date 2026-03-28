# Plan: Fill `cpv_exists_inv_sub_of_closed_unique` sorry

**File:** `LeanModularForms/GeneralizedResidueTheory/Residue/FlatnessTransfer.lean`
**Goal:** Make `generalizedResidueTheorem_3_3` sorry-free (eliminate `sorryAx`)

## Current State

- **1 sorry** at line 4774: `ContinuousOn R (Ioi 0)`
- **~13 compilation errors** in lines 4757-4913 (the proof after the sorry, written in a previous session with wrong Mathlib APIs — were masked by the sorry)

## Error Inventory

### Group 1: hL₀_norm proof (line 4755-4757)
- Line 4757: "No goals to be solved" — `ring_nf; simp` is redundant after simp
- **Fix:** Remove the dead `ring_nf; simp [Real.exp_zero]` line

### Group 2: Case split formulas (lines 4777-4789)
- Lines 4780, 4789: `linarith` fails on complex number equations
- **Root cause:** `Complex.log_exp_exists` gives `log(exp z) = z + n*(2πi)`, need `R = log(F) + (-n)*(2πi)`. `linarith` doesn't work for ℂ.
- **Fix:** Use `linear_combination -hn` or explicit rewrite

### Group 3: hcore Step 4 (line 4820)
- Same formula issue: `linarith` on complex equation
- **Fix:** Use `linear_combination hn` or `omega`-style rewrite

### Group 4: F continuous locally (lines 4861-4863)
- Line 4861: `Function.congr` doesn't exist
- Line 4862: Ambiguous `mem_Ioo.mp` (Set vs Finset)
- **Fix:** Use `ContinuousWithinAt.congr` directly, disambiguate with `Set.mem_Ioo.mp`

### Group 5: log(F) continuous (lines 4864-4866)
- Line 4865: `Complex.continuousAt_clog` doesn't exist
- **Fix:** Use `ContinuousOn.clog` or `ContinuousAt.clog`

### Group 6: DiscreteTopology + phi_const (lines 4876-4903)
- Line 4877: `discreteTopology_iff_isOpen_singleton_of_t2` doesn't exist
- Line 4892: `]]` parse error
- Line 4874: `IsPreconnected.constant_of_mapsTo` application incomplete
- **Fix:** Use `IsDiscrete` or prove discrete topology differently; fix syntax; complete the application

### Group 7: Final assembly (line 4726/4913)
- Unsolved goal at end of hcore — need to unfold `CauchyPrincipalValueExists'` and show R matches
- **Fix:** Complete the final step

### Group 8: The sorry itself (line 4774)
- `ContinuousOn R (Ioi 0)` — the DCT argument
- **Strategy:** Use `intervalIntegral.tendsto_integral_filter_of_dominated_convergence`
  with bound from `piecewiseC1Immersion_deriv_bounded`

## Execution Order

1. Fix Group 1 (trivial)
2. Fix Group 2 (formula sign)
3. Fix Group 3 (formula sign)
4. Fix Groups 4-7 (API names + incomplete proofs) — may need to rewrite lines 4844-4913
5. Fill Group 8 (the sorry — the hard mathematical content)

After each group, check `lean_diagnostic_messages` to verify progress.

## Key Mathlib Lemmas

| Lemma | Purpose |
|-------|---------|
| `Filter.Tendsto.clog` | log(F(ε)) → log(M) when F → M ∈ slitPlane |
| `ContinuousOn.clog` | log continuous on slitPlane |
| `Complex.exp_log` | exp(log x) = x for x ≠ 0 |
| `Complex.exp_eq_exp_iff_exists_int` | exp(x)=exp(y) ↔ ∃n, x=y+n*(2πi) |
| `IsPreconnected.constant` | Continuous function from preconnected to discrete is constant |
| `isPreconnected_Ioo` | (a,b) is preconnected |
| `piecewiseC1Immersion_deriv_bounded` | ∃ M, ∀ t ∈ [a,b], ‖γ'(t)‖ ≤ M |
| `intervalIntegral.tendsto_integral_filter_of_dominated_convergence` | DCT for interval integrals |
