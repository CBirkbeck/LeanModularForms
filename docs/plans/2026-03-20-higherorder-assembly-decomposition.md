# HigherOrderAssembly Decomposition Plan

**File:** `LeanModularForms/GeneralizedResidueTheory/Residue/FlatnessTransfer/HigherOrderAssembly.lean`
**Target:** `higherOrderCancel_assembly_abstract` (672 lines → all proofs ≤50 lines)

## Problem

The proof defines ~15 local names via `set`/`let` that are referenced throughout. Extracting helpers requires passing all of them as parameters, making signatures unwieldy. Previous agents extracted leaf helpers but couldn't break the core structure.

## Strategy: Lift definitions to top level

Instead of `set total_pp := ...` inside the proof, define key objects as **private noncomputable defs** outside the proof. Then helpers can reference them by name.

## Step-by-step Plan

### Step 1: Extract 4 private defs (no proof changes yet)

Define these BEFORE `higherOrderCancel_assembly_abstract`:

```lean
private noncomputable def assembly_totalPP (S0 : Finset ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ s ∈ S0, meromorphicPrincipalPart f s z

private noncomputable def assembly_reg (S0 : Finset ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => f z - assembly_totalPP S0 f z

private noncomputable def assembly_pol (S0 : Finset ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s))

private noncomputable def assembly_regNF (S0 : Finset ℂ) (f : ℂ → ℂ)
    (g_corr : ∀ s ∈ S0, ℂ → ℂ) : ℂ → ℂ :=
  fun z => if hz : z ∈ S0 then
    g_corr z hz z - ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' z
  else assembly_reg S0 f z
```

Then replace `set total_pp := ...` etc. in the proof with these defs.
**Verify:** `lake build` after this step — should be a pure refactoring.

### Step 2: Extract `assembly_regNF_differentiableOn` (~150 lines → ≤50)

The biggest self-contained block. Proves:
```
DifferentiableOn ℂ (assembly_regNF S0 f g_corr) U
```
Split into two sub-helpers:
- `assembly_regNF_differentiableWithinAt_pole` (z ∈ S0 case, ~63 lines)
- `assembly_regNF_differentiableWithinAt_regular` (z ∉ S0 case, ~41 lines)

Then the main helper is:
```lean
private theorem assembly_regNF_differentiableOn ... :
    DifferentiableOn ℂ (assembly_regNF S0 f g_corr) U :=
  fun z hz => by
    by_cases hzS : z ∈ S0
    · exact assembly_regNF_differentiableWithinAt_pole ...
    · exact assembly_regNF_differentiableWithinAt_regular ...
```

**Verify:** `lake build` after this step.

### Step 3: Extract per-pole CPV vanishing (~350 lines → 3 helpers ≤50 each)

The `h_per_s_tendsto` block has 3 branches:

#### 3a: `cpv_perTerm_crossed_zero_order` (~40 lines)
When N_s = 0 and the curve crosses s: the term is identically 0 (pp = 0, res = 0), so CPV → 0 trivially.

#### 3b: `cpv_perTerm_crossed_positive_order` (~270 lines → needs further splitting)
When N_s > 0: decompose term_s = err_nf + polarHigher, show each CPV → 0.
This itself needs sub-helpers:
- `assembly_err_eventuallyEq` — err =ᶠ err_loc near s
- `assembly_err_differentiableOn` — err_nf DifferentiableOn U
- `assembly_polarHigher_continuousOn` — polarHigher ContinuousOn (U \ S0)
- `assembly_cpv_split_err_polar` — CPV(term_s) = CPV(err_nf) + CPV(polarHigher)

#### 3c: `cpv_perTerm_uncrossed` (~29 lines)
When the curve doesn't cross s: term_s is continuous on the image, integral = 0 by h_finset_vanish, then `tendsto_cpv_of_continuousOn_zero_integral`.

**Verify:** `lake build` after each sub-step.

### Step 4: Extract assembly scaffolding

- `assembly_pol_continuousOn` — h_pol ContinuousOn (U \ S0)
- `assembly_cpv_decomposition` — CPV(h) = CPV(h_reg_nf) + CPV(h_pol) pointwise
- `assembly_pol_tendsto_zero` — Tendsto (CPV h_pol) → 0 (from per-pole helpers)

### Step 5: Main theorem becomes ~15 lines

```lean
theorem higherOrderCancel_assembly_abstract ... := by
  intro h
  obtain ⟨g_corr, hg_corr_an, hg_corr_eq⟩ := choose_correction_data ...
  have h_reg_nf_diff := assembly_regNF_differentiableOn ...
  have h_reg_nf_zero := h_holo_vanish _ h_reg_nf_diff
  have h_reg_nf_cpv_zero := tendsto_cpv_of_continuousOn_zero_integral ...
  have h_pol_tendsto := assembly_pol_tendsto_zero ...
  exact combine_cpv_tendsto h_reg_nf_cpv_zero h_pol_tendsto (assembly_cpv_decomposition ...)
```

## Validation Protocol

After EVERY extraction:
1. `lean_diagnostic_messages` on this file (0 errors)
2. `lake build LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy` (0 errors)

## Execution Order

1. Step 1 (extract defs) — safest, pure refactoring
2. Step 2 (regNF differentiability) — self-contained block
3. Step 3c (uncrossed case) — simplest case
4. Step 3a (crossed zero order) — next simplest
5. Step 3b (crossed positive order) — hardest, needs sub-splitting
6. Step 4 (scaffolding)
7. Step 5 (main theorem rewrite)

Each step is a separate commit. If any step breaks downstream, revert immediately.
