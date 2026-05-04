# Ticket Board: HW Theorem 3.3 Tight API

## Summary
- Total: 5 tickets
- Open: 2 | In Progress: 0 | Done: 3
- Parallel capacity: 1 (sequential by dependency)

## Status

* TIGHT-1 ✅ DONE — Laurent polar part extraction (`HW33LaurentPolarPart.lean`)
* TIGHT-2 ✅ DONE — Decomposition identity (`f_minus_pp_eq_higherOrder_plus_holo`)
* TIGHT-5 ✅ DONE — Tight theorem `hw_3_3_tight` (`HW33Tight.lean`)
* TIGHT-3 ⏳ OPEN — Auto-discharge `h_polar_cancel`
* TIGHT-4 ⏳ OPEN — Auto-discharge `h_holo_cancel` via dominated convergence

## Tickets

### [TIGHT-1] Define `laurentPolarPartAt` extracting from condition (B)

- **Status**: open
- **File**: `ForMathlib/HW33LaurentPolarPart.lean` (NEW)
- **Depends on**: none
- **Description**: Define
  ```lean
  noncomputable def laurentPolarPartAt
      (γ : PwC1Immersion x x) (f : ℂ → ℂ) (S : Finset ℂ)
      (hCondB : SatisfiesConditionB γ f S)
      (h_no_endpt_cross : ∀ s ∈ S, ...)
      (h_unique_cross : ∀ s ∈ S, ...)
      (s : ℂ) (hs : s ∈ S) : ℂ → ℂ
  ```
  extracting the polar part `∑ k, a_k / (z - s)^(k+1)` at pole `s` via
  `Classical.choose hCondB.laurent_compatible (...)`. Returns the function
  `fun z => 0` if no crossing parameter exists (vacuous case).
- **API needed**:
  - `laurentPolarPartAt_eq_local`: near `s`, `f = laurentPolarPartAt s + analytic`
  - Differentiability at `z ≠ s`
- **Mathlib check**: not in mathlib

### [TIGHT-2] Define `laurentPolarPartTotal f S` and prove holomorphic remainder

- **Status**: open
- **File**: `ForMathlib/HW33LaurentPolarPart.lean`
- **Depends on**: TIGHT-1
- **Description**:
  ```lean
  noncomputable def laurentPolarPartTotal ... : ℂ → ℂ :=
    fun z => ∑ s ∈ S, laurentPolarPartAt ... s _ z
  ```
  Plus the holomorphic remainder:
  ```lean
  noncomputable def laurentHolomorphicRemainder ... : ℂ → ℂ :=
    fun z => f z - laurentPolarPartTotal ... z
  ```
  Prove: `laurentHolomorphicRemainder` is `DifferentiableOn ℂ (U \ ∅) = U`
  (since the polar parts cancel f's poles).

### [TIGHT-3] CPV vanishing of `laurentPolarPartTotal` under (B)

- **Status**: open
- **File**: `ForMathlib/HW33LaurentPolarPart.lean`
- **Depends on**: TIGHT-1, TIGHT-2
- **Description**: For each pole `s ∈ S` and each Laurent index `k ≥ 1` with
  `a_k ≠ 0`, the (B) condition gives `(k-1)·α ∈ 2πℤ` (where α is the corner
  angle), hence `hasCauchyPVOn_singleton_pow_of_conditionB_assembled` applies.
  Sum over poles + Laurent indices via `HasCauchyPVOn.finset_sum`.

### [TIGHT-4] CPV vanishing of `laurentHolomorphicRemainder` (Cauchy)

- **Status**: open
- **File**: `ForMathlib/HW33LaurentPolarPart.lean`
- **Depends on**: TIGHT-2
- **Description**: The holomorphic remainder is `DifferentiableOn ℂ U` and
  γ is null-homologous, so Cauchy's theorem gives contour integral = 0.
  Avoidance is automatic (γ ⊂ U \ S as set, holo extends to U).

### [TIGHT-5] Compose: `hw_3_3` tight theorem

- **Status**: open
- **File**: `ForMathlib/HW33Tight.lean` (NEW)
- **Depends on**: TIGHT-1, TIGHT-2, TIGHT-3, TIGHT-4
- **Description**: Use the per-piece CPV closures (TIGHT-3, TIGHT-4) as
  the `h_polar_cancel` / `h_holo_cancel` inputs to
  `generalizedResidueTheorem_higherOrder_under_B_closed`. The `hPV_sing`
  comes from `hasCauchyPVOn_simplePoles_nullHomologous_closed_full`
  (B-6 closure). Integrability hypotheses follow from the explicit
  decomposition + auto-discharge helpers.
