# Ticket Board: HW Theorem 3.3 Tight API

## Summary
- Total: 10 tickets
- Open: 4 | In Progress: 0 | Done: 6
- Parallel capacity: 1 (sequential by dependency)

## Final Target Statement

The end goal is a paper-faithful `hw_3_3` with **no Lean-formalization
artifact hypotheses** beyond what the paper requires. Concretely:

```lean
theorem hw_3_3
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hMero  : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I *
        ∑ s ∈ S, generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s)
```

This is exactly the paper hypotheses of Hungerbühler–Wasem Theorem 3.3
(arXiv:1808.00997v2). Compared to current `hw_3_3_tight` we still need to
absorb **8 obligations** into definitional consequences:

| Hypothesis | Eliminated by |
|------------|---------------|
| `h_polar_cancel`     | TIGHT-3 (per-pole (B)-closure + sum) |
| `h_holo_cancel`      | TIGHT-4 (Cauchy + null-hom + dominated convergence) |
| `hI_polar`           | absorbed in TIGHT-3 (closed form) |
| `hI_holo`            | absorbed in TIGHT-4 (closed form) |
| `hPV_sing`           | B-6 closure (already exists) |
| `hI_sing`            | absorbed in B-6 closure |
| `h_no_endpt_cross`   | TIGHT-7 (derive from `hCondB` transversality) |
| `h_unique_cross`     | TIGHT-7 (derive from `hCondB` transversality) |
| (`h_deriv_int` would be added by `_closed` form) | TIGHT-6 (derive from `PwC1Immersion`) |

## Status

* TIGHT-1 ✅ DONE — Laurent polar part extraction (`HW33LaurentPolarPart.lean`)
* TIGHT-2 ✅ DONE — Decomposition identity (`f_minus_pp_eq_higherOrder_plus_holo`)
* TIGHT-5 ✅ DONE — Tight theorem `hw_3_3_tight` (`HW33Tight.lean`)
* TIGHT-3 ⏳ OPEN — Auto-discharge `h_polar_cancel` (deep, multi-session)
* TIGHT-4 ⏳ OPEN — Auto-discharge `h_holo_cancel` via dominated convergence
* TIGHT-6 ✅ DONE — `ClosedPwC1Curve.deriv_extend_intervalIntegrable`
* TIGHT-7 ✅ DONE — Removed vestigial `h_no_endpt_cross` / `h_unique_cross`
* TIGHT-8 ✅ DONE — Bridge `ClosedPwC1Immersion → PwC1Immersion`
* TIGHT-9 ✅ DONE — Paper-faithful `hw_3_3_paper` (curve form, with oracles)
* TIGHT-9b ✅ DONE — `hw_3_3_simple_avoidance_paper` (clean, no oracles)
* TIGHT-10 ⏳ OPEN — Build `ClosedPwC1Immersion` for FD boundary
* TIGHT-11 ✅ DONE — `ClosedPwC1Curve.lipschitzWith_extend` (Lipschitz from paper-faithful structure)
* TIGHT-12 ✅ DONE — Drop `hU_bounded` requirement (unbounded Cauchy)
* TIGHT-13 ✅ DONE — `hw_3_3_higherOrder_avoidance_paper` (higher-order avoidance, polar-decomp data)
* PHASE-5b ✅ DONE (2026-05-12) — `hPV_sing_of_conditionB_avoids` (`HW33PVSing.lean`):
  full discharge of `hw`, `h_avoid_pairs`, `h_int` residuals under avoidance.
  Signature reduced to paper hypotheses (`hSimple`, `hCondB`, `hγ_avoids`).
* PHASE-6.1 ✅ DONE (2026-05-12) — `hPV_sing_of_conditionB_singleCrossing` and
  `hPV_sing_of_conditionB_pointwise_winding` (`HW33PVSing.lean`): discharge `hw`
  via per-pole `SingleCrossingData γ s` witnesses (the existing `SingleCrossing.lean`
  framework). Composes the avoidance-free case with the standard crossing winding
  number API. Audit confirms no native k=1 crossing CPV theorem exists; the
  framework `SingleCrossingData.hasWindingNumber` already lifts a user-supplied
  far-segment FTC limit `E(ε) → L` to `HasGeneralizedWindingNumber γ s (L/(2πi))`.
  All theorems axiom-clean `[propext, Classical.choice, Quot.sound]`.
* PHASE-8 ✅ DONE (2026-05-12) — `hw_3_3_simple_with_crossData` (`HW33SimpleClean.lean`):
  composes the Phase 4 + Phase 5c dischargers into a single paper-faithful
  simple-pole theorem with `SingleCrossingData` crossings. Absorbs four oracle
  hypotheses (`hMero`, `h_holo_cancel`, `hPV_sing`, `hI_sing`) into automatic
  derivations:
  - `hMero` from `HasSimplePoleAt.meromorphicAt`;
  - `h_holo_cancel` from `h_holo_cancel_of_conditionB` (Phase 4);
  - `hPV_sing` from `hPV_sing_of_conditionB_singleCrossing` (Phase 5c);
  - sum-form `hI_sing` from per-pole integrability via
    `cpvIntegrandOn_finset_sum_intervalIntegrable`.
  Remaining inputs: `h_polar_cancel`, `hI_polar`, `hI_holo`, plus geometric
  crossing data (`crossData`, `hδ_pos`, `h_avoid_pairs`, `h_int_perpole`).
  The first three are not yet auto-derivable because
  `hCondB.laurent_compatible` is extracted via `Classical.choose`, so
  `laurentHigherOrderPolar` and `laurentHolomorphicRemainder` are not
  pointwise zero for simple poles without a separate Laurent-uniqueness
  argument. Axiom-clean `[propext, Classical.choice, Quot.sound]`.

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

### [TIGHT-6] `ClosedPwC1Curve.deriv_extend_intervalIntegrable` ✅ DONE (2026-05-05)

- **Status**: done
- **File**: `ForMathlib/PaperPwC1Immersion.lean` (NEW)
- **Achieved**:
  - Defined paper-faithful structures `ClosedPwC1Curve x` and
    `ClosedPwC1Immersion x` matching HW page 3 exactly: partition includes
    `0` and `1`, and `ContDiffOn ℝ 1` is required on each *closed*
    sub-interval `[aₖ, aₖ₊₁]`.
  - `ClosedPwC1Curve.deriv_intervalIntegrable_piece` — integrability on a
    single piece, via continuity of `derivWithin` on the closed piece +
    a.e.-equality with `deriv` on the open interior.
  - `ClosedPwC1Curve.deriv_extend_intervalIntegrable` — global integrability
    on `[0, 1]` via finite-partition gluing
    (`intervalIntegrable_of_consecutive_pieces`, strong induction on
    `s.card`).
  - Axiom-clean: `[propext, Classical.choice, Quot.sound]`.
  - File compiles, no warnings.

Original goal lemma, satisfied:
  ```lean
  theorem ClosedPwC1Curve.deriv_extend_intervalIntegrable
      (γ : ClosedPwC1Curve x) :
      IntervalIntegrable (deriv γ.toPath.extend) volume 0 1
  ```

**Discovery (2026-05-05).** `PwC1Immersion` as currently defined does
**not** suffice to derive this lemma. The structure provides:

- `differentiable_off`, `deriv_continuous_off` on `Ioo 0 1 \ partition`
- `deriv_ne_zero` on `Ioo 0 1 \ partition`
- `left_deriv_limit`, `right_deriv_limit` only at points `p ∈ partition`
- `partition_subset : (partition : Set ℝ) ⊆ Ioo 0 1` — partition excludes 0 and 1

There is **no constraint** on `deriv γ.extend` near `t = 0⁺` or `t = 1⁻`.
A pathological example: `γ t = √t` is `C¹` on `(0, 1)`, has well-defined
left limit at any partition point, but `deriv γ t = 1/(2√t) → ∞` as
`t → 0⁺`. Such a γ would satisfy `PwC1Immersion` (with empty partition)
but its derivative is **not** integrable on `[0, 1]`.

**Two paths forward:**

(A) **Strengthen `PwC1Immersion`** with two new fields:
```lean
right_deriv_limit_zero : ∃ L : E,
  Tendsto (deriv toPath.extend) (𝓝[>] 0) (𝓝 L)
left_deriv_limit_one  : ∃ L : E,
  Tendsto (deriv toPath.extend) (𝓝[<] 1) (𝓝 L)
```
This makes the structure faithful to the paper's "C¹ closed curve" notion:
the derivative has finite one-sided limits everywhere (interior partition
points, plus the global endpoints). All concrete paths in the project
(line segments, arcs) satisfy this. **Cost**: every `PwC1Immersion`
constructor in the codebase must supply two new fields.

(B) **Take Lipschitz as auxiliary hypothesis**:
```lean
theorem PwC1Immersion.deriv_extend_intervalIntegrable
    (γ : PwC1Immersion x x) {K : ℝ≥0}
    (hLip : LipschitzWith K γ.toPath.extend) :
    IntervalIntegrable (deriv γ.toPath.extend) volume 0 1
```
Easy to prove (1-2 lines via `norm_deriv_le_of_lipschitz` + bounded
measurable). **Cost**: `hw_3_3` would still carry one extra hypothesis
(Lipschitz instead of `h_deriv_int`) — strictly weaker than path (A) but
still not paper-faithful.

**Recommendation**: path (A). The paper's statement is for genuine `C¹`
closed curves whose derivatives are bounded; the endpoint-limit fields
just make this explicit. The migration cost is one-time.

### [TIGHT-7] Remove vestigial crossing-regularity hypotheses ✅ DONE (2026-05-05)

- **Status**: done
- **Files**: `GeneralizedResidueTheorem.lean`, `HigherOrderAssembly.lean`,
  `HW33Closed.lean`, `HW33Tight.lean`
- **Discovery**: The hypotheses `_h_no_endpt_cross` and `_h_unique_cross` in
  `generalizedResidueTheorem` (`GeneralizedResidueTheorem.lean:288, 290`) were
  **already prefixed with `_`**, indicating they were unused in the proof body.
  They were vestigial — present in the type signature but never consumed.
  Reading the paper confirms HW does *not* require either: Proposition 2.2
  asserts only "finitely many" crossings (multiple per pole allowed), and
  endpoint crossings are not excluded.
- **Action**: removed the hypotheses from the four signatures (leaf +
  three callers). Build clean, axiom-clean (`[propext, Classical.choice,
  Quot.sound]`). `hw_3_3_tight` is now closer to the paper.

**Note for future work**: there is *additional* signature cleanup remaining
to reach the truly minimal paper form — the closed-form `_closed` analogue of
`hw_3_3_tight` would also discharge `h_polar_cancel`, `h_holo_cancel`, the
four integrability hypotheses, and `hPV_sing`. That's TIGHT-3 + TIGHT-4 + the
B-6 closure composition, which is independent of TIGHT-7.

### [TIGHT-7-DRAFT] Derive crossing regularity from `SatisfiesConditionB` (CANCELLED)

- **Status**: cancelled — superseded by the discovery above
- **File**: `ForMathlib/FlatnessConditions.lean`
- **Depends on**: none (independent of TIGHT-3/4)
- **Parallel**: yes
- **Goal lemmas**:
  ```lean
  theorem SatisfiesConditionB.no_endpoint_crossing
      (hCondB : SatisfiesConditionB γ f S) :
      ∀ s ∈ S, γ.toPiecewiseC1Path 0 ≠ s ∧ γ.toPiecewiseC1Path 1 ≠ s

  theorem SatisfiesConditionB.unique_crossing
      (hCondB : SatisfiesConditionB γ f S) :
      ∀ s ∈ S, ∀ t₁ ∈ Icc (0:ℝ) 1, ∀ t₂ ∈ Icc (0:ℝ) 1,
        γ.toPiecewiseC1Path t₁ = s →
        γ.toPiecewiseC1Path t₂ = s → t₁ = t₂
  ```

**Discovery (2026-05-05).** `SatisfiesConditionB` (in
`FlatnessConditions.lean:334`) currently has only two fields:

- `angle_rational` — angle is rational multiple of π **at each crossing
  whose parameter is in `Ioo 0 1`** (the inner `ht₀ : t₀ ∈ Ioo 0 1` makes
  the condition vacuous when `t₀ = 0` or `t₀ = 1`)
- `laurent_compatible` — Laurent decomposition exists at each such
  crossing

Neither field constrains how many parameters `t` map to a given `s ∈ S`,
nor does either forbid endpoint crossings. So the goal lemmas are **not
derivable** from the current definition.

**Two paths forward:**

(A) **Strengthen `SatisfiesConditionB`** with two new fields capturing
the paper's implicit "transverse crossing" assumption:
```lean
no_endpoint_crossing : ∀ s ∈ S0,
    (γ : ℝ → ℂ) 0 ≠ s ∧ (γ : ℝ → ℂ) 1 ≠ s
unique_crossing : ∀ s ∈ S0, ∀ t₁ ∈ Icc (0:ℝ) 1, ∀ t₂ ∈ Icc (0:ℝ) 1,
    (γ : ℝ → ℂ) t₁ = s → (γ : ℝ → ℂ) t₂ = s → t₁ = t₂
```
This faithfully captures HW's transverse-crossing notion. **Cost**: every
`SatisfiesConditionB` constructor must supply two new fields.

(B) **Define a wrapper structure** `TransverseCrossings γ S` that bundles
`SatisfiesConditionB` + `no_endpoint_crossing` + `unique_crossing`. Then
`hw_3_3` takes a single `TransverseCrossings` argument. Keeps
`SatisfiesConditionB` aligned with paper equation (3.4) (angle/Laurent),
moves transversality into a separate predicate aligned with paper (3.2)
(transverse C¹ curve).

**Recommendation**: path (B). The paper actually separates "transverse
crossing" (Section 2 / equation 3.2) from "Condition (B)" (equation 3.4).
Keeping our `SatisfiesConditionB` aligned with (3.4) and adding a
separate `TransverseCrossings` predicate matches the paper's structure
more faithfully than collapsing them.

## Open Question for User

Both tickets need a structural decision before code can be written.
TIGHT-6 → choose path (A) or (B). TIGHT-7 → choose path (A) or (B).
Until decided, neither ticket can be executed.

### [TIGHT-8] Bridge `ClosedPwC1Immersion → PwC1Immersion` ✅ DONE (2026-05-05)

- **Status**: done
- **File**: `ForMathlib/PaperPwC1Immersion.lean`
- **Achieved**:
  - `ClosedPwC1Curve.toPiecewiseC1Path` — paper-faithful curve produces a
    legacy curve with partition `(γ.partition.erase 0).erase 1` and the
    legacy differentiability conditions deduced from `ContDiffOn` on
    closed pieces.
  - `ClosedPwC1Immersion.toPwC1Immersion` — paper-faithful immersion
    produces a legacy immersion. The `left_deriv_limit` and
    `right_deriv_limit` at every interior partition point are extracted
    via `ContDiffOn.continuousOn_derivWithin` + filter manipulation
    (`nhdsWithin_inter_of_mem'`).
  - Helper lemmas `exists_predecessor`, `exists_successor`,
    `exists_consecutive_pair_containing` in same file.
  - Axiom-clean: `[propext, Classical.choice, Quot.sound]`.

### [TIGHT-9] Paper-faithful `hw_3_3_paper` wrapper ✅ DONE (2026-05-05)

- **Status**: done
- **File**: `ForMathlib/HW33Paper.lean` (NEW)
- **Achieved**:
  - `hw_3_3_paper` takes `γ : ClosedPwC1Immersion x` (paper-faithful curve
    type) and routes through the legacy bridge `toPwC1Immersion` to call
    `hw_3_3_tight`. This is the first user-facing theorem statement that
    matches the paper's curve type verbatim.
  - Cancellation/integrability hypotheses unchanged (orthogonal — TIGHT-3,
    TIGHT-4, B-6 closure).
  - Axiom-clean.

### [TIGHT-10] Build `ClosedPwC1Immersion` for the FD boundary (RESCOPED)

- **Status**: open
- **Original framing**: "migrate the 5 legacy `PwC1Immersion` constructors".
- **Discovery (2026-05-05)**: there are *no* concrete constructors of the
  legacy `PwC1Immersion` in the project — only the new bridge
  `ClosedPwC1Immersion.toPwC1Immersion`. The "5 constructor sites" in the
  earlier audit are for a different structure
  (`GeneralizedResidueTheory.PiecewiseC1Immersion`), which is on a parallel
  development path and unrelated.
- **What's actually needed**: build a concrete `ClosedPwC1Immersion ℂ ⟨…⟩`
  for the fundamental-domain boundary (the eventual application target of
  `hw_3_3_paper`). The work is to discharge the four paper-faithful fields
  (`zero_mem_partition`, `one_mem_partition`, `contDiffOn_pieces`,
  `derivWithin_ne_zero_pieces`) from the FD geometry. Independent of
  TIGHT-3 / TIGHT-4.
