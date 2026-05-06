# HW Theorem 3.3 — refactor and unification

**Date:** 2026-05-06
**Status:** approved, awaiting plan

## Goal

Unify the ~30 theorem variants of Hungerbühler–Wasem Theorem 3.3 currently spread across 17+ files into a single mathlib-quality module: 2 central theorems + 4 corollaries + 1 deferred placeholder, with proofs composed from genuine reusable lemmas (not from "HW3.3 v17" duplicates).

## Motivation

Mathlib PR-readiness requires:
- One general theorem (or here: two incomparable centrals; see below) plus a few clean corollaries for common specializations.
- No 20-line hypothesis blobs — bundle hypotheses into structures (mathlib convention).
- Reusable supporting lemmas, each provable as standalone analysis facts.
- No duplication: every variant theorem in the current code is "HW3.3 with a slightly different hypothesis bundle", composed by chaining other variants. None are reusable as building blocks.

## Architecture

### Public API surface

A single new file `LeanModularForms/ForMathlib/HungerbuhlerWasem.lean` exposing:

| # | Theorem | Hypotheses (sketch) | Status |
|---|---|---|---|
| **A** | `hw_3_3_avoidance` (central) | open `U` + null-hom γ + γ avoids `S` + `PolarPartDecomposition f S U` | proved |
| **B** | `hw_3_3_simplePoles_convex` (central) | convex `U` + simple poles + γ may cross + 2 CPV/continuity oracles | proved (= cleaned `generalizedResidueTheorem'`) |
| 1 | `hw_3_3_simplePoles_avoidance` | A specialized: simple poles drop the decomposition argument | proved |
| 2 | `hw_3_3_convex_avoidance` | A specialized: convex drops null-hom | proved |
| 3 | `hw_3_3_classicalResidue` | 1 + 2 combined: convex + simple poles + avoidance | proved |
| 4 | `hw_3_3_simplePoles_convex_transverse` | B specialized: discharges crossing oracles via project's transverse-crossing machinery | proved (entry point for valence formula) |
| C | `hw_3_3_crossing` | full crossing + higher-order, no oracles | **deferred** — placeholder `sorry`, requires TIGHT-3 + TIGHT-4 |

A and B are incomparable (A has any pole order but requires avoidance; B has simple poles but allows crossings on a convex domain). C unifies them and is future work.

All names live in `namespace HungerbuhlerWasem`.

### Structure: `PolarPartDecomposition`

```lean
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where
  polarPart        : ℂ → ℂ → ℂ
  order            : ℂ → ℕ
  coeff            : (s : ℂ) → Fin (order s) → ℂ
  polarPart_eq     : ∀ s ∈ S, ∀ z, z ≠ s →
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - s) ^ (k.val + 1)
  residue_eq       : ∀ s ∈ S,
    residue f s = if h : 0 < order s then coeff s ⟨0, h⟩ else 0
  analyticRemainder      : ℂ → ℂ
  analyticRemainder_diff : DifferentiableOn ℂ analyticRemainder U
  decomp                 : ∀ z ∈ U \ ↑S,
    f z = analyticRemainder z + ∑ s ∈ S, polarPart s z
```

Constructors / API to provide alongside:
- `PolarPartDecomposition.simplePoles` — build from `∀ s ∈ S, HasSimplePoleAt f s`.
- (later, when mathlib Laurent extraction lands) `PolarPartDecomposition.ofMeromorphic`.

### Central theorem A signature

```lean
theorem hw_3_3_avoidance
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} {x : ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (h_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0:ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s)
    (decomp : PolarPartDecomposition f S U) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * π * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s)
```

8 hypotheses (vs the deleted `hw_3_3_paper`'s 12+).

### Central theorem B signature

(Replacement for `generalizedResidueTheorem'`, renamed and cleaned.)

```lean
theorem hw_3_3_simplePoles_convex
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U \ ↑S))
    {x : ℂ} (γ : ClosedPwC1Immersion x)
    (hγ_in_U : ∀ t ∈ Icc (0:ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U)
    (h_simple : ∀ s ∈ S, HasSimplePoleAt f s)
    (h_ext : ∀ s ∈ S,
      ContinuousAt (fun z => f z - residue f s / (z - s)) s)
    (h_PV_at_crossing : ∀ s ∈ S, CauchyPrincipalValueExists'
      (fun z => residue f s / (z - s))
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 1 s) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * π * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s)
```

The two oracles `h_ext` and `h_PV_at_crossing` are the irreducible inputs for the simple-pole-crossing case. They cannot be discharged in general — they're properties of the specific (`f`, `γ`, `s`) triple that the user must supply or prove for their use case (e.g., transverse crossings via Corollary 4 below).

### Genuine reusable lemmas (composing the central proofs)

Already exist as standalone, properly-stated lemmas — preserved in their current files:

| # | Lemma | File | Mathlib-PR-able |
|---|---|---|---|
| 1 | `contourIntegral_eq_zero_of_nullHomologous_at` (Cauchy/Dixon) | `DixonTheorem.lean` | yes |
| 2 | `contourIntegral_add`, `contourIntegral_finset_sum` | `PiecewiseContourIntegral.lean`, `HW33HigherOrderC3.lean` | yes |
| 3 | `contourIntegral_higherOrder_eq_zero_of_avoids` (∮c/(z-s)^k = 0 for k≥2) | `HW33HigherOrderAvoidance.lean` → moves to new module | yes |
| 4 | `integral_simple_pole_eq_winding` (∮c/(z-s) = 2πi w c) | `SimplePoleIntegral.lean` | yes |
| 5 | `polarPart_eq_simplePole_add_higherOrder` (algebraic split) | `HW33HigherOrderAvoidance.lean` → moves | no (specific to our structure) |
| 6 | `avoids_finset_delta_bound` | `NullHomologous.lean` | yes |
| 7 | `ClosedPwC1Immersion.lipschitzWith_extend` | `PaperPwC1Immersion.lean` | yes |
| 8 | `hasCauchyPVOn_of_avoids` | `MultipointPV.lean` | yes |
| 9 | `dixonFunction_eq_zero_of_nullHomologous_*` (Dixon's lemma core) | `DixonTheorem.lean` | yes |

The proof of Central A is a 30–50 line composition of these 9 lemmas. Central B's proof reuses the existing `simple_poles_decomposition` strategy from `GeneralizedTheoremBase.lean`. Each corollary is 5–10 lines.

## File deletions

15 files to delete (after caller migration):

| File | Reason |
|---|---|
| `HW33Paper.lean` | Oracle-form `hw_3_3_paper` superseded; `hw_3_3_simple_avoidance_paper` becomes Corollary 1 in new module |
| `HW33Tight.lean` | Same |
| `HW33Bridge.lean` | Legacy bridge layer, no longer needed |
| `HW33Closed.lean` | Two specializations folded into corollaries |
| `HW33Final.lean` | One specialization folded in |
| `HW33HigherOrderAuto.lean` | Lipschitz variants — Lipschitz now derived inside Central A |
| `HW33HigherOrderAvoidance.lean` | Content moves to new module; `polarPart_eq_simplePole_add_higherOrder` and `contourIntegral_higherOrder_eq_zero_of_avoids` move to genuine reusable lemma slots |
| `HW33HigherOrderC3.lean` | `contourIntegral_finset_sum` moves to `PiecewiseContourIntegral.lean` |
| `HW33HigherOrderC4.lean` | Two HOPolarSum lemmas folded into Central A's proof |
| `HW33LaurentPolarPart.lean` | `laurentPolarPartAt` machinery → fold into `PolarPartDecomposition.ofMeromorphic` constructor (when mathlib supports it) |
| `HW33Monotonicity.lean` | Specialized helper — review then likely delete |
| `HW33MultiPole.lean` | Specialized — folded into Central A |
| `HW33SectorEven.lean` | Sector-specific (used by valence formula) — relocate near valence-formula tree if still required |
| `HW33ExitTimeWrapper.lean` | Consumer-side wrapper — update callers, then delete |
| `GeneralizedResidueTheorem.lean` | The `_alt`, `_structural`, `_CPV`, `_simplePoles_convex_*` variants delete; only the historically-named `generalizedResidueTheorem` (if still referenced) survives as alias |

Variant theorems inside `HigherOrderAssembly.lean` and `HigherOrderCancel.lean` (the `hCancel_of_*` family, `hasCauchyPVOn_simplePoles_*_full*` variants) likewise delete; the underlying *building-block* lemmas they call into are kept.

## File preservation

Genuine reusable infrastructure — **touched only minimally** (caller migration only):

- `DixonTheorem.lean`, `DixonDef.lean`, `DixonDiff.lean` (Dixon's lemma)
- `NullHomologous.lean` (predicate + API)
- `PiecewiseContourIntegral.lean`, `PiecewiseC1Path.lean` (curve foundations)
- `PaperPwC1Immersion.lean` (paper-faithful curve type)
- `MeromorphicCauchy.lean` (review for one or two consolidatable lemmas)
- `SimplePoleIntegral.lean`, `MultipointPV.lean`, `MultipointPV/...` (single-pole and multipoint formulae)
- `CauchyPrincipalValue.lean`, `ClassicalCPV.lean`, `Residue.lean`, `ResidueCircleIntegral.lean`
- `FlatnessConditions.lean` (Conditions A,B — for deferred crossing form)
- `Cycles.lean` (cycle wrapper)
- `GeneralizedResidueTheory/Residue/GeneralizedTheoremBase.lean` (`simple_poles_decomposition` and `generalizedResidueTheorem'` — the latter is renamed/inlined into Central B)

## Caller migration

Sites that currently call deleted theorems:

- `LeanModularForms/ForMathlib/ValenceFormula/PVChain/Assembly/ResidueSide.lean:365` — calls `generalizedResidueTheorem'`. Migrates to `hw_3_3_simplePoles_convex_transverse` (Corollary 4).
- `LeanModularForms/ForMathlib/ValenceFormulaBridged.lean` — uses the same chain via `valence_formula_textbook_orbit_finsum_FM`. Migrates by transitive update.
- `LeanModularForms/ForMathlib/ValenceFormulaFinal.lean` — uses `valence_formula_textbook_orbit_finsum_FM`. No direct change needed once the bridged file builds.
- Any sites currently calling `hw_3_3_simple_avoidance_paper` → migrate to `hw_3_3_simplePoles_avoidance`.
- Any sites currently calling `hw_3_3_higherOrder_avoidance_paper` → migrate to `hw_3_3_avoidance`.
- Any sites currently calling deleted `hw_3_3_*` variants → migrate to whichever corollary fits.

Estimated ~10–20 callsites total. Mechanical renames with type adjustments.

## Risk and rollout

**Most invasive change:** deleting `GeneralizedResidueTheorem.lean` and renaming `generalizedResidueTheorem'` (in `GeneralizedTheoremBase.lean`) into Central B. Both are referenced by valence-formula machinery. Mitigation: `grep -rE "generalizedResidueTheorem'?"` across the project before deletion; port every consumer outside the delete list manually before deletion.

**Curve-type subtlety:** `generalizedResidueTheorem'` currently takes `γ : PiecewiseC1Immersion` (the type from `GeneralizedResidueTheory/PiecewiseCurveAPI.lean`), while the new Central A takes `γ : ClosedPwC1Immersion x` (paper-faithful). For Central B we have two viable choices:

1. **Keep `PiecewiseC1Immersion`** for B — closer to the existing valence-formula caller, less migration work, but exposes a second curve type in the public API. Document the conversion `ClosedPwC1Immersion.toPiecewiseC1Immersion` for users who want to share γ between A and B.
2. **Switch B to `ClosedPwC1Immersion`** — uniform API, but requires rebuilding `fdBoundary_HImmersion` as a `ClosedPwC1Immersion` and threading the change through `Assembly/ResidueSide.lean`. Larger blast radius.

The implementation plan picks (1) initially (lower risk, ships sooner) and notes (2) as a follow-up. The naming asymmetry (A takes `ClosedPwC1Immersion`, B takes `PiecewiseC1Immersion`) is acceptable given the two centrals are already incomparable.

**Build safety:** every file deletion + caller migration is committed in its own batch (≤200 LoC change per commit) so partial rollback is possible. `lake build` runs after each commit.

**Reversibility:** all changes go on a feature branch (`refactor/hw33-unify`). If migration explodes, revert.

## Out of scope

- Deferred Central C (`hw_3_3_crossing` — full crossing + higher-order). Placeholder with `sorry`, blocked on TIGHT-3 + TIGHT-4 work.
- Mathlib PR itself. This refactor produces a PR-ready module; the actual PR submission is a separate task.
- The `lemma `versus `theorem` keyword choice. Following the project's existing convention.
- Renaming `HasCauchyPVOn` itself (might want `Cauchy.principalValueExists` for mathlib). Out of scope here; addressable in a follow-up.

## Out-of-scope dependencies (kept stable)

- `HasCauchyPVOn`, `cauchyPrincipalValueOn`, `generalizedWindingNumber` definitions stay where they are.
- `IsNullHomologous` predicate stays in `NullHomologous.lean`.
- `ClosedPwC1Immersion` and `PiecewiseC1Path` types stay in their files.

## Success criteria

After this refactor:
- `lake build` passes with 0 errors, 0 warnings, 0 added sorries (the one `sorry` for Central C is intentional).
- The new `HungerbuhlerWasem.lean` compiles standalone and exports exactly 7 theorems + the `PolarPartDecomposition` structure + ≤ 4 small constructor lemmas.
- The 15 listed files are deleted.
- Valence-formula chain compiles and produces identical output (same `valence_formula_textbook` axiom set).
- Spot check: `#print axioms HungerbuhlerWasem.hw_3_3_avoidance` returns `[propext, Classical.choice, Quot.sound]` (axiom-clean).
