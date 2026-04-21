# Development Plan: Chain 1 Extended (HW 3.3 Full Closure)

**Scope:** Close the three remaining oracle-style hypotheses in the
generalized residue theorem (HW 3.3) so the main theorem takes only the
paper's hypotheses (null-homologous γ, holomorphic f on U\S, conditions A'/B
or simple poles).

**Started:** 2026-04-21
**References:**
- Hungerbuhler–Wasem, arXiv:1808.00997v2, §3.3
- `docs/superpowers/plans/2026-04-20-legacy-port-plan.md` (current state)

## Current state

| Theorem | Oracle hypotheses |
|---|---|
| `hasCauchyPVOn_simplePoles_convex_closed` | ✅ None — fully closed |
| `contourIntegral_simplePoles_convex_closed` | ✅ None — fully closed |
| `hasCauchyPVOn_simplePoles_nullHomologous_closed` | `w₀ ∈ U \ γ.image` + Dixon-zero for twisted `(z-w₀)·(f-pp)` |
| `generalizedResidueTheorem` (general, higher-order, A'/B) | 4 oracle hypotheses (`hCancel`, `hPV_sing`, `hI_*`) |

## Goals

1. **A: w₀ existence automation.** Prove `∃ w ∈ U, w ∉ γ.image` for open U
   containing γ's compact image, using that γ's image has 2-D Lebesgue measure 0.

2. **B: Dixon-zero automatic discharge.** Prove
   `∀ w, dixonFunction f U γ w = 0` from `IsNullHomologous γ U` +
   `DifferentiableOn f U` + curve regularity, by chaining existing Dixon
   infrastructure (`dixonFunction_differentiable` + `dixonFunction_eventually_eq_dixonH2`
   + `dixonFunction_eq_zero_of_bounds`).

3. **C: Higher-order HW 3.3 via A'/B.** Close `hCancel` for higher-order
   poles using conditions A' (flatness) and B (Laurent compatibility), via
   sector curve analysis. Existing infrastructure: `SectorCurve.lineCurve`,
   `higherOrder_sector_cancel_odd`, `higherOrder_sector_cancel_even_of_flat`,
   `conditionB_higherOrder_factor_eq`.

## Mathlib inventory

| Concept | Mathlib/existing | Action |
|---|---|---|
| Piecewise C¹ image has measure 0 | Follows from Lipschitz on compact + `MeasureTheory.volume_image_le_lipschitz` | USE |
| `dixonFunction_eq_zero_of_bounds` | Exists in `DixonTheorem.lean` | USE |
| `dixonFunction_differentiable` | Exists in `DixonDiff.lean` | USE |
| `dixonFunction_eventually_eq_dixonH2` | Exists in `DixonTheorem.lean` | USE |
| `dixonH1_differentiableOn`, `dixonH2_differentiableAt` | Exists | USE |
| Sector cancellation (odd/even) | Exists in `HigherOrderCancel.lean` | USE |
| `SatisfiesConditionA'`, `SatisfiesConditionB` | Exists in `FlatnessConditions.lean` | USE |
| Tangent approximation around crossing | NOT in pure FM; need to build | NEW |

## File structure

- `ForMathlib/CurveMeasureZero.lean` (NEW) — piecewise C¹ image has measure 0 + w₀ existence
- `ForMathlib/DixonTheorem.lean` — add `dixonFunction_eq_zero_of_nullHomologous` aggregator
- `ForMathlib/HigherOrderCancel.lean` — add tangent-approximation machinery + A'/B → hCancel
- `ForMathlib/GeneralizedResidueTheorem.lean` — update to state a fully-closed simple-pole null-homologous version, and a higher-order A'/B closed version

## Dependency graph

```
[A: w₀ existence] ──────────────────────┐
                                        │
[B1: h1_diff bundle]                    │
[B2: h2_diff bundle]     ──→ [B: Dixon-zero aggregator]
[B3: h_winding_zero_near]               │
[B4: bounds from regularity]            │
                                        ↓
                              [null-hom closed HW 3.3]
                                        │
[C1: tangent approximation]             │
[C2: curve-to-line reduction]  ──→ [C: A'/B → hCancel]
[C3: A'+B aggregator]                   │
                                        ↓
                              [higher-order closed HW 3.3]
```

## Generality notes

- All theorems parameterize on `x y : ℂ` (endpoints) implicitly where
  possible.
- Null-hom work assumes `PwC1Immersion x x` (closed curve), matching HW.
- Higher-order work needs `PwC1Immersion` for the crossing analysis.

## Non-goals for this phase

- Full `null_homologous_iff_simply_connected` — not needed.
- Homotopy invariance extensions — not in scope.
- Anything related to Chain 2 (valence formula).
