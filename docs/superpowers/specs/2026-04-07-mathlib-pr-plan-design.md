# Mathlib PR Plan: Generalized Residue Theory + Valence Formula

## Summary

Contribute the generalized residue theorem (Hungerbuhler-Wasem, Theorem 3.3), Dixon theorem,
winding number decomposition (Prop 2.3), and the textbook valence formula for modular forms
to mathlib, structured as two PR chains of 100-300 line PRs.

**Paper reference:** Hungerbuhler-Wasem, arXiv:1808.00997v2

## Design Principles

- **No duplication**: Build on existing mathlib infrastructure, especially the new Poincare lemma
  (`MeasureTheory.Integral.CurveIntegral.Poincare`) for convex domain primitives
- **Tendsto-first API**: All limit-based definitions (CPV, winding number, residue) follow the
  `HasDerivAt`/`deriv` pattern: `Tendsto`-based predicate as primary API, `limUnder`-based value
  as secondary
- **Full generality first**: PR the general theorem (higher-order poles, null-homologous curves),
  then deduce clean corollaries (simple poles, convex domains)
- **Wrap mathlib Path**: `PiecewiseC1Path` extends mathlib's `Path` rather than defining from scratch
- **Mathlib quality**: No proofs > ~50 lines, no one-off definitions, clean docstrings
- **Usability-driven**: The SingleCrossingData framework (learned from valence formula work) is
  promoted to Chain 1 because it makes winding number computations practical for downstream users

## Two PR Chains

**Chain 1 — General Complex Analysis** (14 PRs, ~3050 lines)
Broadly useful: piecewise curves, CPV integrals, winding numbers, residues, Dixon, generalized
residue theorem. Useful to anyone doing complex analysis in Lean.

**Chain 2 — Valence Formula** (6 PRs, ~1500 lines)
Builds on Chain 1 + mathlib `ModularForm` infrastructure. Targets the textbook valence formula
`ord_inf + (1/2)ord_i + (1/3)ord_rho + sum(interior) = k/12`.

---

## Chain 1: Detailed PR Breakdown

### Foundation (sequential)

#### PR 1 — Piecewise C1 Curves (~200 lines)

**Theme:** Core curve infrastructure for complex analysis with corners.

**Definitions:**
- `PiecewiseC1Path` — extends mathlib `Path x y` with:
  - `partition : Finset I` (breakpoints in `[0,1]`)
  - `differentiableAt_off_partition` — C1 away from partition
  - `continuousAt_deriv_off_partition` — derivative continuous away from partition
- `PiecewiseC1Immersion` — extends `PiecewiseC1Path` with:
  - `deriv_ne_zero_off_partition` — nonzero derivative (immersion condition)
  - `left_deriv_limit` / `right_deriv_limit` — one-sided nonzero limits at partition points
- `PiecewiseC1Path.IsClosed` — source = target

**Key API:**
- Coercion to `ContinuousMap`, to `Path`
- `PiecewiseC1Path.ofSegments` — build from list of smooth segments
- `translate` — shift by constant

**Depends on:** nothing (only mathlib)

---

#### PR 2 — Contour Integration for Piecewise Curves (~200 lines)

**Theme:** Integration of complex functions along piecewise C1 paths.

**Definitions:**
- `contourIntegral (f : C -> C) (gamma : PiecewiseC1Path x y)` — the line integral

**Key theorems:**
- `contourIntegral_add` — linearity in f
- `contourIntegral_norm_le` — bound by sup norm x arc length
- `contourIntegral_eq_sum_segments` — decompose over partition intervals
- `contourIntegral_eq_sub_of_hasDerivAt` — FTC telescope:
  `integral_gamma F' = F(y) - F(x)` for piecewise C1 gamma

**Depends on:** PR 1

---

#### PR 3 — Cauchy Principal Value Integrals (~250 lines)

**Theme:** CPV framework with Tendsto-first API.

**Definitions (single-point):**
- `HasCauchyPV (f : C -> C) (gamma : PiecewiseC1Path x y) (z0 : C) (L : C)` —
  `Tendsto (fun eps => integral of f*gamma' with ||gamma(t)-z0|| > eps) (nhdsWithin 0 (Ioi 0)) (nhds L)`
- `cauchyPV f gamma z0` — value via `limUnder` (junk when limit doesn't exist)
- `HasCauchyPV.cauchyPV_eq` — bridge: `HasCauchyPV f gamma z0 L -> cauchyPV f gamma z0 = L`

**Definitions (multi-point):**
- `HasCauchyPVOn (S : Finset C) (f : C -> C) (gamma) (L : C)` —
  `Tendsto (fun eps => integral with all ||gamma(t)-s|| > eps for s in S) ... (nhds L)`
- `cauchyPVOn S f gamma` — value

**Key theorems:**
- `HasCauchyPV.add`, `.smul`, `.neg` — algebraic operations on Tendsto predicate
- `hasCauchyPV_of_avoids` — if gamma avoids z0, CPV = ordinary integral
- `cauchyPVIntegrand_intervalIntegrable` — epsilon-cutoff integrand is integrable

**Depends on:** PR 2

---

### Parallel Track A — Winding Numbers

#### PR 4 — Generalized Winding Number (~200 lines)

**Theme:** Winding number via CPV of 1/z, with Tendsto-first API.

**Definitions:**
- `HasGeneralizedWindingNumber (gamma) (z0 : C) (w : C)` —
  `HasCauchyPV (fun z => (z - z0)^(-1)) gamma z0 ((2*pi*I) * w)`
- `generalizedWindingNumber gamma z0` — value via `(2*pi*I)^(-1) * cauchyPV ...`

**Key theorems:**
- `HasGeneralizedWindingNumber.windingNumber_eq` — bridge to value
- `generalizedWindingNumber_circleMap_eq_one` — for z0 inside circle, winding = 1
  (bridge to mathlib `circleIntegral`)
- `generalizedWindingNumber_eq_zero_of_avoids` — winding = 0 if curve avoids z0 and is
  in a convex set (via Poincare bridge, PR 6)

**Depends on:** PR 3

---

#### PR 4b — Single-Crossing Computation Framework (~200 lines)

**Theme:** Reusable framework for computing winding numbers at crossing points.

This PR is the key lesson from the valence formula work: every winding number computation
at a crossing point follows the same 5-step pattern. Without this framework, each downstream
computation is a standalone 1000+ line ordeal. With it, users supply 5 ingredients and get
the winding number automatically.

**Definitions:**
- `SingleCrossingData (gamma) (a b : R) (z0 : C)` — structure packaging:
  - `L : C` — target PV limit
  - `t0 : R` — unique crossing parameter
  - `delta : R -> R` — cutoff function (maps epsilon to parameter window)
  - `threshold : R` — validity bound for epsilon
  - `h_far` / `h_near` — norm bounds: outside delta-window curve is far, inside is near
  - `E : R -> C` — FTC expression for near-crossing integral
  - `h_ftc` — integral over delta-window equals E(eps)
  - `h_limit` — `Tendsto E (nhdsWithin 0 (Ioi 0)) (nhds L)`
- `AsymmetricCrossingData` — variant with `delta_left != delta_right` (for corners
  where left/right geometry differs, e.g. arc meets line segment)

**Key theorems:**
- `HasCauchyPV.of_singleCrossing` — master theorem: SingleCrossingData implies CPV exists
- `HasGeneralizedWindingNumber.of_singleCrossing` — derives winding = L / (2*pi*I)
- `HasGeneralizedWindingNumber.of_singleCrossing_neg_half` — specialization for smooth
  crossing: L = -pi*I gives winding = -1/2
- `HasGeneralizedWindingNumber.of_singleCrossing_neg_sixth` — specialization for 60-degree
  corner: L = -pi*I/3 gives winding = -1/6
- `HasCauchyPV.of_asymmetricCrossing` — asymmetric variant

**Depends on:** PR 4, PR 2 (FTC)

---

#### PR 8 — Winding Number Decomposition: Prop 2.2 + 2.3 (~250 lines)

**Theme:** Angular decomposition of the generalized winding number.

**Definitions:**
- `crossingSet gamma z0` — finite set of parameter values where gamma passes through z0
- `angleAtCrossing gamma z0 t` — signed angle at crossing point t
- `externalWindingContribution gamma z0` — integer-valued external winding

**Key theorems (Prop 2.2):**
- `crossingSet_finite` — crossing set is finite for immersions
- `crossing_isolated` — each crossing is isolated
- `crossingSet_isClosed`

**Key theorems (Prop 2.3):**
- `generalizedWindingNumber_eq_external_sub_angle` — decomposition:
  `w(gamma, z0) = n_ext - (1/2pi) * sum of angles`
- `externalWindingContribution_isInt` — external part is integer
- `generalizedWindingNumber_eq_neg_half_of_smooth_crossing` — smooth crossing gives -1/2

**Depends on:** PR 4

---

### Parallel Track B — Residues

#### PR 5 — Residue Definitions and Simple Pole Calculus (~250 lines)

**Theme:** Residue infrastructure bridging to mathlib's MeromorphicAt.

**Definitions:**
- `HasSimplePoleAt (f : C -> C) (z0 : C) (c : C) (g : C -> C)` —
  `AnalyticAt C g z0 /\ forall^f z in nhds_ne z0, f z = c / (z - z0) + g z`
- `residue (f : C -> C) (z0 : C)` — via `(2*pi*I)^(-1) * lim_{r->0} circleIntegral f z0 r`
  (builds on mathlib's circleIntegral)

**Key theorems:**
- `residue_eq_of_hasSimplePoleAt` — residue from decomposition equals c
- `hasSimplePoleAt_iff_meromorphicOrderAt_eq_neg_one` — bridge to `MeromorphicAt`
- `HasCauchyPV.simple_pole` — PV of c/(z-s) along gamma = 2*pi*I * winding * c
- `residue_eq_zero_of_analyticAt` — no pole means zero residue

**Depends on:** PR 3

---

### Parallel Track C — Poincare Bridge

#### PR 6 — Convex Domain Primitives via Poincare Lemma (~150 lines)

**Theme:** Specialize the Poincare lemma to complex analysis.

**Key theorems:**
- `holomorphic_closedForm_of_differentiableOn` — bridge: f holomorphic on convex U implies
  f dz is a closed 1-form in the Poincare sense (`E -> E ->L[K] F` framework)
- `DifferentiableOn.hasPrimitive_of_convex` — specialization:
  `exists F, forall z in U, HasDerivAt F (f z) z`
- `contourIntegral_eq_zero_of_differentiableOn_convex` — Cauchy theorem on convex domains
  (closed piecewise C1 curve, holomorphic integrand -> integral = 0)

**Depends on:** PR 2, mathlib Poincare lemma

---

### Parallel Track D — Homotopy Invariance

#### PR 7 — Homotopy Invariance of Contour Integrals (~200 lines)

**Theme:** Topological invariance of winding and integrals.

**Definitions:**
- `PiecewiseHomotopy gamma1 gamma2 (U : Set C)` — homotopy through piecewise C1 curves
  within U

**Key theorems:**
- `windingNumber_eq_of_homotopic` — winding preserved under homotopy avoiding z0
- `contourIntegral_eq_of_homotopic` — integral preserved under homotopy in domain of
  holomorphy
- `generalizedWindingNumber_eq_classical_of_avoids` — for curves avoiding z0, agrees with
  classical topological winding number

**Depends on:** PR 4, PR 6

---

### Merge (sequential)

#### PR 9 — Null-Homologous Cycles (~200 lines)

**Theme:** Formal Z-linear combinations of curves with homological condition.

**Definitions:**
- `ContourCycle` — `PiecewiseC1Immersion ->0 Z` (finitely supported)
- `contourIntegralCycle f Gamma` — linearly extend contour integral to cycles
- `windingNumberCycle Gamma z0` — linearly extend winding number
- `cauchyPVCycle S f Gamma` — linearly extend CPV
- `IsNullHomologous gamma U` — winding number vanishes for all z outside U
- `IsNullHomologousCycle Gamma U` — all components null-homologous

**Key theorems:**
- `isNullHomologous_of_convex` — closed curves in convex open sets are null-homologous
- Cycle algebra: `contourIntegralCycle_add`, `_neg`, `_smul`

**Depends on:** PR 4 (winding number), PR 2 (contour integration)

---

#### PR 10 — Dixon Theorem (~300 lines)

**Theme:** Core homological Cauchy theorem via Dixon's method.

**Definitions:**
- `dixonFunction f gamma z w` — the Dixon two-variable auxiliary function

**Key theorems (decomposed from current 259-line + 228-line proofs):**
- Helper lemmas for differentiability (~5 focused lemmas, each <=40 lines):
  - `dixonFunction_continuousOn`
  - `dixonFunction_differentiableOn_fst` — holomorphic in first variable
  - `dixonFunction_differentiableOn_snd` — holomorphic in second variable
  - `dixonFunction_bounded`
  - `dixonFunction_extends_to_diagonal`
- `dixonFunction_differentiable` — full differentiability (from helpers)
- `dixonFunction_tendsto_zero` — vanishes at infinity
- `dixonFunction_eq_zero` — main result

**Depends on:** PR 9 (cycles), PR 6 (convex primitives), PR 7 (homotopy invariance)

---

#### PR 11 — Homological Cauchy for Meromorphic Functions (~250 lines)

**Theme:** Cauchy theorem extended to meromorphic functions with zero residues.

**Key theorems:**
- `contourIntegral_eq_zero_of_holomorphic_nullHomologous` — classical Cauchy for
  null-homologous curves (immediate from Dixon)
- `contourIntegral_eq_zero_of_meromorphic_residueSum_zero` — meromorphic function with
  vanishing residue sum, null-homologous curve
- `contourIntegral_eq_zero_of_meromorphic_residueSum_zero_finset` — induction on finite
  pole set
- `hasCauchyPVOn_of_meromorphic_nullHomologous` — CPV convergence for meromorphic functions

**Depends on:** PR 10 (Dixon), PR 5 (residues)

---

#### PR 12 — Higher-Order Pole Conditions (~150 lines)

**Theme:** Geometric conditions ensuring CPV convergence at higher-order poles.

**Definitions (names TBD — need good mathlib-style names):**
- `IsFlatOfOrder (n : N) (gamma) (t : R)` — curve flatness of order n at crossing
  (tangent deviation is O(|s-t|^n))
- `HasFlatCrossings (f : C -> C) (gamma)` — for each pole s of f on gamma, the crossing
  has flatness >= pole order (working name for condition A')
- `IsLaurentCompatible (f : C -> C) (gamma)` — angle/Laurent coefficient compatibility
  at each crossing (working name for condition B)

**Key theorems:**
- `hasFlatCrossings_of_simplePoles` — automatic for simple poles (no condition needed)
- `isLaurentCompatible_of_simplePoles` — automatic for simple poles
- `meromorphicPrincipalPart f s` — extract finite-rank Laurent principal part
- `meromorphicAt_sub_principalPart_analyticAt` — remainder is analytic

**Depends on:** PR 1 (curves), PR 5 (residues)

---

#### PR 13 — Generalized Residue Theorem (~250 lines)

**Theme:** The main theorem and its corollaries.

**Key theorems:**
- `generalizedResidueTheorem` — **HW Theorem 3.3** (full generality):
  For gamma null-homologous in U, f meromorphic on U with poles S on gamma satisfying
  HasFlatCrossings + IsLaurentCompatible:
  `HasCauchyPVOn S f gamma (2*pi*I * sum_{s in poles} windingNumber(gamma, s) * residue(f, s))`
- `generalizedResidueTheorem_simplePoles` — **Corollary** (deduced):
  Simple poles only, no geometric conditions needed
- `generalizedResidueTheorem_convex` — **Corollary** (deduced):
  Convex domain version, null-homologous automatic

**Depends on:** PR 11 (homological Cauchy), PR 12 (conditions), PR 8 (winding decomposition)

---

## Chain 2: Valence Formula

### Overview

The textbook valence formula for modular forms of weight k on SL(2,Z):

```
ord_inf(f) + (1/2) * ord_i(f) + (1/3) * ord_rho(f) + sum_{z in F°} ord_z(f) = k/12
```

Chain 2 builds on Chain 1's generalized residue theorem (PR 13) and the single-crossing
framework (PR 4b) plus mathlib's existing `ModularForm` infrastructure.

### Proof Strategy

1. Define the 5-segment boundary contour gamma_H of the fundamental domain at height H
2. Apply the generalized residue theorem to logDeriv(f) along gamma_H:
   - Residue side: CPV integral -> 2*pi*I * sum(windingNumber * ord(f, s))
3. Compute winding numbers:
   - Interior points: winding = -1 (via homotopy to polygon -> circle)
   - At i: winding = -1/2 (instantiate SingleCrossingData, arc geometry)
   - At rho, rho+1: winding = -1/6 each (instantiate AsymmetricCrossingData)
4. Compute modular side using T/S transformations:
   - Left + right vertical edges cancel by T-periodicity
   - Arc contributions give -2*pi*I * k/6 via S-transformation
   - Horizontal segment gives 2*pi*I * ord_inf(f)
5. Equate residue side and modular side via limit uniqueness

### Chain 2 PR Breakdown

#### PR V1 — Fundamental Domain Boundary Contour (~250 lines)

**Theme:** The 5-segment closed contour around the standard fundamental domain.

**Definitions:**
- `fdBoundary (H : R)` — piecewise C1 closed path over [0,5] at height H:
  - Segment 1 (t in [0,1]): Right vertical from (1/2 + H*I) down to rho+1
  - Segment 2 (t in [1,2]): Unit circle arc from rho+1 to i
  - Segment 3 (t in [2,3]): Unit circle arc from i to rho
  - Segment 4 (t in [3,4]): Left vertical from rho up to (-1/2 + H*I)
  - Segment 5 (t in [4,5]): Horizontal from (-1/2 + H*I) to (1/2 + H*I)
- `fdBoundary_piecewiseC1Immersion` — it is a PiecewiseC1Immersion
- `fdBoundary_isClosed` — endpoints match

**Key API:**
- Segment accessors and parameterization formulas
- Partition = {0, 1, 2, 3, 4, 5}
- Crossing points: i at t=2, rho at t=3, rho+1 at t=1

**Depends on:** Chain 1 PR 1 (piecewise curves)

---

#### PR V2 — Interior Winding Number (~250 lines)

**Theme:** Winding number = -1 for points in the strict interior of the fundamental domain.

**Key theorems:**
- `generalizedWindingNumber_fdBoundary_eq_neg_one` — for z with ||z|| > 1 and |re(z)| < 1/2:
  `HasGeneralizedWindingNumber (fdBoundary H) z (-1)`

**Proof strategy:**
- Homotopy to inscribed polygon (fdBoundaryToPolygonHomotopy)
- Radial homotopy from polygon to circle around reference point
- Angle integration via FTC: total rotation = -2*pi (clockwise)
- Branch cut handling at left vertical edge crossing

**Helper lemmas:**
- Arc avoidance: interior points stay outside chord homotopy
- Polygon avoidance geometry
- Lifted angle continuity at branch cut crossing

**Depends on:** V1, Chain 1 PR 7 (homotopy invariance)

---

#### PR V3 — Elliptic Point Winding Weights (~300 lines)

**Theme:** Winding number at the three elliptic/boundary points using SingleCrossingData.

**Key theorems:**
- `generalizedWindingNumber_fdBoundary_at_i_eq_neg_half`:
  Instantiate `SingleCrossingData` with:
  - t0 = 2, delta(eps) = (12/pi) * arcsin(eps/2), L = -pi*I
  - Arc geometry: distance = 2*sin(delta*pi/12)
  - FTC via Complex.log on the arc
- `generalizedWindingNumber_fdBoundary_at_rho_eq_neg_sixth`:
  Instantiate `AsymmetricCrossingData` with:
  - t0 = 3, delta_L(eps) = (12/pi)*arcsin(eps/2), delta_R(eps) = eps/(H - sqrt(3)/2)
  - L = -pi*I/3 (60-degree corner)
- `generalizedWindingNumber_fdBoundary_at_rho_plus_one_eq_neg_sixth`:
  Mirror of rho (t0 = 1, delta_L/R swapped)

**Helper lemmas:**
- Arc distance formulas, FTC for log-derivative on arcs
- Vertical segment distance (linear in delta)
- Angle convergence at crossing points

**Depends on:** V1, Chain 1 PR 4b (single-crossing framework)

---

#### PR V4 — Orbit Pairing and T/S Invariance (~250 lines)

**Theme:** Modular symmetry cancellations in the contour integral.

**Key theorems:**
- `contourIntegral_leftEdge_add_rightEdge_eq_zero` — T-periodicity:
  f(z+1) = f(z) implies left + right vertical integrals cancel
- `contourIntegral_arcs_eq` — S-transformation on arcs:
  f(Sz) = z^k * f(z) implies arc₁ + arc₂ = -2*pi*I * k/6
- `ord_rho_plus_one_eq_ord_rho` — T-invariance of orders
- `sum_ord_leftVert_eq_sum_T_image` — orbit pairing on vertical edges

**Depends on:** V1, mathlib `ModularForm`, `SlashAction`

---

#### PR V5 — Valence Formula Core Identity (~250 lines)

**Theme:** Assembly of the valence formula from residue theorem + modular side.

**Key theorems:**
- `cpv_residue_side_tendsto` — residue side:
  `HasCauchyPVOn S (logDeriv f) (fdBoundary H) (2*pi*I * sum(gWN * ord))`
- `cpv_modular_side_tendsto` — modular side:
  CPV integral -> -2*pi*I * (k/12 - ord_inf(f))
- `valenceFormula_core` — equate via Tendsto uniqueness:
  `sum(gWN * ord) = -(k/12 - ord_inf(f))`
- Substitute winding weights from V2, V3:
  `ord_inf + (1/2)*ord_i + (1/3)*ord_rho + sum(interior) = k/12`

**Depends on:** V2, V3, V4, Chain 1 PR 13 (generalized residue theorem)

---

#### PR V6 — Textbook Valence Formula (~200 lines)

**Theme:** Clean user-facing API for the valence formula.

**Key theorems:**
- `valenceFormula_textbook` — the clean statement for `ModularForm (Gamma 1) k`:
  `ord_inf(f) + (1/2) * ord_i(f) + (1/3) * ord_rho(f) + finsum_{z in F°} ord_z(f) = k/12`
- `valenceFormula_textbook_finsum` — orbit-sum form using `finsum` over non-elliptic orbits
- Corollaries:
  - `ModularForm.weight_nonneg` — k >= 0 for nonzero f
  - `ModularForm.weight_eq_zero_iff` — k = 0 iff f is constant
  - `ModularForm.finite_zeros_in_fd` — f has finitely many zeros in the fundamental domain

**Depends on:** V5

---

## Full Dependency Graph

```
CHAIN 1:
PR1 ──> PR2 ──> PR3 ──┬──> PR4 ──> PR4b ──> PR8 ──────────────┐
                       │     │        │                          │
                       │     │        └──> PR9 ──> PR10 ──> PR11 ──> PR13
                       │     │                      ^         ^        ^
                       ├──> PR5 ─────────────────── │─────────┘── PR12─┘
                       │                            │
                       ├──> PR6 ────────────────────┘
                       │
                       └──> PR7 ──────────────────> PR10

CHAIN 2:
V1 (PR1) ──> V2 (PR7) ──────────────────────> V5 (PR13) ──> V6
   │                                            ^
   ├──> V3 (PR4b) ─────────────────────────────┘
   │                                            ^
   └──> V4 (mathlib ModularForm) ──────────────┘
```

## Line Budget

### Chain 1

| PR | Title | Est. Lines | Depends On |
|----|-------|-----------|------------|
| 1  | Piecewise C1 Curves | ~200 | — |
| 2  | Contour Integration | ~200 | 1 |
| 3  | Cauchy Principal Value | ~250 | 2 |
| 4  | Generalized Winding Number | ~200 | 3 |
| 4b | Single-Crossing Framework | ~200 | 4, 2 |
| 5  | Residue Definitions | ~250 | 3 |
| 6  | Poincare Bridge | ~150 | 2 |
| 7  | Homotopy Invariance | ~200 | 4, 6 |
| 8  | Winding Decomposition (Prop 2.2+2.3) | ~250 | 4 |
| 9  | Null-Homologous Cycles | ~200 | 4, 2 |
| 10 | Dixon Theorem | ~300 | 9, 6, 7 |
| 11 | Homological Cauchy (Meromorphic) | ~250 | 10, 5 |
| 12 | Higher-Order Pole Conditions | ~150 | 1, 5 |
| 13 | Generalized Residue Theorem | ~250 | 11, 12, 8 |
| **Chain 1 Total** | | **~3050** | |

### Chain 2

| PR | Title | Est. Lines | Depends On |
|----|-------|-----------|------------|
| V1 | FD Boundary Contour | ~250 | PR 1 |
| V2 | Interior Winding Number | ~250 | V1, PR 7 |
| V3 | Elliptic Point Winding Weights | ~300 | V1, PR 4b |
| V4 | Orbit Pairing / T,S Invariance | ~250 | V1, mathlib |
| V5 | Valence Formula Core Identity | ~250 | V2, V3, V4, PR 13 |
| V6 | Textbook Valence Formula | ~200 | V5 |
| **Chain 2 Total** | | **~1500** | |

### Grand Total: ~4550 lines across 20 PRs

## Open Questions

1. **Naming for conditions A'/B**: `HasFlatCrossings`/`IsLaurentCompatible` are working names.
   Need mathlib-style review.
2. **Dixon proof decomposition**: The current proof is 259+228 lines. PR 10 budgets ~300 lines
   total, so the decomposition into ~5 helper lemmas is essential. May need prototyping.
3. **Poincare bridge details**: Need to verify the exact 1-form translation works smoothly
   with mathlib's `E -> E ->L[K] F` representation.
4. **V2 proof size**: Interior winding = -1 currently uses a 3-layer homotopy argument with
   ~2000 lines of supporting code. Needs aggressive decomposition and may push the 250-line
   budget. Could split into V2a (homotopy construction) + V2b (angle integration).
5. **V3 proof size**: Each elliptic point currently takes 900-1100 lines. The SingleCrossing
   framework should compress this significantly, but the trigonometric helper lemmas for arc
   geometry may still be substantial. May need a V3a (arc geometry lemmas) + V3b (instantiation).

## Refactoring Required

Before PRing, the following current proofs need decomposition to meet mathlib's style:

### Chain 1
- `dixonFunction_differentiable` (259 lines -> ~5 x 40 lines)
- `dixonH1_eq` (228 lines -> ~5 x 40 lines)
- `generalizedResidueTheorem` (166 lines -> ~4 x 40 lines)
- `cpv_integrand_intervalIntegrable` (287 lines -> ~6 x 40 lines)
- `contourIntegral_eq_zero_of_meromorphic_residue_zero_nh` (185 lines -> ~4 x 40 lines)
- `windingNumber_eq_of_piecewise_homotopic` (138 lines -> ~3 x 40 lines)
- Plus ~30 more proofs in the 50-80 line range

### Chain 2
- Interior winding proof (~2000 lines across 4 files -> needs major restructuring)
- Elliptic winding weight proofs (3 x ~1000 lines -> should compress with SingleCrossing)
- Orbit pairing + modular side assembly
