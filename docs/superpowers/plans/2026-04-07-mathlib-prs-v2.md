# Mathlib PRs v2: Full Rework Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Rework ALL existing proofs from `PiecewiseC1Curve` to `PiecewiseC1Path` (wrapping mathlib `Path`), organized into 100-300 line sorry-free PRs, culminating in HW Theorem 3.3, HW Prop 2.3, the Dixon theorem, and the textbook valence formula.

**Architecture:** PRs 1-6 (foundation) are already done. This plan covers PRs 7+ organized into 6 dependency groups (B-F) that can be partially parallelized. Each PR reworks existing working code from the `GeneralizedResidueTheory/` and `ValenceFormula/` directories into the new `PiecewiseC1Path` type system in `ForMathlib/`.

**Tech Stack:** Lean 4, Mathlib v4.29.0-rc8

**Spec:** `docs/superpowers/specs/2026-04-07-mathlib-pr-plan-design.md`

---

## CRITICAL RULES FOR ALL WORKERS

These rules are NON-NEGOTIABLE. Violating any of them makes the PR unusable.

1. **NO `sorry`** — every proof must be complete. If you cannot prove something, DO NOT include it. Including a sorry is WORSE than not including the theorem.

2. **NO custom `axiom` declarations** — only `[propext, Classical.choice, Quot.sound]` in `#print axioms`.

3. **NO watered-down theorems** — if the plan says "HW Theorem 3.3", you implement the FULL theorem with all its hypotheses (conditions A'/B, higher-order poles, null-homologous curves, Tendsto formulation). A simplified "convex-domain simple-poles" version is NOT acceptable as a substitute.

4. **NO imports from existing project code** (i.e., nothing from `LeanModularForms.GeneralizedResidueTheory.*` or `LeanModularForms.ValenceFormula.*`). ForMathlib files import only from `Mathlib.*` and `LeanModularForms.ForMathlib.*`.

5. **Use the new type system exclusively:**
   - `PiecewiseC1Path x y` (NOT `PiecewiseC1Curve`)
   - `PiecewiseC1Immersion x y` (NOT the old parameterless `PiecewiseC1Immersion`)
   - Domain is `[0,1]` via `Path.extend` (NOT `[a,b]`)
   - `HasCauchyPV` / `HasCauchyPVOn` Tendsto-first predicates (NOT `limUnder` values)
   - `HasGeneralizedWindingNumber` (NOT `generalizedWindingNumber'`)

6. **No `_name` hypothesis prefixes** — use bare `_` for unused but required hypotheses.

7. **Verify after every change:** `lake build LeanModularForms.ForMathlib.<ModuleName>` must pass with 0 errors, 0 sorry-related warnings.

8. **Rework means REWORK:** Read the existing proof in the old type system, understand the mathematical argument, then rewrite it using the new types. Do NOT create bridge/conversion functions between old and new types.

## Type Translation Reference

When reworking proofs, apply these mechanical translations:

| Old code | New code |
|----------|----------|
| `γ : PiecewiseC1Curve` | `γ : PiecewiseC1Path x y` |
| `γ : PiecewiseC1Immersion` (no params) | `γ : PiecewiseC1Immersion x y` |
| `γ.toFun` | `γ.toPath.extend` (or just `γ` via CoeFun) |
| `γ.a` | `(0 : ℝ)` |
| `γ.b` | `(1 : ℝ)` |
| `γ.hab : γ.a < γ.b` | `(by norm_num : (0:ℝ) < 1)` |
| `Icc γ.a γ.b` | `Icc (0:ℝ) 1` |
| `Ioo γ.a γ.b` | `Ioo (0:ℝ) 1` |
| `∫ t in γ.a..γ.b, ...` | `∫ t in (0:ℝ)..1, ...` |
| `γ.partition` | `γ.partition` (same, but `Finset ℝ` with subset of `Ioo 0 1`) |
| `γ.partition_subset` | `γ.partition_subset` (now `⊆ Ioo 0 1`, not `⊆ Icc a b`) |
| `γ.endpoints_in_partition` | GONE (partition no longer includes endpoints) |
| `γ.continuous_toFun` | `γ.continuous` (or `γ.toPath.continuous_extend`) |
| `γ.smooth_off_partition t ht htp` | `γ.differentiable_off t ht htp` |
| `γ.toPiecewiseC1Curve.IsClosed` | `PiecewiseC1Path.IsClosed γ` (i.e., `x = y`) |
| `generalizedWindingNumber' γ.toFun γ.a γ.b z₀` | `generalizedWindingNumber γ z₀` (value) or `HasGeneralizedWindingNumber γ z₀ w` (predicate) |
| `cauchyPrincipalValueIntegrandOn S f γ.toFun ε t` | `cpvIntegrandOn S f γ.toPath.extend ε t` |
| `CauchyPrincipalValueExistsOn S f γ.toFun γ.a γ.b` | `HasCauchyPVOn S f γ L` (for some L) |
| `cauchyPrincipalValueOn S f γ.toFun γ.a γ.b` | `cauchyPVOn S f γ` |
| `deriv γ.toFun t` | `deriv γ.toPath.extend t` |

---

## Dependency Groups and Parallelism

```
GROUP A (done): PRs 1-6 — Foundation
    |
    ├─── GROUP B: Winding Number Theory (8 PRs)
    |         Can work in PARALLEL with Group C
    |
    ├─── GROUP C: Residue Infrastructure (10 PRs)
    |         Can work in PARALLEL with Group B
    |
    └─── Both B and C feed into:
              |
              GROUP D: Homological Cauchy (6 PRs)
                   |
                   GROUP E: Main Theorems (3 PRs)
                        |
                        GROUP F: Valence Formula (8 PRs)
```

**Parallelism opportunities:**
- **Groups B and C are fully independent** — two workers can work on them simultaneously
- Within Group B: PRs B1-B3 (crossing/angles) are independent from B4-B7 (homotopy)
- Within Group C: PRs C1-C3 (multi-point PV) are somewhat independent from C4-C7 (principal parts)
- Groups D, E, F are sequential (each depends on the previous)

---

## GROUP A: Foundation (DONE)

PRs 1-6 already implemented and verified.

| PR | File | Lines | Status |
|----|------|-------|--------|
| 1 | PiecewiseC1Path.lean | 149 | Done |
| 2 | PiecewiseContourIntegral.lean | 263 | Done |
| 3 | CauchyPrincipalValue.lean | 293 | Done |
| 4 | GeneralizedWindingNumber.lean | 153 | Done |
| 4b | SingleCrossing.lean | 239 | Done |
| 5 | Residue.lean | 107 | Done |
| 6 | PoincareBridge.lean | 141 | Done |

**Note:** Before starting Group B/C, DELETE the existing wrong files (PRs 7-13, V1-V6) that contain watered-down theorems:
```
rm ForMathlib/{HomotopyInvariance,WindingDecomposition,NullHomologous,Dixon,
   HomologicalCauchy,HigherOrderPoles,GeneralizedResidueTheorem,
   FDBoundary,InteriorWinding,EllipticWeights,OrbitPairing,
   ValenceFormulaCore,ValenceFormulaTextbook}.lean
```

---

## GROUP B: Winding Number Theory (8 PRs)

**Can be worked in PARALLEL with Group C.**

### PR B1: Curve Utilities and Avoidance (~250 lines)

**Source:** `PiecewiseCurveAPI.lean` (256), `CurveAvoidance.lean` (98), `Bridges.lean` (76)

**Target file:** `ForMathlib/CurveUtilities.lean`

**Key content to rework:**
- `sortedPartition` — sorted list of partition points
- `consecutivePairs` — adjacent partition intervals
- Curve avoidance lemmas: min distance from curve to point
- `intervalIntegrable_of_piecewise_continuousOn_bounded` (from Basic.lean:~100-180)

**Key theorems:**
- `min_dist_pos_of_avoids` — if γ avoids z₀, there's a minimum separation
- `sortedPartition_chain` — sorted partition forms a chain covering [0,1]

- [ ] **Step 1:** Read source files, identify declarations to rework
- [ ] **Step 2:** Create `ForMathlib/CurveUtilities.lean` with reworked definitions
- [ ] **Step 3:** Adapt all proofs to `PiecewiseC1Path` types
- [ ] **Step 4:** `lake build LeanModularForms.ForMathlib.CurveUtilities` — 0 errors, 0 sorry
- [ ] **Step 5:** Commit

---

### PR B2: Crossing Analysis — Prop 2.2 (~300 lines)

**Source:** `WindingNumber/Proposition2_2.lean` (747 lines — extract the crossing part)

**Target file:** `ForMathlib/CrossingAnalysis.lean`

**Key content:**
- Crossing set definition: `{t ∈ Icc 0 1 | γ t = z₀}`
- `crossingSet_finite` — crossing set is finite for immersions (key Prop 2.2 result)
- `crossing_isolated` — each crossing is isolated (uses nonzero derivative + inverse function thm)
- CPV integrand integrability on segments between crossings

**Depends on:** PR B1 (curve utilities), PRs 1-4 (foundation)

**Source proof strategy for `crossingSet_finite`:** Uses compactness of `[a,b]`, local injectivity from nonzero derivative, and Bolzano-Weierstrass. Rework by replacing `[a,b]` with `[0,1]`.

- [ ] **Step 1:** Read `Proposition2_2.lean`, extract crossing-related declarations
- [ ] **Step 2:** Create `ForMathlib/CrossingAnalysis.lean`
- [ ] **Step 3:** Adapt crossing set definition to `Icc (0:ℝ) 1`
- [ ] **Step 4:** Rework `crossingSet_finite` proof
- [ ] **Step 5:** Rework integrability lemmas
- [ ] **Step 6:** Build and verify — 0 errors, 0 sorry
- [ ] **Step 7:** Commit

---

### PR B3: Angle Definitions and Winding Decomposition — Prop 2.3 (~300 lines)

**Source:** `WindingNumber/Defs.lean` (206), `WindingNumber/Decomposition.lean` (296)

**Target file:** `ForMathlib/WindingDecomposition.lean` (REPLACE existing wrong version)

**CRITICAL: This must contain the REAL Prop 2.3, not a trivial algebraic identity.**

**Key definitions:**
- `angleAtCrossing γ t₀ ht₀` — signed angle at crossing (from one-sided derivative limits)
- `externalWindingContribution γ z₀ t₀ ht₀` — integer external winding
- `windingNumberWithAngles'` — explicit angle-sum form

**Key theorems (EXACT signatures from project):**
```lean
-- Prop 2.3: winding = external integer - angle/(2π)
theorem generalizedWindingNumber_eq_external_sub_angle
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) :
    generalizedWindingNumber γ z₀ =
      externalWindingContribution γ z₀ t₀ ht₀ -
        (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi)

-- External winding is integer-valued
theorem externalWindingContribution_isInt ...

-- Smooth crossing gives -1/2
theorem generalizedWindingNumber_eq_neg_half_smooth_crossing ...

-- Corner crossing with angle α gives -α/(2π)
theorem generalizedWindingNumber_eq_neg_corner_contribution ...
```

**Depends on:** PR B2 (crossing analysis), PRs 1-4

- [ ] **Step 1:** Read `Defs.lean` and `Decomposition.lean` thoroughly
- [ ] **Step 2:** Create `ForMathlib/WindingDecomposition.lean` (replacing old version)
- [ ] **Step 3:** Rework `angleAtCrossing` — uses one-sided derivative limits from `PiecewiseC1Immersion`
- [ ] **Step 4:** Rework `externalWindingContribution`
- [ ] **Step 5:** Rework decomposition theorem and corollaries
- [ ] **Step 6:** Build and verify — 0 errors, 0 sorry
- [ ] **Step 7:** Commit

---

### PR B4: Homotopy Definitions (~200 lines)

**Source:** `Homotopy/Invariance.lean` (613 — definitions only, lines 1-100)

**Target file:** `ForMathlib/HomotopyDefs.lean` (REPLACE old HomotopyInvariance.lean)

**Key definitions:**
- `PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ P` — piecewise homotopy avoiding a point
- `ClosedCurvesHomotopicAvoiding` — for closed curves
- Basic properties: reflexivity, symmetry, transitivity

**Depends on:** PRs 1-2

- [ ] **Step 1:** Extract homotopy definitions from `Invariance.lean`
- [ ] **Step 2:** Create `ForMathlib/HomotopyDefs.lean`
- [ ] **Step 3:** Adapt to PiecewiseC1Path types
- [ ] **Step 4:** Build and verify
- [ ] **Step 5:** Commit

---

### PR B5: Winding Number Homotopy Invariance (~300 lines)

**Source:** `Homotopy/Invariance.lean` (613 — theorem, lines 100-450)

**Target file:** `ForMathlib/WindingHomotopy.lean`

**THE theorem (reworked signature):**
```lean
theorem windingNumber_eq_of_piecewise_homotopic
    {x : ℂ} (γ₀ γ₁ : PiecewiseC1Path x x) (z₀ : ℂ)
    (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀) :
    HasGeneralizedWindingNumber γ₀ z₀ w →
    HasGeneralizedWindingNumber γ₁ z₀ w
```

**Proof strategy:** Continuity + integer-valued argument. The winding number is continuous in the homotopy parameter and integer-valued, hence constant. This requires:
1. Continuity of the CPV integral in the homotopy parameter
2. Integrality of winding number for closed curves avoiding z₀
3. Connectedness of [0,1]

**Depends on:** PR B4 (homotopy defs), PR B2 (crossing analysis)

**NOTE:** The existing proof is 138 lines. After decomposition into helpers, expect ~250-300 lines.

- [ ] **Step 1:** Read the full proof in `Invariance.lean:304-442`
- [ ] **Step 2:** Decompose into ≤40-line helper lemmas
- [ ] **Step 3:** Rework to PiecewiseC1Path types
- [ ] **Step 4:** Build and verify
- [ ] **Step 5:** Commit

---

### PR B6: Contour Integral Homotopy Invariance (~200 lines)

**Source:** `Homotopy/Invariance.lean` (lines 450-613)

**Target file:** `ForMathlib/ContourIntegralHomotopy.lean`

**Key theorem:**
```lean
theorem contourIntegral_eq_of_homotopic
    {f : ℂ → ℂ} {x : ℂ} (γ₀ γ₁ : PiecewiseC1Path x x)
    (hH : ...) (hf : ...) :
    γ₀.contourIntegral f = γ₁.contourIntegral f
```

**Depends on:** PR B5

---

### PR B7: Winding Number Integrality (~300 lines)

**Source:** `Homotopy/Integrality.lean` (704)

**Target file:** `ForMathlib/WindingIntegrality.lean`

**Key theorem:**
```lean
theorem windingNumber_isInt_of_closed_avoiding
    {x : ℂ} (γ : PiecewiseC1Immersion x x) (z : ℂ)
    (h_avoids : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ z) :
    ∃ n : ℤ, HasGeneralizedWindingNumber γ z n
```

**Depends on:** PR B5, PR B3

---

### PR B8: Circle Parameterization and Mathlib Bridge (~250 lines)

**Source:** `Homotopy/CircleParam.lean` (425), `Homotopy/MathlibBridge.lean` (154)

**Target file:** `ForMathlib/CircleBridge.lean`

**Key content:**
- `circleParam` as a `PiecewiseC1Path`
- Bridge: `generalizedWindingNumber_circleMap_eq_one_of_mem_ball`
- Agreement with mathlib `circleIntegral`

**Depends on:** PR B5

---

## GROUP C: Residue Infrastructure (10 PRs)

**Can be worked in PARALLEL with Group B.**

### PR C1: PV Splitting at Crossings (~250 lines)

**Source:** `ContourIntegral/PVSplit.lean` (131), `ContourIntegral/CrossingLimit.lean` (192)

**Target file:** `ForMathlib/PVSplitting.lean`

**Key content:**
- `pv_split_at_crossing` — PV integral splits into far segments when far/near bounds hold
- `pv_tendsto_of_crossing_limit` — master crossing limit theorem
- `pv_tendsto_of_crossing_limit_asymmetric` — asymmetric variant

These are the analytical backbone of the SingleCrossing framework.

**Depends on:** PRs 1-3 (foundation CPV)

---

### PR C2: Segment FTC and Log-Derivative (~250 lines)

**Source:** `ContourIntegral/SegmentFTC.lean` (223), `LogDerivFTC.lean` (202)

**Target file:** `ForMathlib/SegmentFTC.lean`

**Key content:**
- `ftc_telescope_two`, `ftc_telescope_three` — FTC for 2-3 segment curves
- Log-derivative FTC: `∫ (f'/f) dz = log(f(b)/f(a))`

**Depends on:** PR 2 (contour integration)

---

### PR C3: Multi-Point PV Theory (~300 lines)

**Source:** `Residue/MultipointPV.lean` (640 — extract core)

**Target file:** `ForMathlib/MultipointPV.lean`

**Key content:**
- Multi-point PV integrand splitting
- `cpvIntegrandOn_sub` — subtraction of CPV integrands
- PV convergence when integrands agree off a finite set
- Relationship between single-point and multi-point CPV

**Depends on:** PR C1 (PV splitting), PRs 1-3

---

### PR C4: Simple Pole PV Integral (~300 lines)

**Source:** `Residue.lean` (729 — the integral computation part)

**Target file:** `ForMathlib/SimplePoleIntegral.lean`

**Key theorem (REAL version):**
```lean
-- PV integral of c/(z-s) = 2πi · winding · c (for simple poles)
theorem pv_integral_simple_pole
    {s c : ℂ} {γ : PiecewiseC1Immersion x y}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPV (fun z => c / (z - s)) γ s (2 * Real.pi * I * w * c)
```

This is the full version, not the watered-down one in the current PR 5.

**Depends on:** PR C1 (PV splitting), PR 4 (winding number)

---

### PR C5: Residue via Circle Integral (~300 lines)

**Source:** `Residue/GeneralizedTheoremBase.lean` (734 — extract residueAt part)

**Target file:** `ForMathlib/ResidueCircleIntegral.lean`

**Key definitions:**
- `residueAt f z₀` — via circle integral limit
- `residueAt_eq_residueSimplePole` — agrees with simple pole residue
- Basic residue calculus: additivity, zero for analytic functions

**Depends on:** PR 5 (basic residue defs)

---

### PR C6: MeromorphicAt Bridge (~200 lines)

**Source:** `Residue/MathlibBridge.lean` (215)

**Target file:** `ForMathlib/MeromorphicBridge.lean`

**Key content:**
- `HasSimplePoleAt.meromorphicAt`
- `hasSimplePoleAt_iff_meromorphicOrderAt_eq_neg_one`
- `residueAt_eq_neg_one_coeff` — residue as Laurent coefficient

**Depends on:** PR C5

---

### PR C7: Meromorphic Principal Parts (~300 lines)

**Source:** `Residue/MeromorphicPrincipalPart.lean` (545)

**Target file:** `ForMathlib/PrincipalPart.lean`

**Key definitions:**
- `meromorphicPrincipalPart f z₀` — extract Laurent principal part
- `meromorphicAt_sub_principalPart_analyticAt` — remainder is analytic

**Depends on:** PR C6

---

### PR C8: Sector Curve Analysis Part 1 (~300 lines)

**Source:** `Residue/SectorCurve.lean` (675)

**Target file:** `ForMathlib/SectorCurve.lean`

**Key content:**
- `sectorCurve` definition — model curve for crossing analysis
- Sector curve integral computations
- Asymptotic estimates near crossing points

**Depends on:** PR C2 (segment FTC)

---

### PR C9: Sector Curve Analysis Part 2 (~300 lines)

**Source:** `Residue/SectorCurveLemma.lean` (872)

**Target file:** `ForMathlib/SectorCurveLemma.lean`

**Key content:**
- Detailed sector curve lemmas
- Flatness bounds transfer
- Principal value convergence on sector curves

**Depends on:** PR C8

---

### PR C10: Flatness Conditions A'/B (~300 lines)

**Source:** `Residue/Flatness.lean` (466), `Residue/FlatnessTransfer.lean` (87)

**Target file:** `ForMathlib/FlatnessConditions.lean` (REPLACE old HigherOrderPoles.lean)

**Key definitions (EXACT from project):**
```lean
structure IsFlatOfOrder (γ : ...) (t₀ : ℝ) (n : ℕ) : Prop where
  right_flat : ...  -- deviation from tangent is o(‖γ t - γ t₀‖^n) from right
  left_flat : ...   -- same from left

def SatisfiesConditionA' (γ : PiecewiseC1Immersion x y) (f : ℂ → ℂ)
    (S0 : Finset ℂ) (poleOrder : ℂ → ℕ) : Prop := ...

structure SatisfiesConditionB (γ : PiecewiseC1Immersion x y) (f : ℂ → ℂ)
    (S0 : Finset ℂ) : Prop where
  angle_rational : ...
  laurent_compatible : ...
```

**Key theorem:**
- Conditions are automatic for simple poles

**Depends on:** PR C7 (principal parts), PR B3 (angles)

---

## GROUP D: Homological Cauchy (6 PRs)

**Depends on Groups B and C being complete.**

### PR D1: Null-Homologous Definition (~200 lines)

**Source:** `HomologicalCauchy/Basic.lean` (274)

**Target file:** `ForMathlib/NullHomologous.lean` (REPLACE existing version)

**Key definitions:**
```lean
structure IsNullHomologous (γ : PiecewiseC1Immersion x x) (U : Set ℂ) where
  closed : PiecewiseC1Path.IsClosed γ.toPiecewiseC1Path  -- i.e., x = x (trivial)
  image_subset : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ U
  winding_zero : ∀ z ∉ U, HasGeneralizedWindingNumber γ.toPiecewiseC1Path z 0
```

**Key theorem:**
- `isNullHomologous_of_convex`

**Depends on:** PR B7 (winding integrality), PR 6 (Poincare bridge)

---

### PR D2: Dixon Function Definition + H1/H2 Identity (~300 lines)

**Source:** `HomologicalCauchy/DixonProof.lean` (lines 1-640)

**Target file:** `ForMathlib/DixonDef.lean` (REPLACE existing Dixon.lean)

**Key definitions:**
- `dixonH1 f γ w` — integral of `dslope f (γ t) w` (well-defined for w ∈ U)
- `dixonH2 f γ w` — integral of `f(γ t)/(γ t - w)` (well-defined when w off curve)
- `dixonFunction f U γ w` — piecewise: h1 on U, h2 off U

**Key theorem:**
- `dixonH1_eq` — the h1/h2 identity: `h1(w) = h2(w) - 2πi · n(γ,w) · f(w)`

**Depends on:** PR D1 (null-homologous)

---

### PR D3: Dixon Differentiability (~300 lines)

**Source:** `HomologicalCauchy/DixonProof.lean` (lines 640-900)

**Target file:** `ForMathlib/DixonDiff.lean`

**Key theorems:**
- `dixonH1_differentiableOn` — h1 is holomorphic on U
- `dixonH2_differentiableAt` — h2 is holomorphic away from curve
- `dixonFunction_differentiable` — the Dixon function is ENTIRE

**Proof strategy:** h1 uses differentiation under the integral sign (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`). h2 is straightforward. Patching uses null-homologous condition: near ∂U, winding = 0 so h1 = h2.

**NOTE:** The existing `dixonFunction_differentiable` proof is 259 lines. MUST be decomposed into ≤50-line helpers.

**Depends on:** PR D2

---

### PR D4: Dixon Theorem via Liouville (~200 lines)

**Source:** `HomologicalCauchy/DixonProof.lean` (lines 900-1019)

**Target file:** `ForMathlib/DixonTheorem.lean`

**THE theorem:**
```lean
theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion x x) (h_null : IsNullHomologous γ U) :
    ∀ w, dixonFunction f U γ w = 0
```

**Proof:** dixonFunction is entire (PR D3) + bounded (norm estimates) + tends to 0 at ∞ → identically 0 by Liouville.

**Also includes:**
- `cauchyIntegralFormula_nullHomologous` — ∮ f(z)/(z-w) = 2πi · n(γ,w) · f(w)

**Depends on:** PR D3

---

### PR D5: Meromorphic Cauchy (~300 lines)

**Source:** `HomologicalCauchy/Meromorphic.lean` (487)

**Target file:** `ForMathlib/MeromorphicCauchy.lean` (REPLACE existing HomologicalCauchy.lean)

**Key theorems:**
```lean
-- Single pole: holomorphic contour integral vanishes
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_nh ...

-- Multiple poles: induction on pole count
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh ...

-- Higher-order cancellation with conditions A'/B
theorem conditionsAB_imply_higherOrderCancel_nh ...
```

**Depends on:** PR D4 (Dixon), PR C10 (flatness conditions)

---

### PR D6: PV Infrastructure for Higher-Order Poles (~300 lines)

**Source:** `PVInfrastructure/` (3605 lines — extract what's needed for the main theorem)

**Target file:** `ForMathlib/PVHigherOrder.lean`

**Key content:**
- Uniform step bounds for PV integrals near higher-order poles
- Annulus bound estimates
- Assembly framework: `higherOrderCancel_assembly_abstract`

**NOTE:** The PVInfrastructure is 3600 lines. Only extract what's directly needed for the assembly in PR E1. If the full infrastructure doesn't fit in 300 lines, split into multiple PRs (D6a, D6b, ...).

**Depends on:** PR C8-C9 (sector curves), PR C3 (multi-point PV)

---

## GROUP E: Main Theorems (3 PRs)

### PR E1: Higher-Order Cancellation Assembly (~300 lines)

**Source:** `GeneralizedResidueTheorem.lean` (lines 62-210 — the assembly part)

**Target file:** `ForMathlib/HigherOrderAssembly.lean`

**Key theorem:**
- `higherOrderCancel_assembly` — CPV(f) - CPV(f_res) → 0 using Dixon + conditions A'/B

**Depends on:** PR D5 (meromorphic Cauchy), PR D6 (PV infrastructure)

---

### PR E2: Generalized Residue Theorem — HW Theorem 3.3 (~300 lines)

**Source:** `GeneralizedResidueTheorem.lean` (355)

**Target file:** `ForMathlib/GeneralizedResidueTheorem.lean` (REPLACE existing version)

**THE theorem (FULL, non-negotiable):**
```lean
theorem generalizedResidueTheorem (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc (0:ℝ) 1, γ t ∈ S → γ t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (h_no_endpt_cross : ∀ s ∈ S0, γ 0 ≠ s ∧ γ 1 ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc (0:ℝ) 1, ∀ t₂ ∈ Icc (0:ℝ) 1,
      γ t₁ = s → γ t₂ = s → t₁ = t₂) :
    HasCauchyPVOn S0 f γ.toPiecewiseC1Path
      (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residueAt f s)
```

**Also includes:**
- `generalizedResidueTheorem_simplePoles` — corollary for simple poles (conditions drop out)

**Depends on:** PR E1

---

### PR E3: Cycle Versions (~260 lines)

**Source:** `Cycle.lean` (260)

**Target file:** `ForMathlib/Cycles.lean`

**Key content:**
- `ContourCycle` — ℤ-linear combinations of immersions
- `contourIntegralCycle`, `windingNumberCycle`, `cpvCycle`
- `generalizedResidueTheorem_cycle` — cycle version of HW 3.3
- `windingNumberCycle_isInt`

**Depends on:** PR E2

---

## GROUP F: Valence Formula (8 PRs)

### PR F1: Elliptic Points and Order Definitions (~150 lines)

**Source:** `ValenceFormula/Definitions.lean` (108)

**Target file:** `ForMathlib/EllipticDefs.lean` (REPLACE existing EllipticWeights.lean)

**Key content:**
- `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'` — as UpperHalfPlane
- `orderOfVanishingAt'` — via `meromorphicOrderAt`
- `orderAtCusp'` — via q-expansion order

**Depends on:** mathlib `ModularForm`

---

### PR F2: Modular Invariance (~300 lines)

**Source:** `ValenceFormula/ModularInvariance.lean` (386)

**Target file:** `ForMathlib/ModularInvariance.lean`

**Key theorems:**
- `ord_add_one_eq` — T-invariance of orders
- `ord_S_eq` — S-invariance of orders
- `modularForm_finitely_many_zeros_in_fdBox` — finiteness in bounded box

**Depends on:** PR F1

---

### PR F3: Orbits and Finiteness (~260 lines)

**Source:** `ValenceFormula/OrbitSum.lean` (258)

**Target file:** `ForMathlib/Orbits.lean`

**Key content:**
- `Orbit`, `orb`, `oi`, `orho` — SL₂(ℤ) orbit quotient
- `NonEllOrbit` — subtype excluding elliptic orbits
- `ordOrbit` — order lifted to orbits (well-defined by `ord_smul_eq`)
- `s₀` — zero set in fundamental domain
- `finite_zeros_in_fd`, `finite_support_ordOrbit`

**Depends on:** PR F2

---

### PR F4: FD Boundary and Winding Weights (~300 lines)

**Source:** `ValenceFormula/Boundary/` + `ValenceFormula/WindingWeights/` (3000+ lines total)

**Target file:** `ForMathlib/FDBoundaryWinding.lean` (REPLACE existing FDBoundary.lean)

**Key content:**
- FD boundary as `PiecewiseC1Immersion` (5 segments, reparametrized to [0,1])
- SingleCrossing instantiations for i (→ -1/2), ρ (→ -1/6), ρ+1 (→ -1/6)
- Interior winding = -1 (via homotopy)

**NOTE:** The winding weight computations are ~3000 lines in the existing code. This PR extracts the KEY results and their direct proofs. May need splitting into F4a (boundary def), F4b (winding weights), F4c (interior winding).

**Depends on:** PR 4b (SingleCrossing), PR B5 (homotopy invariance)

---

### PR F5: Orbit Pairing (~300 lines)

**Source:** `ValenceFormula/OrbitPairing.lean` (319)

**Target file:** `ForMathlib/OrbitPairing.lean` (REPLACE existing)

**Key content:**
- T-periodicity: left + right vertical integrals cancel
- S-transformation on arcs
- `sLeftVert` — left-vertical point filter
- `ord_rho_plus_one_eq_ord_rho`

**Depends on:** PR F1, mathlib `SlashAction`

---

### PR F6: Canonical Representatives (~225 lines)

**Source:** `ValenceFormula/TextbookExistence.lean` (225)

**Target file:** `ForMathlib/CanonicalReps.lean`

**Key content:**
- `repStrict`, `repLeftVert`, `repLeftArc` — canonical representative finsets
- `repCanon` — union of the three
- `exists_repCanon_of_nonEllOrbit` — every non-elliptic orbit with nonzero order has a rep
- Injectivity of `orb` on `repCanon`

**Depends on:** PR F3 (orbits), PR F5 (orbit pairing)

---

### PR F7: Core Identity (~300 lines)

**Source:** `ValenceFormula/CoreIdentity.lean` (531)

**Target file:** `ForMathlib/ValenceCore.lean` (REPLACE existing ValenceFormulaCore.lean)

**THE theorem:**
```lean
theorem valence_formula_orbit_sum (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (...), ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (...), ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12
```

**Depends on:** PR E2 (generalized residue theorem), PR F4 (FD boundary + winding), PR F5 (orbit pairing)

---

### PR F8: Textbook Valence Formula (~300 lines)

**Source:** `ValenceFormula/TextbookForm.lean` (506)

**Target file:** `ForMathlib/ValenceTextbook.lean` (REPLACE existing ValenceFormulaTextbook.lean)

**THE theorem (EXACT, non-negotiable):**
```lean
theorem valence_formula_textbook_orbit_finsum :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12
```

**Also includes:**
- `finsum_nonell_eq_repCanon_sum` — bridge finsum to Finset sum
- `repCanon_sum_split` — split into strict + leftVert + leftArc
- `orb_injOn_repCanon` — injectivity

**Depends on:** PR F7 (core identity), PR F6 (canonical reps)

---

## Summary

| Group | PRs | Est. Lines | Parallel? |
|-------|-----|-----------|-----------|
| A (done) | 1-6, 4b | 1345 | Done |
| B (winding) | B1-B8 | ~2100 | YES — parallel with C |
| C (residue) | C1-C10 | ~2800 | YES — parallel with B |
| D (homological) | D1-D6 | ~1600 | After B+C |
| E (main thms) | E1-E3 | ~860 | After D |
| F (valence) | F1-F8 | ~2235 | After E |
| **Total** | **~35 PRs** | **~10,940** | |

## Ticket System for Parallel Work

### Worker 1: Winding Number Track
```
B1 → B2 → B3
B4 → B5 → B6 → B7 → B8
(B1-B3 and B4-B8 are sub-parallel within this track)
```

### Worker 2: Residue Track
```
C1 → C3
C2 → C8 → C9
C4
C5 → C6 → C7 → C10
(Several sub-chains within this track)
```

### Worker 3 (after B+C complete): Merge Track
```
D1 → D2 → D3 → D4 → D5 → D6 → E1 → E2 → E3
```

### Worker 4 (after E complete): Valence Track
```
F1 → F2 → F3 → F5 → F6
F4 (depends on B5 + 4b)
F7 (depends on E2 + F4 + F5)
F8 (depends on F7 + F6)
```

### Dependency DAG (for ticket system)

```
A(done) ──┬── B1 → B2 → B3 ─────────────────────────────────┐
          │                                                    │
          ├── B4 → B5 → B6 → B7                              │
          │         │                                          │
          │         └──────→ B8                               │
          │                                                    │
          ├── C1 → C3 ──────────────────────────────────┐     │
          │                                              │     │
          ├── C2 → C8 → C9 ────────────────────────┐    │     │
          │                                         │    │     │
          ├── C4 ──────────────────────────────┐    │    │     │
          │                                    │    │    │     │
          └── C5 → C6 → C7 → C10 ────────┐   │    │    │     │
                                           │   │    │    │     │
                                           └───┴────┴────┴─→ D1
                                                              │
                                     D1 → D2 → D3 → D4 → D5 → D6
                                                                │
                                                    E1 → E2 → E3
                                                          │
                              F1 → F2 → F3 → F5 → F6     │
                                              │           │
                              F4 ─────────────┴───→ F7 → F8
```
