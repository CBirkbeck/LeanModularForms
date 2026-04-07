# Mathlib PR Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build all 20 mathlib PRs as self-contained files in `LeanModularForms/ForMathlib/` that import only from mathlib + earlier ForMathlib files, ready for eventual submission.

**Architecture:** Each PR = one file under `ForMathlib/`. Files are self-contained (no imports from the existing project code). Proofs are adapted from existing working code in `GeneralizedResidueTheory/` and `ValenceFormula/`, decomposed to ≤50 lines each. API follows Tendsto-first pattern.

**Tech Stack:** Lean 4, Mathlib v4.29.0-rc8

**Spec:** `docs/superpowers/specs/2026-04-07-mathlib-pr-plan-design.md`

---

## File Structure

All new files go under `LeanModularForms/ForMathlib/`:

```
ForMathlib/
  PiecewiseC1Path.lean              -- PR 1: curves
  PiecewiseContourIntegral.lean     -- PR 2: integration
  CauchyPrincipalValue.lean         -- PR 3: CPV
  GeneralizedWindingNumber.lean     -- PR 4: winding number
  SingleCrossing.lean               -- PR 4b: crossing framework
  WindingDecomposition.lean          -- PR 8: Prop 2.2+2.3
  Residue.lean                      -- PR 5: residue defs
  PoincareBridge.lean               -- PR 6: convex primitives
  HomotopyInvariance.lean           -- PR 7: homotopy
  NullHomologous.lean               -- PR 9: cycles
  Dixon.lean                        -- PR 10: Dixon theorem
  HomologicalCauchy.lean            -- PR 11: meromorphic Cauchy
  HigherOrderPoles.lean             -- PR 12: conditions A'/B
  GeneralizedResidueTheorem.lean    -- PR 13: main theorem
  FDBoundary.lean                   -- V1: FD contour
  InteriorWinding.lean              -- V2: winding = -1
  EllipticWeights.lean              -- V3: winding at i,ρ,ρ+1
  OrbitPairing.lean                 -- V4: T/S invariance
  ValenceFormulaCore.lean           -- V5: core identity
  ValenceFormulaTextbook.lean       -- V6: textbook form
```

Existing `ForMathlib/` files (SlashActions.lean, etc.) are untouched.

---

## Phase 1: Foundation (sequential)

### Task 1: PR 1 — Piecewise C1 Paths

**Files:**
- Create: `LeanModularForms/ForMathlib/PiecewiseC1Path.lean`
- Source: `GeneralizedResidueTheory/Basic.lean:30-57`

- [ ] **Step 1: Create file with imports and module doc**

```lean
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Path

/-!
# Piecewise C¹ Paths

Piecewise continuously differentiable paths in the complex plane, extending
mathlib's `Path` with a finite partition where the derivative may be discontinuous.

## Main definitions

* `PiecewiseC1Path` — extends `Path` with C¹ structure off a finite partition
* `PiecewiseC1Immersion` — piecewise C¹ path with nonzero derivative
-/
```

- [ ] **Step 2: Define PiecewiseC1Path wrapping mathlib Path**

The key change from existing code: we wrap `Path x y` (parametrized on `[0,1]`)
instead of using arbitrary `[a,b]`. Use `Set.Icc (0:ℝ) 1` as the domain.

```lean
open Complex Set Filter Topology

noncomputable section

/-- A piecewise continuously differentiable path from `x` to `y` in `ℂ`.
Extends mathlib's `Path` with a finite set of breakpoints where the derivative
may be discontinuous. The path is C¹ on each subinterval between breakpoints. -/
structure PiecewiseC1Path (x y : ℂ) extends Path x y where
  /-- Finite set of breakpoints in `[0, 1]` where smoothness may fail. -/
  partition : Finset (Set.Icc (0:ℝ) 1)
  /-- The path is differentiable at all non-partition points in the interior. -/
  differentiableAt_off_partition :
    ∀ t : ℝ, t ∈ Ioo 0 1 → (⟨t, ⟨le_of_lt (mem_Ioo.mp ‹_›).1,
      le_of_lt (mem_Ioo.mp ‹_›).2⟩⟩ : Set.Icc (0:ℝ) 1) ∉ partition →
    DifferentiableAt ℝ (fun s => toPath.extend s) t
  /-- The derivative is continuous at all non-partition interior points. -/
  continuousAt_deriv_off_partition :
    ∀ t : ℝ, t ∈ Ioo 0 1 → (⟨t, ⟨le_of_lt (mem_Ioo.mp ‹_›).1,
      le_of_lt (mem_Ioo.mp ‹_›).2⟩⟩ : Set.Icc (0:ℝ) 1) ∉ partition →
    ContinuousAt (deriv (fun s => toPath.extend s)) t
```

Note: The exact signature will need iteration during implementation. The key
design constraint is: wrap `Path`, use `[0,1]`, partition is `Finset` of
subtype elements. Adapt from `Basic.lean:30-41` but reparametrize.

- [ ] **Step 3: Define PiecewiseC1Immersion**

```lean
/-- A piecewise C¹ immersion: a piecewise C¹ path with nonzero derivative
away from partition points, and nonzero one-sided limits at partition points. -/
structure PiecewiseC1Immersion (x y : ℂ) extends PiecewiseC1Path x y where
  /-- Nonzero derivative at all non-partition points. -/
  deriv_ne_zero_off_partition :
    ∀ t : ℝ, t ∈ Ioo 0 1 → ... ∉ partition →
    deriv (fun s => toPath.extend s) t ≠ 0
  /-- Left derivative limit exists and is nonzero at each partition point. -/
  left_deriv_limit : ∀ p ∈ partition, (0 : ℝ) < (p : ℝ) →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv (fun s => toPiecewiseC1Path.toPath.extend s))
      (𝓝[<] (p : ℝ)) (𝓝 L)
  /-- Right derivative limit exists and is nonzero at each partition point. -/
  right_deriv_limit : ∀ p ∈ partition, (p : ℝ) < 1 →
    ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv (fun s => toPiecewiseC1Path.toPath.extend s))
      (𝓝[>] (p : ℝ)) (𝓝 L)
```

Adapt from `Basic.lean:51-56`. The key change is `Path.extend` instead of bare `toFun`.

- [ ] **Step 4: Add basic API**

```lean
/-- A piecewise C¹ path is closed when source = target. -/
def PiecewiseC1Path.IsClosed {x y : ℂ} (γ : PiecewiseC1Path x y) : Prop := x = y

/-- Translate a path by a constant. -/
def PiecewiseC1Path.translate {x y : ℂ} (γ : PiecewiseC1Path x y) (c : ℂ) :
    PiecewiseC1Path (x + c) (y + c) := ...

instance {x y : ℂ} : CoeFun (PiecewiseC1Path x y) fun _ => ℝ → ℂ where
  coe γ := fun t => γ.toPath.extend t
```

Adapt `translate` from `WindingNumber/Defs.lean:144`.

- [ ] **Step 5: Verify compilation**

Run: `lake build LeanModularForms.ForMathlib.PiecewiseC1Path`
Expected: Success with 0 errors, 0 sorry

- [ ] **Step 6: Commit**

```bash
git add LeanModularForms/ForMathlib/PiecewiseC1Path.lean
git commit -m "feat(ForMathlib): PR 1 — piecewise C1 paths wrapping mathlib Path"
```

---

### Task 2: PR 2 — Contour Integration

**Files:**
- Create: `LeanModularForms/ForMathlib/PiecewiseContourIntegral.lean`
- Source: `GeneralizedResidueTheory/Basic.lean`, `ContourIntegral/SegmentFTC.lean`

- [ ] **Step 1: Create file with contourIntegral definition**

```lean
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.MeasureTheory.Integral.IntervalIntegral

/-- The contour integral of `f` along a piecewise C¹ path `γ`:
`∮_γ f(z) dz = ∫₀¹ f(γ(t)) · γ'(t) dt`. -/
noncomputable def contourIntegral (f : ℂ → ℂ) {x y : ℂ}
    (γ : PiecewiseC1Path x y) : ℂ :=
  ∫ t in (0:ℝ)..1, f (γ.toPath.extend t) * deriv (fun s => γ.toPath.extend s) t
```

- [ ] **Step 2: Add linearity and bound theorems**

Key theorems to adapt:
- `contourIntegral_add` — linearity in f
- `contourIntegral_norm_le` — sup norm × arc length bound
- `contourIntegral_eq_sum_segments` — decompose over partition

These are standard and short. Adapt from interval integral properties.

- [ ] **Step 3: Add FTC telescope theorem**

```lean
/-- Fundamental theorem of calculus for piecewise C¹ paths:
if `F' = f` along the path, then `∮_γ f dz = F(y) - F(x)`. -/
theorem contourIntegral_eq_sub_of_hasDerivAt {f F : ℂ → ℂ} {x y : ℂ}
    (γ : PiecewiseC1Path x y)
    (hF : ∀ z ∈ γ.toPath.range, HasDerivAt F (f z) z) :
    contourIntegral f γ = F y - F x := by
  ...
```

Adapt from `ContourIntegral/SegmentFTC.lean`. Decompose into per-segment FTC
then telescope. Key helper: `integral_add_adjacent_intervals`.

- [ ] **Step 4: Verify compilation**

Run: `lake build LeanModularForms.ForMathlib.PiecewiseContourIntegral`
Expected: Success with 0 errors, 0 sorry

- [ ] **Step 5: Commit**

```bash
git add LeanModularForms/ForMathlib/PiecewiseContourIntegral.lean
git commit -m "feat(ForMathlib): PR 2 — contour integration for piecewise C1 paths"
```

---

### Task 3: PR 3 — Cauchy Principal Value

**Files:**
- Create: `LeanModularForms/ForMathlib/CauchyPrincipalValue.lean`
- Source: `GeneralizedResidueTheory/Basic.lean:59-86`, `Residue.lean:38-59`

- [ ] **Step 1: Create file with Tendsto-first single-point CPV**

```lean
import LeanModularForms.ForMathlib.PiecewiseContourIntegral

/-! ## Single-point Cauchy principal value -/

/-- The ε-cutoff integrand for a Cauchy principal value integral. -/
def cpvIntegrand (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

/-- The Cauchy principal value integral exists with limit `L`.
This is the PRIMARY API — use this for all downstream theorems. -/
def HasCauchyPV (f : ℂ → ℂ) {x y : ℂ} (γ : PiecewiseC1Path x y)
    (z₀ : ℂ) (L : ℂ) : Prop :=
  Tendsto (fun ε => ∫ t in (0:ℝ)..1,
    cpvIntegrand f (fun t => γ.toPath.extend t) z₀ ε t)
    (𝓝[>] 0) (𝓝 L)

/-- The Cauchy principal value (junk value when limit doesn't exist). -/
noncomputable def cauchyPV (f : ℂ → ℂ) {x y : ℂ} (γ : PiecewiseC1Path x y)
    (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => ∫ t in (0:ℝ)..1,
    cpvIntegrand f (fun t => γ.toPath.extend t) z₀ ε t

/-- Bridge: if `HasCauchyPV` holds, then `cauchyPV` equals the limit. -/
theorem HasCauchyPV.cauchyPV_eq {f : ℂ → ℂ} {x y : ℂ}
    {γ : PiecewiseC1Path x y} {z₀ L : ℂ}
    (h : HasCauchyPV f γ z₀ L) : cauchyPV f γ z₀ = L :=
  h.limUnder_eq
```

Adapt definitions from `Basic.lean:59-85`, reparametrizing to `[0,1]`.

- [ ] **Step 2: Add multi-point CPV with Tendsto-first API**

```lean
/-! ## Multi-point Cauchy principal value -/

/-- Multi-point ε-cutoff integrand: zero near any s in S. -/
def cpvIntegrandOn (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (ε : ℝ) (t : ℝ) : ℂ :=
  if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t

/-- Multi-point CPV exists with limit `L`. PRIMARY API. -/
def HasCauchyPVOn (S : Finset ℂ) (f : ℂ → ℂ) {x y : ℂ}
    (γ : PiecewiseC1Path x y) (L : ℂ) : Prop :=
  Tendsto (fun ε => ∫ t in (0:ℝ)..1,
    cpvIntegrandOn S f (fun t => γ.toPath.extend t) ε t)
    (𝓝[>] 0) (𝓝 L)

/-- Multi-point CPV value. -/
noncomputable def cauchyPVOn (S : Finset ℂ) (f : ℂ → ℂ) {x y : ℂ}
    (γ : PiecewiseC1Path x y) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => ∫ t in (0:ℝ)..1,
    cpvIntegrandOn S f (fun t => γ.toPath.extend t) ε t

/-- Bridge: HasCauchyPVOn → cauchyPVOn equals limit. -/
theorem HasCauchyPVOn.cauchyPVOn_eq ... := ...
```

Adapt from `Residue.lean:38-59`.

- [ ] **Step 3: Add algebraic API on HasCauchyPV**

```lean
theorem HasCauchyPV.add (hf : HasCauchyPV f γ z₀ L₁)
    (hg : HasCauchyPV g γ z₀ L₂) :
    HasCauchyPV (f + g) γ z₀ (L₁ + L₂) := by
  -- Tendsto.add on the underlying filter limits
  ...

theorem HasCauchyPV.smul (c : ℂ) (hf : HasCauchyPV f γ z₀ L) :
    HasCauchyPV (c • f) γ z₀ (c * L) := ...

theorem hasCauchyPV_of_avoids {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (h : ∀ t ∈ Icc 0 1, γ.toPath.extend t ≠ z₀) :
    HasCauchyPV f γ z₀ (contourIntegral f γ) := ...
```

- [ ] **Step 4: Add integrability lemma**

Adapt `cpv_integrand_intervalIntegrable` from `WindingNumber/Proposition2_2.lean`.
This is currently 287 lines — MUST be decomposed into ~6 helper lemmas of ≤40 lines.

Key helpers to extract:
- `cpvIntegrand_measurable` — measurability of the cutoff integrand
- `cpvIntegrand_ae_stronglyMeasurable`
- `cpvIntegrand_norm_le` — pointwise bound
- `cpvIntegrand_integrable_of_continuous` — when f·γ' is continuous

- [ ] **Step 5: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.CauchyPrincipalValue`

```bash
git add LeanModularForms/ForMathlib/CauchyPrincipalValue.lean
git commit -m "feat(ForMathlib): PR 3 — Cauchy principal value with Tendsto-first API"
```

---

## Phase 2: Parallel Tracks (PRs 4, 5, 6, 7 — can be developed concurrently)

### Task 4: PR 4 — Generalized Winding Number

**Files:**
- Create: `LeanModularForms/ForMathlib/GeneralizedWindingNumber.lean`
- Source: `Basic.lean:89-91`, `Homotopy/MathlibBridge.lean`

- [ ] **Step 1: Define HasGeneralizedWindingNumber (Tendsto-first)**

```lean
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-- The generalized winding number of `γ` around `z₀` equals `w`.
Defined via CPV of `(z - z₀)⁻¹`. PRIMARY API. -/
def HasGeneralizedWindingNumber {x y : ℂ} (γ : PiecewiseC1Path x y)
    (z₀ : ℂ) (w : ℂ) : Prop :=
  HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ (2 * ↑Real.pi * I * w)

/-- The generalized winding number value (junk when CPV doesn't exist). -/
noncomputable def generalizedWindingNumber {x y : ℂ}
    (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * cauchyPV (fun z => (z - z₀)⁻¹) γ z₀

/-- Bridge: HasGeneralizedWindingNumber → value equals w. -/
theorem HasGeneralizedWindingNumber.eq (h : HasGeneralizedWindingNumber γ z₀ w) :
    generalizedWindingNumber γ z₀ = w := ...
```

- [ ] **Step 2: Bridge to mathlib circleIntegral**

Adapt `generalizedWindingNumber_circleMap_eq_one_of_mem_ball` from
`Homotopy/MathlibBridge.lean:125`. Key: for `z₀` inside a circle, winding = 1.

```lean
/-- For a circle traversed counterclockwise containing z₀, winding number = 1. -/
theorem hasGeneralizedWindingNumber_circle_eq_one {z₀ c : ℂ} {R : ℝ}
    (hR : 0 < R) (hz : z₀ ∈ Metric.ball c R)
    (γ : PiecewiseC1Path ... ) -- circle path
    : HasGeneralizedWindingNumber γ z₀ 1 := ...
```

- [ ] **Step 3: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.GeneralizedWindingNumber`

```bash
git add LeanModularForms/ForMathlib/GeneralizedWindingNumber.lean
git commit -m "feat(ForMathlib): PR 4 — generalized winding number via CPV"
```

---

### Task 5: PR 5 — Residue Definitions

**Files:**
- Create: `LeanModularForms/ForMathlib/Residue.lean`
- Source: `Residue.lean:63-71`, `Residue/GeneralizedTheoremBase.lean:516`,
  `Residue/MathlibBridge.lean`

- [ ] **Step 1: Define HasSimplePoleAt and residue**

```lean
import LeanModularForms.ForMathlib.CauchyPrincipalValue
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-- Simple pole decomposition: `f(z) = c/(z-z₀) + g(z)` near `z₀` with `g` analytic. -/
def HasSimplePoleAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ c : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z

/-- The residue of `f` at `z₀`, defined via contour integral:
`Res(f, z₀) = (2πi)⁻¹ · lim_{r→0⁺} ∮_{|z-z₀|=r} f(z) dz`. -/
noncomputable def residue (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r =>
    (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(z₀, r), f z
```

Adapt from `Residue.lean:63-70` and `GeneralizedTheoremBase.lean:516`.

- [ ] **Step 2: Bridge to MeromorphicAt**

```lean
/-- A simple pole at z₀ ↔ meromorphic order = -1. -/
theorem hasSimplePoleAt_iff_meromorphicOrderAt_eq_neg_one
    {f : ℂ → ℂ} {z₀ : ℂ} (hf : MeromorphicAt f z₀) :
    HasSimplePoleAt f z₀ ↔ meromorphicOrderAt f z₀ = (-1 : ℤ) := ...
```

Adapt from `Residue/MathlibBridge.lean`.

- [ ] **Step 3: PV of simple pole = winding × residue**

```lean
/-- PV integral of `c/(z-s)` along γ equals `2πi · windingNumber · c`. -/
theorem HasCauchyPV.simple_pole {c : ℂ} {s : ℂ}
    {γ : PiecewiseC1Path x y}
    (hw : HasGeneralizedWindingNumber γ s w) :
    HasCauchyPV (fun z => c / (z - s)) γ s (2 * ↑Real.pi * I * w * c) := ...
```

Adapt from `Residue.lean:~400` (`integral_singular_term_eq_winding_times_coeff`, 113 lines).
Decompose into ≤3 helper lemmas.

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.Residue`

```bash
git add LeanModularForms/ForMathlib/Residue.lean
git commit -m "feat(ForMathlib): PR 5 — residue definitions bridging MeromorphicAt"
```

---

### Task 6: PR 6 — Poincare Bridge

**Files:**
- Create: `LeanModularForms/ForMathlib/PoincareBridge.lean`
- Source: `CauchyPrimitive.lean:425`

- [ ] **Step 1: Bridge holomorphic → closed 1-form**

```lean
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-- A holomorphic function on a convex set induces a closed 1-form. -/
theorem DifferentiableOn.closedForm_of_convex {U : Set ℂ} {f : ℂ → ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U) :
    -- Bridge to Poincare lemma's 1-form framework
    ... := ...
```

This requires understanding the Poincare lemma's exact API. Read
`.lake/packages/mathlib/Mathlib/MeasureTheory/Integral/CurveIntegral/Poincare.lean`
to determine exact types and adapt.

- [ ] **Step 2: Specialize to complex primitive existence**

```lean
/-- Holomorphic functions on convex open sets have holomorphic primitives.
Specializes the Poincaré lemma to complex analysis. -/
theorem DifferentiableOn.hasPrimitive_of_convex {U : Set ℂ} {f : ℂ → ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F U ∧
      ∀ z ∈ U, HasDerivAt F (f z) z := ...
```

If the Poincare bridge is too difficult, fall back to adapting the direct proof
from `CauchyPrimitive.lean:425` (`holomorphic_convex_primitive`, 11 lines).

- [ ] **Step 3: Cauchy theorem on convex domains**

```lean
/-- Cauchy's theorem for convex domains: integral of holomorphic function
along closed piecewise C¹ curve = 0. -/
theorem contourIntegral_eq_zero_of_differentiableOn_convex
    {U : Set ℂ} {f : ℂ → ℂ} {x : ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Path x x) -- closed
    (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t ∈ U) :
    contourIntegral f γ = 0 := by
  obtain ⟨F, _, hF⟩ := hf.hasPrimitive_of_convex hU hUo
  rw [contourIntegral_eq_sub_of_hasDerivAt γ (fun z hz => hF z (... hz))]
  simp
```

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.PoincareBridge`

```bash
git add LeanModularForms/ForMathlib/PoincareBridge.lean
git commit -m "feat(ForMathlib): PR 6 — convex domain primitives via Poincare lemma"
```

---

### Task 7: PR 7 — Homotopy Invariance

**Files:**
- Create: `LeanModularForms/ForMathlib/HomotopyInvariance.lean`
- Source: `Homotopy/Invariance.lean`

- [ ] **Step 1: Define PiecewiseHomotopy**

```lean
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.PoincareBridge

/-- A piecewise C¹ homotopy between paths within a set `U`,
avoiding a point `z₀`. -/
structure PiecewiseHomotopy {x y : ℂ} (γ₁ γ₂ : PiecewiseC1Path x y)
    (U : Set ℂ) where
  /-- The homotopy map H : [0,1] × [0,1] → ℂ. -/
  toFun : ℝ × ℝ → ℂ
  continuous_toFun : Continuous toFun
  map_zero : ∀ t ∈ Icc 0 1, toFun (t, 0) = γ₁.toPath.extend t
  map_one : ∀ t ∈ Icc 0 1, toFun (t, 1) = γ₂.toPath.extend t
  endpoints_fixed : ∀ s ∈ Icc 0 1, toFun (0, s) = x ∧ toFun (1, s) = y
  image_subset : ∀ p ∈ Icc 0 1 ×ˢ Icc 0 1, toFun p ∈ U
```

Adapt from `Homotopy/Invariance.lean`.

- [ ] **Step 2: Winding number homotopy invariance**

```lean
/-- Winding number is invariant under homotopy avoiding z₀. -/
theorem HasGeneralizedWindingNumber.eq_of_homotopy
    (γ₁ γ₂ : PiecewiseC1Path x y)
    (H : PiecewiseHomotopy γ₁ γ₂ (U \ {z₀}))
    (hw₁ : HasGeneralizedWindingNumber γ₁ z₀ w) :
    HasGeneralizedWindingNumber γ₂ z₀ w := ...
```

Adapt from `Invariance.lean:304` (`windingNumber_eq_of_piecewise_homotopic`, 138 lines).
Decompose into ~3 helpers.

- [ ] **Step 3: Contour integral homotopy invariance**

```lean
/-- Contour integral is invariant under homotopy in the domain of holomorphy. -/
theorem contourIntegral_eq_of_homotopy
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (γ₁ γ₂ : PiecewiseC1Path x y)
    (H : PiecewiseHomotopy γ₁ γ₂ U) :
    contourIntegral f γ₁ = contourIntegral f γ₂ := ...
```

Adapt from `Invariance.lean:548` (65 lines).

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.HomotopyInvariance`

```bash
git add LeanModularForms/ForMathlib/HomotopyInvariance.lean
git commit -m "feat(ForMathlib): PR 7 — homotopy invariance of contour integrals"
```

---

## Phase 3: PR 4b + PR 8

### Task 8: PR 4b — Single-Crossing Framework

**Files:**
- Create: `LeanModularForms/ForMathlib/SingleCrossing.lean`
- Source: `ValenceFormula/Boundary/Winding/Framework.lean` (158 lines),
  `ContourIntegral/CrossingLimit.lean`

- [ ] **Step 1: Copy and adapt SingleCrossingData structure**

The existing `SingleCrossingData` and `pv_tendsto_of_crossing_limit` are already
well-factored. Adapt to use the new `HasCauchyPV`/`HasGeneralizedWindingNumber` API.

```lean
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-- Data for computing the generalized winding number at a single crossing point.
Bundles all geometric ingredients for `pv_tendsto_of_crossing_limit`. -/
structure SingleCrossingData {x y : ℂ} (γ : PiecewiseC1Path x y) (z₀ : ℂ) where
  /-- Target PV limit value. -/
  L : ℂ
  /-- Unique crossing parameter in `(0, 1)`. -/
  t₀ : ℝ
  ht₀ : t₀ ∈ Ioo 0 1
  /-- Cutoff function: norm threshold → parameter radius. -/
  δ : ℝ → ℝ
  threshold : ℝ
  hthresh : 0 < threshold
  hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε
  hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀)
  h_far : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ.toPath.extend t - z₀‖
  h_near : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, |t - t₀| ≤ δ ε → ‖γ.toPath.extend t - z₀‖ ≤ ε
  E : ℝ → ℂ
  h_ftc : ∀ ε, 0 < ε → ε < threshold →
    (∫ t in (0:ℝ)..(t₀ - δ ε), ...) + (∫ t in (t₀ + δ ε)..1, ...) = E ε
  hint_left : ...
  hint_right : ...
  h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)
```

Adapt from `Framework.lean:57-93`. Key change: `[0,1]` instead of `[a,b]`,
`PiecewiseC1Path` instead of bare `γ : ℝ → ℂ`.

- [ ] **Step 2: Add AsymmetricCrossingData**

```lean
/-- Asymmetric crossing data: left and right cutoffs differ.
Needed for corners (e.g., arc meets line segment at ρ). -/
structure AsymmetricCrossingData {x y : ℂ} (γ : PiecewiseC1Path x y)
    (z₀ : ℂ) where
  L : ℂ
  t₀ : ℝ
  ht₀ : t₀ ∈ Ioo 0 1
  δ_left : ℝ → ℝ
  δ_right : ℝ → ℝ
  ...
```

Adapt from `CrossingLimit.lean:81` (`pv_tendsto_of_crossing_limit_asymmetric`).

- [ ] **Step 3: Master theorems**

```lean
/-- Master theorem: SingleCrossingData gives HasGeneralizedWindingNumber. -/
theorem SingleCrossingData.hasWindingNumber
    (D : SingleCrossingData γ z₀) :
    HasGeneralizedWindingNumber γ z₀ (D.L / (2 * ↑Real.pi * I)) := ...

/-- Specialization: L = -πi gives winding = -1/2. -/
theorem SingleCrossingData.windingNumber_neg_half
    (D : SingleCrossingData γ z₀) (hL : D.L = -(↑Real.pi * I)) :
    HasGeneralizedWindingNumber γ z₀ (-1/2) := ...

/-- Specialization: L = -πi/3 gives winding = -1/6. -/
theorem SingleCrossingData.windingNumber_neg_sixth
    (D : SingleCrossingData γ z₀) (hL : D.L = -(↑Real.pi / 3 * I)) :
    HasGeneralizedWindingNumber γ z₀ (-1/6) := ...
```

Adapt from `Framework.lean:132-155`.

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.SingleCrossing`

```bash
git add LeanModularForms/ForMathlib/SingleCrossing.lean
git commit -m "feat(ForMathlib): PR 4b — single-crossing winding computation framework"
```

---

### Task 9: PR 8 — Winding Decomposition

**Files:**
- Create: `LeanModularForms/ForMathlib/WindingDecomposition.lean`
- Source: `WindingNumber/Proposition2_2.lean`, `WindingNumber/Decomposition.lean`,
  `WindingNumber/Defs.lean`

- [ ] **Step 1: Crossing set definitions (Prop 2.2)**

```lean
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-- The crossing set: parameter values where γ passes through z₀. -/
noncomputable def crossingSet {x y : ℂ} (γ : PiecewiseC1Immersion x y)
    (z₀ : ℂ) : Finset ℝ := ...

/-- The crossing set is finite for immersions. -/
theorem crossingSet_finite ... := ...

/-- Each crossing is isolated. -/
theorem crossing_isolated ... := ...
```

Adapt from `Proposition2_2.lean` (747 lines). Extract key results, decompose
`cpv_integrand_intervalIntegrable` (287 lines) into helpers.

- [ ] **Step 2: Angle and decomposition definitions (Prop 2.3)**

```lean
/-- Signed angle at a crossing point. -/
noncomputable def angleAtCrossing {x y : ℂ}
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ) (t : ℝ) : ℝ := ...

/-- External winding contribution (integer-valued). -/
noncomputable def externalWindingContribution {x y : ℂ}
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ) : ℤ := ...

/-- Winding number = external (integer) - angle sum / 2π.
This is Proposition 2.3 of Hungerbühler-Wasem. -/
theorem generalizedWindingNumber_eq_external_sub_angle ... := ...

/-- The external winding contribution is an integer. -/
theorem externalWindingContribution_isInt ... := ...
```

Adapt from `WindingNumber/Defs.lean:41,200` and `Decomposition.lean:161`.

- [ ] **Step 3: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.WindingDecomposition`

```bash
git add LeanModularForms/ForMathlib/WindingDecomposition.lean
git commit -m "feat(ForMathlib): PR 8 — winding number decomposition (Prop 2.2+2.3)"
```

---

## Phase 4: Merge (sequential)

### Task 10: PR 9 — Null-Homologous Cycles

**Files:**
- Create: `LeanModularForms/ForMathlib/NullHomologous.lean`
- Source: `Cycle.lean`, `HomologicalCauchy/Basic.lean`

- [ ] **Step 1: Cycle definitions**

```lean
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Mathlib.Data.Finsupp.Defs

/-- A contour cycle: formal ℤ-linear combination of piecewise C¹ immersions. -/
abbrev ContourCycle := PiecewiseC1Immersion →₀ ℤ  -- needs appropriate x y

/-- Contour integral extended linearly to cycles. -/
noncomputable def contourIntegralCycle (f : ℂ → ℂ) (Γ : ContourCycle) : ℂ := ...

/-- Winding number extended linearly to cycles. -/
noncomputable def windingNumberCycle (Γ : ContourCycle) (z₀ : ℂ) : ℂ := ...

/-- A curve is null-homologous in U when its winding number vanishes
for all points outside U. -/
def IsNullHomologous ... := ...
```

Adapt from `Cycle.lean:43-65` and `HomologicalCauchy/Basic.lean:42`.

Note: The `ContourCycle` type needs design thought. The existing code uses
`PiecewiseC1Immersion →₀ ℤ` where `PiecewiseC1Immersion` has no type parameters.
With the new `PiecewiseC1Immersion x y`, we need to handle endpoints. Options:
(a) Use Sigma type: `(Σ (x y : ℂ), PiecewiseC1Immersion x y) →₀ ℤ`
(b) Restrict to closed curves only for cycles
Option (b) is standard and cleaner for homological theory.

- [ ] **Step 2: isNullHomologous_of_convex bridge**

```lean
/-- Every closed curve in a convex open set is null-homologous. -/
theorem isNullHomologous_of_convex {U : Set ℂ} (hU : Convex ℝ U)
    (hUo : IsOpen U) ... := ...
```

Adapt from `HomologicalCauchy/Basic.lean:251`.

- [ ] **Step 3: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.NullHomologous`

```bash
git add LeanModularForms/ForMathlib/NullHomologous.lean
git commit -m "feat(ForMathlib): PR 9 — null-homologous cycles"
```

---

### Task 11: PR 10 — Dixon Theorem

**Files:**
- Create: `LeanModularForms/ForMathlib/Dixon.lean`
- Source: `HomologicalCauchy/DixonProof.lean` (1019 lines)

- [ ] **Step 1: Dixon function definition + continuity**

```lean
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.PoincareBridge
import LeanModularForms.ForMathlib.HomotopyInvariance

/-- The Dixon function: `D(z,w) = ∮_γ f(ζ)/(ζ-z)(ζ-w) dζ` for z ≠ w,
extended continuously to the diagonal. -/
noncomputable def dixonFunction (f : ℂ → ℂ) (γ : ...) (z w : ℂ) : ℂ := ...

/-- The Dixon function is continuous on its domain. -/
theorem dixonFunction_continuousOn ... := ...
```

- [ ] **Step 2: Differentiability helpers (decomposed from 259-line proof)**

The current `dixonFunction_differentiable` is 259 lines. Decompose into:

```lean
/-- Dixon function is holomorphic in the first variable. -/
theorem dixonFunction_differentiableOn_fst ... := ...

/-- Dixon function is holomorphic in the second variable. -/
theorem dixonFunction_differentiableOn_snd ... := ...

/-- Dixon function extends analytically to the diagonal. -/
theorem dixonFunction_extends_to_diagonal ... := ...

/-- Dixon function is bounded on compact subsets. -/
theorem dixonFunction_bounded ... := ...

/-- Full differentiability of the Dixon function. -/
theorem dixonFunction_differentiable ... := ...
```

Each helper should be ≤40 lines. Extract from `DixonProof.lean:640-900`.

- [ ] **Step 3: Main Dixon theorem**

```lean
/-- Dixon's theorem: the Dixon function vanishes for null-homologous curves.
This is the core of the homological Cauchy theorem. -/
theorem dixonFunction_eq_zero (hγ : IsNullHomologous γ U) ... :
    dixonFunction f γ z w = 0 := ...
```

Adapt from `DixonProof.lean:926`.

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.Dixon`

```bash
git add LeanModularForms/ForMathlib/Dixon.lean
git commit -m "feat(ForMathlib): PR 10 — Dixon theorem"
```

---

### Task 12: PR 11 — Homological Cauchy

**Files:**
- Create: `LeanModularForms/ForMathlib/HomologicalCauchy.lean`
- Source: `HomologicalCauchy/Meromorphic.lean` (487 lines)

- [ ] **Step 1: Cauchy theorem for null-homologous curves**

```lean
import LeanModularForms.ForMathlib.Dixon
import LeanModularForms.ForMathlib.Residue

/-- Cauchy's theorem for null-homologous curves: integral of holomorphic
function vanishes. Immediate from Dixon. -/
theorem contourIntegral_eq_zero_of_holomorphic_nullHomologous
    {U : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hγ : IsNullHomologous γ U) :
    contourIntegral f γ = 0 := ...
```

- [ ] **Step 2: Meromorphic version with zero residues**

```lean
/-- Meromorphic function with vanishing residue sum: integral vanishes
on null-homologous curves. -/
theorem contourIntegral_eq_zero_of_meromorphic_residueSum_zero
    {U : Set ℂ} {f : ℂ → ℂ} {S : Finset ℂ}
    (hf : MeromorphicOn f U) (hS : S ⊆ U)
    (hres : ∀ s ∈ S, residue f s = 0)
    (hγ : IsNullHomologous γ (U \ ↑S)) :
    contourIntegral f γ = 0 := ...
```

Adapt from `Meromorphic.lean:57` (185 lines). Decompose into ~4 helpers.

- [ ] **Step 3: CPV convergence for meromorphic functions**

```lean
/-- CPV of meromorphic function converges on null-homologous curves. -/
theorem hasCauchyPVOn_of_meromorphic_nullHomologous
    {U : Set ℂ} {f : ℂ → ℂ} {S : Finset ℂ}
    (hf : MeromorphicOn f (U \ ↑S))
    (hγ : IsNullHomologous γ U) :
    HasCauchyPVOn S f γ
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        windingNumber γ s * residue f s) := ...
```

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.HomologicalCauchy`

```bash
git add LeanModularForms/ForMathlib/HomologicalCauchy.lean
git commit -m "feat(ForMathlib): PR 11 — homological Cauchy for meromorphic functions"
```

---

### Task 13: PR 12 — Higher-Order Pole Conditions

**Files:**
- Create: `LeanModularForms/ForMathlib/HigherOrderPoles.lean`
- Source: `Residue/Flatness.lean`, `Residue/MeromorphicPrincipalPart.lean`

- [ ] **Step 1: Flatness and compatibility conditions**

```lean
import LeanModularForms.ForMathlib.PiecewiseC1Path
import LeanModularForms.ForMathlib.Residue
import Mathlib.Analysis.Meromorphic.NormalForm

/-- Curve flatness of order n at a crossing point: tangent deviation
is O(|t - t₀|^n). (Working name for HW condition A'.) -/
structure IsFlatOfOrder (n : ℕ) {x y : ℂ} (γ : PiecewiseC1Path x y)
    (t₀ : ℝ) where
  ...

/-- All crossings of γ with poles of f have sufficient flatness.
(Working name for HW condition A'.) -/
def HasFlatCrossings (f : ℂ → ℂ) {x y : ℂ}
    (γ : PiecewiseC1Immersion x y) : Prop := ...

/-- Laurent coefficients are compatible with crossing angles.
(Working name for HW condition B.) -/
def IsLaurentCompatible (f : ℂ → ℂ) {x y : ℂ}
    (γ : PiecewiseC1Immersion x y) : Prop := ...
```

Adapt from `Flatness.lean:128`.

- [ ] **Step 2: Automatic satisfaction for simple poles**

```lean
/-- Simple poles automatically satisfy flatness condition. -/
theorem hasFlatCrossings_of_simplePoles ... := ...

/-- Simple poles automatically satisfy Laurent compatibility. -/
theorem isLaurentCompatible_of_simplePoles ... := ...
```

- [ ] **Step 3: Principal part extraction**

```lean
/-- Extract the meromorphic principal part of f at z₀. -/
noncomputable def meromorphicPrincipalPart (f : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ := ...

/-- f minus its principal part is analytic. -/
theorem meromorphicAt_sub_principalPart_analyticAt
    (hf : MeromorphicAt f z₀) :
    AnalyticAt ℂ (fun z => f z - meromorphicPrincipalPart f z₀ z) z₀ := ...
```

Adapt from `MeromorphicPrincipalPart.lean:86`.

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.HigherOrderPoles`

```bash
git add LeanModularForms/ForMathlib/HigherOrderPoles.lean
git commit -m "feat(ForMathlib): PR 12 — higher-order pole conditions (A'/B)"
```

---

### Task 14: PR 13 — Generalized Residue Theorem

**Files:**
- Create: `LeanModularForms/ForMathlib/GeneralizedResidueTheorem.lean`
- Source: `GeneralizedResidueTheorem.lean` (355 lines)

- [ ] **Step 1: Main theorem (HW Theorem 3.3)**

```lean
import LeanModularForms.ForMathlib.HomologicalCauchy
import LeanModularForms.ForMathlib.HigherOrderPoles
import LeanModularForms.ForMathlib.WindingDecomposition

/-- **Generalized Residue Theorem** (Hungerbühler-Wasem, Theorem 3.3).

For a null-homologous curve γ in U, and f meromorphic on U with on-curve
poles S satisfying flatness and Laurent compatibility conditions:

The Cauchy principal value integral converges to
`2πi · ∑_{s ∈ S ∪ S'} n(γ, s) · Res(f, s)`

where S are on-curve poles and S' are off-curve poles. -/
theorem generalizedResidueTheorem
    {U : Set ℂ} {f : ℂ → ℂ}
    {S_on S_off : Finset ℂ}
    (hf : MeromorphicOn f (U \ ↑(S_on ∪ S_off)))
    (hγ_nh : IsNullHomologous γ U)
    (hflat : HasFlatCrossings f γ)
    (hcompat : IsLaurentCompatible f γ) :
    HasCauchyPVOn S_on f γ
      (2 * ↑Real.pi * I *
        ∑ s ∈ S_on ∪ S_off,
          generalizedWindingNumber γ s * residue f s) := ...
```

Adapt from `GeneralizedResidueTheorem.lean:44` (166 lines). Decompose into
~4 helper lemmas.

- [ ] **Step 2: Simple poles corollary**

```lean
/-- Generalized residue theorem for simple poles: no flatness/compatibility
conditions needed. -/
theorem generalizedResidueTheorem_simplePoles
    {U : Set ℂ} {f : ℂ → ℂ} {S : Finset ℂ}
    (hf : ∀ s ∈ S, HasSimplePoleAt f s)
    (hf_hol : DifferentiableOn ℂ f (U \ ↑S))
    (hγ_nh : IsNullHomologous γ U) :
    HasCauchyPVOn S f γ
      (2 * ↑Real.pi * I *
        ∑ s ∈ S, generalizedWindingNumber γ s * residue f s) := by
  exact generalizedResidueTheorem hf_hol.meromorphicOn hγ_nh
    (hasFlatCrossings_of_simplePoles ...) (isLaurentCompatible_of_simplePoles ...)
```

Adapt from `GeneralizedResidueTheorem.lean:217`.

- [ ] **Step 3: Convex domain corollary**

```lean
/-- Generalized residue theorem on convex domains: null-homologous automatic. -/
theorem generalizedResidueTheorem_convex
    {U : Set ℂ} (hU : Convex ℝ U) (hUo : IsOpen U) ... := by
  exact generalizedResidueTheorem ... (isNullHomologous_of_convex hU hUo ...)
    hflat hcompat
```

Adapt from `Residue/FlatnessTransfer.lean:53`.

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.GeneralizedResidueTheorem`

```bash
git add LeanModularForms/ForMathlib/GeneralizedResidueTheorem.lean
git commit -m "feat(ForMathlib): PR 13 — generalized residue theorem (HW Thm 3.3)"
```

---

## Phase 5: Chain 2 — Valence Formula

### Task 15: PR V1 — Fundamental Domain Boundary

**Files:**
- Create: `LeanModularForms/ForMathlib/FDBoundary.lean`
- Source: `ValenceFormula/Boundary/Basic.lean`

- [ ] **Step 1: Define the 5-segment FD boundary**

```lean
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.NumberTheory.ModularForms.Basic

/-- The boundary of the standard fundamental domain for SL₂(ℤ) at height H.
A closed piecewise C¹ path with 5 segments:
1. Right vertical: (1/2 + Hi) → ρ+1
2. Arc: ρ+1 → i (unit circle)
3. Arc: i → ρ (unit circle)
4. Left vertical: ρ → (-1/2 + Hi)
5. Horizontal: (-1/2 + Hi) → (1/2 + Hi) -/
noncomputable def fdBoundary (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    PiecewiseC1Path (1/2 + H * I) (1/2 + H * I) := ...
```

Adapt from `Boundary/Basic.lean`. Note: existing code uses `[0,5]` parametrization;
must reparametrize to `[0,1]` with partition at `{1/5, 2/5, 3/5, 4/5}`.

- [ ] **Step 2: Prove it's an immersion + basic properties**

```lean
/-- The FD boundary is a piecewise C¹ immersion. -/
noncomputable def fdBoundaryImmersion (H : ℝ) (hH : H > Real.sqrt 3 / 2) :
    PiecewiseC1Immersion (1/2 + H * I) (1/2 + H * I) := ...

/-- Crossing points: i at t=2/5, ρ at t=3/5, ρ+1 at t=1/5. -/
theorem fdBoundary_crossing_i ... := ...
theorem fdBoundary_crossing_rho ... := ...
theorem fdBoundary_crossing_rho_plus_one ... := ...
```

- [ ] **Step 3: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.FDBoundary`

```bash
git add LeanModularForms/ForMathlib/FDBoundary.lean
git commit -m "feat(ForMathlib): V1 — fundamental domain boundary contour"
```

---

### Task 16: PR V2 — Interior Winding Number

**Files:**
- Create: `LeanModularForms/ForMathlib/InteriorWinding.lean`
- Source: `ValenceFormula/RectHomotopy/`, `ValenceFormula/InteriorWinding.lean`

- [ ] **Step 1: Main theorem with homotopy strategy**

```lean
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.HomotopyInvariance

/-- The generalized winding number of the FD boundary around any
strict interior point (‖z‖ > 1, |Re z| < 1/2) equals -1. -/
theorem hasGeneralizedWindingNumber_fdBoundary_neg_one
    {z : ℂ} (hz_norm : 1 < ‖z‖) (hz_re : |z.re| < 1/2) (H : ℝ)
    (hH : H > Real.sqrt 3 / 2) (hz_im : z.im < H) :
    HasGeneralizedWindingNumber (fdBoundary H hH) z (-1) := ...
```

Proof strategy (from RectHomotopy/):
1. Homotope FD boundary to inscribed polygon
2. Radial homotopy from polygon to circle
3. Angle integration via FTC: total rotation = -2π

This is the hardest proof (~2000 lines across 4 files). Decompose into:
- `fdBoundary_homotopic_polygon` — polygon homotopy construction
- `polygon_avoids_interior` — arc avoidance geometry
- `polygon_windingNumber_neg_one` — via angle lifting + FTC
- `angle_lifted_continuous` — branch cut handling

Each helper ≤50 lines where possible, but some geometric lemmas will be longer.

- [ ] **Step 2: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.InteriorWinding`

```bash
git add LeanModularForms/ForMathlib/InteriorWinding.lean
git commit -m "feat(ForMathlib): V2 — interior winding number = -1"
```

---

### Task 17: PR V3 — Elliptic Point Winding Weights

**Files:**
- Create: `LeanModularForms/ForMathlib/EllipticWeights.lean`
- Source: `ValenceFormula/WindingWeights/{I,Rho,RhoPlusOne}.lean`

- [ ] **Step 1: Winding at i = -1/2 via SingleCrossingData**

```lean
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.SingleCrossing

/-- SingleCrossingData for i on the FD boundary.
Crossing at t₀ = 2/5, δ(ε) = (12/π)·arcsin(ε/2). -/
noncomputable def singleCrossingData_i (H : ℝ) (hH : ...) :
    SingleCrossingData (fdBoundary H hH) I where
  L := -(↑Real.pi * I)
  t₀ := 2/5
  δ ε := 12 / Real.pi * Real.arcsin (ε / 2)
  ...

/-- Winding number at i equals -1/2. -/
theorem hasGeneralizedWindingNumber_fdBoundary_i_neg_half (H : ℝ) (hH : ...) :
    HasGeneralizedWindingNumber (fdBoundary H hH) I (-1/2) :=
  (singleCrossingData_i H hH).windingNumber_neg_half rfl
```

Adapt arc geometry from `WindingWeights/I.lean`. The key work is proving the
8 obligations of SingleCrossingData. With the framework, this should compress
from ~1061 lines to ~200 lines.

- [ ] **Step 2: Winding at ρ = -1/6 via AsymmetricCrossingData**

```lean
/-- AsymmetricCrossingData for ρ on the FD boundary.
Crossing at t₀ = 3/5, left: arc geometry, right: vertical segment. -/
noncomputable def asymmetricCrossingData_rho ... :=
    AsymmetricCrossingData (fdBoundary H hH) ... where
  L := -(↑Real.pi / 3 * I)
  δ_left ε := 12 / Real.pi * Real.arcsin (ε / 2)  -- arc
  δ_right ε := ε / (H - Real.sqrt 3 / 2)           -- vertical
  ...

theorem hasGeneralizedWindingNumber_fdBoundary_rho_neg_sixth ... :=
  (asymmetricCrossingData_rho ...).windingNumber_neg_sixth rfl
```

Adapt from `WindingWeights/Rho.lean`.

- [ ] **Step 3: Winding at ρ+1 = -1/6 (mirror)**

Mirror of Step 2. Adapt from `WindingWeights/RhoPlusOne.lean`.

- [ ] **Step 4: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.EllipticWeights`

```bash
git add LeanModularForms/ForMathlib/EllipticWeights.lean
git commit -m "feat(ForMathlib): V3 — elliptic point winding weights"
```

---

### Task 18: PR V4 — Orbit Pairing

**Files:**
- Create: `LeanModularForms/ForMathlib/OrbitPairing.lean`
- Source: `ValenceFormula/OrbitPairing.lean`, `ValenceFormula/CoreIdentity.lean`

- [ ] **Step 1: T-periodicity cancellation**

```lean
import LeanModularForms.ForMathlib.FDBoundary
import Mathlib.NumberTheory.ModularForms.Basic

/-- Left + right vertical edge integrals cancel by T-periodicity. -/
theorem contourIntegral_leftEdge_add_rightEdge_eq_zero
    {f : ModularForm (Gamma 1) k} ... :
    ... = 0 := ...
```

- [ ] **Step 2: S-transformation on arcs**

```lean
/-- Arc contributions via S-transformation: sum = -2πi·k/6. -/
theorem contourIntegral_arcs_eq ... := ...

/-- Orders at ρ and ρ+1 agree by T-invariance. -/
theorem ord_rho_plus_one_eq_ord_rho ... := ...
```

- [ ] **Step 3: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.OrbitPairing`

```bash
git add LeanModularForms/ForMathlib/OrbitPairing.lean
git commit -m "feat(ForMathlib): V4 — orbit pairing and T/S invariance"
```

---

### Task 19: PR V5 — Valence Formula Core

**Files:**
- Create: `LeanModularForms/ForMathlib/ValenceFormulaCore.lean`
- Source: `ValenceFormula/CoreIdentity.lean`, `ValenceFormula/PVChain/`

- [ ] **Step 1: Apply generalized residue theorem to logDeriv(f)**

```lean
import LeanModularForms.ForMathlib.GeneralizedResidueTheorem
import LeanModularForms.ForMathlib.InteriorWinding
import LeanModularForms.ForMathlib.EllipticWeights
import LeanModularForms.ForMathlib.OrbitPairing

/-- Core valence formula identity: residue side = modular side.
`∑ winding(s) · ord(f, s) = -(k/12 - ord_∞(f))` -/
theorem valenceFormula_core {f : ModularForm (Gamma 1) k} (hf : f ≠ 0) ... :
    ... := ...
```

- [ ] **Step 2: Substitute winding weights**

```lean
/-- Valence formula with explicit winding weights substituted. -/
theorem valenceFormula_explicit {f : ModularForm (Gamma 1) k} (hf : f ≠ 0) :
    (orderAtCusp f : ℚ) + 1/2 * ord_i f + 1/3 * ord_rho f +
      ∑ z ∈ S, ord_z f = k / 12 := ...
```

- [ ] **Step 3: Verify and commit**

Run: `lake build LeanModularForms.ForMathlib.ValenceFormulaCore`

```bash
git add LeanModularForms/ForMathlib/ValenceFormulaCore.lean
git commit -m "feat(ForMathlib): V5 — valence formula core identity"
```

---

### Task 20: PR V6 — Textbook Valence Formula

**Files:**
- Create: `LeanModularForms/ForMathlib/ValenceFormulaTextbook.lean`
- Source: `ValenceFormula/TextbookForm.lean`

- [ ] **Step 1: Clean textbook statement**

```lean
import LeanModularForms.ForMathlib.ValenceFormulaCore

/-- **Textbook Valence Formula** for modular forms of weight `k` on SL₂(ℤ).

For any nonzero `f ∈ M_k(SL₂(ℤ))`:

`ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + ∑_{z ∈ F°} ord_z(f) = k/12`

where `F°` is the strict interior of the standard fundamental domain. -/
theorem valenceFormula_textbook
    {k : ℤ} {f : ModularForm (Gamma 1) k} (hf : f ≠ 0) :
    ... = (k : ℚ) / 12 := ...
```

- [ ] **Step 2: Finsum orbit form**

```lean
/-- Orbit-sum form using `∑ᶠ` over non-elliptic SL₂(ℤ)-orbits. -/
theorem valenceFormula_textbook_finsum ... := ...
```

- [ ] **Step 3: Corollaries**

```lean
/-- Nonzero modular forms have nonneg weight. -/
theorem ModularForm.weight_nonneg {k : ℤ} {f : ModularForm (Gamma 1) k}
    (hf : f ≠ 0) : 0 ≤ k := ...

/-- Finitely many zeros in the fundamental domain. -/
theorem ModularForm.finite_zeros_in_fd ... := ...
```

- [ ] **Step 4: Verify full build**

Run: `lake build` (full project build — everything compiles)
Expected: 0 errors, 0 sorry in ForMathlib files

- [ ] **Step 5: Commit**

```bash
git add LeanModularForms/ForMathlib/ValenceFormulaTextbook.lean
git commit -m "feat(ForMathlib): V6 — textbook valence formula"
```

---

## Verification Checklist (after all tasks)

- [ ] `lake build` passes with 0 errors
- [ ] No `sorry` in any `ForMathlib/` file
- [ ] No imports from existing project code (only mathlib + ForMathlib)
- [ ] No proofs > 50 lines in ForMathlib/ files
- [ ] Each file has module docstring with Main definitions/results sections
- [ ] All limit-based definitions have Tendsto predicate as primary API

## Notes for Implementer

1. **Reparametrization**: All existing code uses `[a,b]` parametrization. New code
   uses `[0,1]` via `Path.extend`. This affects every theorem statement. Use
   `Set.IccExtend` or `Path.extend` consistently.

2. **Proof decomposition**: The spec identifies 36 proofs > 50 lines. Each must be
   decomposed before inclusion. The pattern: extract the key intermediate claim as
   a helper lemma, prove it separately, then the main proof calls the helper.

3. **MCP tools**: Use `lean_goal`, `lean_diagnostic_messages`, `lean_hover_info` to
   check compilation incrementally. Use `lean_verify` to check axiom-cleanness.

4. **Existing code reference**: The existing files are the working "proof of concept".
   Read them for proof ideas, but rewrite for the new API. Do NOT copy-paste — the
   types have changed (PiecewiseC1Path vs PiecewiseC1Curve, Tendsto vs limUnder, etc.).

5. **Phase 2 parallelism**: Tasks 4-7 (PRs 4, 5, 6, 7) have no dependencies on each
   other — only on Task 3. They can be developed in parallel via subagents.
