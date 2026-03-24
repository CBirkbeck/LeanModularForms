# API Generalization Plan: Piecewise Curve Infrastructure + Mathlib Quality

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extract general-purpose piecewise curve API from FD-specific code, eliminate 1000+ lines of duplicated `by_cases` patterns, and polish GRT interfaces to mathlib quality.

**Architecture:** Three tiers — (1) general piecewise curve API in GRT, (2) reusable geometric modules shared between GRT and VF, (3) GRT API polish. Each tier builds on the previous. New files go in `GeneralizedResidueTheory/` (general) or `ValenceFormula/` (VF-specific helpers).

**Tech Stack:** Lean 4 / Mathlib

---

## File Map

### New files to create:
- `GeneralizedResidueTheory/PiecewiseCurveAPI.lean` — segment-lifting, partition cases, property transfer
- `GeneralizedResidueTheory/CurveAvoidance.lean` — min distance, avoidance, slitPlane membership
- `GeneralizedResidueTheory/ArcCalculus.lean` — unit circle arc norms, derivatives, monotonicity
- `GeneralizedResidueTheory/LogDerivFTC.lean` — FTC for log-derivative integrals along C1 curves

### Files to modify:
- `GeneralizedResidueTheory/Basic.lean` — add simp lemmas, ModelSectorCurve API
- `GeneralizedResidueTheory/PrincipalValue.lean` — add @[simp] decomposition lemmas
- `GeneralizedResidueTheory/HomologicalCauchy.lean` — make private FTC lemmas public
- `GeneralizedResidueTheory/Residue/Flatness.lean` — remove `Classical.propDecidable`
- `ValenceFormula/Boundary/Bounds.lean` — refactor to use new API
- `ValenceFormula/Boundary/Smooth.lean` — refactor derivative proofs
- `ValenceFormula/Boundary/Winding/LeftEdge.lean` — parametrize with RightEdge
- `ValenceFormula/WindingWeights/Common.lean` — extract FTC to LogDerivFTC

---

## Tier 1: General Piecewise Curve API

### Task 1: PiecewiseCurveAPI.lean — Segment-Lifting Framework

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/PiecewiseCurveAPI.lean`
- Reference: `LeanModularForms/GeneralizedResidueTheory/Basic.lean` (PiecewiseC1Curve definition, lines 30-42)
- Reference: `LeanModularForms/ValenceFormula/Boundary/Bounds.lean:150-173` (pattern to replace)

The core abstraction: "to prove a property holds on `[a,b]` for a piecewise curve, prove it on each segment."

Currently this is done via nested `by_cases` chains repeated 1169+ times. We need:

- [ ] **Step 1: Define `PiecewiseC1Curve.segments`**

Extract ordered consecutive intervals from a partition. Given partition `{a, p₁, p₂, ..., pₙ, b}`, produce the list `[(a, p₁), (p₁, p₂), ..., (pₙ, b)]`.

```lean
/-- The consecutive intervals defined by a partition, as pairs (left, right). -/
def PiecewiseC1Curve.consecutivePairs : List (ℝ × ℝ) :=
  let pts := (γ.partition.sort (· ≤ ·))
  pts.zip pts.tail
```

- [ ] **Step 2: Prove `forall_of_forall_segments`**

The main lifting lemma: a property that holds on each segment holds everywhere on `[a,b]`.

```lean
/-- To prove P holds on [a,b], it suffices to prove P on each consecutive segment. -/
theorem PiecewiseC1Curve.forall_of_forall_segments
    {γ : PiecewiseC1Curve} {P : ℝ → Prop}
    (hP_closed : ∀ t, IsClosed {t | P t} ∩ Icc γ.a γ.b)  -- or: P is closed
    (h_segs : ∀ (p q : ℝ), (p, q) ∈ γ.consecutivePairs →
      ∀ t ∈ Icc p q, P t) :
    ∀ t ∈ Icc γ.a γ.b, P t
```

- [ ] **Step 3: Prove `forall_of_forall_openSegments` (open-interval version)**

For properties that hold on open segments and extend by continuity:

```lean
theorem PiecewiseC1Curve.forall_of_forall_openSegments
    {γ : PiecewiseC1Curve} {P : ℝ → Prop}
    (hP_cont : ∀ t ∈ Icc γ.a γ.b, ContinuousAt (fun s => P s) t)  -- continuity
    (h_segs : ∀ (p q : ℝ), (p, q) ∈ γ.consecutivePairs →
      ∀ t ∈ Ioo p q, P t) :
    ∀ t ∈ Icc γ.a γ.b, P t
```

- [ ] **Step 4: Prove `exists_segment_of_mem`**

Given `t ∈ [a,b]`, extract the segment it belongs to:

```lean
theorem PiecewiseC1Curve.exists_segment_of_mem
    {γ : PiecewiseC1Curve} {t : ℝ} (ht : t ∈ Icc γ.a γ.b) :
    ∃ (p q : ℝ), (p, q) ∈ γ.consecutivePairs ∧ t ∈ Icc p q
```

- [ ] **Step 5: Prove specializations for common property types**

Lift `< 0`, `> 0`, `∈ S`, `≤ C` etc.:

```lean
theorem PiecewiseC1Curve.pos_of_pos_on_segments
    {γ : PiecewiseC1Curve} {f : ℝ → ℝ} (hf_cont : ContinuousOn f (Icc γ.a γ.b))
    (h_segs : ∀ (p q : ℝ), (p, q) ∈ γ.consecutivePairs →
      ∀ t ∈ Ioo p q, 0 < f t) :
    ∀ t ∈ Icc γ.a γ.b, 0 < f t
```

- [ ] **Step 6: Add to root imports and build**

Add `import LeanModularForms.GeneralizedResidueTheory.PiecewiseCurveAPI` to `LeanModularForms.lean`. Run `lake build`.

- [ ] **Step 7: Commit**

---

### Task 2: CurveAvoidance.lean — Distance and Avoidance API

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/CurveAvoidance.lean`
- Reference: `LeanModularForms/ValenceFormula/Boundary/Winding/RightEdge.lean:113-141` (min distance pattern)
- Reference: `LeanModularForms/ValenceFormula/Boundary/Winding/LeftEdge.lean:41-81` (duplicate)

- [ ] **Step 1: Define `CurveAvoids` and `CurveMinDist`**

```lean
/-- A continuous curve on [a,b] avoids a point z₀. -/
def CurveAvoids (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∀ t ∈ Icc a b, γ t ≠ z₀

/-- Minimum distance from a point to the image of a curve on [a,b]. -/
noncomputable def curveMinDist (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℝ :=
  ⨅ t ∈ Icc a b, ‖γ t - z₀‖
```

- [ ] **Step 2: Prove `curveMinDist_pos_of_avoids`**

```lean
theorem curveMinDist_pos_of_avoids {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (hab : a ≤ b) (hγ : ContinuousOn γ (Icc a b))
    (h_avoids : CurveAvoids γ a b z₀) :
    0 < curveMinDist γ a b z₀
```

- [ ] **Step 3: Prove `curveAvoids_of_re_bound` and `curveAvoids_of_im_bound`**

Half-plane avoidance from real/imaginary part constraints:

```lean
theorem curveAvoids_of_re_ne {γ : ℝ → ℂ} {z₀ : ℂ}
    (h : ∀ t ∈ Icc a b, (γ t).re ≠ z₀.re) :
    CurveAvoids γ a b z₀

theorem curveAvoids_of_im_bound {γ : ℝ → ℂ} {z₀ : ℂ}
    (h : ∀ t ∈ Icc a b, z₀.im < (γ t).im) :
    CurveAvoids γ a b z₀
```

- [ ] **Step 4: Prove `curve_in_slitPlane` — shifted curve in slitPlane**

```lean
theorem curve_sub_in_slitPlane {γ : ℝ → ℂ} {z₀ : ℂ} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b))
    (h_avoids : CurveAvoids γ a b z₀)
    (h_im_or_re : ∀ t ∈ Icc a b, 0 < (γ t - z₀).im ∨ 0 < (γ t - z₀).re) :
    ∀ t ∈ Icc a b, γ t - z₀ ∈ Complex.slitPlane
```

- [ ] **Step 5: Prove `curveMinDist_union` — combine distances across segments**

```lean
theorem curveMinDist_union {γ : ℝ → ℂ} {a b c : ℝ} {z₀ : ℂ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    curveMinDist γ a c z₀ = min (curveMinDist γ a b z₀) (curveMinDist γ b c z₀)
```

- [ ] **Step 6: Add to root imports and build**

- [ ] **Step 7: Commit**

---

### Task 3: ArcCalculus.lean — Unit Circle Arc Properties

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/ArcCalculus.lean`
- Reference: `LeanModularForms/ValenceFormula/Boundary/Bounds.lean:57-98` (trig helpers)
- Reference: `LeanModularForms/ValenceFormula/Boundary/Winding/UnitArcHelpers.lean` (arc norm/monotonicity)

- [ ] **Step 1: Define `unitArc` parameterization**

```lean
/-- Unit circle arc from angle θ₁ to θ₂, linearly parameterized on [a,b]. -/
def unitArc (θ₁ θ₂ a b : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (↑(θ₁ + (t - a) / (b - a) * (θ₂ - θ₁)) * Complex.I)
```

- [ ] **Step 2: Prove basic properties**

```lean
theorem unitArc_norm : ‖unitArc θ₁ θ₂ a b t‖ = 1
theorem unitArc_start : unitArc θ₁ θ₂ a b a = exp (θ₁ * I)
theorem unitArc_end : unitArc θ₁ θ₂ a b b = exp (θ₂ * I)
theorem unitArc_continuous : Continuous (unitArc θ₁ θ₂ a b)
```

- [ ] **Step 3: Prove derivative formula**

```lean
theorem unitArc_hasDerivAt (t : ℝ) (hab : a < b) :
    HasDerivAt (unitArc θ₁ θ₂ a b)
      (unitArc θ₁ θ₂ a b t * (↑((θ₂ - θ₁) / (b - a)) * I)) t
```

- [ ] **Step 4: Prove distance formulas**

```lean
/-- Distance between two points on the unit circle. -/
theorem unitArc_diff_normSq (θ₁ θ₂ : ℝ) :
    ‖exp (θ₁ * I) - exp (θ₂ * I)‖ ^ 2 = 2 - 2 * Real.cos (θ₁ - θ₂)

/-- Monotonicity: distance from a fixed point increases as angle increases (within π). -/
theorem unitArc_norm_mono {θ₀ θ₁ θ₂ : ℝ}
    (h1 : 0 < θ₁ - θ₀) (h2 : θ₁ - θ₀ < θ₂ - θ₀) (h3 : θ₂ - θ₀ ≤ π) :
    ‖exp (θ₁ * I) - exp (θ₀ * I)‖ < ‖exp (θ₂ * I) - exp (θ₀ * I)‖
```

- [ ] **Step 5: Prove trig helpers (consolidate from Bounds.lean)**

```lean
theorem sin_pos_of_mem_Ioo {θ : ℝ} (h : θ ∈ Ioo 0 π) : 0 < Real.sin θ
theorem abs_cos_le_of_mem_Icc {θ : ℝ} (h : θ ∈ Icc (π/3) (2*π/3)) :
    |Real.cos θ| ≤ 1/2
theorem sin_ge_sqrt3_div2_of_mem_Icc {θ : ℝ} (h : θ ∈ Icc (π/3) (2*π/3)) :
    Real.sqrt 3 / 2 ≤ Real.sin θ
```

- [ ] **Step 6: Add to root imports and build**

- [ ] **Step 7: Commit**

---

### Task 4: LogDerivFTC.lean — FTC for Log-Derivative Integrals

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/LogDerivFTC.lean`
- Move from: `LeanModularForms/ValenceFormula/WindingWeights/Common.lean:99-135` (ftc_log_piece)
- Reference: `LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean:145-197` (ftc_piecewise_contour)

- [ ] **Step 1: Extract and generalize `ftc_log_piece`**

Currently in `WindingWeights/Common.lean`. Move to GRT and generalize:

```lean
/-- FTC for ∫ f'/f along a C¹ curve staying in slitPlane. -/
theorem integral_logDeriv_eq_log_sub {f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a)
```

- [ ] **Step 2: Prove integrability corollary**

```lean
theorem intervalIntegrable_logDeriv_of_slitPlane {f : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b) (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b))
    (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t => deriv f t / f t) volume a b
```

- [ ] **Step 3: Prove piecewise version**

```lean
/-- FTC for ∫ f'/f along a piecewise C¹ curve. -/
theorem integral_logDeriv_piecewise {γ : PiecewiseC1Curve} {f : ℂ → ℂ}
    (hf_hol : ∀ z ∈ Set.range γ.toFun, DifferentiableAt ℂ f z)
    (hf_slit : ∀ t ∈ Icc γ.a γ.b, f (γ t) ∈ Complex.slitPlane) :
    ∫ t in γ.a..γ.b, logDeriv f (γ t) * deriv γ.toFun t =
      Complex.log (f (γ γ.b)) - Complex.log (f (γ γ.a))
```

- [ ] **Step 4: Update `WindingWeights/Common.lean` to import and use**

Replace `ftc_log_piece` with a wrapper around the new general version.

- [ ] **Step 5: Build and commit**

---

## Tier 2: Refactor VF to Use New API

### Task 5: Refactor Boundary/Bounds.lean — Use Segment-Lifting

**Files:**
- Modify: `LeanModularForms/ValenceFormula/Boundary/Bounds.lean`
- Depends on: Task 1 (PiecewiseCurveAPI)

- [ ] **Step 1: Add import of PiecewiseCurveAPI**

- [ ] **Step 2: Refactor `fdBoundary_H_im_pos`**

Replace the 24-line `by_cases` chain (lines 150-173) with:

```lean
lemma fdBoundary_H_im_pos (H : ℝ) (hH : Real.sqrt 3 / 2 < H) :
    ∀ t ∈ Icc (0 : ℝ) 5, 0 < (fdBoundary_H H t).im := by
  apply (fdBoundary_HImmersion H hH).toPiecewiseC1Curve.pos_of_pos_on_segments
    (f := fun t => (fdBoundary_H H t).im)
    (hf_cont := (fdBoundary_H_continuous H).im)
  intro p q hpq t ht
  -- Now handle each segment with the segment formula already applied
  ...
```

- [ ] **Step 3: Refactor `fdBoundary_H_re_abs_le_half`**

Same pattern — replace 20-line `by_cases` chain (lines 209-229).

- [ ] **Step 4: Build and verify all downstream files still compile**

- [ ] **Step 5: Commit**

---

### Task 6: Parametrize Vertical Edge Winding (Right/Left Symmetry)

**Files:**
- Create: `LeanModularForms/ValenceFormula/Boundary/Winding/VerticalEdge.lean`
- Modify: `LeanModularForms/ValenceFormula/Boundary/Winding/RightEdge.lean`
- Modify: `LeanModularForms/ValenceFormula/Boundary/Winding/LeftEdge.lean`
- Reference: RightEdge.lean (814 lines), LeftEdge.lean (605 lines)

- [ ] **Step 1: Create VerticalEdge.lean with parametric lemmas**

The key insight: RightEdge (x₀ = 1/2) and LeftEdge (x₀ = -1/2) have identical proof structure with sign flips. Extract:

```lean
namespace VerticalEdgeWinding

variable (H : ℝ) (x₀ : ℝ) (hH : Real.sqrt 3 / 2 < H)

/-- Unique crossing parameter for a vertical edge at x = x₀. -/
def crossingParam (s : ℂ) (hs_re : s.re = x₀) : ℝ :=
  (H - s.im) / (H - Real.sqrt 3 / 2)

/-- The vertical edge curve avoids s except at the crossing parameter. -/
theorem unique_crossing ...

/-- Minimum distance from s to non-crossing segments. -/
theorem min_dist_pos ...

/-- The gWN at a vertical-edge point is -1/2. -/
theorem gWN_eq_neg_half ...

end VerticalEdgeWinding
```

- [ ] **Step 2: Rewrite RightEdge.lean to instantiate VerticalEdge at x₀ = 1/2**

- [ ] **Step 3: Rewrite LeftEdge.lean to instantiate VerticalEdge at x₀ = -1/2**

- [ ] **Step 4: Build and verify**

- [ ] **Step 5: Commit**

**Expected savings:** ~400 lines (two 600-800 line files → one 400 line parametric file + two 100-line instantiation files).

---

### Task 7: Refactor Derivative Proofs in Smooth.lean

**Files:**
- Modify: `LeanModularForms/ValenceFormula/Boundary/Smooth.lean`
- Depends on: Task 3 (ArcCalculus)

- [ ] **Step 1: Replace `fdBoundary_H_hasDerivAt_seg1'` with affine derivative helper**

Extract a general lemma for affine maps `t ↦ c₀ + c₁ * t`:

```lean
theorem hasDerivAt_affine_complex (c₀ c₁ : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => c₀ + c₁ * ↑s) c₁ t
```

Then seg1, seg4, seg5 derivatives become one-liners.

- [ ] **Step 2: Replace arc derivative proofs with `unitArc_hasDerivAt`**

- [ ] **Step 3: Build and verify**

- [ ] **Step 4: Commit**

---

## Tier 3: GRT API Polish

### Task 8: Add @[simp] Lemmas for PV Integrand

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Basic.lean`
- Modify: `LeanModularForms/GeneralizedResidueTheory/PrincipalValue.lean`

- [ ] **Step 1: Add simp lemmas to Basic.lean after line 61**

```lean
@[simp]
theorem cauchyPrincipalValueIntegrand'_of_gt {ε : ℝ} (h : ε < ‖γ t - z₀‖) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε t = f (γ t) * deriv γ t := by
  simp [cauchyPrincipalValueIntegrand', h]

@[simp]
theorem cauchyPrincipalValueIntegrand'_of_le {ε : ℝ} (h : ‖γ t - z₀‖ ≤ ε) :
    cauchyPrincipalValueIntegrand' f γ z₀ ε t = 0 := by
  simp [cauchyPrincipalValueIntegrand', not_lt.mpr h]

@[simp]
theorem cauchyPrincipalValueIntegrand'_zero_eps :
    cauchyPrincipalValueIntegrand' f γ z₀ 0 t = f (γ t) * deriv γ t := by
  simp [cauchyPrincipalValueIntegrand', norm_pos_iff]
```

- [ ] **Step 2: Build and verify no regressions**

- [ ] **Step 3: Commit**

---

### Task 9: Make Private FTC Lemmas Public in HomologicalCauchy.lean

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean`

- [ ] **Step 1: Make `ftc_piecewise_contour` public (line ~145)**

Change `private theorem ftc_piecewise_contour` to `theorem ftc_piecewise_contour`.

- [ ] **Step 2: Make `ftc_piecewise_contour_induction` public**

- [ ] **Step 3: Make `integrand_intervalIntegrable_of_avoids` public (line ~216)**

- [ ] **Step 4: Add docstrings to each**

```lean
/-- FTC for piecewise C¹ contours: if F is a primitive of f on U and γ lies in U,
    then ∫_γ f(z) dz = F(γ(b)) - F(γ(a)). -/
theorem ftc_piecewise_contour ...
```

- [ ] **Step 5: Build and verify**

- [ ] **Step 6: Commit**

---

### Task 10: Consolidate Homotopy Definitions

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Basic.lean`
- Modify: `LeanModularForms/GeneralizedResidueTheory/Homotopy/Integrality.lean`

Currently 3 different homotopy definitions: `CurvesHomotopic` (Basic.lean:108), `CurvesHomotopicAvoiding` (Basic.lean:116), `PiecewiseCurvesHomotopicAvoiding` (Integrality.lean:38), `ClosedCurvesHomotopicAvoiding` (Integrality.lean:61).

- [ ] **Step 1: Add conversion lemmas between the formulations**

```lean
theorem ClosedCurvesHomotopicAvoiding.toPiecewise
    (h : ClosedCurvesHomotopicAvoiding γ₀ γ₁ a b z₀) :
    PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ ∅

theorem PiecewiseCurvesHomotopicAvoiding.toCurvesHomotopicAvoiding
    (h : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ P) :
    CurvesHomotopicAvoiding γ₀ γ₁ a b z₀
```

- [ ] **Step 2: Add docstrings explaining when to use which**

- [ ] **Step 3: Build and commit**

---

### Task 11: ModelSectorCurve API Lemmas

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Basic.lean`

- [ ] **Step 1: Add API lemmas after line 97**

```lean
@[simp] theorem ModelSectorCurve.gamma1_zero : M.gamma1 0 = 0 := by simp [gamma1]
@[simp] theorem ModelSectorCurve.gamma1_r : M.gamma1 M.r = M.r := by simp [gamma1]
@[simp] theorem ModelSectorCurve.gamma2_zero : M.gamma2 0 = M.r := by simp [gamma2]
@[simp] theorem ModelSectorCurve.gamma3_zero : M.gamma3 0 = 0 := by simp [gamma3]
@[simp] theorem ModelSectorCurve.gamma3_r : M.gamma3 M.r = M.r * exp (I * M.alpha) := by
  simp [gamma3]

theorem ModelSectorCurve.gamma2_norm : ‖M.gamma2 t‖ = M.r := by
  simp [gamma2, norm_mul, Complex.abs_exp_ofReal_mul_I]
  exact abs_of_pos M.r_pos

theorem ModelSectorCurve.gamma2_hasDerivAt :
    HasDerivAt M.gamma2 (M.r * I * exp (I * t)) t := by ...
```

- [ ] **Step 2: Build and commit**

---

### Task 12: Remove `Classical.propDecidable` from Flatness.lean

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/Flatness.lean`

- [ ] **Step 1: Check line 38 for `attribute [local instance] Classical.propDecidable`**

If present, determine if it's needed or if `open Classical` suffices.

- [ ] **Step 2: Replace with `open Classical` if possible**

- [ ] **Step 3: Build and commit**

---

## Dependency Graph

```
Task 1 (PiecewiseCurveAPI) ──────► Task 5 (Refactor Bounds.lean)
                                    │
Task 2 (CurveAvoidance) ──────────►├── Task 6 (VerticalEdge)
                                    │
Task 3 (ArcCalculus) ─────────────►├── Task 7 (Refactor Smooth.lean)
                                    │
Task 4 (LogDerivFTC) ─────────────►│

Task 8 (simp lemmas)       ── independent
Task 9 (public FTC)         ── independent
Task 10 (homotopy defs)     ── independent
Task 11 (ModelSectorCurve)  ── independent
Task 12 (Flatness cleanup)  ── independent
```

**Recommended execution order:** Tasks 8-12 first (quick wins, independent), then Tasks 1-4 (new infrastructure), then Tasks 5-7 (refactoring using new infrastructure).
