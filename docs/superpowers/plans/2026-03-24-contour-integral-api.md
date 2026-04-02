# General Contour Integral API Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a general PV contour integral API that captures the common pattern across all 6 winding number computations, then rewrite the ValenceFormula winding proofs as 10-line instantiations.

**Architecture:** New `ContourIntegral/` directory under `LeanModularForms/` with 4 files building up from basic PV splitting to the full winding number theorem. The ValenceFormula winding files then import and instantiate. The key abstraction: "PV integral of g'/g along a closed piecewise C1 curve with a unique crossing at t₀ equals the limit of the log ratio at the crossing boundary."

**Tech Stack:** Lean 4 / Mathlib, building on existing `GeneralizedResidueTheory/` (PiecewiseCurveAPI, CurveAvoidance, LogDerivFTC, ArcCalculus)

---

## File Map

### New files to create:
- `LeanModularForms/ContourIntegral/PVSplit.lean` — split PV integral at crossing ± δ
- `LeanModularForms/ContourIntegral/SegmentFTC.lean` — FTC for log on piecewise segments away from crossing
- `LeanModularForms/ContourIntegral/CrossingLimit.lean` — log-ratio limit determines PV value
- `LeanModularForms/ContourIntegral/WindingNumber.lean` — gWN = L/(2πi) from Tendsto

### Files to modify later (Phase 2):
- `ValenceFormula/Boundary/Winding/RightEdge.lean` — instantiate general API
- `ValenceFormula/Boundary/Winding/LeftEdge.lean` — instantiate general API
- `ValenceFormula/Boundary/Winding/UnitArc.lean` — instantiate general API
- `ValenceFormula/WindingWeights/I.lean` — instantiate general API
- `ValenceFormula/WindingWeights/Rho.lean` — instantiate general API
- `ValenceFormula/WindingWeights/RhoPlusOne.lean` — instantiate general API

---

## Phase 1: Build General API

### Task 1: PVSplit.lean — Split PV integral at crossing

**Files:**
- Create: `LeanModularForms/ContourIntegral/PVSplit.lean`

This file provides the fundamental decomposition: a PV integral with a unique crossing
splits into left-of-crossing + right-of-crossing (the near-crossing part vanishes).

- [ ] **Step 1: Create file with basic structure**

```lean
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.CurveAvoidance
import Mathlib

/-!
# PV Integral Splitting at Crossings

Split a Cauchy principal value integral at a unique crossing point.
The integral ∫₀⁵ PV(g'/g) decomposes as ∫₀^{t₀-δ} g'/g + ∫_{t₀+δ}⁵ g'/g
when g(t₀) = 0 is the unique crossing.
-/

open Set MeasureTheory Complex Filter
```

- [ ] **Step 2: Define `UniqueCrossing` structure**

The key abstraction capturing "γ passes through s exactly once":

```lean
/-- Data for a piecewise C1 curve with a unique crossing of a point s.
    The crossing occurs at parameter t₀ ∈ (a, b). -/
structure UniqueCrossing (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) where
  t₀ : ℝ
  t₀_mem : t₀ ∈ Ioo a b
  crossing : γ t₀ = s
  unique : ∀ t ∈ Icc a b, γ t = s → t = t₀
  /-- Minimum distance from s to γ on the "far" part of the curve -/
  minDist : ℝ
  minDist_pos : 0 < minDist
  far_bound : ∀ t ∈ Icc a b, |t - t₀| ≥ minDist / C →
    minDist ≤ ‖γ t - s‖
  /-- Near the crossing, norm is controlled by distance to t₀ -/
  near_bound : ∃ C > 0, ∀ δ > 0, δ < some_bound →
    ∀ t, |t - t₀| ≤ δ → ‖γ t - s‖ ≤ C * δ
```

Actually, a simpler version that matches what the proofs actually need:

```lean
/-- A point s on a closed curve γ : [a,b] → ℂ with a unique crossing at t₀.
    For small enough ε, the curve is ε-far from s except near t₀. -/
structure UniqueCrossing (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) where
  t₀ : ℝ
  t₀_mem : t₀ ∈ Ioo a b
  crossing : γ t₀ = s
  /-- For small ε, the set {t : ‖γ t - s‖ ≤ ε} is contained in (t₀-δ(ε), t₀+δ(ε))
      where δ(ε) → 0. -/
  δ : ℝ → ℝ
  δ_pos : ∀ ε > 0, ε < threshold → 0 < δ ε
  δ_bound : ∀ ε > 0, ε < threshold → δ ε < min (t₀ - a) (b - t₀)
  near_captures : ∀ ε > 0, ε < threshold →
    ∀ t ∈ Icc a b, ‖γ t - s‖ ≤ ε → |t - t₀| < δ ε
  threshold : ℝ
  threshold_pos : 0 < threshold
```

- [ ] **Step 3: Prove `pv_split_at_crossing`**

The main splitting theorem:

```lean
/-- The PV integral splits at the crossing: the middle part (near t₀) contributes 0,
    leaving only the integral over [a, t₀-δ] and [t₀+δ, b]. -/
theorem pv_split_at_crossing {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (uc : UniqueCrossing γ a b s) (ε : ℝ) (hε : 0 < ε) (hε_small : ε < uc.threshold) :
    (∫ t in a..b, if ‖γ t - s‖ > ε then (γ t - s)⁻¹ * deriv γ t else 0) =
    (∫ t in a..(uc.t₀ - uc.δ ε), (γ t - s)⁻¹ * deriv γ t) +
    (∫ t in (uc.t₀ + uc.δ ε)..b, (γ t - s)⁻¹ * deriv γ t)
```

This captures the pattern from lines 535-596 of `leftEdge_winding_per_eps`.

- [ ] **Step 4: Build and verify**

- [ ] **Step 5: Commit**

---

### Task 2: SegmentFTC.lean — FTC for log on piecewise segments

**Files:**
- Create: `LeanModularForms/ContourIntegral/SegmentFTC.lean`

This file applies FTC-for-log to the left and right integrals from PVSplit,
yielding a telescoping sum of log differences.

- [ ] **Step 1: Create file**

```lean
import LeanModularForms.ContourIntegral.PVSplit
import LeanModularForms.GeneralizedResidueTheory.LogDerivFTC
import Mathlib
```

- [ ] **Step 2: Define `PiecewiseFTCData`**

Captures the segment structure needed for telescoping FTC:

```lean
/-- Data for applying FTC-for-log piecewise on segments away from a crossing.
    Each segment has a local formula h_i with known derivative, slitPlane membership,
    and matching endpoints between consecutive segments. -/
structure PiecewiseFTCData (γ : ℝ → ℂ) (s : ℂ) (breakpoints : List ℝ) where
  /-- Local segment functions (γ - s restricted to each segment) -/
  segments : Fin (breakpoints.length - 1) → (ℝ → ℂ)
  /-- Each segment function agrees with γ - s on its interval -/
  agrees : ∀ i t, t ∈ Ioo (breakpoints[i]) (breakpoints[i+1]) →
    segments i t = γ t - s
  /-- Consecutive segments match at breakpoints -/
  endpoint_match : ∀ i, segments i (breakpoints[i+1]) = segments (i+1) (breakpoints[i+1])
  /-- Each segment stays in slitPlane -/
  slit : ∀ i t, t ∈ Icc (breakpoints[i]) (breakpoints[i+1]) →
    segments i t ∈ slitPlane
  /-- Each segment is C1 -/
  diff : ∀ i t, t ∈ Ioo (breakpoints[i]) (breakpoints[i+1]) →
    DifferentiableAt ℝ (segments i) t
  /-- Derivatives are continuous -/
  deriv_cont : ∀ i, ContinuousOn (deriv (segments i))
    (Icc (breakpoints[i]) (breakpoints[i+1]))
```

- [ ] **Step 3: Prove `ftc_telescope`**

The telescope theorem: consecutive FTC results collapse to boundary terms only.

```lean
/-- FTC applied piecewise: the integral of g'/g over union of segments
    telescopes to log(last endpoint) - log(first endpoint). -/
theorem ftc_telescope (data : PiecewiseFTCData γ s breakpoints)
    (h_closed : data.segments 0 (breakpoints.head) =
                data.segments (last) (breakpoints.getLast)) :
    ∫ g'/g over left_segments + ∫ g'/g over right_segments =
    log(g(t₀ - δ)) - log(g(t₀ + δ))
```

This captures the telescoping pattern from lines 598-606 of `leftEdge_winding_per_eps`:
all log terms cancel except at the crossing boundary because consecutive endpoints match
and the curve is closed (first = last).

- [ ] **Step 4: Build and verify**

- [ ] **Step 5: Commit**

---

### Task 3: CrossingLimit.lean — Log-ratio limit determines PV value

**Files:**
- Create: `LeanModularForms/ContourIntegral/CrossingLimit.lean`

This is the heart of the API: combining PVSplit + SegmentFTC to show the PV integral
equals the limit of the log ratio at the crossing boundary.

- [ ] **Step 1: Create file**

```lean
import LeanModularForms.ContourIntegral.PVSplit
import LeanModularForms.ContourIntegral.SegmentFTC
import Mathlib
```

- [ ] **Step 2: Prove `pv_eq_of_log_ratio_limit`**

The master theorem:

```lean
/-- The PV integral of (γ-s)⁻¹ · γ' along a closed piecewise C1 curve
    with a unique crossing at t₀ equals the limit of the log ratio
    at the crossing boundary.

    Specifically, if log(g(t₀-δ)) - log(g(t₀+δ)) → L as δ → 0⁺,
    then PV ∮ dz/(z-s) = L.

    This captures the common structure of all 6 winding number computations
    in the ValenceFormula. The only geometry-dependent part is proving the
    log-ratio limit L — everything else (splitting, FTC, telescoping) is generic. -/
theorem pv_eq_of_log_ratio_limit
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {L : ℂ}
    (hγ : PiecewiseC1Curve ...)  -- or just the relevant hypotheses
    (uc : UniqueCrossing γ a b s)
    (ftc_data : PiecewiseFTCData γ s breakpoints)
    (h_limit : Tendsto (fun δ =>
      Complex.log (segment_at_crossing (uc.t₀ - δ)) -
      Complex.log (segment_at_crossing (uc.t₀ + δ)))
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε =>
      ∫ t in a..b, if ‖γ t - s‖ > ε then
        (γ t - s)⁻¹ * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L)
```

- [ ] **Step 3: Build and verify**

- [ ] **Step 4: Commit**

---

### Task 4: WindingNumber.lean — gWN from Tendsto

**Files:**
- Create: `LeanModularForms/ContourIntegral/WindingNumber.lean`

Simple wrapper converting the Tendsto result to a winding number value.

- [ ] **Step 1: Create file with the conversion theorem**

```lean
import LeanModularForms.ContourIntegral.CrossingLimit
import LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib

/-- If the PV integral of (γ-s)⁻¹ · γ' tends to L,
    then the generalized winding number equals L / (2πi). -/
theorem gWN_eq_of_pv_tendsto
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ} {L : ℂ}
    (h : Tendsto (fun ε =>
      ∫ t in a..b, if ‖(γ t - s)‖ > ε then
        (γ t - s)⁻¹ * deriv (fun u => γ u - s) t else 0)
      (𝓝[>] 0) (𝓝 L)) :
    generalizedWindingNumber' γ a b s = L / (2 * ↑Real.pi * I) := by
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  dsimp only []; simp only [sub_zero]
  rw [h.limUnder_eq]
  ring

/-- Specialized: if L = -(π * I), then gWN = -1/2. -/
theorem gWN_eq_neg_half_of_pv_tendsto_neg_pi_I
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (h : Tendsto (...) (𝓝[>] 0) (𝓝 (-(↑Real.pi * I)))) :
    generalizedWindingNumber' γ a b s = -1/2 := by
  rw [gWN_eq_of_pv_tendsto h]
  field_simp [Real.pi_ne_zero, I_ne_zero]

/-- Specialized: if L = -(π/3 * I), then gWN = -1/6. -/
theorem gWN_eq_neg_sixth_of_pv_tendsto
    {γ : ℝ → ℂ} {a b : ℝ} {s : ℂ}
    (h : Tendsto (...) (𝓝[>] 0) (𝓝 (-(↑Real.pi / 3 * I)))) :
    generalizedWindingNumber' γ a b s = -1/6 := by
  rw [gWN_eq_of_pv_tendsto h]
  field_simp [Real.pi_ne_zero, I_ne_zero]
```

- [ ] **Step 2: Build and verify**

- [ ] **Step 3: Commit**

---

### Task 5: Add imports to LeanModularForms.lean

**Files:**
- Modify: `LeanModularForms/LeanModularForms.lean`

- [ ] **Step 1: Add all 4 new imports**

```
import LeanModularForms.ContourIntegral.PVSplit
import LeanModularForms.ContourIntegral.SegmentFTC
import LeanModularForms.ContourIntegral.CrossingLimit
import LeanModularForms.ContourIntegral.WindingNumber
```

- [ ] **Step 2: Build and commit**

---

## Phase 2: Instantiate for ValenceFormula

### Task 6: Rewrite RightEdge using general API

**Files:**
- Modify: `LeanModularForms/ValenceFormula/Boundary/Winding/RightEdge.lean`

- [ ] **Step 1: Add import for ContourIntegral.WindingNumber**

- [ ] **Step 2: Construct `UniqueCrossing` instance for right edge**

```lean
private def rightEdge_crossing (H : ℝ) (hH : ...) (s : ℂ) (hs : ...) :
    UniqueCrossing (fdBoundary_H H) 0 5 s where
  t₀ := (H - s.im) / (H - Real.sqrt 3 / 2)
  t₀_mem := ...
  crossing := rightEdge_fdBoundary_eq ...
  ...
```

- [ ] **Step 3: Prove log-ratio limit for right edge**

```lean
private theorem rightEdge_log_ratio_limit (H : ℝ) (hH : ...) (s : ℂ) (hs : ...) :
    Tendsto (fun δ => Complex.log (g (t₀ - δ)) - Complex.log (g (t₀ + δ)))
      (𝓝[>] 0) (𝓝 (-(↑Real.pi * I))) := ...
```

This is the ONLY geometry-specific part — everything else comes from the general API.

- [ ] **Step 4: Rewrite main theorem**

```lean
theorem gWN_fdBoundary_H_eq_neg_half_of_rightEdge (H : ℝ) (hH : ...) (s : ℂ) (hs : ...) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 s = -1/2 := by
  apply gWN_eq_neg_half_of_pv_tendsto_neg_pi_I
  apply pv_eq_of_log_ratio_limit
    (rightEdge_crossing H hH s hs)
    (rightEdge_ftc_data H hH s hs)
    (rightEdge_log_ratio_limit H hH s hs)
```

- [ ] **Step 5: Delete superseded helpers (winding_per_eps, winding_aux, etc.)**

- [ ] **Step 6: Build and verify**

- [ ] **Step 7: Commit**

---

### Task 7: Rewrite LeftEdge using general API

Same pattern as Task 6 but for left edge (seg4 crossing).

---

### Task 8: Rewrite UnitArc using general API

Same pattern as Task 6 but for unit arc crossing.

---

### Task 9: Rewrite WindingWeights/I using general API

Same pattern but the log-ratio limit is still `-πi` (smooth crossing on arc).

---

### Task 10: Rewrite WindingWeights/Rho and RhoPlusOne

These have limit `-πi/3` (corner crossings). The general API handles this
via `gWN_eq_neg_sixth_of_pv_tendsto`.

---

## Dependency Graph

```
Task 1 (PVSplit) → Task 2 (SegmentFTC) → Task 3 (CrossingLimit) → Task 4 (WindingNumber)
                                                                        ↓
Task 5 (imports) ──────────────────────────────────────────────────── Task 6-10 (instantiate)
```

Phase 1 (Tasks 1-5) is sequential. Phase 2 (Tasks 6-10) can run in parallel.

## Expected Impact

| Metric | Before | After |
|--------|--------|-------|
| RightEdge.lean | ~870 lines | ~200 lines |
| LeftEdge.lean | ~730 lines | ~200 lines |
| UnitArc.lean | ~450 lines | ~150 lines |
| WindingWeights/I.lean | ~890 lines | ~300 lines |
| WindingWeights/Rho.lean | ~890 lines | ~300 lines |
| WindingWeights/RhoPlusOne.lean | ~830 lines | ~300 lines |
| **New ContourIntegral/** | 0 | ~600 lines |
| **Total** | ~4660 lines | ~2050 lines |
| **Savings** | | **~2600 lines (56%)** |
