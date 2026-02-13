# Ticket A — COMPLETE (2026-02-10, Session 60)

**File:** `ValenceFormula_Rect_Homotopy.lean`
**Status:** SORRY-FREE, `lake build` clean (zero errors, lint-only warnings)
**Sorry count:** 0

---

## Exported API for Ticket C

### Main Theorem

```lean
theorem generalizedWindingNumber_fdBoundary_eq_neg_one
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < H_height) :
    generalizedWindingNumber' fdBoundary 0 5 p = -1
```

**Hypotheses:**
- `hp_norm : ‖p‖ > 1` — p is outside the unit circle (not on arc boundary)
- `hp_re : |p.re| < 1/2` — p is between the vertical edges
- `hp_im_pos : 0 < p.im` — p is in the upper half-plane
- `hp_im : p.im < H_height` — p is below the horizontal top edge

### Key Definitions (from this file)

```lean
noncomputable def H_height : ℝ := Real.sqrt 3 / 2 + 1

noncomputable def fdBoundary : ℝ → ℂ  -- parameterized on [0, 5], CLOCKWISE
noncomputable def fdPolygon : ℝ → ℂ   -- chord approximation of fdBoundary
```

### Supporting Lemmas (all sorry-free)

| Lemma | Purpose |
|-------|---------|
| `winding_fdPolygon_eq_neg_one` | Winding of polygon = -1 for all valid interior p |
| `winding_fdPolygon_at_ref_eq_neg_one` | Base case at reference point ref_p₀ |
| `winding_fdPolygon_center_invariant` | Winding invariant under center change |
| `winding_fdPolygon_eq_radialCircle` | Polygon → radial circle homotopy |
| `winding_fdPolygon_eq_circleParamCW` | Full polygon → CW circle chain |
| `fdBoundaryToPolygonHomotopy_continuous` | H₁ homotopy is continuous |
| `fdBoundaryToPolygonHomotopy_avoids` | H₁ avoids interior points |
| `fdBoundaryToPolygonHomotopy_not_diffAt_134` | Non-differentiability at partition |
| `polygonToCircleRadialHomotopy_spec` | Radial homotopy specification |
| `circleToConstantAngleHomotopy_spec` | Angle homotopy specification |
| `circleParamCW_winding_eq_neg_one` | CW circle winding = -1 |

### Import Path

```lean
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Rect_Homotopy
```

This imports from:
- `Basic.lean` — `generalizedWindingNumber'`, `PiecewiseC1Curve`, etc.
- `PiecewiseHomotopy.lean` — `PiecewiseCurvesHomotopicAvoiding`
- `WindingNumber.lean` — winding number properties
- `WindingNumberInterior.lean` — interior winding number results

---

## Proof Architecture (completed)

### 5-Step Transitivity Chain

1. **fdBoundary → fdPolygon** via `fdBoundaryToPolygonHomotopy`
   - Arcs replaced by chords, continuous homotopy avoiding p
2. **fdPolygon → fdPolygonRadialCircle** via radial homotopy
   - Each polygon vertex moved radially to unit circle
3. **fdPolygonRadialCircle → circleParamCW** via angle homotopy on S¹
   - Uniform angular interpolation to constant-speed CW circle
4. **circleParamCW winding = -1** via direct FTC computation
   - `∫₀⁵ (d/dt circleParamCW) / circleParamCW = -2πi` → winding = -1
5. **Center invariance** via straight-line homotopy
   - ref_p₀ = 1.2·I → arbitrary valid interior p

### Key Technical Achievements

- **Piecewise non-differentiability** at partition points {1,2,3,4}: proved by
  showing left/right slopes differ (Re parts have different signs)
- **Lifted angle continuity** (`angle_lifted_ref_p₀_continuousOn`): `ContinuousOn.if'`
  with frontier handling and `Filter.tendsto_sup.mpr`
- **FTC with countable exceptions** (`rc_integral_eq_neg_two_pi_I_ref_p₀`):
  chain rule via `HasDerivAt.scomp` for ℝ→ℂ composed with ℂ→ℂ
- **SlitPlane membership** (`rc_sub_ref_p₀_mem_slitPlane`): fdPolygon(t) - ref_p₀
  avoids the negative real axis for t ≠ tL
