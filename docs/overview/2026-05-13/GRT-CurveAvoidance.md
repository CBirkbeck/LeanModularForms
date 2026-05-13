# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/CurveAvoidance.lean

## def `CurveAvoids`
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∀ t ∈ Icc a b, γ t ≠ z₀`.
- **What**: Predicate "a continuous curve on `[a, b]` avoids `z₀`", i.e.
  no parameter value is mapped to `z₀`.
- **How**: A universal-quantifier wrapper; no proof body.
- **Hypotheses**: n/a (definition).
- **Uses-from-project**: imports `ClassicalCPV` for ambient setup
  (otherwise pure mathlib).
- **Used by**: All other declarations in this file plus downstream CPV /
  generalised-residue lemmas needing curve-avoidance.
- **Visibility**: public `def`; root namespace.
- **Lines**: 30-31.

## def `curveInfDist`
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℝ :=
  Metric.infDist z₀ (γ '' Icc a b)`.
- **What**: Infimum distance from `z₀` to the curve image on `[a, b]`.
- **How**: `Metric.infDist` applied to the image set.
- **Hypotheses**: n/a (definition).
- **Uses-from-project**: mathlib only.
- **Used by**: `curveInfDist_pos_of_avoids` (locally); consumers requiring a
  positive distance from a curve to a singular point.
- **Visibility**: public `noncomputable def`; root namespace.
- **Lines**: 34-35.

## theorem `curveAvoids_of_ne_on_Icc`
- **Type**: `(h : ∀ t ∈ Icc a b, γ t ≠ z₀) → CurveAvoids γ a b z₀`.
- **What**: Trivial wrapper — `CurveAvoids` is *definitionally* the
  pointwise inequality.
- **How**: Returns `h` itself.
- **Hypotheses**: pointwise non-equality on `[a, b]`.
- **Uses-from-project**: `CurveAvoids`.
- **Used by**: Callers who already have the pointwise form.
- **Visibility**: public; root namespace.
- **Lines**: 40-42.

## theorem `curveAvoids_of_im_lt`
- **Type**: `(h : ∀ t ∈ Icc a b, z₀.im < (γ t).im) → CurveAvoids γ a b z₀`.
- **What**: If the curve's imaginary part is strictly above that of `z₀`
  throughout `[a, b]`, the curve avoids `z₀`.
- **How**: `fun t ht heq => (h t ht).ne (heq ▸ rfl)` — a strict inequality
  in `im` rules out equality of complex points.
- **Hypotheses**: strict imaginary-part bound on `[a, b]`.
- **Uses-from-project**: `CurveAvoids`.
- **Used by**: Typically segment-by-segment avoidance proofs (vertical
  edges of the fundamental domain).
- **Visibility**: public; root namespace.
- **Lines**: 46-48.

## theorem `curveAvoids_of_re_ne`
- **Type**: `(h : ∀ t ∈ Icc a b, (γ t).re ≠ z₀.re) → CurveAvoids γ a b z₀`.
- **What**: If real parts differ everywhere, the curve avoids `z₀`.
- **How**: One-line via the `re` projection contradiction.
- **Hypotheses**: pointwise real-part inequality.
- **Uses-from-project**: `CurveAvoids`.
- **Used by**: Vertical-line avoidance arguments.
- **Visibility**: public; root namespace.
- **Lines**: 52-54.

## theorem `curveAvoids_of_norm_ne`
- **Type**: `(h : ∀ t ∈ Icc a b, ‖γ t‖ ≠ ‖z₀‖) → CurveAvoids γ a b z₀`.
- **What**: If norms differ everywhere, the curve avoids `z₀`. Useful for
  curves on circles (avoiding a point not at the curve's radius).
- **How**: One-line via the `norm` contradiction.
- **Hypotheses**: pointwise norm inequality.
- **Uses-from-project**: `CurveAvoids`.
- **Used by**: Arc-avoidance arguments.
- **Visibility**: public; root namespace.
- **Lines**: 58-60.

## theorem `curveInfDist_pos_of_avoids`
- **Type**: For `γ` continuous on `[a, b]`, `a ≤ b`, `CurveAvoids γ a b z₀`:
  `0 < curveInfDist γ a b z₀`.
- **What**: A continuous curve that avoids `z₀` has positive infimum
  distance to `z₀`.
- **How**: The image `γ '' Icc a b` is compact (hence closed) and
  nonempty (contains `γ a`); apply
  `IsClosed.notMem_iff_infDist_pos` and discharge `z₀ ∉ γ '' Icc a b`
  using `CurveAvoids`.
- **Hypotheses**: `ContinuousOn γ (Icc a b)`, `a ≤ b`, `CurveAvoids`.
- **Uses-from-project**: `CurveAvoids`, `curveInfDist`.
- **Used by**: CPV / cutoff-distance arguments that need a positive gap.
- **Visibility**: public; root namespace.
- **Lines**: 66-76.

## theorem `curve_sub_in_slitPlane`
- **Type**: For `γ` continuous on `[a, b]` avoiding `z₀`, with
  `hpos : ∀ t ∈ Icc a b, 0 < (γ t - z₀).im ∨ 0 < (γ t - z₀).re`:
  `∀ t ∈ Icc a b, γ t - z₀ ∈ Complex.slitPlane`.
- **What**: A shifted curve `γ - z₀` lies entirely in `slitPlane` provided
  it is not on the closed negative real axis (positive `im` or positive
  `re` suffices).
- **How**: Apply `Complex.mem_slitPlane_iff` and the disjunction `hpos`:
  the `im > 0` case directly gives `im ≠ 0`; the `re > 0` case gives
  `re ≠ 0` (with sign), satisfying the slit-plane criterion (`re > 0`
  or `im ≠ 0`).
- **Hypotheses**: continuity (named `_hγ`, unused), avoidance (named
  `_hav`, unused), positivity disjunction.
- **Uses-from-project**: `CurveAvoids`.
- **Used by**: Logarithm-branch arguments along boundary segments (e.g.
  cusp-side estimates using `Complex.log` continuity on `slitPlane`).
- **Visibility**: public; root namespace.
- **Lines**: 82-86.

## File Summary
Eight public declarations (two `def`, six `theorem`) covering the
"curve avoidance API": (1) `CurveAvoids` and `curveInfDist` as basic
predicates/quantities, (2) four convenient sufficient conditions for
avoidance (pointwise non-equality, imaginary-part gap, real-part gap,
norm gap), (3) the positivity result `curveInfDist_pos_of_avoids` for
continuous curves avoiding a point, and (4) `curve_sub_in_slitPlane`
for placing the shifted curve in the slit plane (logarithm domain).
General-purpose support for CPV / generalised-residue arguments. No
`sorry`. Imports: `ClassicalCPV` and `Mathlib`.
