# GeneralizedResidueTheory/WindingNumber/Defs.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/WindingNumber/Defs.lean`

---

### def `angleAtCrossing`
- Type: `(γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) : ℝ`
- What: The angle at a crossing point — `arg(L_out) - arg(-L_in)` from one-sided derivative limits at partition points; `π` at smooth points.
- How: `if h : t₀ ∈ γ.toPiecewiseC1Curve.partition` then uses `Classical.choose` of `γ.left_deriv_limit` and `γ.right_deriv_limit` to extract `L_left`, `L_right`; returns `arg L_right - arg (-L_left)`; else returns `Real.pi`.
- Hypotheses: `t₀ ∈ Ioo γ.a γ.b`.
- Uses-from-project: `PiecewiseC1Immersion`, `PiecewiseC1Immersion.left_deriv_limit`, `PiecewiseC1Immersion.right_deriv_limit`, `PiecewiseC1Curve.partition`.
- Used by: `angleAtCrossing_smooth`, `windingNumber_corner_crossing`, `externalWindingContribution`.
- Visibility: public.
- Lines: 40-46.

### theorem `angleAtCrossing_smooth`
- Type: `(γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) → angleAtCrossing γ t₀ ht₀ = Real.pi`
- What: At smooth (non-partition) crossings, the angle is `π`.
- How: `simp only [angleAtCrossing, hsmooth, ↓reduceDIte]`.
- Hypotheses: `t₀ ∉ partition`.
- Uses-from-project: `angleAtCrossing`.
- Used by: `windingNumber_smooth_crossing`.
- Visibility: public.
- Lines: 48-51.

### def `windingNumberWithAngles'`
- Type: `(γ : PiecewiseC1Immersion) (_z₀ : ℂ) (crossings : Finset ℝ) (hcrossings_in) (_hcrossings_at) : ℂ`
- What: Winding number via explicit angle sum at crossings — `∑ t ∈ crossings, angleAtCrossing(γ,t)/(2π)`.
- How: `∑ t : crossings, (angleAtCrossing γ t (hcrossings_in t t.prop)) / (2 * Real.pi)`.
- Hypotheses: every crossing parameter is in `Ioo γ.a γ.b` and maps to `_z₀`.
- Uses-from-project: `PiecewiseC1Immersion`, `angleAtCrossing`.
- Used by: `windingNumber_smooth_crossing`, `windingNumber_corner_crossing`.
- Visibility: public.
- Lines: 54-57.

### theorem `singleton_mem_Ioo`
- Type: `(t₀ : ℝ) (a b : ℝ) (ht₀ : t₀ ∈ Ioo a b) → ∀ t ∈ ({t₀} : Finset ℝ), t ∈ Ioo a b`
- What: Singleton-version of the "all crossings in `Ioo`" predicate.
- How: `intro t ht; rw [Finset.mem_singleton.mp ht]; exact ht₀`.
- Hypotheses: `t₀ ∈ Ioo a b`.
- Uses-from-project: none.
- Used by: `windingNumber_smooth_crossing`, `windingNumber_corner_crossing`.
- Visibility: public.
- Lines: 59-63.

### theorem `singleton_at_crossing`
- Type: `(γ : PiecewiseC1Immersion) (t₀ : ℝ) (z₀ : ℂ) (hcross : γ.toFun t₀ = z₀) → ∀ t ∈ ({t₀} : Finset ℝ), γ.toFun t = z₀`
- What: Singleton-version of the "all crossings map to `z₀`" predicate.
- How: `intro t ht; rw [Finset.mem_singleton.mp ht]; exact hcross`.
- Hypotheses: `γ.toFun t₀ = z₀`.
- Uses-from-project: `PiecewiseC1Immersion.toFun`.
- Used by: `windingNumber_smooth_crossing`, `windingNumber_corner_crossing`.
- Visibility: public.
- Lines: 65-69.

### theorem `windingNumber_smooth_crossing`
- Type: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) → windingNumberWithAngles' γ z₀ {t₀} ... = 1/2`
- What: A single smooth crossing contributes `1/2`.
- How: `simp only [windingNumberWithAngles']`; `Fintype.sum_unique`; `simp [Finset.default_singleton]`; `angleAtCrossing_smooth γ t₀ ht₀ hsmooth`; `field_simp [Real.pi_ne_zero]`.
- Hypotheses: `t₀` is a smooth crossing through `z₀`.
- Uses-from-project: `windingNumberWithAngles'`, `angleAtCrossing_smooth`, `singleton_mem_Ioo`, `singleton_at_crossing`.
- Used by: external (HW Proposition 2.2 / 2.3 callers).
- Visibility: public.
- Lines: 72-82.

### theorem `windingNumber_corner_crossing`
- Type: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ α : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) (hangle : angleAtCrossing γ t₀ ht₀ = α) → windingNumberWithAngles' γ z₀ {t₀} ... = α / (2 * Real.pi)`
- What: A corner crossing with angle `α` contributes `α/(2π)`.
- How: `simp only [windingNumberWithAngles']`; `Fintype.sum_unique`; `simp [Finset.default_singleton]`; `rw [hangle]`.
- Hypotheses: angle hypothesis `angleAtCrossing γ t₀ ht₀ = α`.
- Uses-from-project: `windingNumberWithAngles'`, `singleton_mem_Ioo`, `singleton_at_crossing`.
- Used by: external (corner-winding callers).
- Visibility: public.
- Lines: 84-92.

### theorem `cauchyPrincipalValue_eq_classical_off_curve'`
- Type: `(γ : PiecewiseC1Curve) (z₀ : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) → ∃ δ > 0, ∀ ε < δ, ∀ t ∈ Icc γ.a γ.b, ‖γ.toFun t - z₀‖ > ε`
- What: When γ avoids `z₀`, the PV cutoff is trivial below the minimum distance.
- How: Computes `Metric.infDist z₀ (γ.toFun '' Icc γ.a γ.b)`, uses `infDist_pos_iff_notMem_closure` (with witness `γ.toFun γ.a`, compactness from `isCompact_Icc.image_of_continuousOn γ.continuous_toFun`, closure via `IsClosed.closure_eq`); uses `push Not`; concludes with `Metric.infDist_le_dist_of_mem` and `dist_eq_norm`/`dist_comm`.
- Hypotheses: γ avoids `z₀` on `[γ.a, γ.b]`.
- Uses-from-project: `PiecewiseC1Curve.toFun`, `PiecewiseC1Curve.continuous_toFun`, `PiecewiseC1Curve.hab`.
- Used by: external (classical-CPV equivalence).
- Visibility: public.
- Lines: 95-112.

### theorem `integral_inv_real_axis`
- Type: `(r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) → ∫ t in ε..r, (t : ℂ)⁻¹ = Complex.log r - Complex.log ε`
- What: `∫_ε^r t⁻¹ dt = log r - log ε` (complex-valued via `ofReal`).
- How: `simp_rw [← Complex.ofReal_inv]`; proves the real version via `integral_inv_of_pos hε hr` and `Real.log_div hr.ne' hε.ne'`; lifts via `intervalIntegral.integral_ofReal`; `simp [Complex.ofReal_sub, Complex.ofReal_log hr.le, Complex.ofReal_log hε.le]`.
- Hypotheses: `0 < r`, `0 < ε`.
- Uses-from-project: none (Mathlib only).
- Used by: external (transverse-crossing FTC computations).
- Visibility: public.
- Lines: 114-120.

### def `PiecewiseC1Immersion.translate`
- Type: `(γ : PiecewiseC1Immersion) (c : ℂ) : PiecewiseC1Immersion`
- What: Translation of a piecewise C¹ immersion by a constant complex number.
- How: Field-by-field reconstruction: `toFun := fun t => γ.toFun t + c`; `partition`, `partition_subset`, `endpoints_in_partition`, `hab` from γ; `continuous_toFun` via `.add continuousOn_const`; `smooth_off_partition` via `.add (differentiableAt_const _)`; `deriv_continuous_off_partition` and `deriv_ne_zero` use `deriv_add_const`; left/right `deriv_limit` re-extract limits via `Classical.choose` + `funext` proving `deriv (fun t => γ.toFun t + c) = deriv γ.toFun`.
- Hypotheses: none (definition).
- Uses-from-project: `PiecewiseC1Immersion`.
- Used by: `angleAtCrossing_translate`.
- Visibility: public.
- Lines: 123-157.

### theorem `angleAtCrossing_translate`
- Type: `(γ : PiecewiseC1Immersion) (c : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) → angleAtCrossing (γ.translate c) t₀ ht₀ = angleAtCrossing γ t₀ ht₀`
- What: Translation invariance of the crossing angle.
- How: `unfold angleAtCrossing`; `generalize_proofs at *`; `unfold PiecewiseC1Immersion.translate`; `aesop`.
- Hypotheses: `t₀ ∈ Ioo γ.a γ.b`.
- Uses-from-project: `angleAtCrossing`, `PiecewiseC1Immersion.translate`.
- Used by: external (translation invariance consumers).
- Visibility: public.
- Lines: 160-166.

### def `externalWindingContribution`
- Type: `(γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b) : ℂ`
- What: External (non-local) winding contribution at a single crossing — defined so that `n_{z₀}(γ) = ExternalWinding - α/(2π)`.
- How: `generalizedWindingNumber' γ.toFun γ.a γ.b z₀ + (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * Real.pi)`.
- Hypotheses: `t₀ ∈ Ioo γ.a γ.b`.
- Uses-from-project: `generalizedWindingNumber'`, `angleAtCrossing`.
- Used by: external (HW Proposition 2.2 callers).
- Visibility: public.
- Lines: 176-179.

---

## File Summary
- Total declarations: 11 (4 definitions, 7 theorems).
- Key API: `angleAtCrossing` (the HW-style angle at a crossing point); `windingNumberWithAngles'` (angle-sum form of the generalized winding number); `windingNumber_{smooth,corner}_crossing` (1/2 for smooth; α/(2π) for corner); `cauchyPrincipalValue_eq_classical_off_curve'` (off-curve PV triviality); `integral_inv_real_axis` (basic FTC); `PiecewiseC1Immersion.translate` and translation-invariance lemma; `externalWindingContribution` (HW Proposition 2.2 decomposition).
- Unused declarations within file: none — all are public API for downstream HW-style winding-number proofs.
- Sorries: none.
- `set_option`: none.
- Long proofs (>10 lines): `PiecewiseC1Immersion.translate` (34 lines, field aggregator with proofs of continuity/differentiability/`deriv` invariance); `cauchyPrincipalValue_eq_classical_off_curve'` (~17 lines, uses `Metric.infDist_pos_iff_notMem_closure` and `Metric.infDist_le_dist_of_mem`); `angleAtCrossing_translate` (~6 lines, closed by `aesop`).
- Purpose: Foundational definitions for the Hungerbühler-Wasem angle-based approach to the generalized winding number. Defines the angle at a crossing (`π` for smooth points, `arg(L_out) - arg(-L_in)` for partition points), the explicit angle-sum form `windingNumberWithAngles'`, basic singleton-crossing winding-number values (1/2 for smooth, α/(2π) for corners), the classical-CPV equivalence off curves, and the `externalWindingContribution` from HW Proposition 2.2. Also constructs `PiecewiseC1Immersion.translate` and proves translation invariance of crossing angles.
