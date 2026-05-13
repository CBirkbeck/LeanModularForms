# BoundaryWinding.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/BoundaryWinding.lean`

---

### theorem `hasGeneralizedWindingNumber_neg_half_of_scd`
- Type: `{γ : PiecewiseC1Path x y} {z₀ : ℂ} (D : SingleCrossingData γ z₀) (hL : D.L = -(↑Real.pi * I)) → HasGeneralizedWindingNumber γ z₀ (-1 / 2)`
- What: At any single crossing with limit `L = -(π · I)`, the generalized winding number is `-1/2`.
- How: `convert D.hasWindingNumber using 1`; rewrites `L = -(↑π · I)`; uses `field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]` to collapse `-(π·I)/(2·π·I) = -1/2`.
- Hypotheses: A `SingleCrossingData γ z₀` with limit `L = -(↑π · I)`.
- Uses-from-project: `SingleCrossingData`, `SingleCrossingData.hasWindingNumber`, `HasGeneralizedWindingNumber`.
- Used by: `boundaryWinding_of_smoothFTCHyp`.
- Visibility: public.
- Lines: 58-64.

### theorem `generalizedWindingNumber_neg_half_of_scd`
- Type: `(D : SingleCrossingData γ z₀) (hL : D.L = -(↑π · I)) → generalizedWindingNumber γ z₀ = -1 / 2`
- What: The value-version: `generalizedWindingNumber γ z₀ = -1/2`.
- How: Direct application of `D.windingNumber_neg_half hL`.
- Hypotheses: same as above.
- Uses-from-project: `SingleCrossingData.windingNumber_neg_half`, `generalizedWindingNumber`.
- Used by: external (winding-number consumers).
- Visibility: public.
- Lines: 67-70.

### def `mkSingleCrossingData_smooth`
- Type: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold) (hδ_pos, hδ_small, h_far, h_near) (L : ℂ) (ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold L) → SingleCrossingData γ z₀`
- What: Constructor for `SingleCrossingData` at an arbitrary smooth crossing parameter `t₀`.
- How: Field-by-field aggregation: takes `L`, `t₀`, `ht₀`, `δ`, `threshold`, `hthresh`, `hδ_pos`, `hδ_small`, `h_far`, `h_near` as direct inputs; pulls `E`, `h_ftc`, `hint_left`, `hint_right`, `h_limit` from `ftcHyp.E`, `ftcHyp.h_ftc`, etc.
- Hypotheses: geometric bounds (`h_far`, `h_near`) plus an `ArcFTCHyp` providing FTC, integrability, and the limit.
- Uses-from-project: `SingleCrossingData`, `ArcFTCHyp`, `fdStart`, `PiecewiseC1Path`.
- Used by: `boundaryWinding_of_smoothFTCHyp`.
- Visibility: public, `noncomputable`.
- Lines: 85-108.

### theorem `boundaryWinding_of_smoothFTCHyp`
- Type: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (z₀ : ℂ) (t₀ : ℝ) (ht₀, δ, threshold, hthresh, hδ_pos, hδ_small, h_far, h_near) (ftcHyp : ArcFTCHyp γ z₀ t₀ δ threshold (-(↑π · I))) → HasGeneralizedWindingNumber γ z₀ (-1 / 2)`
- What: From a generic smooth crossing's geometric bounds + ArcFTC hypothesis, extract `HasGeneralizedWindingNumber γ z₀ (-1/2)`.
- How: Composes `hasGeneralizedWindingNumber_neg_half_of_scd` with `mkSingleCrossingData_smooth ... ftcHyp` and `rfl` for `L = -(↑π · I)`.
- Hypotheses: all geometric bounds + `ArcFTCHyp` with limit `-(↑π · I)`.
- Uses-from-project: `hasGeneralizedWindingNumber_neg_half_of_scd`, `mkSingleCrossingData_smooth`.
- Used by: `SmoothBoundaryWindingData.hasWindingNumber`.
- Visibility: public.
- Lines: 112-124.

### structure `SmoothBoundaryWindingData`
- Type: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (z₀ : ℂ)` — bundles `t₀, ht₀, δ, threshold, hthresh, hδ_pos, hδ_small, h_far, h_near, ftcHyp`.
- What: Data witnessing that a smooth boundary point `z₀` has winding number `-1/2`.
- How: Structure with 10 fields packaging the crossing parameter, cutoff, geometric bounds, and `ArcFTCHyp` with limit `-(↑π · I)`.
- Hypotheses: none (definition).
- Uses-from-project: `PiecewiseC1Path`, `fdStart`, `ArcFTCHyp`.
- Used by: `SmoothBoundaryWindingData.hasWindingNumber`.
- Visibility: public.
- Lines: 136-157.

### theorem `SmoothBoundaryWindingData.hasWindingNumber`
- Type: `{H} {γ : PiecewiseC1Path (fdStart H) (fdStart H)} {z₀ : ℂ} (D : SmoothBoundaryWindingData γ z₀) → HasGeneralizedWindingNumber γ z₀ (-1 / 2)`
- What: Extracts `HasGeneralizedWindingNumber γ z₀ (-1/2)` from `SmoothBoundaryWindingData`.
- How: Direct application of `boundaryWinding_of_smoothFTCHyp` with all fields of `D`.
- Hypotheses: `SmoothBoundaryWindingData γ z₀`.
- Uses-from-project: `boundaryWinding_of_smoothFTCHyp`, `SmoothBoundaryWindingData`.
- Used by: external (boundary winding consumers).
- Visibility: public.
- Lines: 160-164.

### def `linDelta`
- Type: `(C : ℝ) (ε : ℝ) : ℝ`
- What: Linear cutoff function `ε / C` inverting `‖γ(t) - z₀‖ = C·|t - t₀|`.
- How: `ε / C`.
- Hypotheses: none.
- Uses-from-project: none.
- Used by: `linDelta_pos`, `linDelta_small`.
- Visibility: public.
- Lines: 172.

### theorem `linDelta_pos`
- Type: `{C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) → 0 < linDelta C ε`
- What: Positivity of the linear cutoff.
- How: `div_pos hε hC`.
- Hypotheses: `0 < C`, `0 < ε`.
- Uses-from-project: `linDelta`.
- Used by: external (linear-cutoff smooth-boundary constructions).
- Visibility: public.
- Lines: 174-175.

### theorem `linDelta_small`
- Type: `{C ε bound : ℝ} (hC : 0 < C) (hε_lt : ε < C * bound) → linDelta C ε < bound`
- What: The linear cutoff stays small enough relative to a chosen bound when `ε < C · bound`.
- How: `rw [linDelta, div_lt_iff₀ hC]; linarith`.
- Hypotheses: `0 < C`, `ε < C · bound`.
- Uses-from-project: `linDelta`.
- Used by: external.
- Visibility: public.
- Lines: 177-180.

---

## File Summary
- Total declarations: 9 (1 structure, 1 constructor `def`, 1 utility `def`, 6 theorems).
- Key API: `hasGeneralizedWindingNumber_neg_half_of_scd` (universal bridge: SCD with limit `-(πI)` ⇒ winding `-1/2`); `SmoothBoundaryWindingData` bundle + `hasWindingNumber` extractor; linear cutoff utilities `linDelta`/`linDelta_pos`/`linDelta_small` for vertical and horizontal segments.
- Unused declarations within file: none — all are public API used downstream (in particular, by the FD boundary smooth-edge winding theorems).
- Sorries: none.
- `set_option`: none.
- Long proofs (>10 lines): `mkSingleCrossingData_smooth` is a 24-line field aggregator (not really a proof); `SmoothBoundaryWindingData` is a 22-line structure definition. No actual long proofs.
- Purpose: Provides the central bridge "smooth crossing with limit `L = -(πI)` ⇒ generalized winding number `-1/2`". Defines `SmoothBoundaryWindingData` as a bundle of geometric bounds + an `ArcFTCHyp` instance for use on arbitrary smooth boundary points (excluding the elliptic special points `i`, `ρ`, `ρ+1` and the partition endpoints), so all per-edge generalized-winding-number theorems (left edge, right edge, etc.) become applications of this single structure. Includes linear cutoff utilities for vertical/horizontal segment crossings.
