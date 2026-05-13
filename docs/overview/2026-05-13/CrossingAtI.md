# CrossingAtI.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/CrossingAtI.lean`

---

### def `arcsinDelta`
- Type: `(ε : ℝ) : ℝ`
- What: Exact cutoff for the arc crossing at `i`: `δ(ε) = (12/(5π)) · arcsin(ε/2)`.
- How: `12 / (5 * Real.pi) * Real.arcsin (ε / 2)`.
- Hypotheses: none.
- Uses-from-project: none.
- Used by: every other theorem in the file (cutoff witness).
- Visibility: public, `noncomputable`.
- Lines: 35.

### theorem `arcsinDelta_pos`
- Type: `{ε : ℝ} (hε : 0 < ε) → 0 < arcsinDelta ε`
- What: Positivity of the arcsin-based cutoff.
- How: `unfold arcsinDelta`; `mul_pos (by positivity) (Real.arcsin_pos.mpr (by linarith))`.
- Hypotheses: `ε > 0`.
- Uses-from-project: `arcsinDelta`.
- Used by: `arc_near_at_I_arcsin`, `singleCrossingData_atI_of_ftcHyp`.
- Visibility: public.
- Lines: 37-39.

### theorem `half_angle_arcsinDelta`
- Type: `(ε : ℝ) → 5 * Real.pi / 12 * arcsinDelta ε = Real.arcsin (ε / 2)`
- What: Half-angle identity that exactly inverts the distance formula.
- How: `unfold arcsinDelta; field_simp`.
- Hypotheses: none.
- Uses-from-project: `arcsinDelta`.
- Used by: `arc_near_at_I_arcsin`, `arc_far_at_I_arcsin`.
- Visibility: public.
- Lines: 42-44.

### theorem `arcsin_le_pi_half_mul`
- Type: `{x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) → Real.arcsin x ≤ Real.pi / 2 * x`
- What: Jordan's inequality for arcsin on `[0,1]`.
- How: Splits `x = 0` (`simp`) vs `0 < x`; uses `Real.mul_le_sin` on `(2/π) · arcsin x`, rewriting via `Real.sin_arcsin` (within `[-1, 1]`); then scales by `π/2` via `mul_le_mul_of_nonneg_left`; closes with `mul_assoc` + `π/2 · 2/π = 1` and `one_mul`.
- Hypotheses: `0 ≤ x ≤ 1`.
- Uses-from-project: none.
- Used by: `arcsinDelta_lt_one_fifth`.
- Visibility: public.
- Lines: 47-58.

### theorem `arcsinDelta_lt_one_fifth`
- Type: `{ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) → arcsinDelta ε < 1/5`
- What: For small `ε`, the cutoff stays below `1/5` (the half-width of the arc interval `(1/5, 3/5)`).
- How: `unfold arcsinDelta`; `calc` chain using `Real.arcsin x ≤ (π/2)·x` (from `arcsin_le_pi_half_mul`), then `gcongr`, `field_simp; ring`, `linarith`.
- Hypotheses: `0 < ε < 1/3`.
- Uses-from-project: `arcsinDelta`, `arcsin_le_pi_half_mul`.
- Used by: `arc_near_at_I_arcsin`, `singleCrossingData_atI_of_ftcHyp`.
- Visibility: public.
- Lines: 61-68.

### private theorem `halfAngle_eq`
- Type: `(t : ℝ) → (fdArcAngle t - Real.pi / 2) / 2 = 5 * (t - 2/5) * Real.pi / 12`
- What: Half-angle identity for the arc parameter centred at `t₀ = 2/5`.
- How: `simp only [fdArcAngle]; ring`.
- Hypotheses: none.
- Uses-from-project: `fdArcAngle`.
- Used by: `arc_near_at_I_arcsin`, `arc_far_at_I_arcsin`.
- Visibility: private.
- Lines: 72-74.

### private theorem `abs_halfAngle_eq`
- Type: `(t : ℝ) → |5*(t - 2/5)*Real.pi/12| = 5*Real.pi/12 * |t - 2/5|`
- What: Absolute-value factoring of the half-angle.
- How: Rewrites to `5*π/12 * (t - 2/5)` first, then `abs_mul` and `abs_of_pos (by positivity)`.
- Hypotheses: none.
- Uses-from-project: none.
- Used by: `abs_halfAngle_le_pi12`, `arc_near_at_I_arcsin`, `arc_far_at_I_arcsin`.
- Visibility: private.
- Lines: 76-79.

### private theorem `abs_halfAngle_le_pi12`
- Type: `{t : ℝ} (ht : t ∈ Icc (1/5 : ℝ) (3/5)) → |5*(t - 2/5)*Real.pi/12| ≤ Real.pi/12`
- What: The half-angle is at most `π/12` on the arc parameter range.
- How: `rw [abs_halfAngle_eq]`; bounds `|t - 2/5| ≤ 1/5` via `abs_le.mpr ⟨ht.1, ht.2⟩` (with `linarith`); `calc` with `gcongr` and `ring`.
- Hypotheses: `t ∈ [1/5, 3/5]`.
- Uses-from-project: `abs_halfAngle_eq`.
- Used by: `arc_far_at_I_arcsin`.
- Visibility: private.
- Lines: 81-89.

### theorem `arc_near_at_I_arcsin`
- Type: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) {t : ℝ} (ht : |t - 2/5| ≤ arcsinDelta ε) → ‖fdBoundaryFun H t - I‖ ≤ ε`
- What: Near bound: when `|t - 2/5|` is within `arcsinDelta(ε)`, the distance to `i` is at most `ε`.
- How: Extracts `1/5 < t` and `t ≤ 3/5` via `arcsinDelta_lt_one_fifth` + `(abs_le.mp ht).{1,2}` + `nlinarith`; rewrites via `fdBoundaryFun_arc_dist_I` and `halfAngle_eq`; sets `α := 5*(t-2/5)*π/12`; shows `|α| ≤ arcsin(ε/2)` using `abs_halfAngle_eq` and `half_angle_arcsinDelta`; uses `arcsin_le_pi_div_two` and `abs_sin_eq_sin_abs_of_abs_le_pi`; concludes via `Real.sin_le_sin_of_le_of_le_pi_div_two` and `linarith`.
- Hypotheses: `0 < ε < 1/3`; `|t - 2/5| ≤ arcsinDelta ε`.
- Uses-from-project: `arcsinDelta`, `arcsinDelta_lt_one_fifth`, `half_angle_arcsinDelta`, `halfAngle_eq`, `abs_halfAngle_eq`, `fdBoundaryFun_arc_dist_I`, `arcsinDelta_pos`.
- Used by: `singleCrossingData_atI_of_ftcHyp`.
- Visibility: public.
- Lines: 94-115.

### theorem `arc_far_at_I_arcsin`
- Type: `(H : ℝ) {ε : ℝ} (hε : 0 < ε) (hε_lt : ε < 1/3) {t : ℝ} (ht_arc : t ∈ Icc (1/5 : ℝ) (3/5)) (hδt : arcsinDelta ε < |t - 2/5|) → ε < ‖fdBoundaryFun H t - I‖`
- What: Far bound: when `|t - 2/5|` exceeds `arcsinDelta(ε)` on the arc, the distance to `i` is strictly greater than `ε`.
- How: `rcases` left endpoint vs strict interior; left endpoint case uses `fdBoundaryFun_seg1_dist_I_lower` and a chain `ε < 1/3 < 1/2 ≤ ‖γ(1/5) - I‖`; strict case rewrites by `fdBoundaryFun_arc_dist_I` + `halfAngle_eq`, sets `α := 5*(t-2/5)*π/12`, derives `arcsin(ε/2) < |α|` via `abs_halfAngle_eq` and `half_angle_arcsinDelta`, uses `abs_halfAngle_le_pi12` + `arcsin_le_pi_div_two`, then `Real.sin_lt_sin_of_lt_of_le_pi_div_two` + `linarith`.
- Hypotheses: `0 < ε < 1/3`; `t ∈ [1/5, 3/5]`; `|t - 2/5| > arcsinDelta ε`.
- Uses-from-project: `arcsinDelta`, `half_angle_arcsinDelta`, `halfAngle_eq`, `abs_halfAngle_eq`, `abs_halfAngle_le_pi12`, `fdBoundaryFun_arc_dist_I`, `fdBoundaryFun_seg1_dist_I_lower`.
- Used by: `singleCrossingData_atI_of_ftcHyp`.
- Visibility: public.
- Lines: 120-140.

### def `singleCrossingData_atI_of_ftcHyp`
- Type: `{H : ℝ} (hH : 1 < H) (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (hγ : ∀ t ∈ Icc 0 1, γ.toPath.extend t = fdBoundaryFun H t) (ftcHyp : ArcFTCHyp γ I (2/5) arcsinDelta (min (1/3) (H - 1)) (-(↑Real.pi · I))) : SingleCrossingData γ I`
- What: Constructs `SingleCrossingData` at `i` with `t₀ = 2/5`, `L = -(πi)`, `threshold = min(1/3, H-1)`, `δ = arcsinDelta`.
- How: Calls `mkSingleCrossingData_atI hH γ hγ` supplying: `threshold = min(1/3, H-1)`, `lt_min (...) (...)`, `min_le_min` for `(1/3, 1/2)`; `hδ_pos` via `arcsinDelta_pos`; `hδ_small` via `arcsinDelta_lt_one_fifth`; `h_far` via `arc_far_at_I_arcsin`; `h_near` via `arc_near_at_I_arcsin`; passes `ftcHyp` directly.
- Hypotheses: `H > 1`; γ agrees with `fdBoundaryFun H` on `[0,1]`; ArcFTC hypothesis at `i`.
- Uses-from-project: `mkSingleCrossingData_atI`, `arcsinDelta`, `arcsinDelta_pos`, `arcsinDelta_lt_one_fifth`, `arc_far_at_I_arcsin`, `arc_near_at_I_arcsin`, `ArcFTCHyp`, `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`.
- Used by: `windingNumber_atI_of_ftcHyp`; downstream WindingWeights/I.
- Visibility: public, `noncomputable`.
- Lines: 148-164.

### theorem `windingNumber_atI_of_ftcHyp`
- Type: `(hH : 1 < H) (γ) (hγ) (ftcHyp : ArcFTCHyp ... (-(↑π · I))) → generalizedWindingNumber γ I = -1/2`
- What: The generalized winding number at `i` is `-1/2`.
- How: Direct application of `(singleCrossingData_atI_of_ftcHyp hH γ hγ ftcHyp).windingNumber_neg_half rfl`.
- Hypotheses: same as `singleCrossingData_atI_of_ftcHyp`.
- Uses-from-project: `singleCrossingData_atI_of_ftcHyp`, `SingleCrossingData.windingNumber_neg_half`, `generalizedWindingNumber`.
- Used by: external (WindingWeights/I, valence-formula assembly).
- Visibility: public.
- Lines: 167-173.

---

## File Summary
- Total declarations: 12 (1 noncomputable def for the cutoff, 1 noncomputable def for the `SingleCrossingData` constructor, 9 theorems including 3 private helpers, 1 final winding-number theorem).
- Key API: `arcsinDelta` (the arcsin-based cutoff); `arcsin_le_pi_half_mul` (Jordan's inequality); `arc_near_at_I_arcsin` / `arc_far_at_I_arcsin` (the two geometric bounds); `singleCrossingData_atI_of_ftcHyp` (the assembled `SingleCrossingData` at `i`); `windingNumber_atI_of_ftcHyp` (the value `-1/2`).
- Unused declarations within file: none — the three private helpers feed the two arc bounds; everything else is public API.
- Sorries: none.
- `set_option`: none.
- Long proofs (>10 lines): `arc_near_at_I_arcsin` (~22 lines, uses `Real.sin_le_sin_of_le_of_le_pi_div_two` after `abs_sin_eq_sin_abs_of_abs_le_pi`); `arc_far_at_I_arcsin` (~21 lines, similar but with `Real.sin_lt_sin_of_lt_of_le_pi_div_two` and an `rcases` for the boundary endpoint); `arcsin_le_pi_half_mul` (~12 lines, Jordan's inequality via `Real.mul_le_sin`).
- Purpose: Builds the `SingleCrossingData` for the arc crossing of the FD boundary at `i` (parameter `t₀ = 2/5`). The exact cutoff `arcsinDelta(ε) = (12/(5π))·arcsin(ε/2)` perfectly inverts the half-angle distance formula `‖γ(t) - i‖ = 2|sin(5(t-2/5)π/12)|`, so the near and far bounds reduce to monotonicity of `sin` on `[0, π/2]` (using `|sin α| = sin|α|` for `|α| ≤ π`). The analytical FTC content is taken as an `ArcFTCHyp` parameter, so this file is the *geometric* component of the winding-number-at-`i` story. Output: `generalizedWindingNumber γ I = -1/2`.
