# FDBoundaryH.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/FDBoundaryH.lean`
Imports: `ClassicalCPV`, `EllipticPoints`

### `def heightCutoff`
- **Type**: `ℝ`
- **What**: Fixed cutoff height `√3/2 + 1` for the standard FD boundary.
- **How**: Defined as `Real.sqrt 3 / 2 + 1`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `one_lt_heightCutoff`, `sqrt3_div2_lt_heightCutoff`, `fdBoundary_seg1`, `fdBoundary_seg4`, `fdBoundary_seg5`, `fdBoundary`, `fdBoundary_at_*` lemmas, `fdBoundary_eq_fdBoundary_H`
- **Visibility**: public
- **Lines**: 32-32
- **Notes**: none

### `lemma one_lt_heightCutoff`
- **Type**: `1 < heightCutoff`
- **What**: `heightCutoff > 1`.
- **How**: Unfold definition, use `Real.sqrt_pos_of_pos 3` and `linarith`.
- **Hypotheses**: None.
- **Uses from project**: `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 34-36
- **Notes**: none

### `lemma sqrt3_div2_lt_heightCutoff`
- **Type**: `Real.sqrt 3 / 2 < heightCutoff`
- **What**: `heightCutoff > √3/2`.
- **How**: Unfold definition, `linarith`.
- **Hypotheses**: None.
- **Uses from project**: `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 38-41
- **Notes**: none

### `def fdBoundary_seg1`
- **Type**: `ℝ → ℂ`
- **What**: Right vertical segment: `1/2 + (heightCutoff - t·(heightCutoff - √3/2)) i` (from `1/2 + heightCutoff·i` down to `ρ+1`).
- **How**: Linear interpolation between top-right corner and `ρ+1`.
- **Hypotheses**: None.
- **Uses from project**: `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 44-45
- **Notes**: none

### `def fdBoundary_seg2`
- **Type**: `ℝ → ℂ`
- **What**: Right arc from `ρ+1` to `i` parameterized by angles `π/3 → π/2`.
- **How**: `Complex.exp ((π/3 + (t-1)·(π/2 - π/3)) i)`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_seg2_H`
- **Visibility**: public
- **Lines**: 48-49
- **Notes**: none

### `def fdBoundary_seg3`
- **Type**: `ℝ → ℂ`
- **What**: Left arc from `i` to `ρ` parameterized by angles `π/2 → 2π/3`.
- **How**: `Complex.exp ((π/2 + (t-2)·(2π/3 - π/2)) i)`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_seg3_H`
- **Visibility**: public
- **Lines**: 52-53
- **Notes**: none

### `def fdBoundary_seg4`
- **Type**: `ℝ → ℂ`
- **What**: Left vertical from `ρ` to top-left corner `-1/2 + heightCutoff·i`.
- **How**: Linear interpolation along `re = -1/2`.
- **Hypotheses**: None.
- **Uses from project**: `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 56-57
- **Notes**: none

### `def fdBoundary_seg5`
- **Type**: `ℝ → ℂ`
- **What**: Horizontal top edge from `-1/2 + heightCutoff·i` to `1/2 + heightCutoff·i`.
- **How**: `(t - 9/2) + heightCutoff·I` (note: parameter shift since global parameter is `[4,5]`).
- **Hypotheses**: None.
- **Uses from project**: `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 60-61
- **Notes**: none

### `def fdBoundary`
- **Type**: `ℝ → ℂ`
- **What**: Full piecewise FD boundary at fixed height `heightCutoff`, parameterized over `[0,5]` with five segments stitched via `if-then-else`.
- **How**: Cascade of `if t ≤ 1 ... else if t ≤ 2 ...` with the five segment formulas inlined.
- **Hypotheses**: None.
- **Uses from project**: `heightCutoff`
- **Used by**: `fdBoundary_at_zero/one/two/three/four/five`, `fdBoundary_closed`, `fdBoundary_eq_fdBoundary_H`
- **Visibility**: public
- **Lines**: 65-82
- **Notes**: none

### `def fdPartition`
- **Type**: `Finset ℝ`
- **What**: Interior partition points `{1, 2, 3, 4}` separating the five segments.
- **How**: `Finset` literal.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 85-85
- **Notes**: none

### `def fdBoundaryFullPartition`
- **Type**: `Finset ℝ`
- **What**: Full partition with endpoints: `{0, 1, 2, 3, 4, 5}`.
- **How**: `Finset` literal.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 88-88
- **Notes**: none

### `lemma fdBoundary_at_zero`
- **Type**: `fdBoundary 0 = 1/2 + heightCutoff * I`
- **What**: Value of FD boundary at start: top-right corner.
- **How**: `simp only` reducing the `if t ≤ 1` branch (true for `t = 0`), `push_cast`, `ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary`, `heightCutoff`
- **Used by**: `fdBoundary_closed`
- **Visibility**: public
- **Lines**: 90-94
- **Notes**: none

### `lemma fdBoundary_at_one`
- **Type**: `fdBoundary 1 = ellipticPointRhoPlusOne`
- **What**: At parameter `1`, the boundary reaches `ρ + 1`.
- **How**: Simplify branch with `t ≤ 1` true, unfold `ellipticPointRhoPlusOne`, `UpperHalfPlane.coe_mk`, `heightCutoff`; `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`, `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 96-102
- **Notes**: none

### `lemma fdBoundary_at_two`
- **Type**: `fdBoundary 2 = ellipticPointI`
- **What**: At parameter `2`, the boundary reaches `i`.
- **How**: Simplify case `t ≤ 2` true (not `≤ 1`); rewrite exponential argument to `(π/2) i`; use `Complex.exp_mul_I` + `ofReal_cos/sin`, `Real.cos_pi_div_two`, `Real.sin_pi_div_two`; `simp [ellipticPointI, ellipticPointI']`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary`, `ellipticPointI`, `ellipticPointI'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 104-114
- **Notes**: none

### `lemma fdBoundary_at_three`
- **Type**: `fdBoundary 3 = ellipticPointRho`
- **What**: At parameter `3`, the boundary reaches `ρ`.
- **How**: Simplify to seg3 branch; rewrite exponent to `↑(2π/3) i`; use `exp_mul_I`, `ofReal_cos/sin`, and identity `2π/3 = π - π/3`; apply `Real.cos_pi_sub`, `Real.cos_pi_div_three`, `Real.sin_pi_sub`, `Real.sin_pi_div_three`; simp + ring.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary`, `ellipticPointRho`, `ellipticPointRho'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 116-129
- **Notes**: none

### `lemma fdBoundary_at_four`
- **Type**: `fdBoundary 4 = -1/2 + heightCutoff * I`
- **What**: At parameter `4`, boundary reaches top-left corner.
- **How**: Reduce to seg4 branch with `t = 4`; `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary`, `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 131-137
- **Notes**: none

### `lemma fdBoundary_at_five`
- **Type**: `fdBoundary 5 = 1/2 + heightCutoff * I`
- **What**: At parameter `5`, boundary returns to top-right corner.
- **How**: Reduce to seg5 branch (`else`); `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary`, `heightCutoff`
- **Used by**: `fdBoundary_closed`
- **Visibility**: public
- **Lines**: 139-145
- **Notes**: none

### `lemma fdBoundary_closed`
- **Type**: `fdBoundary 0 = fdBoundary 5`
- **What**: The FD boundary is closed: `γ(0) = γ(5)`.
- **How**: Rewrite both sides with `fdBoundary_at_zero` and `fdBoundary_at_five`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_at_zero`, `fdBoundary_at_five`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 147-148
- **Notes**: none

### `def fdBoundary_seg1_H`
- **Type**: `(H : ℝ) → ℝ → ℂ`
- **What**: Right vertical segment at variable height `H`.
- **How**: Same as `fdBoundary_seg1` but with `H` in place of `heightCutoff`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 152-153
- **Notes**: none

### `def fdBoundary_seg2_H`
- **Type**: `ℝ → ℂ`
- **What**: Right arc at variable height (height-independent).
- **How**: Alias `fdBoundary_seg2`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_seg2`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 156-156
- **Notes**: none

### `def fdBoundary_seg3_H`
- **Type**: `ℝ → ℂ`
- **What**: Left arc at variable height.
- **How**: Alias `fdBoundary_seg3`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_seg3`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 159-159
- **Notes**: none

### `def fdBoundary_seg4_H`
- **Type**: `(H : ℝ) → ℝ → ℂ`
- **What**: Left vertical segment at variable height.
- **How**: Linear interpolation along `re = -1/2`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 162-163
- **Notes**: none

### `def fdBoundary_seg5_H`
- **Type**: `(H : ℝ) → ℝ → ℂ`
- **What**: Horizontal top edge at variable height `H`.
- **How**: `(t - 9/2) + H·I`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 166-166
- **Notes**: none

### `def fdBoundary_H`
- **Type**: `(H : ℝ) → ℝ → ℂ`
- **What**: FD boundary at variable height `H`, parameterized over `[0,5]`.
- **How**: Cascade of `if t ≤ k` branches mirroring `fdBoundary` but with `H` replacing `heightCutoff`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_eq_fdBoundary_H`, `fdBoundary_H_at_*`, `fdBoundary_H_closed`, `fdBoundary_H_eq_layered`, `fdBoundary_H_continuous`
- **Visibility**: public
- **Lines**: 170-186
- **Notes**: none

### `def fdBoundary_H_partition`
- **Type**: `Finset ℝ`
- **What**: Non-differentiable corners `{1, 3, 4}` (omits `t = 2` since seg2-seg3 transition is smooth).
- **How**: `Finset` literal.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 190-190
- **Notes**: none

### `def seg5_q_radius_H`
- **Type**: `(H : ℝ) → ℝ`
- **What**: q-expansion radius `e^(-2πH)` at height `H`.
- **How**: `Real.exp (-2 * Real.pi * H)`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 193-193
- **Notes**: none

### `theorem fdBoundary_eq_fdBoundary_H`
- **Type**: `fdBoundary = fdBoundary_H heightCutoff`
- **What**: The fixed-height boundary equals `fdBoundary_H` specialized at `heightCutoff`.
- **How**: `ext t`, then `simp only [fdBoundary, fdBoundary_H, heightCutoff]`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary`, `fdBoundary_H`, `heightCutoff`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 195-198
- **Notes**: none

### `lemma fdBoundary_H_at_zero`
- **Type**: `(H : ℝ) → fdBoundary_H H 0 = 1/2 + H * I`
- **What**: Start of variable-height boundary.
- **How**: Simplify `if 0 ≤ 1` true branch; `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`
- **Used by**: `fdBoundary_H_closed`
- **Visibility**: public
- **Lines**: 200-204
- **Notes**: none

### `lemma fdBoundary_H_at_one`
- **Type**: `(H : ℝ) → fdBoundary_H H 1 = ellipticPointRhoPlusOne`
- **What**: At parameter `1`, reaches `ρ+1`.
- **How**: Reduce branch; unfold `ellipticPointRhoPlusOne[']`; `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRhoPlusOne`, `ellipticPointRhoPlusOne'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 206-212
- **Notes**: none

### `lemma fdBoundary_H_at_two`
- **Type**: `(H : ℝ) → fdBoundary_H H 2 = ellipticPointI`
- **What**: At parameter `2`, reaches `i`.
- **How**: Same exp/cos/sin computation as `fdBoundary_at_two` adapted to `fdBoundary_H`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`, `ellipticPointI`, `ellipticPointI'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 214-224
- **Notes**: none

### `lemma fdBoundary_H_at_three`
- **Type**: `(H : ℝ) → fdBoundary_H H 3 = ellipticPointRho`
- **What**: At parameter `3`, reaches `ρ`.
- **How**: Same as `fdBoundary_at_three`: rewrite exponent, use `Real.cos_pi_sub`/`Real.cos_pi_div_three`/`Real.sin_pi_sub`/`Real.sin_pi_div_three`; `simp; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`, `ellipticPointRho`, `ellipticPointRho'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 226-239
- **Notes**: none

### `lemma fdBoundary_H_at_four`
- **Type**: `(H : ℝ) → fdBoundary_H H 4 = -1/2 + H * I`
- **What**: At parameter `4`, reaches top-left corner `-1/2 + H·i`.
- **How**: Reduce to seg4 branch with `t = 4`; `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 241-247
- **Notes**: none

### `lemma fdBoundary_H_at_five`
- **Type**: `(H : ℝ) → fdBoundary_H H 5 = 1/2 + H * I`
- **What**: At parameter `5`, returns to top-right corner.
- **How**: Reduce to seg5 branch; `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`
- **Used by**: `fdBoundary_H_closed`
- **Visibility**: public
- **Lines**: 249-255
- **Notes**: none

### `lemma fdBoundary_H_closed`
- **Type**: `(H : ℝ) → fdBoundary_H H 0 = fdBoundary_H H 5`
- **What**: Closure of the variable-height boundary.
- **How**: Rewrite both endpoints via `fdBoundary_H_at_zero` and `fdBoundary_H_at_five`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H_at_zero`, `fdBoundary_H_at_five`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 257-259
- **Notes**: none

### `lemma fdBoundary_H_seg1_cont`
- **Type**: `(H : ℝ) → Continuous (fun t : ℝ => (1 : ℂ) / 2 + (↑H - ↑t * (↑H - ↑√3 / 2)) * I)`
- **What**: Continuity of segment-1 formula at height `H`.
- **How**: Compose `continuous_const`, `Complex.continuous_ofReal`, and `.mul`/`.add`/`.sub`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_continuous`
- **Visibility**: private
- **Lines**: 261-264
- **Notes**: none

### `lemma fdBoundary_H_seg23_cont`
- **Type**: `Continuous (fun t : ℝ => exp ((↑π/3 + (↑t - 1) * (↑π/2 - ↑π/3)) * I))`
- **What**: Continuity of seg2 (right arc) formula.
- **How**: `Complex.continuous_exp.comp` over the affine inner function.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_inner1234_cont`
- **Visibility**: private
- **Lines**: 266-271
- **Notes**: none

### `lemma fdBoundary_H_seg23b_cont`
- **Type**: `Continuous (fun t : ℝ => exp ((↑π/2 + (↑t - 2) * (2 * ↑π/3 - ↑π/2)) * I))`
- **What**: Continuity of seg3 (left arc) formula.
- **How**: Same `continuous_exp.comp` on affine argument.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_inner234_cont`
- **Visibility**: private
- **Lines**: 273-278
- **Notes**: none

### `lemma fdBoundary_H_seg4_cont`
- **Type**: `(H : ℝ) → Continuous (fun t => (-1 : ℂ)/2 + (↑√3/2 + (↑t - 3) * (↑H - ↑√3/2)) * I)`
- **What**: Continuity of seg4 formula at height `H`.
- **How**: Combine `continuous_const`, `Complex.continuous_ofReal`, additive/multiplicative continuity.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_inner34_cont`
- **Visibility**: private
- **Lines**: 280-285
- **Notes**: none

### `lemma fdBoundary_H_seg5_cont`
- **Type**: `(H : ℝ) → Continuous (fun t : ℝ => (↑t - 9/2 : ℂ) + ↑H * I)`
- **What**: Continuity of seg5 formula.
- **How**: `Complex.continuous_ofReal.sub continuous_const).add continuous_const`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_inner34_cont`
- **Visibility**: private
- **Lines**: 287-289
- **Notes**: none

### `def fdBoundary_H_inner34`
- **Type**: `(H : ℝ) → ℝ → ℂ`
- **What**: Helper: composite of segs 4 and 5 stitched at `t = 4`.
- **How**: `if t ≤ 4 then seg4-formula else seg5-formula`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `fdBoundary_H_inner34_cont`, `fdBoundary_H_inner234`, `fdBoundary_H_eq_layered`
- **Visibility**: private
- **Lines**: 291-294
- **Notes**: none

### `lemma fdBoundary_H_inner34_cont`
- **Type**: `(H : ℝ) → Continuous (fdBoundary_H_inner34 H)`
- **What**: Continuity of the seg4-seg5 stitch.
- **How**: `Continuous.if_le` combining `fdBoundary_H_seg4_cont` and `fdBoundary_H_seg5_cont`; agreement at `t = 4` by substitution and `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H_seg4_cont`, `fdBoundary_H_seg5_cont`, `fdBoundary_H_inner34`
- **Used by**: `fdBoundary_H_inner234_cont`
- **Visibility**: private
- **Lines**: 296-301
- **Notes**: none

### `def fdBoundary_H_inner234`
- **Type**: `(H : ℝ) → ℝ → ℂ`
- **What**: Helper: seg3 stitched with `fdBoundary_H_inner34` at `t = 3`.
- **How**: `if t ≤ 3 then seg3-arc-formula else fdBoundary_H_inner34 H t`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H_inner34`
- **Used by**: `fdBoundary_H_inner234_cont`, `fdBoundary_H_inner1234`, `fdBoundary_H_eq_layered`
- **Visibility**: private
- **Lines**: 303-306
- **Notes**: none

### `lemma fdBoundary_H_inner234_cont`
- **Type**: `(H : ℝ) → Continuous (fdBoundary_H_inner234 H)`
- **What**: Continuity of seg3 + (seg4+seg5) stitch.
- **How**: `Continuous.if_le` with `fdBoundary_H_seg23b_cont` and `fdBoundary_H_inner34_cont`; at `t = 3`, unfold `fdBoundary_H_inner34`, rewrite exponential argument to `(2π/3) i`, then `exp_mul_I` + `cos/sin_pi_sub` + `cos/sin_pi_div_three`, `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H_seg23b_cont`, `fdBoundary_H_inner34_cont`, `fdBoundary_H_inner234`, `fdBoundary_H_inner34`
- **Used by**: `fdBoundary_H_inner1234_cont`
- **Visibility**: private
- **Lines**: 308-325
- **Notes**: none

### `def fdBoundary_H_inner1234`
- **Type**: `(H : ℝ) → ℝ → ℂ`
- **What**: Helper: seg2 stitched with `fdBoundary_H_inner234` at `t = 2`.
- **How**: `if t ≤ 2 then seg2-arc-formula else fdBoundary_H_inner234 H t`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H_inner234`
- **Used by**: `fdBoundary_H_inner1234_cont`, `fdBoundary_H_eq_layered`, `fdBoundary_H_continuous`
- **Visibility**: private
- **Lines**: 327-330
- **Notes**: none

### `lemma fdBoundary_H_inner1234_cont`
- **Type**: `(H : ℝ) → Continuous (fdBoundary_H_inner1234 H)`
- **What**: Continuity of seg2 + rest.
- **How**: `Continuous.if_le` with `fdBoundary_H_seg23_cont` and `fdBoundary_H_inner234_cont`; at `t = 2` show both formulas reduce to `↑(π/2) i` and so equal `i`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H_seg23_cont`, `fdBoundary_H_inner234_cont`, `fdBoundary_H_inner1234`, `fdBoundary_H_inner234`
- **Used by**: `fdBoundary_H_continuous`
- **Visibility**: private
- **Lines**: 332-349
- **Notes**: none

### `lemma fdBoundary_H_eq_layered`
- **Type**: `(H : ℝ) (t : ℝ) → fdBoundary_H H t = (if t ≤ 1 then seg1-formula else fdBoundary_H_inner1234 H t)`
- **What**: Pointwise equality between `fdBoundary_H` and the layered helper.
- **How**: Unfold all `fdBoundary_H_inner*` definitions and `fdBoundary_H`; `split_ifs <;> rfl`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_inner1234`, `fdBoundary_H_inner234`, `fdBoundary_H_inner34`
- **Used by**: `fdBoundary_H_continuous`
- **Visibility**: private
- **Lines**: 351-356
- **Notes**: none

### `theorem fdBoundary_H_continuous`
- **Type**: `(H : ℝ) → Continuous (fdBoundary_H H)`
- **What**: The variable-height FD boundary is continuous on `ℝ`.
- **How**: Rewrite via `fdBoundary_H_eq_layered` to layered form; `Continuous.if_le` between `fdBoundary_H_seg1_cont` and `fdBoundary_H_inner1234_cont`; at `t = 1` reduce inner branch to seg2 at `t = 1`, simplify the exponent to `↑(π/3) i`, apply `exp_mul_I`, `cos_pi_div_three`, `sin_pi_div_three`, `push_cast; ring`.
- **Hypotheses**: None.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_eq_layered`, `fdBoundary_H_seg1_cont`, `fdBoundary_H_inner1234_cont`, `fdBoundary_H_inner1234`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 358-381
- **Notes**: none

## File Summary
- Total declarations: ~38 (14 `def`s incl. helpers, ~13 named `lemma`s, 2 `theorem`s; multiple private helpers prefixed `fdBoundary_H_inner*`).
- Theme: Definitions and basic point/continuity properties for the standard SL₂(ℤ) fundamental domain boundary, both fixed-height (`heightCutoff = √3/2 + 1`) and variable-height versions, with the five segments (vertical-arc-arc-vertical-horizontal) stitched piecewise. Continuity of `fdBoundary_H` is proven via a layered `if-then-else` decomposition matched against `Continuous.if_le`.
- Provides building blocks: `fdBoundary`, `fdBoundary_H`, segment definitions `fdBoundary_seg{1..5}[_H]`, partitions `fdPartition`/`fdBoundary_H_partition`/`fdBoundaryFullPartition`, height `heightCutoff`, q-radius `seg5_q_radius_H`, plus point evaluations at `t = 0, 1, 2, 3, 4, 5` and closure lemmas.
- No `sorry`, no `axiom`, no `set_option` directives.
- No declaration exceeds 30 lines materially (most segment continuity proofs are sub-20-line `Continuous.if_le` chains).
