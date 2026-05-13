# ModularSideProof.md

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ModularSideProof.lean` (419 lines)

Namespace: (none — top-level, in `noncomputable section`)

### `lemma two_pi_I_ne_zero_ms`
- **Type**: `(2 : ℂ) * ↑Real.pi * I ≠ 0`
- **What**: `2πi ≠ 0` in ℂ.
- **How**: `simp` with `ne_eq`, `mul_eq_zero`, `OfNat.ofNat_ne_zero`, `ofReal_eq_zero`, `Real.pi_ne_zero`, `I_ne_zero`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: unused in file
- **Visibility**: private (omits f, hf)
- **Lines**: 74-77
- **Notes**: `omit f hf` to drop irrelevant section vars.

### `structure ModularSideData`
- **Type**: `(H : ℝ) (F_eps : ℝ → ℂ) → Type`
- **What**: Bundles the three analytical ingredients of the modular side at height H: an `arc_value` (`= -(2πi · k/12)`), a `horiz_value` (`= 2πi · ord_cusp`), and a `Tendsto` of `F_eps` to their sum (the T-cancellation absorbed: seg1 + seg4 = 0).
- **How**: Plain `structure` with five fields: `arc_value`, `horiz_value`, `arc_eq`, `horiz_eq`, `h_tendsto`.
- **Hypotheses**: none (just packages data).
- **Uses from project**: `orderAtCusp'`, modular form section variables `f`, `k`.
- **Used by**: `modularSide_tendsto_of_data`, `modularSide_for_discharge`, `modularSideData_of_avoidance`.
- **Visibility**: public
- **Lines**: 93-104
- **Notes**: documentation-rich.

### `theorem modularSide_tendsto_of_data`
- **Type**: `{H : ℝ} {F_eps : ℝ → ℂ} (data : ModularSideData f H F_eps) : Tendsto F_eps (𝓝[>] 0) (𝓝 (-(2*π*I * ((k:ℂ)/12 - orderAtCusp' f))))`
- **What**: Extract from `ModularSideData` the Tendsto statement that `F_eps` converges to `-(2πi · (k/12 - ord_cusp))`.
- **How**: Show `data.arc_value + data.horiz_value` equals the target via `data.arc_eq`, `data.horiz_eq`, and `ring`; conclude with `data.h_tendsto`.
- **Hypotheses**: a `ModularSideData f H F_eps` witness.
- **Uses from project**: `ModularSideData`, `orderAtCusp'`.
- **Used by**: `modularSide_for_discharge`.
- **Visibility**: public
- **Lines**: 113-124
- **Notes**: none

### `theorem modularSide_three_piece`
- **Type**: `(k : ℤ) {ord_cusp : ℂ} (arc_val horiz_val : ℂ) (h_arc : arc_val = -(2*π*I * ((k:ℂ)/12))) (h_horiz : horiz_val = 2*π*I*ord_cusp) : arc_val + horiz_val = -(2*π*I * ((k:ℂ)/12 - ord_cusp))`
- **What**: Three-piece modular side: 0 (T-cancel) + arc + horiz equals `-(2πi · (k/12 - ord_cusp))`.
- **How**: Substitute the two equalities and finish with `ring`.
- **Hypotheses**: arc and horiz match expected closed forms.
- **Uses from project**: none.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 133-139
- **Notes**: `omit f hf`.

### `theorem modularSide_from_segments`
- **Type**: `(k : ℤ) {ord_cusp : ℂ} (seg1_val seg2_val seg3_val seg4_val seg5_val : ℂ) (h_T_cancel : seg1_val + seg4_val = 0) (h_arc : seg2_val + seg3_val = -(2*π*I * ((k:ℂ)/12))) (h_horiz : seg5_val = 2*π*I*ord_cusp) : seg1_val + seg2_val + seg3_val + seg4_val + seg5_val = -(2*π*I * ((k:ℂ)/12 - ord_cusp))`
- **What**: Five-segment decomposition: combining T-cancellation, arc, and horizontal contributions gives the modular-side total `-(2πi · (k/12 - ord_cusp))`.
- **How**: Rearrange segments via `ring` into the form `(seg1+seg4) + (seg2+seg3) + seg5`; substitute the three hypotheses; finish with `ring`.
- **Hypotheses**: T-cancel, arc, and horizontal closed-form equations.
- **Uses from project**: none.
- **Used by**: `modularSide_tendsto_of_segments`.
- **Visibility**: public
- **Lines**: 143-153
- **Notes**: `omit f hf`.

### `theorem modularSide_direct`
- **Type**: `(_S : Finset UpperHalfPlane) (_hS) (_hS_complete) (_mkD) (F_int : ℝ → ℝ → ℂ) (H_mod : ℝ) (_hH_mod_gt) (h_mod : ∀ H, H_mod ≤ H → (hH : √3/2 < H) → Tendsto (F_int H) (𝓝[>] 0) (𝓝 (-(2*π*I*((k:ℂ)/12 - orderAtCusp' f))))) : ∀ H, … same Tendsto`
- **What**: Identity passthrough: from a `h_mod` Tendsto hypothesis, produce the same `h_mod` Tendsto (signature consistency wrapper for `discharge_pvChain_full`).
- **How**: `h_mod`.
- **Hypotheses**: the Tendsto hypothesis itself.
- **Uses from project**: `FDWindingDataFull`, `orderAtCusp'`, `𝒟`, `orderOfVanishingAt'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 161-175
- **Notes**: many unused (`_`-prefixed) arguments for API matching.

### `theorem modularSide_for_discharge`
- **Type**: `(_S) (_hS) (_hS_complete) (_mkD) (F_int : ℝ → ℝ → ℂ) (H_mod : ℝ) (_hH_mod_gt) (mk_data : ∀ H, H_mod ≤ H → (hH : √3/2 < H) → ModularSideData f H (F_int H)) : ∀ H, H_mod ≤ H → … Tendsto (F_int H) (𝓝[>] 0) (𝓝 (-(2*π*I*((k:ℂ)/12 - orderAtCusp' f))))`
- **What**: Given a per-height constructor for `ModularSideData`, produce the `h_mod` parameter for `discharge_pvChain_full`.
- **How**: For each H above threshold, apply `modularSide_tendsto_of_data` to `mk_data H hH_ge hH`.
- **Hypotheses**: per-height `ModularSideData` constructor.
- **Uses from project**: `FDWindingDataFull`, `ModularSideData`, `orderAtCusp'`, `𝒟`, `orderOfVanishingAt'`, `modularSide_tendsto_of_data`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 181-194
- **Notes**: none

### `def modularSideData_of_avoidance`
- **Type**: `(H : ℝ) (arc : ℂ) (h_arc_eq) (horiz : ℂ) (h_horiz_eq) (F_eps : ℝ → ℂ) (h_tendsto : Tendsto F_eps (𝓝[>] 0) (𝓝 (arc + horiz))) : ModularSideData f H F_eps`
- **What**: Construct a `ModularSideData` value from explicit arc/horizontal values and a Tendsto hypothesis.
- **How**: Direct structure literal.
- **Hypotheses**: arc and horiz match expected closed forms; Tendsto holds.
- **Uses from project**: `ModularSideData`, `orderAtCusp'`.
- **Used by**: unused in file
- **Visibility**: public (`noncomputable def`)
- **Lines**: 200-213
- **Notes**: none

### `theorem modularSide_tendsto_of_segments`
- **Type**: `(I_seg1 I_seg2 I_seg3 I_seg4 I_seg5 : ℂ) (h_T_cancel) (h_arc) (h_horiz) (F_eps : ℝ → ℂ) (h_ev : Tendsto F_eps (𝓝[>] 0) (𝓝 (I_seg1+I_seg2+I_seg3+I_seg4+I_seg5))) : Tendsto F_eps (𝓝[>] 0) (𝓝 (-(2*π*I*((k:ℂ)/12 - orderAtCusp' f))))`
- **What**: Given the five-segment values satisfying T-cancellation, arc, and horizontal closed forms, plus a Tendsto to their sum, produce the modular-side Tendsto.
- **How**: Apply `modularSide_from_segments` to evaluate the total; rewrite the inner limit value of `h_ev`.
- **Hypotheses**: T-cancellation, arc, horizontal closed forms; F_eps tends to total.
- **Uses from project**: `orderAtCusp'`, `modularSide_from_segments`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 222-237
- **Notes**: none

### `theorem modularSide_complete_discharge`
- **Type**: `(S : Finset UpperHalfPlane) (hS) (hS_complete) (mkD) (F_int) (H_S : ℝ) (hH_S : ∀ s ∈ S, (s:ℂ).im < H_S) (H_res H_mod : ℝ) (hH_res_gt) (h_res : ∀ H, H_res ≤ H → (hH : √3/2 < H) → Tendsto (F_int H) (𝓝[>] 0) (𝓝 (2πI · ∑ s ∈ S, gWN · ord))) (hH_mod_gt) (h_mod) : ∃ H' D, (∀ s ∈ S, (s:ℂ).im < H') ∧ ∑ gWN · ord = -((k:ℂ)/12 - orderAtCusp' f)`
- **What**: Complete modular-side discharge: combine residue-side Tendsto + modular-side Tendsto into the conclusion of `discharge_pvChain_full` (a single witness height H' and FD data D, plus the orbifold-residue identity equal to `-((k:ℂ)/12 - ord_cusp)`).
- **How**: Delegate entirely to `discharge_pvChain_full f S hS hS_complete mkD H_S hH_S F_int H_res hH_res_gt h_res H_mod hH_mod_gt h_mod`.
- **Hypotheses**: residue side Tendsto eventually; modular side Tendsto eventually; standard FD data and height bounds.
- **Uses from project**: `FDWindingDataFull`, `FDWindingDataFull.boundary`, `discharge_pvChain_full`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`, `𝒟`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 244-269
- **Notes**: `omit hf`; >30 lines (signature).

### `theorem T_cancel_segment_integrals`
- **Type**: `{F : ℝ → ℂ} (h_cancel : ∀ t ∈ Icc 0 (1/5), F (4/5 - t) = -(F t)) (_h_int : IntervalIntegrable F volume 0 (1/5)) : (∫ t in 0..(1/5), F t) + (∫ t in (3/5)..(4/5), F t) = 0`
- **How**: Change of variables on seg4 via `intervalIntegral.integral_comp_sub_left` (a=0,b=1/5) yields `∫ F(4/5 - u) over [0,1/5]`; pointwise cancellation via `integral_congr` + `h_cancel` rewrites to `-∫ F`; combine `h_sub` and `h_neg_int` to get `0`. Key lemma: `intervalIntegral.integral_comp_sub_left`.
- **What**: T-cancellation: under the pointwise antisymmetry `F(4/5 - t) = -F(t)` on `[0, 1/5]`, the integrals over `[0, 1/5]` and `[3/5, 4/5]` sum to 0.
- **Hypotheses**: pointwise cancellation on closed interval `[0, 1/5]`; integrability.
- **Uses from project**: none.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 282-306
- **Notes**: `omit f hf`; >10 lines.

### `theorem arc_contribution_eq`
- **Type**: `(k : ℤ) : -(↑k * ↑Real.pi * I / 6) = -(2 * ↑Real.pi * I * ((k : ℂ) / 12))`
- **What**: Restatement of the arc contribution: `-(kπi/6) = -(2πi · k/12)`.
- **How**: Direct invocation of `arc_contribution_eq_neg_k_over_12 k`.
- **Hypotheses**: none (k : ℤ).
- **Uses from project**: `arc_contribution_eq_neg_k_over_12`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 312-315
- **Notes**: `omit f hf`.

### `structure HorizontalContributionData`
- **Type**: `{H : ℝ} (γ : PiecewiseC1Path (fdStart H) (fdStart H)) → Type`
- **What**: Data structure asserting the seg5 integral equals `2πi · ord_cusp`.
- **How**: Single field `seg5_integral_eq`.
- **Hypotheses**: none (just packages data).
- **Uses from project**: `PiecewiseC1Path`, `fdStart`, `logDeriv`, `UpperHalfPlane.ofComplex`, `orderAtCusp'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 320-327
- **Notes**: none

### `theorem modularSide_of_avoidance_and_ingredients`
- **Type**: `(F_eps : ℝ → ℂ) (contour_val : ℂ) (h_tendsto : Tendsto F_eps (𝓝[>] 0) (𝓝 contour_val)) (h_decomp : contour_val = -(2*π*I*((k:ℂ)/12 - orderAtCusp' f))) : Tendsto F_eps (𝓝[>] 0) (𝓝 (-(2*π*I*((k:ℂ)/12 - orderAtCusp' f))))`
- **What**: If F_eps Tendsto contour_val and contour_val equals the modular side expression, produce the modular side Tendsto.
- **How**: Rewrite `h_decomp` into `h_tendsto`.
- **Hypotheses**: Tendsto to contour_val; decomposition equation.
- **Uses from project**: `orderAtCusp'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 335-343
- **Notes**: none

### `theorem modularSide_tendsto_of_eventually_eq`
- **Type**: `(F_eps : ℝ → ℂ) (L : ℂ) (hL : L = -(2*π*I*((k:ℂ)/12 - orderAtCusp' f))) (h_ev : ∀ᶠ ε in 𝓝[>] 0, F_eps ε = L) : Tendsto F_eps (𝓝[>] 0) (𝓝 (-(2*π*I*((k:ℂ)/12 - orderAtCusp' f))))`
- **What**: If F_eps is eventually equal to a constant L that equals the modular side expression, produce the modular side Tendsto.
- **How**: Rewrite `← hL`; use `tendsto_const_nhds.congr'` with `Filter.EventuallyEq.symm h_ev`.
- **Hypotheses**: L matches expected value; F_eps eventually equals L.
- **Uses from project**: `orderAtCusp'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 346-354
- **Notes**: none

### `theorem modularSide_main`
- **Type**: `(_mkD : ∀ H, √3/2 < H → FDWindingDataFull H) (F_int : ℝ → ℝ → ℂ) (H_mod : ℝ) (_hH_mod_gt) (h_mod : ∀ H, H_mod ≤ H → (hH : √3/2 < H) → Tendsto (F_int H) (𝓝[>] 0) (𝓝 …)) : ∀ H, … Tendsto (F_int H) (𝓝[>] 0) (𝓝 (-(2*π*I*((k:ℂ)/12 - orderAtCusp' f))))`
- **What**: Identity wrapper: pass through the `h_mod` parameter to produce itself (matches the signature expected by `discharge_pvChain_full`).
- **How**: `h_mod`.
- **Hypotheses**: per-height Tendsto.
- **Uses from project**: `FDWindingDataFull`, `orderAtCusp'`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 362-374
- **Notes**: none

### `theorem valence_formula_of_modular_and_residue_sides`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete) (mkD) (H_S : ℝ) (hH_S) (F_int) (H_res H_mod : ℝ) (hH_res_gt) (h_res) (hH_mod_gt) (h_mod) : orderAtCusp' f + (1/2)·ord_i + (1/3)·ord_ρ + (interior orbifold sum) + (left-vert sum) + (left-arc sum) = (k:ℂ)/12`
- **What**: Full valence formula: combining the residue-side and modular-side Tendsto, by uniqueness of limits, yields the classical sum of orders over the fundamental domain orbifold equals k/12.
- **How**: Direct delegation to `valence_formula_of_two_sides`.
- **Hypotheses**: residue-side Tendsto eventually; modular-side Tendsto eventually; FD data and bounds.
- **Uses from project**: `FDWindingDataFull`, `FDWindingDataFull.boundary`, `valence_formula_of_two_sides`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `sLeftVertFM`, `𝒟`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 386-417
- **Notes**: `omit hf`; >30 lines.

## File Summary

`ModularSideProof.lean` provides the modular side of the PV chain: the Cauchy principal value integral of `logDeriv(f)` around the fundamental-domain boundary converges to `-(2πi · (k/12 - ord_cusp))`. The file is structured in four layers:

1. **`ModularSideData` structure** bundles the analytical ingredients (arc value, horizontal value, Tendsto) at a given height H. `modularSide_tendsto_of_data` extracts the modular-side Tendsto from it.

2. **Segment algebra** — pure algebraic combinations: `modularSide_three_piece` (3 pieces) and `modularSide_from_segments` (5 segments, with T-cancellation), and their Tendsto upgrades `modularSide_tendsto_of_segments`. `T_cancel_segment_integrals` proves the T-cancellation `seg1 + seg4 = 0` from pointwise antisymmetry on `[0, 1/5]`.

3. **Bridge layer** — interface theorems for `discharge_pvChain_full`: `modularSide_direct`, `modularSide_for_discharge`, `modularSide_complete_discharge` (the full discharge combining both sides into the witness of `discharge_pvChain_full`). The constructor `modularSideData_of_avoidance` builds `ModularSideData` from explicit ingredients. `modularSide_of_avoidance_and_ingredients` and `modularSide_tendsto_of_eventually_eq` are alternative Tendsto-introduction wrappers. `modularSide_main` is a pure passthrough.

4. **`HorizontalContributionData` structure** packages the seg5 = 2πi·ord_cusp equation for future use (unused in file).

5. **Integration with `PVChainProof`**: `valence_formula_of_modular_and_residue_sides` produces the full classical valence formula (sum of orders = k/12) by delegating to `valence_formula_of_two_sides`. `arc_contribution_eq` is a trivial restatement.

Total: 1 `omit f hf` private lemma + 2 structures + 1 noncomputable def + 13 public theorems = 17 declarations. No sorries, no axioms. Uses `attribute [local instance] Classical.propDecidable`. The file is essentially a thin algebra+plumbing layer above `PVChainProof.discharge_pvChain_full` and `ModularContourIntegral`.

DONE: 14+15+10+17

Wait — recounting `ModularSideProof.lean`: 1 lemma + 2 structures (`ModularSideData`, `HorizontalContributionData`) + 1 def + 13 theorems = 17. For final report we use the count: 14 (ExitTimeExcision) + 15 (CauchyPrimitive) + 10 (HW33PVSing) + 17 (ModularSideProof) = 56.
