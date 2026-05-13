# Inventory: HW33Clean.lean

File: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33Clean.lean
Lines: 487

### `theorem hw_3_3_clean`
- **Type**: `{U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : ClosedPwC1Immersion x) (h_null : IsNullHomologous γ.toPwC1Immersion U) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S (fun s => poleOrderAt f s)) (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S) (s_star : ℂ) (hs_star_in : s_star ∈ S) (hγ_avoids_others : ...) (hw_star : HasGeneralizedWindingNumber ...) : HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path (2 * π * I * ∑ s, w(s) * residue f s)`
- **What**: Paper-faithful HW Theorem 3.3 for the simple-pole case with a **single** transverse crossing at distinguished pole `s_star`. 7 of the 13 oracles required by the raw `hw_3_3_simple_one_crossing_paper` are discharged automatically; only the geometric input `hw_star` (CPV existence at the crossing) and avoidance of other poles remain.
- **How**: Internally discharges three Laurent oracles via `h_polar_cancel_of_conditionB_simple`, `hI_polar_of_conditionB_simple`, `hI_holo_of_conditionB_simple`; then calls `hw_3_3_simple_one_crossing_paper` with those plus user-supplied data.
- **Hypotheses**: 8 paper hypotheses + 4 single-crossing inputs (`s_star ∈ S`, `hγ_avoids_others`, `hw_star`).
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `poleOrderAt`, `HasGeneralizedWindingNumber`, `generalizedWindingNumber`, `HasCauchyPVOn`, `residue`, `h_polar_cancel_of_conditionB_simple`, `hI_polar_of_conditionB_simple`, `hI_holo_of_conditionB_simple`, `hw_3_3_simple_one_crossing_paper`
- **Used by**: `hw_3_3_clean_avoids`, `hw_3_3_clean_with_scd`, `hw_3_3_clean_truly_full`
- **Visibility**: public
- **Lines**: 86-113
- **Notes**: >10 lines

### `theorem hw_3_3_clean_avoids`
- **Type**: `{U} (hU_open hU_ne) (S) (hS_in_U) (f) (hf) (γ) (h_null) (hSimple) (hCondA) (hCondB) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc 0 1, γ t ≠ s) (hs_ne : S.Nonempty) : HasCauchyPVOn ...`
- **What**: HW 3.3 specialization: γ avoids every pole. Combined with `hs_ne` (S nonempty) it picks any `s_star ∈ S`, and CPV existence at `s_star` is automatic via the avoidance δ-bound.
- **How**: `classical`; pick `s_star` from `hs_ne`; obtain `(δ, hδ_pos, hδ_bd)` from `avoids_finset_delta_bound`; apply `hasGeneralizedWindingNumber_of_avoids` to get `hw_star`; chain into `hw_3_3_clean`.
- **Hypotheses**: 8 paper + `hγ_avoids` + `hs_ne`.
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `HasSimplePoleAt`, `SatisfiesConditionA'`, `SatisfiesConditionB`, `poleOrderAt`, `HasGeneralizedWindingNumber`, `generalizedWindingNumber`, `HasCauchyPVOn`, `residue`, `avoids_finset_delta_bound`, `hasGeneralizedWindingNumber_of_avoids`, `hw_3_3_clean`
- **Used by**: `hw_3_3_clean_full`
- **Visibility**: public
- **Lines**: 122-153
- **Notes**: >10 lines

### `theorem hw_3_3_clean_with_scd`
- **Type**: `{U} ... (s_star : ℂ) (hs_star_in : s_star ∈ S) (hγ_avoids_others : ...) (D : SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s_star) : HasCauchyPVOn ...`
- **What**: HW 3.3 single-crossing variant taking a bundled `SingleCrossingData` instead of the raw `hw_star`. Most ergonomic when geometry+analysis are bundled.
- **How**: Extract `hw_raw := D.hasWindingNumber`; use `hw_raw.eq.symm ▸ hw_raw` to coerce to `HasGeneralizedWindingNumber γ s_star (generalizedWindingNumber γ s_star)`; apply `hw_3_3_clean`.
- **Hypotheses**: 8 paper + `s_star ∈ S` + `hγ_avoids_others` + `SingleCrossingData γ s_star`.
- **Uses from project**: `SingleCrossingData`, `SingleCrossingData.hasWindingNumber`, `HasGeneralizedWindingNumber`, `generalizedWindingNumber`, `hw_3_3_clean`, others as in `hw_3_3_clean`.
- **Used by**: `hw_3_3_clean_full`, `hw_3_3_clean_from_crossingGeometry`
- **Visibility**: public
- **Lines**: 166-190
- **Notes**: >10 lines

### `theorem hw_3_3_clean_full`
- **Type**: `{U} ... (s_star) (hs_star_in) (hγ_avoids_others) (h_at_star : (avoidance at s_star) ∨ Nonempty (SingleCrossingData γ s_star)) : HasCauchyPVOn ...`
- **What**: Disjunctive HW 3.3: at `s_star` either γ avoids it OR a `SingleCrossingData` witness exists. Other poles must be avoided.
- **How**: `rcases h_at_star`. In the avoidance branch, build `hγ_avoids` (combining `hγ_avoids_others` with `hγ_avoid_star` via `by_cases hs_eq : s = s_star`) and apply `hw_3_3_clean_avoids`. In the SCD branch, apply `hw_3_3_clean_with_scd` with `D.some`.
- **Hypotheses**: 8 paper + `s_star ∈ S` + `hγ_avoids_others` + disjunction `h_at_star`.
- **Uses from project**: `SingleCrossingData`, `hw_3_3_clean_avoids`, `hw_3_3_clean_with_scd`, others as in `hw_3_3_clean`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 202-236
- **Notes**: >10 lines

### `theorem hw_3_3_clean_from_crossingGeometry`
- **Type**: `{U} ... (s_star) (hs_star_in) (hγ_avoids_others) (G : CrossingGeometry γ s_star) (L : ℂ) (δ : ℝ → ℝ) (threshold : ℝ) (hthresh) (hδ_pos) (hδ_small) (h_far) (h_near) (ftcHyp : ArcFTCHyp γ s_star G.t₀ δ threshold L) : HasCauchyPVOn ...`
- **What**: Higher-level entry: assemble `SingleCrossingData` from `CrossingGeometry` (geometric `t₀`/`ht₀`) + user δ-data (cutoff bounds) + `ArcFTCHyp` (analytic FTC limit), then apply `hw_3_3_clean_with_scd`.
- **How**: `SingleCrossingData.ofGeometryAndFTC γ s_star G L δ threshold hthresh hδ_pos hδ_small h_far h_near ftcHyp` → feed to `hw_3_3_clean_with_scd`.
- **Hypotheses**: 8 paper + `s_star ∈ S` + `hγ_avoids_others` + `CrossingGeometry` + `(L, δ, threshold)` + analytic conditions (`hδ_pos`, `hδ_small`, `h_far`, `h_near`) + `ArcFTCHyp`.
- **Uses from project**: `CrossingGeometry`, `CrossingGeometry.t₀`, `ArcFTCHyp`, `SingleCrossingData.ofGeometryAndFTC`, `hw_3_3_clean_with_scd`, others as in `hw_3_3_clean`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 251-281
- **Notes**: >10 lines

### `theorem hw_3_3_clean_truly_full`
- **Type**: `{U} ... (s_star) (hs_star_in) (hγ_avoids_others) {t₀} (ht₀ : t₀ ∈ Ioo 0 1) (h_at : γ t₀ = s_star) (h_unique : ∀ t ∈ Icc 0 1, γ t = s_star → t = t₀) (h_flat : IsFlatOfOrder γ.toPath.extend t₀ 1) : HasCauchyPVOn ...`
- **What**: Paper-faithful endpoint of the single-crossing chain: the `h_at_star` disjunction is replaced by *minimal structural* data — a unique transverse crossing at `t₀` with `IsFlatOfOrder γ t₀ 1`. CPV existence at the crossing is proved internally.
- **How**: `HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full γ ht₀ h_at h_unique h_flat` gives `(L, hL : HasCauchyPV ...)`. Set `w := L/(2πI)`; use `Complex.two_pi_I_ne_zero` to write `L = 2πI·w`; package `hL` as `HasGeneralizedWindingNumber γ s_star w`; coerce to `generalizedWindingNumber γ s_star` via `.eq.symm ▸`; call `hw_3_3_clean`.
- **Hypotheses**: 8 paper + `s_star ∈ S` + `hγ_avoids_others` + `(t₀, ht₀, h_at, h_unique, h_flat)`.
- **Uses from project**: `IsFlatOfOrder`, `HungerbuhlerWasem.hasCauchyPV_inv_sub_of_flat_one_full`, `HasGeneralizedWindingNumber`, `generalizedWindingNumber`, `hw_3_3_clean`, others as in `hw_3_3_clean`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 315-358
- **Notes**: >10 lines

### `theorem hw_3_3_clean_multi`
- **Type**: `{U} ... {S} ... (γ) (h_null) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) (hCondB) (hCondA : SatisfiesConditionA' γ f S (fun s => PolarPartDecomposition.ofMeromorphicWithCondB ...).order s) (hx_notin_S : x ∉ ↑S) (h_no_corner_crossings) : HasCauchyPVOn S f γ (∑ s, 2πI · w(s) · residue f s)`
- **What**: Paper-faithful HW 3.3 simple-pole multi-pole multi-crossing form: γ may cross any subset of poles in `S` at transverse smooth interior points (not at piecewise-`C¹` corners).
- **How**: Build `hMero` from `hSimple` via `.meromorphicAt`; call `HungerbuhlerWasem.residueTheorem_crossing_full_spec`.
- **Hypotheses**: 8 paper + `hx_notin_S` + `h_no_corner_crossings`.
- **Uses from project**: `ClosedPwC1Immersion`, `HasSimplePoleAt`, `HasSimplePoleAt.meromorphicAt`, `MeromorphicAt`, `SatisfiesConditionB`, `SatisfiesConditionA'`, `IsNullHomologous`, `HungerbuhlerWasem.PolarPartDecomposition`, `HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB`, `HungerbuhlerWasem.residueTheorem_crossing_full_spec`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 392-417
- **Notes**: >10 lines; sum convention `∑ s, 2πI · w · res` (not `2πI · ∑ ...`).

### `theorem hw_3_3_clean_full_mero`
- **Type**: `{U} ... {S} ... (γ) (h_null) (hMero : ∀ s ∈ S, MeromorphicAt f s) (hCondB) (hCondA : SatisfiesConditionA' γ f S (PolarPartDecomposition.order)) (hx_notin_S) : HasCauchyPVOn ...`
- **What**: Maximally general paper-faithful HW 3.3 in this project: arbitrary-order meromorphic poles + arbitrary multi-pole multi-crossing. Hypothesis weakened from `hSimple` to `hMero`. The only Lean residual `hx_notin_S` is documented as a basepoint artifact.
- **How**: Direct call to `HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`.
- **Hypotheses**: 8 paper + `hx_notin_S`.
- **Uses from project**: `ClosedPwC1Immersion`, `IsNullHomologous`, `MeromorphicAt`, `SatisfiesConditionB`, `SatisfiesConditionA'`, `HungerbuhlerWasem.PolarPartDecomposition`, `HungerbuhlerWasem.PolarPartDecomposition.ofMeromorphicWithCondB`, `HungerbuhlerWasem.residueTheorem_crossing_paper_faithful_clean`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 450-469
- **Notes**: >10 lines

## File Summary

HW33Clean.lean: 487 lines, namespace `LeanModularForms`. The paper-faithful endpoint module for Hungerbühler–Wasem Theorem 3.3 (simple-pole + meromorphic, single-crossing + multi-crossing variants), composing the analytical/Laurent machinery into clean public API. Eight public theorems form a hierarchy:

1. `hw_3_3_clean` — 8 paper + 4 single-crossing inputs; 7 oracles auto-discharged.
2. `hw_3_3_clean_avoids` — full avoidance specialization (no crossing).
3. `hw_3_3_clean_with_scd` — single-crossing variant taking bundled `SingleCrossingData`.
4. `hw_3_3_clean_full` — disjunction of avoidance vs. `SingleCrossingData`.
5. `hw_3_3_clean_from_crossingGeometry` — assemble from `CrossingGeometry` + `ArcFTCHyp` + δ-data.
6. `hw_3_3_clean_truly_full` — minimal-data single-crossing form (no oracle, transversality via `IsFlatOfOrder`).
7. `hw_3_3_clean_multi` — simple-pole multi-crossing.
8. `hw_3_3_clean_full_mero` — maximal generality: meromorphic + multi-crossing.

No sorries, no axioms, no `set_option`s. The file is pure API composition with detailed docstrings explaining what each variant discharges and what residual data remains.
