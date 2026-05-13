# Inventory: AsymmetricSingleCrossing.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/AsymmetricSingleCrossing.lean`
Lines: 405

### `structure AsymmetricSingleCrossingData`
- **Type**: `(γ : PiecewiseC1Path x y) (z₀ : ℂ) : Type` with fields `L : ℂ`, `t₀ : ℝ`, `ht₀ : t₀ ∈ Ioo 0 1`, `δ_left δ_right : ℝ → ℝ`, `threshold : ℝ`, `hthresh : 0 < threshold`, and the bound + FTC + limit fields below.
- **What**: Bundled data for computing the generalized winding number at a single crossing where the chord-to-tangent constants on the two sides may differ. Stores left/right cutoffs `δ_left ε, δ_right ε`, threshold, positivity/smallness bounds, far-bound and near-bound predicates on each side, an FTC expression `E : ℝ → ℂ` whose far-segment integrals equal `E ε`, interval-integrability on the two far segments, and the limit `E(ε) → L`.
- **How**: Plain `structure` declaration; carries the geometric, integrability, and asymptotic data needed for the asymmetric CPV proof.
- **Hypotheses**: structure carries its hypotheses in fields; consumers (`hasCauchyPV`, etc.) supply these.
- **Uses from project**: `PiecewiseC1Path`, `PiecewiseC1Path.toPath.extend`.
- **Used by**: `AsymmetricSingleCrossingData.cpvIntegrand_zero_on_middle`, `cpvIntegrand_eq_full_left_ae`, `cpvIntegrand_eq_full_right_ae`, `cutoff_integral_eq_E`, `hasCauchyPV`, `hasWindingNumber`, `windingNumber_eq`, `windingNumber_neg_half`, `hasCauchyPV_simplePole`, `hasCauchyPV_simplePole_eq_two_pi_I_mul`, `SingleCrossingData.toAsymmetric`, `AsymmetricSingleCrossingData.mk_from_bounds`.
- **Visibility**: public
- **Lines**: 48-96
- **Notes**: 14 fields; replaces single-δ `SingleCrossingData` for asymmetric crossings

### `private theorem AsymmetricSingleCrossingData.cpvIntegrand_zero_on_middle`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) (h_mid_lt : D.t₀ - D.δ_left ε < D.t₀ + D.δ_right ε) : ∀ t ∈ uIoc (t₀ - δ_left ε) (t₀ + δ_right ε), cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t = 0`
- **What**: On the middle segment `(t₀ - δ_left ε, t₀ + δ_right ε)`, the cutoff integrand vanishes because the curve is ε-close to z₀ (so the cutoff `if`-guard `‖γ-z₀‖ > ε` fails).
- **How**: `simp only [cpvIntegrand]`; resolve `if_neg`; case-split on `t ≤ t₀`; the left branch uses `D.h_near_left`, the right branch `D.h_near_right` (both bounded via `linarith`).
- **Hypotheses**: `D` valid; `ε` in `(0, threshold)`; the middle interval is non-degenerate.
- **Uses from project**: `AsymmetricSingleCrossingData`, `cpvIntegrand`.
- **Used by**: `cutoff_integral_eq_E`.
- **Visibility**: private
- **Lines**: 104-118

### `private theorem AsymmetricSingleCrossingData.cpvIntegrand_eq_full_left_ae`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) (h_left_lt : 0 < D.t₀ - D.δ_left ε) : ∀ᵐ t ∂volume, t ∈ uIoc 0 (t₀ - δ_left ε) → cpvIntegrand ... t = (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t`
- **What**: On `[0, t₀ - δ_left ε]`, the cutoff integrand a.e. agrees with the unguarded integrand `(γ(t) - z₀)⁻¹ · γ'(t)` (because `‖γ(t) - z₀‖ > ε` there by `h_far_left`).
- **How**: Exclude the measure-zero singleton `{t₀ - δ_left ε}` via `compl_mem_ae_iff` + `Set.finite_singleton`; reduce to strict `t < t₀ - δ_left ε`; resolve `if_pos` via `D.h_far_left` (membership in `Icc 0 1` and `δ < t₀ - t`).
- **Hypotheses**: D valid; ε in `(0, threshold)`; `0 < t₀ - δ_left ε`.
- **Uses from project**: `AsymmetricSingleCrossingData`, `cpvIntegrand`.
- **Used by**: `cutoff_integral_eq_E`.
- **Visibility**: private
- **Lines**: 122-140

### `private theorem AsymmetricSingleCrossingData.cpvIntegrand_eq_full_right_ae`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) (h_right_lt : D.t₀ + D.δ_right ε < 1) : ∀ᵐ t ∂volume, t ∈ uIoc (t₀ + δ_right ε) 1 → cpvIntegrand ... = (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t`
- **What**: On `[t₀ + δ_right ε, 1]`, the cutoff integrand a.e. agrees with the unguarded integrand (because `‖γ(t) - z₀‖ > ε` by `h_far_right`).
- **How**: Same shape as the left version — exclude the singleton `{t₀ + δ_right ε}`, derive `t₀ < t`, resolve `if_pos` via `D.h_far_right`.
- **Hypotheses**: D valid; ε in `(0, threshold)`; `t₀ + δ_right ε < 1`.
- **Uses from project**: `AsymmetricSingleCrossingData`, `cpvIntegrand`.
- **Used by**: `cutoff_integral_eq_E`.
- **Visibility**: private
- **Lines**: 144-161

### `private theorem AsymmetricSingleCrossingData.cutoff_integral_eq_E`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) {ε : ℝ} (hε_pos : 0 < ε) (hε_lt : ε < D.threshold) : ∫ t in 0..1, cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t = D.E ε`
- **What**: For each valid ε, the full cutoff integral over `[0, 1]` equals `D.E ε` — the middle segment contributes zero, and the two outer segments sum to `E ε` by `h_ftc`.
- **How**: Use `cpvIntegrand_zero_on_middle`, `cpvIntegrand_eq_full_left_ae`, `cpvIntegrand_eq_full_right_ae` for pointwise/a.e. identifications; establish interval-integrability of each segment via `IntervalIntegrable.congr_ae` and `IntervalIntegrable.zero.congr`; split `∫_0^1 = ∫_0^{t₀-δ_L} + ∫_{t₀-δ_L}^{t₀+δ_R} + ∫_{t₀+δ_R}^1` via two `intervalIntegral.integral_add_adjacent_intervals`; use `intervalIntegral.integral_zero_ae` on middle and `intervalIntegral.integral_congr_ae` on the two outer pieces; finish with `D.h_ftc`.
- **Hypotheses**: D valid; ε in `(0, threshold)`.
- **Uses from project**: `AsymmetricSingleCrossingData`, `cpvIntegrand`, `cpvIntegrand_zero_on_middle`, `cpvIntegrand_eq_full_left_ae`, `cpvIntegrand_eq_full_right_ae`.
- **Used by**: `hasCauchyPV`.
- **Visibility**: private
- **Lines**: 165-205
- **Notes**: ~41 line proof; key composite tactic is the three-way split + `integral_congr_ae`

### `theorem AsymmetricSingleCrossingData.hasCauchyPV`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) : HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ D.L`
- **What**: From an asymmetric crossing data, the Cauchy principal value of `(z - z₀)⁻¹` along γ exists with value `D.L`.
- **How**: Unfold `HasCauchyPV`; observe that the cutoff integral is eventually equal to `D.E` near `0⁺` via `cutoff_integral_eq_E` (filter `Ioo_mem_nhdsGT D.hthresh`); transport via `Tendsto.congr'` from `D.h_limit`.
- **Hypotheses**: D valid (carries the FTC + limit).
- **Uses from project**: `AsymmetricSingleCrossingData`, `HasCauchyPV`, `cpvIntegrand`, `AsymmetricSingleCrossingData.cutoff_integral_eq_E`.
- **Used by**: `hasWindingNumber`, `hasCauchyPV_simplePole`.
- **Visibility**: public
- **Lines**: 217-225

### `theorem AsymmetricSingleCrossingData.hasWindingNumber`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) : HasGeneralizedWindingNumber γ z₀ (D.L / (2 * ↑Real.pi * I))`
- **What**: The generalized winding number at z₀ equals `L / (2πi)`.
- **How**: Rewrite `L / (2πi) = (2πi)⁻¹ · L` via `ring`; apply `hasGeneralizedWindingNumber_of_hasCauchyPV` on `D.hasCauchyPV`.
- **Hypotheses**: D valid.
- **Uses from project**: `AsymmetricSingleCrossingData`, `HasGeneralizedWindingNumber`, `AsymmetricSingleCrossingData.hasCauchyPV`, `hasGeneralizedWindingNumber_of_hasCauchyPV`.
- **Used by**: `windingNumber_eq`.
- **Visibility**: public
- **Lines**: 228-231

### `theorem AsymmetricSingleCrossingData.windingNumber_eq`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) : generalizedWindingNumber γ z₀ = D.L / (2 * ↑Real.pi * I)`
- **What**: The numerical winding number `generalizedWindingNumber γ z₀` equals `L / (2πi)`.
- **How**: One-line `D.hasWindingNumber.eq`.
- **Hypotheses**: D valid.
- **Uses from project**: `AsymmetricSingleCrossingData`, `generalizedWindingNumber`, `AsymmetricSingleCrossingData.hasWindingNumber`.
- **Used by**: `windingNumber_neg_half`, `hasCauchyPV_simplePole_eq_two_pi_I_mul`.
- **Visibility**: public
- **Lines**: 234-236

### `theorem AsymmetricSingleCrossingData.windingNumber_neg_half`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) (hL : D.L = -(↑Real.pi * I)) : generalizedWindingNumber γ z₀ = -1 / 2`
- **What**: If `L = -πi`, then the generalized winding number is `-1/2` (the FD-edge crossing value).
- **How**: Rewrite via `D.windingNumber_eq` and the hypothesis; `field_simp` closes given `π ≠ 0` and `I ≠ 0`.
- **Hypotheses**: D valid; `L = -(π · I)`.
- **Uses from project**: `AsymmetricSingleCrossingData`, `AsymmetricSingleCrossingData.windingNumber_eq`, `generalizedWindingNumber`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 239-245

### `theorem AsymmetricSingleCrossingData.hasCauchyPV_simplePole`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) (c : ℂ) : HasCauchyPV (fun z => c / (z - z₀)) γ z₀ (c * D.L)`
- **What**: For any complex `c`, the CPV of `c / (z - z₀)` along γ exists with value `c · L`.
- **How**: Multiply `D.hasCauchyPV` by `c` via `HasCauchyPV.smul`; simp with `div_eq_mul_inv` to rewrite `c/(z-z₀)` as `c · (z-z₀)⁻¹`.
- **Hypotheses**: D valid; c arbitrary.
- **Uses from project**: `AsymmetricSingleCrossingData`, `HasCauchyPV`, `HasCauchyPV.smul`, `AsymmetricSingleCrossingData.hasCauchyPV`.
- **Used by**: `hasCauchyPV_simplePole_eq_two_pi_I_mul`.
- **Visibility**: public
- **Lines**: 250-253

### `theorem AsymmetricSingleCrossingData.hasCauchyPV_simplePole_eq_two_pi_I_mul`
- **Type**: `(D : AsymmetricSingleCrossingData γ z₀) (c : ℂ) : HasCauchyPV (fun z => c / (z - z₀)) γ z₀ (2 * ↑Real.pi * I * generalizedWindingNumber γ z₀ * c)`
- **What**: Value form of the simple-pole CPV: the CPV of `c / (z - z₀)` equals `2πi · w(γ, z₀) · c`.
- **How**: Rewrite `c · L = 2πi · w · c` using `D.windingNumber_eq` and `field_simp` (with `2πi ≠ 0`); apply `hasCauchyPV_simplePole`.
- **Hypotheses**: D valid; c arbitrary.
- **Uses from project**: `AsymmetricSingleCrossingData`, `HasCauchyPV`, `generalizedWindingNumber`, `AsymmetricSingleCrossingData.windingNumber_eq`, `AsymmetricSingleCrossingData.hasCauchyPV_simplePole`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 258-267

### `def SingleCrossingData.toAsymmetric`
- **Type**: `(D : SingleCrossingData γ z₀) : AsymmetricSingleCrossingData γ z₀`
- **What**: Lifts a symmetric single-crossing data to the asymmetric framework by taking `δ_left = δ_right = δ`, enabling backwards compatibility for FD-curve constructors.
- **How**: Construct each field of `AsymmetricSingleCrossingData` from the corresponding `SingleCrossingData` field; for the left/right far/near bounds, transport `D.h_far`/`D.h_near` (which use `|t - t₀|`) by rewriting `|·|` via `abs_of_nonneg` / `abs_of_nonpos` and discharging the sign via `linarith`. Smallness uses `min_le_left`/`min_le_right` on `D.hδ_small`.
- **Hypotheses**: a valid `SingleCrossingData γ z₀`.
- **Uses from project**: `SingleCrossingData`, `AsymmetricSingleCrossingData`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 279-317
- **Notes**: ~39 line definition

### `structure AsymmetricArcFTCHyp`
- **Type**: `{x y : ℂ} (γ : PiecewiseC1Path x y) (z₀ : ℂ) (t₀ : ℝ) (δ_left δ_right : ℝ → ℝ) (threshold : ℝ) (L : ℂ) : Type` with fields `E`, `h_ftc`, `hint_left`, `hint_right`, `h_limit`.
- **What**: Bundles the analytic content (FTC equality `∫_0^{t₀-δ_L ε} + ∫_{t₀+δ_R ε}^1 = E ε`, integrability on left/right segments, and the limit `E(ε) → L`) for an asymmetric crossing.
- **How**: Plain `structure` declaration parallel to `ArcFTCHyp` but with separate δ_left/δ_right.
- **Hypotheses**: fields carried in the structure.
- **Uses from project**: `PiecewiseC1Path`.
- **Used by**: `AsymmetricSingleCrossingData.mk_from_bounds`.
- **Visibility**: public
- **Lines**: 330-351

### `def AsymmetricSingleCrossingData.mk_from_bounds`
- **Type**: `{x y : ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) {δ_left δ_right : ℝ → ℝ} {threshold : ℝ} (hthresh : 0 < threshold) (hδ_left_pos hδ_right_pos hδ_left_small hδ_right_small h_far_left h_far_right h_near_left h_near_right) {L : ℂ} (ftcHyp : AsymmetricArcFTCHyp γ z₀ t₀ δ_left δ_right threshold L) : AsymmetricSingleCrossingData γ z₀`
- **What**: Builder/constructor for `AsymmetricSingleCrossingData`, splitting the input into geometric ingredients (δ-cutoffs and far/near bounds) plus an `AsymmetricArcFTCHyp` analytic bundle.
- **How**: Plain `structure` instance — populate the 14 fields of `AsymmetricSingleCrossingData` from the inputs.
- **Hypotheses**: ht₀ in `Ioo 0 1`, threshold positive, δ-positivity/smallness, far/near bounds on both sides, FTC + integrability + limit bundle.
- **Uses from project**: `PiecewiseC1Path`, `AsymmetricSingleCrossingData`, `AsymmetricArcFTCHyp`.
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 363-403

## File Summary

Introduces the **asymmetric** single-crossing framework, generalizing `SingleCrossingData` by allowing different left/right cutoff functions `δ_left ε ≠ δ_right ε`. Two top-level structures (`AsymmetricSingleCrossingData`, `AsymmetricArcFTCHyp`) plus seven public theorems prove that the CPV exists at L, the generalized winding number equals `L / (2πi)`, a `-1/2` specialization, and simple-pole CPV variants. A lift `SingleCrossingData.toAsymmetric` keeps existing symmetric constructors usable. Four private lemmas (`cpvIntegrand_zero_on_middle`, `cpvIntegrand_eq_full_left_ae`, `cpvIntegrand_eq_full_right_ae`, `cutoff_integral_eq_E`) carry the integral-splitting work. No `sorry`/`axiom`/heartbeat overrides.
