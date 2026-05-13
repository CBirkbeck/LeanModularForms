# Inventory: PVChainProof.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/PVChainProof.lean`
Lines: 470

### `private lemma pvChain_two_pi_I_ne_zero`
- **Type**: `(2 : ℂ) * ↑Real.pi * I ≠ 0`
- **What**: `2πi ≠ 0` over `ℂ`
- **How**: `simp [Real.pi_ne_zero]`
- **Hypotheses**: none (uses `omit f hf in`)
- **Uses from project**: []
- **Used by**: `pvChainIdentity`, `eq_of_two_pi_I_mul_eq`, `eq_neg_of_two_pi_I_mul_eq_neg`
- **Visibility**: private
- **Lines**: 71-73

### `structure PVChainData`
- **Type**: `(S : Finset UpperHalfPlane) (H : ℝ) → Type`
- **What**: Bundles, at height `H`: `FDWindingDataFull H`, the height bound for points of `S`, a shared ε-truncated integrand `F_eps`, plus the residue-side and modular-side `Tendsto` limits to `2πi · Σ gWN · ord` and `−2πi (k/12 − ord_cusp)` respectively
- **How**: standard `structure` definition (definitional)
- **Hypotheses**: variable `f : ModularForm (Gamma 1) k`
- **Uses from project**: `FDWindingDataFull`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`
- **Used by**: `pvChainIdentity`, `discharge_pvChain`, `pvChain_rearranged`, `valence_formula_of_pvChainData`
- **Visibility**: public
- **Lines**: 89-108
- **Notes**: takes the modular form `f` and proof `hf : f ≠ 0` as section variables

### `theorem pvChainIdentity`
- **Type**: `(S : Finset UpperHalfPlane) {H : ℝ} (data : PVChainData f S H) : Σ s ∈ S, gWN(D.boundary, s) · ord(f, s) = -((k : ℂ)/12 - ord_cusp(f))`
- **What**: The PV chain identity: equates the winding-weighted ord sum to `-(k/12 - ord_∞)` by uniqueness of limits and cancellation of `2πi`
- **How**: `tendsto_nhds_unique data.h_res data.h_mod` gives equality scaled by `2πi`, then `mul_left_cancel₀` with `pvChain_two_pi_I_ne_zero` after rewriting `-(2πi · b) = 2πi · (-b)`
- **Hypotheses**: `PVChainData` at some height
- **Uses from project**: `pvChain_two_pi_I_ne_zero`
- **Used by**: `discharge_pvChain`, `pvChain_rearranged`, `discharge_pvChain_full`, `discharge_pvChain_full_Hgt1`
- **Visibility**: public
- **Lines**: 122-142
- **Notes**: instantiates `NeBot` on `𝓝[>] 0`

### `theorem discharge_pvChain`
- **Type**: `(S : Finset UpperHalfPlane) (_hS) (_hS_complete) {H : ℝ} (data : PVChainData f S H) : ∃ H' D, height bound ∧ winding-sum identity`
- **What**: Discharges the existential `h_pvChain` hypothesis of `valence_formula_orbit_sum_of_pvChain` by packaging `pvChainIdentity` with the existing height/data
- **How**: returns `⟨H, data.D, data.hH_above, pvChainIdentity f S data⟩`
- **Hypotheses**: `PVChainData f S H`; `hS` and `hS_complete` (unused but matching CoreIdentityProof signature)
- **Uses from project**: `pvChainIdentity`, `FDWindingDataFull`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`
- **Used by**: `valence_formula_of_pvChainData`
- **Visibility**: public
- **Lines**: 152-162

### `theorem discharge_pvChain_full`
- **Type**: `(S : Finset UpperHalfPlane) (_hS) (_hS_complete) (mkD : ∀ H, √3/2 < H → FDWindingDataFull H) (H_S, hH_S) (F : ℝ → ℝ → ℂ) (H_res, hH_res_gt, h_res) (H_mod, _hH_mod_gt, h_mod) : ∃ H' D, ...`
- **What**: Builds `h_pvChain` from a constructor `mkD` for `FDWindingDataFull` (valid for `H > √3/2`) plus existential height bounds on residue and modular sides
- **How**: sets `H = max(max H_res H_mod) H_S + 1`, derives `H_res ≤ H`, `H_mod ≤ H`, `√3/2 < H`, and height-above for `S`; assembles a `PVChainData` and applies `pvChainIdentity` (proof >10 lines)
- **Hypotheses**: `mkD` constructor; height-above for `S`; residue-side and modular-side `Tendsto` for all sufficiently large `H`
- **Uses from project**: `pvChainIdentity`, `FDWindingDataFull`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`
- **Used by**: `valence_formula_of_two_sides`
- **Visibility**: public
- **Lines**: 179-224
- **Notes**: >10 lines

### `theorem pvChain_rearranged`
- **Type**: `(S : Finset UpperHalfPlane) {H : ℝ} (data : PVChainData f S H) : ord_cusp + (-Σ gWN · ord) = (k : ℂ)/12`
- **What**: Algebraic rearrangement of the PV chain identity to `ord_∞ + (-weighted_sum) = k/12`
- **How**: `linear_combination -h` using `h := pvChainIdentity f S data`
- **Hypotheses**: `PVChainData f S H`
- **Uses from project**: `pvChainIdentity`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 230-239

### `def FDWindingDataFull.ofWindingData`
- **Type**: `{H : ℝ} (D : FDWindingData H) (h_bdry : ∀ z : ℂ, z.im > 0 → z.im < H → z ≠ I → z ≠ ρ → z ≠ ρ+1 → ¬(‖z‖ > 1 ∧ |z.re| < 1/2) → normSq z ≥ 1 → |z.re| ≤ 1/2 → HasGeneralizedWindingNumber D.boundary z (-1/2)) : FDWindingDataFull H`
- **What**: Constructor: extends `FDWindingData` to `FDWindingDataFull` given the smooth-boundary winding hypothesis (`gWN = -1/2` for non-elliptic on-curve points)
- **How**: structure constructor with `toFDWindingData := D`, `boundary_winding := h_bdry`
- **Hypotheses**: per-point `HasGeneralizedWindingNumber` at non-elliptic boundary points
- **Uses from project**: `FDWindingData`, `FDWindingDataFull`, `HasGeneralizedWindingNumber`, `ellipticPointRho`, `ellipticPointRhoPlusOne`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 250-259

### `theorem eq_of_two_pi_I_mul_eq`
- **Type**: `{a b : ℂ} (h : 2 * ↑Real.pi * I * a = 2 * ↑Real.pi * I * b) : a = b`
- **What**: Cancellation: if `2πi · a = 2πi · b` then `a = b`
- **How**: `mul_left_cancel₀ pvChain_two_pi_I_ne_zero h`
- **Hypotheses**: section variables omitted via `omit f hf`
- **Uses from project**: `pvChain_two_pi_I_ne_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 266-269

### `theorem eq_neg_of_two_pi_I_mul_eq_neg`
- **Type**: `{a b : ℂ} (h : 2 * ↑Real.pi * I * a = -(2 * ↑Real.pi * I * b)) : a = -b`
- **What**: Cancellation variant: if `2πi · a = -(2πi · b)` then `a = -b`
- **How**: rewrites `-(2πi · b) = 2πi · (-b)` via `mul_neg`, then `mul_left_cancel₀ pvChain_two_pi_I_ne_zero`
- **Hypotheses**: section variables omitted
- **Uses from project**: `pvChain_two_pi_I_ne_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 273-279

### `theorem exists_height_above_finset`
- **Type**: `(S : Finset UpperHalfPlane) : ∃ H_S : ℝ, ∀ s ∈ S, (s : ℂ).im < H_S`
- **What**: Existence of a height upper bound for the imaginary parts of a finite set of upper-half-plane points
- **How**: case-splits on `S.Nonempty`; uses `Finset.sup'` of the imaginary-part function `+ 1` for the nonempty case; takes `1` for empty
- **Hypotheses**: none (section variables omitted)
- **Uses from project**: []
- **Used by**: `exists_height_above_finset_and_sqrt3`
- **Visibility**: public
- **Lines**: 286-295

### `theorem exists_height_above_finset_and_sqrt3`
- **Type**: `(S : Finset UpperHalfPlane) : ∃ H_S : ℝ, √3/2 < H_S ∧ ∀ s ∈ S, (s : ℂ).im < H_S`
- **What**: Combines `exists_height_above_finset` with the lower bound `√3/2 < H_S`
- **How**: take `max H₁ (√3/2) + 1`, verify both inequalities by `linarith` with `le_max_left/right`
- **Hypotheses**: section variables omitted
- **Uses from project**: `exists_height_above_finset`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 299-306

### `theorem valence_formula_of_pvChainData`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ...) {H : ℝ} (data : PVChainData f S H) : ord_cusp + (1/2) ord_i + (1/3) ord_ρ + Σ ord (strict-interior) + Σ ord (leftVert) + Σ ord (left-arc) = (k : ℂ)/12`
- **What**: Orbit-sum valence formula via `PVChainData`: textbook form
- **How**: applies `valence_formula_orbit_sum_of_pvChain` (from `CoreIdentityProof.lean`) to the existential produced by `discharge_pvChain`
- **Hypotheses**: `S` lies in the fundamental domain `𝒟` and contains every zero in `𝒟`; `PVChainData`
- **Uses from project**: `discharge_pvChain`, `valence_formula_orbit_sum_of_pvChain`, `orderAtCusp'`, `orderOfVanishingAt'`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `sLeftVertFM`
- **Used by**: unused in file
- **Visibility**: public (uses `omit hf`)
- **Lines**: 317-334

### `theorem valence_formula_of_two_sides`
- **Type**: `(S, hS, hS_complete, mkD over √3/2, H_S/hH_S, F, H_res/hH_res_gt/h_res, H_mod/hH_mod_gt/h_mod) : textbook orbit-sum identity = (k : ℂ)/12`
- **What**: Complete interface: from `mkD`, residue, and modular `Tendsto` data, produce the full orbit-sum valence formula
- **How**: chains `discharge_pvChain_full` with `valence_formula_orbit_sum_of_pvChain`
- **Hypotheses**: `mkD` valid for `H > √3/2`; `Tendsto` hypotheses for both sides
- **Uses from project**: `discharge_pvChain_full`, `valence_formula_orbit_sum_of_pvChain`, plus textbook decoration names
- **Used by**: unused in file
- **Visibility**: public (uses `omit hf`)
- **Lines**: 347-384

### `theorem discharge_pvChain_full_Hgt1`
- **Type**: variant of `discharge_pvChain_full` with `mkD : ∀ H, 1 < H → FDWindingDataFull H` instead of `> √3/2`
- **What**: Same as `discharge_pvChain_full` but for the stronger lower bound `H > 1`
- **How**: identical structure: sets `H = max(max H_res H_mod) H_S + 1`, derives `1 < H` from `hH_res_gt`, assembles `PVChainData`, applies `pvChainIdentity` (proof >10 lines)
- **Hypotheses**: `mkD` valid for `H > 1`; corresponding `Tendsto` hypotheses
- **Uses from project**: `pvChainIdentity`, `FDWindingDataFull`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`
- **Used by**: `valence_formula_of_two_sides_Hgt1`
- **Visibility**: public (uses `omit hf`)
- **Lines**: 391-431
- **Notes**: >10 lines

### `theorem valence_formula_of_two_sides_Hgt1`
- **Type**: variant of `valence_formula_of_two_sides` with `mkD` over `H > 1`
- **What**: Complete interface variant: the `FDWindingDataFull` constructor only requires `H > 1`
- **How**: chains `discharge_pvChain_full_Hgt1` with `valence_formula_orbit_sum_of_pvChain`
- **Hypotheses**: `mkD` valid for `H > 1`; `Tendsto` hypotheses
- **Uses from project**: `discharge_pvChain_full_Hgt1`, `valence_formula_orbit_sum_of_pvChain`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 436-468

## File Summary

PVChainProof.lean discharges the existential hypothesis `h_pvChain` consumed by `valence_formula_orbit_sum_of_pvChain` in `CoreIdentityProof.lean`. The pivotal `structure PVChainData` bundles two `Tendsto` statements that say the same ε-truncated integrand converges to the residue side `2πi · Σ gWN · ord` and to the modular side `−2πi (k/12 − ord_∞)`. The core theorem `pvChainIdentity` extracts `Σ gWN · ord = −(k/12 − ord_∞)` via `tendsto_nhds_unique` and cancellation of `2πi` (`pvChain_two_pi_I_ne_zero`). The wrappers `discharge_pvChain`, `discharge_pvChain_full`, and `discharge_pvChain_full_Hgt1` package this as the existential `∃ H' D, height bound ∧ identity` (the latter two pick the height `H = max(...)+1` and accept a `mkD` constructor with lower bounds `> √3/2` or `> 1`). The capstone theorems `valence_formula_of_pvChainData`, `valence_formula_of_two_sides`, and `valence_formula_of_two_sides_Hgt1` combine these with `valence_formula_orbit_sum_of_pvChain` to yield the textbook orbit-sum formula `ord_∞ + (1/2)ord_i + (1/3)ord_ρ + non-elliptic sums = k/12`. Auxiliary lemmas `eq_{,neg_}of_two_pi_I_mul_eq`, `exists_height_above_finset[_and_sqrt3]`, and `FDWindingDataFull.ofWindingData` provide reusable algebra/height/constructor utilities. No sorries; depends on `CoreIdentityProof` and Mathlib.
