# ResidueSideProof.lean — Inventory

### `private lemma two_pi_I_ne_zero_rs`
- **Type**: `(2 : ℂ) * ↑Real.pi * I ≠ 0`
- **What**: The complex number `2πi` is nonzero.
- **How**: `simp only` decomposing product into nonzero factors (2, π, i).
- **Hypotheses**: none
- **Uses from project**: []
- **Used by**: `cancel_two_pi_I_sum`
- **Visibility**: private
- **Lines**: 84-87
- **Notes**: `omit f hf in`

### `structure ResidueSideData`
- **Type**: `{H : ℝ} (D : FDWindingDataFull H) (S : Finset UpperHalfPlane) : Type`
- **What**: Bundles the analytical ingredients at height `H`: a singular set `S_sing`, a patched function `F` agreeing with `logDeriv(f ∘ ofComplex)` off `S_sing`, a `HasCauchyPVOn` certificate, and a residue-to-order conversion identity for the winding-weighted residue sum.
- **How**: `structure` with five fields: `S_sing`, `F`, `F_eq_logDeriv`, `h_cpv`, `sum_convert`.
- **Hypotheses**: `D : FDWindingDataFull H`, `S : Finset UpperHalfPlane`
- **Uses from project**: `FDWindingDataFull`, `logDeriv`, `UpperHalfPlane.ofComplex`, `HasCauchyPVOn`, `generalizedWindingNumber`, `orderOfVanishingAt'`
- **Used by**: `residueSide_tendsto_of_data`, `residueSide_for_discharge`
- **Visibility**: public
- **Lines**: 104-126
- **Notes**: none

### `theorem residueSide_tendsto_of_data`
- **Type**: `{H : ℝ} {D : FDWindingDataFull H} {S : Finset UpperHalfPlane} (data : ResidueSideData f S (D := D)) : Tendsto (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrandOn data.S_sing data.F D.boundary.toPath.extend ε t) (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber D.boundary (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ)))`
- **What**: Extracts a `Tendsto` statement from a `ResidueSideData`: the ε-truncated CPV integral converges to `2πi · Σ gWN · ord`.
- **How**: Rewrite the target using `data.sum_convert` then close with `data.h_cpv` (which is `HasCauchyPVOn`).
- **Hypotheses**: `f : ModularForm (Gamma 1) k`; `data : ResidueSideData f S`
- **Uses from project**: `ResidueSideData`, `FDWindingDataFull`, `cpvIntegrandOn`, `generalizedWindingNumber`, `orderOfVanishingAt'`
- **Used by**: `residueSide_for_discharge`
- **Visibility**: public
- **Lines**: 134-146
- **Notes**: none

### `theorem residueSide_sum_convert_of_residue_eq_order`
- **Type**: `{γ : PiecewiseC1Path (fdStart H) (fdStart H)} {S : Finset UpperHalfPlane} {S_sing : Finset ℂ} {F : ℂ → ℂ} (h_res_eq : ∀ s ∈ S, residue F (↑s : ℂ) = ↑(orderOfVanishingAt' (⇑f) s)) (h_non_S_zero : ∀ s ∈ S_sing, s ∉ S.image (↑·) → generalizedWindingNumber γ s * residue F s = 0) (h_S_sub : S.image (↑·) ⊆ S_sing) (h_inj : ∀ p₁ ∈ S, ∀ p₂ ∈ S, (↑p₁ : ℂ) = (↑p₂ : ℂ) → p₁ = p₂) : ∑ s ∈ S_sing, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * residue F s = 2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber γ (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ)`
- **What**: Converts the winding-weighted residue sum over `S_sing` (complex points) into a winding-weighted order sum over `S` (upper half-plane points).
- **How**: Three steps: `Finset.sum_subset` restricts to `S.image` (using `h_non_S_zero`); `Finset.sum_image` rewrites the image sum using `h_inj`; `Finset.mul_sum` factors out `2πi` then `h_res_eq` and `ring` match each term. 22-line proof; key lemmas `Finset.sum_subset`, `Finset.sum_image`, `Finset.mul_sum`.
- **Hypotheses**: residue equals order on `S`; winding × residue vanishes off `S.image`; `S.image ⊆ S_sing`; coercion injective on `S`
- **Uses from project**: `fdStart`, `PiecewiseC1Path`, `generalizedWindingNumber`, `orderOfVanishingAt'`
- **Used by**: unused in file (offered for downstream use)
- **Visibility**: public
- **Lines**: 158-200
- **Notes**: none

### `theorem residueSide_for_discharge`
- **Type**: `(S : Finset UpperHalfPlane) (_hS : ∀ p ∈ S, p ∈ 𝒟) (_hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) (mkD : ∀ H, √3/2 < H → FDWindingDataFull H) (F_int : ℝ → ℝ → ℂ) (H_res : ℝ) (_hH_res_gt : √3/2 < H_res) (mk_data : ∀ H, H_res ≤ H → (hH : √3/2 < H) → ResidueSideData f S (D := mkD H hH)) (h_F_eq : ∀ H (hH_ge : H_res ≤ H) (hH : √3/2 < H), (fun ε => ∫ t in 0..1, cpvIntegrandOn (mk_data H hH_ge hH).S_sing (mk_data H hH_ge hH).F (mkD H hH).boundary.toPath.extend ε t) =ᶠ[𝓝[>] 0] F_int H) : ∀ H, H_res ≤ H → (hH : √3/2 < H) → Tendsto (F_int H) (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * ∑ s ∈ S, ...))`
- **What**: Bridges a per-height `ResidueSideData` and an eventual-equality of the CPV integral to a common integrand, producing the `h_res` parameter for `discharge_pvChain_full`.
- **How**: For each `H`, invoke `residueSide_tendsto_of_data` then transport along `h_F_eq` via `Tendsto.congr'`.
- **Hypotheses**: `f`; `S ⊆ 𝒟`; completeness of `S`; height-parameterized winding data; common integrand match
- **Uses from project**: `𝒟`, `orderOfVanishingAt'`, `FDWindingDataFull`, `ResidueSideData`, `cpvIntegrandOn`, `residueSide_tendsto_of_data`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 214-239
- **Notes**: none

### `theorem residueSide_direct`
- **Type**: `(S : Finset UpperHalfPlane) (_hS : ∀ p ∈ S, p ∈ 𝒟) (_hS_complete : ...) (mkD : ∀ H, √3/2 < H → FDWindingDataFull H) (F_int : ℝ → ℝ → ℂ) (H_res : ℝ) (_hH_res_gt : √3/2 < H_res) (h_res : ∀ H, H_res ≤ H → (hH : √3/2 < H) → Tendsto (F_int H) (𝓝[>] 0) (𝓝 (...))) : ∀ H, H_res ≤ H → (hH : √3/2 < H) → Tendsto (F_int H) (𝓝[>] 0) (𝓝 (...))`
- **What**: A pass-through identity: if you already have the residue-side `Tendsto`, this packages it in the exact form `discharge_pvChain_full` expects.
- **How**: `:= h_res` — definitional.
- **Hypotheses**: `f`; `S ⊆ 𝒟`; completeness of `S`; the prepared `Tendsto`
- **Uses from project**: `𝒟`, `orderOfVanishingAt'`, `FDWindingDataFull`, `generalizedWindingNumber`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 251-269
- **Notes**: none

### `theorem valence_formula_of_residueSideData`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ...) (mkD : ∀ H, √3/2 < H → FDWindingDataFull H) (F_int : ℝ → ℝ → ℂ) (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S) (H_res : ℝ) (hH_res_gt : √3/2 < H_res) (h_res : ...) (H_mod : ℝ) (hH_mod_gt : √3/2 < H_mod) (h_mod : ...) : ∃ H' : ℝ, ∃ D : FDWindingDataFull H', (∀ s ∈ S, (s : ℂ).im < H') ∧ ∑ s ∈ S, generalizedWindingNumber D.boundary (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ) = -((k : ℂ) / 12 - (orderAtCusp' f : ℂ))`
- **What**: Combines residue and modular Tendsto sides via `discharge_pvChain_full` to produce the orbit-sum identity equating `Σ gWN · ord` with `-(k/12 - ord_∞)`.
- **How**: Direct delegation `:= discharge_pvChain_full f S hS hS_complete mkD H_S hH_S F_int H_res hH_res_gt h_res H_mod hH_mod_gt h_mod`.
- **Hypotheses**: `f`; completeness of `S`; common integrand at heights above `√3/2`; residue-side Tendsto; modular-side Tendsto
- **Uses from project**: `discharge_pvChain_full`, `𝒟`, `orderOfVanishingAt'`, `FDWindingDataFull`, `generalizedWindingNumber`, `orderAtCusp'`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 280-308
- **Notes**: none

### `theorem logDeriv_residue_eq_orderOfVanishing`
- **Type**: `(p : UpperHalfPlane) (hMero : MeromorphicAt (⇑f ∘ UpperHalfPlane.ofComplex) (↑p : ℂ)) (hord : meromorphicOrderAt (⇑f ∘ UpperHalfPlane.ofComplex) (↑p : ℂ) ≠ ⊤) : residue (logDeriv (⇑f ∘ UpperHalfPlane.ofComplex)) (↑p : ℂ) = ↑(meromorphicOrderAt (⇑f ∘ UpperHalfPlane.ofComplex) (↑p : ℂ)).untop₀`
- **What**: At a meromorphic point of `f`, the residue of `logDeriv(f ∘ ofComplex)` equals the order of vanishing.
- **How**: Direct delegation to `logDeriv_residue_eq_order`.
- **Hypotheses**: `f`; meromorphicity of `f ∘ ofComplex` at `↑p`; nonzero order
- **Uses from project**: `logDeriv_residue_eq_order`, `UpperHalfPlane.ofComplex`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 320-326
- **Notes**: none

### `theorem exists_height_above_S_and_sqrt3`
- **Type**: `(S : Finset UpperHalfPlane) : ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ s ∈ S, (s : ℂ).im < H₀`
- **What**: For any finite set of upper-half-plane points, some height `H₀` exceeds both `√3/2` and every imaginary part.
- **How**: Empty/nonempty split; for nonempty, pick `max (√3/2) (sup' im S) + 1` and apply `Finset.le_sup'`. Lemma `Real.sq_sqrt` bounds `√3/2 < 1`.
- **Hypotheses**: none (`omit f hf in`)
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 333-344
- **Notes**: `omit f hf in`

### `theorem residueSide_of_avoidance_case`
- **Type**: `{x₀ : ℂ} {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty) (S_sing : Finset ℂ) (hS_in_U : ↑S_sing ⊆ U) (F : ℂ → ℂ) (hF_diff : DifferentiableOn ℂ F (U \ ↑S_sing)) (γ : PiecewiseC1Path x₀ x₀) (hSimplePoles : ∀ s ∈ S_sing, HasSimplePoleAt F s) (hγ_in_U : ∀ t ∈ Icc 0 1, γ t ∈ U) (hγ_avoids : ∀ s ∈ S_sing, ∀ t ∈ Icc 0 1, γ t ≠ s) (hδ : ...) (h_rem_int : ...) (h_pp_int : ...) (hI : ...) : HasCauchyPVOn S_sing F γ (∑ s ∈ S_sing, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * residue F s)`
- **What**: In the avoidance case (γ avoids `S_sing`), the generalized residue theorem on a convex domain delivers the CPV with the winding-weighted residue sum as limit.
- **How**: Direct delegation to `hasCauchyPVOn_simplePoles_convex_auto`.
- **Hypotheses**: `f`; convex open nonempty `U` containing `S_sing` and γ; differentiability off `S_sing`; simple poles; avoidance with δ-bound; integrability of remainder and principal-part and individual fibers
- **Uses from project**: `hasCauchyPVOn_simplePoles_convex_auto`, `PiecewiseC1Path`, `HasSimplePoleAt`, `principalPartSum`, `HasCauchyPVOn`, `generalizedWindingNumber`, `residue`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 356-380
- **Notes**: none

### `theorem factor_two_pi_I_from_sum`
- **Type**: `{γ : PiecewiseC1Path x₀ x₀} {S : Finset ℂ} {c : ℂ → ℂ} : ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c s = 2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber γ s * c s`
- **What**: Algebraic identity: factor `2πi` out of a winding-weighted finite sum.
- **How**: `Finset.mul_sum` plus `Finset.sum_congr rfl; ring`.
- **Hypotheses**: none (`omit f hf in`)
- **Uses from project**: `PiecewiseC1Path`, `generalizedWindingNumber`
- **Used by**: `cancel_two_pi_I_sum`
- **Visibility**: public
- **Lines**: 388-395
- **Notes**: `omit f hf in`

### `theorem cancel_two_pi_I_sum`
- **Type**: `{γ : PiecewiseC1Path x₀ x₀} {S : Finset ℂ} {c₁ c₂ : ℂ → ℂ} (h : ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c₁ s = ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c₂ s) : ∑ s ∈ S, generalizedWindingNumber γ s * c₁ s = ∑ s ∈ S, generalizedWindingNumber γ s * c₂ s`
- **What**: Cancel the prefactor `2πi` from equal winding-weighted sums.
- **How**: Apply `factor_two_pi_I_from_sum` on both sides of `h`, then `mul_left_cancel₀ two_pi_I_ne_zero_rs`.
- **Hypotheses**: `omit f hf`; the equality `h` after `2πi` factor
- **Uses from project**: `factor_two_pi_I_from_sum`, `two_pi_I_ne_zero_rs`, `PiecewiseC1Path`, `generalizedWindingNumber`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 399-406
- **Notes**: `omit f hf in`

### `theorem valence_formula_of_two_tendsto_sides`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ...) (mkD : ∀ H, √3/2 < H → FDWindingDataFull H) (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S) (F_int : ℝ → ℝ → ℂ) (H_res : ℝ) (hH_res_gt : √3/2 < H_res) (h_res : ...) (H_mod : ℝ) (hH_mod_gt : √3/2 < H_mod) (h_mod : ...) : (orderAtCusp' f : ℂ) + (1/2) * ↑(ord f ellipticPointI') + (1/3) * ↑(ord f ellipticPointRho') + ∑ s ∈ S.filter (strict interior pred), ↑(ord f s) + ∑ s ∈ sLeftVertFM S, ↑(ord f s) + ∑ s ∈ S.filter (left-arc pred), ↑(ord f s) = (k : ℂ) / 12`
- **What**: The textbook valence formula: weighted sum of orders (cusp + i × 1/2 + ρ × 1/3 + interior + left vertical + left arc) equals `k/12`.
- **How**: Direct delegation to `valence_formula_of_two_sides`.
- **Hypotheses**: `omit hf`; same as `valence_formula_of_residueSideData` (residue-side and modular-side Tendsto at heights above `√3/2`); completeness of `S`
- **Uses from project**: `valence_formula_of_two_sides`, `𝒟`, `orderOfVanishingAt'`, `orderAtCusp'`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `sLeftVertFM`, `FDWindingDataFull`, `generalizedWindingNumber`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 419-452
- **Notes**: `omit hf in`; 31-line signature

## File Summary

- **Total declarations**: 13 (1 structure, 1 private lemma, 11 theorems)
- **Purpose**: Public residue-side API for the valence-formula PV chain — bundles `HasCauchyPVOn` for `logDeriv(f)` at FD-boundary height `H` and converts winding-weighted residue sums to winding-weighted order sums.
- **Imports used**: `PVChainProof` (`discharge_pvChain_full`, `valence_formula_of_two_sides`), `HigherOrderAssembly` (`hasCauchyPVOn_simplePoles_convex_auto`, `HasCauchyPVOn`, `cpvIntegrandOn`, `principalPartSum`, `residue`, `HasSimplePoleAt`), `LogDerivModularForm` (`logDeriv_residue_eq_order`)
- **External dependencies**: `FDWindingDataFull`, `fdStart`, `𝒟`, `ellipticPointI'/Rho'/RhoPlusOne'`, `sLeftVertFM`, `UpperHalfPlane`
- **No sorries, no axioms, no `set_option`**.
- **Architecture**: Layer 1 (`ResidueSideData`) → Layer 2 (`residueSide_sum_convert_of_residue_eq_order`) → Layer 3 bridges (`residueSide_for_discharge`, `residueSide_direct`, `valence_formula_of_residueSideData`, `valence_formula_of_two_tendsto_sides`).
