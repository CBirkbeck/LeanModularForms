# OrbitPairing.lean Inventory

### `private lemma normSq_add_one_eq_of_re_neg_halfFM`
- **Type**: `(z : ℂ) (hre : z.re = −1/2) → Complex.normSq (z + 1) = Complex.normSq z`
- **What**: For `re z = −1/2`, the normSq is invariant under `z ↦ z + 1` (left vertical edge ↔ right vertical edge identification).
- **How**: Unfold `normSq_apply`, expand and ring.
- **Hypotheses**: `z.re = −1/2`.
- **Uses from project**: []
- **Used by**: `norm_add_one_eq_of_re_neg_halfFM`, `vAdd_one_mem_fd_of_left_vertFM`
- **Visibility**: private
- **Lines**: 34-37
- **Notes**: none

### `private lemma normSq_sub_one_eq_of_re_halfFM`
- **Type**: `(z : ℂ) (hre : z.re = 1/2) → Complex.normSq (z − 1) = Complex.normSq z`
- **What**: For `re z = 1/2`, the normSq is invariant under `z ↦ z − 1`.
- **How**: Unfold `normSq_apply`, expand and ring.
- **Hypotheses**: `z.re = 1/2`.
- **Uses from project**: []
- **Used by**: `norm_sub_one_eq_of_re_halfFM`, `vAdd_neg_one_mem_fd_of_right_vertFM`
- **Visibility**: private
- **Lines**: 39-42
- **Notes**: none

### `private lemma eq_of_sq_eq_of_nonnegFM`
- **Type**: `{a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^2 = b^2) → a = b`
- **What**: Equality of squares with both arguments nonnegative implies equality.
- **How**: `(a − b) * (a + b) = 0` (via `nlinarith`), case-split and `linarith`.
- **Hypotheses**: Both nonnegative; squares equal.
- **Uses from project**: []
- **Used by**: `norm_eq_of_normSq_eqFM`
- **Visibility**: private
- **Lines**: 44-47
- **Notes**: none

### `private lemma norm_eq_of_normSq_eqFM`
- **Type**: `{z w : ℂ} (h : Complex.normSq z = Complex.normSq w) → ‖z‖ = ‖w‖`
- **What**: Equal normSq implies equal norm.
- **How**: `norm_nonneg`, `normSq_eq_norm_sq`, and `eq_of_sq_eq_of_nonnegFM`.
- **Hypotheses**: `normSq` equal.
- **Uses from project**: [`eq_of_sq_eq_of_nonnegFM`]
- **Used by**: `norm_add_one_eq_of_re_neg_halfFM`, `norm_sub_one_eq_of_re_halfFM`
- **Visibility**: private
- **Lines**: 49-54
- **Notes**: none

### `private lemma one_le_normSq_of_norm_gt_oneFM`
- **Type**: `{z : ℂ} (h : ‖z‖ > 1) → 1 ≤ Complex.normSq z`
- **What**: `‖z‖ > 1 ⇒ 1 ≤ normSq z` (entry into FD-membership data).
- **How**: `nlinarith` after `normSq_eq_norm_sq`.
- **Hypotheses**: `‖z‖ > 1`.
- **Uses from project**: []
- **Used by**: `vAdd_one_leftVert_subset_rightVertFM`
- **Visibility**: private
- **Lines**: 56-59
- **Notes**: none

### `private lemma normSq_eq_one_of_norm_eq_oneFM`
- **Type**: `{z : ℂ} (h : ‖z‖ = 1) → Complex.normSq z = 1`
- **What**: Norm 1 implies normSq 1.
- **How**: `normSq_eq_norm_sq` then `norm_num`.
- **Hypotheses**: `‖z‖ = 1`.
- **Uses from project**: []
- **Used by**: `S_smul_re_neg_of_unitFM`, `S_smul_mem_fd_of_unitFM`
- **Visibility**: private
- **Lines**: 61-64
- **Notes**: none

### `lemma vAdd_one_coeFM`
- **Type**: `(p : ℍ) → ((1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) + 1`
- **What**: Coercion identity for T-translation by 1.
- **How**: `change ((1 : ℝ) : ℂ) + (p : ℂ) = (p : ℂ) + 1`, `push_cast`, `ring`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `vAdd_one_reFM`, `vAdd_one_im_eqFM`, `vAdd_one_norm_eq_of_re_neg_halfFM`, `vAdd_one_mem_fd_of_left_vertFM`, `vAdd_one_leftVert_subset_rightVertFM`, `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 69-72
- **Notes**: none

### `lemma vAdd_one_reFM`
- **Type**: `(p : ℍ) → ((1 : ℝ) +ᵥ p : ℍ).re = p.re + 1`
- **What**: T-translation shifts real part by 1.
- **How**: Unfold to `((1 : ℝ) +ᵥ p : ℂ).re`, use `vAdd_one_coeFM`, simp `add_re, one_re`, `rfl`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_one_coeFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 75-79
- **Notes**: none

### `lemma vAdd_one_im_eqFM`
- **Type**: `(p : ℍ) → ((1 : ℝ) +ᵥ p : ℍ).im = p.im`
- **What**: T-translation preserves imaginary part.
- **How**: Same pattern as `vAdd_one_reFM`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_one_coeFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 82-86
- **Notes**: none

### `lemma vAdd_neg_one_coeFM`
- **Type**: `(p : ℍ) → ((−1 : ℝ) +ᵥ p : ℂ) = (p : ℂ) − 1`
- **What**: Coercion identity for T⁻¹-translation by 1.
- **How**: `change`, `push_cast`, `ring`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `vAdd_neg_one_reFM`, `vAdd_neg_one_im_eqFM`, `vAdd_neg_one_norm_eq_of_re_halfFM`, `vAdd_neg_one_mem_fd_of_right_vertFM`, `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 89-92
- **Notes**: none

### `lemma vAdd_neg_one_reFM`
- **Type**: `(p : ℍ) → ((−1 : ℝ) +ᵥ p : ℍ).re = p.re − 1`
- **What**: T⁻¹-translation shifts real part by −1.
- **How**: Same pattern as `vAdd_one_reFM`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_neg_one_coeFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 95-99
- **Notes**: none

### `lemma vAdd_neg_one_im_eqFM`
- **Type**: `(p : ℍ) → ((−1 : ℝ) +ᵥ p : ℍ).im = p.im`
- **What**: T⁻¹-translation preserves imaginary part.
- **How**: Same pattern as `vAdd_one_im_eqFM`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_neg_one_coeFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 102-106
- **Notes**: none

### `lemma norm_add_one_eq_of_re_neg_halfFM`
- **Type**: `(z : ℂ) (hre : z.re = −1/2) → ‖z + 1‖ = ‖z‖`
- **What**: Norm preservation under `z ↦ z + 1` for `re = −1/2`.
- **How**: Apply `norm_eq_of_normSq_eqFM` to `normSq_add_one_eq_of_re_neg_halfFM`.
- **Hypotheses**: `re z = −1/2`.
- **Uses from project**: [`norm_eq_of_normSq_eqFM`, `normSq_add_one_eq_of_re_neg_halfFM`]
- **Used by**: `vAdd_one_norm_eq_of_re_neg_halfFM`
- **Visibility**: public
- **Lines**: 111-113
- **Notes**: none

### `lemma norm_sub_one_eq_of_re_halfFM`
- **Type**: `(z : ℂ) (hre : z.re = 1/2) → ‖z − 1‖ = ‖z‖`
- **What**: Norm preservation under `z ↦ z − 1` for `re = 1/2`.
- **How**: Apply `norm_eq_of_normSq_eqFM` to `normSq_sub_one_eq_of_re_halfFM`.
- **Hypotheses**: `re z = 1/2`.
- **Uses from project**: [`norm_eq_of_normSq_eqFM`, `normSq_sub_one_eq_of_re_halfFM`]
- **Used by**: `vAdd_neg_one_norm_eq_of_re_halfFM`
- **Visibility**: public
- **Lines**: 116-118
- **Notes**: none

### `lemma vAdd_one_norm_eq_of_re_neg_halfFM`
- **Type**: `(p : ℍ) (hre : (p : ℂ).re = −1/2) → ‖((1 : ℝ) +ᵥ p : ℂ)‖ = ‖(p : ℂ)‖`
- **What**: UHP-level norm preservation for left-vertical points under T-translation.
- **How**: Rewrite via `vAdd_one_coeFM`, apply `norm_add_one_eq_of_re_neg_halfFM`.
- **Hypotheses**: `re p = −1/2`.
- **Uses from project**: [`vAdd_one_coeFM`, `norm_add_one_eq_of_re_neg_halfFM`]
- **Used by**: `vAdd_one_leftVert_subset_rightVertFM`, `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 121-124
- **Notes**: none

### `lemma vAdd_neg_one_norm_eq_of_re_halfFM`
- **Type**: `(p : ℍ) (hre : (p : ℂ).re = 1/2) → ‖((−1 : ℝ) +ᵥ p : ℂ)‖ = ‖(p : ℂ)‖`
- **What**: UHP-level norm preservation for right-vertical points under T⁻¹-translation.
- **How**: Rewrite via `vAdd_neg_one_coeFM`, apply `norm_sub_one_eq_of_re_halfFM`.
- **Hypotheses**: `re p = 1/2`.
- **Uses from project**: [`vAdd_neg_one_coeFM`, `norm_sub_one_eq_of_re_halfFM`]
- **Used by**: `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 127-130
- **Notes**: none

### `theorem vAdd_one_mem_fd_of_left_vertFM`
- **Type**: `(p : ℍ) (hp_fd : p ∈ 𝒟) (hre : (p : ℂ).re = −1/2) → (1 : ℝ) +ᵥ p ∈ 𝒟`
- **What**: T-translation maps left-vertical FD points back into 𝒟 (their image is on the right-vertical edge).
- **How** (~10 lines): Use the FD normSq bound and re-bound; for normSq, `vAdd_one_coeFM` + `normSq_add_one_eq_of_re_neg_halfFM`; for `|re|`, push `vAdd_one_coeFM` + `hre`, `norm_num`.
- **Hypotheses**: `p ∈ 𝒟`, `re p = −1/2`.
- **Uses from project**: [`vAdd_one_coeFM`, `normSq_add_one_eq_of_re_neg_halfFM`]
- **Used by**: `ellipticPointRhoPlusOne_mem_fdFM`, `vAdd_one_leftVert_subset_rightVertFM`, `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 135-144
- **Notes**: none

### `theorem vAdd_neg_one_mem_fd_of_right_vertFM`
- **Type**: `(p : ℍ) (hp_fd : p ∈ 𝒟) (hre : (p : ℂ).re = 1/2) → (−1 : ℝ) +ᵥ p ∈ 𝒟`
- **What**: T⁻¹-translation maps right-vertical FD points back into 𝒟.
- **How** (~10 lines): Mirror of `vAdd_one_mem_fd_of_left_vertFM`.
- **Hypotheses**: `p ∈ 𝒟`, `re p = 1/2`.
- **Uses from project**: [`vAdd_neg_one_coeFM`, `normSq_sub_one_eq_of_re_halfFM`]
- **Used by**: `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 147-156
- **Notes**: none

### `theorem vAdd_one_rho_eq_rho_plus_oneFM`
- **Type**: `(1 : ℝ) +ᵥ ellipticPointRho' = ellipticPointRhoPlusOne'`
- **What**: T-translation of `ρ` equals `ρ + 1` as UHP elements.
- **How**: `UpperHalfPlane.ext` reduces to `ℂ`; then `vAdd_one_coeFM` and `ellipticPointRho_add_one_eq`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_one_coeFM`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointRho_add_one_eq`]
- **Used by**: `vAdd_neg_one_rho_plus_one_eq_rhoFM`, `ellipticPointRhoPlusOne_mem_fdFM`, `ord_rho_plus_one_eq_ord_rho_via_vAddFM`
- **Visibility**: public
- **Lines**: 161-165
- **Notes**: none

### `theorem vAdd_neg_one_rho_plus_one_eq_rhoFM`
- **Type**: `(−1 : ℝ) +ᵥ ellipticPointRhoPlusOne' = ellipticPointRho'`
- **What**: T⁻¹-translation of `ρ + 1` equals `ρ`.
- **How**: `UpperHalfPlane.ext`, `vAdd_neg_one_coeFM`, `sub_eq_iff_eq_add`, `ellipticPointRho_add_one_eq.symm`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_neg_one_coeFM`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointRho_add_one_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 168-172
- **Notes**: none

### `theorem ellipticPointRhoPlusOne_mem_fdFM`
- **Type**: `ellipticPointRhoPlusOne' ∈ 𝒟`
- **What**: `ρ + 1` is in the standard fundamental domain.
- **How**: Apply `vAdd_one_mem_fd_of_left_vertFM` to `ρ` (which is on the left vertical edge with `re = −1/2`), then rewrite to `ρ + 1` via `vAdd_one_rho_eq_rho_plus_oneFM`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_one_rho_eq_rho_plus_oneFM`, `vAdd_one_mem_fd_of_left_vertFM`, `ellipticPointRho'`, `ellipticPointRho_mem_fd`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 175-179
- **Notes**: none

### `theorem ord_rho_plus_one_eq_ord_rho_via_vAddFM`
- **Type**: `(f : ModularForm (Gamma 1) k) → orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne' = orderOfVanishingAt' (⇑f) ellipticPointRho'`
- **What**: T-invariance: `ord(f, ρ+1) = ord(f, ρ)` via the UHP-level T-translation lemma.
- **How**: Rewrite `ρ + 1 = 1 +ᵥ ρ` (via `vAdd_one_rho_eq_rho_plus_oneFM`), then apply `ord_add_one_eq`.
- **Hypotheses**: None.
- **Uses from project**: [`vAdd_one_rho_eq_rho_plus_oneFM`, `ord_add_one_eq`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 186-190
- **Notes**: none

### `lemma S_smul_coeFM`
- **Type**: `(p : ℍ) → ((ModularGroup.S • p : ℍ) : ℂ) = (−(p : ℂ))⁻¹`
- **What**: Coercion identity for the S-action: `S • p = (−p)⁻¹` in `ℂ`.
- **How**: `UpperHalfPlane.modular_S_smul`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `S_smul_norm_of_unitFM`, `S_smul_re_neg_of_unitFM`, `S_smul_mem_fd_of_unitFM`
- **Visibility**: public
- **Lines**: 195-196
- **Notes**: none

### `theorem S_smul_norm_of_unitFM`
- **Type**: `(p : ℍ) (hp : ‖(p : ℂ)‖ = 1) → ‖((ModularGroup.S • p : ℍ) : ℂ)‖ = 1`
- **What**: S-action preserves norm on the unit circle.
- **How**: `S_smul_coeFM`, `norm_inv`, `norm_neg`, hypothesis, `inv_one`.
- **Hypotheses**: `‖p‖ = 1`.
- **Uses from project**: [`S_smul_coeFM`]
- **Used by**: `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: public
- **Lines**: 199-201
- **Notes**: none

### `theorem S_smul_re_neg_of_unitFM`
- **Type**: `(p : ℍ) (hp : ‖(p : ℂ)‖ = 1) → (ModularGroup.S • p : ℍ).re = −p.re`
- **What**: On the unit circle, the S-action negates the real part.
- **How** (~7 lines): `S_smul_coeFM`, `Complex.inv_re`, `Complex.neg_re`, `Complex.normSq_neg`, use `normSq_eq_one_of_norm_eq_oneFM` to set `normSq = 1`, `div_one`, `rfl`.
- **Hypotheses**: `‖p‖ = 1`.
- **Uses from project**: [`normSq_eq_one_of_norm_eq_oneFM`, `S_smul_coeFM`]
- **Used by**: `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: public
- **Lines**: 204-210
- **Notes**: none

### `theorem S_smul_mem_fd_of_unitFM`
- **Type**: `(p : ℍ) (hp_fd : p ∈ 𝒟) (hp_norm : ‖(p : ℂ)‖ = 1) → ModularGroup.S • p ∈ 𝒟`
- **What**: S-action preserves FD-membership for unit-circle points.
- **How** (~10 lines): For normSq bound, simp `S_smul_coeFM`, `map_inv₀`, `Complex.normSq_neg`, `normSq_eq_one_of_norm_eq_oneFM`, `inv_one`. For `|re|`, use S-action formula and `abs_neg`, fall back to the FD hypothesis on `|p.re|`.
- **Hypotheses**: `p ∈ 𝒟`, `‖p‖ = 1`.
- **Uses from project**: [`S_smul_coeFM`, `normSq_eq_one_of_norm_eq_oneFM`]
- **Used by**: `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: public
- **Lines**: 213-223
- **Notes**: none

### `private lemma S_mul_SFM`
- **Type**: `ModularGroup.S * ModularGroup.S = −1`
- **What**: `S² = −1` in SL₂(ℤ).
- **How**: `ext i j; fin_cases i <;> fin_cases j <;> simp [ModularGroup.S] <;> decide`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `S_smul_S_smulFM`
- **Visibility**: private
- **Lines**: 227-229
- **Notes**: none

### `lemma S_smul_S_smulFM`
- **Type**: `(p : ℍ) → ModularGroup.S • (ModularGroup.S • p) = p`
- **What**: S² acts as identity on ℍ.
- **How**: `mul_smul`, `S_mul_SFM`, `SL_neg_smul`, `one_smul`.
- **Hypotheses**: None.
- **Uses from project**: [`S_mul_SFM`]
- **Used by**: `S_smul_injectiveFM`, `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: public
- **Lines**: 232-233
- **Notes**: none

### `lemma S_smul_injectiveFM`
- **Type**: `Function.Injective (ModularGroup.S • · : ℍ → ℍ)`
- **What**: The S-action on ℍ is injective.
- **How**: `Function.HasLeftInverse.injective` with witness `S_smul_S_smulFM`.
- **Hypotheses**: None.
- **Uses from project**: [`S_smul_S_smulFM`]
- **Used by**: `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: public
- **Lines**: 236-237
- **Notes**: none

### `lemma orb_vAdd_neg_one_eq`
- **Type**: `(p : ℍ) → orbFM ((−1 : ℝ) +ᵥ p) = orbFM p`
- **What**: T⁻¹-translation preserves orbits.
- **How** (~10 lines): Witness `(−1 : ℝ) +ᵥ p = ModularGroup.T⁻¹ • p` via `smul_inv_smul` + `UpperHalfPlane.modular_T_smul`; conclude with `Quotient.eq''`, `MulAction.orbitRel_apply`, `MulAction.mem_orbit_iff`.
- **Hypotheses**: None.
- **Uses from project**: [`orbFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 242-253
- **Notes**: none

### `lemma orb_vAdd_one_eq`
- **Type**: `(p : ℍ) → orbFM ((1 : ℝ) +ᵥ p) = orbFM p`
- **What**: T-translation preserves orbits.
- **How**: Same as above with `ModularGroup.T`.
- **Hypotheses**: None.
- **Uses from project**: [`orbFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 256-260
- **Notes**: none

### `lemma orb_S_smul_eq`
- **Type**: `(p : ℍ) → orbFM (ModularGroup.S • p) = orbFM p`
- **What**: S-action preserves orbits.
- **How**: `Quotient.eq''`, `MulAction.orbitRel_apply`, witness `S`.
- **Hypotheses**: None.
- **Uses from project**: [`orbFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 263-267
- **Notes**: none

### `def sLeftVertFM`
- **Type**: `(S : Finset ℍ) → Finset ℍ`
- **What**: Points of `S` on the left vertical edge: `re = −1/2 ∧ ‖p‖ > 1`.
- **How**: `Finset.filter`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `vAdd_one_leftVert_subset_rightVertFM`, `sum_ord_leftVert_eq_sum_T_imageFM`, `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 272-273
- **Notes**: none

### `def sRightVertFM`
- **Type**: `(S : Finset ℍ) → Finset ℍ`
- **What**: Points of `S` on the right vertical edge: `re = 1/2 ∧ ‖p‖ > 1`.
- **How**: `Finset.filter`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `vAdd_one_leftVert_subset_rightVertFM`, `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 276-277
- **Notes**: none

### `def sLeftArcFM`
- **Type**: `(S : Finset ℍ) → Finset ℍ`
- **What**: Points of `S` on the unit-circle arc with `re < 0`.
- **How**: `Finset.filter`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: public
- **Lines**: 280-281
- **Notes**: none

### `def sRightArcFM`
- **Type**: `(S : Finset ℍ) → Finset ℍ`
- **What**: Points of `S` on the unit-circle arc with `re > 0`.
- **How**: `Finset.filter`.
- **Hypotheses**: None.
- **Uses from project**: []
- **Used by**: `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: public
- **Lines**: 284-285
- **Notes**: none

### `lemma ord_vAdd_neg_one_eqFM`
- **Type**: `(f : ModularForm (Gamma 1) k) (p : ℍ) → orderOfVanishingAt' (⇑f) ((−1 : ℝ) +ᵥ p) = orderOfVanishingAt' (⇑f) p`
- **What**: T⁻¹-invariance of vanishing order.
- **How**: Apply `ord_add_one_eq` at `(−1 : ℝ) +ᵥ p` and simplify `1 +ᵥ ((−1) +ᵥ p) = p` by `ext + push_cast + ring`, then `.symm`.
- **Hypotheses**: None.
- **Uses from project**: [`ord_add_one_eq`]
- **Used by**: `sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Visibility**: public
- **Lines**: 290-298
- **Notes**: none

### `private lemma ord_ne_zero_of_cast_ne_zeroFM`
- **Type**: `{p : ℍ} {g : ℍ → ℂ} (h : (orderOfVanishingAt' g p : ℂ) ≠ 0) → orderOfVanishingAt' g p ≠ 0`
- **What**: Cast-version `≠ 0` reflects to the integer `≠ 0`.
- **How**: `exact_mod_cast h`.
- **Hypotheses**: Cast nonzero.
- **Uses from project**: []
- **Used by**: `sum_ord_rightVert_eq_sum_ord_leftVertFM`, `sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Visibility**: private
- **Lines**: 302-304
- **Notes**: none

### `theorem vAdd_one_leftVert_subset_rightVertFM`
- **Type**: `(S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) → ∀ p ∈ sLeftVertFM S, orderOfVanishingAt' (⇑f) p ≠ 0 → (1 : ℝ) +ᵥ p ∈ sRightVertFM S`
- **What**: Under FD-completeness, T-translation maps left-vertical singular points to right-vertical singular points.
- **How** (~20 lines): Extract `(hre, hnorm)` from the filter; build `p ∈ 𝒟` via `one_le_normSq_of_norm_gt_oneFM` plus `|re|`-bound; then `vAdd_one_mem_fd_of_left_vertFM` and `ord_add_one_eq` give the image FD-data; finally `vAdd_one_coeFM`, `vAdd_one_norm_eq_of_re_neg_halfFM` close the filter.
- **Hypotheses**: FD-completeness of `S`.
- **Uses from project**: [`sLeftVertFM`, `sRightVertFM`, `vAdd_one_coeFM`, `one_le_normSq_of_norm_gt_oneFM`, `vAdd_one_mem_fd_of_left_vertFM`, `vAdd_one_norm_eq_of_re_neg_halfFM`, `ord_add_one_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 307-329
- **Notes**: none

### `theorem sum_ord_leftVert_eq_sum_T_imageFM`
- **Type**: `(S : Finset ℍ) → ∑ p ∈ sLeftVertFM S, (ord' f p : ℂ) = ∑ p ∈ sLeftVertFM S, (ord' f ((1 : ℝ) +ᵥ p) : ℂ)`
- **What**: Reindexing identity: orders at left-vertical points equal orders at their T-translates (pointwise via T-invariance).
- **How**: `Finset.sum_congr rfl` + `ord_add_one_eq`.
- **Hypotheses**: None.
- **Uses from project**: [`sLeftVertFM`, `ord_add_one_eq`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 332-335
- **Notes**: none

### `theorem sum_ord_rightVert_eq_sum_ord_leftVertFM`
- **Type**: `(S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) → ∑ p ∈ sRightVertFM S, (ord' f p : ℂ) = ∑ p ∈ sLeftVertFM S, (ord' f p : ℂ)`
- **What**: Sum of vanishing orders over the right vertical edge equals the sum over the left vertical edge.
- **How** (~45 lines): Reduce to filtered nonzero terms (`Finset.sum_filter_ne_zero`), then bijection by `(−1 : ℝ) +ᵥ ·` via `Finset.sum_nbij`. Forward map uses `vAdd_neg_one_mem_fd_of_right_vertFM`, `ord_vAdd_neg_one_eqFM`, `vAdd_neg_one_coeFM`, `vAdd_neg_one_norm_eq_of_re_halfFM`. Injectivity by cancelling `1 +ᵥ ((−1) +ᵥ ·)`. Surjective inverse `(1 : ℝ) +ᵥ ·` parallels using `vAdd_one_mem_fd_of_left_vertFM`, `ord_add_one_eq`, `vAdd_one_coeFM`, `vAdd_one_norm_eq_of_re_neg_halfFM`. Sum equality from `ord_vAdd_neg_one_eqFM`.
- **Hypotheses**: All of `S` in `𝒟`; FD-completeness of `S` for the order non-vanishing predicate.
- **Uses from project**: [`sLeftVertFM`, `sRightVertFM`, `vAdd_neg_one_mem_fd_of_right_vertFM`, `vAdd_one_mem_fd_of_left_vertFM`, `vAdd_one_coeFM`, `vAdd_neg_one_coeFM`, `vAdd_one_norm_eq_of_re_neg_halfFM`, `vAdd_neg_one_norm_eq_of_re_halfFM`, `ord_add_one_eq`, `ord_vAdd_neg_one_eqFM`, `ord_ne_zero_of_cast_ne_zeroFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 338-384
- **Notes**: > 30 lines

### `theorem sum_ord_rightArc_eq_sum_ord_leftArcFM`
- **Type**: `(S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) → ∑ p ∈ sRightArcFM S, (ord' f p : ℂ) = ∑ p ∈ sLeftArcFM S, (ord' f p : ℂ)`
- **What**: Sum of vanishing orders over the right arc equals the sum over the left arc.
- **How** (~35 lines): Same pattern as `sum_ord_rightVert_eq_sum_ord_leftVertFM` but with the S-action: forward uses `S_smul_mem_fd_of_unitFM`, `ord_S_eq`, `S_smul_norm_of_unitFM`, `S_smul_re_neg_of_unitFM`; injectivity via `S_smul_injectiveFM`; surjectivity via `S_smul_S_smulFM`; sum equality via `ord_S_eq`.
- **Hypotheses**: All of `S` in `𝒟`; FD-completeness.
- **Uses from project**: [`sLeftArcFM`, `sRightArcFM`, `S_smul_mem_fd_of_unitFM`, `S_smul_norm_of_unitFM`, `S_smul_re_neg_of_unitFM`, `S_smul_injectiveFM`, `S_smul_S_smulFM`, `ord_S_eq`, `ord_ne_zero_of_cast_ne_zeroFM`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 389-423
- **Notes**: > 30 lines

## File Summary

Pure-algebra orbit-pairing lemmas for the valence formula: T-translation and T⁻¹-translation move singular points between left and right vertical edges of the fundamental domain (`vAdd_one_mem_fd_of_left_vertFM`, `vAdd_neg_one_mem_fd_of_right_vertFM`), and the S-action swaps left/right arcs (`S_smul_mem_fd_of_unitFM`). The vertical edge pairing (`sum_ord_rightVert_eq_sum_ord_leftVertFM`) and arc pairing (`sum_ord_rightArc_eq_sum_ord_leftArcFM`) use `Finset.sum_nbij` to identify singular contributions on opposite boundary components, with orbit identities (`orb_vAdd_one_eq`, `orb_vAdd_neg_one_eq`, `orb_S_smul_eq`) supporting orbit-level reasoning. The S-involution data (`S_smul_S_smulFM`, `S_smul_injectiveFM`) and `S_mul_SFM = −1` underwrite the arc bijection.
