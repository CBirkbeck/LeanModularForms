# Inventory: ValenceFormula.lean

### `def ordOrbitQ`
- **Type**: `(q : NonEllOrbitFM) → ℂ`
- **What**: The order of vanishing on a non-elliptic orbit, cast to `ℂ`.
- **How**: Definitional — `(ordOrbitFM f q.val : ℂ)`.
- **Hypotheses**: Implicit `f : ModularForm (Gamma 1) k`, `hf : f ≠ 0` in scope.
- **Uses from project**: `NonEllOrbitFM`, `ordOrbitFM`
- **Used by**: `finsum_nonell_eq_repCanon_sum`, `valence_formula_textbook_orbit_finsum`
- **Visibility**: public
- **Lines**: 39-40
- **Notes**: noncomputable section

### `lemma ellipticPointI'_coe`
- **Type**: `(ellipticPointI' : ℂ) = Complex.I`
- **What**: The canonical representative of orbit `i` coerces to `Complex.I`.
- **How**: `rfl`.
- **Hypotheses**: none
- **Uses from project**: `ellipticPointI'`
- **Used by**: `normSq_denom_eq_one_of_smul_i_in_fd`, `re_smul_ellipticPointI`, `fd_orbit_i_eq_i`
- **Visibility**: private
- **Lines**: 44
- **Notes**: none

### `lemma ellipticPointI'_im`
- **Type**: `(ellipticPointI' : ℍ).im = 1`
- **What**: The imaginary part of the canonical representative `i`.
- **How**: `Complex.I_im`.
- **Hypotheses**: none
- **Uses from project**: `ellipticPointI'`
- **Used by**: `normSq_denom_eq_one_of_smul_i_in_fd`, `fd_orbit_i_eq_i`
- **Visibility**: private
- **Lines**: 45
- **Notes**: none

### `lemma ellipticPointRho'_re`
- **Type**: `(ellipticPointRho' : ℍ).re = -1/2`
- **What**: Real part of `ρ = -1/2 + i√3/2`.
- **How**: `change` to complex form, then `simp` and `norm_num`.
- **Hypotheses**: none
- **Uses from project**: `ellipticPointRho'`
- **Used by**: `fd_orbit_rho_eq`
- **Visibility**: private
- **Lines**: 47-50
- **Notes**: none

### `lemma ellipticPointRho'_im`
- **Type**: `(ellipticPointRho' : ℍ).im = Real.sqrt 3 / 2`
- **What**: Imaginary part of ρ.
- **How**: `change` to complex form, then `simp`.
- **Hypotheses**: none
- **Uses from project**: `ellipticPointRho'`
- **Used by**: `normSq_denom_eq_one_of_smul_rho_in_fd`, `abs_re_eq_half_of_smul_rho_in_fd`, `fd_orbit_rho_eq`
- **Visibility**: private
- **Lines**: 52-56
- **Notes**: none

### `lemma ellipticPointRhoPlusOne'_re`
- **Type**: `(ellipticPointRhoPlusOne' : ℍ).re = 1/2`
- **What**: Real part of ρ+1.
- **How**: `change`, then `simp` and `norm_num`.
- **Hypotheses**: none
- **Uses from project**: `ellipticPointRhoPlusOne'`
- **Used by**: `fd_orbit_rho_eq`
- **Visibility**: private
- **Lines**: 58-62
- **Notes**: none

### `lemma ellipticPointRhoPlusOne'_im`
- **Type**: `(ellipticPointRhoPlusOne' : ℍ).im = Real.sqrt 3 / 2`
- **What**: Imaginary part of ρ+1.
- **How**: `change`, then `simp`.
- **Hypotheses**: none
- **Uses from project**: `ellipticPointRhoPlusOne'`
- **Used by**: `fd_orbit_rho_eq`
- **Visibility**: private
- **Lines**: 64-68
- **Notes**: none

### `lemma sl2_det`
- **Type**: `(g : SL(2, ℤ)) → g₀₀·g₁₁ - g₀₁·g₁₀ = 1`
- **What**: The 2x2 determinant identity for SL₂(ℤ) matrices.
- **How**: `g.prop` rewritten via `Matrix.det_fin_two`.
- **Hypotheses**: `g : SL(2, ℤ)`
- **Uses from project**: []
- **Used by**: `normSq_denom_eq_one_of_smul_i_in_fd`
- **Visibility**: private
- **Lines**: 73-78
- **Notes**: `omit f hf in`

### `lemma denom_at_I`
- **Type**: `UpperHalfPlane.denom (map g) I = g₁₀·I + g₁₁`
- **What**: Computes the denominator of an SL₂(ℝ) action at `I`.
- **How**: `simp` unfolds `denom`, `toGL`, `map`.
- **Hypotheses**: `g : SL(2, ℤ)`
- **Uses from project**: []
- **Used by**: `normSq_denom_at_I`
- **Visibility**: private
- **Lines**: 81-86
- **Notes**: `omit f hf in`

### `lemma normSq_denom_at_I`
- **Type**: `normSq (denom (map g) I) = g₁₀² + g₁₁²`
- **What**: Squared modulus of denominator at `I`.
- **How**: `rw [denom_at_I, normSq_apply]`, simp, `ring`.
- **Hypotheses**: `g : SL(2, ℤ)`
- **Uses from project**: `denom_at_I`
- **Used by**: `normSq_denom_eq_one_of_smul_i_in_fd`, `fd_orbit_i_eq_i`
- **Visibility**: private
- **Lines**: 89-97
- **Notes**: `omit f hf in`

### `lemma normSq_denom_eq_one_of_smul_i_in_fd`
- **Type**: `(g : SL(2,ℤ)) → g•i ∈ 𝒟 → g₁₀² + g₁₁² = 1`
- **What**: For `g • i` in the standard FD, the integers `(c,d)` satisfy `c² + d² = 1`.
- **How**: 12 lines — uses `ModularGroup.im_smul_eq_div_normSq`, `fd_im_gt_halfFM`, `sl2_det`; via nlinarith on `c² + d² ∈ {1}` after bracketing in `[1, 2)`.
- **Hypotheses**: `g • ellipticPointI' ∈ 𝒟`
- **Uses from project**: `ellipticPointI'`, `ellipticPointI'_im`, `ellipticPointI'_coe`, `normSq_denom_at_I`, `fd_im_gt_halfFM`, `sl2_det`, `𝒟`
- **Used by**: `fd_orbit_i_eq_i`
- **Visibility**: private
- **Lines**: 100-124
- **Notes**: `omit f hf in`, >10 lines; key lemma `ModularGroup.im_smul_eq_div_normSq`

### `lemma re_smul_ellipticPointI`
- **Type**: `(g•i).re = (g₀₀·g₁₀ + g₀₁·g₁₁) / (g₁₀² + g₁₁²)`
- **What**: Real part of `g • i` as an explicit rational expression.
- **How**: `change`, `rw [coe_specialLinearGroup_apply, div_re, normSq_apply]`, `simp`, `ring`.
- **Hypotheses**: `g : SL(2, ℤ)`
- **Uses from project**: `ellipticPointI'_coe`
- **Used by**: `fd_orbit_i_eq_i`
- **Visibility**: private
- **Lines**: 127-139
- **Notes**: `omit f hf in`

### `theorem fd_orbit_i_eq_i`
- **Type**: `(p : ℍ) → p ∈ 𝒟 → orbFM p = oiFM → p = ellipticPointI'`
- **What**: FD orbit rigidity at `i`: any FD point in the i-orbit equals i.
- **How**: 24 lines — extract `g • i = p` via `Quotient.exact'`; uses `normSq_denom_eq_one_of_smul_i_in_fd` to force `c² + d² = 1`; then `re_smul_ellipticPointI` gives `Re = (ac+bd)`; bounds via `Int.one_le_abs` force `n = 0`.
- **Hypotheses**: `p ∈ 𝒟`, `orbFM p = oiFM`
- **Uses from project**: `𝒟`, `orbFM`, `oiFM`, `ellipticPointI'`, `normSq_denom_eq_one_of_smul_i_in_fd`, `ellipticPointI'_im`, `ellipticPointI'_coe`, `normSq_denom_at_I`, `re_smul_ellipticPointI`
- **Used by**: `orb_repCanon_nonEll`
- **Visibility**: public
- **Lines**: 145-171
- **Notes**: `omit f hf in`, >10 lines; key lemma `ModularGroup.im_smul_eq_div_normSq`, `UpperHalfPlane.ext_re_im`

### `lemma denom_at_rho`
- **Type**: `denom (map g) ρ = g₁₀·(-1/2+(√3/2)i) + g₁₁`
- **What**: Denominator of action at ρ.
- **How**: `simp` unfolding denominator pieces and `ellipticPointRho'`.
- **Hypotheses**: `g : SL(2, ℤ)`
- **Uses from project**: `ellipticPointRho'`
- **Used by**: `normSq_denom_at_rho`
- **Visibility**: private
- **Lines**: 176-183
- **Notes**: `omit f hf in`

### `lemma normSq_denom_at_rho`
- **Type**: `normSq (denom (map g) ρ) = g₁₀² - g₁₀·g₁₁ + g₁₁²`
- **What**: Squared modulus of denominator at ρ.
- **How**: `rw [denom_at_rho, normSq_apply]`, simp, ring_nf, nlinarith with `Real.mul_self_sqrt`.
- **Hypotheses**: `g : SL(2, ℤ)`
- **Uses from project**: `denom_at_rho`
- **Used by**: `normSq_denom_eq_one_of_smul_rho_in_fd`, `abs_re_eq_half_of_smul_rho_in_fd`, `fd_orbit_rho_eq`
- **Visibility**: private
- **Lines**: 186-197
- **Notes**: `omit f hf in`

### `lemma normSq_denom_eq_one_of_smul_rho_in_fd`
- **Type**: `(g : SL(2,ℤ)) → g•ρ ∈ 𝒟 → c² - cd + d² = 1`
- **What**: For `g • ρ` in FD, the integers `(c,d)` satisfy `c² - cd + d² = 1`.
- **How**: 18 lines — uses `ModularGroup.im_smul_eq_div_normSq`, `fd_im_gt_halfFM`; bound the form via `nlinarith` with `Real.mul_self_sqrt (3 ≥ 0)`; then omega.
- **Hypotheses**: `g • ellipticPointRho' ∈ 𝒟`
- **Uses from project**: `ellipticPointRho'`, `ellipticPointRho'_im`, `normSq_denom_at_rho`, `fd_im_gt_halfFM`, `𝒟`
- **Used by**: `abs_re_eq_half_of_smul_rho_in_fd`, `fd_orbit_rho_eq`
- **Visibility**: private
- **Lines**: 200-224
- **Notes**: `omit f hf in`, >10 lines; key lemma `ModularGroup.im_smul_eq_div_normSq`

### `lemma abs_re_eq_half_of_smul_rho_in_fd`
- **Type**: `g • ρ ∈ 𝒟 → c² - cd + d² = 1 → |(g•ρ).re| = 1/2`
- **What**: When `g•ρ` is in FD and norm condition holds, `|Re| = 1/2`.
- **How**: 17 lines — uses `ModularGroup.im_smul_eq_div_normSq`, computes `im = √3/2`, hence `im² = 3/4`; from `‖p‖² ≥ 1` and `re² + 3/4 ≥ 1` get `|re| ≥ 1/2`, combined with `|re| ≤ 1/2` (FD).
- **Hypotheses**: `g • ellipticPointRho' ∈ 𝒟`, `c² - cd + d² = 1`
- **Uses from project**: `ellipticPointRho'`, `ellipticPointRho'_im`, `normSq_denom_at_rho`, `𝒟`
- **Used by**: `fd_orbit_rho_eq`
- **Visibility**: private
- **Lines**: 227-250
- **Notes**: `omit f hf in`, >10 lines; key lemma `Complex.normSq_apply`

### `theorem fd_orbit_rho_eq`
- **Type**: `(p : ℍ) → p ∈ 𝒟 → orbFM p = orhoFM → p = ρ ∨ p = ρ+1`
- **What**: FD orbit rigidity at ρ: any FD point in the ρ-orbit equals ρ or ρ+1.
- **How**: 22 lines — extract `g • ρ = p`; uses `normSq_denom_eq_one_of_smul_rho_in_fd`, `abs_re_eq_half_of_smul_rho_in_fd` to get `Re ∈ {-1/2, 1/2}`; case split via `UpperHalfPlane.ext_re_im`.
- **Hypotheses**: `p ∈ 𝒟`, `orbFM p = orhoFM`
- **Uses from project**: `𝒟`, `orbFM`, `orhoFM`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointRho'_im`, `ellipticPointRho'_re`, `ellipticPointRhoPlusOne'_re`, `ellipticPointRhoPlusOne'_im`, `normSq_denom_eq_one_of_smul_rho_in_fd`, `normSq_denom_at_rho`, `abs_re_eq_half_of_smul_rho_in_fd`
- **Used by**: `orb_repCanon_nonEll`
- **Visibility**: public
- **Lines**: 256-278
- **Notes**: `omit f hf in`, >10 lines; key lemma `ModularGroup.im_smul_eq_div_normSq`, `UpperHalfPlane.ext_re_im`

### `theorem orb_repCanon_nonEll`
- **Type**: `p ∈ repCanon f hf → orbFM p ≠ oiFM ∧ orbFM p ≠ orhoFM`
- **What**: `repCanon` elements are non-elliptic.
- **How**: From `repCanon_ne_elliptic` and FD-rigidity (`fd_orbit_i_eq_i`, `fd_orbit_rho_eq`).
- **Hypotheses**: `p ∈ repCanon f hf`
- **Uses from project**: `repCanon`, `repCanon_ne_elliptic`, `repCanon_mem_fd`, `fd_orbit_i_eq_i`, `fd_orbit_rho_eq`, `orbFM`, `oiFM`, `orhoFM`
- **Used by**: `finsum_nonell_eq_repCanon_sum`
- **Visibility**: public
- **Lines**: 283-288
- **Notes**: none

### `theorem finsum_nonell_eq_repCanon_sum`
- **Type**: `∑ᶠ q : NonEllOrbitFM, ordOrbitQ f q = ∑ s ∈ repCanon f hf, orderOfVanishingAt' f s`
- **What**: The finsum over non-elliptic orbits equals the `repCanon` Finset sum.
- **How**: 22 lines — convert finsum to Finset.sum via `finsum_eq_sum_of_support_subset` using `finite_support_ordOrbit_nonEllFM`; build bijection `repCanon → support` using `orb_repCanon_nonEll`, `orb_injOn_repCanon`, `exists_repCanon_of_nonEllOrbit`; apply `Finset.sum_bij`.
- **Hypotheses**: `f : ModularForm (Gamma 1) k`, `hf : f ≠ 0`
- **Uses from project**: `NonEllOrbitFM`, `ordOrbitQ`, `repCanon`, `orderOfVanishingAt'`, `finite_support_ordOrbit_nonEllFM`, `orb_repCanon_nonEll`, `ordOrbitFM`, `ordOrbit_mkFM`, `repCanon_mem_s₀`, `s₀FM`, `exists_repCanon_of_nonEllOrbit`, `orb_injOn_repCanon`, `orbFM`
- **Used by**: `valence_formula_textbook_orbit_finsum`
- **Visibility**: public
- **Lines**: 293-318
- **Notes**: >10 lines; key lemma `Finset.sum_bij`

### `theorem repCanon_sum_split`
- **Type**: `∑ s ∈ repCanon = ∑ s ∈ repStrict + ∑ s ∈ repLeftVert + ∑ s ∈ repLeftArc`
- **What**: The `repCanon` decomposes as strict-interior + left-vertical + left-arc sums.
- **How**: Unfold `repCanon`, apply `Finset.sum_union` twice using `disjoint_union_repLeftArc` and `disjoint_repStrict_repLeftVert`.
- **Hypotheses**: `f, hf` (implicit)
- **Uses from project**: `repCanon`, `repStrict`, `repLeftVert`, `repLeftArc`, `disjoint_union_repLeftArc`, `disjoint_repStrict_repLeftVert`, `orderOfVanishingAt'`
- **Used by**: `valence_formula_textbook_orbit_finsum`
- **Visibility**: public
- **Lines**: 323-330
- **Notes**: none

### `theorem valence_formula_textbook_orbit_finsum`
- **Type**: takes a `h_core` hypothesis (the FD coefficient expansion identity) → textbook orbit-sum valence formula
- **What**: **The Valence Formula** in textbook orbit-sum form: `ord∞(f) + (1/2)ord_i(f) + (1/3)ord_ρ(f) + ∑ᶠ ord_q(f) = k/12`, conditional on the core FD identity.
- **How**: Rewrite via `finsum_nonell_eq_repCanon_sum`, then `repCanon_sum_split`; unfold the three rep-Finsets; close via `linear_combination` against `h_core` applied to `s₀FM f hf` with `s₀FM_mem_fd` and `s₀FM_complete`.
- **Hypotheses**: `hf : f ≠ 0`; `h_core` (universal coefficient identity over `S : Finset ℍ` capturing all zeros).
- **Uses from project**: `orderAtCusp'`, `orderOfVanishingAt'`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `sLeftVertFM`, `NonEllOrbitFM`, `ordOrbitQ`, `finsum_nonell_eq_repCanon_sum`, `repCanon_sum_split`, `repStrict`, `repLeftVert`, `repLeftArc`, `s₀FM`, `s₀FM_mem_fd`, `s₀FM_complete`, `𝒟`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 341-365
- **Notes**: >10 lines; `include hf`; doc-string the textbook formula; key tactic `linear_combination`

## File Summary
- 17 declarations: 1 def, 14 private lemmas/theorems (elliptic-point coordinates, SL₂ denominator computations, FD orbit rigidity), 3 public theorems (`orb_repCanon_nonEll`, `finsum_nonell_eq_repCanon_sum`, `repCanon_sum_split`), and 1 main result `valence_formula_textbook_orbit_finsum`.
- Builds on `CanonicalReps` (`repCanon`, `repStrict`, `repLeftVert`, `repLeftArc`, `s₀FM`, `ordOrbit*`, etc.).
- Establishes FD-orbit rigidity (i and ρ have unique FD representatives) and packages the textbook orbit-sum valence formula conditional on the core FD coefficient identity proved elsewhere.
- No sorries, no axioms, no `set_option`. `attribute [local instance] Classical.propDecidable`, `noncomputable section`.
