# CoreIdentityProof.md Inventory

### `structure FDWindingDataFull (H : ℝ) extends FDWindingData H`
- **Type**: structure extending `FDWindingData H` with field `boundary_winding : ∀ z, z.im > 0 → z.im < H → z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne → ¬(‖z‖ > 1 ∧ |z.re| < 1/2) → Complex.normSq z ≥ 1 → |z.re| ≤ 1/2 → HasGeneralizedWindingNumber toFDWindingData.boundary z (−1/2)`
- **What**: Extends `FDWindingData` with the smooth-boundary winding: at any non-elliptic on-curve point, the generalized winding number is `−1/2` (vertical edges and non-elliptic arc points).
- **How**: structure declaration; field captures the `−1/2` winding from `SmoothBoundaryWindingData` at all FD smooth boundary points.
- **Hypotheses**: parameter `H : ℝ` (height cutoff).
- **Uses from project**: [`FDWindingData`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `HasGeneralizedWindingNumber`]
- **Used by**: `explicit_coefficients_of_pvChain`, `boundary_weight_at`, `valence_formula_orbit_sum_of_pvChain`
- **Visibility**: public
- **Lines**: 77–83

### `lemma ellipticPointRho_re_neg`
- **Type**: `(ellipticPointRho' : ℂ).re < 0`
- **What**: The real part of `ρ = −1/2 + (√3/2) i` is negative.
- **How**: `change` to `(−1/2 + (Real.sqrt 3/2)·I).re`; `simp` with `add_re, mul_re, I_re, I_im`; `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: [`ellipticPointRho'`]
- **Used by**: `rho_singleton_sum_eq`, `bdry_ne_eq_union`
- **Visibility**: private
- **Lines**: 88–92
- **Notes**: `omit f hf`.

### `lemma ellipticPointRhoPlusOne_re_pos`
- **Type**: `(ellipticPointRhoPlusOne' : ℂ).re > 0`
- **What**: The real part of `ρ + 1 = 1/2 + (√3/2) i` is positive.
- **How**: `change` + `simp` with the same lemmas + `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: [`ellipticPointRhoPlusOne'`]
- **Used by**: `rho_singleton_sum_eq`, `bdry_ne_eq_union`
- **Visibility**: private
- **Lines**: 94–98
- **Notes**: `omit f hf`.

### `lemma ellipticPoint_ne_iρ1FM`
- **Type**: `ellipticPointI' ≠ ellipticPointRhoPlusOne'`
- **What**: `i ≠ ρ+1` (distinguishing two elliptic points).
- **How**: Apply `congr_arg` to `(z : ℂ).re`; `simp` reveals `0 ≠ 1/2`.
- **Hypotheses**: none.
- **Uses from project**: [`ellipticPointI'`, `ellipticPointRhoPlusOne'`]
- **Used by**: `elliptic_finset_sum_eq_three`
- **Visibility**: private
- **Lines**: 101–104
- **Notes**: `omit f hf`.

### `lemma ellipticPoint_ne_ρρ1FM`
- **Type**: `ellipticPointRho' ≠ ellipticPointRhoPlusOne'`
- **What**: `ρ ≠ ρ + 1`.
- **How**: Same recipe via `(z : ℂ).re` and `norm_num`.
- **Hypotheses**: none.
- **Uses from project**: [`ellipticPointRho'`, `ellipticPointRhoPlusOne'`]
- **Used by**: `elliptic_finset_sum_eq_three`
- **Visibility**: private
- **Lines**: 107–111
- **Notes**: `omit f hf`.

### `lemma elliptic_finset_sum_eq_three`
- **Type**: `(S : Finset UpperHalfPlane) (g : UpperHalfPlane → ℂ) (_hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete_zero : ∀ p, p ∈ 𝒟 → p ∉ S → g p = 0) : let P := (p = i ∨ p = ρ ∨ p = ρ+1) in ∑ s ∈ S.filter P, g s = g i + g ρ + g (ρ+1)`
- **What**: For an FD sum, the elliptic-point-filtered sum equals `g(i) + g(ρ) + g(ρ+1)` (zeros elsewhere are absorbed).
- **How**: Upgrade `S.filter P ⊆ {i, ρ, ρ+1}` with `Finset.sum_subset`; show outside terms are `0` via `hS_complete_zero` (using FD membership lemmas `ellipticPointI_mem_fd`, `ellipticPointRho_mem_fd`, `ellipticPointRhoPlusOne_mem_fdFM`); apply `Finset.sum_insert` twice + `Finset.sum_singleton`; final `ring`. Disjointness facts use `ellipticPointI_ne_rho`, `ellipticPoint_ne_iρ1FM`, `ellipticPoint_ne_ρρ1FM`.
- **Hypotheses**: `S` lies in FD; `g` vanishes outside `S` for `p ∈ 𝒟`.
- **Uses from project**: [`ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointI_mem_fd`, `ellipticPointRho_mem_fd`, `ellipticPointRhoPlusOne_mem_fdFM`, `ellipticPointI_ne_rho`, `ellipticPoint_ne_iρ1FM`, `ellipticPoint_ne_ρρ1FM`, `𝒟`]
- **Used by**: `explicit_coefficients_of_pvChain`
- **Visibility**: private
- **Lines**: 116–148
- **Notes**: `omit f hf`; >10 lines.

### `theorem explicit_coefficients_of_pvChain`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H : ℝ} (D : FDWindingDataFull H) (h_pv : ∑ s ∈ S, generalizedWindingNumber D.boundary (↑s) * (ord_p f s : ℂ) = −((k:ℂ)/12 − orderAtCusp' f)) : orderAtCusp' f + 1/2 * ord_p f i + 1/6 * ord_p f ρ + 1/6 * ord_p f (ρ+1) + ∑_{s ∈ non-elliptic part of S} (−gWN_D s) * ord_p f s = k/12`
- **What**: Substitute the explicit winding weights `−1/2` at `i`, `−1/6` at `ρ`, `−1/6` at `ρ+1` into the PV chain identity, exposing the elliptic contributions and leaving a residual sum over the non-elliptic part.
- **How**: Set `g s := gWN_D s · ord_p f s`. Split the sum via `Finset.sum_filter_add_sum_filter_not`. Reduce the elliptic part with `elliptic_finset_sum_eq_three`. Use `D.toFDWindingData.winding_at_i.eq`, `winding_at_rho.eq`, `winding_at_rho_plus_one.eq` to get the weights. Rewrite `S.filter (¬P)` as `S.filter (p ≠ i ∧ p ≠ ρ ∧ p ≠ ρ+1)` using `not_or`. Close with `linear_combination -h_pv`.
- **Hypotheses**: `S` collects FD points, complete for nonzero orders, full winding data, PV chain identity at height `H`.
- **Uses from project**: [`FDWindingDataFull`, `FDWindingData.winding_at_i`, `FDWindingData.winding_at_rho`, `FDWindingData.winding_at_rho_plus_one`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`, `elliptic_finset_sum_eq_three`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `𝒟`]
- **Used by**: `valence_formula_orbit_sum_of_pvChain`
- **Visibility**: private
- **Lines**: 153–212
- **Notes**: >40 lines.

### `lemma unit_circle_re_neg_half_eq_rho`
- **Type**: `(s : ℍ) (hs_norm : ‖(s:ℂ)‖ = 1) (hs_re : (s:ℂ).re = −1/2) : s = ellipticPointRho'`
- **What**: A point on the unit circle with real part `−1/2` is exactly `ρ`.
- **How**: From `‖s‖ = 1` derive `Complex.normSq s = 1`; with `re = −1/2` get `im² = 3/4`; factor `(im − √3/2)(im + √3/2) = 0` and reject the negative root by `s.2 > 0`; conclude `im = √3/2`. Apply `UpperHalfPlane.ext` + `Complex.ext` with simp lemmas.
- **Hypotheses**: `‖s‖ = 1`, `s.re = −1/2`.
- **Uses from project**: [`ellipticPointRho'`]
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 217–234
- **Notes**: `omit f hf`; >10 lines.

### `lemma unit_circle_re_pos_half_eq_rho_plus_one`
- **Type**: `(s : ℍ) (hs_norm : ‖(s:ℂ)‖ = 1) (hs_re : (s:ℂ).re = 1/2) : s = ellipticPointRhoPlusOne'`
- **What**: A point on the unit circle with real part `1/2` is exactly `ρ + 1`.
- **How**: Same factoring `(im − √3/2)(im + √3/2) = 0` followed by `UpperHalfPlane.ext` + `Complex.ext`.
- **Hypotheses**: `‖s‖ = 1`, `s.re = 1/2`.
- **Uses from project**: [`ellipticPointRhoPlusOne'`]
- **Used by**: unused in file
- **Visibility**: private
- **Lines**: 237–255
- **Notes**: `omit f hf`; >10 lines.

### `lemma unit_circle_re_zero_eq_i`
- **Type**: `(s : ℍ) (hs_norm : ‖(s:ℂ)‖ = 1) (hs_re : (s:ℂ).re = 0) : s = ellipticPointI'`
- **What**: A point on the unit circle with real part `0` is exactly `i`.
- **How**: `‖s‖ = 1 ∧ re = 0` ⇒ `im² = 1` ⇒ `im = 1` (using `s.2 > 0` and `mul_le_of_le_one_right`); `UpperHalfPlane.ext` + `Complex.ext` with `Complex.I_re`, `Complex.I_im`.
- **Hypotheses**: `‖s‖ = 1`, `s.re = 0`.
- **Uses from project**: [`ellipticPointI'`]
- **Used by**: `bdry_ne_mem_union`
- **Visibility**: private
- **Lines**: 258–269
- **Notes**: `omit f hf`; >10 lines.

### `theorem boundary_weight_at`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) {H : ℝ} (D : FDWindingDataFull H) (hH_above : ∀ s ∈ S, (s:ℂ).im < H) (s : ℍ) (hs : s ∈ S) (hsi : s ≠ i) (hsρ : s ≠ ρ) (hsρ1 : s ≠ ρ+1) (h_not_int : ¬(‖(s:ℂ)‖ > 1 ∧ |(s:ℂ).re| < 1/2)) : generalizedWindingNumber D.boundary (↑s) = −1/2`
- **What**: At non-elliptic non-interior FD points in `S` (vertical edges or non-elliptic arc), `gWN = −1/2`.
- **How**: From `s ∈ 𝒟` extract `|re| ≤ 1/2` and `1 ≤ ‖s‖`. Convert `1 ≤ ‖s‖` to `Complex.normSq s ≥ 1` via `Complex.normSq_eq_norm_sq` + `nlinarith`. Invoke `D.boundary_winding` with negation lemmas casting `s ≠ x'` to `(↑s : ℂ) ≠ x`.
- **Hypotheses**: FD membership, height bound, three non-elliptic conditions, non-interior.
- **Uses from project**: [`FDWindingDataFull`, `generalizedWindingNumber`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `𝒟`]
- **Used by**: `valence_formula_orbit_sum_of_pvChain`
- **Visibility**: private
- **Lines**: 273–297
- **Notes**: `omit f hf`; >10 lines.

### `lemma rho_singleton_sum_eq`
- **Type**: `(S : Finset UpperHalfPlane) (hS_complete : ∀ p, p ∈ 𝒟 → ord_p f p ≠ 0 → p ∈ S) (h_ord : ord_p f ρ ≠ 0) : ∑_{s ∈ if ρ+1 ∈ sRightArcFM S then {ρ+1} else ∅} (ord_p f s : ℂ) = ∑_{s ∈ if ρ ∈ sLeftArcFM S then {ρ} else ∅} (ord_p f s : ℂ)`
- **What**: When `ord_p f ρ ≠ 0`, both singletons {ρ+1} ∈ sRightArcFM and {ρ} ∈ sLeftArcFM appear, and the cast sums are equal.
- **How**: Show `ρ ∈ sLeftArcFM S` and `ρ+1 ∈ sRightArcFM S` via FD membership lemmas and the arc-classification lemmas `ellipticPointRho_norm`, `ellipticPointRho_re_neg`, `ellipticPointRhoPlusOne_norm`, `ellipticPointRhoPlusOne_re_pos`. Both `if`-conditions are true; sums become `Finset.sum_singleton`. Cast `ord_p f (ρ+1) = ord_p f ρ` via `ord_rho_plus_one_eq_ord_rho_via_vAddFM`.
- **Hypotheses**: completeness of `S`, `ord_p f ρ ≠ 0`.
- **Uses from project**: [`sLeftArcFM`, `sRightArcFM`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointRho_mem_fd`, `ellipticPointRhoPlusOne_mem_fdFM`, `ellipticPointRho_norm`, `ellipticPointRhoPlusOne_norm`, `ellipticPointRho_re_neg`, `ellipticPointRhoPlusOne_re_pos`, `orderOfVanishingAt'`, `ord_rho_plus_one_eq_ord_rho_via_vAddFM`]
- **Used by**: `sum_nonEllArc_right_eq_left`
- **Visibility**: private
- **Lines**: 301–320
- **Notes**: >10 lines.

### `theorem sum_nonEllArc_right_eq_left`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → ord_p f p ≠ 0 → p ∈ S) : let RA_ne := S.filter (p ≠ ρ+1 ∧ ‖p‖ = 1 ∧ p.re > 0), LA_ne := S.filter (p ≠ ρ ∧ ‖p‖ = 1 ∧ p.re < 0) in ∑ p ∈ RA_ne, ord_p f p = ∑ p ∈ LA_ne, ord_p f p`
- **What**: Non-elliptic right-arc and left-arc ord sums are equal (S-action pairing).
- **How**: Show `RA_ne = (sRightArcFM S).filter (· ≠ ρ+1)` and similarly for `LA_ne`. Split via `Finset.sum_filter_add_sum_filter_not`. The total-arc identity `sum_ord_rightArc_eq_sum_ord_leftArcFM` gives `RA = LA`. Subtracting the singletons `{ρ+1}` and `{ρ}` (using `Finset.filter_eq'`) reduces to `rho_singleton_sum_eq` (case `ord ≠ 0`) or both zero (case `ord = 0`).
- **Hypotheses**: `S ⊆ 𝒟`, complete for nonzero orders.
- **Uses from project**: [`sRightArcFM`, `sLeftArcFM`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `sum_ord_rightArc_eq_sum_ord_leftArcFM`, `orderOfVanishingAt'`, `ord_rho_plus_one_eq_ord_rho_via_vAddFM`, `rho_singleton_sum_eq`]
- **Used by**: `half_bdry_sum_eq_leftVert_plus_leftArc`
- **Visibility**: private
- **Lines**: 323–366
- **Notes**: >30 lines.

### `theorem bdry_ne_mem_union`
- **Type**: `(S : Finset UpperHalfPlane) (s : ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟) (hs_S : s ∈ S) (hsi : s ≠ i) (hsρ : s ≠ ρ) (hsρ1 : s ≠ ρ+1) (h_not_int : ¬(‖s‖ > 1 ∧ |s.re| < 1/2)) : s ∈ sRightVertFM S ∨ s ∈ sLeftVertFM S ∨ (s ∈ S ∧ s ≠ ρ+1 ∧ ‖s‖ = 1 ∧ s.re > 0) ∨ (s ∈ S ∧ s ≠ ρ ∧ ‖s‖ = 1 ∧ s.re < 0)`
- **What**: Any non-elliptic non-interior FD point falls into one of four boundary classes: right-vert, left-vert, right-arc-ne, left-arc-ne.
- **How**: Case split on `1 ≤ ‖s‖` via `eq_or_lt_of_le`. Equality (arc): trichotomy on `s.re` versus `0`, rejecting `re = 0` by `unit_circle_re_zero_eq_i`. Strict inequality (vert): `|re| ≤ 1/2` from FD; `h_not_int` forces `|re| = 1/2`; case split via `abs_cases`.
- **Hypotheses**: `S ⊆ 𝒟`, three non-elliptic conditions, non-interior.
- **Uses from project**: [`sRightVertFM`, `sLeftVertFM`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `unit_circle_re_zero_eq_i`, `𝒟`]
- **Used by**: `bdry_ne_eq_union`
- **Visibility**: private
- **Lines**: 371–392
- **Notes**: `omit f hf`; >10 lines.

### `theorem bdry_ne_eq_union`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) : (S.filter (non-elliptic).filter (non-interior)) = sRightVertFM S ∪ sLeftVertFM S ∪ (right-arc-ne) ∪ (left-arc-ne)`
- **What**: The non-elliptic boundary points of `S` equal the union of right-vert, left-vert, right-arc-ne, left-arc-ne.
- **How**: Set equality via `ext`. Forward direction uses `bdry_ne_mem_union`. Backward direction: distinguish each branch and prove `s ≠ i, ρ, ρ+1` and `¬interior` using `ellipticPointRho_norm`, `ellipticPointRhoPlusOne_norm`, `ellipticPointRho_re_neg`, `ellipticPointRhoPlusOne_re_pos`, and direct `linarith`/`norm_num` on real parts and norms.
- **Hypotheses**: `S ⊆ 𝒟`.
- **Uses from project**: [`sRightVertFM`, `sLeftVertFM`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointRho_norm`, `ellipticPointRhoPlusOne_norm`, `ellipticPointRho_re_neg`, `ellipticPointRhoPlusOne_re_pos`, `bdry_ne_mem_union`, `𝒟`]
- **Used by**: `half_bdry_sum_eq_leftVert_plus_leftArc`
- **Visibility**: private
- **Lines**: 395–438
- **Notes**: `omit f hf`; >30 lines.

### `lemma bdry_four_disjoint`
- **Type**: `(S : Finset UpperHalfPlane) (RA_ne LA_ne : Finset UpperHalfPlane) (hRA : RA_ne = S.filter (· ≠ ρ+1 ∧ ‖·‖ = 1 ∧ ·.re > 0)) (hLA : LA_ne = S.filter (· ≠ ρ ∧ ‖·‖ = 1 ∧ ·.re < 0)) : Disjoint (sRightVertFM S ∪ sLeftVertFM S ∪ RA_ne) LA_ne`
- **What**: The first three boundary classes are jointly disjoint from the left-arc-ne class (sign-of-`re` separation).
- **How**: `Finset.disjoint_union_left.mpr` twice. Each disjointness reduces to `linarith` on real parts and norms via `Finset.disjoint_filter`.
- **Hypotheses**: definitional descriptions of `RA_ne` and `LA_ne`.
- **Uses from project**: [`sRightVertFM`, `sLeftVertFM`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`]
- **Used by**: `half_bdry_sum_eq_leftVert_plus_leftArc`
- **Visibility**: private
- **Lines**: 441–457
- **Notes**: `omit f hf`; >10 lines.

### `theorem half_bdry_sum_eq_leftVert_plus_leftArc`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → ord_p f p ≠ 0 → p ∈ S) : (1/2) * ∑_{s ∈ BDRY} ord_p f s = ∑_{s ∈ sLeftVertFM S} ord_p f s + ∑_{s ∈ LA_ne} ord_p f s`
- **What**: Half of the non-elliptic boundary ord-sum equals left-vert + left-arc-ne ord sums (from T-translation and S-action pairings).
- **How**: Decompose `BDRY` via `bdry_ne_eq_union` and `Finset.sum_union` using disjointness (`bdry_four_disjoint`, plus right-vert/left-vert disjoint, plus vert vs right-arc-ne disjoint). Apply pairing identities: `sum_ord_rightVert_eq_sum_ord_leftVertFM` (T-translation) and `sum_nonEllArc_right_eq_left` (S-action). Final `ring`.
- **Hypotheses**: `S ⊆ 𝒟`, complete for nonzero orders.
- **Uses from project**: [`sRightVertFM`, `sLeftVertFM`, `orderOfVanishingAt'`, `bdry_ne_eq_union`, `bdry_four_disjoint`, `sum_ord_rightVert_eq_sum_ord_leftVertFM`, `sum_nonEllArc_right_eq_left`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`]
- **Used by**: `valence_formula_orbit_sum_of_pvChain`
- **Visibility**: private
- **Lines**: 460–495
- **Notes**: >30 lines.

### `theorem valence_formula_orbit_sum_of_pvChain`
- **Type**: `(S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → ord_p f p ≠ 0 → p ∈ S) (h_pvChain : ∃ H, ∃ D : FDWindingDataFull H, (∀ s ∈ S, s.im < H) ∧ ∑_{s∈S} gWN_D s · ord_p f s = −((k:ℂ)/12 − orderAtCusp' f)) : orderAtCusp' f + 1/2 * ord_p f i + 1/3 * ord_p f ρ + ∑_{s∈INT} ord_p f s + ∑_{s∈sLeftVertFM S} ord_p f s + ∑_{s∈LA_ne} ord_p f s = k/12`
- **What**: The main orbit-sum form of the valence formula (Diamond–Shurman / Serre): mass `1/2` at `i`, `1/3` at `ρ`, integer mass at every interior FD point, and matching boundary mass on the left vertical + left arc.
- **How**: (>50 lines) Apply `explicit_coefficients_of_pvChain` then `ord_rho_plus_one_eq_ord_rho_via_vAddFM` to collapse `1/6 · ord_p f (ρ+1) + 1/6 · ord_p f ρ` into `1/3 · ord_p f ρ`. Rewrite the non-elliptic sum: at interior points `gWN = −1` via `D.toFDWindingData.interior_winding`, at boundary points `gWN = −1/2` via `boundary_weight_at`; combine via `if-then-else` and `Finset.sum_filter_add_sum_filter_not`. Apply `half_bdry_sum_eq_leftVert_plus_leftArc` to recast `(1/2) · ∑ BDRY` as `∑ LV + ∑ LA_ne`. Close with `linear_combination`.
- **Hypotheses**: `S ⊆ 𝒟`, complete for nonzero orders, PV chain (existential height + full winding data + chain identity).
- **Uses from project**: [`FDWindingDataFull`, `FDWindingData.interior_winding`, `generalizedWindingNumber`, `orderOfVanishingAt'`, `orderAtCusp'`, `sLeftVertFM`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ord_rho_plus_one_eq_ord_rho_via_vAddFM`, `explicit_coefficients_of_pvChain`, `boundary_weight_at`, `half_bdry_sum_eq_leftVert_plus_leftArc`, `𝒟`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 512–612
- **Notes**: >80 lines.

## File Summary
CoreIdentityProof.lean assembles the orbit-sum form of the valence formula `[f] = k/12` for weight-`k` modular forms on `SL₂(ℤ)`, conditional on a PV chain identity `h_pvChain` packaging the height-`H` winding data and the residue-theorem identity. The architecture is: (1) `FDWindingDataFull` extends `FDWindingData` with `−1/2` smooth-boundary winding; (2) elliptic and unit-circle classification lemmas; (3) the elliptic-coefficient substitution `explicit_coefficients_of_pvChain` (substituting `−1/2, −1/6, −1/6`); (4) boundary classification (`bdry_ne_mem_union`, `bdry_ne_eq_union`, `bdry_four_disjoint`); (5) orbit pairings `sum_nonEllArc_right_eq_left` (S-action) and reuse of `sum_ord_rightVert_eq_sum_ord_leftVertFM` (T-translation) to halve the boundary sum (`half_bdry_sum_eq_leftVert_plus_leftArc`); (6) the main theorem `valence_formula_orbit_sum_of_pvChain`. 18 declarations total (1 structure, 14 private helpers, 1 public theorem). Imports `ValenceFormula`, `FDBoundary`, `GeneralizedWindingNumber` from ForMathlib. No `sorry`, `axiom`, or `set_option`. Uses `attribute [local instance] Classical.propDecidable`.

## N3 = 18
