# Inventory: CanonicalReps.lean

File: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/CanonicalReps.lean
Lines: 474

### `def repStrict`
- **Type**: `{k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0) : Finset ℍ`
- **What**: Strict interior representatives — points in `s₀FM f hf` with `‖p‖ > 1`, `|re| < 1/2`, distinct from the three elliptic points.
- **How**: Filter on `s₀FM f hf` by the conjunction of inequalities.
- **Hypotheses**: `f` modular form, `f ≠ 0` (implicit via `s₀FM`).
- **Uses from project**: `s₀FM`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`
- **Used by**: `repCanon`, `repStrict_mem_s₀`, `disjoint_repStrict_repLeftVert`, `disjoint_union_repLeftArc`
- **Visibility**: public (`noncomputable def`)
- **Lines**: 46-48
- **Notes**: none

### `def repLeftVert`
- **Type**: `(f : ModularForm (Gamma 1) k) (hf : f ≠ 0) : Finset ℍ`
- **What**: Left vertical edge representatives — points in `s₀` with `re = -1/2`, `‖p‖ > 1`.
- **How**: `sLeftVertFM (s₀FM f hf)`.
- **Hypotheses**: same.
- **Uses from project**: `s₀FM`, `sLeftVertFM`
- **Used by**: `repCanon`, `repLeftVert_mem_s₀`, `disjoint_repStrict_repLeftVert`, `disjoint_union_repLeftArc`
- **Visibility**: public
- **Lines**: 50-51
- **Notes**: none

### `def repLeftArc`
- **Type**: `(f : ModularForm (Gamma 1) k) (hf : f ≠ 0) : Finset ℍ`
- **What**: Left arc representatives — points in `s₀` with `‖p‖ = 1`, `re < 0`, distinct from `ρ`.
- **How**: Filter on `s₀FM f hf` by the conjunction of inequalities.
- **Hypotheses**: same.
- **Uses from project**: `s₀FM`, `ellipticPointRho'`
- **Used by**: `repCanon`, `repLeftArc_mem_s₀`, `disjoint_union_repLeftArc`
- **Visibility**: public
- **Lines**: 53-55
- **Notes**: none

### `def repCanon`
- **Type**: `(f : ModularForm (Gamma 1) k) (hf : f ≠ 0) : Finset ℍ`
- **What**: Union of the three canonical sets `repStrict ∪ repLeftVert ∪ repLeftArc`.
- **How**: `Finset.union` of the three.
- **Hypotheses**: same.
- **Uses from project**: `repStrict`, `repLeftVert`, `repLeftArc`
- **Used by**: `repCanon_mem_s₀`, `repCanon_mem_fd`, `repCanon_ne_elliptic`, `exists_repCanon_of_nonEllOrbit`, helpers, `orb_injOn_repCanon`
- **Visibility**: public
- **Lines**: 57-59
- **Notes**: none

### `theorem repStrict_mem_s₀`
- **Type**: `{p : ℍ} (hp : p ∈ repStrict f hf) : p ∈ s₀FM f hf`
- **What**: Strict reps lie in `s₀FM`.
- **How**: `(Finset.mem_filter.mp hp).1` (first conjunct).
- **Hypotheses**: `p ∈ repStrict f hf`.
- **Uses from project**: `repStrict`, `s₀FM`
- **Used by**: `repCanon_mem_s₀`
- **Visibility**: public
- **Lines**: 63-64
- **Notes**: none

### `theorem repLeftVert_mem_s₀`
- **Type**: `{p : ℍ} (hp : p ∈ repLeftVert f hf) : p ∈ s₀FM f hf`
- **What**: Left vertical reps lie in `s₀FM`.
- **How**: `(Finset.mem_filter.mp hp).1`.
- **Hypotheses**: `p ∈ repLeftVert f hf`.
- **Uses from project**: `repLeftVert`, `s₀FM`, `sLeftVertFM`
- **Used by**: `repCanon_mem_s₀`
- **Visibility**: public
- **Lines**: 66-67
- **Notes**: none

### `theorem repLeftArc_mem_s₀`
- **Type**: `{p : ℍ} (hp : p ∈ repLeftArc f hf) : p ∈ s₀FM f hf`
- **What**: Left arc reps lie in `s₀FM`.
- **How**: `(Finset.mem_filter.mp hp).1`.
- **Hypotheses**: `p ∈ repLeftArc f hf`.
- **Uses from project**: `repLeftArc`, `s₀FM`
- **Used by**: `repCanon_mem_s₀`
- **Visibility**: public
- **Lines**: 69-70
- **Notes**: none

### `theorem repCanon_mem_s₀`
- **Type**: `{p : ℍ} (hp : p ∈ repCanon f hf) : p ∈ s₀FM f hf`
- **What**: Every element of `repCanon` lies in `s₀`.
- **How**: `Finset.mem_union`-case-split into the three subsets; apply `repStrict_mem_s₀`/`repLeftVert_mem_s₀`/`repLeftArc_mem_s₀`.
- **Hypotheses**: `p ∈ repCanon f hf`.
- **Uses from project**: `repCanon`, `s₀FM`, `repStrict_mem_s₀`, `repLeftVert_mem_s₀`, `repLeftArc_mem_s₀`
- **Used by**: `repCanon_mem_fd`
- **Visibility**: public
- **Lines**: 73-79
- **Notes**: none

### `theorem repCanon_mem_fd`
- **Type**: `{p : ℍ} (hp : p ∈ repCanon f hf) : p ∈ 𝒟`
- **What**: Every element of `repCanon` lies in the fundamental domain `𝒟`.
- **How**: `s₀FM_mem_fd f hf p (repCanon_mem_s₀ f hf hp)`.
- **Hypotheses**: `p ∈ repCanon f hf`.
- **Uses from project**: `repCanon`, `s₀FM_mem_fd`, `repCanon_mem_s₀`
- **Used by**: `injOn_c_eq_zero`, `orb_injOn_repCanon`
- **Visibility**: public
- **Lines**: 82-83
- **Notes**: none

### `theorem repCanon_ne_elliptic`
- **Type**: `(p : ℍ) (hp : p ∈ repCanon f hf) : p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne'`
- **What**: Elements of `repCanon` are distinct from all three elliptic points `i`, `ρ`, `ρ+1`.
- **How**: Three cases on `Finset.mem_union`. **Strict**: direct conjuncts from filter. **Left vertical** (re = -1/2): `i` has re=0 (contradiction), `ρ` has norm=1 (but `‖p‖>1`), `ρ+1` has re=1/2 (contradiction with re=-1/2). **Left arc** (‖p‖=1, re<0): `i` has re=0, `ρ+1` has re=1/2, and the `ρ` case is built into the filter.
- **Hypotheses**: `p ∈ repCanon f hf`.
- **Uses from project**: `repCanon`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `ellipticPointRho_norm`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 88-116
- **Notes**: >10 lines

### `theorem disjoint_repStrict_repLeftVert`
- **Type**: `: Disjoint (repStrict f hf) (repLeftVert f hf)`
- **What**: `repStrict` and `repLeftVert` are disjoint Finsets.
- **How**: `Finset.disjoint_left.mpr`; in strict `|re| < 1/2`, in left-vert `re = -1/2`, so `|−1/2| < 1/2` is contradicted via `norm_num`.
- **Hypotheses**: implicit.
- **Uses from project**: `repStrict`, `repLeftVert`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 121-126
- **Notes**: none

### `theorem disjoint_union_repLeftArc`
- **Type**: `: Disjoint (repStrict f hf ∪ repLeftVert f hf) (repLeftArc f hf)`
- **What**: The union `repStrict ∪ repLeftVert` is disjoint from `repLeftArc`.
- **How**: `Finset.disjoint_left.mpr`; in left arc `‖p‖ = 1`, in strict or left-vert `‖p‖ > 1`; contradiction via `linarith`.
- **Hypotheses**: implicit.
- **Uses from project**: `repStrict`, `repLeftVert`, `repLeftArc`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 129-138
- **Notes**: none

### `lemma uhp_norm_one_re_zero_eq_i`
- **Type**: `(p : ℍ) (hn : ‖(p:ℂ)‖ = 1) (hr : (p:ℂ).re = 0) : p = ellipticPointI'`
- **What**: If `p ∈ ℍ` has norm 1 and re = 0, then `p = i`.
- **How**: From `normSq = 1` and `re = 0`, deduce `im² = 1`; case-split on the factorization `(im-1)(im+1) = 0`; use `p.2 > 0` to rule out `im = -1`. Then `Complex.ext`.
- **Hypotheses**: `‖p‖ = 1`, `p.re = 0`.
- **Uses from project**: `ellipticPointI'`
- **Used by**: `exists_repCanon_of_nonEllOrbit`
- **Visibility**: private
- **Lines**: 142-154
- **Notes**: >10 lines

### `lemma case_right_vertical_via_tInv`
- **Type**: `(q : NonEllOrbitFM) (p0 : ℍ) (hp0_fd : p0 ∈ 𝒟) (hp0_ord : orderOfVanishingAt' f p0 ≠ 0) (h_half : (p0:ℂ).re = 1/2) (h_gt : ‖(p0:ℂ)‖ > 1) (hp0_orb : orbFM p0 = q.val) : ∃ p1 ∈ repCanon f hf, orbFM p1 = q.val`
- **What**: From a representative `p0` on the *right* vertical edge `re = 1/2`, apply `T⁻¹` (`(−1) +ᵥ p0`) to get a representative `p1` on the left vertical edge.
- **How**: `p1 := (-1 : ℝ) +ᵥ p0`. Order preserved (`ord_vAdd_neg_one_eqFM`); FD membership via `vAdd_neg_one_mem_fd_of_right_vertFM`; `re = -1/2` via `vAdd_neg_one_coeFM`; norm preserved via `vAdd_neg_one_norm_eq_of_re_halfFM`; orbit preserved via `orb_vAdd_neg_one_eq`. Witness via `Or.inl (Or.inr ...)` in the union.
- **Hypotheses**: `p0 ∈ 𝒟`, `ord f p0 ≠ 0`, `(p0).re = 1/2`, `‖p0‖ > 1`, `orbFM p0 = q.val`.
- **Uses from project**: `NonEllOrbitFM`, `orderOfVanishingAt'`, `orbFM`, `ord_vAdd_neg_one_eqFM`, `s₀FM_complete`, `s₀FM`, `vAdd_neg_one_mem_fd_of_right_vertFM`, `vAdd_neg_one_coeFM`, `vAdd_neg_one_norm_eq_of_re_halfFM`, `orb_vAdd_neg_one_eq`, `repCanon`
- **Used by**: `exists_repCanon_of_nonEllOrbit`
- **Visibility**: private
- **Lines**: 158-175
- **Notes**: >10 lines

### `lemma case_right_arc_via_S`
- **Type**: `(q : NonEllOrbitFM) (p0 : ℍ) (hp0_fd : p0 ∈ 𝒟) (hp0_ord : orderOfVanishingAt' f p0 ≠ 0) (h_norm_eq : ‖(p0:ℂ)‖ = 1) (h_pos : (p0:ℂ).re > 0) (hp0_orb : orbFM p0 = q.val) (hq_ne_rho : orbFM (ellipticPointRho' : ℍ) ≠ q.val) : ∃ p1 ∈ repCanon f hf, orbFM p1 = q.val`
- **What**: From a representative `p0` on the *right* arc `‖p‖ = 1`, `re > 0`, apply `S` to get a representative `p1` on the left arc.
- **How**: `p1 := ModularGroup.S • p0`. Order preserved (`ord_S_eq`); FD membership via `S_smul_mem_fd_of_unitFM`; `re < 0` from `S_smul_re_neg_of_unitFM`; not `ρ` (via orbit non-equality `hq_ne_rho`); orbit preserved via `orb_S_smul_eq`. Witness via `Or.inr (...)`.
- **Hypotheses**: `p0 ∈ 𝒟`, `ord f p0 ≠ 0`, `‖p0‖ = 1`, `(p0).re > 0`, `orbFM p0 = q.val`, orbit ≠ orbit of `ρ`.
- **Uses from project**: `NonEllOrbitFM`, `orderOfVanishingAt'`, `orbFM`, `ord_S_eq`, `s₀FM_complete`, `s₀FM`, `S_smul_mem_fd_of_unitFM`, `S_smul_re_neg_of_unitFM`, `S_smul_norm_of_unitFM`, `orb_S_smul_eq`, `ellipticPointRho'`, `repCanon`
- **Used by**: `exists_repCanon_of_nonEllOrbit`
- **Visibility**: private
- **Lines**: 177-200
- **Notes**: >10 lines

### `theorem exists_repCanon_of_nonEllOrbit`
- **Type**: `: ∀ q : NonEllOrbitFM, ordOrbitFM f q.val ≠ 0 → ∃ p ∈ repCanon f hf, orbFM p = q.val`
- **What**: Every non-elliptic orbit with nonzero order of vanishing has a representative in `repCanon`.
- **How**: Choose any FD representative `p0` (`orbit_has_fd_repFM`). It has nonzero order, lies in `s₀FM`, and is distinct from each elliptic point. Case on `‖p0‖ ≥ 1` (always true in `𝒟`): if `> 1`, case on `|re| < 1/2` vs `= 1/2`: strict → witness directly; `re = -1/2` → witness directly; `re = +1/2` → apply `case_right_vertical_via_tInv`. If `‖p0‖ = 1`, case on sign of `re` (it's nonzero by `uhp_norm_one_re_zero_eq_i`): `< 0` → witness directly; `> 0` → apply `case_right_arc_via_S`. >10 lines.
- **Hypotheses**: `ordOrbitFM f q.val ≠ 0`.
- **Uses from project**: `NonEllOrbitFM`, `ordOrbitFM`, `repCanon`, `orbFM`, `orbit_has_fd_repFM`, `orderOfVanishingAt'`, `ordOrbit_mkFM`, `s₀FM_complete`, `s₀FM`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `orb_rho_plus_one_eq_orb_rhoFM`, `Complex.normSq_eq_norm_sq`, `case_right_vertical_via_tInv`, `case_right_arc_via_S`, `uhp_norm_one_re_zero_eq_i`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 205-248
- **Notes**: >10 lines

### `lemma repCanon_re_lt_half`
- **Type**: `(p : ℍ) (hp : p ∈ repCanon f hf) : p.re < 1/2`
- **What**: Real parts in `repCanon` are strictly less than `1/2`.
- **How**: Three cases by union: strict gives `|re| < 1/2`; left-vert gives `re = -1/2`; left arc gives `re < 0`. All imply `re < 1/2`.
- **Hypotheses**: `p ∈ repCanon f hf`.
- **Uses from project**: `repCanon`, `repLeftVert`, `sLeftVertFM`
- **Used by**: `injOn_c_eq_zero`
- **Visibility**: private
- **Lines**: 253-261
- **Notes**: >10 lines

### `lemma repCanon_norm_one_re_neg`
- **Type**: `(p : ℍ) (hp : p ∈ repCanon f hf) (h_norm : ‖(p:ℂ)‖ = 1) : (p:ℂ).re < 0`
- **What**: An element of `repCanon` on the unit circle has negative real part.
- **How**: Three cases. Strict and left-vert have `‖p‖ > 1` (contradicting `‖p‖ = 1`); only left arc remains, whose filter gives `re < 0`.
- **Hypotheses**: `p ∈ repCanon f hf`, `‖p‖ = 1`.
- **Uses from project**: `repCanon`
- **Used by**: `injOn_c_ne_zero`
- **Visibility**: private
- **Lines**: 264-270
- **Notes**: none

### `lemma denom_formula_general`
- **Type**: `(h : SL(2,ℤ)) (p : ℍ) : UpperHalfPlane.denom h p = ((h:Matrix) 1 0 : ℂ)·p + ((h:Matrix) 1 1 : ℂ)`
- **What**: Concrete formula for `UpperHalfPlane.denom h p` in terms of matrix entries.
- **How**: `simp` on `UpperHalfPlane.denom`, `Matrix.SpecialLinearGroup.toGL`, etc., then `rfl`.
- **Hypotheses**: none.
- **Uses from project**: none (mathlib-only).
- **Used by**: `normSq_denom_expand_general`
- **Visibility**: private
- **Lines**: 272-277
- **Notes**: none

### `lemma normSq_denom_expand_general`
- **Type**: `(h : SL(2,ℤ)) (p : ℍ) : Complex.normSq (denom h p) = c² · normSq p + 2cd · p.re + d²`
- **What**: Expand `|cz + d|²` in real components.
- **How**: Apply `denom_formula_general`; `Complex.normSq_apply`; `ring`.
- **Hypotheses**: none.
- **Uses from project**: `denom_formula_general`
- **Used by**: `normSq_denom_ge_one`, `normSq_eq_one_of_denom_one`
- **Visibility**: private
- **Lines**: 279-288
- **Notes**: none

### `lemma abs_int_cast_eq_one_of_sq_one`
- **Type**: `{c : ℤ} (h : (c:ℝ)² = 1) : |(c:ℝ)| = 1`
- **What**: Squared casted integer = 1 implies `|c| = 1` as reals.
- **How**: `nlinarith` with `sq_abs`, `abs_nonneg`, `sq_nonneg(|c|-1)`.
- **Hypotheses**: `(c:ℝ)² = 1`.
- **Uses from project**: none.
- **Used by**: `normSq_denom_ge_one`, `normSq_eq_one_of_denom_one`
- **Visibility**: private
- **Lines**: 290-292
- **Notes**: none

### `lemma d_mul_linear_nonneg`
- **Type**: `{c d : ℤ} {z : ℍ} (hz : z ∈ 𝒟) (h_c_abs : |(c:ℝ)| = 1) : (d:ℝ) · (2c·z.re + d) ≥ 0`
- **What**: For `z ∈ 𝒟` with `|c| = 1`, the product `d·(2cz.re + d) ≥ 0`.
- **How**: From `|2c·re| ≤ 1` (use `|re| ≤ 1/2`). Case split on `d ≤ 0` vs `d > 0`. For `d = 0` trivial; for `d ≤ -1` and `d ≥ 1`, use `mul_nonneg_iff` and `abs_le`.
- **Hypotheses**: `z ∈ 𝒟`, `|c| = 1`.
- **Uses from project**: none (uses `z ∈ 𝒟` projection only).
- **Used by**: `normSq_denom_ge_one`, `normSq_eq_one_of_denom_one`
- **Visibility**: private
- **Lines**: 294-307
- **Notes**: >10 lines

### `lemma normSq_denom_ge_one`
- **Type**: `(h : SL(2,ℤ)) (z : ℍ) (hz : z ∈ 𝒟) (h_csq : ((h:Matrix) 1 0)² = 1) : Complex.normSq (denom h z) ≥ 1`
- **What**: For `z ∈ 𝒟` and `|c| = 1`, the norm-squared denominator is ≥ 1.
- **How**: Expand via `normSq_denom_expand_general`; substitute `c² = 1` (real cast); `nlinarith` using `z ∈ 𝒟`'s `normSq ≥ 1` and `d_mul_linear_nonneg`.
- **Hypotheses**: `z ∈ 𝒟`, `c² = 1`.
- **Uses from project**: `normSq_denom_expand_general`, `d_mul_linear_nonneg`, `abs_int_cast_eq_one_of_sq_one`
- **Used by**: `injOn_c_ne_zero`
- **Visibility**: private
- **Lines**: 309-315
- **Notes**: none

### `lemma normSq_eq_one_of_denom_one`
- **Type**: `(g : SL(2,ℤ)) (z : ℍ) (hz : z ∈ 𝒟) (h_csq : ((g:Matrix) 1 0)² = 1) (h_denom : Complex.normSq (denom g z) = 1) : Complex.normSq (z:ℂ) = 1`
- **What**: If denominator has norm 1 and `|c| = 1`, then `z` is on the unit circle (`|z| = 1`).
- **How**: Plug `h_denom = 1` into the expansion `1 · normSq z + 2cd · re + d² = 1`; `nlinarith` with the non-negative cross-term `d_mul_linear_nonneg`.
- **Hypotheses**: `z ∈ 𝒟`, `c² = 1`, `normSq(denom) = 1`.
- **Uses from project**: `normSq_denom_expand_general`, `d_mul_linear_nonneg`, `abs_int_cast_eq_one_of_sq_one`
- **Used by**: `injOn_c_ne_zero`
- **Visibility**: private
- **Lines**: 317-325
- **Notes**: none

### `lemma inv_c_sq_eq`
- **Type**: `(g : SL(2,ℤ)) : ((g⁻¹:SL(2,ℤ)).1 1 0)² = ((g:Matrix) 1 0)²`
- **What**: Inverse matrix has `c'` such that `(c')² = c²` (in fact `c' = -c`).
- **How**: `coe_inv` + `adjugate_fin_two`; rewrite `c' = -c`; `ring`.
- **Hypotheses**: none.
- **Uses from project**: none.
- **Used by**: `injOn_c_ne_zero`
- **Visibility**: private
- **Lines**: 327-335
- **Notes**: none

### `lemma c_abs_le_one_of_smul_fd`
- **Type**: `(g : SL(2,ℤ)) (p₁ p₂ : ℍ) (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ 𝒟) (hp₂ : p₂ ∈ 𝒟) : |(g:Matrix) 1 0| ≤ 1`
- **What**: If `g` maps `p₂ ∈ 𝒟` to `p₁ ∈ 𝒟`, then `|c| ≤ 1`. (Classical fact: only finitely many ways to move within `𝒟`.)
- **How**: `by_contra! h_gt`. Get `c² ≥ 4`. Apply `c_mul_im_sq_le_normSq_denom` and `im_smul_eq_div_normSq` to bound `c²·p₂.im²·p₁.im ≤ p₂.im`. Use `p₁.im, p₂.im > 1/2` from `fd_im_gt_halfFM`. `nlinarith`.
- **Hypotheses**: `g • p₂ = p₁`, both `p₁ p₂ ∈ 𝒟`.
- **Uses from project**: `fd_im_gt_halfFM`
- **Used by**: `orb_injOn_repCanon`
- **Visibility**: private
- **Lines**: 337-374
- **Notes**: >10 lines

### `lemma normSq_denom_one_of_im_eq`
- **Type**: `(g : SL(2,ℤ)) (p₁ p₂ : ℍ) (h_smul : g • p₁ = p₂) (h_im : p₁.im = p₂.im) : Complex.normSq (denom g p₁) = 1`
- **What**: If `g` is an isometry of `im` (equal imaginary parts), then `|denom| = 1`.
- **How**: From `im_smul_eq_div_normSq`, get `p₂.im = p₁.im / normSq(denom)`; `eq_div_iff` then `nlinarith`.
- **Hypotheses**: `g • p₁ = p₂`, `p₁.im = p₂.im`.
- **Uses from project**: none (mathlib `ModularGroup.im_smul_eq_div_normSq`).
- **Used by**: `injOn_c_ne_zero`
- **Visibility**: private
- **Lines**: 376-387
- **Notes**: none

### `lemma injOn_c_eq_zero`
- **Type**: `(g : SL(2,ℤ)) (p₁ p₂ : ℍ) (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ repCanon f hf) (hp₂ : p₂ ∈ repCanon f hf) (hc : (g:Matrix) 1 0 = 0) : p₁ = p₂`
- **What**: When `c = 0`, the modular transformation is `T^n` for some `n`, and `n = 0` is forced (so `p₁ = p₂`) by the `re` bounds in `repCanon`.
- **How**: From `c = 0`, `ModularGroup.exists_eq_T_zpow_of_c_eq_zero` gives `g = T^n`; so `p₁.re = p₂.re + n`. Combine `repCanon_re_lt_half` and `(p ∈ 𝒟).2 ⇒ -1/2 ≤ re` to bound `-1 < n < 1`, hence `n = 0` (`omega`).
- **Hypotheses**: `g • p₂ = p₁`, `p₁ p₂ ∈ repCanon`, `c = 0`.
- **Uses from project**: `repCanon`, `repCanon_re_lt_half`, `repCanon_mem_fd`
- **Used by**: `orb_injOn_repCanon`
- **Visibility**: private
- **Lines**: 389-414
- **Notes**: >10 lines

### `lemma injOn_c_ne_zero`
- **Type**: `(g : SL(2,ℤ)) (p₁ p₂ : ℍ) (hg : g • p₂ = p₁) (hp₁ : p₁ ∈ repCanon f hf) (hp₂ : p₂ ∈ repCanon f hf) (hp₁_fd : p₁ ∈ 𝒟) (hp₂_fd : p₂ ∈ 𝒟) (h_c_ne : (g:Matrix) 1 0 ≠ 0) (h_abs_c : |(g:Matrix) 1 0| ≤ 1) : p₁ = p₂`
- **What**: When `c ≠ 0` (so `c² = 1` since `|c| ≤ 1`), both `p₁` and `p₂` must lie on the unit circle with negative real parts, and equal imaginary parts force `p₁ = p₂`.
- **How**: From `|c| ≤ 1` and `c ≠ 0`, get `c² = 1`. Compute `normSq(denom) = p₂.im/p₁.im`. Use `normSq_denom_ge_one` on both `g, g⁻¹` to sandwich the imaginary parts equal. Then `normSq_eq_one_of_denom_one` for both (using `inv_c_sq_eq`) gives both norms `= 1`. With `repCanon_norm_one_re_neg`, both have `re < 0`; combined with `normSq(z) = re² + im² = 1` and `im` equal, get `re` equal. Conclude via `UpperHalfPlane.ext_re_im`.
- **Hypotheses**: `g • p₂ = p₁`, `p₁ p₂ ∈ repCanon ∩ 𝒟`, `c ≠ 0`, `|c| ≤ 1`.
- **Uses from project**: `repCanon`, `repCanon_norm_one_re_neg`, `normSq_denom_ge_one`, `normSq_eq_one_of_denom_one`, `normSq_denom_one_of_im_eq`, `inv_c_sq_eq`
- **Used by**: `orb_injOn_repCanon`
- **Visibility**: private
- **Lines**: 416-457
- **Notes**: >10 lines

### `theorem orb_injOn_repCanon`
- **Type**: `: Set.InjOn orbFM ↑(repCanon f hf)`
- **What**: The orbit map `orbFM` is injective on `repCanon`.
- **How**: From `orbFM p₁ = orbFM p₂`, `Quotient.exact'` gives `g ∈ SL(2,ℤ)` with `g • p₂ = p₁`. Case split on `c = 0` vs `c ≠ 0`; apply `injOn_c_eq_zero` or `injOn_c_ne_zero` (with `c_abs_le_one_of_smul_fd` providing the `|c| ≤ 1` bound in the latter case).
- **Hypotheses**: implicit (just `f`, `hf`).
- **Uses from project**: `repCanon`, `orbFM`, `repCanon_mem_fd`, `injOn_c_eq_zero`, `injOn_c_ne_zero`, `c_abs_le_one_of_smul_fd`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 462-472
- **Notes**: >10 lines

## File Summary

CanonicalReps.lean: 474 lines. Defines canonical representative finsets for non-elliptic orbits of `SL(2,ℤ)` on `ℍ`, used for the orbit sum in the valence formula. The fundamental domain `𝒟` decomposes into the three open subsets: strict interior (`|re| < 1/2`, `‖p‖ > 1`), left vertical edge (`re = -1/2`, `‖p‖ > 1`), and left arc (`‖p‖ = 1`, `re < 0`). The right vertical (`re = +1/2`) and right arc (`re > 0` on unit circle) are excluded; representatives there get mapped by `T⁻¹` or `S` respectively to land in the canonical sets.

Architecture:
1. **Definitions**: `repStrict`, `repLeftVert`, `repLeftArc`, `repCanon = ∪`.
2. **Containment lemmas**: each subset is contained in `s₀FM`; `repCanon ⊆ s₀ ⊆ 𝒟`.
3. **Distinctness**: `repCanon_ne_elliptic` (avoids `i, ρ, ρ+1`).
4. **Disjointness**: pairwise disjoint.
5. **Existence**: `exists_repCanon_of_nonEllOrbit` — every non-elliptic orbit with nonzero order has a representative, via case analysis (strict, left/right vertical edges, left/right arc).
6. **Injectivity**: `orb_injOn_repCanon` — case-split on `c = 0` (forces `T^n` with `n = 0`) vs `c ≠ 0` (forces both on unit circle with equal `im`, hence equal). Helpers compute `|cz+d|²` and reduce to `|c| ≤ 1`.

The mathematical content is a textbook orbit-representative argument adapted to the canonical-edges convention chosen for the valence formula. No sorries, no axioms, no `set_option`s. The file establishes a clean injective parametrization of `NonEllOrbitFM` orbits with nonzero order by `repCanon` elements.
