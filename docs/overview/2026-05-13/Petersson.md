# Petersson.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/Petersson.lean`
Lines: 136

## File Status: ENTIRELY COMMENTED OUT
The whole file is a single block comment `/- … -/`. No declarations are exported.

Below is the inventory of declarations as **drafted** in the comment block (useful for understanding intent and downstream re-enablement), each marked as commented-out.

## def/`UpperHalfPlane.petersson` (commented)
- **Type**: `(k : ℤ) → (f f' : ℍ → ℂ) → ℍ → ℂ`
- **What**: Petersson scalar-product integrand: `τ ↦ conj (f τ) · f' τ · τ.im ^ k`.
- **How**: Direct definition `conj (f τ) * f' τ * τ.im ^ k`.
- **Hypotheses**: None.
- **Uses-from-project**: `QExpansion` (imported, but no symbols used here).
- **Used by**: `petersson_continuous`, `petersson_slash`, `petersson_slash_SL`, the four `IsZeroAtImInfty.petersson_*` lemmas, `SlashInvariantFormClass.petersson_smul`, `ModularFormClass.petersson_continuous` (all commented).
- **Visibility**: would be public; currently commented out
- **Lines**: 27–28

## lemma/`UpperHalfPlane.petersson_continuous` (commented)
- **Type**: `(k : ℤ) → Continuous f → Continuous f' → Continuous (petersson k f f')`
- **What**: Continuity of the Petersson integrand from continuity of `f`, `f'`.
- **How**: Two `Continuous.mul` reductions; `Complex.continuous_conj.comp`; `Complex.continuous_ofReal.comp continuous_im`'s `zpow₀` (with `τ.im_ne_zero`).
- **Hypotheses**: `Continuous f`, `Continuous f'`.
- **Uses-from-project**: `petersson`.
- **Used by**: `ModularFormClass.petersson_continuous` (commented).
- **Visibility**: would be public; commented out
- **Lines**: 30–35

## lemma/`UpperHalfPlane.petersson_slash` (commented)
- **Type**: For `g : GL(2, ℝ)` with `0 < det g`, `petersson k (f ∣[k] g) (f' ∣[k] g) τ = (det g)^(k-2) · petersson k f f' (g • τ)`.
- **What**: Transformation law of the Petersson integrand under a `g ∈ GL(2,ℝ)⁺`.
- **How**: 4-step `calc`: unfold `slash_def` (with `σ g = id` from positivity), expand `conj·` over factors using `normSq_eq_conj_mul_self` and `zpow_add₀ hD`, rearrange to expose `(D·τ.im/j.normSq)^k`, and identify with `im (g • τ)` via `im_smul_eq_div_normSq` + `abs_of_pos hg`.
- **Hypotheses**: `0 < g.val.det`.
- **Uses-from-project**: `petersson`.
- **Used by**: `petersson_slash_SL` (commented).
- **Visibility**: would be public; commented out
- **Lines**: 38–58
- **Notes**: Comment marks a TODO to generalize after mathlib PR #24830 merges.

## lemma/`UpperHalfPlane.petersson_slash_SL` (commented)
- **Type**: For `g : SL(2, ℤ)`, `petersson k (f ∣[k] g) (f' ∣[k] g) τ = petersson k f f' (g • τ)`.
- **What**: SL-invariance specialization.
- **How**: Two `ModularForm.SL_slash` rewrites; apply `petersson_slash`; close determinant side conditions via `Matrix.SpecialLinearGroup.det_coe`.
- **Hypotheses**: None beyond ambient.
- **Uses-from-project**: `petersson_slash`, `petersson`.
- **Used by**: `SlashInvariantFormClass.petersson_smul` (commented).
- **Visibility**: would be public; commented out
- **Lines**: 60–64

## lemma/`IsZeroAtImInfty.petersson_exp_decay_left` (commented)
- **Type**: For modular forms `f` (with `IsZeroAtImInfty f`) and `f'` of same weight `k` on `Γ`, `∃ a > 0, petersson k f f' =O[atImInfty] (τ ↦ exp(-a · im τ))`.
- **What**: Exponential decay of Petersson at the cusp when one factor is a cusp form.
- **How**: Use `h_bd.exp_decay_atImInfty` (rate `b`) and `ModularFormClass.bdd_at_infty f' 1` to bound the other factor; pick `a ∈ (0, b)`; reduce the `IsBigO` via norm-manipulation; final step compares `t^k · exp(-b t)` with `exp(-a t)` using `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`.
- **Hypotheses**: `Γ.FiniteIndex`; `IsZeroAtImInfty f`.
- **Uses-from-project**: `petersson`.
- **Used by**: `IsZeroAtImInfty.petersson_exp_decay_right`, `IsZeroAtImInfty.petersson_isZeroAtImInfty_left` (commented).
- **Visibility**: would be public; commented out
- **Lines**: 68–87

## lemma/`IsZeroAtImInfty.petersson_exp_decay_right` (commented)
- **Type**: As `_left` but with `IsZeroAtImInfty f'`.
- **What**: Symmetric version — decay when the *right* factor vanishes at infinity.
- **How**: Reduce to `_left` by swapping factors using `congr_left` and `mul_comm` after `isBigO_norm_left`.
- **Hypotheses**: `Γ.FiniteIndex`; `IsZeroAtImInfty f'`.
- **Uses-from-project**: `petersson`, `petersson_exp_decay_left`.
- **Used by**: `petersson_isZeroAtImInfty_right` (commented).
- **Visibility**: would be public; commented out
- **Lines**: 91–100

## lemma/`IsZeroAtImInfty.petersson_isZeroAtImInfty_left` (commented)
- **Type**: `IsZeroAtImInfty f → IsZeroAtImInfty (petersson k f f')`.
- **What**: Petersson vanishes at infinity when `f` does.
- **How**: Compose `petersson_exp_decay_left` with `Real.tendsto_exp_atBot` along `tendsto_id.const_mul_atTop_of_neg` of `-a`.
- **Hypotheses**: as in `_left`.
- **Uses-from-project**: `petersson_exp_decay_left`.
- **Used by**: None (would feed Petersson inner-product convergence).
- **Visibility**: would be public; commented out
- **Lines**: 102–109

## lemma/`IsZeroAtImInfty.petersson_isZeroAtImInfty_right` (commented)
- **Type**: As above but for `f'`.
- **What**: Symmetric vanishing.
- **How**: As `_left` but via `petersson_exp_decay_right`.
- **Hypotheses**: as in `_right`.
- **Uses-from-project**: `petersson_exp_decay_right`.
- **Used by**: None.
- **Visibility**: would be public; commented out
- **Lines**: 111–118

## lemma/`SlashInvariantFormClass.petersson_smul` (commented)
- **Type**: For `g ∈ Γ`, `petersson k f f' (g • τ) = petersson k f f' τ`.
- **What**: Γ-invariance of Petersson on SlashInvariantForm classes.
- **How**: Combine `petersson_slash_SL` (symmetric) with `SlashInvariantFormClass.slash_action_eq` (slash by `g ∈ Γ` is identity).
- **Hypotheses**: `g ∈ Γ`.
- **Uses-from-project**: `petersson_slash_SL`.
- **Used by**: None.
- **Visibility**: would be public; commented out
- **Lines**: 122–128

## lemma/`ModularFormClass.petersson_continuous` (commented)
- **Type**: `(k : ℤ) (Γ : Subgroup SL(2,ℤ)) (f : F) (f' : F') → Continuous (petersson k f f')`.
- **What**: Continuity of the Petersson integrand for modular forms.
- **How**: `UpperHalfPlane.petersson_continuous` with continuity supplied by `(ModularFormClass.holo _).continuous` on each factor.
- **Hypotheses**: `ModularFormClass F Γ k`, `ModularFormClass F' Γ k`.
- **Uses-from-project**: `petersson_continuous`.
- **Used by**: None.
- **Visibility**: would be public; commented out
- **Lines**: 130–135

## File Summary
**Entire file is commented out** (single block comment from line 1 to line 137). The intended content was a draft Petersson scalar-product integrand `petersson k f f' = conj(f) · f' · τ.im^k` together with its slash transformation (`petersson_slash`), SL-invariance (`petersson_slash_SL`, `petersson_smul`), continuity, and exponential decay/vanishing at the cusp when one of `f`, `f'` is a cusp form. The slash lemma carries a TODO note tied to mathlib PR #24830. Currently inert in the build.
