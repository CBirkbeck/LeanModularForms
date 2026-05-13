# QExpansion.lean Inventory

## File-level note

The **entire file body is wrapped in a single block comment** `/- ... -/` (lines 1-265). The opening line `/- /-` and closing line `-/` on line 264 form a single outer comment that disables all declarations. Consequently, **no Lean declarations are actually elaborated**: the file contributes nothing to the build. Below are the declarations that *would* be present if the comment were removed; each entry reflects the textual content of the file but the visibility is effectively "commented-out / inactive".

### `lemma Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable`
- **Type**: `(h0 : 0 < R) (n : ℕ) (hs : s.Countable) (hc : ContinuousOn f (closedBall c R)) (hd : ∀ z ∈ ball c R \ s, DifferentiableAt ℂ f z) : (∮ z in C(c, R), (1 / (z - c) ^ (n+1)) • f z) = (2 * π * I / n.factorial) • iteratedDeriv n f c`
- **What**: Cauchy integral formula for higher derivatives at the central point, in its most general form (differentiability off a countable set).
- **How**: Uses `hasFPowerSeriesOnBall_of_differentiable_off_countable (R := ⟨R, h0.le⟩) hs hc hd h0 |>.factorial_smul 1 n`, rewrites via `iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod`, `Finset.prod_const_one`, `one_smul`; then `cauchyPowerSeries_apply`, `Nat.cast_smul_eq_nsmul ℂ`, two `mul_smul`s, `div_mul_cancel₀ _ (mod_cast n.factorial_ne_zero)`, `mul_inv_cancel₀ two_pi_I_ne_zero`, `one_smul`, and finishes with `simp [← mul_smul, pow_succ, mul_comm]`.
- **Hypotheses**: `0 < R`, countability of the bad set, continuity on the closed ball, differentiability off the countable set inside the open ball.
- **Uses from project**: []  (pure mathlib lemma intended for upstreaming).
- **Used by**: `DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul`, indirectly `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul` and `qExpansion_coeff_eq_circleIntegral`.
- **Visibility**: would be public (`lemma`), but commented out.
- **Lines**: 55-65 (inside outer block comment).
- **Notes**: Mathlib-style auxiliary; sits in a `section Cauchy` with `variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]`.

### `lemma DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul`
- **Type**: `(h0 : 0 < R) (n : ℕ) (hc : DiffContOnCl ℂ f (ball c R)) : (∮ z in C(c, R), (1 / (z - c) ^ (n+1)) • f z) = (2 * π * I / n.factorial) • iteratedDeriv n f c`
- **What**: Cauchy formula for higher derivatives assuming differentiability on the open ball and continuity on its closure.
- **How**: Delegates to `Complex.circleIntegral_one_div_sub_center_pow_smul_of_differentiable_on_off_countable` with `s := ∅`: `Set.countable_empty`, `hc.continuousOn_ball`, `fun _ hx ↦ hc.differentiableAt isOpen_ball hx.1`.
- **Hypotheses**: `0 < R`, `DiffContOnCl ℂ f (ball c R)`.
- **Uses from project**: []
- **Used by**: `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`.
- **Visibility**: would be public, but commented out.
- **Lines**: 69-74.
- **Notes**: Specialisation to empty exceptional set.

### `lemma DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul`
- **Type**: `(h0 : 0 < R) (n : ℕ) (hc : DifferentiableOn ℂ f (closedBall c R)) : (∮ z in C(c, R), (1 / (z - c) ^ (n+1)) • f z) = (2 * π * I / n.factorial) • iteratedDeriv n f c`
- **What**: Cauchy formula assuming differentiability on the closed ball.
- **How**: `(hc.mono closure_ball_subset_closedBall).diffContOnCl |>.circleIntegral_one_div_sub_center_pow_smul h0 n`.
- **Hypotheses**: `0 < R`, `DifferentiableOn ℂ f (closedBall c R)`.
- **Uses from project**: []
- **Used by**: `qExpansion_coeff_eq_circleIntegral`.
- **Visibility**: would be public, but commented out.
- **Lines**: 78-83.
- **Notes**: Most ergonomic form for modular-form applications.

### `theorem SlashInvariantFormClass.periodic_comp_ofComplex'`
- **Type**: `(hΓ : Γ.width ∣ h) : Periodic (f ∘ ofComplex) h`
- **What**: For a slash-invariant form `f` of level `Γ`, composition `f ∘ ofComplex : ℂ → ℂ` is periodic with period `h`, provided the cusp width of `Γ` divides `h`.
- **How**: `intro w`; split on `0 < im w`. Positive case: derives `0 < im (w + h)`, simps `ofComplex_apply_of_im_pos` on both `w + h` and `w`, then rewrites by `← vAdd_width_periodic f k (Nat.cast_dvd_cast hΓ) ⟨w, hw⟩` and closes via `UpperHalfPlane.ext_iff`, `add_comm`. Non-positive case: both invocations of `ofComplex` land in the `≤ 0` branch, so the goal reduces immediately.
- **Hypotheses**: `[SlashInvariantFormClass F Γ k]`, `Γ.width ∣ h`.
- **Uses from project**: `LeanModularForms.ForMathlib.Identities` (provides `vAdd_width_periodic`).
- **Used by**: `eq_cuspFunction'`, `differentiableAt_cuspFunction'`, `exp_decay_atImInfty_of_width_dvd`.
- **Visibility**: would be public, but commented out.
- **Lines**: 104-114.
- **Notes**: Has `include hF` for the slash-invariant typeclass.

### `theorem SlashInvariantFormClass.eq_cuspFunction'`
- **Type**: `{τ : ℍ} [NeZero h] (hΓ : Γ.width ∣ h) : cuspFunction h f (𝕢 h τ) = f τ`
- **What**: The cusp function evaluated at the `q`-parameter of `τ` recovers `f τ`.
- **How**: `simpa using (periodic_comp_ofComplex' f hΓ).eq_cuspFunction (NeZero.ne _) τ`.
- **Hypotheses**: `[SlashInvariantFormClass F Γ k]`, `[NeZero h]`, `Γ.width ∣ h`.
- **Uses from project**: `periodic_comp_ofComplex'` (this file).
- **Used by**: `qExpansion_coeff_eq_intervalIntegral`.
- **Visibility**: would be public, but commented out.
- **Lines**: 116-118.
- **Notes**: Direct reuse of mathlib's `Periodic.eq_cuspFunction`.

### `theorem ModularFormClass.differentiableAt_cuspFunction'`
- **Type**: `(hq : ‖q‖ < 1) : DifferentiableAt ℂ (cuspFunction h f) q`
- **What**: When `f` is a modular form, its cusp function is differentiable on the open unit disc (including at 0).
- **How**: Sets `npos : 0 < (h : ℝ)` via `Nat.pos_iff_ne_zero.mpr (NeZero.ne _)`. Case-splits on `q = 0`: at `q = 0` uses `Periodic.differentiableAt_cuspFunction_zero` together with `bounded_at_infty_comp_ofComplex f` and `eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0)) (fun _ ↦ differentiableAt_comp_ofComplex f)`. At `q ≠ 0` rewrites via `Periodic.qParam_right_inv npos.ne' hq'` and applies `Periodic.differentiableAt_cuspFunction` together with `differentiableAt_comp_ofComplex` and `Periodic.im_invQParam_pos_of_norm_lt_one`.
- **Hypotheses**: `[ModularFormClass F Γ k]`, `[NeZero h]`, `Γ.width ∣ h`, `‖q‖ < 1`.
- **Uses from project**: `periodic_comp_ofComplex'` (this file).
- **Used by**: `qExpansion_coeff_eq_circleIntegral`.
- **Visibility**: would be public, but commented out.
- **Lines**: 138-148.
- **Notes**: Has `include hF` and `include hΓ` blocks.

### `lemma ModularFormClass.qExpansion_coeff_eq_circleIntegral`
- **Type**: `(n : ℕ) {R : ℝ} (hR : 0 < R) (hR' : R < 1) : (qExpansion h f).coeff n = ((2 * π * I)⁻¹ * ∮ z in C(0, R), cuspFunction h f z / z ^ (n+1))`
- **What**: The `q`-expansion coefficient as a contour integral on a circle of radius `R < 1`.
- **How**: Builds `DifferentiableOn ℂ (cuspFunction h f) (Metric.closedBall 0 R)` from `differentiableAt_cuspFunction'`, applies `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul hR n`, then rewrites by `smul_eq_mul`, `div_eq_mul_inv`, `mul_assoc`, `mul_comm`, `← div_eq_iff two_pi_I_ne_zero`. Concludes via `simp_rw [qExpansion, PowerSeries.coeff_mk, ← this, sub_zero, smul_eq_mul, one_div_mul_eq_div, div_eq_inv_mul]`.
- **Hypotheses**: `[ModularFormClass F Γ k]`, `[NeZero h]`, `Γ.width ∣ h`, `0 < R < 1`.
- **Uses from project**: `differentiableAt_cuspFunction'` (this file); `DifferentiableOn.circleIntegral_one_div_sub_center_pow_smul` (this file).
- **Used by**: `qExpansion_coeff_eq_intervalIntegral`.
- **Visibility**: would be public, but commented out.
- **Lines**: 155-164.
- **Notes**: Cauchy formula applied to the cusp function.

### `lemma ModularFormClass.qExpansion_coeff_eq_intervalIntegral`
- **Type**: `(n : ℕ) {t : ℝ} (ht : 0 < t) : (qExpansion h f).coeff n = 1 / h * ∫ u in 0..h, 1 / 𝕢 h (u + t * I) ^ n * f (⟨u + t * I, _⟩)`
- **What**: The `q`-expansion coefficient as an interval integral along the horizontal line `Im z = t` in the upper half-plane.
- **How**: Sets `R := Real.exp (-2 * π * t / h)`, derives `0 < R` (from `Real.exp_pos`) and `R < 1` (from `Real.exp_lt_one_iff.mpr` plus `div_pos (by positivity) (mod_cast Nat.pos_of_neZero h)`). Applies `qExpansion_coeff_eq_circleIntegral f hΓ n hR0 hR1`, unfolds `circleIntegral`, rewrites `2 * π = h * (2 * π / h)` (cleared by `field_simp [NeZero.ne]`). Reparameterises via `← intervalIntegral.smul_integral_comp_mul_right`, `real_smul`, `← mul_assoc`, `← intervalIntegral.integral_const_mul`. Identifies `circleMap 0 R (u * (2π/h)) = 𝕢 h τ` for `τ := ⟨u + t*I, ...⟩` by `simp only [circleMap, ofReal_exp, ← exp_add, zero_add]; push_cast; ring_nf; rw [I_sq]; ring_nf`. Finishes with `simp_rw [deriv_circleMap, this, ..., eq_cuspFunction' _ hΓ, smul_eq_mul, pow_succ]`, then `ring_nf`, `field_simp [(show 𝕢 h τ ≠ 0 from Complex.exp_ne_zero _), Real.pi_ne_zero, NeZero.ne]`, and a second `ring_nf`.
- **Hypotheses**: `[ModularFormClass F Γ k]`, `[NeZero h]`, `Γ.width ∣ h`, `0 < t`.
- **Uses from project**: `qExpansion_coeff_eq_circleIntegral`, `eq_cuspFunction'` (this file).
- **Used by**: (no in-file users; intended public API).
- **Visibility**: would be public, but commented out.
- **Lines**: 169-199.
- **Notes**: Proof >30 lines. Contains an interesting comment `-- why do we need to do ring_nf twice here?`.

### `lemma UpperHalfPlane.IsZeroAtImInfty.zeroAtFilter_comp_ofComplex`
- **Type**: `{α : Type*} [Zero α] [TopologicalSpace α] {f : ℍ → α} (hf : IsZeroAtImInfty f) : ZeroAtFilter I∞ (f ∘ ofComplex)`
- **What**: Vanishing at the imaginary infinity cusp pulled back along `ofComplex`.
- **How**: `simpa using hf.comp tendsto_comap_im_ofComplex`.
- **Hypotheses**: vanishing at `atImInfty`.
- **Uses from project**: []
- **Used by**: `cuspFunction_apply_zero`, `exp_decay_atImInfty_of_width_dvd`.
- **Visibility**: would be public, but commented out.
- **Lines**: 209-211.
- **Notes**: Has `variable {f}` reset.

### `theorem UpperHalfPlane.IsZeroAtImInfty.cuspFunction_apply_zero`
- **Type**: `[NeZero h] (hf : IsZeroAtImInfty f) : cuspFunction h f 0 = 0`
- **What**: A modular form vanishing at `i∞` has `cuspFunction h f 0 = 0`.
- **How**: `Periodic.cuspFunction_zero_of_zero_at_inf (mod_cast (Nat.pos_iff_ne_zero.mpr (NeZero.ne _))) hf.zeroAtFilter_comp_ofComplex`.
- **Hypotheses**: `[NeZero h]`, `IsZeroAtImInfty f`.
- **Uses from project**: `zeroAtFilter_comp_ofComplex` (this file).
- **Used by**: (no in-file users).
- **Visibility**: would be public, but commented out.
- **Lines**: 213-216.
- **Notes**: Bridge from `IsZeroAtImInfty` to `cuspFunction 0 = 0`.

### `theorem UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty_of_width_dvd`
- **Type**: `[ModularFormClass F Γ k] (hf : IsZeroAtImInfty f) (hΓ : Γ.width ∣ h) : f =O[atImInfty] fun τ ↦ Real.exp (-2 * π * τ.im / h)`
- **What**: A modular form vanishing at `i∞` decays at least as fast as `exp(-2π τ.im / h)` whenever `h` is divisible by the cusp width.
- **How**: Case-split `h = 0` (then `Real.exp_zero` and the goal reduces to `f =O[atImInfty] 1`, settled by `hf.isBoundedAtImInfty`). Otherwise `haveI : NeZero h := ⟨hΓ'⟩` then `simpa [comp_def] using ((periodic_comp_ofComplex' f hΓ).exp_decay_of_zero_at_inf (mod_cast …) (eventually_of_mem (preimage_mem_comap (Ioi_mem_atTop 0)) fun _ ↦ differentiableAt_comp_ofComplex f) hf.zeroAtFilter_comp_ofComplex).comp_tendsto tendsto_coe_atImInfty`.
- **Hypotheses**: `[ModularFormClass F Γ k]`, `IsZeroAtImInfty f`, `Γ.width ∣ h`.
- **Uses from project**: `periodic_comp_ofComplex'`, `zeroAtFilter_comp_ofComplex` (this file).
- **Used by**: `exp_decay_atImInfty`.
- **Visibility**: would be public, but commented out.
- **Lines**: 222-236.
- **Notes**: Uses `mathlib`'s `Periodic.exp_decay_of_zero_at_inf` for the analytic core.

### `theorem UpperHalfPlane.IsZeroAtImInfty.exp_decay_atImInfty`
- **Type**: `[ModularFormClass F Γ k] (hf : IsZeroAtImInfty f) [Γ.FiniteIndex] : ∃ a, 0 < a ∧ f =O[atImInfty] fun τ ↦ Real.exp (-a * τ.im)`
- **What**: For modular forms vanishing at `i∞` on a finite-index `Γ`, exponential decay with rate `a = 2π/Γ.width`.
- **How**: Uses `Γ.width_ne_zero` and `NeZero.mk` to bring both bundled and unbundled forms into scope. Sets `a := 2 * π / Γ.width`, `positivity` for `0 < a`. Applies `hf.exp_decay_atImInfty_of_width_dvd dvd_rfl` and `convert … using 3`, closes by `ring`.
- **Hypotheses**: `[ModularFormClass F Γ k]`, `IsZeroAtImInfty f`, `[Γ.FiniteIndex]`.
- **Uses from project**: `exp_decay_atImInfty_of_width_dvd` (this file).
- **Used by**: `exp_decay_atImInfty_translate`.
- **Visibility**: would be public, but commented out.
- **Lines**: 239-245.
- **Notes**: Concrete decay rate `2π/width`.

### `theorem CuspFormClass.exp_decay_atImInfty_translate`
- **Type**: `[Γ.FiniteIndex] (γ : SL(2, ℤ)) : ∃ a, 0 < a ∧ (f ∣[k] γ) =O[atImInfty] fun τ ↦ Real.exp (-a * τ.im)`
- **What**: For cuspidal `f`, every `SL(2,ℤ)`-translate of `f` has exponential decay at the corresponding cusp.
- **How**: `have hf : IsZeroAtImInfty (CuspForm.translate f γ) := CuspFormClass.zero_at_infty f γ`; `suffices (Γ.map <| MulAut.conj γ⁻¹).FiniteIndex from hf.exp_decay_atImInfty`. The remaining `FiniteIndex` proved by `constructor; rw [Γ.index_map_of_bijective (EquivLike.bijective _)]; apply Subgroup.FiniteIndex.index_ne_zero`.
- **Hypotheses**: `[CuspFormClass F Γ k]`, `[Γ.FiniteIndex]`.
- **Uses from project**: `exp_decay_atImInfty` (this file).
- **Used by**: (no in-file users).
- **Visibility**: would be public, but commented out.
- **Lines**: 255-261.
- **Notes**: Has `include hF`. Final consequence of the exponential decay chain.

## File Summary

- **Total decls**: 13 declarations (all inside an outer block comment — none elaborated).
- **Key API** (used 3+ in this file textually): `periodic_comp_ofComplex'` (used by `eq_cuspFunction'`, `differentiableAt_cuspFunction'`, `exp_decay_atImInfty_of_width_dvd` — 3 uses).
- **Unused in file**: `cuspFunction_apply_zero`, `qExpansion_coeff_eq_intervalIntegral`, `exp_decay_atImInfty_translate` have no in-file callers (they are terminal public API).
- **Sorries**: 0 (file is fully commented out, so no live declarations).
- **set_options**: none.
- **Proofs >30 lines**: `qExpansion_coeff_eq_intervalIntegral` (~30 lines including the `circleMap = 𝕢 h τ` sub-proof).
- **One-paragraph file purpose**: This file is **entirely commented out** with a single outer `/- ... -/` block (lines 1-265). When uncommented, it would define `q`-expansions of modular forms in the style of David Loeffler's mathlib draft: for a slash-invariant form `f`, the cusp function `F` such that `f τ = F(exp(2πi τ / h))` is shown to be differentiable on the open unit disc (`differentiableAt_cuspFunction'`); the `q`-expansion coefficient is expressed both as a circle integral (`qExpansion_coeff_eq_circleIntegral`) and as a horizontal interval integral (`qExpansion_coeff_eq_intervalIntegral`); cusp forms are shown to decay exponentially at `i∞` (`exp_decay_atImInfty_of_width_dvd`, `exp_decay_atImInfty`) with rate `2π/Γ.width`, and this decay generalises to every `SL₂(ℤ)`-translate. The file also contains three preliminary mathlib-style Cauchy-integral-formula lemmas (`circleIntegral_one_div_sub_center_pow_smul_*`) that are independent of modular-form theory and would naturally upstream into `Mathlib.Analysis.Complex.CauchyIntegral`. Because the whole file is commented, it currently has no effect on the build; it is presumably staged for a later mathlib PR.
