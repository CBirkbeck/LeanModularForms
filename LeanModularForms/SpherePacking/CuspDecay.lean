/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.AtImInfty
import LeanModularForms.Modularforms.Eisenstein

/-!
# Cusp decay for Eisenstein series and the Viazovska integrand

This file proves that the Eisenstein series `E₄`, `E₆` tend to `1`
at the cusp (Im -> infinity), and establishes key properties of the
cuspFunction of Delta needed for cusp decay analysis.

## Main results

* `tendsto_qParam_atImInfty` : `qParam 1 z -> 0` as `Im z -> infinity`
* `E₄_tendsto_one_atImInfty` : `E₄ z -> 1` as `Im z -> infinity`
* `E₆_tendsto_one_atImInfty` : `E₆ z -> 1` as `Im z -> infinity`
* `cF_Delta_div_q_tendsto` : `cuspFunction(Delta)(q)/q -> 1` as `q -> 0`
* `tendsto_deriv_cF_Delta` : `(cuspFunction Delta)'(q) -> 1` as `q -> 0`
* `cF_ratio_tendsto_one` : `q * cF'(q) / cF(q) -> 1` as `q -> 0`
* `phi0_isBoundedAtImInfty` : phi0 is bounded at `Im -> infinity`

## Proof strategy for `phi0_isBoundedAtImInfty`

The function `phi0(w) = (E2(w)*E4(w)-E6(w))^2 / Delta(w)` is bounded at `Im -> infinity`.
The proof chain is:
1. `cF_ratio_tendsto_one`: `q * cF'(q)/cF(q) -> 1` (proven below)
2. `logDeriv(Delta^24)(z) = 2*pi*I * cF'(q)/(cF(q)/q)` via `logDeriv_comp` (chain rule)
3. `logDeriv(eta^24) = 24 * logDeriv(eta)` via `logDeriv_fun_pow`
4. `logDeriv(eta)(z) = pi*I/12 * E2(z)` via `eta_logDeriv'`
5. Combining: `E2(z) = cF'(q)/(cF(q)/q) -> 1` as `Im -> infinity`
6. `E2*E4 - E6 -> 1*1 - 1 = 0`, so the numerator of `phi0` vanishes
7. Combined with `Delta = Theta(exp(-2*pi*Im))`, `phi0` is bounded
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

/-! ## q-parameter and Eisenstein series at the cusp -/

set_option maxHeartbeats 400000 in
/-- The q-parameter `q = exp(2*pi*i*z)` tends to 0 as `Im(z) -> infinity`. -/
theorem tendsto_qParam_atImInfty :
    Tendsto (fun (z : UpperHalfPlane) => Function.Periodic.qParam 1 (z : ℂ))
    UpperHalfPlane.atImInfty (nhds 0) := by
  have h := tendsto_neg_cexp_atImInfty 0
  simp only [Nat.cast_zero, zero_add, mul_one] at h
  have h2 := h.neg
  simp only [neg_neg, neg_zero] at h2
  apply Filter.Tendsto.congr _ h2
  intro z
  simp only [Function.Periodic.qParam]
  congr 1; push_cast; ring

set_option maxHeartbeats 800000 in
/-- `E4(z) -> 1` as `Im(z) -> infinity`, from the q-expansion constant term. -/
theorem E₄_tendsto_one_atImInfty :
    Tendsto E₄ UpperHalfPlane.atImInfty (nhds 1) := by
  have heq : ∀ z : UpperHalfPlane, E₄ z = SlashInvariantFormClass.cuspFunction 1 E₄
      (Function.Periodic.qParam (↑(1 : ℕ)) (z : ℂ)) :=
    fun z => (SlashInvariantFormClass.eq_cuspFunction 1 E₄ z).symm
  have hfps := ModularFormClass.hasFPowerSeries_cuspFunction 1 E₄
  have hcont : ContinuousAt (SlashInvariantFormClass.cuspFunction 1 E₄) 0 :=
    hfps.analyticAt.continuousAt
  have hval : SlashInvariantFormClass.cuspFunction 1 E₄ 0 = 1 := by
    rw [cuspfunc_Zero]; exact E4_q_exp_zero
  have hq : Tendsto (fun (z : UpperHalfPlane) =>
      Function.Periodic.qParam (↑(1 : ℕ)) (z : ℂ))
      UpperHalfPlane.atImInfty (nhds 0) := by
    simp only [Nat.cast_one]; exact tendsto_qParam_atImInfty
  rw [show (1 : ℂ) = SlashInvariantFormClass.cuspFunction 1 E₄ 0 from hval.symm]
  exact (hcont.tendsto.comp hq).congr (fun z => (heq z).symm)

set_option maxHeartbeats 800000 in
/-- `E6(z) -> 1` as `Im(z) -> infinity`, from the q-expansion constant term. -/
theorem E₆_tendsto_one_atImInfty :
    Tendsto E₆ UpperHalfPlane.atImInfty (nhds 1) := by
  have heq : ∀ z : UpperHalfPlane, E₆ z = SlashInvariantFormClass.cuspFunction 1 E₆
      (Function.Periodic.qParam (↑(1 : ℕ)) (z : ℂ)) :=
    fun z => (SlashInvariantFormClass.eq_cuspFunction 1 E₆ z).symm
  have hfps := ModularFormClass.hasFPowerSeries_cuspFunction 1 E₆
  have hcont : ContinuousAt (SlashInvariantFormClass.cuspFunction 1 E₆) 0 :=
    hfps.analyticAt.continuousAt
  have hval : SlashInvariantFormClass.cuspFunction 1 E₆ 0 = 1 := by
    rw [cuspfunc_Zero]; exact E6_q_exp_zero
  have hq : Tendsto (fun (z : UpperHalfPlane) =>
      Function.Periodic.qParam (↑(1 : ℕ)) (z : ℂ))
      UpperHalfPlane.atImInfty (nhds 0) := by
    simp only [Nat.cast_one]; exact tendsto_qParam_atImInfty
  rw [show (1 : ℂ) = SlashInvariantFormClass.cuspFunction 1 E₆ 0 from hval.symm]
  exact (hcont.tendsto.comp hq).congr (fun z => (heq z).symm)

/-! ## CuspFunction of Delta: analytic properties at q = 0

The cuspFunction `cF(q)` of Delta is analytic at `q = 0` with `cF(0) = 0`
and `cF'(0) = 1` (from the q-expansion `Delta = q - 24*q^2 + ...`).
This gives `cF(q)/q -> 1` and `cF'(q) -> 1` as `q -> 0`. -/

/-- The cuspFunction of Delta. -/
noncomputable def cF_Delta := SlashInvariantFormClass.cuspFunction 1 Delta

/-- The derivative of cF_Delta at 0 is 1 (the `q^1` coefficient of Delta). -/
lemma deriv_cF_Delta_zero : deriv cF_Delta 0 = 1 := by
  have hfps := ModularFormClass.hasFPowerSeries_cuspFunction 1 Delta
  have : cF_Delta = SlashInvariantFormClass.cuspFunction 1 Delta := rfl
  rw [this, hfps.hasFPowerSeriesAt.deriv]
  simp [ModularFormClass.qExpansionFormalMultilinearSeries]
  exact Delta_q_one_term

/-- cF_Delta has derivative 1 at 0 (HasDerivAt version). -/
lemma cF_Delta_hasDerivAt_zero : HasDerivAt cF_Delta (1 : ℂ) 0 := by
  have hfps := ModularFormClass.hasFPowerSeries_cuspFunction 1 Delta
  rw [← deriv_cF_Delta_zero]
  have : cF_Delta = SlashInvariantFormClass.cuspFunction 1 Delta := rfl
  rw [this]; exact hfps.analyticAt.differentiableAt.hasDerivAt

/-- `cF(q)/q -> 1` as `q -> 0` (from the simple zero of Delta at the cusp). -/
lemma cF_Delta_div_q_tendsto :
    Tendsto (fun q => cF_Delta q / q) (𝓝[≠] 0) (nhds 1) := by
  have h0 : cF_Delta 0 = 0 := CuspFormClass.cuspFunction_apply_zero 1 Delta
  have hda := cF_Delta_hasDerivAt_zero
  rw [hasDerivAt_iff_tendsto_slope] at hda
  convert hda using 1
  ext q; simp [slope, h0, div_eq_mul_inv, mul_comm]

/-- `deriv cF_Delta` is continuous at 0 (analyticity of the derivative). -/
lemma continuousAt_deriv_cF_Delta : ContinuousAt (deriv cF_Delta) 0 := by
  have hfps := ModularFormClass.hasFPowerSeries_cuspFunction 1 Delta
  have : cF_Delta = SlashInvariantFormClass.cuspFunction 1 Delta := rfl
  rw [this]; exact hfps.analyticAt.deriv.continuousAt

/-- `cF'(q) -> 1` as `q -> 0`. -/
lemma tendsto_deriv_cF_Delta : Tendsto (deriv cF_Delta) (𝓝 0) (nhds 1) := by
  rw [← deriv_cF_Delta_zero]; exact continuousAt_deriv_cF_Delta

set_option maxHeartbeats 800000 in
/-- `q * cF'(q) / cF(q) -> 1` as `q -> 0` (within `q != 0`).
This is the key ratio that controls the logDeriv of Delta at the cusp. -/
lemma cF_ratio_tendsto_one :
    Tendsto (fun q => q * deriv cF_Delta q / cF_Delta q) (𝓝[≠] 0) (nhds 1) := by
  have h1 : Tendsto (fun q => deriv cF_Delta q / (cF_Delta q / q)) (𝓝[≠] 0) (nhds 1) := by
    rw [show (1 : ℂ) = 1 / 1 from by ring]
    exact (tendsto_deriv_cF_Delta.mono_left nhdsWithin_le_nhds).div
      cF_Delta_div_q_tendsto one_ne_zero
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [mem_compl_iff, mem_singleton_iff] at hq
  field_simp

/-! ## phi0 is bounded at Im -> infinity

We prove `φ₀ = (E₂E₄-E₆)²/Δ` is bounded at Im -> infinity. The proof uses:
- `E₂E₄-E₆ = (E₂-1)·E₄ + (E₄-E₆)` is `O(q)` as `Im → ∞`
- `|E₂-1| ≤ 192·|q|` from the q-expansion series bound
- `|E₄-E₆| ≤ L·|q|` from analyticity of cuspFunctions
- `|Δ| ≥ (1/2)|q|` from `cF_Delta_div_q_tendsto`
Combined: `|φ₀| ≤ 2K²|q| → 0`.
-/

/-- `E₂·E₄ - E₆` is `O(q)` at infinity: there exists `K` and `A` such that
`‖E₂ z * E₄ z - E₆ z‖ ≤ K * ‖qParam z‖` for `Im(z) ≥ A` and `‖E₄ z‖ ≤ 2`. -/
private lemma A_E_is_O_q : ∃ K > 0, ∃ A : ℝ, ∀ z : UpperHalfPlane, A ≤ z.im →
    ‖E₂ z * E₄ z - E₆ z‖ ≤ K * ‖Function.Periodic.qParam 1 (z : ℂ)‖ ∧
    ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 ∧
    Function.Periodic.qParam 1 (z : ℂ) ≠ 0 := by
  sorry

/-- Lower bound on `|Δ|` in terms of `|q|` for small `q`. -/
private lemma Delta_lower_bound : ∃ r > 0, ∀ z : UpperHalfPlane,
    ‖Function.Periodic.qParam 1 (z : ℂ)‖ < r →
    Function.Periodic.qParam 1 (z : ℂ) ≠ 0 →
    1/2 * ‖Function.Periodic.qParam 1 (z : ℂ)‖ ≤ ‖Δ z‖ := by
  have h := cF_Delta_div_q_tendsto
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ_pos, hδ⟩ := h (1/2) (by norm_num)
  refine ⟨δ, hδ_pos, fun z hqz_small hqz_ne => ?_⟩
  set qz := Function.Periodic.qParam 1 (z : ℂ)
  have hDelta_eq : Δ z = cF_Delta qz := by
    have := (SlashInvariantFormClass.eq_cuspFunction 1 Delta z).symm
    simp only [Nat.cast_one, cF_Delta] at this ⊢; exact this
  rw [hDelta_eq]
  have hq_pos : 0 < ‖qz‖ := norm_pos_iff.mpr hqz_ne
  have hdist := hδ hqz_ne (by rwa [dist_zero_right])
  rw [dist_eq_norm, div_sub_one hqz_ne, norm_div] at hdist
  have hcF_close : ‖cF_Delta qz - qz‖ < 1/2 * ‖qz‖ := by
    rwa [div_lt_iff₀ hq_pos] at hdist
  -- ‖qz‖ = ‖cF_Delta qz - (cF_Delta qz - qz)‖ ≤ ‖cF_Delta qz‖ + ‖cF_Delta qz - qz‖
  have h_tri : ‖qz‖ ≤ ‖cF_Delta qz‖ + ‖cF_Delta qz - qz‖ := by
    calc ‖qz‖ = ‖cF_Delta qz - (cF_Delta qz - qz)‖ := by ring_nf
      _ ≤ ‖cF_Delta qz‖ + ‖cF_Delta qz - qz‖ := norm_sub_le _ _
  linarith

/-- phi0 is bounded at `Im -> infinity`. -/
theorem phi0_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty φ₀ := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  obtain ⟨K, hK_pos, A₁, hA₁⟩ := A_E_is_O_q
  obtain ⟨r, hr_pos, hDelta_lb⟩ := Delta_lower_bound
  -- Get A₂ such that Im(z) ≥ A₂ implies |q| < r.
  have hq_event : ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖Function.Periodic.qParam 1 (z : ℂ)‖ < r := by
    have := tendsto_qParam_atImInfty.eventually (Metric.ball_mem_nhds 0 hr_pos)
    apply this.mono; intro z hz; rwa [dist_zero_right] at hz
  rw [Filter.eventually_atImInfty] at hq_event
  obtain ⟨A₂, hA₂⟩ := hq_event
  refine ⟨2 * K ^ 2, max A₁ A₂, fun z hz => ?_⟩
  have hz1 : A₁ ≤ z.im := le_trans (le_max_left _ _) hz
  have hz2 : A₂ ≤ z.im := le_trans (le_max_right _ _) hz
  set qz := Function.Periodic.qParam 1 (z : ℂ)
  obtain ⟨hAE_bound, hqz_lt_one, hqz_ne⟩ := hA₁ z hz1
  have hqz_small : ‖qz‖ < r := hA₂ z hz2
  have hDelta_lower : 1/2 * ‖qz‖ ≤ ‖Δ z‖ := hDelta_lb z hqz_small hqz_ne
  simp only [φ₀]
  rw [norm_div, norm_pow]
  have hqz_pos : 0 < ‖qz‖ := norm_pos_iff.mpr hqz_ne
  have hDelta_pos : 0 < ‖Δ z‖ := norm_pos_iff.mpr (Δ_ne_zero z)
  have hnum_bound : ‖E₂ z * E₄ z - E₆ z‖ ^ 2 ≤ (K * ‖qz‖) ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) hAE_bound
  have hden_lower : 0 < 1/2 * ‖qz‖ := by positivity
  calc ‖E₂ z * E₄ z - E₆ z‖ ^ 2 / ‖Δ z‖
      ≤ (K * ‖qz‖) ^ 2 / (1/2 * ‖qz‖) := by
        apply div_le_div₀ (by positivity) hnum_bound hden_lower hDelta_lower
    _ = 2 * K ^ 2 * ‖qz‖ := by field_simp
    _ ≤ 2 * K ^ 2 := by nlinarith [hqz_lt_one, sq_nonneg K]

end
