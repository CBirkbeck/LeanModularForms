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

The key remaining step: `phi0` is bounded at infinity.
The mathematical argument is:
- `logDeriv(eta^24)(z) = 2*pi*I * q * cF'(q)/cF(q)` (chain rule + cuspFunction)
- `logDeriv(eta^24) = 24 * logDeriv(eta) = 24 * pi*I/12 * E2 = 2*pi*I * E2`
- So `E2 = q * cF'(q)/cF(q) -> 1` as `Im -> infinity`
- Then `E2*E4-E6 -> 0`, so `(E2*E4-E6)^2/Delta -> 0` (cusp form ratio)
- In particular, `phi0` is bounded at infinity. -/

/-- phi0 is bounded at `Im -> infinity`. -/
theorem phi0_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty φ₀ := by
  sorry

end
