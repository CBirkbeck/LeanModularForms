/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.NumberTheory.ModularForms.LevelOne
import LeanModularForms.Modularforms.AtImInfty
import LeanModularForms.Modularforms.Eisenstein

/-!
# Cusp decay for Eisenstein series and the Viazovska integrand

This file proves that the Eisenstein series `E₄`, `E₆` tend to `1` at the cusp
(`Im → ∞`), establishes the analytic properties at `q = 0` of the cuspFunction of
`Δ` needed for cusp decay analysis (analyticity, `cF(0) = 0`, `cF'(0) = 1`), and
combines these to show `φ₀ = (E₂E₄ - E₆)² / Δ` is bounded at the cusp.

## Main results

* `tendsto_qParam_atImInfty` : `qParam 1 z → 0` as `Im z → ∞`.
* `E₄_tendsto_one_atImInfty`, `E₆_tendsto_one_atImInfty` : `E₄`, `E₆` tend to `1`
  at the cusp, from their `q`-expansion constant term.
* `cF_Delta_div_q_tendsto` : `cuspFunction(Δ)(q) / q → 1` as `q → 0`.
* `tendsto_deriv_cF_Delta` : `(cuspFunction Δ)'(q) → 1` as `q → 0`.
* `cF_ratio_tendsto_one` : `q · cF'(q) / cF(q) → 1` as `q → 0`.
* `phi0_isBoundedAtImInfty` : `φ₀` is bounded at the cusp.

## Proof strategy for `phi0_isBoundedAtImInfty`

The proof that `φ₀(w) = (E₂(w)·E₄(w) - E₆(w))² / Δ(w)` is bounded at `Im → ∞`
combines a numerator bound `‖E₂E₄ - E₆‖ = O(‖q‖)` with a denominator lower bound
`‖Δ‖ ≥ (1/2)‖q‖`:
* `E₂E₄ - E₆ = E₂(E₄ - 1) + (E₂ - 1) - (E₆ - 1)` and each factor is `O(q)`
  (`|E₂ - 1| ≤ 192|q|` from the Eisenstein `q`-series; `|E₄ - 1|`, `|E₆ - 1|`
  from analyticity of the cuspFunctions);
* `|Δ| ≥ (1/2)|q|` follows from `cF_Delta_div_q_tendsto`;
* combined, `|φ₀| ≤ 2K²|q|`, which is bounded.
-/

open Complex Set Filter Topology MeasureTheory ModularFormClass

noncomputable section

/-- The `q`-parameter `q = exp (2π i z)` tends to `0` as `Im(z) → ∞`. -/
theorem tendsto_qParam_atImInfty :
    Tendsto (fun (z : UpperHalfPlane) => Function.Periodic.qParam 1 (z : ℂ))
    UpperHalfPlane.atImInfty (nhds 0) := by
  have h := (tendsto_neg_cexp_atImInfty 0).neg
  simp only [Nat.cast_zero, zero_add, mul_one, neg_neg, neg_zero] at h
  exact h.congr fun z => by simp only [Function.Periodic.qParam]; congr 1; push_cast; ring

private lemma tendsto_one_atImInfty_of_cuspFunction_eq_one {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k)
    (hval : SlashInvariantFormClass.cuspFunction 1 f 0 = 1) :
    Tendsto f UpperHalfPlane.atImInfty (nhds 1) := by
  have hcont : ContinuousAt (SlashInvariantFormClass.cuspFunction 1 f) 0 :=
    (analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL2Z).continuousAt
  rw [show (1 : ℂ) = SlashInvariantFormClass.cuspFunction 1 f 0 from hval.symm]
  exact (hcont.tendsto.comp tendsto_qParam_atImInfty).congr fun z =>
    SlashInvariantFormClass.eq_cuspFunction f z one_mem_strictPeriods_SL2Z one_ne_zero

private lemma cuspFunction_E₄_zero : SlashInvariantFormClass.cuspFunction 1 E₄ 0 = 1 := by
  have h := cuspfunc_Zero (n := 1) (f := E₄)
  simp only [Nat.cast_one] at h
  rw [h]; exact E4_q_exp_zero

private lemma cuspFunction_E₆_zero : SlashInvariantFormClass.cuspFunction 1 E₆ 0 = 1 := by
  have h := cuspfunc_Zero (n := 1) (f := E₆)
  simp only [Nat.cast_one] at h
  rw [h]; exact E6_q_exp_zero

/-- `E₄(z) → 1` as `Im(z) → ∞`, from the `q`-expansion constant term. -/
theorem E₄_tendsto_one_atImInfty : Tendsto E₄ UpperHalfPlane.atImInfty (nhds 1) :=
  tendsto_one_atImInfty_of_cuspFunction_eq_one E₄ cuspFunction_E₄_zero

/-- `E₆(z) → 1` as `Im(z) → ∞`, from the `q`-expansion constant term. -/
theorem E₆_tendsto_one_atImInfty : Tendsto E₆ UpperHalfPlane.atImInfty (nhds 1) :=
  tendsto_one_atImInfty_of_cuspFunction_eq_one E₆ cuspFunction_E₆_zero

/-- The cuspFunction of `Δ`. -/
noncomputable def cF_Delta := SlashInvariantFormClass.cuspFunction 1 Delta

/-- The derivative of `cF_Delta` at `0` equals `1`. -/
lemma deriv_cF_Delta_zero : deriv cF_Delta 0 = 1 := by
  have hfps := ModularFormClass.hasFPowerSeries_cuspFunction Delta one_pos
    one_mem_strictPeriods_SL2Z
  unfold cF_Delta
  rw [hfps.hasFPowerSeriesAt.deriv]
  simp [ModularFormClass.qExpansionFormalMultilinearSeries]
  exact Delta_q_one_term

/-- `cF_Delta` has derivative `1` at `0`. -/
lemma cF_Delta_hasDerivAt_zero : HasDerivAt cF_Delta (1 : ℂ) 0 := by
  rw [← deriv_cF_Delta_zero]
  exact (ModularFormClass.analyticAt_cuspFunction_zero Delta one_pos
    one_mem_strictPeriods_SL2Z).differentiableAt.hasDerivAt

/-- `cF(q) / q → 1` as `q → 0`. -/
lemma cF_Delta_div_q_tendsto :
    Tendsto (fun q => cF_Delta q / q) (𝓝[≠] 0) (nhds 1) := by
  have h0 : cF_Delta 0 = 0 := CuspFormClass.cuspFunction_apply_zero Delta one_pos
    one_mem_strictPeriods_SL2Z
  have hda := cF_Delta_hasDerivAt_zero
  rw [hasDerivAt_iff_tendsto_slope] at hda
  convert hda using 1
  ext q; simp [slope, h0, div_eq_mul_inv, mul_comm]

/-- `deriv cF_Delta` is continuous at `0`. -/
lemma continuousAt_deriv_cF_Delta : ContinuousAt (deriv cF_Delta) 0 :=
  (ModularFormClass.analyticAt_cuspFunction_zero Delta one_pos
    one_mem_strictPeriods_SL2Z).deriv.continuousAt

/-- `cF'(q) → 1` as `q → 0`. -/
lemma tendsto_deriv_cF_Delta : Tendsto (deriv cF_Delta) (𝓝 0) (nhds 1) :=
  deriv_cF_Delta_zero ▸ continuousAt_deriv_cF_Delta

/-- The ratio `q · cF'(q) / cF(q) → 1` as `q → 0`, away from `q = 0`. -/
lemma cF_ratio_tendsto_one :
    Tendsto (fun q => q * deriv cF_Delta q / cF_Delta q) (𝓝[≠] 0) (nhds 1) := by
  have h1 : Tendsto (fun q => deriv cF_Delta q / (cF_Delta q / q)) (𝓝[≠] 0) (nhds 1) := by
    simpa using (tendsto_deriv_cF_Delta.mono_left nhdsWithin_le_nhds).div
      cF_Delta_div_q_tendsto one_ne_zero
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with q hq
  simp only [mem_compl_iff, mem_singleton_iff] at hq
  field_simp

private lemma exp_eq_qParam_pow (z : UpperHalfPlane) (n : ℕ+) :
    cexp (2 * ↑Real.pi * I * ↑↑n * ↑z) =
    (Function.Periodic.qParam 1 (z : ℂ)) ^ (n : ℕ) := by
  simp only [Function.Periodic.qParam, ← exp_nsmul, nsmul_eq_mul, ofReal_one, div_one]
  ring_nf

private lemma tsum_pnat_eq_r_times (r : ℝ) :
    ∑' (n : ℕ+), (↑↑n : ℝ) * r ^ (n : ℕ) =
    r * ∑' (m : ℕ), (↑(m + 1) : ℝ) * r ^ m := by
  have h1 : ∑' (n : ℕ+), (↑↑n : ℝ) * r ^ (n : ℕ) =
      ∑' (m : ℕ), (↑(m + 1) : ℝ) * r ^ (m + 1) := by
    rw [← Equiv.tsum_eq Equiv.pnatEquivNat]
    congr 1
    ext n
    simp only [Equiv.pnatEquivNat, Equiv.coe_fn_mk]
    rw [show (↑↑n : ℝ) = (↑(n.natPred + 1) : ℝ) from by rw [n.natPred_add_one.symm],
        show (n : ℕ) = n.natPred + 1 from n.natPred_add_one.symm]
  rw [h1, ← tsum_mul_left]
  congr 1
  ext m
  ring

private lemma norm_term_le_two_mul {q : ℂ} (hq : ‖q‖ ≤ 1/2) (n : ℕ+) :
    ‖(↑↑n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
    2 * (n : ℝ) * ‖q‖ ^ (n : ℕ) := by
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast]
  have hqn_le : ‖q‖ ^ (n : ℕ) ≤ 1/2 :=
    (pow_le_pow_left₀ (norm_nonneg q) hq n).trans
      ((pow_le_pow_of_le_one (by norm_num) (by norm_num) n.2).trans (by norm_num))
  have h1_sub : 1/2 ≤ ‖1 - q ^ (n : ℕ)‖ := by
    linarith [norm_sub_norm_le (1 : ℂ) (q ^ (n : ℕ)), norm_one (α := ℂ),
      show ‖q ^ (n : ℕ)‖ ≤ 1/2 from norm_pow q n ▸ hqn_le]
  calc (n : ℝ) * ‖q‖ ^ (n : ℕ) / ‖1 - q ^ ↑n‖
      ≤ (n : ℝ) * ‖q‖ ^ (n : ℕ) / (1/2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) h1_sub
    _ = 2 * (n : ℝ) * ‖q‖ ^ (n : ℕ) := by ring

private lemma summable_nat_mul_pow {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => (↑n : ℝ) * r ^ n) :=
  (summable_pow_mul_geometric_of_norm_lt_one 1 hr).congr fun n => by simp only [pow_one]

private lemma summable_two_mul_pnat_pow {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ+ => 2 * (↑↑n : ℝ) * r ^ (n : ℕ)) := by
  change Summable ((fun m : ℕ => 2 * (↑m : ℝ) * r ^ m) ∘ (↑· : ℕ+ → ℕ))
  exact (((summable_nat_mul_pow hr).mul_left 2).congr
    fun n => by ring).comp_injective Subtype.val_injective

private lemma summable_norm_E2_terms {q : ℂ} (hq : ‖q‖ ≤ 1/2) :
    Summable (fun n : ℕ+ => ‖(↑↑n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖) := by
  have hnn : ‖(‖q‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)]
    exact hq.trans_lt (by norm_num)
  exact Summable.of_norm_bounded (summable_two_mul_pnat_pow hnn) fun n => by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact norm_term_le_two_mul hq n

private lemma tsum_succ_mul_pow {r : ℝ} (hr : ‖r‖ < 1) :
    ∑' m : ℕ, (↑(m + 1) : ℝ) * r ^ m = 1 / (1 - r) ^ 2 := by
  have := tsum_choose_mul_geometric_of_norm_lt_one 1 hr
  simp at this
  rw [one_div]
  convert this using 1
  congr 1
  ext n
  push_cast
  ring

private lemma tsum_two_mul_pnat_pow {r : ℝ} (hr : ‖r‖ < 1) :
    ∑' (n : ℕ+), 2 * (↑↑n : ℝ) * r ^ (n : ℕ) = 2 * (r / (1 - r) ^ 2) := by
  rw [show (fun n : ℕ+ => 2 * (↑↑n : ℝ) * r ^ (n : ℕ)) =
      (fun n : ℕ+ => 2 * ((↑↑n : ℝ) * r ^ (n : ℕ))) from by ext n; ring,
    tsum_mul_left, tsum_pnat_eq_r_times r, tsum_succ_mul_pow hr]
  ring

private lemma tsum_E2_series_bound {q : ℂ} (hq : ‖q‖ ≤ 1/2) :
    24 * ‖∑' (n : ℕ+), (↑↑n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ ≤
    192 * ‖q‖ := by
  have hq_lt : ‖q‖ < 1 := hq.trans_lt (by norm_num)
  have hnn : ‖(‖q‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg q)]
  calc 24 * ‖∑' (n : ℕ+), (↑↑n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖
      ≤ 24 * ∑' (n : ℕ+), ‖(↑↑n : ℂ) * q ^ (n : ℕ) / (1 - q ^ (n : ℕ))‖ :=
        mul_le_mul_of_nonneg_left
          (norm_tsum_le_tsum_norm (summable_norm_E2_terms hq)) (by norm_num)
    _ ≤ 24 * ∑' (n : ℕ+), 2 * (↑↑n : ℝ) * ‖q‖ ^ (n : ℕ) :=
        mul_le_mul_of_nonneg_left ((summable_norm_E2_terms hq).tsum_le_tsum
          (norm_term_le_two_mul hq) (summable_two_mul_pnat_pow hnn)) (by norm_num)
    _ = 24 * (2 * (‖q‖ / (1 - ‖q‖) ^ 2)) := by rw [tsum_two_mul_pnat_pow hnn]
    _ ≤ 24 * (2 * (4 * ‖q‖)) := by
        gcongr
        rw [div_le_iff₀ (pow_pos (by linarith) 2)]
        nlinarith [norm_nonneg q, sq_nonneg (1 - 2 * ‖q‖)]
    _ = 192 * ‖q‖ := by ring

private lemma E2_sub_one_bound (z : UpperHalfPlane)
    (hq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ ≤ 1/2) :
    ‖E₂ z - 1‖ ≤ 192 * ‖Function.Periodic.qParam 1 (z : ℂ)‖ := by
  set q := Function.Periodic.qParam 1 (z : ℂ)
  have hE2_sub :
      E₂ z - 1 = (-24) * ∑' (n : ℕ+), ↑↑n * q ^ (n : ℕ) / (1 - q ^ (n : ℕ)) := by
    have : E₂ z - 1 = (-24) * ∑' (n : ℕ+),
        ↑↑n * cexp (2 * ↑Real.pi * I * ↑↑n * ↑z) /
        (1 - cexp (2 * ↑Real.pi * I * ↑↑n * ↑z)) := by rw [E₂_eq z]; ring
    rw [this]
    congr 1
    exact tsum_congr fun n => by rw [exp_eq_qParam_pow z n]
  rw [hE2_sub, norm_mul, show ‖(-24 : ℂ)‖ = 24 from by norm_num]
  exact tsum_E2_series_bound hq

private lemma cuspFunction_sub_one_isBigO {k : ℤ}
    {f : ModularForm (CongruenceSubgroup.Gamma 1) k}
    (hval : SlashInvariantFormClass.cuspFunction 1 f 0 = 1) :
    (fun q : ℂ => SlashInvariantFormClass.cuspFunction 1 f q - 1) =O[𝓝 0] id := by
  have hbig := (ModularFormClass.analyticAt_cuspFunction_zero f one_pos
    one_mem_strictPeriods_SL2Z).differentiableAt.hasFDerivAt.isBigO_sub
  simpa only [hval, sub_zero] using hbig

private lemma sub_one_eventually_le_of_cuspFunction_eq_one {k : ℤ}
    (f : ModularForm (CongruenceSubgroup.Gamma 1) k)
    (hval : SlashInvariantFormClass.cuspFunction 1 f 0 = 1) :
    ∃ C > 0, ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
    ‖f z - 1‖ ≤ C * ‖Function.Periodic.qParam 1 (z : ℂ)‖ := by
  obtain ⟨C, hC, hbound⟩ := (cuspFunction_sub_one_isBigO hval).exists_pos
  exact ⟨C, hC, (tendsto_qParam_atImInfty.eventually
    (hbound.bound.mono fun q hq => by simpa [id] using hq)).mono fun z hz => by
      rwa [(SlashInvariantFormClass.eq_cuspFunction f z
        one_mem_strictPeriods_SL2Z one_ne_zero).symm]⟩

private lemma E4_sub_one_eventually_le : ∃ C > 0,
    ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
    ‖E₄ z - 1‖ ≤ C * ‖Function.Periodic.qParam 1 (z : ℂ)‖ :=
  sub_one_eventually_le_of_cuspFunction_eq_one E₄ cuspFunction_E₄_zero

private lemma E6_sub_one_eventually_le : ∃ C > 0,
    ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
    ‖E₆ z - 1‖ ≤ C * ‖Function.Periodic.qParam 1 (z : ℂ)‖ :=
  sub_one_eventually_le_of_cuspFunction_eq_one E₆ cuspFunction_E₆_zero

private lemma E2_sub_one_eventually_le :
    ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
    ‖E₂ z - 1‖ ≤ 192 * ‖Function.Periodic.qParam 1 (z : ℂ)‖ :=
  (tendsto_qParam_atImInfty.eventually
    (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ) < 1/2))).mono fun z hz =>
    E2_sub_one_bound z (by simp only [dist_zero_right] at hz; linarith)

private lemma qParam_eventually_lt_one :
    ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
    ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 :=
  (tendsto_qParam_atImInfty.eventually
    (Metric.ball_mem_nhds 0 (by norm_num : (0:ℝ) < 1))).mono fun _ hz => by
    rwa [dist_zero_right] at hz

private lemma E2E4_sub_E6_bound {z : UpperHalfPlane} {C₁ C₂ : ℝ} (hC₁ : 0 < C₁)
    (hE4 : ‖E₄ z - 1‖ ≤ C₁ * ‖Function.Periodic.qParam 1 (z : ℂ)‖)
    (hE6 : ‖E₆ z - 1‖ ≤ C₂ * ‖Function.Periodic.qParam 1 (z : ℂ)‖)
    (hE2 : ‖E₂ z - 1‖ ≤ 192 * ‖Function.Periodic.qParam 1 (z : ℂ)‖)
    (hq_lt : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1) :
    ‖E₂ z * E₄ z - E₆ z‖ ≤
    (193 * C₁ + 192 + C₂) * ‖Function.Periodic.qParam 1 (z : ℂ)‖ := by
  set qz := Function.Periodic.qParam 1 (z : ℂ)
  have hE2_norm : ‖E₂ z‖ ≤ 193 :=
    calc ‖E₂ z‖ ≤ ‖(1 : ℂ)‖ + ‖E₂ z - 1‖ := norm_le_insert' _ _
      _ ≤ 1 + 192 * ‖qz‖ := by linarith [norm_one (α := ℂ)]
      _ ≤ 1 + 192 * 1 := by nlinarith [norm_nonneg qz]
      _ = 193 := by norm_num
  rw [show E₂ z * E₄ z - E₆ z =
    E₂ z * (E₄ z - 1) + (E₂ z - 1) - (E₆ z - 1) from by ring]
  calc ‖E₂ z * (E₄ z - 1) + (E₂ z - 1) - (E₆ z - 1)‖
      ≤ ‖E₂ z * (E₄ z - 1)‖ + ‖E₂ z - 1‖ + ‖E₆ z - 1‖ := by
        linarith [norm_sub_le (E₂ z * (E₄ z - 1) + (E₂ z - 1)) (E₆ z - 1),
                  norm_add_le (E₂ z * (E₄ z - 1)) (E₂ z - 1)]
    _ ≤ ‖E₂ z‖ * (C₁ * ‖qz‖) + 192 * ‖qz‖ + C₂ * ‖qz‖ := by
        gcongr
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hE4 (norm_nonneg _)
    _ = (‖E₂ z‖ * C₁ + 192 + C₂) * ‖qz‖ := by ring
    _ ≤ (193 * C₁ + 192 + C₂) * ‖qz‖ := by gcongr

private lemma A_E_is_O_q : ∃ K > 0, ∃ A : ℝ, ∀ z : UpperHalfPlane, A ≤ z.im →
    ‖E₂ z * E₄ z - E₆ z‖ ≤ K * ‖Function.Periodic.qParam 1 (z : ℂ)‖ ∧
    ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 ∧
    Function.Periodic.qParam 1 (z : ℂ) ≠ 0 := by
  obtain ⟨C₁, hC₁, hE4⟩ := E4_sub_one_eventually_le
  obtain ⟨C₂, _, hE6⟩ := E6_sub_one_eventually_le
  have hE2 := E2_sub_one_eventually_le
  have hqlt := qParam_eventually_lt_one
  rw [Filter.eventually_atImInfty] at hE4 hE6 hE2 hqlt
  obtain ⟨A₁, h₁⟩ := hE4
  obtain ⟨A₂, h₂⟩ := hE6
  obtain ⟨A₃, h₃⟩ := hE2
  obtain ⟨A₅, h₅⟩ := hqlt
  refine ⟨193 * C₁ + 192 + C₂, by positivity, A₁ ⊔ A₂ ⊔ A₃ ⊔ A₅, fun z hz => ?_⟩
  have ge : ∀ Aᵢ, Aᵢ ≤ A₁ ⊔ A₂ ⊔ A₃ ⊔ A₅ → Aᵢ ≤ z.im := fun _ h => h.trans hz
  have g₁ := h₁ z (ge _ (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))
  have g₂ := h₂ z (ge _ (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))
  have g₃ := h₃ z (ge _ (le_sup_of_le_left le_sup_right))
  have g₅ := h₅ z (ge _ le_sup_right)
  exact ⟨E2E4_sub_E6_bound hC₁ g₁ g₂ g₃ g₅, g₅, Function.Periodic.qParam_ne_zero _⟩

private lemma Delta_lower_bound : ∃ r > 0, ∀ z : UpperHalfPlane,
    ‖Function.Periodic.qParam 1 (z : ℂ)‖ < r →
    Function.Periodic.qParam 1 (z : ℂ) ≠ 0 →
    1/2 * ‖Function.Periodic.qParam 1 (z : ℂ)‖ ≤ ‖Δ z‖ := by
  have h := cF_Delta_div_q_tendsto
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  obtain ⟨δ, hδ_pos, hδ⟩ := h (1/2) (by norm_num)
  refine ⟨δ, hδ_pos, fun z hqz_small hqz_ne => ?_⟩
  set qz := Function.Periodic.qParam 1 (z : ℂ)
  have hDelta_eq : Δ z = cF_Delta qz :=
    (SlashInvariantFormClass.eq_cuspFunction Delta z
      one_mem_strictPeriods_SL2Z one_ne_zero).symm
  rw [hDelta_eq]
  have hq_pos : 0 < ‖qz‖ := norm_pos_iff.mpr hqz_ne
  have hdist := hδ hqz_ne (by rwa [dist_zero_right])
  rw [dist_eq_norm, div_sub_one hqz_ne, norm_div] at hdist
  have hcF_close : ‖cF_Delta qz - qz‖ < 1/2 * ‖qz‖ := by rwa [div_lt_iff₀ hq_pos] at hdist
  linarith [show ‖qz‖ ≤ ‖cF_Delta qz‖ + ‖cF_Delta qz - qz‖ from
    calc ‖qz‖ = ‖cF_Delta qz - (cF_Delta qz - qz)‖ := by ring_nf
      _ ≤ ‖cF_Delta qz‖ + ‖cF_Delta qz - qz‖ := norm_sub_le _ _]

/-- `φ₀ = (E₂E₄ - E₆)² / Δ` is bounded at the cusp `Im → ∞`. -/
theorem phi0_isBoundedAtImInfty :
    UpperHalfPlane.IsBoundedAtImInfty φ₀ := by
  rw [UpperHalfPlane.isBoundedAtImInfty_iff]
  obtain ⟨K, hK_pos, A₁, hA₁⟩ := A_E_is_O_q
  obtain ⟨r, hr_pos, hDelta_lb⟩ := Delta_lower_bound
  have hq_event : ∀ᶠ z : UpperHalfPlane in UpperHalfPlane.atImInfty,
      ‖Function.Periodic.qParam 1 (z : ℂ)‖ < r :=
    (tendsto_qParam_atImInfty.eventually
      (Metric.ball_mem_nhds 0 hr_pos)).mono fun z hz => by rwa [dist_zero_right] at hz
  rw [Filter.eventually_atImInfty] at hq_event
  obtain ⟨A₂, hA₂⟩ := hq_event
  refine ⟨2 * K ^ 2, max A₁ A₂, fun z hz => ?_⟩
  set qz := Function.Periodic.qParam 1 (z : ℂ)
  obtain ⟨hAE_bound, hqz_lt_one, hqz_ne⟩ := hA₁ z ((le_max_left _ _).trans hz)
  have hDelta_lower : 1/2 * ‖qz‖ ≤ ‖Δ z‖ :=
    hDelta_lb z (hA₂ z ((le_max_right _ _).trans hz)) hqz_ne
  simp only [φ₀]
  rw [norm_div, norm_pow]
  calc ‖E₂ z * E₄ z - E₆ z‖ ^ 2 / ‖Δ z‖
      ≤ (K * ‖qz‖) ^ 2 / (1/2 * ‖qz‖) :=
        div_le_div₀ (by positivity) (pow_le_pow_left₀ (norm_nonneg _) hAE_bound 2)
          (by positivity) hDelta_lower
    _ = 2 * K ^ 2 * ‖qz‖ := by field_simp
    _ ≤ 2 * K ^ 2 := by nlinarith [hqz_lt_one, sq_nonneg K]

end
