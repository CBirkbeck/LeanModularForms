/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.E2
import LeanModularForms.Modularforms.csqrt
import LeanModularForms.Modularforms.logDeriv_lems
import LeanModularForms.Modularforms.exp_lems
import LeanModularForms.Modularforms.upperhalfplane

/-!
# The Dedekind eta function (working version)

This file develops the Dedekind eta function `η(z) = q^{1/24} * ∏ (1 - q^{n+1})`
on the complex plane, with the goal of computing its logarithmic derivative and
its transformation law under `z ↦ -1/z`.

The companion file `LeanModularForms.Modularforms.eta` uses mathlib's
`ModularForm.eta` for the same construction; this file keeps a local primed
copy that is used downstream in `LeanModularForms.SpherePacking.PhiHolomorphic`.

## Main definitions

* `dedekindEtaFun'`: the Dedekind eta function on `ℂ`.
* `etaProdTerm`: the infinite product factor `∏' (1 - q^{n+1})`.

## Main results

* `dedekindEtaFun'_ne_zero`: `η` does not vanish on the upper half-plane.
* `eta_DifferentiableAt_UpperHalfPlane'`: `η` is differentiable on the upper half-plane.
* `etaProdTerm_ne_zero`: the product term is non-zero on the upper half-plane.
* `eta_logDeriv'`: the logarithmic derivative of `η` equals `(πI/12) * E₂`.
* `eta_equality'`: the modular transformation `η(-1/z) = √(z/I) * η(z)`.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

local notation "𝕢" => Periodic.qParam

local notation "𝕢₁" => Periodic.qParam 1

noncomputable abbrev eta_q (n : ℕ) (z : ℂ) := (𝕢₁ z) ^ (n + 1)

private lemma eta_q_eq_exp (n : ℕ) (z : ℂ) :
    eta_q n z = cexp (2 * π * Complex.I * (n + 1) * z) := by
  simp [eta_q, Periodic.qParam, ← Complex.exp_nsmul]
  ring_nf

private lemma eta_q_eq_pow (n : ℕ) (z : ℂ) :
    eta_q n z = cexp (2 * π * Complex.I * z) ^ (n + 1) := by
  simp [eta_q, Periodic.qParam]

private lemma one_add_eta_q_ne_zero (n : ℕ) (z : ℍ) : 1 - eta_q n z ≠ 0 := by
  rw [eta_q_eq_exp, sub_ne_zero]
  intro h
  simpa [← h] using exp_upperHalfPlane_lt_one_nat z n

/-- The infinite product factor `∏' (1 - q^{n+1})` of the Dedekind eta function. -/
noncomputable abbrev etaProdTerm (z : ℂ) := ∏' (n : ℕ), (1 - eta_q n z)

local notation "ηₚ" => etaProdTerm

/-- The Dedekind eta function on `ℂ`. We define it on the whole complex plane (rather
than just the upper half-plane) so we can take its logarithmic derivative. -/
noncomputable def dedekindEtaFun' (z : ℂ) := (𝕢 24 z) * ηₚ z

local notation "η" => dedekindEtaFun'

private theorem summable_eta_q (z : ℍ) : Summable fun n : ℕ ↦ ‖-eta_q n z‖ := by
  simp [eta_q, eta_q_eq_pow, summable_nat_add_iff 1, exp_upperHalfPlane_lt_one z]

private lemma hasProdLocallyUniformlyOn_eta :
    HasProdLocallyUniformlyOn (fun n a ↦ 1 - eta_q n a) ηₚ {x | 0 < x.im} := by
  simp_rw [sub_eq_add_neg]
  apply hasProdLocallyUniformlyOn_of_forall_compact
    (isOpen_lt continuous_const Complex.continuous_im)
  intro K hK hcK
  by_cases hN : ¬ Nonempty K
  · rw [hasProdUniformlyOn_iff_tendstoUniformlyOn]
    simpa [not_nonempty_iff_eq_empty'.mp hN] using tendstoUniformlyOn_empty
  have hc : ContinuousOn (fun x ↦ ‖cexp (2 * ↑π * Complex.I * x)‖) K := by fun_prop
  obtain ⟨z, hz, hB, HB⟩ := IsCompact.exists_sSup_image_eq_and_ge hcK (by simpa using hN) hc
  apply Summable.hasProdUniformlyOn_nat_one_add hcK (summable_eta_q ⟨z, by simpa using (hK hz)⟩)
  · filter_upwards with n x hx
    simpa only [eta_q, eta_q_eq_pow n x, norm_neg, norm_pow, coe_mk,
        eta_q_eq_pow n (⟨z, hK hz⟩ : ℍ)] using
        pow_le_pow_left₀ (by simp [norm_nonneg]) (HB x hx) (n + 1)
  · simp_rw [eta_q, Periodic.qParam]
    fun_prop

theorem etaProdTerm_ne_zero (z : ℍ) : ηₚ z ≠ 0 := by
  refine tprod_one_add_ne_zero_of_summable (f := fun n => -eta_q n z) ?_ ?_
  · exact fun i => by simpa using one_add_eta_q_ne_zero i z
  · simpa [eta_q, ← summable_norm_iff] using summable_eta_q z

/-- Eta is non-vanishing on the upper half-plane. -/
lemma dedekindEtaFun'_ne_zero (z : ℍ) : η z ≠ 0 := by
  simpa [dedekindEtaFun', Periodic.qParam] using etaProdTerm_ne_zero z

private lemma logDeriv_one_sub_mul_cexp_comp (r : ℂ) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * (deriv g z) * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp (by fun_prop) (hg y), logDeriv_one_sub_exp]
  ring

private theorem one_sub_eta_q_logDeriv_eq (z : ℂ) (i : ℕ) :
    logDeriv (fun x ↦ 1 - eta_q i x) z =
      2 * ↑π * Complex.I * (↑i + 1) * -eta_q i z / (1 - eta_q i z) := by
  have h2 : (fun x ↦ 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x)) =
      ((fun z ↦ 1 - 1 * cexp z) ∘ fun x ↦ 2 * ↑π * Complex.I * (↑i + 1) * x) := by aesop
  have h3 : deriv (fun x : ℂ ↦ (2 * π * Complex.I * (i + 1) * x)) =
      fun _ ↦ 2 * π * Complex.I * (i + 1) := by
    ext y
    simpa using deriv_const_mul (2 * π * Complex.I * (i + 1)) (d := fun (x : ℂ) => x) (x := y)
  simp_rw [eta_q_eq_exp, h2, logDeriv_one_sub_mul_cexp_comp 1
    (g := fun x => (2 * π * Complex.I * (i + 1) * x)) (by fun_prop), h3]
  simp

private lemma tsum_logDeriv_eta_q (z : ℂ) :
    ∑' (i : ℕ), logDeriv (fun x ↦ 1 - eta_q i x) z =
      ∑' n : ℕ, (2 * ↑π * Complex.I * (n + 1)) * (-eta_q n z) / (1 - eta_q n z) :=
  tsum_congr (fun i => one_sub_eta_q_logDeriv_eq z i)

private lemma tsum_logDeriv_eta_q_mul_left (z : ℂ) :
    ∑' (i : ℕ), logDeriv (fun x ↦ 1 - eta_q i x) z =
      (2 * ↑π * Complex.I) * ∑' n : ℕ, (n + 1) * (-eta_q n z) / (1 - eta_q n z) := by
  rw [tsum_logDeriv_eta_q z, ← tsum_mul_left]
  exact tsum_congr fun i => by ring

private lemma logDeriv_qParam_24 (z : ℍ) : logDeriv (𝕢 24) ↑z = 2 * ↑π * Complex.I / 24 := by
  have : (𝕢 24) = (fun z ↦ cexp z) ∘ (fun z => (2 * ↑π * Complex.I / 24) * z) := by
    ext y
    simp only [Periodic.qParam, ofReal_ofNat, comp_apply]
    ring_nf
  rw [this, logDeriv_comp, deriv_const_mul]
  · simp [logDeriv_exp]
  all_goals fun_prop

theorem etaProdTerm_differentiableAt (z : ℍ) : DifferentiableAt ℂ ηₚ ↑z := by
  have hD := hasProdLocallyUniformlyOn_eta.tendstoLocallyUniformlyOn_finsetRange.differentiableOn ?_
    (isOpen_lt continuous_const Complex.continuous_im)
  · exact (hD z z.2).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds z.2)
  · filter_upwards with b _
    apply (DifferentiableOn.finset_prod (u := Finset.range b)
      (f := fun i x => 1 - cexp (2 * ↑π * Complex.I * (↑i + 1) * x))
      (by fun_prop)).congr
    intro x _
    simp [sub_eq_add_neg, eta_q_eq_exp]

lemma eta_DifferentiableAt_UpperHalfPlane' (z : ℍ) : DifferentiableAt ℂ dedekindEtaFun' z :=
  DifferentiableAt.mul (by fun_prop) (etaProdTerm_differentiableAt z)

/-- The logarithmic derivative of the Dedekind eta function on the upper half-plane is
`(πI/12) * E₂`. -/
lemma eta_logDeriv' (z : ℍ) : logDeriv dedekindEtaFun' z = (π * Complex.I / 12) * E₂ z := by
  unfold dedekindEtaFun' etaProdTerm
  rw [logDeriv_mul (UpperHalfPlane.coe z) _ (etaProdTerm_ne_zero z) _
    (etaProdTerm_differentiableAt z)]
  · have HG := logDeriv_tprod_eq_tsum2 (isOpen_lt continuous_const Complex.continuous_im)
      ⟨(z : ℂ), z.2⟩ (fun n x => 1 - eta_q n x)
      (fun i ↦ one_add_eta_q_ne_zero i z) ?_ ?_ ?_ (etaProdTerm_ne_zero z)
    rw [show (⟨(z : ℂ), z.2⟩ : {b : ℂ | 0 < b.im}).1 = UpperHalfPlane.coe z by rfl] at HG
    rw [HG]
    · simp only [tsum_logDeriv_eta_q_mul_left z, E₂, logDeriv_qParam_24 z, mul_neg]
      rw [show E2 z = E₂ z from rfl, E₂_eq z, mul_sub, sub_eq_add_neg]
      conv_rhs => rw [show (∑' (n : ℕ+), ↑↑n * cexp (2 * ↑π * Complex.I * ↑↑n * ↑z) /
          (1 - cexp (2 * ↑π * Complex.I * ↑↑n * ↑z))) = ∑' (n : ℕ),
          (↑(n + 1 : ℕ) * cexp (2 * ↑π * Complex.I * ↑(n + 1 : ℕ) * ↑z) /
          (1 - cexp (2 * ↑π * Complex.I * ↑(n + 1 : ℕ) * ↑z))) from by
        rw [← Equiv.pnatEquivNat.symm.tsum_eq]; simp]
      simp_rw [eta_q_eq_exp]
      congr 1
      · ring
      · rw [← tsum_mul_left, ← neg_eq_iff_eq_neg]
        conv_rhs => rw [← tsum_mul_left, ← tsum_mul_left]
        rw [← tsum_neg]
        exact tsum_congr fun n => by push_cast; ring
    · intro i x _
      simp_rw [eta_q_eq_exp]
      fun_prop
    · simp only [one_sub_eta_q_logDeriv_eq]
      refine ((summable_nat_add_iff 1).mpr ((logDeriv_q_expo_summable (𝕢₁ z)
        (by simpa [Periodic.qParam] using exp_upperHalfPlane_lt_one z)).mul_left
          (-2 * π * Complex.I))).congr fun b => ?_
      have := one_add_eta_q_ne_zero b z
      simp only [ne_eq, neg_mul, Nat.cast_add, Nat.cast_one, mul_neg] at *
      field_simp
    · exact hasProdLocallyUniformlyOn_eta.multipliableLocallyUniformlyOn
  · simp [Periodic.qParam]
  · fun_prop

/-- Decompose `logDeriv (η ∘ (-1/·)) z` into `(z²)⁻¹ * logDeriv η (-1/z)`. -/
private lemma logDeriv_eta_comp_inv_neg (z : ℍ) :
    (logDeriv (η ∘ (fun z : ℂ => -1/z))) z =
      ((z : ℂ) ^ (2 : ℤ))⁻¹ *
        (logDeriv η) (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
  rw [logDeriv_comp, mul_comm]
  · congr
    conv =>
      enter [1, 1]
      intro z
      rw [neg_div]
      simp
    simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
    norm_cast
  · simpa only using
      eta_DifferentiableAt_UpperHalfPlane' (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
  · conv =>
      enter [2]
      ext z
      rw [neg_div]
      simp
    refine .neg (.inv ?_ (ne_zero z))
    simp

/-- `csqrt` is differentiable at `z` for `z ∈ ℍ`. -/
private lemma csqrt_differentiableAt' (z : ℍ) : DifferentiableAt ℂ csqrt ↑z := by
  unfold csqrt
  rw [show (fun a ↦ cexp (1 / 2 * Complex.log a)) = cexp ∘ (fun a ↦ 1 / 2 * Complex.log a) by rfl]
  refine .comp _ (by simp) (.const_mul (Complex.differentiableAt_log ?_) _)
  rw [mem_slitPlane_iff]
  right
  exact Ne.symm (ne_of_lt (by simpa using z.2))

lemma eta_logDeriv_eql' (z : ℍ) :
    (logDeriv (η ∘ (fun z : ℂ => -1/z))) z = (logDeriv ((csqrt) * η)) z := by
  rw [logDeriv_eta_comp_inv_neg z, show ((csqrt) * η) = (fun x => (csqrt) x * η x) by rfl,
    logDeriv_mul]
  nth_rw 2 [logDeriv_apply]
  unfold csqrt
  rw [csqrt_deriv z]
  simp only [one_div, neg_mul, smul_eq_mul]
  nth_rw 2 [div_eq_mul_inv]
  rw [← Complex.exp_neg,
    show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
      (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z))) * 2⁻¹ by ring,
    ← Complex.exp_add, ← sub_eq_add_neg,
    show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring,
    Complex.exp_neg, Complex.exp_log, eta_logDeriv' z]
  rw [eta_logDeriv' (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)]
  have E := E₂_transform z
  simp only [SL_slash_def, modular_S_smul, ModularGroup.denom_S, Int.reduceNeg, zpow_neg] at *
  have h00 : (UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos) =
      (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    simp
    ring_nf
  rw [h00] at E
  rw [← mul_assoc, mul_comm, ← mul_assoc, E, add_mul, add_comm]
  congr 1
  · have hzne : (z : ℂ) ≠ 0 := ne_zero z
    have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  · ring
  · simpa only [UpperHalfPlane.coe, ne_eq] using ne_zero z
  · simp [csqrt]
  · exact dedekindEtaFun'_ne_zero z
  · exact csqrt_differentiableAt' z
  · exact eta_DifferentiableAt_UpperHalfPlane' z

lemma eta_logderivs' : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ => -1/z)))
    (logDeriv ((csqrt) * η)) :=
  fun _ hz => eta_logDeriv_eql' ⟨_, hz⟩

lemma eta_logderivs_const' : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
    (z • ((csqrt) * η)) := by
  have h := eta_logderivs'
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · exact ({z : ℂ | 0 < z.im})
    · exact fun x hx => (eta_DifferentiableAt_UpperHalfPlane' ⟨x, hx⟩).differentiableWithinAt
    · apply DifferentiableOn.div (by fun_prop) (by fun_prop)
      intro x hx
      have := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv =>
        enter [2,1]
        rw [neg_div]
        rw [div_eq_mul_inv]
        simp
      simpa using this
  · apply DifferentiableOn.mul
    · exact fun x hx => (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    · exact fun x hx => (eta_DifferentiableAt_UpperHalfPlane' ⟨x, hx⟩).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · haveI : IsBoundedSMul ℝ ℂ := NormedSpace.toIsBoundedSMul
    exact (convex_halfSpace_im_gt 0).isPreconnected
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨?_, dedekindEtaFun'_ne_zero ⟨x, hx⟩⟩
    simp [csqrt]
  · intro x hx
    simpa using dedekindEtaFun'_ne_zero ⟨-1 / x, by simpa using pnat_div_upper 1 ⟨x, hx⟩⟩

lemma eta_equality' : {z : ℂ | 0 < z.im}.EqOn ((η ∘ (fun z : ℂ => -1/z)))
    ((csqrt (Complex.I))⁻¹ • ((csqrt) * η)) := by
  obtain ⟨z, hz, h⟩ := eta_logderivs_const'
  intro x hx
  have h2 := h hx
  have hI : (Complex.I) ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp at h3
  conv at h3 =>
    enter [2]
    rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := dedekindEtaFun'_ne_zero UpperHalfPlane.I
  have hcd := (mul_eq_right₀ he).mp (Eq.symm h3)
  rw [mul_eq_one_iff_inv_eq₀ hz, inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2
