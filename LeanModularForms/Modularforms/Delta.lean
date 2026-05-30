/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.QExpansion
public import LeanModularForms.Modularforms.ForMathlib_Cusps
public import LeanModularForms.Modularforms.NormNumI
public import LeanModularForms.Modularforms.ResToImagAxis
public import LeanModularForms.Modularforms.SlashActionAuxil
public import LeanModularForms.Modularforms.clog_arg_lems
public import LeanModularForms.Modularforms.eta
public import LeanModularForms.Modularforms.multipliable_lems

/-!
# The discriminant modular form `Δ`

This file defines the discriminant `Δ`, a cusp form of weight `12` on `SL(2, ℤ)`,
via its product expansion
`Δ(z) = q · ∏ₙ (1 - qⁿ)²⁴` where `q = exp(2πi z)`,
and establishes its basic properties.

## Main definitions

* `Δ`: the discriminant function on the upper half-plane.
* `Discriminant_SIF`: `Δ` as a `SlashInvariantForm` of weight `12` on `Γ(1)`.
* `Delta`: `Δ` as a `CuspForm` of weight `12` on `Γ(1)`.
* `CuspForm_div_Discriminant`: division by `Δ` as a map from cusp forms of weight `k` to
  modular forms of weight `k - 12`.

## Main results

* `Delta_eq_eta_pow`: `Δ = η²⁴`.
* `Δ_ne_zero`: `Δ` is nowhere-vanishing on the upper half-plane.
* `Delta_isTheta_rexp`: `Δ` has order of magnitude `exp(-2π·im z)` at the cusp `∞`.
* `Delta_imag_axis_pos`: `Δ(it)` is positive for `t > 0`.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open ArithmeticFunction

noncomputable section Definitions

/-- The discriminant modular form `Δ(z) = q · ∏ₙ (1 - qⁿ⁺¹)²⁴`, where `q = exp(2πi z)`. -/
def Δ (z : UpperHalfPlane) := cexp (2 * π * Complex.I * z) * ∏' (n : ℕ),
    (1 - cexp (2 * π * Complex.I * (n + 1) * z)) ^ 24

lemma DiscriminantProductFormula (z : ℍ) : Δ z = cexp (2 * π * Complex.I * z) * ∏' (n : ℕ+),
    (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24 := by
  simp only [Δ]
  conv_lhs =>
    enter [2, 1]
    ext n
    rw [show (n : ℂ) + 1 = ((n + 1) : ℕ) by simp]
  rw [tprod_pnat_eq_tprod_succ (f := fun n ↦ (1 - cexp (2 * π * Complex.I * (n) * z)) ^ 24)]

lemma Delta_eq_eta_pow (z : ℍ) : Δ z = (η z) ^ 24 := by
  have hm : Multipliable (fun n : ℕ ↦ 1 - ModularForm.eta_q n z) :=
    (MultipliableEtaProductExpansion z).congr fun n ↦ by simp [ModularForm.eta_q_eq_cexp]
  rw [η, ModularForm.eta, Δ, mul_pow,
    tprod_pow (f := fun n : ℕ ↦ 1 - ModularForm.eta_q n z) hm 24]
  congr
  · rw [Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    simp [field]
  · ext n
    simp [ModularForm.eta_q_eq_cexp]

lemma Δ_ne_zero (z : UpperHalfPlane) : Δ z ≠ 0 := by
  rw [Delta_eq_eta_pow]
  simpa [η] using ModularForm.eta_ne_zero (z := (z : ℂ)) z.2

lemma Discriminant_T_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.T) = Δ := by
  ext z
  rw [modular_slash_T_apply, Δ, Δ]
  simp only [coe_vadd, ofReal_one]
  rw [show cexp (2 * ↑π * Complex.I * (1 + ↑z)) = cexp (2 * ↑π * Complex.I * (↑z)) by
        simpa using exp_periodo z 1]
  simp only [mul_eq_mul_left_iff, Complex.exp_ne_zero, or_false]
  refine tprod_congr fun b ↦ ?_
  have := exp_periodo z (b + 1)
  simp only [Nat.cast_add, Nat.cast_one] at this
  rw [this]

lemma Discriminant_S_invariant : (Δ ∣[(12 : ℤ)] ModularGroup.S) = Δ := by
  ext z
  rw [modular_slash_S_apply, Delta_eq_eta_pow, Delta_eq_eta_pow]
  have he := eta_equality z.2
  simp only [comp_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul,
    Int.reduceNeg, zpow_neg] at *
  rw [show -1 / (z.1 : ℂ) = (-(z : ℂ))⁻¹ by rw [neg_div, ← neg_inv]; simp] at he
  rw [he, mul_pow, mul_pow, inv_pow, csqrt_I]
  simp only [inv_one, one_mul]
  rw [mul_comm, csqrt_pow_24 z.1 (ne_zero z), ← mul_assoc]
  have hz := ne_zero z
  simp only [ne_eq] at hz
  norm_cast
  field_simp

/-- Δ as a SlashInvariantForm of weight 12 -/
def Discriminant_SIF : SlashInvariantForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Δ
  slash_action_eq' :=
    slashaction_generators_GL2R Δ 12 Discriminant_S_invariant Discriminant_T_invariant

/-- Δ is 1-periodic: Δ(z + 1) = Δ(z) -/
lemma Δ_periodic (z : ℍ) : Δ ((1 : ℝ) +ᵥ z) = Δ z := by
  simpa using SlashInvariantForm.vAdd_width_periodic 1 12 1 Discriminant_SIF z

/-- Δ transforms under S as: Δ(-1/z) = z¹² · Δ(z) -/
lemma Δ_S_transform (z : ℍ) : Δ (ModularGroup.S • z) = z ^ (12 : ℕ) * Δ z := by
  have h := congr_fun Discriminant_S_invariant z
  rw [SL_slash_apply] at h
  simp only [ModularGroup.denom_S, zpow_neg] at h
  field_simp [ne_zero z] at h
  rw [h, mul_comm]

lemma I_in_atImInfty (A : ℝ) : { z : ℍ | A ≤ z.im} ∈ atImInfty := by
  rw [atImInfty_mem]
  exact ⟨A, fun _ h ↦ h⟩

instance natPosSMul : SMul ℕ+ ℍ where
  smul x z := UpperHalfPlane.mk (x * z) <| by simp; apply z.2

theorem natPosSMul_apply (c : ℕ+) (z : ℍ) : ((c • z : ℍ) : ℂ) = (c : ℂ) * (z : ℂ) := rfl

def pnat_smul_stable (S : Set ℍ) := ∀ n : ℕ+, ∀ s ∈ S, n • s ∈ S

lemma atImInfty_pnat_mono (S : Set ℍ) (hS : S ∈ atImInfty) (B : ℝ) : ∃ A : ℝ,
    pnat_smul_stable (S ∩ {z : ℍ | max A B ≤ z.im}) ∧ S ∩ {z : ℍ | max A B ≤ z.im} ∈ atImInfty := by
  have hS2 := hS
  rw [atImInfty_mem] at hS
  obtain ⟨A, hA⟩ := hS
  refine ⟨A, ?_, ?_⟩
  · intro n s hs
    simp only [mem_inter_iff, mem_setOf_eq] at *
    have K : max A B ≤ (n • s).im := by
      rw [UpperHalfPlane.im, natPosSMul_apply]
      simp only [mul_im, natCast_re, coe_im, natCast_im, coe_re, zero_mul, add_zero]
      have hs2 := hs.2
      simp at *
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast PNat.one_le n
      refine ⟨le_trans hs2.1 ?_, le_trans hs2.2 ?_⟩ <;>
        exact (le_mul_iff_one_le_left s.2).mpr hn
    refine ⟨?_, K⟩
    simp at K
    exact hA _ K.1
  · simp only [inter_mem_iff, hS2, true_and]
    exact I_in_atImInfty _

lemma cexp_two_pi_I_im_antimono (a b : ℍ) (h : a.im ≤ b.im) (n : ℕ) :
    ‖cexp (2 * ↑π * Complex.I * n * b)‖ ≤ ‖cexp (2 * ↑π * Complex.I * n * a)‖ := by
  simp_rw [Complex.norm_exp]
  simp
  gcongr

theorem tendsto_neg_cexp_atImInfty (k : ℕ) :
    Tendsto (fun x : ℍ ↦ -cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) atImInfty (𝓝 0) := by
  have h := (Tendsto.neg (f := fun x : ℍ ↦ cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x))
    (l := atImInfty) (y := 0))
  simp only [neg_zero] at h
  refine h ?_
  refine tendsto_exp_nhds_zero_iff.mpr ?_
  simp
  refine Filter.Tendsto.const_mul_atTop (by positivity) ?_
  exact tendsto_iff_comap.mpr fun _ a ↦ a

theorem log_one_neg_cexp_tendsto_zero (k : ℕ) :
    Tendsto (fun x : ℍ ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24))
      atImInfty (𝓝 0) := by
  rw [show (fun x : ℍ ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑k + 1) * ↑x)) ^ 24)) =
      Complex.log ∘ (fun x ↦ x ^ 24) ∘
        (fun x : ℍ ↦ 1 - cexp (2 * π * Complex.I * (k + 1) * x)) by ext x; simp]
  refine Tendsto.comp (y := 𝓝 1) ?_ ?_
  · nth_rw 1 [← Complex.log_one]
    exact ContinuousAt.tendsto (continuousAt_clog (by simp))
  refine Tendsto.comp (y := 𝓝 1) ((continuous_pow 24).tendsto' 1 1 (by simp)) ?_
  simp_rw [sub_eq_add_neg]
  nth_rw 3 [show (1 : ℂ) = 1 + 0 by ring]
  refine Tendsto.add ?_ (tendsto_neg_cexp_atImInfty k)
  simp only [tendsto_const_nhds_iff]


variable {α ι : Type*}

lemma Complex.cexp_tsum_eq_tprod_func (f : ι → α → ℂ) (hfn : ∀ x n, f n x ≠ 0)
    (hf : ∀ x : α, Summable fun n ↦ log (f n x)) :
    (cexp ∘ fun a : α ↦ ∑' n : ι, log (f n a)) = fun a : α ↦ ∏' n : ι, f n a := by
  ext a
  refine (HasProd.tprod_eq ?_).symm
  refine ((hf a).hasSum.cexp).congr fun _ ↦ ?_
  congr
  exact funext fun x ↦ exp_log (hfn a x)

theorem Delta_boundedfactor :
    Tendsto (fun x : ℍ ↦ ∏' (n : ℕ), (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24)
      atImInfty (𝓝 1) := by
  have := Complex.cexp_tsum_eq_tprod_func
    (fun n : ℕ ↦ fun x : ℍ ↦ (1 - cexp (2 * ↑π * Complex.I * (↑n + 1) * ↑x)) ^ 24) ?_ ?_
  conv =>
    enter [1]
    rw [← this]
  · apply Tendsto.comp (y := (𝓝 0))
    · exact Complex.continuous_exp.tendsto' 0 1 Complex.exp_zero
    have := tendsto_tsum_of_dominated_convergence (𝓕 := atImInfty) (g := fun (x : ℕ) ↦ (0 : ℂ))
        (f := (fun x : ℍ ↦ fun (n : ℕ) ↦ Complex.log ((1 - cexp (2 * ↑π * Complex.I * (↑n + 1) *
          (x : ℂ))) ^ 24)))
        (bound := fun k ↦ ‖(24 *((3/2)* cexp (2 * ↑π * Complex.I * (↑k + 1) * Complex.I)))‖)
    simp at this
    apply this
    · apply Summable.mul_left
      apply Summable.mul_left
      simpa using (summable_exp_pow UpperHalfPlane.I)
    · apply log_one_neg_cexp_tendsto_zero
    · have := fun k ↦ (tendsto_neg_cexp_atImInfty k)
      have h0 := this 0
      have h1 := clog_pow2 24 _ h0
      simp only [CharP.cast_eq_zero, zero_add, mul_one, Nat.cast_ofNat] at h1
      rw [Metric.tendsto_nhds] at h0
      have h00 := h0 (1/2) (one_half_pos)
      simp only [CharP.cast_eq_zero, zero_add, mul_one, dist_zero_right, norm_neg, one_div] at h00
      rw [Filter.eventually_iff_exists_mem ] at *
      obtain ⟨a, ha0, ha⟩ := h1
      obtain ⟨a2, ha2, ha3⟩ := h00
      have hminmem: min a a2 ∈ atImInfty := by
        simp only [inf_eq_inter, inter_mem_iff, ha0, ha2, and_self]
      have hT := atImInfty_pnat_mono (min a a2) hminmem 1
      obtain ⟨A, hA, hAmem⟩ := hT
      use (a ⊓ a2) ∩ {z | A ⊔ 1 ≤ z.im}
      refine ⟨hAmem, ?_⟩
      intro b hb k
      let K : ℕ+ := ⟨k+1, Nat.zero_lt_succ k⟩
      have haa := ha (K • b) (by have h8 := hA K b hb; simp only [inf_eq_inter, sup_le_iff,
        mem_inter_iff, mem_setOf_eq] at h8; exact h8.1.1)
      simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, K] at haa
      have := Complex.norm_log_one_add_half_le_self (z := -cexp (2 * ↑π * Complex.I * (↑k + 1) * b))
      rw [sub_eq_add_neg]
      simp_rw [← mul_assoc] at haa
      rw [haa]
      simp only [forall_exists_index, and_imp, gt_iff_lt, CharP.cast_eq_zero, zero_add, mul_one,
        dist_zero_right, norm_neg, inf_eq_inter, inter_mem_iff, sup_le_iff, mem_inter_iff,
        mem_setOf_eq, one_div, Complex.norm_mul, norm_ofNat, Nat.ofNat_pos, mul_le_mul_iff_right₀,
        ge_iff_le] at *
      apply le_trans (this ?_)
      · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_iff_right₀]
        have hr := cexp_two_pi_I_im_antimono UpperHalfPlane.I b (n := k + 1) ?_
        · simpa using hr
        simp only [UpperHalfPlane.I_im, hb.2.2]
      have HH := ha3 (K • b) (by
        have h8 := hA K b hb; simp only [mem_inter_iff, mem_setOf_eq] at h8; exact h8.1.2)
      simp only [natPosSMul_apply, PNat.mk_coe, Nat.cast_add, Nat.cast_one, ← mul_assoc, K] at HH
      exact HH.le
  · intro x n
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff]
    apply term_ne_zero
  · intro x
    simp only
    have := log_summable_pow (fun n ↦ -cexp (2 * ↑π * Complex.I * (↑n + 1) * x)) ?_ 24
    · apply this.congr
      intro b
      rw [sub_eq_add_neg]
    · rw [←summable_norm_iff]
      simpa using (summable_exp_pow x)

open Real

lemma Discriminant_zeroAtImInfty :
    ∀ γ ∈ 𝒮ℒ, IsZeroAtImInfty (Discriminant_SIF ∣[(12 : ℤ)] (γ : GL (Fin 2) ℝ)) := by
  intro γ ⟨γ', hγ⟩
  rw [IsZeroAtImInfty, ZeroAtFilter]
  have h := Discriminant_SIF.slash_action_eq' γ ⟨γ', CongruenceSubgroup.mem_Gamma_one γ', hγ⟩
  simp at *
  rw [h]
  simp [Discriminant_SIF]
  unfold Δ
  rw [show (0 : ℂ) = 0 * 1 by ring]
  refine Tendsto.mul ?_ Delta_boundedfactor
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Complex.norm_exp, mul_re, re_ofNat, ofReal_re, im_ofNat,
    ofReal_im, mul_zero, sub_zero, Complex.I_re, mul_im, zero_mul, add_zero, Complex.I_im,
    mul_one, sub_self, coe_re, coe_im, zero_sub, tendsto_exp_comp_nhds_zero,
    tendsto_neg_atBot_iff]
  rw [Filter.tendsto_const_mul_atTop_iff_pos]
  · exact two_pi_pos
  rw [atImInfty]
  exact tendsto_comap

/-- `Δ` as a cusp form of weight `12` on `SL(2, ℤ)`. -/
def Delta : CuspForm (CongruenceSubgroup.Gamma 1) 12 where
  toFun := Discriminant_SIF
  slash_action_eq' := Discriminant_SIF.slash_action_eq'
  holo' := by
    rw [mdifferentiable_iff]
    simp only [SlashInvariantForm.coe_mk]
    have he2 : DifferentiableOn ℂ (fun z ↦ (η z) ^ 24) {z | 0 < z.im} :=
      DifferentiableOn.pow (fun x hx ↦ DifferentiableAt.differentiableWithinAt <| by
        simpa [η] using ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx) _
    rw [Discriminant_SIF]
    simp only [SlashInvariantForm.coe_mk]
    refine he2.congr fun z hz ↦ ?_
    have := Delta_eq_eta_pow (⟨z, hz⟩ : ℍ)
    simp only [comp_apply] at *
    rw [ofComplex_apply_of_im_pos hz]
    exact this
  zero_at_cusps' hc := zero_at_cusps_of_zero_at_infty hc Discriminant_zeroAtImInfty

lemma Delta_apply (z : ℍ) : Delta z = Δ z := rfl

lemma Delta_isTheta_rexp : Delta =Θ[atImInfty] (fun τ ↦ Real.exp (-2 * π * τ.im)) := by
  rw [Asymptotics.IsTheta]
  refine ⟨by simpa using CuspFormClass.exp_decay_atImInfty (h := 1) Delta, ?_⟩
  rw [Asymptotics.isBigO_iff']
  have hl := Filter.Tendsto.eventually_const_le (one_half_lt_one (α := ℝ))
    (by simpa using Delta_boundedfactor.norm)
  refine ⟨2, by simp, ?_⟩
  rw [Filter.eventually_iff_exists_mem] at *
  obtain ⟨A1, hA1, hA2⟩ := hl
  refine ⟨A1, hA1, fun z hz ↦ ?_⟩
  rw [Delta_apply, Δ]
  simp only [neg_mul, Real.norm_eq_abs, Real.abs_exp, norm_mul]
  have hA3 := hA2 z hz
  conv =>
    enter [2, 2, 1]
    rw [Complex.norm_exp]
  simp only [mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, Complex.I_re,
    mul_im, zero_mul, add_zero, Complex.I_im, mul_one, sub_self, coe_re, coe_im, zero_sub]
  have h4 := mul_le_mul_of_nonneg_left hA3 (by positivity : (0 : ℝ) ≤ 2 * rexp (-(2 * π * z.im)))
  conv at h4 =>
    enter [1]
    rw [mul_comm, ← mul_assoc]
    simp
  simp only [one_div, ge_iff_le] at *
  rw [← mul_assoc]
  exact h4

lemma CuspForm_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) (z : ℍ) :
    f.toFun z = f z := rfl

theorem div_Delta_is_SIF (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma 1)) :
    (⇑f / ⇑Delta) ∣[k - 12] γ = ⇑f / ⇑Delta := by
  simp only [Subgroup.mem_map] at hγ
  obtain ⟨γ, hA₁, hA₂⟩ := hγ
  rw [← hA₂]
  ext z
  change ((⇑f / ⇑Delta) ∣[k - 12] γ) z = (⇑f / ⇑Delta) z
  rw [ModularForm.slash_action_eq'_iff (k - 12) _ γ]
  have h0 : (⇑f / ⇑Delta) z = (⇑f z / ⇑Delta z) := rfl
  have h1 : (⇑f / ⇑Delta) (γ • z) = (⇑f (γ • z) / ⇑Delta (γ • z)) := rfl
  have h2 : (f.toFun ∣[k] γ) z = f.toFun z :=
    congrFun (f.slash_action_eq' _
      (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hA₁)) z
  have h3 : (Delta.toFun ∣[(12 : ℤ)] γ) z = Delta.toFun z :=
    congrFun (Delta.slash_action_eq' _
      (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) hA₁)) z
  rw [ModularForm.slash_action_eq'_iff, CuspForm_apply, CuspForm_apply] at h2 h3
  rw [h0, h1, h2, h3, Delta_apply]
  have hD := Δ_ne_zero z
  have := pow_ne_zero 12 (denom_ne_zero γ z)
  rw [ModularGroup.denom_apply] at this
  ring_nf
  nth_rw 2 [mul_comm]
  rw [← inv_zpow, inv_zpow']
  simp_rw [← mul_assoc]
  rw [zpow_add₀ (by apply denom_ne_zero γ z)]
  ring

/-- Division by `Δ` as a map from cusp forms of weight `k` to modular forms of weight `k - 12`. -/
def CuspForm_div_Discriminant (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k) :
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
  toFun := f / Delta
  slash_action_eq' γ hγ := div_Delta_is_SIF _ _ γ hγ
  holo' := by
    rw [mdifferentiable_iff]
    simp only [SlashInvariantForm.coe_mk]
    rw [show (⇑f / ⇑Delta) ∘ ↑ofComplex = (⇑f ∘ ↑ofComplex) / (Delta ∘ ↑ofComplex) from rfl]
    refine DifferentiableOn.div ?_ ?_ ?_
    · simpa only [CuspForm.toSlashInvariantForm_coe] using
        UpperHalfPlane.mdifferentiable_iff.mp f.holo'
    · simpa only [CuspForm.toSlashInvariantForm_coe] using
        UpperHalfPlane.mdifferentiable_iff.mp Delta.holo'
    · intro x hx
      have := Δ_ne_zero ⟨x, hx⟩
      simp only [comp_apply, ne_eq]
      rwa [ofComplex_apply_of_im_pos hx]
  bdd_at_cusps' {c} hc := by
    refine bounded_at_cusps_of_bounded_at_infty hc fun A ⟨A', hA'⟩ ↦ ?_
    have h1 := CuspFormClass.exp_decay_atImInfty (h := 1) f zero_lt_one (by simp)
    have h2 := Delta_isTheta_rexp.2
    rw [IsBoundedAtImInfty, BoundedAtFilter] at *
    rw [Asymptotics.isBigO_iff'] at h1 ⊢
    rw [Asymptotics.isBigO_iff''] at h2
    simp only [neg_mul, div_one, Real.norm_eq_abs, Real.abs_exp,
      Pi.one_apply, norm_one, mul_one] at *
    obtain ⟨e1, he1, hf⟩ := h1
    obtain ⟨e2, he2, hD⟩ := h2
    refine ⟨e1 / e2, by positivity, ?_⟩
    rw [eventually_iff_exists_mem] at *
    obtain ⟨A1, hA, hA2⟩ := hf
    obtain ⟨B2, hB2, hB3⟩ := hD
    refine ⟨min A1 B2, by simp [hA, hB2], fun z hz ↦ ?_⟩
    have heq : ((⇑f / ⇑Delta) ∣[k - 12] (A : GL (Fin 2) ℝ)) z = (⇑f z / ⇑Delta z) := by
      have := congrFun (div_Delta_is_SIF k f A'
        (Subgroup.mem_map.mp ⟨A', CongruenceSubgroup.mem_Gamma_one A', rfl⟩)) z
      rw [← hA']
      simpa [SL_slash, Pi.div_apply] using this
    rw [heq]
    simp
    rw [show e1 / e2 = (e1 * rexp (-(2 * π * z.im))) / (e2 * rexp (-(2 * π * z.im))) from
      (mul_div_mul_right e1 e2 (Real.exp_ne_zero _)).symm]
    refine div_le_div₀ (by positivity) (hA2 _ hz.1) (by positivity) (hB3 _ hz.2)

lemma CuspForm_div_Discriminant_apply (k : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma 1) k)
    (z : ℍ) : (CuspForm_div_Discriminant k f) z = f z / Δ z := rfl

theorem CuspForm_div_Discriminant_Add (k : ℤ) (x y : CuspForm (CongruenceSubgroup.Gamma 1) k) :
    (fun f ↦ CuspForm_div_Discriminant k f) (x + y) =
      (fun f ↦ CuspForm_div_Discriminant k f) x + (fun f ↦ CuspForm_div_Discriminant k f) y := by
  ext z
  simp only [CuspForm_div_Discriminant_apply, CuspForm.add_apply, ModularForm.add_apply]
  ring

private lemma cexp_two_pi_I_mul_I_eq_rexp (t : ℝ) :
    cexp (2 * ↑π * Complex.I * (Complex.I * t)) = rexp (-2 * π * t) := by
  calc
    _ = cexp (2 * ↑π * (Complex.I * Complex.I) * t) := by ring_nf
    _ = rexp (-2 * π * t) := by simp

private lemma cexp_two_pi_I_succ_mul_I_eq_rexp (t : ℝ) (n : ℕ) :
    cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t)) = rexp (-(2 * π * (n + 1) * t)) := by
  calc
    _ = cexp (2 * ↑π * (n + 1) * (Complex.I * Complex.I) * t) := by ring_nf
    _ = rexp (-(2 * π * (n + 1) * t)) := by simp

private lemma one_sub_rexp_pos (t : ℝ) (n : ℕ) (ht : 0 < t) :
    0 < 1 - rexp (-(2 * π * (n + 1) * t)) := by
  have : rexp (-(2 * π * (n + 1) * t)) < 1 := exp_lt_one_iff.mpr (by simp; positivity)
  linarith

private lemma cexp_neg_two_pi_succ_mul_im (t : ℝ) (n : ℕ) :
    (cexp (-2 * π * (n + 1) * t)).im = 0 := by
  simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-2 * π * (n + 1) * t)

private lemma cexp_neg_two_pi_mul_im (t : ℝ) : (cexp (-(2 * π * t))).im = 0 := by
  simpa [Complex.ofReal_mul, Complex.ofReal_neg] using exp_ofReal_im (-(2 * π * t))

lemma Complex.im_finset_prod_eq_zero_of_im_eq_zero {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) (h : ∀ i ∈ s, (f i).im = 0) :
    (∏ i ∈ s, f i).im = 0 := by
  classical
  revert h
  refine Finset.induction_on s (fun _ ↦ by simp) ?_
  intro a s ha ih h
  simp [Finset.prod_insert, ha, Complex.mul_im, h a (by simp),
    ih (fun i hi ↦ h i (by simp [hi]))]

lemma Complex.im_pow_eq_zero_of_im_eq_zero {z : ℂ} (hz : z.im = 0) (m : ℕ) :
    (z ^ m).im = 0 := by
  induction m with
  | zero => simp
  | succ m ih => simp [pow_succ, Complex.mul_im, *]

lemma Complex.im_tprod_eq_zero_of_im_eq_zero (f : ℕ → ℂ)
    (hf : Multipliable f) (him : ∀ n, (f n).im = 0) :
    (∏' n : ℕ, f n).im = 0 := by
  classical
  have hz : ∀ n, (∏ i ∈ Finset.range n, f i).im = 0 := fun n ↦
    Complex.im_finset_prod_eq_zero_of_im_eq_zero (s := Finset.range n) (f := f)
      (by intro i _; simpa using him i)
  have h1 := ((Complex.continuous_im.tendsto _).comp hf.hasProd.tendsto_prod_nat)
  have h2 : Tendsto (fun n ↦ (∏ i ∈ Finset.range n, f i).im) atTop (𝓝 (0 : ℝ)) := by simp [hz]
  exact tendsto_nhds_unique h1 h2

/-- `Δ(it)` is real on the positive imaginary axis. -/
lemma Delta_imag_axis_real : ResToImagAxis.Real Δ := by
  intro t ht
  simp [ResToImagAxis, ht, Δ]
  set g : ℕ → ℂ := fun n ↦ (1 - cexp (2 * π * Complex.I * (n + 1) * (Complex.I * t))) ^ 24
  have hArg (n : ℕ) :
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t) = -(2 * (π : ℂ) * (n + 1) * t) := by
    calc
      2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t)
        = 2 * (π : ℂ) * (Complex.I * Complex.I) * (n + 1) * t := by ring
      _ = -(2 * (π : ℂ) * (n + 1) * t) := by simp
  have him_g : ∀ n, (g n).im = 0 := fun n ↦ by
    have : (cexp (-(2 * (π : ℂ) * ((n + 1) : ℂ) * t))).im = 0 := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using cexp_neg_two_pi_succ_mul_im t n
    have : ((1 - cexp (2 * (π : ℂ) * Complex.I * (n + 1) * (Complex.I * t))) : ℂ).im = 0 := by
      simpa [Complex.sub_im, hArg n] using this
    simpa [g] using Complex.im_pow_eq_zero_of_im_eq_zero this 24
  let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
  have hmul : Multipliable g := by
    have hz : (z : ℂ) = Complex.I * t := rfl
    simpa [g, hz] using
      (Multipliable_pow _ (by simpa using MultipliableEtaProductExpansion z) 24)
  have htprod_im : (∏' n : ℕ, g n).im = 0 :=
    Complex.im_tprod_eq_zero_of_im_eq_zero g hmul him_g
  have him_pref : (cexp (2 * π * Complex.I * (Complex.I * t))).im = 0 := by
    have : (cexp (-(2 * (π : ℂ) * t))).im = 0 := by simpa using cexp_neg_two_pi_mul_im t
    simpa [by simpa using hArg 0] using this
  simp [g, him_pref, htprod_im]

lemma re_ResToImagAxis_Delta_eq_real_prod (t : ℝ) (ht : 0 < t) :
    (Δ.resToImagAxis t).re =
      Real.exp (-2 * π * t) *
        ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
  set fR : ℕ → ℝ := fun n ↦ (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24
  have hMap' : Complex.ofReal (∏' n : ℕ, fR n) = ∏' n : ℕ, ((fR n : ℝ) : ℂ) := by
    simpa using Function.LeftInverse.map_tprod (f := fR)
      (g := Complex.ofRealHom.toMonoidHom)
      (hg := by simpa using Complex.continuous_ofReal)
      (hg' := Complex.continuous_re)
      (hgg' := by intro x; simp)
  simpa [ResToImagAxis, ht, Delta_apply, Δ, cexp_two_pi_I_mul_I_eq_rexp,
    cexp_two_pi_I_succ_mul_I_eq_rexp, hMap', fR] using
    Complex.ofReal_re (Real.exp (-2 * π * t) * ∏' n : ℕ, fR n)

lemma tprod_pos_nat_im (z : ℍ) :
    0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := by
  have hpos_pow : ∀ n : ℕ, 0 < (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24 := fun n ↦
    pow_pos (by simpa [mul_comm, mul_left_comm, mul_assoc] using
      one_sub_rexp_pos (t := z.im) n z.2) _
  have hsum_log : Summable fun n : ℕ ↦
      Real.log ((1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24) := by
    simp only [Real.log_pow, Nat.cast_ofNat, ← smul_eq_mul]
    refine Summable.const_smul _ ?_
    simp [sub_eq_add_neg]
    refine Real.summable_log_one_add_of_summable (Summable.neg ?_)
    have h0 : Summable fun n : ℕ ↦ Real.exp (n * (-(2 * π * z.im))) :=
      Real.summable_exp_nat_mul_iff.mpr
        (by simpa using neg_lt_zero.mpr (by positivity : 0 < 2 * π * z.im))
    simpa [Nat.cast_add, Nat.cast_one, mul_comm, mul_left_comm, mul_assoc] using
      (summable_nat_add_iff 1).2 h0
  rw [← Real.rexp_tsum_eq_tprod
    (f := fun n : ℕ ↦ (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * z.im))) ^ 24) hpos_pow hsum_log]
  exact Real.exp_pos _

/-- `Δ(it)` is positive on the positive imaginary axis. -/
lemma Delta_imag_axis_pos : ResToImagAxis.Pos Δ := by
  rw [ResToImagAxis.Pos]
  refine ⟨Delta_imag_axis_real, fun t ht ↦ ?_⟩
  have hprod : 0 < ∏' (n : ℕ), (1 - Real.exp (-(2 * π * ((n + 1) : ℝ) * t))) ^ 24 := by
    let z : ℍ := ⟨Complex.I * t, by simp [ht]⟩
    have hz : z.im = t := by simp [UpperHalfPlane.im, z]
    simpa [hz] using tprod_pos_nat_im z
  rw [re_ResToImagAxis_Delta_eq_real_prod t ht]
  exact mul_pos (Real.exp_pos _) hprod
