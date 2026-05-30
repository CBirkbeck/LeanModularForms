/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.NumberTheory.ModularForms.LevelOne
public import LeanModularForms.Modularforms.Eisenstein
public import LeanModularForms.Modularforms.DimGenCongLevels.Basic
public import LeanModularForms.Modularforms.DimGenCongLevels.NormReduction
public import LeanModularForms.Modularforms.DimGenCongLevels.FiniteDimensional
public import LeanModularForms.Modularforms.DimGenCongLevels.NormTransfer

@[expose] public section

/-!
# Dimension formulas for level-one modular forms

This file proves the classical dimension formula for the space of modular forms of weight
`k` for the full modular group `SL₂(ℤ)`. The argument peels off one factor of the
discriminant `Δ` to relate weight `k` to weight `k - 12`, using the explicit identification
`Δ = (E₄³ - E₆²)/1728` to handle the base cases.

## Main results

* `ModularForm.dimension_level_one`: the dimension formula
  `dim_ℂ M_k(SL₂(ℤ)) = ⌊k/12⌋ + 1` (or `⌊k/12⌋` when `12 ∣ k - 2`)
  for even `k ≥ 3`.
* `finiteDimensional_modularForm_level_one`: every space of level-one modular forms is
  finite-dimensional, including the odd-weight and negative-weight cases.
* `finiteDimensional_modularForm_SL2Z`: finite-dimensionality transferred to the
  GL₂(ℝ)-side subgroup `𝒮ℒ`.
* `dim_gen_cong_levels`: finite-dimensionality for any finite-index congruence subgroup.

-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

def mul_Delta_map (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    ModularForm (CongruenceSubgroup.Gamma 1) k :=
  ModularForm.mcast (by ring : k - 12 + 12 = k) (f.mul (ModForm_mk _ 12 Delta))

lemma mcast_apply {a b : ℤ} {Γ : Subgroup SL(2, ℤ)} (h : a = b) (f : ModularForm Γ a) (z : ℍ) :
    (ModularForm.mcast h f) z = f z := rfl

lemma mul_Delta_map_eq (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) (z : ℍ) :
    (mul_Delta_map k f) z = f z * Delta z := by
  rw [mul_Delta_map, mcast_apply]
  rfl

lemma mul_Delta_map_eq_mul (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    ((mul_Delta_map k f) : ℍ → ℂ) = (f.mul (ModForm_mk _ 12 Delta)) := by
  ext z
  rw [mul_Delta_map, mcast_apply]

lemma qExpansion_coe_smul {n : ℕ} [NeZero n] {k : ℤ} (a : ℂ) (f : ModularForm Γ(n) k) :
    qExpansion n (⇑(a • f)) = qExpansion n (a • ⇑f) := rfl

lemma qExpansion_coe_smul_cusp {n : ℕ} [NeZero n] {k : ℤ} (a : ℂ) (f : CuspForm Γ(n) k) :
    qExpansion n (⇑(a • f)) = qExpansion n (a • ⇑f) := rfl

lemma qExpansion_coe_sub {k : ℤ} (f g : ModularForm Γ(1) k) :
    qExpansion (1 : ℕ) (⇑(f - g)) = qExpansion (1 : ℕ) (⇑f - ⇑g) := rfl

lemma mul_Delta_IsCuspForm (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    IsCuspForm (CongruenceSubgroup.Gamma 1) k (mul_Delta_map k f) := by
  rw [IsCuspForm_iff_coeffZero_eq_zero, qExpansion_ext2 _ _ (mul_Delta_map_eq_mul k f),
    ← Nat.cast_one (R := ℝ), qExpansion_mul_coeff]
  simp only [PowerSeries.coeff_mul, Finset.antidiagonal_zero, Prod.mk_zero_zero,
    Finset.sum_singleton, Prod.fst_zero, Prod.snd_zero, mul_eq_zero]
  right
  rw [Nat.cast_one, ← IsCuspForm_iff_coeffZero_eq_zero, IsCuspForm, CuspFormSubmodule,
    CuspForm_to_ModularForm]
  simp

def Modform_mul_Delta' (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12)) :
    CuspForm (CongruenceSubgroup.Gamma 1) k :=
  IsCuspForm_to_CuspForm _ k (mul_Delta_map k f) (mul_Delta_IsCuspForm k f)

theorem mul_apply {k₁ k₂ : ℤ} {Γ : Subgroup SL(2, ℤ)} (f : SlashInvariantForm Γ k₁)
    (g : SlashInvariantForm Γ k₂) (z : ℍ) : (f.mul g) z = f z * g z := rfl

lemma Modform_mul_Delta_apply (k : ℤ) (f : ModularForm (CongruenceSubgroup.Gamma 1) (k - 12))
    (z : ℍ) : (Modform_mul_Delta' k f) z = f z * Delta z := by
  rw [Modform_mul_Delta']
  have := congr_fun
    (CuspForm_to_ModularForm_Fun_coe _ _ (mul_Delta_map k f) (mul_Delta_IsCuspForm k f)) z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
    toSlashInvariantForm_coe] at this
  rw [mul_Delta_map_eq] at this
  exact this

def CuspForms_iso_Modforms (k : ℤ) : CuspForm (CongruenceSubgroup.Gamma 1) k ≃ₗ[ℂ]
    ModularForm (CongruenceSubgroup.Gamma 1) (k - 12) where
  toFun f := CuspForm_div_Discriminant k f
  map_add' a b := CuspForm_div_Discriminant_Add k a b
  map_smul' m a := by
    ext z
    simp only [CuspForm_div_Discriminant_apply, CuspForm.IsGLPos.smul_apply, smul_eq_mul,
      RingHom.id_apply, IsGLPos.smul_apply]
    exact mul_div_assoc m (a z) (Δ z)
  invFun := Modform_mul_Delta' k
  left_inv f := by
    ext z
    simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply]
    rw [Delta_apply, div_mul_cancel₀]
    apply Δ_ne_zero
  right_inv f := by
    ext z
    simp [Modform_mul_Delta_apply, CuspForm_div_Discriminant_apply]
    rw [Delta_apply, mul_div_cancel_right₀]
    apply Δ_ne_zero

lemma delta_eq_E4E6_const : ∃ (c : ℂ), (c • Delta) = Delta_E4_E6_aux := by
  have hr : Module.finrank ℂ (CuspForm Γ(1) 12) = 1 := by
    apply Module.finrank_eq_of_rank_eq
    rw [LinearEquiv.rank_eq (CuspForms_iso_Modforms 12)]
    simp
    exact ModularForm.levelOne_weight_zero_rank_one
  exact (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).mp hr Delta_E4_E6_aux

lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) :
    Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  rw [LinearEquiv.rank_eq (CuspForms_iso_Modforms k)]
  exact ModularForm.levelOne_neg_weight_rank_zero (by linarith)

lemma IsCuspForm_weight_lt_eq_zero (k : ℤ) (hk : k < 12) (f : ModularForm Γ(1) k)
    (hf : IsCuspForm Γ(1) k f) : f = 0 := by
  have hfc2 := CuspForm_to_ModularForm_coe _ _ f hf
  ext z
  have hz := congr_fun (congr_arg (fun x ↦ x.1) hfc2) z
  simp only [SlashInvariantForm.toFun_eq_coe, CuspForm.toSlashInvariantForm_coe,
    toSlashInvariantForm_coe] at hz
  rw [ModularForm.zero_apply, ← hz,
    rank_zero_iff_forall_zero.mp (cuspform_weight_lt_12_zero k hk)
      (IsCuspForm_to_CuspForm Γ(1) k f hf)]
  simp only [CuspForm.zero_apply]

lemma Delta_E4_E6_eq : ModForm_mk _ _ Delta_E4_E6_aux =
    ((1/ 1728 : ℂ) • (((DirectSum.of _ 4 E₄)^3 - (DirectSum.of _ 6 E₆)^2) 12)) := by
  ext
  rfl

lemma Delta_E4_E6_aux_q_one_term : (qExpansion 1 Delta_E4_E6_aux).coeff 1 = 1 := by
  have h1 : (qExpansion 1 Delta_E4_E6_aux) = qExpansion 1 (ModForm_mk Γ(1) 12 Delta_E4_E6_aux) := by
    refine qExpansion_ext2 Delta_E4_E6_aux (ModForm_mk Γ(1) 12 Delta_E4_E6_aux) ?_
    ext z
    rw [Delta_E4_E6_aux, ModForm_mk]
    simp
    rfl
  rw [h1, Delta_E4_E6_eq]
  simp only [one_div, DirectSum.sub_apply]
  let A : ModularForm Γ(1) 12 := (((DirectSum.of _ 4 E₄) ^ 3) 12)
  let B : ModularForm Γ(1) 12 := (((DirectSum.of _ 6 E₆) ^ 2) 12)
  change (PowerSeries.coeff 1) (qExpansion 1 ((1728⁻¹ : ℂ) • ((A - B : ModularForm Γ(1) 12)))) = 1
  rw [← Nat.cast_one (R := ℝ), ← qExpansion_smul2]
  have hsub2 : qExpansion 1 (⇑A - ⇑B) = qExpansion 1 ⇑A - qExpansion 1 ⇑B := by
    simpa using (qExpansion_sub (Γ := Γ(1)) (h := (1 : ℕ))
      (hh := by positivity) (hΓ := by simp) (f := A) (g := B))
  have hmain : (PowerSeries.coeff 1) ((1728⁻¹ : ℂ) • (qExpansion 1 ⇑A - qExpansion 1 ⇑B)) = 1 := by
    have h4 := qExpansion_pow E₄ 3
    have h6 := qExpansion_pow E₆ 2
    simp only [Nat.cast_ofNat, Int.reduceMul] at h4 h6
    have hA : qExpansion 1 A = (qExpansion 1 E₄) ^ 3 := by simpa [A] using h4
    have hB : qExpansion 1 B = (qExpansion 1 E₆) ^ 2 := by simpa [B] using h6
    rw [hA, hB]
    simp
    rw [pow_three, pow_two]
    simp_rw [PowerSeries.coeff_mul]
    rw [antidiagonal_one]
    simp [Finset.mem_singleton, Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self,
      not_false_eq_true, Finset.sum_insert, Finset.antidiagonal_zero, Prod.mk_zero_zero,
      Finset.sum_singleton, Prod.fst_zero, Prod.snd_zero]
    have he4 := E4_q_exp_zero
    have he6 := E6_q_exp_zero
    simp only [PowerSeries.coeff_zero_eq_constantCoeff] at he4 he6
    simp_rw [E4_q_exp_one, he4, he6]
    ring_nf
    rw [antidiagonal_one]
    simp [Finset.mem_singleton, Prod.mk.injEq, one_ne_zero, zero_ne_one, and_self,
      not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
    simp_rw [E4_q_exp_one, he4, E6_q_exp_one]
    ring
  simpa [hsub2] using hmain

theorem Delta_eq_Delta_E4_E6_aux : Delta = Delta_E4_E6_aux := by
  ext z
  obtain ⟨c, H⟩ := delta_eq_E4E6_const
  suffices h2 : c = 1 by
    rw [h2] at H
    simp at H
    rw [H]
  have h2 := Delta_E4_E6_aux_q_one_term
  rw [← H] at h2
  have hs := (qExpansion_smul (Γ := Γ(1)) (h := (1 : ℕ))
    (hh := by positivity) (hΓ := by simp) c Delta).symm
  rw [show qExpansion 1 ⇑(c • Delta) = qExpansion 1 (c • ⇑Delta) from rfl,
    ← Nat.cast_one (R := ℝ), ← hs] at h2
  simp at h2
  rw [Delta_q_one_term] at h2
  simpa using h2

lemma weight_eight_one_dimensional (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [rank_eq_one_iff]
  refine ⟨E k hk, Ek_ne_zero k hk hk2, ?_⟩
  by_contra h
  simp at h
  obtain ⟨f, hf⟩ := h
  by_cases hf2 : IsCuspForm Γ(1) k f
  · have hfc1 := hf 0
    simp at *
    have := IsCuspForm_weight_lt_eq_zero k (by simpa using hk3) f hf2
    aesop
  have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 :=
    fun h ↦ hf2 ((IsCuspForm_iff_coeffZero_eq_zero (k := (k : ℤ)) f).mpr h)
  set c := (qExpansion 1 f).coeff 0 with hc
  have hcusp : IsCuspForm Γ(1) k (E k hk - c⁻¹ • f) := by
    rw [IsCuspForm_iff_coeffZero_eq_zero, ← Nat.cast_one (R := ℝ), qExpansion_coe_sub,
      qExpansion_sub (Γ := Γ(1)) (h := (1 : ℕ)) (hh := by positivity) (hΓ := by simp)]
    have hnorm0 := modularForm_normalise f hf2
    have hcInv : c⁻¹ = ((PowerSeries.coeff 0) (qExpansion 1 ⇑f))⁻¹ := by simp [hc]
    have hnorm : (PowerSeries.coeff 0) (qExpansion 1 ⇑(c⁻¹ • f)) = 1 := by
      calc
        (PowerSeries.coeff 0) (qExpansion 1 ⇑(c⁻¹ • f)) =
            (PowerSeries.coeff 0) (qExpansion 1 (c⁻¹ • ⇑f)) := by rfl
        _ = (PowerSeries.coeff 0)
            (qExpansion 1 (((PowerSeries.coeff 0) (qExpansion 1 ⇑f))⁻¹ • ⇑f)) := by
            simp [hcInv]
        _ = 1 := hnorm0
    have hnorm' : PowerSeries.constantCoeff (qExpansion 1 (c⁻¹ • ⇑f)) = 1 := by
      simpa [PowerSeries.constantCoeff] using hnorm
    simp [map_sub, Ek_q_exp_zero k hk hk2, hnorm']
  have := IsCuspForm_weight_lt_eq_zero k (by simpa using hk3) (E k hk - c⁻¹ • f) hcusp
  have hfc := hf c
  rw [sub_eq_zero] at this
  aesop

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 :=
  weight_eight_one_dimensional 4 (by norm_num) ⟨2, rfl⟩ (by norm_num)

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 :=
  weight_eight_one_dimensional 6 (by norm_num) ⟨3, rfl⟩ (by norm_num)

private lemma weight_two_c4_eq_coeff_sq (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) (c4 : ℂ)
    (hc4 : c4 • E₄ = f.mul f) : c4 = ((qExpansion 1 f).coeff 0) ^ 2 := by
  have := qExpansion_mul_coeff 1 2 2 f f
  rw [← hc4, qExpansion_coe_smul (a := c4) (f := E₄), ← qExpansion_smul2 1 c4] at this
  have hh := congr_arg (fun x ↦ x.coeff 0) this
  simp only [_root_.map_smul, smul_eq_mul] at hh
  rw [Nat.cast_one, E4_q_exp_zero] at hh
  rw [pow_two]
  simpa using hh

private lemma weight_two_c6_eq_coeff_cube (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) (c6 : ℂ)
    (hc6 : c6 • E₆ = (f.mul f).mul f) : c6 = ((qExpansion 1 f).coeff 0) ^ 3 := by
  have := qExpansion_mul_coeff 1 4 2 (f.mul f) f
  have h2 := qExpansion_mul_coeff 1 2 2 f f
  rw [← hc6, qExpansion_coe_smul (a := c6) (f := E₆), ← qExpansion_smul2 1 c6, h2] at this
  have hh := congr_arg (fun x ↦ x.coeff 0) this
  simp only [_root_.map_smul, smul_eq_mul] at hh
  rw [Nat.cast_one, E6_q_exp_zero] at hh
  rw [pow_three]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd, mul_one, map_mul] at *
  rw [← mul_assoc]
  exact hh

private lemma weight_two_coeff_pow_six_smul_delta_eq_zero
    (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) (c4 c6 : ℂ) (hc4 : c4 • E₄ = f.mul f)
    (hc6 : c6 • E₆ = (f.mul f).mul f) (hc4e : c4 = ((qExpansion 1 f).coeff 0) ^ 2)
    (hc6e : c6 = ((qExpansion 1 f).coeff 0) ^ 3) :
    ((qExpansion 1 f).coeff 0) ^ 6 • (DirectSum.of _ 12 (ModForm_mk Γ(1) 12 Delta) 12) = 0 := by
  let F := DirectSum.of _ 2 f
  have HF2 : (F ^ 2) = c4 • (DirectSum.of _ 4 E₄) := by
    rw [← DirectSum.of_smul, hc4]
    simp [F]
    rw [pow_two, DirectSum.of_mul_of]
    rfl
  have HF3 : (F ^ 3) = c6 • (DirectSum.of _ 6 E₆) := by
    rw [← DirectSum.of_smul, hc6]
    simp [F]
    rw [pow_three, ← mul_assoc, DirectSum.of_mul_of, DirectSum.of_mul_of]
    rfl
  have HF12 : (((F ^ 2) ^ 3) 12) = ((qExpansion 1 f).coeff 0) ^ 6 • (E₄.mul (E₄.mul E₄)) := by
    rw [HF2, pow_three]
    simp
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of, hc4e, smul_smul, smul_smul]
    ring_nf
    rw [DirectSum.smul_apply]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd, DirectSum.of_eq_same]
    rfl
  have hF2 : (((F ^ 3) ^ 2) 12) = ((qExpansion 1 f).coeff 0) ^ 6 • ((E₆.mul E₆)) := by
    rw [HF3, pow_two]
    simp only [Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Int.reduceAdd,
      PowerSeries.coeff_zero_eq_constantCoeff]
    rw [DirectSum.of_mul_of, hc6e, smul_smul]
    ring_nf
    rw [DirectSum.smul_apply]
    simp only [PowerSeries.coeff_zero_eq_constantCoeff, Int.reduceAdd, DirectSum.of_eq_same]
    rfl
  have V : (1 / 1728 : ℂ) • ((((F ^ 2) ^ 3) 12) - (((F ^ 3) ^ 2) 12)) =
      ((qExpansion 1 f).coeff 0) ^ 6 • (DirectSum.of _ 12 (ModForm_mk Γ(1) 12 Delta) 12) := by
    rw [HF12, hF2]
    simp only [one_div, Int.reduceAdd, PowerSeries.coeff_zero_eq_constantCoeff,
      DirectSum.of_eq_same]
    rw [Delta_eq_Delta_E4_E6_aux, Delta_E4_E6_eq, pow_two, pow_three, DirectSum.of_mul_of,
      DirectSum.of_mul_of, DirectSum.of_mul_of]
    simp only [one_div, Int.reduceAdd, DirectSum.sub_apply, DirectSum.of_eq_same]
    ext y
    simp only [IsGLPos.smul_apply, sub_apply, Int.reduceAdd, smul_eq_mul]
    ring_nf
    rfl
  have ht : (1 / 1728 : ℂ) • ((((F ^ 2) ^ 3) 12) - (((F ^ 3) ^ 2) 12)) = 0 := by
    ext y
    simp only [one_div, IsGLPos.smul_apply, sub_apply, smul_eq_mul, zero_apply, mul_eq_zero,
      inv_eq_zero, OfNat.ofNat_ne_zero, false_or, F]
    ring_nf
  rw [ht] at V
  exact V.symm

lemma weight_two_zero (f : ModularForm (CongruenceSubgroup.Gamma 1) 2) : f = 0 := by
  by_cases hf : IsCuspForm (CongruenceSubgroup.Gamma 1) 2 f
  · exact IsCuspForm_weight_lt_eq_zero 2 (by norm_num) f hf
  have hc1 : (qExpansion 1 f).coeff 0 ≠ 0 := fun h ↦
    hf ((IsCuspForm_iff_coeffZero_eq_zero (k := 2) f).mpr h)
  obtain ⟨c6, hc6⟩ := exists_smul_eq_of_rank_one' weight_six_one_dimensional E6_ne_zero
    ((f.mul f).mul f)
  obtain ⟨c4, hc4⟩ := exists_smul_eq_of_rank_one' weight_four_one_dimensional E4_ne_zero
    (f.mul f)
  exfalso
  have V := weight_two_coeff_pow_six_smul_delta_eq_zero f c4 c6 hc4 hc6
    (weight_two_c4_eq_coeff_sq f c4 hc4) (weight_two_c6_eq_coeff_cube f c6 hc6)
  have hr := congr_fun (congr_arg (fun x ↦ x.toFun) V) UpperHalfPlane.I
  simp only [SlashInvariantForm.toFun_eq_coe, toSlashInvariantForm_coe, zero_apply,
    PowerSeries.coeff_zero_eq_constantCoeff, DirectSum.of_eq_same, IsGLPos.smul_apply,
    smul_eq_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
    mul_eq_zero] at hr
  rcases hr with h | h
  · exact hc1 (by rwa [PowerSeries.coeff_zero_eq_constantCoeff])
  · simp only [ModForm_mk] at h
    exact (Delta_apply UpperHalfPlane.I ▸ Δ_ne_zero UpperHalfPlane.I) h

lemma dim_modforms_eq_one_add_dim_cuspforms (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) =
      1 + Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
  have h1 : Module.rank ℂ (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k) =
      Module.rank ℂ (CuspForm (CongruenceSubgroup.Gamma 1) k) := by
    simpa using LinearEquiv.rank_eq (CuspForm_iso_CuspFormSubmodule Γ(1) k).symm
  rw [← h1, ← Submodule.rank_quotient_add_rank (CuspFormSubmodule (CongruenceSubgroup.Gamma 1) k)]
  congr
  rw [rank_eq_one_iff]
  refine ⟨Submodule.Quotient.mk (E k hk), ?_, ?_⟩
  · intro hq
    rw [Submodule.Quotient.mk_eq_zero, CuspFormSubmodule_mem_iff_coeffZero_eq_zero,
      Ek_q_exp_zero k hk hk2] at hq
    simp at hq
  · intro v
    obtain ⟨f, rfl⟩ := Quotient.exists_rep v
    refine ⟨(qExpansion 1 f).coeff 0, ?_⟩
    change Submodule.Quotient.mk (((qExpansion 1 f).coeff 0) • E k hk) = Submodule.Quotient.mk f
    rw [Submodule.Quotient.eq, CuspFormSubmodule_mem_iff_coeffZero_eq_zero]
    let c : ℂ := (qExpansion 1 f).coeff 0
    change (PowerSeries.coeff 0) (qExpansion 1 ⇑(c • E k hk - f)) = 0
    have hqsub : qExpansion 1 ⇑(c • E k hk - f) =
        qExpansion 1 ⇑(c • E k hk) - qExpansion 1 ⇑f := by
      simpa using
        (qExpansion_sub (Γ := Γ(1)) (h := (1 : ℕ)) (hh := by positivity) (hΓ := by simp)
          (f := c • E k hk) (g := f))
    have hsmul : qExpansion 1 ⇑(c • E k hk) = c • qExpansion 1 (E k hk) := by
      simpa using (qExpansion_smul2 1 c (E k hk)).symm
    rw [hqsub, hsmul, ← Nat.cast_one (R := ℝ)]
    simp [PowerSeries.coeff_zero_eq_constantCoeff, map_sub, smul_eq_mul, Ek_q_exp_zero k hk hk2, c]

theorem dim_weight_two : Module.rank ℂ (ModularForm Γ(1) ↑2) = 0 := by
  rw [rank_zero_iff_forall_zero]
  exact weight_two_zero

lemma Nat_floor_div_sub (k a : ℚ) (ha : 0 < a) (hak : a ≤ k) :
    1 + Nat.floor ((k - a) / a) = Nat.floor (k / a) := by
  rw [div_sub_same ha.ne']
  have := Nat.floor_sub_one (k / a)
  norm_cast at *
  rw [this]
  refine Nat.add_sub_cancel' <| Nat.le_floor <| (le_div_iff₀ ha).mpr ?_
  simpa using hak

private lemma dim_modforms_lvl_one_step (k : ℕ) (HK : (3 : ℤ) ≤ (k : ℤ) - 12)
    (iH : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) ((k - 12 : ℕ) : ℤ)) =
      if 12 ∣ ((k - 12 : ℕ) : ℤ) - 2 then Nat.floor (((k - 12 : ℕ) : ℚ) / 12)
        else Nat.floor (((k - 12 : ℕ) : ℚ) / 12) + 1) :
    1 + Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) ((k : ℤ) - 12)) =
      if 12 ∣ (k : ℤ) - 2 then Nat.floor ((k : ℚ) / 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  have hk12 : (((k - 12) : ℕ) : ℤ) = k - 12 := by
    norm_cast
    exact (Int.subNatNat_of_le (by omega)).symm
  rw [hk12] at iH
  have hcast : ((k - 12) : ℕ) = (k : ℚ) - 12 := by norm_cast
  rw [iH, hcast]
  by_cases h12 : 12 ∣ ((k) : ℤ) - 2
  · have h12k : 12 ∣ (k : ℤ) - 12 - 2 := by omega
    simp only [h12k, ↓reduceIte, h12]
    have := Nat_floor_div_sub k 12 (by norm_num)
    norm_cast at *
    apply this
    omega
  · have h12k : ¬ 12 ∣ (k : ℤ) - 12 - 2 := by omega
    simp only [h12k, ↓reduceIte, Nat.cast_add, Nat.cast_one, h12]
    have := Nat_floor_div_sub k 12 (by norm_num)
    norm_cast at *
    rw [← add_assoc, this]
    omega

private lemma dim_modforms_lvl_one_base (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k)
    (HK : ¬ (3 : ℤ) ≤ (k : ℤ) - 12) :
    1 + Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) ((k : ℤ) - 12)) =
      if 12 ∣ (k : ℤ) - 2 then Nat.floor ((k : ℚ) / 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  simp only [not_le] at HK
  have hkop : k ∈ Finset.filter Even (Finset.Icc 3 14) := by
    simp only [Finset.mem_filter, Finset.mem_Icc, hk2, and_true]
    omega
  have hset : Finset.filter Even (Finset.Icc 3 14) = ({4, 6, 8, 10, 12, 14} : Finset ℕ) := by decide
  rw [hset] at hkop
  fin_cases hkop
  · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
    rw [ModularForm.levelOne_neg_weight_rank_zero (by norm_num : (-8 : ℤ) < 0)]
    norm_cast
  · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
    rw [ModularForm.levelOne_neg_weight_rank_zero (by norm_num : (-6 : ℤ) < 0)]
    norm_cast
  · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
    rw [ModularForm.levelOne_neg_weight_rank_zero (by norm_num : (-4 : ℤ) < 0)]
    norm_cast
  · simp only [Nat.cast_ofNat, Int.reduceSub, Int.reduceNeg, Nat.cast_ite]
    rw [ModularForm.levelOne_neg_weight_rank_zero (by norm_num : (-2 : ℤ) < 0)]
    norm_cast
  · simp only [Nat.cast_ofNat, Int.reduceSub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      div_self, Nat.floor_one, Nat.reduceAdd, Nat.cast_ite, Nat.cast_one]
    rw [ModularForm.levelOne_weight_zero_rank_one]
    norm_cast
  · simp only [Nat.cast_ofNat, Int.reduceSub, dim_weight_two, add_zero, dvd_refl, ↓reduceIte]
    norm_cast

lemma dim_modforms_lvl_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = if 12 ∣ (k : ℤ) - 2 then
      Nat.floor ((k : ℚ) / 12) else Nat.floor ((k : ℚ) / 12) + 1 := by
  induction k using Nat.strong_induction_on with | h k ihn =>
  rw [dim_modforms_eq_one_add_dim_cuspforms k (by omega) hk2,
    LinearEquiv.rank_eq (CuspForms_iso_Modforms (k : ℤ))]
  by_cases HK : (3 : ℤ) ≤ (k : ℤ) - 12
  · refine dim_modforms_lvl_one_step k HK (ihn (k - 12) (by omega) (by omega) ?_)
    refine (Nat.even_sub (by omega)).mpr ?_
    simp only [hk2, true_iff]
    decide
  · exact dim_modforms_lvl_one_base k hk hk2 HK

lemma ModularForm.dimension_level_one (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) :
    Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) k) = if 12 ∣ (k : ℤ) - 2 then
      Nat.floor ((k : ℚ) / 12) else Nat.floor ((k : ℚ) / 12) + 1 :=
  dim_modforms_lvl_one k hk hk2

private lemma finiteDimensional_of_subsingleton_aux (V : Type*) [AddCommGroup V] [Module ℂ V]
    [Subsingleton V] : FiniteDimensional ℂ V := by
  refine (Module.finite_def).2 ?_
  simpa [Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule ℂ V))] using
    (Submodule.fg_bot : (⊥ : Submodule ℂ V).FG)

private lemma finiteDimensional_of_rank_lt_aleph0_aux (V : Type*) [AddCommGroup V] [Module ℂ V]
    (h : Module.rank ℂ V < Cardinal.aleph0) : FiniteDimensional ℂ V := by
  haveI : Module.Free ℂ V := by infer_instance
  simpa using (Module.rank_lt_aleph0_iff (R := ℂ) (M := V)).1 h

/-- Level-one modular forms of odd weight are identically zero, via invariance under `-I`. -/
lemma ModularForm.levelOne_eq_zero_of_odd_weight {k : ℤ} (hk : Odd k)
    (f : ModularForm Γ(1) k) : f = 0 := by
  ext z
  have h' : f z = -f z := by
    have h : f z = (-1 : ℂ) ^ k * f z := by
      simpa [denom, show (-1 : SL(2, ℤ)) • z = z by simp] using
        (SlashInvariantForm.slash_action_eqn_SL'' (f := f) (γ := (-1 : SL(2, ℤ)))
          (hγ := CongruenceSubgroup.mem_Gamma_one (-1 : SL(2, ℤ))) z)
    simpa [hk.neg_one_zpow, neg_one_mul] using h
  simpa using (CharZero.eq_neg_self_iff (a := f z)).1 h'

lemma finiteDimensional_modularForm_level_one (k : ℤ) :
    FiniteDimensional ℂ (ModularForm Γ(1) k) := by
  by_cases hkneg : k < 0
  · exact Module.finite_of_rank_eq_zero
      (ModularForm.levelOne_neg_weight_rank_zero (k := k) hkneg)
  have hk0le : 0 ≤ k := le_of_not_gt hkneg
  by_cases hk0 : k = 0
  · subst hk0
    refine finiteDimensional_of_rank_lt_aleph0_aux (V := ModularForm Γ(1) (0 : ℤ)) ?_
    simp [ModularForm.levelOne_weight_zero_rank_one, Cardinal.one_lt_aleph0]
  rcases Int.even_or_odd k with hk2 | hk2
  · set kN : ℕ := Int.toNat k
    have hkNat : (kN : ℤ) = k := by simpa [kN] using (Int.toNat_of_nonneg hk0le)
    have hk2Nat : Even (Int.toNat k) := by
      have : Even (kN : ℤ) := by simpa [hkNat, kN] using hk2
      simpa [kN] using (Int.even_coe_nat kN).1 this
    by_cases hk2' : k = 2
    · subst hk2'
      refine finiteDimensional_of_rank_lt_aleph0_aux (V := ModularForm Γ(1) (2 : ℤ)) ?_
      simpa [show Module.rank ℂ (ModularForm Γ(1) (2 : ℤ)) = 0 by simpa using dim_weight_two]
        using (Cardinal.natCast_lt_aleph0 (n := 0))
    · have hkNat_ge3 : (3 : ℤ) ≤ (Int.toNat k : ℤ) := by grind only [= Int.even_iff]
      have hr : Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) kN) =
          if 12 ∣ ((kN : ℤ) - 2) then Nat.floor ((kN : ℚ) / 12) else
            Nat.floor ((kN : ℚ) / 12) + 1 := by
        simpa [kN] using ModularForm.dimension_level_one (k := kN) hkNat_ge3 hk2Nat
      have hr' :
          Module.rank ℂ (ModularForm (CongruenceSubgroup.Gamma 1) kN) < Cardinal.aleph0 := by
        by_cases hdiv : 12 ∣ ((kN : ℤ) - 2)
        · simp [hr, hdiv]
        · simpa [hr, hdiv] using
            (Cardinal.add_lt_aleph0
              (Cardinal.natCast_lt_aleph0 (n := Nat.floor ((kN : ℚ) / 12)))
              Cardinal.one_lt_aleph0)
      haveI : FiniteDimensional ℂ (ModularForm (CongruenceSubgroup.Gamma 1) (kN : ℤ)) :=
        finiteDimensional_of_rank_lt_aleph0_aux
          (V := ModularForm (CongruenceSubgroup.Gamma 1) (kN : ℤ)) hr'
      exact hkNat ▸ (show FiniteDimensional ℂ (ModularForm Γ(1) (kN : ℤ)) by infer_instance)
  · have hz : ∀ f : ModularForm Γ(1) k, f = 0 := fun f ↦
      ModularForm.levelOne_eq_zero_of_odd_weight (k := k) hk2 f
    haveI : Subsingleton (ModularForm Γ(1) k) := subsingleton_of_forall_eq 0 hz
    exact finiteDimensional_of_subsingleton_aux (V := ModularForm Γ(1) k)

lemma finiteDimensional_modularForm_congr {k : ℤ} {H K : Subgroup (GL (Fin 2) ℝ)}
    (h : H = K) [H.HasDetOne] [K.HasDetOne]
    (hH : FiniteDimensional ℂ (ModularForm H k)) :
    FiniteDimensional ℂ (ModularForm K k) := by
  cases h; simpa using hH

lemma finiteDimensional_modularForm_SL2Z (k : ℤ) :
    FiniteDimensional ℂ (ModularForm 𝒮ℒ k) := by
  let f : SL(2, ℤ) →* GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ
  change FiniteDimensional ℂ (ModularForm f.range k)
  have hΓ1 : FiniteDimensional ℂ (ModularForm (Subgroup.map f (Γ(1) : Subgroup SL(2, ℤ))) k) := by
    simpa [f] using (finiteDimensional_modularForm_level_one (k := k))
  have hΓ : (Γ(1) : Subgroup SL(2, ℤ)) = ⊤ := by
    simpa using (CongruenceSubgroup.Gamma_one_top : CongruenceSubgroup.Gamma 1 = ⊤)
  have htop : FiniteDimensional ℂ (ModularForm (Subgroup.map f (⊤ : Subgroup SL(2, ℤ))) k) :=
    finiteDimensional_modularForm_congr (congrArg (Subgroup.map f) hΓ) hΓ1
  have hrange : f.range = Subgroup.map f (⊤ : Subgroup SL(2, ℤ)) := by
    simpa [f] using (MonoidHom.range_eq_map f)
  exact finiteDimensional_modularForm_congr (k := k) hrange.symm htop

open SpherePacking.ModularForms.NormReduction in
private lemma dim_gen_cong_levels_eq_of_coeff_eq_zero {k : ℤ} {Γ : Subgroup SL(2, ℤ)}
    [Γ.FiniteIndex] {N : ℕ}
    (hNinj : Function.Injective fun (f : ModularForm 𝒮ℒ (k * Nat.card (Q Γ)))
      (n : Fin N) ↦ (qExpansion (cuspWidth (Γ := Γ)) f).coeff n) (f g : ModularForm (G Γ) k)
    (hcoeff : ∀ m < N, (qExpansion (cuspWidth (Γ := Γ)) (⇑(f - g))).coeff m = 0) : f = g := by
  have hcoeff_norm : ∀ m < N,
      (qExpansion (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ (f - g))).coeff m = 0 := fun m hm ↦
    SpherePacking.ModularForms.NormReduction.qExpansion_coeff_eq_zero_norm_of_qExpansion_coeff_eq_zero
      (Γ := Γ) (k := k) (f := (f - g)) (N := N) (n := m) hm hcoeff
  have hfun :
      (fun n : Fin N ↦ (qExpansion (cuspWidth (Γ := Γ)) (ModularForm.norm 𝒮ℒ (f - g))).coeff n) =
        fun n : Fin N ↦
          (qExpansion (cuspWidth (Γ := Γ)) (0 : ModularForm 𝒮ℒ (k * Nat.card (Q Γ)))).coeff n := by
    ext n
    simpa [qExpansion_zero (cuspWidth (Γ := Γ))] using hcoeff_norm (n : ℕ) n.isLt
  have hnorm : ModularForm.norm 𝒮ℒ (f - g) = (0 : ModularForm 𝒮ℒ (k * Nat.card (Q Γ))) :=
    hNinj hfun
  have hsub : (f - g : ModularForm (G Γ) k) = 0 :=
    (coe_eq_zero_iff (f - g)).mp <|
      (ModularForm.norm_eq_zero_iff (ℋ := 𝒮ℒ) (f := (f - g)) (k := k)).1 (by simpa using hnorm)
  simpa [sub_eq_zero] using hsub

open SpherePacking.ModularForms.NormReduction in
lemma dim_gen_cong_levels (k : ℤ) (Γ : Subgroup SL(2, ℤ)) (hΓ : Subgroup.index Γ ≠ 0) :
    FiniteDimensional ℂ (ModularForm Γ k) := by
  by_cases hkneg : k < 0
  · exact SpherePacking.ModularForms.finiteDimensional_modularForm_neg_weight Γ hΓ k hkneg
  by_cases hk0 : k = 0
  · subst hk0
    exact SpherePacking.ModularForms.finiteDimensional_modularForm_weight_zero Γ hΓ
  haveI : Γ.FiniteIndex := ⟨hΓ⟩
  let GΓ : Subgroup (GL (Fin 2) ℝ) := SpherePacking.ModularForms.NormReduction.G Γ
  let h : ℝ := SpherePacking.ModularForms.NormReduction.cuspWidth (Γ := Γ)
  have hh : 0 < h := SpherePacking.ModularForms.NormReduction.cuspWidth_pos (Γ := Γ) hΓ
  have hperΓ : h ∈ GΓ.strictPeriods := by
    simpa [h] using SpherePacking.ModularForms.NormReduction.cuspWidth_mem_strictPeriods (Γ := Γ)
  have hperSL : h ∈ (𝒮ℒ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simpa [h] using
      SpherePacking.ModularForms.NormReduction.cuspWidth_mem_strictPeriods_levelOne (Γ := Γ)
  haveI : GΓ.IsArithmetic :=
    SpherePacking.ModularForms.NormReduction.instIsArithmetic (Γ := Γ) hΓ
  haveI : GΓ.IsFiniteRelIndex 𝒮ℒ := Subgroup.IsArithmetic.isFiniteRelIndexSL (𝒢 := GΓ)
  let w : ℤ := k * Nat.card (SpherePacking.ModularForms.NormReduction.Q Γ)
  haveI : FiniteDimensional ℂ (ModularForm 𝒮ℒ w) := by
    simpa [w] using (finiteDimensional_modularForm_SL2Z (k := w))
  obtain ⟨N, hNinj⟩ :=
    SpherePacking.ModularForms.exists_qCoeff_injective
      (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) (k := w) (h := h) hh hperSL
  let trunc : ModularForm GΓ k →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun f n ↦ (qExpansion h f).coeff n
      map_add' f g := by ext n; simp [qExpansion_add hh hperΓ f g]
      map_smul' a f := by ext n; simp [qExpansion_smul hh hperΓ a f] }
  have htrunc_inj : Function.Injective trunc := by
    intro f g hfg
    refine dim_gen_cong_levels_eq_of_coeff_eq_zero hNinj f g fun m hm ↦ ?_
    have hsub : trunc (f - g) = 0 := by
      rw [trunc.map_sub, hfg, sub_self]
    have := congrArg (fun t : Fin N → ℂ ↦ t ⟨m, hm⟩) hsub
    simpa [trunc] using this
  haveI : FiniteDimensional ℂ (Fin N → ℂ) := by infer_instance
  simpa using (FiniteDimensional.of_injective trunc htrunc_inj)
