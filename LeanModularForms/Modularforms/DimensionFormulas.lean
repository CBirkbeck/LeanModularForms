/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.NumberTheory.ModularForms.LevelOne.Basic
public import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula
public import LeanModularForms.Modularforms.Eisenstein
public import LeanModularForms.Modularforms.DimGenCongLevels.Basic
public import LeanModularForms.Modularforms.DimGenCongLevels.NormReduction
public import LeanModularForms.Modularforms.DimGenCongLevels.FiniteDimensional
public import LeanModularForms.Modularforms.DimGenCongLevels.NormTransfer

@[expose] public section

/-!
# Dimension formulas for level-one modular forms

This file is a thin wrapper around mathlib's level-one dimension formula
(`ModularForm.dimension_level_one`) and the related finite-dimensionality results.
Mathlib now states these for the `GL`-side subgroup `𝒮ℒ`; the project still uses the
`SL`-side notation `Γ(1)` extensively, so we transport the rank statements along the
identification `↑Γ(1) = 𝒮ℒ` (`CongruenceSubgroup.Gamma_one_coe_eq_SL`) via
`ModularForm.mcast` / `CuspForm.mcast`-based `LinearEquiv`s.

## Main results

* `modularFormGammaOneEquivSL`, `cuspFormGammaOneEquivSL`: linear equivalences carrying
  the project's `Γ(1)`-indexed spaces to mathlib's `𝒮ℒ`-indexed ones.
* `cuspform_weight_lt_12_zero`, `IsCuspForm_weight_lt_eq_zero`: weight-`< 12` cusp form
  vanishing (used by `Modularforms/ThetaDerivIdentities.lean`,
  `Modularforms/JacobiTheta.lean`).
* `CuspForms_iso_Modforms`: the division-by-`Δ` isomorphism for `Γ(1)`, transported from
  `CuspForm.discriminantEquiv` (used by `Modularforms/JacobiTheta.lean`).
* `weight_four_one_dimensional`, `weight_six_one_dimensional`, `weight_eight_one_dimensional`:
  one-dimensionality of low even-weight spaces (used in `Modularforms/RamanujanIdentities.lean`).
* `Delta_eq_Delta_E4_E6_aux`, `Delta_E4_E6_eq`: the explicit identification of the
  discriminant with `(E₄³ - E₆²)/1728` (used by `Modularforms/FG.lean`).
* `dim_gen_cong_levels`: finite-dimensionality for any finite-index congruence subgroup,
  via mathlib's `FiniteDimensional ℂ (ModularForm 𝒮ℒ k)` instance and the norm-reduction
  injection.
-/

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups SlashInvariantFormClass ModularFormClass

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat
  Real MatrixGroups CongruenceSubgroup

noncomputable section

/-! ### Transport equivalences between `Γ(1)` and `𝒮ℒ` -/

/-- Linear equivalence between `Γ(1)`-modular forms and `𝒮ℒ`-modular forms, transported via
`ModularForm.mcast` along the equality `↑Γ(1) = 𝒮ℒ`. -/
def modularFormGammaOneEquivSL (k : ℤ) : ModularForm Γ(1) k ≃ₗ[ℂ] ModularForm 𝒮ℒ k where
  toFun f := ModularForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  invFun f := ModularForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma modularFormGammaOneEquivSL_apply (k : ℤ) (f : ModularForm Γ(1) k) (z : ℍ) :
    modularFormGammaOneEquivSL k f z = f z := rfl

/-- Linear equivalence between `Γ(1)`-cusp forms and `𝒮ℒ`-cusp forms, transported via
`CuspForm.mcast` along the equality `↑Γ(1) = 𝒮ℒ`. -/
def cuspFormGammaOneEquivSL (k : ℤ) : CuspForm Γ(1) k ≃ₗ[ℂ] CuspForm 𝒮ℒ k where
  toFun f := CuspForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL.symm
  invFun f := CuspForm.mcast rfl f CongruenceSubgroup.Gamma_one_coe_eq_SL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] lemma cuspFormGammaOneEquivSL_apply (k : ℤ) (f : CuspForm Γ(1) k) (z : ℍ) :
    cuspFormGammaOneEquivSL k f z = f z := rfl

/-! ### Weight-`< 12` cusp forms vanish -/

/-- The space of `Γ(1)` cusp forms of weight `k < 12` has rank zero. -/
lemma cuspform_weight_lt_12_zero (k : ℤ) (hk : k < 12) :
    Module.rank ℂ (CuspForm Γ(1) k) = 0 := by
  rw [LinearEquiv.rank_eq (cuspFormGammaOneEquivSL k)]
  exact CuspForm.rank_eq_zero_of_weight_lt_twelve hk

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

/-! ### The `CuspForm Γ(1) k ≃ₗ ModularForm Γ(1) (k-12)` isomorphism -/

/-- Division by the discriminant yields a linear equivalence between `Γ(1)`-cusp forms of
weight `k` and `Γ(1)`-modular forms of weight `k - 12`. This is the project's wrapper around
mathlib's `CuspForm.discriminantEquiv` (stated for `𝒮ℒ`). -/
def CuspForms_iso_Modforms (k : ℤ) :
    CuspForm Γ(1) k ≃ₗ[ℂ] ModularForm Γ(1) (k - 12) :=
  (cuspFormGammaOneEquivSL k).trans
    (CuspForm.discriminantEquiv.trans (modularFormGammaOneEquivSL (k - 12)).symm)

/-! ### Low even weights are one-dimensional -/

lemma weight_four_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 4) = 1 := by
  rw [LinearEquiv.rank_eq (modularFormGammaOneEquivSL 4)]
  exact ModularForm.levelOne_weight_four_rank_one

lemma weight_six_one_dimensional : Module.rank ℂ (ModularForm Γ(1) 6) = 1 := by
  rw [LinearEquiv.rank_eq (modularFormGammaOneEquivSL 6)]
  exact ModularForm.levelOne_weight_six_rank_one

/-- For even `k` with `3 ≤ k < 12`, the space of `Γ(1)` modular forms of weight `k` is
one-dimensional. -/
lemma weight_eight_one_dimensional (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (hk3 : k < 12) :
    Module.rank ℂ (ModularForm Γ(1) k) = 1 := by
  rw [LinearEquiv.rank_eq (modularFormGammaOneEquivSL (k : ℤ))]
  have hdim := ModularForm.dimension_level_one k hk2
  have hdiv : k / 12 = 0 := Nat.div_eq_zero_iff.mpr (Or.inr hk3)
  by_cases hmod : k ≡ 2 [MOD 12]
  · have hk2' : k = 2 := by
      have h12 : k % 12 = 2 % 12 := hmod
      have hk' : k = k % 12 := (Nat.mod_eq_of_lt hk3).symm
      omega
    omega
  · rw [hdim, if_neg hmod, hdiv]
    norm_cast

/-! ### Explicit identification of `Δ` with `(E₄³ - E₆²)/1728` -/

lemma delta_eq_E4E6_const : ∃ (c : ℂ), (c • Delta) = Delta_E4_E6_aux := by
  have hr : Module.finrank ℂ (CuspForm Γ(1) 12) = 1 := by
    apply Module.finrank_eq_of_rank_eq
    rw [LinearEquiv.rank_eq (CuspForms_iso_Modforms 12),
      LinearEquiv.rank_eq (modularFormGammaOneEquivSL (12 - 12))]
    simpa using ModularForm.levelOne_weight_zero_rank_one
  exact (finrank_eq_one_iff_of_nonzero' Delta Delta_ne_zero).mp hr Delta_E4_E6_aux

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
    simpa using (ModularForm.qExpansion_sub (Γ := Γ(1)) (h := (1 : ℕ))
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
  have hs := (ModularForm.qExpansion_smul (Γ := Γ(1)) (h := (1 : ℕ))
    (hh := by positivity) (hΓ := by simp) c Delta).symm
  rw [show qExpansion 1 ⇑(c • Delta) = qExpansion 1 (c • ⇑Delta) from rfl,
    ← Nat.cast_one (R := ℝ), ← hs] at h2
  simp at h2
  rw [Delta_q_one_term] at h2
  simpa using h2

/-! ### Finite-dimensionality for arbitrary finite-index congruence subgroups -/

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
  haveI : FiniteDimensional ℂ (ModularForm 𝒮ℒ w) := inferInstance
  obtain ⟨N, hNinj⟩ :=
    SpherePacking.ModularForms.exists_qCoeff_injective
      (Γ := (𝒮ℒ : Subgroup (GL (Fin 2) ℝ))) (k := w) (h := h) hh hperSL
  let trunc : ModularForm GΓ k →ₗ[ℂ] (Fin N → ℂ) :=
    { toFun := fun f n ↦ (qExpansion h f).coeff n
      map_add' f g := by ext n; simp [ModularForm.qExpansion_add hh hperΓ f g]
      map_smul' a f := by ext n; simp [ModularForm.qExpansion_smul hh hperΓ a f] }
  have htrunc_inj : Function.Injective trunc := by
    intro f g hfg
    refine dim_gen_cong_levels_eq_of_coeff_eq_zero hNinj f g fun m hm ↦ ?_
    have hsub : trunc (f - g) = 0 := by
      rw [trunc.map_sub, hfg, sub_self]
    have := congrArg (fun t : Fin N → ℂ ↦ t ⟨m, hm⟩) hsub
    simpa [trunc] using this
  haveI : FiniteDimensional ℂ (Fin N → ℂ) := by infer_instance
  simpa using (FiniteDimensional.of_injective trunc htrunc_inj)
