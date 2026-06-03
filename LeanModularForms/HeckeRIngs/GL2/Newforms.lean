/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeReduction
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms, eigenforms, and oldforms (Phase 6)

This file develops the theory of newforms following Diamond–Shurman §5.6–5.8
and Atkin–Lehner [AL70].

## Design

Following the Mathlib convention where `CuspForm` extends `SlashInvariantForm`,
we define `Eigenform`, `Newform`, and `Oldform` as structures **extending**
`CuspForm`, plus supporting predicates `IsEigenform`, `IsNewform`, `IsOldform`.

The structure-based approach makes it easy to:
- Pass an eigenform as a cusp form (via the auto-generated `toCuspForm` projection)
- Speak of "the eigenvalues of f" as field access
- Define submodules `cuspFormsOld` and `cuspFormsNew` as the carrier sets

## Main definitions

### Structures extending CuspForm
* `Eigenform N k` — a cusp form together with eigenvalue data for all T_n with (n,N)=1
* `Newform N k` — an eigenform that is in the new subspace and is normalised (a_1 = 1)

### Predicates
* `IsEigenform f` — f is a common Hecke eigenform
* `IsOldform f` — f is in the span of level-raised forms from proper divisors
* `IsNewform f` — f is a newform (eigen + new + normalised)

### Submodules
* `cuspFormsOld` — submodule of oldforms
* `cuspFormsNew` — submodule of newforms (orthogonal complement)

## Main results

* `cuspFormsOld_isCompl_cuspFormsNew` — DS (5.20): direct sum decomposition
* `heckeT_n_preserves_cuspFormsOld/New` — DS Prop 5.6.2
* `newform_unique` — DS Thm 5.8.2 (Atkin-Lehner uniqueness)
* `mainLemma` — DS Thm 5.7.1 (Atkin-Lehner main lemma)
* `strongMultiplicityOne` — the goal of the project

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §§5.6–5.8
* [AL70] Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970)
* [Miy] Miyake, *Modular Forms*, §4.6
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The full Newform Euler product on `Re s > k/2 + 1`, given full coprime
multiplicativity of the Fourier coefficient sequence `f.lCoeff`. -/
theorem Newform.lSeries_full_hasProd_of_full_coprime_mul
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (h_full_mul : ∀ {m n : ℕ}, Nat.Coprime m n →
      f.lCoeff (m * n) = f.lCoeff m * f.lCoeff n)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd
      (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e))
      (LSeries f.lCoeff s) := by
  refine EulerProduct.eulerProduct_hasProd (f := LSeries.term f.lCoeff s) ?_ ?_
    (f.lSeriesSummable hs).norm rfl
  · rw [LSeries.term_def, if_neg one_ne_zero, f.lCoeff_one, Nat.cast_one, Complex.one_cpow, div_one]
  · intro m n hmn
    rw [LSeries.term_def₀ f.lCoeff_zero, LSeries.term_def₀ f.lCoeff_zero,
      LSeries.term_def₀ f.lCoeff_zero, h_full_mul hmn]
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]; ring

private lemma Newform.term_lCoeff_pow_of_bad_prime_pow
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) {p : ℕ}
    (h_bad_pow : ∀ r : ℕ, f.lCoeff (p ^ r) = f.lCoeff p ^ r) (s : ℂ) (e : ℕ) :
    LSeries.term f.lCoeff s (p ^ e) = (f.lCoeff p * (p : ℂ) ^ (-s)) ^ e := by
  rw [LSeries.term_def₀ f.lCoeff_zero, h_bad_pow e]
  push_cast
  rw [mul_pow, show ((p : ℂ) ^ e) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e by
    rw [← Complex.natCast_cpow_natCast_mul (p : ℕ) e (-s),
      show ((e : ℂ) * (-s)) = (-s) * (e : ℂ) from by ring, Complex.cpow_mul_nat]]

private lemma Newform.tsum_term_lCoeff_pow_at_bad_prime_eq_geom
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) {p : ℕ} (hp : p.Prime)
    (h_bad_pow : ∀ r : ℕ, f.lCoeff (p ^ r) = f.lCoeff p ^ r)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    ‖f.lCoeff p * (p : ℂ) ^ (-s)‖ < 1 ∧
    ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e) =
      (1 - f.lCoeff p * (p : ℂ) ^ (-s))⁻¹ := by
  have h_term (e : ℕ) : LSeries.term f.lCoeff s ((p : ℕ) ^ e) =
      (f.lCoeff p * ((p : ℕ) : ℂ) ^ (-s)) ^ e :=
    f.term_lCoeff_pow_of_bad_prime_pow h_bad_pow s e
  have h_sum_pow : Summable fun e : ℕ ↦ ‖LSeries.term f.lCoeff s ((p : ℕ) ^ e)‖ :=
    (f.lSeriesSummable hs).norm.comp_injective
      fun _ _ hab ↦ Nat.pow_right_injective hp.two_le hab
  have h_sum_pow_geom : Summable fun e : ℕ ↦ (f.lCoeff p * ((p : ℕ) : ℂ) ^ (-s)) ^ e :=
    Summable.of_norm <| h_sum_pow.congr fun e ↦ by rw [h_term e]
  have h_norm_lt : ‖f.lCoeff p * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 :=
    summable_geometric_iff_norm_lt_one.mp h_sum_pow_geom
  exact ⟨h_norm_lt, by rw [tsum_congr h_term, tsum_geometric_of_norm_lt_one h_norm_lt]⟩

/-- Prime-factor membership of `N` characterises `(Nat.primeFactors N).attach.image …`. -/
private lemma Newform.mem_primeFactors_image_iff {N : ℕ} [NeZero N] (p : Nat.Primes) :
    p ∈ (Nat.primeFactors N).attach.image
        (fun ⟨q, hq⟩ ↦ (⟨q, (Nat.mem_primeFactors.mp hq).1⟩ : Nat.Primes)) ↔
      (p : ℕ) ∣ N := by
  simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists, Nat.mem_primeFactors]
  refine ⟨fun ⟨q, ⟨_, hq_N, _⟩, hq_eq⟩ ↦ ?_,
    fun hp_dvd ↦ ⟨(p : ℕ), ⟨p.prop, hp_dvd, NeZero.ne N⟩, rfl⟩⟩
  have h_eq : (p : ℕ) = q := by simpa using congr_arg (fun (x : Nat.Primes) ↦ (x : ℕ)) hq_eq.symm
  rw [h_eq]; exact hq_N

/-- Builds an `Newform.EulerStrippingArithmeticInput f χ` from the bundled
Hecke multiplicative structure `Newform.HasHeckeMultiplicativeStructure f χ`
(Diamond–Shurman §5.8 Prop 5.8.5, Miyake §4.5.16). -/
noncomputable def Newform.eulerStrippingArithmeticInput_of_heckeStruct
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (h : Newform.HasHeckeMultiplicativeStructure f χ) :
    Newform.EulerStrippingArithmeticInput f χ where
  hfχ := h.hfχ
  S := (Nat.primeFactors N).attach.image
    (fun ⟨p, hp⟩ ↦ ⟨p, (Nat.mem_primeFactors.mp hp).1⟩)
  hS p := Newform.mem_primeFactors_image_iff p
  hf_full_euler := fun {_} hs ↦ f.lSeries_full_hasProd_of_full_coprime_mul h.full_coprime_mul hs
  h_bad_local_inv := fun s hs p hp_S ↦
    (f.tsum_term_lCoeff_pow_at_bad_prime_eq_geom p.prop
      (h.bad_prime_pow p.prop ((Newform.mem_primeFactors_image_iff p).mp hp_S)) hs).2
  h_bad_local_ne_zero := by
    intro s hs p hp_S h_eq_zero
    have h_norm := (f.tsum_term_lCoeff_pow_at_bad_prime_eq_geom p.prop
      (h.bad_prime_pow p.prop ((Newform.mem_primeFactors_image_iff p).mp hp_S)) hs).1
    rw [(sub_eq_zero.mp h_eq_zero).symm, norm_one] at h_norm
    exact lt_irrefl 1 h_norm


/-- A `Newform.CompletedFrickeData f` exists for any newform `f` (with
`0 < (k : ℝ)`) given the Fricke twist `Newform.HasFrickeTwistAsCuspForm f` and
the Euler-stripping multiplier `Newform.HasEulerStrippingMultiplier f`. -/
theorem Newform.completedFrickeData_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (h_fricke : Newform.HasFrickeTwistAsCuspForm f)
    (hk_pos : 0 < (k : ℝ)) (h_stripping : Newform.HasEulerStrippingMultiplier f) :
    Nonempty (Newform.CompletedFrickeData f) :=
  let ⟨twist, slash_eq⟩ := h_fricke
  let ⟨stripping, stripping_diff, stripping_bridge⟩ := h_stripping
  ⟨Newform.CompletedFrickeData.ofSlashEqWithStripping f twist slash_eq hk_pos
    stripping stripping_diff stripping_bridge⟩

/-- Projects `Newform.CompletedFrickeData` onto `Newform.CompletedMellinData`,
discarding the slash-side data and keeping the analytic-content fields. -/
noncomputable def Newform.CompletedMellinData.ofCompletedFrickeData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.CompletedFrickeData f) : Newform.CompletedMellinData f where
  pair := data.pair
  hk_pos := data.hk_pos
  completed_bridge := data.completed_bridge
  stripping := data.stripping
  stripping_diff := data.stripping_diff
  stripping_bridge := data.stripping_bridge

/-- The global `Newform.HeckeEntireExtension` from per-newform
`Newform.CompletedFrickeData`. -/
theorem Newform.HeckeEntireExtension_of_CompletedFrickeData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.CompletedFrickeData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_CompletedMellinData
    fun _N _ _k f ↦ Newform.CompletedMellinData.ofCompletedFrickeData (h f)


private lemma levelRaiseMatrix_inv_smul_vadd_one_eq
    {l : ℕ} [NeZero l] (τ : UpperHalfPlane) :
    ((levelRaiseMatrix l)⁻¹ • ((1 : ℝ) +ᵥ τ) : UpperHalfPlane) =
      ((1 : ℝ) / (l : ℝ)) +ᵥ ((levelRaiseMatrix l)⁻¹ • τ) := by
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_inv_smul, UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd,
    coe_levelRaiseMatrix_inv_smul]
  push_cast
  ring

private lemma exp_two_pi_mul_I_div_natCast_pow_eq_one (l : ℕ) [NeZero l] :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) ^ l = 1 := by
  rw [← Complex.exp_nat_mul, mul_div_cancel₀ _ (mod_cast NeZero.ne l : (l : ℂ) ≠ 0)]
  exact Complex.exp_two_pi_mul_I

private lemma qExpansion_coeff_smul_qParam_pow_shift_eq
    {N : ℕ} [NeZero N] {l : ℕ} [NeZero l] {k : ℤ}
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_supp : ∀ n : ℕ, ¬ l ∣ n → (ModularFormClass.qExpansion (1 : ℝ) g).coeff n = 0)
    (σ : UpperHalfPlane) (n : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) g).coeff n •
        Function.Periodic.qParam (1 : ℝ)
          ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) ^ n =
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff n •
        Function.Periodic.qParam (1 : ℝ) (σ : ℂ) ^ n := by
  have hqP :
      Function.Periodic.qParam (1 : ℝ) ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) =
        Function.Periodic.qParam (1 : ℝ) (σ : ℂ) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) := by
    unfold Function.Periodic.qParam
    rw [UpperHalfPlane.coe_vadd, ← Complex.exp_add]
    congr 1; push_cast; ring
  by_cases hln : l ∣ n
  · obtain ⟨m, rfl⟩ := hln
    rw [hqP, mul_pow,
      show Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) ^ (l * m) =
          (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (l : ℂ)) ^ l) ^ m from pow_mul _ l m,
      exp_two_pi_mul_I_div_natCast_pow_eq_one l, one_pow, mul_one]
  · rw [hg_supp n hln, zero_smul, zero_smul]

theorem exists_levelRaise_preimage_of_coeff_support_multiples
    {N : ℕ} [NeZero N] {l : ℕ} [NeZero l] (_hl : 1 < l) (_hlN : l ∣ N) {k : ℤ}
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_supp : ∀ n : ℕ, ¬ l ∣ n →
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff n = 0) :
    ∃ f : UpperHalfPlane → ℂ,
      (⇑g : UpperHalfPlane → ℂ) = levelRaiseFun l k f ∧
      f ∣[k] (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ) = f := by
  refine ⟨fun τ ↦ (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ), ?_, ?_⟩
  · funext τ
    show (⇑g : _ → ℂ) τ = levelRaiseFun l k _ τ
    rw [levelRaiseFun_apply]
    show (⇑g : _ → ℂ) τ =
      (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • (levelRaiseMatrix l • τ))
    rw [← mul_smul, inv_mul_cancel, one_smul]
  · have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        CongruenceSubgroup.strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    funext τ
    show ((fun τ' ↦ (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ')) ∣[k]
        (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)) τ =
        (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ)
    rw [show ((fun τ' ↦ (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ')) ∣[k]
          (mapGL ℝ ModularGroup.T : GL (Fin 2) ℝ)) =
        ((fun τ' ↦ (⇑g : _ → ℂ) ((levelRaiseMatrix l)⁻¹ • τ')) ∣[k]
          (ModularGroup.T : SL(2, ℤ))) from rfl,
      modular_slash_T_apply]
    set σ : UpperHalfPlane := (levelRaiseMatrix l)⁻¹ • τ
    rw [levelRaiseMatrix_inv_smul_vadd_one_eq τ]
    set σ' : UpperHalfPlane := ((1 : ℝ) / (l : ℝ)) +ᵥ σ
    have Hσ' : HasSum (fun n : ℕ ↦
        (ModularFormClass.qExpansion (1 : ℝ) g).coeff n •
          Function.Periodic.qParam (1 : ℝ) (σ' : ℂ) ^ n) ((⇑g : _ → ℂ) σ') :=
      ModularFormClass.hasSum_qExpansion (f := g) one_pos h1_period σ'
    rw [funext (qExpansion_coeff_smul_qParam_pow_shift_eq g hg_supp σ)] at Hσ'
    exact (ModularFormClass.hasSum_qExpansion (f := g) one_pos h1_period σ |>.unique Hσ').symm

end HeckeRing.GL2
