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


private lemma Newform.term_lCoeff_pow_of_bad_prime_pow
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) {p : ℕ}
    (h_bad_pow : ∀ r : ℕ, f.lCoeff (p ^ r) = f.lCoeff p ^ r) (s : ℂ) (e : ℕ) :
    LSeries.term f.lCoeff s (p ^ e) = (f.lCoeff p * (p : ℂ) ^ (-s)) ^ e := by
  rw [LSeries.term_def₀ f.lCoeff_zero, h_bad_pow e]
  push_cast
  rw [mul_pow, show ((p : ℂ) ^ e) ^ (-s) = ((p : ℂ) ^ (-s)) ^ e by
    rw [← Complex.natCast_cpow_natCast_mul (p : ℕ) e (-s),
      show ((e : ℂ) * (-s)) = (-s) * (e : ℂ) from by ring, Complex.cpow_mul_nat]]

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
    (hg_supp : ∀ n : ℕ, ¬ l ∣ n → (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0)
    (σ : UpperHalfPlane) (n : ℕ) :
    (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n •
        Function.Periodic.qParam (1 : ℝ)
          ((((1 : ℝ) / (l : ℝ)) +ᵥ σ : UpperHalfPlane) : ℂ) ^ n =
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n •
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
      (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n = 0) :
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
    haveI : Fact (IsCusp OnePoint.infty ((Gamma1 N).map (mapGL ℝ))) :=
      ⟨((Gamma1 N).map (mapGL ℝ)).isCusp_of_mem_strictPeriods one_pos h1_period⟩
    have Hσ' : HasSum (fun n : ℕ ↦
        (UpperHalfPlane.qExpansion (1 : ℝ) g).coeff n •
          Function.Periodic.qParam (1 : ℝ) (σ' : ℂ) ^ n) ((⇑g : _ → ℂ) σ') :=
      UpperHalfPlane.hasSum_qExpansion one_pos
        (SlashInvariantFormClass.periodic_comp_ofComplex g h1_period)
        (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) σ'
    rw [funext (qExpansion_coeff_smul_qParam_pow_shift_eq g hg_supp σ)] at Hσ'
    exact (UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex g h1_period)
      (ModularFormClass.holo g) (ModularFormClass.bdd_at_infty g) σ |>.unique Hσ').symm

end HeckeRing.GL2
