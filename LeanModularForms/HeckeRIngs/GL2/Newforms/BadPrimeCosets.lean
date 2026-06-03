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
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeAdjoint
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: bad-prime coset combinatorics and per-coset Petersson adjoints

Coset combinatorics for the bad-prime Hecke double coset and the per-coset
Petersson adjoint identities used in the bad-prime Fricke adjoint argument.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- Lower-triangular `GL (Fin 2) ℝ` coset representative `!![p, 0; -N·b, 1]`,
with determinant `p` (so it lives in `GL (Fin 2) ℝ` whenever `p ≠ 0`). -/
noncomputable def Newform.T_p_lower_with_offset (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(p : ℝ), 0; -((N : ℝ) * b), 1] : Matrix (Fin 2) (Fin 2) ℝ)
    (by simp [Matrix.det_fin_two, hp.ne'])

/-- Underlying matrix of `T_p_lower_with_offset N hp b`. -/
@[simp]
lemma Newform.T_p_lower_with_offset_coe (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; -((N : ℝ) * b), 1] := by
  simp [Newform.T_p_lower_with_offset, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private lemma Newform.glMap_T_p_upper_coe_real {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
  change (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
    !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)]
  rw [T_p_upper_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma Newform.glMap_T_p_upper_coe_real_intMap {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(1 : ℤ), (b : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
  change (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
    (!![(1 : ℤ), (b : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)
  rw [T_p_upper_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma Newform.alpha_p_mul_eq_M_mul_T_p_upper_int
    (p a b' c d B bb : ℤ) (hB : B * p = b' - a * bb) :
    (!![(1 : ℤ), 0; 0, p] : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b'; c, d] =
      !![a, B; p * c, d - c * bb] * !![(1 : ℤ), bb; 0, p] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

private lemma Newform.intCast_eq_one_of_dvd_of_eq_one {N p : ℕ} (hpN : p ∣ N) {a : ℤ}
    (ha : (a : ZMod N) = 1) :
    (a : ZMod p) = 1 := by
  have hN_int_dvd : (N : ℤ) ∣ (a - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ha]
    ring
  rw [show (a : ZMod p) = ((a - 1 : ℤ) : ZMod p) + 1 by push_cast; ring,
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr
      (dvd_trans (Int.natCast_dvd_natCast.mpr hpN) hN_int_dvd), zero_add]

private lemma Newform.det_alpha_p_factor_eq_one (p a b' c d B bb : ℤ) (hBp : B * p = b' - a * bb)
    (h_det : a * d - b' * c = 1) :
    (!![a, B; p * c, d - c * bb] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  linear_combination h_det - c * hBp

/-- The adjugate of `T_p_lower_with_offset` as an explicit `GL (Fin 2) ℝ`
element: the adjugate of `!![p, 0; -N·b, 1]` is `!![1, 0; N·b, p]` (also with
determinant `p`). -/
noncomputable def Newform.T_p_lower_with_offset_adjugate (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(1 : ℝ), 0; ((N : ℝ) * b), (p : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ)
    (by simp [Matrix.det_fin_two, hp.ne'])

/-- Underlying matrix of `T_p_lower_with_offset_adjugate`. -/
@[simp]
lemma Newform.T_p_lower_with_offset_adjugate_coe (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), 0; ((N : ℝ) * b), (p : ℝ)] := by
  simp [Newform.T_p_lower_with_offset_adjugate, Matrix.GeneralLinearGroup.mkOfDetNeZero]



/-- `peterssonAdj (T_p_lower_with_offset N hp b) = T_p_lower_with_offset_adjugate N hp b`
as `GL (Fin 2) ℝ` elements. -/
lemma Newform.peterssonAdj_T_p_lower_with_offset_eq (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    peterssonAdj (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) =
      Newform.T_p_lower_with_offset_adjugate N hp b := by
  apply Units.ext
  rw [peterssonAdj_coe, Newform.T_p_lower_with_offset_coe,
    Newform.T_p_lower_with_offset_adjugate_coe, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Slash by `peterssonAdj (T_p_lower_with_offset N hp b)` reduces to slash by
the explicit adjugate `T_p_lower_with_offset_adjugate N hp b`. -/
@[simp]
lemma Newform.slash_peterssonAdj_T_p_lower_with_offset {N : ℕ} {k : ℤ} {p : ℕ} (hp : 0 < p)
    (b : ℕ) (g : UpperHalfPlane → ℂ) :
    g ∣[k] peterssonAdj (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) =
      g ∣[k] (Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) := by
  rw [Newform.peterssonAdj_T_p_lower_with_offset_eq]



end HeckeRing.GL2
