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

/-- GL-level Fricke / bad-prime upper coset rewrite:
`W_N * glMap (T_p_upper p hp b) = T_p_lower_with_offset N hp b * W_N`. -/
lemma Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (Newform.frickeMatrix N : GL (Fin 2) ℝ) * (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) *
        (Newform.frickeMatrix N : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Newform.T_p_lower_with_offset_coe, Newform.frickeMatrix_coe,
    Newform.glMap_T_p_upper_coe_real hp b]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]


open UpperHalfPlane MeasureTheory ModularGroup in
private lemma Newform.glMap_T_p_upper_coe_real_intMap {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(1 : ℤ), (b : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
  change (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
    (!![(1 : ℤ), (b : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ)
  rw [T_p_upper_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma Newform.fin_eq_of_mul_eq_sub {p : ℕ} (hp : 0 < p) (b1 b2 : Fin p) (m : ℤ)
    (h : m * (p : ℤ) = (b2.val : ℤ) - (b1.val : ℤ)) : b1 = b2 := by
  have hb1 : (b1.val : ℤ) < (p : ℤ) := mod_cast b1.isLt
  have hb2 : (b2.val : ℤ) < (p : ℤ) := mod_cast b2.isLt
  have hn1 : (0 : ℤ) ≤ (b1.val : ℤ) := Int.natCast_nonneg _
  have hn2 : (0 : ℤ) ≤ (b2.val : ℤ) := Int.natCast_nonneg _
  have key : (b2.val : ℤ) - (b1.val : ℤ) = 0 :=
    Int.eq_zero_of_abs_lt_dvd (m := (p : ℤ)) ⟨m, by rw [← h]; ring⟩
      (by have : (0 : ℤ) < (p : ℤ) := mod_cast hp
          rw [abs_lt]; constructor <;> linarith)
  ext
  grind

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

private lemma Newform.glMap_T_p_upper_zero_mul_mapGL_eq_of_int {p : ℕ} (hp : 0 < p)
    (γ γ' : SL(2, ℤ)) (b : ℕ)
    (h_int : (!![(1 : ℤ), 0; 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
      γ'.val * !![(1 : ℤ), (b : ℤ); 0, (p : ℤ)]) :
    (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ γ' : GL (Fin 2) ℝ) * (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) := by
  apply Units.ext
  change ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    ((mapGL ℝ γ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
      ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  have hα := Newform.glMap_T_p_upper_coe_real_intMap hp 0
  rw [Nat.cast_zero] at hα
  have hβ := Newform.glMap_T_p_upper_coe_real_intMap hp b
  have hγ_mat : ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    γ.val.map (algebraMap ℤ ℝ) := mapGL_coe_matrix γ
  have hγ'_mat : ((mapGL ℝ γ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    γ'.val.map (algebraMap ℤ ℝ) := mapGL_coe_matrix γ'
  rw [hα, hβ, hγ_mat, hγ'_mat, ← Matrix.map_mul, ← Matrix.map_mul, h_int]

private lemma Newform.exists_Gamma1_mul_T_p_upper_int
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ∃ (γ' : SL(2, ℤ)) (b : Fin p), γ' ∈ Gamma1 N ∧
      (!![(1 : ℤ), 0; 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
        γ'.val * !![(1 : ℤ), (b.val : ℤ); 0, (p : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp_dvd_N : (p : ℕ) ∣ N := not_not.mp fun h ↦ hpN (hp.coprime_iff_not_dvd.mpr h)
  set a : ℤ := γ.val 0 0 with ha_def
  set b' : ℤ := γ.val 0 1 with hb'_def
  set c : ℤ := γ.val 1 0 with hc_def
  set d : ℤ := γ.val 1 1 with hd_def
  have hg := (Gamma1_mem N γ).mp hγ
  have ha_mod_N : (a : ZMod N) = 1 := mod_cast hg.1
  have hd_mod_N : (d : ZMod N) = 1 := mod_cast hg.2.1
  have hc_mod_N : (c : ZMod N) = 0 := mod_cast hg.2.2
  have h_det_γ : a * d - b' * c = 1 := by
    have hdet := γ.property
    rw [Matrix.det_fin_two] at hdet
    exact hdet
  set b : Fin p := ⟨((b' : ZMod p)).val, ZMod.val_lt _⟩ with hb_def
  have hbval_zmod : ((b.val : ℕ) : ZMod p) = (b' : ZMod p) := by
    change (((b' : ZMod p).val : ℕ) : ZMod p) = (b' : ZMod p)
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hp_dvd_diff : (p : ℤ) ∣ (b' - a * (b.val : ℤ)) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    rw [Newform.intCast_eq_one_of_dvd_of_eq_one hp_dvd_N ha_mod_N, hbval_zmod]
    ring
  obtain ⟨B, hB_eq⟩ := hp_dvd_diff
  have hBp_int : B * (p : ℤ) = b' - a * (b.val : ℤ) := by linarith
  have hM_det : (!![a, B; (p : ℤ) * c, d - c * (b.val : ℤ)] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 :=
    Newform.det_alpha_p_factor_eq_one (p : ℤ) a b' c d B (b.val : ℤ) hBp_int h_det_γ
  refine ⟨⟨_, hM_det⟩, b, ?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · change ((a : ℤ) : ZMod N) = 1
      exact mod_cast ha_mod_N
    · change ((d - c * (b.val : ℤ) : ℤ) : ZMod N) = 1
      push_cast
      rw [hd_mod_N, hc_mod_N]
      ring
    · change (((p : ℤ) * c : ℤ) : ZMod N) = 0
      push_cast
      rw [hc_mod_N]
      ring
  · change (!![(1 : ℤ), 0; 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
      !![a, B; (p : ℤ) * c, d - c * (b.val : ℤ)] * !![(1 : ℤ), (b.val : ℤ); 0, (p : ℤ)]
    rw [Matrix.eta_fin_two γ.val, ← ha_def, ← hb'_def, ← hc_def, ← hd_def]
    exact Newform.alpha_p_mul_eq_M_mul_T_p_upper_int (p : ℤ) a b' c d B (b.val : ℤ) hBp_int

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
