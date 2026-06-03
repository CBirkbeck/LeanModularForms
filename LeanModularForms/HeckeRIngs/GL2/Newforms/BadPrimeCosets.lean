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

/-- Function-level slash-action analog of the GL-level Fricke rewrite:
`(f ∣[k] W_N) ∣[k] glMap (T_p_upper p hp b) = (f ∣[k] T_p_lower_with_offset N hp b) ∣[k] W_N`. -/
lemma Newform.slash_frickeMatrix_T_p_upper_rewrite {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : 0 < p) (b : ℕ) (f : UpperHalfPlane → ℂ) :
    (f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      (f ∣[k] (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)) ∣[k]
        (Newform.frickeMatrix N : GL (Fin 2) ℝ) := by
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul,
    Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix]

open UpperHalfPlane MeasureTheory ModularGroup in
private lemma Newform.slash_W_N_T_p_upper_W_N_eq_smul_T_p_lower_with_offset
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p) (b : ℕ)
    (g : UpperHalfPlane → ℂ) :
    ((g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ) =
      Newform.frickeSquareScalar N k •
        (g ∣[k] (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)) := by
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul,
    show (Newform.frickeMatrix N : GL (Fin 2) ℝ) *
          ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) *
            (Newform.frickeMatrix N : GL (Fin 2) ℝ)) =
        (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) *
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) *
            (Newform.frickeMatrix N : GL (Fin 2) ℝ)) by
      rw [← mul_assoc,
          Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix,
          mul_assoc]]
  rw [SlashAction.slash_mul, SlashAction.slash_mul,
    Newform.slash_frickeMatrix_frickeMatrix]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The function representation of the normalized bad-prime Fricke adjoint candidate
equals the `b`-sum of `T_p_lower_with_offset`-slashed `⇑g`:
`⇑(frickeBadAdjointCandidateNormalized k p g) = Σ_b ⇑g ∣ T_p_lower_with_offset N hp.pos b`. -/
lemma Newform.frickeBadAdjointCandidateNormalized_coe_eq_bsum_lower
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(Newform.frickeBadAdjointCandidateNormalized k p g) : UpperHalfPlane → ℂ) =
      ∑ b ∈ Finset.range p,
        (⇑g : UpperHalfPlane → ℂ) ∣[k]
          (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) := by
  rw [Newform.frickeBadAdjointCandidateNormalized_apply]
  show ((Newform.frickeSquareScalar N k)⁻¹ •
      (⇑(Newform.frickeBadAdjointCandidate k p g) : UpperHalfPlane → ℂ)) = _
  rw [Newform.frickeBadAdjointCandidate_apply, Newform.frickeSlashCuspForm_coe,
    show (⇑(heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) :
        UpperHalfPlane → ℂ) =
      ∑ b ∈ Finset.range p,
        (⇑(Newform.frickeSlashCuspForm g) ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) by
      change (heckeT_n k p ((Newform.frickeSlashCuspForm g).toModularForm') :
            UpperHalfPlane → ℂ) =
          heckeT_p_ut k p hp.pos ⇑(Newform.frickeSlashCuspForm g)
      rw [heckeT_n_prime k hp,
        heckeT_p_all_not_coprime_apply (k := k) hp hpN
          (Newform.frickeSlashCuspForm g).toModularForm']
      rfl]
  have h_term : ∀ b ∈ Finset.range p,
      ((⇑(Newform.frickeSlashCuspForm g) ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) =
        Newform.frickeSquareScalar N k •
          ((⇑g : UpperHalfPlane → ℂ) ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ)) := by
    intro b _
    rw [Newform.frickeSlashCuspForm_coe]
    show ((((⇑g : UpperHalfPlane → ℂ) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) =
        Newform.frickeSquareScalar N k •
          ((⇑g : UpperHalfPlane → ℂ) ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ))
    exact Newform.slash_W_N_T_p_upper_W_N_eq_smul_T_p_lower_with_offset hp.pos b ⇑g
  rw [SlashAction.sum_slash, Finset.sum_congr rfl h_term, ← Finset.smul_sum, smul_smul]
  have h_c_ne : Newform.frickeSquareScalar N k ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (by norm_num))
      (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  rw [inv_mul_cancel₀ h_c_ne, one_smul]

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

/-- Left-coset injectivity for the bad-prime upper family at level `Γ₁(N)`: if
`mapGL ℝ γ * glMap (T_p_upper p hp b₁.val) = glMap (T_p_upper p hp b₂.val)` for
`γ ∈ Γ₁(N)`, then `b₁ = b₂` in `Fin p`. -/
theorem Newform.T_p_upper_left_coset_injective_Gamma1
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p)
    (b1 b2 : Fin p) (γ : SL(2, ℤ)) (_hγ : γ ∈ Gamma1 N)
    (h : (mapGL ℝ γ : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp b1.val) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp b2.val) : GL (Fin 2) ℝ)) :
    b1 = b2 := by
  have hmat : (((mapGL ℝ γ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)) *
      (((glMap (T_p_upper p hp b1.val) : GL (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (((glMap (T_p_upper p hp b2.val) : GL (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) := by
    simpa [Matrix.GeneralLinearGroup.coe_mul] using congrArg Units.val h
  have hγ_mat : ((mapGL ℝ γ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      γ.val.map (algebraMap ℤ ℝ) := mapGL_coe_matrix γ
  rw [Newform.glMap_T_p_upper_coe_real hp b1.val,
    Newform.glMap_T_p_upper_coe_real hp b2.val, hγ_mat] at hmat
  have h00 := congr_fun (congr_fun hmat 0) 0
  have h01 := congr_fun (congr_fun hmat 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, algebraMap_int_eq,
    Int.coe_castRingHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    mul_one, mul_zero, add_zero] at h00 h01
  have h00_int : γ.val 0 0 = 1 := mod_cast h00
  rw [h00_int] at h01
  push_cast at h01
  have h_real : (γ.val 0 1 : ℝ) * (p : ℝ) = (b2.val : ℝ) - (b1.val : ℝ) := by linarith
  have h_diff : γ.val 0 1 * (p : ℤ) = (b2.val : ℤ) - (b1.val : ℤ) := mod_cast h_real
  exact Newform.fin_eq_of_mul_eq_sub hp b1 b2 _ h_diff

open scoped Pointwise in
/-- The left `Γ₁(N)`-cosets `Γ₁(N).map (mapGL ℝ) · {β_b} ⊆ GL(2, ℝ)` for
`b ∈ Fin p` are pairwise disjoint. -/
theorem Newform.T_p_upper_left_cosets_pairwiseDisjoint_Gamma1
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p) :
    (Set.univ : Set (Fin p)).PairwiseDisjoint
      (fun b ↦ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) := by
  intro b1 _ b2 _ hb_ne
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨g1, hg1, β1, hβ1_in, hx_eq1⟩ ⟨g2, hg2, β2, hβ2_in, hx_eq2⟩
  rw [Set.mem_singleton_iff] at hβ1_in hβ2_in
  subst hβ1_in hβ2_in
  dsimp only at hx_eq1 hx_eq2
  rw [← hx_eq2] at hx_eq1
  obtain ⟨γ1, hγ1, rfl⟩ := Subgroup.mem_map.mp hg1
  obtain ⟨γ2, hγ2, rfl⟩ := Subgroup.mem_map.mp hg2
  apply hb_ne
  apply Newform.T_p_upper_left_coset_injective_Gamma1 N hp b1 b2 (γ2⁻¹ * γ1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ2) hγ1)
  rw [map_mul, map_inv, mul_assoc, hx_eq1, ← mul_assoc, inv_mul_cancel, one_mul]

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

/-- Per-`γ` Hecke double-coset decomposition at level `Γ₁(N)` for bad primes
(DS Lemma 5.5.2(a) variant): for a prime `p ∣ N` and `γ ∈ Γ₁(N)`, the product
`α_p · γ` factors as `γ' · β_b` in `GL(2, ℝ)` for some `γ' ∈ Γ₁(N)` and
`b ∈ Fin p`, where `α_p := T_p_upper p hp.pos 0` and `β_b := T_p_upper p hp.pos b.val`. -/
theorem Newform.alpha_p_mul_Gamma1_eq_Gamma1_mul_T_p_upper_b
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ∃ (γ' : SL(2, ℤ)) (b : Fin p), γ' ∈ Gamma1 N ∧
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
          (mapGL ℝ γ : GL (Fin 2) ℝ) =
        (mapGL ℝ γ' : GL (Fin 2) ℝ) *
          (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) := by
  obtain ⟨γ', b, hγ'_mem, h_int⟩ :=
    Newform.exists_Gamma1_mul_T_p_upper_int hp hpN γ hγ
  exact ⟨γ', b, hγ'_mem,
    Newform.glMap_T_p_upper_zero_mul_mapGL_eq_of_int hp.pos γ γ' b.val h_int⟩

private lemma Newform.glMap_T_p_upper_eq_glMap_zero_mul_shiftSL {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        (mapGL ℝ (shiftSL (b : ℤ)) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  change ((T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ)) i j =
    ((((T_p_upper p hp 0 : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ)) *
      ((shiftSL (b : ℤ) : SL(2, ℤ)).val.map (algebraMap ℤ ℝ))) i j)
  simp only [T_p_upper_coe, shiftSL, Matrix.map_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Matrix.SpecialLinearGroup.coe_mk]
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Pointwise in
/-- The double coset `Γ₁(N) · α_p · Γ₁(N) ⊆ GL(2, ℝ)` (where
`α_p := glMap (T_p_upper p hp.pos 0)`) decomposes as the union over `b : Fin p`
of the left cosets `Γ₁(N) · β_b`, where `β_b := glMap (T_p_upper p hp.pos b.val)`. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_eq_iUnion_T_p_upper_left_cosets
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) =
    (⋃ b : Fin p,
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) := by
  ext x
  constructor
  · rintro ⟨y, hy, g2, hg2, rfl⟩
    obtain ⟨g1, hg1, α', hα', rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hα'
    subst hα'
    obtain ⟨γ2_int, hγ2_int, rfl⟩ := Subgroup.mem_map.mp hg2
    obtain ⟨γ2', b, hγ2'_mem, h_eq⟩ :=
      Newform.alpha_p_mul_Gamma1_eq_Gamma1_mul_T_p_upper_b hp hpN γ2_int hγ2_int
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    refine ⟨g1 * (mapGL ℝ γ2' : GL (Fin 2) ℝ), ?_,
      (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ), rfl, ?_⟩
    · exact Subgroup.mul_mem _ hg1
        (Subgroup.mem_map.mpr ⟨γ2', hγ2'_mem, rfl⟩)
    · change (g1 * (mapGL ℝ γ2' : GL (Fin 2) ℝ)) *
          (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) =
        (g1 * (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) *
          (mapGL ℝ γ2_int : GL (Fin 2) ℝ)
      rw [mul_assoc, ← h_eq, ← mul_assoc]
  · intro hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    obtain ⟨g, hg, β', hβ', rfl⟩ := hb
    rw [Set.mem_singleton_iff] at hβ'
    subst hβ'
    refine ⟨g * (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ), ?_,
      (mapGL ℝ (shiftSL (b.val : ℤ)) : GL (Fin 2) ℝ), ?_, ?_⟩
    · exact ⟨g, hg, glMap (T_p_upper p hp.pos 0), rfl, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨shiftSL (b.val : ℤ), shiftSL_mem_Gamma1 N _, rfl⟩
    · change (g * (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) *
          (mapGL ℝ (shiftSL (b.val : ℤ)) : GL (Fin 2) ℝ) =
        g * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)
      rw [mul_assoc, ← Newform.glMap_T_p_upper_eq_glMap_zero_mul_shiftSL hp.pos b.val]

open scoped Pointwise in
/-- The double coset `Γ₁(N) · α_p · Γ₁(N)` as a disjoint union of `p` left
`Γ₁(N)`-cosets indexed by `Fin p`: the decomposition equality together with
left-coset pairwise disjointness. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) =
    (⋃ b : Fin p,
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) ∧
    (Set.univ : Set (Fin p)).PairwiseDisjoint
      (fun b ↦ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) :=
  ⟨Newform.alpha_p_Gamma1_doubleCoset_eq_iUnion_T_p_upper_left_cosets N (p := p) hp hpN,
    Newform.T_p_upper_left_cosets_pairwiseDisjoint_Gamma1 N (p := p) hp.pos⟩

open scoped Pointwise in
/-- Each element of the bad-prime double coset `Γ₁(N) · α_p · Γ₁(N)` lies in the
left `Γ₁(N)`-coset of a unique `β_b`, `b : Fin p`. -/
theorem Newform.existsUnique_T_p_upper_left_coset_index_of_mem_alpha_p_doubleCoset
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) {x : GL (Fin 2) ℝ}
    (hx : x ∈
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)))) :
    ∃! b : Fin p,
      x ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) := by
  have hpart :=
    Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets N (p := p) hp hpN
  rw [hpart.1] at hx
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
  refine ⟨b, hb, ?_⟩
  intro c hc
  by_contra hne
  exact Set.disjoint_left.mp (hpart.2 (Set.mem_univ b) (Set.mem_univ c) fun h ↦ hne h.symm) hb hc

open scoped Pointwise in
/-- Each element `x` of the bad-prime double coset factors as `x = γ · β_b` with
`γ ∈ Γ₁(N).map (mapGL ℝ)` and a unique `b : Fin p`. -/
theorem Newform.existsUnique_T_p_upper_left_factor_of_mem_alpha_p_doubleCoset
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) {x : GL (Fin 2) ℝ}
    (hx : x ∈
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)))) :
    ∃! b : Fin p, ∃ γ : GL (Fin 2) ℝ,
      γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) ∧
        γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) = x := by
  obtain ⟨b, hb, huniq⟩ :=
    Newform.existsUnique_T_p_upper_left_coset_index_of_mem_alpha_p_doubleCoset
      N (p := p) hp hpN hx
  refine ⟨b, ?_, ?_⟩
  · obtain ⟨γ, hγ, y, hy, hmul⟩ := hb
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨γ, hγ, hmul⟩
  · intro c hc
    obtain ⟨γ', hγ', hmul'⟩ := hc
    exact huniq c ⟨γ', hγ', glMap (T_p_upper p hp.pos c.val), rfl, hmul'⟩

open scoped Pointwise in
/-- Membership in the bad-prime double coset as a left-factor biconditional:
`x ∈ Γ₁(N)·α_p·Γ₁(N) ↔ ∃ b ∃ γ ∈ Γ₁(N), γ · β_b = x`. -/
theorem Newform.mem_alpha_p_Gamma1_doubleCoset_iff_exists_T_p_upper_left_factor
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) {x : GL (Fin 2) ℝ} :
    x ∈
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) ↔
      ∃ b : Fin p, ∃ γ : GL (Fin 2) ℝ,
        γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) ∧
          γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) = x := by
  refine ⟨?_, ?_⟩
  · intro hx
    obtain ⟨b, hb, _⟩ :=
      Newform.existsUnique_T_p_upper_left_factor_of_mem_alpha_p_doubleCoset
        N (p := p) hp hpN hx
    exact ⟨b, hb⟩
  · rintro ⟨b, γ, hγ, hmul⟩
    rw [(Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets N (p := p) hp hpN).1]
    exact Set.mem_iUnion.mpr ⟨b, ⟨γ, hγ, glMap (T_p_upper p hp.pos b.val), rfl, hmul⟩⟩

open scoped Pointwise in
/-- Membership in the double-coset-translated tile `Γ₁(N)·α_p·Γ₁(N) • D`: every
`z` equals `(γ · β_b) • w` for some `b : Fin p`, `γ ∈ Γ₁(N)`, `w ∈ D`. -/
theorem Newform.mem_alpha_p_Gamma1_doubleCoset_smul_set_iff_exists_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) {z : UpperHalfPlane} :
    z ∈
      (((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D) ↔
      ∃ b : Fin p,
        ∃ γ : GL (Fin 2) ℝ,
          γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) ∧
            ∃ w ∈ D,
              (γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) • w = z := by
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx, w, hw, hsmul⟩
    rw [Newform.mem_alpha_p_Gamma1_doubleCoset_iff_exists_T_p_upper_left_factor
      N (p := p) hp hpN] at hx
    obtain ⟨b, γ, hγ, hmul⟩ := hx
    subst hmul
    exact ⟨b, γ, hγ, w, hw, hsmul⟩
  · rintro ⟨b, γ, hγ, w, hw, hsmul⟩
    refine ⟨γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ), ?_, w, hw, hsmul⟩
    rw [Newform.mem_alpha_p_Gamma1_doubleCoset_iff_exists_T_p_upper_left_factor
      N (p := p) hp hpN]
    exact ⟨b, γ, hγ, rfl⟩

open scoped Pointwise in
/-- Nested `iUnion` form of the double-coset-translated tile:
`(Γ₁(N) · α_p · Γ₁(N)) • D = ⋃ b ⋃ γ ⋃ (_ : γ ∈ Γ₁(N)), (γ · β_b) • D`. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D =
      Set.iUnion (fun b : Fin p ↦
        Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
            γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
              Set (GL (Fin 2) ℝ))} ↦
          (((γ : GL (Fin 2) ℝ) *
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) • D))) := by
  ext z
  rw [Newform.mem_alpha_p_Gamma1_doubleCoset_smul_set_iff_exists_T_p_upper_left_factor_smul
    N (p := p) hp hpN D]
  simp only [Set.mem_iUnion, Set.mem_smul_set]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, γ, hγ, w, hw, hsmul⟩
    exact ⟨b, ⟨γ, hγ⟩, w, hw, hsmul⟩
  · rintro ⟨b, ⟨γ, hγ⟩, w, hw, hsmul⟩
    exact ⟨b, γ, hγ, w, hw, hsmul⟩

open scoped Pointwise in
/-- `q`-tile specialization of the bad-prime double-coset tile equality. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_qOut_inv_fd_eq_iUnion_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
        ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)) =
      Set.iUnion (fun b : Fin p ↦
        Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
            γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
              Set (GL (Fin 2) ℝ))} ↦
          (((γ : GL (Fin 2) ℝ) *
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))) := by
  simpa using
    Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_T_p_upper_left_factor_smul
      N (p := p) hp hpN ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))

open scoped Pointwise in
/-- `q`-aggregate tile-set equality for the bad-prime double coset. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_iUnion_qOut_inv_fd_eq_iUnion_q_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))) =
      Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
        Set.iUnion (fun b : Fin p ↦
          Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
              γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
                Set (GL (Fin 2) ℝ))} ↦
            (((γ : GL (Fin 2) ℝ) *
              (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
                ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))))) := by
  refine Set.iUnion_congr fun q ↦ ?_
  exact Newform.alpha_p_Gamma1_doubleCoset_smul_qOut_inv_fd_eq_iUnion_T_p_upper_left_factor_smul
    N (p := p) hp hpN q

open scoped Pointwise in

open scoped Pointwise in
/-- `Γ₁`-action regrouping for one bad-prime upper representative. -/
theorem Newform.iUnion_Gamma1_T_p_upper_left_factor_smul_eq_Gamma1_smul_T_p_upper_left_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (b : Fin p)
    (D : Set UpperHalfPlane) :
    Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
        γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ))} ↦
      (((γ : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) • D)) =
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
        Set (GL (Fin 2) ℝ)) •
        ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • D) := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_smul_set]
  constructor
  · rintro ⟨γ, w, hw, hzw⟩
    refine ⟨(γ : GL (Fin 2) ℝ), γ.property,
      (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • w, ?_, ?_⟩
    · exact ⟨w, hw, rfl⟩
    · simpa [mul_smul] using hzw
  · rintro ⟨γ, hγ, y, hy, hzy⟩
    rcases hy with ⟨w, hw, hyw⟩
    refine ⟨⟨γ, hγ⟩, w, hw, ?_⟩
    rw [mul_smul, show (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • w = y from hyw]
    exact hzy

open scoped Pointwise in
/-- `Γ₁`-action form of the bad-prime double-coset tile equality. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_Gamma1_smul_T_p_upper_left_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D =
      Set.iUnion (fun b : Fin p ↦
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ)) •
          ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • D)) := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_T_p_upper_left_factor_smul
    N (p := p) hp hpN D]
  refine Set.iUnion_congr fun b ↦ ?_
  exact Newform.iUnion_Gamma1_T_p_upper_left_factor_smul_eq_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp b D

open scoped Pointwise in
/-- Whole-`q`-domain `Γ₁`-action form of the bad-prime double-coset tile equality. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_iUnion_q_Gamma1_smul_T_p_upper_left_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
        (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))) =
      Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
        Set.iUnion (fun b : Fin p ↦
          (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))) := by
  rw [Set.smul_iUnion]
  refine Set.iUnion_congr fun q ↦ ?_
  exact Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp hpN ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))

open scoped Pointwise in
/-- Set-action regrouping pulling `Γ₁(N)` out of the `b`-iUnion in the
double-coset tile equality, giving the `Γ₁(N) • (⋃_b β_b • D)` shape. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_Gamma1_smul_iUnion_T_p_upper_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D =
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
        Set.iUnion (fun b : Fin p ↦
          (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • D) := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp hpN D, Set.smul_iUnion]

open scoped Pointwise in
/-- Whole-`q`-domain set-action regrouping pulling `Γ₁(N)` out of the
`(q, b)`-iUnion: the bad-prime double coset acting on the SL(2,ℤ)-fundamental
cover `⋃_q q.out⁻¹ • fd` as a single `Γ₁(N)`-orbit of the per-`(q, b)` tile family. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
        (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))) =
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
        Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
          Set.iUnion (fun b : Fin p ↦
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))) := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_iUnion_q_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp hpN, Set.smul_iUnion]
  refine Set.iUnion_congr fun q ↦ ?_
  rw [Set.smul_iUnion]

open UpperHalfPlane MeasureTheory in

open UpperHalfPlane MeasureTheory in
/-- Whole-`q`-domain set-integral form of the regrouping: the integral over
`(Γ₁(N) · α_p · Γ₁(N)) • ⋃_q q.out⁻¹ • fd` rewrites as the integral over
`Γ₁(N) • ⋃_q ⋃_b β_b · q.out⁻¹ • fd`. -/
theorem Newform.setIntegral_alpha_p_doubleCoset_smul_whole_qOut_inv_fd_eq_setIntegral_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h : UpperHalfPlane → ℂ) :
    ∫ τ in
      (((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
            ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
          (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
            (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))),
        h τ ∂μ_hyp =
      ∫ τ in
        ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
          Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦
            Set.iUnion (fun b : Fin p ↦
              (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
                ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))),
        h τ ∂μ_hyp := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    N (p := p) hp hpN]

open UpperHalfPlane MeasureTheory in

/-- Determinant of `T_p_lower_with_offset`. -/
lemma Newform.T_p_lower_with_offset_det (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (Newform.T_p_lower_with_offset N hp b).det.val = (p : ℝ) := by
  change ((Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ)
  rw [Newform.T_p_lower_with_offset_coe]
  simp [Matrix.det_fin_two]

/-- Positive determinant for `T_p_lower_with_offset`. -/
lemma Newform.T_p_lower_with_offset_det_pos (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    0 < (Newform.T_p_lower_with_offset N hp b).det.val := by
  rw [Newform.T_p_lower_with_offset_det]
  exact mod_cast hp

open UpperHalfPlane MeasureTheory in

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

/-- Determinant of `T_p_lower_with_offset_adjugate`. -/
lemma Newform.T_p_lower_with_offset_adjugate_det (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (Newform.T_p_lower_with_offset_adjugate N hp b).det.val = (p : ℝ) := by
  change ((Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ)
  rw [Newform.T_p_lower_with_offset_adjugate_coe]
  simp [Matrix.det_fin_two]

/-- Positive determinant for `T_p_lower_with_offset_adjugate`. -/
lemma Newform.T_p_lower_with_offset_adjugate_det_pos (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    0 < (Newform.T_p_lower_with_offset_adjugate N hp b).det.val := by
  rw [Newform.T_p_lower_with_offset_adjugate_det]
  exact mod_cast hp

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
