/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.SlashActionAuxil
import LeanModularForms.Eigenforms.ConductorTheorem
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import LeanModularForms.HeckeRIngs.GL2.Newforms.FrickeTwist

/-!
# Newforms: bad-prime Fricke adjoint candidate and the extended newspace

The bad-prime Hecke linear map and Fricke adjoint candidate with its auxiliary
discharges, the scalar-corrected bad-prime Fricke `petN` adjoint, and the
extended-oldspace / extended-newspace API (`NewformExtended`) for the SMO route.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The bad-prime Hecke operator `heckeT_n_cusp k n` packaged as a `ℂ`-linear
endomorphism of cusp forms, so it can be composed with
`Newform.frickeSlashCuspForm`. -/
noncomputable def Newform.heckeT_n_cusp_lin
    {N : ℕ} [NeZero N] (k : ℤ) (n : ℕ) [NeZero n] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := heckeT_n_cusp k n
  map_add' := heckeT_n_cusp_add n
  map_smul' c f := heckeT_n_cusp_smul n c f

/-- Bad-prime Fricke-conjugated adjoint candidate
`frickeSlashCuspForm ∘ heckeT_n_cusp_lin k p ∘ frickeSlashCuspForm`, the
`W_N · T_p · W_N`-style conjugate operator. -/
noncomputable def Newform.frickeBadAdjointCandidate
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  Newform.frickeSlashCuspForm ∘ₗ Newform.heckeT_n_cusp_lin k p ∘ₗ
    Newform.frickeSlashCuspForm

@[simp]
lemma Newform.frickeBadAdjointCandidate_apply
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Newform.frickeBadAdjointCandidate k p g =
      Newform.frickeSlashCuspForm
        (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) :=
  rfl



/-- The Atkin-Lehner / Fricke matrix `W_M` post-multiplied by the level-raising
matrix `α_d` equals `W_N` where `N = d * M`. -/
lemma Newform.frickeMatrix_mul_levelRaiseMatrix
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] :
    haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    (Newform.frickeMatrix M : GL (Fin 2) ℝ) *
        HeckeRing.GL2.levelRaiseMatrix d =
      Newform.frickeMatrix (d * M) := by
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Newform.frickeMatrix, HeckeRing.GL2.levelRaiseMatrix,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_mul, Matrix.mul_apply,
      Fin.sum_univ_two, mul_comm d M]


private lemma frickeSlashCuspForm_levelInclude_cusp_eq_smul_levelRaise
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] (hMN : M ∣ d * M) {k : ℤ}
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    Newform.frickeSlashCuspForm (levelInclude_cusp hMN k g) =
      (d : ℂ) ^ (k - 1) • levelRaise M d k (Newform.frickeSlashCuspForm g) := by
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  set Y : CuspForm ((Gamma1 M).map (mapGL ℝ)) k := Newform.frickeSlashCuspForm g
  apply CuspForm.ext
  intro τ
  have h_zpow_cancel : ((d : ℂ) ^ (k - 1)) * ((d : ℂ) ^ (1 - k)) = 1 := by
    rw [← zpow_add₀ (Nat.cast_ne_zero.mpr (NeZero.ne d)),
      show (k - 1) + (1 - k) = (0 : ℤ) by ring, zpow_zero]
  show (⇑(Newform.frickeSlashCuspForm
      (levelInclude_cusp hMN k g)) : UpperHalfPlane → ℂ) τ =
      (⇑((d : ℂ) ^ (k - 1) • levelRaise M d k Y) : UpperHalfPlane → ℂ) τ
  rw [show (⇑(Newform.frickeSlashCuspForm
        (levelInclude_cusp hMN k g)) : UpperHalfPlane → ℂ) =
      (⇑(levelInclude_cusp hMN k g) : UpperHalfPlane → ℂ) ∣[k]
        (Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) from rfl,
    show (⇑(levelInclude_cusp hMN k g) : UpperHalfPlane → ℂ) = ⇑g from rfl,
    (Newform.frickeMatrix_mul_levelRaiseMatrix (M := M) (d := d)).symm,
    SlashAction.slash_mul]
  show ((⇑g ∣[k] (Newform.frickeMatrix M : GL (Fin 2) ℝ)) ∣[k]
        (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ =
    ((d : ℂ) ^ (k - 1)) * ((⇑(levelRaise M d k Y) : UpperHalfPlane → ℂ) τ)
  rw [show (⇑(levelRaise M d k Y) : UpperHalfPlane → ℂ) τ =
      ((d : ℂ) ^ (1 - k)) *
        ((⇑Y : UpperHalfPlane → ℂ) ∣[k]
          (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ from rfl,
    show (⇑Y : UpperHalfPlane → ℂ) = ⇑g ∣[k]
      (Newform.frickeMatrix M : GL (Fin 2) ℝ) from rfl,
    show ((d : ℂ) ^ (k - 1)) *
        (((d : ℂ) ^ (1 - k)) *
          (((⇑g ∣[k] (Newform.frickeMatrix M : GL (Fin 2) ℝ)) ∣[k]
            (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ)) =
      (((d : ℂ) ^ (k - 1)) * ((d : ℂ) ^ (1 - k))) *
        (((⇑g ∣[k] (Newform.frickeMatrix M : GL (Fin 2) ℝ)) ∣[k]
          (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ) by ring,
    h_zpow_cancel, one_mul]

private lemma alpha_d_smul_frickeMatrix_dM_smul_eq_frickeMatrix_M_smul
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] (τ : UpperHalfPlane) :
    haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ) •
        ((Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) • τ) =
      (Newform.frickeMatrix M : GL (Fin 2) ℝ) • τ := by
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  apply UpperHalfPlane.ext
  rw [coe_levelRaiseMatrix_smul, Newform.frickeMatrix_smul, Newform.frickeMatrix_smul]
  have hd_ne : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  have hM_ne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  push_cast
  field_simp

private lemma levelRaise_frickeSlash_scalar_eq
    {d M : ℕ} {k : ℤ} (hd : (d : ℂ) ≠ 0) (X τ : ℂ) :
    X * ((↑(d * M) : ℝ) : ℂ) ^ (k - 1) * (((d * M : ℕ) : ℂ) * τ) ^ (-k) =
      (d : ℂ)⁻¹ * (X * ((M : ℝ) : ℂ) ^ (k - 1) * ((M : ℂ) * τ) ^ (-k)) := by
  rw [show (((d * M : ℕ) : ℝ) : ℂ) = (d : ℂ) * (M : ℂ) by push_cast; ring,
    show (((d * M : ℕ) : ℂ) * τ) = (d : ℂ) * (M : ℂ) * τ by push_cast; ring,
    mul_zpow, mul_zpow ((d : ℂ) * (M : ℂ)) τ (-k), mul_zpow (d : ℂ) (M : ℂ) (-k),
    show (((M : ℝ) : ℂ) ^ (k - 1) : ℂ) = (M : ℂ) ^ (k - 1) by push_cast; rfl,
    mul_zpow (M : ℂ) τ (-k)]
  have h_d_combine : (d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) = (d : ℂ)⁻¹ := by
    rw [← zpow_add₀ hd, show (k - 1) + (-k) = (-1 : ℤ) by ring, zpow_neg_one]
  rw [show X * ((d : ℂ) ^ (k - 1) * (M : ℂ) ^ (k - 1)) *
        ((d : ℂ) ^ (-k) * (M : ℂ) ^ (-k) * τ ^ (-k)) =
      ((d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k)) *
        (X * (M : ℂ) ^ (k - 1) * ((M : ℂ) ^ (-k) * τ ^ (-k))) by ring]
  rw [h_d_combine]

private lemma frickeSlashCuspForm_levelRaise_eq_smul_levelInclude_cusp
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] (hMN : M ∣ d * M) {k : ℤ}
    (g₀ : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
    Newform.frickeSlashCuspForm (levelRaise M d k g₀) =
      (d : ℂ)⁻¹ • levelInclude_cusp hMN k (Newform.frickeSlashCuspForm g₀) := by
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  set h_inclusion : CuspForm ((Gamma1 (d * M)).map (mapGL ℝ)) k :=
    levelInclude_cusp hMN k (Newform.frickeSlashCuspForm g₀)
  apply CuspForm.ext
  intro τ
  show (⇑(Newform.frickeSlashCuspForm
        (levelRaise M d k g₀)) : UpperHalfPlane → ℂ) τ =
      (⇑((d : ℂ)⁻¹ • h_inclusion) : UpperHalfPlane → ℂ) τ
  rw [show (⇑(Newform.frickeSlashCuspForm
          (levelRaise M d k g₀)) : UpperHalfPlane → ℂ) =
      (⇑(levelRaise M d k g₀) : UpperHalfPlane → ℂ) ∣[k]
        (Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) from rfl,
    Newform.frickeMatrix_slash_apply,
    show (⇑(levelRaise M d k g₀) : UpperHalfPlane → ℂ)
        ((Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) • τ) =
      levelRaiseFun d k (⇑g₀)
        ((Newform.frickeMatrix (d * M) : GL (Fin 2) ℝ) • τ) from rfl,
    levelRaiseFun_apply,
    alpha_d_smul_frickeMatrix_dM_smul_eq_frickeMatrix_M_smul]
  show ⇑g₀ ((Newform.frickeMatrix M : GL (Fin 2) ℝ) • τ) *
        ((↑(d * M) : ℝ) : ℂ) ^ (k - 1) * (((d * M : ℕ) : ℂ) * (τ : ℂ)) ^ (-k) =
      (⇑((d : ℂ)⁻¹ • h_inclusion) : UpperHalfPlane → ℂ) τ
  rw [show (⇑((d : ℂ)⁻¹ • h_inclusion) : UpperHalfPlane → ℂ) τ =
        (d : ℂ)⁻¹ * (⇑h_inclusion : UpperHalfPlane → ℂ) τ from rfl,
    show (⇑h_inclusion : UpperHalfPlane → ℂ) =
        (⇑(Newform.frickeSlashCuspForm g₀) : UpperHalfPlane → ℂ) from rfl,
    show (⇑(Newform.frickeSlashCuspForm g₀) : UpperHalfPlane → ℂ) =
        (⇑g₀ : UpperHalfPlane → ℂ) ∣[k]
          (Newform.frickeMatrix M : GL (Fin 2) ℝ) from rfl,
    Newform.frickeMatrix_slash_apply]
  exact levelRaise_frickeSlash_scalar_eq (Nat.cast_ne_zero.mpr (NeZero.ne d))
    (⇑g₀ ((Newform.frickeMatrix M : GL (Fin 2) ℝ) • τ)) (τ : ℂ)

/-- For the bad-prime case `p ∣ N`, the Hecke operator `heckeT_n_cusp k p`
preserves `cuspFormsOld N k`. Stated as a named Prop for downstream discharge. -/
def Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOld N k → heckeT_n_cusp k p g ∈ cuspFormsOld N k


/-- Scalar-corrected bad-prime Fricke adjoint candidate
`(frickeSquareScalar N k)⁻¹ • frickeBadAdjointCandidate k p`, the operator whose
`petN` adjoint identity holds with no extra scalar (the classical
`W_N⁻¹ T_p W_N`). -/
noncomputable def Newform.frickeBadAdjointCandidateNormalized
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (Newform.frickeSquareScalar N k)⁻¹ • Newform.frickeBadAdjointCandidate k p

/-- Underlying-function form of the normalized candidate. -/
@[simp]
lemma Newform.frickeBadAdjointCandidateNormalized_apply
    {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Newform.frickeBadAdjointCandidateNormalized k p g =
      (Newform.frickeSquareScalar N k)⁻¹ •
        Newform.frickeBadAdjointCandidate k p g :=
  rfl

private lemma heckeT_n_cusp_prime_apply_of_not_coprime
    {L : ℕ} [NeZero L] {k : ℤ} {p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (hpL : ¬ Nat.Coprime p L)
    (F : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (heckeT_n_cusp k p F) z = heckeT_p_ut k p hp.pos ⇑F z := by
  show (heckeT_n k p F.toModularForm').toFun z = _
  rw [heckeT_n_prime k hp]
  exact congrFun (heckeT_p_all_not_coprime_apply k hp hpL _) z

private lemma diamondOp_slash_T_p_lower_apply
    {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpcop : Nat.Coprime p M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm') ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) z =
      ((p : ℂ) ^ (k - 1)) * ⇑(levelRaise M p k
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g)) z := by
  have h_glMap_eq : (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) = levelRaiseMatrix p := by
    apply Units.ext
    ext i j
    show ((T_p_lower p hp.pos : Matrix (Fin 2) (Fin 2) ℚ).map
          (algebraMap ℚ ℝ)) i j =
         (!![(p : ℝ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℝ) i j
    rw [T_p_lower_coe]
    fin_cases i
    · fin_cases j
      · show ((p : ℚ) : ℝ) = (p : ℝ); norm_num
      · show ((0 : ℚ) : ℝ) = 0; norm_num
    · fin_cases j
      · show ((0 : ℚ) : ℝ) = 0; norm_num
      · show ((1 : ℚ) : ℝ) = (1 : ℝ); norm_num
  show (⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm') ∣[k]
        glMap (T_p_lower p hp.pos)) z = _
  rw [h_glMap_eq, ModularForm.slash_apply, σ_levelRaiseMatrix, ContinuousAlgEquiv.refl_apply,
      abs_levelRaiseMatrix_det_val, denom_levelRaiseMatrix, one_zpow, mul_one]
  have h_LR_apply : ⇑(levelRaise M p k
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g)) z =
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g) (levelRaiseMatrix p • z) := by
    show levelRaiseFun p k ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpcop) g) z = _
    rw [levelRaiseFun_apply]
  rw [h_LR_apply]
  show ⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm')
        (levelRaiseMatrix p • z) * ((p : ℝ) ^ (k - 1) : ℂ) =
      (p : ℂ) ^ (k - 1) *
        ⇑(diamondOp k (ZMod.unitOfCoprime p hpcop) g.toModularForm')
          (levelRaiseMatrix p • z)
  rw [show ((p : ℝ) ^ (k - 1) : ℂ) = (p : ℂ) ^ (k - 1) by push_cast; rfl]
  ring

/-- The intersection of `cuspFormsOldExtended` and `cuspFormsNewExtended` is
trivial. Mirrors `cuspFormsOld_disjoint_cuspFormsNew`. -/
theorem cuspFormsOldExtended_disjoint_cuspFormsNewExtended
    {N : ℕ} [NeZero N] {k : ℤ} :
    Disjoint (cuspFormsOldExtended N k) (cuspFormsNewExtended N k) := by
  rw [Submodule.disjoint_def]
  intro f hf_old hf_new
  exact petN_definite f (hf_new f hf_old)

/-- Bundled extended newform: an `Eigenform` together with extended-newspace
membership and normalisation. Strictly stronger than `Newform N k`. -/
@[ext]
structure NewformExtended (N : ℕ) [NeZero N] (k : ℤ)
    extends Eigenform N k where
  /-- The form is in the *extended* new subspace `cuspFormsNewExtended`. -/
  isNew : toCuspForm ∈ cuspFormsNewExtended N k
  /-- Normalisation at the canonical Fourier period: the first Fourier
  coefficient is `1`. -/
  isNorm : (UpperHalfPlane.qExpansion (1 : ℝ) toCuspForm).coeff 1 = 1

end HeckeRing.GL2
