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
