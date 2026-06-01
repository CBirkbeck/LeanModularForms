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
import LeanModularForms.HeckeRIngs.GL2.Newforms.MellinBridges

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

/-- For `p` prime with `p ∣ N`, the bad-prime Hecke operator `heckeT_n_cusp k p`
preserves `cuspFormsNew N k`, given the petN adjoint relation `h_adj` and
oldspace preservation `h_old` for `frickeBadAdjointCandidate k p`. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_fricke_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      petN (heckeT_n_cusp k p f) g =
        petN f (Newform.frickeBadAdjointCandidate k p g))
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOld N k →
        Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOld N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint hp hpN
    (Newform.frickeBadAdjointCandidate k p) h_adj h_old f hf

/-- `Newform.frickeSlashCuspForm` preserves `cuspFormsOld N k`: the Atkin-Lehner
involution `f ↦ f ∣[k] W_N` maps oldforms to oldforms. Stated as a named Prop
for downstream discharge. -/
def Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld
    (N : ℕ) [NeZero N] (k : ℤ) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOld N k → Newform.frickeSlashCuspForm g ∈ cuspFormsOld N k

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

/-- `Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld` holds iff the Fricke
slash of every level-raise oldform generator lies in `cuspFormsOld N k`. -/
theorem Newform.hasFrickeSlashCuspFormPreservesCuspFormsOld_iff_on_generators
    {N : ℕ} [NeZero N] {k : ℤ} :
    Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld N k ↔
      ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        IsOldformGenerator f →
          Newform.frickeSlashCuspForm f ∈ cuspFormsOld N k := by
  constructor
  · intro h_pres f h_gen
    exact h_pres f (Submodule.subset_span h_gen)
  · intro h_gen f hf
    refine Submodule.span_induction
      (p := fun (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ ↦
        Newform.frickeSlashCuspForm x ∈ cuspFormsOld N k)
      h_gen ?_ ?_ ?_ hf
    · change Newform.frickeSlashCuspForm
        (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ ihx ihy
      change Newform.frickeSlashCuspForm (x + y) ∈ cuspFormsOld N k
      rw [map_add]; exact Submodule.add_mem _ ihx ihy
    · intro c x _ ihx
      change Newform.frickeSlashCuspForm (c • x) ∈ cuspFormsOld N k
      rw [map_smul]; exact Submodule.smul_mem _ c ihx

/-- `Newform.frickeSlashCuspForm` preserves `cuspFormsOldExtended N k` iff it
maps every generator of the family
`IsOldformGenerator f ∨ IsLevelInclusionOldformGenerator f` into
`cuspFormsOldExtended N k`. -/
theorem Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended_iff_on_generators
    {N : ℕ} [NeZero N] {k : ℤ} :
    (∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsOldExtended N k →
        Newform.frickeSlashCuspForm g ∈ cuspFormsOldExtended N k) ↔
      ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        (IsOldformGenerator f ∨ IsLevelInclusionOldformGenerator f) →
          Newform.frickeSlashCuspForm f ∈ cuspFormsOldExtended N k := by
  constructor
  · intro h_pres f h_gen
    exact h_pres f (Submodule.subset_span h_gen)
  · intro h_gen g hg
    refine Submodule.span_induction
      (p := fun (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ ↦
        Newform.frickeSlashCuspForm x ∈ cuspFormsOldExtended N k)
      h_gen ?_ ?_ ?_ hg
    · change Newform.frickeSlashCuspForm
          (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOldExtended N k
      rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ ihx ihy
      change Newform.frickeSlashCuspForm (x + y) ∈ cuspFormsOldExtended N k
      rw [map_add]; exact Submodule.add_mem _ ihx ihy
    · intro c x _ ihx
      change Newform.frickeSlashCuspForm (c • x) ∈ cuspFormsOldExtended N k
      rw [map_smul]; exact Submodule.smul_mem _ c ihx

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
      show (k - 1) + (1 - k) = (0 : ℤ) from by ring, zpow_zero]
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
          (HeckeRing.GL2.levelRaiseMatrix d : GL (Fin 2) ℝ)) τ) from by ring,
    h_zpow_cancel, one_mul]

/-- For a proper divisor `M < N`, the Fricke slash of a trivially-included
level-`M` cusp form lands in the extended oldspace `cuspFormsOldExtended N k`. -/
theorem Newform.frickeSlashCuspForm_levelInclude_cusp_mem_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {M : ℕ} [NeZero M] (hMN : M ∣ N) (hMltN : M < N) {k : ℤ}
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    Newform.frickeSlashCuspForm (levelInclude_cusp hMN k g) ∈
      cuspFormsOldExtended N k := by
  obtain ⟨d, hd⟩ := id hMN
  have hd_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with hd_zero | hd_pos
    · simp [hd_zero] at hd; exact absurd hd (NeZero.ne N)
    · exact hd_pos
  haveI : NeZero d := ⟨hd_pos.ne'⟩
  have hd_lt : 1 < d := by
    by_contra! h_le
    rw [le_antisymm h_le hd_pos, Nat.mul_one] at hd
    exact hMltN.ne hd.symm
  haveI : NeZero (d * M) := ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne M)⟩
  have heq_N : N = d * M := by rw [mul_comm]; exact hd
  subst heq_N
  rw [frickeSlashCuspForm_levelInclude_cusp_eq_smul_levelRaise hMN g]
  refine Submodule.smul_mem _ _ (cuspFormsOld_le_cuspFormsOldExtended
    (Submodule.subset_span ?_))
  exact ⟨M, d, inferInstance, inferInstance, hd_lt, rfl, _, rfl⟩

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
  rw [show (((d * M : ℕ) : ℝ) : ℂ) = (d : ℂ) * (M : ℂ) from by push_cast; ring,
    show (((d * M : ℕ) : ℂ) * τ) = (d : ℂ) * (M : ℂ) * τ from by push_cast; ring,
    mul_zpow, mul_zpow ((d : ℂ) * (M : ℂ)) τ (-k), mul_zpow (d : ℂ) (M : ℂ) (-k),
    show (((M : ℝ) : ℂ) ^ (k - 1) : ℂ) = (M : ℂ) ^ (k - 1) from by push_cast; rfl,
    mul_zpow (M : ℂ) τ (-k)]
  have h_d_combine : (d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k) = (d : ℂ)⁻¹ := by
    rw [← zpow_add₀ hd, show (k - 1) + (-k) = (-1 : ℤ) from by ring, zpow_neg_one]
  rw [show X * ((d : ℂ) ^ (k - 1) * (M : ℂ) ^ (k - 1)) *
        ((d : ℂ) ^ (-k) * (M : ℂ) ^ (-k) * τ ^ (-k)) =
      ((d : ℂ) ^ (k - 1) * (d : ℂ) ^ (-k)) *
        (X * (M : ℂ) ^ (k - 1) * ((M : ℂ) ^ (-k) * τ ^ (-k))) from by ring]
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

/-- For a proper divisor `M` of `N` with `d := N/M > 1`, the Fricke slash of a
level-raised cusp form `levelRaise M d k g₀` lands in the extended oldspace
`cuspFormsOldExtended N k`. -/
theorem Newform.frickeSlashCuspForm_levelRaise_mem_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {M : ℕ} [NeZero M]
    {d : ℕ} [NeZero d] (hd_lt : 1 < d) (heq : d * M = N) {k : ℤ}
    (g₀ : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    Newform.frickeSlashCuspForm (heq ▸ levelRaise M d k g₀) ∈
      cuspFormsOldExtended N k := by
  subst heq
  have hMN : M ∣ d * M := ⟨d, (mul_comm d M)⟩
  have hMltN : M < d * M := by nlinarith [hd_lt, Nat.pos_of_neZero M]
  rw [frickeSlashCuspForm_levelRaise_eq_smul_levelInclude_cusp hMN g₀]
  exact Submodule.smul_mem _ _
    (levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _)

/-- `Newform.frickeSlashCuspForm` preserves `cuspFormsOldExtended N k`: the
Atkin-Lehner / Fricke involution maps the extended oldspace to itself. -/
theorem Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {k : ℤ} (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeSlashCuspForm g ∈ cuspFormsOldExtended N k :=
  Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended_iff_on_generators.mpr
    (fun f h_or ↦ h_or.elim
      (fun h_lr_gen ↦ by
        obtain ⟨M, d, hM_NeZero, hd_NeZero, hd_lt, heq, g₀, h_eq⟩ := h_lr_gen
        haveI := hM_NeZero
        haveI := hd_NeZero
        rw [← h_eq]
        exact Newform.frickeSlashCuspForm_levelRaise_mem_cuspFormsOldExtended
          hd_lt heq g₀)
      (fun h_inc_gen ↦ by
        obtain ⟨M, hM_NeZero, hMN, hMltN, g₀, h_eq⟩ := h_inc_gen
        haveI := hM_NeZero
        rw [← h_eq]
        exact Newform.frickeSlashCuspForm_levelInclude_cusp_mem_cuspFormsOldExtended
          hMN hMltN g₀)) g hg

/-- Named-Prop form of `Fricke` preservation on `cuspFormsOldExtended`. -/
def Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOldExtended N k →
    Newform.frickeSlashCuspForm g ∈ cuspFormsOldExtended N k

/-- `HasFrickeSlashCuspFormPreservesCuspFormsOldExtended` holds unconditionally. -/
theorem Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) :
    Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k :=
  Newform.frickeSlashCuspForm_preserves_cuspFormsOldExtended

/-- For the bad-prime case `p ∣ N`, the Hecke operator `heckeT_n_cusp k p`
preserves `cuspFormsOld N k`. Stated as a named Prop for downstream discharge. -/
def Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOld N k → heckeT_n_cusp k p g ∈ cuspFormsOld N k

/-- `frickeBadAdjointCandidate k p` preserves `cuspFormsOld N k`, assuming Fricke
and bad-prime Hecke each preserve `cuspFormsOld N k`. -/
lemma Newform.frickeBadAdjointCandidate_preserves_cuspFormsOld
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    {hp : p.Prime} {hpN : ¬ Nat.Coprime p N}
    (h_fricke_old :
      Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld N k)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld N k p hp hpN)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g ∈ cuspFormsOld N k) :
    Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOld N k := by
  rw [Newform.frickeBadAdjointCandidate_apply]
  exact h_fricke_old _ (h_T_p_old _ (h_fricke_old _ hg))

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

/-- The `petN` adjoint identity for the normalized bad-prime Fricke candidate,
packaged as a Prop. The heart of the bad-prime Atkin-Lehner adjoint theorem. -/
def Newform.HasBadPrimeFrickePetNAdjoint
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    petN (heckeT_n_cusp k p f) g =
      petN f (Newform.frickeBadAdjointCandidateNormalized k p g)

/-- For `p` prime with `p ∣ N`, the bad-prime Hecke operator `heckeT_n_cusp k p`
preserves `cuspFormsNew N k`, given the normalized petN-adjoint Prop `h_adj` and
oldspace preservation `h_old` of the normalized candidate. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_normalized_fricke_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOld N k →
        Newform.frickeBadAdjointCandidateNormalized k p g ∈ cuspFormsOld N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint hp hpN
    (Newform.frickeBadAdjointCandidateNormalized k p) h_adj h_old f hf

/-- `frickeBadAdjointCandidateNormalized` preserves `cuspFormsOld`, from the
unnormalized preservation. -/
lemma Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOld
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (h_unnormalized :
      ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsOld N k →
          Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOld N k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hg : g ∈ cuspFormsOld N k) :
    Newform.frickeBadAdjointCandidateNormalized k p g ∈ cuspFormsOld N k := by
  rw [Newform.frickeBadAdjointCandidateNormalized_apply]
  exact (cuspFormsOld N k).smul_mem _ (h_unnormalized g hg)

/-- For `p` prime with `p ∣ N`, the bad-prime Hecke operator `heckeT_n_cusp k p`
preserves `cuspFormsNew N k`, given the three classical inputs: the petN-adjoint
identity `h_adj` and the two oldspace-preservation Props `h_fricke_old`,
`h_T_p_old`.

References: Diamond–Shurman §5.5.1 (Atkin-Lehner involutions),
§5.6 Prop 5.6.2 (T_p preserves new/old subspaces); Miyake §4.6.5–4.6.6. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_fricke_old : Newform.HasFrickeSlashCuspFormPreservesCuspFormsOld N k)
    (h_T_p_old : Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_normalized_fricke_adjoint
    hp hpN h_adj
    (fun g hg ↦
      Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOld
        (Newform.frickeBadAdjointCandidate_preserves_cuspFormsOld
          (hp := hp) (hpN := hpN) h_fricke_old h_T_p_old)
        g hg)
    f hf

/-- For `p ∣ N`, given a Petersson-adjoint `T_adj` for `T_p` that preserves
`cuspFormsOldExtended`, the bad-prime Hecke operator preserves
`cuspFormsNewExtended`. -/
theorem heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_petersson_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (T_adj : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
             CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_adj : ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      petN (heckeT_n_cusp k p f) g = petN f (T_adj g))
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOldExtended N k → T_adj g ∈ cuspFormsOldExtended N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k := by
  let _ := hp
  let _ := hpN
  intro g hg
  rw [h_adj f g]
  exact hf _ (h_old g hg)

/-- Bad-prime Hecke preservation of `cuspFormsOldExtended`, as a named Prop;
the extended-oldspace companion of
`Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOld`. -/
def Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    g ∈ cuspFormsOldExtended N k → heckeT_n_cusp k p g ∈ cuspFormsOldExtended N k

/-- Named Prop for the gap that `heckeT_n_cusp k p` preserves `levelInclude_cusp`
images (the trivial-inclusion summand of `cuspFormsOldExtended`). -/
def Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : Nat.Prime p) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (M : ℕ) [NeZero M] (hMN : M ∣ N) (_hMltN : M < N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    heckeT_n_cusp k p (levelInclude_cusp hMN k g) ∈ cuspFormsOldExtended N k

/-- Bad-prime Hecke preservation of `cuspFormsOldExtended`, given the
trivial-inclusion preservation gap Prop `h_trivial`. -/
theorem Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_proof
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (h_trivial :
      Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended
        N k p hp hpN) :
    Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN := by
  intro f hf
  refine Submodule.span_induction
    (p := fun x _ ↦ heckeT_n_cusp k p x ∈ cuspFormsOldExtended N k)
    ?_ ?_ ?_ ?_ hf
  · rintro f₀ (⟨M, d, _, _, hd, heq, g, rfl⟩ | ⟨M, _, hMN, hMltN, g, rfl⟩)
    · by_cases hpd : p ∣ d
      · exact Newform.HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended_proof hp hpN
          M d heq hd hpd g
      · have hpd_cop : Nat.Coprime p d := (hp.coprime_iff_not_dvd).mpr hpd
        rw [heckeT_p_all_levelRaise_comm_divN p hp hpN M d heq hpd_cop g]
        apply cuspFormsOld_le_cuspFormsOldExtended
        refine Submodule.subset_span ?_
        exact ⟨M, d, inferInstance, inferInstance, hd, heq, _, rfl⟩
    · exact h_trivial M hMN hMltN g
  · change heckeT_n_cusp k p (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      cuspFormsOldExtended N k
    rw [heckeT_n_cusp_zero]; exact (cuspFormsOldExtended N k).zero_mem
  · intros f₁ f₂ _ _ ih₁ ih₂
    change heckeT_n_cusp k p (f₁ + f₂) ∈ cuspFormsOldExtended N k
    rw [heckeT_n_cusp_add]; exact (cuspFormsOldExtended N k).add_mem ih₁ ih₂
  · intros c f₁ _ ih
    change heckeT_n_cusp k p (c • f₁) ∈ cuspFormsOldExtended N k
    rw [heckeT_n_cusp_smul]; exact (cuspFormsOldExtended N k).smul_mem c ih

/-- Named Prop for the `Coprime p M ∧ p * M = N` corner case of trivial-inclusion
preservation. -/
def Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : Nat.Prime p) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (M : ℕ) [NeZero M] (hMN : M ∣ N) (_hMltN : M < N)
    (_hpcop_M : Nat.Coprime p M) (_hpM_eq : p * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    heckeT_n_cusp k p (levelInclude_cusp hMN k g) ∈ cuspFormsOldExtended N k

private lemma heckeT_n_cusp_prime_apply_of_not_coprime
    {L : ℕ} [NeZero L] {k : ℤ} {p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (hpL : ¬ Nat.Coprime p L)
    (F : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (heckeT_n_cusp k p F) z = heckeT_p_ut k p hp.pos ⇑F z := by
  show (heckeT_n k p F.toModularForm').toFun z = _
  rw [heckeT_n_prime k hp]
  exact congrFun (heckeT_p_all_not_coprime_apply k hp hpL _) z

/-- Trivial-inclusion preservation, reduced to the `Coprime p M ∧ p * M = N`
corner case `h_minimal`. -/
theorem Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_proof
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (h_minimal :
      Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal
        N k p hp hpN) :
    Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended N k p hp hpN := by
  intro M _ hMN hMltN g
  by_cases hpM : p ∣ M
  · have hpcop_M : ¬ Nat.Coprime p M := fun h ↦ hp.coprime_iff_not_dvd.mp h hpM
    have h_eq : heckeT_n_cusp k p (levelInclude_cusp hMN k g) =
        levelInclude_cusp hMN k (heckeT_n_cusp k p g) := by
      apply CuspForm.ext; intro z
      rw [levelInclude_cusp_coe, heckeT_n_cusp_prime_apply_of_not_coprime hp hpN,
        heckeT_n_cusp_prime_apply_of_not_coprime hp hpcop_M, levelInclude_cusp_coe]
    rw [h_eq]
    exact levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _
  · have hpcop_M : Nat.Coprime p M := hp.coprime_iff_not_dvd.mpr hpM
    have hp_dvd_N : p ∣ N := by
      by_contra h_ndvd; exact hpN (hp.coprime_iff_not_dvd.mpr h_ndvd)
    have hpM_dvd : p * M ∣ N := hpcop_M.mul_dvd_of_dvd_of_dvd hp_dvd_N hMN
    by_cases hpM_lt : p * M < N
    · haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
      have hpcop_pM : ¬ Nat.Coprime p (p * M) := fun h ↦
        hp.coprime_iff_not_dvd.mp h ⟨M, rfl⟩
      have h_eq : heckeT_n_cusp k p (levelInclude_cusp hMN k g) =
          levelInclude_cusp hpM_dvd k
            (heckeT_n_cusp k p (levelInclude_cusp (Dvd.intro_left p rfl) k g)) := by
        apply CuspForm.ext; intro z
        rw [levelInclude_cusp_coe, heckeT_n_cusp_prime_apply_of_not_coprime hp hpN,
          heckeT_n_cusp_prime_apply_of_not_coprime hp hpcop_pM]
        simp only [levelInclude_cusp_coe]
      rw [h_eq]
      exact levelInclude_cusp_mem_cuspFormsOldExtended hpM_dvd hpM_lt _
    · push Not at hpM_lt
      have hpM_eq : p * M = N := le_antisymm
        (Nat.le_of_dvd (NeZero.pos N) hpM_dvd) hpM_lt
      exact h_minimal M hMN hMltN hpcop_M hpM_eq g

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
  rw [h_glMap_eq, ModularForm.slash_apply, σ_levelRaiseMatrix, RingHom.id_apply,
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
  rw [show ((p : ℝ) ^ (k - 1) : ℂ) = (p : ℂ) ^ (k - 1) from by push_cast; rfl]
  ring

private lemma heckeT_n_cusp_levelInclude_cusp_eq_sub_smul_levelRaise_diamond
    {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} [NeZero p] (hp : Nat.Prime p)
    (hpcop_M : Nat.Coprime p M) (hMN : M ∣ p * M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
    heckeT_n_cusp k p (levelInclude_cusp hMN k g) =
      levelInclude_cusp hMN k (heckeT_n_cusp k p g) -
        (p : ℂ) ^ (k - 1) •
          levelRaise M p k (diamondOp_cusp k (ZMod.unitOfCoprime p hpcop_M) g) := by
  haveI : NeZero (p * M) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne M)⟩
  have hpN : ¬ Nat.Coprime p (p * M) := fun h ↦ hp.coprime_iff_not_dvd.mp h ⟨M, rfl⟩
  set a : (ZMod M)ˣ := ZMod.unitOfCoprime p hpcop_M
  set LR_p_D : CuspForm ((Gamma1 (p * M)).map (mapGL ℝ)) k :=
    levelRaise M p k (diamondOp_cusp k a g)
  apply CuspForm.ext; intro z
  rw [heckeT_n_cusp_prime_apply_of_not_coprime hp hpN, levelInclude_cusp_coe]
  show heckeT_p_ut k p hp.pos ⇑g z =
      (heckeT_n_cusp k p g) z - (p : ℂ) ^ (k - 1) * (LR_p_D : CuspForm _ _) z
  have h_T_M_apply : (heckeT_n_cusp k p g : CuspForm _ _) z =
      heckeT_p_ut k p hp.pos ⇑g z +
        ((⇑(diamondOp k a g.toModularForm') ∣[k]
          (T_p_lower p hp.pos : GL (Fin 2) ℚ)) z) := by
    show (heckeT_n k p g.toModularForm').toFun z = _
    rw [heckeT_n_prime k hp, heckeT_p_all_coprime k hp hpcop_M]
    rfl
  rw [h_T_M_apply, diamondOp_slash_T_p_lower_apply hp hpcop_M g z]
  ring

/-- Proof of the `Coprime p M ∧ p * M = N` minimal corner case of
trivial-inclusion preservation. -/
theorem Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal_proof
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal
      N k p hp hpN := by
  intro M _ hMN hMltN hpcop_M hpM_eq g
  subst hpM_eq
  rw [heckeT_n_cusp_levelInclude_cusp_eq_sub_smul_levelRaise_diamond hp hpcop_M hMN g]
  apply Submodule.sub_mem
  · exact levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN _
  · refine Submodule.smul_mem _ _ (cuspFormsOld_le_cuspFormsOldExtended
      (Submodule.subset_span ?_))
    exact ⟨M, p, inferInstance, inferInstance, hp.one_lt, rfl, _, rfl⟩

/-- Trivial-inclusion preservation, unconditional. -/
theorem Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended N k p hp hpN :=
  Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_proof hp hpN
    (Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_minimal_proof
      hp hpN)

/-- Bad-prime Hecke preservation of `cuspFormsOldExtended`, unconditional. -/
theorem Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN :=
  Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_proof hp hpN
    (Newform.HasHeckeT_n_cusp_TrivialInclusion_preserves_cuspFormsOldExtended_unconditional
      hp hpN)

/-- `frickeBadAdjointCandidate k p` preserves `cuspFormsOldExtended`, assuming
Fricke and bad-prime Hecke each preserve it. -/
lemma Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    {hp : p.Prime} {hpN : ¬ Nat.Coprime p N}
    (h_fricke_old :
      Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOldExtended N k := by
  rw [Newform.frickeBadAdjointCandidate_apply]
  exact h_fricke_old _ (h_T_p_old _ (h_fricke_old _ hg))

/-- `frickeBadAdjointCandidateNormalized` preserves `cuspFormsOldExtended`, from
the unnormalized preservation. -/
lemma Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (h_unnormalized :
      ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsOldExtended N k →
          Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOldExtended N k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidateNormalized k p g ∈
        cuspFormsOldExtended N k := by
  rw [Newform.frickeBadAdjointCandidateNormalized_apply]
  exact (cuspFormsOldExtended N k).smul_mem _ (h_unnormalized g hg)

/-- Bad-prime newspace-extended preservation from the petN-adjoint identity
`h_adj` and oldspace-extended preservation `h_old` of the normalized candidate. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_normalized_fricke_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOldExtended N k →
        Newform.frickeBadAdjointCandidateNormalized k p g ∈
            cuspFormsOldExtended N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_petersson_adjoint
    hp hpN
    (Newform.frickeBadAdjointCandidateNormalized k p) h_adj h_old f hf

/-- Bad-prime Hecke preservation of `cuspFormsNewExtended` from the three
classical inputs (the petN-adjoint identity `h_adj` and the two extended
oldspace-preservation Props) at the extended level. -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_fricke_old :
      Newform.HasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_normalized_fricke_adjoint
    hp hpN h_adj
    (fun g hg ↦
      Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended
        (Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended
          (hp := hp) (hpN := hpN) h_fricke_old h_T_p_old)
        g hg)
    f hf

/-- Bad-prime newspace-extended preservation needing only the petN-adjoint
identity `h_adj` and the extended-oldspace Hecke preservation `h_T_p_old`
(Fricke preservation being unconditional). -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs
    hp hpN h_adj
    (Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    h_T_p_old f hf

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
  isNorm : (ModularFormClass.qExpansion (1 : ℝ) toCuspForm).coeff 1 = 1

/-- For `f ∈ cuspFormsNewExtended` and `p ∣ N`, the bad-prime Hecke operator
`heckeT_n_cusp k p f` lies in the classical `cuspFormsNew N k`, given the
petN-adjoint identity `h_adj` and extended-oldspace preservation `h_T_p_old`. -/
theorem heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (h_T_p_old :
      Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended N k p hp hpN)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  cuspFormsNewExtended_le_cuspFormsNew
    (Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171
      hp hpN h_adj h_T_p_old f hf)

/-- Bad-prime newspace-extended preservation needing only the petN-adjoint
identity `h_adj` (the extended-oldspace input being unconditional). -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170_T171
    hp hpN h_adj
    (Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
      hp hpN)
    f hf

/-- Bad-prime classical-newspace consumer needing only the petN-adjoint identity
`h_adj`; the conclusion is in the classical `cuspFormsNew N k`. -/
theorem heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  cuspFormsNewExtended_le_cuspFormsNew
    (Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170
      hp hpN h_adj f hf)

/-- Final extended consumer needing only the petN-adjoint identity `h_adj` (the
Fricke and extended-oldspace inputs being unconditional). -/
theorem Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs_T170_only
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNewExtended N k :=
  Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_classicalInputs
    hp hpN h_adj
    (Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
      hp hpN)
    f hf

/-- `frickeBadAdjointCandidate` preserves `cuspFormsOldExtended` unconditionally. -/
lemma Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidate k p g ∈ cuspFormsOldExtended N k :=
  Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended
    (hp := hp) (hpN := hpN)
    (Newform.hasFrickeSlashCuspFormPreservesCuspFormsOldExtended N k)
    (Newform.HasHeckeT_n_cusp_at_divN_PreservesCuspFormsOldExtended_unconditional
      hp hpN)
    g hg

/-- `frickeBadAdjointCandidateNormalized` preserves `cuspFormsOldExtended`
unconditionally. -/
lemma Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsOldExtended N k) :
    Newform.frickeBadAdjointCandidateNormalized k p g ∈
        cuspFormsOldExtended N k :=
  Newform.frickeBadAdjointCandidateNormalized_preserves_cuspFormsOldExtended
    (Newform.frickeBadAdjointCandidate_preserves_cuspFormsOldExtended_unconditional
      hp hpN)
    g hg

/-- For `f ∈ cuspFormsNewExtended` and every prime `p`, the Hecke operator
`heckeT_n_cusp k p f` lies in the classical `cuspFormsNew N k`, with the
petN-adjoint hypothesis `h_adj_at_bad` required only at bad primes. -/
theorem heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_of_T170_unified
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (h_adj_at_bad : ¬ Nat.Coprime p N → Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k := by
  by_cases hpN : Nat.Coprime p N
  · exact heckeT_n_preserves_cuspFormsNew p hpN f
      (cuspFormsNewExtended_le_cuspFormsNew hf)
  · exact heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_at_divN_of_T170
      hp hpN (h_adj_at_bad hpN) f hf

/-- Bundled `NewformExtended` form of the unified Hecke consumer. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (h_adj_at_bad : ¬ Nat.Coprime p N → Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : NewformExtended N k) :
    heckeT_n_cusp k p f.toCuspForm ∈ cuspFormsNew N k :=
  heckeT_n_cusp_preserves_cuspFormsNew_of_NewformExtended_of_T170_unified
    hp h_adj_at_bad f.toCuspForm f.isNew

/-- For `(p, N) = 1`, every `NewformExtended` is preserved in `cuspFormsNew`
without any petN-adjoint hypothesis. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_coprime
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp_cop : Nat.Coprime p N) (f : NewformExtended N k) :
    heckeT_n_cusp k p f.toCuspForm ∈ cuspFormsNew N k :=
  heckeT_n_preserves_cuspFormsNew p hp_cop f.toCuspForm
    (cuspFormsNewExtended_le_cuspFormsNew f.isNew)

/-- Coprime arbitrary-`n` consumer for `NewformExtended`, by delegation to the
classical `heckeT_n_preserves_cuspFormsNew`. No petN-adjoint hypothesis needed. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_coprime_arbitrary_n
    {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} [NeZero n] (hn : Nat.Coprime n N)
    (f : NewformExtended N k) :
    heckeT_n_cusp k n f.toCuspForm ∈ cuspFormsNew N k :=
  heckeT_n_preserves_cuspFormsNew n hn f.toCuspForm
    (cuspFormsNewExtended_le_cuspFormsNew f.isNew)

private lemma heckeT_n_succ_pp_eq_at_bad_prime
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N) (v : ℕ) :
    haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : NeZero (p ^ (v + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    heckeT_n (N := N) k (p ^ (v + 1)) =
      heckeT_n k p * heckeT_n k (p ^ v) := by
  haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI : NeZero (p ^ (v + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rcases Nat.eq_zero_or_pos v with hv0 | hv_pos
  · subst hv0
    have h1 : heckeT_n (N := N) k (p ^ 1) = heckeT_n k p := by
      haveI : NeZero (p ^ 1) := ⟨pow_ne_zero _ hp.ne_zero⟩
      rw [heckeT_n_prime_pow k hp 1 Nat.one_pos, heckeT_ppow_one, heckeT_n_prime k hp]
    have h2 : heckeT_n (N := N) k (p ^ 0) = 1 := heckeT_n_one k
    rw [h1, h2, mul_one]
  · rw [heckeT_n_prime_pow k hp (v + 1) (Nat.succ_pos v),
      heckeT_n_prime k hp,
      heckeT_n_prime_pow k hp v hv_pos,
      heckeT_ppow_eq_pow_of_not_coprime k hp hpN (v + 1),
      heckeT_ppow_eq_pow_of_not_coprime k hp hpN v,
      pow_succ' (heckeT_p_all k p hp) v]

/-- For a bad prime `p ∣ N` with the petN-adjoint hypothesis `h_adj`, `T_{p^v}`
preserves `cuspFormsNewExtended` for every `v : ℕ`. -/
theorem NewformExtended.heckeT_pp_cusp_mem_cuspFormsNewExtended_at_bad_of_T170
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hpN : ¬ Nat.Coprime p N)
    (h_adj : Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (v : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
    heckeT_n_cusp k (p ^ v) f ∈ cuspFormsNewExtended N k := by
  induction v with
  | zero =>
    haveI : NeZero (p ^ 0) := ⟨by simp⟩
    have h_op : heckeT_n (N := N) k (p ^ 0) = 1 := heckeT_n_one k
    have h_eq : heckeT_n_cusp k (p ^ 0) f = f := by
      apply CuspForm.ext; intro z
      show (heckeT_n k (p ^ 0) f.toModularForm').toFun z = f z
      rw [h_op]; rfl
    rw [h_eq]; exact hf
  | succ v ih =>
    haveI : NeZero (p ^ v) := ⟨pow_ne_zero _ hp.ne_zero⟩
    haveI : NeZero (p ^ (v + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have h_step : heckeT_n_cusp k (p ^ (v + 1)) f =
        heckeT_n_cusp k p (heckeT_n_cusp k (p ^ v) f) := by
      apply CuspForm.ext; intro z
      show (heckeT_n k (p ^ (v + 1)) f.toModularForm').toFun z =
        ((heckeT_n k p) ((heckeT_n k (p ^ v)) f.toModularForm')).toFun z
      rw [heckeT_n_succ_pp_eq_at_bad_prime hp hpN v]; rfl
    rw [h_step]
    exact Newform.heckeT_n_cusp_preserves_cuspFormsNewExtended_at_divN_of_T170
      hp hpN h_adj _ ih

private lemma heckeT_n_cusp_mem_cuspFormsNewExtended_bad_only_step
    {N : ℕ} [NeZero N] {k : ℤ} (m : ℕ) (hm_gt : 1 < m)
    (h_bad : ∀ p, p.Prime → p ∣ m → ¬ Nat.Coprime p N)
    (h_adj : ∀ (p : ℕ) [NeZero p], p.Prime → p ∣ m →
      Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (ih : ∀ j, j < m → (hj : 0 < j) →
      (∀ p, p.Prime → p ∣ j → ¬ Nat.Coprime p N) →
      (∀ (p : ℕ) [NeZero p], p.Prime → p ∣ j →
        Newform.HasBadPrimeFrickePetNAdjoint N k p) →
      ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsNewExtended N k →
        haveI : NeZero j := ⟨by omega⟩
        heckeT_n_cusp k j g ∈ cuspFormsNewExtended N k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg : g ∈ cuspFormsNewExtended N k) :
    haveI : NeZero m := ⟨by omega⟩
    heckeT_n_cusp k m g ∈ cuspFormsNewExtended N k := by
  haveI : NeZero m := ⟨by omega⟩
  set p := m.minFac
  have hpp : p.Prime := Nat.minFac_prime (by omega : m ≠ 1)
  set v := m.factorization p
  have hpv_pos : 0 < p ^ v := pow_pos hpp.pos v
  have hdiv_pos : 0 < m / p ^ v :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) hpv_pos
  haveI : NeZero (p ^ v) := ⟨hpv_pos.ne'⟩
  haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
  haveI : NeZero p := ⟨hpp.ne_zero⟩
  have h_mid : heckeT_n_cusp k (m / p ^ v) g ∈ cuspFormsNewExtended N k :=
    ih (m / p ^ v) (heckeT_n_unfold_lt m hm_gt) hdiv_pos
      (fun q hq hqdiv ↦
        h_bad q hq (hqdiv.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p))))
      (fun q _ hq_prime hqdiv ↦
        h_adj q hq_prime (hqdiv.trans (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p))))
      g hg
  rw [show heckeT_n_cusp k m g =
      heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) g) from
    CuspForm.ext fun z ↦ heckeT_n_cusp_unfold m hm_gt g z]
  exact NewformExtended.heckeT_pp_cusp_mem_cuspFormsNewExtended_at_bad_of_T170
    hpp (h_bad p hpp (Nat.minFac_dvd m)) (h_adj p hpp (Nat.minFac_dvd m)) v _ h_mid

/-- For `n : ℕ` whose every prime factor divides `N`, with the petN-adjoint
hypothesis `h_adj_at_each` for each such prime, `T_n` preserves
`cuspFormsNewExtended`. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNewExtended_of_bad_only_T170
    {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ) [NeZero n]
    (h_bad_only : ∀ p, p.Prime → p ∣ n → ¬ Nat.Coprime p N)
    (h_adj_at_each : ∀ (p : ℕ) [NeZero p], p.Prime → p ∣ n →
      Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNewExtended N k) :
    heckeT_n_cusp k n f ∈ cuspFormsNewExtended N k := by
  suffices h : ∀ (m : ℕ) (_ : 0 < m),
      (∀ p, p.Prime → p ∣ m → ¬ Nat.Coprime p N) →
      (∀ (p : ℕ) [NeZero p], p.Prime → p ∣ m →
          Newform.HasBadPrimeFrickePetNAdjoint N k p) →
      ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
        g ∈ cuspFormsNewExtended N k →
        haveI : NeZero m := ⟨by omega⟩
        heckeT_n_cusp k m g ∈ cuspFormsNewExtended N k from
    h n (NeZero.pos n) h_bad_only h_adj_at_each f hf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm_pos h_bad h_adj g hg
    haveI : NeZero m := ⟨by omega⟩
    by_cases hm1 : m = 1
    · subst hm1
      rw [show heckeT_n_cusp k 1 g = g from
        CuspForm.ext fun z ↦ by rw [show (heckeT_n_cusp k 1 g) z =
          (heckeT_n k 1 g.toModularForm').toFun z from rfl, heckeT_n_one]; rfl]
      exact hg
    · exact heckeT_n_cusp_mem_cuspFormsNewExtended_bad_only_step m (by omega)
        h_bad h_adj ih g hg

/-- Bundled `NewformExtended`-level wrapper of the bad-only arbitrary-`n`
consumer. -/
theorem NewformExtended.heckeT_n_cusp_mem_cuspFormsNew_of_bad_only_T170
    {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ} [NeZero n]
    (h_bad_only : ∀ p, p.Prime → p ∣ n → ¬ Nat.Coprime p N)
    (h_adj_at_each : ∀ (p : ℕ) [NeZero p], p.Prime → p ∣ n →
      Newform.HasBadPrimeFrickePetNAdjoint N k p)
    (f : NewformExtended N k) :
    heckeT_n_cusp k n f.toCuspForm ∈ cuspFormsNew N k :=
  cuspFormsNewExtended_le_cuspFormsNew
    (NewformExtended.heckeT_n_cusp_mem_cuspFormsNewExtended_of_bad_only_T170
      n h_bad_only h_adj_at_each f.toCuspForm f.isNew)

end HeckeRing.GL2
