/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1
import LeanModularForms.Modularforms.PeterssonInner
import LeanModularForms.Modularforms.PeterssonLevelN
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Hecke adjoint theory: FD-transport infrastructure.

The Hecke conjugate intersection group `Γ_p(α)`, fundamental-domain transport
adapters, and their `PSL(2, ℝ)` ambient instantiations.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

open CongruenceSubgroup Pointwise ConjAct in
/-- The Hecke conjugate intersection group `Γ_p(α) := conjGL Γ₁(N) α ⊓ Γ₁(N)`. -/
noncomputable def Gamma_p_α (α : GL (Fin 2) ℚ) : Subgroup SL(2, ℤ) :=
  conjGL (Gamma1 N) (α.map (Rat.castHom ℝ)) ⊓ Gamma1 N

open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(α)` has finite index in `SL(2, ℤ)`. -/
theorem Gamma_p_α_finiteIndex (α : GL (Fin 2) ℚ) :
    (Gamma_p_α (N := N) α).FiniteIndex := by
  have : (conjGL (Gamma1 N) (α.map (Rat.castHom ℝ))).FiniteIndex :=
    ((Gamma1_is_congruence N).conjGL α).finiteIndex
  show (conjGL (Gamma1 N) (α.map (Rat.castHom ℝ)) ⊓ Gamma1 N).FiniteIndex
  exact inferInstance

open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(α) ≤ Γ₁(N)`. -/
lemma Gamma_p_α_le_Gamma1 (α : GL (Fin 2) ℚ) :
    Gamma_p_α (N := N) α ≤ Gamma1 N :=
  inf_le_right

open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(α)` has finite index in `Γ₁(N)`. -/
theorem Gamma_p_α_finiteIndex_in_Gamma1 (α : GL (Fin 2) ℚ) :
    ((Gamma_p_α (N := N) α).subgroupOf (Gamma1 N)).FiniteIndex := by
  have : (Gamma_p_α (N := N) α).FiniteIndex := Gamma_p_α_finiteIndex α
  exact Subgroup.instFiniteIndex_subgroupOf _ _

open CongruenceSubgroup Pointwise ConjAct in
/-- `Γ_p(α)` conjugation embedding. -/
lemma Gamma_p_α_conj_mem_Gamma1 (α : GL (Fin 2) ℚ)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    ∃ δ ∈ Gamma1 N,
      ((mapGL ℝ δ : GL (Fin 2) ℝ)) =
        (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
          (mapGL ℝ γ : GL (Fin 2) ℝ) *
          ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ := by
  rcases hγ with ⟨h_conj, _⟩
  rcases mem_conjGL.mp h_conj with ⟨δ, hδ_mem, hδ_eq⟩
  exact ⟨δ, hδ_mem, hδ_eq⟩

open CongruenceSubgroup Pointwise ConjAct in
/-- `conjGL` ↔ `ConjAct.toConjAct` GL-level identity. -/
lemma conjGL_map_eq_conjAct_inv_smul_inter
    (Γ : Subgroup SL(2, ℤ)) (g : GL (Fin 2) ℝ) :
    (conjGL Γ g).map (mapGL ℝ) =
      (ConjAct.toConjAct g⁻¹ • (Γ.map (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ))) ⊓
        (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ).range := by
  rw [conjGL, Subgroup.map_comap_eq, inf_comm]

open CongruenceSubgroup Pointwise ConjAct in
/-- Conjugation-by-α function `Γ_p(α) → Γ₁(N)`. -/
noncomputable def Gamma_p_α_conjBy (α : GL (Fin 2) ℚ)
    (γ : Gamma_p_α (N := N) α) : Gamma1 N :=
  ⟨Classical.choose (Gamma_p_α_conj_mem_Gamma1 α γ.property),
    (Classical.choose_spec (Gamma_p_α_conj_mem_Gamma1 α γ.property)).1⟩

open CongruenceSubgroup Pointwise ConjAct in
/-- Defining equality of `Gamma_p_α_conjBy`:
`mapGL ℝ (Gamma_p_α_conjBy α γ) = α · mapGL ℝ γ · α⁻¹` in `GL (Fin 2) ℝ`. -/
lemma Gamma_p_α_conjBy_spec (α : GL (Fin 2) ℚ)
    (γ : Gamma_p_α (N := N) α) :
    (mapGL ℝ ((Gamma_p_α_conjBy α γ : SL(2, ℤ))) : GL (Fin 2) ℝ) =
      (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ : SL(2, ℤ))) : GL (Fin 2) ℝ) *
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ :=
  (Classical.choose_spec (Gamma_p_α_conj_mem_Gamma1 α γ.property)).2

open CongruenceSubgroup Pointwise ConjAct in
/-- Injectivity of `Gamma_p_α_conjBy`. -/
lemma Gamma_p_α_conjBy_injective (α : GL (Fin 2) ℚ) :
    Function.Injective (Gamma_p_α_conjBy (N := N) α) := by
  intro γ₁ γ₂ h
  apply Subtype.ext
  have h_mapGL :
      (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ₁ : SL(2, ℤ))) : GL (Fin 2) ℝ) *
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ =
      (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ₂ : SL(2, ℤ))) : GL (Fin 2) ℝ) *
        ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))⁻¹ := by
    rw [← Gamma_p_α_conjBy_spec α γ₁, congrArg Subtype.val h,
      Gamma_p_α_conjBy_spec α γ₂]
  have h_γ : (mapGL ℝ ((γ₁ : SL(2, ℤ))) : GL (Fin 2) ℝ) =
      mapGL ℝ ((γ₂ : SL(2, ℤ))) := by
    have h_step1 : (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
        (mapGL ℝ ((γ₁ : SL(2, ℤ))) : GL (Fin 2) ℝ) =
        (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) * mapGL ℝ ((γ₂ : SL(2, ℤ))) := by
      have hh1 := congrArg (· * (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) h_mapGL
      simp only [inv_mul_cancel_right] at hh1
      exact hh1
    exact mul_left_cancel h_step1
  exact mapGL_injective h_γ

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Slash by α is `Γ_p(α)`-invariant on Γ₁(N)-cusp forms. -/
lemma slash_α_Gamma_p_α_invariant (α : GL (Fin 2) ℚ)
    (f : ℍ → ℂ)
    (hf : ∀ δ ∈ Gamma1 N,
      f ∣[k] ((mapGL ℝ δ : GL (Fin 2) ℝ)) = f)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    (f ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
      ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
    f ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) := by
  obtain ⟨δ, hδ_mem, hδ_eq⟩ := Gamma_p_α_conj_mem_Gamma1 α hγ
  have hαγ : (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) *
      (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ δ : GL (Fin 2) ℝ) * (α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ) := by
    rw [hδ_eq]
    group
  rw [← SlashAction.slash_mul, hαγ, SlashAction.slash_mul, hf δ hδ_mem]

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Cusp-form specialization of `slash_α_Gamma_p_α_invariant`. -/
lemma slash_α_Gamma_p_α_invariant_cuspForm
    (α : GL (Fin 2) ℚ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) α) :
    ((⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
      ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
    (⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) := by
  refine slash_α_Gamma_p_α_invariant α (⇑f) ?_ hγ
  intro δ hδ
  rw [show ((mapGL ℝ δ : GL (Fin 2) ℝ)) =
        (((δ : SL(2, ℤ)) : GL (Fin 2) ℝ)) from rfl, ← ModularForm.SL_slash]
  exact slash_Gamma1_eq f δ hδ

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Finite-index FD-transport reduction. -/
lemma slash_α_Gamma_p_α_invariant_at_FD_decomp_witness
    (α : GL (Fin 2) ℚ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∀ {γ : SL(2, ℤ)}, γ ∈ Gamma_p_α (N := N) α →
      ((⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ))) ∣[k]
        ((mapGL ℝ γ : GL (Fin 2) ℝ)) =
      (⇑f) ∣[k] ((α.map (Rat.castHom ℝ) : GL (Fin 2) ℝ)) :=
  fun hγ ↦ slash_α_Gamma_p_α_invariant_cuspForm α f hγ

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- FD-shift adapter (generic `GL(2, ℝ)⁺` form). -/
theorem isFundamentalDomain_GLPos_smul_conjAct
    (α' : GL(2, ℝ)⁺) {H₁ : Subgroup (GL(2, ℝ)⁺)} {s : Set ℍ}
    (hs : MeasureTheory.IsFundamentalDomain (H₁ : Subgroup (GL(2, ℝ)⁺)) s μ_hyp) :
    MeasureTheory.IsFundamentalDomain
      ((ConjAct.toConjAct α' • H₁ : Subgroup (GL(2, ℝ)⁺)))
      (α' • s) μ_hyp :=
  MeasureTheory.IsFundamentalDomain.smul_of_eq_conjAct hs rfl

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- FD-shift adapter for `Γ_p(α)` (`GL(2, ℝ)⁺` lift). -/
theorem Gamma_p_α_GLPos_lift_FD_smul_conjAct
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) {s : Set ℍ}
    (hs : IsFundamentalDomain
      ((Gamma_p_α (N := N) α).map
        (ModularGroup.coeHom : SL(2, ℤ) →* GL(2, ℝ)⁺))
      s μ_hyp) :
    IsFundamentalDomain
      (ConjAct.toConjAct α' •
        ((Gamma_p_α (N := N) α).map
          (ModularGroup.coeHom : SL(2, ℤ) →* GL(2, ℝ)⁺)) :
          Subgroup GL(2, ℝ)⁺)
      (α' • s) μ_hyp :=
  isFundamentalDomain_GLPos_smul_conjAct α' hs

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Finite-index FD decomposition for `Γ_p(α) ≤ Γ₁(N)` (generic ambient). -/
theorem Gamma_p_α_FD_finite_index_decomp
    {G_outer : Type*} [Group G_outer] [MulAction G_outer ℍ]
    [MeasurableConstSMul G_outer ℍ] [SMulInvariantMeasure G_outer ℍ μ_hyp]
    (α : GL (Fin 2) ℚ) (φ : SL(2, ℤ) →* G_outer) {D : Set ℍ}
    (hD : IsFundamentalDomain ((Gamma1 N).map φ) D μ_hyp)
    [Countable
      (((Gamma1 N).map φ) ⧸
        (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ)))] :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ))
      (⋃ q : ((Gamma1 N).map φ) ⧸
              (((Gamma_p_α (N := N) α).map φ).subgroupOf ((Gamma1 N).map φ)),
        ((q.out : ((Gamma1 N).map φ)) : G_outer)⁻¹ • D)
      μ_hyp :=
  hD.subgroup_iUnion_out_smul _

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Generic projective FD-shift adapter at `PSL(2, ℝ)`. -/
theorem isFundamentalDomain_PSL_R_smul_conjAct
    (α : PSL(2, ℝ)) {H₁ : Subgroup (PSL(2, ℝ))} {s : Set ℍ}
    (hs : MeasureTheory.IsFundamentalDomain (H₁ : Subgroup (PSL(2, ℝ))) s μ_hyp) :
    MeasureTheory.IsFundamentalDomain
      ((ConjAct.toConjAct α • H₁ : Subgroup (PSL(2, ℝ))))
      (α • s) μ_hyp :=
  MeasureTheory.IsFundamentalDomain.smul_of_eq_conjAct hs rfl

open CongruenceSubgroup in
/-- Finite-index instance for the projective image of `Γ_p(α)` inside the
projective image of `Γ₁(N)`. -/
instance Gamma_p_α_image_PSL_R_finiteIndex_in_Gamma1_image
    (α : GL (Fin 2) ℚ) :
    (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
      ((Gamma1 N).map SL2Z_to_PSL2R)).FiniteIndex := by
  have : (Gamma_p_α (N := N) α).FiniteIndex := Gamma_p_α_finiteIndex α
  have : (Gamma_p_α (N := N) α ⊔ SL2Z_to_PSL2R.ker).FiniteIndex :=
    Subgroup.finiteIndex_of_le le_sup_left
  refine ⟨?_⟩
  show ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).relIndex
        ((Gamma1 N).map SL2Z_to_PSL2R) ≠ 0
  rw [Subgroup.relIndex_map_map]
  exact (Subgroup.instFiniteIndex_subgroupOf
    (Gamma1 N ⊔ SL2Z_to_PSL2R.ker)
    (H := Gamma_p_α (N := N) α ⊔ SL2Z_to_PSL2R.ker)).index_ne_zero

open CongruenceSubgroup in
/-- `Fintype` of the right-coset space. -/
noncomputable instance Gamma_p_α_image_PSL_R_quotient_fintype
    (α : GL (Fin 2) ℚ) :
    Fintype
      (((Gamma1 N).map SL2Z_to_PSL2R) ⧸
        (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
          ((Gamma1 N).map SL2Z_to_PSL2R))) :=
  Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Finite-index FD decomposition for `Γ_p(α) ≤ Γ₁(N)` at the `PSL(2, ℝ)`
ambient. -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp
    (α : GL (Fin 2) ℚ)
    [Countable
      (((Gamma1 N).map SL2Z_to_PSL2R) ⧸
        (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
          ((Gamma1 N).map SL2Z_to_PSL2R)))] :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
        ((Gamma1 N).map SL2Z_to_PSL2R))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
          Gamma1_fundDomain_PSL N)
      μ_hyp := by
  apply Gamma_p_α_FD_finite_index_decomp α SL2Z_to_PSL2R
  rw [map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R]
  exact isFundamentalDomain_Gamma1_PSL_R

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- `_auto` wrapper for the `PSL(2, ℝ)` FD decomposition. -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp_auto
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
        ((Gamma1 N).map SL2Z_to_PSL2R))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
          Gamma1_fundDomain_PSL N)
      μ_hyp :=
  Gamma_p_α_PSL_R_FD_finite_index_decomp α

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Projective FD-shift adapter for `Γ_p(α)` at `PSL(2, ℝ)`. -/
theorem Gamma_p_α_PSL_R_lift_FD_smul_conjAct
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) {s : Set ℍ}
    (hs : IsFundamentalDomain
      ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) s μ_hyp) :
    IsFundamentalDomain
      ((ConjAct.toConjAct (GLPos_to_PSL_R_term α') •
        ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)) :
          Subgroup (PSL(2, ℝ)))
      (GLPos_to_PSL_R_term α' • s) μ_hyp :=
  isFundamentalDomain_PSL_R_smul_conjAct (GLPos_to_PSL_R_term α') hs

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- Projective shifted FD-decomposition (general α/α'). -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) :
    IsFundamentalDomain
      ((ConjAct.toConjAct (GLPos_to_PSL_R_term α') •
        ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)) :
          Subgroup PSL(2, ℝ))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        (GLPos_to_PSL_R_term α' *
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp := by
  have h_ambient :
      IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
        (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
                (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                  ((Gamma1 N).map SL2Z_to_PSL2R)),
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
            (Gamma1_fundDomain_PSL N : Set ℍ))
        μ_hyp := by
    have h_image := (Gamma_p_α_PSL_R_FD_finite_index_decomp_auto (N := N) α).image_of_equiv
      (Equiv.refl ℍ) (MeasureTheory.Measure.QuasiMeasurePreserving.id _)
      ((Subgroup.subgroupOfEquivOfLe (Subgroup.map_mono (Gamma_p_α_le_Gamma1 α))).symm.toEquiv)
      (fun _ _ ↦ rfl)
    simp only [Equiv.coe_refl, Set.image_id] at h_image
    exact h_image
  have h_set_eq :
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        (GLPos_to_PSL_R_term α' *
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ)) =
      GLPos_to_PSL_R_term α' •
        (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
                (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
                  ((Gamma1 N).map SL2Z_to_PSL2R)),
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
            (Gamma1_fundDomain_PSL N : Set ℍ)) := by
    rw [Set.smul_set_iUnion]
    refine Set.iUnion_congr ?_
    intro q
    exact mul_smul _ _ _
  rw [h_set_eq]
  exact Gamma_p_α_PSL_R_lift_FD_smul_conjAct α α' h_ambient

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Packaged per-α `Γ_p(α)`-fundamental-domain set. -/
noncomputable def Gamma_p_α_fundDomain_PSL (α : GL (Fin 2) ℚ) : Set ℍ :=
  ⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
          (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
            ((Gamma1 N).map SL2Z_to_PSL2R)),
    ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹ •
      (Gamma1_fundDomain_PSL N : Set ℍ)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- The shifted FD set as `α' • Γ_p(α)-FD`. -/
theorem Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted_eq_smul
    (α : GL (Fin 2) ℚ) (α' : GL(2, ℝ)⁺) :
    (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
            (((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R).subgroupOf
              ((Gamma1 N).map SL2Z_to_PSL2R)),
      (GLPos_to_PSL_R_term α' *
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) =
    GLPos_to_PSL_R_term α' • Gamma_p_α_fundDomain_PSL (N := N) α := by
  unfold Gamma_p_α_fundDomain_PSL
  rw [Set.smul_set_iUnion]
  exact Set.iUnion_congr fun q ↦ mul_smul _ _ _

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Generic SL outer-quotient ↔ scaled `Gamma1_fundDomain_PSL` integral bridge. -/
theorem setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h (Gamma1_fundDomain_PSL N) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, h τ ∂μ_hyp := by
  classical
  calc ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_fd_eq_fdo h q
    _ = ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ slToPslQuot q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        sum_SL_tile_eq_fiberwise_PSL_tile h h_inv
    _ = (slToPslQuot_fiberCard N) • ∑ q' : PSL(2, ℤ) ⧸ imageGamma1_PSL N,
          ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        congr 1
        convert slToPslQuot_fiberCard_eq q' using 2
        congr
    _ = (slToPslQuot_fiberCard N) • ∫ τ in Gamma1_fundDomain_PSL N, h τ ∂μ_hyp := by
        rw [← setIntegral_Gamma1_fundDomain_PSL_eq_sum h h_int]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Petersson-integrand specialization of the generic SL outer-quotient bridge. -/
theorem peterssonInner_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
    (slToPslQuot_fiberCard N) •
      ∫ τ in Gamma1_fundDomain_PSL N, petersson k ⇑f ⇑g τ ∂μ_hyp :=
  setIntegral_Gamma1_fundDomain_PSL_eq_SL_outer_q_sum
    (petersson k ⇑f ⇑g)
    (fun γ hγ τ ↦ petersson_Gamma1_invariant f g γ hγ τ)
    (integrableOn_petersson_Gamma1_fundDomain_PSL f g)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Generic per-`q` SL slash-domain reducer. -/
theorem peterssonInner_fd_slash_q_eq_setIntegral_shifted_fd
    (F G : ℍ → ℂ) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    peterssonInner k fd (F ∣[k] (q.out : SL(2, ℤ))⁻¹) (G ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
      petersson k F G τ ∂μ_hyp := by
  simp only [peterssonInner]
  simp_rw [petersson_slash_SL]
  rw [← Set.image_smul,
    ← (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Per-`q` slash-compose plus slash-domain reducer. -/
theorem peterssonInner_slash_compose_q_eq_setIntegral_shifted_fd
    (A B : GL (Fin 2) ℝ) (q : SL(2, ℤ) ⧸ Gamma1 N) (F G : ℍ → ℂ) :
    peterssonInner k fd
      (F ∣[k] (A * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹)))
      (G ∣[k] (B * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹))) =
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
      petersson k (F ∣[k] A) (G ∣[k] B) τ ∂μ_hyp := by
  rw [SlashAction.slash_mul, SlashAction.slash_mul]
  exact peterssonInner_fd_slash_q_eq_setIntegral_shifted_fd
    (F ∣[k] A) (G ∣[k] B) q

open CongruenceSubgroup ModularGroup MeasureTheory in
/-- The image of `Γ_p(α)` in `PSL(2, ℤ) = SL(2, ℤ) / {±I}`. -/
noncomputable def image_Gamma_p_α_PSL (α : GL (Fin 2) ℚ) : Subgroup PSL(2, ℤ) :=
  (Gamma_p_α (N := N) α).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))

open CongruenceSubgroup in
/-- `image_Gamma_p_α_PSL α` has finite index in `PSL(2, ℤ)`. -/
instance image_Gamma_p_α_PSL_finiteIndex (α : GL (Fin 2) ℚ) :
    (image_Gamma_p_α_PSL (N := N) α).FiniteIndex := by
  have : (Gamma_p_α (N := N) α).FiniteIndex :=
    Gamma_p_α_finiteIndex (N := N) α
  refine ⟨fun h ↦ ?_⟩
  have h_dvd : (image_Gamma_p_α_PSL (N := N) α).index ∣
      (Gamma_p_α (N := N) α).index := by
    apply Subgroup.index_map_dvd
    exact QuotientGroup.mk_surjective
  rw [h] at h_dvd
  exact Subgroup.FiniteIndex.index_ne_zero (Nat.eq_zero_of_zero_dvd h_dvd)

open CongruenceSubgroup in
/-- `Fintype` of the right-coset space `PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL α`. -/
noncomputable instance image_Gamma_p_α_PSL_quotient_fintype (α : GL (Fin 2) ℚ) :
    Fintype (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :=
  Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup in
/-- `Fintype` of `SL(2, ℤ) ⧸ Γ_p(α)`. -/
noncomputable instance Gamma_p_α_quotient_fintype (α : GL (Fin 2) ℚ) :
    Fintype (SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) := by
  have : (Gamma_p_α (N := N) α).FiniteIndex :=
    Gamma_p_α_finiteIndex (N := N) α
  exact Subgroup.fintypeQuotientOfFiniteIndex

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Canonical PSL-coset fundamental domain for `image_Gamma_p_α_PSL α`. -/
noncomputable def Gamma_p_α_fundDomain_PSL_canonical (α : GL (Fin 2) ℚ) : Set ℍ :=
  ⋃ q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
    ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ)

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL_canonical α` is a fundamental domain for
`image_Gamma_p_α_PSL α` acting on `ℍ`. -/
theorem isFundamentalDomain_Gamma_p_α_PSL_canonical (α : GL (Fin 2) ℚ) :
    MeasureTheory.IsFundamentalDomain (image_Gamma_p_α_PSL (N := N) α)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp :=
  isFundamentalDomain_fdo_PSL.subgroup_iUnion_out_smul
    (image_Gamma_p_α_PSL (N := N) α)

open CongruenceSubgroup in
/-- The natural quotient map `SL ⧸ Γ_p(α) → PSL ⧸ image_Γ_p(α)_PSL`,
sending each `Γ_p(α)`-coset `[g]` to the `image_Gamma_p_α_PSL`-coset `[PSL.mk g]`. -/
noncomputable def slToPslQuot_Gamma_p_α (α : GL (Fin 2) ℚ) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α →
      PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply (QuotientGroup.eq).mpr
      have h_psl : (QuotientGroup.mk a : PSL(2, ℤ))⁻¹ * QuotientGroup.mk b =
          QuotientGroup.mk (a⁻¹ * b) := by
        rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rw [h_psl]
      exact ⟨a⁻¹ * b, hab, rfl⟩)

@[simp]
theorem slToPslQuot_Gamma_p_α_mk (α : GL (Fin 2) ℚ) (g : SL(2, ℤ)) :
    slToPslQuot_Gamma_p_α (N := N) α
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :=
  rfl

theorem slToPslQuot_Gamma_p_α_surjective (α : GL (Fin 2) ℚ) :
    Function.Surjective (slToPslQuot_Gamma_p_α (N := N) α) := by
  intro q'
  obtain ⟨g_psl, hg_psl⟩ := QuotientGroup.mk_surjective q'
  obtain ⟨g_sl, hg_sl⟩ := QuotientGroup.mk_surjective g_psl
  refine ⟨QuotientGroup.mk g_sl, ?_⟩
  rw [slToPslQuot_Gamma_p_α_mk, hg_sl, hg_psl]

open CongruenceSubgroup in
/-- Left-multiplication action on `SL ⧸ Γ_p(α)`. -/
noncomputable def slLeftMul_Gamma_p_α (α : GL (Fin 2) ℚ) (h : SL(2, ℤ)) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α → SL(2, ℤ) ⧸ Gamma_p_α (N := N) α :=
  Quotient.lift (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk (h * g) : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply QuotientGroup.eq.mpr
      have : (h * a)⁻¹ * (h * b) = a⁻¹ * b := by group
      rwa [this])

@[simp]
theorem slLeftMul_Gamma_p_α_mk (α : GL (Fin 2) ℚ) (h g : SL(2, ℤ)) :
    slLeftMul_Gamma_p_α (N := N) α h
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk (h * g) :=
  rfl

theorem slLeftMul_Gamma_p_α_one (α : GL (Fin 2) ℚ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    slLeftMul_Gamma_p_α (N := N) α 1 q = q := by
  induction q using QuotientGroup.induction_on with | _ g => simp

theorem slLeftMul_Gamma_p_α_comp (α : GL (Fin 2) ℚ) (h₁ h₂ : SL(2, ℤ))
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    slLeftMul_Gamma_p_α (N := N) α h₁ (slLeftMul_Gamma_p_α (N := N) α h₂ q) =
      slLeftMul_Gamma_p_α (N := N) α (h₁ * h₂) q := by
  induction q using QuotientGroup.induction_on with | _ g => simp [mul_assoc]

private lemma slToPslQuot_mk_left_transport (α : GL (Fin 2) ℚ) (a b g : SL(2, ℤ))
    (hg : slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk g) =
        slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk b)) :
    slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (a * b⁻¹ * g)) =
      slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk a) := by
  rw [slToPslQuot_Gamma_p_α_mk, slToPslQuot_Gamma_p_α_mk] at hg ⊢
  rw [QuotientGroup.eq] at hg ⊢
  have key : ((QuotientGroup.mk (a * b⁻¹ * g) : PSL(2, ℤ)))⁻¹ * QuotientGroup.mk a =
      (QuotientGroup.mk g : PSL(2, ℤ))⁻¹ * QuotientGroup.mk b := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (by group)
  rwa [key]

open CongruenceSubgroup Classical in
/-- Uniform fiber size of `slToPslQuot_Gamma_p_α`. -/
theorem slToPslQuot_Gamma_p_α_fiber_card_uniform (α : GL (Fin 2) ℚ)
    (q₁' q₂' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slToPslQuot_Gamma_p_α (N := N) α q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slToPslQuot_Gamma_p_α (N := N) α q = q₂')).card := by
  haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
  obtain ⟨q₁, hq₁⟩ := slToPslQuot_Gamma_p_α_surjective (N := N) α q₁'
  obtain ⟨q₂, hq₂⟩ := slToPslQuot_Gamma_p_α_surjective (N := N) α q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h⁻¹ q)
    (fun q hq ↦ ?_)
    (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h⁻¹
        (slLeftMul_Gamma_p_α (N := N) α h q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h
        (slLeftMul_Gamma_p_α (N := N) α h⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (h * g)) = q₂'
    rw [hh_def, ← hq₂]
    exact slToPslQuot_mk_left_transport α g₂ g₁ g (hq.trans hq₁.symm)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slToPslQuot_Gamma_p_α (N := N) α (QuotientGroup.mk (h⁻¹ * g)) = q₁'
    rw [hh_def, mul_inv_rev, inv_inv, ← hq₁]
    exact slToPslQuot_mk_left_transport α g₁ g₂ g (hq.trans hq₂.symm)

open CongruenceSubgroup Classical in
/-- Uniform fiber cardinality of `slToPslQuot_Gamma_p_α`, computed at the
identity coset. -/
noncomputable def slToPslQuot_fiberCard_Gamma_p_α (α : GL (Fin 2) ℚ) : ℕ :=
  haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
    slToPslQuot_Gamma_p_α (N := N) α q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α))).card

theorem slToPslQuot_fiberCard_Gamma_p_α_eq (α : GL (Fin 2) ℚ)
    (q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    haveI : DecidableEq (PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
      slToPslQuot_Gamma_p_α (N := N) α q = q')).card =
    slToPslQuot_fiberCard_Gamma_p_α (N := N) α := by
  rw [slToPslQuot_fiberCard_Gamma_p_α]
  exact slToPslQuot_Gamma_p_α_fiber_card_uniform (N := N) α q' _

open CongruenceSubgroup UpperHalfPlane MeasureTheory in
/-- Fiber-invariance of the SL-tile integral at `H = Γ_p(α)`. -/
theorem setIntegral_SL_tile_eq_PSL_tile_Gamma_p_α (α : GL (Fin 2) ℚ)
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ •
        (fdo : Set ℍ), h τ ∂μ_hyp := by
  have h_quot_eq :
      (QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) =
      QuotientGroup.mk ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ)) := by
    have h1 : slToPslQuot_Gamma_p_α (N := N) α q =
        QuotientGroup.mk (QuotientGroup.mk q.out : PSL(2, ℤ)) := by
      conv_lhs => rw [← q.out_eq]
      rfl
    exact h1.symm.trans (slToPslQuot_Gamma_p_α (N := N) α q).out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := h_quot_eq
  have h_eq_PSL : ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ)) =
      QuotientGroup.mk q.out * QuotientGroup.mk γ := by
    have h_mul : (QuotientGroup.mk q.out : PSL(2, ℤ)) *
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ *
          (slToPslQuot_Gamma_p_α (N := N) α q).out) =
        (slToPslQuot_Gamma_p_α (N := N) α q).out := by group
    rw [← h_mul, ← hγ_eq]
    rfl
  rw [show ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ) =
      ((QuotientGroup.mk γ : PSL(2, ℤ))⁻¹ •
        ((QuotientGroup.mk q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) by
      rw [h_eq_PSL, mul_inv_rev, mul_smul]]
  have h_psl_q : ((QuotientGroup.mk q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ) =
      (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ) := by
    rw [show ((QuotientGroup.mk q.out : PSL(2, ℤ)))⁻¹ =
          (QuotientGroup.mk q.out⁻¹ : PSL(2, ℤ)) from
        (QuotientGroup.mk_inv _ _).symm]
    rfl
  have h_psl_γ : ((QuotientGroup.mk γ : PSL(2, ℤ)))⁻¹ •
        ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) =
      (γ : SL(2, ℤ))⁻¹ • ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) := by
    rw [show ((QuotientGroup.mk γ : PSL(2, ℤ)))⁻¹ =
          (QuotientGroup.mk γ⁻¹ : PSL(2, ℤ)) from
        (QuotientGroup.mk_inv _ _).symm]
    rfl
  rw [h_psl_q, h_psl_γ]
  symm
  rw [show ((γ⁻¹ : SL(2, ℤ)) • ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) : Set ℍ) =
      (fun τ ↦ (γ⁻¹ : SL(2, ℤ)) • τ) '' ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ)) from rfl,
    (measurePreserving_smul (γ⁻¹ : SL(2, ℤ)) μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]
  congr 1
  ext τ
  exact h_inv γ⁻¹ ((Gamma_p_α (N := N) α).inv_mem hγ_mem) τ

open CongruenceSubgroup UpperHalfPlane MeasureTheory Classical in
/-- SL→PSL fiber-sum reindexing for `Γ_p(α)`-invariant integrands. -/
theorem sum_SL_tile_eq_fiberwise_PSL_tile_Gamma_p_α (α : GL (Fin 2) ℚ)
    (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp =
      ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
        (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
          slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in ((slToPslQuot_Gamma_p_α (N := N) α q).out : PSL(2, ℤ))⁻¹ •
            (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_eq_PSL_tile_Gamma_p_α (N := N) α h h_inv q
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slToPslQuot_Gamma_p_α (N := N) α q = q'),
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        (Finset.sum_fiberwise' Finset.univ
          (slToPslQuot_Gamma_p_α (N := N) α)
          (fun q' ↦ ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp)).symm
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
              ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        exact Finset.sum_const _

open UpperHalfPlane ModularGroup MeasureTheory in
/-- `fd` ↔ `fdo` SL-tile integral equality at `H = Γ_p(α)`. -/
theorem setIntegral_SL_tile_fd_eq_fdo_Gamma_p_α
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [show ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fd : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    show ((q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ) : Set ℍ) =
        (fun τ ↦ (q.out : SL(2, ℤ))⁻¹ • τ) '' (fdo : Set ℍ) from rfl,
    (measurePreserving_smul (q.out : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _),
    setIntegral_fd_eq_fdo]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Pairwise AE-disjointness of the canonical PSL coset tiles for `Γ_p(α)`. -/
theorem aedisjoint_PSL_coset_tiles_Gamma_p_α (α : GL (Fin 2) ℚ) :
    Pairwise (fun q₁ q₂ : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α =>
      MeasureTheory.AEDisjoint μ_hyp
        ((q₁.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))
        ((q₂.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ))) := by
  intro q₁ q₂ hne
  have h_inv_ne : (q₁.out : PSL(2, ℤ))⁻¹ ≠ (q₂.out : PSL(2, ℤ))⁻¹ := by
    intro hg
    apply hne
    rw [← q₁.out_eq, ← q₂.out_eq, inv_injective hg]
  exact isFundamentalDomain_fdo_PSL.aedisjoint h_inv_ne

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Null-measurability of the canonical PSL coset tiles for `Γ_p(α)`. -/
theorem nullMeasurableSet_PSL_coset_tile_Gamma_p_α
    (α : GL (Fin 2) ℚ)
    (q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α) :
    MeasureTheory.NullMeasurableSet
      ((q.out : PSL(2, ℤ))⁻¹ • (fdo : Set ℍ)) μ_hyp :=
  isFundamentalDomain_fdo_PSL.nullMeasurableSet_smul _

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL_canonical` integral as a PSL-tile sum. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp =
      ∑ q : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
        ∫ τ in ((q.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
  rw [Gamma_p_α_fundDomain_PSL_canonical,
    integral_iUnion_ae
      (nullMeasurableSet_PSL_coset_tile_Gamma_p_α (N := N) α)
      (aedisjoint_PSL_coset_tiles_Gamma_p_α (N := N) α) h_int,
    tsum_fintype]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- SL outer-q sum ↔ scaled `Gamma_p_α_fundDomain_PSL_canonical` integral. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp := by
  classical
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_fd_eq_fdo_Gamma_p_α (N := N) α h q
    _ = ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
          (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slToPslQuot_Gamma_p_α (N := N) α q = q')).card •
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp :=
        sum_SL_tile_eq_fiberwise_PSL_tile_Gamma_p_α (N := N) α h h_inv
    _ = (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
          ∑ q' : PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) α,
            ∫ τ in ((q'.out : PSL(2, ℤ)))⁻¹ • (fdo : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        congr 1
        convert slToPslQuot_fiberCard_Gamma_p_α_eq (N := N) α q' using 2
        congr
    _ = (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
          ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp := by
        rw [← setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_sum
          (N := N) α h h_int]

open CongruenceSubgroup Pointwise in
/-- `(Γ_p(α)).map SL2Z_to_PSL2R = (image_Gamma_p_α_PSL α).map PSL2Z_to_PSL2R`. -/
theorem map_SL2Z_to_PSL2R_eq_image_Gamma_p_α_PSL_R
    (α : GL (Fin 2) ℚ) :
    (Gamma_p_α (N := N) α).map SL2Z_to_PSL2R =
      (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R := by
  unfold image_Gamma_p_α_PSL
  rw [Subgroup.map_map]
  rfl

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- The canonical FD is also a FD for `(Γ_p(α)).map SL2Z_to_PSL2R`. -/
theorem isFundamentalDomain_Gamma_p_α_PSL_canonical_at_PSL_R
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp := by
  rw [map_SL2Z_to_PSL2R_eq_image_Gamma_p_α_PSL_R]
  have h_image_eq : (Equiv.refl ℍ) '' (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) =
      Gamma_p_α_fundDomain_PSL_canonical (N := N) α := by
    simp
  rw [← h_image_eq]
  refine (isFundamentalDomain_Gamma_p_α_PSL_canonical (N := N) α).image_of_equiv (Equiv.refl ℍ)
    (MeasureTheory.Measure.QuasiMeasurePreserving.id μ_hyp)
    ((Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm) ?_
  intro g τ
  show (Equiv.refl ℍ) (((Subgroup.equivMapOfInjective
        (image_Gamma_p_α_PSL (N := N) α) PSL2Z_to_PSL2R
        PSL2Z_to_PSL2R_injective).toEquiv.symm g :
        image_Gamma_p_α_PSL (N := N) α) • τ) =
      ((g : (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R) :
        PSL(2, ℝ)) • (Equiv.refl ℍ) τ
  simp only [Equiv.refl_apply]
  set g' : image_Gamma_p_α_PSL (N := N) α :=
    (Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.symm g
  have h_g_coe :
      ((g : (image_Gamma_p_α_PSL (N := N) α).map PSL2Z_to_PSL2R) : PSL(2, ℝ)) =
        PSL2Z_to_PSL2R (g' : PSL(2, ℤ)) := by
    rw [← Subgroup.coe_equivMapOfInjective_apply (f := PSL2Z_to_PSL2R)
      (hf := PSL2Z_to_PSL2R_injective)]
    congr 1
    exact ((Subgroup.equivMapOfInjective (image_Gamma_p_α_PSL (N := N) α)
      PSL2Z_to_PSL2R PSL2Z_to_PSL2R_injective).toEquiv.apply_symm_apply g).symm
  rw [h_g_coe, PSL2Z_to_PSL2R_smul_eq]
  rfl

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL` is also a FD for `(Γ_p(α)).map SL2Z_to_PSL2R`. -/
theorem isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R
    (α : GL (Fin 2) ℚ) :
    IsFundamentalDomain ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)
      (Gamma_p_α_fundDomain_PSL (N := N) α) μ_hyp := by
  have h_image := (Gamma_p_α_PSL_R_FD_finite_index_decomp_auto (N := N) α).image_of_equiv
    (Equiv.refl ℍ) (MeasureTheory.Measure.QuasiMeasurePreserving.id _)
    ((Subgroup.subgroupOfEquivOfLe (Subgroup.map_mono (Gamma_p_α_le_Gamma1 α))).symm.toEquiv)
    (fun _ _ ↦ rfl)
  simp only [Equiv.coe_refl, Set.image_id] at h_image
  exact h_image

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- `Γ_p(α)`-invariance lifts to `(Γ_p(α)).map SL2Z_to_PSL2R`-invariance. -/
theorem inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α
    (α : GL (Fin 2) ℚ) {h : ℍ → ℂ}
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (g : ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R)) (τ : ℍ) :
    h (g • τ) = h τ := by
  obtain ⟨γ, hγ_mem, hγ_eq⟩ := g.property
  have h_smul : (g : PSL(2, ℝ)) • τ = γ • τ := by
    rw [← hγ_eq, SL2Z_to_PSL2R_smul]
    rfl
  show h ((g : PSL(2, ℝ)) • τ) = h τ
  rw [h_smul]
  exact h_inv γ hγ_mem τ

open CongruenceSubgroup Pointwise in
/-- Countability of the `PSL(2, ℝ)`-side image of `Γ_p(α)`. -/
instance Gamma_p_α_PSL_R_countable
    (α : GL (Fin 2) ℚ) :
    Countable ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) := by
  classical
  let F : Gamma_p_α (N := N) α →
      ((Gamma_p_α (N := N) α).map SL2Z_to_PSL2R) :=
    fun γ ↦ ⟨SL2Z_to_PSL2R (γ : SL(2, ℤ)),
      ⟨(γ : SL(2, ℤ)), γ.property, rfl⟩⟩
  exact Function.Surjective.countable (f := F) (by
    intro g
    rcases g.property with ⟨γ, hγ, hγ_eq⟩
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact Subtype.ext hγ_eq)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- Integral equality between `Gamma_p_α_fundDomain_PSL` and the canonical FD
for `Γ_p(α)`-invariant integrands. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_eq_canonical
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, h τ ∂μ_hyp =
      ∫ τ in Gamma_p_α_fundDomain_PSL_canonical (N := N) α, h τ ∂μ_hyp :=
  (isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R (N := N) α).setIntegral_eq
    (isFundamentalDomain_Gamma_p_α_PSL_canonical_at_PSL_R (N := N) α)
    (fun g τ ↦ inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α (N := N) α h_inv g τ)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- The `Γ_p(α)` outer-SL bridge for `Gamma_p_α_fundDomain_PSL`. -/
theorem setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma_p_α (N := N) α, ∀ τ : ℍ, h (γ • τ) = h τ)
    (h_int : IntegrableOn h
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set ℍ), h τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α, h τ ∂μ_hyp := by
  rw [setIntegral_Gamma_p_α_fundDomain_PSL_eq_canonical (N := N) α h h_inv]
  exact setIntegral_Gamma_p_α_fundDomain_PSL_canonical_eq_SL_outer_q_sum
    (N := N) α h h_inv h_int

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- `Gamma_p_α_fundDomain_PSL_canonical α` has finite measure. -/
theorem hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top
    (α : GL (Fin 2) ℚ) :
    μ_hyp (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) < ⊤ := by
  rw [Gamma_p_α_fundDomain_PSL_canonical]
  refine lt_of_le_of_lt (measure_iUnion_le _) ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun q' _ ↦ ?_
  rw [(isFundamentalDomain_fdo_PSL.smul _).measure_eq isFundamentalDomain_fdo_PSL]
  exact lt_of_le_of_lt (measure_mono fdo_subset_fd) hyperbolicMeasure_fd_lt_top

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- The Petersson kernel is integrable on the canonical `Γ_p(α)` FD. -/
theorem integrableOn_petersson_Gamma_p_α_fundDomain_PSL_canonical
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn (fun τ ↦ petersson k ⇑f ⇑g τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) α) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f g
  exact IntegrableOn.of_bound
    (hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top (N := N) α)
    ((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g)).aestronglyMeasurable.restrict)
    C (ae_of_all _ fun τ ↦ hC τ)

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- α-uniform Petersson specialization of the `Γ_p(α)` outer-SL bridge. -/
theorem peterssonInner_petersson_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (ModularGroup.fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
    (slToPslQuot_fiberCard_Gamma_p_α (N := N) α) •
      ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) α,
        petersson k ⇑f ⇑g τ ∂μ_hyp :=
  setIntegral_Gamma_p_α_fundDomain_PSL_eq_SL_outer_q_sum
    (N := N) α
    (petersson k ⇑f ⇑g)
    (fun γ hγ_mem τ ↦ petersson_Gamma1_invariant f g γ ((Gamma_p_α_le_Gamma1 α) hγ_mem) τ)
    (integrableOn_petersson_Gamma_p_α_fundDomain_PSL_canonical (N := N) α f g)

open CongruenceSubgroup in
/-- The natural quotient map `SL ⧸ Γ_p(α) → SL ⧸ Γ₁(N)`, sending each
`Γ_p(α)`-coset `[g]` to its `Γ₁(N)`-coset `[g]`. -/
noncomputable def slGamma_p_αToGamma1 (α : GL (Fin 2) ℚ) :
    SL(2, ℤ) ⧸ Gamma_p_α (N := N) α →
      SL(2, ℤ) ⧸ Gamma1 N :=
  Quotient.lift
    (fun g : SL(2, ℤ) ↦ (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N))
    (by
      intro a b hab
      change (QuotientGroup.leftRel _).r _ _ at hab
      rw [QuotientGroup.leftRel_apply] at hab
      apply (QuotientGroup.eq).mpr
      exact (Gamma_p_α_le_Gamma1 α) hab)

@[simp]
theorem slGamma_p_αToGamma1_mk (α : GL (Fin 2) ℚ) (g : SL(2, ℤ)) :
    slGamma_p_αToGamma1 (N := N) α
        (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) =
      QuotientGroup.mk g := rfl

theorem slGamma_p_αToGamma1_surjective (α : GL (Fin 2) ℚ) :
    Function.Surjective (slGamma_p_αToGamma1 (N := N) α) := by
  intro q'
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective q'
  refine ⟨QuotientGroup.mk g, ?_⟩
  rw [slGamma_p_αToGamma1_mk, hg]

open CongruenceSubgroup Classical in
/-- Uniform fiber cardinality of `slGamma_p_αToGamma1`. -/
theorem slGamma_p_αToGamma1_fiber_card_uniform (α : GL (Fin 2) ℚ)
    (q₁' q₂' : SL(2, ℤ) ⧸ Gamma1 N) :
    haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slGamma_p_αToGamma1 (N := N) α q = q₁')).card =
      (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
        slGamma_p_αToGamma1 (N := N) α q = q₂')).card := by
  haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
  obtain ⟨q₁, hq₁⟩ := slGamma_p_αToGamma1_surjective (N := N) α q₁'
  obtain ⟨q₂, hq₂⟩ := slGamma_p_αToGamma1_surjective (N := N) α q₂'
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  set h := g₂ * g₁⁻¹ with hh_def
  refine Finset.card_bij'
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h q)
    (fun q _ ↦ slLeftMul_Gamma_p_α (N := N) α h⁻¹ q)
    (fun q hq ↦ ?_) (fun q hq ↦ ?_)
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h⁻¹
        (slLeftMul_Gamma_p_α (N := N) α h q) = q
      rw [slLeftMul_Gamma_p_α_comp, inv_mul_cancel, slLeftMul_Gamma_p_α_one])
    (fun q _ ↦ by
      show slLeftMul_Gamma_p_α (N := N) α h
        (slLeftMul_Gamma_p_α (N := N) α h⁻¹ q) = q
      rw [slLeftMul_Gamma_p_α_comp, mul_inv_cancel, slLeftMul_Gamma_p_α_one])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (h * g)) = q₂'
    rw [slGamma_p_αToGamma1_mk]
    have h_g₂ : (QuotientGroup.mk g₂ : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq₂
    have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq
    have h_g₁ : (QuotientGroup.mk g₁ : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq₁
    rw [← h_g₂, hh_def, QuotientGroup.eq]
    have hq_eq : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g₁ :=
      h_g.trans h_g₁.symm
    rw [QuotientGroup.eq] at hq_eq
    have : (g₂ * g₁⁻¹ * g)⁻¹ * g₂ = g⁻¹ * g₁ := by group
    rwa [this]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    induction q using QuotientGroup.induction_on with | _ g => ?_
    show slGamma_p_αToGamma1 (N := N) α (QuotientGroup.mk (h⁻¹ * g)) = q₁'
    rw [slGamma_p_αToGamma1_mk]
    have h_g₁ : (QuotientGroup.mk g₁ : SL(2, ℤ) ⧸ Gamma1 N) = q₁' := hq₁
    have h_g : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq
    have h_g₂ : (QuotientGroup.mk g₂ : SL(2, ℤ) ⧸ Gamma1 N) = q₂' := hq₂
    rw [← h_g₁, hh_def, QuotientGroup.eq]
    have hq_eq : (QuotientGroup.mk g : SL(2, ℤ) ⧸ Gamma1 N) = QuotientGroup.mk g₂ :=
      h_g.trans h_g₂.symm
    rw [QuotientGroup.eq] at hq_eq
    have : ((g₂ * g₁⁻¹)⁻¹ * g)⁻¹ * g₁ = g⁻¹ * g₂ := by group
    rwa [this]

open CongruenceSubgroup Classical in
/-- Uniform fiber cardinality of `slGamma_p_αToGamma1`, computed at the identity. -/
noncomputable def slGamma_p_αToGamma1_fiberCard (α : GL (Fin 2) ℚ) : ℕ :=
  haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
  (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
    slGamma_p_αToGamma1 (N := N) α q =
      (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma1 N))).card

theorem slGamma_p_αToGamma1_fiberCard_eq (α : GL (Fin 2) ℚ)
    (q' : SL(2, ℤ) ⧸ Gamma1 N) :
    haveI : DecidableEq (SL(2, ℤ) ⧸ Gamma1 N) := Classical.decEq _
    (Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
      slGamma_p_αToGamma1 (N := N) α q = q')).card =
    slGamma_p_αToGamma1_fiberCard (N := N) α := by
  rw [slGamma_p_αToGamma1_fiberCard]
  exact slGamma_p_αToGamma1_fiber_card_uniform (N := N) α q' _

open CongruenceSubgroup UpperHalfPlane MeasureTheory in
/-- Fiber-invariance of the SL-tile integral at `H = Γ₁(N)`, `Γ_p(α)`-quotient. -/
theorem setIntegral_SL_tile_Gamma_p_α_eq_SL_tile_Gamma1
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α) :
    ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
      ∫ τ in ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ •
        (fd : Set ℍ), h τ ∂μ_hyp := by
  have h_quot_eq : (QuotientGroup.mk q.out : SL(2, ℤ) ⧸ Gamma1 N) =
      QuotientGroup.mk ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ)) := by
    have h1 : slGamma_p_αToGamma1 (N := N) α q = QuotientGroup.mk q.out := by
      conv_lhs => rw [← q.out_eq]
      rfl
    exact h1.symm.trans (slGamma_p_αToGamma1 (N := N) α q).out_eq.symm
  rw [QuotientGroup.eq] at h_quot_eq
  set γ := (q.out : SL(2, ℤ))⁻¹ * (slGamma_p_αToGamma1 (N := N) α q).out with hγ_def
  have h_eq : ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ)) = q.out * γ := by
    rw [hγ_def]
    group
  rw [show ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ • (fd : Set ℍ) =
      ((γ : SL(2, ℤ))⁻¹ • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ))) by
    rw [h_eq, mul_inv_rev, mul_smul]]
  symm
  rw [show ((γ⁻¹ : SL(2, ℤ)) • ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) : Set ℍ) =
      (fun τ ↦ (γ⁻¹ : SL(2, ℤ)) • τ) '' ((q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ)) from rfl,
    (measurePreserving_smul (γ⁻¹ : SL(2, ℤ)) μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]
  congr 1
  ext τ
  exact h_inv γ⁻¹ ((Gamma1 N).inv_mem h_quot_eq) τ

open CongruenceSubgroup UpperHalfPlane MeasureTheory Classical in
/-- SL/Γ_p(α) → SL/Γ₁(N) fiber-sum reindex. -/
theorem sum_SL_tile_Gamma_p_α_eq_fiberCard_mul_SL_tile_Gamma1
    (α : GL (Fin 2) ℚ) (h : ℍ → ℂ)
    (h_inv : ∀ γ ∈ Gamma1 N, ∀ τ : ℍ, h (γ • τ) = h τ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp =
    (slGamma_p_αToGamma1_fiberCard (N := N) α) •
      ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
        ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp := by
  calc ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp
      = ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
          ∫ τ in ((slGamma_p_αToGamma1 (N := N) α q).out : SL(2, ℤ))⁻¹ •
            (fd : Set ℍ), h τ ∂μ_hyp :=
        Finset.sum_congr rfl fun q _ ↦ setIntegral_SL_tile_Gamma_p_α_eq_SL_tile_Gamma1 (N := N) α h h_inv q
    _ = ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
          ∑ q ∈ Finset.univ.filter (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α =>
            slGamma_p_αToGamma1 (N := N) α q = q'),
            ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp :=
        (Finset.sum_fiberwise' Finset.univ
          (slGamma_p_αToGamma1 (N := N) α)
          (fun q' ↦ ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp)).symm
    _ = (slGamma_p_αToGamma1_fiberCard (N := N) α) •
          ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
            ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ), h τ ∂μ_hyp := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun q' _ ↦ ?_
        rw [Finset.sum_const]
        congr 1
        convert slGamma_p_αToGamma1_fiberCard_eq (N := N) α q' using 2
        congr

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Petersson kernel: `Γ_p(α)` outer-SL sum equals `relIndex • petN`. -/
theorem sum_SL_Gamma_p_α_setIntegral_fd_petersson_eq_relIndex_mul_petN
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
    (slGamma_p_αToGamma1_fiberCard (N := N) α) • petN f g := by
  rw [sum_SL_tile_Gamma_p_α_eq_fiberCard_mul_SL_tile_Gamma1 (N := N) α
      (petersson k ⇑f ⇑g)
      (fun γ hγ τ ↦ petersson_Gamma1_invariant f g γ hγ τ)]
  congr 1
  show ∑ q' : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q'.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
        petersson k ⇑f ⇑g τ ∂μ_hyp = petN f g
  unfold petN
  refine Finset.sum_congr rfl fun q' _ ↦ ?_
  exact (petN_summand_eq_setIntegral f g q').symm

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Generic SL-element Petersson-fd-slash setIntegral identity. -/
theorem peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd
    (F G : ℍ → ℂ) (s : SL(2, ℤ)) :
    peterssonInner k fd (F ∣[k] (s : SL(2, ℤ))⁻¹) (G ∣[k] (s : SL(2, ℤ))⁻¹) =
    ∫ τ in (s : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
      petersson k F G τ ∂μ_hyp := by
  simp only [peterssonInner]
  simp_rw [petersson_slash_SL]
  rw [← Set.image_smul,
    ← (measurePreserving_smul (s : SL(2, ℤ))⁻¹ μ_hyp).setIntegral_image_emb
      (measurableEmbedding_const_smul _)]

open CongruenceSubgroup UpperHalfPlane ModularGroup MeasureTheory in
/-- Petersson kernel: `Γ_p(α)` outer-SL `petN`-summand sum equals `relIndex • petN`. -/
theorem sum_SL_Gamma_p_α_petN_summand_eq_relIndex_mul_petN
    (α : GL (Fin 2) ℚ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
      peterssonInner k (ModularGroup.fd : Set ℍ)
        (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    (slGamma_p_αToGamma1_fiberCard (N := N) α) • petN f g := by
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        peterssonInner k (ModularGroup.fd : Set ℍ)
          (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
          (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹)) =
      ∑ q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) α,
        ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set ℍ),
          petersson k ⇑f ⇑g τ ∂μ_hyp from
    Finset.sum_congr rfl fun q _ ↦ peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd ⇑f ⇑g q.out]
  exact sum_SL_Gamma_p_α_setIntegral_fd_petersson_eq_relIndex_mul_petN α f g

end HeckeRing.GL2
