/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.Modularforms.DimensionFormulas
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.NumberTheory.MulChar.Duality

/-!
# Character decomposition of `ModularForm (Γ₁(N)) k`

For each character `χ : (ZMod N)ˣ →* ℂˣ`, the Nebentypus character space

  `modFormCharSpace k χ = ⨅ d : (ZMod N)ˣ, eigenspace (diamondOpHom k d) (χ d)`

is already defined in `Gamma1Pair.lean`. This file proves the internal direct
sum decomposition

  `ModularForm (Γ₁(N)) k = ⨁_{χ : (ZMod N)ˣ →* ℂˣ} modFormCharSpace k χ`.

## Main results

* `ModularForm_Gamma1_iSup_charSpace`: `⨆ χ, modFormCharSpace k χ = ⊤`.
* `ModularForm_Gamma1_iSupIndep_charSpace`: the family is supremum-independent.
* `ModularForm_Gamma1_charSpace_directSum`: the `DirectSum.IsInternal` statement.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial

open scoped MatrixGroups DirectSum

namespace HeckeRing.GL2

noncomputable section

section Abstract

variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalue at the
identity is `1`. -/
lemma charDecomp_char_one_of_jointEigenvector
    (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) :
    χ 1 = 1 := by
  have h1 := hv_mem 1
  rw [Module.End.mem_eigenspace_iff, map_one, Module.End.one_apply] at h1
  by_contra hne
  have heq : (χ 1 - 1) • v = 0 := by
    rw [sub_smul, one_smul, sub_eq_zero]; exact h1.symm
  exact (smul_eq_zero.mp heq).elim (fun hc ↦ hne (sub_eq_zero.mp hc)) hv

/-- If `v ≠ 0` is a joint eigenvector of a monoid-hom representation
`ρ : G →* Module.End K V` with eigenvalues `χ g`, then the eigenvalues are
multiplicative: `χ (g₁ * g₂) = χ g₁ * χ g₂`. -/
lemma charDecomp_char_mul_of_jointEigenvector
    (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g))
    (g₁ g₂ : G) :
    χ (g₁ * g₂) = χ g₁ * χ g₂ := by
  have h := hv_mem (g₁ * g₂)
  rw [Module.End.mem_eigenspace_iff, map_mul] at h
  have h₁ := (Module.End.mem_eigenspace_iff).mp (hv_mem g₁)
  have h₂ := (Module.End.mem_eigenspace_iff).mp (hv_mem g₂)
  have hcomp : (ρ g₁ * ρ g₂) v = (χ g₁ * χ g₂) • v := by
    change ρ g₁ (ρ g₂ v) = (χ g₁ * χ g₂) • v
    rw [h₂, map_smul, h₁, smul_smul, mul_comm]
  rw [hcomp] at h
  by_contra hne
  have heq : (χ (g₁ * g₂) - χ g₁ * χ g₂) • v = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp heq).elim (fun hc ↦ hne (sub_eq_zero.mp hc)) hv

/-- If `g` has finite order and `v ≠ 0` is a joint eigenvector with eigenvalues
`χ`, then `χ g ≠ 0`: the eigenvalue of a finite-order element is a root of
unity (hence a unit). -/
lemma charDecomp_char_ne_zero_of_jointEigenvector
    (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g))
    {g : G} (hg : IsOfFinOrder g) :
    χ g ≠ 0 := by
  obtain ⟨n, hnpos, hn⟩ := hg.exists_pow_eq_one
  have hχ_mul := charDecomp_char_mul_of_jointEigenvector ρ χ v hv hv_mem
  have hχ_one := charDecomp_char_one_of_jointEigenvector ρ χ v hv hv_mem
  have hχ_pow : ∀ m : ℕ, χ (g ^ m) = (χ g) ^ m := fun m ↦ by
    induction m with
    | zero => simp [hχ_one]
    | succ k ih => rw [pow_succ, hχ_mul, ih, pow_succ]
  intro hzero
  have hgn_zero : χ (g ^ n) = 0 := by rw [hχ_pow, hzero, zero_pow hnpos.ne']
  rw [hn, hχ_one] at hgn_zero
  exact one_ne_zero hgn_zero

/-- Given a joint eigenvector `v ≠ 0` for a monoid-hom representation
`ρ : G →* Module.End K V` of a *finite* group `G`, the eigenvalue function
`χ : G → K` factors through a unique monoid homomorphism `G →* Kˣ`. -/
noncomputable def charDecomp_charHomOfEigenvector [Finite G]
    (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) :
    G →* Kˣ where
  toFun g := Units.mk0 (χ g)
    (charDecomp_char_ne_zero_of_jointEigenvector ρ χ v hv hv_mem (isOfFinOrder_of_finite g))
  map_one' := Units.ext (charDecomp_char_one_of_jointEigenvector ρ χ v hv hv_mem)
  map_mul' g₁ g₂ :=
    Units.ext (charDecomp_char_mul_of_jointEigenvector ρ χ v hv hv_mem g₁ g₂)

@[simp]
lemma charDecomp_charHomOfEigenvector_val [Finite G]
    (ρ : G →* Module.End K V) (χ : G → K)
    (v : V) (hv : v ≠ 0) (hv_mem : ∀ g, v ∈ (ρ g).eigenspace (χ g)) (g : G) :
    ((charDecomp_charHomOfEigenvector ρ χ v hv hv_mem g) : K) = χ g := rfl

/-- For a finite-order endomorphism, separability of `X^n - 1` over a
characteristic-zero field implies semisimplicity. -/
lemma charDecomp_isSemisimple_of_isOfFinOrder [CharZero K]
    {f : Module.End K V} (hf : IsOfFinOrder f) :
    f.IsSemisimple := by
  obtain ⟨n, hnpos, hn⟩ := hf.exists_pow_eq_one
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hnpos.ne'
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := (X : K[X]) ^ n - 1)
    (Polynomial.X_pow_sub_one_separable_iff.mpr hnK).squarefree
  simp [map_sub, aeval_X_pow, hn]

private lemma iSup_inf_iInf_eigenspace_eq_self_of_invariant {ι : Type*}
    [FiniteDimensional K V] (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hss : ∀ i, (f i).IsSemisimple)
    (htop : ∀ i, ⨆ μ : K, (f i).eigenspace μ = ⊤)
    (p : Submodule K V) (hp : ∀ i, ∀ x ∈ p, f i x ∈ p) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p := by
  have hmax : ∀ (i : ι) (μ : K), (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    fun i μ ↦ Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (hss i).isFinitelySemisimple μ
  simp_rw [← hmax,
    fun χ : ι → K ↦ Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo
      (f := f) (μ := χ) p (fun i ↦ hp i),
    ← Submodule.map_iSup]
  suffices h_restrict_top :
      (⨆ χ : ι → K, ⨅ i,
        Module.End.maxGenEigenspace ((f i).restrict (hp i)) (χ i)) = ⊤ by
    rw [h_restrict_top, Submodule.map_top, Submodule.range_subtype]
  apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
  · intro i j hij
    refine LinearMap.ext fun ⟨x, _⟩ ↦ Subtype.ext ?_
    simpa only [Module.End.mul_apply, LinearMap.restrict_coe_apply] using
      LinearMap.congr_fun (hcomm hij).eq x
  · refine fun i ↦ Module.End.genEigenspace_restrict_eq_top (hp i) ?_
    simpa only [hmax] using htop i

end Abstract

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- Each diamond operator has finite order (it is the image of a finite-order
group element under `diamondOpHom`). -/
lemma diamondOpHom_isOfFinOrder (d : (ZMod N)ˣ) :
    IsOfFinOrder (diamondOpHom k d) :=
  (diamondOpHom k).isOfFinOrder (isOfFinOrder_of_finite d)

/-- Finite-dimensionality of the space of modular forms for `Γ₁(N)`. Derived
from `dim_gen_cong_levels` in `DimensionFormulas.lean`. -/
instance modularForm_Gamma1_finiteDimensional :
    FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  dim_gen_cong_levels k (Gamma1 N) Subgroup.FiniteIndex.index_ne_zero

/-- Finite-dimensionality of the space of modular forms for `Γ₀(N)`, derived
from `dim_gen_cong_levels`. -/
instance modularForm_Gamma0_finiteDimensional :
    FiniteDimensional ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  dim_gen_cong_levels k (Gamma0 N) Subgroup.FiniteIndex.index_ne_zero

/-- Each character subspace `modFormCharSpace k χ` is finite-dimensional over
`ℂ`, as a submodule of the finite-dimensional ambient
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
instance modFormCharSpace_finiteDimensional
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    FiniteDimensional ℂ (modFormCharSpace k χ) := inferInstance

/-- The character group `(ZMod N)ˣ →* ℂˣ` is finite. -/
instance finite_charHom : Finite ((ZMod N)ˣ →* ℂˣ) :=
  .of_equiv (MulChar (ZMod N) ℂ) MulChar.equivToUnitHom

/-- `Fintype` version of `finite_charHom`, needed to state sums over the
character group at the statement level (`∑ χ : …`). -/
noncomputable instance fintype_charHom : Fintype ((ZMod N)ˣ →* ℂˣ) :=
  Fintype.ofFinite _

private noncomputable def cuspFormToModularFormLin_local :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm := f.toSlashInvariantForm
      holo' := f.holo'
      bdd_at_cusps' := fun {c} hc g hg ↦
        (f.zero_at_cusps' hc g hg).boundedAtFilter }
  map_add' f g := by ext z; rfl
  map_smul' c f := by ext z; rfl

omit [NeZero N] in
private lemma cuspFormToModularFormLin_local_injective :
    Function.Injective (cuspFormToModularFormLin_local (N := N) (k := k)) := fun _ _ hfg ↦ by
  ext z; exact congr_arg (fun h : ModularForm _ _ ↦ h.toFun z) hfg

/-- Finite-dimensionality of `CuspForm Γ₁(N) k`, derived via the natural
injection into `ModularForm Γ₁(N) k`. -/
instance cuspForm_Gamma1_finiteDimensional :
    FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  FiniteDimensional.of_injective
    (cuspFormToModularFormLin_local (N := N) (k := k))
    cuspFormToModularFormLin_local_injective

/-- Each cusp-form diamond operator has finite order. -/
lemma diamondOpCuspHom_isOfFinOrder (d : (ZMod N)ˣ) :
    IsOfFinOrder (diamondOpCuspHom k d) :=
  (diamondOpCuspHom k).isOfFinOrder (isOfFinOrder_of_finite d)

/-- Each cusp-form diamond operator is semisimple. -/
lemma diamondOpCusp_isSemisimple (d : (ZMod N)ˣ) :
    (diamondOpCuspHom k d).IsSemisimple :=
  charDecomp_isSemisimple_of_isOfFinOrder (diamondOpCuspHom_isOfFinOrder d)

/-- The cusp-form diamond operators pairwise commute. -/
lemma diamondOpCuspHom_pairwise_commute :
    Pairwise fun d₁ d₂ : (ZMod N)ˣ ↦
      Commute (diamondOpCuspHom k d₁) (diamondOpCuspHom k d₂) :=
  fun _ _ _ ↦ (Commute.all _ _).map (diamondOpCuspHom k)

/-- For each cusp-form diamond operator, the supremum of its eigenspaces is
the whole space. -/
lemma diamondOpCusp_iSup_eigenspace_eq_top (d : (ZMod N)ˣ) :
    ⨆ μ : ℂ, (diamondOpCuspHom k d).eigenspace μ =
    (⊤ : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  simpa only [Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (diamondOpCusp_isSemisimple d).isFinitelySemisimple] using
    Module.End.iSup_maxGenEigenspace_eq_top (diamondOpCuspHom k d)

/-- The joint cusp-form eigenspace indexed by an arbitrary function
`χ : (ZMod N)ˣ → ℂ`.  For characters this coincides with
`cuspFormCharSpace`; for non-characters it is `⊥`. -/
noncomputable def jointDiamondCuspEigenspace (k : ℤ) (χ : (ZMod N)ˣ → ℂ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, (diamondOpCuspHom k d).eigenspace (χ d)

/-- `jointDiamondCuspEigenspace` at the underlying function of a character
agrees with `cuspFormCharSpace`. -/
lemma jointDiamondCuspEigenspace_eq_cuspFormCharSpace (χ₀ : (ZMod N)ˣ →* ℂˣ) :
    jointDiamondCuspEigenspace k (fun d ↦ (χ₀ d : ℂ)) =
      cuspFormCharSpace k χ₀ := rfl

/-- If `jointDiamondCuspEigenspace k χ ≠ ⊥`, then `χ` comes from a character. -/
lemma exists_charHom_of_jointDiamondCuspEigenspace_ne_bot {χ : (ZMod N)ˣ → ℂ}
    (hχ : jointDiamondCuspEigenspace k χ ≠ ⊥) :
    ∃ χ₀ : (ZMod N)ˣ →* ℂˣ, (fun d ↦ ((χ₀ d) : ℂ)) = χ := by
  rw [Submodule.ne_bot_iff] at hχ
  obtain ⟨f, hf_mem, hf_ne⟩ := hχ
  exact ⟨charDecomp_charHomOfEigenvector
    (V := CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (diamondOpCuspHom k) χ f hf_ne fun d ↦ Submodule.mem_iInf _ |>.mp hf_mem d, rfl⟩

/-- **The cusp-form character subspaces form an independent family.** -/
theorem CuspForm_Gamma1_iSupIndep_charSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ ↦ cuspFormCharSpace k χ) := by
  have heq : ∀ d (μ : ℂ), (diamondOpCuspHom (N := N) k d).maxGenEigenspace μ =
      (diamondOpCuspHom k d).eigenspace μ :=
    fun d μ ↦ Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (diamondOpCusp_isSemisimple d).isFinitelySemisimple μ
  have h_indep_fun :
      iSupIndep (fun χ : (ZMod N)ˣ → ℂ ↦ jointDiamondCuspEigenspace k χ) := by
    have h_mapsTo : ∀ (i j : (ZMod N)ˣ) (φ : ℂ),
        Set.MapsTo (diamondOpCuspHom (N := N) k i)
          ((diamondOpCuspHom k j).maxGenEigenspace φ : Set _)
          ((diamondOpCuspHom k j).maxGenEigenspace φ : Set _) := fun i j φ ↦
      Module.End.mapsTo_maxGenEigenspace_of_comm
        (by rcases eq_or_ne i j with rfl | hij
            · exact Commute.refl _
            · exact diamondOpCuspHom_pairwise_commute hij.symm) φ
    simpa [jointDiamondCuspEigenspace, heq] using
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
        (f := diamondOpCuspHom (N := N) k) h_mapsTo
  refine h_indep_fun.comp fun χ₁ χ₂ h ↦ ?_
  ext d
  exact_mod_cast congr_fun h d

/-- Each cusp-form character subspace `cuspFormCharSpace k χ` is
finite-dimensional over `ℂ`, as a submodule of the finite-dimensional
`CuspForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
instance cuspFormCharSpace_finiteDimensional
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    FiniteDimensional ℂ (cuspFormCharSpace k χ) := inferInstance

section InvariantSubmoduleCharDecomp

/-- **Character decomposition of a diamond-invariant submodule of
`CuspForm (Γ₁(N)) k`.**  The cusp-form analogue of
`modFormCharSpace_iSup_inf_of_diamondOpHom_invariant`. -/
theorem cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ cuspFormCharSpace k χ) = p := by
  have h_fun_top :
      (⨆ χ : (ZMod N)ˣ → ℂ, p ⊓ jointDiamondCuspEigenspace k χ) = p := by
    simp only [jointDiamondCuspEigenspace]
    exact iSup_inf_iInf_eigenspace_eq_self_of_invariant (diamondOpCuspHom k)
      diamondOpCuspHom_pairwise_commute diamondOpCusp_isSemisimple
      diamondOpCusp_iSup_eigenspace_eq_top p hp
  refine le_antisymm (iSup_le fun _ ↦ inf_le_left) ?_
  conv_lhs => rw [← h_fun_top]
  refine iSup_le fun χ ↦ ?_
  by_cases hχ : p ⊓ jointDiamondCuspEigenspace k χ = ⊥
  · simp [hχ]
  · obtain ⟨χ₀, hχ₀⟩ := exists_charHom_of_jointDiamondCuspEigenspace_ne_bot
      (fun h_bot ↦ hχ (by rw [h_bot, inf_bot_eq]))
    rw [← hχ₀, jointDiamondCuspEigenspace_eq_cuspFormCharSpace]
    exact le_iSup (fun ψ : (ZMod N)ˣ →* ℂˣ ↦ p ⊓ cuspFormCharSpace k ψ) χ₀

/-- **Finsupp-indexed character decomposition of a cusp form in a
diamond-invariant submodule.**  Cusp-form analogue of
`exists_finsupp_charSpace_of_diamondOpHom_invariant`. -/
theorem exists_finsupp_charSpace_of_diamondOpCuspHom_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ cuspFormCharSpace k χ) ∧
      (g.sum fun _ y ↦ y) = f :=
  (Submodule.mem_iSup_iff_exists_finsupp _ _).mp <|
    (cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant k p hp).symm ▸ hf

end InvariantSubmoduleCharDecomp

end

end HeckeRing.GL2
