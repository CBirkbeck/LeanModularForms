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

/-!
# Character decomposition of `ModularForm (Γ₁(N)) k`

For each character `χ : (ZMod N)ˣ →* ℂˣ`, the Nebentypus character space

  `modFormCharSpace k χ = ⨅ d : (ZMod N)ˣ, eigenspace (diamondOpHom k d) (χ d)`

is already defined in `Gamma1Pair.lean`. This file proves the internal direct
sum decomposition

  `ModularForm (Γ₁(N)) k = ⨁_{χ : (ZMod N)ˣ →* ℂˣ} modFormCharSpace k χ`.

## Mathematical strategy

The argument uses semisimplicity of the diamond representation of the finite
abelian group `(ZMod N)ˣ`:

1. Each `diamondOpHom k d` has finite order (since `d` does), so
   `(diamondOp k d)^n = 1` with `n = |(ZMod N)ˣ|`. The polynomial `X^n - 1` is
   separable over `ℂ`, hence squarefree, hence each diamond operator is
   semisimple.
2. Diamond operators pairwise commute (image of an abelian group).
3. Over `ℂ` (algebraically closed, char 0), `FiniteDimensional ℂ (ModularForm …)`
   (from `dim_gen_cong_levels`) plus mathlib's
   `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`
   gives `⨆ χ : G → ℂ, ⨅ d, maxGenEigenspace (diamondOp k d) (χ d) = ⊤`.
4. Semisimplicity upgrades `maxGenEigenspace` to `eigenspace`.
5. For non-multiplicative `χ : G → ℂ`, the joint eigenspace vanishes, so the
   supremum restricts to characters `χ : (ZMod N)ˣ →* ℂˣ`.
6. Independence of joint eigenspaces of a commuting family comes from
   mathlib's `Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo`;
   restriction along the injection `(ZMod N)ˣ →* ℂˣ ↪ ((ZMod N)ˣ → ℂ)`
   (`χ₀ ↦ (d ↦ (χ₀ d : ℂ))`) preserves independence.

## Main results

* `ModularForm_Gamma1_iSup_charSpace`: `⨆ χ, modFormCharSpace k χ = ⊤`.
* `ModularForm_Gamma1_iSupIndep_charSpace`: the family is supremum-independent.
* `ModularForm_Gamma1_charSpace_directSum`: the `DirectSum.IsInternal` statement.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup Polynomial

open scoped MatrixGroups

namespace HeckeRing.GL2

noncomputable section

/-! ### General lemmas: finite-order representations on a vector space -/

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
  rcases smul_eq_zero.mp heq with hc | hv'
  · exact hne (sub_eq_zero.mp hc)
  · exact hv hv'

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
  have h₁ := hv_mem g₁; rw [Module.End.mem_eigenspace_iff] at h₁
  have h₂ := hv_mem g₂; rw [Module.End.mem_eigenspace_iff] at h₂
  have hcomp : (ρ g₁ * ρ g₂) v = (χ g₁ * χ g₂) • v := by
    show ρ g₁ (ρ g₂ v) = (χ g₁ * χ g₂) • v
    rw [h₂, map_smul, h₁, smul_smul, mul_comm]
  rw [hcomp] at h
  by_contra hne
  have heq : (χ (g₁ * g₂) - χ g₁ * χ g₂) • v = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp heq with hc | hv'
  · exact hne (sub_eq_zero.mp hc)
  · exact hv hv'

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
  have hχ_pow : ∀ (m : ℕ), χ (g ^ m) = (χ g) ^ m := by
    intro m
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

end Abstract

/-! ### Diamond operators are semisimple, commute, and span the whole space -/

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- Each diamond operator has finite order (it is the image of a finite-order
group element under `diamondOpHom`). -/
lemma diamondOpHom_isOfFinOrder (d : (ZMod N)ˣ) :
    IsOfFinOrder (diamondOpHom k d) :=
  (diamondOpHom k).isOfFinOrder (isOfFinOrder_of_finite d)

/-- Each diamond operator is a semisimple endomorphism. -/
lemma diamondOp_isSemisimple (d : (ZMod N)ˣ) :
    (diamondOpHom k d).IsSemisimple :=
  charDecomp_isSemisimple_of_isOfFinOrder (diamondOpHom_isOfFinOrder d)

/-- The diamond operators pairwise commute. They are all images under the
monoid homomorphism `diamondOpHom` from the abelian group `(ZMod N)ˣ`, so their
images commute. -/
lemma diamondOpHom_pairwise_commute :
    Pairwise fun d₁ d₂ : (ZMod N)ˣ ↦ Commute (diamondOpHom k d₁) (diamondOpHom k d₂) := by
  intro d₁ d₂ _
  show diamondOpHom k d₁ * diamondOpHom k d₂ = diamondOpHom k d₂ * diamondOpHom k d₁
  rw [← map_mul, ← map_mul, mul_comm]

/-- Finite-dimensionality of the space of modular forms for `Γ₁(N)`. Derived
from `dim_gen_cong_levels` in `DimensionFormulas.lean`. -/
instance modularForm_Gamma1_finiteDimensional :
    FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have hidx : (Gamma1 N).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have := dim_gen_cong_levels k (Gamma1 N) hidx
  show FiniteDimensional ℂ (ModularForm ((Gamma1 N : Subgroup (GL (Fin 2) ℝ))) k)
  exact this

/-- For each diamond operator, the supremum of its eigenspaces is the whole
space. Combining semisimplicity (`diamondOp_isSemisimple`) with algebraic
closedness of `ℂ` and finite-dimensionality, the maximal generalized
eigenspaces exhaust the space; semisimplicity then identifies them with the
ordinary eigenspaces. -/
lemma diamondOp_iSup_eigenspace_eq_top (d : (ZMod N)ˣ) :
    ⨆ μ : ℂ, (diamondOpHom k d).eigenspace μ =
    (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have h_top := Module.End.iSup_maxGenEigenspace_eq_top (diamondOpHom k d)
  have heq : ∀ μ : ℂ, (diamondOpHom k d).maxGenEigenspace μ =
      (diamondOpHom k d).eigenspace μ :=
    fun μ => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (diamondOp_isSemisimple d).isFinitelySemisimple μ
  simp_rw [heq] at h_top
  exact h_top

/-! ### From functions `χ : (ZMod N)ˣ → ℂ` to characters `(ZMod N)ˣ →* ℂˣ` -/

/-- The joint eigenspace indexed by a function `χ : (ZMod N)ˣ → ℂ`. When `χ` is
not the underlying function of a character `(ZMod N)ˣ →* ℂˣ`, this space is
`⊥`; otherwise it coincides with `modFormCharSpace k χ₀` for that character. -/
noncomputable def jointDiamondEigenspace (k : ℤ) (χ : (ZMod N)ˣ → ℂ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, (diamondOpHom k d).eigenspace (χ d)

lemma mem_jointDiamondEigenspace_iff (χ : (ZMod N)ˣ → ℂ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ jointDiamondEigenspace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpHom k d f = χ d • f := by
  simp only [jointDiamondEigenspace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

/-- `jointDiamondEigenspace` at the underlying function of a character agrees
with `modFormCharSpace`. -/
lemma jointDiamondEigenspace_eq_modFormCharSpace (χ₀ : (ZMod N)ˣ →* ℂˣ) :
    jointDiamondEigenspace k (fun d => (χ₀ d : ℂ)) = modFormCharSpace k χ₀ := rfl

/-- If `jointDiamondEigenspace k χ ≠ ⊥`, then `χ` comes from a character, i.e.,
equals `(d ↦ (χ₀ d : ℂ))` for some `χ₀ : (ZMod N)ˣ →* ℂˣ`. -/
lemma exists_charHom_of_jointDiamondEigenspace_ne_bot {χ : (ZMod N)ˣ → ℂ}
    (hχ : jointDiamondEigenspace k χ ≠ ⊥) :
    ∃ χ₀ : (ZMod N)ˣ →* ℂˣ, (fun d => ((χ₀ d) : ℂ)) = χ := by
  rw [Submodule.ne_bot_iff] at hχ
  obtain ⟨f, hf_mem, hf_ne⟩ := hχ
  have hmem : ∀ d : (ZMod N)ˣ, f ∈ (diamondOpHom k d).eigenspace (χ d) := by
    intro d
    exact (Submodule.mem_iInf (p := fun d : (ZMod N)ˣ =>
      (diamondOpHom k d).eigenspace (χ d))).mp hf_mem d
  exact ⟨charDecomp_charHomOfEigenvector
    (V := ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (diamondOpHom k) χ f hf_ne hmem, rfl⟩

/-! ### The decomposition theorems -/

/-- **The character subspaces `modFormCharSpace k χ` span the whole space**:
modular forms for `Γ₁(N)` decompose into the span of Nebentypus character
spaces, one for each character `(ZMod N)ˣ →* ℂˣ`. -/
theorem ModularForm_Gamma1_iSup_charSpace (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ) =
    (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  -- Step 1: the bigger sum (over all functions) equals the top.
  have h_top_fun :
      (⨆ χ : (ZMod N)ˣ → ℂ, jointDiamondEigenspace k χ) =
      (⊤ : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
    have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (diamondOpHom (N := N) k) diamondOpHom_pairwise_commute
      (fun d => by
        have heq : ∀ μ : ℂ, (diamondOpHom k d).maxGenEigenspace μ =
            (diamondOpHom k d).eigenspace μ :=
          fun μ => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
            (diamondOp_isSemisimple d).isFinitelySemisimple μ
        simp_rw [heq]
        exact diamondOp_iSup_eigenspace_eq_top d)
    have heq : ∀ (χ : (ZMod N)ˣ → ℂ) d, (diamondOpHom k d).maxGenEigenspace (χ d) =
        (diamondOpHom k d).eigenspace (χ d) :=
      fun _ d => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
        (diamondOp_isSemisimple d).isFinitelySemisimple _
    simp_rw [heq] at h
    exact h
  -- Step 2: the supremum over functions equals the supremum over characters.
  apply le_antisymm le_top
  rw [← h_top_fun]
  refine iSup_le (fun χ => ?_)
  by_cases hχ : jointDiamondEigenspace k χ = ⊥
  · rw [hχ]; exact bot_le
  · obtain ⟨χ₀, hχ₀⟩ := exists_charHom_of_jointDiamondEigenspace_ne_bot hχ
    rw [← hχ₀]
    exact le_iSup (fun χ₀ : (ZMod N)ˣ →* ℂˣ => modFormCharSpace k χ₀) χ₀

/-- **The character subspaces form an independent family**. Distinct
characters differ at some `d`, giving distinct eigenvalues of the corresponding
diamond operator; the eigenspaces of that operator at distinct eigenvalues are
disjoint. -/
theorem ModularForm_Gamma1_iSupIndep_charSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ => modFormCharSpace k χ) := by
  -- Independence for the bigger family (over all functions χ : (ZMod N)ˣ → ℂ)
  -- follows from mathlib: commuting operators' joint max-gen-eigenspaces are
  -- independent. Semisimplicity identifies max-gen-eigenspaces with eigenspaces.
  have h_indep_fun :
      iSupIndep (fun χ : (ZMod N)ˣ → ℂ => jointDiamondEigenspace k χ) := by
    have h_mapsTo :
        ∀ (i j : (ZMod N)ˣ) (φ : ℂ), Set.MapsTo (diamondOpHom (N := N) k i)
          ((diamondOpHom k j).maxGenEigenspace φ : Set _)
          ((diamondOpHom k j).maxGenEigenspace φ : Set _) := by
      intro i j φ
      refine Module.End.mapsTo_maxGenEigenspace_of_comm ?_ φ
      rcases eq_or_ne i j with rfl | hij
      · exact Commute.refl _
      · exact diamondOpHom_pairwise_commute hij.symm
    have h_indep :=
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
        (f := diamondOpHom (N := N) k) h_mapsTo
    -- Translate max-gen-eigenspaces to eigenspaces via semisimplicity.
    have heq : ∀ (χ : (ZMod N)ˣ → ℂ),
        (⨅ d, (diamondOpHom (N := N) k d).maxGenEigenspace (χ d)) =
        jointDiamondEigenspace k χ := by
      intro χ
      unfold jointDiamondEigenspace
      refine iInf_congr (fun d => ?_)
      exact Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
        (diamondOp_isSemisimple d).isFinitelySemisimple _
    simp_rw [heq] at h_indep
    exact h_indep
  -- Restrict to characters via the injection
  -- `(ZMod N)ˣ →* ℂˣ ↪ ((ZMod N)ˣ → ℂ)` given by `χ₀ ↦ (d ↦ (χ₀ d : ℂ))`.
  have hφ_inj : Function.Injective
      (fun (χ₀ : (ZMod N)ˣ →* ℂˣ) => fun d => ((χ₀ d) : ℂ)) := by
    intro χ₁ χ₂ h
    ext d
    have hd : ((χ₁ d) : ℂ) = ((χ₂ d) : ℂ) := congr_fun h d
    exact_mod_cast hd
  exact h_indep_fun.comp hφ_inj

/-- **Internal direct sum decomposition**: `ModularForm (Γ₁(N)) k` decomposes
as the direct sum of the Nebentypus character spaces `modFormCharSpace k χ`. -/
theorem ModularForm_Gamma1_charSpace_directSum (k : ℤ)
    [DecidableEq ((ZMod N)ˣ →* ℂˣ)] :
    DirectSum.IsInternal (fun χ : (ZMod N)ˣ →* ℂˣ => modFormCharSpace k χ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (ModularForm_Gamma1_iSupIndep_charSpace k)
    (ModularForm_Gamma1_iSup_charSpace k)

end

end HeckeRing.GL2
