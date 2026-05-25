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

open scoped MatrixGroups DirectSum

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

/-- **Function-indexed joint-eigenspace decomposition of an invariant
submodule.**  For a commuting family `f : ι → Module.End K V` of semisimple
endomorphisms whose eigenspaces span `V`, any invariant submodule `p` is the
supremum over functions `χ : ι → K` of its intersections with the joint
eigenspaces `⨅ i, (f i).eigenspace (χ i)`.

This is the abstract backbone shared by the diamond-invariant character
decompositions for both modular and cusp forms: the joint eigenspace pulls
back through `p.subtype` (`Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`),
and the restricted family still spans `⊤` on `p`
(`Module.End.genEigenspace_restrict_eq_top` plus the joint spanning theorem
`Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute`). -/
private lemma iSup_inf_iInf_eigenspace_eq_self_of_invariant {ι : Type*}
    [FiniteDimensional K V] (f : ι → Module.End K V)
    (hcomm : Pairwise fun i j ↦ Commute (f i) (f j))
    (hss : ∀ i, (f i).IsSemisimple)
    (htop : ∀ i, ⨆ μ : K, (f i).eigenspace μ = ⊤)
    (p : Submodule K V) (hp : ∀ i, ∀ x ∈ p, f i x ∈ p) :
    (⨆ χ : ι → K, p ⊓ ⨅ i, (f i).eigenspace (χ i)) = p := by
  have hmax : ∀ (i : ι) (μ : K),
      (f i).maxGenEigenspace μ = (f i).eigenspace μ :=
    fun i μ => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (hss i).isFinitelySemisimple μ
  -- Rewrite each joint eigenspace as a joint maximal-generalised eigenspace,
  -- then pull it back through the inclusion `p.subtype`.
  simp_rw [← hmax]
  have h_per_χ : ∀ χ : ι → K,
      p ⊓ (⨅ i, (f i).maxGenEigenspace (χ i)) =
        (⨅ i, Module.End.maxGenEigenspace ((f i).restrict (hp i)) (χ i)).map p.subtype :=
    fun χ => Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo
      (f := f) (μ := χ) p (fun i => hp i)
  simp_rw [h_per_χ, ← Submodule.map_iSup]
  -- The restricted family still spans `⊤` on `p`, so the image is all of `p`.
  suffices h_restrict_top :
      (⨆ χ : ι → K, ⨅ i,
        Module.End.maxGenEigenspace ((f i).restrict (hp i)) (χ i)) = ⊤ by
    rw [h_restrict_top, Submodule.map_top, Submodule.range_subtype]
  apply Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
  · -- Restrictions of commuting endomorphisms commute.
    intro i j hij
    refine LinearMap.ext fun ⟨x, hx⟩ => Subtype.ext ?_
    simp only [Module.End.mul_apply, LinearMap.restrict_coe_apply]
    exact LinearMap.congr_fun (hcomm hij).eq x
  · -- Each restricted endomorphism has `⨆ μ, maxGenEigenspace μ = ⊤` on `p`.
    intro i
    refine Module.End.genEigenspace_restrict_eq_top (hp i) ?_
    show ⨆ μ : K, (f i).maxGenEigenspace μ = ⊤
    simp_rw [hmax]; exact htop i

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

/-- Finite-dimensionality of the space of modular forms for `Γ₀(N)`. A direct
downstream consequence of `dim_gen_cong_levels`: `Γ₀(N)` is a finite-index
subgroup of `SL₂(ℤ)`, so the port immediately yields this instance. -/
instance modularForm_Gamma0_finiteDimensional :
    FiniteDimensional ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) := by
  have hidx : (Gamma0 N).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have := dim_gen_cong_levels k (Gamma0 N) hidx
  show FiniteDimensional ℂ (ModularForm ((Gamma0 N : Subgroup (GL (Fin 2) ℝ))) k)
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

/-- **The character decomposition as a linear equivalence.**  Packages
`ModularForm_Gamma1_charSpace_directSum` as an explicit `≃ₗ[ℂ]` between
the direct sum `⨁ χ, modFormCharSpace k χ` and `ModularForm (Γ₁(N)) k`.

This is the consumer-facing form of the direct sum decomposition: every
modular form at `Γ₁(N)` corresponds canonically to a `DirectSum`-supported
family of Nebentypus components, and vice versa. -/
noncomputable def ModularForm_Gamma1_charSpace_linearEquiv
    (k : ℤ) [DecidableEq ((ZMod N)ˣ →* ℂˣ)] :
    (⨁ χ : (ZMod N)ˣ →* ℂˣ, modFormCharSpace k χ) ≃ₗ[ℂ]
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _)
    (ModularForm_Gamma1_charSpace_directSum k)

/-- Each character subspace `modFormCharSpace k χ` is finite-dimensional over
`ℂ`, as a submodule of the finite-dimensional ambient
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
instance modFormCharSpace_finiteDimensional
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    FiniteDimensional ℂ (modFormCharSpace k χ) := inferInstance

/-- The character group `(ZMod N)ˣ →* ℂˣ` is finite. Derived by transport
across `MulChar.equivToUnitHom` from `MulChar.finite`, which requires
`[Finite (ZMod N)ˣ]` (automatic) and `[IsDomain ℂ]` (automatic). -/
instance finite_charHom : Finite ((ZMod N)ˣ →* ℂˣ) :=
  .of_equiv (MulChar (ZMod N) ℂ) MulChar.equivToUnitHom

/-- `Fintype` version of `finite_charHom`, obtained classically. Needed to
state sums over the character group at the statement level (`∑ χ : …`). -/
noncomputable instance fintype_charHom : Fintype ((ZMod N)ˣ →* ℂˣ) :=
  Fintype.ofFinite _

/-- **Dimension formula**: `dim_ℂ M_k(Γ₁(N)) = ∑_χ dim_ℂ M_k(Γ₁(N), χ)`.
A direct consequence of the character decomposition `LinearEquiv` combined
with `Module.finrank_directSum`. -/
theorem ModularForm_Gamma1_finrank_eq_sum_charSpace (k : ℤ) :
    Module.finrank ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    ∑ χ : (ZMod N)ˣ →* ℂˣ, Module.finrank ℂ (modFormCharSpace k χ) := by
  classical
  rw [← LinearEquiv.finrank_eq (ModularForm_Gamma1_charSpace_linearEquiv k)]
  simp [Module.finrank_directSum]

/-! ### CuspForm character decomposition

The cusp-form analogue of the decomposition above: the character spaces
`cuspFormCharSpace k χ` span, are independent, and form an internal
direct sum decomposition of `CuspForm (Γ₁(N)) k`.

This is the reverse/consumer building block needed by `Newforms.mainLemma`
and the newspace API: any cusp form splits uniquely as a sum of
Nebentypus pieces.

The proof mirrors the `ModularForm` proofs above, using `diamondOpCuspHom`
in place of `diamondOpHom` and a local cusp-form finite-dimensionality
instance derived via the natural injection `CuspForm → ModularForm`. -/

/-- The natural `ℂ`-linear injection `CuspForm Γ k →ₗ[ℂ] ModularForm Γ k`,
defined locally to avoid depending on `AdjointTheory.lean`.  A cusp form is
a modular form because being zero at cusps implies being bounded. -/
private noncomputable def cuspFormToModularFormLin_local :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm := f.toSlashInvariantForm
      holo' := f.holo'
      bdd_at_cusps' := fun {c} hc g hg =>
        (f.zero_at_cusps' hc g hg).boundedAtFilter }
  map_add' f g := by ext z; rfl
  map_smul' c f := by ext z; rfl

private lemma cuspFormToModularFormLin_local_injective :
    Function.Injective
      (cuspFormToModularFormLin_local (N := N) (k := k)) := by
  intro f g hfg
  ext z
  exact congr_arg (fun h : ModularForm _ _ => h.toFun z) hfg

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
      Commute (diamondOpCuspHom k d₁) (diamondOpCuspHom k d₂) := by
  intro d₁ d₂ _
  show diamondOpCuspHom k d₁ * diamondOpCuspHom k d₂ =
    diamondOpCuspHom k d₂ * diamondOpCuspHom k d₁
  rw [← map_mul, ← map_mul, mul_comm]

/-- For each cusp-form diamond operator, the supremum of its eigenspaces is
the whole space. -/
lemma diamondOpCusp_iSup_eigenspace_eq_top (d : (ZMod N)ˣ) :
    ⨆ μ : ℂ, (diamondOpCuspHom k d).eigenspace μ =
    (⊤ : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have h_top := Module.End.iSup_maxGenEigenspace_eq_top (diamondOpCuspHom k d)
  have heq : ∀ μ : ℂ, (diamondOpCuspHom k d).maxGenEigenspace μ =
      (diamondOpCuspHom k d).eigenspace μ :=
    fun μ => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
      (diamondOpCusp_isSemisimple d).isFinitelySemisimple μ
  simp_rw [heq] at h_top
  exact h_top

/-- The joint cusp-form eigenspace indexed by an arbitrary function
`χ : (ZMod N)ˣ → ℂ`.  For characters this coincides with
`cuspFormCharSpace`; for non-characters it is `⊥`. -/
noncomputable def jointDiamondCuspEigenspace (k : ℤ) (χ : (ZMod N)ˣ → ℂ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ d : (ZMod N)ˣ, (diamondOpCuspHom k d).eigenspace (χ d)

lemma mem_jointDiamondCuspEigenspace_iff (χ : (ZMod N)ˣ → ℂ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ jointDiamondCuspEigenspace k χ ↔
    ∀ d : (ZMod N)ˣ, diamondOpCuspHom k d f = χ d • f := by
  simp only [jointDiamondCuspEigenspace, Submodule.mem_iInf,
    Module.End.mem_eigenspace_iff]

lemma jointDiamondCuspEigenspace_eq_cuspFormCharSpace (χ₀ : (ZMod N)ˣ →* ℂˣ) :
    jointDiamondCuspEigenspace k (fun d => (χ₀ d : ℂ)) =
      cuspFormCharSpace k χ₀ := rfl

lemma exists_charHom_of_jointDiamondCuspEigenspace_ne_bot {χ : (ZMod N)ˣ → ℂ}
    (hχ : jointDiamondCuspEigenspace k χ ≠ ⊥) :
    ∃ χ₀ : (ZMod N)ˣ →* ℂˣ, (fun d => ((χ₀ d) : ℂ)) = χ := by
  rw [Submodule.ne_bot_iff] at hχ
  obtain ⟨f, hf_mem, hf_ne⟩ := hχ
  have hmem : ∀ d : (ZMod N)ˣ, f ∈ (diamondOpCuspHom k d).eigenspace (χ d) := by
    intro d
    exact (Submodule.mem_iInf (p := fun d : (ZMod N)ˣ =>
      (diamondOpCuspHom k d).eigenspace (χ d))).mp hf_mem d
  exact ⟨charDecomp_charHomOfEigenvector
    (V := CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (diamondOpCuspHom k) χ f hf_ne hmem, rfl⟩

/-- **The cusp-form character subspaces `cuspFormCharSpace k χ` span
`CuspForm (Γ₁(N)) k`.**  The reverse/consumer analogue of
`ModularForm_Gamma1_iSup_charSpace` for cusp forms. -/
theorem CuspForm_Gamma1_iSup_charSpace (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormCharSpace k χ) =
    (⊤ : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  -- Step 1: the bigger sum (over all functions) equals the top.
  have h_top_fun :
      (⨆ χ : (ZMod N)ˣ → ℂ, jointDiamondCuspEigenspace k χ) =
      (⊤ : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
    have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (diamondOpCuspHom (N := N) k) diamondOpCuspHom_pairwise_commute
      (fun d => by
        have heq : ∀ μ : ℂ, (diamondOpCuspHom k d).maxGenEigenspace μ =
            (diamondOpCuspHom k d).eigenspace μ :=
          fun μ => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
            (diamondOpCusp_isSemisimple d).isFinitelySemisimple μ
        simp_rw [heq]
        exact diamondOpCusp_iSup_eigenspace_eq_top d)
    have heq : ∀ (χ : (ZMod N)ˣ → ℂ) d,
        (diamondOpCuspHom k d).maxGenEigenspace (χ d) =
        (diamondOpCuspHom k d).eigenspace (χ d) :=
      fun _ d => Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
        (diamondOpCusp_isSemisimple d).isFinitelySemisimple _
    simp_rw [heq] at h
    exact h
  -- Step 2: the supremum over functions equals the supremum over characters.
  apply le_antisymm le_top
  rw [← h_top_fun]
  refine iSup_le (fun χ => ?_)
  by_cases hχ : jointDiamondCuspEigenspace k χ = ⊥
  · rw [hχ]; exact bot_le
  · obtain ⟨χ₀, hχ₀⟩ := exists_charHom_of_jointDiamondCuspEigenspace_ne_bot hχ
    rw [← hχ₀]
    exact le_iSup (fun χ₀ : (ZMod N)ˣ →* ℂˣ => cuspFormCharSpace k χ₀) χ₀

/-- **The cusp-form character subspaces form an independent family.** -/
theorem CuspForm_Gamma1_iSupIndep_charSpace (k : ℤ) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormCharSpace k χ) := by
  -- Independence for the bigger family (over all functions χ : (ZMod N)ˣ → ℂ)
  -- follows from mathlib: commuting operators' joint max-gen-eigenspaces are
  -- independent; semisimplicity identifies them with eigenspaces.
  have h_indep_fun :
      iSupIndep (fun χ : (ZMod N)ˣ → ℂ => jointDiamondCuspEigenspace k χ) := by
    have h_mapsTo :
        ∀ (i j : (ZMod N)ˣ) (φ : ℂ),
          Set.MapsTo (diamondOpCuspHom (N := N) k i)
            ((diamondOpCuspHom k j).maxGenEigenspace φ : Set _)
            ((diamondOpCuspHom k j).maxGenEigenspace φ : Set _) := by
      intro i j φ
      refine Module.End.mapsTo_maxGenEigenspace_of_comm ?_ φ
      rcases eq_or_ne i j with rfl | hij
      · exact Commute.refl _
      · exact diamondOpCuspHom_pairwise_commute hij.symm
    have h_indep :=
      Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
        (f := diamondOpCuspHom (N := N) k) h_mapsTo
    have heq : ∀ (χ : (ZMod N)ˣ → ℂ),
        (⨅ d, (diamondOpCuspHom (N := N) k d).maxGenEigenspace (χ d)) =
        jointDiamondCuspEigenspace k χ := by
      intro χ
      unfold jointDiamondCuspEigenspace
      refine iInf_congr (fun d => ?_)
      exact Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
        (diamondOpCusp_isSemisimple d).isFinitelySemisimple _
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

/-- **Internal direct sum decomposition for cusp forms**: `CuspForm (Γ₁(N)) k`
decomposes as the direct sum of the Nebentypus character spaces
`cuspFormCharSpace k χ`.  This is the consumer-facing theorem for
`Newforms.mainLemma` and the newspace API: every cusp form at `Γ₁(N)`
splits uniquely as a finite sum of Nebentypus pieces. -/
theorem CuspForm_Gamma1_charSpace_directSum (k : ℤ)
    [DecidableEq ((ZMod N)ˣ →* ℂˣ)] :
    DirectSum.IsInternal (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormCharSpace k χ) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (CuspForm_Gamma1_iSupIndep_charSpace k)
    (CuspForm_Gamma1_iSup_charSpace k)

/-- **The cusp-form character decomposition as a linear equivalence.**  The
cusp-form analogue of `ModularForm_Gamma1_charSpace_linearEquiv`: packages
`CuspForm_Gamma1_charSpace_directSum` as a `≃ₗ[ℂ]`. -/
noncomputable def CuspForm_Gamma1_charSpace_linearEquiv
    (k : ℤ) [DecidableEq ((ZMod N)ˣ →* ℂˣ)] :
    (⨁ χ : (ZMod N)ˣ →* ℂˣ, cuspFormCharSpace k χ) ≃ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  LinearEquiv.ofBijective (DirectSum.coeLinearMap _)
    (CuspForm_Gamma1_charSpace_directSum k)

/-- Each cusp-form character subspace `cuspFormCharSpace k χ` is
finite-dimensional over `ℂ`, as a submodule of the finite-dimensional
`CuspForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
instance cuspFormCharSpace_finiteDimensional
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    FiniteDimensional ℂ (cuspFormCharSpace k χ) := inferInstance

/-- **Dimension formula (cusp forms)**:
`dim_ℂ S_k(Γ₁(N)) = ∑_χ dim_ℂ S_k(Γ₁(N), χ)`. -/
theorem CuspForm_Gamma1_finrank_eq_sum_charSpace (k : ℤ) :
    Module.finrank ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
    ∑ χ : (ZMod N)ˣ →* ℂˣ, Module.finrank ℂ (cuspFormCharSpace k χ) := by
  classical
  rw [← LinearEquiv.finrank_eq (CuspForm_Gamma1_charSpace_linearEquiv k)]
  simp [Module.finrank_directSum]

/-! ### Character decomposition of diamond-invariant submodules (T129)

Any submodule of `ModularForm (Γ₁(N)) k` or `CuspForm (Γ₁(N)) k` that is
stable under every diamond operator `⟨d⟩` inherits the Nebentypus
character decomposition: it equals the supremum of its intersections with
the character subspaces, and this family is `iSup`-independent.

These theorems are the reusable backbone for the composite `mainLemma`
story.  Applied to `cuspFormsOld N k` (diamond-invariant via
`diamondOp_preserves_cuspFormsOld`, landed in `Newforms.lean`), they
reduce the general-`N` `mainLemma` statement to its per-character-space
form: it suffices to show, for each Nebentypus character `χ`, that a
`f ∈ cuspFormCharSpace k χ` satisfying the coprime-coefficient vanishing
hypothesis is in `cuspFormsOld N k`.  The prime-power case is already
delivered by `AtkinLehner.mainLemma_charSpace_primePower`; the composite
case is reduced to a prime-supported decomposition by
`AtkinLehner.mainLemma_charSpace_of_primeFactors_decomposition` (T125).

**Proof.**  For a `⟨d⟩`-invariant submodule `p`, the restricted diamond
operators on `p` pairwise commute and each has `⨆ μ, maxGenEigenspace μ =
⊤` in `p` (restriction of finite-order/semisimple operators preserves
these properties; the key mathlib ingredient is
`Module.End.genEigenspace_restrict_eq_top`).  Applying mathlib's joint
max-gen eigenspace spanning theorem to the restricted family yields
`⊤`-decomposition in `p`, which pulls back through the inclusion
`p.subtype` via `Submodule.inf_iInf_maxGenEigenspace_of_forall_mapsTo`
plus `Submodule.map_iSup` / `Submodule.range_subtype`.  The final
reduction from index type `(ZMod N)ˣ → ℂ` to multiplicative characters
`(ZMod N)ˣ →* ℂˣ` follows the standard pattern:
`exists_charHom_of_jointDiamondEigenspace_ne_bot` (resp. the cusp-form
variant) extracts a character from any nonzero joint eigenspace. -/

section InvariantSubmoduleCharDecomp

/-- **Character decomposition of a diamond-invariant submodule of
`ModularForm (Γ₁(N)) k`.**  If `p ⊆ M_k(Γ₁(N))` is stable under every
diamond operator `⟨d⟩` for `d ∈ (ZMod N)ˣ`, then `p` equals the supremum
of its intersections with the Nebentypus character subspaces
`modFormCharSpace k χ`.

Specialising `p = ⊤` recovers `ModularForm_Gamma1_iSup_charSpace`.  The
intended consumer is applied to oldform / newform subspaces (which are
diamond-invariant) to reduce the `N`-level `mainLemma` to its per-character
form. -/
theorem modFormCharSpace_iSup_inf_of_diamondOpHom_invariant
    (k : ℤ) (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ modFormCharSpace k χ) = p := by
  -- Step 1: decomposition of `p` indexed by functions `(ZMod N)ˣ → ℂ`, from
  -- the abstract joint-eigenspace decomposition of an invariant submodule.
  have h_fun_top :
      (⨆ χ : (ZMod N)ˣ → ℂ, p ⊓ jointDiamondEigenspace k χ) = p := by
    simp only [jointDiamondEigenspace]
    exact iSup_inf_iInf_eigenspace_eq_self_of_invariant (diamondOpHom k)
      diamondOpHom_pairwise_commute diamondOp_isSemisimple
      diamondOp_iSup_eigenspace_eq_top p hp
  -- Step 2: restrict from `(ZMod N)ˣ → ℂ` to multiplicative characters.
  apply le_antisymm (iSup_le (fun _ => inf_le_left))
  conv_lhs => rw [← h_fun_top]
  refine iSup_le (fun χ => ?_)
  by_cases hχ : p ⊓ jointDiamondEigenspace k χ = ⊥
  · rw [hχ]; exact bot_le
  · -- A non-bottom joint eigenspace forces `χ` to come from a character.
    have hchar_ne_bot : jointDiamondEigenspace k χ ≠ ⊥ := by
      intro h_bot
      exact hχ (by rw [h_bot, inf_bot_eq])
    obtain ⟨χ₀, hχ₀⟩ := exists_charHom_of_jointDiamondEigenspace_ne_bot hchar_ne_bot
    calc p ⊓ jointDiamondEigenspace k χ
        = p ⊓ jointDiamondEigenspace k (fun d => (χ₀ d : ℂ)) := by rw [hχ₀]
      _ = p ⊓ modFormCharSpace k χ₀ := by
            rw [jointDiamondEigenspace_eq_modFormCharSpace]
      _ ≤ ⨆ ψ : (ZMod N)ˣ →* ℂˣ, p ⊓ modFormCharSpace k ψ :=
          le_iSup (fun ψ : (ZMod N)ˣ →* ℂˣ => p ⊓ modFormCharSpace k ψ) χ₀

/-- **`iSupIndep` for the character decomposition of a diamond-invariant
submodule of `ModularForm (Γ₁(N)) k`.**  The family of intersections
`(p ⊓ modFormCharSpace k χ)_χ` is `iSup`-independent for any submodule
`p` (the diamond-invariance hypothesis is not needed for independence —
it is inherited from the ambient independence
`ModularForm_Gamma1_iSupIndep_charSpace`). -/
theorem modFormCharSpace_iSupIndep_inf
    (k : ℤ) (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ => p ⊓ modFormCharSpace k χ) :=
  (ModularForm_Gamma1_iSupIndep_charSpace (N := N) k).mono (fun _ => inf_le_right)

/-- **Character decomposition of a diamond-invariant submodule of
`CuspForm (Γ₁(N)) k`.**  The cusp-form analogue of
`modFormCharSpace_iSup_inf_of_diamondOpHom_invariant`.

Applied to `cuspFormsOld N k` (diamond-invariant by
`diamondOp_preserves_cuspFormsOld`) or `cuspFormsNew N k` (by
`diamondOp_preserves_cuspFormsNew`) this gives the character-wise
decomposition of the oldform / newform subspaces — the structural input
to the composite-`N` `mainLemma` via T125
(`mainLemma_charSpace_of_primeFactors_decomposition`). -/
theorem cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, p ⊓ cuspFormCharSpace k χ) = p := by
  -- Mirror the ModularForm proof with the cusp-form operators, via the
  -- abstract joint-eigenspace decomposition of an invariant submodule.
  have h_fun_top :
      (⨆ χ : (ZMod N)ˣ → ℂ, p ⊓ jointDiamondCuspEigenspace k χ) = p := by
    simp only [jointDiamondCuspEigenspace]
    exact iSup_inf_iInf_eigenspace_eq_self_of_invariant (diamondOpCuspHom k)
      diamondOpCuspHom_pairwise_commute diamondOpCusp_isSemisimple
      diamondOpCusp_iSup_eigenspace_eq_top p hp
  apply le_antisymm (iSup_le (fun _ => inf_le_left))
  conv_lhs => rw [← h_fun_top]
  refine iSup_le (fun χ => ?_)
  by_cases hχ : p ⊓ jointDiamondCuspEigenspace k χ = ⊥
  · rw [hχ]; exact bot_le
  · have hchar_ne_bot : jointDiamondCuspEigenspace k χ ≠ ⊥ := by
      intro h_bot
      exact hχ (by rw [h_bot, inf_bot_eq])
    obtain ⟨χ₀, hχ₀⟩ :=
      exists_charHom_of_jointDiamondCuspEigenspace_ne_bot hchar_ne_bot
    calc p ⊓ jointDiamondCuspEigenspace k χ
        = p ⊓ jointDiamondCuspEigenspace k (fun d => (χ₀ d : ℂ)) := by rw [hχ₀]
      _ = p ⊓ cuspFormCharSpace k χ₀ := by
            rw [jointDiamondCuspEigenspace_eq_cuspFormCharSpace]
      _ ≤ ⨆ ψ : (ZMod N)ˣ →* ℂˣ, p ⊓ cuspFormCharSpace k ψ :=
          le_iSup (fun ψ : (ZMod N)ˣ →* ℂˣ => p ⊓ cuspFormCharSpace k ψ) χ₀

/-- **`iSupIndep` for the character decomposition of a diamond-invariant
submodule of `CuspForm (Γ₁(N)) k`.**  As in the ModularForm case, the
family `(p ⊓ cuspFormCharSpace k χ)_χ` is `iSup`-independent from the
ambient independence; diamond-invariance is not required. -/
theorem cuspFormCharSpace_iSupIndep_inf
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) :
    iSupIndep (fun χ : (ZMod N)ˣ →* ℂˣ => p ⊓ cuspFormCharSpace k χ) :=
  (CuspForm_Gamma1_iSupIndep_charSpace (N := N) k).mono (fun _ => inf_le_right)

/-- **Finsupp-indexed character decomposition of a modular form in a
diamond-invariant submodule.**  Consumer-facing corollary of
`modFormCharSpace_iSup_inf_of_diamondOpHom_invariant`: any element of a
diamond-invariant submodule `p ⊆ M_k(Γ₁(N))` is a finitely-supported sum
of Nebentypus-character components, each landing simultaneously in `p`
and in its character subspace. -/
theorem exists_finsupp_charSpace_of_diamondOpHom_invariant
    (k : ℤ) (p : Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpHom k d f ∈ p)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ modFormCharSpace k χ) ∧
      (g.sum fun _ y => y) = f := by
  have h_iSup := modFormCharSpace_iSup_inf_of_diamondOpHom_invariant k p hp
  rw [← h_iSup] at hf
  exact (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hf

/-- **Finsupp-indexed character decomposition of a cusp form in a
diamond-invariant submodule.**  Cusp-form analogue of
`exists_finsupp_charSpace_of_diamondOpHom_invariant`.

The intended downstream consumer is the composite-`N` `mainLemma`:
applied with `p := cuspFormsOld N k` (diamond-invariant by
`diamondOp_preserves_cuspFormsOld`, landed in `Newforms.lean`), this
produces a finite χ-wise decomposition of any oldform with each piece
simultaneously an oldform AND a χ-Nebentypus form, ready to feed into
`AtkinLehner.mainLemma_charSpace_of_primeFactors_decomposition` (T125)
or the prime-power character-space mainLemma
`AtkinLehner.mainLemma_charSpace_primePower` (T118). -/
theorem exists_finsupp_charSpace_of_diamondOpCuspHom_invariant
    (k : ℤ) (p : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    (hp : ∀ d : (ZMod N)ˣ, ∀ f ∈ p, diamondOpCuspHom k d f ∈ p)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ p) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ p ⊓ cuspFormCharSpace k χ) ∧
      (g.sum fun _ y => y) = f := by
  have h_iSup := cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant k p hp
  rw [← h_iSup] at hf
  exact (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hf

end InvariantSubmoduleCharDecomp

end

end HeckeRing.GL2
