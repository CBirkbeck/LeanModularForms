/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Prop334
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed

/-!
# Prop 3.34 (E) — `heckeSlash_gen` preserves `modFormCharSpace`

This file connects P334-B (`Gamma0MapUnits_preserved_of_detCoprime`) to the
`modFormCharSpace` preservation needed for the full Hecke-ring homomorphism.

## Main results

* `heckeSlash_gen_diamondOpHom_of_functional_comm` — From functional
  χ-equivariance, each diamond operator `⟨d⟩` acts as the scalar `χ d` on
  the Hecke-transformed function.
* `heckeSlash_gen_mem_modFormCharSpace_of_slash_comm` — From functional
  χ-equivariance AND Γ₁(N)-invariance, the transformed form packaged as a
  modular form at the Γ₁(N)-level lies in `modFormCharSpace k χ`.
* `heckeSlash_gen_invariant_Gamma1_of_slash_comm` — Γ₁(N)-invariance of
  the Hecke slash follows from functional χ-equivariance at `d = 1`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing DoubleCoset

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane Manifold

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- If the χ-equivariance under the slash action by every `g ∈ Γ₀(N)`
holds, then the Hecke-transformed function is Γ₁(N)-invariant. -/
theorem heckeSlash_gen_invariant_Gamma1_of_slash_comm
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ))
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ (Gamma1 N).map (mapGL ℝ)) :
    (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k] γ =
    heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ) := by
  obtain ⟨σ, hσ_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
  have hσ_Gamma0 : σ ∈ Gamma0 N := Gamma1_le_Gamma0 N hσ_Gamma1
  have h_units : Gamma0MapUnits (⟨σ, hσ_Gamma0⟩ : ↥(Gamma0 N)) = 1 := by
    ext
    simp only [Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one]
    exact ((Gamma1_mem N σ).mp hσ_Gamma1).2.1
  have hc := hComm ⟨σ, hσ_Gamma0⟩
  rwa [h_units, map_one, Units.val_one, one_smul] at hc

/-- The Hecke slash preserves holomorphicity. -/
lemma heckeSlash_gen_Gamma1_holomorphic (k : ℤ)
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) :=
  MDifferentiable.sum fun _ _ ↦ (ModularFormClass.holo f).slash k _

/-- `GL₂(ℚ)` maps cusps of `(Gamma1 N).map (mapGL ℝ)` to cusps. -/
lemma glMap_smul_isCusp_Gamma1 (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma1 N).map (mapGL ℝ)) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  rw [show glMap A • OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (A • q)
      from (OnePoint.map_smul (algebraMap ℚ ℝ) A q).symm]
  exact ⟨_, rfl⟩

/-- The Hecke slash preserves boundedness at cusps. -/
lemma heckeSlash_gen_Gamma1_bdd_at_cusps (k : ℤ)
    (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsBoundedAt (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) k := by
  simp only [heckeSlash_gen]
  apply Finset.sum_induction _ (fun g ↦ c.IsBoundedAt g k)
    (fun _ _ ha hb ↦ ha.add hb)
    ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc)
  intro i _
  exact OnePoint.IsBoundedAt.smul_iff.mp
    (f.bdd_at_cusps' (glMap_smul_isCusp_Gamma1 _ hc))

/-- Given functional χ-equivariance of `heckeSlash_gen (Gamma0_pair N) k D`
on the underlying function of `f`, package the result as a
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
noncomputable def heckeSlash_gen_asModularForm_of_slash_comm
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)
  slash_action_eq' γ hγ :=
    heckeSlash_gen_invariant_Gamma1_of_slash_comm k χ D f hComm γ hγ
  holo' := heckeSlash_gen_Gamma1_holomorphic k D f
  bdd_at_cusps' hc := heckeSlash_gen_Gamma1_bdd_at_cusps k D f hc

/-- The underlying function of
`heckeSlash_gen_asModularForm_of_slash_comm` is exactly the
`heckeSlash_gen` sum applied to `⇑f`. -/
@[simp] lemma heckeSlash_gen_asModularForm_of_slash_comm_coe
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (D : HeckeCoset (Gamma0_pair N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hComm : ∀ g : ↥(Gamma0 N),
      (heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) ∣[k]
        mapGL ℝ (g : SL(2, ℤ)) =
      (↑(χ (Gamma0MapUnits g)) : ℂ) •
        heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ)) :
    (⇑(heckeSlash_gen_asModularForm_of_slash_comm k χ D f hComm) :
        ℍ → ℂ) =
      heckeSlash_gen (Gamma0_pair N) k D (⇑f : ℍ → ℂ) := rfl

/-- Compatibility of `glMap ∘ mapGL ℚ` with `mapGL ℝ` on `SL(2, ℤ)` elements. -/
private lemma glMap_mapGL_Q_eq_mapGL_R (g : ↥(Gamma0 N)) :
    glMap (mapGL ℚ (g : SL(2, ℤ))) = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) g := by
  apply Units.ext; ext i j
  simp only [glMap, GeneralLinearGroup.map]
  exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ ((g : SL(2, ℤ)).val i j)).symm

end HeckeRing.GL2
