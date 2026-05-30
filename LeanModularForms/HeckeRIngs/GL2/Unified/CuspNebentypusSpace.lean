/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusSpace
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson

/-!
# Experimental cusp-space `Γ₀(N), χ` model

This file mirrors the modular-form experimental unification layer on cusp-form
character spaces. It packages the existing restricted cusp Hecke operators into
the `GoodHeckeFamily` interface and transports them onto a `Γ₀(N), χ`-style
space whose carrier is expressed via the twisted-slash/Nebentypus predicate.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The ambient cusp-form Hecke operator attached to a good index. -/
noncomputable def ambientCuspHeckeOfGoodIndex (k : ℤ) (n : GoodIndex N) :
    Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  refine
    { toFun := heckeT_n_cusp (N := N) k (n : ℕ)
      map_add' := ?_
      map_smul' := ?_ }
  · intro f g
    ext z
    change (heckeT_n k (n : ℕ) (f + g).toModularForm').toFun z =
      ((heckeT_n k (n : ℕ) f.toModularForm').toFun z +
        (heckeT_n k (n : ℕ) g.toModularForm').toFun z)
    rw [show (f + g).toModularForm' = f.toModularForm' + g.toModularForm' from rfl, map_add]
    rfl
  · intro c f
    ext z
    change (heckeT_n k (n : ℕ) (c • f).toModularForm').toFun z =
      c • (heckeT_n k (n : ℕ) f.toModularForm').toFun z
    rw [show (c • f).toModularForm' = c • f.toModularForm' from rfl, map_smul]
    rfl

/-- The ambient good-index cusp operators commute by reducing to the ambient
modular multiplication-table proof source. -/
theorem ambientCuspHeckeOfGoodIndex_commute_from_mulFormula (k : ℤ) (m n : GoodIndex N) :
    Commute (ambientCuspHeckeOfGoodIndex (N := N) k m)
      (ambientCuspHeckeOfGoodIndex (N := N) k n) :=
  LinearMap.ext fun f ↦ CuspForm.ext fun z ↦
    congrArg (fun mf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ mf z)
      (ambientHeckeOfGoodIndex_commute_apply_from_mulFormula (N := N) k m n f.toModularForm')

/-- Pointwise form of `ambientCuspHeckeOfGoodIndex_commute_from_mulFormula`. -/
theorem ambientCuspHeckeOfGoodIndex_commute_apply_from_mulFormula (k : ℤ) (m n : GoodIndex N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ambientCuspHeckeOfGoodIndex (N := N) k m
        (ambientCuspHeckeOfGoodIndex (N := N) k n f) =
      ambientCuspHeckeOfGoodIndex (N := N) k n
        (ambientCuspHeckeOfGoodIndex (N := N) k m f) :=
  LinearMap.congr_fun (ambientCuspHeckeOfGoodIndex_commute_from_mulFormula (N := N) k m n).eq f

/-- The restricted cusp `Γ₁(N), χ` operator attached to a good index. -/
noncomputable def cuspCharHeckeOfGoodIndex
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N) :
    Module.End ℂ (cuspFormCharSpace k χ) := by
  letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  exact heckeT_n_cusp_charRestrict k (n : ℕ) n.property.2 χ

/-- The restricted cusp `Γ₁(N), χ` good-index operators commute by restricting
the ambient multiplication-table proof source. -/
theorem heckeT_n_cusp_charRestrict_commute_from_mulFormula (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) :
    Commute (cuspCharHeckeOfGoodIndex (N := N) k χ m)
      (cuspCharHeckeOfGoodIndex (N := N) k χ n) :=
  LinearMap.ext fun f ↦ Subtype.ext <|
    ambientCuspHeckeOfGoodIndex_commute_apply_from_mulFormula
      (N := N) k m n (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- The existing restricted cusp Hecke operators, packaged as a good Hecke
family on `cuspFormCharSpace k χ`. -/
noncomputable def cuspFormCharSpaceFamily
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    GoodHeckeFamily N (cuspFormCharSpace k χ) where
  op := cuspCharHeckeOfGoodIndex (N := N) k χ
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply CuspForm.ext
    intro z
    change (heckeT_n k 1 (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).toModularForm').toFun z =
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) z
    rw [heckeT_n_one]
    rfl
  map_mul_of_coprime' m n hmn := by
    letI : NeZero (m : ℕ) := ⟨Nat.pos_iff_ne_zero.mp m.property.1⟩
    letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
    letI : NeZero ((m : ℕ) * n) :=
      ⟨Nat.mul_ne_zero (NeZero.ne (m : ℕ)) (NeZero.ne (n : ℕ))⟩
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply CuspForm.ext
    intro z
    change (heckeT_n k ((m : ℕ) * n)
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).toModularForm').toFun z =
      ((heckeT_n k (m : ℕ))
        ((heckeT_n k (n : ℕ))
          (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).toModularForm')).toFun z
    rw [heckeT_n_mul_coprime k (m : ℕ) (n : ℕ) hmn]
    rfl
  commute' := heckeT_n_cusp_charRestrict_commute_from_mulFormula (N := N) k χ

/-- The restricted cusp `Γ₁(N), χ` good-index operators commute by restricting
the ambient multiplication-table proof source. -/
theorem cuspFormCharSpaceFamily_commute_from_mulFormula
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) :
    Commute ((cuspFormCharSpaceFamily (N := N) k χ).op m)
      ((cuspFormCharSpaceFamily (N := N) k χ).op n) :=
  heckeT_n_cusp_charRestrict_commute_from_mulFormula (N := N) k χ m n

@[simp] lemma cuspCharHeckeOfGoodIndex_coe
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (n : GoodIndex N) (f : cuspFormCharSpace k χ) :
    (((cuspCharHeckeOfGoodIndex (N := N) k χ n f :
        cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
      ambientCuspHeckeOfGoodIndex (N := N) k n
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  exact CuspForm.ext fun _ ↦ rfl

@[simp] lemma cuspFormCharSpaceFamily_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N)
    (f : cuspFormCharSpace k χ) :
    (((cuspFormCharSpaceFamily (N := N) k χ).op n f : cuspFormCharSpace k χ) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ambientCuspHeckeOfGoodIndex (N := N) k n
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  simp [cuspFormCharSpaceFamily, cuspCharHeckeOfGoodIndex_coe]

/-- The cusp-form `Γ₀(N), χ`-style space, expressed using the twisted-slash
predicate rather than the diamond-eigenspace definition. -/
noncomputable def cuspGamma0NebentypusSubmodule
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (cuspFormCharSpace k χ).copy
    {f | IsNebentypus k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ)}
    (by
      ext f
      simp [cuspFormCharSpace_iff_nebentypus, isNebentypus_iff, gamma0NebentypusChar])

@[simp] lemma mem_cuspGamma0NebentypusSubmodule_iff (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspGamma0NebentypusSubmodule (N := N) k χ ↔
      IsNebentypus k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ) :=
  Iff.rfl

/-- Identity linear equivalence between the existing cusp character space and the
experimental twisted-slash cusp space. -/
noncomputable def cuspFormCharSpace_equiv_gamma0Nebentypus
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ ≃ₗ[ℂ] cuspGamma0NebentypusSubmodule (N := N) k χ where
  toFun f := ⟨f.1, (isNebentypus_iff k (gamma0NebentypusChar (N := N) χ)
    (f.1 : UpperHalfPlane → ℂ)).2 ((cuspFormCharSpace_iff_nebentypus (N := N) k χ f.1).1 f.2)⟩
  invFun f := ⟨f.1, (cuspFormCharSpace_iff_nebentypus (N := N) k χ f.1).2
    ((isNebentypus_iff k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ)).1
      ((mem_cuspGamma0NebentypusSubmodule_iff (N := N) k χ f.1).1 f.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma mem_cuspFormCharSpace_iff_mem_cuspGamma0NebentypusSubmodule (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormCharSpace k χ ↔ f ∈ cuspGamma0NebentypusSubmodule (N := N) k χ :=
  (cuspFormCharSpace_iff_nebentypus (N := N) k χ f).trans
    (isNebentypus_iff k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ)).symm

@[simp] lemma mem_cuspGamma0NebentypusSubmodule_iff_toModularForm'_mem_gamma0NebentypusSubmodule
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspGamma0NebentypusSubmodule (N := N) k χ ↔
      f.toModularForm' ∈ gamma0NebentypusSubmodule (N := N) k χ := by
  rw [mem_cuspGamma0NebentypusSubmodule_iff, mem_gamma0NebentypusSubmodule_iff]; rfl

/-- The good cusp Hecke family transported to the experimental `Γ₀(N), χ`-style
cusp space. -/
noncomputable def cuspGamma0NebentypusFamily
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    GoodHeckeFamily N (cuspGamma0NebentypusSubmodule (N := N) k χ) :=
  GoodHeckeFamily.transport
    (cuspFormCharSpace_equiv_gamma0Nebentypus (N := N) k χ)
    (cuspFormCharSpaceFamily (N := N) k χ)

@[simp] lemma cuspGamma0NebentypusFamily_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N)
    (f : cuspGamma0NebentypusSubmodule (N := N) k χ) :
    (((cuspGamma0NebentypusFamily (N := N) k χ).op n f :
        cuspGamma0NebentypusSubmodule (N := N) k χ) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ambientCuspHeckeOfGoodIndex (N := N) k n
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  cuspFormCharSpaceFamily_coe (N := N) k χ n
    ((cuspFormCharSpace_equiv_gamma0Nebentypus (N := N) k χ).symm f)

end HeckeRing.GL2.Unified
