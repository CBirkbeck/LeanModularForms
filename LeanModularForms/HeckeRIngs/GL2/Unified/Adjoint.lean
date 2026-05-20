 /-
 Copyright (c) 2026. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: LeanModularForms contributors
 -/
import LeanModularForms.HeckeRIngs.GL2.Unified.TwistedSlash

/-!
# Good-prime adjointness and normality interface

This file adds the spectral input that the experimental unification layer still
needs downstream: a `GoodHeckeFamily` may carry a pairing for which each good
Hecke operator has scalar adjoint. In the cusp-form setting this is exactly the
Petersson story:

* on `S_k(Γ₁(N), χ)`, `T_n* = χ(n)⁻¹ T_n`;
* after transport, the same scalar-adjoint relation holds on the experimental
  `Γ₀(N), χ`-style cusp submodule.

The file keeps the interface deliberately lightweight: the abstract layer only
records a pairing and the scalar-adjoint law, and then packages the derived
adjoint operator and normality relation.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- A good Hecke family together with a pairing against which each good operator
has scalar adjoint. The intended example is the Petersson pairing on cusp
spaces, where the adjoint of `T_n` is a scalar multiple of `T_n` itself. -/
structure GoodHeckeFamilyScalarAdjoint
    {V : Type*} [AddCommGroup V] [Module ℂ V] (F : GoodHeckeFamily N V) where
  pairing : V → V → ℂ
  smul_right' : ∀ c : ℂ, ∀ f g : V, pairing f (c • g) = c * pairing f g
  adjointScalar : GoodIndex N → ℂ
  adjoint' : ∀ n : GoodIndex N, ∀ f g : V,
    pairing (F.op n f) g = adjointScalar n * pairing f (F.op n g)

namespace GoodHeckeFamilyScalarAdjoint

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
variable {F : GoodHeckeFamily N V}

/-- The abstract adjoint operator attached to a scalar-adjoint Hecke family. -/
noncomputable def adjointOp (A : GoodHeckeFamilyScalarAdjoint (N := N) F)
    (n : GoodIndex N) : Module.End ℂ V :=
  A.adjointScalar n • F.op n

@[simp] lemma adjointOp_apply
    (A : GoodHeckeFamilyScalarAdjoint (N := N) F)
    (n : GoodIndex N) (f : V) :
    A.adjointOp n f = A.adjointScalar n • F.op n f := rfl

lemma smul_right
    (A : GoodHeckeFamilyScalarAdjoint (N := N) F)
    (c : ℂ) (f g : V) :
    A.pairing f (c • g) = c * A.pairing f g :=
  A.smul_right' c f g

lemma adjoint
    (A : GoodHeckeFamilyScalarAdjoint (N := N) F)
    (n : GoodIndex N) (f g : V) :
    A.pairing (F.op n f) g = A.pairing f (A.adjointOp n g) := by
  rw [adjointOp_apply, A.smul_right, A.adjoint' n f g]

/-- Since the abstract adjoint is a scalar multiple of the original operator,
it commutes with it. This is the normality package needed downstream. -/
lemma normal
    (A : GoodHeckeFamilyScalarAdjoint (N := N) F)
    (n : GoodIndex N) :
    Commute (F.op n) (A.adjointOp n) := by
  ext f
  simp [adjointOp, Module.End.mul_apply]

end GoodHeckeFamilyScalarAdjoint

/-- The Petersson pairing on the existing cusp-form character space. -/
noncomputable def cuspFormCharSpacePetPairing
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspFormCharSpace k χ → cuspFormCharSpace k χ → ℂ :=
  fun f g => petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- The Petersson pairing on the experimental `Γ₀(N), χ` cusp submodule. -/
noncomputable def cuspGamma0NebentypusPetPairing
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    cuspGamma0NebentypusSubmodule (N := N) k χ →
      cuspGamma0NebentypusSubmodule (N := N) k χ → ℂ :=
  fun f g => petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- On `cuspFormCharSpace k χ`, the Petersson adjoint of the good Hecke operator
indexed by `n` is the scalar `χ(n)⁻¹` times the operator itself. -/
noncomputable def cuspFormCharSpaceScalarAdjoint
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    GoodHeckeFamilyScalarAdjoint
      (N := N) (cuspFormCharSpaceFamily (N := N) k χ) where
  pairing := cuspFormCharSpacePetPairing (N := N) k χ
  smul_right' c f g := petN_smul_right c _ _
  adjointScalar n := (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ)
  adjoint' n f g := by
    letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
    change petN (heckeT_n_cusp k (n : ℕ)
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ) *
        petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (heckeT_n_cusp k (n : ℕ)
            (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    rw [heckeT_n_adjoint (N := N) (k := k) (n := (n : ℕ)) n.property.2
      (f := (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
      (g := (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))]
    have hTg :
        heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
          cuspFormCharSpace k χ :=
      heckeT_n_cusp_preserves_cuspFormCharSpace
        (N := N) k (n : ℕ) n.property.2 χ g.property
    change petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        (diamondOpCusp k (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹
          (heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))) =
      (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ) *
        petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (heckeT_n_cusp k (n : ℕ)
            (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    rw [show diamondOpCusp k (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹
          (heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
        (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹) : ℂ) •
          heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) from
      diamondOpCusp_apply_charSpace (N := N) k χ
        (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹ hTg]
    simp only [map_inv, Units.val_inv_eq_inv_val]
    exact petN_smul_right _ _ _

/-- The transported Petersson scalar-adjoint package on the experimental
`Γ₀(N), χ` cusp space. -/
noncomputable def cuspGamma0NebentypusScalarAdjoint
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    GoodHeckeFamilyScalarAdjoint
      (N := N) (cuspGamma0NebentypusFamily (N := N) k χ) where
  pairing := cuspGamma0NebentypusPetPairing (N := N) k χ
  smul_right' c f g := petN_smul_right c _ _
  adjointScalar n := (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ)
  adjoint' n f g := by
    letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
    have hf_char :
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormCharSpace k χ :=
      (mem_cuspFormCharSpace_iff_mem_cuspGamma0NebentypusSubmodule
        (N := N) k χ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr f.property
    have hg_char :
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormCharSpace k χ :=
      (mem_cuspFormCharSpace_iff_mem_cuspGamma0NebentypusSubmodule
        (N := N) k χ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).mpr g.property
    change petN
        (ambientCuspHeckeOfGoodIndex (N := N) k n
          (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ) *
        petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (ambientCuspHeckeOfGoodIndex (N := N) k n
            (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    change petN (heckeT_n_cusp k (n : ℕ)
        (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
        (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ) *
        petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (heckeT_n_cusp k (n : ℕ)
            (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    rw [heckeT_n_adjoint (N := N) (k := k) (n := (n : ℕ)) n.property.2
      (f := (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
      (g := (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))]
    have hTg :
        heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
          cuspFormCharSpace k χ :=
      heckeT_n_cusp_preserves_cuspFormCharSpace
        (N := N) k (n : ℕ) n.property.2 χ hg_char
    change petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
        (diamondOpCusp k (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹
          (heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))) =
      (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ) *
        petN (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (heckeT_n_cusp k (n : ℕ)
            (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k))
    rw [show diamondOpCusp k (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹
          (heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) =
        (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹) : ℂ) •
          heckeT_n_cusp k (n : ℕ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) from
      diamondOpCusp_apply_charSpace (N := N) k χ
        (ZMod.unitOfCoprime (n : ℕ) n.property.2)⁻¹ hTg]
    simp only [map_inv, Units.val_inv_eq_inv_val]
    exact petN_smul_right _ _ _

@[simp] lemma cuspGamma0NebentypusScalarAdjoint_adjointScalar
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N) :
    (cuspGamma0NebentypusScalarAdjoint (N := N) k χ).adjointScalar n =
      (↑(χ (ZMod.unitOfCoprime (n : ℕ) n.property.2))⁻¹ : ℂ) := rfl

end HeckeRing.GL2.Unified
