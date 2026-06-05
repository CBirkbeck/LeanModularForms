/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.Core

/-!
# The good Hecke family on `Γ₁(N)` character spaces

This file packages the restricted operators
`heckeT_coprimeRestrict k χ : coprimeToN N → End(modFormCharSpace k χ)` into the
`GoodHeckeFamily` interface.

## Main definitions

* `ambientHeckeOfGoodIndex`: the ambient `Γ₁(N)` Hecke operator `heckeT_n`
  attached to a good index.
* `modFormCharSpaceFamily`: the good Hecke family of restricted operators on
  `modFormCharSpace k χ`.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The ambient `Γ₁(N)` Hecke operator `heckeT_n` attached to a good index. -/
noncomputable def ambientHeckeOfGoodIndex (k : ℤ) (n : GoodIndex N) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeT_n k (n : ℕ)

/-- The ambient good-index Hecke operators pairwise commute. -/
theorem ambientHeckeOfGoodIndex_commute (k : ℤ) (m n : GoodIndex N) :
    Commute (ambientHeckeOfGoodIndex k m) (ambientHeckeOfGoodIndex k n) :=
  heckeT_n_comm k (m : ℕ) (n : ℕ) m.property.2 n.property.2

/-- Pointwise form of `ambientHeckeOfGoodIndex_commute`. -/
theorem ambientHeckeOfGoodIndex_commute_apply (k : ℤ) (m n : GoodIndex N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ambientHeckeOfGoodIndex k m (ambientHeckeOfGoodIndex k n f) =
      ambientHeckeOfGoodIndex k n (ambientHeckeOfGoodIndex k m f) :=
  LinearMap.congr_fun (ambientHeckeOfGoodIndex_commute k m n).eq f

/-- The restricted `Γ₁(N), χ` good-index Hecke operators pairwise commute. -/
theorem heckeT_coprimeRestrict_commute (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) : Commute (heckeT_coprimeRestrict k χ m) (heckeT_coprimeRestrict k χ n) :=
  LinearMap.ext fun f ↦ Subtype.ext <|
    ambientHeckeOfGoodIndex_commute_apply k m n
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- The restricted `Γ₁(N), χ` Hecke operators as a `GoodHeckeFamily`. -/
noncomputable def modFormCharSpaceFamily (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    GoodHeckeFamily N (modFormCharSpace k χ) where
  op := heckeT_coprimeRestrict k χ
  map_one' := heckeT_coprimeRestrict_one k χ
  map_mul_of_coprime' := heckeT_coprimeRestrict_mul_coprime k χ
  commute' := heckeT_coprimeRestrict_commute k χ

/-- The operator of `modFormCharSpaceFamily k χ` at index `n` is
`heckeT_coprimeRestrict k χ n`. -/
@[simp] lemma modFormCharSpaceFamily_op (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N) :
    (modFormCharSpaceFamily k χ).op n = heckeT_coprimeRestrict k χ n := rfl

/-- The restricted operator on `modFormCharSpace k χ` coerces to the ambient
`ambientHeckeOfGoodIndex`. -/
@[simp] lemma modFormCharSpaceFamily_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N)
    (f : modFormCharSpace k χ) :
    ((modFormCharSpaceFamily k χ).op n f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ambientHeckeOfGoodIndex k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  heckeT_n_charRestrict_coe k (n : ℕ) n.property.2 χ f

end HeckeRing.GL2.Unified
