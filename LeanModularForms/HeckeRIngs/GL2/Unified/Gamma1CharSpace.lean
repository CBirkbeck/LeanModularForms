 /-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.Core

/-!
# Unified good-Hecke-family model on `Γ₁(N)` character spaces

This file packages the existing restricted operators
`heckeT_coprimeRestrict k χ : coprimeToN N → End(modFormCharSpace k χ)` into the
experimental `GoodHeckeFamily` interface.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The ambient `Γ₁(N)` Hecke operator attached to a good index. This is just
`heckeT_n`, with the `NeZero` instance discharged from the positivity packaged
inside `GoodIndex N`. -/
noncomputable def ambientHeckeOfGoodIndex (k : ℤ) (n : GoodIndex N) :
    Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  exact heckeT_n k (n : ℕ)

/-- The ambient good-index operators commute by the symmetric multiplication
table `heckeT_n_mul`, not by the later `heckeT_n_comm` induction. -/
theorem ambientHeckeOfGoodIndex_commute_from_mulFormula
    (k : ℤ) (m n : GoodIndex N) :
    Commute (ambientHeckeOfGoodIndex (N := N) k m)
      (ambientHeckeOfGoodIndex (N := N) k n) := by
  letI : NeZero (m : ℕ) := ⟨Nat.pos_iff_ne_zero.mp m.property.1⟩
  letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  show heckeT_n (N := N) k (m : ℕ) * heckeT_n k (n : ℕ) =
      heckeT_n (N := N) k (n : ℕ) * heckeT_n k (m : ℕ)
  rw [heckeT_n_mul (N := N) k (m : ℕ) (n : ℕ),
    heckeT_n_mul (N := N) k (n : ℕ) (m : ℕ)]
  refine Finset.sum_bij
    (fun d _ => ⟨d.1, by simpa [Nat.gcd_comm] using d.2⟩)
    (fun _ _ => Finset.mem_attach _ _)
    (fun a _ b _ h => by
      exact Subtype.ext (congrArg (fun z => z.1) h))
    (fun d _ => ⟨⟨d.1, by simpa [Nat.gcd_comm] using d.2⟩, Finset.mem_attach _ _, by rfl⟩)
    (fun d _ => by simp [Nat.mul_comm])

/-- Pointwise form of `ambientHeckeOfGoodIndex_commute_from_mulFormula`. -/
theorem ambientHeckeOfGoodIndex_commute_apply_from_mulFormula
    (k : ℤ) (m n : GoodIndex N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ambientHeckeOfGoodIndex (N := N) k m
        (ambientHeckeOfGoodIndex (N := N) k n f) =
      ambientHeckeOfGoodIndex (N := N) k n
        (ambientHeckeOfGoodIndex (N := N) k m f) := by
  exact LinearMap.congr_fun
    (ambientHeckeOfGoodIndex_commute_from_mulFormula (N := N) k m n).eq f

/-- The restricted `Γ₁(N), χ` good-index operators commute by restricting the
ambient multiplication-table proof source. -/
theorem heckeT_coprimeRestrict_commute_from_mulFormula
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) :
    Commute (heckeT_coprimeRestrict k χ m) (heckeT_coprimeRestrict k χ n) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  exact ambientHeckeOfGoodIndex_commute_apply_from_mulFormula
    (N := N) k m n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)

/-- The existing restricted `Γ₁(N), χ` Hecke operators, viewed through the unified
"good Hecke family" interface. -/
noncomputable def modFormCharSpaceFamily (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    GoodHeckeFamily N (modFormCharSpace k χ) where
  op := heckeT_coprimeRestrict k χ
  map_one' := heckeT_coprimeRestrict_one k χ
  map_mul_of_coprime' := heckeT_coprimeRestrict_mul_coprime k χ
  commute' := heckeT_coprimeRestrict_commute_from_mulFormula (N := N) k χ

/-- The restricted `Γ₁(N), χ` good-index operators commute by restricting the
ambient multiplication-table proof source. -/
theorem modFormCharSpaceFamily_commute_from_mulFormula
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) :
    Commute ((modFormCharSpaceFamily (N := N) k χ).op m)
      ((modFormCharSpaceFamily (N := N) k χ).op n) :=
  heckeT_coprimeRestrict_commute_from_mulFormula (N := N) k χ m n

@[simp] lemma modFormCharSpaceFamily_apply
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N) :
    (modFormCharSpaceFamily (N := N) k χ).op n = heckeT_coprimeRestrict k χ n :=
  rfl

@[simp] lemma modFormCharSpaceFamily_coe
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : GoodIndex N) (f : modFormCharSpace k χ) :
    (((modFormCharSpaceFamily (N := N) k χ).op n f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ambientHeckeOfGoodIndex (N := N) k n
        (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  haveI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  calc
    (((modFormCharSpaceFamily (N := N) k χ).op n f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      = heckeT_n k (n : ℕ) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
          simpa [modFormCharSpaceFamily, heckeT_coprimeRestrict] using
            (heckeT_n_charRestrict_coe (N := N) k (n : ℕ) n.property.2 χ f)
    _ = ambientHeckeOfGoodIndex (N := N) k n
          (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
          rfl

lemma modFormCharSpaceFamily_commute_apply
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) (f : modFormCharSpace k χ) :
    (modFormCharSpaceFamily (N := N) k χ).op m
        ((modFormCharSpaceFamily k χ).op n f) =
      (modFormCharSpaceFamily (N := N) k χ).op n
        ((modFormCharSpaceFamily k χ).op m f) :=
  (modFormCharSpaceFamily (N := N) k χ).commute_apply m n f

end HeckeRing.GL2.Unified
