/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.Gamma1CharSpace
import LeanModularForms.HeckeRIngs.GL2.CharSpaceIso
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0_Bridge

/-!
# Unified good-Hecke-family model on `Γ₀(N)` via the trivial character space

This file transports the unified `Γ₁(N)`-character-space Hecke family for
`χ = 1` across the canonical equivalence

`modFormCharSpace_one_equiv_Gamma0 :
  modFormCharSpace k 1 ≃ₗ[ℂ] ModularForm ((Gamma0 N).map (mapGL ℝ)) k`.

The resulting family is the experimental unified `Γ₀(N)` model. For primes
`p ∤ N`, we also record that its `p`-operator agrees with the existing abstract
`Γ₀(N)` Hecke operator on the double coset `D_p_Gamma0`.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The trivial-character `Γ₁(N)` good Hecke family, transported to
`M_k(Γ₀(N))`. -/
noncomputable def gamma0TrivialFamily (k : ℤ) :
    GoodHeckeFamily N (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :=
  GoodHeckeFamily.transport (modFormCharSpace_one_equiv_Gamma0 N k)
    (modFormCharSpaceFamily (N := N) k (1 : (ZMod N)ˣ →* ℂˣ))

@[simp] lemma gamma0TrivialFamily_apply
    (k : ℤ) (n : GoodIndex N) (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (gamma0TrivialFamily (N := N) k).op n f =
      modFormCharSpace_one_equiv_Gamma0 N k
        ((modFormCharSpaceFamily (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)).op n
          ((modFormCharSpace_one_equiv_Gamma0 N k).symm f)) :=
  rfl

/-- Validation on prime indices: the transported unified operator agrees with the
existing abstract `Γ₀(N)` Hecke operator on `D_p_Gamma0`. -/
theorem gamma0TrivialFamily_prime_eq_heckeOperator_Gamma0
    (k : ℤ) {p : ℕ} (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (gamma0TrivialFamily (N := N) k).op ⟨p, hp.pos, hpN⟩ f =
      heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos) f := by
  let e := modFormCharSpace_one_equiv_Gamma0 N k
  calc
    (gamma0TrivialFamily (N := N) k).op ⟨p, hp.pos, hpN⟩ f
      = e ⟨heckeT_p k p hp hpN
            ((e.symm f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
              ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
          heckeT_p_preserves_modFormCharSpace k p hp hpN
            (1 : (ZMod N)ˣ →* ℂˣ) (e.symm f).property⟩ := by
      rw [gamma0TrivialFamily_apply]
      refine congrArg e (Subtype.ext ?_)
      simpa [ambientHeckeOfGoodIndex, heckeT_n_prime_coprime (N := N) k hp hpN] using
        (modFormCharSpaceFamily_coe (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)
          ⟨p, hp.pos, hpN⟩ (e.symm f))
    _ = heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos) (e (e.symm f)) := by
      simpa using (heckeOperator_Gamma0_eq_equiv_heckeT_p_on_charSpace_one
        (N := N) k p hp hpN (e.symm f)).symm
    _ = heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos) f := by
      rw [e.apply_symm_apply]

/-- The `N = 1` instance of `gamma0TrivialFamily` is the level-1 experimental
unified model. Since `Γ₀(1) = SL₂(ℤ)`, this is the common "away from the level"
Hecke family in level-1 form, kept on the `Γ₀(1)` side for now. -/
noncomputable abbrev levelOneFamily (k : ℤ) :
    GoodHeckeFamily 1 (ModularForm ((Gamma0 1).map (mapGL ℝ)) k) :=
  gamma0TrivialFamily (N := 1) k

end HeckeRing.GL2.Unified
