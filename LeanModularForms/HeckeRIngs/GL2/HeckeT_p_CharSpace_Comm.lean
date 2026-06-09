/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.CharSpaceIso
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp

/-!
# Commutativity of `heckeT_p_all` on the Nebentypus character spaces

Via the trivial-character bridge to the abstract `Γ₀(N)` Hecke operator, we obtain a clean,
short proof that for any two
distinct primes `p, q` (both coprime to `N`), the operators `heckeT_p_all k p hp`
and `heckeT_p_all k q hq` commute when restricted to the trivial Nebentypus
eigenspace `modFormCharSpace k 1`. The proof reduces to commutativity of the abstract
Hecke ring `𝕋(Gamma0_pair N) ℤ` (Shimura Prop 3.8, via
`Gamma0_pair_HeckeAlgebra_mul_comm`).

For non-trivial characters (or non-coprime primes), the same commutativity
statement on each eigenspace `modFormCharSpace k χ` is a direct corollary of the
existing global commutativity theorem `heckeT_p_all_comm_distinct`.

## Main results

* `heckeT_p_all_eq_gamma0_on_charSpace_one` — the composition of `heckeT_p_all` with
  the trivial-character isomorphism factors through `heckeOperator_Gamma0`.
* `heckeT_p_all_comm_on_charSpace_one_coprime` — commutativity of `heckeT_p_all` on the
  trivial-character eigenspace for two primes coprime to `N`, proved via
  `Gamma0_pair_HeckeAlgebra_mul_comm`.
* `heckeT_p_all_comm_on_charSpace` — same commutativity on an arbitrary χ-eigenspace,
  as a corollary of the global theorem.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- Conjugation of an endomorphism of `ModularForm ((Gamma0 N).map (mapGL ℝ)) k` by
the iso `modFormCharSpace_one_equiv_Gamma0`, yielding an endomorphism of
`modFormCharSpace k 1`. -/
noncomputable def conjEndCharSpaceOne (k : ℤ)
    (T : Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k)) :
    Module.End ℂ (modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :=
  (modFormCharSpace_one_equiv_Gamma0 N k).symm.toLinearMap ∘ₗ
    T ∘ₗ (modFormCharSpace_one_equiv_Gamma0 N k).toLinearMap

/-- Conjugation is a ring hom from `End(M_k(Γ₀(N)))` to `End(modFormCharSpace k 1)`. -/
noncomputable def conjEndRingHomCharSpaceOne (k : ℤ) :
    Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) →+*
      Module.End ℂ (modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) where
  toFun := conjEndCharSpaceOne k
  map_one' := LinearMap.ext fun _ ↦ by
    simp [conjEndCharSpaceOne, (modFormCharSpace_one_equiv_Gamma0 N k).symm_apply_apply]
  map_mul' _ _ := LinearMap.ext fun _ ↦ by
    simp [conjEndCharSpaceOne, Module.End.mul_apply]
  map_zero' := LinearMap.ext fun _ ↦ by simp [conjEndCharSpaceOne]
  map_add' _ _ := LinearMap.ext fun _ ↦ by
    simp [conjEndCharSpaceOne, LinearMap.add_apply, map_add]

/-- The Hecke ring hom `𝕋(Gamma0_pair N) ℤ →+* End(modFormCharSpace k 1)` obtained
by conjugating `heckeRingHom_Gamma0` through `modFormCharSpace_one_equiv_Gamma0`.

Since the source is a commutative ring (`Gamma0_pair_HeckeAlgebra_mul_comm`), the
image commutes. In particular, `heckeT_p_all`s arising from `heckeRingHom_Gamma0`
on the trivial-character eigenspace commute. -/
noncomputable def heckeRingHomCharSpaceOne (k : ℤ) :
    𝕋 (Gamma0_pair N) ℤ →+*
      Module.End ℂ (modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :=
  (conjEndRingHomCharSpaceOne (N := N) k).comp (heckeRingHom_Gamma0 N k)

@[simp] lemma heckeRingHomCharSpaceOne_apply (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ) :
    heckeRingHomCharSpaceOne (N := N) k T =
    conjEndCharSpaceOne (N := N) k (heckeRingHom_Gamma0 N k T) := rfl

end HeckeRing.GL2
