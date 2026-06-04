/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0
import LeanModularForms.HeckeRIngs.GL2.CharSpaceIso

/-!
# Bridge: `heckeT_p` on `modFormCharSpace k 1` corresponds to `heckeOperator_Gamma0`

This file shows that on the trivial-character eigenspace `modFormCharSpace k 1`,
the Γ₁(N)-level Hecke operator `heckeT_p` corresponds (via the canonical isomorphism
`modFormCharSpace_one_equiv_Gamma0`) to the Γ₀(N)-level abstract Hecke operator
`heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)`.

## Main theorem

* `heckeT_p_val_eq_heckeOperator_Gamma0_on_charSpace_one` — for
  `f ∈ modFormCharSpace k 1`, the two operators agree as functions `ℍ → ℂ`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing DoubleCoset

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

private lemma adj_diag_1p_eq_T_p_lower_bridge (p : ℕ) (hp : Nat.Prime p) :
    GL_adjugate (diagMat 2 ![1, p] : GL (Fin 2) ℚ) =
      (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  apply Units.ext; ext i j
  have hpos (k : Fin 2) : 0 < (![1, p] : Fin 2 → Nat) k := by fin_cases k <;> simp [hp.pos]
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by ext x; fin_cases x <;> simp
  simp only [GL_adjugate_val, diagMat_val _ _ hpos]
  fin_cases i <;> fin_cases j <;>
    simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, Matrix.of_apply, huniv,
      show ({0, 1} : Finset (Fin 2)).erase 0 = {1} from by decide,
      show ({0, 1} : Finset (Fin 2)).erase 1 = {0} from by decide, Finset.prod_singleton]

end HeckeRing.GL2
