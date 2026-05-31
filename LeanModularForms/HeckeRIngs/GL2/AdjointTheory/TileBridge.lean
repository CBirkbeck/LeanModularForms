/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.DeltaBSystem

/-!
# Hecke adjoint theory: minimal `T_p_upper` / `peterssonAdj` helpers.

Surviving residue of the former DS double-coset tile bridge module. The
abandoned T024 `DSDoubleCosetTileBridge` sum-chain route was deleted; the
four protected headlines (`heckeT_p_adjoint`,
`exists_simultaneous_eigenform_basis`, `strongMultiplicityOne_constMul`,
`strongMultiplicityOne_axiom_clean`) all route through
`petN_heckeT_p_adjoint_via_trace` in `ConcreteFamily`.

This file now contains only:

* `glMap_T_p_upper_det_pos` — positivity of the `T_p_upper b` GL determinant
  (needed by `ConcreteFamily`, `SummandAdjoint`, and `Newforms.BadPrimeReduction`).
* `peterssonAdj_mul_self_smul_set` — set-level triviality of
  `(peterssonAdj β · β) • S = S` (needed by `Newforms.BadPrimeReduction`).
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

theorem glMap_T_p_upper_det_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
    0 < (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ).det.val := by
  show 0 < ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ).det
  rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      ((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
  rw [show (((T_p_upper p hp b : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
      (algebraMap ℚ ℝ) (((T_p_upper p hp b : GL (Fin 2) ℚ).val).det) from
        (RingHom.map_det _ _).symm]
  rw [show ((T_p_upper p hp b : GL (Fin 2) ℚ).val).det = (p : ℚ) by
    simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two, Matrix.of_apply]]
  show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
  rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
  exact_mod_cast hp

open UpperHalfPlane in
private lemma peterssonAdj_mul_self_smul
    (β : GL (Fin 2) ℝ) (τ : ℍ) :
    ((peterssonAdj β * β : GL (Fin 2) ℝ) • τ : ℍ) = τ := by
  rw [mul_smul, peterssonAdj_smul_eq, inv_smul_smul]

open UpperHalfPlane in
/-- **T090 trivial action of `peterssonAdj β · β` on sets of `ℍ`.**

Set-level extension of `peterssonAdj_mul_self_smul`: pointwise triviality
implies `(peterssonAdj β · β) • S = S` for any `S : Set ℍ`. -/
lemma peterssonAdj_mul_self_smul_set
    (β : GL (Fin 2) ℝ) (S : Set ℍ) :
    ((peterssonAdj β * β : GL (Fin 2) ℝ) • S : Set ℍ) = S := by
  ext τ
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs, hτ⟩
    have hτ' : (peterssonAdj β * β : GL (Fin 2) ℝ) • s = τ := hτ
    rw [peterssonAdj_mul_self_smul] at hτ'
    exact hτ' ▸ hs
  · intro hτ
    refine ⟨τ, hτ, ?_⟩
    show (peterssonAdj β * β : GL (Fin 2) ℝ) • τ = τ
    exact peterssonAdj_mul_self_smul β τ

end HeckeRing.GL2
