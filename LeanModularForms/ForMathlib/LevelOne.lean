/- /-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.NumberTheory.Modular
import LeanModularForms.ForMathlib.QExpansion
import LeanModularForms.ForMathlib.CongruenceSubgrps
import LeanModularForms.ForMathlib.Identities
import Mathlib.NumberTheory.ModularForms.LevelOne
/-!
# Level one modular forms

This file contains results specific to modular forms of level one, ie. modular forms for `SL(2, ℤ)`.

TODO: Add finite-dimensionality of these spaces of modular forms.

-/

open UpperHalfPlane ModularGroup SlashInvariantForm ModularForm Complex
  CongruenceSubgroup Real Function SlashInvariantFormClass ModularFormClass Periodic

local notation "𝕢" => qParam

variable {F : Type*} [FunLike F ℍ ℂ] {k : ℤ}

namespace ModularFormClass

variable [ModularFormClass F Γ(1) k]

private theorem cuspFunction_eqOn_const_of_nonpos_wt (hk : k ≤ 0) (f : F) :
    Set.EqOn (cuspFunction 1 f) (const ℂ (cuspFunction 1 f 0)) (Metric.ball 0 1) := by
  refine eq_const_of_exists_le (fun q hq ↦ ?_) (exp_nonneg (-π)) ?_ (fun q hq ↦ ?_)
  · exact (differentiableAt_cuspFunction' f (dvd_of_eq <| Subgroup.Gamma_width 1)
      (mem_ball_zero_iff.mp hq)).differentiableWithinAt
  · simp only [exp_lt_one_iff, Left.neg_neg_iff, pi_pos]
  · simp only [Metric.mem_closedBall, dist_zero_right]
    rcases eq_or_ne q 0 with rfl | hq'
    · refine ⟨0, by simpa only [norm_zero] using exp_nonneg _, le_rfl⟩
    · obtain ⟨ξ, hξ, hξ₂⟩ := exists_one_half_le_im_and_norm_le hk f
        ⟨_, im_invQParam_pos_of_norm_lt_one Real.zero_lt_one (mem_ball_zero_iff.mp hq) hq'⟩
      exact ⟨_, norm_qParam_le_of_one_half_le_im hξ,
        by simpa [← eq_cuspFunction' f (dvd_of_eq <| Subgroup.Gamma_width 1),
          Nat.cast_one, coe_mk, qParam_right_inv one_ne_zero hq'] using hξ₂⟩

private theorem levelOne_nonpos_wt_const (hk : k ≤ 0) (f : F) :
    ⇑f = Function.const _ (cuspFunction 1 f 0) := funext fun z ↦ by
  have hQ : 𝕢 1 z ∈ Metric.ball 0 1 := by simpa using (norm_qParam_lt_iff zero_lt_one 0 _).mpr z.2
  simpa [← eq_cuspFunction' f (dvd_of_eq <| Subgroup.Gamma_width 1)] using
    cuspFunction_eqOn_const_of_nonpos_wt hk f hQ


end ModularFormClass
 -/
