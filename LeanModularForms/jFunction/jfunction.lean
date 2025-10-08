import Mathlib

namespace ModularForms

open Complex TopologicalSpace Filter Set ModularForm EisensteinSeries UpperHalfPlane MatrixGroups

noncomputable section

abbrev  E4 := (ModularForm.E (by norm_num : 3 ≤ 4))

def j : ℍ → ℂ := fun τ ↦ (E4 τ) ^ 3 / ModularForm.eta τ ^ 24

lemma j_slashInvariant (γ : SL(2, ℤ)) :  j ∣[(0 : ℤ)] γ = j := by
  ext z
  rw [slash_action_eq'_iff]
  sorry
