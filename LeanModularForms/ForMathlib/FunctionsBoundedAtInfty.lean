import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

open UpperHalfPlane

theorem isBoundedAtImInfty_neg_iff (f : ℍ → ℂ) :
    IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f := by
  simp [UpperHalfPlane.isBoundedAtImInfty_iff]

alias ⟨_, IsBoundedAtImInfty.neg⟩ := isBoundedAtImInfty_neg_iff
