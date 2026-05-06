import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-!
# Lemmas about `atImInfty`

Probably put this at `Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`.
-/

open UpperHalfPlane

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)

lemma Filter.tendsto_im_atImInfty : Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop :=
  tendsto_comap
