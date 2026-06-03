/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

@[expose] public section

/-!
# Helper lemmas for `UpperHalfPlane.atImInfty`

A few utility lemmas about the filter `atImInfty` on the upper half-plane: unfolding
`Eventually` predicates, the imaginary-part tendsto, and a non-vanishing criterion from
a non-zero limit. Candidates for upstreaming to
`Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty`.
-/

open UpperHalfPlane Filter Topology

lemma Filter.eventually_atImInfty {p : ℍ → Prop} :
    (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z :=
  atImInfty_mem (setOf p)

