/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace

/-!
# The `Γ₀(N), χ` model of the character space

This file repackages `modFormCharSpace k χ` with its carrier expressed by the
twisted `Γ₀(N)`-slash/Nebentypus predicate from `Gamma1Pair.lean`, exposing the
`Γ₁(N)` character-space API in `Γ₀(N), χ` form.

## Main definitions

* `gamma0NebentypusChar`: the `Γ₀(N)`-character `χ ∘ Gamma0MapUnits` attached to
  a Dirichlet character `χ`.
* `gamma0NebentypusSubmodule`: `modFormCharSpace k χ`, with membership stated as
  the Nebentypus condition for `gamma0NebentypusChar χ`.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ}

/-- The `Γ₀(N)`-character obtained from a Dirichlet character `χ` by composing
with `Gamma0MapUnits`. -/
noncomputable def gamma0NebentypusChar (χ : (ZMod N)ˣ →* ℂˣ) : Gamma0 N →* ℂˣ :=
  χ.comp (Gamma0MapUnits (N := N))

@[simp] lemma gamma0NebentypusChar_apply (χ : (ZMod N)ˣ →* ℂˣ) (g : Gamma0 N) :
    gamma0NebentypusChar χ g = χ (Gamma0MapUnits g) := rfl

variable [NeZero N]

/-- The existing `modFormCharSpace k χ`, copied so that its carrier is expressed
as the twisted `Γ₀(N)`-Nebentypus condition. -/
noncomputable def gamma0NebentypusSubmodule (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (modFormCharSpace k χ).copy
    {f | IsNebentypus k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ)}
    (Set.ext fun f ↦ by simp [modFormCharSpace_iff_nebentypus, isNebentypus_iff])

/-- Membership in the `Γ₀(N), χ` model is exactly the twisted slash/Nebentypus condition. -/
@[simp] lemma mem_gamma0NebentypusSubmodule_iff (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ gamma0NebentypusSubmodule (N := N) k χ ↔
      IsNebentypus k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ) :=
  Iff.rfl

end HeckeRing.GL2.Unified
