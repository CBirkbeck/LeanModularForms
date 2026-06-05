/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace

/-!
# Experimental `Γ₀(N), χ`-style space model

This file repackages the existing `modFormCharSpace k χ` using the twisted
`Γ₀(N)`-slash/Nebentypus predicate already proved in `Gamma1Pair.lean`.

The point is not to introduce new mathematics, but to expose the current
`Γ₁(N)` character-space API in the form suggested by the intended unified
architecture:

* a `Γ₀(N)`-character `χ ∘ Gamma0MapUnits`
* a corresponding twisted-slash/Nebentypus subspace
* the good Hecke family transported onto that space

This remains experimental and isolated from the active SMO path.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The `Γ₀(N)`-character obtained from a Dirichlet character `χ` by composing
with `Gamma0MapUnits`. -/
noncomputable def gamma0NebentypusChar (χ : (ZMod N)ˣ →* ℂˣ) : ↥(Gamma0 N) →* ℂˣ :=
  χ.comp (Gamma0MapUnits (N := N))

omit [NeZero N] in

/-- The existing `modFormCharSpace k χ`, copied so that its carrier is expressed
as the twisted `Γ₀(N)`-Nebentypus condition. -/
noncomputable def gamma0NebentypusSubmodule (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (modFormCharSpace k χ).copy
    {f | IsNebentypus k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ)}
    (by ext f; simp [modFormCharSpace_iff_nebentypus, isNebentypus_iff, gamma0NebentypusChar])

/-- Membership in the experimental `Γ₀(N), χ`-style space is exactly the twisted
slash/Nebentypus condition. -/
@[simp] lemma mem_gamma0NebentypusSubmodule_iff (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ gamma0NebentypusSubmodule (N := N) k χ ↔
      IsNebentypus k (gamma0NebentypusChar (N := N) χ) (f : UpperHalfPlane → ℂ) :=
  Iff.rfl

end HeckeRing.GL2.Unified
