/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.CuspNebentypusSpace

/-!
# Experimental twisted `Γ₀(N)` action on `Γ₁(N)` spaces

This file adds the missing operator-level infrastructure behind the experimental
`Γ₀(N), χ` model. Instead of only transporting the already-existing character
spaces, we package the twisted slash law as actual `Γ₀(N)`-indexed endomorphisms
of the ambient `Γ₁(N)` modular and cusp spaces, then identify their fixed
submodules with the previously defined experimental Nebentypus spaces.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The twisted `Γ₀(N)` slash action on `M_k(Γ₁(N))`, realised as an actual
linear endomorphism of the ambient modular-form space. -/
noncomputable def gamma0TwistedSlashModHom (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    ↥(Gamma0 N) →* Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun g :=
    (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
      diamondOpHom (N := N) k (Gamma0MapUnits g)
  map_one' := by simp [gamma0NebentypusChar]
  map_mul' g₁ g₂ := by simp [gamma0NebentypusChar, map_mul, smul_smul, mul_comm]

@[simp] lemma gamma0TwistedSlashModHom_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (g : ↥(Gamma0 N))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ((gamma0TwistedSlashModHom (N := N) k χ g) f : UpperHalfPlane → ℂ) =
      twistedSlash k (gamma0NebentypusChar (N := N) χ) g (f : UpperHalfPlane → ℂ) := by
  ext z
  change ((((↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
      diamondOp (N := N) k (Gamma0MapUnits g)) f) : ModularForm _ _) z =
    twistedSlash k (gamma0NebentypusChar (N := N) χ) g (f : UpperHalfPlane → ℂ) z
  rw [diamondOp_eq_diamondOpAux (N := N) k (Gamma0MapUnits g) g rfl]
  rfl

/-- The twisted `Γ₀(N)` slash action on `S_k(Γ₁(N))`, realised as an actual
linear endomorphism of the ambient cusp-form space. -/
noncomputable def gamma0TwistedSlashCuspHom (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    ↥(Gamma0 N) →* Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun g :=
    (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
      diamondOpCuspHom (N := N) k (Gamma0MapUnits g)
  map_one' := by simp [gamma0NebentypusChar]
  map_mul' g₁ g₂ := by simp [gamma0NebentypusChar, map_mul, smul_smul, mul_comm]

@[simp] lemma gamma0TwistedSlashCuspHom_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (g : ↥(Gamma0 N))
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ((gamma0TwistedSlashCuspHom (N := N) k χ g) f : UpperHalfPlane → ℂ) =
      twistedSlash k (gamma0NebentypusChar (N := N) χ) g (f : UpperHalfPlane → ℂ) := by
  ext z
  change ((((↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
      diamondOpCusp (N := N) k (Gamma0MapUnits g)) f) : CuspForm _ _) z =
    twistedSlash k (gamma0NebentypusChar (N := N) χ) g (f : UpperHalfPlane → ℂ) z
  rw [diamondOpCusp_eq (N := N) k (Gamma0MapUnits g) g rfl]
  rfl

/-- The fixed submodule of the twisted `Γ₀(N)` action on the ambient modular
form space. -/
noncomputable def gamma0TwistedSlashModFixedSubmodule (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ g : ↥(Gamma0 N), Module.End.eigenspace (gamma0TwistedSlashModHom (N := N) k χ g) (1 : ℂ)

@[simp] lemma mem_gamma0TwistedSlashModFixedSubmodule_iff (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ gamma0TwistedSlashModFixedSubmodule (N := N) k χ ↔
      ∀ g : ↥(Gamma0 N), gamma0TwistedSlashModHom (N := N) k χ g f = f := by
  simp [gamma0TwistedSlashModFixedSubmodule, Submodule.mem_iInf]

/-- The fixed submodule of the twisted `Γ₀(N)` action on the ambient cusp-form
space. -/
noncomputable def gamma0TwistedSlashCuspFixedSubmodule (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ g : ↥(Gamma0 N), Module.End.eigenspace (gamma0TwistedSlashCuspHom (N := N) k χ g) (1 : ℂ)

@[simp] lemma mem_gamma0TwistedSlashCuspFixedSubmodule_iff (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ gamma0TwistedSlashCuspFixedSubmodule (N := N) k χ ↔
      ∀ g : ↥(Gamma0 N), gamma0TwistedSlashCuspHom (N := N) k χ g f = f := by
  simp [gamma0TwistedSlashCuspFixedSubmodule, Submodule.mem_iInf]

end HeckeRing.GL2.Unified
