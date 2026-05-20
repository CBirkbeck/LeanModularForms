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
noncomputable def gamma0TwistedSlashModHom
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    ↥(Gamma0 N) →* Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun g :=
    (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
      diamondOpHom (N := N) k (Gamma0MapUnits g)
  map_one' := by
    ext f z
    simp [gamma0NebentypusChar]
  map_mul' g₁ g₂ := by
    ext f z
    simp [gamma0NebentypusChar, map_mul, Module.End.mul_apply, smul_smul, mul_comm, mul_assoc]

@[simp] lemma gamma0TwistedSlashModHom_apply
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : ↥(Gamma0 N)) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
noncomputable def gamma0TwistedSlashCuspHom
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    ↥(Gamma0 N) →* Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun g :=
    (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
      diamondOpCuspHom (N := N) k (Gamma0MapUnits g)
  map_one' := by
    ext f z
    simp [gamma0NebentypusChar]
  map_mul' g₁ g₂ := by
    ext f z
    simp [gamma0NebentypusChar, map_mul, Module.End.mul_apply, smul_smul, mul_comm, mul_assoc]

@[simp] lemma gamma0TwistedSlashCuspHom_apply
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (g : ↥(Gamma0 N)) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
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
noncomputable def gamma0TwistedSlashModFixedSubmodule
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ g : ↥(Gamma0 N), Module.End.eigenspace (gamma0TwistedSlashModHom (N := N) k χ g) (1 : ℂ)

  @[simp] lemma mem_gamma0TwistedSlashModFixedSubmodule_iff
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ gamma0TwistedSlashModFixedSubmodule (N := N) k χ ↔
      ∀ g : ↥(Gamma0 N), gamma0TwistedSlashModHom (N := N) k χ g f = f := by
  simp [gamma0TwistedSlashModFixedSubmodule, Submodule.mem_iInf]

theorem gamma0TwistedSlashModFixedSubmodule_eq_modFormCharSpace
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    gamma0TwistedSlashModFixedSubmodule (N := N) k χ = modFormCharSpace k χ := by
  ext f
  rw [mem_gamma0TwistedSlashModFixedSubmodule_iff, mem_modFormCharSpace_iff]
  constructor
  · intro hf d
    obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    have hgfix := hf g
    change (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
        diamondOpHom (N := N) k (Gamma0MapUnits g) f = f at hgfix
    have hgfix' := congrArg (fun x => (↑(gamma0NebentypusChar (N := N) χ g) : ℂ) • x) hgfix
    simp [gamma0NebentypusChar] at hgfix'
    rw [hg] at hgfix'
    simpa [gamma0NebentypusChar, hg] using hgfix'
  · intro hf g
    have hfg := hf (Gamma0MapUnits g)
    change (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
        diamondOpHom (N := N) k (Gamma0MapUnits g) f = f
    rw [hfg]
    simp [gamma0NebentypusChar]

theorem gamma0TwistedSlashModFixedSubmodule_eq_gamma0NebentypusSubmodule
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    gamma0TwistedSlashModFixedSubmodule (N := N) k χ =
      gamma0NebentypusSubmodule (N := N) k χ := by
  rw [gamma0TwistedSlashModFixedSubmodule_eq_modFormCharSpace]
  ext f
  simp [mem_modFormCharSpace_iff_mem_gamma0NebentypusSubmodule]

/-- The fixed submodule of the twisted `Γ₀(N)` action on the ambient cusp-form
space. -/
noncomputable def gamma0TwistedSlashCuspFixedSubmodule
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨅ g : ↥(Gamma0 N), Module.End.eigenspace (gamma0TwistedSlashCuspHom (N := N) k χ g) (1 : ℂ)

  @[simp] lemma mem_gamma0TwistedSlashCuspFixedSubmodule_iff
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ gamma0TwistedSlashCuspFixedSubmodule (N := N) k χ ↔
      ∀ g : ↥(Gamma0 N), gamma0TwistedSlashCuspHom (N := N) k χ g f = f := by
  simp [gamma0TwistedSlashCuspFixedSubmodule, Submodule.mem_iInf]

theorem gamma0TwistedSlashCuspFixedSubmodule_eq_cuspFormCharSpace
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    gamma0TwistedSlashCuspFixedSubmodule (N := N) k χ = cuspFormCharSpace k χ := by
  ext f
  rw [mem_gamma0TwistedSlashCuspFixedSubmodule_iff, mem_cuspFormCharSpace_iff]
  constructor
  · intro hf d
    obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
    have hgfix := hf g
    change (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
        diamondOpCuspHom (N := N) k (Gamma0MapUnits g) f = f at hgfix
    have hgfix' := congrArg (fun x => (↑(gamma0NebentypusChar (N := N) χ g) : ℂ) • x) hgfix
    simp [gamma0NebentypusChar] at hgfix'
    rw [hg] at hgfix'
    simpa [gamma0NebentypusChar, hg] using hgfix'
  · intro hf g
    have hfg := hf (Gamma0MapUnits g)
    change (↑(gamma0NebentypusChar (N := N) χ g) : ℂ)⁻¹ •
        diamondOpCuspHom (N := N) k (Gamma0MapUnits g) f = f
    rw [hfg]
    simp [gamma0NebentypusChar]

theorem gamma0TwistedSlashCuspFixedSubmodule_eq_cuspGamma0NebentypusSubmodule
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    gamma0TwistedSlashCuspFixedSubmodule (N := N) k χ =
      cuspGamma0NebentypusSubmodule (N := N) k χ := by
  rw [gamma0TwistedSlashCuspFixedSubmodule_eq_cuspFormCharSpace]
  ext f
  simp [mem_cuspFormCharSpace_iff_mem_cuspGamma0NebentypusSubmodule]

end HeckeRing.GL2.Unified
