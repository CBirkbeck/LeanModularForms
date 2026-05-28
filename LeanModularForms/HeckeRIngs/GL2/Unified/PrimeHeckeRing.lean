/- 
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.Gamma0Trivial
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusSpace
import LeanModularForms.HeckeRIngs.GL2.HeckeModularForm_Gamma0

/-!
# Experimental prime-generator Hecke-ring route

This file isolates the part of the "derive commutativity from the Hecke ring"
story that is already genuinely available in the current codebase without new
mathematics:

* the commutative `Γ₀(N)` Hecke algebra `𝕋 (Gamma0_pair N) ℤ`
* its ring hom on `M_k(Γ₀(N))`
* transport of that ring hom to the experimental `Γ₀(N), χ = 1` space

The point is to make the proof source explicit in the isolated `Unified/`
folder. The general-`χ` twisted ring hom is now constructed separately in
`Unified.TwistedHeckeRing`; this file records the prime-generator route and the
trivial-character transport story.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

section Transport

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- Transport an endomorphism ring across a linear equivalence. If `e : V ≃ₗ W`,
an endomorphism of `W` induces one of `V` by conjugation. -/
noncomputable def conjEndRingHom (e : V ≃ₗ[ℂ] W) :
    Module.End ℂ W →+* Module.End ℂ V where
  toFun T := e.symm.toLinearMap ∘ₗ T ∘ₗ e.toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.one_apply]
    exact e.symm_apply_apply v
  map_mul' T S := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.End.mul_apply,
      LinearEquiv.apply_symm_apply]
  map_zero' := by
    apply LinearMap.ext
    intro v
    simp
  map_add' T S := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply]
    rw [map_add]

/-- Transport a ring hom `R → End(W)` across a linear equivalence `V ≃ₗ W`. -/
noncomputable def transportRingHom {R : Type*} [Semiring R]
    (e : V ≃ₗ[ℂ] W) (ρ : R →+* Module.End ℂ W) :
    R →+* Module.End ℂ V :=
  (conjEndRingHom e).comp ρ

end Transport

/-! ### Prime Hecke generators -/

/-- The abstract `Γ₀(N)` Hecke-algebra element attached to the prime double coset
`D_p_Gamma0`. -/
noncomputable def primeHeckeElement (p : ℕ) (hp : Nat.Prime p) :
    𝕋 (Gamma0_pair N) ℤ :=
  T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp.pos) 1

/-- Any ring hom out of the `Γ₀(N)` Hecke algebra sends prime generators to
commuting endomorphisms because the source ring is commutative. -/
theorem primeHeckeElement_commute_of_ringHom
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ V)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Commute (ρ (primeHeckeElement p hp))
      (ρ (primeHeckeElement q hq)) := by
  show ρ (primeHeckeElement p hp) * ρ (primeHeckeElement q hq) =
      ρ (primeHeckeElement q hq) * ρ (primeHeckeElement p hp)
  rw [← map_mul, ← map_mul, Gamma0_pair_HeckeAlgebra_mul_comm]

/-- Pointwise form of `primeHeckeElement_commute_of_ringHom`. -/
theorem primeHeckeElement_commute_apply_of_ringHom
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : 𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ V)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (v : V) :
    ρ (primeHeckeElement p hp) (ρ (primeHeckeElement q hq) v) =
      ρ (primeHeckeElement q hq) (ρ (primeHeckeElement p hp) v) := by
  exact LinearMap.congr_fun
    (primeHeckeElement_commute_of_ringHom ρ hp hq).eq v

/-! ### The trivial-character experimental `Γ₀(N)` route -/

/-- The experimental `Γ₀(N), χ = 1` space is linearly equivalent to the actual
`Γ₀(N)` modular-form space. -/
noncomputable def gamma0NebentypusOneEquivGamma0 (k : ℤ) :
    gamma0NebentypusSubmodule (N := N) k (1 : (ZMod N)ˣ →* ℂˣ) ≃ₗ[ℂ]
      ModularForm ((Gamma0 N).map (mapGL ℝ)) k :=
  (modFormCharSpace_equiv_gamma0Nebentypus (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)).symm.trans
    (modFormCharSpace_one_equiv_Gamma0 N k)

/-- Transport the genuine `Γ₀(N)` Hecke ring hom to the experimental
`Γ₀(N), χ = 1` space. This is the actual ring-based proof source currently
available inside the unified layer. -/
noncomputable def gamma0NebentypusOneRingHom (k : ℤ) :
    𝕋 (Gamma0_pair N) ℤ →+* Module.End ℂ
      (gamma0NebentypusSubmodule (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)) :=
  transportRingHom (gamma0NebentypusOneEquivGamma0 (N := N) k)
    (heckeRingHom_Gamma0 N k)

/-- On the experimental `Γ₀(N), χ = 1` space, prime-generator Hecke operators
commute because they come from the commutative `Γ₀(N)` Hecke ring. -/
theorem gamma0NebentypusOne_prime_commute_from_ring
    (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Commute
      (gamma0NebentypusOneRingHom (N := N) k (primeHeckeElement p hp))
      (gamma0NebentypusOneRingHom (N := N) k (primeHeckeElement q hq)) :=
  primeHeckeElement_commute_of_ringHom (gamma0NebentypusOneRingHom (N := N) k)
    hp hq

/-- Pointwise version of `gamma0NebentypusOne_prime_commute_from_ring`. -/
theorem gamma0NebentypusOne_prime_commute_apply_from_ring
    (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (f : gamma0NebentypusSubmodule (N := N) k (1 : (ZMod N)ˣ →* ℂˣ)) :
    gamma0NebentypusOneRingHom (N := N) k (primeHeckeElement p hp)
        (gamma0NebentypusOneRingHom (N := N) k (primeHeckeElement q hq) f) =
      gamma0NebentypusOneRingHom (N := N) k (primeHeckeElement q hq)
        (gamma0NebentypusOneRingHom (N := N) k (primeHeckeElement p hp) f) := by
  exact LinearMap.congr_fun
    (gamma0NebentypusOne_prime_commute_from_ring (N := N) k hp hq).eq f

/-! ### Ring-based prime commutativity for the experimental `Γ₀(N)` family -/

/-- Pointwise prime commutativity on the transported experimental `Γ₀(N)` family,
with proof source the commutativity of `𝕋 (Gamma0_pair N) ℤ`. -/
theorem gamma0TrivialFamily_prime_commute_apply_from_ring
    (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    (gamma0TrivialFamily (N := N) k).op ⟨p, hp.pos, hpN⟩
        ((gamma0TrivialFamily (N := N) k).op ⟨q, hq.pos, hqN⟩ f) =
      (gamma0TrivialFamily (N := N) k).op ⟨q, hq.pos, hqN⟩
        ((gamma0TrivialFamily (N := N) k).op ⟨p, hp.pos, hpN⟩ f) := by
  rw [gamma0TrivialFamily_prime_eq_heckeOperator_Gamma0 (N := N) k hp hpN,
    gamma0TrivialFamily_prime_eq_heckeOperator_Gamma0 (N := N) k hq hqN,
    gamma0TrivialFamily_prime_eq_heckeOperator_Gamma0 (N := N) k hq hqN,
    gamma0TrivialFamily_prime_eq_heckeOperator_Gamma0 (N := N) k hp hpN]
  simpa [primeHeckeElement] using
    (primeHeckeElement_commute_apply_of_ringHom (N := N)
      (ρ := heckeRingHom_Gamma0 N k) hp hq f)

/-- Prime operators in the transported experimental `Γ₀(N)` family commute
because they are the images of commuting Hecke-ring generators. -/
theorem gamma0TrivialFamily_prime_commute_from_ring
    (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) :
    Commute
      ((gamma0TrivialFamily (N := N) k).op ⟨p, hp.pos, hpN⟩)
      ((gamma0TrivialFamily (N := N) k).op ⟨q, hq.pos, hqN⟩) := by
  show
    (gamma0TrivialFamily (N := N) k).op ⟨p, hp.pos, hpN⟩ *
      (gamma0TrivialFamily (N := N) k).op ⟨q, hq.pos, hqN⟩ =
    (gamma0TrivialFamily (N := N) k).op ⟨q, hq.pos, hqN⟩ *
      (gamma0TrivialFamily (N := N) k).op ⟨p, hp.pos, hpN⟩
  ext f z
  simp only [Module.End.mul_apply]
  exact congrArg (fun g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k ↦ g z)
    (gamma0TrivialFamily_prime_commute_apply_from_ring (N := N) k hp hq hpN hqN f)

/-- The level-1 specialization of the ring-based prime commutativity theorem. -/
theorem levelOneFamily_prime_commute_from_ring
    (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) :
    Commute
      ((levelOneFamily k).op ⟨p, hp.pos, by simpa using Nat.coprime_one_right p⟩)
      ((levelOneFamily k).op ⟨q, hq.pos, by simpa using Nat.coprime_one_right q⟩) := by
  simpa [levelOneFamily] using
    (gamma0TrivialFamily_prime_commute_from_ring (N := 1) k hp hq
      (by simpa using Nat.coprime_one_right p)
      (by simpa using Nat.coprime_one_right q))

/-! ### Interface point

Theorems above isolate the exact remaining gap for the general-`χ` route:

* once one has a ring hom
  `𝕋 (Gamma0_pair N) ℤ →+* End(Γ₀(N), χ-space)`,
  `primeHeckeElement_commute_of_ringHom` gives prime commutativity immediately;
* the current codebase supplies that ring hom only for `χ = 1`, so the unified
  proof source is presently real only in the trivial-character branch.
-/

end HeckeRing.GL2.Unified
