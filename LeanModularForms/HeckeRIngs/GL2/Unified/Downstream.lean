 /-
 Copyright (c) 2026. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: LeanModularForms contributors
 -/
import LeanModularForms.HeckeRIngs.GL2.Unified.Adjoint
import LeanModularForms.Eigenforms.AtkinLehner
import LeanModularForms.HeckeRIngs.GL2.Newforms

/-!
# Downstream bridges from the experimental `Γ₀(N), χ` spaces

This file exposes the existing Atkin–Lehner, newform, and strong multiplicity
one results through the experimental `Γ₀(N), χ`-style spaces. Nothing new is
proved mathematically here: each theorem is a transport wrapper from the
current `Γ₁(N)` character-space API to the isolated experimental submodules.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

/-- The prime-power Atkin–Lehner main lemma, restated for the experimental
`Γ₀(p^r), χ` cusp space. -/
theorem mainLemma_gamma0Nebentypus_primePower
    {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 0 < r) {k : ℤ}
    (χ : DirichletCharacter ℂ (p ^ r))
    (f : CuspForm ((Gamma1 (p ^ r)).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspGamma0NebentypusSubmodule (N := p ^ r) k χ.toUnitHom)
    (h : ∀ n : ℕ, Nat.Coprime n (p ^ r) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld (p ^ r) k := by
  exact HeckeRing.GL2.AtkinLehner.mainLemma_charSpace_primePower hr χ f
    ((mem_cuspFormCharSpace_iff_mem_cuspGamma0NebentypusSubmodule
      (N := p ^ r) k χ.toUnitHom f).mpr hfχ) h

/-- The decomposition-based Atkin–Lehner main lemma, restated for the
experimental `Γ₀(N), χ` cusp space. -/
theorem mainLemma_gamma0Nebentypus_of_prime_decomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors)
    (f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_decomp : f = ∑ p ∈ S, f_p p)
    (h_char : ∀ p ∈ S, f_p p ∈ cuspGamma0NebentypusSubmodule (N := N) k χ.toUnitHom)
    (h_supp : ∀ p ∈ S,
      f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p) :
    f ∈ cuspFormsOld N k := by
  exact HeckeRing.GL2.AtkinLehner.mainLemma_charSpace_of_prime_decomposition χ f S hS f_p
    h_decomp
    (fun p hp =>
      (mem_cuspFormCharSpace_iff_mem_cuspGamma0NebentypusSubmodule
        (N := N) k χ.toUnitHom (f_p p)).mpr (h_char p hp))
    h_supp

/-- The full-prime-factor Atkin–Lehner main lemma, restated for the
experimental `Γ₀(N), χ` cusp space. -/
theorem mainLemma_gamma0Nebentypus_of_primeFactors_decomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_decomp : f = ∑ p ∈ N.primeFactors, f_p p)
    (h_char : ∀ p ∈ N.primeFactors, f_p p ∈
      cuspGamma0NebentypusSubmodule (N := N) k χ.toUnitHom)
    (h_supp : ∀ p ∈ N.primeFactors,
      f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p) :
    f ∈ cuspFormsOld N k := by
  exact HeckeRing.GL2.AtkinLehner.mainLemma_charSpace_of_primeFactors_decomposition χ f f_p
    h_decomp
    (fun p hp =>
      (mem_cuspFormCharSpace_iff_mem_cuspGamma0NebentypusSubmodule
        (N := N) k χ.toUnitHom (f_p p)).mpr (h_char p hp))
    h_supp

/-- Atkin–Lehner uniqueness, restated using the experimental `Γ₀(N), χ`
modular-form subspace. -/
theorem newform_unique_of_gamma0Nebentypus
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ gamma0NebentypusSubmodule (N := N) k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ gamma0NebentypusSubmodule (N := N) k χ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  exact newform_unique f g χ
    ((mem_modFormCharSpace_iff_mem_gamma0NebentypusSubmodule
      (N := N) k χ f.toCuspForm.toModularForm').mpr hfχ)
    ((mem_modFormCharSpace_iff_mem_gamma0NebentypusSubmodule
      (N := N) k χ g.toCuspForm.toModularForm').mpr hgχ)
    h

namespace Newform

/-- Coprime multiplicativity of newform eigenvalues, restated using the
experimental `Γ₀(N), χ` modular-form subspace. -/
theorem eigenvalue_coprime_mul_of_gamma0Nebentypus
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) (m n : ℕ+)
    (hm : Nat.Coprime m.val N) (hn : Nat.Coprime n.val N)
    (hmn : Nat.Coprime m.val n.val) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ gamma0NebentypusSubmodule (N := N) k χ) :
    f.eigenvalue ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩ =
      f.eigenvalue m * f.eigenvalue n := by
  exact f.eigenvalue_coprime_mul m n hm hn hmn χ
    ((mem_modFormCharSpace_iff_mem_gamma0NebentypusSubmodule
      (N := N) k χ f.toCuspForm.toModularForm').mpr hfχ)

end Newform

/-- Strong multiplicity one, restated using the experimental `Γ₀(N), χ`
modular-form subspace. -/
theorem strongMultiplicityOne_of_gamma0Nebentypus
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ gamma0NebentypusSubmodule (N := N) k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ gamma0NebentypusSubmodule (N := N) k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  exact strongMultiplicityOne f g χ
    ((mem_modFormCharSpace_iff_mem_gamma0NebentypusSubmodule
      (N := N) k χ f.toCuspForm.toModularForm').mpr hfχ)
    ((mem_modFormCharSpace_iff_mem_gamma0NebentypusSubmodule
      (N := N) k χ g.toCuspForm.toModularForm').mpr hgχ)
    S h

end HeckeRing.GL2.Unified
