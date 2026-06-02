/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Unified.CuspNebentypusSpace

/-!
# Ring-sourced coprime commutativity in the experimental unified layer

This file isolates the part of commutativity that already follows from the
abstract Hecke-ring multiplication table without using the later global
`heckeT_n_comm` induction.

The key source theorem is `heckeT_n_mul_coprime`, whose proof is explicitly
transported from the Hecke-ring identity `T_sum_mul_coprime`. For coprime
indices, commutativity is then immediate from

`T_{mn} = T_m T_n = T_n T_m = T_{nm}`.

We record that route on:

* the ambient `Γ₁(N)` modular-form space;
* the existing `Γ₁(N), χ` character spaces;
* the transported experimental `Γ₀(N), χ` modular-form space;
* the cusp-space analogues.

This does not yet solve the full non-coprime general-`χ` commutativity problem;
it isolates the part of the proof source that is already genuinely ring-based.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

private lemma prime_coprime_of_ne {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Nat.Coprime p q :=
  (Nat.coprime_primes hp hq).mpr hpq

/-- On the ambient `Γ₁(N)` modular-form space, the good-index operators satisfy
coprime multiplicativity via `heckeT_n_mul_coprime`. -/
theorem ambientHeckeOfGoodIndex_mul_of_coprime
    (k : ℤ) (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    ambientHeckeOfGoodIndex (N := N) k (m * n) =
      ambientHeckeOfGoodIndex (N := N) k m *
        ambientHeckeOfGoodIndex (N := N) k n := by
  letI : NeZero (m : ℕ) := ⟨Nat.pos_iff_ne_zero.mp m.property.1⟩
  letI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  letI : NeZero ((m : ℕ) * n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (m : ℕ)) (NeZero.ne (n : ℕ))⟩
  exact heckeT_n_mul_coprime (N := N) k (m : ℕ) (n : ℕ) hmn

/-- Coprime good-index operators on the ambient `Γ₁(N)` space commute by
`heckeT_n_mul_coprime`, without using `heckeT_n_comm`. -/
theorem ambientHeckeOfGoodIndex_commute_of_coprime
    (k : ℤ) (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    Commute (ambientHeckeOfGoodIndex (N := N) k m)
      (ambientHeckeOfGoodIndex (N := N) k n) := by
  rw [Commute, SemiconjBy,
    ← ambientHeckeOfGoodIndex_mul_of_coprime (N := N) k m n hmn,
    ← ambientHeckeOfGoodIndex_mul_of_coprime (N := N) k n m hmn.symm,
    show m * n = n * m from Subtype.ext (Nat.mul_comm (m : ℕ) (n : ℕ))]

/-- Pointwise form of `ambientHeckeOfGoodIndex_commute_of_coprime`. -/
theorem ambientHeckeOfGoodIndex_commute_apply_of_coprime
    (k : ℤ) (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ambientHeckeOfGoodIndex (N := N) k m
        (ambientHeckeOfGoodIndex (N := N) k n f) =
      ambientHeckeOfGoodIndex (N := N) k n
        (ambientHeckeOfGoodIndex (N := N) k m f) :=
  LinearMap.congr_fun
    (ambientHeckeOfGoodIndex_commute_of_coprime (N := N) k m n hmn).eq f

/-- Distinct good primes commute on the ambient `Γ₁(N)` space by the same
coprime-multiplicative route. -/
theorem ambientHeckeOfGoodIndex_prime_commute_from_mul
    (k : ℤ) {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) :
    Commute
      (ambientHeckeOfGoodIndex (N := N) k ⟨p, hp.pos, hpN⟩)
      (ambientHeckeOfGoodIndex (N := N) k ⟨q, hq.pos, hqN⟩) :=
  ambientHeckeOfGoodIndex_commute_of_coprime (N := N) k
    ⟨p, hp.pos, hpN⟩ ⟨q, hq.pos, hqN⟩
    (prime_coprime_of_ne hp hq hpq)

/-- On the existing `Γ₁(N), χ` character spaces, coprime good-index operators
already commute by multiplicativity alone. -/
theorem modFormCharSpaceFamily_commute_of_coprime_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    Commute
      ((modFormCharSpaceFamily (N := N) k χ).op m)
      ((modFormCharSpaceFamily (N := N) k χ).op n) :=
  (modFormCharSpaceFamily (N := N) k χ).commute_of_coprime_from_mul m n hmn

/-- Pointwise form of `modFormCharSpaceFamily_commute_of_coprime_from_mul`. -/
theorem modFormCharSpaceFamily_commute_apply_of_coprime_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ))
    (f : modFormCharSpace k χ) :
    (modFormCharSpaceFamily (N := N) k χ).op m
        ((modFormCharSpaceFamily (N := N) k χ).op n f) =
      (modFormCharSpaceFamily (N := N) k χ).op n
        ((modFormCharSpaceFamily (N := N) k χ).op m f) :=
  (modFormCharSpaceFamily (N := N) k χ).commute_apply_of_coprime_from_mul
    m n hmn f

/-- Distinct good primes commute on `modFormCharSpace k χ` by the coprime
multiplicative route. -/
theorem modFormCharSpaceFamily_prime_commute_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) :
    Commute
      ((modFormCharSpaceFamily (N := N) k χ).op ⟨p, hp.pos, hpN⟩)
      ((modFormCharSpaceFamily (N := N) k χ).op ⟨q, hq.pos, hqN⟩) :=
  modFormCharSpaceFamily_commute_of_coprime_from_mul (N := N) k χ
    ⟨p, hp.pos, hpN⟩ ⟨q, hq.pos, hqN⟩
    (prime_coprime_of_ne hp hq hpq)

/-- On the transported experimental `Γ₀(N), χ` modular-form space, coprime
good-index operators commute by the same multiplicative source theorem. -/
theorem gamma0NebentypusFamily_commute_of_coprime_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    Commute
      ((gamma0NebentypusFamily (N := N) k χ).op m)
      ((gamma0NebentypusFamily (N := N) k χ).op n) :=
  (gamma0NebentypusFamily (N := N) k χ).commute_of_coprime_from_mul m n hmn

/-- Pointwise form of `gamma0NebentypusFamily_commute_of_coprime_from_mul`. -/
theorem gamma0NebentypusFamily_commute_apply_of_coprime_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ))
    (f : gamma0NebentypusSubmodule (N := N) k χ) :
    (gamma0NebentypusFamily (N := N) k χ).op m
        ((gamma0NebentypusFamily (N := N) k χ).op n f) =
      (gamma0NebentypusFamily (N := N) k χ).op n
        ((gamma0NebentypusFamily (N := N) k χ).op m f) :=
  (gamma0NebentypusFamily (N := N) k χ).commute_apply_of_coprime_from_mul
    m n hmn f

/-- Distinct good primes commute on the transported experimental
`Γ₀(N), χ` modular-form space by coprime multiplicativity. -/
theorem gamma0NebentypusFamily_prime_commute_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N) :
    Commute
      ((gamma0NebentypusFamily (N := N) k χ).op ⟨p, hp.pos, hpN⟩)
      ((gamma0NebentypusFamily (N := N) k χ).op ⟨q, hq.pos, hqN⟩) :=
  gamma0NebentypusFamily_commute_of_coprime_from_mul (N := N) k χ
    ⟨p, hp.pos, hpN⟩ ⟨q, hq.pos, hqN⟩
    (prime_coprime_of_ne hp hq hpq)

/-- On `cuspFormCharSpace k χ`, coprime good-index operators commute from
coprime multiplicativity alone. -/
theorem cuspFormCharSpaceFamily_commute_of_coprime_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    Commute
      ((cuspFormCharSpaceFamily (N := N) k χ).op m)
      ((cuspFormCharSpaceFamily (N := N) k χ).op n) :=
  (cuspFormCharSpaceFamily (N := N) k χ).commute_of_coprime_from_mul m n hmn

/-- On the transported experimental `Γ₀(N), χ` cusp space, coprime good-index
operators commute from the same source theorem. -/
theorem cuspGamma0NebentypusFamily_commute_of_coprime_from_mul
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : GoodIndex N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    Commute
      ((cuspGamma0NebentypusFamily (N := N) k χ).op m)
      ((cuspGamma0NebentypusFamily (N := N) k χ).op n) :=
  (cuspGamma0NebentypusFamily (N := N) k χ).commute_of_coprime_from_mul m n hmn

end HeckeRing.GL2.Unified
