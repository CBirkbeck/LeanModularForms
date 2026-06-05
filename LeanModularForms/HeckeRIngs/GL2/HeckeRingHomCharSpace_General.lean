/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace
import LeanModularForms.HeckeRIngs.GL2.Unified.RingTransport

/-!
# Multiplicative structure of `heckeT_n_charRestrict` on `modFormCharSpace k χ`

For any Nebentypus character `χ : (ZMod N)ˣ →* ℂˣ`, the restricted Hecke
operators `heckeT_n_charRestrict k n hn χ` (for `n` coprime to `N`) assemble into
a coprime-multiplicative family of commuting endomorphisms of `modFormCharSpace k χ`.

This file packages the existing results

* `heckeT_n_mul_coprime` — `T_{mn} = T_m T_n` when `Nat.Coprime m n`
* `heckeT_n_one` — `T_1 = 1`
* `heckeT_n_comm` — `T_m T_n = T_n T_m`

into a clean "coprime multiplicative" structure on `Module.End ℂ (modFormCharSpace k χ)`.

## Main definitions and results

* `heckeT_n_charRestrict_one` — the restricted `T_1` is the identity.
* `heckeT_n_charRestrict_mul_coprime` — `T_{mn}|_χ = T_m|_χ · T_n|_χ`
  when `Nat.Coprime m n` (both coprime to `N`).
* `heckeCoprimeMonoidHom_CharSpace` — the multiplicative monoid
  `{n : ℕ // 0 < n ∧ Nat.Coprime n N}` (with mul = coprime product) assembles
  (on coprime pairs) into commuting operators.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4, §3.5.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- The restricted `T_1` is the identity on `modFormCharSpace k χ`. -/
@[simp] lemma heckeT_n_charRestrict_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    heckeT_n_charRestrict k 1 (Nat.coprime_one_left N) χ = 1 :=
  LinearMap.ext fun f ↦ Subtype.ext <| by
    show heckeT_n k 1 (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ((1 : Module.End ℂ (modFormCharSpace k χ)) f :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    rw [heckeT_n_one, Module.End.one_apply, Module.End.one_apply]

/-- For coprime `m, n` (both coprime to `N`), the restricted operators satisfy
`T_{mn}|_χ = T_m|_χ · T_n|_χ`, matching the classical coprime multiplicativity
of the Hecke operators. -/
theorem heckeT_n_charRestrict_mul_coprime (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {m n : ℕ} [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) (hmn : Nat.Coprime m n) :
    haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
    heckeT_n_charRestrict k (m * n) (Nat.Coprime.mul_left hm hn) χ =
      heckeT_n_charRestrict k m hm χ * heckeT_n_charRestrict k n hn χ := by
  haveI : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  refine LinearMap.ext fun f ↦ Subtype.ext ?_
  show heckeT_n k (m * n) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    ((heckeT_n_charRestrict k m hm χ * heckeT_n_charRestrict k n hn χ) f :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
  rw [heckeT_n_mul_coprime k m n hmn hm hn]; rfl

/-- The submonoid of ℕ of positive naturals coprime to `N`.
Closed under multiplication because `Nat.Coprime.mul_left`. -/
def coprimeToN (N : ℕ) : Submonoid ℕ where
  carrier := {n | 0 < n ∧ Nat.Coprime n N}
  mul_mem' ha hb :=
    ⟨Nat.mul_pos ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨Nat.one_pos, Nat.coprime_one_left N⟩

@[simp] lemma mem_coprimeToN {N n : ℕ} :
    n ∈ coprimeToN N ↔ 0 < n ∧ Nat.Coprime n N := Iff.rfl

/-- `heckeT_n` restricted to `modFormCharSpace k χ`, indexed by elements of
`coprimeToN N`. Wraps `heckeT_n_charRestrict` with the positivity→`NeZero` bridge. -/
noncomputable def heckeT_coprimeRestrict (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (n : coprimeToN N) :
    Module.End ℂ (modFormCharSpace k χ) :=
  haveI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  heckeT_n_charRestrict k (n : ℕ) n.property.2 χ

@[simp] lemma heckeT_coprimeRestrict_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    heckeT_coprimeRestrict k χ 1 = 1 :=
  heckeT_n_charRestrict_one k χ

/-- Coprime-multiplicativity of `heckeT_coprimeRestrict`: for `m, n ∈ coprimeToN N`
with `Nat.Coprime m.1 n.1`, `T_{m * n} = T_m · T_n`. -/
theorem heckeT_coprimeRestrict_mul_coprime (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : coprimeToN N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    heckeT_coprimeRestrict k χ (m * n) =
      heckeT_coprimeRestrict k χ m * heckeT_coprimeRestrict k χ n := by
  haveI : NeZero (m : ℕ) := ⟨Nat.pos_iff_ne_zero.mp m.property.1⟩
  haveI : NeZero (n : ℕ) := ⟨Nat.pos_iff_ne_zero.mp n.property.1⟩
  haveI : NeZero ((m : ℕ) * n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (m : ℕ)) (NeZero.ne (n : ℕ))⟩
  exact heckeT_n_charRestrict_mul_coprime k χ m.property.2 n.property.2 hmn

end HeckeRing.GL2
