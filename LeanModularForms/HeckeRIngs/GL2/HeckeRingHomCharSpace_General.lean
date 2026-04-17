/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeRingHomCharSpace

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

Because the multiplicative structure `T_m T_n = T_{mn}` requires `Nat.Coprime m n`,
we do not get a global monoid homomorphism `ℕ →* End`; instead, the composition of
coprime operators factors through the underlying `T_n` operation. This matches the
classical statement of Shimura / Diamond–Shurman: the Hecke algebra has a
multiplicative structure on coprime indices, assembled via the abstract formal
Dirichlet convolution.

## Relationship to `heckeRingHomCharSpaceOne`

For the trivial character `χ = 1`, a full ring homomorphism
`heckeRingHomCharSpaceOne k : 𝕋(Gamma0_pair N) ℤ →+* End ℂ (modFormCharSpace k 1)`
exists (see `HeckeT_p_CharSpace_Comm.lean`). For non-trivial `χ`, a full ring hom
from `𝕋(Gamma0_pair N) ℤ` would require showing that `heckeSlash_gen (Gamma0_pair N) k D`
preserves `modFormCharSpace k χ` for every double coset `D`, which is a delicate
nebentypus-twisted refinement of `heckeSlash_gen_slash_invariant`. The coprime-case
machinery in this file gives a clean, well-defined multiplicative structure on the
part of the Hecke algebra directly reachable from `heckeT_n` (coprime-to-`N`
operators), covering the main case of interest for the classical theory.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4, §3.5.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ### Identity and multiplicativity for `heckeT_n_charRestrict` -/

/-- The restricted `T_1` is the identity on `modFormCharSpace k χ`. -/
@[simp] lemma heckeT_n_charRestrict_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    heckeT_n_charRestrict k 1 (Nat.coprime_one_left N) χ = 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
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
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  show heckeT_n k (m * n) (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    ((heckeT_n_charRestrict k m hm χ * heckeT_n_charRestrict k n hn χ) f :
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
  rw [heckeT_n_mul_coprime k m n hmn]
  rfl

/-! ### Coercion simp lemma: subtype coercion is strict `heckeT_n` -/

/-- Applying `heckeT_n_charRestrict k n hn χ * heckeT_n_charRestrict k m hm χ` and
coercing back to the ambient `ModularForm` space gives `heckeT_n k n (heckeT_n k m ...)`. -/
lemma heckeT_n_charRestrict_mul_coe (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N)
    (f : modFormCharSpace k χ) :
    ((heckeT_n_charRestrict k m hm χ * heckeT_n_charRestrict k n hn χ) f :
        modFormCharSpace k χ) =
      ⟨heckeT_n k m (heckeT_n k n (f : ModularForm _ k)),
        heckeT_n_preserves_charSpace k m hm χ
          (heckeT_n_preserves_charSpace k n hn χ f.property)⟩ := by
  apply Subtype.ext
  rw [show (heckeT_n_charRestrict k m hm χ * heckeT_n_charRestrict k n hn χ) f =
      heckeT_n_charRestrict k m hm χ (heckeT_n_charRestrict k n hn χ f) from rfl]
  simp only [heckeT_n_charRestrict_coe]

/-! ### Pointwise commutativity of `T_m T_n` and `T_n T_m` on charSpace

`heckeT_n_charRestrict_commute` (in `HeckeRingHomCharSpace.lean`) gives the abstract
commutativity in `Module.End`. Here we record the pointwise version, which is the form
most useful when reasoning about how `T_m T_n f` and `T_n T_m f` relate inside
`modFormCharSpace k χ`. -/

/-- Pointwise commutativity: `T_m T_n f = T_n T_m f` on `modFormCharSpace k χ`. -/
theorem heckeT_n_charRestrict_commute_apply (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N)
    (f : modFormCharSpace k χ) :
    heckeT_n_charRestrict k m hm χ (heckeT_n_charRestrict k n hn χ f) =
    heckeT_n_charRestrict k n hn χ (heckeT_n_charRestrict k m hm χ f) := by
  have h := heckeT_n_charRestrict_commute k χ m n hm hn
  have := congr_fun (congr_arg DFunLike.coe h) f
  simpa [Module.End.mul_apply] using this

/-! ### Coprime multiplicativity: a chain-rule form

The multiplicativity `T_{mn} = T_m T_n` at coprime pairs propagates through any
finite product of pairwise coprime factors (all coprime to `N`). We state a clean
two-step and three-step version suitable for applications. -/

/-- Three-way coprime multiplicativity:
`T_{mnr}|_χ = T_m|_χ · T_n|_χ · T_r|_χ` for pairwise coprime `m, n, r` all coprime to `N`. -/
theorem heckeT_n_charRestrict_mul_coprime_three (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    {m n r : ℕ} [NeZero m] [NeZero n] [NeZero r]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) (hr : Nat.Coprime r N)
    (hmn : Nat.Coprime m n) (hmr : Nat.Coprime m r) (hnr : Nat.Coprime n r) :
    haveI : NeZero (n * r) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne r)⟩
    haveI : NeZero (m * (n * r)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne m)
        (Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne r))⟩
    heckeT_n_charRestrict k (m * (n * r))
        (Nat.Coprime.mul_left hm (Nat.Coprime.mul_left hn hr)) χ =
      heckeT_n_charRestrict k m hm χ *
        (heckeT_n_charRestrict k n hn χ *
          heckeT_n_charRestrict k r hr χ) := by
  haveI : NeZero (n * r) := ⟨Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne r)⟩
  have hm_nr : Nat.Coprime m (n * r) := Nat.Coprime.mul_right hmn hmr
  have hnr_N : Nat.Coprime (n * r) N := Nat.Coprime.mul_left hn hr
  have key1 := heckeT_n_charRestrict_mul_coprime k χ hm hnr_N hm_nr
  have key2 := heckeT_n_charRestrict_mul_coprime k χ hn hr hnr
  rw [key1, key2]

/-! ### Ring-hom view (restricted subring)

On the trivial-character eigenspace (`χ = 1`), a full ring hom
`heckeRingHomCharSpaceOne` from the abstract Hecke ring exists (via the iso to
`M_k(Γ₀(N))`). For general `χ`, we record the coprime-submonoid image directly.

The monoid `coprimeNats N := {n : ℕ // 0 < n ∧ Nat.Coprime n N}` (with multiplication
the ℕ product on representatives when the product is also coprime to `N`) is the
natural target for the Hecke operators obtainable from `heckeT_n`. Because
`N.Coprime mn` iff `N.Coprime m ∧ N.Coprime n`, this is closed under ℕ-multiplication. -/

/-- The submonoid of ℕ of positive naturals coprime to `N`.
Closed under multiplication because `Nat.Coprime.mul_left`. -/
def coprimeToN (N : ℕ) : Submonoid ℕ where
  carrier := {n | 0 < n ∧ Nat.Coprime n N}
  mul_mem' ha hb :=
    ⟨Nat.mul_pos ha.1 hb.1, Nat.Coprime.mul_left ha.2 hb.2⟩
  one_mem' := ⟨Nat.one_pos, Nat.coprime_one_left N⟩

@[simp] lemma mem_coprimeToN {N n : ℕ} :
    n ∈ coprimeToN N ↔ 0 < n ∧ Nat.Coprime n N := Iff.rfl

/-! ### Well-defined restricted operator indexed by `coprimeToN N`

Given `⟨n, hn_pos, hn⟩ : coprimeToN N`, we obtain the endomorphism
`heckeT_n_charRestrict k n hn χ`, using `hn_pos` to provide the `NeZero n` instance. -/

/-- `heckeT_n` restricted to `modFormCharSpace k χ`, indexed by elements of
`coprimeToN N`. Wraps `heckeT_n_charRestrict` with the positivity→`NeZero` bridge. -/
noncomputable def heckeT_coprimeRestrict (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (n : coprimeToN N) :
    Module.End ℂ (modFormCharSpace k χ) :=
  haveI : NeZero (n : ℕ) := ⟨(Nat.pos_iff_ne_zero.mp n.property.1)⟩
  heckeT_n_charRestrict k (n : ℕ) n.property.2 χ

@[simp] lemma heckeT_coprimeRestrict_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    heckeT_coprimeRestrict k χ 1 = 1 := by
  show heckeT_n_charRestrict k 1 _ χ = 1
  exact heckeT_n_charRestrict_one k χ

/-- Coprime-multiplicativity of `heckeT_coprimeRestrict`: for `m, n ∈ coprimeToN N`
with `Nat.Coprime m.1 n.1`, `T_{m * n} = T_m · T_n`. -/
theorem heckeT_coprimeRestrict_mul_coprime (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : coprimeToN N) (hmn : Nat.Coprime (m : ℕ) (n : ℕ)) :
    heckeT_coprimeRestrict k χ (m * n) =
      heckeT_coprimeRestrict k χ m * heckeT_coprimeRestrict k χ n := by
  haveI hmz : NeZero (m : ℕ) := ⟨(Nat.pos_iff_ne_zero.mp m.property.1)⟩
  haveI hnz : NeZero (n : ℕ) := ⟨(Nat.pos_iff_ne_zero.mp n.property.1)⟩
  haveI : NeZero ((m : ℕ) * n) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (m : ℕ)) (NeZero.ne (n : ℕ))⟩
  show heckeT_n_charRestrict k ((m * n : coprimeToN N) : ℕ) _ χ =
    heckeT_n_charRestrict k (m : ℕ) _ χ * heckeT_n_charRestrict k (n : ℕ) _ χ
  show heckeT_n_charRestrict k ((m : ℕ) * n) _ χ = _
  exact heckeT_n_charRestrict_mul_coprime k χ m.property.2 n.property.2 hmn

/-- Commutativity: `T_m · T_n = T_n · T_m` on `modFormCharSpace k χ`
for any `m, n ∈ coprimeToN N`. -/
theorem heckeT_coprimeRestrict_commute (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : coprimeToN N) :
    Commute (heckeT_coprimeRestrict k χ m) (heckeT_coprimeRestrict k χ n) := by
  haveI : NeZero (m : ℕ) := ⟨(Nat.pos_iff_ne_zero.mp m.property.1)⟩
  haveI : NeZero (n : ℕ) := ⟨(Nat.pos_iff_ne_zero.mp n.property.1)⟩
  show heckeT_n_charRestrict k (m : ℕ) _ χ * heckeT_n_charRestrict k (n : ℕ) _ χ =
    heckeT_n_charRestrict k (n : ℕ) _ χ * heckeT_n_charRestrict k (m : ℕ) _ χ
  exact heckeT_n_charRestrict_commute k χ _ _ _ _

/-! ### Summary

For any Nebentypus character `χ : (ZMod N)ˣ →* ℂˣ` and any weight `k : ℤ`, the
restricted Hecke operators on `modFormCharSpace k χ` satisfy:

* `heckeT_coprimeRestrict k χ 1 = 1` (identity)
* `heckeT_coprimeRestrict k χ (m * n) = heckeT_coprimeRestrict k χ m *
    heckeT_coprimeRestrict k χ n` when `Nat.Coprime m n`
* All `heckeT_coprimeRestrict k χ m` commute with each other.

This captures the classical multiplicative structure `T_{mn} = T_m T_n` for coprime
`m, n` coprime to `N`, packaged as commuting endomorphisms of `modFormCharSpace k χ`.

The coprimality restriction reflects the classical identity
  `T_m T_n = Σ_{d | gcd(m,n)} d^{k-1} ⟨d⟩ T_{mn/d²}`
which reduces to `T_{mn}` exactly when `gcd(m, n) = 1`. -/

end HeckeRing.GL2
