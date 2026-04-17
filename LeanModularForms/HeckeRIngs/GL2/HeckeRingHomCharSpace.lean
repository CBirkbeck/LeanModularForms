/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_CharSpace_Comm

/-!
# Hecke operators restricted to `modFormCharSpace k χ`

This file packages the action of `heckeT_p_all k p hp` (for `p` prime, arbitrary `χ`)
as an endomorphism of the character eigenspace `modFormCharSpace k χ`. It also
provides the pairwise commutativity of these restricted operators, giving a
clean, ring-hom-style package for the Hecke action on each character component.

For `p` coprime to `N`, preservation of `modFormCharSpace k χ` follows from
`heckeT_p_preserves_modFormCharSpace`. For `p ∣ N`, we first prove that the
upper-triangular Hecke operator `heckeT_p_divN` commutes with diamond operators
(using `heckeT_p_ut_orbit_comm_gamma0`), and then deduce preservation of the
character eigenspace.

## Main definitions

* `heckeT_p_all_comm_diamondOp_divN` — for `p ∣ N`, `heckeT_p_all k p hp` commutes
  with every diamond operator `⟨d⟩`.
* `heckeT_p_all_comm_diamondOp` — unified diamond commutation for all primes `p`.
* `heckeT_p_all_preserves_modFormCharSpace` — `heckeT_p_all k p hp` preserves any
  `modFormCharSpace k χ`, unconditionally on `p` and `χ`.
* `heckeT_p_all_charRestrict` — `heckeT_p_all k p hp` as an endomorphism of
  `modFormCharSpace k χ`.
* `heckeT_n_charRestrict` — `heckeT_n k n` (for `n` coprime to `N`) restricted
  to `modFormCharSpace k χ`.

## Main results

* `heckeT_p_all_charRestrict_commute_distinct` — for distinct primes `p ≠ q`,
  `heckeT_p_all_charRestrict k p χ` and `heckeT_p_all_charRestrict k q χ`
  commute (as a direct corollary of `heckeT_p_all_comm_distinct`).
* `heckeT_n_charRestrict_commute` — for any `m, n` coprime to `N`, the
  restrictions commute (as a direct corollary of `heckeT_n_comm`).

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-! ### Commutation of `heckeT_p_divN` with diamond operators

For `p ∣ N`, the Hecke operator is purely the upper-triangular sum
`heckeT_p_ut k p hp.pos (⇑f)`. The diamond operator `⟨d⟩` is implemented by
`diamondOpAux k σ` for some `σ ∈ Γ₀(N)` with `Gamma0MapUnits σ = d`. Since
`heckeT_p_ut` commutes with the `Γ₀(N)` slash action (by
`heckeT_p_ut_orbit_comm_gamma0_fun`), these commute. -/

/-- For `p ∣ N`, the operator `heckeT_p_all k p hp` commutes with every diamond
operator `⟨d⟩`. This is the `p ∣ N` analogue of `heckeT_p_comm_diamondOp`. -/
theorem heckeT_p_all_comm_diamondOp_divN (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : ¬Nat.Coprime p N) (d : (ZMod N)ˣ) :
    (diamondOp k d).comp (heckeT_p_all k p hp) =
    (heckeT_p_all k p hp).comp (diamondOp k d) := by
  obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective (N := N) d
  ext f z
  show (diamondOp k d (heckeT_p_all k p hp f)) z =
    (heckeT_p_all k p hp (diamondOp k d f)) z
  rw [diamondOp_eq_diamondOpAux k d g hg]
  -- LHS: diamondOpAux k g (heckeT_p_all k p hp f) = ⇑(heckeT_p_all k p hp f) ∣[k] mapGL ℝ g.
  -- When p ∣ N, heckeT_p_all k p hp unfolds to `heckeT_p_divN k p hp hpN`, whose
  -- coercion is `heckeT_p_ut k p hp.pos (⇑f)`.
  show (⇑(heckeT_p_all k p hp f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z =
    ⇑(heckeT_p_all k p hp (diamondOpAux k g f)) z
  rw [heckeT_p_all_not_coprime_apply k hp hpN f,
    heckeT_p_all_not_coprime_apply k hp hpN (diamondOpAux k g f)]
  -- Now: (heckeT_p_ut k p hp.pos (⇑f)) ∣[k] mapGL ℝ g = heckeT_p_ut k p hp.pos (⇑(diamondOpAux k g f))
  -- The RHS is exactly `heckeT_p_ut_orbit_comm_gamma0_fun` applied at z.
  exact congr_fun (heckeT_p_ut_orbit_comm_gamma0_fun k p hp hpN f g) z

/-- Unified diamond commutation for `heckeT_p_all`, covering both the coprime and
non-coprime cases. -/
theorem heckeT_p_all_comm_diamondOp (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (d : (ZMod N)ˣ) :
    (diamondOp k d).comp (heckeT_p_all k p hp) =
    (heckeT_p_all k p hp).comp (diamondOp k d) := by
  by_cases hpN : Nat.Coprime p N
  · rw [heckeT_p_all_coprime k hp hpN]
    exact heckeT_p_comm_diamondOp k p hp hpN d
  · exact heckeT_p_all_comm_diamondOp_divN k p hp hpN d

/-! ### Preservation of `modFormCharSpace k χ` -/

/-- `heckeT_p_all k p hp` preserves the modular-form character space
`M_k(Γ₁(N), χ)`, unconditionally on `p` and `χ`. -/
theorem heckeT_p_all_preserves_modFormCharSpace (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeT_p_all k p hp f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff] at hf ⊢
  intro d
  have h_comm := heckeT_p_all_comm_diamondOp k p hp d
  have h1 : diamondOpHom k d (heckeT_p_all k p hp f) =
      heckeT_p_all k p hp (diamondOpHom k d f) := by
    show (diamondOp k d).comp (heckeT_p_all k p hp) f =
      (heckeT_p_all k p hp).comp (diamondOp k d) f
    rw [h_comm]
  rw [h1, hf d, map_smul]

/-! ### Restriction to the character eigenspace: `heckeT_p_all_charRestrict` -/

/-- `heckeT_p_all k p hp` restricted to `modFormCharSpace k χ` as a `ℂ`-linear
endomorphism. -/
noncomputable def heckeT_p_all_charRestrict (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_p_all_preserves_modFormCharSpace k p hp χ f.property⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    show heckeT_p_all k p hp ((f₁ + f₂ :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeT_p_all k p hp (f₁ : ModularForm _ k) +
        heckeT_p_all k p hp (f₂ : ModularForm _ k)
    rw [show ((f₁ + f₂ : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (f₁ : ModularForm _ k) + (f₂ : ModularForm _ k) from rfl, map_add]
  map_smul' c f := by
    apply Subtype.ext
    show heckeT_p_all k p hp
        ((c • f : modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • heckeT_p_all k p hp (f : ModularForm _ k)
    rw [show ((c • f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (f : ModularForm _ k) from rfl, map_smul]

@[simp] lemma heckeT_p_all_charRestrict_coe (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_p_all_charRestrict k p hp χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-! ### Pairwise commutativity on `modFormCharSpace k χ` -/

/-- **Commutativity of restricted Hecke operators**: for distinct primes `p ≠ q`,
the restricted operators `heckeT_p_all_charRestrict k p χ` and
`heckeT_p_all_charRestrict k q χ` commute. This is an immediate corollary of the
global `heckeT_p_all_comm_distinct`. -/
theorem heckeT_p_all_charRestrict_commute_distinct (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) :
    Commute (heckeT_p_all_charRestrict k p hp χ)
      (heckeT_p_all_charRestrict k q hq χ) := by
  show heckeT_p_all_charRestrict k p hp χ * heckeT_p_all_charRestrict k q hq χ =
    heckeT_p_all_charRestrict k q hq χ * heckeT_p_all_charRestrict k p hp χ
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  simp only [Module.End.mul_apply, heckeT_p_all_charRestrict_coe]
  have h := heckeT_p_all_comm_distinct (N := N) k hp hq hpq
  have := congr_fun (congr_arg DFunLike.coe h) (f : ModularForm _ k)
  simpa [Module.End.mul_apply] using this

/-! ### Restriction of `heckeT_n` to `modFormCharSpace k χ`

For `n` coprime to `N`, the Hecke operator `heckeT_n k n` preserves
`modFormCharSpace k χ` (`heckeT_n_preserves_charSpace`). The restriction is a
`ℂ`-linear endomorphism. -/

/-- `heckeT_n k n` (for `n` coprime to `N`) restricted to `modFormCharSpace k χ`
as a `ℂ`-linear endomorphism. -/
noncomputable def heckeT_n_charRestrict (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_n_preserves_charSpace k n hn χ f.property⟩
  map_add' f₁ f₂ := by
    apply Subtype.ext
    show heckeT_n k n ((f₁ + f₂ :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      heckeT_n k n (f₁ : ModularForm _ k) + heckeT_n k n (f₂ : ModularForm _ k)
    rw [show ((f₁ + f₂ : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (f₁ : ModularForm _ k) + (f₂ : ModularForm _ k) from rfl, map_add]
  map_smul' c f := by
    apply Subtype.ext
    show heckeT_n k n
        ((c • f : modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • heckeT_n k n (f : ModularForm _ k)
    rw [show ((c • f : modFormCharSpace k χ) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      c • (f : ModularForm _ k) from rfl, map_smul]

@[simp] lemma heckeT_n_charRestrict_coe (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_n_charRestrict k n hn χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- **Commutativity of `heckeT_n` restrictions**: for any `m, n` coprime to `N`,
`heckeT_n_charRestrict k m hm χ` and `heckeT_n_charRestrict k n hn χ` commute.
This is an immediate corollary of `heckeT_n_comm`. -/
theorem heckeT_n_charRestrict_commute (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) :
    Commute (heckeT_n_charRestrict k m hm χ) (heckeT_n_charRestrict k n hn χ) := by
  show heckeT_n_charRestrict k m hm χ * heckeT_n_charRestrict k n hn χ =
    heckeT_n_charRestrict k n hn χ * heckeT_n_charRestrict k m hm χ
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  simp only [Module.End.mul_apply, heckeT_n_charRestrict_coe]
  have h := heckeT_n_comm (N := N) k m n
  have := congr_fun (congr_arg DFunLike.coe h) (f : ModularForm _ k)
  simpa [Module.End.mul_apply] using this

/-! ### Cleaner proof of `heckeT_p_all_comm_on_charSpace` via the restricted operators -/

/-- **Clean restatement of commutativity on `modFormCharSpace k χ`**: for distinct
primes `p ≠ q`, the operators `heckeT_p_all k p hp` and `heckeT_p_all k q hq` commute
pointwise on the eigenspace `modFormCharSpace k χ`.

This version uses the restriction `heckeT_p_all_charRestrict` explicitly, making
the ring-hom-style structure visible (cf. `heckeRingHomCharSpaceOne` for χ=1). -/
theorem heckeT_p_all_comm_on_charSpace_via_charRestrict (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ)
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (f : modFormCharSpace k χ) :
    heckeT_p_all k p hp (heckeT_p_all k q hq
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
    heckeT_p_all k q hq (heckeT_p_all k p hp
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have hcomm := heckeT_p_all_charRestrict_commute_distinct k χ hp hq hpq
  have h := congr_fun (congr_arg DFunLike.coe hcomm) f
  simp only [Module.End.mul_apply] at h
  have := congr_arg (Subtype.val (α := _) (p := _)) h
  simpa using this

/-! ### Full commutativity via `heckeT_n_charRestrict` (coprime case)

For `n, m` coprime to `N`, `heckeT_n_charRestrict` gives a clean commutativity
result on `modFormCharSpace k χ`, valid for ALL `m, n` (not just distinct primes).
This captures the full "Hecke algebra commutativity for the coprime part" on each
character eigenspace. -/

/-- For `m, n` coprime to `N` and any `χ`, the operators `heckeT_n k m` and
`heckeT_n k n` commute pointwise on `modFormCharSpace k χ`. -/
theorem heckeT_n_comm_on_charSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m n : ℕ) [NeZero m] [NeZero n]
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N)
    (f : modFormCharSpace k χ) :
    heckeT_n k m (heckeT_n k n
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
    heckeT_n k n (heckeT_n k m
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  have hcomm := heckeT_n_charRestrict_commute k χ m n hm hn
  have h := congr_fun (congr_arg DFunLike.coe hcomm) f
  simp only [Module.End.mul_apply] at h
  have := congr_arg (Subtype.val (α := _) (p := _)) h
  simpa using this

/-! ### Summary: ring-hom-style package on `modFormCharSpace k χ`

For any `χ : (ZMod N)ˣ →* ℂˣ`:
* `heckeT_p_all_charRestrict k p hp χ` is an endomorphism of `modFormCharSpace k χ`.
* `heckeT_n_charRestrict k n hn χ` (for `n` coprime to `N`) likewise.
* These commute pairwise (`heckeT_p_all_charRestrict_commute_distinct` and
  `heckeT_n_charRestrict_commute`).

For `χ = 1`, a true ring homomorphism
`heckeRingHomCharSpaceOne k : 𝕋 (Gamma0_pair N) ℤ →+* End ℂ (modFormCharSpace k 1)`
exists (see `HeckeT_p_CharSpace_Comm.lean`), obtained by transporting
`heckeRingHom_Gamma0 N k` through the canonical isomorphism
`modFormCharSpace_one_equiv_Gamma0`. For `χ ≠ 1`, the analogous construction would
require a nebentypus-twisted generalization of
`heckeSlash_gen_slash_invariant` (proving that `heckeSlash_gen (Gamma0_pair N) k D`
preserves `modFormCharSpace k χ` for ALL `D`, not just `D_p_Gamma0 N p`): this is
left for future work. -/

end HeckeRing.GL2
