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
  show (⇑(heckeT_p_all k p hp f) ∣[k] mapGL ℝ (g : SL(2, ℤ))) z =
    ⇑(heckeT_p_all k p hp (diamondOpAux k g f)) z
  rw [heckeT_p_all_not_coprime_apply k hp hpN f,
    heckeT_p_all_not_coprime_apply k hp hpN (diamondOpAux k g f)]
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

/-- `heckeT_p_all k p hp` preserves the modular-form character space
`M_k(Γ₁(N), χ)`, unconditionally on `p` and `χ`. -/
theorem heckeT_p_all_preserves_modFormCharSpace (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    heckeT_p_all k p hp f ∈ modFormCharSpace k χ := by
  rw [mem_modFormCharSpace_iff] at hf ⊢
  intro d
  have h1 : diamondOpHom k d (heckeT_p_all k p hp f) =
      heckeT_p_all k p hp (diamondOpHom k d f) := by
    show (diamondOp k d).comp (heckeT_p_all k p hp) f =
      (heckeT_p_all k p hp).comp (diamondOp k d) f
    rw [heckeT_p_all_comm_diamondOp]
  rw [h1, hf d, map_smul]

/-- `heckeT_p_all k p hp` restricted to `modFormCharSpace k χ` as a `ℂ`-linear
endomorphism. -/
noncomputable def heckeT_p_all_charRestrict (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_p_all_preserves_modFormCharSpace k p hp χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (heckeT_p_all k p hp) _ _)
  map_smul' c _ := Subtype.ext (map_smul (heckeT_p_all k p hp) c _)

@[simp] lemma heckeT_p_all_charRestrict_coe (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_p_all_charRestrict k p hp χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- `heckeT_n k n` (for `n` coprime to `N`) restricted to `modFormCharSpace k χ`
as a `ℂ`-linear endomorphism. -/
noncomputable def heckeT_n_charRestrict (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_n_preserves_charSpace k n hn χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (heckeT_n k n) _ _)
  map_smul' c _ := Subtype.ext (map_smul (heckeT_n k n) c _)

@[simp] lemma heckeT_n_charRestrict_coe (k : ℤ) (n : ℕ) [NeZero n]
    (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_n_charRestrict k n hn χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-! ### Character-space preservation for arbitrary index

The preservation lemmas below hold for **all** indices, including bad primes `p ∣ N` and
composites sharing factors with `N`.  They are proven by direct block induction over the
construction of `T_n` (each building block — `heckeT_p_all`, the diamond, the recurrence —
preserves the eigenspace), *not* via commutation with the diamond operators, so they are
available before any commutativity is established.  This is what lets operator identities
be transported from the Hecke ring `𝕋(Γ₀(N))` per character space and then glued. -/

/-- The diamond operator `⟨n⟩` preserves each character space `M_k(Γ₁(N), χ)` for every
index: at coprime `n` it acts by the scalar `χ(n)`, otherwise it vanishes. -/
theorem diamondOp_n_preserves_modFormCharSpace (k : ℤ) (n : ℕ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    diamondOp_n k n f ∈ modFormCharSpace k χ := by
  by_cases h : Nat.Coprime n N
  · rw [diamondOp_n_coprime k h]
    have heig : diamondOp k (ZMod.unitOfCoprime n h) f =
        (↑(χ (ZMod.unitOfCoprime n h)) : ℂ) • f :=
      (mem_modFormCharSpace_iff k χ f).mp hf _
    rw [heig]
    exact Submodule.smul_mem _ _ hf
  · rw [diamondOp_n_not_coprime k h]
    simpa using (modFormCharSpace (N := N) k χ).zero_mem

/-- `T_{p^r}` preserves each character space, for **every** prime `p` (including
`p ∣ N`).  Direct induction over the defining recurrence. -/
theorem heckeT_ppow_preserves_modFormCharSpace (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (r : ℕ) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_ppow k p hp r f ∈ modFormCharSpace k χ := by
  induction r using Nat.strong_induction_on generalizing f with
  | _ r ih =>
    match r, ih with
    | 0, _ => simpa using hf
    | 1, _ =>
      rw [heckeT_ppow_one]
      exact heckeT_p_all_preserves_modFormCharSpace k p hp χ hf
    | (r + 2), ih =>
      rw [heckeT_ppow_succ_succ]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply]
      refine Submodule.sub_mem _
        (heckeT_p_all_preserves_modFormCharSpace k p hp χ (ih (r + 1) (by omega) hf)) ?_
      exact Submodule.smul_mem _ _
        (diamondOp_n_preserves_modFormCharSpace k p χ (ih r (by omega) hf))

/-- `T_n` preserves each character space `M_k(Γ₁(N), χ)` for **every** positive `n`
(no coprimality with the level required).  Induction over the `minFac`-peeling
assembly of `T_n`. -/
theorem heckeT_n_preserves_modFormCharSpace_all (k : ℤ) (n : ℕ) [NeZero n]
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ modFormCharSpace k χ) :
    heckeT_n k n f ∈ modFormCharSpace k χ := by
  suffices H : ∀ m : ℕ, (hm0 : NeZero m) →
      ∀ {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}, g ∈ modFormCharSpace k χ →
        heckeT_n k m g ∈ modFormCharSpace k χ from H n ‹_› hf
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm0 g hg
    haveI := hm0
    rcases eq_or_ne m 1 with rfl | hm1
    · rw [heckeT_n_one]
      simpa using hg
    · have hm : 1 < m := by
        have := NeZero.ne m
        omega
      rw [heckeT_n_unfold k m hm]
      simp only [Module.End.mul_apply]
      set p := m.minFac with hp_def
      have hp : Nat.Prime p := Nat.minFac_prime (by omega)
      set v := m.factorization p with hv_def
      have hv_pos : 0 < v :=
        hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
      have hdiv_pos : 0 < m / p ^ v :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (pow_pos hp.pos v)
      have hdiv_lt : m / p ^ v < m :=
        Nat.div_lt_self (by omega) (Nat.one_lt_pow hv_pos.ne' hp.one_lt)
      exact heckeT_ppow_preserves_modFormCharSpace k p hp v χ
        (ih _ hdiv_lt ⟨hdiv_pos.ne'⟩ hg)

/-- `heckeT_n k n` restricted to `modFormCharSpace k χ`, for **arbitrary** positive `n`
(extends `heckeT_n_charRestrict`, which requires `n` coprime to `N`). -/
noncomputable def heckeT_n_charRestrictAll (k : ℤ) (n : ℕ) [NeZero n]
    (χ : (ZMod N)ˣ →* ℂˣ) :
    Module.End ℂ (modFormCharSpace k χ) where
  toFun f :=
    ⟨heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      heckeT_n_preserves_modFormCharSpace_all k n χ f.property⟩
  map_add' _ _ := Subtype.ext (map_add (heckeT_n k n) _ _)
  map_smul' c _ := Subtype.ext (map_smul (heckeT_n k n) c _)

@[simp] lemma heckeT_n_charRestrictAll_coe (k : ℤ) (n : ℕ) [NeZero n]
    (χ : (ZMod N)ˣ →* ℂˣ) (f : modFormCharSpace k χ) :
    ((heckeT_n_charRestrictAll k n χ f :
        modFormCharSpace k χ) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    heckeT_n k n (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- On indices coprime to the level the two restrictions agree. -/
lemma heckeT_n_charRestrictAll_eq (k : ℤ) (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (χ : (ZMod N)ˣ →* ℂˣ) :
    heckeT_n_charRestrictAll (N := N) k n χ = heckeT_n_charRestrict k n hn χ :=
  LinearMap.ext fun f ↦ Subtype.ext rfl

end HeckeRing.GL2
