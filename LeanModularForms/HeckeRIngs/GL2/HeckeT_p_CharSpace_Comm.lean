/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma0_Bridge
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp

/-!
# Commutativity of `heckeT_p_all` on the Nebentypus character spaces

Using the trivial-character bridge `heckeT_p_val_eq_heckeOperator_Gamma0_on_charSpace_one`
from `HeckeT_p_Gamma0_Bridge.lean`, we obtain a clean, short proof that for any two
distinct primes `p, q` (both coprime to `N`), the operators `heckeT_p_all k p hp`
and `heckeT_p_all k q hq` commute when restricted to the trivial Nebentypus
eigenspace `modFormCharSpace k 1`. The proof reduces to commutativity of the abstract
Hecke ring `𝕋(Gamma0_pair N) ℤ` (Shimura Prop 3.8, via
`Gamma0_pair_HeckeAlgebra_mul_comm`).

For non-trivial characters (or non-coprime primes), the same commutativity
statement on each eigenspace `modFormCharSpace k χ` is a direct corollary of the
existing global commutativity theorem `heckeT_p_all_comm_distinct`.

## Main results

* `heckeT_p_all_eq_gamma0_on_charSpace_one` — the composition of `heckeT_p_all` with
  the trivial-character isomorphism factors through `heckeOperator_Gamma0`.
* `heckeT_p_all_comm_on_charSpace_one_coprime` — commutativity of `heckeT_p_all` on the
  trivial-character eigenspace for two primes coprime to `N`, proved via
  `Gamma0_pair_HeckeAlgebra_mul_comm`.
* `heckeT_p_all_comm_on_charSpace` — same commutativity on an arbitrary χ-eigenspace,
  as a corollary of the global theorem.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1.
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- On the trivial-character eigenspace, `heckeT_p_all k p hp` (coprime case) is
carried by the iso `modFormCharSpace_one_equiv_Gamma0` to the abstract Hecke operator
`heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)`. This is the Γ₀(N)-bridge made
operational: `heckeT_p_all` on `modFormCharSpace k 1` is conjugate to a Γ₀(N)-Hecke
operator. -/
theorem heckeT_p_all_eq_gamma0_on_charSpace_one (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeT_p_all k p hp (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
    ((modFormCharSpace_one_equiv_Gamma0 N k).symm
      (heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)
        (modFormCharSpace_one_equiv_Gamma0 N k f)) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  rw [heckeT_p_all_coprime k hp hpN]
  exact heckeT_p_val_eq_heckeOperator_Gamma0_on_charSpace_one k p hp hpN f

/-- `heckeT_p_all k p hp`, restricted to the trivial-character eigenspace, preserves
the eigenspace. For `p` coprime to `N`, this specialises
`heckeT_p_preserves_modFormCharSpace` to `χ = 1`. -/
lemma heckeT_p_all_preserves_charSpace_one_coprime (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeT_p_all k p hp f ∈ modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ) := by
  rw [heckeT_p_all_coprime k hp hpN]
  exact heckeT_p_preserves_modFormCharSpace k p hp hpN _ hf

/-- The two Γ₀(N)-Hecke operators `heckeOperator_Gamma0` for primes `p, q` commute
pointwise on `g`. This is the analytic shadow of commutativity of the abstract Hecke
ring `𝕋 (Gamma0_pair N) ℤ` (`Gamma0_pair_HeckeAlgebra_mul_comm`): both operators are
single-`T` images, so their composites agree by `heckeSum_Gamma0_mul`. -/
private lemma heckeOperator_Gamma0_comm_of_coprime (k : ℤ) {p q : ℕ}
    (hp : 0 < p) (hq : 0 < q) (g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k) :
    heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp)
      (heckeOperator_Gamma0 N k (D_p_Gamma0 N q hq) g) =
    heckeOperator_Gamma0 N k (D_p_Gamma0 N q hq)
      (heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp) g) := by
  have hpq_comm :
      heckeOperatorLinear_Gamma0 N k (D_p_Gamma0 N p hp) *
        heckeOperatorLinear_Gamma0 N k (D_p_Gamma0 N q hq) =
      heckeOperatorLinear_Gamma0 N k (D_p_Gamma0 N q hq) *
        heckeOperatorLinear_Gamma0 N k (D_p_Gamma0 N p hp) := by
    have hp_one : heckeOperatorLinear_Gamma0 N k (D_p_Gamma0 N p hp) =
        heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N p hp) 1) := by
      rw [heckeSum_Gamma0_T_single, one_smul]
    have hq_one : heckeOperatorLinear_Gamma0 N k (D_p_Gamma0 N q hq) =
        heckeSum_Gamma0 N k (T_single (Gamma0_pair N) ℤ (D_p_Gamma0 N q hq) 1) := by
      rw [heckeSum_Gamma0_T_single, one_smul]
    rw [hp_one, hq_one, ← heckeSum_Gamma0_mul, ← heckeSum_Gamma0_mul,
      Gamma0_pair_HeckeAlgebra_mul_comm]
  simpa [Module.End.mul_apply] using congr_fun (congr_arg DFunLike.coe hpq_comm) g

/-- On the trivial-character eigenspace, the iso `modFormCharSpace_one_equiv_Gamma0`
intertwines `heckeT_p_all k p hp` (for `p` coprime to `N`) with the Γ₀(N)-Hecke
operator `heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)`. -/
private lemma equiv_heckeT_p_all_eq_heckeOperator_Gamma0 (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ))
    (hpres : heckeT_p_all k p hp (f : ModularForm _ k) ∈
      modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    modFormCharSpace_one_equiv_Gamma0 N k
        ⟨heckeT_p_all k p hp (f : ModularForm _ k), hpres⟩ =
      heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)
        (modFormCharSpace_one_equiv_Gamma0 N k f) := by
  refine ModularForm.ext fun z ↦ ?_
  rw [modFormCharSpace_one_equiv_Gamma0_apply, Subtype.coe_mk,
    heckeT_p_all_eq_gamma0_on_charSpace_one k p hp hpN f,
    modFormCharSpace_one_equiv_Gamma0_symm_apply]

/-- Helper for `heckeT_p_all_comm_on_charSpace_one_coprime`: the composite
`heckeT_p_all k p hp (heckeT_p_all k q hq f)` on the trivial-character eigenspace
factors as a double `heckeOperator_Gamma0` on the Γ₀(N) side. -/
private lemma heckeT_p_all_comp_eq_gamma0_double (k : ℤ) {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ))
    (hf_pres_q : heckeT_p_all k q hq (f : ModularForm _ k) ∈
      modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeT_p_all k p hp (heckeT_p_all k q hq (f : ModularForm _ k)) =
    ((modFormCharSpace_one_equiv_Gamma0 N k).symm
      (heckeOperator_Gamma0 N k (D_p_Gamma0 N p hp.pos)
        (heckeOperator_Gamma0 N k (D_p_Gamma0 N q hq.pos)
          (modFormCharSpace_one_equiv_Gamma0 N k f))) :
        ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  have h_outer := heckeT_p_all_eq_gamma0_on_charSpace_one k p hp hpN
    ⟨heckeT_p_all k q hq (f : ModularForm _ k), hf_pres_q⟩
  rw [Subtype.coe_mk] at h_outer
  rw [h_outer, equiv_heckeT_p_all_eq_heckeOperator_Gamma0 k q hq hqN f hf_pres_q]

/-- On `modFormCharSpace k 1`, for two primes `p, q` both coprime to `N`,
`heckeT_p_all k p hp (heckeT_p_all k q hq f) = heckeT_p_all k q hq (heckeT_p_all k p hp f)`
— a direct corollary of `Gamma0_pair_HeckeAlgebra_mul_comm`. The proof goes through
the iso `modFormCharSpace_one_equiv_Gamma0`.

The main mathematical content: `heckeT_p_all` on the trivial-χ eigenspace *is* a
Γ₀(N)-Hecke operator (up to conjugation by `equiv`), and Γ₀(N) Hecke operators commute
by the abstract Hecke ring being commutative. -/
theorem heckeT_p_all_comm_on_charSpace_one_coprime (k : ℤ) {p q : ℕ} (hp : Nat.Prime p)
    (hq : Nat.Prime q) (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :
    heckeT_p_all k p hp (heckeT_p_all k q hq
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
    heckeT_p_all k q hq (heckeT_p_all k p hp
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  set g : ModularForm ((Gamma0 N).map (mapGL ℝ)) k := modFormCharSpace_one_equiv_Gamma0 N k f
  rw [heckeT_p_all_comp_eq_gamma0_double k hp hq hpN hqN f
      (heckeT_p_all_preserves_charSpace_one_coprime k q hq hqN f.property),
    heckeT_p_all_comp_eq_gamma0_double k hq hp hqN hpN f
      (heckeT_p_all_preserves_charSpace_one_coprime k p hp hpN f.property)]
  congr 2
  exact heckeOperator_Gamma0_comm_of_coprime k hp.pos hq.pos g

/-- **Commutativity on `modFormCharSpace k χ`**: for distinct primes `p, q` and any
character `χ`, the operators `heckeT_p_all k p hp` and `heckeT_p_all k q hq` commute
pointwise on the eigenspace `modFormCharSpace k χ`.

This is an immediate corollary of the global commutativity theorem
`heckeT_p_all_comm_distinct`. -/
theorem heckeT_p_all_comm_on_charSpace (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q) (f : modFormCharSpace k χ) :
    heckeT_p_all k p hp (heckeT_p_all k q hq
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) =
    heckeT_p_all k q hq (heckeT_p_all k p hp
      (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) := by
  simpa [Module.End.mul_apply] using congr_fun
    (congr_arg DFunLike.coe (heckeT_p_all_comm_distinct (N := N) k hp hq hpq))
    (f : ModularForm _ k)

/-- Conjugation of an endomorphism of `ModularForm ((Gamma0 N).map (mapGL ℝ)) k` by
the iso `modFormCharSpace_one_equiv_Gamma0`, yielding an endomorphism of
`modFormCharSpace k 1`. -/
noncomputable def conjEndCharSpaceOne (k : ℤ)
    (T : Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k)) :
    Module.End ℂ (modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :=
  (modFormCharSpace_one_equiv_Gamma0 N k).symm.toLinearMap ∘ₗ
    T ∘ₗ (modFormCharSpace_one_equiv_Gamma0 N k).toLinearMap

/-- Conjugation is a ring hom from `End(M_k(Γ₀(N)))` to `End(modFormCharSpace k 1)`. -/
noncomputable def conjEndRingHomCharSpaceOne (k : ℤ) :
    Module.End ℂ (ModularForm ((Gamma0 N).map (mapGL ℝ)) k) →+*
      Module.End ℂ (modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) where
  toFun := conjEndCharSpaceOne k
  map_one' := LinearMap.ext fun f ↦ by
    simp [conjEndCharSpaceOne, (modFormCharSpace_one_equiv_Gamma0 N k).symm_apply_apply]
  map_mul' T₁ T₂ := LinearMap.ext fun f ↦ by
    simp [conjEndCharSpaceOne, Module.End.mul_apply]
  map_zero' := LinearMap.ext fun f ↦ by simp [conjEndCharSpaceOne]
  map_add' T₁ T₂ := LinearMap.ext fun f ↦ by
    simp [conjEndCharSpaceOne, LinearMap.add_apply, map_add]

/-- The Hecke ring hom `𝕋(Gamma0_pair N) ℤ →+* End(modFormCharSpace k 1)` obtained
by conjugating `heckeRingHom_Gamma0` through `modFormCharSpace_one_equiv_Gamma0`.

Since the source is a commutative ring (`Gamma0_pair_HeckeAlgebra_mul_comm`), the
image commutes. In particular, `heckeT_p_all`s arising from `heckeRingHom_Gamma0`
on the trivial-character eigenspace commute. -/
noncomputable def heckeRingHomCharSpaceOne (k : ℤ) :
    𝕋 (Gamma0_pair N) ℤ →+*
      Module.End ℂ (modFormCharSpace k (1 : (ZMod N)ˣ →* ℂˣ)) :=
  (conjEndRingHomCharSpaceOne (N := N) k).comp (heckeRingHom_Gamma0 N k)

@[simp] lemma heckeRingHomCharSpaceOne_apply (k : ℤ) (T : 𝕋 (Gamma0_pair N) ℤ) :
    heckeRingHomCharSpaceOne (N := N) k T =
    conjEndCharSpaceOne (N := N) k (heckeRingHom_Gamma0 N k T) := rfl

/-- The image of `heckeRingHomCharSpaceOne` is commutative, because the source ring
`𝕋 (Gamma0_pair N) ℤ` is commutative. -/
lemma heckeRingHomCharSpaceOne_commute (k : ℤ) (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    Commute (heckeRingHomCharSpaceOne (N := N) k T₁) (heckeRingHomCharSpaceOne k T₂) := by
  show _ * _ = _ * _
  rw [← map_mul, ← map_mul, Gamma0_pair_HeckeAlgebra_mul_comm]

end HeckeRing.GL2
