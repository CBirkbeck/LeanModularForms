/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanModularForms.HeckeRIngs.GLn.DiagonalRepresentatives
import LeanModularForms.HeckeRIngs.GLn.SLnTransvection
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication

/-!
# Block Embedding Bijection: abstract `HeckePair` lemmas

Stabilizer invariance, conjugation equivalence on `decompQuot`s, and coset
helpers for an abstract `HeckePair`. Foundation layer of the block-embedding
bijection split (Shimura §3.2, Lemma 3.19).
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing

/-! ### Stabilizer subgroup invariance -/

section StabilizerInvariance

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Right multiplication by `h ∈ H` does not change the stabilizer subgroup:
`Stab(g·h) = Stab(g)` when `h ∈ H`, because `(g·h)H(g·h)⁻¹ = g(hHh⁻¹)g⁻¹ = gHg⁻¹`. -/
lemma stabilizerSubgroup_mul_right_H (g : P.Δ) (h : P.H) :
    (ConjAct.toConjAct ((g : G) * (h : G)) • P.H).subgroupOf P.H =
    (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx
    have key : (g : G)⁻¹ * (x : G) * g =
        (h : G) * (((g : G) * (h : G))⁻¹ * (x : G) * ((g : G) * (h : G))) * (h : G)⁻¹ := by
      group
    rw [key]; exact P.H.mul_mem (P.H.mul_mem h.2 hx) (P.H.inv_mem h.2)
  · intro hx
    have key : ((g : G) * (h : G))⁻¹ * (x : G) * ((g : G) * (h : G)) =
        (h : G)⁻¹ * ((g : G)⁻¹ * (x : G) * (g : G)) * (h : G) := by group
    rw [key]; exact P.H.mul_mem (P.H.mul_mem (P.H.inv_mem h.2) hx) h.2

/-- Left multiplication by `h ∈ H` conjugates the stabilizer:
`Stab(h·g) = conj(h)(Stab(g))` as subgroups of `H`.
Concretely, `x ∈ Stab(h·g)` iff `h⁻¹·x·h ∈ Stab(g)`. -/
lemma stab_mul_left_eq_map_conj (g : P.Δ) (h : P.H) :
    (ConjAct.toConjAct ((h : G) * (g : G)) • P.H).subgroupOf P.H =
    ((ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H).map
      (MulAut.conj h).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨⟨(h : G)⁻¹ * (x : G) * (h : G),
      P.H.mul_mem (P.H.mul_mem (P.H.inv_mem h.2) x.2) h.2⟩, ?_, ?_⟩
    · show (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * (g : G) ∈ P.H
      rw [show (g : G)⁻¹ * ((h : G)⁻¹ * (x : G) * (h : G)) * (g : G) =
        ((h : G) * (g : G))⁻¹ * (x : G) * ((h : G) * (g : G)) from by
        rw [_root_.mul_inv_rev]; simp [mul_assoc]]
      exact hx
    · ext; show (h : G) * ((h : G)⁻¹ * (x : G) * (h : G)) * (h : G)⁻¹ = (x : G)
      simp [mul_assoc]
  · rintro ⟨y, hy, rfl⟩
    show ((h : G) * (g : G))⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) * ((h : G) * (g : G)) ∈ P.H
    rw [show ((h : G) * (g : G))⁻¹ * ((h : G) * (y : G) * (h : G)⁻¹) * ((h : G) * (g : G)) =
      (g : G)⁻¹ * (y : G) * (g : G) from by
      rw [_root_.mul_inv_rev]; simp [mul_assoc]]
    exact hy

end StabilizerInvariance

/-! ### Conjugation equivalence on decompQuots -/

section ConjugationEquiv

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Conjugation by `h ∈ H` gives an Equiv on decomposition quotients:
`H/Stab(h·g) ≃ H/Stab(g)` via `σ ↦ h⁻¹·σ·h`.

The well-definedness uses `Stab(h·g) = h·Stab(g)·h⁻¹`, which means
`σ₁ ~_{Stab(h·g)} σ₂` iff `h⁻¹·σ₁·h ~_{Stab(g)} h⁻¹·σ₂·h`. -/
noncomputable def decompQuot_mul_left_equiv (g : P.Δ) (h : P.H)
    (hm : (h : G) * (g : G) ∈ P.Δ) :
    decompQuot P ⟨(h : G) * g, hm⟩ ≃ decompQuot P g := by
  set K := (ConjAct.toConjAct (g : G) • P.H).subgroupOf P.H
  set K' := K.map (MulAut.conj h).toMonoidHom
  refine (Subgroup.quotientEquivOfEq (stab_mul_left_eq_map_conj P g h)).trans ?_
  have h_wd : ∀ a b : P.H, QuotientGroup.leftRel K' a b →
      QuotientGroup.leftRel K ((MulAut.conj h⁻¹) a) ((MulAut.conj h⁻¹) b) := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [show ((MulAut.conj h⁻¹) a)⁻¹ * (MulAut.conj h⁻¹) b =
      (MulAut.conj h⁻¹) (a⁻¹ * b) by simp [map_inv, map_mul]]
    rw [Subgroup.mem_map] at hab; obtain ⟨k, hk, hkeq⟩ := hab
    show (MulAut.conj h⁻¹) (a⁻¹ * b) ∈ K
    have : a⁻¹ * b = (MulAut.conj h) k := hkeq.symm
    rw [this]; convert hk using 1; ext; simp [MulAut.conj_apply, mul_assoc]
  exact Equiv.ofBijective
    (Quotient.map' (MulAut.conj h⁻¹) h_wd)
    ⟨fun x y hxy ↦ by
      revert x y; exact Quotient.ind₂ fun a b hxy ↦ by
        simp only [Quotient.map'_mk''] at hxy
        rw [Quotient.eq''] at hxy ⊢
        rw [QuotientGroup.leftRel_apply] at hxy ⊢
        rw [show ((MulAut.conj h⁻¹) a)⁻¹ * (MulAut.conj h⁻¹) b =
          (MulAut.conj h⁻¹) (a⁻¹ * b) by simp [map_inv, map_mul]] at hxy
        rw [Subgroup.mem_map]
        exact ⟨(MulAut.conj h⁻¹) (a⁻¹ * b), hxy, by
          ext; simp [MulAut.conj_apply, mul_assoc]⟩,
    fun x ↦ by
      revert x; exact Quotient.ind fun b ↦ ⟨Quotient.mk'' ((MulAut.conj h) b), by
        simp only [Quotient.map'_mk'']; rw [Quotient.eq'', QuotientGroup.leftRel_apply]
        rw [show ((MulAut.conj h⁻¹) ((MulAut.conj h) b))⁻¹ * b =
          1 by ext; simp [MulAut.conj_apply, mul_assoc]]
        exact K.one_mem⟩⟩

/-- Combined left-right invariance: `decompQuot(h·g·k) ≃ decompQuot(g)` for `h, k ∈ H`.
Composes right-invariance (stabilizer equality) with left-conjugation. -/
noncomputable def decompQuot_double_H_equiv (g : P.Δ) (h k : P.H)
    (hm : (h : G) * (g : G) * (k : G) ∈ P.Δ) :
    decompQuot P ⟨(h : G) * (g : G) * (k : G), hm⟩ ≃ decompQuot P g := by
  have hgk : (g : G) * (k : G) ∈ P.Δ := P.Δ.mul_mem g.2 (P.h₀ k.2)
  have hhgk : (h : G) * ((g : G) * (k : G)) ∈ P.Δ := by rwa [mul_assoc] at hm
  refine (Subgroup.quotientEquivOfEq ?_).trans
    ((decompQuot_mul_left_equiv P ⟨(g : G) * k, hgk⟩ h hhgk).trans
    (Subgroup.quotientEquivOfEq (stabilizerSubgroup_mul_right_H P g k)))
  show (ConjAct.toConjAct ((h : G) * (g : G) * (k : G)) • P.H).subgroupOf P.H =
    (ConjAct.toConjAct ((h : G) * ((g : G) * (k : G))) • P.H).subgroupOf P.H
  congr 2; exact mul_assoc _ _ _

end ConjugationEquiv

/-! ### Coset manipulation helpers -/

section CosetHelpers

variable {G : Type*} [Group G] (P : HeckePair G)

/-- Right-multiplying by an H-element doesn't change the right coset `{a} * H`. -/
lemma singleton_mul_H_absorb_right (a c : G) (hc : c ∈ P.H) :
    ({a * c} : Set G) * (P.H : Set G) = ({a} : Set G) * (P.H : Set G) := by
  ext x; constructor
  · rintro ⟨_, rfl, k, hk, rfl⟩; exact ⟨_, rfl, c * k, P.H.mul_mem hc hk, by group⟩
  · rintro ⟨_, rfl, k, hk, rfl⟩
    exact ⟨_, rfl, c⁻¹ * k, P.H.mul_mem (P.H.inv_mem hc) hk, by group⟩

/-- If two `H`-elements are in the same `decompQuot` class for `g`, they give the same
left coset `{σ * g} * H`. -/
lemma decompQuot_coset_indep' (g : P.Δ)
    (x y : P.H) (hxy : (⟦x⟧ : decompQuot P g) = ⟦y⟧) :
    ({(x : G) * (g : G)} : Set G) * (P.H : Set G) =
    {(y : G) * (g : G)} * (P.H : Set G) := by
  rw [Quotient.eq''] at hxy
  change (QuotientGroup.leftRel _) x y at hxy
  rw [QuotientGroup.leftRel_apply] at hxy
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at hxy
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, Subgroup.coe_mul, Subgroup.coe_inv,
    inv_inv] at hxy
  have hxy' : (g : G)⁻¹ * (x : G)⁻¹ * (y : G) * (g : G) ∈ P.H := by
    convert hxy using 1; group
  ext z; simp only [Set.singleton_mul, Set.image_mul_left, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · intro hz
    show ((y : G) * (g : G))⁻¹ * z ∈ P.H
    have key : ((y : G) * (g : G))⁻¹ * z =
        ((g : G)⁻¹ * (x : G)⁻¹ * (y : G) * (g : G))⁻¹ *
        (((x : G) * (g : G))⁻¹ * z) := by group
    rw [key]; exact P.H.mul_mem (P.H.inv_mem hxy') hz
  · intro hz
    show ((x : G) * (g : G))⁻¹ * z ∈ P.H
    have key : ((x : G) * (g : G))⁻¹ * z =
        ((g : G)⁻¹ * (x : G)⁻¹ * (y : G) * (g : G)) *
        (((y : G) * (g : G))⁻¹ * z) := by group
    rw [key]; exact P.H.mul_mem hxy' hz

/-- The `out` representative of a quotient element gives the same coset as the original. -/
lemma decompQuot_out_coset_eq' (g : P.Δ) (x : P.H) :
    ({((⟦x⟧ : decompQuot P g).out : G) * (g : G)} : Set G) * (P.H : Set G) =
    {(x : G) * (g : G)} * (P.H : Set G) :=
  decompQuot_coset_indep' P g (⟦x⟧ : decompQuot P g).out x (Quotient.out_eq _)

end CosetHelpers

end HeckeRing
