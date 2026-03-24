/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic

/-!
# Hecke Rings: Multiplication

Shimura's multiplicity `heckeMultiplicity`, the multiplication finsupp `m`, the `Mul` instance
on `𝕋 P ℤ`,
and the `NonUnitalNonAssocSemiring` instance. Proves that `HeckeCoset.one` is the identity element.
-/

open Commensurable Classical MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G)

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

/-- The stabilizer quotient for the identity double coset is trivial. -/
lemma decompQuot_T_one_eq_top :
    (ConjAct.toConjAct ((HeckeCoset.one P).doubleCoset_eq.choose : G) • P.H).subgroupOf P.H =
    ⊤ := by
  have h := T_one_choose_mem_H P; rw [Subgroup.subgroupOf_eq_top]
  intro x hx; rw [← @SetLike.mem_coe]; simp only [Subgroup.coe_pointwise_smul]
  rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h,
    Subgroup.subgroup_mul_singleton (by simp [h])]; exact hx

/-- The decomposition quotient for `HeckeCoset.one` is nonempty. -/
lemma one_in_decompQuot_T_one : Nonempty (decompQuot P (HeckeCoset.one P)) :=
  ⟨(1 : P.H)⟩

/-- The decomposition quotient for `HeckeCoset.one` is a subsingleton. -/
lemma subsingleton_decompQuot_T_one :
    Subsingleton (decompQuot P (HeckeCoset.one P)) := by
  unfold decompQuot; rw [decompQuot_T_one_eq_top]
  exact QuotientGroup.subsingleton_quotient_top

private lemma self_mem_singleton_mul (a : G) : a ∈ {a} * (H : Set G) := by simp

private lemma conjAct_mem_of_leftCoset_eq (d : Δ) (h h' : H)
    (hyp : {(h : G)} * {(d : G)} * (H : Set G) =
      {(h' : G)} * {(d : G)} * (H : Set G)) :
    (h')⁻¹ * h ∈ (ConjAct.toConjAct (d : G) • H).subgroupOf H := by
  have h_mem_lhs : (h : G) * (d : G) ∈ {(h : G)} * {(d : G)} * (H : Set G) := by
    rw [Set.singleton_mul_singleton]
    exact ⟨(h : G) * (d : G), Set.mem_singleton _, 1, H.one_mem, by simp⟩
  rw [hyp, Set.singleton_mul_singleton] at h_mem_lhs
  obtain ⟨_, rfl, k, hk, hkk⟩ := h_mem_lhs
  have hkk' : ↑h' * ↑d * k = ↑h * ↑d := hkk
  have key : (h' : G)⁻¹ * (h : G) = (d : G) * k * (d : G)⁻¹ := by
    apply mul_right_cancel (b := (d : G))
    rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    apply mul_left_cancel (a := (h' : G))
    rw [mul_inv_cancel_left, ← mul_assoc]
    exact hkk'.symm
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, Subgroup.coe_mul,
    Subgroup.coe_inv]
  rw [inv_inv, key]
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]; exact hk

/-- Distinct elements of `decompQuot` give distinct left cosets. -/
lemma decompQuot_coset_diff (D : HeckeCoset P) (i j : decompQuot P D) (hij : i ≠ j) :
  {((i.out : G) * (D.doubleCoset_eq.choose : G))} * (P.H : Set G) ≠
    {((j.out : G) * (D.doubleCoset_eq.choose : G))} * (P.H : Set G) := by
  intro h
  simp_rw [← Set.singleton_mul_singleton] at h
  have := conjAct_mem_of_leftCoset_eq P.H P.Δ D.doubleCoset_eq.choose i.out j.out h
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at this
  simp only [Quotient.out_eq'] at this
  exact hij this.symm

/-- Two left cosets that are not disjoint must be equal. -/
lemma leftCoset_eq_of_not_disjoint (f g : G)
    (h : ¬ Disjoint (g • (H : Set G)) (f • H)) :
    {g} * (H : Set G) = {f} * H := by
  simp_rw [← Set.singleton_smul] at *; rw [@not_disjoint_iff] at h
  obtain ⟨a, ha, ha2⟩ := h
  simp only [smul_eq_mul, singleton_mul, image_mul_left, mem_preimage,
    SetLike.mem_coe] at ha ha2
  refine Set.ext ?intro.intro.h; intro Y
  simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe]
  simp_rw [← @QuotientGroup.eq] at *; rw [← ha] at ha2; rw [ha2]

private lemma singleton_mul_subset_mul (g : G) (T S : Set G) (h : g ∈ S) :
    {g} * T ⊆ S * T := mul_subset_mul_right (singleton_subset_iff.mpr h)

private lemma leftCoset_exists (D : HeckeCoset P) : ∃ (i : decompQuot P D),
  {(D.doubleCoset_eq.choose : G)} * (P.H : Set G) = {(i.out : G)} * {(D.doubleCoset_eq.choose : G)} * P.H := by
  have hc := D.doubleCoset_eq.choose_spec
  rw [DoubleCoset.doubleCoset_eq_iUnion_leftCosets] at hc
  have h1 : {(D.doubleCoset_eq.choose : G)} * (P.H : Set G) ⊆ D.carrier := by
    have v0 := D.doubleCoset_eq.choose_spec
    conv =>
      enter [2]
      rw [v0]
    intro i hi
    simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe] at *
    rw [mem_doubleCoset]
    use 1
    simp only [SetLike.mem_coe, one_mem, one_mul, true_and]
    use (D.doubleCoset_eq.choose : G)⁻¹ * i
    simp [hi]
  have hr := hc.le
  have h3 := le_trans h1 hr
  simp only [le_eq_subset] at h3
  have h4 : (D.doubleCoset_eq.choose : G) ∈ {(D.doubleCoset_eq.choose : G)} * (P.H : Set G) := by
    simp [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe]
  have h45 := h3 h4
  simp only [mem_iUnion] at h45
  obtain ⟨i, hi⟩ := h45
  use i
  rw [smul_eq_singleton_mul] at hi
  have h6 := singleton_mul_subset_mul _ P.H _ hi
  conv at h6 =>
    enter [2]
    rw [mul_assoc, coe_mul_coe]
  rw [Set.singleton_mul_singleton]
  apply leftCoset_eq_of_not_disjoint
  apply Set.Nonempty.not_disjoint
  simp_rw [smul_eq_singleton_mul]
  have := Set.inter_eq_self_of_subset_left h6
  have ht := nonempty_of_mem h4
  rw [← this] at ht
  convert ht

private lemma leftCoset_exists_unique (D : HeckeCoset P) : ∃! (i : decompQuot P D),
  {(D.doubleCoset_eq.choose : G)} * (P.H : Set G) = {(i.out : G) * (D.doubleCoset_eq.choose : G)} * P.H := by
  obtain ⟨i, hi⟩ := leftCoset_exists P D
  use i
  rw [Set.singleton_mul_singleton] at hi
  simp only [hi,true_and]
  intro j h
  by_contra c
  have := (decompQuot_coset_diff P D j i c).symm
  aesop

private lemma mul_mem_delta (a : H) (g : Δ)
    (h₀ : H.toSubmonoid ≤ Δ) :
    (a : G) * (g : G) ∈ Δ :=
  Submonoid.mul_mem _ (h₀ a.2) g.2

/-- The map sending a pair of coset representatives `(σ_i, τ_j)` to the double coset
of their product `H(σ_i τ_j)H`. -/
noncomputable def mulMap (D1 D2 : HeckeCoset P)
    (i : decompQuot P D1 × decompQuot P D2) : HeckeCoset P :=
  HeckeCoset.mk' P ⟨i.1.out * D1.doubleCoset_eq.choose * (i.2.out * D2.doubleCoset_eq.choose),
    Submonoid.mul_mem _ (mul_mem_delta P.H P.Δ i.1.out D1.doubleCoset_eq.choose P.h₀)
      (mul_mem_delta P.H P.Δ i.2.out D2.doubleCoset_eq.choose P.h₀)⟩

/-- Shimura's multiplicity (Proposition 3.2): `heckeMultiplicity(D1, D2, d)` counts pairs
`(i,j)` such that `σᵢ τⱼ H = ξ H`. -/
noncomputable def heckeMultiplicity (D1 D2 d : HeckeCoset P) : ℤ :=
  Nat.card {⟨i, j⟩ : decompQuot P D1 × decompQuot P D2 |
    ({(i.out : G) * (D1.doubleCoset_eq.choose : G)} : Set G) *
      {(j.out : G) * (D2.doubleCoset_eq.choose : G)} * P.H =
    {(d.doubleCoset_eq.choose : G)} * (P.H : Set G)}

/-- The finite set of double cosets appearing in the product `D1 * D2`. -/
noncomputable def mulSupport (D1 D2 : HeckeCoset P) : Finset (HeckeCoset P) :=
  Finset.image (mulMap P D1 D2) ⊤

/-- If `σ_i τ_j H = ξ H` then the double coset of `σ_i τ_j` equals
that of `ξ`. -/
lemma doubleCoset_eq_of_rightCoset_eq (D1 D2 d : HeckeCoset P)
    (p : decompQuot P D1 × decompQuot P D2)
    (heq : ({(p.1.out : G) * (D1.doubleCoset_eq.choose : G)} : Set G) *
      {(p.2.out : G) * (D2.doubleCoset_eq.choose : G)} * P.H =
      {(d.doubleCoset_eq.choose : G)} * (P.H : Set G)) :
    mulMap P D1 D2 p = d := by
  apply HeckeRing.HeckeCoset_ext P
  rw [mulMap, HeckeCoset.mk']
  simp only
  have h_mem : (p.1.out : G) * (D1.doubleCoset_eq.choose : G) * ((p.2.out : G) * (D2.doubleCoset_eq.choose : G))
      ∈ ({(d.doubleCoset_eq.choose : G)} : Set G) * (P.H : Set G) := by
    rw [← heq, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, P.H.one_mem, by simp⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_mem
  simp only [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  dsimp only at hprod ⊢
  rw [← hprod]
  conv_rhs => rw [d.doubleCoset_eq.choose_spec]
  exact DoubleCoset.doubleCoset_mul_right_eq_self P ⟨h, hh⟩ _

private lemma mulMap_T_one_eq (D1 : HeckeCoset P) (i : decompQuot P D1) (j : decompQuot P (HeckeCoset.one P)) :
    mulMap P D1 (HeckeCoset.one P) (i, j) = D1 := by
  unfold mulMap
  apply HeckeRing.HeckeCoset_ext P
  simp only [HeckeCoset.mk']
  have hD1 := D1.doubleCoset_eq.choose_spec
  conv => enter [2]; rw [hD1]
  rw [mul_assoc, doset_mul_left_eq_self]
  apply DoubleCoset.doubleCoset_mul_right_eq_self P ⟨j.out * (HeckeCoset.one P).doubleCoset_eq.choose, by
    apply Subgroup.mul_mem _ (by simp) (T_one_choose_mem_H P)⟩

/-- Left multiplication by a singleton set is cancellative. -/
lemma set_singleton_mul_left_cancel (a : G) {S T : Set G}
    (h : ({a} : Set G) * S = ({a} : Set G) * T) : S = T := by
  ext x; constructor
  · intro hx
    have hax : a * x ∈ ({a} : Set G) * T := by
      rw [← h]; exact Set.mul_mem_mul (Set.mem_singleton a) hx
    obtain ⟨b, hb, y, hy, heq⟩ := hax
    rw [Set.mem_singleton_iff.mp hb] at heq; exact mul_left_cancel heq ▸ hy
  · intro hx
    have hax : a * x ∈ ({a} : Set G) * S := by
      rw [h]; exact Set.mul_mem_mul (Set.mem_singleton a) hx
    obtain ⟨b, hb, y, hy, heq⟩ := hax
    rw [Set.mem_singleton_iff.mp hb] at heq; exact mul_left_cancel heq ▸ hy

/-- When the first-component representatives agree, the second-component
    representatives must also agree (by left-cancellation on the common prefix). -/
lemma decompQuot_snd_eq_of_fst_eq (D1 D2 d : HeckeCoset P)
    (i : decompQuot P D1) (j₁ j₂ : decompQuot P D2)
    (h₁ : ({(i.out : G) * (D1.doubleCoset_eq.choose : G)} : Set G) *
        {(j₁.out : G) * (D2.doubleCoset_eq.choose : G)} * P.H =
      {(d.doubleCoset_eq.choose : G)} * (P.H : Set G))
    (h₂ : ({(i.out : G) * (D1.doubleCoset_eq.choose : G)} : Set G) *
        {(j₂.out : G) * (D2.doubleCoset_eq.choose : G)} * P.H =
      {(d.doubleCoset_eq.choose : G)} * (P.H : Set G)) :
    j₁ = j₂ := by
  by_contra hne
  exact decompQuot_coset_diff P D2 j₁ j₂ hne
    (set_singleton_mul_left_cancel _ (by
      have := h₁.trans h₂.symm; rwa [mul_assoc, mul_assoc] at this))

/-- When `j.out * D2.choose ∈ H`, the second factor collapses and
    first-component injectivity follows from coset disjointness. -/
lemma decompQuot_fst_eq_of_snd_mem_H (D1 D2 d : HeckeCoset P)
    (i₁ i₂ : decompQuot P D1) (j : decompQuot P D2)
    (hj : (j.out : G) * (D2.doubleCoset_eq.choose : G) ∈ P.H)
    (h₁ : ({(i₁.out : G) * (D1.doubleCoset_eq.choose : G)} : Set G) *
        {(j.out : G) * (D2.doubleCoset_eq.choose : G)} * P.H =
      {(d.doubleCoset_eq.choose : G)} * (P.H : Set G))
    (h₂ : ({(i₂.out : G) * (D1.doubleCoset_eq.choose : G)} : Set G) *
        {(j.out : G) * (D2.doubleCoset_eq.choose : G)} * P.H =
      {(d.doubleCoset_eq.choose : G)} * (P.H : Set G)) :
    i₁ = i₂ := by
  by_contra hne; apply decompQuot_coset_diff P D1 i₁ i₂ hne
  simp only [mul_assoc, Subgroup.singleton_mul_subgroup hj] at h₁ h₂
  exact h₁.trans h₂.symm

/-- Right multiplication by `HeckeCoset.one` has multiplicity `1` on the diagonal and `0` elsewhere. -/
lemma heckeMultiplicity_mul_one (D1 d : HeckeCoset P) : D1 = d ↔ heckeMultiplicity P D1 (HeckeCoset.one P) d = 1 := by
  constructor
  · intro h; subst h
    simp only [heckeMultiplicity]; norm_cast; rw [Nat.card_eq_one_iff_unique]
    haveI : Subsingleton (decompQuot P (HeckeCoset.one P)) := subsingleton_decompQuot_T_one P
    refine ⟨⟨?_⟩, ?_⟩
    · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂; subst hj
      simp only [Set.mem_setOf_eq] at h₁ h₂
      exact Subtype.ext (Prod.ext
        (decompQuot_fst_eq_of_snd_mem_H P D1 (HeckeCoset.one P) D1 i₁ i₂ j₁
          (Subgroup.mul_mem _ (SetLike.coe_mem j₁.out) (T_one_choose_mem_H P)) h₁ h₂)
        rfl)
    · obtain ⟨i₀, hi₀⟩ := leftCoset_exists P D1
      obtain ⟨j₀⟩ := one_in_decompQuot_T_one P
      refine ⟨⟨(i₀, j₀), ?_⟩⟩
      simp only [Set.mem_setOf_eq]
      have hmem : (j₀.out : G) * ((HeckeCoset.one P).doubleCoset_eq.choose : G) ∈ P.H :=
        Subgroup.mul_mem _ (SetLike.coe_mem j₀.out) (T_one_choose_mem_H P)
      rw [mul_assoc, Subgroup.singleton_mul_subgroup hmem]
      rw [Set.singleton_mul_singleton] at hi₀
      exact hi₀.symm
  · intro hm; by_contra hne
    have : heckeMultiplicity P D1 (HeckeCoset.one P) d = 0 := by
      simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
      intro ⟨i, j⟩ heq
      exact (Ne.symm hne) ((doubleCoset_eq_of_rightCoset_eq P D1 (HeckeCoset.one P) d (i, j)
        heq).symm ▸ mulMap_T_one_eq P D1 i j)
    omega

private lemma mulMap_one_T_eq (D1 : HeckeCoset P) (i : decompQuot P (HeckeCoset.one P)) (j : decompQuot P D1) :
    mulMap P (HeckeCoset.one P) D1 (i, j) = D1 := by
  unfold mulMap
  apply HeckeRing.HeckeCoset_ext P
  simp only [HeckeCoset.mk']
  have hD1 := D1.doubleCoset_eq.choose_spec
  conv => enter [2]; rw [hD1]
  rw [mul_assoc]
  simp_rw [doset_mul_left_eq_self,
    doset_mul_left_eq_self P ⟨(HeckeCoset.one P).doubleCoset_eq.choose, T_one_choose_mem_H P⟩,
    doset_mul_left_eq_self]

/-- The multiplicity `heckeMultiplicity` is nonzero for double cosets in the multiplication support. -/
lemma heckeMultiplicity_pos_of_mem_mulSupport (D1 D2 d : HeckeCoset P) (hd : d ∈ mulSupport P D1 D2) :
    heckeMultiplicity P D1 D2 d ≠ 0 := by
  rw [heckeMultiplicity]; simp only [ne_eq, Nat.cast_eq_zero]
  rw [Nat.card_eq_zero, not_or, not_isEmpty_iff]
  refine ⟨?_, not_infinite_iff_finite.mpr inferInstance⟩
  rw [mulSupport] at hd
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists] at hd
  obtain ⟨i₀, j₀, hmap⟩ := hd
  have hset_eq : DoubleCoset.doubleCoset
      ((↑i₀.out : G) * (D1.doubleCoset_eq.choose : G) * ((↑j₀.out : G) * (D2.doubleCoset_eq.choose : G)))
      (P.H : Set G) (P.H : Set G) =
      DoubleCoset.doubleCoset (d.doubleCoset_eq.choose : G) P.H P.H := by
    have := congr_arg HeckeCoset.carrier hmap; rw [mulMap, HeckeCoset.mk'] at this
    simp only at this; rwa [d.doubleCoset_eq.choose_spec] at this
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := (DoubleCoset.eq P.H P.H _ _).mp
    (DoubleCoset.mk_eq_of_doubleCoset_eq hset_eq)
  set α := (D1.doubleCoset_eq.choose : G)
  set β := (D2.doubleCoset_eq.choose : G)
  set K₁ := (ConjAct.toConjAct α • P.H).subgroupOf P.H
  set i' : decompQuot P D1 := ⟦⟨h₁ * ↑i₀.out, P.H.mul_mem hh₁ i₀.out.2⟩⟧
  obtain ⟨κ₁, hκ₁_eq⟩ := QuotientGroup.mk_out_eq_mul K₁
    ⟨h₁ * ↑i₀.out, P.H.mul_mem hh₁ i₀.out.2⟩
  have hκ₁_conj : α⁻¹ * (κ₁.val : G) * α ∈ P.H := by
    have := κ₁.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct] using this
  set K₂ := (ConjAct.toConjAct β • P.H).subgroupOf P.H
  set j' : decompQuot P D2 := ⟦⟨(α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out,
    P.H.mul_mem (P.H.inv_mem hκ₁_conj) j₀.out.2⟩⟧
  obtain ⟨κ₂, hκ₂_eq⟩ := QuotientGroup.mk_out_eq_mul K₂
    ⟨(α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out,
      P.H.mul_mem (P.H.inv_mem hκ₁_conj) j₀.out.2⟩
  have hκ₂_conj : β⁻¹ * (κ₂.val : G) * β ∈ P.H := by
    have := κ₂.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct] using this
  have hi'_coe : (↑i'.out : G) = h₁ * ↑i₀.out * (κ₁.val : G) := by
    have h := hκ₁_eq; apply_fun (↑· : ↥P.H → G) at h
    simp only [Subgroup.coe_mul] at h; exact h
  have hj'_coe : (↑j'.out : G) =
      (α⁻¹ * (κ₁.val : G) * α)⁻¹ * ↑j₀.out * (κ₂.val : G) := by
    have h := hκ₂_eq; apply_fun (↑· : ↥P.H → G) at h
    simp only [Subgroup.coe_mul] at h; exact h
  refine ⟨⟨(i', j'), ?_⟩⟩
  simp only [Set.mem_setOf_eq]
  have hprod_main : (↑i'.out : G) * α * ((↑j'.out : G) * β) =
      (d.doubleCoset_eq.choose : G) * (h₂⁻¹ * (β⁻¹ * (κ₂.val : G) * β)) := by
    rw [hi'_coe, hj'_coe]
    have hprod' : (d.doubleCoset_eq.choose : G) =
      h₁ * (↑i₀.out * α * (↑j₀.out * β)) * h₂ := hprod
    rw [hprod']; group
  rw [Set.singleton_mul_singleton, hprod_main, ← Set.singleton_mul_singleton, mul_assoc,
    Subgroup.singleton_mul_subgroup (P.H.mul_mem (P.H.inv_mem hh₂) hκ₂_conj)]

/-- The multiplicity `heckeMultiplicity` is zero for double cosets outside the multiplication support. -/
lemma heckeMultiplicity_eq_zero_of_nmem_mulSupport (D1 D2 d : HeckeCoset P) (hd : d ∉ mulSupport P D1 D2) :
    heckeMultiplicity P D1 D2 d = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
  rintro ⟨i, j⟩ hij
  apply hd
  rw [mulSupport]
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  exact ⟨i, j, doubleCoset_eq_of_rightCoset_eq P D1 D2 d _ hij⟩

/-- A multiplicity that is both at most one and positive must equal one. -/
lemma heckeMultiplicity_eq_one_of_le_one_and_pos (D1 D2 d : HeckeCoset P)
    (h_le : heckeMultiplicity P D1 D2 d ≤ 1)
    (h_pos : 0 < heckeMultiplicity P D1 D2 d) :
    heckeMultiplicity P D1 D2 d = 1 := by omega

/-- The multiplicity `heckeMultiplicity` is positive for double cosets in the multiplication support. -/
lemma heckeMultiplicity_pos_of_mem (D1 D2 d : HeckeCoset P) (hd : d ∈ mulSupport P D1 D2) :
    0 < heckeMultiplicity P D1 D2 d := by
  have h_ne := heckeMultiplicity_pos_of_mem_mulSupport P D1 D2 d hd
  have : (0 : ℤ) ≤ heckeMultiplicity P D1 D2 d := by
    simp only [heckeMultiplicity]; exact Nat.cast_nonneg _
  omega

/-- Left multiplication by `HeckeCoset.one` has multiplicity `1` on the diagonal and `0` elsewhere. -/
lemma heckeMultiplicity_one_mul (D1 d : HeckeCoset P) : D1 = d ↔ heckeMultiplicity P (HeckeCoset.one P) D1 d = 1 := by
  constructor
  · intro h; subst h
    simp only [heckeMultiplicity]; norm_cast; rw [Nat.card_eq_one_iff_unique]
    haveI : Subsingleton (decompQuot P (HeckeCoset.one P)) := subsingleton_decompQuot_T_one P
    refine ⟨⟨?_⟩, ?_⟩
    · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      simp only [Set.mem_setOf_eq] at h₁ h₂
      exact Subtype.ext (Prod.ext rfl (decompQuot_snd_eq_of_fst_eq P (HeckeCoset.one P) D1 D1 i₁ j₁ j₂ h₁ h₂))
    · have hd_mem : D1 ∈ mulSupport P (HeckeCoset.one P) D1 := by
        simp only [mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
          Prod.exists]
        obtain ⟨i₀⟩ := one_in_decompQuot_T_one P
        exact ⟨i₀, ⟦⟨1, P.H.one_mem⟩⟧, mulMap_one_T_eq P D1 i₀ _⟩
      have hne := heckeMultiplicity_pos_of_mem_mulSupport P (HeckeCoset.one P) D1 D1 hd_mem
      rw [heckeMultiplicity, ne_eq, Nat.cast_eq_zero, Nat.card_eq_zero, not_or, not_isEmpty_iff] at hne
      exact hne.1
  · intro hm; by_contra hne
    have : heckeMultiplicity P (HeckeCoset.one P) D1 d = 0 := by
      simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
      intro ⟨i, j⟩ heq
      exact (Ne.symm hne) ((doubleCoset_eq_of_rightCoset_eq P (HeckeCoset.one P) D1 d (i, j)
        heq).symm ▸ mulMap_one_T_eq P D1 i j)
    omega

/-- Scalar multiplication on finitely supported functions by ring elements. -/
noncomputable instance instSMulZeroClass : SMulZeroClass Z (α →₀ Z) where
  smul a v := v.mapRange (a • ·) (smul_zero _)
  smul_zero a := by ext; exact smul_zero _

/-- The multiplication finsupp: `m(D1, D2)` is the formal sum `Σ_d heckeMultiplicity(D1, D2, d) · d`
encoding the product of two double cosets. -/
noncomputable def m (D1 D2 : HeckeCoset P) : (HeckeCoset P) →₀ ℤ :=
  ⟨mulSupport P D1 D2, fun d => heckeMultiplicity P D1 D2 d, fun a =>
    ⟨heckeMultiplicity_pos_of_mem_mulSupport P D1 D2 a, fun hm => by
      by_contra hemp; exact hm (heckeMultiplicity_eq_zero_of_nmem_mulSupport P D1 D2 a hemp)⟩⟩

/-- The multiplication on the Hecke ring, defined via the multiplicity function `m`. -/
noncomputable instance (P : HeckePair G) : Mul (𝕋 P ℤ) where
  mul f g := Finsupp.sum f fun D1 b₁ =>
    g.sum fun D2 b₂ => b₁ • b₂ • m P D1 D2

/-- Multiplication in the Hecke ring unfolds as a double Finsupp sum over multiplicities. -/
lemma mul_def (f g : 𝕋 P ℤ) : f * g = Finsupp.sum f
    (fun D1 b₁ => g.sum fun D2 b₂ => b₁ • b₂ • m P D1 D2) := rfl

/-- A basis element of the Hecke ring: `T_single D b` is the formal sum `b · [D]`. -/
noncomputable abbrev T_single (a : HeckeCoset P) (b : Z) : 𝕋 P Z :=
  Finsupp.single a b

/-- A basis element of the Hecke module: `HeckeLeftCoset_single m b` is the formal sum `b · [m]`. -/
noncomputable abbrev HeckeLeftCoset_single (a : HeckeLeftCoset P) (b : Z) : HeckeModule P Z :=
  Finsupp.single a b

/-- Shimura's notation: `T⦃D⦄` is the basis element `[HgH]` in the Hecke ring,
    corresponding to the double coset `D` with coefficient 1. -/
scoped notation:max "T⦃" D "⦄" => T_single _ ℤ D (1 : ℤ)

/-- Shimura's notation: `T⦃D, a⦄` is the element `a · [HgH]` in the Hecke ring. -/
scoped notation:max "T⦃" D ", " a "⦄" => T_single _ ℤ D a

/-- Multiplication of two basis elements in the Hecke ring. -/
lemma mul_singleton_𝕋 (D1 D2 : HeckeCoset P) (a b : ℤ) :
    T_single P ℤ D1 a * T_single P ℤ D2 b = a • b • m P D1 D2 := by
  simp_rw [T_single, mul_def]
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index, m]
  · simp only [zero_smul, smul_zero]
  · ext a; simp only [m, zero_smul, Finsupp.sum_fun_zero, Finsupp.coe_zero, Pi.zero_apply]

open Finsupp

/-- If all pairs under `mulMap` land on a single double coset `D_out`, then `heckeMultiplicity` vanishes
on every other coset. -/
lemma heckeMultiplicity_eq_zero_of_mulMap_unique (D1 D2 D_out A : HeckeCoset P)
    (hA : A ≠ D_out)
    (h : ∀ p : decompQuot P D1 × decompQuot P D2,
      mulMap P D1 D2 p = D_out) : heckeMultiplicity P D1 D2 A = 0 :=
  heckeMultiplicity_eq_zero_of_nmem_mulSupport P D1 D2 A (by
    rw [mulSupport]; simp only [Finset.top_eq_univ, Finset.mem_image,
      Finset.mem_univ, true_and, Prod.exists, not_exists]
    exact fun i j heq => hA (heq ▸ h (i, j)))

/-- When `heckeMultiplicity` equals one on a single output coset and vanishes elsewhere,
the multiplication finsupp is a singleton. -/
lemma m_eq_single (D1 D2 D_out : HeckeCoset P) (h_one : heckeMultiplicity P D1 D2 D_out = 1)
    (h_zero : ∀ A, A ≠ D_out → heckeMultiplicity P D1 D2 A = 0) :
    m P D1 D2 = Finsupp.single D_out 1 := by
  ext A; simp only [m, Finsupp.coe_mk, Finsupp.single_apply]
  split_ifs with h1 <;> [exact h1 ▸ h_one; exact h_zero A (ne_comm.mp h1)]

/-- The off-diagonal multiplicity for right multiplication by `HeckeCoset.one` is zero. -/
lemma heckeMultiplicity_mul_one_eq_zero (D1 A : HeckeCoset P) (h : A ≠ D1) : heckeMultiplicity P D1 (HeckeCoset.one P) A = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
  intro ⟨i, j⟩ heq
  exact h ((doubleCoset_eq_of_rightCoset_eq P D1 (HeckeCoset.one P) A (i, j) heq).symm ▸
    mulMap_T_one_eq P D1 i j)

/-- Right multiplication by `HeckeCoset.one` acts as the identity: `m(D1, HeckeCoset.one) = δ_{D1}`. -/
lemma m_mul_one_eq_single (D1 : HeckeCoset P) : m P D1 (HeckeCoset.one P) = Finsupp.single D1 1 :=
  m_eq_single P D1 (HeckeCoset.one P) D1
    ((heckeMultiplicity_mul_one P D1 D1).mp rfl) (fun A hA => heckeMultiplicity_mul_one_eq_zero P D1 A hA)

/-- `T_single D b * T_single (HeckeCoset.one P) 1 = T_single D b`. -/
lemma singleton_one_mul_𝕋 (D2 : HeckeCoset P) (b : ℤ) :
    T_single P ℤ D2 b * T_single P ℤ (HeckeCoset.one P) 1 = T_single P ℤ D2 b := by
  simp only [T_single, HeckeCoset.one, HeckeCoset.mk', OneMemClass.coe_one, mul_singleton_𝕋, one_smul]
  rw [← Finsupp.smul_single_one]; congr; exact m_mul_one_eq_single P D2

/-- The off-diagonal multiplicity for left multiplication by `HeckeCoset.one` is zero. -/
lemma heckeMultiplicity_one_mul_eq_zero (D1 A : HeckeCoset P) (h : A ≠ D1) : heckeMultiplicity P (HeckeCoset.one P) D1 A = 0 := by
  simp only [heckeMultiplicity, Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
  intro ⟨i, j⟩ heq
  exact h ((doubleCoset_eq_of_rightCoset_eq P (HeckeCoset.one P) D1 A (i, j) heq).symm ▸
    mulMap_one_T_eq P D1 i j)

/-- Left multiplication by `HeckeCoset.one` acts as the identity: `m(HeckeCoset.one, D1) = δ_{D1}`. -/
lemma m_one_mul_eq_single (D1 : HeckeCoset P) : m P (HeckeCoset.one P) D1 = Finsupp.single D1 1 :=
  m_eq_single P (HeckeCoset.one P) D1 D1
    ((heckeMultiplicity_one_mul P D1 D1).mp rfl) (fun A hA => heckeMultiplicity_one_mul_eq_zero P D1 A hA)

/-- `T_single (HeckeCoset.one P) 1 * T_single D b = T_single D b`. -/
lemma one_mul_singleton_𝕋 (D2 : HeckeCoset P) (b : ℤ) :
    T_single P ℤ (HeckeCoset.one P) 1 * T_single P ℤ D2 b = T_single P ℤ D2 b := by
  simp only [T_single, HeckeCoset.one, HeckeCoset.mk', OneMemClass.coe_one, mul_singleton_𝕋, one_smul]
  rw [← Finsupp.smul_single_one]; congr; exact m_one_mul_eq_single P D2

/-- The Hecke ring is a non-unital non-associative semiring (distributivity and zero laws). -/
noncomputable instance instNonUnitalNonAssocSemiring : NonUnitalNonAssocSemiring (𝕋 P ℤ) :=
  { (instAddCommGroup𝕋 P ℤ) with
    left_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (congr_arg (Finsupp.sum f)
        (funext₂ fun a₁ b₁ => Finsupp.sum_add_index ?_ ?_))
        ?_ <;>
        simp
      intro D1 _ a b
      simp_rw [← smul_assoc, smul_eq_mul]
      ring_nf
      rw [@add_smul]

    right_distrib := fun f g h => by
      simp only [mul_def]
      refine Eq.trans (Finsupp.sum_add_index ?_ ?_) ?_ <;>
        simp only [Finset.mem_union, mem_support_iff, ne_eq, zero_smul, sum_fun_zero, implies_true]
      intro D1 _ a b
      apply Finsupp.ext; intro t
      simp_rw [add_smul]
      simp only [sum_add, coe_add, Pi.add_apply, sum_apply, coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [add_apply]
      simp only [sum_apply, coe_smul, Pi.smul_apply, smul_eq_mul]

    zero_mul := fun f => by
      simp only [mul_def]
      exact Finsupp.sum_zero_index
    mul_zero := fun f => by
      simp only [mul_def]
      exact Eq.trans (congr_arg (sum f)
        (funext₂ fun a₁ b₁ => sum_zero_index)) (sum_fun_zero f) }
