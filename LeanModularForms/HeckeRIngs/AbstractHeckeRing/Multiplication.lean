/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic

/-!
# Hecke Rings: Multiplication

Shimura's multiplicity `m'`, the multiplication finsupp `m`, the `Mul` instance on `𝕋 P ℤ`,
and the `NonUnitalNonAssocSemiring` instance. Proves that `T_one` is the identity element.
-/

open Commensurable Classical MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

variable (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] [IsDomain Z]

lemma decompQuot_T_one_eq_bot :
    (ConjAct.toConjAct ((T_one P).eql.choose : G) • P.H).subgroupOf
      P.H = ⊤ := by
  have h := T_one_choose_mem_H P
  rw [Subgroup.subgroupOf_eq_top ]
  intro x hx
  rw [← @SetLike.mem_coe]
  simp only [Subgroup.coe_pointwise_smul]
  rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h,
    Subgroup.subgroup_mul_singleton (by simp [h])]
  exact hx

lemma one_in_decompQuot_T_one : Nonempty (decompQuot P (T_one P)) := by
  use (1 : P.H)

lemma subsingleton_decompQuot_T_one : Subsingleton (decompQuot P (T_one P)) := by
  unfold decompQuot
  rw [decompQuot_T_one_eq_bot]
  apply QuotientGroup.subsingleton_quotient_top

private lemma self_mem_singleton_mul (a : G) : a ∈ {a} * (H : Set G) := by simp

private lemma conjAct_mem_of_leftCoset_eq (d : Δ) (h h' : H)
  (hyp : {(h : G)} * {(d : G)} * (H : Set G) = {(h' : G)} * {(d : G)} * (H : Set G)):
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
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [inv_inv, key]
  simp only [mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left]
  exact hk

lemma decompQuot_coset_diff (D : T' P) (i j : decompQuot P D) (hij : i ≠ j) :
  {((i.out : G) * (D.eql.choose : G))} * (P.H : Set G) ≠
    {((j.out : G) * (D.eql.choose : G))} * (P.H : Set G) := by
  intro h
  simp_rw [← Set.singleton_mul_singleton] at h
  have := conjAct_mem_of_leftCoset_eq P.H P.Δ D.eql.choose i.out j.out h
  rw [← @QuotientGroup.leftRel_apply, ← @Quotient.eq''] at this
  simp only [Quotient.out_eq'] at this
  exact hij this.symm

lemma leftCoset_eq_of_not_disjoint (f g : G) (h : ¬ Disjoint (g • (H : Set G)) (f • H)) :
    {g} * (H : Set G) = {f} * H := by
  simp_rw [← Set.singleton_smul] at *
  rw [@not_disjoint_iff] at h
  obtain ⟨a, ha, ha2⟩ := h
  simp only [smul_eq_mul, singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe] at ha ha2
  refine Set.ext ?intro.intro.h
  intro Y
  simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe]
  simp_rw [← @QuotientGroup.eq] at *
  rw [← ha] at ha2
  rw [ha2]

private lemma singleton_mul_subset_mul (g : G) (T S : Set G) (h : g ∈ S) : {g} * T ⊆ S * T :=
  mul_subset_mul_right (singleton_subset_iff.mpr h)

private lemma left_coset_exist (D : T' P) : ∃ (i : decompQuot P D),
  {(D.eql.choose : G)} * (P.H : Set G) = {(i.out : G)} * {(D.eql.choose : G)} * P.H := by
  have hc := D.eql.choose_spec
  rw [DoubleCoset.doubleCoset_eq_iUnion_leftCosets] at hc
  have h1 : {(D.eql.choose : G)} * (P.H : Set G) ⊆ D.set := by
    have v0 := D.eql.choose_spec
    conv =>
      enter [2]
      rw [v0]
    intro i hi
    simp only [singleton_mul, image_mul_left, mem_preimage, SetLike.mem_coe] at *
    rw [mem_doubleCoset]
    use 1
    simp only [SetLike.mem_coe, one_mem, one_mul, true_and]
    use (D.eql.choose : G)⁻¹ * i
    simp [hi]
  have hr := hc.le
  have h3 := le_trans h1 hr
  simp only [le_eq_subset] at h3
  have h4 : (D.eql.choose : G) ∈ {(D.eql.choose : G)} * (P.H : Set G) := by
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

private lemma left_coset_exist_unique (D : T' P) : ∃! (i : decompQuot P D),
  {(D.eql.choose : G)} * (P.H : Set G) = {(i.out : G) * (D.eql.choose : G)} * P.H := by
  obtain ⟨i, hi⟩ := left_coset_exist P D
  use i
  rw [Set.singleton_mul_singleton] at hi
  simp only [hi,true_and]
  intro j h
  by_contra c
  have := (decompQuot_coset_diff P D j i c).symm
  aesop

private lemma mul_mem_delta (a : H) (g : Δ)
    (h₀ : H.toSubmonoid ≤ Δ) :
    (a : G) * (g : G) ∈ Δ := by
  apply Submonoid.mul_mem _ (h₀ a.2) (g.2)

noncomputable def mulMap (D1 D2 : T' P) (i : decompQuot P D1 × decompQuot P D2) : T' P := T_mk P
    ⟨i.1.out * D1.eql.choose * (i.2.out * D2.eql.choose),
      Submonoid.mul_mem _ (mul_mem_delta P.H P.Δ i.1.out D1.eql.choose P.h₀)
        (mul_mem_delta P.H P.Δ i.2.out D2.eql.choose P.h₀)⟩

/-- Shimura's multiplicity (Proposition 3.2): the number of pairs (i,j) of right coset
representatives such that `σᵢ τⱼ` lands in the right coset `d.choose · H`.
This is the right-coset analog of Shimura's formula
`m(u·v; w) = #{(i,j) | Γ αᵢ βⱼ = Γξ}`. -/
noncomputable def m' (D1 D2 d : T' P) : ℤ :=
  Nat.card {⟨i, j⟩ : (decompQuot P D1) × (decompQuot P D2) |
    ({(i.out : G) * (D1.eql.choose : G)} : Set G) * {(j.out : G) * (D2.eql.choose : G)} * P.H =
     {(d.eql.choose : G)} * (P.H : Set G)}

noncomputable def mulSupport (D1 D2 : T' P) : (Finset (T' P)) := Finset.image (mulMap P D1 D2) ⊤

/-- If the right-coset condition `σ_i τ_j H = ξ H` holds, then the double coset of
`σ_i τ_j` equals the double coset of `ξ`. This is because `g ∈ ξ H` implies
`H g H = H ξ H` (the right H-coset is contained in the double coset). -/
private lemma doubleCoset_eq_of_rightCoset_eq
    (D1 D2 d : T' P)
    (p : decompQuot P D1 × decompQuot P D2)
    (heq : ({(p.1.out : G) * (D1.eql.choose : G)} : Set G) *
      {(p.2.out : G) * (D2.eql.choose : G)} * P.H =
      {(d.eql.choose : G)} * (P.H : Set G)) :
    mulMap P D1 D2 p = d := by
  apply HeckeRing.T'_ext P
  rw [mulMap, T_mk]
  simp only
  have h_mem : (p.1.out : G) * (D1.eql.choose : G) * ((p.2.out : G) * (D2.eql.choose : G))
      ∈ ({(d.eql.choose : G)} : Set G) * (P.H : Set G) := by
    rw [← heq, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, P.H.one_mem, by simp⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_mem
  simp only [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  dsimp only at hprod ⊢
  rw [← hprod]
  conv_rhs => rw [d.eql.choose_spec]
  exact DoubleCoset.doubleCoset_mul_right_eq_self P ⟨h, hh⟩ _

private lemma mulMap_T_one_eq (D1 : T' P) (i : decompQuot P D1) (j : decompQuot P (T_one P)) :
    mulMap P D1 (T_one P) (i, j) = D1 := by
  unfold mulMap
  apply HeckeRing.T'_ext P
  simp only [T_mk]
  have hD1 := D1.eql.choose_spec
  conv => enter [2]; rw [hD1]
  rw [mul_assoc, doset_mul_left_eq_self]
  apply DoubleCoset.doubleCoset_mul_right_eq_self P ⟨j.out * (T_one P).eql.choose, by
    apply Subgroup.mul_mem _ (by simp) (T_one_choose_mem_H P)⟩

lemma m'_T_one (D1 d : T' P) : D1 = d ↔ m' P D1 (T_one P) d = 1 := by
  constructor
  · intro h; subst h
    simp only [m']; norm_cast; rw [Nat.card_eq_one_iff_unique]
    haveI : Subsingleton (decompQuot P (T_one P)) := subsingleton_decompQuot_T_one P
    refine ⟨⟨?_⟩, ?_⟩
    · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hj : j₁ = j₂ := Subsingleton.elim j₁ j₂; subst hj
      have hmem₁ : (j₁.out : G) * ((T_one P).eql.choose : G) ∈ P.H :=
        Subgroup.mul_mem _ (SetLike.coe_mem j₁.out) (T_one_choose_mem_H P)
      have hi : i₁ = i₂ := by
        by_contra hne; apply decompQuot_coset_diff P D1 i₁ i₂ hne
        have h₁' := h₁; have h₂' := h₂
        simp only [Set.mem_setOf_eq, mul_assoc,
          Subgroup.singleton_mul_subgroup hmem₁] at h₁' h₂'
        exact h₁'.trans h₂'.symm
      subst hi; rfl
    · obtain ⟨i₀, hi₀⟩ := left_coset_exist P D1
      obtain ⟨j₀⟩ := one_in_decompQuot_T_one P
      refine ⟨⟨(i₀, j₀), ?_⟩⟩
      simp only [Set.mem_setOf_eq]
      have hmem : (j₀.out : G) * ((T_one P).eql.choose : G) ∈ P.H :=
        Subgroup.mul_mem _ (SetLike.coe_mem j₀.out) (T_one_choose_mem_H P)
      rw [mul_assoc, Subgroup.singleton_mul_subgroup hmem]
      rw [Set.singleton_mul_singleton] at hi₀
      exact hi₀.symm
  · intro hm; by_contra hne
    have : m' P D1 (T_one P) d = 0 := by
      simp only [m', Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
      intro ⟨i, j⟩ heq
      exact (Ne.symm hne) ((doubleCoset_eq_of_rightCoset_eq P D1 (T_one P) d (i, j)
        heq).symm ▸ mulMap_T_one_eq P D1 i j)
    omega

private lemma mulMap_one_T_eq (D1 : T' P) (i : decompQuot P (T_one P)) (j : decompQuot P D1) :
    mulMap P (T_one P) D1 (i, j) = D1 := by
  unfold mulMap
  apply HeckeRing.T'_ext P
  simp only [T_mk]
  have hD1 := D1.eql.choose_spec
  conv => enter [2]; rw [hD1]
  rw [mul_assoc]
  simp_rw [doset_mul_left_eq_self,
    doset_mul_left_eq_self P ⟨(T_one P).eql.choose, T_one_choose_mem_H P⟩,
    doset_mul_left_eq_self]

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

/-- The degree formula: `deg(d) · m'(D1, D2, d) = #{(i,j) | mulMap(i,j) = d}`.
This implies `d ∈ mulSupport → m'(d) ≠ 0` (the hard direction of the support condition). -/
lemma m'_pos_of_mem_mulSupport (D1 D2 d : T' P) (hd : d ∈ mulSupport P D1 D2) :
    m' P D1 D2 d ≠ 0 := by
  rw [m']; simp only [ne_eq, Nat.cast_eq_zero]
  rw [Nat.card_eq_zero, not_or, not_isEmpty_iff]
  refine ⟨?_, not_infinite_iff_finite.mpr inferInstance⟩
  rw [mulSupport] at hd
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists] at hd
  obtain ⟨i₀, j₀, hmap⟩ := hd
  have hset_eq : DoubleCoset.doubleCoset
      ((↑i₀.out : G) * (D1.eql.choose : G) * ((↑j₀.out : G) * (D2.eql.choose : G)))
      (P.H : Set G) (P.H : Set G) =
      DoubleCoset.doubleCoset (d.eql.choose : G) P.H P.H := by
    have := congr_arg T'.set hmap; rw [mulMap, T_mk] at this
    simp only at this; rwa [d.eql.choose_spec] at this
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := (DoubleCoset.eq P.H P.H _ _).mp
    (DoubleCoset.mk_eq_of_doubleCoset_eq hset_eq)
  set α := (D1.eql.choose : G)
  set β := (D2.eql.choose : G)
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
      (d.eql.choose : G) * (h₂⁻¹ * (β⁻¹ * (κ₂.val : G) * β)) := by
    rw [hi'_coe, hj'_coe]
    have hprod' : (d.eql.choose : G) =
      h₁ * (↑i₀.out * α * (↑j₀.out * β)) * h₂ := hprod
    rw [hprod']; group
  rw [Set.singleton_mul_singleton, hprod_main, ← Set.singleton_mul_singleton, mul_assoc,
    Subgroup.singleton_mul_subgroup (P.H.mul_mem (P.H.inv_mem hh₂) hκ₂_conj)]

lemma m'_eq_zero_of_nmem_mulSupport (D1 D2 d : T' P) (hd : d ∉ mulSupport P D1 D2) :
    m' P D1 D2 d = 0 := by
  simp only [m', Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
  rintro ⟨i, j⟩ hij
  apply hd
  rw [mulSupport]
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  exact ⟨i, j, doubleCoset_eq_of_rightCoset_eq P D1 D2 d _ hij⟩

lemma m'_one_T (D1 d : T' P) : D1 = d ↔ m' P (T_one P) D1 d = 1 := by
  constructor
  · intro h; subst h
    simp only [m']; norm_cast; rw [Nat.card_eq_one_iff_unique]
    haveI : Subsingleton (decompQuot P (T_one P)) := subsingleton_decompQuot_T_one P
    refine ⟨⟨?_⟩, ?_⟩
    · intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
      have hj : j₁ = j₂ := by
        by_contra hne; apply decompQuot_coset_diff P D1 j₁ j₂ hne
        have h₁' := h₁; have h₂' := h₂
        simp only [Set.mem_setOf_eq] at h₁' h₂'
        rw [mul_assoc] at h₁' h₂'
        exact set_singleton_mul_left_cancel _ (h₁'.trans h₂'.symm)
      subst hj; rfl
    · have hd_mem : D1 ∈ mulSupport P (T_one P) D1 := by
        simp only [mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
          Prod.exists]
        obtain ⟨i₀⟩ := one_in_decompQuot_T_one P
        exact ⟨i₀, ⟦⟨1, P.H.one_mem⟩⟧, mulMap_one_T_eq P D1 i₀ _⟩
      have hne := m'_pos_of_mem_mulSupport P (T_one P) D1 D1 hd_mem
      rw [m', ne_eq, Nat.cast_eq_zero, Nat.card_eq_zero, not_or, not_isEmpty_iff] at hne
      exact hne.1
  · intro hm; by_contra hne
    have : m' P (T_one P) D1 d = 0 := by
      simp only [m', Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
      intro ⟨i, j⟩ heq
      exact (Ne.symm hne) ((doubleCoset_eq_of_rightCoset_eq P (T_one P) D1 d (i, j)
        heq).symm ▸ mulMap_one_T_eq P D1 i j)
    omega

noncomputable instance instSMulZeroClass : SMulZeroClass Z (α →₀ Z) where
  smul a v := v.mapRange (a • ·) (smul_zero _)
  smul_zero a := by ext; exact smul_zero _

noncomputable def m (D1 D2 : T' P) : (T' P) →₀ ℤ :=
  ⟨mulSupport P D1 D2, fun d => m' P D1 D2 d, by
   intro a
   constructor
   · exact m'_pos_of_mem_mulSupport P D1 D2 a
   · intro hm
     by_contra hemp
     exact hm (m'_eq_zero_of_nmem_mulSupport P D1 D2 a hemp)⟩

/-- Hecke ring multiplication: `HgH * HhH = ∑ m(g,h,i) · HiH`, extended bilinearly. -/
noncomputable instance (P : ArithmeticGroupPair G) : Mul (𝕋 P ℤ) where
 mul f g := Finsupp.sum f (fun D1 b₁ => g.sum fun D2 b₂ => b₁ • b₂ • m P D1 D2)

lemma mul_def (f g : 𝕋 P ℤ) : f * g = Finsupp.sum f
  (fun D1 b₁ => g.sum fun D2 b₂ => b₁ • b₂ • m P D1 D2) := rfl

noncomputable abbrev T_single (a : T' P) (b : Z) : (𝕋 P Z) := Finsupp.single a b

noncomputable abbrev M_single (a : M P) (b : Z) : (𝕄 P Z) := Finsupp.single a b

/-- Shimura's notation: `T⦃D⦄` is the basis element `[HgH]` in the Hecke ring,
    corresponding to the double coset `D` with coefficient 1. -/
scoped notation:max "T⦃" D "⦄" => T_single _ ℤ D (1 : ℤ)

/-- Shimura's notation: `T⦃D, a⦄` is the element `a · [HgH]` in the Hecke ring. -/
scoped notation:max "T⦃" D ", " a "⦄" => T_single _ ℤ D a

lemma 𝕋_mul_singleton (D1 D2 : (T' P)) (a b : ℤ) :
  (T_single P ℤ D1 a) * (T_single P ℤ D2 b) = a • b • m P D1 D2 := by
  simp_rw [T_single, mul_def]
  rw [Finsupp.sum_single_index, Finsupp.sum_single_index, m]
  simp only [zero_smul, smul_zero]
  ext a
  simp only [m, zero_smul, Finsupp.sum_zero, Finsupp.coe_zero, Pi.zero_apply]

open Finsupp

lemma m'_T_one_eq_zero (D1 A : T' P) (h : A ≠ D1) : m' P D1 (T_one P) A = 0 := by
  simp only [m', Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
  intro ⟨i, j⟩ heq
  exact h ((doubleCoset_eq_of_rightCoset_eq P D1 (T_one P) A (i, j) heq).symm ▸
    mulMap_T_one_eq P D1 i j)

lemma m_right_T_one_eq_single (D1 : T' P) : m P D1 (T_one P) = Finsupp.single D1 1 := by
  ext A
  simp only [m, Finsupp.coe_mk]
  rw [Finsupp.single_apply]
  split_ifs with h1
  · rw [← h1]
    exact (m'_T_one P D1 D1).mp rfl
  · exact m'_T_one_eq_zero P D1 A (Ne.symm h1)

lemma 𝕋_singleton_one_mul (D2 : (T' P)) (b : ℤ) :
  (T_single P ℤ D2 b) * T_single P ℤ (T_one P) (1 : ℤ) = (T_single P ℤ D2 b) := by
  simp only [T_single, T_one, T_mk, OneMemClass.coe_one, 𝕋_mul_singleton, one_smul]
  rw [← Finsupp.smul_single_one]
  congr
  exact m_right_T_one_eq_single P D2

lemma m'_one_T_eq_zero (D1 A : T' P) (h : A ≠ D1) : m' P (T_one P) D1 A = 0 := by
  simp only [m', Nat.cast_eq_zero, Nat.card_eq_zero, isEmpty_subtype]; left
  intro ⟨i, j⟩ heq
  exact h ((doubleCoset_eq_of_rightCoset_eq P (T_one P) D1 A (i, j) heq).symm ▸
    mulMap_one_T_eq P D1 i j)

lemma m_left_T_one_eq_single (D1 : T' P) : m P (T_one P) D1 = Finsupp.single D1 1 := by
  ext A
  simp only [m, Finsupp.coe_mk]
  rw [Finsupp.single_apply]
  split_ifs with h1
  · rw [← h1]
    exact (m'_one_T P D1 D1).mp rfl
  · exact m'_one_T_eq_zero P D1 A (Ne.symm h1)

lemma 𝕋_one_mul_singleton (D2 : (T' P)) (b : ℤ) :
  T_single P ℤ (T_one P) (1 : ℤ) * (T_single P ℤ D2 b) = (T_single P ℤ D2 b) := by
  simp only [T_single, T_one, T_mk, OneMemClass.coe_one, 𝕋_mul_singleton, one_smul]
  rw [← Finsupp.smul_single_one]
  congr
  exact m_left_T_one_eq_single P D2

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
        simp only [Finset.mem_union, mem_support_iff, ne_eq, zero_smul, sum_zero, implies_true]
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
      exact Eq.trans (congr_arg (sum f) (funext₂ fun a₁ b₁ => sum_zero_index)) sum_zero }
