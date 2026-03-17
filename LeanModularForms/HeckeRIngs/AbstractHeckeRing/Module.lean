/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication

/-!
# Hecke Rings: Module Action

The module action of `𝕋 P ℤ` on `𝕄 P ℤ` (formal sums of left cosets), the faithfulness
theorem `𝕋_eq_of_smul_eq_smul`, and auxiliary Finsupp algebra helpers.
-/

open Commensurable Classical Doset MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

variable (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] [IsDomain Z]

open Finsupp

noncomputable instance instSMul𝕋 : SMul (𝕋 P ℤ) (𝕋 P ℤ) where
  smul := fun x y => y * x

/-- The orbit `{m · σᵢ · g | σᵢ ∈ Q(t)}` of left coset representatives acting on `m`. -/
noncomputable def smulOrbit (t : T' P) (m : M P) :
    Finset (M P) :=
  Finset.image (fun i : (decompQuot P t) =>
    M_mk P ⟨((m.eql.choose : G) * (i.out : G) *
      (t.eql.choose : G)),
    delta_mul_mem P.H P.Δ i.out
      m.eql.choose t.eql.choose P.h₀⟩) ⊤

lemma smulOrbit_nonempty (t : T' P) (m : M P) : (smulOrbit P t m).Nonempty := by
  rw [smulOrbit]
  simp

/-- Module action of `𝕋 P Z` on `𝕄 P Z`:
    `HgH • vH = ∑ᵢ v·σᵢ·g H`, extended bilinearly. -/
noncomputable instance instSMul𝕄 : SMul (𝕋 P Z) (𝕄 P Z) where
  smul := fun t => fun mm => Finsupp.sum t (fun D1 b₁ => mm.sum fun m b₂ =>
    ((∑ i ∈ smulOrbit P D1 m, Finsupp.single (i) (b₁*b₂ : Z) : (M P) →₀ Z)))

omit [IsDomain Z] in
lemma smul_eq_sum (T : 𝕋 P Z) (m : 𝕄 P Z) :
    T • m = Finsupp.sum T (fun D1 b₁ =>
      m.sum fun m b₂ =>
        ((∑ i ∈ smulOrbit P D1 m,
          Finsupp.single (i) (b₁ * b₂ : Z) :
            (M P) →₀ Z))) := rfl

noncomputable instance instHSMul𝕄 : HSMul (𝕋 P Z) (𝕄 P Z) (𝕄 P Z) := inferInstance

omit [IsDomain Z] in
lemma single_smul_single (t : T' P) (m : M P) (a b : Z) :
  (instHSMul𝕄 P Z).hSMul ((Finsupp.single t a) : 𝕋 P Z) ((Finsupp.single m b) : 𝕄 P Z) =
   ((∑ i ∈ smulOrbit P t m, Finsupp.single (i) (a * b : Z) : (M P) →₀ Z)):= by
  rw [smul_eq_sum]
  simp [mul_zero, single_zero, Finset.sum_const_zero,
    sum_single_index, zero_mul]

omit [IsDomain Z] in
lemma single_basis {α : Type*} (t : Finsupp α Z) :
    t = ∑ (i ∈ t.support), single i (t.toFun i) := by
  ext a
  simp_rw [Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp only [Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  aesop

omit [IsDomain Z] in
private lemma support_eq {α : Type*}
    (t s : Finsupp α Z)
    (h : t.support = s.support)
    (h2 : ∀ a ∈ t.support, t a = s a) :
    t = s := by
  ext a
  by_cases ha : a ∈ t.support
  exact h2 a ha
  have hsa := ha
  rw [h] at hsa
  rw [notMem_support_iff] at *
  rw [ha, hsa]

noncomputable instance instOne𝕄 : One (𝕄 P Z) := ⟨Finsupp.single (M_one P) (1 : Z)⟩

omit [IsDomain Z] in
lemma one_eq_M_single : (1 : 𝕄 P Z) = Finsupp.single (M_one P) (1 : Z) := rfl

omit [IsDomain Z] in
private lemma sum_single_eq_zero {α : Type*} (s : Finset α) (fs : α → Z)
    (h : ∑ i ∈ s, single (i : α) (fs i) = 0) : ∀ i ∈ s, fs i = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.notMem_empty, false_implies, implies_true] at *
  | insert i s hi hs =>
  have hfin := h
  rw [Finset.sum_insert hi, @add_eq_zero_iff_eq_neg] at h hfin
  rw [← @Finset.sum_neg_distrib] at h
  conv at h =>
    enter [2,2]
    ext r
    rw [← @single_neg]
  rw [eq_comm, eq_single_iff] at h
  simp at h
  rcases h.1 with hl | hr
  · intro j hj
    simp at hj
    rcases hj with hj1 | hj2
    · have h2 := h.2
      have : ∑ c ∈ s, (single c (fs c)) i = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        rw [single_apply]
        split_ifs with heq
        · exfalso; exact hi (heq ▸ hc)
        · rfl
      rw [this, neg_zero] at h2
      rw [hj1, h2]
    · apply hs hl
      exact hj2
  · intro j hj
    simp at hj
    rcases hj with hj1 | hj2
    · have h2 := h.2
      rw [← hj1] at h2 hr
      have hgg := Finsupp.support_finset_sum (s := s) (f := fun m => single m (fs m))
      rw [hr] at hgg
      simp only [Finset.singleton_subset_iff, Finset.mem_biUnion, mem_support_iff, ne_eq] at hgg
      obtain ⟨x, hx, hxx⟩ := hgg
      rw [@single_apply_eq_zero] at hxx
      simp at hxx
      rw [hj1] at hxx
      rw [← hxx.1] at hx
      exfalso
      exact hi hx
    · have hgg := Finsupp.support_finset_sum (s := s) (f := fun m => single m (fs m))
      rw [hr] at hgg
      simp only [Finset.singleton_subset_iff, Finset.mem_biUnion, mem_support_iff, ne_eq] at hgg
      obtain ⟨x, hx, hxx⟩ := hgg
      rw [@single_apply_eq_zero] at hxx
      simp at hxx
      exfalso
      rw [← hxx.1] at hx
      exact hi hx

omit [IsDomain Z] in
private lemma sum_single_support (s : Finset (M P)) (fs : M P → Z) :
  (∑ i ∈ s, single i (fs i)).support ⊆ s := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs =>
  rw [Finset.sum_insert hi]
  apply Finset.Subset.trans (Finsupp.support_add)
  rw [@Finset.insert_eq]
  exact Finset.union_subset_union support_single_subset hs

omit [IsDomain Z] in
private lemma sum_disj (s t : Finset (M P)) (x y : M P → Z) (hst : Disjoint s t) :
  (∑ i ∈ s, single i (x i) + ∑ j ∈ t, single j (y j) = 0) ↔
    ∑ i ∈ s, single i (x i) = 0 ∧ ∑ j ∈ t, single j (y j) = 0 := by
  constructor
  intro h
  rw [@add_eq_zero_iff_eq_neg, ← @Finset.sum_neg_distrib, @ext_iff'] at h
  have hs1 := sum_single_support P Z s x
  have hs2 := sum_single_support P Z t (-y)
  simp only [Finset.sum_neg_distrib, support_neg, mem_support_iff, ne_eq, coe_neg, Pi.neg_apply,
    single_neg] at *
  have := hst.mono hs1 hs2
  have ht := this
  rw [h.1] at this
  rw [← h.1] at ht
  simp at this ht
  exact ⟨ht, this⟩
  intro h
  rw [h.1, h.2]
  exact card_support_eq_zero.mp (by simp only [add_zero, support_zero, Finset.card_empty])

omit [IsDomain Z] in
private lemma finsupp_sum_support_subset_union_support (s : Finset (𝕄 P Z)) :
  ((∑ x ∈ s, x).support) ≤ Finset.biUnion s fun i ↦ i.support := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi hs =>
  conv =>
    enter[1,1]
    rw [Finset.sum_insert hi]
  apply le_trans Finsupp.support_add
  rw [@Finset.biUnion_insert]
  exact Finset.union_subset_union (Finset.Subset.refl _) hs

omit [IsDomain Z] in
private lemma sum_disj2 (S : (Finset (𝕄 P Z)))
    (hst : PairwiseDisjoint (S : Set (𝕄 P Z))
      fun x => x.support) :
    (∑ i ∈ S, i = 0) ↔
      ∀ i : S, i = (0 : 𝕄 P Z) := by
  constructor
  · intro h
    induction S using Finset.induction_on with
    | empty => simp only [IsEmpty.forall_iff]
    | insert i s hi hs =>
      simp only [Subtype.forall, Finset.mem_insert, forall_eq_or_imp]
      rw [Finset.sum_insert hi, single_basis Z i, single_basis Z (∑ x ∈ s, x)] at h
      rw [single_basis Z i]
      have := (sum_disj P Z i.support
        (∑ x ∈ s, x).support i.toFun
        (∑ x ∈ s, x).toFun ?_).mp h
      · constructor
        · apply this.1
        · rw [single_basis Z (∑ x ∈ s, x)] at hs
          simp only [Subtype.forall] at hs
          apply hs
          · simp only [Finset.coe_insert] at hst
            rw [pairwiseDisjoint_insert] at hst
            exact hst.1
          · apply this.2
      · have sup : ((∑ x ∈ s, x).support) ≤ Finset.biUnion s fun i ↦ i.support := by
          apply finsupp_sum_support_subset_union_support P Z s
        have sup2 : i.support ≤ i.support := le_refl _
        have := Disjoint.mono sup sup2 ?_
        · rw [@disjoint_comm]
          exact this
        · rw [@Finset.disjoint_biUnion_left]
          intro I hI
          simp only [Finset.coe_insert, pairwiseDisjoint_insert] at hst
          rw [@disjoint_comm]
          apply hst.2 I (hI) (Ne.symm (ne_of_mem_of_not_mem hI hi))
  · intro h
    refine Finset.sum_eq_zero ?mpr.h
    simpa using h

private lemma disjoint_sdiff_inter_sdiff
    {α : Type*} (a b : Finset α) :
    Disjoint (a \ (a ∩ b)) (b \ (a ∩ b)) := by
  simp [Finset.disjoint_iff_inter_eq_empty]
  rw [← Finset.inter_sdiff_assoc]
  simp only [Finset.sdiff_inter_self, Finset.empty_sdiff]

private lemma disjoint_sdiff_self_inter
    {α : Type*} (a b : Finset α) :
    Disjoint (a \ (a ∩ b)) ((a ∩ b)) := by
  simp [Finset.disjoint_iff_inter_eq_empty]
  refine Finset.disjoint_iff_inter_eq_empty.mp ?_
  exact Finset.disjoint_sdiff_inter a b

omit [IsDomain Z] in
private lemma eq_of_sum_single_sdiff_eq_zero
    (s t : Finset (M P)) (x y : Z)
    (hst : ¬ s ⊆ t) (hts : ¬ t ⊆ s)
    (h : ∑ i ∈ (s \ t), single i x +
      ∑ j ∈ (t \ s), single j y = 0) :
    x = y := by
  have : Disjoint (s \ t) (t \ s) := by
    exact disjoint_sdiff_sdiff
  rw [sum_disj P Z (s \ t) (t \ s) (fun _ => x) (fun _ => y) this] at h
  have s1 := sum_single_eq_zero Z (s \ t) (fun _ => x) h.1
  have s2 := sum_single_eq_zero Z (t \ s) (fun _ => y) h.2
  rw [← Finset.sdiff_eq_empty_iff_subset] at hst hts
  simp [Finset.mem_sdiff, and_imp] at s1 s2
  rw [← @Finset.not_nonempty_iff_eq_empty, not_not] at hst hts
  have c1 : ∃ i ∈ s, i ∉ t := by
    have := Finset.Nonempty.exists_mem hst
    simpa using this
  have c2 : ∃ i ∈ t, i ∉ s := by
    have := Finset.Nonempty.exists_mem hts
    simpa using this
  obtain ⟨i, hi, hi2⟩ := c1
  obtain ⟨j, hj, hj2⟩ := c2
  have h1 := s1 i hi hi2
  have h2 := s2 j hj hj2
  rw [h1, h2]

omit [IsDomain Z] in
private lemma support_sum_single_const (s : Finset (M P)) (x : Z) (hx : x ≠ 0) :
  (∑ i ∈ s, single i x).support = s := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, support_zero]
  | insert i s hi hs =>
  rw [Finset.sum_insert hi, support_add_eq, hs, Finsupp.support_single_ne_zero i hx]
  rfl
  rwa [hs, Finsupp.support_single_ne_zero i hx, Finset.disjoint_singleton_left]

omit [IsDomain Z] in
private lemma finsupp_toFun_add (s t : 𝕄 P Z) : (s + t).toFun = s.toFun + t.toFun := rfl

omit [IsDomain Z] in
private lemma sum_single_toFun_eq_indicator (s : Finset (M P)) (x : Z):
  (∑ i ∈ s, single i x).toFun = Finsupp.indicator s (fun _ _ => x) := by
  ext t
  simp
  have : (∑ i ∈ s, single i x).toFun = ∑ i ∈ s, (single i x).toFun := by
    induction s using Finset.induction_on with
    | empty => simp; exact rfl
    | insert i s hi hs =>
    simp_rw [Finset.sum_insert hi]
    ext u
    rw [@Pi.add_apply, finsupp_toFun_add]
    simp [hs]
  rw [this, @Finset.sum_apply]
  conv =>
    enter [1,2]
    ext r
    rw [single]
    simp
    rw [Pi.single_apply]
  simp

omit [IsDomain Z] in
private lemma sum_single_disjoint_parts_eq_zero
    (s t : Finset (M P)) (x y z : Z)
    (h : ∑ i ∈ (s ∩ t), single i z +
      ∑ j ∈ (s \ t), single j y +
      ∑ k ∈ (t \ s), single k x = 0) :
    ∑ i ∈ (s ∩ t), single i z = 0 ∧
      ∑ j ∈ (s \ t), single j y = 0 ∧
      ∑ k ∈ (t \ s), single k x = 0 := by
  rw [add_assoc,
    single_basis Z (∑ j ∈ (s \ t), single j y +
      ∑ k ∈ (t \ s), single k x),
    sum_disj P Z (s ∩ t)
      (∑ j ∈ (s \ t), single j y +
        ∑ k ∈ (t \ s), single k x).support] at h
  simp only [h.1, true_and]
  have h2 := h.2
  simp at h2
  by_cases hy : y ≠ 0
  by_cases hx : x ≠ 0
  have h3 : ( ∑ j ∈ (s \ t), single j y +
    ∑ k ∈ (t \ s), single k x).support = (s \ t) ∪ (t \ s) := by
    have hh := support_add_eq (g₁ := ∑ j ∈ (s \ t), single j y)
      (g₂ := ∑ k ∈ (t \ s), single k x) ?_
    rw [hh, support_sum_single_const _ _ _ _ hx, support_sum_single_const _ _ _ _ hy]
    rw [support_sum_single_const _ _ _ _ hx, support_sum_single_const _ _ _ _ hy]
    exact disjoint_sdiff_sdiff
  rw [h3, Finset.sum_union (disjoint_sdiff_sdiff), sum_disj P Z (s \ t) (t \ s)] at h2
  conv at h2 =>
    enter [1,1,2]
    ext r
    rw [finsupp_toFun_add]
    simp
  conv at h2 =>
    enter [2,1,2]
    ext r
    rw [finsupp_toFun_add]
    simp
  simp_rw [sum_single_toFun_eq_indicator] at h2
  constructor
  · rw [← h2.1]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ne_eq, Finsupp.indicator_apply, Finset.mem_sdiff, dite_eq_ite] at *
    rw [if_pos hi]
    simp only [left_eq_add, single_eq_zero, ite_eq_right_iff, and_imp]
    intro _ hj
    exfalso
    exact hj hi.1
  · rw [← h2.2]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ne_eq, Finsupp.indicator_apply, Finset.mem_sdiff, dite_eq_ite] at *
    rw [if_pos hi]
    simp only [right_eq_add, single_eq_zero, ite_eq_right_iff, and_imp]
    intro _ hj
    exfalso
    exact hj hi.1
  · exact (disjoint_sdiff_sdiff)
  · simp only [ne_eq, Decidable.not_not] at hx
    rw [hx]
    simp only [single_zero, Finset.sum_const_zero, and_true]
    simp_rw [hx] at h2
    simp at h2
    rw [support_sum_single_const _ _ _ _ hy, sum_single_toFun_eq_indicator] at h2
    rw [← h2]
    apply Finset.sum_congr rfl
    intro i hi
    simp at *
    rw [if_pos hi]
  simp at hy
  by_cases hx : x ≠ 0
  rw [hy]
  simp
  simp_rw [hy] at h2
  simp at h2
  rw [support_sum_single_const _ _ _ _ hx, sum_single_toFun_eq_indicator] at h2
  rw [← h2]
  apply Finset.sum_congr rfl
  intro i hi
  simp at *
  rw [if_pos hi]
  simp at hx
  rw [hx, hy]
  simp
  have hh := support_add_eq (g₁ := ∑ j ∈ (s \ t), single j y)
      (g₂ := ∑ k ∈ (t \ s), single k x) ?_
  by_cases hx : x ≠ 0
  by_cases hy : y ≠ 0
  rw [support_sum_single_const _ _ _ _ hx, support_sum_single_const _ _ _ _ hy] at hh
  rw [hh, disjoint_comm]

  simp
  have t1 := disjoint_sdiff_self_inter s t
  have t2 := disjoint_sdiff_self_inter t s
  simp at t1 t2
  refine ⟨t1, ?_⟩
  rwa [Finset.inter_comm]
  simp at hy
  rw [hy]
  simp
  rw [support_sum_single_const _ _ _ _ hx, disjoint_comm, Finset.inter_comm]
  have := disjoint_sdiff_self_inter t s
  simpa using this
  simp at hx
  by_cases hy : y ≠ 0
  rw [hx]
  simp
  rw [support_sum_single_const _ _ _ _ hy, disjoint_comm]
  simpa using disjoint_sdiff_self_inter s t
  simp at hy
  rw [hx, hy]
  simp
  by_cases hx : x ≠ 0
  by_cases hy : y ≠ 0
  rw [support_sum_single_const _ _ _ _ hx, support_sum_single_const _ _ _ _ hy]
  exact (disjoint_sdiff_sdiff)
  simp at hy
  rw [hy]
  simp
  simp at hx
  rw [hx]
  simp

omit [IsDomain Z] in
private lemma sum_finset_single_indep2
    {s t : Finset (M P)} {x y : Z}
    (hs : s.Nonempty) (ht : t.Nonempty)
  (h : ∑ i ∈ s, single (i : M P) (x) = ∑ i ∈ t, single (i : M P) (y)) :
    ((s ∩ t) ≠ ∅ ∧ x = y) ∨ (x = 0 ∧ y = 0) := by
  by_cases h1 : (s ∩ t) = ∅
  simp [h1]
  have D : Disjoint s t := Finset.disjoint_iff_inter_eq_empty.mpr h1
  have : ∑ i ∈ s, single i (x) - ∑ i ∈ t, single i (y) = 0 := by
    rw [h, sub_self]
  rw [sub_eq_add_neg, ← @Finset.sum_neg_distrib] at this
  have hr := sum_disj P Z s t (fun _ => x) (fun _ => -y) D
  simp only [single_neg] at hr
  have tt := hr.mp this
  have t2 := sum_single_eq_zero Z s (fun _ => x) tt.1
  have tt2 := tt.2
  simp at tt2
  have t3 := sum_single_eq_zero Z t (fun _ => y) tt2
  have v1 := Finset.Nonempty.exists_mem hs
  have v2 := Finset.Nonempty.exists_mem ht
  obtain ⟨i, hi⟩ := v1
  obtain ⟨j, hj⟩ := v2
  have T1 := t2 i hi
  have T2 := t3 j hj
  simp at T1 T2
  refine ⟨T1, T2⟩
  simp [h1]
  left
  have hl : ∑ i ∈ s, single i x =
      ∑ i ∈ (s ∩ t), single i x +
      ∑ i ∈ s \ (s ∩ t), single i x := by
    have hss : (s ∩ t) ⊆ s := Finset.inter_subset_left
    rw [← Finset.sum_sdiff hss, add_comm]
  have hr : ∑ j ∈ t, single j y =
      ∑ j ∈ (s ∩ t), single j y +
      ∑ j ∈ t \ (s ∩ t), single j y := by
    have hss : (s ∩ t) ⊆ t := Finset.inter_subset_right
    rw [← Finset.sum_sdiff hss, add_comm]
  rw [hr, hl, ← @add_neg_eq_iff_eq_add, ← sub_eq_zero] at h
  simp at h
  have e1 : ∑ i ∈ s ∩ t, single i x + ∑ i ∈ s \ t, single i x +
    -∑ x ∈ t \ s, single x y - ∑ x ∈ s ∩ t, single x y = (∑ i ∈ s ∩ t, single i x
       - ∑ x ∈ s ∩ t, single x y) +
    ∑ i ∈ s \ t, single i x + -∑ x ∈ t \ s, single x y := by abel
  have e2 : (∑ i ∈ s ∩ t, single i x - ∑ x ∈ s ∩ t, single x y) = (∑ i ∈ s ∩ t,
    (single i x - single i y)) := by
    simp only [Finset.sum_sub_distrib]
  rw [e1,e2] at h
  conv at h =>
    enter [1,1,1,2]
    ext t
    rw [← single_sub]
  by_cases hxy : x = y
  · exact hxy
  have := sum_single_disjoint_parts_eq_zero P Z s t (-y) (x) (x-y)
  simp only [single_neg, Finset.sum_neg_distrib, neg_eq_zero] at this
  have G := this h
  have G1 := G.1
  have := sum_single_eq_zero Z (s ∩ t) (fun _ => x - y) G1
  simp at this
  rw [@sub_eq_zero] at this
  rw [← @Finset.not_nonempty_iff_eq_empty, not_not] at h1
  have c1 : ∃ i ∈ s, i ∈ t := by
    have := Finset.Nonempty.exists_mem h1
    simpa using this
  obtain ⟨i, hi, hi2⟩ := c1
  apply this i hi hi2

omit [IsDomain Z] in
lemma smul_add_left (T₁ T₂ : 𝕋 P Z) (m : 𝕄 P Z) :
    (T₁ + T₂) • m = T₁ • m + T₂ • m := by
  simp only [smul_eq_sum]
  rw [Finsupp.sum_add_index]
  · intro D1 _
    simp only [zero_mul, Finsupp.single_zero, Finset.sum_const_zero, Finsupp.sum_zero]
  · intro D1 _ y b₂
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _
    simp_rw [add_mul, Finsupp.single_add]

omit [IsDomain Z] in
private lemma smul_add (s : Finset (T' P)) (r : T' P → Z) (a : 𝕄 P Z) :
  (∑ i ∈ s, (T_single P Z i (r i))) • a = (∑ i ∈ s, (T_single P Z i (r i)) • a) := by
  induction s using Finset.induction_on with
  | empty => simp [smul_eq_sum, Finsupp.sum_zero_index]
  | @insert x s hni ih => rw [Finset.sum_insert hni, smul_add_left, ih, Finset.sum_insert hni]

omit [IsDomain Z] in
lemma zero_smul_𝕄 (z : 𝕄 P Z) : (0 : 𝕋 P Z) • z = 0 := by
  simp only [smul_eq_sum]; exact Finsupp.sum_zero_index

omit [IsDomain Z] in
lemma smul_zero_𝕄 (T : 𝕋 P Z) : T • (0 : 𝕄 P Z) = 0 := by
  simp only [smul_eq_sum, Finsupp.sum_zero_index, Finsupp.sum_zero]

omit [IsDomain Z] in
lemma smul_add_right (T : 𝕋 P Z) (m₁ m₂ : 𝕄 P Z) :
    T • (m₁ + m₂) = T • m₁ + T • m₂ := by
  simp only [smul_eq_sum]
  have inner_split : ∀ D (b : Z),
      (m₁ + m₂).sum (fun m c => ∑ i ∈ smulOrbit P D m, Finsupp.single i (b * c)) =
      m₁.sum (fun m c => ∑ i ∈ smulOrbit P D m, Finsupp.single i (b * c)) +
      m₂.sum (fun m c => ∑ i ∈ smulOrbit P D m, Finsupp.single i (b * c)) := by
    intro D b
    rw [Finsupp.sum_add_index']
    · intro m; simp [mul_zero, Finsupp.single_zero, Finset.sum_const_zero]
    · intro m c₁ c₂
      simp only [← Finset.sum_add_distrib, mul_add, Finsupp.single_add]
  simp_rw [inner_split]
  rw [← Finsupp.sum_add]

lemma smulOrbit_disjoint_of_ne (D₁ D₂ : T' P) (m : M P) (hne : D₁ ≠ D₂) :
    Disjoint (smulOrbit P D₁ m) (smulOrbit P D₂ m) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  apply hne; apply HeckeRing.T'_ext P
  simp only [smulOrbit, Finset.mem_image] at hx₁ hx₂
  obtain ⟨i₁, _, hi₁⟩ := hx₁; obtain ⟨i₂, _, hi₂⟩ := hx₂
  rw [← hi₂] at hi₁
  have hset := congr_arg M.set hi₁
  simp only [M_mk] at hset
  have hmem : (m.eql.choose : G) * ↑(Quotient.out i₁) * (D₁.eql.choose : G) ∈
      ({(m.eql.choose : G) * ↑(Quotient.out i₂) * (D₂.eql.choose : G)} : Set G) *
      (↑P.H : Set G) := by
    rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have hstep : ↑(Quotient.out i₂) * (D₂.eql.choose : G) * k =
      ↑(Quotient.out i₁) * (D₁.eql.choose : G) := by
    have h : (m.eql.choose : G) * (↑(Quotient.out i₂) * (D₂.eql.choose : G) * k) =
        (m.eql.choose : G) * (↑(Quotient.out i₁) * (D₁.eql.choose : G)) := by
      have := hkk; dsimp at this; group at this ⊢; exact this
    exact mul_left_cancel h
  have hg : (D₁.eql.choose : G) =
      ↑((Quotient.out i₁)⁻¹ * Quotient.out i₂) * (D₂.eql.choose : G) * k := by
    apply mul_left_cancel (a := (↑(Quotient.out i₁) : G))
    have : ↑(Quotient.out i₁) * (↑((Quotient.out i₁)⁻¹ * Quotient.out i₂) *
        (D₂.eql.choose : G) * k) = ↑(Quotient.out i₂) * (D₂.eql.choose : G) * k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]; exact hstep.symm
  rw [D₁.eql.choose_spec, D₂.eql.choose_spec]
  conv_lhs => rw [hg]
  exact (DoubleCoset.doubleCoset_mul_right_eq_self P ⟨k, hk⟩ _).trans
    (doset_mul_left_eq_self P ((Quotient.out i₁)⁻¹ * Quotient.out i₂) _)

omit [IsDomain Z] in
private lemma smul_one_eval (T : 𝕋 P Z) (D : T' P) (m : M P)
    (hm : m ∈ smulOrbit P D (M_one P)) :
    (T • (1 : 𝕄 P Z)).toFun m = T.toFun D := by
  rw [smul_eq_sum, one_eq_M_single]
  have hsimp : ∀ D1 (b₁ : Z),
      Finsupp.sum (Finsupp.single (M_one P) (1 : Z))
        (fun m' b₂ => ∑ i ∈ smulOrbit P D1 m', Finsupp.single i (b₁ * b₂)) =
      ∑ i ∈ smulOrbit P D1 (M_one P), Finsupp.single i b₁ := by
    intro D1 b1
    rw [Finsupp.sum_single_index
      (by simp [mul_zero, Finsupp.single_zero, Finset.sum_const_zero]), mul_one]
  simp_rw [hsimp]; unfold Finsupp.sum
  show (∑ x ∈ T.support,
    ∑ i ∈ smulOrbit P x (M_one P),
      Finsupp.single i (T.toFun x)) m = T.toFun D
  rw [Finsupp.finset_sum_apply]
  simp_rw [Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single D]
  · rw [Finset.sum_eq_single_of_mem m hm (fun b _ hb => if_neg hb), if_pos rfl]
  · intro D' _ hne
    exact Finset.sum_eq_zero fun i hi =>
      if_neg (fun heq => absurd (heq ▸ hi)
        (Finset.disjoint_left.mp (smulOrbit_disjoint_of_ne P D D' (M_one P) (Ne.symm hne)) hm))
  · intro hns
    exact Finset.sum_eq_zero fun x _ => by
      have h0 : T.toFun D = 0 := Finsupp.notMem_support_iff.mp hns
      simp [h0]

omit [IsDomain Z] in
lemma 𝕋_eq_of_smul_eq_smul (T1 T2 : (𝕋 P Z))
    (h : ∀ (a : 𝕄 P Z), T1 • a = T2 • a) :
    T1 = T2 :=
  Finsupp.ext fun D => by
    obtain ⟨m, hm⟩ := smulOrbit_nonempty P D (M_one P)
    have h1 := congrFun (congrArg Finsupp.toFun (h 1)) m
    rwa [smul_one_eval P Z T1 D m hm, smul_one_eval P Z T2 D m hm] at h1

noncomputable instance instFaithfulSMul𝕄 : FaithfulSMul (𝕋 P ℤ) (𝕄 P ℤ) where
  eq_of_smul_eq_smul {t1 t2} h := 𝕋_eq_of_smul_eq_smul P ℤ t1 t2 h

lemma smul_def (f g : 𝕋 P ℤ) : f • g = g * f := rfl
