/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.Int.Star
import Mathlib.GroupTheory.Commensurable
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Group

/-!
# Hecke Rings: Basic Definitions

Basic definitions for Hecke rings following Shimura Ch. 3: `ArithmeticGroupPair`, double coset
spaces `T'` and `M`, the Hecke ring type `𝕋`, and foundational double coset lemmas.
-/

open Commensurable Classical Doset MulOpposite Set DoubleCoset Subgroup
  Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

lemma conjAct_smul_coe_eq (g : G) : ((ConjAct.toConjAct g • H) : Set G) = {g} * H * {g⁻¹} := by
  ext x
  refine ⟨?_, ?_⟩ <;> intro h
  · rw [mem_smul_set] at h
    obtain ⟨a, ha⟩ := h
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at ha
    rw [← ha.2]
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right, inv_inv, mem_preimage,
      inv_mul_cancel_right, inv_mul_cancel_left, ha.1]
  · rw [mem_smul_set]
    use g⁻¹ * x * g
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    group
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right, inv_inv, mem_preimage,
      SetLike.mem_coe, Int.reduceNeg, zpow_neg, zpow_one, and_true] at *
    rwa [← mul_assoc] at h

lemma conjAct_smul_elt_eq (h : H) : ConjAct.toConjAct (h : G) • H = H := by
  have : ConjAct.toConjAct (h : G) • (H : Set G) = H := by
    rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h.2,
      Subgroup.subgroup_mul_singleton (by simp)]
  rw [← Subgroup.coe_pointwise_smul] at this
  norm_cast at *

lemma leftCoset_eq_of_subset (a b : G)
    (h : {a} * (H : Set G) ⊆ {b} * H) :
    {a} * (H : Set G) = {b} * H := by
  have ha : a ∈ {a} * (H : Set G) := by
    rw [Set.mem_mul]
    use a
    simp
  have hb := h ha
  rw [Set.mem_mul] at hb
  obtain ⟨b', hb', y, hy, hb_eq⟩ := hb
  simp at hb'
  rw [← hb_eq, hb', ← Set.singleton_mul_singleton,
    mul_assoc, Subgroup.singleton_mul_subgroup hy]

/-- An arithmetic group pair `(H, Δ)` consisting of a subgroup `H` and a submonoid `Δ` of a
group `G`, satisfying `H ≤ Δ ≤ commensurator(H)`. This is the data needed to construct
a Hecke ring. -/
structure ArithmeticGroupPair (G : Type*) [Group G] where
  H : Subgroup G
  Δ : Submonoid G
  h₀ : H.toSubmonoid ≤ Δ
  h₁ : Δ ≤ (commensurator H).toSubmonoid

/-- Given an arithmetic pair `P`, consisting of a subgroup `H` of `G` and a submonoid `Δ` of
the commensurator of H, this is the data of a set in `G` equal to some double coset
`HgH`, with `g : Δ`. -/
structure T' (P : ArithmeticGroupPair G) where
  set : Set G
  eql : ∃ elt : P.Δ, set = DoubleCoset.doubleCoset (elt : G) P.H P.H

/-- A left coset `gH` with `g ∈ Δ`. -/
structure M (P : ArithmeticGroupPair G) where
  set : Set G
  eql : ∃ elt : P.Δ, set = {(elt : G)} * (P.H : Set G)

@[ext]
lemma T'_ext (P : ArithmeticGroupPair G) (D1 D2 : T' P) (h : D1.set = D2.set): D1 = D2 := by
  cases D1; cases D2; simp_all

/-- Make an element of `T' P` given an element `g : P.Δ`, i.e make `HgH`. -/
def T_mk (P : ArithmeticGroupPair G) (g : P.Δ) : T' P :=
  ⟨DoubleCoset.doubleCoset g P.H P.H, g, rfl⟩

/-- Make an element of `M P` given an element `g : P.Δ`, i.e make `gH`. -/
def M_mk (P : ArithmeticGroupPair G) (g : P.Δ) : M P := ⟨{(g : G)} * (P.H : Set G), g, rfl⟩

/-- The multiplicative identity. -/
def T_one (P : ArithmeticGroupPair G) : T' P := T_mk P (1 : P.Δ)

lemma T_one_eq (P : ArithmeticGroupPair G) : T_one P = T_mk P (1 : P.Δ) := rfl

lemma T_one_eq_doset_one (P : ArithmeticGroupPair G) :
    T_one P =
      ⟨DoubleCoset.doubleCoset (1 : P.Δ) P.H P.H, 1, rfl⟩ :=
  rfl

lemma T_one_choose_doubleCoset_eq (P : ArithmeticGroupPair G) :
    DoubleCoset.doubleCoset ((T_one P).eql.choose : G)
      P.H P.H =
    DoubleCoset.doubleCoset (1 : G) P.H P.H := by
  have := (T_one P).eql.choose_spec
  rw [T_one_eq_doset_one] at this
  simpa using this.symm

lemma T_one_choose_eq (P : ArithmeticGroupPair G) : ∃ h₁ h₂ : P.H,
    h₁ * ((T_one P).eql.choose : G) * h₂ = 1 := by
  have := (T_one P).eql.choose_spec
  rw [T_one, T_mk] at this
  have h2 := (DoubleCoset.eq P.H P.H _ _).mp (DoubleCoset.mk_eq_of_doubleCoset_eq this.symm)
  obtain ⟨h₁, h1, h₂, h2 ⟩ := h2
  refine ⟨⟨h₁,h1⟩, ⟨h₂,h2.1⟩,h2.2.symm⟩

lemma T_one_choose_mem_H (P : ArithmeticGroupPair G) : ((T_one P).eql.choose : G) ∈ P.H := by
  obtain ⟨h₁, h₂, h₃⟩ := T_one_choose_eq P
  rw [@mul_eq_one_iff_eq_inv, ← @eq_inv_mul_iff_mul_eq] at h₃
  rw [h₃]
  apply Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁.2) (Subgroup.inv_mem _ h₂.2)

lemma doset_mul_left_eq_self (P : ArithmeticGroupPair G)
    (h : P.H) (g : G) :
    DoubleCoset.doubleCoset ((h : G) * g) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← singleton_mul_singleton, ← mul_assoc]
  conv =>
    enter [1,1,1]
    rw [Subgroup.subgroup_mul_singleton h.2]

lemma DoubleCoset.doubleCoset_mul_right_eq_self
    (P : ArithmeticGroupPair G) (h : P.H) (g : G) :
    DoubleCoset.doubleCoset (g * h) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← singleton_mul_singleton, ← mul_assoc]
  conv =>
    enter [1]
    rw [mul_assoc]
    rw [Subgroup.singleton_mul_subgroup h.2]

lemma DoubleCoset.doubleCoset_mul_assoc (f g h : G) :
    DoubleCoset.doubleCoset ((f * g) * h) H H =
    DoubleCoset.doubleCoset (f * (g * h)) H H := by
  simp_rw [DoubleCoset.doubleCoset, ← singleton_mul_singleton, ← mul_assoc]

/-- The identity left coset `1 · H = H`. -/
def M_one (P : ArithmeticGroupPair G) : M P := M_mk P (1 : P.Δ)

lemma smul_eq_singleton_mul (s : Set G) (g : G) : g • s = {g} * s :=
    Set.singleton_smul.symm

lemma set_eq_iUnion_leftCosets (K : Subgroup G)
    (hK : K ≤ H) : (H : Set G) =
    ⋃ (i : H ⧸ K.subgroupOf H),
      (i.out : G) • (K : Set G) := by
  ext a
  constructor
  · intro ha
    simp only [mem_iUnion]
    use (⟨a, ha⟩ : H)
    have := QuotientGroup.mk_out_eq_mul (K.subgroupOf H) (⟨a, ha⟩ : H)
    obtain ⟨h, hh⟩ := this
    rw [hh]
    simp
    refine mem_smul_set.mpr ?h.intro.a
    have : (h : H) • (K : Set G) = K := by
      apply smul_coe_set
      refine Subgroup.mem_subgroupOf.mp ?ha.a
      simp only [SetLike.coe_mem]
    use h⁻¹
    simp
    refine Subgroup.mem_subgroupOf.mp ?h.a
    exact SetLike.coe_mem h
  · intro ha
    simp only [mem_iUnion] at ha
    obtain ⟨i, hi⟩ := ha
    have : Quotient.out i • (K : Set G) ⊆ (H : Set G) := by
      intro a ha
      rw [mem_smul_set] at ha
      obtain ⟨h, hh⟩ := ha
      rw [← hh.2]
      simp
      rw [show Quotient.out i • h = Quotient.out i * h from rfl]
      apply mul_mem
      simp
      apply hK hh.1
    exact this hi

lemma conjAct_mul_self_eq_self (g : G) : ((ConjAct.toConjAct g • H) : Set G) *
    (ConjAct.toConjAct g • H) = (ConjAct.toConjAct g • H) := by
  rw [conjAct_smul_coe_eq,
    show {g} * (H : Set G) * {g⁻¹} * ({g} * ↑H * {g⁻¹}) =
      {g} * ↑H * (({g⁻¹} * {g}) * ↑H) * {g⁻¹} by
        simp_rw [← mul_assoc],
    Set.singleton_mul_singleton]
  conv =>
    enter [1,1,2]
    simp
  conv =>
    enter [1,1]
    rw [mul_assoc, coe_mul_coe H]

lemma inter_mul_conjAct_eq_conjAct (g : G) : ((H : Set G) ∩ (ConjAct.toConjAct g • H)) *
    (ConjAct.toConjAct g • H) = (ConjAct.toConjAct g • H) := by
  have := Set.inter_mul_subset (s₁ := (H : Set G)) (s₂ := (ConjAct.toConjAct g • H))
    (t := (ConjAct.toConjAct g • H))
  apply Subset.antisymm
  · apply le_trans this
    simp only [conjAct_mul_self_eq_self, le_eq_subset, inter_subset_right]
  · refine subset_mul_right (ConjAct.toConjAct g • (H : Set G)) ?h₂.hs
    simp only [mem_inter_iff, SetLike.mem_coe]
    refine ⟨ Subgroup.one_mem H, Subgroup.one_mem (ConjAct.toConjAct g • H)⟩

lemma mul_singleton_right_cancel (g : G) (K L : Set G) (h : K * {g} = L * {g}) : K = L := by
  have h2 := congrFun (congrArg HMul.hMul h) {g⁻¹}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at h2
  simpa using h2

lemma DoubleCoset.doubleCoset_eq_iUnion_leftCosets (g : G) : DoubleCoset.doubleCoset g H H =
  ⋃ (i : (H ⧸ (ConjAct.toConjAct g • H).subgroupOf H)), (i.out * g) • (H : Set G) := by
  rw [DoubleCoset.doubleCoset]
  have := set_eq_iUnion_leftCosets H (((ConjAct.toConjAct g • H).subgroupOf H).map H.subtype)
  simp only [Subgroup.subgroupOf_map_subtype, inf_le_right, Subgroup.coe_inf,
    Subgroup.coe_pointwise_smul, true_implies] at this
  have h2 := congrFun (congrArg HMul.hMul this) ((ConjAct.toConjAct g • H) : Set G)
  rw [iUnion_mul, inter_comm] at h2
  apply mul_singleton_right_cancel g⁻¹
  rw [conjAct_smul_coe_eq ] at *
  simp_rw [← mul_assoc] at h2
  rw [h2]
  have : (Subgroup.map H.subtype ((ConjAct.toConjAct g • H).subgroupOf H)).subgroupOf H =
    (ConjAct.toConjAct g • H).subgroupOf H := by
    simp
  rw [this]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
    ((i.out) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹} =
      (↑(Quotient.out i) * g) • ↑H * {g⁻¹} := by
    intro i
    have := inter_mul_conjAct_eq_conjAct H g
    rw [conjAct_smul_coe_eq ] at this
    have hr : ((i.out ) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹} =
      (i.out : G) • (((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) * {g} * ↑H * {g⁻¹}) := by
      simp_rw [smul_mul_assoc]
    rw [hr]
    simp_rw [← mul_assoc] at this
    conv =>
      enter [1,2]
      rw [this]
    simp_rw [smul_eq_singleton_mul, ← singleton_mul_singleton, ← mul_assoc]
  have := iUnion_congr h1
  convert this
  rw [iUnion_mul]

lemma doubleCoset_mul_doubleCoset_left (g h : G) :
    (DoubleCoset.doubleCoset g H H) *
      (DoubleCoset.doubleCoset h H H) =
    (DoubleCoset.doubleCoset (g) H H) * {h} * H := by
  simp_rw [DoubleCoset.doubleCoset,
    show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
      H * {g} * (H * H) * {h} * H by
        simp_rw [← mul_assoc],
    coe_mul_coe H]

lemma doubleCoset_mul_doubleCoset_right (g h : G) :
    (DoubleCoset.doubleCoset g H H) *
      (DoubleCoset.doubleCoset h H H) =
    H * {g} * (DoubleCoset.doubleCoset (h) H H) := by
  simp_rw [DoubleCoset.doubleCoset,
    show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
      H * {g} * (H * H) * {h} * H by
        simp_rw [← mul_assoc],
    coe_mul_coe H, ← mul_assoc]

lemma doubleCoset_mul_eq_iUnion_doubleCoset (g h : G) :
    (DoubleCoset.doubleCoset (g : G) (H : Set G) H) *
      DoubleCoset.doubleCoset (h : G) (H : Set G) H =
    ⋃ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
      DoubleCoset.doubleCoset (g * i.out * h : G)
        H H := by
  rw [doubleCoset_mul_doubleCoset_right,
    DoubleCoset.doubleCoset_eq_iUnion_leftCosets,
    Set.mul_iUnion]
  simp_rw [DoubleCoset.doubleCoset]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
    (H : Set G) * {g} *
      (↑(Quotient.out i) * h) • ↑H =
    ↑H * {g * ↑(Quotient.out i) * h} * ↑H := by
    intro i
    rw [smul_eq_singleton_mul, show (H : Set G) * {g} * ({↑(Quotient.out i) * h} * ↑H) =
      H * {g} * {↑(Quotient.out i) * h} * ↑H by simp_rw [← mul_assoc],
        ← Set.singleton_mul_singleton,
        ← Set.singleton_mul_singleton,
        ← Set.singleton_mul_singleton]
    simp_rw [← mul_assoc]
  apply iUnion_congr h1

lemma DoubleCoset.doubleCoset_one_mul (h : G) :
    DoubleCoset.doubleCoset (h : G) (H : Set G) H =
    ⋃ (_ : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
      DoubleCoset.doubleCoset (h : G) H H := by
  simp [iUnion_const]

/-- Finite linear combinations of double cosets `HgH` with `g` in the commensurator of `H`. -/
def 𝕋 (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] := Finsupp (T' P) Z

def 𝕄 (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] := Finsupp (M P) Z

variable (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] [IsDomain Z]

noncomputable instance (P : ArithmeticGroupPair G) (D : T' P) :
    Fintype (P.H ⧸ ((ConjAct.toConjAct (D.eql.choose : G)) • P.H).subgroupOf P.H) :=
  Subgroup.fintypeOfIndexNeZero (P.h₁ D.eql.choose.2).1

lemma delta_mul_mem (i : H) (a b : Δ) (h₀ : H.toSubmonoid ≤ Δ) : a * (i : G) * b ∈ Δ := by
  rw [mul_assoc]
  exact Submonoid.mul_mem _ a.2 (Submonoid.mul_mem _ (h₀ i.2) b.2)

noncomputable instance instAddCommGroup𝕋 : AddCommGroup (𝕋 P Z) :=
  inferInstanceAs (AddCommGroup ((T' P) →₀ Z))

noncomputable instance instAddCommGroup𝕄 : AddCommGroup (𝕄 P Z) :=
  inferInstanceAs (AddCommGroup ((M P) →₀ Z))

/-- The quotient `H / (H ∩ gHg⁻¹)` indexing right coset representatives in `HgH`. -/
abbrev decompQuot (D : T' P) :=
  (P.H ⧸ (ConjAct.toConjAct (D.eql.choose : G) •
    P.H).subgroupOf P.H)
