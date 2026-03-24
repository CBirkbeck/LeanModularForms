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

Basic definitions for Hecke rings following Shimura Ch. 3: `HeckePair`, double coset
spaces `HeckeCoset` and `HeckeLeftCoset`, the Hecke ring type `𝕋`, and foundational double coset lemmas.
-/

open Commensurable Classical MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G)
  (h₀ : H.toSubmonoid ≤ Δ) (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

/-- The conjugation action on `H` as a set product: `gHg⁻¹ = {g} * H * {g⁻¹}`. -/
lemma conjAct_smul_coe_eq (g : G) :
    ((ConjAct.toConjAct g • H) : Set G) = {g} * H * {g⁻¹} := by
  ext x; refine ⟨?_, ?_⟩ <;> intro h
  · rw [Set.mem_smul_set] at h; obtain ⟨a, ha⟩ := h
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct] at ha; rw [← ha.2]
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right,
      inv_inv, mem_preimage, inv_mul_cancel_right, inv_mul_cancel_left, ha.1]
  · rw [Set.mem_smul_set]; use g⁻¹ * x * g
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]; group
    simp only [singleton_mul, image_mul_left, mul_singleton, image_mul_right,
      inv_inv, mem_preimage, SetLike.mem_coe, Int.reduceNeg, zpow_neg, zpow_one,
      and_true] at *
    rwa [← mul_assoc] at h

/-- Conjugation by an element of `H` fixes `H`. -/
lemma conjAct_smul_elt_eq (h : H) :
    ConjAct.toConjAct (h : G) • H = H := by
  have : ConjAct.toConjAct (h : G) • (H : Set G) = H := by
    rw [conjAct_smul_coe_eq, Subgroup.singleton_mul_subgroup h.2,
      Subgroup.subgroup_mul_singleton (by simp)]
  rw [← Subgroup.coe_pointwise_smul] at this; norm_cast at *

/-- A left coset contained in another left coset is equal to it. -/
lemma leftCoset_eq_of_subset (a b : G)
    (h : {a} * (H : Set G) ⊆ {b} * H) : {a} * (H : Set G) = {b} * H := by
  have ha : a ∈ {a} * (H : Set G) := by rw [Set.mem_mul]; use a; simp
  have hb := h ha; rw [Set.mem_mul] at hb
  obtain ⟨b', hb', y, hy, hb_eq⟩ := hb; simp at hb'
  rw [← hb_eq, hb', ← Set.singleton_mul_singleton, mul_assoc,
    Subgroup.singleton_mul_subgroup hy]

/-- An arithmetic group pair `(H, Δ)` consisting of a subgroup `H` and a submonoid `Δ`
of a group `G`, satisfying `H ≤ Δ ≤ commensurator(H)`. -/
structure HeckePair (G : Type*) [Group G] where
  H : Subgroup G
  Δ : Submonoid G
  h₀ : H.toSubmonoid ≤ Δ
  h₁ : Δ ≤ (commensurator H).toSubmonoid

/-- A set in `G` equal to some double coset `HgH` with `g : Δ`. -/
structure HeckeCoset (P : HeckePair G) where
  carrier : Set G
  doubleCoset_eq : ∃ elt : P.Δ, carrier = DoubleCoset.doubleCoset (elt : G) P.H P.H

/-- A left coset `gH` with `g ∈ Δ`. -/
structure HeckeLeftCoset (P : HeckePair G) where
  carrier : Set G
  leftCoset_eq : ∃ elt : P.Δ, carrier = {(elt : G)} * (P.H : Set G)

/-- Two double cosets in `HeckeCoset` are equal if their underlying sets are equal. -/
@[ext] lemma HeckeCoset_ext (P : HeckePair G) (D1 D2 : HeckeCoset P)
    (h : D1.carrier = D2.carrier) : D1 = D2 := by cases D1; cases D2; simp_all

/-- The chosen Δ-representative of a double coset. -/
noncomputable def HeckeCoset_rep {P : HeckePair G} (D : HeckeCoset P) : P.Δ :=
  D.doubleCoset_eq.choose

/-- The double coset equals `H · rep · H`. -/
lemma HeckeCoset_set_eq_doubleCoset {P : HeckePair G} (D : HeckeCoset P) :
    D.carrier = DoubleCoset.doubleCoset (HeckeCoset_rep D : G) P.H P.H :=
  D.doubleCoset_eq.choose_spec

/-- The representative lies in its own double coset. -/
lemma HeckeCoset_rep_mem {P : HeckePair G} (D : HeckeCoset P) :
    (HeckeCoset_rep D : G) ∈ D.carrier := by
  rw [HeckeCoset_set_eq_doubleCoset]; exact DoubleCoset.mem_doubleCoset_self P.H P.H _

/-- Make an element of `HeckeCoset P` given an element `g : P.Δ`, i.e. make `HgH`. -/
def HeckeCoset.mk' (P : HeckePair G) (g : P.Δ) : HeckeCoset P :=
  ⟨DoubleCoset.doubleCoset g P.H P.H, g, rfl⟩

/-- Make an element of `HeckeLeftCoset P` given an element `g : P.Δ`, i.e. make `gH`. -/
def HeckeLeftCoset.mk' (P : HeckePair G) (g : P.Δ) : HeckeLeftCoset P :=
  ⟨{(g : G)} * (P.H : Set G), g, rfl⟩

/-- The identity double coset `H · 1 · H = H`. -/
def HeckeCoset.one (P : HeckePair G) : HeckeCoset P := HeckeCoset.mk' P (1 : P.Δ)

/-- `HeckeCoset.one` is definitionally `HeckeCoset.mk' P 1`. -/
lemma T_one_eq (P : HeckePair G) : HeckeCoset.one P = HeckeCoset.mk' P (1 : P.Δ) :=
  rfl

/-- `HeckeCoset.one` is the double coset of the identity element. -/
lemma T_one_eq_doset_one (P : HeckePair G) :
    HeckeCoset.one P =
      ⟨DoubleCoset.doubleCoset (1 : P.Δ) P.H P.H, 1, rfl⟩ := rfl

/-- The chosen representative of `HeckeCoset.one` has the same double coset as `1`. -/
lemma T_one_choose_doubleCoset_eq (P : HeckePair G) :
    DoubleCoset.doubleCoset ((HeckeCoset.one P).doubleCoset_eq.choose : G) P.H P.H =
    DoubleCoset.doubleCoset (1 : G) P.H P.H := by
  have := (HeckeCoset.one P).doubleCoset_eq.choose_spec
  rw [T_one_eq_doset_one] at this; simpa using this.symm

/-- The chosen representative of `HeckeCoset.one` is the product of two elements of `H` with `1`. -/
lemma T_one_choose_eq (P : HeckePair G) :
    ∃ h₁ h₂ : P.H, h₁ * ((HeckeCoset.one P).doubleCoset_eq.choose : G) * h₂ = 1 := by
  have := (HeckeCoset.one P).doubleCoset_eq.choose_spec; rw [HeckeCoset.one, HeckeCoset.mk'] at this
  have h2 := (DoubleCoset.eq P.H P.H _ _).mp
    (DoubleCoset.mk_eq_of_doubleCoset_eq this.symm)
  obtain ⟨h₁, h1, h₂, h2⟩ := h2
  exact ⟨⟨h₁, h1⟩, ⟨h₂, h2.1⟩, h2.2.symm⟩

/-- The chosen representative of `HeckeCoset.one` belongs to `H`. -/
lemma T_one_choose_mem_H (P : HeckePair G) :
    ((HeckeCoset.one P).doubleCoset_eq.choose : G) ∈ P.H := by
  obtain ⟨h₁, h₂, h₃⟩ := T_one_choose_eq P
  rw [@mul_eq_one_iff_eq_inv, ← @eq_inv_mul_iff_mul_eq] at h₃; rw [h₃]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁.2) (Subgroup.inv_mem _ h₂.2)

/-- Left-multiplying the representative by an element of `H` does not change the double coset. -/
lemma doset_mul_left_eq_self (P : HeckePair G) (h : P.H) (g : G) :
    DoubleCoset.doubleCoset ((h : G) * g) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]
  conv => enter [1, 1, 1]; rw [Subgroup.subgroup_mul_singleton h.2]

/-- Right-multiplying the representative by an element of `H` does not change the double coset. -/
lemma DoubleCoset.doubleCoset_mul_right_eq_self (P : HeckePair G)
    (h : P.H) (g : G) : DoubleCoset.doubleCoset (g * h) P.H P.H =
    DoubleCoset.doubleCoset g P.H P.H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]
  conv => enter [1]; rw [mul_assoc, Subgroup.singleton_mul_subgroup h.2]

/-- Associativity of group multiplication lifts to double coset representatives. -/
lemma DoubleCoset.doubleCoset_mul_assoc (f g h : G) :
    DoubleCoset.doubleCoset ((f * g) * h) H H =
    DoubleCoset.doubleCoset (f * (g * h)) H H := by
  simp_rw [DoubleCoset.doubleCoset, ← Set.singleton_mul_singleton, ← mul_assoc]

/-- The identity left coset `1 · H = H`. -/
def HeckeLeftCoset.one (P : HeckePair G) : HeckeLeftCoset P := HeckeLeftCoset.mk' P (1 : P.Δ)

/-- Scalar multiplication by a group element is the same as singleton set multiplication. -/
lemma smul_eq_singleton_mul (s : Set G) (g : G) : g • s = {g} * s :=
  Set.singleton_smul.symm

/-- A subgroup `H` is the union of left cosets of any sub-subgroup `K ≤ H`. -/
lemma set_eq_iUnion_leftCosets (K : Subgroup G) (hK : K ≤ H) :
    (H : Set G) = ⋃ (i : H ⧸ K.subgroupOf H), (i.out : G) • (K : Set G) := by
  ext a; constructor
  · intro ha; simp only [Set.mem_iUnion]
    use (⟨a, ha⟩ : H)
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf H) (⟨a, ha⟩ : H)
    rw [hh]; simp
    refine Set.mem_smul_set.mpr ?h.intro.a
    have : (h : H) • (K : Set G) = K := by
      apply smul_coe_set; exact Subgroup.mem_subgroupOf.mp (SetLike.coe_mem _)
    use h⁻¹; simp; exact Subgroup.mem_subgroupOf.mp (SetLike.coe_mem h)
  · intro ha; simp only [Set.mem_iUnion] at ha; obtain ⟨i, hi⟩ := ha
    have : Quotient.out i • (K : Set G) ⊆ (H : Set G) := by
      intro a ha; rw [Set.mem_smul_set] at ha; obtain ⟨h, hh⟩ := ha
      rw [← hh.2]; simp
      rw [show Quotient.out i • h = Quotient.out i * h from rfl]
      exact mul_mem (by simp) (hK hh.1)
    exact this hi

/-- The conjugate subgroup `gHg⁻¹` is closed under multiplication. -/
lemma conjAct_mul_self_eq_self (g : G) :
    ((ConjAct.toConjAct g • H) : Set G) * (ConjAct.toConjAct g • H) =
    (ConjAct.toConjAct g • H) := by
  rw [conjAct_smul_coe_eq,
    show {g} * (H : Set G) * {g⁻¹} * ({g} * ↑H * {g⁻¹}) =
      {g} * ↑H * (({g⁻¹} * {g}) * ↑H) * {g⁻¹} by simp_rw [← mul_assoc],
    Set.singleton_mul_singleton]
  conv => enter [1, 1, 2]; simp
  conv => enter [1, 1]; rw [mul_assoc, coe_mul_coe H]

/-- The intersection `H ∩ gHg⁻¹` acts trivially on `gHg⁻¹` by left multiplication. -/
lemma inter_mul_conjAct_eq_conjAct (g : G) :
    ((H : Set G) ∩ (ConjAct.toConjAct g • H)) * (ConjAct.toConjAct g • H) =
    (ConjAct.toConjAct g • H) := by
  have := Set.inter_mul_subset (s₁ := (H : Set G))
    (s₂ := (ConjAct.toConjAct g • H)) (t := (ConjAct.toConjAct g • H))
  refine Subset.antisymm ?_ ?_
  · exact le_trans this (by simp [conjAct_mul_self_eq_self])
  · exact subset_mul_right _ ⟨Subgroup.one_mem H,
      Subgroup.one_mem (ConjAct.toConjAct g • H)⟩

/-- Right multiplication by a singleton is cancellative. -/
lemma mul_singleton_right_cancel (g : G) (K L : Set G)
    (h : K * {g} = L * {g}) : K = L := by
  have h2 := congrFun (congrArg HMul.hMul h) {g⁻¹}
  simp_rw [mul_assoc, Set.singleton_mul_singleton] at h2; simpa using h2

/-- A double coset `HgH` decomposes as a disjoint union of left cosets of `H`. -/
lemma DoubleCoset.doubleCoset_eq_iUnion_leftCosets (g : G) :
    DoubleCoset.doubleCoset g H H =
    ⋃ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
      (i.out * g) • (H : Set G) := by
  rw [DoubleCoset.doubleCoset]
  have := set_eq_iUnion_leftCosets H
    (((ConjAct.toConjAct g • H).subgroupOf H).map H.subtype)
  simp only [Subgroup.subgroupOf_map_subtype, inf_le_right, Subgroup.coe_inf,
    Subgroup.coe_pointwise_smul, true_implies] at this
  have h2 := congrFun (congrArg HMul.hMul this)
    ((ConjAct.toConjAct g • H) : Set G)
  rw [Set.iUnion_mul, inter_comm] at h2
  apply mul_singleton_right_cancel g⁻¹
  rw [conjAct_smul_coe_eq] at *; simp_rw [← mul_assoc] at h2; rw [h2]
  have : (Subgroup.map H.subtype
      ((ConjAct.toConjAct g • H).subgroupOf H)).subgroupOf H =
    (ConjAct.toConjAct g • H).subgroupOf H := by simp
  rw [this]
  have h1 : ∀ (i : H ⧸ (ConjAct.toConjAct g • H).subgroupOf H),
      ((i.out) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) *
        {g} * ↑H * {g⁻¹} =
      (↑(Quotient.out i) * g) • ↑H * {g⁻¹} := by
    intro i
    have := inter_mul_conjAct_eq_conjAct H g
    rw [conjAct_smul_coe_eq] at this
    have hr : ((i.out) : G) • ((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) *
        {g} * ↑H * {g⁻¹} =
      (i.out : G) • (((H : Set G) ∩ ({g} * ↑H * {g⁻¹})) *
        {g} * ↑H * {g⁻¹}) := by simp_rw [smul_mul_assoc]
    rw [hr]; simp_rw [← mul_assoc] at this
    conv => enter [1, 2]; rw [this]
    simp_rw [smul_eq_singleton_mul, ← Set.singleton_mul_singleton, ← mul_assoc]
  convert Set.iUnion_congr h1; rw [Set.iUnion_mul]

/-- The product of two double cosets simplifies using `H * H = H` on the left. -/
lemma doubleCoset_mul_doubleCoset_left (g h : G) :
    DoubleCoset.doubleCoset g H H * DoubleCoset.doubleCoset h H H =
    DoubleCoset.doubleCoset g H H * {h} * H := by
  simp_rw [DoubleCoset.doubleCoset,
    show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
      H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc], coe_mul_coe H]

/-- The product of two double cosets simplifies using `H * H = H` on the right. -/
lemma doubleCoset_mul_doubleCoset_right (g h : G) :
    DoubleCoset.doubleCoset g H H * DoubleCoset.doubleCoset h H H =
    H * {g} * DoubleCoset.doubleCoset h H H := by
  simp_rw [DoubleCoset.doubleCoset,
    show (H : Set G) * {g} * (H : Set G) * (H * {h} * H) =
      H * {g} * (H * H) * {h} * H by simp_rw [← mul_assoc],
    coe_mul_coe H, ← mul_assoc]

/-- The set-theoretic product of two double cosets is a union of double cosets. -/
lemma doubleCoset_mul_eq_iUnion_doubleCoset (g h : G) :
    DoubleCoset.doubleCoset g (H : Set G) H *
      DoubleCoset.doubleCoset h (H : Set G) H =
    ⋃ (i : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
      DoubleCoset.doubleCoset (g * i.out * h : G) H H := by
  rw [doubleCoset_mul_doubleCoset_right, DoubleCoset.doubleCoset_eq_iUnion_leftCosets,
    Set.mul_iUnion]
  simp_rw [DoubleCoset.doubleCoset]
  apply Set.iUnion_congr fun i => by
    rw [smul_eq_singleton_mul,
      show (H : Set G) * {g} * ({↑(Quotient.out i) * h} * ↑H) =
        H * {g} * {↑(Quotient.out i) * h} * ↑H by simp_rw [← mul_assoc],
      ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton,
      ← Set.singleton_mul_singleton]
    simp_rw [← mul_assoc]

/-- The double coset `HhH` is a constant union indexed by the trivial quotient. -/
lemma DoubleCoset.doubleCoset_one_mul (h : G) :
    DoubleCoset.doubleCoset h (H : Set G) H =
    ⋃ (_ : H ⧸ (ConjAct.toConjAct h • H).subgroupOf H),
      DoubleCoset.doubleCoset h H H := by simp [Set.iUnion_const]

/-- The Hecke ring type: formal `Z`-linear combinations of double cosets `HeckeCoset P`. -/
def 𝕋 (P : HeckePair G) (Z : Type*) [CommRing Z] := Finsupp (HeckeCoset P) Z

/-- The Hecke module type: formal `Z`-linear combinations of left cosets `HeckeLeftCoset P`. -/
def HeckeModule (P : HeckePair G) (Z : Type*) [CommRing Z] := Finsupp (HeckeLeftCoset P) Z

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

/-- The decomposition quotient is finite because `Δ ≤ commensurator(H)`. -/
noncomputable instance (P : HeckePair G) (D : HeckeCoset P) :
    Fintype (P.H ⧸ ((ConjAct.toConjAct (D.doubleCoset_eq.choose : G)) •
      P.H).subgroupOf P.H) :=
  Subgroup.fintypeOfIndexNeZero (P.h₁ D.doubleCoset_eq.choose.2).1

/-- Products of the form `a · h · b` with `h ∈ H`, `a, b ∈ Δ` remain in `Δ`. -/
lemma delta_mul_mem (i : H) (a b : Δ) (h₀ : H.toSubmonoid ≤ Δ) :
    a * (i : G) * b ∈ Δ := by
  rw [mul_assoc]; exact Submonoid.mul_mem _ a.2 (Submonoid.mul_mem _ (h₀ i.2) b.2)

/-- The additive commutative group structure on the Hecke ring. -/
noncomputable instance instAddCommGroup𝕋 : AddCommGroup (𝕋 P Z) :=
  inferInstanceAs (AddCommGroup ((HeckeCoset P) →₀ Z))

/-- The additive commutative group structure on the Hecke module. -/
noncomputable instance instAddCommGroupHeckeModule : AddCommGroup (HeckeModule P Z) :=
  inferInstanceAs (AddCommGroup ((HeckeLeftCoset P) →₀ Z))

/-- The quotient `H / (H ∩ gHg⁻¹)` indexing left cosets in the decomposition of a
double coset `HgH`. -/
abbrev decompQuot (D : HeckeCoset P) :=
  P.H ⧸ (ConjAct.toConjAct (D.doubleCoset_eq.choose : G) • P.H).subgroupOf P.H
