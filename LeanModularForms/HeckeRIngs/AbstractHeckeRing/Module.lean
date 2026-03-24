/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Multiplication

/-!
# Hecke Rings: Module Action

The module action of `𝕋 P ℤ` on `HeckeModule P ℤ` (formal sums of left cosets) and the faithfulness
theorem `eq_of_smul_eq_smul_𝕋`.
-/

open Commensurable Classical MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

open Finsupp

/-- The scalar multiplication on `𝕋` by itself, defined as reverse multiplication. -/
noncomputable instance instSMul𝕋 : SMul (𝕋 P ℤ) (𝕋 P ℤ) where
  smul x y := y * x

/-- The orbit of a left coset representative `β` under double coset representative `g`:
the set of left cosets `{β · σ_i · g | σ_i ∈ H/(H ∩ gHg⁻¹)}`. -/
noncomputable def smulOrbit (g : P.Δ) (β : P.Δ) :
    Finset (HeckeLeftCoset P) :=
  Finset.image (fun i : decompQuot P g =>
    (⟦⟨(β : G) * (i.out : G) * (g : G),
      delta_mul_mem P.H P.Δ i.out β g P.h₀⟩⟧ : HeckeLeftCoset P)) ⊤

/-- The smul orbit of any left coset under any double coset is nonempty. -/
lemma smulOrbit_nonempty (g : P.Δ) (β : P.Δ) :
    (smulOrbit P g β).Nonempty := by rw [smulOrbit]; simp

/-- The orbit is invariant under left coset equivalence: if `β₁H = β₂H`, then
    `smulOrbit g β₁ = smulOrbit g β₂`. This is the key API lemma that lets us
    replace `HeckeLeftCoset.rep j` with any representative of `j`. -/
lemma smulOrbit_lcRel (g : P.Δ) {β₁ β₂ : P.Δ} (h : lcRel P β₁ β₂) :
    smulOrbit P g β₁ = smulOrbit P g β₂ := by
  ext x; simp only [smulOrbit, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    -- β₁ * i.out * g is in the same left coset as β₂ * i'.out * g for some i'
    -- because β₁H = β₂H means β₂⁻¹β₁ ∈ H
    sorry
  · rintro ⟨i, hi⟩
    sorry

/-- Corollary: `smulOrbit g (HeckeLeftCoset.rep ⟦β⟧) = smulOrbit g β`. -/
lemma smulOrbit_rep_mk (g β : P.Δ) :
    smulOrbit P g (HeckeLeftCoset.rep ⟦β⟧) = smulOrbit P g β :=
  smulOrbit_lcRel P g (Quotient.exact (Quotient.out_eq (⟦β⟧ : HeckeLeftCoset P)))

/-- The orbit is invariant under double coset equivalence. -/
lemma smulOrbit_dcRel {g₁ g₂ : P.Δ} (β : P.Δ) (h : dcRel P g₁ g₂) :
    smulOrbit P g₁ β = smulOrbit P g₂ β := by
  sorry

/-- Corollary: `smulOrbit (HeckeCoset.rep ⟦g⟧) β = smulOrbit g β`. -/
lemma smulOrbit_rep_mk_dc (g β : P.Δ) :
    smulOrbit P (HeckeCoset.rep ⟦g⟧) β = smulOrbit P g β :=
  smulOrbit_dcRel P β (Quotient.exact (Quotient.out_eq (⟦g⟧ : HeckeCoset P)))

/-- The module action of the Hecke ring on formal sums of left cosets. -/
noncomputable instance instSMulHeckeModule : SMul (𝕋 P Z) (HeckeModule P Z) where
  smul t mm := Finsupp.sum t fun D1 b₁ => mm.sum fun m b₂ =>
    (∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep m),
      Finsupp.single i (b₁ * b₂ : Z) : (HeckeLeftCoset P) →₀ Z)

/-- The scalar multiplication on `HeckeModule` unfolds as a double sum over orbits. -/
lemma smul_eq_sum (T : 𝕋 P Z) (m : HeckeModule P Z) :
    T • m = Finsupp.sum T (fun D1 b₁ => m.sum fun m b₂ =>
      (∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep m),
        Finsupp.single i (b₁ * b₂ : Z) : (HeckeLeftCoset P) →₀ Z)) := rfl

/-- The heterogeneous scalar multiplication instance for the module action. -/
noncomputable instance instHSMulHeckeModule : HSMul (𝕋 P Z) (HeckeModule P Z) (HeckeModule P Z) :=
  inferInstance

/-- The action of a basis Hecke element on a basis module element. -/
lemma single_smul_single (t : HeckeCoset P) (m : HeckeLeftCoset P) (a b : Z) :
    (instHSMulHeckeModule P Z).hSMul ((Finsupp.single t a) : 𝕋 P Z)
      ((Finsupp.single m b) : HeckeModule P Z) =
    (∑ i ∈ smulOrbit P (HeckeCoset.rep t) (HeckeLeftCoset.rep m),
      Finsupp.single i (a * b : Z) : (HeckeLeftCoset P) →₀ Z) := by
  rw [smul_eq_sum]
  simp [mul_zero, single_zero, Finset.sum_const_zero, sum_single_index, zero_mul]

/-- Every finsupp is a sum of its basis elements. -/
lemma single_basis {α : Type*} (t : Finsupp α Z) :
    t = ∑ (i ∈ t.support), single i (t.toFun i) :=
  (Finsupp.sum_single t).symm

/-- The one element of `HeckeModule`: the basis element for the identity left coset. -/
noncomputable instance instOneHeckeModule : One (HeckeModule P Z) :=
  ⟨Finsupp.single (HeckeLeftCoset.one P) 1⟩

/-- The one element of `HeckeModule` is the basis element corresponding to the identity
left coset. -/
lemma one_eq_HeckeLeftCoset_single :
    (1 : HeckeModule P Z) = Finsupp.single (HeckeLeftCoset.one P) 1 := rfl

/-- The module action is additive in the Hecke ring argument. -/
lemma smul_add_left (T₁ T₂ : 𝕋 P Z) (m : HeckeModule P Z) :
    (T₁ + T₂) • m = T₁ • m + T₂ • m := by
  simp only [smul_eq_sum]
  rw [Finsupp.sum_add_index]
  · intro D1 _
    simp only [zero_mul, Finsupp.single_zero, Finset.sum_const_zero, Finsupp.sum_fun_zero]
  · intro D1 _ y b₂
    simp only [Finsupp.sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro m _
    simp_rw [add_mul, Finsupp.single_add]

/-- The zero element of the Hecke ring acts as zero on the module. -/
lemma zero_smul_HeckeModule (z : HeckeModule P Z) : (0 : 𝕋 P Z) • z = 0 := by
  simp only [smul_eq_sum]; exact Finsupp.sum_zero_index

/-- Any Hecke ring element acts as zero on the zero module element. -/
lemma smul_zero_HeckeModule (T : 𝕋 P Z) : T • (0 : HeckeModule P Z) = 0 := by
  simp only [smul_eq_sum, Finsupp.sum_zero_index, Finsupp.sum_fun_zero]

/-- The module action is additive in the module argument. -/
lemma smul_add_right (T : 𝕋 P Z) (m₁ m₂ : HeckeModule P Z) :
    T • (m₁ + m₂) = T • m₁ + T • m₂ := by
  simp only [smul_eq_sum]
  have inner_split : ∀ D (b : Z),
      (m₁ + m₂).sum (fun m c =>
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * c)) =
      m₁.sum (fun m c =>
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * c)) +
      m₂.sum (fun m c =>
        ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m),
          Finsupp.single i (b * c)) := by
    intro D b
    rw [Finsupp.sum_add_index']
    · intro m; simp [mul_zero, Finsupp.single_zero, Finset.sum_const_zero]
    · intro m c₁ c₂
      simp only [← Finset.sum_add_distrib, mul_add, Finsupp.single_add]
  simp_rw [inner_split]
  rw [← Finsupp.sum_add]

/-- The smul orbits of distinct double cosets acting on the same left coset are disjoint. -/
lemma smulOrbit_disjoint_of_ne (g₁ g₂ : P.Δ) (β : P.Δ)
    (hne : (⟦g₁⟧ : HeckeCoset P) ≠ ⟦g₂⟧) :
    Disjoint (smulOrbit P g₁ β) (smulOrbit P g₂ β) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  apply hne; apply Quotient.sound; show dcRel P _ _
  simp only [smulOrbit, Finset.mem_image] at hx₁ hx₂
  obtain ⟨i₁, _, hi₁⟩ := hx₁; obtain ⟨i₂, _, hi₂⟩ := hx₂
  rw [← hi₂] at hi₁
  have hset : ({(β : G) * (i₁.out : G) *
      (g₁ : G)} : Set G) * (P.H : Set G) =
    {(β : G) * (i₂.out : G) *
      (g₂ : G)} * P.H := by
    have := Quotient.exact hi₁
    exact this
  have hmem : (β : G) * ↑i₁.out * (g₁ : G) ∈
      ({(β : G) * ↑i₂.out * (g₂ : G)} : Set G) * (↑P.H : Set G) := by
    rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have hstep : ↑i₂.out * (g₂ : G) * k =
      ↑i₁.out * (g₁ : G) := by
    have h : (β : G) *
        (↑i₂.out * (g₂ : G) * k) =
        (β : G) *
        (↑i₁.out * (g₁ : G)) := by
      have := hkk; dsimp at this; group at this ⊢; exact this
    exact mul_left_cancel h
  have hg : (g₁ : G) =
      ↑(i₁.out⁻¹ * i₂.out) *
        (g₂ : G) * k := by
    apply mul_left_cancel (a := (↑i₁.out : G))
    have : ↑i₁.out *
        (↑(i₁.out⁻¹ * i₂.out) *
        (g₂ : G) * k) =
        ↑i₂.out * (g₂ : G) * k := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]; exact hstep.symm
  show DoubleCoset.doubleCoset (g₁ : G) P.H P.H =
    DoubleCoset.doubleCoset (g₂ : G) P.H P.H
  conv_lhs => rw [show (g₁ : G) = _ from hg]
  exact (DoubleCoset.doubleCoset_mul_right_eq_self P ⟨k, hk⟩ _).trans
    (doset_mul_left_eq_self P (i₁.out⁻¹ * i₂.out) _)

private lemma smul_one_eval (T : 𝕋 P Z) (D : HeckeCoset P) (m : HeckeLeftCoset P)
    (hm : m ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep (HeckeLeftCoset.one P))) :
    (T • (1 : HeckeModule P Z)).toFun m = T.toFun D := by
  rw [smul_eq_sum, one_eq_HeckeLeftCoset_single]
  have hsimp : ∀ D1 (b₁ : Z),
      Finsupp.sum (Finsupp.single (HeckeLeftCoset.one P) (1 : Z))
        (fun m' b₂ => ∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep m'),
          Finsupp.single i (b₁ * b₂)) =
      ∑ i ∈ smulOrbit P (HeckeCoset.rep D1) (HeckeLeftCoset.rep (HeckeLeftCoset.one P)),
        Finsupp.single i b₁ := by
    intro D1 b1
    rw [Finsupp.sum_single_index
      (by simp [mul_zero, Finsupp.single_zero, Finset.sum_const_zero]), mul_one]
  simp_rw [hsimp]; unfold Finsupp.sum
  show (∑ x ∈ T.support,
    ∑ i ∈ smulOrbit P (HeckeCoset.rep x) (HeckeLeftCoset.rep (HeckeLeftCoset.one P)),
      Finsupp.single i (T.toFun x)) m = T.toFun D
  rw [Finsupp.finset_sum_apply]
  simp_rw [Finsupp.finset_sum_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single D]
  · rw [Finset.sum_eq_single_of_mem m hm (fun b _ hb => if_neg hb), if_pos rfl]
  · intro D' _ hne
    exact Finset.sum_eq_zero fun i hi =>
      if_neg (fun heq => absurd (heq ▸ hi)
        (Finset.disjoint_left.mp
          (smulOrbit_disjoint_of_ne P (HeckeCoset.rep D) (HeckeCoset.rep D')
            (HeckeLeftCoset.rep (HeckeLeftCoset.one P))
            (by simp only [HeckeCoset.rep, Quotient.out_eq]; exact Ne.symm hne)) hm))
  · intro hns
    exact Finset.sum_eq_zero fun x _ => by
      have h0 : T.toFun D = 0 := Finsupp.notMem_support_iff.mp hns
      simp [h0]

/-- Faithfulness of the module action: if two Hecke ring elements act identically on all
module elements, they are equal. -/
lemma eq_of_smul_eq_smul_𝕋 (T1 T2 : (𝕋 P Z))
    (h : ∀ (a : HeckeModule P Z), T1 • a = T2 • a) :
    T1 = T2 :=
  Finsupp.ext fun D => by
    obtain ⟨m, hm⟩ := smulOrbit_nonempty P (HeckeCoset.rep D)
      (HeckeLeftCoset.rep (HeckeLeftCoset.one P))
    have h1 := congrFun (congrArg Finsupp.toFun (h 1)) m
    rwa [smul_one_eval P Z T1 D m hm, smul_one_eval P Z T2 D m hm] at h1

/-- The module action of `𝕋 P ℤ` on `HeckeModule P ℤ` is faithful. -/
noncomputable instance instFaithfulSMulHeckeModule :
    FaithfulSMul (𝕋 P ℤ) (HeckeModule P ℤ) where
  eq_of_smul_eq_smul {t1 t2} h := eq_of_smul_eq_smul_𝕋 P ℤ t1 t2 h

/-- The scalar multiplication on `𝕋` is defined as reverse multiplication. -/
lemma smul_def (f g : 𝕋 P ℤ) : f • g = g * f := rfl
