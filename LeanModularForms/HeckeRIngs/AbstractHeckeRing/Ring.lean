/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Associativity

/-!
# Hecke Rings: Ring Instance and API

The `Ring (𝕋 P ℤ)` instance and user-facing API lemmas for working with Hecke rings.
-/

open Commensurable Classical Doset MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G α : Type*} [Group G] (H : Subgroup G) (Δ : Submonoid G) (h₀ : H.toSubmonoid ≤ Δ)
  (h₁ : (Δ ≤ (commensurator H).toSubmonoid))

variable (P : ArithmeticGroupPair G) (Z : Type*) [CommRing Z] [IsDomain Z]

open Finsupp

lemma 𝕋_mul_assoc (f g h : 𝕋 P ℤ) : (f * g) * h = f * (g * h) := by
  apply (instFaithfulSMul𝕄 P).eq_of_smul_eq_smul (M := (𝕋 P ℤ))
  intro a
  have e1 := (instIsScalarTower P).smul_assoc g f a
  have e2 := (instIsScalarTower P).smul_assoc h g (f • a)
  have e3 := (instIsScalarTower P).smul_assoc (g * h) f a
  have e4 := (instIsScalarTower P).smul_assoc h (f * g) a
  simp only [smul_def] at e1 e2 e3 e4
  rw [e1] at e4
  rw [← e2] at e4
  rwa [← e3] at e4

noncomputable instance instNonUnitalSemiring : NonUnitalSemiring (𝕋 P ℤ) :=
  {instNonUnitalNonAssocSemiring P with
    mul_assoc := 𝕋_mul_assoc P }

/-- The identity is `H1H`. -/
noncomputable instance instOne𝕋 : One (𝕋 P Z) := ⟨T_single P Z (T_one P) (1 : Z)⟩

omit [IsDomain Z] in
theorem one_def : (1 : (𝕋 P Z)) = T_single P Z (T_one P) (1 : Z) :=
  rfl

noncomputable instance instNonAssocSemiring : NonAssocSemiring (𝕋 P ℤ) :=
  { instNonUnitalNonAssocSemiring P with
    natCast := fun n => T_single P ℤ (T_one P) (n : ℤ)
    natCast_zero := by simp only [Nat.cast_zero, single_zero]
    natCast_succ := fun _ => by
      simp only [Nat.cast_add, Nat.cast_one, single_add, add_right_inj]
      rfl
    one_mul := fun f => by
      simp only [one_def, mul_def]

      rw [T_single]
      simp
      have := Finsupp.sum_single f
      nth_rw 2 [← this]
      congr
      ext D z v
      have := 𝕋_one_mul_singleton P D z
      simp_rw [T_single] at *
      rw [← this]
      rw [𝕋_mul_singleton]
      simp only [one_smul]
    mul_one :=fun f => by
      simp only [one_def, mul_def, zero_smul, smul_zero, sum_single_index, one_smul]
      have := Finsupp.sum_single f
      nth_rw 2 [← this]
      congr
      ext D z v
      have := 𝕋_singleton_one_mul P D z
      simp_rw [T_single] at this
      rw [← this]
      rw [𝕋_mul_singleton]
      simp only [one_smul] }

noncomputable instance instSemiring : Semiring (𝕋 P ℤ) :=
  {HeckeRing.instNonUnitalSemiring P ,
    (HeckeRing.instNonAssocSemiring P ) with}

noncomputable instance instNonAssocRing : NonAssocRing (𝕋 P ℤ) :=
  { HeckeRing.instAddCommGroup𝕋 P ℤ,
    (HeckeRing.instNonAssocSemiring P ) with
    intCast := fun n => T_single P ℤ (T_one P) (n : ℤ)
    intCast_ofNat := fun n => rfl
    intCast_negSucc := fun n => by
      simp only [T_single, Int.negSucc_eq, Finsupp.single_neg]
      congr 1 }

noncomputable instance instRing : Ring (𝕋 P ℤ) :=
    {HeckeRing.instNonAssocRing P , HeckeRing.instSemiring P with }

section API

@[simp] lemma T_single_zero (D : T' P) : T_single P ℤ D 0 = 0 :=
  Finsupp.single_zero _

@[simp] lemma T_single_add (D : T' P) (a b : ℤ) :
    T_single P ℤ D a + T_single P ℤ D b = T_single P ℤ D (a + b) :=
  (Finsupp.single_add D a b).symm

@[simp] lemma T_single_neg (D : T' P) (a : ℤ) :
    - T_single P ℤ D a = T_single P ℤ D (-a) :=
  (Finsupp.single_neg D a).symm

lemma T_single_sub (D : T' P) (a b : ℤ) :
    T_single P ℤ D a - T_single P ℤ D b = T_single P ℤ D (a - b) := by
  simp [sub_eq_add_neg]

lemma T_single_smul (D : T' P) (n a : ℤ) :
    n • T_single P ℤ D a = T_single P ℤ D (n * a) :=
  Finsupp.smul_single' n D a

lemma one_eq_T_single : (1 : 𝕋 P ℤ) = T_single P ℤ (T_one P) 1 := rfl

@[simp] lemma intCast_eq (n : ℤ) :
    (n : 𝕋 P ℤ) = T_single P ℤ (T_one P) n := rfl

/-- The fundamental multiplication rule: product of two basis elements equals
    `a * b` times Shimura's multiplicity finsupp `m P D₁ D₂`.
    This is the workhorse for computing products in the Hecke ring. -/
lemma T_single_mul_T_single (D₁ D₂ : T' P) (a b : ℤ) :
    T_single P ℤ D₁ a * T_single P ℤ D₂ b = a • b • m P D₁ D₂ :=
  𝕋_mul_singleton P D₁ D₂ a b

/-- Product of two unit-coefficient basis elements is just Shimura's multiplicity. -/
@[simp] lemma T_single_one_mul_T_single_one (D₁ D₂ : T' P) :
    T_single P ℤ D₁ 1 * T_single P ℤ D₂ 1 = m P D₁ D₂ := by
  simp [T_single_mul_T_single]

/-- Multiplication by the identity double coset on the right. -/
@[simp] lemma T_single_mul_one (D : T' P) (a : ℤ) :
    T_single P ℤ D a * 1 = T_single P ℤ D a :=
  𝕋_singleton_one_mul P D a

/-- Multiplication by the identity double coset on the left. -/
@[simp] lemma one_mul_T_single (D : T' P) (a : ℤ) :
    1 * T_single P ℤ D a = T_single P ℤ D a :=
  𝕋_one_mul_singleton P D a

/-- Evaluating the multiplicity finsupp at a double coset gives `m'`. -/
@[simp] lemma m_apply (D₁ D₂ D : T' P) : (m P D₁ D₂) D = m' P D₁ D₂ D := rfl

/-- The multiplicity finsupp for `D * T_one` is the Kronecker delta at `D`. -/
@[simp] lemma m_mul_T_one (D : T' P) : m P D (T_one P) = Finsupp.single D 1 :=
  m_right_T_one_eq_single P D

/-- The multiplicity finsupp for `T_one * D` is the Kronecker delta at `D`. -/
@[simp] lemma m_T_one_mul (D : T' P) : m P (T_one P) D = Finsupp.single D 1 :=
  m_left_T_one_eq_single P D

/-- The support of `m P D₁ D₂` is exactly the set of double cosets that appear
    in the product `D₁ · D₂`. -/
lemma m_support (D₁ D₂ : T' P) : (m P D₁ D₂).support = mulSupport P D₁ D₂ := rfl

/-- `m'` is nonneg (it's a natural number cast to ℤ). -/
lemma m'_nonneg (D₁ D₂ D : T' P) : 0 ≤ m' P D₁ D₂ D := by simp [m']

/-- Two elements of `𝕋 P ℤ` are equal iff they have the same coefficient at every
    double coset. This is the main extensionality principle. -/
@[ext] lemma 𝕋_ext {f g : 𝕋 P ℤ} (h : ∀ D : T' P, f.toFun D = g.toFun D) : f = g :=
  Finsupp.ext h

/-- Induction principle for the Hecke ring: to prove `P f` for all `f : 𝕋 P ℤ`,
    it suffices to prove `P 0` and `P g → P (T_single D a + g)` for singles. -/
lemma 𝕋.induction_on {C : 𝕋 P ℤ → Prop} (f : 𝕋 P ℤ)
    (h_zero : C 0)
    (h_add : ∀ (D : T' P) (a : ℤ) (g : 𝕋 P ℤ), D ∉ g.support → a ≠ 0 → C g →
      C (T_single P ℤ D a + g)) :
    C f :=
  Finsupp.induction f h_zero h_add

/-- Linear induction: to prove `P f` for all `f`, it suffices to prove `P 0`,
    `P (T_single D a)` for all `D, a`, and `P f → P g → P (f + g)`. -/
lemma 𝕋.induction_linear {C : 𝕋 P ℤ → Prop} (f : 𝕋 P ℤ)
    (h_zero : C 0)
    (h_single : ∀ (D : T' P) (a : ℤ), C (T_single P ℤ D a))
    (h_add : ∀ f g : 𝕋 P ℤ, C f → C g → C (f + g)) :
    C f :=
  Finsupp.induction_linear f h_zero h_add h_single

/-- Every element of the Hecke ring is a finite sum of basis elements. -/
lemma 𝕋_sum_single (f : 𝕋 P ℤ) :
    f = ∑ D ∈ f.support, T_single P ℤ D (f.toFun D) :=
  single_basis ℤ f

omit [IsDomain Z] in
/-- The module action of a single basis element on a single left coset. -/
lemma T_single_smul_M_single (D : T' P) (m₀ : M P) (a b : Z) :
    (T_single P Z D a) • (M_single P Z m₀ b) =
    ∑ i ∈ smulOrbit P D m₀, M_single P Z i (a * b) :=
  single_smul_single P Z D m₀ a b

end API

end HeckeRing
