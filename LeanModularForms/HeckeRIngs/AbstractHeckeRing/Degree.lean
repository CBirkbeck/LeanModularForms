/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring

/-!
# Hecke Rings: Degree Map

The degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ`, which sends each double coset `HgH` to the
number of left cosets it contains: `deg(HgH) = [H : H ∩ gHg⁻¹]`.

This is Shimura §3.1, Proposition 3.3.

## Main definitions

* `T'_deg P D` : the degree of a single double coset
* `deg P` : the degree ring homomorphism `𝕋 P ℤ →+* ℤ`

## Main results

* `deg_T_single` : `deg(T_single D a) = a * T'_deg D`
* `T'_deg_pos` : `0 < T'_deg D`
* `deg_one` : `deg 1 = 1`

## Proof strategy

Multiplicativity `deg(f * g) = deg(f) * deg(g)` is proved using the module action on `𝕄 P ℤ`.
We show `deg(f) = coeffSum(f • 1)` where `coeffSum` sums all coefficients, and then use
`IsScalarTower` (Shimura Prop 3.4) to get `(f * g) • 1 = g • (f • 1)`. The key intermediate
result is `coeffSum(f • m) = deg(f) * coeffSum(m)`, which follows from the orbit cardinality
lemma `smulOrbit_card`.
-/

open Commensurable Classical Doset MulOpposite Set DoubleCoset Subgroup Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]
variable (P : ArithmeticGroupPair G)

open Finsupp

/-- The degree of a double coset: the index `[H : H ∩ gHg⁻¹]`.
    Shimura §3.1, Proposition 3.3. -/
noncomputable def T'_deg (D : T' P) : ℤ :=
  Fintype.card (decompQuot P D)

@[simp]
lemma T'_deg_T_one : T'_deg P (T_one P) = 1 := by
  simp only [T'_deg]
  haveI := subsingleton_decompQuot_T_one P
  haveI : Unique (decompQuot P (T_one P)) :=
    uniqueOfSubsingleton (one_in_decompQuot_T_one P).some
  simp [Fintype.card_unique]

lemma T'_deg_pos (D : T' P) : 0 < T'_deg P D := by
  simp only [T'_deg]; exact_mod_cast Fintype.card_pos

section SmulOrbitCard

/-- The orbit map `Q(D) → M P` sending `i ↦ m₀ · i · g_D` is injective. -/
private lemma smulOrbit_map_inj (D : T' P) (m₀ : M P) :
    Function.Injective (fun i : decompQuot P D =>
      M_mk P ⟨((m₀.eql.choose : G) * (i.out : G) * (D.eql.choose : G)),
        delta_mul_mem P.H P.Δ i.out m₀.eql.choose D.eql.choose P.h₀⟩) := by
  intro i₁ i₂ heq
  by_contra hne
  have hset := congr_arg M.set heq
  simp only [M_mk] at hset
  have hmem : (m₀.eql.choose : G) * (i₁.out : G) * (D.eql.choose : G) ∈
      ({(m₀.eql.choose : G) * (i₂.out : G) * (D.eql.choose : G)} : Set G) *
      (P.H : Set G) := by
    rw [← hset]; exact ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have cancel : (i₂.out : G) * (D.eql.choose : G) * k = (i₁.out : G) * (D.eql.choose : G) := by
    apply mul_left_cancel (a := (m₀.eql.choose : G))
    have := hkk; group at this ⊢; exact this
  exact decompQuot_coset_diff P D i₁ i₂ hne
    (leftCoset_eq_of_not_disjoint (H := P.H) _ _ (by
      rw [@not_disjoint_iff]
      exact ⟨(i₁.out : G) * (D.eql.choose : G),
        ⟨1, P.H.one_mem, mul_one _⟩,
        ⟨k, hk, cancel⟩⟩))

/-- The smulOrbit has the same cardinality as `Q(D)`. -/
lemma smulOrbit_card (D : T' P) (m₀ : M P) :
    (smulOrbit P D m₀).card = Fintype.card (decompQuot P D) := by
  simp only [smulOrbit, Finset.card_image_of_injective _ (smulOrbit_map_inj P D m₀)]
  exact Finset.card_univ

lemma smulOrbit_card_intCast (D : T' P) (m₀ : M P) :
    ((smulOrbit P D m₀).card : ℤ) = T'_deg P D := by
  simp [smulOrbit_card, T'_deg]

end SmulOrbitCard

section CoeffSum

/-- Sum of all coefficients of a left-coset formal sum, as an `AddMonoidHom`. -/
noncomputable def coeffSum : 𝕄 P ℤ →+ ℤ :=
  Finsupp.liftAddHom (fun _ : M P => AddMonoidHom.id ℤ)

@[simp]
lemma coeffSum_single (m₀ : M P) (b : ℤ) :
    coeffSum P (M_single P ℤ m₀ b) = b :=
  Finsupp.liftAddHom_apply_single _ _ _

lemma coeffSum_zero : coeffSum P (0 : 𝕄 P ℤ) = 0 := map_zero _

lemma coeffSum_add (m₁ m₂ : 𝕄 P ℤ) :
    coeffSum P (m₁ + m₂) = coeffSum P m₁ + coeffSum P m₂ := map_add _ _ _

lemma coeffSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → 𝕄 P ℤ) :
    coeffSum P (∑ i ∈ s, f i) = ∑ i ∈ s, coeffSum P (f i) := map_sum _ _ _

/-- Key computation: `coeffSum` of a single-on-single module action. -/
lemma coeffSum_single_smul_single (D : T' P) (m₀ : M P) (a b : ℤ) :
    coeffSum P ((T_single P ℤ D a) • (M_single P ℤ m₀ b)) =
    a * T'_deg P D * b := by
  rw [T_single_smul_M_single, coeffSum_finset_sum]
  simp only [coeffSum_single, Finset.sum_const, Int.nsmul_eq_mul,
    smulOrbit_card_intCast]
  ring

end CoeffSum

section DegreeMap

/-- The degree function: `deg(∑ aᵢ [HgᵢH]) = ∑ aᵢ · [H : H ∩ gᵢHgᵢ⁻¹]`. -/
noncomputable def deg_fun (f : 𝕋 P ℤ) : ℤ := f.sum fun D a => a * T'_deg P D

@[simp]
lemma deg_fun_zero : deg_fun P (0 : 𝕋 P ℤ) = 0 := Finsupp.sum_zero_index

@[simp]
lemma deg_fun_T_single (D : T' P) (a : ℤ) :
    deg_fun P (T_single P ℤ D a) = a * T'_deg P D :=
  Finsupp.sum_single_index (by simp)

lemma deg_fun_add (f g : 𝕋 P ℤ) :
    deg_fun P (f + g) = deg_fun P f + deg_fun P g :=
  Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

@[simp]
lemma deg_fun_one : deg_fun P (1 : 𝕋 P ℤ) = 1 := by
  rw [one_eq_T_single, deg_fun_T_single, T'_deg_T_one, mul_one]

/-- `deg(f)` equals the sum of coefficients when `f` acts on `1 ∈ 𝕄`. -/
lemma deg_fun_eq_coeffSum_smul_one (f : 𝕋 P ℤ) :
    deg_fun P f = coeffSum P (f • (1 : 𝕄 P ℤ)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [zero_smul_𝕄]
  | add f g ihf ihg =>
    rw [deg_fun_add, ihf, ihg, smul_add_left, coeffSum_add]
  | single D a =>
    rw [deg_fun_T_single, one_eq_M_single, coeffSum_single_smul_single, mul_one]

/-- Key lemma: `coeffSum(f • m) = deg(f) * coeffSum(m)`. -/
lemma coeffSum_smul_eq (f : 𝕋 P ℤ) (m : 𝕄 P ℤ) :
    coeffSum P (f • m) = deg_fun P f * coeffSum P m := by
  induction f using Finsupp.induction_linear with
  | zero => simp [zero_smul_𝕄]
  | add f₁ f₂ ih₁ ih₂ =>
    rw [smul_add_left, coeffSum_add, ih₁, ih₂, deg_fun_add]; ring
  | single D a =>
    induction m using Finsupp.induction_linear with
    | zero => simp [smul_zero_𝕄]
    | add m₁ m₂ ih₁ ih₂ =>
      rw [smul_add_right, coeffSum_add, ih₁, ih₂, coeffSum_add, deg_fun_T_single]; ring
    | single m₀ b =>
      rw [coeffSum_single_smul_single, coeffSum_single, deg_fun_T_single]

/-- The degree function is multiplicative (Shimura Proposition 3.3). -/
lemma deg_fun_mul (f g : 𝕋 P ℤ) :
    deg_fun P (f * g) = deg_fun P f * deg_fun P g := by
  have h := (instIsScalarTower P).smul_assoc g f (1 : 𝕄 P ℤ)
  simp only [smul_def] at h
  rw [deg_fun_eq_coeffSum_smul_one P (f * g), h, coeffSum_smul_eq,
      ← deg_fun_eq_coeffSum_smul_one P f]
  ring

/-- The degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ`. -/
noncomputable def deg : 𝕋 P ℤ →+* ℤ where
  toFun := deg_fun P
  map_zero' := deg_fun_zero P
  map_one' := deg_fun_one P
  map_add' := deg_fun_add P
  map_mul' := deg_fun_mul P

end DegreeMap

section API

@[simp]
lemma deg_T_single (D : T' P) (a : ℤ) :
    deg P (T_single P ℤ D a) = a * T'_deg P D :=
  deg_fun_T_single P D a

@[simp]
lemma deg_one_val : deg P (1 : 𝕋 P ℤ) = 1 := (deg P).map_one

lemma deg_mul (f g : 𝕋 P ℤ) : deg P (f * g) = deg P f * deg P g :=
  (deg P).map_mul f g

lemma deg_add (f g : 𝕋 P ℤ) : deg P (f + g) = deg P f + deg P g :=
  (deg P).map_add f g

@[simp]
lemma deg_intCast (n : ℤ) : deg P (n : 𝕋 P ℤ) = n := by
  simp [deg, deg_fun, T'_deg_T_one]

end API

end HeckeRing
