/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.ModularForms.QExpansion
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.Cases

@[expose] public section

/-!
# Auxiliary lemmas for q-expansions of modular forms

This file collects miscellaneous lemmas about q-expansions, cusp functions, and iterated
derivatives used in the development of modular forms.
-/

open ModularForm UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open SlashInvariantFormClass ModularFormClass
variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup SL(2, ℤ)} (n : ℕ) (f : F)

open scoped Real MatrixGroups CongruenceSubgroup

theorem modform_tendto_ndhs_zero {k : ℤ} (n : ℕ) [ModularFormClass F Γ(n) k] [NeZero n] :
    Tendsto (fun x ↦ (⇑f ∘ ↑ofComplex) (Periodic.invQParam (↑n) x)) (𝓝[≠] 0)
    (𝓝 (cuspFunction n f 0)) := by
  simp only [comp_apply]
  have hi : IsCusp OnePoint.infty Γ(n) := by
    apply Γ(n).isCusp_of_mem_strictPeriods (h := n)
    · exact_mod_cast Nat.pos_of_neZero n
    · simp
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply (Function.Periodic.differentiableAt_cuspFunction_zero (h := n)
      hn_pos ?_ ?_ ?_).continuousAt.tendsto
    · apply SlashInvariantFormClass.periodic_comp_ofComplex
      simp
    · simp only [eventually_comap, eventually_atTop, ge_iff_le]
      refine ⟨1, fun b hb a ha ↦ ?_⟩
      apply ModularFormClass.differentiableAt_comp_ofComplex (z := a)
      rw [ha]
      linarith
    exact ModularFormClass.bounded_at_infty_comp_ofComplex f hi
  apply h2.congr'
  rw [eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  refine ⟨ball 0 1, Metric.ball_mem_nhds _ Real.zero_lt_one, fun y hy hy0 ↦ ?_⟩
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0

theorem derivWithin_mul2 (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hd : DifferentiableOn ℂ g s) :
    s.restrict (derivWithin (fun y ↦ f y * g y) s) =
      s.restrict (derivWithin f s * g + f * derivWithin g s) := by
  ext y
  simp only [restrict_apply, Pi.add_apply, Pi.mul_apply]
  rw [derivWithin_fun_mul (hf y y.2) (hd y y.2)]



lemma qExpansion_mul_coeff (a b : ℤ) (f : ModularForm Γ(n) a) (g : ModularForm Γ(n) b)
    [NeZero n] : qExpansion n (f.mul g) = qExpansion n f * qExpansion n g := by
  simpa using
    (ModularForm.qExpansion_mul (Γ := Γ(n)) (h := n)
      (hh := Nat.cast_pos.mpr (Nat.pos_of_neZero n))
      (hΓ := by simp) f g)

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]


lemma qExpansion_smul2 (a : ℂ) (f : ModularForm Γ(n) k) [NeZero n] :
    a • qExpansion n f = qExpansion n (a • f) :=
  (qExpansion_smul (Γ := Γ(n)) (h := n) (hh := Nat.cast_pos.mpr (Nat.pos_of_neZero n))
    (hΓ := by simp) a f).symm

instance : FunLike (ℍ → ℂ) ℍ ℂ where
  coe := fun ⦃a₁⦄ ↦ a₁
  coe_injective' := fun ⦃_ _⦄ a ↦ a



lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β) (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  have hcf : cuspFunction 1 f = cuspFunction 1 g := congrArg (cuspFunction 1) h
  ext m
  simp [qExpansion_coeff, hcf]

@[simp]
lemma IteratedDeriv_zero_fun (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun _ : ℂ ↦ (0 : ℂ)) z = 0 := by
  induction n with
  | zero => simp
  | succ n hn => simp


lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
    qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k) f) ^ n) (n * k)) =
      (qExpansion 1 f) ^ n := by
  exact_mod_cast qExpansion_of_pow (Γ := Γ(1)) (h := (1 : ℕ))
    (hh := by positivity) (hΓ := by simp) (f := f) (n := n)

