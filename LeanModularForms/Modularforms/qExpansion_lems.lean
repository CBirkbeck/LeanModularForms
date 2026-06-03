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
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_neZero n
  have hΓ : (n : ℝ) ∈ Γ(n).strictPeriods := by simp
  have h2 : Tendsto (cuspFunction n f) (𝓝[≠] 0) (𝓝 (cuspFunction n f 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have hAn := ModularFormClass.analyticAt_cuspFunction_zero (f := f) hn_pos hΓ
    exact hAn.continuousAt.tendsto
  apply h2.congr'
  rw [eventuallyEq_nhdsWithin_iff, eventually_iff_exists_mem]
  refine ⟨ball 0 1, Metric.ball_mem_nhds _ Real.zero_lt_one, fun y hy hy0 ↦ ?_⟩
  apply Function.Periodic.cuspFunction_eq_of_nonzero
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using hy0




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
  (ModularForm.qExpansion_smul (Γ := Γ(n)) (h := n)
      (hh := Nat.cast_pos.mpr (Nat.pos_of_neZero n)) (hΓ := by simp) a f).symm

instance : FunLike (ℍ → ℂ) ℍ ℂ where
  coe := fun ⦃a₁⦄ ↦ a₁
  coe_injective' := fun ⦃_ _⦄ a ↦ a



lemma qExpansion_ext2 {α β : Type*} [FunLike α ℍ ℂ] [FunLike β ℍ ℂ] (f : α) (g : β) (h : ⇑f = ⇑g) :
    qExpansion 1 f = qExpansion 1 g := by
  have hcf : cuspFunction 1 f = cuspFunction 1 g := congrArg (cuspFunction 1) h
  ext m
  simp [qExpansion_coeff, hcf]

lemma qExpansion_pow (f : ModularForm Γ(1) k) (n : ℕ) :
    qExpansion 1 ((((DirectSum.of (ModularForm Γ(1)) k) f) ^ n) (n * k)) =
      (qExpansion 1 f) ^ n := by
  exact_mod_cast qExpansion_of_pow (Γ := Γ(1)) (h := (1 : ℕ))
    (hh := by positivity) (hΓ := by simp) (f := f) (n := n)

