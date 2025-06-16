/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Modular forms

This file defines modular forms and proves some basic properties about them. Including constructing
the graded ring of modular forms.

We begin by defining modular forms and cusp forms as extension of `SlashInvariantForm`s then we
define the space of modular forms, cusp forms and prove that the product of two modular forms is a
modular form.
-/

open Complex UpperHalfPlane

open scoped Topology Manifold MatrixGroups ComplexConjugate

noncomputable section

section ModularForm

open ModularForm

/-- The weight `k` slash action of `GL(2, ℝ)⁺` preserves holomorphic functions. This is private,
since it is a step towards the proof of `MDifferentiable.slash` which is more general. -/
private lemma MDifferentiable.slash_of_pos {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (k : ℤ) {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] g) := by
  refine .mul (.mul ?_ mdifferentiable_const) (mdifferentiable_denom_zpow g _)
  simpa only [σ, hg, ↓reduceIte] using hf.comp (mdifferentiable_smul hg)

private abbrev J : GL (Fin 2) ℝ :=
  ⟨!![1, 0; 0, -1], !![1, 0; 0, -1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

private lemma J_sq : J ^2 = 1 := by
  ext : 1
  simp [sq, Matrix.mul_fin_two, Matrix.one_fin_two]

private lemma J_smul (τ : ℍ) :
    J • τ = ofComplex (-(conj ↑τ)) := by
  ext
  simp [UpperHalfPlane.coe_smul, σ, if_neg (show ¬(1 : ℝ) < 0 by norm_num), num, denom,
    div_neg, ofComplex_apply_of_im_pos (by simpa using τ.im_pos : 0 < (-(starRingEnd ℂ) ↑τ).im)]

private lemma slash_J (f : ℍ → ℂ) (k : ℤ) :
    f ∣[k] J = fun τ : ℍ ↦ -conj (f <| ofComplex <| -(conj ↑τ)) := by
  ext τ
  simp only [slash_def]
  have detj : J.det = -1 := by ext; simp [J]
  have sigj : σ J = starRingEnd ℂ := by simp [σ, J]
  have denj : denom J τ = -1 := by simp [denom]
  rw [detj, sigj, denj, Units.val_neg, Units.val_one, ofReal_neg, ofReal_one, mul_assoc,
    ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (by ring : k - 1 + -k = -1),
    zpow_neg_one, inv_neg_one, mul_neg_one, J_smul]

/-- The weight `k` slash action of the negative-determinant matrix `J` preserves holomorphic
functions. -/
private lemma MDifferentiable.slashJ {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (k : ℤ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] J) := by
  simp only [mdifferentiable_iff, slash_J, Function.comp_def] at hf ⊢
  have : {z | 0 < z.im}.EqOn (fun x ↦ -conj (f <| ofComplex <| -conj ↑(ofComplex x)))
      (fun x ↦ -conj (f <| ofComplex <| -conj x)) := fun z hz ↦ by
    simp [ofComplex_apply_of_im_pos hz]
  refine .congr (fun z hz ↦ DifferentiableAt.differentiableWithinAt ?_) this
  have : 0 < (-conj z).im := by simpa using hz
  have := hf.differentiableAt ((Complex.continuous_im.isOpen_preimage _ isOpen_Ioi).mem_nhds this)
  simpa using (this.comp _ differentiable_neg.differentiableAt).star_star.neg

/-- The weight `k` slash action of `GL(2, ℝ)` preserves holomorphic functions. -/
lemma MDifferentiable.slash' {f : ℍ → ℂ} (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (k : ℤ) (g : GL (Fin 2) ℝ) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (f ∣[k] g) := by
  rcases g.det_ne_zero.lt_or_gt with hg | hg
  · have : g = J * (J * g) := by rw [← mul_assoc, ← sq, J_sq, one_mul]
    rw [this, SlashAction.slash_mul]
    apply (hf.slashJ k).slash_of_pos
    simpa only [map_mul, Units.val_mul, g.val_det_apply] using mul_pos_of_neg_of_neg (by simp) hg
  · exact hf.slash_of_pos k hg
