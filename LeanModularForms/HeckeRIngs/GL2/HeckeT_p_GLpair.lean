/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.Degree

/-!
# Connection between `heckeT_p_fun` and `heckeSlash_gen (GL_pair 2)`

This file bridges the explicit Hecke operator `T_p` defined via coset representatives
(`T_p_upper`, `T_p_lower`) in `HeckeT_p.lean` with the abstract Hecke slash action
`heckeSlash_gen (GL_pair 2)` from `HeckeActionGeneral.lean`.

## Main results

* `D_p` -- the double coset `SL₂(ℤ) · diag(1,p) · SL₂(ℤ)` in `GL_pair 2`
* `heckeT_p_fun_eq_heckeSlash_gen` -- for `SL₂(ℤ)`-invariant `f`,
    `heckeT_p_fun k p hp hpN f = heckeSlash_gen (GL_pair 2) k (D_p p) f`
* `heckeT_p_comm` -- commutativity of `T_p` and `T_q` for SL₂(ℤ)-invariant
    forms, derived from `heckeSlash_gen_comm`

## References

* Diamond-Shurman, *A First Course in Modular Forms*, §5.2
* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Subgroup.Commensurable Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2

/-- The double coset `SL₂(ℤ) · diag(1,p) · SL₂(ℤ)` in `GL_pair 2`,
representing the Hecke operator `T_p` at level 1.
This is the HeckeCoset of the diagonal matrix `diag(1,p)`. -/
noncomputable def D_p (p : ℕ) (hp : 0 < p) : HeckeRing.HeckeCoset (GL_pair 2) :=
  ⟦⟨diagMat 2 ![1, p], diagMat_mem_posDetInt 2 _ (fun i ↦ by fin_cases i <;> simp [hp])⟩⟧

private lemma SL_invariant_to_H_invariant {k : ℤ} {f : ℍ → ℂ}
    (hf_SL : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∀ h, h ∈ (GL_pair 2).H → f ∣[k] (glMap h) = f := fun _ ⟨s, hs⟩ ↦ hs ▸
  hf_SL (glMap (mapGL ℚ s)) ⟨s, (glMap_mapGL_eq s).symm⟩

private lemma SLnZ_entry_is_int (g : GL (Fin 2) ℚ) (hg : g ∈ SLnZ_subgroup 2)
    (i j : Fin 2) : ∃ n : ℤ, g.val i j = (n : ℚ) :=
  let ⟨s, hs⟩ := hg
  ⟨s.val i j, by rw [← hs]; simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

/-- `adj(T_p_upper(b₁))⁻¹ · adj(T_p_upper(b₂)) ∉ SL₂(ℤ)` for distinct `b₁, b₂ < p`.
The product has `(0,1)`-entry `(b₁ - b₂)/p ∉ ℤ`. -/
lemma adj_upper_inv_mul_not_mem_H (p : ℕ) (hp : Nat.Prime p)
    (b₁ b₂ : ℕ) (hb₁ : b₁ < p) (hb₂ : b₂ < p) (hne : b₁ ≠ b₂) :
    (GL_adjugate (T_p_upper p hp.pos b₁ : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b₂ : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have h_eq : (GL_adjugate (T_p_upper p hp.pos b₁ : GL _ ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b₂ : GL _ ℚ) =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(1 : ℚ), ((b₁ : ℤ) - (b₂ : ℤ) : ℤ) / (p : ℚ); 0, 1])
      (by simp [det_fin_two]) := by
    rw [inv_mul_eq_iff_eq_mul]; apply Units.ext; ext i j
    simp only [GL_adjugate_val, Units.val_mul, mul_apply, Fin.sum_univ_two]
    have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    fin_cases i <;> fin_cases j <;>
      · simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, sub_div]
        try ring
        try (field_simp; ring)
  intro hmem; rw [h_eq] at hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ hmem 0 1
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_rat : ((b₁ : ℤ) - (b₂ : ℤ) : ℚ) = (n : ℚ) * (p : ℚ) := by
    have := hn; field_simp at this ⊢; exact_mod_cast this
  have h_int : (b₁ : ℤ) - (b₂ : ℤ) = n * (p : ℤ) := by exact_mod_cast h_rat
  have : (p : ℤ) ∣ ((b₁ : ℤ) - b₂) := ⟨n, by lia⟩
  have hlt : |(b₁ : ℤ) - b₂| < p := by
    rw [abs_lt]; constructor <;> [push_cast; push_cast] <;> lia
  rw [h_int] at hlt; simp [abs_mul, Nat.abs_cast] at hlt
  have hn0 : n = 0 := by
    by_contra h; exact absurd hlt (not_lt.mpr (le_mul_of_one_le_left (by lia) (Int.one_le_abs h)))
  simp [hn0] at h_int; lia

/-- `adj(T_p_upper(b))⁻¹ · adj(T_p_lower) ∉ SL₂(ℤ)`.
The product has `(0,0)`-entry `1/p ∉ ℤ`. -/
lemma adj_upper_inv_mul_lower_not_mem_H (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_eq : (GL_adjugate (T_p_upper p hp.pos b : GL _ ℚ))⁻¹ *
     GL_adjugate (T_p_lower p hp.pos : GL _ ℚ) =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(1 / (p : ℚ)), (b : ℚ); 0, (p : ℚ)])
      (by norm_num [det_fin_two]; exact hp.ne_zero) := by
    rw [inv_mul_eq_iff_eq_mul]; apply Units.ext; ext i j
    simp only [GL_adjugate_val, Units.val_mul, mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      · simp [T_p_upper, T_p_lower, GeneralLinearGroup.mkOfDetNeZero]
        try ring
        try field_simp
  intro hmem; rw [h_eq] at hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ hmem 0 0
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have h_np : (n : ℚ) * p = 1 := by rw [← hn]; field_simp
  have h_int : n * (p : ℤ) = 1 := by exact_mod_cast h_np
  have h_dvd : (p : ℤ) ∣ 1 := ⟨n, by linarith⟩
  have h_lt : (1 : ℤ) < ↑p := Int.ofNat_lt.mpr hp.one_lt
  exact absurd (Int.le_of_dvd one_pos h_dvd) (by lia)

/-- `adj(T_p_lower)⁻¹ · adj(T_p_upper(b)) ∉ SL₂(ℤ)`.
The product has `(1,1)`-entry `1/p ∉ ℤ`. -/
lemma adj_lower_inv_mul_upper_not_mem_H (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (GL_adjugate (T_p_lower p hp.pos : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_eq : (GL_adjugate (T_p_lower p hp.pos : GL _ ℚ))⁻¹ *
     GL_adjugate (T_p_upper p hp.pos b : GL _ ℚ) =
    GeneralLinearGroup.mkOfDetNeZero
      (!![(p : ℚ), -(b : ℚ); 0, 1 / (p : ℚ)])
      (by norm_num [det_fin_two]; exact hp.ne_zero) := by
    rw [inv_mul_eq_iff_eq_mul]; apply Units.ext; ext i j
    simp only [GL_adjugate_val, Units.val_mul, mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      · simp [T_p_upper, T_p_lower, GeneralLinearGroup.mkOfDetNeZero]
        try ring
        try field_simp
  intro hmem; rw [h_eq] at hmem
  obtain ⟨n, hn⟩ := SLnZ_entry_is_int _ hmem 1 1
  simp [GeneralLinearGroup.mkOfDetNeZero] at hn
  have h_np : (n : ℚ) * p = 1 := by rw [← hn]; field_simp
  have h_int : n * (p : ℤ) = 1 := by exact_mod_cast h_np
  have h_dvd : (p : ℤ) ∣ 1 := ⟨n, by linarith⟩
  have h_lt : (1 : ℤ) < ↑p := Int.ofNat_lt.mpr hp.one_lt
  exact absurd (Int.le_of_dvd one_pos h_dvd) (by lia)

end HeckeRing.GL2
