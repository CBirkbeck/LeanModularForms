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

/-- `T_p_lower = [[p,0],[0,1]]` lies in the double coset `D_p`.
It equals `[[0,-1],[1,0]] · diag(1,p) · [[0,1],[-1,0]]`, where both factors are in SL₂(ℤ). -/
lemma T_p_lower_mem_D_p (p : ℕ) (hp : Nat.Prime p) :
    (T_p_lower p hp.pos : GL (Fin 2) ℚ) ∈ HeckeCoset.toSet (D_p p hp.pos) := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  have hrep := HeckeCoset.rep_mem (D_p p hp.pos)
  rw [D_p, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, habc⟩ := hrep
  have hw_det : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set w : SL(2, ℤ) := ⟨!![(0 : ℤ), -1; 1, 0], hw_det⟩
  have hw_mem : mapGL ℚ w ∈ (GL_pair 2).H := coe_mem_SLnZ 2 w
  have hwinv_det : (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set winv : SL(2, ℤ) := ⟨!![(0 : ℤ), 1; -1, 0], hwinv_det⟩
  have hwinv_mem : mapGL ℚ winv ∈ (GL_pair 2).H := coe_mem_SLnZ 2 winv
  have hfact : (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
      mapGL ℚ w * diagMat 2 ![1, p] * mapGL ℚ winv := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k ↦ by
      fin_cases k <;> simp [hp.pos]
    simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, w, winv,
        mapGL_coe_matrix, algebraMap_int_eq]
  have hdiag_eq : (diagMat 2 ![1, p] : GL _ ℚ) =
      a⁻¹ * ((D_p p hp.pos).rep : GL _ ℚ) * c⁻¹ := by
    change (diagMat 2 ![1, p] : GL _ ℚ) = a⁻¹ * ↑(HeckeCoset.rep (D_p p hp.pos)) * c⁻¹
    unfold D_p; rw [habc]; group
  refine ⟨mapGL ℚ w * a⁻¹, (GL_pair 2).H.mul_mem hw_mem ((GL_pair 2).H.inv_mem ha),
    c⁻¹ * mapGL ℚ winv, (GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hc) hwinv_mem, ?_⟩
  rw [hfact, hdiag_eq]; group

private lemma SL_invariant_to_H_invariant {k : ℤ} {f : ℍ → ℂ}
    (hf_SL : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∀ h, h ∈ (GL_pair 2).H → f ∣[k] (glMap h) = f := fun _ ⟨s, hs⟩ ↦ hs ▸
  hf_SL (glMap (mapGL ℚ s)) ⟨s, (glMap_mapGL_eq s).symm⟩

private lemma slash_eq_tRep_gen_of_adj_mem (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) (D : HeckeCoset (GL_pair 2)) (g h₁ h₂ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (GL_pair 2).H) (hh₂ : h₂ ∈ (GL_pair 2).H)
    (hadj : GL_adjugate g = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    f ∣[k] g = f ∣[k] tRep_gen (GL_pair 2) D ⟦⟨h₁, hh₁⟩⟧ := by
  rw [show g = GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) from by
    rw [← hadj, GL_adjugate_involutive]]
  exact slash_tRep_gen_of_mem k D h₁ h₂ hh₁ hh₂ f (SL_invariant_to_H_invariant hf)

private lemma GL_adjugate_mem_D (D : HeckeCoset (GL_pair 2))
    (g : GL (Fin 2) ℚ) (hg : g ∈ HeckeCoset.toSet D)
    (hadj_rep : GL_adjugate (HeckeCoset.rep D : GL _ ℚ) ∈ HeckeCoset.toSet D) :
    GL_adjugate g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hg hadj_rep ⊢
  obtain ⟨a, ha, c, hc, heq⟩ := hg
  obtain ⟨r₁, hr₁, r₂, hr₂, hrep_eq⟩ := hadj_rep
  refine ⟨GL_adjugate c * r₁,
    (GL_pair 2).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hr₁,
    r₂ * GL_adjugate a,
    (GL_pair 2).H.mul_mem hr₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  rw [heq, GL_adjugate_mul, GL_adjugate_mul,
    show GL_adjugate (HeckeCoset.rep D : GL _ ℚ) = r₁ * (HeckeCoset.rep D : GL _ ℚ) * r₂
      from hrep_eq]
  group

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

private lemma adj_inv_mul_mem_H_of_decompQuot_eq (D : HeckeCoset (GL_pair 2))
    (a₁ : GL _ ℚ) (ha₁ : a₁ ∈ (GL_pair 2).H) (c₁ : GL _ ℚ) (hc₁ : c₁ ∈ (GL_pair 2).H)
    (a₂ : GL _ ℚ) (ha₂ : a₂ ∈ (GL_pair 2).H) (c₂ : GL _ ℚ) (hc₂ : c₂ ∈ (GL_pair 2).H)
    (g₁ g₂ : GL _ ℚ)
    (heq₁ : GL_adjugate g₁ = a₁ * (HeckeCoset.rep D : GL _ ℚ) * c₁)
    (heq₂ : GL_adjugate g₂ = a₂ * (HeckeCoset.rep D : GL _ ℚ) * c₂)
    (hquot : (⟦(⟨a₁, ha₁⟩ : (GL_pair 2).H)⟧ : decompQuot (GL_pair 2) (HeckeCoset.rep D)) =
      ⟦⟨a₂, ha₂⟩⟧) :
    (GL_adjugate g₁)⁻¹ * GL_adjugate g₂ ∈ (GL_pair 2).H := by
  rw [heq₁, heq₂]
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact hquot)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hrel
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, map_inv, inv_inv,
    Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  rw [show (a₁ * ↑(HeckeCoset.rep D) * c₁)⁻¹ * (a₂ * ↑(HeckeCoset.rep D) * c₂) =
      c₁⁻¹ * ((↑(HeckeCoset.rep D))⁻¹ * (a₁⁻¹ * a₂) * ↑(HeckeCoset.rep D)) * c₂ from by group]
  exact (GL_pair 2).H.mul_mem ((GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hc₁) hrel) hc₂

end HeckeRing.GL2
