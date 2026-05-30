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

/-- `T_p_upper(b)` has det p > 0 and integer entries, hence lies in Δ. -/
lemma T_p_upper_mem_Delta (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (T_p_upper p hp b : GL (Fin 2) ℚ) ∈ (GL_pair 2).Δ := by
  refine ⟨⟨!![1, (b : ℤ); 0, (p : ℤ)], ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, Matrix.map_apply]
  · rw [T_p_upper_det]; exact_mod_cast hp

/-- `T_p_lower` has det p > 0 and integer entries, hence lies in Δ. -/
lemma T_p_lower_mem_Delta (p : ℕ) (hp : 0 < p) :
    (T_p_lower p hp : GL (Fin 2) ℚ) ∈ (GL_pair 2).Δ := by
  refine ⟨⟨!![(p : ℤ), 0; 0, 1], ?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero, Matrix.map_apply]
  · rw [T_p_lower_det]; exact_mod_cast hp

/-- `T_p_upper(b)` lies in the double coset `D_p` for `b < p`.
Both `diag(1,p)` and `T_p_upper(b) = [[1,b],[0,p]]` have determinant `p`, and
their ratio lies in `SL₂(ℤ)` on both sides. -/
lemma T_p_upper_mem_D_p (p : ℕ) (hp : Nat.Prime p) (b : ℕ) :
    (T_p_upper p hp.pos b : GL (Fin 2) ℚ) ∈ HeckeCoset.toSet (D_p p hp.pos) := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  have hrep := HeckeCoset.rep_mem (D_p p hp.pos)
  rw [D_p, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, habc⟩ := hrep
  have hσ_det : (!![1, (b : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set σ_b : SL(2, ℤ) := ⟨!![1, (b : ℤ); 0, 1], hσ_det⟩
  have hσ_mem : mapGL ℚ σ_b ∈ (GL_pair 2).H := coe_mem_SLnZ 2 σ_b
  have hfact : (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
      diagMat 2 ![1, p] * (mapGL ℚ σ_b) := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k ↦ by
      fin_cases k <;> simp [hp.pos]
    simp only [diagMat_val _ _ hpos, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply]
    fin_cases i <;> fin_cases j <;>
      simp [T_p_upper, GeneralLinearGroup.mkOfDetNeZero, σ_b, mapGL_coe_matrix, algebraMap_int_eq]
  have hdiag_eq : (diagMat 2 ![1, p] : GL _ ℚ) =
      a⁻¹ * ((D_p p hp.pos).rep : GL _ ℚ) * c⁻¹ := by
    change (diagMat 2 ![1, p] : GL _ ℚ) = a⁻¹ * ↑(HeckeCoset.rep (D_p p hp.pos)) * c⁻¹
    unfold D_p; rw [habc]; group
  refine ⟨a⁻¹, (GL_pair 2).H.inv_mem ha, c⁻¹ * mapGL ℚ σ_b,
    (GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hc) hσ_mem, ?_⟩
  rw [hfact, hdiag_eq, mul_assoc, mul_assoc]

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
    ∀ h, h ∈ (GL_pair 2).H → f ∣[k] (glMap h) = f := by
  intro h hh; obtain ⟨s, hs⟩ := hh; rw [← hs]
  exact hf_SL (glMap (mapGL ℚ s)) ⟨s, (glMap_mapGL_eq s).symm⟩

/-- `T_p_lower = w * diag(1,p) * w⁻¹` where `w = [[0,-1],[1,0]] ∈ SL₂(ℤ)`.
For SL₂(ℤ)-invariant `f`, the left `w` factor is absorbed:
`f ∣[k] T_p_lower = (f ∣[k] diag(1,p)) ∣[k] w⁻¹`. -/
lemma slash_T_p_lower_factor (k : ℤ) (p : ℕ) (hp : Nat.Prime p)
    (f : ℍ → ℂ) (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
    (f ∣[k] (diagMat 2 ![1, p] : GL (Fin 2) ℚ)) ∣[k]
      (mapGL ℚ ⟨!![(0 : ℤ), 1; -1, 0],
        by simp [det_fin_two]⟩ : GL (Fin 2) ℚ) := by
  have hw_det : (!![(0 : ℤ), -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set w : SL(2, ℤ) := ⟨!![(0 : ℤ), -1; 1, 0], hw_det⟩
  have hwinv_det : (!![(0 : ℤ), 1; -1, 0] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp [det_fin_two]
  set winv : SL(2, ℤ) := ⟨!![(0 : ℤ), 1; -1, 0], hwinv_det⟩
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
  rw [hfact, SlashAction.slash_mul, SlashAction.slash_mul]
  congr 2
  exact SL_invariant_to_H_invariant hf _ ⟨w, rfl⟩

private lemma slash_eq_tRep_gen_of_adj_mem (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f)
    (D : HeckeCoset (GL_pair 2))
    (g : GL (Fin 2) ℚ) (h₁ h₂ : GL (Fin 2) ℚ)
    (hh₁ : h₁ ∈ (GL_pair 2).H) (hh₂ : h₂ ∈ (GL_pair 2).H)
    (hadj : GL_adjugate g = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    f ∣[k] g = f ∣[k] tRep_gen (GL_pair 2) D ⟦⟨h₁, hh₁⟩⟧ := by
  have hg : g = GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) := by
    rw [← hadj, GL_adjugate_involutive]
  rw [hg]
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
  rw [heq, GL_adjugate_mul, GL_adjugate_mul]
  rw [show GL_adjugate (HeckeCoset.rep D : GL _ ℚ) = r₁ * (HeckeCoset.rep D : GL _ ℚ) * r₂
    from hrep_eq]
  group

private lemma adj_rep_mem_D_p (p : ℕ) (hp : Nat.Prime p) :
    GL_adjugate (HeckeCoset.rep (D_p p hp.pos) : GL _ ℚ) ∈
      HeckeCoset.toSet (D_p p hp.pos) := by
  have hrep := HeckeCoset.rep_mem (D_p p hp.pos)
  rw [D_p, HeckeCoset.toSet_mk, DoubleCoset.mem_doubleCoset] at hrep
  obtain ⟨a, ha, c, hc, hrep_eq⟩ := hrep
  have hTl := T_p_lower_mem_D_p p hp
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hTl
  obtain ⟨b₁, hb₁, b₂, hb₂, hTl_eq⟩ := hTl
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  have hadj_diag : GL_adjugate (diagMat 2 ![1, p] : GL _ ℚ) =
      (T_p_lower p hp.pos : GL _ ℚ) := by
    apply Units.ext; ext i j
    have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → Nat) k := fun k ↦ by
      fin_cases k <;> simp [hp.pos]
    simp only [GL_adjugate_val, diagMat_val _ _ hpos]
    have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
      ext x; fin_cases x <;> simp
    have he0 : ({0, 1} : Finset (Fin 2)).erase 0 = {1} := by decide
    have he1 : ({0, 1} : Finset (Fin 2)).erase 1 = {0} := by decide
    fin_cases i <;> fin_cases j <;>
      simp [T_p_lower, GeneralLinearGroup.mkOfDetNeZero,
        Matrix.of_apply, huniv, he0, he1,
        Finset.prod_singleton]
  refine ⟨GL_adjugate c * b₁,
    (GL_pair 2).H.mul_mem (HeckePairAction.adjugate_mem_H c hc) hb₁,
    b₂ * GL_adjugate a,
    (GL_pair 2).H.mul_mem hb₂ (HeckePairAction.adjugate_mem_H a ha), ?_⟩
  have h1 : GL_adjugate (HeckeCoset.rep (D_p p hp.pos) : GL _ ℚ) =
      GL_adjugate c * GL_adjugate (diagMat 2 ![1, p]) * GL_adjugate a := by
    conv_lhs => rw [show (HeckeCoset.rep (D_p p hp.pos) : GL _ ℚ) =
      a * diagMat 2 ![1, p] * c from hrep_eq]
    rw [GL_adjugate_mul, GL_adjugate_mul, mul_assoc]
  rw [h1, hadj_diag, hTl_eq]; group

private lemma SLnZ_entry_is_int (g : GL (Fin 2) ℚ) (hg : g ∈ SLnZ_subgroup 2)
    (i j : Fin 2) : ∃ n : ℤ, g.val i j = (n : ℚ) := by
  obtain ⟨s, rfl⟩ := hg
  exact ⟨s.val i j, by simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

private lemma adj_mem_dc (D : HeckeCoset (GL_pair 2))
    (g : GL (Fin 2) ℚ) (hg : g ∈ HeckeCoset.toSet D)
    (hadj_rep : GL_adjugate (HeckeCoset.rep D : GL _ ℚ) ∈ HeckeCoset.toSet D) :
    ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (GL_pair 2).H) (h₂ : GL _ ℚ) (_ : h₂ ∈ (GL_pair 2).H),
      GL_adjugate g = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂ := by
  have := GL_adjugate_mem_D D g hg hadj_rep
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at this
  obtain ⟨a, ha, b, hb, heq⟩ := this
  exact ⟨a, ha, b, hb, heq⟩

private lemma card_decompQuot_D_p (p : ℕ) (hp : Nat.Prime p) :
    Fintype.card (decompQuot (GL_pair 2) (HeckeCoset.rep (D_p p hp.pos))) = p + 1 := by
  have h1 : D_p p hp.pos = T_diag (![1, p]) := by
    change ⟦⟨diagMat 2 ![1, p], _⟩⟧ = ⟦diagMat_delta 2 ![1, p]⟧
    unfold diagMat_delta; simp [dif_pos hp.pos]
  have h2 : HeckeCoset_deg (GL_pair 2) (D_p p hp.pos) = ↑(p + 1) := by
    rw [h1]; convert deg_T_diag_ppow p hp 0 1 (by lia) using 2
    · congr 1; ext i; fin_cases i <;> simp
    · simp
  simp only [HeckeCoset_deg] at h2; exact_mod_cast h2

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
  have h_dvd : (p : ℤ) ∣ 1 := ⟨n, by lia⟩
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
  have h_dvd : (p : ℤ) ∣ 1 := ⟨n, by lia⟩
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

private lemma sum_range_add_eq_sum_fin_succ_dite {M : Type*} [AddCommMonoid M]
    (p : ℕ) (F : ℕ → M) (G : M) :
    (∑ j ∈ Finset.range p, F j) + G =
    ∑ j : Fin (p + 1), if _h : (j : ℕ) < p then F (j : ℕ) else G := by
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_castSucc]; congr 1
  · congr 1; ext j; simp [j.isLt]
  · simp

private lemma adj_Tp_rep_inv_mul_not_mem_H (p : ℕ) (hp : Nat.Prime p)
    (j₁ j₂ : Fin (p + 1)) (hne : j₁ ≠ j₂) :
    (GL_adjugate (if (j₁ : ℕ) < p then T_p_upper p hp.pos (j₁ : ℕ)
        else T_p_lower p hp.pos : GL (Fin 2) ℚ))⁻¹ *
     GL_adjugate (if (j₂ : ℕ) < p then T_p_upper p hp.pos (j₂ : ℕ)
        else T_p_lower p hp.pos : GL (Fin 2) ℚ) ∉ (GL_pair 2).H := by
  split_ifs
  · exact adj_upper_inv_mul_not_mem_H p hp (j₁ : ℕ) (j₂ : ℕ) ‹(j₁ : ℕ) < p› ‹(j₂ : ℕ) < p›
      (fun h ↦ hne (Fin.ext h))
  · exact adj_upper_inv_mul_lower_not_mem_H p hp (j₁ : ℕ)
  · exact adj_lower_inv_mul_upper_not_mem_H p hp (j₂ : ℕ)
  · exact absurd (Fin.ext (show (j₁ : ℕ) = (j₂ : ℕ) by
      have := j₁.isLt; have := j₂.isLt; lia)) hne

private lemma sum_tRep_gen_eq_sum_of_adj_factored {ι : Type*} [Fintype ι] (k : ℤ) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) (D : HeckeCoset (GL_pair 2)) (g : ι → GL (Fin 2) ℚ)
    (hcard : Fintype.card ι = Fintype.card (decompQuot (GL_pair 2) (HeckeCoset.rep D)))
    (hfac : ∀ j, ∃ (h₁ : GL _ ℚ) (_ : h₁ ∈ (GL_pair 2).H)
        (h₂ : GL _ ℚ) (_ : h₂ ∈ (GL_pair 2).H),
        GL_adjugate (g j) = h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)
    (hdist : ∀ j₁ j₂, j₁ ≠ j₂ →
        (GL_adjugate (g j₁))⁻¹ * GL_adjugate (g j₂) ∉ (GL_pair 2).H) :
    ∑ σ : decompQuot (GL_pair 2) (HeckeCoset.rep D), f ∣[k] tRep_gen (GL_pair 2) D σ =
    ∑ j, f ∣[k] g j := by
  classical
  let φ : ι → decompQuot (GL_pair 2) (HeckeCoset.rep D) := fun j ↦
    ⟦⟨(hfac j).choose, (hfac j).choose_spec.choose⟩⟧
  have h_val : ∀ j, f ∣[k] g j = f ∣[k] tRep_gen (GL_pair 2) D (φ j) := fun j ↦
    slash_eq_tRep_gen_of_adj_mem k f hf D _ _ _ (hfac j).choose_spec.choose
      (hfac j).choose_spec.choose_spec.choose_spec.choose
      (hfac j).choose_spec.choose_spec.choose_spec.choose_spec
  have h_inj : Function.Injective φ := by
    intro j₁ j₂ heq
    by_contra hne
    refine hdist j₁ j₂ hne (adj_inv_mul_mem_H_of_decompQuot_eq D
      (hfac j₁).choose (hfac j₁).choose_spec.choose
      (hfac j₁).choose_spec.choose_spec.choose
      (hfac j₁).choose_spec.choose_spec.choose_spec.choose
      (hfac j₂).choose (hfac j₂).choose_spec.choose
      (hfac j₂).choose_spec.choose_spec.choose
      (hfac j₂).choose_spec.choose_spec.choose_spec.choose
      (g j₁) (g j₂) (hfac j₁).choose_spec.choose_spec.choose_spec.choose_spec
      (hfac j₂).choose_spec.choose_spec.choose_spec.choose_spec heq)
  have h_bij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]; exact ⟨h_inj, hcard⟩
  exact (Fintype.sum_bijective φ h_bij _ _ h_val).symm

theorem tRep_gen_D_p_matches_T_p_reps (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∑ i : decompQuot (GL_pair 2) (HeckeCoset.rep (D_p p hp.pos)),
      f ∣[k] tRep_gen (GL_pair 2) (D_p p hp.pos) i =
    (∑ b ∈ Finset.range p, f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) +
      f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) := by
  set D := D_p p hp.pos
  have hadj_rep := adj_rep_mem_D_p p hp
  set g : Fin (p + 1) → GL (Fin 2) ℚ := fun j ↦
    if (j : ℕ) < p then T_p_upper p hp.pos (j : ℕ) else T_p_lower p hp.pos with hg
  have hmem : ∀ j, g j ∈ HeckeCoset.toSet D := by
    intro j; simp only [hg]; split_ifs
    · exact T_p_upper_mem_D_p p hp (j : ℕ)
    · exact T_p_lower_mem_D_p p hp
  have hfac := fun j ↦ adj_mem_dc D (g j) (hmem j) hadj_rep
  have hdist : ∀ j₁ j₂ : Fin (p + 1), j₁ ≠ j₂ →
      (GL_adjugate (g j₁))⁻¹ * GL_adjugate (g j₂) ∉ (GL_pair 2).H := by
    intro j₁ j₂ hne; simp only [hg]; exact adj_Tp_rep_inv_mul_not_mem_H p hp j₁ j₂ hne
  rw [sum_tRep_gen_eq_sum_of_adj_factored k f hf D g
      (by rw [Fintype.card_fin]; exact (card_decompQuot_D_p p hp).symm) hfac hdist,
    sum_range_add_eq_sum_fin_succ_dite p
      (fun n ↦ f ∣[k] (T_p_upper p hp.pos n : GL (Fin 2) ℚ))
      (f ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ))]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [hg]; split_ifs <;> rfl

/-- For an SL₂(ℤ)-invariant modular form, the diamond operator acts trivially:
`⟨d⟩f = f` for any `d ∈ (ℤ/Nℤ)ˣ`, because every `Γ₀(N)` element lies in `SL₂(ℤ)`. -/
lemma diamondOp_trivial_of_SL_invariant {N : ℕ} [NeZero N] (k : ℤ) (u : (ZMod N)ˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    ⇑(diamondOp k u f) = ⇑f := by
  obtain ⟨g, hg⟩ := Gamma0MapUnits_surjective u
  rw [diamondOp_eq_diamondOpAux k u g hg]
  change (⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) = ⇑f
  exact hf_SL _ ⟨g, rfl⟩

/-- **Main theorem.** For an SL₂(ℤ)-invariant function `f : ℍ → ℂ`, the explicit
Hecke operator `T_p` (at any level N with `gcd(p,N) = 1`) reduces on SL₂(ℤ)-invariant
forms to the abstract Hecke operator `heckeSlash_gen (GL_pair 2) k (D_p p)`. -/
theorem heckeT_p_fun_eq_heckeSlash_gen {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ)
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    heckeT_p_fun k p hp hpN f =
    heckeSlash_gen (GL_pair 2) k (D_p p hp.pos) (⇑f) := by
  rw [heckeSlash_gen, tRep_gen_D_p_matches_T_p_reps k p hp (⇑f) hf_SL]
  simp only [heckeT_p_fun, heckeT_p_ut]
  congr 2
  exact diamondOp_trivial_of_SL_invariant k _ f hf_SL

/-- The heckeSlash_gen operators commute for GL_pair 2 because the Hecke algebra
`𝕋 (GL_pair 2) ℤ` is commutative. -/
theorem heckeSlash_gen_GL_pair_comm (k : ℤ) (D₁ D₂ : HeckeCoset (GL_pair 2)) (f : ℍ → ℂ)
    (hf : ∀ h, h ∈ (GL_pair 2).H → f ∣[k] (glMap h) = f) :
    heckeSlash_gen (GL_pair 2) k D₁ (heckeSlash_gen (GL_pair 2) k D₂ f) =
    heckeSlash_gen (GL_pair 2) k D₂ (heckeSlash_gen (GL_pair 2) k D₁ f) :=
  heckeSlash_gen_comm k D₁ D₂ f hf (fun _ _ ↦ mul_comm _ _)

private lemma heckeSlash_gen_SL_invariant {k : ℤ} (D : HeckeCoset (GL_pair 2)) {f : ℍ → ℂ}
    (hf_SL : ∀ γ ∈ 𝒮ℒ, f ∣[k] γ = f) :
    ∀ γ ∈ 𝒮ℒ, (heckeSlash_gen (GL_pair 2) k D f) ∣[k] γ =
      heckeSlash_gen (GL_pair 2) k D f := by
  intro γ hγ; obtain ⟨s, hs⟩ := hγ
  have hmem : mapGL ℚ s ∈ (GL_pair 2).H := ⟨s, rfl⟩
  rw [← hs]
  change (heckeSlash_gen (GL_pair 2) k D f) ∣[k] glMap (mapGL ℚ s) =
    heckeSlash_gen (GL_pair 2) k D f
  exact heckeSlash_gen_slash_invariant k D f (SL_invariant_to_H_invariant hf_SL) _ hmem

/-- **Commutativity of Hecke operators at level 1.**
For SL₂(ℤ)-invariant `f`, the Hecke operators `T_p` and `T_q` commute:
`T_p(T_q(f)) = T_q(T_p(f))`. -/
theorem heckeT_p_fun_comm_of_GL_pair {N : ℕ} [NeZero N] (k : ℤ)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    heckeT_p_fun k p hp hpN (⟨⟨heckeT_p_fun k q hq hqN f,
        (heckeT_p k q hq hqN f).slash_action_eq'⟩,
        (heckeT_p k q hq hqN f).holo',
        (heckeT_p k q hq hqN f).bdd_at_cusps'⟩ : ModularForm _ k) =
    heckeT_p_fun k q hq hqN (⟨⟨heckeT_p_fun k p hp hpN f,
        (heckeT_p k p hp hpN f).slash_action_eq'⟩,
        (heckeT_p k p hp hpN f).holo',
        (heckeT_p k p hp hpN f).bdd_at_cusps'⟩ : ModularForm _ k) := by
  have heckeT_p_fun_SL : ∀ r : ℕ, ∀ hr : Nat.Prime r, ∀ hrN : Nat.Coprime r N,
      ∀ γ ∈ 𝒮ℒ, heckeT_p_fun k r hr hrN f ∣[k] γ = heckeT_p_fun k r hr hrN f :=
    fun r hr hrN γ hγ ↦ by
      rw [heckeT_p_fun_eq_heckeSlash_gen k r hr hrN f hf_SL]
      exact heckeSlash_gen_SL_invariant (D_p r hr.pos) hf_SL γ hγ
  have hTqf_SL := heckeT_p_fun_SL q hq hqN
  have hTpf_SL := heckeT_p_fun_SL p hp hpN
  set Tqf : ModularForm _ k :=
    ⟨⟨heckeT_p_fun k q hq hqN f, (heckeT_p k q hq hqN f).slash_action_eq'⟩,
     (heckeT_p k q hq hqN f).holo', (heckeT_p k q hq hqN f).bdd_at_cusps'⟩
  set Tpf : ModularForm _ k :=
    ⟨⟨heckeT_p_fun k p hp hpN f, (heckeT_p k p hp hpN f).slash_action_eq'⟩,
     (heckeT_p k p hp hpN f).holo', (heckeT_p k p hp hpN f).bdd_at_cusps'⟩
  rw [heckeT_p_fun_eq_heckeSlash_gen k p hp hpN Tqf hTqf_SL,
      heckeT_p_fun_eq_heckeSlash_gen k q hq hqN Tpf hTpf_SL]
  change heckeSlash_gen (GL_pair 2) k (D_p p hp.pos) (heckeT_p_fun k q hq hqN f) =
    heckeSlash_gen (GL_pair 2) k (D_p q hq.pos) (heckeT_p_fun k p hp hpN f)
  conv_lhs => rw [heckeT_p_fun_eq_heckeSlash_gen k q hq hqN f hf_SL]
  conv_rhs => rw [heckeT_p_fun_eq_heckeSlash_gen k p hp hpN f hf_SL]
  exact heckeSlash_gen_GL_pair_comm k (D_p p hp.pos) (D_p q hq.pos) (⇑f)
    (SL_invariant_to_H_invariant hf_SL)

/-- Cleaner version using the `heckeT_p` linear map directly. -/
theorem heckeT_p_comm {N : ℕ} [NeZero N] (k : ℤ)
    (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpN : Nat.Coprime p N) (hqN : Nat.Coprime q N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_SL : ∀ γ ∈ 𝒮ℒ, (⇑f) ∣[k] γ = ⇑f) :
    heckeT_p k p hp hpN (heckeT_p k q hq hqN f) =
    heckeT_p k q hq hqN (heckeT_p k p hp hpN f) := by
  ext z
  exact congr_fun (heckeT_p_fun_comm_of_GL_pair k p q hp hq hpN hqN f hf_SL) z

end HeckeRing.GL2
