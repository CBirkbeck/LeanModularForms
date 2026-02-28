/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_TextbookPackaging
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_OrbitSum
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_OrbitPairing
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_TextbookOrbitFinsum_Existence
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Textbook Orbit-Finsum Form of the Valence Formula

This file proves the valence formula in literal orbit-sum form using `∑ᶠ` over
non-elliptic orbits of `SL₂(ℤ)` acting on `ℍ`.

## Main Results

* `valenceFormula_textbook_orbit_finsum` — the valence formula with `∑ᶠ`
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-- The order of vanishing on non-elliptic orbits, cast to `ℂ`. -/
def ordOrbitQ (q : NonEllOrbit) : ℂ := (ordOrbit f q.val : ℂ)

/-! ## RepCanon points are not elliptic -/

private lemma rho_normSq_eq_one : Complex.normSq (ellipticPoint_rho' : ℂ) = 1 := by
  show Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  rw [Complex.normSq_apply]
  simp only [add_re, neg_re, one_re, div_ofNat_re, ofReal_re, mul_re, I_re, mul_zero,
    I_im, mul_one, sub_zero, add_im, neg_im, one_im, div_ofNat_im, ofReal_im, zero_div,
    mul_im, zero_mul, add_zero]
  ring_nf
  have h3 := Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
  nlinarith

private lemma rho_norm_eq_one : ‖(ellipticPoint_rho' : ℂ)‖ = 1 := by
  have h2 : ‖(ellipticPoint_rho' : ℂ)‖ ^ 2 = 1 := by
    rw [← normSq_eq_norm_sq]; exact rho_normSq_eq_one
  nlinarith [norm_nonneg (ellipticPoint_rho' : ℂ), sq_nonneg (‖(ellipticPoint_rho' : ℂ)‖ - 1)]

/-- RepCanon points are distinct from the three elliptic points. -/
private lemma repCanon_ne_elliptic (p : ℍ) (hp : p ∈ RepCanon f hf) :
    p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one' := by
  simp only [RepCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · -- RepStrict: explicitly excludes all three
    have hf := (Finset.mem_filter.mp h).2
    exact ⟨hf.1, hf.2.1, hf.2.2.1⟩
  · -- RepLeftVert: re = -1/2, ‖p‖ > 1
    have hf := (Finset.mem_filter.mp h).2
    refine ⟨?_, ?_, ?_⟩
    · intro heq; rw [heq] at hf
      have : (ellipticPoint_i' : ℂ).re = 0 := Complex.I_re
      linarith [hf.1]
    · intro heq; rw [heq] at hf; linarith [hf.2, rho_norm_eq_one]
    · intro heq; rw [heq] at hf
      have : (ellipticPoint_rho_plus_one' : ℂ).re = 1/2 := by
        show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2
        simp [add_re, mul_re, I_re, I_im]
      linarith [hf.1]
  · -- RepLeftArc: ‖p‖ = 1, re < 0, p ≠ ρ
    have hf := (Finset.mem_filter.mp h).2
    refine ⟨?_, hf.1, ?_⟩
    · intro heq; rw [heq] at hf
      have : (ellipticPoint_i' : ℂ).re = 0 := Complex.I_re
      linarith [hf.2.2]
    · intro heq; rw [heq] at hf
      have : (ellipticPoint_rho_plus_one' : ℂ).re = 1/2 := by
        show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2
        simp [add_re, mul_re, I_re, I_im]
      linarith [hf.2.2]

/-! ## Orbit identification: 𝒟' representatives of elliptic orbits -/

/-- Helper: denom of SL₂(ℤ) element at Complex.I simplifies to c*I + d. -/
private lemma denom_at_I (g : SL(2, ℤ)) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (Complex.I) =
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) * Complex.I +
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) := by
  simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.map]

/-- Helper: normSq of denom at I = c² + d². -/
private lemma normSq_denom_at_I (g : SL(2, ℤ)) :
    Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (Complex.I)) =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  rw [denom_at_I, Complex.normSq_apply]
  simp [add_re, mul_re, add_im, mul_im, Complex.I_re, Complex.I_im]
  ring

/-- Helper: det condition for SL₂(ℤ). -/
private lemma sl2_det (g : SL(2, ℤ)) :
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
    (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
  have h := g.prop
  rw [Matrix.det_fin_two] at h
  exact_mod_cast h

/-- Helper: `ellipticPoint_i'` is definitionally `⟨I, _⟩`. -/
private lemma ellipticPoint_i'_coe : (ellipticPoint_i' : ℂ) = Complex.I := rfl

/-- Helper: im of ellipticPoint_i' is 1. -/
private lemma ellipticPoint_i'_im : (ellipticPoint_i' : ℍ).im = 1 := by
  show (Complex.I : ℂ).im = 1; exact Complex.I_im

/-- Helper: points in 𝒟' have im > 1/2 (imported from OrbitSum). -/
private lemma fd'_im_gt_half' (p : ℍ) (hp : p ∈ 𝒟') : (1 : ℝ)/2 < (p : ℂ).im := by
  by_contra h_le; push_neg at h_le
  have hre : p.re = (↑p : ℂ).re := rfl
  have h_pos : (0 : ℝ) < (p : ℂ).im := p.2
  have h1 : (1 : ℝ) ≤ (p : ℂ).re * (p : ℂ).re + (p : ℂ).im * (p : ℂ).im := by
    have := hp.2
    have h_nsq := normSq_eq_norm_sq (p : ℂ)
    rw [Complex.normSq_apply] at h_nsq
    nlinarith [sq_nonneg (‖(p : ℂ)‖ - 1), sq_nonneg ‖(p : ℂ)‖]
  have ⟨hlo, hhi⟩ := abs_le.mp hp.1
  rw [hre] at hlo hhi
  have hre1 : (1/2 - (p : ℂ).re) * (1/2 + (p : ℂ).re) ≥ 0 :=
    mul_nonneg (by linarith) (by linarith)
  have him1 : (1/2 - (p : ℂ).im) * (p : ℂ).im ≥ 0 :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- Key lemma: if g • i ∈ 𝒟', then c² + d² = 1 (where c,d are bottom row of g). -/
private lemma normSq_denom_eq_one_of_smul_i_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPoint_i' ∈ 𝒟') :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1 := by
  -- Abbreviate c, d as ℤ values
  let c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  -- im(g•i) = 1/(c²+d²), im(g•i) > 1/2
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPoint_i'
  rw [ellipticPoint_i'_im, show (ellipticPoint_i' : ℂ) = I from rfl, normSq_denom_at_I] at h_im
  have h_gt : (1 : ℝ)/2 < (g • ellipticPoint_i').im := fd'_im_gt_half' _ h_fd
  rw [h_im] at h_gt
  -- The real sum S := c²+d²
  have h_pos : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 > 0 := by
    by_contra h_le; push_neg at h_le
    have h1 : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 = 0 := le_antisymm h_le (by positivity)
    have hc0 : c = 0 := by
      have : (c : ℝ) = 0 := by nlinarith [sq_nonneg (c : ℝ)]
      exact_mod_cast this
    have hd0 : d = 0 := by
      have : (d : ℝ) = 0 := by nlinarith [sq_nonneg (d : ℝ)]
      exact_mod_cast this
    have h_det : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * d -
                 (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c = 1 := sl2_det g
    simp [hc0, hd0] at h_det
  have h_lt2 : (c : ℝ) ^ 2 + (d : ℝ) ^ 2 < 2 := by
    have h1 := mul_lt_mul_of_pos_right h_gt h_pos
    rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt h_pos)] at h1; linarith
  -- Integer: c²+d² ≥ 1 and < 2 → = 1
  have h_ge : c ^ 2 + d ^ 2 ≥ 1 := by
    by_contra h; push_neg at h
    have hc0 : c = 0 := by nlinarith [sq_nonneg c]
    have hd0 : d = 0 := by nlinarith [sq_nonneg d]
    have h_det : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * d -
                 (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c = 1 := sl2_det g
    simp [hc0, hd0] at h_det
  have h_eq : c ^ 2 + d ^ 2 = 1 := by
    have : c ^ 2 + d ^ 2 < 2 := by exact_mod_cast h_lt2
    omega
  show (c : ℝ) ^ 2 + (d : ℝ) ^ 2 = 1
  exact_mod_cast h_eq

/-- Helper: re of g • i equals (ac+bd)/(c²+d²) where a,b,c,d are matrix entries. -/
private lemma re_smul_ellipticPoint_i (g : SL(2, ℤ)) :
    (g • ellipticPoint_i').re =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 +
     (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) /
    (((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 +
     ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2) := by
  show (↑(g • ellipticPoint_i') : ℂ).re = _
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, ellipticPoint_i'_coe]
  simp only [algebraMap_int_eq, Int.coe_castRingHom]
  rw [Complex.div_re, Complex.normSq_apply]
  simp only [add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_zero, add_im, mul_im, zero_mul, add_zero,
    zero_add, zero_sub]
  push_cast
  ring

/-- In 𝒟', the only representative of the orbit of `i` is `i` itself. -/
private theorem fd'_orbit_i_eq_i (p : ℍ) (hp : p ∈ 𝒟') (horb : orb p = oi) :
    p = ellipticPoint_i' := by
  -- Extract g with g • i = p from orbit equality
  have h_rel := Quotient.exact' horb
  obtain ⟨g, hg⟩ := (h_rel : ∃ g : SL(2, ℤ), g • ellipticPoint_i' = p)
  -- p = g • i, and p ∈ 𝒟'
  subst hg
  -- Key facts about g
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc_def
  set d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd_def
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha_def
  set b := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb_def
  -- c²+d² = 1 (as reals)
  have h_cd1 := normSq_denom_eq_one_of_smul_i_in_fd g hp
  -- im(g•i) = 1
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPoint_i'
  rw [ellipticPoint_i'_im, show (ellipticPoint_i' : ℂ) = I from rfl,
      normSq_denom_at_I, h_cd1, div_one] at h_im
  -- re constraint from 𝒟': |re(g•i)| ≤ 1/2
  have h_re_bound := hp.1
  -- re(g•i) = (ac+bd)/(c²+d²) = (ac+bd)/1 = ac+bd (integer!)
  have h_re := re_smul_ellipticPoint_i g
  rw [h_cd1, div_one] at h_re
  -- ac+bd is an integer, and |ac+bd| ≤ 1/2, so ac+bd = 0
  have h_re_is_int : ∃ n : ℤ, (g • ellipticPoint_i').re = (n : ℝ) :=
    ⟨a * c + b * d, by rw [h_re]; push_cast; ring⟩
  obtain ⟨n, hn⟩ := h_re_is_int
  have h_n_zero : n = 0 := by
    by_contra h_ne
    have : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs h_ne
    have h_bound_re := h_re_bound
    rw [hn] at h_bound_re
    linarith
  -- re = 0 and im = 1, conclude g • i = i
  have h_re_zero : (g • ellipticPoint_i').re = 0 := by rw [hn, h_n_zero, Int.cast_zero]
  have h_i_re : ellipticPoint_i'.re = 0 := show (Complex.I : ℂ).re = 0 from Complex.I_re
  have h_i_im : ellipticPoint_i'.im = 1 := ellipticPoint_i'_im
  exact UpperHalfPlane.ext' (by linarith) (by linarith)

/-- Helper: re and im of ρ. -/
private lemma ellipticPoint_rho'_re : (ellipticPoint_rho' : ℍ).re = -1/2 := by
  show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = -1/2
  simp [add_re, mul_re, I_re, I_im]

private lemma ellipticPoint_rho'_im : (ellipticPoint_rho' : ℍ).im = Real.sqrt 3 / 2 := by
  show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2
  simp [add_im, mul_im, I_re, I_im]

/-- Helper: re and im of ρ+1. -/
private lemma ellipticPoint_rho_plus_one'_re : (ellipticPoint_rho_plus_one' : ℍ).re = 1/2 := by
  show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2
  simp [add_re, mul_re, I_re, I_im]

private lemma ellipticPoint_rho_plus_one'_im : (ellipticPoint_rho_plus_one' : ℍ).im = Real.sqrt 3 / 2 := by
  show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im = Real.sqrt 3 / 2
  simp [add_im, mul_im, I_re, I_im]

/-- Helper: denom of SL₂(ℤ) element at ρ. -/
private lemma denom_at_rho (g : SL(2, ℤ)) :
    UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (ellipticPoint_rho' : ℍ) =
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) * (-1/2 + (Real.sqrt 3 / 2) * I) +
    ↑((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) := by
  simp [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.map, ellipticPoint_rho']

/-- Helper: normSq of denom at ρ = c² - cd + d². -/
private lemma normSq_denom_at_rho (g : SL(2, ℤ)) :
    Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) (ellipticPoint_rho' : ℍ)) =
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  rw [denom_at_rho, Complex.normSq_apply]
  simp only [add_re, mul_re, neg_re, one_re, div_ofNat_re, ofReal_re, mul_zero,
    I_re, I_im, sub_zero, mul_one, add_im, neg_im, one_im, div_ofNat_im, ofReal_im,
    zero_div, mul_im, zero_mul, add_zero, Complex.intCast_re, Complex.intCast_im]
  have h3 := Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
  ring_nf
  nlinarith

/-- Key lemma: if g • ρ ∈ 𝒟', then c² - cd + d² = 1 (where c,d are bottom row of g). -/
private lemma normSq_denom_eq_one_of_smul_rho_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPoint_rho' ∈ 𝒟') :
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1 := by
  -- Abbreviate c, d as ℤ values
  let c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  -- im(g•ρ) = (√3/2) / (c²-cd+d²), and im(g•ρ) > 1/2 from 𝒟'
  have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPoint_rho'
  rw [ellipticPoint_rho'_im, normSq_denom_at_rho] at h_im
  have h_gt : (1 : ℝ)/2 < (g • ellipticPoint_rho').im := fd'_im_gt_half' _ h_fd
  rw [h_im] at h_gt
  -- The real sum S := c²-cd+d²
  have h_pos : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 > 0 := by
    have h_nn : (0 : ℝ) ≤ (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 :=
      by nlinarith [sq_nonneg ((2 : ℝ) * c - d), sq_nonneg (d : ℝ)]
    rcases eq_or_lt_of_le h_nn with h0 | hlt
    · exfalso
      have h_zero : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 = 0 := by linarith
      have hd_le : (d : ℝ) ^ 2 ≤ 0 := by nlinarith [sq_nonneg ((2 : ℝ) * c - d)]
      have hd0 : (d : ℝ) = 0 := sq_eq_zero_iff.mp (le_antisymm hd_le (sq_nonneg _))
      have hc_le : (c : ℝ) ^ 2 ≤ 0 := by nlinarith
      have hc0 : (c : ℝ) = 0 := sq_eq_zero_iff.mp (le_antisymm hc_le (sq_nonneg _))
      have hc_int : c = 0 := by exact_mod_cast hc0
      have hd_int : d = 0 := by exact_mod_cast hd0
      have h_det : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * d -
                   (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c = 1 := sl2_det g
      simp [hc_int, hd_int] at h_det
    · exact hlt
  have h_lt_sqrt3 : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 < Real.sqrt 3 := by
    have h1 := mul_lt_mul_of_pos_right h_gt h_pos
    rw [div_mul_cancel₀ (Real.sqrt 3 / 2 : ℝ) (ne_of_gt h_pos)] at h1
    nlinarith
  have h_lt2 : (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 < 2 := by
    have h_sqrt3_lt : Real.sqrt 3 < 2 := by
      have h3 := Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num)
      nlinarith [Real.sqrt_nonneg 3, sq_nonneg (Real.sqrt 3 - 2)]
    linarith
  -- Integer: c²-cd+d² ≥ 1 and < 2 → = 1
  -- Use: 4(c²-cd+d²) = (2c-d)² + 3d²
  have h_ge : c ^ 2 - c * d + d ^ 2 ≥ 1 := by
    by_contra h; push_neg at h
    have h_le : c ^ 2 - c * d + d ^ 2 ≤ 0 := by omega
    have h_nn : 0 ≤ c ^ 2 - c * d + d ^ 2 := by
      nlinarith [sq_nonneg (2 * c - d), sq_nonneg d]
    have h_eq : c ^ 2 - c * d + d ^ 2 = 0 := le_antisymm h_le h_nn
    have hd_le : d ^ 2 ≤ 0 := by nlinarith [sq_nonneg (2 * c - d)]
    have hd0 : d = 0 := sq_eq_zero_iff.mp (le_antisymm hd_le (sq_nonneg d))
    rw [hd0] at h_eq; simp at h_eq
    -- h_eq : c = 0 (simp simplified c^2 = 0 to c = 0)
    have h_det : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * d -
                 (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * c = 1 := sl2_det g
    simp [h_eq, hd0] at h_det
  have h_eq : c ^ 2 - c * d + d ^ 2 = 1 := by
    have : c ^ 2 - c * d + d ^ 2 < 2 := by exact_mod_cast h_lt2
    omega
  show (c : ℝ) ^ 2 - (c : ℝ) * (d : ℝ) + (d : ℝ) ^ 2 = 1
  exact_mod_cast h_eq

/-- Helper: |re(g•ρ)| = 1/2 from ‖p‖ ≥ 1 and |re| ≤ 1/2. -/
private lemma abs_re_eq_half_of_smul_rho_in_fd (g : SL(2, ℤ))
    (h_fd : g • ellipticPoint_rho' ∈ 𝒟') (h_cd1 : ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 -
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) * ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) +
    ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 = 1) :
    |(g • ellipticPoint_rho').re| = 1/2 := by
  have h_re_bound := h_fd.1
  have h_norm_ge := h_fd.2
  have h_im_eq : (g • ellipticPoint_rho').im = Real.sqrt 3 / 2 := by
    have h_im := ModularGroup.im_smul_eq_div_normSq g ellipticPoint_rho'
    rw [ellipticPoint_rho'_im, normSq_denom_at_rho, h_cd1, div_one] at h_im
    exact h_im
  -- im² = 3/4, so re² + 3/4 ≥ 1, so re² ≥ 1/4, so |re| ≥ 1/2
  have h_im_sq : (g • ellipticPoint_rho').im ^ 2 = 3/4 := by
    rw [h_im_eq]; have := Real.mul_self_sqrt (show (3 : ℝ) ≥ 0 by norm_num); nlinarith
  have h_nsq : (g • ellipticPoint_rho').re ^ 2 + (g • ellipticPoint_rho').im ^ 2 ≥ 1 := by
    -- Bridge UpperHalfPlane.re/im to Complex.re/im via rfl
    have h_coe_im : (↑(g • ellipticPoint_rho') : ℂ).im = (g • ellipticPoint_rho').im := rfl
    have h_coe_re : (↑(g • ellipticPoint_rho') : ℂ).re = (g • ellipticPoint_rho').re := rfl
    have h_norm_sq := normSq_eq_norm_sq (↑(g • ellipticPoint_rho') : ℂ)
    rw [Complex.normSq_apply, h_coe_re, h_coe_im] at h_norm_sq
    -- h_norm_sq : re*re + im*im = ‖...‖²
    -- h_norm_ge : ‖...‖ ≥ 1, so ‖...‖² ≥ 1
    have h_sq : (g • ellipticPoint_rho').re * (g • ellipticPoint_rho').re +
        (g • ellipticPoint_rho').im * (g • ellipticPoint_rho').im ≥ 1 := by
      nlinarith [sq_nonneg (‖(↑(g • ellipticPoint_rho') : ℂ)‖ - 1)]
    nlinarith [sq_nonneg (g • ellipticPoint_rho').re, sq_nonneg (g • ellipticPoint_rho').im]
  have h_re_ge : (g • ellipticPoint_rho').re ^ 2 ≥ 1/4 := by nlinarith
  -- |re| ≥ 1/2 from re² ≥ 1/4
  have h_re_abs_ge : |(g • ellipticPoint_rho').re| ≥ 1/2 := by
    by_contra h_lt; push_neg at h_lt
    have h_nn := abs_nonneg (g • ellipticPoint_rho').re
    nlinarith [sq_abs (g • ellipticPoint_rho').re,
               mul_pos (show (0:ℝ) < 1/2 - |(g • ellipticPoint_rho').re| by linarith)
                        (show (0:ℝ) < 1/2 + |(g • ellipticPoint_rho').re| by linarith)]
  exact le_antisymm h_re_bound h_re_abs_ge

/-- In 𝒟', the only representatives of the orbit of `ρ` are `ρ` and `ρ+1`. -/
private theorem fd'_orbit_rho_eq (p : ℍ) (hp : p ∈ 𝒟') (horb : orb p = orho) :
    p = ellipticPoint_rho' ∨ p = ellipticPoint_rho_plus_one' := by
  -- Extract g with g • ρ = p from orbit equality
  have h_rel := Quotient.exact' horb
  obtain ⟨g, hg⟩ := (h_rel : ∃ g : SL(2, ℤ), g • ellipticPoint_rho' = p)
  -- p = g • ρ, and p ∈ 𝒟'
  rw [← hg] at hp ⊢
  -- Key facts about g
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc_def
  set d := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd_def
  set a := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha_def
  set b := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb_def
  -- c²-cd+d² = 1
  have h_cd1 := normSq_denom_eq_one_of_smul_rho_in_fd g hp
  -- im(g•ρ) = √3/2
  have h_im : (g • ellipticPoint_rho').im = Real.sqrt 3 / 2 := by
    have h_im_eq := ModularGroup.im_smul_eq_div_normSq g ellipticPoint_rho'
    rw [ellipticPoint_rho'_im, normSq_denom_at_rho, h_cd1, div_one] at h_im_eq
    exact h_im_eq
  -- |re(g•ρ)| = 1/2
  have h_re_abs := abs_re_eq_half_of_smul_rho_in_fd g hp h_cd1
  -- re(g•ρ) ∈ {-1/2, 1/2}, so either g•ρ = ρ or g•ρ = ρ+1
  have h_re_bound := hp.1
  have h_re_eq : (g • ellipticPoint_rho').re = -1/2 ∨ (g • ellipticPoint_rho').re = 1/2 := by
    rcases le_or_lt (g • ellipticPoint_rho').re 0 with h_neg | h_pos
    · left; linarith [abs_of_nonpos h_neg]
    · right; linarith [abs_of_pos h_pos]
  rcases h_re_eq with h_re_left | h_re_right
  · -- Case: re = -1/2
    left
    exact UpperHalfPlane.ext' (by linarith [h_re_left, ellipticPoint_rho'_re]) (by linarith [h_im, ellipticPoint_rho'_im])
  · -- Case: re = 1/2
    right
    exact UpperHalfPlane.ext' (by linarith [h_re_right, ellipticPoint_rho_plus_one'_re]) (by linarith [h_im, ellipticPoint_rho_plus_one'_im])

/-! ## Non-elliptic orbit property for RepCanon -/

/-- Points in `RepCanon` map to non-elliptic orbits. -/
private theorem orb_repCanon_nonEll (p : ℍ) (hp : p ∈ RepCanon f hf) :
    orb p ≠ oi ∧ orb p ≠ orho := by
  have ⟨hne_i, hne_rho, hne_rho1⟩ := repCanon_ne_elliptic f hf p hp
  have hp_fd := repCanon_mem_fd f hf hp
  exact ⟨fun h => hne_i (fd'_orbit_i_eq_i p hp_fd h),
         fun h => (fd'_orbit_rho_eq p hp_fd h).elim hne_rho hne_rho1⟩

/-! ## Helper lemmas for injectivity proof -/

/-- General formula for denom of SL₂(ℤ) element in terms of integer matrix entries. -/
private lemma denom_formula_general (h : SL(2, ℤ)) (p : ℍ) :
    UpperHalfPlane.denom h p =
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * ↑p +
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℂ) := by
  simp only [UpperHalfPlane.denom, Matrix.SpecialLinearGroup.toGL,
    Matrix.SpecialLinearGroup.map, RingHom.mapMatrix_apply]; rfl

/-- normSq of denom expanded in integer entries. -/
private lemma normSq_denom_expand_general (h : SL(2, ℤ)) (p : ℍ) :
    Complex.normSq (UpperHalfPlane.denom h p) =
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) ^ 2 * Complex.normSq (↑p) +
    2 * ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) *
      ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) * (↑p : ℂ).re +
    ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℝ) ^ 2 := by
  rw [denom_formula_general, Complex.normSq_apply]
  simp only [add_re, mul_re, add_im, mul_im,
    Complex.intCast_re, Complex.intCast_im, Complex.normSq_apply]
  ring

set_option maxHeartbeats 1600000 in
/-- If c² = 1 (bottom-left entry) and z ∈ 𝒟', then normSq(denom) ≥ 1. -/
private lemma normSq_denom_ge_one (h : SL(2, ℤ)) (z : ℍ) (hz : z ∈ 𝒟')
    (h_csq : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1) :
    Complex.normSq (UpperHalfPlane.denom h z) ≥ 1 := by
  set c_val := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d_val := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hre : |(z : ℂ).re| ≤ 1/2 := hz.1
  have hnsq : Complex.normSq (z : ℂ) ≥ 1 := by
    have hn : ‖(z : ℂ)‖ ≥ 1 := hz.2
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖(z : ℂ)‖ - 1)]
  rw [normSq_denom_expand_general]
  have h_csq_real : (↑c_val : ℝ) ^ 2 = 1 := by exact_mod_cast h_csq
  rw [h_csq_real, one_mul]
  suffices h_key : (↑d_val : ℝ) * (2 * (↑c_val : ℝ) * (↑z : ℂ).re + (↑d_val : ℝ)) ≥ 0 by
    nlinarith
  have h_c_abs : |(↑c_val : ℝ)| = 1 := by
    have h1 := sq_abs (↑c_val : ℝ); rw [h_csq_real] at h1
    nlinarith [abs_nonneg (↑c_val : ℝ), sq_nonneg (|(↑c_val : ℝ)| - 1)]
  have h_2cre_bound : |2 * (↑c_val : ℝ) * (↑z : ℂ).re| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0), h_c_abs]
    nlinarith [abs_nonneg (↑z : ℂ).re]
  rcases le_or_gt (d_val : ℤ) 0 with hd | hd
  · rcases eq_or_lt_of_le hd with hd0 | hd_neg
    · have : (↑d_val : ℝ) = 0 := by exact_mod_cast hd0
      rw [this]; simp
    · have hd_le : (↑d_val : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hd_neg
      have h1 : 2 * (↑c_val : ℝ) * (↑z : ℂ).re + (↑d_val : ℝ) ≤ 0 := by
        linarith [abs_le.mp h_2cre_bound]
      exact mul_nonneg_iff.mpr (Or.inr ⟨by linarith, h1⟩)
  · have hd_ge : (↑d_val : ℝ) ≥ 1 := by exact_mod_cast hd
    have h1 : 2 * (↑c_val : ℝ) * (↑z : ℂ).re + (↑d_val : ℝ) ≥ 0 := by
      linarith [abs_le.mp h_2cre_bound]
    exact mul_nonneg (by linarith) h1

/-- (g⁻¹)₁₀ squared equals (g₁₀) squared. -/
private lemma inv_c_sq_eq (g : SL(2, ℤ)) :
    ((g⁻¹ : SL(2, ℤ)).1 1 0) ^ 2 = ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 := by
  have : (g⁻¹ : SL(2, ℤ)).1 1 0 = -((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    show (↑g⁻¹ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = _
    rw [Matrix.SpecialLinearGroup.coe_inv g, Matrix.adjugate_fin_two]; simp
  rw [this]; ring

/-- If p ∈ RepCanon and ‖p‖ = 1, then re(p) < 0 (p must be in RepLeftArc). -/
private lemma repCanon_norm_one_re_neg (p : ℍ) (hp : p ∈ RepCanon f hf)
    (h_norm : ‖(p : ℂ)‖ = 1) : (p : ℂ).re < 0 := by
  simp only [RepCanon, Finset.mem_union] at hp
  rcases hp with (h | h) | h
  · exfalso; exact absurd h_norm (ne_of_gt (Finset.mem_filter.mp h).2.2.2.2.1)
  · exfalso
    simp only [RepLeftVert, S_leftVert, Finset.mem_filter] at h
    linarith [h.2.2]
  · exact (Finset.mem_filter.mp h).2.2.2

set_option maxHeartbeats 1600000 in
/-- If c² = 1 and z ∈ 𝒟' and normSq(denom) = 1, then normSq(z) = 1. -/
private lemma normSq_eq_one_of_denom_one (h : SL(2, ℤ)) (z : ℍ) (hz : z ∈ 𝒟')
    (h_csq : ((h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) ^ 2 = 1)
    (h_denom : Complex.normSq (UpperHalfPlane.denom h z) = 1) :
    Complex.normSq (z : ℂ) = 1 := by
  set c_val := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d_val := (h : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have hre : |(z : ℂ).re| ≤ 1/2 := hz.1
  have hnsq : Complex.normSq (z : ℂ) ≥ 1 := by
    have hn : ‖(z : ℂ)‖ ≥ 1 := hz.2
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [sq_nonneg (‖(z : ℂ)‖ - 1)]
  have h_expand := normSq_denom_expand_general h z
  have h_csq_real : (↑c_val : ℝ) ^ 2 = 1 := by exact_mod_cast h_csq
  rw [h_denom, h_csq_real, one_mul] at h_expand
  have h_c_abs : |(↑c_val : ℝ)| = 1 := by
    have h1 := sq_abs (↑c_val : ℝ); rw [h_csq_real] at h1
    nlinarith [abs_nonneg (↑c_val : ℝ), sq_nonneg (|(↑c_val : ℝ)| - 1)]
  have h_2cre_bound : |2 * (↑c_val : ℝ) * (↑z : ℂ).re| ≤ 1 := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (2:ℝ) > 0), h_c_abs]
    nlinarith [abs_nonneg (↑z : ℂ).re]
  have h_key : (↑d_val : ℝ) * (2 * (↑c_val : ℝ) * (↑z : ℂ).re + (↑d_val : ℝ)) ≥ 0 := by
    rcases le_or_gt (d_val : ℤ) 0 with hd | hd
    · rcases eq_or_lt_of_le hd with hd0 | hd_neg
      · have : (↑d_val : ℝ) = 0 := by exact_mod_cast hd0
        rw [this]; simp
      · have hd_le : (↑d_val : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hd_neg
        have h1 : 2 * (↑c_val : ℝ) * (↑z : ℂ).re + (↑d_val : ℝ) ≤ 0 := by
          linarith [abs_le.mp h_2cre_bound]
        exact mul_nonneg_iff.mpr (Or.inr ⟨by linarith, h1⟩)
    · have hd_ge : (↑d_val : ℝ) ≥ 1 := by exact_mod_cast hd
      have h1 : 2 * (↑c_val : ℝ) * (↑z : ℂ).re + (↑d_val : ℝ) ≥ 0 := by
        linarith [abs_le.mp h_2cre_bound]
      exact mul_nonneg (by linarith) h1
  nlinarith


/-! ## Injectivity of `orb` on RepCanon -/

set_option maxHeartbeats 3200000 in
/-- Injectivity of `orb` on canonical representatives. -/
private theorem orb_injOn_repCanon :
    Set.InjOn orb ↑(RepCanon f hf) := by
  intro p₁ hp₁ p₂ hp₂ h_eq
  simp only [orb] at h_eq
  obtain ⟨g, hg⟩ := Quotient.exact' h_eq
  -- hg : g • p₂ = p₁ (direction from MulAction.orbitRel)
  have hg' : g • p₂ = p₁ := hg
  have hp₁_fd := repCanon_mem_fd f hf hp₁
  have hp₂_fd := repCanon_mem_fd f hf hp₂
  set c := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  have hp₁_mathlib : p₁ ∈ 𝒟 := fd_eq_fundamentalDomain ▸ hp₁_fd
  have hp₂_mathlib : p₂ ∈ 𝒟 := fd_eq_fundamentalDomain ▸ hp₂_fd
  have h_3_p1 : 3 ≤ 4 * p₁.im ^ 2 :=
    ModularGroup.three_le_four_mul_im_sq_of_mem_fd hp₁_mathlib
  have h_3_p2 : 3 ≤ 4 * p₂.im ^ 2 :=
    ModularGroup.three_le_four_mul_im_sq_of_mem_fd hp₂_mathlib
  have h_p1_im_pos : (0 : ℝ) < p₁.im := p₁.im_pos
  have h_p2_im_pos : (0 : ℝ) < p₂.im := p₂.im_pos
  -- Key: normSq(denom g p₂) = p₂.im / p₁.im (from hg' : g • p₂ = p₁)
  have h_csq_le := p₂.c_mul_im_sq_le_normSq_denom g
  have h_p1_im_eq : p₁.im = p₂.im / Complex.normSq (UpperHalfPlane.denom g p₂) := by
    have := ModularGroup.im_smul_eq_div_normSq g p₂; rw [hg'] at this; exact this
  have h_nsq_eq : Complex.normSq (UpperHalfPlane.denom g p₂) = p₂.im / p₁.im := by
    rw [h_p1_im_eq]; field_simp
  -- |c| ≤ 1 from the c⁴ bound argument
  have h_abs_c_le : |c| ≤ 1 := by
    by_contra h_gt; push_neg at h_gt
    have h_c2 : c ^ 2 ≥ 4 := by nlinarith [sq_abs c]
    have h1 : (↑c : ℝ) ^ 2 * p₂.im ^ 2 ≤ p₂.im / p₁.im := by
      rw [← h_nsq_eq]; convert h_csq_le using 1
      have h_eq : (↑c : ℝ) = (↑(Matrix.SpecialLinearGroup.toGL
          ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) g)) :
          Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by simp [c]
      rw [h_eq]; ring
    have h2 : (↑c : ℝ) ^ 2 * p₂.im ^ 2 * p₁.im ≤ p₂.im := by
      have := mul_le_mul_of_nonneg_right h1 h_p1_im_pos.le
      rwa [div_mul_cancel₀ _ (ne_of_gt h_p1_im_pos)] at this
    have h3 : (↑c : ℝ) ^ 2 * p₂.im * p₁.im ≤ 1 := by
      have h_eq : (↑c : ℝ) ^ 2 * p₂.im * p₁.im =
          (↑c : ℝ) ^ 2 * p₂.im ^ 2 * p₁.im / p₂.im := by field_simp
      rw [h_eq]; exact (div_le_one h_p2_im_pos).mpr h2
    have h4 : (↑c : ℝ) ^ 4 * p₂.im ^ 2 * p₁.im ^ 2 ≤ 1 := by
      have h_nonneg : (0 : ℝ) ≤ (↑c : ℝ) ^ 2 * p₂.im * p₁.im := by positivity
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - (↑c : ℝ) ^ 2 * p₂.im * p₁.im by linarith)
                 h_nonneg]
    have h_c4 : (↑c : ℝ) ^ 4 ≥ 16 := by
      have : (↑c : ℝ) ^ 2 ≥ 4 := by exact_mod_cast h_c2
      nlinarith [sq_nonneg ((↑c : ℝ) ^ 2 - 4)]
    have h_im1 : (3 : ℝ) / 4 ≤ p₁.im ^ 2 := by linarith
    have h_im2 : (3 : ℝ) / 4 ≤ p₂.im ^ 2 := by linarith
    have h5 : (↑c : ℝ) ^ 4 * p₂.im ^ 2 ≥ 12 := by nlinarith
    nlinarith
  -- Case split: c = 0 (T-translation) or c ≠ 0 (direct equality via normSq)
  rcases eq_or_ne c 0 with h_c_zero | h_c_ne_zero
  · -- Case c = 0: p₁ = T^n • p₂ with n = 0
    obtain ⟨n, hn⟩ := ModularGroup.exists_eq_T_zpow_of_c_eq_zero h_c_zero
    have hTn : p₁ = ModularGroup.T ^ n • p₂ := by
      have h := hg'; rw [hn] at h; exact h.symm
    have h_re_shift : p₁.re = p₂.re + (n : ℝ) := by
      rw [hTn]; exact ModularGroup.re_T_zpow_smul p₂ n
    have h_re_p1_lt : p₁.re < 1/2 := by
      simp only [RepCanon, Finset.mem_union, Finset.mem_coe] at hp₁
      rcases hp₁ with (h | h) | h
      · exact lt_of_abs_lt (Finset.mem_filter.mp h).2.2.2.2.2
      · simp only [RepLeftVert, S_leftVert, Finset.mem_filter] at h
        have : p₁.re = (↑p₁ : ℂ).re := rfl; linarith [h.2.1]
      · have := (Finset.mem_filter.mp h).2.2.2
        have : p₁.re = (↑p₁ : ℂ).re := rfl; linarith
    have h_re_p2_lt : p₂.re < 1/2 := by
      simp only [RepCanon, Finset.mem_union, Finset.mem_coe] at hp₂
      rcases hp₂ with (h | h) | h
      · exact lt_of_abs_lt (Finset.mem_filter.mp h).2.2.2.2.2
      · simp only [RepLeftVert, S_leftVert, Finset.mem_filter] at h
        have : p₂.re = (↑p₂ : ℂ).re := rfl; linarith [h.2.1]
      · have := (Finset.mem_filter.mp h).2.2.2
        have : p₂.re = (↑p₂ : ℂ).re := rfl; linarith
    have h_re_p1_ge : p₁.re ≥ -1/2 := by
      have := hp₁_fd.1; linarith [abs_le.mp this]
    have h_re_p2_ge : p₂.re ≥ -1/2 := by
      have := hp₂_fd.1; linarith [abs_le.mp this]
    have h_n_zero : n = 0 := by
      have : (n : ℝ) < 1 := by linarith
      have : (-1 : ℝ) < n := by linarith
      have : n < 1 := by exact_mod_cast ‹(n : ℝ) < 1›
      have : -1 < n := by exact_mod_cast ‹(-1 : ℝ) < (n : ℝ)›
      omega
    rw [hTn, h_n_zero, zpow_zero, one_smul]
  · -- Case c ≠ 0: prove p₁ = p₂ via normSq argument
    have h_csq : c ^ 2 = 1 := by
      have h2 := Int.one_le_abs h_c_ne_zero
      have : |c| = 1 := le_antisymm h_abs_c_le h2
      nlinarith [sq_abs c]
    -- Forward: normSq(denom g p₂) ≥ 1, so p₂.im ≥ p₁.im
    have h_nsq_ge1 : Complex.normSq (UpperHalfPlane.denom g p₂) ≥ 1 :=
      normSq_denom_ge_one g p₂ hp₂_fd h_csq
    have h_ge_forward : p₁.im ≤ p₂.im := by
      have h := h_nsq_ge1; rw [h_nsq_eq] at h
      rwa [ge_iff_le, le_div_iff₀ h_p1_im_pos, one_mul] at h
    -- Reverse: use g⁻¹ to get p₂.im ≤ p₁.im
    have h_inv_smul : g⁻¹ • p₁ = p₂ := inv_smul_eq_iff.mpr hg'.symm
    -- Don't annotate types with denom g⁻¹ to avoid coercion mismatch
    have h_inv_ge := normSq_denom_ge_one g⁻¹ p₁ hp₁_fd ((inv_c_sq_eq g).trans h_csq)
    have h_inv_im := ModularGroup.im_smul_eq_div_normSq g⁻¹ p₁
    rw [h_inv_smul] at h_inv_im
    -- h_inv_im : p₂.im = p₁.im / <normSq_inv>, h_inv_ge : <normSq_inv> ≥ 1
    have h_ge_reverse : p₂.im ≤ p₁.im := by rw [h_inv_im]; exact div_le_self h_p1_im_pos.le h_inv_ge
    have h_im_equal : p₁.im = p₂.im := le_antisymm h_ge_forward h_ge_reverse
    -- normSq(denom g p₂) = 1
    have h_denom_one : Complex.normSq (UpperHalfPlane.denom g p₂) = 1 := by
      rw [h_nsq_eq, h_im_equal, div_self (ne_of_gt h_p2_im_pos)]
    -- normSq(denom g⁻¹ p₁) = 1
    have h_denom_inv_one := by
      have := h_inv_im; rw [h_im_equal] at this
      -- this : p₂.im = p₂.im / <normSq_inv>
      have h_ne : p₂.im ≠ 0 := ne_of_gt h_p2_im_pos
      field_simp at this; exact this
    -- normSq(p₁) = 1 and normSq(p₂) = 1
    have h_p2_nsq : Complex.normSq (p₂ : ℂ) = 1 :=
      normSq_eq_one_of_denom_one g p₂ hp₂_fd h_csq h_denom_one
    have h_p1_nsq : Complex.normSq (p₁ : ℂ) = 1 :=
      normSq_eq_one_of_denom_one g⁻¹ p₁ hp₁_fd ((inv_c_sq_eq g).trans h_csq) h_denom_inv_one
    -- ‖p₁‖ = 1 and ‖p₂‖ = 1
    have h_p1_norm : ‖(p₁ : ℂ)‖ = 1 := by
      have := Complex.normSq_eq_norm_sq (p₁ : ℂ)
      nlinarith [norm_nonneg (p₁ : ℂ), sq_nonneg (‖(p₁ : ℂ)‖ - 1)]
    have h_p2_norm : ‖(p₂ : ℂ)‖ = 1 := by
      have := Complex.normSq_eq_norm_sq (p₂ : ℂ)
      nlinarith [norm_nonneg (p₂ : ℂ), sq_nonneg (‖(p₂ : ℂ)‖ - 1)]
    -- Both in RepCanon with norm 1 → re < 0
    have h_re_p1_neg : (p₁ : ℂ).re < 0 := repCanon_norm_one_re_neg f hf p₁ hp₁ h_p1_norm
    have h_re_p2_neg : (p₂ : ℂ).re < 0 := repCanon_norm_one_re_neg f hf p₂ hp₂ h_p2_norm
    -- re(p₁)² = re(p₂)² from normSq = 1 and im equal
    have h_re_sq : (p₁ : ℂ).re ^ 2 = (p₂ : ℂ).re ^ 2 := by
      rw [Complex.normSq_apply] at h_p1_nsq h_p2_nsq
      rw [show (↑p₁ : ℂ).im = (↑p₂ : ℂ).im from h_im_equal] at h_p1_nsq
      nlinarith [sq_nonneg (p₁ : ℂ).re, sq_nonneg (p₂ : ℂ).re]
    -- Both re < 0, re² equal → re equal
    have h_re_eq : (p₁ : ℂ).re = (p₂ : ℂ).re := by
      nlinarith [sq_nonneg ((p₁ : ℂ).re - (p₂ : ℂ).re),
                 sq_nonneg ((p₁ : ℂ).re + (p₂ : ℂ).re)]
    exact UpperHalfPlane.ext' h_re_eq h_im_equal

/-! ## Bridge lemma: finsum = RepCanon sum -/

/-- The finsum over non-elliptic orbits equals the RepCanon sum. -/
theorem finsum_nonell_eq_repCanon_sum :
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    ∑ s ∈ RepCanon f hf, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  -- Step 1: Convert finsum to Finset.sum using finite support
  have h_fin := finite_support_ordOrbit_nonEll f hf
  set S := h_fin.toFinset with hS_def
  have h_supp : Function.support (ordOrbitQ f) ⊆ ↑S := by
    intro q hq
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    exact Int.cast_ne_zero.mp (Function.mem_support.mp hq)
  rw [finsum_eq_sum_of_support_subset _ h_supp]
  -- Step 2: Define the map RepCanon → NonEllOrbit
  set R := RepCanon f hf with hR_def
  set φ : (p : ℍ) → p ∈ R → NonEllOrbit :=
    fun p hp => ⟨orb p, orb_repCanon_nonEll f hf p hp⟩ with hφ_def
  -- Step 3: Image in S (φ p maps into S)
  have h_im : ∀ p (hp : p ∈ R), φ p hp ∈ S := by
    intro p hp
    rw [Set.Finite.mem_toFinset]
    show ordOrbit f (orb p) ≠ 0
    rw [ordOrbit_mk]
    have hp_S0 := repCanon_mem_S0 f hf hp
    rw [S0, Set.Finite.mem_toFinset] at hp_S0
    exact hp_S0.2
  -- Step 4: Injectivity
  have h_inj : ∀ p₁ (h₁ : p₁ ∈ R) p₂ (h₂ : p₂ ∈ R),
      φ p₁ h₁ = φ p₂ h₂ → p₁ = p₂ := by
    intro p₁ h₁ p₂ h₂ heq
    exact orb_injOn_repCanon f hf h₁ h₂ (congr_arg Subtype.val heq)
  -- Step 5: Surjectivity
  have h_surj : ∀ q ∈ S, ∃ p, ∃ hp : p ∈ R, φ p hp = q := by
    intro q hq
    have hq' : ordOrbit f q.val ≠ 0 := (Set.Finite.mem_toFinset _).mp hq
    obtain ⟨p, hp_mem, hp_orb⟩ := exists_repCanon_of_nonEllOrbit f hf q hq'
    exact ⟨p, hp_mem, Subtype.ext hp_orb⟩
  -- Step 6: Value equality
  have h_val : ∀ p (hp : p ∈ R),
      (orderOfVanishingAt' (⇑f) p : ℂ) = ordOrbitQ f (φ p hp) := by
    intro p hp
    simp only [ordOrbitQ, hφ_def]
    exact_mod_cast (ordOrbit_mk f p).symm
  -- Step 7: Apply Finset.sum_bij
  exact (Finset.sum_bij φ h_im h_inj h_surj h_val).symm

/-! ## RepCanon sum decomposition -/

/-- RepStrict is disjoint from RepLeftVert (|re| < 1/2 vs re = -1/2). -/
private lemma disjoint_repStrict_repLeftVert :
    Disjoint (RepStrict f hf) (RepLeftVert f hf) := by
  apply Finset.disjoint_left.mpr
  intro p hp_s hp_lv
  have hs := (Finset.mem_filter.mp hp_s).2
  have hlv := (Finset.mem_filter.mp hp_lv).2
  -- RepStrict: |(p:ℂ).re| < 1/2
  -- RepLeftVert = S_leftVert: (p:ℂ).re = -1/2
  have h1 : |(p : ℂ).re| < 1/2 := hs.2.2.2.2
  have h2 : (p : ℂ).re = -1/2 := hlv.1
  rw [h2] at h1; norm_num at h1

/-- (RepStrict ∪ RepLeftVert) is disjoint from RepLeftArc (‖p‖ > 1 vs ‖p‖ = 1). -/
private lemma disjoint_union_repLeftArc :
    Disjoint (RepStrict f hf ∪ RepLeftVert f hf) (RepLeftArc f hf) := by
  apply Finset.disjoint_left.mpr
  intro p hp_u hp_a
  have ha := (Finset.mem_filter.mp hp_a).2
  -- RepLeftArc: ‖(p:ℂ)‖ = 1
  have h_norm_eq : ‖(p : ℂ)‖ = 1 := ha.2.1
  -- Both RepStrict and RepLeftVert have ‖p‖ > 1
  simp only [Finset.mem_union] at hp_u
  rcases hp_u with hp_s | hp_lv
  · exact absurd h_norm_eq (ne_of_gt (Finset.mem_filter.mp hp_s).2.2.2.2.1)
  · exact absurd h_norm_eq (ne_of_gt (Finset.mem_filter.mp hp_lv).2.2)

/-- The RepCanon sum splits into three sub-sums. -/
private lemma repCanon_sum_split :
    ∑ s ∈ RepCanon f hf, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ RepStrict f hf, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ RepLeftVert f hf, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ RepLeftArc f hf, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  simp only [RepCanon]
  rw [Finset.sum_union (disjoint_union_repLeftArc f hf),
      Finset.sum_union (disjoint_repStrict_repLeftVert f hf)]

/-! ## Final Theorem -/

include hf in
/-- **Textbook Orbit-Finsum Valence Formula**.

For a nonzero modular form `f` of weight `k` for `SL₂(ℤ)`:
```
  ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + ∑ᶠ_{non-ell orbits} ordOrbit(f) = k/12
```
Only hypotheses are `f` (a modular form) and `hf : f ≠ 0`. -/
theorem valenceFormula_textbook_orbit_finsum :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 := by
  rw [finsum_nonell_eq_repCanon_sum f hf, repCanon_sum_split f hf]
  -- Now the three sums match valenceFormula_orbit_sum_S0 (up to associativity)
  unfold RepStrict RepLeftVert RepLeftArc
  linear_combination valenceFormula_orbit_sum_S0 f hf

end
