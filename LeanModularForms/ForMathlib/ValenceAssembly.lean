/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ValenceFormula
import LeanModularForms.ForMathlib.FDBoundary

/-!
# Valence Formula Assembly — Core Identity from FDWindingData

This file assembles the core identity for the valence formula from `FDWindingData`.
Given winding weight data for the fundamental domain boundary at height `H`, we prove
the orbit-sum identity that discharges the `h_core` hypothesis in `ValenceFormula.lean`.

## Strategy

Given `FDWindingData H` plus boundary winding = -1/2 for non-interior non-elliptic
on-curve points, we:

1. Split the sum over S into elliptic points + non-elliptic interior + boundary
2. Substitute the known winding weights at each point
3. Apply orbit pairing (T-invariance collapses left/right verticals,
   S-invariance collapses left/right arcs)
4. Combine with the ρ+1 → ρ order identity to get the 1/3 coefficient

## Main definitions

* `FDWindingDataFull` — extends `FDWindingData` with boundary winding for non-interior
  non-elliptic points

## Main results

* `valence_formula_core_of_windingDataFull` — the core identity conditional on
  `FDWindingDataFull` and a residue-modular hypothesis
* `valence_formula_textbook_of_windingDataFull` — the full textbook valence formula
  conditional on a `∀ H`-level residue-modular hypothesis
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Extended winding data -/

/-- Extended winding data that also covers non-interior non-elliptic boundary points.

In addition to everything in `FDWindingData`, this provides the winding number `-1/2`
at smooth boundary points: vertical edges (re = ±1/2, ‖z‖ > 1) and non-elliptic arc
points (‖z‖ = 1, |re| < 1/2, z ≠ i). These are points where the FD boundary passes
through smoothly, giving a crossing angle of π and hence winding number -1/2.

The primary consumer of this structure is `valence_formula_core_of_windingDataFull`. -/
structure FDWindingDataFull (H : ℝ) extends FDWindingData H where
  /-- Winding number = -1/2 at non-interior non-elliptic boundary points. -/
  boundary_winding : ∀ z : ℂ, z.im > 0 → z.im < H →
    z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
    ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
    1 ≤ Complex.normSq z → |z.re| ≤ 1/2 →
    HasGeneralizedWindingNumber boundary z (-1/2)

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Elliptic point auxiliary lemmas -/

omit f hf in
private lemma ellipticPointRho_re_neg : (ellipticPointRho' : ℂ).re < 0 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re < 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]
  norm_num

omit f hf in
private lemma ellipticPointRhoPlusOne_re_pos :
    (ellipticPointRhoPlusOne' : ℂ).re > 0 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re > 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]
  norm_num

omit f hf in
private lemma ellipticPoint_ne_iρ1 : ellipticPointI' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp only [ellipticPointI', ellipticPointRhoPlusOne'] at this; norm_num at this

omit f hf in
private lemma ellipticPoint_ne_ρρ1 : ellipticPointRho' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp only [ellipticPointRho', ellipticPointRhoPlusOne'] at this; norm_num at this

/-! ### Unit circle point classification -/

omit f hf in
private lemma unit_circle_re_neg_half_eq_rho (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = -1/2) : s = ellipticPointRho' := by
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) *
        ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  apply UpperHalfPlane.ext; apply Complex.ext <;>
    simp only [ellipticPointRho', UpperHalfPlane.coe_mk, add_re, add_im, neg_re, neg_im, one_re,
      one_im, div_ofNat_re, div_ofNat_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, sub_zero, add_zero, zero_add, zero_div, neg_zero] <;>
    linarith

omit f hf in
private lemma unit_circle_re_pos_half_eq_rho_plus_one (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = 1/2) :
    s = ellipticPointRhoPlusOne' := by
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re] at h_nsq
  have h_im : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h_prod : ((s : ℂ).im - Real.sqrt 3 / 2) *
        ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      nlinarith [Real.mul_self_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
    rcases mul_eq_zero.mp h_prod with h | h
    · linarith
    · exact absurd h (ne_of_gt (add_pos s.2 (by positivity)))
  apply UpperHalfPlane.ext; apply Complex.ext <;>
    simp only [ellipticPointRhoPlusOne', UpperHalfPlane.coe_mk, add_re, add_im, one_re, one_im,
      div_ofNat_re, div_ofNat_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
      mul_one, sub_zero, add_zero, zero_add, zero_div] <;>
    linarith

omit f hf in
private lemma unit_circle_re_zero_eq_i (s : ℍ)
    (hs_norm : ‖(s : ℂ)‖ = 1) (hs_re : (s : ℂ).re = 0) : s = ellipticPointI' := by
  have h_nsq : Complex.normSq (s : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, hs_norm, one_pow]
  rw [Complex.normSq_apply, hs_re, mul_zero, zero_add] at h_nsq
  have h_le : (s : ℂ).im ≤ 1 := by nlinarith [mul_self_nonneg ((s : ℂ).im - 1), h_nsq]
  have h_ge : 1 ≤ (s : ℂ).im := by
    nlinarith [mul_le_of_le_one_right s.2.le h_le, h_nsq]
  apply UpperHalfPlane.ext; apply Complex.ext
  · exact hs_re.trans Complex.I_re.symm
  · exact (le_antisymm h_le h_ge).trans Complex.I_im.symm

/-! ### Elliptic Finset sum decomposition -/

omit f hf in
private lemma elliptic_finset_sum_eq_three (S : Finset UpperHalfPlane)
    (g : UpperHalfPlane → ℂ) (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete_zero : ∀ p, p ∈ 𝒟 → p ∉ S → g p = 0) :
    let P := fun (p : UpperHalfPlane) =>
      p = ellipticPointI' ∨ p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne'
    ∑ s ∈ S.filter P, g s =
      g ellipticPointI' + g ellipticPointRho' + g ellipticPointRhoPlusOne' := by
  intro P
  have h_ell_sub : S.filter P ⊆
      ({ellipticPointI', ellipticPointRho',
        ellipticPointRhoPlusOne'} : Finset UpperHalfPlane) := by
    intro x hx; have := (Finset.mem_filter.mp hx).2
    simp only [Finset.mem_insert, Finset.mem_singleton]; exact this
  have h_zero_outside : ∀ x ∈
      ({ellipticPointI', ellipticPointRho',
        ellipticPointRhoPlusOne'} : Finset UpperHalfPlane),
      x ∉ S.filter P → g x = 0 := by
    intro x hx hx_not
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hx_not_S : x ∉ S :=
      fun hx_S => hx_not (Finset.mem_filter.mpr ⟨hx_S, hx⟩)
    have hx_fd : x ∈ 𝒟 := by
      rcases hx with rfl | rfl | rfl
      · exact ellipticPointI_mem_fd
      · exact ellipticPointRho_mem_fd
      · exact ellipticPointRhoPlusOne_mem_fd
    exact hS_complete_zero x hx_fd hx_not_S
  rw [Finset.sum_subset h_ell_sub h_zero_outside,
    Finset.sum_insert (show ellipticPointI' ∉ ({ellipticPointRho', ellipticPointRhoPlusOne'} :
        Finset ℍ) by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨ellipticPointI_ne_rho, ellipticPoint_ne_iρ1⟩),
    Finset.sum_insert (show ellipticPointRho' ∉ ({ellipticPointRhoPlusOne'} : Finset ℍ) by
      simp only [Finset.mem_singleton]
      exact ellipticPoint_ne_ρρ1), Finset.sum_singleton]
  ring

/-! ### Non-elliptic right-arc sum equals left-arc sum -/

private lemma rho_singleton_sum_eq (S : Finset UpperHalfPlane)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_ord : orderOfVanishingAt' (⇑f) ellipticPointRho' ≠ 0) :
    ∑ s ∈ (if ellipticPointRhoPlusOne' ∈ sRightArc S
        then {ellipticPointRhoPlusOne'} else ∅),
      (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ (if ellipticPointRho' ∈ sLeftArc S
        then {ellipticPointRho'} else ∅),
      (orderOfVanishingAt' (⇑f) s : ℂ) := by
  have hρ_in_LA : ellipticPointRho' ∈ sLeftArc S := by
    simp only [sLeftArc, Finset.mem_filter]
    exact ⟨hS_complete _ ellipticPointRho_mem_fd h_ord,
      ellipticPointRho_norm, ellipticPointRho_re_neg⟩
  have hρ1_in_RA : ellipticPointRhoPlusOne' ∈ sRightArc S := by
    simp only [sRightArc, Finset.mem_filter]
    exact ⟨hS_complete _ ellipticPointRhoPlusOne_mem_fd
      (by rwa [ord_rho_plus_one_eq_ord_rho_via_vAdd]),
      ellipticPointRhoPlusOne_norm, ellipticPointRhoPlusOne_re_pos⟩
  rw [if_pos hρ1_in_RA, if_pos hρ_in_LA, Finset.sum_singleton, Finset.sum_singleton]
  exact_mod_cast congr_arg (Int.cast (R := ℂ)) (ord_rho_plus_one_eq_ord_rho_via_vAdd f)

private theorem sum_nonEllArc_right_eq_left
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    let RA_ne := S.filter (fun p =>
      p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0)
    let LA_ne := S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
    ∑ p ∈ RA_ne, (orderOfVanishingAt' (⇑f) p : ℂ) =
    ∑ p ∈ LA_ne, (orderOfVanishingAt' (⇑f) p : ℂ) := by
  intro RA_ne LA_ne
  have h_ra_ne : RA_ne =
      (sRightArc S).filter (· ≠ ellipticPointRhoPlusOne') := by
    ext s; simp only [RA_ne, sRightArc, Finset.mem_filter]; tauto
  have h_la_ne : LA_ne =
      (sLeftArc S).filter (· ≠ ellipticPointRho') := by
    ext s; simp only [LA_ne, sLeftArc, Finset.mem_filter]; tauto
  rw [h_ra_ne, h_la_ne]
  set f_ord := fun s : ℍ => (orderOfVanishingAt' (⇑f) s : ℂ) with hf_ord_def
  have h_ra_split := Finset.sum_filter_add_sum_filter_not (sRightArc S)
    (· ≠ ellipticPointRhoPlusOne') f_ord
  have h_la_split := Finset.sum_filter_add_sum_filter_not (sLeftArc S)
    (· ≠ ellipticPointRho') f_ord
  suffices h_sing :
      ∑ p ∈ (sRightArc S).filter
          (fun x => ¬(x ≠ ellipticPointRhoPlusOne')), f_ord p =
      ∑ p ∈ (sLeftArc S).filter
          (fun x => ¬(x ≠ ellipticPointRho')), f_ord p by
    linear_combination
      sum_ord_rightArc_eq_sum_ord_leftArc f S hS hS_complete +
        h_ra_split - h_la_split - h_sing
  simp_rw [not_not]
  conv_lhs => rw [Finset.filter_eq' (sRightArc S) ellipticPointRhoPlusOne']
  conv_rhs => rw [Finset.filter_eq' (sLeftArc S) ellipticPointRho']
  by_cases h_ord : orderOfVanishingAt' (⇑f) ellipticPointRho' = 0
  · have hf1 : f_ord ellipticPointRho' = 0 := by simp only [hf_ord_def, h_ord, Int.cast_zero]
    have hf2 : f_ord ellipticPointRhoPlusOne' = 0 := by
      simp only [hf_ord_def, ord_rho_plus_one_eq_ord_rho_via_vAdd f ▸ h_ord, Int.cast_zero]
    split_ifs <;> simp only [Finset.sum_singleton, Finset.sum_empty, hf1, hf2]
  · simp only [hf_ord_def]; exact rho_singleton_sum_eq f S hS_complete h_ord

/-! ### Boundary point classification -/

omit f hf in
private theorem bdry_ne_mem_union (S : Finset UpperHalfPlane) (s : UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟) (hs_S : s ∈ S) (hsi : s ≠ ellipticPointI')
    (hsρ : s ≠ ellipticPointRho') (hsρ1 : s ≠ ellipticPointRhoPlusOne')
    (h_not_int : ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2)) :
    s ∈ sRightVert S ∨ s ∈ sLeftVert S ∨
    (s ∈ S ∧ s ≠ ellipticPointRhoPlusOne' ∧ ‖(s : ℂ)‖ = 1 ∧ (s : ℂ).re > 0) ∨
    (s ∈ S ∧ s ≠ ellipticPointRho' ∧ ‖(s : ℂ)‖ = 1 ∧ (s : ℂ).re < 0) := by
  have hs_fd := hS s hs_S
  have hnorm_ge : 1 ≤ ‖(s : ℂ)‖ := by
    rw [Complex.norm_def]; exact Real.sqrt_one ▸ Real.sqrt_le_sqrt hs_fd.1
  rcases eq_or_lt_of_le hnorm_ge with h_eq | h_gt
  · rcases lt_trichotomy (s : ℂ).re 0 with hre_neg | hre_zero | hre_pos
    · exact Or.inr (Or.inr (Or.inr ⟨hs_S, hsρ, h_eq.symm, hre_neg⟩))
    · exact absurd (unit_circle_re_zero_eq_i s h_eq.symm hre_zero) hsi
    · exact Or.inr (Or.inr (Or.inl ⟨hs_S, hsρ1, h_eq.symm, hre_pos⟩))
  · have h_abs_eq : |(s : ℂ).re| = 1/2 := by
      by_contra h_ne; exact h_not_int ⟨h_gt, lt_of_le_of_ne hs_fd.2 h_ne⟩
    rcases abs_cases (s : ℂ).re with ⟨_, h_sign⟩ | ⟨_, h_sign⟩
    · exact Or.inl (Finset.mem_filter.mpr ⟨hs_S, by linarith, h_gt⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hs_S, by linarith, h_gt⟩))

omit f hf in
private theorem bdry_ne_eq_union (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) :
    let S_NE := S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne')
    S_NE.filter (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)) =
    (sRightVert S) ∪ (sLeftVert S) ∪
    S.filter (fun p =>
      p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0) ∪
    S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0) := by
  intro S_NE
  have h_rho_norm := ellipticPointRho_norm
  have h_rho1_norm := ellipticPointRhoPlusOne_norm
  ext s; simp only [S_NE, sRightVert, sLeftVert, Finset.mem_union, Finset.mem_filter]
  constructor
  · intro ⟨⟨hs_S, hsi, hsρ, hsρ1⟩, h_not_int⟩
    have := bdry_ne_mem_union S s hS hs_S hsi hsρ hsρ1 h_not_int
    simp only [sRightVert, sLeftVert, Finset.mem_filter] at this; tauto
  · intro h
    rcases h with
      ((⟨hs, hre, hn⟩ | ⟨hs, hre, hn⟩) | ⟨hs, hne, hn_eq, hre⟩) |
        ⟨hs, hne, hn_eq, hre⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; norm_num [ellipticPointI'] at hre,
        fun h => by rw [h] at hn; linarith [h_rho_norm],
        fun h => by rw [h] at hn; linarith [h_rho1_norm]⟩,
        fun ⟨_, h⟩ => by have := (abs_lt.mp h).2; linarith⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; norm_num [ellipticPointI'] at hre,
        fun h => by rw [h] at hn; linarith [h_rho_norm],
        fun h => by rw [h] at hn; linarith [h_rho1_norm]⟩,
        fun ⟨_, h⟩ => by have := (abs_lt.mp h).1; linarith⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; simp [ellipticPointI'] at hre,
        fun h => by rw [h] at hre; linarith [ellipticPointRho_re_neg],
        hne⟩,
        fun ⟨h, _⟩ => by linarith⟩
    · exact ⟨⟨hs,
        fun h => by rw [h] at hre; simp [ellipticPointI'] at hre,
        hne,
        fun h => by rw [h] at hre; linarith [ellipticPointRhoPlusOne_re_pos]⟩,
        fun ⟨h, _⟩ => by linarith⟩

omit f hf in
private lemma bdry_four_disjoint (S : Finset UpperHalfPlane)
    (RA_ne LA_ne : Finset UpperHalfPlane)
    (hRA : RA_ne = S.filter (fun p =>
      p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0))
    (hLA : LA_ne = S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)) :
    Disjoint (sRightVert S ∪ sLeftVert S ∪ RA_ne) LA_ne := by
  subst hRA; subst hLA
  apply Finset.disjoint_union_left.mpr
  exact ⟨Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_filter.mpr
        fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith,
      Finset.disjoint_filter.mpr
        fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith⟩,
    Finset.disjoint_filter.mpr
      fun s _ ⟨_, _, hre1⟩ ⟨_, _, hre2⟩ => by linarith⟩

private theorem half_bdry_sum_eq_leftVert_plus_leftArc
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    let S_NE := S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne')
    let BDRY := S_NE.filter
      (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2))
    let LA_ne := S.filter (fun p =>
      p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
    (1/2 : ℂ) * ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
    ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) := by
  intro S_NE BDRY LA_ne
  set RA_ne := S.filter (fun p =>
    p ≠ ellipticPointRhoPlusOne' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re > 0) with hRA_ne_def
  have h_disj_RV_LV : Disjoint (sRightVert S) (sLeftVert S) :=
    Finset.disjoint_filter.mpr fun s _ ⟨hre1, _⟩ ⟨hre2, _⟩ => by linarith
  have h12 : Disjoint (sRightVert S ∪ sLeftVert S) RA_ne :=
    Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_filter.mpr fun s _ ⟨_, hn⟩ ⟨_, hn_eq, _⟩ => by linarith,
        Finset.disjoint_filter.mpr fun s _ ⟨hre, _⟩ ⟨_, _, hre2⟩ => by linarith⟩
  have h_sum_decomp :
      ∑ s ∈ BDRY, (orderOfVanishingAt' (⇑f) s : ℂ) =
      ∑ s ∈ sRightVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ RA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) +
      ∑ s ∈ LA_ne, (orderOfVanishingAt' (⇑f) s : ℂ) := by
    have h_bdry_decomp : BDRY =
        sRightVert S ∪ sLeftVert S ∪ RA_ne ∪ LA_ne := bdry_ne_eq_union S hS
    rw [h_bdry_decomp,
      Finset.sum_union (bdry_four_disjoint S RA_ne LA_ne hRA_ne_def rfl),
      Finset.sum_union h12, Finset.sum_union h_disj_RV_LV]
  rw [h_sum_decomp, sum_ord_rightVert_eq_sum_ord_leftVert f S hS hS_complete,
    sum_nonEllArc_right_eq_left f S hS hS_complete]; ring

/-! ### The core identity from FDWindingDataFull -/

/-- Substitute known winding values at elliptic points into the residue-modular identity.

Given that `g s = (-gWN(s)) * ord(f, s)` and the elliptic winding values
(-1/2 at i, -1/6 at rho and rho+1), this derives the formula with 1/2, 1/3 coefficients
and a non-elliptic remainder sum. The 1/3 arises from 1/6 + 1/6 after T-invariance
identifies `ord(f, rho+1) = ord(f, rho)`. -/
private theorem elliptic_winding_substitution
    {H : ℝ} (wd : FDWindingDataFull H)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_residue_modular :
      (orderAtCusp' f : ℂ) +
      ∑ s ∈ S, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne'),
      (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12 := by
  set g := fun (s : UpperHalfPlane) =>
    (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
      (orderOfVanishingAt' (⇑f) s : ℂ) with hg_def
  have h_ord_zero : ∀ p, p ∈ 𝒟 → p ∉ S → orderOfVanishingAt' (⇑f) p = 0 :=
    fun p hp hp_not => by_contra fun h_ne => hp_not (hS_complete _ hp h_ne)
  set P := fun (p : UpperHalfPlane) =>
    p = ellipticPointI' ∨ p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne'
  have h_ell_sum : ∑ s ∈ S.filter P, g s =
      g ellipticPointI' + g ellipticPointRho' + g ellipticPointRhoPlusOne' :=
    elliptic_finset_sum_eq_three S g hS (fun p hp hp_not => by
      simp only [hg_def, h_ord_zero p hp hp_not, Int.cast_zero, mul_zero])
  have hg_i : g ellipticPointI' =
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') := by
    show (-generalizedWindingNumber wd.boundary I) *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointI') = _; rw [wd.winding_at_i.eq]; ring
  have hg_ρ : g ellipticPointRho' =
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') := by
    show (-generalizedWindingNumber wd.boundary ellipticPointRho) *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') = _; rw [wd.winding_at_rho.eq]; ring
  have hg_ρ1 : g ellipticPointRhoPlusOne' =
      (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') := by
    show (-generalizedWindingNumber wd.boundary ellipticPointRhoPlusOne) *
      ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') = _
    rw [wd.winding_at_rho_plus_one.eq,
      show (orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne' : ℂ) =
        ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') from
        congr_arg _ (ord_rho_plus_one_eq_ord_rho_via_vAdd f)]; ring
  have h_filter_eq : S.filter (fun p => ¬P p) = S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne') := by
    ext x; simp only [P, Finset.mem_filter, not_or]
  have h_sum_eq : ∑ s ∈ S, g s =
      ∑ s ∈ S.filter P, g s + ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne'), g s := by
    rw [← h_filter_eq]; exact (Finset.sum_filter_add_sum_filter_not S P g).symm
  rw [h_sum_eq, h_ell_sum, hg_i, hg_ρ, hg_ρ1] at h_residue_modular
  linear_combination h_residue_modular

/-- Decompose the non-elliptic winding-weighted sum into interior + left-vertical + left-arc.

For interior points (‖z‖ > 1, |re| < 1/2), winding = -1, so the coefficient is 1.
For boundary points, winding = -1/2, so the coefficient is 1/2. We then use
`half_bdry_sum_eq_leftVert_plus_leftArc` to rewrite the half-boundary sum. -/
private theorem nonEll_gWN_sum_eq_int_plus_bdry
    {H : ℝ} (wd : FDWindingDataFull H)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hgw_int : ∀ s ∈ S, ‖(s : ℂ)‖ > 1 → |(s : ℂ).re| < 1/2 →
      generalizedWindingNumber wd.boundary (↑s) = -1)
    (hgw_bdry : ∀ s ∈ S, s ≠ ellipticPointI' → s ≠ ellipticPointRho' →
      s ≠ ellipticPointRhoPlusOne' → ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) →
      generalizedWindingNumber wd.boundary (↑s) = -1/2) :
    let S_NE := S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne')
    let INT := S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
      ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)
    ∑ s ∈ S_NE, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) =
      ∑ s ∈ INT, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
        ↑(orderOfVanishingAt' (⇑f) s) := by
  intro S_NE INT
  -- Substitute winding values: interior → 1, boundary → 1/2
  set g := fun (s : UpperHalfPlane) =>
    (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
      (orderOfVanishingAt' (⇑f) s : ℂ)
  have h_gWN_val : ∀ s ∈ S_NE, g s =
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s) := by
    intro s hs
    simp only [S_NE, Finset.mem_filter] at hs
    obtain ⟨hs_S, hsi, hsρ, hsρ1⟩ := hs
    split_ifs with h_int
    · simp only [g]; rw [hgw_int s hs_S h_int.1 h_int.2]; ring
    · simp only [g]; rw [hgw_bdry s hs_S hsi hsρ hsρ1 h_int]; ring
  rw [Finset.sum_congr rfl h_gWN_val]
  -- Split into interior (coefficient 1) and boundary (coefficient 1/2) parts
  set BDRY := S_NE.filter
    (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2))
  have h_ne_int : S_NE.filter
      (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) = INT := by
    ext s; simp only [S_NE, INT, Finset.mem_filter]; tauto
  have h_split := Finset.sum_filter_add_sum_filter_not S_NE
    (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) (fun s =>
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s))
  have h_int_sum :
      ∑ x ∈ S_NE.filter (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
      ∑ x ∈ INT, ↑(orderOfVanishingAt' (⇑f) x) := by
    rw [h_ne_int]; apply Finset.sum_congr rfl; intro s hs
    simp only [INT, Finset.mem_filter] at hs
    rw [if_pos ⟨hs.2.2.2.2.1, hs.2.2.2.2.2⟩, one_mul]
  have h_bdry_sum :
      ∑ x ∈ BDRY,
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
      (1/2 : ℂ) * ∑ x ∈ BDRY, (orderOfVanishingAt' (⇑f) x : ℂ) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs
    rw [if_neg (show ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) from
      (Finset.mem_filter.mp hs).2)]
  have h_bdry_identity := half_bdry_sum_eq_leftVert_plus_leftArc f S hS hS_complete
  linear_combination h_int_sum + h_bdry_sum + h_bdry_identity - h_split

omit f hf in
/-- Extract boundary winding = -1/2 from `FDWindingDataFull`, lifting from `ℂ` to `ℍ`. -/
private theorem boundary_winding_eq_neg_half
    {H : ℝ} (wd : FDWindingDataFull H)
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_below : ∀ s ∈ S, (s : ℂ).im < H) :
    ∀ s ∈ S, s ≠ ellipticPointI' → s ≠ ellipticPointRho' →
      s ≠ ellipticPointRhoPlusOne' → ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2) →
      generalizedWindingNumber wd.boundary (↑s) = -1/2 := by
  intro s hs hsi hsρ hsρ1 h_not_int
  have hs_fd := hS s hs
  exact (wd.boundary_winding (↑s) s.2 (hS_below s hs)
    (by intro h; exact hsi (UpperHalfPlane.ext h))
    (by intro h; exact hsρ (UpperHalfPlane.ext h))
    (by intro h; exact hsρ1 (UpperHalfPlane.ext h))
    h_not_int hs_fd.1 hs_fd.2).eq

set_option linter.unusedSectionVars false in
include hf in
/-- **Core identity** for the valence formula, conditional on `FDWindingDataFull`.

Given full winding weight data for the FD boundary at height `H`, plus the
residue-modular identity, we prove the explicit coefficient form of the valence formula
with coefficients 1/2 (at i), 1/3 (at rho), 1 (strict interior), and the canonical
left-vertical and left-arc sums.

The `h_residue_modular` hypothesis encodes: applying the generalized residue theorem to
logDeriv(f) along the FD boundary, and computing the modular side (horizontal segment
gives cusp order, verticals cancel by T-periodicity, arcs give -k/6 by S-identity). -/
theorem valence_formula_core_of_windingDataFull
    {H : ℝ} (wd : FDWindingDataFull H)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hS_below : ∀ s ∈ S, (s : ℂ).im < H)
    (h_residue_modular :
      (orderAtCusp' f : ℂ) +
      ∑ s ∈ S, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  have h_formula := elliptic_winding_substitution f wd S hS hS_complete h_residue_modular
  have h_eq := nonEll_gWN_sum_eq_int_plus_bdry f wd S hS hS_complete
    (fun s hs hn hr => (wd.interior_winding (↑s) hn hr s.2 (hS_below s hs)).eq)
    (boundary_winding_eq_neg_half wd S hS hS_below)
  rw [h_eq] at h_formula; linear_combination h_formula

/-! ### The full textbook valence formula -/

include hf in
/-- **The Valence Formula** for weight-`k` modular forms on `SL₂(ℤ)`, in textbook
orbit-sum form, conditional on `FDWindingDataFull` and a height-parametrized
residue-modular identity.

The `h_residue_modular_exists` hypothesis states that there exists a height `H` above
all zeros in 𝒟 such that the winding-weighted sum identity holds. This is the output
of applying the generalized residue theorem + modular invariance computation.

From this, we derive the standard form:

$$\operatorname{ord}_\infty(f) + \tfrac{1}{2}\operatorname{ord}_i(f)
  + \tfrac{1}{3}\operatorname{ord}_\rho(f)
  + \sum_{q\;\text{non-ell}} \operatorname{ord}_q(f) = \frac{k}{12}$$ -/
theorem valence_formula_textbook_of_windingDataFull
    (h_residue_modular_exists : ∃ (H : ℝ) (wd : FDWindingDataFull H),
      (∀ p : ℍ, p ∈ 𝒟 → (p : ℂ).im < H) ∧
      ∀ (S : Finset ℍ), (∀ p ∈ S, p ∈ 𝒟) →
        (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) →
        (orderAtCusp' f : ℂ) +
        ∑ s ∈ S, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 := by
  obtain ⟨H, wd, hH_above, h_rm⟩ := h_residue_modular_exists
  exact valence_formula_textbook_orbit_finsum f hf (fun S hS hS_complete =>
    valence_formula_core_of_windingDataFull f hf wd S hS hS_complete
      (fun s hs => hH_above s (hS s hs))
      (h_rm S hS hS_complete))

end
