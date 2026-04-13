/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ValenceFormula
import LeanModularForms.ForMathlib.FDBoundary
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# Core Identity Proof for the Valence Formula

This file proves the core identity underlying the valence formula for weight-`k`
modular forms on `SL₂(ℤ)`, using only ForMathlib imports.

## Architecture

The main theorem `valence_formula_orbit_sum_of_pvChain` takes a single
hypothesis `h_pvChain` which bundles:
1. An `FDWindingDataFull H` for some large `H`
2. The PV chain identity at that height

From this it derives the orbit-sum form of the valence formula by:
- Substituting explicit winding weights at elliptic points
- Using `gWN = -1` at strict interior points (from FDWindingData)
- Using `gWN = -1/2` at smooth boundary points (from FDWindingDataFull)
- Pairing right/left boundary subsets via T-translation and S-action

## Discharging the hypothesis

The `h_pvChain` hypothesis requires assembling:
1. `generalizedResidueTheorem_simplePoles_convex` applied to `logDeriv(f)`
2. The modular contour integral (T-cancel + S-arc + horizontal)
3. The uniqueness-of-limits argument and `2πi` cancellation
4. Construction of `FDWindingDataFull` (from InteriorContourIntegral +
   ArcFTCAtI + CornerFTCAtRho + BoundaryWinding)

Each ingredient exists in the ForMathlib chain. When their composition is
completed, `h_pvChain` can be discharged unconditionally.

## Main definitions

* `FDWindingDataFull` -- extends `FDWindingData` with smooth boundary winding

## Main results

* `explicit_coefficients_of_pvChain` -- weight substitution at elliptic points
* `valence_formula_orbit_sum_of_pvChain` -- the orbit-sum identity

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Serre, *A Course in Arithmetic*, Chapter VII
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Extended FDWindingData -/

/-- Full winding data for the FD boundary at height `H`.

Extends `FDWindingData` with the smooth boundary winding: at any non-elliptic
on-curve point, the generalized winding number is `-1/2`. This covers vertical
edges (`re = ±1/2`, `‖z‖ > 1`) and non-elliptic arc points (`‖z‖ = 1`,
`re ≠ ±1/2`).

Each case follows from `SmoothBoundaryWindingData` (BoundaryWinding.lean):
the boundary is locally a smooth curve through `z₀`, and the crossing angle
is `π`, yielding winding = `-(π·i) / (2π·i) = -1/2`. -/
structure FDWindingDataFull (H : ℝ) extends FDWindingData H where
  /-- Winding number = -1/2 at smooth non-elliptic boundary points. -/
  boundary_winding : ∀ z : ℂ, z.im > 0 → z.im < H →
    z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
    ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
    Complex.normSq z ≥ 1 → |z.re| ≤ 1/2 →
    HasGeneralizedWindingNumber toFDWindingData.boundary z (-1/2)

/-! ### Elliptic point geometric facts -/

omit f hf in
private lemma ellipticPointRho_re_neg : (ellipticPointRho' : ℂ).re < 0 := by
  change (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re < 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num

omit f hf in
private lemma ellipticPointRhoPlusOne_re_pos :
    (ellipticPointRhoPlusOne' : ℂ).re > 0 := by
  change (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re > 0
  simp only [add_re, mul_re, I_re, I_im, mul_zero, mul_one]; norm_num

omit f hf in
private lemma ellipticPoint_ne_iρ1 : ellipticPointI' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp [ellipticPointI', ellipticPointRhoPlusOne'] at this

omit f hf in
private lemma ellipticPoint_ne_ρρ1 : ellipticPointRho' ≠ ellipticPointRhoPlusOne' := by
  intro h; have := congr_arg (fun z : UpperHalfPlane => (z : ℂ).re) h
  simp [ellipticPointRho', ellipticPointRhoPlusOne'] at this; norm_num at this

/-! ### Elliptic point filter lemma -/

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
    Finset.sum_insert (by simp [ellipticPointI_ne_rho, ellipticPoint_ne_iρ1]),
    Finset.sum_insert (by simp [ellipticPoint_ne_ρρ1]), Finset.sum_singleton]
  ring

/-! ### Stage 2: Explicit coefficients -/

/-- Substitute explicit winding weights at the three elliptic points. -/
private theorem explicit_coefficients_of_pvChain
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (D : FDWindingDataFull H)
    (h_pv : ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) =
      -((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    (1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
        p ≠ ellipticPointRhoPlusOne'),
      (-generalizedWindingNumber D.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  set g := fun (s : UpperHalfPlane) =>
    generalizedWindingNumber D.boundary (↑s : ℂ) *
      (orderOfVanishingAt' (⇑f) s : ℂ) with hg_def
  have h_ord_zero : ∀ p, p ∈ 𝒟 → p ∉ S → orderOfVanishingAt' (⇑f) p = 0 :=
    fun p hp hp_not => by_contra fun h_ne => hp_not (hS_complete _ hp h_ne)
  set P := fun (p : UpperHalfPlane) =>
    p = ellipticPointI' ∨ p = ellipticPointRho' ∨ p = ellipticPointRhoPlusOne'
  have h_split := (Finset.sum_filter_add_sum_filter_not S P g).symm
  have h_ell_sum : ∑ s ∈ S.filter P, g s =
      g ellipticPointI' + g ellipticPointRho' + g ellipticPointRhoPlusOne' :=
    elliptic_finset_sum_eq_three S g hS (fun p hp hp_not => by
      simp [hg_def, h_ord_zero p hp hp_not, Int.cast_zero, mul_zero])
  have hg_i : g ellipticPointI' =
      (-1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') := by
    simp only [hg_def]
    have : (ellipticPointI' : ℂ) = I := rfl
    rw [this, D.toFDWindingData.winding_at_i.eq]
  have hg_ρ : g ellipticPointRho' =
      (-1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') := by
    simp only [hg_def]
    have : (ellipticPointRho' : ℂ) = ellipticPointRho := rfl
    rw [this, D.toFDWindingData.winding_at_rho.eq]
  have hg_ρ1 : g ellipticPointRhoPlusOne' =
      (-1/6 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRhoPlusOne') := by
    simp only [hg_def]
    have : (ellipticPointRhoPlusOne' : ℂ) = ellipticPointRhoPlusOne := rfl
    rw [this, D.toFDWindingData.winding_at_rho_plus_one.eq]
  have h_filter_eq : S.filter (fun p => ¬P p) = S.filter (fun p =>
      p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne') := by
    ext x; simp only [Finset.mem_filter, P, not_or]
  set R := ∑ s ∈ S.filter (fun p => ¬P p), g s with hR_def
  have h_neg_R :
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne'),
        (-generalizedWindingNumber D.boundary (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) = -R := by
    rw [hR_def, h_filter_eq]; simp only [neg_mul, Finset.sum_neg_distrib, hg_def]
  rw [h_neg_R]; rw [h_split, h_ell_sum, hg_i, hg_ρ, hg_ρ1] at h_pv
  linear_combination -h_pv

/-! ### Unit circle classification lemmas -/

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

/-! ### Boundary weight theorem -/

omit f hf in
/-- For non-elliptic non-interior points in `S ⊆ 𝒟`, the winding number is `-1/2`. -/
private theorem boundary_weight_at
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    {H : ℝ} (D : FDWindingDataFull H)
    (hH_above : ∀ s ∈ S, (s : ℂ).im < H)
    (s : UpperHalfPlane) (hs : s ∈ S)
    (hsi : s ≠ ellipticPointI') (hsρ : s ≠ ellipticPointRho')
    (hsρ1 : s ≠ ellipticPointRhoPlusOne')
    (h_not_int : ¬(‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2)) :
    generalizedWindingNumber D.boundary (↑s : ℂ) = -1/2 := by
  have hs_fd := hS s hs
  have habs_re := hs_fd.2
  have hnorm_ge : 1 ≤ ‖(s : ℂ)‖ := by
    rw [Complex.norm_def]; exact Real.sqrt_one ▸ Real.sqrt_le_sqrt hs_fd.1
  have h_im_lt_H : (s : ℂ).im < H := hH_above s hs
  have h_nsq_ge : Complex.normSq (s : ℂ) ≥ 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [hnorm_ge, sq_nonneg (‖(s : ℂ)‖ - 1)]
  exact (D.boundary_winding (↑s) s.2 h_im_lt_H
    (fun h => hsi (by ext; change (s : ℂ) = I; exact h))
    (fun h => hsρ (by ext; change (s : ℂ) = ellipticPointRho; exact h))
    (fun h => hsρ1 (by ext; change (s : ℂ) = ellipticPointRhoPlusOne; exact h))
    h_not_int h_nsq_ge habs_re).eq

/-! ### Rho singleton sum equality -/

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

/-- Non-elliptic right-arc ord sum equals non-elliptic left-arc ord sum. -/
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
  · have hf1 : f_ord ellipticPointRho' = 0 := by simp [hf_ord_def, h_ord]
    have hf2 : f_ord ellipticPointRhoPlusOne' = 0 := by
      simp [hf_ord_def, ord_rho_plus_one_eq_ord_rho_via_vAdd f ▸ h_ord]
    split_ifs <;> simp [Finset.sum_singleton, Finset.sum_empty, hf1, hf2]
  · simp only [hf_ord_def]; exact rho_singleton_sum_eq f S hS_complete h_ord

/-! ### Boundary decomposition lemmas -/

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
      ((⟨hs, hre, hn⟩ | ⟨hs, hre, hn⟩) |
        ⟨hs, hne, hn_eq, hre⟩) |
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

/-- Half the boundary-sum equals left-vert plus left-arc. -/
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

/-! ### The Main Theorem -/

/-- **Orbit-sum valence formula**, conditional on the PV chain identity.

The hypothesis `h_pvChain` bundles:
- `FDWindingDataFull H` for some large `H` (with all winding numbers)
- The PV chain identity: the winding-weighted sum equals `-(k/12 - ord_∞)`

This is dischargeable from ForMathlib ingredients:
1. `FDWindingDataFull` from InteriorContourIntegral + CrossingAtI/Rho + BoundaryWinding
2. The PV chain identity from GeneralizedResidueTheorem + ModularContourIntegral

Given this, the proof substitutes explicit weights and pairs orbits to obtain
the textbook orbit-sum form matching `valence_formula_textbook_orbit_finsum`
in `ForMathlib/ValenceFormula.lean`. -/
theorem valence_formula_orbit_sum_of_pvChain
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_pvChain : ∃ H : ℝ, ∃ D : FDWindingDataFull H,
      (∀ s ∈ S, (s : ℂ).im < H) ∧
      ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) =
      -((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :
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
  obtain ⟨H, D, hH_above, h_pv⟩ := h_pvChain
  have h_explicit := explicit_coefficients_of_pvChain f S hS hS_complete D h_pv
  rw [ord_rho_plus_one_eq_ord_rho_via_vAdd f] at h_explicit
  -- h_explicit gives the formula with -gWN * ord for non-elliptic points.
  -- We need to substitute: gWN = -1 for interior, gWN = -1/2 for boundary.
  have h_formula : (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
      (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne'),
        (-generalizedWindingNumber D.boundary (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 := by linear_combination h_explicit
  set S_NE := S.filter (fun p =>
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧
    p ≠ ellipticPointRhoPlusOne') with hS_NE_def
  set INT := S.filter (fun p =>
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
    ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)
  suffices h_eq :
      ∑ s ∈ S_NE,
        (-generalizedWindingNumber D.boundary (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      ∑ s ∈ INT, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
      ∑ s ∈ S.filter (fun p =>
          p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
        ↑(orderOfVanishingAt' (⇑f) s) by
    rw [h_eq] at h_formula; linear_combination h_formula
  -- Compute gWN for each non-elliptic point
  have h_gWN_val : ∀ s ∈ S_NE,
      (-generalizedWindingNumber D.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) =
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1 : ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s) := by
    intro s hs
    simp only [hS_NE_def, Finset.mem_filter] at hs
    obtain ⟨hs_S, hsi, hsρ, hsρ1⟩ := hs
    split_ifs with h_int
    · obtain ⟨hnorm, hre⟩ := h_int
      rw [(D.toFDWindingData.interior_winding (↑s) hnorm hre s.2
        (hH_above s hs_S)).eq]; ring
    · rw [boundary_weight_at S hS D hH_above s hs_S hsi hsρ hsρ1 h_int]; ring
  rw [Finset.sum_congr rfl h_gWN_val]
  set LA_ne := S.filter (fun p =>
    p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
  set BDRY := S_NE.filter
    (fun (p : ℍ) => ¬(‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2))
  have h_ne_int : S_NE.filter
      (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) = INT := by
    ext s; simp only [hS_NE_def, INT, Finset.mem_filter]; tauto
  have h_bdry_identity := half_bdry_sum_eq_leftVert_plus_leftArc f S hS hS_complete
  have h_split := Finset.sum_filter_add_sum_filter_not S_NE
    (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2) (fun s =>
      (if ‖(s : ℂ)‖ > 1 ∧ |(s : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
        ↑(orderOfVanishingAt' (⇑f) s))
  have h_int_sum :
      ∑ x ∈ S_NE.filter (fun (p : ℍ) => ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
        (if ‖(x : ℂ)‖ > 1 ∧ |(x : ℂ).re| < 1/2 then (1:ℂ) else 1/2) *
          ↑(orderOfVanishingAt' (⇑f) x) =
      ∑ x ∈ INT, ↑(orderOfVanishingAt' (⇑f) x) := by
    rw [h_ne_int]; apply Finset.sum_congr rfl
    intro s hs
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
  linear_combination h_int_sum + h_bdry_sum + h_bdry_identity - h_split

end
