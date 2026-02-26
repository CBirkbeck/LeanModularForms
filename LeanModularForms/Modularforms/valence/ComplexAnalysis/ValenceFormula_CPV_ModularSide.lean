/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_PV
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ModularSide_Param

/-!
# CPV Modular Side — Generalized PV Modular-Side Theorems

This file provides the **generalized principal value** (CPV) versions of the modular-side
identity, removing the `IntervalIntegrable` (`hint_H`) and full boundary nonvanishing
(`h_nv`) hypotheses.

## Problem

The standard modular-side theorem `pv_integral_eq_modular_transformation_H` requires
`IntervalIntegrable`, which FAILS when `f` vanishes at elliptic points on the FD boundary
arc (like E₄ at ρ or E₆ at i). The logDeriv has non-integrable poles there.

## Solution

Use `cauchyPrincipalValueOn S₀ (logDeriv g) (fdBoundary_H H) 0 5` with
`S₀ = {i, ρ', ρ}`. The ε-truncation properly regularizes the poles, and the
S-symmetry argument works for each fixed ε:
- Vertical pair cancel by T-invariance (exact for each ε)
- Arc: 2·I_arc(ε) = -k·(πi/6)·m(ε) where m(ε) → 2
- Seg5: no truncation needed for large H

## Main Results

* `fdBoundaryArcSingularSet` — The singular set {i, ρ', ρ}
* `S_action_ellipticPoint_i` — S(i) = i
* `S_action_rho_plus_one` — S(ρ') = ρ
* `S_action_rho` — S(ρ) = ρ'
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ## Singular Set -/

/-- Singular set for CPV on the FD boundary: the three elliptic/corner points {i, ρ', ρ}. -/
def fdBoundaryArcSingularSet : Finset ℂ :=
  {ellipticPoint_i, ellipticPoint_rho_plus_one, ellipticPoint_rho}

/-! ## S-Action on Singular Points

The modular S-transformation z ↦ -1/z maps {i, ρ', ρ} to itself:
- S(i) = -1/i = i
- S(ρ') = -1/ρ' = ρ  (since |ρ'| = 1)
- S(ρ) = -1/ρ = ρ'   (since |ρ| = 1) -/

/-- S(i) = i: the imaginary unit is a fixed point of z ↦ -1/z. -/
lemma S_action_ellipticPoint_i : -(1:ℂ) / ellipticPoint_i = ellipticPoint_i := by
  show -(1:ℂ) / I = I
  rw [neg_div, one_div, Complex.inv_I, neg_neg]

/-- normSq of ρ' = 1/2 + √3/2 · i equals 1 (since |ρ'| = 1). -/
private lemma normSq_ellipticPoint_rho_plus_one :
    Complex.normSq ellipticPoint_rho_plus_one = 1 := by
  show Complex.normSq (1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (1/2 : ℝ)^2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

/-- normSq of ρ = -1/2 + √3/2 · i equals 1 (since |ρ| = 1). -/
private lemma normSq_ellipticPoint_rho :
    Complex.normSq ellipticPoint_rho = 1 := by
  show Complex.normSq (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) = 1
  have h1 : (-1/2 + (Real.sqrt 3 / 2) * I : ℂ) =
      ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [h1, Complex.normSq_add_mul_I]
  have h2 : (-1/2 : ℝ)^2 = 1/4 := by ring
  have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
  rw [h2, h3]; ring

/-- ρ' is nonzero. -/
private lemma ellipticPoint_rho_plus_one_ne_zero : ellipticPoint_rho_plus_one ≠ 0 := by
  intro h
  have := normSq_ellipticPoint_rho_plus_one
  rw [h, map_zero] at this
  norm_num at this

/-- ρ is nonzero. -/
private lemma ellipticPoint_rho_ne_zero : ellipticPoint_rho ≠ 0 := by
  intro h
  have := normSq_ellipticPoint_rho
  rw [h, map_zero] at this
  norm_num at this

/-- S(ρ') = ρ: the S-transformation maps ρ' = 1/2 + √3/2·i to ρ = -1/2 + √3/2·i. -/
lemma S_action_rho_plus_one :
    -(1:ℂ) / ellipticPoint_rho_plus_one = ellipticPoint_rho := by
  show -(1:ℂ) / (1/2 + (Real.sqrt 3 / 2) * I) = -1/2 + (Real.sqrt 3 / 2) * I
  rw [show -(1:ℂ) / (1/2 + (Real.sqrt 3 / 2) * I) =
    -(1/2 + (Real.sqrt 3 / 2) * I)⁻¹ from by field_simp]
  rw [Complex.inv_def]
  have h_ns : Complex.normSq (1/2 + (↑(Real.sqrt 3) / 2) * I) = 1 := by
    have h1 : (1/2 + (↑(Real.sqrt 3) / 2) * I : ℂ) =
        ((1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
    rw [h1, Complex.normSq_add_mul_I]
    have h2 : (1/2 : ℝ)^2 = 1/4 := by ring
    have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
    rw [h2, h3]; ring
  simp only [h_ns, inv_one, Complex.ofReal_one, mul_one]
  apply Complex.ext
  · simp only [neg_re, Complex.conj_re, add_re, ofReal_re, ofReal_im, mul_re, I_re, mul_zero,
      I_im, mul_one, one_re, div_ofNat]
    ring
  · simp only [neg_im, Complex.conj_im, add_im, ofReal_im, ofReal_re, mul_im, I_re, mul_zero,
      I_im, mul_one, one_im, div_ofNat]
    ring

/-- S(ρ) = ρ': the S-transformation maps ρ = -1/2 + √3/2·i to ρ' = 1/2 + √3/2·i. -/
lemma S_action_rho :
    -(1:ℂ) / ellipticPoint_rho = ellipticPoint_rho_plus_one := by
  show -(1:ℂ) / (-1/2 + (Real.sqrt 3 / 2) * I) = 1/2 + (Real.sqrt 3 / 2) * I
  rw [show -(1:ℂ) / (-1/2 + (Real.sqrt 3 / 2) * I) =
    -(-1/2 + (Real.sqrt 3 / 2) * I)⁻¹ from by field_simp]
  rw [Complex.inv_def]
  have h_ns : Complex.normSq (-1/2 + (↑(Real.sqrt 3) / 2) * I) = 1 := by
    have h1 : (-1/2 + (↑(Real.sqrt 3) / 2) * I : ℂ) =
        ((-1/2 : ℝ) : ℂ) + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * I := by push_cast; ring
    rw [h1, Complex.normSq_add_mul_I]
    have h2 : (-1/2 : ℝ)^2 = 1/4 := by ring
    have h3 : (Real.sqrt 3 / 2)^2 = 3/4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0)]; norm_num
    rw [h2, h3]; ring
  simp only [h_ns, inv_one, Complex.ofReal_one, mul_one]
  apply Complex.ext
  · simp only [neg_re, Complex.conj_re, add_re, ofReal_re, ofReal_im, mul_re, I_re, mul_zero,
      I_im, mul_one, one_re, div_ofNat]
    ring
  · simp only [neg_im, Complex.conj_im, add_im, ofReal_im, ofReal_re, mul_im, I_re, mul_zero,
      I_im, mul_one, one_im, div_ofNat]
    ring

/-- S maps the singular set to itself: for any s ∈ {i, ρ', ρ}, -1/s ∈ {i, ρ', ρ}. -/
lemma S_maps_singularSet_to_self (s : ℂ) (hs : s ∈ fdBoundaryArcSingularSet) :
    -(1:ℂ) / s ∈ fdBoundaryArcSingularSet := by
  simp only [fdBoundaryArcSingularSet, Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with rfl | rfl | rfl
  · left; exact S_action_ellipticPoint_i
  · right; right; exact S_action_rho_plus_one
  · right; left; exact S_action_rho

/-! ## Imaginary Parts of Singular Points

All points in S₀ have imaginary part ≤ 1. This means seg5 at height H > 1
is far from S₀. -/

/-- All points in the singular set have imaginary part ≤ 1. -/
lemma singularSet_im_le_one (s : ℂ) (hs : s ∈ fdBoundaryArcSingularSet) :
    s.im ≤ 1 := by
  simp only [fdBoundaryArcSingularSet, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · -- s = i: im = 1
    show (I : ℂ).im ≤ 1; simp [Complex.I_im]
  · -- s = ρ': im = √3/2 ≤ 1
    show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).im ≤ 1
    simp only [add_im, one_im, div_ofNat, ofReal_im, ofReal_re, mul_im, I_re, mul_zero, I_im,
      mul_one]
    have : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
    linarith
  · -- s = ρ: im = √3/2 ≤ 1
    show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).im ≤ 1
    simp only [add_im, neg_im, one_im, div_ofNat, ofReal_im, ofReal_re, mul_im, I_re, mul_zero,
      I_im, mul_one]
    have : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
    linarith

/-! ## Seg5 Distance from S₀

The seg5 horizontal segment at height H is at distance ≥ H - 1 from any point
in S₀. So for ε < H - 1, the CPV truncation doesn't affect seg5. -/

/-- seg5_H has constant imaginary part H. -/
lemma fdBoundary_seg5_H_im (H : ℝ) (t : ℝ) :
    (fdBoundary_seg5_H H t).im = H := by
  simp [fdBoundary_seg5_H, add_im, ofReal_im, mul_im, I_re, mul_zero, I_im, mul_one, zero_add]

/-- For any s ∈ S₀ and H > 1, seg5_H(t) is far from s: ‖seg5_H(t) - s‖ ≥ H - 1. -/
lemma seg5_far_from_singularSet (H : ℝ) (hH : 1 < H) (t : ℝ)
    (s : ℂ) (hs : s ∈ fdBoundaryArcSingularSet) :
    H - 1 ≤ ‖fdBoundary_seg5_H H t - s‖ := by
  have h_im : (fdBoundary_seg5_H H t - s).im = H - s.im := by
    simp [sub_im, fdBoundary_seg5_H_im]
  have h_im_bound : s.im ≤ 1 := singularSet_im_le_one s hs
  calc H - 1 ≤ H - s.im := by linarith
    _ = |H - s.im| := by rw [abs_of_nonneg]; linarith
    _ = |(fdBoundary_seg5_H H t - s).im| := by rw [h_im]
    _ ≤ ‖fdBoundary_seg5_H H t - s‖ := abs_im_le_norm _

/-- For ε < H - 1, the CPV truncation does not affect seg5. -/
lemma cpv_truncation_trivial_seg5 (H : ℝ) (hH : 1 < H) (ε : ℝ) (hε_small : ε < H - 1)
    (t : ℝ) :
    cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet) (logDeriv (modularFormCompOfComplex f))
      (fdBoundary_seg5_H H) ε t =
    logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) * deriv (fdBoundary_seg5_H H) t := by
  apply cauchyPrincipalValueIntegrandOn_eq_of_far
  intro s hs
  have := seg5_far_from_singularSet H hH t s hs
  linarith

/-! ## Vertical Indicator Symmetry

The T-shift seg4_H(4-t) = seg1_H(t) - 1 induces a bijection on S₀:
  ‖seg1_H(t) - i‖ = ‖seg4_H(4-t) - i‖
  ‖seg1_H(t) - ρ'‖ = ‖seg4_H(4-t) - ρ‖
  ‖seg1_H(t) - ρ‖ = ‖seg4_H(4-t) - ρ'‖
This means the CPV indicator is symmetric under the T-shift. -/

/-- At height H, seg4(4-s) = seg1(s) - 1 for s ∈ [0,1]. (Re-proved here as the
    original in PV.lean is private.) -/
private lemma seg4_eq_seg1_minus_one_H' (H : ℝ) (s : ℝ) (_hs : s ∈ Icc 0 1) :
    fdBoundary_seg4_H H (4 - s) = fdBoundary_seg1_H H s - 1 := by
  simp only [fdBoundary_seg4_H, fdBoundary_seg1_H]
  have h1 : ((4 - s : ℝ) : ℂ) - 3 = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  simp only [h1]; push_cast; ring

/-- ‖↑a + ↑b * I‖ = ‖↑(-a) + ↑b * I‖: negating the real part preserves the norm. -/
private lemma norm_ofReal_add_mul_I_neg (a b : ℝ) :
    ‖(↑a + ↑b * I : ℂ)‖ = ‖(↑(-a) + ↑b * I : ℂ)‖ := by
  simp only [Complex.norm_def]
  congr 1
  rw [Complex.normSq_add_mul_I, Complex.normSq_add_mul_I]
  ring

/-- ρ' - 1 = ρ (since ρ' = 1/2 + √3/2·i and ρ = -1/2 + √3/2·i). -/
private lemma rho_plus_one_sub_one :
    (ellipticPoint_rho_plus_one : ℂ) - 1 = ellipticPoint_rho := by
  show (1/2 + (Real.sqrt 3 / 2) * I : ℂ) - 1 = -1/2 + (Real.sqrt 3 / 2) * I
  ring

/-- The CPV indicator is symmetric under the vertical T-shift:
    for each s ∈ S₀, there exists s' ∈ S₀ with ‖seg1_H(t) - s‖ = ‖seg4_H(4-t) - s'‖. -/
lemma vertical_indicator_symmetric (H : ℝ) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_seg1_H H t - s‖ ≤ ε) ↔
    (∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_seg4_H H (4 - t) - s‖ ≤ ε) := by
  have h_seg : fdBoundary_seg4_H H (4 - t) = fdBoundary_seg1_H H t - 1 :=
    seg4_eq_seg1_minus_one_H' H t ht
  -- Exact equality: z - ρ' = (z-1) - ρ (since ρ' - 1 = ρ)
  have h_eq_rho' : fdBoundary_seg1_H H t - ellipticPoint_rho_plus_one =
      (fdBoundary_seg1_H H t - 1) - ellipticPoint_rho := by
    rw [← rho_plus_one_sub_one]; ring
  -- Norm equality for i: ‖z - i‖ = ‖(z-1) - i‖ (since (1/2)² = (-1/2)²)
  have h_norm_i : ‖fdBoundary_seg1_H H t - ellipticPoint_i‖ =
      ‖(fdBoundary_seg1_H H t - 1) - ellipticPoint_i‖ := by
    have h1 : (fdBoundary_seg1_H H t - ellipticPoint_i : ℂ) =
        ↑(1/2 : ℝ) + ↑(H - (H - Real.sqrt 3 / 2) * t - 1 : ℝ) * I := by
      show fdBoundary_seg1_H H t - I = _
      simp [fdBoundary_seg1_H]; ring
    have h2 : ((fdBoundary_seg1_H H t - 1) - ellipticPoint_i : ℂ) =
        ↑(-(1/2) : ℝ) + ↑(H - (H - Real.sqrt 3 / 2) * t - 1 : ℝ) * I := by
      show fdBoundary_seg1_H H t - 1 - I = _
      simp [fdBoundary_seg1_H]; ring
    rw [h1, h2]; exact norm_ofReal_add_mul_I_neg _ _
  -- Norm equality for ρ: ‖z - ρ‖ = ‖(z-1) - ρ'‖ (since 1² = (-1)²)
  have h_norm_rho : ‖fdBoundary_seg1_H H t - ellipticPoint_rho‖ =
      ‖(fdBoundary_seg1_H H t - 1) - ellipticPoint_rho_plus_one‖ := by
    have h1 : (fdBoundary_seg1_H H t - ellipticPoint_rho : ℂ) =
        ↑(1 : ℝ) + ↑(H - (H - Real.sqrt 3 / 2) * t - Real.sqrt 3 / 2 : ℝ) * I := by
      show fdBoundary_seg1_H H t - (-1/2 + (Real.sqrt 3 / 2) * I) = _
      simp [fdBoundary_seg1_H]; ring
    have h2 : ((fdBoundary_seg1_H H t - 1) - ellipticPoint_rho_plus_one : ℂ) =
        ↑(-(1) : ℝ) + ↑(H - (H - Real.sqrt 3 / 2) * t - Real.sqrt 3 / 2 : ℝ) * I := by
      show fdBoundary_seg1_H H t - 1 - (1/2 + (Real.sqrt 3 / 2) * I) = _
      simp [fdBoundary_seg1_H]; ring
    rw [h1, h2]; exact norm_ofReal_add_mul_I_neg _ _
  -- The iff follows by case analysis with the norm equalities
  rw [h_seg]
  constructor
  · rintro ⟨s, hs, h_le⟩
    simp only [fdBoundaryArcSingularSet, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · -- i → i
      refine ⟨ellipticPoint_i, ?_, ?_⟩
      · simp [fdBoundaryArcSingularSet]
      · rwa [← h_norm_i]
    · -- ρ' → ρ
      refine ⟨ellipticPoint_rho, ?_, ?_⟩
      · simp [fdBoundaryArcSingularSet]
      · rw [← h_eq_rho']; exact h_le
    · -- ρ → ρ'
      refine ⟨ellipticPoint_rho_plus_one, ?_, ?_⟩
      · simp [fdBoundaryArcSingularSet]
      · rwa [← h_norm_rho]
  · rintro ⟨s, hs, h_le⟩
    simp only [fdBoundaryArcSingularSet, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · -- i → i
      refine ⟨ellipticPoint_i, ?_, ?_⟩
      · simp [fdBoundaryArcSingularSet]
      · rwa [h_norm_i]
    · -- ρ' → ρ (have ‖(z-1) - ρ'‖ ≤ ε, need ‖z - ρ‖ ≤ ε)
      refine ⟨ellipticPoint_rho, ?_, ?_⟩
      · simp [fdBoundaryArcSingularSet]
      · rwa [h_norm_rho]
    · -- ρ → ρ' (have ‖(z-1) - ρ‖ ≤ ε, need ‖z - ρ'‖ ≤ ε)
      refine ⟨ellipticPoint_rho_plus_one, ?_, ?_⟩
      · simp [fdBoundaryArcSingularSet]
      · rw [h_eq_rho']; exact h_le

/-! ## Truncated Vertical Pair Cancellation

For each ε > 0, the truncated integrals over seg1 and seg4 cancel. -/

/-- The ε-truncated integrals over vertical segments cancel for every ε.

Proof sketch: change variables t ↦ 4-t in seg4, then use:
1. seg4_H(4-t) = seg1_H(t) - 1 (proven)
2. logDeriv is 1-periodic (proven)
3. deriv(seg4)(4-t) = -deriv(seg1)(t) (proven)
4. Indicator symmetry (vertical_indicator_symmetric)
Therefore integrands cancel pointwise. -/
theorem cpv_truncated_vertical_cancel_H (H : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∫ t in (0:ℝ)..1, cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg1_H H) ε t) +
    (∫ t in (3:ℝ)..4, cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε t) = 0 := by
  -- Periodicity
  have h_periodic : Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
    simp only [Nat.cast_one] at this; exact this
  have h_logDeriv_periodic : Function.Periodic (logDeriv (modularFormCompOfComplex f)) (1 : ℂ) :=
    logDeriv_periodic_of_periodic h_periodic
  -- Derivative relation: deriv seg4_H (4-s) = -deriv seg1_H s
  have h_deriv_rel : ∀ s : ℝ, deriv (fdBoundary_seg4_H H) (4 - s) =
      -(deriv (fdBoundary_seg1_H H) s) := by
    intro s; rw [deriv_fdBoundary_seg4_H, deriv_fdBoundary_seg1_H]; ring
  -- Change of variables: ∫₃⁴ F₄(t) dt = ∫₀¹ F₄(4-s) ds
  have h_cov := @intervalIntegral.integral_comp_sub_left ℂ _ _ 0 1
      (cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε) 4
  simp only [show (4:ℝ) - 1 = 3 from by norm_num,
      show (4:ℝ) - 0 = 4 from by norm_num] at h_cov
  rw [← h_cov]
  -- Goal: ∫₀¹ F₁(s) ds + ∫₀¹ F₄(4-s) ds = 0
  -- Pointwise: F₄(4-s) = -F₁(s) for s ∈ [[0,1]]
  have h_pw : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      (cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε) (4 - s) =
      -(cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg1_H H) ε s) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    simp only [cauchyPrincipalValueIntegrandOn]
    -- Use vertical_indicator_symmetric to relate the if conditions
    have h_seg : fdBoundary_seg4_H H (4 - s) = fdBoundary_seg1_H H s - 1 :=
      seg4_eq_seg1_minus_one_H' H s hs
    have h_ind := vertical_indicator_symmetric (ε := ε) H s hs
    -- Case split on the indicator
    by_cases h_near : ∃ p ∈ fdBoundaryArcSingularSet, ‖fdBoundary_seg1_H H s - p‖ ≤ ε
    · -- Near a singular point: both integrands are 0
      have h_near' : ∃ p ∈ fdBoundaryArcSingularSet,
          ‖fdBoundary_seg4_H H (4 - s) - p‖ ≤ ε := h_ind.mp h_near
      simp [h_near, h_near']
    · -- Far from singular points: use periodicity and derivative relation
      have h_far' : ¬∃ p ∈ fdBoundaryArcSingularSet,
          ‖fdBoundary_seg4_H H (4 - s) - p‖ ≤ ε :=
        fun h_abs => h_near (h_ind.mpr h_abs)
      simp only [h_near, h_far', ite_false]
      rw [h_seg]
      have h_logD : logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H s - 1) =
          logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H s) := by
        have := h_logDeriv_periodic (fdBoundary_seg1_H H s - 1)
        simp only [sub_add_cancel] at this; exact this.symm
      rw [h_logD, h_deriv_rel]; ring
  -- Apply pointwise equality to rewrite the second integral, then cancel
  rw [intervalIntegral.integral_congr h_pw]
  simp only [intervalIntegral.integral_neg]
  exact add_neg_eq_zero.mpr rfl

/-! ## Arc S-isometry on Unit Circle

S(z) = -1/z is an isometry on the unit circle: ‖S(z) - S(w)‖ = ‖z - w‖ when |z|=|w|=1.
This ensures the CPV truncation is symmetric under the S-action. -/

/-- S = z ↦ -1/z is an isometry on the unit circle. -/
lemma S_isometry_unit_circle (z w : ℂ) (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖-(1:ℂ)/z - (-(1:ℂ)/w)‖ = ‖z - w‖ := by
  -- Get nonzero from norms
  have hzne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; norm_num at hz
  have hwne : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; norm_num at hw
  -- Simplify: -1/z - (-1/w) = -1/z + 1/w = (z - w)/(z*w)
  have h_eq : -(1:ℂ)/z - (-(1:ℂ)/w) = (z - w) / (z * w) := by
    field_simp; ring
  rw [h_eq, norm_div, norm_mul, hz, hw]
  -- ‖z - w‖ / (1 * 1) = ‖z - w‖
  norm_num

/-! ## Arc CPV Helper Lemmas

The S-symmetry proof decomposes into three components:
1. **Arc indicator symmetry**: `indicator(ε, 4-t) = indicator(ε, t)` on the arc.
   Uses S-isometry on unit circle + S maps S₀ to S₀.
2. **Arc S-reversal**: `γ(4-t) = S(γ(t)) = -1/γ(t)` on the arc.
3. **Pointwise S-identity**: When the indicator is 1 (far from S₀):
   `F(4-t) = -F(t) - k · (iπ/6)`, from the modular logDeriv functional equation.

Combining: `I(ε) = -I(ε) - k·(iπ/6)·m(ε)`, so `I(ε) = -k·(iπ/6)·m(ε)/2`.
As `m(ε) → 2`, we get `I(ε) → -(2πik/12)`. -/

/-- On the arc (1,3), the S-reversal identity holds: γ(4-t) = -1/γ(t).

Uses `fdBoundary_H_eq_arc` to normalize both sides to `exp(i·π·(1+t)/6)`,
then `exp(α)·exp(β) = exp(πi) = -1` where `α + β = πi`. -/
lemma fdBoundary_arc_S_reverse (H : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) :
    fdBoundary_H H (4 - t) = -(1:ℂ) / fdBoundary_H H t := by
  -- Both t and 4-t are in (1,3)
  rw [fdBoundary_H_eq_arc (by linarith [ht.2]) (by linarith [ht.1]),
      fdBoundary_H_eq_arc ht.1 ht.2]
  have hne : exp ((↑(Real.pi * (1 + t) / 6) : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
  -- Suffices: exp(α) * exp(β) = -1 where α + β = πI
  rw [eq_div_iff hne, ← Complex.exp_add]
  convert exp_pi_mul_I using 2
  push_cast; ring

/-- The arc CPV indicator is symmetric under t ↦ 4-t.

This combines the S-reversal `γ(4-t) = -1/γ(t)`, the S-isometry on the unit circle,
and the fact that S maps S₀ = {i, ρ', ρ} to itself. -/
lemma arc_indicator_symmetric (H : ℝ) (ε : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) :
    (∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_H H (4 - t) - (s : ℂ)‖ ≤ ε) ↔
    (∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε) := by
  have h_arc_rev : fdBoundary_H H (4 - t) = -(1:ℂ) / fdBoundary_H H t :=
    fdBoundary_arc_S_reverse H t ht
  have h_norm_t : ‖fdBoundary_H H t‖ = 1 := by
    rw [fdBoundary_H_eq_arc ht.1 ht.2]; exact Complex.norm_exp_ofReal_mul_I _
  -- All singular points have norm 1
  have hs_norm : ∀ s ∈ fdBoundaryArcSingularSet, ‖(s : ℂ)‖ = 1 := by
    intro s hs
    simp only [fdBoundaryArcSingularSet, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · show ‖(I : ℂ)‖ = 1; exact Complex.norm_I
    · have : ‖(ellipticPoint_rho_plus_one : ℂ)‖ ^ 2 = 1 := by
        rw [Complex.sq_norm]; exact_mod_cast normSq_ellipticPoint_rho_plus_one
      nlinarith [norm_nonneg (ellipticPoint_rho_plus_one : ℂ)]
    · have : ‖(ellipticPoint_rho : ℂ)‖ ^ 2 = 1 := by
        rw [Complex.sq_norm]; exact_mod_cast normSq_ellipticPoint_rho
      nlinarith [norm_nonneg (ellipticPoint_rho : ℂ)]
  -- All singular points are nonzero
  have hs_ne : ∀ s ∈ fdBoundaryArcSingularSet, (s : ℂ) ≠ 0 := by
    intro s hs; intro h; have := hs_norm s hs; rw [h, norm_zero] at this; norm_num at this
  -- Key: ‖γ(4-t) - (-1/s)‖ = ‖γ(t) - s‖ via S-isometry + h_arc_rev
  have h_key : ∀ s ∈ fdBoundaryArcSingularSet,
      ‖fdBoundary_H H (4 - t) - (-(1:ℂ) / s)‖ = ‖fdBoundary_H H t - s‖ := by
    intro s hs; rw [h_arc_rev]
    exact S_isometry_unit_circle _ s h_norm_t (hs_norm s hs)
  constructor
  · rintro ⟨s₀, hs₀, h_le⟩
    -- Take s₁ = -1/s₀ ∈ S₀; then ‖γ(t) - s₁‖ = ‖γ(4-t) - s₀‖ ≤ ε
    refine ⟨-(1:ℂ) / s₀, S_maps_singularSet_to_self s₀ hs₀, ?_⟩
    rw [← h_key (-(1:ℂ) / s₀) (S_maps_singularSet_to_self s₀ hs₀)]
    rwa [show -(1:ℂ) / (-(1:ℂ) / s₀) = s₀ from by field_simp]
  · rintro ⟨s₁, hs₁, h_le⟩
    -- Take s₀ = -1/s₁ ∈ S₀; then ‖γ(4-t) - s₀‖ = ‖γ(t) - s₁‖ ≤ ε
    refine ⟨-(1:ℂ) / s₁, S_maps_singularSet_to_self s₁ hs₁, ?_⟩
    rw [h_key s₁ hs₁]; exact h_le

/-- The CPV integrand is IntervalIntegrable on the arc [1,3], given that f is nonvanishing
at non-excluded points of the arc and ε > 0.

The function is either 0 (on the ε-excluded set near {i, ρ, ρ'}) or logDeriv g ∘ γ * deriv γ
(on the non-excluded compact set where g is analytic and nonzero). -/
private lemma cpv_integrand_intervalIntegrable_arc (H : ℝ) (ε : ℝ) (hε : 0 < ε)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    IntervalIntegrable
      (fun t => cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t)
      MeasureTheory.volume 1 3 := by
  set g := modularFormCompOfComplex f with hg_def
  set γ := fdBoundary_H H with hγ_def
  set S₀ := fdBoundaryArcSingularSet
  set F := fun t => cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t
  -- Step 1: Define the compact set K' where the indicator is false (far from all singular points)
  set K' := {t ∈ Set.Icc (1:ℝ) 3 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
  -- Step 2: K' is compact
  have hK'_compact : IsCompact K' := by
    refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
    apply IsClosed.inter isClosed_Icc
    -- The set {t | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖} is closed as a finite intersection of closed sets
    have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
      isClosed_iInter fun s => isClosed_iInter fun _ =>
        isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
          (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
    convert this using 1
    ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
  -- Step 3: Define K = non-excluded part = {t ∈ uIoc 1 3 | not near singular set}
  set K := {t ∈ Set.uIoc (1:ℝ) 3 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
  -- Step 4: K ⊆ K'
  have hK_subset_K' : K ⊆ K' := by
    intro t ⟨ht_uioc, h_not_near⟩
    have ht_Ioc : t ∈ Set.Ioc 1 3 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
    refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
    by_contra h_contra; push_neg at h_contra
    exact h_not_near ⟨s, hs, h_contra.le⟩
  -- Step 5: h(t) := logDeriv g (γ t) * deriv γ t is ContinuousOn K'
  have h_cont : ContinuousOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
    intro t ⟨⟨ht1, ht3⟩, h_far⟩
    -- For t ∈ K', we must have t ∈ (1,3) and t ≠ 2 because:
    -- γ(1) = ρ', γ(3) = ρ, γ(2) = i are all in S₀, so at these points dist(γ t, s) = 0 for some s ∈ S₀,
    -- which violates ε ≤ dist(γ t, s) (since ε > 0)
    have h_at_1 : γ 1 = ellipticPoint_rho_plus_one :=
      (fdBoundary_H_at_one H).trans fdBoundary_at_one
    have h_at_2 : γ 2 = ellipticPoint_i :=
      (fdBoundary_H_at_two H).trans fdBoundary_at_two
    have h_at_3 : γ 3 = ellipticPoint_rho :=
      (fdBoundary_H_at_three H).trans fdBoundary_at_three
    have rho'_in_S₀ : ellipticPoint_rho_plus_one ∈ S₀ := by
      show ellipticPoint_rho_plus_one ∈ fdBoundaryArcSingularSet
      simp [fdBoundaryArcSingularSet]
    have i_in_S₀ : ellipticPoint_i ∈ S₀ := by
      show ellipticPoint_i ∈ fdBoundaryArcSingularSet
      simp [fdBoundaryArcSingularSet]
    have rho_in_S₀ : ellipticPoint_rho ∈ S₀ := by
      show ellipticPoint_rho ∈ fdBoundaryArcSingularSet
      simp [fdBoundaryArcSingularSet]
    have ht_not_1 : t ≠ 1 := by
      intro h_eq; subst h_eq
      have := h_far ellipticPoint_rho_plus_one rho'_in_S₀
      rw [h_at_1, sub_self, norm_zero] at this
      linarith
    have ht_not_3 : t ≠ 3 := by
      intro h_eq; subst h_eq
      have := h_far ellipticPoint_rho rho_in_S₀
      rw [h_at_3, sub_self, norm_zero] at this
      linarith
    have ht_ne_2 : t ≠ 2 := by
      intro h_eq; subst h_eq
      have := h_far ellipticPoint_i i_in_S₀
      rw [h_at_2, sub_self, norm_zero] at this
      linarith
    have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
      ⟨lt_of_le_of_ne ht1 (Ne.symm ht_not_1), lt_of_le_of_ne ht3 ht_not_3⟩
    -- Now apply the main continuity argument
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.comp
      · have h_im : 0 < (γ t).im := by
          rw [show γ t = _ from fdBoundary_H_eq_arc ht_ioo.1 ht_ioo.2, Complex.exp_ofReal_mul_I_im]
          exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        have h_ne : g (γ t) ≠ 0 := h_arc_nv t ht_ioo ht_ne_2
        exact (analyticAt_logDeriv_off_zeros f (γ t) h_im h_ne).continuousAt
      · exact (fdBoundary_H_continuous H).continuousAt
    · -- For the deriv part, use that deriv γ t = π/6 * I * γ t on the arc
      have h_deriv_eq : deriv γ =ᶠ[𝓝 t] fun s => ↑(Real.pi / 6) * I * γ s := by
        filter_upwards [Ioo_mem_nhds ht_ioo.1 ht_ioo.2] with s hs
        show deriv (fdBoundary_H H) s = ↑(Real.pi / 6) * I * fdBoundary_H H s
        rw [fdBoundary_H_eq_arc hs.1 hs.2]
        exact (fdBoundary_H_hasDerivAt_arc H hs.1 hs.2).deriv
      exact (ContinuousAt.mul (ContinuousAt.mul continuousAt_const continuousAt_const)
        (fdBoundary_H_continuous H).continuousAt).congr h_deriv_eq.symm
  -- Step 6: h is IntegrableOn K'
  have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' :=
    ContinuousOn.integrableOn_compact hK'_compact h_cont
  -- Step 7: F = h on K (since not in indicator set) and F = 0 on uIoc \ K
  have hK_meas : MeasurableSet K := by
    apply measurableSet_uIoc.inter
    apply MeasurableSet.compl
    suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
      have hm := h.measurableSet
      convert hm using 1
      ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
    exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
      isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        continuous_const
  have hF_K : EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
    intro t ⟨_, h_not_near⟩
    show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
    rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
  have h_int_K : MeasureTheory.IntegrableOn F K :=
    (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
  -- Step 8: F = 0 on uIoc \ K (by definition of cauchyPrincipalValueIntegrandOn)
  have h_compl_zero : EqOn F 0 (Set.uIoc (1:ℝ) 3 \ K) := by
    intro t ⟨ht_uioc, h_not_K⟩
    show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
    rw [cauchyPrincipalValueIntegrandOn]
    have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
      by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
    exact if_pos h_near
  have hcompl_meas : MeasurableSet (Set.uIoc (1:ℝ) 3 \ K) :=
    measurableSet_uIoc.diff hK_meas
  have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (1:ℝ) 3 \ K) :=
    MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
  -- Step 9: Union and interval integrability
  have h_union : K ∪ (Set.uIoc (1:ℝ) 3 \ K) = Set.uIoc (1:ℝ) 3 :=
    Set.union_diff_cancel (fun t ht => ht.1)
  have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (1:ℝ) 3) := by
    have := h_int_K.union h_int_compl; rwa [h_union] at this
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  rwa [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at h_int_union

/-- The ε-truncated arc integral satisfies the S-symmetry identity:
`I(ε) = -I(ε) - k · (iπ/6) · m(ε)` where `m(ε)` is the non-excluded measure.

Dividing: `I(ε) = -k · (iπ/12) · m(ε)`.
The proof combines the change of variables t ↦ 4-t, arc indicator symmetry,
and the pointwise logDeriv functional equation F(4-t) = -F(t) - k·(iπ/6). -/
lemma arc_cpv_integral_S_identity (H : ℝ) (ε : ℝ) (hε : 0 < ε)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
        (↑fdBoundaryArcSingularSet)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) =
    -(↑k * (↑Real.pi / 12 * I)) *
      ↑(∫ t in (1:ℝ)..3,
        if (∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
        then (0:ℝ) else 1) := by
  -- Abbreviations
  set g := modularFormCompOfComplex f with hg_def
  set γ := fdBoundary_H H with hγ_def
  set F := cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet) (logDeriv g) γ ε
  set ind := fun t => ∃ s ∈ fdBoundaryArcSingularSet, ‖γ t - (s : ℂ)‖ ≤ ε
  -- ---- Boundary values ----
  have h_gamma_1 : γ 1 = ellipticPoint_rho_plus_one := by
    rw [show γ = fdBoundary_H H from rfl, fdBoundary_H_at_one, fdBoundary_at_one]
  have h_gamma_3 : γ 3 = ellipticPoint_rho := by
    rw [show γ = fdBoundary_H H from rfl, fdBoundary_H_at_three, fdBoundary_at_three]
  have h_ind_1 : ind 1 := by
    refine ⟨ellipticPoint_rho_plus_one, ?_, ?_⟩
    · simp [fdBoundaryArcSingularSet]
    · rw [h_gamma_1, sub_self, norm_zero]; linarith
  have h_ind_3 : ind 3 := by
    refine ⟨ellipticPoint_rho, ?_, ?_⟩
    · simp [fdBoundaryArcSingularSet]
    · rw [h_gamma_3, sub_self, norm_zero]; linarith
  -- ---- Step 1: Change of variables t ↦ 4-t on [1,3] ----
  have h_cov : ∫ t in (1:ℝ)..3, F (4 - t) = ∫ t in (1:ℝ)..3, F t := by
    have h := @intervalIntegral.integral_comp_sub_left ℂ _ _ 1 3 F 4
    simp only [show (4:ℝ) - 3 = 1 from by norm_num,
        show (4:ℝ) - 1 = 3 from by norm_num] at h
    exact h
  -- ---- Step 2: Indicator symmetry ----
  have h_ind_sym : ∀ t ∈ Set.Ioo (1:ℝ) 3, (ind (4 - t) ↔ ind t) :=
    fun t ht => arc_indicator_symmetric H ε t ht
  -- ---- Step 3: Arc properties ----
  have h_arc_ne_zero : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → γ t ≠ 0 := by
    intro t ht; rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2]; exact exp_ne_zero _
  have h_arc_im_pos : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → 0 < (γ t).im := by
    intro t ht
    rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2, Complex.exp_ofReal_mul_I_im]
    apply Real.sin_pos_of_pos_of_lt_pi
    · nlinarith [ht.1, Real.pi_pos]
    · nlinarith [ht.2, Real.pi_pos]
  have h_4mt_ioo : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → (4 - t) ∈ Set.Ioo (1:ℝ) 3 := by
    intro t ht; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h_deriv_arc : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 →
      deriv γ t = ↑(Real.pi / 6) * I * γ t := by
    intro t ht
    have h1 := (fdBoundary_H_hasDerivAt_arc H ht.1 ht.2).deriv
    rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2]
    exact h1
  -- ---- Step 4: Pointwise identity ----
  -- F(4-t) + F(t) = -(k*(π/6*I)) * (if ind t then 0 else 1) for t ∈ [1,3]
  have h_pw : ∀ t ∈ Set.uIcc (1:ℝ) 3,
      F (4 - t) + F t = -(↑k * (↑Real.pi / 6 * I)) *
        ↑(if ind t then (0:ℝ) else 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht
    by_cases h_near : ind t
    · -- Near case: both F(4-t) and F(t) are 0
      have h_F_t : F t = 0 := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = 0
        rw [cauchyPrincipalValueIntegrandOn, if_pos h_near]
      have h_ind_4mt : ind (4 - t) := by
        by_cases h1 : 1 < t ∧ t < 3
        · exact (h_ind_sym t ⟨h1.1, h1.2⟩).mpr h_near
        · push_neg at h1
          -- t ∈ [1,3] but not in (1,3), so t = 1 or t = 3
          rcases eq_or_lt_of_le ht.1 with rfl | h_lt
          · -- t = 1: 4 - 1 = 3, ind 3 holds
            exact (show (4:ℝ) - 1 = 3 from by norm_num) ▸ h_ind_3
          · -- 1 < t, so by h1: t ≥ 3, combined with ht.2: t = 3
            have : t = 3 := le_antisymm ht.2 (h1 h_lt)
            subst this; exact (show (4:ℝ) - 3 = 1 from by norm_num) ▸ h_ind_1
      have h_F_4mt : F (4 - t) = 0 := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = 0
        rw [cauchyPrincipalValueIntegrandOn, if_pos h_ind_4mt]
      rw [h_F_4mt, h_F_t]; simp [h_near]
    · -- Far case: t ∈ (1,3) strictly (since ind is true at 1 and 3)
      have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 := by
        constructor
        · exact lt_of_le_of_ne ht.1 (fun h => h_near (h ▸ h_ind_1))
        · exact lt_of_le_of_ne ht.2 (fun h => h_near (h ▸ h_ind_3))
      -- Also 4-t ∈ (1,3) and ¬ind(4-t)
      have h_4mt := h_4mt_ioo t ht_ioo
      have h_not_ind_4mt : ¬ind (4 - t) :=
        fun h => h_near ((h_ind_sym t ht_ioo).mp h)
      -- Expand F using cauchyPrincipalValueIntegrandOn definition
      have h_F_t : F t = logDeriv g (γ t) * deriv γ t := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_near]
      have h_F_4mt : F (4 - t) = logDeriv g (γ (4 - t)) * deriv γ (4 - t) := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_ind_4mt]
      rw [h_F_4mt, h_F_t, if_neg h_near]
      simp only [Complex.ofReal_one, mul_one]
      -- S-reversal: γ(4-t) = -1/γ(t)
      have h_rev : γ (4 - t) = -(1:ℂ) / γ t := fdBoundary_arc_S_reverse H t ht_ioo
      -- Derivatives
      have h_d_t := h_deriv_arc t ht_ioo -- deriv γ t = (π/6)*I*γ(t)
      have h_d_4mt := h_deriv_arc (4-t) h_4mt -- deriv γ (4-t) = (π/6)*I*γ(4-t)
      -- logDeriv S-transform
      have hz_ne := h_arc_ne_zero t ht_ioo
      have hz_im := h_arc_im_pos t ht_ioo
      have h_not_eq_2 : t ≠ 2 := by
        intro h_eq; subst h_eq; apply h_near
        exact ⟨ellipticPoint_i, by simp [fdBoundaryArcSingularSet], by
          rw [show γ 2 = _ from fdBoundary_H_at_two H,
              show fdBoundary 2 = ellipticPoint_i from fdBoundary_at_two,
              sub_self, norm_zero]; linarith⟩
      have hg_ne : g (γ t) ≠ 0 := h_arc_nv t ht_ioo h_not_eq_2
      -- S-transform: logDeriv g z = logDeriv g (-1/z)/z^2 - k/z
      have h_logD := logDeriv_modform_S_transform f (γ t) hz_im hz_ne hg_ne
      -- Normalize to use g (= modularFormCompOfComplex f) everywhere
      simp only [← hg_def] at h_logD
      -- Substitute γ(4-t) = -1/γ(t) everywhere, then derivatives and S-transform
      rw [h_rev] at h_d_4mt ⊢
      rw [h_d_4mt, h_d_t, h_logD]
      -- Goal is now purely in terms of logDeriv g (-1/γ t), γ t, k, π, I
      -- After field_simp clears γ t denominators, push_cast + ring finishes
      field_simp
      push_cast
      ring
  -- ---- Step 5: Integrability ----
  -- F is bounded: either 0 (near singular) or logDeriv*deriv (bounded on compact arc)
  have hF_int : IntervalIntegrable F MeasureTheory.volume 1 3 :=
    cpv_integrand_intervalIntegrable_arc f H ε hε h_arc_nv
  -- ---- Step 6: Conclude via CoV + pointwise identity ----
  -- From h_pw: F(4-t) + F(t) = C * ind_real(t) for t ∈ [1,3]
  -- From h_cov: ∫ F(4-t) = ∫ F(t)
  -- So: 2 * ∫ F(t) = ∫ (F(4-t) + F(t)) = C * ∫ ind_real(t)
  set I_val := ∫ t in (1:ℝ)..3, F t
  set m_val := ∫ t in (1:ℝ)..3, if ind t then (0:ℝ) else 1
  -- Compute ∫ (F(4-t) + F(t))
  have h_sum_int : ∫ t in (1:ℝ)..3, (F (4 - t) + F t) =
      -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
    calc ∫ t in (1:ℝ)..3, (F (4 - t) + F t)
        = ∫ t in (1:ℝ)..3, -(↑k * (↑Real.pi / 6 * I)) *
            ↑(if ind t then (0:ℝ) else 1) :=
          intervalIntegral.integral_congr h_pw
      _ = -(↑k * (↑Real.pi / 6 * I)) *
            ∫ t in (1:ℝ)..3, (↑(if ind t then (0:ℝ) else 1) : ℂ) :=
          intervalIntegral.integral_const_mul _ _
      _ = -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
          congr 1; exact intervalIntegral.integral_ofReal
  -- Split the sum: ∫ (F(4-·) + F) = ∫ F(4-·) + ∫ F
  have h_cov_int : IntervalIntegrable (fun t => F (4 - t)) MeasureTheory.volume 1 3 := by
    convert (hF_int.comp_sub_left 4).symm using 2 <;> norm_num
  have h_sum_split : ∫ t in (1:ℝ)..3, (F (4 - t) + F t) =
      (∫ t in (1:ℝ)..3, F (4 - t)) + ∫ t in (1:ℝ)..3, F t :=
    intervalIntegral.integral_add h_cov_int hF_int
  -- Combine: ∫ F(4-·) = ∫ F, so I+I = C * m
  have h_2I : I_val + I_val = -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
    have : (∫ t in (1:ℝ)..3, F (4 - t)) + I_val =
        -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
      rw [← h_sum_split]; exact h_sum_int
    rwa [h_cov] at this
  -- Solve: I = (C/2) * m = -(k*(π/12*I)) * m
  have h_solve : I_val = -(↑k * (↑Real.pi / 12 * I)) * ↑m_val := by
    have two_ne : (2 : ℂ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ two_ne
    rw [show (2 : ℂ) * I_val = I_val + I_val from by ring, h_2I]; ring
  exact h_solve

omit f in
/-- On the open arc (1,3), the curve `fdBoundary_H H t` avoids all singular points
except at t = 2. For t ∈ (1,3) with t ≠ 2,
`fdBoundary_H H t ≠ s` for every s ∈ S₀ = {i, ρ', ρ}.

Proof: compare real parts. The arc gives re(γ(t)) = cos(π(1+t)/6), and cos is
strictly anti-monotone on [0,π]. The real parts of ρ', i, ρ are 1/2, 0, -1/2,
matching cos(π/3), cos(π/2), cos(2π/3), which force t = 1, 2, 3 respectively. -/
private lemma arc_avoids_singular_off_two (H : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (1:ℝ) 3)
    (ht2 : t ≠ 2) (s : ℂ) (hs : s ∈ fdBoundaryArcSingularSet) :
    fdBoundary_H H t ≠ s := by
  rw [fdBoundary_H_eq_arc ht.1 ht.2]
  simp only [fdBoundaryArcSingularSet, Finset.mem_insert, Finset.mem_singleton] at hs
  intro h_eq
  have h_re := congr_arg Complex.re h_eq
  rw [Complex.exp_ofReal_mul_I_re] at h_re
  have hpi := Real.pi_pos
  have hθ_mem : Real.pi * (1 + t) / 6 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  rcases hs with rfl | rfl | rfl
  · -- s = i: re(i) = 0 = cos(π/2), so θ = π/2, t = 2
    have h_re_val : (ellipticPoint_i : ℂ).re = 0 := by show (I : ℂ).re = 0; exact Complex.I_re
    rw [h_re_val] at h_re
    have h_pi2 : Real.pi / 2 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
    have h_cos : Real.cos (Real.pi * (1 + t) / 6) = Real.cos (Real.pi / 2) := by
      rw [Real.cos_pi_div_two]; linarith
    have := Real.strictAntiOn_cos.injOn hθ_mem h_pi2 h_cos
    -- this : π*(1+t)/6 = π/2, need t = 2
    have h1 : Real.pi * (t - 2) = 0 := by linear_combination 6 * this
    exact ht2 (by linarith [(mul_eq_zero.mp h1).resolve_left (ne_of_gt hpi)])
  · -- s = ρ': re(ρ') = 1/2 = cos(π/3), so θ = π/3, t = 1
    have h_re_val : (ellipticPoint_rho_plus_one : ℂ).re = 1/2 := by
      show (1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = 1/2
      simp [add_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self]
    rw [h_re_val] at h_re
    have h_pi3 : Real.pi / 3 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
    have h_cos : Real.cos (Real.pi * (1 + t) / 6) = Real.cos (Real.pi / 3) := by
      rw [Real.cos_pi_div_three]; linarith
    have := Real.strictAntiOn_cos.injOn hθ_mem h_pi3 h_cos
    -- this : π*(1+t)/6 = π/3, need t = 1 contradicting ht.1
    have h1 : Real.pi * (t - 1) = 0 := by linear_combination 6 * this
    linarith [(mul_eq_zero.mp h1).resolve_left (ne_of_gt hpi), ht.1]
  · -- s = ρ: re(ρ) = -1/2 = cos(2π/3), so θ = 2π/3, t = 3
    have h_re_val : (ellipticPoint_rho : ℂ).re = -1/2 := by
      show (-1/2 + (Real.sqrt 3 / 2) * I : ℂ).re = -1/2
      simp [add_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, I_im, mul_one, sub_self]
    rw [h_re_val] at h_re
    have h_2pi3 : 2 * Real.pi / 3 ∈ Set.Icc 0 Real.pi := ⟨by linarith, by linarith⟩
    have h_cos : Real.cos (Real.pi * (1 + t) / 6) = Real.cos (2 * Real.pi / 3) := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; linarith
    have := Real.strictAntiOn_cos.injOn hθ_mem h_2pi3 h_cos
    -- this : π*(1+t)/6 = 2π/3, need t = 3 contradicting ht.2
    have h1 : Real.pi * (t - 3) = 0 := by linear_combination 6 * this
    linarith [(mul_eq_zero.mp h1).resolve_left (ne_of_gt hpi), ht.2]

/-- For t ∈ (1,3) with t ≠ 2, there exists δ > 0 with ‖γ(t) - s‖ ≥ δ for all s ∈ S₀. -/
private lemma arc_min_dist_pos (H : ℝ) {t : ℝ} (ht : t ∈ Set.Ioo (1:ℝ) 3) (ht2 : t ≠ 2) :
    ∃ δ > 0, ∀ s ∈ fdBoundaryArcSingularSet, δ ≤ ‖fdBoundary_H H t - s‖ := by
  obtain ⟨s₀, hs₀, h_min⟩ := Finset.exists_min_image fdBoundaryArcSingularSet
    (fun s => ‖fdBoundary_H H t - s‖)
    ⟨ellipticPoint_i, by simp [fdBoundaryArcSingularSet]⟩
  exact ⟨‖fdBoundary_H H t - s₀‖,
    norm_pos_iff.mpr (sub_ne_zero.mpr (arc_avoids_singular_off_two H ht ht2 s₀ hs₀)),
    h_min⟩

/-- The non-excluded arc measure m(ε) → 2 as ε → 0⁺.

Proof by dominated convergence: the integrand `g(ε,t) = 𝟙_{E(ε)^c}(t)` converges
pointwise to 1 for a.e. t ∈ [1,3] (the exceptional set {t=2} ∪ {t=3} has measure 0),
is bounded by 1, and 1 is integrable on [1,3]. -/
lemma arc_non_excluded_measure_tendsto (H : ℝ) :
    Tendsto (fun ε => ∫ t in (1:ℝ)..3,
        if (∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
        then (0:ℝ) else 1)
      (𝓝[>] 0) (𝓝 2) := by
  -- Rewrite target as ∫₁³ 1 dt = 2
  have h_int_one : ∫ t in (1:ℝ)..3, (1:ℝ) = 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; norm_num
  rw [show (2:ℝ) = ∫ t in (1:ℝ)..3, (1:ℝ) from h_int_one.symm]
  -- Apply dominated convergence with bound = 1, limit function = 1
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
  · -- (1) Measurability of F(ε, ·) on Ioc 1 3
    apply Filter.Eventually.of_forall; intro ε
    apply Measurable.aestronglyMeasurable
    apply measurable_const.ite _ measurable_const
    -- The condition set {t | ∃ s ∈ S₀, ‖γ(t) - s‖ ≤ ε} is measurable
    -- because it's a finite union of preimages of closed sets under continuous maps
    have : {a | ∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_H H a - s‖ ≤ ε} =
        ⋃ s ∈ (fdBoundaryArcSingularSet : Finset ℂ), {a | ‖fdBoundary_H H a - s‖ ≤ ε} := by
      ext x; simp [Set.mem_iUnion]
    rw [this]
    exact Finset.measurableSet_biUnion _ (fun s _hs =>
      (isClosed_le
        (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        continuous_const).measurableSet)
  · -- (2) Bound: |F(ε, t)| ≤ 1
    apply Filter.Eventually.of_forall; intro ε
    apply Filter.Eventually.of_forall; intro t; intro _
    split_ifs <;> simp
  · -- (3) Bound integrable: constant 1 is integrable
    exact intervalIntegrable_const
  · -- (4) Pointwise a.e. limit: for a.e. t ∈ Ioc 1 3, F(ε,t) → 1
    -- The failure set is contained in {2, 3} (measure zero).
    -- For t ∈ (1,3) with t ≠ 2, all singular points are far from γ(t).
    rw [ae_iff]
    apply measure_mono_null (t := ({2, 3} : Set ℝ))
    · -- {t | ¬(t ∈ uIoc 1 3 → Tendsto ...)} ⊆ {2, 3}
      intro t ht
      push_neg at ht
      obtain ⟨ht_mem, ht_not⟩ := ht
      rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht_mem
      -- t ∈ Ioc 1 3 and F(ε,t) does NOT tend to 1
      -- Show: t ∈ {2, 3} (by contradiction: if t ∉ {2,3}, we derive Tendsto)
      by_contra h_not_in
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h_not_in
      apply ht_not
      -- t ∈ Ioo 1 3 and t ≠ 2
      have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
        ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 h_not_in.2⟩
      -- Min distance from γ(t) to S₀ is positive
      obtain ⟨δ, hδ_pos, hδ_le⟩ := arc_min_dist_pos H ht_ioo h_not_in.1
      -- For ε < δ, the condition is FALSE, so F(ε,t) = 1
      -- Hence Tendsto is eventually constant at 1
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
      rw [Set.mem_Ioo] at hε
      rw [if_neg]; push_neg
      intro s hs
      calc ε < δ := hε.2
        _ ≤ ‖fdBoundary_H H t - ↑s‖ := hδ_le s hs
    · -- volume {2, 3} = 0 (two singletons under Lebesgue measure)
      rw [show ({2, 3} : Set ℝ) = {2} ∪ {3} from by ext; simp [or_comm] ]
      exact measure_union_null Real.volume_singleton Real.volume_singleton

/-! ## Arc CPV Contribution

The CPV of the arc integral equals -(2πik/12), matching the standard result.

For each ε, the ε-truncated arc integral satisfies the S-symmetry identity
`I(ε) = -k · (iπ/6) · m(ε)` (from `arc_cpv_integral_S_identity`),
and `m(ε) → 2` (from `arc_non_excluded_measure_tendsto`).
Therefore `I(ε) → -k · iπ/6 = -(2πik/12)`.

**Hypothesis `h_arc_nv`**: f does not vanish on the open arc (1,3) except
possibly at t = 2 (where γ(2) = i ∈ S₀). This is needed because zeros of f
outside S₀ create non-integrable poles that the ε-truncation does not regularize. -/

set_option maxHeartbeats 400000 in
theorem arc_cpv_contribution_is_k_div_12 (H : ℝ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    Tendsto (fun ε => ∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
        (↑fdBoundaryArcSingularSet)
        (logDeriv (modularFormCompOfComplex f))
        (fdBoundary_H H) ε t)
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * (k : ℂ) / 12))) := by
  -- Key: For each ε > 0, I(ε) = -k·(iπ/12)·m(ε) (from S-symmetry identity)
  -- As ε → 0: m(ε) → 2, so I(ε) → -k·iπ/6 = -(2πik/12)
  set I_arc : ℝ → ℂ := fun ε => ∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
      (↑fdBoundaryArcSingularSet)
      (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t
  set m_fun : ℝ → ℝ := fun ε => ∫ t in (1:ℝ)..3,
      if (∃ s ∈ fdBoundaryArcSingularSet, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
      then (0:ℝ) else 1
  set g_fun : ℝ → ℂ := fun x => -(↑k * (↑Real.pi / 12 * I)) * (↑x : ℂ)
  -- Step 1: I_arc =ᶠ g_fun ∘ m_fun (S-symmetry identity for each ε > 0)
  have h_id : I_arc =ᶠ[𝓝[>] (0:ℝ)] (g_fun ∘ m_fun) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact arc_cpv_integral_S_identity f H ε hε h_arc_nv
  -- Step 2: m_fun → 2
  have h_m : Tendsto m_fun (𝓝[>] 0) (𝓝 2) := arc_non_excluded_measure_tendsto H
  -- Step 3: g_fun is continuous, g_fun(2) = -(2πik/12)
  have h_g_cont : Tendsto g_fun (𝓝 2) (𝓝 (g_fun 2)) :=
    (continuous_const.mul Complex.continuous_ofReal).continuousAt
  have h_target : -(2 * ↑Real.pi * I * (↑k : ℂ) / 12) = g_fun 2 := by
    simp only [g_fun]; push_cast; ring
  -- Step 4: Compose and transfer via eventual equality
  rw [h_target]
  exact Filter.Tendsto.congr' h_id.symm (h_g_cont.comp h_m)

/-! ## Seg5 CPV Convergence Infrastructure

The seg5 CPV integral ∫₄⁵ CPV(ε,t) dt converges to 2πi·orderAtCusp as ε → 0.
This uses dominated convergence: for a.e. t, the CPV integrand converges pointwise
to the standard integrand (the failure set where seg5(t) ∈ S₀ has measure 0).

The key nonvanishing result: under `hcusp_nonvan`, the modular form is nonzero
along the entire seg5 path, so logDeriv is continuous and the standard integral
exists and equals 2πi·orderAtCusp by `seg5_logDeriv_integral_eq_H`. -/

/-- The modular form composition is nonzero along seg5 at height H,
given the cusp nonvanishing hypothesis. -/
private lemma modularFormCompOfComplex_ne_zero_seg5_H
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (t : ℝ) : modularFormCompOfComplex f (fdBoundary_seg5_H H t) ≠ 0 := by
  set z := fdBoundary_seg5_H H t
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f
  set q := Function.Periodic.qParam (1 : ℝ) z
  have hH_pos : 0 < H := by linarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)]
  -- g(z) = F(q(z)) via functional equality
  have h_func_eq : modularFormCompOfComplex f = F ∘ (Function.Periodic.qParam (1 : ℝ)) := by
    ext w
    simp only [modularFormCompOfComplex, Function.comp_def, F,
      SlashInvariantFormClass.cuspFunction]
    have := (SlashInvariantFormClass.periodic_comp_ofComplex 1 f).eq_cuspFunction
      (Nat.cast_ne_zero.mpr (by norm_num : (1 : ℕ) ≠ 0)) w
    convert this.symm using 2; norm_cast
  -- ‖q‖ = R (via norm_qParam + seg5 has Im = H)
  have hq_norm : ‖q‖ = seg5_q_radius_H H := by
    simp only [q, Function.Periodic.norm_qParam, div_one, seg5_q_radius_H]
    rw [fdBoundary_seg5_H_im]
  -- q ≠ 0
  have hq_ne : q ≠ 0 := by
    intro h; rw [h, norm_zero] at hq_norm
    exact absurd hq_norm.symm (ne_of_gt (seg5_q_radius_H_pos H))
  -- q ∈ closedBall(0, R)
  have hq_mem : q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H) := by
    rw [Metric.mem_closedBall, dist_zero_right, hq_norm]
  -- Apply hcusp_nonvan
  rw [show modularFormCompOfComplex f z = F q from congr_fun h_func_eq z]
  exact hcusp_nonvan q hq_mem hq_ne

/-- logDeriv of the modular form composition is continuous along seg5
when the form is nonvanishing there. -/
private lemma continuousOn_logDeriv_seg5_H
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ContinuousOn (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t))
      (Set.Icc 4 5) := by
  have hH_pos : 0 < H := by linarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 3)]
  intro t ht
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.comp
  · have h_im : 0 < (fdBoundary_seg5_H H t).im := by
      rw [fdBoundary_seg5_H_im]; exact hH_pos
    have h_ne : modularFormCompOfComplex f (fdBoundary_seg5_H H t) ≠ 0 :=
      modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan t
    exact (analyticAt_logDeriv_off_zeros f _ h_im h_ne).continuousAt
  · exact (continuous_fdBoundary_seg5_H H).continuousAt

/-- For H > √3/2, seg5(t) ≠ s for every s ∈ S₀, provided t ≠ 9/2. -/
private lemma seg5_H_ne_singularSet_off_mid
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ≠ 9/2) :
    ∀ s ∈ fdBoundaryArcSingularSet, fdBoundary_seg5_H H t ≠ s := by
  intro s hs
  simp only [fdBoundaryArcSingularSet, Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with rfl | rfl | rfl
  · -- s = i: real parts differ (t - 9/2 ≠ 0 while Re(i) = 0)
    intro h_eq
    have h_re := congr_arg Complex.re h_eq
    simp only [fdBoundary_seg5_H, add_re, ofReal_re, mul_re, I_re, mul_zero, I_im,
      mul_one, sub_zero] at h_re
    show False
    have this_re : (ellipticPoint_i : ℂ).re = 0 := by show (I : ℂ).re = 0; exact I_re
    rw [this_re] at h_re
    -- h_re : (↑t - 9 / 2).re + (0 - (↑H).im) = 0
    simp only [Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im, zero_re, zero_sub,
      Complex.zero_im, neg_zero, add_zero] at h_re
    norm_num at h_re
    -- h_re : t - 9/2 = 0, so t = 9/2
    have : t = 9/2 := by linarith
    exact ht this
  · -- s = ρ': imaginary parts differ (H > √3/2 = Im(ρ'))
    apply ne_of_apply_ne Complex.im
    rw [fdBoundary_seg5_H_im]
    simp only [ellipticPoint_rho_plus_one]
    norm_num
    intro h
    -- h : H = (ellipticPoint_rho_plus_one' : ℍ).im
    -- The imaginary part computes to √3/2, so H = √3/2
    -- But hH : √3 / 2 < H, a contradiction
    have him : ellipticPoint_rho_plus_one'.im = Real.sqrt 3 / 2 := by
      simp [ellipticPoint_rho_plus_one', UpperHalfPlane.im]
    linarith
  · -- s = ρ: imaginary parts differ (H > √3/2 = Im(ρ))
    apply ne_of_apply_ne Complex.im
    rw [fdBoundary_seg5_H_im]
    simp only [ellipticPoint_rho]
    norm_num
    intro h
    -- h : H = (ellipticPoint_rho' : ℍ).im
    -- The imaginary part computes to √3/2, so H = √3/2
    -- But hH : √3 / 2 < H, a contradiction
    have him : ellipticPoint_rho'.im = Real.sqrt 3 / 2 := by
      simp [ellipticPoint_rho', UpperHalfPlane.im]
    linarith

/-- For H > √3/2 and t ≠ 9/2, the minimum distance from seg5(t) to S₀ is positive. -/
private lemma seg5_H_min_dist_pos
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ≠ 9/2) :
    ∃ δ > 0, ∀ s ∈ fdBoundaryArcSingularSet, δ ≤ ‖fdBoundary_seg5_H H t - s‖ := by
  obtain ⟨s₀, hs₀, h_min⟩ := Finset.exists_min_image fdBoundaryArcSingularSet
    (fun s => ‖fdBoundary_seg5_H H t - s‖)
    ⟨ellipticPoint_i, by simp [fdBoundaryArcSingularSet]⟩
  exact ⟨‖fdBoundary_seg5_H H t - s₀‖,
    norm_pos_iff.mpr (sub_ne_zero.mpr (seg5_H_ne_singularSet_off_mid hH ht s₀ hs₀)),
    h_min⟩

/-! ## Main CPV Modular-Side Theorem

The full CPV integral over the parameterized FD boundary equals
  -(2πi(k/12 - ord_∞))
under hypotheses:
- f ≠ 0
- H > √3/2 (boundary reaches fundamental domain)
- f nonvanishing on open arc except at S₀ points
- Cusp nonvanishing (for seg5 contribution)

Key difference from `pv_integral_eq_modular_transformation_H`:
- Uses `pv_integral_logDeriv` (CPV) instead of `pv_integral` (standard integral)
- Does NOT require `hint_H` (IntervalIntegrable)
- Does NOT require `h_nv` (boundary nonvanishing) at i, ρ, ρ'
-/

set_option maxHeartbeats 800000 in
include hf in
theorem pv_integral_logDeriv_eq_modular_H_cpv
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_vert_nv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp f : ℂ))) := by
  -- Unfold to limUnder form
  unfold pv_integral_logDeriv cauchyPrincipalValueOn
  haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  -- Step 1: Integral splitting — ∀ᶠ ε, ∫₀⁵ = ∫₁³ + ∫₄⁵ (verticals cancel)
  have h_split : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ t in (0:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t =
      (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
          (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) +
      (∫ t in (4:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    -- hε : ε ∈ Set.Ioi 0
    have hε_pos : 0 < ε := hε
    set g := modularFormCompOfComplex f with hg_def
    set γ := fdBoundary_H H with hγ_def
    set F := fun t => cauchyPrincipalValueIntegrandOn
        (↑fdBoundaryArcSingularSet) (logDeriv g) γ ε t with hF_def
    -- ---- Step 1: IntervalIntegrable on each sub-interval ----
    -- [1,3]: from existing lemma
    have hint_13 : IntervalIntegrable F volume 1 3 :=
      cpv_integrand_intervalIntegrable_arc f H ε hε_pos h_arc_nv
    -- [0,1] and [3,4]: using the K/complement decomposition
    -- Helper: logDeriv g ∘ γ * deriv γ is ContinuousOn the "far" subset of each interval
    -- For [0,1]:
    have hint_01 : IntervalIntegrable F volume 0 1 := by
      set S₀ := fdBoundaryArcSingularSet
      -- The "far" set K' where integrand is nonzero
      set K' := {t ∈ Set.Icc (0:ℝ) 1 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      -- K' is compact
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        apply IsClosed.inter isClosed_Icc
        convert this using 1
        ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      -- ContinuousOn the "far" set
      have h_cont : ContinuousOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        intro t ⟨⟨ht0, ht1⟩, h_far⟩
        -- t = 1 is excluded (γ(1) = ρ' ∈ S₀, distance 0 < ε)
        have h_at_1 : γ 1 = ellipticPoint_rho_plus_one :=
          (fdBoundary_H_at_one H).trans fdBoundary_at_one
        have rho'_in_S₀ : ellipticPoint_rho_plus_one ∈ S₀ := by
          unfold S₀; simp [fdBoundaryArcSingularSet]
        have ht_ne_1 : t ≠ 1 := by
          intro h_eq; subst h_eq
          have := h_far ellipticPoint_rho_plus_one rho'_in_S₀
          rw [h_at_1, sub_self, norm_zero] at this; linarith
        have ht_ioo : t ∈ Set.Ioo (0:ℝ) 1 ∨ t = 0 := by
          rcases eq_or_lt_of_le ht0 with rfl | h
          · right; rfl
          · left; exact ⟨h, lt_of_le_of_ne ht1 ht_ne_1⟩
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.mul
        · -- logDeriv g ∘ γ is continuous: g(γ t) ≠ 0
          apply ContinuousAt.comp
          · have h_im : 0 < (γ t).im := by
              rw [show γ t = fdBoundary_seg1_H H t from
                fdBoundary_H_eq_seg1_H (le_of_lt (lt_of_le_of_ne ht1 ht_ne_1))]
              have him : (fdBoundary_seg1_H H t).im = H - t * (H - Real.sqrt 3 / 2) := by
                simp [fdBoundary_seg1_H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
              rw [him]
              nlinarith [hH, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
            have h_ne : g (γ t) ≠ 0 := by
              rcases ht_ioo with h | rfl
              · exact h_vert_nv t h
              · -- t = 0: γ(0) = seg5(5), use cusp nonvanishing
                rw [show γ 0 = fdBoundary_seg5_H H 5 from by
                  rw [hγ_def, fdBoundary_H_at_zero]; simp [fdBoundary_seg5_H]; push_cast; ring]
                exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 5
            exact (analyticAt_logDeriv_off_zeros f _ h_im h_ne).continuousAt
          · exact (fdBoundary_H_continuous H).continuousAt
        · -- deriv γ is continuous at t (for t ∈ [0,1))
          have ht_lt_1 : t < 1 := lt_of_le_of_ne ht1 ht_ne_1
          have h_deriv_eq : deriv γ =ᶠ[𝓝 t] fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I := by
            filter_upwards [Iio_mem_nhds ht_lt_1] with s hs
            exact (fdBoundary_H_hasDerivAt_seg1 H hs).deriv
          exact continuousAt_const.congr h_deriv_eq.symm
      -- IntegrableOn the far set (compact + continuous)
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' :=
        ContinuousOn.integrableOn_compact hK'_compact h_cont
      -- The CPV integrand is either 0 or equal to logDeriv g ∘ γ * deriv γ
      set K := {t ∈ Set.uIoc (0:ℝ) 1 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 0 1 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter
        apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (0:ℝ) 1 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have hcompl_meas : MeasurableSet (Set.uIoc (0:ℝ) 1 \ K) :=
        measurableSet_uIoc.diff hK_meas
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (0:ℝ) 1 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
      have h_union : K ∪ (Set.uIoc (0:ℝ) 1 \ K) = Set.uIoc (0:ℝ) 1 :=
        Set.union_diff_cancel (fun t ht => ht.1)
      have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (0:ℝ) 1) := by
        have := h_int_K.union h_int_compl; rwa [h_union] at this
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h_int_union
    -- For [3,4]: analogous using T-periodicity
    have hint_34 : IntervalIntegrable F volume 3 4 := by
      set S₀ := fdBoundaryArcSingularSet
      set K' := {t ∈ Set.Icc (3:ℝ) 4 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        apply IsClosed.inter isClosed_Icc
        convert this using 1
        ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      -- ContinuousOn for just the logDeriv g ∘ γ factor on K'
      -- (the full product logDeriv g (γ t) * deriv γ t is NOT continuous at junction t=4)
      have h_cont_logDeriv : ContinuousOn (fun t => logDeriv g (γ t)) K' := by
        intro t ⟨⟨ht3, ht4⟩, h_far⟩
        have h_at_3 : γ 3 = ellipticPoint_rho :=
          (fdBoundary_H_at_three H).trans fdBoundary_at_three
        have rho_in_S₀ : ellipticPoint_rho ∈ S₀ := by
          simp [S₀, fdBoundaryArcSingularSet]
        have ht_ne_3 : t ≠ 3 := by
          intro h_eq; subst h_eq
          have h_zero : ‖γ 3 - ellipticPoint_rho‖ = 0 := by
            rw [h_at_3, sub_self, norm_zero]
          linarith [h_far ellipticPoint_rho rho_in_S₀]
        have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm ht_ne_3)
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.comp
        · -- logDeriv g is analytic at γ(t) for all t ∈ (3, 4]
          have h_eq_seg4 : γ t = fdBoundary_seg4_H H t :=
            fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) ht4
          have h_im : 0 < (γ t).im := by
            rw [h_eq_seg4]
            have him : (fdBoundary_seg4_H H t).im = Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
              simp [fdBoundary_seg4_H, add_im, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
            rw [him]
            nlinarith [hH, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
          have h_ne : g (γ t) ≠ 0 := by
            have h_periodic : Function.Periodic g (1 : ℂ) := by
              have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
              simp only [Nat.cast_one] at this; exact this
            by_cases ht4' : t < 4
            · -- T-periodicity for t ∈ (3, 4)
              rw [h_eq_seg4]
              have h_s := seg4_eq_seg1_minus_one_H' H (4 - t)
                (by constructor <;> linarith)
              rw [show 4 - (4 - t) = t from by ring] at h_s
              rw [h_s]
              have h_4mt : 4 - t ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
              rw [show g (fdBoundary_seg1_H H (4 - t) - 1) =
                  g (fdBoundary_seg1_H H (4 - t)) from by
                have := h_periodic (fdBoundary_seg1_H H (4 - t) - 1)
                simp only [sub_add_cancel] at this; exact this.symm]
              have : g (fdBoundary_seg1_H H (4 - t)) ≠ 0 := by
                convert h_vert_nv (4 - t) h_4mt using 2
                exact (fdBoundary_H_eq_seg1_H (le_of_lt h_4mt.2)).symm
              exact this
            · -- t = 4: use seg5 nonvanishing
              push_neg at ht4'; have := le_antisymm ht4 ht4'; subst this
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 4
          exact (analyticAt_logDeriv_off_zeros f _ h_im h_ne).continuousAt
        · exact (fdBoundary_H_continuous H).continuousAt
      -- IntegrableOn via ae-equality with a "nice" function (logDeriv * const)
      -- The full product is NOT continuous at t=4 (deriv γ has a jump), but agrees ae
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        -- Nice function (with constant seg4 derivative) is ContinuousOn K', hence integrable
        have h_nice_int : MeasureTheory.IntegrableOn
            (fun t => logDeriv g (γ t) * ((↑(H - Real.sqrt 3 / 2) : ℂ) * I)) K' :=
          (h_cont_logDeriv.mul continuousOn_const).integrableOn_compact hK'_compact
        -- Actual function agrees ae with nice (differ only at {3,4}, measure 0)
        exact h_nice_int.congr (by
          have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
          have h_null : volume ({3, 4} : Set ℝ) = 0 :=
            measure_union_null Real.volume_singleton Real.volume_singleton
          filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr h_null),
            ae_restrict_mem hK'_meas] with t ht_compl ht_K'
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_compl
          congr 1; rw [hγ_def]
          exact (fdBoundary_H_hasDerivAt_seg4 H
            (lt_of_le_of_ne ht_K'.1.1 (Ne.symm ht_compl.1))
            (lt_of_le_of_ne ht_K'.1.2 ht_compl.2)).deriv.symm)
      set K := {t ∈ Set.uIoc (3:ℝ) 4 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 3 4 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter
        apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (3:ℝ) 4 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have hcompl_meas : MeasurableSet (Set.uIoc (3:ℝ) 4 \ K) :=
        measurableSet_uIoc.diff hK_meas
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (3:ℝ) 4 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
      have h_union : K ∪ (Set.uIoc (3:ℝ) 4 \ K) = Set.uIoc (3:ℝ) 4 :=
        Set.union_diff_cancel (fun t ht => ht.1)
      have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (3:ℝ) 4) := by
        have := h_int_K.union h_int_compl; rwa [h_union] at this
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (3:ℝ) ≤ 4)]
      rwa [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at h_int_union
    -- For [4,5]: using seg5 nonvanishing
    have hint_45 : IntervalIntegrable F volume 4 5 := by
      set S₀ := fdBoundaryArcSingularSet
      set K' := {t ∈ Set.Icc (4:ℝ) 5 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        apply IsClosed.inter isClosed_Icc
        convert this using 1
        ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have hH_pos : 0 < H := by
        linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
      -- ContinuousOn for just the logDeriv g ∘ γ factor on K'
      -- (the full product is NOT continuous at junction t=4)
      have h_cont_logDeriv : ContinuousOn (fun t => logDeriv g (γ t)) K' := by
        intro t ⟨⟨ht4, ht5⟩, _h_far⟩
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.comp
        · rcases eq_or_lt_of_le ht4 with rfl | ht4'
          · -- t = 4
            exact (analyticAt_logDeriv_off_zeros f _ (by
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              rw [fdBoundary_seg5_H_im]; exact hH_pos) (by
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 4)).continuousAt
          · -- 4 < t ≤ 5
            exact (analyticAt_logDeriv_off_zeros f _ (by
              have : γ t = fdBoundary_seg5_H H t := by
                rw [hγ_def]; exact fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)
              rw [this, fdBoundary_seg5_H_im]; exact hH_pos) (by
              have : γ t = fdBoundary_seg5_H H t := by
                rw [hγ_def]; exact fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)
              rw [this]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan t)).continuousAt
        · exact (fdBoundary_H_continuous H).continuousAt
      -- IntegrableOn via ae-equality with logDeriv g ∘ γ (nice function: deriv = 1 on seg5)
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        -- logDeriv g ∘ γ is integrable on compact K'
        have h_nice_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t)) K' :=
          h_cont_logDeriv.integrableOn_compact hK'_compact
        -- Actual agrees ae: on (4, 5], deriv γ t = 1, so logDeriv * deriv = logDeriv * 1
        -- They differ at most at {4}, which has Lebesgue measure 0
        have h_ae : (fun t => logDeriv g (γ t)) =ᵐ[volume.restrict K']
            (fun t => logDeriv g (γ t) * deriv γ t) := by
          have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
          filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr
            (Real.volume_singleton : volume ({4} : Set ℝ) = 0)),
            ae_restrict_mem hK'_meas] with t ht_ne4 ht_K'
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht_ne4
          rw [(fdBoundary_H_hasDerivAt_seg5 H
            (lt_of_le_of_ne ht_K'.1.1 (Ne.symm ht_ne4))).deriv, mul_one]
        exact h_nice_int.congr h_ae
      set K := {t ∈ Set.uIoc (4:ℝ) 5 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 4 5 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter
        apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (4:ℝ) 5 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have hcompl_meas : MeasurableSet (Set.uIoc (4:ℝ) 5 \ K) :=
        measurableSet_uIoc.diff hK_meas
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (4:ℝ) 5 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
      have h_union : K ∪ (Set.uIoc (4:ℝ) 5 \ K) = Set.uIoc (4:ℝ) 5 :=
        Set.union_diff_cancel (fun t ht => ht.1)
      have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (4:ℝ) 5) := by
        have := h_int_K.union h_int_compl; rwa [h_union] at this
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (4:ℝ) ≤ 5)]
      rwa [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at h_int_union
    -- ---- Step 2: Split ∫₀⁵ = ∫₀¹ + ∫₁³ + ∫₃⁴ + ∫₄⁵ ----
    have h_05 : (∫ t in (0:ℝ)..5, F t) =
        (∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t) +
        (∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t) := by
      rw [show (∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t) +
          (∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t) =
        ((∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t)) +
          ((∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t)) from by ring]
      rw [intervalIntegral.integral_add_adjacent_intervals hint_01 hint_13,
          intervalIntegral.integral_add_adjacent_intervals hint_34 hint_45,
          intervalIntegral.integral_add_adjacent_intervals
            (hint_01.trans hint_13) (hint_34.trans hint_45)]
    -- ---- Step 3: Bridge CPV(γ) to CPV(seg1/seg4) on verticals ----
    -- On [0,1]: CPV(γ) = CPV(seg1) a.e.
    have h_congr_01 : ∫ t in (0:ℝ)..1, F t =
        ∫ t in (0:ℝ)..1, cauchyPrincipalValueIntegrandOn
          (↑fdBoundaryArcSingularSet) (logDeriv g) (fdBoundary_seg1_H H) ε t := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      show F t = _
      simp only [hF_def, cauchyPrincipalValueIntegrandOn]
      -- γ t = seg1 t for t ∈ (0, 1]
      have hγ_eq : γ t = fdBoundary_seg1_H H t :=
        fdBoundary_H_eq_seg1_H ht.2
      rw [hγ_eq]
      -- deriv γ t = deriv seg1 t for t < 1
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · -- t = 1: both sides have same γ value, deriv might differ but check if-condition
        -- γ(1) = ρ' ∈ S₀, so ‖γ 1 - ρ'‖ = 0 ≤ ε, both sides are 0
        have h_near : ∃ s ∈ fdBoundaryArcSingularSet,
            ‖fdBoundary_seg1_H H 1 - s‖ ≤ ε := by
          refine ⟨ellipticPoint_rho_plus_one, by simp [fdBoundaryArcSingularSet], ?_⟩
          rw [show fdBoundary_seg1_H H 1 = ellipticPoint_rho_plus_one from by
            rw [← fdBoundary_H_eq_seg1_H (le_refl 1),
                (fdBoundary_H_at_one H).trans fdBoundary_at_one]
          ]
          rw [sub_self, norm_zero]; linarith
        simp [h_near]
      · -- t < 1: deriv γ = deriv seg1
        have h_deriv : deriv γ t = deriv (fdBoundary_seg1_H H) t := by
          have heq : γ =ᶠ[𝓝 t] fdBoundary_seg1_H H :=
            Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht1,
              fun s hs => fdBoundary_H_eq_seg1_H (le_of_lt hs)⟩
          exact Filter.EventuallyEq.deriv_eq heq
        rw [h_deriv]
    -- On [3,4]: CPV(γ) = CPV(seg4) a.e. (excluding measure-zero endpoints {3, 4})
    have h_congr_34 : ∫ t in (3:ℝ)..4, F t =
        ∫ t in (3:ℝ)..4, cauchyPrincipalValueIntegrandOn
          (↑fdBoundaryArcSingularSet) (logDeriv g) (fdBoundary_seg4_H H) ε t := by
      apply intervalIntegral.integral_congr_ae
      -- Need: ∀ᵐ t, t ∈ Ι 3 4 → F t = CPV(seg4, ε, t)
      -- Ι 3 4 = Ioc 3 4. Equality holds for t ∈ (3,4); {4} has measure 0.
      rw [ae_iff]
      apply measure_mono_null (t := ({3, 4} : Set ℝ))
      · intro t ht
        simp only [Set.mem_setOf_eq, not_forall] at ht
        obtain ⟨ht_mem, h_ne⟩ := ht
        rw [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at ht_mem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        -- t ∈ (3,4] and F t ≠ CPV(seg4, ε, t)
        -- For t ∈ (3,4), they ARE equal, so t must be 3 or 4
        by_contra h_not_34
        push_neg at h_not_34
        obtain ⟨h_ne_3, h_ne_4⟩ := h_not_34
        have ht3 : 3 < t := ht_mem.1
        have ht4 : t < 4 := lt_of_le_of_ne ht_mem.2 h_ne_4
        apply h_ne
        show F t = _
        simp only [hF_def, cauchyPrincipalValueIntegrandOn]
        have hγ_eq : γ t = fdBoundary_seg4_H H t :=
          fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) (le_of_lt ht4)
        rw [hγ_eq]
        have heq : γ =ᶠ[𝓝 t] fdBoundary_seg4_H H :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4, Ioo_mem_nhds ht3 ht4,
            fun s hs => fdBoundary_H_eq_seg4_H (by linarith [hs.1])
              (by linarith [hs.1]) (by linarith [hs.1]) (le_of_lt hs.2)⟩
        rw [Filter.EventuallyEq.deriv_eq heq]
      · -- {3, 4} has measure 0
        exact (Set.Finite.insert 3 (Set.finite_singleton (4:ℝ))).measure_zero _
    -- ---- Step 4: Vertical cancellation ----
    have h_cancel := cpv_truncated_vertical_cancel_H f H ε hε_pos
    -- ---- Step 5: Algebra ----
    rw [h_05, h_congr_01, h_congr_34]
    linear_combination h_cancel
  -- Step 2: Arc CPV limit: ∫₁³ → -(2πik/12) as ε → 0
  have h_arc := arc_cpv_contribution_is_k_div_12 f H h_arc_nv
  -- Step 3: Seg5 CPV limit: ∫₄⁵ → 2πi·orderAtCusp as ε → 0
  have h_seg5 : Tendsto (fun ε => ∫ t in (4:ℝ)..5,
      cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t)
      (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * ↑(orderAtCusp f))) := by
    set g := modularFormCompOfComplex f with hg_def
    set γ := fdBoundary_H H with hγ_def
    have hH_pos : 0 < H := by
      linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
    -- Bridge: on (4, ∞), γ = seg5 and deriv γ = 1
    have h_γ_seg5 : ∀ t, 4 < t → γ t = fdBoundary_seg5_H H t :=
      fun t ht => fdBoundary_H_eq_seg5_H
        (by linarith) (by linarith) (by linarith) (by linarith)
    have h_deriv_one : ∀ t, 4 < t → deriv γ t = 1 :=
      fun t ht => (fdBoundary_H_hasDerivAt_seg5 H ht).deriv
    -- Rewrite target as the standard integral
    rw [show (2 * ↑Real.pi * I * ↑(orderAtCusp f) : ℂ) =
        ∫ t in (4:ℝ)..5, logDeriv g (fdBoundary_seg5_H H t) from
        (seg5_logDeriv_integral_eq_H f hf hH_pos hcusp_nonvan).symm]
    -- Apply DCT with bound ‖logDeriv g (seg5 t)‖
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => ‖logDeriv g (fdBoundary_seg5_H H t)‖)
    · -- (C1) AEStronglyMeasurable for each ε
      apply Filter.Eventually.of_forall; intro ε
      have h_cont_g : ContinuousOn (logDeriv g) (γ '' Set.Icc 4 5) := by
        intro z ⟨t, ht, hz⟩; rw [← hz]
        have h_eq : γ t = fdBoundary_seg5_H H t := by
          rcases eq_or_lt_of_le ht.1 with rfl | h
          · simp only [hγ_def, fdBoundary_H_at_four, fdBoundary_seg5_H]; push_cast; ring
          · exact h_γ_seg5 t h
        rw [h_eq]
        exact (analyticAt_logDeriv_off_zeros f _
          (by rw [fdBoundary_seg5_H_im]; exact hH_pos)
          (modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan t)
          ).continuousAt.continuousWithinAt
      have h_cont_deriv : ContinuousOn (deriv γ) (Set.Icc 4 5 \ ↑({4} : Finset ℝ)) :=
        continuousOn_const.congr (fun s ⟨hs_icc, hs_4⟩ => by
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hs_4
          exact h_deriv_one s (lt_of_le_of_ne hs_icc.1 (Ne.symm hs_4)))
      have h_fun_eq : cauchyPrincipalValueIntegrandOn (↑fdBoundaryArcSingularSet)
          (logDeriv g) γ ε = fun t => if ∃ s ∈ fdBoundaryArcSingularSet,
          ‖γ t - ↑s‖ ≤ ε then 0 else logDeriv g (γ t) * deriv γ t := rfl
      rw [h_fun_eq, show (Ι (4:ℝ) 5) = Set.Ioc 4 5 from
        Set.uIoc_of_le (by norm_num)]
      have h_meas := aEStronglyMeasurable_pv_integrand_multipoint (ε := ε)
        fdBoundaryArcSingularSet h_cont_g
        ((fdBoundary_H_continuous H).continuousOn) (P := {4}) h_cont_deriv
      exact h_meas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    · -- (C2) Bound: ‖CPV integrand‖ ≤ ‖logDeriv g (seg5 t)‖ a.e.
      apply Filter.Eventually.of_forall; intro ε
      apply Filter.Eventually.of_forall; intro t; intro ht
      rw [Set.uIoc_of_le (show (4:ℝ) ≤ 5 by norm_num)] at ht
      unfold cauchyPrincipalValueIntegrandOn
      rw [h_γ_seg5 t ht.1, h_deriv_one t ht.1, mul_one]
      split_ifs with h_near
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_refl _
    · -- (C3) Bound integrable: ‖logDeriv g ∘ seg5‖ on [4,5]
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (show (4:ℝ) ≤ 5 by norm_num)]
      exact (continuousOn_logDeriv_seg5_H f hH hcusp_nonvan).norm.integrableOn_compact
        isCompact_Icc
    · -- (C4) Pointwise a.e. limit: CPV(ε,t) → logDeriv g (seg5 t)
      rw [ae_iff]
      apply measure_mono_null (t := ({(9:ℝ)/2} : Set ℝ))
      · -- Failure set ⊆ {9/2}
        intro t ht; push_neg at ht; obtain ⟨ht_mem, ht_not⟩ := ht
        rw [Set.uIoc_of_le (show (4:ℝ) ≤ 5 by norm_num)] at ht_mem
        simp only [Set.mem_singleton_iff]
        by_contra h92; exact ht_not (by
          obtain ⟨δ, hδ_pos, hδ_le⟩ := seg5_H_min_dist_pos hH h92
          apply tendsto_const_nhds.congr'
          filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
          rw [Set.mem_Ioo] at hε
          unfold cauchyPrincipalValueIntegrandOn
          rw [h_γ_seg5 t ht_mem.1, h_deriv_one t ht_mem.1, mul_one]
          rw [if_neg (show ¬∃ s ∈ fdBoundaryArcSingularSet,
              ‖fdBoundary_seg5_H H t - s‖ ≤ ε from by
            push_neg; intro s hs; exact lt_of_lt_of_le hε.2 (hδ_le s hs))])
      · exact Real.volume_singleton
  -- Step 4: Combined Tendsto: (arc + seg5) → -(2πik/12) + 2πi·orderAtCusp
  have h_combined : Tendsto
      (fun ε => (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
          (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) +
        (∫ t in (4:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (↑fdBoundaryArcSingularSet)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t))
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * (k : ℂ) / 12) +
        2 * ↑Real.pi * I * ↑(orderAtCusp f))) :=
    h_arc.add h_seg5
  -- Step 5: Algebra: arc_limit + seg5_limit = target
  have h_eq : -(2 * ↑Real.pi * I * (k : ℂ) / 12) +
      2 * ↑Real.pi * I * ↑(orderAtCusp f) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ↑(orderAtCusp f))) := by
    ring
  rw [h_eq] at h_combined
  -- Step 6: Transfer Tendsto via eventual equality, then extract limUnder
  exact (h_combined.congr' (h_split.mono (fun _ h => h.symm))).limUnder_eq

/-! ## Auto-Cusp Wrapper

Existential version: choose H automatically from f ≠ 0.
The arc nonvanishing hypothesis `h_arc_nv` is passed through since the arc
does not depend on H (it's always the unit circle segment). -/

include hf in
theorem modular_side_auto_cusp_generalizedPV
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun {H'} hH' h_vert_nv => ?_⟩
  -- Arc nonvanishing is H-independent: arc = exp(iπ(1+t)/6), no H dependence
  have h_arc_nv' : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
      modularFormCompOfComplex f (fdBoundary_H H' t) ≠ 0 := by
    intro t ht hne
    have := h_arc_nv t ht hne
    rw [fdBoundary_H_eq_arc ht.1 ht.2] at this ⊢; exact this
  rw [show orderAtCusp' f = orderAtCusp f from rfl]
  exact pv_integral_logDeriv_eq_modular_H_cpv f hf (by linarith [hH₀_gt]) h_arc_nv'
    h_vert_nv (cusp_nonvanishing_seg5_q_radius_H_mono f hH' hH₀_nonvan)

/-! ## On-Curve Zero Membership in Singular Set

If the modular form vanishes at a curve point and the form is nonvanishing on the
open vertical, arc (off t=2), and horizontal segments, then the vanishing point
must be one of the three elliptic/corner points {i, ρ', ρ}. -/

/-- Any zero of `modularFormCompOfComplex f` on the parameterized boundary
`fdBoundary_H H` must lie in the singular set `{i, ρ', ρ}`, provided the form
is nonvanishing on the open segments (vertical, arc away from t=2, horizontal). -/
theorem oncurve_zero_in_fdBoundaryArcSingularSet_of_nonvanishing
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_vert_nv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 5)
    (h_zero : modularFormCompOfComplex f (fdBoundary_H H t) = 0) :
    (fdBoundary_H H t : ℂ) ∈ (fdBoundaryArcSingularSet : Set ℂ) := by
  -- T-periodicity: f(z+1) = f(z), hence f(z-1) = f(z)
  have h_periodic : Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
    simp only [Nat.cast_one] at this; exact this
  -- seg5 nonvanishing: all points at height H have f ≠ 0
  have h_seg5_nv : ∀ s : ℝ, modularFormCompOfComplex f (fdBoundary_seg5_H H s) ≠ 0 :=
    modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan
  obtain ⟨h0, h5⟩ := ht
  -- Case split on which segment t belongs to
  by_cases h1 : t ≤ 1
  · -- [0,1]: seg1 (right vertical)
    by_cases h1' : t = 1
    · -- t = 1 → γ(1) = ρ' ∈ S_arc
      rw [h1', fdBoundary_H_at_one, fdBoundary_at_one]
      exact Finset.mem_coe.mpr (by simp [fdBoundaryArcSingularSet])
    · by_cases h0' : t = 0
      · -- t = 0 → same point as seg5(5), contradiction with seg5 nonvanishing
        exfalso
        have h_eq : fdBoundary_H H 0 = fdBoundary_seg5_H H 5 := by
          rw [fdBoundary_H_at_zero]; simp [fdBoundary_seg5_H]; ring
        rw [h0', h_eq] at h_zero; exact h_seg5_nv 5 h_zero
      · -- t ∈ (0,1) → contradiction with h_vert_nv
        exact absurd h_zero (h_vert_nv t
          ⟨lt_of_le_of_ne h0 (Ne.symm h0'), lt_of_le_of_ne h1 h1'⟩)
  · push_neg at h1 -- h1 : 1 < t
    by_cases h3 : t ≤ 3
    · -- (1,3]: arc
      by_cases h2 : t = 2
      · -- t = 2 → γ(2) = i ∈ S_arc
        rw [h2, fdBoundary_H_at_two, fdBoundary_at_two]
        change ellipticPoint_i ∈ (↑fdBoundaryArcSingularSet : Set ℂ)
        exact Finset.mem_coe.mpr (by simp [fdBoundaryArcSingularSet])
      · by_cases h3' : t = 3
        · -- t = 3 → γ(3) = ρ ∈ S_arc
          rw [h3', fdBoundary_H_at_three, fdBoundary_at_three]
          exact Finset.mem_coe.mpr (by simp [fdBoundaryArcSingularSet])
        · -- t ∈ (1,3) \ {2} → contradiction with h_arc_nv
          exact absurd h_zero (h_arc_nv t ⟨h1, lt_of_le_of_ne h3 h3'⟩ h2)
    · push_neg at h3 -- h3 : 3 < t
      by_cases h4 : t ≤ 4
      · -- (3,4]: seg4 (left vertical)
        by_cases h4' : t = 4
        · -- t = 4 → same point as seg5(4), contradiction with seg5 nonvanishing
          exfalso
          have h_eq : fdBoundary_H H 4 = fdBoundary_seg5_H H 4 := by
            rw [fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; ring
          rw [h4', h_eq] at h_zero; exact h_seg5_nv 4 h_zero
        · -- t ∈ (3,4) → reduce to seg1 via T-invariance + seg4 = seg1 - 1
          exfalso
          have h_t_lt_4 : t < 4 := lt_of_le_of_ne h4 h4'
          -- Step 1: fdBoundary_H H t = fdBoundary_seg4_H H t
          have h_eq1 : fdBoundary_H H t = fdBoundary_seg4_H H t :=
            fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) (by linarith)
          -- Step 2: fdBoundary_seg4_H H t = fdBoundary_seg1_H H (4-t) - 1
          have h_eq2 := seg4_eq_seg1_minus_one_H' H (4 - t)
            (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
          simp only [show (4 : ℝ) - (4 - t) = t from by ring] at h_eq2
          -- Step 3: f(z - 1) = f(z) by T-periodicity
          have h_per : modularFormCompOfComplex f (fdBoundary_seg1_H H (4 - t) - 1) =
              modularFormCompOfComplex f (fdBoundary_seg1_H H (4 - t)) := by
            have := (h_periodic (fdBoundary_seg1_H H (4 - t) - 1)).symm
            rwa [sub_add_cancel] at this
          -- Step 4: fdBoundary_seg1_H H (4-t) = fdBoundary_H H (4-t)
          have h_eq3 : fdBoundary_seg1_H H (4 - t) = fdBoundary_H H (4 - t) :=
            (fdBoundary_H_eq_seg1_H (by linarith : (4 - t : ℝ) ≤ 1)).symm
          -- Chain: h_zero uses fdBoundary_H H t → ... → fdBoundary_H H (4-t)
          rw [h_eq1, h_eq2, h_per, h_eq3] at h_zero
          exact h_vert_nv (4 - t) ⟨by linarith, by linarith⟩ h_zero
      · -- (4,5]: seg5 (top horizontal), contradiction with seg5 nonvanishing
        push_neg at h4 -- h4 : 4 < t
        exfalso
        have h_eq : fdBoundary_H H t = fdBoundary_seg5_H H t :=
          fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)
        rw [h_eq] at h_zero; exact h_seg5_nv t h_zero

/-! ## S_arc Generalization — Dynamic Singular Set

The following section generalizes the fixed singular set `fdBoundaryArcSingularSet = {i, ρ', ρ}`
to an arbitrary `S_arc : Finset ℂ` satisfying:
- `h_S_unit`: all points lie on the unit circle
- `h_S_closed`: the set is closed under the S-map z ↦ -1/z
- `h_oncurve_in_S_arc`: all on-curve zeros of f are in S_arc

This removes `h_arc_nv` from the main theorem signature. -/

omit f hf in
/-- normSq s = 1 when ‖s‖ = 1. -/
private lemma normSq_eq_one_of_norm_one {s : ℂ} (hs : ‖s‖ = 1) : Complex.normSq s = 1 := by
  rw [Complex.normSq_eq_norm_sq, hs]; norm_num

omit f hf in
/-- Re(-1/s) = -Re(s) for s on the unit circle. -/
private lemma neg_inv_re_of_norm_one {s : ℂ} (hs : ‖s‖ = 1) :
    (-(1:ℂ) / s).re = -s.re := by
  rw [neg_div, neg_re, one_div, Complex.inv_re, normSq_eq_one_of_norm_one hs, div_one]

omit f hf in
/-- Im(-1/s) = Im(s) for s on the unit circle. -/
private lemma neg_inv_im_of_norm_one {s : ℂ} (hs : ‖s‖ = 1) :
    (-(1:ℂ) / s).im = s.im := by
  rw [neg_div, neg_im, one_div, Complex.inv_im, normSq_eq_one_of_norm_one hs, div_one, neg_neg]

omit f hf in
/-- -1/(-1/s) = s for s on the unit circle. -/
private lemma neg_inv_involution {s : ℂ} (hs : ‖s‖ = 1) :
    -(1:ℂ) / (-(1:ℂ) / s) = s := by
  have hne : s ≠ 0 := by intro h; rw [h, norm_zero] at hs; norm_num at hs
  field_simp

omit f hf in
/-- ‖-1/s‖ = 1 when ‖s‖ = 1. -/
private lemma norm_neg_inv_of_norm_one {s : ℂ} (hs : ‖s‖ = 1) :
    ‖-(1:ℂ) / s‖ = 1 := by
  rw [norm_div, norm_neg, norm_one, hs, div_one]

omit f hf in
/-- Distance equality for vertical indicator symmetry with unit-circle points:
    ‖seg1(t) - s‖ = ‖(seg1(t) - 1) - (-1/s)‖ when ‖s‖ = 1. -/
private lemma dist_seg1_neg_inv_eq {H t : ℝ} (s : ℂ) (hs : ‖s‖ = 1) :
    ‖fdBoundary_seg1_H H t - s‖ = ‖(fdBoundary_seg1_H H t - 1) - (-(1:ℂ) / s)‖ := by
  set z := fdBoundary_seg1_H H t
  have h_z_re : z.re = 1/2 := by simp [z, fdBoundary_seg1_H]
  -- Both sides have same normSq since Re parts differ by sign, Im parts agree
  have h_nsq : Complex.normSq (z - s) = Complex.normSq ((z - 1) - (-(1:ℂ) / s)) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    rw [neg_inv_re_of_norm_one hs, neg_inv_im_of_norm_one hs, h_z_re]
    ring
  nlinarith [Complex.sq_norm (z - s), Complex.sq_norm ((z - 1) - (-(1:ℂ) / s)),
    norm_nonneg (z - s), norm_nonneg ((z - 1) - (-(1:ℂ) / s))]

omit f hf in
/-- The CPV indicator is symmetric under the vertical T-shift for arbitrary S_arc
    (unit-circle + S-map closure). -/
lemma vertical_indicator_symmetric_of_Sarc (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (H t ε : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (∃ s ∈ S_arc, ‖fdBoundary_seg1_H H t - s‖ ≤ ε) ↔
    (∃ s ∈ S_arc, ‖fdBoundary_seg4_H H (4 - t) - s‖ ≤ ε) := by
  rw [seg4_eq_seg1_minus_one_H' H t ht]
  constructor
  · rintro ⟨s, hs, h_le⟩
    exact ⟨-(1:ℂ)/s, h_S_closed s hs, by rwa [← dist_seg1_neg_inv_eq s (h_S_unit s hs)]⟩
  · rintro ⟨s, hs, h_le⟩
    exact ⟨-(1:ℂ)/s, h_S_closed s hs, by
      rw [dist_seg1_neg_inv_eq (-(1:ℂ)/s) (norm_neg_inv_of_norm_one (h_S_unit s hs)),
          neg_inv_involution (h_S_unit s hs)]; exact h_le⟩

omit f hf in
/-- The arc CPV indicator is symmetric under t ↦ 4-t for arbitrary S_arc
    (unit-circle + S-map closure). -/
lemma arc_indicator_symmetric_of_Sarc (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (H ε : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) :
    (∃ s ∈ S_arc, ‖fdBoundary_H H (4 - t) - (s : ℂ)‖ ≤ ε) ↔
    (∃ s ∈ S_arc, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε) := by
  have h_arc_rev : fdBoundary_H H (4 - t) = -(1:ℂ) / fdBoundary_H H t :=
    fdBoundary_arc_S_reverse H t ht
  have h_norm_t : ‖fdBoundary_H H t‖ = 1 := by
    rw [fdBoundary_H_eq_arc ht.1 ht.2]; exact Complex.norm_exp_ofReal_mul_I _
  constructor
  · -- Forward: from (4-t) side to t side via S-isometry
    rintro ⟨s₀, hs₀, h_le⟩
    refine ⟨-(1:ℂ)/s₀, h_S_closed s₀ hs₀, ?_⟩
    calc ‖fdBoundary_H H t - (-(1:ℂ)/s₀)‖
        = ‖-(1:ℂ)/fdBoundary_H H t - (-(1:ℂ)/(-(1:ℂ)/s₀))‖ :=
          (S_isometry_unit_circle _ _ h_norm_t
            (norm_neg_inv_of_norm_one (h_S_unit s₀ hs₀))).symm
      _ = ‖-(1:ℂ)/fdBoundary_H H t - s₀‖ := by
          rw [neg_inv_involution (h_S_unit s₀ hs₀)]
      _ = ‖fdBoundary_H H (4 - t) - s₀‖ := by rw [← h_arc_rev]
      _ ≤ ε := h_le
  · -- Backward: from t side to (4-t) side via S-isometry
    rintro ⟨s₁, hs₁, h_le⟩
    refine ⟨-(1:ℂ)/s₁, h_S_closed s₁ hs₁, ?_⟩
    rw [h_arc_rev, S_isometry_unit_circle _ _ h_norm_t (h_S_unit s₁ hs₁)]
    exact h_le

omit f hf in
/-- `-1/ρ = ρ'` (ρ + 1) for the elliptic points on the unit circle. -/
private lemma neg_inv_rho_eq_rho_plus_one :
    -(1:ℂ) / ellipticPoint_rho = ellipticPoint_rho_plus_one := by
  have h_ne : (ellipticPoint_rho : ℂ) ≠ 0 := by
    show (-1/2 + ↑(Real.sqrt 3) / 2 * I : ℂ) ≠ 0
    intro h
    have him := congr_arg Complex.im h
    simp only [add_im, neg_im, ofReal_im, div_ofNat, mul_im, ofReal_re, I_re, I_im,
      zero_im, one_im] at him
    linarith [Real.sqrt_pos.mpr (show (3:ℝ) > 0 by norm_num)]
  rw [div_eq_iff h_ne]
  show -(1:ℂ) = (1/2 + ↑(Real.sqrt 3) / 2 * I) * (-1/2 + ↑(Real.sqrt 3) / 2 * I)
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
  apply Complex.ext <;>
    simp only [mul_re, mul_im, add_re, add_im, ofReal_re, ofReal_im, div_ofNat,
      I_re, I_im, neg_re, neg_im, one_re, one_im, mul_zero, add_zero, mul_one,
      zero_sub] <;>
    nlinarith

omit f hf in
/-- If ρ ∈ S_arc and S_arc is S-closed, then ρ' = ρ + 1 ∈ S_arc. -/
private lemma rho_plus_one_in_Sarc (S_arc : Finset ℂ)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc) :
    (ellipticPoint_rho_plus_one : ℂ) ∈ S_arc := by
  rw [← neg_inv_rho_eq_rho_plus_one]; exact h_S_closed _ h_rho_in

/-- Vertical CPV integrals cancel for arbitrary S_arc (unit-circle + S-closure). -/
theorem cpv_truncated_vertical_cancel_H_of_Sarc (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (H : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∫ t in (0:ℝ)..1, cauchyPrincipalValueIntegrandOn (↑S_arc)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg1_H H) ε t) +
    (∫ t in (3:ℝ)..4, cauchyPrincipalValueIntegrandOn (↑S_arc)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε t) = 0 := by
  -- Periodicity
  have h_periodic : Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
    simp only [Nat.cast_one] at this; exact this
  have h_logDeriv_periodic : Function.Periodic (logDeriv (modularFormCompOfComplex f)) (1 : ℂ) :=
    logDeriv_periodic_of_periodic h_periodic
  -- Derivative relation
  have h_deriv_rel : ∀ s : ℝ, deriv (fdBoundary_seg4_H H) (4 - s) =
      -(deriv (fdBoundary_seg1_H H) s) := by
    intro s; rw [deriv_fdBoundary_seg4_H, deriv_fdBoundary_seg1_H]; ring
  -- Change of variables
  have h_cov := @intervalIntegral.integral_comp_sub_left ℂ _ _ 0 1
      (cauchyPrincipalValueIntegrandOn (↑S_arc)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε) 4
  simp only [show (4:ℝ) - 1 = 3 from by norm_num,
      show (4:ℝ) - 0 = 4 from by norm_num] at h_cov
  rw [← h_cov]
  -- Pointwise: F₄(4-s) = -F₁(s) for s ∈ [[0,1]]
  have h_pw : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      (cauchyPrincipalValueIntegrandOn (↑S_arc)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε) (4 - s) =
      -(cauchyPrincipalValueIntegrandOn (↑S_arc)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg1_H H) ε s) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    simp only [cauchyPrincipalValueIntegrandOn]
    have h_seg : fdBoundary_seg4_H H (4 - s) = fdBoundary_seg1_H H s - 1 :=
      seg4_eq_seg1_minus_one_H' H s hs
    have h_ind := vertical_indicator_symmetric_of_Sarc S_arc h_S_unit h_S_closed H s ε hs
    by_cases h_near : ∃ p ∈ S_arc, ‖fdBoundary_seg1_H H s - (p : ℂ)‖ ≤ ε
    · have h_near' : ∃ p ∈ S_arc,
          ‖fdBoundary_seg4_H H (4 - s) - (p : ℂ)‖ ≤ ε := h_ind.mp h_near
      simp [h_near, h_near']
    · have h_far' : ¬∃ p ∈ S_arc,
          ‖fdBoundary_seg4_H H (4 - s) - (p : ℂ)‖ ≤ ε :=
        fun h_abs => h_near (h_ind.mpr h_abs)
      simp only [h_near, h_far', ite_false]
      rw [h_seg]
      have h_logD : logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H s - 1) =
          logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H s) := by
        have := h_logDeriv_periodic (fdBoundary_seg1_H H s - 1)
        simp only [sub_add_cancel] at this; exact this.symm
      rw [h_logD, h_deriv_rel]; ring
  rw [intervalIntegral.integral_congr h_pw]
  simp only [intervalIntegral.integral_neg]
  exact add_neg_eq_zero.mpr rfl

/-- IntervalIntegrable of the arc CPV integrand on [1,3] for arbitrary S_arc.
    Requires ρ ∈ S_arc (for derivative well-definedness at arc endpoints)
    and h_oncurve (for nonvanishing of f away from S_arc). -/
private lemma cpv_integrand_intervalIntegrable_arc_of_Sarc
    (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (H : ℝ) (ε : ℝ) (hε : 0 < ε)
    (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑S_arc : Set ℂ)) :
    IntervalIntegrable
      (fun t => cauchyPrincipalValueIntegrandOn (↑S_arc)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t)
      MeasureTheory.volume 1 3 := by
  set g := modularFormCompOfComplex f with hg_def
  set γ := fdBoundary_H H with hγ_def
  set F := fun t => cauchyPrincipalValueIntegrandOn (↑S_arc) (logDeriv g) γ ε t
  -- Step 1: K' where indicator is false
  set K' := {t ∈ Set.Icc (1:ℝ) 3 | ∀ s ∈ S_arc, ε ≤ ‖γ t - (s : ℂ)‖}
  -- Step 2: K' is compact
  have hK'_compact : IsCompact K' := by
    refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
    apply IsClosed.inter isClosed_Icc
    have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S_arc), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
      isClosed_iInter fun s => isClosed_iInter fun _ =>
        isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
          (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
    convert this using 1
    ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
  -- Step 3: K where F is nonzero
  set K := {t ∈ Set.uIoc (1:ℝ) 3 | ¬∃ s ∈ (↑S_arc : Set ℂ), ‖γ t - s‖ ≤ ε}
  -- Step 4: K ⊆ K'
  have hK_subset_K' : K ⊆ K' := by
    intro t ⟨ht_uioc, h_not_near⟩
    have ht_Ioc : t ∈ Set.Ioc 1 3 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
    refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
    by_contra h_contra; push_neg at h_contra
    exact h_not_near ⟨s, Finset.mem_coe.mpr hs, h_contra.le⟩
  -- Step 5: ContinuousOn h on K'
  have h_cont : ContinuousOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
    intro t ⟨⟨ht1, ht3⟩, h_far⟩
    -- Show t ≠ 1 (since ρ' ∈ S_arc and ‖γ(1) - ρ'‖ = 0)
    have h_rho'_in := rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in
    have ht_not_1 : t ≠ 1 := by
      intro h_eq; subst h_eq
      have h1 := h_far _ h_rho'_in
      have h_at : γ 1 = ellipticPoint_rho_plus_one :=
        show fdBoundary_H H 1 = _ from (fdBoundary_H_at_one H).trans fdBoundary_at_one
      rw [h_at, sub_self, norm_zero] at h1; linarith
    -- Show t ≠ 3 (since ρ ∈ S_arc and ‖γ(3) - ρ‖ = 0)
    have ht_not_3 : t ≠ 3 := by
      intro h_eq; subst h_eq
      have h3 := h_far _ h_rho_in
      have h_at : γ 3 = ellipticPoint_rho :=
        show fdBoundary_H H 3 = _ from (fdBoundary_H_at_three H).trans fdBoundary_at_three
      rw [h_at, sub_self, norm_zero] at h3; linarith
    have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
      ⟨lt_of_le_of_ne ht1 (Ne.symm ht_not_1), lt_of_le_of_ne ht3 ht_not_3⟩
    -- f(γ(t)) ≠ 0 by h_oncurve contrapositive
    have h_ne : g (γ t) ≠ 0 := by
      intro h_zero
      have h_zero' : g (fdBoundary_H H t) = 0 := h_zero
      have h_in_S := h_oncurve t ht_ioo h_zero'
      rw [Finset.mem_coe] at h_in_S
      have h_dist := h_far _ h_in_S
      simp only [hγ_def] at h_dist
      rw [sub_self, norm_zero] at h_dist; linarith
    -- ContinuousAt of logDeriv
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.mul
    · apply ContinuousAt.comp
      · have h_im : 0 < (γ t).im := by
          rw [show γ t = _ from fdBoundary_H_eq_arc ht_ioo.1 ht_ioo.2, Complex.exp_ofReal_mul_I_im]
          exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
        exact (analyticAt_logDeriv_off_zeros f (γ t) h_im h_ne).continuousAt
      · exact (fdBoundary_H_continuous H).continuousAt
    · have h_deriv_eq : deriv γ =ᶠ[𝓝 t] fun s => ↑(Real.pi / 6) * I * γ s := by
        filter_upwards [Ioo_mem_nhds ht_ioo.1 ht_ioo.2] with s hs
        show deriv (fdBoundary_H H) s = ↑(Real.pi / 6) * I * fdBoundary_H H s
        rw [fdBoundary_H_eq_arc hs.1 hs.2]
        exact (fdBoundary_H_hasDerivAt_arc H hs.1 hs.2).deriv
      exact (ContinuousAt.mul (ContinuousAt.mul continuousAt_const continuousAt_const)
        (fdBoundary_H_continuous H).continuousAt).congr h_deriv_eq.symm
  -- Step 6: IntegrableOn h on K'
  have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' :=
    ContinuousOn.integrableOn_compact hK'_compact h_cont
  -- Step 7: F = h on K, F = 0 on complement
  have hK_meas : MeasurableSet K := by
    apply measurableSet_uIoc.inter
    apply MeasurableSet.compl
    suffices h : IsClosed (⋃ s ∈ (↑S_arc : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
      have hm := h.measurableSet
      convert hm using 1
      ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
    exact S_arc.finite_toSet.isClosed_biUnion fun s _ =>
      isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        continuous_const
  have hF_K : EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
    intro t ⟨_, h_not_near⟩
    show cauchyPrincipalValueIntegrandOn (↑S_arc) (logDeriv g) γ ε t = _
    simp only [cauchyPrincipalValueIntegrandOn]
    simp only [Finset.mem_coe] at h_not_near
    exact if_neg h_not_near
  have h_int_K : MeasureTheory.IntegrableOn F K :=
    (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
  -- Step 8: F = 0 on complement
  have h_compl_zero : EqOn F 0 (Set.uIoc (1:ℝ) 3 \ K) := by
    intro t ⟨ht_uioc, h_not_K⟩
    show cauchyPrincipalValueIntegrandOn (↑S_arc) (logDeriv g) γ ε t = 0
    simp only [cauchyPrincipalValueIntegrandOn]
    have h_near : ∃ s ∈ (↑S_arc : Set ℂ), ‖γ t - s‖ ≤ ε := by
      by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
    simp only [Finset.mem_coe] at h_near
    exact if_pos h_near
  have hcompl_meas : MeasurableSet (Set.uIoc (1:ℝ) 3 \ K) :=
    measurableSet_uIoc.diff hK_meas
  have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (1:ℝ) 3 \ K) :=
    MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
  -- Step 9: Conclude
  have h_union : K ∪ (Set.uIoc (1:ℝ) 3 \ K) = Set.uIoc (1:ℝ) 3 :=
    Set.union_diff_cancel (fun t ht => ht.1)
  have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (1:ℝ) 3) := by
    have := h_int_K.union h_int_compl; rwa [h_union] at this
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 3)]
  rwa [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at h_int_union

omit f hf in
/-- The preimage of a point under the arc parameterization has at most one element
    in (1,3), since cos is strictly decreasing on [π/3, 2π/3]. -/
private lemma arc_preimage_subsingleton (H : ℝ) (s : ℂ) :
    Set.Subsingleton ({t ∈ Set.Ioo (1:ℝ) 3 | fdBoundary_H H t = s}) := by
  intro t₁ ⟨ht₁, h₁⟩ t₂ ⟨ht₂, h₂⟩
  have h_re : (Complex.exp (↑(Real.pi * (1 + t₁) / 6) * I)).re =
      (Complex.exp (↑(Real.pi * (1 + t₂) / 6) * I)).re := by
    rw [fdBoundary_H_eq_arc ht₁.1 ht₁.2] at h₁
    rw [fdBoundary_H_eq_arc ht₂.1 ht₂.2] at h₂; rw [h₁, h₂]
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_re] at h_re
  have hpi := Real.pi_pos
  have hθ₁ : Real.pi * (1 + t₁) / 6 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith [ht₁.1], by nlinarith [ht₁.2]⟩
  have hθ₂ : Real.pi * (1 + t₂) / 6 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith [ht₂.1], by nlinarith [ht₂.2]⟩
  have h_angles := Real.strictAntiOn_cos.injOn hθ₁ hθ₂ h_re
  have h_prod : Real.pi * (1 + t₁) = Real.pi * (1 + t₂) := by linarith
  linarith [mul_left_cancel₀ (ne_of_gt hpi) h_prod]

omit f hf in
/-- For t ∈ (1,3) with γ(t) ∉ S_arc, ∃ δ > 0 with ‖γ(t) - s‖ ≥ δ for all s ∈ S_arc. -/
private lemma arc_min_dist_pos_of_Sarc (S_arc : Finset ℂ)
    (H : ℝ) {t : ℝ} (_ht : t ∈ Set.Ioo (1:ℝ) 3)
    (h_not_in : (fdBoundary_H H t : ℂ) ∉ (↑S_arc : Set ℂ)) :
    ∃ δ > 0, ∀ s ∈ S_arc, δ ≤ ‖fdBoundary_H H t - s‖ := by
  rcases S_arc.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, fun s hs => absurd hs (Finset.notMem_empty s)⟩
  · obtain ⟨s₀, hs₀, h_min⟩ := S_arc.exists_min_image
        (fun s => ‖fdBoundary_H H t - s‖) hne
    exact ⟨‖fdBoundary_H H t - s₀‖,
      norm_pos_iff.mpr (sub_ne_zero.mpr (fun h_eq => by
        rw [h_eq] at h_not_in; exact h_not_in (Finset.mem_coe.mpr hs₀))),
      h_min⟩

/-- S-symmetry identity for the arc CPV integral with dynamic S_arc:
    `I(ε) = -k · (iπ/12) · m(ε)`. -/
lemma arc_cpv_integral_S_identity_of_Sarc
    (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (H : ℝ) (ε : ℝ) (hε : 0 < ε)
    (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑S_arc : Set ℂ)) :
    (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn S_arc
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) =
    -(↑k * (↑Real.pi / 12 * I)) *
      ↑(∫ t in (1:ℝ)..3,
        if (∃ s ∈ S_arc, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
        then (0:ℝ) else 1) := by
  set g := modularFormCompOfComplex f with hg_def
  set γ := fdBoundary_H H with hγ_def
  set F := cauchyPrincipalValueIntegrandOn S_arc (logDeriv g) γ ε
  set ind := fun t => ∃ s ∈ S_arc, ‖γ t - (s : ℂ)‖ ≤ ε
  -- Boundary values
  have h_rho'_in := rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in
  have h_gamma_1 : γ 1 = ellipticPoint_rho_plus_one := by
    rw [show γ = fdBoundary_H H from rfl, fdBoundary_H_at_one, fdBoundary_at_one]
  have h_gamma_3 : γ 3 = ellipticPoint_rho := by
    rw [show γ = fdBoundary_H H from rfl, fdBoundary_H_at_three, fdBoundary_at_three]
  have h_ind_1 : ind 1 := ⟨_, h_rho'_in, by rw [h_gamma_1, sub_self, norm_zero]; linarith⟩
  have h_ind_3 : ind 3 := ⟨_, h_rho_in, by rw [h_gamma_3, sub_self, norm_zero]; linarith⟩
  -- Change of variables
  have h_cov : ∫ t in (1:ℝ)..3, F (4 - t) = ∫ t in (1:ℝ)..3, F t := by
    have h := @intervalIntegral.integral_comp_sub_left ℂ _ _ 1 3 F 4
    simp only [show (4:ℝ) - 3 = 1 from by norm_num, show (4:ℝ) - 1 = 3 from by norm_num] at h
    exact h
  -- Indicator symmetry
  have h_ind_sym : ∀ t ∈ Set.Ioo (1:ℝ) 3, (ind (4 - t) ↔ ind t) :=
    fun t ht => arc_indicator_symmetric_of_Sarc S_arc h_S_unit h_S_closed H ε t ht
  -- Arc properties
  have h_arc_ne_zero : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → γ t ≠ 0 := by
    intro t ht; rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2]; exact exp_ne_zero _
  have h_arc_im_pos : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → 0 < (γ t).im := by
    intro t ht
    rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2, Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [ht.1, Real.pi_pos])
      (by nlinarith [ht.2, Real.pi_pos])
  have h_4mt_ioo : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 → (4 - t) ∈ Set.Ioo (1:ℝ) 3 :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h_deriv_arc : ∀ t, t ∈ Set.Ioo (1:ℝ) 3 →
      deriv γ t = ↑(Real.pi / 6) * I * γ t := by
    intro t ht; rw [show γ t = _ from fdBoundary_H_eq_arc ht.1 ht.2]
    exact (fdBoundary_H_hasDerivAt_arc H ht.1 ht.2).deriv
  -- Pointwise identity
  have h_pw : ∀ t ∈ Set.uIcc (1:ℝ) 3,
      F (4 - t) + F t = -(↑k * (↑Real.pi / 6 * I)) *
        ↑(if ind t then (0:ℝ) else 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht
    by_cases h_near : ind t
    · have h_F_t : F t = 0 := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = 0
        rw [cauchyPrincipalValueIntegrandOn, if_pos h_near]
      have h_ind_4mt : ind (4 - t) := by
        by_cases h1 : 1 < t ∧ t < 3
        · exact (h_ind_sym t ⟨h1.1, h1.2⟩).mpr h_near
        · push_neg at h1
          rcases eq_or_lt_of_le ht.1 with rfl | h_lt
          · exact (show (4:ℝ) - 1 = 3 from by norm_num) ▸ h_ind_3
          · have : t = 3 := le_antisymm ht.2 (h1 h_lt)
            subst this; exact (show (4:ℝ) - 3 = 1 from by norm_num) ▸ h_ind_1
      have h_F_4mt : F (4 - t) = 0 := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = 0
        rw [cauchyPrincipalValueIntegrandOn, if_pos h_ind_4mt]
      rw [h_F_4mt, h_F_t]; simp [h_near]
    · -- Far case: t ∈ (1,3) strictly
      have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 := by
        constructor
        · exact lt_of_le_of_ne ht.1 (fun h => h_near (h ▸ h_ind_1))
        · exact lt_of_le_of_ne ht.2 (fun h => h_near (h ▸ h_ind_3))
      have h_4mt := h_4mt_ioo t ht_ioo
      have h_not_ind_4mt : ¬ind (4 - t) := fun h => h_near ((h_ind_sym t ht_ioo).mp h)
      have h_F_t : F t = logDeriv g (γ t) * deriv γ t := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_near]
      have h_F_4mt : F (4 - t) = logDeriv g (γ (4 - t)) * deriv γ (4 - t) := by
        show cauchyPrincipalValueIntegrandOn _ _ _ _ _ = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_ind_4mt]
      rw [h_F_4mt, h_F_t, if_neg h_near]; simp only [Complex.ofReal_one, mul_one]
      have h_rev : γ (4 - t) = -(1:ℂ) / γ t := fdBoundary_arc_S_reverse H t ht_ioo
      have h_d_t := h_deriv_arc t ht_ioo
      have h_d_4mt := h_deriv_arc (4-t) h_4mt
      have hz_ne := h_arc_ne_zero t ht_ioo
      have hz_im := h_arc_im_pos t ht_ioo
      -- g(γ(t)) ≠ 0 from h_oncurve contrapositive
      have hg_ne : g (γ t) ≠ 0 := by
        intro h_zero
        have h_in : (γ t : ℂ) ∈ (↑S_arc : Set ℂ) := h_oncurve t ht_ioo h_zero
        rw [Finset.mem_coe] at h_in
        exact h_near ⟨γ t, h_in, by rw [sub_self, norm_zero]; linarith⟩
      have h_logD := logDeriv_modform_S_transform f (γ t) hz_im hz_ne hg_ne
      simp only [← hg_def] at h_logD
      rw [h_rev] at h_d_4mt ⊢; rw [h_d_4mt, h_d_t, h_logD]
      field_simp; push_cast; ring
  -- Integrability
  have hF_int : IntervalIntegrable F MeasureTheory.volume 1 3 :=
    cpv_integrand_intervalIntegrable_arc_of_Sarc f S_arc h_S_unit h_S_closed h_rho_in H ε hε
      h_oncurve
  -- Conclude via CoV + pointwise identity
  set I_val := ∫ t in (1:ℝ)..3, F t
  set m_val := ∫ t in (1:ℝ)..3, if ind t then (0:ℝ) else 1
  have h_sum_int : ∫ t in (1:ℝ)..3, (F (4 - t) + F t) =
      -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
    calc ∫ t in (1:ℝ)..3, (F (4 - t) + F t)
        = ∫ t in (1:ℝ)..3, -(↑k * (↑Real.pi / 6 * I)) *
            ↑(if ind t then (0:ℝ) else 1) :=
          intervalIntegral.integral_congr h_pw
      _ = -(↑k * (↑Real.pi / 6 * I)) *
            ∫ t in (1:ℝ)..3, (↑(if ind t then (0:ℝ) else 1) : ℂ) :=
          intervalIntegral.integral_const_mul _ _
      _ = -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
          congr 1; exact intervalIntegral.integral_ofReal
  have h_cov_int : IntervalIntegrable (fun t => F (4 - t)) MeasureTheory.volume 1 3 := by
    convert (hF_int.comp_sub_left 4).symm using 2 <;> norm_num
  have h_sum_split : ∫ t in (1:ℝ)..3, (F (4 - t) + F t) =
      (∫ t in (1:ℝ)..3, F (4 - t)) + ∫ t in (1:ℝ)..3, F t :=
    intervalIntegral.integral_add h_cov_int hF_int
  have h_2I : I_val + I_val = -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
    have : (∫ t in (1:ℝ)..3, F (4 - t)) + I_val =
        -(↑k * (↑Real.pi / 6 * I)) * ↑m_val := by
      rw [← h_sum_split]; exact h_sum_int
    rwa [h_cov] at this
  have h_solve : I_val = -(↑k * (↑Real.pi / 12 * I)) * ↑m_val := by
    have two_ne : (2 : ℂ) ≠ 0 := by norm_num
    apply mul_left_cancel₀ two_ne
    rw [show (2 : ℂ) * I_val = I_val + I_val from by ring, h_2I]; ring
  exact h_solve

/-- The non-excluded arc measure m(ε) → 2 as ε → 0⁺ for dynamic S_arc. -/
lemma arc_non_excluded_measure_tendsto_of_Sarc (S_arc : Finset ℂ)
    (_h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (H : ℝ) :
    Tendsto (fun ε => ∫ t in (1:ℝ)..3,
        if (∃ s ∈ S_arc, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
        then (0:ℝ) else 1)
      (𝓝[>] 0) (𝓝 2) := by
  have h_int_one : ∫ t in (1:ℝ)..3, (1:ℝ) = 2 := by
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one]; norm_num
  rw [show (2:ℝ) = ∫ t in (1:ℝ)..3, (1:ℝ) from h_int_one.symm]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
  · -- Measurability
    apply Filter.Eventually.of_forall; intro ε
    apply Measurable.aestronglyMeasurable
    apply measurable_const.ite _ measurable_const
    have : {a | ∃ s ∈ S_arc, ‖fdBoundary_H H a - s‖ ≤ ε} =
        ⋃ s ∈ (S_arc : Finset ℂ), {a | ‖fdBoundary_H H a - s‖ ≤ ε} := by
      ext x; simp [Set.mem_iUnion]
    rw [this]
    exact Finset.measurableSet_biUnion _ (fun s _hs =>
      (isClosed_le
        (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        continuous_const).measurableSet)
  · -- Bound
    apply Filter.Eventually.of_forall; intro ε
    apply Filter.Eventually.of_forall; intro t _
    split_ifs <;> simp
  · exact intervalIntegrable_const
  · -- Pointwise a.e. limit
    rw [ae_iff]
    -- Failure set ⊆ ⋃_{s ∈ S_arc} {t ∈ Ioo 1 3 : γ(t) = s} ∪ {3}
    -- Each preimage is subsingleton; {3} is singleton. Total is finite → measure 0.
    apply measure_mono_null
        (t := (⋃ s ∈ (S_arc : Finset ℂ),
            {t ∈ Set.Ioo (1:ℝ) 3 | fdBoundary_H H t = ↑s}) ∪ {3})
    · intro t ht
      push_neg at ht; obtain ⟨ht_mem, ht_not⟩ := ht
      rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht_mem
      simp only [Set.mem_union, Set.mem_iUnion, Set.mem_sep_iff, Set.mem_singleton_iff]
      by_contra h_not_in
      push_neg at h_not_in
      obtain ⟨h_pre, h_ne_3⟩ := h_not_in
      apply ht_not
      have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
        ⟨ht_mem.1, lt_of_le_of_ne ht_mem.2 h_ne_3⟩
      have h_not_in_S : (fdBoundary_H H t : ℂ) ∉ (↑S_arc : Set ℂ) := by
        rw [Finset.mem_coe]; intro h_mem
        exact h_pre _ h_mem ht_ioo rfl
      obtain ⟨δ, hδ_pos, hδ_le⟩ := arc_min_dist_pos_of_Sarc S_arc H ht_ioo h_not_in_S
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
      rw [Set.mem_Ioo] at hε
      rw [if_neg]; push_neg
      intro s hs
      calc ε < δ := hε.2
        _ ≤ ‖fdBoundary_H H t - ↑s‖ := hδ_le s hs
    · apply measure_union_null
      · exact (S_arc.finite_toSet.biUnion (fun s _ =>
            (arc_preimage_subsingleton H s).finite)).measure_zero _
      · exact Real.volume_singleton

set_option maxHeartbeats 400000 in
/-- The arc CPV contribution tends to -(2πik/12) as ε → 0⁺ for dynamic S_arc. -/
theorem arc_cpv_contribution_is_k_div_12_of_Sarc
    (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (H : ℝ)
    (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑S_arc : Set ℂ)) :
    Tendsto (fun ε => ∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn S_arc
        (logDeriv (modularFormCompOfComplex f))
        (fdBoundary_H H) ε t)
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * (k : ℂ) / 12))) := by
  set I_arc : ℝ → ℂ := fun ε => ∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn S_arc
      (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t
  set m_fun : ℝ → ℝ := fun ε => ∫ t in (1:ℝ)..3,
      if (∃ s ∈ S_arc, ‖fdBoundary_H H t - (s : ℂ)‖ ≤ ε)
      then (0:ℝ) else 1
  set g_fun : ℝ → ℂ := fun x => -(↑k * (↑Real.pi / 12 * I)) * (↑x : ℂ)
  have h_id : I_arc =ᶠ[𝓝[>] (0:ℝ)] (g_fun ∘ m_fun) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact arc_cpv_integral_S_identity_of_Sarc f S_arc h_S_unit h_S_closed h_rho_in H ε hε
      h_oncurve
  have h_m : Tendsto m_fun (𝓝[>] 0) (𝓝 2) :=
    arc_non_excluded_measure_tendsto_of_Sarc S_arc h_rho_in H
  have h_g_cont : Tendsto g_fun (𝓝 2) (𝓝 (g_fun 2)) :=
    (continuous_const.mul Complex.continuous_ofReal).continuousAt
  have h_target : -(2 * ↑Real.pi * I * (↑k : ℂ) / 12) = g_fun 2 := by
    simp only [g_fun]; push_cast; ring
  rw [h_target]
  exact Filter.Tendsto.congr' h_id.symm (h_g_cont.comp h_m)

omit f hf in
/-- Seg5 maps distinct t-values to distinct complex points (injectivity). -/
private lemma seg5_preimage_subsingleton (H : ℝ) (s : ℂ) :
    Set.Subsingleton {t : ℝ | fdBoundary_seg5_H H t = s} := by
  intro t₁ h₁ t₂ h₂
  simp only [Set.mem_setOf_eq] at h₁ h₂
  have h_eq := h₁.trans h₂.symm
  have h_re := congr_arg Complex.re h_eq
  simp [fdBoundary_seg5_H, add_re, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im] at h_re
  linarith

/-! ## Main CPV Modular-Side Theorem (Dynamic S_arc)

Generalizes `pv_integral_logDeriv_eq_modular_H_cpv` from the fixed singular set
`fdBoundaryArcSingularSet = {i, ρ', ρ}` to a dynamic finite set `S_arc` of
unit-circle points that is closed under the S-transformation `s ↦ -1/s`,
contains `ρ`, and includes all on-curve zeros.
-/

set_option maxHeartbeats 800000 in
include hf in
theorem pv_integral_logDeriv_eq_modular_H_cpv_of_Sarc
    (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑S_arc : Set ℂ))
    (h_vert_nv : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral_logDeriv f (fdBoundary_H H) 0 5 S_arc =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp f : ℂ))) := by
  -- Unfold to limUnder form
  unfold pv_integral_logDeriv cauchyPrincipalValueOn
  haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  -- Step 1: Integral splitting — ∀ᶠ ε, ∫₀⁵ = ∫₁³ + ∫₄⁵ (verticals cancel)
  have h_split : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ t in (0:ℝ)..5, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t =
      (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) +
      (∫ t in (4:ℝ)..5, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : 0 < ε := hε
    set g := modularFormCompOfComplex f with hg_def
    set γ := fdBoundary_H H with hγ_def
    set F := fun t => cauchyPrincipalValueIntegrandOn
        S_arc (logDeriv g) γ ε t with hF_def
    -- ---- Step 1: IntervalIntegrable on each sub-interval ----
    have hint_13 : IntervalIntegrable F volume 1 3 :=
      cpv_integrand_intervalIntegrable_arc_of_Sarc f S_arc h_S_unit h_S_closed h_rho_in
        H ε hε_pos h_oncurve
    -- [0,1]: K'/K decomposition
    have hint_01 : IntervalIntegrable F volume 0 1 := by
      set S₀ := S_arc
      set K' := {t ∈ Set.Icc (0:ℝ) 1 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        apply IsClosed.inter isClosed_Icc
        convert this using 1
        ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have h_cont : ContinuousOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        intro t ⟨⟨ht0, ht1⟩, h_far⟩
        have h_at_1 : γ 1 = ellipticPoint_rho_plus_one :=
          (fdBoundary_H_at_one H).trans fdBoundary_at_one
        have rho'_in_S₀ : ellipticPoint_rho_plus_one ∈ S₀ :=
          rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in
        have ht_ne_1 : t ≠ 1 := by
          intro h_eq; subst h_eq
          have := h_far ellipticPoint_rho_plus_one rho'_in_S₀
          rw [h_at_1, sub_self, norm_zero] at this; linarith
        have ht_ioo : t ∈ Set.Ioo (0:ℝ) 1 ∨ t = 0 := by
          rcases eq_or_lt_of_le ht0 with rfl | h
          · right; rfl
          · left; exact ⟨h, lt_of_le_of_ne ht1 ht_ne_1⟩
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.mul
        · apply ContinuousAt.comp
          · have h_im : 0 < (γ t).im := by
              rw [show γ t = fdBoundary_seg1_H H t from
                fdBoundary_H_eq_seg1_H (le_of_lt (lt_of_le_of_ne ht1 ht_ne_1))]
              have him : (fdBoundary_seg1_H H t).im = H - t * (H - Real.sqrt 3 / 2) := by
                simp [fdBoundary_seg1_H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
              rw [him]
              nlinarith [hH, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
            have h_ne : g (γ t) ≠ 0 := by
              rcases ht_ioo with h | rfl
              · exact h_vert_nv t h
              · rw [show γ 0 = fdBoundary_seg5_H H 5 from by
                  rw [hγ_def, fdBoundary_H_at_zero]; simp [fdBoundary_seg5_H]; push_cast; ring]
                exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 5
            exact (analyticAt_logDeriv_off_zeros f _ h_im h_ne).continuousAt
          · exact (fdBoundary_H_continuous H).continuousAt
        · have ht_lt_1 : t < 1 := lt_of_le_of_ne ht1 ht_ne_1
          have h_deriv_eq : deriv γ =ᶠ[𝓝 t] fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I := by
            filter_upwards [Iio_mem_nhds ht_lt_1] with s hs
            exact (fdBoundary_H_hasDerivAt_seg1 H hs).deriv
          exact continuousAt_const.congr h_deriv_eq.symm
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' :=
        ContinuousOn.integrableOn_compact hK'_compact h_cont
      set K := {t ∈ Set.uIoc (0:ℝ) 1 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 0 1 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter
        apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (0:ℝ) 1 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have hcompl_meas : MeasurableSet (Set.uIoc (0:ℝ) 1 \ K) :=
        measurableSet_uIoc.diff hK_meas
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (0:ℝ) 1 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
      have h_union : K ∪ (Set.uIoc (0:ℝ) 1 \ K) = Set.uIoc (0:ℝ) 1 :=
        Set.union_diff_cancel (fun t ht => ht.1)
      have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (0:ℝ) 1) := by
        have := h_int_K.union h_int_compl; rwa [h_union] at this
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rwa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at h_int_union
    -- [3,4]: K'/K decomposition
    have hint_34 : IntervalIntegrable F volume 3 4 := by
      set S₀ := S_arc
      set K' := {t ∈ Set.Icc (3:ℝ) 4 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        apply IsClosed.inter isClosed_Icc
        convert this using 1
        ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have h_cont_logDeriv : ContinuousOn (fun t => logDeriv g (γ t)) K' := by
        intro t ⟨⟨ht3, ht4⟩, h_far⟩
        have h_at_3 : γ 3 = ellipticPoint_rho :=
          (fdBoundary_H_at_three H).trans fdBoundary_at_three
        have ht_ne_3 : t ≠ 3 := by
          intro h_eq; subst h_eq
          have h_zero : ‖γ 3 - ellipticPoint_rho‖ = 0 := by
            rw [h_at_3, sub_self, norm_zero]
          linarith [h_far ellipticPoint_rho h_rho_in]
        have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm ht_ne_3)
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.comp
        · have h_eq_seg4 : γ t = fdBoundary_seg4_H H t :=
            fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) ht4
          have h_im : 0 < (γ t).im := by
            rw [h_eq_seg4]
            have him : (fdBoundary_seg4_H H t).im = Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
              simp [fdBoundary_seg4_H, add_im, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
            rw [him]
            nlinarith [hH, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
          have h_ne : g (γ t) ≠ 0 := by
            have h_periodic : Function.Periodic g (1 : ℂ) := by
              have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
              simp only [Nat.cast_one] at this; exact this
            by_cases ht4' : t < 4
            · rw [h_eq_seg4]
              have h_s := seg4_eq_seg1_minus_one_H' H (4 - t)
                (by constructor <;> linarith)
              rw [show 4 - (4 - t) = t from by ring] at h_s
              rw [h_s]
              have h_4mt : 4 - t ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
              rw [show g (fdBoundary_seg1_H H (4 - t) - 1) =
                  g (fdBoundary_seg1_H H (4 - t)) from by
                have := h_periodic (fdBoundary_seg1_H H (4 - t) - 1)
                simp only [sub_add_cancel] at this; exact this.symm]
              have : g (fdBoundary_seg1_H H (4 - t)) ≠ 0 := by
                convert h_vert_nv (4 - t) h_4mt using 2
                exact (fdBoundary_H_eq_seg1_H (le_of_lt h_4mt.2)).symm
              exact this
            · push_neg at ht4'; have := le_antisymm ht4 ht4'; subst this
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 4
          exact (analyticAt_logDeriv_off_zeros f _ h_im h_ne).continuousAt
        · exact (fdBoundary_H_continuous H).continuousAt
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        have h_nice_int : MeasureTheory.IntegrableOn
            (fun t => logDeriv g (γ t) * ((↑(H - Real.sqrt 3 / 2) : ℂ) * I)) K' :=
          (h_cont_logDeriv.mul continuousOn_const).integrableOn_compact hK'_compact
        exact h_nice_int.congr (by
          have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
          have h_null : volume ({3, 4} : Set ℝ) = 0 :=
            measure_union_null Real.volume_singleton Real.volume_singleton
          filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr h_null),
            ae_restrict_mem hK'_meas] with t ht_compl ht_K'
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_compl
          congr 1; rw [hγ_def]
          exact (fdBoundary_H_hasDerivAt_seg4 H
            (lt_of_le_of_ne ht_K'.1.1 (Ne.symm ht_compl.1))
            (lt_of_le_of_ne ht_K'.1.2 ht_compl.2)).deriv.symm)
      set K := {t ∈ Set.uIoc (3:ℝ) 4 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 3 4 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter
        apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (3:ℝ) 4 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have hcompl_meas : MeasurableSet (Set.uIoc (3:ℝ) 4 \ K) :=
        measurableSet_uIoc.diff hK_meas
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (3:ℝ) 4 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
      have h_union : K ∪ (Set.uIoc (3:ℝ) 4 \ K) = Set.uIoc (3:ℝ) 4 :=
        Set.union_diff_cancel (fun t ht => ht.1)
      have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (3:ℝ) 4) := by
        have := h_int_K.union h_int_compl; rwa [h_union] at this
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (3:ℝ) ≤ 4)]
      rwa [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at h_int_union
    -- [4,5]: K'/K decomposition (seg5 nonvanishing)
    have hint_45 : IntervalIntegrable F volume 4 5 := by
      set S₀ := S_arc
      set K' := {t ∈ Set.Icc (4:ℝ) 5 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le (f := fun _ => ε) (g := fun t => ‖γ t - s‖) continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        apply IsClosed.inter isClosed_Icc
        convert this using 1
        ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have hH_pos : 0 < H := by
        linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
      have h_cont_logDeriv : ContinuousOn (fun t => logDeriv g (γ t)) K' := by
        intro t ⟨⟨ht4, ht5⟩, _h_far⟩
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.comp
        · rcases eq_or_lt_of_le ht4 with rfl | ht4'
          · exact (analyticAt_logDeriv_off_zeros f _ (by
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              rw [fdBoundary_seg5_H_im]; exact hH_pos) (by
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 4)).continuousAt
          · exact (analyticAt_logDeriv_off_zeros f _ (by
              have : γ t = fdBoundary_seg5_H H t := by
                rw [hγ_def]; exact fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)
              rw [this, fdBoundary_seg5_H_im]; exact hH_pos) (by
              have : γ t = fdBoundary_seg5_H H t := by
                rw [hγ_def]; exact fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)
              rw [this]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan t)).continuousAt
        · exact (fdBoundary_H_continuous H).continuousAt
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        have h_nice_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t)) K' :=
          h_cont_logDeriv.integrableOn_compact hK'_compact
        have h_ae : (fun t => logDeriv g (γ t)) =ᵐ[volume.restrict K']
            (fun t => logDeriv g (γ t) * deriv γ t) := by
          have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
          filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr
            (Real.volume_singleton : volume ({4} : Set ℝ) = 0)),
            ae_restrict_mem hK'_meas] with t ht_ne4 ht_K'
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht_ne4
          rw [(fdBoundary_H_hasDerivAt_seg5 H
            (lt_of_le_of_ne ht_K'.1.1 (Ne.symm ht_ne4))).deriv, mul_one]
        exact h_nice_int.congr h_ae
      set K := {t ∈ Set.uIoc (4:ℝ) 5 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 4 5 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter
        apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]; exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (MeasureTheory.IntegrableOn.mono_set h_int hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (4:ℝ) 5 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have hcompl_meas : MeasurableSet (Set.uIoc (4:ℝ) 5 \ K) :=
        measurableSet_uIoc.diff hK_meas
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (4:ℝ) 5 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm hcompl_meas
      have h_union : K ∪ (Set.uIoc (4:ℝ) 5 \ K) = Set.uIoc (4:ℝ) 5 :=
        Set.union_diff_cancel (fun t ht => ht.1)
      have h_int_union : MeasureTheory.IntegrableOn F (Set.uIoc (4:ℝ) 5) := by
        have := h_int_K.union h_int_compl; rwa [h_union] at this
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (4:ℝ) ≤ 5)]
      rwa [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at h_int_union
    -- ---- Step 2: Split ∫₀⁵ = ∫₀¹ + ∫₁³ + ∫₃⁴ + ∫₄⁵ ----
    have h_05 : (∫ t in (0:ℝ)..5, F t) =
        (∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t) +
        (∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t) := by
      rw [show (∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t) +
          (∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t) =
        ((∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t)) +
          ((∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t)) from by ring]
      rw [intervalIntegral.integral_add_adjacent_intervals hint_01 hint_13,
          intervalIntegral.integral_add_adjacent_intervals hint_34 hint_45,
          intervalIntegral.integral_add_adjacent_intervals
            (hint_01.trans hint_13) (hint_34.trans hint_45)]
    -- ---- Step 3: Bridge CPV(γ) to CPV(seg1/seg4) on verticals ----
    have h_congr_01 : ∫ t in (0:ℝ)..1, F t =
        ∫ t in (0:ℝ)..1, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv g) (fdBoundary_seg1_H H) ε t := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      show F t = _
      simp only [hF_def, cauchyPrincipalValueIntegrandOn]
      have hγ_eq : γ t = fdBoundary_seg1_H H t :=
        fdBoundary_H_eq_seg1_H ht.2
      rw [hγ_eq]
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · -- t = 1: γ(1) = ρ' ∈ S_arc, so both sides are 0
        have h_near : ∃ s ∈ S_arc,
            ‖fdBoundary_seg1_H H 1 - s‖ ≤ ε := by
          refine ⟨ellipticPoint_rho_plus_one,
            rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in, ?_⟩
          rw [show fdBoundary_seg1_H H 1 = ellipticPoint_rho_plus_one from by
            rw [← fdBoundary_H_eq_seg1_H (le_refl 1),
                (fdBoundary_H_at_one H).trans fdBoundary_at_one]
          ]
          rw [sub_self, norm_zero]; linarith
        simp [h_near]
      · -- t < 1: deriv γ = deriv seg1
        have h_deriv : deriv γ t = deriv (fdBoundary_seg1_H H) t := by
          have heq : γ =ᶠ[𝓝 t] fdBoundary_seg1_H H :=
            Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht1,
              fun s hs => fdBoundary_H_eq_seg1_H (le_of_lt hs)⟩
          exact Filter.EventuallyEq.deriv_eq heq
        rw [h_deriv]
    -- On [3,4]: CPV(γ) = CPV(seg4) a.e.
    have h_congr_34 : ∫ t in (3:ℝ)..4, F t =
        ∫ t in (3:ℝ)..4, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv g) (fdBoundary_seg4_H H) ε t := by
      apply intervalIntegral.integral_congr_ae
      rw [ae_iff]
      apply measure_mono_null (t := ({3, 4} : Set ℝ))
      · intro t ht
        simp only [Set.mem_setOf_eq, not_forall] at ht
        obtain ⟨ht_mem, h_ne⟩ := ht
        rw [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at ht_mem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        by_contra h_not_34
        push_neg at h_not_34
        obtain ⟨h_ne_3, h_ne_4⟩ := h_not_34
        have ht3 : 3 < t := ht_mem.1
        have ht4 : t < 4 := lt_of_le_of_ne ht_mem.2 h_ne_4
        apply h_ne
        show F t = _
        simp only [hF_def, cauchyPrincipalValueIntegrandOn]
        have hγ_eq : γ t = fdBoundary_seg4_H H t :=
          fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) (le_of_lt ht4)
        rw [hγ_eq]
        have heq : γ =ᶠ[𝓝 t] fdBoundary_seg4_H H :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4, Ioo_mem_nhds ht3 ht4,
            fun s hs => fdBoundary_H_eq_seg4_H (by linarith [hs.1])
              (by linarith [hs.1]) (by linarith [hs.1]) (le_of_lt hs.2)⟩
        rw [Filter.EventuallyEq.deriv_eq heq]
      · exact (Set.Finite.insert 3 (Set.finite_singleton (4:ℝ))).measure_zero _
    -- ---- Step 4: Vertical cancellation ----
    have h_cancel := cpv_truncated_vertical_cancel_H_of_Sarc f S_arc h_S_unit h_S_closed H ε hε_pos
    -- ---- Step 5: Algebra ----
    rw [h_05, h_congr_01, h_congr_34]
    linear_combination h_cancel
  -- Step 2: Arc CPV limit: ∫₁³ → -(2πik/12) as ε → 0
  have h_arc := arc_cpv_contribution_is_k_div_12_of_Sarc f S_arc h_S_unit h_S_closed
    h_rho_in H h_oncurve
  -- Step 3: Seg5 CPV limit: ∫₄⁵ → 2πi·orderAtCusp as ε → 0
  have h_seg5 : Tendsto (fun ε => ∫ t in (4:ℝ)..5,
      cauchyPrincipalValueIntegrandOn S_arc
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t)
      (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * ↑(orderAtCusp f))) := by
    set g := modularFormCompOfComplex f with hg_def
    set γ := fdBoundary_H H with hγ_def
    have hH_pos : 0 < H := by
      linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
    have h_γ_seg5 : ∀ t, 4 < t → γ t = fdBoundary_seg5_H H t :=
      fun t ht => fdBoundary_H_eq_seg5_H
        (by linarith) (by linarith) (by linarith) (by linarith)
    have h_deriv_one : ∀ t, 4 < t → deriv γ t = 1 :=
      fun t ht => (fdBoundary_H_hasDerivAt_seg5 H ht).deriv
    rw [show (2 * ↑Real.pi * I * ↑(orderAtCusp f) : ℂ) =
        ∫ t in (4:ℝ)..5, logDeriv g (fdBoundary_seg5_H H t) from
        (seg5_logDeriv_integral_eq_H f hf hH_pos hcusp_nonvan).symm]
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => ‖logDeriv g (fdBoundary_seg5_H H t)‖)
    · -- (C1) AEStronglyMeasurable for each ε
      apply Filter.Eventually.of_forall; intro ε
      have h_cont_g : ContinuousOn (logDeriv g) (γ '' Set.Icc 4 5) := by
        intro z ⟨t, ht, hz⟩; rw [← hz]
        have h_eq : γ t = fdBoundary_seg5_H H t := by
          rcases eq_or_lt_of_le ht.1 with rfl | h
          · simp only [hγ_def, fdBoundary_H_at_four, fdBoundary_seg5_H]; push_cast; ring
          · exact h_γ_seg5 t h
        rw [h_eq]
        exact (analyticAt_logDeriv_off_zeros f _
          (by rw [fdBoundary_seg5_H_im]; exact hH_pos)
          (modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan t)
          ).continuousAt.continuousWithinAt
      have h_cont_deriv : ContinuousOn (deriv γ) (Set.Icc 4 5 \ ↑({4} : Finset ℝ)) :=
        continuousOn_const.congr (fun s ⟨hs_icc, hs_4⟩ => by
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hs_4
          exact h_deriv_one s (lt_of_le_of_ne hs_icc.1 (Ne.symm hs_4)))
      have h_fun_eq : cauchyPrincipalValueIntegrandOn S_arc
          (logDeriv g) γ ε = fun t => if ∃ s ∈ S_arc,
          ‖γ t - ↑s‖ ≤ ε then 0 else logDeriv g (γ t) * deriv γ t := rfl
      rw [h_fun_eq, show (Ι (4:ℝ) 5) = Set.Ioc 4 5 from
        Set.uIoc_of_le (by norm_num)]
      have h_meas := aEStronglyMeasurable_pv_integrand_multipoint (ε := ε)
        S_arc h_cont_g
        ((fdBoundary_H_continuous H).continuousOn) (P := {4}) h_cont_deriv
      exact h_meas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    · -- (C2) Bound: ‖CPV integrand‖ ≤ ‖logDeriv g (seg5 t)‖ a.e.
      apply Filter.Eventually.of_forall; intro ε
      apply Filter.Eventually.of_forall; intro t; intro ht
      rw [Set.uIoc_of_le (show (4:ℝ) ≤ 5 by norm_num)] at ht
      unfold cauchyPrincipalValueIntegrandOn
      rw [h_γ_seg5 t ht.1, h_deriv_one t ht.1, mul_one]
      split_ifs with h_near
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_refl _
    · -- (C3) Bound integrable: ‖logDeriv g ∘ seg5‖ on [4,5]
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (show (4:ℝ) ≤ 5 by norm_num)]
      exact (continuousOn_logDeriv_seg5_H f hH hcusp_nonvan).norm.integrableOn_compact
        isCompact_Icc
    · -- (C4) Pointwise a.e. limit: CPV(ε,t) → logDeriv g (seg5 t)
      rw [ae_iff]
      apply measure_mono_null (t := (⋃ s ∈ (↑S_arc : Set ℂ),
        {t : ℝ | fdBoundary_seg5_H H t = s}))
      · -- Failure set ⊆ ⋃
        intro t ht; push_neg at ht; obtain ⟨ht_mem, ht_not⟩ := ht
        rw [Set.uIoc_of_le (show (4:ℝ) ≤ 5 by norm_num)] at ht_mem
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
        by_contra h_all_ne; push_neg at h_all_ne
        exact ht_not (by
          have h_not_near : ∀ s ∈ S_arc, fdBoundary_seg5_H H t ≠ (s : ℂ) :=
            fun s hs => h_all_ne s hs
          have ⟨δ, hδ_pos, hδ_le⟩ : ∃ δ > 0, ∀ s ∈ S_arc,
              δ ≤ ‖fdBoundary_seg5_H H t - s‖ := by
            rcases S_arc.eq_empty_or_nonempty with rfl | hne
            · exact ⟨1, one_pos, fun s hs => absurd hs (Finset.notMem_empty s)⟩
            · obtain ⟨s₀, hs₀, h_min⟩ := S_arc.exists_min_image
                  (fun s => ‖fdBoundary_seg5_H H t - s‖) hne
              exact ⟨‖fdBoundary_seg5_H H t - s₀‖,
                norm_pos_iff.mpr (sub_ne_zero.mpr (h_not_near s₀ hs₀)),
                h_min⟩
          apply tendsto_const_nhds.congr'
          filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
          rw [Set.mem_Ioo] at hε
          unfold cauchyPrincipalValueIntegrandOn
          rw [h_γ_seg5 t ht_mem.1, h_deriv_one t ht_mem.1, mul_one]
          rw [if_neg (show ¬∃ s ∈ S_arc, ‖fdBoundary_seg5_H H t - s‖ ≤ ε from by
            push_neg; intro s hs; exact lt_of_lt_of_le hε.2 (hδ_le s hs))])
      · -- Measure zero: finite union of subsingleton preimages
        exact (S_arc.finite_toSet.biUnion (fun s _ =>
            (seg5_preimage_subsingleton H s).finite)).measure_zero _
  -- Step 4: Combined Tendsto: (arc + seg5) → -(2πik/12) + 2πi·orderAtCusp
  have h_combined : Tendsto
      (fun ε => (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) +
        (∫ t in (4:ℝ)..5, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t))
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * (k : ℂ) / 12) +
        2 * ↑Real.pi * I * ↑(orderAtCusp f))) :=
    h_arc.add h_seg5
  -- Step 5: Algebra: arc_limit + seg5_limit = target
  have h_eq : -(2 * ↑Real.pi * I * (k : ℂ) / 12) +
      2 * ↑Real.pi * I * ↑(orderAtCusp f) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ↑(orderAtCusp f))) := by
    ring
  rw [h_eq] at h_combined
  -- Step 6: Transfer Tendsto via eventual equality, then extract limUnder
  exact (h_combined.congr' (h_split.mono (fun _ h => h.symm))).limUnder_eq

/-! ## Auto-Cusp Wrapper (Dynamic S_arc)

Existential version: choose H automatically from f ≠ 0.
The on-curve hypothesis `h_oncurve` is transferred between heights using the
H-independence of the arc segment. -/

include hf in
theorem modular_side_auto_cusp_generalizedPV_of_Sarc
    (S_arc : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (h_oncurve : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑S_arc : Set ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 S_arc =
          -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun {H'} hH' h_vert_nv => ?_⟩
  -- Arc is H-independent: transfer h_oncurve to H'
  have h_oncurve' : ∀ t ∈ Set.Ioo (1:ℝ) 3,
      modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
      fdBoundary_H H' t ∈ (↑S_arc : Set ℂ) := by
    intro t ht h_zero
    rw [fdBoundary_H_eq_arc ht.1 ht.2] at h_zero ⊢
    have := h_oncurve t ht
    rw [fdBoundary_H_eq_arc ht.1 ht.2] at this
    exact this h_zero
  rw [show orderAtCusp' f = orderAtCusp f from rfl]
  exact pv_integral_logDeriv_eq_modular_H_cpv_of_Sarc f hf S_arc h_S_unit h_S_closed h_rho_in
    (by linarith [hH₀_gt, hH']) h_oncurve' h_vert_nv
    (cusp_nonvanishing_seg5_q_radius_H_mono f hH' hH₀_nonvan)

/-! ## Dynamic Vertical Set Infrastructure (SarcSvert)

Removes `h_vert_nv` by adding a dynamic vertical singular set `S_vert`.
Points in `S_vert` must lie on Re = ±1/2 and come in pairs linked by ±1 shift.
The combined set `S_arc ∪ S_vert` is used for the CPV integral.
-/

omit f hf in
/-- The real part of seg1_H is always 1/2. -/
private lemma fdBoundary_seg1_H_re (H t : ℝ) :
    (fdBoundary_seg1_H H t).re = 1 / 2 := by
  simp [fdBoundary_seg1_H, add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, div_ofNat]

omit f hf in
/-- If Re(s) = -1/2, then ‖(seg1 t - 1) - s‖ ≤ ‖seg1 t - s‖.
    Both have the same Im-difference; the real-part gap shrinks from 1 to 0. -/
private lemma norm_sub_one_le_of_re_neg_half (H t : ℝ) (s : ℂ)
    (hs : s.re = -1 / 2) :
    ‖fdBoundary_seg1_H H t - 1 - s‖ ≤ ‖fdBoundary_seg1_H H t - s‖ := by
  have h_re := fdBoundary_seg1_H_re H t
  simp only [Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, sub_re, sub_im, one_re, one_im]
  rw [h_re, hs]; ring_nf; nlinarith

omit f hf in
/-- If Re(s) = 1/2, then ‖seg1 t - s‖ ≤ ‖(seg1 t - 1) - s‖.
    Both have the same Im-difference; the real-part gap shrinks from 1 to 0. -/
private lemma norm_le_sub_one_of_re_half (H t : ℝ) (s : ℂ)
    (hs : s.re = 1 / 2) :
    ‖fdBoundary_seg1_H H t - s‖ ≤ ‖fdBoundary_seg1_H H t - 1 - s‖ := by
  have h_re := fdBoundary_seg1_H_re H t
  simp only [Complex.norm_def]
  apply Real.sqrt_le_sqrt
  simp only [Complex.normSq_apply, sub_re, sub_im, one_re, one_im]
  rw [h_re, hs]; ring_nf; nlinarith

omit f hf in
/-- Vertical indicator symmetry for `S_arc ∪ S_vert`:
    `(∃ s ∈ S_arc ∪ S_vert, ‖seg1(t) - s‖ ≤ ε) ↔ (∃ s ∈ S_arc ∪ S_vert, ‖seg4(4-t) - s‖ ≤ ε)`.
    - S_arc points use `-1/s` witness (S-closure)
    - S_vert points use `s ± 1` witness (pairing) or self (norm inequality) -/
lemma vertical_indicator_symmetric_of_SarcSvert (S_arc S_vert : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_vert_re : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 ∨ (s : ℂ).re = -1/2)
    (h_vert_pair_left : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 → s - 1 ∈ S_vert)
    (h_vert_pair_right : ∀ s ∈ S_vert, (s : ℂ).re = -1/2 → s + 1 ∈ S_vert)
    (H t ε : ℝ) (ht : t ∈ Icc (0:ℝ) 1) :
    (∃ s ∈ S_arc ∪ S_vert, ‖fdBoundary_seg1_H H t - s‖ ≤ ε) ↔
    (∃ s ∈ S_arc ∪ S_vert, ‖fdBoundary_seg4_H H (4 - t) - s‖ ≤ ε) := by
  rw [seg4_eq_seg1_minus_one_H' H t ht]
  constructor
  · rintro ⟨s, hs, h_le⟩
    rcases Finset.mem_union.mp hs with hs_arc | hs_vert
    · -- S_arc: use -1/s witness (existing S-closure argument)
      exact ⟨-(1:ℂ)/s, Finset.mem_union_left _ (h_S_closed s hs_arc),
        by rwa [← dist_seg1_neg_inv_eq s (h_S_unit s hs_arc)]⟩
    · -- S_vert: case split on Re(s)
      rcases h_vert_re s hs_vert with h_re | h_re
      · -- Re(s) = 1/2: use s - 1 (pairing)
        exact ⟨s - 1, Finset.mem_union_right _ (h_vert_pair_left s hs_vert h_re),
          by rwa [show fdBoundary_seg1_H H t - 1 - (s - 1) =
            fdBoundary_seg1_H H t - s from by ring]⟩
      · -- Re(s) = -1/2: use s itself (norm decreases: gap shrinks from 1 to 0)
        exact ⟨s, Finset.mem_union_right _ hs_vert,
          le_trans (norm_sub_one_le_of_re_neg_half H t s (by linarith)) h_le⟩
  · rintro ⟨s, hs, h_le⟩
    rcases Finset.mem_union.mp hs with hs_arc | hs_vert
    · -- S_arc: use -1/s witness
      exact ⟨-(1:ℂ)/s, Finset.mem_union_left _ (h_S_closed s hs_arc), by
        rw [dist_seg1_neg_inv_eq (-(1:ℂ)/s) (norm_neg_inv_of_norm_one (h_S_unit s hs_arc)),
            neg_inv_involution (h_S_unit s hs_arc)]; exact h_le⟩
    · -- S_vert: case split on Re(s)
      rcases h_vert_re s hs_vert with h_re | h_re
      · -- Re(s) = 1/2: use s itself (norm decreases: gap shrinks from 1 to 0)
        exact ⟨s, Finset.mem_union_right _ hs_vert,
          le_trans (norm_le_sub_one_of_re_half H t s (by linarith)) h_le⟩
      · -- Re(s) = -1/2: use s + 1 (pairing)
        exact ⟨s + 1, Finset.mem_union_right _ (h_vert_pair_right s hs_vert h_re),
          by rwa [show fdBoundary_seg1_H H t - (s + 1) =
            fdBoundary_seg1_H H t - 1 - s from by ring]⟩

/-- Vertical cancel for `S_arc ∪ S_vert`: seg1 + seg4 integrals cancel for every ε > 0. -/
theorem cpv_truncated_vertical_cancel_H_of_SarcSvert (S_arc S_vert : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_vert_re : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 ∨ (s : ℂ).re = -1/2)
    (h_vert_pair_left : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 → s - 1 ∈ S_vert)
    (h_vert_pair_right : ∀ s ∈ S_vert, (s : ℂ).re = -1/2 → s + 1 ∈ S_vert)
    (H : ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∫ t in (0:ℝ)..1, cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg1_H H) ε t) +
    (∫ t in (3:ℝ)..4, cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert)
        (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε t) = 0 := by
  -- Periodicity
  have h_periodic : Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
    simp only [Nat.cast_one] at this; exact this
  have h_logDeriv_periodic : Function.Periodic (logDeriv (modularFormCompOfComplex f)) (1 : ℂ) :=
    logDeriv_periodic_of_periodic h_periodic
  -- Derivative relation
  have h_deriv_rel : ∀ s : ℝ, deriv (fdBoundary_seg4_H H) (4 - s) =
      -(deriv (fdBoundary_seg1_H H) s) := by
    intro s; rw [deriv_fdBoundary_seg4_H, deriv_fdBoundary_seg1_H]; ring
  -- Change of variables
  have h_cov := @intervalIntegral.integral_comp_sub_left ℂ _ _ 0 1
      (cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε) 4
  simp only [show (4:ℝ) - 1 = 3 from by norm_num,
      show (4:ℝ) - 0 = 4 from by norm_num] at h_cov
  rw [← h_cov]
  -- Pointwise: F₄(4-s) = -F₁(s) for s ∈ [[0,1]]
  have h_pw : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      (cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg4_H H) ε) (4 - s) =
      -(cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_seg1_H H) ε s) := by
    intro s hs
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hs
    have h_seg : fdBoundary_seg4_H H (4 - s) = fdBoundary_seg1_H H s - 1 :=
      seg4_eq_seg1_minus_one_H' H s hs
    have h_ind := vertical_indicator_symmetric_of_SarcSvert S_arc S_vert
      h_S_unit h_S_closed h_vert_re h_vert_pair_left h_vert_pair_right H s ε hs
    by_cases h_near : ∃ p ∈ S_arc ∪ S_vert, ‖fdBoundary_seg1_H H s - (p : ℂ)‖ ≤ ε
    · have h_near' : ∃ p ∈ S_arc ∪ S_vert,
          ‖fdBoundary_seg4_H H (4 - s) - (p : ℂ)‖ ≤ ε := h_ind.mp h_near
      show cauchyPrincipalValueIntegrandOn _ _ _ ε (4 - s) =
        -(cauchyPrincipalValueIntegrandOn _ _ _ ε s)
      rw [cauchyPrincipalValueIntegrandOn, if_pos h_near',
          cauchyPrincipalValueIntegrandOn, if_pos h_near]; simp
    · have h_far' : ¬∃ p ∈ S_arc ∪ S_vert,
          ‖fdBoundary_seg4_H H (4 - s) - (p : ℂ)‖ ≤ ε :=
        fun h_abs => h_near (h_ind.mpr h_abs)
      show cauchyPrincipalValueIntegrandOn _ _ _ ε (4 - s) =
        -(cauchyPrincipalValueIntegrandOn _ _ _ ε s)
      rw [cauchyPrincipalValueIntegrandOn, if_neg h_far',
          cauchyPrincipalValueIntegrandOn, if_neg h_near]
      rw [h_seg]
      have h_logD : logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H s - 1) =
          logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H s) := by
        have := h_logDeriv_periodic (fdBoundary_seg1_H H s - 1)
        simp only [sub_add_cancel] at this; exact this.symm
      rw [h_logD, h_deriv_rel]; ring
  rw [intervalIntegral.integral_congr h_pw]
  simp only [intervalIntegral.integral_neg]
  exact add_neg_eq_zero.mpr rfl

include f hf

omit f hf in
/-- On the arc `(1,3)`, the real part of `γ(t)` is strictly between -1/2 and 1/2. -/
private lemma arc_re_strictly_between (H : ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (1:ℝ) 3) :
    -1/2 < (fdBoundary_H H t).re ∧ (fdBoundary_H H t).re < 1/2 := by
  rw [fdBoundary_H_eq_arc ht.1 ht.2, Complex.exp_ofReal_mul_I_re]
  have hpi := Real.pi_pos
  have hθ_lo : Real.pi / 3 < Real.pi * (1 + t) / 6 := by nlinarith [ht.1]
  have hθ_hi : Real.pi * (1 + t) / 6 < 2 * Real.pi / 3 := by nlinarith [ht.2]
  have hθ_Icc : Real.pi * (1 + t) / 6 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
  have hpi3_Icc : Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith, by nlinarith⟩
  have h23_Icc : 2 * Real.pi / 3 ∈ Set.Icc 0 Real.pi :=
    ⟨by nlinarith, by nlinarith⟩
  constructor
  · have h1 := Real.strictAntiOn_cos hθ_Icc h23_Icc hθ_hi
    have h2 : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
      rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
          Real.cos_pi_sub, Real.cos_pi_div_three]; ring
    linarith
  · have h1 := Real.strictAntiOn_cos hpi3_Icc hθ_Icc hθ_lo
    rw [Real.cos_pi_div_three] at h1; linarith

omit f hf in
private lemma arc_ne_svert (H : ℝ) (S_arc : Finset ℂ)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (s : ℂ) (hs_re : s.re = 1/2 ∨ s.re = -1/2) (hs_not : s ∉ S_arc)
    (t : ℝ) (ht : t ∈ Set.Icc (1:ℝ) 3) :
    fdBoundary_H H t ≠ s := by
  intro h_eq
  rcases lt_or_eq_of_le ht.1 with ht1 | rfl
  · rcases lt_or_eq_of_le ht.2 with ht3 | rfl
    · have := arc_re_strictly_between H t ⟨ht1, ht3⟩
      rw [h_eq] at this
      rcases hs_re with h | h <;> linarith [this.1, this.2]
    · have h3 : fdBoundary_H H 3 = ellipticPoint_rho :=
        (fdBoundary_H_at_three H).trans fdBoundary_at_three
      rw [h3] at h_eq; exact hs_not (h_eq ▸ h_rho_in)
  · have h1 : fdBoundary_H H 1 = ellipticPoint_rho_plus_one :=
      (fdBoundary_H_at_one H).trans fdBoundary_at_one
    rw [h1] at h_eq
    exact hs_not (h_eq ▸ rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in)

omit f hf in
private lemma arc_min_dist_pos_of_svert (H : ℝ) (S_arc : Finset ℂ)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (s : ℂ) (hs_re : s.re = 1/2 ∨ s.re = -1/2) (hs_not : s ∉ S_arc) :
    ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖ := by
  have h_ne_s : ∀ t ∈ Set.Icc (1:ℝ) 3, fdBoundary_H H t ≠ s :=
    arc_ne_svert H S_arc h_S_closed h_rho_in s hs_re hs_not
  have h_cont : ContinuousOn (fun t => ‖fdBoundary_H H t - s‖) (Set.Icc 1 3) :=
    (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const)).continuousOn
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    (⟨1, le_refl _, by norm_num⟩ : (Set.Icc (1:ℝ) 3).Nonempty) h_cont
  exact ⟨‖fdBoundary_H H t₀ - s‖, norm_pos_iff.mpr (sub_ne_zero.mpr (h_ne_s t₀ ht₀)),
    fun t ht => ht₀_min ht⟩

omit f hf in
private lemma arc_svert_combined_dist (H : ℝ) (S_arc S_vert : Finset ℂ)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (h_vert_re : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 ∨ (s : ℂ).re = -1/2) :
    ∃ δ > 0, ∀ s ∈ S_vert, s ∉ S_arc →
      ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖ := by
  by_cases h_all_in : ∀ s ∈ S_vert, s ∈ S_arc
  · exact ⟨1, one_pos, fun s hs hs_not => absurd (h_all_in s hs) hs_not⟩
  · push_neg at h_all_in
    have h_each : ∀ s ∈ S_vert, s ∉ S_arc →
        ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖ :=
      fun s hs hs_not => arc_min_dist_pos_of_svert H S_arc h_S_closed h_rho_in s
        (h_vert_re s hs) hs_not
    -- Extract uniform δ by induction on an auxiliary Finset
    suffices key : ∀ (S : Finset ℂ),
        (∀ s ∈ S, s ∈ S_vert → s ∉ S_arc →
          ∃ δ > 0, ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖) →
        ∃ δ > 0, ∀ s ∈ S, s ∈ S_vert → s ∉ S_arc →
          ∀ t ∈ Set.Icc (1:ℝ) 3, δ ≤ ‖fdBoundary_H H t - s‖ by
      obtain ⟨δ, hδ_pos, hδ_bound⟩ := key S_vert (fun s hs _ => h_each s hs)
      exact ⟨δ, hδ_pos, fun s hs hs_not t ht => hδ_bound s hs hs hs_not t ht⟩
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨1, one_pos, fun s hs => absurd hs (Finset.not_mem_empty s)⟩
    | @insert a S' _ha ih =>
      intro h_all
      obtain ⟨δ₁, hδ₁_pos, hδ₁_bound⟩ := ih (fun s hs => h_all s (Finset.mem_insert_of_mem hs))
      by_cases ha_need : a ∈ S_vert ∧ a ∉ S_arc
      · obtain ⟨δ₂, hδ₂_pos, hδ₂_bound⟩ :=
          h_all a (Finset.mem_insert_self _ _) ha_need.1 ha_need.2
        exact ⟨min δ₁ δ₂, lt_min hδ₁_pos hδ₂_pos, fun s hs h_sv h_na t ht => by
          rcases Finset.mem_insert.mp hs with rfl | h
          · exact le_trans (min_le_right _ _) (hδ₂_bound t ht)
          · exact le_trans (min_le_left _ _) (hδ₁_bound s h h_sv h_na t ht)⟩
      · push_neg at ha_need
        exact ⟨δ₁, hδ₁_pos, fun s hs h_sv h_na t ht => by
          rcases Finset.mem_insert.mp hs with rfl | h
          · exact absurd (ha_need h_sv) h_na
          · exact hδ₁_bound s h h_sv h_na t ht⟩

omit f hf in
lemma arc_cpv_eventually_eq_of_SarcSvert (S_arc S_vert : Finset ℂ)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (h_vert_re : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 ∨ (s : ℂ).re = -1/2)
    (H : ℝ) (g : ℂ → ℂ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert)
          g (fdBoundary_H H) ε t =
      ∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn S_arc
          g (fdBoundary_H H) ε t := by
  obtain ⟨δ, hδ_pos, h_far⟩ := arc_svert_combined_dist H S_arc S_vert
    h_S_closed h_rho_in h_vert_re
  have h_Iio : Set.Iio δ ∈ 𝓝[>] (0:ℝ) := nhdsWithin_le_nhds (Iio_mem_nhds hδ_pos)
  filter_upwards [self_mem_nhdsWithin, h_Iio] with ε hε_pos hε_lt
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 3)] at ht
  show cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert) g (fdBoundary_H H) ε t =
    cauchyPrincipalValueIntegrandOn S_arc g (fdBoundary_H H) ε t
  have h_ind_eq : ∀ p ∈ S_vert, p ∉ S_arc → ε < ‖fdBoundary_H H t - p‖ := by
    intro p hp hp_not; exact lt_of_lt_of_le hε_lt (h_far p hp hp_not t ht)
  unfold cauchyPrincipalValueIntegrandOn
  by_cases h_sarc : ∃ s ∈ S_arc, ‖fdBoundary_H H t - s‖ ≤ ε
  · have h_union : ∃ s ∈ S_arc ∪ S_vert, ‖fdBoundary_H H t - s‖ ≤ ε := by
      obtain ⟨s, hs, hle⟩ := h_sarc; exact ⟨s, Finset.mem_union_left _ hs, hle⟩
    rw [if_pos h_union, if_pos h_sarc]
  · have h_no_union : ¬∃ s ∈ S_arc ∪ S_vert, ‖fdBoundary_H H t - s‖ ≤ ε := by
      rintro ⟨s, hs, hle⟩
      rcases Finset.mem_union.mp hs with h_arc | h_vert
      · exact h_sarc ⟨s, h_arc, hle⟩
      · by_cases hs_arc : s ∈ S_arc
        · exact h_sarc ⟨s, hs_arc, hle⟩
        · exact absurd hle (not_le.mpr (h_ind_eq s h_vert hs_arc))
    rw [if_neg h_no_union, if_neg h_sarc]

/-! ## Main CPV Modular-Side Theorem with `S_arc ∪ S_vert` (no `h_vert_nv`)

Removes the `h_vert_nv` (vertical nonvanishing) hypothesis by using a dynamic
vertical singular set `S_vert`. Points in `S_vert` lie on Re = ±1/2 and are
paired via ±1 shifts. The CPV integral cuts out balls around `S_arc ∪ S_vert`,
so zeros of `f` on the vertical segments are properly regularized.

Key changes from `pv_integral_logDeriv_eq_modular_H_cpv_of_Sarc`:
- No `h_vert_nv`: replaced by `h_oncurve_vert` (on-curve capture for verticals)
- Vertical cancel: uses `cpv_truncated_vertical_cancel_H_of_SarcSvert`
- Arc integral: reduces to `S_arc` via `arc_cpv_eventually_eq_of_SarcSvert`
- Integrability on verticals: K'/K argument with on-curve capture contradiction -/

set_option maxHeartbeats 1600000 in
include hf in
theorem pv_integral_logDeriv_eq_modular_H_cpv_of_SarcSvert
    (S_arc S_vert : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (h_vert_re : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 ∨ (s : ℂ).re = -1/2)
    (h_vert_pair_left : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 → s - 1 ∈ S_vert)
    (h_vert_pair_right : ∀ s ∈ S_vert, (s : ℂ).re = -1/2 → s + 1 ∈ S_vert)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H)
    (h_oncurve_arc : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑S_arc : Set ℂ))
    (h_oncurve_vert : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        (fdBoundary_H H t : ℂ) ∈ (↑S_vert : Set ℂ))
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc ∪ S_vert) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp f : ℂ))) := by
  unfold pv_integral_logDeriv cauchyPrincipalValueOn
  haveI : (𝓝[>] (0:ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  -- Step 1: ∀ᶠ ε, ∫₀⁵(S₀) = ∫₁³(S₀) + ∫₄⁵(S₀), by splitting + vertical cancel
  have h_split : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ t in (0:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (S_arc ∪ S_vert) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t =
      (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
          (S_arc ∪ S_vert) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) +
      (∫ t in (4:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (S_arc ∪ S_vert) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : 0 < ε := hε
    set g := modularFormCompOfComplex f with hg_def
    set γ := fdBoundary_H H with hγ_def
    set S₀ := (S_arc ∪ S_vert : Finset ℂ)
    set F := fun t => cauchyPrincipalValueIntegrandOn
        S₀ (logDeriv g) γ ε t with hF_def
    -- ---- Integrability on each sub-interval ----
    -- [1,3]: K'/K (same as _of_Sarc but with S₀)
    have hint_13 : IntervalIntegrable F volume 1 3 := by
      set K' := {t ∈ Set.Icc (1:ℝ) 3 | ∀ s ∈ S₀, ε ≤ ‖γ t - (s : ℂ)‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        apply IsClosed.inter isClosed_Icc
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        convert this using 1; ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have h_cont : ContinuousOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        intro t ⟨⟨ht1, ht3⟩, h_far⟩
        have ht_not_1 : t ≠ 1 := by
          intro h_eq; subst h_eq
          have h_rho'_in := Finset.mem_union_left S_vert
            (rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in)
          have h1 := h_far _ h_rho'_in
          rw [show γ 1 = ellipticPoint_rho_plus_one from
            (fdBoundary_H_at_one H).trans fdBoundary_at_one, sub_self, norm_zero] at h1
          linarith
        have ht_not_3 : t ≠ 3 := by
          intro h_eq; subst h_eq
          have h3 := h_far _ (Finset.mem_union_left S_vert h_rho_in)
          rw [show γ 3 = ellipticPoint_rho from
            (fdBoundary_H_at_three H).trans fdBoundary_at_three, sub_self, norm_zero] at h3
          linarith
        have ht_ioo : t ∈ Set.Ioo (1:ℝ) 3 :=
          ⟨lt_of_le_of_ne ht1 (Ne.symm ht_not_1), lt_of_le_of_ne ht3 ht_not_3⟩
        have h_ne : g (γ t) ≠ 0 := by
          intro h_zero
          have h_in_S := h_oncurve_arc t ht_ioo h_zero
          rw [Finset.mem_coe] at h_in_S
          have h_dist := h_far _ (Finset.mem_union_left S_vert h_in_S)
          simp only [hγ_def] at h_dist; rw [sub_self, norm_zero] at h_dist; linarith
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.mul
        · apply ContinuousAt.comp
          · have h_im : 0 < (γ t).im := by
              rw [show γ t = _ from fdBoundary_H_eq_arc ht_ioo.1 ht_ioo.2,
                  Complex.exp_ofReal_mul_I_im]
              exact Real.sin_pos_of_pos_of_lt_pi
                (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
            exact (analyticAt_logDeriv_off_zeros f (γ t) h_im h_ne).continuousAt
          · exact (fdBoundary_H_continuous H).continuousAt
        · have h_deriv_eq : deriv γ =ᶠ[𝓝 t] fun s => ↑(Real.pi / 6) * I * γ s := by
            filter_upwards [Ioo_mem_nhds ht_ioo.1 ht_ioo.2] with s hs
            rw [show γ s = _ from fdBoundary_H_eq_arc hs.1 hs.2]
            exact (fdBoundary_H_hasDerivAt_arc H hs.1 hs.2).deriv
          exact (ContinuousAt.mul (ContinuousAt.mul continuousAt_const continuousAt_const)
            (fdBoundary_H_continuous H).continuousAt).congr h_deriv_eq.symm
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' :=
        ContinuousOn.integrableOn_compact hK'_compact h_cont
      set K := {t ∈ Set.uIoc (1:ℝ) 3 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 1 3 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter; apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]
          exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (h_int.mono_set hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (1:ℝ) 3 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (1:ℝ) 3 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm
          (measurableSet_uIoc.diff hK_meas)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (1:ℝ) ≤ 3)]
      have := h_int_K.union h_int_compl
      rwa [Set.union_diff_cancel (fun t ht => ht.1),
           Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 3)] at this
    -- [0,1]: K'/K with on-curve capture (replaces h_vert_nv)
    have hint_01 : IntervalIntegrable F volume 0 1 := by
      set K' := {t ∈ Set.Icc (0:ℝ) 1 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        apply IsClosed.inter isClosed_Icc
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        convert this using 1; ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have h_cont : ContinuousOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        intro t ⟨⟨ht0, ht1⟩, h_far⟩
        have ht_ne_1 : t ≠ 1 := by
          intro h_eq; subst h_eq
          have := h_far _ (Finset.mem_union_left S_vert
            (rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in))
          have h_at_1 : γ 1 = ellipticPoint_rho_plus_one :=
            hγ_def ▸ (fdBoundary_H_at_one H).trans fdBoundary_at_one
          rw [h_at_1, sub_self, norm_zero] at this; linarith
        have ht_ioo : t ∈ Set.Ioo (0:ℝ) 1 ∨ t = 0 := by
          rcases eq_or_lt_of_le ht0 with rfl | h
          · right; rfl
          · left; exact ⟨h, lt_of_le_of_ne ht1 ht_ne_1⟩
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.mul
        · apply ContinuousAt.comp
          · have h_im : 0 < (γ t).im := by
              rw [show γ t = fdBoundary_seg1_H H t from
                fdBoundary_H_eq_seg1_H (le_of_lt (lt_of_le_of_ne ht1 ht_ne_1))]
              have him : (fdBoundary_seg1_H H t).im = H - t * (H - Real.sqrt 3 / 2) := by
                simp [fdBoundary_seg1_H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
                  div_ofNat]
              rw [him]
              nlinarith [hH, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
            -- KEY CHANGE: on-curve capture replaces h_vert_nv
            have h_ne : g (γ t) ≠ 0 := by
              rcases ht_ioo with h | rfl
              · -- t ∈ (0,1): if g(γ t) = 0 then γ t ∈ S_vert ⊆ S₀, contradicting K'
                intro h_zero
                have h_in := h_oncurve_vert t h h_zero
                have h_mem : γ t ∈ S₀ :=
                  Finset.mem_union_right _ (Finset.mem_coe.mp h_in)
                have := h_far _ h_mem; rw [sub_self, norm_zero] at this; linarith
              · rw [show γ 0 = fdBoundary_seg5_H H 5 from by
                  rw [hγ_def, fdBoundary_H_at_zero]; simp [fdBoundary_seg5_H]; push_cast; ring]
                exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 5
            exact (analyticAt_logDeriv_off_zeros f _ h_im h_ne).continuousAt
          · exact (fdBoundary_H_continuous H).continuousAt
        · have ht_lt_1 : t < 1 := lt_of_le_of_ne ht1 ht_ne_1
          have h_deriv_eq : deriv γ =ᶠ[𝓝 t] fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I := by
            filter_upwards [Iio_mem_nhds ht_lt_1] with s hs
            exact (fdBoundary_H_hasDerivAt_seg1 H hs).deriv
          exact continuousAt_const.congr h_deriv_eq.symm
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' :=
        ContinuousOn.integrableOn_compact hK'_compact h_cont
      set K := {t ∈ Set.uIoc (0:ℝ) 1 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 0 1 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter; apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]
          exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (h_int.mono_set hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (0:ℝ) 1 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (0:ℝ) 1 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm
          (measurableSet_uIoc.diff hK_meas)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      have := h_int_K.union h_int_compl
      rwa [Set.union_diff_cancel (fun t ht => ht.1),
           Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at this
    -- [3,4]: K'/K with on-curve capture + periodicity + pairing
    have hint_34 : IntervalIntegrable F volume 3 4 := by
      set K' := {t ∈ Set.Icc (3:ℝ) 4 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        apply IsClosed.inter isClosed_Icc
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        convert this using 1; ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have h_cont_logDeriv : ContinuousOn (fun t => logDeriv g (γ t)) K' := by
        intro t ⟨⟨ht3, ht4⟩, h_far⟩
        have ht_ne_3 : t ≠ 3 := by
          intro h_eq; subst h_eq
          have h3 := h_far _ (Finset.mem_union_left S_vert h_rho_in)
          have h_at_3 : γ 3 = ellipticPoint_rho :=
            hγ_def ▸ (fdBoundary_H_at_three H).trans fdBoundary_at_three
          rw [h_at_3, sub_self, norm_zero] at h3; linarith
        have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm ht_ne_3)
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.comp
        · have h_eq_seg4 : γ t = fdBoundary_seg4_H H t :=
            fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) ht4
          have h_im : 0 < (γ t).im := by
            rw [h_eq_seg4]
            have him : (fdBoundary_seg4_H H t).im =
                Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
              simp [fdBoundary_seg4_H, add_im, neg_im, mul_im, I_re, I_im, ofReal_re,
                ofReal_im, div_ofNat]
            rw [him]
            nlinarith [hH, Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
          -- KEY CHANGE: on-curve capture + periodicity + pairing replaces h_vert_nv
          have h_ne : g (γ t) ≠ 0 := by
            intro h_zero
            by_cases ht4' : t < 4
            · -- t ∈ (3,4): γ(t) = seg4(t) = seg1(4-t) - 1
              rw [h_eq_seg4] at h_zero
              have h_4mt : 4 - t ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith, by linarith⟩
              have h_s := seg4_eq_seg1_minus_one_H' H (4 - t) (by constructor <;> linarith)
              rw [show 4 - (4 - t) = t from by ring] at h_s
              rw [h_s] at h_zero
              -- g(seg1(4-t) - 1) = g(seg1(4-t)) by periodicity
              have h_periodic' : Function.Periodic g (1 : ℂ) := by
                have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
                simp only [Nat.cast_one] at this; exact this
              have h_per := h_periodic' (fdBoundary_seg1_H H (4 - t) - 1)
              simp only [sub_add_cancel] at h_per
              -- g(seg1(4-t)) = 0
              have h_zero_seg1 : g (fdBoundary_seg1_H H (4 - t)) = 0 := h_per ▸ h_zero
              -- seg1(4-t) ∈ S_vert (on-curve capture)
              have h_eq_seg1 : γ (4 - t) = fdBoundary_seg1_H H (4 - t) :=
                hγ_def ▸ fdBoundary_H_eq_seg1_H (le_of_lt h_4mt.2)
              have h_in_sv := h_oncurve_vert (4 - t) h_4mt (by
                rw [h_eq_seg1]; exact h_zero_seg1)
              -- seg1(4-t) has Re = 1/2, so seg1(4-t) - 1 ∈ S_vert (pairing)
              have h_re : (γ (4 - t)).re = 1 / 2 := by
                rw [h_eq_seg1]; exact fdBoundary_seg1_H_re H (4 - t)
              have h_mem_sv := h_vert_pair_left _ (Finset.mem_coe.mp h_in_sv) h_re
              -- γ(t) = seg1(4-t) - 1 ∈ S_vert ⊆ S₀
              have h_mem_S₀ : γ t ∈ S₀ := by
                have h_eq_t : γ t = fdBoundary_seg1_H H (4 - t) - 1 := h_eq_seg4.trans h_s
                rw [h_eq_t, ← fdBoundary_H_eq_seg1_H (le_of_lt h_4mt.2)]
                exact Finset.mem_union_right _ h_mem_sv
              have := h_far _ h_mem_S₀; rw [sub_self, norm_zero] at this; linarith
            · -- t = 4: use cusp nonvanishing
              push_neg at ht4'; have := le_antisymm ht4 ht4'; subst this
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring
              ] at h_zero
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 4 h_zero
          exact (analyticAt_logDeriv_off_zeros f _ h_im h_ne).continuousAt
        · exact (fdBoundary_H_continuous H).continuousAt
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        have h_nice_int : MeasureTheory.IntegrableOn
            (fun t => logDeriv g (γ t) * ((↑(H - Real.sqrt 3 / 2) : ℂ) * I)) K' :=
          (h_cont_logDeriv.mul continuousOn_const).integrableOn_compact hK'_compact
        exact h_nice_int.congr (by
          have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
          have h_null : volume ({3, 4} : Set ℝ) = 0 :=
            measure_union_null Real.volume_singleton Real.volume_singleton
          filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr h_null),
            ae_restrict_mem hK'_meas] with t ht_compl ht_K'
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
            not_or] at ht_compl
          congr 1; rw [hγ_def]
          exact (fdBoundary_H_hasDerivAt_seg4 H
            (lt_of_le_of_ne ht_K'.1.1 (Ne.symm ht_compl.1))
            (lt_of_le_of_ne ht_K'.1.2 ht_compl.2)).deriv.symm)
      set K := {t ∈ Set.uIoc (3:ℝ) 4 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 3 4 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter; apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]
          exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (h_int.mono_set hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (3:ℝ) 4 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (3:ℝ) 4 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm
          (measurableSet_uIoc.diff hK_meas)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (3:ℝ) ≤ 4)]
      have := h_int_K.union h_int_compl
      rwa [Set.union_diff_cancel (fun t ht => ht.1),
           Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at this
    -- [4,5]: K'/K (same structure, cusp nonvanishing on seg5)
    have hint_45 : IntervalIntegrable F volume 4 5 := by
      set K' := {t ∈ Set.Icc (4:ℝ) 5 | ∀ s ∈ S₀, ε ≤ ‖γ t - s‖}
      have hK'_compact : IsCompact K' := by
        refine IsCompact.of_isClosed_subset isCompact_Icc ?_ (fun _t ⟨ht, _⟩ => ht)
        apply IsClosed.inter isClosed_Icc
        have : IsClosed (⋂ (s : ℂ) (_ : s ∈ S₀), {t : ℝ | ε ≤ ‖γ t - s‖}) :=
          isClosed_iInter fun s => isClosed_iInter fun _ =>
            isClosed_le continuous_const
              (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
        convert this using 1; ext t; simp only [Set.mem_iInter, Set.mem_setOf]; exact Iff.rfl
      have hH_pos : 0 < H := by
        linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
      have h_cont_logDeriv : ContinuousOn (fun t => logDeriv g (γ t)) K' := by
        intro t ⟨⟨ht4, ht5⟩, _⟩
        apply ContinuousAt.continuousWithinAt
        apply ContinuousAt.comp
        · rcases eq_or_lt_of_le ht4 with rfl | ht4'
          · exact (analyticAt_logDeriv_off_zeros f _ (by
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              rw [fdBoundary_seg5_H_im]; exact hH_pos) (by
              rw [show γ 4 = fdBoundary_seg5_H H 4 from by
                rw [hγ_def, fdBoundary_H_at_four]; simp [fdBoundary_seg5_H]; push_cast; ring]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan 4)).continuousAt
          · exact (analyticAt_logDeriv_off_zeros f _ (by
              rw [show γ t = fdBoundary_seg5_H H t from hγ_def ▸
                fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith),
                fdBoundary_seg5_H_im]; exact hH_pos) (by
              rw [show γ t = fdBoundary_seg5_H H t from hγ_def ▸
                fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)]
              exact modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan t)).continuousAt
        · exact (fdBoundary_H_continuous H).continuousAt
      have h_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t) * deriv γ t) K' := by
        have h_nice_int : MeasureTheory.IntegrableOn (fun t => logDeriv g (γ t)) K' :=
          h_cont_logDeriv.integrableOn_compact hK'_compact
        have h_ae : (fun t => logDeriv g (γ t)) =ᵐ[volume.restrict K']
            (fun t => logDeriv g (γ t) * deriv γ t) := by
          have hK'_meas : MeasurableSet K' := hK'_compact.isClosed.measurableSet
          filter_upwards [ae_restrict_of_ae (compl_mem_ae_iff.mpr
            (Real.volume_singleton : volume ({4} : Set ℝ) = 0)),
            ae_restrict_mem hK'_meas] with t ht_ne4 ht_K'
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht_ne4
          rw [(fdBoundary_H_hasDerivAt_seg5 H
            (lt_of_le_of_ne ht_K'.1.1 (Ne.symm ht_ne4))).deriv, mul_one]
        exact h_nice_int.congr h_ae
      set K := {t ∈ Set.uIoc (4:ℝ) 5 | ¬∃ s ∈ S₀, ‖γ t - s‖ ≤ ε}
      have hK_subset_K' : K ⊆ K' := by
        intro t ⟨ht_uioc, h_not_near⟩
        have ht_Ioc : t ∈ Set.Ioc 4 5 := by rwa [Set.uIoc_of_le (by norm_num)] at ht_uioc
        refine ⟨⟨le_of_lt ht_Ioc.1, ht_Ioc.2⟩, fun s hs => ?_⟩
        by_contra h_contra; push_neg at h_contra
        exact h_not_near ⟨s, hs, h_contra.le⟩
      have hK_meas : MeasurableSet K := by
        apply measurableSet_uIoc.inter; apply MeasurableSet.compl
        suffices h : IsClosed (⋃ s ∈ (↑S₀ : Set ℂ), {t : ℝ | ‖γ t - s‖ ≤ ε}) by
          have hm := h.measurableSet
          convert hm using 1
          ext t; simp only [Set.mem_iUnion, Set.mem_setOf, Finset.mem_coe, exists_prop]
          exact Iff.rfl
        exact S₀.finite_toSet.isClosed_biUnion fun s _ =>
          isClosed_le (continuous_norm.comp ((fdBoundary_H_continuous H).sub continuous_const))
            continuous_const
      have hF_K : Set.EqOn F (fun t => logDeriv g (γ t) * deriv γ t) K := by
        intro t ⟨_, h_not_near⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = _
        rw [cauchyPrincipalValueIntegrandOn, if_neg h_not_near]
      have h_int_K : MeasureTheory.IntegrableOn F K :=
        (h_int.mono_set hK_subset_K').congr_fun hF_K.symm hK_meas
      have h_compl_zero : Set.EqOn F 0 (Set.uIoc (4:ℝ) 5 \ K) := by
        intro t ⟨ht_uioc, h_not_K⟩
        show cauchyPrincipalValueIntegrandOn S₀ (logDeriv g) γ ε t = 0
        rw [cauchyPrincipalValueIntegrandOn]
        have h_near : ∃ s ∈ S₀, ‖γ t - s‖ ≤ ε := by
          by_contra h_far; exact h_not_K ⟨ht_uioc, h_far⟩
        exact if_pos h_near
      have h_int_compl : MeasureTheory.IntegrableOn F (Set.uIoc (4:ℝ) 5 \ K) :=
        MeasureTheory.integrableOn_zero.congr_fun h_compl_zero.symm
          (measurableSet_uIoc.diff hK_meas)
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (4:ℝ) ≤ 5)]
      have := h_int_K.union h_int_compl
      rwa [Set.union_diff_cancel (fun t ht => ht.1),
           Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)] at this
    -- ---- Split ∫₀⁵ = ∫₀¹ + ∫₁³ + ∫₃⁴ + ∫₄⁵ ----
    have h_05 : (∫ t in (0:ℝ)..5, F t) =
        (∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t) +
        (∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t) := by
      rw [show (∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t) +
          (∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t) =
        ((∫ t in (0:ℝ)..1, F t) + (∫ t in (1:ℝ)..3, F t)) +
          ((∫ t in (3:ℝ)..4, F t) + (∫ t in (4:ℝ)..5, F t)) from by ring]
      rw [intervalIntegral.integral_add_adjacent_intervals hint_01 hint_13,
          intervalIntegral.integral_add_adjacent_intervals hint_34 hint_45,
          intervalIntegral.integral_add_adjacent_intervals
            (hint_01.trans hint_13) (hint_34.trans hint_45)]
    -- ---- Congr: CPV(γ) → CPV(seg1/seg4) on verticals ----
    have h_congr_01 : ∫ t in (0:ℝ)..1, F t =
        ∫ t in (0:ℝ)..1, cauchyPrincipalValueIntegrandOn
          S₀ (logDeriv g) (fdBoundary_seg1_H H) ε t := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall; intro t ht
      rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
      show F t = _; simp only [hF_def, cauchyPrincipalValueIntegrandOn]
      have hγ_eq : γ t = fdBoundary_seg1_H H t := fdBoundary_H_eq_seg1_H ht.2
      rw [hγ_eq]
      rcases eq_or_lt_of_le ht.2 with rfl | ht1
      · have h_near : ∃ s ∈ S₀, ‖fdBoundary_seg1_H H 1 - s‖ ≤ ε := by
          refine ⟨ellipticPoint_rho_plus_one,
            Finset.mem_union_left _ (rho_plus_one_in_Sarc S_arc h_S_closed h_rho_in), ?_⟩
          rw [show fdBoundary_seg1_H H 1 = ellipticPoint_rho_plus_one from by
            rw [← fdBoundary_H_eq_seg1_H (le_refl 1),
                (fdBoundary_H_at_one H).trans fdBoundary_at_one], sub_self, norm_zero]
          linarith
        simp [h_near]
      · have h_deriv : deriv γ t = deriv (fdBoundary_seg1_H H) t := by
          have heq : γ =ᶠ[𝓝 t] fdBoundary_seg1_H H :=
            Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Iio 1, Iio_mem_nhds ht1,
              fun s hs => fdBoundary_H_eq_seg1_H (le_of_lt hs)⟩
          exact Filter.EventuallyEq.deriv_eq heq
        rw [h_deriv]
    have h_congr_34 : ∫ t in (3:ℝ)..4, F t =
        ∫ t in (3:ℝ)..4, cauchyPrincipalValueIntegrandOn
          S₀ (logDeriv g) (fdBoundary_seg4_H H) ε t := by
      apply intervalIntegral.integral_congr_ae; rw [ae_iff]
      apply measure_mono_null (t := ({3, 4} : Set ℝ))
      · intro t ht; simp only [Set.mem_setOf_eq, not_forall] at ht
        obtain ⟨ht_mem, h_ne⟩ := ht
        rw [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)] at ht_mem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        by_contra h_not_34; push_neg at h_not_34
        apply h_ne; show F t = _
        simp only [hF_def, cauchyPrincipalValueIntegrandOn]
        have ht3 : 3 < t := ht_mem.1
        have ht4 : t < 4 := lt_of_le_of_ne ht_mem.2 h_not_34.2
        have hγ_eq : γ t = fdBoundary_seg4_H H t :=
          fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) (le_of_lt ht4)
        rw [hγ_eq]
        have heq : γ =ᶠ[𝓝 t] fdBoundary_seg4_H H :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Set.Ioo 3 4, Ioo_mem_nhds ht3 ht4,
            fun s hs => fdBoundary_H_eq_seg4_H (by linarith [hs.1])
              (by linarith [hs.1]) (by linarith [hs.1]) (le_of_lt hs.2)⟩
        rw [Filter.EventuallyEq.deriv_eq heq]
      · exact (Set.Finite.insert 3 (Set.finite_singleton (4:ℝ))).measure_zero _
    -- ---- Vertical cancel ----
    have h_cancel := cpv_truncated_vertical_cancel_H_of_SarcSvert f S_arc S_vert
      h_S_unit h_S_closed h_vert_re h_vert_pair_left h_vert_pair_right H ε hε_pos
    -- ---- Algebra: ∫₀⁵ = ∫₁³ + ∫₄⁵ ----
    rw [h_05, h_congr_01, h_congr_34]; linear_combination h_cancel
  -- Step 2: Arc CPV eventual equality: ∫₁³(S₀) = ∫₁³(S_arc)
  have h_arc_eq := arc_cpv_eventually_eq_of_SarcSvert S_arc S_vert h_S_closed h_rho_in
    h_vert_re H (logDeriv (modularFormCompOfComplex f))
  -- Step 3: Combined eventual equality
  have h_evt : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∫ t in (0:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (S_arc ∪ S_vert) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t =
      (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn S_arc
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) +
      (∫ t in (4:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (S_arc ∪ S_vert) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) := by
    filter_upwards [h_split, h_arc_eq] with ε h_sp h_ae
    calc _ = _ := h_sp
      _ = _ := by rw [h_ae]
  -- Step 4: Arc CPV limit
  have h_arc := arc_cpv_contribution_is_k_div_12_of_Sarc f S_arc h_S_unit h_S_closed
    h_rho_in H h_oncurve_arc
  -- Step 5: Seg5 CPV limit (adapted for S₀ = S_arc ∪ S_vert)
  have h_seg5 : Tendsto (fun ε => ∫ t in (4:ℝ)..5,
      cauchyPrincipalValueIntegrandOn (S_arc ∪ S_vert)
          (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t)
      (𝓝[>] 0) (𝓝 (2 * ↑Real.pi * I * ↑(orderAtCusp f))) := by
    set g := modularFormCompOfComplex f with hg_def
    set γ := fdBoundary_H H with hγ_def
    set S₀ := (S_arc ∪ S_vert : Finset ℂ)
    have hH_pos : 0 < H := by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
    have h_γ_seg5 : ∀ t, 4 < t → γ t = fdBoundary_seg5_H H t :=
      fun t ht => fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)
    have h_deriv_one : ∀ t, 4 < t → deriv γ t = 1 :=
      fun t ht => (fdBoundary_H_hasDerivAt_seg5 H ht).deriv
    rw [show (2 * ↑Real.pi * I * ↑(orderAtCusp f) : ℂ) =
        ∫ t in (4:ℝ)..5, logDeriv g (fdBoundary_seg5_H H t) from
        (seg5_logDeriv_integral_eq_H f hf hH_pos hcusp_nonvan).symm]
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
        (fun t => ‖logDeriv g (fdBoundary_seg5_H H t)‖)
    · -- (C1) AEStronglyMeasurable for each ε
      apply Filter.Eventually.of_forall; intro ε
      have h_cont_g : ContinuousOn (logDeriv g) (γ '' Set.Icc 4 5) := by
        intro z ⟨t, ht, hz⟩; rw [← hz]
        have h_eq : γ t = fdBoundary_seg5_H H t := by
          rcases eq_or_lt_of_le ht.1 with rfl | h
          · simp only [hγ_def, fdBoundary_H_at_four, fdBoundary_seg5_H]; push_cast; ring
          · exact h_γ_seg5 t h
        rw [h_eq]
        exact (analyticAt_logDeriv_off_zeros f _
          (by rw [fdBoundary_seg5_H_im]; exact hH_pos)
          (modularFormCompOfComplex_ne_zero_seg5_H f hH hcusp_nonvan t)
          ).continuousAt.continuousWithinAt
      have h_cont_deriv : ContinuousOn (deriv γ) (Set.Icc 4 5 \ ↑({4} : Finset ℝ)) :=
        continuousOn_const.congr (fun s ⟨hs_icc, hs_4⟩ => by
          simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hs_4
          exact h_deriv_one s (lt_of_le_of_ne hs_icc.1 (Ne.symm hs_4)))
      have h_fun_eq : cauchyPrincipalValueIntegrandOn S₀
          (logDeriv g) γ ε = fun t => if ∃ s ∈ S₀,
          ‖γ t - ↑s‖ ≤ ε then 0 else logDeriv g (γ t) * deriv γ t := rfl
      rw [h_fun_eq, show (Ι (4:ℝ) 5) = Set.Ioc 4 5 from Set.uIoc_of_le (by norm_num)]
      have h_meas := aEStronglyMeasurable_pv_integrand_multipoint (ε := ε)
        S₀ h_cont_g ((fdBoundary_H_continuous H).continuousOn) (P := {4}) h_cont_deriv
      exact h_meas.mono_measure (Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    · -- (C2) Bound: ‖CPV integrand‖ ≤ ‖logDeriv g (seg5 t)‖ a.e.
      apply Filter.Eventually.of_forall; intro ε
      apply Filter.Eventually.of_forall; intro t; intro ht
      rw [Set.uIoc_of_le (show (4:ℝ) ≤ 5 by norm_num)] at ht
      unfold cauchyPrincipalValueIntegrandOn
      rw [h_γ_seg5 t ht.1, h_deriv_one t ht.1, mul_one]
      split_ifs with h_near
      · rw [norm_zero]; exact norm_nonneg _
      · exact le_refl _
    · -- (C3) Bound integrable
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le (show (4:ℝ) ≤ 5 by norm_num)]
      exact (continuousOn_logDeriv_seg5_H f hH hcusp_nonvan).norm.integrableOn_compact
        isCompact_Icc
    · -- (C4) Pointwise a.e. limit: CPV(ε,t) → logDeriv g (seg5 t)
      rw [ae_iff]
      apply measure_mono_null (t := (⋃ s ∈ (↑S₀ : Set ℂ),
        {t : ℝ | fdBoundary_seg5_H H t = s}))
      · intro t ht; push_neg at ht; obtain ⟨ht_mem, ht_not⟩ := ht
        rw [Set.uIoc_of_le (show (4:ℝ) ≤ 5 by norm_num)] at ht_mem
        simp only [Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe]
        by_contra h_all_ne; push_neg at h_all_ne
        exact ht_not (by
          have h_not_near : ∀ s ∈ S₀, fdBoundary_seg5_H H t ≠ (s : ℂ) :=
            fun s hs => h_all_ne s hs
          have ⟨δ, hδ_pos, hδ_le⟩ : ∃ δ > 0, ∀ s ∈ S₀, δ ≤ ‖fdBoundary_seg5_H H t - s‖ := by
            rcases S₀.eq_empty_or_nonempty with h_empty | hne
            · exact ⟨1, one_pos, fun s hs => absurd (h_empty ▸ hs) (Finset.not_mem_empty s)⟩
            · obtain ⟨s₀, hs₀, h_min⟩ := S₀.exists_min_image
                  (fun s => ‖fdBoundary_seg5_H H t - s‖) hne
              exact ⟨‖fdBoundary_seg5_H H t - s₀‖,
                norm_pos_iff.mpr (sub_ne_zero.mpr (h_not_near s₀ hs₀)), h_min⟩
          apply tendsto_const_nhds.congr'
          filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
          rw [Set.mem_Ioo] at hε
          unfold cauchyPrincipalValueIntegrandOn
          rw [h_γ_seg5 t ht_mem.1, h_deriv_one t ht_mem.1, mul_one]
          rw [if_neg (show ¬∃ s ∈ S₀, ‖fdBoundary_seg5_H H t - s‖ ≤ ε from by
            push_neg; intro s hs; exact lt_of_lt_of_le hε.2 (hδ_le s hs))])
      · exact (S₀.finite_toSet.biUnion (fun s _ =>
            (seg5_preimage_subsingleton H s).finite)).measure_zero _
  -- Step 6: Combined Tendsto + algebra + limUnder_eq
  have h_combined : Tendsto
      (fun ε => (∫ t in (1:ℝ)..3, cauchyPrincipalValueIntegrandOn
          S_arc (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t) +
        (∫ t in (4:ℝ)..5, cauchyPrincipalValueIntegrandOn
          (S_arc ∪ S_vert) (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H) ε t))
      (𝓝[>] 0) (𝓝 (-(2 * ↑Real.pi * I * (k : ℂ) / 12) +
        2 * ↑Real.pi * I * ↑(orderAtCusp f))) :=
    h_arc.add h_seg5
  have h_eq : -(2 * ↑Real.pi * I * (k : ℂ) / 12) +
      2 * ↑Real.pi * I * ↑(orderAtCusp f) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ↑(orderAtCusp f))) := by ring
  rw [h_eq] at h_combined
  exact (h_combined.congr' (h_evt.mono (fun _ h => h.symm))).limUnder_eq

/-! ## Auto-Cusp Wrapper (SarcSvert)

Existential version: choose H automatically from f ≠ 0.
The on-curve hypotheses are transferred between heights. -/

include hf in
theorem modular_side_auto_cusp_generalizedPV_of_SarcSvert
    (S_arc S_vert : Finset ℂ)
    (h_S_unit : ∀ s ∈ S_arc, ‖(s : ℂ)‖ = 1)
    (h_S_closed : ∀ s ∈ S_arc, -(1:ℂ) / s ∈ S_arc)
    (h_rho_in : (ellipticPoint_rho : ℂ) ∈ S_arc)
    (h_vert_re : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 ∨ (s : ℂ).re = -1/2)
    (h_vert_pair_left : ∀ s ∈ S_vert, (s : ℂ).re = 1/2 → s - 1 ∈ S_vert)
    (h_vert_pair_right : ∀ s ∈ S_vert, (s : ℂ).re = -1/2 → s + 1 ∈ S_vert)
    (h_oncurve_arc : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
        fdBoundary_H H t ∈ (↑S_arc : Set ℂ))
    (h_oncurve_vert : ∀ (H' : ℝ), Real.sqrt 3 / 2 < H' → ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
        (fdBoundary_H H' t : ℂ) ∈ (↑S_vert : Set ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc ∪ S_vert) =
          -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun {H'} hH' => ?_⟩
  -- Arc is H-independent: transfer h_oncurve_arc to H'
  have h_oncurve_arc' : ∀ t ∈ Set.Ioo (1:ℝ) 3,
      modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
      fdBoundary_H H' t ∈ (↑S_arc : Set ℂ) := by
    intro t ht h_zero
    rw [fdBoundary_H_eq_arc ht.1 ht.2] at h_zero ⊢
    have := h_oncurve_arc t ht
    rw [fdBoundary_H_eq_arc ht.1 ht.2] at this
    exact this h_zero
  -- Vertical on-curve capture at H': use parametric hypothesis directly
  have h_oncurve_vert' : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
      (fdBoundary_H H' t : ℂ) ∈ (↑S_vert : Set ℂ) :=
    h_oncurve_vert H' (by linarith [hH₀_gt, hH'])
  rw [show orderAtCusp' f = orderAtCusp f from rfl]
  exact pv_integral_logDeriv_eq_modular_H_cpv_of_SarcSvert f hf S_arc S_vert
    h_S_unit h_S_closed h_rho_in h_vert_re h_vert_pair_left h_vert_pair_right
    (by linarith [hH₀_gt, hH']) h_oncurve_arc' h_oncurve_vert'
    (cusp_nonvanishing_seg5_q_radius_H_mono f hH' hH₀_nonvan)

end
