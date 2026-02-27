/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Final_AxiomClean

/-!
# Textbook Packaging of the Valence Formula

This file defines `S0 f hf`, the canonical finset of zeros of a nonzero modular form
`f` in the fundamental domain `𝒟'`, and applies the axiom-clean valence formula with
`S := S0 f hf` to eliminate the `S` parameter from the user-facing API.

## Main Definitions

* `S0` — the finset of points `p ∈ 𝒟'` where `orderOfVanishingAt' f p ≠ 0`.

## Main Results

* `S0_mem_fd` — every point in `S0` lies in `𝒟'`.
* `S0_complete` — `S0` contains every point in `𝒟'` with nonzero order of vanishing.
* `valenceFormula_full_explicit_S0` — the valence formula with `S := S0 f hf`.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ## Bridge Lemmas -/

/-- The ℂ-extended version of a modular form is analytic at points of ℍ.
This is the function `w ↦ if 0 < w.im then f ⟨w, h⟩ else 0`. -/
private theorem G_analyticAt_pkg (p : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) := by
  have h_im_pos : 0 < (p : ℂ).im := p.im_pos
  have h_g_diffAt : ∀ᶠ w in 𝓝 (p : ℂ), DifferentiableAt ℂ
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) w := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds h_im_pos] with w hw
    have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp f.holo'
    have h_eq_w : ∀ᶠ u in 𝓝 w,
        (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) u =
          (f ∘ UpperHalfPlane.ofComplex) u := by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
      simp only [Function.comp_apply, dif_pos hu]
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hu]
    exact ((h_diffOn w hw).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq_w
  exact analyticAt_iff_eventually_differentiableAt.mpr h_g_diffAt

/-- Evaluating the ℂ-extended function at a point of ℍ recovers `f p`. -/
private theorem G_eval_eq_f (p : ℍ) :
    (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p := by
  simp only []  -- beta reduce
  split_ifs with h
  · congr 1
  · exact absurd p.im_pos h

/-- If `f p ≠ 0`, then `orderOfVanishingAt' f p = 0`. -/
theorem orderOfVanishingAt'_eq_zero_of_ne_zero_pkg (p : ℍ) (hp : f p ≠ 0) :
    orderOfVanishingAt' f p = 0 := by
  unfold orderOfVanishingAt'
  have h_nf := (G_analyticAt_pkg f p).meromorphicNFAt
  have hGp : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) ≠ 0 := by
    rw [G_eval_eq_f]; exact hp
  rw [h_nf.meromorphicOrderAt_eq_zero_iff.mpr hGp]; rfl

/-- Contrapositive: `orderOfVanishingAt' f p ≠ 0` implies `f p = 0`. -/
theorem eq_zero_of_orderOfVanishingAt'_ne_zero_pkg (p : ℍ)
    (hp : orderOfVanishingAt' (⇑f) p ≠ 0) : f p = 0 := by
  by_contra h; exact hp (orderOfVanishingAt'_eq_zero_of_ne_zero_pkg f p h)

/-- `modularFormCompOfComplex f` agrees with `f` at points of ℍ. -/
private theorem modularFormCompOfComplex_eq_f (p : ℍ) :
    modularFormCompOfComplex f (p : ℂ) = f p := by
  simp only [modularFormCompOfComplex, Function.comp_apply]
  congr 1
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos]
  ext; rfl

/-! ## Cusp Bridge: No Zeros Above Height H -/

include hf in
/-- A nonzero modular form has no zeros above a certain height.
Proof: cusp nonvanishing gives `cuspFunction ≠ 0` on a q-ball, which translates
to `f(τ) ≠ 0` for `Im(τ) ≥ H₀`. -/
private theorem no_zeros_above_height :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ (p : ℍ), H₀ ≤ (p : ℂ).im → f p ≠ 0 := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun p hp hfp => ?_⟩
  -- f(p) = cuspFunction(qParam(p)), and qParam(p) is in the nonvanishing ball
  have h_eq := SlashInvariantFormClass.eq_cuspFunction (1 : ℕ) f p
  have h_qParam_mem : Function.Periodic.qParam (↑(1 : ℕ)) (↑p : ℂ) ∈
      Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H₀)) := by
    rw [Metric.mem_closedBall, dist_zero_right, Function.Periodic.norm_qParam]
    simp only [Nat.cast_one, div_one]
    exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
  have h_qParam_ne : Function.Periodic.qParam (↑(1 : ℕ)) (↑p : ℂ) ≠ 0 := by
    simp only [Function.Periodic.qParam, ne_eq]
    exact Complex.exp_ne_zero _
  exact hH₀_nonvan _ h_qParam_mem h_qParam_ne (h_eq ▸ hfp)

/-! ## Finiteness of Zeros in 𝒟' -/

/-- Points in `𝒟'` have `im > 1/2`. -/
private theorem fd_im_gt_half (p : ℍ) (hp : p ∈ 𝒟') : (1:ℝ)/2 < (p : ℂ).im := by
  have h_norm := hp.2  -- ‖(p : ℂ)‖ ≥ 1
  have h_re := hp.1    -- |p.re| ≤ 1/2
  have h_im_pos : 0 < (p : ℂ).im := p.im_pos
  have h_nsq : 1 ≤ (p : ℂ).re * (p : ℂ).re + (p : ℂ).im * (p : ℂ).im := by
    have h1 : 1 ≤ ‖(p : ℂ)‖ ^ 2 := by nlinarith
    rw [Complex.sq_norm] at h1; rwa [Complex.normSq_apply] at h1
  have h_re_sq : (p : ℂ).re * (p : ℂ).re ≤ 1/4 := by
    have : p.re = (↑p : ℂ).re := rfl
    nlinarith [abs_le.mp h_re, mul_self_nonneg (p : ℂ).re]
  nlinarith [sq_nonneg ((p : ℂ).im - 1)]

include hf in
/-- The set of zeros of a nonzero modular form in `𝒟'` is finite.

Proof: zeros have bounded imaginary part (cusp nonvanishing), and the bounded
part of 𝒟' maps into `fdBox M` where finiteness is known. -/
theorem finite_zeros_in_fd :
    Set.Finite {p : ℍ | p ∈ 𝒟' ∧ orderOfVanishingAt' (⇑f) p ≠ 0} := by
  -- Step 1: Reduce to f p = 0 via contrapositive
  apply Set.Finite.subset (s := {p : ℍ | p ∈ 𝒟' ∧ f p = 0})
  swap
  · intro p ⟨hp_fd, hp_ord⟩
    exact ⟨hp_fd, eq_zero_of_orderOfVanishingAt'_ne_zero_pkg f p hp_ord⟩
  -- Step 2: Get height bound from cusp nonvanishing
  obtain ⟨H₀, hH₀_gt, hH₀_no_zeros⟩ := no_zeros_above_height f hf
  -- Step 3: Choose M for fdBox
  set M := H₀ + 1 with hM_def
  have hM_half : (1:ℝ)/2 < M := by
    linarith [Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 3)]
  -- Step 4: Get finiteness in fdBox M
  have h_fin := modularForm_finitely_many_zeros_in_fdBox f hf hM_half
  -- Step 5: Our ℍ-set maps to ℂ-set under Subtype.val
  have h_sub : {p : ℍ | p ∈ 𝒟' ∧ f p = 0} ⊆
      Subtype.val ⁻¹' {z ∈ fdBox M | modularFormCompOfComplex f z = 0} := by
    intro p ⟨hp_fd, hp_zero⟩
    show (p : ℂ) ∈ {z ∈ fdBox M | modularFormCompOfComplex f z = 0}
    refine ⟨?_, ?_⟩
    · -- (p : ℂ) ∈ fdBox M
      simp only [fdBox, Set.mem_setOf_eq]
      have hre_bridge : p.re = (↑p : ℂ).re := rfl
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- -1 < re
        have := (abs_le.mp hp_fd.1).1; linarith [hre_bridge]
      · -- re < 1
        have := (abs_le.mp hp_fd.1).2; linarith [hre_bridge]
      · -- 1/2 < im
        exact fd_im_gt_half p hp_fd
      · -- im < M = H₀ + 1
        by_contra h_ge
        push_neg at h_ge
        exact absurd hp_zero (hH₀_no_zeros p (by linarith))
    · -- modularFormCompOfComplex f (p : ℂ) = 0
      rw [modularFormCompOfComplex_eq_f f p]; exact hp_zero
  -- Step 6: Pull back finiteness via injectivity of Subtype.val
  exact (h_fin.preimage (fun _ _ _ _ h => Subtype.val_injective h)).subset h_sub

/-! ## S0 Definition -/

/-- The canonical finset of zeros of `f` in the fundamental domain `𝒟'`.
Contains exactly the points `p ∈ 𝒟'` with `orderOfVanishingAt' f p ≠ 0`. -/
noncomputable def S0 : Finset ℍ :=
  (finite_zeros_in_fd f hf).toFinset

/-- Every point in `S0` lies in the fundamental domain `𝒟'`. -/
theorem S0_mem_fd : ∀ p ∈ S0 f hf, p ∈ 𝒟' := by
  intro p hp
  rw [S0, Set.Finite.mem_toFinset] at hp
  exact hp.1

/-- `S0` contains every point in `𝒟'` with nonzero order of vanishing. -/
theorem S0_complete :
    ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S0 f hf := by
  intro p hp hord
  rw [S0, Set.Finite.mem_toFinset]
  exact ⟨hp, hord⟩

/-! ## Main Theorem: Valence Formula with S0 -/

open Classical in
/-- **The Valence Formula with canonical zero set** (axiom-clean).

For a nonzero modular form `f` of weight `k` for `SL₂(ℤ)`, there exists `H₀ > 1`
such that for all `H ≥ H₀`:
  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{non-ell} (-gWN)·ord(s) = k/12`

where the sum ranges over non-elliptic zeros in `𝒟'`. -/
theorem valenceFormula_full_explicit_S0 :
    ∃ H₀ : ℝ, 1 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H →
      (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
      (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
      ∑ s ∈ (S0 f hf).filter (fun p =>
          p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧ p ≠ ellipticPoint_rho_plus_one'),
        (-generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ)) *
          ↑(orderOfVanishingAt' (⇑f) s) =
      (k : ℂ) / 12 :=
  valenceFormula_collapsed_rho_auto f hf (S0 f hf) (S0_mem_fd f hf) (S0_complete f hf)

open Classical in
/-- **Textbook Orbit-Sum Valence Formula with canonical zero set** (axiom-clean).

For a nonzero modular form `f` of weight `k` for `SL₂(ℤ)`:
```
ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{int} ord_p(f)
    + Σ_{leftVert} ord_p(f) + Σ_{leftArc} ord_p(f) = k/12
```
where the sums range over the canonical zero set `S0 f hf`. -/
theorem valenceFormula_orbit_sum_S0 :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_i') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPoint_rho') +
    ∑ s ∈ (S0 f hf).filter (fun p => p ≠ ellipticPoint_i' ∧ p ≠ ellipticPoint_rho' ∧
        p ≠ ellipticPoint_rho_plus_one' ∧ ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S_leftVert (S0 f hf), ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ (S0 f hf).filter (fun p => p ≠ ellipticPoint_rho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 :=
  valenceFormula_orbit_sum_auto f hf (S0 f hf) (S0_mem_fd f hf) (S0_complete f hf)

end
