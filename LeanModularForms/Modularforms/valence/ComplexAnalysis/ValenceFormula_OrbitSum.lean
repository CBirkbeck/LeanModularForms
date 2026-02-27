/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ResidueSide
import Mathlib.NumberTheory.Modular
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Orbit-Sum Form of the Valence Formula

This file proves that `orderOfVanishingAt'` is invariant under the full modular
group `SL(2, ℤ)`, defines `ordOrbit` on orbits, and establishes finite support
for the orbit sum.

## Main Results

### Milestone A1: Full modular invariance
* `ord_smul_eq` — `orderOfVanishingAt' f (g • p) = orderOfVanishingAt' f p` for all `g : SL(2, ℤ)`

### Milestone A2: Orbit quotient
* `Orbit` — type alias for `MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`
* `ordOrbit` — well-defined lift of `orderOfVanishingAt'` to orbits
* `ordOrbit_mk` — evaluating `ordOrbit` at `⟦p⟧` gives `orderOfVanishingAt' f p`

### Milestone A3: Non-elliptic orbits and finite support
* `oi`, `orho` — the orbits of `i` and `ρ`
* `NonEllOrbit` — orbits that are neither `oi` nor `orho`
* `finite_support_ordOrbit` — finitely many orbits have nonzero `ordOrbit`
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ## Milestone A1: Full Modular Invariance of orderOfVanishingAt' -/

/-- `orderOfVanishingAt'` is invariant under the action of any `g ∈ SL(2, ℤ)`. -/
theorem ord_smul_eq (g : SL(2, ℤ)) (p : ℍ) :
    orderOfVanishingAt' (⇑f) (g • p) = orderOfVanishingAt' (⇑f) p := by
  have hg_mem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
  suffices h : ∀ q : ℍ, orderOfVanishingAt' (⇑f) (g • q) =
      orderOfVanishingAt' (⇑f) q from h p
  revert g hg_mem
  intro g hg_mem
  induction hg_mem using Subgroup.closure_induction with
  | mem x hx =>
    intro q
    rcases hx with rfl | rfl
    · exact ord_S_eq f q
    · rw [UpperHalfPlane.modular_T_smul]; exact ord_add_one_eq f q
  | one =>
    intro q; simp [one_smul]
  | mul x y _ _ ihx ihy =>
    intro q; rw [mul_smul, ihx (y • q)]; exact ihy q
  | inv x _ ihx =>
    intro q; have := ihx (x⁻¹ • q); rw [smul_inv_smul] at this; exact this.symm

/-! ## Milestone A2: Orbit Quotient and ordOrbit -/

/-- The type of orbits of `SL(2, ℤ)` acting on `ℍ`. -/
abbrev Orbit := MulAction.orbitRel.Quotient SL(2, ℤ) ℍ

/-- The canonical map from `ℍ` to its orbit. -/
def orb (p : ℍ) : Orbit := Quotient.mk'' p

/-- The order of vanishing lifted to orbits. Well-defined by `ord_smul_eq`. -/
def ordOrbit (q : Orbit) : ℤ :=
  Quotient.liftOn' q (fun p => orderOfVanishingAt' (⇑f) p)
    (fun a b hab => by
      rw [MulAction.orbitRel_apply] at hab
      obtain ⟨g, hg⟩ := hab
      rw [← hg]; exact ord_smul_eq f g b)

@[simp]
theorem ordOrbit_mk (p : ℍ) : ordOrbit f (orb p) = orderOfVanishingAt' (⇑f) p := rfl

/-! ## Milestone A3: Non-Elliptic Orbits and Finite Support -/

/-- The orbit of `i`. -/
def oi : Orbit := orb ellipticPoint_i'

/-- The orbit of `ρ`. -/
def orho : Orbit := orb ellipticPoint_rho'

/-- A non-elliptic orbit is one distinct from both `oi` and `orho`. -/
def NonEllOrbit := {q : Orbit // q ≠ oi ∧ q ≠ orho}

/-- Every orbit has a representative in the fundamental domain `𝒟` (mathlib). -/
theorem orbit_has_fd_rep (q : Orbit) : ∃ p : ℍ, orb p = q ∧ p ∈ 𝒟 := by
  induction q using Quotient.inductionOn' with
  | h z =>
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    refine ⟨g • z, ?_, hg⟩
    exact Quotient.sound' ⟨g, rfl⟩

/-- Mathlib's `normSq z ≥ 1` is equivalent to the project's `‖z‖ ≥ 1`. -/
private theorem normSq_ge_one_iff_norm_ge_one (z : ℂ) :
    1 ≤ Complex.normSq z ↔ 1 ≤ ‖z‖ := by
  rw [Complex.normSq_eq_norm_sq]
  constructor
  · intro h; nlinarith [norm_nonneg z, sq_nonneg (‖z‖ - 1)]
  · intro h; nlinarith [norm_nonneg z]

/-- The mathlib and project fundamental domains agree extensionally. -/
theorem fd_eq_fundamentalDomain : (𝒟 : Set ℍ) = 𝒟' := by
  ext z
  simp only [ModularGroup.fd, fundamentalDomain, Set.mem_setOf_eq]
  constructor
  · intro ⟨hnsq, hre⟩
    exact ⟨hre, (normSq_ge_one_iff_norm_ge_one _).mp hnsq⟩
  · intro ⟨hre, hnorm⟩
    exact ⟨(normSq_ge_one_iff_norm_ge_one _).mpr hnorm, hre⟩

/-- Every orbit has a representative in `𝒟'` (project FD). -/
theorem orbit_has_fd'_rep (q : Orbit) : ∃ p : ℍ, orb p = q ∧ p ∈ 𝒟' := by
  obtain ⟨p, hp_orb, hp_fd⟩ := orbit_has_fd_rep q
  exact ⟨p, hp_orb, fd_eq_fundamentalDomain ▸ hp_fd⟩

/-! ### Bridge: ℂ-extended function and finiteness in 𝒟' -/

/-- The ℂ-extended version of a modular form is analytic at points of ℍ. -/
private theorem G_analyticAt (p : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) := by
  have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with w hw
  have h_eq : ∀ᶠ u in 𝓝 w,
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) u =
        (f ∘ UpperHalfPlane.ofComplex) u := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    simp only [Function.comp_apply, dif_pos hu, UpperHalfPlane.ofComplex_apply_of_im_pos hu]
  exact ((h_diffOn w hw).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq

/-- Evaluating the ℂ-extended function at a point of ℍ recovers `f p`. -/
private theorem G_eval_eq_f (p : ℍ) :
    (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p := by
  simp only []
  split_ifs with h
  · congr 1
  · exact absurd p.im_pos h

/-- If `f p ≠ 0`, then `orderOfVanishingAt' f p = 0`. -/
theorem orderOfVanishingAt'_eq_zero_of_ne_zero' (p : ℍ) (hp : f p ≠ 0) :
    orderOfVanishingAt' f p = 0 := by
  unfold orderOfVanishingAt'
  have h_nf : MeromorphicNFAt _ (p : ℂ) := AnalyticAt.meromorphicNFAt (G_analyticAt f p)
  have hGp : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) ≠ 0 := by
    rw [G_eval_eq_f]; exact hp
  rw [h_nf.meromorphicOrderAt_eq_zero_iff.mpr hGp]; rfl

/-- `orderOfVanishingAt' f p ≠ 0` implies `f p = 0`. -/
theorem eq_zero_of_orderOfVanishingAt'_ne_zero' (p : ℍ)
    (hp : orderOfVanishingAt' (⇑f) p ≠ 0) : f p = 0 := by
  by_contra h; exact hp (orderOfVanishingAt'_eq_zero_of_ne_zero' f p h)

/-- `modularFormCompOfComplex f` agrees with `f` at points of ℍ. -/
private theorem modularFormCompOfComplex_eq' (p : ℍ) :
    modularFormCompOfComplex f (p : ℂ) = f p := by
  simp only [modularFormCompOfComplex, Function.comp_apply]
  congr 1; rw [UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos]; ext; rfl

/-- Points in `𝒟'` have `im > 1/2`. -/
private theorem fd'_im_gt_half (p : ℍ) (hp : p ∈ 𝒟') : (1:ℝ)/2 < (p : ℂ).im := by
  by_contra h_le; push_neg at h_le
  have h_nsq : 1 ≤ (p : ℂ).re * (p : ℂ).re + (p : ℂ).im * (p : ℂ).im := by
    have h1 : 1 ≤ ‖(p : ℂ)‖ ^ 2 := by nlinarith [hp.2]
    rw [Complex.sq_norm] at h1; rwa [Complex.normSq_apply] at h1
  have h_re_sq : (p : ℂ).re * (p : ℂ).re ≤ 1/4 := by
    have hre := abs_le.mp hp.1
    have : UpperHalfPlane.re p = (↑p : ℂ).re := rfl
    nlinarith [mul_self_nonneg (p : ℂ).re]
  -- From im ≤ 1/2 and im > 0: im² ≤ im/2 ≤ 1/4
  have him_sq : (p : ℂ).im * (p : ℂ).im ≤ 1/4 := by
    have : p.im = (↑p : ℂ).im := rfl
    nlinarith [p.im_pos]
  -- But 1 ≤ re² + im² ≤ 1/4 + 1/4 = 1/2, contradiction
  linarith

/-- A nonzero modular form has no zeros above a certain height. -/
private theorem no_zeros_above_height' (hf : f ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ (p : ℍ), H₀ ≤ (p : ℂ).im → f p ≠ 0 := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  refine ⟨H₀, hH₀_gt, fun p hp hfp => ?_⟩
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

/-- The set of zeros (with nonzero order) in `𝒟'` is finite. -/
theorem finite_zeros_in_fd' (hf : f ≠ 0) :
    Set.Finite {p : ℍ | p ∈ 𝒟' ∧ orderOfVanishingAt' (⇑f) p ≠ 0} := by
  apply Set.Finite.subset (s := {p : ℍ | p ∈ 𝒟' ∧ f p = 0})
  swap
  · intro p ⟨hp_fd, hp_ord⟩
    exact ⟨hp_fd, eq_zero_of_orderOfVanishingAt'_ne_zero' f p hp_ord⟩
  obtain ⟨H₀, hH₀_gt, hH₀_no_zeros⟩ := no_zeros_above_height' f hf
  have hM_half : (1:ℝ)/2 < H₀ + 1 := by
    linarith [Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 3)]
  have h_fin := modularForm_finitely_many_zeros_in_fdBox f hf hM_half
  apply Set.Finite.subset (h_fin.preimage (fun _ _ _ _ h => Subtype.val_injective h))
  intro p ⟨hp_fd, hp_zero⟩
  show (p : ℂ) ∈ {z ∈ fdBox (H₀ + 1) | modularFormCompOfComplex f z = 0}
  have hre := abs_le.mp hp_fd.1
  have him_gt := fd'_im_gt_half p hp_fd
  have hre_bridge : UpperHalfPlane.re p = (↑p : ℂ).re := rfl
  constructor
  · simp only [fdBox, Set.mem_setOf_eq]
    refine ⟨by linarith, by linarith, him_gt, ?_⟩
    by_contra h_ge; push_neg at h_ge
    have : H₀ ≤ (↑p : ℂ).im := by linarith
    exact absurd hp_zero (hH₀_no_zeros p this)
  · -- modularFormCompOfComplex f (↑p) = 0
    exact (modularFormCompOfComplex_eq' f p).symm ▸ hp_zero

/-- The set of orbits with nonzero `ordOrbit` is finite. -/
theorem finite_support_ordOrbit (hf : f ≠ 0) :
    Set.Finite {q : Orbit | ordOrbit f q ≠ 0} := by
  choose rep hrep using fun q : Orbit => orbit_has_fd'_rep q
  set S := {q : Orbit | ordOrbit f q ≠ 0}
  have h_fin := finite_zeros_in_fd' f hf
  have h_image : rep '' S ⊆ {p : ℍ | p ∈ 𝒟' ∧ orderOfVanishingAt' (⇑f) p ≠ 0} := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨(hrep q).2, by rw [← ordOrbit_mk f (rep q), (hrep q).1]; exact hq⟩
  have h_inj : Set.InjOn rep S := by
    intro q₁ _ q₂ _ h
    have : orb (rep q₁) = orb (rep q₂) := congrArg orb h
    rw [(hrep q₁).1, (hrep q₂).1] at this; exact this
  exact Set.Finite.of_finite_image (h_fin.subset h_image) h_inj

/-- The set of non-elliptic orbits with nonzero `ordOrbit` is finite. -/
theorem finite_support_ordOrbit_nonEll (hf : f ≠ 0) :
    Set.Finite {q : NonEllOrbit | ordOrbit f q.val ≠ 0} := by
  apply Set.Finite.subset
    ((finite_support_ordOrbit f hf).preimage
      (fun (a : NonEllOrbit) _ (b : NonEllOrbit) _ h =>
        Subtype.val_injective h))
  intro ⟨q, hq_ne⟩ hq_ord
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hq_ord ⊢
  exact hq_ord

/-! ## Bridge: Orbit Sum -/

/-- The orbit of `ρ+1` equals the orbit of `ρ` (they are in the same SL₂(ℤ)-orbit). -/
theorem orb_rho_plus_one_eq_orb_rho :
    orb ellipticPoint_rho_plus_one' = (orho : Orbit) := by
  show Quotient.mk'' ellipticPoint_rho_plus_one' = Quotient.mk'' ellipticPoint_rho'
  rw [Quotient.eq'']
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  exact ⟨ModularGroup.T, by
    rw [UpperHalfPlane.modular_T_smul]
    ext
    simp [ellipticPoint_rho', ellipticPoint_rho_plus_one', UpperHalfPlane.coe_vadd]
    ring⟩

end
