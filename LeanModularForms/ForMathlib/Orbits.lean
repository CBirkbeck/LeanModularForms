/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.ModularForms.LevelOne
import LeanModularForms.ForMathlib.ModularInvariance

/-!
# SL₂(ℤ) Orbits on the Upper Half-Plane

`orderOfVanishingAt'` is invariant under the full modular group SL(2, ℤ). We define `ordOrbitFM`
on orbits and establish finite support for the orbit sum.

## Main Definitions

* `OrbitFM` — the orbit quotient `MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`
* `orbFM` — canonical quotient map `ℍ → OrbitFM`
* `ordOrbitFM` — order of vanishing lifted to orbits
* `oiFM`, `orhoFM` — orbits of the elliptic points `i` and `ρ`
* `NonEllOrbitFM` — non-elliptic orbits
* `s₀` — the finite set of zeros in the fundamental domain

## Main Results

* `ord_smul_eqFM` — `orderOfVanishingAt' f (g • p) = orderOfVanishingAt' f p`
* `finite_zeros_in_fdFM` — finiteness of zeros with nonzero order in `𝒟`
* `finite_support_ordOrbitFM` — finitely many orbits have nonzero `ordOrbitFM`
* `orbit_has_fd_repFM` — every orbit has a representative in `𝒟`
* `orb_rho_plus_one_eq_orb_rhoFM` — T-equivalence of elliptic orbits
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-- `orderOfVanishingAt'` is invariant under the action of any `g ∈ SL(2, ℤ)`. -/
theorem ord_smul_eqFM (g : SL(2, ℤ)) (p : ℍ) :
    orderOfVanishingAt' (⇑f) (g • p) = orderOfVanishingAt' (⇑f) p := by
  have hg_mem : g ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top g
  induction hg_mem using Subgroup.closure_induction generalizing p with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ord_S_eq f p
    · rw [UpperHalfPlane.modular_T_smul]; exact ord_add_one_eq f p
  | one => simp only [one_smul]
  | mul x y _ _ ihx ihy => rw [mul_smul, ihx]; exact ihy p
  | inv x _ ihx => rw [← ihx, smul_inv_smul]

/-- The type of orbits of `SL(2, ℤ)` acting on `ℍ`. -/
abbrev OrbitFM := MulAction.orbitRel.Quotient SL(2, ℤ) ℍ

/-- The canonical map from `ℍ` to its orbit. -/
def orbFM (p : ℍ) : OrbitFM := Quotient.mk'' p

/-- The order of vanishing lifted to orbits. Well-defined by `ord_smul_eqFM`. -/
def ordOrbitFM (q : OrbitFM) : ℤ :=
  Quotient.liftOn' q (orderOfVanishingAt' (⇑f)) fun _ b ⟨g, hg⟩ => by
    rw [← hg]; exact ord_smul_eqFM f g b

@[simp]
theorem ordOrbit_mkFM (p : ℍ) : ordOrbitFM f (orbFM p) = orderOfVanishingAt' (⇑f) p := rfl

/-- The orbit of `i`. -/
def oiFM : OrbitFM := orbFM ellipticPointI'

/-- The orbit of `ρ`. -/
def orhoFM : OrbitFM := orbFM ellipticPointRho'

/-- A non-elliptic orbit is one distinct from both `oiFM` and `orhoFM`. -/
def NonEllOrbitFM := {q : OrbitFM // q ≠ oiFM ∧ q ≠ orhoFM}

/-- Every orbit has a representative in the fundamental domain `𝒟`. -/
theorem orbit_has_fd_repFM (q : OrbitFM) : ∃ p : ℍ, orbFM p = q ∧ p ∈ 𝒟 := by
  induction q using Quotient.inductionOn' with
  | h z =>
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    exact ⟨g • z, Quotient.sound' ⟨g, rfl⟩, hg⟩

private theorem G_analyticAtFM (p : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) := by
  have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with w hw
  have h_eq : ∀ᶠ u in 𝓝 w, (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) u =
        (f ∘ UpperHalfPlane.ofComplex) u := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    simp only [Function.comp_apply, dif_pos hu, UpperHalfPlane.ofComplex_apply_of_im_pos hu]
  exact ((h_diffOn w hw).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq

private theorem G_eval_eq_fFM (p : ℍ) :
    (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p :=
  dif_pos p.im_pos

/-- If `f p ≠ 0`, then `orderOfVanishingAt' f p = 0`. -/
theorem orderOfVanishingAt'_eq_zero_of_ne_zero' (p : ℍ) (hp : f p ≠ 0) :
    orderOfVanishingAt' f p = 0 := by
  unfold orderOfVanishingAt'
  have h_nf : MeromorphicNFAt _ (p : ℂ) := (G_analyticAtFM f p).meromorphicNFAt
  have hGp : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) ≠ 0 := by
    rwa [G_eval_eq_fFM]
  rw [h_nf.meromorphicOrderAt_eq_zero_iff.mpr hGp]; rfl

/-- `f ≠ 0` and `f p = 0` implies `orderOfVanishingAt' f p ≠ 0`. -/
theorem orderOfVanishingAt'_ne_zero_of_eq_zeroFM (hf : f ≠ 0) (p : ℍ) (hp : f p = 0) :
    orderOfVanishingAt' (⇑f) p ≠ 0 := by
  unfold orderOfVanishingAt'
  intro h_untop_eq
  have h_nf : MeromorphicNFAt _ (p : ℂ) := (G_analyticAtFM f p).meromorphicNFAt
  have h_ord_ne : meromorphicOrderAt
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑p) ≠ (0 : WithTop ℤ) := by
    intro h0
    apply h_nf.meromorphicOrderAt_eq_zero_iff.mp h0
    split_ifs with h
    · exact_mod_cast hp
    · exact absurd p.im_pos h
  have h_top := (WithTop.untop₀_eq_zero.mp h_untop_eq).resolve_left h_ord_ne
  rw [meromorphicOrderAt_eq_top_iff] at h_top
  have h_analOn : AnalyticOnNhd ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0)
      {w | 0 < w.im} := fun w hw => G_analyticAtFM f ⟨w, hw⟩
  have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} :=
    ((convex_halfSpace_im_gt 0).isConnected ⟨I, by simp [I_im]⟩).isPreconnected
  apply hf
  ext z
  exact (G_eval_eq_fFM f z).symm.trans
    (h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
      h_preconn p.im_pos h_top.frequently z.im_pos)

/-- A point in the fundamental domain `𝒟` has imaginary part strictly above `1/2`. -/
theorem fd_im_gt_halfFM (p : ℍ) (hp : p ∈ 𝒟) : (1:ℝ)/2 < (p : ℂ).im := by
  by_contra h_le
  push Not at h_le
  obtain ⟨hnormSq, habs_re⟩ := hp
  have hre := abs_le.mp habs_re
  nlinarith [normSq_apply (↑p : ℂ), p.im_pos, mul_self_nonneg (p : ℂ).re,
    show UpperHalfPlane.re p = (↑p : ℂ).re from rfl, show p.im = (↑p : ℂ).im from rfl]

end
