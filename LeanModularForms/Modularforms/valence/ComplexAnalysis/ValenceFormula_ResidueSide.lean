/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_InteriorWinding
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_EllipticContrib
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_PV
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ResidueTheory
import LeanModularForms.Modularforms.valence.ComplexAnalysis.WindingNumber
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Rect_Homotopy
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Residue Side of the Valence Formula

This file assembles the **residue side** of the valence formula, which computes
the PV integral via the generalized residue theorem.

## Main Results

* `effectiveWinding`: The effective winding number at each point, combining
  interior winding (= 1) with elliptic point coefficients (1/2 at i, 1/3 at ρ).

* `effectiveWinding_eq_windingCoeff_of_classified`: The effective winding equals the
  orbifold coefficient for classified points (interior/i/ρ).

* `pv_equals_residue_sum`: The generalized residue theorem applied to ∂𝒟.

## The Effective Winding Function

For the valence formula, we define:
- Interior points p: effective winding = generalizedWindingNumber' = 1
- At i: effective winding = 1/2 (orbifold coefficient)
- At ρ and ρ': effective winding = 1/6 each (angle contribution)

The key insight is that for interior points, we use the PV winding number,
but for elliptic points on the boundary, we use the angle contributions directly.

## References

See `VALENCE_AI_PLAN_CORE.md` for the detailed proof strategy.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Placeholder Definitions -/

/-- Residue of a function at a point (alias for `residueSimplePole`). -/
def residue (g : ℂ → ℂ) (z₀ : ℂ) : ℂ := residueSimplePole g z₀

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ## Boundary Classification -/

/-- A point is in the interior of the fundamental domain. -/
def isInteriorPoint (p : ℍ) : Prop :=
  ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2 ∧ (p : ℂ).im < H_height

/-- A point is the elliptic point i. -/
def isEllipticI (p : ℍ) : Prop := p = ellipticPoint_i'

/-- A point is the elliptic point ρ. -/
def isEllipticRho (p : ℍ) : Prop := p = ellipticPoint_rho'

/-- Boundary points classification: interior, i, ρ, or on the boundary proper. -/
inductive BoundaryPointType where
  | interior : BoundaryPointType  -- strictly inside ∂𝒟
  | elliptic_i : BoundaryPointType  -- the point i
  | elliptic_rho : BoundaryPointType  -- the point ρ
  | boundary : BoundaryPointType  -- on ∂𝒟 but not elliptic
  deriving DecidableEq

/-- Classify a point in the fundamental domain. -/
def classifyPoint (p : ℍ) : BoundaryPointType :=
  if p = ellipticPoint_i' then .elliptic_i
  else if p = ellipticPoint_rho' then .elliptic_rho
  else if ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2 ∧ (p : ℂ).im < H_height then .interior
  else .boundary

/-! ## Effective Winding -/

/-- The effective winding number at a point p.

This is the coefficient that multiplies ord_p(f) in the valence formula:
- Interior: 1 (from winding number)
- At i: 1/2 (orbifold coefficient)
- At ρ: 1/3 (orbifold coefficient = sum of angle contributions at ρ and ρ')
- On boundary (not elliptic): 0 (doesn't contribute to interior sum) -/
def effectiveWinding (p : ℍ) : ℚ :=
  match classifyPoint p with
  | .interior => 1
  | .elliptic_i => 1/2
  | .elliptic_rho => 1/3
  | .boundary => 0

/-! ## Coefficient Lemmas -/

lemma isInteriorPoint_ne_i (p : ℍ) (hp : isInteriorPoint p) :
    p ≠ ellipticPoint_i' := by
  intro heq; subst heq; unfold isInteriorPoint at hp; simp [ellipticPoint_i'] at hp

lemma isInteriorPoint_ne_rho (p : ℍ) (hp : isInteriorPoint p) :
    p ≠ ellipticPoint_rho' := by
  intro heq; subst heq; unfold isInteriorPoint at hp
  simp [ellipticPoint_rho'] at hp
  obtain ⟨h1, _⟩ := hp
  have : ‖-(1 / 2 : ℂ) + ↑(Real.sqrt 3) / 2 * I‖ ^ 2 ≤ 1 := by
    rw [Complex.sq_norm]; simp [normSq_apply]
    nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
  nlinarith [norm_nonneg (-(1 / 2 : ℂ) + ↑(Real.sqrt 3) / 2 * I)]

lemma effectiveWinding_eq_one_of_interior (p : ℍ) (hp : isInteriorPoint p) :
    effectiveWinding p = 1 := by
  have : classifyPoint p = .interior := by
    unfold classifyPoint
    simp only [isInteriorPoint_ne_i p hp, ↓reduceIte, isInteriorPoint_ne_rho p hp,
      hp.1, hp.2.1, hp.2.2, and_self]
  simp [effectiveWinding, this]

lemma effectiveWinding_eq_half_at_i : effectiveWinding ellipticPoint_i' = 1/2 := by
  simp [effectiveWinding, classifyPoint]

lemma effectiveWinding_eq_third_at_rho : effectiveWinding ellipticPoint_rho' = 1/3 := by
  simp [effectiveWinding, classifyPoint, ellipticPoint_i_ne_rho.symm]

/-- The effective winding equals the winding number coefficient for classified points. -/
lemma effectiveWinding_eq_windingCoeff_of_classified (p : ℍ)
    (hclass : isInteriorPoint p ∨ p = ellipticPoint_i' ∨ p = ellipticPoint_rho') :
    effectiveWinding p = windingNumberCoeff' p := by
  rcases hclass with hp_int | hp_i | hp_rho
  · rw [effectiveWinding_eq_one_of_interior p hp_int,
        windingNumberCoeff_interior p (isInteriorPoint_ne_i p hp_int)
          (isInteriorPoint_ne_rho p hp_int)]
  · subst hp_i; simp [effectiveWinding, classifyPoint, windingNumberCoeff_at_i]
  · subst hp_rho
    simp [effectiveWinding, classifyPoint, ellipticPoint_i_ne_rho.symm,
      windingNumberCoeff_at_rho]

/-! ## ρ+1 Coefficient -/

/-- The effective winding at ρ+1 is 0: it is classified as a boundary point
    (‖ρ+1‖ = 1, not > 1, so `classifyPoint` returns `.boundary`). -/
lemma effectiveWinding_rho_plus_one_eq_zero :
    effectiveWinding ellipticPoint_rho_plus_one' = 0 := by
  unfold effectiveWinding classifyPoint
  have hne_i : ellipticPoint_rho_plus_one' ≠ ellipticPoint_i' := by
    intro h
    have h1 : (ellipticPoint_rho_plus_one' : ℂ).re = (ellipticPoint_i' : ℂ).re :=
      congr_arg Complex.re (congr_arg Subtype.val h)
    simp [ellipticPoint_rho_plus_one', ellipticPoint_i'] at h1
  have hne_rho : ellipticPoint_rho_plus_one' ≠ ellipticPoint_rho' := by
    intro h
    have h1 : (ellipticPoint_rho_plus_one' : ℂ).re = (ellipticPoint_rho' : ℂ).re :=
      congr_arg Complex.re (congr_arg Subtype.val h)
    simp [ellipticPoint_rho_plus_one', ellipticPoint_rho'] at h1
    norm_num at h1
  simp only [hne_i, ↓reduceIte, hne_rho]
  have h_not_int : ¬(‖(ellipticPoint_rho_plus_one' : ℂ)‖ > 1 ∧
      |(↑ellipticPoint_rho_plus_one' : ℂ).re| < 1 / 2 ∧
      (↑ellipticPoint_rho_plus_one' : ℂ).im < H_height) := by
    intro ⟨_, h_re, _⟩
    simp [ellipticPoint_rho_plus_one'] at h_re
  rw [if_neg h_not_int]

/-! ## Interior Winding Number -/

/-- Interior winding number is -1 (CW orientation).
Proven via `generalizedWindingNumber_fdBoundary_eq_neg_one` from Rect_Homotopy. -/
private lemma winding_number_interior_bridge
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < H_height) :
    generalizedWindingNumber' fdBoundary 0 5 p = -1 :=
  RectHomotopyProof.generalizedWindingNumber_fdBoundary_eq_neg_one p hp_norm hp_re hp_im_pos hp_im

/-- For interior points, the generalized winding number is -1 (clockwise). -/
lemma gWN_interior_eq_neg_one (p : ℍ) (hp : isInteriorPoint p) :
    generalizedWindingNumber' fdBoundary 0 5 (p : ℂ) = -1 :=
  winding_number_interior_bridge (p : ℂ) hp.1 hp.2.1 p.im_pos hp.2.2

/-- For interior zeros, gWN = -(effectiveWinding). -/
lemma gWN_interior_eq_neg_ew (p : ℍ) (hp : isInteriorPoint p) :
    generalizedWindingNumber' fdBoundary 0 5 (p : ℂ) = -(effectiveWinding p : ℂ) := by
  rw [gWN_interior_eq_neg_one p hp, effectiveWinding_eq_one_of_interior p hp]; push_cast; ring

/-! ## Boundary Winding Micro-Lemmas

`gWN_interior_eq_neg_one` (using the interior bridge) handles interior points.
Elliptic points (i, ρ, ρ+1) are excluded as zeros under h_nv since they lie on the
curve. Exterior points above H_height use `gWN_eq_zero_of_boundary_zero`.
-/

set_option maxHeartbeats 400000 in
/-- Translation invariance of meromorphicOrderAt: composing with (· - c) shifts the base point
by c. That is, `meromorphicOrderAt (fun w => g (w - c)) (x + c) = meromorphicOrderAt g x`. -/
private lemma meromorphicOrderAt_comp_sub_const (g : ℂ → ℂ) (x c : ℂ) :
    meromorphicOrderAt (fun w => g (w - c)) (x + c) = meromorphicOrderAt g x := by
  -- Analytic maps for shifting
  have h_sub_an : AnalyticAt ℂ (· - c) (x + c) :=
    (analyticAt_id (𝕜 := ℂ)).sub analyticAt_const
  have h_add_an : AnalyticAt ℂ (· + c) x :=
    (analyticAt_id (𝕜 := ℂ)).add analyticAt_const
  -- Transport MeromorphicAt: use explicit ∃ to avoid comp_analyticAt unification issues
  have h_mero_fwd : MeromorphicAt g x → MeromorphicAt (fun w => g (w - c)) (x + c) := by
    rintro ⟨n, hn⟩; refine ⟨n, ?_⟩
    have : (fun w => (w - (x + c)) ^ n • g (w - c)) =
        (fun z => (z - x) ^ n • g z) ∘ (· - c) := by
      ext w; simp only [Function.comp]; congr 1; ring
    rw [this]; exact hn.comp_of_eq h_sub_an (by simp)
  have h_mero_bwd : MeromorphicAt (fun w => g (w - c)) (x + c) → MeromorphicAt g x := by
    rintro ⟨n, hn⟩; refine ⟨n, ?_⟩
    have : (fun w => (w - x) ^ n • g w) =
        (fun z => (z - (x + c)) ^ n • g (z - c)) ∘ (· + c) := by
      ext w; simp only [Function.comp, add_sub_cancel_right]; congr 1; ring
    rw [this]; exact hn.comp_of_eq h_add_an (by simp)
  -- Case 1: g not meromorphic at x → both orders = 0
  by_cases hg_mero : MeromorphicAt g x
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hg_mero,
        meromorphicOrderAt_of_not_meromorphicAt (mt h_mero_bwd hg_mero)]
  -- Filter transport via homeomorphism
  have hmap : ∀ {p : ℂ → Prop}, (∀ᶠ z in 𝓝[≠] x, p z) →
      ∀ᶠ w in 𝓝[≠] (x + c), p (w - c) := by
    intro p hp
    have : map (Homeomorph.addRight (-c)) (𝓝[≠] (x + c)) = 𝓝[≠] x := by
      rw [Homeomorph.map_punctured_nhds_eq]; simp
    rw [← this] at hp; rw [eventually_map] at hp
    exact hp.mono fun z hz => by simpa [sub_eq_add_neg] using hz
  -- Case 2: order = ⊤
  by_cases htop : meromorphicOrderAt g x = ⊤
  · rw [htop, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    exact hmap htop
  -- Case 3: finite order n
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (meromorphicOrderAt_eq_int_iff hg_mero).mp hn.symm
    rw [hn.symm, meromorphicOrderAt_eq_int_iff (h_mero_fwd hg_mero)]
    refine ⟨fun w => h (w - c), hh_an.comp_of_eq h_sub_an (by simp),
      by simpa using hh_ne, ?_⟩
    exact (hmap hh_eq).mono fun z hz => by
      simp only [smul_eq_mul] at hz ⊢; rw [hz]; congr 1; congr 1; ring

/-- T-invariance of vanishing order: ord(ρ+1) = ord(ρ) for modular forms of Γ(1).

For f ∈ M_k(Γ(1)), T-periodicity gives f(z+1) = f(z), hence
meromorphicOrderAt at ρ+1 equals meromorphicOrderAt at ρ. -/
private lemma ord_rho_plus_one_eq_ord_rho :
    orderOfVanishingAt' f ellipticPoint_rho_plus_one' =
    orderOfVanishingAt' f ellipticPoint_rho' := by
  unfold orderOfVanishingAt'
  -- Define the extended function G
  set G : ℂ → ℂ := fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0 with hG_def
  -- Key values
  set ρ_cplx : ℂ := (ellipticPoint_rho' : ℂ) with hρ_def
  set ρ1_cplx : ℂ := (ellipticPoint_rho_plus_one' : ℂ) with hρ1_def
  -- Show ρ1 = ρ + 1
  have hρ1_eq : ρ1_cplx = ρ_cplx + 1 :=
    ellipticPoint_rho_add_one_eq.symm
  -- Step 1: G(w) = G(w - 1) for all w with positive imaginary part
  -- (T-periodicity: f(z+1) = f(z) for f ∈ M_k(Γ(1)))
  have hG_periodic : ∀ w : ℂ, 0 < w.im → G w = G (w - 1) := by
    intro w hw
    simp only [hG_def]
    have hw_sub : 0 < (w - 1).im := by simp [sub_im, hw]
    rw [dif_pos hw, dif_pos hw_sub]
    -- Use T-periodicity: f(T • z) = f(z), i.e., f((1:ℝ) +ᵥ z) = f(z)
    set z₀ : ℍ := ⟨w - 1, hw_sub⟩
    have h_period := SlashInvariantForm.vAdd_width_periodic 1 k 1
      f.toSlashInvariantForm z₀
    simp only [Nat.cast_one, mul_one, Int.cast_one] at h_period
    -- (1 : ℝ) +ᵥ z₀ has complex value 1 + (w-1) = w
    have h_vadd_coe : ((1 : ℝ) +ᵥ z₀ : ℍ) = ⟨w, hw⟩ := by
      apply Subtype.ext
      show ((1 : ℝ) : ℂ) + (z₀ : ℍ).val = w
      simp only [z₀]; push_cast; ring
    rw [h_vadd_coe] at h_period
    -- h_period : f.toSlashInvariantForm ⟨w, hw⟩ = f.toSlashInvariantForm z₀
    -- Convert to f via toSlashInvariantForm_coe
    simp only [ModularForm.toSlashInvariantForm_coe] at h_period
    exact h_period
  -- Step 2: G =ᶠ[𝓝[≠] ρ1] (fun w => G(w - 1))
  have hG_eq_near : G =ᶠ[𝓝[≠] ρ1_cplx] (fun w => G (w - 1)) := by
    -- ρ1 has positive imaginary part, so in a neighborhood all points do too
    have hρ1_im : 0 < ρ1_cplx.im := by
      show 0 < (ellipticPoint_rho_plus_one' : ℂ).im
      exact ellipticPoint_rho_plus_one'.im_pos
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds hρ1_im] with z hz _
    exact hG_periodic z hz
  -- Step 3: meromorphicOrderAt G ρ1 = meromorphicOrderAt (fun w => G(w-1)) ρ1
  have step3 : meromorphicOrderAt G ρ1_cplx =
      meromorphicOrderAt (fun w => G (w - 1)) ρ1_cplx :=
    meromorphicOrderAt_congr hG_eq_near
  -- Step 4: meromorphicOrderAt (fun w => G(w-1)) (ρ+1) = meromorphicOrderAt G ρ
  have step4 : meromorphicOrderAt (fun w => G (w - 1)) (ρ_cplx + 1) =
      meromorphicOrderAt G ρ_cplx :=
    meromorphicOrderAt_comp_sub_const G ρ_cplx 1
  -- Combine
  show (meromorphicOrderAt G ρ1_cplx).untop₀ = (meromorphicOrderAt G ρ_cplx).untop₀
  rw [step3, hρ1_eq, step4]

/-! ## Residue of f'/f -/

/-- The residue of f'/f at z₀ equals n when f has a zero/pole of order n. -/
lemma residue_logDeriv_of_factored {f : ℂ → ℂ} {z₀ : ℂ} {n : ℤ}
    {g : ℂ → ℂ} (hg_an : AnalyticAt ℂ g z₀) (hg_ne : g z₀ ≠ 0)
    (hf_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ n * g z) :
    residueSimplePole (fun z => deriv f z / f z) z₀ = (n : ℂ) := by
  unfold residueSimplePole
  have h_limit : Tendsto (fun z => (z - z₀) * (deriv f z / f z)) (𝓝[≠] z₀) (𝓝 n) := by
    have hg_diff : DifferentiableAt ℂ g z₀ := hg_an.differentiableAt
    have hg'_an : AnalyticAt ℂ (deriv g) z₀ := hg_an.deriv
    have hg'_cont : ContinuousAt (deriv g) z₀ := hg'_an.continuousAt
    have hg'_div_g_cont : ContinuousAt (fun z => deriv g z / g z) z₀ := by
      apply ContinuousAt.div hg'_cont hg_an.continuousAt hg_ne
    have h_sub_tends : Tendsto (fun z => z - z₀) (𝓝 z₀) (𝓝 0) := by
      convert tendsto_id.sub_const z₀; simp
    have h_remainder : Tendsto (fun z => (z - z₀) * (deriv g z / g z)) (𝓝 z₀) (𝓝 0) := by
      apply Tendsto.zero_mul_isBoundedUnder_le h_sub_tends
      exact hg'_div_g_cont.norm.isBoundedUnder_le
    have h_eq_near : ∀ᶠ z in 𝓝[≠] z₀,
        (z - z₀) * (deriv f z / f z) = n + (z - z₀) * (deriv g z / g z) := by
      have hg_ne_near : ∀ᶠ z in 𝓝 z₀, g z ≠ 0 := hg_an.continuousAt.eventually_ne hg_ne
      have hg_an_near : ∀ᶠ z in 𝓝 z₀, AnalyticAt ℂ g z := hg_an.eventually_analyticAt
      rw [eventually_nhdsWithin_iff] at hf_eq
      rw [Metric.eventually_nhds_iff] at hf_eq hg_ne_near hg_an_near
      obtain ⟨R, hR_pos, hR_eq⟩ := hf_eq
      obtain ⟨r₁, hr₁_pos, hr₁_ne⟩ := hg_ne_near
      obtain ⟨r₂, hr₂_pos, hr₂_an⟩ := hg_an_near
      let r := min R (min r₁ r₂)
      have hr_pos : 0 < r := lt_min hR_pos (lt_min hr₁_pos hr₂_pos)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      use r, hr_pos
      intro z hz_dist hz_ne_set
      have hz_ne : z ≠ z₀ := Set.mem_compl_singleton_iff.mp hz_ne_set
      have hz_in_R : dist z z₀ < R := lt_of_lt_of_le hz_dist (min_le_left R _)
      have hz_in_r₁ : dist z z₀ < r₁ := lt_of_lt_of_le hz_dist
        (le_trans (min_le_right R _) (min_le_left r₁ r₂))
      have hz_in_r₂ : dist z z₀ < r₂ := lt_of_lt_of_le hz_dist
        (le_trans (min_le_right R _) (min_le_right r₁ r₂))
      have hz_f : f z = (z - z₀)^n * g z := hR_eq hz_in_R hz_ne_set
      have hz_g : g z ≠ 0 := hr₁_ne hz_in_r₁
      have hg_an_z : AnalyticAt ℂ g z := hr₂_an hz_in_r₂
      have hz_sub_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
      have hz_pow_ne : (z - z₀)^n ≠ 0 := zpow_ne_zero n hz_sub_ne
      -- Show f =ᶠ[𝓝 z] (fun w => (w - z₀)^n * g w)
      have hf_eq_nhds : f =ᶠ[𝓝 z] (fun w => (w - z₀)^n * g w) := by
        rw [Filter.EventuallyEq, Metric.eventually_nhds_iff]
        have h_dist_pos : 0 < dist z z₀ := dist_pos.mpr hz_ne
        let ε := min (R - dist z z₀) (dist z z₀) / 2
        have h_diff_pos : 0 < R - dist z z₀ := sub_pos.mpr hz_in_R
        have hε_pos : 0 < ε := by
          simp only [ε]; exact div_pos (lt_min h_diff_pos h_dist_pos) two_pos
        use ε, hε_pos
        intro w hw
        have hw_ne : w ≠ z₀ := by
          intro h_eq; rw [h_eq, dist_comm] at hw
          have h1 : dist z z₀ < ε := hw
          have h2 : ε ≤ dist z z₀ / 2 := by
            simp only [ε]; exact div_le_div_of_nonneg_right (min_le_right _ _) two_pos.le
          linarith
        have hw_in_R : dist w z₀ < R := by
          calc dist w z₀ ≤ dist w z + dist z z₀ := dist_triangle w z z₀
            _ < ε + dist z z₀ := by linarith
            _ ≤ (R - dist z z₀) / 2 + dist z z₀ := by
                have : ε ≤ (R - dist z z₀) / 2 := by
                  simp only [ε]; exact div_le_div_of_nonneg_right (min_le_left _ _) two_pos.le
                linarith
            _ = R / 2 + dist z z₀ / 2 := by ring
            _ < R := by linarith
        have hw_ne_set : w ∈ ({z₀}ᶜ : Set ℂ) := Set.mem_compl_singleton_iff.mpr hw_ne
        exact hR_eq hw_in_R hw_ne_set
      -- deriv f z = deriv (fun w => (w - z₀)^n * g w) z
      have h_deriv_eq : deriv f z = deriv (fun w => (w - z₀)^n * g w) z :=
        hf_eq_nhds.deriv_eq
      -- Compute deriv using product rule
      have h1 : DifferentiableAt ℂ (fun w => (w - z₀)^n) z :=
        (differentiableAt_id.sub_const z₀).zpow (Or.inl hz_sub_ne)
      have h2 : DifferentiableAt ℂ g z := hg_an_z.differentiableAt
      have h_prod_deriv : deriv (fun w => (w - z₀)^n * g w) z =
          n * (z - z₀)^(n-1) * g z + (z - z₀)^n * deriv g z := by
        have h_eq : (fun w => (w - z₀)^n * g w) = (fun w => (w - z₀)^n) * g := rfl
        rw [h_eq, deriv_mul h1 h2]
        congr 1
        have h_sub_diff : DifferentiableAt ℂ (fun w => w - z₀) z :=
          differentiableAt_id.sub_const z₀
        have h_zpow_diff : DifferentiableAt ℂ (fun y => y^n) (z - z₀) :=
          differentiableAt_zpow.mpr (Or.inl hz_sub_ne)
        rw [show (fun w => (w - z₀)^n) = (fun y => y^n) ∘ (fun w => w - z₀) by rfl]
        rw [deriv_comp z h_zpow_diff h_sub_diff, deriv_zpow n (z - z₀)]
        simp only [deriv_sub_const, deriv_id'', mul_one]
      -- Algebraic manipulation
      rw [h_deriv_eq, h_prod_deriv, hz_f]
      have h_zpow_identity : (z - z₀) * (z - z₀)^(n-1) = (z - z₀)^n := by
        have h1 : (1 : ℤ) + (n - 1) = n := by ring
        calc (z - z₀) * (z - z₀)^(n-1)
            = (z - z₀)^(1 : ℤ) * (z - z₀)^(n-1) := by rw [zpow_one]
          _ = (z - z₀)^(1 + (n - 1)) := by rw [← zpow_add₀ hz_sub_ne]
          _ = (z - z₀)^n := by rw [h1]
      have h_f_ne : (z - z₀)^n * g z ≠ 0 := mul_ne_zero hz_pow_ne hz_g
      field_simp [h_f_ne, hz_g]
      calc (z - z₀) * (↑n * (z - z₀) ^ (n - 1) * g z + (z - z₀) ^ n * deriv g z)
          = ↑n * ((z - z₀) * (z - z₀) ^ (n - 1)) * g z +
            (z - z₀) * (z - z₀) ^ n * deriv g z := by ring
        _ = ↑n * (z - z₀) ^ n * g z + (z - z₀) * (z - z₀) ^ n * deriv g z := by
            rw [h_zpow_identity]
        _ = (z - z₀) ^ n * (↑n * g z + (z - z₀) * deriv g z) := by ring
    rw [show (n : ℂ) = n + 0 by ring]
    have h_tends_add : Tendsto (fun z => n + (z - z₀) * (deriv g z / g z))
        (𝓝[≠] z₀) (𝓝 (n + 0)) := by
      apply Tendsto.add tendsto_const_nhds
      exact h_remainder.mono_left nhdsWithin_le_nhds
    have h_eq_near' : (fun z => n + (z - z₀) * (deriv g z / g z)) =ᶠ[𝓝[≠] z₀]
        (fun z => (z - z₀) * (deriv f z / f z)) :=
      h_eq_near.mono (fun z hz => hz.symm)
    exact h_tends_add.congr' h_eq_near'
  exact h_limit.limUnder_eq

/-- The residue of f'/f at a zero s of f equals the order of vanishing. -/
theorem residue_logDeriv_eq_order (s : ℍ) (hs : f s = 0) :
    residue (fun z => (deriv (f ∘ UpperHalfPlane.ofComplex) z) /
        ((f ∘ UpperHalfPlane.ofComplex) z)) (s : ℂ) =
      orderOfVanishingAt' f s := by
  unfold residue orderOfVanishingAt'
  set G : ℂ → ℂ := fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0
  -- F and G agree on a neighborhood of s
  have hFG : (⇑f ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 (s : ℂ)] G := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds s.im_pos] with z hz
    show f (UpperHalfPlane.ofComplex z) = if h : 0 < z.im then f ⟨z, h⟩ else 0
    rw [dif_pos hz, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  -- G is analytic at s
  have hG_an : AnalyticAt ℂ G (s : ℂ) := by
    apply analyticAt_iff_eventually_differentiableAt.mpr
    have hDO : DifferentiableOn ℂ (⇑f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp f.holo'
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds s.im_pos] with w hw
    exact ((hDO w hw).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq
      (by filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
          show (if h : 0 < u.im then f ⟨u, h⟩ else 0) = f (UpperHalfPlane.ofComplex u)
          rw [dif_pos hu, UpperHalfPlane.ofComplex_apply_of_im_pos hu])
  by_cases htop : meromorphicOrderAt G (s : ℂ) = ⊤
  · -- Order ⊤: both sides are 0
    simp only [htop, WithTop.untop₀_top, Int.cast_zero]
    show residueSimplePole _ _ = 0
    unfold residueSimplePole
    have hFz : ∀ᶠ z in 𝓝[≠] (s : ℂ), (⇑f ∘ UpperHalfPlane.ofComplex) z = 0 :=
      (hFG.filter_mono nhdsWithin_le_nhds).trans (meromorphicOrderAt_eq_top_iff.mp htop)
    have h_ev : ∀ᶠ z in 𝓝[≠] (s : ℂ),
        (z - ↑s) * (deriv (⇑f ∘ UpperHalfPlane.ofComplex) z /
          (⇑f ∘ UpperHalfPlane.ofComplex) z) = 0 := by
      filter_upwards [hFz] with z hz; rw [hz, div_zero, mul_zero]
    exact ((Filter.tendsto_congr' h_ev).mpr tendsto_const_nhds).limUnder_eq
  · -- Finite order: extract factored form and apply helper
    obtain ⟨g, hg_an, hg_ne, hG_fact⟩ :=
      (meromorphicOrderAt_ne_top_iff hG_an.meromorphicAt).mp htop
    have hF_fact : ∀ᶠ z in 𝓝[≠] (s : ℂ), (⇑f ∘ UpperHalfPlane.ofComplex) z =
        (z - ↑s) ^ (meromorphicOrderAt G (s : ℂ)).untop₀ * g z :=
      (hFG.filter_mono nhdsWithin_le_nhds).trans
        (hG_fact.mono fun z h => by simp only [smul_eq_mul] at h; exact h)
    exact residue_logDeriv_of_factored hg_an hg_ne hF_fact

/-! ## Generalized Residue Theorem -/

/-- Algebraic core: given the sum-level winding identity and residue theorem output,
derive the CW-signed PV integral formula.

Takes a **sum-level** identity `h_sum_eq` (not pointwise winding), which is the correct
target since the PV winding number at ρ is -1/6 (not -1/3). The sum-level identity
accounts for both ρ and ρ+1 contributions via T-invariance. -/
private lemma pv_equals_residue_sum_from_assumptions
    (zeros : Finset ℍ)
    (h_sum_eq : ∑ s ∈ zeros,
        generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) *
          (orderOfVanishingAt' f s : ℂ) =
      -(∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)))
    (h_integral_residue : pv_integral f fdBoundary 0 5 =
      2 * Real.pi * I * ∑ s ∈ zeros,
        generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) *
          (orderOfVanishingAt' f s : ℂ)) :
    pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) := by
  rw [h_integral_residue, h_sum_eq, mul_neg]

/-! ### Micro-lemmas for Residue Theorem Application

These lemmas decompose `h_integral_residue_of_generalizedResidueTheorem` into
independently-provable pieces:

1. `isBigO_sub_inv_integrand_at_zero` — BigO bound at zeros (proved)
2. `nonvanishing_on_fdBoundary_of_integrable` — integrability → nonvanishing (proved from 1)
3. `zeros_avoid_fdBoundary_of_nonvanishing` — nonvanishing → avoidance (proved)
4. `argument_principle_on_fdBoundary` — residue theorem proper (**sorry**)
5. `h_integral_residue_of_generalizedResidueTheorem` — main result (proved from 2 + 4)
-/

/-- At any `t₀ ∈ [0,5]` where `fdBoundary(t₀)` has positive imaginary part,
we can lift `fdBoundary(t₀)` to an element of ℍ. -/
private def fdBoundary_uhp (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0:ℝ) 5) : ℍ :=
  ⟨fdBoundary t₀, fdBoundary_im_pos t₀ ht₀⟩

/-- If `modularFormCompOfComplex f (fdBoundary t₀) = 0`, then `f` vanishes at the
corresponding upper half-plane point. -/
private lemma f_vanishes_at_fdBoundary (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0:ℝ) 5)
    (hzero : modularFormCompOfComplex f (fdBoundary t₀) = 0) :
    f (fdBoundary_uhp t₀ ht₀) = 0 := by
  have h_im := fdBoundary_im_pos t₀ ht₀
  simp only [modularFormCompOfComplex, Function.comp_apply] at hzero
  rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im] at hzero

include hf in
/-- One-sided BigO via a segment function. Given a smooth curve `γ` that:
(1) passes through `z₀ = fdBoundary(t₀)`,
(2) has nonzero derivative at `t₀`,
(3) for each point `t` in the one-sided filter `l`, `fdBoundary =ᶠ[𝓝 t] γ`
    (full neighborhood agreement, giving both value and derivative agreement),
we get `(t-t₀)⁻¹ =O[l]` of the `fdBoundary` integrand. -/
private lemma isBigO_sub_inv_via_segment
    (γ : ℝ → ℂ) (t₀ : ℝ)
    (hγ_eq : γ t₀ = fdBoundary t₀)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_deriv_ne : deriv γ t₀ ≠ 0)
    (hγ_deriv_cont : ContinuousAt (deriv γ) t₀)
    (n : ℤ) (hn : n > 0) (g_reg : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g_reg (fdBoundary t₀))
    (hg_ne : g_reg (fdBoundary t₀) ≠ 0)
    (h_formula : ∀ᶠ z in 𝓝 (fdBoundary t₀), z ≠ fdBoundary t₀ →
      logDeriv (modularFormCompOfComplex f) z = (n : ℂ) / (z - fdBoundary t₀) + logDeriv g_reg z)
    {l : Filter ℝ} (hl : l ≤ 𝓝[≠] t₀)
    (h_nhds_agree : ∀ᶠ t in l, fdBoundary =ᶠ[𝓝 t] γ) :
    (fun t => (t - t₀)⁻¹) =O[l]
      (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) *
        deriv fdBoundary t) := by
  have h_bigO_γ := isBigO_sub_inv_logDeriv_arc f γ t₀ (fdBoundary t₀) hγ_eq
    hγ_diff hγ_deriv_ne hγ_deriv_cont n hn g_reg hg_analytic hg_ne h_formula
  refine (h_bigO_γ.mono hl).congr' (EventuallyEq.refl l _) ?_
  exact h_nhds_agree.mono fun t h_eq => by
    have h_val : fdBoundary t = γ t := h_eq.eq_of_nhds
    have h_deriv : deriv fdBoundary t = deriv γ t := h_eq.deriv_eq
    show logDeriv (modularFormCompOfComplex f) (γ t) * deriv γ t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t
    rw [h_val, h_deriv]

-- Segment smoothness and derivative helpers, extracted to top-level lemmas.
-- Uses `rw [h_eq]` pattern to bridge definitional unfolding vs canonical forms.
private lemma seg1_contDiff : ContDiff ℝ ⊤ fdBoundary_seg1 := by
  have h_eq : fdBoundary_seg1 =
      fun t => (1:ℂ)/2 + (↑(H_height - t * (H_height - Real.sqrt 3 / 2))) * I := by
    ext t; simp [fdBoundary_seg1]
  rw [h_eq]
  exact contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.sub (contDiff_id.mul contDiff_const))).mul contDiff_const)

private lemma seg1_deriv_ne (t₀ : ℝ) : deriv fdBoundary_seg1 t₀ ≠ 0 := by
  have h_eq : fdBoundary_seg1 =
      fun t => (1:ℂ)/2 + (↑(H_height - t * (H_height - Real.sqrt 3 / 2))) * I := by
    ext t; simp [fdBoundary_seg1]
  have h_inner : HasDerivAt (fun t => H_height - t * (H_height - Real.sqrt 3 / 2))
      (-(H_height - Real.sqrt 3 / 2)) t₀ := by
    have := (hasDerivAt_const t₀ H_height).sub
      ((hasDerivAt_id t₀).mul_const (H_height - Real.sqrt 3 / 2))
    convert this using 1; ring
  have hda : HasDerivAt fdBoundary_seg1 (↑(-(H_height - Real.sqrt 3 / 2)) * I) t₀ := by
    rw [h_eq]; exact (h_inner.ofReal_comp.mul_const I).const_add _
  rw [hda.deriv]; apply mul_ne_zero
  · simp only [ofReal_neg, neg_ne_zero, ofReal_sub]
    exact_mod_cast sub_ne_zero.mpr H_height_gt_rho_height.ne'
  · exact I_ne_zero

private lemma seg4_contDiff : ContDiff ℝ ⊤ fdBoundary_seg4 := by
  have h_eq : fdBoundary_seg4 =
      fun t => -(1:ℂ)/2 + (↑(Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2))) * I := by
    ext t; simp [fdBoundary_seg4]
  rw [h_eq]
  exact contDiff_const.add
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.add ((contDiff_id.sub contDiff_const).mul contDiff_const))).mul contDiff_const)

private lemma seg4_deriv_ne (t₀ : ℝ) : deriv fdBoundary_seg4 t₀ ≠ 0 := by
  have h_eq : fdBoundary_seg4 =
      fun t => -(1:ℂ)/2 + (↑(Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2))) * I := by
    ext t; simp [fdBoundary_seg4]
  have h_inner : HasDerivAt (fun t => Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2))
      (H_height - Real.sqrt 3 / 2) t₀ := by
    have := (hasDerivAt_const t₀ (Real.sqrt 3 / 2)).add
      (((hasDerivAt_id t₀).sub_const (3 : ℝ)).mul_const (H_height - Real.sqrt 3 / 2))
    convert this using 1; ring
  have hda : HasDerivAt fdBoundary_seg4 (↑(H_height - Real.sqrt 3 / 2) * I) t₀ := by
    rw [h_eq]; exact (h_inner.ofReal_comp.mul_const I).const_add _
  rw [hda.deriv]; apply mul_ne_zero
  · simp only [ofReal_sub, ne_eq]
    exact_mod_cast sub_ne_zero.mpr H_height_gt_rho_height.ne'
  · exact I_ne_zero

private lemma seg5_contDiff : ContDiff ℝ ⊤ fdBoundary_seg5 := by
  have h_eq : fdBoundary_seg5 = fun t => (↑(t - (9:ℝ)/2) : ℂ) + ↑H_height * I := by
    ext t; simp [fdBoundary_seg5]
  rw [h_eq]
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_id.sub contDiff_const)).add contDiff_const

private lemma seg5_deriv_ne (t₀ : ℝ) : deriv fdBoundary_seg5 t₀ ≠ 0 := by
  have h_eq : fdBoundary_seg5 = fun t => (↑(t - (9:ℝ)/2) : ℂ) + ↑H_height * I := by
    ext t; simp [fdBoundary_seg5]
  have hda : HasDerivAt fdBoundary_seg5 (1 : ℂ) t₀ := by
    rw [h_eq]; exact ((hasDerivAt_id t₀).sub_const _).ofReal_comp.add_const _
  rw [hda.deriv]; exact one_ne_zero

private lemma seg2_contDiff : ContDiff ℝ ⊤ fdBoundary_seg2 := by
  have h_eq : fdBoundary_seg2 =
      fun t => Complex.exp ((↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) * I) := by
    ext t; simp [fdBoundary_seg2]
  rw [h_eq]
  exact ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.add ((contDiff_id.sub contDiff_const).mul contDiff_const))).mul contDiff_const)
    |>.cexp

private lemma seg2_deriv_ne (t₀ : ℝ) : deriv fdBoundary_seg2 t₀ ≠ 0 := by
  have h_eq : fdBoundary_seg2 =
      fun t => Complex.exp ((↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) * I) := by
    ext t; simp [fdBoundary_seg2]
  have h_r : HasDerivAt (fun t => Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))
      (Real.pi / 2 - Real.pi / 3) t₀ := by
    have := (hasDerivAt_const t₀ (Real.pi / 3)).add
      (((hasDerivAt_id t₀).sub_const (1 : ℝ)).mul_const (Real.pi / 2 - Real.pi / 3))
    convert this using 1; ring
  have h_cexp := (h_r.ofReal_comp.mul_const (I : ℂ)).cexp
  rw [h_eq, h_cexp.deriv]
  apply mul_ne_zero (exp_ne_zero _)
  apply mul_ne_zero _ I_ne_zero
  exact_mod_cast (show Real.pi / 2 - Real.pi / 3 > 0 by linarith [Real.pi_pos]).ne'

private lemma seg3_contDiff : ContDiff ℝ ⊤ fdBoundary_seg3 := by
  have h_eq : fdBoundary_seg3 =
      fun t => Complex.exp ((↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) * I) := by
    ext t; simp [fdBoundary_seg3]
  rw [h_eq]
  exact ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.add ((contDiff_id.sub contDiff_const).mul contDiff_const))).mul contDiff_const)
    |>.cexp

private lemma seg3_deriv_ne (t₀ : ℝ) : deriv fdBoundary_seg3 t₀ ≠ 0 := by
  have h_eq : fdBoundary_seg3 =
      fun t => Complex.exp ((↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) * I) := by
    ext t; simp [fdBoundary_seg3]
  have h_r : HasDerivAt (fun t => Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))
      (2 * Real.pi / 3 - Real.pi / 2) t₀ := by
    have := (hasDerivAt_const t₀ (Real.pi / 2)).add
      (((hasDerivAt_id t₀).sub_const (2 : ℝ)).mul_const (2 * Real.pi / 3 - Real.pi / 2))
    convert this using 1; ring
  have h_cexp := (h_r.ofReal_comp.mul_const (I : ℂ)).cexp
  rw [h_eq, h_cexp.deriv]
  apply mul_ne_zero (exp_ne_zero _)
  apply mul_ne_zero _ I_ne_zero
  exact_mod_cast (show 2 * Real.pi / 3 - Real.pi / 2 > 0 by linarith [Real.pi_pos]).ne'

include hf in
/-- BigO bound: at a zero of F on the boundary, the integrand grows at least as fast
as 1/(t - t₀). This follows from the simple pole of logDeriv F at zeros and the
immersion property of the boundary curve (γ'(t₀) ≠ 0).

**Mathematical content**: If F has a zero of order n at z₀ = γ(t₀), then
logDeriv F(γ(t)) · γ'(t) ≈ n · γ'(t)/(γ'(t₀)(t-t₀)) ≈ n/(t-t₀) near t₀.
Hence `(t-t₀)⁻¹ =O (logDeriv F ∘ γ · γ')` near t₀.

**Proof route**: Use `hasSimplePoleAt_logDeriv_of_zero` for the logDeriv pole,
Taylor expansion of `fdBoundary` at t₀, and `fdBoundaryImmersion.deriv_ne_zero`
for γ'(t₀) ≠ 0. -/
private lemma isBigO_sub_inv_integrand_at_zero (t₀ : ℝ) (ht₀ : t₀ ∈ Icc (0:ℝ) 5)
    (hzero : modularFormCompOfComplex f (fdBoundary t₀) = 0) :
    (fun t => (t - t₀)⁻¹) =O[𝓝[≠] t₀]
      (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) *
        deriv fdBoundary t) := by
  -- Step 1: Get the zero at the UHP point and the pole decomposition
  set z₀ := fdBoundary t₀
  have h_im := fdBoundary_im_pos t₀ ht₀
  set s : ℍ := ⟨z₀, h_im⟩
  have h_fs : f s = 0 := f_vanishes_at_fdBoundary f t₀ ht₀ hzero
  obtain ⟨n, g_reg, hn_pos, hg_analytic, hg_ne_zero, _, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s h_fs
  -- Step 2: Case split on whether t₀ is a partition point
  by_cases ht_part : t₀ ∉ fdBoundaryFullPartition
  · -- Non-partition point: fdBoundary is C1 with nonzero derivative
    have ht_ioo : t₀ ∈ Ioo (0:ℝ) 5 := by
      simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton, not_or]
        at ht_part
      exact ⟨lt_of_le_of_ne ht₀.1 (Ne.symm ht_part.1), lt_of_le_of_ne ht₀.2 ht_part.2.2.2.2.2⟩
    have h_diff : DifferentiableAt ℝ fdBoundary t₀ := by
      have htp' : t₀ ∉ fdPartition := by
        simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton,
          not_or] at ht_part
        simp only [fdPartition, Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨ht_part.2.1, ht_part.2.2.1, ht_part.2.2.2.1, ht_part.2.2.2.2.1⟩
      exact fdBoundary_differentiableAt_off_partition t₀ ht_ioo htp'
    have h_deriv_ne : deriv fdBoundary t₀ ≠ 0 :=
      fdBoundaryImmersion.deriv_ne_zero t₀ ht₀ ht_part
    have h_deriv_cont : ContinuousAt (deriv fdBoundary) t₀ :=
      fdBoundaryCurve.deriv_continuous_off_partition t₀ ht_ioo ht_part
    exact isBigO_sub_inv_logDeriv_arc f fdBoundary t₀ z₀ rfl
      h_diff h_deriv_ne h_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
  · -- Partition point: We use the direct approach based on the product
    -- (t - t₀) * integrand(t) → n ≠ 0, avoiding the need for differentiability
    -- of fdBoundary at t₀.
    push_neg at ht_part
    -- Step A: fdBoundary is continuous, so fdBoundary(t) → z₀
    have h_cont_bd : ContinuousAt fdBoundary t₀ :=
      fdBoundary_continuous.continuousAt
    -- Step B: fdBoundary(t) ≠ z₀ for t ≠ t₀ near t₀
    -- (follows from immersion: one-sided slopes are nonzero)
    -- Step C: The product (t-t₀) * integrand(t) is eventually bounded away from 0
    -- This gives the BigO bound.
    -- We use left/right derivative limits from the immersion structure.
    -- At each partition point, fdBoundaryImmersion provides nonzero left/right limits.
    -- Split into one-sided filters
    have h_nhds_split : 𝓝[≠] t₀ = 𝓝[<] t₀ ⊔ 𝓝[>] t₀ := by
      rw [← nhdsWithin_union, ← Iio_union_Ioi]
    rw [h_nhds_split, Asymptotics.isBigO_sup]
    simp only [fdBoundaryFullPartition, Finset.mem_insert, Finset.mem_singleton] at ht_part
    -- For each side, use isBigO_sub_inv_via_segment with the appropriate segment function.
    -- Use extracted top-level lemmas for segment smoothness and derivative nonzero
    have h_seg1_deriv_ne := fun t₀' => seg1_deriv_ne t₀'
    have h_seg1_smooth := seg1_contDiff
    have h_seg4_deriv_ne := fun t₀' => seg4_deriv_ne t₀'
    have h_seg4_smooth := seg4_contDiff
    have h_seg5_deriv_ne := fun t₀' => seg5_deriv_ne t₀'
    have h_seg5_smooth := seg5_contDiff
    have h_seg2_smooth := seg2_contDiff
    have h_seg3_smooth := seg3_contDiff
    have h_seg2_deriv_ne := fun t₀' => seg2_deriv_ne t₀'
    have h_seg3_deriv_ne := fun t₀' => seg3_deriv_ne t₀'
    -- Segment value at boundary: seg(t₀) = fdBoundary(t₀)
    -- For left/right of partition points, we need seg_k(t₀) = fdBoundary(t₀)
    -- fdBoundary uses the LEFT branch at each partition point (t ≤ k):
    -- seg1 at t₀=0,1; seg2 at t₀=2; seg3 at t₀=3; seg4 at t₀=4
    -- The RIGHT segment must also equal fdBoundary at the point (by continuity).
    -- We can compute this directly:
    -- seg2(1) should equal fdBoundary(1) = seg1(1) (both = ρ+1)
    -- seg3(2) should equal fdBoundary(2) (both = I)
    -- seg4(3) should equal fdBoundary(3) (both = ρ)
    -- seg5(4) should equal fdBoundary(4) (both = -1/2 + Hi)
    -- Helper for nhds agreement on one-sided intervals
    -- For t < a (near a), fdBoundary =ᶠ[𝓝 t] seg_left
    -- because in a full neighborhood of t < a, all points are < a
    rcases ht_part with rfl | rfl | rfl | rfl | rfl | rfl
    · -- t₀ = 0: both sides use seg1
      constructor <;> (
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg1 0
          (fdBoundary_eq_seg1_on 0 ⟨le_rfl, by norm_num⟩).symm
          (h_seg1_smooth.differentiable le_top).differentiableAt
          (h_seg1_deriv_ne 0)
          (h_seg1_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula)
      · exact nhdsLT_le_nhdsNE _
      · filter_upwards [Ioo_mem_nhdsLT (show (-1:ℝ) < 0 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Iio_mem_nhds (show t < 1 by linarith)] with u hu
        have hu' : u < 1 := mem_Iio.mp hu
        show fdBoundary u = fdBoundary_seg1 u
        unfold fdBoundary fdBoundary_seg1; rw [if_pos hu'.le]
      · exact nhdsGT_le_nhdsNE _
      · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Iio_mem_nhds htm.2] with u hu
        have hu' : u < 1 := mem_Iio.mp hu
        show fdBoundary u = fdBoundary_seg1 u
        unfold fdBoundary fdBoundary_seg1; rw [if_pos hu'.le]
    · -- t₀ = 1: seg1 on left, seg2 on right
      constructor
      · -- Left of 1: use seg1
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg1 1
          (fdBoundary_eq_seg1_on 1 ⟨by norm_num, le_rfl⟩).symm
          (h_seg1_smooth.differentiable le_top).differentiableAt
          (h_seg1_deriv_ne 1)
          (h_seg1_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula
          (nhdsLT_le_nhdsNE _)
        filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Iio_mem_nhds htm.2] with u hu
        have hu' : u < 1 := mem_Iio.mp hu
        show fdBoundary u = fdBoundary_seg1 u
        unfold fdBoundary fdBoundary_seg1; rw [if_pos hu'.le]
      · -- Right of 1: use seg2
        -- Need: fdBoundary_seg2 1 = fdBoundary 1
        have h_seg2_at_1 : fdBoundary_seg2 1 = fdBoundary 1 := by
          rw [fdBoundary_at_one]
          simp only [fdBoundary_seg2, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
          -- seg2(1) = exp((π/3 + (1-1)*(π/2 - π/3))*I) = exp(π/3*I)
          have h_angle : (↑Real.pi / 3 + (↑(1:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) =
              ↑Real.pi / 3 := by push_cast; ring
          rw [h_angle, Complex.exp_mul_I]
          -- cos(↑π/3) + sin(↑π/3)*I = ↑⟨1/2 + ↑√3/2*I, ...⟩
          -- Rewrite arg to ofReal form so ofReal_cos/sin can match
          have hπ3 : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3 : ℝ) := by push_cast; ring
          rw [hπ3, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
              Real.cos_pi_div_three, Real.sin_pi_div_three]
          simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
          rfl
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg2 1
          h_seg2_at_1
          (h_seg2_smooth.differentiable le_top).differentiableAt
          (h_seg2_deriv_ne 1)
          (h_seg2_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula
          (nhdsGT_le_nhdsNE _)
        filter_upwards [Ioo_mem_nhdsGT (show (1:ℝ) < 2 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Ioo_mem_nhds htm.1 htm.2] with u hu
        exact fdBoundary_eq_seg2_on u ⟨(mem_Ioo.mp hu).1, (mem_Ioo.mp hu).2.le⟩
    · -- t₀ = 2: fdBoundary is differentiable at 2 (smooth junction)
      -- fdBoundary agrees with fdBoundary_seg2 on all of (1,3) (seg2 and seg3 are the same
      -- function via the identity π/3 + (s-1)*(π/2-π/3) = π/2 + (s-2)*(2π/3-π/2) for all s)
      have h_agree : fdBoundary =ᶠ[𝓝 2] fdBoundary_seg2 := by
        filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3)]
          with s hs
        have hsm := mem_Ioo.mp hs
        simp only [fdBoundary, if_neg (not_le.mpr hsm.1)]
        by_cases h : s ≤ 2
        · simp only [if_pos h, fdBoundary_seg2]
        · push_neg at h
          simp only [if_neg (not_le.mpr h), if_pos hsm.2.le, fdBoundary_seg2]
          congr 1; congr 1; ring
      -- Transfer differentiability, derivative, and continuity from seg2
      have h_diff : DifferentiableAt ℝ fdBoundary 2 := fdBoundary_differentiableAt_two
      have h_deriv_eq : deriv fdBoundary 2 = deriv fdBoundary_seg2 2 :=
        h_agree.deriv_eq
      have h_deriv_ne : deriv fdBoundary 2 ≠ 0 := by
        rw [h_deriv_eq]; exact h_seg2_deriv_ne 2
      have h_deriv_cont : ContinuousAt (deriv fdBoundary) 2 := by
        have h_eq_deriv : deriv fdBoundary =ᶠ[𝓝 2] deriv fdBoundary_seg2 := by
          filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ) < 2) (by norm_num : (2:ℝ) < 3)]
            with s hs
          have hsm := mem_Ioo.mp hs
          have h_loc : fdBoundary =ᶠ[𝓝 s] fdBoundary_seg2 := by
            filter_upwards [Ioo_mem_nhds hsm.1 hsm.2] with u hu
            have hum := mem_Ioo.mp hu
            simp only [fdBoundary, if_neg (not_le.mpr hum.1)]
            by_cases h : u ≤ 2
            · simp only [if_pos h, fdBoundary_seg2]
            · push_neg at h
              simp only [if_neg (not_le.mpr h), if_pos hum.2.le, fdBoundary_seg2]
              congr 1; congr 1; ring
          exact h_loc.deriv_eq
        exact (h_seg2_smooth.continuous_deriv le_top).continuousAt.congr h_eq_deriv.symm
      have h_bigO := isBigO_sub_inv_logDeriv_arc f fdBoundary 2 z₀ rfl
        h_diff h_deriv_ne h_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
      exact ⟨h_bigO.mono (nhdsLT_le_nhdsNE _), h_bigO.mono (nhdsGT_le_nhdsNE _)⟩
    · -- t₀ = 3: seg3 on left, seg4 on right
      constructor
      · -- Left of 3: use seg3
        have h_seg3_at_3 : fdBoundary_seg3 3 = fdBoundary 3 := by
          rw [fdBoundary_at_three]
          simp only [fdBoundary_seg3, ellipticPoint_rho, ellipticPoint_rho']
          -- seg3(3) = exp((π/2 + (3-2)*(2π/3 - π/2))*I) = exp(2π/3*I)
          have h_angle : (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) =
              2 * ↑Real.pi / 3 := by push_cast; ring
          rw [h_angle, Complex.exp_mul_I]
          -- cos(2↑π/3) + sin(2↑π/3)*I = ↑⟨-1/2 + ↑√3/2*I, ...⟩
          have h_cos : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
            have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
            rw [h, Real.cos_pi_sub, Real.cos_pi_div_three]; ring
          have h_sin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
            have h : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
            rw [h, Real.sin_pi_sub, Real.sin_pi_div_three]
          -- Rewrite arg to ofReal form so ofReal_cos/sin can match
          have h2π3 : (2 * ↑Real.pi / 3 : ℂ) = ↑(2 * Real.pi / 3 : ℝ) := by push_cast; ring
          rw [h2π3, ← Complex.ofReal_cos, ← Complex.ofReal_sin, h_cos, h_sin]
          simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
          rfl
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg3 3
          h_seg3_at_3
          (h_seg3_smooth.differentiable le_top).differentiableAt
          (h_seg3_deriv_ne 3)
          (h_seg3_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula
          (nhdsLT_le_nhdsNE _)
        filter_upwards [Ioo_mem_nhdsLT (show (2:ℝ) < 3 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Ioo_mem_nhds htm.1 htm.2] with u hu
        exact fdBoundary_eq_seg3_on u ⟨(mem_Ioo.mp hu).1, (mem_Ioo.mp hu).2.le⟩
      · -- Right of 3: use seg4
        have h_seg4_at_3 : fdBoundary_seg4 3 = fdBoundary 3 := by
          rw [fdBoundary_at_three]
          unfold fdBoundary_seg4 ellipticPoint_rho ellipticPoint_rho'
          congr 1; push_cast; ring
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg4 3
          h_seg4_at_3
          (h_seg4_smooth.differentiable le_top).differentiableAt
          (h_seg4_deriv_ne 3)
          (h_seg4_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula
          (nhdsGT_le_nhdsNE _)
        filter_upwards [Ioo_mem_nhdsGT (show (3:ℝ) < 4 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Ioo_mem_nhds htm.1 htm.2] with u hu
        exact fdBoundary_eq_seg4_on u ⟨(mem_Ioo.mp hu).1, (mem_Ioo.mp hu).2.le⟩
    · -- t₀ = 4: seg4 on left, seg5 on right
      constructor
      · -- Left of 4: use seg4
        have h_seg4_at_4 : fdBoundary_seg4 4 = fdBoundary 4 := by
          rw [fdBoundary_at_four]; unfold fdBoundary_seg4; push_cast; ring
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg4 4
          h_seg4_at_4
          (h_seg4_smooth.differentiable le_top).differentiableAt
          (h_seg4_deriv_ne 4)
          (h_seg4_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula
          (nhdsLT_le_nhdsNE _)
        filter_upwards [Ioo_mem_nhdsLT (show (3:ℝ) < 4 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Ioo_mem_nhds htm.1 htm.2] with u hu
        exact fdBoundary_eq_seg4_on u ⟨(mem_Ioo.mp hu).1, (mem_Ioo.mp hu).2.le⟩
      · -- Right of 4: use seg5
        have h_seg5_at_4 : fdBoundary_seg5 4 = fdBoundary 4 := by
          rw [fdBoundary_at_four]; unfold fdBoundary_seg5; push_cast; ring
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg5 4
          h_seg5_at_4
          (h_seg5_smooth.differentiable le_top).differentiableAt
          (h_seg5_deriv_ne 4)
          (h_seg5_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula
          (nhdsGT_le_nhdsNE _)
        filter_upwards [Ioo_mem_nhdsGT (show (4:ℝ) < 5 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Ioi_mem_nhds htm.1] with u hu
        have hu' : 4 < u := mem_Ioi.mp hu
        show fdBoundary u = fdBoundary_seg5 u
        unfold fdBoundary fdBoundary_seg5
        rw [if_neg (not_le.mpr (show 1 < u by linarith)),
          if_neg (not_le.mpr (show 2 < u by linarith)),
          if_neg (not_le.mpr (show 3 < u by linarith)),
          if_neg (not_le.mpr (show 4 < u by linarith))]
    · -- t₀ = 5: both sides use seg5
      constructor <;> (
        apply isBigO_sub_inv_via_segment f hf fdBoundary_seg5 5
          (by rw [fdBoundary_at_five]; unfold fdBoundary_seg5; push_cast; ring)
          (h_seg5_smooth.differentiable le_top).differentiableAt
          (h_seg5_deriv_ne 5)
          (h_seg5_smooth.continuous_deriv le_top).continuousAt
          n hn_pos g_reg hg_analytic hg_ne_zero h_formula)
      · exact nhdsLT_le_nhdsNE _
      · filter_upwards [Ioo_mem_nhdsLT (show (4:ℝ) < 5 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Ioi_mem_nhds htm.1] with u hu
        have hu' : 4 < u := mem_Ioi.mp hu
        show fdBoundary u = fdBoundary_seg5 u
        unfold fdBoundary fdBoundary_seg5
        rw [if_neg (not_le.mpr (show 1 < u by linarith)),
          if_neg (not_le.mpr (show 2 < u by linarith)),
          if_neg (not_le.mpr (show 3 < u by linarith)),
          if_neg (not_le.mpr (show 4 < u by linarith))]
      · exact nhdsGT_le_nhdsNE _
      · -- For t > 5, fdBoundary agrees with seg5 in a full neighborhood of t
        -- because for ALL u > 4, fdBoundary u = fdBoundary_seg5 u (the else branch)
        have h_seg5_all : ∀ u : ℝ, 4 < u → fdBoundary u = fdBoundary_seg5 u := by
          intro u hu
          simp only [fdBoundary, fdBoundary_seg5, if_neg (not_le.mpr (lt_trans (by norm_num : (1:ℝ) < 4) hu)),
            if_neg (not_le.mpr (lt_trans (by norm_num : (2:ℝ) < 4) hu)),
            if_neg (not_le.mpr (lt_trans (by norm_num : (3:ℝ) < 4) hu)),
            if_neg (not_le.mpr hu)]
        filter_upwards [Ioo_mem_nhdsGT (show (5:ℝ) < 6 by norm_num)] with t ht
        have htm := mem_Ioo.mp ht
        filter_upwards [Ioi_mem_nhds (show (4:ℝ) < t by linarith)] with u hu
        exact h_seg5_all u (mem_Ioi.mp hu)

include hf in
/-- If the logDeriv integrand is interval-integrable on [0,5], then the modular form
has no zeros on the boundary curve. Proven by contradiction using the BigO bound
and `not_intervalIntegrable_of_sub_inv_isBigO_punctured` from mathlib. -/
private lemma nonvanishing_on_fdBoundary_of_integrable
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5) :
    ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0 := by
  intro t₀ ht₀ hzero
  exact absurd hint (not_intervalIntegrable_of_sub_inv_isBigO_punctured
    (isBigO_sub_inv_integrand_at_zero f hf t₀ ht₀ hzero)
    (by norm_num : (0:ℝ) ≠ 5)
    (by rw [Set.uIcc_of_le (show (0:ℝ) ≤ 5 by norm_num)]; exact ht₀))

/-- Zeros of f in the fundamental domain, viewed as complex numbers, avoid the
boundary curve image. Follows directly from nonvanishing. -/
private lemma zeros_avoid_fdBoundary_of_nonvanishing
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0) :
    ∀ s ∈ zeros, ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t ≠ (s : ℂ) := by
  intro s hs t ht heq
  apply h_nv t ht
  show modularFormCompOfComplex f (fdBoundary t) = 0
  change (f ∘ UpperHalfPlane.ofComplex) (fdBoundary t) = 0
  rw [heq, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos s.im_pos]
  exact hzeros s hs

/-! ### Ambient Box and Zero Set Infrastructure

These micro-lemmas provide the hypotheses needed for `integral_eq_sum_residues_of_avoids`
(ResidueTheory.lean:2755). The single structurally blocked hypothesis is `DifferentiableOn`.
All other hypotheses are discharged. -/

/-- An open box in ℂ containing the fundamental domain truncated at height `M`:
  `{z | -1 < z.re < 1 ∧ 1/2 < z.im < M}`. -/
def fdBox (M : ℝ) : Set ℂ :=
  {z : ℂ | -1 < z.re ∧ z.re < 1 ∧ (1:ℝ)/2 < z.im ∧ z.im < M}

private lemma fdBox_isOpen (M : ℝ) : IsOpen (fdBox M) := by
  refine IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt Complex.continuous_re continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact isOpen_lt Complex.continuous_im continuous_const

private lemma strict_convex_comb_lb {a b x y L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : L < x) (hy : L < y) : L < a * x + b * y := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp at hab; subst hab; simp; linarith
  · have h1 : a * L < a * x := mul_lt_mul_of_pos_left hx ha'
    have h2 : b * L ≤ b * y := mul_le_mul_of_nonneg_left hy.le hb
    have h3 : a * L + b * L = L := by rw [← add_mul, hab, one_mul]
    linarith

private lemma strict_convex_comb_ub {a b x y U : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : x < U) (hy : y < U) : a * x + b * y < U := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp at hab; subst hab; simp; linarith
  · have h1 : a * x < a * U := mul_lt_mul_of_pos_left hx ha'
    have h2 : b * y ≤ b * U := mul_le_mul_of_nonneg_left hy.le hb
    have h3 : a * U + b * U = U := by rw [← add_mul, hab, one_mul]
    linarith

private lemma fdBox_convex (M : ℝ) : Convex ℝ (fdBox M) := by
  intro x hx y hy a b ha hb hab
  simp only [fdBox, Set.mem_setOf_eq] at hx hy ⊢
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by
    simp [add_re]
  have him : (a • x + b • y).im = a * x.im + b * y.im := by
    simp [add_im]
  exact ⟨hre ▸ strict_convex_comb_lb ha hb hab hx.1 hy.1,
         hre ▸ strict_convex_comb_ub ha hb hab hx.2.1 hy.2.1,
         him ▸ strict_convex_comb_lb ha hb hab hx.2.2.1 hy.2.2.1,
         him ▸ strict_convex_comb_ub ha hb hab hx.2.2.2 hy.2.2.2⟩

/-- Points in fdBox have positive imaginary part. -/
private lemma fdBox_im_pos {M : ℝ} {z : ℂ} (hz : z ∈ fdBox M) : 0 < z.im := by
  linarith [hz.2.2.1]

/-- |Re(fdBoundary t)| ≤ 1/2 for t ∈ [0, 5]. Each segment has Re in [-1/2, 1/2]. -/
private lemma fdBoundary_re_abs_le_half (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) :
    |(fdBoundary t).re| ≤ 1/2 := by
  by_cases h1 : t ≤ 1
  · -- seg1: Re = 1/2
    have : fdBoundary t = fdBoundary_seg1 t := fdBoundary_eq_seg1_on t ⟨ht.1, h1⟩
    rw [this]
    unfold fdBoundary_seg1; simp [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]
  · push_neg at h1
    by_cases h2 : t ≤ 2
    · -- seg2: exp(θI), θ ∈ [π/3, π/2]. Re = cos θ ∈ [0, 1/2]
      have : fdBoundary t = fdBoundary_seg2 t := fdBoundary_eq_seg2_on t ⟨h1, h2⟩
      rw [this]; unfold fdBoundary_seg2
      rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
          ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I_re]
      set θ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
      have hθ_lo : Real.pi / 3 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
      have hθ_hi : θ ≤ Real.pi / 2 := by simp only [hθ_def]; nlinarith
      have h_cos_nn : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], hθ_hi⟩
      rw [abs_of_nonneg h_cos_nn]
      -- cos θ ≤ cos(π/3) = 1/2 since cos is decreasing on [0, π]
      exact le_trans (Real.cos_le_cos_of_nonneg_of_le_pi
        (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) hθ_lo)
        (by rw [Real.cos_pi_div_three])
    · push_neg at h2
      by_cases h3 : t ≤ 3
      · -- seg3: exp(θI), θ ∈ [π/2, 2π/3]. Re = cos θ ∈ [-1/2, 0]
        have : fdBoundary t = fdBoundary_seg3 t := fdBoundary_eq_seg3_on t ⟨h2, h3⟩
        rw [this]; unfold fdBoundary_seg3
        rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
            ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
        rw [Complex.exp_ofReal_mul_I_re]
        set θ := Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) with hθ_def
        have hθ_lo : Real.pi / 2 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
        have hθ_hi : θ ≤ 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith
        have h_cos_np : Real.cos θ ≤ 0 :=
          Real.cos_nonpos_of_pi_div_two_le_of_le hθ_lo (by nlinarith [Real.pi_pos])
        rw [abs_of_nonpos h_cos_np]
        -- -cos θ ≤ -cos(2π/3) = 1/2 since cos is decreasing on [0, π]
        have h_cos_mono : Real.cos (2 * Real.pi / 3) ≤ Real.cos θ :=
          Real.cos_le_cos_of_nonneg_of_le_pi
            (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos]) (by nlinarith)
        have h_cos_val : Real.cos (2 * Real.pi / 3) = -(1/2) := by
          rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring]
          rw [Real.cos_pi_sub]; rw [Real.cos_pi_div_three]
        linarith
      · push_neg at h3
        by_cases h4 : t ≤ 4
        · -- seg4: Re = -1/2
          have : fdBoundary t = fdBoundary_seg4 t := fdBoundary_eq_seg4_on t ⟨h3, h4⟩
          rw [this]; unfold fdBoundary_seg4
          simp [add_re, neg_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]; norm_num
        · -- seg5: Re = t - 9/2 ∈ [-1/2, 1/2]
          push_neg at h4
          have : fdBoundary t = fdBoundary_seg5 t := fdBoundary_eq_seg5_on t ⟨h4, ht.2⟩
          rw [this]; unfold fdBoundary_seg5
          -- Rewrite (t : ℂ) - 9/2 as ↑(t - 9/2 : ℝ) so ofReal_re applies
          have h_sub : (t : ℂ) - 9/2 = ↑(t - 9/2 : ℝ) := by push_cast; ring
          have h_re_eq : ((t : ℂ) - 9/2 + ↑H_height * I).re = t - 9/2 := by
            conv_lhs => rw [h_sub]
            simp [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]
          rw [h_re_eq, abs_le]; exact ⟨by linarith, by linarith [ht.2]⟩

/-- Im(fdBoundary t) ≥ √3/2 for t ∈ [0, 5]. -/
private lemma fdBoundary_im_ge_sqrt3_div_2 (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) :
    (fdBoundary t).im ≥ Real.sqrt 3 / 2 := by
  by_cases h1 : t ≤ 1
  · have : fdBoundary t = fdBoundary_seg1 t := fdBoundary_eq_seg1_on t ⟨ht.1, h1⟩
    rw [this]; show (fdBoundary_seg1 t).im ≥ _
    have h_im : (fdBoundary_seg1 t).im = H_height - t * (H_height - Real.sqrt 3 / 2) := by
      unfold fdBoundary_seg1; simp [add_im, mul_im, ofReal_re, I_re, ofReal_im, I_im]
    rw [h_im]; have hH : H_height - Real.sqrt 3 / 2 = 1 := by unfold H_height; ring
    rw [hH]; linarith
  · push_neg at h1
    by_cases h2 : t ≤ 2
    · have : fdBoundary t = fdBoundary_seg2 t := fdBoundary_eq_seg2_on t ⟨h1, h2⟩
      rw [this]; unfold fdBoundary_seg2
      rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
          ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
      rw [Complex.exp_ofReal_mul_I_im]
      set θ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
      have hθ_lo : Real.pi / 3 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
      have hθ_hi : θ ≤ Real.pi / 2 := by simp only [hθ_def]; nlinarith
      -- sin θ ≥ sin(π/3) = √3/2 since sin is increasing on [-π/2, π/2]
      have h_sin_mono := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by nlinarith [Real.pi_pos]) hθ_hi hθ_lo
      linarith [Real.sin_pi_div_three]
    · push_neg at h2
      by_cases h3 : t ≤ 3
      · have : fdBoundary t = fdBoundary_seg3 t := fdBoundary_eq_seg3_on t ⟨h2, h3⟩
        rw [this]; unfold fdBoundary_seg3
        rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
            ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
        rw [Complex.exp_ofReal_mul_I_im]
        set θ := Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) with hθ_def
        have hθ_lo : Real.pi / 2 ≤ θ := by simp only [hθ_def]; nlinarith [Real.pi_pos]
        have hθ_hi : θ ≤ 2 * Real.pi / 3 := by simp only [hθ_def]; nlinarith
        -- sin θ = sin(π - θ), and π - θ ∈ [π/3, π/2], so sin(π-θ) ≥ sin(π/3) = √3/2
        have h_pi_sub_lo : Real.pi / 3 ≤ Real.pi - θ := by nlinarith
        have h_pi_sub_hi : Real.pi - θ ≤ Real.pi / 2 := by nlinarith
        have h_sin_eq : Real.sin θ = Real.sin (Real.pi - θ) := (Real.sin_pi_sub θ).symm
        rw [h_sin_eq]
        have h_sin_mono := Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) h_pi_sub_hi h_pi_sub_lo
        linarith [Real.sin_pi_div_three]
      · push_neg at h3
        by_cases h4 : t ≤ 4
        · have : fdBoundary t = fdBoundary_seg4 t := fdBoundary_eq_seg4_on t ⟨h3, h4⟩
          rw [this]; show (fdBoundary_seg4 t).im ≥ _
          have h_im : (fdBoundary_seg4 t).im = Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2) := by
            unfold fdBoundary_seg4; simp [add_im, mul_im, ofReal_re, I_re, ofReal_im, I_im, neg_im]
          rw [h_im]; nlinarith [H_height_gt_rho_height]
        · push_neg at h4
          have : fdBoundary t = fdBoundary_seg5 t := fdBoundary_eq_seg5_on t ⟨h4, ht.2⟩
          rw [this]; show (fdBoundary_seg5 t).im ≥ _
          have h_im : (fdBoundary_seg5 t).im = H_height := by
            unfold fdBoundary_seg5; simp [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
          rw [h_im]; unfold H_height; linarith

/-- fdBoundary image lies in fdBox M when M > H_height. -/
private lemma fdBoundary_mem_fdBox {M : ℝ} (hM : H_height < M)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) : fdBoundary t ∈ fdBox M := by
  have h_re := fdBoundary_re_abs_le_half t ht
  have h_im_lo := fdBoundary_im_ge_sqrt3_div_2 t ht
  have h_im_hi := fdBoundary_im_le_H_height t ht
  have h_sqrt3_gt_1 : 1 < Real.sqrt 3 := by
    rw [show (1:ℝ) = Real.sqrt 1 from by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  exact ⟨by linarith [abs_le.mp h_re], by linarith [abs_le.mp h_re],
         by linarith, by linarith⟩

/-- FD zeros projected to ℂ. -/
private def Sfd (zeros : Finset ℍ) : Finset ℂ := zeros.image (fun s : ℍ => (s : ℂ))

/-- ℍ → ℂ coercion is injective (subtype projection). -/
private lemma uhp_coe_injective : Function.Injective (fun s : ℍ => (s : ℂ)) :=
  Subtype.coe_injective

/-- Sum reindexing: ∑ over Sfd = ∑ over zeros. -/
private lemma sum_Sfd_eq_sum_zeros {zeros : Finset ℍ} (g : ℂ → ℂ) :
    ∑ z ∈ Sfd zeros, g z = ∑ s ∈ zeros, g (s : ℂ) :=
  Finset.sum_image (fun _ _ _ _ h => uhp_coe_injective h)

/-- FD zeros are in fdBox when the box is tall enough. -/
private lemma Sfd_in_fdBox {zeros : Finset ℍ} {M : ℝ}
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hM_zeros : ∀ s ∈ zeros, (s : ℂ).im < M) :
    ∀ s ∈ Sfd zeros, s ∈ fdBox M := by
  intro z hz
  simp only [Sfd, Finset.mem_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  have hfd := hzeros_fd s hs
  simp only [fundamentalDomain, Set.mem_setOf_eq] at hfd
  -- Bridge UpperHalfPlane coercions
  have h_re_eq : s.re = (s : ℂ).re := rfl
  have h_im_eq : s.im = (s : ℂ).im := rfl
  have h_im_pos : 0 < (s : ℂ).im := by rw [← h_im_eq]; exact s.im_pos
  have h_re_bds := abs_le.mp hfd.1
  -- From ‖s‖ ≥ 1: s.re² + s.im² ≥ 1
  have h_norm_sq : (s : ℂ).re ^ 2 + (s : ℂ).im ^ 2 ≥ 1 := by
    have h1 : ‖(s : ℂ)‖ ^ 2 = (s : ℂ).re ^ 2 + (s : ℂ).im ^ 2 := by
      show Real.sqrt (Complex.normSq (s : ℂ)) ^ 2 = _
      rw [Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]; ring
    nlinarith [sq_nonneg (‖(s : ℂ)‖ - 1), norm_nonneg (s : ℂ)]
  -- s.re² ≤ 1/4, so s.im² ≥ 3/4
  have h_im_sq : (s : ℂ).im ^ 2 ≥ 3/4 := by
    nlinarith [sq_abs (s : ℂ).re, h_re_eq]
  -- s.im > 1/2 (since s.im > 0 and im² ≥ 3/4 > 1/4)
  have h_im_gt : 1/2 < (s : ℂ).im := by
    by_contra h; push_neg at h
    nlinarith [mul_nonneg (show (0:ℝ) ≤ 1/2 - (s:ℂ).im from by linarith)
                           (show (0:ℝ) ≤ 1/2 + (s:ℂ).im from by linarith)]
  exact ⟨by linarith [h_re_eq], by linarith [h_re_eq], h_im_gt, hM_zeros s hs⟩

/-- fdBoundary avoids all points in Sfd (follows from nonvanishing). -/
private lemma fdBoundary_avoids_Sfd
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0) :
    ∀ s ∈ Sfd zeros, ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t ≠ s := by
  intro z hz t ht
  simp only [Sfd, Finset.mem_image] at hz
  obtain ⟨s, hs, rfl⟩ := hz
  exact zeros_avoid_fdBoundary_of_nonvanishing f h_nv zeros hzeros s hs t ht

/-- fdBox height strictly above H_height and all zero heights. -/
private noncomputable def fdBox_M (zeros : Finset ℍ) : ℝ :=
  if h : zeros.Nonempty then
    max (H_height + 1) (zeros.sup' h (fun s : ℍ => (s : ℂ).im) + 1)
  else H_height + 1

private lemma fdBox_M_gt_H (zeros : Finset ℍ) : H_height < fdBox_M zeros := by
  unfold fdBox_M
  split
  · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  · linarith

private lemma fdBox_M_gt_zeros {zeros : Finset ℍ} :
    ∀ s ∈ zeros, (s : ℂ).im < fdBox_M zeros := by
  intro s hs
  have hne : zeros.Nonempty := ⟨s, hs⟩
  simp only [fdBox_M, dif_pos hne]
  calc (s : ℂ).im ≤ zeros.sup' hne (fun s : ℍ => (s : ℂ).im) :=
        Finset.le_sup' (fun s : ℍ => (s : ℂ).im) hs
    _ < zeros.sup' hne (fun s : ℍ => (s : ℂ).im) + 1 := by linarith
    _ ≤ max (H_height + 1) (zeros.sup' hne (fun s : ℍ => (s : ℂ).im) + 1) :=
        le_max_right _ _

/-! ### Patched logDeriv infrastructure

To apply `integral_eq_sum_residues_of_avoids`, we need `ContinuousAt` of the regular part
at each simple pole. This fails for raw `logDeriv` due to Lean's `div_zero` convention.
Solution: define a "patched" function that equals `logDeriv` off the pole set and takes
the correct regular-part value at each pole. -/

omit hf in
private lemma limUnder_congr_local {F : Filter ℂ} {f g : ℂ → ℂ}
    (h : f =ᶠ[F] g) : limUnder F f = limUnder F g := by
  unfold limUnder; congr 1; exact Filter.map_congr h

omit hf in
private lemma residueSimplePole_congr_local (f g : ℂ → ℂ) (z₀ : ℂ)
    (h : f =ᶠ[𝓝[≠] z₀] g) : residueSimplePole f z₀ = residueSimplePole g z₀ := by
  unfold residueSimplePole
  exact limUnder_congr_local (h.mono fun z hz => by show (z - z₀) * f z = (z - z₀) * g z; rw [hz])

omit hf in
/-- The residue of a function with a simple pole equals the Laurent coefficient `c`. -/
private lemma residueSimplePole_eq_hasSimplePoleAt_coeff {F : ℂ → ℂ} {z₀ c : ℂ} {g : ℂ → ℂ}
    (hg_an : AnalyticAt ℂ g z₀)
    (heq : ∀ᶠ z in 𝓝[≠] z₀, F z = c / (z - z₀) + g z) :
    residueSimplePole F z₀ = c := by
  unfold residueSimplePole
  apply Filter.Tendsto.limUnder_eq
  -- (z - z₀) * F z =ᶠ c + (z - z₀) * g z
  have h_ne : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ :=
    eventually_nhdsWithin_of_forall fun z (hz : z ∈ ({z₀} : Set ℂ)ᶜ) => hz
  have h_eq : ∀ᶠ z in 𝓝[≠] z₀, (z - z₀) * F z = c + (z - z₀) * g z := by
    filter_upwards [heq, h_ne] with z hz hzne
    rw [hz]; field_simp [sub_ne_zero.mpr hzne]
  -- c + (z - z₀) * g z → c
  have h_sub : Filter.Tendsto (fun z => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
    rw [show (0 : ℂ) = z₀ - z₀ from (sub_self z₀).symm]
    exact (continuous_sub_right z₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_g : Filter.Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) :=
    hg_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_sum : Filter.Tendsto (fun z => c + (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 c) := by
    have h_prod := h_sub.mul h_g
    simp only [zero_mul] at h_prod
    have := h_prod.const_add c
    rwa [add_zero] at this
  exact Filter.Tendsto.congr' (h_eq.mono fun z hz => hz.symm) h_sum

omit hf in
/-- Patched logDeriv: at each pole s ∈ S0, replace value with regular-part value g(s)
from the `HasSimplePoleAt` witness. Elsewhere, equal to `F`. -/
private noncomputable def logDeriv_patched (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) : ℂ → ℂ := fun z =>
  if h : z ∈ S0 then
    Classical.choose (Classical.choose_spec (hsp z h)) z
  else F z

omit hf in
private lemma logDeriv_patched_eq_raw_off_S0 (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) {z : ℂ} (hz : z ∉ S0) :
    logDeriv_patched F S0 hsp z = F z :=
  dif_neg hz

omit hf in
private lemma logDeriv_patched_eventuallyEq_raw_punctured (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (hs : s ∈ S0) :
    logDeriv_patched F S0 hsp =ᶠ[𝓝[≠] s] F := by
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  have h_open : IsOpen ((↑(S0.erase s) : Set ℂ)ᶜ) :=
    (S0.erase s).finite_toSet.isClosed.isOpen_compl
  have h_s_mem : s ∈ ((↑(S0.erase s) : Set ℂ)ᶜ) := by
    simp [Set.mem_compl_iff, Finset.mem_coe, Finset.mem_erase]
  filter_upwards [h_open.mem_nhds h_s_mem] with z hz hzne
  exact dif_neg (fun habs => hz (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzne, habs⟩)))

omit hf in
private lemma hasSimplePoleAt_logDeriv_patched (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (hs : s ∈ S0) :
    HasSimplePoleAt (logDeriv_patched F S0 hsp) s := by
  obtain ⟨c, g, hg_an, hF_eq⟩ := hsp s hs
  exact ⟨c, g, hg_an, by
    filter_upwards [logDeriv_patched_eventuallyEq_raw_punctured F S0 hsp s hs, hF_eq]
      with z h1 h2
    rw [h1]; exact h2⟩

omit hf in
private lemma residue_logDeriv_patched_eq_raw (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (hs : s ∈ S0) :
    residueSimplePole (logDeriv_patched F S0 hsp) s = residueSimplePole F s :=
  residueSimplePole_congr_local _ _ _
    (logDeriv_patched_eventuallyEq_raw_punctured F S0 hsp s hs)

omit hf in
/-- The patched logDeriv satisfies the ContinuousAt condition for the residue theorem. -/
private lemma logDeriv_patched_hf_ext (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) :
    ∀ s ∈ S0, ContinuousAt
      (fun z => logDeriv_patched F S0 hsp z -
        residueSimplePole (logDeriv_patched F S0 hsp) s / (z - s)) s := by
  intro s hs
  -- Use set/have to maintain definitional equality with logDeriv_patched
  -- (obtain would make g opaque, breaking the match with Classical.choose)
  set c := (hsp s hs).choose with hc_def
  set g := (hsp s hs).choose_spec.choose with hg_def
  have hg_an : AnalyticAt ℂ g s := (hsp s hs).choose_spec.choose_spec.1
  have hF_eq : ∀ᶠ z in 𝓝[≠] s, F z = c / (z - s) + g z :=
    (hsp s hs).choose_spec.choose_spec.2
  have h_res : residueSimplePole (logDeriv_patched F S0 hsp) s = c := by
    rw [residue_logDeriv_patched_eq_raw F S0 hsp s hs]
    exact residueSimplePole_eq_hasSimplePoleAt_coeff hg_an hF_eq
  rw [h_res]
  -- The function z ↦ Fp(z) - c/(z-s) equals g near s (including at s via div_zero)
  -- ContinuousAt g s follows from analyticity; transfer via eventuallyEq
  apply ContinuousAt.congr hg_an.continuousAt
  -- Goal: g =ᶠ[𝓝 s] fun z => Fp z - c/(z-s)
  have h_open_compl : IsOpen ((↑(S0.erase s) : Set ℂ)ᶜ) :=
    (S0.erase s).finite_toSet.isClosed.isOpen_compl
  rw [eventually_nhdsWithin_iff] at hF_eq
  rw [Filter.EventuallyEq]
  filter_upwards [hF_eq, h_open_compl.mem_nhds (by simp : s ∈ (↑(S0.erase s) : Set ℂ)ᶜ)]
    with z hz_F hz_compl
  by_cases hzs : z = s
  · -- At z = s: g(s) = Fp(s) - c/(s-s) = Fp(s) - 0 = Fp(s) = g(s) by defn
    subst hzs
    simp only [sub_self, div_zero, sub_zero]
    -- g z = logDeriv_patched F S0 hsp z; both sides are definitionally equal via set
    unfold logDeriv_patched
    rw [dif_pos hs]
  · -- z ≠ s, z ∉ S0: Fp(z) = F(z) = c/(z-s) + g(z), so g(z) = F(z) - c/(z-s)
    have hz_not_S0 : z ∉ S0 :=
      fun habs => hz_compl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzs, habs⟩))
    rw [logDeriv_patched_eq_raw_off_S0 F S0 hsp hz_not_S0]
    rw [show F z = c / (z - s) + g z from hz_F hzs]; ring

include hf in
/-- Proven core of the residue theorem application to `logDeriv F` along `fdBoundary`.
Takes `h_noExtraZeros` as explicit hypothesis: no zeros of `f` in `fdBox` outside `Sfd`.

The proof uses the **patched integrand** `logDeriv_patched` to fix the `ContinuousAt`
issue caused by Lean's div_zero convention, and `analyticAt_logDeriv_off_zeros` for
differentiability. All 11 hypotheses of `integral_eq_sum_residues_of_avoids` are discharged. -/
private lemma integral_logDeriv_eq_sum_winding_residue_of_noExtraZeros
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_noExtraZeros : ∀ z ∈ fdBox (fdBox_M zeros) \ ↑(Sfd zeros),
        modularFormCompOfComplex f z ≠ 0) :
    pv_integral f fdBoundary 0 5 =
      2 * Real.pi * I * ∑ s ∈ zeros,
        generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) *
          residueSimplePole (logDeriv (modularFormCompOfComplex f)) (s : ℂ) := by
  set M := fdBox_M zeros with hM_def
  set U := fdBox M with hU_def
  set S0 := Sfd zeros with hS0_def
  set F := logDeriv (modularFormCompOfComplex f) with hF_def
  have hU_open : IsOpen U := fdBox_isOpen M
  have hU_convex : Convex ℝ U := fdBox_convex M
  have hS0_in_U : ∀ s ∈ S0, s ∈ U := Sfd_in_fdBox hzeros_fd fdBox_M_gt_zeros
  have hγ_closed : fdBoundaryCurve.IsClosed := fdBoundaryImmersion_closed
  have hγ_in_U : ∀ t ∈ Icc fdBoundaryCurve.a fdBoundaryCurve.b, fdBoundaryCurve.toFun t ∈ U := by
    intro t ht; show fdBoundary t ∈ fdBox M
    exact fdBoundary_mem_fdBox (fdBox_M_gt_H zeros) t ht
  have hγ_avoids : ∀ s ∈ S0, ∀ t ∈ Icc fdBoundaryCurve.a fdBoundaryCurve.b,
      fdBoundaryCurve.toFun t ≠ s :=
    fdBoundary_avoids_Sfd f h_nv zeros hzeros
  have hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt F s := by
    intro z hz
    simp only [hS0_def, Sfd, Finset.mem_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    exact hasSimplePoleAt_logDeriv_of_zero' f hf s (hzeros s hs)
  have hγ'_bdd := piecewiseC1Immersion_deriv_bounded fdBoundaryImmersion
  -- Patched integrand: fixes ContinuousAt issue at poles (div_zero convention)
  set Fp := logDeriv_patched F S0 hSimplePoles with hFp_def
  -- DifferentiableOn Fp: agrees with F on U \ S0 where F is analytic (no extra zeros)
  have hFp_diff : DifferentiableOn ℂ Fp (U \ S0) := by
    intro z hz
    have h_ev : Fp =ᶠ[𝓝 z] F := by
      have h_open : IsOpen ((↑S0 : Set ℂ)ᶜ) := S0.finite_toSet.isClosed.isOpen_compl
      filter_upwards [h_open.mem_nhds hz.2] with w hw
      exact logDeriv_patched_eq_raw_off_S0 F S0 hSimplePoles hw
    exact (h_ev.differentiableAt_iff.mpr
      (analyticAt_logDeriv_off_zeros f z (fdBox_im_pos hz.1)
        (h_noExtraZeros z hz)).differentiableAt).differentiableWithinAt
  -- Apply residue theorem to Fp (all hypotheses discharged)
  have h_res := integral_eq_sum_residues_of_avoids U hU_open hU_convex S0 hS0_in_U Fp hFp_diff
    fdBoundaryCurve hγ_closed hγ_in_U hγ_avoids
    (fun s hs => hasSimplePoleAt_logDeriv_patched F S0 hSimplePoles s hs)
    (logDeriv_patched_hf_ext F S0 hSimplePoles) hγ'_bdd
  rw [show fdBoundaryCurve.a = (0:ℝ) from rfl, show fdBoundaryCurve.b = (5:ℝ) from rfl] at h_res
  rw [show fdBoundaryCurve.toFun = fdBoundary from rfl] at h_res
  -- Rewrite LHS: Fp(γ(t)) = F(γ(t)) since curve avoids S0
  have h_lhs : Set.EqOn (fun t => Fp (fdBoundary t) * deriv fdBoundary t)
      (fun t => F (fdBoundary t) * deriv fdBoundary t) (Set.uIcc 0 5) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at ht
    show Fp (fdBoundary t) * deriv fdBoundary t = F (fdBoundary t) * deriv fdBoundary t
    rw [show Fp (fdBoundary t) = F (fdBoundary t) from
      logDeriv_patched_eq_raw_off_S0 F S0 hSimplePoles
        (fun habs => hγ_avoids (fdBoundary t) habs t ht rfl)]
  rw [intervalIntegral.integral_congr h_lhs] at h_res
  -- Rewrite RHS: residueSimplePole(Fp, s) = residueSimplePole(F, s) at each pole
  have h_rhs : ∑ s ∈ S0, generalizedWindingNumber' fdBoundary 0 5 s *
      residueSimplePole Fp s = ∑ s ∈ S0, generalizedWindingNumber' fdBoundary 0 5 s *
      residueSimplePole F s :=
    Finset.sum_congr rfl fun s hs => by
      congr 1; exact residue_logDeriv_patched_eq_raw F S0 hSimplePoles s hs
  rw [h_rhs] at h_res
  show pv_integral f fdBoundary 0 5 = _
  unfold pv_integral
  rw [h_res, hS0_def, sum_Sfd_eq_sum_zeros]

/-! ### Helper Lemmas for Sbox Approach -/

omit hf in
/-- 1/2 < fdBox_M zeros (needed for finiteness). -/
private lemma fdBox_M_half_lt (zeros : Finset ℍ) : (1:ℝ)/2 < fdBox_M zeros := by
  have h1 : H_height > Real.sqrt 3 / 2 := H_height_gt_rho_height
  have h2 : (1:ℝ)/2 < Real.sqrt 3 / 2 := by
    have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)
    have hpos : Real.sqrt 3 > 0 := Real.sqrt_pos_of_pos (by norm_num : (3:ℝ) > 0)
    nlinarith
  have h3 := fdBox_M_gt_H zeros
  linarith

include hf in
/-- Zeros of a nonzero modular form in fdBox M form a finite set.
Proof: by contradiction, an infinite zero set in a bounded box would have an accumulation
point (Bolzano-Weierstrass) in the upper half plane, so the identity principle forces
f = 0 on all of ℍ, contradicting hf. -/
private lemma finite_zeros_in_fdBox {M : ℝ} (hM : (1:ℝ)/2 < M) :
    Set.Finite {z ∈ fdBox M | modularFormCompOfComplex f z = 0} := by
  by_contra h_inf
  -- Z is the infinite zero set
  set Z := {z ∈ fdBox M | modularFormCompOfComplex f z = 0} with hZ_def
  have hZ_inf : Z.Infinite := h_inf
  -- Step 1: fdBox M is bounded (all points have |re| < 1 and |im| < M, so ‖z‖ ≤ 1 + M)
  have hBdd : Bornology.IsBounded (fdBox M) := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨1 + M, fun z hz => by
      calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
        _ ≤ 1 + M := by
          have hre : |z.re| < 1 := by
            rw [abs_lt]; exact ⟨by linarith [hz.1], hz.2.1⟩
          have him : |z.im| ≤ M := by
            rw [abs_le]; constructor <;> linarith [hz.2.2.1, hz.2.2.2]
          linarith⟩
  -- Step 2: closure(fdBox M) is compact in ProperSpace ℂ
  have hK : IsCompact (closure (fdBox M)) := hBdd.isCompact_closure
  -- Step 3: Z ⊆ closure(fdBox M)
  have hZ_sub : Z ⊆ closure (fdBox M) :=
    (Set.sep_subset _ _).trans subset_closure
  -- Step 4: Bolzano-Weierstrass — get accumulation point z₀
  obtain ⟨z₀, hz₀K, hz₀_acc⟩ := hZ_inf.exists_accPt_of_subset_isCompact hK hZ_sub
  -- Step 5: z₀.im ≥ 1/2 (from closure of fdBox M ⊆ {z | 1/2 ≤ z.im})
  have hz₀_im : (1:ℝ)/2 ≤ z₀.im := by
    have h_closed : IsClosed {z : ℂ | (1:ℝ)/2 ≤ z.im} :=
      isClosed_le continuous_const Complex.continuous_im
    have h_sub : fdBox M ⊆ {z : ℂ | (1:ℝ)/2 ≤ z.im} :=
      fun z hz => le_of_lt hz.2.2.1
    exact closure_minimal h_sub h_closed hz₀K
  have hz₀_pos : 0 < z₀.im := by linarith
  -- Step 6: Zeros frequently approach z₀ in punctured neighborhoods
  have h_freq : ∃ᶠ y in 𝓝[≠] z₀, modularFormCompOfComplex f y = 0 := by
    have h1 := accPt_iff_frequently_nhdsNE.mp hz₀_acc
    exact h1.mono fun y hy => hy.2
  -- Step 7: f is analytic on the upper half plane
  let U := {z : ℂ | 0 < z.im}
  have hU_open : IsOpen U := UpperHalfPlane.isOpen_upperHalfPlaneSet
  have h_diffOn : DifferentiableOn ℂ (modularFormCompOfComplex f) U :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  have h_analOn : AnalyticOnNhd ℂ (modularFormCompOfComplex f) U :=
    fun z hz => h_diffOn.analyticAt (hU_open.mem_nhds hz)
  -- Step 8: U is preconnected (ℍ is connected)
  have h_preconn : IsPreconnected U := by
    have : IsConnected U := by
      apply Complex.isConnected_of_upperHalfPlane (r := (0 : ℝ))
      · intro z (hz : (0 : ℝ) < z.im); exact hz
      · intro z (hz : (0 : ℝ) < z.im); exact le_of_lt hz
    exact this.isPreconnected
  -- Step 9: z₀ ∈ U
  have hz₀_in_U : z₀ ∈ U := hz₀_pos
  -- Step 10: By identity principle, f = 0 on all of U
  have h_zero_on_U : Set.EqOn (modularFormCompOfComplex f) 0 U :=
    h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero h_preconn hz₀_in_U h_freq
  -- Step 11: f = 0 on all of ℍ, contradicting hf
  apply hf
  ext z
  simp only [ModularForm.coe_zero, Pi.zero_apply]
  have hz_in_U : (z : ℂ) ∈ U := z.im_pos
  have h_eq := h_zero_on_U hz_in_U
  simp only [Pi.zero_apply, modularFormCompOfComplex, Function.comp_apply,
    UpperHalfPlane.ofComplex_apply] at h_eq
  exact h_eq

include hf in
/-- A nonzero modular form has finitely many zeros in `fdBox M`.

Proof: by Bolzano-Weierstrass, infinitely many zeros in a bounded box would produce
an accumulation point in ℍ, and the identity principle would force `f = 0`. -/
theorem modularForm_finitely_many_zeros_in_fdBox {M : ℝ} (hM : (1:ℝ)/2 < M) :
    Set.Finite {z ∈ fdBox M | modularFormCompOfComplex f z = 0} :=
  finite_zeros_in_fdBox f hf hM

/-- All zeros of f in fdBox M as a Finset ℂ. -/
private noncomputable def allZerosInFdBox {M : ℝ} (hM : (1:ℝ)/2 < M) : Finset ℂ :=
  (finite_zeros_in_fdBox f hf hM).toFinset

/-- Membership characterization for allZerosInFdBox. -/
private lemma mem_allZerosInFdBox_iff {M : ℝ} (hM : (1:ℝ)/2 < M) {z : ℂ} :
    z ∈ allZerosInFdBox f hf hM ↔ z ∈ fdBox M ∧ modularFormCompOfComplex f z = 0 := by
  simp only [allZerosInFdBox, Set.Finite.mem_toFinset, Set.mem_sep_iff]

/-- FD zeros (Sfd) are contained in allZerosInFdBox. -/
private lemma Sfd_sub_allZeros {zeros : Finset ℍ}
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain) :
    ∀ s ∈ Sfd zeros, s ∈ allZerosInFdBox f hf (fdBox_M_half_lt zeros) := by
  intro z hz
  rw [mem_allZerosInFdBox_iff]
  constructor
  · exact Sfd_in_fdBox hzeros_fd fdBox_M_gt_zeros z hz
  · simp only [Sfd, Finset.mem_image] at hz
    obtain ⟨s, hs, rfl⟩ := hz
    show modularFormCompOfComplex f (s : ℂ) = 0
    change (f ∘ UpperHalfPlane.ofComplex) (s : ℂ) = 0
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos s.im_pos]
    exact hzeros s hs

/-- logDeriv (modularFormCompOfComplex f) has a simple pole at each zero in allZerosInFdBox. -/
private lemma hasSimplePoleAt_at_allZero {M : ℝ} (hM : (1:ℝ)/2 < M) (z : ℂ)
    (hz : z ∈ allZerosInFdBox f hf hM) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) z := by
  rw [mem_allZerosInFdBox_iff] at hz
  have h_im : 0 < z.im := fdBox_im_pos hz.1
  -- Construct the ℍ-point
  set s : ℍ := ⟨z, h_im⟩ with hs_def
  have h_fs : f s = 0 := by
    have : modularFormCompOfComplex f z = 0 := hz.2
    change (f ∘ UpperHalfPlane.ofComplex) z = 0 at this
    rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos h_im] at this
    exact this
  have := hasSimplePoleAt_logDeriv_of_zero' f hf s h_fs
  convert this using 1

/-- fdBoundary avoids allZerosInFdBox (since f(γ(t)) ≠ 0 on the curve). -/
private lemma fdBoundary_avoids_allZeros {M : ℝ} (hM : (1:ℝ)/2 < M)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0) :
    ∀ s ∈ allZerosInFdBox f hf hM, ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t ≠ s := by
  intro s hs t ht heq
  rw [mem_allZerosInFdBox_iff] at hs
  exact h_nv t ht (heq ▸ hs.2)

/-- ‖fdBoundary t‖ ≥ 1 for t ∈ [0, 5].
Segments 2,3 are on the unit circle; segments 1,4 have re = ±1/2, im ≥ √3/2;
segment 5 has im = H_height > 1. -/
private lemma fdBoundary_norm_ge_one (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) :
    ‖fdBoundary t‖ ≥ 1 := by
  -- Strategy: show ‖z‖² ≥ 1, then conclude ‖z‖ ≥ 1
  suffices h : 1 ≤ ‖fdBoundary t‖ ^ 2 by
    nlinarith [norm_nonneg (fdBoundary t)]
  rw [Complex.sq_norm]
  by_cases h1 : t ≤ 1
  · -- seg1: re = 1/2, im ≥ √3/2, so normSq = 1/4 + im² ≥ 1
    have hseg : fdBoundary t = fdBoundary_seg1 t := fdBoundary_eq_seg1_on t ⟨ht.1, h1⟩
    rw [hseg, Complex.normSq_apply]
    have h_re : (fdBoundary_seg1 t).re = 1/2 := by
      unfold fdBoundary_seg1; simp [add_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]
    have h_im_ge : (fdBoundary_seg1 t).im ≥ Real.sqrt 3 / 2 := by
      have h_im : (fdBoundary_seg1 t).im = H_height - t * (H_height - Real.sqrt 3 / 2) := by
        unfold fdBoundary_seg1; simp [add_im, mul_im, ofReal_re, I_re, ofReal_im, I_im]
      have hH : H_height - Real.sqrt 3 / 2 = 1 := by unfold H_height; ring
      rw [h_im, hH]; linarith
    rw [h_re]
    -- Goal: 1 ≤ 1/2 * (1/2) + im * im where im ≥ √3/2
    -- im ≥ √3/2 ≥ 0 so im² ≥ 3/4 and total ≥ 1/4 + 3/4 = 1
    have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
    have h_sqrt3_pos : Real.sqrt 3 / 2 ≥ 0 := by positivity
    nlinarith [mul_self_nonneg ((fdBoundary_seg1 t).im - Real.sqrt 3 / 2)]
  · push_neg at h1
    by_cases h2 : t ≤ 2
    · -- seg2: on unit circle
      have hseg : fdBoundary t = fdBoundary_seg2 t := fdBoundary_eq_seg2_on t ⟨h1, h2⟩
      rw [hseg]; rw [show Complex.normSq (fdBoundary_seg2 t) = ‖fdBoundary_seg2 t‖ ^ 2 from
        (Complex.sq_norm _).symm]; rw [norm_fdBoundary_seg2_eq_one]; norm_num
    · push_neg at h2
      by_cases h3 : t ≤ 3
      · -- seg3: on unit circle
        have hseg : fdBoundary t = fdBoundary_seg3 t := fdBoundary_eq_seg3_on t ⟨h2, h3⟩
        rw [hseg]; rw [show Complex.normSq (fdBoundary_seg3 t) = ‖fdBoundary_seg3 t‖ ^ 2 from
          (Complex.sq_norm _).symm]; rw [norm_fdBoundary_seg3_eq_one]; norm_num
      · push_neg at h3
        by_cases h4 : t ≤ 4
        · -- seg4: re = -1/2, im ≥ √3/2
          have hseg : fdBoundary t = fdBoundary_seg4 t := fdBoundary_eq_seg4_on t ⟨h3, h4⟩
          rw [hseg, Complex.normSq_apply]
          have h_re : (fdBoundary_seg4 t).re = -1/2 := by
            unfold fdBoundary_seg4
            simp [add_re, neg_re, ofReal_re, mul_re, I_re, ofReal_im, I_im]
          have h_im_ge : (fdBoundary_seg4 t).im ≥ Real.sqrt 3 / 2 := by
            have h_im : (fdBoundary_seg4 t).im =
                Real.sqrt 3 / 2 + (t - 3) * (H_height - Real.sqrt 3 / 2) := by
              unfold fdBoundary_seg4
              simp [add_im, mul_im, ofReal_re, I_re, ofReal_im, I_im, neg_im]
            rw [h_im]; nlinarith [H_height_gt_rho_height]
          rw [h_re]
          have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 :=
            Real.mul_self_sqrt (by norm_num : (3:ℝ) ≥ 0)
          have h_sqrt3_pos : (0:ℝ) ≤ Real.sqrt 3 / 2 := by positivity
          have h_im_mul : Real.sqrt 3 / 2 * (fdBoundary_seg4 t).im ≥
              Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) :=
            mul_le_mul_of_nonneg_left h_im_ge h_sqrt3_pos
          nlinarith [mul_self_nonneg ((fdBoundary_seg4 t).im - Real.sqrt 3 / 2)]
        · -- seg5: im = H_height > 1
          push_neg at h4
          have hseg : fdBoundary t = fdBoundary_seg5 t := fdBoundary_eq_seg5_on t ⟨h4, ht.2⟩
          rw [hseg, Complex.normSq_apply]
          have h_im : (fdBoundary_seg5 t).im = H_height := by
            unfold fdBoundary_seg5
            simp [add_im, sub_im, ofReal_im, mul_im, ofReal_re, I_re, I_im]
          nlinarith [H_height_gt_one, sq_nonneg (fdBoundary_seg5 t).re,
                     sq_nonneg ((fdBoundary_seg5 t).im - 1)]

/-- Winding number = 0 for points in fdBox that are NOT in the fundamental domain.
These points are either to the left/right of the vertical strip |Re| ≤ 1/2
(so separated from the curve in the real direction) or inside the unit disk
(separated from the curve which stays on/outside the unit circle).
In all cases, FTC with a Complex.log antiderivative gives ∫ = 0. -/
private lemma winding_zero_for_non_fd_point {zeros : Finset ℍ} (z₀ : ℂ)
    (hz₀_zero : z₀ ∈ allZerosInFdBox f hf (fdBox_M_half_lt zeros))
    (hz₀_not_sfd : z₀ ∉ Sfd zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) :
    generalizedWindingNumber' fdBoundary 0 5 z₀ = 0 := by
  -- Extract z₀ properties from allZerosInFdBox
  rw [mem_allZerosInFdBox_iff] at hz₀_zero
  have hz₀_box : z₀ ∈ fdBox (fdBox_M zeros) := hz₀_zero.1
  have hz₀_zero_f : modularFormCompOfComplex f z₀ = 0 := hz₀_zero.2
  have hz₀_im_pos : 0 < z₀.im := fdBox_im_pos hz₀_box
  -- Step 1: z₀ is not on the curve (f(z₀) = 0 but f(γ(t)) ≠ 0)
  have h_off : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t ≠ z₀ := by
    intro t ht heq; exact h_nv t ht (heq ▸ hz₀_zero_f)
  -- Step 2: z₀ ∉ fundamentalDomain
  have hz₀_not_fd : ¬ (|z₀.re| ≤ 1/2 ∧ ‖z₀‖ ≥ 1) := by
    intro ⟨h_re, h_norm⟩
    -- If z₀ were in FD conditions, form the ℍ-point
    set s : ℍ := ⟨z₀, hz₀_im_pos⟩ with hs_def
    have h_fs : f s = 0 := by
      have : modularFormCompOfComplex f z₀ = 0 := hz₀_zero_f
      change (f ∘ UpperHalfPlane.ofComplex) z₀ = 0 at this
      rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz₀_im_pos] at this
      exact this
    have h_fd : s ∈ fundamentalDomain := by
      simp only [fundamentalDomain, mem_setOf_eq]
      refine ⟨?_, h_norm⟩
      show |s.re| ≤ 1/2
      have : s.re = z₀.re := rfl
      rw [this]; exact h_re
    have h_in_zeros : s ∈ zeros := hzeros_complete s h_fd h_fs
    -- Then (s : ℂ) = z₀ ∈ Sfd zeros
    have : z₀ ∈ Sfd zeros := by
      simp only [Sfd, Finset.mem_image]; exact ⟨s, h_in_zeros, rfl⟩
    exact hz₀_not_sfd this
  -- Step 3: Case split on which FD condition fails
  push_neg at hz₀_not_fd
  -- Step 4: Convert PV winding number to classical integral
  have h_classical := generalizedWindingNumber_eq_classical_away fdBoundaryCurve z₀
    (by intro t ht; exact h_off t ht)
  rw [show fdBoundaryCurve.toFun = fdBoundary from rfl,
      show fdBoundaryCurve.a = (0:ℝ) from rfl,
      show fdBoundaryCurve.b = (5:ℝ) from rfl] at h_classical
  rw [h_classical]
  -- Step 5: Show the integral is 0 by FTC
  suffices h_int : ∫ t in (0:ℝ)..5,
      (fdBoundary t - z₀)⁻¹ * deriv fdBoundary t = 0 by
    rw [h_int]; simp
  -- Case split: either |z₀.re| > 1/2 or ‖z₀‖ < 1
  by_cases h_re_half : |z₀.re| ≤ 1/2
  · -- Case C: |z₀.re| ≤ 1/2 and ‖z₀‖ < 1
    have h_norm_lt : ‖z₀‖ < 1 := by
      exact hz₀_not_fd h_re_half
    -- Use antiderivative F(t) = log((-I) * (fdBoundary t - z₀))
    -- Slit plane: (-I)(w-z₀) ∈ slitPlane because ‖w‖ ≥ 1 > ‖z₀‖
    have h_slit : ∀ t ∈ Icc (0:ℝ) 5,
        (-I) * (fdBoundary t - z₀) ∈ Complex.slitPlane := by
      intro t ht
      rw [Complex.mem_slitPlane_iff]
      -- re((-I)(w-z₀)) = im(w) - z₀.im; im((-I)(w-z₀)) = -(re(w) - z₀.re)
      by_contra h_not_slit
      push_neg at h_not_slit
      have h_re_neg_I : ((-I) * (fdBoundary t - z₀)).re = (fdBoundary t).im - z₀.im := by
        simp [mul_re, neg_re, neg_im, I_re, I_im, sub_re, sub_im]
      have h_im_neg_I : ((-I) * (fdBoundary t - z₀)).im = -((fdBoundary t).re - z₀.re) := by
        simp [mul_im, neg_re, neg_im, I_re, I_im, sub_re, sub_im]
      have h1 : (fdBoundary t).im ≤ z₀.im := by linarith [h_re_neg_I ▸ h_not_slit.1]
      have h2 : (fdBoundary t).re = z₀.re := by
        have := h_not_slit.2; rw [h_im_neg_I] at this; linarith
      -- Now: im(γ(t)) ≤ z₀.im and re(γ(t)) = z₀.re
      -- So ‖γ(t)‖² = z₀.re² + im(γ(t))² ≤ z₀.re² + z₀.im² = ‖z₀‖² < 1
      -- But ‖γ(t)‖ ≥ 1, contradiction
      have h_norm_curve : ‖fdBoundary t‖ ≥ 1 := fdBoundary_norm_ge_one t ht
      -- ‖z₀‖² < 1 and ‖γ(t)‖² ≥ 1
      have h_sq_norm_z₀ := Complex.sq_norm z₀
      rw [Complex.normSq_apply] at h_sq_norm_z₀
      have h_sq_norm_curve := Complex.sq_norm (fdBoundary t)
      rw [Complex.normSq_apply] at h_sq_norm_curve
      -- h_sq_norm_z₀ : ‖z₀‖^2 = z₀.re*z₀.re + z₀.im*z₀.im
      -- h_sq_norm_curve : ‖γ(t)‖^2 = re*re + im*im
      -- h_norm_lt : ‖z₀‖ < 1, h_norm_curve : ‖γ(t)‖ ≥ 1
      -- h2 : re(γ(t)) = z₀.re, h1 : im(γ(t)) ≤ z₀.im
      rw [h2] at h_sq_norm_curve
      -- γ(t).im ≤ z₀.im, both > 0, so γ(t).im² ≤ z₀.im²
      -- But ‖γ(t)‖² = z₀.re² + γ(t).im² ≥ 1 > z₀.re² + z₀.im² = ‖z₀‖²
      -- That gives γ(t).im² > z₀.im², contradiction
      -- From ‖z₀‖ < 1 and ‖z₀‖ ≥ 0: ‖z₀‖^2 < 1
      have h_z₀_sq_lt : ‖z₀‖ ^ 2 < 1 := by nlinarith [norm_nonneg z₀]
      -- From ‖γ(t)‖ ≥ 1: ‖γ(t)‖^2 ≥ 1
      have h_curve_sq_ge : ‖fdBoundary t‖ ^ 2 ≥ 1 := by nlinarith [norm_nonneg (fdBoundary t)]
      -- So z₀.re² + z₀.im² < 1 ≤ z₀.re² + γ(t).im²
      -- Hence z₀.im² < γ(t).im²
      -- But γ(t).im ≤ z₀.im and γ(t).im > 0 ⟹ γ(t).im² ≤ z₀.im²
      -- Contradiction
      have h_im_pos : 0 < (fdBoundary t).im := by
        linarith [fdBoundary_im_ge_sqrt3_div_2 t ht,
                  Real.sqrt_pos_of_pos (by norm_num : (3:ℝ) > 0)]
      -- z₀.im² ≥ γ.im² (since both positive and γ.im ≤ z₀.im)
      have h_prod : (z₀.im - (fdBoundary t).im) * (z₀.im + (fdBoundary t).im) ≥ 0 :=
        mul_nonneg (by linarith) (by linarith)
      -- h_prod expands to z₀.im² - γ.im² ≥ 0
      -- Combined with h_sq_norm_z₀, h_sq_norm_curve, h_z₀_sq_lt, h_curve_sq_ge:
      -- z₀.re² + γ.im² ≥ 1 > z₀.re² + z₀.im² ≥ z₀.re² + γ.im²
      nlinarith
    -- F(t) = log((-I) * (fdBoundary t - z₀))
    set F : ℝ → ℂ := fun t => Complex.log ((-I) * (fdBoundary t - z₀)) with hF_def
    set F' : ℝ → ℂ := fun t => (fdBoundary t - z₀)⁻¹ * deriv fdBoundary t with hF'_def
    -- (a) F is continuous on [0, 5]
    have hF_cont : ContinuousOn F (Icc 0 5) := by
      apply ContinuousOn.clog
      · exact (continuousOn_const.mul
          (fdBoundary_continuous.continuousOn.sub continuousOn_const))
      · exact h_slit
    -- (b) HasDerivAt for t ∈ (0,5) \ partition
    have hF_deriv : ∀ t ∈ Ioo (0:ℝ) 5 \ (↑fdPartition : Set ℝ),
        HasDerivAt F (F' t) t := by
      intro t ⟨ht_ioo, ht_not_P⟩
      have h_diff_bd : DifferentiableAt ℝ fdBoundary t :=
        fdBoundary_differentiableAt_off_partition t ht_ioo ht_not_P
      have h_slit_t : (-I) * (fdBoundary t - z₀) ∈ Complex.slitPlane :=
        h_slit t (Ioo_subset_Icc_self ht_ioo)
      have h_log : HasDerivAt Complex.log ((-I) * (fdBoundary t - z₀))⁻¹
          ((-I) * (fdBoundary t - z₀)) :=
        Complex.hasDerivAt_log h_slit_t
      have h_inner : HasDerivAt (fun u => (-I) * (fdBoundary u - z₀))
          ((-I) * deriv fdBoundary t) t := by
        have := (h_diff_bd.hasDerivAt.sub_const z₀).const_mul (-I)
        convert this using 1
      have h_comp := h_log.scomp t h_inner
      -- h_comp : HasDerivAt (log ∘ (fun u => (-I)*(γ(u)-z₀)))
      --          ((-I)*γ'(t)) • ((-I)*(γ(t)-z₀))⁻¹  t
      -- Need: HasDerivAt F (F' t) t where F t = log((-I)*(γ(t)-z₀))
      -- and F' t = (γ(t)-z₀)⁻¹ * γ'(t)
      -- The function parts match: (log ∘ ...) = F
      -- The derivative: smul to mul, then cancel (-I)*(-I)⁻¹
      convert h_comp using 1
      rw [smul_eq_mul]
      have hne : (-I : ℂ) ≠ 0 := by
        simp [Complex.ext_iff, I_re, I_im]
      field_simp
      ring
    -- (c) F' integrable
    have hF'_int : IntervalIntegrable F' volume 0 5 := by
      let g : ℂ → ℂ := fun z => (z - z₀)⁻¹
      have hF'_eq : F' = fun t => g (fdBoundary t) * deriv fdBoundary t := by
        ext t; simp only [hF'_def, g]
      rw [hF'_eq]
      apply intervalIntegrable_pv_integrand_piecewiseC1
        (P := fdBoundaryFullPartition) (by norm_num : (0:ℝ) ≤ 5)
      · apply ContinuousOn.inv₀
        · exact continuousOn_id.sub continuousOn_const
        · intro z ⟨t, ht, hzt⟩; rw [← hzt]; exact sub_ne_zero.mpr (h_off t ht)
      · exact fdBoundary_continuous.continuousOn
      · intro t ht
        have ht_ioo : t ∈ Ioo (0:ℝ) 5 := by
          refine ⟨lt_of_le_of_ne ht.1.1 ?_, lt_of_le_of_ne ht.1.2 ?_⟩
          · intro h; exact ht.2 (by rw [← h]; simp [fdBoundaryFullPartition])
          · intro h; exact ht.2 (by rw [h]; simp [fdBoundaryFullPartition])
        exact (fdBoundaryCurve.deriv_continuous_off_partition t ht_ioo ht.2).continuousWithinAt
      · apply continuousOn_image_bounded fdBoundary_continuous.continuousOn
        apply ContinuousOn.inv₀
        · exact continuousOn_id.sub continuousOn_const
        · intro z ⟨t, ht, hzt⟩; rw [← hzt]; exact sub_ne_zero.mpr (h_off t ht)
      · exact fdBoundaryImmersion.deriv_bounded
    -- (d) Countable exceptions
    have h_countable : (↑fdPartition : Set ℝ).Countable := fdPartition.countable_toSet
    -- (e) FTC
    have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F'
      (by norm_num : (0:ℝ) ≤ 5) h_countable hF_cont hF_deriv hF'_int
    rw [hFTC]
    -- (f) F(5) - F(0) = 0 since fdBoundary is closed
    show F 5 - F 0 = 0
    simp only [hF_def, fdBoundary_closed]; ring
  · -- Cases A/B: |z₀.re| > 1/2
    push_neg at h_re_half
    by_cases h_re_pos : z₀.re > 1/2
    · -- Case A: z₀.re > 1/2, use log(z₀ - γ(t))
      -- re(z₀ - γ(t)) = z₀.re - re(γ(t)) > 1/2 - 1/2 = 0
      have h_slit : ∀ t ∈ Icc (0:ℝ) 5, z₀ - fdBoundary t ∈ Complex.slitPlane := by
        intro t ht; rw [Complex.mem_slitPlane_iff]; left
        simp only [sub_re]
        have h_re_le := fdBoundary_re_abs_le_half t ht
        linarith [abs_le.mp h_re_le]
      set F : ℝ → ℂ := fun t => Complex.log (z₀ - fdBoundary t) with hF_def
      set F' : ℝ → ℂ := fun t => (fdBoundary t - z₀)⁻¹ * deriv fdBoundary t with hF'_def
      -- (a) F continuous
      have hF_cont : ContinuousOn F (Icc 0 5) := by
        exact (continuousOn_const.sub fdBoundary_continuous.continuousOn).clog h_slit
      -- (b) HasDerivAt
      have hF_deriv : ∀ t ∈ Ioo (0:ℝ) 5 \ (↑fdPartition : Set ℝ),
          HasDerivAt F (F' t) t := by
        intro t ⟨ht_ioo, ht_not_P⟩
        have h_diff_bd := fdBoundary_differentiableAt_off_partition t ht_ioo ht_not_P
        have h_slit_t := h_slit t (Ioo_subset_Icc_self ht_ioo)
        have h_log := Complex.hasDerivAt_log h_slit_t
        have h_sub : HasDerivAt (fun u => z₀ - fdBoundary u) (-deriv fdBoundary t) t := by
          have h := (hasDerivAt_const t z₀).sub h_diff_bd.hasDerivAt
          convert h using 1; ring
        have h_comp := h_log.scomp t h_sub
        convert h_comp using 1
        -- Goal: F' t = -deriv γ t • (z₀ - γ t)⁻¹
        -- i.e. (γ t - z₀)⁻¹ * deriv γ t = -deriv γ t * (z₀ - γ t)⁻¹
        -- Since (γ t - z₀) = -(z₀ - γ t), inv distributes the neg
        rw [smul_eq_mul]
        have h_inv_neg : (fdBoundary t - z₀)⁻¹ = -(z₀ - fdBoundary t)⁻¹ := by
          rw [show fdBoundary t - z₀ = -(z₀ - fdBoundary t) from by ring]
          rw [neg_inv]
        simp only [hF'_def, h_inv_neg]
        ring
      -- (c) F' integrable
      have hF'_int : IntervalIntegrable F' volume 0 5 := by
        let g : ℂ → ℂ := fun z => (z - z₀)⁻¹
        have hF'_eq : F' = fun t => g (fdBoundary t) * deriv fdBoundary t := by
          ext t; simp only [hF'_def, g]
        rw [hF'_eq]
        apply intervalIntegrable_pv_integrand_piecewiseC1
          (P := fdBoundaryFullPartition) (by norm_num : (0:ℝ) ≤ 5)
        · apply ContinuousOn.inv₀
          · exact continuousOn_id.sub continuousOn_const
          · intro z ⟨t, ht, hzt⟩; rw [← hzt]; exact sub_ne_zero.mpr (h_off t ht)
        · exact fdBoundary_continuous.continuousOn
        · intro t ht
          have ht_ioo : t ∈ Ioo (0:ℝ) 5 := by
            refine ⟨lt_of_le_of_ne ht.1.1 ?_, lt_of_le_of_ne ht.1.2 ?_⟩
            · intro h; exact ht.2 (by rw [← h]; simp [fdBoundaryFullPartition])
            · intro h; exact ht.2 (by rw [h]; simp [fdBoundaryFullPartition])
          exact (fdBoundaryCurve.deriv_continuous_off_partition t ht_ioo ht.2).continuousWithinAt
        · apply continuousOn_image_bounded fdBoundary_continuous.continuousOn
          apply ContinuousOn.inv₀
          · exact continuousOn_id.sub continuousOn_const
          · intro z ⟨t, ht, hzt⟩; rw [← hzt]; exact sub_ne_zero.mpr (h_off t ht)
        · exact fdBoundaryImmersion.deriv_bounded
      have h_countable : (↑fdPartition : Set ℝ).Countable := fdPartition.countable_toSet
      have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F'
        (by norm_num : (0:ℝ) ≤ 5) h_countable hF_cont hF_deriv hF'_int
      rw [hFTC]; show F 5 - F 0 = 0
      simp only [hF_def, fdBoundary_closed]; ring
    · -- Case B: z₀.re < -1/2, use log(γ(t) - z₀)
      -- re(γ(t) - z₀) = re(γ(t)) - z₀.re > -1/2 - z₀.re > 0
      have h_re_neg : z₀.re < -1/2 := by
        cases abs_cases z₀.re with
        | inl h => linarith [h.1]
        | inr h => linarith [h.1, h_re_pos]
      have h_slit : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t - z₀ ∈ Complex.slitPlane := by
        intro t ht; rw [Complex.mem_slitPlane_iff]; left
        simp only [sub_re]
        have h_re_le := fdBoundary_re_abs_le_half t ht
        linarith [abs_le.mp h_re_le]
      -- This is exactly the same as gWN_eq_zero_of_boundary_zero's approach
      set F : ℝ → ℂ := fun t => Complex.log (fdBoundary t - z₀) with hF_def
      set F' : ℝ → ℂ := fun t => (fdBoundary t - z₀)⁻¹ * deriv fdBoundary t with hF'_def
      have hF_cont : ContinuousOn F (Icc 0 5) :=
        (fdBoundary_continuous.continuousOn.sub continuousOn_const).clog h_slit
      have hF_deriv : ∀ t ∈ Ioo (0:ℝ) 5 \ (↑fdPartition : Set ℝ),
          HasDerivAt F (F' t) t := by
        intro t ⟨ht_ioo, ht_not_P⟩
        have h_diff_bd := fdBoundary_differentiableAt_off_partition t ht_ioo ht_not_P
        have h_slit_t := h_slit t (Ioo_subset_Icc_self ht_ioo)
        have h_log := Complex.hasDerivAt_log h_slit_t
        have h_sub : HasDerivAt (fun u => fdBoundary u - z₀) (deriv fdBoundary t) t :=
          h_diff_bd.hasDerivAt.sub_const _
        have h_comp := h_log.scomp t h_sub
        simp only [hF_def, hF'_def]
        have : (Complex.log ∘ fun u => fdBoundary u - z₀) = F := by ext u; simp [hF_def]
        rw [this] at h_comp; convert h_comp using 1
        rw [smul_eq_mul, mul_comm]
      have hF'_int : IntervalIntegrable F' volume 0 5 := by
        let g : ℂ → ℂ := fun z => (z - z₀)⁻¹
        have hF'_eq : F' = fun t => g (fdBoundary t) * deriv fdBoundary t := by
          ext t; simp only [hF'_def, g]
        rw [hF'_eq]
        apply intervalIntegrable_pv_integrand_piecewiseC1
          (P := fdBoundaryFullPartition) (by norm_num : (0:ℝ) ≤ 5)
        · apply ContinuousOn.inv₀
          · exact continuousOn_id.sub continuousOn_const
          · intro z ⟨t, ht, hzt⟩; rw [← hzt]; exact sub_ne_zero.mpr (h_off t ht)
        · exact fdBoundary_continuous.continuousOn
        · intro t ht
          have ht_ioo : t ∈ Ioo (0:ℝ) 5 := by
            refine ⟨lt_of_le_of_ne ht.1.1 ?_, lt_of_le_of_ne ht.1.2 ?_⟩
            · intro h; exact ht.2 (by rw [← h]; simp [fdBoundaryFullPartition])
            · intro h; exact ht.2 (by rw [h]; simp [fdBoundaryFullPartition])
          exact (fdBoundaryCurve.deriv_continuous_off_partition t ht_ioo ht.2).continuousWithinAt
        · apply continuousOn_image_bounded fdBoundary_continuous.continuousOn
          apply ContinuousOn.inv₀
          · exact continuousOn_id.sub continuousOn_const
          · intro z ⟨t, ht, hzt⟩; rw [← hzt]; exact sub_ne_zero.mpr (h_off t ht)
        · exact fdBoundaryImmersion.deriv_bounded
      have h_countable : (↑fdPartition : Set ℝ).Countable := fdPartition.countable_toSet
      have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F'
        (by norm_num : (0:ℝ) ≤ 5) h_countable hF_cont hF_deriv hF'_int
      rw [hFTC]; show F 5 - F 0 = 0
      simp only [hF_def, fdBoundary_closed]; ring

include hf in
/-- The residue theorem applied to `logDeriv F` along `fdBoundary`.

**Single remaining sorry**: deriving `h_noExtraZeros` (that `f` has no zeros in `fdBox`
outside `Sfd`) from the current hypotheses. The convex hull of `∂𝒟` extends below the
unit circle arc, potentially containing non-FD zeros of `f`. -/
private lemma integral_logDeriv_eq_sum_winding_residue
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) :
    pv_integral f fdBoundary 0 5 =
      2 * Real.pi * I * ∑ s ∈ zeros,
        generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) *
          residueSimplePole (logDeriv (modularFormCompOfComplex f)) (s : ℂ) := by
  -- New Sbox-based approach: use ALL zeros in fdBox, not just Sfd
  set M := fdBox_M zeros with hM_def
  set U := fdBox M with hU_def
  set Sbox := allZerosInFdBox f hf (fdBox_M_half_lt zeros) with hSbox_def
  set F := logDeriv (modularFormCompOfComplex f) with hF_def

  have hU_open : IsOpen U := fdBox_isOpen M
  have hU_convex : Convex ℝ U := fdBox_convex M
  have hSbox_in_U : ∀ s ∈ Sbox, s ∈ U := by
    intro s hs
    rw [mem_allZerosInFdBox_iff] at hs
    exact hs.1

  have hγ_closed : fdBoundaryCurve.IsClosed := fdBoundaryImmersion_closed
  have hγ_in_U : ∀ t ∈ Icc fdBoundaryCurve.a fdBoundaryCurve.b, fdBoundaryCurve.toFun t ∈ U := by
    intro t ht; show fdBoundary t ∈ fdBox M
    exact fdBoundary_mem_fdBox (fdBox_M_gt_H zeros) t ht
  have hγ_avoids : ∀ s ∈ Sbox, ∀ t ∈ Icc fdBoundaryCurve.a fdBoundaryCurve.b,
      fdBoundaryCurve.toFun t ≠ s :=
    fdBoundary_avoids_allZeros f hf (fdBox_M_half_lt zeros) h_nv

  have hSimplePoles : ∀ s ∈ Sbox, HasSimplePoleAt F s :=
    hasSimplePoleAt_at_allZero f hf (fdBox_M_half_lt zeros)

  have hγ'_bdd := piecewiseC1Immersion_deriv_bounded fdBoundaryImmersion

  -- Patched integrand: fixes ContinuousAt issue at poles
  set Fp := logDeriv_patched F Sbox hSimplePoles with hFp_def

  -- DifferentiableOn Fp on U \ Sbox
  have hFp_diff : DifferentiableOn ℂ Fp (U \ Sbox) := by
    intro z hz
    have h_ev : Fp =ᶠ[𝓝 z] F := by
      have h_open : IsOpen ((↑Sbox : Set ℂ)ᶜ) := Sbox.finite_toSet.isClosed.isOpen_compl
      filter_upwards [h_open.mem_nhds hz.2] with w hw
      exact logDeriv_patched_eq_raw_off_S0 F Sbox hSimplePoles hw
    -- At z, we have z ∉ Sbox, so z is NOT a zero of f (since all zeros are in Sbox)
    have hz_not_zero : modularFormCompOfComplex f z ≠ 0 := by
      intro h_zero
      have : z ∈ Sbox := by
        rw [mem_allZerosInFdBox_iff]
        exact ⟨hz.1, h_zero⟩
      exact hz.2 this
    exact (h_ev.differentiableAt_iff.mpr
      (analyticAt_logDeriv_off_zeros f z (fdBox_im_pos hz.1) hz_not_zero).differentiableAt).differentiableWithinAt

  -- Apply residue theorem to Fp
  have h_res := integral_eq_sum_residues_of_avoids U hU_open hU_convex Sbox hSbox_in_U Fp hFp_diff
    fdBoundaryCurve hγ_closed hγ_in_U hγ_avoids
    (fun s hs => hasSimplePoleAt_logDeriv_patched F Sbox hSimplePoles s hs)
    (logDeriv_patched_hf_ext F Sbox hSimplePoles) hγ'_bdd

  rw [show fdBoundaryCurve.a = (0:ℝ) from rfl, show fdBoundaryCurve.b = (5:ℝ) from rfl] at h_res
  rw [show fdBoundaryCurve.toFun = fdBoundary from rfl] at h_res

  -- Rewrite LHS: Fp(γ(t)) = F(γ(t)) since curve avoids Sbox
  have h_lhs : Set.EqOn (fun t => Fp (fdBoundary t) * deriv fdBoundary t)
      (fun t => F (fdBoundary t) * deriv fdBoundary t) (Set.uIcc 0 5) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)] at ht
    show Fp (fdBoundary t) * deriv fdBoundary t = F (fdBoundary t) * deriv fdBoundary t
    rw [show Fp (fdBoundary t) = F (fdBoundary t) from
      logDeriv_patched_eq_raw_off_S0 F Sbox hSimplePoles
        (fun habs => hγ_avoids (fdBoundary t) habs t ht rfl)]
  rw [intervalIntegral.integral_congr h_lhs] at h_res

  -- Rewrite RHS: residueSimplePole(Fp, s) = residueSimplePole(F, s) at each pole
  have h_rhs : ∑ s ∈ Sbox, generalizedWindingNumber' fdBoundary 0 5 s *
      residueSimplePole Fp s = ∑ s ∈ Sbox, generalizedWindingNumber' fdBoundary 0 5 s *
      residueSimplePole F s :=
    Finset.sum_congr rfl fun s hs => by
      congr 1; exact residue_logDeriv_patched_eq_raw F Sbox hSimplePoles s hs
  rw [h_rhs] at h_res

  -- Split Sbox = Sfd ∪ (Sbox \ Sfd) and show the difference term is 0
  have h_Sfd_sub_Sbox : Sfd zeros ⊆ Sbox := by
    intro s hs
    exact Sfd_sub_allZeros f hf hzeros hzeros_fd s hs

  -- Reindex the sum: Sbox = Sfd ∪ (Sbox \ Sfd)
  rw [show (∑ s ∈ Sbox, generalizedWindingNumber' fdBoundary 0 5 s * residueSimplePole F s) =
      (∑ s ∈ Sfd zeros, generalizedWindingNumber' fdBoundary 0 5 s *
        residueSimplePole F s) +
      (∑ s ∈ Sbox \ Sfd zeros, generalizedWindingNumber' fdBoundary 0 5 s *
        residueSimplePole F s) by
    rw [← Finset.sum_sdiff h_Sfd_sub_Sbox]; ac_rfl] at h_res

  -- Show the (Sbox \ Sfd) term = 0 using winding_zero_for_non_fd_point
  have h_diff_zero : ∑ s ∈ Sbox \ Sfd zeros, generalizedWindingNumber' fdBoundary 0 5 s *
      residueSimplePole F s = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    have h_not_sfd : s ∉ Sfd zeros := by
      simp only [Finset.mem_sdiff] at hs; exact hs.2
    have h_in_sbox : s ∈ Sbox := by
      simp only [Finset.mem_sdiff] at hs; exact hs.1
    rw [winding_zero_for_non_fd_point f hf s h_in_sbox h_not_sfd h_nv hzeros_complete, zero_mul]

  rw [h_diff_zero, add_zero] at h_res

  -- Reindex back to zeros
  show pv_integral f fdBoundary 0 5 = _
  unfold pv_integral
  rw [h_res, sum_Sfd_eq_sum_zeros]

include hf in
/-- The argument principle for f'/f on the fundamental domain boundary.

Decomposes into:
- **(A)** `integral_logDeriv_eq_sum_winding_residue`: the residue theorem (**sorry**)
- **(B)** `residue_logDeriv_eq_order`: residue of logDeriv = order of vanishing (**proven**)
-/
private lemma argument_principle_on_fdBoundary
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) :
    pv_integral f fdBoundary 0 5 =
      2 * Real.pi * I * ∑ s ∈ zeros,
        generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) *
          (orderOfVanishingAt' f s : ℂ) := by
  -- Part (A): Residue theorem application (sorry — blocked on infrastructure)
  have h_rt := integral_logDeriv_eq_sum_winding_residue f hf h_nv zeros hzeros hzeros_fd
    hzeros_complete
  -- Part (B): Convert residueSimplePole(logDeriv F) → orderOfVanishingAt' (proven)
  rw [h_rt]; congr 1
  apply Finset.sum_congr rfl
  intro s hs; congr 1
  exact residue_logDeriv_eq_order f s (hzeros s hs)

/-- Apply the generalized residue theorem to f'/f on ∂𝒟.
Takes an explicit `hf_ne : f ≠ 0` to avoid auto-including the `variable hf`
(which would propagate to `pv_equals_residue_sum` and break Core.lean). -/
private lemma h_integral_residue_of_generalizedResidueTheorem
    (hf_ne : f ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) :
    pv_integral f fdBoundary 0 5 =
      2 * Real.pi * I * ∑ s ∈ zeros,
        generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) *
          (orderOfVanishingAt' f s : ℂ) :=
  argument_principle_on_fdBoundary f hf_ne
    (nonvanishing_on_fdBoundary_of_integrable f hf_ne hint)
    zeros hzeros hzeros_fd hzeros_complete

/-! ### Helpers for Sum-Level Winding Identity -/

/-- ρ+1 is in the standard fundamental domain (|Re| = 1/2 ≤ 1/2, ‖ρ+1‖ = 1 ≥ 1). -/
private lemma ellipticPoint_rho_plus_one_mem_fd :
    ellipticPoint_rho_plus_one' ∈ fundamentalDomain := by
  simp only [fundamentalDomain, ellipticPoint_rho_plus_one', mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · simp only [UpperHalfPlane.re]; norm_num
  · rw [ge_iff_le, ← ellipticPoint_rho_plus_one_norm]; rfl

/-- T-invariance at the level of values: f(ρ+1) = f(ρ) for f ∈ M_k(Γ(1)). -/
private lemma f_at_rho_plus_one_eq_f_rho :
    f ellipticPoint_rho_plus_one' = f ellipticPoint_rho' := by
  set z₀ : ℍ := ellipticPoint_rho' with hz₀_def
  have h_period := SlashInvariantForm.vAdd_width_periodic 1 k 1
    f.toSlashInvariantForm z₀
  simp only [Nat.cast_one, mul_one, Int.cast_one] at h_period
  have h_vadd_coe : ((1 : ℝ) +ᵥ z₀ : ℍ) = ellipticPoint_rho_plus_one' := by
    apply Subtype.ext
    show ((1 : ℝ) : ℂ) + (z₀ : ℍ).val = (ellipticPoint_rho_plus_one' : ℍ).val
    simp only [hz₀_def, ellipticPoint_rho', ellipticPoint_rho_plus_one', Subtype.coe_mk]
    push_cast; ring
  rw [h_vadd_coe] at h_period
  simp only [ModularForm.toSlashInvariantForm_coe] at h_period
  exact h_period

set_option maxHeartbeats 400000 in
/-- Points in FD that are not interior and not at elliptic points lie on the fdBoundary curve
when im ≤ H_height. The three cases: ‖s‖ = 1 (on arc, IVT), |Re s| = 1/2 (on vertical side),
im s = H_height (on top horizontal). -/
private lemma fd_noninterior_on_curve (s : ℍ)
    (hs_fd : s ∈ fundamentalDomain) (hs_ne_i : s ≠ ellipticPoint_i')
    (hs_ne_rho : s ≠ ellipticPoint_rho') (hs_ne_rho1 : s ≠ ellipticPoint_rho_plus_one')
    (hs_not_int : ¬isInteriorPoint s) (hs_low : (s : ℂ).im ≤ H_height) :
    ∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = (s : ℂ) := by
  -- Extract the FD conditions
  simp only [fundamentalDomain, mem_setOf_eq] at hs_fd
  obtain ⟨h_re_abs, h_norm_ge⟩ := hs_fd
  -- Extract the negation of interior-point condition
  simp only [isInteriorPoint, not_and, not_lt] at hs_not_int
  -- Three-way case split
  rcases le_or_lt ‖(s : ℂ)‖ 1 with h_norm_le | h_norm_gt
  · -- **Case 1: ‖s‖ = 1** (on the arc)
    have h_norm_eq : ‖(s : ℂ)‖ = 1 := le_antisymm h_norm_le h_norm_ge
    -- Since ‖s‖ = 1 and |s.re| ≤ 1/2, if |s.re| = 1/2 then s = ρ or ρ+1 (contradiction)
    -- So |s.re| < 1/2
    have h_re_strict : |(s : ℂ).re| < 1/2 := by
      by_contra h_not_lt; push_neg at h_not_lt
      have h_re_eq : |(s : ℂ).re| = 1/2 := le_antisymm h_re_abs h_not_lt
      -- From ‖s‖ = 1 and |s.re| = 1/2: s.im² = 1 - 1/4 = 3/4, so s.im = √3/2
      have h_normSq : (s : ℂ).re ^ 2 + (s : ℂ).im ^ 2 = 1 := by
        have h := Complex.sq_norm (s : ℂ)
        rw [h_norm_eq, one_pow, Complex.normSq_apply] at h
        nlinarith
      have h_im_sq : (s : ℂ).im ^ 2 = 3/4 := by nlinarith [sq_abs (s : ℂ).re, h_re_eq]
      have h_im_pos : (s : ℂ).im > 0 := by exact_mod_cast s.im_pos
      have h_im_val : (s : ℂ).im = Real.sqrt 3 / 2 := by
        have h_sqrt : Real.sqrt 3 / 2 > 0 := by positivity
        nlinarith [sq_nonneg ((s : ℂ).im - Real.sqrt 3 / 2),
                   Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)]
      -- Now s.re = 1/2 or s.re = -1/2
      rcases abs_cases (s : ℂ).re with ⟨h_abs_eq, _⟩ | ⟨h_abs_eq, _⟩
      · -- s.re = 1/2: then s = 1/2 + (√3/2)I = ρ+1
        have h_re_val : (s : ℂ).re = 1/2 := by linarith [h_re_eq, h_abs_eq]
        have : s = ellipticPoint_rho_plus_one' := by
          apply UpperHalfPlane.ext
          show (s : ℂ) = (ellipticPoint_rho_plus_one' : ℂ)
          have hre_rhs : (ellipticPoint_rho_plus_one' : ℂ).re = 1/2 := by
            simp [ellipticPoint_rho_plus_one', Complex.add_re, Complex.ofReal_re,
                  Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
          have him_rhs : (ellipticPoint_rho_plus_one' : ℂ).im = Real.sqrt 3 / 2 := by
            simp [ellipticPoint_rho_plus_one', Complex.add_im, Complex.ofReal_re,
                  Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          exact Complex.ext (by linarith) (by linarith)
        exact absurd this hs_ne_rho1
      · -- s.re = -1/2: then s = -1/2 + (√3/2)I = ρ
        have h_re_val : (s : ℂ).re = -1/2 := by linarith [h_re_eq, h_abs_eq]
        have : s = ellipticPoint_rho' := by
          apply UpperHalfPlane.ext
          show (s : ℂ) = (ellipticPoint_rho' : ℂ)
          have hre_rhs : (ellipticPoint_rho' : ℂ).re = -1/2 := by
            simp [ellipticPoint_rho', Complex.add_re, Complex.neg_re, Complex.ofReal_re,
                  Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
          have him_rhs : (ellipticPoint_rho' : ℂ).im = Real.sqrt 3 / 2 := by
            simp [ellipticPoint_rho', Complex.add_im, Complex.neg_im, Complex.ofReal_re,
                  Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
          exact Complex.ext (by linarith) (by linarith)
        exact absurd this hs_ne_rho
    -- Use IVT: (fdBoundary ·).re is continuous on [1,3], goes from 1/2 to -1/2
    -- So there exists t₀ ∈ [1, 3] with (fdBoundary t₀).re = s.re
    have h_cont_re : ContinuousOn (fun t => (fdBoundary t).re) (Icc 1 3) :=
      (Complex.continuous_re.comp_continuousOn
        fdBoundary_continuous.continuousOn).mono (by intro x hx; exact hx)
    have h_re_at_1 : (fdBoundary 1).re = 1/2 := by
      rw [fdBoundary_at_one]; simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
    have h_re_at_3 : (fdBoundary 3).re = -1/2 := by
      rw [fdBoundary_at_three]; simp [ellipticPoint_rho, ellipticPoint_rho']
    have h_s_re_mem : (s : ℂ).re ∈ Icc (-1/2 : ℝ) (1/2) := by
      have h_bounds := abs_lt.mp h_re_strict
      exact ⟨by linarith [h_bounds.1], by linarith [h_bounds.2]⟩
    -- IVT: Icc (f 3) (f 1) = Icc (-1/2) (1/2) ⊆ f '' Icc 1 3
    have h_ivt : Icc ((fun t => (fdBoundary t).re) 3) ((fun t => (fdBoundary t).re) 1) ⊆
        (fun t => (fdBoundary t).re) '' Icc 1 3 :=
      intermediate_value_Icc' (by norm_num : (1:ℝ) ≤ 3) h_cont_re
    simp only at h_ivt
    rw [h_re_at_1, h_re_at_3] at h_ivt
    obtain ⟨t₀, ht₀_mem, ht₀_re⟩ := h_ivt h_s_re_mem
    -- Now show fdBoundary t₀ = (s : ℂ) by showing equal norms, equal re, equal im
    refine ⟨t₀, ?_, ?_⟩
    · exact ⟨by linarith [ht₀_mem.1], by linarith [ht₀_mem.2]⟩
    · -- Both fdBoundary t₀ and s are on the unit circle
      -- Step 1: ‖fdBoundary t₀‖ = 1
      have h_norm_curve : ‖fdBoundary t₀‖ = 1 := by
        rcases le_or_lt t₀ 1 with h_le_1 | h_gt_1
        · -- t₀ ≤ 1 and t₀ ≥ 1, so t₀ = 1
          have : t₀ = 1 := le_antisymm h_le_1 ht₀_mem.1
          rw [this, fdBoundary_at_one]; exact ellipticPoint_rho_plus_one_norm
        · rcases le_or_lt t₀ 2 with h_le_2 | h_gt_2
          · -- t₀ ∈ (1, 2]: seg2, fdBoundary t₀ = exp(angle*I)
            have h_eq : fdBoundary t₀ = fdBoundary_seg2 t₀ :=
              fdBoundary_eq_seg2_on t₀ ⟨h_gt_1, h_le_2⟩
            rw [h_eq]; unfold fdBoundary_seg2
            rw [show (↑Real.pi / 3 + (↑t₀ - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
                ↑(Real.pi / 3 + (t₀ - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
            exact Complex.norm_exp_ofReal_mul_I _
          · rcases le_or_lt t₀ 3 with h_le_3 | h_gt_3
            · -- t₀ ∈ (2, 3]: seg3
              have h_eq : fdBoundary t₀ = fdBoundary_seg3 t₀ :=
                fdBoundary_eq_seg3_on t₀ ⟨h_gt_2, h_le_3⟩
              rw [h_eq]; unfold fdBoundary_seg3
              rw [show (↑Real.pi / 2 + (↑t₀ - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
                  ↑(Real.pi / 2 + (t₀ - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
              exact Complex.norm_exp_ofReal_mul_I _
            · linarith [ht₀_mem.2]
      -- Step 2: Both on unit circle with same re → same im² → same im (both positive)
      have h_normSq_curve : (fdBoundary t₀).re ^ 2 + (fdBoundary t₀).im ^ 2 = 1 := by
        have h := Complex.sq_norm (fdBoundary t₀)
        rw [h_norm_curve, one_pow, Complex.normSq_apply] at h
        nlinarith
      have h_normSq_s : (s : ℂ).re ^ 2 + (s : ℂ).im ^ 2 = 1 := by
        have h := Complex.sq_norm (s : ℂ)
        rw [h_norm_eq, one_pow, Complex.normSq_apply] at h
        nlinarith
      have h_im_sq_eq : (fdBoundary t₀).im ^ 2 = (s : ℂ).im ^ 2 := by
        have hre : (fdBoundary t₀).re = (s : ℂ).re := ht₀_re
        have hre_sq : (fdBoundary t₀).re ^ 2 = (s : ℂ).re ^ 2 := by rw [hre]
        nlinarith
      have h_im_pos_curve : (fdBoundary t₀).im > 0 :=
        fdBoundary_im_pos t₀ ⟨by linarith [ht₀_mem.1], by linarith [ht₀_mem.2]⟩
      have h_im_pos_s : (s : ℂ).im > 0 := by exact_mod_cast s.im_pos
      have h_im_eq : (fdBoundary t₀).im = (s : ℂ).im := by nlinarith [sq_nonneg ((fdBoundary t₀).im - (s : ℂ).im)]
      exact Complex.ext ht₀_re h_im_eq
  · -- ‖s‖ > 1, so ¬isInteriorPoint tells us |s.re| ≥ 1/2 or s.im ≥ H_height
    rcases le_or_lt (1/2 : ℝ) |(s : ℂ).re| with h_re_ge | h_re_lt
    · -- **Case 2: |s.re| = 1/2** (on vertical edge)
      have h_re_eq : |(s : ℂ).re| = 1/2 := le_antisymm h_re_abs h_re_ge
      -- s.im ∈ [√3/2, H_height] from ‖s‖ ≥ 1, re = ±1/2, hs_low
      have h_im_lower : (s : ℂ).im ≥ Real.sqrt 3 / 2 := by
        have h_im_pos : (s : ℂ).im > 0 := by exact_mod_cast s.im_pos
        -- Step 1: re² = 1/4 from |re| = 1/2
        have h_re_sq : (s : ℂ).re ^ 2 = 1/4 := by
          rcases abs_cases (s : ℂ).re with ⟨h, _⟩ | ⟨h, _⟩
          · have : (s : ℂ).re = 1/2 := by linarith
            rw [this]; norm_num
          · have : (s : ℂ).re = -1/2 := by linarith
            rw [this]; norm_num
        -- Step 2: im² ≥ 3/4 from ‖s‖² ≥ 1 and re² = 1/4
        have h_im_sq : (s : ℂ).im ^ 2 ≥ 3/4 := by
          have h := Complex.sq_norm (s : ℂ)
          rw [Complex.normSq_apply, ← sq, ← sq] at h
          -- h : ‖(s:ℂ)‖^2 = (s:ℂ).re^2 + (s:ℂ).im^2
          have h2 : 1 ≤ ‖(s : ℂ)‖ ^ 2 := by
            have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) h_norm_ge 2
            simpa using this
          linarith
        -- Step 3: im ≥ √3/2 by contradiction
        by_contra h_lt; push_neg at h_lt
        have hsq := sq_lt_sq' (show -(Real.sqrt 3 / 2) < (s : ℂ).im by linarith) h_lt
        have h_sq3 : (Real.sqrt 3 / 2) ^ 2 = 3/4 := by
          rw [div_pow, Real.sq_sqrt (show (3:ℝ) ≥ 0 by norm_num)]; norm_num
        linarith
      rcases abs_cases (s : ℂ).re with ⟨h_re_pos, _⟩ | ⟨h_re_neg, _⟩
      · -- **Sub-case 2a: s.re = 1/2** (right vertical, seg1)
        -- Exclude s = ρ+1: that would give s.im = √3/2 and s = 1/2 + (√3/2)I = ρ+1
        have h_ne_sqrt3 : (s : ℂ).im ≠ Real.sqrt 3 / 2 := by
          intro h_eq
          have : s = ellipticPoint_rho_plus_one' := by
            apply UpperHalfPlane.ext
            show (s : ℂ) = (ellipticPoint_rho_plus_one' : ℂ)
            have h_rho1_re : (ellipticPoint_rho_plus_one' : ℂ).re = 1/2 := by
              simp [ellipticPoint_rho_plus_one', Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
            have h_rho1_im : (ellipticPoint_rho_plus_one' : ℂ).im = Real.sqrt 3 / 2 := by
              simp [ellipticPoint_rho_plus_one', Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
            exact Complex.ext (by linarith [h_re_pos]) (by linarith)
          exact absurd this hs_ne_rho1
        have h_im_strict : (s : ℂ).im > Real.sqrt 3 / 2 := lt_of_le_of_ne h_im_lower (Ne.symm h_ne_sqrt3)
        -- Use t := H_height - s.im (since H - √3/2 = 1, seg1 param maps t ↦ im = H - t)
        -- Actually, seg1: im = H - t*(H - √3/2) = H - t (since H - √3/2 = 1)
        -- So t = H - s.im, and t ∈ [0, 1) since s.im ∈ (√3/2, H]
        set t₀ := H_height - (s : ℂ).im with ht₀_def
        have h_t₀_ge : t₀ ≥ 0 := by simp only [ht₀_def]; linarith [hs_low]
        have h_t₀_lt : t₀ < 1 := by
          simp only [ht₀_def]; unfold H_height; linarith
        have h_t₀_le : t₀ ≤ 1 := le_of_lt h_t₀_lt
        refine ⟨t₀, ⟨h_t₀_ge, by linarith⟩, ?_⟩
        -- fdBoundary t₀ = 1/2 + (H - t₀*(H - √3/2))*I
        -- Since t₀ ≤ 1, we're in seg1
        simp only [fdBoundary, h_t₀_le, ↓reduceIte]
        -- Need: 1/2 + (H - t₀*(H - √3/2))*I = (s : ℂ)
        -- Since H - √3/2 = 1 and t₀ = H - s.im: H - t₀*1 = H - (H - s.im) = s.im
        apply Complex.ext
        · -- .re: seg1 re is 1/2 = (↑s).re
          simp
          have : s.re = (↑s : ℂ).re := rfl
          linarith [h_re_pos, h_re_eq]
        · -- .im: seg1 im simplifies to s.im via t₀ = H - s.im
          simp [ht₀_def]
          unfold H_height; ring
      · -- **Sub-case 2b: s.re = -1/2** (left vertical, seg4)
        -- Exclude s = ρ
        have h_ne_sqrt3 : (s : ℂ).im ≠ Real.sqrt 3 / 2 := by
          intro h_eq
          have : s = ellipticPoint_rho' := by
            apply UpperHalfPlane.ext
            show (s : ℂ) = (ellipticPoint_rho' : ℂ)
            have h_rho_re : (ellipticPoint_rho' : ℂ).re = -1/2 := by
              simp [ellipticPoint_rho', Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re, Complex.I_im]
            have h_rho_im : (ellipticPoint_rho' : ℂ).im = Real.sqrt 3 / 2 := by
              simp [ellipticPoint_rho', Complex.add_im, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
            exact Complex.ext (by linarith [h_re_neg]) (by linarith)
          exact absurd this hs_ne_rho
        have h_im_strict : (s : ℂ).im > Real.sqrt 3 / 2 := lt_of_le_of_ne h_im_lower (Ne.symm h_ne_sqrt3)
        -- seg4: im = √3/2 + (t-3)*(H - √3/2) = √3/2 + (t-3)
        -- So t-3 = s.im - √3/2, t = 3 + s.im - √3/2
        set t₀ := 3 + (s : ℂ).im - Real.sqrt 3 / 2 with ht₀_def
        have h_t₀_gt_3 : t₀ > 3 := by simp only [ht₀_def]; linarith
        have h_t₀_le_4 : t₀ ≤ 4 := by simp only [ht₀_def]; unfold H_height at hs_low; linarith
        refine ⟨t₀, ⟨by linarith, by linarith⟩, ?_⟩
        -- fdBoundary t₀: t₀ > 1, > 2, > 3, ≤ 4 → seg4
        show fdBoundary t₀ = ↑s
        unfold fdBoundary
        rw [if_neg (show ¬(t₀ ≤ 1) from by linarith), if_neg (show ¬(t₀ ≤ 2) from by linarith),
            if_neg (show ¬(t₀ ≤ 3) from by linarith), if_pos h_t₀_le_4]
        apply Complex.ext
        · -- .re: seg4 re is -1/2 = (↑s).re
          simp
          have : s.re = (↑s : ℂ).re := rfl
          linarith [h_re_neg, h_re_eq]
        · -- .im: seg4 im simplifies to s.im via t₀ = 3 + s.im - √3/2
          simp [ht₀_def]
          unfold H_height; ring
    · -- |s.re| < 1/2, so from ¬isInteriorPoint and hs_low: **Case 3: s.im = H_height**
      have h_im_ge : (s : ℂ).im ≥ H_height := hs_not_int h_norm_gt h_re_lt
      have h_im_eq : (s : ℂ).im = H_height := le_antisymm hs_low h_im_ge
      -- seg5: re = t - 9/2, im = H. So t = s.re + 9/2
      set t₀ := (s : ℂ).re + 9/2 with ht₀_def
      have h_t₀_ge : t₀ ≥ 4 := by
        simp only [ht₀_def]; have := (abs_le.mp (le_of_lt (by linarith : |(s : ℂ).re| < 1/2))).1; linarith
      have h_t₀_le : t₀ ≤ 5 := by
        simp only [ht₀_def]; have := (abs_le.mp (le_of_lt (by linarith : |(s : ℂ).re| < 1/2))).2; linarith
      refine ⟨t₀, ⟨by linarith, h_t₀_le⟩, ?_⟩
      -- fdBoundary t₀: t₀ > 4 → seg5
      have h_not4 : ¬(t₀ ≤ 4) := by
        simp only [ht₀_def]; push_neg; linarith [(abs_lt.mp h_re_lt).1]
      show fdBoundary t₀ = ↑s
      unfold fdBoundary
      rw [if_neg (show ¬(t₀ ≤ 1) from by linarith), if_neg (show ¬(t₀ ≤ 2) from by linarith),
          if_neg (show ¬(t₀ ≤ 3) from by linarith), if_neg h_not4]
      apply Complex.ext
      · -- .re: seg5 re is t₀ - 9/2 = s.re
        simp [ht₀_def]
      · -- .im: seg5 im is H_height = s.im
        simp
        have : s.im = (↑s : ℂ).im := rfl
        linarith [h_im_eq]

/-- For boundary-classified zeros not at elliptic points, the generalized winding number is 0.
Uses `fd_noninterior_on_curve` for the geometric case analysis, then FTC with Complex.log. -/
private lemma gWN_eq_zero_of_boundary_zero (s : ℍ)
    (hs_zero : f s = 0)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hs_fd : s ∈ fundamentalDomain) (hs_ne_i : s ≠ ellipticPoint_i')
    (hs_ne_rho : s ≠ ellipticPoint_rho') (hs_ne_rho1 : s ≠ ellipticPoint_rho_plus_one')
    (hs_not_int : ¬isInteriorPoint s) :
    generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) = 0 := by
  -- Step 1: s is not on the fdBoundary curve (from h_nv + hs_zero)
  have h_off : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t ≠ (s : ℂ) := by
    intro t ht heq; apply h_nv t ht
    change (f ∘ UpperHalfPlane.ofComplex) (fdBoundary t) = 0
    rw [heq, Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos s.im_pos]
    exact hs_zero
  -- Step 2: s.im > H_height (if im ≤ H_height, s is on the curve → contradiction)
  have h_im_gt : (s : ℂ).im > H_height := by
    by_contra h_not_gt; push_neg at h_not_gt
    obtain ⟨t, ht, heq⟩ := fd_noninterior_on_curve s hs_fd hs_ne_i hs_ne_rho hs_ne_rho1
      hs_not_int h_not_gt
    exact h_off t ht heq
  -- Step 3: Convert PV winding number to classical integral
  have h_classical := generalizedWindingNumber_eq_classical_away fdBoundaryCurve (s : ℂ)
    (by intro t ht; exact h_off t ht)
  rw [show fdBoundaryCurve.toFun = fdBoundary from rfl,
      show fdBoundaryCurve.a = (0:ℝ) from rfl,
      show fdBoundaryCurve.b = (5:ℝ) from rfl] at h_classical
  rw [h_classical]
  -- Step 4: Show the integral is 0 by FTC with log antiderivative
  suffices h_int : ∫ t in (0:ℝ)..5,
      (fdBoundary t - (s : ℂ))⁻¹ * deriv fdBoundary t = 0 by
    rw [h_int]; simp
  -- F(t) = log(fdBoundary(t) - s) is the antiderivative
  -- fdBoundary(t) - s is in slitPlane (im < 0 since fdBoundary.im ≤ H_height < s.im)
  have h_slit : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t - (s : ℂ) ∈ Complex.slitPlane := by
    intro t ht; rw [Complex.mem_slitPlane_iff]; right
    simp only [sub_im]; linarith [fdBoundary_im_le_H_height t ht]
  -- Apply FTC with countable exceptions at breakpoints {1, 2, 3, 4}
  -- ∫₀⁵ F' = F(5) - F(0) = log(fdBoundary 5 - s) - log(fdBoundary 0 - s) = 0
  -- (since fdBoundary is closed)
  set F : ℝ → ℂ := fun t => Complex.log (fdBoundary t - (s : ℂ)) with hF_def
  set F' : ℝ → ℂ := fun t => (fdBoundary t - (s : ℂ))⁻¹ * deriv fdBoundary t with hF'_def
  -- (a) F is continuous on [0, 5]
  have hF_cont : ContinuousOn F (Icc 0 5) := by
    exact (fdBoundary_continuous.continuousOn.sub continuousOn_const).clog h_slit
  -- (b) HasDerivAt F F'(t) for t ∈ (0, 5) \ {1, 2, 3, 4}
  have hF_deriv : ∀ t ∈ Ioo (0:ℝ) 5 \ (↑fdPartition : Set ℝ),
      HasDerivAt F (F' t) t := by
    intro t ⟨ht_ioo, ht_not_P⟩
    -- fdBoundary is differentiable at t (away from partition)
    have h_diff_bd : DifferentiableAt ℝ fdBoundary t :=
      fdBoundary_differentiableAt_off_partition t ht_ioo ht_not_P
    -- fdBoundary t - s ∈ slitPlane
    have h_slit_t : fdBoundary t - (s : ℂ) ∈ Complex.slitPlane :=
      h_slit t (Ioo_subset_Icc_self ht_ioo)
    -- Chain rule: d/dt log(γ(t) - s) = (γ(t) - s)⁻¹ * γ'(t)
    have h_log : HasDerivAt Complex.log (fdBoundary t - (s : ℂ))⁻¹ (fdBoundary t - (s : ℂ)) :=
      Complex.hasDerivAt_log h_slit_t
    have h_sub : HasDerivAt (fun u => fdBoundary u - (s : ℂ)) (deriv fdBoundary t) t :=
      h_diff_bd.hasDerivAt.sub_const _
    have h_comp := h_log.scomp t h_sub
    -- h_comp : HasDerivAt (Complex.log ∘ (fun u => fdBoundary u - ↑s))
    --          (deriv fdBoundary t • (fdBoundary t - ↑s)⁻¹) t
    -- Convert smul to mul and reorder
    show HasDerivAt F (F' t) t
    simp only [hF_def, hF'_def]
    have : (Complex.log ∘ fun u => fdBoundary u - (s : ℂ)) = F := by
      ext u; simp [hF_def]
    rw [this] at h_comp
    convert h_comp using 1
    rw [smul_eq_mul, mul_comm]
  -- (c) F' is interval integrable on [0, 5]
  -- F' = (γ(t) - s)⁻¹ * γ'(t). Since s.im > H_height and fdBoundary.im ≤ H_height,
  -- the denominator is bounded away from 0. Combined with piecewise C1 of fdBoundary,
  -- this gives uniform boundedness and hence integrability.
  have hF'_int : IntervalIntegrable F' volume 0 5 := by
    -- F'(t) = g(γ(t)) * γ'(t) where g(z) = (z - s)⁻¹, γ = fdBoundary
    -- Use intervalIntegrable_pv_integrand_piecewiseC1
    let g : ℂ → ℂ := fun z => (z - (s : ℂ))⁻¹
    have hF'_eq : F' = fun t => g (fdBoundary t) * deriv fdBoundary t := by
      ext t; simp only [hF'_def, g]
    rw [hF'_eq]
    apply intervalIntegrable_pv_integrand_piecewiseC1
      (P := fdBoundaryFullPartition) (by norm_num : (0:ℝ) ≤ 5)
    · -- ContinuousOn g (fdBoundary '' Icc 0 5)
      apply ContinuousOn.inv₀
      · exact continuousOn_id.sub continuousOn_const
      · intro z ⟨t, ht, hzt⟩
        rw [← hzt]
        exact sub_ne_zero.mpr (h_off t ht)
    · -- ContinuousOn fdBoundary (Icc 0 5)
      exact fdBoundary_continuous.continuousOn
    · -- ContinuousOn (deriv fdBoundary) (Icc 0 5 \ fdBoundaryFullPartition)
      intro t ht
      have ht_ioo : t ∈ Ioo (0:ℝ) 5 := by
        refine ⟨lt_of_le_of_ne ht.1.1 ?_, lt_of_le_of_ne ht.1.2 ?_⟩
        · intro h; exact ht.2 (by rw [← h]; simp [fdBoundaryFullPartition])
        · intro h; exact ht.2 (by rw [h]; simp [fdBoundaryFullPartition])
      exact (fdBoundaryCurve.deriv_continuous_off_partition t ht_ioo ht.2).continuousWithinAt
    · -- ∃ Mg, ∀ z ∈ fdBoundary '' Icc 0 5, ‖g z‖ ≤ Mg
      apply continuousOn_image_bounded fdBoundary_continuous.continuousOn
      apply ContinuousOn.inv₀
      · exact continuousOn_id.sub continuousOn_const
      · intro z ⟨t, ht, hzt⟩
        rw [← hzt]
        exact sub_ne_zero.mpr (h_off t ht)
    · -- ∃ Mγ, ∀ t ∈ Icc 0 5, ‖deriv fdBoundary t‖ ≤ Mγ
      exact fdBoundaryImmersion.deriv_bounded
  -- (d) {1, 2, 3, 4} is countable
  have h_countable : (↑fdPartition : Set ℝ).Countable :=
    fdPartition.countable_toSet
  -- (e) Apply FTC
  have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F'
    (by norm_num : (0:ℝ) ≤ 5) h_countable hF_cont hF_deriv hF'_int
  rw [hFTC]
  -- (f) F(5) - F(0) = 0 since fdBoundary is closed
  show F 5 - F 0 = 0
  simp only [hF_def, fdBoundary_closed]
  ring

/-- Sum-level winding identity: Σ gWN(s) · ord_s = -(Σ ew(s) · ord_s).

Under h_nv (f nonvanishing on the curve), elliptic points (i, ρ, ρ+1) cannot
be zeros of f since they lie on the fdBoundary curve. So every zero s is either:
- **interior** (gWN = -1, ew = 1, so gWN + ew = 0), or
- **boundary above H_height** (gWN = 0, ew = 0, so gWN + ew = 0).

Hence each term in Σ (gWN + ew) · ord is individually 0. -/
private lemma h_sum_winding_eq_neg_ew
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (_hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) :
    ∑ s ∈ zeros,
        generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) *
          (orderOfVanishingAt' f s : ℂ) =
      -(∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) := by
  -- Rewrite as: Σ (gWN(s) + ew(s)) * ord(s) = 0
  rw [eq_neg_iff_add_eq_zero, ← Finset.sum_add_distrib]
  simp_rw [← add_mul]
  -- Each term is individually 0
  apply Finset.sum_eq_zero
  intro s hs
  -- Under h_nv, zeros avoid the curve, so elliptic points can't be zeros
  have h_avoid := zeros_avoid_fdBoundary_of_nonvanishing f h_nv zeros hzeros
  have hs_ne_i : s ≠ ellipticPoint_i' := by
    intro heq; subst heq
    exact h_avoid ellipticPoint_i' hs 2 (by norm_num)
      (by simp [fdBoundary_at_two, ellipticPoint_i'])
  have hs_ne_rho : s ≠ ellipticPoint_rho' := by
    intro heq; subst heq
    exact h_avoid ellipticPoint_rho' hs 3 (by norm_num)
      (by simp [fdBoundary_at_three, ellipticPoint_rho, ellipticPoint_rho'])
  have hs_ne_rho1 : s ≠ ellipticPoint_rho_plus_one' := by
    intro heq; subst heq
    exact h_avoid ellipticPoint_rho_plus_one' hs 1 (by norm_num)
      (by simp [fdBoundary_at_one, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one'])
  -- Show gWN(s) + ew(s) = 0, then multiply by ord gives 0
  suffices h : generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) +
      (effectiveWinding s : ℂ) = 0 by
    rw [h, zero_mul]
  by_cases hs_int : isInteriorPoint s
  · -- Interior: gWN = -1, ew = 1
    rw [gWN_interior_eq_neg_one s hs_int,
        effectiveWinding_eq_one_of_interior s hs_int]; push_cast; ring
  · -- Not interior: gWN = 0, ew = 0
    have hew : effectiveWinding s = 0 := by
      unfold effectiveWinding classifyPoint
      simp only [hs_ne_i, ↓reduceIte, hs_ne_rho]
      rw [if_neg]; exact fun ⟨h1, h2, h3⟩ => hs_int ⟨h1, h2, h3⟩
    rw [gWN_eq_zero_of_boundary_zero f s (hzeros s hs) h_nv
          (hzeros_fd s hs) hs_ne_i hs_ne_rho hs_ne_rho1 hs_int,
        hew]; push_cast; ring

/-- The generalized residue theorem for f'/f on ∂𝒟 (CW orientation).

PV ∮_{CW ∂𝒟} f'/f dz = -(2πi · Σ_s effectiveWinding(s) · ord_s(f))

where the sum is over all zeros s of f in 𝒟'. The negative sign arises
because the boundary is traversed clockwise.

**Proof**: Combines `h_sum_winding_eq_neg_ew` (sum-level winding identity)
with `h_integral_residue_of_generalizedResidueTheorem` (residue theorem application)
via the algebraic core `pv_equals_residue_sum_from_assumptions`. -/
theorem pv_equals_residue_sum
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) :
    pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) := by
  -- Use by_cases to avoid auto-including the `variable hf` (which would
  -- change the signature and break the call site in Core.lean).
  by_cases hf_zero : f = 0
  · -- f = 0: both sides are 0 (integrand is 0, orders are all 0)
    subst hf_zero
    -- Step 1: orderOfVanishingAt' of zero form is 0 (meromorphicOrderAt = ⊤ → untop₀ = 0)
    have h_ord : ∀ s : ℍ, orderOfVanishingAt' (⇑(0 : ModularForm (Gamma 1) k)) s = 0 := by
      intro s; unfold orderOfVanishingAt'
      suffices h : meromorphicOrderAt
          (fun w : ℂ => if h : 0 < w.im then
            (⇑(0 : ModularForm (Gamma 1) k)) ⟨w, h⟩ else 0) ↑s = ⊤ by
        rw [h, WithTop.untop₀_top]
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards with z
      split_ifs <;> simp
    -- Step 2: RHS sum is 0 (each term has orderOfVanishingAt' = 0)
    simp only [h_ord, Int.cast_zero, mul_zero, Finset.sum_const_zero, mul_zero, neg_zero]
    -- Step 3: LHS = 0 (pv_integral of zero form = 0)
    show pv_integral 0 fdBoundary 0 5 = 0
    unfold pv_integral
    have hF_zero : modularFormCompOfComplex (0 : ModularForm (Gamma 1) k) =
        fun _ : ℂ => (0 : ℂ) := by
      ext z; simp [modularFormCompOfComplex]
    rw [hF_zero, logDeriv_const]
    simp
  · -- f ≠ 0: apply the full argument principle chain
    have h_nv := nonvanishing_on_fdBoundary_of_integrable f hf_zero hint
    exact pv_equals_residue_sum_from_assumptions f zeros
      (h_sum_winding_eq_neg_ew f h_nv zeros hzeros hzeros_fd hzeros_complete)
      (h_integral_residue_of_generalizedResidueTheorem f hf_zero hint zeros hzeros
        hzeros_fd hzeros_complete)

/-! ## Interior Sum -/

/-- For interior points, the winding contribution equals the standard contribution.

If p is an interior point (not i or ρ), then its contribution to the sum is
simply ord_p(f), because the effective winding is 1. -/
theorem interior_contribution (p : ℍ) (hp_int : isInteriorPoint p)
    (hp_zero : f p = 0) :
    (effectiveWinding p : ℂ) * (orderOfVanishingAt' f p : ℂ) =
      (orderOfVanishingAt' f p : ℂ) := by
  have h_classify : classifyPoint p = .interior := by
    unfold classifyPoint
    have hp_norm : ‖(p : ℂ)‖ > 1 := hp_int.1
    have h_ne_i : p ≠ ellipticPoint_i' := by
      intro heq; subst heq; simp [ellipticPoint_i'] at hp_norm
    have h_ne_rho : p ≠ ellipticPoint_rho' := by
      intro heq; subst heq; simp [ellipticPoint_rho'] at hp_norm
      have h_sq : ‖-(1 / 2 : ℂ) + ↑(Real.sqrt 3) / 2 * I‖ ^ 2 ≤ 1 := by
        rw [Complex.sq_norm]; simp [normSq_apply]
        nlinarith [Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num)]
      nlinarith [norm_nonneg (-(1 / 2 : ℂ) + ↑(Real.sqrt 3) / 2 * I)]
    simp only [h_ne_i, ↓reduceIte, h_ne_rho, hp_int.1, hp_int.2.1, hp_int.2.2, and_self]
  simp [effectiveWinding, h_classify]

/-! ## Elliptic Contributions -/

/-- At i, the contribution is (1/2) · ord_i(f). -/
theorem elliptic_i_contribution (hi : f ellipticPoint_i' = 0) :
    (effectiveWinding ellipticPoint_i' : ℂ) * (orderOfVanishingAt' f ellipticPoint_i' : ℂ) =
      (1/2 : ℂ) * (orderOfVanishingAt' f ellipticPoint_i' : ℂ) := by
  congr 1
  show (effectiveWinding ellipticPoint_i' : ℂ) = 1/2
  simp [effectiveWinding, classifyPoint]

/-- At ρ, the contribution is (1/3) · ord_ρ(f). -/
theorem elliptic_rho_contribution (hr : f ellipticPoint_rho' = 0) :
    (effectiveWinding ellipticPoint_rho' : ℂ) * (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) =
      (1/3 : ℂ) * (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) := by
  congr 1
  show (effectiveWinding ellipticPoint_rho' : ℂ) = 1/3
  simp [effectiveWinding, classifyPoint, ellipticPoint_i_ne_rho.symm]

/-! ### M15: Crossing-Cauchy Infrastructure

Core.lean expects these API functions from ResidueSide:
- `S_onCurve`: the zeros whose images lie on fdBoundary
- `intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing`: nonvanishing → integrable
- `pv_equals_residue_sum_of_nonvanishing_of_ne_zero`: PV identity via nonvanishing
- `pv_equals_residue_sum_of_crossingCauchy_of_integrable`: PV identity with h_cc + hint
- `pv_equals_residue_sum_of_crossingCauchy_auto_of_integrable`: PV identity with hint only -/

/-- The set of zeros (as ℂ values) that lie on the fdBoundary curve.
Under nonvanishing, this set is empty (no zero can lie on the boundary). -/
noncomputable def S_onCurve (f : ModularForm (Gamma 1) k) (_hf : f ≠ 0)
    (zeros : Finset ℍ) : Finset ℂ :=
  (zeros.image (fun s : ℍ => (s : ℂ))).filter
    (fun s => ∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = s)

omit hf in
/-- Nonvanishing of the modular form on fdBoundary implies integrability of the
logDeriv integrand. Derives from the parameterized version at H = H_height. -/
theorem intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0) :
    IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5 :=
  intervalIntegrable_logDeriv_fdBoundary_H_of_nonvanishing f
    (by linarith [H_height_gt_one] : (0 : ℝ) < H_height) h_nv

include hf in
/-- PV residue identity under nonvanishing + f ≠ 0. Derives integrability from
nonvanishing, then forwards to `pv_equals_residue_sum`. -/
theorem pv_equals_residue_sum_of_nonvanishing_of_ne_zero
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) :
    pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) := by
  exact pv_equals_residue_sum f
    (intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing f h_nv)
    zeros hzeros hzeros_fd hzeros_complete

include hf in
/-- PV residue identity with crossing-Cauchy + integrability. Since integrability implies
nonvanishing on the boundary, the h_cc condition is vacuously satisfied and unused. -/
theorem pv_equals_residue_sum_of_crossingCauchy_of_integrable
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (_h_cc : ∀ s ∈ S_onCurve f hf zeros,
      (∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = s) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in (0:ℝ)..5,
            if ε < ‖fdBoundary t - s‖ then
              (fdBoundary t - s)⁻¹ * deriv fdBoundary t
            else 0)
          (𝓝[>] 0))) :
    pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) :=
  pv_equals_residue_sum f hint zeros hzeros hzeros_fd hzeros_complete

include hf in
/-- PV residue identity with only integrability — no crossing-Cauchy hypothesis needed.
Under integrability, the boundary avoids all zeros, so the crossing-Cauchy condition
is vacuously satisfied. -/
theorem pv_equals_residue_sum_of_crossingCauchy_auto_of_integrable
    (zeros : Finset ℍ) (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5) :
    pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) :=
  pv_equals_residue_sum f hint zeros hzeros hzeros_fd hzeros_complete

/-! ### M16: Auto-discharge of crossing-Cauchy hypothesis

The key theorem `fdBoundary_crossing_cauchy` shows that fdBoundary, being a
PiecewiseC1Immersion, automatically satisfies the Cauchy filter condition for the
ε-cutoff Cauchy kernel integral. -/

omit hf in
/-- Helper: if fdBoundary never hits s on [0,5], the cutoff integral is eventually
constant (and equals the unconditional integral). -/
private lemma fdBoundary_cutoff_integral_eventually_constant_of_avoids (s : ℂ)
    (h_avoids : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary t ≠ s) :
    ∃ L : ℂ, Filter.Tendsto (fun ε =>
      ∫ t in (0:ℝ)..5,
        if ε < ‖fdBoundary t - s‖ then
          (fdBoundary t - s)⁻¹ * deriv fdBoundary t
        else 0)
      (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨δ', hδ', hc⟩ := far_part_constant fdBoundary s
    (fun t => (fdBoundary t - s)⁻¹ * deriv fdBoundary t)
    (by norm_num : (0:ℝ) ≤ 5) h_avoids fdBoundary_continuous
  exact ⟨∫ t in (0:ℝ)..5, (fdBoundary t - s)⁻¹ * deriv fdBoundary t,
    (Filter.Tendsto.congr' (f₁ := fun _ =>
      ∫ t in (0:ℝ)..5, (fdBoundary t - s)⁻¹ * deriv fdBoundary t)
      (by rw [Filter.EventuallyEq, Filter.eventually_iff_exists_mem]
          exact ⟨Ioo 0 δ', Ioo_mem_nhdsGT hδ', fun ε hε => (hc ε hε).symm⟩)
      tendsto_const_nhds)⟩

omit hf in
/-- PV limit exists for a C^∞ segment function γ_seg on [a, b] around a crossing t₀.
Each segment function is C^∞ on all of ℝ with nonzero derivative everywhere,
so pv_limit_via_dyadic applies directly. -/
private lemma pv_limit_seg_function
    (γ_seg : ℝ → ℂ) (a b t₀ : ℝ) (s : ℂ)
    (_hab : a < b) (ht₀ : t₀ ∈ Ioo a b)
    (hγ_smooth : ContDiff ℝ ⊤ γ_seg)
    (hγ_deriv_ne : ∀ t : ℝ, deriv γ_seg t ≠ 0)
    (hγ_eq : γ_seg t₀ = s)
    (h_inj : ∀ t ∈ Icc a b, γ_seg t = s → t = t₀) :
    ∃ L : ℂ, Tendsto (fun ε =>
      ∫ t in a..b, if ε < ‖γ_seg t - s‖ then
        (γ_seg t - s)⁻¹ * deriv γ_seg t else 0)
      (𝓝[>] 0) (𝓝 L) := by
  rw [← hγ_eq]
  exact pv_limit_via_dyadic ht₀ (hγ_deriv_ne t₀)
    (hγ_smooth.contDiffAt.of_le le_top)
    rfl
    (hγ_smooth.continuous_deriv le_top |>.continuousOn)
    hγ_smooth.continuous.measurable
    hγ_smooth.continuous.continuousOn
    (fun t ht heq => h_inj t ht (by rw [heq, hγ_eq]))

omit hf in
/-- The ε-cutoff integral of `(γ(t)-s)⁻¹ · γ'(t)` along fdBoundary is Cauchy as ε → 0⁺,
for any point s on the curve.

**Proof**: fdBoundary is a PiecewiseC1Immersion, so the crossing set
`{t ∈ [0,5] | fdBoundary(t) = s}` is finite. Near each crossing t₀, the integrand
decomposes as `1/(t-t₀) + r(t)` where r is bounded (since γ'(t₀) ≠ 0). The model
integral `∫_{|t-t₀|>δ} 1/(t-t₀) dt` is constant in δ (log terms cancel symmetrically).
The remainder integral converges by DCT. Away from crossings, the integrand is bounded
and the cutoff integral is eventually constant. -/
theorem fdBoundary_crossing_cauchy (s : ℂ)
    (h_on : ∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = s) :
    Cauchy (Filter.map (fun ε =>
      ∫ t in (0:ℝ)..5,
        if ε < ‖fdBoundary t - s‖ then
          (fdBoundary t - s)⁻¹ * deriv fdBoundary t
        else 0)
      (𝓝[>] 0)) := by
  -- Strategy: Cauchy ↔ convergent in complete ℂ. We show the limit exists.
  rw [cauchy_map_iff_exists_tendsto]
  -- The crossing set is finite (fdBoundary is a PiecewiseC1Immersion)
  have h_finite : Set.Finite {t ∈ Icc (0:ℝ) 5 | fdBoundary t = s} :=
    piecewiseC1Immersion_finite_zeros fdBoundaryImmersion s
  -- If there are no crossings, contradiction with h_on
  by_cases h_empty : {t ∈ Icc (0:ℝ) 5 | fdBoundary t = s} = ∅
  · exfalso
    obtain ⟨t, ht, hts⟩ := h_on
    exact Set.notMem_empty t (h_empty ▸ (⟨ht, hts⟩ : t ∈ {t ∈ Icc (0:ℝ) 5 | fdBoundary t = s}))
  · -- There exists at least one crossing. Use the PiecewiseC1 structure.
    -- The crossing set is finite and nonempty.
    have h_ne : {t ∈ Icc (0:ℝ) 5 | fdBoundary t = s}.Nonempty :=
      nonempty_iff_ne_empty.mpr h_empty
    obtain ⟨t₀, ht₀_mem⟩ := h_ne
    obtain ⟨ht₀_Icc, ht₀_eq⟩ := ht₀_mem
    -- Step 1: Determine which segment contains t₀.
    -- fdBoundary = seg_j on (j-1, j) for j ∈ {1,...,5}.
    -- t₀ ∈ [0, 5], so t₀ is either in an open segment interior or at a
    -- partition point {0, 1, 2, 3, 4, 5}.
    --
    -- Step 2: Pick a segment function γ_ext that passes through s at t₀.
    -- For t₀ ∈ (k, k+1): γ_ext = seg_{k+1}, which is C^∞ and equals fdBoundary
    --   on (k, k+1). The crossing is in the interior of a smooth segment.
    -- For t₀ = k (partition point): pick seg_k (the left segment function).
    --   γ_ext(k) = fdBoundary(k) = s, and γ_ext is C^∞ on all of ℝ.
    --
    -- Step 3: Apply pv_limit_seg_function to γ_ext on a suitable interval
    --   containing t₀ in its interior. This gives convergence of the
    --   ε-cutoff integral for γ_ext.
    --
    -- Step 4: Relate the fdBoundary integral to the γ_ext integral.
    --   On segments where fdBoundary = γ_ext: equal a.e.
    --   On other segments: the correction is bounded (the 1/(t-t₀)
    --   singularities cancel when two smooth functions share a zero).
    --
    -- Step 5: Combine: fdBoundary integral = γ_ext integral + correction,
    --   both convergent, so the fdBoundary integral converges.
    --
    -- This argument handles both interior and corner crossings uniformly.
    -- The key mathematical fact is that the symmetric ε-cutoff of 1/(t-t₀)
    -- produces a constant (log terms cancel), regardless of whether the
    -- curve is smooth at t₀ or has a corner there.
    --
    -- Full formalization blocked on: proving correction convergence at corners.
    -- The correction integrand at a corner involves two smooth functions
    -- whose leading 1/(t-k) terms cancel, giving a bounded difference.
    -- The cutoff-region mismatch (different ε-balls for different segments)
    -- contributes O(log(|d₁|/|d₂|)) which is constant in ε.
    sorry

end
