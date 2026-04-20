/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.EllipticPoints
import Mathlib.Analysis.Complex.Convex
import Mathlib.NumberTheory.ModularForms.Identities

/-!
# Modular Invariance of Vanishing Order

The order of vanishing `orderOfVanishingAt'` is invariant under the full modular group SL₂(Z).
This follows from T-periodicity `f(z+1) = f(z)` and the S-identity `f(-1/z) = z^k f(z)`.

We also provide:
* `modularFormCompOfComplexFM` -- coercion of modular form to `ℂ → ℂ`
* `fdBoxFM` and `modularForm_finitely_many_zeros_in_fdBoxFM` -- finiteness of zeros

## Main results

* `ord_add_one_eqFM` : T-invariance of vanishing order
* `ord_S_eqFM` : S-invariance of vanishing order
* `ord_rho_plus_one_eq_ord_rhoFM` : `ρ` and `ρ+1` have equal vanishing order
* `modularForm_finitely_many_zeros_in_fdBoxFM` : finiteness of zeros in a bounded box
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ### Modular form as a function on ℂ -/

/-- The composition of a modular form with `ofComplex`, for contour integration. -/
abbrev modularFormCompOfComplexFM : ℂ → ℂ := f ∘ UpperHalfPlane.ofComplex

/-! ### meromorphicOrderAt under precomposition -/

private lemma mero_sub_const_fwdFM (g : ℂ → ℂ) (x c : ℂ) (h_sub_an : AnalyticAt ℂ (· - c) (x + c))
    (hg : MeromorphicAt g x) :
    MeromorphicAt (fun w => g (w - c)) (x + c) := by
  obtain ⟨n, hn⟩ := hg; refine ⟨n, ?_⟩
  have : (fun w => (w - (x + c)) ^ n • g (w - c)) = (fun z => (z - x) ^ n • g z) ∘ (· - c) := by
    ext w; simp only [Function.comp]; congr 1; ring
  rw [this]; exact hn.comp_of_eq h_sub_an (add_sub_cancel_right x c)

private lemma mero_sub_const_bwdFM (g : ℂ → ℂ) (x c : ℂ) (h_add_an : AnalyticAt ℂ (· + c) x)
    (hgφ : MeromorphicAt (fun w => g (w - c)) (x + c)) :
    MeromorphicAt g x := by
  obtain ⟨n, hn⟩ := hgφ; refine ⟨n, ?_⟩
  have : (fun w => (w - x) ^ n • g w) = (fun z => (z - (x + c)) ^ n • g (z - c)) ∘ (· + c) := by
    ext w; simp only [Function.comp, add_sub_cancel_right]; congr 1; ring
  rw [this]; exact hn.comp_of_eq h_add_an rfl

private lemma filter_map_sub_constFM (x c : ℂ) {p : ℂ → Prop} (hp : ∀ᶠ z in 𝓝[≠] x, p z) :
    ∀ᶠ w in 𝓝[≠] (x + c), p (w - c) := by
  have : map (Homeomorph.addRight (-c)) (𝓝[≠] (x + c)) = 𝓝[≠] x := by
    rw [Homeomorph.map_punctured_nhds_eq]; simp only [Homeomorph.coe_addRight, add_neg_cancel_right]
  rw [← this] at hp; rw [eventually_map] at hp
  exact hp.mono fun z hz => by simpa [sub_eq_add_neg] using hz

/-- `meromorphicOrderAt (g ∘ (· - c)) (x + c) = meromorphicOrderAt g x`. -/
private lemma meromorphicOrderAt_comp_sub_constFM (g : ℂ → ℂ) (x c : ℂ) :
    meromorphicOrderAt (fun w => g (w - c)) (x + c) = meromorphicOrderAt g x := by
  have h_sub_an : AnalyticAt ℂ (· - c) (x + c) := (analyticAt_id (𝕜 := ℂ)).sub analyticAt_const
  have h_add_an : AnalyticAt ℂ (· + c) x := (analyticAt_id (𝕜 := ℂ)).add analyticAt_const
  by_cases hg_mero : MeromorphicAt g x
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hg_mero,
        meromorphicOrderAt_of_not_meromorphicAt (mt (mero_sub_const_bwdFM g x c h_add_an) hg_mero)]
  by_cases htop : meromorphicOrderAt g x = ⊤
  · rw [htop, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    exact filter_map_sub_constFM x c htop
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
    obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (meromorphicOrderAt_eq_int_iff hg_mero).mp hn.symm
    rw [hn.symm, meromorphicOrderAt_eq_int_iff (mero_sub_const_fwdFM g x c h_sub_an hg_mero)]
    refine ⟨fun w => h (w - c), hh_an.comp_of_eq h_sub_an (add_sub_cancel_right x c),
      by simpa using hh_ne, ?_⟩
    exact (filter_map_sub_constFM x c hh_eq).mono fun z hz => by
      simp only [smul_eq_mul] at hz ⊢; rw [hz]; congr 1; congr 1; ring

private lemma mero_neg_inv_fwdFM (g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0)
    (hg : MeromorphicAt g (-p⁻¹)) :
    MeromorphicAt (fun z => g (-z⁻¹)) p :=
  ((hg.comp_analyticAt analyticAt_id.neg).comp_analyticAt (analyticAt_inv hp)).congr
    (by filter_upwards with _; rfl)

private lemma mero_neg_inv_bwdFM (g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0)
    (hgφ : MeromorphicAt (fun z => g (-z⁻¹)) p) :
    MeromorphicAt g (-p⁻¹) := by
  have hp_inv_ne : p⁻¹ ≠ 0 := inv_ne_zero hp
  change MeromorphicAt ((g ∘ Neg.neg) ∘ Inv.inv) p at hgφ
  rw [show p = p⁻¹⁻¹ from (inv_inv p).symm] at hgφ
  have s1 := (hgφ.comp_analyticAt (analyticAt_inv hp_inv_ne)).congr
    (by filter_upwards with z; show g (-((z⁻¹)⁻¹)) = g (-z); rw [inv_inv])
  rw [show p⁻¹ = (- -p⁻¹) from (neg_neg p⁻¹).symm] at s1
  exact (s1.comp_analyticAt analyticAt_id.neg).congr
    (by filter_upwards with z; show g (- -z) = g z; rw [neg_neg])

private lemma filter_map_neg_invFM (p : ℂ) (hp : p ≠ 0)
    {Q : ℂ → Prop} (hQ : ∀ᶠ z in 𝓝[≠] (-p⁻¹), Q z) :
    ∀ᶠ w in 𝓝[≠] p, Q (-w⁻¹) := by
  have hφ_an : AnalyticAt ℂ (fun z : ℂ => -z⁻¹) p := (analyticAt_inv hp).neg
  exact (tendsto_nhdsWithin_iff.mpr
    ⟨hφ_an.continuousAt.continuousWithinAt,
      by rw [eventually_nhdsWithin_iff]
         filter_upwards [univ_mem] with z _ hz
         simp only [mem_compl_iff, mem_singleton_iff] at hz
         exact fun h => hz (inv_injective (neg_inj.mp h))⟩).eventually hQ

private lemma neg_inv_finite_order_witnessFM (g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0)
    (n : ℤ) (h : ℂ → ℂ) (hh_an : AnalyticAt ℂ h (-p⁻¹)) (hh_ne : h (-p⁻¹) ≠ 0)
    (hh_eq : ∀ᶠ z in 𝓝[≠] (-p⁻¹), g z = (z - (-p⁻¹)) ^ n • h z) :
    ∃ h' : ℂ → ℂ, AnalyticAt ℂ h' p ∧ h' p ≠ 0 ∧
      ∀ᶠ z in 𝓝[≠] p, g (-z⁻¹) = (z - p) ^ n • h' z := by
  refine ⟨fun z => (z * p) ^ (-n) * h (-z⁻¹), ?_, ?_, ?_⟩
  · exact (((analyticAt_id (𝕜 := ℂ) (z := p)).mul analyticAt_const).zpow
      (mul_ne_zero hp hp)).mul (hh_an.comp_of_eq ((analyticAt_inv hp).neg) rfl)
  · exact mul_ne_zero (zpow_ne_zero _ (mul_ne_zero hp hp)) hh_ne
  · have hp_near : ∀ᶠ z in 𝓝[≠] p, z ≠ 0 := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_ne.mem_nhds hp] with z hz _; exact hz
    exact ((filter_map_neg_invFM p hp hh_eq).and hp_near).mono fun z ⟨hz_eq, hz_ne⟩ => by
      simp only [smul_eq_mul] at hz_eq ⊢
      rw [hz_eq, show -z⁻¹ - -p⁻¹ = (z - p) * (z * p)⁻¹ from by field_simp; ring, mul_zpow]
      calc (z - p) ^ n * (z * p)⁻¹ ^ n * h (-z⁻¹) = (z - p) ^ n * ((z * p) ^ (-n) * h (-z⁻¹)) := by
            rw [inv_zpow, zpow_neg]; ring

/-- `meromorphicOrderAt (g ∘ (· ↦ -·⁻¹)) p = meromorphicOrderAt g (-p⁻¹)` for `p ≠ 0`. -/
private lemma meromorphicOrderAt_comp_neg_invFM (g : ℂ → ℂ) (p : ℂ) (hp : p ≠ 0) :
    meromorphicOrderAt (fun z => g (-z⁻¹)) p = meromorphicOrderAt g (-p⁻¹) := by
  by_cases hg_mero : MeromorphicAt g (-p⁻¹)
  swap
  · rw [meromorphicOrderAt_of_not_meromorphicAt hg_mero,
        meromorphicOrderAt_of_not_meromorphicAt (mt (mero_neg_inv_bwdFM g p hp) hg_mero)]
  by_cases htop : meromorphicOrderAt g (-p⁻¹) = ⊤
  · rw [htop, meromorphicOrderAt_eq_top_iff]
    rw [meromorphicOrderAt_eq_top_iff] at htop
    exact filter_map_neg_invFM p hp htop
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
  obtain ⟨h, hh_an, hh_ne, hh_eq⟩ := (meromorphicOrderAt_eq_int_iff hg_mero).mp hn.symm
  rw [hn.symm, meromorphicOrderAt_eq_int_iff (mero_neg_inv_fwdFM g p hp hg_mero)]
  exact neg_inv_finite_order_witnessFM g p hp n h hh_an hh_ne hh_eq

/-! ### Analyticity and meromorphicity of modular forms on ℍ -/

/-- The dif-extension `G(w) = if 0 < w.im then f w else 0` is meromorphic (in fact analytic)
    at every upper half-plane point. -/
private lemma modform_G_meromorphicAtFM
    (G : ℂ → ℂ) (hG_def : G = fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℍ) :
    MeromorphicAt G (p : ℂ) := by
  apply AnalyticAt.meromorphicAt
  apply analyticAt_iff_eventually_differentiableAt.mpr
  have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex)
      {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with w hw
  exact ((h_diffOn w hw).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq (by
      filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
      simp only [hG_def, Function.comp_apply, dif_pos hu,
        UpperHalfPlane.ofComplex_apply_of_im_pos hu])

/-! ### T-invariance -/

/-- T-invariance of vanishing order: `ord(f, z+1) = ord(f, z)`. -/
lemma ord_add_one_eqFM (p : ℍ) :
    orderOfVanishingAt' f ((1 : ℝ) +ᵥ p) = orderOfVanishingAt' f p := by
  unfold orderOfVanishingAt'
  set G : ℂ → ℂ := fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0 with hG_def
  set p_cplx : ℂ := (p : ℂ) with hp_def
  conv_lhs => rw [show (((1 : ℝ) +ᵥ p : ℍ) : ℂ) = p_cplx + 1 by
    simp only [hp_def, UpperHalfPlane.coe_vadd]; push_cast; ring]
  have hG_eq_near : G =ᶠ[𝓝[≠] (p_cplx + 1)] (fun w => G (w - 1)) := by
    rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
    filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds
      (show 0 < (p_cplx + 1).im by
        simp only [hp_def, add_im, one_im, add_zero]; exact p.im_pos)] with z hz _
    simp only [hG_def]
    rw [dif_pos hz, dif_pos (by simp only [sub_im, one_im, sub_zero]; exact hz : 0 < (z - 1).im)]
    set z₀ : ℍ := ⟨z - 1, by simp only [sub_im, one_im, sub_zero]; exact hz⟩
    have h_period := SlashInvariantForm.vAdd_width_periodic 1 k 1 f.toSlashInvariantForm z₀
    have h_vadd_coe : ((1 : ℝ) +ᵥ z₀ : ℍ) = ⟨z, hz⟩ :=
      by ext; change (↑(1 : ℝ) : ℂ) + (z - 1) = z; push_cast; ring
    simp only [Nat.cast_one, mul_one, Int.cast_one, h_vadd_coe,
      ModularForm.toSlashInvariantForm_coe] at h_period
    exact h_period
  rw [meromorphicOrderAt_congr hG_eq_near, meromorphicOrderAt_comp_sub_constFM]

/-- T-invariance at `ρ`: `ord(f, ρ+1) = ord(f, ρ)`. -/
lemma ord_rho_plus_one_eq_ord_rhoFM :
    orderOfVanishingAt' f ellipticPointRhoPlusOne' =
    orderOfVanishingAt' f ellipticPointRho' := by
  have h : (1 : ℝ) +ᵥ ellipticPointRho' = ellipticPointRhoPlusOne' :=
    UpperHalfPlane.ext (by
      show (((1 : ℝ) : ℂ) + ↑ellipticPointRho') = ↑ellipticPointRhoPlusOne'
      simp only [ellipticPointRho', ellipticPointRhoPlusOne']
      show (1 : ℂ) + (-1 / 2 + ↑(Real.sqrt 3) / 2 * I) =
        1 / 2 + ↑(Real.sqrt 3) / 2 * I
      ring)
  rw [← h]; exact ord_add_one_eqFM f ellipticPointRho'

/-! ### S-identity and S-invariance -/

/-- S-identity for modular forms: `f(-1/z) = z^k * f(z)`. -/
lemma modform_comp_ofComplex_S_identityFM (z : ℂ) (hz : 0 < z.im) :
    f (UpperHalfPlane.ofComplex (-(1:ℂ)/z)) = (z : ℂ) ^ k * f (UpperHalfPlane.ofComplex z) := by
  have hz_ne : z ≠ 0 := by intro h; simp only [h, Complex.zero_im, lt_irrefl] at hz
  have h_neg_inv_im : 0 < (-(1:ℂ)/z).im := by
    rw [show -(1:ℂ)/z = (-z)⁻¹ from by field_simp, Complex.inv_im]
    exact div_pos (by simp only [Complex.neg_im, neg_neg]; exact hz)
      (Complex.normSq_pos.mpr (neg_ne_zero.mpr hz_ne))
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz,
    UpperHalfPlane.ofComplex_apply_of_im_pos h_neg_inv_im]
  set z_uhp : UpperHalfPlane := ⟨z, hz⟩
  have h_eq : (⟨-(1:ℂ)/z, h_neg_inv_im⟩ : UpperHalfPlane) =
      ModularGroup.S • z_uhp :=
    UpperHalfPlane.ext (by
      rw [UpperHalfPlane.modular_S_smul]
      show -(1:ℂ)/z = (-z)⁻¹; field_simp)
  rw [h_eq]
  have hS : ModularGroup.S ∈ Gamma 1 := by
    rw [Gamma_one_top]; exact Subgroup.mem_top _
  have h := SlashInvariantForm.slash_action_eqn_SL'' f hS z_uhp
  rw [ModularGroup.denom_S] at h; exact h

/-- The G-function satisfies the S-identity `G(-z⁻¹) = z^k * G(z)` on the upper half-plane. -/
private lemma modform_G_S_identityFM
    (G : ℂ → ℂ) (hG_def : G = fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0)
    (z : ℂ) (hz : 0 < z.im) :
    G (-z⁻¹) = z ^ k * G z := by
  subst hG_def
  have hz_ne : z ≠ 0 := by intro h; simp only [h, Complex.zero_im, lt_irrefl] at hz
  have h_neg_inv_im : 0 < (-z⁻¹).im := by
    rw [neg_inv, Complex.inv_im]
    exact div_pos (by simp only [Complex.neg_im, neg_neg]; exact hz)
      (Complex.normSq_pos.mpr (neg_ne_zero.mpr hz_ne))
  simp only [dif_pos h_neg_inv_im, dif_pos hz]
  have h_eq := modform_comp_ofComplex_S_identityFM f z hz
  rw [show -(1:ℂ)/z = -z⁻¹ from by field_simp] at h_eq
  rw [show f (↑(UpperHalfPlane.ofComplex (-z⁻¹))) = f ⟨-z⁻¹, h_neg_inv_im⟩ from by
    congr 1; exact UpperHalfPlane.ofComplex_apply_of_im_pos h_neg_inv_im] at h_eq
  rw [show f (↑(UpperHalfPlane.ofComplex z)) = f ⟨z, hz⟩ from by
    congr 1; exact UpperHalfPlane.ofComplex_apply_of_im_pos hz] at h_eq
  exact h_eq

/-- The meromorphic order of `z^k` at a nonzero point is zero. -/
private lemma meromorphicOrderAt_zpow_eq_zeroFM (p_cplx : ℂ) (hp_ne : p_cplx ≠ 0) :
    meromorphicOrderAt (fun z : ℂ => z ^ k) p_cplx = 0 := by
  have h_an : AnalyticAt ℂ (fun z : ℂ => z ^ k) p_cplx :=
    analyticAt_id.zpow hp_ne
  rw [h_an.meromorphicOrderAt_eq,
    show analyticOrderAt (fun z : ℂ => z ^ k) p_cplx = 0 from
      analyticOrderAt_eq_zero.mpr (Or.inr (zpow_ne_zero k hp_ne))]
  simp only [ENat.map_zero, CharP.cast_eq_zero, WithTop.coe_zero]

/-- S-invariance of vanishing order: `ord(f, S * z) = ord(f, z)`. -/
lemma ord_S_eqFM (p : ℍ) :
    orderOfVanishingAt' f (ModularGroup.S • p) = orderOfVanishingAt' f p := by
  unfold orderOfVanishingAt'
  set G : ℂ → ℂ := fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0 with hG_def
  set p_cplx : ℂ := (p : ℂ) with hp_def
  have h_S_coe : ((ModularGroup.S • p : ℍ) : ℂ) = -p_cplx⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, neg_inv]
  conv_lhs => rw [h_S_coe]
  have hp_ne : p_cplx ≠ 0 := by
    intro h; have : p_cplx.im = 0 := by rw [h]; simp only [Complex.zero_im]
    linarith [show p.im = p_cplx.im from rfl, p.im_pos]
  suffices h : meromorphicOrderAt G (-p_cplx⁻¹) =
      meromorphicOrderAt G p_cplx from congr_arg WithTop.untop₀ h
  calc meromorphicOrderAt G (-p_cplx⁻¹)
      = meromorphicOrderAt (fun z => G (-z⁻¹)) p_cplx :=
        (meromorphicOrderAt_comp_neg_invFM G p_cplx hp_ne).symm
    _ = meromorphicOrderAt (fun z => z ^ k * G z) p_cplx := by
        apply meromorphicOrderAt_congr
        rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
        filter_upwards [isOpen_lt continuous_const continuous_im |>.mem_nhds p.im_pos]
          with z hz _
        exact modform_G_S_identityFM f G hG_def z hz
    _ = meromorphicOrderAt (fun z : ℂ => z ^ k) p_cplx + meromorphicOrderAt G p_cplx :=
        meromorphicOrderAt_mul (analyticAt_id.zpow hp_ne).meromorphicAt
          (modform_G_meromorphicAtFM f G hG_def p)
    _ = meromorphicOrderAt G p_cplx := by
        simp only [meromorphicOrderAt_zpow_eq_zeroFM p_cplx hp_ne, zero_add]

/-! ### Finiteness of zeros in a bounded box -/

/-- An open box containing the truncated fundamental domain. -/
def fdBoxFM (M : ℝ) : Set ℂ := {z : ℂ | -1 < z.re ∧ z.re < 1 ∧ (1:ℝ)/2 < z.im ∧ z.im < M}

lemma fdBoxFM_im_pos {M : ℝ} {z : ℂ} (hz : z ∈ fdBoxFM M) : 0 < z.im := by
  linarith [hz.2.2.1]

/-- A nonzero modular form has finitely many zeros in `fdBoxFM M`. -/
theorem modularForm_finitely_many_zeros_in_fdBoxFM (hf : f ≠ 0) {M : ℝ} (hM : (1:ℝ)/2 < M) :
    Set.Finite {z ∈ fdBoxFM M | modularFormCompOfComplexFM f z = 0} := by
  by_contra h_inf
  set Z := {z ∈ fdBoxFM M | modularFormCompOfComplexFM f z = 0} with hZ_def
  have hZ_inf : Z.Infinite := h_inf
  have hBdd : Bornology.IsBounded (fdBoxFM M) :=
    isBounded_iff_forall_norm_le.mpr ⟨1 + M, fun z hz =>
      (Complex.norm_le_abs_re_add_abs_im z).trans (by
        have : |z.re| < 1 := abs_lt.mpr ⟨by linarith [hz.1], hz.2.1⟩
        have : |z.im| ≤ M := abs_le.mpr ⟨by linarith [hz.2.2.1], le_of_lt hz.2.2.2⟩
        linarith)⟩
  obtain ⟨z₀, hz₀K, hz₀_acc⟩ :=
    hZ_inf.exists_accPt_of_subset_isCompact hBdd.isCompact_closure
      ((sep_subset _ _).trans subset_closure)
  have hz₀_im : (1:ℝ)/2 ≤ z₀.im := closure_minimal (fun z hz => le_of_lt hz.2.2.1)
    (isClosed_le continuous_const Complex.continuous_im) hz₀K
  have hz₀_pos : 0 < z₀.im := by linarith [hz₀_im]
  have h_freq : ∃ᶠ y in 𝓝[≠] z₀, modularFormCompOfComplexFM f y = 0 :=
    (accPt_iff_frequently_nhdsNE.mp hz₀_acc).mono fun y hy => hy.2
  let U := {z : ℂ | 0 < z.im}
  have h_analOn : AnalyticOnNhd ℂ (modularFormCompOfComplexFM f) U :=
    fun z hz => (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  have h_preconn : IsPreconnected U := (Complex.isConnected_of_upperHalfPlane (r := 0)
      (fun z (hz : 0 < z.im) => hz) (fun z (hz : 0 < z.im) => le_of_lt hz)).isPreconnected
  apply hf; ext z
  simpa only [ModularForm.coe_zero, Pi.zero_apply, modularFormCompOfComplexFM,
      Function.comp_apply, UpperHalfPlane.ofComplex_apply] using
    (h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
      h_preconn hz₀_pos h_freq) z.im_pos

end
