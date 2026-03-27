/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ValenceFormula.PVChain.OnCurveCapture
import LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase
import LeanModularForms.ValenceFormula.ModularInvariance
import LeanModularForms.ValenceFormula.Boundary.Smooth

/-!
# Residue-Side Infrastructure for the PV Chain

Infrastructure lemmas needed to apply `generalizedResidueTheorem'` to
`logDeriv (modularFormCompOfComplex f)` on `fdBoundary_H H`.

## Main Results

* `hasSimplePoleAt_logDeriv_of_zero'` — logDeriv f has `HasSimplePoleAt` at zeros
* `hasSimplePoleAt_logDeriv_at_nonzero` — trivial `HasSimplePoleAt` at non-zeros
* `fdBox_isOpen`, `fdBox_convex` — fdBox properties
* `fdBoundary_H_mem_fdBox'` — curve is inside fdBox
* `residueSimplePole_logDeriv_eq_order` — residue = order at zeros
* `residueSimplePole_logDeriv_eq_zero_at_nonzero` — residue = 0 at non-zeros
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### fdBox properties -/

lemma fdBox_isOpen (M : ℝ) : IsOpen (fdBox M) := by
  refine IsOpen.inter ?_ (IsOpen.inter ?_ (IsOpen.inter ?_ ?_))
  · exact isOpen_lt continuous_const Complex.continuous_re
  · exact isOpen_lt Complex.continuous_re continuous_const
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact isOpen_lt Complex.continuous_im continuous_const

private lemma strict_convex_comb_lb {a b x y L : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : L < x) (hy : L < y) : L < a * x + b * y := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp only [zero_mul, zero_add, one_mul]; linarith
  · have h1 : a * L < a * x := mul_lt_mul_of_pos_left hx ha'
    have h2 : b * L ≤ b * y := mul_le_mul_of_nonneg_left hy.le hb
    have : a * L + b * L = L := by rw [← add_mul, hab, one_mul]
    linarith

private lemma strict_convex_comb_ub {a b x y U : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (hx : x < U) (hy : y < U) : a * x + b * y < U := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · simp only [zero_add] at hab; subst hab; simp only [zero_mul, zero_add, one_mul]; linarith
  · have h1 : a * x < a * U := mul_lt_mul_of_pos_left hx ha'
    have h2 : b * y ≤ b * U := mul_le_mul_of_nonneg_left hy.le hb
    have : a * U + b * U = U := by rw [← add_mul, hab, one_mul]
    linarith

lemma fdBox_convex (M : ℝ) : Convex ℝ (fdBox M) := by
  intro x hx y hy a b ha hb hab
  simp only [fdBox, Set.mem_setOf_eq] at hx hy ⊢
  have hre : (a • x + b • y).re = a * x.re + b * y.re := by simp [add_re]
  have him : (a • x + b • y).im = a * x.im + b * y.im := by simp [add_im]
  exact ⟨hre ▸ strict_convex_comb_lb ha hb hab hx.1 hy.1,
         hre ▸ strict_convex_comb_ub ha hb hab hx.2.1 hy.2.1,
         him ▸ strict_convex_comb_lb ha hb hab hx.2.2.1 hy.2.2.1,
         him ▸ strict_convex_comb_ub ha hb hab hx.2.2.2 hy.2.2.2⟩

private lemma fdBox_im_pos' {M : ℝ} {z : ℂ} (hz : z ∈ fdBox M) : 0 < z.im := by
  linarith [hz.2.2.1]

/-! ### allZerosInFdBox -/

noncomputable def allZerosInFdBox {M : ℝ} (hM : (1:ℝ)/2 < M) : Finset ℂ :=
  (modularForm_finitely_many_zeros_in_fdBox f hf hM).toFinset

lemma mem_allZerosInFdBox_iff {M : ℝ} (hM : (1:ℝ)/2 < M) {z : ℂ} :
    z ∈ allZerosInFdBox f hf hM ↔ z ∈ fdBox M ∧ modularFormCompOfComplex f z = 0 := by
  simp only [allZerosInFdBox, Set.Finite.mem_toFinset, Set.mem_sep_iff]

/-! ### HasSimplePoleAt for logDeriv at zeros -/

private lemma analyticAt_modform (z : ℂ) (hz : 0 < z.im) :
    AnalyticAt ℂ (modularFormCompOfComplex f) z :=
  (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)

lemma analyticAt_logDeriv_off_zeros' (z : ℂ) (hz : 0 < z.im)
    (hfz : modularFormCompOfComplex f z ≠ 0) :
    AnalyticAt ℂ (logDeriv (modularFormCompOfComplex f)) z :=
  (analyticAt_modform f z hz).deriv.fun_div (analyticAt_modform f z hz) hfz

include hf in
private lemma modform_not_locally_zero (s : ℍ) :
    analyticOrderAt (modularFormCompOfComplex f) (s : ℂ) ≠ ⊤ := by
  intro h_top
  rw [analyticOrderAt_eq_top] at h_top
  have h_analOn : AnalyticOnNhd ℂ (modularFormCompOfComplex f) {w | 0 < w.im} :=
    fun w hw => (UpperHalfPlane.mdifferentiable_iff.mp f.holo').analyticAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)
  have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} :=
    (Complex.isConnected_of_upperHalfPlane (r := 0)
      (fun w (hw : 0 < w.im) => hw) (fun w (hw : 0 < w.im) => le_of_lt hw)).isPreconnected
  have h_zero_on := h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    h_preconn s.im_pos (h_top.filter_mono nhdsWithin_le_nhds).frequently
  apply hf; ext z
  simpa only [ModularForm.coe_zero, Pi.zero_apply, modularFormCompOfComplex,
    Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h_zero_on z.im_pos

include hf in
/-- logDeriv of a modular form has a simple pole at each zero, with the factorization
`logDeriv F(z) = n/(z-s) + logDeriv g(z)` where `n` is the vanishing order and
`g` is analytic with `g(s) ≠ 0`. -/
theorem hasSimplePoleAt_logDeriv_of_zero_full (s : ℍ) (hs : f s = 0) :
    ∃ (n : ℤ) (g : ℂ → ℂ), n > 0 ∧ AnalyticAt ℂ g (s : ℂ) ∧ g (s : ℂ) ≠ 0 ∧
      n = analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) ∧
      ∀ᶠ z in 𝓝 (s : ℂ), z ≠ (s : ℂ) →
        logDeriv (modularFormCompOfComplex f) z =
          n / (z - (s : ℂ)) + logDeriv g z := by
  have h_analytic := analyticAt_modform f (s : ℂ) s.im_pos
  have h_not_top := modform_not_locally_zero f hf s
  have h_order_ne_zero : analyticOrderAt (modularFormCompOfComplex f) (s : ℂ) ≠ 0 := by
    rw [h_analytic.analyticOrderAt_ne_zero]
    simp only [modularFormCompOfComplex, Function.comp_apply,
      UpperHalfPlane.ofComplex_apply]; exact hs
  obtain ⟨g, hg_analytic, hg_ne_zero, hg_eq⟩ := (h_analytic.analyticOrderAt_ne_top.mp h_not_top)
  set n : ℕ := analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) with hn_def
  have hn_pos : (n : ℤ) > 0 := by
    have : n ≠ 0 := by
      intro h_eq_zero
      exact h_order_ne_zero (by
        rw [← Nat.cast_analyticOrderNatAt h_not_top, ← hn_def, h_eq_zero]
        simp only [Nat.cast_zero])
    omega
  refine ⟨n, g, hn_pos, hg_analytic, hg_ne_zero, rfl, ?_⟩
  have hg_eventually_analytic := hg_analytic.eventually_analyticAt
  have hg_eventually_ne_zero := hg_analytic.continuousAt.eventually_ne hg_ne_zero
  have h_all : ∀ᶠ z in 𝓝 (s : ℂ), ((modularFormCompOfComplex f) z = (z - (s : ℂ)) ^ n • g z) ∧
      AnalyticAt ℂ g z ∧ g z ≠ 0 := by
    filter_upwards [hg_eq, hg_eventually_analytic, hg_eventually_ne_zero]
      with z hz hza hzne
    exact ⟨hz, hza, hzne⟩
  obtain ⟨U, hU_mem, hU_cond⟩ := Filter.eventually_iff_exists_mem.mp h_all
  obtain ⟨V, hV_sub, hV_open, hs_in_V⟩ := mem_nhds_iff.mp hU_mem
  filter_upwards [IsOpen.mem_nhds hV_open hs_in_V] with z hz_in_V using by
    intro hz_ne_s
    have ⟨hz, hz_analytic, hz_ne_zero⟩ := hU_cond z (hV_sub hz_in_V)
    have h_eq_mul : modularFormCompOfComplex f z = (z - (s : ℂ)) ^ n * g z := hz
    have h_pow_ne_zero : (z - (s : ℂ)) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz_ne_s)
    have h_logDeriv_product :
        logDeriv (fun w => (w - (s : ℂ)) ^ n * g w) z =
          logDeriv (fun w => (w - (s : ℂ)) ^ n) z + logDeriv g z :=
      logDeriv_mul z h_pow_ne_zero hz_ne_zero
        ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
        hz_analytic.differentiableAt
    have h_logDeriv_pow :
        logDeriv (fun w => (w - (s : ℂ)) ^ n) z = ↑↑n / (z - (s : ℂ)) := by
      have hzs : z - (s : ℂ) ≠ 0 := sub_ne_zero.mpr hz_ne_s
      have hn' : 0 < n := by exact_mod_cast hn_pos
      have h_hd : HasDerivAt (fun w => (w - (s : ℂ)) ^ n) (↑n * (z - (s : ℂ)) ^ (n - 1)) z := by
        convert ((hasDerivAt_id z).sub (hasDerivAt_const z (s : ℂ))).pow n using 1
        simp only [Pi.sub_apply, id_eq, sub_zero, mul_one]
      rw [logDeriv_apply, h_hd.deriv]
      rw [div_eq_div_iff (pow_ne_zero _ hzs) hzs]
      rw [mul_assoc, ← pow_succ, show n - 1 + 1 = n from by omega]
    calc logDeriv (modularFormCompOfComplex f) z
        = logDeriv (fun w => (w - (s : ℂ)) ^ n * g w) z := by
          unfold logDeriv; simp only [Pi.div_apply]
          have h_val_eq := h_eq_mul
          have h_deriv_eq : deriv (modularFormCompOfComplex f) z =
              deriv (fun w => (w - (s : ℂ)) ^ n * g w) z := by
            have h_eq_at_z : (modularFormCompOfComplex f) =ᶠ[𝓝 z]
                  (fun w => (w - (s : ℂ)) ^ n * g w) := by
              apply Filter.eventually_iff_exists_mem.mpr
              exact ⟨V, IsOpen.mem_nhds hV_open hz_in_V,
                fun w hw => (hU_cond w (hV_sub hw)).1⟩
            exact h_eq_at_z.deriv_eq
          rw [h_deriv_eq, h_val_eq]
      _ = logDeriv (fun w => (w - (s : ℂ)) ^ n) z + logDeriv g z := h_logDeriv_product
      _ = ↑↑n / (z - (s : ℂ)) + logDeriv g z := by rw [h_logDeriv_pow]

include hf in
/-- logDeriv of a modular form has `HasSimplePoleAt` at each zero. -/
theorem hasSimplePoleAt_logDeriv_of_zero' (s : ℍ) (hs : f s = 0) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) (s : ℂ) := by
  obtain ⟨n, g, _, hg_analytic, hg_ne_zero, _, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero_full f hf s hs
  exact ⟨(n : ℂ), logDeriv g, hg_analytic.deriv.fun_div hg_analytic hg_ne_zero, by
    rw [eventually_nhdsWithin_iff]; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact h_formula⟩

omit hf in
/-- `HasSimplePoleAt` of logDeriv at a non-zero point (trivial: c = 0, g = logDeriv f). -/
lemma hasSimplePoleAt_logDeriv_at_nonzero (z : ℂ) (hz_im : 0 < z.im)
    (hz_nz : modularFormCompOfComplex f z ≠ 0) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) z := by
  exact ⟨0, logDeriv (modularFormCompOfComplex f),
    analyticAt_logDeriv_off_zeros' f z hz_im hz_nz, by
    filter_upwards with z; simp [zero_div, zero_add]⟩

include hf in
/-- `HasSimplePoleAt` for any point with positive imaginary part. -/
lemma hasSimplePoleAt_logDeriv_at_point (z : ℂ) (hz_im : 0 < z.im) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) z := by
  by_cases hz : modularFormCompOfComplex f z = 0
  · have h_im : 0 < z.im := hz_im
    exact hasSimplePoleAt_logDeriv_of_zero' f hf ⟨z, h_im⟩
      (by simp only [modularFormCompOfComplex, Function.comp_apply,
            UpperHalfPlane.ofComplex_apply_of_im_pos h_im] at hz ⊢; exact hz)
  · exact hasSimplePoleAt_logDeriv_at_nonzero f z hz_im hz

/-! ### ContinuousAt of the regular part (for hf_ext) -/

/-! ### orderOfVanishingAt' = analyticOrderNatAt -/

include hf in
private lemma orderOfVanishingAt'_eq_analyticOrderNatAt (s : ℍ) (_hs : f s = 0) :
    orderOfVanishingAt' (⇑f) s = (analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) : ℤ) := by
  unfold orderOfVanishingAt'
  set g₁ := fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0
  set g₂ := modularFormCompOfComplex f
  have h_eq : g₁ =ᶠ[𝓝[≠] (s : ℂ)] g₂ := by
    apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds s.im_pos] with w hw
    simp only [g₁, g₂, modularFormCompOfComplex, Function.comp_apply, dif_pos hw,
      UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  have h_order_eq : meromorphicOrderAt g₁ (s : ℂ) = meromorphicOrderAt g₂ (s : ℂ) :=
    meromorphicOrderAt_congr h_eq
  have h_analytic := analyticAt_modform f (s : ℂ) s.im_pos
  have h_not_top := modform_not_locally_zero f hf s
  rw [h_order_eq, h_analytic.meromorphicOrderAt_eq]
  cases h : analyticOrderAt g₂ (s : ℂ) with
  | top => exact absurd h h_not_top
  | coe n => simp only [analyticOrderNatAt, h, ENat.toNat_coe]; norm_cast

/-! ### residueSimplePole lemmas -/

include hf in
/-- At a zero `s` of `f`, `residueSimplePole(logDeriv f, s) = orderOfVanishingAt'(f, s)`. -/
theorem residueSimplePole_logDeriv_eq_order (s : ℍ) (hs : f s = 0) :
    residueSimplePole (logDeriv (modularFormCompOfComplex f)) (s : ℂ) =
      (orderOfVanishingAt' (⇑f) s : ℂ) := by
  obtain ⟨n, g, _, hg_analytic, hg_ne_zero, hn_eq, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero_full f hf s hs
  have h_logDeriv_g_analytic : AnalyticAt ℂ (logDeriv g) (s : ℂ) :=
    hg_analytic.deriv.fun_div hg_analytic hg_ne_zero
  have h_decomp : ∀ᶠ z in 𝓝[≠] (s : ℂ),
      logDeriv (modularFormCompOfComplex f) z = (n : ℂ) / (z - (s : ℂ)) + logDeriv g z := by
    rw [eventually_nhdsWithin_iff]; simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact h_formula
  have h_res := residue_simple_pole_eq_laurent _ (s : ℂ) (n : ℂ) (logDeriv g)
    h_logDeriv_g_analytic h_decomp
  rw [h_res, hn_eq]
  exact_mod_cast (orderOfVanishingAt'_eq_analyticOrderNatAt f hf s hs).symm

omit hf in
/-- At a non-zero point, `residueSimplePole(logDeriv f, z) = 0`. -/
lemma residueSimplePole_logDeriv_eq_zero_at_nonzero (z : ℂ) (hz_im : 0 < z.im)
    (hz_nz : modularFormCompOfComplex f z ≠ 0) :
    residueSimplePole (logDeriv (modularFormCompOfComplex f)) z = 0 := by
  have h_cont := (analyticAt_logDeriv_off_zeros' f z hz_im hz_nz).continuousAt
  have h1 : Tendsto (· - z) (𝓝[≠] z) (𝓝 0) := by
    rw [show (0 : ℂ) = z - z from (sub_self z).symm]
    exact (continuous_id.sub continuous_const).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have h_prod : Tendsto (fun w => (w - z) * logDeriv (modularFormCompOfComplex f) w)
      (𝓝[≠] z) (𝓝 (0 * logDeriv (modularFormCompOfComplex f) z)) :=
    h1.mul (h_cont.tendsto.mono_left nhdsWithin_le_nhds)
  rw [zero_mul] at h_prod
  exact h_prod.limUnder_eq

/-! ### fdBoundary_H ∈ fdBox -/

omit f hf in
/-- For `H ≥ 1` and `M > H`, `fdBoundary_H H t ∈ fdBox M` for `t ∈ [0, 5]`. -/
lemma fdBoundary_H_mem_fdBox' {H M : ℝ} (hH : 1 ≤ H) (hM : H < M)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) : fdBoundary_H H t ∈ fdBox M := by
  have h_re_abs := fdBoundary_H_re_abs_le_half H t ht
  constructor
  · linarith [abs_le.mp h_re_abs]
  constructor
  · linarith [abs_le.mp h_re_abs]
  constructor
  · have hH_sqrt3 : Real.sqrt 3 / 2 ≤ H := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
    have h_half_lt_sqrt3 : (1:ℝ)/2 < Real.sqrt 3 / 2 := by
      nlinarith [Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num),
        Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
    exact lt_of_lt_of_le h_half_lt_sqrt3 (fdBoundary_H_im_ge_sqrt3_div_2 H hH_sqrt3 t ht)
  · exact lt_of_le_of_lt (fdBoundary_H_im_le_H hH t ht) hM

/-! ### Discrete set separation -/

omit f hf in
lemma finset_discrete (S0 : Finset ℂ) :
    ∀ s ∈ (↑S0 : Set ℂ), ∃ ε > 0, ∀ s' ∈ (↑S0 : Set ℂ), s' ≠ s → ε ≤ ‖s' - s‖ := by
  intro s hs
  rcases (S0.erase s).eq_empty_or_nonempty with h_empty | h_ne
  · exact ⟨1, one_pos, fun s' hs' hne => absurd
      (h_empty ▸ Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hs'⟩ :
        s' ∈ (∅ : Finset ℂ)) (Finset.notMem_empty _)⟩
  · set img := (S0.erase s).image (fun s' => ‖s' - s‖)
    refine ⟨img.min' (h_ne.image _), ?_, ?_⟩
    · have := Finset.min'_mem img (h_ne.image _)
      obtain ⟨s', hs', hs'_eq⟩ := Finset.mem_image.mp this
      rw [← hs'_eq]; exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_erase.mp hs').1)
    · intro s' hs' hne
      exact Finset.min'_le _ _
        (Finset.mem_image.mpr ⟨s', Finset.mem_erase.mpr ⟨hne, Finset.mem_coe.mp hs'⟩, rfl⟩)

/-! ### CPV existence at off-curve singular points -/

omit f hf in
/-- CPV of `c/(z - s)` exists when the curve avoids `s` (limit is just the regular integral). -/
lemma cpvExists_of_off_curve (γ : ℝ → ℂ) (hγ_cont : Continuous γ)
    (a b : ℝ) (s : ℂ) (c : ℂ) (hab : a ≤ b) (h_off : ∀ t ∈ Icc a b, γ t ≠ s) :
    CauchyPrincipalValueExists' (fun z => c / (z - s)) γ a b s := by
  have h_cont : ContinuousOn (fun t => ‖γ t - s‖) (Icc a b) :=
    (hγ_cont.continuousOn.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, left_mem_Icc.mpr hab⟩ h_cont
  have hδ_pos : 0 < ‖γ t₀ - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h_off t₀ ht₀))
  refine ⟨∫ t in a..b, (c / (γ t - s)) * deriv γ t, ?_⟩
  apply Filter.Tendsto.congr'
  swap; exact tendsto_const_nhds
  rw [Filter.EventuallyEq]
  filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact (if_pos (show ‖γ t - s‖ > ε from lt_of_lt_of_le hε.2 (ht₀_min ht))).symm

omit f hf in
/-- CPV of `c · (z - s)⁻¹` from CPV of `(z - s)⁻¹` by scaling. -/
lemma cpvExists_scale (γ : ℝ → ℂ) (a b : ℝ) (s c : ℂ)
    (h : CauchyPrincipalValueExists' (fun z => (z - s)⁻¹) γ a b s) :
    CauchyPrincipalValueExists' (fun z => c / (z - s)) γ a b s := by
  obtain ⟨L, hL⟩ := h
  refine ⟨c * L, ?_⟩
  have h_eq : (fun ε => ∫ t in a..b, if ‖γ t - s‖ > ε
      then (c / (γ t - s)) * deriv γ t else 0) =
    fun ε => c * ∫ t in a..b, if ‖γ t - s‖ > ε
      then (γ t - s)⁻¹ * deriv γ t else 0 := by
    ext ε; rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro t _
    dsimp only; split_ifs with h <;> ring
  rw [h_eq]
  exact hL.const_mul c

/-! ### logDeriv_patched — patched logDeriv for ContinuousAt at zeros

At zeros of `f`, Lean's `div_zero` convention makes `logDeriv f(z) = 0/0 = 0`,
but the limit from the punctured neighborhood is `g(z) ≠ 0`. This breaks the
`ContinuousAt` hypothesis of `generalizedResidueTheorem'`.

The fix: define `logDerivPatched F S0` which equals `F` away from `S0` and
equals the regular part `g(z)` at each `z ∈ S0` (from the `HasSimplePoleAt`
decomposition). This makes the ContinuousAt hypothesis hold. -/

omit f hf in
private lemma residueSimplePole_congr_local (F G : ℂ → ℂ) (z₀ : ℂ)
    (h : F =ᶠ[𝓝[≠] z₀] G) : residueSimplePole F z₀ = residueSimplePole G z₀ := by
  simp only [residueSimplePole, limUnder]
  congr 1; exact Filter.map_congr (h.mono fun z hz => by simp only [hz])

omit f hf in
noncomputable def logDerivPatched (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) : ℂ → ℂ := fun z =>
  if h : z ∈ S0 then
    Classical.choose (Classical.choose_spec (hsp z h)) z
  else F z

omit f hf in
lemma logDerivPatched_eq_raw_off (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) {z : ℂ} (hz : z ∉ S0) :
    logDerivPatched F S0 hsp z = F z :=
  dif_neg hz

omit f hf in
private lemma logDerivPatched_eventuallyEq_raw_punctured (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (_hs : s ∈ S0) :
    logDerivPatched F S0 hsp =ᶠ[𝓝[≠] s] F := by
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  have h_open : IsOpen ((↑(S0.erase s) : Set ℂ)ᶜ) := (S0.erase s).finite_toSet.isClosed.isOpen_compl
  have h_s_mem : s ∈ ((↑(S0.erase s) : Set ℂ)ᶜ) := by
    simp [Set.mem_compl_iff]
  filter_upwards [h_open.mem_nhds h_s_mem] with z hz hzne
  exact dif_neg (fun habs => hz (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzne, habs⟩)))

omit f hf in
lemma hasSimplePoleAt_logDerivPatched (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (hs : s ∈ S0) :
    HasSimplePoleAt (logDerivPatched F S0 hsp) s := by
  obtain ⟨c, g, hg_an, hF_eq⟩ := hsp s hs
  exact ⟨c, g, hg_an, by
    filter_upwards [logDerivPatched_eventuallyEq_raw_punctured F S0 hsp s hs, hF_eq]
      with z h1 h2
    rw [h1]; exact h2⟩

omit f hf in
lemma residue_logDerivPatched_eq_raw (F : ℂ → ℂ) (S0 : Finset ℂ)
    (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) (s : ℂ) (hs : s ∈ S0) :
    residueSimplePole (logDerivPatched F S0 hsp) s = residueSimplePole F s :=
  residueSimplePole_congr_local _ _ _ (logDerivPatched_eventuallyEq_raw_punctured F S0 hsp s hs)

omit f hf in
/-- The patched logDeriv satisfies `ContinuousAt` for `generalizedResidueTheorem'`. -/
lemma logDerivPatched_hf_ext (F : ℂ → ℂ) (S0 : Finset ℂ) (hsp : ∀ s ∈ S0, HasSimplePoleAt F s) :
    ∀ s ∈ S0, ContinuousAt (fun z => logDerivPatched F S0 hsp z -
        residueSimplePole (logDerivPatched F S0 hsp) s / (z - s)) s := by
  intro s hs
  set c := (hsp s hs).choose with hc_def
  set g := (hsp s hs).choose_spec.choose with hg_def
  have hg_an : AnalyticAt ℂ g s := (hsp s hs).choose_spec.choose_spec.1
  have hF_eq : ∀ᶠ z in 𝓝[≠] s, F z = c / (z - s) + g z := (hsp s hs).choose_spec.choose_spec.2
  have h_res : residueSimplePole (logDerivPatched F S0 hsp) s = c := by
    rw [residue_logDerivPatched_eq_raw F S0 hsp s hs]
    exact residue_simple_pole_eq_laurent _ _ _ _ hg_an hF_eq
  rw [h_res]
  apply ContinuousAt.congr hg_an.continuousAt
  have h_open_compl : IsOpen ((↑(S0.erase s) : Set ℂ)ᶜ) :=
    (S0.erase s).finite_toSet.isClosed.isOpen_compl
  rw [eventually_nhdsWithin_iff] at hF_eq
  rw [Filter.EventuallyEq]
  filter_upwards [hF_eq,
      h_open_compl.mem_nhds (Set.mem_compl_iff _ _ |>.mpr (Finset.notMem_erase s S0))]
    with z hz_F hz_compl
  by_cases hzs : z = s
  · subst hzs
    simp only [sub_self, div_zero, sub_zero]
    unfold logDerivPatched; rw [dif_pos hs]
  · have hz_not_S0 : z ∉ S0 :=
      fun habs =>
        hz_compl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hzs, habs⟩))
    rw [logDerivPatched_eq_raw_off F S0 hsp hz_not_S0]
    rw [show F z = c / (z - s) + g z from hz_F hzs]; ring

/-! ### Norm bounds for fdBoundary_H -/

omit f hf in
/-- On the arc segments (1 < t ≤ 3), `fdBoundary_H H = fdBoundary`. -/
private lemma fdBoundary_H_eq_fdBoundary_on_13 (H : ℝ) {t : ℝ}
    (ht1 : ¬(t ≤ 1)) (ht3 : t ≤ 3) :
    fdBoundary_H H t = fdBoundary t := by
  unfold fdBoundary_H fdBoundary
  simp only [ht1, ↓reduceIte, ht3]

omit f hf in
/-- `‖fdBoundary_H H t‖ ≥ 1` for `t ∈ [0, 5]` when `H ≥ 1`. -/
lemma fdBoundary_H_norm_ge_one {H : ℝ} (hH : 1 ≤ H) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) :
    ‖fdBoundary_H H t‖ ≥ 1 := by
  have hH_sqrt3 : Real.sqrt 3 / 2 ≤ H := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1]
    have hre : (fdBoundary_seg1_H H t).re = 1/2 := by
      simp [fdBoundary_seg1_H, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
    have him : (fdBoundary_seg1_H H t).im ≥ Real.sqrt 3 / 2 := by
      have := fdBoundary_H_im_ge_sqrt3_div_2 H hH_sqrt3 t ht
      rwa [fdBoundary_H_eq_seg1_H h1] at this
    have h_nsq : normSq (fdBoundary_seg1_H H t) ≥ 1 := by
      rw [normSq_apply, hre]
      nlinarith [mul_self_le_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 2) him,
                 Real.mul_self_sqrt (show (0:ℝ) ≤ 3 from by norm_num)]
    calc ‖fdBoundary_seg1_H H t‖ = Real.sqrt (normSq (fdBoundary_seg1_H H t)) := rfl
      _ ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h_nsq
      _ = 1 := by simp only [Real.sqrt_one]
  · push_neg at h1; by_cases h3 : t ≤ 3
    · rw [fdBoundary_H_eq_fdBoundary_on_13 H (by linarith) h3]
      suffices ‖fdBoundary t‖ = 1 by linarith
      simp only [fdBoundary, show ¬(t ≤ 1) from by linarith, ↓reduceIte]
      split_ifs with h2
      · show ‖fdBoundary_seg2 t‖ = 1
        unfold fdBoundary_seg2
        rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
            ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
      · show ‖fdBoundary_seg3 t‖ = 1
        unfold fdBoundary_seg3
        rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
            ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
        exact Complex.norm_exp_ofReal_mul_I _
    · push_neg at h3; by_cases h4 : t ≤ 4
      · rw [fdBoundary_H_eq_seg4_H h3 h4]
        have hre : (fdBoundary_seg4_H H t).re = -(1/2) := by
          simp [fdBoundary_seg4_H, add_re, neg_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
            div_ofNat]; ring
        have him : (fdBoundary_seg4_H H t).im ≥ Real.sqrt 3 / 2 := by
          have := fdBoundary_H_im_ge_sqrt3_div_2 H hH_sqrt3 t ht
          rwa [fdBoundary_H_eq_seg4_H h3 h4] at this
        have h_nsq : normSq (fdBoundary_seg4_H H t) ≥ 1 := by
          rw [normSq_apply, hre]
          nlinarith [mul_self_le_mul_self (by positivity : (0:ℝ) ≤ Real.sqrt 3 / 2) him,
                     Real.mul_self_sqrt (show (0:ℝ) ≤ 3 from by norm_num)]
        calc ‖fdBoundary_seg4_H H t‖ = Real.sqrt (normSq (fdBoundary_seg4_H H t)) := rfl
          _ ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h_nsq
          _ = 1 := by simp only [Real.sqrt_one]
      · push_neg at h4
        rw [fdBoundary_H_eq_seg5_H h4]
        have him : (fdBoundary_seg5_H H t).im = H := by
          simp [fdBoundary_seg5_H, add_im, sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
            div_ofNat]
        have h_nsq : normSq (fdBoundary_seg5_H H t) ≥ 1 := by
          rw [normSq_apply]
          have him_ge : (fdBoundary_seg5_H H t).im ≥ 1 := by rw [him]; linarith
          nlinarith [mul_self_nonneg (fdBoundary_seg5_H H t).re,
            mul_self_le_mul_self (by linarith : (0:ℝ) ≤ 1) him_ge]
        calc ‖fdBoundary_seg5_H H t‖ = Real.sqrt (normSq (fdBoundary_seg5_H H t)) := rfl
          _ ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h_nsq
          _ = 1 := by simp only [Real.sqrt_one]

omit f hf in
/-- The boundary `fdBoundary_H H` avoids every point NOT in the closed FD. -/
lemma off_curve_of_not_in_fd_H {H : ℝ} (hH : 1 ≤ H) (z₀ : ℂ)
    (hz₀_not_fd : ¬ (|z₀.re| ≤ 1/2 ∧ ‖z₀‖ ≥ 1)) :
    ∀ t ∈ Icc (0:ℝ) 5, fdBoundary_H H t ≠ z₀ := by
  push_neg at hz₀_not_fd
  intro t ht heq
  by_cases h_re : |z₀.re| ≤ 1/2
  · have h_norm_lt : ‖z₀‖ < 1 := hz₀_not_fd h_re
    have h_norm_ge : ‖fdBoundary_H H t‖ ≥ 1 := fdBoundary_H_norm_ge_one hH t ht
    linarith [heq ▸ h_norm_ge]
  · push_neg at h_re
    have h_re_le := fdBoundary_H_re_abs_le_half H t ht
    linarith [heq ▸ h_re_le]

omit f hf in
/-- FTC: integral = 0 for a closed curve with slit-plane avoidance. -/
lemma ftc_integral_zero_of_closed_slit {γ : ℝ → ℂ} {z₀ : ℂ} {ω : ℂ} (hω : ω ≠ 0)
    (hγ_cont : Continuous γ) (hγ_closed : γ 0 = γ 5) (h_off : ∀ t ∈ Icc (0:ℝ) 5, γ t ≠ z₀)
    (h_slit : ∀ t ∈ Icc (0:ℝ) 5, ω * (γ t - z₀) ∈ Complex.slitPlane)
    (hγ_diff : ∀ t, t ∉ (fdBoundaryFullPartition : Finset ℝ) →
      DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ t ∈ Ioo (0:ℝ) 5, t ∉ (fdBoundaryFullPartition : Finset ℝ) →
      ContinuousAt (deriv γ) t)
    (hγ_deriv_bdd : ∃ Mγ : ℝ, ∀ t ∈ Icc (0:ℝ) 5, ‖deriv γ t‖ ≤ Mγ) :
    ∫ t in (0:ℝ)..5, (γ t - z₀)⁻¹ * deriv γ t = 0 := by
  set F : ℝ → ℂ := fun t => Complex.log (ω * (γ t - z₀)) with hF_def
  set F' : ℝ → ℂ := fun t => (γ t - z₀)⁻¹ * deriv γ t with hF'_def
  have hF_cont : ContinuousOn F (Icc 0 5) :=
    ContinuousOn.clog (continuousOn_const.mul (hγ_cont.continuousOn.sub continuousOn_const)) h_slit
  have hF_deriv : ∀ t ∈ Ioo (0:ℝ) 5 \ (↑fdBoundaryFullPartition : Set ℝ),
      HasDerivAt F (F' t) t := by
    intro t ⟨ht_ioo, ht_not_P⟩
    have h_diff := hγ_diff t (Finset.mem_coe.not.mp ht_not_P)
    have h_slit_t := h_slit t (Ioo_subset_Icc_self ht_ioo)
    have h_log := Complex.hasDerivAt_log h_slit_t
    have h_inner : HasDerivAt (fun u => ω * (γ u - z₀)) (ω * deriv γ t) t := by
      convert (h_diff.hasDerivAt.sub_const z₀).const_mul ω using 1
    have h_comp := h_log.scomp t h_inner
    convert h_comp using 1
    rw [smul_eq_mul]
    have hne := sub_ne_zero.mpr (h_off t (Ioo_subset_Icc_self ht_ioo))
    have hωne : ω * (γ t - z₀) ≠ 0 := mul_ne_zero hω hne
    simp only [hF'_def]; field_simp
  have hF'_int : IntervalIntegrable F' volume 0 5 := by
    obtain ⟨Mγ, hMγ⟩ := hγ_deriv_bdd
    have hg_cont : ContinuousOn (fun z => (z - z₀)⁻¹) (γ '' Icc 0 5) :=
      (continuousOn_id.sub continuousOn_const).inv₀
        (fun z ⟨t, ht, hzt⟩ => by rw [← hzt]; exact sub_ne_zero.mpr (h_off t ht))
    obtain ⟨Mg, hMg⟩ := continuousOn_image_bounded hγ_cont.continuousOn hg_cont
    have h_cont : ContinuousOn F' (Icc 0 5 \ fdBoundaryFullPartition) := by
      intro t ⟨ht_Icc, ht_not_P⟩
      show ContinuousWithinAt (fun t => (γ t - z₀)⁻¹ * deriv γ t) _ t
      have ht_Ioo : t ∈ Ioo (0:ℝ) 5 := by
        refine ⟨lt_of_le_of_ne ht_Icc.1 ?_, lt_of_le_of_ne ht_Icc.2 ?_⟩
        · intro h; exact ht_not_P (by rw [← h]; simp [fdBoundaryFullPartition])
        · intro h; exact ht_not_P (by rw [h]; simp [fdBoundaryFullPartition])
      exact ((hγ_cont.continuousAt.sub continuousAt_const).inv₀
        (sub_ne_zero.mpr (h_off t ht_Icc))).continuousWithinAt.mul
        (hγ_deriv_cont t ht_Ioo (Finset.mem_coe.not.mp ht_not_P)).continuousWithinAt
    have h_bound : ∀ t ∈ Icc (0:ℝ) 5, ‖F' t‖ ≤ Mg * Mγ := by
      intro t ht
      show ‖(γ t - z₀)⁻¹ * deriv γ t‖ ≤ Mg * Mγ
      rw [norm_mul]
      exact mul_le_mul (hMg _ ⟨t, ht, rfl⟩) (hMγ t ht) (norm_nonneg _)
        (le_trans (norm_nonneg _) (hMg _ ⟨t, ht, rfl⟩))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 5)]
    exact (integrableOn_of_bounded_aeMeasurable (Mg * Mγ)
      (aEStronglyMeasurable_of_continuousOn_off_finite h_cont) h_bound).mono_set
      Ioc_subset_Icc_self
  have hFTC := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le F F'
    (by norm_num : (0:ℝ) ≤ 5) fdBoundaryFullPartition.countable_toSet
    hF_cont hF_deriv hF'_int
  rw [hFTC]; show F 5 - F 0 = 0
  simp only [hF_def, hγ_closed]; ring

include hf in
/-- Winding number = 0 for points in `fdBox` but NOT in the fundamental domain. -/
lemma winding_zero_for_non_fd_point_H_geo (S : Finset UpperHalfPlane)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH : 1 ≤ H) (z₀ : ℂ)
    (hz₀_zero : z₀ ∈ allZerosInFdBox f hf (show (1:ℝ)/2 < H + 1 by linarith))
    (hz₀_not_S : ∀ s ∈ S, (s : ℂ) ≠ z₀) :
    generalizedWindingNumber' (fdBoundary_H H) 0 5 z₀ = 0 := by
  have hz₀_box := ((mem_allZerosInFdBox_iff f hf _).mp hz₀_zero).1
  have hz₀_im_pos : 0 < z₀.im := fdBox_im_pos' hz₀_box
  have hz₀_not_fd : ¬ (|z₀.re| ≤ 1/2 ∧ ‖z₀‖ ≥ 1) := by
    intro ⟨h_re, h_norm⟩
    set s : ℍ := ⟨z₀, hz₀_im_pos⟩
    have h_fs : f s = 0 := by
      have := ((mem_allZerosInFdBox_iff f hf _).mp hz₀_zero).2
      change (f ∘ UpperHalfPlane.ofComplex) z₀ = 0 at this
      rw [Function.comp_apply, UpperHalfPlane.ofComplex_apply_of_im_pos hz₀_im_pos] at this
      exact this
    have h_fd : s ∈ 𝒟 := by
      refine ⟨?_, h_re⟩
      show 1 ≤ Complex.normSq z₀
      have h_sq := Complex.sq_norm z₀
      rw [Complex.normSq_apply] at h_sq ⊢
      nlinarith [h_sq]
    have h_ord : orderOfVanishingAt' (⇑f) s ≠ 0 :=
      orderOfVanishingAt'_ne_zero_of_eq_zero f hf s h_fs
    exact hz₀_not_S s (hS_complete s h_fd h_ord) rfl
  have h_off : ∀ t ∈ Icc (0:ℝ) 5, fdBoundary_H H t ≠ z₀ :=
    off_curve_of_not_in_fd_H hH z₀ hz₀_not_fd
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  have h_classical := generalizedWindingNumber_eq_classical_away
    (fdBoundary_HCurve H) z₀ (by intro t ht; exact h_off t ht)
  rw [show (fdBoundary_HCurve H).toFun = fdBoundary_H H from rfl,
      show (fdBoundary_HCurve H).a = (0:ℝ) from rfl,
      show (fdBoundary_HCurve H).b = (5:ℝ) from rfl] at h_classical
  rw [h_classical]
  suffices h_int : ∫ t in (0:ℝ)..5, (fdBoundary_H H t - z₀)⁻¹ * deriv (fdBoundary_H H) t = 0 by
    rw [h_int]; simp only [mul_zero]
  push_neg at hz₀_not_fd
  have hγ_diff : ∀ t, t ∉ (fdBoundaryFullPartition : Finset ℝ) →
      DifferentiableAt ℝ (fdBoundary_H H) t := by
    intro t ht
    apply fdBoundary_H_differentiableAt_off_partition H
    intro habs; exact ht (by
      simp only [fdBoundaryFullPartition, fdBoundary_H_partition,
        Finset.mem_insert, Finset.mem_singleton] at habs ⊢; tauto)
  have hγ_deriv_cont := (fdBoundary_HCurve H).deriv_continuous_off_partition
  have hγ_deriv_bdd := piecewiseC1Immersion_deriv_bounded (fdBoundary_HImmersion H hH_sqrt3)
  by_cases h_re_half : |z₀.re| ≤ 1/2
  · have h_norm_lt : ‖z₀‖ < 1 := hz₀_not_fd h_re_half
    apply ftc_integral_zero_of_closed_slit (ω := -I) (by simp [Complex.ext_iff, I_re, I_im])
      (fdBoundary_H_continuous H) (fdBoundary_H_closed H) h_off
    · intro t ht
      rw [Complex.mem_slitPlane_iff]
      by_contra h_not_slit; push_neg at h_not_slit
      have h_re_neg_I : ((-I) * (fdBoundary_H H t - z₀)).re =
          (fdBoundary_H H t).im - z₀.im := by
        simp [mul_re, neg_re, I_re, I_im, sub_re, sub_im]
      have h_im_neg_I : ((-I) * (fdBoundary_H H t - z₀)).im =
          -((fdBoundary_H H t).re - z₀.re) := by
        simp [mul_im, neg_im, I_re, I_im, sub_re, sub_im]
      have h1 : (fdBoundary_H H t).im ≤ z₀.im := by
        linarith [h_re_neg_I ▸ h_not_slit.1]
      have h2 : (fdBoundary_H H t).re = z₀.re := by
        have := h_not_slit.2; rw [h_im_neg_I] at this; linarith
      have h_norm_curve : ‖fdBoundary_H H t‖ ≥ 1 :=
        fdBoundary_H_norm_ge_one hH t ht
      have h_sq_norm_z₀ := Complex.sq_norm z₀
      rw [Complex.normSq_apply] at h_sq_norm_z₀
      have h_sq_norm_curve := Complex.sq_norm (fdBoundary_H H t)
      rw [Complex.normSq_apply] at h_sq_norm_curve
      rw [h2] at h_sq_norm_curve
      have h_z₀_sq_lt : ‖z₀‖ ^ 2 < 1 := by nlinarith [norm_nonneg z₀]
      have h_curve_sq_ge : ‖fdBoundary_H H t‖ ^ 2 ≥ 1 := by
        nlinarith [norm_nonneg (fdBoundary_H H t)]
      have h_im_pos : 0 < (fdBoundary_H H t).im :=
        fdBoundary_H_im_pos H hH_sqrt3 t ht
      have h_prod : (z₀.im - (fdBoundary_H H t).im) * (z₀.im + (fdBoundary_H H t).im) ≥ 0 :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    · exact hγ_diff
    · exact hγ_deriv_cont
    · exact hγ_deriv_bdd
  · push_neg at h_re_half
    by_cases h_re_pos : z₀.re > 1/2
    · apply ftc_integral_zero_of_closed_slit (ω := -1) (by norm_num)
        (fdBoundary_H_continuous H) (fdBoundary_H_closed H) h_off
      · intro t ht; rw [Complex.mem_slitPlane_iff]; left
        show 0 < ((-1 : ℂ) * (fdBoundary_H H t - z₀)).re
        simp only [neg_one_mul, neg_re, sub_re]
        linarith [abs_le.mp (fdBoundary_H_re_abs_le_half H t ht)]
      · exact hγ_diff
      · exact hγ_deriv_cont
      · exact hγ_deriv_bdd
    · have h_re_neg : z₀.re < -1/2 := by
        cases abs_cases z₀.re with
        | inl h => linarith [h.1]
        | inr h => linarith [h.1, h_re_pos]
      apply ftc_integral_zero_of_closed_slit (ω := 1) one_ne_zero
        (fdBoundary_H_continuous H) (fdBoundary_H_closed H) h_off
      · intro t ht; rw [Complex.mem_slitPlane_iff]; left
        simp only [one_mul, sub_re]
        linarith [abs_le.mp (fdBoundary_H_re_abs_le_half H t ht)]
      · exact hγ_diff
      · exact hγ_deriv_cont
      · exact hγ_deriv_bdd

end
