/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.HW33MultiPole
import LeanModularForms.ForMathlib.HW33HigherOrderC3
import LeanModularForms.ForMathlib.HW33Paper
import LeanModularForms.ForMathlib.PiecewiseContourIntegral

/-!
# HW Theorem 3.3 — higher-order pole avoidance form

This file extends the simple-pole avoidance theorem
`hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids` to *higher-order*
poles in the avoidance case (γ does not pass through any pole).

**Why higher-order avoidance is achievable.** Dixon's theorem
(`dixonFunction_eq_zero_of_nullHomologous_open_full`) gives `∮_γ g = 0` for any
function `g` differentiable on `U` and γ null-homologous in `U` — there's no
restriction to simple poles. The simple-pole specialization
(`hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`) is just an
*application*. For higher-order poles, the same template works once the user
supplies the polar parts: subtract them to get an analytic remainder, apply
Dixon, then compute polar contributions term-by-term.

The two non-residue contributions:

* For `c / (z - s)^k` with `k ≥ 2`: `∮_γ = 0` because the antiderivative
  `-c / ((k-1) (z - s)^{k-1})` is single-valued on `ℂ \ {s}`.
* For `c / (z - s)`: `∮_γ = 2πi · winding(γ, s) · c`.

Hence only the residue (`k = 1`) coefficient contributes, exactly matching the
classical residue formula.

## Main result

* `hw_3_3_higherOrder_avoidance_paper` — paper-faithful statement for higher-
  order pole avoidance, taking the polar-part decomposition as user-supplied
  data. This is a stepping-stone: the truly paper-faithful version takes only
  `∀ s ∈ S, MeromorphicAt f s` and extracts polar parts internally via Laurent
  decomposition, but mathlib does not yet have the Laurent-extraction API
  needed for that final step.
-/

open Set Filter Topology Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- A **polar-part decomposition** of a meromorphic function `f` on a domain
`U \ S`: for each pole `s ∈ S`, an explicit polar part `polarPart s z =
∑ k, a_{s,k} / (z - s)^(k+1)` such that `f` minus the total polar part extends
analytically to all of `U`.

This bundles the data the residue formula needs without requiring access to
mathlib's Laurent-extraction API. Each polar part is a finite Laurent
combination at its pole; the residue at `s` is the `k = 0` coefficient. -/
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where
  /-- The polar part at each pole, viewed as a function of `z`. -/
  polarPart : ℂ → ℂ → ℂ
  /-- Order of the polar part at each pole. -/
  order : ℂ → ℕ
  /-- Laurent coefficients of the polar part at each pole. -/
  coeff : (s : ℂ) → Fin (order s) → ℂ
  /-- The polar part at `s` is the explicit Laurent sum
  `∑ k, coeff s k / (z - s)^(k+1)`. -/
  polarPart_eq : ∀ s ∈ S, ∀ z, z ≠ s →
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - s) ^ (k.val + 1)
  /-- The residue at `s ∈ S` equals the `k = 0` Laurent coefficient (for non-empty
  polar parts) or zero (for empty). -/
  residue_eq : ∀ s ∈ S,
    residue f s = if h : 0 < order s then coeff s ⟨0, h⟩ else 0
  /-- After subtracting the total polar part, `f` extends to a function
  differentiable on all of `U`. -/
  analyticRemainder : ℂ → ℂ
  analyticRemainder_diff : DifferentiableOn ℂ analyticRemainder U
  decomp : ∀ z ∈ U \ (↑S : Set ℂ),
    f z = analyticRemainder z + ∑ s ∈ S, polarPart s z

/-! ## The "higher-order" part of a polar decomposition

A polar part `polarPart s z = ∑ k, a_k/(z-s)^(k+1)` (`k = 0, ..., N-1`) splits
into the simple-pole part `a_0/(z-s)` (the residue contribution) and the
higher-order part `∑_{k≥1} a_k/(z-s)^(k+1)`. The higher-order part integrates
to zero along any closed curve avoiding `s`. -/

/-- The strictly-higher-order part of a polar part: `∑_{k≥1} a_k/(z-s)^(k+1)`. -/
noncomputable def higherOrderPart {N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ :=
  ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0

/-- The simple-pole part of a polar part: `a_0/(z-s)` (or 0 if N = 0). -/
noncomputable def simplePolePart {N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ :=
  if h : 0 < N then a ⟨0, h⟩ / (z - s) else 0

/-- The polar part decomposes into simple-pole + higher-order. -/
theorem polarPart_eq_simplePole_add_higherOrder {N : ℕ} (a : Fin N → ℂ) (s z : ℂ) :
    (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      simplePolePart a s z + higherOrderPart a s z := by
  classical
  unfold simplePolePart higherOrderPart
  by_cases h : 0 < N
  · simp only [dif_pos h]
    have hsplit : ∀ k : Fin N,
        a k / (z - s) ^ (k.val + 1) =
          (if k.val = 0 then a ⟨0, h⟩ / (z - s) else 0) +
          (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) := by
      intro k
      by_cases hk : k.val = 0
      · have : k = ⟨0, h⟩ := Fin.ext hk
        simp [this]
      · have hk1 : k.val ≥ 1 := by omega
        simp [hk, hk1]
    rw [show (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
        ∑ k : Fin N, ((if k.val = 0 then a ⟨0, h⟩ / (z - s) else 0) +
          (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0)) from
        Finset.sum_congr rfl (fun k _ => hsplit k)]
    rw [Finset.sum_add_distrib]
    have h_first : (∑ k : Fin N,
        if k.val = 0 then a ⟨0, h⟩ / (z - s) else 0) = a ⟨0, h⟩ / (z - s) := by
      rw [Finset.sum_eq_single ⟨0, h⟩]
      · simp
      · intro k _ hk
        have hk0 : k.val ≠ 0 := fun h_eq => hk (Fin.ext h_eq)
        simp [hk0]
      · simp
    rw [h_first]
  · simp only [dif_neg h]
    have hN : N = 0 := Nat.eq_zero_of_not_pos h
    subst hN
    simp

/-! ## Higher-order Laurent term: contour integral vanishes -/

/-- For `k ≥ 2`, the function `c / (z - s)^k` has the single-valued antiderivative
`-c / ((k-1)(z-s)^(k-1))` on `ℂ \ {s}`. Hence its contour integral along any
closed piecewise-`C¹` path avoiding `s` vanishes. -/
theorem contourIntegral_higherOrder_eq_zero_of_avoids
    {x s : ℂ} (γ : PiecewiseC1Path x x)
    (h_avoids : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toPath.extend t ≠ s)
    {k : ℕ} (hk : 2 ≤ k) (c : ℂ)
    (h_int : IntervalIntegrable
      (fun t => c / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral (fun z => c / (z - s) ^ k) = 0 := by
  have hk_natcast : ((k - 1 : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    omega
  set F : ℂ → ℂ := fun z =>
    (-c / ((k - 1 : ℕ) : ℂ)) * (z - s) ^ (-((k - 1 : ℕ) : ℤ))
  have hU_img : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ ({s} : Set ℂ)ᶜ :=
    fun t ht => h_avoids t ht
  have hF : ∀ z ∈ ({s} : Set ℂ)ᶜ, HasDerivAt F (c / (z - s) ^ k) z := by
    intro z hz
    have hz_sub : z - s ≠ 0 := sub_ne_zero.mpr hz
    have h_id_sub : HasDerivAt (fun w => w - s) 1 z :=
      (hasDerivAt_id z).sub_const s
    have h_inner :=
      (hasDerivAt_zpow (-((k - 1 : ℕ) : ℤ)) (z - s) (Or.inl hz_sub)).comp z h_id_sub
    simp only [Function.comp_def, mul_one] at h_inner
    have h_total := h_inner.const_mul (-c / ((k - 1 : ℕ) : ℂ))
    convert h_total using 1
    have hk_eq : -((k - 1 : ℕ) : ℤ) - 1 = -(k : ℤ) := by omega
    rw [hk_eq, zpow_neg, zpow_natCast]
    field_simp
    push_cast
    ring
  exact PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed γ rfl hU_img hF h_int

/-! ## Higher-order part contour integral vanishes -/

/-- The contour integral of `higherOrderPart a s` along a closed γ avoiding `s`
vanishes: each term `a_k/(z-s)^(k+1)` for `k ≥ 1` (i.e. `k+1 ≥ 2`) has a
single-valued antiderivative on `ℂ \ {s}`, so its contour integral is zero. -/
theorem contourIntegral_higherOrderPart_eq_zero_of_avoids
    {x s : ℂ} (γ : PiecewiseC1Path x x)
    (h_avoids : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toPath.extend t ≠ s)
    {N : ℕ} (a : Fin N → ℂ)
    (h_int_each : ∀ k : Fin N, k.val ≥ 1 → IntervalIntegrable
      (fun t => a k / (γ.toPath.extend t - s) ^ (k.val + 1) *
        deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral (higherOrderPart a s) = 0 := by
  classical
  have h_int : ∀ k : Fin N, IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) γ) volume 0 1 := by
    intro k
    by_cases hk : k.val ≥ 1
    · simp only [if_pos hk]
      change IntervalIntegrable
        (fun t => a k / (γ.toPath.extend t - s) ^ (k.val + 1) *
          deriv γ.toPath.extend t) volume 0 1
      exact h_int_each k hk
    · simp only [if_neg hk]
      change IntervalIntegrable
        (fun t => (0 : ℂ) * deriv γ.toPath.extend t) volume 0 1
      simp only [zero_mul]
      exact intervalIntegrable_const
  change PiecewiseC1Path.contourIntegral
    (fun z => ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) γ = 0
  rw [contourIntegral_finset_sum Finset.univ _ γ (fun k _ => h_int k)]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k.val ≥ 1
  · have hk_ge_2 : 2 ≤ k.val + 1 := by omega
    have h_term_eq : (fun z => if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) =
        fun z => a k / (z - s) ^ (k.val + 1) := by
      ext z
      simp [hk]
    rw [h_term_eq]
    exact contourIntegral_higherOrder_eq_zero_of_avoids γ h_avoids hk_ge_2 (a k)
      (h_int_each k hk)
  · have h_term_eq : (fun z => if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) =
        fun _ => (0 : ℂ) := by
      ext z
      simp [hk]
    rw [h_term_eq]
    exact PiecewiseC1Path.contourIntegral_zero γ

/-! ## Main theorem -/

/-- **HW Theorem 3.3 — higher-order pole avoidance, paper-faithful curve.** -/
theorem hw_3_3_higherOrder_avoidance_paper
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s)
    (decomp : PolarPartDecomposition f S U) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  obtain ⟨δ, hδ_pos, hδ_bound⟩ :=
    avoids_finset_delta_bound γ.toPwC1Immersion.toPiecewiseC1Path S hγ_avoids
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_higherOrder_int_each : ∀ s ∈ S, ∀ k : Fin (decomp.order s), k.val ≥ 1 →
      IntervalIntegrable
        (fun t => decomp.coeff s k /
          (γP.toPath.extend t - s) ^ (k.val + 1) *
          deriv γP.toPath.extend t) volume 0 1 := by
    intro s hs k _
    have h_avoid_s : ∀ t ∈ Icc (0 : ℝ) 1, γP.toPath.extend t ≠ s :=
      hγ_avoids s hs
    have h_cont_inv : ContinuousOn
        (fun t => decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1))
        (Icc (0 : ℝ) 1) := by
      apply ContinuousOn.div continuousOn_const
      · exact (γP.toPath.continuous_extend.continuousOn.sub continuousOn_const).pow _
      · intro t ht hzero
        exact h_avoid_s t ht
          (sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_pos _).ne' |>.mp hzero))
    have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend)
        MeasureTheory.volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
      refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
        (stronglyMeasurable_deriv _).aestronglyMeasurable
        (ae_restrict_of_ae (Filter.Eventually.of_forall
          (fun _ => norm_deriv_le_of_lipschitz hLip)))
    exact h_deriv_int.continuousOn_mul (h_cont_inv.mono
      (by rw [uIcc_of_le (zero_le_one' ℝ)]))
  have h_polarPart_integral : ∀ s ∈ S,
      γP.contourIntegral (decomp.polarPart s) =
        2 * ↑Real.pi * I *
          generalizedWindingNumber γP s * residue f s := by
    intro s hs
    have h_avoid_s : ∀ t ∈ Icc (0 : ℝ) 1, γP.toPath.extend t ≠ s :=
      hγ_avoids s hs
    have h_polarPart_curve : ∀ t ∈ Icc (0 : ℝ) 1,
        decomp.polarPart s (γP.toPath.extend t) =
          ∑ k : Fin (decomp.order s),
            decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1) := by
      intro t ht
      exact decomp.polarPart_eq s hs (γP.toPath.extend t) (h_avoid_s t ht)
    have h_int_eq : γP.contourIntegral (decomp.polarPart s) =
        γP.contourIntegral (fun z => ∑ k : Fin (decomp.order s),
          decomp.coeff s k / (z - s) ^ (k.val + 1)) := by
      simp only [PiecewiseC1Path.contourIntegral]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (zero_le_one' ℝ)] at ht
      change decomp.polarPart s (γP.toPath.extend t) * deriv γP.toPath.extend t =
        (∑ k : Fin (decomp.order s),
          decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1)) *
            deriv γP.toPath.extend t
      rw [h_polarPart_curve t ht]
    rw [h_int_eq]
    have h_int_each : ∀ k : Fin (decomp.order s), IntervalIntegrable
        (PiecewiseC1Path.contourIntegrand
          (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)) γP) volume 0 1 := by
      intro k
      change IntervalIntegrable
        (fun t => decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1) *
          deriv γP.toPath.extend t) volume 0 1
      by_cases hk : k.val ≥ 1
      · exact h_higherOrder_int_each s hs k hk
      · have h_cont_inv : ContinuousOn
            (fun t => decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1))
            (Icc (0 : ℝ) 1) := by
          apply ContinuousOn.div continuousOn_const
          · exact (γP.toPath.continuous_extend.continuousOn.sub continuousOn_const).pow _
          · intro t ht hzero
            exact h_avoid_s t ht
              (sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_pos _).ne' |>.mp hzero))
        have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend)
            MeasureTheory.volume 0 1 := by
          rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
          refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
            (stronglyMeasurable_deriv _).aestronglyMeasurable
            (ae_restrict_of_ae (Filter.Eventually.of_forall
              (fun _ => norm_deriv_le_of_lipschitz hLip)))
        exact h_deriv_int.continuousOn_mul (h_cont_inv.mono
          (by rw [uIcc_of_le (zero_le_one' ℝ)]))
    rw [contourIntegral_finset_sum Finset.univ _ γP (fun k _ => h_int_each k)]
    by_cases h_order_pos : 0 < decomp.order s
    · have h_split := Finset.sum_eq_single_of_mem
        (s := (Finset.univ : Finset (Fin (decomp.order s))))
        (a := ⟨0, h_order_pos⟩)
        (f := fun k : Fin (decomp.order s) =>
          γP.contourIntegral (fun z => decomp.coeff s k / (z - s) ^ (k.val + 1)))
        (Finset.mem_univ _)
        (fun k _ hk_ne => by
          have hk_ge_1 : k.val ≥ 1 := by
            have : k.val ≠ 0 := fun h => hk_ne (Fin.ext h)
            omega
          have hk_succ_ge_2 : 2 ≤ k.val + 1 := by omega
          exact contourIntegral_higherOrder_eq_zero_of_avoids γP h_avoid_s hk_succ_ge_2
            _ (h_higherOrder_int_each s hs k hk_ge_1))
      rw [h_split]
      simp only [zero_add, pow_one]
      have h_residue_eq : decomp.coeff s ⟨0, h_order_pos⟩ = residue f s :=
        ((decomp.residue_eq s hs).trans (dif_pos h_order_pos)).symm
      rw [h_residue_eq]
      set w := generalizedWindingNumber γP s with hw_def
      have h_winding_int_eq :
          γP.contourIntegral (fun z => (z - s)⁻¹) = 2 * ↑Real.pi * I * w := by
        have h1 := hasCauchyPV_of_avoids (f := fun z => (z - s)⁻¹) (γ := γP) (z₀ := s)
          ⟨δ, hδ_pos, fun t ht => hδ_bound s hs t ht⟩
        unfold generalizedWindingNumber at hw_def
        rw [h1.cauchyPV_eq] at hw_def
        have h2pi_ne : (2 * (↑Real.pi : ℂ) * I) ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero
            (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
        rw [hw_def, mul_inv_cancel_left₀ h2pi_ne]
      have h_const_factor : γP.contourIntegral (fun z => residue f s / (z - s)) =
          residue f s * γP.contourIntegral (fun z => (z - s)⁻¹) := by
        rw [show (fun z => residue f s / (z - s)) =
            (fun z => residue f s * (z - s)⁻¹) from funext fun z => div_eq_mul_inv _ _]
        exact PiecewiseC1Path.contourIntegral_smul (residue f s) _ γP
      rw [h_const_factor, h_winding_int_eq]
      ring
    · have h_residue_zero : residue f s = 0 := by
        have h := decomp.residue_eq s hs
        rwa [dif_neg h_order_pos] at h
      rw [h_residue_zero, mul_zero]
      apply Finset.sum_eq_zero
      intro k _
      exfalso
      have := k.isLt
      omega
  obtain ⟨w₀, hw₀_in_U, hw₀_off⟩ :=
    ForMathlib.exists_mem_not_mem_path_image_of_isOpen γP hU_open hU_ne hLip
  obtain ⟨δ', hδ'_pos, hδ'_bound⟩ := avoids_delta_bound γP w₀ hw₀_off
  have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have hG_diff : DifferentiableOn ℂ (fun z => (z - w₀) * decomp.analyticRemainder z) U :=
    fun z hz => ((differentiableAt_id.sub_const w₀).differentiableWithinAt).mul
      (decomp.analyticRemainder_diff z hz)
  have h_dixon_G : ∀ w,
      dixonFunction (fun z => (z - w₀) * decomp.analyticRemainder z) U γP w = 0 :=
    dixonFunction_eq_zero_of_nullHomologous_open_full_unbounded hU_open hG_diff
      γ.toPwC1Immersion h_null hLip
      (fun w hw_notin h_avoid_local =>
        h_null.winding_zero_nhds_of_not_mem_of_closed hw_notin h_avoid_local hLip)
  have hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γP t ∈ U := h_null.image_subset
  have h_inv_cont : ContinuousOn
      (fun t => (γP t - w₀)⁻¹) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    refine ContinuousOn.inv₀
      (γP.toPath.continuous_extend.continuousOn.sub continuousOn_const) ?_
    intro t ht heq
    have := hδ'_bound t ht
    rw [heq, norm_zero] at this
    linarith
  have h_base_int : IntervalIntegrable
      (fun t => (γP t - w₀)⁻¹ * deriv γP.toPath.extend t)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_inv_cont
  have h_rem_curve_cont : ContinuousOn
      (fun t => decomp.analyticRemainder (γP t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact decomp.analyticRemainder_diff.continuousOn.comp
      γP.toPath.continuous_extend.continuousOn (fun t ht => hγ_in_U t ht)
  have h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_rem_curve_cont
  have h_cauchy_int : IntervalIntegrable
      (fun t => (γP t - w₀) * decomp.analyticRemainder (γP t) / (γP t - w₀) *
        deriv γP.toPath.extend t) MeasureTheory.volume 0 1 := by
    refine h_rem_int.congr ?_
    intro t ht
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    have h_ne : γP t - w₀ ≠ 0 :=
      sub_ne_zero.mpr (hw₀_off t (Ioc_subset_Icc_self ht))
    change PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP t =
      (γP t - w₀) * decomp.analyticRemainder (γP t) / (γP t - w₀) *
        deriv γP.toPath.extend t
    unfold PiecewiseC1Path.contourIntegrand
    rw [show (γP t - w₀) * decomp.analyticRemainder (γP t) / (γP t - w₀) =
      decomp.analyticRemainder (γP t) from by field_simp]
  have h_rem_zero : γP.contourIntegral decomp.analyticRemainder = 0 :=
    contourIntegral_eq_zero_of_nullHomologous_at w₀ hw₀_in_U hw₀_off
      (h_dixon_G w₀) h_cauchy_int h_base_int
  have h_polar_int : ∀ s ∈ S, IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP)
      MeasureTheory.volume 0 1 := by
    intro s hs
    have h_avoid_s : ∀ t ∈ Icc (0 : ℝ) 1, γP.toPath.extend t ≠ s :=
      hγ_avoids s hs
    have h_pp_curve_cont : ContinuousOn
        (fun t => decomp.polarPart s (γP.toPath.extend t)) (uIcc (0 : ℝ) 1) := by
      rw [uIcc_of_le (zero_le_one' ℝ)]
      have h_sum_cont : ContinuousOn
          (fun t => ∑ k : Fin (decomp.order s),
            decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1))
          (Icc (0 : ℝ) 1) := by
        refine continuousOn_finset_sum _ ?_
        intro k _
        apply ContinuousOn.div continuousOn_const
        · exact (γP.toPath.continuous_extend.continuousOn.sub continuousOn_const).pow _
        · intro t ht hzero
          exact h_avoid_s t ht
            (sub_eq_zero.mp (pow_eq_zero_iff (Nat.succ_pos _).ne' |>.mp hzero))
      refine h_sum_cont.congr ?_
      intro t ht
      change decomp.polarPart s (γP.toPath.extend t) =
        ∑ k : Fin (decomp.order s),
          decomp.coeff s k / (γP.toPath.extend t - s) ^ (k.val + 1)
      exact decomp.polarPart_eq s hs (γP.toPath.extend t) (h_avoid_s t ht)
    exact h_deriv_int.continuousOn_mul h_pp_curve_cont
  have h_total_polar_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => ∑ s ∈ S, decomp.polarPart s z) γP) MeasureTheory.volume 0 1 := by
    have h_eq : (fun t : ℝ =>
        (∑ s ∈ S, decomp.polarPart s (γP.toPath.extend t)) *
          deriv γP.toPath.extend t) =
        fun t => ∑ s ∈ S, decomp.polarPart s (γP.toPath.extend t) *
          deriv γP.toPath.extend t := by
      funext t
      rw [Finset.sum_mul]
    change IntervalIntegrable
      (fun t => (∑ s ∈ S, decomp.polarPart s (γP.toPath.extend t)) *
        deriv γP.toPath.extend t) volume 0 1
    rw [h_eq]
    have h_sum := IntervalIntegrable.sum S (fun s hs => h_polar_int s hs)
    have hfun : (∑ s ∈ S, PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP) =
        fun t => ∑ s ∈ S, decomp.polarPart s (γP.toPath.extend t) *
          deriv γP.toPath.extend t := by
      funext t
      rw [Finset.sum_apply]
      rfl
    rwa [hfun] at h_sum
  have h_int_eq : γP.contourIntegral f =
      γP.contourIntegral (fun z =>
        decomp.analyticRemainder z + ∑ s ∈ S, decomp.polarPart s z) := by
    simp only [PiecewiseC1Path.contourIntegral]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (zero_le_one' ℝ)] at ht
    have h_in : γP t ∈ U \ (↑S : Set ℂ) :=
      ⟨hγ_in_U t ht, fun hmem => hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
    change f (γP t) * deriv γP.toPath.extend t =
      (decomp.analyticRemainder (γP t) + ∑ s ∈ S, decomp.polarPart s (γP t)) *
        deriv γP.toPath.extend t
    rw [decomp.decomp _ h_in]
  have h_total : γP.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γP s * residue f s := by
    rw [h_int_eq, PiecewiseC1Path.contourIntegral_add _ _ γP h_rem_int h_total_polar_int,
        h_rem_zero, zero_add,
        contourIntegral_finset_sum S (fun s z => decomp.polarPart s z) γP h_polar_int]
    exact Finset.sum_congr rfl (fun s hs => h_polarPart_integral s hs)
  rw [← h_total]
  exact hasCauchyPVOn_of_avoids ⟨δ, hδ_pos, hδ_bound⟩
