/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.NullHomologous
import LeanModularForms.ForMathlib.DixonTheorem
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.SimplePoleIntegral
import LeanModularForms.ForMathlib.MultipointPV
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import LeanModularForms.ForMathlib.MeromorphicCauchy
import LeanModularForms.ForMathlib.CurveMeasureZero
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue.MeasureHelpers

-- NOTE on imports / Central B:
-- The project currently maintains two parallel residue libraries with overlapping
-- root-namespace identifiers (e.g. both `LeanModularForms.ForMathlib.Residue` and
-- `LeanModularForms.ForMathlib.GeneralizedResidueTheory.Residue` define
-- `HasSimplePoleAt`; both `MultipointPV` files define `disjoint_balls_of_small_epsilon`).
-- This file commits to the legacy chain (`Residue`, `SimplePoleIntegral`,
-- `MultipointPV`, `MeromorphicCauchy`). Central theorem B
-- (`residueTheorem_simplePoles_convex`) and corollary 4
-- (`residueTheorem_simplePoles_convex_transverse`) wrap the existing
-- `generalizedResidueTheorem'` in `GeneralizedResidueTheory.Residue.GeneralizedTheoremBase`,
-- which uses the GRT chain. Until the two trees are unified (out of scope here),
-- those two thin wrappers live in a sibling file
-- `HungerbuhlerWasemConvex.lean` (TODO).

/-!
# Hungerbühler–Wasem residue theorem

The generalized residue theorem of Hungerbühler and Wasem
(arXiv:1808.00997v2, Theorem 3.3): the Cauchy principal value of `∮f` along a
closed piecewise-`C¹` immersion `γ` null-homologous in an open domain `U`
equals `2πi · Σ winding(γ, s) · residue(f, s)` over the singular set `S ⊆ U`.

## Main results

* `HungerbuhlerWasem.PolarPartDecomposition` — the data of an explicit
  Laurent polar-part decomposition of a meromorphic function.
* `HungerbuhlerWasem.residueTheorem_avoidance` — central theorem A:
  decomposition-as-data form. γ avoids every pole.
* `HungerbuhlerWasem.residueTheorem_simplePoles_convex` — central theorem B:
  simple poles only on a convex domain. γ may cross poles, but two CPV
  oracles must be supplied.
* Four corollaries specializing one or the other central theorem:
  `residueTheorem_simplePoles_avoidance`, `residueTheorem_convex_avoidance`,
  `residueTheorem_simplePoles_convex_avoidance`,
  `residueTheorem_simplePoles_convex_transverse`.
* `HungerbuhlerWasem.residueTheorem_crossing` — unifying form (higher-order
  + crossings); lives in
  `LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing`.
-/

open Set Filter Topology Complex MeasureTheory
open scoped Interval

noncomputable section

namespace HungerbuhlerWasem

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

/-! ## Polar-part split helpers -/

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
  rw [PiecewiseC1Path.contourIntegral_finset_sum Finset.univ _ γ (fun k _ => h_int k)]
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

/-! ## Analytic remainder Cauchy under crossings (T-AR-01) -/

variable {x : ℂ}

/-- The contour integral of the analytic remainder along a null-homologous
closed γ in U vanishes — even when γ passes through poles of f, because the
analytic remainder extends to all of U by construction of `PolarPartDecomposition`. -/
theorem analyticRemainder_contourIntegral_zero
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U) :
    γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral
      decomp.analyticRemainder = 0 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
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
  exact contourIntegral_eq_zero_of_nullHomologous_at w₀ hw₀_in_U hw₀_off
    (h_dixon_G w₀) h_cauchy_int h_base_int

/-! ## Analytic remainder CPV (T-BR-05)

The two oracle hypotheses `h_rem_cpv` / `h_rem_int` of `residueTheorem_crossing` —
asserting the multi-point CPV of the analytic remainder along γ vanishes and that
its cutoff integrand is interval-integrable — are derivable from
`analyticRemainder_contourIntegral_zero` plus differentiability of the remainder
on all of `U`. -/

/-- The bad set `γ⁻¹(S) ∩ Icc 0 1` for a piecewise-`C¹` immersion `γ` and a
finite set `S` has Lebesgue measure zero. -/
theorem volume_preimage_finset_in_Icc01_zero
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) :
    volume {t ∈ Icc (0 : ℝ) 1 |
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set ℂ)} = 0 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set P : Finset ℝ := insert 0 (insert 1 γP.partition)
  have hP_zero : (0 : ℝ) ∈ P := Finset.mem_insert_self _ _
  have hP_one : (1 : ℝ) ∈ P :=
    Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have h_in_Ioo : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P → t ∈ Ioo (0 : ℝ) 1 := by
    intro t ht htP
    have h0 : t ≠ 0 := fun h => htP (h ▸ hP_zero)
    have h1 : t ≠ 1 := fun h => htP (h ▸ hP_one)
    exact ⟨lt_of_le_of_ne ht.1 (Ne.symm h0), lt_of_le_of_ne ht.2 h1⟩
  have h_not_part : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P → t ∉ γP.partition := by
    intro t _ htP h_part
    exact htP (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h_part))
  have hγ_diff : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P →
      DifferentiableAt ℝ γP.toPath.extend t := by
    intro t ht htP
    exact γP.differentiable_off t (h_in_Ioo t ht htP) (h_not_part t ht htP)
  have hγ'_ne : ∀ t ∈ Icc (0 : ℝ) 1, t ∉ P → deriv γP.toPath.extend t ≠ 0 := by
    intro t ht htP
    exact γ.toPwC1Immersion.deriv_ne_zero t (h_in_Ioo t ht htP)
      (h_not_part t ht htP)
  have hγ_cont : ContinuousOn γP.toPath.extend (Icc (0 : ℝ) 1) :=
    γP.toPath.continuous_extend.continuousOn
  exact preimage_finset_measure_zero_of_deriv_ne_zero S hγ_cont hγ_diff hγ'_ne

/-- For a function `g` differentiable on `U` and a closed piecewise-`C¹`
immersion `γ` with image in `U`, the contour integrand `g(γ(t)) · γ'(t)` is
interval-integrable on `[0, 1]`. -/
private theorem contourIntegrand_diff_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {g : ℂ → ℂ}
    (h_diff : DifferentiableOn ℂ g U)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) :
    IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand g
        γ.toPwC1Immersion.toPiecewiseC1Path) MeasureTheory.volume 0 1 := by
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have h_curve_cont : ContinuousOn (fun t => g (γP t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact h_diff.continuousOn.comp γP.toPath.continuous_extend.continuousOn
      (fun t ht => hγ_in_U t ht)
  exact h_deriv_int.continuousOn_mul h_curve_cont

/-- The "bad set" of times where γ comes within ε of some pole. -/
def cpv_badSet (γP : PiecewiseC1Path x x) (S : Finset ℂ) (ε : ℝ) :
    Set ℝ := {t : ℝ | ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε}

private theorem cpv_badSet_isClosed (γP : PiecewiseC1Path x x) (S : Finset ℂ) (ε : ℝ) :
    IsClosed (cpv_badSet γP S ε) := by
  classical
  unfold cpv_badSet
  have h_eq : {t : ℝ | ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε} =
      ⋃ s ∈ S, {t : ℝ | ‖γP.toPath.extend t - s‖ ≤ ε} := by
    ext t; simp [Set.mem_setOf_eq]
  rw [h_eq]
  refine isClosed_biUnion_finset fun s _ => ?_
  exact isClosed_le ((γP.toPath.continuous_extend.sub continuous_const).norm)
    continuous_const

private theorem cpv_badSet_measurableSet (γP : PiecewiseC1Path x x) (S : Finset ℂ)
    (ε : ℝ) : MeasurableSet (cpv_badSet γP S ε) :=
  (cpv_badSet_isClosed γP S ε).measurableSet

/-- Express `cpvIntegrandOn S g γ.extend ε` as an indicator of the contour
integrand on the complement of the bad set. -/
theorem cpvIntegrandOn_eq_indicator_compl
    (γP : PiecewiseC1Path x x) (S : Finset ℂ) (g : ℂ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S g γP.toPath.extend ε t =
      (cpv_badSet γP S ε)ᶜ.indicator
        (PiecewiseC1Path.contourIntegrand g γP) t := by
  classical
  unfold cpvIntegrandOn cpv_badSet
  by_cases h : ∃ s ∈ S, ‖γP.toPath.extend t - s‖ ≤ ε
  · simp only [h, ite_true]
    rw [Set.indicator_of_notMem]
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not]
    exact h
  · simp only [h, ite_false]
    rw [Set.indicator_of_mem]
    · rfl
    · simp only [Set.mem_compl_iff, Set.mem_setOf_eq]; exact h

/-- The cutoff integrand `cpvIntegrandOn S g γ.extend ε` is interval-integrable
on `[0, 1]` for any `ε`, when `g` is differentiable on `U` and γ has image in
`U`. The proof realizes the cutoff as an indicator of the (interval-integrable)
contour integrand on a measurable set. -/
theorem cpvIntegrandOn_diff_intervalIntegrable
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) {U : Set ℂ} {g : ℂ → ℂ}
    (h_diff : DifferentiableOn ℂ g U)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U) (ε : ℝ) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S g
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      MeasureTheory.volume 0 1 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_full := contourIntegrand_diff_intervalIntegrable γ h_diff hγ_in_U
  have h_indicator_eq :
      (fun t => cpvIntegrandOn S g γP.toPath.extend ε t) =
      (cpv_badSet γP S ε)ᶜ.indicator
        (PiecewiseC1Path.contourIntegrand g γP) :=
    funext fun t => cpvIntegrandOn_eq_indicator_compl γP S g ε t
  rw [h_indicator_eq]
  rw [intervalIntegrable_iff] at h_full ⊢
  exact h_full.indicator (cpv_badSet_measurableSet γP S ε).compl

/-- Almost every `t ∈ Icc 0 1` satisfies `γ(t) ∉ S` — a consequence of the
immersion property (the bad set has measure zero). -/
private theorem cpv_ae_not_mem_S (γ : ClosedPwC1Immersion x) (S : Finset ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Icc (0 : ℝ) 1)),
      γ.toPwC1Immersion.toPiecewiseC1Path t ∉ (↑S : Set ℂ) := by
  have h_zero := volume_preimage_finset_in_Icc01_zero γ S
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_iff]
  refine MeasureTheory.measure_mono_null ?_ h_zero
  intro t ht
  push Not at ht
  exact ⟨ht.1, ht.2⟩

/-- For a function `g` differentiable on `U` and γ ⊆ U, the cutoff integrands
converge pointwise a.e. on `Icc 0 1` to the contour integrand as `ε → 0⁺`. -/
theorem cpvIntegrandOn_tendsto_contourIntegrand_ae
    (γ : ClosedPwC1Immersion x) (S : Finset ℂ) (g : ℂ → ℂ) :
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)),
      Tendsto
        (fun ε => cpvIntegrandOn S g
          γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
        (𝓝[>] 0)
        (𝓝 (PiecewiseC1Path.contourIntegrand g
          γ.toPwC1Immersion.toPiecewiseC1Path t)) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have h_ae := cpv_ae_not_mem_S γ S
  rw [Set.uIoc_of_le zero_le_one]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_ae
  filter_upwards [h_ae] with t h_not_mem ht
  have h_not_mem' : γP t ∉ (↑S : Set ℂ) := h_not_mem ⟨le_of_lt ht.1, ht.2⟩
  have h_far : ∀ s ∈ S, 0 < ‖γP.toPath.extend t - s‖ := fun s hs =>
    norm_pos_iff.mpr <| sub_ne_zero.mpr <| fun heq =>
      h_not_mem' (heq ▸ Finset.mem_coe.mpr hs : γP.toPath.extend t ∈ (↑S : Set ℂ))
  by_cases hS : S.Nonempty
  · -- Take δ = min over S of ‖γ t - s‖ > 0
    obtain ⟨δ, hδ_mem, hδ_min⟩ := Finset.exists_min_image S
      (fun s => ‖γP.toPath.extend t - s‖) hS
    have hδ_pos : 0 < ‖γP.toPath.extend t - δ‖ := h_far δ hδ_mem
    have h_lim_const :
        (fun ε => cpvIntegrandOn S g γP.toPath.extend ε t) =ᶠ[𝓝[>] 0]
          (fun _ => PiecewiseC1Path.contourIntegrand g γP t) := by
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε
      have h_all : ∀ s ∈ S, ε < ‖γP.toPath.extend t - s‖ := fun s hs =>
        lt_of_lt_of_le hε.2 (hδ_min s hs)
      rw [cpvIntegrandOn_of_forall_gt h_all]
      rfl
    exact Tendsto.congr' h_lim_const.symm tendsto_const_nhds
  · -- Empty S
    have h_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have h_lim_const :
        (fun ε => cpvIntegrandOn S g γP.toPath.extend ε t) =ᶠ[𝓝[>] 0]
          (fun _ => PiecewiseC1Path.contourIntegrand g γP t) := by
      filter_upwards [self_mem_nhdsWithin] with ε _
      subst h_empty
      rfl
    exact Tendsto.congr' h_lim_const.symm tendsto_const_nhds

/-- The Cauchy principal value of the analytic remainder along a null-homologous
closed piecewise-`C¹` immersion vanishes — even when `γ` may pass through poles
of `f`, because the analytic remainder extends to all of `U` by construction
of the polar-part decomposition.

This eliminates the `h_rem_cpv` oracle from `residueTheorem_crossing`. -/
theorem analyticRemainder_hasCauchyPVOn_zero
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (decomp : PolarPartDecomposition f S U) :
    HasCauchyPVOn S decomp.analyticRemainder
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  have hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γP t ∈ U := h_null.image_subset
  have h_full := contourIntegrand_diff_intervalIntegrable γ
    decomp.analyticRemainder_diff hγ_in_U
  have h_zero := analyticRemainder_contourIntegral_zero hU_open hU_ne hS_in_U
    γ h_null decomp
  -- Now apply DCT: the cutoff integrals tend to ∫ contourIntegrand = 0.
  have h_meas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun t => cpvIntegrandOn S decomp.analyticRemainder
        γP.toPath.extend ε t)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have h_full_int := cpvIntegrandOn_diff_intervalIntegrable γ S
      decomp.analyticRemainder_diff hγ_in_U ε
    exact h_full_int.aestronglyMeasurable_restrict_uIoc
  have h_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Set.uIoc (0 : ℝ) 1 →
      ‖cpvIntegrandOn S decomp.analyticRemainder γP.toPath.extend ε x‖ ≤
        ‖PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP x‖ := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine MeasureTheory.ae_of_all _ fun t _ => ?_
    rw [cpvIntegrandOn_eq_indicator_compl γP S decomp.analyticRemainder ε t]
    by_cases ht_in : t ∈ (cpv_badSet γP S ε)ᶜ
    · rw [Set.indicator_of_mem ht_in]
    · rw [Set.indicator_of_notMem ht_in]
      simp only [norm_zero]
      exact norm_nonneg _
  have h_pointwise_raw := cpvIntegrandOn_tendsto_contourIntegrand_ae γ S
    decomp.analyticRemainder
  have h_pointwise : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.uIoc (0 : ℝ) 1 →
      Tendsto (fun ε => cpvIntegrandOn S decomp.analyticRemainder
          γP.toPath.extend ε x) (𝓝[>] 0)
        (𝓝 (PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP x)) := by
    rwa [MeasureTheory.ae_restrict_iff' measurableSet_uIoc] at h_pointwise_raw
  have h_dct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => ‖PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP t‖)
    h_meas h_bound h_full.norm h_pointwise
  unfold HasCauchyPVOn
  rw [show (0 : ℂ) = γP.contourIntegral decomp.analyticRemainder from h_zero.symm]
  exact h_dct

/-! ## Polar-part cutoff integrability (T-BR-05b)

The cutoff integrand `cpvIntegrandOn S (decomp.polarPart s) γ.extend ε` is
interval-integrable on `[0, 1]` for every `ε > 0`. Unlike the analytic
remainder, the polar part is not differentiable on all of `U` (it has a
singularity at `s ∈ S`); however, the cutoff zeroes the integrand on the
"bad set" `{t : ∃ s' ∈ S, ‖γ(t) - s'‖ ≤ ε}`, and on its complement the polar
part's value is bounded by the explicit Laurent estimate
`∑_k ‖coeff s k‖ / ε^(k+1)`. -/

/-- Interval-integrability of the cutoff integrand of a polar part of the
decomposition. Eliminates the `h_polar_int` oracle from
`residueTheorem_crossing`. -/
theorem cpvIntegrandOn_polarPart_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {U : Set ℂ} {S : Finset ℂ}
    (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ}
    (decomp : PolarPartDecomposition f S U) {s : ℂ} (hs : s ∈ S)
    (_h_null : IsNullHomologous γ.toPwC1Immersion U) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S (decomp.polarPart s)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend ε t)
      MeasureTheory.volume 0 1 := by
  classical
  obtain ⟨K, hLip⟩ := ClosedPwC1Immersion.lipschitzWith_extend γ
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path
  set N : ℕ := decomp.order s
  set a : Fin N → ℂ := decomp.coeff s
  -- Patched Laurent-sum function (well-defined globally; equals `polarPart s`
  -- off `{s}` by `polarPart_eq`).
  set laurentSum : ℂ → ℂ := fun z => ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)
  -- Patched integrand using `laurentSum` everywhere.
  set h_curve : ℝ → ℂ := fun t =>
    laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
  -- Step 1: cpvIntegrandOn rewritten as indicator of (badSet)ᶜ applied to
  -- the contour integrand of `polarPart s`.
  have h_indicator_eq :
      (fun t => cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) =
      (cpv_badSet γP S ε)ᶜ.indicator
        (PiecewiseC1Path.contourIntegrand (decomp.polarPart s) γP) :=
    funext fun t =>
      cpvIntegrandOn_eq_indicator_compl γP S (decomp.polarPart s) ε t
  -- Step 2: on (badSet)ᶜ, contour integrand of polarPart equals h_curve
  -- (because γ(t) ≠ s, so polarPart_eq applies).
  have h_indicator_eq' :
      (fun t => cpvIntegrandOn S (decomp.polarPart s)
        γP.toPath.extend ε t) =
      (cpv_badSet γP S ε)ᶜ.indicator h_curve := by
    rw [h_indicator_eq]
    funext t
    by_cases ht_in : t ∈ (cpv_badSet γP S ε)ᶜ
    · rw [Set.indicator_of_mem ht_in, Set.indicator_of_mem ht_in]
      have h_far : ∀ s' ∈ S, ε < ‖γP.toPath.extend t - s'‖ := by
        intro s' hs'
        unfold cpv_badSet at ht_in
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and,
          not_le] at ht_in
        exact ht_in s' hs'
      have h_ne : γP.toPath.extend t ≠ s := by
        intro heq
        have := h_far s hs
        rw [heq, sub_self, norm_zero] at this
        linarith
      change decomp.polarPart s (γP.toPath.extend t) *
        deriv γP.toPath.extend t =
        laurentSum (γP.toPath.extend t) * deriv γP.toPath.extend t
      rw [decomp.polarPart_eq s hs (γP.toPath.extend t) h_ne]
    · rw [Set.indicator_of_notMem ht_in, Set.indicator_of_notMem ht_in]
  -- Step 3: bound h_curve on (badSet)ᶜ
  set M_polar : ℝ := ∑ k : Fin N, ‖a k‖ / ε ^ (k.val + 1)
  set M : ℝ := M_polar * K
  have h_M_polar_nonneg : 0 ≤ M_polar :=
    Finset.sum_nonneg (fun k _ => div_nonneg (norm_nonneg _) (pow_nonneg hε.le _))
  have h_M_nonneg : 0 ≤ M := mul_nonneg h_M_polar_nonneg (NNReal.coe_nonneg K)
  have h_bound_on_compl : ∀ t ∈ (cpv_badSet γP S ε)ᶜ, ‖h_curve t‖ ≤ M := by
    intro t ht_in
    have h_far : ∀ s' ∈ S, ε < ‖γP.toPath.extend t - s'‖ := by
      intro s' hs'
      unfold cpv_badSet at ht_in
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and,
        not_le] at ht_in
      exact ht_in s' hs'
    have h_far_s : ε < ‖γP.toPath.extend t - s‖ := h_far s hs
    have h_lap_bound : ‖laurentSum (γP.toPath.extend t)‖ ≤ M_polar := by
      change ‖∑ k : Fin N, a k / (γP.toPath.extend t - s) ^ (k.val + 1)‖ ≤ M_polar
      refine (norm_sum_le _ _).trans ?_
      refine Finset.sum_le_sum fun k _ => ?_
      rw [norm_div, norm_pow]
      apply div_le_div_of_nonneg_left (norm_nonneg _)
        (pow_pos hε _)
      exact pow_le_pow_left₀ hε.le h_far_s.le _
    have h_deriv_bound : ‖deriv γP.toPath.extend t‖ ≤ K :=
      norm_deriv_le_of_lipschitz hLip
    calc ‖h_curve t‖ = ‖laurentSum (γP.toPath.extend t)‖ *
          ‖deriv γP.toPath.extend t‖ := norm_mul _ _
      _ ≤ M_polar * K := by
          apply mul_le_mul h_lap_bound h_deriv_bound (norm_nonneg _) h_M_polar_nonneg
  -- Step 4: bound the indicator everywhere
  have h_bound_indicator : ∀ t,
      ‖(cpv_badSet γP S ε)ᶜ.indicator h_curve t‖ ≤ M := by
    intro t
    by_cases ht_in : t ∈ (cpv_badSet γP S ε)ᶜ
    · rw [Set.indicator_of_mem ht_in]
      exact h_bound_on_compl t ht_in
    · rw [Set.indicator_of_notMem ht_in]
      simp only [norm_zero]
      exact h_M_nonneg
  -- Step 5: measurability of h_curve
  have h_γ_meas : Measurable γP.toPath.extend :=
    γP.toPath.continuous_extend.measurable
  have h_γ'_meas : Measurable (deriv γP.toPath.extend) := measurable_deriv _
  have h_laurentSum_meas : Measurable (fun t => laurentSum (γP.toPath.extend t)) := by
    refine Finset.measurable_sum (Finset.univ : Finset (Fin N)) (fun k _ => ?_)
    refine Measurable.const_div ?_ _
    refine Measurable.pow_const ?_ _
    exact h_γ_meas.sub_const s
  have h_curve_meas : Measurable h_curve :=
    h_laurentSum_meas.mul h_γ'_meas
  -- Step 6: indicator is AEStronglyMeasurable
  have h_aemeas : AEStronglyMeasurable
      ((cpv_badSet γP S ε)ᶜ.indicator h_curve)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) 1)) := by
    refine (h_curve_meas.aestronglyMeasurable).indicator ?_
    exact (cpv_badSet_measurableSet γP S ε).compl
  -- Step 7: integrability
  rw [intervalIntegrable_iff, h_indicator_eq']
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top h_aemeas M ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with t _
  exact h_bound_indicator t

/-! ## Central theorem A: avoidance form -/

/-- **Hungerbühler–Wasem Theorem 3.3 — avoidance form (central A).**

For `f` admitting a `PolarPartDecomposition` over `S ⊆ U` (open, nonempty,
with no other constraint) and a closed paper-faithful piecewise-`C¹`
immersion `γ` null-homologous in `U` and avoiding every pole in `S`, the
contour integral of `f` along `γ` has a Cauchy principal value equal to
`∑ s ∈ S, 2πi · w(γ, s) · residue(f, s)`. -/
theorem residueTheorem_avoidance
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S))
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
    rw [PiecewiseC1Path.contourIntegral_finset_sum Finset.univ _ γP (fun k _ => h_int_each k)]
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
  have h_deriv_int : IntervalIntegrable (deriv γP.toPath.extend)
      MeasureTheory.volume 0 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
    refine MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γP t ∈ U := h_null.image_subset
  have h_rem_curve_cont : ContinuousOn
      (fun t => decomp.analyticRemainder (γP t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact decomp.analyticRemainder_diff.continuousOn.comp
      γP.toPath.continuous_extend.continuousOn (fun t ht => hγ_in_U t ht)
  have h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand decomp.analyticRemainder γP)
      MeasureTheory.volume 0 1 :=
    h_deriv_int.continuousOn_mul h_rem_curve_cont
  have h_rem_zero : γP.contourIntegral decomp.analyticRemainder = 0 :=
    analyticRemainder_contourIntegral_zero hU_open hU_ne hS_in_U γ h_null decomp
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
        PiecewiseC1Path.contourIntegral_finset_sum S (fun s z => decomp.polarPart s z) γP
          h_polar_int]
    exact Finset.sum_congr rfl (fun s hs => h_polarPart_integral s hs)
  rw [← h_total]
  exact hasCauchyPVOn_of_avoids ⟨δ, hδ_pos, hδ_bound⟩

/-! ## Constructors for `PolarPartDecomposition` -/

/-- Build a `PolarPartDecomposition` from the hypothesis that every pole is
simple. The simple-pole coefficient is the residue, and the analytic
remainder is the corrected `f - ∑ residue(f, s) / (z - s)`. -/
noncomputable def PolarPartDecomposition.ofSimplePoles
    {U : Set ℂ} (hU_open : IsOpen U) {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (h_simple : ∀ s ∈ S, HasSimplePoleAt f s) :
    PolarPartDecomposition f S U := by
  classical
  set c : ℂ → ℂ := fun s => if h : s ∈ S then (h_simple s h).coeff else 0
  have hc_eq : ∀ (s : ℂ) (hs : s ∈ S), (h_simple s hs).coeff = c s := by
    intro s hs
    simp [c, hs]
  have hc_residue : ∀ s ∈ S, c s = residue f s := by
    intro s hs
    simp only [c, dif_pos hs]
    exact (residue_eq_coeff_of_hasSimplePoleAt (h_simple s hs)).symm
  set h_ext :=
    sub_principalPartSum_corrected_differentiableOn hU_open hf hS_in_U
      h_simple hc_eq
  let g : ℂ → ℂ := h_ext.choose
  have hg_spec := h_ext.choose_spec
  have hg_diff : DifferentiableOn ℂ g U := hg_spec.1
  have hg_agree : ∀ z ∈ U \ (↑S : Set ℂ), g z = f z - principalPartSum S c z :=
    hg_spec.2
  refine
    { polarPart := fun s z => c s / (z - s)
      order := fun _ => 1
      coeff := fun s _ => c s
      polarPart_eq := ?_
      residue_eq := ?_
      analyticRemainder := g
      analyticRemainder_diff := hg_diff
      decomp := ?_ }
  · intro s _hs z _hz
    simp
  · intro s hs
    simp [hc_residue s hs]
  · intro z hz
    have h_g := hg_agree z hz
    have h_pps : principalPartSum S c z = ∑ s ∈ S, c s / (z - s) := rfl
    rw [h_pps] at h_g
    linear_combination -h_g

/-! ## Corollary: simple-pole avoidance form -/

/-- **Hungerbühler–Wasem — simple-pole avoidance form (corollary).**

Specialization of `residueTheorem_avoidance` to simple poles. The
`PolarPartDecomposition` is constructed automatically from the
`HasSimplePoleAt` hypothesis. -/
theorem residueTheorem_simplePoles_avoidance
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (h_simple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  residueTheorem_avoidance hU_open hU_ne S hS_in_U f hf γ h_null hγ_avoids
    (PolarPartDecomposition.ofSimplePoles hU_open hS_in_U hf h_simple)

/-! ## Corollary: convex-domain avoidance form -/

/-- **Hungerbühler–Wasem — convex-domain avoidance form (corollary).**

When `U` is convex, null-homologous becomes automatic. Higher-order poles
allowed via `PolarPartDecomposition`. -/
theorem residueTheorem_convex_avoidance
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s)
    (decomp : PolarPartDecomposition f S U) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  residueTheorem_avoidance hU_open hU_ne S hS_in_U f hf γ
    (isNullHomologous_of_convex hU_convex hU_open hU_ne γ.toPwC1Immersion hγ_in_U)
    hγ_avoids decomp

/-! ## Corollary: classical residue theorem (convex + simple poles) -/

/-- **Classical residue theorem (corollary).**

Convex `U`, simple poles only, γ avoids the poles. The textbook form. -/
theorem residueTheorem_simplePoles_convex_avoidance
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ U)
    (h_simple : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) :=
  residueTheorem_convex_avoidance hU_convex hU_open hU_ne S hS_in_U f hf γ
    hγ_in_U hγ_avoids
    (PolarPartDecomposition.ofSimplePoles hU_open hS_in_U hf h_simple)

/-! ## Full crossing form

The unified Hungerbühler–Wasem Theorem 3.3 — `residueTheorem_crossing` —
lives in `LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing` (which
imports this file via `LaurentExtraction → CrossingCPV → Crossing`). The
unified form admits γ that may cross poles of any order under conditions
(A') and (B) at each crossing, and returns the same residue formula as the
avoidance form. Both `residueTheorem_avoidance` and the simple-pole
specializations in this file are corollaries. -/

end HungerbuhlerWasem

end
