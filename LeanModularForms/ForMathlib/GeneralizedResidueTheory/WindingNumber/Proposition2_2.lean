/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV
import LeanModularForms.ForMathlib.GeneralizedResidueTheory.OnCurvePV.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Proposition 2.2: Finite Crossings and Isolated Crossing Intervals

For a `PiecewiseC1Immersion` γ : [a,b] → ℂ, we prove that the set of parameter
values where γ passes through a given point z₀ is finite. This is
Proposition 2.2 from Hungerbuhler-Wasem.

## Main Results

* `finite_crossings` — the set `{t ∈ Icc a b | γ t = z₀}` is finite
* `exists_isolated_crossing_interval` — each crossing has an isolating sub-interval

## Proof Strategy

At smooth points, `HasDerivAt.eventually_ne` (from `deriv_ne_zero`) shows crossings
are isolated. At partition points, one-sided derivative limits are nonzero, which
also gives isolation on each side via strict monotonicity of a real projection.
The crossing set is closed and has no accumulation points, hence finite by compactness.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

/-- If `f` has derivative `f'` at `x`, then `Re ∘ f` has derivative `Re(f')` at `x`. -/
private lemma HasDerivAt.re' {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun t => (f t).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- The partition minus a point is finite hence closed; its complement is a nhds of `p`. -/
private lemma eventually_not_in_partition_left
    (γ : PiecewiseC1Immersion) (p : ℝ) :
    ∀ᶠ t in 𝓝[<] p, t ∉ γ.toPiecewiseC1Curve.partition := by
  have hcl : IsClosed ((↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Curve.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ) := by
    simp only [Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff, not_and, not_not,
      implies_true]
  have h1 : ∀ᶠ t in 𝓝[<] p, t ∈ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[<] p, t < p := eventually_nhdsWithin_of_forall fun t ht => ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_lt⟩ ht_part =>
    ht_compl ⟨ht_part, ne_of_lt ht_lt⟩

private lemma eventually_not_in_partition_right
    (γ : PiecewiseC1Immersion) (p : ℝ) :
    ∀ᶠ t in 𝓝[>] p, t ∉ γ.toPiecewiseC1Curve.partition := by
  have hcl : IsClosed ((↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Curve.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ) := by
    simp only [Set.mem_diff, Finset.mem_coe, Set.mem_singleton_iff, not_and, not_not,
      implies_true]
  have h1 : ∀ᶠ t in 𝓝[>] p, t ∈ (↑γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[>] p, p < t := eventually_nhdsWithin_of_forall fun t ht => ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_gt⟩ ht_part =>
    ht_compl ⟨ht_part, ne_of_gt ht_gt⟩

/-- At a smooth point (not in partition) where γ(t₀) = z₀, there is a punctured
neighborhood in which γ(t) ≠ z₀. -/
theorem PiecewiseC1Immersion.eventually_ne_at_smooth_crossing (γ : PiecewiseC1Immersion)
    (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b) (hcross : γ.toFun t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    ∀ᶠ t in 𝓝[≠] t₀, γ.toFun t ≠ z₀ :=
  hcross ▸ (γ.smooth_off_partition t₀ ht₀ hsmooth).hasDerivAt.eventually_ne
    (γ.deriv_ne_zero t₀ ht₀ hsmooth)

/-- At a partition point p with a < p, the left-sided derivative limit is nonzero,
so γ(t) ≠ γ(p) for t sufficiently close to p from the left. -/
theorem PiecewiseC1Immersion.eventually_ne_left_of_partition (γ : PiecewiseC1Immersion)
    (z₀ : ℂ) (p : ℝ) (hp : p ∈ γ.toPiecewiseC1Curve.partition) (hap : γ.a < p) (hpb : p ≤ γ.b)
    (hcross : γ.toFun p = z₀) :
    ∀ᶠ t in 𝓝[<] p, γ.toFun t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.left_deriv_limit p hp hap
  set h : ℝ → ℝ := fun t => ((starRingEnd ℂ L) * (γ.toFun t - z₀)).re with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, mul_zero, Complex.zero_re]
  have h_ev_smooth : ∀ᶠ t in 𝓝[<] p, t ∉ γ.toPiecewiseC1Curve.partition :=
    eventually_not_in_partition_left γ p
  have hL_sq_pos : (0 : ℝ) < ‖L‖ ^ 2 := by positivity
  have h_lim_val : (starRingEnd ℂ L * L).re = ‖L‖ ^ 2 := by
    have : starRingEnd ℂ L * L = (↑(‖L‖) : ℂ) ^ 2 := Complex.conj_mul' L
    rw [this, sq, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[<] p,
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 := by
    have : Tendsto (fun t => (starRingEnd ℂ L * deriv γ.toFun t).re)
        (𝓝[<] p) (𝓝 (‖L‖ ^ 2)) := by
      rw [← h_lim_val]
      exact (continuous_re.tendsto _).comp
        (hL_tendsto.const_mul (starRingEnd ℂ L))
    exact this.eventually (Ioi_mem_nhds hL_sq_pos)
  have h_ev_Iab : ∀ᶠ t in 𝓝[<] p, t ∈ Icc γ.a γ.b := by
    have h1 : ∀ᶠ t in 𝓝[<] p, γ.a < t :=
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hap)
    have h2 : ∀ᶠ t in 𝓝[<] p, t < p := eventually_nhdsWithin_of_forall fun t ht => ht
    exact (h1.and h2).mono fun t ⟨hat, htp⟩ => ⟨hat.le, htp.le.trans hpb⟩
  have h_all : {t | t ∉ γ.toPiecewiseC1Curve.partition ∧
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 ∧ t ∈ Icc γ.a γ.b} ∈ 𝓝[<] p :=
    (h_ev_smooth.and (h_ev_deriv_pos.and h_ev_Iab))
  rw [mem_nhdsLT_iff_exists_Ioo_subset' hap] at h_all
  obtain ⟨q, hq_lt_p, hq_cond⟩ := h_all
  have hqp_sub : Icc q p ⊆ Icc γ.a γ.b := by
    have h_ioo_sub : Ioo q p ⊆ Icc γ.a γ.b := fun t ht => (hq_cond ht).2.2
    have h_cl := closure_minimal h_ioo_sub isClosed_Icc
    rwa [closure_Ioo (ne_of_lt hq_lt_p)] at h_cl
  have hh_cont_qp : ContinuousOn h (Icc q p) :=
    (Complex.continuous_re.comp_continuousOn
      (continuousOn_const.mul (γ.continuous_toFun.mono hqp_sub |>.sub continuousOn_const)))
  have hh_deriv_pos : ∀ s ∈ interior (Icc q p), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_smooth, hs_deriv, hs_Iab⟩ := hq_cond hs
    have hh_has : HasDerivAt h ((starRingEnd ℂ L * deriv γ.toFun s).re) s :=
      (((γ.smooth_off_partition s hs_Iab hs_smooth).hasDerivAt.sub
        (hasDerivAt_const s z₀)).const_mul (starRingEnd ℂ L)).congr_deriv (by ring) |>.re'
    rw [hh_has.deriv]
    exact hs_deriv
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc q p) hh_cont_qp hh_deriv_pos
  rw [Filter.Eventually, mem_nhdsLT_iff_exists_Ioo_subset' hap]
  exact ⟨q, hq_lt_p, fun t ht hγt => by
    have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, mul_zero, Complex.zero_re]
    have : h t < h p := hh_mono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hq_lt_p.le) ht.2
    linarith⟩

/-- At a partition point p with p < b, the right-sided derivative limit is nonzero,
so γ(t) ≠ γ(p) for t sufficiently close to p from the right. -/
theorem PiecewiseC1Immersion.eventually_ne_right_of_partition (γ : PiecewiseC1Immersion)
    (z₀ : ℂ) (p : ℝ) (hp : p ∈ γ.toPiecewiseC1Curve.partition) (hap : γ.a ≤ p) (hpb : p < γ.b)
    (hcross : γ.toFun p = z₀) :
    ∀ᶠ t in 𝓝[>] p, γ.toFun t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.right_deriv_limit p hp hpb
  set h : ℝ → ℝ := fun t => ((starRingEnd ℂ L) * (γ.toFun t - z₀)).re with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, mul_zero, Complex.zero_re]
  have h_ev_smooth : ∀ᶠ t in 𝓝[>] p, t ∉ γ.toPiecewiseC1Curve.partition :=
    eventually_not_in_partition_right γ p
  have hL_sq_pos : (0 : ℝ) < ‖L‖ ^ 2 := by positivity
  have h_lim_val : (starRingEnd ℂ L * L).re = ‖L‖ ^ 2 := by
    have : starRingEnd ℂ L * L = (↑(‖L‖) : ℂ) ^ 2 := Complex.conj_mul' L
    rw [this, sq, ← Complex.ofReal_mul, Complex.ofReal_re, sq]
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[>] p,
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 := by
    have : Tendsto (fun t => (starRingEnd ℂ L * deriv γ.toFun t).re)
        (𝓝[>] p) (𝓝 (‖L‖ ^ 2)) := by
      rw [← h_lim_val]
      exact (continuous_re.tendsto _).comp (hL_tendsto.const_mul (starRingEnd ℂ L))
    exact this.eventually (Ioi_mem_nhds hL_sq_pos)
  have h_ev_Iab : ∀ᶠ t in 𝓝[>] p, t ∈ Icc γ.a γ.b := by
    have h1 : ∀ᶠ t in 𝓝[>] p, t < γ.b :=
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hpb)
    have h2 : ∀ᶠ t in 𝓝[>] p, p < t := eventually_nhdsWithin_of_forall fun t ht => ht
    exact (h1.and h2).mono fun t ⟨htb, htp⟩ => ⟨hap.trans htp.le, htb.le⟩
  have h_all : {t | t ∉ γ.toPiecewiseC1Curve.partition ∧
      (starRingEnd ℂ L * deriv γ.toFun t).re > 0 ∧ t ∈ Icc γ.a γ.b} ∈ 𝓝[>] p :=
    h_ev_smooth.and (h_ev_deriv_pos.and h_ev_Iab)
  rw [mem_nhdsGT_iff_exists_Ioo_subset' hpb] at h_all
  obtain ⟨r, hr_gt_p, hr_cond⟩ := h_all
  have hpr_sub : Icc p r ⊆ Icc γ.a γ.b := by
    have h_ioo_sub : Ioo p r ⊆ Icc γ.a γ.b := fun t ht => (hr_cond ht).2.2
    have h_cl := closure_minimal h_ioo_sub isClosed_Icc
    rwa [closure_Ioo (ne_of_lt hr_gt_p)] at h_cl
  have hh_cont_pr : ContinuousOn h (Icc p r) :=
    (Complex.continuous_re.comp_continuousOn
      (continuousOn_const.mul (γ.continuous_toFun.mono hpr_sub |>.sub continuousOn_const)))
  have hh_deriv_pos : ∀ s ∈ interior (Icc p r), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_smooth, hs_deriv, hs_Iab⟩ := hr_cond hs
    have hh_has : HasDerivAt h ((starRingEnd ℂ L * deriv γ.toFun s).re) s :=
      (((γ.smooth_off_partition s hs_Iab hs_smooth).hasDerivAt.sub
        (hasDerivAt_const s z₀)).const_mul (starRingEnd ℂ L)).congr_deriv (by ring) |>.re'
    rw [hh_has.deriv]
    exact hs_deriv
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc p r) hh_cont_pr hh_deriv_pos
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset' hpb]
  exact ⟨r, hr_gt_p, fun t ht hγt => by
    have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, mul_zero, Complex.zero_re]
    have : h p < h t := hh_mono (left_mem_Icc.mpr hr_gt_p.le) (Ioo_subset_Icc_self ht) ht.1
    linarith⟩

/-- At any crossing t₀ ∈ [a, b], there is a punctured neighborhood with no
other crossings in [a,b]. -/
theorem PiecewiseC1Immersion.crossing_isolated_nhds (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b) (hcross : γ.toFun t₀ = z₀) :
    ∀ᶠ t in 𝓝[≠] t₀, γ.toFun t ≠ z₀ ∨ t ∉ Icc γ.a γ.b := by
  by_cases hpart : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · rw [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, Filter.eventually_sup]
    constructor
    · by_cases hap : γ.a < t₀
      · exact (γ.eventually_ne_left_of_partition z₀ t₀ hpart hap ht₀.2 hcross).mono
          (fun t ht => Or.inl ht)
      · have hle : t₀ ≤ γ.a := not_lt.mp hap
        apply Filter.Eventually.mono
          (eventually_nhdsWithin_of_forall (fun t (ht : t < t₀) => ht))
        intro t ht
        right
        simp only [mem_Icc, not_and_or, not_le]
        left
        linarith
    · by_cases hpb : t₀ < γ.b
      · exact (γ.eventually_ne_right_of_partition z₀ t₀ hpart ht₀.1 hpb hcross).mono
          (fun t ht => Or.inl ht)
      · have hle : γ.b ≤ t₀ := not_lt.mp hpb
        apply Filter.Eventually.mono
          (eventually_nhdsWithin_of_forall (fun t (ht : t₀ < t) => ht))
        intro t ht
        right
        simp only [mem_Icc, not_and_or, not_le]
        right
        linarith
  · exact (γ.eventually_ne_at_smooth_crossing z₀ t₀ ht₀ hcross hpart).mono
      (fun t ht => Or.inl ht)

/-- No point of the crossing set is an accumulation point. -/
theorem PiecewiseC1Immersion.crossing_not_accPt (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc γ.a γ.b) (hcross : γ.toFun t₀ = z₀) :
    ¬AccPt t₀ (𝓟 {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}) := by
  rw [accPt_iff_frequently_nhdsNE, Filter.not_frequently]
  exact (γ.crossing_isolated_nhds z₀ t₀ ht₀ hcross).mono
    (fun t ht ht_mem => by
      simp only [mem_setOf_eq] at ht_mem
      exact ht.elim (fun h => h ht_mem.2) (fun h => h ht_mem.1))

/-- The crossing set is closed. -/
theorem crossing_set_isClosed (γ : PiecewiseC1Immersion) (z₀ : ℂ) :
    IsClosed {t ∈ Icc γ.a γ.b | γ.toFun t = z₀} := by
  change IsClosed (Icc γ.a γ.b ∩ γ.toFun ⁻¹' {z₀})
  exact γ.continuous_toFun.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton

/-- For each crossing, there exists an isolating sub-interval. -/
theorem exists_isolated_crossing_interval (γ : PiecewiseC1Immersion) (z₀ : ℂ) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) :
    ∃ a' b' : ℝ, a' < t₀ ∧ t₀ < b' ∧
      Icc a' b' ⊆ Icc γ.a γ.b ∧
      (∀ t ∈ Icc a' b', γ.toFun t = z₀ → t = t₀) ∧
      (∀ t ∈ Ioo a' b', t ∉ γ.toPiecewiseC1Curve.partition →
        DifferentiableAt ℝ γ.toFun t) := by
  have h_isol := γ.crossing_isolated_nhds z₀ t₀ (Ioo_subset_Icc_self ht₀) hcross
  rw [eventually_nhdsWithin_iff] at h_isol
  obtain ⟨l, u, ⟨hl_lt, hlt_u⟩, h_Ioo⟩ := h_isol.exists_Ioo_subset
  set a' := (max l γ.a + t₀) / 2 with ha'_def
  set b' := (t₀ + min u γ.b) / 2 with hb'_def
  have h_max_lt : max l γ.a < t₀ := max_lt hl_lt ht₀.1
  have h_t₀_lt_min : t₀ < min u γ.b := lt_min hlt_u ht₀.2
  have ha'_lt : a' < t₀ := by linarith
  have ht₀_lt_b' : t₀ < b' := by linarith
  have hl_lt_a' : l < a' := by linarith [le_max_left l γ.a]
  have hb'_lt_u : b' < u := by linarith [min_le_left u γ.b]
  have ha_le_a' : γ.a ≤ a' := by linarith [le_max_right l γ.a]
  have hb'_le_b : b' ≤ γ.b := by linarith [min_le_right u γ.b]
  refine ⟨a', b', ha'_lt, ht₀_lt_b', ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨le_trans ha_le_a' ht.1, le_trans ht.2 hb'_le_b⟩
  · intro t ht hγt
    by_contra h_ne
    have ht_Ioo_lu : t ∈ Ioo l u :=
      ⟨lt_of_lt_of_le hl_lt_a' ht.1, lt_of_le_of_lt ht.2 hb'_lt_u⟩
    have := h_Ioo ht_Ioo_lu h_ne
    rcases this with h_ne_z₀ | h_not_Icc
    · exact h_ne_z₀ hγt
    · exact h_not_Icc ⟨le_trans ha_le_a' ht.1, le_trans ht.2 hb'_le_b⟩
  · intro t ht ht_part
    have ht_Icc : t ∈ Icc γ.a γ.b :=
      ⟨le_trans ha_le_a' (Ioo_subset_Icc_self ht).1,
       le_trans (Ioo_subset_Icc_self ht).2 hb'_le_b⟩
    exact γ.smooth_off_partition t ht_Icc ht_part

theorem PiecewiseC1Immersion.deriv_ne_zero_of_C2 (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo γ.a γ.b) (hγ_C2 : ContDiffAt ℝ 2 γ.toFun t₀) :
    deriv γ.toFun t₀ ≠ 0 := by
  by_cases hpart : t₀ ∈ γ.toPiecewiseC1Curve.partition
  · have h_cont_at : ContinuousAt (deriv γ.toFun) t₀ :=
      continuousAt_deriv_of_contDiffAt_two hγ_C2
    obtain ⟨L, hL_ne, hL_tend⟩ := γ.right_deriv_limit t₀ hpart ht₀.2
    have h_eq : deriv γ.toFun t₀ = L :=
      tendsto_nhds_unique (h_cont_at.mono_left nhdsWithin_le_nhds) hL_tend
    rw [h_eq]
    exact hL_ne
  · exact γ.deriv_ne_zero t₀ (Ioo_subset_Icc_self ht₀) hpart

/-- CPV of `(z - z₀)⁻¹` exists on a sub-interval with a single crossing,
given C² regularity at the crossing point.

This combines `pv_limit_via_dyadic` with `cpv_exists_from_shifted_tendsto`
to prove CPV existence on a sub-interval containing exactly one crossing. -/
theorem cpv_exists_single_crossing (γ : PiecewiseC1Immersion) (z₀ : ℂ) (a' b' t₀ : ℝ)
    (hat₀ : t₀ ∈ Ioo a' b') (hcross : γ.toFun t₀ = z₀) (h_sub : Icc a' b' ⊆ Icc γ.a γ.b)
    (h_inj : ∀ t ∈ Icc a' b', γ.toFun t = z₀ → t = t₀) (hγ_C2 : ContDiffAt ℝ 2 γ.toFun t₀)
    (h_cont_deriv : ContinuousOn (deriv γ.toFun) (Icc a' b')) (hγ_meas : Measurable γ.toFun) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun a' b' z₀ := by
  have hab' : a' ≤ b' := (hat₀.1.trans hat₀.2).le
  have ht₀_Ioo_ab : t₀ ∈ Ioo γ.a γ.b :=
    ⟨(h_sub (left_mem_Icc.mpr hab')).1.trans_lt hat₀.1,
     hat₀.2.trans_le (h_sub (right_mem_Icc.mpr hab')).2⟩
  have hL_ne : deriv γ.toFun t₀ ≠ 0 := γ.deriv_ne_zero_of_C2 t₀ ht₀_Ioo_ab hγ_C2
  have hγ_cont : ContinuousOn γ.toFun (Icc a' b') := γ.continuous_toFun.mono h_sub
  have h_inj' : ∀ t ∈ Icc a' b', γ.toFun t = γ.toFun t₀ → t = t₀ :=
    fun t ht hγt => h_inj t ht (hγt.trans hcross)
  obtain ⟨limit, h_limit⟩ := pv_limit_via_dyadic hat₀ hL_ne hγ_C2
    rfl h_cont_deriv hγ_meas hγ_cont h_inj'
  exact ⟨limit, h_limit.congr (fun ε => intervalIntegral.integral_congr
    (fun t _ => by rw [hcross]))⟩

/-- The cutoff integrand for `(z - z₀)⁻¹` is interval-integrable along a
piecewise C¹ curve. The integrand is bounded: `(γ(t) - z₀)⁻¹` is bounded by
`1/ε` on the region `‖γ(t) - z₀‖ > ε`, and the derivative is locally bounded
by continuity. -/
theorem cpv_integrand_intervalIntegrable (γ : PiecewiseC1Immersion) (z₀ : ℂ) (c d : ℝ)
    (hcd : c ≤ d) (h_sub : Icc c d ⊆ Icc γ.a γ.b) (ε : ℝ) (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ε < ‖γ.toFun t - z₀‖
        then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0)
      volume c d := by
  obtain ⟨D, hD⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hD_nn : 0 ≤ D := (norm_nonneg _).trans (hD γ.a (left_mem_Icc.mpr γ.hab.le))
  set g : ℝ → ℂ := fun t => if ε < ‖γ.toFun t - z₀‖
      then (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t else 0 with hg_def
  have h_bound : ∀ t ∈ Icc c d, ‖g t‖ ≤ ε⁻¹ * D := fun t ht => by
    simp only [hg_def]
    split_ifs with h
    · rw [norm_mul, norm_inv]
      exact mul_le_mul (inv_anti₀ hε h.le) (hD t (h_sub ht))
        (norm_nonneg _) (inv_nonneg.mpr hε.le)
    · simp only [norm_zero]; exact mul_nonneg (inv_nonneg.mpr hε.le) hD_nn
  have hγ_cont_cd : ContinuousOn γ.toFun (Icc c d) := γ.continuous_toFun.mono h_sub
  have hS_meas : MeasurableSet ({t | ε < ‖γ.toFun t - z₀‖} ∩ Icc c d) :=
    measurableSet_norm_gt_Icc ε (hγ_cont_cd.sub continuousOn_const)
  have h_meas : AEStronglyMeasurable g (volume.restrict (Icc c d)) := by
    let S := {t | ε < ‖γ.toFun t - z₀‖} ∩ Icc c d
    have h_pw : AEStronglyMeasurable
        (S.piecewise (fun t => (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t) (fun _ => (0 : ℂ)))
        volume := by
      refine AEStronglyMeasurable.piecewise hS_meas ?_ aestronglyMeasurable_const
      have h_cont_on_S : ContinuousOn (fun t => (γ.toFun t - z₀)⁻¹ * deriv γ.toFun t)
          (S \ γ.partition) := by
        intro t ⟨⟨ht_far, ht_Icc⟩, ht_notP⟩
        have h_ne : γ.toFun t - z₀ ≠ 0 := fun heq => by
          simp only [Set.mem_setOf_eq, heq, norm_zero] at ht_far; linarith
        refine ContinuousWithinAt.mul
          (((hγ_cont_cd.continuousWithinAt ht_Icc).sub continuousWithinAt_const
            |>.mono (fun x hx => hx.1.2)).inv₀ h_ne) ?_
        by_cases ht_Ioo : t ∈ Ioo γ.a γ.b
        · exact (γ.toPiecewiseC1Curve.deriv_continuous_off_partition
              t ht_Ioo ht_notP).continuousWithinAt
        · have ht_ab := h_sub ht_Icc
          simp only [Set.mem_Ioo, not_and, not_lt] at ht_Ioo
          have : t = γ.a ∨ t = γ.b := by
            rcases ht_ab.1.lt_or_eq with h | h
            · exact Or.inr (le_antisymm ht_ab.2 (ht_Ioo h))
            · exact Or.inl h.symm
          rcases this with rfl | rfl
          · exact absurd γ.toPiecewiseC1Curve.endpoints_in_partition.1 ht_notP
          · exact absurd γ.toPiecewiseC1Curve.endpoints_in_partition.2 ht_notP
      have h_P_null : volume (↑γ.partition ∩ S) = 0 :=
        (γ.partition.finite_toSet.inter_of_left S).measure_zero volume
      have h_eq_S : S = (S \ γ.partition) ∪ (↑γ.partition ∩ S) := by
        ext x; simp only [S, Set.mem_union, Set.mem_diff, Set.mem_inter_iff]; tauto
      rw [show volume.restrict S =
          volume.restrict ((S \ γ.partition) ∪ (↑γ.partition ∩ S)) from by rw [← h_eq_S],
        aestronglyMeasurable_union_iff]
      exact ⟨h_cont_on_S.aestronglyMeasurable
        (hS_meas.diff γ.partition.finite_toSet.measurableSet),
        (Measure.restrict_zero_set h_P_null).symm ▸ aestronglyMeasurable_zero_measure _⟩
    refine (h_pw.mono_measure Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem isClosed_Icc.measurableSet] with t ht
    symm; simp only [hg_def, piecewise]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ⟨h1, ht⟩ h2
    · exact absurd h2.1 h1
    · rfl
  exact (uIcc_of_le hcd ▸
    IntegrableOn.of_bound (Real.volume_Icc ▸ ENNReal.ofReal_lt_top) h_meas (ε⁻¹ * D)
      (by filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
          exact h_bound t ht)).intervalIntegrable

/-- Helper: CPV of `(z - z₀)⁻¹` exists on any sub-interval `[c, d] ⊆ [a, b]`
where there are no crossings. This follows directly from `cpv_avoidance`. -/
private theorem cpv_avoidance_sub (γ : PiecewiseC1Immersion) (z₀ : ℂ) (c d : ℝ)
    (hcd : c ≤ d) (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_avoid : ∀ t ∈ Icc c d, γ.toFun t ≠ z₀) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun c d z₀ :=
  cpv_avoidance _ γ.toFun c d z₀ (γ.continuous_toFun.mono h_sub) hcd h_avoid

end
