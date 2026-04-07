/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Winding Number Decomposition (Hungerbuhler-Wasem Propositions 2.2 and 2.3)

This file provides the crossing set definition and finiteness theorem (Prop 2.2),
plus the angle-based decomposition of the generalized winding number (Prop 2.3).

## Main definitions

* `crossingSet γ z₀` -- the set `{t ∈ [0,1] | γ(t) = z₀}`, parameter values where
  the piecewise C1 immersion `γ` passes through `z₀`.

* `angleAtCrossing γ t₀ ht₀` -- the signed angle at a crossing point, defined via
  `Complex.arg` of one-sided derivative limits at partition points and `π` at smooth points.

* `externalWindingContribution' γ z₀ α` -- the external winding contribution,
  defined as `generalizedWindingNumber + α/(2π)`.

## Main results

* `crossingSet_isClosed` -- the crossing set is closed.

* `crossing_isolated_interior` -- each interior crossing is isolated.

* `crossingSet_finite` -- the crossing set is finite (Prop 2.2), when the curve
  avoids `z₀` at the endpoints.

* `windingNumber_eq_external_sub_angle` -- the decomposition identity:
  `generalizedWindingNumber γ z₀ = N - α/(2π)`.

* `windingNumberWithAngles_smooth_crossing` -- a single smooth crossing contributes `1/2`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-! ### Helper lemmas -/

/-- If `f` has derivative `f'` at `t`, then `Re ∘ f` has derivative `Re(f')` at `t`. -/
private lemma HasDerivAt.re' {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (h : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).re) f'.re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h

/-- The partition minus a point is finite hence closed; its complement is in `𝓝[<] p`. -/
private lemma eventually_not_in_partition_left
    (γ : PiecewiseC1Immersion x y) (p : ℝ) :
    ∀ᶠ t in 𝓝[<] p, t ∉ γ.partition := by
  have hcl : IsClosed ((↑γ.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Path.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.partition \ {p} : Set ℝ) := by
    simp only [mem_diff, Finset.mem_coe, mem_singleton_iff, not_and, not_not, implies_true]
  have h1 : ∀ᶠ t in 𝓝[<] p, t ∈ (↑γ.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[<] p, t < p := eventually_nhdsWithin_of_forall fun t ht => ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_lt⟩ ht_part =>
    ht_compl ⟨ht_part, ne_of_lt ht_lt⟩

/-- The partition minus a point is finite hence closed; its complement is in `𝓝[>] p`. -/
private lemma eventually_not_in_partition_right
    (γ : PiecewiseC1Immersion x y) (p : ℝ) :
    ∀ᶠ t in 𝓝[>] p, t ∉ γ.partition := by
  have hcl : IsClosed ((↑γ.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Path.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.partition \ {p} : Set ℝ) := by
    simp only [mem_diff, Finset.mem_coe, mem_singleton_iff, not_and, not_not, implies_true]
  have h1 : ∀ᶠ t in 𝓝[>] p, t ∈ (↑γ.partition \ {p} : Set ℝ)ᶜ :=
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem)
  have h2 : ∀ᶠ t in 𝓝[>] p, p < t := eventually_nhdsWithin_of_forall fun t ht => ht
  exact (h1.and h2).mono fun t ⟨ht_compl, ht_gt⟩ ht_part =>
    ht_compl ⟨ht_part, ne_of_gt ht_gt⟩

/-! ### Crossing set definition and closedness -/

/-- The crossing set: parameter values in `[0, 1]` where `γ` passes through `z₀`. -/
def crossingSet (γ : PiecewiseC1Immersion x y) (z₀ : ℂ) : Set ℝ :=
  {t ∈ Icc 0 1 | (γ : ℝ → ℂ) t = z₀}

/-- The crossing set is closed (intersection of a closed interval and a closed preimage). -/
theorem crossingSet_isClosed (γ : PiecewiseC1Immersion x y) (z₀ : ℂ) :
    IsClosed (crossingSet γ z₀) := by
  have : crossingSet γ z₀ = Icc 0 1 ∩ (γ : ℝ → ℂ) ⁻¹' {z₀} := by
    ext t; simp only [crossingSet, mem_sep_iff, mem_inter_iff, mem_preimage, mem_singleton_iff]
  rw [this]
  exact isClosed_Icc.inter (isClosed_singleton.preimage γ.continuous)

/-- The crossing set is a subset of `[0, 1]`. -/
theorem crossingSet_subset_Icc (γ : PiecewiseC1Immersion x y) (z₀ : ℂ) :
    crossingSet γ z₀ ⊆ Icc 0 1 :=
  fun _ ht => ht.1

/-! ### Isolation of crossings -/

/-- At a smooth crossing point (not in partition) in `(0, 1)`, `γ` is eventually different
from `z₀` in a punctured neighborhood. Uses `HasDerivAt.eventually_ne`. -/
theorem crossing_isolated_at_smooth
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (hcross : (γ : ℝ → ℂ) t₀ = z₀)
    (hsmooth : t₀ ∉ γ.partition) :
    ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → ℂ) t ≠ z₀ :=
  hcross ▸
    (γ.toPiecewiseC1Path.differentiable_off t₀ ht₀ hsmooth).hasDerivAt.eventually_ne
      (γ.deriv_ne_zero t₀ ht₀ hsmooth)

/-- At a partition point with `0 < p`, the left-sided derivative limit is nonzero, so
`Re(conj(L) · (γ(t) - z₀))` is strictly monotone, giving isolation on the left. -/
private theorem crossing_isolated_left_of_partition
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ)
    (p : ℝ) (hp : p ∈ γ.partition) (h0p : 0 < p)
    (hcross : (γ : ℝ → ℂ) p = z₀) :
    ∀ᶠ t in 𝓝[<] p, (γ : ℝ → ℂ) t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.left_deriv_limit p hp
  set h : ℝ → ℝ := fun t => ((starRingEnd ℂ L) * ((γ : ℝ → ℂ) t - z₀)).re with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, mul_zero, zero_re]
  have hL_sq_pos : (0 : ℝ) < ‖L‖ ^ 2 := by positivity
  have h_lim_val : (starRingEnd ℂ L * L).re = ‖L‖ ^ 2 := by
    have : starRingEnd ℂ L * L = (↑(‖L‖) : ℂ) ^ 2 := conj_mul' L
    rw [this, sq, ← ofReal_mul, ofReal_re, sq]
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[<] p,
      (starRingEnd ℂ L * deriv (γ : ℝ → ℂ) t).re > 0 := by
    have : Tendsto (fun t => (starRingEnd ℂ L * deriv (γ : ℝ → ℂ) t).re)
        (𝓝[<] p) (𝓝 (‖L‖ ^ 2)) := by
      rw [← h_lim_val]
      exact (continuous_re.tendsto _).comp (hL_tendsto.const_mul (starRingEnd ℂ L))
    exact this.eventually (Ioi_mem_nhds hL_sq_pos)
  have h_ev_Ioo : ∀ᶠ t in 𝓝[<] p, t ∈ Ioo 0 1 := by
    have h1 : ∀ᶠ t in 𝓝[<] p, 0 < t :=
      eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds h0p)
    have h2 : ∀ᶠ t in 𝓝[<] p, t < p := eventually_nhdsWithin_of_forall fun t ht => ht
    have hp1 : p < 1 := (γ.toPiecewiseC1Path.partition_subset hp).2
    exact (h1.and h2).mono fun t ⟨hat, htp⟩ => ⟨hat, lt_trans htp hp1⟩
  have h_all := (eventually_not_in_partition_left γ p).and (h_ev_deriv_pos.and h_ev_Ioo)
  rw [eventually_nhdsWithin_iff] at h_all
  obtain ⟨l, u, ⟨hl_lt, hlt_u⟩, h_Ioo⟩ := h_all.exists_Ioo_subset
  set q := max l 0
  have hq_lt_p : q < p := max_lt hl_lt h0p
  have hqp_sub_01 : Icc q p ⊆ Icc 0 1 := by
    intro t ht
    exact ⟨le_trans (le_max_right l 0) ht.1,
           le_of_lt (lt_of_le_of_lt ht.2 (γ.toPiecewiseC1Path.partition_subset hp).2)⟩
  have hh_cont_qp : ContinuousOn h (Icc q p) :=
    continuous_re.comp_continuousOn
      (continuousOn_const.mul
        (γ.continuous.continuousOn.mono hqp_sub_01 |>.sub continuousOn_const))
  have hh_deriv_pos : ∀ s ∈ interior (Icc q p), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    have hs_in_lu : s ∈ Ioo l u :=
      ⟨lt_of_le_of_lt (le_max_left l 0) hs.1, lt_trans hs.2 hlt_u⟩
    obtain ⟨hs_smooth, hs_deriv, hs_Ioo⟩ := h_Ioo hs_in_lu hs.2
    have hd := γ.toPiecewiseC1Path.differentiable_off s hs_Ioo hs_smooth
    have h1 : HasDerivAt (fun t => (γ : ℝ → ℂ) t - z₀)
        (deriv (γ : ℝ → ℂ) s - 0) s :=
      hd.hasDerivAt.sub (hasDerivAt_const s z₀)
    simp only [sub_zero] at h1
    rw [((h1.const_mul _).re').deriv]; exact hs_deriv
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc q p) hh_cont_qp hh_deriv_pos
  filter_upwards [Ioo_mem_nhdsLT hq_lt_p] with t ht hγt
  have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, mul_zero, zero_re]
  linarith [hh_mono (Ioo_subset_Icc_self ht) (right_mem_Icc.mpr hq_lt_p.le) ht.2]

/-- At a partition point with `p < 1`, the right-sided derivative limit is nonzero, so
`Re(conj(L) · (γ(t) - z₀))` is strictly monotone, giving isolation on the right. -/
private theorem crossing_isolated_right_of_partition
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ)
    (p : ℝ) (hp : p ∈ γ.partition) (hp1 : p < 1)
    (hcross : (γ : ℝ → ℂ) p = z₀) :
    ∀ᶠ t in 𝓝[>] p, (γ : ℝ → ℂ) t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.right_deriv_limit p hp
  set h : ℝ → ℝ := fun t => ((starRingEnd ℂ L) * ((γ : ℝ → ℂ) t - z₀)).re with hh_def
  have hh_p : h p = 0 := by simp only [hh_def, hcross, sub_self, mul_zero, zero_re]
  have hL_sq_pos : (0 : ℝ) < ‖L‖ ^ 2 := by positivity
  have h_lim_val : (starRingEnd ℂ L * L).re = ‖L‖ ^ 2 := by
    have : starRingEnd ℂ L * L = (↑(‖L‖) : ℂ) ^ 2 := conj_mul' L
    rw [this, sq, ← ofReal_mul, ofReal_re, sq]
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[>] p,
      (starRingEnd ℂ L * deriv (γ : ℝ → ℂ) t).re > 0 := by
    have : Tendsto (fun t => (starRingEnd ℂ L * deriv (γ : ℝ → ℂ) t).re)
        (𝓝[>] p) (𝓝 (‖L‖ ^ 2)) := by
      rw [← h_lim_val]
      exact (continuous_re.tendsto _).comp (hL_tendsto.const_mul (starRingEnd ℂ L))
    exact this.eventually (Ioi_mem_nhds hL_sq_pos)
  have hp0 : 0 < p := (γ.toPiecewiseC1Path.partition_subset hp).1
  have h_ev_Ioo : ∀ᶠ t in 𝓝[>] p, t ∈ Ioo 0 1 := by
    have h1 : ∀ᶠ t in 𝓝[>] p, t < 1 :=
      eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hp1)
    have h2 : ∀ᶠ t in 𝓝[>] p, p < t := eventually_nhdsWithin_of_forall fun t ht => ht
    exact (h1.and h2).mono fun t ⟨htb, htp⟩ => ⟨lt_trans hp0 htp, htb⟩
  have h_all := (eventually_not_in_partition_right γ p).and (h_ev_deriv_pos.and h_ev_Ioo)
  rw [eventually_nhdsWithin_iff] at h_all
  obtain ⟨l, u, ⟨hl_lt, hlt_u⟩, h_Ioo⟩ := h_all.exists_Ioo_subset
  set r := min u 1
  have hp_lt_r : p < r := lt_min hlt_u hp1
  have hpr_sub_01 : Icc p r ⊆ Icc 0 1 := by
    intro t ht
    exact ⟨le_trans (le_of_lt hp0) ht.1, le_trans ht.2 (min_le_right u 1)⟩
  have hh_cont_pr : ContinuousOn h (Icc p r) :=
    continuous_re.comp_continuousOn
      (continuousOn_const.mul
        (γ.continuous.continuousOn.mono hpr_sub_01 |>.sub continuousOn_const))
  have hh_deriv_pos : ∀ s ∈ interior (Icc p r), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    have hs_in_lu : s ∈ Ioo l u :=
      ⟨lt_trans hl_lt hs.1, lt_of_lt_of_le hs.2 (min_le_left u 1)⟩
    obtain ⟨hs_smooth, hs_deriv, hs_Ioo⟩ := h_Ioo hs_in_lu hs.1
    have hd := γ.toPiecewiseC1Path.differentiable_off s hs_Ioo hs_smooth
    have h1 : HasDerivAt (fun t => (γ : ℝ → ℂ) t - z₀)
        (deriv (γ : ℝ → ℂ) s - 0) s :=
      hd.hasDerivAt.sub (hasDerivAt_const s z₀)
    simp only [sub_zero] at h1
    rw [((h1.const_mul _).re').deriv]; exact hs_deriv
  have hh_mono := strictMonoOn_of_deriv_pos (convex_Icc p r) hh_cont_pr hh_deriv_pos
  filter_upwards [Ioo_mem_nhdsGT hp_lt_r] with t ht hγt
  have hht : h t = 0 := by simp only [hh_def, hγt, sub_self, mul_zero, zero_re]
  linarith [hh_mono (left_mem_Icc.mpr hp_lt_r.le) (Ioo_subset_Icc_self ht) ht.1]

/-- At any interior crossing `t₀ ∈ (0, 1)`, there is a punctured neighborhood with no
crossings. Combines smooth-point and partition-point isolation. -/
theorem crossing_isolated_interior
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1)
    (hcross : (γ : ℝ → ℂ) t₀ = z₀) :
    ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → ℂ) t ≠ z₀ := by
  by_cases hpart : t₀ ∈ γ.partition
  · rw [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, eventually_sup]
    exact ⟨crossing_isolated_left_of_partition γ z₀ t₀ hpart ht₀.1 hcross,
           crossing_isolated_right_of_partition γ z₀ t₀ hpart ht₀.2 hcross⟩
  · exact hcross ▸
      (γ.toPiecewiseC1Path.differentiable_off t₀ ht₀ hpart).hasDerivAt.eventually_ne
        (γ.deriv_ne_zero t₀ ht₀ hpart)

/-- No interior point of the crossing set is an accumulation point of the crossing set. -/
theorem crossing_not_accPt_interior
    (γ : PiecewiseC1Immersion x y) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (hcross : (γ : ℝ → ℂ) t₀ = z₀) :
    ¬AccPt t₀ (𝓟 (crossingSet γ z₀)) := by
  rw [accPt_iff_frequently_nhdsNE, not_frequently]
  exact (crossing_isolated_interior γ z₀ t₀ ht₀ hcross).mono fun t ht ht_mem => by
    simp only [crossingSet, mem_setOf_eq] at ht_mem
    exact ht ht_mem.2

/-! ### Finiteness of crossings (Proposition 2.2) -/

/-- **Proposition 2.2**: The crossing set `{t ∈ [0,1] | γ(t) = z₀}` is finite
when `γ` avoids `z₀` at the endpoints.

The proof uses compactness of `[0,1]` and the isolation of interior crossings:
if the crossing set were infinite, Bolzano-Weierstrass gives an accumulation point
in `[0,1]`, which must lie in the (closed) crossing set. Since the endpoints are
excluded by hypothesis, the accumulation point is interior, contradicting isolation. -/
theorem crossingSet_finite (γ : PiecewiseC1Immersion x y) (z₀ : ℂ)
    (h0 : (γ : ℝ → ℂ) 0 ≠ z₀) (h1 : (γ : ℝ → ℂ) 1 ≠ z₀) :
    (crossingSet γ z₀).Finite := by
  by_contra hS_not_fin
  have hS_inf : (crossingSet γ z₀).Infinite := hS_not_fin
  obtain ⟨t, _, ht_acc⟩ := hS_inf.exists_accPt_of_subset_isCompact
    isCompact_Icc (crossingSet_subset_Icc γ z₀)
  have ht_closure : t ∈ closure (crossingSet γ z₀) :=
    mem_closure_iff_clusterPt.mpr ht_acc.clusterPt
  have ht_S : t ∈ crossingSet γ z₀ := by
    rwa [(crossingSet_isClosed γ z₀).closure_eq] at ht_closure
  -- The accumulation point is in (0,1) since endpoints are excluded
  have ht_int : t ∈ Ioo 0 1 := by
    constructor
    · rcases eq_or_lt_of_le ht_S.1.1 with h | h
      · exact absurd (h ▸ ht_S.2) h0
      · exact h
    · rcases eq_or_lt_of_le ht_S.1.2 with h | h
      · exact absurd (h ▸ ht_S.2) h1
      · exact h
  exact crossing_not_accPt_interior γ z₀ t ht_int ht_S.2 ht_acc

/-- The crossing set is bounded above by the interior crossings plus endpoint contributions.
This allows computing the crossing set by handling the (finite) interior part
and the at-most-two endpoint values separately. -/
theorem crossingSet_subset_union_endpoints (γ : PiecewiseC1Immersion x y) (z₀ : ℂ) :
    crossingSet γ z₀ ⊆ (crossingSet γ z₀ ∩ Ioo 0 1) ∪ {(0 : ℝ), 1} := by
  intro t ht
  by_cases ht_int : t ∈ Ioo 0 1
  · exact Or.inl ⟨ht, ht_int⟩
  · simp only [mem_Ioo, not_and_or, not_lt] at ht_int
    rcases ht_int with h | h
    · exact Or.inr (Or.inl (le_antisymm h ht.1.1))
    · exact Or.inr (Or.inr (le_antisymm ht.1.2 h))

/-! ### Angle at crossing -/

/-- The angle at a crossing point where `γ` passes through `z₀`.

At smooth points (not in partition), the one-sided derivatives agree and the
angle is `π` (a straight crossing).

At partition points (corners), the angle is `arg(L_right) - arg(-L_left)` where
`L_left` and `L_right` are the one-sided derivative limits. -/
def angleAtCrossing (γ : PiecewiseC1Immersion x y) (t₀ : ℝ)
    (_ : t₀ ∈ Ioo 0 1) : ℝ :=
  if h : t₀ ∈ γ.partition then
    let L_left := Classical.choose (γ.left_deriv_limit t₀ h)
    let L_right := Classical.choose (γ.right_deriv_limit t₀ h)
    arg L_right - arg (-L_left)
  else Real.pi

/-- At smooth points, the crossing angle is `π`. -/
theorem angleAtCrossing_smooth (γ : PiecewiseC1Immersion x y)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1)
    (hsmooth : t₀ ∉ γ.partition) :
    angleAtCrossing γ t₀ ht₀ = Real.pi := by
  simp only [angleAtCrossing, hsmooth, ↓reduceDIte]

/-! ### External winding contribution -/

/-- The external winding contribution at a crossing point.

The decomposition is `generalizedWindingNumber γ z₀ = N - α/(2π)` where `α` is the
crossing angle and `N` is the external winding. So `N = gWN + α/(2π)`. -/
def externalWindingContribution' (γ : PiecewiseC1Path x y)
    (z₀ : ℂ) (α : ℝ) : ℂ :=
  generalizedWindingNumber γ z₀ + (α : ℂ) / (2 * Real.pi)

/-! ### Decomposition identity (Proposition 2.3) -/

/-- **Proposition 2.3**: The generalized winding number decomposes as
`n_{z₀}(γ) = N - α/(2π)` where `N` is the external winding contribution
and `α` is the crossing angle. This is an immediate algebraic identity. -/
theorem windingNumber_eq_external_sub_angle
    (γ : PiecewiseC1Path x y) (z₀ : ℂ) (α : ℝ) :
    generalizedWindingNumber γ z₀ =
      externalWindingContribution' γ z₀ α -
        (α : ℂ) / (2 * Real.pi) := by
  simp only [externalWindingContribution', add_sub_cancel_right]

/-- When the external winding vanishes, the winding number equals `-α/(2π)`. -/
theorem windingNumber_eq_neg_angle_of_external_zero
    (γ : PiecewiseC1Path x y) (z₀ : ℂ) (α : ℝ)
    (h_external : externalWindingContribution' γ z₀ α = 0) :
    generalizedWindingNumber γ z₀ = -((α : ℂ) / (2 * Real.pi)) := by
  rw [windingNumber_eq_external_sub_angle γ z₀ α, h_external, zero_sub]

/-! ### Angle-sum winding number -/

/-- Winding number via explicit angle sum at crossings. -/
def windingNumberWithAngles
    (γ : PiecewiseC1Immersion x y)
    (crossings : Finset ℝ)
    (hcrossings_in : ∀ t ∈ crossings, t ∈ Ioo 0 1) : ℂ :=
  ∑ t : crossings,
    (angleAtCrossing γ t (hcrossings_in t t.prop) : ℂ) / (2 * Real.pi)

/-- A single smooth crossing contributes `1/2` to the angle-sum winding number. -/
theorem windingNumberWithAngles_smooth_crossing
    (γ : PiecewiseC1Immersion x y)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo 0 1) (hsmooth : t₀ ∉ γ.partition) :
    windingNumberWithAngles γ {t₀}
      (fun t ht => by simp only [Finset.mem_singleton] at ht; rw [ht]; exact ht₀) =
    1 / 2 := by
  simp only [windingNumberWithAngles]
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [angleAtCrossing_smooth γ t₀ ht₀ hsmooth]
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hpi]

/-- A corner crossing with angle `α` contributes `α/(2π)` to the angle-sum. -/
theorem windingNumberWithAngles_corner_crossing
    (γ : PiecewiseC1Immersion x y)
    (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo 0 1)
    (hangle : angleAtCrossing γ t₀ ht₀ = α) :
    windingNumberWithAngles γ {t₀}
      (fun t ht => by simp only [Finset.mem_singleton] at ht; rw [ht]; exact ht₀) =
    (α : ℂ) / (2 * Real.pi) := by
  simp only [windingNumberWithAngles]
  rw [Fintype.sum_unique]
  simp only [Finset.default_singleton]
  rw [hangle]

end
