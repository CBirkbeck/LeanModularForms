/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanModularForms.ForMathlib.CurveUtilities
public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Topology.Compactness.Compact

/-!
# Crossing Analysis — Proposition 2.2

For a `PwC1Immersion` γ : [0,1] → E, the set of parameter values where γ
passes through a given point z₀ is finite. This is Proposition 2.2 from
Hungerbühler–Wasem.

## Main definitions

* `PwC1Immersion.crossingSet` — the set `{t ∈ Icc 0 1 | γ t = z₀}`

## Main results

* `PwC1Immersion.crossingSet_isClosed` — the crossing set is closed
* `PwC1Immersion.crossing_isolated_smooth` — crossings at smooth points are isolated
* `PwC1Immersion.crossing_isolated_left` — crossings at partition points are
  isolated from the left
* `PwC1Immersion.crossing_isolated_right` — crossings at partition points are
  isolated from the right
* `PwC1Immersion.crossing_isolated` — every crossing in `(0,1)` is isolated
* `PwC1Immersion.crossingSet_finite` — **Proposition 2.2**: the crossing set is finite

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology

@[expose] public section

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : E}

namespace PwC1Immersion

/-- The crossing set: parameter values in `[0, 1]` where the path passes through `z₀`. -/
def crossingSet (γ : PwC1Immersion x y) (z₀ : E) : Set ℝ :=
  {t ∈ Icc (0 : ℝ) 1 | (γ : ℝ → E) t = z₀}

theorem crossingSet_subset_Icc (γ : PwC1Immersion x y) (z₀ : E) :
    γ.crossingSet z₀ ⊆ Icc (0 : ℝ) 1 :=
  fun _ ht => ht.1

/-- The crossing set is closed. -/
theorem crossingSet_isClosed (γ : PwC1Immersion x y) (z₀ : E) :
    _root_.IsClosed (γ.crossingSet z₀) := by
  have : γ.crossingSet z₀ = Icc (0 : ℝ) 1 ∩ (γ : ℝ → E) ⁻¹' {z₀} := by
    ext t
    simp only [crossingSet, mem_sep_iff, mem_inter_iff, mem_preimage, mem_singleton_iff]
  rw [this]
  exact isClosed_Icc.inter (isClosed_singleton.preimage γ.toPiecewiseC1Path.continuous)

/-- Near `p` within any `u ∌ p`, points are eventually not in the partition. -/
private theorem eventually_not_in_partition
    (γ : PwC1Immersion x y) {p : ℝ} {u : Set ℝ} (hu : p ∉ u) :
    ∀ᶠ t in 𝓝[u] p, t ∉ γ.toPiecewiseC1Path.partition := by
  have hcl : _root_.IsClosed ((↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ)) :=
    (γ.toPiecewiseC1Path.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : p ∉ (↑γ.toPiecewiseC1Path.partition \ {p} : Set ℝ) := by simp
  filter_upwards [
    eventually_nhdsWithin_of_eventually_nhds (hcl.isOpen_compl.mem_nhds hmem),
    self_mem_nhdsWithin] with t ht_compl ht_mem ht_part
  exact ht_compl ⟨ht_part, fun h => hu (h ▸ ht_mem)⟩

/-- `Ioo q p ⊆ Ioo 0 1` implies `Icc q p ⊆ Icc 0 1` by taking closures. -/
private theorem Icc_subset_of_Ioo_subset {q p : ℝ} (hqp : q < p)
    (h : Ioo q p ⊆ Ioo (0 : ℝ) 1) : Icc q p ⊆ Icc (0 : ℝ) 1 := by
  have := closure_mono h
  rwa [closure_Ioo (ne_of_lt hqp), closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at this

/-- At a smooth point where `γ(t₀) = z₀`, there is a punctured neighborhood in which
`γ(t) ≠ z₀`. -/
theorem crossing_isolated_smooth (γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcross : (γ : ℝ → E) t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) :
    ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → E) t ≠ z₀ := by
  rw [← hcross]
  exact (γ.toPiecewiseC1Path.differentiable_off_extend t₀ ht₀ hsmooth).hasDerivAt.eventually_ne
    (γ.deriv_ne_zero t₀ ht₀ hsmooth)

/-- **At-most-one-crossing core.** If a dual functional `f` of a one-sided
tangent has positive derivative along `γ - z₀` on `(a, b) ⊆ (0, 1)` off the
partition, then `f ∘ (γ - z₀)` is strictly monotone on `[a, b]`, so `γ` meets
`z₀` at most once there. Shared by both one-sided isolation lemmas. -/
private theorem crossing_atMostOne_of_dual_deriv_pos
    (γ : PwC1Immersion x y) {z₀ : E} {f : StrongDual ℝ E} {a b : ℝ}
    (h_sub : Icc a b ⊆ Icc (0 : ℝ) 1)
    (h_cond : ∀ t ∈ Ioo a b, t ∉ γ.toPiecewiseC1Path.partition ∧
      t ∈ Ioo (0 : ℝ) 1 ∧ f (deriv (γ : ℝ → E) t) > 0) :
    ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b,
      (γ : ℝ → E) t₁ = z₀ → (γ : ℝ → E) t₂ = z₀ → t₁ = t₂ := by
  set h : ℝ → ℝ := fun t => f ((γ : ℝ → E) t - z₀) with hh_def
  have hh_cont : ContinuousOn h (Icc a b) :=
    f.continuous.comp_continuousOn
      ((γ.toPiecewiseC1Path.continuous.continuousOn.mono h_sub).sub continuousOn_const)
  have hh_deriv_pos : ∀ s ∈ interior (Icc a b), 0 < deriv h s := by
    rw [interior_Icc]
    intro s hs
    obtain ⟨hs_smooth, hs_Ioo, hs_dpos⟩ := h_cond s hs
    have h_sub' : HasDerivAt (fun t => (γ : ℝ → E) t - z₀) (deriv (γ : ℝ → E) s - 0) s :=
      (γ.toPiecewiseC1Path.differentiable_off_extend s hs_Ioo hs_smooth).hasDerivAt.sub
        (hasDerivAt_const s z₀)
    simp only [sub_zero] at h_sub'
    exact (f.hasFDerivAt.comp_hasDerivAt s h_sub').deriv ▸ hs_dpos
  intro t₁ ht₁ t₂ ht₂ hc₁ hc₂
  refine (strictMonoOn_of_deriv_pos (convex_Icc a b) hh_cont hh_deriv_pos).injOn ht₁ ht₂ ?_
  simp only [hh_def, hc₁, hc₂]

/-- At a partition point `p` with `0 < p`, `γ(t) ≠ γ(p)` for `t` sufficiently close
to `p` from the left. -/
theorem crossing_isolated_left (γ : PwC1Immersion x y) (z₀ : E) (p : ℝ)
    (hp_part : p ∈ γ.toPiecewiseC1Path.partition) (hp_pos : 0 < p)
    (hcross : (γ : ℝ → E) p = z₀) :
    ∀ᶠ t in 𝓝[<] p, (γ : ℝ → E) t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.left_deriv_limit p hp_part
  obtain ⟨f, _, hf_L⟩ := exists_dual_vector ℝ L (norm_ne_zero_iff.mpr hL_ne)
  have hfL_pos : (0 : ℝ) < f L := by
    rw [hf_L]
    exact_mod_cast norm_pos_iff.mpr hL_ne
  have hp_Ioo := γ.toPiecewiseC1Path.partition_subset hp_part
  have h_ev_Ioo : ∀ᶠ t in 𝓝[<] p, t ∈ Ioo (0 : ℝ) 1 :=
    (eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds hp_pos) |>.and
      (eventually_nhdsWithin_of_forall fun _ ht => ht)).mono
      fun _ ⟨h0t, htp⟩ => ⟨h0t, lt_trans htp hp_Ioo.2⟩
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[<] p, f (deriv (γ : ℝ → E) t) > 0 :=
    (f.continuous.continuousAt.tendsto.comp hL_tendsto).eventually (Ioi_mem_nhds hfL_pos)
  have h_all := (eventually_not_in_partition γ self_notMem_Iio).and
    (h_ev_Ioo.and h_ev_deriv_pos)
  rw [Filter.Eventually, mem_nhdsLT_iff_exists_Ioo_subset' hp_pos] at h_all
  obtain ⟨q, hq_lt_p, hq_cond⟩ := h_all
  have h_once := crossing_atMostOne_of_dual_deriv_pos γ (z₀ := z₀)
    (Icc_subset_of_Ioo_subset hq_lt_p fun t ht => (hq_cond ht).2.1) fun t ht => hq_cond ht
  rw [Filter.Eventually, mem_nhdsLT_iff_exists_Ioo_subset' hp_pos]
  exact ⟨q, hq_lt_p, fun t ht hγt => (ne_of_lt ht.2) (h_once t (Ioo_subset_Icc_self ht) p
    (right_mem_Icc.mpr hq_lt_p.le) hγt hcross)⟩

/-- At a partition point `p` with `p < 1`, `γ(t) ≠ γ(p)` for `t` sufficiently close
to `p` from the right. -/
theorem crossing_isolated_right (γ : PwC1Immersion x y) (z₀ : E) (p : ℝ)
    (hp_part : p ∈ γ.toPiecewiseC1Path.partition) (hp_lt_one : p < 1)
    (hcross : (γ : ℝ → E) p = z₀) :
    ∀ᶠ t in 𝓝[>] p, (γ : ℝ → E) t ≠ z₀ := by
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.right_deriv_limit p hp_part
  obtain ⟨f, _, hf_L⟩ := exists_dual_vector ℝ L (norm_ne_zero_iff.mpr hL_ne)
  have hfL_pos : (0 : ℝ) < f L := by
    rw [hf_L]
    exact_mod_cast norm_pos_iff.mpr hL_ne
  have hp_Ioo := γ.toPiecewiseC1Path.partition_subset hp_part
  have h_ev_Ioo : ∀ᶠ t in 𝓝[>] p, t ∈ Ioo (0 : ℝ) 1 :=
    (eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hp_lt_one) |>.and
      (eventually_nhdsWithin_of_forall fun _ ht => ht)).mono
      fun _ ⟨ht1, htp⟩ => ⟨lt_trans hp_Ioo.1 htp, ht1⟩
  have h_ev_deriv_pos : ∀ᶠ t in 𝓝[>] p, f (deriv (γ : ℝ → E) t) > 0 :=
    (f.continuous.continuousAt.tendsto.comp hL_tendsto).eventually (Ioi_mem_nhds hfL_pos)
  have h_all := (eventually_not_in_partition γ self_notMem_Ioi).and
    (h_ev_Ioo.and h_ev_deriv_pos)
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset' hp_lt_one] at h_all
  obtain ⟨r, hr_gt_p, hr_cond⟩ := h_all
  have h_once := crossing_atMostOne_of_dual_deriv_pos γ (z₀ := z₀)
    (Icc_subset_of_Ioo_subset hr_gt_p fun t ht => (hr_cond ht).2.1) fun t ht => hr_cond ht
  rw [Filter.Eventually, mem_nhdsGT_iff_exists_Ioo_subset' hp_lt_one]
  exact ⟨r, hr_gt_p, fun t ht hγt => (ne_of_gt ht.1) (h_once t (Ioo_subset_Icc_self ht) p
    (left_mem_Icc.mpr hr_gt_p.le) hγt hcross)⟩

/-- At any crossing `t₀ ∈ (0, 1)`, there is a punctured neighborhood with no other
crossings in `[0, 1]`. Combines the smooth-point and partition-point cases. -/
theorem crossing_isolated (γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcross : (γ : ℝ → E) t₀ = z₀) :
    ∀ᶠ t in 𝓝[≠] t₀, (γ : ℝ → E) t ≠ z₀ ∨ t ∉ Icc (0 : ℝ) 1 := by
  by_cases hpart : t₀ ∈ γ.toPiecewiseC1Path.partition
  · rw [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, Filter.eventually_sup]
    exact ⟨(crossing_isolated_left γ z₀ t₀ hpart ht₀.1 hcross).mono fun t ht => Or.inl ht,
           (crossing_isolated_right γ z₀ t₀ hpart ht₀.2 hcross).mono fun t ht => Or.inl ht⟩
  · exact (crossing_isolated_smooth γ z₀ t₀ ht₀ hcross hpart).mono fun t ht => Or.inl ht

/-- No point of the crossing set in `(0, 1)` is an accumulation point. -/
theorem crossing_not_accPt (γ : PwC1Immersion x y) (z₀ : E) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hcross : (γ : ℝ → E) t₀ = z₀) :
    ¬AccPt t₀ (𝓟 (γ.crossingSet z₀)) := by
  rw [accPt_iff_frequently_nhdsNE, Filter.not_frequently]
  exact (crossing_isolated γ z₀ t₀ ht₀ hcross).mono fun t ht ht_mem => by
    simp only [crossingSet, mem_sep_iff] at ht_mem
    exact ht.elim (fun h => h ht_mem.2) (fun h => h ht_mem.1)

/-- **Proposition 2.2** (Hungerbühler–Wasem): The crossing set of a piecewise C¹
immersion is finite, provided the endpoints avoid `z₀`. -/
theorem crossingSet_finite (γ : PwC1Immersion x y) (z₀ : E)
    (h0 : (γ : ℝ → E) 0 ≠ z₀) (h1 : (γ : ℝ → E) 1 ≠ z₀) :
    Set.Finite (γ.crossingSet z₀) := by
  by_contra hS_inf
  obtain ⟨a, _, ha_acc⟩ := (Set.not_finite.mp hS_inf).exists_accPt_of_subset_isCompact
    isCompact_Icc (crossingSet_subset_Icc γ z₀)
  have ha_S : a ∈ γ.crossingSet z₀ :=
    (γ.crossingSet_isClosed z₀).closure_eq ▸ mem_closure_iff_clusterPt.mpr ha_acc.clusterPt
  have ha_Ioo : a ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne ha_S.1.1 (Ne.symm (fun h => h0 (h ▸ ha_S.2))),
     lt_of_le_of_ne ha_S.1.2 (fun h => h1 (h ▸ ha_S.2))⟩
  exact γ.crossing_not_accPt z₀ a ha_Ioo ha_S.2 ha_acc

end PwC1Immersion

end

end
