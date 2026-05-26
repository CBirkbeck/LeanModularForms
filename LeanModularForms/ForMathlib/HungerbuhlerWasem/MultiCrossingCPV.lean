/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HungerbuhlerWasem.Crossing

/-!
# Multi-crossing CPV existence — general cardinality (T-BR-Y9d, T-BR-Y9e)

This file delivers two headline multi-crossing CPV theorems for **arbitrary**
cardinality `D.crossings.card ≥ 0`:

* `hasCauchyPV_inv_sub_multiCrossing` (T-BR-Y9d): simple-pole CPV existence.
* `hasCauchyPVOn_multiCrossing_higherOrder` (T-BR-Y9e): higher-order CPV
  vanishing under condition (B).

## Strategy

Given `D : MultiPoleCrossData γ s` with `crossings.card = n`:

1. **Common radius `r > 0`**: take `r` to be the minimum of the geometric
   `multi_pole_common_radius` and the per-crossing chord-quotient threshold
   radii from `exists_chord_slitPlane_radius_right/left` and
   `exists_chord_div_endpoint_slitPlane_right/left`.

2. **Smooth complement bound** via `multi_pole_smooth_complement_far_bound`.

3. **Per-window convergence**: for each crossing `t_i`, apply
   `perCrossing_window_integral_tendsto_exact` to get convergence of
   `∫_{t_i - r}^{t_i + r} cpvIntegrand` to some `λ_i`.

4. **Recursive decomposition** along sorted breakpoints: the cutoff integral
   `∫_0^1 cpvIntegrand` decomposes into a sum of smooth-piece integrals
   (which are constant in ε for ε small) plus window integrals.

5. **Sum convergence**: combine constant smooth pieces and per-window
   convergences via `Tendsto.add`.

## Main result

* `hasCauchyPV_inv_sub_multiCrossing` — multi-crossing CPV existence for
  any `card ≥ 0`.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2 §3.
-/

open Filter Topology Set Complex MeasureTheory
open scoped Real Interval

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-- Given a nonempty Finset `S` and a function `f` taking positive values on members
of `S`, extract a positive lower bound `r_min` for `f` on `S`. -/
private lemma exists_pos_min_image {α : Type*} {S : Finset α} (h_nonempty : S.Nonempty)
    (f : ∀ a ∈ S, ℝ) (hf_pos : ∀ a (ha : a ∈ S), 0 < f a ha) :
    ∃ r_min > 0, ∀ a (ha : a ∈ S), r_min ≤ f a ha := by
  obtain ⟨⟨a₀, ha₀⟩, _, h_min⟩ := Finset.exists_min_image S.attach
    (fun ⟨a, ha⟩ => f a ha) (Finset.attach_nonempty_iff.mpr h_nonempty)
  exact ⟨_, hf_pos a₀ ha₀, fun a ha => h_min ⟨a, ha⟩ (Finset.mem_attach _ _)⟩

/-- Shared boilerplate for the four CPV existence theorems: given crossing
endpoint/pairwise data at the geometric radius `r_geom` and a shrunk radius
`r ≤ r_geom` with `r < r_geom`, derive: window inclusion in `[0, 1]`, endpoint
bounds (loose and strict) at `r`, and the pairwise `2r < |t - t'|`. -/
private lemma multiCrossing_window_data {crossings : Finset ℝ} {r r_geom : ℝ}
    (hr_le_geom : r ≤ r_geom) (hr_lt_geom : r < r_geom)
    (hr_geom_endpts : ∀ t ∈ crossings, r_geom ≤ t ∧ t ≤ 1 - r_geom)
    (hr_geom_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r_geom < |t - t'|) :
    (∀ t_i ∈ crossings, Set.Icc (t_i - r) (t_i + r) ⊆ Set.Icc (0 : ℝ) 1) ∧
    (∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r) ∧
    (∀ t ∈ crossings, r < t ∧ t < 1 - r) ∧
    (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|) :=
  ⟨fun t_i ht_i_mem t ht =>
      ⟨by linarith [ht.1, (hr_geom_endpts t_i ht_i_mem).1],
       by linarith [ht.2, (hr_geom_endpts t_i ht_i_mem).2]⟩,
   fun t ht =>
      ⟨hr_le_geom.trans (hr_geom_endpts t ht).1,
       by linarith [(hr_geom_endpts t ht).2]⟩,
   fun t ht =>
      ⟨hr_lt_geom.trans_le (hr_geom_endpts t ht).1,
       by linarith [(hr_geom_endpts t ht).2]⟩,
   fun t ht t' ht' hne => by linarith [hr_geom_pair t ht t' ht' hne]⟩

/-- **Per-crossing radius existence**: for each crossing `t_i`, extract a
positive radius `r_i` such that all four slit-plane chord-quotient/boundary
conditions hold uniformly on `[t_i - r_i, t_i + r_i]`. -/
private theorem exists_per_crossing_radius
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ = s) :
    ∃ (r : ℝ) (L_R L_L : ℂ),
      0 < r ∧ L_R ≠ 0 ∧ L_L ≠ 0 ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_R
        (Set.Ioi t₀) t₀ ∧
      HasDerivWithinAt γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend L_L
        (Set.Iio t₀) t₀ ∧
      (∀ a b, t₀ < a → a ≤ b → b ≤ t₀ + r →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (∀ a b, t₀ - r ≤ a → a ≤ b → b < t₀ →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend b - s) /
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a - s) ∈
            Complex.slitPlane) ∧
      (∀ r', 0 < r' → r' ≤ r →
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ + r') - s) / L_R ∈
          Complex.slitPlane) ∧
      (∀ r', 0 < r' → r' ≤ r →
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r') ≠ s →
          (-L_L) /
            (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t₀ - r') - s) ∈
            Complex.slitPlane) := by
  obtain ⟨L_R, L_L, hL_R_ne, hL_L_ne, h_deriv_right, h_deriv_left⟩ :=
    oneSided_deriv_setup γ ht₀
  obtain ⟨r_R₁, hr_R₁_pos, hr_R₁_slit⟩ :=
    exists_chord_slitPlane_radius_right h_deriv_right h_at hL_R_ne
  obtain ⟨r_L₁, hr_L₁_pos, hr_L₁_slit⟩ :=
    exists_chord_slitPlane_radius_left h_deriv_left h_at hL_L_ne
  obtain ⟨r_R₂, hr_R₂_pos, hr_R₂_endpoint⟩ :=
    exists_chord_div_endpoint_slitPlane_right h_deriv_right h_at hL_R_ne
  obtain ⟨r_L₂, hr_L₂_pos, hr_L₂_endpoint⟩ :=
    exists_chord_div_endpoint_slitPlane_left h_deriv_left h_at hL_L_ne
  set r : ℝ := min (min r_R₁ r_L₁) (min r_R₂ r_L₂)
  have hr_le_R₁ : r ≤ r_R₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hr_le_L₁ : r ≤ r_L₁ := (min_le_left _ _).trans (min_le_right _ _)
  have hr_le_R₂ : r ≤ r_R₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hr_le_L₂ : r ≤ r_L₂ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, L_R, L_L, lt_min (lt_min hr_R₁_pos hr_L₁_pos) (lt_min hr_R₂_pos hr_L₂_pos),
    hL_R_ne, hL_L_ne, h_deriv_right, h_deriv_left, ?_, ?_, ?_, ?_⟩
  · exact fun a b ha_gt hab hb_le =>
      hr_R₁_slit a b ha_gt hab (hb_le.trans (by linarith [hr_le_R₁]))
  · exact fun a b ha_ge hab hb_lt =>
      hr_L₁_slit a b ((by linarith [hr_le_L₁] : t₀ - r_L₁ ≤ a)) hab hb_lt
  · exact fun r' hr'_pos hr'_le =>
      hr_R₂_endpoint r' hr'_pos (hr'_le.trans hr_le_R₂)
  · exact fun r' hr'_pos hr'_le h_γ_ne =>
      hr_L₂_endpoint r' hr'_pos (hr'_le.trans hr_le_L₂) h_γ_ne

/-- **Inductive convergence statement, corner-friendly form** (T-BR-Y11c).

Counterpart to `cpv_tendsto_along_sorted` that drops the off-partition
hypothesis per crossing. -/
private theorem cpv_tendsto_along_sorted_corner
    (γ : ClosedPwC1Immersion x) {s : ℂ} (r : ℝ) (hr_pos : 0 < r) :
    ∀ (sorted : List ℝ), sorted.SortedLT →
    ∀ (a : ℝ), (∀ t ∈ sorted, a < t - r) → a ≤ 1 →
      Set.Icc a 1 ⊆ Set.Icc (0 : ℝ) 1 →
      (∀ t ∈ sorted, t ≤ 1 - r) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r < |t - t'|) →
      (∀ t ∈ sorted, ∀ t' ∈ Set.Icc (t - r) (t + r),
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t' = s → t' = t) →
      (∀ t ∈ sorted, t ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ t ∈ sorted, γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s) →
      (∀ t ∈ sorted, ∃ lam_t : ℂ,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t - r)..(t + r),
            cpvIntegrand (fun z => (z - s)⁻¹)
              γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε u)
          (𝓝[>] (0 : ℝ)) (𝓝 lam_t)) →
      (∃ m : ℝ, 0 < m ∧ ∀ u ∈ Set.Icc a 1,
        (∀ t ∈ sorted, u ∉ Set.Ioo (t - r) (t + r)) → m ≤
          ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend u - s‖) →
      ∃ L : ℂ, Tendsto (fun ε : ℝ =>
        ∫ t in a..1,
          cpvIntegrand (fun z => (z - s)⁻¹)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
        (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  intro sorted hsorted
  induction sorted with
  | nil =>
    intro a _h_a_lt h_a_le_1 _h_a_in_unit _h_t_le_1mr _h_pairwise
      _h_local_unique _h_t_Ioo _h_t_at _h_window_conv h_smooth_bound
    obtain ⟨m, hm_pos, hm_bound⟩ := h_smooth_bound
    have h_far_uniform : ∀ u ∈ Set.Icc a 1, m ≤ ‖γf u - s‖ := fun u hu =>
      hm_bound u hu (fun _ h => absurd h List.not_mem_nil)
    refine ⟨∫ t in a..1, (γf t - s)⁻¹ * deriv γf t, ?_⟩
    have h_event : (fun ε : ℝ =>
        ∫ t in a..1, cpvIntegrand (fun z => (z - s)⁻¹) γf s ε t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun _ => ∫ t in a..1, (γf t - s)⁻¹ * deriv γf t) := by
      filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le h_a_le_1] at hu
      exact cpvIntegrand_of_gt (lt_of_lt_of_le hε.2 (h_far_uniform u hu))
    exact Tendsto.congr' h_event.symm tendsto_const_nhds
  | cons t rest IH =>
    intro a h_a_lt h_a_le_1 h_a_in_unit h_t_le_1mr h_pairwise
      h_local_unique h_t_Ioo h_t_at h_window_conv h_smooth_bound
    have h_a_lt_t : a < t - r := h_a_lt t (List.mem_cons_self)
    obtain ⟨m, hm_pos, hm_bound⟩ := h_smooth_bound
    obtain ⟨lam_t, h_lam_t⟩ := h_window_conv t (List.mem_cons_self)
    have hrest_sorted : rest.SortedLT := hsorted.pairwise.tail.sortedLT
    have h_t_le_1mr_t : t ≤ 1 - r := h_t_le_1mr t (List.mem_cons_self)
    have h_rest_gt_t : ∀ t' ∈ rest, t < t' := fun t' ht' =>
      (List.pairwise_cons.mp hsorted.pairwise).1 t' ht'
    have h_rest_window_above : ∀ t' ∈ rest, t + r < t' - r := by
      intro t' ht'
      have h_t_lt_t' : t < t' := h_rest_gt_t t' ht'
      have h_pair := h_pairwise t List.mem_cons_self t'
        (List.mem_cons_of_mem t ht') (ne_of_gt h_t_lt_t')
      have h_abs : |t - t'| = t' - t := by
        rw [abs_sub_comm]; exact abs_of_pos (by linarith)
      linarith
    have h_t_plus_r_le_1 : t + r ≤ 1 := by linarith
    have h_IH_a_lt : ∀ t' ∈ rest, t + r < t' - r := h_rest_window_above
    have h_IH_a_in_unit : Set.Icc (t + r) 1 ⊆ Set.Icc (0 : ℝ) 1 := fun u hu =>
      ⟨by linarith [(h_t_Ioo t List.mem_cons_self).1, hu.1, hr_pos], hu.2⟩
    have h_IH_t_le : ∀ t' ∈ rest, t' ≤ 1 - r := fun t' ht' =>
      h_t_le_1mr t' (List.mem_cons_of_mem t ht')
    have h_IH_pair : ∀ t' ∈ rest, ∀ t'' ∈ rest, t'' ≠ t' →
        2 * r < |t' - t''| := fun t' ht' t'' ht'' hne =>
      h_pairwise t' (List.mem_cons_of_mem t ht') t''
        (List.mem_cons_of_mem t ht'') hne
    have h_IH_local : ∀ t' ∈ rest, ∀ u ∈ Set.Icc (t' - r) (t' + r),
        γf u = s → u = t' := fun t' ht' u hu h_eq =>
      h_local_unique t' (List.mem_cons_of_mem t ht') u hu h_eq
    have h_IH_t_Ioo : ∀ t' ∈ rest, t' ∈ Set.Ioo (0 : ℝ) 1 := fun t' ht' =>
      h_t_Ioo t' (List.mem_cons_of_mem t ht')
    have h_IH_t_at : ∀ t' ∈ rest, γf t' = s := fun t' ht' =>
      h_t_at t' (List.mem_cons_of_mem t ht')
    have h_IH_window_conv : ∀ t' ∈ rest, ∃ lam_t' : ℂ,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t' - r)..(t' + r),
            cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
          (𝓝[>] (0 : ℝ)) (𝓝 lam_t') :=
      fun t' ht' => h_window_conv t' (List.mem_cons_of_mem t ht')
    have h_IH_smooth_bound : ∃ m' : ℝ, 0 < m' ∧
        ∀ u ∈ Set.Icc (t + r) 1,
          (∀ t' ∈ rest, u ∉ Set.Ioo (t' - r) (t' + r)) → m' ≤ ‖γf u - s‖ := by
      refine ⟨m, hm_pos, ?_⟩
      intro u hu h_avoid
      have hu_in_a : u ∈ Set.Icc a 1 := by
        refine ⟨?_, hu.2⟩
        linarith [hu.1, h_a_lt_t]
      apply hm_bound u hu_in_a
      intro t' ht' h_in
      rcases List.mem_cons.mp ht' with rfl | h_in_rest
      · linarith [hu.1, h_in.2]
      · exact h_avoid t' h_in_rest h_in
    obtain ⟨L_rest, hL_rest⟩ := IH hrest_sorted (t + r) h_IH_a_lt h_t_plus_r_le_1
      h_IH_a_in_unit h_IH_t_le h_IH_pair h_IH_local h_IH_t_Ioo
      h_IH_t_at h_IH_window_conv h_IH_smooth_bound
    have h_a_lt_t_minus_r : a ≤ t - r := le_of_lt h_a_lt_t
    have h_smooth_left : ∀ u ∈ Set.Icc a (t - r), m ≤ ‖γf u - s‖ := by
      intro u hu
      apply hm_bound u ⟨hu.1, by linarith [hu.2, h_t_le_1mr_t]⟩
      intro t' ht' h_in_window
      rcases List.mem_cons.mp ht' with rfl | h_in_rest
      · linarith [hu.2, h_in_window.1]
      · linarith [hu.2, h_in_window.1, h_rest_window_above t' h_in_rest]
    have h_ne_smooth_left : ∀ u ∈ Set.Icc a (t - r), γf u ≠ s := fun u hu h_eq => by
      have h_bd := h_smooth_left u hu
      rw [h_eq, sub_self, norm_zero] at h_bd; linarith
    set const_left : ℂ := ∫ u in a..(t - r), (γf u - s)⁻¹ * deriv γf u
    have h_in_unit_left : Set.Icc a (t - r) ⊆ Set.Icc (0 : ℝ) 1 := by
      intro u hu
      refine ⟨h_a_in_unit ⟨hu.1, le_trans hu.2 ?_⟩|>.1,
        h_a_in_unit ⟨hu.1, le_trans hu.2 ?_⟩|>.2⟩
      all_goals linarith [h_t_le_1mr_t]
    have h_int_left :=
      inv_sub_mul_deriv_intervalIntegrable γ h_a_lt_t_minus_r
        h_in_unit_left h_ne_smooth_left
    have h_smooth_left_const : (fun ε : ℝ =>
        ∫ u in a..(t - r), cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
        =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => const_left) := by
      filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
      have hε_pos : 0 < ε := hε.1
      have hε_lt_m : ε < m := hε.2
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le h_a_lt_t_minus_r] at hu
      have h_norm := h_smooth_left u hu
      exact cpvIntegrand_of_gt (lt_of_lt_of_le hε_lt_m h_norm)
    refine ⟨const_left + lam_t + L_rest, ?_⟩
    have h_t_minus_r_lt_t_plus_r : t - r ≤ t + r := by linarith
    have h_split_eq : (fun ε : ℝ =>
        ∫ u in a..1, cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε => (∫ u in a..(t - r), cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u) +
                  (∫ u in (t - r)..(t + r), cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u) +
                  (∫ u in (t + r)..1, cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)) := by
      filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
      have hε_pos : 0 < ε := hε.1
      have hε_lt_m : ε < m := hε.2
      have h_cpv_int_on : ∀ α β : ℝ, α ≤ β → Set.Icc α β ⊆ Set.Icc (0 : ℝ) 1 →
          IntervalIntegrable
            (fun u => cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
            MeasureTheory.volume α β := by
        intro α β hαβ h_in_unit
        have hγ_int_01 : IntervalIntegrable (deriv γf) MeasureTheory.volume 0 1 :=
          γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable
        have hα_ge_0 : 0 ≤ α := (h_in_unit (Set.left_mem_Icc.mpr hαβ)).1
        have hβ_le_1 : β ≤ 1 := (h_in_unit (Set.right_mem_Icc.mpr hαβ)).2
        have hγ_int : IntervalIntegrable (deriv γf) MeasureTheory.volume α β := by
          refine hγ_int_01.mono_set ?_
          rw [Set.uIcc_of_le hαβ, Set.uIcc_of_le zero_le_one]
          exact Set.Icc_subset_Icc hα_ge_0 hβ_le_1
        have h_cont_γf : Continuous γf :=
          γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
        have h_sm_γf : Measurable γf := h_cont_γf.measurable
        have h_sm_norm : Measurable (fun u => ‖γf u - s‖) :=
          ((h_sm_γf.sub measurable_const).norm)
        have h_meas_pred : MeasurableSet {u | ε < ‖γf u - s‖} :=
          h_sm_norm measurableSet_Ioi
        have h_sm_prod : Measurable (fun u => (γf u - s)⁻¹ * deriv γf u) :=
          (h_sm_γf.sub measurable_const).inv.mul (measurable_deriv γf)
        have h_sm : Measurable (fun u => cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u) := by
          unfold cpvIntegrand
          exact Measurable.ite h_meas_pred h_sm_prod measurable_const
        have h_meas : AEStronglyMeasurable
            (fun u => cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
            (MeasureTheory.volume.restrict (Set.uIoc α β)) :=
          h_sm.aestronglyMeasurable
        have h_bd : ∀ u, ‖cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u‖ ≤
            (1 / ε) * ‖deriv γf u‖ := by
          intro u
          simp only [cpvIntegrand]
          split_ifs with h_gt
          · have h_norm_pos : 0 < ‖γf u - s‖ := lt_trans hε_pos h_gt
            rw [norm_mul, norm_inv]
            have h_le : 1 / ‖γf u - s‖ ≤ 1 / ε :=
              one_div_le_one_div_of_le hε_pos h_gt.le
            calc ‖γf u - s‖⁻¹ * ‖deriv γf u‖
                = (1 / ‖γf u - s‖) * ‖deriv γf u‖ := by rw [inv_eq_one_div]
              _ ≤ (1 / ε) * ‖deriv γf u‖ :=
                mul_le_mul_of_nonneg_right h_le (norm_nonneg _)
          · simp [norm_zero]
            positivity
        have h_int_dom : IntervalIntegrable (fun u => (1 / ε) * ‖deriv γf u‖)
            MeasureTheory.volume α β :=
          (hγ_int.norm).const_mul (1 / ε)
        exact IntervalIntegrable.mono_fun' h_int_dom h_meas
          (Filter.Eventually.of_forall fun u => h_bd u)
      have h_in_unit_a_tr : Set.Icc a (t - r) ⊆ Set.Icc (0 : ℝ) 1 := by
        intro u hu
        refine ⟨?_, ?_⟩
        · exact le_trans (h_a_in_unit ⟨le_refl _, h_a_le_1⟩).1 hu.1
        · linarith [hu.2, h_t_le_1mr_t]
      have h_cpv_int_left : IntervalIntegrable
          (fun u => cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
          MeasureTheory.volume a (t - r) :=
        h_cpv_int_on a (t - r) h_a_lt_t_minus_r h_in_unit_a_tr
      have h_t_minus_r_ge_0 : 0 ≤ t - r := by
        linarith [(h_a_in_unit ⟨le_refl _, h_a_le_1⟩).1, h_a_lt_t]
      have h_in_unit_mid : Set.Icc (t - r) (t + r) ⊆ Set.Icc (0 : ℝ) 1 :=
        Set.Icc_subset_Icc h_t_minus_r_ge_0 h_t_plus_r_le_1
      have h_cpv_int_mid : IntervalIntegrable
          (fun u => cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
          MeasureTheory.volume (t - r) (t + r) :=
        h_cpv_int_on (t - r) (t + r) h_t_minus_r_lt_t_plus_r h_in_unit_mid
      have h_cpv_int_right : IntervalIntegrable
          (fun u => cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
          MeasureTheory.volume (t + r) 1 :=
        h_cpv_int_on (t + r) 1 h_t_plus_r_le_1 h_IH_a_in_unit
      have h_split1 := intervalIntegral.integral_add_adjacent_intervals
        h_cpv_int_left h_cpv_int_mid
      have h_split2 := intervalIntegral.integral_add_adjacent_intervals
        (h_cpv_int_left.trans h_cpv_int_mid) h_cpv_int_right
      rw [← h_split2, ← h_split1]
    refine Tendsto.congr' h_split_eq.symm ?_
    have h_tendsto_left : Tendsto (fun ε : ℝ =>
        ∫ u in a..(t - r), cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
        (𝓝[>] (0 : ℝ)) (𝓝 const_left) :=
      Tendsto.congr' h_smooth_left_const.symm tendsto_const_nhds
    exact ((h_tendsto_left.add h_lam_t).add hL_rest)

/-- **Corner-friendly common local-uniqueness radius** (T-BR-Y11c / T-BR-Y11b).
Returns `r > 0` such that for every `t_i ∈ crossings`:
* `t_i - r ≥ 0`, `t_i + r ≤ 1`;
* Windows are pairwise disjoint at width `2r`;
* No partition point in `partition \ crossings` lies in `[t_i - r, t_i + r]`. -/
private theorem multi_pole_common_radius_corner_simple
    {crossings partition : Finset ℝ}
    (h_nonempty : crossings.Nonempty)
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ r > 0,
      (∀ t ∈ crossings, r ≤ t ∧ t ≤ 1 - r) ∧
      (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t →
        2 * r < |t - t'|) ∧
      (∀ t ∈ crossings, ∀ p ∈ partition, p ∉ crossings → r < |t - p|) := by
  classical
  set P' : Finset ℝ := partition \ crossings
  have h_off' : ∀ t ∈ crossings, t ∉ P' := fun _ ht hP' =>
    (Finset.mem_sdiff.mp hP').2 ht
  obtain ⟨r, hr_pos, h_endpts, h_pair, h_part⟩ :=
    multi_pole_common_radius (crossings := crossings) (partition := P')
      h_nonempty h_Ioo h_off'
  exact ⟨r, hr_pos, h_endpts, h_pair, fun t ht p hp hp_notin =>
    h_part t ht p (Finset.mem_sdiff.mpr ⟨hp, hp_notin⟩)⟩

/-- **Corner-friendly multi-crossing simple-pole CPV existence (T-BR-Y11c).**

Counterpart to `hasCauchyPV_inv_sub_multiCrossing` that admits corner
crossings. The caller provides a `Finset ℝ` of crossings (all in the
open unit interval, hitting `s`, and complete) together with per-crossing
flatness of order 1. There exists `L : ℂ` with
`HasCauchyPV ((z - s)⁻¹) γ s L`.

For smooth crossings (`t_i ∉ partition`) this reduces to T-BR-Y9d; the
corner case is handled by the same per-window infrastructure, since
`perCrossing_window_integral_tendsto_exact` and `localDerivedCutoffs` no
longer require off-partition. -/
theorem hasCauchyPV_inv_sub_multiCrossing_corner
    {γ : ClosedPwC1Immersion x} {s : ℂ}
    {crossings : Finset ℝ}
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : ∀ t ∈ crossings,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s)
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    (_h_flat_at_each : ∀ t₀ ∈ crossings,
      IsFlatOfOrder γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1) :
    ∃ L : ℂ, HasCauchyPV (fun z => (z - s)⁻¹)
      γ.toPwC1Immersion.toPiecewiseC1Path s L := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  by_cases h_empty : crossings = ∅
  · have h_avoid : ∀ t ∈ Set.Icc (0 : ℝ) 1, γf t ≠ s := fun t ht h_eq =>
      absurd (h_empty ▸ h_complete t ht h_eq) (Finset.notMem_empty t)
    have hγ_cont : Continuous γf :=
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
    obtain ⟨t_min, ht_min_mem, ht_min⟩ := isCompact_Icc.exists_isMinOn
      ⟨0, le_rfl, zero_le_one⟩ ((hγ_cont.continuousOn.sub continuousOn_const).norm)
    refine ⟨_, hasCauchyPV_of_avoids (f := fun z => (z - s)⁻¹)
      ⟨‖γf t_min - s‖, norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t_min ht_min_mem)),
       fun t ht => ht_min ht⟩⟩
  · have h_nonempty : crossings.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    have h_per_cross : ∀ t_i ∈ crossings, ∃ (r : ℝ) (L_R L_L : ℂ),
        0 < r ∧ L_R ≠ 0 ∧ L_L ≠ 0 ∧
        HasDerivWithinAt γf L_R (Set.Ioi t_i) t_i ∧
        HasDerivWithinAt γf L_L (Set.Iio t_i) t_i ∧
        (∀ a b, t_i < a → a ≤ b → b ≤ t_i + r →
          (γf b - s) / (γf a - s) ∈ Complex.slitPlane) ∧
        (∀ a b, t_i - r ≤ a → a ≤ b → b < t_i →
          (γf b - s) / (γf a - s) ∈ Complex.slitPlane) ∧
        (∀ r', 0 < r' → r' ≤ r → (γf (t_i + r') - s) / L_R ∈ Complex.slitPlane) ∧
        (∀ r', 0 < r' → r' ≤ r → γf (t_i - r') ≠ s →
          (-L_L) / (γf (t_i - r') - s) ∈ Complex.slitPlane) := by
      intro t_i ht_i_mem
      have ht_i_Ioo : t_i ∈ Set.Ioo (0 : ℝ) 1 := h_Ioo t_i ht_i_mem
      have h_at_t_i : γf t_i = s := h_at t_i ht_i_mem
      exact exists_per_crossing_radius (s := s) (t₀ := t_i) γ ht_i_Ioo h_at_t_i
    let r_at : ∀ t_i ∈ crossings, ℝ := fun t_i ht_i_mem =>
      (h_per_cross t_i ht_i_mem).choose
    have hr_at_pos : ∀ t_i (ht_i_mem : t_i ∈ crossings), 0 < r_at t_i ht_i_mem :=
      fun t_i ht_i_mem => (h_per_cross t_i ht_i_mem).choose_spec.choose_spec.choose_spec.1
    obtain ⟨r_chord, hr_chord_pos, hr_chord_min⟩ :=
      exists_pos_min_image h_nonempty r_at hr_at_pos
    obtain ⟨r_geom, hr_geom_pos, hr_geom_endpts, hr_geom_pair, _hr_geom_part⟩ :=
      multi_pole_common_radius_corner_simple (crossings := crossings)
        (partition := γ.toPwC1Immersion.toPiecewiseC1Path.partition)
        h_nonempty
        (fun t ht => h_Ioo t ht)
    set r : ℝ := min r_chord (r_geom / 2)
    have hr_pos : 0 < r := lt_min hr_chord_pos (by linarith)
    have hr_le_chord : r ≤ r_chord := min_le_left _ _
    have hr_lt_geom : r < r_geom := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hr_le_geom : r ≤ r_geom := hr_lt_geom.le
    obtain ⟨h_window_in_unit, h_endpts_r, h_endpts_r_strict, h_pair_r⟩ :=
      multiCrossing_window_data hr_le_geom hr_lt_geom hr_geom_endpts hr_geom_pair
    have h_local_unique_at : ∀ t_i ∈ crossings,
        ∀ t ∈ Set.Icc (t_i - r) (t_i + r), γf t = s → t = t_i := by
      intro t_i ht_i_mem t ht_in h_eq
      apply multi_pole_local_uniqueness γ hr_pos
        h_endpts_r h_pair_r
        (fun t' ht'_in h_eq' => h_complete t' ht'_in h_eq')
        ht_i_mem ht_in h_eq
    obtain ⟨m, hm_pos, h_smooth_bound⟩ :=
      multi_pole_smooth_complement_far_bound (γ := γ) (s := s)
        (crossings := crossings) h_complete (fun _ => r) (fun _ _ => hr_pos)
    have hr_le_r_at : ∀ t_i (ht_i_mem : t_i ∈ crossings),
        r ≤ r_at t_i ht_i_mem := fun t_i ht_i_mem =>
      le_trans hr_le_chord (hr_chord_min t_i ht_i_mem)
    have h_per_window_conv : ∀ t_i ∈ crossings, ∃ L_i : ℂ,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t_i - r)..(t_i + r), cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
          (𝓝[>] (0 : ℝ)) (𝓝 L_i) := by
      intro t_i ht_i_mem
      have ht_i_Ioo : t_i ∈ Set.Ioo (0 : ℝ) 1 := h_Ioo t_i ht_i_mem
      have h_at_t_i : γf t_i = s := h_at t_i ht_i_mem
      have h_w_unit := h_window_in_unit t_i ht_i_mem
      have h_lu := h_local_unique_at t_i ht_i_mem
      have hr_at_le := hr_le_r_at t_i ht_i_mem
      set spec := (h_per_cross t_i ht_i_mem).choose_spec.choose_spec.choose_spec
      obtain ⟨_hr_at_pos, hL_R_ne, hL_L_ne, h_deriv_right, h_deriv_left,
        h_slit_R_at, h_slit_L_at, h_endR_at, h_endL_at⟩ := spec
      have h_slit_R : ∀ a b, t_i < a → a ≤ b → b ≤ t_i + r →
          (γf b - s) / (γf a - s) ∈ Complex.slitPlane :=
        fun a b ha_gt hab hb_le =>
          h_slit_R_at a b ha_gt hab (le_trans hb_le (by linarith [hr_at_le]))
      have h_slit_L : ∀ a b, t_i - r ≤ a → a ≤ b → b < t_i →
          (γf b - s) / (γf a - s) ∈ Complex.slitPlane :=
        fun a b ha_ge hab hb_lt =>
          h_slit_L_at a b (le_trans (by linarith [hr_at_le]) ha_ge) hab hb_lt
      have h_γPlus_div_LR := h_endR_at r hr_pos hr_at_le
      have h_γMinus_ne : γf (t_i - r) ≠ s := fun h_eq => by
        have := h_lu _ ⟨le_rfl, by linarith⟩ h_eq; linarith
      have h_LL_neg_div_γMinus := h_endL_at r hr_pos hr_at_le h_γMinus_ne
      exact perCrossing_window_integral_tendsto_exact γ ht_i_Ioo h_at_t_i hr_pos
        h_w_unit h_lu hL_R_ne hL_L_ne h_deriv_right h_deriv_left
        h_slit_R h_slit_L h_γPlus_div_LR h_LL_neg_div_γMinus
    set sortedList : List ℝ := crossings.sort (· ≤ ·)
    have hsorted_lt : sortedList.SortedLT := Finset.sortedLT_sort crossings
    have h_sorted_eq : ∀ t, t ∈ sortedList ↔ t ∈ crossings := by
      intro t; exact Finset.mem_sort _
    have h_sorted_a_lt : ∀ t ∈ sortedList, (0 : ℝ) < t - r := by
      intro t ht
      have ht_in : t ∈ crossings := (h_sorted_eq t).mp ht
      have ⟨ht_gt, _⟩ := h_endpts_r_strict t ht_in
      linarith
    have h_a_le_1 : (0 : ℝ) ≤ 1 := zero_le_one
    have h_a_in_unit : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := subset_refl _
    have h_sorted_t_le_1mr : ∀ t ∈ sortedList, t ≤ 1 - r := fun t ht =>
      (h_endpts_r t ((h_sorted_eq t).mp ht)).2
    have h_sorted_pair : ∀ t ∈ sortedList, ∀ t' ∈ sortedList, t' ≠ t →
        2 * r < |t - t'| := fun t ht t' ht' hne =>
      h_pair_r t ((h_sorted_eq t).mp ht) t' ((h_sorted_eq t').mp ht') hne
    have h_sorted_local : ∀ t ∈ sortedList,
        ∀ u ∈ Set.Icc (t - r) (t + r), γf u = s → u = t := fun t ht =>
      h_local_unique_at t ((h_sorted_eq t).mp ht)
    have h_sorted_Ioo : ∀ t ∈ sortedList, t ∈ Set.Ioo (0 : ℝ) 1 := fun t ht =>
      h_Ioo t ((h_sorted_eq t).mp ht)
    have h_sorted_at : ∀ t ∈ sortedList, γf t = s := fun t ht =>
      h_at t ((h_sorted_eq t).mp ht)
    have h_sorted_window_conv : ∀ t ∈ sortedList, ∃ lam_t : ℂ,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t - r)..(t + r), cpvIntegrand (fun z => (z - s)⁻¹) γf s ε u)
          (𝓝[>] (0 : ℝ)) (𝓝 lam_t) := fun t ht =>
      h_per_window_conv t ((h_sorted_eq t).mp ht)
    have h_sorted_smooth : ∃ m : ℝ, 0 < m ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          (∀ t ∈ sortedList, u ∉ Set.Ioo (t - r) (t + r)) → m ≤ ‖γf u - s‖ := by
      refine ⟨m, hm_pos, ?_⟩
      intro u hu h_avoid
      apply h_smooth_bound u hu
      intro t_i ht_i_in
      have ht_i_sort : t_i ∈ sortedList := (h_sorted_eq t_i).mpr ht_i_in
      exact h_avoid t_i ht_i_sort
    obtain ⟨L, hL⟩ := cpv_tendsto_along_sorted_corner γ r hr_pos sortedList hsorted_lt
      (0 : ℝ) h_sorted_a_lt h_a_le_1 h_a_in_unit h_sorted_t_le_1mr h_sorted_pair
      h_sorted_local h_sorted_Ioo h_sorted_at h_sorted_window_conv h_sorted_smooth
    refine ⟨L, ?_⟩
    unfold HasCauchyPV
    exact hL

/-- **Integrability of `c · γ' / (γ - s)^k` on an interval avoiding `s`.**

For a closed piecewise-`C¹` immersion `γ` and an interval `[a, b] ⊆ [0, 1]`
on which `γ` avoids `s`, the integrand `c · γ' / (γ - s)^k` is
interval-integrable. -/
private theorem pow_inv_mul_deriv_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ} (c : ℂ) (k : ℕ)
    (hab : a ≤ b) (h_in_Icc : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1)
    (h_ne : ∀ t ∈ Set.Icc a b,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s) :
    IntervalIntegrable
      (fun t => c *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t /
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t - s) ^ k)
      MeasureTheory.volume a b := by
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    with hγf_def
  have hγ_int_01 : IntervalIntegrable (deriv γf) MeasureTheory.volume 0 1 :=
    γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable
  have hγ_int : IntervalIntegrable (deriv γf) MeasureTheory.volume a b := by
    refine hγ_int_01.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]
    exact h_in_Icc
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  have h_pow_inv_cont : ContinuousOn (fun t => c / (γf t - s) ^ k) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have h_ft_ne : γf t ≠ s := h_ne t ht
    have h_pow_ne : (γf t - s) ^ k ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr h_ft_ne)
    refine ContinuousAt.continuousWithinAt
      (ContinuousAt.div continuousAt_const ?_ h_pow_ne)
    refine ContinuousAt.pow ?_ k
    exact (hγ_cont.continuousAt).sub continuousAt_const
  exact (hγ_int.mul_continuousOn h_pow_inv_cont).congr (fun t _ => by ring)

/-- **Cutoff integrand bounded by `‖c‖ / ε^k · ‖γ'‖`**, integrable on `[a, b]`. -/
private theorem cpvIntegrand_higherOrder_intervalIntegrable
    (γ : ClosedPwC1Immersion x) {s : ℂ} {a b : ℝ}
    (c : ℂ) (k : ℕ) (_hk_pos : 1 ≤ k)
    {ε : ℝ} (hε_pos : 0 < ε)
    (hab : a ≤ b) (h_in_Icc : Set.Icc a b ⊆ Set.Icc (0 : ℝ) 1) :
    IntervalIntegrable
      (fun t => cpvIntegrand (fun z => c / (z - s) ^ k)
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
      MeasureTheory.volume a b := by
  set γf : ℝ → ℂ := fun t => γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_int : IntervalIntegrable (deriv γf) MeasureTheory.volume a b := by
    refine γ.toClosedPwC1Curve.deriv_extend_intervalIntegrable.mono_set ?_
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le zero_le_one]; exact h_in_Icc
  have h_sm_γf : Measurable γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend.measurable
  have h_sm : Measurable
      (fun u => cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u) := by
    unfold cpvIntegrand
    exact Measurable.ite ((h_sm_γf.sub measurable_const).norm measurableSet_Ioi)
      (((h_sm_γf.sub measurable_const).pow_const k).const_div c |>.mul (measurable_deriv γf))
      measurable_const
  set M : ℝ := ‖c‖ / ε ^ k
  have h_bd : ∀ u,
      ‖cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u‖ ≤ M * ‖deriv γf u‖ := by
    intro u
    simp only [cpvIntegrand]
    split_ifs with h_gt
    · rw [norm_mul, norm_div, norm_pow]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_left (norm_nonneg c) (pow_pos hε_pos k)
          (pow_le_pow_left₀ hε_pos.le h_gt.le k)) (norm_nonneg _)
    · simp only [norm_zero]; positivity
  exact IntervalIntegrable.mono_fun' ((hγ_int.norm).const_mul M) h_sm.aestronglyMeasurable
    (Filter.Eventually.of_forall h_bd)

/-- Antiderivative `F(z) = -(k-1)⁻¹ · (z - s)^{-(k-1)}` for `k ≥ 2`. -/
private noncomputable def antiderivPow (s : ℂ) (k : ℕ) (z : ℂ) : ℂ :=
  -(↑(k - 1) : ℂ)⁻¹ * ((z - s) ^ (k - 1))⁻¹

/-- **Empty-case higher-order CPV vanishing.** When `γ` avoids `s` on `[0, 1]`,
the higher-order CPV `c / (z-s)^k` (for `k ≥ 2`) vanishes: the FTC integral
`∫_0^1 c·γ'/(γ-s)^k = c·(F(γ(1)) - F(γ(0))) = 0` by closedness, and
`hasCauchyPVOn_of_avoids` then gives the cutoff convergence. Shared between
`hasCauchyPVOn_multiCrossing_higherOrder` (T-BR-Y9e) and its corner-friendly
counterpart `hasCauchyPVOn_multiCrossing_higherOrder_corner` (T-BR-Y11b). -/
private theorem hasCauchyPVOn_higherOrder_of_avoids
    (γ : ClosedPwC1Immersion x) {s : ℂ} {k : ℕ} (hk : 2 ≤ k) (c : ℂ)
    (h_avoid : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t ≠ s) :
    HasCauchyPVOn {s} (fun z => c / (z - s) ^ k)
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  have hγ_cont : Continuous γf :=
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
  obtain ⟨t_min, ht_min_mem, ht_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨0, le_rfl, zero_le_one⟩ ((hγ_cont.continuousOn.sub continuousOn_const).norm)
  have hδ_pos : 0 < ‖γf t_min - s‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t_min ht_min_mem))
  set partSet : Set ℝ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) with partSet_def
  have h_partSet_countable : partSet.Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  have h_diff : ∀ u ∈ Set.Ioo (0 : ℝ) 1 \ partSet, HasDerivAt γf (deriv γf u) u :=
    fun u ⟨h_u_in, h_u_off⟩ =>
      (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend
        u h_u_in h_u_off).hasDerivAt
  have h_int : IntervalIntegrable
      (fun u => c * deriv γf u / (γf u - s) ^ k) MeasureTheory.volume 0 1 :=
    pow_inv_mul_deriv_intervalIntegrable γ c k zero_le_one (subset_refl _) h_avoid
  have h_FTC : ∫ u in (0 : ℝ)..1, c * deriv γf u / (γf u - s) ^ k =
      c * antiderivPow s k (γf 1) - c * antiderivPow s k (γf 0) := by
    set F : ℂ → ℂ := fun z => c * antiderivPow s k z
    have h_F_diff_at : ∀ u ∈ Set.Ioo (0 : ℝ) 1 \ partSet,
        HasDerivAt (fun v => F (γf v)) (c * deriv γf u / (γf u - s) ^ k) u := by
      intro u hu
      have h_γu_ne_s : γf u ≠ s := h_avoid u (Set.Ioo_subset_Icc_self hu.1)
      have h_F_at : HasDerivAt F (c * (1 / (γf u - s) ^ k)) (γf u) :=
        (hasDerivAt_antiderivative_pow_inv_complex hk h_γu_ne_s).const_mul c
      have h_chain := h_F_at.comp u (h_diff u hu)
      rw [show c * (1 / (γf u - s) ^ k) * deriv γf u =
          c * deriv γf u / (γf u - s) ^ k from by ring] at h_chain
      exact h_chain
    have h_Fγ_cont : ContinuousOn (fun v => F (γf v)) (Set.Icc (0 : ℝ) 1) := fun u hu =>
      (((hasDerivAt_antiderivative_pow_inv_complex hk
        (h_avoid u hu)).continuousAt).const_mul
        c).comp_continuousWithinAt (hγ_cont.continuousOn u hu)
    exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
      (fun v => F (γf v)) (fun u => c * deriv γf u / (γf u - s) ^ k)
      zero_le_one h_partSet_countable h_Fγ_cont h_F_diff_at h_int
  have h_closed : γf 0 = γf 1 := closed_immersion_extend_zero_eq_one γ
  have h_contour : γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral
      (fun z => c / (z - s) ^ k) = 0 := by
    show ∫ t in (0 : ℝ)..1,
        (fun z => c / (z - s) ^ k)
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) *
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = 0
    rw [show (fun t => (fun z => c / (z - s) ^ k)
      (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) *
      deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t) =
      (fun u => c * deriv γf u / (γf u - s) ^ k) from
      funext fun u => by ring, h_FTC, h_closed]
    ring
  have h_pv : HasCauchyPVOn {s} (fun z => c / (z - s) ^ k)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (γ.toPwC1Immersion.toPiecewiseC1Path.contourIntegral
        (fun z => c / (z - s) ^ k)) := by
    apply hasCauchyPVOn_of_avoids
    refine ⟨‖γf t_min - s‖, hδ_pos, ?_⟩
    intro s' hs' t ht
    rw [Finset.mem_singleton] at hs'
    subst hs'
    exact ht_min ht
  rw [h_contour] at h_pv
  exact h_pv

/-- **Inductive higher-order convergence statement, corner-friendly form**.

Counterpart to `cpv_higherOrder_tendsto_along_sorted` that drops the
off-partition hypothesis per crossing — the FTC machinery already tolerates
finite exceptions, so corner crossings are admitted. -/
private theorem cpv_higherOrder_tendsto_along_sorted_corner
    (γ : ClosedPwC1Immersion x) {s : ℂ} (r : ℝ) (hr_pos : 0 < r)
    (c : ℂ) (k : ℕ) (hk : 2 ≤ k) :
    ∀ (sorted : List ℝ), sorted.SortedLT →
    ∀ (a : ℝ), (∀ t ∈ sorted, a < t - r) → a ≤ 1 →
      Set.Icc a 1 ⊆ Set.Icc (0 : ℝ) 1 →
      (∀ t ∈ sorted, t ≤ 1 - r) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r < |t - t'|) →
      (∀ t ∈ sorted,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t - r)..(t + r),
            cpvIntegrand (fun z => c / (z - s) ^ k)
              γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε u)
          (𝓝[>] (0 : ℝ))
          (𝓝 (c * (antiderivPow s k
            (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t + r)) -
            antiderivPow s k
              (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t - r)))))) →
      (∃ m : ℝ, 0 < m ∧ ∀ u ∈ Set.Icc a 1,
        (∀ t ∈ sorted, u ∉ Set.Ioo (t - r) (t + r)) → m ≤
          ‖γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend u - s‖) →
      (∀ t ∈ sorted, t ∈ Set.Ioo (0 : ℝ) 1) →
      (∀ t ∈ sorted, γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s) →
      (∀ t ∈ sorted, ∀ u ∈ Set.Icc (t - r) (t + r),
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend u = s → u = t) →
      Tendsto (fun ε : ℝ =>
        ∫ t in a..1,
          cpvIntegrand (fun z => c / (z - s) ^ k)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (c * (antiderivPow s k
          (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1) -
          antiderivPow s k
            (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend a)))) := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  intro sorted hsorted
  induction sorted with
  | nil =>
    intro a _h_a_lt h_a_le_1 h_a_in_unit _h_t_le_1mr _h_pairwise
      _h_window_conv h_smooth_bound _h_t_Ioo _h_t_at _h_local_unique
    obtain ⟨m, hm_pos, hm_bound⟩ := h_smooth_bound
    have h_far_uniform : ∀ u ∈ Set.Icc a 1, m ≤ ‖γf u - s‖ := fun u hu =>
      hm_bound u hu (fun _ h => absurd h List.not_mem_nil)
    have h_ne : ∀ u ∈ Set.Icc a 1, γf u ≠ s := fun u hu h_eq => by
      have h_bd := h_far_uniform u hu
      rw [h_eq, sub_self, norm_zero] at h_bd; linarith
    set partSet : Set ℝ :=
      (γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) with partSet_def
    have h_partSet_countable : partSet.Countable :=
      γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
    have h_diff : ∀ u ∈ Set.Ioo a 1 \ partSet, HasDerivAt γf (deriv γf u) u := by
      intro u ⟨h_u_in, h_u_off⟩
      have h_u_pos : 0 < u := by
        linarith [(h_a_in_unit ⟨le_rfl, h_a_le_1⟩).1, h_u_in.1]
      exact (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend
        u ⟨h_u_pos, h_u_in.2⟩ h_u_off).hasDerivAt
    have hγ_continuous : Continuous γf :=
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
    have hγ_cont : ContinuousOn γf (Set.Icc a 1) := hγ_continuous.continuousOn
    have h_int : IntervalIntegrable
        (fun u => c * deriv γf u / (γf u - s) ^ k) MeasureTheory.volume a 1 :=
      pow_inv_mul_deriv_intervalIntegrable γ c k h_a_le_1 h_a_in_unit h_ne
    have h_FTC : ∫ u in a..1, c * deriv γf u / (γf u - s) ^ k =
        c * antiderivPow s k (γf 1) - c * antiderivPow s k (γf a) := by
      set F : ℂ → ℂ := fun z => c * antiderivPow s k z
      have h_F_diff_at : ∀ u ∈ Set.Ioo a 1 \ partSet,
          HasDerivAt (fun v => F (γf v)) (c * deriv γf u / (γf u - s) ^ k) u := by
        intro u hu
        have h_γu_ne_s : γf u ≠ s := h_ne u (Set.Ioo_subset_Icc_self hu.1)
        have h_F_at : HasDerivAt F (c * (1 / (γf u - s) ^ k)) (γf u) :=
          (hasDerivAt_antiderivative_pow_inv_complex hk h_γu_ne_s).const_mul c
        have h_chain := h_F_at.comp u (h_diff u hu)
        rw [show c * (1 / (γf u - s) ^ k) * deriv γf u =
            c * deriv γf u / (γf u - s) ^ k from by ring] at h_chain
        exact h_chain
      have h_Fγ_cont : ContinuousOn (fun v => F (γf v)) (Set.Icc a 1) := fun u hu =>
        (((hasDerivAt_antiderivative_pow_inv_complex hk (h_ne u hu)).continuousAt).const_mul
          c).comp_continuousWithinAt (hγ_cont u hu)
      exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (fun v => F (γf v)) (fun u => c * deriv γf u / (γf u - s) ^ k)
        h_a_le_1 h_partSet_countable h_Fγ_cont h_F_diff_at h_int
    have h_event : (fun ε : ℝ =>
        ∫ t in a..1, cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε t) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun _ => c * antiderivPow s k (γf 1) - c * antiderivPow s k (γf a)) := by
      filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
      have hε_pos : 0 < ε := hε.1
      have hε_lt_m : ε < m := hε.2
      calc ∫ t in a..1, cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε t
          = ∫ t in a..1, c * deriv γf t / (γf t - s) ^ k := by
            apply intervalIntegral.integral_congr
            intro u hu
            rw [Set.uIcc_of_le h_a_le_1] at hu
            have h_norm_gt : ε < ‖γf u - s‖ := lt_of_lt_of_le hε_lt_m (h_far_uniform u hu)
            simp only [cpvIntegrand, h_norm_gt, ite_true]
            ring
        _ = c * antiderivPow s k (γf 1) - c * antiderivPow s k (γf a) := h_FTC
    have h_target_eq : c * (antiderivPow s k (γf 1) - antiderivPow s k (γf a)) =
        c * antiderivPow s k (γf 1) - c * antiderivPow s k (γf a) := by ring
    rw [h_target_eq]
    exact Tendsto.congr' h_event.symm tendsto_const_nhds
  | cons t rest IH =>
    intro a h_a_lt h_a_le_1 h_a_in_unit h_t_le_1mr h_pairwise
      h_window_conv h_smooth_bound h_t_Ioo h_t_at h_local_unique
    have h_a_lt_t : a < t - r := h_a_lt t (List.mem_cons_self)
    obtain ⟨m, hm_pos, hm_bound⟩ := h_smooth_bound
    have h_lam_t := h_window_conv t (List.mem_cons_self)
    have hrest_sorted : rest.SortedLT := hsorted.pairwise.tail.sortedLT
    have h_t_le_1mr_t : t ≤ 1 - r := h_t_le_1mr t (List.mem_cons_self)
    have h_rest_gt_t : ∀ t' ∈ rest, t < t' := fun t' ht' =>
      (List.pairwise_cons.mp hsorted.pairwise).1 t' ht'
    have h_rest_window_above : ∀ t' ∈ rest, t + r < t' - r := by
      intro t' ht'
      have h_t_lt_t' : t < t' := h_rest_gt_t t' ht'
      have h_pair := h_pairwise t List.mem_cons_self t'
        (List.mem_cons_of_mem t ht') (ne_of_gt h_t_lt_t')
      have h_abs : |t - t'| = t' - t := by
        rw [abs_sub_comm]; exact abs_of_pos (by linarith)
      linarith
    have h_t_plus_r_le_1 : t + r ≤ 1 := by linarith
    have h_IH_a_lt : ∀ t' ∈ rest, t + r < t' - r := h_rest_window_above
    have h_IH_a_in_unit : Set.Icc (t + r) 1 ⊆ Set.Icc (0 : ℝ) 1 := fun u hu =>
      ⟨by linarith [(h_t_Ioo t List.mem_cons_self).1, hu.1, hr_pos], hu.2⟩
    have h_IH_t_le : ∀ t' ∈ rest, t' ≤ 1 - r := fun t' ht' =>
      h_t_le_1mr t' (List.mem_cons_of_mem t ht')
    have h_IH_pair : ∀ t' ∈ rest, ∀ t'' ∈ rest, t'' ≠ t' →
        2 * r < |t' - t''| := fun t' ht' t'' ht'' hne =>
      h_pairwise t' (List.mem_cons_of_mem t ht') t''
        (List.mem_cons_of_mem t ht'') hne
    have h_IH_t_Ioo : ∀ t' ∈ rest, t' ∈ Set.Ioo (0 : ℝ) 1 := fun t' ht' =>
      h_t_Ioo t' (List.mem_cons_of_mem t ht')
    have h_IH_t_at : ∀ t' ∈ rest, γf t' = s := fun t' ht' =>
      h_t_at t' (List.mem_cons_of_mem t ht')
    have h_IH_window_conv : ∀ t' ∈ rest,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t' - r)..(t' + r),
            cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
          (𝓝[>] (0 : ℝ))
          (𝓝 (c * (antiderivPow s k (γf (t' + r)) -
            antiderivPow s k (γf (t' - r))))) :=
      fun t' ht' => h_window_conv t' (List.mem_cons_of_mem t ht')
    have h_IH_local : ∀ t' ∈ rest, ∀ u ∈ Set.Icc (t' - r) (t' + r),
        γf u = s → u = t' := fun t' ht' =>
      h_local_unique t' (List.mem_cons_of_mem t ht')
    have h_IH_smooth_bound : ∃ m' : ℝ, 0 < m' ∧
        ∀ u ∈ Set.Icc (t + r) 1,
          (∀ t' ∈ rest, u ∉ Set.Ioo (t' - r) (t' + r)) → m' ≤ ‖γf u - s‖ := by
      refine ⟨m, hm_pos, ?_⟩
      intro u hu h_avoid
      have hu_in_a : u ∈ Set.Icc a 1 := by
        refine ⟨?_, hu.2⟩
        linarith [hu.1, h_a_lt_t]
      apply hm_bound u hu_in_a
      intro t' ht' h_in
      rcases List.mem_cons.mp ht' with rfl | h_in_rest
      · linarith [hu.1, h_in.2]
      · exact h_avoid t' h_in_rest h_in
    have hL_rest := IH hrest_sorted (t + r) h_IH_a_lt h_t_plus_r_le_1
      h_IH_a_in_unit h_IH_t_le h_IH_pair h_IH_window_conv h_IH_smooth_bound
      h_IH_t_Ioo h_IH_t_at h_IH_local
    have h_a_lt_t_minus_r : a ≤ t - r := le_of_lt h_a_lt_t
    have h_smooth_left : ∀ u ∈ Set.Icc a (t - r), m ≤ ‖γf u - s‖ := by
      intro u hu
      apply hm_bound u ⟨hu.1, by linarith [hu.2, h_t_le_1mr_t]⟩
      intro t' ht' h_in_window
      rcases List.mem_cons.mp ht' with rfl | h_in_rest
      · linarith [hu.2, h_in_window.1]
      · linarith [hu.2, h_in_window.1, h_rest_window_above t' h_in_rest]
    have h_ne_smooth_left : ∀ u ∈ Set.Icc a (t - r), γf u ≠ s := fun u hu h_eq => by
      have h_bd := h_smooth_left u hu
      rw [h_eq, sub_self, norm_zero] at h_bd; linarith
    have h_a_in_unit_left : Set.Icc a (t - r) ⊆ Set.Icc (0 : ℝ) 1 := fun u hu =>
      ⟨(h_a_in_unit ⟨le_rfl, h_a_le_1⟩).1.trans hu.1,
       by linarith [hu.2, h_t_le_1mr_t]⟩
    set partSet : Set ℝ :=
      (γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) with partSet_def
    have h_partSet_countable : partSet.Countable :=
      γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
    have h_diff_left : ∀ u ∈ Set.Ioo a (t - r) \ partSet,
        HasDerivAt γf (deriv γf u) u := by
      intro u ⟨h_u_in, h_u_off⟩
      have h_u_pos : 0 < u := by
        linarith [(h_a_in_unit ⟨le_rfl, h_a_le_1⟩).1, h_u_in.1]
      have h_u_lt_1 : u < 1 := by linarith [h_u_in.2, h_t_le_1mr_t, hr_pos]
      exact (γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend
        u ⟨h_u_pos, h_u_lt_1⟩ h_u_off).hasDerivAt
    have hγ_continuous : Continuous γf :=
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
    have hγ_cont_left : ContinuousOn γf (Set.Icc a (t - r)) := hγ_continuous.continuousOn
    have h_int_left' : IntervalIntegrable
        (fun u => c * deriv γf u / (γf u - s) ^ k) MeasureTheory.volume a (t - r) :=
      pow_inv_mul_deriv_intervalIntegrable γ c k h_a_lt_t_minus_r
        h_a_in_unit_left h_ne_smooth_left
    have h_FTC_left :
        ∫ u in a..(t - r), c * deriv γf u / (γf u - s) ^ k =
        c * antiderivPow s k (γf (t - r)) - c * antiderivPow s k (γf a) := by
      set F : ℂ → ℂ := fun z => c * antiderivPow s k z
      have h_F_diff_at : ∀ u ∈ Set.Ioo a (t - r) \ partSet,
          HasDerivAt (fun v => F (γf v)) (c * deriv γf u / (γf u - s) ^ k) u := by
        intro u hu
        have h_γu_ne_s : γf u ≠ s := h_ne_smooth_left u (Set.Ioo_subset_Icc_self hu.1)
        have h_F_at : HasDerivAt F (c * (1 / (γf u - s) ^ k)) (γf u) :=
          (hasDerivAt_antiderivative_pow_inv_complex hk h_γu_ne_s).const_mul c
        have h_chain := h_F_at.comp u (h_diff_left u hu)
        rw [show c * (1 / (γf u - s) ^ k) * deriv γf u =
            c * deriv γf u / (γf u - s) ^ k from by ring] at h_chain
        exact h_chain
      have h_Fγ_cont : ContinuousOn (fun v => F (γf v)) (Set.Icc a (t - r)) := fun u hu =>
        (((hasDerivAt_antiderivative_pow_inv_complex hk
          (h_ne_smooth_left u hu)).continuousAt).const_mul
          c).comp_continuousWithinAt (hγ_cont_left u hu)
      exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (fun v => F (γf v)) (fun u => c * deriv γf u / (γf u - s) ^ k)
        h_a_lt_t_minus_r h_partSet_countable h_Fγ_cont h_F_diff_at h_int_left'
    have h_smooth_left_const : (fun ε : ℝ =>
        ∫ u in a..(t - r), cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
        =ᶠ[𝓝[>] (0 : ℝ)]
        (fun _ => c * antiderivPow s k (γf (t - r)) - c * antiderivPow s k (γf a)) := by
      filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
      have hε_pos : 0 < ε := hε.1
      have hε_lt_m : ε < m := hε.2
      calc ∫ u in a..(t - r), cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u
          = ∫ u in a..(t - r), c * deriv γf u / (γf u - s) ^ k := by
            apply intervalIntegral.integral_congr
            intro u hu
            rw [Set.uIcc_of_le h_a_lt_t_minus_r] at hu
            have h_norm_gt : ε < ‖γf u - s‖ := lt_of_lt_of_le hε_lt_m (h_smooth_left u hu)
            simp only [cpvIntegrand, h_norm_gt, ite_true]
            ring
        _ = _ := h_FTC_left
    have h_t_minus_r_lt_t_plus_r : t - r ≤ t + r := by linarith
    have h_split_eq : (fun ε : ℝ =>
        ∫ u in a..1, cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
        =ᶠ[𝓝[>] (0 : ℝ)]
        (fun ε =>
          (∫ u in a..(t - r), cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u) +
          (∫ u in (t - r)..(t + r), cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u) +
          (∫ u in (t + r)..1, cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)) := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε_pos : 0 < ε)
      have hk_pos : 1 ≤ k := by omega
      have h_in_unit_a_tr : Set.Icc a (t - r) ⊆ Set.Icc (0 : ℝ) 1 := h_a_in_unit_left
      have h_cpv_int_left : IntervalIntegrable
          (fun u => cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
          MeasureTheory.volume a (t - r) :=
        cpvIntegrand_higherOrder_intervalIntegrable γ c k hk_pos hε_pos
          h_a_lt_t_minus_r h_in_unit_a_tr
      have h_t_minus_r_ge_0 : 0 ≤ t - r := by
        linarith [(h_a_in_unit ⟨le_refl _, h_a_le_1⟩).1, h_a_lt_t]
      have h_in_unit_mid : Set.Icc (t - r) (t + r) ⊆ Set.Icc (0 : ℝ) 1 :=
        Set.Icc_subset_Icc h_t_minus_r_ge_0 h_t_plus_r_le_1
      have h_cpv_int_mid : IntervalIntegrable
          (fun u => cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
          MeasureTheory.volume (t - r) (t + r) :=
        cpvIntegrand_higherOrder_intervalIntegrable γ c k hk_pos hε_pos
          h_t_minus_r_lt_t_plus_r h_in_unit_mid
      have h_cpv_int_right : IntervalIntegrable
          (fun u => cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
          MeasureTheory.volume (t + r) 1 :=
        cpvIntegrand_higherOrder_intervalIntegrable γ c k hk_pos hε_pos
          h_t_plus_r_le_1 h_IH_a_in_unit
      have h_split1 := intervalIntegral.integral_add_adjacent_intervals
        h_cpv_int_left h_cpv_int_mid
      have h_split2 := intervalIntegral.integral_add_adjacent_intervals
        (h_cpv_int_left.trans h_cpv_int_mid) h_cpv_int_right
      rw [← h_split2, ← h_split1]
    refine Tendsto.congr' h_split_eq.symm ?_
    have h_tendsto_left : Tendsto (fun ε : ℝ =>
        ∫ u in a..(t - r), cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
        (𝓝[>] (0 : ℝ))
        (𝓝 (c * antiderivPow s k (γf (t - r)) - c * antiderivPow s k (γf a))) :=
      Tendsto.congr' h_smooth_left_const.symm tendsto_const_nhds
    have h_combined : Tendsto (fun ε =>
        (∫ u in a..(t - r), cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u) +
        (∫ u in (t - r)..(t + r), cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u) +
        (∫ u in (t + r)..1, cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((c * antiderivPow s k (γf (t - r)) - c * antiderivPow s k (γf a)) +
            c * (antiderivPow s k (γf (t + r)) - antiderivPow s k (γf (t - r))) +
            c * (antiderivPow s k (γf 1) - antiderivPow s k (γf (t + r))))) :=
      ((h_tendsto_left.add h_lam_t).add hL_rest)
    have h_target_simplify :
        (c * antiderivPow s k (γf (t - r)) - c * antiderivPow s k (γf a)) +
            c * (antiderivPow s k (γf (t + r)) - antiderivPow s k (γf (t - r))) +
            c * (antiderivPow s k (γf 1) - antiderivPow s k (γf (t + r))) =
        c * (antiderivPow s k (γf 1) - antiderivPow s k (γf a)) := by ring
    rw [← h_target_simplify]
    exact h_combined

/-- **Per-crossing higher-order window convergence (corner-friendly form).**

Generalises `perCrossing_higherOrder_window_integral_tendsto` to accept
separate one-sided derivative limits `L_+`, `L_-` (possibly at a partition
point) plus the general-angle form of `h_B`. The per-window cutoff integral
converges to the FTC-difference at the window endpoints, as in the smooth
case. -/
private theorem perCrossing_higherOrder_window_integral_tendsto_corner
    (γ : ClosedPwC1Immersion x) {s : ℂ} {t_i : ℝ}
    (ht_i_Ioo : t_i ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t_i = s)
    {r : ℝ} (hr_pos : 0 < r)
    (h_window_Icc : Set.Icc (t_i - r) (t_i + r) ⊆ Set.Icc (0 : ℝ) 1)
    (h_local_unique_r : ∀ t ∈ Set.Icc (t_i - r) (t_i + r),
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t = t_i)
    {L_minus L_plus : ℂ} (hL_minus_ne : L_minus ≠ 0) (hL_plus_ne : L_plus ≠ 0)
    (hL_right : Tendsto
      (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
      (𝓝[>] t_i) (𝓝 L_plus))
    (hL_left : Tendsto
      (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
      (𝓝[<] t_i) (𝓝 L_minus))
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_flat : IsFlatOfOrder
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t_i n)
    (h_B :
      (L_plus / (↑‖L_plus‖ : ℂ)) ^ (k - 1) =
      ((-L_minus) / (↑‖L_minus‖ : ℂ)) ^ (k - 1))
    (c : ℂ) :
    Tendsto (fun ε : ℝ =>
        ∫ u in (t_i - r)..(t_i + r),
          cpvIntegrand (fun z => c / (z - s) ^ k)
            γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend s ε u)
      (𝓝[>] (0 : ℝ))
      (𝓝 (c * (antiderivPow s k
        (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t_i + r)) -
          antiderivPow s k
            (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend (t_i - r))))) := by
  classical
  set f : ℝ → ℂ := fun t =>
    γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
  have hγ_continuous : Continuous f :=
    γ.toPwC1Immersion.toPiecewiseC1Path.continuous
  have hγ_cont_t_i : ContinuousAt f t_i := hγ_continuous.continuousAt
  have hγ_diff_right : ∀ᶠ t in 𝓝[>] t_i, DifferentiableAt ℝ f t :=
    eventually_differentiable_right γ ht_i_Ioo
  have hγ_diff_left : ∀ᶠ t in 𝓝[<] t_i, DifferentiableAt ℝ f t :=
    eventually_differentiable_left γ ht_i_Ioo
  obtain ⟨r_R, hr_R_pos, hγ_mono_at_radius⟩ :=
    norm_sub_strictMonoOn_right h_at hL_plus_ne hL_right hγ_cont_t_i hγ_diff_right
  obtain ⟨r_L, hr_L_pos, hγ_anti_at_radius⟩ :=
    norm_sub_strictAntiOn_left h_at hL_minus_ne hL_left hγ_cont_t_i hγ_diff_left
  set r_mono : ℝ := min r (min r_R r_L) / 2
  have hr_mono_pos : 0 < r_mono :=
    half_pos (lt_min hr_pos (lt_min hr_R_pos hr_L_pos))
  have h_min_le : r_mono ≤ min r (min r_R r_L) :=
    half_le_self (lt_min hr_pos (lt_min hr_R_pos hr_L_pos)).le
  have hr_mono_le_r : r_mono ≤ r := h_min_le.trans (min_le_left _ _)
  have hr_mono_le_r_R : r_mono ≤ r_R :=
    (h_min_le.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hr_mono_le_r_L : r_mono ≤ r_L :=
    (h_min_le.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hγ_mono : StrictMonoOn (fun t => ‖f t - s‖)
      (Set.Icc t_i (t_i + r_mono)) :=
    hγ_mono_at_radius.mono (Set.Icc_subset_Icc le_rfl (by linarith))
  have hγ_anti : StrictAntiOn (fun t => ‖f t - s‖)
      (Set.Icc (t_i - r_mono) t_i) :=
    hγ_anti_at_radius.mono (Set.Icc_subset_Icc (by linarith) le_rfl)
  have hγ_cont_right_delta : ContinuousOn f
      (Set.Icc t_i (t_i + r_mono)) := hγ_continuous.continuousOn
  have hγ_cont_left_delta : ContinuousOn f
      (Set.Icc (t_i - r_mono) t_i) := hγ_continuous.continuousOn
  have h_ft_i : f t_i = s := h_at
  have h_leave_right : ∀ t ∈ Set.Ioc t_i (t_i + r_mono), f t ≠ s := by
    intro t ht heq
    have h_strict' : ‖f t_i - s‖ < ‖f t - s‖ :=
      hγ_mono ⟨le_rfl, by linarith [hr_mono_pos]⟩ ⟨ht.1.le, ht.2⟩ ht.1
    rw [h_ft_i, heq] at h_strict'; simp at h_strict'
  have h_leave_left : ∀ t ∈ Set.Ico (t_i - r_mono) t_i, f t ≠ s := by
    intro t ht heq
    have h_strict' : ‖f t_i - s‖ < ‖f t - s‖ :=
      hγ_anti ⟨ht.1, ht.2.le⟩ ⟨by linarith [hr_mono_pos], le_rfl⟩ ht.2
    rw [h_ft_i, heq] at h_strict'; simp at h_strict'
  have h_deriv_right : HasDerivWithinAt f L_plus (Set.Ioi t_i) t_i :=
    hasDerivWithinAt_Ioi_of_tendsto hγ_cont_t_i hγ_diff_right hL_right
  have h_deriv_left : HasDerivWithinAt f L_minus (Set.Iio t_i) t_i :=
    hasDerivWithinAt_Iio_of_tendsto hγ_cont_t_i hγ_diff_left hL_left
  set t_eps_plus := LeanModularForms.firstExitTimeRight f t_i r_mono s
  set t_eps_minus := LeanModularForms.firstExitTimeLeft f t_i r_mono s
  have h_plus_to : Tendsto t_eps_plus (𝓝[>] (0 : ℝ)) (𝓝[>] t_i) :=
    LeanModularForms.firstExitTimeRight_tendsto_t₀ hr_mono_pos
      hγ_cont_right_delta h_at h_leave_right
  have h_plus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖f (t_eps_plus ε) - s‖ = ε :=
    LeanModularForms.firstExitTimeRight_radius_eventually hr_mono_pos
      hγ_cont_right_delta h_at h_leave_right
  have h_minus_to : Tendsto t_eps_minus (𝓝[>] (0 : ℝ)) (𝓝[<] t_i) :=
    LeanModularForms.firstExitTimeLeft_tendsto_t₀ hr_mono_pos
      hγ_cont_left_delta h_at h_leave_left
  have h_minus_radius : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖f (t_eps_minus ε) - s‖ = ε :=
    LeanModularForms.firstExitTimeLeft_radius_eventually hr_mono_pos
      hγ_cont_left_delta h_at h_leave_left
  have h_F_curve_diff :=
    F_curve_diff_tendsto_zero_under_conditionB
      (γ := f) (t₀ := t_i) (s := s) (L_minus := L_minus) (L_plus := L_plus)
      (n := n) (k := k) h_flat hL_minus_ne hL_plus_ne h_deriv_right h_deriv_left
      hL_right hL_left h_at hk hkn hn1 h_B
      t_eps_plus t_eps_minus h_plus_to h_plus_radius h_minus_to h_minus_radius
  have h_F_curve_diff_cx :
      Tendsto (fun ε =>
        antiderivPow s k (f (t_eps_minus ε)) -
          antiderivPow s k (f (t_eps_plus ε)))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact h_F_curve_diff
  have h_t_minus_in_Ioo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      t_eps_minus ε ∈ Set.Ioo (t_i - r_mono) t_i := by
    rw [Filter.tendsto_def] at h_minus_to
    exact h_minus_to (Set.Ioo (t_i - r_mono) t_i)
      (Ioo_mem_nhdsLT (by linarith [hr_mono_pos]))
  have h_t_plus_in_Ioo : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      t_eps_plus ε ∈ Set.Ioo t_i (t_i + r_mono) := by
    rw [Filter.tendsto_def] at h_plus_to
    exact h_plus_to (Set.Ioo t_i (t_i + r_mono))
      (Ioo_mem_nhdsGT (by linarith [hr_mono_pos]))
  have h_t_minus_in_window : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      t_eps_minus ε ∈ Set.Ioo (t_i - r) t_i := by
    filter_upwards [h_t_minus_in_Ioo] with ε hε
    exact ⟨by linarith [hε.1], hε.2⟩
  have h_t_plus_in_window : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      t_eps_plus ε ∈ Set.Ioo t_i (t_i + r) := by
    filter_upwards [h_t_plus_in_Ioo] with ε hε
    exact ⟨hε.1, by linarith [hε.2]⟩
  set partSet : Set ℝ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.partition : Set ℝ) with partSet_def
  have h_partSet_countable : partSet.Countable :=
    γ.toPwC1Immersion.toPiecewiseC1Path.partition.finite_toSet.countable
  obtain ⟨m_avoid, hm_avoid_pos, h_far_left, h_far_right⟩ :=
    multi_pole_local_far_bound (γ := γ) (s := s) (t_i := t_i) (r := r) hr_pos
      h_local_unique_r (r' := r_mono) hr_mono_pos hr_mono_le_r
  have h_eps_lt_m_avoid : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < m_avoid := by
    filter_upwards [Ioo_mem_nhdsGT hm_avoid_pos] with ε hε
    exact hε.2
  have h_window_le_unit : Set.Icc (t_i - r) (t_i + r) ⊆ Set.Icc (0 : ℝ) 1 :=
    h_window_Icc
  have ht_i_r_pos : 0 ≤ t_i - r := (h_window_le_unit ⟨le_rfl, by linarith⟩).1
  have ht_i_r_le_1 : t_i + r ≤ 1 := (h_window_le_unit ⟨by linarith, le_rfl⟩).2
  have h_eventually_eq : (fun ε : ℝ =>
        ∫ u in (t_i - r)..(t_i + r),
          cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => c * (antiderivPow s k (f (t_i + r)) - antiderivPow s k (f (t_i - r))) +
        c * (antiderivPow s k (f (t_eps_minus ε)) -
              antiderivPow s k (f (t_eps_plus ε)))) := by
    filter_upwards [h_t_minus_in_window, h_t_plus_in_window, h_minus_radius,
      h_plus_radius, h_t_minus_in_Ioo, h_t_plus_in_Ioo, h_eps_lt_m_avoid,
      self_mem_nhdsWithin] with ε htmw htpw hmr hpr htm_ioo htp_ioo hε_lt_m_avoid
      (hε_pos : 0 < ε)
    have htme := htmw
    have htpe := htpw
    have h_lb : t_i - r ≤ t_eps_minus ε := htme.1.le
    have h_ub : t_eps_plus ε ≤ t_i + r := htpe.2.le
    have h_mid : t_eps_minus ε ≤ t_eps_plus ε := by
      have h1 : t_eps_minus ε < t_i := htme.2
      have h2 : t_i < t_eps_plus ε := htpe.1
      linarith
    have h_in_unit_left : Set.Icc (t_i - r) (t_eps_minus ε) ⊆ Set.Icc (0 : ℝ) 1 := fun u hu =>
      ⟨by linarith [hu.1, ht_i_r_pos],
       by linarith [hu.2, htme.2, ht_i_r_le_1, hr_pos]⟩
    have h_in_unit_right : Set.Icc (t_eps_plus ε) (t_i + r) ⊆ Set.Icc (0 : ℝ) 1 := fun u hu =>
      ⟨by linarith [htpe.1, hu.1, ht_i_r_pos, hr_pos],
       by linarith [hu.2, ht_i_r_le_1]⟩
    have h_in_unit_mid : Set.Icc (t_eps_minus ε) (t_eps_plus ε) ⊆ Set.Icc (0 : ℝ) 1 := fun u hu =>
      ⟨by linarith [hu.1, htme.1, ht_i_r_pos],
       by linarith [hu.2, htpe.2, ht_i_r_le_1]⟩
    have hk_pos : 1 ≤ k := by omega
    have h_int_left : IntervalIntegrable
        (fun u => cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u)
        MeasureTheory.volume (t_i - r) (t_eps_minus ε) :=
      cpvIntegrand_higherOrder_intervalIntegrable γ c k hk_pos hε_pos h_lb h_in_unit_left
    have h_int_mid : IntervalIntegrable
        (fun u => cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u)
        MeasureTheory.volume (t_eps_minus ε) (t_eps_plus ε) :=
      cpvIntegrand_higherOrder_intervalIntegrable γ c k hk_pos hε_pos h_mid h_in_unit_mid
    have h_int_right : IntervalIntegrable
        (fun u => cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u)
        MeasureTheory.volume (t_eps_plus ε) (t_i + r) :=
      cpvIntegrand_higherOrder_intervalIntegrable γ c k hk_pos hε_pos h_ub h_in_unit_right
    have h_split1 := intervalIntegral.integral_add_adjacent_intervals
      h_int_left h_int_mid
    have h_split2 := intervalIntegral.integral_add_adjacent_intervals
      (h_int_left.trans h_int_mid) h_int_right
    have h_mid_zero : ∫ u in (t_eps_minus ε)..(t_eps_plus ε),
        cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u = 0 := by
      have h_norm_le_on_Ioo : ∀ u ∈ Set.Ioo (t_eps_minus ε) (t_eps_plus ε),
          ‖f u - s‖ ≤ ε := by
        intro u hu_strict
        by_cases h_le_t_i : u ≤ t_i
        · have h_u_ge : t_i - r_mono ≤ u := by linarith [htm_ioo.1, hu_strict.1]
          have h_u_in : u ∈ Set.Icc (t_i - r_mono) t_i := ⟨h_u_ge, h_le_t_i⟩
          have htme_in : t_eps_minus ε ∈ Set.Icc (t_i - r_mono) t_i :=
            ⟨htm_ioo.1.le, htm_ioo.2.le⟩
          by_cases h_eq_t_i : u = t_i
          · have h_ft_i : f t_i = s := h_at
            rw [h_eq_t_i, h_ft_i, sub_self, norm_zero]
            exact hε_pos.le
          · push Not at h_eq_t_i
            have h_anti_apply := hγ_anti htme_in h_u_in hu_strict.1
            have h_anti_apply' : ‖f u - s‖ < ‖f (t_eps_minus ε) - s‖ := h_anti_apply
            rw [hmr] at h_anti_apply'
            exact h_anti_apply'.le
        · push Not at h_le_t_i
          have h_u_le : u ≤ t_i + r_mono := by linarith [htp_ioo.2, hu_strict.2]
          have h_u_in : u ∈ Set.Icc t_i (t_i + r_mono) := ⟨h_le_t_i.le, h_u_le⟩
          have htpe_in : t_eps_plus ε ∈ Set.Icc t_i (t_i + r_mono) :=
            ⟨htp_ioo.1.le, htp_ioo.2.le⟩
          have h_mono_apply := hγ_mono h_u_in htpe_in hu_strict.2
          have h_mono_apply' : ‖f u - s‖ < ‖f (t_eps_plus ε) - s‖ := h_mono_apply
          rw [hpr] at h_mono_apply'
          exact h_mono_apply'.le
      have h_eq : (fun u =>
          cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u) =ᶠ[ae
          (MeasureTheory.volume.restrict
            (Set.uIoc (t_eps_minus ε) (t_eps_plus ε)))] (fun _ => 0) := by
        rw [Set.uIoc_of_le h_mid]
        have h_singleton_compl_ae : ({t_eps_plus ε}ᶜ : Set ℝ) ∈
            MeasureTheory.ae (MeasureTheory.volume.restrict
              (Set.Ioc (t_eps_minus ε) (t_eps_plus ε))) := by
          refine MeasureTheory.compl_mem_ae_iff.mpr ?_
          rw [MeasureTheory.Measure.restrict_apply (measurableSet_singleton _)]
          exact MeasureTheory.measure_mono_null Set.inter_subset_left
            (MeasureTheory.measure_singleton _)
        filter_upwards [self_mem_ae_restrict measurableSet_Ioc, h_singleton_compl_ae]
          with u hu hu_ne_endpt
        have h_u_lt : u < t_eps_plus ε := lt_of_le_of_ne hu.2 hu_ne_endpt
        have hu_strict : u ∈ Set.Ioo (t_eps_minus ε) (t_eps_plus ε) :=
          ⟨hu.1, h_u_lt⟩
        have h_norm_le : ‖f u - s‖ ≤ ε := h_norm_le_on_Ioo u hu_strict
        simp only [cpvIntegrand, if_neg h_norm_le.not_gt]
      calc ∫ u in (t_eps_minus ε)..(t_eps_plus ε),
            cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u
          = ∫ _u in (t_eps_minus ε)..(t_eps_plus ε), (0 : ℂ) :=
            intervalIntegral.integral_congr_ae_restrict h_eq
        _ = 0 := by simp
    have h_left_eq : ∫ u in (t_i - r)..(t_eps_minus ε),
        cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u =
        ∫ u in (t_i - r)..(t_eps_minus ε),
          c * deriv f u / (f u - s) ^ k := by
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le h_lb]
      have h_singleton_meas_zero :
          MeasureTheory.volume ({t_eps_minus ε} : Set ℝ) = 0 :=
        MeasureTheory.measure_singleton _
      have h_singleton_compl_ae : ({t_eps_minus ε}ᶜ : Set ℝ) ∈
          (MeasureTheory.ae MeasureTheory.volume) :=
        MeasureTheory.compl_mem_ae_iff.mpr h_singleton_meas_zero
      filter_upwards [h_singleton_compl_ae] with u hu_ne_endpt hu
      have h_u_ne_endpt : u ≠ t_eps_minus ε := hu_ne_endpt
      have h_u_lt_t_minus : u < t_eps_minus ε := lt_of_le_of_ne hu.2 h_u_ne_endpt
      have h_norm_gt : ε < ‖f u - s‖ := by
        by_cases h_lt_t_i_minus_r_mono : u < t_i - r_mono
        · have h_u_in : u ∈ Set.Icc (t_i - r) (t_i - r_mono) :=
            ⟨hu.1.le, h_lt_t_i_minus_r_mono.le⟩
          exact lt_of_lt_of_le hε_lt_m_avoid (h_far_left u h_u_in)
        · push Not at h_lt_t_i_minus_r_mono
          have h_u_lt_t_i : u < t_i := lt_of_lt_of_le h_u_lt_t_minus htme.2.le
          have h_u_in : u ∈ Set.Icc (t_i - r_mono) t_i :=
            ⟨h_lt_t_i_minus_r_mono, h_u_lt_t_i.le⟩
          have htme_in : t_eps_minus ε ∈ Set.Icc (t_i - r_mono) t_i :=
            ⟨htm_ioo.1.le, htm_ioo.2.le⟩
          have h_anti_apply := hγ_anti h_u_in htme_in h_u_lt_t_minus
          have h_anti_apply' : ‖f (t_eps_minus ε) - s‖ < ‖f u - s‖ := h_anti_apply
          rw [hmr] at h_anti_apply'
          exact h_anti_apply'
      simp only [cpvIntegrand, h_norm_gt, ite_true]
      ring
    have h_right_eq : ∫ u in (t_eps_plus ε)..(t_i + r),
        cpvIntegrand (fun z => c / (z - s) ^ k) f s ε u =
        ∫ u in (t_eps_plus ε)..(t_i + r),
          c * deriv f u / (f u - s) ^ k := by
      apply intervalIntegral.integral_congr_ae
      rw [Set.uIoc_of_le h_ub]
      filter_upwards with u hu
      have h_norm_gt : ε < ‖f u - s‖ := by
        by_cases h_lt_t_i_plus_r_mono : u > t_i + r_mono
        · have h_u_in : u ∈ Set.Icc (t_i + r_mono) (t_i + r) :=
            ⟨h_lt_t_i_plus_r_mono.le, hu.2⟩
          exact lt_of_lt_of_le hε_lt_m_avoid (h_far_right u h_u_in)
        · push Not at h_lt_t_i_plus_r_mono
          have h_t_i_lt_u : t_i < u := lt_trans htpe.1 hu.1
          have h_u_in : u ∈ Set.Icc t_i (t_i + r_mono) :=
            ⟨h_t_i_lt_u.le, h_lt_t_i_plus_r_mono⟩
          have htpe_in : t_eps_plus ε ∈ Set.Icc t_i (t_i + r_mono) :=
            ⟨htp_ioo.1.le, htp_ioo.2.le⟩
          have h_mono_apply := hγ_mono htpe_in h_u_in hu.1
          have h_mono_apply' : ‖f (t_eps_plus ε) - s‖ < ‖f u - s‖ := h_mono_apply
          rw [hpr] at h_mono_apply'
          exact h_mono_apply'
      simp only [cpvIntegrand, h_norm_gt, ite_true]
      ring
    have h_avoids_left : ∀ u ∈ Set.Icc (t_i - r) (t_eps_minus ε), f u ≠ s := fun u hu h_eq => by
      have h_u_lt_t_i : u < t_i := lt_of_le_of_lt hu.2 htme.2
      linarith [h_local_unique_r u ⟨hu.1, by linarith [h_u_lt_t_i, hr_pos]⟩ h_eq]
    have h_avoids_right : ∀ u ∈ Set.Icc (t_eps_plus ε) (t_i + r), f u ≠ s := fun u hu h_eq => by
      have h_t_i_lt_u : t_i < u := lt_of_lt_of_le htpe.1 hu.1
      linarith [h_local_unique_r u ⟨by linarith [h_t_i_lt_u, hr_pos], hu.2⟩ h_eq]
    have h_diff_left : ∀ u ∈ Set.Ioo (t_i - r) (t_eps_minus ε) \ partSet,
        HasDerivAt f (deriv f u) u := by
      intro u hu
      obtain ⟨h_u_in, h_u_off⟩ := hu
      have h_u_lt_t_i : u < t_i := lt_trans h_u_in.2 htme.2
      have h_u_pos : 0 < u := lt_of_le_of_lt ht_i_r_pos h_u_in.1
      have h_u_lt_1 : u < 1 := by linarith [ht_i_r_le_1, h_u_lt_t_i, ht_i_Ioo.2, hr_pos]
      have h_u_in_Ioo01 : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨h_u_pos, h_u_lt_1⟩
      have h_diff_at : DifferentiableAt ℝ f u :=
        γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend u h_u_in_Ioo01 h_u_off
      exact h_diff_at.hasDerivAt
    have h_diff_right : ∀ u ∈ Set.Ioo (t_eps_plus ε) (t_i + r) \ partSet,
        HasDerivAt f (deriv f u) u := by
      intro u hu
      obtain ⟨h_u_in, h_u_off⟩ := hu
      have h_t_i_lt_u : t_i < u := lt_trans htpe.1 h_u_in.1
      have h_u_pos : 0 < u := by linarith [ht_i_Ioo.1, h_t_i_lt_u]
      have h_u_lt_1 : u < 1 := lt_of_lt_of_le h_u_in.2 ht_i_r_le_1
      have h_u_in_Ioo01 : u ∈ Set.Ioo (0 : ℝ) 1 := ⟨h_u_pos, h_u_lt_1⟩
      have h_diff_at : DifferentiableAt ℝ f u :=
        γ.toPwC1Immersion.toPiecewiseC1Path.differentiable_off_extend u h_u_in_Ioo01 h_u_off
      exact h_diff_at.hasDerivAt
    have hγ_cont_window : ContinuousOn f
        (Set.Icc (t_i - r) (t_eps_minus ε)) := hγ_continuous.continuousOn
    have hγ_cont_window_right : ContinuousOn f
        (Set.Icc (t_eps_plus ε) (t_i + r)) := hγ_continuous.continuousOn
    have h_int_left' : IntervalIntegrable
        (fun u => c * deriv f u / (f u - s) ^ k) MeasureTheory.volume
        (t_i - r) (t_eps_minus ε) :=
      pow_inv_mul_deriv_intervalIntegrable γ c k h_lb h_in_unit_left h_avoids_left
    have h_int_right' : IntervalIntegrable
        (fun u => c * deriv f u / (f u - s) ^ k) MeasureTheory.volume
        (t_eps_plus ε) (t_i + r) :=
      pow_inv_mul_deriv_intervalIntegrable γ c k h_ub h_in_unit_right h_avoids_right
    have h_FTC_left :
        ∫ u in (t_i - r)..(t_eps_minus ε), c * deriv f u / (f u - s) ^ k =
        c * antiderivPow s k (f (t_eps_minus ε)) -
        c * antiderivPow s k (f (t_i - r)) := by
      set F : ℂ → ℂ := fun z => c * antiderivPow s k z
      have h_F_diff_at : ∀ u ∈ Set.Ioo (t_i - r) (t_eps_minus ε) \ partSet,
          HasDerivAt (fun v => F (f v)) (c * deriv f u / (f u - s) ^ k) u := by
        intro u hu
        have h_γu_ne_s : f u ≠ s := h_avoids_left u (Set.Ioo_subset_Icc_self hu.1)
        have h_F_at : HasDerivAt F (c * (1 / (f u - s) ^ k)) (f u) :=
          (hasDerivAt_antiderivative_pow_inv_complex hk h_γu_ne_s).const_mul c
        have h_chain := h_F_at.comp u (h_diff_left u hu)
        rw [show c * (1 / (f u - s) ^ k) * deriv f u =
            c * deriv f u / (f u - s) ^ k from by ring] at h_chain
        exact h_chain
      have h_Fγ_cont : ContinuousOn (fun v => F (f v))
          (Set.Icc (t_i - r) (t_eps_minus ε)) := fun u hu =>
        (((hasDerivAt_antiderivative_pow_inv_complex hk
          (h_avoids_left u hu)).continuousAt).const_mul
          c).comp_continuousWithinAt (hγ_cont_window u hu)
      exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (fun v => F (f v)) (fun u => c * deriv f u / (f u - s) ^ k) h_lb
        h_partSet_countable h_Fγ_cont h_F_diff_at h_int_left'
    have h_FTC_right :
        ∫ u in (t_eps_plus ε)..(t_i + r), c * deriv f u / (f u - s) ^ k =
        c * antiderivPow s k (f (t_i + r)) -
        c * antiderivPow s k (f (t_eps_plus ε)) := by
      set F : ℂ → ℂ := fun z => c * antiderivPow s k z
      have h_F_diff_at : ∀ u ∈ Set.Ioo (t_eps_plus ε) (t_i + r) \ partSet,
          HasDerivAt (fun v => F (f v)) (c * deriv f u / (f u - s) ^ k) u := by
        intro u hu
        have h_γu_ne_s : f u ≠ s := h_avoids_right u (Set.Ioo_subset_Icc_self hu.1)
        have h_F_at : HasDerivAt F (c * (1 / (f u - s) ^ k)) (f u) :=
          (hasDerivAt_antiderivative_pow_inv_complex hk h_γu_ne_s).const_mul c
        have h_chain := h_F_at.comp u (h_diff_right u hu)
        rw [show c * (1 / (f u - s) ^ k) * deriv f u =
            c * deriv f u / (f u - s) ^ k from by ring] at h_chain
        exact h_chain
      have h_Fγ_cont : ContinuousOn (fun v => F (f v))
          (Set.Icc (t_eps_plus ε) (t_i + r)) := fun u hu =>
        (((hasDerivAt_antiderivative_pow_inv_complex hk
          (h_avoids_right u hu)).continuousAt).const_mul
          c).comp_continuousWithinAt (hγ_cont_window_right u hu)
      exact MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (fun v => F (f v)) (fun u => c * deriv f u / (f u - s) ^ k) h_ub
        h_partSet_countable h_Fγ_cont h_F_diff_at h_int_right'
    rw [← h_split2, ← h_split1, h_mid_zero, add_zero, h_left_eq, h_right_eq,
      h_FTC_left, h_FTC_right]
    ring
  change Tendsto _ (𝓝[>] (0 : ℝ))
    (𝓝 (c * (antiderivPow s k (f (t_i + r)) - antiderivPow s k (f (t_i - r)))))
  refine Tendsto.congr' h_eventually_eq.symm ?_
  have h_const_part : Tendsto (fun _ : ℝ =>
      c * (antiderivPow s k (f (t_i + r)) - antiderivPow s k (f (t_i - r))))
      (𝓝[>] (0 : ℝ))
      (𝓝 (c * (antiderivPow s k (f (t_i + r)) - antiderivPow s k (f (t_i - r))))) :=
    tendsto_const_nhds
  have h_var_part : Tendsto (fun ε =>
      c * (antiderivPow s k (f (t_eps_minus ε)) -
        antiderivPow s k (f (t_eps_plus ε))))
      (𝓝[>] (0 : ℝ)) (𝓝 (c * 0)) :=
    h_F_curve_diff_cx.const_mul c
  have h_combined := h_const_part.add h_var_part
  have h_lim_eq :
      c * (antiderivPow s k (f (t_i + r)) - antiderivPow s k (f (t_i - r))) + c * 0 =
      c * (antiderivPow s k (f (t_i + r)) - antiderivPow s k (f (t_i - r))) := by
    ring
  rw [h_lim_eq] at h_combined
  exact h_combined

/-- **Corner-friendly multi-crossing higher-order CPV vanishing (T-BR-Y11b).**

Generalises `hasCauchyPVOn_multiCrossing_higherOrder` (T-BR-Y9e) to admit
**corner crossings** (crossings on the legacy partition). For each crossing
`t_i ∈ crossings`, the caller supplies:
* `L_plus t_i`, `L_minus t_i` — one-sided derivative limits (`≠ 0`);
* `hL_right t_i`, `hL_left t_i` — `tendsto` to those limits;
* `h_B t_i` — the general-angle compatibility
  `(L_+/‖L_+‖)^(k-1) = ((-L_-)/‖L_-‖)^(k-1)`.

For smooth crossings (`t_i ∉ partition`), the caller may set
`L_+ = L_- = deriv γ t_i`, recovering the smooth-only form.

The Cauchy principal value of `c / (z - s)^k` along γ vanishes. -/
theorem hasCauchyPVOn_multiCrossing_higherOrder_corner
    {γ : ClosedPwC1Immersion x} {s : ℂ}
    {crossings : Finset ℝ}
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : ∀ t ∈ crossings,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s)
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_flat_at_each : ∀ t₀ ∈ crossings,
      IsFlatOfOrder γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ n)
    (L_plus L_minus : ℝ → ℂ)
    (hL_plus_ne : ∀ t ∈ crossings, L_plus t ≠ 0)
    (hL_minus_ne : ∀ t ∈ crossings, L_minus t ≠ 0)
    (hL_right : ∀ t ∈ crossings,
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] t) (𝓝 (L_plus t)))
    (hL_left : ∀ t ∈ crossings,
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] t) (𝓝 (L_minus t)))
    (h_B : ∀ t ∈ crossings,
      (L_plus t / (↑‖L_plus t‖ : ℂ)) ^ (k - 1) =
      ((-(L_minus t)) / (↑‖L_minus t‖ : ℂ)) ^ (k - 1))
    (c : ℂ) :
    HasCauchyPVOn {s} (fun z => c / (z - s) ^ k)
      γ.toPwC1Immersion.toPiecewiseC1Path 0 := by
  classical
  set γf : ℝ → ℂ :=
    (γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend : ℝ → ℂ) with hγf_def
  by_cases h_empty : crossings = ∅
  · refine hasCauchyPVOn_higherOrder_of_avoids γ hk c fun t ht h_eq => ?_
    exact absurd (h_empty ▸ h_complete t ht h_eq) (Finset.notMem_empty t)
  · have h_nonempty : crossings.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
    have h_per_cross : ∀ t_i ∈ crossings, ∃ rr : ℝ, 0 < rr ∧
        StrictMonoOn (fun t => ‖γf t - s‖) (Set.Icc t_i (t_i + rr)) ∧
        StrictAntiOn (fun t => ‖γf t - s‖) (Set.Icc (t_i - rr) t_i) := by
      intro t_i ht_i_mem
      have ht_i_Ioo : t_i ∈ Set.Ioo (0 : ℝ) 1 := h_Ioo t_i ht_i_mem
      have h_at_t_i : γf t_i = s := h_at t_i ht_i_mem
      have hγ_continuous : Continuous γf :=
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.continuous_extend
      have hγ_cont_at : ContinuousAt γf t_i := hγ_continuous.continuousAt
      have hγ_diff_right : ∀ᶠ t in 𝓝[>] t_i, DifferentiableAt ℝ γf t :=
        eventually_differentiable_right γ ht_i_Ioo
      have hγ_diff_left : ∀ᶠ t in 𝓝[<] t_i, DifferentiableAt ℝ γf t :=
        eventually_differentiable_left γ ht_i_Ioo
      obtain ⟨r_R, hr_R_pos, hmono⟩ :=
        norm_sub_strictMonoOn_right h_at_t_i (hL_plus_ne t_i ht_i_mem)
          (hL_right t_i ht_i_mem) hγ_cont_at hγ_diff_right
      obtain ⟨r_L, hr_L_pos, hanti⟩ :=
        norm_sub_strictAntiOn_left h_at_t_i (hL_minus_ne t_i ht_i_mem)
          (hL_left t_i ht_i_mem) hγ_cont_at hγ_diff_left
      refine ⟨min r_R r_L, lt_min hr_R_pos hr_L_pos, ?_, ?_⟩
      · exact hmono.mono (Set.Icc_subset_Icc le_rfl (by linarith [min_le_left r_R r_L]))
      · exact hanti.mono (Set.Icc_subset_Icc (by linarith [min_le_right r_R r_L]) le_rfl)
    let r_at : ∀ t_i ∈ crossings, ℝ := fun t_i ht_i_mem =>
      (h_per_cross t_i ht_i_mem).choose
    have hr_at_pos : ∀ t_i (ht_i_mem : t_i ∈ crossings), 0 < r_at t_i ht_i_mem :=
      fun t_i ht_i_mem => (h_per_cross t_i ht_i_mem).choose_spec.1
    obtain ⟨r_chord, hr_chord_pos, hr_chord_min⟩ :=
      exists_pos_min_image h_nonempty r_at hr_at_pos
    obtain ⟨r_geom, hr_geom_pos, hr_geom_endpts, hr_geom_pair, hr_geom_part⟩ :=
      multi_pole_common_radius_corner_simple (crossings := crossings)
        (partition := γ.toPwC1Immersion.toPiecewiseC1Path.partition)
        h_nonempty
        (fun t ht => h_Ioo t ht)
    set r : ℝ := min r_chord (r_geom / 2)
    have hr_pos : 0 < r := lt_min hr_chord_pos (by linarith)
    have hr_le_chord : r ≤ r_chord := min_le_left _ _
    have hr_lt_geom : r < r_geom := lt_of_le_of_lt (min_le_right _ _) (by linarith)
    have hr_le_geom : r ≤ r_geom := hr_lt_geom.le
    obtain ⟨h_window_in_unit, h_endpts_r, h_endpts_r_strict, h_pair_r⟩ :=
      multiCrossing_window_data hr_le_geom hr_lt_geom hr_geom_endpts hr_geom_pair
    have h_local_unique_at : ∀ t_i ∈ crossings,
        ∀ t ∈ Set.Icc (t_i - r) (t_i + r), γf t = s → t = t_i := by
      intro t_i ht_i_mem t ht_in h_eq
      apply multi_pole_local_uniqueness γ hr_pos
        h_endpts_r h_pair_r
        (fun t' ht'_in h_eq' => h_complete t' ht'_in h_eq')
        ht_i_mem ht_in h_eq
    obtain ⟨m, hm_pos, h_smooth_bound⟩ :=
      multi_pole_smooth_complement_far_bound (γ := γ) (s := s)
        (crossings := crossings) h_complete (fun _ => r) (fun _ _ => hr_pos)
    have h_per_window_higher_conv : ∀ t_i ∈ crossings,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t_i - r)..(t_i + r),
            cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
          (𝓝[>] (0 : ℝ))
          (𝓝 (c * (antiderivPow s k (γf (t_i + r)) -
            antiderivPow s k (γf (t_i - r))))) := by
      intro t_i ht_i_mem
      have ht_i_Ioo : t_i ∈ Set.Ioo (0 : ℝ) 1 := h_Ioo t_i ht_i_mem
      have h_at_t_i : γf t_i = s := h_at t_i ht_i_mem
      have h_w_unit := h_window_in_unit t_i ht_i_mem
      have h_lu := h_local_unique_at t_i ht_i_mem
      have h_flat_t_i := h_flat_at_each t_i ht_i_mem
      exact perCrossing_higherOrder_window_integral_tendsto_corner
        (γ := γ) (s := s) (t_i := t_i) ht_i_Ioo h_at_t_i hr_pos
        h_w_unit h_lu
        (hL_minus_ne t_i ht_i_mem) (hL_plus_ne t_i ht_i_mem)
        (hL_right t_i ht_i_mem) (hL_left t_i ht_i_mem)
        hk hkn hn1 h_flat_t_i (h_B t_i ht_i_mem) c
    set sortedList : List ℝ := crossings.sort (· ≤ ·)
    have hsorted_lt : sortedList.SortedLT := Finset.sortedLT_sort crossings
    have h_sorted_eq : ∀ t, t ∈ sortedList ↔ t ∈ crossings := by
      intro t; exact Finset.mem_sort _
    have h_sorted_a_lt : ∀ t ∈ sortedList, (0 : ℝ) < t - r := by
      intro t ht
      have ht_in : t ∈ crossings := (h_sorted_eq t).mp ht
      have ⟨ht_gt, _⟩ := h_endpts_r_strict t ht_in
      linarith
    have h_a_le_1 : (0 : ℝ) ≤ 1 := zero_le_one
    have h_a_in_unit : Set.Icc (0 : ℝ) 1 ⊆ Set.Icc (0 : ℝ) 1 := subset_refl _
    have h_sorted_t_le_1mr : ∀ t ∈ sortedList, t ≤ 1 - r := fun t ht =>
      (h_endpts_r t ((h_sorted_eq t).mp ht)).2
    have h_sorted_pair : ∀ t ∈ sortedList, ∀ t' ∈ sortedList, t' ≠ t →
        2 * r < |t - t'| := fun t ht t' ht' hne =>
      h_pair_r t ((h_sorted_eq t).mp ht) t' ((h_sorted_eq t').mp ht') hne
    have h_sorted_Ioo : ∀ t ∈ sortedList, t ∈ Set.Ioo (0 : ℝ) 1 := fun t ht =>
      h_Ioo t ((h_sorted_eq t).mp ht)
    have h_sorted_at : ∀ t ∈ sortedList, γf t = s := fun t ht =>
      h_at t ((h_sorted_eq t).mp ht)
    have h_sorted_local : ∀ t ∈ sortedList, ∀ u ∈ Set.Icc (t - r) (t + r),
        γf u = s → u = t := fun t ht =>
      h_local_unique_at t ((h_sorted_eq t).mp ht)
    have h_sorted_window_conv : ∀ t ∈ sortedList,
        Tendsto (fun ε : ℝ =>
          ∫ u in (t - r)..(t + r),
            cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε u)
          (𝓝[>] (0 : ℝ))
          (𝓝 (c * (antiderivPow s k (γf (t + r)) -
            antiderivPow s k (γf (t - r))))) := fun t ht =>
      h_per_window_higher_conv t ((h_sorted_eq t).mp ht)
    have h_sorted_smooth : ∃ m : ℝ, 0 < m ∧
        ∀ u ∈ Set.Icc (0 : ℝ) 1,
          (∀ t ∈ sortedList, u ∉ Set.Ioo (t - r) (t + r)) → m ≤ ‖γf u - s‖ := by
      refine ⟨m, hm_pos, ?_⟩
      intro u hu h_avoid
      apply h_smooth_bound u hu
      intro t_i ht_i_in
      have ht_i_sort : t_i ∈ sortedList := (h_sorted_eq t_i).mpr ht_i_in
      exact h_avoid t_i ht_i_sort
    have h_recursive : Tendsto (fun ε : ℝ =>
        ∫ t in (0 : ℝ)..1,
          cpvIntegrand (fun z => c / (z - s) ^ k) γf s ε t)
        (𝓝[>] (0 : ℝ))
        (𝓝 (c * (antiderivPow s k (γf 1) - antiderivPow s k (γf 0)))) :=
      cpv_higherOrder_tendsto_along_sorted_corner γ r hr_pos c k hk
        sortedList hsorted_lt (0 : ℝ) h_sorted_a_lt h_a_le_1 h_a_in_unit
        h_sorted_t_le_1mr h_sorted_pair h_sorted_window_conv h_sorted_smooth
        h_sorted_Ioo h_sorted_at h_sorted_local
    have h_closed : γf 0 = γf 1 := closed_immersion_extend_zero_eq_one γ
    have h_target_zero :
        c * (antiderivPow s k (γf 1) - antiderivPow s k (γf 0)) = 0 := by
      rw [← h_closed]
      ring
    rw [h_target_zero] at h_recursive
    unfold HasCauchyPVOn
    refine Tendsto.congr ?_ h_recursive
    intro ε
    apply intervalIntegral.integral_congr
    intro t _
    exact cpvIntegrand_eq_cpvIntegrandOn_singleton

/-- Shared computation for the two `cpv_polarPart_at_multiCrossed_pole_under_condB*`
theorems: the sum `∑ k, L k` over Laurent coefficient slots, where `L k` is
`2πi · w · a k` on `k = 0` and `0` otherwise, equals `2πi · w · residue f s`. -/
private lemma sum_simplePole_only_eq_residue
    {s : ℂ} {S : Finset ℂ} (hs : s ∈ S) {f : ℂ → ℂ} {U : Set ℂ}
    (decomp : PolarPartDecomposition f S U) (w : ℂ) :
    (∑ k : Fin (decomp.order s),
        if k.val = 0 then 2 * ↑Real.pi * I * w * decomp.coeff s k else 0) =
      2 * ↑Real.pi * I * w * residue f s := by
  rw [decomp.residue_eq s hs]
  by_cases h_pos : 0 < decomp.order s
  · rw [dif_pos h_pos, Finset.sum_eq_single (⟨0, h_pos⟩ : Fin (decomp.order s))]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (fun h_eq => hk (Fin.ext h_eq))]
    · exact fun h => absurd (Finset.mem_univ _) h
  · rw [dif_neg h_pos, mul_zero]
    exact Finset.sum_eq_zero fun k _ => absurd k.isLt (by omega)

/-- **Corner-friendly per-pole polar-part multi-crossing CPV (T-BR-Y11b).**

Generalises `cpv_polarPart_at_multiCrossed_pole_under_condB` to admit corner
crossings (no `h_off` per crossing). Takes the simple-pole CPV existence
`h_simple_cpv` as a hypothesis (auto-discharged by smooth-only / single-crossing
machinery for typical callers). -/
theorem cpv_polarPart_at_multiCrossed_pole_under_condB_corner
    {γ : ClosedPwC1Immersion x} {s : ℂ} {S : Finset ℂ} (hs : s ∈ S)
    {f : ℂ → ℂ} {U : Set ℂ}
    (decomp : PolarPartDecomposition f S U)
    {crossings : Finset ℝ}
    (h_Ioo : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1)
    (h_at : ∀ t ∈ crossings,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s)
    (h_complete : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s → t ∈ crossings)
    (h_flat_at_each : ∀ t₀ ∈ crossings,
      IsFlatOfOrder γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀
        (decomp.order s))
    (L_plus L_minus : ℝ → ℂ)
    (hL_plus_ne : ∀ t ∈ crossings, L_plus t ≠ 0)
    (hL_minus_ne : ∀ t ∈ crossings, L_minus t ≠ 0)
    (hL_right : ∀ t ∈ crossings,
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[>] t) (𝓝 (L_plus t)))
    (hL_left : ∀ t ∈ crossings,
      Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
        (𝓝[<] t) (𝓝 (L_minus t)))
    /- Corner-form angle equation per crossing, per coefficient — only required
       when the coefficient is nonzero (matches the inner case-split). -/
    (h_B : ∀ (k : Fin (decomp.order s)), 1 ≤ k.val → decomp.coeff s k ≠ 0 →
      ∀ t ∈ crossings,
        (L_plus t / (↑‖L_plus t‖ : ℂ)) ^ k.val =
        ((-(L_minus t)) / (↑‖L_minus t‖ : ℂ)) ^ k.val)
    /- Simple-pole CPV existence (auto-discharged by single-crossing /
       smooth-only multi-crossing infrastructure for typical callers). -/
    (h_simple_cpv : ∃ L : ℂ, HasCauchyPV (fun z => (z - s)⁻¹)
      γ.toPwC1Immersion.toPiecewiseC1Path s L) :
    HasCauchyPVOn {s} (decomp.polarPart s)
      γ.toPwC1Immersion.toPiecewiseC1Path
      (2 * ↑Real.pi * Complex.I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
        residue f s) := by
  classical
  set γP : PiecewiseC1Path x x := γ.toPwC1Immersion.toPiecewiseC1Path with hγP_def
  set N : ℕ := decomp.order s with hN_def
  set a : Fin N → ℂ := decomp.coeff s
  set w : ℂ := generalizedWindingNumber γP s
  have h_term_int : ∀ k : Fin N, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrand (fun z => a k / (z - s) ^ (k.val + 1))
        γP.toPath.extend s ε t) volume 0 1 := fun k ε hε =>
    (HungerbuhlerWasem.cpvIntegrandOn_singleMonomial_intervalIntegrable
      γ (S := {s}) (Finset.mem_singleton.mpr rfl) (a k) (k.val + 1) hε).congr
      (fun _ _ => (cpvIntegrand_eq_cpvIntegrandOn_singleton (z₀ := s)).symm)
  set L : Fin N → ℂ := fun k =>
    if k.val = 0 then 2 * ↑Real.pi * I * w * a k else 0 with hL_def
  have h_each : ∀ k : Fin N,
      HasCauchyPV (fun z => a k / (z - s) ^ (k.val + 1)) γP s (L k) := by
    intro k
    by_cases hk : k.val = 0
    · have h_pow_one : (k.val + 1 : ℕ) = 1 := by omega
      have h_term_eq :
          (fun z => a k / (z - s) ^ (k.val + 1)) = fun z => a k / (z - s) := by
        funext z; rw [h_pow_one, pow_one]
      have h_L_eq : L k = 2 * ↑Real.pi * I * w * a k := by simp [L, hk]
      rw [h_term_eq, h_L_eq]
      obtain ⟨L_inv, h_inv_cpv⟩ := h_simple_cpv
      have h_w_eq : w = (2 * ↑Real.pi * I)⁻¹ * L_inv :=
        (hasGeneralizedWindingNumber_of_hasCauchyPV h_inv_cpv).eq
      have h_L_inv_eq : L_inv = 2 * ↑Real.pi * I * w := by
        rw [h_w_eq]; field_simp
      have h_scaled : HasCauchyPV (fun z => a k / (z - s)) γP s (a k * L_inv) :=
        HungerbuhlerWasem.hasCauchyPV_simplePole_of_inv (a k) h_inv_cpv
      rw [show 2 * ↑Real.pi * I * w * a k = a k * L_inv by rw [h_L_inv_eq]; ring]
      exact h_scaled
    · have hk_ge_one : 1 ≤ k.val := by omega
      have h_L_eq : L k = (0 : ℂ) := by simp [L, hk]
      rw [h_L_eq]
      by_cases h_zero : a k = 0
      · have h_eq : (fun z => a k / (z - s) ^ (k.val + 1)) = fun _ => (0 : ℂ) := by
          funext z; rw [h_zero, zero_div]
        rw [h_eq]
        exact hasCauchyPV_of_hasCauchyPVOn_singleton
          (HasCauchyPVOn.zero_fun (γ := γP) (S := ({s} : Finset ℂ)))
      · have hk_succ_ge_two : 2 ≤ k.val + 1 := by omega
        have hk_succ_le_N : k.val + 1 ≤ N := k.isLt
        have hN_pos : 1 ≤ N := le_trans (by omega : 1 ≤ k.val + 1) hk_succ_le_N
        have h_B_at_each : ∀ t ∈ crossings,
            (L_plus t / (↑‖L_plus t‖ : ℂ)) ^ ((k.val + 1) - 1) =
            ((-(L_minus t)) / (↑‖L_minus t‖ : ℂ)) ^ ((k.val + 1) - 1) := fun t ht => by
          rw [show (k.val + 1) - 1 = k.val by omega]
          exact h_B k hk_ge_one h_zero t ht
        exact hasCauchyPV_of_hasCauchyPVOn_singleton
          (hasCauchyPVOn_multiCrossing_higherOrder_corner (γ := γ) (s := s)
            (crossings := crossings) h_Ioo h_at h_complete
            (n := N) (k := k.val + 1) hk_succ_ge_two hk_succ_le_N hN_pos
            h_flat_at_each L_plus L_minus hL_plus_ne hL_minus_ne hL_right hL_left
            h_B_at_each (a k))
  have h_sum_cpv : HasCauchyPV
      (fun z => ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) γP s
      (∑ k : Fin N, L k) :=
    HasCauchyPV.finset_sum (Finset.univ : Finset (Fin N))
      (γ := γP) (z₀ := s)
      (f := fun k z => a k / (z - s) ^ (k.val + 1))
      (L := L) (fun k _ => h_each k) (fun k _ => h_term_int k)
  have h_sum_L_eq : (∑ k : Fin N, L k) =
      2 * ↑Real.pi * I * w * residue f s := by
    simp only [hL_def]; exact sum_simplePole_only_eq_residue hs decomp w
  have h_pp_eq : ∀ z, z ≠ s →
      (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) = decomp.polarPart s z :=
    fun z hz => (decomp.polarPart_eq s hs z hz).symm
  have h_cpv_polar : HasCauchyPV (decomp.polarPart s) γP s
      (2 * ↑Real.pi * I * w * residue f s) := by
    rw [← h_sum_L_eq]
    exact HasCauchyPV.congr_pointwise h_sum_cpv h_pp_eq
  exact HasCauchyPV.to_singletonOn h_cpv_polar

/-- **HW3.3 — Corner-friendly clean spec form (T-BR-Y11c).**

The clean version of `residueTheorem_crossing_paper_faithful` admitting
BOTH multi-crossings AND corner crossings, with the eight paper spec
hypotheses plus a basepoint-off residual `hx_notin_S`. The per-pole
simple-pole CPV existence hypothesis is auto-discharged internally via
`hasCauchyPV_inv_sub_multiCrossing_corner`. -/
theorem residueTheorem_crossing_paper_faithful_clean
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    {S : Finset ℂ} (hS_in_U : ↑S ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : ClosedPwC1Immersion x)
    (h_null : IsNullHomologous γ.toPwC1Immersion U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondB : SatisfiesConditionB γ.toPwC1Immersion f S)
    (hCondA : SatisfiesConditionA' γ.toPwC1Immersion f S
      (fun s => (PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
        (γ := γ.toPwC1Immersion) hMero hCondB).order s))
    (hx_notin_S : x ∉ (↑S : Set ℂ)) :
    HasCauchyPVOn S f γ.toPwC1Immersion.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPwC1Immersion.toPiecewiseC1Path s *
          residue f s) := by
  classical
  set decomp : PolarPartDecomposition f S U :=
    PolarPartDecomposition.ofMeromorphicWithCondB hU_open hS_in_U hf
      (γ := γ.toPwC1Immersion) hMero hCondB
  refine residueTheorem_crossing_compositional hU_open hU_ne S hS_in_U f hf γ
    h_null decomp ?_
  intro s hs
  by_cases h_avoid : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      γ.toPwC1Immersion.toPiecewiseC1Path t ≠ s
  · -- Uncrossed: γ avoids s.
    exact cpv_polarPart_at_uncrossed_pole hU_open hU_ne hS_in_U γ h_null decomp s hs
      h_avoid
  · -- Crossed: build crossings via `crossingSet_finite` (uses `hx_notin_S`).
    have h0_ne : (γ.toPwC1Immersion : ℝ → ℂ) 0 ≠ s := by
      simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 0 =
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 from rfl,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_zero]
      exact fun h_eq => hx_notin_S (h_eq ▸ hs)
    have h1_ne : (γ.toPwC1Immersion : ℝ → ℂ) 1 ≠ s := by
      simp only [show (γ.toPwC1Immersion : ℝ → ℂ) 1 =
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1 from rfl,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend_one]
      exact fun h_eq => hx_notin_S (h_eq ▸ hs)
    have hfin : Set.Finite (γ.toPwC1Immersion.crossingSet s) :=
      PwC1Immersion.crossingSet_finite γ.toPwC1Immersion s h0_ne h1_ne
    set crossings : Finset ℝ := hfin.toFinset with hcrossings_def
    have h_Ioo' : ∀ t ∈ crossings, t ∈ Set.Ioo (0 : ℝ) 1 := fun t ht => by
      rw [hcrossings_def, Set.Finite.mem_toFinset] at ht
      refine ⟨lt_of_le_of_ne ht.1.1 fun h_eq => h0_ne ?_,
              lt_of_le_of_ne ht.1.2 fun h_eq => h1_ne ?_⟩
      · rw [← h_eq] at ht; exact ht.2
      · rw [h_eq] at ht; exact ht.2
    have h_at' : ∀ t ∈ crossings,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s := fun t ht => by
      rw [hcrossings_def, Set.Finite.mem_toFinset] at ht; exact ht.2
    have h_complete' : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t = s →
          t ∈ crossings := fun t ht h_eq => by
      rw [hcrossings_def, Set.Finite.mem_toFinset]; exact ⟨ht, h_eq⟩
    have h_flat_at_each : ∀ t₀ ∈ crossings,
        IsFlatOfOrder γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀
          (decomp.order s) := fun t₀ ht₀ =>
      hCondA s hs t₀ (Ioo_subset_Icc_self (h_Ioo' t₀ ht₀)) (h_at' t₀ ht₀) (h_Ioo' t₀ ht₀)
    let L_plus : ℝ → ℂ := fun t =>
      if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
        Classical.choose (γ.toPwC1Immersion.right_deriv_limit t h_part)
      else
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    let L_minus : ℝ → ℂ := fun t =>
      if h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition then
        Classical.choose (γ.toPwC1Immersion.left_deriv_limit t h_part)
      else
        deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t
    have hL_plus_ne : ∀ t ∈ crossings, L_plus t ≠ 0 := fun t ht => by
      by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
      · simpa [L_plus, dif_pos h_part] using
          (Classical.choose_spec (γ.toPwC1Immersion.right_deriv_limit t h_part)).1
      · simpa [L_plus, dif_neg h_part] using
          (deriv_limit_eq_at_off_partition γ (h_Ioo' t ht) h_part).1
    have hL_minus_ne : ∀ t ∈ crossings, L_minus t ≠ 0 := fun t ht => by
      by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
      · simpa [L_minus, dif_pos h_part] using
          (Classical.choose_spec (γ.toPwC1Immersion.left_deriv_limit t h_part)).1
      · simpa [L_minus, dif_neg h_part] using
          (deriv_limit_eq_at_off_partition γ (h_Ioo' t ht) h_part).1
    have hL_right' : ∀ t ∈ crossings,
        Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
          (𝓝[>] t) (𝓝 (L_plus t)) := fun t ht => by
      by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
      · simpa [L_plus, dif_pos h_part] using
          (Classical.choose_spec (γ.toPwC1Immersion.right_deriv_limit t h_part)).2
      · simpa [L_plus, dif_neg h_part] using
          (deriv_limit_eq_at_off_partition γ (h_Ioo' t ht) h_part).2.1
    have hL_left' : ∀ t ∈ crossings,
        Tendsto (deriv γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend)
          (𝓝[<] t) (𝓝 (L_minus t)) := fun t ht => by
      by_cases h_part : t ∈ γ.toPwC1Immersion.toPiecewiseC1Path.partition
      · simpa [L_minus, dif_pos h_part] using
          (Classical.choose_spec (γ.toPwC1Immersion.left_deriv_limit t h_part)).2
      · simpa [L_minus, dif_neg h_part] using
          (deriv_limit_eq_at_off_partition γ (h_Ioo' t ht) h_part).2.2
    have h_B' : ∀ (k : Fin (decomp.order s)), 1 ≤ k.val →
        decomp.coeff s k ≠ 0 → ∀ t ∈ crossings,
          (L_plus t / (↑‖L_plus t‖ : ℂ)) ^ k.val =
          ((-(L_minus t)) / (↑‖L_minus t‖ : ℂ)) ^ k.val :=
      condB_to_h_B_at_crossings_corner hU_open hS_in_U γ decomp hCondB hs
        h_Ioo' h_at' L_plus L_minus (fun _ _ => rfl) (fun _ _ => rfl)
        hL_plus_ne hL_minus_ne
    have h_flat_one : ∀ t₀ ∈ crossings,
        IsFlatOfOrder γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend t₀ 1 :=
      fun t₀ ht₀ => isFlatOfOrder_one γ.toPwC1Immersion t₀ (h_Ioo' t₀ ht₀)
    have h_simple_cpv : ∃ L : ℂ,
        HasCauchyPV (fun z => (z - s)⁻¹)
          γ.toPwC1Immersion.toPiecewiseC1Path s L :=
      hasCauchyPV_inv_sub_multiCrossing_corner (γ := γ) (s := s)
        (crossings := crossings) h_Ioo' h_at' h_complete' h_flat_one
    exact MultiPoleDCT.hasCauchyPVOn_polarPart_of_hasCauchyPV_multipole
      hS_in_U decomp γ hs h_null
      (hasCauchyPV_of_hasCauchyPVOn_singleton
        (cpv_polarPart_at_multiCrossed_pole_under_condB_corner
          hs decomp h_Ioo' h_at' h_complete' h_flat_at_each
          L_plus L_minus hL_plus_ne hL_minus_ne hL_right' hL_left' h_B'
          h_simple_cpv))

end HungerbuhlerWasem

end
