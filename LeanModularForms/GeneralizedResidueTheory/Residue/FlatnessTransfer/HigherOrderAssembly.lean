/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.PerTermVanishing
import LeanModularForms.GeneralizedResidueTheory.Residue.MeromorphicLaurent

/-!
# Higher-Order Cancellation Assembly

Assembles the per-term vanishing results into the full higher-order cancellation
proof, and provides the bridge from conditions (A')+(B) to `hHigherOrderCancel`.

## Main results

* `conditionsAB_imply_higherOrderCancel`: conditions (A')+(B) imply the cancellation hypothesis
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

noncomputable section

namespace GeneralizedResidueTheory

private lemma laurent_coeff_index_le_poleOrder
    (f : ℂ → ℂ) (s : ℂ) (hMero_s : MeromorphicAt f s)
    {N_s : ℕ} (a_s : Fin N_s → ℂ) (g_loc : ℂ → ℂ)
    (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    (kv : ℕ) (hkv : kv < N_s) (ha_zero : a_s ⟨kv, hkv⟩ ≠ 0) :
    kv + 1 ≤ poleOrderAt f s := by
  unfold poleOrderAt
  let nonzero_idx := (Finset.univ : Finset (Fin N_s)).filter (fun k => a_s k ≠ 0)
  have h_ne : nonzero_idx.Nonempty :=
    ⟨⟨kv, hkv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha_zero⟩⟩
  set m_idx := (nonzero_idx.max' h_ne) with hm_def
  have hm_ne : a_s m_idx ≠ 0 :=
    (Finset.mem_filter.mp (nonzero_idx.max'_mem h_ne)).2
  have hkv_le_m : kv ≤ m_idx.val :=
    Finset.le_max' nonzero_idx ⟨kv, hkv⟩
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha_zero⟩)
  have hm_max : ∀ k : Fin N_s, a_s k ≠ 0 → k ≤ m_idx :=
    fun k hk => Finset.le_max' nonzero_idx k
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
  suffices h_ord : meromorphicOrderAt f s = ↑(-(↑(m_idx.val + 1) : ℤ)) by
    rw [h_ord]; simp only [WithTop.untop₀_coe, neg_neg, Int.toNat_natCast]; omega
  rw [meromorphicOrderAt_eq_int_iff hMero_s]
  refine ⟨fun z => (z - s) ^ (m_idx.val + 1) * g_loc z +
    ∑ k : Fin N_s, a_s k * (z - s) ^ (m_idx.val - k.val), ?_, ?_, ?_⟩
  · exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg_loc_an |>.add
      (Finset.analyticAt_fun_sum Finset.univ
        (fun k _ => analyticAt_const.mul
          ((analyticAt_id.sub analyticAt_const).pow _)))
  · simp only [sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul, zero_add]
    have : ∑ k : Fin N_s, a_s k * (0 : ℂ) ^ (m_idx.val - k.val) = a_s m_idx := by
      rw [Finset.sum_eq_single m_idx]
      · simp
      · intro k _ hk; by_cases hkm : k.val < m_idx.val
        · simp [zero_pow (by omega : m_idx.val - k.val ≠ 0)]
        · push_neg at hkm
          have hk_gt := lt_of_le_of_ne (Fin.mk_le_mk.mpr hkm) (Ne.symm hk)
          simp only [show a_s k = 0 from by
            by_contra ha; exact absurd (hm_max k ha) (not_le.mpr hk_gt), zero_mul]
      · intro h; exact absurd (Finset.mem_univ m_idx) h
    rw [this]; exact hm_ne
  · filter_upwards [hf_eq_loc, self_mem_nhdsWithin] with z hfz hz
    rw [smul_eq_mul, hfz]
    have hzs_ne : z - s ≠ 0 := sub_ne_zero.mpr hz
    rw [mul_add, ← mul_assoc,
      zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hzs_ne), one_mul]
    congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl
    intro k _
    by_cases hk_le : k.val ≤ m_idx.val
    · field_simp [pow_ne_zero _ hzs_ne]; rw [mul_assoc (a_s k), ← pow_add,
        show k.val + 1 + (m_idx.val - k.val) = m_idx.val + 1 from by omega]
    · push_neg at hk_le; by_cases ha_k : a_s k = 0
      · simp [ha_k]
      · exact absurd (hm_max k ha_k) (not_le.mpr hk_le)

private lemma cpv_single_polar_term_tendsto_zero
    (S0 : Finset ℂ) (f : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0)
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hMero_s : MeromorphicAt f s)
    {N_s : ℕ} (a_s : Fin N_s → ℂ) (g_loc : ℂ → ℂ)
    (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    (t₁ : ℝ) (ht₁_Ioo : t₁ ∈ Ioo γ.a γ.b) (hcross₁ : γ.toFun t₁ = s)
    (h_angle : ∀ (k : Fin N_s), a_s k ≠ 0 → k.val ≥ 1 →
      ∃ m : ℤ, (k.val : ℝ) * _root_.angleAtCrossing γ t₁ ht₁_Ioo = ↑m * (2 * Real.pi))
    (h_flat_s : IsFlatOfOrder γ.toFun t₁ (poleOrderAt f s))
    (h_unique_s : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₁)
    (_hN_s_pos : N_s > 0)
    (kv : ℕ) (hkv : kv < N_s) (hk_ge : kv ≥ 1) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
        γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
  have hm : 2 ≤ kv + 1 := by omega
  by_cases ha_zero : a_s ⟨kv, hkv⟩ = 0
  · have h_zero : ∀ ε t, cauchyPrincipalValueIntegrandOn S0
        (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1)) γ.toFun ε t = 0 := by
      intro ε t; simp only [cauchyPrincipalValueIntegrandOn, ha_zero,
        zero_div, zero_mul, ite_self]
    simp only [show (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1)) γ.toFun ε t) =
      fun _ => 0 from funext fun ε => by
        rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
            (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1)) γ.toFun ε t) =
          fun _ => 0 from funext (h_zero ε)]
        exact intervalIntegral.integral_zero]
    exact tendsto_const_nhds
  · have h_order_bound : kv + 1 ≤ poleOrderAt f s :=
      laurent_coeff_index_le_poleOrder f s hMero_s a_s g_loc
        hg_loc_an hf_eq_loc kv hkv ha_zero
    have h_flat_k : IsFlatOfOrder γ.toFun t₁ (kv + 1) := IsFlatOfOrder.of_le h_flat_s
      h_order_bound ((γ.continuous_toFun t₁ (Ioo_subset_Icc_self ht₁_Ioo)).continuousAt
        (Icc_mem_nhds ht₁_Ioo.1 ht₁_Ioo.2))
    have h_angle_k : ∃ n : ℤ, ((kv + 1 - 1 : ℕ) : ℝ) *
        _root_.angleAtCrossing γ t₁ ht₁_Ioo = ↑n * (2 * Real.pi) := by
      rw [show (kv + 1 - 1 : ℕ) = kv from by omega]
      exact h_angle ⟨kv, hkv⟩ ha_zero hk_ge
    have h_zpow := multipoint_pv_zpow_tendsto_zero S0 γ s (kv + 1) hm
      hs t₁ ht₁_Ioo hcross₁ h_unique_s hγ_closed h_flat_k h_angle_k
    have h_eq : (fun ε => ∫ t in γ.a..γ.b,
          cauchyPrincipalValueIntegrandOn S0
            (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
            γ.toFun ε t) =
        fun ε => a_s ⟨kv, hkv⟩ * ∫ t in γ.a..γ.b,
          cauchyPrincipalValueIntegrandOn S0
            (fun z => (z - s) ^ (-(↑(kv + 1) : ℤ)))
            γ.toFun ε t := by
      ext ε; rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
          (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
          γ.toFun ε t) = (fun t => a_s ⟨kv, hkv⟩ *
          cauchyPrincipalValueIntegrandOn S0
            (fun z => (z - s) ^ (-(↑(kv + 1) : ℤ)))
            γ.toFun ε t) from funext fun t => by
        have : (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1)) =
            fun z => a_s ⟨kv, hkv⟩ * (z - s) ^ (-(↑(kv + 1) : ℤ)) := by
          ext z; rw [div_eq_mul_inv, zpow_neg, zpow_natCast, inv_eq_one_div, one_div]
        rw [this]; exact cpvIntegrandOn_const_smul S0 _ _ γ.toFun ε t]
      exact intervalIntegral.integral_const_mul _ _
    rw [h_eq, show (0 : ℂ) = a_s ⟨kv, hkv⟩ * 0 from (mul_zero _).symm]
    exact Filter.Tendsto.const_smul h_zpow (a_s ⟨kv, hkv⟩)

private lemma cpv_polarHigher_tendsto_zero
    (U : Set ℂ) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (s : ℂ) (hs : s ∈ S0)
    (_hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    {N_s : ℕ} (a_s : Fin N_s → ℂ)
    (h_polar_term_tendsto : ∀ (k : Fin N_s), k.val ≥ 1 →
        Tendsto (fun ε => ∫ t in γ.a..γ.b,
          cauchyPrincipalValueIntegrandOn S0
            (fun z => a_s k / (z - s) ^ (k.val + 1))
            γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    let polarHigher : ℂ → ℂ := fun z =>
      ∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 polarHigher γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  intro polarHigher
  have h_per_k_tendsto : ∀ k : Fin N_s, Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
        γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
    intro k; by_cases hk : k.val ≥ 1
    · simp_rw [show (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0) =
        fun z => a_s k / (z - s) ^ (k.val + 1) from by ext z; simp [hk]]
      exact h_polar_term_tendsto k hk
    · simp_rw [show (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0) =
        fun _ => (0 : ℂ) from by ext z; simp [hk],
        cauchyPrincipalValueIntegrandOn, zero_mul, ite_self, intervalIntegral.integral_zero]
      exact tendsto_const_nhds
  have h_per_k_int : ∀ (k : Fin N_s), ∀ ε > 0, IntervalIntegrable
      (cauchyPrincipalValueIntegrandOn S0
        (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0) γ.toFun ε)
      volume γ.a γ.b := by
    intro k ε hε; apply intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0
    · by_cases hk : k.val ≥ 1
      · simp only [hk, ite_true]; apply ContinuousOn.div continuousOn_const
          ((continuousOn_id.sub continuousOn_const).pow _)
        intro z ⟨_, hz_not_S0⟩; exact pow_ne_zero _ (sub_ne_zero.mpr
          (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs)))
      · simp only [hk, ite_false]; exact continuousOn_const
    · exact hγ_in_U
    · exact hε
  have h_int_eq : ∀ ε > 0, ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 polarHigher γ.toFun ε t =
    ∑ k : Fin N_s, ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
      (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
      γ.toFun ε t := by
    intro ε hε
    rw [show (fun t => cauchyPrincipalValueIntegrandOn S0 polarHigher γ.toFun ε t) =
      fun t => ∑ k : Fin N_s, cauchyPrincipalValueIntegrandOn S0
        (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
        γ.toFun ε t from funext (cpvIntegrandOn_finset_sum S0 Finset.univ
      (fun k z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0) γ.toFun ε)]
    exact intervalIntegral.integral_finset_sum (fun k _ => h_per_k_int k ε hε)
  apply (show Tendsto (fun ε => ∑ k : Fin N_s, ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
        γ.toFun ε t) (𝓝[>] 0) (𝓝 0) from by
    rw [show (0 : ℂ) = ∑ _k : Fin N_s, (0 : ℂ) from Finset.sum_const_zero.symm]
    exact tendsto_finset_sum Finset.univ (fun k _ => h_per_k_tendsto k)).congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (h_int_eq ε hε).symm

private lemma cpv_term_tendsto_zero_of_no_poles
    (S0 : Finset ℂ) (f : ℂ → ℂ) (s : ℂ)
    (γ : PiecewiseC1Immersion)
    (hMero_s : MeromorphicAt f s)
    (g_loc : ℂ → ℂ) (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s, f z = g_loc z) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  have hf_tends : Tendsto f (𝓝[≠] s) (𝓝 (g_loc s)) := by
    apply Filter.Tendsto.congr'
    · filter_upwards [hf_eq_loc] with z hz; exact hz.symm
    · exact hg_loc_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h_ord_nn : 0 ≤ meromorphicOrderAt f s :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg hMero_s).mp ⟨g_loc s, hf_tends⟩
  have h_pp_zero : meromorphicPrincipalPart f s = fun _ => 0 := by
    unfold meromorphicPrincipalPart
    exact dif_neg (fun h => absurd h.2 (not_lt.mpr h_ord_nn))
  have h_res_zero : residueAt f s = 0 := by
    unfold residueAt; apply Filter.Tendsto.limUnder_eq
    obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_loc_an.exists_ball_analyticOnNhd
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq_loc
    obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq_loc
    have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
    apply tendsto_nhds_of_eventually_eq
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hr₀_pos] with r hr_lt hr_pos
    simp only [Set.mem_Ioi] at hr_pos; simp only [Set.mem_Iio] at hr_lt
    have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
    have h_eq_on : ∀ z ∈ Metric.sphere s r, f z = g_loc z := by
      intro z hz
      have hne : z ≠ s := by
        intro h; rw [h, Metric.mem_sphere, dist_self] at hz; linarith
      exact hrf_eq ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf),
        Set.mem_compl_singleton_iff.mpr hne⟩
    have hg_cont : ContinuousOn g_loc (Metric.closedBall s r) :=
      hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
    have hg_diff : DifferentiableOn ℂ g_loc (Metric.ball s r) := by
      intro z hz; exact (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)
        ).differentiableAt.differentiableWithinAt
    have hg_ci_zero : (∮ z in C(s, r), g_loc z) = 0 :=
      Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        hr_pos.le Set.countable_empty hg_cont
        (fun z ⟨hz, _⟩ => hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz))
    simp [circleIntegral.integral_congr hr_pos.le h_eq_on, hg_ci_zero]
  have h_term_eq_zero :
      (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) =
        fun _ => 0 := by
    ext z; simp only [h_pp_zero, h_res_zero]; simp [zero_div]
  rw [h_term_eq_zero]
  simp only [cauchyPrincipalValueIntegrandOn, zero_mul, ite_self]
  simp [intervalIntegral.integral_zero]

private lemma ppMinusRes_err_eventuallyEq
    (f : ℂ → ℂ) (s : ℂ) {N_s : ℕ} (hN_s_pos : N_s > 0)
    (a_s : Fin N_s → ℂ) (g_loc g_rp : ℂ → ℂ)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    (hg_rp_eq : ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_rp z)
    (h_a0_eq : a_s ⟨0, hN_s_pos⟩ = residueAt f s) :
    let term_s : ℂ → ℂ := fun z =>
      meromorphicPrincipalPart f s z - residueAt f s / (z - s)
    let polarHigher : ℂ → ℂ := fun z =>
      ∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0
    let err_loc : ℂ → ℂ := fun z => g_loc z - g_rp z
    let err_nf : ℂ → ℂ := fun z =>
      if z = s then err_loc s else term_s z - polarHigher z
    err_nf =ᶠ[𝓝 s] err_loc := by
  intro term_s polarHigher err_loc err_nf
  rw [Filter.eventuallyEq_iff_exists_mem]
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq_loc hg_rp_eq
  obtain ⟨r1, hr1_pos, hr1_eq⟩ := hf_eq_loc
  obtain ⟨r2, hr2_pos, hr2_eq⟩ := hg_rp_eq
  set r := min r1 r2 with hr_def
  have hr_pos : 0 < r := lt_min hr1_pos hr2_pos
  refine ⟨Metric.ball s r, Metric.ball_mem_nhds s hr_pos, fun z hz => ?_⟩
  by_cases hzs : z = s
  · subst hzs; simp [err_nf]
  · simp only [err_nf, if_neg hzs]
    have hz_in_1 : z ∈ Metric.ball s r1 ∩ {s}ᶜ :=
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _)),
       Set.mem_compl_singleton_iff.mpr hzs⟩
    have hz_in_2 : z ∈ Metric.ball s r2 ∩ {s}ᶜ :=
      ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _)),
       Set.mem_compl_singleton_iff.mpr hzs⟩
    have hfz : f z = g_loc z + ∑ k : Fin N_s,
        a_s k / (z - s) ^ (k.val + 1) := hr1_eq hz_in_1
    have hgrpz : f z - meromorphicPrincipalPart f s z = g_rp z := hr2_eq hz_in_2
    change meromorphicPrincipalPart f s z - residueAt f s / (z - s) -
      (∑ k : Fin N_s, if k.val ≥ 1 then
        a_s k / (z - s) ^ (k.val + 1) else 0) = g_loc z - g_rp z
    have hpp : meromorphicPrincipalPart f s z = f z - g_rp z := by
      linear_combination -hgrpz
    rw [hpp, hfz]
    have h_sum_split : ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1) -
        ∑ k : Fin N_s, (if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0) =
        a_s ⟨0, hN_s_pos⟩ / (z - s) := by
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single ⟨0, hN_s_pos⟩]
      · simp
      · intro k _ hk
        have hkval : k.val ≥ 1 := by
          by_contra h; push_neg at h
          have : k.val = 0 := by omega
          exact hk (Fin.ext this)
        simp [hkval]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h_a0_eq] at h_sum_split; linear_combination h_sum_split

private lemma ppMinusRes_err_differentiableOn
    (U : Set ℂ) (S0 : Finset ℂ) (f : ℂ → ℂ) (s : ℂ) (hs : s ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    {N_s : ℕ} (a_s : Fin N_s → ℂ) (g_loc g_rp : ℂ → ℂ)
    (hg_loc_an : AnalyticAt ℂ g_loc s) (hg_rp_an : AnalyticAt ℂ g_rp s)
    (h_ev : (fun z => if z = s then (g_loc z - g_rp z)
      else (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) -
        (∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0))
      =ᶠ[𝓝 s] fun z => g_loc z - g_rp z) :
    DifferentiableOn ℂ (fun z => if z = s then (g_loc z - g_rp z)
      else (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) -
        (∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)) U := by
  set err_nf := fun z => if z = s then (g_loc z - g_rp z)
    else (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) -
      (∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
  intro z hz
  by_cases hzs : z = s
  · rw [hzs]
    exact ((h_ev.differentiableAt_iff (𝕜 := ℂ)).mpr
      (hg_loc_an.sub hg_rp_an).differentiableAt).differentiableWithinAt
  · have h_ev_z : err_nf =ᶠ[𝓝 z] fun w =>
        (meromorphicPrincipalPart f s w - residueAt f s / (w - s)) -
        (∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      refine ⟨{s}ᶜ, IsOpen.mem_nhds isOpen_compl_singleton
        (Set.mem_compl_singleton_iff.mpr hzs), fun w hw => ?_⟩
      simp only [err_nf, if_neg (Set.mem_compl_singleton_iff.mp hw)]
    apply DifferentiableAt.differentiableWithinAt
    rw [h_ev_z.differentiableAt_iff]
    have h_term_diff : DifferentiableAt ℂ
        (fun w => meromorphicPrincipalPart f s w - residueAt f s / (w - s)) z := by
      apply DifferentiableAt.sub
      · exact (meromorphicPrincipalPart_differentiableOn f s
          (hMero s hs) z (Set.mem_compl_singleton_iff.mpr hzs)).differentiableAt
          (IsOpen.mem_nhds isOpen_compl_singleton
            (Set.mem_compl_singleton_iff.mpr hzs))
      · exact (differentiableAt_const _).div
          (differentiableAt_id.sub (differentiableAt_const _))
          (sub_ne_zero.mpr hzs)
    have h_polar_diff : DifferentiableAt ℂ (fun w =>
        ∑ k : Fin N_s, if k.val ≥ 1
          then a_s k / (w - s) ^ (k.val + 1) else 0) z := by
      have h_eq_sum : (fun w => ∑ k : Fin N_s,
          if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) =
        ∑ k : Fin N_s, fun w =>
          if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0 := by
        ext w; simp [Finset.sum_apply]
      rw [h_eq_sum]; apply DifferentiableAt.sum; intro k _
      by_cases hk : k.val ≥ 1
      · simp only [hk, ite_true]
        exact (differentiableAt_const _).div
          ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
          (pow_ne_zero _ (sub_ne_zero.mpr hzs))
      · simp only [hk, ite_false]; exact differentiableAt_const 0
    exact h_term_diff.sub h_polar_diff

private lemma polarHigher_continuousOn_diff
    (S0 : Finset ℂ) (s : ℂ) (hs : s ∈ S0)
    {N_s : ℕ} (a_s : Fin N_s → ℂ) :
    ContinuousOn (fun z =>
      ∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
      (univ \ ↑S0) := by
  apply continuousOn_finset_sum; intro k _
  by_cases hk : k.val ≥ 1
  · simp only [hk, ite_true]
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_id.sub continuousOn_const).pow _)
    intro z ⟨_, hz_not_S0⟩
    exact pow_ne_zero _ (sub_ne_zero.mpr
      (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs)))
  · simp only [hk, ite_false]; exact continuousOn_const

private lemma cpv_tendsto_of_err_plus_polar_split
    (U : Set ℂ) (S0 : Finset ℂ) (s : ℂ) (hs : s ∈ S0)
    (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    {N_s : ℕ} (a_s : Fin N_s → ℂ)
    (err_nf : ℂ → ℂ)
    (h_off_s : ∀ z, z ≠ s →
      (meromorphicPrincipalPart _ s z - residueAt _ s / (z - s)) =
      err_nf z + ∑ k : Fin N_s,
        if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
    (h_err_nf_diff : DifferentiableOn ℂ err_nf U)
    (h_err_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 err_nf γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0))
    (h_polar_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (fun z =>
          ∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
        γ.toFun ε t) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart _ s z - residueAt _ s / (z - s))
        γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
  apply Filter.Tendsto.congr' _ (h_err_cpv.add h_polar_cpv)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  have h_pw_eq : ∀ t, cauchyPrincipalValueIntegrandOn S0
      (fun z => meromorphicPrincipalPart _ s z - residueAt _ s / (z - s))
      γ.toFun ε t = cauchyPrincipalValueIntegrandOn S0
      (fun z => err_nf z + ∑ k : Fin N_s,
        if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
      γ.toFun ε t := by
    intro t; simp only [cauchyPrincipalValueIntegrandOn]
    split_ifs with h_near
    · rfl
    · push_neg at h_near
      have hne : γ.toFun t ≠ s := fun heq => by
        have := h_near s hs; rw [heq, sub_self, norm_zero] at this; linarith
      congr 1; exact h_off_s (γ.toFun t) hne
  rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
      (fun z => meromorphicPrincipalPart _ s z - residueAt _ s / (z - s))
      γ.toFun ε t) = fun t => cauchyPrincipalValueIntegrandOn S0
      (fun z => err_nf z + ∑ k : Fin N_s,
        if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
      γ.toFun ε t from funext h_pw_eq,
    show (fun t => cauchyPrincipalValueIntegrandOn S0
      (fun z => err_nf z + ∑ k : Fin N_s,
        if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
      γ.toFun ε t) = fun t =>
      cauchyPrincipalValueIntegrandOn S0 err_nf γ.toFun ε t +
      cauchyPrincipalValueIntegrandOn S0 (fun z =>
        ∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
        γ.toFun ε t from
    funext (fun t => cpvIntegrandOn_add S0 err_nf _ γ.toFun ε t)]
  exact (intervalIntegral.integral_add
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 err_nf
      (h_err_nf_diff.continuousOn.mono Set.diff_subset) γ hγ_in_U ε hε)
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 _
      ((polarHigher_continuousOn_diff S0 s hs a_s).mono
        (fun z ⟨_, h⟩ => ⟨Set.mem_univ z, h⟩))
      γ hγ_in_U ε hε)).symm

private lemma cpv_term_tendsto_zero_of_crossed_positive_order
    (U : Set ℂ) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (_hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (_hCondB : SatisfiesConditionB γ f S0)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (h_holo_vanish : ∀ (g : ℂ → ℂ), DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (s : ℂ) (hs : s ∈ S0)
    (t₁ : ℝ) (ht₁ : t₁ ∈ Icc γ.a γ.b) (hcross₁ : γ.toFun t₁ = s)
    (ht₁_Ioo : t₁ ∈ Ioo γ.a γ.b)
    {N_s : ℕ} (hN_s_pos : N_s > 0)
    (a_s : Fin N_s → ℂ) (g_loc : ℂ → ℂ)
    (hg_loc_an : AnalyticAt ℂ g_loc s)
    (hf_eq_loc : ∀ᶠ z in 𝓝[≠] s,
      f z = g_loc z + ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1))
    (h_angle : ∀ (k : Fin N_s), a_s k ≠ 0 → k.val ≥ 1 →
      ∃ m : ℤ, (k.val : ℝ) * _root_.angleAtCrossing γ t₁ ht₁_Ioo = ↑m * (2 * Real.pi)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  have h_unique_s : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₁ :=
    fun t ht hc => h_unique_cross s hs t ht t₁ ht₁ hc hcross₁
  have h_a0_eq : a_s ⟨0, hN_s_pos⟩ = residueAt f s :=
    (residueAt_eq_laurent_head_coeff f s N_s hN_s_pos a_s g_loc
      hg_loc_an hf_eq_loc).symm
  have h_polar_term_tendsto : ∀ (k : Fin N_s), k.val ≥ 1 →
      Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => a_s k / (z - s) ^ (k.val + 1))
          γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
    intro ⟨kv, hkv⟩ hk_ge; simp at hk_ge
    exact cpv_single_polar_term_tendsto_zero S0 f s hs γ hγ_closed
      (hMero s hs) a_s g_loc hg_loc_an hf_eq_loc t₁ ht₁_Ioo hcross₁
      h_angle (hCondA s hs t₁ ht₁ hcross₁ ht₁_Ioo) h_unique_s hN_s_pos kv hkv hk_ge
  obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
    meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
  set err_nf : ℂ → ℂ := fun z =>
    if z = s then (g_loc z - g_rp z)
    else (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) -
      (∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
  have h_off_s : ∀ z, z ≠ s →
      (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) =
      err_nf z + ∑ k : Fin N_s,
        if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0 := by
    intro z hz; simp only [err_nf, if_neg hz]; ring
  have h_ev := ppMinusRes_err_eventuallyEq f s hN_s_pos a_s g_loc g_rp
    hf_eq_loc hg_rp_eq h_a0_eq
  have h_err_nf_diff := ppMinusRes_err_differentiableOn U S0 f s hs hMero
    a_s g_loc g_rp hg_loc_an hg_rp_an h_ev
  exact cpv_tendsto_of_err_plus_polar_split U S0 s hs γ hγ_in_U a_s err_nf
    h_off_s h_err_nf_diff
    (tendsto_cpv_of_continuousOn_zero_integral S0 err_nf γ
      (h_err_nf_diff.continuousOn.mono
        (fun z ⟨t, ht, htz⟩ => htz ▸ hγ_in_U t ht))
      (h_holo_vanish err_nf h_err_nf_diff))
    (cpv_polarHigher_tendsto_zero U S0 f γ s hs hMero hγ_in_U a_s
      h_polar_term_tendsto)

private lemma circleIntegral_ppMinusRes_eq_fMinusRes
    (f : ℂ → ℂ) (s : ℂ) (hMero_s : MeromorphicAt f s)
    (g_rp : ℂ → ℂ) (hg_rp_an : AnalyticAt ℂ g_rp s)
    (hg_rp_eq : ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_rp z)
    (r : ℝ) (hr_pos : 0 < r)
    (hr_rp : ∀ z ∈ Metric.ball s r ∩ {s}ᶜ,
      f z - meromorphicPrincipalPart f s z = g_rp z)
    (hr_an : AnalyticOnNhd ℂ g_rp (Metric.ball s r)) :
    (∮ z in C(s, r), (fun z =>
      meromorphicPrincipalPart f s z - residueAt f s / (z - s)) z) =
    (∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z) := by
  have hg_cont := hr_an.continuousOn.mono (Metric.closedBall_subset_ball (le_refl r))
  have hg_ci_zero : (∮ z in C(s, r), g_rp z) = 0 :=
    Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
      hr_pos.le Set.countable_empty
      (hr_an.continuousOn.mono (Metric.sphere_subset_closedBall.trans
        (Metric.closedBall_subset_ball (le_refl r))))
      (fun z ⟨hz, _⟩ => (hr_an z hz).differentiableAt.differentiableWithinAt.differentiableAt
        (Metric.isOpen_ball.mem_nhds hz))
  have hg_ci : CircleIntegrable g_rp s r :=
    (hr_an.continuousOn.mono (Metric.sphere_subset_closedBall.trans
      (Metric.closedBall_subset_ball (le_refl r)))).circleIntegrable hr_pos.le
  have h_sphere_sub : Metric.sphere s r ⊆ ({s}ᶜ : Set ℂ) :=
    fun z hz heq => by rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
  have h_term_ci : CircleIntegrable
      (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) s r :=
    ((meromorphicPrincipalPart_differentiableOn f s hMero_s).sub
      (DifferentiableOn.div (differentiableOn_const _)
        (differentiableOn_id.sub (differentiableOn_const _))
        (fun z hz => sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)))).continuousOn.mono
      h_sphere_sub |>.circleIntegrable hr_pos.le
  have h_eq_on : ∀ z ∈ Metric.sphere s r,
      (meromorphicPrincipalPart f s z - residueAt f s / (z - s)) =
      (f z - residueAt f s / (z - s)) - g_rp z := by
    intro z hz
    have hne : z ≠ s := fun heq => by rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    linear_combination -(hr_rp ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]),
      Set.mem_compl_singleton_iff.mpr hne⟩)
  calc (∮ z in C(s, r), (fun z =>
        meromorphicPrincipalPart f s z - residueAt f s / (z - s)) z)
      = _ + 0 := (add_zero _).symm
    _ = _ + (∮ z in C(s, r), g_rp z) := by rw [hg_ci_zero]
    _ = (∮ z in C(s, r), (fun z => (meromorphicPrincipalPart f s z -
        residueAt f s / (z - s)) + g_rp z) z) :=
      (circleIntegral.integral_add h_term_ci hg_ci).symm
    _ = _ := circleIntegral.integral_congr hr_pos.le (fun z hz => by
        linear_combination h_eq_on z hz)

private lemma residueAt_ppMinusRes_eq_zero
    (f : ℂ → ℂ) (s : ℂ) (hMero_s : MeromorphicAt f s) :
    residueAt (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) s = 0 := by
  have h_single := residueAt_sub_residueSum_eq_zero {s} f s
    (Finset.mem_singleton.mpr rfl) hMero_s
  simp only [Finset.sum_singleton] at h_single
  obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
    meromorphicAt_sub_principalPart_eventually f s hMero_s
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_rp_an.exists_ball_analyticOnNhd
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hg_rp_eq
  obtain ⟨rp, hrp_pos, hrp_eq⟩ := hg_rp_eq
  set ρ' := min rg rp
  have hρ'_pos : 0 < ρ' := lt_min hrg_pos hrp_pos
  rw [show residueAt (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) s =
    residueAt (fun z => f z - residueAt f s / (z - s)) s from by
    unfold residueAt limUnder; congr 1; apply Filter.map_congr
    apply Filter.Eventually.mono (Ioo_mem_nhdsGT hρ'_pos)
    intro r ⟨hr_pos, hr_lt⟩; simp only; congr 1
    exact circleIntegral_ppMinusRes_eq_fMinusRes f s hMero_s g_rp hg_rp_an
      (by rw [Filter.Eventually, Metric.mem_nhdsWithin_iff]; exact ⟨rp, hrp_pos, hrp_eq⟩)
      r hr_pos
      (fun z ⟨hz_ball, hz_ne⟩ => hrp_eq ⟨Metric.mem_ball.mpr
        ((Metric.mem_ball.mp hz_ball).trans (hr_lt.trans_le (min_le_right _ _))), hz_ne⟩)
      (hg_ball.mono (Metric.ball_subset_ball (hr_lt.trans_le (min_le_left _ _)).le))]
  exact h_single

private lemma cpv_term_tendsto_zero_of_uncrossed
    (U : Set ℂ) (_hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (s : ℂ) (hs : s ∈ S0)
    (_hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    let term_s : ℂ → ℂ := fun z =>
      meromorphicPrincipalPart f s z - residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 term_s γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  intro term_s
  have h_term_cont_image : ContinuousOn term_s (γ.toFun '' Icc γ.a γ.b) := by
    apply ContinuousOn.sub
    · exact (meromorphicPrincipalPart_differentiableOn f s
        (hMero s hs)).continuousOn.mono
        (fun z ⟨t, ht, htz⟩ =>
          Set.mem_compl_singleton_iff.mpr (htz ▸ h_avoids t ht))
    · apply ContinuousOn.div continuousOn_const
        (continuousOn_id.sub continuousOn_const)
      intro z ⟨t, ht, htz⟩
      exact sub_ne_zero.mpr (htz ▸ h_avoids t ht)
  have h_term_int_zero : ∫ t in γ.a..γ.b,
      term_s (γ.toFun t) * deriv γ.toFun t = 0 := by
    have h_term_diff : DifferentiableOn ℂ term_s (U \ {s}) := by
      apply DifferentiableOn.sub
      · exact (meromorphicPrincipalPart_differentiableOn f s
          (hMero s hs)).mono (fun z hz => by
          exact Set.mem_compl_singleton_iff.mpr hz.2)
      · apply DifferentiableOn.div (differentiableOn_const _)
          (differentiableOn_id.sub (differentiableOn_const _))
        intro z ⟨_, hz⟩
        exact sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
    have h_term_mero : MeromorphicAt term_s s := by
      obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
        meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
      have h_pp_eq : (fun z => f z - g_rp z) =ᶠ[𝓝[≠] s]
          meromorphicPrincipalPart f s := by
        filter_upwards [hg_rp_eq] with z hz
        linear_combination hz
      have h_pp_mero : MeromorphicAt (meromorphicPrincipalPart f s) s :=
        ((hMero s hs).fun_sub hg_rp_an.meromorphicAt).congr h_pp_eq
      exact h_pp_mero.fun_sub
        ((MeromorphicAt.const (residueAt f s) s).fun_div
          ((MeromorphicAt.id s).fun_sub (MeromorphicAt.const s s)))
    have h_term_res : residueAt term_s s = 0 :=
      residueAt_ppMinusRes_eq_zero f s (hMero s hs)
    exact h_finset_vanish {s} term_s
      (fun s' hs' => by rw [Finset.mem_singleton.mp hs']; exact h_term_mero)
      (fun s' hs' => by rw [Finset.mem_singleton.mp hs']; exact h_term_res)
      (by rwa [Finset.coe_singleton])
      (fun s' hs' => by rw [Finset.mem_singleton.mp hs']; exact hS0_in_U s hs)
      (fun s' hs' t ht => by rw [Finset.mem_singleton.mp hs']; exact h_avoids t ht)
  exact tendsto_cpv_of_continuousOn_zero_integral S0 term_s γ
    h_term_cont_image h_term_int_zero

private lemma regularPart_nf_differentiableOn_at_pole
    (U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (g_corr : ∀ s ∈ S0, ℂ → ℂ)
    (hg_corr_an : ∀ s (hs : s ∈ S0), AnalyticAt ℂ (g_corr s hs) s)
    (hg_corr_eq : ∀ s (hs : s ∈ S0),
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_corr s hs z)
    (z : ℂ) (hz : z ∈ U) (hz_S : z ∈ S0) :
    let h_reg_nf : ℂ → ℂ := fun w =>
      if hw : w ∈ S0 then
        g_corr w hw w - ∑ s' ∈ S0.erase w, meromorphicPrincipalPart f s' w
      else f w - ∑ s ∈ S0, meromorphicPrincipalPart f s w
    DifferentiableWithinAt ℂ h_reg_nf U z := by
  intro h_reg_nf
  have h_other_pp_diff : DifferentiableAt ℂ
      (fun w => ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) z := by
    have h_each : ∀ s' ∈ S0.erase z,
        DifferentiableAt ℂ (meromorphicPrincipalPart f s') z := by
      intro s' hs'
      have hne : z ≠ s' := (Finset.ne_of_mem_erase hs').symm
      exact (meromorphicPrincipalPart_differentiableOn f s'
        (hMero s' (Finset.mem_of_mem_erase hs')) z
        (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
    have h_sum := DifferentiableAt.sum h_each
    rwa [show (fun w => ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) =
        (∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s') from
      funext (fun w => (Finset.sum_apply w _ _).symm)]
  have h_corr_diff : DifferentiableAt ℂ
      (fun w => g_corr z hz_S w -
        ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) z :=
    (hg_corr_an z hz_S).differentiableAt.sub h_other_pp_diff
  have h_compl_open : IsOpen (↑(S0.erase z) : Set ℂ)ᶜ :=
    (S0.erase z).finite_toSet.isClosed.isOpen_compl
  have hz_in_compl : z ∈ (↑(S0.erase z) : Set ℂ)ᶜ :=
    Set.mem_compl (fun hh => (Finset.notMem_erase z S0) (Finset.mem_coe.mp hh))
  have h_ev : (fun w => g_corr z hz_S w -
      ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) =ᶠ[𝓝 z] h_reg_nf := by
    have hg_corr_eq_z := hg_corr_eq z hz_S
    rw [Filter.Eventually, mem_nhdsWithin] at hg_corr_eq_z
    obtain ⟨V, hV_open, hz_V, hV_eq⟩ := hg_corr_eq_z
    apply Filter.Eventually.mono
      ((hV_open.inter h_compl_open).mem_nhds ⟨hz_V, hz_in_compl⟩)
    intro w ⟨hw_V, hw_compl⟩
    change (fun w => g_corr z hz_S w -
      ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w) w = h_reg_nf w
    simp only [h_reg_nf]
    by_cases hw_S : w ∈ S0
    · rw [show w = z from by
        by_contra hne; exact hw_compl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hw_S⟩))]
      simp [hz_S]
    · have hw_ne_z : w ≠ z := fun heq => hw_S (heq ▸ hz_S)
      have h_fw : f w - meromorphicPrincipalPart f z w = g_corr z hz_S w :=
        hV_eq ⟨hw_V, hw_ne_z⟩
      simp only [dif_neg hw_S]
      rw [show (∑ s ∈ S0, meromorphicPrincipalPart f s w) =
          meromorphicPrincipalPart f z w +
          ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w from
        (Finset.add_sum_erase S0 _ hz_S).symm,
        ← h_fw]
      ring
  exact (h_ev.differentiableAt_iff.mp h_corr_diff).differentiableWithinAt

private lemma regularPart_nf_differentiableOn_off_poles
    (U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (z : ℂ) (hz : z ∈ U) (hz_S : z ∉ S0) :
    let total_pp : ℂ → ℂ := fun w => ∑ s ∈ S0, meromorphicPrincipalPart f s w
    let h_reg_nf : ℂ → ℂ := fun w =>
      if _ : w ∈ S0 then 0 else f w - total_pp w
    DifferentiableWithinAt ℂ (fun w => f w - total_pp w) U z := by
  intro total_pp _
  have hz_punct : z ∈ U \ ↑S0 := ⟨hz, fun hh => hz_S (Finset.mem_coe.mp hh)⟩
  have hU_S_open : IsOpen (U \ ↑S0) := hU.sdiff (S0.finite_toSet.isClosed)
  have hf_da : DifferentiableAt ℂ f z :=
    (hf z hz_punct).differentiableAt (hU_S_open.mem_nhds hz_punct)
  have htp_da : DifferentiableAt ℂ total_pp z := by
    have h_each : ∀ s ∈ S0,
        DifferentiableAt ℂ (meromorphicPrincipalPart f s) z := by
      intro s hs
      have hne : z ≠ s := fun heq => hz_S (heq ▸ hs)
      exact (meromorphicPrincipalPart_differentiableOn f s (hMero s hs) z
        (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
    have h_sum := DifferentiableAt.sum h_each
    rwa [show total_pp = (∑ s ∈ S0, meromorphicPrincipalPart f s) from
      funext (fun z => (Finset.sum_apply z _ _).symm)]
  exact (hf_da.sub htp_da).differentiableWithinAt

private lemma cpv_ppMinusRes_per_term_tendsto_zero
    (U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (s : ℂ) (hs : s ∈ S0) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  by_cases h_crossed : ∃ t ∈ Icc γ.a γ.b, γ.toFun t = s
  · obtain ⟨t₁, ht₁, hcross₁⟩ := h_crossed
    have ht₁_Ioo : t₁ ∈ Ioo γ.a γ.b := by
      have h_endpt := h_no_endpt s hs
      exact ⟨(lt_or_eq_of_le ht₁.1).elim id (fun h => absurd (h ▸ hcross₁) h_endpt.1),
        (lt_or_eq_of_le ht₁.2).elim id (fun h => absurd (h ▸ hcross₁) h_endpt.2)⟩
    obtain ⟨N_s, a_s, g_loc, hg_loc_an, hf_eq_loc, h_angle⟩ :=
      hCondB.laurent_compatible s hs t₁ ht₁ hcross₁ ht₁_Ioo
    rcases Nat.eq_zero_or_pos N_s with hN_s_zero | hN_s_pos
    · subst hN_s_zero
      exact cpv_term_tendsto_zero_of_no_poles S0 f s γ (hMero s hs) g_loc hg_loc_an
        (hf_eq_loc.mono fun _ hz => by
          simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hz; exact hz)
    · exact cpv_term_tendsto_zero_of_crossed_positive_order U S0 f hf γ
        hγ_closed hγ_in_U hMero hCondA hCondB h_unique_cross h_holo_vanish
        s hs t₁ ht₁ hcross₁ ht₁_Ioo hN_s_pos a_s g_loc hg_loc_an hf_eq_loc h_angle
  · push_neg at h_crossed
    exact cpv_term_tendsto_zero_of_uncrossed U hU S0 f γ s hs
      hγ_in_U hMero hS0_in_U h_finset_vanish h_crossed

private lemma cpv_ppMinusRes_sum_tendsto_zero
    (U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0,
          (meromorphicPrincipalPart f s z - residueAt f s / (z - s)))
        γ.toFun ε t)
    (𝓝[>] 0) (𝓝 0) := by
  have h_per_s_cont : ∀ s ∈ S0,
      ContinuousOn (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        (U \ ↑S0) := by
    intro s hs; apply ContinuousOn.sub
    · exact (meromorphicPrincipalPart_differentiableOn f s (hMero s hs)).continuousOn.mono
        (fun z hz => Set.mem_compl_singleton_iff.mpr
          (fun heq => by subst heq; exact hz.2 (Finset.mem_coe.mpr hs)))
    · apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
      intro z ⟨_, hz_not_S0⟩
      exact sub_ne_zero.mpr (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs))
  have h_per_s_int : ∀ s ∈ S0, ∀ ε > 0, IntervalIntegrable
      (cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) γ.toFun ε)
      volume γ.a γ.b := fun s hs ε hε =>
    intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 _ (h_per_s_cont s hs) γ hγ_in_U ε hε
  have h_int_sum : ∀ ε > 0, ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
      (fun z => ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s)))
      γ.toFun ε t = ∑ s ∈ S0, ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t := by
    intro ε hε
    rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s)))
        γ.toFun ε t) = (fun t => ∑ s ∈ S0, cauchyPrincipalValueIntegrandOn S0
        (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        γ.toFun ε t) from funext (cpvIntegrandOn_finset_sum S0 S0
      (fun s z => meromorphicPrincipalPart f s z - residueAt f s / (z - s)) γ.toFun ε)]
    exact intervalIntegral.integral_finset_sum (fun s _hs => h_per_s_int s _hs ε hε)
  rw [show (0 : ℂ) = ∑ _s ∈ S0, (0 : ℂ) from (Finset.sum_const_zero).symm]
  apply Filter.Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε); exact (h_int_sum ε hε).symm
  · exact tendsto_finset_sum S0 (fun s hs => cpv_ppMinusRes_per_term_tendsto_zero U hU S0 f hf γ
      hγ_closed hγ_in_U hMero hCondA hCondB h_no_endpt h_unique_cross hS0_in_U h_holo_vanish
      h_finset_vanish s hs)

private lemma ppMinusRes_sum_continuousOn_diff
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hMero : ∀ s ∈ S0, MeromorphicAt f s) :
    ContinuousOn (fun z =>
      ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s)))
      (univ \ ↑S0) := by
  apply continuousOn_finset_sum; intro s hs
  apply ContinuousOn.sub
  · exact (meromorphicPrincipalPart_differentiableOn f s (hMero s hs)).continuousOn.mono
      (fun z hz => Set.mem_compl_singleton_iff.mpr
        (fun heq => by subst heq; exact hz.2 (Finset.mem_coe.mpr hs)))
  · apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro z ⟨_, hz_not_S0⟩
    exact sub_ne_zero.mpr (fun heq => by
      subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs))

private lemma assembly_no_crossings_case
    (U : Set ℂ) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_no_crossings : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (hfres_diff : DifferentiableOn ℂ
      (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) (U \ ↑S0)) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  intro h
  have hh_cont : ContinuousOn h (γ.toFun '' Icc γ.a γ.b) :=
    (hf.sub hfres_diff).continuousOn.mono (fun z ⟨t, ht, htz⟩ => by
      subst htz; exact ⟨hγ_in_U t ht, fun hz_S0 =>
        h_no_crossings _ (Finset.mem_coe.mp hz_S0) t ht rfl⟩)
  have h_mero_sum : ∀ s ∈ S0, MeromorphicAt h s := by
    intro s hs
    apply MeromorphicAt.fun_sub (hMero s hs)
    suffices ∀ T : Finset ℂ,
        MeromorphicAt (fun z => ∑ s' ∈ T, residueAt f s' / (z - s')) s from this S0
    intro T; induction T using Finset.induction with
    | empty => simp only [Finset.sum_empty]; exact MeromorphicAt.const 0 s
    | insert a T' ha' ih =>
      rw [show (fun z => ∑ s' ∈ insert a T', residueAt f s' / (z - s')) =
          (fun z => residueAt f a / (z - a) + ∑ s' ∈ T', residueAt f s' / (z - s')) from
        funext fun z => Finset.sum_insert ha']
      exact ((MeromorphicAt.const (residueAt f a) s).fun_div
        ((MeromorphicAt.id s).fun_sub (MeromorphicAt.const a s))).fun_add ih
  exact tendsto_cpv_of_continuousOn_zero_integral S0 h γ hh_cont
    (h_finset_vanish S0 h h_mero_sum
      (fun s hs => residueAt_sub_residueSum_eq_zero S0 f s hs (hMero s hs))
      (hf.sub hfres_diff) hS0_in_U h_no_crossings)

private lemma assembly_crossings_case
    (U : Set ℂ) (hU : IsOpen U) (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  intro h; choose g_corr hg_corr_an hg_corr_eq using
    fun s (hs : s ∈ S0) => meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
  let h_pol : ℂ → ℂ := fun z =>
    ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s))
  let h_reg_nf : ℂ → ℂ := fun z => if hz : z ∈ S0 then
    g_corr z hz z - ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' z
    else f z - ∑ s ∈ S0, meromorphicPrincipalPart f s z
  have h_pol_cont := (ppMinusRes_sum_continuousOn_diff S0 f hMero).mono
    (fun z (⟨_, h⟩ : z ∈ U \ ↑S0) => (⟨Set.mem_univ z, h⟩ : z ∈ univ \ ↑S0))
  have h_reg_nf_diff_U : DifferentiableOn ℂ h_reg_nf U := by
    intro z hz; by_cases hz_S : z ∈ S0
    · exact regularPart_nf_differentiableOn_at_pole U hU S0 f hf hMero
        g_corr hg_corr_an hg_corr_eq z hz hz_S
    · exact ((Filter.EventuallyEq.differentiableAt_iff (f₁ := h_reg_nf)
        (Filter.Eventually.mono ((hU.sdiff S0.finite_toSet.isClosed).mem_nhds
          (⟨hz, fun hh => hz_S (Finset.mem_coe.mp hh)⟩ : z ∈ U \ ↑S0))
          (fun w ⟨_, hw⟩ => by simp only [h_reg_nf,
            show ¬(w ∈ S0) from fun hh => hw (Finset.mem_coe.mpr hh), dite_false]))).mp
        (regularPart_nf_differentiableOn_off_poles U hU S0 f hf hMero z hz hz_S).differentiableAt
          (hU.mem_nhds hz)).differentiableWithinAt
  have h_cpv_eq : ∀ ε > 0, ∀ t,
      cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t =
      cauchyPrincipalValueIntegrandOn S0 (fun z => h_reg_nf z + h_pol z) γ.toFun ε t := by
    intro ε hε t; simp only [cauchyPrincipalValueIntegrandOn]; split_ifs with h_near
    · rfl
    · push_neg at h_near; congr 1
      have hne : γ.toFun t ∉ (↑S0 : Set ℂ) := fun hmem => by
        have := h_near _ (Finset.mem_coe.mp hmem); rw [sub_self, norm_zero] at this; linarith
      simp only [h_reg_nf, dif_neg (fun hh => hne (Finset.mem_coe.mpr hh))]
      show f _ - ∑ s ∈ S0, residueAt f s / (_ - s) =
        (f _ - ∑ s ∈ S0, meromorphicPrincipalPart f s _) +
        ∑ s ∈ S0, (meromorphicPrincipalPart f s _ - residueAt f s / (_ - s))
      rw [Finset.sum_sub_distrib]; ring
  rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
  apply Filter.Tendsto.congr'
    _ ((tendsto_cpv_of_continuousOn_zero_integral S0 h_reg_nf γ
      (h_reg_nf_diff_U.continuousOn.mono (fun z ⟨t, ht, htz⟩ => htz ▸ hγ_in_U t ht))
      (h_holo_vanish h_reg_nf h_reg_nf_diff_U)).add (cpv_ppMinusRes_sum_tendsto_zero U hU S0 f hf
      γ hγ_closed hγ_in_U hMero hCondA hCondB h_no_endpt h_unique_cross hS0_in_U
      h_holo_vanish h_finset_vanish))
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  rw [funext (h_cpv_eq ε hε), funext (cpvIntegrandOn_add S0 h_reg_nf h_pol γ.toFun ε)]
  exact (intervalIntegral.integral_add
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 h_reg_nf
      (h_reg_nf_diff_U.continuousOn.mono Set.diff_subset) γ hγ_in_U ε hε)
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 h_pol
      h_pol_cont γ hγ_in_U ε hε)).symm

theorem higherOrderCancel_assembly_abstract
    (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (h_holo_vanish : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g U →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0)
    (h_finset_vanish : ∀ (T : Finset ℂ) (g : ℂ → ℂ),
      (∀ s ∈ T, MeromorphicAt g s) → (∀ s ∈ T, residueAt g s = 0) →
      DifferentiableOn ℂ g (U \ ↑T) → (∀ s ∈ T, s ∈ U) →
      (∀ s ∈ T, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
  intro h
  have hfres_diff : DifferentiableOn ℂ
      (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) (U \ ↑S0) := by
    have h_eq : (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) =
        (∑ s ∈ S0, fun z => residueAt f s / (z - s)) := by
      ext z; simp [Finset.sum_apply]
    rw [h_eq]; apply DifferentiableOn.sum; intro s _
    apply DifferentiableOn.div (differentiableOn_const _)
      (differentiableOn_id.sub (differentiableOn_const _))
    intro z ⟨_, hz_not_S0⟩
    exact sub_ne_zero.mpr (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr ‹_›))
  by_cases h_no_crossings : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s
  · exact assembly_no_crossings_case U S0 f hf γ hγ_in_U hMero hS0_in_U
      h_finset_vanish h_no_crossings hfres_diff
  · push_neg at h_no_crossings; obtain ⟨_, _, _, _, _⟩ := h_no_crossings
    exact assembly_crossings_case U hU S0 f hf γ hγ_closed hγ_in_U hMero hCondA hCondB
      h_no_endpt h_unique_cross hS0_in_U h_holo_vanish h_finset_vanish

/-- Convex-set specialization of `higherOrderCancel_assembly_abstract`. -/
theorem higherOrderCancel_assembly
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) :=
  higherOrderCancel_assembly_abstract U hU S0 f hf γ hγ_closed hγ_in_U
    hMero hCondA hCondB _hγ_meas h_no_endpt h_unique_cross hS0_in_U
    (fun g hg => by
      have hU_ne : U.Nonempty :=
        ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr (le_of_lt γ.hab))⟩
      obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU hU_ne hg
      have h_Fγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) := fun t ht =>
        (hF (γ.toFun t) (hγ_in_U t ht)).continuousAt.continuousWithinAt.comp
          (γ.continuous_toFun t ht) (fun t' ht' => hγ_in_U t' ht')
      have h_deriv : ∀ t ∈ Ioo γ.a γ.b \ (↑γ.partition ∩ Ioo γ.a γ.b : Set ℝ),
          HasDerivAt (F ∘ γ.toFun) (g (γ.toFun t) * deriv γ.toFun t) t := by
        intro t ⟨ht, hp⟩; exact (hF (γ.toFun t) (hγ_in_U t (Ioo_subset_Icc_self ht))).comp_of_eq
          t ((γ.smooth_off_partition t (Ioo_subset_Icc_self ht)
            (fun hh => hp ⟨hh, ht⟩)).hasDerivAt) rfl
      have h_int : IntervalIntegrable
          (fun t => g (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b :=
        IntervalIntegrable.continuousOn_mul
          (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
            (piecewiseC1Immersion_deriv_bounded γ))
          (by rw [Set.uIcc_of_le (le_of_lt γ.hab)]
              exact hg.continuousOn.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht))
      have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
        (F ∘ γ.toFun) (fun t => g (γ.toFun t) * deriv γ.toFun t)
        (le_of_lt γ.hab) h_countable h_Fγ_cont h_deriv h_int
      rw [h_ftc, Function.comp_apply, Function.comp_apply,
        (hγ_closed : γ.toFun γ.a = γ.toFun γ.b), sub_self])
    (fun T g hg_mero hg_res hg_diff hT_in_U hg_avoids =>
      contourIntegral_eq_zero_of_meromorphic_residue_zero_finset T g
        hg_mero hg_res U hU hU_convex hg_diff hT_in_U γ hγ_closed hγ_in_U hg_avoids)

/-! ## L5: Assembly — conditions (A')+(B) imply higher-order cancellation

The main result: combine per-term vanishing over all Laurent terms and all
crossing points to show the global PV difference tends to 0.

Note: This uses `SatisfiesConditionA'` (variable-order flatness matching the
pole order) rather than `SatisfiesConditionA` (order 1 only). The paper's
Theorem 3.3 requires flatness of the pole order, which is stronger than
flatness of order 1 for higher-order poles. -/

/-- **Bridge Lemma:** Conditions (A') (flatness of pole order) and (B)
(angle/Laurent compatibility) from Hungerbühler-Wasem imply the higher-order
cancellation hypothesis `hHigherOrderCancel` needed by
`generalizedResidueTheorem_higher_order`.

The proof decomposes `f - f_res` near each crossing `s` into:
- **Analytic part** `g(z)`: bounded, its cutoff integral converges →
  cancels in the PV difference.
- **Higher-order polar terms** `aₖ/(z-s)^{k+1}` for `k ≥ 1`: each vanishes
  by `pv_higher_order_term_tendsto_zero`, using flatness of order `≥ k+1`
  (from condition A') and the angle condition `k · α ∈ 2πℤ` (from condition B).
Then sums over the finitely many crossings in `S0`. -/
theorem conditionsAB_imply_higherOrderCancel
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0) := by
  set h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s) with hh_def
  have h_integrand_eq : ∀ ε t,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
      cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t =
      cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t := by
    intro ε t
    exact cpvIntegrandOn_sub S0 f (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t
  suffices h_main : Tendsto
      (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) by
    apply h_main.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    symm
    have h_int_f : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε) volume γ.a γ.b :=
      intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
        U S0 f hf.continuousOn γ hγ_in_U ε hε
    have h_int_fres : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε)
        volume γ.a γ.b := by
      have hfres_cont : ContinuousOn (fun z => ∑ s ∈ S0, residueAt f s / (z - s))
          (U \ ↑S0) := by
        apply continuousOn_finset_sum; intro s _
        apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
        intro z ⟨_, hz_not_S0⟩
        exact sub_ne_zero.mpr
          (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr ‹_›))
      exact intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
        U S0 _ hfres_cont γ hγ_in_U ε hε
    rw [← intervalIntegral.integral_sub h_int_f h_int_fres]
    congr 1; ext t
    exact h_integrand_eq ε t
  exact higherOrderCancel_assembly U hU hU_convex S0 f hf γ hγ_closed hγ_in_U
    hMero hCondA hCondB hγ_meas h_no_endpt h_unique_cross hS0_in_U

end GeneralizedResidueTheory
