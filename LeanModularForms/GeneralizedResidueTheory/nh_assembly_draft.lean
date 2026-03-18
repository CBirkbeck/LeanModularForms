private theorem higherOrderCancel_assembly_nh
    (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U)
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
      (𝓝[>] 0) (𝓝 0) := by
  intro h
  have hh_cont : ContinuousOn h (U \ ↑S0) := by
    apply ContinuousOn.sub (hf.continuousOn)
    apply continuousOn_finset_sum; intro s hs
    apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
    intro z ⟨_, hz_not_S0⟩
    exact sub_ne_zero.mpr (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs))
  have h_uncrossed_pos_dist : ∀ s ∈ S0,
      (∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) →
      ∃ d > 0, ∀ t ∈ Icc γ.a γ.b, d ≤ ‖γ.toFun t - s‖ := by
    intro s _ h_ne
    have h_ne_zero : ∀ t ∈ Icc γ.a γ.b, (0 : ℝ) < ‖γ.toFun t - s‖ :=
      fun t ht => norm_pos_iff.mpr (sub_ne_zero.mpr (h_ne t ht))
    have h_cont : ContinuousOn (fun t => ‖γ.toFun t - s‖) (Icc γ.a γ.b) :=
      (γ.continuous_toFun.sub continuousOn_const).norm
    have h_ne_empty : (Icc γ.a γ.b).Nonempty :=
      ⟨γ.a, left_mem_Icc.mpr (le_of_lt γ.hab)⟩
    have h_compact : IsCompact (Icc γ.a γ.b) := isCompact_Icc
    obtain ⟨t_min, ht_min, h_min⟩ := h_compact.exists_isMinOn h_ne_empty h_cont
    exact ⟨‖γ.toFun t_min - s‖, h_ne_zero t_min ht_min,
      fun t ht => h_min ht⟩
  have hfres_diff : DifferentiableOn ℂ
      (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) (U \ ↑S0) := by
    have h_eq : (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) =
        (∑ s ∈ S0, fun z => residueAt f s / (z - s)) := by
      ext z; simp [Finset.sum_apply]
    rw [h_eq]
    apply DifferentiableOn.sum; intro s _
    apply DifferentiableOn.div (differentiableOn_const _)
      (differentiableOn_id.sub (differentiableOn_const _))
    intro z ⟨_, hz_not_S0⟩
    exact sub_ne_zero.mpr (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr ‹_›))
  have hh_diff : DifferentiableOn ℂ h (U \ ↑S0) := hf.sub hfres_diff
  by_cases h_no_crossings : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s
  · have h_image_sub : γ.toFun '' Icc γ.a γ.b ⊆ U \ ↑S0 := by
      intro z ⟨t, ht, htz⟩; subst htz
      exact ⟨h_null.image_subset t ht, fun hz_S0 =>
        h_no_crossings _ (Finset.mem_coe.mp hz_S0) t ht rfl⟩
    have hh_cont_image : ContinuousOn h (γ.toFun '' Icc γ.a γ.b) :=
      hh_cont.mono h_image_sub
    have h_integral_zero : ∫ t in γ.a..γ.b, h (γ.toFun t) * deriv γ.toFun t = 0 := by
      apply contourIntegral_eq_zero_of_meromorphic_residue_zero_finset S0 h
      · intro s hs
        apply MeromorphicAt.fun_sub (hMero s hs)
        suffices ∀ (T : Finset ℂ),
            MeromorphicAt (fun z => ∑ s' ∈ T, residueAt f s' / (z - s')) s by
          exact this S0
        intro T
        induction T using Finset.induction with
        | empty =>
          simp only [Finset.sum_empty]
          exact MeromorphicAt.const 0 s
        | insert a T' ha' ih =>
          have h_eq : (fun z => ∑ s' ∈ insert a T', residueAt f s' / (z - s')) =
              (fun z => residueAt f a / (z - a) + ∑ s' ∈ T', residueAt f s' / (z - s')) := by
            ext z; exact Finset.sum_insert ha'
          rw [h_eq]
          exact ((MeromorphicAt.const (residueAt f a) s).fun_div
            ((MeromorphicAt.id s).fun_sub (MeromorphicAt.const a s))).fun_add ih
      · intro s hs
        exact residueAt_sub_residueSum_eq_zero S0 f s hs (hMero s hs)
      · exact hU
      · exact contourIntegral_eq_zero_of_nullHomologous hU (hh_diff.mono (Set.diff_subset.trans le_rfl)) γ h_null
      · exact hh_diff
      · intro s hs; exact hS0_in_U s hs
      · exact h_null.closed
      · exact h_null.image_subset
      · exact fun s hs t ht => h_no_crossings s hs t ht
    exact tendsto_cpv_of_continuousOn_zero_integral S0 h γ
      hh_cont_image h_integral_zero
  · push_neg at h_no_crossings
    obtain ⟨s₀, hs₀, t₀, ht₀, hcross₀⟩ := h_no_crossings
    have h_crossed_in_Ioo : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s →
        t ∈ Ioo γ.a γ.b := by
      intro s hs t ht hcross
      have h_endpt := h_no_endpt s hs
      constructor
      · rcases lt_or_eq_of_le ht.1 with h | h
        · exact h
        · exact absurd (h ▸ hcross) h_endpt.1
      · rcases lt_or_eq_of_le ht.2 with h | h
        · exact h
        · exact absurd (h ▸ hcross) h_endpt.2
    have h_correction : ∀ s ∈ S0, ∃ (g_s : ℂ → ℂ), AnalyticAt ℂ g_s s ∧
        (∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_s z) := by
      intro s hs; exact meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
    choose g_corr hg_corr_an hg_corr_eq using h_correction
    let total_pp : ℂ → ℂ := fun z => ∑ s ∈ S0, meromorphicPrincipalPart f s z
    let h_reg : ℂ → ℂ := fun z => f z - total_pp z
    let h_pol : ℂ → ℂ := fun z =>
      ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s))
    let h_reg_nf : ℂ → ℂ := fun z =>
      if hz : z ∈ S0 then
        g_corr z hz z - ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' z
      else h_reg z
    have h_pol_cont : ContinuousOn h_pol (U \ ↑S0) := by
      apply continuousOn_finset_sum
      intro s hs
      apply ContinuousOn.sub
      · exact (meromorphicPrincipalPart_differentiableOn f s (hMero s hs)).continuousOn.mono
          (fun z hz => Set.mem_compl_singleton_iff.mpr
            (fun heq => by subst heq; exact hz.2 (Finset.mem_coe.mpr hs)))
      · apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
        intro z ⟨_, hz_not_S0⟩
        exact sub_ne_zero.mpr (fun heq => by
          subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs))
    have h_reg_nf_diff_U : DifferentiableOn ℂ h_reg_nf U := by
      intro z hz
      by_cases hz_S : z ∈ S0
      · have h_other_pp_diff : DifferentiableAt ℂ
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
        have h_S_minus_z_closed : IsClosed ((↑(S0.erase z) : Set ℂ)) :=
          (S0.erase z).finite_toSet.isClosed
        have hz_not_erase : z ∉ (↑(S0.erase z) : Set ℂ) :=
          fun hh => (Finset.notMem_erase z S0) (Finset.mem_coe.mp hh)
        have h_compl_open : IsOpen (↑(S0.erase z) : Set ℂ)ᶜ :=
          h_S_minus_z_closed.isOpen_compl
        have hz_in_compl : z ∈ (↑(S0.erase z) : Set ℂ)ᶜ :=
          Set.mem_compl hz_not_erase
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
          · have hw_eq : w = z := by
              by_contra hne
              exact hw_compl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hw_S⟩))
            rw [hw_eq]; simp [hz_S]
          · have hw_ne_z : w ≠ z := fun heq => hw_S (heq ▸ hz_S)
            have h_fw : f w - meromorphicPrincipalPart f z w = g_corr z hz_S w :=
              hV_eq ⟨hw_V, hw_ne_z⟩
            simp only [dif_neg hw_S, h_reg, total_pp]
            rw [show (∑ s ∈ S0, meromorphicPrincipalPart f s w) =
                meromorphicPrincipalPart f z w +
                ∑ s' ∈ S0.erase z, meromorphicPrincipalPart f s' w from
              (Finset.add_sum_erase S0 _ hz_S).symm,
              ← h_fw]
            ring
        exact (h_ev.differentiableAt_iff.mp h_corr_diff).differentiableWithinAt
      · have hz_punct : z ∈ U \ ↑S0 := ⟨hz, fun hh => hz_S (Finset.mem_coe.mp hh)⟩
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
        have h_reg_diff : DifferentiableAt ℂ h_reg z := hf_da.sub htp_da
        have h_ev : h_reg =ᶠ[𝓝 z] h_reg_nf := by
          apply Filter.Eventually.mono (hU_S_open.mem_nhds hz_punct)
          intro w ⟨_, hw_not_S⟩
          have hw_not_S' : w ∉ S0 := fun hh => hw_not_S (Finset.mem_coe.mpr hh)
          simp only [h_reg_nf, hw_not_S', dite_false]
        exact (h_ev.differentiableAt_iff.mp h_reg_diff).differentiableWithinAt
    have h_reg_nf_cont : ContinuousOn h_reg_nf (γ.toFun '' Icc γ.a γ.b) :=
      h_reg_nf_diff_U.continuousOn.mono
        (fun z ⟨t, ht, htz⟩ => htz ▸ h_null.image_subset t ht)
    have hU_ne : U.Nonempty := ⟨s₀, hS0_in_U s₀ hs₀⟩
    have h_reg_nf_zero := contourIntegral_eq_zero_of_nullHomologous hU h_reg_nf_diff_U γ h_null
    have h_nf_zero := h_reg_nf_zero
    have h_reg_nf_cpv_zero : Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h_reg_nf γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) :=
      tendsto_cpv_of_continuousOn_zero_integral S0 h_reg_nf γ h_reg_nf_cont h_nf_zero
    have h_agree : ∀ z ∈ U \ (↑S0 : Set ℂ), h z = h_reg_nf z + h_pol z := by
      intro z ⟨hz_U, hz_not_S0⟩
      have hz_not_S : z ∉ S0 := fun hh => hz_not_S0 (Finset.mem_coe.mpr hh)
      have h_nf_eq : h_reg_nf z = h_reg z := dif_neg hz_not_S
      have h_decomp : h z = h_reg z + h_pol z := by
        simp only [h, h_reg, h_pol, total_pp]
        rw [Finset.sum_sub_distrib]; ring
      rw [h_nf_eq]; exact h_decomp
    have h_fun_eq_off_S0 : ∀ z, z ∉ (↑S0 : Set ℂ) →
        h z = h_reg_nf z + h_pol z := by
      intro z hz_not_S0
      have hz_not_S : z ∉ S0 := fun hh => hz_not_S0 (Finset.mem_coe.mpr hh)
      have h_nf_eq : h_reg_nf z = h_reg z := dif_neg hz_not_S
      have h_decomp : h z = h_reg z + h_pol z := by
        change f z - ∑ s ∈ S0, residueAt f s / (z - s) =
          (f z - ∑ s ∈ S0, meromorphicPrincipalPart f s z) +
          ∑ s ∈ S0, (meromorphicPrincipalPart f s z - residueAt f s / (z - s))
        rw [Finset.sum_sub_distrib]; ring
      rw [h_nf_eq]; exact h_decomp
    have h_cpv_eq : ∀ ε > 0, ∀ t,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t =
        cauchyPrincipalValueIntegrandOn S0 (fun z => h_reg_nf z + h_pol z) γ.toFun ε t := by
      intro ε hε t
      simp only [cauchyPrincipalValueIntegrandOn]
      split_ifs with h_near
      · rfl
      · push_neg at h_near
        have hγt_not_S0 : (γ.toFun t) ∉ (↑S0 : Set ℂ) := by
          intro hmem
          have hmem' := Finset.mem_coe.mp hmem
          have := h_near (γ.toFun t) hmem'
          rw [sub_self, norm_zero] at this
          linarith
        congr 1
        exact h_fun_eq_off_S0 (γ.toFun t) hγt_not_S0
    have h_pol_tendsto : Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h_pol γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) := by
      have h_cpv_sum : ∀ ε t,
          cauchyPrincipalValueIntegrandOn S0 h_pol γ.toFun ε t =
          ∑ s ∈ S0, cauchyPrincipalValueIntegrandOn S0
            (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
            γ.toFun ε t :=
        fun ε t => cpvIntegrandOn_finset_sum S0 S0
          (fun s z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
          γ.toFun ε t
      have h_per_s_cont : ∀ s ∈ S0,
          ContinuousOn (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
            (U \ ↑S0) := by
        intro s hs
        apply ContinuousOn.sub
        · exact (meromorphicPrincipalPart_differentiableOn f s (hMero s hs)).continuousOn.mono
            (fun z hz => Set.mem_compl_singleton_iff.mpr
              (fun heq => by subst heq; exact hz.2 (Finset.mem_coe.mpr hs)))
        · apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
          intro z ⟨_, hz_not_S0⟩
          exact sub_ne_zero.mpr (fun heq => by
            subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs))
      have h_per_s_int : ∀ s ∈ S0, ∀ ε > 0,
          IntervalIntegrable
            (cauchyPrincipalValueIntegrandOn S0
              (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
              γ.toFun ε)
            volume γ.a γ.b := by
        intro s hs ε hε
        exact intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 _
          (h_per_s_cont s hs) γ h_null.image_subset ε hε
      have h_int_sum : ∀ ε > 0,
          ∫ t in γ.a..γ.b,
            cauchyPrincipalValueIntegrandOn S0 h_pol γ.toFun ε t =
          ∑ s ∈ S0, ∫ t in γ.a..γ.b,
            cauchyPrincipalValueIntegrandOn S0
              (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
              γ.toFun ε t := by
        intro ε hε
        rw [show (fun t => cauchyPrincipalValueIntegrandOn S0 h_pol γ.toFun ε t) =
            (fun t => ∑ s ∈ S0, cauchyPrincipalValueIntegrandOn S0
              (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
              γ.toFun ε t) from funext (h_cpv_sum ε)]
        exact intervalIntegral.integral_finset_sum
          (fun s _hs => h_per_s_int s _hs ε hε)
      have h_per_s_tendsto : ∀ s ∈ S0,
          Tendsto (fun ε => ∫ t in γ.a..γ.b,
            cauchyPrincipalValueIntegrandOn S0
              (fun z => meromorphicPrincipalPart f s z - residueAt f s / (z - s))
              γ.toFun ε t)
          (𝓝[>] 0) (𝓝 0) := by
        intro s hs
        set term_s : ℂ → ℂ := fun z =>
          meromorphicPrincipalPart f s z - residueAt f s / (z - s) with hterm_s_def
        by_cases h_crossed : ∃ t ∈ Icc γ.a γ.b, γ.toFun t = s
        · obtain ⟨t₁, ht₁, hcross₁⟩ := h_crossed
          have ht₁_Ioo := h_crossed_in_Ioo s hs t₁ ht₁ hcross₁
          obtain ⟨N_s, a_s, g_loc, hg_loc_an, hf_eq_loc, h_angle⟩ :=
            hCondB.laurent_compatible s hs t₁ ht₁ hcross₁ ht₁_Ioo
          have h_flat_s : IsFlatOfOrder γ.toFun t₁ (poleOrderAt f s) :=
            hCondA s hs t₁ ht₁ hcross₁ ht₁_Ioo
          have h_unique_s : ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → t = t₁ :=
            fun t ht hc => h_unique_cross s hs t ht t₁ ht₁ hc hcross₁
          rcases Nat.eq_zero_or_pos N_s with hN_s_zero | hN_s_pos
          · subst hN_s_zero
            have hf_tends : Tendsto f (𝓝[≠] s) (𝓝 (g_loc s)) := by
              apply Filter.Tendsto.congr'
              · filter_upwards [hf_eq_loc] with z hz
                simp only [Finset.univ_eq_empty, Finset.sum_empty,
                  add_zero] at hz
                exact hz.symm
              · exact hg_loc_an.continuousAt.tendsto.mono_left
                  nhdsWithin_le_nhds
            have h_ord_nn : 0 ≤ meromorphicOrderAt f s :=
              (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hMero s hs)).mp
                ⟨g_loc s, hf_tends⟩
            have h_pp_zero : meromorphicPrincipalPart f s = fun _ => 0 := by
              unfold meromorphicPrincipalPart
              exact dif_neg (fun h => absurd h.2 (not_lt.mpr h_ord_nn))
            have h_res_zero : residueAt f s = 0 := by
              unfold residueAt
              apply Filter.Tendsto.limUnder_eq
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
                have h_in : z ∈ Metric.ball s rf ∩ {s}ᶜ :=
                  ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf),
                   Set.mem_compl_singleton_iff.mpr hne⟩
                have := hrf_eq h_in
                simp only [Finset.univ_eq_empty, Finset.sum_empty,
                  add_zero] at this
                exact this
              have hg_cont : ContinuousOn g_loc (Metric.closedBall s r) :=
                hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
              have hg_diff : DifferentiableOn ℂ g_loc (Metric.ball s r) := by
                intro z hz; exact (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)
                  ).differentiableAt.differentiableWithinAt
              have hg_ci_zero : (∮ z in C(s, r), g_loc z) = 0 :=
                Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
                  hr_pos.le Set.countable_empty hg_cont
                  (fun z ⟨hz, _⟩ => hg_diff.differentiableAt
                    (Metric.isOpen_ball.mem_nhds hz))
              have hf_ci : (∮ z in C(s, r), f z) =
                  (∮ z in C(s, r), g_loc z) :=
                circleIntegral.integral_congr hr_pos.le h_eq_on
              simp [hf_ci, hg_ci_zero]
            have h_term_eq_zero : term_s = fun _ => 0 := by
              ext z; simp only [hterm_s_def, h_pp_zero, h_res_zero]
              simp [zero_div]
            rw [h_term_eq_zero]
            simp only [cauchyPrincipalValueIntegrandOn, zero_mul, ite_self]
            simp [intervalIntegral.integral_zero]
          · have h_a0_eq : a_s ⟨0, hN_s_pos⟩ = residueAt f s :=
              (residueAt_eq_laurent_head_coeff f s N_s hN_s_pos a_s g_loc
                hg_loc_an hf_eq_loc).symm
            have h_polar_term_tendsto : ∀ (k : Fin N_s), k.val ≥ 1 →
                Tendsto (fun ε => ∫ t in γ.a..γ.b,
                  cauchyPrincipalValueIntegrandOn S0
                    (fun z => a_s k / (z - s) ^ (k.val + 1))
                    γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
              intro ⟨kv, hkv⟩ hk_ge
              simp at hk_ge
              have hm : 2 ≤ kv + 1 := by omega
              by_cases ha_zero : a_s ⟨kv, hkv⟩ = 0
              · have h_zero : ∀ ε t, cauchyPrincipalValueIntegrandOn S0
                    (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
                    γ.toFun ε t = 0 := by
                  intro ε t; simp only [cauchyPrincipalValueIntegrandOn, ha_zero,
                    zero_div, zero_mul, ite_self]
                simp only [show (fun ε => ∫ t in γ.a..γ.b,
                    cauchyPrincipalValueIntegrandOn S0
                      (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
                      γ.toFun ε t) = fun _ => 0 from
                  funext fun ε => by
                    rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
                        (fun z => a_s ⟨kv, hkv⟩ / (z - s) ^ (kv + 1))
                        γ.toFun ε t) = fun _ => 0 from funext (h_zero ε)]
                    exact intervalIntegral.integral_zero]
                exact tendsto_const_nhds
              · have h_order_bound : kv + 1 ≤ poleOrderAt f s := by
                  unfold poleOrderAt
                  have hf_mero := hMero s hs
                  let nonzero_idx := (Finset.univ : Finset (Fin N_s)).filter
                    (fun k => a_s k ≠ 0)
                  have h_ne : nonzero_idx.Nonempty :=
                    ⟨⟨kv, hkv⟩, Finset.mem_filter.mpr
                      ⟨Finset.mem_univ _, ha_zero⟩⟩
                  set m_idx := (nonzero_idx.max' h_ne) with hm_def
                  have hm_ne : a_s m_idx ≠ 0 :=
                    (Finset.mem_filter.mp (nonzero_idx.max'_mem h_ne)).2
                  have hkv_le_m : kv ≤ m_idx.val :=
                    Finset.le_max' nonzero_idx ⟨kv, hkv⟩
                      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha_zero⟩)
                  have hm_max : ∀ k : Fin N_s, a_s k ≠ 0 → k ≤ m_idx :=
                    fun k hk => Finset.le_max' nonzero_idx k
                      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
                  suffices h_ord : meromorphicOrderAt f s =
                      ↑(-(↑(m_idx.val + 1) : ℤ)) by
                    rw [h_ord]; simp only [WithTop.untop₀_coe, neg_neg, Int.toNat_natCast]
                    omega
                  rw [meromorphicOrderAt_eq_int_iff hf_mero]
                  refine ⟨fun z => (z - s) ^ (m_idx.val + 1) * g_loc z +
                    ∑ k : Fin N_s, a_s k * (z - s) ^ (m_idx.val - k.val), ?_, ?_, ?_⟩
                  · exact ((analyticAt_id.sub analyticAt_const).pow _).mul hg_loc_an |>.add
                      (Finset.analyticAt_fun_sum Finset.univ
                        (fun k _ => analyticAt_const.mul
                          ((analyticAt_id.sub analyticAt_const).pow _)))
                  · simp only [sub_self, zero_pow (Nat.succ_ne_zero _), zero_mul, zero_add]
                    have : ∑ k : Fin N_s, a_s k * (0 : ℂ) ^ (m_idx.val - k.val) =
                        a_s m_idx := by
                      rw [Finset.sum_eq_single m_idx]
                      · simp
                      · intro k _ hk
                        by_cases hkm : k.val < m_idx.val
                        · simp [zero_pow (by omega : m_idx.val - k.val ≠ 0)]
                        · push_neg at hkm
                          have hk_gt : m_idx < k :=
                            lt_of_le_of_ne (Fin.mk_le_mk.mpr hkm) (Ne.symm hk)
                          have := hm_max k
                          have hk_eq : a_s k = 0 := by
                            by_contra ha; exact absurd (this ha) (not_le.mpr hk_gt)
                          simp only [hk_eq, zero_mul]
                      · intro h; exact absurd (Finset.mem_univ m_idx) h
                    rw [this]; exact hm_ne
                  · filter_upwards [hf_eq_loc, self_mem_nhdsWithin] with z hfz hz
                    rw [smul_eq_mul, hfz]
                    have hzs_ne : z - s ≠ 0 := sub_ne_zero.mpr hz
                    rw [mul_add, ← mul_assoc,
                      zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hzs_ne),
                      one_mul]
                    congr 1
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro k _
                    by_cases hk_le : k.val ≤ m_idx.val
                    · have hpow_k : (z - s) ^ (k.val + 1) ≠ 0 := pow_ne_zero _ hzs_ne
                      have hpow_m : (z - s) ^ (m_idx.val + 1) ≠ 0 := pow_ne_zero _ hzs_ne
                      field_simp
                      rw [mul_assoc (a_s k), ← pow_add,
                        show k.val + 1 + (m_idx.val - k.val) = m_idx.val + 1 from by omega]
                    · push_neg at hk_le
                      by_cases ha_k : a_s k = 0
                      · simp [ha_k]
                      · exact absurd (hm_max k ha_k) (not_le.mpr hk_le)
                have h_flat_k : IsFlatOfOrder γ.toFun t₁ (kv + 1) :=
                  IsFlatOfOrder.of_le h_flat_s h_order_bound
                    ((γ.continuous_toFun t₁
                      (Ioo_subset_Icc_self ht₁_Ioo)).continuousAt
                      (Icc_mem_nhds ht₁_Ioo.1 ht₁_Ioo.2))
                have h_angle_k : ∃ n : ℤ, ((kv + 1 - 1 : ℕ) : ℝ) *
                    _root_.angleAtCrossing γ t₁ ht₁_Ioo = ↑n * (2 * Real.pi) := by
                  rw [show (kv + 1 - 1 : ℕ) = kv from by omega]
                  exact h_angle ⟨kv, hkv⟩ ha_zero hk_ge
                have h_zpow := multipoint_pv_zpow_tendsto_zero S0 γ s (kv + 1) hm
                  hs t₁ ht₁_Ioo hcross₁ h_unique_s h_null.closed h_flat_k h_angle_k
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
                      ext z; rw [div_eq_mul_inv, zpow_neg, zpow_natCast, inv_eq_one_div,
                        one_div]
                    rw [this]; exact cpvIntegrandOn_const_smul S0 _ _ γ.toFun ε t]
                  exact intervalIntegral.integral_const_mul _ _
                rw [h_eq, show (0 : ℂ) = a_s ⟨kv, hkv⟩ * 0 from (mul_zero _).symm]
                exact Filter.Tendsto.const_smul h_zpow (a_s ⟨kv, hkv⟩)
            obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
              meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
            let polarHigher : ℂ → ℂ := fun z =>
              ∑ k : Fin N_s, if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0
            let err_loc : ℂ → ℂ := fun z => g_loc z - g_rp z
            have h_err_loc_an : AnalyticAt ℂ err_loc s := hg_loc_an.sub hg_rp_an
            let err_nf : ℂ → ℂ := fun z =>
              if z = s then err_loc s else term_s z - polarHigher z
            have h_off_s : ∀ z, z ≠ s → term_s z = err_nf z + polarHigher z := by
              intro z hz; simp only [err_nf, if_neg hz]; ring
            have h_ev : err_nf =ᶠ[𝓝 s] err_loc := by
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
                have hgrpz : f z - meromorphicPrincipalPart f s z = g_rp z :=
                  hr2_eq hz_in_2
                change meromorphicPrincipalPart f s z - residueAt f s / (z - s) -
                  (∑ k : Fin N_s, if k.val ≥ 1 then
                    a_s k / (z - s) ^ (k.val + 1) else 0) = g_loc z - g_rp z
                have hpp : meromorphicPrincipalPart f s z = f z - g_rp z := by
                  linear_combination -hgrpz
                rw [hpp, hfz]
                have h_sum_split : ∑ k : Fin N_s, a_s k / (z - s) ^ (k.val + 1) -
                    ∑ k : Fin N_s, (if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0) =
                    a_s ⟨0, hN_s_pos⟩ / (z - s) := by
                  rw [← Finset.sum_sub_distrib]
                  rw [Finset.sum_eq_single ⟨0, hN_s_pos⟩]
                  · simp
                  · intro k _ hk
                    have hkval : k.val ≥ 1 := by
                      by_contra h
                      push_neg at h
                      have : k.val = 0 := by omega
                      exact hk (Fin.ext this)
                    simp [hkval]
                  · intro h; exact absurd (Finset.mem_univ _) h
                rw [h_a0_eq] at h_sum_split
                linear_combination h_sum_split
            have h_err_nf_diff : DifferentiableOn ℂ err_nf U := by
              intro z hz
              by_cases hzs : z = s
              · rw [hzs]
                exact ((h_ev.differentiableAt_iff (𝕜 := ℂ)).mpr
                  h_err_loc_an.differentiableAt).differentiableWithinAt
              · have h_ev_z : err_nf =ᶠ[𝓝 z] fun w => term_s w - polarHigher w := by
                  rw [Filter.eventuallyEq_iff_exists_mem]
                  refine ⟨{s}ᶜ, IsOpen.mem_nhds isOpen_compl_singleton
                    (Set.mem_compl_singleton_iff.mpr hzs), fun w hw => ?_⟩
                  simp only [err_nf, if_neg (Set.mem_compl_singleton_iff.mp hw)]
                apply DifferentiableAt.differentiableWithinAt
                rw [h_ev_z.differentiableAt_iff]
                have h_term_diff : DifferentiableAt ℂ term_s z := by
                  apply DifferentiableAt.sub
                  · exact (meromorphicPrincipalPart_differentiableOn f s
                      (hMero s hs) z (Set.mem_compl_singleton_iff.mpr hzs)).differentiableAt
                      (IsOpen.mem_nhds isOpen_compl_singleton
                        (Set.mem_compl_singleton_iff.mpr hzs))
                  · exact (differentiableAt_const _).div
                      (differentiableAt_id.sub (differentiableAt_const _))
                      (sub_ne_zero.mpr hzs)
                have h_polar_diff : DifferentiableAt ℂ polarHigher z := by
                  have h_each : ∀ k : Fin N_s, DifferentiableAt ℂ
                      (fun w => if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) z := by
                    intro k
                    by_cases hk : k.val ≥ 1
                    · simp only [hk, ite_true]
                      exact (differentiableAt_const _).div
                        ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
                        (pow_ne_zero _ (sub_ne_zero.mpr hzs))
                    · simp only [hk, ite_false]
                      exact differentiableAt_const 0
                  change DifferentiableAt ℂ (fun w => ∑ k : Fin N_s,
                    if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) z
                  have h_eq_sum : (fun w => ∑ k : Fin N_s,
                      if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0) =
                    ∑ k : Fin N_s, fun w =>
                      if k.val ≥ 1 then a_s k / (w - s) ^ (k.val + 1) else 0 := by
                    ext w; simp [Finset.sum_apply]
                  rw [h_eq_sum]
                  exact DifferentiableAt.sum fun k _ => h_each k
                exact h_term_diff.sub h_polar_diff
            have h_err_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
                cauchyPrincipalValueIntegrandOn S0 err_nf γ.toFun ε t)
              (𝓝[>] 0) (𝓝 0) :=
              tendsto_cpv_of_continuousOn_zero_integral S0
                err_nf γ (h_err_nf_diff.continuousOn.mono
                  (fun z ⟨t, ht, htz⟩ => htz ▸ h_null.image_subset t ht))
                (contourIntegral_eq_zero_of_nullHomologous hU h_err_nf_diff γ h_null)
                err_nf h_err_nf_diff γ h_null.closed h_null.image_subset
            have h_polar_cpv : Tendsto (fun ε => ∫ t in γ.a..γ.b,
                cauchyPrincipalValueIntegrandOn S0 polarHigher γ.toFun ε t)
              (𝓝[>] 0) (𝓝 0) := by
              have h_cpv_decomp : ∀ ε t,
                  cauchyPrincipalValueIntegrandOn S0 polarHigher γ.toFun ε t =
                  ∑ k : Fin N_s, cauchyPrincipalValueIntegrandOn S0
                    (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
                    γ.toFun ε t :=
                fun ε t => cpvIntegrandOn_finset_sum S0 Finset.univ
                  (fun k z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
                  γ.toFun ε t
              have h_per_k_tendsto : ∀ k : Fin N_s,
                  Tendsto (fun ε => ∫ t in γ.a..γ.b,
                    cauchyPrincipalValueIntegrandOn S0
                      (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
                      γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
                intro k
                by_cases hk : k.val ≥ 1
                · have h_eq : (fun z => if k.val ≥ 1 then
                      a_s k / (z - s) ^ (k.val + 1) else 0) =
                    fun z => a_s k / (z - s) ^ (k.val + 1) := by
                    ext z; simp [hk]
                  simp_rw [h_eq]
                  exact h_polar_term_tendsto k hk
                · have h_eq : (fun z => if k.val ≥ 1 then
                      a_s k / (z - s) ^ (k.val + 1) else 0) =
                    fun _ => (0 : ℂ) := by
                    ext z; simp [hk]
                  simp_rw [h_eq, cauchyPrincipalValueIntegrandOn, zero_mul, ite_self,
                    intervalIntegral.integral_zero]
                  exact tendsto_const_nhds
              have h_per_k_int : ∀ (k : Fin N_s), ∀ ε > 0,
                  IntervalIntegrable
                    (cauchyPrincipalValueIntegrandOn S0
                      (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
                      γ.toFun ε) volume γ.a γ.b := by
                intro k ε hε
                apply intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0
                · by_cases hk : k.val ≥ 1
                  · simp only [hk, ite_true]
                    apply ContinuousOn.div continuousOn_const
                      ((continuousOn_id.sub continuousOn_const).pow _)
                    intro z ⟨_, hz_not_S0⟩
                    exact pow_ne_zero _ (sub_ne_zero.mpr
                      (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs)))
                  · simp only [hk, ite_false]
                    exact continuousOn_const
                · exact h_null.image_subset
                · exact hε
              have h_int_eq : ∀ ε > 0,
                  ∫ t in γ.a..γ.b,
                    cauchyPrincipalValueIntegrandOn S0 polarHigher γ.toFun ε t =
                  ∑ k : Fin N_s, ∫ t in γ.a..γ.b,
                    cauchyPrincipalValueIntegrandOn S0
                      (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
                      γ.toFun ε t := by
                intro ε hε
                rw [show (fun t => cauchyPrincipalValueIntegrandOn S0 polarHigher
                    γ.toFun ε t) = fun t => ∑ k : Fin N_s,
                    cauchyPrincipalValueIntegrandOn S0
                      (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
                      γ.toFun ε t from funext (h_cpv_decomp ε)]
                exact intervalIntegral.integral_finset_sum
                  (fun k _ => h_per_k_int k ε hε)
              have h_sum_tendsto : Tendsto (fun ε => ∑ k : Fin N_s,
                  ∫ t in γ.a..γ.b,
                    cauchyPrincipalValueIntegrandOn S0
                      (fun z => if k.val ≥ 1 then a_s k / (z - s) ^ (k.val + 1) else 0)
                      γ.toFun ε t) (𝓝[>] 0) (𝓝 0) := by
                have h0 : (0 : ℂ) = ∑ _k : Fin N_s, (0 : ℂ) :=
                  Finset.sum_const_zero.symm
                conv_rhs => rw [h0]
                exact tendsto_finset_sum Finset.univ (fun k _ => h_per_k_tendsto k)
              apply h_sum_tendsto.congr'
              filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
              exact (h_int_eq ε hε).symm
            rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
            apply Filter.Tendsto.congr' _ (h_err_cpv.add h_polar_cpv)
            filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
            have h_pw_eq : ∀ t, cauchyPrincipalValueIntegrandOn S0 term_s γ.toFun ε t =
                cauchyPrincipalValueIntegrandOn S0 (fun z => err_nf z + polarHigher z)
                  γ.toFun ε t := by
              intro t; simp only [cauchyPrincipalValueIntegrandOn]
              split_ifs with h_near
              · rfl
              · push_neg at h_near
                have hne : γ.toFun t ≠ s := fun heq => by
                  have := h_near s hs; rw [heq, sub_self, norm_zero] at this; linarith
                congr 1; exact h_off_s (γ.toFun t) hne
            rw [show (fun t => cauchyPrincipalValueIntegrandOn S0 term_s γ.toFun ε t) =
                fun t => cauchyPrincipalValueIntegrandOn S0
                  (fun z => err_nf z + polarHigher z) γ.toFun ε t from funext h_pw_eq]
            rw [show (fun t => cauchyPrincipalValueIntegrandOn S0
                  (fun z => err_nf z + polarHigher z) γ.toFun ε t) =
                fun t => cauchyPrincipalValueIntegrandOn S0 err_nf γ.toFun ε t +
                  cauchyPrincipalValueIntegrandOn S0 polarHigher γ.toFun ε t from
              funext (fun t => cpvIntegrandOn_add S0 err_nf polarHigher γ.toFun ε t)]
            exact (intervalIntegral.integral_add
              (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 err_nf
                (h_err_nf_diff.continuousOn.mono Set.diff_subset) γ h_null.image_subset ε hε)
              (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 polarHigher
                (by
                  apply continuousOn_finset_sum
                  intro k _
                  by_cases hk : k.val ≥ 1
                  · simp only [hk, ite_true]
                    apply ContinuousOn.div continuousOn_const
                      ((continuousOn_id.sub continuousOn_const).pow _)
                    intro z ⟨_, hz_not_S0⟩
                    exact pow_ne_zero _ (sub_ne_zero.mpr
                      (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr hs)))
                  · simp only [hk, ite_false]
                    exact continuousOn_const) γ h_null.image_subset ε hε)).symm
        · push_neg at h_crossed
          have h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s :=
            fun t ht => h_crossed t ht
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
            have h_term_res : residueAt term_s s = 0 := by
              have h_single := residueAt_sub_residueSum_eq_zero {s} f s
                (Finset.mem_singleton.mpr rfl) (hMero s hs)
              simp only [Finset.sum_singleton] at h_single
              obtain ⟨g_rp, hg_rp_an, hg_rp_eq⟩ :=
                meromorphicAt_sub_principalPart_eventually f s (hMero s hs)
              obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_rp_an.exists_ball_analyticOnNhd
              have h_ev_mem : {z | f z - meromorphicPrincipalPart f s z = g_rp z} ∈ 𝓝[≠] s :=
                hg_rp_eq
              rw [Metric.mem_nhdsWithin_iff] at h_ev_mem
              obtain ⟨rp, hrp_pos, hrp_eq⟩ := h_ev_mem
              set ρ' := min rg rp with hρ'_def
              have hρ'_pos : 0 < ρ' := lt_min hrg_pos hrp_pos
              have h_ci_agree : ∀ r, 0 < r → r < ρ' →
                  (∮ z in C(s, r), term_s z) =
                  (∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z) := by
                intro r hr_pos hr_lt
                have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
                have hr_lt_rp : r < rp := lt_of_lt_of_le hr_lt (min_le_right _ _)
                have h_eq_on : ∀ z ∈ Metric.sphere s r,
                    term_s z = (f z - residueAt f s / (z - s)) - g_rp z := by
                  intro z hz
                  have hne : z ≠ s := by
                    intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
                  have h_in : z ∈ Metric.ball s rp ∩ {s}ᶜ :=
                    ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; exact hr_lt_rp),
                     Set.mem_compl_singleton_iff.mpr hne⟩
                  have hfpp := hrp_eq h_in
                  simp only [Set.mem_setOf_eq] at hfpp
                  change meromorphicPrincipalPart f s z - residueAt f s / (z - s) =
                    f z - residueAt f s / (z - s) - g_rp z
                  linear_combination -hfpp
                have hg_cont : ContinuousOn g_rp (Metric.closedBall s r) :=
                  hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
                have hg_diff : DifferentiableOn ℂ g_rp (Metric.ball s r) := by
                  intro z hz
                  have := hg_ball z
                    (Metric.ball_subset_ball hr_lt_rg.le hz)
                  exact this.differentiableAt.differentiableWithinAt
                have hg_ci_zero : (∮ z in C(s, r), g_rp z) = 0 :=
                  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
                    hr_pos.le Set.countable_empty hg_cont
                    (fun z ⟨hz, _⟩ => hg_diff.differentiableAt
                      (Metric.isOpen_ball.mem_nhds hz))
                have hg_ci : CircleIntegrable g_rp s r :=
                  hg_cont.mono Metric.sphere_subset_closedBall |>.circleIntegrable hr_pos.le
                have h_sphere_sub : Metric.sphere s r ⊆ ({s}ᶜ : Set ℂ) := by
                  intro z hz heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
                have h_term_diff_compl : DifferentiableOn ℂ term_s ({s}ᶜ : Set ℂ) :=
                  DifferentiableOn.sub
                    (meromorphicPrincipalPart_differentiableOn f s (hMero s hs))
                    (DifferentiableOn.div (differentiableOn_const _)
                      (differentiableOn_id.sub (differentiableOn_const _))
                      (fun z hz => sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)))
                have h_term_ci : CircleIntegrable term_s s r :=
                  (h_term_diff_compl.continuousOn.mono h_sphere_sub).circleIntegrable hr_pos.le
                have h_add_ci : CircleIntegrable (fun z => term_s z + g_rp z) s r :=
                  h_term_ci.add hg_ci
                have h_split : (∮ z in C(s, r), (fun z => term_s z + g_rp z) z) =
                    (∮ z in C(s, r), term_s z) + (∮ z in C(s, r), g_rp z) :=
                  circleIntegral.integral_add h_term_ci hg_ci
                have h_sum_eq : ∀ z ∈ Metric.sphere s r,
                    (fun z => term_s z + g_rp z) z =
                    (fun z => f z - residueAt f s / (z - s)) z := by
                  intro z hz
                  have := h_eq_on z hz
                  simp only
                  linear_combination this
                have h_int_eq : (∮ z in C(s, r), (fun z => term_s z + g_rp z) z) =
                    (∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z) :=
                  circleIntegral.integral_congr hr_pos.le h_sum_eq
                calc (∮ z in C(s, r), term_s z)
                    = (∮ z in C(s, r), term_s z) + 0 := (add_zero _).symm
                  _ = (∮ z in C(s, r), term_s z) + (∮ z in C(s, r), g_rp z) := by
                      rw [hg_ci_zero]
                  _ = (∮ z in C(s, r), (fun z => term_s z + g_rp z) z) := h_split.symm
                  _ = (∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z) := h_int_eq
              rw [show residueAt term_s s =
                residueAt (fun z => f z - residueAt f s / (z - s)) s from by
                change limUnder (𝓝[>] (0 : ℝ))
                    (fun r => (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(s, r), term_s z) =
                  limUnder (𝓝[>] (0 : ℝ))
                    (fun r => (2 * ↑Real.pi * I)⁻¹ *
                      ∮ z in C(s, r), (fun z => f z - residueAt f s / (z - s)) z)
                unfold limUnder
                congr 1
                apply Filter.map_congr
                apply Filter.Eventually.mono (Ioo_mem_nhdsGT hρ'_pos)
                intro r ⟨hr_pos, hr_lt⟩
                simp only
                congr 1
                exact h_ci_agree r hr_pos hr_lt]
              exact h_single
            exact contourIntegral_eq_zero_of_nullHomologous hU
              (sorry /- term_s meromorphic + residue 0 → holomorphic on U -/) γ h_null
              h_term_diff (hS0_in_U s hs) γ h_null.closed h_null.image_subset h_avoids
          exact tendsto_cpv_of_continuousOn_zero_integral S0 term_s γ
            h_term_cont_image h_term_int_zero
      rw [show (0 : ℂ) = ∑ _s ∈ S0, (0 : ℂ) from (Finset.sum_const_zero).symm]
      apply Filter.Tendsto.congr'
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        exact (h_int_sum ε hε).symm
      · exact tendsto_finset_sum S0 (fun s hs => h_per_s_tendsto s hs)
    rw [show (0 : ℂ) = 0 + 0 from (add_zero 0).symm]
    apply Filter.Tendsto.congr' _ (h_reg_nf_cpv_zero.add h_pol_tendsto)
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    have h_eq_sum : (fun t => cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t) =
        (fun t => cauchyPrincipalValueIntegrandOn S0
          (fun z => h_reg_nf z + h_pol z) γ.toFun ε t) :=
      funext (fun t => h_cpv_eq ε hε t)
    have h_split : (fun t => cauchyPrincipalValueIntegrandOn S0
        (fun z => h_reg_nf z + h_pol z) γ.toFun ε t) =
        (fun t => cauchyPrincipalValueIntegrandOn S0 h_reg_nf γ.toFun ε t +
          cauchyPrincipalValueIntegrandOn S0 h_pol γ.toFun ε t) :=
      funext (fun t => cpvIntegrandOn_add S0 h_reg_nf h_pol γ.toFun ε t)
    have h_int_nf : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0 h_reg_nf γ.toFun ε) volume γ.a γ.b :=
      intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 h_reg_nf
        (h_reg_nf_diff_U.continuousOn.mono Set.diff_subset) γ h_null.image_subset ε hε
    have h_int_pol : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0 h_pol γ.toFun ε) volume γ.a γ.b :=
      intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff U S0 h_pol
        h_pol_cont γ h_null.image_subset ε hε
    rw [h_eq_sum, h_split]
    exact (intervalIntegral.integral_add h_int_nf h_int_pol).symm

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
