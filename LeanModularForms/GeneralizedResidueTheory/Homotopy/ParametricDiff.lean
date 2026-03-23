/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Parametric Differentiation for Homotopy Integrals

Lemmas for differentiating contour integrals under a C² homotopy
parameter, including the Schwarz theorem for mixed partial
derivatives and the key vanishing-derivative result used in
homotopy invariance of contour integrals.

## Main Results

* `intervalIntegral_continuous_on_param` — continuity of a
    parametric interval integral
* `schwarz_partialDeriv_comm` — mixed partials of a C² function
    commute
* `hasDerivAt_homotopy_integral_zero` — derivative of the
    homotopy integral vanishes when boundary s-derivatives are
    zero
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Continuity of a parametric interval integral. -/
theorem intervalIntegral_continuous_on_param
    (f : ℝ → ℝ → ℂ) (a b : ℝ) (S : Set ℝ) (hab : a ≤ b)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (_hf_int : ∀ s ∈ S,
      IntervalIntegrable (f · s) volume a b) :
    ContinuousOn (fun s => ∫ t in a..b, f t s) S := by
  intro s₀ _hs₀
  apply ContinuousAt.continuousWithinAt
  have hmeas : ∀ s,
      AEStronglyMeasurable (f · s)
        (volume.restrict (Set.uIoc a b)) := by
    intro s
    apply Continuous.aestronglyMeasurable
    exact hf_cont.comp
      (continuous_id.prodMk continuous_const)
  have hcont_pt : ∀ᵐ t ∂volume,
      t ∈ Set.uIoc a b →
        ContinuousAt (f t) s₀ := by
    filter_upwards with t _
    exact (hf_cont.comp
      (continuous_const.prodMk continuous_id)).continuousAt
  have hcompact :
      IsCompact (Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1)) :=
    isCompact_Icc.prod isCompact_Icc
  have hbound : ∃ M : ℝ,
      ∀ p ∈ Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1),
        ‖(fun p => f p.1 p.2) p‖ ≤ M :=
    hcompact.exists_bound_of_continuousOn
      hf_cont.continuousOn
  obtain ⟨M, hM⟩ := hbound
  apply intervalIntegral.continuousAt_of_dominated_interval
  · filter_upwards with s; exact hmeas s
  · have h_nhd : Ioo (s₀ - 1) (s₀ + 1) ∈ 𝓝 s₀ := by
      apply Ioo_mem_nhds <;> linarith
    filter_upwards [h_nhd] with s hs
    filter_upwards with t
    intro ht
    by_cases htab : t ∈ Icc a b
    · exact hM (t, s)
        ⟨htab, le_of_lt hs.1, le_of_lt hs.2⟩
    · rw [Set.uIoc_of_le hab] at ht
      exact absurd (Ioc_subset_Icc_self ht) htab
  · exact intervalIntegrable_const
  · exact hcont_pt

lemma contDiff_partialDeriv_snd_of_contDiff_two
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      deriv (fun s => H (p.1, s)) p.2) := by
  have h1 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ H p) :=
    hH.fderiv_right le_rfl
  have h2 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ H p) (0, 1)) :=
    h1.clm_apply contDiff_const
  convert h2 using 1
  ext p
  have hH_diff : Differentiable ℝ H :=
    hH.differentiable
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have h_emb_diff :
      DifferentiableAt ℝ (fun s : ℝ => (p.1, s)) p.2 :=
    (differentiableAt_const p.1).prodMk differentiableAt_id
  show deriv (fun s => H (p.1, s)) p.2 =
    fderiv ℝ H p (0, 1)
  have h_deriv_emb :
      deriv (fun s => (p.1, s)) p.2 = (0, 1) := by
    have : HasDerivAt (fun s => (p.1, s)) (0, 1) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk
        (hasDerivAt_id p.2)
    exact this.deriv
  calc deriv (fun s => H (p.1, s)) p.2
      = (fderiv ℝ H (p.1, p.2))
          (deriv (fun s => (p.1, s)) p.2) := by
        apply fderiv_comp_deriv p.2
          (hH_diff (p.1, p.2)) h_emb_diff
    _ = (fderiv ℝ H p) (0, 1) := by
        rw [h_deriv_emb]

lemma contDiff_partialDeriv_fst_of_contDiff_two
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ =>
      deriv (fun t => H (t, p.2)) p.1) := by
  have h1 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ H p) :=
    hH.fderiv_right le_rfl
  have h2 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => (fderiv ℝ H p) (1, 0)) :=
    h1.clm_apply contDiff_const
  convert h2 using 1
  ext p
  have hH_diff : Differentiable ℝ H :=
    hH.differentiable
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have h_emb_diff :
      DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
    differentiableAt_id.prodMk (differentiableAt_const p.2)
  show deriv (fun t => H (t, p.2)) p.1 =
    fderiv ℝ H p (1, 0)
  have h_deriv_emb :
      deriv (fun t => (t, p.2)) p.1 = (1, 0) := by
    have : HasDerivAt (fun t => (t, p.2)) (1, 0) p.1 :=
      (hasDerivAt_id p.1).prodMk
        (hasDerivAt_const p.1 p.2)
    exact this.deriv
  calc deriv (fun t => H (t, p.2)) p.1
      = (fderiv ℝ H (p.1, p.2))
          (deriv (fun t => (t, p.2)) p.1) := by
        apply fderiv_comp_deriv p.1
          (hH_diff (p.1, p.2)) h_emb_diff
    _ = (fderiv ℝ H p) (1, 0) := by
        rw [h_deriv_emb]

/-- Schwarz theorem: mixed partials of a C² function commute. -/
lemma schwarz_partialDeriv_comm
    (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) :
    deriv (fun s' =>
      deriv (fun t' => H (t', s')) t) s =
    deriv (fun t' =>
      deriv (fun s' => H (t', s')) s) t := by
  have h_symm : IsSymmSndFDerivAt ℝ H (t, s) :=
    (hH.contDiffAt).isSymmSndFDerivAt (by simp)
  have hH_diff : Differentiable ℝ H :=
    hH.differentiable
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hH1 : ContDiff ℝ 1
      (fun p : ℝ × ℝ => fderiv ℝ H p) :=
    hH.fderiv_right le_rfl
  have hfH : Differentiable ℝ (fun p => fderiv ℝ H p) :=
    hH1.differentiable le_rfl
  have h_inner_t : ∀ s',
      deriv (fun t' => H (t', s')) t =
        fderiv ℝ H (t, s') (1, 0) := fun s' => by
    have h_emb :
        DifferentiableAt ℝ (fun t' : ℝ => (t', s')) t :=
      differentiableAt_id.prodMk
        (differentiableAt_const s')
    have h_has_deriv :
        HasDerivAt (fun t' => (t', s')) (1, 0) t := by
      have h1 : HasDerivAt (fun t' => t') 1 t :=
        hasDerivAt_id t
      have h2 : HasDerivAt (fun _ : ℝ => s') 0 t :=
        hasDerivAt_const t s'
      exact h1.prodMk h2
    calc deriv (fun t' => H (t', s')) t
        = (fderiv ℝ H (t, s'))
            (deriv (fun t' => (t', s')) t) :=
          fderiv_comp_deriv t (hH_diff (t, s')) h_emb
      _ = (fderiv ℝ H (t, s')) (1, 0) := by
          rw [h_has_deriv.deriv]
  have h_inner_s : ∀ t',
      deriv (fun s' => H (t', s')) s =
        fderiv ℝ H (t', s) (0, 1) := fun t' => by
    have h_emb :
        DifferentiableAt ℝ (fun s' : ℝ => (t', s')) s :=
      (differentiableAt_const t').prodMk differentiableAt_id
    have h_has_deriv :
        HasDerivAt (fun s' => (t', s')) (0, 1) s := by
      have h1 : HasDerivAt (fun _ : ℝ => t') 0 s :=
        hasDerivAt_const s t'
      have h2 : HasDerivAt (fun s' => s') 1 s :=
        hasDerivAt_id s
      exact h1.prodMk h2
    calc deriv (fun s' => H (t', s')) s
        = (fderiv ℝ H (t', s))
            (deriv (fun s' => (t', s')) s) :=
          fderiv_comp_deriv s (hH_diff (t', s)) h_emb
      _ = (fderiv ℝ H (t', s)) (0, 1) := by
          rw [h_has_deriv.deriv]
  simp_rw [h_inner_t, h_inner_s]
  have h_emb_s :
      DifferentiableAt ℝ (fun s' : ℝ => (t, s')) s :=
    (differentiableAt_const t).prodMk differentiableAt_id
  have h_deriv_emb_s :
      deriv (fun s' => (t, s')) s = (0, 1) := by
    have h1 : HasDerivAt (fun _ : ℝ => t) (0 : ℝ) s :=
      hasDerivAt_const s t
    have h2 : HasDerivAt (fun s' : ℝ => s') (1 : ℝ) s :=
      hasDerivAt_id s
    exact (HasDerivAt.prodMk h1 h2).deriv
  have h_emb_t :
      DifferentiableAt ℝ (fun t' : ℝ => (t', s)) t :=
    differentiableAt_id.prodMk (differentiableAt_const s)
  have h_deriv_emb_t :
      deriv (fun t' => (t', s)) t = (1, 0) := by
    have h1 : HasDerivAt (fun t' : ℝ => t') (1 : ℝ) t :=
      hasDerivAt_id t
    have h2 : HasDerivAt (fun _ : ℝ => s) (0 : ℝ) t :=
      hasDerivAt_const t s
    exact (HasDerivAt.prodMk h1 h2).deriv
  have hLHS :
      deriv (fun s' =>
        (fderiv ℝ H (t, s')) (1, 0)) s =
      (fderiv ℝ (fun p => fderiv ℝ H p) (t, s))
        (0, 1) (1, 0) := by
    have h_clm_diff :
        DifferentiableAt ℝ
          (fun s' => fderiv ℝ H (t, s')) s :=
      (hfH (t, s)).comp s h_emb_s
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : ℝ => (1, 0) : ℝ → ℝ × ℝ) s :=
      differentiableAt_const (1, 0)
    rw [deriv_clm_apply h_clm_diff h_const_diff]
    simp only [deriv_const, map_zero, add_zero]
    have h_comp :
        (fun s' => fderiv ℝ H (t, s')) =
          (fun p => fderiv ℝ H p) ∘
            (fun s' => (t, s')) := rfl
    rw [h_comp,
      fderiv_comp_deriv s (hfH (t, s)) h_emb_s,
      h_deriv_emb_s]
  have hRHS :
      deriv (fun t' =>
        (fderiv ℝ H (t', s)) (0, 1)) t =
      (fderiv ℝ (fun p => fderiv ℝ H p) (t, s))
        (1, 0) (0, 1) := by
    have h_clm_diff :
        DifferentiableAt ℝ
          (fun t' => fderiv ℝ H (t', s)) t :=
      (hfH (t, s)).comp t h_emb_t
    have h_const_diff :
        DifferentiableAt ℝ
          (fun _ : ℝ => (0, 1) : ℝ → ℝ × ℝ) t :=
      differentiableAt_const (0, 1)
    rw [deriv_clm_apply h_clm_diff h_const_diff]
    simp only [deriv_const, map_zero, add_zero]
    have h_comp :
        (fun t' => fderiv ℝ H (t', s)) =
          (fun p => fderiv ℝ H p) ∘
            (fun t' => (t', s)) := rfl
    rw [h_comp,
      fderiv_comp_deriv t (hfH (t, s)) h_emb_t,
      h_deriv_emb_t]
  rw [hLHS, hRHS]
  exact h_symm.eq (0, 1) (1, 0)

private lemma differentiableAt_mul_of_contDiff
    (g : ℝ → ℂ) (h : ℝ → ℂ) (t : ℝ)
    (hg : DifferentiableAt ℝ g t)
    (hh : ContDiff ℝ 1 h) :
    DifferentiableAt ℝ (fun t' => g t' * h t') t :=
  hg.mul (hh.differentiable le_rfl t)

private lemma differentiableAt_comp_of_holomorphic
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (t s : ℝ)
    (hH : ContDiff ℝ 2 H)
    (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ
      (fun t' => f (H (t', s))) t := by
  have hH_diff :
      DifferentiableAt ℝ (fun t' => H (t', s)) t := by
    have h := hH.differentiable
      (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    exact DifferentiableAt.comp t (h (t, s))
      (differentiableAt_id.prodMk
        (differentiableAt_const s))
  exact (hf.restrictScalars ℝ).comp t hH_diff

set_option maxHeartbeats 1600000 in
/-- Derivative of the homotopy integral vanishes. -/
theorem hasDerivAt_homotopy_integral_zero
    (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ)
    (hab : a < b)
    (hH_smooth : ContDiff ℝ 2 H)
    (hf_diff : ∀ t ∈ Icc a b,
      ∀ s' ∈ Icc (0:ℝ) 1,
        DifferentiableAt ℂ f (H (t, s')))
    (hfH_cont : Continuous (f ∘ H))
    (hs : s ∈ Set.Icc 0 1)
    (hderiv_a :
      deriv (fun s' => H (a, s')) s = 0)
    (hderiv_b :
      deriv (fun s' => H (b, s')) s = 0)
    (hf_differentiable : Differentiable ℂ f) :
    HasDerivAt
      (fun s' => ∫ t in a..b,
        f (H (t, s')) *
          deriv (fun t' => H (t', s')) t) 0 s := by
  let F : ℝ → ℝ → ℂ := fun s' t =>
    f (H (t, s')) *
      deriv (fun t' => H (t', s')) t
  let J : ℝ → ℝ → ℂ := fun t s' =>
    f (H (t, s')) *
      deriv (fun s'' => H (t, s'')) s'
  have hJ_a : J a s = 0 := by
    simp only [J, hderiv_a, mul_zero]
  have hJ_b : J b s = 0 := by
    simp only [J, hderiv_b, mul_zero]
  have h_boundary : J b s - J a s = 0 := by
    simp only [hJ_a, hJ_b, sub_zero]
  have h_deriv :
      HasDerivAt (fun s' => ∫ t in a..b, F s' t)
        (J b s - J a s) s := by
    have hJ_diff_t : ∀ t ∈ Icc a b,
        DifferentiableAt ℝ (fun t' => J t' s) t := by
      intro t ht
      simp only [J]
      have hH_diff : Differentiable ℝ H :=
        hH_smooth.differentiable
          (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
      have h_emb :
          DifferentiableAt ℝ
            (fun t' : ℝ => (t', s)) t :=
        differentiableAt_id.prodMk
          (differentiableAt_const s)
      have hH_t :
          DifferentiableAt ℝ
            (fun t' => H (t', s)) t :=
        (hH_diff (t, s)).comp t h_emb
      have hf_at :
          DifferentiableAt ℂ f (H (t, s)) :=
        hf_diff t ht s hs
      have hfH_diff :
          DifferentiableAt ℝ
            (fun t' => f (H (t', s))) t :=
        (hf_at.restrictScalars ℝ).comp t hH_t
      have h_partialS :
          ContDiff ℝ 1 (fun p : ℝ × ℝ =>
            deriv (fun s'' => H (p.1, s'')) p.2) :=
        contDiff_partialDeriv_snd_of_contDiff_two
          H hH_smooth
      have h_partial_diff :
          DifferentiableAt ℝ
            (fun t' =>
              deriv (fun s'' => H (t', s'')) s) t := by
        have h_comp :
            (fun t' =>
              deriv (fun s'' => H (t', s'')) s) =
              (fun p : ℝ × ℝ =>
                deriv (fun s'' => H (p.1, s'')) p.2) ∘
                  (fun t' => (t', s)) := rfl
        rw [h_comp]
        exact (h_partialS.differentiable le_rfl (t, s)).comp
          t h_emb
      exact hfH_diff.mul h_partial_diff
    have hJ_deriv_cont :
        ContinuousOn (fun t =>
          deriv (fun t' => J t' s) t) (Icc a b) := by
      have hH_diff : Differentiable ℝ H :=
        hH_smooth.differentiable
          (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
      have h_partialS :
          ContDiff ℝ 1 (fun p : ℝ × ℝ =>
            deriv (fun s'' => H (p.1, s'')) p.2) :=
        contDiff_partialDeriv_snd_of_contDiff_two
          H hH_smooth
      have h_partial_cont :
          Continuous (fun t =>
            deriv (fun s'' => H (t, s'')) s) :=
        h_partialS.continuous.comp
          (by continuity : Continuous (fun t => (t, s)))
      have h_partial_deriv_cont :
          Continuous (fun t =>
            deriv (fun t' =>
              deriv (fun s'' => H (t', s'')) s) t) := by
        have h_eq :
            (fun t => deriv (fun t' =>
              deriv (fun s'' => H (t', s'')) s) t) =
              deriv (fun t =>
                deriv (fun s'' => H (t, s'')) s) := rfl
        rw [h_eq]
        exact (h_partialS.comp
          (contDiff_id.prodMk contDiff_const) :
            ContDiff ℝ 1 _).continuous_deriv le_rfl
      have h_fH_cont :
          Continuous (fun t => f (H (t, s))) :=
        hfH_cont.comp
          (by continuity : Continuous (fun t => (t, s)))
      have h_deriv_eq : ∀ t ∈ Icc a b,
          deriv (fun t' => J t' s) t =
            deriv (fun t' => f (H (t', s))) t *
              deriv (fun s'' => H (t, s'')) s +
            f (H (t, s)) *
              deriv (fun t' =>
                deriv (fun s'' => H (t', s'')) s) t := by
        intro t ht
        simp only [J]
        have h_emb :
            DifferentiableAt ℝ
              (fun t' : ℝ => (t', s)) t :=
          differentiableAt_id.prodMk
            (differentiableAt_const s)
        have hfH_diff :
            DifferentiableAt ℝ
              (fun t' => f (H (t', s))) t := by
          have hH_t :
              DifferentiableAt ℝ
                (fun t' => H (t', s)) t :=
            (hH_diff (t, s)).comp t h_emb
          exact ((hf_diff t ht s hs).restrictScalars ℝ
            ).comp t hH_t
        have h_partial_diff :
            DifferentiableAt ℝ
              (fun t' =>
                deriv (fun s'' => H (t', s'')) s) t := by
          have h_comp :
              (fun t' =>
                deriv (fun s'' => H (t', s'')) s) =
                (fun p : ℝ × ℝ =>
                  deriv (fun s'' => H (p.1, s'')) p.2) ∘
                    (fun t' => (t', s)) := rfl
          rw [h_comp]
          exact (h_partialS.differentiable le_rfl
            (t, s)).comp t h_emb
        exact deriv_mul hfH_diff h_partial_diff
      suffices h_rhs_cont : ContinuousOn (fun t =>
          deriv (fun t' => f (H (t', s))) t *
            deriv (fun s'' => H (t, s'')) s +
          f (H (t, s)) *
            deriv (fun t' =>
              deriv (fun s'' => H (t', s'')) s) t)
          (Icc a b) by
        exact h_rhs_cont.congr
          (fun t ht => h_deriv_eq t ht)
      apply ContinuousOn.add
      · apply ContinuousOn.mul _
          h_partial_cont.continuousOn
        have h_partialT :
            ContDiff ℝ 1 (fun p : ℝ × ℝ =>
              deriv (fun t'' => H (t'', p.2)) p.1) :=
          contDiff_partialDeriv_fst_of_contDiff_two
            H hH_smooth
        have h_partialT_cont :
            Continuous (fun t =>
              deriv (fun t' => H (t', s)) t) :=
          h_partialT.continuous.comp
            (by continuity :
              Continuous (fun t => (t, s)))
        have h_chain : ∀ t ∈ Icc a b,
            deriv (fun t' => f (H (t', s))) t =
              deriv f (H (t, s)) *
                deriv (fun t' => H (t', s)) t := by
          intro t ht
          have h_emb :
              DifferentiableAt ℝ
                (fun t' : ℝ => (t', s)) t :=
            differentiableAt_id.prodMk
              (differentiableAt_const s)
          have hH_t :
              DifferentiableAt ℝ
                (fun t' => H (t', s)) t :=
            (hH_diff (t, s)).comp t h_emb
          have hf_at :
              DifferentiableAt ℂ f (H (t, s)) :=
            hf_diff t ht s hs
          have h_eq :
              (fun t' => f (H (t', s))) =
                f ∘ (fun t' => H (t', s)) := rfl
          rw [h_eq,
            deriv.scomp t hf_at hH_t,
            smul_eq_mul, mul_comm]
        suffices h_chain_cont : ContinuousOn (fun t =>
            deriv f (H (t, s)) *
              deriv (fun t' => H (t', s)) t)
            (Icc a b) by
          exact h_chain_cont.congr
            (fun t ht => h_chain t ht)
        apply ContinuousOn.mul _
          h_partialT_cont.continuousOn
        apply Continuous.continuousOn
        have h_deriv_f_cont :
            Continuous (deriv f ∘ H) := by
          have := hf_differentiable.contDiff (n := ⊤)
          exact (this.continuous_deriv le_top).comp
            hH_smooth.continuous
        exact h_deriv_f_cont.comp
          (by continuity :
            Continuous (fun t => (t, s)))
      · exact (h_fH_cont.mul
          h_partial_deriv_cont).continuousOn
    have h_ftc :
        ∫ t in a..b,
          deriv (fun t' => J t' s) t =
            J b s - J a s := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        have hab' : a ≤ b := le_of_lt hab
        have ha_mem : a ∈ Icc a b :=
          ⟨le_refl a, hab'⟩
        have hb_mem : b ∈ Icc a b :=
          ⟨hab', le_refl b⟩
        have h_mem : t ∈ Icc a b :=
          Set.uIcc_subset_Icc ha_mem hb_mem ht
        exact (hJ_diff_t t h_mem).hasDerivAt
      · exact ContinuousOn.intervalIntegrable_of_Icc
          (le_of_lt hab) hJ_deriv_cont
    have h_schwarz : ∀ t ∈ Ioo a b,
        deriv (fun s' => F s' t) s =
          deriv (fun t' => J t' s) t := by
      intro t ht
      have hH_diff : Differentiable ℝ H :=
        hH_smooth.differentiable
          (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
      have h_partialS :
          ContDiff ℝ 1 (fun p : ℝ × ℝ =>
            deriv (fun s'' => H (p.1, s'')) p.2) :=
        contDiff_partialDeriv_snd_of_contDiff_two
          H hH_smooth
      have h_partialT :
          ContDiff ℝ 1 (fun p : ℝ × ℝ =>
            deriv (fun t'' => H (t'', p.2)) p.1) :=
        contDiff_partialDeriv_fst_of_contDiff_two
          H hH_smooth
      have ht_mem : t ∈ Icc a b :=
        Ioo_subset_Icc_self ht
      have h_mixed :
          deriv (fun s' =>
            deriv (fun t' => H (t', s')) t) s =
          deriv (fun t' =>
            deriv (fun s' => H (t', s')) s) t :=
        schwarz_partialDeriv_comm H hH_smooth t s
      simp only [F, J]
      have h_emb_s :
          DifferentiableAt ℝ
            (fun s' : ℝ => (t, s')) s :=
        (differentiableAt_const t).prodMk
          differentiableAt_id
      have h_emb_t :
          DifferentiableAt ℝ
            (fun t' : ℝ => (t', s)) t :=
        differentiableAt_id.prodMk
          (differentiableAt_const s)
      have hfH_diff_s :
          DifferentiableAt ℝ
            (fun s' => f (H (t, s'))) s := by
        have hH_s :
            DifferentiableAt ℝ
              (fun s' => H (t, s')) s :=
          (hH_diff (t, s)).comp s h_emb_s
        exact ((hf_diff t ht_mem s hs
          ).restrictScalars ℝ).comp s hH_s
      have hfH_diff_t :
          DifferentiableAt ℝ
            (fun t' => f (H (t', s))) t := by
        have hH_t :
            DifferentiableAt ℝ
              (fun t' => H (t', s)) t :=
          (hH_diff (t, s)).comp t h_emb_t
        exact ((hf_diff t ht_mem s hs
          ).restrictScalars ℝ).comp t hH_t
      have h_partialT_diff_s :
          DifferentiableAt ℝ
            (fun s' =>
              deriv (fun t' => H (t', s')) t) s := by
        have h_comp :
            (fun s' =>
              deriv (fun t' => H (t', s')) t) =
              (fun p : ℝ × ℝ =>
                deriv (fun t' => H (t', p.2)) p.1) ∘
                  (fun s' => (t, s')) := rfl
        rw [h_comp]
        exact (h_partialT.differentiable le_rfl
          (t, s)).comp s h_emb_s
      have h_partialS_diff_t :
          DifferentiableAt ℝ
            (fun t' =>
              deriv (fun s' => H (t', s')) s) t := by
        have h_comp :
            (fun t' =>
              deriv (fun s' => H (t', s')) s) =
              (fun p : ℝ × ℝ =>
                deriv (fun s' => H (p.1, s')) p.2) ∘
                  (fun t' => (t', s)) := rfl
        rw [h_comp]
        exact (h_partialS.differentiable le_rfl
          (t, s)).comp t h_emb_t
      have hf_at :
          DifferentiableAt ℂ f (H (t, s)) :=
        hf_diff t ht_mem s hs
      have hH_s :
          DifferentiableAt ℝ
            (fun s' => H (t, s')) s :=
        (hH_diff (t, s)).comp s h_emb_s
      have hH_t :
          DifferentiableAt ℝ
            (fun t' => H (t', s)) t :=
        (hH_diff (t, s)).comp t h_emb_t
      have hLHS :
          deriv (fun s' =>
            f (H (t, s')) *
              deriv (fun t' => H (t', s')) t) s =
            deriv (fun s' => f (H (t, s'))) s *
              deriv (fun t' => H (t', s)) t +
            f (H (t, s)) *
              deriv (fun s' =>
                deriv (fun t' => H (t', s')) t) s := by
        show deriv ((fun s' => f (H (t, s'))) *
          (fun s' =>
            deriv (fun t' => H (t', s')) t)) s =
          deriv (fun s' => f (H (t, s'))) s *
            deriv (fun t' => H (t', s)) t +
          f (H (t, s)) *
            deriv (fun s' =>
              deriv (fun t' => H (t', s')) t) s
        rw [deriv_mul hfH_diff_s h_partialT_diff_s]
      have hRHS :
          deriv (fun t' =>
            f (H (t', s)) *
              deriv (fun s'' => H (t', s'')) s) t =
            deriv (fun t' => f (H (t', s))) t *
              deriv (fun s' => H (t, s')) s +
            f (H (t, s)) *
              deriv (fun t' =>
                deriv (fun s' => H (t', s')) s) t := by
        show deriv ((fun t' => f (H (t', s))) *
          (fun t' =>
            deriv (fun s' => H (t', s')) s)) t =
          deriv (fun t' => f (H (t', s))) t *
            deriv (fun s' => H (t, s')) s +
          f (H (t, s)) *
            deriv (fun t' =>
              deriv (fun s' => H (t', s')) s) t
        rw [deriv_mul hfH_diff_t h_partialS_diff_t]
      have h_chain_s :
          deriv (fun s' => f (H (t, s'))) s =
            deriv f (H (t, s)) *
              deriv (fun s' => H (t, s')) s := by
        have h_eq :
            (fun s' => f (H (t, s'))) =
              f ∘ (fun s' => H (t, s')) := rfl
        rw [h_eq,
          deriv.scomp s hf_at hH_s,
          smul_eq_mul, mul_comm]
      have h_chain_t :
          deriv (fun t' => f (H (t', s))) t =
            deriv f (H (t, s)) *
              deriv (fun t' => H (t', s)) t := by
        have h_eq :
            (fun t' => f (H (t', s))) =
              f ∘ (fun t' => H (t', s)) := rfl
        rw [h_eq,
          deriv.scomp t hf_at hH_t,
          smul_eq_mul, mul_comm]
      rw [hLHS, hRHS, h_chain_s, h_chain_t, h_mixed]
      ring
    have h_param :
        HasDerivAt (fun s' => ∫ t in a..b, F s' t)
          (∫ t in a..b,
            deriv (fun t' => J t' s) t) s := by
      have hH_diff : Differentiable ℝ H :=
        hH_smooth.differentiable
          (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
      have h_partialT :
          ContDiff ℝ 1 (fun p : ℝ × ℝ =>
            deriv (fun t'' => H (t'', p.2)) p.1) :=
        contDiff_partialDeriv_fst_of_contDiff_two
          H hH_smooth
      have h_partialS :
          ContDiff ℝ 1 (fun p : ℝ × ℝ =>
            deriv (fun s'' => H (p.1, s'')) p.2) :=
        contDiff_partialDeriv_snd_of_contDiff_two
          H hH_smooth
      have h_integral_eq :
          ∫ t in a..b,
            deriv (fun s' => F s' t) s =
          ∫ t in a..b,
            deriv (fun t' => J t' s) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht
        rw [Set.uIoc_of_le (le_of_lt hab)] at ht
        by_cases htb : t = b
        · have hb_mem : b ∈ Icc a b :=
            ⟨le_of_lt hab, le_refl b⟩
          have h_emb_s :
              DifferentiableAt ℝ
                (fun s' : ℝ => (t, s')) s :=
            (differentiableAt_const t).prodMk
              differentiableAt_id
          have h_emb_t :
              DifferentiableAt ℝ
                (fun t' : ℝ => (t', s)) t :=
            differentiableAt_id.prodMk
              (differentiableAt_const s)
          have ht_mem : t ∈ Icc a b := by
            rw [htb]; exact hb_mem
          have hfH_diff_s :
              DifferentiableAt ℝ
                (fun s' => f (H (t, s'))) s := by
            have hH_s :
                DifferentiableAt ℝ
                  (fun s' => H (t, s')) s :=
              (hH_diff (t, s)).comp s h_emb_s
            exact ((hf_diff t ht_mem s hs
              ).restrictScalars ℝ).comp s hH_s
          have hfH_diff_t :
              DifferentiableAt ℝ
                (fun t' => f (H (t', s))) t := by
            have hH_t :
                DifferentiableAt ℝ
                  (fun t' => H (t', s)) t :=
              (hH_diff (t, s)).comp t h_emb_t
            exact ((hf_diff t ht_mem s hs
              ).restrictScalars ℝ).comp t hH_t
          have h_partialT_diff_s :
              DifferentiableAt ℝ (fun s' =>
                deriv (fun t' => H (t', s')) t) s := by
            have h_comp :
                (fun s' =>
                  deriv (fun t' => H (t', s')) t) =
                  (fun p : ℝ × ℝ =>
                    deriv (fun t' =>
                      H (t', p.2)) p.1) ∘
                      (fun s' => (t, s')) := rfl
            rw [h_comp]
            exact (h_partialT.differentiable le_rfl
              (t, s)).comp s h_emb_s
          have h_partialS_diff_t :
              DifferentiableAt ℝ (fun t' =>
                deriv (fun s' => H (t', s')) s) t := by
            have h_comp :
                (fun t' =>
                  deriv (fun s' => H (t', s')) s) =
                  (fun p : ℝ × ℝ =>
                    deriv (fun s' =>
                      H (p.1, s')) p.2) ∘
                      (fun t' => (t', s)) := rfl
            rw [h_comp]
            exact (h_partialS.differentiable le_rfl
              (t, s)).comp t h_emb_t
          have h_mixed :
              deriv (fun s' =>
                deriv (fun t' => H (t', s')) t) s =
              deriv (fun t' =>
                deriv (fun s' => H (t', s')) s) t :=
            schwarz_partialDeriv_comm H hH_smooth t s
          simp only [F, J]
          have hf_at :
              DifferentiableAt ℂ f (H (t, s)) :=
            hf_diff t ht_mem s hs
          have hH_s :
              DifferentiableAt ℝ
                (fun s' => H (t, s')) s :=
            (hH_diff (t, s)).comp s h_emb_s
          have hH_t :
              DifferentiableAt ℝ
                (fun t' => H (t', s)) t :=
            (hH_diff (t, s)).comp t h_emb_t
          have hLHS :
              deriv (fun s' =>
                f (H (t, s')) *
                  deriv (fun t' => H (t', s')) t) s =
                deriv (fun s' => f (H (t, s'))) s *
                  deriv (fun t' => H (t', s)) t +
                f (H (t, s)) *
                  deriv (fun s' =>
                    deriv (fun t' =>
                      H (t', s')) t) s := by
            show deriv ((fun s' => f (H (t, s'))) *
              (fun s' =>
                deriv (fun t' =>
                  H (t', s')) t)) s =
              deriv (fun s' => f (H (t, s'))) s *
                deriv (fun t' => H (t', s)) t +
              f (H (t, s)) *
                deriv (fun s' =>
                  deriv (fun t' =>
                    H (t', s')) t) s
            rw [deriv_mul hfH_diff_s
              h_partialT_diff_s]
          have hRHS :
              deriv (fun t' =>
                f (H (t', s)) *
                  deriv (fun s'' =>
                    H (t', s'')) s) t =
                deriv (fun t' =>
                  f (H (t', s))) t *
                  deriv (fun s' => H (t, s')) s +
                f (H (t, s)) *
                  deriv (fun t' =>
                    deriv (fun s' =>
                      H (t', s')) s) t := by
            show deriv ((fun t' => f (H (t', s))) *
              (fun t' =>
                deriv (fun s' =>
                  H (t', s')) s)) t =
              deriv (fun t' =>
                f (H (t', s))) t *
                deriv (fun s' => H (t, s')) s +
              f (H (t, s)) *
                deriv (fun t' =>
                  deriv (fun s' =>
                    H (t', s')) s) t
            rw [deriv_mul hfH_diff_t
              h_partialS_diff_t]
          have h_chain_s :
              deriv (fun s' =>
                f (H (t, s'))) s =
                deriv f (H (t, s)) *
                  deriv (fun s' => H (t, s')) s := by
            have h_eq :
                (fun s' => f (H (t, s'))) =
                  f ∘ (fun s' => H (t, s')) := rfl
            rw [h_eq,
              deriv.scomp s hf_at hH_s,
              smul_eq_mul, mul_comm]
          have h_chain_t :
              deriv (fun t' =>
                f (H (t', s))) t =
                deriv f (H (t, s)) *
                  deriv (fun t' => H (t', s)) t := by
            have h_eq :
                (fun t' => f (H (t', s))) =
                  f ∘ (fun t' => H (t', s)) := rfl
            rw [h_eq,
              deriv.scomp t hf_at hH_t,
              smul_eq_mul, mul_comm]
          rw [hLHS, hRHS,
            h_chain_s, h_chain_t, h_mixed]
          ring
        · have ht_Ioo : t ∈ Set.Ioo a b :=
            ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
          exact h_schwarz t ht_Ioo
      let ε : ℝ := 1 / 4
      have hε_pos : (0 : ℝ) < ε := by norm_num
      have h_embed_t :
          Continuous (fun t : ℝ => (t, s)) :=
        continuous_id.prodMk continuous_const
      have hF_meas : ∀ᶠ s' in 𝓝 s,
          AEStronglyMeasurable (F s')
            (volume.restrict (Ι a b)) := by
        filter_upwards [Filter.univ_mem] with s' _
        apply Continuous.aestronglyMeasurable
        have h_embed_s' :
            Continuous (fun t : ℝ => (t, s')) :=
          continuous_id.prodMk continuous_const
        have h1 :
            Continuous (fun t => f (H (t, s'))) :=
          hfH_cont.comp h_embed_s'
        have h2 :
            Continuous (fun t =>
              deriv (fun t' => H (t', s')) t) :=
          h_partialT.continuous.comp h_embed_s'
        exact h1.mul h2
      have hF_int :
          IntervalIntegrable (F s) volume a b := by
        apply Continuous.intervalIntegrable
        have h1 :
            Continuous (fun t => f (H (t, s))) :=
          hfH_cont.comp h_embed_t
        have h2 :
            Continuous (fun t =>
              deriv (fun t' => H (t', s)) t) :=
          h_partialT.continuous.comp h_embed_t
        exact h1.mul h2
      have h_F'_cont :
          Continuous (fun p : ℝ × ℝ =>
            deriv (fun s'' => F s'' p.1) p.2) := by
        have h_fH' :
            Continuous (fun p : ℝ × ℝ =>
              f (H (p.1, p.2))) := hfH_cont
        have h_derivf' :
            Continuous (fun p : ℝ × ℝ =>
              deriv f (H (p.1, p.2))) := by
          have := hf_differentiable.contDiff (n := ⊤)
          exact (this.continuous_deriv le_top).comp
            hH_smooth.continuous
        have h_partialS' :
            Continuous (fun p : ℝ × ℝ =>
              deriv (fun s' => H (p.1, s')) p.2) :=
          h_partialS.continuous
        have h_partialT' :
            Continuous (fun p : ℝ × ℝ =>
              deriv (fun t' => H (t', p.2)) p.1) :=
          h_partialT.continuous
        have h_mixed' :
            Continuous (fun p : ℝ × ℝ =>
              deriv (fun s' =>
                deriv (fun t' =>
                  H (t', s')) p.1) p.2) := by
          have h_eq :
              (fun p : ℝ × ℝ =>
                deriv (fun s' =>
                  deriv (fun t' =>
                    H (t', s')) p.1) p.2) =
              (fun p : ℝ × ℝ =>
                fderiv ℝ (fun p' : ℝ × ℝ =>
                  deriv (fun t' =>
                    H (t', p'.2)) p'.1) p
                      (0, 1)) := by
            ext p
            have hg_diff :
                Differentiable ℝ (fun p' : ℝ × ℝ =>
                  deriv (fun t' =>
                    H (t', p'.2)) p'.1) :=
              h_partialT.differentiable le_rfl
            have h_emb_diff :
                DifferentiableAt ℝ
                  (fun s' : ℝ => (p.1, s')) p.2 :=
              (differentiableAt_const p.1).prodMk
                differentiableAt_id
            have h_deriv_emb :
                deriv (fun s' => (p.1, s')) p.2 =
                  (0, 1) := by
              have :
                  HasDerivAt (fun s' => (p.1, s'))
                    (0, 1) p.2 :=
                (hasDerivAt_const p.2 p.1).prodMk
                  (hasDerivAt_id p.2)
              exact this.deriv
            calc deriv (fun s' =>
                  deriv (fun t' =>
                    H (t', s')) p.1) p.2
                = deriv ((fun p' : ℝ × ℝ =>
                    deriv (fun t' =>
                      H (t', p'.2)) p'.1) ∘
                    (fun s' => (p.1, s'))) p.2 := rfl
              _ = (fderiv ℝ (fun p' =>
                    deriv (fun t' =>
                      H (t', p'.2)) p'.1) p)
                    (deriv (fun s' =>
                      (p.1, s')) p.2) := by
                  apply fderiv_comp_deriv p.2
                    (hg_diff p) h_emb_diff
              _ = (fderiv ℝ (fun p' =>
                    deriv (fun t' =>
                      H (t', p'.2)) p'.1) p)
                    (0, 1) := by rw [h_deriv_emb]
          rw [h_eq]
          have h_fderiv_cont :
              Continuous (fun p : ℝ × ℝ =>
                fderiv ℝ (fun p' =>
                  deriv (fun t' =>
                    H (t', p'.2)) p'.1) p) :=
            h_partialT.continuous_fderiv le_rfl
          exact h_fderiv_cont.clm_apply
            continuous_const
        have hF'_eq : ∀ t s',
            deriv (fun s'' => F s'' t) s' =
              deriv f (H (t, s')) *
                deriv (fun s'' => H (t, s'')) s' *
                deriv (fun t' => H (t', s')) t +
              f (H (t, s')) *
                deriv (fun s'' =>
                  deriv (fun t' =>
                    H (t', s'')) t) s' := by
          intro t s'
          simp only [F]
          have h_emb_s' :
              DifferentiableAt ℝ
                (fun s'' : ℝ => (t, s'')) s' :=
            (differentiableAt_const t).prodMk
              differentiableAt_id
          have hH_diff_s' :
              DifferentiableAt ℝ
                (fun s'' => H (t, s'')) s' :=
            (hH_diff (t, s')).comp s' h_emb_s'
          have hfH_diff_s' :
              DifferentiableAt ℝ
                (fun s'' => f (H (t, s''))) s' := by
            exact (hf_differentiable (H (t, s'))
              |>.restrictScalars ℝ).comp s'
                hH_diff_s'
          have h_partialT_diff_s' :
              DifferentiableAt ℝ
                (fun s'' =>
                  deriv (fun t' =>
                    H (t', s'')) t) s' := by
            have h_comp :
                (fun s'' =>
                  deriv (fun t' =>
                    H (t', s'')) t) =
                  (fun p : ℝ × ℝ =>
                    deriv (fun t' =>
                      H (t', p.2)) p.1) ∘
                      (fun s'' => (t, s'')) := rfl
            rw [h_comp]
            exact (h_partialT.differentiable le_rfl
              (t, s')).comp s' h_emb_s'
          show deriv ((fun s'' => f (H (t, s''))) *
            (fun s'' =>
              deriv (fun t' =>
                H (t', s'')) t)) s' =
            deriv f (H (t, s')) *
              deriv (fun s'' => H (t, s'')) s' *
              deriv (fun t' => H (t', s')) t +
            f (H (t, s')) *
              deriv (fun s'' =>
                deriv (fun t' =>
                  H (t', s'')) t) s'
          rw [deriv_mul hfH_diff_s'
            h_partialT_diff_s']
          have h_chain :
              deriv (fun s'' =>
                f (H (t, s''))) s' =
                deriv f (H (t, s')) *
                  deriv (fun s'' =>
                    H (t, s'')) s' := by
            have h_eq :
                (fun s'' => f (H (t, s''))) =
                  f ∘ (fun s'' => H (t, s'')) := rfl
            rw [h_eq,
              deriv.scomp s'
                (hf_differentiable (H (t, s')))
                hH_diff_s',
              smul_eq_mul, mul_comm]
          simp only [h_chain, mul_assoc]
        have hF'_fun_eq :
            (fun p : ℝ × ℝ =>
              deriv (fun s'' => F s'' p.1) p.2) =
            (fun p : ℝ × ℝ =>
              deriv f (H (p.1, p.2)) *
                deriv (fun s'' =>
                  H (p.1, s'')) p.2 *
                deriv (fun t' =>
                  H (t', p.2)) p.1 +
              f (H (p.1, p.2)) *
                deriv (fun s'' =>
                  deriv (fun t' =>
                    H (t', s'')) p.1) p.2) := by
          ext ⟨t, s'⟩; exact hF'_eq t s'
        rw [hF'_fun_eq]
        exact ((h_derivf'.mul h_partialS').mul
          h_partialT').add (h_fH'.mul h_mixed')
      have h_uIoc_subset :
          (Ι a b : Set ℝ) ⊆ Icc a b :=
        Set.uIoc_subset_uIcc.trans
          (Set.uIcc_of_le (le_of_lt hab)).subset
      have hF'_meas :
          AEStronglyMeasurable
            (fun t =>
              deriv (fun s' => F s' t) s)
            (volume.restrict (Ι a b)) := by
        have h_cont :
            Continuous (fun t =>
              deriv (fun s' => F s' t) s) :=
          h_F'_cont.comp
            (continuous_id.prodMk continuous_const)
        exact h_cont.aestronglyMeasurable
      let K : Set (ℝ × ℝ) :=
        Icc a b ×ˢ Icc (s - ε) (s + ε)
      have hK_compact : IsCompact K :=
        isCompact_Icc.prod isCompact_Icc
      have hK_ne : K.Nonempty :=
        ⟨(a, s),
          left_mem_Icc.mpr (le_of_lt hab),
          by constructor <;> linarith⟩
      obtain ⟨M_pt, hM_pt_mem, hM_pt_max⟩ :=
        hK_compact.exists_isMaxOn hK_ne
          (continuous_norm.comp
            h_F'_cont).continuousOn
      let M : ℝ :=
        ‖deriv (fun s'' => F s'' M_pt.1) M_pt.2‖
      have h_ball_subset :
          Metric.ball s ε ⊆ Icc (s - ε) (s + ε) := by
        intro x hx
        simp only [Metric.mem_ball,
          Real.dist_eq] at hx
        constructor <;> linarith [abs_lt.mp hx]
      have h_bound : ∀ᵐ t ∂volume,
          t ∈ Ι a b →
            ∀ s' ∈ Metric.ball s ε,
              ‖deriv (fun s'' => F s'' t) s'‖ ≤
                M := by
        filter_upwards with t ht s' hs'
        have ht_Icc : t ∈ Icc a b :=
          h_uIoc_subset ht
        have hs'_Icc :
            s' ∈ Icc (s - ε) (s + ε) :=
          h_ball_subset hs'
        have h_mem_K : (t, s') ∈ K :=
          ⟨ht_Icc, hs'_Icc⟩
        have h_le := hM_pt_max h_mem_K
        simp only [Set.mem_setOf_eq,
          Function.comp_apply] at h_le
        exact h_le
      have h_bound_int :
          IntervalIntegrable (fun _ => M) volume a b :=
        intervalIntegrable_const
      have h_diff : ∀ᵐ t ∂volume,
          t ∈ Ι a b →
            ∀ s' ∈ Metric.ball s ε,
              HasDerivAt (fun s'' => F s'' t)
                (deriv (fun s'' => F s'' t) s')
                s' := by
        filter_upwards with t _ht s' _hs'
        have h_emb_s' :
            DifferentiableAt ℝ
              (fun s'' : ℝ => (t, s'')) s' :=
          (differentiableAt_const t).prodMk
            differentiableAt_id
        have hH_diff_s' :
            DifferentiableAt ℝ
              (fun s'' => H (t, s'')) s' :=
          (hH_diff (t, s')).comp s' h_emb_s'
        have hfH_diff_s' :
            DifferentiableAt ℝ
              (fun s'' => f (H (t, s''))) s' := by
          exact (hf_differentiable (H (t, s'))
            |>.restrictScalars ℝ).comp s'
              hH_diff_s'
        have h_partialT_diff_s' :
            DifferentiableAt ℝ
              (fun s'' =>
                deriv (fun t' =>
                  H (t', s'')) t) s' := by
          have h_comp :
              (fun s'' =>
                deriv (fun t' =>
                  H (t', s'')) t) =
                (fun p : ℝ × ℝ =>
                  deriv (fun t' =>
                    H (t', p.2)) p.1) ∘
                    (fun s'' => (t, s'')) := rfl
          rw [h_comp]
          exact (h_partialT.differentiable le_rfl
            (t, s')).comp s' h_emb_s'
        exact (hfH_diff_s'.mul
          h_partialT_diff_s').hasDerivAt
      have h_param :=
        intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
          hε_pos hF_meas hF_int hF'_meas
          h_bound h_bound_int h_diff
      rw [← h_integral_eq]
      exact h_param.2
    rw [h_ftc] at h_param
    exact h_param
  rw [h_boundary] at h_deriv
  exact h_deriv

end
