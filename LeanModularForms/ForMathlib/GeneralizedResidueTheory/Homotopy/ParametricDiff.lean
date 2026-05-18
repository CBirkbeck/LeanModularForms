/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

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

private noncomputable instance : ContinuousSMul ℝ ℂ where
  continuous_smul := by
    convert (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd using 1

/-- Continuity of a parametric interval integral. -/
theorem intervalIntegral_continuous_on_param (f : ℝ → ℝ → ℂ) (a b : ℝ) (S : Set ℝ)
    (hab : a ≤ b) (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (_hf_int : ∀ s ∈ S, IntervalIntegrable (f · s) volume a b) :
    ContinuousOn (fun s => ∫ t in a..b, f t s) S := by
  intro s₀ _hs₀
  apply ContinuousAt.continuousWithinAt
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact
    (Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1))).exists_bound_of_continuousOn hf_cont.continuousOn
  apply intervalIntegral.continuousAt_of_dominated_interval
  · filter_upwards with s
    exact (hf_cont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (show s₀ - 1 < s₀ by linarith) (show s₀ < s₀ + 1 by linarith)]
      with s hs
    filter_upwards with t ht
    rw [Set.uIoc_of_le hab] at ht
    exact hM (t, s) ⟨Ioc_subset_Icc_self ht, hs.1.le, hs.2.le⟩
  · exact intervalIntegrable_const
  · filter_upwards with t _
    exact (hf_cont.comp (continuous_const.prodMk continuous_id)).continuousAt

/-- The s-partial of a C² function is C¹. -/
lemma contDiff_partialDeriv_snd_of_contDiff_two (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun s => H (p.1, s)) p.2) := by
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ H p) (0, 1)) :=
    (hH.fderiv_right le_rfl).clm_apply contDiff_const
  convert h2 using 1
  ext p
  change deriv (fun s => H (p.1, s)) p.2 = fderiv ℝ H p (0, 1)
  calc deriv (fun s => H (p.1, s)) p.2
      = (fderiv ℝ H (p.1, p.2)) (deriv (fun s => (p.1, s)) p.2) :=
        fderiv_comp_deriv p.2 (hH.differentiable two_ne_zero (p.1, p.2))
          ((differentiableAt_const p.1).prodMk differentiableAt_id)
    _ = (fderiv ℝ H p) (0, 1) := by
        congr 1
        exact ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).deriv

/-- The t-partial of a C² function is C¹. -/
lemma contDiff_partialDeriv_fst_of_contDiff_two (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => H (t, p.2)) p.1) := by
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ H p) (1, 0)) :=
    (hH.fderiv_right le_rfl).clm_apply contDiff_const
  convert h2 using 1
  ext p
  change deriv (fun t => H (t, p.2)) p.1 = fderiv ℝ H p (1, 0)
  calc deriv (fun t => H (t, p.2)) p.1
      = (fderiv ℝ H (p.1, p.2)) (deriv (fun t => (t, p.2)) p.1) :=
        fderiv_comp_deriv p.1 (hH.differentiable two_ne_zero (p.1, p.2))
          (differentiableAt_id.prodMk (differentiableAt_const p.2))
    _ = (fderiv ℝ H p) (1, 0) := by
        congr 1
        exact ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)).deriv

/-- Schwarz theorem: mixed partials of a C² function commute. -/
lemma schwarz_partialDeriv_comm (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    deriv (fun s' => deriv (fun t' => H (t', s')) t) s =
      deriv (fun t' => deriv (fun s' => H (t', s')) s) t := by
  have h_symm : IsSymmSndFDerivAt ℝ H (t, s) := hH.contDiffAt.isSymmSndFDerivAt
    (by simp only [minSmoothness_of_isRCLikeNormedField, le_refl])
  have hH_diff : Differentiable ℝ H := hH.differentiable two_ne_zero
  have hfH : Differentiable ℝ (fun p => fderiv ℝ H p) :=
    (hH.fderiv_right le_rfl).differentiable one_ne_zero
  have h_inner_t : ∀ s', deriv (fun t' => H (t', s')) t = fderiv ℝ H (t, s') (1, 0) := fun s' => by
    have h_has_deriv : HasDerivAt (fun t' => (t', s')) (1, 0) t :=
      (hasDerivAt_id t).prodMk (hasDerivAt_const t s')
    calc deriv (fun t' => H (t', s')) t
        = (fderiv ℝ H (t, s')) (deriv (fun t' => (t', s')) t) := fderiv_comp_deriv t
          (hH_diff (t, s')) (differentiableAt_id.prodMk (differentiableAt_const s'))
      _ = (fderiv ℝ H (t, s')) (1, 0) := by rw [h_has_deriv.deriv]
  have h_inner_s : ∀ t', deriv (fun s' => H (t', s')) s = fderiv ℝ H (t', s) (0, 1) := fun t' => by
    have h_has_deriv : HasDerivAt (fun s' => (t', s')) (0, 1) s :=
      (hasDerivAt_const s t').prodMk (hasDerivAt_id s)
    calc deriv (fun s' => H (t', s')) s
        = (fderiv ℝ H (t', s)) (deriv (fun s' => (t', s')) s) := fderiv_comp_deriv s
          (hH_diff (t', s)) ((differentiableAt_const t').prodMk differentiableAt_id)
      _ = (fderiv ℝ H (t', s)) (0, 1) := by rw [h_has_deriv.deriv]
  simp_rw [h_inner_t, h_inner_s]
  have h_emb_s : DifferentiableAt ℝ (fun s' : ℝ => (t, s')) s :=
    (differentiableAt_const t).prodMk differentiableAt_id
  have h_deriv_emb_s : deriv (fun s' => (t, s')) s = (0, 1) :=
    ((hasDerivAt_const s t).prodMk (hasDerivAt_id s)).deriv
  have h_emb_t : DifferentiableAt ℝ (fun t' : ℝ => (t', s)) t :=
    differentiableAt_id.prodMk (differentiableAt_const s)
  have h_deriv_emb_t : deriv (fun t' => (t', s)) t = (1, 0) :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t s)).deriv
  have hLHS : deriv (fun s' => (fderiv ℝ H (t, s')) (1, 0)) s =
      (fderiv ℝ (fun p => fderiv ℝ H p) (t, s)) (0, 1) (1, 0) := by
    have h_clm_diff : DifferentiableAt ℝ (fun s' => fderiv ℝ H (t, s')) s :=
      (hfH (t, s)).comp s h_emb_s
    rw [deriv_clm_apply h_clm_diff (differentiableAt_const (1, 0))]
    simp only [deriv_const, map_zero, add_zero]
    rw [show (fun s' => fderiv ℝ H (t, s')) =
      (fun p => fderiv ℝ H p) ∘ (fun s' => (t, s')) from rfl,
      fderiv_comp_deriv s (hfH (t, s)) h_emb_s, h_deriv_emb_s]
  have hRHS : deriv (fun t' => (fderiv ℝ H (t', s)) (0, 1)) t =
      (fderiv ℝ (fun p => fderiv ℝ H p) (t, s)) (1, 0) (0, 1) := by
    have h_clm_diff : DifferentiableAt ℝ (fun t' => fderiv ℝ H (t', s)) t :=
      (hfH (t, s)).comp t h_emb_t
    rw [deriv_clm_apply h_clm_diff (differentiableAt_const (0, 1))]
    simp only [deriv_const, map_zero, add_zero]
    rw [show (fun t' => fderiv ℝ H (t', s)) =
      (fun p => fderiv ℝ H p) ∘ (fun t' => (t', s)) from rfl,
      fderiv_comp_deriv t (hfH (t, s)) h_emb_t, h_deriv_emb_t]
  rw [hLHS, hRHS]
  exact h_symm.eq (0, 1) (1, 0)

private lemma homotopy_H_differentiableAt_s (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun s' => H (t, s')) s :=
  (hH.differentiable two_ne_zero (t, s)).comp s
    ((differentiableAt_const t).prodMk differentiableAt_id)

private lemma homotopy_H_differentiableAt_t (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun t' => H (t', s)) t :=
  (hH.differentiable two_ne_zero (t, s)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const s))

private lemma homotopy_fH_differentiableAt_s (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ (fun s' => f (H (t, s'))) s :=
  (hf.restrictScalars ℝ).comp s (homotopy_H_differentiableAt_s H hH t s)

private lemma homotopy_fH_differentiableAt_t (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ (fun t' => f (H (t', s))) t :=
  (hf.restrictScalars ℝ).comp t (homotopy_H_differentiableAt_t H hH t s)

private lemma homotopy_partialT_differentiableAt_s (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) : DifferentiableAt ℝ (fun s' => deriv (fun t' => H (t', s')) t) s := by
  change DifferentiableAt ℝ
    ((fun p : ℝ × ℝ => deriv (fun t' => H (t', p.2)) p.1) ∘ (fun s' => (t, s'))) s
  exact ((contDiff_partialDeriv_fst_of_contDiff_two H hH).differentiable one_ne_zero (t, s)).comp s
    ((differentiableAt_const t).prodMk differentiableAt_id)

private lemma homotopy_partialS_differentiableAt_t (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) : DifferentiableAt ℝ (fun t' => deriv (fun s' => H (t', s')) s) t := by
  change DifferentiableAt ℝ
    ((fun p : ℝ × ℝ => deriv (fun s' => H (p.1, s')) p.2) ∘ (fun t' => (t', s))) t
  exact ((contDiff_partialDeriv_snd_of_contDiff_two H hH).differentiable one_ne_zero (t, s)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const s))

private lemma homotopy_chain_rule_s (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : Differentiable ℂ f) :
    deriv (fun s' => f (H (t, s'))) s =
      deriv f (H (t, s)) * deriv (fun s' => H (t, s')) s := by
  simpa [smul_eq_mul, mul_comm] using
    deriv.scomp s (hf (H (t, s))) (homotopy_H_differentiableAt_s H hH t s)

private lemma homotopy_chain_rule_t (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : Differentiable ℂ f) :
    deriv (fun t' => f (H (t', s))) t =
      deriv f (H (t, s)) * deriv (fun t' => H (t', s)) t := by
  simpa [smul_eq_mul, mul_comm] using
    deriv.scomp t (hf (H (t, s))) (homotopy_H_differentiableAt_t H hH t s)

private lemma homotopy_schwarz_product_rule (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf_at : DifferentiableAt ℂ f (H (t, s))) (hf : Differentiable ℂ f) :
    deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
      deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t := by
  have hLHS : deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
      deriv (fun s' => f (H (t, s'))) s * deriv (fun t' => H (t', s)) t +
        f (H (t, s)) * deriv (fun s' => deriv (fun t' => H (t', s')) t) s :=
    deriv_mul (homotopy_fH_differentiableAt_s f H hH t s hf_at)
      (homotopy_partialT_differentiableAt_s H hH t s)
  have hRHS : deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t =
      deriv (fun t' => f (H (t', s))) t * deriv (fun s' => H (t, s')) s +
        f (H (t, s)) * deriv (fun t' => deriv (fun s' => H (t', s')) s) t :=
    deriv_mul (homotopy_fH_differentiableAt_t f H hH t s hf_at)
      (homotopy_partialS_differentiableAt_t H hH t s)
  rw [hLHS, hRHS, homotopy_chain_rule_s f H hH t s hf, homotopy_chain_rule_t f H hH t s hf,
    schwarz_partialDeriv_comm H hH t s]
  ring

private lemma homotopy_mixed_partial_continuous (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2) := by
  have h_partialT := contDiff_partialDeriv_fst_of_contDiff_two H hH
  have h_eq : (fun p : ℝ × ℝ => deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2) =
      (fun p : ℝ × ℝ =>
        fderiv ℝ (fun p' : ℝ × ℝ => deriv (fun t' => H (t', p'.2)) p'.1) p (0, 1)) := by
    ext p
    have h_deriv_emb : deriv (fun s' => (p.1, s')) p.2 = (0, 1) :=
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).deriv
    calc deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2
        = deriv ((fun p' : ℝ × ℝ =>
            deriv (fun t' => H (t', p'.2)) p'.1) ∘ (fun s' => (p.1, s'))) p.2 := rfl
      _ = (fderiv ℝ (fun p' => deriv (fun t' => H (t', p'.2)) p'.1) p)
            (deriv (fun s' => (p.1, s')) p.2) :=
          fderiv_comp_deriv p.2 (h_partialT.differentiable one_ne_zero p)
            ((differentiableAt_const p.1).prodMk differentiableAt_id)
      _ = (fderiv ℝ (fun p' => deriv (fun t' => H (t', p'.2)) p'.1) p) (0, 1) := by
          rw [h_deriv_emb]
  rw [h_eq]
  exact (h_partialT.continuous_fderiv one_ne_zero).clm_apply continuous_const

private lemma homotopy_F'_eq (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hf : Differentiable ℂ f) (t s' : ℝ) :
    deriv (fun s'' => f (H (t, s'')) * deriv (fun t' => H (t', s'')) t) s' =
      deriv f (H (t, s')) * deriv (fun s'' => H (t, s'')) s' *
        deriv (fun t' => H (t', s')) t +
      f (H (t, s')) * deriv (fun s'' => deriv (fun t' => H (t', s'')) t) s' := by
  change deriv ((fun s'' => f (H (t, s''))) *
    (fun s'' => deriv (fun t' => H (t', s'')) t)) s' = _
  erw [deriv_mul (homotopy_fH_differentiableAt_s f H hH t s' (hf _))
    (homotopy_partialT_differentiableAt_s H hH t s'), homotopy_chain_rule_s f H hH t s' hf,
    mul_assoc]
  rfl

private lemma homotopy_F'_continuous (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hfH_cont : Continuous (f ∘ H)) (hf : Differentiable ℂ f) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun s'' => f (H (p.1, s'')) * deriv (fun t' => H (t', s'')) p.1) p.2) := by
  rw [show (fun p : ℝ × ℝ =>
      deriv (fun s'' => f (H (p.1, s'')) * deriv (fun t' => H (t', s'')) p.1) p.2) =
      (fun p : ℝ × ℝ =>
        deriv f (H (p.1, p.2)) * deriv (fun s'' => H (p.1, s'')) p.2 *
          deriv (fun t' => H (t', p.2)) p.1 +
        f (H (p.1, p.2)) * deriv (fun s'' => deriv (fun t' => H (t', s'')) p.1) p.2) from
    funext fun ⟨t, s'⟩ => homotopy_F'_eq f H hH hf t s']
  exact ((((hf.contDiff (n := ⊤) |>.continuous_deriv le_top).comp hH.continuous).mul
    (contDiff_partialDeriv_snd_of_contDiff_two H hH).continuous).mul
    (contDiff_partialDeriv_fst_of_contDiff_two H hH).continuous).add
    (hfH_cont.mul (homotopy_mixed_partial_continuous H hH))

private lemma homotopy_uniform_bound (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b)
    (hH : ContDiff ℝ 2 H) (hfH_cont : Continuous (f ∘ H)) (hf : Differentiable ℂ f) :
    ∃ (ε : ℝ) (M : ℝ), 0 < ε ∧
      (∀ᵐ t ∂volume, t ∈ Ι a b → ∀ s' ∈ Metric.ball s ε,
        ‖deriv (fun s'' => f (H (t, s'')) * deriv (fun t' => H (t', s'')) t) s'‖ ≤ M) ∧
      IntervalIntegrable (fun _ => M) volume a b ∧ Metric.ball s ε ∈ 𝓝 s := by
  let ε : ℝ := 1 / 4
  have hε_pos : (0 : ℝ) < ε := by norm_num
  let K : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (s - ε) (s + ε)
  obtain ⟨M_pt, _, hM_pt_max⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact K).exists_isMaxOn
    ⟨(a, s), left_mem_Icc.mpr hab.le, by constructor <;> linarith⟩
    (continuous_norm.comp (homotopy_F'_continuous f H hH hfH_cont hf)).continuousOn
  let M : ℝ := ‖deriv (fun s'' => f (H (M_pt.1, s'')) *
    deriv (fun t' => H (t', s'')) M_pt.1) M_pt.2‖
  have h_ball_subset : Metric.ball s ε ⊆ Icc (s - ε) (s + ε) := fun x hx => by
    simp only [Metric.mem_ball, Real.dist_eq] at hx
    constructor <;> linarith [abs_lt.mp hx]
  refine ⟨ε, M, hε_pos, ?_, intervalIntegrable_const, Metric.ball_mem_nhds s hε_pos⟩
  filter_upwards with t ht s' hs'
  simpa using hM_pt_max (show (t, s') ∈ K from
    ⟨Set.uIoc_subset_uIcc.trans (Set.uIcc_of_le hab.le).subset ht, h_ball_subset hs'⟩)

private lemma homotopy_F_continuous_t (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hfH_cont : Continuous (f ∘ H)) (s' : ℝ) :
    Continuous (fun t => f (H (t, s')) * deriv (fun t' => H (t', s')) t) :=
  (hfH_cont.comp (continuous_id.prodMk continuous_const)).mul
    ((contDiff_partialDeriv_fst_of_contDiff_two H hH).continuous.comp
      (continuous_id.prodMk continuous_const))

private lemma hasDerivAt_homotopy_param (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b)
    (hH_smooth : ContDiff ℝ 2 H)
    (hf_diff : ∀ t ∈ Icc a b, ∀ s' ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f (H (t, s')))
    (hfH_cont : Continuous (f ∘ H)) (hs : s ∈ Set.Icc 0 1) (hf_differentiable : Differentiable ℂ f)
    (h_schwarz : ∀ t ∈ Ioo a b,
        deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
          deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t) :
    HasDerivAt (fun s' => ∫ t in a..b, f (H (t, s')) * deriv (fun t' => H (t', s')) t)
      (∫ t in a..b, deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t) s := by
  let F : ℝ → ℝ → ℂ := fun s' t => f (H (t, s')) * deriv (fun t' => H (t', s')) t
  have h_integral_eq : ∫ t in a..b, deriv (fun s' => F s' t) s =
      ∫ t in a..b, deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    rw [Set.uIoc_of_le hab.le] at ht
    by_cases htb : t = b
    · change deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s = _
      exact homotopy_schwarz_product_rule f H hH_smooth t s
        (htb ▸ hf_diff b (right_mem_Icc.mpr hab.le) s hs) hf_differentiable
    · exact h_schwarz t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  obtain ⟨ε, M, _, h_bound, h_bound_int, h_ball_mem⟩ :=
    homotopy_uniform_bound f H a b s hab hH_smooth hfH_cont hf_differentiable
  rw [← h_integral_eq]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le h_ball_mem
    (.of_forall fun s' =>
      (homotopy_F_continuous_t f H hH_smooth hfH_cont s').aestronglyMeasurable)
    ((homotopy_F_continuous_t f H hH_smooth hfH_cont s).intervalIntegrable (a := a) (b := b))
    (((homotopy_F'_continuous f H hH_smooth hfH_cont hf_differentiable).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable) h_bound h_bound_int ?_).2
  filter_upwards with t _ s' _
  exact ((homotopy_fH_differentiableAt_s f H hH_smooth t s' (hf_differentiable (H (t, s')))).mul
    (homotopy_partialT_differentiableAt_s H hH_smooth t s')).hasDerivAt

private lemma homotopy_J_deriv_continuousOn (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ)
    (hH : ContDiff ℝ 2 H) (hfH_cont : Continuous (f ∘ H))
    (hf_diff : ∀ t ∈ Icc a b, ∀ s' ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f (H (t, s')))
    (hs : s ∈ Set.Icc 0 1) (hf : Differentiable ℂ f) :
    ContinuousOn (fun t => deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t)
      (Icc a b) := by
  have h_partialS := contDiff_partialDeriv_snd_of_contDiff_two H hH
  have h_embed : Continuous (fun t : ℝ => (t, s)) := continuous_id.prodMk continuous_const
  have h_deriv_eq : ∀ t ∈ Icc a b,
      deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t =
        deriv (fun t' => f (H (t', s))) t * deriv (fun s'' => H (t, s'')) s +
          f (H (t, s)) * deriv (fun t' => deriv (fun s'' => H (t', s'')) s) t := fun t ht =>
    deriv_mul (homotopy_fH_differentiableAt_t f H hH t s (hf_diff t ht s hs))
      (homotopy_partialS_differentiableAt_t H hH t s)
  refine ContinuousOn.congr ?_ h_deriv_eq
  refine .add ?_ ((hfH_cont.comp h_embed).mul
    ((h_partialS.comp (contDiff_id.prodMk contDiff_const) :
      ContDiff ℝ 1 _).continuous_deriv le_rfl)).continuousOn
  refine ContinuousOn.mul ?_ (h_partialS.continuous.comp h_embed).continuousOn
  refine ContinuousOn.congr ?_ fun t _ => homotopy_chain_rule_t f H hH t s hf
  exact ((((hf.contDiff (n := ⊤) |>.continuous_deriv le_top).comp hH.continuous).comp h_embed).mul
    ((contDiff_partialDeriv_fst_of_contDiff_two H hH).continuous.comp h_embed)).continuousOn

/-- Derivative of the homotopy integral vanishes. -/
theorem hasDerivAt_homotopy_integral_zero (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b)
    (hH_smooth : ContDiff ℝ 2 H)
    (hf_diff : ∀ t ∈ Icc a b, ∀ s' ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f (H (t, s')))
    (hfH_cont : Continuous (f ∘ H)) (hs : s ∈ Set.Icc 0 1)
    (hderiv_a : deriv (fun s' => H (a, s')) s = 0)
    (hderiv_b : deriv (fun s' => H (b, s')) s = 0) (hf_differentiable : Differentiable ℂ f) :
    HasDerivAt (fun s' => ∫ t in a..b, f (H (t, s')) * deriv (fun t' => H (t', s')) t) 0 s := by
  let J : ℝ → ℝ → ℂ := fun t s' => f (H (t, s')) * deriv (fun s'' => H (t, s'')) s'
  have h_ftc : ∫ t in a..b, deriv (fun t' => J t' s) t = J b s - J a s := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt _
      (ContinuousOn.intervalIntegrable_of_Icc hab.le
        (homotopy_J_deriv_continuousOn f H a b s hH_smooth hfH_cont hf_diff hs hf_differentiable))
    intro t ht
    have ht' : t ∈ Icc a b :=
      Set.uIcc_subset_Icc ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ ht
    exact ((homotopy_fH_differentiableAt_t f H hH_smooth t s (hf_diff t ht' s hs)).mul
      (homotopy_partialS_differentiableAt_t H hH_smooth t s)).hasDerivAt
  have h_boundary : J b s - J a s = 0 := by simp only [J, hderiv_a, hderiv_b, mul_zero, sub_zero]
  rw [← h_boundary, ← h_ftc]
  exact hasDerivAt_homotopy_param f H a b s hab hH_smooth hf_diff hfH_cont hs hf_differentiable
    fun t ht => homotopy_schwarz_product_rule f H hH_smooth t s
      (hf_diff t (Ioo_subset_Icc_self ht) s hs) hf_differentiable

end
