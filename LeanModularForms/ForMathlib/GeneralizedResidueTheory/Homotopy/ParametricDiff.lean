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

private noncomputable instance : ContinuousSMul ℝ ℂ :=
  ⟨(show (fun p : ℝ × ℂ => p.1 • p.2) = (fun p => (p.1 : ℂ) * p.2) from
    funext fun p => by simp [Complex.real_smul]) ▸
    (Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd⟩

/-- Continuity of a parametric interval integral. -/
theorem intervalIntegral_continuous_on_param (f : ℝ → ℝ → ℂ) (a b : ℝ) (S : Set ℝ)
    (hab : a ≤ b) (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (_hf_int : ∀ s ∈ S, IntervalIntegrable (f · s) volume a b) :
    ContinuousOn (fun s => ∫ t in a..b, f t s) S := by
  intro s₀ _hs₀
  apply ContinuousAt.continuousWithinAt
  have hmeas : ∀ s, AEStronglyMeasurable (f · s) (volume.restrict (Set.uIoc a b)) := fun s =>
    (hf_cont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  have hcont_pt : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → ContinuousAt (f t) s₀ := by
    filter_upwards with t _
    exact (hf_cont.comp (continuous_const.prodMk continuous_id)).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact
    (Icc a b ×ˢ Icc (s₀ - 1) (s₀ + 1))).exists_bound_of_continuousOn hf_cont.continuousOn
  apply intervalIntegral.continuousAt_of_dominated_interval
  · filter_upwards with s using hmeas s
  · filter_upwards [show Ioo (s₀ - 1) (s₀ + 1) ∈ 𝓝 s₀ from
      Ioo_mem_nhds (by linarith) (by linarith)] with s hs
    filter_upwards with t ht
    by_cases htab : t ∈ Icc a b
    · exact hM (t, s) ⟨htab, hs.1.le, hs.2.le⟩
    · rw [Set.uIoc_of_le hab] at ht
      exact absurd (Ioc_subset_Icc_self ht) htab
  · exact intervalIntegrable_const
  · exact hcont_pt

lemma contDiff_partialDeriv_snd_of_contDiff_two (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun s => H (p.1, s)) p.2) := by
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ H p) := hH.fderiv_right le_rfl
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ H p) (0, 1)) := h1.clm_apply contDiff_const
  convert h2 using 1
  ext p
  have hH_diff : Differentiable ℝ H := hH.differentiable two_ne_zero
  have h_emb_diff : DifferentiableAt ℝ (fun s : ℝ => (p.1, s)) p.2 :=
    (differentiableAt_const p.1).prodMk differentiableAt_id
  change deriv (fun s => H (p.1, s)) p.2 = fderiv ℝ H p (0, 1)
  calc deriv (fun s => H (p.1, s)) p.2
      = (fderiv ℝ H (p.1, p.2)) (deriv (fun s => (p.1, s)) p.2) :=
        fderiv_comp_deriv p.2 (hH_diff (p.1, p.2)) h_emb_diff
    _ = (fderiv ℝ H p) (0, 1) := by
        congr 1
        exact ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).deriv

lemma contDiff_partialDeriv_fst_of_contDiff_two (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => deriv (fun t => H (t, p.2)) p.1) := by
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => fderiv ℝ H p) := hH.fderiv_right le_rfl
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (fderiv ℝ H p) (1, 0)) := h1.clm_apply contDiff_const
  convert h2 using 1
  ext p
  have hH_diff : Differentiable ℝ H := hH.differentiable two_ne_zero
  have h_emb_diff : DifferentiableAt ℝ (fun t : ℝ => (t, p.2)) p.1 :=
    differentiableAt_id.prodMk (differentiableAt_const p.2)
  change deriv (fun t => H (t, p.2)) p.1 = fderiv ℝ H p (1, 0)
  calc deriv (fun t => H (t, p.2)) p.1
      = (fderiv ℝ H (p.1, p.2)) (deriv (fun t => (t, p.2)) p.1) :=
        fderiv_comp_deriv p.1 (hH_diff (p.1, p.2)) h_emb_diff
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
    have h_const_diff : DifferentiableAt ℝ (fun _ : ℝ => (1, 0) : ℝ → ℝ × ℝ) s :=
      differentiableAt_const (1, 0)
    rw [deriv_clm_apply h_clm_diff h_const_diff]
    simp only [deriv_const, map_zero, add_zero]
    have h_comp : (fun s' => fderiv ℝ H (t, s')) =
        (fun p => fderiv ℝ H p) ∘ (fun s' => (t, s')) := rfl
    rw [h_comp, fderiv_comp_deriv s (hfH (t, s)) h_emb_s, h_deriv_emb_s]
  have hRHS : deriv (fun t' => (fderiv ℝ H (t', s)) (0, 1)) t =
      (fderiv ℝ (fun p => fderiv ℝ H p) (t, s)) (1, 0) (0, 1) := by
    have h_clm_diff : DifferentiableAt ℝ (fun t' => fderiv ℝ H (t', s)) t :=
      (hfH (t, s)).comp t h_emb_t
    have h_const_diff : DifferentiableAt ℝ (fun _ : ℝ => (0, 1) : ℝ → ℝ × ℝ) t :=
      differentiableAt_const (0, 1)
    rw [deriv_clm_apply h_clm_diff h_const_diff]
    simp only [deriv_const, map_zero, add_zero]
    have h_comp : (fun t' => fderiv ℝ H (t', s)) =
        (fun p => fderiv ℝ H p) ∘ (fun t' => (t', s)) := rfl
    rw [h_comp, fderiv_comp_deriv t (hfH (t, s)) h_emb_t, h_deriv_emb_t]
  rw [hLHS, hRHS]
  exact h_symm.eq (0, 1) (1, 0)

/-- `s' ↦ H(t, s')` is differentiable when H is C². -/
private lemma homotopy_H_differentiableAt_s (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun s' => H (t, s')) s :=
  (hH.differentiable two_ne_zero (t, s)).comp s
    ((differentiableAt_const t).prodMk differentiableAt_id)

/-- `t' ↦ H(t', s)` is differentiable when H is C². -/
private lemma homotopy_H_differentiableAt_t (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) (t s : ℝ) :
    DifferentiableAt ℝ (fun t' => H (t', s)) t :=
  (hH.differentiable two_ne_zero (t, s)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const s))

/-- `s' ↦ f(H(t, s'))` is differentiable. -/
private lemma homotopy_fH_differentiableAt_s (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ (fun s' => f (H (t, s'))) s :=
  (hf.restrictScalars ℝ).comp s (homotopy_H_differentiableAt_s H hH t s)

/-- `t' ↦ f(H(t', s))` is differentiable. -/
private lemma homotopy_fH_differentiableAt_t (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : DifferentiableAt ℂ f (H (t, s))) :
    DifferentiableAt ℝ (fun t' => f (H (t', s))) t :=
  (hf.restrictScalars ℝ).comp t (homotopy_H_differentiableAt_t H hH t s)

/-- `s' ↦ ∂H/∂t(t, s')` is differentiable. -/
private lemma homotopy_partialT_differentiableAt_s (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) : DifferentiableAt ℝ (fun s' => deriv (fun t' => H (t', s')) t) s := by
  change DifferentiableAt ℝ
    ((fun p : ℝ × ℝ => deriv (fun t' => H (t', p.2)) p.1) ∘ (fun s' => (t, s'))) s
  exact ((contDiff_partialDeriv_fst_of_contDiff_two H hH).differentiable one_ne_zero (t, s)).comp s
    ((differentiableAt_const t).prodMk differentiableAt_id)

/-- `t' ↦ ∂H/∂s(t', s)` is differentiable. -/
private lemma homotopy_partialS_differentiableAt_t (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) : DifferentiableAt ℝ (fun t' => deriv (fun s' => H (t', s')) s) t := by
  change DifferentiableAt ℝ
    ((fun p : ℝ × ℝ => deriv (fun s' => H (p.1, s')) p.2) ∘ (fun t' => (t', s))) t
  exact ((contDiff_partialDeriv_snd_of_contDiff_two H hH).differentiable one_ne_zero (t, s)).comp t
    (differentiableAt_id.prodMk (differentiableAt_const s))

/-- Chain rule for `s' ↦ f(H(t, s'))`. -/
private lemma homotopy_chain_rule_s (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : Differentiable ℂ f) :
    deriv (fun s' => f (H (t, s'))) s =
      deriv f (H (t, s)) * deriv (fun s' => H (t, s')) s := by
  simpa [smul_eq_mul, mul_comm] using
    deriv.scomp s (hf (H (t, s))) (homotopy_H_differentiableAt_s H hH t s)

/-- Chain rule for `t' ↦ f(H(t', s))`. -/
private lemma homotopy_chain_rule_t (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf : Differentiable ℂ f) :
    deriv (fun t' => f (H (t', s))) t =
      deriv f (H (t, s)) * deriv (fun t' => H (t', s)) t := by
  simpa [smul_eq_mul, mul_comm] using
    deriv.scomp t (hf (H (t, s))) (homotopy_H_differentiableAt_t H hH t s)

/-- The s-derivative of `f(H(t,s')) * ∂H/∂t(t,s')` equals the t-derivative of
`f(H(t',s)) * ∂H/∂s(t',s)`, via the product rule, chain rule, and Schwarz symmetry. -/
private lemma homotopy_schwarz_product_rule (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (t s : ℝ) (hf_at : DifferentiableAt ℂ f (H (t, s))) (hf : Differentiable ℂ f) :
    deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
      deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t := by
  have hLHS : deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
      deriv (fun s' => f (H (t, s'))) s * deriv (fun t' => H (t', s)) t +
        f (H (t, s)) * deriv (fun s' => deriv (fun t' => H (t', s')) t) s := by
    change deriv ((fun s' => f (H (t, s'))) *
      (fun s' => deriv (fun t' => H (t', s')) t)) s = _
    exact deriv_mul (homotopy_fH_differentiableAt_s f H hH t s hf_at)
      (homotopy_partialT_differentiableAt_s H hH t s)
  have hRHS : deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t =
      deriv (fun t' => f (H (t', s))) t * deriv (fun s' => H (t, s')) s +
        f (H (t, s)) * deriv (fun t' => deriv (fun s' => H (t', s')) s) t := by
    change deriv ((fun t' => f (H (t', s))) *
      (fun t' => deriv (fun s' => H (t', s')) s)) t = _
    exact deriv_mul (homotopy_fH_differentiableAt_t f H hH t s hf_at)
      (homotopy_partialS_differentiableAt_t H hH t s)
  rw [hLHS, hRHS, homotopy_chain_rule_s f H hH t s hf, homotopy_chain_rule_t f H hH t s hf,
    schwarz_partialDeriv_comm H hH t s]
  ring

/-- Continuity of the mixed partial `(t, s') ↦ ∂/∂s' (∂H/∂t(t, s'))`. -/
private lemma homotopy_mixed_partial_continuous (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H) :
    Continuous (fun p : ℝ × ℝ => deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2) := by
  have h_partialT := contDiff_partialDeriv_fst_of_contDiff_two H hH
  have h_eq : (fun p : ℝ × ℝ => deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2) =
      (fun p : ℝ × ℝ =>
        fderiv ℝ (fun p' : ℝ × ℝ => deriv (fun t' => H (t', p'.2)) p'.1) p (0, 1)) := by
    ext p
    have h_emb_diff : DifferentiableAt ℝ (fun s' : ℝ => (p.1, s')) p.2 :=
      (differentiableAt_const p.1).prodMk differentiableAt_id
    have h_deriv_emb : deriv (fun s' => (p.1, s')) p.2 = (0, 1) :=
      ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)).deriv
    calc deriv (fun s' => deriv (fun t' => H (t', s')) p.1) p.2
        = deriv ((fun p' : ℝ × ℝ =>
            deriv (fun t' => H (t', p'.2)) p'.1) ∘ (fun s' => (p.1, s'))) p.2 := rfl
      _ = (fderiv ℝ (fun p' => deriv (fun t' => H (t', p'.2)) p'.1) p)
            (deriv (fun s' => (p.1, s')) p.2) :=
          fderiv_comp_deriv p.2 (h_partialT.differentiable one_ne_zero p) h_emb_diff
      _ = (fderiv ℝ (fun p' => deriv (fun t' => H (t', p'.2)) p'.1) p) (0, 1) := by
          rw [h_deriv_emb]
  rw [h_eq]
  exact (h_partialT.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- The s-derivative of `f(H(t,s')) * ∂H/∂t(t,s')` has a closed-form expression. -/
private lemma homotopy_F'_eq (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hf : Differentiable ℂ f) (t s' : ℝ) :
    deriv (fun s'' => f (H (t, s'')) * deriv (fun t' => H (t', s'')) t) s' =
      deriv f (H (t, s')) * deriv (fun s'' => H (t, s'')) s' *
        deriv (fun t' => H (t', s')) t +
      f (H (t, s')) * deriv (fun s'' => deriv (fun t' => H (t', s'')) t) s' := by
  have hfH_diff_s' : DifferentiableAt ℝ (fun s'' => f (H (t, s''))) s' :=
    homotopy_fH_differentiableAt_s f H hH t s' (hf _)
  have h_chain := homotopy_chain_rule_s f H hH t s' hf
  change deriv ((fun s'' => f (H (t, s''))) *
    (fun s'' => deriv (fun t' => H (t', s'')) t)) s' = _
  have h_dm := deriv_mul hfH_diff_s' (homotopy_partialT_differentiableAt_s H hH t s')
  erw [h_dm, h_chain, mul_assoc]
  rfl

/-- Continuity of `(t, s') ↦ ∂/∂s' [f(H(t,s')) * ∂H/∂t(t,s')]`. -/
private lemma homotopy_F'_continuous (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (hH : ContDiff ℝ 2 H)
    (hfH_cont : Continuous (f ∘ H)) (hf : Differentiable ℂ f) :
    Continuous (fun p : ℝ × ℝ =>
      deriv (fun s'' => f (H (p.1, s'')) * deriv (fun t' => H (t', s'')) p.1) p.2) := by
  have hF'_fun_eq : (fun p : ℝ × ℝ =>
      deriv (fun s'' => f (H (p.1, s'')) * deriv (fun t' => H (t', s'')) p.1) p.2) =
      (fun p : ℝ × ℝ =>
        deriv f (H (p.1, p.2)) * deriv (fun s'' => H (p.1, s'')) p.2 *
          deriv (fun t' => H (t', p.2)) p.1 +
        f (H (p.1, p.2)) * deriv (fun s'' => deriv (fun t' => H (t', s'')) p.1) p.2) := by
    ext ⟨t, s'⟩
    exact homotopy_F'_eq f H hH hf t s'
  rw [hF'_fun_eq]
  exact ((((hf.contDiff (n := ⊤) |>.continuous_deriv le_top).comp hH.continuous).mul
    (contDiff_partialDeriv_snd_of_contDiff_two H hH).continuous).mul
    (contDiff_partialDeriv_fst_of_contDiff_two H hH).continuous).add
    (hfH_cont.mul (homotopy_mixed_partial_continuous H hH))

/-- Uniform bound on the s-derivative of the integrand over a compact set. -/
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
  have h_ball_subset : Metric.ball s ε ⊆ Icc (s - ε) (s + ε) := by
    intro x hx
    simp only [Metric.mem_ball, Real.dist_eq] at hx
    constructor <;> linarith [abs_lt.mp hx]
  have h_uIoc_subset : (Ι a b : Set ℝ) ⊆ Icc a b :=
    Set.uIoc_subset_uIcc.trans (Set.uIcc_of_le hab.le).subset
  refine ⟨ε, M, hε_pos, ?_, intervalIntegrable_const, Metric.ball_mem_nhds s hε_pos⟩
  filter_upwards with t ht s' hs'
  simpa using hM_pt_max (show (t, s') ∈ K from ⟨h_uIoc_subset ht, h_ball_subset hs'⟩)

/-- Continuity of `t ↦ f(H(t,s')) * ∂H/∂t(t,s')` for fixed s'. -/
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
        (hf_diff t (by rw [htb]; exact ⟨hab.le, le_refl b⟩) s hs) hf_differentiable
    · exact h_schwarz t ⟨ht.1, lt_of_le_of_ne ht.2 htb⟩
  have hF_meas : ∀ᶠ s' in 𝓝 s, AEStronglyMeasurable (F s') (volume.restrict (Ι a b)) :=
    .of_forall fun s' => (homotopy_F_continuous_t f H hH_smooth hfH_cont s').aestronglyMeasurable
  have hF_int : IntervalIntegrable (F s) volume a b :=
    (homotopy_F_continuous_t f H hH_smooth hfH_cont s).intervalIntegrable (a := a) (b := b)
  have hF'_meas : AEStronglyMeasurable (fun t => deriv (fun s' => F s' t) s)
      (volume.restrict (Ι a b)) :=
    ((homotopy_F'_continuous f H hH_smooth hfH_cont hf_differentiable).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  obtain ⟨ε, M, _, h_bound, h_bound_int, h_ball_mem⟩ :=
    homotopy_uniform_bound f H a b s hab hH_smooth hfH_cont hf_differentiable
  have h_diff : ∀ᵐ t ∂volume, t ∈ Ι a b → ∀ s' ∈ Metric.ball s ε,
      HasDerivAt (fun s'' => F s'' t) (deriv (fun s'' => F s'' t) s') s' := by
    filter_upwards with t _ht s' _hs'
    exact ((homotopy_fH_differentiableAt_s f H hH_smooth t s'
      (hf_differentiable (H (t, s')))).mul
      (homotopy_partialT_differentiableAt_s H hH_smooth t s')).hasDerivAt
  rw [← h_integral_eq]
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    h_ball_mem hF_meas hF_int hF'_meas h_bound h_bound_int h_diff).2

/-- Continuity of `t ↦ deriv_{t'} [f(H(t', s)) * ∂H/∂s(t', s)]` on `[a, b]`. -/
private lemma homotopy_J_deriv_continuousOn (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ)
    (hH : ContDiff ℝ 2 H) (hfH_cont : Continuous (f ∘ H))
    (hf_diff : ∀ t ∈ Icc a b, ∀ s' ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f (H (t, s')))
    (hs : s ∈ Set.Icc 0 1) (hf : Differentiable ℂ f) :
    ContinuousOn (fun t => deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t)
      (Icc a b) := by
  have h_partialS := contDiff_partialDeriv_snd_of_contDiff_two H hH
  have h_partialT := contDiff_partialDeriv_fst_of_contDiff_two H hH
  have h_embed : Continuous (fun t : ℝ => (t, s)) := continuous_id.prodMk continuous_const
  have h_partial_cont : Continuous (fun t => deriv (fun s'' => H (t, s'')) s) :=
    h_partialS.continuous.comp h_embed
  have h_partial_deriv_cont :
      Continuous (fun t => deriv (fun t' => deriv (fun s'' => H (t', s'')) s) t) :=
    (h_partialS.comp (contDiff_id.prodMk contDiff_const) : ContDiff ℝ 1 _).continuous_deriv le_rfl
  have h_fH_cont : Continuous (fun t => f (H (t, s))) := hfH_cont.comp h_embed
  have h_deriv_eq : ∀ t ∈ Icc a b,
      deriv (fun t' => f (H (t', s)) * deriv (fun s'' => H (t', s'')) s) t =
        deriv (fun t' => f (H (t', s))) t * deriv (fun s'' => H (t, s'')) s +
          f (H (t, s)) * deriv (fun t' => deriv (fun s'' => H (t', s'')) s) t := fun t ht =>
    deriv_mul (homotopy_fH_differentiableAt_t f H hH t s (hf_diff t ht s hs))
      (homotopy_partialS_differentiableAt_t H hH t s)
  suffices h_rhs_cont : ContinuousOn (fun t =>
      deriv (fun t' => f (H (t', s))) t * deriv (fun s'' => H (t, s'')) s +
      f (H (t, s)) * deriv (fun t' => deriv (fun s'' => H (t', s'')) s) t) (Icc a b) by
    exact h_rhs_cont.congr h_deriv_eq
  apply ContinuousOn.add
  · apply ContinuousOn.mul _ h_partial_cont.continuousOn
    suffices ContinuousOn (fun t =>
        deriv f (H (t, s)) * deriv (fun t' => H (t', s)) t) (Icc a b) by
      exact this.congr fun t _ => homotopy_chain_rule_t f H hH t s hf
    exact ((((hf.contDiff (n := ⊤) |>.continuous_deriv le_top).comp
      hH.continuous).comp h_embed).mul (h_partialT.continuous.comp h_embed)).continuousOn
  · exact (h_fH_cont.mul h_partial_deriv_cont).continuousOn

/-- Derivative of the homotopy integral vanishes. -/
theorem hasDerivAt_homotopy_integral_zero (f : ℂ → ℂ) (H : ℝ × ℝ → ℂ) (a b s : ℝ) (hab : a < b)
    (hH_smooth : ContDiff ℝ 2 H)
    (hf_diff : ∀ t ∈ Icc a b, ∀ s' ∈ Icc (0:ℝ) 1, DifferentiableAt ℂ f (H (t, s')))
    (hfH_cont : Continuous (f ∘ H)) (hs : s ∈ Set.Icc 0 1)
    (hderiv_a : deriv (fun s' => H (a, s')) s = 0)
    (hderiv_b : deriv (fun s' => H (b, s')) s = 0) (hf_differentiable : Differentiable ℂ f) :
    HasDerivAt (fun s' => ∫ t in a..b, f (H (t, s')) * deriv (fun t' => H (t', s')) t) 0 s := by
  let J : ℝ → ℝ → ℂ := fun t s' => f (H (t, s')) * deriv (fun s'' => H (t, s'')) s'
  have h_boundary : J b s - J a s = 0 := by
    simp only [J, hderiv_a, hderiv_b, mul_zero, sub_zero]
  have h_deriv : HasDerivAt (fun s' => ∫ t in a..b,
      f (H (t, s')) * deriv (fun t' => H (t', s')) t) (J b s - J a s) s := by
    have hJ_diff_t : ∀ t ∈ Icc a b, DifferentiableAt ℝ (fun t' => J t' s) t := by
      intro t ht
      simp only [J]
      exact (homotopy_fH_differentiableAt_t f H hH_smooth t s (hf_diff t ht s hs)).mul
        (homotopy_partialS_differentiableAt_t H hH_smooth t s)
    have h_ftc : ∫ t in a..b, deriv (fun t' => J t' s) t = J b s - J a s := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro t ht
        exact (hJ_diff_t t (Set.uIcc_subset_Icc
          ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ ht)).hasDerivAt
      · exact ContinuousOn.intervalIntegrable_of_Icc hab.le
          (homotopy_J_deriv_continuousOn f H a b s hH_smooth hfH_cont hf_diff hs hf_differentiable)
    have h_schwarz : ∀ t ∈ Ioo a b,
        deriv (fun s' => f (H (t, s')) * deriv (fun t' => H (t', s')) t) s =
          deriv (fun t' => J t' s) t := by
      intro t ht
      simp only [J]
      exact homotopy_schwarz_product_rule f H hH_smooth t s
        (hf_diff t (Ioo_subset_Icc_self ht) s hs) hf_differentiable
    rw [← h_ftc]
    exact hasDerivAt_homotopy_param f H a b s hab hH_smooth hf_diff hfH_cont hs
      hf_differentiable h_schwarz
  rwa [h_boundary] at h_deriv

end
