module
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.NumberTheory.TsumDivisorsAntidiagonal

/-!
# Lemmas about `logDeriv`

This file collects auxiliary lemmas about the logarithmic derivative `logDeriv`, including
formulas for `logDeriv` of exponential expressions, a basic summability statement, and
the "equal logDeriv ⟺ proportional" characterization on a connected open set.

## Main statements

* `logDeriv_one_sub_exp_comp`: chain rule for `logDeriv ((1 - r * cexp ·) ∘ g)`.
* `logDeriv_q_expo_summable`: summability of `n * r^n / (1 - r^n)` for `‖r‖ < 1`.
* `logDeriv_eqOn_iff'`: on a convex open set where `f` and `g` are differentiable and
  nonvanishing, `logDeriv f = logDeriv g` iff `f` and `g` are proportional.
-/

open Set Function Complex

lemma logDeriv_one_sub_exp (r : ℂ) : logDeriv (fun z ↦ 1 - r * cexp z) =
    fun z ↦ -r * cexp z / (1 - r * cexp z) := by
  ext z
  simp [logDeriv]

/-- A chain rule computation for `logDeriv` of `(fun z ↦ 1 - r * cexp z) ∘ g`. -/
public lemma logDeriv_one_sub_exp_comp (r : ℂ) (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    logDeriv ((fun z ↦ 1 - r * cexp z) ∘ g) =
    fun z ↦ -r * deriv g z * cexp (g z) / (1 - r * cexp (g z)) := by
  ext y
  rw [logDeriv_comp _ (hg y), logDeriv_one_sub_exp]
  · ring
  · fun_prop

/-- If `‖r‖ < 1`, then the series `∑ n, n * r^n / (1 - r^n)` is summable. -/
public lemma logDeriv_q_expo_summable (r : ℂ) (hr : ‖r‖ < 1) : Summable fun n : ℕ ↦
    (n * r^n / (1 - r^n)) := by
  simpa [pow_one] using (summable_norm_pow_mul_geometric_div_one_sub (𝕜 := ℂ) 1 (r := r) hr)

lemma func_div (a b c d : ℂ → ℂ) (x : ℂ) (hb : b x ≠ 0) (hd : d x ≠ 0) :
    (a / b) x = (c / d) x ↔ (a * d) x = (b * c) x := by
  simp only [Pi.div_apply, Pi.mul_apply, div_eq_div_iff hb hd, mul_comm (b x)]

lemma deriv_EqOn_congr {f g : ℂ → ℂ} (s : Set ℂ) (hfg : s.EqOn f g) (hs : IsOpen s) :
    s.EqOn (deriv f) (deriv g) := fun x hx ↦ by
  rw [← derivWithin_of_isOpen hs hx, ← derivWithin_of_isOpen hs hx]
  exact derivWithin_congr hfg (hfg hx)

lemma logDeriv_eqOn_iff' (f g : ℂ → ℂ) (s : Set ℂ) (hf : DifferentiableOn ℂ f s)
    (hg : DifferentiableOn ℂ g s) (hs : s.Nonempty) (hs2 : IsOpen s) (hsc : Convex ℝ s)
    (hgn : ∀ x, x ∈ s → g x ≠ 0) (hfn : ∀ x, x ∈ s → f x ≠ 0) :
    EqOn (logDeriv f) (logDeriv g) s ↔ ∃ z : ℂ, z ≠ 0 ∧ EqOn (f) (z • g) s where
  mp h := by
    simp_rw [logDeriv] at h
    obtain ⟨t, ht⟩ := hs
    refine ⟨f t * (g t)⁻¹, mul_ne_zero (hfn t ht) (by simpa using hgn t ht), ?_⟩
    intro y hy
    have h2 := h hy
    rw [func_div] at h2
    · have hderiv : EqOn (deriv (f * g⁻¹)) (deriv f * g⁻¹ - f * deriv g / g ^ 2) s := by
        intro z hz
        rw [deriv_mul]
        · have hgi : g⁻¹ = (fun x ↦ x⁻¹) ∘ g := by
            ext y
            simp only [Pi.inv_apply, comp_apply]
          rw [hgi, deriv_comp, deriv_inv]
          · simp only [comp_apply, neg_mul, mul_neg, Pi.sub_apply, Pi.mul_apply, Pi.div_apply,
              Pi.pow_apply]
            ring
          · exact differentiableAt_inv (hgn z hz)
          · exact hg.differentiableAt (IsOpen.mem_nhds hs2 hz)
        · exact hf.differentiableAt (IsOpen.mem_nhds hs2 hz)
        · exact (hg.differentiableAt (IsOpen.mem_nhds hs2 hz)).inv (hgn z hz)
      · have H3 :=
          Convex.is_const_of_fderivWithin_eq_zero (f := f * g⁻¹) (𝕜 := ℂ) (s := s) ?_ ?_ ?_ hy ht
        · simp only [Pi.mul_apply, Pi.inv_apply] at H3
          rw [← H3]
          field_simp [hgn y hy]
          simp_all
        · exact hsc
        · exact hf.mul (hg.inv hgn)
        · have he : s.EqOn (deriv f * g⁻¹ - f * deriv g / g ^ 2) 0 := by
            intro z hz
            have Hmul : deriv f z * g z = f z * deriv g z :=
              (func_div (deriv f) f (deriv g) g z (hfn z hz) (hgn z hz)).1
                (by simpa [logDeriv, Pi.div_apply] using h hz)
            show deriv f z * (g z)⁻¹ - f z * deriv g z / g z ^ 2 = 0
            grind
          · intro v hv
            have H := h hv
            rw [func_div] at H
            · have ha := hderiv hv
              rw [he hv] at ha
              simp only [Pi.zero_apply] at ha
              rw [fderivWithin_of_isOpen hs2 hv]
              exact ContinuousLinearMap.ext_ring ha
            · exact hfn v hv
            · exact hgn v hv
    · exact hfn y hy
    · exact hgn y hy
  mpr := fun ⟨z, hz0, hz⟩ x hx ↦ by
    simp_rw [logDeriv_apply]
    rw [deriv_EqOn_congr s hz hs2 hx, hz hx,
      deriv_const_smul _ (hg.differentiableAt (IsOpen.mem_nhds hs2 hx))]
    simp [mul_div_mul_left (deriv g x) (g x) hz0]
