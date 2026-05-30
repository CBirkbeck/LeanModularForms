module

public import LeanModularForms.Modularforms.E2
public import LeanModularForms.Modularforms.csqrt
public import LeanModularForms.Modularforms.upperhalfplane
public import Mathlib.NumberTheory.ModularForms.DedekindEta

@[expose] public section

/-!
# The Dedekind `η` function and its `S`-transformation

Compatibility alias `η` for Mathlib's `ModularForm.eta`, together with the proof that
`η(-1/z) = (Complex.I)^(1/2)⁻¹ · sqrt(z) · η(z)`, derived from the logarithmic-derivative
identity `(log η)'(-1/z) = (log (csqrt · η))'(z)`.

## Main results

* `eta_logDeriv_eql`: pointwise logarithmic-derivative identity.
* `eta_logderivs`, `eta_logderivs_const`, `eta_equality`: the `S`-transformation law.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

/-- The eta function. We use mathlib's upstream definition. -/
noncomputable abbrev η : ℂ → ℂ := ModularForm.eta

lemma eta_logDeriv_eql (z : ℍ) : logDeriv (η ∘ (fun z : ℂ ↦ -1 / z)) z =
    logDeriv (csqrt * η) z := by
  have h0 : logDeriv (η ∘ (fun z : ℂ ↦ -1 / z)) z =
      ((z : ℂ) ^ (2 : ℤ))⁻¹ *
        logDeriv η (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
    rw [logDeriv_comp, mul_comm]
    · congr
      conv => enter [1, 1]; intro z; rw [neg_div]; simp
      simp only [deriv.fun_neg', deriv_inv', neg_neg, inv_inj]
      norm_cast
    · simpa [η] using ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet
        (z := -1 / (z : ℂ)) (by simpa using pnat_div_upper 1 z)
    conv => enter [2]; ext z; rw [neg_div]; simp
    exact (differentiableAt_fun_id.inv (ne_zero z)).neg
  rw [h0, show (csqrt * η) = (fun x ↦ csqrt x * η x) from rfl, logDeriv_mul]
  · nth_rw 2 [logDeriv_apply]
    unfold csqrt
    rw [csqrt_deriv z]
    simp only [one_div, neg_mul, smul_eq_mul]
    nth_rw 2 [div_eq_mul_inv]
    · rw [← Complex.exp_neg,
        show 2⁻¹ * cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z)) =
            (cexp (-(2⁻¹ * Complex.log ↑z)) * cexp (-(2⁻¹ * Complex.log ↑z))) * 2⁻¹ by ring,
        ← Complex.exp_add, ← sub_eq_add_neg,
        show -(2⁻¹ * Complex.log ↑z) - 2⁻¹ * Complex.log ↑z = -Complex.log ↑z by ring,
        Complex.exp_neg, Complex.exp_log,
        show logDeriv η z = (π * Complex.I / 12) * E₂ z by
          simpa [η, E₂] using ModularForm.logDeriv_eta_eq_E2 z]
      · have Rb : logDeriv η (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) =
            (π * Complex.I / 12) * E₂ (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
          simpa [η, E₂] using ModularForm.logDeriv_eta_eq_E2
            (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ)
        rw [Rb]
        have E := E₂_transform z
        simp only [SL_slash_def, modular_S_smul, ModularGroup.denom_S, Int.reduceNeg,
          zpow_neg] at *
        have h00 : UpperHalfPlane.mk (-z : ℂ)⁻¹ z.im_inv_neg_coe_pos =
            (⟨-1 / z, by simpa using pnat_div_upper 1 z⟩ : ℍ) := by
          simp; ring_nf
        rw [h00] at E
        rw [← mul_assoc, mul_comm, ← mul_assoc, E, add_mul, add_comm]
        congr 1
        · have hpi : (π : ℂ) ≠ 0 := by
            simp only [ne_eq, ofReal_eq_zero]
            exact Real.pi_ne_zero
          have hzne := ne_zero z
          have hI : Complex.I ≠ 0 := I_ne_zero
          field_simp
          ring
        rw [mul_comm]
      simpa only [UpperHalfPlane.coe, ne_eq] using ne_zero z
  · simp only [csqrt, one_div, ne_eq, Complex.exp_ne_zero, not_false_eq_true]
  · simpa [η] using ModularForm.eta_ne_zero (z := (z : ℂ)) z.2
  · exact csqrt_differentiableAt z
  · simpa [η] using
      ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := (z : ℂ)) z.2

lemma eta_logderivs : {z : ℂ | 0 < z.im}.EqOn (logDeriv (η ∘ (fun z : ℂ ↦ -1 / z)))
    (logDeriv (csqrt * η)) :=
  fun z hz ↦ eta_logDeriv_eql ⟨z, hz⟩

lemma eta_logderivs_const : ∃ z : ℂ, z ≠ 0 ∧ {z : ℂ | 0 < z.im}.EqOn (η ∘ (fun z : ℂ ↦ -1 / z))
    (z • (csqrt * η)) := by
  have h := eta_logderivs
  rw [logDeriv_eqOn_iff] at h
  · exact h
  · apply DifferentiableOn.comp
    pick_goal 4
    · use {z : ℂ | 0 < z.im}
    · intro x hx
      apply DifferentiableAt.differentiableWithinAt
      simpa [η] using ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx
    · apply DifferentiableOn.div
      · fun_prop
      · fun_prop
      intro x hx
      have hx2 := ne_zero (⟨x, hx⟩ : ℍ)
      norm_cast at *
    · intro y hy
      simp
      have := UpperHalfPlane.im_inv_neg_coe_pos (⟨y, hy⟩ : ℍ)
      conv => enter [2, 1]; rw [neg_div, div_eq_mul_inv]; simp
      simp at *
      exact this
  · apply DifferentiableOn.mul
    · intro x hx
      exact (csqrt_differentiableAt ⟨x, hx⟩).differentiableWithinAt
    intro x hx
    have hηx : DifferentiableAt ℂ η x := by
      simpa [η] using ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := x) hx
    exact hηx.differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_im
  · exact (convex_halfSpace_im_gt 0).isPreconnected
  · intro x hx
    simp only [Pi.mul_apply, ne_eq, mul_eq_zero, not_or]
    refine ⟨?_, by simpa [η] using ModularForm.eta_ne_zero (z := x) hx⟩
    unfold csqrt
    simp only [one_div, Complex.exp_ne_zero, not_false_eq_true]
  · intro x hx
    simp only [comp_apply, ne_eq]
    simpa only [ne_eq] using ModularForm.eta_ne_zero (z := -1 / x)
      (by simpa using pnat_div_upper 1 ⟨x, hx⟩)

lemma eta_equality : {z : ℂ | 0 < z.im}.EqOn (η ∘ (fun z : ℂ ↦ -1 / z))
    ((csqrt Complex.I)⁻¹ • (csqrt * η)) := by
  obtain ⟨z, hz, h⟩ := eta_logderivs_const
  intro x hx
  have h2 := h hx
  have hI : Complex.I ∈ {z : ℂ | 0 < z.im} := by
    simp only [mem_setOf_eq, Complex.I_im, zero_lt_one]
  have h3 := h hI
  simp at h3
  conv at h3 => enter [2]; rw [← mul_assoc]
  have he : η Complex.I ≠ 0 := by
    simpa [η] using ModularForm.eta_ne_zero (z := Complex.I) (by simp)
  have hcd := (mul_eq_right₀ he).mp h3.symm
  rw [mul_eq_one_iff_inv_eq₀ hz, inv_eq_iff_eq_inv] at hcd
  rw [hcd] at h2
  exact h2
