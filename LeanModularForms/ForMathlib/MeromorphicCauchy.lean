/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.DixonTheorem
import LeanModularForms.ForMathlib.SimplePoleIntegral
import LeanModularForms.ForMathlib.PrincipalPart

/-!
# Meromorphic Cauchy Theorem

This file extends the Cauchy theorem to meromorphic functions with finitely many simple
poles via pole subtraction. The main results show that for a meromorphic function `f`
with simple poles at a finite set `S` inside a convex open domain `U`:

  `contour integral of f = sum over s in S of 2*pi*I * winding(gamma, s) * c(s)`

## Main results

* `contourIntegral_principalPartSum_eq` -- the contour integral of the principal part
  sum equals the sum of `2*pi*I * winding * coefficient`.

* `contourIntegral_decomp_of_simple_poles` -- the contour integral of `f` decomposes
  as the integral of the holomorphic remainder plus the winding number sum.

* `sub_principalPartSum_corrected_differentiableOn` -- the corrected remainder
  (with removable singularities filled in) is differentiable on all of `U`.

* `contourIntegral_eq_sum_winding_coefficients_convex` -- the residue theorem for convex
  domains.

* `contourIntegral_eq_zero_of_zero_coefficients_convex` -- when all coefficients are
  zero, the contour integral vanishes.

## Proof strategy

The key decomposition: given `f` with simple poles at `S` with coefficients `c`:
  `f = (f - principalPartSum S c) + principalPartSum S c`

1. By `sub_principalPartSum_analyticAt`, `f - principalPartSum S c` is locally equal
   to an analytic function at each pole, so it has removable singularities.
2. Define a corrected function `g` that uses the analytic limit at poles and agrees
   with the remainder elsewhere. Show `g` is DifferentiableOn U.
3. Since gamma avoids S, the contour integrals of `g` and `f - principalPartSum` agree.
4. The integral of `g` vanishes by Cauchy for convex domains.
5. The integral of `principalPartSum` is the winding number sum.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, 1971
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-! ## Contour integral of principalPartSum -/

/-- The contour integral of the principal part sum along a closed path equals the
sum of `2*pi*I * winding(gamma, s) * c(s)` over `s in S`, when `gamma` avoids all
poles with positive distance. -/
theorem contourIntegral_principalPartSum_eq {S : Finset ℂ} {c : ℂ → ℂ}
    {γ : PiecewiseC1Path x x}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (c s / (γ.toPath.extend t - s)) * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral (principalPartSum S c) =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c s :=
  integral_sum_simple_poles_eq_winding hδ hI

/-! ## Contour integral decomposition -/

/-- **Pole subtraction decomposition for contour integrals.**

When `gamma` avoids all poles in `S` and both the remainder and the individual pole
terms are integrable, the contour integral of `f` decomposes as:

  `integral f = integral (f - principalPartSum) + sum 2*pi*I * winding * c` -/
theorem contourIntegral_decomp_of_simple_poles {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    {γ : PiecewiseC1Path x x}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (fun z => f z - principalPartSum S c z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (principalPartSum S c) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (c s / (γ.toPath.extend t - s)) * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral f =
      γ.contourIntegral (fun z => f z - principalPartSum S c z) +
        ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c s := by
  rw [← contourIntegral_principalPartSum_eq hδ hI,
      ← γ.contourIntegral_add _ _ h_rem_int h_pp_int]
  congr 1 with z
  ring

/-! ## Analyticity of the remainder at poles -/

/-- The remainder `f - principalPartSum S c` is locally equal to an analytic function
at each pole `s in S`. -/
theorem sub_principalPartSum_analyticAt_all {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    (h_pole : ∀ s ∈ S, HasSimplePoleAt f s)
    (h_coeff : ∀ (s : ℂ) (hs : s ∈ S), (h_pole s hs).coeff = c s) :
    ∀ s ∈ S, ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - principalPartSum S c z = g z :=
  fun s hs => sub_principalPartSum_analyticAt hs (h_pole s hs) (h_coeff s hs)

/-! ## Removable singularity: corrected remainder is DifferentiableOn -/

/-- At a pole, the limit-corrected function agrees with the analytic extension in a full
neighborhood. -/
private lemma correction_eventuallyEq_analyticExt {S : Finset ℂ} {z : ℂ}
    (rem : ℂ → ℂ) (g_z : ℂ → ℂ) (hzS : z ∈ (↑S : Set ℂ))
    (hg_z_an : AnalyticAt ℂ g_z z) (hg_z_eq : ∀ᶠ w in 𝓝[≠] z, rem w = g_z w) :
    (fun w => if w ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] w) rem else rem w) =ᶠ[𝓝 z] g_z := by
  set correction := fun w => if w ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] w) rem else rem w
  have h_lim_eq : limUnder (𝓝[≠] z) rem = g_z z :=
    (hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      |>.congr' (hg_z_eq.mono fun _ h => h.symm)).limUnder_eq
  have h_at_z : correction z = g_z z := by
    simp only [correction, hzS, ↓reduceIte, h_lim_eq]
  have hz_not_erase : z ∉ (↑(S.erase z) : Set ℂ) := by
    simp only [Finset.mem_coe, Finset.mem_erase, ne_eq, not_true_eq_false, false_and,
      not_false_eq_true]
  obtain ⟨V, hV_open, hz_V, hV_eq⟩ := mem_nhdsWithin.mp hg_z_eq
  have h_erase_away : (↑(S.erase z) : Set ℂ)ᶜ ∈ 𝓝 z :=
    (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds hz_not_erase
  apply Filter.mem_of_superset (Filter.inter_mem (hV_open.mem_nhds hz_V) h_erase_away)
  intro w ⟨hw_V, hw_erase⟩
  change correction w = g_z w
  by_cases hwz : w = z
  · rw [hwz, h_at_z]
  · have hw_not_S : w ∉ (↑S : Set ℂ) := by
      intro hmem
      exact hw_erase (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwz, Finset.mem_coe.mp hmem⟩))
    change (if w ∈ (↑S : Set ℂ) then _ else rem w) = g_z w
    rw [if_neg hw_not_S]
    exact hV_eq ⟨hw_V, hwz⟩

/-- Away from `S`, the limit-corrected function agrees with the remainder in a neighborhood. -/
private lemma correction_eventuallyEq_rem {S : Finset ℂ} {z : ℂ}
    (rem : ℂ → ℂ) (hzS : z ∉ (↑S : Set ℂ)) :
    (fun w => if w ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] w) rem else rem w) =ᶠ[𝓝 z] rem := by
  apply Filter.mem_of_superset (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
  intro w hw
  change (if w ∈ (↑S : Set ℂ) then _ else rem w) = rem w
  rw [if_neg hw]

/-- **The corrected remainder is DifferentiableOn U.**

Given `f` differentiable on `U \ S` with simple poles at `S` matching coefficients `c`,
there exists a function `g` that is DifferentiableOn U and agrees with
`f - principalPartSum S c` on `U \ S`. -/
theorem sub_principalPartSum_corrected_differentiableOn {f : ℂ → ℂ} {U : Set ℂ}
    {S : Finset ℂ} {c : ℂ → ℂ}
    (hU_open : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (_hS_sub : ↑S ⊆ U)
    (h_pole : ∀ s ∈ S, HasSimplePoleAt f s)
    (h_coeff : ∀ (s : ℂ) (hs : s ∈ S), (h_pole s hs).coeff = c s) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z ∈ U \ (↑S : Set ℂ), g z = f z - principalPartSum S c z := by
  have h_ext : ∀ s ∈ S, ∃ g_s : ℂ → ℂ, AnalyticAt ℂ g_s s ∧
      ∀ᶠ z in 𝓝[≠] s, (f z - principalPartSum S c z) = g_s z :=
    sub_principalPartSum_analyticAt_all h_pole h_coeff
  set rem : ℂ → ℂ := fun z => f z - principalPartSum S c z
  set correction : ℂ → ℂ := fun z =>
    if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) rem else rem z
  refine ⟨correction, ?_, ?_⟩
  · intro z hz
    by_cases hzS : z ∈ (↑S : Set ℂ)
    · obtain ⟨g_z, hg_z_an, hg_z_eq⟩ := h_ext z (Finset.mem_coe.mp hzS)
      exact (hg_z_an.differentiableAt.congr_of_eventuallyEq
        (correction_eventuallyEq_analyticExt rem g_z hzS hg_z_an hg_z_eq)).differentiableWithinAt
    · have h_rem_diff : DifferentiableAt ℂ rem z := by
        have h_U_minus_S := hU_open.sdiff S.finite_toSet.isClosed
        exact ((hf_diff z ⟨hz, hzS⟩).differentiableAt
          (h_U_minus_S.mem_nhds ⟨hz, hzS⟩)).sub
          (principalPartSum_differentiableAt (hz := hzS))
      exact (h_rem_diff.congr_of_eventuallyEq
        (correction_eventuallyEq_rem rem hzS)).differentiableWithinAt
  · intro z ⟨_, hzS⟩
    change (if z ∈ (↑S : Set ℂ) then _ else rem z) = rem z
    rw [if_neg hzS]

/-! ## Residue theorem for convex domains -/

/-- The contour integral of `g` equals that of `f - principalPartSum` when `g` agrees with
the remainder on the curve. -/
private lemma contourIntegral_corrected_eq_rem {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {g : ℂ → ℂ}
    (h_g_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S c (γ t)) :
    γ.contourIntegral g =
      γ.contourIntegral (fun z => f z - principalPartSum S c z) := by
  simp only [PiecewiseC1Path.contourIntegral, PiecewiseC1Path.extendedPath_eq]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (zero_le_one' ℝ)] at ht
  simp only [PiecewiseC1Path.extendedPath_eq] at h_g_on_curve
  change g (γ.toPath.extend t) * _ = (f (γ.toPath.extend t) - _) * _
  rw [h_g_on_curve t ht]

/-- The contour integrand of the corrected remainder is EqOn the integrand of the
original remainder on `uIoc 0 1`, and hence the corrected function is integrable. -/
private lemma corrected_remainder_integrable {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {g : ℂ → ℂ}
    (h_g_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S c (γ t))
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (fun z => f z - principalPartSum S c z) γ)
      volume 0 1) :
    IntervalIntegrable (PiecewiseC1Path.contourIntegrand g γ) volume 0 1 := by
  have h_eqOn : EqOn (PiecewiseC1Path.contourIntegrand g γ)
      (PiecewiseC1Path.contourIntegrand (fun z => f z - principalPartSum S c z) γ)
      (uIoc 0 1) := by
    intro t ht
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.contourIntegrand]
    rw [h_g_on_curve t (Ioc_subset_Icc_self ht)]
  exact h_rem_int.congr h_eqOn.symm

/-- **Residue theorem for convex domains.**

For a meromorphic function `f` with simple poles at `S ⊂ U` with coefficients `c`,
where `U` is convex and open, the contour integral of `f` along a closed path
in `U` avoiding `S` equals the sum of `2*pi*I * winding(gamma, s) * c(s)`. -/
theorem contourIntegral_eq_sum_winding_coefficients_convex
    {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    (γ : PiecewiseC1Path x x)
    (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (hS_sub : ↑S ⊆ U)
    (h_pole : ∀ s ∈ S, HasSimplePoleAt f s)
    (h_coeff : ∀ (s : ℂ) (hs : s ∈ S), (h_pole s hs).coeff = c s)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    -- Integrability hypotheses
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (fun z => f z - principalPartSum S c z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (principalPartSum S c) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (c s / (γ.toPath.extend t - s)) * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c s := by
  obtain ⟨g, hg_diff, hg_agree⟩ :=
    sub_principalPartSum_corrected_differentiableOn hU_open hf_diff hS_sub h_pole h_coeff
  have h_g_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S c (γ t) :=
    fun t ht => hg_agree (γ t) ⟨hγ t ht, fun hmem =>
      hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
  have hg_zero : γ.contourIntegral g = 0 :=
    γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU_convex hU_open hU_ne
      hg_diff hγ (corrected_remainder_integrable h_g_on_curve h_rem_int)
  rw [contourIntegral_decomp_of_simple_poles hδ h_rem_int h_pp_int hI,
    show γ.contourIntegral (fun z => f z - principalPartSum S c z) = 0 from
      (contourIntegral_corrected_eq_rem h_g_on_curve) ▸ hg_zero, zero_add]

/-! ## Special case: zero coefficients -/

/-- **Vanishing for zero coefficients.**

When all coefficients are zero, the contour integral of `f` vanishes along any closed
path in a convex domain `U` avoiding the poles. -/
theorem contourIntegral_eq_zero_of_zero_coefficients_convex
    {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    (γ : PiecewiseC1Path x x)
    (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (hS_sub : ↑S ⊆ U)
    (h_pole : ∀ s ∈ S, HasSimplePoleAt f s)
    (h_coeff : ∀ (s : ℂ) (hs : s ∈ S), (h_pole s hs).coeff = c s)
    (hc_zero : ∀ s ∈ S, c s = 0)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (fun z => f z - principalPartSum S c z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (principalPartSum S c) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (c s / (γ.toPath.extend t - s)) * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral f = 0 := by
  rw [contourIntegral_eq_sum_winding_coefficients_convex γ hU_convex hU_open hU_ne
    hf_diff hS_sub h_pole h_coeff hγ hγ_avoids hδ h_rem_int h_pp_int hI]
  apply Finset.sum_eq_zero
  intro s hs
  rw [hc_zero s hs, mul_zero]

/-! ## Residue computation -/

/-- The contour integral of `f` along a closed path in a convex domain equals
`sum of 2*pi*I * winding * residue(f, s)`, stated using the residue function. -/
theorem contourIntegral_eq_sum_winding_residues_convex
    {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    (γ : PiecewiseC1Path x x)
    (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (hS_sub : ↑S ⊆ U)
    (h_pole : ∀ s ∈ S, HasSimplePoleAt f s)
    (h_coeff : ∀ (s : ℂ) (hs : s ∈ S), (h_pole s hs).coeff = c s)
    (h_res : ∀ s ∈ S, residue f s = c s)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (fun z => f z - principalPartSum S c z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (principalPartSum S c) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (c s / (γ.toPath.extend t - s)) * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * residue f s := by
  rw [contourIntegral_eq_sum_winding_coefficients_convex γ hU_convex hU_open hU_ne
    hf_diff hS_sub h_pole h_coeff hγ hγ_avoids hδ h_rem_int h_pp_int hI]
  exact Finset.sum_congr rfl fun s hs => by rw [h_res s hs]

end
