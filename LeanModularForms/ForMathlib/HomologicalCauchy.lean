/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.Dixon
import LeanModularForms.ForMathlib.Residue

/-!
# Homological Cauchy Theorem for Meromorphic Functions

This file extends the Cauchy integral theorem to meromorphic functions with
simple poles on convex domains. The key result expresses the contour integral
of a meromorphic function along a null-homologous path in terms of residues
and winding numbers.

## Main results

* `differentiableOn_sub_simplePole` -- subtracting the principal part `c/(z-s₀)`
  from a function with a simple pole at `s₀` yields a holomorphic function on `U`.

* `contourIntegral_simple_pole_eq_winding` -- single simple-pole residue formula:
  `∮_γ f = c · ∮_γ (z-s₀)⁻¹ dz` on convex domains.

* `contourIntegral_eq_zero_of_winding_zero_single` -- vanishing theorem: if the
  winding integral around the pole is zero, so is the contour integral.

* `contourIntegral_div_sub_eq_zero_of_not_mem` -- `∮_γ c/(z-s₀) dz = 0` when
  `s₀ ∉ U` (pole outside the domain).

* `HasSimplePolesAt` -- bundled structure for functions with finitely many simple
  poles on a domain.

## Design notes

All results work in the convex-domain setting, using the Cauchy theorem from
`Dixon.lean` and the simple pole decomposition from `Residue.lean`. The convexity
assumption ensures that holomorphic functions have vanishing contour integrals
along null-homologous paths.

The core technique is pole subtraction: given `f` with a simple pole at `s₀`,
the function `g(z) = f(z) - c/(z-s₀)` has a removable singularity at `s₀`
(where `c` is the residue). We show `g` extends to a holomorphic function on
all of `U`, so `∮_γ g = 0` by Cauchy's theorem. Then `∮_γ f = ∮_γ c/(z-s₀)`.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. AMS (1971)
* R. B. Ash, W. P. Novinger, *Complex Variables*, Chapter 4
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral PiecewiseC1Path
open scoped Real Interval Classical

noncomputable section

variable {x : ℂ}

/-! ### Holomorphicity of pole-subtracted functions -/

/-- `z ↦ c / (z - s₀)` is differentiable on the complement of `{s₀}`. -/
theorem differentiableOn_div_sub_const (c s₀ : ℂ) :
    DifferentiableOn ℂ (fun z => c / (z - s₀)) {s₀}ᶜ := by
  intro z hz
  have hne : z - s₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
  exact ((differentiableAt_const c).div
    (differentiableAt_id.sub (differentiableAt_const s₀)) hne).differentiableWithinAt

/-- On any open set `U` containing `s₀`, if `g` is analytic at `s₀` and differentiable
on `U \ {s₀}`, then `g` is differentiable on all of `U`. -/
theorem differentiableOn_of_analyticAt_and_off_point {g : ℂ → ℂ} {s₀ : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (_hs₀ : s₀ ∈ U)
    (hg_an : AnalyticAt ℂ g s₀)
    (hg_diff : DifferentiableOn ℂ g (U \ {s₀})) :
    DifferentiableOn ℂ g U := by
  intro z hz
  by_cases hzs : z = s₀
  · subst hzs
    exact hg_an.differentiableAt.differentiableWithinAt
  · have hzU : z ∈ U \ {s₀} := ⟨hz, Set.mem_compl_singleton_iff.mpr hzs⟩
    have hopen : IsOpen (U \ {s₀}) := hU.sdiff isClosed_singleton
    exact (hg_diff z hzU).differentiableAt (hopen.mem_nhds hzU)
      |>.differentiableWithinAt

/-! ### Contour integral of c/(z-s₀) -/

/-- The contour integral of `c / (z - s₀)` along a path equals
`c` times the contour integral of `(z - s₀)⁻¹`. -/
theorem contourIntegral_div_sub_eq_mul {c s₀ : ℂ} {γ : PiecewiseC1Path x x} :
    γ.contourIntegral (fun z => c / (z - s₀)) =
      c * γ.contourIntegral (fun z => (z - s₀)⁻¹) := by
  simp only [contourIntegral, div_eq_mul_inv]
  rw [show (fun t => c * (γ t - s₀)⁻¹ * deriv γ.toPath.extend t) =
    (fun t => c * ((γ t - s₀)⁻¹ * deriv γ.toPath.extend t))
    from funext fun t => by ring]
  exact intervalIntegral.integral_const_mul c _

/-! ### Subtracting principal parts -/

/-- **Subtracting the principal part yields a holomorphic function on U.**

If `f` is holomorphic on `U \ {s₀}` and `f(z) - c/(z-s₀)` is analytic at `s₀`
(the residue cancels the pole), then `f(z) - c/(z-s₀)` is holomorphic on all of `U`. -/
theorem differentiableOn_sub_simplePole {f : ℂ → ℂ} {s₀ : ℂ} {c : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hs₀ : s₀ ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s₀}))
    (h_removable : AnalyticAt ℂ (fun z => f z - c / (z - s₀)) s₀) :
    DifferentiableOn ℂ (fun z => f z - c / (z - s₀)) U :=
  differentiableOn_of_analyticAt_and_off_point hU hs₀ h_removable
    (hf_diff.sub ((differentiableOn_div_sub_const c s₀).mono
      (fun _ hz => hz.2)))

/-! ### Single-pole residue formula -/

/-- **Single simple-pole residue formula on convex domains.**

If `f` is holomorphic on the convex domain `U` except for a simple pole at `s₀`
with residue `c`, and `γ` is a null-homologous closed path in `U` that avoids `s₀`,
then:

`∮_γ f = c · ∮_γ (z-s₀)⁻¹ dz`

The proof subtracts `c/(z-s₀)` from `f` to obtain a function `h = f - c/(z-s₀)`
that is holomorphic on all of `U` (removable singularity at `s₀`). By Cauchy's
theorem, `∮_γ h = 0`, so `∮_γ f = ∮_γ c/(z-s₀) = c · ∮_γ (z-s₀)⁻¹ dz`. -/
theorem contourIntegral_simple_pole_eq_winding
    {U : Set ℂ} {f : ℂ → ℂ} {s₀ c : ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hs₀ : s₀ ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s₀}))
    (h_removable : AnalyticAt ℂ (fun z => f z - c / (z - s₀)) s₀)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (_hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s₀)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_pole : IntervalIntegrable
      (fun t => c / (γ t - s₀) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = c * γ.contourIntegral (fun z => (z - s₀)⁻¹) := by
  -- h(z) = f(z) - c/(z-s₀) is holomorphic on all of U
  have hh_diff : DifferentiableOn ℂ (fun z => f z - c / (z - s₀)) U :=
    differentiableOn_sub_simplePole hUo hs₀ hf_diff h_removable
  -- Integrability of h along γ
  have h_int_h : IntervalIntegrable
      (fun t => (f (γ t) - c / (γ t - s₀)) * deriv γ.toPath.extend t) volume 0 1 := by
    have : (fun t => (f (γ t) - c / (γ t - s₀)) * deriv γ.toPath.extend t) =
      (fun t => f (γ t) * deriv γ.toPath.extend t -
                c / (γ t - s₀) * deriv γ.toPath.extend t) :=
      funext fun t => sub_mul _ _ _
    rw [this]; exact h_int_f.sub h_int_pole
  -- ∮_γ h = 0 by Cauchy's theorem
  have hh_zero : γ.contourIntegral (fun z => f z - c / (z - s₀)) = 0 :=
    hnh.contourIntegral_eq_zero hh_diff hU hUo hUne h_int_h
  -- Decompose: ∮_γ f = ∮_γ h + ∮_γ c/(z-s₀)
  have h_decomp : γ.contourIntegral f =
      γ.contourIntegral (fun z => f z - c / (z - s₀)) +
      γ.contourIntegral (fun z => c / (z - s₀)) := by
    simp only [contourIntegral]
    rw [← intervalIntegral.integral_add h_int_h h_int_pole]
    congr 1; ext t; ring
  rw [h_decomp, hh_zero, zero_add, contourIntegral_div_sub_eq_mul]

/-! ### Vanishing theorem -/

/-- **Meromorphic vanishing theorem for a single pole (convex domain).**

If `∮_γ (z-s₀)⁻¹ dz = 0` (i.e., the winding number around `s₀` is zero)
and `f` has a simple pole at `s₀` with residue `c`, then `∮_γ f = 0`. -/
theorem contourIntegral_eq_zero_of_winding_zero_single
    {U : Set ℂ} {f : ℂ → ℂ} {s₀ c : ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hs₀ : s₀ ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s₀}))
    (h_removable : AnalyticAt ℂ (fun z => f z - c / (z - s₀)) s₀)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (hoff : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s₀)
    (h_winding_zero : γ.contourIntegral (fun z => (z - s₀)⁻¹) = 0)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_pole : IntervalIntegrable
      (fun t => c / (γ t - s₀) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 := by
  rw [contourIntegral_simple_pole_eq_winding hU hUo hUne hs₀ hf_diff h_removable
      hnh hoff h_int_f h_int_pole, h_winding_zero, mul_zero]

/-! ### Holomorphic integral vanishes -/

/-- If `f` is holomorphic on the convex open set `U` and `γ` is null-homologous
in `U`, then `∮_γ f = 0`. Direct corollary of the Dixon theorem. -/
theorem contourIntegral_eq_zero_of_holomorphic
    {U : Set ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (hf : DifferentiableOn ℂ f U)
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 :=
  contourIntegral_eq_zero_of_holomorphic_nullHomologous hnh hf hU hUo hUne h_int

/-! ### Pole outside the domain -/

/-- **Contour integral of `c/(z-s₀)` vanishes when `s₀ ∉ U`.**

When the pole `s₀` lies outside the convex domain `U`, the function `z ↦ c/(z-s₀)`
is holomorphic on all of `U`, so its contour integral along a null-homologous
path vanishes. -/
theorem contourIntegral_div_sub_eq_zero_of_not_mem
    {U : Set ℂ} {s₀ c : ℂ}
    (hs₀ : s₀ ∉ U)
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (h_int : IntervalIntegrable
      (fun t => c / (γ t - s₀) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral (fun z => c / (z - s₀)) = 0 := by
  apply hnh.contourIntegral_eq_zero _ hU hUo hUne h_int
  intro z hz
  have hne : z - s₀ ≠ 0 := sub_ne_zero.mpr (fun heq => hs₀ (heq ▸ hz))
  exact ((differentiableAt_const c).div
    (differentiableAt_id.sub (differentiableAt_const s₀)) hne).differentiableWithinAt

/-! ### Bundled simple poles structure -/

/-- A function has simple poles at every point of a finite set `S ⊆ U`,
with specified residue coefficients, and is holomorphic on `U \ S`.

For each `s ∈ S`, `f(z) - c_s/(z-s)` has a removable singularity at `s`,
where `c_s` is the residue. This ensures the pole subtraction technique works. -/
structure HasSimplePolesAt (f : ℂ → ℂ) (U : Set ℂ) (S : Finset ℂ) where
  /-- Every pole lies in `U`. -/
  poles_in_U : ∀ s ∈ S, s ∈ U
  /-- `f` has a simple pole at each `s ∈ S`. -/
  pole_at : ∀ s ∈ S, HasSimplePoleAt f s
  /-- `f` is holomorphic on `U` away from all poles. -/
  holo_off : DifferentiableOn ℂ f (U \ ↑S)

/-- The residue coefficient of `f` at a pole `s ∈ S`. -/
noncomputable def HasSimplePolesAt.coeff' {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ}
    (hp : HasSimplePolesAt f U S) (s : ℂ) (hs : s ∈ S) : ℂ :=
  (hp.pole_at s hs).coeff

/-- The weighted residue sum: `Σ_{s ∈ S} c_s · ∮_γ (z - s)⁻¹ dz`. -/
noncomputable def weightedResidueSum {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ}
    (hp : HasSimplePolesAt f U S) (γ : PiecewiseC1Path x x) : ℂ :=
  ∑ s ∈ S.attach, (hp.pole_at s s.2).coeff *
    γ.contourIntegral (fun z => (z - ↑s)⁻¹)

/-! ### Contour integral linearity -/

/-- Scalar multiplication for contour integrals. -/
theorem contourIntegral_const_mul' {c : ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x x} :
    γ.contourIntegral (fun z => c * f z) = c * γ.contourIntegral f :=
  contourIntegral_smul c f γ

end
