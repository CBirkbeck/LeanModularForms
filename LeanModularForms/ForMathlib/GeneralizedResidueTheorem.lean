/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HomologicalCauchy
import LeanModularForms.ForMathlib.HigherOrderPoles

/-!
# The Generalized Residue Theorem (Simple Poles)

This file proves the generalized residue theorem for meromorphic functions with
finitely many simple poles on convex domains. This is the main theorem of Chain 1.

The key result expresses the contour integral of a meromorphic function with simple
poles along a null-homologous path in terms of residues and winding numbers:

`∮_γ f = Σ_{s ∈ S} c_s · ∮_γ (z - s)⁻¹ dz`

where `c_s` is the residue at each pole `s ∈ S`.

## Main results

* `differentiableOn_principalPartSum` -- the principal part sum
  `Σ c_s / (z - s)` is differentiable on `Sᶜ`.

* `differentiableOn_sub_principalPartSum` -- subtracting the principal part sum
  from `f` yields a function holomorphic on all of `U`, given removability hypotheses.

* `contourIntegral_principalPartSum_eq_sum` -- the contour integral of the principal
  part sum equals the sum of the individual pole contributions.

* `generalizedResidueTheorem_simplePoles` -- the residue theorem for simple poles
  on convex domains: `∮_γ f = Σ_{s ∈ S} c_s · ∮_γ (z - s)⁻¹ dz`.

* `generalizedResidueTheorem_simplePoles_winding` -- variant expressing the result
  using winding numbers: `∮_γ f = Σ_{s ∈ S} 2πi · n(γ,s) · c_s`.

* `generalizedResidueTheorem_simplePoles_classical` -- classical form with factor
  pulled out: `∮_γ f = 2πi · Σ_{s ∈ S} n(γ,s) · c_s`.

## Proof strategy

For each `s ∈ S`, `f` has a simple pole with residue `c_s`, meaning
`f(z) = c_s/(z-s) + g_s(z)` near `s` with `g_s` analytic.

Define `pp(z) = Σ_{s ∈ S} c_s/(z-s)`, the **principal part sum**.

The function `h(z) = f(z) - pp(z)` has removable singularities at each `s ∈ S`
(the principal parts cancel the poles), so `h` extends to a holomorphic function
on all of `U`. By Cauchy's theorem, `∮_γ h = 0`. By linearity of the contour
integral, `∮_γ f = ∮_γ pp = Σ c_s · ∮_γ (z-s)⁻¹ dz`.

## References

* J. D. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. AMS (1971)
* R. B. Ash, W. P. Novinger, *Complex Variables*, Chapter 4
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral PiecewiseC1Path
open scoped Real Interval Classical

noncomputable section

variable {x : ℂ}

/-! ### Principal part sum -/

/-- The principal part sum `pp(z) = Σ_{s ∈ S} c(s) / (z - s)`, where `c : ℂ → ℂ` gives
the residue coefficient at each pole. -/
def principalPartSum (S : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ s ∈ S, c s / (z - s)

/-- The principal part sum is differentiable on the complement of the poles. -/
theorem differentiableOn_principalPartSum (S : Finset ℂ) (c : ℂ → ℂ) :
    DifferentiableOn ℂ (principalPartSum S c) (↑S : Set ℂ)ᶜ := by
  unfold principalPartSum
  have heq : (fun z => ∑ s ∈ S, c s / (z - s)) =
      (∑ s ∈ S, fun z => c s / (z - s)) := by
    ext z; simp [Finset.sum_apply]
  rw [heq]
  apply DifferentiableOn.sum
  intro s hs
  apply DifferentiableOn.div (differentiableOn_const _)
    (differentiableOn_id.sub (differentiableOn_const _))
  intro z hz
  exact sub_ne_zero.mpr (fun heq => hz (heq ▸ Finset.mem_coe.mpr hs))

/-- Each term `c / (z - s)` is differentiable at points away from `s`. -/
theorem differentiableAt_div_sub_of_ne {s z : ℂ} {c : ℂ} (hne : z ≠ s) :
    DifferentiableAt ℂ (fun w => c / (w - s)) z :=
  (differentiableAt_const c).div
    (differentiableAt_id.sub (differentiableAt_const s))
    (sub_ne_zero.mpr hne)

/-! ### Holomorphicity of f - pp on all of U -/

/-- **Key lemma**: subtracting the principal part sum from `f` yields a function that is
holomorphic on all of `U`.

The hypotheses require:
1. `f` is holomorphic on `U \ S`.
2. At each pole `s₀ ∈ S`, the function `z ↦ f(z) - pp(z)` has a removable singularity
   (is analytic at `s₀`). This follows from the pole subtraction cancelling the
   singularity, but depends on the function value at the pole point.

The proof uses `differentiableOn_of_analyticAt_and_off_point` at each pole. -/
theorem differentiableOn_sub_principalPartSum
    {f : ℂ → ℂ} {U : Set ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    (hU : IsOpen U)
    (_hSU : ∀ s ∈ S, s ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (h_removable : ∀ s ∈ S,
      AnalyticAt ℂ (fun z => f z - principalPartSum S c z) s) :
    DifferentiableOn ℂ (fun z => f z - principalPartSum S c z) U := by
  intro z hz
  by_cases hzS : z ∈ (↑S : Set ℂ)
  · -- z is a pole: use the removability hypothesis
    exact (h_removable z (Finset.mem_coe.mp hzS)).differentiableAt.differentiableWithinAt
  · -- z is not a pole: both f and pp are differentiable
    have hzU' : z ∈ U \ ↑S := ⟨hz, hzS⟩
    have hU' : IsOpen (U \ ↑S) := hU.sdiff S.finite_toSet.isClosed
    -- f is differentiable at z (open set argument)
    have hf_at : DifferentiableAt ℂ f z :=
      (hf_diff z hzU').differentiableAt (hU'.mem_nhds hzU')
    -- pp is differentiable at z (z is away from all poles)
    have hpp_at : DifferentiableAt ℂ (principalPartSum S c) z := by
      unfold principalPartSum
      have heq : (fun z => ∑ s ∈ S, c s / (z - s)) =
          (∑ s ∈ S, fun z => c s / (z - s)) := by
        ext z; simp [Finset.sum_apply]
      rw [heq]
      apply DifferentiableAt.sum
      intro s hs
      exact differentiableAt_div_sub_of_ne
        (fun heq => hzS (heq ▸ Finset.mem_coe.mpr hs))
    exact (hf_at.sub hpp_at).differentiableWithinAt

/-! ### Contour integral of the principal part sum -/

/-- The contour integral of the principal part sum equals the sum of the individual
pole contributions, under integrability. The proof uses induction on the finite set
of poles, splitting off one pole at a time. -/
theorem contourIntegral_principalPartSum_eq_sum
    {S : Finset ℂ} {c : ℂ → ℂ} {γ : PiecewiseC1Path x x}
    (h_int : ∀ s ∈ S, IntervalIntegrable
      (fun t => c s / (γ t - s) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral (principalPartSum S c) =
      ∑ s ∈ S, c s * γ.contourIntegral (fun z => (z - s)⁻¹) := by
  induction S using Finset.cons_induction with
  | empty => simp [contourIntegral, principalPartSum]
  | cons a S' ha ih =>
    have h_int' : ∀ s ∈ S', IntervalIntegrable
        (fun t => c s / (γ t - s) * deriv γ.toPath.extend t) volume 0 1 :=
      fun s hs => h_int s (Finset.mem_cons.mpr (Or.inr hs))
    have ih' := ih h_int'
    have ha_int := h_int a (Finset.mem_cons_self a S')
    rw [Finset.cons_eq_insert _ _ ha] at *
    rw [Finset.sum_insert ha]
    -- Integrability of the S' part
    have h_int_S' : IntervalIntegrable
        (fun t => (∑ s ∈ S', c s / (γ t - s)) *
          deriv γ.toPath.extend t) volume 0 1 := by
      have heq : (fun t => (∑ s ∈ S', c s / (γ t - s)) *
            deriv γ.toPath.extend t) =
          (∑ s ∈ S', fun t => c s / (γ t - s) *
            deriv γ.toPath.extend t) := by
        ext t; rw [Finset.sum_apply, Finset.sum_mul]
      rw [heq]
      exact IntervalIntegrable.sum S' (fun s hs => h_int' s hs)
    -- Split the contour integral
    simp only [contourIntegral, principalPartSum] at ih' ⊢
    rw [show (fun t => (∑ s ∈ insert a S', c s / (γ t - s)) *
          deriv γ.toPath.extend t) =
      (fun t => c a / (γ t - a) * deriv γ.toPath.extend t +
        (∑ s ∈ S', c s / (γ t - s)) * deriv γ.toPath.extend t)
      from funext fun t => by rw [Finset.sum_insert ha]; ring]
    rw [intervalIntegral.integral_add ha_int h_int_S', ih']
    congr 1
    -- c(a)/(γ t - a) = c(a) * (γ t - a)⁻¹
    rw [show (fun t => c a / (γ t - a) * deriv γ.toPath.extend t) =
      (fun t => c a * ((γ t - a)⁻¹ * deriv γ.toPath.extend t))
      from funext fun t => by rw [div_eq_mul_inv]; ring]
    exact intervalIntegral.integral_const_mul _ _

/-! ### The Generalized Residue Theorem (Simple Poles) -/

/-- **Generalized Residue Theorem for Simple Poles on Convex Domains.**

If `f` is meromorphic on a convex open domain `U` with simple poles at `S ⊆ U` and
residue coefficients `c`, and `γ` is a null-homologous closed path in `U`, then:

`∮_γ f = Σ_{s ∈ S} c(s) · ∮_γ (z - s)⁻¹ dz`

The proof subtracts the principal part sum `pp(z) = Σ c(s)/(z-s)` from `f`. The
function `h = f - pp` is holomorphic on `U` (each pole's singularity is cancelled
by the corresponding term in `pp`). By Cauchy's theorem, `∮_γ h = 0`. By linearity,
`∮_γ f = ∮_γ pp = Σ c(s) · ∮_γ (z-s)⁻¹ dz`. -/
theorem generalizedResidueTheorem_simplePoles
    {U : Set ℂ} {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hSU : ∀ s ∈ S, s ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (h_removable : ∀ s ∈ S,
      AnalyticAt ℂ (fun z => f z - principalPartSum S c z) s)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_pp : IntervalIntegrable
      (fun t => principalPartSum S c (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_poles : ∀ s ∈ S, IntervalIntegrable
      (fun t => c s / (γ t - s) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, c s * γ.contourIntegral (fun z => (z - s)⁻¹) := by
  -- Step 1: h(z) = f(z) - pp(z) is holomorphic on U
  have hh_diff := differentiableOn_sub_principalPartSum hUo hSU hf_diff h_removable
  -- Step 2: ∮_γ h = 0 by Cauchy's theorem
  have h_int_h : IntervalIntegrable
      (fun t => (f (γ t) - principalPartSum S c (γ t)) *
        deriv γ.toPath.extend t) volume 0 1 := by
    have : (fun t => (f (γ t) - principalPartSum S c (γ t)) *
        deriv γ.toPath.extend t) =
      (fun t => f (γ t) * deriv γ.toPath.extend t -
        principalPartSum S c (γ t) * deriv γ.toPath.extend t) :=
      funext fun t => sub_mul _ _ _
    rw [this]; exact h_int_f.sub h_int_pp
  have hh_zero : γ.contourIntegral (fun z => f z - principalPartSum S c z) = 0 :=
    hnh.contourIntegral_eq_zero hh_diff hU hUo hUne h_int_h
  -- Step 3: ∮_γ f = ∮_γ pp
  have h_decomp : γ.contourIntegral f =
      γ.contourIntegral (fun z => f z - principalPartSum S c z) +
      γ.contourIntegral (principalPartSum S c) := by
    simp only [contourIntegral]
    rw [← intervalIntegral.integral_add h_int_h h_int_pp]
    congr 1; ext t; ring
  rw [h_decomp, hh_zero, zero_add]
  -- Step 4: ∮_γ pp = Σ c(s) · ∮_γ (z-s)⁻¹
  exact contourIntegral_principalPartSum_eq_sum h_int_poles

/-! ### Winding number form -/

/-- **Generalized Residue Theorem -- Winding Number Form.**

If additionally the contour integral of `(z-s)⁻¹` is known at each pole, then:

`∮_γ f = Σ_{s ∈ S} 2πi · n(s) · c(s)`

This follows from the basic residue theorem plus the substitution
`∮_γ (z - s)⁻¹ dz = 2πi · n(s)`. -/
theorem generalizedResidueTheorem_simplePoles_winding
    {U : Set ℂ} {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} {n : ℂ → ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hSU : ∀ s ∈ S, s ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (h_removable : ∀ s ∈ S,
      AnalyticAt ℂ (fun z => f z - principalPartSum S c z) s)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (h_winding : ∀ s ∈ S,
      γ.contourIntegral (fun z => (z - s)⁻¹) = 2 * ↑Real.pi * I * n s)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_pp : IntervalIntegrable
      (fun t => principalPartSum S c (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_poles : ∀ s ∈ S, IntervalIntegrable
      (fun t => c s / (γ t - s) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * n s * c s := by
  rw [generalizedResidueTheorem_simplePoles hU hUo hUne hSU hf_diff h_removable
      hnh h_int_f h_int_pp h_int_poles]
  apply Finset.sum_congr rfl
  intro s hs
  rw [h_winding s hs]; ring

/-- **Generalized Residue Theorem -- 2πi · Σ n(γ,s) · Res(f,s) Form.**

The classical form with the `2πi` factor pulled out:

`∮_γ f = 2πi · Σ_{s ∈ S} n(γ, s) · c(s)` -/
theorem generalizedResidueTheorem_simplePoles_classical
    {U : Set ℂ} {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ} {n : ℂ → ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hSU : ∀ s ∈ S, s ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (h_removable : ∀ s ∈ S,
      AnalyticAt ℂ (fun z => f z - principalPartSum S c z) s)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (h_winding : ∀ s ∈ S,
      γ.contourIntegral (fun z => (z - s)⁻¹) = 2 * ↑Real.pi * I * n s)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_pp : IntervalIntegrable
      (fun t => principalPartSum S c (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_poles : ∀ s ∈ S, IntervalIntegrable
      (fun t => c s / (γ t - s) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 2 * ↑Real.pi * I * ∑ s ∈ S, n s * c s := by
  rw [generalizedResidueTheorem_simplePoles_winding hU hUo hUne hSU hf_diff h_removable
      hnh h_winding h_int_f h_int_pp h_int_poles, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _hs; ring

/-! ### Empty pole set -/

/-- When there are no poles (`S = ∅`), the residue theorem reduces to Cauchy's theorem. -/
theorem generalizedResidueTheorem_empty
    {U : Set ℂ} {f : ℂ → ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hf_diff : DifferentiableOn ℂ f U)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 :=
  hnh.contourIntegral_eq_zero hf_diff hU hUo hUne h_int_f

/-! ### Single pole specialization -/

/-- **Residue Theorem for a Single Simple Pole.**

When there is exactly one pole at `s₀` with residue coefficient `c₀`:

`∮_γ f = c₀ · ∮_γ (z - s₀)⁻¹ dz`

This specializes the multi-pole theorem to `S = {s₀}`. The removability hypothesis
becomes: `f(z) - c₀/(z-s₀)` is analytic at `s₀` (the pole is cancelled). -/
theorem generalizedResidueTheorem_singleton
    {U : Set ℂ} {f : ℂ → ℂ} {s₀ c₀ : ℂ}
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    (hs₀ : s₀ ∈ U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s₀}))
    (h_removable : AnalyticAt ℂ (fun z => f z - c₀ / (z - s₀)) s₀)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_pole : IntervalIntegrable
      (fun t => c₀ / (γ t - s₀) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = c₀ * γ.contourIntegral (fun z => (z - s₀)⁻¹) := by
  have h := generalizedResidueTheorem_simplePoles (S := {s₀})
    (c := fun _ => c₀) hU hUo hUne
    (fun s hs => by rwa [Finset.mem_singleton.mp hs])
    (by rwa [Finset.coe_singleton])
    (fun s hs => by
      rw [Finset.mem_singleton.mp hs]
      convert h_removable using 1
      ext z; simp [principalPartSum])
    hnh h_int_f
    (by convert h_int_pole using 1; ext t; simp [principalPartSum])
    (fun s hs => by rwa [Finset.mem_singleton.mp hs])
  rw [h]; simp

/-! ### Bundled form using HasSimplePolesAt -/

/-- **Generalized Residue Theorem using the bundled `HasSimplePolesAt` structure.**

If `hp : HasSimplePolesAt f U S` (bundling pole locations, residues, and holomorphicity)
and `γ` is null-homologous in `U`, then:

`∮_γ f = Σ_{s ∈ S} c_s · ∮_γ (z - s)⁻¹ dz`

where `c_s` is the residue coefficient. The removability of singularities must be
provided separately (it depends on the function values at the pole points). -/
theorem generalizedResidueTheorem_convex
    {U : Set ℂ} {f : ℂ → ℂ} {S : Finset ℂ}
    (hp : HasSimplePolesAt f U S)
    (hU : Convex ℝ U) (hUo : IsOpen U) (hUne : U.Nonempty)
    {c : ℂ → ℂ}
    (h_removable : ∀ s ∈ S,
      AnalyticAt ℂ (fun z => f z - principalPartSum S c z) s)
    {γ : PiecewiseC1Path x x} (hnh : IsNullHomologous γ U)
    (h_int_f : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_pp : IntervalIntegrable
      (fun t => principalPartSum S c (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (h_int_poles : ∀ s ∈ S, IntervalIntegrable
      (fun t => c s / (γ t - s) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, c s * γ.contourIntegral (fun z => (z - s)⁻¹) :=
  generalizedResidueTheorem_simplePoles hU hUo hUne hp.poles_in_U
    hp.holo_off h_removable hnh h_int_f h_int_pp h_int_poles

end
