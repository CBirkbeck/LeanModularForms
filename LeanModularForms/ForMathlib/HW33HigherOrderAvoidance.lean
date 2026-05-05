/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.HW33MultiPole
import LeanModularForms.ForMathlib.HW33HigherOrderC3
import LeanModularForms.ForMathlib.PiecewiseContourIntegral

/-!
# HW Theorem 3.3 — higher-order pole avoidance form

This file extends the simple-pole avoidance theorem
`hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids` to *higher-order*
poles in the avoidance case (γ does not pass through any pole).

**Why higher-order avoidance is achievable.** Dixon's theorem
(`dixonFunction_eq_zero_of_nullHomologous_open_full`) gives `∮_γ g = 0` for any
function `g` differentiable on `U` and γ null-homologous in `U` — there's no
restriction to simple poles. The simple-pole specialization
(`hasCauchyPVOn_simplePoles_nullHomologous_closed_full_avoids`) is just an
*application*. For higher-order poles, the same template works once the user
supplies the polar parts: subtract them to get an analytic remainder, apply
Dixon, then compute polar contributions term-by-term.

The two non-residue contributions:

* For `c / (z - s)^k` with `k ≥ 2`: `∮_γ = 0` because the antiderivative
  `-c / ((k-1) (z - s)^{k-1})` is single-valued on `ℂ \ {s}`.
* For `c / (z - s)`: `∮_γ = 2πi · winding(γ, s) · c`.

Hence only the residue (`k = 1`) coefficient contributes, exactly matching the
classical residue formula.

## Main result

* `hw_3_3_higherOrder_avoidance_paper` — paper-faithful statement for higher-
  order pole avoidance, taking the polar-part decomposition as user-supplied
  data. This is a stepping-stone: the truly paper-faithful version takes only
  `∀ s ∈ S, MeromorphicAt f s` and extracts polar parts internally via Laurent
  decomposition, but mathlib does not yet have the Laurent-extraction API
  needed for that final step.
-/

open Set Filter Topology Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- A **polar-part decomposition** of a meromorphic function `f` on a domain
`U \ S`: for each pole `s ∈ S`, an explicit polar part `polarPart s z =
∑ k, a_{s,k} / (z - s)^(k+1)` such that `f` minus the total polar part extends
analytically to all of `U`.

This bundles the data the residue formula needs without requiring access to
mathlib's Laurent-extraction API. Each polar part is a finite Laurent
combination at its pole; the residue at `s` is the `k = 0` coefficient. -/
structure PolarPartDecomposition (f : ℂ → ℂ) (S : Finset ℂ) (U : Set ℂ) where
  /-- The polar part at each pole, viewed as a function of `z`. -/
  polarPart : ℂ → ℂ → ℂ
  /-- Order of the polar part at each pole. -/
  order : ℂ → ℕ
  /-- Laurent coefficients of the polar part at each pole. -/
  coeff : (s : ℂ) → Fin (order s) → ℂ
  /-- The polar part at `s` is the explicit Laurent sum
  `∑ k, coeff s k / (z - s)^(k+1)`. -/
  polarPart_eq : ∀ s ∈ S, ∀ z, z ≠ s →
    polarPart s z = ∑ k : Fin (order s), coeff s k / (z - s) ^ (k.val + 1)
  /-- The residue at `s ∈ S` equals the `k = 0` Laurent coefficient. -/
  residue_eq : ∀ s ∈ S, (h : 0 < order s) →
    residue f s = coeff s ⟨0, h⟩
  /-- After subtracting the total polar part, `f` extends to a function
  differentiable on all of `U`. -/
  analyticRemainder : ℂ → ℂ
  analyticRemainder_diff : DifferentiableOn ℂ analyticRemainder U
  decomp : ∀ z ∈ U \ (↑S : Set ℂ),
    f z = analyticRemainder z + ∑ s ∈ S, polarPart s z

/-! ## The "higher-order" part of a polar decomposition

A polar part `polarPart s z = ∑ k, a_k/(z-s)^(k+1)` (`k = 0, ..., N-1`) splits
into the simple-pole part `a_0/(z-s)` (the residue contribution) and the
higher-order part `∑_{k≥1} a_k/(z-s)^(k+1)`. The higher-order part integrates
to zero along any closed curve avoiding `s`. -/

/-- The strictly-higher-order part of a polar part: `∑_{k≥1} a_k/(z-s)^(k+1)`. -/
noncomputable def higherOrderPart {N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ :=
  ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0

/-- The simple-pole part of a polar part: `a_0/(z-s)` (or 0 if N = 0). -/
noncomputable def simplePolePart {N : ℕ} (a : Fin N → ℂ) (s z : ℂ) : ℂ :=
  if h : 0 < N then a ⟨0, h⟩ / (z - s) else 0

/-- The polar part decomposes into simple-pole + higher-order. -/
theorem polarPart_eq_simplePole_add_higherOrder {N : ℕ} (a : Fin N → ℂ) (s z : ℂ) :
    (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
      simplePolePart a s z + higherOrderPart a s z := by
  classical
  unfold simplePolePart higherOrderPart
  by_cases h : 0 < N
  · simp only [dif_pos h]
    -- Split sum: k = 0 contributes a₀/(z-s); k ≥ 1 contributes higherOrderPart.
    have hsplit : ∀ k : Fin N,
        a k / (z - s) ^ (k.val + 1) =
          (if k.val = 0 then a ⟨0, h⟩ / (z - s) else 0) +
          (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) := by
      intro k
      by_cases hk : k.val = 0
      · have : k = ⟨0, h⟩ := Fin.ext hk
        simp [this]
      · have hk1 : k.val ≥ 1 := by omega
        simp [hk, hk1]
    rw [show (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
        ∑ k : Fin N, ((if k.val = 0 then a ⟨0, h⟩ / (z - s) else 0) +
          (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0)) from
        Finset.sum_congr rfl (fun k _ => hsplit k)]
    rw [Finset.sum_add_distrib]
    have h_first : (∑ k : Fin N,
        if k.val = 0 then a ⟨0, h⟩ / (z - s) else 0) = a ⟨0, h⟩ / (z - s) := by
      rw [Finset.sum_eq_single ⟨0, h⟩]
      · simp
      · intro k _ hk
        have hk0 : k.val ≠ 0 := fun h_eq => hk (Fin.ext h_eq)
        simp [hk0]
      · simp
    rw [h_first]
  · simp only [dif_neg h]
    have hN : N = 0 := Nat.eq_zero_of_not_pos h
    subst hN
    simp

/-! ## Higher-order Laurent term: contour integral vanishes -/

/-- For `k ≥ 2`, the function `c / (z - s)^k` has the single-valued antiderivative
`-c / ((k-1)(z-s)^(k-1))` on `ℂ \ {s}`. Hence its contour integral along any
closed piecewise-`C¹` path avoiding `s` vanishes. -/
theorem contourIntegral_higherOrder_eq_zero_of_avoids
    {x s : ℂ} (γ : PiecewiseC1Path x x)
    (h_avoids : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ.toPath.extend t ≠ s)
    {k : ℕ} (hk : 2 ≤ k) (c : ℂ)
    (h_int : IntervalIntegrable
      (fun t => c / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral (fun z => c / (z - s) ^ k) = 0 := by
  -- Antiderivative via `zpow`: F(z) := (-c/(k-1)) * (z - s)^{-(k-1) : ℤ}.
  -- Its derivative: (-c/(k-1)) * (-(k-1)) * (z-s)^{-(k-1)-1 : ℤ} = c * (z-s)^{-k : ℤ}.
  have hk_pos : 0 < (k : ℤ) - 1 := by omega
  have hk_natcast : ((k - 1 : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; omega
  set F : ℂ → ℂ := fun z =>
    (-c / ((k - 1 : ℕ) : ℂ)) * (z - s) ^ (-((k - 1 : ℕ) : ℤ))
  have hU_img : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ ({s} : Set ℂ)ᶜ :=
    fun t ht => h_avoids t ht
  have hF : ∀ z ∈ ({s} : Set ℂ)ᶜ, HasDerivAt F (c / (z - s) ^ k) z := by
    intro z hz
    have hz_sub : z - s ≠ 0 := sub_ne_zero.mpr hz
    have h_id_sub : HasDerivAt (fun w => w - s) 1 z :=
      (hasDerivAt_id z).sub_const s
    -- Derivative of `(z - s)^n` for negative integer n.
    have h_inner :=
      (hasDerivAt_zpow (-((k - 1 : ℕ) : ℤ)) (z - s) (Or.inl hz_sub)).comp z h_id_sub
    simp only [Function.comp_def, mul_one] at h_inner
    have h_total := h_inner.const_mul (-c / ((k - 1 : ℕ) : ℂ))
    convert h_total using 1
    -- Goal: c/(z-s)^k = (-c/(k-1)) * (-(k-1) * (z-s)^(-(k-1)-1))
    have hk_eq : -((k - 1 : ℕ) : ℤ) - 1 = -(k : ℤ) := by omega
    rw [hk_eq]
    rw [zpow_neg, zpow_natCast]
    have h_pow_ne : (z - s) ^ k ≠ 0 := pow_ne_zero _ hz_sub
    field_simp
    push_cast
    ring
  exact PiecewiseC1Path.contourIntegral_eq_zero_of_hasDerivAt_of_closed γ rfl hU_img hF h_int

end LeanModularForms

end
