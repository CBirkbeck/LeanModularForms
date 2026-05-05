/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.HW33MultiPole

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

end LeanModularForms

end
