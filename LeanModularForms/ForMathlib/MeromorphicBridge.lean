/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.ResidueCircleIntegral
import Mathlib.Analysis.Meromorphic.Order

/-!
# Bridge: `HasSimplePoleAt` and Mathlib `MeromorphicAt`

This file connects the project's `HasSimplePoleAt` decomposition to Mathlib's
`MeromorphicAt` / `meromorphicOrderAt` API.

## Main results

* `HasSimplePoleAt.meromorphicAt` -- a simple pole is meromorphic.
* `meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt` -- a simple pole with nonzero
  coefficient has meromorphic order exactly `-1`.
* `meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero` -- a simple pole with zero
  coefficient has non-negative order (the function is effectively analytic).
* `hasSimplePoleAt_of_meromorphicAt_order_neg_one` -- converse: meromorphic order `-1`
  implies `HasSimplePoleAt`.
* `residue_eq_leadingCoeff_of_order_neg_one` -- the residue equals the leading
  coefficient `g(z_0)` from Mathlib's meromorphic factorization at order `-1`.
* `hasSimplePoleAt_of_analyticAt` -- an analytic function has a simple pole decomposition
  with coefficient `0`.

## Design

The key algebraic identity underlying most proofs is:

  `c / (z - z_0) + g(z) = (z - z_0)^(-1) * (c + (z - z_0) * g(z))`

where `c + (z - z_0) * g(z)` is analytic at `z_0` with value `c` there. This converts
between the project's additive decomposition and Mathlib's multiplicative factorization.

For the converse direction, we use the analytic order factorization: if `g` is analytic
at `z_0`, then `g(z) - g(z_0) = (z - z_0) * h(z)` for some analytic `h`, giving
`(z - z_0)^(-1) * g(z) = g(z_0) / (z - z_0) + h(z)`.
-/

open Complex Set Filter Topology

section

/-! ### Forward direction: `HasSimplePoleAt` to `MeromorphicAt` -/

/-- A function with a simple pole at `z_0` is meromorphic at `z_0`.

The proof rewrites the additive decomposition `f(z) = c/(z-z_0) + g(z)` into
`f(z) = (z-z_0)^(-1) * (c + (z-z_0) * g(z))` and checks that
`z |-> c + (z-z_0) * g(z)` is analytic. -/
theorem HasSimplePoleAt.meromorphicAt {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) : MeromorphicAt f z₀ := by
  obtain ⟨c, g, hg_an, hf_eq⟩ := h
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  refine ⟨-1, fun z => c + (z - z₀) * g z,
    analyticAt_const.add (analyticAt_id.sub analyticAt_const |>.mul hg_an), ?_⟩
  filter_upwards [hf_eq, self_mem_nhdsWithin] with z hz hne
  have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [hz]
  simp only [zpow_neg_one, smul_eq_mul]
  field_simp

/-! ### Meromorphic order of simple poles -/

/-- A simple pole with nonzero coefficient has meromorphic order exactly `-1`.

The witness for `meromorphicOrderAt_eq_int_iff` is `G(z) = c + (z - z_0) * g(z)`
where `G(z_0) = c /= 0`. -/
theorem meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) (hc : h.coeff ≠ 0) :
    meromorphicOrderAt f z₀ = (-1 : ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff h.meromorphicAt]
  refine ⟨fun z => h.coeff + (z - z₀) * h.regularPart z,
    analyticAt_const.add
      (analyticAt_id.sub analyticAt_const |>.mul h.regularPart_analyticAt),
    by simp [hc], ?_⟩
  filter_upwards [h.eventually_eq, self_mem_nhdsWithin] with z hz hne
  have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [hz]
  simp only [zpow_neg_one, smul_eq_mul]
  field_simp

/-- A simple pole with zero coefficient has non-negative meromorphic order: the
function is eventually equal to its analytic regular part. -/
theorem meromorphicOrderAt_nonneg_of_hasSimplePoleAt_coeff_zero {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) (hc : h.coeff = 0) :
    (0 : ℤ) ≤ meromorphicOrderAt f z₀ := by
  have hev : f =ᶠ[𝓝[≠] z₀] h.regularPart := by
    filter_upwards [h.eventually_eq] with z hz
    rw [hz, hc, zero_div, zero_add]
  rw [meromorphicOrderAt_congr hev]
  exact h.regularPart_analyticAt.meromorphicOrderAt_nonneg

/-! ### Converse: `MeromorphicAt` with order `-1` to `HasSimplePoleAt` -/

/-- Internal: from `f =ᶠ (z - z_0)^(-1) * g(z)` with `g` analytic, factor
`g z = g z₀ + (z - z₀) * h(z)` and rewrite as `f =ᶠ g(z_0)/(z - z_0) + h(z)`. -/
private lemma simplePoleDecomp_of_eventuallyEq_zpow_neg_one
    {f g : ℂ → ℂ} {z₀ : ℂ} (hg_an : AnalyticAt ℂ g z₀)
    (hg_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-1 : ℤ) • g z) :
    ∃ h_fn : ℂ → ℂ, AnalyticAt ℂ h_fn z₀ ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z = g z₀ / (z - z₀) + h_fn z := by
  have h_an_diff : AnalyticAt ℂ (fun z => g z - g z₀) z₀ := hg_an.sub analyticAt_const
  have h_ord : 1 ≤ analyticOrderAt (fun z => g z - g z₀) z₀ := by
    rw [← not_lt, ENat.lt_one_iff_eq_zero]
    exact h_an_diff.analyticOrderAt_ne_zero.mpr (by simp)
  obtain ⟨h_fn, hh_an, hh_eq⟩ := (natCast_le_analyticOrderAt h_an_diff).mp h_ord
  refine ⟨h_fn, hh_an, ?_⟩
  filter_upwards [hg_eq, hh_eq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with z hz hh hne
  have hzsub : z - z₀ ≠ 0 := sub_ne_zero.mpr hne
  rw [hz]
  simp only [zpow_neg_one, smul_eq_mul, pow_one] at hh ⊢
  have hg_val : g z = g z₀ + (z - z₀) * h_fn z := by linear_combination hh
  rw [hg_val]
  field_simp

/-- If `f` is meromorphic at `z_0` with order exactly `-1`, then `f` has a simple pole
at `z_0`.

From Mathlib's factorization `f =ᶠ (z - z_0)^(-1) * g(z)` with `g` analytic, we write
`g(z) = g(z_0) + (z - z_0) * h(z)` (analytic order factorization of `g - g(z_0)`),
giving `f =ᶠ g(z_0)/(z - z_0) + h(z)`. -/
theorem hasSimplePoleAt_of_meromorphicAt_order_neg_one {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ = (-1 : ℤ)) :
    HasSimplePoleAt f z₀ := by
  obtain ⟨g, hg_an, _, hg_eq⟩ := (meromorphicOrderAt_eq_int_iff hf).mp hord
  obtain ⟨h_fn, hh_an, hf_decomp⟩ := simplePoleDecomp_of_eventuallyEq_zpow_neg_one hg_an hg_eq
  exact ⟨g z₀, h_fn, hh_an, hf_decomp⟩

/-! ### Residue bridge -/

/-- At a simple pole (Mathlib order `-1`), the project's `residue` equals `g(z_0)`, the
value of the analytic factor from Mathlib's meromorphic factorization.

This connects `lim_{r->0+} (2 pi i)^{-1} oint_{|z-z_0|=r} f(z) dz` to
Mathlib's factorization `f =ᶠ (z - z_0)^(-1) * g(z)`. -/
theorem residue_eq_leadingCoeff_of_order_neg_one {f : ℂ → ℂ} {z₀ : ℂ}
    (_hf : MeromorphicAt f z₀) (_hord : meromorphicOrderAt f z₀ = (-1 : ℤ))
    {g : ℂ → ℂ} (hg_an : AnalyticAt ℂ g z₀) (_hg_ne : g z₀ ≠ 0)
    (hg_eq : ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ (-1 : ℤ) • g z) :
    residue f z₀ = g z₀ := by
  obtain ⟨_, hh_an, hf_decomp⟩ := simplePoleDecomp_of_eventuallyEq_zpow_neg_one hg_an hg_eq
  exact residue_eq_of_simple_pole_decomp hh_an hf_decomp


/-! ### Analytic functions as trivial simple poles -/

/-- An analytic function has a simple pole decomposition with coefficient `0`. -/
theorem hasSimplePoleAt_of_analyticAt {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : AnalyticAt ℂ f z₀) : HasSimplePoleAt f z₀ := by
  refine ⟨0, f, hf, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z _
  simp [zero_div]

/-! ### Equivalence for order -1 -/


end
