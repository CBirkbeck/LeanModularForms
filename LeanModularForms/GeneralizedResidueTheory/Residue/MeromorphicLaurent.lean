/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheorem
import LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
-- Note: Does NOT import FlatnessTransfer to avoid circular dependencies.
-- The zpow FTC lemmas used here are reproved locally.
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Meromorphic Laurent Principal Parts and Zero-Residue Contour Vanishing

This file connects `MeromorphicAt` from Mathlib with Laurent principal parts and
proves that contour integrals of meromorphic functions with zero residues vanish
on closed curves in convex domains.

## Main Definitions

* `meromorphicPrincipalPart` — the finite-rank polar part of a meromorphic function

## Main Results

* `meromorphicPrincipalPart_differentiableOn` — principal part is differentiable away from the pole
* `meromorphicAt_sub_principalPart_eventually` — f minus its principal part is analytic at the pole
* `contourIntegral_zpow_eq_zero` — ∮ (z-s)^n dz = 0 for n ≤ -2 on closed curves
* `contourIntegral_principalPart_eq_zero_of_residue_zero` — ∮ pp = 0 when residue is zero
* `contourIntegral_eq_zero_of_meromorphic_residue_zero` — single-pole vanishing
* `contourIntegral_eq_zero_of_meromorphic_residue_zero_finset` — multi-pole vanishing

## Mathematical Overview

For a function `f` meromorphic at `s` with a pole of order `N`, Mathlib gives a
decomposition `f =ᶠ (z - s)^(-N) • g` near `s` with `g` analytic and `g(s) ≠ 0`.
The principal part is the sum of the first `N` terms of the Laurent series:

  pp(z) = Σ_{k=1}^{N} c_k / (z - s)^k

where `c_k = (1/k!) · iteratedDeriv k g s` (adjusted by the order).

When `Res(f, s) = 0`, the `(z-s)^{-1}` coefficient vanishes, and each `(z-s)^{-k}`
term for `k ≥ 2` integrates to zero on closed curves (by FTC). So `∮ pp = 0`.
The regular part `f - pp` is analytic at `s` and differentiable on `U \ {s}`, hence
differentiable on all of `U`; by Cauchy's theorem on convex sets, `∮ (f - pp) = 0`.
Combining gives `∮ f = 0`.

## References

* Hungerbühler-Wasem, arXiv:1808.00997v2, Theorem 3.3
* Mathlib `MeromorphicAt`, `meromorphicOrderAt`
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

attribute [local instance] Classical.propDecidable

noncomputable section

namespace GeneralizedResidueTheory

/-! ### Definition of the meromorphic principal part

For `f` meromorphic at `s`, the principal part extracts the finite Laurent tail.
If `meromorphicOrderAt f s = -N` (pole of order N), we use the Mathlib decomposition
`f =ᶠ (z - s)^(-N) • g` with `g` analytic and `g(s) ≠ 0`, then:

  pp(z) = Σ_{k=0}^{N-1} (g^(k)(s) / k!) · (z - s)^{k - N}

This equals `Σ_{j=1}^{N} c_j / (z-s)^j` where `c_j = g^{(N-j)}(s) / (N-j)!`.

If `f` is analytic at `s` (order ≥ 0) or not meromorphic, the principal part is 0. -/

/-- Helper: extract the pole order as a natural number from meromorphic data. -/
private noncomputable def poleOrderNat (f : ℂ → ℂ) (s : ℂ) : ℕ :=
  (-(meromorphicOrderAt f s).untop₀).toNat

/-- Helper: extract the analytic factor g from the meromorphic decomposition. -/
private noncomputable def meromorphicFactor (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (hne : meromorphicOrderAt f s ≠ ⊤) : ℂ → ℂ :=
  ((meromorphicOrderAt_ne_top_iff hf).mp hne).choose

/-- The meromorphic principal part of `f` at `s`.

If `f` has a pole of order `N` at `s` (i.e., `meromorphicOrderAt f s = -(N : ℤ)` with N > 0),
the principal part is a rational function that captures the singular behavior.
If `f` is analytic at `s` or not meromorphic, returns 0. -/
noncomputable def meromorphicPrincipalPart (f : ℂ → ℂ) (s : ℂ) : ℂ → ℂ :=
  if h : MeromorphicAt f s ∧ meromorphicOrderAt f s < 0 then
    fun z => (Finset.range (poleOrderNat f s)).sum fun k =>
      (iteratedDeriv k (meromorphicFactor f s h.1 h.2.ne_top) s /
        ↑(Nat.factorial k)) * (z - s) ^ ((k : ℤ) - (poleOrderNat f s : ℤ))
  else
    fun _ => 0

/-- When `f` is analytic at `s` (non-negative order), the principal part is zero. -/
theorem meromorphicPrincipalPart_eq_zero_of_analyticAt (f : ℂ → ℂ) (s : ℂ)
    (hf : AnalyticAt ℂ f s) :
    meromorphicPrincipalPart f s = fun _ => 0 := by
  unfold meromorphicPrincipalPart
  have h_ord : 0 ≤ meromorphicOrderAt f s := hf.meromorphicOrderAt_nonneg
  exact dif_neg (fun h => absurd h.2 (not_lt.mpr h_ord))

/-! ### Differentiability of the principal part -/

/-- Each term `c * (z - s)^n` with `n < 0` is differentiable away from `s`. -/
private theorem differentiableOn_zpow_sub_compl (s : ℂ) (n : ℤ) (c : ℂ) :
    DifferentiableOn ℂ (fun z => c * (z - s) ^ n) {s}ᶜ := by
  intro z hz
  have hne : z - s ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_const c).mul
    ((differentiableAt_id.sub (differentiableAt_const s)).zpow (Or.inl hne))

set_option maxHeartbeats 400000 in
/-- The principal part is differentiable on `{s}ᶜ`. -/
theorem meromorphicPrincipalPart_differentiableOn (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) :
    DifferentiableOn ℂ (meromorphicPrincipalPart f s) {s}ᶜ := by
  unfold meromorphicPrincipalPart
  by_cases h_neg : meromorphicOrderAt f s < 0
  · rw [dif_pos ⟨hf, h_neg⟩]
    apply DifferentiableOn.fun_sum
    intro k _
    exact differentiableOn_zpow_sub_compl s _ _
  · rw [dif_neg (not_and_of_not_right _ h_neg)]
    exact differentiableOn_const 0

/-- When the meromorphic order is negative, `untop₀` is also negative. -/
private theorem untop₀_neg_of_order_neg {f : ℂ → ℂ} {s : ℂ}
    (h_neg : meromorphicOrderAt f s < 0) :
    (meromorphicOrderAt f s).untop₀ < 0 := by
  cases h : meromorphicOrderAt f s with
  | top => exact absurd h h_neg.ne_top
  | coe v => simp [WithTop.untop₀]; rw [h] at h_neg; exact_mod_cast h_neg

/-- When the meromorphic order is negative, the pole order is positive. -/
private theorem poleOrderNat_pos {f : ℂ → ℂ} {s : ℂ}
    (h_neg : meromorphicOrderAt f s < 0) :
    0 < poleOrderNat f s := by
  show 0 < (-(meromorphicOrderAt f s).untop₀).toNat
  have := untop₀_neg_of_order_neg h_neg
  omega

/-- The `untop₀` of the meromorphic order equals `-(poleOrderNat f s)`. -/
private theorem untop₀_eq_neg_poleOrderNat {f : ℂ → ℂ} {s : ℂ}
    (h_neg : meromorphicOrderAt f s < 0) :
    (meromorphicOrderAt f s).untop₀ = -(poleOrderNat f s : ℤ) := by
  show (meromorphicOrderAt f s).untop₀ = -↑((-((meromorphicOrderAt f s).untop₀)).toNat)
  have := untop₀_neg_of_order_neg h_neg
  omega

/-- Taylor remainder factorization: if `G` is analytic at `s` and `P` is its degree-`N`
Taylor polynomial, then `G - P = (z - s)^N * H` near `s` for some analytic `H`. -/
private theorem taylor_remainder_factored {s : ℂ} {N : ℕ} {G : ℂ → ℂ}
    (hG_an : AnalyticAt ℂ G s)
    (P : ℂ → ℂ)
    (hP_an : AnalyticAt ℂ P s)
    (hP_eq : P = fun z => ∑ k ∈ Finset.range N,
      (iteratedDeriv k G s / ↑(k.factorial)) * (z - s) ^ (k : ℕ)) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H s ∧
      ∀ᶠ z in 𝓝 s, G z - P z = (z - s) ^ N • H z := by
  exact (natCast_le_analyticOrderAt (hG_an.sub hP_an)).mp (by
    rw [natCast_le_analyticOrderAt (hG_an.sub hP_an)]
    have hG_fps := hG_an.hasFPowerSeriesAt
    set pG := FormalMultilinearSeries.ofScalars ℂ
      (fun n => iteratedDeriv n G s / ↑(n.factorial)) with hpG_def
    have hH_fps := HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope N hG_fps
    set H := (Function.swap dslope s)^[N] G
    refine ⟨H, hH_fps.analyticAt, ?_⟩
    have hG_sum := hasFPowerSeriesAt_iff'.mp hG_fps
    have hH_sum := hasFPowerSeriesAt_iff'.mp hH_fps
    filter_upwards [hG_sum, hH_sum] with z hG_z hH_z
    simp only [FormalMultilinearSeries.coeff_iterate_fslope, smul_eq_mul] at hG_z hH_z
    show G z - P z = (z - s) ^ N * H z
    set c := fun k => (z - s) ^ k * pG.coeff k with hc_def
    have hG_tail : HasSum (fun j => c (j + N))
        (G z - ∑ i ∈ Finset.range N, c i) :=
      (hasSum_nat_add_iff' N).mpr hG_z
    have hP_eq' : P z = ∑ i ∈ Finset.range N, c i := by
      rw [hP_eq]
      simp only [c, pG, FormalMultilinearSeries.coeff_ofScalars]
      congr 1; ext k; ring
    rw [hP_eq', ← hG_tail.tsum_eq, ← hH_z.tsum_eq, ← tsum_mul_left]
    congr 1; ext j
    simp only [c]; ring)

/-- The principal part equals `(z-s)^{-N} * P(z)` near `s` (away from `s`),
where `P` is the Taylor polynomial of the meromorphic factor. -/
private theorem principalPart_eq_zpow_mul_taylor (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (h_neg : meromorphicOrderAt f s < 0) :
    let N := poleOrderNat f s
    let G := meromorphicFactor f s hf h_neg.ne_top
    let P := fun z => ∑ k ∈ Finset.range N,
      (iteratedDeriv k G s / ↑(k.factorial)) * (z - s) ^ (k : ℕ)
    ∀ᶠ z in 𝓝[≠] s, meromorphicPrincipalPart f s z =
      (z - s) ^ (-(N : ℤ)) * P z := by
  intro N G P
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hne : z - s ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
  show meromorphicPrincipalPart f s z = _
  unfold meromorphicPrincipalPart; rw [dif_pos ⟨hf, h_neg⟩]
  simp only [P, N, G]; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro k _
  rw [show (z - s) ^ ((k : ℤ) - (poleOrderNat f s : ℤ)) =
    (z - s) ^ (-(poleOrderNat f s : ℤ)) * (z - s) ^ (k : ℕ) from by
    rw [← zpow_natCast (z - s) k, ← zpow_add₀ hne]; congr 1; omega]
  ring

/-! ### The regular part is analytic

f minus its principal part extends analytically to the pole. -/

/-- If `f` is meromorphic at `s`, then `f - meromorphicPrincipalPart f s` agrees
with an analytic function near `s` (away from `s`). Since the principal part
captures exactly the singular behavior, the difference extends analytically. -/
theorem meromorphicAt_sub_principalPart_eventually (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g z := by
  by_cases h_neg : meromorphicOrderAt f s < 0
  · set N := poleOrderNat f s
    set G := meromorphicFactor f s hf h_neg.ne_top
    have hG_spec := ((meromorphicOrderAt_ne_top_iff hf).mp h_neg.ne_top).choose_spec
    have hG_an : AnalyticAt ℂ G s := hG_spec.1
    have hf_ev : f =ᶠ[𝓝[≠] s] fun z =>
        (z - s) ^ (meromorphicOrderAt f s).untop₀ • G z := hG_spec.2.2
    have h_ord_eq := untop₀_eq_neg_poleOrderNat h_neg
    set P : ℂ → ℂ := fun z => ∑ k ∈ Finset.range N,
      (iteratedDeriv k G s / ↑(k.factorial)) * (z - s) ^ (k : ℕ)
    have hP_an : AnalyticAt ℂ P s := by
      apply Finset.analyticAt_fun_sum; intro k _
      exact analyticAt_const.mul ((analyticAt_id ℂ s).sub analyticAt_const |>.pow _)
    have h_pp_eq := principalPart_eq_zpow_mul_taylor f s hf h_neg
    obtain ⟨H, hH_an, hH_eq⟩ := taylor_remainder_factored hG_an P hP_an rfl
    refine ⟨H, hH_an, ?_⟩
    filter_upwards [hf_ev, h_pp_eq, hH_eq.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hf_z hpp_z hH_z hz_ne
    have hne : z - s ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz_ne)
    simp only [smul_eq_mul] at hf_z hH_z ⊢
    rw [hf_z, hpp_z]; simp only [h_ord_eq]
    rw [← mul_sub, hH_z, ← mul_assoc, ← zpow_natCast (z - s) N, ← zpow_add₀ hne,
      neg_add_cancel, zpow_zero, one_mul]
  · have h_pp : meromorphicPrincipalPart f s = fun _ => 0 := by
      unfold meromorphicPrincipalPart
      rw [dif_neg (not_and_of_not_right _ h_neg)]
    push_neg at h_neg
    refine ⟨toMeromorphicNFAt f s, ?_, ?_⟩
    · exact (meromorphicNFAt_toMeromorphicNFAt.meromorphicOrderAt_nonneg_iff_analyticAt).mp
        (by rwa [← meromorphicOrderAt_congr hf.eq_nhdsNE_toMeromorphicNFAt])
    · filter_upwards [hf.eq_nhdsNE_toMeromorphicNFAt] with z hz
      simp [h_pp, hz]

/-! ### Local reproductions of zpow FTC lemmas

These lemmas were previously imported from FlatnessTransfer.lean. They are
reproved here locally to avoid a circular dependency. -/

/-- ContinuousOn for `t ↦ (γ(t) - s)^n` on a set where `γ(t) ≠ s`. -/
private theorem continuousOn_zpow_comp_sub'
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {A : Set ℝ}
    (hγ : ContinuousOn γ A)
    (hne : ∀ t ∈ A, γ t ≠ s) :
    ContinuousOn (fun t => (γ t - s) ^ n) A := by
  apply ContinuousOn.zpow₀ (hγ.sub continuousOn_const)
  intro t ht; exact Or.inl (sub_ne_zero.mpr (hne t ht))

/-- HasDerivAt for `(γ(t) - s)^n` when `γ` is differentiable and `γ(t) ≠ s`. -/
private theorem hasDerivAt_zpow_comp_sub'
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} {t : ℝ} {L : ℂ}
    (hγ : HasDerivAt γ L t) (hne : γ t ≠ s) :
    HasDerivAt (fun t => (γ t - s) ^ n) (↑n * (γ t - s) ^ (n - 1) * L) t := by
  have h := (hasDerivAt_zpow n (γ t - s) (Or.inl (sub_ne_zero.mpr hne))).comp t (hγ.sub_const s)
  exact h.congr_deriv (by simp)

/-- FTC for the integral of `(γ(t) - s)^n · γ'(t)` on `[a, b]` when `γ(t) ≠ s`
on `[a, b]` and `n ≠ -1`. The primitive is `(γ(t) - s)^{n+1} / (n+1)`. -/
private theorem integral_zpow_comp_sub_mul_deriv'
    {γ : ℝ → ℂ} {s : ℂ} {n : ℤ} (hn : n ≠ -1)
    {a b : ℝ} (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_ne : ∀ t ∈ Icc a b, γ t ≠ s)
    (E : Set ℝ) (hE : E.Countable) (_hE_sub : E ∩ Ioo a b ⊆ Ioo a b)
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ E → DifferentiableAt ℝ γ t)
    (h_int : IntervalIntegrable
      (fun t => (γ t - s) ^ n * (deriv γ t : ℂ)) MeasureTheory.volume a b) :
    ∫ t in a..b, (γ t - s) ^ n * (deriv γ t : ℂ) =
      ((γ b - s) ^ (n + 1) - (γ a - s) ^ (n + 1)) / (↑(n + 1) : ℂ) := by
  have hn1 : (n : ℤ) + 1 ≠ 0 := by omega
  have hn1_cast : (↑(n + 1) : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn1
  set F : ℝ → ℂ := fun t => (γ t - s) ^ (n + 1) / (↑(n + 1) : ℂ) with hF_def
  set f : ℝ → ℂ := fun t => (γ t - s) ^ n * (deriv γ t : ℂ) with hf_def
  have hF_cont : ContinuousOn F (Icc a b) :=
    (continuousOn_zpow_comp_sub' hγ_cont hγ_ne (n := n + 1)).div_const _
  have hE_count : (E ∩ Ioo a b).Countable := hE.mono Set.inter_subset_left
  have hF_deriv : ∀ t ∈ Ioo a b \ (E ∩ Ioo a b),
      HasDerivAt F (f t) t := by
    intro t ⟨ht, ht_not⟩
    have ht_not_E : t ∉ E := fun hE_mem => ht_not ⟨hE_mem, ht⟩
    have hγ_da := (hγ_diff t ht ht_not_E).hasDerivAt
    have hne : γ t ≠ s := hγ_ne t (Ioo_subset_Icc_self ht)
    have h_zpow := hasDerivAt_zpow_comp_sub' (n := n + 1) hγ_da hne
    have h_div := h_zpow.div_const (↑(n + 1) : ℂ)
    show HasDerivAt F ((γ t - s) ^ n * ↑(deriv γ t)) t
    have : (↑(n + 1) : ℂ) * (γ t - s) ^ (n + 1 - 1) * ↑(deriv γ t) / (↑(n + 1) : ℂ)
        = (γ t - s) ^ n * ↑(deriv γ t) := by
      rw [show (n + 1 : ℤ) - 1 = n from by ring]
      rw [mul_assoc, mul_div_cancel_left₀ _ hn1_cast]
    rwa [this] at h_div
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    F f hab hE_count hF_cont hF_deriv h_int
  rw [h_ftc]
  simp only [F]
  rw [← sub_div]

/-! ### Contour integral of zpow on closed curves

For n ≤ -2, the function z ↦ (z - s)^n has a primitive (z - s)^{n+1}/(n+1),
which is single-valued away from s. On a closed curve avoiding s, the boundary
terms cancel. -/

/-- For `n ≤ -2`, the contour integral `∮ (z - s)^n dz = 0` along any closed
piecewise C^1 immersion that avoids `s`. This follows from the fundamental
theorem of calculus: the primitive `(z-s)^{n+1}/(n+1)` is well-defined since
`n + 1 ≤ -1 ≠ -1` (i.e. `n + 1 ≠ 0`), and the boundary values cancel by closedness. -/
theorem contourIntegral_zpow_eq_zero (s : ℂ) (n : ℤ) (hn : n ≤ -2)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, (γ.toFun t - s) ^ n * deriv γ.toFun t = 0 := by
  -- Use the local FTC lemma: integral_zpow_comp_sub_mul_deriv'
  -- n ≠ -1 since n ≤ -2
  have hn_ne : n ≠ -1 := by omega
  -- Integrability of (γ(t) - s)^n * γ'(t) on the piecewise C^1 curve
  have h_int : IntervalIntegrable
      (fun t => (γ.toFun t - s) ^ n * (deriv γ.toFun t : ℂ)) volume γ.a γ.b := by
    -- (γ(t) - s)^n is continuous on [a,b] since γ avoids s
    have h_zpow_cont : ContinuousOn (fun t => (γ.toFun t - s) ^ n) (Icc γ.a γ.b) :=
      continuousOn_zpow_comp_sub' γ.continuous_toFun hγ_avoids
    -- γ' is piecewise continuous and bounded
    exact IntervalIntegrable.continuousOn_mul
      (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
        (piecewiseC1Immersion_deriv_bounded γ))
      (h_zpow_cont.mono (by rw [Set.uIcc_of_le (le_of_lt γ.hab)]))
  -- Apply FTC
  have h_ftc := integral_zpow_comp_sub_mul_deriv' hn_ne (le_of_lt γ.hab)
    γ.continuous_toFun hγ_avoids
    (↑γ.partition : Set ℝ) (γ.partition.finite_toSet.countable)
    (fun _ ⟨_, h⟩ => h)
    (fun t ht hn_part => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hn_part)
    h_int
  -- Now h_ftc says the integral = ((γ b - s)^{n+1} - (γ a - s)^{n+1}) / (n+1)
  rw [h_ftc]
  -- Since γ is closed, γ(b) = γ(a), so the numerator is 0
  have h_eq : γ.toFun γ.b = γ.toFun γ.a := hγ_closed.symm
  rw [h_eq, sub_self, zero_div]

/-- Variant: contour integral of `c * (z - s)^n` is zero for `n ≤ -2`. -/
theorem contourIntegral_const_mul_zpow_eq_zero (s : ℂ) (n : ℤ) (hn : n ≤ -2) (c : ℂ)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, c * (γ.toFun t - s) ^ n * deriv γ.toFun t = 0 := by
  have h_eq : ∀ t, c * (γ.toFun t - s) ^ n * deriv γ.toFun t =
      c * ((γ.toFun t - s) ^ n * deriv γ.toFun t) := fun t => by ring
  simp_rw [h_eq]
  rw [intervalIntegral.integral_const_mul]
  rw [contourIntegral_zpow_eq_zero s n hn γ hγ_closed hγ_avoids]
  simp

/-! ### Residue of the principal part

The residue of the principal part equals the (N-1)-th coefficient `c_{N-1}`.
This is computed directly via circle integrals: in the sum `Σ c_k (z-s)^{k-N}`,
only the k=N-1 term (exponent -1) contributes to the residue. -/

/-- Each term `c_k * (z-s)^{k-N}` integrates to `c_{N-1} * 2piI` when `k = N-1`
and to `0` otherwise. -/
private theorem circleIntegral_zpow_term (s : ℂ) (N : ℕ) (hN : 0 < N) (c : ℕ → ℂ)
    {r : ℝ} (hr_ne : r ≠ 0) :
    ∀ k, (∮ z in C(s, r), c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
      if k = N - 1 then c (N - 1) * (2 * ↑Real.pi * I) else 0 := by
  intro k
  by_cases hk : k = N - 1
  · subst hk; simp only [↓reduceIte]
    have h_exp : ((N - 1 : ℕ) : ℤ) - (N : ℤ) = -1 := by omega
    have h_fn_eq : (fun z => c (N - 1) * (z - s) ^ (((N - 1 : ℕ) : ℤ) - (N : ℤ))) =
        fun z => c (N - 1) * (z - s)⁻¹ := by ext z; rw [h_exp, zpow_neg_one]
    conv_lhs => rw [h_fn_eq]
    rw [circleIntegral.integral_const_mul, circleIntegral.integral_sub_center_inv s hr_ne]
  · simp only [hk, ↓reduceIte]
    conv_lhs => rw [show (fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
      fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ)) from rfl]
    rw [circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_zpow_of_ne (show (k : ℤ) - (N : ℤ) ≠ -1 by omega),
      mul_zero]

/-- The circle integral distributes over a finite sum of zpow terms. -/
private theorem circleIntegral_finset_sum_zpow (s : ℂ) (N : ℕ) (c : ℕ → ℂ)
    {r : ℝ} (hr_pos : 0 < r) :
    (∮ z in C(s, r), ∑ k ∈ Finset.range N, c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
    ∑ k ∈ Finset.range N,
      (∮ z in C(s, r), c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) := by
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have h_ci : ∀ k, CircleIntegrable (fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) s r := by
    intro k
    have h_zpow_ci : CircleIntegrable (fun z => (z - s) ^ ((k : ℤ) - (N : ℤ))) s r :=
      circleIntegrable_sub_zpow_iff.mpr (Or.inr (Or.inr (by
        intro hmem; rw [Metric.mem_sphere] at hmem
        simp [dist_self] at hmem; exact hr_ne (abs_eq_zero.mp hmem.symm))))
    exact h_zpow_ci.const_fun_smul
  have : ∀ S : Finset ℕ,
      (∮ z in C(s, r), ∑ k ∈ S, c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) =
      ∑ k ∈ S, (∮ z in C(s, r), c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) := by
    intro S; induction S using Finset.induction with
    | empty => simp [circleIntegral]
    | @insert a S' ha' ih =>
      simp_rw [Finset.sum_insert ha']
      have h_sum_ci : CircleIntegrable
          (fun z => ∑ k ∈ S', c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) s r := by
        have := CircleIntegrable.sum S'
          (f := fun k => fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ)))
          (fun k _ => h_ci k)
        rwa [show (∑ k ∈ S', (fun z => c k * (z - s) ^ ((k : ℤ) - (N : ℤ)))) =
          fun z => ∑ k ∈ S', c k * (z - s) ^ ((k : ℤ) - (N : ℤ)) from
          funext (fun z => Finset.sum_apply z S' _)] at this
      rw [circleIntegral.integral_add (h_ci a) h_sum_ci, ih]
  exact this _

/-- The residue of `Σ_{k<N} c_k * (z-s)^{k-N}` equals `c_{N-1}` (the coefficient
of `(z-s)^{-1}`). Proved directly by circle integral computation. -/
private theorem residueAt_zpow_sum (s : ℂ) (N : ℕ) (hN : 0 < N) (c : ℕ → ℂ) :
    residueAt (fun z => ∑ k ∈ Finset.range N, c k * (z - s) ^ ((k : ℤ) - (N : ℤ))) s =
    c (N - 1) := by
  unfold residueAt
  apply Filter.Tendsto.limUnder_eq
  apply tendsto_nhds_of_eventually_eq
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 from one_pos)] with r _ hr_pos
  simp only [Set.mem_Ioi] at hr_pos
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have h2piI_ne : (2 : ℂ) * ↑Real.pi * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  rw [circleIntegral_finset_sum_zpow s N c hr_pos]
  simp_rw [circleIntegral_zpow_term s N hN c hr_ne]
  rw [Finset.sum_ite_eq' (Finset.range N) (N - 1)]
  simp only [Finset.mem_range, Nat.sub_one_lt_of_le hN le_rfl, ↓reduceIte]
  rw [mul_comm (c (N - 1)) _, ← mul_assoc, inv_mul_cancel₀ h2piI_ne, one_mul]

/-! ### Principal part integral vanishing

When the residue is zero, the principal part integral vanishes on closed curves.
The principal part is a finite sum of terms `c_k * (z - s)^{k - N}` for k = 0..N-1.
The term with k = N-1 gives exponent -1 (the residue term), which vanishes by assumption.
All other terms have exponent ≤ -2, so they vanish by `contourIntegral_zpow_eq_zero`. -/

/-- The residue of `f` equals the residue of its principal part: `f - pp` is analytic
at `s`, and analytic functions have residue zero on circles. -/
private theorem residueAt_eq_residueAt_principalPart (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (h_neg : meromorphicOrderAt f s < 0) :
    let N := poleOrderNat f s
    let g := meromorphicFactor f s hf h_neg.ne_top
    let pp := fun z => ∑ k ∈ Finset.range N,
      iteratedDeriv k g s / ↑(k.factorial) * (z - s) ^ ((k : ℤ) - (N : ℤ))
    residueAt f s = residueAt pp s := by
  intro N g pp
  have h_pp_is : pp = meromorphicPrincipalPart f s := by
    ext z; unfold meromorphicPrincipalPart; rw [dif_pos ⟨hf, h_neg⟩]
  obtain ⟨g_an, hg_an_at, hg_eq⟩ := meromorphicAt_sub_principalPart_eventually f s hf
  have hg_eq' : ∀ᶠ z in 𝓝[≠] s, f z - pp z = g_an z := by rw [h_pp_is]; exact hg_eq
  obtain ⟨rg, hrg_pos, hg_ball⟩ := hg_an_at.exists_ball_analyticOnNhd
  rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hg_eq'
  obtain ⟨rf, hrf_pos, hrf_eq⟩ := hg_eq'
  have hr₀_pos : 0 < min rg rf := lt_min hrg_pos hrf_pos
  unfold residueAt
  show limUnder (𝓝[>] (0 : ℝ)) (fun r => (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(s, r), f z) =
    limUnder (𝓝[>] (0 : ℝ)) (fun r => (2 * ↑Real.pi * I)⁻¹ * ∮ z in C(s, r), pp z)
  unfold limUnder; congr 1; apply Filter.map_congr
  apply Filter.Eventually.mono (Ioo_mem_nhdsGT hr₀_pos)
  intro r ⟨hr_pos, hr_lt⟩
  have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
  have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  suffices h_circ : (∮ z in C(s, r), f z) = (∮ z in C(s, r), pp z) by simp only; rw [h_circ]
  have h_eq_on : Set.EqOn f (fun z => pp z + g_an z) (Metric.sphere s r) := by
    intro z hz
    have h_ne : z ≠ s := by intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    have h_mem : z ∈ Metric.ball s rf ∩ {s}ᶜ :=
      ⟨Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; exact hr_lt_rf),
       Set.mem_compl_singleton_iff.mpr h_ne⟩
    rw [show f z = pp z + (f z - pp z) from (add_sub_cancel _ _).symm, hrf_eq h_mem]
  have h_g_cont : ContinuousOn g_an (Metric.closedBall s r) :=
    hg_ball.continuousOn.mono (Metric.closedBall_subset_ball hr_lt_rg)
  have h_ci_g : CircleIntegrable g_an s r :=
    (h_g_cont.mono Metric.sphere_subset_closedBall).circleIntegrable hr_pos.le
  have hs_not : s ∉ Metric.sphere s r := by simp [hr_ne.symm]
  have h_ci_pp : CircleIntegrable pp s r := by
    apply (continuousOn_finset_sum _ (fun k _ => ?_)).circleIntegrable hr_pos.le
    exact ContinuousOn.mul continuousOn_const
      (ContinuousOn.zpow₀ (continuousOn_id.sub continuousOn_const)
        (fun z hz => Or.inl (sub_ne_zero.mpr (ne_of_mem_of_not_mem hz hs_not))))
  rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
    circleIntegral.integral_add h_ci_pp h_ci_g,
    circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
      Set.countable_empty h_g_cont
      (fun z ⟨hz, _⟩ => (hg_ball z (Metric.ball_subset_ball hr_lt_rg.le hz)).differentiableAt),
    add_zero]

/-- When `f` has a pole of order `N` at `s` with `Res(f,s) = 0`, the `(N-1)`-th
Taylor coefficient of the meromorphic factor is zero. -/
private theorem meromorphicFactor_coeff_zero_of_residue_zero (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (h_neg : meromorphicOrderAt f s < 0)
    (hres : residueAt f s = 0) :
    let N := poleOrderNat f s
    let g := meromorphicFactor f s hf h_neg.ne_top
    iteratedDeriv (N - 1) g s / ↑((N - 1).factorial) = 0 := by
  intro N g
  have hN_pos := poleOrderNat_pos h_neg
  have h_res_pp := residueAt_zpow_sum s N hN_pos (fun k => iteratedDeriv k g s / ↑(k.factorial))
  have h_res_eq := residueAt_eq_residueAt_principalPart f s hf h_neg
  rw [hres] at h_res_eq; rw [← h_res_pp]; exact h_res_eq.symm

/-- The contour integral of the principal part vanishes when the residue is zero. -/
theorem contourIntegral_principalPart_eq_zero_of_residue_zero
    (f : ℂ → ℂ) (s : ℂ) (hf : MeromorphicAt f s)
    (hres : residueAt f s = 0)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, meromorphicPrincipalPart f s (γ.toFun t) * deriv γ.toFun t = 0 := by
  by_cases h_neg : meromorphicOrderAt f s < 0
  · set N := poleOrderNat f s with hN_def
    set g := meromorphicFactor f s hf h_neg.ne_top with hg_def
    have h_pp_eq : meromorphicPrincipalPart f s = fun z =>
        (Finset.range N).sum fun k =>
          (iteratedDeriv k g s / ↑(Nat.factorial k)) * (z - s) ^ ((k : ℤ) - (N : ℤ)) := by
      unfold meromorphicPrincipalPart; rw [dif_pos ⟨hf, h_neg⟩]
    rw [h_pp_eq]; simp_rw [Finset.sum_mul]
    have h_coeff_zero := meromorphicFactor_coeff_zero_of_residue_zero f s hf h_neg hres
    have h_int : ∀ k ∈ Finset.range N, IntervalIntegrable
        (fun t => iteratedDeriv k g s / ↑(k.factorial) * (γ.toFun t - s) ^
          ((k : ℤ) - (N : ℤ)) * deriv γ.toFun t) MeasureTheory.volume γ.a γ.b := by
      intro k _
      exact IntervalIntegrable.continuousOn_mul
        (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
          (piecewiseC1Immersion_deriv_bounded γ))
        ((continuousOn_const.mul (continuousOn_zpow_comp_sub' γ.continuous_toFun hγ_avoids)).mono
          (by rw [Set.uIcc_of_le (le_of_lt γ.hab)]))
    rw [intervalIntegral.integral_finset_sum h_int]
    apply Finset.sum_eq_zero; intro k hk
    rw [Finset.mem_range] at hk
    by_cases hk_eq : k = N - 1
    · subst hk_eq; simp only [h_coeff_zero, zero_mul, intervalIntegral.integral_zero]
    · exact contourIntegral_const_mul_zpow_eq_zero s _ (by omega) _ γ hγ_closed hγ_avoids
  · have h_pp : meromorphicPrincipalPart f s = fun _ => 0 := by
      unfold meromorphicPrincipalPart; rw [dif_neg (not_and_of_not_right _ h_neg)]
    simp only [h_pp, zero_mul, intervalIntegral.integral_zero]

/-! ### Single-point vanishing theorem

For a meromorphic function with zero residue at the unique singularity in a convex
domain, the contour integral vanishes. -/

/-- Cauchy-FTC: if `h` is DifferentiableOn a convex open `U` and `γ` is a closed
piecewise C^1 curve in `U`, then `∮ h dz = 0`. -/
private theorem contourIntegral_eq_zero_of_differentiableOn_convex
    (h : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (hU_ne : U.Nonempty)
    (h_diff : DifferentiableOn ℂ h U)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (h_int : IntervalIntegrable (fun t => h (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) :
    ∫ t in γ.a..γ.b, h (γ.toFun t) * deriv γ.toFun t = 0 := by
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU hU_ne h_diff
  have h_Fγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) := by
    intro t ht
    exact ((hF (γ.toFun t) (hγ_in_U t ht)).continuousAt.continuousWithinAt.comp
      (γ.continuous_toFun t ht) (fun t' ht' => hγ_in_U t' ht'))
  have h_countable : (↑γ.partition ∩ Ioo γ.a γ.b : Set ℝ).Countable :=
    (γ.partition.finite_toSet.inter_of_left _).countable
  have h_deriv : ∀ t ∈ Ioo γ.a γ.b \ (↑γ.partition ∩ Ioo γ.a γ.b),
      HasDerivAt (F ∘ γ.toFun) (h (γ.toFun t) * deriv γ.toFun t) t := by
    intro t ⟨ht, hp⟩
    exact (hF (γ.toFun t) (hγ_in_U t (Ioo_subset_Icc_self ht))).comp_of_eq t
      ((γ.smooth_off_partition t (Ioo_subset_Icc_self ht) (fun hm => hp ⟨hm, ht⟩)).hasDerivAt) rfl
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (F ∘ γ.toFun) _ (le_of_lt γ.hab) h_countable h_Fγ_cont h_deriv h_int
  rw [h_ftc, Function.comp_apply, Function.comp_apply,
    (hγ_closed : γ.toFun γ.a = γ.toFun γ.b), sub_self]

/-- The corrected regular part `Function.update rp s (g_an s)` is DifferentiableOn `U`
when `rp = f - pp`, `g_an` is analytic at `s` and agrees with `rp` near `s`, and
`f` is differentiable on `U \ {s}`. -/
private theorem regularPart_update_differentiableOn
    (f : ℂ → ℂ) (s : ℂ) (hf : MeromorphicAt f s)
    (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s}))
    (g_an : ℂ → ℂ) (hg_an_at : AnalyticAt ℂ g_an s)
    (hg_eq : ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_an z) :
    let rp := fun z => f z - meromorphicPrincipalPart f s z
    let rp_nf := Function.update rp s (g_an s)
    DifferentiableOn ℂ rp_nf U := by
  intro rp rp_nf
  have h_rp_nf_an : AnalyticAt ℂ rp_nf s := by
    apply hg_an_at.congr
    rw [Filter.Eventually, mem_nhdsWithin] at hg_eq
    obtain ⟨V, hV_open, hs_V, hV_eq⟩ := hg_eq
    apply Filter.Eventually.mono (hV_open.mem_nhds hs_V)
    intro z hz
    by_cases h : z = s
    · rw [h]; exact (Function.update_self s (g_an s) rp).symm
    · rw [Function.update_of_ne h]; exact (hV_eq ⟨hz, h⟩).symm
  intro z hz
  by_cases h : z = s
  · subst h; exact h_rp_nf_an.differentiableAt.differentiableWithinAt
  · have h_f_diff : DifferentiableAt ℂ f z :=
      (hf_diff z ⟨hz, Set.mem_compl_singleton_iff.mpr h⟩).differentiableAt
        ((hU.sdiff isClosed_singleton).mem_nhds ⟨hz, Set.mem_compl_singleton_iff.mpr h⟩)
    have h_pp_diff : DifferentiableAt ℂ (meromorphicPrincipalPart f s) z :=
      (meromorphicPrincipalPart_differentiableOn f s hf z
        (Set.mem_compl_singleton_iff.mpr h)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr h))
    have h_ev : rp =ᶠ[𝓝 z] rp_nf := by
      apply Filter.Eventually.mono (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr h))
      intro w hw
      exact (Function.update_of_ne (Set.mem_compl_singleton_iff.mp hw) (g_an s) rp).symm
    exact (h_ev.differentiableAt_iff.mp (h_f_diff.sub h_pp_diff)).differentiableWithinAt

/-- The regular part `f - pp` integrates to zero on a closed curve when `f` is
meromorphic at `s` with zero residue and differentiable on `U \ {s}`. -/
private theorem regularPart_integral_zero
    (f : ℂ → ℂ) (s : ℂ) (hf : MeromorphicAt f s)
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s})) (hs_in_U : s ∈ U)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, (f (γ.toFun t) - meromorphicPrincipalPart f s (γ.toFun t)) *
      deriv γ.toFun t = 0 := by
  set rp := fun z => f z - meromorphicPrincipalPart f s z
  obtain ⟨g_an, hg_an_at, hg_eq⟩ := meromorphicAt_sub_principalPart_eventually f s hf
  set rp_nf := Function.update rp s (g_an s)
  have h_rp_nf_diff_U : DifferentiableOn ℂ rp_nf U :=
    regularPart_update_differentiableOn f s hf U hU hf_diff g_an hg_an_at hg_eq
  have h_int_nf := contour_mul_deriv_integrable rp_nf γ
    ((h_rp_nf_diff_U.continuousOn.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht)).mono
      (Set.image_subset_range _ _))
  have h_nf_zero := contourIntegral_eq_zero_of_differentiableOn_convex
    rp_nf U hU hU_convex ⟨s, hs_in_U⟩ h_rp_nf_diff_U γ hγ_closed hγ_in_U h_int_nf
  rw [show (∫ t in γ.a..γ.b, rp (γ.toFun t) * deriv γ.toFun t) =
    (∫ t in γ.a..γ.b, rp_nf (γ.toFun t) * deriv γ.toFun t) from by
    apply intervalIntegral.integral_congr_ae; apply ae_of_all; intro t ht
    rw [Set.uIoc_of_le (le_of_lt γ.hab)] at ht; congr 1
    exact (Function.update_of_ne (hγ_avoids t (Ioc_subset_Icc_self ht)) (g_an s) rp).symm]
  exact h_nf_zero

/-- If `f` is meromorphic at `s` with `Res(f, s) = 0`, and `f` is differentiable on
`U \ {s}` for a convex open `U` containing `s`, then `∮_γ f = 0` for any closed
curve in `U` avoiding `s`. -/
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero
    (f : ℂ → ℂ) (s : ℂ) (hf : MeromorphicAt f s)
    (hres : residueAt f s = 0)
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s}))
    (hs_in_U : s ∈ U)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  set pp := meromorphicPrincipalPart f s
  have h_pp_zero := contourIntegral_principalPart_eq_zero_of_residue_zero
    f s hf hres γ hγ_closed hγ_avoids
  have h_rp_zero := regularPart_integral_zero f s hf U hU hU_convex hf_diff hs_in_U
    γ hγ_closed hγ_in_U hγ_avoids
  have hpp_cont : ContinuousOn pp (γ.toFun '' Icc γ.a γ.b) :=
    (meromorphicPrincipalPart_differentiableOn f s hf).continuousOn.mono
      (fun z ⟨t, ht, htz⟩ => htz ▸ Set.mem_compl_singleton_iff.mpr (hγ_avoids t ht))
  have h_int_pp := contour_mul_deriv_integrable pp γ hpp_cont
  have h_int_rp := contour_mul_deriv_integrable (fun z => f z - pp z) γ
    (ContinuousOn.sub
      (hf_diff.continuousOn.mono (fun z ⟨t, ht, rfl⟩ =>
        ⟨hγ_in_U t ht, hγ_avoids t ht⟩)) hpp_cont)
  simp_rw [show ∀ t, f (γ.toFun t) * deriv γ.toFun t =
    (f (γ.toFun t) - pp (γ.toFun t)) * deriv γ.toFun t +
    pp (γ.toFun t) * deriv γ.toFun t from fun t => by ring]
  rw [intervalIntegral.integral_add h_int_rp h_int_pp, h_rp_zero, h_pp_zero, add_zero]

/-! ### Multi-point vanishing theorem

The main consumer theorem: for finitely many meromorphic singularities, all with
zero residue, the contour integral vanishes. -/

/-- Multi-point version: if `f` is meromorphic at each `s ∈ S` with `Res(f, s) = 0`,
`f` is differentiable on `U \ S`, and `U` is convex open, then `∮_γ f = 0` for any
closed curve in `U` avoiding all of `S`.

**Proof strategy**: Subtract all principal parts at once. The remainder
`r(z) = f(z) - Σ_{s ∈ S} pp_s(z)` is analytic at each `s ∈ S` (by
`meromorphicAt_sub_principalPart_eventually` plus the fact that each `pp_{s'}` with `s' ≠ s`
is already analytic at `s`). So `r` is differentiable on all of `U`. By Cauchy,
`∮ r = 0`. By linearity, `∮ f = Σ ∮ pp_s = 0` (each vanishes by zero residue). -/
/-- The corrected remainder `r_nf` at a point `z ∈ S` agrees with
`g_corr z - Σ_{s' ∈ S.erase z} pp_{s'}` in a neighborhood of `z`. -/
private theorem corrected_remainder_eventuallyEq_at_singularity
    (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (g_corr : ∀ s ∈ S, ℂ → ℂ)
    (hg_corr_eq : ∀ s (hs : s ∈ S),
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_corr s hs z)
    (r_nf : ℂ → ℂ)
    (hr_nf_def : r_nf = fun z => if hz : z ∈ S then
        g_corr z hz z - ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' z
      else f z - ∑ s ∈ S, meromorphicPrincipalPart f s z)
    {z : ℂ} (hz_S : z ∈ S) :
    (fun w => g_corr z hz_S w -
      ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' w) =ᶠ[𝓝 z] r_nf := by
  have h_compl_open : IsOpen (↑(S.erase z) : Set ℂ)ᶜ :=
    (S.erase z).finite_toSet.isClosed.isOpen_compl
  have hz_in_compl : z ∈ (↑(S.erase z) : Set ℂ)ᶜ :=
    Set.mem_compl (fun h => (Finset.notMem_erase z S) (Finset.mem_coe.mp h))
  have hg_corr_eq_z := hg_corr_eq z hz_S
  rw [Filter.Eventually, mem_nhdsWithin] at hg_corr_eq_z
  obtain ⟨V, hV_open, hz_V, hV_eq⟩ := hg_corr_eq_z
  apply Filter.Eventually.mono
    ((hV_open.inter h_compl_open).mem_nhds ⟨hz_V, hz_in_compl⟩)
  intro w ⟨hw_V, hw_compl⟩
  rw [hr_nf_def]
  by_cases hw_S : w ∈ S
  · have hw_eq : w = z := by
      by_contra hne; exact hw_compl (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, hw_S⟩))
    rw [hw_eq]; simp [hz_S]
  · have hw_ne_z : w ≠ z := fun heq => hw_S (heq ▸ hz_S)
    have h_fw := hV_eq ⟨hw_V, hw_ne_z⟩
    simp only [hw_S, dite_false]
    rw [show (∑ s ∈ S, meromorphicPrincipalPart f s w) =
        meromorphicPrincipalPart f z w +
        ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' w from
      (Finset.add_sum_erase S _ hz_S).symm, ← h_fw]; ring

/-- At a singularity `z ∈ S`, the corrected remainder is DifferentiableWithinAt `U`. -/
private theorem corrected_remainder_differentiableWithinAt_singularity
    (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (g_corr : ∀ s ∈ S, ℂ → ℂ)
    (hg_corr_an : ∀ s (hs : s ∈ S), AnalyticAt ℂ (g_corr s hs) s)
    (hg_corr_eq : ∀ s (hs : s ∈ S),
      ∀ᶠ z in 𝓝[≠] s, f z - meromorphicPrincipalPart f s z = g_corr s hs z)
    (r_nf : ℂ → ℂ)
    (hr_nf_def : r_nf = fun z => if hz : z ∈ S then
        g_corr z hz z - ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' z
      else f z - ∑ s ∈ S, meromorphicPrincipalPart f s z)
    {z : ℂ} (hz_S : z ∈ S) (U : Set ℂ) (_ : z ∈ U) :
    DifferentiableWithinAt ℂ r_nf U z := by
  have h_other_pp_diff : DifferentiableAt ℂ
      (fun w => ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' w) z := by
    have h_each : ∀ s' ∈ S.erase z, DifferentiableAt ℂ (meromorphicPrincipalPart f s') z := by
      intro s' hs'
      have hne : z ≠ s' := (Finset.ne_of_mem_erase hs').symm
      exact (meromorphicPrincipalPart_differentiableOn f s'
        (hf_mero s' (Finset.mem_of_mem_erase hs')) z
        (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
    have h_sum := DifferentiableAt.sum h_each
    rwa [show (fun w => ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' w) =
        (∑ s' ∈ S.erase z, meromorphicPrincipalPart f s') from
      funext (fun w => (Finset.sum_apply w _ _).symm)]
  have h_corr_diff : DifferentiableAt ℂ
      (fun w => g_corr z hz_S w - ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' w) z :=
    (hg_corr_an z hz_S).differentiableAt.sub h_other_pp_diff
  exact ((corrected_remainder_eventuallyEq_at_singularity S f hf_mero g_corr hg_corr_eq
    r_nf hr_nf_def hz_S).differentiableAt_iff.mp h_corr_diff).differentiableWithinAt

/-- Away from all singularities, the corrected remainder is DifferentiableWithinAt `U`. -/
private theorem corrected_remainder_differentiableWithinAt_regular
    (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (r_nf : ℂ → ℂ)
    (hr_nf_def : r_nf = fun z => if hz : z ∈ S then _
      else f z - ∑ s ∈ S, meromorphicPrincipalPart f s z)
    {z : ℂ} (hz_S : z ∉ S) (hz_U : z ∈ U) :
    DifferentiableWithinAt ℂ r_nf U z := by
  have hz_punct : z ∈ U \ ↑S := ⟨hz_U, fun h => hz_S (Finset.mem_coe.mp h)⟩
  have hU_S_open : IsOpen (U \ ↑S) := hU.sdiff (S.finite_toSet.isClosed)
  have hf_da : DifferentiableAt ℂ f z :=
    (hf_diff z hz_punct).differentiableAt (hU_S_open.mem_nhds hz_punct)
  have htp_da : DifferentiableAt ℂ (fun w => ∑ s ∈ S, meromorphicPrincipalPart f s w) z := by
    apply (DifferentiableAt.sum (fun s hs => ?_)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun w => (Finset.sum_apply w S _).symm))
    have hne : z ≠ s := fun heq => hz_S (heq ▸ hs)
    exact (meromorphicPrincipalPart_differentiableOn f s (hf_mero s hs) z
      (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
  have h_r_diff : DifferentiableAt ℂ (fun z => f z - ∑ s ∈ S, meromorphicPrincipalPart f s z) z :=
    hf_da.sub htp_da
  have h_ev : (fun w => f w - ∑ s ∈ S, meromorphicPrincipalPart f s w) =ᶠ[𝓝 z] r_nf := by
    apply Filter.Eventually.mono (hU_S_open.mem_nhds hz_punct)
    intro w ⟨_, hw_not_S⟩
    rw [hr_nf_def]; simp only [show ¬(w ∈ S) from fun h => hw_not_S (Finset.mem_coe.mpr h),
      dite_false]
  exact (h_ev.differentiableAt_iff.mp h_r_diff).differentiableWithinAt

/-- Continuity of the total principal part along the curve. -/
private theorem total_pp_continuousOn_image
    (S : Finset ℂ) (f : ℂ → ℂ) (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (γ : PiecewiseC1Immersion) (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ContinuousOn (fun z => ∑ s ∈ S, meromorphicPrincipalPart f s z)
      (γ.toFun '' Icc γ.a γ.b) := by
  apply continuousOn_finset_sum; intro s hs
  apply (meromorphicPrincipalPart_differentiableOn f s (hf_mero s hs)).continuousOn.mono
  intro z hz; obtain ⟨t, ht, rfl⟩ := hz
  exact Set.mem_compl_singleton_iff.mpr (hγ_avoids s hs t ht)

/-- Integrability of `h(gamma(t)) * gamma'(t)` when `h` is continuous on the curve's image. -/
private theorem contour_mul_deriv_integrable
    (h : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (h_cont : ContinuousOn h (γ.toFun '' Icc γ.a γ.b)) :
    IntervalIntegrable (fun t => h (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b :=
  IntervalIntegrable.continuousOn_mul
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve
      (piecewiseC1Immersion_deriv_bounded γ))
    ((h_cont.comp γ.continuous_toFun (Set.mapsTo_image _ _)).mono
      (by rw [Set.uIcc_of_le (le_of_lt γ.hab)]))

/-- The remainder `r = f - total_pp` is integral-zero on a closed curve. -/
private theorem remainder_integral_zero_finset
    (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (hU_ne : U.Nonempty)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (r_nf : ℂ → ℂ) (h_r_nf_diff_U : DifferentiableOn ℂ r_nf U)
    (hr_eq_rnf : ∀ t ∈ Ioc γ.a γ.b, (f (γ.toFun t) - ∑ s ∈ S, meromorphicPrincipalPart f s (γ.toFun t)) =
      r_nf (γ.toFun t)) :
    ∫ t in γ.a..γ.b,
      (f (γ.toFun t) - ∑ s ∈ S, meromorphicPrincipalPart f s (γ.toFun t)) *
        deriv γ.toFun t = 0 := by
  have h_int_nf : IntervalIntegrable
      (fun t => r_nf (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b :=
    contour_mul_deriv_integrable r_nf γ
      ((h_r_nf_diff_U.continuousOn.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht)).mono
        (Set.image_subset_range _ _))
  have h_nf_zero := contourIntegral_eq_zero_of_differentiableOn_convex
    r_nf U hU hU_convex hU_ne h_r_nf_diff_U γ hγ_closed hγ_in_U h_int_nf
  rw [show (∫ t in γ.a..γ.b, (f (γ.toFun t) -
      ∑ s ∈ S, meromorphicPrincipalPart f s (γ.toFun t)) * deriv γ.toFun t) =
    (∫ t in γ.a..γ.b, r_nf (γ.toFun t) * deriv γ.toFun t) from by
    apply intervalIntegral.integral_congr_ae; apply ae_of_all; intro t ht
    rw [Set.uIoc_of_le (le_of_lt γ.hab)] at ht
    congr 1; exact hr_eq_rnf t ht]
  exact h_nf_zero

theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_finset
    (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (hres : ∀ s ∈ S, residueAt f s = 0)
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (hS_in_U : ∀ s ∈ S, s ∈ U)
    (γ : PiecewiseC1Immersion) (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  have h_pp_zero : ∀ s ∈ S,
      ∫ t in γ.a..γ.b, meromorphicPrincipalPart f s (γ.toFun t) * deriv γ.toFun t = 0 :=
    fun s hs => contourIntegral_principalPart_eq_zero_of_residue_zero f s (hf_mero s hs)
      (hres s hs) γ hγ_closed (hγ_avoids s hs)
  choose g_corr hg_corr_an hg_corr_eq using
    fun s (hs : s ∈ S) => meromorphicAt_sub_principalPart_eventually f s (hf_mero s hs)
  set r_nf := fun z => if hz : z ∈ S then
      g_corr z hz z - ∑ s' ∈ S.erase z, meromorphicPrincipalPart f s' z
    else f z - ∑ s ∈ S, meromorphicPrincipalPart f s z
  have h_r_nf_diff_U : DifferentiableOn ℂ r_nf U := by
    intro z hz; by_cases hz_S : z ∈ S
    · exact corrected_remainder_differentiableWithinAt_singularity
        S f hf_mero g_corr hg_corr_an hg_corr_eq r_nf rfl hz_S U hz
    · exact corrected_remainder_differentiableWithinAt_regular
        S f hf_mero U hU hf_diff r_nf rfl hz_S hz
  have hU_ne : U.Nonempty := by
    rcases S.eq_empty_or_nonempty with rfl | ⟨s, hs⟩
    · exact ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr (le_of_lt γ.hab))⟩
    · exact ⟨s, hS_in_U s hs⟩
  have htp_cont := total_pp_continuousOn_image S f hf_mero γ hγ_avoids
  have h_r_zero := remainder_integral_zero_finset S f hf_mero U hU hU_convex hU_ne hf_diff
    γ hγ_closed hγ_in_U hγ_avoids r_nf h_r_nf_diff_U (fun t ht => by
      simp only [show ¬(γ.toFun t ∈ S) from
        fun hmem => hγ_avoids _ hmem t (Ioc_subset_Icc_self ht) rfl, dite_false])
  have h_int_r := contour_mul_deriv_integrable
    (fun z => f z - ∑ s ∈ S, meromorphicPrincipalPart f s z) γ
    ((ContinuousOn.sub
      (hf_diff.continuousOn.mono (fun z ⟨t, ht, rfl⟩ =>
        ⟨hγ_in_U t ht, fun hmem => hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩))
      htp_cont))
  have h_int_each_pp : ∀ s ∈ S, IntervalIntegrable
      (fun t => meromorphicPrincipalPart f s (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b :=
    fun s hs => contour_mul_deriv_integrable _ γ
      ((meromorphicPrincipalPart_differentiableOn f s (hf_mero s hs)).continuousOn.mono
        (fun z ⟨t, ht, rfl⟩ => Set.mem_compl_singleton_iff.mpr (hγ_avoids s hs t ht)))
  have h_int_tp := contour_mul_deriv_integrable
    (fun z => ∑ s ∈ S, meromorphicPrincipalPart f s z) γ htp_cont
  simp_rw [show ∀ t, f (γ.toFun t) * deriv γ.toFun t =
    (f (γ.toFun t) - ∑ s ∈ S, meromorphicPrincipalPart f s (γ.toFun t)) * deriv γ.toFun t +
    (∑ s ∈ S, meromorphicPrincipalPart f s (γ.toFun t)) * deriv γ.toFun t from fun t => by ring]
  rw [intervalIntegral.integral_add h_int_r h_int_tp, h_r_zero]
  simp_rw [show ∀ t, (∑ s ∈ S, meromorphicPrincipalPart f s (γ.toFun t)) * deriv γ.toFun t =
    ∑ s ∈ S, (meromorphicPrincipalPart f s (γ.toFun t) * deriv γ.toFun t) from
    fun t => Finset.sum_mul _ _ _]
  rw [intervalIntegral.integral_finset_sum h_int_each_pp, Finset.sum_eq_zero h_pp_zero, zero_add]

end GeneralizedResidueTheory

end
