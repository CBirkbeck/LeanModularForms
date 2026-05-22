/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.MeromorphicBridge

/-!
# Principal Parts for Simple Poles

This file defines the principal part sum for a finite collection of simple poles and
proves that subtracting it produces an analytic function. This is the key ingredient
for the generalized residue theorem: given a meromorphic function with finitely many
simple poles, one can subtract off all the principal parts to obtain a globally
holomorphic remainder.

## Main definitions

* `poleOrderAt f z₀` — the pole order at `z₀` as a natural number (`0` for analytic points).
* `principalPartSum S c` — the rational function `∑ s ∈ S, c s / (z - s)` for a finite set
  of poles `S` with coefficients `c`.

## Main results

* `principalPartSum_differentiableOn` — `principalPartSum S c` is differentiable on `(↑S)ᶜ`.
* `sub_principalPartSum_analyticAt` — for a function with simple poles at every point of `S`
  whose coefficients match, `f - principalPartSum S c` is analytic at each `s ∈ S`.
* `residue_principalPartSum` — the residue of the principal part sum at `s ∈ S` is `c s`.
* `principalPartSum_meromorphicAt` — the principal part sum is meromorphic everywhere.

## Design note

We focus on simple poles (order 1) rather than higher-order poles. This covers the main
use case for the generalized residue theorem, where simple pole decompositions suffice.
The general case (arbitrary finite-order poles) can be built on top by iterating
this construction with higher-order terms.
-/

open Complex Set Filter Topology Metric

noncomputable section

open scoped Classical

/-- The pole order of `f` at `z₀` as a natural number.

If `f` is meromorphic at `z₀` with `meromorphicOrderAt f z₀ = -n` for some `n > 0`,
returns `n`. Returns `0` if `f` is analytic at `z₀`, not meromorphic, or has a zero. -/
noncomputable def poleOrderAt (f : ℂ → ℂ) (z₀ : ℂ) : ℕ :=
  if _h : MeromorphicAt f z₀ then
    (-(meromorphicOrderAt f z₀).untop₀).toNat
  else 0

theorem poleOrderAt_eq_one_of_order_neg_one {f : ℂ → ℂ} {z₀ : ℂ}
    (hf : MeromorphicAt f z₀) (hord : meromorphicOrderAt f z₀ = (-1 : ℤ)) :
    poleOrderAt f z₀ = 1 := by
  rw [poleOrderAt, dif_pos hf, hord]; rfl

theorem poleOrderAt_eq_one_of_hasSimplePoleAt {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) (hc : h.coeff ≠ 0) :
    poleOrderAt f z₀ = 1 :=
  poleOrderAt_eq_one_of_order_neg_one h.meromorphicAt
    (meromorphicOrderAt_eq_neg_one_of_hasSimplePoleAt h hc)

/-- Principal part sum for simple poles: `∑ s ∈ S, c(s) / (z - s)`.

Given a finite set `S` of pole locations and a coefficient function `c : ℂ → ℂ`,
this is the rational function that captures the singular part of a meromorphic function
with simple poles at the points of `S`. -/
noncomputable def principalPartSum (S : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ s ∈ S, c s / (z - s)

/-- A single term `c / (z - s)` is differentiable at any `z ≠ s`. -/
theorem differentiableAt_div_sub {s : ℂ} {c : ℂ} {z : ℂ} (hz : z ≠ s) :
    DifferentiableAt ℂ (fun w => c / (w - s)) z :=
  differentiableAt_const c |>.div (differentiableAt_id.sub (differentiableAt_const s))
    (sub_ne_zero.mpr hz)

/-- A single term `c / (z - s)` is differentiable on `{s}ᶜ`. -/
theorem differentiableOn_div_sub (s : ℂ) (c : ℂ) :
    DifferentiableOn ℂ (fun z => c / (z - s)) {s}ᶜ :=
  fun _z hz => (differentiableAt_div_sub (mem_compl_singleton_iff.mp hz)).differentiableWithinAt

/-- The principal part sum `∑ s ∈ S, c(s) / (z - s)` is differentiable on `(↑S)ᶜ`. -/
theorem principalPartSum_differentiableOn (S : Finset ℂ) (c : ℂ → ℂ) :
    DifferentiableOn ℂ (principalPartSum S c) (↑S : Set ℂ)ᶜ := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.fun_sum
  intro s hs
  exact differentiableAt_div_sub (fun heq => hz (Finset.mem_coe.mpr (heq ▸ hs)))

/-- If `f` has a simple pole at `z₀` with coefficient `c`, then `f(z) - c/(z - z₀)` extends
analytically to `z₀`.

This is the fundamental fact: the principal part captures exactly the singular behavior,
so subtracting it leaves an analytic function. -/
theorem sub_simplePole_analyticAt {f : ℂ → ℂ} {z₀ : ℂ} {c : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g z₀)
    (hev : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h z₀ ∧
      ∀ᶠ z in 𝓝[≠] z₀, f z - c / (z - z₀) = h z :=
  ⟨g, hg, hev.mono fun z hz => by rw [hz]; ring⟩

private theorem principalPartSum_rest_analyticAt
    (S : Finset ℂ) (s : ℂ) (c : ℂ → ℂ) :
    AnalyticAt ℂ (fun z => ∑ t ∈ S.erase s, c t / (z - t)) s := by
  apply Finset.analyticAt_fun_sum
  intro t ht
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr (Finset.ne_of_mem_erase ht).symm)

/-- The principal part sum decomposes at `s ∈ S` as:
`principalPartSum S c z = c s / (z - s) + ∑ t ∈ S.erase s, c t / (z - t)`. -/
theorem principalPartSum_eq_term_add_rest
    {S : Finset ℂ} {s : ℂ} (hs : s ∈ S) (c : ℂ → ℂ) (z : ℂ) :
    principalPartSum S c z = c s / (z - s) + ∑ t ∈ S.erase s, c t / (z - t) :=
  (Finset.add_sum_erase _ _ hs).symm

/-- If `f` has a simple pole decomposition `f(z) = c(s)/(z-s) + g_s(z)` at each `s ∈ S`,
then `f - principalPartSum S c` is analytic at each pole `s ∈ S`.

The key idea: at any particular pole `s`,
  `f(z) - principalPartSum S c z`
  `= f(z) - c(s)/(z-s) - ∑_{t ≠ s} c(t)/(z-t)`
  `= g_s(z) - ∑_{t ≠ s} c(t)/(z-t)`
which is analytic at `s` since `g_s` is analytic and the remaining sum avoids `s`. -/
theorem sub_principalPartSum_analyticAt {f : ℂ → ℂ} {S : Finset ℂ} {c : ℂ → ℂ}
    {s : ℂ} (hs : s ∈ S)
    (h_pole : HasSimplePoleAt f s)
    (h_coeff : h_pole.coeff = c s) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - principalPartSum S c z = g z := by
  refine ⟨fun z => h_pole.regularPart z - ∑ t ∈ S.erase s, c t / (z - t),
    h_pole.regularPart_analyticAt.sub (principalPartSum_rest_analyticAt S s c), ?_⟩
  filter_upwards [h_pole.eventually_eq] with z hf_eq
  rw [principalPartSum_eq_term_add_rest hs c z, hf_eq, h_coeff]
  ring

/-- The residue of `principalPartSum S c` at `s ∈ S` equals `c s`. -/
theorem residue_principalPartSum {S : Finset ℂ} {c : ℂ → ℂ} {s : ℂ} (hs : s ∈ S) :
    residue (principalPartSum S c) s = c s :=
  residue_eq_of_simple_pole_decomp (principalPartSum_rest_analyticAt S s c)
    (.of_forall fun z => principalPartSum_eq_term_add_rest hs c z)

/-- The residue of `f` at a simple pole equals its coefficient. -/
theorem residue_eq_coeff_of_hasSimplePoleAt {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) :
    residue f z₀ = h.coeff :=
  residue_eq_coeff h

/-- The principal part sum is analytic at any point not in `S`. -/
theorem principalPartSum_analyticAt {S : Finset ℂ} {c : ℂ → ℂ} {z : ℂ}
    (hz : z ∉ S) :
    AnalyticAt ℂ (principalPartSum S c) z := by
  change AnalyticAt ℂ (fun w => ∑ s ∈ S, c s / (w - s)) z
  apply Finset.analyticAt_fun_sum
  intro s hs
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr (fun heq => hz (heq ▸ hs)))

/-- The principal part sum is differentiable at any point not in `S`. -/
theorem principalPartSum_differentiableAt {S : Finset ℂ} {c : ℂ → ℂ} {z : ℂ}
    (hz : z ∉ S) :
    DifferentiableAt ℂ (principalPartSum S c) z :=
  (principalPartSum_analyticAt hz).differentiableAt

/-- The principal part sum is meromorphic at every point of `ℂ`. -/
theorem principalPartSum_meromorphicAt (S : Finset ℂ) (c : ℂ → ℂ) (z : ℂ) :
    MeromorphicAt (principalPartSum S c) z :=
  MeromorphicAt.fun_sum fun _ _ =>
    analyticAt_const.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt

end
