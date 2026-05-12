/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.HungerbuhlerWasem
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Laurent extraction for HungerbuhlerWasem (T-LE-01)

For the Hungerbühler–Wasem residue theorem in its full crossing form, we need
to extract a Laurent decomposition `f = polarPart + holomorphicRemainder` at
each pole `s ∈ S`. Condition (B) (`SatisfiesConditionB.laurent_compatible`)
already carries this data via `∃ N a g, ...`.

This file extracts that data into named functions (using `Classical.choose`)
and builds a `PolarPartDecomposition` from a `SatisfiesConditionB` hypothesis.

## Main definitions

* `HungerbuhlerWasem.IsCrossed γ s` — `γ` crosses `s` in the open interval.
* `HungerbuhlerWasem.crossingParam γ s` — the crossing parameter `t₀` selected
  via `Classical.choose`.
* `HungerbuhlerWasem.laurentPolarPartAt hCondB s _ z` — the local polar part
  at a (possibly uncrossed) pole `s`.
* `HungerbuhlerWasem.laurentAnalyticPartAt hCondB s _` — the analytic part `g_s`
  from condition (B)'s `laurent_compatible` field.
* `HungerbuhlerWasem.PolarPartDecomposition.ofConditionB` — the constructor
  consuming `SatisfiesConditionB γ f S` to build a `PolarPartDecomposition`.

## Strategy

We use `Classical.choose` on `hCondB.laurent_compatible` to extract the data
`(N, a, g)` for each crossed pole. For uncrossed poles, we use a default
`order = 0` (empty polar part) and the analytic remainder is `f` locally.
This adds no axioms beyond the existing `Classical.choice`.
-/

open Filter Topology Set Complex MeasureTheory Metric

noncomputable section

namespace HungerbuhlerWasem

variable {x : ℂ}

/-! ## Crossing parameter extraction -/

/-- Predicate: pole `s` is crossed by `γ` in the open interval `(0, 1)`. -/
def IsCrossed (γ : PwC1Immersion x x) (s : ℂ) : Prop :=
  ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s

/-- Selector for the crossing parameter `t₀` of pole `s`: the unique `t₀ ∈ (0, 1)`
with `γ(t₀) = s` if any exists, or `0` (default) otherwise. -/
noncomputable def crossingParam (γ : PwC1Immersion x x) (s : ℂ) : ℝ :=
  open Classical in if h : IsCrossed γ s then Classical.choose h else 0

theorem crossingParam_mem_Ioo {γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) :
    crossingParam γ s ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa [crossingParam, h] using (Classical.choose_spec h).1

theorem γ_at_crossingParam {γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) :
    (γ : ℝ → ℂ) (crossingParam γ s) = s := by
  simpa [crossingParam, h] using (Classical.choose_spec h).2

/-! ## Laurent decomposition extraction from condition (B) -/

/-- Helper: when `s ∈ S`, `γ` crosses `s`, and `hCondB.laurent_compatible`
holds, extract the existential at `s`. -/
private theorem laurent_data_exists {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      (∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧
      (∀ k : Fin N, a k ≠ 0 → k.val ≥ 1 → ∃ m : ℤ,
        (↑k.val : ℝ) * angleAtCrossing γ (crossingParam γ s)
          (crossingParam_mem_Ioo h_cross) = ↑m * (2 * Real.pi)) :=
  hCondB.laurent_compatible s hs (crossingParam γ s)
    (Set.Ioo_subset_Icc_self (crossingParam_mem_Ioo h_cross))
    (γ_at_crossingParam h_cross) (crossingParam_mem_Ioo h_cross)

/-- Local polar part at pole `s`: `∑ k ∈ Fin N, a_k / (z - s)^(k+1)`,
where `N` and `a_k` come from condition (B) at the crossing parameter
of `s` (if crossed; zero otherwise).

The single `if-then-else` (rather than separate `order` / `coeff` definitions
on the side) avoids dependent-type clashes when unfolding: the `Fin` index,
the coefficients, and the sum all live inside the same conditional, so
`dif_pos` reduces the whole expression cleanly. -/
noncomputable def laurentPolarPartAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S)
    (z : ℂ) : ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    ∑ k : Fin (laurent_data_exists hCondB hs h).choose,
      (laurent_data_exists hCondB hs h).choose_spec.choose k /
        (z - s) ^ (k.val + 1)
  else 0

/-- Order of the local polar part at `s ∈ S`. For crossed poles, this is the
`N` from condition (B); for uncrossed poles, this is `0`. -/
noncomputable def laurentPolarOrderAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) :
    ℕ :=
  open Classical in
  if h : IsCrossed γ s then
    (laurent_data_exists hCondB hs h).choose
  else 0

/-- Laurent coefficient `a_k` at `s ∈ S`. The `Fin` index lives in
`Fin (laurentPolarOrderAt _ _ _)`. For crossed poles, this is from
condition (B); for uncrossed poles, the order is 0 so this is vacuous. -/
noncomputable def laurentPolarCoeffAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S)
    (k : Fin (laurentPolarOrderAt hCondB s hs)) : ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    have hN : laurentPolarOrderAt hCondB s hs =
        (laurent_data_exists hCondB hs h).choose := by
      simp only [laurentPolarOrderAt, h, ↓reduceDIte]
    (laurent_data_exists hCondB hs h).choose_spec.choose
      (Fin.cast hN k)
  else by
    have h0 : laurentPolarOrderAt hCondB s hs = 0 := by
      simp only [laurentPolarOrderAt, h, ↓reduceDIte]
    exact absurd k.isLt (by omega)

/-- The analytic remainder `g` from condition (B)'s Laurent compatibility data
at a (possibly uncrossed) pole `s ∈ S`. By definition, when `s` is crossed,
`f z = g z + ∑ a_k / (z-s)^(k+1)` holds eventually near `s`. For uncrossed
`s`, this is the function `f` itself (local analytic remainder is just `f`,
since there is no polar part to subtract). -/
noncomputable def laurentAnalyticPartAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) :
    ℂ → ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    (laurent_data_exists hCondB hs h).choose_spec.choose_spec.choose
  else f

/-! ## Unfolding lemmas -/

private lemma laurentAnalyticPartAt_eq_data {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    laurentAnalyticPartAt hCondB s hs =
      (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose := by
  simp [laurentAnalyticPartAt, h_cross]

private lemma laurentPolarPartAt_eq_data {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) (z : ℂ) :
    laurentPolarPartAt hCondB s hs z =
      ∑ k : Fin (laurent_data_exists hCondB hs h_cross).choose,
        (laurent_data_exists hCondB hs h_cross).choose_spec.choose k /
          (z - s) ^ (k.val + 1) := by
  simp [laurentPolarPartAt, h_cross]

private lemma laurentPolarPartAt_uncrossed {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_not_cross : ¬ IsCrossed γ s) (z : ℂ) :
    laurentPolarPartAt hCondB s hs z = 0 := by
  simp [laurentPolarPartAt, h_not_cross]

private lemma laurentPolarOrderAt_eq_data {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    laurentPolarOrderAt hCondB s hs = (laurent_data_exists hCondB hs h_cross).choose := by
  simp [laurentPolarOrderAt, h_cross]

private lemma laurentPolarOrderAt_uncrossed {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_not_cross : ¬ IsCrossed γ s) :
    laurentPolarOrderAt hCondB s hs = 0 := by
  simp [laurentPolarOrderAt, h_not_cross]

/-- The analytic part is `AnalyticAt ℂ` at `s` (for crossed `s`). -/
theorem laurentAnalyticPartAt_analyticAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    AnalyticAt ℂ (laurentAnalyticPartAt hCondB s hs) s := by
  rw [laurentAnalyticPartAt_eq_data hCondB hs h_cross]
  exact (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose_spec.1

/-- **Local Laurent decomposition**: near a crossed pole `s`, `f` decomposes
as `analyticPartAt s + polarPartAt s` (eventually equal in the punctured
neighborhood). -/
theorem f_eq_analyticPart_plus_polarPart_eventually {γ : PwC1Immersion x x}
    {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    ∀ᶠ z in 𝓝[≠] s, f z =
      laurentAnalyticPartAt hCondB s hs z + laurentPolarPartAt hCondB s hs z := by
  filter_upwards
    [(laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose_spec.2.1]
    with z hz
  rw [hz, laurentPolarPartAt_eq_data hCondB hs h_cross z]
  congr 1
  exact congrArg (· z) (laurentAnalyticPartAt_eq_data hCondB hs h_cross).symm

/-- **Corollary**: `f - laurentPolarPartAt s = laurentAnalyticPartAt s`
eventually in the punctured neighborhood of a crossed pole `s`. -/
theorem f_minus_polarPartAt_eventuallyEq_analyticPartAt {γ : PwC1Immersion x x}
    {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    (fun z => f z - laurentPolarPartAt hCondB s hs z) =ᶠ[𝓝[≠] s]
      laurentAnalyticPartAt hCondB s hs := by
  filter_upwards [f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross] with z hz
  rw [hz]
  ring

/-! ## Differentiability of the polar part -/

/-- `laurentPolarPartAt s` is differentiable at any point `z ≠ s`. -/
theorem laurentPolarPartAt_differentiableAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) {z : ℂ}
    (hz : z ≠ s) :
    DifferentiableAt ℂ (laurentPolarPartAt hCondB s hs) z := by
  unfold laurentPolarPartAt
  by_cases h : IsCrossed γ s
  · simp only [dif_pos h]
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact (differentiableAt_const _).div
      ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
      (pow_ne_zero _ (sub_ne_zero.mpr hz))
  · simp only [dif_neg h]
    exact differentiableAt_const _

/-! ## Polar part = explicit Laurent sum (using order/coeff) -/

/-- The polar part `laurentPolarPartAt` written as the explicit Laurent sum
using `laurentPolarOrderAt` (the order) and `laurentPolarCoeffAt` (the
coefficients). This is the form needed for `PolarPartDecomposition.polarPart_eq`. -/
theorem laurentPolarPartAt_eq_sum {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (z : ℂ) :
    laurentPolarPartAt hCondB s hs z =
      ∑ k : Fin (laurentPolarOrderAt hCondB s hs),
        laurentPolarCoeffAt hCondB s hs k / (z - s) ^ (k.val + 1) := by
  by_cases h : IsCrossed γ s
  · rw [laurentPolarPartAt_eq_data hCondB hs h z, ← Fin.sum_congr'
      (fun k : Fin (laurent_data_exists hCondB hs h).choose =>
        (laurent_data_exists hCondB hs h).choose_spec.choose k /
          (z - s) ^ (k.val + 1)) (laurentPolarOrderAt_eq_data hCondB hs h)]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp [laurentPolarCoeffAt, h]
  · rw [laurentPolarPartAt_uncrossed hCondB hs h z]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    have h0 : laurentPolarOrderAt hCondB s hs = 0 :=
      laurentPolarOrderAt_uncrossed hCondB hs h
    exact absurd k.isLt (by omega)

/-! ## Residue from the Laurent expansion

For the residue formula `residue f s = a_0` from a Laurent expansion
`f z = g z + ∑_k a_k / (z - s)^(k+1)`, we compute via the circle integral:

* `g` analytic ⇒ `∮ g = 0`
* `a_0 / (z - s)` ⇒ `∮ = 2πi · a_0`
* `a_k / (z - s)^(k+1)` for `k ≥ 1` (i.e. exponent ≤ -2) ⇒ `∮ = 0` by
  `circleIntegral.integral_sub_zpow_of_ne`

Hence `(2πi)⁻¹ · ∮ f = a_0`, so `residue f s = a_0`. -/

private lemma circleIntegral_higherOrder_eq_zero
    {s : ℂ} {r : ℝ} {n : ℕ} (hn : 2 ≤ n) (c : ℂ) :
    ∮ z in C(s, r), c / (z - s) ^ n = 0 := by
  have h_eq : (fun z => c / (z - s) ^ n) = fun z => c * (z - s) ^ (-(n : ℤ)) := by
    funext z
    rw [div_eq_mul_inv, zpow_neg, zpow_natCast]
  rw [h_eq, circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_zpow_of_ne (by omega) s s r, mul_zero]

private lemma circleIntegral_higherOrder_sum_eq_zero
    {s : ℂ} {r : ℝ} (hr : 0 < r) {N : ℕ} (a : Fin N → ℂ) :
    ∮ z in C(s, r),
      (∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) = 0 := by
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hs_notin : s ∉ sphere s |r| := by
    rw [mem_sphere, dist_self, abs_of_pos hr]
    exact hr_ne.symm
  have h_each_int : ∀ k : Fin N, CircleIntegrable
      (fun z => if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) s r := by
    intro k
    by_cases hk : k.val ≥ 1
    · simp only [hk, ↓reduceIte]
      have h_eq : (fun z => a k / (z - s) ^ (k.val + 1)) =
          fun z => a k * (z - s) ^ (-((k.val + 1 : ℕ) : ℤ)) := by
        funext z
        rw [div_eq_mul_inv, zpow_neg, zpow_natCast]
      rw [h_eq]
      apply CircleIntegrable.const_smul
      change CircleIntegrable (fun z => (z - s) ^ (-((k.val + 1 : ℕ) : ℤ))) s r
      rw [circleIntegrable_sub_zpow_iff]
      exact Or.inr (Or.inr hs_notin)
    · simp only [hk, ↓reduceIte]
      exact circleIntegrable_const _ _ _
  rw [circleIntegral.integral_fun_sum (s := Finset.univ) (fun k _ => h_each_int k)]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k.val ≥ 1
  · simp only [hk, ↓reduceIte]
    exact circleIntegral_higherOrder_eq_zero (by omega) (a k)
  · simp only [hk, ↓reduceIte]
    simp [circleIntegral]

/-- **Residue computation from Laurent data.** For a function `f` with the
Laurent expansion `f z = g z + ∑ k : Fin N, a k / (z - s)^(k+1)` near `s`
(where `g` is analytic at `s`), the residue equals `a 0` (or `0` if `N = 0`).

This is the higher-order generalization of `residue_eq_of_simple_pole_decomp`:
the analytic part contributes zero, the order-0 Laurent term `a_0/(z-s)`
contributes `a_0`, and higher-order terms `a_k/(z-s)^(k+1)` for `k ≥ 1` all
have circle integral zero. -/
theorem residue_of_laurent_expansion {f g : ℂ → ℂ} {s : ℂ} (N : ℕ) (a : Fin N → ℂ)
    (hg : AnalyticAt ℂ g s)
    (hf_eq : ∀ᶠ z in 𝓝[≠] s,
      f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) :
    residue f s = if h : 0 < N then a ⟨0, h⟩ else 0 := by
  by_cases hN_pos : 0 < N
  · rw [dif_pos hN_pos]
    set rest : ℂ → ℂ := fun z =>
      g z + ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0
        with hrest_def
    have hf_eq' : ∀ᶠ z in 𝓝[≠] s, f z = a ⟨0, hN_pos⟩ / (z - s) + rest z := by
      filter_upwards [hf_eq] with z hz
      rw [hz, hrest_def]
      have hsplit : ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) =
          a ⟨0, hN_pos⟩ / (z - s) +
            ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0 := by
        rw [show (∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) =
            ∑ k : Fin N, ((if k.val = 0 then a ⟨0, hN_pos⟩ / (z - s) else 0) +
              (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0)) from ?_,
          Finset.sum_add_distrib]
        · congr 1
          rw [Finset.sum_eq_single ⟨0, hN_pos⟩]
          · simp
          · intro k _ hk
            have hk0 : k.val ≠ 0 := fun h_eq => hk (Fin.ext h_eq)
            simp [hk0]
          · simp
        · refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hk : k.val = 0
          · have heq : k = ⟨0, hN_pos⟩ := Fin.ext hk
            simp [heq]
          · have hk1 : k.val ≥ 1 := by omega
            simp [hk, hk1]
      rw [hsplit]
      ring
    unfold residue
    apply Filter.Tendsto.limUnder_eq
    apply tendsto_nhds_of_eventually_eq
    obtain ⟨rg, hrg_pos, hg_ball⟩ := hg.exists_ball_analyticOnNhd
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hf_eq'
    obtain ⟨rf, hrf_pos, hrf_eq⟩ := hf_eq'
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (lt_min hrg_pos hrf_pos)] with r hr_lt hr_pos
    simp only [mem_Ioi, mem_Iio] at hr_pos hr_lt
    have hr_lt_rg : r < rg := lt_of_lt_of_le hr_lt (min_le_left _ _)
    have hr_lt_rf : r < rf := lt_of_lt_of_le hr_lt (min_le_right _ _)
    have hr_ne : r ≠ 0 := ne_of_gt hr_pos
    have h_eq_on : EqOn f (fun z => a ⟨0, hN_pos⟩ * (z - s)⁻¹ + rest z) (sphere s r) := by
      intro z hz
      have h_ne : z ≠ s := by
        intro heq
        rw [heq, mem_sphere, dist_self] at hz
        linarith
      have h_mem_ball : z ∈ ball s rf := by
        rw [mem_ball, mem_sphere.mp hz]
        exact hr_lt_rf
      have h_mem : z ∈ ball s rf ∩ {s}ᶜ :=
        ⟨h_mem_ball, mem_compl_singleton_iff.mpr h_ne⟩
      have := hrf_eq h_mem
      simp only [mem_setOf_eq] at this
      rw [this, div_eq_mul_inv]
    have h_ci_g : CircleIntegrable g s r :=
      ((hg_ball.continuousOn.mono (closedBall_subset_ball hr_lt_rg)).mono
        sphere_subset_closedBall).circleIntegrable hr_pos.le
    have hs_notin : s ∉ sphere s |r| := by
      rw [mem_sphere, dist_self, abs_of_pos hr_pos]
      exact hr_ne.symm
    have h_ci_higher_each : ∀ k : Fin N, CircleIntegrable
        (fun z => if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) s r := by
      intro k
      by_cases hk : k.val ≥ 1
      · simp only [hk, ↓reduceIte]
        have h_eq : (fun z => a k / (z - s) ^ (k.val + 1)) =
            fun z => a k * (z - s) ^ (-((k.val + 1 : ℕ) : ℤ)) := by
          funext z
          rw [div_eq_mul_inv, zpow_neg, zpow_natCast]
        rw [h_eq]
        apply CircleIntegrable.const_smul
        change CircleIntegrable (fun z => (z - s) ^ (-((k.val + 1 : ℕ) : ℤ))) s r
        rw [circleIntegrable_sub_zpow_iff]
        exact Or.inr (Or.inr hs_notin)
      · simp only [hk, ↓reduceIte]
        exact circleIntegrable_const _ _ _
    have h_ci_higher_sum : CircleIntegrable
        (fun z => ∑ k : Fin N, if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0)
        s r := by
      change CircleIntegrable
        (fun z => ∑ k ∈ Finset.univ,
          if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0) s r
      have h_eq : (fun z => ∑ k ∈ Finset.univ,
          (if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0 : ℂ)) =
          ∑ k ∈ (Finset.univ : Finset (Fin N)),
            fun z => if k.val ≥ 1 then a k / (z - s) ^ (k.val + 1) else 0 := by
        funext z
        rw [Finset.sum_apply]
      rw [h_eq]
      exact CircleIntegrable.sum _ (fun k _ => h_ci_higher_each k)
    have h_ci_rest : CircleIntegrable rest s r := by
      simp only [hrest_def]
      exact h_ci_g.add h_ci_higher_sum
    have h_ci_a0_inv : CircleIntegrable (fun z => a ⟨0, hN_pos⟩ * (z - s)⁻¹) s r :=
      (circleIntegrable_sub_inv_iff.mpr (Or.inr (by
        rw [mem_sphere, dist_self, abs_of_pos hr_pos]
        exact hr_ne.symm))).const_fun_smul
    rw [circleIntegral.integral_congr hr_pos.le h_eq_on,
      circleIntegral.integral_add h_ci_a0_inv h_ci_rest,
      circleIntegral.integral_const_mul,
      circleIntegral.integral_sub_center_inv s hr_ne]
    have h_int_g : ∮ z in C(s, r), g z = 0 := by
      apply circleIntegral_eq_zero_of_differentiable_on_off_countable hr_pos.le
        countable_empty
        (hg_ball.continuousOn.mono (closedBall_subset_ball hr_lt_rg))
      intro z ⟨hz, _⟩
      exact (hg_ball z (ball_subset_ball hr_lt_rg.le hz)).differentiableAt
    have h_int_rest : ∮ z in C(s, r), rest z = 0 := by
      simp only [hrest_def]
      rw [circleIntegral.integral_add h_ci_g h_ci_higher_sum, h_int_g, zero_add]
      exact circleIntegral_higherOrder_sum_eq_zero hr_pos a
    rw [h_int_rest, add_zero]
    field_simp
  · have hN_zero : N = 0 := by omega
    subst hN_zero
    rw [dif_neg (by omega)]
    have hf_eq_g : ∀ᶠ z in 𝓝[≠] s, f z = g z := by
      filter_upwards [hf_eq] with z hz
      rw [hz]
      simp
    rw [residue_congr hf_eq_g]
    exact residue_eq_zero_of_analyticAt hg

/-- The leading Laurent coefficient `a_0` equals the residue of `f` at `s`
(for crossed `s`). -/
theorem laurentPolarCoeffAt_zero_eq_residue {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) (h_pos : 0 < laurentPolarOrderAt hCondB s hs) :
    laurentPolarCoeffAt hCondB s hs ⟨0, h_pos⟩ = residue f s := by
  have h_data := laurent_data_exists hCondB hs h_cross
  set N := h_data.choose
  set a := h_data.choose_spec.choose
  set g := h_data.choose_spec.choose_spec.choose
  have hg_an : AnalyticAt ℂ g s := h_data.choose_spec.choose_spec.choose_spec.1
  have hf_eq : ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) :=
    h_data.choose_spec.choose_spec.choose_spec.2.1
  have hN_eq : laurentPolarOrderAt hCondB s hs = N :=
    laurentPolarOrderAt_eq_data hCondB hs h_cross
  have hN_pos : 0 < N := hN_eq ▸ h_pos
  have hres := residue_of_laurent_expansion N a hg_an hf_eq
  rw [dif_pos hN_pos] at hres
  unfold laurentPolarCoeffAt
  simp only [h_cross, ↓reduceDIte]
  rw [hres]
  rfl

/-! ## The `PolarPartDecomposition.ofConditionB` constructor

Given a function `f : ℂ → ℂ` differentiable on `U \ S` with `SatisfiesConditionB`
data and the additional hypothesis that γ crosses every pole in `S`, we
construct a `PolarPartDecomposition`. The constructor uses condition (B)'s
Laurent data via `Classical.choose` to extract the per-pole order, coefficients,
and analytic remainder.

The hypothesis `hAllCrossed : ∀ s ∈ S, IsCrossed γ s` is needed because
condition (B) only provides Laurent data at crossed poles. For uncrossed
poles (γ doesn't pass through them), separate Laurent data would be needed
(e.g., from `MeromorphicAt`). The follow-up T-LE-02 generalizes this to
mixed crossed/uncrossed poles using `MeromorphicAt`. -/

/-- The total polar part across all poles. -/
noncomputable def laurentPolarPartTotal {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, laurentPolarPartAt hCondB s.1 s.2 z

/-- Local Laurent decomposition for the OTHER polar parts (not at `s`):
their sum is analytic at `s`. -/
private theorem otherPolar_analyticAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (_hs : s ∈ S) :
    AnalyticAt ℂ (fun z => ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
      laurentPolarPartAt hCondB s'.1 s'.2 z) s := by
  refine Finset.analyticAt_fun_sum _ fun s' hs' => ?_
  have h_ne : s'.1 ≠ s := (Finset.mem_filter.mp hs').2
  unfold laurentPolarPartAt
  by_cases h_cross : IsCrossed γ s'.1
  · simp only [dif_pos h_cross]
    refine Finset.analyticAt_fun_sum _ fun k _ => ?_
    exact (analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
      (pow_ne_zero _ (sub_ne_zero.mpr h_ne.symm)))
  · simp only [dif_neg h_cross]
    exact analyticAt_const

/-- **Local analytic decomposition near `s` (crossed pole).**
Near `s ∈ S` (with γ crossing `s`):
  `f - ∑ s' ∈ S, polarPart s' = (f - polarPart s) - ∑ s' ≠ s, polarPart s'`
                              = analyticPart s - ∑ s' ≠ s, polarPart s'
The right side is analytic at `s`. -/
private theorem f_minus_total_eventuallyEq_analytic {γ : PwC1Immersion x x}
    {f : ℂ → ℂ} {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    ∃ g_s : ℂ → ℂ, AnalyticAt ℂ g_s s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - laurentPolarPartTotal hCondB z = g_s z := by
  set g_s : ℂ → ℂ := fun z =>
    laurentAnalyticPartAt hCondB s hs z -
      ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
        laurentPolarPartAt hCondB s'.1 s'.2 z with hg_s_def
  refine ⟨g_s, (laurentAnalyticPartAt_analyticAt hCondB hs h_cross).sub
    (otherPolar_analyticAt hCondB hs), ?_⟩
  filter_upwards [f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross]
    with z hz
  rw [hg_s_def, hz]
  suffices h_total : laurentPolarPartTotal hCondB z =
      laurentPolarPartAt hCondB s hs z +
        ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
          laurentPolarPartAt hCondB s'.1 s'.2 z by
    rw [h_total]
    ring
  unfold laurentPolarPartTotal
  rw [show (∑ s' ∈ S.attach, laurentPolarPartAt hCondB s'.1 s'.2 z) =
      (∑ s' ∈ S.attach.filter (fun s' => s'.1 = s),
        laurentPolarPartAt hCondB s'.1 s'.2 z) +
      (∑ s' ∈ S.attach.filter (fun s' => ¬ s'.1 = s),
        laurentPolarPartAt hCondB s'.1 s'.2 z) from
    (Finset.sum_filter_add_sum_filter_not S.attach _ _).symm]
  have h_singleton : S.attach.filter (fun s' => s'.1 = s) = {⟨s, hs⟩} := by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
    refine ⟨fun h_eq => ?_, fun h_eq => ?_⟩
    · ext
      exact h_eq
    · rw [h_eq]
  rw [h_singleton, Finset.sum_singleton]

/-- **The constructor: `PolarPartDecomposition.ofConditionB`.**

Given:
- `U` open in `ℂ`, `S ⊆ U` finite,
- `f : ℂ → ℂ` differentiable on `U \ S`,
- A piecewise-`C¹` immersion `γ` with `SatisfiesConditionB γ f S`,
- The hypothesis `hAllCrossed` that γ crosses every pole in `S`,

we build a `PolarPartDecomposition f S U` with the polar parts and Laurent
coefficients extracted from condition (B) via `Classical.choose`. -/
noncomputable def PolarPartDecomposition.ofConditionB {U : Set ℂ} (hU_open : IsOpen U)
    {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U \ ↑S)) {γ : PwC1Immersion x x}
    (hCondB : SatisfiesConditionB γ f S) (hAllCrossed : ∀ s ∈ S, IsCrossed γ s) :
    PolarPartDecomposition f S U := by
  let polarPart : ℂ → ℂ → ℂ := fun s z =>
    if h_mem : s ∈ S then laurentPolarPartAt hCondB s h_mem z else 0
  let order : ℂ → ℕ := fun s =>
    if h_mem : s ∈ S then laurentPolarOrderAt hCondB s h_mem else 0
  let coeff : (s : ℂ) → Fin (order s) → ℂ := fun s k =>
    if h_mem : s ∈ S then
      laurentPolarCoeffAt hCondB s h_mem (Fin.cast (by simp [order, h_mem]) k)
    else by
      have h0 : order s = 0 := by simp [order, h_mem]
      exact absurd k.isLt (by omega)
  set rem : ℂ → ℂ := fun z => f z - laurentPolarPartTotal hCondB z with hrem_def
  set correction : ℂ → ℂ := fun z =>
    if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) rem else rem z with hcorr_def
  refine
    { polarPart := polarPart
      order := order
      coeff := coeff
      polarPart_eq := ?_
      residue_eq := ?_
      analyticRemainder := correction
      analyticRemainder_diff := ?_
      decomp := ?_ }
  · intro s hs z _hz
    have h_pp : polarPart s z = laurentPolarPartAt hCondB s hs z := by
      simp only [polarPart, hs, ↓reduceDIte]
    have h_order : order s = laurentPolarOrderAt hCondB s hs := by
      simp only [order, hs, ↓reduceDIte]
    rw [h_pp, laurentPolarPartAt_eq_sum hCondB hs z, ← Fin.sum_congr'
      (fun k : Fin (laurentPolarOrderAt hCondB s hs) =>
        laurentPolarCoeffAt hCondB s hs k / (z - s) ^ (k.val + 1)) h_order]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [coeff, hs, ↓reduceDIte]
  · intro s hs
    have h_order : order s = laurentPolarOrderAt hCondB s hs := by
      simp only [order, hs, ↓reduceDIte]
    by_cases h_pos : 0 < order s
    · rw [dif_pos h_pos]
      have h_pos' : 0 < laurentPolarOrderAt hCondB s hs := h_order ▸ h_pos
      rw [← laurentPolarCoeffAt_zero_eq_residue hCondB hs (hAllCrossed s hs) h_pos']
      change laurentPolarCoeffAt hCondB s hs ⟨0, h_pos'⟩ = coeff s ⟨0, h_pos⟩
      simp only [coeff, hs, ↓reduceDIte]
      rfl
    · rw [dif_neg h_pos]
      have h_order_zero : order s = 0 := by omega
      have h_zero : laurentPolarOrderAt hCondB s hs = 0 := by
        rw [← h_order]
        exact h_order_zero
      have h_cross := hAllCrossed s hs
      have h_data := laurent_data_exists hCondB hs h_cross
      set N := h_data.choose
      set a := h_data.choose_spec.choose
      set g := h_data.choose_spec.choose_spec.choose
      have hg_an : AnalyticAt ℂ g s := h_data.choose_spec.choose_spec.choose_spec.1
      have hf_eq : ∀ᶠ z in 𝓝[≠] s,
          f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) :=
        h_data.choose_spec.choose_spec.choose_spec.2.1
      have hN_eq : laurentPolarOrderAt hCondB s hs = N :=
        laurentPolarOrderAt_eq_data hCondB hs h_cross
      have hN_zero : N = 0 := hN_eq ▸ h_zero
      have hres := residue_of_laurent_expansion N a hg_an hf_eq
      rw [dif_neg (by omega)] at hres
      exact hres
  · intro z hzU
    by_cases hzS : z ∈ (↑S : Set ℂ)
    · have hzS' := Finset.mem_coe.mp hzS
      obtain ⟨g_z, hg_z_an, hg_z_eq⟩ :=
        f_minus_total_eventuallyEq_analytic hCondB hzS' (hAllCrossed z hzS')
      have h_corr_eq : (fun w => correction w) =ᶠ[𝓝 z] g_z := by
        have h_lim_eq : limUnder (𝓝[≠] z) rem = g_z z :=
          (hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            |>.congr' (hg_z_eq.mono fun _ h => h.symm)).limUnder_eq
        have h_at_z : correction z = g_z z := by
          change (if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) rem else rem z) = g_z z
          rw [if_pos hzS, h_lim_eq]
        have hz_not_erase : z ∉ (↑(S.erase z) : Set ℂ) := fun hmem =>
          (Finset.mem_erase.mp (Finset.mem_coe.mp hmem)).1 rfl
        obtain ⟨V, hV_open, hz_V, hV_eq⟩ := mem_nhdsWithin.mp hg_z_eq
        have h_erase_away : (↑(S.erase z) : Set ℂ)ᶜ ∈ 𝓝 z :=
          (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds hz_not_erase
        apply Filter.mem_of_superset (Filter.inter_mem (hV_open.mem_nhds hz_V) h_erase_away)
        intro w ⟨hw_V, hw_erase⟩
        change correction w = g_z w
        by_cases hwz : w = z
        · rw [hwz, h_at_z]
        · have hw_not_S : w ∉ (↑S : Set ℂ) := fun hmem => hw_erase
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwz, Finset.mem_coe.mp hmem⟩))
          change (if w ∈ (↑S : Set ℂ) then _ else rem w) = g_z w
          rw [if_neg hw_not_S]
          exact hV_eq ⟨hw_V, hwz⟩
      exact (hg_z_an.differentiableAt.congr_of_eventuallyEq h_corr_eq).differentiableWithinAt
    · have h_U_minus_S := hU_open.sdiff S.finite_toSet.isClosed
      have hzU_S : z ∈ U \ (↑S : Set ℂ) := ⟨hzU, hzS⟩
      have h_f_diff : DifferentiableAt ℂ f z :=
        (hf z hzU_S).differentiableAt (h_U_minus_S.mem_nhds hzU_S)
      have h_total_diff : DifferentiableAt ℂ (laurentPolarPartTotal hCondB) z := by
        unfold laurentPolarPartTotal
        refine DifferentiableAt.fun_sum fun s' _ => ?_
        refine laurentPolarPartAt_differentiableAt hCondB s'.2 fun h_eq => ?_
        exact hzS (h_eq ▸ Finset.mem_coe.mpr s'.2)
      have h_corr_eq : (fun w => correction w) =ᶠ[𝓝 z] rem := by
        apply Filter.mem_of_superset (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
        intro w hw
        change (if w ∈ (↑S : Set ℂ) then _ else rem w) = rem w
        rw [if_neg hw]
      exact ((h_f_diff.sub h_total_diff).congr_of_eventuallyEq h_corr_eq).differentiableWithinAt
  · intro z ⟨_, hzS⟩
    have h_corr : correction z = rem z := by simp only [hcorr_def, hzS, ↓reduceIte]
    have h_rem : rem z = f z - laurentPolarPartTotal hCondB z := by simp only [hrem_def]
    have h_total : laurentPolarPartTotal hCondB z = ∑ s ∈ S, polarPart s z := by
      unfold laurentPolarPartTotal
      rw [show ∑ s ∈ S, polarPart s z = ∑ s' ∈ S.attach, polarPart s'.1 z from
        (Finset.sum_attach S _).symm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [polarPart, s'.2, ↓reduceDIte]
    change f z = correction z + ∑ s ∈ S, polarPart s z
    rw [h_corr, h_rem, h_total]
    ring

/-! ## Generalization to mixed crossed/uncrossed poles via `MeromorphicAt` (T-BR-01)

For uncrossed poles, condition (B) does not provide Laurent data. Instead, we
extract Laurent data from `MeromorphicAt` via `meromorphicOrderAt_ne_top_iff`.
The strategy is:

1. From `MeromorphicAt f s`, get the analytic factorization
   `f =ᶠ[𝓝[≠] s] (z - s)^n • g₀(z)` where `g₀` is analytic at `s`.
2. If `n ≥ 0`: removable singularity. Set `N = 0`, polar part empty,
   analytic part `(z - s)^n · g₀(z)`.
3. If `n < 0`: true pole of order `k = -n`. Taylor-expand `g₀` to depth `k`:
   `g₀(z) = ∑_{j < k} c_j (z-s)^j + (z-s)^k · R(z)`. Then
   `f(z) = ∑_{j < k} c_j / (z-s)^(k-j) + R(z)`. Reindex with `i = k-1-j` to get
   the standard Laurent form `∑_{i < k} c_{k-1-i} / (z-s)^(i+1) + R(z)`.

This yields a uniform Laurent decomposition `f = g + ∑ a_k / (z-s)^(k+1)` for
ANY meromorphic function — independent of whether `γ` crosses `s`.
-/

/-- Peeling lemma: if `g : ℂ → ℂ` is analytic at `s`, then
`g(z) = g(s) + (z - s) * g₁(z)` near `s` for some `g₁` analytic at `s`. -/
private lemma analyticAt_peel_one {g : ℂ → ℂ} {s : ℂ} (hg : AnalyticAt ℂ g s) :
    ∃ g₁ : ℂ → ℂ, AnalyticAt ℂ g₁ s ∧
      ∀ᶠ z in 𝓝 s, g z = g s + (z - s) * g₁ z := by
  have h_diff : AnalyticAt ℂ (fun z => g z - g s) s := hg.sub analyticAt_const
  have h_value : (fun z => g z - g s) s = 0 := by simp
  have h_ord_ne : analyticOrderAt (fun z => g z - g s) s ≠ 0 := fun h_eq =>
    (h_diff.analyticOrderAt_eq_zero).mp h_eq h_value
  have h_ge : (1 : ℕ∞) ≤ analyticOrderAt (fun z => g z - g s) s :=
    Order.one_le_iff_ne_zero.mpr h_ord_ne
  obtain ⟨g₁, hg₁_an, hg₁_eq⟩ :=
    (natCast_le_analyticOrderAt h_diff).mp (by exact_mod_cast h_ge)
  refine ⟨g₁, hg₁_an, ?_⟩
  filter_upwards [hg₁_eq] with z hz
  have heq : g z - g s = (z - s) * g₁ z := by
    have := hz
    simp [smul_eq_mul, pow_one] at this
    exact this
  linear_combination heq

/-- Taylor decomposition for an analytic function: for any `g` analytic at `s` and
`k : ℕ`, there exist coefficients `c : Fin k → ℂ` and an analytic remainder
`R : ℂ → ℂ` (analytic at `s`) with
`g(z) = ∑_{j : Fin k} c j · (z - s)^j + (z - s)^k · R(z)` near `s`. -/
private lemma analyticAt_taylor_decomp {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g s) (k : ℕ) :
    ∃ (c : Fin k → ℂ) (R : ℂ → ℂ), AnalyticAt ℂ R s ∧
      ∀ᶠ z in 𝓝 s, g z = (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z := by
  induction k with
  | zero =>
      refine ⟨Fin.elim0, g, hg, ?_⟩
      filter_upwards with z
      simp
  | succ k ih =>
      obtain ⟨c, R, hR_an, hR_eq⟩ := ih
      obtain ⟨R', hR'_an, hR'_eq⟩ := analyticAt_peel_one hR_an
      refine ⟨Fin.snoc c (R s), R', hR'_an, ?_⟩
      filter_upwards [hR_eq, hR'_eq] with z hR_eq_z hR'_eq_z
      rw [hR_eq_z, hR'_eq_z, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_last,
        Fin.val_castSucc]
      ring

/-- Algebraic helper: `w^j / w^k = w^{-(k-j)}` (as inverses) for `j < k` and `w ≠ 0`. -/
private lemma pow_div_pow_neg {w : ℂ} (hw : w ≠ 0) {k j : ℕ} (hjk : j < k) :
    w ^ j * (w ^ k)⁻¹ = (w ^ (k - j))⁻¹ := by
  have h_exp : (k - j) + j = k := by omega
  rw [show (w ^ k)⁻¹ = (w ^ ((k - j) + j))⁻¹ from by rw [h_exp]]
  rw [pow_add]
  have hw_pow_j : w ^ j ≠ 0 := pow_ne_zero _ hw
  have hw_pow_kj : w ^ (k - j) ≠ 0 := pow_ne_zero _ hw
  field_simp

/-- Reindex helper: a sum `∑ j : Fin k, c j / w^(k-j)` equals
`∑ i : Fin k, c (rev i) / w^(i+1)` via the involution `j ↦ k - 1 - j`. -/
private lemma reindex_sum_fin_neg {k : ℕ} (_hk : 0 < k) (c : Fin k → ℂ) (w : ℂ) :
    (∑ j : Fin k, c j / w ^ (k - j.val)) =
      ∑ i : Fin k,
        c ⟨k - 1 - i.val, by have := i.isLt; omega⟩ / w ^ (i.val + 1) := by
  let σ : Fin k → Fin k := fun j => ⟨k - 1 - j.val, by have := j.isLt; omega⟩
  have hσ_invol : Function.Involutive σ := fun j => by
    ext
    have := j.isLt
    simp [σ]
    omega
  have h_sum_eq : (∑ i : Fin k, c (σ i) / w ^ (k - (σ i).val)) =
      ∑ j : Fin k, c j / w ^ (k - j.val) := by
    apply (Equiv.sum_comp ⟨σ, σ, hσ_invol.leftInverse, hσ_invol.rightInverse⟩
      (fun j => c j / w ^ (k - j.val)))
  rw [← h_sum_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi_lt : i.val < k := i.isLt
  congr 1
  show w ^ (k - (σ i).val) = w ^ (i.val + 1)
  congr 1
  simp only [σ]
  omega

/-- **Generic Laurent data extraction from `MeromorphicAt`.** For any meromorphic
function `f` at `s`, there exist `(N, a, g)` such that `g` is analytic at `s` and
`f =ᶠ[𝓝[≠] s] g + ∑ k : Fin N, a k / (z - s)^(k+1)`. -/
theorem mero_laurent_data_exists {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) := by
  classical
  obtain ⟨n, g₀, hg₀_an, hg₀_eq⟩ :=
    MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt.mp hMero
  by_cases hn_neg : n < 0
  · -- Pole case: n < 0
    set k : ℕ := (-n).toNat with hk_def
    have hk_eq : (k : ℤ) = -n := by rw [hk_def]; omega
    have hk_pos : 0 < k := by rw [hk_def]; omega
    have hn_eq : n = -(k : ℤ) := by omega
    obtain ⟨c, R, hR_an, hR_eq⟩ := analyticAt_taylor_decomp hg₀_an k
    refine ⟨k, fun i : Fin k => c ⟨k - 1 - i.val, by have := i.isLt; omega⟩, R, hR_an, ?_⟩
    have hR_eq_nbhd : ∀ᶠ z in 𝓝[≠] s, g₀ z =
        (∑ j : Fin k, c j * (z - s) ^ j.val) + (z - s) ^ k * R z :=
      nhdsWithin_le_nhds hR_eq
    have h_punc : ∀ᶠ z in 𝓝[≠] s, z ≠ s := self_mem_nhdsWithin
    have hg₀_eq' : ∀ᶠ z in 𝓝[≠] s, f z = (z - s) ^ (-(k : ℤ)) • g₀ z := by
      filter_upwards [hg₀_eq] with z hz
      rw [hz, hn_eq]
    filter_upwards [hg₀_eq', hR_eq_nbhd, h_punc] with z hf_eq hR_eq_z hz_ne
    have hz_sub : (z - s) ≠ 0 := sub_ne_zero.mpr hz_ne
    rw [hf_eq, hR_eq_z, smul_eq_mul, zpow_neg, zpow_natCast, mul_add]
    have h1 : ((z - s) ^ k)⁻¹ * ((z - s) ^ k * R z) = R z := by field_simp
    rw [h1, add_comm]
    congr 1
    rw [Finset.mul_sum]
    have h_target_term : ∀ j : Fin k,
        ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
          c j / (z - s) ^ (k - j.val) := by
      intro j
      have hj_lt := j.isLt
      rw [div_eq_mul_inv]
      rw [show ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
          c j * ((z - s) ^ j.val * ((z - s) ^ k)⁻¹) from by ring]
      rw [pow_div_pow_neg hz_sub hj_lt]
    rw [show ∑ j : Fin k, ((z - s) ^ k)⁻¹ * (c j * (z - s) ^ j.val) =
        ∑ j : Fin k, c j / (z - s) ^ (k - j.val) from
      Finset.sum_congr rfl fun j _ => h_target_term j]
    exact reindex_sum_fin_neg hk_pos c (z - s)
  · -- Removable singularity case: n ≥ 0
    have hn_nonneg : 0 ≤ n := not_lt.mp hn_neg
    set m : ℕ := n.toNat with hm_def
    have hm_eq : (m : ℤ) = n := by rw [hm_def]; omega
    refine ⟨0, Fin.elim0, fun z => (z - s) ^ m * g₀ z, ?_, ?_⟩
    · exact ((analyticAt_id.sub analyticAt_const).pow m).mul hg₀_an
    · filter_upwards [hg₀_eq] with z hf_eq
      simp only [Finset.sum_empty, Finset.univ_eq_empty, add_zero]
      rw [hf_eq, smul_eq_mul]
      rw [show n = (m : ℤ) by omega]
      rw [zpow_natCast]

/-! ## Mero-based Laurent data via `Classical.choose` -/

/-- Local polar part at pole `s` from a `MeromorphicAt` hypothesis: extracted
via `Classical.choose` on `mero_laurent_data_exists`. -/
noncomputable def meroPolarPartAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (z : ℂ) : ℂ :=
  ∑ k : Fin (mero_laurent_data_exists hMero).choose,
    (mero_laurent_data_exists hMero).choose_spec.choose k /
      (z - s) ^ (k.val + 1)

/-- Order of the local polar part at `s` from a `MeromorphicAt` hypothesis. -/
noncomputable def meroPolarOrderAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s) :
    ℕ :=
  (mero_laurent_data_exists hMero).choose

/-- Laurent coefficient `a_k` at `s` from a `MeromorphicAt` hypothesis. -/
noncomputable def meroPolarCoeffAt {f : ℂ → ℂ} {s : ℂ} (hMero : MeromorphicAt f s)
    (k : Fin (meroPolarOrderAt hMero)) : ℂ :=
  (mero_laurent_data_exists hMero).choose_spec.choose
    (Fin.cast (by simp [meroPolarOrderAt]) k)

/-- The analytic remainder `g` at `s` from a `MeromorphicAt` hypothesis. -/
noncomputable def meroAnalyticPartAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : ℂ → ℂ :=
  (mero_laurent_data_exists hMero).choose_spec.choose_spec.choose

/-- The analytic part is `AnalyticAt ℂ` at `s`. -/
theorem meroAnalyticPartAt_analyticAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) : AnalyticAt ℂ (meroAnalyticPartAt hMero) s :=
  (mero_laurent_data_exists hMero).choose_spec.choose_spec.choose_spec.1

/-- **Local Laurent decomposition** from `MeromorphicAt`: near `s`,
`f = analyticPart + polarPart` (in the punctured neighborhood). -/
theorem mero_f_eq_analyticPart_plus_polarPart_eventually {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    ∀ᶠ z in 𝓝[≠] s, f z = meroAnalyticPartAt hMero z + meroPolarPartAt hMero z := by
  filter_upwards
    [(mero_laurent_data_exists hMero).choose_spec.choose_spec.choose_spec.2]
    with z hz
  rw [hz]
  rfl

/-- **Corollary**: `f - meroPolarPartAt s = meroAnalyticPartAt s` eventually
in the punctured neighborhood of `s`. -/
theorem mero_f_minus_polarPartAt_eventuallyEq_analyticPartAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) :
    (fun z => f z - meroPolarPartAt hMero z) =ᶠ[𝓝[≠] s] meroAnalyticPartAt hMero := by
  filter_upwards [mero_f_eq_analyticPart_plus_polarPart_eventually hMero] with z hz
  rw [hz]
  ring

/-- `meroPolarPartAt s` is differentiable at any point `z ≠ s`. -/
theorem meroPolarPartAt_differentiableAt {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {z : ℂ} (hz : z ≠ s) :
    DifferentiableAt ℂ (meroPolarPartAt hMero) z := by
  unfold meroPolarPartAt
  refine DifferentiableAt.fun_sum fun k _ => ?_
  exact (differentiableAt_const _).div
    ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hz))

/-- `meroPolarPartAt s` is `AnalyticAt ℂ` at any point `w ≠ s`. -/
theorem meroPolarPartAt_analyticAt_off {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) {w : ℂ} (hw : w ≠ s) :
    AnalyticAt ℂ (meroPolarPartAt hMero) w := by
  unfold meroPolarPartAt
  refine Finset.analyticAt_fun_sum _ fun k _ => ?_
  exact analyticAt_const.div ((analyticAt_id.sub analyticAt_const).pow _)
    (pow_ne_zero _ (sub_ne_zero.mpr hw))

/-- Polar part written as the explicit Laurent sum using order/coeff. -/
theorem meroPolarPartAt_eq_sum {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (z : ℂ) :
    meroPolarPartAt hMero z =
      ∑ k : Fin (meroPolarOrderAt hMero),
        meroPolarCoeffAt hMero k / (z - s) ^ (k.val + 1) := by
  unfold meroPolarPartAt meroPolarCoeffAt meroPolarOrderAt
  rfl

/-- The leading Laurent coefficient `a_0` equals the residue of `f` at `s`. -/
theorem meroPolarCoeffAt_zero_eq_residue {f : ℂ → ℂ} {s : ℂ}
    (hMero : MeromorphicAt f s) (h_pos : 0 < meroPolarOrderAt hMero) :
    meroPolarCoeffAt hMero ⟨0, h_pos⟩ = residue f s := by
  have h_data := mero_laurent_data_exists hMero
  set N := h_data.choose
  set a := h_data.choose_spec.choose
  set g := h_data.choose_spec.choose_spec.choose
  have hg_an : AnalyticAt ℂ g s := h_data.choose_spec.choose_spec.choose_spec.1
  have hf_eq : ∀ᶠ z in 𝓝[≠] s, f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) :=
    h_data.choose_spec.choose_spec.choose_spec.2
  have hN_pos : 0 < N := h_pos
  have hres := residue_of_laurent_expansion N a hg_an hf_eq
  rw [dif_pos hN_pos] at hres
  unfold meroPolarCoeffAt
  rw [hres]
  rfl

/-! ## The new constructor: `PolarPartDecomposition.ofMeromorphicWithCondB` -/

/-- The total polar part across all poles, using `MeromorphicAt` data
(uniform across crossed and uncrossed poles). -/
noncomputable def meroPolarPartTotal {S : Finset ℂ} {f : ℂ → ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, meroPolarPartAt (hMero s.1 s.2) z

/-- Local Laurent decomposition for the OTHER polar parts (not at `s`):
their sum is analytic at `s`. -/
private theorem mero_otherPolar_analyticAt {S : Finset ℂ} {f : ℂ → ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (_hs : s ∈ S) :
    AnalyticAt ℂ (fun z => ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
      meroPolarPartAt (hMero s'.1 s'.2) z) s := by
  refine Finset.analyticAt_fun_sum _ fun s' hs' => ?_
  have h_ne : s'.1 ≠ s := (Finset.mem_filter.mp hs').2
  exact meroPolarPartAt_analyticAt_off (hMero s'.1 s'.2) h_ne.symm

/-- **Local analytic decomposition near `s`** under `MeromorphicAt`:
`f - ∑_{s' ∈ S} polarPart_s' = analyticPart_s - ∑_{s' ≠ s} polarPart_s'`
is analytic at `s`. -/
private theorem mero_f_minus_total_eventuallyEq_analytic {S : Finset ℂ} {f : ℂ → ℂ}
    (hMero : ∀ s ∈ S, MeromorphicAt f s) {s : ℂ} (hs : s ∈ S) :
    ∃ g_s : ℂ → ℂ, AnalyticAt ℂ g_s s ∧
      ∀ᶠ z in 𝓝[≠] s, f z - meroPolarPartTotal hMero z = g_s z := by
  set g_s : ℂ → ℂ := fun z =>
    meroAnalyticPartAt (hMero s hs) z -
      ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
        meroPolarPartAt (hMero s'.1 s'.2) z with hg_s_def
  refine ⟨g_s, (meroAnalyticPartAt_analyticAt (hMero s hs)).sub
    (mero_otherPolar_analyticAt hMero hs), ?_⟩
  filter_upwards [mero_f_eq_analyticPart_plus_polarPart_eventually (hMero s hs)] with z hz
  rw [hg_s_def, hz]
  suffices h_total : meroPolarPartTotal hMero z =
      meroPolarPartAt (hMero s hs) z +
        ∑ s' ∈ S.attach.filter (fun s' => s'.1 ≠ s),
          meroPolarPartAt (hMero s'.1 s'.2) z by
    rw [h_total]
    ring
  unfold meroPolarPartTotal
  rw [show (∑ s' ∈ S.attach, meroPolarPartAt (hMero s'.1 s'.2) z) =
      (∑ s' ∈ S.attach.filter (fun s' => s'.1 = s),
        meroPolarPartAt (hMero s'.1 s'.2) z) +
      (∑ s' ∈ S.attach.filter (fun s' => ¬ s'.1 = s),
        meroPolarPartAt (hMero s'.1 s'.2) z) from
    (Finset.sum_filter_add_sum_filter_not S.attach _ _).symm]
  have h_singleton : S.attach.filter (fun s' => s'.1 = s) = {⟨s, hs⟩} := by
    ext s'
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
    refine ⟨fun h_eq => ?_, fun h_eq => ?_⟩
    · ext
      exact h_eq
    · rw [h_eq]
  rw [h_singleton, Finset.sum_singleton]

/-- **The new constructor: `PolarPartDecomposition.ofMeromorphicWithCondB`.**

Given:
- `U` open in `ℂ`, `S ⊆ U` finite,
- `f : ℂ → ℂ` differentiable on `U \ S`,
- `hMero : ∀ s ∈ S, MeromorphicAt f s` — meromorphicity at each pole,
- A piecewise-`C¹` immersion `γ` with `SatisfiesConditionB γ f S`,

we build a `PolarPartDecomposition f S U`. Unlike `ofConditionB`, this
constructor handles **both crossed and uncrossed** poles (no `hAllCrossed`
hypothesis), since for each pole `s` we extract Laurent data from the
`MeromorphicAt` hypothesis directly via `meromorphicOrderAt_ne_top_iff`.

The `hCondB` parameter is kept in the signature for use downstream (e.g. by
per-pole CPV dischargers that need the angle compatibility data); it is not
required by this constructor's body. -/
noncomputable def PolarPartDecomposition.ofMeromorphicWithCondB
    {U : Set ℂ} (hU_open : IsOpen U)
    {S : Finset ℂ} (_hS_in_U : ↑S ⊆ U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (U \ ↑S))
    {γ : PwC1Immersion x x}
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (_hCondB : SatisfiesConditionB γ f S) :
    PolarPartDecomposition f S U := by
  let polarPart : ℂ → ℂ → ℂ := fun s z =>
    if h_mem : s ∈ S then meroPolarPartAt (hMero s h_mem) z else 0
  let order : ℂ → ℕ := fun s =>
    if h_mem : s ∈ S then meroPolarOrderAt (hMero s h_mem) else 0
  let coeff : (s : ℂ) → Fin (order s) → ℂ := fun s k =>
    if h_mem : s ∈ S then
      meroPolarCoeffAt (hMero s h_mem) (Fin.cast (by simp [order, h_mem]) k)
    else by
      have h0 : order s = 0 := by simp [order, h_mem]
      exact absurd k.isLt (by omega)
  set rem : ℂ → ℂ := fun z => f z - meroPolarPartTotal hMero z with hrem_def
  set correction : ℂ → ℂ := fun z =>
    if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) rem else rem z with hcorr_def
  refine
    { polarPart := polarPart
      order := order
      coeff := coeff
      polarPart_eq := ?_
      residue_eq := ?_
      analyticRemainder := correction
      analyticRemainder_diff := ?_
      decomp := ?_ }
  · intro s hs z _hz
    have h_pp : polarPart s z = meroPolarPartAt (hMero s hs) z := by
      simp only [polarPart, hs, ↓reduceDIte]
    have h_order : order s = meroPolarOrderAt (hMero s hs) := by
      simp only [order, hs, ↓reduceDIte]
    rw [h_pp, meroPolarPartAt_eq_sum (hMero s hs) z, ← Fin.sum_congr'
      (fun k : Fin (meroPolarOrderAt (hMero s hs)) =>
        meroPolarCoeffAt (hMero s hs) k / (z - s) ^ (k.val + 1)) h_order]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    simp only [coeff, hs, ↓reduceDIte]
  · intro s hs
    have h_order : order s = meroPolarOrderAt (hMero s hs) := by
      simp only [order, hs, ↓reduceDIte]
    by_cases h_pos : 0 < order s
    · rw [dif_pos h_pos]
      have h_pos' : 0 < meroPolarOrderAt (hMero s hs) := h_order ▸ h_pos
      rw [← meroPolarCoeffAt_zero_eq_residue (hMero s hs) h_pos']
      change meroPolarCoeffAt (hMero s hs) ⟨0, h_pos'⟩ = coeff s ⟨0, h_pos⟩
      simp only [coeff, hs, ↓reduceDIte]
      rfl
    · rw [dif_neg h_pos]
      have h_order_zero : order s = 0 := by omega
      have h_zero : meroPolarOrderAt (hMero s hs) = 0 := by
        rw [← h_order]
        exact h_order_zero
      have h_data := mero_laurent_data_exists (hMero s hs)
      set N := h_data.choose
      set a := h_data.choose_spec.choose
      set g := h_data.choose_spec.choose_spec.choose
      have hg_an : AnalyticAt ℂ g s := h_data.choose_spec.choose_spec.choose_spec.1
      have hf_eq : ∀ᶠ z in 𝓝[≠] s,
          f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1) :=
        h_data.choose_spec.choose_spec.choose_spec.2
      have hN_zero : N = 0 := h_zero
      have hres := residue_of_laurent_expansion N a hg_an hf_eq
      rw [dif_neg (by omega)] at hres
      exact hres
  · intro z hzU
    by_cases hzS : z ∈ (↑S : Set ℂ)
    · have hzS' := Finset.mem_coe.mp hzS
      obtain ⟨g_z, hg_z_an, hg_z_eq⟩ :=
        mero_f_minus_total_eventuallyEq_analytic hMero hzS'
      have h_corr_eq : (fun w => correction w) =ᶠ[𝓝 z] g_z := by
        have h_lim_eq : limUnder (𝓝[≠] z) rem = g_z z :=
          (hg_z_an.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
            |>.congr' (hg_z_eq.mono fun _ h => h.symm)).limUnder_eq
        have h_at_z : correction z = g_z z := by
          change (if z ∈ (↑S : Set ℂ) then limUnder (𝓝[≠] z) rem else rem z) = g_z z
          rw [if_pos hzS, h_lim_eq]
        have hz_not_erase : z ∉ (↑(S.erase z) : Set ℂ) := fun hmem =>
          (Finset.mem_erase.mp (Finset.mem_coe.mp hmem)).1 rfl
        obtain ⟨V, hV_open, hz_V, hV_eq⟩ := mem_nhdsWithin.mp hg_z_eq
        have h_erase_away : (↑(S.erase z) : Set ℂ)ᶜ ∈ 𝓝 z :=
          (S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds hz_not_erase
        apply Filter.mem_of_superset (Filter.inter_mem (hV_open.mem_nhds hz_V) h_erase_away)
        intro w ⟨hw_V, hw_erase⟩
        change correction w = g_z w
        by_cases hwz : w = z
        · rw [hwz, h_at_z]
        · have hw_not_S : w ∉ (↑S : Set ℂ) := fun hmem => hw_erase
            (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwz, Finset.mem_coe.mp hmem⟩))
          change (if w ∈ (↑S : Set ℂ) then _ else rem w) = g_z w
          rw [if_neg hw_not_S]
          exact hV_eq ⟨hw_V, hwz⟩
      exact (hg_z_an.differentiableAt.congr_of_eventuallyEq h_corr_eq).differentiableWithinAt
    · have h_U_minus_S := hU_open.sdiff S.finite_toSet.isClosed
      have hzU_S : z ∈ U \ (↑S : Set ℂ) := ⟨hzU, hzS⟩
      have h_f_diff : DifferentiableAt ℂ f z :=
        (hf z hzU_S).differentiableAt (h_U_minus_S.mem_nhds hzU_S)
      have h_total_diff : DifferentiableAt ℂ (meroPolarPartTotal hMero) z := by
        unfold meroPolarPartTotal
        refine DifferentiableAt.fun_sum fun s' _ => ?_
        refine meroPolarPartAt_differentiableAt (hMero s'.1 s'.2) fun h_eq => ?_
        exact hzS (h_eq ▸ Finset.mem_coe.mpr s'.2)
      have h_corr_eq : (fun w => correction w) =ᶠ[𝓝 z] rem := by
        apply Filter.mem_of_superset (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
        intro w hw
        change (if w ∈ (↑S : Set ℂ) then _ else rem w) = rem w
        rw [if_neg hw]
      exact ((h_f_diff.sub h_total_diff).congr_of_eventuallyEq h_corr_eq).differentiableWithinAt
  · intro z ⟨_, hzS⟩
    have h_corr : correction z = rem z := by simp only [hcorr_def, hzS, ↓reduceIte]
    have h_rem : rem z = f z - meroPolarPartTotal hMero z := by simp only [hrem_def]
    have h_total : meroPolarPartTotal hMero z = ∑ s ∈ S, polarPart s z := by
      unfold meroPolarPartTotal
      rw [show ∑ s ∈ S, polarPart s z = ∑ s' ∈ S.attach, polarPart s'.1 z from
        (Finset.sum_attach S _).symm]
      refine Finset.sum_congr rfl fun s' _ => ?_
      simp only [polarPart, s'.2, ↓reduceDIte]
    change f z = correction z + ∑ s ∈ S, polarPart s z
    rw [h_corr, h_rem, h_total]
    ring

end HungerbuhlerWasem

end
