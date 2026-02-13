/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions

/-!
# Cusp Height Infrastructure — Existential Nonvanishing Radius

For a nonzero modular form `f`, the cusp function `F(q) = cuspFunction 1 f q` is
analytic at `q = 0` and not identically zero. Therefore its zeros near 0 are isolated,
and there exists a radius `r > 0` such that `F` is nonvanishing on `closedBall(0, r) \ {0}`.

This file provides:
* `cuspFunction_not_identically_zero` — the cusp function of a nonzero modular form
  is not identically zero near 0.
* `exists_radius_cusp_nonvanishing` — existence of a nonvanishing radius.
* `heightOfRadius` — converts a q-radius to a boundary height.
* `exists_height_cusp_nonvanishing` — existence of a height `H > √3/2` with
  cusp nonvanishing.

## Proof Strategy

1. `cuspFunction 1 f` is analytic at 0 (Mathlib: `analyticAt_cuspFunction_zero`).
2. If `cuspFunction 1 f ≡ 0` near 0, then `f(τ) = 0` for `Im(τ)` large (via
   `eq_cuspFunction`), hence `f ≡ 0` on ℍ by the identity principle. Contradiction.
3. By `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, the cusp function is
   eventually nonzero in `𝓝[≠] 0`.
4. Extract a metric ball from the `Eventually` filter.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

noncomputable section

/-- The cusp function of a nonzero modular form is not identically zero near 0.
Proof: if F ≡ 0 near 0, then f(τ) = F(q(τ)) = 0 for Im(τ) large, hence f ≡ 0
by the identity principle on the connected upper half-plane. -/
theorem cuspFunction_not_eventually_zero {k : ℤ} (f : ModularForm (Gamma 1) k)
    (hf : f ≠ 0) :
    ¬∀ᶠ q in 𝓝 (0 : ℂ), SlashInvariantFormClass.cuspFunction (1 : ℕ) f q = 0 := by
  intro h_freq
  -- The cusp function is analytic on the open unit disk
  have h_diff : DifferentiableOn ℂ (SlashInvariantFormClass.cuspFunction (1 : ℕ) f)
      (Metric.ball 0 1) := fun q hq =>
    (ModularFormClass.differentiableAt_cuspFunction (n := 1) (f := f)
      (by rwa [Metric.mem_ball, dist_zero_right] at hq)).differentiableWithinAt
  have h_anal : AnalyticOnNhd ℂ (SlashInvariantFormClass.cuspFunction (1 : ℕ) f)
      (Metric.ball 0 1) := h_diff.analyticOnNhd Metric.isOpen_ball
  -- By the identity principle, it's zero on the entire open unit disk
  have h_eqOn : EqOn (SlashInvariantFormClass.cuspFunction (1 : ℕ) f) 0 (Metric.ball 0 1) :=
    h_anal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball 0 1).isPreconnected (Metric.mem_ball_self (by norm_num : (0:ℝ) < 1)) h_freq
  -- For any τ ∈ ℍ, qParam 1 τ ∈ ball(0, 1), so cuspFunction(qParam 1 τ) = 0
  -- Since cuspFunction(qParam 1 τ) = f(τ), we get f(τ) = 0 for all τ
  apply hf; ext τ
  simp only [ModularForm.coe_zero, Pi.zero_apply]
  have h_eq := SlashInvariantFormClass.eq_cuspFunction (1 : ℕ) f τ
  rw [← h_eq]
  have h_qmem : Function.Periodic.qParam (↑(1 : ℕ)) (↑τ : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact UpperHalfPlane.norm_qParam_lt_one 1 τ
  exact h_eqOn h_qmem

/-- For a nonzero modular form, the cusp function is eventually nonzero
in a punctured neighborhood of 0. -/
theorem cuspFunction_eventually_ne_zero {k : ℤ} (f : ModularForm (Gamma 1) k)
    (hf : f ≠ 0) :
    ∀ᶠ q in 𝓝[≠] (0 : ℂ),
      SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0 := by
  have h_anal : AnalyticAt ℂ (SlashInvariantFormClass.cuspFunction (1 : ℕ) f) 0 :=
    ModularFormClass.analyticAt_cuspFunction_zero (n := 1) (f := f)
  rcases h_anal.eventually_eq_zero_or_eventually_ne_zero with h_zero | h_ne
  · exact absurd h_zero (cuspFunction_not_eventually_zero f hf)
  · exact h_ne

/-- For a nonzero modular form, there exists `r > 0` such that the cusp function
is nonvanishing on the punctured ball `ball(0, r) \ {0}`. -/
theorem exists_radius_cusp_nonvanishing {k : ℤ} (f : ModularForm (Gamma 1) k)
    (hf : f ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ q : ℂ, q ∈ Metric.closedBall (0 : ℂ) r →
      q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0 := by
  -- Extract a ball from the eventually-nonzero filter
  have h_ev := cuspFunction_eventually_ne_zero f hf
  rw [eventually_nhdsWithin_iff] at h_ev
  obtain ⟨s, hs_prop, hs_open, hs_zero⟩ := eventually_nhds_iff.mp h_ev
  -- s is a neighborhood of 0, so it contains a ball
  obtain ⟨r, hr_pos, hr_ball⟩ := Metric.isOpen_iff.mp hs_open 0 hs_zero
  -- Use r/2 for the closed ball
  refine ⟨r / 2, by linarith, fun q hq hq_ne => ?_⟩
  have hq_dist : dist q 0 < r := by
    calc dist q 0 ≤ r / 2 := Metric.mem_closedBall.mp hq
    _ < r := by linarith
  exact hs_prop q (hr_ball hq_dist) (Set.mem_compl_singleton_iff.mpr hq_ne)

/-- Convert a q-radius to a FD boundary height: if `|q| = e^{-2πH}`,
then `H = -log(r) / (2π)`. -/
noncomputable def heightOfRadius (r : ℝ) : ℝ := -Real.log r / (2 * Real.pi)

lemma heightOfRadius_pos_of_lt_one {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    0 < heightOfRadius r := by
  unfold heightOfRadius
  have h_log_neg : Real.log r < 0 := Real.log_neg hr hr1
  have h_pi_pos : 0 < 2 * Real.pi := by positivity
  exact div_pos (neg_pos.mpr h_log_neg) h_pi_pos

/-- For a nonzero modular form, there exists `H > √3/2` such that the cusp function
is nonvanishing on `closedBall(0, e^{-2πH}) \ {0}`. This is the height at which
the FD boundary should be placed. -/
theorem exists_height_cusp_nonvanishing {k : ℤ} (f : ModularForm (Gamma 1) k)
    (hf : f ≠ 0) :
    ∃ H : ℝ, Real.sqrt 3 / 2 < H ∧
      ∀ q : ℂ, q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H)) →
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0 := by
  obtain ⟨r, hr_pos, hr_nonvan⟩ := exists_radius_cusp_nonvanishing f hf
  -- Choose H = max(heightOfRadius r, √3/2 + 1) to ensure H > √3/2
  -- and the q-circle at height H fits inside the nonvanishing ball
  let H₀ := max (heightOfRadius r) (Real.sqrt 3 / 2 + 1)
  refine ⟨H₀, ?_, ?_⟩
  · calc Real.sqrt 3 / 2 < Real.sqrt 3 / 2 + 1 := by linarith
      _ ≤ H₀ := le_max_right _ _
  · intro q hq hq_ne
    apply hr_nonvan q _ hq_ne
    -- Need: closedBall(0, exp(-2πH₀)) ⊆ closedBall(0, r)
    -- i.e., exp(-2πH₀) ≤ r
    -- Since H₀ ≥ heightOfRadius r = -log(r)/(2π), we have
    -- -2πH₀ ≤ -2π·(-log(r)/(2π)) = log(r), so exp(-2πH₀) ≤ exp(log(r)) = r
    apply Metric.closedBall_subset_closedBall _ hq
    have hH₀_ge : heightOfRadius r ≤ H₀ := le_max_left _ _
    have h_pi_pos : 0 < Real.pi := Real.pi_pos
    have h_exp_mono : Real.exp (-2 * Real.pi * H₀) ≤ Real.exp (-2 * Real.pi * heightOfRadius r) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    calc Real.exp (-2 * Real.pi * H₀)
        ≤ Real.exp (-2 * Real.pi * heightOfRadius r) := h_exp_mono
      _ = r := by
          rw [show -2 * Real.pi * heightOfRadius r = Real.log r from by
            unfold heightOfRadius; field_simp]
          exact Real.exp_log hr_pos

/-! ## Monotonicity Infrastructure -/

/-- Radius monotonicity: nonvanishing on `closedBall(0, r₁)` implies nonvanishing on
any smaller `closedBall(0, r₂)` with `r₂ ≤ r₁`. -/
lemma cusp_nonvanishing_closedBall_mono {k : ℤ} (f : ModularForm (Gamma 1) k)
    {r₁ r₂ : ℝ} (hr : r₂ ≤ r₁)
    (h : ∀ q ∈ Metric.closedBall (0 : ℂ) r₁, q ≠ 0 →
      SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∀ q ∈ Metric.closedBall (0 : ℂ) r₂, q ≠ 0 →
      SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0 :=
  fun q hq hq_ne => h q (Metric.closedBall_subset_closedBall hr hq) hq_ne

/-- Height monotonicity: if `H₁ ≤ H₂` then `exp(-2πH₂) ≤ exp(-2πH₁)`, so
nonvanishing at height `H₁` implies nonvanishing at any higher `H₂`. -/
lemma cusp_nonvanishing_height_mono {k : ℤ} (f : ModularForm (Gamma 1) k)
    {H₁ H₂ : ℝ} (hH : H₁ ≤ H₂)
    (h : ∀ q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H₁)), q ≠ 0 →
      SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∀ q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H₂)), q ≠ 0 →
      SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0 :=
  cusp_nonvanishing_closedBall_mono f (Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])) h

/-- Existence above arbitrary floor: for any `Hmin`, there exists `H ≥ Hmin` (and `H > √3/2`)
with cusp nonvanishing on the corresponding q-circle. -/
theorem exists_height_cusp_nonvanishing_above {k : ℤ} (f : ModularForm (Gamma 1) k)
    (hf : f ≠ 0) (Hmin : ℝ) :
    ∃ H : ℝ, Hmin ≤ H ∧ Real.sqrt 3 / 2 < H ∧
      ∀ q : ℂ, q ∈ Metric.closedBall (0 : ℂ) (Real.exp (-2 * Real.pi * H)) →
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0 := by
  obtain ⟨H₀, hH₀_gt, hH₀_nonvan⟩ := exists_height_cusp_nonvanishing f hf
  exact ⟨max H₀ Hmin, le_max_right _ _, lt_of_lt_of_le hH₀_gt (le_max_left _ _),
    cusp_nonvanishing_height_mono f (le_max_left _ _) hH₀_nonvan⟩

end
