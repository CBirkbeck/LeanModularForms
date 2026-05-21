/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.HungerbuhlerWasem.ExitTimeExcision
import LeanModularForms.ForMathlib.HW33ExitTimeWrapper

/-!
# HW Theorem 3.3 — assembled single-pole closure (`HasCauchyPVOn` form)

This file packages the full HW 3.3 closure for the `k`-odd transverse case at a
single pole into the `HasCauchyPVOn` form, composing the parametric
symmetric-excision PV, the eventual shape from
`HungerbuhlerWasem.ExitTimeExcision`, and the bridge
`hasCauchyPVOn_singleton_of_exitTime_excision`.

## Main results

* `hasCauchyPVOn_singleton_pow_of_transverse_assembled`: the assembled
  `HasCauchyPVOn` closure at a single transverse pole.
-/

open Filter Topology Set Complex MeasureTheory HungerbuhlerWasem

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **HW Theorem 3.3 — k-odd transverse case (single pole, `HasCauchyPVOn` form).**

For a closed Lipschitz `γ : PiecewiseC1Path x x` with a single transverse
crossing at `t₀ ∈ (0, 1)` of pole `s`, where `γ' (t₀) = L ≠ 0` from both sides,
γ is flat of order `n ≥ k` (with `k` odd), strict (anti-)monotonicity of
`‖γ - s‖` near `t₀`, and avoidance margins / integrability outside, the CPV
along γ vanishes:

  `HasCauchyPVOn {s} (fun z => 1 / (z - s)^k) γ 0`.

This is the **fully assembled HW 3.3 closure for the k-odd transverse case**
in the `HasCauchyPVOn` form, composing:

* `hw_theorem_3_3_odd_transverse_concrete` (parametric symmetric-excision PV)
* `shape_eventually_of_strict_mono` (shape hypothesis)
* `hasCauchyPVOn_singleton_of_exitTime_excision` (bridge to `HasCauchyPVOn`).

All lower-level machinery (exit times, strict mono from transverse, integral
splitting under shape) closes cleanly with no new sorries.

The strict (anti-)monotonicity hypotheses can be derived from the more basic
transverse data via `exists_strictMonoOn_norm_right_of_transverse` and
`exists_strictAntiOn_norm_left_of_transverse` from `HW33Monotonicity.lean`. -/
theorem hasCauchyPVOn_singleton_pow_of_transverse_assembled
    {γ : PiecewiseC1Path x x} {s L : ℂ}
    {t₀ δMinus δPlus : ℝ} {n k : ℕ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδMinus : 0 < δMinus) (hδPlus : 0 < δPlus)
    (h_close : γ.toPath.extend 0 = γ.toPath.extend 1)
    (h_flat : IsFlatOfOrder γ.toPath.extend t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ.toPath.extend L (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ.toPath.extend L (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ.toPath.extend) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ.toPath.extend) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ.toPath.extend t₀ = s)
    (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (hγ_cont_right : ContinuousOn γ.toPath.extend (Set.Icc t₀ (t₀ + δPlus)))
    (hγ_cont_left : ContinuousOn γ.toPath.extend (Set.Icc (t₀ - δMinus) t₀))
    (h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + δPlus), γ.toPath.extend t ≠ s)
    (h_leave_left : ∀ t ∈ Set.Ico (t₀ - δMinus) t₀, γ.toPath.extend t ≠ s)
    (hγ_anti : StrictAntiOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc (t₀ - δMinus) t₀))
    (hγ_mono : StrictMonoOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc t₀ (t₀ + δPlus)))
    {δ_avoid_left δ_avoid_right : ℝ}
    (h_avoid_left_pos : 0 < δ_avoid_left)
    (h_avoid_right_pos : 0 < δ_avoid_right)
    (h_avoid_left : ∀ t ∈ Set.Icc (0 : ℝ) (t₀ - δMinus),
      δ_avoid_left ≤ ‖γ.toPath.extend t - s‖)
    (h_avoid_right : ∀ t ∈ Set.Icc (t₀ + δPlus) (1 : ℝ),
      δ_avoid_right ≤ ‖γ.toPath.extend t - s‖)
    (h_minus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_minus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      γ.toPath.extend t ≠ s)
    (h_minus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume 0
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε))
    (h_plus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_plus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      γ.toPath.extend t ≠ s)
    (h_plus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ))
    (h_int_full : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn {s}
        (fun z => (1 : ℂ) / (z - s) ^ k) γ.toPath.extend ε t)
      MeasureTheory.volume 0 1) :
    HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0 :=
  hasCauchyPVOn_singleton_of_exitTime_excision γ s
    (fun z => (1 : ℂ) / (z - s) ^ k)
    (shape_eventually_of_strict_mono h_t₀_minus_pos h_t₀_plus_le hδMinus hδPlus
      hγ_cont_left hγ_cont_right hγ_anti hγ_mono h_s
      h_avoid_left_pos h_avoid_right_pos h_avoid_left h_avoid_right) h_int_full
    ((hw_theorem_3_3_odd_transverse_concrete (γ := γ.toPath.extend)
      (γ' := deriv γ.toPath.extend) (s := s) (L := L) (n := n) (k := k)
      (a := 0) (b := 1) (t₀ := t₀) (δMinus := δMinus) (δPlus := δPlus)
      hδPlus hδMinus h_close h_flat hL h_deriv_right h_deriv_left
      hL_right hL_left h_s hk hk_odd hkn hn1
      hγ_cont_right hγ_cont_left h_leave_right h_leave_left
      h_minus_smooth h_minus_avoids h_minus_int
      h_plus_smooth h_plus_avoids h_plus_int).congr fun ε => by
        congr 1 <;> exact intervalIntegral.integral_congr fun t _ => by ring)

end LeanModularForms

end
