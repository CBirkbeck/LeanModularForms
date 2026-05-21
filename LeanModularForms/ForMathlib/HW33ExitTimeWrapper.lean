/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HigherOrderCancel
import LeanModularForms.ForMathlib.ExitTime

/-!
# HW Theorem 3.3 — odd transverse case via bundled exit-time data

This file provides the **plug-in form** of `hw_theorem_3_3_odd_transverse_parametric`
using the `HW33ExitData` bundle from `ExitTime.lean`. The parametric theorem
takes four hypotheses on `t_eps_plus` / `t_eps_minus` (Tendsto + radius equality
on each side); the bundled form takes a single `HW33ExitData` value.

## Main results

* `hw_theorem_3_3_odd_transverse_bundled`: the parametric theorem with the four
  exit-time hypotheses unpacked from a `HW33ExitData` value.

* `hw_theorem_3_3_odd_transverse_concrete`: the **fully concrete** form using
  `firstExitTimeRight` and `firstExitTimeLeft` directly. The user supplies the
  curve smoothness / integrability hypotheses on the punctured interval, plus
  the local "γ leaves `s`" hypothesis on each side, and obtains the
  CPV → 0 conclusion.

These are the intended user-facing forms of HW Theorem 3.3 (k odd transverse).
-/

open Filter Topology
open scoped Real

namespace LeanModularForms

variable {γ γ' : ℝ → ℂ} {a b t₀ : ℝ} {s L : ℂ} {n k : ℕ}

/-- **HW Theorem 3.3 — odd transverse, bundled form.** Same as
`hw_theorem_3_3_odd_transverse_parametric`, but the four asymptotic hypotheses
on the exit-time functions are packaged into a single `HW33ExitData` value. -/
theorem hw_theorem_3_3_odd_transverse_bundled
    (h_close : γ a = γ b)
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (data : HW33ExitData γ t₀ s)
    (h_minus_smooth : ∀ ε > 0, ∀ t ∈ Set.uIcc a (data.tMinus ε), HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ ε > 0, ∀ t ∈ Set.uIcc a (data.tMinus ε), γ t ≠ s)
    (h_minus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume a (data.tMinus ε))
    (h_plus_smooth : ∀ ε > 0, ∀ t ∈ Set.uIcc (data.tPlus ε) b, HasDerivAt γ (γ' t) t)
    (h_plus_avoids : ∀ ε > 0, ∀ t ∈ Set.uIcc (data.tPlus ε) b, γ t ≠ s)
    (h_plus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume (data.tPlus ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(data.tMinus ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (data.tPlus ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  hw_theorem_3_3_odd_transverse_parametric
    h_close h_flat hL h_deriv_right h_deriv_left hL_right hL_left
    h_s hk hk_odd hkn hn1
    data.tPlus data.tMinus
    data.plus_to data.plus_radius data.minus_to data.minus_radius
    h_minus_smooth h_minus_avoids h_minus_int
    h_plus_smooth h_plus_avoids h_plus_int

/-- **HW Theorem 3.3 — odd transverse, fully concrete form.** Uses
`firstExitTimeRight` and `firstExitTimeLeft` directly. The user supplies:

* The crossing data: γ flat of order n, derivative L ≠ 0 from each side, and
  γ(t₀) = s, with k odd ∈ [2, n].
* Continuity of γ on `[t₀ - δMinus, t₀ + δPlus]`.
* The "γ leaves `s` away from `t₀`" hypothesis on each side.
* The smoothness / avoidance / integrability hypotheses on the punctured
  outer intervals (these are already needed for the Phase 3 PV theorem).

The conclusion is the CPV vanishing as ε → 0⁺. -/
theorem hw_theorem_3_3_odd_transverse_concrete
    {δPlus δMinus : ℝ} (hδPlus : 0 < δPlus) (hδMinus : 0 < δMinus)
    (h_close : γ a = γ b)
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (hγ_cont_right : ContinuousOn γ (Set.Icc t₀ (t₀ + δPlus)))
    (hγ_cont_left : ContinuousOn γ (Set.Icc (t₀ - δMinus) t₀))
    (h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + δPlus), γ t ≠ s)
    (h_leave_left : ∀ t ∈ Set.Ico (t₀ - δMinus) t₀, γ t ≠ s)
    (h_minus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc a (firstExitTimeLeft γ t₀ δMinus s ε), HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc a (firstExitTimeLeft γ t₀ δMinus s ε), γ t ≠ s)
    (h_minus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume a (firstExitTimeLeft γ t₀ δMinus s ε))
    (h_plus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (firstExitTimeRight γ t₀ δPlus s ε) b, HasDerivAt γ (γ' t) t)
    (h_plus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (firstExitTimeRight γ t₀ δPlus s ε) b, γ t ≠ s)
    (h_plus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume (firstExitTimeRight γ t₀ δPlus s ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(firstExitTimeLeft γ t₀ δMinus s ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (firstExitTimeRight γ t₀ δPlus s ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  hw_theorem_3_3_odd_transverse_bundled
    h_close h_flat hL h_deriv_right h_deriv_left hL_right hL_left
    h_s hk hk_odd hkn hn1
    (HW33ExitData.ofExitTimes hδPlus hδMinus
      hγ_cont_right hγ_cont_left h_s h_leave_right h_leave_left)
    h_minus_smooth h_minus_avoids h_minus_int
    h_plus_smooth h_plus_avoids h_plus_int

end LeanModularForms
