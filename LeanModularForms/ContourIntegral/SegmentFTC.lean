/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.LogDerivFTC
import Mathlib

/-!
# Telescoping FTC for Log-Derivative on Piecewise Segments

When FTC-for-log is applied to consecutive segments sharing endpoints,
the log terms telescope. For a closed curve split at a crossing t₀ ± δ,
the total integral reduces to log(g(t₀-δ)) - log(g(t₀+δ)).

## Main results

* `ftc_telescope_two` — FTC on two consecutive segments telescopes
* `ftc_telescope_closed_split` — for closed curves, the full integral telescopes
  to the log difference at the crossing boundary
-/

open Set MeasureTheory Complex
open scoped Interval

namespace ContourIntegral

/-- FTC on two consecutive segments telescopes: if the integral over [a,b] is
log(f b) - log(f a) and the integral over [b,c] is log(f c) - log(f b),
then the integral over [a,c] is log(f c) - log(f a). -/
theorem ftc_telescope_two {f : ℝ → ℂ} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hint_ab : IntervalIntegrable (fun t => deriv f t / f t) volume a b)
    (hint_bc : IntervalIntegrable (fun t => deriv f t / f t) volume b c)
    (h_ab : ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a))
    (h_bc : ∫ t in b..c, deriv f t / f t = Complex.log (f c) - Complex.log (f b)) :
    ∫ t in a..c, deriv f t / f t = Complex.log (f c) - Complex.log (f a) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals hint_ab hint_bc, h_ab, h_bc]
  ring

/-- For a closed curve (f a = f b), the integral from a to (t₀ - δ) plus from
(t₀ + δ) to b telescopes to log(f(t₀ - δ)) - log(f(t₀ + δ)), because the log
terms at a and b cancel by closedness. -/
theorem ftc_telescope_closed_split {f : ℝ → ℂ} {a b t₀ δ : ℝ}
    (h_closed : f a = f b)
    (hint_left : IntervalIntegrable (fun t => deriv f t / f t) volume a (t₀ - δ))
    (hint_right : IntervalIntegrable (fun t => deriv f t / f t) volume (t₀ + δ) b)
    (h_left : ∫ t in a..(t₀ - δ), deriv f t / f t =
      Complex.log (f (t₀ - δ)) - Complex.log (f a))
    (h_right : ∫ t in (t₀ + δ)..b, deriv f t / f t =
      Complex.log (f b) - Complex.log (f (t₀ + δ))) :
    (∫ t in a..(t₀ - δ), deriv f t / f t) + (∫ t in (t₀ + δ)..b, deriv f t / f t) =
    Complex.log (f (t₀ - δ)) - Complex.log (f (t₀ + δ)) := by
  rw [h_left, h_right, ← h_closed]
  ring

end ContourIntegral
