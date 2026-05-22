/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib
import LeanModularForms.ForMathlib.SegmentFTC

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
    (hint_ab : IntervalIntegrable (fun t => deriv f t / f t) volume a b)
    (hint_bc : IntervalIntegrable (fun t => deriv f t / f t) volume b c)
    (h_ab : ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a))
    (h_bc : ∫ t in b..c, deriv f t / f t = Complex.log (f c) - Complex.log (f b)) :
    ∫ t in a..c, deriv f t / f t = Complex.log (f c) - Complex.log (f a) := by
  simp [← intervalIntegral.integral_add_adjacent_intervals hint_ab hint_bc, h_ab, h_bc]

/-- For a closed curve (f a = f b), the integral from a to (t₀ - δ) plus from
(t₀ + δ) to b telescopes to log(f(t₀ - δ)) - log(f(t₀ + δ)), because the log
terms at a and b cancel by closedness. -/
theorem ftc_telescope_closed_split {f : ℝ → ℂ} {a b t₀ δ : ℝ} (h_closed : f a = f b)
    (h_left : ∫ t in a..(t₀ - δ), deriv f t / f t =
      Complex.log (f (t₀ - δ)) - Complex.log (f a))
    (h_right : ∫ t in (t₀ + δ)..b, deriv f t / f t =
      Complex.log (f b) - Complex.log (f (t₀ + δ))) :
    (∫ t in a..(t₀ - δ), deriv f t / f t) + (∫ t in (t₀ + δ)..b, deriv f t / f t) =
    Complex.log (f (t₀ - δ)) - Complex.log (f (t₀ + δ)) := by
  simp [h_left, h_right, ← h_closed]

/-- FTC on three consecutive segments telescopes: the integral over [a,d] is
log(f d) - log(f a) if each sub-interval satisfies the FTC-for-log. -/
theorem ftc_telescope_three {f : ℝ → ℂ} {a b c d : ℝ}
    (hint_ab : IntervalIntegrable (fun t => deriv f t / f t) volume a b)
    (hint_bc : IntervalIntegrable (fun t => deriv f t / f t) volume b c)
    (hint_cd : IntervalIntegrable (fun t => deriv f t / f t) volume c d)
    (h_ab : ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a))
    (h_bc : ∫ t in b..c, deriv f t / f t = Complex.log (f c) - Complex.log (f b))
    (h_cd : ∫ t in c..d, deriv f t / f t = Complex.log (f d) - Complex.log (f c)) :
    ∫ t in a..d, deriv f t / f t = Complex.log (f d) - Complex.log (f a) := by
  simp [← intervalIntegral.integral_add_adjacent_intervals (hint_ab.trans hint_bc) hint_cd,
    ← intervalIntegral.integral_add_adjacent_intervals hint_ab hint_bc, h_ab, h_bc, h_cd]

/-- Transfer integrability from a local function `h` to `g` given that their
log-derivatives agree almost everywhere on the interval.  The `h_ae` hypothesis
has the direction `deriv g / g = deriv h / h` pointwise a.e., which is reversed
internally to match the `congr_ae` requirement. -/
theorem ftc_telescope_integrability {g h : ℝ → ℂ} {a b : ℝ}
    (hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b)
    (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b :=
  hint_h.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr
    (h_ae.mono (fun _t ht hm => (ht hm).symm)))

/-- Transfer an FTC result from a local function `h` to `g` given that their
log-derivatives agree a.e. and their values agree at the endpoints.
Produces both integrability and the FTC equality for `g`. -/
theorem ftc_telescope_transfer {g h : ℝ → ℂ} {a b : ℝ}
    (hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b)
    (h_ftc : ∫ t in a..b, deriv h t / h t = Complex.log (h b) - Complex.log (h a))
    (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t)
    (h_ga : g a = h a) (h_gb : g b = h b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  refine ⟨ftc_telescope_integrability hint_h h_ae, ?_⟩
  rw [intervalIntegral.integral_congr_ae h_ae, h_ftc, h_ga, h_gb]

/-- General piecewise FTC telescope for a function `g` on `[a, b]` that is split at a
single interior breakpoint `p`.  Given FTC results on `[a, p]` and `[p, b]` for local
functions `h₁` and `h₂` respectively, together with a.e. agreement of log-derivatives
and matching endpoints, the combined integral telescopes to `log(g b) - log(g a)`. -/
theorem ftc_telescope_piecewise_two {g h₁ h₂ : ℝ → ℂ} {a p b : ℝ}
    (hint₁ : IntervalIntegrable (fun t => deriv h₁ t / h₁ t) volume a p)
    (hint₂ : IntervalIntegrable (fun t => deriv h₂ t / h₂ t) volume p b)
    (h_ftc₁ : ∫ t in a..p, deriv h₁ t / h₁ t = Complex.log (h₁ p) - Complex.log (h₁ a))
    (h_ftc₂ : ∫ t in p..b, deriv h₂ t / h₂ t = Complex.log (h₂ b) - Complex.log (h₂ p))
    (h_ae₁ : ∀ᵐ t ∂volume, t ∈ Ι a p → deriv g t / g t = deriv h₁ t / h₁ t)
    (h_ae₂ : ∀ᵐ t ∂volume, t ∈ Ι p b → deriv g t / g t = deriv h₂ t / h₂ t)
    (h_ga : g a = h₁ a) (h_gp_left : g p = h₁ p) (h_gp_right : g p = h₂ p)
    (h_gb : g b = h₂ b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hint_g₁ := ftc_telescope_integrability hint₁ h_ae₁
  have hint_g₂ := ftc_telescope_integrability hint₂ h_ae₂
  have h_eq₁ : ∫ t in a..p, deriv g t / g t = Complex.log (g p) - Complex.log (g a) := by
    rw [intervalIntegral.integral_congr_ae h_ae₁, h_ftc₁, h_ga, h_gp_left]
  have h_eq₂ : ∫ t in p..b, deriv g t / g t = Complex.log (g b) - Complex.log (g p) := by
    rw [intervalIntegral.integral_congr_ae h_ae₂, h_ftc₂, h_gp_right, h_gb]
  exact ⟨hint_g₁.trans hint_g₂, ftc_telescope_two hint_g₁ hint_g₂ h_eq₁ h_eq₂⟩

/-- Piecewise FTC telescope with three local functions (two interior breakpoints). -/
theorem ftc_telescope_piecewise_three {g h₁ h₂ h₃ : ℝ → ℂ} {a p q b : ℝ}
    (hint₁ : IntervalIntegrable (fun t => deriv h₁ t / h₁ t) volume a p)
    (hint₂ : IntervalIntegrable (fun t => deriv h₂ t / h₂ t) volume p q)
    (hint₃ : IntervalIntegrable (fun t => deriv h₃ t / h₃ t) volume q b)
    (h_ftc₁ : ∫ t in a..p, deriv h₁ t / h₁ t = Complex.log (h₁ p) - Complex.log (h₁ a))
    (h_ftc₂ : ∫ t in p..q, deriv h₂ t / h₂ t = Complex.log (h₂ q) - Complex.log (h₂ p))
    (h_ftc₃ : ∫ t in q..b, deriv h₃ t / h₃ t = Complex.log (h₃ b) - Complex.log (h₃ q))
    (h_ae₁ : ∀ᵐ t ∂volume, t ∈ Ι a p → deriv g t / g t = deriv h₁ t / h₁ t)
    (h_ae₂ : ∀ᵐ t ∂volume, t ∈ Ι p q → deriv g t / g t = deriv h₂ t / h₂ t)
    (h_ae₃ : ∀ᵐ t ∂volume, t ∈ Ι q b → deriv g t / g t = deriv h₃ t / h₃ t)
    (h_ga : g a = h₁ a) (h_gp : g p = h₁ p) (h_gp' : g p = h₂ p)
    (h_gq : g q = h₂ q) (h_gq' : g q = h₃ q) (h_gb : g b = h₃ b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧
    ∫ t in a..b, deriv g t / g t = Complex.log (g b) - Complex.log (g a) := by
  have hint_g₁ := ftc_telescope_integrability hint₁ h_ae₁
  have hint_g₂ := ftc_telescope_integrability hint₂ h_ae₂
  have hint_g₃ := ftc_telescope_integrability hint₃ h_ae₃
  have h_eq₁ : ∫ t in a..p, deriv g t / g t = Complex.log (g p) - Complex.log (g a) := by
    rw [intervalIntegral.integral_congr_ae h_ae₁, h_ftc₁, h_ga, h_gp]
  have h_eq₂ : ∫ t in p..q, deriv g t / g t = Complex.log (g q) - Complex.log (g p) := by
    rw [intervalIntegral.integral_congr_ae h_ae₂, h_ftc₂, h_gp', h_gq]
  have h_eq₃ : ∫ t in q..b, deriv g t / g t = Complex.log (g b) - Complex.log (g q) := by
    rw [intervalIntegral.integral_congr_ae h_ae₃, h_ftc₃, h_gq', h_gb]
  exact ⟨(hint_g₁.trans hint_g₂).trans hint_g₃,
    ftc_telescope_three hint_g₁ hint_g₂ hint_g₃ h_eq₁ h_eq₂ h_eq₃⟩

end ContourIntegral
