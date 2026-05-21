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

/-- For a closed curve with a crossing gap, the FTC telescopes across five piecewise
segments `[a, p₁], [p₁, p₂], [p₂, tₗ]` (left of gap) and `[tᵣ, p₃], [p₃, b]`
(right of gap).  Each segment has a local function satisfying FTC, and `g` agrees
a.e. with each.  The closed-curve condition `h₁ a = h₅ b` (implying `g a = g b`)
means the outer log terms cancel, telescoping to `log(g tₗ) - log(g tᵣ)`. -/
theorem ftc_telescope_closed_split_five
    {g h₁ h₂ h₃ h₄ h₅ : ℝ → ℂ} {a p₁ p₂ tₗ tᵣ p₃ b : ℝ}
    (hint₁ : IntervalIntegrable (fun t => deriv h₁ t / h₁ t) volume a p₁)
    (hint₂ : IntervalIntegrable (fun t => deriv h₂ t / h₂ t) volume p₁ p₂)
    (hint₃ : IntervalIntegrable (fun t => deriv h₃ t / h₃ t) volume p₂ tₗ)
    (hint₄ : IntervalIntegrable (fun t => deriv h₄ t / h₄ t) volume tᵣ p₃)
    (hint₅ : IntervalIntegrable (fun t => deriv h₅ t / h₅ t) volume p₃ b)
    (h_ftc₁ : ∫ t in a..p₁, deriv h₁ t / h₁ t = Complex.log (h₁ p₁) - Complex.log (h₁ a))
    (h_ftc₂ : ∫ t in p₁..p₂, deriv h₂ t / h₂ t = Complex.log (h₂ p₂) - Complex.log (h₂ p₁))
    (h_ftc₃ : ∫ t in p₂..tₗ, deriv h₃ t / h₃ t = Complex.log (h₃ tₗ) - Complex.log (h₃ p₂))
    (h_ftc₄ : ∫ t in tᵣ..p₃, deriv h₄ t / h₄ t = Complex.log (h₄ p₃) - Complex.log (h₄ tᵣ))
    (h_ftc₅ : ∫ t in p₃..b, deriv h₅ t / h₅ t = Complex.log (h₅ b) - Complex.log (h₅ p₃))
    (h_ae₁ : ∀ᵐ t ∂volume, t ∈ Ι a p₁ → deriv g t / g t = deriv h₁ t / h₁ t)
    (h_ae₂ : ∀ᵐ t ∂volume, t ∈ Ι p₁ p₂ → deriv g t / g t = deriv h₂ t / h₂ t)
    (h_ae₃ : ∀ᵐ t ∂volume, t ∈ Ι p₂ tₗ → deriv g t / g t = deriv h₃ t / h₃ t)
    (h_ae₄ : ∀ᵐ t ∂volume, t ∈ Ι tᵣ p₃ → deriv g t / g t = deriv h₄ t / h₄ t)
    (h_ae₅ : ∀ᵐ t ∂volume, t ∈ Ι p₃ b → deriv g t / g t = deriv h₅ t / h₅ t)
    (h_ga : g a = h₁ a) (h_gp₁ : g p₁ = h₁ p₁) (h_gp₁' : g p₁ = h₂ p₁)
    (h_gp₂ : g p₂ = h₂ p₂) (h_gp₂' : g p₂ = h₃ p₂)
    (h_gtₗ : g tₗ = h₃ tₗ) (h_gtᵣ : g tᵣ = h₄ tᵣ)
    (h_gp₃ : g p₃ = h₄ p₃) (h_gp₃' : g p₃ = h₅ p₃) (h_gb : g b = h₅ b)
    (h_closed : h₁ a = h₅ b) :
    IntervalIntegrable (fun t => deriv g t / g t) volume a tₗ ∧
    IntervalIntegrable (fun t => deriv g t / g t) volume tᵣ b ∧
    (∫ t in a..tₗ, deriv g t / g t) + (∫ t in tᵣ..b, deriv g t / g t) =
      Complex.log (g tₗ) - Complex.log (g tᵣ) := by
  have hint_g₁ := ftc_telescope_integrability hint₁ h_ae₁
  have hint_g₂ := ftc_telescope_integrability hint₂ h_ae₂
  have hint_g₃ := ftc_telescope_integrability hint₃ h_ae₃
  have hint_g₄ := ftc_telescope_integrability hint₄ h_ae₄
  have hint_g₅ := ftc_telescope_integrability hint₅ h_ae₅
  have h_eq₁ : ∫ t in a..p₁, deriv g t / g t = Complex.log (g p₁) - Complex.log (g a) := by
    rw [intervalIntegral.integral_congr_ae h_ae₁, h_ftc₁, h_ga, h_gp₁]
  have h_eq₂ : ∫ t in p₁..p₂, deriv g t / g t = Complex.log (g p₂) - Complex.log (g p₁) := by
    rw [intervalIntegral.integral_congr_ae h_ae₂, h_ftc₂, h_gp₁', h_gp₂]
  have h_eq₃ : ∫ t in p₂..tₗ, deriv g t / g t = Complex.log (g tₗ) - Complex.log (g p₂) := by
    rw [intervalIntegral.integral_congr_ae h_ae₃, h_ftc₃, h_gp₂', h_gtₗ]
  have h_eq₄ : ∫ t in tᵣ..p₃, deriv g t / g t = Complex.log (g p₃) - Complex.log (g tᵣ) := by
    rw [intervalIntegral.integral_congr_ae h_ae₄, h_ftc₄, h_gtᵣ, h_gp₃]
  have h_eq₅ : ∫ t in p₃..b, deriv g t / g t = Complex.log (g b) - Complex.log (g p₃) := by
    rw [intervalIntegral.integral_congr_ae h_ae₅, h_ftc₅, h_gp₃', h_gb]
  have hint_left : IntervalIntegrable (fun t => deriv g t / g t) volume a tₗ :=
    (hint_g₁.trans hint_g₂).trans hint_g₃
  have hint_right : IntervalIntegrable (fun t => deriv g t / g t) volume tᵣ b :=
    hint_g₄.trans hint_g₅
  have h_left_sum : ∫ t in a..tₗ, deriv g t / g t =
      Complex.log (g tₗ) - Complex.log (g a) := by
    simp [← intervalIntegral.integral_add_adjacent_intervals (hint_g₁.trans hint_g₂) hint_g₃,
      ← intervalIntegral.integral_add_adjacent_intervals hint_g₁ hint_g₂, h_eq₁, h_eq₂, h_eq₃]
  have h_right_sum : ∫ t in tᵣ..b, deriv g t / g t =
      Complex.log (g b) - Complex.log (g tᵣ) := by
    simp [← intervalIntegral.integral_add_adjacent_intervals hint_g₄ hint_g₅, h_eq₄, h_eq₅]
  have h_closed_g : g a = g b := by rw [h_ga, h_gb, h_closed]
  refine ⟨hint_left, hint_right, ?_⟩
  simp [h_left_sum, h_right_sum, ← h_closed_g]

end ContourIntegral
