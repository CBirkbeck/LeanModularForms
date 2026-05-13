# Inventory: SegmentFTC.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/SegmentFTC.lean` (319 lines)

Purpose: Fundamental Theorem of Calculus (FTC) lemmas for integrals of `f'/f` (log-derivative) along segments of piecewise-C¹ paths. Provides:
1. Telescoping FTC over two/three consecutive segments, including closed-curve splits.
2. Transfer lemmas to upgrade FTC for a reference function `h` to a function `g` agreeing with `h` a.e.
3. Single-function FTC: integrability + integral identity when `f` (or `−f`) stays in `slitPlane`.

Imports: `LeanModularForms.ForMathlib.PiecewiseContourIntegral`, `Mathlib.Analysis.SpecialFunctions.Complex.Log`, `Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv`.

Namespaces: `SegmentFTC` (Part 1, telescoping) and `LogDerivFTC` (Part 2, single-function FTC).

---

## Part 1: namespace `SegmentFTC`

### `theorem ftc_telescope_two`
- **Type**: `{f : ℝ → ℂ} {a b c : ℝ} (hint_ab : IntervalIntegrable (fun t => deriv f t / f t) volume a b) (hint_bc : IntervalIntegrable (fun t => deriv f t / f t) volume b c) (h_ab : ∫ t in a..b, deriv f t / f t = log (f b) - log (f a)) (h_bc : ∫ t in b..c, deriv f t / f t = log (f c) - log (f b)) : ∫ t in a..c, deriv f t / f t = log (f c) - log (f a)`
- **What**: Two consecutive FTC-for-log identities concatenate; the `log (f b)` terms cancel.
- **How**: `intervalIntegral.integral_add_adjacent_intervals` to merge integrals; substitute `h_ab`, `h_bc`; `ring`.
- **Hypotheses**: both subintegrals interval-integrable; each obeys FTC-for-log.
- **Uses from project**: [].
- **Used by**: `ftc_telescope_three`, `ftc_telescope_piecewise_two`.
- **Visibility**: public
- **Lines**: 58–65

### `theorem ftc_telescope_three`
- **Type**: `{f : ℝ → ℂ} {a b c d : ℝ}` with three IntervalIntegrable hypotheses on `[a,b]`, `[b,c]`, `[c,d]` and three FTC-for-log hypotheses; conclusion `∫ t in a..d, deriv f t / f t = log (f d) - log (f a)`.
- **What**: Three-segment telescoping of FTC-for-log.
- **How**: Two applications of `intervalIntegral.integral_add_adjacent_intervals` to merge into `[a,d]`; substitute; `ring`.
- **Hypotheses**: three IntervalIntegrable + three local FTC equalities.
- **Uses from project**: [].
- **Used by**: `ftc_telescope_piecewise_three`.
- **Visibility**: public
- **Lines**: 69–80

### `theorem ftc_telescope_closed_split`
- **Type**: `{f : ℝ → ℂ} {a b t₀ δ : ℝ} (h_closed : f a = f b) (h_left : ∫ t in a..(t₀-δ), deriv f t / f t = log (f (t₀-δ)) - log (f a)) (h_right : ∫ t in (t₀+δ)..b, deriv f t / f t = log (f b) - log (f (t₀+δ))) : (∫ t in a..(t₀-δ), deriv f t / f t) + (∫ t in (t₀+δ)..b, deriv f t / f t) = log (f (t₀-δ)) - log (f (t₀+δ))`
- **What**: For a closed curve split at a crossing `t₀ ± δ`, the partial integrals telescope to a log-difference at the gap.
- **How**: Substitute the two local FTCs; use `f a = f b` to cancel; `ring`.
- **Hypotheses**: `f a = f b` (closedness); local FTCs on the two sides of the crossing.
- **Uses from project**: [].
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 85–94

### `theorem ftc_telescope_integrability`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hint_h : IntervalIntegrable (fun t => deriv h t / h t) volume a b) (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t) : IntervalIntegrable (fun t => deriv g t / g t) volume a b`
- **What**: Integrability of `g'/g` from integrability of `h'/h` plus a.e. equality of their log-derivatives on the unordered interval `Ι a b`.
- **How**: `IntervalIntegrable.congr_ae` after upgrading the implication to an equality on a measurable set via `ae_restrict_iff'`.
- **Hypotheses**: integrability of `h'/h`; a.e.-equality of log-derivatives.
- **Uses from project**: [].
- **Used by**: `ftc_telescope_transfer`, `ftc_telescope_piecewise_two`, `ftc_telescope_piecewise_three`.
- **Visibility**: public
- **Lines**: 100–105

### `theorem ftc_telescope_transfer`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ}` with `h`-FTC, a.e.-agreement, and endpoint agreement of `g` with `h`; conclusion: both integrability of `g'/g` and `∫ g'/g = log(g b) - log(g a)`.
- **What**: Transfer FTC from `h` to `g` provided log-derivatives agree a.e. and endpoint values match.
- **How**: Combine `ftc_telescope_integrability` with `intervalIntegral.integral_congr_ae`, rewriting via endpoint equalities.
- **Hypotheses**: `h`-integrability, `h`-FTC, a.e.-agreement of log-derivatives, endpoint agreement.
- **Uses from project**: `ftc_telescope_integrability`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 110–121

### `theorem ftc_telescope_piecewise_two`
- **Type**: `{g h₁ h₂ : ℝ → ℂ} {a p b : ℝ}` with FTC + integrability on each side via `h₁`, `h₂`, plus a.e.-agreement and four endpoint conditions (a, p left, p right, b); conclusion: integrability and FTC for `g` on `[a,b]`.
- **What**: Piecewise FTC: combine FTCs on `[a,p]` and `[p,b]` for two distinct comparison functions agreeing with `g` a.e.
- **How**: `ftc_telescope_integrability` for each side; rewrite endpoint values; conclude via `IntervalIntegrable.trans` and `ftc_telescope_two`.
- **Hypotheses**: per-piece integrability/FTC for `h₁`, `h₂`; piecewise a.e.-agreement; four endpoint equalities.
- **Uses from project**: `ftc_telescope_integrability`, `ftc_telescope_two`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 129–148
- **Notes**: >15 lines.

### `theorem ftc_telescope_piecewise_three`
- **Type**: `{g h₁ h₂ h₃ : ℝ → ℂ} {a p q b : ℝ}` with FTC + integrability on three pieces `[a,p]`, `[p,q]`, `[q,b]` via `h₁,h₂,h₃`, plus a.e.-agreement and six endpoint equalities; conclusion: integrability + FTC for `g` on `[a,b]`.
- **What**: Piecewise FTC with two interior breakpoints.
- **How**: Apply `ftc_telescope_integrability` and per-piece value rewrites three times; finish via `ftc_telescope_three`.
- **Hypotheses**: three pieces' integrability/FTC + a.e.-agreement + endpoint equalities.
- **Uses from project**: `ftc_telescope_integrability`, `ftc_telescope_three`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 151–178
- **Notes**: >20 lines.

---

## Part 2: namespace `LogDerivFTC`

### `theorem intervalIntegrable_logDeriv_of_slitPlane`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf_cont : ContinuousOn f (Icc a b)) (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b)) (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) : IntervalIntegrable (fun t => deriv f t / f t) volume a b`
- **What**: When `f` is continuous, `deriv f` continuous, and `f` stays in `slitPlane`, the log-derivative `f'/f` is interval-integrable.
- **How**: `slitPlane_ne_zero` gives `f t ≠ 0`; `ContinuousOn.div` gives continuity of `f'/f` on `Icc a b`; `.intervalIntegrable` finishes.
- **Hypotheses**: a ≤ b; `f` and `deriv f` continuous on `Icc`; `f t ∈ slitPlane`.
- **Uses from project**: [].
- **Used by**: `integral_logDeriv_eq_log_sub`, `ftc_log_on_segment`.
- **Visibility**: public
- **Lines**: 193–202

### `theorem integral_logDeriv_eq_log_sub`
- **Type**: `{f : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hf_cont : ContinuousOn f (Icc a b)) (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t) (hf_deriv_cont : ContinuousOn (deriv f) (Icc a b)) (hf_slit : ∀ t ∈ Icc a b, f t ∈ Complex.slitPlane) : ∫ t in a..b, deriv f t / f t = Complex.log (f b) - Complex.log (f a)`
- **What**: FTC for log-derivatives in the slit plane: the integral is `log f(b) − log f(a)`.
- **How**: `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`; primitive is `Complex.log ∘ f`, continuous via `ContinuousOn.clog`; derivative via `.hasDerivAt.clog_real`; integrability via `intervalIntegrable_logDeriv_of_slitPlane`.
- **Hypotheses**: a ≤ b; `f` continuous on `Icc`; `f` differentiable on `Ioo`; `deriv f` continuous on `Icc`; `f t ∈ slitPlane`.
- **Uses from project**: `intervalIntegrable_logDeriv_of_slitPlane`.
- **Used by**: `ftc_log_on_segment`, `ftc_log_pieceFM`.
- **Visibility**: public
- **Lines**: 208–217

### `theorem ftc_log_on_segment`
- **Type**: Same hypotheses as `integral_logDeriv_eq_log_sub`; conclusion: integrability AND the FTC identity packaged together.
- **What**: Combined integrability + FTC for log-derivative when `f` stays in `slitPlane`.
- **How**: Pair `intervalIntegrable_logDeriv_of_slitPlane` and `integral_logDeriv_eq_log_sub`.
- **Hypotheses**: same as above.
- **Uses from project**: `intervalIntegrable_logDeriv_of_slitPlane`, `integral_logDeriv_eq_log_sub`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 224–232

### `theorem ftc_log_neg_on_segment`
- **Type**: Same shape as `ftc_log_on_segment` but with `-f t ∈ slitPlane`; conclusion: integrability AND `∫ deriv f t / f t = log (-f b) - log (-f a)`.
- **What**: FTC variant when `−f` stays in `slitPlane`; primitive is `log ∘ (−f)`.
- **How**: Continuity of `log(−f)` via `.neg.clog`; derivative via `.hasDerivAt.neg.clog_real`; key identity `-deriv f / -f = deriv f / f` via `neg_div_neg_eq`; integrability via continuity of `deriv f / f` (uses `f t ≠ 0` from `neg_ne_zero.mp ∘ slitPlane_ne_zero`).
- **Hypotheses**: a ≤ b; `f` continuous; `f` differentiable on `Ioo`; `deriv f` continuous; `-f t ∈ slitPlane`.
- **Uses from project**: [].
- **Used by**: `integral_logDeriv_eq_neg_log_sub`.
- **Visibility**: public
- **Lines**: 237–260
- **Notes**: >20 lines.

### `theorem integral_logDeriv_eq_neg_log_sub`
- **Type**: Same hypotheses as `ftc_log_neg_on_segment`; conclusion: `∫ t in a..b, deriv f t / f t = log (-f b) - log (-f a)`.
- **What**: Bare FTC formulation of the `−f ∈ slitPlane` variant.
- **How**: Project second component of `ftc_log_neg_on_segment`.
- **Hypotheses**: same as `ftc_log_neg_on_segment`.
- **Uses from project**: `ftc_log_neg_on_segment`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 264–270

### `theorem ftc_log_pieceFM`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hh_cont : ContinuousOn h (Icc a b)) (hh_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ h t) (hh_deriv_cont : ContinuousOn (deriv h) (Icc a b)) (hh_slit : ∀ t ∈ Icc a b, h t ∈ slitPlane) (heq : ∀ t ∈ Ioo a b, g t = h t ∧ deriv g t = deriv h t) (heq_a : g a = h a) (heq_b : g b = h b) : IntervalIntegrable (fun t => deriv g t / g t) volume a b ∧ ∫ t in a..b, deriv g t / g t = log (g b) - log (g a)`
- **What**: FTC for `g'/g` when `g` agrees with a reference `h` (which lies in `slitPlane`) on `Ioo a b` and at the endpoints.
- **How**: Build `h`-integrability via `ContinuousOn.div` and `.intervalIntegrable`; observe `g'/g = h'/h` a.e. on `Ι a b` via the cocountable set `{b}ᶜ`; transport `h`-integrability with `Integrable.congr` and combine with `integral_logDeriv_eq_log_sub` and endpoint rewrites; the `Ioc b a = ∅` case handled directly via `integrableOn_empty`.
- **Hypotheses**: `h`-continuity/differentiability/`slitPlane`; interior + endpoint agreement of `g` and `h`.
- **Uses from project**: `integral_logDeriv_eq_log_sub`.
- **Used by**: unused in file (consumed by `ValenceFormula/WindingWeights/Common.lean` and others).
- **Visibility**: public
- **Lines**: 278–317
- **Notes**: >30 lines (40 lines); careful a.e.-agreement with `mem_ae_iff` + `compl_compl` + `measure_singleton`.

---

## File Summary

- **Declarations**: 11 theorems (7 in `SegmentFTC`, 4 in `LogDerivFTC`; one bonus `intervalIntegrable_logDeriv_of_slitPlane`). All public, no axioms, no sorries.
- **Theme**: Two complementary toolkits for FTC of log-derivative integrals:
  1. **Telescoping** (Part 1): chain FTC identities across segments, optionally transferring from a reference function to an a.e.-equal target.
  2. **Single-segment FTC** (Part 2): integrability and explicit integral value for `∫ f'/f` on `[a,b]` when `f` (or `−f`) stays in `slitPlane`.
- **Internal call graph**: `intervalIntegrable_logDeriv_of_slitPlane` underlies `integral_logDeriv_eq_log_sub`, which underlies `ftc_log_on_segment` and `ftc_log_pieceFM`. The `_neg` variant is independent. In Part 1, `ftc_telescope_integrability` is the workhorse for `ftc_telescope_transfer` and the piecewise variants.
- **Notes**: No `set_option`, no `sorry`, no `axiom`, no `TODO`. Used downstream by the winding-weight files (e.g., `ValenceFormula/WindingWeights/Common.lean` redefines `ftc_log_pieceFM` as a thin wrapper around `LogDerivFTC.ftc_log_pieceFM`).
