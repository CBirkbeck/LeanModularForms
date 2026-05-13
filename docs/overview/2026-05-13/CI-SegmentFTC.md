# SegmentFTC.lean (ContourIntegral)

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ContourIntegral/SegmentFTC.lean
**Lines**: 205
**Imports**: `LeanModularForms.ForMathlib.SegmentFTC` (sibling), `Mathlib`
**Namespace**: `ContourIntegral`

---

## theorem `ftc_telescope_two`
- **Type**: `{f : ℝ → ℂ} {a b c : ℝ} (hint_ab : IntervalIntegrable (fun t => deriv f t / f t) volume a b) (hint_bc : IntervalIntegrable (...) volume b c) (h_ab : ∫ t in a..b, deriv f t / f t = log (f b) - log (f a)) (h_bc : ∫ t in b..c, deriv f t / f t = log (f c) - log (f b)) : ∫ t in a..c, deriv f t / f t = log (f c) - log (f a)`
- **What**: FTC-for-log telescopes across two consecutive segments.
- **How**: `rw [← intervalIntegral.integral_add_adjacent_intervals hint_ab hint_bc, h_ab, h_bc]; ring`.
- **Hypotheses**: per-segment integrability and FTC results.
- **Uses-from-project**: none directly (mathlib `intervalIntegral.integral_add_adjacent_intervals`).
- **Used by**: `ftc_telescope_piecewise_two`.
- **Visibility**: public (in namespace).
- **Lines**: 31-38.
- **Notes**: Inner `log f b` cancels.

## theorem `ftc_telescope_closed_split`
- **Type**: `{f : ℝ → ℂ} {a b t₀ δ : ℝ} (h_closed : f a = f b) (h_left : ∫ t in a..(t₀ - δ), deriv f t / f t = log (f (t₀ - δ)) - log (f a)) (h_right : ∫ t in (t₀ + δ)..b, deriv f t / f t = log (f b) - log (f (t₀ + δ))) : (∫ t in a..(t₀ - δ), ...) + (∫ t in (t₀ + δ)..b, ...) = log (f (t₀ - δ)) - log (f (t₀ + δ))`
- **What**: For a closed curve, the FTC on `[a, t₀ − δ] ∪ [t₀ + δ, b]` telescopes to `log(f(t₀ − δ)) − log(f(t₀ + δ))`.
- **How**: `rw [h_left, h_right, ← h_closed]; ring` — the outer logs cancel via closedness.
- **Hypotheses**: `f a = f b` (closed), and FTC on each side of the gap.
- **Uses-from-project**: none.
- **Used by**: external (single-crossing FTC).
- **Visibility**: public.
- **Lines**: 43-51.
- **Notes**: Crossing-gap telescope.

## theorem `ftc_telescope_three`
- **Type**: `{f : ℝ → ℂ} {a b c d : ℝ} (hint_ab) (hint_bc) (hint_cd) (h_ab : log diff) (h_bc) (h_cd) : ∫ t in a..d, deriv f t / f t = log (f d) - log (f a)`
- **What**: FTC-for-log telescopes across three consecutive segments.
- **How**: `rw [← intervalIntegral.integral_add_adjacent_intervals (hint_ab.trans hint_bc) hint_cd, ← intervalIntegral.integral_add_adjacent_intervals hint_ab hint_bc, h_ab, h_bc, h_cd]`.
- **Hypotheses**: per-segment integrability and FTC results on three intervals.
- **Uses-from-project**: none.
- **Used by**: `ftc_telescope_piecewise_three`, `ftc_telescope_closed_split_five`.
- **Visibility**: public.
- **Lines**: 55-65.
- **Notes**: Triple-segment telescope (extension of `ftc_telescope_two`).

## theorem `ftc_telescope_integrability`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hint_h : IntervalIntegrable (deriv h / h) volume a b) (h_ae : ∀ᵐ t ∂volume, t ∈ Ι a b → deriv g t / g t = deriv h t / h t) : IntervalIntegrable (deriv g / g) volume a b`
- **What**: Transfer integrability from a local function `h` to a global function `g` given pointwise a.e. agreement of log-derivatives on the interval.
- **How**: `hint_h.congr_ae ((ae_restrict_iff' measurableSet_uIoc).mpr (h_ae.mono (fun _t ht hm => (ht hm).symm)))`.
- **Hypotheses**: integrability of `h`'s log-derivative, a.e. agreement of `g/h` log-derivatives on `Ι a b`.
- **Uses-from-project**: none.
- **Used by**: `ftc_telescope_transfer`, `ftc_telescope_piecewise_two`, `ftc_telescope_piecewise_three`, `ftc_telescope_closed_split_five`.
- **Visibility**: public.
- **Lines**: 71-76.
- **Notes**: AE-direction inversion: the hypothesis gives `g/g = h/h` but `congr_ae` wants the symmetric direction, hence `.symm` inside the `.mono`.

## theorem `ftc_telescope_transfer`
- **Type**: `{g h : ℝ → ℂ} {a b : ℝ} (hint_h) (h_ftc) (h_ae) (h_ga : g a = h a) (h_gb : g b = h b) : IntervalIntegrable (deriv g / g) volume a b ∧ ∫ t in a..b, deriv g t / g t = log (g b) - log (g a)`
- **What**: Transfer an FTC result from a local `h` to `g` given a.e. log-derivative agreement and endpoint value agreement.
- **How**: Use `ftc_telescope_integrability hint_h h_ae` for integrability; for the FTC, `rw [intervalIntegral.integral_congr_ae h_ae, h_ftc, h_ga, h_gb]`.
- **Hypotheses**: local-`h` integrability and FTC, a.e. log-derivative agreement, endpoint agreement.
- **Uses-from-project**: `ftc_telescope_integrability`.
- **Used by**: external.
- **Visibility**: public.
- **Lines**: 81-89.
- **Notes**: Bundles integrability and FTC equality for `g`.

## theorem `ftc_telescope_piecewise_two`
- **Type**: `{g h₁ h₂ : ℝ → ℂ} {a p b : ℝ} (hint₁) (hint₂) (h_ftc₁) (h_ftc₂) (h_ae₁) (h_ae₂) (h_ga, h_gp_left, h_gp_right, h_gb : endpoint matches) : IntervalIntegrable (deriv g / g) volume a b ∧ ∫ t in a..b, deriv g t / g t = log (g b) - log (g a)`
- **What**: Piecewise FTC telescope on `[a, b]` with one interior breakpoint `p` and two local functions.
- **How** (>10 lines): Build `hint_g₁`, `hint_g₂` from `ftc_telescope_integrability hint_k h_ae_k` (k=1,2). Derive `h_eq₁ : ∫ a..p = log (g p) - log (g a)` via `intervalIntegral.integral_congr_ae h_ae₁`, `h_ftc₁`, `h_ga`, `h_gp_left`; similarly `h_eq₂` via `h_ae₂`, `h_ftc₂`, `h_gp_right`, `h_gb`. Conclude with `ftc_telescope_two hint_g₁ hint_g₂ h_eq₁ h_eq₂` and `.trans` for integrability.
- **Hypotheses**: per-piece integrability/FTC for `h₁, h₂`, a.e. agreement of `g` with each, and endpoint matches.
- **Uses-from-project**: `ftc_telescope_integrability`, `ftc_telescope_two`.
- **Used by**: external.
- **Visibility**: public.
- **Lines**: 95-112.
- **Notes**: Two-piece transfer.

## theorem `ftc_telescope_piecewise_three`
- **Type**: `{g h₁ h₂ h₃ : ℝ → ℂ} {a p q b : ℝ} (hint₁) (hint₂) (hint₃) (h_ftc₁) (h_ftc₂) (h_ftc₃) (h_ae₁) (h_ae₂) (h_ae₃) (six endpoint matches) : IntervalIntegrable (deriv g / g) volume a b ∧ ∫ t in a..b, deriv g t / g t = log (g b) - log (g a)`
- **What**: Piecewise FTC telescope with two interior breakpoints `p < q` and three local functions.
- **How** (>10 lines): Build `hint_g₁, hint_g₂, hint_g₃` via `ftc_telescope_integrability`. Derive per-segment FTC results `h_eq₁, h_eq₂, h_eq₃` via `intervalIntegral.integral_congr_ae` and `h_ftc_k`, `h_ga`, `h_gp`, `h_gp'`, `h_gq`, `h_gq'`, `h_gb`. Conclude with `ftc_telescope_three hint_g₁ hint_g₂ hint_g₃ h_eq₁ h_eq₂ h_eq₃` and `(hint_g₁.trans hint_g₂).trans hint_g₃`.
- **Hypotheses**: per-piece integrability/FTC for h₁,h₂,h₃, per-piece a.e. agreement, six endpoint matches.
- **Uses-from-project**: `ftc_telescope_integrability`, `ftc_telescope_three`.
- **Used by**: external.
- **Visibility**: public.
- **Lines**: 115-139.
- **Notes**: Three-piece transfer.

## theorem `ftc_telescope_closed_split_five`
- **Type**: `{g h₁ h₂ h₃ h₄ h₅ : ℝ → ℂ} {a p₁ p₂ tₗ tᵣ p₃ b : ℝ} (5× integrability) (5× FTC) (5× a.e. agreement) (10 endpoint matches) (h_closed : h₁ a = h₅ b) : ⟨IntervalIntegrable (deriv g / g) volume a tₗ, IntervalIntegrable ... volume tᵣ b, (∫ a..tₗ) + (∫ tᵣ..b) = log (g tₗ) - log (g tᵣ)⟩`
- **What**: Closed-curve FTC telescope across five piecewise segments with a crossing gap `[tₗ, tᵣ]`.
- **How** (>10 lines): Five `ftc_telescope_integrability` invocations to lift each `hint_k` to `hint_g_k`. Five `intervalIntegral.integral_congr_ae`-based equalities for `g`'s log-derivative integral on each segment (`h_eq₁` through `h_eq₅`), using endpoint matches `h_ga`, `h_gp₁`, `h_gp₁'`, `h_gp₂`, `h_gp₂'`, `h_gtₗ`, `h_gtᵣ`, `h_gp₃`, `h_gp₃'`, `h_gb`. Combine to `hint_left = (hint_g₁.trans hint_g₂).trans hint_g₃` and `hint_right = hint_g₄.trans hint_g₅`. For the sums, use `← intervalIntegral.integral_add_adjacent_intervals` twice on the left and once on the right with `h_eq₁..₃` and `h_eq₄, h_eq₅` (`ring`-cancelled). Derive `g a = g b` from `h_ga`, `h_gb`, `h_closed`, then `rw [h_left_sum, h_right_sum, ← h_closed_g]; ring` to telescope to `log (g tₗ) - log (g tᵣ)`.
- **Hypotheses**: per-segment integrability/FTC for five local functions, per-segment a.e. agreement with `g`, ten endpoint matches, closedness `h₁ a = h₅ b`.
- **Uses-from-project**: `ftc_telescope_integrability` (only; the rest is mathlib `intervalIntegral`).
- **Used by**: external (closed-curve FTC over a crossing gap with three left and two right local pieces).
- **Visibility**: public.
- **Lines**: 146-203.
- **Notes**: The "5-segment" closed-curve telescope — the main workhorse for crossing-gap FTC analyses in the ContourIntegral pipeline.

---

## File Summary

Telescoping FTC-for-log lemmas for piecewise segments. The atomic combinators `ftc_telescope_two` and `ftc_telescope_three` cancel inner-endpoint logs across two and three consecutive segments. `ftc_telescope_closed_split` handles a closed curve with a single crossing gap. `ftc_telescope_integrability` transfers integrability from a local function `h` to a global `g` via a.e. log-derivative agreement (with the direction-inversion subtlety inside `.mono`), and `ftc_telescope_transfer` packages integrability plus FTC equality. `ftc_telescope_piecewise_two` and `ftc_telescope_piecewise_three` lift the two- and three-segment telescopes to piecewise transfer via per-segment local functions and endpoint matches. The capstone `ftc_telescope_closed_split_five` handles a closed curve cut into three left and two right segments (with crossing gap `[tₗ, tᵣ]`), telescoping to `log(g tₗ) - log(g tᵣ)` by exploiting closedness `g a = g b` (deduced from `h₁ a = h₅ b` plus endpoint matches). All lemmas are namespaced under `ContourIntegral`.
