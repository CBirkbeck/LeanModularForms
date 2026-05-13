# HW33ExitTimeWrapper.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33ExitTimeWrapper.lean`
Lines: 118

## theorem/`LeanModularForms.hw_theorem_3_3_odd_transverse_bundled`
- **Type**: Same conclusion as the parametric version: `Tendsto (fun ε ↦ ∫_a^{data.tMinus ε} γ'/(γ-s)^k + ∫_{data.tPlus ε}^b γ'/(γ-s)^k) (𝓝[>] 0) (𝓝 0)`, parameterized by a `HW33ExitData γ t₀ s` bundle instead of two exit-time functions.
- **What**: **Bundled form** of `hw_theorem_3_3_odd_transverse_parametric` — packages the four `Tendsto`/radius hypotheses on `t_eps_plus` and `t_eps_minus` into a single `HW33ExitData` value.
- **How**: Direct invocation of `hw_theorem_3_3_odd_transverse_parametric` with `data.tPlus`, `data.tMinus`, `data.plus_to`, `data.plus_radius`, `data.minus_to`, `data.minus_radius` extracted from the bundle; pass the smoothness/avoidance/integrability hypotheses through.
- **Hypotheses**: closure `γ a = γ b`; `IsFlatOfOrder γ t₀ n`; `L ≠ 0`; one-sided `HasDerivWithinAt γ L (Ioi t₀) t₀` and `(Iio t₀) t₀`; one-sided `Tendsto (deriv γ)` to `L`; `γ t₀ = s`; `2 ≤ k`, `Odd k`, `k ≤ n`, `1 ≤ n`; bundled `HW33ExitData γ t₀ s`; punctured-side smoothness/avoidance/integrability via `data.tMinus`/`data.tPlus`.
- **Uses-from-project**: `hw_theorem_3_3_odd_transverse_parametric`, `HW33ExitData`, `IsFlatOfOrder`.
- **Used by**: `hw_theorem_3_3_odd_transverse_concrete` (this file).
- **Visibility**: public (in namespace `LeanModularForms`)
- **Lines**: 40–68

## theorem/`LeanModularForms.hw_theorem_3_3_odd_transverse_concrete`
- **Type**: Same Tendsto-to-zero conclusion, but with `firstExitTimeRight` / `firstExitTimeLeft` in place of `data.tPlus` / `data.tMinus`.
- **What**: **Fully concrete form** of HW Theorem 3.3 (odd transverse), using the project-level `firstExitTimeRight` / `firstExitTimeLeft` constructions directly. The user supplies continuity, the "γ leaves `s` away from `t₀`" hypothesis on each side, and the smoothness/avoidance/integrability oracles on the punctured outer intervals — `HW33ExitData` is auto-built via `HW33ExitData.ofExitTimes`.
- **How**: `hw_theorem_3_3_odd_transverse_bundled` with `data := HW33ExitData.ofExitTimes hδPlus hδMinus hγ_cont_right hγ_cont_left h_s h_leave_right h_leave_left`; pass through all other oracles.
- **Hypotheses**: `0 < δPlus`, `0 < δMinus`; closure `γ a = γ b`; `IsFlatOfOrder γ t₀ n`; `L ≠ 0`; one-sided derivative existence and `Tendsto` for `deriv γ`; `γ t₀ = s`; `2 ≤ k`, `Odd k`, `k ≤ n`, `1 ≤ n`; one-sided continuity on `[t₀, t₀+δPlus]` and `[t₀-δMinus, t₀]`; "leave `s`" on each one-sided punctured interval; smoothness/avoidance/integrability via `firstExitTimeRight`/`firstExitTimeLeft`.
- **Uses-from-project**: `hw_theorem_3_3_odd_transverse_bundled`, `HW33ExitData.ofExitTimes`, `firstExitTimeRight`, `firstExitTimeLeft`, `IsFlatOfOrder`.
- **Used by**: User-facing endpoint; downstream HW33 closed/paper forms.
- **Visibility**: public (in namespace `LeanModularForms`)
- **Lines**: 81–116

## File Summary
Two wrappers for the odd-transverse case of HW Theorem 3.3 (the parametric "PV → 0" result). The `bundled` form repackages four exit-time `Tendsto`/radius hypotheses into a single `HW33ExitData` value; the `concrete` form goes further and uses the project's `firstExitTimeRight`/`firstExitTimeLeft` directly, only requiring one-sided continuity and the "γ leaves `s` away from `t₀`" hypotheses on each side. Both are thin pass-throughs over `hw_theorem_3_3_odd_transverse_parametric` (from `HigherOrderCancel.lean`); the work lives in `ExitTime.lean` and the parametric theorem.
