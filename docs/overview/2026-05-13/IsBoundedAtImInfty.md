# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/IsBoundedAtImInfty.lean

(Entire file is commented out — wrapped in `/-` ... `-/`. The declarations
below are not currently part of the build, but the source is preserved
for reference / future re-enabling.)

## lemma `EisensteinSeries.summable_norm_eisSummand` (commented out)
- **Type**: `{k : ℤ} (hk : 3 ≤ k) (z : ℍ)
  → Summable fun (x : Fin 2 → ℤ) ↦ ‖eisSummand k x z‖`.
- **What**: For weight `k ≥ 3`, the norm-summand series of the level-`Γ(N)`
  Eisenstein series is summable.
- **How**: Compares to `(summable_one_div_norm_rpow hk').mul_left (r z ^ (-k))`
  using `Summable.of_nonneg_of_le` and the mathlib `summand_bound`.
- **Hypotheses**: `3 ≤ k`.
- **Uses-from-project**: `Identities`, `CongruenceSubgrps` (transitively
  imported).
- **Used by**: `norm_le_tsum_norm`, `isBoundedAtImInfty_eisensteinSeries_SIF`
  (locally — all commented).
- **Visibility**: would be public `lemma`; namespace `EisensteinSeries`.
- **Lines**: 38-45 (inside commented block).

## lemma `EisensteinSeries.norm_le_tsum_norm` (commented out)
- **Type**: `(N : ℕ) (a : Fin 2 → ZMod N) (k : ℤ) (hk : 3 ≤ k) (z : ℍ)
  → ‖eisensteinSeries a k z‖ ≤ ∑' (x : Fin 2 → ℤ), ‖eisSummand k x z‖`.
- **What**: The norm of the restricted Eisenstein series is bounded by
  the full sum of summand norms.
- **How**: Uses `norm_tsum_le_tsum_norm` for the subtype-restricted sum
  followed by `Summable.tsum_subtype_le` against the full summand series.
- **Hypotheses**: `3 ≤ k`.
- **Uses-from-project**: `summable_norm_eisSummand`.
- **Used by**: `isBoundedAtImInfty_eisensteinSeries_SIF` (locally).
- **Visibility**: would be public; namespace `EisensteinSeries`.
- **Lines**: 48-53 (commented).
- **Notes**: Has deprecated alias `abs_le_tsum_abs`.

## theorem `EisensteinSeries.isBoundedAtImInfty_eisensteinSeries_SIF` (commented out)
- **Type**: `{N : ℕ+} (a : Fin 2 → ZMod N) {k : ℤ} (hk : 3 ≤ k) (A : SL(2, ℤ))
  → IsBoundedAtImInfty ((eisensteinSeries_SIF a k).toFun ∣[k] A)`.
- **What**: Level-`Γ(N)` Eisenstein series of weight `k ≥ 3` are bounded
  at `i∞` after any `SL(2, ℤ)`-slash.
- **How**: Reduces to a vertical-strip bound via
  `ModularGroup_T_zpow_mem_verticalStrip` and `Subgroup.Gamma_width` (giving
  `Γ(N).width ∣ N * n`), rewrites the slash through
  `eisensteinSeries_slash_apply` and `T_zpow_width_invariant`, then uses
  `summand_bound_of_mem_verticalStrip` (mathlib) to bound termwise; finally
  applies `Summable.tsum_le_tsum`.
- **Hypotheses**: `3 ≤ k`, `N : ℕ+`, `a : Fin 2 → ZMod N`, `A : SL(2, ℤ)`.
- **Uses-from-project**: `Subgroup.Gamma_width` (from `CongruenceSubgrps`),
  `norm_le_tsum_norm` (above), `summable_norm_eisSummand` (above);
  mathlib's `ModularGroup_T_zpow_mem_verticalStrip`,
  `T_zpow_width_invariant`, `eisensteinSeries_slash_apply`,
  `verticalStrip_anti_right`.
- **Used by**: Boundedness-at-infinity callers for modular-form structure
  on the level-`Γ(N)` Eisenstein series (currently disabled).
- **Visibility**: would be public `theorem`; namespace `EisensteinSeries`.
- **Lines**: 57-75 (commented).
- **Notes**: Header explains the strategy: slash-action shifts the
  congruence vector `a` to `a ᵥ* A`, then the bound is via a vertical
  strip after a power of `T`.

## File Summary
The entire content is wrapped in a block comment `/- ... -/`. Three
declarations are sketched: `summable_norm_eisSummand`, `norm_le_tsum_norm`
(plus deprecated alias `abs_le_tsum_abs`), and the main
`isBoundedAtImInfty_eisensteinSeries_SIF`. The intended purpose is to
prove that level-`Γ(N)` Eisenstein series of weight `≥ 3` are bounded at
`i∞` after any `SL(2, ℤ)` slash. As of the current build the file
exports no live declarations. Imports declared at the top:
`Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty`,
`Mathlib.Analysis.Normed.Order.Lattice`,
`Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence`,
`Mathlib.NumberTheory.ModularForms.Identities`,
`Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`,
`LeanModularForms.ForMathlib.CongruenceSubgrps`,
`LeanModularForms.ForMathlib.Identities` (also inside the comment).
