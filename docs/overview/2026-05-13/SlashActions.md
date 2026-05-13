# SlashActions.lean

## theorem/ModularForm.slash_neg_one
- **Type**: `{k : ℤ} (f : ℍ → ℂ) (hk : Even k) → f ∣[k] (-1 : (GL (Fin 2) ℝ)) = f ∣[k] (1 : (GL (Fin 2) ℝ))`
- **What**: Slash action by `-I₂` (as `GL(n, ℝ)⁺` matrix) equals slash action by identity when weight `k` is even.
- **How**: `ext x; simp [slash_def, denom, hk.neg_one_zpow, Matrix.det_neg, σ]`.
- **Hypotheses**: `Even k`.
- **Uses-from-project**: [].
- **Used by**: `ModularForm.slash_neg` (same file).
- **Visibility**: public.
- **Lines**: ~21-24.
- **Notes**: From Sphere Pack project; candidate for mathlib `NumberTheory/ModularForms/SlashActions.lean`.

## theorem/ModularForm.slash_neg_one'
- **Type**: `{k : ℤ} (f : ℍ → ℂ) (hk : Even k) → f ∣[k] (-1 : SL(2, ℤ)) = f ∣[k] (1 : SL(2, ℤ))`
- **What**: `SL(2, ℤ)` version: slash by `-I₂` equals slash by identity for even weight.
- **How**: `ext x; simp [SL_slash_def, denom, hk.neg_one_zpow]`.
- **Hypotheses**: `Even k`.
- **Uses-from-project**: [].
- **Used by**: `ModularForm.slash_neg'` (same file).
- **Visibility**: public.
- **Lines**: ~28-31.
- **Notes**: Companion to `slash_neg_one` for SL(2,ℤ).

## theorem/ModularForm.slash_neg
- **Type**: `{k : ℤ} (g : GL (Fin 2) ℝ) (f : ℍ → ℂ) (hk : Even k) → f ∣[k] (-g) = f ∣[k] g`
- **What**: Slash invariance under negation `g ↦ -g` for `GL(n, ℝ)⁺` for even weight.
- **How**: `rw [← neg_one_mul, SlashAction.slash_mul, slash_neg_one f hk, SlashAction.slash_one]`.
- **Hypotheses**: `Even k`.
- **Uses-from-project**: `slash_neg_one`.
- **Used by**: `ModularForm.slash_neg'`.
- **Visibility**: public.
- **Lines**: ~34-36.
- **Notes**: Built on `slash_neg_one`.

## theorem/ModularForm.slash_neg'
- **Type**: `{k : ℤ} (g : SL(2, ℤ)) (f : ℍ → ℂ) (hk : Even k) → f ∣[k] (-g) = f ∣[k] g`
- **What**: SL(2,ℤ) version of `slash_neg`.
- **How**: `rw [SL_slash, ← slash_neg _ _ hk]; congr; ext; simp`.
- **Hypotheses**: `Even k`.
- **Uses-from-project**: `slash_neg`.
- **Used by**: Downstream modular form symmetry arguments.
- **Visibility**: public.
- **Lines**: ~39-44.
- **Notes**: Final SL(2,ℤ) version, built atop the GL(n, ℝ)⁺ chain.

### File Summary
Four mathlib-style theorems on slash action invariance under negation for even-weight forms (GL(n, ℝ)⁺ and SL(2,ℤ) flavors). Candidates for mathlib `NumberTheory/ModularForms/SlashActions.lean`. No project deps.
