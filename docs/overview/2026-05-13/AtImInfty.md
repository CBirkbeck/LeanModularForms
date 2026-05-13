# AtImInfty.lean

## lemma/Filter.eventually_atImInfty
- **Type**: `{p : ℍ → Prop} → (∀ᶠ x in atImInfty, p x) ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ z.im → p z`
- **What**: Characterization of `eventually` for `atImInfty`: equivalent to existence of `A` such that `p` holds for all `z : ℍ` with `A ≤ z.im`.
- **How**: `atImInfty_mem (setOf p)`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: Downstream files dealing with eventual behavior near `i∞`.
- **Visibility**: public; in `Filter` namespace.
- **Lines**: ~12-14.
- **Notes**: Candidate for mathlib `Analysis/Complex/UpperHalfPlane/FunctionsBoundedAtInfty.lean`.

## lemma/Filter.tendsto_im_atImInfty
- **Type**: `Tendsto (fun x : ℍ ↦ x.im) atImInfty atTop`
- **What**: The imaginary-part projection tends to `atTop` along `atImInfty`.
- **How**: `tendsto_comap`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: Limits/asymptotic arguments at `i∞`.
- **Visibility**: public; in `Filter` namespace.
- **Lines**: ~16-17.
- **Notes**: Pure filter convenience lemma.

### File Summary
Two `Filter`-namespace convenience lemmas for `atImInfty`: characterization of `eventually` and `tendsto im → atTop`. Candidates for mathlib upstream. No project deps.
