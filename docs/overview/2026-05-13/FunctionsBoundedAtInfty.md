# FunctionsBoundedAtInfty.lean

## theorem/isBoundedAtImInfty_neg_iff
- **Type**: `(f : ℍ → ℂ) → IsBoundedAtImInfty (-f) ↔ IsBoundedAtImInfty f`
- **What**: Negation preserves bounded-at-`i∞`.
- **How**: `simp [UpperHalfPlane.isBoundedAtImInfty_iff]`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: `IsBoundedAtImInfty.neg` (its `mpr` direction alias, same file).
- **Visibility**: public.
- **Lines**: ~5-7.
- **Notes**: Mathlib-style; candidate for upstream.

## alias/IsBoundedAtImInfty.neg
- **Type**: forward direction of `isBoundedAtImInfty_neg_iff`
- **What**: Alias giving `IsBoundedAtImInfty f → IsBoundedAtImInfty (-f)` (the `mpr` direction).
- **How**: `alias ⟨_, IsBoundedAtImInfty.neg⟩ := isBoundedAtImInfty_neg_iff`.
- **Hypotheses**: none.
- **Uses-from-project**: `isBoundedAtImInfty_neg_iff`.
- **Used by**: Dot-notation users of `.neg` on a bounded-at-`i∞` hypothesis.
- **Visibility**: public.
- **Lines**: ~9.
- **Notes**: Standard mathlib pattern of generating a forward alias from an iff.

### File Summary
Mini file containing a single `iff` lemma (`IsBoundedAtImInfty` preserved under negation) plus its forward alias for dot-notation use. Candidate for mathlib upstream. No project deps.
