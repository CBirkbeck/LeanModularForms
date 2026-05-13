# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/GeneralizedResidueTheory/Residue/MeasureHelpers.lean

## theorem `Set.countable_setOf_isolated_points'`
- **Type**: For `S : Set ℝ` with the property "for every `t ∈ S` there is
  `ε > 0` such that every other `s ∈ S` is at distance `≥ ε`": `S.Countable`.
- **What**: A set of isolated points in `ℝ` is countable. (Stronger
  `'` variant — `ε` may depend on `t`.)
- **How**: Trivial when `S = ∅`. Otherwise `choose` extracts radii `r t > 0`
  and separation property `hr_sep` from `h`; the balls
  `ball t (r t / 2)` indexed by `S` are pairwise disjoint
  (`linarith` with `abs_sub_le` and the two separations), open, and
  nonempty. Then `Pairwise.countable_of_isOpen_disjoint` gives
  `Countable S` (as a subtype), and `Set.countable_coe_iff` converts to
  `S.Countable`.
- **Hypotheses**: per-point isolation witness `∀ t ∈ S, ∃ ε > 0, ...`.
- **Uses-from-project**: imports `ClassicalCPV` only for ambient setup
  (open/topology/interval) — the proof itself uses mathlib.
- **Used by**: `preimage_singleton_measure_zero_of_deriv_ne_zero` (locally).
- **Visibility**: public `theorem`; namespace `Set`.
- **Lines**: 20-46.
- **Notes**: ~27-line proof. The pairwise-disjoint argument is the heart.

## theorem `preimage_singleton_measure_zero_of_deriv_ne_zero`
- **Type**: For `γ : ℝ → ℂ`, `a b : ℝ`, finite singular set `P : Finset ℝ`,
  point `z₀ : ℂ`, continuous-on hyp, differentiability off `P`, and
  non-vanishing derivative off `P`: `volume {t ∈ Icc a b | γ t = z₀} = 0`.
- **What**: Preimage of a singleton under a piecewise-C¹ immersion has
  Lebesgue measure zero in the parameter line.
- **How**: Let `S = {t ∈ Icc a b | γ t = z₀}`. For `t₀ ∈ S \ P`,
  `HasDerivAt.eventually_ne` (with the nonzero derivative `hγ'_ne` applied
  to `c := z₀`) gives a punctured neighborhood in which
  `γ ≠ z₀`, supplying isolation. Decompose
  `S = (S ∩ P) ∪ (S \ P)`: the first is finite (subset of `↑P`), the second
  is countable by `Set.countable_setOf_isolated_points'`. Their union is
  countable; `Countable.measure_zero` closes the goal.
- **Hypotheses**: `ContinuousOn γ (Icc a b)` (named `_hγ`, unused);
  differentiability and non-vanishing derivative off `P`.
- **Uses-from-project**: `Set.countable_setOf_isolated_points'` (above).
- **Used by**: `preimage_finset_measure_zero_of_deriv_ne_zero` (next), and
  any CPV / generalised-residue argument needing measure-zero preimage of
  singularities.
- **Visibility**: public `theorem`; root namespace.
- **Lines**: 49-79.
- **Notes**: ~31-line proof. Uses `eventually_nhdsWithin_iff` to extract
  an `ε`-ball in which `γ ≠ z₀` off the singleton `{t₀}`.

## theorem `preimage_finset_measure_zero_of_deriv_ne_zero`
- **Type**: For a `Finset ℂ` of points `S` and the same data as above:
  `volume {t ∈ Icc a b | γ t ∈ ↑S} = 0`.
- **What**: Preimage of a finite set of points under a piecewise-C¹
  immersion is measure-zero. (Finset upgrade of the singleton version.)
- **How**: Rewrite the set as a finite union
  `⋃ s ∈ ↑S, {t ∈ Icc a b | γ t = s}` via `Set.ext`, apply
  `measure_biUnion_null_iff` (countability of the finite-as-set witness),
  and finish with the singleton lemma
  `preimage_singleton_measure_zero_of_deriv_ne_zero` on each `s`.
- **Hypotheses**: `ContinuousOn γ`, differentiable off `P`, nonzero deriv
  off `P`.
- **Uses-from-project**:
  `preimage_singleton_measure_zero_of_deriv_ne_zero`.
- **Used by**: CPV / generalised residue arguments where the singular set is
  a finset of complex points.
- **Visibility**: public `theorem`; root namespace.
- **Lines**: 83-100.

## File Summary
Three public declarations in `noncomputable section`: one general-purpose
mathlib-style fact `Set.countable_setOf_isolated_points'`, and two
specialisations to piecewise-C¹ immersions:
`preimage_singleton_measure_zero_of_deriv_ne_zero` and its finset
extension `preimage_finset_measure_zero_of_deriv_ne_zero`. Together they
say: under a non-degenerate (`deriv ≠ 0`) piecewise-C¹ curve, the
parameter preimage of any finite set of complex points has measure 0,
which is the analytical foundation for "the CPV ignores how the curve
crosses a finite singular set" arguments. No `sorry`. Imports only
`ClassicalCPV` from the project (otherwise mathlib).
