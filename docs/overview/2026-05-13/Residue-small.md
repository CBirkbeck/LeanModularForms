# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/Residue.lean

## def `HasSimplePoleAt`
- **Type**: `(f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ c : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z`.
- **What**: Predicate "`f` has a simple pole at `z₀`": there exist a
  coefficient `c` and an analytic part `g` such that
  `f(z) = c/(z-z₀) + g(z)` on a punctured neighbourhood of `z₀`.
- **How**: Existential statement, no proof body.
- **Hypotheses**: n/a (definition).
- **Uses-from-project**: imports `GeneralizedWindingNumber` (for the
  downstream theorem) and mathlib's
  `MeasureTheory.Integral.CircleIntegral`.
- **Used by**: `HasSimplePoleAt.coeff`, `HasSimplePoleAt.regularPart`,
  `hasSimplePoleAt_of_decomposition`, and any consumer talking about
  simple-pole decompositions.
- **Visibility**: public `def`; root namespace.
- **Lines**: 41-43.

## def `HasSimplePoleAt.coeff`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) → ℂ`.
- **What**: The pole coefficient `c` in the simple-pole decomposition,
  i.e. the residue at `z₀`.
- **How**: `h.choose` from the existential.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses-from-project**: `HasSimplePoleAt`.
- **Used by**: `HasSimplePoleAt.eventually_eq`; downstream residue
  computations.
- **Visibility**: public `def`; namespace `HasSimplePoleAt`.
- **Lines**: 46-47.

## def `HasSimplePoleAt.regularPart`
- **Type**: `{f : ℂ → ℂ} {z₀ : ℂ} (h : HasSimplePoleAt f z₀) → ℂ → ℂ`.
- **What**: The analytic part `g` in the decomposition.
- **How**: `h.choose_spec.choose`.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses-from-project**: `HasSimplePoleAt`.
- **Used by**: `HasSimplePoleAt.regularPart_analyticAt`,
  `HasSimplePoleAt.eventually_eq`.
- **Visibility**: public `def`; namespace `HasSimplePoleAt`.
- **Lines**: 50-52.

## theorem `HasSimplePoleAt.regularPart_analyticAt`
- **Type**: `(h : HasSimplePoleAt f z₀) → AnalyticAt ℂ h.regularPart z₀`.
- **What**: The regular part is analytic at the pole point.
- **How**: Direct projection `h.choose_spec.choose_spec.1`.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses-from-project**: `HasSimplePoleAt`, `HasSimplePoleAt.regularPart`.
- **Used by**: Downstream identification of the residue and analytic part.
- **Visibility**: public; namespace `HasSimplePoleAt`.
- **Lines**: 54-56.

## theorem `HasSimplePoleAt.eventually_eq`
- **Type**: `(h : HasSimplePoleAt f z₀)
  → ∀ᶠ z in 𝓝[≠] z₀, f z = h.coeff / (z - z₀) + h.regularPart z`.
- **What**: The defining equation of the simple-pole decomposition,
  filtered to a punctured neighbourhood of `z₀`.
- **How**: `h.choose_spec.choose_spec.2`.
- **Hypotheses**: `HasSimplePoleAt f z₀`.
- **Uses-from-project**: `HasSimplePoleAt`, `coeff`, `regularPart`.
- **Used by**: Downstream meromorphic / residue arguments.
- **Visibility**: public; namespace `HasSimplePoleAt`.
- **Lines**: 58-61.

## theorem `hasSimplePoleAt_of_decomposition`
- **Type**: For `g` analytic at `z₀` and `f =ᶠ[𝓝[≠] z₀] c/(z-z₀) + g z`:
  `HasSimplePoleAt f z₀`.
- **What**: Constructor: a simple pole can be assembled from explicit
  decomposition data.
- **How**: One-line `⟨c, g, hg, hf⟩`.
- **Hypotheses**: `AnalyticAt ℂ g z₀`; eventual equality on `𝓝[≠] z₀`.
- **Uses-from-project**: `HasSimplePoleAt`.
- **Used by**: Producers of simple poles.
- **Visibility**: public; root namespace.
- **Lines**: 64-67.

## def `residue`
- **Type**: `(f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun r => (2 * ↑π * I)⁻¹ * ∮ z in C(z₀, r), f z`.
- **What**: Residue of `f` at `z₀` as the limit of normalised circle
  integrals around `z₀` as `r → 0⁺`. Coincides with the simple-pole
  coefficient when one exists.
- **How**: `limUnder` of the small-radius circle-integral functional.
- **Hypotheses**: n/a.
- **Uses-from-project**: mathlib `CircleIntegral`; the residue may also
  feed into downstream Hungerbühler/Wasem residue-theorem statements.
- **Used by**: Downstream generalised-residue theorems.
- **Visibility**: public `def`; root namespace.
- **Lines**: 73-74.

## theorem `hasCauchyPV_simple_pole`
- **Type**: `{s c : ℂ} {γ : PiecewiseC1Path x y} {w : ℂ}
  (hw : HasGeneralizedWindingNumber γ s w)
  → HasCauchyPV (fun z => c / (z - s)) γ s (2 * π * I * w * c)`.
- **What**: The Cauchy principal value of the simple-pole integrand
  `c/(z-s)` along `γ` equals `2πi · w · c`, where `w` is the generalised
  winding number — the link between residues and winding numbers.
- **How**: Rewrites `c / (z - s)` as `c * (z - s)⁻¹` and rearranges
  constants so the answer reads `c * (2πi w)`; closes via
  `HasGeneralizedWindingNumber.const_mul c`.
- **Hypotheses**: `HasGeneralizedWindingNumber γ s w`.
- **Uses-from-project**: `PiecewiseC1Path`, `HasGeneralizedWindingNumber`,
  `HasCauchyPV`, `HasGeneralizedWindingNumber.const_mul` (from the
  `GeneralizedWindingNumber` import).
- **Used by**: Residue-theorem assembly for simple poles.
- **Visibility**: public `theorem`; root namespace.
- **Lines**: 84-89.

## theorem `hasCauchyPV_simple_pole_zero`
- **Type**: `(hw : HasGeneralizedWindingNumber γ s w)
  → HasCauchyPV (fun z => (0 : ℂ) / (z - s)) γ s 0`.
- **What**: Trivial case of the simple-pole CPV with zero coefficient.
- **How**: `simpa` from `hasCauchyPV_simple_pole` at `c = 0`.
- **Hypotheses**: same.
- **Uses-from-project**: `hasCauchyPV_simple_pole`.
- **Used by**: Edge-case discharge in residue assemblies.
- **Visibility**: public; root namespace.
- **Lines**: 92-95.

## File Summary
Eight public declarations (three `def`, five `theorem`) under
`noncomputable section`. Establishes the `HasSimplePoleAt` predicate
with its `coeff`/`regularPart` accessors and constructor, the residue
defined via small-circle integral limit, and the key bridge
`hasCauchyPV_simple_pole`: `CPV(c/(z-s)) = 2πi·w·c` where `w` is the
generalised winding number. Together this is the entry point that
connects simple-pole structure to CPV / generalised winding numbers.
Imports `GeneralizedWindingNumber` from the project plus mathlib's
circle-integral library. No `sorry`. References Hungerbühler–Wasem in
the header.
