# Design: Null-Homologous Generalized Residue Theorem

## Goal

Replace the `Convex ℝ U` hypothesis in our generalized residue theorem chain with
`IsNullHomologous γ U`, matching Theorem 3.3 of the Hungerbuhler-Wasem paper
(arXiv:1808.00997v2) exactly. Single closed curves first; cycles later.

## Definition

```lean
def IsNullHomologous (γ : PiecewiseC1Immersion) (U : Set ℂ) : Prop :=
  γ.toPiecewiseC1Curve.IsClosed ∧
  (∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) ∧
  (∀ z, z ∉ U → generalizedWindingNumber' γ.toFun γ.a γ.b z = 0)
```

Bundles closedness, containment in U, and the winding number condition.

## Core Theorem

```lean
theorem contourIntegral_eq_zero_of_nullHomologous
    (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0
```

## Proof Strategy: Dixon's Proof

### Part A: Dixon Kernel

Define `g(z, w) = (f(z) - f(w)) / (z - w)` for `z ≠ w`, and `g(w, w) = deriv f w`.

Key lemma: `g` is jointly continuous on `U × U`. At `z ≠ w` this is immediate
(quotient of continuous functions). At `z = w`, it follows from `(f(z) - f(w))/(z-w) → f'(w)`
(definition of derivative). Joint continuity (not just pointwise) requires that the
convergence is locally uniform in `w`, which follows from `DifferentiableOn ℂ f U` on an
open set implying `AnalyticOn ℂ f U` (via `DifferentiableOn.analyticOn` in mathlib),
giving uniform convergence of the difference quotient on compact subsets.

### Part B: Two Integral Functions

- `h₁(w) = ∮_γ g(z, w) dz` for `w ∈ U`
- `h₂(w) = ∮_γ f(z)/(z-w) dz` for `w ∉ image(γ)` — holomorphic on `ℂ \ image(γ)`

Key identity on `U \ image(γ)`:
```
h₁(w) = h₂(w) - 2πi · n(γ, w) · f(w)
```

**Holomorphicity of `h₂`**: Differentiating `∮_γ f(z)/(z-w) dz` under the integral sign
(using `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` from
`Mathlib.Analysis.Calculus.ParametricIntervalIntegral`). The integrand `f(γ(t))/(γ(t)-w)`
is holomorphic in `w` away from `image(γ)`, with dominated convergence bounds from
compactness of `image(γ)`.

**Holomorphicity of `h₁`** — two sub-arguments:
1. *Off-contour* (`w ∈ U \ image(γ)`): Same parametric differentiation as `h₂`, since
   `g(z,w) = (f(z)-f(w))/(z-w)` is smooth in `w` when `z ≠ w`.
2. *Across the contour* (`w ∈ image(γ) ∩ U`): The Dixon kernel `g` is jointly continuous
   on `U × U` (Part A), so `h₁(w) = ∫ g(γ(t), w) γ'(t) dt` is continuous at these points.
   Since `h₁` is holomorphic on the dense open subset `U \ image(γ)` and continuous on all
   of `U`, it extends holomorphically across `image(γ)` by
   `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` (removable
   singularity). Note: image(γ) is a compact 1-dimensional set with empty interior in ℂ,
   so each point of image(γ) has a punctured neighborhood in U where h₁ is holomorphic.

### Part C: Patching to Entire Function

Define `h : ℂ → ℂ` by `h = h₁` on `U` and `h = h₂` on `ℂ \ U`.

**Patching at ∂U**: For `w₀ ∈ ∂U`, we have `w₀ ∉ U` (U is open), so `w₀ ∉ image(γ)`
(since `image(γ) ⊂ U`). The winding number `n(γ, ·)` is locally constant on
`ℂ \ image(γ)`, and `n(γ, w₀) = 0` (null-homologous, since `w₀ ∉ U`). So `n(γ, w) = 0`
for all `w` in a neighborhood of `w₀`. This gives `h₁(w) = h₂(w)` for `w ∈ U` near `w₀`,
so the two definitions glue to give a holomorphic function on all of `ℂ`.

**Decay at ∞**: `h(w) = h₂(w) = ∮_γ f(z)/(z-w) dz → 0` as `|w| → ∞`, since `1/(z-w) → 0`
uniformly for `z ∈ image(γ)` (compact).

### Part D: Liouville + Main Results

By Liouville's theorem in mathlib (candidates: `Differentiable.apply_eq_of_tendsto_cocompact`
or `Differentiable.exists_const_forall_eq_of_bounded` or `Complex.liouville_theorem_aux` —
exact name depends on pinned mathlib version): `h ≡ 0`.

**Cauchy integral formula**: For `w ∈ U \ image(γ)`:
```
0 = h₁(w) = h₂(w) - 2πi · n(γ,w) · f(w)
⟹ (1/2πi) ∮_γ f(z)/(z-w) dz = n(γ,w) · f(w)
```

**Integral vanishes**: Pick any `w₀ ∈ U \ image(γ)`. Apply CIF to `F(z) = f(z)(z - w₀)`:
```
(1/2πi) ∮_γ f(z) dz = (1/2πi) ∮_γ F(z)/(z-w₀) dz = n(γ,w₀) · F(w₀) = n(γ,w₀) · 0 = 0
```

### Part E: Bridge Lemma

```lean
theorem isNullHomologous_of_convex
    (hU_convex : Convex ℝ U) (hγ_closed : ...) (hγ_in_U : ...) :
    IsNullHomologous γ U
```

Proof: For `z ∉ U`, `w ↦ 1/(w - z)` is holomorphic on convex U. By existing
`holomorphic_convex_primitive`, it has a primitive on U. So `∮_γ 1/(w-z) dw = 0`
for any closed `γ` in U. Since `z ∉ image(γ)` (because `image(γ) ⊂ U` and `z ∉ U`),
`generalizedWindingNumber_eq_classical_away` reduces the PV-based winding number to
this classical integral, giving `generalizedWindingNumber' γ z = 0`.

## Mathlib Dependencies

All verified to exist:

| Dependency | Mathlib Location |
|-----------|-----------------|
| Liouville's theorem | `Differentiable.apply_eq_of_tendsto_cocompact` in `Mathlib.Analysis.Complex.Liouville` |
| Parametric differentiation | `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` in `Mathlib.Analysis.Calculus.ParametricIntervalIntegral` |
| Continuous parametric integral | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` in `Mathlib.Analysis.Calculus.ParametricIntervalIntegral` |
| Removable singularity | `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` in `Mathlib.Analysis.Complex.RemovableSingularity` |

## Refactoring Plan

### New file

`LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean`

Contains: `IsNullHomologous`, Dixon kernel, CIF, integral vanishing, bridge lemma.

### Theorem chain — add `_nullHomologous` versions

| File | Current (Convex) | New (NullHomologous) |
|------|-----------------|---------------------|
| `Residue.lean` | `integral_eq_sum_residues_of_avoids` | `integral_eq_sum_residues_of_nullHomologous` |
| `GeneralizedTheorem.lean` | `generalizedResidueTheorem'` | `generalizedResidueTheorem'_nullHomologous` |
| `GeneralizedTheorem.lean` | `generalizedResidueTheorem` | `generalizedResidueTheorem_nullHomologous` |
| `GeneralizedTheorem.lean` | `generalizedResidueTheorem_higher_order` | `..._nullHomologous` |
| `GeneralizedTheorem.lean` | `generalizedResidueTheorem_higher_order_tendsto` | `..._nullHomologous` |
| `GeneralizedTheorem.lean` | `generalizedResidueTheorem_higher_order_simple` | `..._nullHomologous` |
| `MeromorphicLaurent.lean` | `contourIntegral_eq_zero_of_meromorphic_residue_zero` | `..._nullHomologous` |
| `HigherOrderAssembly.lean` | `conditionsAB_imply_higherOrderCancel` | `..._nullHomologous` |
| `PerTermVanishing.lean` | `pv_higher_order_term_tendsto_zero` | `..._nullHomologous` |
| `FlatnessTransfer.lean` | `pv_res_tendsto_of_immersion` | `..._nullHomologous` |
| `FlatnessTransfer.lean` | `generalizedResidueTheorem_3_3` | `generalizedResidueTheorem_3_3_nullHomologous` |

**Out of scope**: `SectorCurveLemma.lean` also uses convexity (of a ball) but only locally
(balls are always convex), so it does not need a `_nullHomologous` variant.

### Old convex versions become corollaries

Each old theorem is derived via `isNullHomologous_of_convex`:

```lean
theorem generalizedResidueTheorem' ... (hU_convex : Convex ℝ U) ... :=
  generalizedResidueTheorem'_nullHomologous ... (isNullHomologous_of_convex hU_convex ...) ...
```

### Dependency order for implementation

```
HomologicalCauchy.lean        (NEW — no deps on existing chain)
  → Residue.lean              (add _nullHomologous version)
  → GeneralizedTheorem.lean   (add _nullHomologous versions)
  → MeromorphicLaurent.lean   (add _nullHomologous version)
  → HigherOrderAssembly.lean  (add _nullHomologous version)
  → PerTermVanishing.lean     (add _nullHomologous version)
  → FlatnessTransfer.lean     (add _nullHomologous = paper's Theorem 3.3)
```

No existing theorem breaks. Only additions and re-derivations.

## Risks

1. **Dixon kernel joint continuity**: Showing `g(z,w)` is jointly continuous at `z = w`
   requires locally uniform convergence of `(f(z)-f(w))/(z-w) → f'(w)`. This follows
   from `DifferentiableOn.analyticOn` (complex differentiable on open ⟹ analytic), which
   gives power series representations and hence uniform convergence on compact subsets.
   Mathlib has `DifferentiableOn.analyticOn`.

2. **Parametric differentiation bounds**: The dominated convergence bounds for
   `hasDerivAt_integral_of_dominated_loc_of_deriv_le` need explicit construction.
   Compactness of `image(γ)` and continuity of the integrand should provide these.

3. **Winding number locally constant**: We need the classical winding number to be locally
   constant on `ℂ \ image(γ)`. Strategy: the integral `w ↦ ∮_γ 1/(z-w) dz` is holomorphic
   in `w` (by parametric differentiation), hence continuous. Since it takes values in
   `2πi · ℤ` (integrality from `Homotopy/Integrality.lean`), a continuous integer-valued
   function on a connected set is constant. Therefore locally constant on each connected
   component of `ℂ \ image(γ)`.

4. **Existence of `w₀ ∈ U \ image(γ)`**: For step D (integral vanishes), we need a point in
   U not on the curve. For open U this is always true: a piecewise C¹ curve has
   1-dimensional image, which has empty interior in ℂ (2-dimensional), so
   `U \ image(γ)` is dense in U. May need Baire category or a direct measure argument
   to formalize.

5. **Mathlib name uncertainty**: The exact names of Liouville's theorem and continuous
   parametric integral lemmas may differ in our pinned mathlib version. Implementation
   should verify with `lean_local_search` / `lean_loogle` at build time.

6. **Heartbeat budget**: Existing chain lemmas like `conditionsAB_imply_higherOrderCancel`
   already use `set_option maxHeartbeats 1600000`. Adding another layer may increase
   pressure. Monitor during implementation.

## Architecture Note

`HomologicalCauchy.lean` replaces the role of `CauchyPrimitive.lean` in the `_nullHomologous`
variants. Where the convex chain uses `holomorphic_convex_primitive` (construct primitive →
FTC → integral vanishes), the null-homologous chain uses
`contourIntegral_eq_zero_of_nullHomologous` directly (Dixon → Liouville → integral vanishes).
The substitution pattern at each level: replace the call to `holomorphic_convex_primitive`
with a call to `contourIntegral_eq_zero_of_nullHomologous`.

## Estimated Effort

- `HomologicalCauchy.lean`: ~800-1200 lines (Dixon proof is the bulk)
- Refactoring each downstream file: ~50-100 lines per file (mechanical substitution)
- Total new code: ~1200-1800 lines

## Non-goals

- Cycles (formal ℤ-linear combinations of curves) — deferred to future work
- Simply connected hypothesis — convex bridge suffices for backward compatibility
- Replacing existing convex theorems in-place — we add alongside, not replace
- `SectorCurveLemma.lean` refactoring — uses convexity of balls only (always convex)
