# Cycles.lean Inventory

### `structure ClosedImmersion`
- **Type**: `ClosedImmersion : Type` with fields `basepoint : ℂ` and `immersion : PwC1Immersion basepoint basepoint`
- **What**: Bundle a closed piecewise C¹ immersion together with its basepoint so different loops can live in one type.
- **How**: Existentially-quantified basepoint inside a structure.
- **Hypotheses**: None (definition).
- **Uses from project**: [`PwC1Immersion`]
- **Used by**: `ClosedImmersion.toPath`, `ClosedImmersion.toPath_eq`, `ClosedImmersion.coe_eq`, `ClosedImmersion.mk'`, `ContourCycle`, `IsNullHomologousCycle`, all theorems involving cycles.
- **Visibility**: public
- **Lines**: 54-58
- **Notes**: None.

### `def ClosedImmersion.toPath`
- **Type**: `(γ : ClosedImmersion) : PiecewiseC1Path γ.basepoint γ.basepoint`
- **What**: Underlying piecewise C¹ path of a closed immersion.
- **How**: `γ.immersion.toPiecewiseC1Path`.
- **Hypotheses**: None.
- **Uses from project**: [`ClosedImmersion`, `PiecewiseC1Path`, `PwC1Immersion.toPiecewiseC1Path`]
- **Used by**: `ClosedImmersion.toPath_eq`, all definitions/theorems integrating over a cycle.
- **Visibility**: public
- **Lines**: 63-64
- **Notes**: None.

### `theorem ClosedImmersion.toPath_eq`
- **Type**: `(γ : ClosedImmersion) : γ.toPath = γ.immersion.toPiecewiseC1Path`
- **What**: Definitional unfolding lemma for `toPath`.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: [`ClosedImmersion.toPath`]
- **Used by**: `windingNumberCycle_eq_zero_outside`
- **Visibility**: public (`@[simp]`)
- **Lines**: 66-68
- **Notes**: None.

### `instance CoeFun ClosedImmersion`
- **Type**: `CoeFun ClosedImmersion (fun _ => ℝ → ℂ)`
- **What**: Allow a `ClosedImmersion` to be applied as `γ t` directly.
- **How**: Coerce via `γ.toPath.extendedPath`.
- **Hypotheses**: None.
- **Uses from project**: [`ClosedImmersion.toPath`, `PiecewiseC1Path.extendedPath`]
- **Used by**: `ClosedImmersion.coe_eq`
- **Visibility**: public
- **Lines**: 71-72
- **Notes**: None.

### `theorem ClosedImmersion.coe_eq`
- **Type**: `(γ : ClosedImmersion) : (γ : ℝ → ℂ) = γ.toPath.extendedPath`
- **What**: Definitional unfolding lemma for the coercion.
- **How**: `rfl`.
- **Hypotheses**: None.
- **Uses from project**: [`ClosedImmersion.toPath`, `PiecewiseC1Path.extendedPath`]
- **Used by**: unused in file
- **Visibility**: public (`@[simp]`)
- **Lines**: 74-76
- **Notes**: None.

### `def ClosedImmersion.mk'`
- **Type**: `{x : ℂ} (γ : PwC1Immersion x x) : ClosedImmersion`
- **What**: Wrap a closed `PwC1Immersion x x` into a `ClosedImmersion`.
- **How**: Set `basepoint := x` and `immersion := γ`.
- **Hypotheses**: None.
- **Uses from project**: [`ClosedImmersion`, `PwC1Immersion`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 79-82
- **Notes**: None.

### `abbrev ContourCycle`
- **Type**: `ContourCycle := ClosedImmersion →₀ ℤ`
- **What**: A contour cycle is a formal Z-linear combination of closed immersions.
- **How**: `Finsupp` abbreviation.
- **Hypotheses**: None.
- **Uses from project**: [`ClosedImmersion`]
- **Used by**: All cycle definitions and theorems below.
- **Visibility**: public
- **Lines**: 88-88
- **Notes**: None.

### `def contourIntegralCycle`
- **Type**: `(f : ℂ → ℂ) (Γ : ContourCycle) : ℂ`
- **What**: Contour integral of `f` over a cycle, extended by linearity: `Σ_γ n_γ · ∮_γ f`.
- **How**: `Γ.sum fun γ n => (n : ℂ) * γ.toPath.contourIntegral f`.
- **Hypotheses**: None.
- **Uses from project**: [`ContourCycle`, `ClosedImmersion.toPath`, `PiecewiseC1Path.contourIntegral`]
- **Used by**: `contourIntegralCycle_single`, `generalizedResidueTheorem_simplePoles_cycle_structural`, `contourIntegralCycle_single_mul`, `contourIntegralCycle_zero`
- **Visibility**: public
- **Lines**: 94-95
- **Notes**: None.

### `def windingNumberCycle`
- **Type**: `(Γ : ContourCycle) (z : ℂ) : ℂ`
- **What**: Winding number of a cycle around `z`, extended by linearity.
- **How**: `Γ.sum fun γ n => (n : ℂ) * generalizedWindingNumber γ.toPath z`.
- **Hypotheses**: None.
- **Uses from project**: [`ContourCycle`, `ClosedImmersion.toPath`, `generalizedWindingNumber`]
- **Used by**: `windingNumberCycle_single`, `windingNumberCycle_eq_zero_outside`, `sum_swap_winding_residue`, `generalizedResidueTheorem_simplePoles_cycle_structural`, `windingNumberCycle_isInt`, `windingNumberCycle_single_mul`, `windingNumberCycle_zero`
- **Visibility**: public
- **Lines**: 99-100
- **Notes**: None.

### `def IsNullHomologousCycle`
- **Type**: `(Γ : ContourCycle) (U : Set ℂ) : Prop`
- **What**: Each component of `Γ` is null-homologous in `U`.
- **How**: `∀ γ ∈ Γ.support, IsNullHomologous γ.immersion U`.
- **Hypotheses**: None.
- **Uses from project**: [`ContourCycle`, `IsNullHomologous`]
- **Used by**: `isNullHomologousCycle_single`, `windingNumberCycle_eq_zero_outside`, `IsNullHomologousCycle.add`, `isNullHomologousCycle_zero`
- **Visibility**: public
- **Lines**: 104-105
- **Notes**: None.

### `def cpvCycle`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (Γ : ContourCycle) : ℂ`
- **What**: Cauchy principal value of `f` over a cycle, extended by linearity.
- **How**: `Γ.sum fun γ n => (n : ℂ) * cauchyPVOn S f γ.toPath`.
- **Hypotheses**: None.
- **Uses from project**: [`ContourCycle`, `cauchyPVOn`, `ClosedImmersion.toPath`]
- **Used by**: `cpvCycle_single`, `cpvCycle_eq_sum`, `cpvCycle_zero`
- **Visibility**: public
- **Lines**: 108-109
- **Notes**: None.

### `theorem contourIntegralCycle_single`
- **Type**: `(f : ℂ → ℂ) (γ : ClosedImmersion) : contourIntegralCycle f (Finsupp.single γ 1) = γ.toPath.contourIntegral f`
- **What**: Single-curve cycle with multiplicity 1 reduces to ordinary contour integral.
- **How**: `Finsupp.sum_single_index` after unfolding.
- **Hypotheses**: None.
- **Uses from project**: [`contourIntegralCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 114-117
- **Notes**: None.

### `theorem windingNumberCycle_single`
- **Type**: `(γ : ClosedImmersion) (z : ℂ) : windingNumberCycle (Finsupp.single γ 1) z = generalizedWindingNumber γ.toPath z`
- **What**: Single-curve cycle's winding number equals the underlying generalized winding number.
- **How**: `Finsupp.sum_single_index` after unfolding.
- **Hypotheses**: None.
- **Uses from project**: [`windingNumberCycle`, `generalizedWindingNumber`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 120-124
- **Notes**: None.

### `theorem isNullHomologousCycle_single`
- **Type**: `(γ : ClosedImmersion) (U : Set ℂ) (h : IsNullHomologous γ.immersion U) : IsNullHomologousCycle (Finsupp.single γ 1) U`
- **What**: A null-homologous single curve yields a null-homologous singleton cycle.
- **How**: `Finsupp.support_single_ne_zero` reduces support to `{γ}`; rewrite hypothesis to match.
- **Hypotheses**: `IsNullHomologous γ.immersion U`.
- **Uses from project**: [`IsNullHomologous`, `IsNullHomologousCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 127-131
- **Notes**: None.

### `theorem cpvCycle_single`
- **Type**: `(S : Finset ℂ) (f : ℂ → ℂ) (γ : ClosedImmersion) : cpvCycle S f (Finsupp.single γ 1) = cauchyPVOn S f γ.toPath`
- **What**: Single-curve cycle's CPV equals the ordinary multi-point CPV.
- **How**: `Finsupp.sum_single_index` after unfolding.
- **Hypotheses**: None.
- **Uses from project**: [`cpvCycle`, `cauchyPVOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 134-137
- **Notes**: None.

### `theorem windingNumberCycle_eq_zero_outside`
- **Type**: `{U} (Γ) (h_null : IsNullHomologousCycle Γ U) {z} (hz : z ∉ U) : windingNumberCycle Γ z = 0`
- **What**: Null-homologous cycle has zero winding number outside `U`.
- **How**: Reduce to a `Finset.sum_eq_zero` where each term vanishes via `(h_null γ hγ).winding_zero z hz` and `mul_zero`.
- **Hypotheses**: `IsNullHomologousCycle Γ U`, `z ∉ U`.
- **Uses from project**: [`windingNumberCycle`, `IsNullHomologousCycle`, `ClosedImmersion.toPath_eq`, `IsNullHomologous.winding_zero`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 142-148
- **Notes**: None.

### `private theorem sum_swap_winding_residue`
- **Type**: `(Γ) (S) (f) : Σ_{γ ∈ Γ.support} Γ γ · Σ_{s ∈ S} 2πi · winding · residue = 2πi · Σ_{s ∈ S} windingNumberCycle Γ s · residue f s`
- **What**: Swap the order of summation to express the weighted residue sum as the cycle-level residue sum.
- **How**: `Finset.mul_sum`, `Finset.sum_comm`, then `Finset.sum_congr` plus `Finset.mul_sum`/`sum_mul` to extract the `2πi` factor; uses an inline `show`/`ring` to rearrange the multiplicands.
- **Hypotheses**: None.
- **Uses from project**: [`windingNumberCycle`, `generalizedWindingNumber`, `residue`]
- **Used by**: `generalizedResidueTheorem_simplePoles_cycle_structural`
- **Visibility**: private
- **Lines**: 154-170
- **Notes**: 17 lines.

### `theorem generalizedResidueTheorem_simplePoles_cycle_structural`
- **Type**: `(S) (f) (Γ) (h_comp : ∀ γ ∈ Γ.support, γ.toPath.contourIntegral f = Σ_{s ∈ S} 2πi · winding γ s · residue f s) : contourIntegralCycle f Γ = 2πi · Σ_{s ∈ S} windingNumberCycle Γ s · residue f s`
- **What**: Cycle-level generalized residue theorem at simple poles (structural form).
- **How**: Unfold `contourIntegralCycle` to a `Finsupp.sum`, rewrite each term via `h_comp`, then close with `sum_swap_winding_residue`.
- **Hypotheses**: Per-component residue identity `h_comp`.
- **Uses from project**: [`contourIntegralCycle`, `windingNumberCycle`, `generalizedWindingNumber`, `residue`, `sum_swap_winding_residue`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 180-192
- **Notes**: None.

### `theorem windingNumberCycle_isInt`
- **Type**: `(Γ) (z) (h_int : ∀ γ ∈ Γ.support, ∃ n : ℤ, generalizedWindingNumber γ.toPath z = ↑n) : ∃ n : ℤ, windingNumberCycle Γ z = ↑n`
- **What**: A cycle's winding number is an integer when each component's winding number is.
- **How**: `Finset.sum_induction` on the predicate "is an integer"; closed under addition (push_cast + ring), zero base case, multiplication step combines `Γ γ` with the component integer `m`.
- **Hypotheses**: Per-component integrality.
- **Uses from project**: [`windingNumberCycle`, `generalizedWindingNumber`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 198-214
- **Notes**: 17 lines.

### `theorem cpvCycle_eq_sum`
- **Type**: `(S) (f) (Γ) : cpvCycle S f Γ = Σ_{γ ∈ Γ.support} Γ γ · cauchyPVOn S f γ.toPath`
- **What**: CPV of a cycle expressed as a `Finset` sum over the support.
- **How**: `rfl` (definitional unfold of `Finsupp.sum`).
- **Hypotheses**: None.
- **Uses from project**: [`cpvCycle`, `cauchyPVOn`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 219-221
- **Notes**: None.

### `theorem IsNullHomologousCycle.add`
- **Type**: `{U Γ₁ Γ₂} (h₁ : IsNullHomologousCycle Γ₁ U) (h₂ : IsNullHomologousCycle Γ₂ U) : IsNullHomologousCycle (Γ₁ + Γ₂) U`
- **What**: Sum of null-homologous cycles is null-homologous.
- **How**: Reduce support membership to `Pi.add_apply`, case-split on `Γ₁ γ = 0`, dispatch to whichever cycle has nonzero coefficient at `γ`.
- **Hypotheses**: Both cycles null-homologous in `U`.
- **Uses from project**: [`IsNullHomologousCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 227-237
- **Notes**: 11 lines.

### `def ContourCycle.ofSingle`
- **Type**: `(γ : ClosedImmersion) (n : ℤ) : ContourCycle`
- **What**: Singleton cycle with multiplicity `n`.
- **How**: `Finsupp.single γ n`.
- **Hypotheses**: None.
- **Uses from project**: [`ClosedImmersion`, `ContourCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 242-243
- **Notes**: None.

### `theorem contourIntegralCycle_single_mul`
- **Type**: `(f) (γ) (n : ℤ) : contourIntegralCycle f (Finsupp.single γ n) = (n : ℂ) * γ.toPath.contourIntegral f`
- **What**: Singleton cycle with arbitrary multiplicity has its contour integral scaled by `n`.
- **How**: `Finsupp.sum_single_index` + `simp`.
- **Hypotheses**: None.
- **Uses from project**: [`contourIntegralCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 246-251
- **Notes**: None.

### `theorem windingNumberCycle_single_mul`
- **Type**: `(γ) (z) (n : ℤ) : windingNumberCycle (Finsupp.single γ n) z = (n : ℂ) * generalizedWindingNumber γ.toPath z`
- **What**: Singleton cycle winding number scales with multiplicity.
- **How**: `Finsupp.sum_single_index` + `simp`.
- **Hypotheses**: None.
- **Uses from project**: [`windingNumberCycle`, `generalizedWindingNumber`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 254-259
- **Notes**: None.

### `theorem contourIntegralCycle_zero`
- **Type**: `(f) : contourIntegralCycle f 0 = 0`
- **What**: Contour integral of the zero cycle is zero.
- **How**: `simp [contourIntegralCycle, Finsupp.sum]`.
- **Hypotheses**: None.
- **Uses from project**: [`contourIntegralCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 264-266
- **Notes**: None.

### `theorem windingNumberCycle_zero`
- **Type**: `(z) : windingNumberCycle 0 z = 0`
- **What**: Winding number of the zero cycle is zero.
- **How**: `simp [windingNumberCycle, Finsupp.sum]`.
- **Hypotheses**: None.
- **Uses from project**: [`windingNumberCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 269-271
- **Notes**: None.

### `theorem isNullHomologousCycle_zero`
- **Type**: `(U) : IsNullHomologousCycle 0 U`
- **What**: The zero cycle is null-homologous in any set.
- **How**: Support of zero is empty, derive contradiction from membership via `simp`.
- **Hypotheses**: None.
- **Uses from project**: [`IsNullHomologousCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 274-277
- **Notes**: None.

### `theorem cpvCycle_zero`
- **Type**: `(S) (f) : cpvCycle S f 0 = 0`
- **What**: CPV of the zero cycle is zero.
- **How**: `simp [cpvCycle, Finsupp.sum]`.
- **Hypotheses**: None.
- **Uses from project**: [`cpvCycle`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 280-282
- **Notes**: None.

## File Summary
Introduces the contour-cycle formalism: `ClosedImmersion` bundles a closed piecewise C¹ immersion with its basepoint, and `ContourCycle := ClosedImmersion →₀ ℤ` is a formal Z-linear combination. Extends contour integration, generalized winding number, null-homologousness, and CPV by linearity. Provides bridge lemmas for singletons, the cycle-level generalized residue theorem at simple poles, integrality of cycle winding numbers, additivity of null-homologousness, and zero-cycle vanishing lemmas. Uses `open scoped Classical` to make `Finsupp` work without decidable equality. No sorries, no axioms.
