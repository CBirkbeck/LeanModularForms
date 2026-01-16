# Blueprint for Filling Remaining Sorries

## Overview

This blueprint maps the remaining sorries in `GeneralizedResidueTheorem.lean` to the corresponding
results in Isabelle's HOL-Complex_Analysis library, providing a roadmap for completion.

**Key Insight**: Our approach using Cauchy principal values differs from Isabelle's classical approach.
Isabelle requires paths to avoid singularities and uses homotopy/wiggle relations. Our PV approach
handles singularities on contours directly, making some Isabelle lemmas unnecessary while requiring
different foundational work.

---

## Category 1: Finiteness of Zeros (Lines 371, 475, 914)

### Sorries
- `zeros_finite_left_of_partition` (line 371)
- `zeros_finite_right_of_partition` (line 475)
- `piecewiseC1Immersion_finite_zeros` (line 914)

### Mathematical Content
Show that a piecewise C^1 immersion has only finitely many zeros (points where γ(t) = z₀).

### Isabelle Parallel
**Not directly in Isabelle** - Isabelle assumes paths avoid singularities. However, related results:
- `finite_imp_compact` in `HOL-Analysis`
- The isolation of zeros for analytic functions

### Proof Strategy
1. **On each smooth segment** (away from partition points):
   - The derivative is nonzero (immersion condition)
   - By inverse function theorem, zeros are isolated
   - Compact interval + isolated points → finite

2. **Near partition points**:
   - Use one-sided derivative limits (assumed nonzero in `PiecewiseC1Immersion'`)
   - Apply same isolation argument from each side

### Dependencies
- `zeros_uniformly_separated` (✅ proven)
- `zeros_finite_on_interval` (✅ proven)
- One-sided derivative limit assumptions in `PiecewiseC1Immersion'`

### Estimated Difficulty: Medium
The structure is in place; main gap is handling behavior at partition points.

---

## Category 2: Principal Value Integrability (Line 625)

### Sorry
- `cauchyPrincipalValue_add` integrability condition (line 625)

### Mathematical Content
Show that if PV limits exist for f and g separately, then the sum of integrands is integrable.

### Isabelle Parallel
- `has_contour_integral_add` in `Contour_Integration.thy`
- `contour_integrable_add` for sum of integrable functions

### Proof Strategy
1. The integrand for f+g equals sum of integrands (already proven: `cauchyPrincipalValueIntegrand_add`)
2. Each integrand is bounded on [a,b] minus small neighborhoods of singularities
3. Use `IntervalIntegrable.add` from mathlib

### Dependencies
- `MeasureTheory.IntervalIntegrable` from mathlib
- Boundedness of integrands away from singularities

### Estimated Difficulty: Easy
Standard measure theory; main work is setting up the right hypotheses.

---

## Category 3: Homotopy Invariance (Lines 1668, 2522-2537)

### Sorries
- `homotopy_pv_integral_eq` final step (line 1668)
- `windingNumber_homotopy_invariant` (lines 2522-2537)

### Mathematical Content
If two curves Γ and γ are homotopic (in the sense that H(t,s) ≠ 0 for interior t),
their PV integrals/winding numbers agree.

### Isabelle Parallel
**Key file**: `Winding_Numbers.thy`
- `winding_number_homotopy_paths` - winding number invariant under homotopy
- `contour_integral_unique` - integral depends only on homotopy class

**Key file**: `Cauchy_Integral_Theorem.thy`
- `Cauchy_theorem_homotopic_paths` - integrals agree for homotopic paths

### Proof Strategy
1. **Parametrize the homotopy**: H : [a,b] × [0,1] → ℂ
2. **Show integral is continuous in s**:
   - Use continuity of H and dominated convergence
3. **Show integral is locally constant**:
   - On any interval where H(t,s) ≠ 0, the integrand varies continuously
   - The PV limit commutes with the s-derivative
4. **Conclude**: Continuous + locally constant on connected [0,1] → constant

### Dependencies
- Dominated convergence theorem (from mathlib)
- Continuity of contour integrals under perturbation

### Estimated Difficulty: Hard
This is a deep result. May need to develop intermediate lemmas about continuous dependence of PV integrals.

---

## Category 4: Classical Winding Number is Integer (Line 2657)

### Sorry
- `generalizedWindingNumber_eq_classical` final step (line 2657)

### Mathematical Content
When a closed curve avoids z₀, the winding number ∮ dz/(z-z₀) / (2πi) is an integer.

### Isabelle Parallel
**Key file**: `Winding_Numbers.thy`
- `winding_number_integer` - winding number of closed path is integer
- `winding_number_exp_2pi` - exp(2πi · n) = 1 characterization

**Key file**: `Cauchy_Integral_Formula.thy`
- The winding number counts how many times the curve wraps around z₀

### Proof Strategy
**Option A: Use mathlib's winding number**
- Mathlib has `Complex.windingNumber` in `Mathlib.Analysis.Complex.CauchyIntegral`
- Show our `generalizedWindingNumber` equals mathlib's when curve avoids z₀
- Use mathlib's `winding_number_integer`

**Option B: Direct proof via logarithm**
1. Define θ(t) = arg(γ(t) - z₀) (continuous branch)
2. Show ∮ dz/(z-z₀) = i·(θ(b) - θ(a))
3. For closed curve: θ(b) - θ(a) = 2πn for some n ∈ ℤ

### Dependencies
- `Mathlib.Analysis.Complex.CauchyIntegral` - mathlib's winding number
- Continuity of argument on curves avoiding origin

### Estimated Difficulty: Medium
The result is standard; main work is connecting our definition to mathlib's.

---

## Category 5: Winding Number Decomposition (Line 1780)

### Sorry
- `generalizedWindingNumber_decomposition` non-empty case (line 1780)

### Mathematical Content
When γ passes through z₀ at times t₁,...,tₙ:
```
n_{z₀}(γ) = n_{z₀}(γ̃) + Σᵢ αᵢ/(2π)
```
where γ̃ avoids z₀ and αᵢ are angles at intersection points.

### Isabelle Parallel
**Not directly in Isabelle** - Isabelle requires paths to avoid singularities.
However, related:
- Path decomposition lemmas in `Contour_Integration.thy`
- `contour_integral_join` for splitting paths

### Proof Strategy
1. **Split integral at zeros**: Use `integral_add_adjacent_intervals`
2. **Near each zero tᵢ**:
   - The local curve is homotopic to a model sector (by `homotopy_pv_integral_eq`)
   - Apply `generalizedWindingNumber_modelSector` to get αᵢ/(2π)
3. **Away from zeros**:
   - The curve avoids z₀
   - Classical integral theory applies
4. **Combine**: Sum all contributions

### Dependencies
- `generalizedWindingNumber_modelSector` (✅ proven)
- `homotopy_pv_integral_eq` (needs Category 3)
- `integral_add_adjacent_intervals` (from mathlib)
- Proper definition of angles at intersection points

### Estimated Difficulty: Hard
Requires construction of γ̃ and careful bookkeeping of angle contributions.

---

## Category 6: Asymptotic Estimates (Lines 1872, 1951, 1981, 1992, 2083, 2144)

### Sorries
- `numerator_O_t_squared` (line 1872)
- `denominator_Theta_t_squared` (line 1951)
- Various Taylor expansion sorries (lines 1981, 1992, 2083, 2144)

### Mathematical Content
For a C^{1,1} curve γ with γ(t₀) = 0:
- Numerator x·ẏ - y·ẋ = O(t²)
- Denominator x² + y² = Θ(t²)
- Hence integrand is O(1), i.e., bounded

### Isabelle Parallel
These are standard calculus estimates, not specific to complex analysis.
Related mathlib:
- `Asymptotics.IsBigO` and `Asymptotics.IsLittleO`
- Taylor expansion lemmas in `Mathlib.Analysis.Calculus.Taylor`

### Proof Strategy
1. **Use Taylor expansion**:
   - x(t) = (t-t₀)·ẋ(t₀) + O((t-t₀)²)
   - y(t) = (t-t₀)·ẏ(t₀) + O((t-t₀)²)
2. **Compute products**:
   - x·ẏ - y·ẋ involves (t-t₀)² terms
3. **Use immersion condition**:
   - ẋ(t₀)² + ẏ(t₀)² > 0 ensures denominator ~ c·(t-t₀)²

### Dependencies
- Taylor's theorem from mathlib
- Lipschitz condition on derivatives (C^{1,1})
- Immersion condition (derivative nonzero)

### Estimated Difficulty: Medium
Standard calculus with careful bookkeeping.

---

## Category 7: Residue Theory (Lines 2265-2383, 2506-2511)

### Sorries
- `pv_integral_z_power_n` (line 2265, 2278)
- `laurent_term_compatibility` (line 2289, 2313, 2319)
- `compatible_laurent_residue_formula` (line 2377, 2383)
- `generalizedResidueTheorem` (lines 2506, 2511)

### Mathematical Content
The generalized residue theorem:
```
PV ∮_γ f = 2πi · Σₛ n_s(γ) · res_s(f)
```

### Isabelle Parallel
**Key file**: `Residue_Theorem.thy`
- `Residue_theorem` - main residue theorem
- `Cauchy_theorem_singularities` - handles multiple singularities

**Key file**: `Complex_Residues.thy`
- `residue_simple_pole` - residue at simple pole = lim (z-z₀)f(z)
- `residue_integral` - residue via contour integral

### Proof Strategy
1. **For simple poles**:
   - f(z) = c/(z-z₀) + g(z) where g is holomorphic
   - res_z₀(f) = c
   - PV∮f = PV∮(c/(z-z₀)) + ∮g = 2πi·n·c + 0

2. **General case**:
   - Decompose f into singular and regular parts near each singularity
   - Sum contributions using linearity of PV

3. **Laurent compatibility**:
   - For flatness order p/q, certain Laurent coefficients must vanish
   - This ensures PV exists

### Dependencies
- `generalizedWindingNumber_modelSector` (✅ proven)
- `cauchyPrincipalValue_add` (Category 2)
- Laurent series from mathlib
- Cauchy integral formula from mathlib

### Estimated Difficulty: Hard
Core theorem of the file; requires all previous categories.

---

## Category 8: Valence Formula (Lines 2888, 2929)

### Sorries
- `valenceFormula` (line 2888)
- `valenceFormula_classical` (line 2929)

### Mathematical Content
For a modular form f of weight k:
```
ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_p ord_p(f) = k/12
```

### Isabelle Parallel
**Not in Isabelle** - This is specific to modular forms, not general complex analysis.

### Proof Strategy
1. **Apply generalized residue theorem** to f'/f on fundamental domain boundary
2. **Compute winding numbers**:
   - At interior points: n = 1
   - At i: n = 1/2 (boundary has angle π)
   - At ρ: n = 1/3 (boundary has angle 2π/3)
   - At ∞: contribution from cusp
3. **Use modular transformation** to relate contributions from identified edges

### Dependencies
- `generalizedResidueTheorem` (Category 7)
- Modular forms theory from `Mathlib.NumberTheory.ModularForms`
- Geometry of fundamental domain
- Order of vanishing computations

### Estimated Difficulty: Very Hard
Requires deep integration of complex analysis with modular forms theory.

---

## Category 9: Zeppelin Curve Example (Line 2580)

### Sorry
- `zeppelinCurve_windingNumber` (line 2580)

### Mathematical Content
The zeppelin curve γ(t) = sin(t) + i·sin(2t) has winding number 3/2 around the origin.

### Proof Strategy
1. **Direct computation**:
   - The curve passes through origin at t = π
   - Apply decomposition: n = n(γ̃) + α/(2π)
   - Compute angle α from tangent directions

2. **Or symbolic**:
   - Use explicit formula for winding number integrand
   - Evaluate the integral

### Dependencies
- `generalizedWindingNumber_decomposition` (Category 5)
- Trigonometric identities

### Estimated Difficulty: Medium
Concrete computation; good test case for the theory.

---

## Recommended Implementation Order

### Phase A: Foundations (can be done in parallel)
1. **Category 2**: PV integrability - Easy, unblocks other proofs
2. **Category 6**: Asymptotic estimates - Medium, needed for boundedness
3. **Category 1**: Finiteness of zeros - Medium, needed for decomposition

### Phase B: Core Winding Number Theory
4. **Category 4**: Classical winding number is integer - Medium
5. **Category 3**: Homotopy invariance - Hard, but can use sorry if needed
6. **Category 5**: Winding number decomposition - Hard

### Phase C: Residue Theorem
7. **Category 7**: Residue theory - Hard, main theorem

### Phase D: Applications
8. **Category 9**: Zeppelin curve - Medium, good validation
9. **Category 8**: Valence formula - Very Hard, final goal

---

## Mapping to Isabelle Files

| Our Lemma | Isabelle File | Isabelle Lemma |
|-----------|---------------|----------------|
| `generalizedWindingNumber_eq_classical` | `Winding_Numbers.thy` | `winding_number_integer` |
| `windingNumber_homotopy_invariant` | `Winding_Numbers.thy` | `winding_number_homotopy_paths` |
| `homotopy_pv_integral_eq` | `Cauchy_Integral_Theorem.thy` | `Cauchy_theorem_homotopic_paths` |
| `generalizedResidueTheorem` | `Residue_Theorem.thy` | `Residue_theorem` |
| `residue` definition | `Complex_Residues.thy` | `residue` |
| Contour integral additivity | `Contour_Integration.thy` | `contour_integral_join` |

---

## Key Differences from Isabelle

1. **Path handling**: We allow paths through singularities via PV; Isabelle requires avoidance
2. **Winding numbers**: We get ℂ-valued; Isabelle gets ℤ-valued (for closed curves)
3. **Homotopy**: We need weaker homotopy (fixing singular set); Isabelle uses standard homotopy
4. **Residues**: We use Laurent coefficient; Isabelle uses contour integral characterization

These differences mean some Isabelle proofs translate directly, while others need adaptation.

---

## Estimated Total Effort

- **Easy sorries** (Categories 1, 2, parts of 6): ~2-3 days
- **Medium sorries** (Categories 4, 9, rest of 6): ~1 week
- **Hard sorries** (Categories 3, 5, 7): ~2-3 weeks
- **Very hard sorries** (Category 8): ~1-2 weeks

**Total**: ~5-7 weeks of focused work

The critical path goes through Categories 3→5→7→8. Categories 1, 2, 4, 6 can be done in parallel.
