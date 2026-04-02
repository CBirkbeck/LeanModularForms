# Null-Homologous Generalized Residue Theorem — Implementation Plan

> **For agentic workers:** REQUIRED: Use superpowers:subagent-driven-development (if subagents available) or superpowers:executing-plans to implement this plan. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace `Convex ℝ U` with `IsNullHomologous γ U` in the generalized residue theorem chain, matching Theorem 3.3 of the HW paper exactly.

**Architecture:** New file `HomologicalCauchy.lean` proves the homological Cauchy theorem via Dixon's proof (Liouville + parametric integrals). Each downstream file gets a `_nullHomologous` variant; old convex versions become corollaries via `isNullHomologous_of_convex`.

**Tech Stack:** Lean 4, Mathlib (Liouville, parametric integrals, removable singularity)

**Spec:** `docs/superpowers/specs/2026-03-17-null-homologous-residue-theorem-design.md`

---

## File Structure

| File | Action | Responsibility |
|------|--------|---------------|
| `GeneralizedResidueTheory/HomologicalCauchy.lean` | **Create** | IsNullHomologous def, Dixon proof, CIF, integral vanishing, bridge lemma |
| `GeneralizedResidueTheory/Residue.lean` | Modify (~502) | Add `integral_eq_sum_residues_of_nullHomologous` |
| `GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean` | Modify (~217, ~580, ~793, ~963) | Add `_nullHomologous` for 4 theorems |
| `GeneralizedResidueTheory/Residue/MeromorphicLaurent.lean` | Modify (~736, ~891) | Add `_nullHomologous` for 2 theorems |
| `GeneralizedResidueTheory/Residue/FlatnessTransfer/HigherOrderAssembly.lean` | Modify (~1000) | Add `_nullHomologous` for `conditionsAB_imply_higherOrderCancel` |
| `GeneralizedResidueTheory/Residue/FlatnessTransfer.lean` | Modify (~320, ~408) | Add `_nullHomologous` for `pv_res_tendsto_of_immersion` + Theorem 3.3 |

---

## Chunk 1: HomologicalCauchy.lean — Definition + Bridge

### Task 1: IsNullHomologous Definition and Bridge Lemma

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean`

This task creates the new file with the core definition and the bridge lemma
that connects convexity to null-homologous. The bridge lemma lets us later
derive all old convex theorems as corollaries.

- [ ] **Step 1: Create file with imports and definition**

```lean
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
import LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.RemovableSingularity

open Complex Set Filter Topology MeasureTheory intervalIntegral

noncomputable section

namespace GeneralizedResidueTheory

/-- A closed piecewise C¹ immersion γ is null-homologous in an open set U if:
1. γ is a closed curve
2. γ lies entirely in U
3. The winding number of γ around every point outside U is zero.

This matches the definition in Hungerbühler-Wasem (arXiv:1808.00997v2),
Section 3.1: "A cycle C is null-homologous in D ⊂ ℂ, if its winding number
n_z(C) = 0 for all z ∉ D." -/
structure IsNullHomologous (γ : PiecewiseC1Immersion) (U : Set ℂ) : Prop where
  closed : γ.toPiecewiseC1Curve.IsClosed
  image_subset : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U
  winding_zero : ∀ z, z ∉ U →
    generalizedWindingNumber' γ.toFun γ.a γ.b z = 0
```

Note: Using `structure` instead of `def` with `∧` gives us named projections
(`.closed`, `.image_subset`, `.winding_zero`) which are cleaner to use downstream.

- [ ] **Step 2: Add the bridge lemma `isNullHomologous_of_convex`**

```lean
/-- Every closed curve in a convex open set is null-homologous.
Proof: for z ∉ U, w ↦ 1/(w-z) is holomorphic on convex U, so by
`holomorphic_convex_primitive` it has a primitive, giving ∮_γ 1/(w-z) dw = 0,
so the winding number n(γ,z) = 0. -/
theorem isNullHomologous_of_convex
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (hU_ne : U.Nonempty)
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    IsNullHomologous γ U where
  closed := hγ_closed
  image_subset := hγ_in_U
  winding_zero := by
    intro z hz
    -- w ↦ 1/(w - z) is holomorphic on U since z ∉ U
    -- By holomorphic_convex_primitive, it has a primitive on U
    -- So the contour integral vanishes, giving winding number = 0
    -- Use generalizedWindingNumber_eq_classical_away to reduce PV to classical
    sorry -- Fill in: use holomorphic_convex_primitive + FTC
```

- [ ] **Step 3: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy`
Expected: builds with one `sorry` (in `isNullHomologous_of_convex`)

- [ ] **Step 4: Fill the bridge lemma sorry**

The proof needs:
1. Show `fun w => (w - z)⁻¹` is `DifferentiableOn ℂ` on `U` (since `z ∉ U`)
2. Apply `holomorphic_convex_primitive hU_convex hU hU_ne` to get primitive `F`
3. Use `HasDerivAt` + FTC to conclude `∮_γ (w-z)⁻¹ dw = F(γ(b)) - F(γ(a)) = 0`
4. Use `generalizedWindingNumber_eq_classical_away` (or equivalent) to connect
   the PV winding number to this classical integral

- [ ] **Step 5: Build and verify sorry-free**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy`
Expected: builds with 0 sorries, 0 errors

- [ ] **Step 6: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean
git commit -m "feat: add IsNullHomologous definition and convex bridge lemma"
```

---

## Chunk 2: HomologicalCauchy.lean — Dixon Kernel

### Task 2: Dixon Kernel Construction and Continuity

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean`

The Dixon kernel is the key ingredient: `g(z,w) = (f(z)-f(w))/(z-w)` for `z ≠ w`
and `g(w,w) = deriv f w`. Joint continuity on `U × U` is the main technical lemma.

- [ ] **Step 1: Define the Dixon kernel**

```lean
/-- The Dixon kernel: g(z,w) = (f(z) - f(w))/(z - w) for z ≠ w,
and g(w,w) = deriv f w. This is the key construction in Dixon's proof
of the homological Cauchy theorem. -/
def dixonKernel (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  if z = w then deriv f w else (f z - f w) / (z - w)
```

- [ ] **Step 2: Prove basic unfold lemmas**

```lean
theorem dixonKernel_of_ne (f : ℂ → ℂ) {z w : ℂ} (h : z ≠ w) :
    dixonKernel f z w = (f z - f w) / (z - w)

theorem dixonKernel_self (f : ℂ → ℂ) (w : ℂ) :
    dixonKernel f w w = deriv f w
```

- [ ] **Step 3: Prove the Dixon kernel is jointly continuous on U × U**

This is the hard lemma. Strategy:
- At `(z₀, w₀)` with `z₀ ≠ w₀`: continuous because quotient of continuous functions
  with nonzero denominator.
- At `(w₀, w₀)`: use `DifferentiableOn.analyticOn` (complex differentiable on open set
  implies analytic), which gives locally uniform convergence of difference quotients.

```lean
theorem dixonKernel_continuousOn (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fun p : ℂ × ℂ => dixonKernel f p.1 p.2) (U ×ˢ U)
```

This may require helper lemmas:
- `dixonKernel_tendsto_deriv`: for `w ∈ U`, `dixonKernel f z w → deriv f w` as `z → w`
- Use `DifferentiableAt.hasDerivAt` to get the limit

- [ ] **Step 4: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy`
Expected: builds, 0 errors. Some sorries acceptable at this stage.

- [ ] **Step 5: Fill any remaining sorries in kernel lemmas**

Iterate until all kernel lemmas are sorry-free.

- [ ] **Step 6: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean
git commit -m "feat: Dixon kernel construction with joint continuity"
```

---

## Chunk 3: HomologicalCauchy.lean — Integral Functions and Holomorphicity

### Task 3: Define h₁, h₂ and Prove Holomorphicity

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean`

Define the two integral functions from Dixon's proof and show they are holomorphic
on their respective domains.

- [ ] **Step 1: Define h₁ (Dixon kernel integral, holomorphic on U)**

```lean
/-- h₁(w) = ∮_γ g(z,w) dz — the integral of the Dixon kernel.
Defined for w ∈ U. Holomorphic on all of U including image(γ). -/
def dixonH1 (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, dixonKernel f (γ.toFun t) w * deriv γ.toFun t
```

- [ ] **Step 2: Define h₂ (Cauchy-type integral, holomorphic off curve)**

```lean
/-- h₂(w) = ∮_γ f(z)/(z-w) dz — the Cauchy-type integral.
Defined for w ∉ image(γ). Holomorphic on ℂ \ image(γ). -/
def dixonH2 (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t
```

- [ ] **Step 3: Prove the key identity h₁ = h₂ - 2πi·n·f on U \ image(γ)**

```lean
theorem dixonH1_eq (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    {w : ℂ} (hU : w ∈ U) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH1 f γ w = dixonH2 f γ w -
      2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w
```

This follows from expanding `dixonKernel` and splitting the integral.

- [ ] **Step 4: Prove h₁ is holomorphic on U**

Two sub-arguments:

**Off-contour**: Use `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
to differentiate under the integral sign. The integrand
`dixonKernel f (γ(t)) w * γ'(t)` is holomorphic in `w` when `γ(t) ≠ w`.

**Across contour**: `h₁` is continuous on all of U (by `dixonKernel_continuousOn`
and `continuous_parametric_intervalIntegral_of_continuous'`). Since h₁ is holomorphic
on the dense open subset `U \ image(γ)` and continuous on all of U, apply
`Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt` to extend.

```lean
theorem dixonH1_differentiableOn (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    DifferentiableOn ℂ (dixonH1 f γ) U
```

- [ ] **Step 5: Prove h₂ is holomorphic off the curve**

```lean
theorem dixonH2_differentiable_off_curve (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    {w : ℂ} (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    DifferentiableAt ℂ (dixonH2 f γ) w
```

Uses parametric differentiation: d/dw ∫ f(γ(t))/(γ(t)-w) γ'(t) dt =
∫ f(γ(t))/(γ(t)-w)² γ'(t) dt. The dominated convergence bound comes from
`min_{t} |γ(t) - w| > 0` (continuous function on compact set, bounded away from 0).

- [ ] **Step 6: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy`
Expected: builds. Sorries in proof bodies are acceptable.

- [ ] **Step 7: Fill sorries, iterate until sorry-free**

- [ ] **Step 8: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean
git commit -m "feat: Dixon integral functions h₁, h₂ with holomorphicity"
```

---

## Chunk 4: HomologicalCauchy.lean — Patching, Liouville, Main Theorems

### Task 4: Entire Function, Liouville, CIF, Integral Vanishing

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean`

This is the culmination of Dixon's proof: patch h₁ and h₂ into an entire function,
apply Liouville, derive the Cauchy integral formula and integral vanishing.

- [ ] **Step 1: Prove winding number is locally constant off curve**

```lean
/-- The classical winding number is locally constant on ℂ \ image(γ).
Proof: w ↦ ∮_γ 1/(z-w) dz is holomorphic (parametric differentiation),
hence continuous. Since it takes values in 2πi·ℤ (integrality), a continuous
integer-valued function is locally constant. -/
theorem windingNumber_locallyConstant_off_curve
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed) :
    IsLocallyConstant
      (fun w => generalizedWindingNumber' γ.toFun γ.a γ.b w)
      -- restricted to {w | ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w}
```

Note: The exact statement may need adjustment based on what's already in
`WindingNumber.lean` or `Homotopy/Integrality.lean`. Check existing infrastructure.

- [ ] **Step 2: Prove h₁ = h₂ near ∂U (patching lemma)**

```lean
/-- Near ∂U, the winding number is 0 (by null-homologous + locally constant),
so h₁ = h₂ on the overlap. -/
theorem dixonH1_eq_dixonH2_near_boundary
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U) :
    ∀ w₀ ∈ frontier U,
      ∃ ε > 0, ∀ w ∈ Metric.ball w₀ ε ∩ U,
        dixonH1 f γ w = dixonH2 f γ w
```

Key argument: `w₀ ∈ frontier U` means `w₀ ∉ U` (since U is open). Since
`image(γ) ⊂ U`, we have `w₀ ∉ image(γ)`. The winding number is locally constant
near `w₀`, and `n(γ, w₀) = 0` (null-homologous). So `n(γ, w) = 0` for `w` near `w₀`.
By the key identity, `h₁(w) = h₂(w) - 0 = h₂(w)`.

- [ ] **Step 3: Construct the entire function h and prove it's entire**

```lean
/-- The Dixon function: h₁ on U, h₂ on ℂ \ U. These agree near ∂U
(by the patching lemma), so h is holomorphic on all of ℂ. -/
def dixonFunction (f : ℂ → ℂ) (U : Set ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  if w ∈ U then dixonH1 f γ w else dixonH2 f γ w

theorem dixonFunction_differentiable
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    Differentiable ℂ (dixonFunction f U γ)
```

- [ ] **Step 4: Prove h → 0 at ∞**

```lean
theorem dixonFunction_tendsto_zero
    (U : Set ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U) :
    Tendsto (dixonFunction f U γ) (Filter.cocompact ℂ) (𝓝 0)
```

For `w` far from `image(γ)`: `h(w) = h₂(w) = ∮_γ f(z)/(z-w) dz`. Since
`|1/(z-w)| ≤ 1/dist(w, image(γ))` and `image(γ)` is compact, the integral
tends to 0 as `|w| → ∞`.

- [ ] **Step 5: Apply Liouville: h ≡ 0**

```lean
theorem dixonFunction_eq_zero
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    dixonFunction f U γ = 0
```

Use `Differentiable.apply_eq_of_tendsto_cocompact` (or the appropriate mathlib
Liouville variant): entire + tends to 0 at ∞ ⟹ identically 0.

- [ ] **Step 6: Derive the Cauchy integral formula for null-homologous curves**

```lean
/-- Cauchy integral formula for null-homologous curves:
(1/2πi) ∮_γ f(z)/(z-w) dz = n(γ,w) · f(w) for w ∈ U \ image(γ). -/
theorem cauchyIntegralFormula_nullHomologous
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    {w : ℂ} (hw : w ∈ U) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH2 f γ w =
      2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w
```

From `dixonFunction_eq_zero`: `0 = h₁(w) = h₂(w) - 2πi·n(γ,w)·f(w)`,
so `h₂(w) = 2πi·n(γ,w)·f(w)`.

- [ ] **Step 7: Derive the main theorem — contour integral vanishes**

```lean
/-- The homological Cauchy theorem: if f is holomorphic on open U and γ is
null-homologous in U, then ∮_γ f = 0.

Proof: Pick w₀ ∈ U \ image(γ) (exists because image(γ) has empty interior
in ℂ and U is open). Apply the CIF to F(z) = f(z)(z - w₀):
  ∮_γ f(z) dz = ∮_γ F(z)/(z-w₀) dz = 2πi · n(γ,w₀) · F(w₀) = 0
since F(w₀) = f(w₀)·(w₀ - w₀) = 0. -/
theorem contourIntegral_eq_zero_of_nullHomologous
    (U : Set ℂ) (hU : IsOpen U) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0
```

- [ ] **Step 8: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy`
Expected: builds. Sorries acceptable at this stage.

- [ ] **Step 9: Fill all remaining sorries**

This is the most substantial proving work. Iterate until the file is sorry-free.
Use `lean_goal`, `lean_multi_attempt`, and search tools liberally.

- [ ] **Step 10: Verify axiom cleanliness**

Run: `lean_verify` on key theorems to check they don't introduce custom axioms.
Expected: only `[propext, Classical.choice, Quot.sound]`

- [ ] **Step 11: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/HomologicalCauchy.lean
git commit -m "feat: homological Cauchy theorem via Dixon's proof"
```

---

## Chunk 5: Refactoring — Residue.lean and GeneralizedTheorem.lean

### Task 5: Add `_nullHomologous` to Residue.lean

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue.lean` (after line ~560)

- [ ] **Step 1: Add import for HomologicalCauchy**

Add to imports:
```lean
import LeanModularForms.GeneralizedResidueTheory.HomologicalCauchy
```

- [ ] **Step 2: Add `integral_eq_sum_residues_of_nullHomologous`**

Copy the signature of `integral_eq_sum_residues_of_avoids` (line 502), replace
`(hU_convex : Convex ℝ U)` with `(h_null : IsNullHomologous γ U)`.

In the proof body, replace the call to `holomorphic_convex_primitive` with
`contourIntegral_eq_zero_of_nullHomologous`. The rest of the proof (subtracting
principal parts, showing the remainder is holomorphic) should remain the same.

Also extract the `hγ_closed` and `hγ_in_U` from `h_null` where they were
previously separate parameters.

- [ ] **Step 3: Re-derive old convex version as corollary**

After the new theorem, add:
```lean
-- Old convex version is now a corollary
theorem integral_eq_sum_residues_of_avoids' ... (hU_convex : Convex ℝ U) ... :=
  integral_eq_sum_residues_of_nullHomologous ...
    (isNullHomologous_of_convex U hU hU_convex ⟨...⟩ γ hγ_closed hγ_in_U) ...
```

Note: Don't rename the original theorem yet. Add the new one alongside and verify
everything still builds. Renaming can be done in a cleanup pass.

- [ ] **Step 4: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.Residue`
Expected: 0 errors

- [ ] **Step 5: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue.lean
git commit -m "feat: add integral_eq_sum_residues_of_nullHomologous"
```

### Task 6: Add `_nullHomologous` to GeneralizedTheorem.lean

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean`

Four theorems need `_nullHomologous` variants:
1. `generalizedResidueTheorem'` (line 217) — uses convexity via Residue.lean
2. `generalizedResidueTheorem` (line 580) — uses convexity via `generalizedResidueTheorem'`
3. `generalizedResidueTheorem_higher_order` (line 793) — uses convexity directly
4. `generalizedResidueTheorem_higher_order_simple` (line 963) — uses `generalizedResidueTheorem`

Note: `generalizedResidueTheorem_higher_order_tendsto` (line 926) does NOT take
`Convex ℝ U` — it takes `Tendsto` hypotheses. No change needed.

- [ ] **Step 1: Add `generalizedResidueTheorem'_nullHomologous`**

Replace `(hU_convex : Convex ℝ U)` with `(h_null : IsNullHomologous γ U)`.
In the proof, replace the call to `integral_eq_sum_residues_of_avoids` with
`integral_eq_sum_residues_of_nullHomologous`.

- [ ] **Step 2: Add `generalizedResidueTheorem_nullHomologous`**

Same pattern. Replace convexity parameter, use new `generalizedResidueTheorem'_nullHomologous`.

- [ ] **Step 3: Add `generalizedResidueTheorem_higher_order_nullHomologous`**

Same pattern. This one calls `holomorphic_convex_primitive` directly — replace with
`contourIntegral_eq_zero_of_nullHomologous`.

- [ ] **Step 4: Add `generalizedResidueTheorem_higher_order_simple_nullHomologous`**

Uses `generalizedResidueTheorem_nullHomologous` internally.

- [ ] **Step 5: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheorem`
Expected: 0 errors

- [ ] **Step 6: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean
git commit -m "feat: add _nullHomologous variants to GeneralizedTheorem"
```

---

## Chunk 6: Refactoring — MeromorphicLaurent, HigherOrderAssembly, FlatnessTransfer

### Task 7: Add `_nullHomologous` to MeromorphicLaurent.lean

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/MeromorphicLaurent.lean`

Two theorems:
1. `contourIntegral_eq_zero_of_meromorphic_residue_zero` (line 736)
2. `contourIntegral_eq_zero_of_meromorphic_residue_zero_finset` (line 891)

- [ ] **Step 1: Add both `_nullHomologous` variants**

Replace `(hU_convex : Convex ℝ U)` with `(h_null : IsNullHomologous γ U)`.
Replace internal calls to `holomorphic_convex_primitive` with
`contourIntegral_eq_zero_of_nullHomologous`.

- [ ] **Step 2: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.Residue.MeromorphicLaurent`
Expected: 0 errors

- [ ] **Step 3: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/MeromorphicLaurent.lean
git commit -m "feat: add _nullHomologous to MeromorphicLaurent"
```

### Task 8: Add `_nullHomologous` to HigherOrderAssembly.lean

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/FlatnessTransfer/HigherOrderAssembly.lean`

One theorem: `conditionsAB_imply_higherOrderCancel` (line 1000)

- [ ] **Step 1: Add `conditionsAB_imply_higherOrderCancel_nullHomologous`**

Replace `(hU_convex : Convex ℝ U)` with `(h_null : IsNullHomologous γ U)`.
This theorem calls `holomorphic_convex_primitive` (via internal helpers) — replace
with `contourIntegral_eq_zero_of_nullHomologous`. Also calls
`contourIntegral_eq_zero_of_meromorphic_residue_zero_finset` — use the new
`_nullHomologous` variant.

- [ ] **Step 2: Build and verify**

Run: `lake build LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.HigherOrderAssembly`
Expected: 0 errors

- [ ] **Step 3: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/FlatnessTransfer/HigherOrderAssembly.lean
git commit -m "feat: add _nullHomologous to conditionsAB_imply_higherOrderCancel"
```

### Task 9: Add `_nullHomologous` to FlatnessTransfer.lean — Theorem 3.3

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/FlatnessTransfer.lean`

Two theorems:
1. `pv_res_tendsto_of_immersion` (line 320)
2. `generalizedResidueTheorem_3_3` (line 408) — **this is the paper's Theorem 3.3**

- [ ] **Step 1: Add `pv_res_tendsto_of_immersion_nullHomologous`**

Replace `(hU_convex : Convex ℝ U)` with `(h_null : IsNullHomologous γ U)`.
Uses `generalizedResidueTheorem'` internally — switch to `_nullHomologous` variant.

- [ ] **Step 2: Add `generalizedResidueTheorem_3_3_nullHomologous`**

This is the crown jewel — Theorem 3.3 of the HW paper with `IsNullHomologous`:

```lean
/-- Theorem 3.3 of Hungerbühler-Wasem (arXiv:1808.00997v2).
Generalized residue theorem for null-homologous curves with conditions (A')+(B).
This is the full-strength version matching the paper exactly. -/
theorem generalizedResidueTheorem_3_3_nullHomologous
    (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s))
```

The proof combines the two `_nullHomologous` ingredients:
```lean
  generalizedResidueTheorem_higher_order_tendsto S0 f γ
    (conditionsAB_imply_higherOrderCancel_nullHomologous U hU S0 f hf γ
      h_null.closed h_null.image_subset hMero hCondA hCondB hγ_meas
      h_no_endpt_cross h_unique_cross (fun s hs => hS_in_U s (hS0_subset s hs)))
    (pv_res_tendsto_of_immersion_nullHomologous U hU S hS_in_U hS_discrete hS_closed
      S0 hS0_subset f γ h_null hS_on_curve hγ_meas h_no_endpt_cross h_unique_cross)
```

- [ ] **Step 3: Build full project**

Run: `lake build`
Expected: full build passes, 0 errors in GeneralizedResidueTheory

- [ ] **Step 4: Verify axiom cleanliness of Theorem 3.3**

Run `lean_verify` on `generalizedResidueTheorem_3_3_nullHomologous`.
Expected: `[propext, Classical.choice, Quot.sound]` (no `sorryAx`)

- [ ] **Step 5: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/FlatnessTransfer.lean
git commit -m "feat: Theorem 3.3 for null-homologous curves (HW paper)"
```

---

## Chunk 7: Verification and Cleanup

### Task 10: Full Verification and Cleanup

**Files:**
- All modified files in `GeneralizedResidueTheory/`

- [ ] **Step 1: Full build verification**

Run: `lake build`
Expected: full project builds with 0 errors

- [ ] **Step 2: Check no existing theorems are broken**

Verify the old convex versions still work by checking they're still called
from outside `GeneralizedResidueTheory/` (e.g., in the valence formula files).

Run: `grep -rn "generalizedResidueTheorem_3_3\b" LeanModularForms/ --include="*.lean" | grep -v nullHomologous`
Expected: existing callers still reference the old name and still build.

- [ ] **Step 3: Count sorries in GeneralizedResidueTheory**

Run: `grep -rn "sorry" LeanModularForms/GeneralizedResidueTheory/ --include="*.lean" | grep -v "sorry-free\|no sorry\|-- sorry\|sorryAx"`
Expected: 0 sorries (or same count as before this work)

- [ ] **Step 4: Run axiom check on all new theorems**

Use `lean_verify` on each new `_nullHomologous` theorem.
Expected: all `[propext, Classical.choice, Quot.sound]`

- [ ] **Step 5: Final commit**

```bash
git add -A
git commit -m "chore: verify null-homologous residue theorem chain is complete"
```

---

## Implementation Notes

### Key Mathlib Lemmas to Find at Build Time

The exact names may vary by mathlib version. Use `lean_local_search` and `lean_loogle`
to find the correct names:

| Concept | Search query |
|---------|-------------|
| Liouville's theorem | `lean_loogle "Differentiable ℂ f → Bornology.IsBounded"` |
| Parametric differentiation | `lean_local_search "hasDerivAt_integral_of_dominated"` |
| Continuous parametric integral | `lean_local_search "continuous_parametric_intervalIntegral"` |
| Removable singularity | `lean_local_search "analyticAt_of_differentiable_on_punctured"` |
| DifferentiableOn → AnalyticOn | `lean_loogle "DifferentiableOn ℂ → AnalyticOn"` |

### Heartbeat Management

Several existing proofs use `set_option maxHeartbeats 1600000`. The new proofs may
need similar or higher limits. Start with default, increase if needed.

### The Hardest Proof

`dixonKernel_continuousOn` (joint continuity of the Dixon kernel) is likely the hardest
single lemma. If this blocks progress, it can be `sorry`'d temporarily while the rest
of the chain is built, then filled in a focused session.

### Fallback Strategy

If the full Dixon proof proves too difficult to formalize, a pragmatic alternative:
1. State `contourIntegral_eq_zero_of_nullHomologous` as `sorry`
2. Build the entire `_nullHomologous` chain on top of it
3. Fill the sorry later (or with a different proof strategy)

This isolates the hard mathematical proof from the mechanical refactoring.
