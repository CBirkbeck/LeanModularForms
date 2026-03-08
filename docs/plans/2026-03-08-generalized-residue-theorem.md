# Generalized Residue Theorem Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Prove the generalized residue theorem (Thm 3.3) and Prop 2.2 from the Hungerbühler-Wasem paper (arXiv 1808.00997v2), replacing the existing `generalizedResidueTheorem'` so that `CauchyPrincipalValueExists` is *proven*, not assumed.

**Architecture:** Six phases building bottom-up: (1) Prop 2.2 — PV existence for `1/(z-z₀)` along immersions, (2) Lemma 3.1 — PV on model sector-curves for Laurent series, (3) Def 3.2 — flatness + higher-order PV invariance, (4) Thm 3.3 — clean generalized residue theorem replacing old version, (5) ValenceFormula downstream update, (6) Cycle support.

**Tech Stack:** Lean 4, Mathlib, existing `GeneralizedResidueTheory/` infrastructure

**Key existing infrastructure to reuse:**
- `pv_limit_via_dyadic` (OnCurvePV/Basic.lean:24) — PV at single C² crossing
- `cpv_avoidance` (OnCurvePV/Basic.lean:298) — PV when curve avoids z₀
- `cpv_concat` (OnCurvePV/Basic.lean:319) — glue PV on adjacent intervals
- `aEStronglyMeasurable_pv_integrand_piecewiseC1` (OnCurvePV/Basic.lean:185) — measurability
- `angleAtCrossing` (WindingNumber.lean:34) — oriented angle at crossing
- `windingNumberWithAngles'` (WindingNumber.lean:53) — winding via angle sum
- `HasSimplePoleAt` (Residue.lean:66) — simple pole decomposition
- `residueSimplePole` (Residue.lean:61) — residue via limit
- `simple_poles_decomposition` (Residue.lean:333) — f = singular + regular
- `integral_eq_sum_residues_of_avoids` (Residue.lean:502) — classical residue theorem
- `ModelSectorCurve` (Basic.lean:80) — sector curve structure (γ₁, γ₂, γ₃)
- `generalizedResidueTheorem'` (Residue/GeneralizedTheorem.lean:210) — TO BE REPLACED

**Verification command:** `lake build` (run after every file change; 0 errors required)

---

## Phase 1: Proposition 2.2 — PV of `1/(z-z₀)` Exists for Immersions

### Task 1: Finite Crossings Lemma

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean`

**Context:** The paper uses Rolle's theorem on arc-length parameterization to prove finiteness. In Lean, we can use the fact that a continuous injective curve on a compact set has finitely many preimages of any point — or more directly, use the immersion property (nonzero derivative) to show crossings are isolated, then compactness gives finiteness.

**Step 1: Create file with imports and state the finite crossings lemma**

```lean
/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.OnCurvePV.Basic
import LeanModularForms.GeneralizedResidueTheory.WindingNumber

/-!
# Proposition 2.2: PV Winding Number for Immersions

We prove that for a closed piecewise C¹ immersion Λ and any point z₀,
the Cauchy principal value of `1/(2πi) ∮ dz/(z-z₀)` exists and equals
`n_{z₀}(Λ̃) + Σ αₗ/(2π)` where Λ̃ avoids z₀ and αₗ are oriented crossing angles.

Reference: Hungerbühler-Wasem, arXiv:1808.00997v2, Proposition 2.2.
-/

open Complex MeasureTheory Set Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The set of parameter values where a piecewise C¹ immersion passes through z₀
is finite. This follows from the immersion property: nonzero derivative means
crossings are isolated, and compactness of [a,b] gives finiteness. -/
theorem finite_crossings (γ : PiecewiseC1Immersion) (z₀ : ℂ) :
    Set.Finite {t ∈ Set.Icc γ.a γ.b | γ.toFun t = z₀} := by
  sorry

end
```

**Step 2: Run `lake build` to verify the file compiles with sorry**

Run: `lake build`
Expected: 0 errors (sorry is allowed)

**Step 3: Prove `finite_crossings`**

The proof strategy:
1. Use `IsCompact.finite` on the compact set `Icc a b`
2. Show the crossing set is discrete: at each crossing `t₀`, the nonzero derivative `γ'(t₀) ≠ 0` implies `γ` is locally injective near `t₀` (inverse function theorem), so `t₀` is an isolated crossing
3. Discrete + compact = finite

Key mathlib lemmas to use:
- `IsCompact.finite` or `Set.Finite.of_discrete_topology`
- `HasStrictDerivAt.localInverse` or manual argument via continuity of `γ(t) - z₀`
- The immersion's `deriv_ne_zero` field for smooth points
- The `left_deriv_limit`/`right_deriv_limit` fields for partition points

**Step 4: Run `lake build` to verify**

Run: `lake build`
Expected: 0 errors, 0 sorries in this file

**Step 5: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean
git commit -m "feat: prove finite crossings for piecewise C¹ immersions"
```

---

### Task 2: PV Existence at Each Crossing Point

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean`

**Context:** We need to show that `CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun a b z₀` holds. The existing `pv_limit_via_dyadic` proves PV at a single crossing on a sub-interval where the crossing is unique. We need to:
1. For each crossing `tₖ`, find a sub-interval `[aₖ, bₖ]` containing only that crossing
2. Apply `pv_limit_via_dyadic` on each sub-interval
3. Use `cpv_avoidance` on intervals between crossings
4. Use `cpv_concat` to glue everything together

**Step 1: State the single-crossing sub-interval lemma**

```lean
/-- For each crossing point, there exists a sub-interval containing only that crossing
where the curve is C² (smooth, away from partition). -/
lemma exists_isolated_crossing_interval (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc γ.a γ.b) (hcross : γ.toFun t₀ = z₀) :
    ∃ a' b' : ℝ, a' < t₀ ∧ t₀ < b' ∧ Set.Icc a' b' ⊆ Set.Icc γ.a γ.b ∧
      (∀ t ∈ Set.Icc a' b', γ.toFun t = z₀ → t = t₀) ∧
      ContDiffAt ℝ 2 γ.toFun t₀ ∧
      ContinuousOn (deriv γ.toFun) (Set.Icc a' b') := by
  sorry
```

For endpoint crossings (t₀ = a or t₀ = b), the proof is simpler since a closed curve means `γ(a) = γ(b)` and we can treat the crossing at the boundary differently. Consider handling this case separately if needed.

**Step 2: State and prove PV existence for a single-point PV of `(z - z₀)⁻¹`**

```lean
/-- PV of `(z - z₀)⁻¹` exists on a sub-interval with a single crossing.
Wraps `pv_limit_via_dyadic` for the specific integrand `(z - z₀)⁻¹`. -/
lemma cpv_exists_single_crossing (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (a' b' t₀ : ℝ) (ha' : γ.a ≤ a') (hb' : b' ≤ γ.b)
    (hat₀ : t₀ ∈ Set.Ioo a' b')
    (hcross : γ.toFun t₀ = z₀)
    (h_unique : ∀ t ∈ Set.Icc a' b', γ.toFun t = z₀ → t = t₀)
    (h_C2 : ContDiffAt ℝ 2 γ.toFun t₀)
    (h_deriv_cont : ContinuousOn (deriv γ.toFun) (Set.Icc a' b')) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun a' b' z₀ := by
  sorry
```

The proof applies `pv_limit_via_dyadic` (which gives PV for `(γ t - γ t₀)⁻¹ * γ'(t)`), then uses `cpv_exists_from_shifted_tendsto` to convert to the `(z - z₀)⁻¹` form.

**Step 3: Prove full PV existence by iterating over crossings**

```lean
/-- PV of `(z - z₀)⁻¹` exists along the full curve [a,b].
Proved by induction on the finite set of crossings, using
`cpv_avoidance` between crossings and `cpv_concat` to glue. -/
theorem cpv_exists_inv_sub (γ : PiecewiseC1Immersion) (z₀ : ℂ) :
    CauchyPrincipalValueExists' (fun z => (z - z₀)⁻¹) γ.toFun γ.a γ.b z₀ := by
  sorry
```

**Proof strategy for `cpv_exists_inv_sub`:**
1. Use `finite_crossings` to get finitely many crossings `{t₁, ..., tₙ}` in `[a, b]`
2. Sort them: `a ≤ t₁ < t₂ < ... < tₙ ≤ b`
3. On each interval `[tₖ, tₖ₊₁]` between consecutive crossings:
   - If no crossing: `cpv_avoidance`
   - If crossing at endpoint: `cpv_exists_single_crossing` on sub-interval + `cpv_avoidance` + `cpv_concat`
4. Use `cpv_concat` to glue all intervals
5. Handle the endpoint case (closed curve: `γ(a) = γ(b)`)

For the induction, use `Finset.induction` on the sorted crossing set, or manually iterate via `List.foldl` on the sorted list.

**Step 4: Verify compilation**

Run: `lake build`
Expected: 0 errors

**Step 5: Commit**

```bash
git add LeanModularForms/GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean
git commit -m "feat: prove PV of (z-z₀)⁻¹ exists for piecewise C¹ immersions"
```

---

### Task 3: Proposition 2.2 — Full Statement with Angle Formula

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean`

**Context:** The full Prop 2.2 says the PV winding number equals `n_{z₀}(Λ̃) + Σ αₗ/(2π)`. This connects the PV-based `generalizedWindingNumber'` to the angle-based `windingNumberWithAngles'`.

**Step 1: State the proposition**

```lean
/-- Proposition 2.2 (Hungerbühler-Wasem): For a closed piecewise C¹ immersion,
the PV winding number equals the classical winding of the detoured curve plus
the sum of angle contributions at crossing points.

`generalizedWindingNumber' γ a b z₀ = n_{z₀}(γ̃) + Σ αₖ/(2π)`

where γ̃ avoids z₀ by detouring around crossings on clockwise circular arcs. -/
theorem proposition_2_2 (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed) (z₀ : ℂ)
    (crossings : Finset ℝ)
    (hcross_in : ∀ t ∈ crossings, t ∈ Set.Ioo γ.a γ.b)
    (hcross_at : ∀ t ∈ crossings, γ.toFun t = z₀)
    (hcross_all : ∀ t ∈ Set.Ioo γ.a γ.b, γ.toFun t = z₀ → t ∈ crossings) :
    generalizedWindingNumber' γ.toFun γ.a γ.b z₀ =
      windingNumberWithAngles' γ z₀ crossings hcross_in hcross_at := by
  sorry
```

**Note:** This theorem connects two existing definitions. The proof requires showing that the PV integral decomposes into classical winding (on the detoured curve) plus angle contributions. This is the deepest part of Phase 1 and may require substantial infrastructure about curve deformation and homotopy invariance.

**Alternative simpler formulation** (if the full detour decomposition is too complex initially):

```lean
/-- At a smooth crossing (not in partition), the PV winding contribution is 1/2.
This is a corollary of Prop 2.2 for the smooth case. -/
theorem pv_winding_at_smooth_crossing (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo γ.a γ.b)
    (hcross : γ.toFun t₀ = z₀)
    (hsmooth : t₀ ∉ γ.toPiecewiseC1Curve.partition) :
    -- The local PV contribution at this crossing is 1/2
    sorry := sorry
```

**Step 2: Fill the proof**

The proof of `proposition_2_2` proceeds by:
1. Decompose the PV integral into sub-intervals around each crossing
2. On each crossing sub-interval, the PV integral equals `angleAtCrossing/(2π)` (from `pv_limit_via_dyadic` + asymptotic analysis)
3. On avoiding sub-intervals, the integral contributes to the classical winding `n_{z₀}(γ̃)`
4. Sum everything up

**Step 3: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/WindingNumber/Proposition2_2.lean
git commit -m "feat: prove Proposition 2.2 — PV winding number formula"
```

---

## Phase 2: Lemma 3.1 — PV on Model Sector-Curve

### Task 4: Model Sector-Curve as PiecewiseC1Immersion

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`

**Context:** The model sector-curve consists of three segments:
- γ₁: radial ray from 0 to r along direction 1 (positive real)
- γ₂: circular arc of radius r from angle 0 to angle α
- γ₃: radial ray from r·e^{iα} back to 0

The existing `ModelSectorCurve` in Basic.lean:80 defines the components but doesn't bundle them as a `PiecewiseC1Immersion`.

**Step 1: Create file and construct the sector curve as PiecewiseC1Immersion**

```lean
/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.OnCurvePV.Basic

/-!
# Sector Curve PV Computation (Lemma 3.1)

We define the model sector-curve and prove that
`PV ∮_γ z^n dz/z = { iα if n=0; 0 if n≥1 }`
under appropriate angle conditions.

Reference: Hungerbühler-Wasem, arXiv:1808.00997v2, Lemma 3.1.
-/

open Complex MeasureTheory Set Filter Topology

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The model sector-curve parameterized on [0,3]:
- [0,1]: radial ray from 0 to r (along positive real axis)
- [1,2]: circular arc from angle 0 to α at radius r
- [2,3]: radial ray from r·e^{iα} back to 0 -/
def sectorCurve (r : ℝ) (α : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1 then (t * r : ℝ)
  else if t ≤ 2 then r * exp (I * ((t - 1) * α))
  else ((3 - t) * r : ℝ) * exp (I * α)

end
```

**Step 2: Prove basic properties**

```lean
/-- The sector curve is continuous. -/
lemma sectorCurve_continuous (r : ℝ) (hr : 0 < r) (α : ℝ) :
    Continuous (sectorCurve r α) := by
  sorry

/-- The sector curve passes through 0 at t=0 and t=3. -/
lemma sectorCurve_zero (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 := by sorry

lemma sectorCurve_three (r : ℝ) (α : ℝ) :
    sectorCurve r α 3 = 0 := by sorry

/-- The sector curve passes through r at t=1. -/
lemma sectorCurve_one (r : ℝ) (α : ℝ) :
    sectorCurve r α 1 = r := by sorry
```

**Step 3: Construct as PiecewiseC1Immersion (partition = {0, 1, 2, 3})**

```lean
/-- The sector curve as a piecewise C¹ immersion on [0, 3]
with partition {0, 1, 2, 3}. -/
def sectorCurveImmersion (r : ℝ) (hr : 0 < r) (α : ℝ) (hα : α ≠ 0) :
    PiecewiseC1Immersion := by
  sorry
```

**Step 4: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean
git commit -m "feat: define model sector-curve as PiecewiseC1Immersion"
```

---

### Task 5: PV Computation on Sector Curve

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`

**Context:** The key computation is:
- `PV ∮_γ dz/z = iα` (the radial parts cancel, arc contributes iα)
- `PV ∮_γ z^{n-1} dz = 0` when `n ≥ 1` and the angle condition `α = (p/q)π` with `q ∤ (n+1)` holds

**Step 1: Prove the fundamental sector PV integral**

```lean
/-- PV of `dz/z` along the sector curve equals `iα`.
The two radial segments contribute integrals of `dt/t` which diverge but cancel
symmetrically (same radius r → same logarithmic divergence). The arc contributes
`∫₀^α i dθ = iα`. -/
theorem pv_sector_dz_over_z (r : ℝ) (hr : 0 < r) (α : ℝ) (hα : α ≠ 0) :
    CauchyPrincipalValueExists' (fun z => z⁻¹) (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' (fun z => z⁻¹) (sectorCurve r α) 0 3 = I * α := by
  sorry
```

**Proof sketch:**
1. Split integral into three segments: [0,1], [1,2], [2,3]
2. Segment [0,1] (radial out): `∫_ε^1 (tr)⁻¹ · r dt = ∫_ε^1 dt/t = -ln ε`
3. Segment [2,3] (radial back): `∫_ε^1 ((3-t)r·e^{iα})⁻¹ · (-r·e^{iα}) dt = -∫_ε^1 dt/t = ln ε` (cancels!)
4. Segment [1,2] (arc): `∫_0^α (r·e^{iθ})⁻¹ · (ir·e^{iθ}) dθ = ∫_0^α i dθ = iα`
5. Total PV = 0 + iα + 0 = iα

**Step 2: Prove PV of higher powers vanishes**

```lean
/-- PV of `z^{n-1} dz` along the sector curve vanishes when α = pπ/q
and q ∤ (n+1). The radial contributions are finite (integrable for n ≥ 1)
and the arc contribution involves `∫₀^α e^{inθ} dθ` which equals
`(e^{inα} - 1)/(in)`. When α = pπ/q and q ∤ n, this is finite and
the overall integral is zero by symmetry. -/
theorem pv_sector_higher_power (r : ℝ) (hr : 0 < r) (α : ℝ)
    (n : ℤ) (hn : n ≥ 1)
    (p q : ℕ) (hq : q ≠ 0) (hα_eq : α = p * Real.pi / q)
    (hgcd : Nat.Coprime p q) (h_ndvd : ¬ (q : ℤ) ∣ (n + 1)) :
    ∫ t in (0:ℝ)..3, (sectorCurve r α t) ^ (n - 1) *
      deriv (sectorCurve r α) t = 0 := by
  sorry
```

**Note:** For `n ≥ 1`, the integrand `z^{n-1}` is continuous at 0, so no PV is needed — the integral exists classically. The key is showing the integral vanishes under the angle condition.

**Step 3: State and prove Lemma 3.1**

```lean
/-- Lemma 3.1 (Hungerbühler-Wasem): PV of `f(z) dz` along a sector curve
equals `n₀(γ) · res₀(f)` when:
- f has a Laurent expansion at 0
- α = pπ/q with gcd(p,q)=1
- Laurent series only has terms a_n/z^n for n = 2kq/p + 1

For simple poles (Laurent series = c/z + holomorphic), condition (B) is
automatically satisfied for any rational angle. -/
theorem lemma_3_1_simple_pole (r : ℝ) (hr : 0 < r) (α : ℝ) (hα : α ≠ 0)
    (f : ℂ → ℂ) (hf : HasSimplePoleAt f 0) :
    CauchyPrincipalValueExists' f (sectorCurve r α) 0 3 0 ∧
    cauchyPrincipalValue' f (sectorCurve r α) 0 3 =
      (I * α / (2 * Real.pi)) * residueSimplePole f 0 := by
  sorry
```

**Proof sketch:**
1. Decompose `f(z) = c/z + g(z)` using `HasSimplePoleAt`
2. PV of `c/z` = c · PV of `1/z` = c · iα (from `pv_sector_dz_over_z`)
3. Integral of `g(z) dz` is classical (g is analytic, so continuous at 0)
4. Since g is analytic near 0, `∮_γ g(z) dz = 0` (sector curve is contractible in ℂ \ {0})
5. Total = c · iα = (iα/(2πi)) · (2πi · c) = n₀(γ) · res₀(f)
   - Here `n₀(γ) = iα/(2πi) = α/(2π)` is the winding number of the sector curve

**Step 4: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean
git commit -m "feat: prove Lemma 3.1 — PV on sector curves for simple poles"
```

---

## Phase 3: Flatness and Higher-Order Poles

### Task 6: Define Flatness (Definition 3.2)

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/Residue/Flatness.lean`

**Context:** A curve is flat of order n at a crossing point if it stays close to its tangent lines with error `o(|Γ(x) - z₁|^n)`. Every piecewise C¹ curve is flat of order 1.

**Step 1: Create file and define flatness**

```lean
/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic

/-!
# Flatness of Curves at Crossing Points (Definition 3.2)

A piecewise C¹ curve is flat of order n at a point if it stays close
to its tangent lines with error o(|Γ(x) - z₁|^n).

Reference: Hungerbühler-Wasem, arXiv:1808.00997v2, Definition 3.2.
-/

open Complex Set Filter Topology

noncomputable section

/-- A curve `γ` is flat of order `n` at parameter value `t₀` if the curve
stays within `o(|γ(t) - γ(t₀)|^n)` of the tangent lines at `t₀`.

More precisely: if `P⁺` is the orthogonal projection onto the right tangent
direction `lim_{t→t₀⁺} γ'(t)` and `P⁻` onto `-lim_{t→t₀⁻} γ'(t)`, then
`|γ(t) - P⁺(γ(t))| = o(|γ(t) - γ(t₀)|^n)` as `t → t₀⁺` and similarly
for `P⁻` as `t → t₀⁻`. -/
def IsFlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop :=
  -- Right flatness: distance to right tangent line is o(|γ(t)-γ(t₀)|^n) as t → t₀⁺
  (∀ L_right : ℂ, L_right ≠ 0 →
    Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L_right) →
    Filter.Tendsto
      (fun t => ‖γ t - γ t₀ - ((γ t - γ t₀).re * L_right.re + (γ t - γ t₀).im * L_right.im) /
        (L_right.re ^ 2 + L_right.im ^ 2) • L_right‖ / ‖γ t - γ t₀‖ ^ n)
      (𝓝[>] t₀) (𝓝 0)) ∧
  -- Left flatness: distance to left tangent line is o(|γ(t)-γ(t₀)|^n) as t → t₀⁻
  (∀ L_left : ℂ, L_left ≠ 0 →
    Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L_left) →
    Filter.Tendsto
      (fun t => ‖γ t - γ t₀ - ((γ t - γ t₀).re * (-L_left).re + (γ t - γ t₀).im * (-L_left).im) /
        (L_left.re ^ 2 + L_left.im ^ 2) • (-L_left)‖ / ‖γ t - γ t₀‖ ^ n)
      (𝓝[<] t₀) (𝓝 0))

/-- Every piecewise C¹ curve is flat of order 1 at all its points. -/
theorem isFlatOfOrder_one (γ : PiecewiseC1Immersion) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Set.Icc γ.a γ.b) :
    IsFlatOfOrder γ.toFun t₀ 1 := by
  sorry

end
```

**Note:** The flatness definition is somewhat involved because it requires projecting onto tangent lines. An alternative cleaner formulation might use the angle between `γ(t) - γ(t₀)` and the tangent direction, requiring it to go to 0.

**Step 2: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/Flatness.lean
git commit -m "feat: define flatness of order n (Definition 3.2)"
```

---

### Task 7: Conditions (A) and (B) for Higher-Order Poles

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/Flatness.lean`

**Context:** Conditions (A) and (B) govern when the generalized residue theorem extends to higher-order poles on the curve.

**Step 1: Define conditions (A) and (B)**

```lean
/-- Condition (A): If z₀ is a pole of order n on the curve C, then C is flat
of order n at z₀. -/
def SatisfiesConditionA (γ : PiecewiseC1Immersion) (f : ℂ → ℂ)
    (crossings : Finset ℝ) : Prop :=
  ∀ t₀ ∈ crossings, ∀ n : ℕ,
    -- If f has a pole of order n at γ(t₀)
    (meromorphicOrderAt f (γ.toFun t₀) = -↑n) →
    IsFlatOfOrder γ.toFun t₀ n

/-- Condition (B): The angle at each crossing is a rational multiple of π,
and the Laurent series contains only terms compatible with the angle. -/
def SatisfiesConditionB (γ : PiecewiseC1Immersion) (f : ℂ → ℂ)
    (crossings : Finset ℝ)
    (hcross_in : ∀ t ∈ crossings, t ∈ Set.Ioo γ.a γ.b) : Prop :=
  ∀ t₀ ∈ crossings,
    let α := angleAtCrossing γ t₀ (hcross_in t₀ ‹_›)
    ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
      α = ↑p * Real.pi / ↑q ∧
      -- Laurent series only has terms a_n/(z-z₀)^n with n = 2kq/p + 1
      True -- TODO: Formalize Laurent coefficient condition
```

**Note:** The Laurent coefficient condition in (B) is the most technically demanding part to formalize. For the simple pole case (which is what we primarily need), condition (B) is automatic since the only negative Laurent term is `a_{-1}/(z-z₀)`, corresponding to `n = 1`, which always satisfies `1 = 2·0·q/p + 1`.

**Step 2: Prove conditions are automatic for simple poles**

```lean
/-- For simple poles, conditions (A) and (B) are automatically satisfied.
(A): order-1 flatness holds for all piecewise C¹ curves.
(B): the Laurent series has only the n=1 term, compatible with any angle. -/
theorem conditions_AB_automatic_simple_poles
    (γ : PiecewiseC1Immersion) (f : ℂ → ℂ)
    (crossings : Finset ℝ)
    (hcross_in : ∀ t ∈ crossings, t ∈ Set.Ioo γ.a γ.b)
    (hcross_at : ∀ t ∈ crossings, γ.toFun t ∈ S)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) :
    SatisfiesConditionA γ f crossings ∧
    SatisfiesConditionB γ f crossings hcross_in := by
  sorry
```

**Step 3: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/Flatness.lean
git commit -m "feat: define conditions (A) and (B), prove automatic for simple poles"
```

---

## Phase 4: Theorem 3.3 — Replace Generalized Residue Theorem

### Task 8: State the Clean Theorem

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean`

**Context:** Replace `generalizedResidueTheorem'` with a clean version that does NOT take `hPV_singular` as a hypothesis. For simple poles, PV existence is proven from the immersion structure. For higher-order poles, conditions (A) and (B) are required.

**Step 1: Read the current file**

Read: `LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean`

Study the proof structure of the current `generalizedResidueTheorem'` (lines 210-543) to understand what parts can be reused.

**Step 2: Add new imports and state the clean theorem**

Add imports for Proposition2_2, SectorCurve, and Flatness at the top.

```lean
import LeanModularForms.GeneralizedResidueTheory.WindingNumber.Proposition2_2
import LeanModularForms.GeneralizedResidueTheory.Residue.SectorCurve
import LeanModularForms.GeneralizedResidueTheory.Residue.Flatness
```

State the clean theorem (simple pole version first):

```lean
/-- Theorem 3.3 (Hungerbühler-Wasem) — Simple poles version.

For a holomorphic function with simple poles, the Cauchy PV of the contour
integral equals the residue sum weighted by generalized winding numbers.
NO PV existence hypothesis is needed — it is proven from the immersion structure.

Reference: arXiv:1808.00997v2, Theorem 3.3. -/
theorem generalizedResidueTheorem
    (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt
      (fun z => f z - residueSimplePole f s / (z - s)) s) :
    CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b ∧
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueSimplePole f s := by
  sorry
```

**Key difference from old version:** The `hPV_singular` hypothesis is GONE. Instead, PV existence is proved internally using:
1. `cpv_exists_inv_sub` from Prop 2.2 (Phase 1) — proves PV of `1/(z-s)` exists
2. Simple pole decomposition: `f = Σ cₛ/(z-s) + g` where g is regular
3. PV of g exists trivially (no singularity)
4. PV of f = PV of singular part + classical integral of g

**Step 3: Prove the theorem**

**Proof strategy:**
1. Use `simple_poles_decomposition` to write `f = Σ residue_s/(z-s) + g_reg` where g is holomorphic on U
2. For PV existence:
   a. PV of each `residue_s/(z-s)` exists by `cpv_exists_inv_sub` (from Prop 2.2)
   b. PV of `g_reg` exists trivially (continuous, no singularity)
   c. PV of sum exists by linearity
3. For the equality:
   a. PV integral of `g_reg` on closed curve in convex domain = 0 (Cauchy's theorem)
   b. PV integral of `residue_s/(z-s)` = `residue_s · PV ∮ dz/(z-s)` = `residue_s · 2πi · n_s(γ)`
   c. Sum: `Σ residue_s · 2πi · n_s(γ)` = `2πi · Σ n_s · residue_s`

This follows the same structure as the old proof but derives `hPV_singular` internally.

**Step 4: Mark old theorem as deprecated**

```lean
@[deprecated generalizedResidueTheorem (since := "2026-03-08")]
theorem generalizedResidueTheorem' ... := ...
```

Or better: delete the old theorem entirely and update all references.

**Step 5: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean
git commit -m "feat: prove Theorem 3.3 — clean generalized residue theorem without PV hypothesis"
```

---

### Task 9: Higher-Order Poles Extension

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean`

**Context:** Extend the theorem to higher-order poles, requiring conditions (A) and (B).

**Step 1: State the higher-order version**

```lean
/-- Theorem 3.3 (Hungerbühler-Wasem) — Higher-order poles version.

Extends `generalizedResidueTheorem` to allow poles of arbitrary order on the
curve, provided conditions (A) (flatness) and (B) (angle/Laurent compatibility)
are satisfied. For simple poles, these conditions are automatic. -/
theorem generalizedResidueTheorem_higher_order
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    -- Poles of any order (not just simple)
    (hMeromorphic : ∀ s ∈ S0, MeromorphicAt f s)
    -- Conditions (A) and (B) for on-curve singularities
    (crossings : Finset ℝ)
    (hcross_in : ∀ t ∈ crossings, t ∈ Set.Ioo γ.a γ.b)
    (hCondA : SatisfiesConditionA γ f crossings)
    (hCondB : SatisfiesConditionB γ f crossings hcross_in) :
    CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b ∧
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueSimplePole f s := by
  sorry
```

**Note:** This is lower priority than the simple pole version. The valence formula only needs simple poles. This task can be deferred.

**Step 2: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Residue/GeneralizedTheorem.lean
git commit -m "feat: state higher-order poles extension of Theorem 3.3"
```

---

## Phase 5: ValenceFormula Downstream Update

### Task 10: Update ValenceFormula to Use New Theorem

**Files:**
- Modify: Files in `LeanModularForms/ValenceFormula/` that reference the old theorem

**Context:** After replacing `generalizedResidueTheorem'` with `generalizedResidueTheorem`, update all downstream usage to drop the `hPV_singular` hypothesis.

**Step 1: Find all references to the old theorem**

Run: `grep -r "generalizedResidueTheorem'" LeanModularForms/ValenceFormula/`
Run: `grep -r "hPV_singular" LeanModularForms/ValenceFormula/`

**Step 2: Update each reference**

For each file referencing `generalizedResidueTheorem'`:
1. Change the theorem name to `generalizedResidueTheorem`
2. Remove the `hPV_singular` argument
3. Verify compilation

**Step 3: Verify full build**

Run: `lake build`
Expected: 0 errors

**Step 4: Commit**

```bash
git add LeanModularForms/ValenceFormula/
git commit -m "refactor: update ValenceFormula to use clean residue theorem"
```

---

## Phase 6: Cycle Support

### Task 11: Define Cycles

**Files:**
- Create: `LeanModularForms/GeneralizedResidueTheory/Cycle.lean`

**Context:** A cycle is a formal integer-weighted sum of closed piecewise C¹ immersions: `C = Σ mₗ γₗ`.

**Step 1: Define the Cycle type**

```lean
/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic

/-!
# Cycles — Formal Integer-Weighted Sums of Curves

A cycle `C = Σ mₗ γₗ` is a formal sum of closed piecewise C¹ immersions
with integer multiplicities.
-/

open Complex Set

noncomputable section

/-- A cycle is a formal integer-weighted sum of closed piecewise C¹ immersions. -/
structure Cycle where
  curves : List PiecewiseC1Immersion
  multiplicities : List ℤ
  h_lengths : curves.length = multiplicities.length
  h_closed : ∀ γ ∈ curves, γ.toPiecewiseC1Curve.IsClosed

/-- The winding number of a cycle at a point. -/
def Cycle.windingNumber (C : Cycle) (z₀ : ℂ) : ℂ :=
  (List.zip C.multiplicities C.curves).foldl
    (fun acc ⟨m, γ⟩ => acc + m * generalizedWindingNumber' γ.toFun γ.a γ.b z₀) 0

/-- A cycle is null-homologous in U if every winding number vanishes
for points outside U. -/
def Cycle.IsNullHomologousIn (C : Cycle) (U : Set ℂ) : Prop :=
  ∀ z₀ ∉ U, C.windingNumber z₀ = 0

end
```

**Step 2: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Cycle.lean
git commit -m "feat: define Cycle type for formal sums of curves"
```

---

### Task 12: Lift Residue Theorem to Cycles

**Files:**
- Modify: `LeanModularForms/GeneralizedResidueTheory/Cycle.lean`

**Step 1: State the cycle version**

```lean
/-- Theorem 3.3 for cycles: PV integral over a null-homologous cycle
equals the residue sum weighted by cycle winding numbers. -/
theorem generalizedResidueTheorem_cycle
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (C : Cycle)
    (hC_in_U : ∀ γ ∈ C.curves, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt
      (fun z => f z - residueSimplePole f s / (z - s)) s) :
    -- PV integral over cycle = 2πi · Σ n_s(C) · res_s(f)
    sorry := by
  sorry
```

**Proof strategy:** Apply `generalizedResidueTheorem` to each curve in the cycle, then take the integer-weighted sum. By linearity of PV integrals and winding numbers.

**Step 2: Verify and commit**

Run: `lake build`

```bash
git add LeanModularForms/GeneralizedResidueTheory/Cycle.lean
git commit -m "feat: state generalized residue theorem for cycles"
```

---

## Dependency Graph

```
Task 1 (finite_crossings)
  └─► Task 2 (cpv_exists_inv_sub)
       └─► Task 3 (proposition_2_2)
            └─► Task 8 (generalizedResidueTheorem)
                 ├─► Task 9 (higher_order — optional)
                 ├─► Task 10 (ValenceFormula update)
                 └─► Task 12 (cycle version)

Task 4 (sectorCurveImmersion)
  └─► Task 5 (pv_sector_dz_over_z, lemma_3_1)
       └─► Task 8 (generalizedResidueTheorem)

Task 6 (IsFlatOfOrder)
  └─► Task 7 (conditions A+B)
       └─► Task 9 (higher_order)

Task 11 (Cycle type)
  └─► Task 12 (cycle version)
```

**Critical path:** Tasks 1 → 2 → 3 → 8 → 10

**Parallelizable:** Tasks 4-5 can run in parallel with Tasks 1-3. Tasks 6-7 can run in parallel with everything else (only needed for Task 9).

---

## Priority Order

1. **Tasks 1-2** (HIGH): Finite crossings + PV existence — core of Prop 2.2
2. **Tasks 4-5** (HIGH): Sector curve PV — needed for residue formula
3. **Task 8** (HIGH): Clean theorem statement — the goal
4. **Task 3** (MEDIUM): Full Prop 2.2 angle formula — nice to have, may not be strictly needed if Task 8 can be proved more directly
5. **Task 10** (MEDIUM): Downstream update — mechanical after Task 8
6. **Tasks 6-7, 9** (LOW): Higher-order poles — not needed for valence formula
7. **Tasks 11-12** (LOW): Cycles — extension, not needed for valence formula

---

## Notes for Implementer

### Key Mathematical Insight

The fundamental insight of the proof is that PV existence for `f(z) dz` at an on-curve singularity follows from:
1. Decompose `f = singular part + regular part` (simple pole decomposition, already proven)
2. Regular part integral exists classically (no singularity)
3. Singular part `c/(z-z₀)` has PV that exists by Prop 2.2 (the immersion property + C² at crossing gives dyadic convergence)
4. Therefore PV of `f` exists = PV of singular part + classical integral of regular part

### What's Already Proven

Much of the hard analysis is done:
- `pv_limit_via_dyadic`: 130-line proof of PV existence at single crossing (dyadic Cauchy criterion)
- `simple_poles_decomposition`: decomposes f into singular + regular parts
- `integral_eq_sum_residues_of_avoids`: classical residue theorem for non-crossing curves
- `cpv_avoidance` + `cpv_concat`: gluing PV across intervals

### What's New

The main new work is:
1. **Finite crossings** (Task 1): ~50 lines, use immersion + compactness
2. **Assembling PV over all crossings** (Task 2): ~100 lines, iterate `cpv_concat`
3. **Sector curve computation** (Task 5): ~150 lines, explicit integral calculation
4. **Combining into clean theorem** (Task 8): ~100 lines, assemble from existing pieces

### Testing Strategy

Every step is verified by `lake build`. There are no separate test files — the type checker IS the test. A theorem compiling without `sorry` means it's correct.

After each task, run:
```bash
lake build 2>&1 | grep -E "error|sorry"
```
to check for errors and count remaining sorries.

### Lean-Specific Tips

- Use `lean_goal` MCP tool to inspect proof state at any point
- Use `lean_multi_attempt` to try multiple tactics: `["simp", "ring", "omega", "linarith", "norm_num"]`
- Use `lean_leansearch` for natural language mathlib search: e.g., "compact set finite preimage continuous"
- Use `lean_loogle` for type pattern search: e.g., `IsCompact → Set.Finite`
- Check `CLAUDE.md` for project-specific conventions and common pitfalls
