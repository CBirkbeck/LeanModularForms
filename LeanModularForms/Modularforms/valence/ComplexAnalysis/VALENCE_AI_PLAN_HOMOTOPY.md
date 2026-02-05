# Valence Formula – Homotopy Work Plan (Rect/Polygon Path)

**Scope for AI:** finish the homotopy proof used to show
`generalizedWindingNumber_fdBoundary_eq_one` in
`ValenceFormula_InteriorWinding.lean` (the split successor of
`ValenceFormula_Rect_Homotopy.lean`).

**Target deliverable (no sorries in this file):**
```
theorem generalizedWindingNumber_fdBoundary_eq_one
  (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2) (hp_im : p.im < H_height) :
  generalizedWindingNumber' fdBoundary 0 5 p = 1
```

**Critical-path note:** this lemma feeds the **core** valence formula via
`effectiveWinding_eq_windingNumberCoeff'`. Finish this file first.

---

## 0) Snapshot of remaining sorries (from `rg -n "sorry"`)

In `ValenceFormula_InteriorWinding.lean` (migrated from the Rect‑Homotopy file) the remaining sorries are:
- `H_deriv_seg2_continuousOn`, `H_deriv_seg3_continuousOn`
- `hH1_deriv_cont` (segments 2/3/4 case split)
- `hH1_bound` partition point edges t=1,2,3,4
- `hH1_bound` segment‑2/3 interior bound
- `polygonToCircleRadial` derivative continuity + bound
- `h_circle` (winding of `circleFromPolygon` = 1)
- (Optional/not critical) `fdPolygon_not_differentiableAt_partition`

Do **not** start new big proofs. Break them into small helper lemmas.

**After split imports:** this file should import
`ValenceFormulaDefinitions`, `ValenceFormula_FD_Boundary`,
`WindingNumberInterior`, and `PiecewiseHomotopy`.

---

## 1) Group A – Finish hhom₁ (fdBoundary → fdPolygon)

### 1.1 Segment‑wise derivative formulas (small lemmas)
You already have `fdBoundaryToPolygonHomotopy_seg2_differentiable` and
`fdBoundaryToPolygonHomotopy_seg3_differentiable`. Next, expose the **explicit**
derivative formulas to make continuity/bounds trivial.

Add helper lemmas (exact statements):
```
lemma H_seg2_deriv_formula (t s : ℝ) :
  deriv (fun t' : ℝ =>
    let arc := Complex.exp ((Real.pi / 3 + (t' - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
    let chord := chordSegment rho' i_point (t' - 1)
    (1 - s) • arc + s • chord) t
  = (1 - s) * (Real.pi / 6) * I *
      Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
    + s * (i_point - rho')

lemma H_seg3_deriv_formula (t s : ℝ) :
  deriv (fun t' : ℝ =>
    let arc := Complex.exp ((Real.pi / 2 + (t' - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
    let chord := chordSegment i_point rho (t' - 2)
    (1 - s) • arc + s • chord) t
  = (1 - s) * (Real.pi / 6) * I *
      Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
    + s * (rho - i_point)
```
**How:** use `deriv_add`, `deriv_const_smul`, `deriv_cexp`, `deriv_linear` for chord.
Then simplify with `simp` and `ring`.

### 1.2 Prove continuity on segments 2/3
Now `H_deriv_seg2_continuousOn` / `H_deriv_seg3_continuousOn` reduce to
continuity of the RHS formulas.

Use:
```
continuous_exp : Continuous (fun x => Complex.exp x)
continuous_const, continuous_fst, continuous_snd
```
and `ContinuousOn` composition. Show each factor is continuous:
- `t ↦ exp((a + b*t) * I)` continuous
- `s ↦ (1-s)` continuous
- chord constant derivative `i_point - rho'`, `rho - i_point`

Then `ContinuousOn.add` and `ContinuousOn.mul` finish.

### 1.3 Finish `hH1_deriv_cont`
In `hH1_deriv_cont`, the only sorry is the branch:
```
-- Remaining segments 2, 3, 4
sorry -- Segments 2, 3, 4 derivative continuity
```
Break it up with **three tiny lemmas** and use them in the case split:

```
lemma H_deriv_cont_seg2 :
  ContinuousOn (fun q => deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
    (Ioo 1 2 ×ˢ Icc 0 1)

lemma H_deriv_cont_seg3 :
  ContinuousOn (fun q => deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
    (Ioo 2 3 ×ˢ Icc 0 1)

lemma H_deriv_cont_seg4 :
  ContinuousOn (fun q => deriv (fun t' => fdBoundaryToPolygonHomotopy (t', q.2)) q.1)
    (Ioo 3 4 ×ˢ Icc 0 1)
```
Then in `hH1_deriv_cont`, prove `Ioo p₁ p₂` is contained in exactly one of
`(1,2),(2,3),(3,4)` and apply the appropriate lemma.

### 1.4 Finish `hH1_bound`
Two sub-problems:

**(a) interior bounds on segments 2,3**
Use the explicit derivative formulas from 1.1 and show:
```
‖(1-s)*(π/6)*I*exp(...) + s*(i_point - rho')‖ ≤ 5
‖(1-s)*(π/6)*I*exp(...) + s*(rho - i_point)‖ ≤ 5
```

**Small helper lemmas** (exactly):
```
lemma exp_norm_one (θ : ℝ) : ‖Complex.exp (θ * I)‖ = 1

lemma seg2_deriv_bound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
  ‖(1-s)*(Real.pi/6)*I*Complex.exp( ... ) + s*(i_point - rho')‖ ≤ 5

lemma seg3_deriv_bound (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) :
  ‖(1-s)*(Real.pi/6)*I*Complex.exp( ... ) + s*(rho - i_point)‖ ≤ 5
```
Use `‖a+b‖ ≤ ‖a‖+‖b‖`, `‖exp(… )‖=1`, `‖i_point - rho'‖ ≤ 2`, `‖rho - i_point‖ ≤ 2`,
`|1-s| ≤ 1`, `0 ≤ s ≤ 1`, and `π/6 < 1`.

**(b) partition points t=1,2,3,4**
Inside `hH1_bound` you are already in the branch `hd : DifferentiableAt`. Instead of
trying to compute a derivative at the partition, **prove this cannot happen**:

```
lemma fdBoundaryToPolygonHomotopy_not_differentiableAt_partition
  (s : ℝ) (hs : s ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : t ∈ ({1,2,3,4}:Finset ℝ)) :
  ¬ DifferentiableAt ℝ (fun t' => fdBoundaryToPolygonHomotopy (t', s)) t
```

Then in each partition branch, do:
```
exfalso; exact (fdBoundaryToPolygonHomotopy_not_differentiableAt_partition s hs t ht) hd
```
which discharges the branch without numeric bounds.

To prove `..._not_differentiableAt_partition`, reuse the earlier derivative mismatch
lemmas at t=1..4 (`fdPolygon_deriv_ne_at_t1` etc.) and the fact that on each side
of the partition the homotopy reduces to a smooth formula with distinct derivatives.

---

## 2) Group B – Finish hhom₂ (fdPolygon → circleFromPolygon)

### 2.1 Derivative continuity on pieces
In the `hhom₂` block, the sorry is:
```
-- Derivative continuity of radial homotopy
```
Add a lemma:
```
lemma polygonToCircleRadial_deriv_continuousOn_piece
  (p : ℂ) (p₁ p₂ : ℝ) (hp₁p₂ : p₁ < p₂)
  (h_no_partition : ∀ t ∈ Ioo p₁ p₂, t ∉ ({1,2,3,4}:Finset ℝ))
  (h_in_Ioo : Ioo p₁ p₂ ⊆ Ioo 0 5)
  (h_ne : ∀ t ∈ Icc 0 5, fdPolygon t ≠ p) :
  ContinuousOn
    (fun q : ℝ × ℝ => deriv (fun t' => polygonToCircleRadial p (t', q.2)) q.1)
    (Ioo p₁ p₂ ×ˢ Icc 0 1)
```

**How:**
- On an interval without partition points, `fdPolygon` is affine → `deriv fdPolygon` constant.
- Use chain rule on `polygonToCircleRadial` with `dir = fdPolygon t - p`.
- Use `norm_deriv_normalized_le` (from `WindingNumberInterior.lean`) to bound and show
  continuity of the normalized direction derivative.
- Combine with continuity of coefficients `(1-s)*‖dir‖ + s`.

### 2.2 Derivative bound for radial homotopy
Add lemma:
```
lemma polygonToCircleRadial_deriv_bound
  (p : ℂ) (h_ne : ∀ t ∈ Icc 0 5, fdPolygon t ≠ p) :
  ∃ M, ∀ t ∈ Icc 0 5, ∀ s ∈ Icc (0:ℝ) 1,
    ‖deriv (fun t' => polygonToCircleRadial p (t', s)) t‖ ≤ M
```

**How:**
- Use the bound on `‖deriv fdPolygon‖` (already ≤ 3 in file).
- Use `dir_norm_lower_bound` to get δ > 0 with ‖dir‖ ≥ δ.
- Apply `norm_deriv_normalized_le` to bound derivative of `dir/‖dir‖`.
- Combine bounds in the formula for derivative of
  `p + ((1-s)*‖dir‖ + s) • (dir/‖dir‖)`.

This is **exactly** the pattern used in `safeRotationHomotopy_deriv_bound_lipschitz`
from `WindingNumberInterior.lean` — reuse that proof structure.

---

## 3) Group C – Finish `h_circle`

`circleFromPolygon` is a unit‑circle loop around `p`.
We need:
```
have h_circle : generalizedWindingNumber' (circleFromPolygon p) 0 5 p = 1
```

### Option A (preferred, small lemmas)
Show `circleFromPolygon` is a **reparameterization** of `circleParam`:

1. Prove the loop is on the unit circle:
```
lemma circleFromPolygon_on_circle (p : ℂ) (t : ℝ) :
  ‖circleFromPolygon p t - p‖ = 1
```
2. Build an angle lift `θ : ℝ → ℝ` with `circleFromPolygon p t = p + exp(I*θ t)`.
3. Prove `θ(5) - θ(0) = 2π` (loop wraps once).
4. Use reparameterization invariance:
```
lemma winding_eq_of_reparam_circle
  (φ : ℝ → ℝ) (hφ_mono : MonotoneOn φ (Icc 0 5))
  (hφ_end : φ 0 = 0 ∧ φ 5 = 5) :
  generalizedWindingNumber' (circleParam p 1 0 5 ∘ φ) 0 5 p =
  generalizedWindingNumber' (circleParam p 1 0 5) 0 5 p
```
Then show `circleFromPolygon = circleParam ∘ φ`.

### Option B (fallback)
Show `circleFromPolygon` is homotopic to `circleParam` **within the circle**, using
angle interpolation:
```
H(t,s) = p + exp(I * ((1-s)θ_poly(t) + s θ_circ(t)))
```
This avoids antipodality because it stays on the unit circle. Prove the 8
homotopy conditions with trivial bounds (derivative is bounded by |θ'|).

---

## 4) Final assembly checklist

When all Group A/B/C sorries are resolved:
1. `hH1_deriv_cont` + `hH1_bound` → finish `hhom₁`.
2. `polygonToCircleRadial_deriv_continuousOn_piece` + bound → finish `hhom₂`.
3. `h_circle` → get `winding(circleFromPolygon)=1`.
4. `generalizedWindingNumber_fdBoundary_eq_one` completes.

---

## Reporting back (required)
When you return, include:
- Which lemmas you completed (by name),
- Any new helper lemmas you introduced,
- The **main blockers** still remaining (if any).

Keep proofs short. If a proof grows, split it into helper lemmas first.
