# Valence Formula – PV Work Plan

**Scope for AI:** finish the PV infrastructure needed for the modular side of the valence formula.  
Primary file (after split): `ValenceFormula_PV.lean`.  
Ignore any `❌ NOT TARGET` sorries (homotopy/core work).

**After split imports:** this file should import
`ValenceFormulaDefinitions`, `ValenceFormula_FD_Boundary`,
`PrincipalValue`, `ResidueTheory`, and any curve infrastructure needed.

Target deliverable: a sorry‑free

```
lemma pv_integral_eq_modular_transformation ...
```

so that core work can close `pv_equals_modular_total`.

---

## 0) Required dependency chain (must be completed in order)

1) `cauchy_integral_difference_bound`  
2) `cauchy_cutoff_of_linear_approx`  
3) `immersion_crossing_cauchy` (smooth + corner)  
4) `pv_integral_exists_f'_over_f` (uses `immersion_crossing_cauchy`)  
5) `pv_integral_decompose_segments` **or** bypass with direct assembly  
6) `pv_integral_eq_modular_transformation`

Everything above is already scaffolded in the file, with helper lemmas A1–A5.

---

## 1) Finish `cauchy_integral_difference_bound`

**Current state:** A1–A4 are mostly done; A5 is bookkeeping assembly.

### 1.1 Use the A‑lemmas as a fixed pipeline

For `cauchy_integral_difference_bound`, the proof should **not** invent new math; just assemble:

- **A1**: `cutoff_upper_bound_t`
- **A1'**: `cutoff_lower_bound_t`
- **A2**: `integrand_split_bound` / `integrand_asymptotic`
- **A3**: `singular_annulus_cancels`
- **A4**: `remainder_annulus_bound`
- **A5 helpers already in file:**  
  `cutoff_diff_eq_annulus`, `annulus_maps_to_t_annulus`, `taylor_upper_bound`

**Precise assembly lemma** (add if missing):

```
lemma annulus_integral_bound
  (r : ℝ → ℂ) (t₀ c₁ c₂ η : ℝ)
  (hc₁_pos : 0 < c₁) (hc₂_pos : 0 < c₂) (hc₁₂ : c₁ < c₂)
  (hr : ∀ t, c₁ < |t - t₀| → |t - t₀| < c₂ → ‖r t‖ ≤ η / |t - t₀|) :
  ‖∫_{t₀-c₂}^{t₀-c₁} r + ∫_{t₀+c₁}^{t₀+c₂} r‖ ≤ 2 * η * log(c₂/c₁)
```

Then in A5 (use existing helper lemmas, do **not** re‑prove calculus):

```
I(ε₁) - I(ε₂)
 = ∫ annulus (1/(t-t₀) + r(t))
 = ∫ annulus 1/(t-t₀) + ∫ annulus r(t)
```

Use A3 to show the singular part cancels; use A4 to bound the remainder.

### 1.2 Concrete check list for A5

1. From `h_asymp` get the `η`‑bound for `r(t)`.
2. From `h_lower` + `taylor_upper_bound` get the t‑annulus bounds.
3. Translate γ‑annulus to t‑annulus via `cutoff_lower_bound_t` / `cutoff_upper_bound_t`.
4. Use `cutoff_diff_eq_annulus` to rewrite `I(ε₁) - I(ε₂)` as the annulus integral.
4. Apply A3 and A4.
5. Choose `η` small enough (already done in file) to force `< ε'`.

---

## 2) Finish `cauchy_cutoff_of_linear_approx`

**Target statement** (verify matches file):

```
lemma cauchy_cutoff_of_linear_approx (γ : ℝ → ℂ) (a b t₀ : ℝ)
  (hat₀ : t₀ ∈ Ioo a b) (L : ℂ) (hL : L ≠ 0)
  (hγ_hasderiv : HasDerivAt γ L t₀)
  (hγ_cont_deriv : ContinuousOn (deriv γ) (Icc a b)) :
  Cauchy (Filter.map (fun ε => ∫ ... cutoff ...) (𝓝[>] 0))
```

**How to finish:** call `cauchy_integral_difference_bound` with:
- `h_asymp` from `integrand_split_bound`
- `h_lower` from the remainder bound with ε = ‖L‖/2
- `hγ_cont_deriv` for uniform derivative bounds

Then close the Cauchy goal with the bound (avoid log‑ratio explosion by using A5).

---

## 3) Finish `immersion_crossing_cauchy`

Two cases inside:

### 3.1 Smooth case (t₀ not in partition)

Add a helper lemma to localize the interval:

```
lemma exists_partition_free_interval
  (γ : PiecewiseC1Immersion) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo γ.a γ.b)
  (ht₀_part : t₀ ∉ γ.partition) :
  ∃ a' b', a' < t₀ ∧ t₀ < b' ∧
    Icc a' b' ⊆ Icc γ.a γ.b ∧
    (∀ t ∈ Ioo a' b', t ∉ γ.partition)
```

Then apply `cauchy_cutoff_of_linear_approx` on `[a',b']` and show the far parts are constant
for small ε.

### 3.2 Corner case (t₀ in partition)

Use one‑sided derivatives. You don’t need the exact angle, only **existence** of the limit.

Introduce helper lemma:

```
lemma cauchy_cutoff_of_linear_approx_one_sided
  (γ : ℝ → ℂ) (a b t₀ : ℝ)
  (hat₀ : t₀ ∈ Ioo a b)
  (L₊ L₋ : ℂ) (hL₊ : L₊ ≠ 0) (hL₋ : L₋ ≠ 0)
  (h_right : HasDerivAt γ L₊ t₀) (h_left : HasDerivAt γ L₋ t₀) :
  Cauchy (Filter.map ... )
```

Apply to left/right intervals separately and combine. If this is too hard,
reduce to smooth case on each side + additivity of integrals.

---

## 4) Finish `pv_integral_exists_f'_over_f`

Once `immersion_crossing_cauchy` is solved, this is mechanical:

- Use `cauchyPrincipalValueOn_singular_sum` from `ResidueTheory.lean`.
- Provide: simple pole at each zero (`hasSimplePoleAt_logDeriv_of_zero`).
- Provide: `CauchyPrincipalValueExists'` for each singular term (from `immersion_crossing_cauchy`).
- Regular part continuity: **use `regularPartExt`** instead of the naive formula.

If the file still requires the naive `continuousOn_logDeriv_regular_part`,
replace it by `continuousOn_regularPartExt` and justify equality a.e.

---

## 5) Segment decomposition vs direct assembly

You can finish `pv_integral_eq_modular_transformation` either by:

### Option A: Prove `pv_integral_decompose_segments`

Define explicit parameterizations for the 5 FD boundary pieces and apply
`cauchyPrincipalValue_split` four times.

Helper lemmas (precise):

```
lemma fd_seg1_param : ... = right vertical
lemma fd_seg2_param : ... = arc ρ'→i
lemma fd_seg3_param : ... = arc i→ρ
lemma fd_seg4_param : ... = left vertical
lemma fd_seg5_param : ... = top horizontal

lemma pv_split_four_times ... :
  PV(γ) = PV(seg1) + PV(seg2) + PV(seg3) + PV(seg4) + PV(seg5)
```

### Option B (recommended): Skip explicit decomposition

Use the already‑proved components directly in `pv_integral_eq_modular_transformation`:
- `pv_integral_vertical_cancel` (T‑invariance)
- `arc_contribution_is_k_div_12`
- `cusp_contribution` (q‑expansion)

Then show the PV integral equals the sum of those three by arguing:
`cauchyPrincipalValueOn` reduces to the ordinary integral on each segment
(where no singularities lie), and the integral is additive.

This is acceptable for valence formula if you justify additivity for PV.

---

## 6) Final assembly: `pv_integral_eq_modular_transformation`

**Precise goal:**

```
lemma pv_integral_eq_modular_transformation {k : ℤ}
  (f : ModularForm (Gamma 1) k) (γ : PiecewiseC1Immersion) ... :
  cauchyPrincipalValueOn S0 (f'/f) γ = 2πi * (k/12 - ord_∞ f)
```

**Assembly steps:**
1. Use segment decomposition (Option A or B).
2. Cancel vertical edges.
3. Evaluate arc.
4. Evaluate cusp.

---

## Reporting back (required)
When you return, include:
- Which lemmas you completed (by name),
- Any new helper lemmas you introduced,
- The **main blockers** still remaining (if any).

Keep proofs short. If a proof grows, split it into helper lemmas first.
5. Ring to factor into `2πi * (k/12 - ord_∞)`.

---

## 7) Reporting requirements

When you report back, include:
- which lemma you completed,
- which helper lemmas you introduced,
- any blocker you hit (with line number).
