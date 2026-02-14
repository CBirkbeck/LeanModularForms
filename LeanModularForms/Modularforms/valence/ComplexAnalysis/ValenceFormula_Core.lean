/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ResidueSide
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ModularSide
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ModularSide_Param

/-!
# Core Identity of the Valence Formula

This file establishes the core identity of the valence formula by equating the
residue side and the modular side.

## Main Result

* `valence_formula_base_identity`: The fundamental identity
  Σ (effectiveWinding(p) · ord_p(f)) = k/12 - ord_∞(f)

## The Core Identity

The valence formula follows from equating two computations of the same PV integral:

**Residue Side** (from `ValenceFormula_ResidueSide`):
  PV ∮_{∂𝒟} f'/f dz = 2πi · Σ_p effectiveWinding(p) · ord_p(f)

**Modular Side** (from `ValenceFormula_ModularSide`):
  PV ∮_{∂𝒟} f'/f dz = 2πi · (k/12 - ord_∞(f))

Equating and dividing by 2πi:
  Σ_p effectiveWinding(p) · ord_p(f) = k/12 - ord_∞(f)

## Expanding the Sum

The left side expands to:
  (1) · Σ_{p ∈ interior} ord_p(f) + (1/2) · ord_i(f) + (1/3) · ord_ρ(f)

Which gives the classical valence formula:
  ord_∞(f) + (1/2) · ord_i(f) + (1/3) · ord_ρ(f) + Σ_{p ∈ 𝒟°} ord_p(f) = k/12

## References

See `VALENCE_AI_PLAN_CORE.md` for the detailed proof strategy.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ## Contour Computation Equality -/

/-- Equating residue side and modular side (CW orientation).

Both sides have a negative sign from the clockwise orientation.
We cancel -(2πi) to equate the two sides directly. -/
theorem contour_computation_equality :
    (∀ zeros : Finset ℍ, (∀ s ∈ zeros, f s = 0) → (∀ s ∈ zeros, s ∈ fundamentalDomain) →
      (∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) →
      pv_integral f fdBoundary 0 5 =
        -(2 * Real.pi * I * ∑ s ∈ zeros,
          (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) →
    pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) →
    ∀ zeros : Finset ℍ, (∀ s ∈ zeros, f s = 0) → (∀ s ∈ zeros, s ∈ fundamentalDomain) →
      (∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros) →
      ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
        (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  intro h_residue h_modular zeros hzeros hzeros_fd hzeros_complete
  have h1 := h_residue zeros hzeros hzeros_fd hzeros_complete
  have h3 : -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) =
      -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
    rw [← h1, h_modular]
  have hpi : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  exact mul_left_cancel₀ hpi (neg_inj.mp h3)

/-! ## The Core Identity -/

include hf

/-- **The Core Identity**: The sum of weighted orders equals k/12 - ord_∞.

This is the BASE theorem of the valence formula. It states:
  Σ_p effectiveWinding(p) · ord_p(f) = k/12 - ord_∞(f)

where the sum is over all points p in the fundamental domain 𝒟' where f vanishes.

**Proof**:
1. By the residue side: PV ∮ f'/f = 2πi · Σ effectiveWinding(p) · ord_p(f)
2. By the modular side: PV ∮ f'/f = 2πi · (k/12 - ord_∞(f))
3. Equating: Σ effectiveWinding(p) · ord_p(f) = k/12 - ord_∞(f)

The effectiveWinding coefficients are:
- Interior points: 1
- At i: 1/2
- At ρ: 1/3
-/
theorem valence_formula_base_identity (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  exact contour_computation_equality f
    (pv_equals_residue_sum f hint)
    (modular_side_mult_form f hf hint hcusp_nonvan)
    zeros hzeros hzeros_fd hzeros_complete

/-! ## Unconditional Sum Decomposition

The following lemmas prove the sum decomposition WITHOUT requiring `hclass`,
by using the fact that `effectiveWinding = 0` for all "boundary" cases.
This eliminates the need for `zeros_in_fd_are_classified4` and related sorry'd theorems. -/

omit hf in
/-- effectiveWinding is 0 for points not classified as interior, i, or ρ.
This covers: high-altitude zeros, left/right edge zeros, arc non-elliptic zeros,
and any other non-interior FD point. -/
lemma effectiveWinding_eq_zero_of_boundary_case (p : ℍ)
    (h1 : ¬isInteriorPoint p) (h2 : p ≠ ellipticPoint_i') (h3 : p ≠ ellipticPoint_rho') :
    effectiveWinding p = 0 := by
  have hcp : classifyPoint p = .boundary := by
    unfold classifyPoint
    rw [if_neg h2, if_neg h3]
    unfold isInteriorPoint at h1
    exact if_neg h1
  simp [effectiveWinding, hcp]

omit hf in
/-- Pointwise: ew(s)*ord(s) decomposes into three conditional terms.
The boundary case contributes 0 because ew = 0. -/
private lemma effectiveWinding_term_split (s : ℍ) :
    (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (if s = ellipticPoint_i' then (1/2 : ℂ) * (orderOfVanishingAt' f s : ℂ) else 0) +
      (if s = ellipticPoint_rho' then (1/3 : ℂ) * (orderOfVanishingAt' f s : ℂ) else 0) +
      (if isInteriorPoint s then (orderOfVanishingAt' f s : ℂ) else 0) := by
  rcases em (s = ellipticPoint_i') with rfl | hi
  · have h1 : ¬isInteriorPoint ellipticPoint_i' := fun h => isInteriorPoint_ne_i _ h rfl
    have h2 : ellipticPoint_i' ≠ ellipticPoint_rho' := ellipticPoint_i_ne_rho
    rw [if_pos rfl, if_neg h2, if_neg h1, effectiveWinding_eq_half_at_i]
    push_cast; ring
  · rcases em (s = ellipticPoint_rho') with rfl | hr
    · have h1 : ¬isInteriorPoint ellipticPoint_rho' := fun h => isInteriorPoint_ne_rho _ h rfl
      rw [if_neg hi, if_pos rfl, if_neg h1, effectiveWinding_eq_third_at_rho]
      push_cast; ring
    · rcases em (isInteriorPoint s) with hint | hint
      · rw [if_neg hi, if_neg hr, if_pos hint, effectiveWinding_eq_one_of_interior s hint]
        push_cast; ring
      · rw [if_neg hi, if_neg hr, if_neg hint,
            effectiveWinding_eq_zero_of_boundary_case s hint hi hr]
        push_cast; ring

omit hf in
/-- The weighted sum decomposes unconditionally (without `hclass`).

This is the key lemma that makes the 3 classification sorries unnecessary:
boundary points have `effectiveWinding = 0`, so they contribute nothing. -/
lemma sum_ew_ord_decompose_unconditional (zeros : Finset ℍ) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
        (orderOfVanishingAt' f s : ℂ) := by
  simp_rw [effectiveWinding_term_split f]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1; congr 1
  · rw [Finset.sum_ite_eq']; split_ifs <;> ring
  · rw [Finset.sum_ite_eq']; split_ifs <;> ring
  · exact (Finset.sum_filter (fun s => isInteriorPoint s) _).symm

/-! ## Conditional Sum Decomposition

`sum_ew_ord_decompose` and `zeros_decomposition` previously lived here but required
a `hclass` hypothesis (every zero is interior/i/ρ) which is FALSE for:
- high-altitude zeros (im ≥ H_height)
- left/right edge zeros (|re| = 1/2, z ≠ ρ, ρ+1)
- arc non-elliptic zeros (‖z‖ = 1, z ≠ i, ρ)

Replaced by `sum_ew_ord_decompose_unconditional` above, which handles all
boundary cases via `effectiveWinding = 0`. -/

/-! ## Classical Form -/

/-- The classical form of the valence formula.

Expanding the effectiveWinding coefficients:
  ord_∞(f) + (1/2) · ord_i(f) + (1/3) · ord_ρ(f) + Σ_{p ∈ interior} ord_p(f) = k/12

From `valence_formula_base_identity` + `sum_ew_ord_decompose_unconditional`.

This does NOT require any zero-classification hypothesis (`hclass`):
boundary points (high-altitude, left/right edge, arc non-elliptic, etc.) all
have `effectiveWinding = 0` and contribute nothing to the sum. -/
theorem valence_formula_classical_form (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 := by
  have h_base := valence_formula_base_identity f hf zeros hzeros hzeros_fd
    hzeros_complete hint hcusp_nonvan
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

/-- Alias for `valence_formula_classical_form` (kept for backward compat). -/
theorem valence_formula_classical_form_unconditional (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 :=
  valence_formula_classical_form f hf zeros hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-! ## Geometric Micro-Lemmas (sorry-free, useful for reference)

These are proven geometric facts about the fundamental domain that may be useful
for future refinements. They do NOT depend on any sorry'd theorems. -/

omit hf in
/-- A point on the left edge (Re = -1/2) of 𝒟c with ‖z‖ = 1 is ρ.

Proof: from ‖z‖ = 1 and Re = -1/2, we get Im² = 1 - 1/4 = 3/4.
Since Im > 0 (z ∈ ℍ), Im = √3/2. So z = -1/2 + (√3/2)·I = ρ. -/
theorem left_edge_zero_is_rho (s : ℍ)
    (hs_re : (s : ℂ).re = -1/2)
    (hs_norm : ‖(s : ℂ)‖ = 1) :
    s = ellipticPoint_rho' := by
  have him_pos : (s : ℂ).im > 0 := s.im_pos
  have h_sq : (s : ℂ).re ^ 2 + (s : ℂ).im ^ 2 = 1 := by
    have h1 : Complex.normSq (s : ℂ) = 1 := by
      have : ‖(s : ℂ)‖ * ‖(s : ℂ)‖ = 1 := by rw [hs_norm]; ring
      rwa [show ‖(s : ℂ)‖ * ‖(s : ℂ)‖ = Complex.normSq (s : ℂ) from
        Real.mul_self_sqrt (Complex.normSq_nonneg _)] at this
    rw [Complex.normSq_apply] at h1; nlinarith
  have him_sq : (s : ℂ).im ^ 2 = 3 / 4 := by nlinarith
  have him_val : (s : ℂ).im = Real.sqrt 3 / 2 := by
    have h1 : ((s : ℂ).im - Real.sqrt 3 / 2) * ((s : ℂ).im + Real.sqrt 3 / 2) = 0 := by
      have : (Real.sqrt 3 / 2) ^ 2 = 3 / 4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (3:ℝ) ≥ 0)]; norm_num
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right (by positivity))
  have hre_bridge : s.re = (s : ℂ).re := (UpperHalfPlane.coe_re s).symm
  have him_bridge : s.im = (s : ℂ).im := (UpperHalfPlane.coe_im s).symm
  apply UpperHalfPlane.ext; apply Complex.ext
  · simp only [ellipticPoint_rho']
    simp [add_re, neg_re, one_re, div_ofNat, mul_re, I_re, I_im, ofReal_re, ofReal_im]
    linarith
  · simp only [ellipticPoint_rho']
    simp [add_im, neg_im, one_im, div_ofNat, mul_im, I_re, I_im, ofReal_re, ofReal_im]
    linarith

omit hf in
/-- A point in 𝒟c is either strictly interior (norm > 1, re > -1/2),
on the arc (norm = 1), or on the left edge (re = -1/2, norm > 1).

This trichotomy decomposes classification into the three geometric cases.
Proved by case-splitting on ‖z‖ = 1 vs > 1, then re = -1/2 vs > -1/2. -/
theorem fdCanonical_zero_implies_not_high_altitude_or_boundary_case (s : ℍ)
    (hs_fd : s ∈ (fundamentalDomainCanonical : Set ℍ)) :
    (‖(s : ℂ)‖ > 1 ∧ (s : ℂ).re > -1/2) ∨
    ‖(s : ℂ)‖ = 1 ∨
    ((s : ℂ).re = -1/2 ∧ ‖(s : ℂ)‖ > 1) := by
  obtain ⟨⟨hre_left, _⟩, hnorm⟩ := hs_fd
  simp only [UpperHalfPlane.coe_re]
  rcases eq_or_lt_of_le hnorm with h_eq | h_gt
  · exact Or.inr (Or.inl h_eq.symm)
  · rcases eq_or_lt_of_le hre_left with h_eq | h_gt'
    · exact Or.inr (Or.inr ⟨h_eq.symm, h_gt⟩)
    · exact Or.inl ⟨h_gt, h_gt'⟩

/-! ## Removed: Classification Stubs (formerly sorry-based)

The following theorems were removed because they contained `sorry` and are
unnecessary for the valence formula:

- `arc_zero_is_elliptic_canonical`: Claimed every arc zero (‖z‖ = 1) of a modular
  form in 𝒟c is i or ρ. This is FALSE as a pure-geometric statement and may be
  false even with modular form hypotheses (non-elliptic arc zeros can exist in
  S-equivalent pairs).

- `zeros_in_fdCanonical_are_classified`: Required `arc_zero_is_elliptic_canonical`.

- `zeros_in_fd_are_classified4`: 4-way classification on closed FD. Blocked by
  the `isInteriorPoint` definition (strict bounds on re and im) excluding
  high-altitude zeros, edge zeros, and arc non-elliptic zeros.

- `zeros_in_fd_are_classified`, `zeros_in_fd_are_classified_of_no_rpo`:
  Depended on `zeros_in_fd_are_classified4`.

All these are unnecessary because `valence_formula_classical_form` uses
`sum_ew_ord_decompose_unconditional`, which handles ALL boundary cases
(high-altitude, left/right edge, arc non-elliptic, right-edge/ρ+1) by
noting that `effectiveWinding = 0` for non-interior/non-elliptic points. -/

/-! ## Nonvanishing-Parameterized Variants

These variants replace `hint` (integrability) with `h_nv` (boundary nonvanishing),
giving a cleaner API that doesn't expose internal curve constants.

Integrability is derived from nonvanishing via
`intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing`. -/

/-- M7-T1: Base identity via generalizedPV residue path.

Uses `pv_equals_residue_sum_of_nonvanishing_of_ne_zero` (M6) which routes through
the generalized Cauchy PV infrastructure rather than `pv_equals_residue_sum_from_assumptions`. -/
theorem valence_formula_base_identity_of_nonvanishing_via_generalizedPV (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  have hint := intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing f h_nv
  exact contour_computation_equality f
    (pv_equals_residue_sum_of_nonvanishing_of_ne_zero f hf h_nv)
    (modular_side_mult_form f hf hint hcusp_nonvan)
    zeros hzeros hzeros_fd hzeros_complete

/-- M7-T2: Classical form via generalizedPV residue path.

Forwards to `valence_formula_base_identity_of_nonvanishing_via_generalizedPV`
+ `sum_ew_ord_decompose_unconditional`. -/
theorem valence_formula_classical_form_of_nonvanishing_via_generalizedPV (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 := by
  have h_base := valence_formula_base_identity_of_nonvanishing_via_generalizedPV f hf zeros
    hzeros hzeros_fd hzeros_complete h_nv hcusp_nonvan
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

/-- M7-T3a: Base identity parameterized by boundary nonvanishing (`h_nv`).

Now routes through the generalizedPV path. -/
theorem valence_formula_base_identity_of_nonvanishing (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) :=
  valence_formula_base_identity_of_nonvanishing_via_generalizedPV f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv hcusp_nonvan

/-- M7-T3b: Classical form parameterized by boundary nonvanishing (`h_nv`).

Now routes through the generalizedPV path. -/
theorem valence_formula_classical_form_of_nonvanishing (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 :=
  valence_formula_classical_form_of_nonvanishing_via_generalizedPV f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv hcusp_nonvan

/-! ## Crossing-Cauchy Variants

These variants take `h_pv_eq_residue` — the result of composing the crossing-Cauchy
CPV residue computation (M8's `pv_equals_residue_sum_of_crossingCauchy`) — rather
than requiring boundary nonvanishing (`h_nv`).

**Design note**: The Core level takes the *result* (`pv_integral = -(2πi Σ ew·ord)`)
rather than the internal crossing-Cauchy pieces (`h_cc`, `h_sum_bridge`, `hcpv_eq_pv`),
because `allZerosInFdBox` and `fdBox_M_half_lt` are private to `ResidueSide.lean`.
Callers compose `pv_equals_residue_sum_of_crossingCauchy` at the ResidueSide level
and pass the result here. -/

/-- M9-T1: Base identity via crossing-Cauchy residue path.

Takes the residue-side result `h_pv_eq_residue : pv_integral = -(2πi Σ ew·ord)`
(produced by `pv_equals_residue_sum_of_crossingCauchy` from M8) and equates it with
the modular side to derive the valence formula identity. -/
theorem valence_formula_base_identity_of_crossingCauchy (zeros : Finset ℍ)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  have h_mod := modular_side_mult_form f hf hint hcusp_nonvan
  have h3 : -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) =
      -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
    rw [← h_pv_eq_residue, h_mod]
  have hpi : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  exact mul_left_cancel₀ hpi (neg_inj.mp h3)

/-- M9-T2: Classical form via crossing-Cauchy residue path.

Forwards from `valence_formula_base_identity_of_crossingCauchy`
+ `sum_ew_ord_decompose_unconditional`. -/
theorem valence_formula_classical_form_of_crossingCauchy (zeros : Finset ℍ)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 := by
  have h_base := valence_formula_base_identity_of_crossingCauchy f hf zeros
    hint hcusp_nonvan h_pv_eq_residue
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

/-- M9-T3: Compatibility — under boundary nonvanishing, the crossing-Cauchy base identity
reduces to the standard `valence_formula_base_identity_of_nonvanishing`. -/
theorem valence_formula_base_identity_of_crossingCauchy_of_nonvanishing (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) :=
  valence_formula_base_identity_of_nonvanishing f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv hcusp_nonvan

/-! ## Larger-Radius Variants

These variants allow the cusp nonvanishing hypothesis to be stated on a larger
closed ball `closedBall(0, r)` with `r ≥ seg5_q_radius`. Useful when the
nonvanishing radius comes from an existential choice rather than the fixed
`seg5_q_radius`. -/

/-! ## Crossing-Cauchy-of-Integrable Variants

These compose `pv_equals_residue_sum_of_crossingCauchy_of_integrable` (from ResidueSide)
with the crossing-Cauchy core theorems. The caller provides `hint` + `h_cc` + zero data +
cusp nonvanishing; the residue identity is derived internally. -/

/-- M12-T3a: Base identity via crossing-Cauchy + integrability.

Derives the PV residue identity from `hint` + `h_cc` via
`pv_equals_residue_sum_of_crossingCauchy_of_integrable`, then forwards to
`valence_formula_base_identity_of_crossingCauchy`. -/
theorem valence_formula_base_identity_of_crossingCauchy_of_integrable (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_cc : ∀ s ∈ S_onCurve f hf zeros,
      (∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = s) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in (0:ℝ)..5,
            if ε < ‖fdBoundary t - s‖ then
              (fdBoundary t - s)⁻¹ * deriv fdBoundary t
            else 0)
          (𝓝[>] 0))) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  have h_pv := pv_equals_residue_sum_of_crossingCauchy_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint h_cc
  exact valence_formula_base_identity_of_crossingCauchy f hf zeros hint hcusp_nonvan h_pv

/-- M12-T3b: Classical form via crossing-Cauchy + integrability.

Forwards from `valence_formula_base_identity_of_crossingCauchy_of_integrable`
+ `sum_ew_ord_decompose_unconditional`. -/
theorem valence_formula_classical_form_of_crossingCauchy_of_integrable (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_cc : ∀ s ∈ S_onCurve f hf zeros,
      (∃ t ∈ Icc (0:ℝ) 5, fdBoundary t = s) →
        Cauchy (Filter.map (fun ε =>
          ∫ t in (0:ℝ)..5,
            if ε < ‖fdBoundary t - s‖ then
              (fdBoundary t - s)⁻¹ * deriv fdBoundary t
            else 0)
          (𝓝[>] 0))) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 := by
  have h_base := valence_formula_base_identity_of_crossingCauchy_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan h_cc
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

/-! ## Crossing-Cauchy-Auto Variants (No h_cc)

These compose `pv_equals_residue_sum_of_crossingCauchy_auto_of_integrable` (from ResidueSide)
with the crossing-Cauchy core theorems. The caller provides `hint` + zero data +
cusp nonvanishing; no `h_cc` is needed. When `hint` holds, the boundary avoids all
zeros, so the crossing-Cauchy condition is vacuously satisfied. -/

/-- M15-T2a: Base identity via integrability — no `h_cc` needed.

Derives the PV residue identity from `hint` via
`pv_equals_residue_sum_of_crossingCauchy_auto_of_integrable`, then forwards to
`valence_formula_base_identity_of_crossingCauchy`. -/
theorem valence_formula_base_identity_of_crossingCauchy_auto_of_integrable (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  have h_pv := pv_equals_residue_sum_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint
  exact valence_formula_base_identity_of_crossingCauchy f hf zeros hint hcusp_nonvan h_pv

/-- M15-T2b: Classical form via integrability — no `h_cc` needed.

Forwards from `valence_formula_base_identity_of_crossingCauchy_auto_of_integrable`
+ `sum_ew_ord_decompose_unconditional`. -/
theorem valence_formula_classical_form_of_crossingCauchy_auto_of_integrable (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 := by
  have h_base := valence_formula_base_identity_of_crossingCauchy_auto_of_integrable f hf zeros
    hzeros hzeros_fd hzeros_complete hint hcusp_nonvan
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

/-! ## Larger-Radius Variants

These variants allow the cusp nonvanishing hypothesis to be stated on a larger
closed ball `closedBall(0, r)` with `r ≥ seg5_q_radius`. Useful when the
nonvanishing radius comes from an existential choice rather than the fixed
`seg5_q_radius`. -/

theorem valence_formula_base_identity_of_larger_radius (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 - (orderAtCusp' f : ℂ) :=
  valence_formula_base_identity f hf zeros hzeros hzeros_fd hzeros_complete hint
    (fun q hq hq_ne => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq_ne)

theorem valence_formula_classical_form_of_larger_radius (zeros : Finset ℍ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℂ) +
      (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
      (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℂ) =
      (k : ℂ) / 12 :=
  valence_formula_classical_form f hf zeros hzeros hzeros_fd hzeros_complete hint
    (fun q hq hq_ne => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq_ne)

/-! ## Auto-Cusp Variants (No `hcusp_nonvan`)

These variants use `modular_side_auto_cusp_of_integrable` to derive cusp nonvanishing
from `hf : f ≠ 0`, eliminating the `hcusp_nonvan` parameter entirely.

The result is existential: `∃ H₀ > √3/2`, for any `H ≥ H₀`, given integrability and
the residue-side result at height H, the valence formula identity holds.

Unlike the fixed-boundary variants above, these operate on the parameterized boundary
curve `fdBoundary_H H`, not the fixed `fdBoundary`. The conclusion (the algebraic
identity `Σ ew·ord = k/12 - ord_∞`) is curve-independent. -/

/-- Base identity via auto-cusp: no `hcusp_nonvan` needed.

From `hf : f ≠ 0`, cusp nonvanishing holds for sufficiently large height H.
The caller provides the residue-side result `h_pv_eq_residue` and integrability
`hint_H`, both at height H. The modular side is derived automatically. -/
theorem valence_formula_base_identity_auto_cusp (zeros : Finset ℍ) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
          (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
          (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := modular_side_auto_cusp_of_integrable f hf
  refine ⟨H₀, hH₀_gt, fun {H} hH hint_H h_pv_eq_residue => ?_⟩
  have h_mod := h_auto hH hint_H
  have h3 : -(2 * Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) =
      -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
    rw [← h_pv_eq_residue, h_mod]
  have hpi : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  exact mul_left_cancel₀ hpi (neg_inj.mp h3)

/-- Classical form via auto-cusp: no `hcusp_nonvan` needed.

Forwards from `valence_formula_base_identity_auto_cusp`
+ `sum_ew_ord_decompose_unconditional`. -/
theorem valence_formula_classical_form_auto_cusp (zeros : Finset ℍ) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
          (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℂ) +
          (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
          (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
          ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℂ) =
          (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := valence_formula_base_identity_auto_cusp f hf zeros
  refine ⟨H₀, hH₀_gt, fun {H} hH hint_H h_pv_eq_residue => ?_⟩
  have h_base := h_auto hH hint_H h_pv_eq_residue
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

end
