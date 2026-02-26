/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ResidueSide
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ModularSide
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_ModularSide_Param
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_CPV_ModularSide
import Mathlib.Analysis.Meromorphic.NormalForm

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

/-! ## Auto-Cusp Generalized PV Variants (via CPV modular side)

These variants use `modular_side_auto_cusp_generalizedPV` from `ValenceFormula_CPV_ModularSide`,
which replaces `IntervalIntegrable` with local nonvanishing hypotheses (`h_arc_nv`, `h_vert_nv`).
The PV integral uses `pv_integral_logDeriv` with `fdBoundaryArcSingularSet` instead of
`pv_integral`. -/

/-- Base identity via auto-cusp with generalized PV: no `hcusp_nonvan` or `IntervalIntegrable`.

Takes arc nonvanishing `h_arc_nv` (H-independent) as an explicit hypothesis.
For `H ≥ H₀`, given vertical nonvanishing and the CPV residue-side equality, derives
the algebraic identity. -/
theorem valence_formula_base_identity_auto_cusp_generalizedPV (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
          (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := modular_side_auto_cusp_generalizedPV f hf h_arc_nv
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv h_cpv_eq_residue => ?_⟩
  have h_mod := h_auto hH h_vert_nv
  have h3 : -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
    rw [← h_cpv_eq_residue, h_mod]
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  exact mul_left_cancel₀ hpi (neg_inj.mp h3)

/-- Classical form via auto-cusp with generalized PV: no `hcusp_nonvan` or `IntervalIntegrable`.

Forwards from `valence_formula_base_identity_auto_cusp_generalizedPV`
+ `sum_ew_ord_decompose_unconditional`. -/
theorem valence_formula_classical_form_auto_cusp_generalizedPV (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℂ) +
          (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
          (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
          ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℂ) =
          (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_cusp_generalizedPV f hf zeros h_arc_nv
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv h_cpv_eq_residue => ?_⟩
  have h_base := h_auto hH h_vert_nv h_cpv_eq_residue
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

/-! ## Auto-Cusp Generalized PV + Residue-Auto Variants

These compose the modular-side existential with a residue-auto provider, removing
`h_cpv_eq_residue` from the per-height API entirely. The caller only needs to supply
`h_vert_nv` (vertical nonvanishing) at each height. -/

/-- Base identity with residue-auto provider: no `h_cpv_eq_residue` at each height.

Combines the modular-side `∃ H₀_mod` from `modular_side_auto_cusp_generalizedPV` with the
residue-auto provider `∃ H₁` at `H₀ := max H₀_mod H₁`. For `H ≥ H₀`, both the modular
side and residue side hold simultaneously, yielding the algebraic identity. -/
theorem valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
          (k : ℂ) / 12 - (orderAtCusp' f : ℂ) := by
  obtain ⟨H₀_mod, hH₀_mod_gt, h_mod⟩ := modular_side_auto_cusp_generalizedPV f hf h_arc_nv
  obtain ⟨H₁, hH₁_gt, h_res⟩ := h_residue_auto
  refine ⟨max H₀_mod H₁, lt_of_lt_of_le hH₀_mod_gt (le_max_left _ _),
    fun {H} hH h_vert_nv => ?_⟩
  have h_modular := h_mod (le_trans (le_max_left _ _) hH) h_vert_nv
  have h_residue := h_res (le_trans (le_max_right _ _) hH) h_vert_nv
  have h3 : -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
    rw [← h_residue, h_modular]
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  exact mul_left_cancel₀ hpi (neg_inj.mp h3)

/-- Classical form with residue-auto provider: no `h_cpv_eq_residue` at each height.

Forwards from `valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto`
+ `sum_ew_ord_decompose_unconditional`. -/
theorem valence_formula_classical_form_auto_cusp_generalizedPV_of_residue_auto
    (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℂ) +
          (1/2 : ℂ) * (if ellipticPoint_i' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_i' : ℂ) else 0) +
          (1/3 : ℂ) * (if ellipticPoint_rho' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℂ) else 0) +
          ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℂ) =
          (k : ℂ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto f hf zeros
      h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  have h_base := h_auto hH h_vert_nv
  rw [sum_ew_ord_decompose_unconditional f zeros] at h_base
  linear_combination h_base

/-! ## F7-B Assembly: Generalized Winding Number Valence Formula via CPV

These definitions and theorems produce a valence formula identity using
generalized winding numbers (gWN) and Cauchy principal value integrals.

The modular side is derived internally from `modular_side_auto_cusp_generalizedPV_of_SarcSvert`
using derived singular sets `S_arc_of_S S` and `S_vert_of_S S`.
The residue side is taken as a provider hypothesis, parametrized by the derived singular sets.

### Key Definitions

* `S_arc_of_S S` — Arc singular set derived from S (unit circle zeros + S-transforms + ρ, ρ+1)
* `S_vert_of_S S` — Vertical singular set derived from S (re=±1/2 zeros + T-shifts)
* `OnCurvePVProvider f S` — Type alias for what Worker A needs to provide (PV existence)

### Main Results

* `valence_formula_gWN_cpv_from_S` — Assembly theorem: `∃ H₀, ∀ H ≥ H₀, Σ gWN·ord = -(k/12 - ord_∞)`
-/

/-! ### Derived Singular Sets from S -/

omit f hf in
/-- Arc singular set derived from S: points in S on the unit circle (and their
S-transforms `z ↦ -1/z`), plus the elliptic points ρ and ρ+1.

All elements have norm 1 and the set is closed under `z ↦ -1/z`. -/
noncomputable def S_arc_of_S (S : Finset ℍ) : Finset ℂ :=
  (S.filter (fun (p : ℍ) => ‖(↑p : ℂ)‖ = 1)).image (↑· : ℍ → ℂ) ∪
  (S.filter (fun (p : ℍ) => ‖(↑p : ℂ)‖ = 1)).image (fun (p : ℍ) => -(1:ℂ) / (↑p : ℂ)) ∪
  {ellipticPoint_rho, ellipticPoint_rho_plus_one}

omit f hf in
/-- Vertical singular set derived from S: points in S on re=±1/2 with ‖z‖>1,
plus their T-shifted pairs (z ↦ z±1). -/
noncomputable def S_vert_of_S (S : Finset ℍ) : Finset ℂ :=
  (S.filter (fun (p : ℍ) => (↑p : ℂ).re = 1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image (↑· : ℍ → ℂ) ∪
  (S.filter (fun (p : ℍ) => (↑p : ℂ).re = 1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image (fun (p : ℍ) => (↑p : ℂ) - 1) ∪
  (S.filter (fun (p : ℍ) => (↑p : ℂ).re = -1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image (↑· : ℍ → ℂ) ∪
  (S.filter (fun (p : ℍ) => (↑p : ℂ).re = -1/2 ∧ ‖(↑p : ℂ)‖ > 1)).image (fun (p : ℍ) => (↑p : ℂ) + 1)

/-- What Worker A needs to provide: PV existence at on-curve singular points. -/
def OnCurvePVProvider (f : ModularForm (Gamma 1) k) (S : Finset ℍ) : Prop :=
  ∀ (H : ℝ), Real.sqrt 3 / 2 < H →
    ∀ s ∈ S_arc_of_S S ∪ S_vert_of_S S,
      (∃ t ∈ Set.Icc (0:ℝ) 5, fdBoundary_H H t = s) →
      CauchyPrincipalValueExists'
        (fun z => (z - s)⁻¹) (fdBoundary_H H) 0 5 s

/-! ### Properties of S_arc_of_S -/

omit f hf in
lemma S_arc_of_S_rho_in (S : Finset ℍ) :
    (ellipticPoint_rho : ℂ) ∈ S_arc_of_S S := by
  simp [S_arc_of_S]

omit f hf in
lemma S_arc_of_S_rho_plus_one_in (S : Finset ℍ) :
    (ellipticPoint_rho_plus_one : ℂ) ∈ S_arc_of_S S := by
  simp [S_arc_of_S]

omit f hf in
private lemma norm_ellipticPoint_rho_eq_one : ‖(ellipticPoint_rho : ℂ)‖ = 1 := by
  have hre : (ellipticPoint_rho : ℂ).re = -1/2 := by simp [ellipticPoint_rho, ellipticPoint_rho']
  have him : (ellipticPoint_rho : ℂ).im = Real.sqrt 3 / 2 := by simp [ellipticPoint_rho, ellipticPoint_rho']
  rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him, div_pow, div_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

omit f hf in
private lemma norm_ellipticPoint_rho_plus_one_eq_one : ‖(ellipticPoint_rho_plus_one : ℂ)‖ = 1 := by
  have hre : (ellipticPoint_rho_plus_one : ℂ).re = 1/2 := by
    simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  have him : (ellipticPoint_rho_plus_one : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him, div_pow, div_pow,
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
  norm_num

omit f hf in
lemma S_arc_of_S_unit (S : Finset ℍ) (_hS : ∀ p ∈ S, p ∈ 𝒟') :
    ∀ s ∈ S_arc_of_S S, ‖s‖ = 1 := by
  intro s hs
  simp only [S_arc_of_S, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with ⟨⟨p, ⟨_, hp_norm⟩, rfl⟩ | ⟨p, ⟨_, hp_norm⟩, rfl⟩⟩ | hs
  · exact hp_norm
  · rw [norm_div, norm_neg, norm_one, hp_norm, div_one]
  · rcases hs with rfl | rfl
    · exact norm_ellipticPoint_rho_eq_one
    · exact norm_ellipticPoint_rho_plus_one_eq_one

omit f hf in
private lemma neg_inv_rho_eq_rho_plus_one :
    -(1:ℂ) / (ellipticPoint_rho : ℂ) = (ellipticPoint_rho_plus_one : ℂ) := by
  have hre : (ellipticPoint_rho : ℂ).re = -1/2 := by simp [ellipticPoint_rho, ellipticPoint_rho']
  have him : (ellipticPoint_rho : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPoint_rho, ellipticPoint_rho']
  have hre2 : (ellipticPoint_rho_plus_one : ℂ).re = 1/2 := by
    simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  have him2 : (ellipticPoint_rho_plus_one : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  have hnormSq : -(1/2 : ℝ) * -(1/2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  apply Complex.ext
  · simp only [neg_div, Complex.neg_re, Complex.div_re, Complex.one_re, Complex.one_im,
      Complex.normSq_apply, hre, him, hre2, hnormSq]; ring
  · simp only [neg_div, Complex.neg_im, Complex.div_im, Complex.one_re, Complex.one_im,
      Complex.normSq_apply, hre, him, him2, hnormSq]; ring

omit f hf in
private lemma neg_inv_rho_plus_one_eq_rho :
    -(1:ℂ) / (ellipticPoint_rho_plus_one : ℂ) = (ellipticPoint_rho : ℂ) := by
  have hre : (ellipticPoint_rho_plus_one : ℂ).re = 1/2 := by
    simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  have him : (ellipticPoint_rho_plus_one : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
  have hre2 : (ellipticPoint_rho : ℂ).re = -1/2 := by simp [ellipticPoint_rho, ellipticPoint_rho']
  have him2 : (ellipticPoint_rho : ℂ).im = Real.sqrt 3 / 2 := by
    simp [ellipticPoint_rho, ellipticPoint_rho']
  have hnormSq : (1/2 : ℝ) * (1/2) + Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 1 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  apply Complex.ext
  · simp only [neg_div, Complex.neg_re, Complex.div_re, Complex.one_re, Complex.one_im,
      Complex.normSq_apply, hre, him, hre2, hnormSq]; ring
  · simp only [neg_div, Complex.neg_im, Complex.div_im, Complex.one_re, Complex.one_im,
      Complex.normSq_apply, hre, him, him2, hnormSq]; ring

omit f hf in
lemma S_arc_of_S_closed (S : Finset ℍ) (_hS : ∀ p ∈ S, p ∈ 𝒟') :
    ∀ s ∈ S_arc_of_S S, -(1:ℂ) / s ∈ S_arc_of_S S := by
  intro s hs
  simp only [S_arc_of_S, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs ⊢
  rcases hs with ⟨⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩⟩ | hs
  · -- s = ↑p with ‖↑p‖ = 1: then -1/↑p is in second component
    left; right; exact ⟨p, hp, rfl⟩
  · -- s = -1/↑p with ‖↑p‖ = 1: then -1/(-1/↑p) = ↑p is in first component
    have hp_ne : (↑p : ℂ) ≠ 0 := by
      intro h; have := hp.2; rw [h, norm_zero] at this; norm_num at this
    left; left
    refine ⟨p, hp, ?_⟩
    field_simp
  · rcases hs with rfl | rfl
    · -- s = ρ: -1/ρ = ρ+1
      right; right
      exact neg_inv_rho_eq_rho_plus_one
    · -- s = ρ+1: -1/(ρ+1) = ρ
      right; left
      exact neg_inv_rho_plus_one_eq_rho

omit f hf in
lemma S_arc_of_S_im_pos (S : Finset ℍ) :
    ∀ s ∈ S_arc_of_S S, 0 < s.im := by
  intro s hs
  simp only [S_arc_of_S, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with ⟨⟨p, _, rfl⟩ | ⟨p, ⟨_, hp_norm⟩, rfl⟩⟩ | hs
  · exact p.2
  · -- -1/↑p: im > 0 when ‖↑p‖ = 1 and im(↑p) > 0
    have hp_ne : (↑p : ℂ) ≠ 0 := by
      intro h; rw [h, norm_zero] at hp_norm; norm_num at hp_norm
    rw [show -(1:ℂ) / (↑p : ℂ) = -((↑p : ℂ))⁻¹ from by ring]
    rw [Complex.neg_im, neg_pos, Complex.inv_im]
    have hsq : Complex.normSq (↑p : ℂ) > 0 := Complex.normSq_pos.mpr hp_ne
    rw [neg_div]
    linarith [div_pos (show 0 < (↑p : ℂ).im from p.2) hsq]
  · rcases hs with rfl | rfl
    · have : (ellipticPoint_rho : ℂ).im = Real.sqrt 3 / 2 := by
        simp [ellipticPoint_rho, ellipticPoint_rho']
      rw [this]; positivity
    · have : (ellipticPoint_rho_plus_one : ℂ).im = Real.sqrt 3 / 2 := by
        simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
      rw [this]; positivity

/-! ### Properties of S_vert_of_S -/

omit f hf in
lemma S_vert_of_S_re (S : Finset ℍ) :
    ∀ s ∈ S_vert_of_S S, s.re = 1/2 ∨ s.re = -1/2 := by
  intro s hs
  unfold S_vert_of_S at hs
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · rcases Finset.mem_image.mp hA with ⟨p, hp_filter, rfl⟩
        obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
        left; exact hp_re
      · rcases Finset.mem_image.mp hB with ⟨p, hp_filter, rfl⟩
        obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
        right; simp only [Complex.sub_re, hp_re]; norm_num
    · rcases Finset.mem_image.mp hC with ⟨p, hp_filter, rfl⟩
      obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
      right; exact hp_re
  · rcases Finset.mem_image.mp hD with ⟨p, hp_filter, rfl⟩
    obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
    left; simp only [Complex.add_re, hp_re]; norm_num

omit f hf in
lemma S_vert_of_S_pair_left (S : Finset ℍ) :
    ∀ s ∈ S_vert_of_S S, s.re = 1/2 → s - 1 ∈ S_vert_of_S S := by
  intro s hs hre
  unfold S_vert_of_S at hs ⊢
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · -- s ∈ A (image ↑·, re=1/2 filter): s-1 ∈ B
        rcases Finset.mem_image.mp hA with ⟨p, hp_filter, rfl⟩
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; right
        exact Finset.mem_image.mpr ⟨p, hp_filter, rfl⟩
      · -- s ∈ B (image (↑·-1), re=1/2 filter): s.re = (↑p).re - 1 = -1/2, contradicts hre
        rcases Finset.mem_image.mp hB with ⟨p, hp_filter, rfl⟩
        exfalso
        obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.I_re] at hre
        rw [hp_re] at hre
        norm_num at hre
    · -- s ∈ C (image ↑·, re=-1/2 filter): s.re = -1/2, contradicts hre
      rcases Finset.mem_image.mp hC with ⟨p, hp_filter, rfl⟩
      exfalso
      obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
      linarith
  · -- s ∈ D (image (↑·+1), re=-1/2 filter): s-1 = ↑p ∈ C
    rcases Finset.mem_image.mp hD with ⟨p, hp_filter, rfl⟩
    have : (↑p : ℂ) + 1 - 1 = (↑p : ℂ) := by ring
    rw [this]
    apply Finset.mem_union.mpr; left
    apply Finset.mem_union.mpr; right
    exact Finset.mem_image.mpr ⟨p, hp_filter, rfl⟩

omit f hf in
lemma S_vert_of_S_pair_right (S : Finset ℍ) :
    ∀ s ∈ S_vert_of_S S, s.re = -1/2 → s + 1 ∈ S_vert_of_S S := by
  intro s hs hre
  unfold S_vert_of_S at hs ⊢
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · -- s ∈ A (image ↑·, re=1/2 filter): s.re = 1/2, contradicts hre
        rcases Finset.mem_image.mp hA with ⟨p, hp_filter, rfl⟩
        exfalso
        obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
        linarith
      · -- s ∈ B (image (↑·-1), re=1/2 filter): s.re = -1/2 ✓, s+1 = ↑p ∈ A
        rcases Finset.mem_image.mp hB with ⟨p, hp_filter, rfl⟩
        have : (↑p : ℂ) - 1 + 1 = (↑p : ℂ) := by ring
        rw [this]
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left
        apply Finset.mem_union.mpr; left
        exact Finset.mem_image.mpr ⟨p, hp_filter, rfl⟩
    · -- s ∈ C (image ↑·, re=-1/2 filter): s+1 ∈ D
      rcases Finset.mem_image.mp hC with ⟨p, hp_filter, rfl⟩
      apply Finset.mem_union.mpr; right
      exact Finset.mem_image.mpr ⟨p, hp_filter, rfl⟩
  · -- s ∈ D (image (↑·+1), re=-1/2 filter): s.re = 1/2, contradicts hre
    rcases Finset.mem_image.mp hD with ⟨p, hp_filter, rfl⟩
    exfalso
    obtain ⟨_, hp_re, _⟩ := Finset.mem_filter.mp hp_filter
    simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re] at hre
    rw [hp_re] at hre
    norm_num at hre

omit f hf in
lemma S_vert_of_S_im_pos (S : Finset ℍ) :
    ∀ s ∈ S_vert_of_S S, 0 < s.im := by
  intro s hs
  unfold S_vert_of_S at hs
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · -- A: image ↑· from re=1/2 filter (p : ℍ)
        rcases Finset.mem_image.mp hA with ⟨p, _, rfl⟩; exact p.2
      · -- B: image (·-1) from re=1/2 filter (p : ℍ)
        rcases Finset.mem_image.mp hB with ⟨p, hp_filter, rfl⟩
        obtain ⟨_hp_in_S, _hp_re, _hp_norm⟩ := Finset.mem_filter.mp hp_filter
        show 0 < ((↑p : ℂ) - 1).im
        simp only [Complex.sub_im, Complex.one_im, sub_zero]
        exact p.2
    · -- C: image ↑· from re=-1/2 filter (p : ℍ)
      rcases Finset.mem_image.mp hC with ⟨p, _, rfl⟩; exact p.2
  · -- D: image (·+1) from re=-1/2 filter (p : ℍ)
    rcases Finset.mem_image.mp hD with ⟨p, hp_filter, rfl⟩
    obtain ⟨_hp_in_S, _hp_re, _hp_norm⟩ := Finset.mem_filter.mp hp_filter
    show 0 < ((↑p : ℂ) + 1).im
    simp only [Complex.add_im, Complex.one_im, add_zero]
    exact p.2

/-! ### Assembly: Generalized Winding Number Valence Formula via CPV -/

include hf in
/-- **Generalized Winding Number Valence Formula via CPV** (no h_arc_nv, no h_vert_nv).

Composes the modular side (via `modular_side_auto_cusp_generalizedPV_of_SarcSvert`)
with a residue-side provider to get the valence formula with generalized winding numbers.

The residue provider states that for large H, the CPV integral of `f'/f` along
`fdBoundary_H H` over the singular set `S_arc_of_S S ∪ S_vert_of_S S` equals
`2πi · Σ gWN(p) · ord_p(f)`.

**Hypotheses**:
- `S, hS, hS_complete`: standard zero superset in 𝒟'
- `h_oncurve_arc, h_oncurve_vert`: on-curve zero capture into S_arc/S_vert
- `h_residue_provider`: the residue side equality (from Worker A)

**Conclusion**: `∃ H₀ > √3/2, ∀ H ≥ H₀, Σ gWN · ord = -(k/12 - ord_∞)` -/
theorem valence_formula_gWN_cpv_from_S
    (S : Finset ℍ)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    -- On-curve capture (derived from hS_complete + geometry; see oncurve_arc/vert lemmas)
    (h_oncurve_arc : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H 1 t) = 0 →
        fdBoundary_H 1 t ∈ (↑(S_arc_of_S S) : Set ℂ))
    (h_oncurve_vert : ∀ (H' : ℝ), Real.sqrt 3 / 2 < H' → ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
        (fdBoundary_H H' t : ℂ) ∈ (↑(S_vert_of_S S) : Set ℂ))
    -- Residue side provider
    (h_residue_provider : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc_of_S S ∪ S_vert_of_S S) =
          2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
              (orderOfVanishingAt' f s : ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S.filter (fun p => f p = 0),
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  -- Modular side: obtain ∃ H₀_mod, pv_integral = -(2πi · (k/12 - ord_∞))
  obtain ⟨H₀_mod, hH₀_mod_gt, h_mod⟩ :=
    modular_side_auto_cusp_generalizedPV_of_SarcSvert f hf
      (S_arc_of_S S) (S_vert_of_S S)
      (S_arc_of_S_unit S hS) (S_arc_of_S_closed S hS) (S_arc_of_S_rho_in S)
      (S_vert_of_S_re S) (S_vert_of_S_pair_left S) (S_vert_of_S_pair_right S)
      h_oncurve_arc h_oncurve_vert
  -- Residue side: obtain ∃ H₁, pv_integral = 2πi · Σ gWN · ord
  obtain ⟨H₁, hH₁_gt, h_res⟩ := h_residue_provider
  -- Compose at H ≥ max(H₀_mod, H₁)
  refine ⟨max H₀_mod H₁, lt_of_lt_of_le hH₀_mod_gt (le_max_left _ _),
    fun {H} hH => ?_⟩
  have h_modular := h_mod (le_trans (le_max_left _ _) hH)
  have h_residue := h_res (le_trans (le_max_right _ _) hH)
  -- Equate: 2πi · Σ gWN · ord = -(2πi · (k/12 - ord_∞))
  have h3 : 2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
        generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
          (orderOfVanishingAt' f s : ℂ) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
    rw [← h_residue, h_modular]
  -- Cancel 2πi: Σ = -(k/12 - ord_∞)
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, ofReal_eq_zero,
      Real.pi_ne_zero, I_ne_zero, or_self]
  rw [show -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) =
    2 * ↑Real.pi * I * (-((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) from by ring] at h3
  exact mul_left_cancel₀ hpi h3

/-! ### B1-B3: Auto On-Curve Capture + Wrapper Theorems

These lemmas automatically derive `h_oncurve_arc` and `h_oncurve_vert` from
`S, hS, hS_complete`, so the caller only needs to supply `h_residue_provider`. -/

/-! #### Private Helpers (copies of private lemmas from other files) -/

omit hf in
private lemma G_analyticAt_core (p : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) := by
  have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with w hw
  have h_eq : ∀ᶠ u in 𝓝 w, (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) u =
      (f ∘ UpperHalfPlane.ofComplex) u := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    simp only [Function.comp_apply, dif_pos hu, UpperHalfPlane.ofComplex_apply_of_im_pos hu]
  exact ((h_diffOn w hw).differentiableAt
    (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq

omit hf in
private lemma G_eq_f_core (p : ℍ) :
    (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p := by
  have him : 0 < (↑p : ℂ).im := p.im_pos
  simp only [him, ↓reduceDIte]; congr 1

private lemma orderOfVanishingAt'_ne_zero_of_eq_zero_core (p : ℍ) (hp : f p = 0) :
    orderOfVanishingAt' (⇑f) p ≠ 0 := by
  unfold orderOfVanishingAt'
  intro h_untop_eq
  have him : 0 < (↑p : ℂ).im := p.im_pos
  have h_anal : AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0)
      (p : ℂ) := G_analyticAt_core f p
  have h_nf : MeromorphicNFAt (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0)
      (p : ℂ) := AnalyticAt.meromorphicNFAt h_anal
  have h_ord_ne : meromorphicOrderAt
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑p) ≠ (0 : WithTop ℤ) := by
    intro h0; apply h_nf.meromorphicOrderAt_eq_zero_iff.mp h0
    simp only [him, ↓reduceDIte]; exact_mod_cast hp
  have h_top : meromorphicOrderAt
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑p) = ⊤ :=
    (WithTop.untop₀_eq_zero.mp h_untop_eq).resolve_left h_ord_ne
  rw [meromorphicOrderAt_eq_top_iff] at h_top
  have h_analOn : AnalyticOnNhd ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0)
      {w | 0 < w.im} := fun w hw => G_analyticAt_core f ⟨w, hw⟩
  have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} :=
    ((convex_halfSpace_im_gt 0).isConnected
      ⟨Complex.I, by simp [Complex.I_im]⟩).isPreconnected
  have h_zero_on := h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    h_preconn p.im_pos h_top.frequently
  apply hf; ext z
  have hG_eq : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑z) = f z :=
    G_eq_f_core f z
  simp only [ModularForm.coe_zero, Pi.zero_apply, ← hG_eq, h_zero_on z.im_pos]

omit f hf in
private lemma fdBoundary_H_im_ge_sqrt3_div_2_core {H : ℝ} (hH : Real.sqrt 3 / 2 ≤ H)
    (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) :
    (fdBoundary_H H t).im ≥ Real.sqrt 3 / 2 := by
  by_cases h1 : t ≤ 1
  · rw [fdBoundary_H_eq_seg1_H h1]
    have him : (fdBoundary_seg1_H H t).im = H - t * (H - Real.sqrt 3 / 2) := by
      simp [fdBoundary_seg1_H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
    rw [him]; nlinarith [ht.1]
  · push_neg at h1; by_cases h3 : t ≤ 3
    · -- For 1 < t ≤ 3, fdBoundary_H H t = fdBoundary t (arc segment)
      have h_eq : fdBoundary_H H t = fdBoundary t := by
        unfold fdBoundary_H fdBoundary
        simp only [show ¬(t ≤ 1) from by linarith, ↓reduceIte, h3]
      rw [h_eq]
      -- fdBoundary t on (1,3] is exp(θ*I), im = sin(θ) ≥ √3/2
      simp only [fdBoundary, show ¬(t ≤ 1) from by linarith, ↓reduceIte]
      split_ifs with h2
      · -- t ≤ 2: seg2, angle θ in [π/3, π/2]
        show (fdBoundary_seg2 t).im ≥ Real.sqrt 3 / 2
        unfold fdBoundary_seg2
        rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
            ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
        rw [Complex.exp_ofReal_mul_I_im]
        set θ := Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) with hθ_def
        have hθ_lo : Real.pi / 3 ≤ θ := by rw [hθ_def]; nlinarith [Real.pi_pos]
        have hθ_hi : θ ≤ Real.pi / 2 := by rw [hθ_def]; nlinarith
        linarith [Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) hθ_hi hθ_lo, Real.sin_pi_div_three]
      · -- t > 2: seg3, angle θ in [π/2, 2π/3], sin θ = sin(π-θ) ≥ sin(π/3)
        show (fdBoundary_seg3 t).im ≥ Real.sqrt 3 / 2
        unfold fdBoundary_seg3
        rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
            ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
        rw [Complex.exp_ofReal_mul_I_im]
        set θ := Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) with hθ_def
        have hθ_lo : Real.pi / 2 ≤ θ := by rw [hθ_def]; nlinarith [Real.pi_pos]
        have hθ_hi : θ ≤ 2 * Real.pi / 3 := by rw [hθ_def]; nlinarith
        have h_pi_sub_lo : Real.pi / 3 ≤ Real.pi - θ := by nlinarith
        have h_pi_sub_hi : Real.pi - θ ≤ Real.pi / 2 := by nlinarith
        rw [show Real.sin θ = Real.sin (Real.pi - θ) from (Real.sin_pi_sub θ).symm]
        linarith [Real.sin_le_sin_of_le_of_le_pi_div_two
          (by nlinarith [Real.pi_pos]) h_pi_sub_hi h_pi_sub_lo, Real.sin_pi_div_three]
    · push_neg at h3; by_cases h4 : t ≤ 4
      · rw [fdBoundary_H_eq_seg4_H (by linarith) (by linarith) (by linarith) h4]
        have him : (fdBoundary_seg4_H H t).im = Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2) := by
          simp [fdBoundary_seg4_H, add_im, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
        rw [him]; nlinarith
      · push_neg at h4
        rw [fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)]
        have him : (fdBoundary_seg5_H H t).im = H := by
          simp [fdBoundary_seg5_H, add_im, sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
        rw [him]; linarith

/-! #### B1: Arc Capture -/

/-- If `f` vanishes at an arc point `fdBoundary_H H t` with `‖·‖ = 1` and `t ∈ [0,5]`,
then that point is in `S_arc_of_S S`. -/
private lemma oncurve_arc_capture_auto
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 5)
    (h_norm : ‖fdBoundary_H H t‖ = 1)
    (h_zero : modularFormCompOfComplex f (fdBoundary_H H t) = 0) :
    fdBoundary_H H t ∈ (↑(S_arc_of_S S) : Set ℂ) := by
  set z := fdBoundary_H H t with hz_def
  -- Step 1: im ≥ √3/2 > 0
  have h_im_ge := fdBoundary_H_im_ge_sqrt3_div_2_core hH.le t ht
  have h_im_pos : 0 < z.im := by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
  -- Step 2: from ‖z‖ = 1 and im ≥ √3/2, deduce |re| ≤ 1/2
  have h_normSq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [h_norm] at this; linarith
  have h_re_sq : z.re ^ 2 = 1 - z.im ^ 2 := by linarith
  have h_im_sq_ge : z.im ^ 2 ≥ 3/4 := by
    have hsqrt : Real.sqrt 3 / 2 ≤ z.im := h_im_ge
    have h_sq : (Real.sqrt 3 / 2) ^ 2 = 3/4 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
    have := mul_self_le_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) hsqrt
    nlinarith
  have h_re_sq_le : z.re ^ 2 ≤ 1/4 := by linarith
  have h_abs_re : |z.re| ≤ 1/2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg (z.re + 1/2), sq_nonneg (z.re - 1/2)]
  -- Step 3: construct ℍ point
  let p : ℍ := ⟨z, h_im_pos⟩
  -- Step 4: p ∈ 𝒟'
  have hp_fd : p ∈ 𝒟' := by
    refine ⟨?_, ?_⟩
    · show |z.re| ≤ 1/2; exact h_abs_re
    · show ‖z‖ ≥ 1; rw [h_norm]
  -- Step 5: f p = 0
  have hp_zero : f p = 0 := by
    have := h_zero
    simp only [modularFormCompOfComplex, Function.comp_apply] at this
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at this
  -- Step 6: ord ≠ 0 → p ∈ S
  have h_ord := orderOfVanishingAt'_ne_zero_of_eq_zero_core f hf p hp_zero
  have hp_in_S := hS_complete p hp_fd h_ord
  -- Step 7: ↑p ∈ S_arc_of_S S (first image component)
  show z ∈ (↑(S_arc_of_S S) : Set ℂ)
  simp only [S_arc_of_S, Finset.coe_union, Finset.coe_image, Finset.coe_insert,
    Finset.coe_singleton, Set.mem_union, Set.mem_image]
  left; left
  exact ⟨p, Finset.mem_filter.mpr ⟨hp_in_S, show ‖z‖ = 1 from h_norm⟩, rfl⟩

/-! #### B2: Vert Capture -/

/-- If `f` vanishes at a seg1 point `fdBoundary_H H' t` with `t ∈ (0,1)` and `H' > √3/2`,
then that point is in `S_vert_of_S S`. -/
private lemma oncurve_vert_capture_auto
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H' : ℝ} (hH' : Real.sqrt 3 / 2 < H') {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1)
    (h_zero : modularFormCompOfComplex f (fdBoundary_H H' t) = 0) :
    (fdBoundary_H H' t : ℂ) ∈ (↑(S_vert_of_S S) : Set ℂ) := by
  set z := fdBoundary_H H' t with hz_def
  -- For t ∈ (0,1), fdBoundary_H H' t = fdBoundary_seg1_H H' t
  have ht_le : t ≤ 1 := le_of_lt ht.2
  have hz_seg : z = fdBoundary_seg1_H H' t := by rw [hz_def, fdBoundary_H_eq_seg1_H ht_le]
  -- Re = 1/2
  have h_re : z.re = 1/2 := by
    rw [hz_seg]; simp [fdBoundary_seg1_H, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  -- Im = H' - t(H' - √3/2) > √3/2 (since t < 1)
  have h_im_val : z.im = H' - t * (H' - Real.sqrt 3 / 2) := by
    rw [hz_seg]; simp [fdBoundary_seg1_H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
  have h_im_gt : z.im > Real.sqrt 3 / 2 := by
    rw [h_im_val]; nlinarith [ht.2]
  have h_im_pos : 0 < z.im := by
    linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
  -- ‖z‖ > 1 (since re² = 1/4 and im > √3/2 gives im² > 3/4)
  have h_norm_gt : ‖z‖ > 1 := by
    have h_im_sq_gt : z.im ^ 2 > 3 / 4 := by
      have := mul_self_lt_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) h_im_gt
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
    have h_re_sq : z.re ^ 2 = 1/4 := by rw [h_re]; ring
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    calc 1 = Real.sqrt 1 := by simp
      _ < Real.sqrt (z.re ^ 2 + z.im ^ 2) :=
          Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  -- Construct ℍ point
  let p : ℍ := ⟨z, h_im_pos⟩
  -- p ∈ 𝒟'
  have hp_fd : p ∈ 𝒟' := by
    refine ⟨?_, ?_⟩
    · show |z.re| ≤ 1/2; rw [h_re]; norm_num
    · show ‖z‖ ≥ 1; linarith
  -- f p = 0
  have hp_zero : f p = 0 := by
    have := h_zero
    simp only [modularFormCompOfComplex, Function.comp_apply] at this
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at this
  -- ord ≠ 0 → p ∈ S
  have h_ord := orderOfVanishingAt'_ne_zero_of_eq_zero_core f hf p hp_zero
  have hp_in_S := hS_complete p hp_fd h_ord
  -- ↑p ∈ S_vert_of_S S (first component: re = 1/2, ‖·‖ > 1)
  show z ∈ (↑(S_vert_of_S S) : Set ℂ)
  unfold S_vert_of_S
  rw [Finset.coe_union, Finset.coe_union, Finset.coe_union]
  left; left; left
  rw [Finset.coe_image]
  refine ⟨p, Finset.mem_filter.mpr ⟨hp_in_S, ?_⟩, rfl⟩
  constructor
  · exact h_re
  · exact h_norm_gt

/-! #### B3: Assembly Wrapper with Auto Capture -/

include hf in
/-- **Generalized Winding Number Valence Formula via CPV — Auto Capture**.

Same as `valence_formula_gWN_cpv_from_S` but without `h_oncurve_arc` or `h_oncurve_vert`.
These are derived automatically from `hS_complete` and the geometry of the fundamental domain.

The caller only needs to supply `h_residue_provider` (= `OnCurvePVProvider`, Worker A's job). -/
theorem valence_formula_gWN_cpv_from_S_auto_capture
    (S : Finset ℍ)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_residue_provider : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc_of_S S ∪ S_vert_of_S S) =
          2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
              (orderOfVanishingAt' f s : ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S.filter (fun p => f p = 0),
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  -- Derive h_oncurve_arc from hS_complete + arc geometry
  have h_oncurve_arc : ∀ t ∈ Set.Ioo (1:ℝ) 3,
      modularFormCompOfComplex f (fdBoundary_H 1 t) = 0 →
      fdBoundary_H 1 t ∈ (↑(S_arc_of_S S) : Set ℂ) := by
    intro t ht h_zero
    have ht_Icc : t ∈ Set.Icc (0:ℝ) 5 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have h_norm : ‖fdBoundary_H 1 t‖ = 1 := by
      rw [fdBoundary_H_eq_arc ht.1 ht.2]
      exact Complex.norm_exp_ofReal_mul_I _
    have h_sqrt3_lt_2 : Real.sqrt 3 < 2 := by
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
    exact oncurve_arc_capture_auto f hf S hS_complete (by linarith)
      ht_Icc h_norm h_zero
  -- Derive h_oncurve_vert from hS_complete + seg1 geometry
  have h_oncurve_vert : ∀ (H' : ℝ), Real.sqrt 3 / 2 < H' → ∀ t ∈ Set.Ioo (0:ℝ) 1,
      modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
      (fdBoundary_H H' t : ℂ) ∈ (↑(S_vert_of_S S) : Set ℂ) := by
    intro H' hH' t ht h_zero
    exact oncurve_vert_capture_auto f hf S hS_complete hH' ht h_zero
  -- Forward to existing theorem
  exact valence_formula_gWN_cpv_from_S f hf S hS hS_complete
    h_oncurve_arc h_oncurve_vert h_residue_provider

/-! #### B4-B5: Residue Provider from OnCurvePVProvider + Wrapper Theorems

These theorems build `h_residue_provider` from `OnCurvePVProvider`, then provide
wrapper theorems that take only `OnCurvePVProvider` (= Worker A's deliverable). -/

-- Copies of theorems from FD_WindingWeights (avoiding problematic import)
omit f hf in
private lemma fdBoundary_H_at_one_eq_rho_plus_one' (H : ℝ) :
    fdBoundary_H H 1 = ellipticPoint_rho_plus_one := by
  simp only [fdBoundary_H, show (1 : ℝ) ≤ 1 from le_refl 1, ↓reduceIte,
    ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one', UpperHalfPlane.coe_mk_subtype,
    Complex.ofReal_one, one_mul]
  ring

omit f hf in
private lemma fdBoundary_H_at_three_eq_rho' (H : ℝ) :
    fdBoundary_H H 3 = ellipticPoint_rho := by
  simp only [fdBoundary_H, show ¬((3 : ℝ) ≤ 1) from by norm_num,
    show ¬((3 : ℝ) ≤ 2) from by norm_num,
    show (3 : ℝ) ≤ 3 from le_refl 3, ↓reduceIte]
  rw [show (↑(Real.pi : ℝ) / 2 + (↑(3:ℝ) - 2) * (2 * ↑(Real.pi : ℝ) / 3 - ↑(Real.pi : ℝ) / 2)) * I =
    ↑(2 * Real.pi / 3) * I from by push_cast; ring]
  simp only [ellipticPoint_rho, ellipticPoint_rho', UpperHalfPlane.coe_mk_subtype]
  -- exp(↑(2π/3) * I) = cos(2π/3) + sin(2π/3)*I = -1/2 + √3/2*I
  have h_angle : (2 : ℝ) * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  apply Complex.ext
  · -- Real parts: exp(2πi/3).re = cos(2π/3) = -1/2
    rw [Complex.exp_ofReal_mul_I_re, h_angle, Real.cos_pi_sub, Real.cos_pi_div_three]
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.neg_re]
    ring
  · -- Imaginary parts: exp(2πi/3).im = sin(2π/3) = √3/2
    rw [Complex.exp_ofReal_mul_I_im, h_angle, Real.sin_pi_sub, Real.sin_pi_div_three]
    simp [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, Complex.neg_im]

-- C1: Height bound
omit f hf in
private lemma exists_height_bound_S (S : Finset ℍ) :
    ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧ 1 ≤ H₁ ∧ ∀ s ∈ S, (s : ℂ).im < H₁ := by
  rcases S.eq_empty_or_nonempty with h_empty | h_ne
  · exact ⟨1, by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)],
      le_refl 1, by simp [h_empty]⟩
  · set M := S.sup' h_ne (fun s : ℍ => (s : ℂ).im) with hM_def
    refine ⟨max 1 (M + 1), lt_of_lt_of_le ?_ (le_max_left _ _), le_max_left _ _, ?_⟩
    · nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
    · intro s hs
      calc (s : ℂ).im ≤ M := Finset.le_sup' (fun s : ℍ => (↑s : ℂ).im) hs
        _ < M + 1 := by linarith
        _ ≤ max 1 (M + 1) := le_max_right _ _

-- C2: seg4 = seg1 - 1 (copy of private lemma from CPV_ModularSide)
omit f hf in
private lemma seg4_eq_seg1_minus_one_H_core (H : ℝ) (s : ℝ) (_hs : s ∈ Icc 0 1) :
    fdBoundary_seg4_H H (4 - s) = fdBoundary_seg1_H H s - 1 := by
  simp only [fdBoundary_seg4_H, fdBoundary_seg1_H]
  have h1 : ((4 - s : ℝ) : ℂ) - 3 = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  simp only [h1]; push_cast; ring

-- Height contradiction helper
include hf in
private lemma height_contradiction_core
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_ge1 : 1 ≤ H) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H)
    {z : ℂ} (h_im : z.im = H) (h_re : |z.re| ≤ 1/2)
    (h_zero : modularFormCompOfComplex f z = 0) : False := by
  have h_im_pos : 0 < z.im := by linarith
  let p : ℍ := ⟨z, h_im_pos⟩
  have hp_fd : p ∈ 𝒟' := by
    refine ⟨h_re, ?_⟩
    show 1 ≤ ‖z‖
    have : z.im ≤ ‖z‖ := by
      calc z.im ≤ |z.im| := le_abs_self _
        _ = Real.sqrt (z.im ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (z.re ^ 2 + z.im ^ 2) := Real.sqrt_le_sqrt (by linarith [sq_nonneg z.re])
        _ = ‖z‖ := (Complex.norm_eq_sqrt_sq_add_sq z).symm
    linarith
  have hp_zero : f p = 0 := by
    simp only [modularFormCompOfComplex, Function.comp_apply] at h_zero
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at h_zero
  have h_ord := orderOfVanishingAt'_ne_zero_of_eq_zero_core f hf p hp_zero
  have hp_in_S := hS_complete p hp_fd h_ord
  have h_p_im : (↑p : ℂ).im = z.im := rfl
  linarith [hH_bound p hp_in_S]

-- C3: Seg4 zero capture
include hf in
private lemma oncurve_seg4_capture_auto
    (S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Set.Ioo (3:ℝ) 4)
    (h_zero : modularFormCompOfComplex f (fdBoundary_H H t) = 0) :
    fdBoundary_H H t ∈ (↑(S_vert_of_S S) : Set ℂ) := by
  set z := fdBoundary_H H t with hz_def
  -- z = fdBoundary_seg4_H H t
  have hz_seg : z = fdBoundary_seg4_H H t :=
    fdBoundary_H_eq_seg4_H (by linarith [ht.1]) (by linarith [ht.1])
      (by linarith [ht.1]) (le_of_lt ht.2)
  -- Set s = 4 - t in (0, 1)
  set s := 4 - t with hs_def
  have hs_Icc : s ∈ Icc (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hs_Ioo : s ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  -- seg4(t) = seg4(4-s) = seg1(s) - 1
  have h4s : (4:ℝ) - s = t := by rw [hs_def]; ring
  have h_seg_eq : z = fdBoundary_seg1_H H s - 1 := by
    rw [hz_seg, ← h4s]
    exact seg4_eq_seg1_minus_one_H_core H s hs_Icc
  -- T-periodicity: f(z) = f(z+1)
  have h_periodic : Function.Periodic (modularFormCompOfComplex f) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
    simp only [Nat.cast_one] at this; exact this
  -- f(z) = 0 -> f(z+1) = 0, and z+1 = seg1(s)
  have h_z_plus_1 : z + 1 = fdBoundary_seg1_H H s := by rw [h_seg_eq]; ring
  have h_zero_seg1 : modularFormCompOfComplex f (fdBoundary_seg1_H H s) = 0 := by
    rw [← h_z_plus_1]
    have := (h_periodic z).symm; rwa [← this]
  -- seg1(s) has re = 1/2
  have h_re : (fdBoundary_seg1_H H s).re = 1/2 := by
    simp [fdBoundary_seg1_H, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
  -- im(seg1(s)) = H - s*(H - sqrt3/2) > sqrt3/2 (since s < 1)
  have h_im_val : (fdBoundary_seg1_H H s).im = H - s * (H - Real.sqrt 3 / 2) := by
    simp [fdBoundary_seg1_H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, div_ofNat]
  have h_im_gt : (fdBoundary_seg1_H H s).im > Real.sqrt 3 / 2 := by
    rw [h_im_val]; nlinarith [hs_Ioo.2]
  have h_im_pos : 0 < (fdBoundary_seg1_H H s).im := by
    linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 by norm_num)]
  -- norm(seg1(s)) > 1
  have h_norm_gt : ‖fdBoundary_seg1_H H s‖ > 1 := by
    have h_im_sq_gt : (fdBoundary_seg1_H H s).im ^ 2 > 3/4 := by
      have h_sqrt3_sq : (Real.sqrt 3 / 2) ^ 2 = 3/4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
      have := mul_self_lt_mul_self (by positivity : 0 ≤ Real.sqrt 3 / 2) h_im_gt
      nlinarith
    have h_re_sq : (fdBoundary_seg1_H H s).re ^ 2 = 1/4 := by rw [h_re]; ring
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    calc 1 = Real.sqrt 1 := by simp
      _ < Real.sqrt ((fdBoundary_seg1_H H s).re ^ 2 + (fdBoundary_seg1_H H s).im ^ 2) :=
        Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  -- Construct UHP point p from seg1(s)
  let p : ℍ := ⟨fdBoundary_seg1_H H s, h_im_pos⟩
  -- p in FD'
  have hp_fd : p ∈ 𝒟' := by
    refine ⟨?_, ?_⟩
    · show |(fdBoundary_seg1_H H s).re| ≤ 1/2; rw [h_re]; norm_num
    · show ‖fdBoundary_seg1_H H s‖ ≥ 1; linarith
  -- f p = 0
  have hp_zero : f p = 0 := by
    simp only [modularFormCompOfComplex, Function.comp_apply] at h_zero_seg1
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at h_zero_seg1
  -- ord != 0 -> p in S
  have h_ord := orderOfVanishingAt'_ne_zero_of_eq_zero_core f hf p hp_zero
  have hp_in_S := hS_complete p hp_fd h_ord
  -- z = p - 1 in S_vert_of_S S (component B: image of re=1/2 under (. - 1))
  show z ∈ (↑(S_vert_of_S S) : Set ℂ)
  rw [h_seg_eq]
  unfold S_vert_of_S
  rw [Finset.coe_union, Finset.coe_union, Finset.coe_union]
  left; left; right
  rw [Finset.coe_image]
  exact ⟨p, Finset.mem_filter.mpr ⟨hp_in_S, h_re, h_norm_gt⟩, rfl⟩

-- C4: Full on-curve capture
include hf in
private lemma oncurve_full_capture_auto
    (S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (hH_ge1 : 1 ≤ H) (hH_sqrt3 : Real.sqrt 3 / 2 < H)
    (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) :
    ∀ t ∈ Icc (0:ℝ) 5,
      modularFormCompOfComplex f (fdBoundary_H H t) = 0 →
      fdBoundary_H H t ∈ (↑(S_arc_of_S S ∪ S_vert_of_S S) : Set ℂ) := by
  intro t ht h_zero
  rw [Finset.coe_union]
  rcases le_or_lt t 1 with h1 | h1
  · -- t in [0, 1]
    rcases (eq_or_lt_of_le ht.1 : 0 = t ∨ 0 < t) with rfl | h0
    · -- t = 0: im = H, contradiction
      exfalso
      have h_re : |((fdBoundary_H H 0)).re| ≤ 1/2 := by
        rw [fdBoundary_H_eq_seg1_H (by norm_num : (0:ℝ) ≤ 1)]
        simp [fdBoundary_seg1_H, add_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
      have h_im : (fdBoundary_H H 0).im = H := by
        rw [fdBoundary_H_eq_seg1_H (by norm_num : (0:ℝ) ≤ 1)]
        simp [fdBoundary_seg1_H, add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
      exact height_contradiction_core f hf S hS_complete hH_ge1 hH_bound h_im h_re h_zero
    · -- t in (0, 1]
      rcases (eq_or_lt_of_le h1 : t = 1 ∨ t < 1) with rfl | h1s
      · -- t = 1: rho' in S_arc
        left
        rw [fdBoundary_H_at_one_eq_rho_plus_one' H]
        exact Finset.mem_coe.mpr (S_arc_of_S_rho_plus_one_in S)
      · -- t in (0, 1): vert capture
        right
        exact oncurve_vert_capture_auto f hf S hS_complete hH_sqrt3 ⟨h0, h1s⟩ h_zero
  · -- t > 1
    rcases le_or_lt t 3 with h3 | h3
    · rcases (eq_or_lt_of_le h3 : t = 3 ∨ t < 3) with rfl | h3s
      · -- t = 3: rho in S_arc
        left
        rw [fdBoundary_H_at_three_eq_rho' H]
        exact Finset.mem_coe.mpr (S_arc_of_S_rho_in S)
      · -- t in (1, 3): arc, norm = 1
        left
        have h_norm : ‖fdBoundary_H H t‖ = 1 := by
          rw [fdBoundary_H_eq_arc h1 h3s]
          exact Complex.norm_exp_ofReal_mul_I _
        exact oncurve_arc_capture_auto f hf S hS_complete hH_sqrt3
          ⟨by linarith, by linarith [ht.2]⟩ h_norm h_zero
    · -- t > 3
      rcases le_or_lt t 4 with h4 | h4
      · rcases (eq_or_lt_of_le h4 : t = 4 ∨ t < 4) with rfl | h4s
        · -- t = 4: im = H, contradiction
          exfalso
          have h_re : |(fdBoundary_H H 4).re| ≤ 1/2 := by
            rw [fdBoundary_H_eq_seg4_H (by norm_num) (by norm_num) (by norm_num) (le_refl 4)]
            simp [fdBoundary_seg4_H, add_re, neg_re, mul_re, I_re, I_im, ofReal_re, ofReal_im,
              div_ofNat]; norm_num
          have h_im : (fdBoundary_H H 4).im = H := by
            rw [fdBoundary_H_eq_seg4_H (by norm_num) (by norm_num) (by norm_num) (le_refl 4)]
            simp [fdBoundary_seg4_H, add_im, neg_im, mul_im, I_re, I_im, ofReal_re, ofReal_im,
              div_ofNat]; ring
          exact height_contradiction_core f hf S hS_complete hH_ge1 hH_bound h_im h_re h_zero
        · -- t in (3, 4): seg4 capture
          right
          exact oncurve_seg4_capture_auto f hf S hS_complete hH_sqrt3 ⟨h3, h4s⟩ h_zero
      · -- t > 4: seg5, im = H, contradiction
        exfalso
        have h_re : |(fdBoundary_H H t).re| ≤ 1/2 := by
          rw [fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)]
          simp [fdBoundary_seg5_H, add_re, sub_re, mul_re, I_re, I_im, ofReal_re, ofReal_im]
          rw [abs_le]; constructor <;> linarith [ht.2]
        have h_im : (fdBoundary_H H t).im = H := by
          rw [fdBoundary_H_eq_seg5_H (by linarith) (by linarith) (by linarith) (by linarith)]
          simp [fdBoundary_seg5_H, add_im, sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im]
        exact height_contradiction_core f hf S hS_complete hH_ge1 hH_bound h_im h_re h_zero

-- CPV helpers (private)
omit f hf in
private lemma cpv_exists_const_mul_core (c : ℂ) (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (h : CauchyPrincipalValueExists' g γ a b s) :
    CauchyPrincipalValueExists' (fun z => c * g z) γ a b s := by
  obtain ⟨L, hL⟩ := h
  refine ⟨c * L, ?_⟩
  have heq : (fun ε => ∫ t in a..b,
      if ‖γ t - s‖ > ε then (c * g (γ t)) * deriv γ t else 0) =
    (fun ε => c * ∫ t in a..b,
      if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0) := by
    ext ε; rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr; intro t _; dsimp only
    split_ifs <;> ring
  rw [heq]; exact tendsto_const_nhds.mul hL

omit f hf in
private lemma cpv_exists_of_avoids_core (g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (s : ℂ)
    (h_cont : Continuous γ) (hab : a ≤ b)
    (h_avoid : ∀ t ∈ Icc a b, γ t ≠ s) :
    CauchyPrincipalValueExists' g γ a b s := by
  have h_cont_norm : ContinuousOn (fun t => ‖γ t - s‖) (Icc a b) :=
    (h_cont.continuousOn.sub continuousOn_const).norm
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_Icc.exists_isMinOn
    ⟨a, left_mem_Icc.mpr hab⟩ h_cont_norm
  have hδ : 0 < ‖γ t₀ - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))
  refine ⟨∫ t in a..b, g (γ t) * deriv γ t, ?_⟩
  apply Filter.Tendsto.congr'
  swap; exact tendsto_const_nhds
  rw [Filter.EventuallyEq]
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  apply intervalIntegral.integral_congr; intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact (if_pos (lt_of_lt_of_le hε.2 (ht₀_min ht))).symm

-- Helper: vert elements have im > sqrt(3)/2
omit f hf in
private lemma S_vert_of_S_im_gt_sqrt3_half (S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟') :
    ∀ s ∈ S_vert_of_S S, s.im > Real.sqrt 3 / 2 := by
  intro s hs
  unfold S_vert_of_S at hs
  -- Helper for the common pattern: |re| = 1/2, ‖p‖ > 1 => im > sqrt3/2
  have key : ∀ (p : ℍ), p ∈ S → (|(↑p : ℂ).re| = 1/2) → ‖(↑p : ℂ)‖ > 1 →
      (↑p : ℂ).im > Real.sqrt 3 / 2 := by
    intro p hp_in_S hp_re_half hp_norm
    have h_re_sq : (↑p : ℂ).re ^ 2 = 1/4 := by
      have := hp_re_half; rw [abs_eq (by norm_num : (0:ℝ) ≤ 1/2)] at this
      rcases this with h | h <;> rw [h] <;> norm_num
    have h_norm_sq_gt : ‖(↑p : ℂ)‖ ^ 2 > 1 := by
      calc ‖(↑p : ℂ)‖ ^ 2 = ‖(↑p : ℂ)‖ * ‖(↑p : ℂ)‖ := sq _
        _ > 1 * 1 := mul_lt_mul hp_norm (le_of_lt hp_norm) one_pos (norm_nonneg _)
        _ = 1 := one_mul 1
    have h_sq : (↑p : ℂ).re ^ 2 + (↑p : ℂ).im ^ 2 = ‖(↑p : ℂ)‖ ^ 2 := by
      rw [Complex.norm_eq_sqrt_sq_add_sq, Real.sq_sqrt (by positivity)]
    have h_im_sq_gt : (↑p : ℂ).im ^ 2 > 3/4 := by linarith
    have h_coe_im_pos : 0 < (↑p : ℂ).im := p.2
    -- im > sqrt(3)/2: from im^2 > 3/4 and im > 0
    by_contra h_le
    push_neg at h_le
    have h_im_sq_le : (↑p : ℂ).im ^ 2 ≤ 3/4 := by
      have := mul_self_le_mul_self (le_of_lt h_coe_im_pos) h_le
      have : (Real.sqrt 3 / 2) ^ 2 = 3/4 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]; norm_num
      nlinarith
    linarith
  rcases Finset.mem_union.mp hs with h | hD
  · rcases Finset.mem_union.mp h with h | hC
    · rcases Finset.mem_union.mp h with hA | hB
      · -- A: image (coe), re=1/2
        rcases Finset.mem_image.mp hA with ⟨p, hp_filter, rfl⟩
        obtain ⟨hp_in_S, hp_re, hp_norm⟩ := Finset.mem_filter.mp hp_filter
        exact key p hp_in_S (by rw [hp_re]; norm_num) hp_norm
      · -- B: image (coe - 1), re=1/2
        rcases Finset.mem_image.mp hB with ⟨p, hp_filter, rfl⟩
        obtain ⟨hp_in_S, hp_re, hp_norm⟩ := Finset.mem_filter.mp hp_filter
        show ((↑p : ℂ) - 1).im > Real.sqrt 3 / 2
        simp only [Complex.sub_im, Complex.one_im, sub_zero]
        exact key p hp_in_S (by rw [hp_re]; norm_num) hp_norm
    · -- C: image (coe), re=-1/2
      rcases Finset.mem_image.mp hC with ⟨p, hp_filter, rfl⟩
      obtain ⟨hp_in_S, hp_re, hp_norm⟩ := Finset.mem_filter.mp hp_filter
      exact key p hp_in_S (by rw [hp_re]; norm_num) hp_norm
  · -- D: image (coe + 1), re=-1/2
    rcases Finset.mem_image.mp hD with ⟨p, hp_filter, rfl⟩
    obtain ⟨hp_in_S, hp_re, hp_norm⟩ := Finset.mem_filter.mp hp_filter
    show ((↑p : ℂ) + 1).im > Real.sqrt 3 / 2
    simp only [Complex.add_im, Complex.one_im, add_zero]
    exact key p hp_in_S (by rw [hp_re]; norm_num) hp_norm

-- S_arc_of_S geometric bounds
omit f hf in
private lemma S_arc_of_S_re_le_half
    (S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟') :
    ∀ s ∈ S_arc_of_S S, |s.re| ≤ 1/2 := by
  intro s hs
  simp only [S_arc_of_S, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_insert, Finset.mem_singleton] at hs
  rcases hs with ⟨⟨p, ⟨hp_in_S, _⟩, rfl⟩ | ⟨p, ⟨hp_in_S, hp_norm⟩, rfl⟩⟩ | hs
  · exact (hS p hp_in_S).1
  · -- -1/p: |re(-1/p)| = |re(p)| when norm(p) = 1
    have hp_fd := hS p hp_in_S
    have h_re_p : |(↑p : ℂ).re| ≤ 1/2 := hp_fd.1
    have h_normSq : Complex.normSq (↑p : ℂ) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hp_norm]; norm_num
    -- re(-1/p) = -re(p)/normSq(p) = -re(p) when normSq = 1
    have h_neg_inv_re : (-(1:ℂ) / (↑p : ℂ)).re = -(↑p : ℂ).re := by
      rw [show -(1:ℂ) / (↑p : ℂ) = -((↑p : ℂ))⁻¹ from by ring]
      rw [Complex.neg_re, Complex.inv_re, h_normSq, div_one]
    rw [h_neg_inv_re, abs_neg]; exact h_re_p
  · rcases hs with rfl | rfl
    · -- s = ellipticPoint_rho: re = -1/2
      have : (ellipticPoint_rho : ℂ).re = -1/2 := by
        simp [ellipticPoint_rho, ellipticPoint_rho']
      rw [this]; norm_num
    · -- s = ellipticPoint_rho_plus_one: re = 1/2
      have : (ellipticPoint_rho_plus_one : ℂ).re = 1/2 := by
        simp [ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
      rw [this]; norm_num

-- C5: Main theorem - build h_residue_provider from OnCurvePVProvider
include hf in
theorem h_residue_provider_of_OnCurvePVProvider
    (S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hPV : OnCurvePVProvider f S) :
    ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc_of_S S ∪ S_vert_of_S S) =
          2 * ↑Real.pi * I * ∑ s ∈ S.filter (fun p => f p = 0),
            generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
              (orderOfVanishingAt' f s : ℂ) := by
  -- Get height bound
  obtain ⟨H₁, hH₁_sqrt3, hH₁_ge1, hH₁_bound⟩ := exists_height_bound_S S
  refine ⟨H₁, hH₁_sqrt3, fun {H} hH => ?_⟩
  -- Setup
  have hH_ge1 : 1 ≤ H := le_trans hH₁_ge1 hH
  have hH_sqrt3 : Real.sqrt 3 / 2 < H := lt_of_lt_of_le hH₁_sqrt3 hH
  have hH_bound : ∀ s ∈ S, (s : ℂ).im < H := fun s hs => lt_of_lt_of_le (hH₁_bound s hs) hH
  set S_combined := S_arc_of_S S ∪ S_vert_of_S S with hS_comb_def
  set zeros := S.filter (fun p => f p = 0) with hzeros_def
  -- zeros hypotheses
  have hzeros : ∀ s ∈ zeros, f s = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain := fun s hs =>
    hS s (Finset.mem_filter.mp hs).1
  have hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros := by
    intro s hs_fd hs_zero
    rw [hzeros_def, Finset.mem_filter]
    exact ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero_core f hf s hs_zero),
      hs_zero⟩
  -- im_pos
  have hS_im_pos : ∀ s ∈ S_combined, 0 < s.im := by
    intro s hs
    rcases Finset.mem_union.mp hs with h | h
    · exact S_arc_of_S_im_pos S s h
    · exact S_vert_of_S_im_pos S s h
  -- Geometric bounds
  have hS_geom : ∀ s ∈ S_combined, -1 < s.re ∧ s.re < 1 ∧ (1:ℝ)/2 < s.im ∧ s.im < H + 1 := by
    intro s hs
    rcases Finset.mem_union.mp hs with h_arc | h_vert
    · -- Arc: norm = 1, |re| <= 1/2 -> re in (-1,1), im >= sqrt3/2 > 1/2, im <= 1 < H+1
      have h_unit := S_arc_of_S_unit S hS s h_arc
      have h_im_pos := S_arc_of_S_im_pos S s h_arc
      have h_re_le := S_arc_of_S_re_le_half S hS s h_arc
      have h_sq : s.re ^ 2 + s.im ^ 2 = 1 := by
        have : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]; ring
        rw [h_unit] at this; linarith
      -- -1 < re < 1
      have h_re_bounds : -1 < s.re ∧ s.re < 1 := by
        constructor <;> nlinarith [abs_le.mp h_re_le]
      -- re^2 <= 1/4 from |re| <= 1/2
      have h_re_sq_le : s.re ^ 2 ≤ 1/4 := by
        have := sq_abs s.re  -- |s.re|^2 = s.re^2
        have := abs_nonneg s.re  -- 0 <= |s.re|
        nlinarith [mul_self_nonneg (1/2 - |s.re|)]
      -- im^2 >= 3/4 from re^2 + im^2 = 1
      have h_im_sq_ge : s.im ^ 2 ≥ 3/4 := by linarith
      -- sqrt(3)/2 <= im
      have h_im_ge : Real.sqrt 3 / 2 ≤ s.im := by
        nlinarith [sq_nonneg (s.im - Real.sqrt 3 / 2),
          Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
      -- 1/2 < im (since sqrt(3)/2 > 1/2)
      have h_sqrt3_gt : Real.sqrt 3 > 1 := by
        rw [show (1:ℝ) = Real.sqrt 1 from by simp]
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      -- im < H + 1: from im <= 1 <= H < H + 1
      have h_im_le : s.im ≤ 1 := by nlinarith [sq_nonneg s.re]
      exact ⟨h_re_bounds.1, h_re_bounds.2, by linarith, by linarith⟩
    · -- Vert: re = +/- 1/2, im > sqrt3/2 > 1/2, im < H < H+1
      have h_re := S_vert_of_S_re S s h_vert
      -- re bounds
      have h_re_bounds : -1 < s.re ∧ s.re < 1 := by
        rcases h_re with h | h <;> constructor <;> linarith
      -- im > sqrt3/2 > 1/2
      have h_im_gt := S_vert_of_S_im_gt_sqrt3_half S hS s h_vert
      have h_sqrt3_half_gt : Real.sqrt 3 / 2 > 1 / 2 := by
        have : Real.sqrt 3 > 1 := by
          rw [show (1:ℝ) = Real.sqrt 1 from by simp]
          exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        linarith
      -- im < H + 1
      have h_im_bound : s.im < H + 1 := by
        unfold S_vert_of_S at h_vert
        rcases Finset.mem_union.mp h_vert with h | hD
        · rcases Finset.mem_union.mp h with h | hC
          · rcases Finset.mem_union.mp h with hA | hB
            · -- A: image (coe), re=1/2
              rcases Finset.mem_image.mp hA with ⟨p, hp_filter, rfl⟩
              obtain ⟨hp_in_S, _, _⟩ := Finset.mem_filter.mp hp_filter
              linarith [hH_bound p hp_in_S]
            · -- B: image (coe - 1), re=1/2
              rcases Finset.mem_image.mp hB with ⟨p, hp_filter, rfl⟩
              obtain ⟨hp_in_S, _, _⟩ := Finset.mem_filter.mp hp_filter
              show ((↑p : ℂ) - 1).im < H + 1
              simp only [Complex.sub_im, Complex.one_im, sub_zero]
              linarith [hH_bound p hp_in_S]
          · -- C: image (coe), re=-1/2
            rcases Finset.mem_image.mp hC with ⟨p, hp_filter, rfl⟩
            obtain ⟨hp_in_S, _, _⟩ := Finset.mem_filter.mp hp_filter
            linarith [hH_bound p hp_in_S]
        · -- D: image (coe + 1), re=-1/2
          rcases Finset.mem_image.mp hD with ⟨p, hp_filter, rfl⟩
          obtain ⟨hp_in_S, _, _⟩ := Finset.mem_filter.mp hp_filter
          show ((↑p : ℂ) + 1).im < H + 1
          simp only [Complex.add_im, Complex.one_im, add_zero]
          linarith [hH_bound p hp_in_S]
      exact ⟨h_re_bounds.1, h_re_bounds.2, by linarith, h_im_bound⟩
  -- On-curve capture
  have h_oncurve := oncurve_full_capture_auto f hf S hS hS_complete hH_ge1 hH_sqrt3 hH_bound
  -- CPV for res/(z-s) for each s in S_combined
  have hPV_onCurve : ∀ s ∈ S_combined,
      CauchyPrincipalValueExists'
        (fun z => residueSimplePole (logDeriv (modularFormCompOfComplex f)) s / (z - s))
        (fdBoundary_H H) 0 5 s := by
    intro s hs
    rcases Classical.em (∃ t ∈ Icc (0:ℝ) 5, fdBoundary_H H t = s) with ⟨t, ht, rfl⟩ | h_off
    · -- On-curve: use OnCurvePVProvider + const_mul
      have h_cpv_inv := hPV H hH_sqrt3 _ hs ⟨t, ht, rfl⟩
      -- Convert (z-s)^{-1} to res/(z-s) = res * (z-s)^{-1}
      set c := residueSimplePole (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H t)
      have h_cpv := cpv_exists_const_mul_core c _ _ _ _ _ h_cpv_inv
      have h_eq : (fun z => c / (z - fdBoundary_H H t)) =
          (fun z => c * (z - fdBoundary_H H t)⁻¹) := by
        ext z; rw [div_eq_mul_inv]
      rw [h_eq]; exact h_cpv
    · -- Off-curve: CPV trivially exists
      push_neg at h_off
      exact cpv_exists_of_avoids_core _ _ _ _ _ (fdBoundary_H_continuous H) (by norm_num) h_off
  -- Apply the public wrapper
  exact cpv_logDeriv_eq_winding_public f hf hH_ge1 zeros hzeros hzeros_fd hzeros_complete
    S_combined hS_im_pos hS_geom h_oncurve hPV_onCurve

-- C6: Wrapper theorem
include hf in
theorem valence_formula_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider
    (S : Finset ℍ)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hPV : OnCurvePVProvider f S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S.filter (fun p => f p = 0),
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) :=
  valence_formula_gWN_cpv_from_S_auto_capture f hf S hS hS_complete
    (h_residue_provider_of_OnCurvePVProvider f hf S hS hS_complete hPV)

end
