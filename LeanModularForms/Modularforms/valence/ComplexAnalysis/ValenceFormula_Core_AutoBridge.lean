/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Core
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_CuspHeight

/-!
# Auto Bridge — Valence Formula with Residue-Auto Provider

This file provides bridge theorems that consume a **residue-auto provider** hypothesis
`h_residue_auto` and forward to the D2.1 Core theorems, removing `h_cpv_eq_residue`
from the per-height API.

## Architecture

The proof chain composes:
1. **Modular side** (`modular_side_auto_cusp_generalizedPV`): provides `∃ H₀_mod > √3/2`
   such that for `H ≥ H₀_mod`, the generalized PV integral equals the modular side.
2. **Residue-auto provider** (`h_residue_auto`): provides `∃ H₁ > √3/2` such that
   for `H ≥ H₁`, the generalized PV integral equals the residue side.
3. At `H₀ := max H₀_mod H₁`, both sides hold, yielding the algebraic identity.

## Theorems

* `valence_formula_base_identity_auto_of_residue_auto` — existential-height base identity
  (effectiveWinding form, ℂ-valued)
* `valence_formula_classical_rat_auto_of_residue_auto` — existential-height classical form
  (decomposed 1/2, 1/3, interior filter, ℚ-valued, **no `hclass`**)
* `valence_formula_windingCoeff_rat_auto_of_residue_auto` — existential-height windingCoeff form
  (windingNumberCoeff' form, ℚ-valued, requires `hclass` — prefer the classical form above)

## Available Infrastructure

From `ValenceFormula_CuspHeight.lean`:
- `cuspFunction_not_eventually_zero` : f ≠ 0 → cuspFunction not eventually zero near 0
- `cuspFunction_eventually_ne_zero` : f ≠ 0 → cuspFunction eventually nonzero in 𝓝[≠] 0
- `exists_radius_cusp_nonvanishing` : ∃ r > 0, cuspFunction nonvanishing on ball(0,r)\{0}
- `exists_height_cusp_nonvanishing` : ∃ H > √3/2, cuspFunction nonvanishing on corresponding q-circle
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

include hf

/-- Existential-height base identity with residue-auto provider.

Forwards to `valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto`
from Core. The provider `h_residue_auto` supplies a height above which the generalized
PV integral equals the residue sum; combined with the modular side, yields the
algebraic identity `Σ ew·ord = k/12 - ord_∞`. -/
theorem valence_formula_base_identity_auto_of_residue_auto (zeros : Finset ℍ)
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
          (k : ℂ) / 12 - (orderAtCusp' f : ℂ) :=
  valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto f hf zeros
    h_arc_nv h_residue_auto

/-- Classical form (ℚ-valued, `hclass`-free) with residue-auto provider.

Decomposes the `effectiveWinding` sum using `sum_ew_ord_decompose_unconditional`
into explicit `(1/2)·ord_i + (1/3)·ord_ρ + Σ_{interior} ord_p` terms.
**No `hclass` hypothesis needed** — boundary points have `effectiveWinding = 0`
and contribute nothing.

  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{interior} ord_p(f) = k/12` -/
theorem valence_formula_classical_rat_auto_of_residue_auto (zeros : Finset ℍ)
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
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_classical_form_auto_cusp_generalizedPV_of_residue_auto f hf zeros
      h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  have h_C := h_auto hH h_vert_nv
  apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
  push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
  exact h_C

/-- Existential-height windingCoeff form with residue-auto provider (ℚ-valued).

Converts `effectiveWinding` to `windingNumberCoeff'` using the classification
hypothesis `hclass`, then rearranges to `ord_∞ + Σ wc·ord = k/12`.

**Prefer `valence_formula_classical_rat_auto_of_residue_auto`** which avoids `hclass`. -/
theorem valence_formula_windingCoeff_rat_auto_of_residue_auto (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * I * ∑ s ∈ zeros,
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)))
    (hclass : ∀ s ∈ zeros,
      isInteriorPoint s ∨ s = ellipticPoint_i' ∨ s = ellipticPoint_rho') :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          ∑ s ∈ zeros, windingNumberCoeff' s * (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_of_residue_auto f hf zeros h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  have h_base := h_auto hH h_vert_nv
  have h_rat : ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by exact_mod_cast h_base
  have h_sum_eq : ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      ∑ s ∈ zeros, windingNumberCoeff' s * (orderOfVanishingAt' f s : ℚ) := by
    apply Finset.sum_congr rfl
    intro s hs
    congr 1
    exact effectiveWinding_eq_windingCoeff_of_classified s (hclass s hs)
  rw [h_sum_eq] at h_rat
  linarith

/-! ## Decomposed-Hypothesis Variants

These theorems replace the abstract `h_residue_auto` provider with the concrete
decomposed hypotheses (`h_elliptic_nv`, `h_vert_nv_ref`, `hcusp_ref`, zero set)
from `exists_height_residue_auto_of_decomposed_nv`. -/

/-- Base identity with decomposed hypotheses (ℂ-valued, effectiveWinding form).

Composes `exists_height_residue_auto_of_decomposed_nv` with the base identity assembly.
Replaces `h_nv_ref` with `h_elliptic_nv + h_vert_nv_ref`. -/
theorem valence_formula_base_identity_of_decomposed_nv (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_elliptic_nv :
        modularFormCompOfComplex f (ellipticPoint_i : ℂ) ≠ 0 ∧
        modularFormCompOfComplex f (ellipticPoint_rho_plus_one : ℂ) ≠ 0 ∧
        modularFormCompOfComplex f (ellipticPoint_rho : ℂ) ≠ 0)
    (h_vert_nv_ref : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H_height t) ≠ 0)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hcusp_ref : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H_height),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        ∑ s ∈ zeros, (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ) =
          (k : ℂ) / 12 - (orderAtCusp' f : ℂ) :=
  valence_formula_base_identity_auto_of_residue_auto f hf zeros h_arc_nv
    (exists_height_residue_auto_of_decomposed_nv f hf zeros h_arc_nv h_elliptic_nv
      h_vert_nv_ref hzeros hzeros_fd hzeros_complete hcusp_ref)

/-- Classical valence formula with decomposed hypotheses (ℚ-valued).

  `ord_∞(f) + (1/2)·ord_i(f) + (1/3)·ord_ρ(f) + Σ_{interior} ord_p(f) = k/12`

Hypotheses are the decomposed form of the monolithic `h_nv_ref`:
- `h_arc_nv`: f nonzero on arc (H-independent)
- `h_elliptic_nv`: f nonzero at i, ρ', ρ
- `h_vert_nv_ref`: f nonzero on vertical at `H_height`
- `hcusp_ref`: cusp nonvanishing at `H_height`
- `hzeros*`: zero set completeness -/
theorem valence_formula_classical_rat_of_decomposed_nv (zeros : Finset ℍ)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_elliptic_nv :
        modularFormCompOfComplex f (ellipticPoint_i : ℂ) ≠ 0 ∧
        modularFormCompOfComplex f (ellipticPoint_rho_plus_one : ℂ) ≠ 0 ∧
        modularFormCompOfComplex f (ellipticPoint_rho : ℂ) ≠ 0)
    (h_vert_nv_ref : ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H_height t) ≠ 0)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ fundamentalDomain)
    (hzeros_complete : ∀ s, s ∈ fundamentalDomain → f s = 0 → s ∈ zeros)
    (hcusp_ref : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H_height),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 :=
  valence_formula_classical_rat_auto_of_residue_auto f hf zeros h_arc_nv
    (exists_height_residue_auto_of_decomposed_nv f hf zeros h_arc_nv h_elliptic_nv
      h_vert_nv_ref hzeros hzeros_fd hzeros_complete hcusp_ref)

end
