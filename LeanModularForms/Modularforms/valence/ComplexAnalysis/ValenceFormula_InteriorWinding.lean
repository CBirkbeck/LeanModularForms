/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Rect_Homotopy

/-!
# Interior Winding Number for Fundamental Domain Boundary

This file bridges the proven homotopy result from `ValenceFormula_Rect_Homotopy.lean`
(namespaced as `RectHomotopyProof`) to the canonical split-file definitions.

## Main Result

* `generalizedWindingNumber_fdBoundary_eq_neg_one`:
  For `p` in the interior of the truncated fundamental domain
  (`‖p‖ > 1`, `|p.re| < 1/2`, `p.im < H_height`), we have
  `generalizedWindingNumber' fdBoundary 0 5 p = -1`.

  The sign is **negative** because `fdBoundary` traverses the fundamental domain
  **clockwise** (DOWN-LEFT-UP-RIGHT). This is consistent with the downstream
  `h_winding = -(effectiveWinding ...)` convention in `ValenceFormula_Core.lean`.

## Proof Status

The proof forwards to `RectHomotopyProof.generalizedWindingNumber_fdBoundary_eq_neg_one`
which is sorry-free. The bridge lemmas verify definitional equality of `fdBoundary`
and `H_height` across the two namespaces.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval UpperHalfPlane

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Bridge Lemmas -/

/-- The canonical `fdBoundary` equals the `RectHomotopyProof` copy (same definition body). -/
private lemma fdBoundary_eq_rect : fdBoundary = RectHomotopyProof.fdBoundary := by
  ext t; unfold fdBoundary RectHomotopyProof.fdBoundary H_height RectHomotopyProof.H_height; rfl

/-- The canonical `H_height` equals the `RectHomotopyProof` copy. -/
private lemma H_height_eq_rect : H_height = RectHomotopyProof.H_height := by
  unfold H_height RectHomotopyProof.H_height; rfl

/-! ## Main Theorem -/

/-- The generalized winding number of `fdBoundary` around an interior point is `-1`.

The sign is negative because `fdBoundary` is parameterized **clockwise**
(segments: right-vertical DOWN, arc LEFT, left-vertical UP, horizontal RIGHT).

**Proof**: forwards to `RectHomotopyProof.generalizedWindingNumber_fdBoundary_eq_neg_one`
via definitional equality of `fdBoundary` and `H_height`. -/
theorem generalizedWindingNumber_fdBoundary_eq_neg_one
    (p : ℂ) (hp_norm : ‖p‖ > 1) (hp_re : |p.re| < 1/2)
    (hp_im_pos : 0 < p.im) (hp_im : p.im < H_height) :
    generalizedWindingNumber' fdBoundary 0 5 p = -1 := by
  rw [fdBoundary_eq_rect]
  exact RectHomotopyProof.generalizedWindingNumber_fdBoundary_eq_neg_one p hp_norm hp_re
    hp_im_pos (H_height_eq_rect ▸ hp_im)

/-! ## Convenience Variants -/

/-- Variant of `generalizedWindingNumber_fdBoundary_eq_neg_one` for upper half-plane points.
Derives `0 < p.im` from `s.im_pos`. -/
theorem generalizedWindingNumber_fdBoundary_eq_neg_one_uhp
    (s : ℍ) (hs_norm : ‖(s : ℂ)‖ > 1) (hs_re : |(s : ℂ).re| < 1/2)
    (hs_im : (s : ℂ).im < H_height) :
    generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) = -1 :=
  generalizedWindingNumber_fdBoundary_eq_neg_one (s : ℂ) hs_norm hs_re s.im_pos hs_im

/-- For interior points (non-elliptic, in the fundamental domain), the generalized winding
number equals `-(windingNumberCoeff' s : ℂ)`.

This is the exact form needed by the downstream `h_winding` hypothesis in
`valence_formula_base_identity` (via `effectiveWinding_eq_windingCoeff_of_classified`). -/
theorem generalizedWindingNumber_fdBoundary_eq_neg_windingCoeff_interior
    (s : ℍ) (hs_norm : ‖(s : ℂ)‖ > 1) (hs_re : |(s : ℂ).re| < 1/2)
    (hs_im : (s : ℂ).im < H_height)
    (hs_not_i : s ≠ ellipticPoint_i') (hs_not_rho : s ≠ ellipticPoint_rho') :
    generalizedWindingNumber' fdBoundary 0 5 (s : ℂ) = -(windingNumberCoeff' s : ℂ) := by
  rw [windingNumberCoeff_interior s hs_not_i hs_not_rho]
  push_cast
  exact generalizedWindingNumber_fdBoundary_eq_neg_one_uhp s hs_norm hs_re hs_im
