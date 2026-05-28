/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import LeanModularForms.Modularforms.PhiTransform

/-!
# Lemmas about the transformation of `φ₀`

This file records translation-periodicity lemmas for the auxiliary functions `φ₂'`, `φ₄'` and `φ₀`,
as well as a convenient reformulation of `φ₀_S_transform`.

Here the prime in `φ₂'` and `φ₄'` is part of the name of these auxiliary functions.

## Main statements
* `φ₂'_periodic` and `φ₄'_periodic`
* `φ₀_periodic_neg_one`
* `φ₀_S_transform_mul_sq`
-/

open scoped Real

open ModularForm EisensteinSeries UpperHalfPlane Complex

noncomputable section

/-- `φ₂'` is 1-periodic: `φ₂' ((1 : ℝ) +ᵥ z) = φ₂' z`. -/
public theorem φ₂'_periodic (z : ℍ) : φ₂' ((1 : ℝ) +ᵥ z) = φ₂' z := by
  simp [φ₂', E₂_periodic, E₄_periodic, E₆_periodic, Δ_periodic]

/-- `φ₄'` is 1-periodic: `φ₄' ((1 : ℝ) +ᵥ z) = φ₄' z`. -/
public theorem φ₄'_periodic (z : ℍ) : φ₄' ((1 : ℝ) +ᵥ z) = φ₄' z := by
  simp [φ₄', E₄_periodic, Δ_periodic]

private theorem periodic_neg_one_aux {α : Type*} (F : ℍ → α)
    (hper : ∀ z : ℍ, F ((1 : ℝ) +ᵥ z) = F z) (z : ℍ) : F ((-1 : ℝ) +ᵥ z) = F z := by
  simpa [add_vadd] using (hper ((-1 : ℝ) +ᵥ z)).symm

/-- `φ₂'` is also `(-1)`-periodic. -/
public theorem φ₂'_periodic_neg_one (z : ℍ) : φ₂' ((-1 : ℝ) +ᵥ z) = φ₂' z :=
  periodic_neg_one_aux φ₂' φ₂'_periodic z

/-- `φ₄'` is also `(-1)`-periodic. -/
public theorem φ₄'_periodic_neg_one (z : ℍ) : φ₄' ((-1 : ℝ) +ᵥ z) = φ₄' z :=
  periodic_neg_one_aux φ₄' φ₄'_periodic z

/-- `φ₀` is also `(-1)`-periodic. -/
public theorem φ₀_periodic_neg_one (z : ℍ) : φ₀ ((-1 : ℝ) +ᵥ z) = φ₀ z :=
  periodic_neg_one_aux φ₀ φ₀_periodic z

/-- A convenient form of `φ₀_S_transform`, clearing the denominators by multiplying by `z^2`. -/
public theorem φ₀_S_transform_mul_sq (z : ℍ) :
    φ₀ (ModularGroup.S • z) * (z : ℂ) ^ (2 : ℕ) =
      φ₀ z * (z : ℂ) ^ (2 : ℕ) - (12 * Complex.I) / π * (z : ℂ) * φ₂' z -
        36 / (π ^ 2) * φ₄' z := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hmul := congrArg (fun w : ℂ ↦ w * (z : ℂ) ^ (2 : ℕ)) (φ₀_S_transform z)
  have hz2 : (z : ℂ) ^ (2 : ℕ) ≠ 0 := pow_ne_zero _ hz
  have hsimp :
      (φ₀ z - (12 * Complex.I) / (π * z) * φ₂' z - 36 / (π ^ 2 * z ^ (2 : ℕ)) * φ₄' z) *
            (z : ℂ) ^ (2 : ℕ) =
          φ₀ z * (z : ℂ) ^ (2 : ℕ) - (12 * Complex.I) / π * (z : ℂ) * φ₂' z -
            36 / (π ^ 2) * φ₄' z := by
    simp [pow_two, sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    field_simp [hz, hz2, hπ]
  simpa [hsimp] using hmul

end
