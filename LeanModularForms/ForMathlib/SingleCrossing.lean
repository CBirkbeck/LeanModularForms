/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber

/-!
# Single-Crossing Winding Number Framework

Unified framework for computing `generalizedWindingNumber γ z₀` when the
piecewise C1 curve `γ` crosses the point `z₀` at exactly one parameter value `t₀ ∈ (0, 1)`.

## Overview

The three edge/arc winding proofs (RightEdge, LeftEdge, UnitArc) share a
common 5-step structure:

1. Identify the unique crossing parameter `t₀`
2. Define a cutoff function `δ(ε)` that maps the norm threshold `ε` to a
   parameter-space interval radius around `t₀`
3. Prove far/near bounds: curve is ε-far from `z₀` outside `[t₀-δ, t₀+δ]`,
   and ε-close inside
4. Prove the FTC telescope: the far-segment integrals sum to some `E(ε)`
5. Prove `E(ε) → L` as `ε → 0⁺`, giving `gWN = L / (2πi)`

This file provides:
- `SingleCrossingData`: a structure bundling all geometric ingredients
- `SingleCrossingData.hasCauchyPV`: the CPV integral has limit `L`
- `SingleCrossingData.hasWindingNumber`: the generalized winding number is `L / (2πi)`
- `SingleCrossingData.windingNumber_neg_half`: specialized for `L = -πi` giving `-1/2`
- `SingleCrossingData.windingNumber_neg_sixth`: specialized for `L = -πi/3` giving `-1/6`

## Design

The key abstraction is that the PV integral splits into three pieces:
on `[0, t₀-δ]` and `[t₀+δ, 1]` the cutoff integrand equals the full integrand
(by the far bound), while on `[t₀-δ, t₀+δ]` it vanishes (by the near bound).
The sum of the two outer pieces equals `E(ε)`, which tends to `L`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-- Data for computing the generalized winding number at a single crossing point.
The curve `γ` crosses `z₀` at exactly one parameter value `t₀ ∈ (0, 1)`. -/
structure SingleCrossingData (γ : PiecewiseC1Path x y) (z₀ : ℂ) where
  /-- Target PV limit value. -/
  L : ℂ
  /-- Unique crossing parameter in `(0, 1)`. -/
  t₀ : ℝ
  ht₀ : t₀ ∈ Ioo 0 1
  /-- Cutoff function: norm threshold `ε` maps to parameter radius. -/
  δ : ℝ → ℝ
  /-- Threshold below which all bounds hold. -/
  threshold : ℝ
  hthresh : 0 < threshold
  /-- `δ(ε)` is positive for valid `ε`. -/
  hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε
  /-- `δ(ε)` is small enough: stays within `(0, 1)` around `t₀`. -/
  hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min t₀ (1 - t₀)
  /-- Far bound: curve is ε-far from `z₀` outside the δ-window. -/
  h_far : ∀ ε, 0 < ε → ε < threshold →
    ∀ t ∈ Icc 0 1, δ ε < |t - t₀| → ε < ‖γ t - z₀‖
  /-- Near bound: curve is ε-close inside the δ-window. -/
  h_near : ∀ ε, 0 < ε → ε < threshold →
    ∀ t, |t - t₀| ≤ δ ε → ‖γ t - z₀‖ ≤ ε
  /-- FTC expression for the far-segment integrals. -/
  E : ℝ → ℂ
  /-- The far-segment integrals equal `E(ε)`. -/
  h_ftc : ∀ ε, 0 < ε → ε < threshold →
    (∫ t in (0 : ℝ)..(t₀ - δ ε),
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t) +
    (∫ t in (t₀ + δ ε)..1,
        (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t) = E ε
  /-- Integrability on the left segment. -/
  hint_left : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t)
      volume 0 (t₀ - δ ε)
  /-- Integrability on the right segment. -/
  hint_right : ∀ ε, 0 < ε → ε < threshold →
    IntervalIntegrable
      (fun t => (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t)
      volume (t₀ + δ ε) 1
  /-- `E(ε) → L` as `ε → 0⁺`. -/
  h_limit : Tendsto E (𝓝[>] 0) (𝓝 L)

namespace SingleCrossingData

variable {γ : PiecewiseC1Path x y} {z₀ : ℂ}

/-- The CPV of `(z - z₀)⁻¹` along `γ` exists and equals `D.L`.

The proof splits the cutoff integral into three pieces at `t₀ ± δ(ε)`:
- On `[0, t₀-δ]` and `[t₀+δ, 1]`: the cutoff is inactive (by `h_far`),
  so the integrand matches the full function.
- On `[t₀-δ, t₀+δ]`: the cutoff zeroes the integrand (by `h_near`).
The sum of the two outer pieces equals `E(ε)` (by `h_ftc`), which tends to `L`. -/
theorem hasCauchyPV (D : SingleCrossingData γ z₀) :
    HasCauchyPV (fun z => (z - z₀)⁻¹) γ z₀ D.L := by
  simp only [HasCauchyPV]
  -- Show the cutoff integral eventually equals E(ε), then use h_limit
  have h_ev : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrand (fun z => (z - z₀)⁻¹) γ.toPath.extend z₀ ε t)
      =ᶠ[𝓝[>] 0] D.E := by
    filter_upwards [Ioo_mem_nhdsGT D.hthresh] with ε hε
    have hε_pos : 0 < ε := hε.1
    have hε_lt : ε < D.threshold := hε.2
    -- Extract key bounds
    have hδ_pos := D.hδ_pos ε hε_pos hε_lt
    have hδ_small := D.hδ_small ε hε_pos hε_lt
    have hδ_lt_t₀ : D.δ ε < D.t₀ := lt_of_lt_of_le hδ_small (min_le_left _ _)
    have hδ_lt_1mt₀ : D.δ ε < 1 - D.t₀ := lt_of_lt_of_le hδ_small (min_le_right _ _)
    have h_left_lt : (0 : ℝ) < D.t₀ - D.δ ε := by linarith
    have h_mid_lt : D.t₀ - D.δ ε < D.t₀ + D.δ ε := by linarith
    have h_right_lt : D.t₀ + D.δ ε < 1 := by linarith
    -- Set up the cutoff integrand
    set F := fun t => cpvIntegrand (fun z => (z - z₀)⁻¹)
      γ.toPath.extend z₀ ε t with hF_def
    -- F = 0 on the middle segment
    have hF_mid : ∀ t ∈ Set.uIoc (D.t₀ - D.δ ε) (D.t₀ + D.δ ε), F t = 0 := by
      intro t ht
      rw [Set.uIoc_of_le (le_of_lt h_mid_lt)] at ht
      simp only [hF_def, cpvIntegrand]
      rw [if_neg (not_lt.mpr _)]
      exact D.h_near ε hε_pos hε_lt t (by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2])
    -- F = full integrand a.e. on [0, t₀ - δ]
    have hF_left : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 (D.t₀ - D.δ ε) →
        F t = (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t := by
      have h_sing : ({D.t₀ - D.δ ε} : Set ℝ)ᶜ ∈ ae volume :=
        compl_mem_ae_iff.mpr (by exact (Set.finite_singleton _).measure_zero volume)
      filter_upwards [h_sing] with t ht_ne ht_mem
      rw [Set.uIoc_of_le (le_of_lt h_left_lt)] at ht_mem
      have ht_lt : t < D.t₀ - D.δ ε :=
        lt_of_le_of_ne ht_mem.2 (fun h => ht_ne (Set.mem_singleton_iff.mpr h))
      simp only [hF_def, cpvIntegrand]
      rw [if_pos]
      apply D.h_far ε hε_pos hε_lt t
      · exact ⟨le_of_lt ht_mem.1, le_of_lt (by linarith)⟩
      · rw [abs_of_nonpos (by linarith)]
        linarith
    -- F = full integrand a.e. on [t₀ + δ, 1]
    have hF_right : ∀ᵐ t ∂volume, t ∈ Set.uIoc (D.t₀ + D.δ ε) 1 →
        F t = (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t := by
      have h_sing : ({D.t₀ + D.δ ε} : Set ℝ)ᶜ ∈ ae volume :=
        compl_mem_ae_iff.mpr (by exact (Set.finite_singleton _).measure_zero volume)
      filter_upwards [h_sing] with t ht_ne ht_mem
      rw [Set.uIoc_of_le (le_of_lt h_right_lt)] at ht_mem
      have ht_gt : D.t₀ + D.δ ε < t :=
        ht_mem.1
      simp only [hF_def, cpvIntegrand]
      rw [if_pos]
      apply D.h_far ε hε_pos hε_lt t
      · exact ⟨by linarith [D.ht₀.1], ht_mem.2⟩
      · rw [abs_of_pos (by linarith)]
        linarith
    -- Integrability of F on each piece
    have hF_int_left : IntervalIntegrable F volume 0 (D.t₀ - D.δ ε) :=
      (D.hint_left ε hε_pos hε_lt).congr_ae
        ((ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_left.mono (fun t ht hm => (ht hm).symm)))
    have hF_int_mid : IntervalIntegrable F volume (D.t₀ - D.δ ε) (D.t₀ + D.δ ε) :=
      (IntervalIntegrable.zero (μ := volume)
        (a := D.t₀ - D.δ ε) (b := D.t₀ + D.δ ε)).congr
        (fun t ht => (hF_mid t ht).symm)
    have hF_int_right : IntervalIntegrable F volume (D.t₀ + D.δ ε) 1 :=
      (D.hint_right ε hε_pos hε_lt).congr_ae
        ((ae_restrict_iff' measurableSet_uIoc).mpr
          (hF_right.mono (fun t ht hm => (ht hm).symm)))
    -- Split the full integral into three pieces
    have h_split : ∫ t in (0 : ℝ)..1, F t =
        (∫ t in (0 : ℝ)..(D.t₀ - D.δ ε), F t) +
        (∫ t in (D.t₀ - D.δ ε)..(D.t₀ + D.δ ε), F t) +
        (∫ t in (D.t₀ + D.δ ε)..1, F t) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals
            (hF_int_left.trans hF_int_mid) hF_int_right,
          ← intervalIntegral.integral_add_adjacent_intervals hF_int_left hF_int_mid]
    -- Middle integral is zero
    have h_mid_zero : ∫ t in (D.t₀ - D.δ ε)..(D.t₀ + D.δ ε), F t = 0 :=
      intervalIntegral.integral_zero_ae (ae_of_all _ (fun t ht => hF_mid t ht))
    -- Left and right integrals match the full integrand
    have h_eq_left : ∫ t in (0 : ℝ)..(D.t₀ - D.δ ε), F t =
        ∫ t in (0 : ℝ)..(D.t₀ - D.δ ε),
          (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t :=
      intervalIntegral.integral_congr_ae hF_left
    have h_eq_right : ∫ t in (D.t₀ + D.δ ε)..1, F t =
        ∫ t in (D.t₀ + D.δ ε)..1,
          (γ.toPath.extend t - z₀)⁻¹ * deriv γ.toPath.extend t :=
      intervalIntegral.integral_congr_ae hF_right
    -- Assemble: the full integral equals E(ε)
    show ∫ t in (0 : ℝ)..1, F t = D.E ε
    rw [h_split, h_mid_zero, h_eq_left, h_eq_right, add_zero]
    exact D.h_ftc ε hε_pos hε_lt
  exact D.h_limit.congr' h_ev.symm

/-- The generalized winding number at `z₀` equals `L / (2πi)`. -/
theorem hasWindingNumber (D : SingleCrossingData γ z₀) :
    HasGeneralizedWindingNumber γ z₀ (D.L / (2 * ↑Real.pi * I)) := by
  rw [show D.L / (2 * ↑Real.pi * I) = (2 * ↑Real.pi * I)⁻¹ * D.L from by ring]
  exact hasGeneralizedWindingNumber_of_hasCauchyPV D.hasCauchyPV

/-- The generalized winding number equals the concrete value determined by `L`. -/
theorem windingNumber_eq (D : SingleCrossingData γ z₀) :
    generalizedWindingNumber γ z₀ = D.L / (2 * ↑Real.pi * I) :=
  D.hasWindingNumber.eq

/-- If `L = -(π * I)`, then the generalized winding number is `-1/2`.
This is the most common case, used for edges crossing through a non-elliptic point. -/
theorem windingNumber_neg_half (D : SingleCrossingData γ z₀)
    (hL : D.L = -(↑Real.pi * I)) :
    generalizedWindingNumber γ z₀ = -1 / 2 := by
  rw [D.windingNumber_eq, hL]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

/-- If `L = -(π / 3 * I)`, then the generalized winding number is `-1/6`.
Used for elliptic point winding number computations. -/
theorem windingNumber_neg_sixth (D : SingleCrossingData γ z₀)
    (hL : D.L = -(↑Real.pi / 3 * I)) :
    generalizedWindingNumber γ z₀ = -1 / 6 := by
  rw [D.windingNumber_eq, hL]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp; ring

end SingleCrossingData

end
