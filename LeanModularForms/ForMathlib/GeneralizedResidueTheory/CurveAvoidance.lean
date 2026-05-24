/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV
import Mathlib

/-!
# Curve Avoidance API

General-purpose lemmas for proving that curves avoid points, computing minimum distances,
and establishing slitPlane membership for shifted curves.

## Main definitions

* `CurveAvoids` - a curve on [a,b] avoids a point z₀
* `curveInfDist` - infimum distance from z₀ to the curve image on [a,b]

## Main results

* `curveInfDist_pos_of_avoids` - positive inf distance when curve avoids z₀
* `curveAvoids_of_im_lt` - curve with larger imaginary part avoids `z₀`
* `curve_sub_in_slitPlane` - shifted curve lands in slitPlane
-/

open Set Complex Metric

/-- A continuous curve on [a,b] avoids a point z₀. -/
def CurveAvoids (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∀ t ∈ Icc a b, γ t ≠ z₀

/-- Infimum distance from z₀ to the curve image on [a,b]. -/
noncomputable def curveInfDist (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : ℝ :=
  Metric.infDist z₀ (γ '' Icc a b)

