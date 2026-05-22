/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Data.Real.StarOrdered
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

/-!
# Auxiliary identities for `riemannZeta`

Specialisations of mathlib's `two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even` used in the
modular-forms development.
-/

open TopologicalSpace Set MeasureTheory intervalIntegral Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

lemma zeta_two_eqn : ∑' (n : ℤ), ((n : ℂ) ^ 2)⁻¹ = 2 * riemannZeta 2 := by
  simpa using (two_mul_riemannZeta_eq_tsum_int_inv_pow_of_even (k := 2) le_rfl even_two).symm
