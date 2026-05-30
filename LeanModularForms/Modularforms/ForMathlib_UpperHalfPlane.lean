/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Data.Fintype.Parity
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# `S² = -I` in `SL(2, ℤ)`

A small lemma about the standard generator `S` of `SL(2, ℤ)` satisfying `S * S = -I`.
Candidate for upstreaming to `Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup`.
-/

@[expose] public section

/-- The standard generator `S = ![![0, -1], ![1, 0]]` of `SL(2, ℤ)` satisfies `S * S = -I`. -/
theorem ModularGroup.modular_S_sq : S * S = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [S]
