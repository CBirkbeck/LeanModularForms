/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.ModularForms.BoundedAtCusp

@[expose] public section

/-!
# Cuspidal vanishing/boundedness from infinity-side hypotheses

Reduces vanishing/boundedness at an arbitrary cusp to vanishing/boundedness at the cusp
at infinity, by lifting along the `SL(2, ℤ)` action via
`OnePoint.isZeroAt_iff_forall_SL2Z` / `OnePoint.isBoundedAt_iff_forall_SL2Z`.
-/

open scoped MatrixGroups ModularForm UpperHalfPlane

