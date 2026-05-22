/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Data.Real.StarOrdered

@[expose] public section

/-!
# `ℕ+`/positive-`ℤ` reformulations of `UpperHalfPlane.im_pnat_div_pos`

Convenience wrappers around `UpperHalfPlane.im_pnat_div_pos` for `ℕ+` and positive `ℤ`
indices, used in the modular-forms development.
-/

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := im_pnat_div_pos (↑n) z

lemma pos_nat_div_upper (n : ℤ) (hn : 0 < n) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  lift n to ℕ+ using hn; exact pnat_div_upper n z
