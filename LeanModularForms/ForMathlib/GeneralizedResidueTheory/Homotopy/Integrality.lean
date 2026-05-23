/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.ForMathlib.ClassicalCPV
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Homotopy Integrality Helper

A small filter helper used by the winding-number-classical formula in
`Homotopy.Invariance`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- If f is eventually equal to a constant, `limUnder` equals that constant. -/
theorem limUnder_eventually_eq_const {α : Type*} [TopologicalSpace α] {f : α → ℂ}
    {l : Filter α} {c : ℂ} [l.NeBot] (hf : ∀ᶠ x in l, f x = c) : limUnder l f = c :=
  (tendsto_const_nhds.congr' (hf.mono fun _ h => h.symm)).limUnder_eq

end
