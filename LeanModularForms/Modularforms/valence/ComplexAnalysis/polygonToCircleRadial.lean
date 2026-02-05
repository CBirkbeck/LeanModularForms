/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PiecewiseHomotopy
import LeanModularForms.Modularforms.valence.ComplexAnalysis.WindingNumberInterior
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Rect_Homotopy


noncomputable section

open Complex Set



lemma polygonToCircleRadial_continuous (p : ℂ) : Continuous (polygonToCircleRadial p) := by
  rw [continuous_iff_continuousAt ]
  unfold polygonToCircleRadial
  simp [fdPolygon]


  sorry
