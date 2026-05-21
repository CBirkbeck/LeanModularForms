/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path

/-!
# Piecewise C¹ Paths on Arbitrary Intervals

This file generalizes `PiecewiseC1Path` (defined on the unit interval `[0, 1]` via
mathlib's `Path`) to a free interval `[a, b]` with `a < b`. This is Phase 1 of the
P4 unification plan (see `P4_PLAN.md`).

## Main definitions

* `PiecewiseC1PathOn a b hab x y` — a continuous function `ℝ → E` with `f a = x`,
  `f b = y`, continuous on `[a, b]`, that is `C¹` away from a finite set of breakpoints
  in `(a, b)`. The partition lives in the open interval `Ioo a b`.

* `PiecewiseC1Path.toPiecewiseC1PathOn` — embed the unit-interval form into the
  free-interval form at `a = 0, b = 1`.

## Design notes

This is a parallel structure to `PiecewiseC1Path`. Existing call sites keep using
`PiecewiseC1Path`; new infrastructure (Phases 2–4) can build directly on
`PiecewiseC1PathOn`. Affine reparametrization between the two forms is established
in a follow-up file.

We deliberately do not require the underlying carrier to be a mathlib `Path`,
because `Path` is fixed to `[0, 1]` via `unitInterval`. A free-interval generalization
needs a raw `ℝ → E` with continuity on `Icc a b`.

## References

* `PROJECT_OVERVIEW.md` §3.6 (four parallel curve types).
* `P4_PLAN.md` (multi-day plan).
-/

open Set Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A piecewise continuously differentiable path from `x` to `y` on a free interval
`[a, b]` in a normed space.

The smoothness conditions (differentiability and continuous derivative) hold at every
point of `(a, b)` outside a finite set of breakpoints. The partition lives in the open
interval `Ioo a b` — the endpoints `a` and `b` are not partition points. -/
structure PiecewiseC1PathOn (a b : ℝ) (hab : a < b) (x y : E) where
  /-- The underlying function `ℝ → E`. -/
  toFun : ℝ → E
  /-- The path starts at `x` (at parameter `a`). -/
  source : toFun a = x
  /-- The path ends at `y` (at parameter `b`). -/
  target : toFun b = y
  /-- The path is continuous on the closed interval `[a, b]`. -/
  continuous_toFun : ContinuousOn toFun (Icc a b)
  /-- Finite set of breakpoints in the open interval `(a, b)`. -/
  partition : Finset ℝ
  /-- All breakpoints lie in the open interval `(a, b)`. -/
  partition_subset : (partition : Set ℝ) ⊆ Ioo a b
  /-- `toFun` is differentiable at every point of `(a, b)` outside the partition. -/
  differentiable_off : ∀ t ∈ Ioo a b, t ∉ partition → DifferentiableAt ℝ toFun t
  /-- The derivative of `toFun` is continuous at every point of `(a, b)` outside the
  partition. -/
  deriv_continuous_off : ∀ t ∈ Ioo a b, t ∉ partition → ContinuousAt (deriv toFun) t

namespace PiecewiseC1PathOn

variable {a b : ℝ} {hab : a < b} {x y : E}

instance : CoeFun (PiecewiseC1PathOn a b hab x y) fun _ => ℝ → E where
  coe := PiecewiseC1PathOn.toFun

@[simp]
theorem coe_mk (toFun : ℝ → E) (source target continuous_toFun partition partition_subset
    differentiable_off deriv_continuous_off) :
    ((PiecewiseC1PathOn.mk toFun source target continuous_toFun partition partition_subset
      differentiable_off deriv_continuous_off : PiecewiseC1PathOn a b hab x y) : ℝ → E) = toFun :=
  rfl

@[simp]
theorem apply_left (γ : PiecewiseC1PathOn a b hab x y) : γ a = x := γ.source

@[simp]
theorem apply_right (γ : PiecewiseC1PathOn a b hab x y) : γ b = y := γ.target

/-- A piecewise C¹ path on `[a, b]` is closed if its endpoints coincide. -/
def IsClosed (_γ : PiecewiseC1PathOn a b hab x y) : Prop := x = y

end PiecewiseC1PathOn

/-! ## Embedding the unit-interval form

A `PiecewiseC1Path x y` (defined on `[0, 1]` via `Path.extend`) yields a
`PiecewiseC1PathOn 0 1 zero_lt_one x y` by taking `toFun = γ.toPath.extend`.
-/

namespace PiecewiseC1Path

variable {x y : E}

/-- Convert a `PiecewiseC1Path` (on `[0, 1]` via `Path`) to a free-interval
`PiecewiseC1PathOn 0 1 zero_lt_one`. -/
def toPiecewiseC1PathOn (γ : PiecewiseC1Path x y) :
    PiecewiseC1PathOn 0 1 zero_lt_one x y where
  toFun := γ.toPath.extend
  source := γ.toPath.extend_zero
  target := γ.toPath.extend_one
  continuous_toFun := γ.toPath.continuous_extend.continuousOn
  partition := γ.partition
  partition_subset := γ.partition_subset
  differentiable_off := γ.differentiable_off
  deriv_continuous_off := γ.deriv_continuous_off

@[simp]
theorem toPiecewiseC1PathOn_toFun (γ : PiecewiseC1Path x y) :
    (γ.toPiecewiseC1PathOn : ℝ → E) = γ.toPath.extend := rfl

@[simp]
theorem toPiecewiseC1PathOn_partition (γ : PiecewiseC1Path x y) :
    γ.toPiecewiseC1PathOn.partition = γ.partition := rfl

end PiecewiseC1Path
