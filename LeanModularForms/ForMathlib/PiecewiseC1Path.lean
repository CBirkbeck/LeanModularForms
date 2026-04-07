/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Path

/-!
# Piecewise C¹ Paths

This file defines piecewise C¹ paths in normed spaces, wrapping mathlib's `Path x y`
(parametrized on `[0,1]`) with piecewise C¹ smoothness conditions.

## Main definitions

* `PiecewiseC1Path x y` — a `Path x y` that is C¹ away from finitely many breakpoints
  in `(0, 1)`. Differentiability and derivative continuity are stated in terms of
  `Path.extend`, which extends the path to all of `ℝ`.

* `PiecewiseC1Immersion x y` — a `PiecewiseC1Path x y` whose derivative is nonzero away
  from partition points, with nonzero one-sided derivative limits at partition points.

* `PiecewiseC1Path.IsClosed` — predicate that a path is closed (`x = y`).

## Design notes

We use `Path.extend` (of type `C(ℝ, X)`) for differentiability statements because `deriv`
operates on functions `ℝ → E`, while `Path` is defined on `Set.Icc 0 1`. The partition is a
`Finset ℝ` with elements in the open interval `Ioo 0 1` — the endpoints 0 and 1 are not
partition points.

The definitions are stated for a `NormedAddCommGroup E` with `NormedSpace ℝ E`, which
covers `ℂ` as the main application.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : E}

/-- A piecewise continuously differentiable path from `x` to `y` in a normed space.

The underlying `Path x y` is extended to `ℝ` via `Path.extend`, and the smoothness conditions
(differentiability and continuous derivative) hold at every point of `(0, 1)` outside a finite
set of breakpoints. -/
structure PiecewiseC1Path (x y : E) extends Path x y where
  /-- Finite set of breakpoints in the open interval `(0, 1)`. -/
  partition : Finset ℝ
  /-- All breakpoints lie in the open interval `(0, 1)`. -/
  partition_subset : ↑partition ⊆ Ioo 0 1
  /-- The extended path is differentiable at every point of `(0, 1)` outside the partition. -/
  differentiable_off : ∀ t ∈ Ioo 0 1, t ∉ partition → DifferentiableAt ℝ toPath.extend t
  /-- The derivative of the extended path is continuous at every point of `(0, 1)` outside
  the partition. -/
  deriv_continuous_off : ∀ t ∈ Ioo 0 1, t ∉ partition →
    ContinuousAt (deriv toPath.extend) t

namespace PiecewiseC1Path

/-- The underlying continuous function `ℝ → E` obtained by extending the path. -/
def toFun (γ : PiecewiseC1Path x y) : ℝ → E := γ.toPath.extend

instance : CoeFun (PiecewiseC1Path x y) fun _ => ℝ → E where
  coe := toFun

@[simp]
theorem coe_toFun (γ : PiecewiseC1Path x y) : γ.toFun = γ.toPath.extend := rfl

@[simp]
theorem apply_zero (γ : PiecewiseC1Path x y) : γ 0 = x :=
  γ.toPath.extend_zero

@[simp]
theorem apply_one (γ : PiecewiseC1Path x y) : γ 1 = y :=
  γ.toPath.extend_one

/-- A piecewise C¹ path is closed if its endpoints coincide. -/
def IsClosed (_γ : PiecewiseC1Path x y) : Prop := x = y

/-- The underlying extended path is continuous. -/
theorem continuous (γ : PiecewiseC1Path x y) : Continuous (γ : ℝ → E) :=
  γ.toPath.continuous_extend

/-- Translate a piecewise C¹ path by a constant. The partition is unchanged. -/
def translate (γ : PiecewiseC1Path x y) (c : E) : PiecewiseC1Path (x + c) (y + c) where
  toPath := {
    toContinuousMap := ⟨fun t => γ.toPath t + c,
      γ.toPath.continuous.add continuous_const⟩
    source' := by simp [γ.toPath.source]
    target' := by simp [γ.toPath.target]
  }
  partition := γ.partition
  partition_subset := γ.partition_subset
  differentiable_off := fun t ht htp => by
    have hd := γ.differentiable_off t ht htp
    show DifferentiableAt ℝ (Path.extend _) t
    sorry
  deriv_continuous_off := fun t ht htp => by
    have hc := γ.deriv_continuous_off t ht htp
    show ContinuousAt (deriv (Path.extend _)) t
    sorry

end PiecewiseC1Path

/-- A piecewise C¹ immersion from `x` to `y` in a normed space.

This extends `PiecewiseC1Path x y` with the condition that the derivative is nonzero away from
partition points, and has nonzero one-sided limits at partition points. This ensures the path
has a well-defined tangent direction everywhere. -/
structure PiecewiseC1Immersion (x y : E) extends PiecewiseC1Path x y where
  /-- The derivative is nonzero at every point of `(0, 1)` outside the partition. -/
  deriv_ne_zero : ∀ t ∈ Ioo 0 1, t ∉ partition →
    deriv toPiecewiseC1Path.toPath.extend t ≠ 0
  /-- At each partition point, the left derivative limit exists and is nonzero. -/
  left_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧
    Tendsto (deriv toPiecewiseC1Path.toPath.extend) (𝓝[<] p) (𝓝 L)
  /-- At each partition point, the right derivative limit exists and is nonzero. -/
  right_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧
    Tendsto (deriv toPiecewiseC1Path.toPath.extend) (𝓝[>] p) (𝓝 L)

namespace PiecewiseC1Immersion

instance : CoeFun (PiecewiseC1Immersion x y) fun _ => ℝ → E where
  coe γ := γ.toPiecewiseC1Path.toFun

/-- A piecewise C¹ immersion is closed if its endpoints coincide. -/
def IsClosed (_γ : PiecewiseC1Immersion x y) : Prop := x = y

end PiecewiseC1Immersion

end
