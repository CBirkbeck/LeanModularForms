/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1PathOn
import Mathlib.Topology.Path

/-!
# Piecewise C¹ Paths

This file defines piecewise C¹ paths in normed spaces, wrapping mathlib's `Path x y`
(parametrized on `[0,1]`) with piecewise C¹ smoothness conditions.

## Main definitions

* `PiecewiseC1Path x y` — a free-interval `PiecewiseC1PathOn 0 1 zero_lt_one x y`
  bundled with a mathlib `Path x y` whose `extend` agrees pointwise with `toFun` on
  `[0, 1]`. Differentiability and derivative continuity are inherited from the
  parent structure.

* `PwC1Immersion x y` — a `PiecewiseC1Path x y` whose derivative is nonzero away
  from partition points, with nonzero one-sided derivative limits at partition points.

* `PiecewiseC1Path.IsClosed` — predicate that a path is closed (`x = y`).

## Design notes

`PiecewiseC1Path` extends `PiecewiseC1PathOn 0 1 zero_lt_one x y` (the free-interval
form). The bundled `Path x y` is kept as an explicit field because the `Path` API is
heavily used by call sites — in particular, the coercion `γ t = γ.toPath.extend t`
must remain stable. The witness `toPath_extend_eq_toFun` ties the two forms together
on `Icc 0 1`.

The definitions are stated for a `NormedAddCommGroup E` with `NormedSpace ℝ E`, which
covers `ℂ` as the main application.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : E}

/-- A piecewise continuously differentiable path from `x` to `y` in a normed space.

This bundles a free-interval `PiecewiseC1PathOn 0 1 zero_lt_one x y` together with a
mathlib `Path x y` whose `extend` agrees with the underlying function on `[0, 1]`.
Differentiability and continuous-derivative conditions are inherited from the parent. -/
structure PiecewiseC1Path (x y : E) extends PiecewiseC1PathOn 0 1 zero_lt_one x y where
  /-- The bundled mathlib `Path x y`. Kept as a field so that `Path.extend`-based
  call sites can continue to use the `Path` API. -/
  toPath : Path x y
  /-- The extended path agrees with the underlying function on the closed unit interval. -/
  toPath_extend_eq_toFun : ∀ t ∈ Icc (0:ℝ) 1, toPath.extend t = toFun t

namespace PiecewiseC1Path

/-- The underlying function `ℝ → E` obtained by extending the path. -/
def extendedPath (γ : PiecewiseC1Path x y) : ℝ → E := γ.toPath.extend

instance : CoeFun (PiecewiseC1Path x y) fun _ => ℝ → E where
  coe := extendedPath

@[simp]
theorem extendedPath_eq (γ : PiecewiseC1Path x y) :
    γ.extendedPath = γ.toPath.extend := rfl

/-- The extended path is differentiable at every point of `(0, 1)` outside the partition.
Same statement as the inherited `differentiable_off` but phrased in terms of `toPath.extend`
instead of `toFun`. The two forms agree on `Icc 0 1` via `toPath_extend_eq_toFun`. -/
theorem differentiable_off_extend (γ : PiecewiseC1Path x y) :
    ∀ t ∈ Ioo (0:ℝ) 1, t ∉ γ.partition → DifferentiableAt ℝ γ.toPath.extend t := by
  intro t ht htp
  exact (γ.differentiable_off t ht htp).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
      fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu))

/-- The derivative of the extended path is continuous at every point of `(0, 1)` outside
the partition. Same statement as `deriv_continuous_off` but in terms of `toPath.extend`. -/
theorem deriv_continuous_off_extend (γ : PiecewiseC1Path x y) :
    ∀ t ∈ Ioo (0:ℝ) 1, t ∉ γ.partition → ContinuousAt (deriv γ.toPath.extend) t := by
  intro t ht htp
  have h_eq : γ.toPath.extend =ᶠ[𝓝 t] γ.toFun :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
      fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu)
  exact (γ.deriv_continuous_off t ht htp).congr h_eq.deriv.symm

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

omit [NormedSpace ℝ E] in
private def translatePath (γ : Path x y) (c : E) : Path (x + c) (y + c) where
  toFun t := γ t + c
  continuous_toFun := γ.continuous.add continuous_const
  source' := by simp
  target' := by simp

omit [NormedSpace ℝ E] in
private theorem translatePath_extend (γ : Path x y) (c : E) :
    (translatePath γ c).extend = fun t => γ.extend t + c := rfl

/-- Translate a piecewise C¹ path by a constant. The partition is unchanged. -/
def translate (γ : PiecewiseC1Path x y) (c : E) : PiecewiseC1Path (x + c) (y + c) where
  toFun := (translatePath γ.toPath c).extend
  source := (translatePath γ.toPath c).extend_zero
  target := (translatePath γ.toPath c).extend_one
  continuous_toFun := (translatePath γ.toPath c).continuous_extend.continuousOn
  partition := γ.partition
  partition_subset := γ.partition_subset
  differentiable_off := fun t ht htp => by
    -- Goal: `DifferentiableAt ℝ (translatePath γ.toPath c).extend t`
    -- = `DifferentiableAt ℝ (fun u => γ.toPath.extend u + c) t`
    rw [translatePath_extend]
    -- Use `γ.differentiable_off`, which gives differentiability of `γ.toFun`. Bridge to
    -- `γ.toPath.extend` via the equality on `Icc 0 1`.
    have h_eq : γ.toPath.extend =ᶠ[𝓝 t] γ.toFun :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
        fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu)
    exact ((γ.differentiable_off t ht htp).congr_of_eventuallyEq h_eq).add
      (differentiableAt_const c)
  deriv_continuous_off := fun t ht htp => by
    have h_eq : γ.toPath.extend =ᶠ[𝓝 t] γ.toFun :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
        fun u hu => γ.toPath_extend_eq_toFun u (Ioo_subset_Icc_self hu)
    have h_deriv_eq : deriv γ.toFun =ᶠ[𝓝 t] deriv (translatePath γ.toPath c).extend := by
      rw [translatePath_extend]
      have h_add : deriv (fun u => γ.toPath.extend u + c) =ᶠ[𝓝 t]
          deriv γ.toPath.extend :=
        Filter.Eventually.of_forall fun u => by rw [deriv_add_const']
      exact h_eq.symm.deriv.trans h_add.symm
    exact (γ.deriv_continuous_off t ht htp).congr h_deriv_eq
  toPath := translatePath γ.toPath c
  toPath_extend_eq_toFun := fun _ _ => rfl

end PiecewiseC1Path

/-- A piecewise C¹ immersion from `x` to `y` in a normed space.

This extends `PiecewiseC1Path x y` with the condition that the derivative is nonzero away from
partition points, and has nonzero one-sided limits at partition points. This ensures the path
has a well-defined tangent direction everywhere. -/
structure PwC1Immersion (x y : E) extends PiecewiseC1Path x y where
  /-- The derivative is nonzero at every point of `(0, 1)` outside the partition. -/
  deriv_ne_zero : ∀ t ∈ Ioo 0 1, t ∉ partition →
    deriv toPiecewiseC1Path.toPath.extend t ≠ 0
  /-- At each partition point, the left derivative limit exists and is nonzero. -/
  left_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧
    Tendsto (deriv toPiecewiseC1Path.toPath.extend) (𝓝[<] p) (𝓝 L)
  /-- At each partition point, the right derivative limit exists and is nonzero. -/
  right_deriv_limit : ∀ p ∈ partition, ∃ L : E, L ≠ 0 ∧
    Tendsto (deriv toPiecewiseC1Path.toPath.extend) (𝓝[>] p) (𝓝 L)

namespace PwC1Immersion

instance : CoeFun (PwC1Immersion x y) fun _ => ℝ → E where
  coe γ := γ.toPiecewiseC1Path.extendedPath

/-- A piecewise C¹ immersion is closed if its endpoints coincide. -/
def IsClosed (_γ : PwC1Immersion x y) : Prop := x = y

/-- The underlying extended path is continuous. -/
theorem continuous (γ : PwC1Immersion x y) : Continuous (γ : ℝ → E) :=
  γ.toPiecewiseC1Path.continuous

end PwC1Immersion

/-! ## Bridge: free-interval `[0, 1]` → unit-interval form

Given `γ : PiecewiseC1PathOn 0 1 zero_lt_one x y`, build a `Path x y` via
`Path.ofLine γ.continuous_toFun γ.source γ.target`. On any point `t ∈ Ioo 0 1`,
`Path.extend` of this path agrees with `γ.toFun` on the open neighborhood `Ioo 0 1`,
so differentiability and derivative continuity transfer via `EventuallyEq`. -/

namespace PiecewiseC1PathOn

variable {x y : E}

/-- The unit-interval `Path` underlying a free-interval path on `[0, 1]`. -/
private def toPath01 (γ : PiecewiseC1PathOn 0 1 zero_lt_one x y) : Path x y :=
  Path.ofLine γ.continuous_toFun γ.source γ.target

/-- On `Icc 0 1`, the extended path agrees pointwise with `γ.toFun`. -/
private theorem toPath01_extend_eqOn_Icc (γ : PiecewiseC1PathOn 0 1 zero_lt_one x y) :
    EqOn γ.toPath01.extend γ.toFun (Icc 0 1) := by
  intro t ht
  show (γ.toPath01).extend t = γ.toFun t
  rw [Path.extend_apply _ ht]
  rfl

/-- On the open interval `Ioo 0 1`, the extended path is eventually equal to
`γ.toFun` in any neighborhood. -/
private theorem toPath01_extend_eventuallyEq (γ : PiecewiseC1PathOn 0 1 zero_lt_one x y)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    γ.toPath01.extend =ᶠ[𝓝 t] γ.toFun :=
  eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht)
    (fun _ hu => γ.toPath01_extend_eqOn_Icc (Ioo_subset_Icc_self hu))

/-- Convert a free-interval `PiecewiseC1PathOn 0 1` to a unit-interval `PiecewiseC1Path`.
Inverse-of-restriction to `Path.ofLine` at the carrier level; differentiability and derivative
continuity transfer via the `EventuallyEq` of `Path.extend` and `γ.toFun` on `Ioo 0 1`. -/
def toPiecewiseC1Path (γ : PiecewiseC1PathOn 0 1 zero_lt_one x y) :
    PiecewiseC1Path x y where
  toPiecewiseC1PathOn := γ
  toPath := γ.toPath01
  toPath_extend_eq_toFun := fun _ ht => γ.toPath01_extend_eqOn_Icc ht

@[simp]
theorem toPiecewiseC1Path_partition (γ : PiecewiseC1PathOn 0 1 zero_lt_one x y) :
    γ.toPiecewiseC1Path.partition = γ.partition := rfl

end PiecewiseC1PathOn

end
