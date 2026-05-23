/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn

/-!
# Piecewise C¹ Paths on Arbitrary Intervals

This file defines `PiecewiseC1PathOn a b hab x y`, the free-interval form of a
piecewise C¹ path. The unit-interval form `PiecewiseC1Path` (defined in
`PiecewiseC1Path.lean`) is built on top of this by extending and bundling a
mathlib `Path x y`.

## Main definitions

* `PiecewiseC1PathOn a b hab x y` — a continuous function `ℝ → E` with `f a = x`,
  `f b = y`, continuous on `[a, b]`, that is `C¹` away from a finite set of breakpoints
  in `(a, b)`. The partition lives in the open interval `Ioo a b`.

## Design notes

This file deliberately does not depend on `Mathlib.Topology.Path`. The unit-interval
form `PiecewiseC1Path` extends this structure and adds a bundled `Path x y` together
with an equality witness `toPath.extend t = toFun t` on `Icc 0 1`.

We do not require the underlying carrier to be a mathlib `Path` because `Path` is
fixed to `[0, 1]` via `unitInterval`. A free-interval generalization needs a raw
`ℝ → E` with continuity on `Icc a b`.

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

end PiecewiseC1PathOn

/-! ### Concatenation of adjacent piecewise C¹ paths -/

namespace PiecewiseC1PathOn

variable {a b c : ℝ} {x y z : E}

/-- The underlying piecewise function used to concatenate two adjacent paths. -/
private noncomputable def concatFun (γ₁ : ℝ → E) (γ₂ : ℝ → E) (b : ℝ) : ℝ → E :=
  fun t => if t ≤ b then γ₁ t else γ₂ t

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma concatFun_of_le {γ₁ γ₂ : ℝ → E} {b t : ℝ} (h : t ≤ b) :
    concatFun γ₁ γ₂ b t = γ₁ t := if_pos h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private lemma concatFun_of_lt {γ₁ γ₂ : ℝ → E} {b t : ℝ} (h : b < t) :
    concatFun γ₁ γ₂ b t = γ₂ t := if_neg (not_le.mpr h)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- For `t < b`, `concatFun γ₁ γ₂ b` agrees with `γ₁` on the open neighborhood
`Iio b` of `t`. -/
private lemma concatFun_eventuallyEq_left {γ₁ γ₂ : ℝ → E} {b t : ℝ} (h : t < b) :
    concatFun γ₁ γ₂ b =ᶠ[𝓝 t] γ₁ := by
  filter_upwards [Iio_mem_nhds h] with s hs
  exact concatFun_of_le hs.le

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- For `b < t`, `concatFun γ₁ γ₂ b` agrees with `γ₂` on the open neighborhood
`Ioi b` of `t`. -/
private lemma concatFun_eventuallyEq_right {γ₁ γ₂ : ℝ → E} {b t : ℝ} (h : b < t) :
    concatFun γ₁ γ₂ b =ᶠ[𝓝 t] γ₂ := by
  filter_upwards [Ioi_mem_nhds h] with s hs
  exact concatFun_of_lt hs

/-- Concatenate two piecewise C¹ paths sharing endpoint `y` at parameter `b`:
the first path is used on `[a, b]` and the second on `[b, c]`. The shared parameter
`b` becomes a (possibly removable) breakpoint of the result. -/
noncomputable def concat {a b c : ℝ} {x y z : E}
    (hab : a < b) (hbc : b < c)
    (γ₁ : PiecewiseC1PathOn a b hab x y)
    (γ₂ : PiecewiseC1PathOn b c hbc y z) :
    PiecewiseC1PathOn a c (lt_trans hab hbc) x z where
  toFun := concatFun γ₁.toFun γ₂.toFun b
  source := by
    show concatFun γ₁.toFun γ₂.toFun b a = x
    rw [concatFun_of_le hab.le, γ₁.source]
  target := by
    show concatFun γ₁.toFun γ₂.toFun b c = z
    rw [concatFun_of_lt hbc, γ₂.target]
  continuous_toFun := by
    -- Continuity on `Icc a c` via piecewise gluing on `Icc a b` ∪ `Icc b c`.
    have hsplit : Icc a c = Icc a b ∪ Icc b c := (Icc_union_Icc_eq_Icc hab.le hbc.le).symm
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · -- Continuity on `Icc a b`: function equals `γ₁` there.
      refine γ₁.continuous_toFun.congr ?_
      intro t ht
      exact concatFun_of_le ht.2
    · -- Continuity on `Icc b c`: function equals `γ₂` except possibly at `t = b`,
      -- where both expressions equal `y`.
      refine γ₂.continuous_toFun.congr ?_
      intro t ht
      rcases eq_or_lt_of_le ht.1 with hb | hb
      · -- t = b: concatFun reduces to γ₁ b = y = γ₂ b.
        subst hb
        rw [concatFun_of_le le_rfl, γ₁.target]
        exact γ₂.source.symm
      · -- b < t, so we take the right branch
        exact concatFun_of_lt hb
  partition := γ₁.partition ∪ γ₂.partition ∪ {b}
  partition_subset := by
    intro t ht
    have hac : a < c := lt_trans hab hbc
    simp only [Finset.coe_union, Finset.coe_singleton, mem_union, Finset.mem_coe,
      Set.mem_singleton_iff] at ht
    rcases ht with ((h₁ | h₂) | hb)
    · -- t ∈ γ₁.partition ⊆ Ioo a b
      have := γ₁.partition_subset h₁
      exact ⟨this.1, lt_trans this.2 hbc⟩
    · -- t ∈ γ₂.partition ⊆ Ioo b c
      have := γ₂.partition_subset h₂
      exact ⟨lt_trans hab this.1, this.2⟩
    · -- t = b
      subst hb
      exact ⟨hab, hbc⟩
  differentiable_off := by
    intro t ht htP
    -- t is in (a, c) and not in γ₁.partition ∪ γ₂.partition ∪ {b}.
    have htb : t ≠ b := by
      intro heq
      apply htP
      simp [heq]
    have ht₁ : t ∉ γ₁.partition := by
      intro h
      apply htP
      simp [h]
    have ht₂ : t ∉ γ₂.partition := by
      intro h
      apply htP
      simp [h]
    rcases lt_or_gt_of_ne htb with hlt | hgt
    · -- t < b: use γ₁'s differentiability and the local equality with γ₁.
      have htIoo : t ∈ Ioo a b := ⟨ht.1, hlt⟩
      have := γ₁.differentiable_off t htIoo ht₁
      exact this.congr_of_eventuallyEq (concatFun_eventuallyEq_left hlt)
    · -- b < t: use γ₂'s differentiability and local equality with γ₂.
      have htIoo : t ∈ Ioo b c := ⟨hgt, ht.2⟩
      have := γ₂.differentiable_off t htIoo ht₂
      exact this.congr_of_eventuallyEq (concatFun_eventuallyEq_right hgt)
  deriv_continuous_off := by
    intro t ht htP
    have htb : t ≠ b := by
      intro heq
      apply htP
      simp [heq]
    have ht₁ : t ∉ γ₁.partition := by
      intro h
      apply htP
      simp [h]
    have ht₂ : t ∉ γ₂.partition := by
      intro h
      apply htP
      simp [h]
    rcases lt_or_gt_of_ne htb with hlt | hgt
    · -- t < b: derivatives agree near t with γ₁'s derivative.
      have htIoo : t ∈ Ioo a b := ⟨ht.1, hlt⟩
      have hderiv : ContinuousAt (deriv γ₁.toFun) t :=
        γ₁.deriv_continuous_off t htIoo ht₁
      have heq : deriv (concatFun γ₁.toFun γ₂.toFun b) =ᶠ[𝓝 t] deriv γ₁.toFun :=
        (concatFun_eventuallyEq_left hlt).deriv
      exact hderiv.congr_of_eventuallyEq heq
    · -- b < t: derivatives agree near t with γ₂'s derivative.
      have htIoo : t ∈ Ioo b c := ⟨hgt, ht.2⟩
      have hderiv : ContinuousAt (deriv γ₂.toFun) t :=
        γ₂.deriv_continuous_off t htIoo ht₂
      have heq : deriv (concatFun γ₁.toFun γ₂.toFun b) =ᶠ[𝓝 t] deriv γ₂.toFun :=
        (concatFun_eventuallyEq_right hgt).deriv
      exact hderiv.congr_of_eventuallyEq heq

end PiecewiseC1PathOn

end
