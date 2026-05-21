/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

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

* `PiecewiseC1PathOn.reparamUnit` — affine reparametrization `[a, b] → [0, 1]` via
  `t ↦ γ ((b - a) * t + a)`. The chain rule applies because the off-partition set
  is open and the affine map is smooth.

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

/-! ## Affine reparametrization between free intervals and `[0, 1]`

Given `γ : PiecewiseC1PathOn a b hab x y`, the affine map `t ↦ (b - a) * t + a`
sends `[0, 1]` onto `[a, b]`. Composing `γ.toFun` with this map yields a path on
`[0, 1]`. The chain rule for the derivative requires a local-neighborhood argument
because `γ.differentiable_off` only gives pointwise differentiability — but the
off-partition set is open, so on a neighborhood of any off-partition point the
composition is differentiable everywhere and `deriv_comp` applies.
-/

namespace PiecewiseC1PathOn

variable {a b : ℝ} {hab : a < b} {x y : E}

/-- The affine map sending `[0, 1]` onto `[a, b]`. Used by `reparamUnit`. -/
private def affineToFree (a b : ℝ) : ℝ → ℝ := fun t => (b - a) * t + a

private theorem affineToFree_zero (a b : ℝ) : affineToFree a b 0 = a := by
  simp [affineToFree]

private theorem affineToFree_one (a b : ℝ) : affineToFree a b 1 = b := by
  simp [affineToFree]

private theorem continuous_affineToFree (a b : ℝ) : Continuous (affineToFree a b) := by
  unfold affineToFree; fun_prop

private theorem affineToFree_mapsTo_Icc (a b : ℝ) (hab : a < b) :
    MapsTo (affineToFree a b) (Icc 0 1) (Icc a b) := by
  intro t ht
  simp only [affineToFree, mem_Icc] at ht ⊢
  have hba : 0 ≤ b - a := by linarith
  refine ⟨?_, ?_⟩
  · nlinarith [ht.1]
  · nlinarith [ht.2]

private theorem affineToFree_mapsTo_Ioo (a b : ℝ) (hab : a < b) :
    MapsTo (affineToFree a b) (Ioo 0 1) (Ioo a b) := by
  intro t ht
  simp only [affineToFree, mem_Ioo] at ht ⊢
  have hba : 0 < b - a := by linarith
  refine ⟨?_, ?_⟩
  · nlinarith [ht.1]
  · nlinarith [ht.2]

private theorem hasDerivAt_affineToFree (a b t : ℝ) :
    HasDerivAt (affineToFree a b) (b - a) t := by
  unfold affineToFree
  have h1 : HasDerivAt (fun u : ℝ => (b - a) * u) ((b - a) * 1) t :=
    HasDerivAt.const_mul (b - a) (hasDerivAt_id t)
  have h2 : HasDerivAt (fun u : ℝ => (b - a) * u + a) ((b - a) * 1) t := h1.add_const a
  simpa using h2

private theorem differentiableAt_affineToFree (a b t : ℝ) :
    DifferentiableAt ℝ (affineToFree a b) t :=
  (hasDerivAt_affineToFree a b t).differentiableAt

private theorem deriv_affineToFree (a b t : ℝ) :
    deriv (affineToFree a b) t = b - a :=
  (hasDerivAt_affineToFree a b t).deriv

private theorem partition_image_back (γ : PiecewiseC1PathOn a b hab x y) (t : ℝ)
    (h_in_part : affineToFree a b t ∈ γ.partition) :
    t ∈ γ.partition.image (fun s => (s - a) / (b - a)) := by
  simp only [Finset.mem_image]
  refine ⟨affineToFree a b t, h_in_part, ?_⟩
  simp only [affineToFree]
  have hba_ne : b - a ≠ 0 := by linarith
  field_simp
  ring

/-- Affine reparametrization of a free-interval path to `[0, 1]`.

The new path on `[0, 1]` has `toFun t = γ.toFun ((b - a) * t + a)`. The breakpoints
are pulled back: each `s ∈ γ.partition` maps to `(s - a) / (b - a) ∈ Ioo 0 1`. -/
def reparamUnit (γ : PiecewiseC1PathOn a b hab x y) :
    PiecewiseC1PathOn 0 1 zero_lt_one x y where
  toFun t := γ.toFun (affineToFree a b t)
  source := by
    show γ.toFun (affineToFree a b 0) = x
    rw [affineToFree_zero]; exact γ.source
  target := by
    show γ.toFun (affineToFree a b 1) = y
    rw [affineToFree_one]; exact γ.target
  continuous_toFun :=
    γ.continuous_toFun.comp (continuous_affineToFree a b).continuousOn
      (affineToFree_mapsTo_Icc a b hab)
  partition := γ.partition.image (fun s => (s - a) / (b - a))
  partition_subset := by
    intro t ht
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at ht
    obtain ⟨s, hs_mem, hst⟩ := ht
    have hs_in_Ioo := γ.partition_subset hs_mem
    simp only [mem_Ioo] at hs_in_Ioo
    have hba : 0 < b - a := by linarith
    subst hst
    simp only [mem_Ioo]
    refine ⟨?_, ?_⟩
    · exact div_pos (sub_pos.mpr hs_in_Ioo.1) hba
    · rw [div_lt_one hba]; linarith [hs_in_Ioo.2]
  differentiable_off := by
    intro t ht htn
    have h_aff_t_in_Ioo : affineToFree a b t ∈ Ioo a b := affineToFree_mapsTo_Ioo a b hab ht
    have h_aff_t_notin : affineToFree a b t ∉ γ.partition := by
      intro h; exact htn (partition_image_back γ t h)
    have h_at_g : HasDerivAt γ.toFun (deriv γ.toFun (affineToFree a b t)) (affineToFree a b t) :=
      (γ.differentiable_off (affineToFree a b t) h_aff_t_in_Ioo h_aff_t_notin).hasDerivAt
    exact (HasDerivAt.scomp t h_at_g (hasDerivAt_affineToFree a b t)).differentiableAt
  deriv_continuous_off := by
    intro t ht htn
    have h_aff_t_in_Ioo : affineToFree a b t ∈ Ioo a b := affineToFree_mapsTo_Ioo a b hab ht
    have h_aff_t_notin : affineToFree a b t ∉ γ.partition := by
      intro h; exact htn (partition_image_back γ t h)
    -- The off-partition set is open: Ioo a b minus a finite set.
    have h_open_set : IsOpen ((Ioo a b : Set ℝ) \ ↑γ.partition) :=
      isOpen_Ioo.sdiff γ.partition.finite_toSet.isClosed
    -- The preimage of this open set under the continuous affine map is also open.
    have h_pre_open : IsOpen (affineToFree a b ⁻¹' ((Ioo a b : Set ℝ) \ ↑γ.partition)) :=
      h_open_set.preimage (continuous_affineToFree a b)
    have h_t_in_pre : t ∈ affineToFree a b ⁻¹' ((Ioo a b : Set ℝ) \ ↑γ.partition) :=
      ⟨h_aff_t_in_Ioo, h_aff_t_notin⟩
    -- On the open preimage, `deriv (γ ∘ affineToFree) s = (b - a) * deriv γ (affineToFree s)`.
    have h_deriv_eq : ∀ s ∈ affineToFree a b ⁻¹' ((Ioo a b : Set ℝ) \ ↑γ.partition),
        deriv (fun u => γ.toFun (affineToFree a b u)) s
          = (b - a) • deriv γ.toFun (affineToFree a b s) := by
      intro s hs
      have h_at_g : HasDerivAt γ.toFun (deriv γ.toFun (affineToFree a b s)) (affineToFree a b s) :=
        (γ.differentiable_off (affineToFree a b s) hs.1 hs.2).hasDerivAt
      exact (HasDerivAt.scomp s h_at_g (hasDerivAt_affineToFree a b s)).deriv
    -- Derivatives agree eventually in a neighborhood of `t`.
    have h_eventually : deriv (fun u => γ.toFun (affineToFree a b u)) =ᶠ[𝓝 t]
        (fun s => (b - a) • deriv γ.toFun (affineToFree a b s)) := by
      filter_upwards [h_pre_open.mem_nhds h_t_in_pre] with s hs using h_deriv_eq s hs
    -- The RHS is continuous at `t`, since `deriv γ` is continuous off the partition and the
    -- affine map is continuous, and we multiply by a constant.
    have h_rhs_cont : ContinuousAt (fun s => (b - a) • deriv γ.toFun (affineToFree a b s)) t :=
      ((γ.deriv_continuous_off (affineToFree a b t) h_aff_t_in_Ioo h_aff_t_notin).comp
        (continuous_affineToFree a b).continuousAt).const_smul (b - a)
    exact h_rhs_cont.congr h_eventually.symm

/-! ### Inverse direction: `reparamFree`

Given a path on `[0, 1]`, embed it onto a free interval `[a, b]` via the inverse
affine map `s ↦ (s - a) / (b - a)`.
-/

/-- The affine map sending `[a, b]` onto `[0, 1]`. Inverse of `affineToFree`. -/
private def affineToUnit (a b : ℝ) : ℝ → ℝ := fun s => (s - a) / (b - a)

private theorem affineToUnit_left (a b : ℝ) : affineToUnit a b a = 0 := by
  simp [affineToUnit]

private theorem affineToUnit_right (a b : ℝ) (hab : a < b) : affineToUnit a b b = 1 := by
  have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  unfold affineToUnit
  exact div_self hba_ne

private theorem continuous_affineToUnit (a b : ℝ) (hab : a < b) : Continuous (affineToUnit a b) := by
  unfold affineToUnit
  have hba_ne : b - a ≠ 0 := by linarith
  fun_prop

private theorem affineToUnit_mapsTo_Icc (a b : ℝ) (hab : a < b) :
    MapsTo (affineToUnit a b) (Icc a b) (Icc 0 1) := by
  intro s hs
  simp only [affineToUnit, mem_Icc] at hs ⊢
  have hba : 0 < b - a := by linarith
  refine ⟨div_nonneg (by linarith [hs.1]) hba.le, ?_⟩
  rw [div_le_one hba]; linarith [hs.2]

private theorem affineToUnit_mapsTo_Ioo (a b : ℝ) (_hab : a < b) :
    MapsTo (affineToUnit a b) (Ioo a b) (Ioo 0 1) := by
  intro s hs
  simp only [affineToUnit, mem_Ioo] at hs ⊢
  have hba : 0 < b - a := by linarith
  refine ⟨div_pos (by linarith [hs.1]) hba, ?_⟩
  rw [div_lt_one hba]; linarith [hs.2]

private theorem hasDerivAt_affineToUnit (a b : ℝ) (hab : a < b) (s : ℝ) :
    HasDerivAt (affineToUnit a b) ((b - a)⁻¹) s := by
  unfold affineToUnit
  have hba_ne : b - a ≠ 0 := by linarith
  have h_sub : HasDerivAt (fun u => u - a) (1 : ℝ) s :=
    (hasDerivAt_id s).sub_const a
  have h : HasDerivAt (fun u => (u - a) / (b - a)) ((1 : ℝ) / (b - a)) s :=
    h_sub.div_const (b - a)
  simpa [one_div] using h

private theorem deriv_affineToUnit (a b : ℝ) (hab : a < b) (s : ℝ) :
    deriv (affineToUnit a b) s = (b - a)⁻¹ :=
  (hasDerivAt_affineToUnit a b hab s).deriv

private theorem partition_image_back_unit {a b : ℝ} (hab : a < b)
    {x y : E} (γ : PiecewiseC1PathOn 0 1 zero_lt_one x y) (s : ℝ)
    (h_in_part : affineToUnit a b s ∈ γ.partition) :
    s ∈ γ.partition.image (fun t => a + t * (b - a)) := by
  simp only [Finset.mem_image]
  refine ⟨affineToUnit a b s, h_in_part, ?_⟩
  show a + affineToUnit a b s * (b - a) = s
  unfold affineToUnit
  have hba_ne : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  rw [div_mul_cancel₀ _ hba_ne]; ring

/-- Affine reparametrization of a `[0, 1]` path onto a free interval `[a, b]`.

The new path on `[a, b]` has `toFun s = γ.toFun ((s - a) / (b - a))`. The breakpoints
are pulled back: each `t ∈ γ.partition` (with `t ∈ Ioo 0 1`) maps to
`a + t * (b - a) ∈ Ioo a b`. -/
def reparamFree (a b : ℝ) (hab : a < b) {x y : E}
    (γ : PiecewiseC1PathOn 0 1 zero_lt_one x y) :
    PiecewiseC1PathOn a b hab x y where
  toFun s := γ.toFun (affineToUnit a b s)
  source := by
    show γ.toFun (affineToUnit a b a) = x
    rw [affineToUnit_left a b]; exact γ.source
  target := by
    show γ.toFun (affineToUnit a b b) = y
    rw [affineToUnit_right a b hab]; exact γ.target
  continuous_toFun :=
    γ.continuous_toFun.comp (continuous_affineToUnit a b hab).continuousOn
      (affineToUnit_mapsTo_Icc a b hab)
  partition := γ.partition.image (fun t => a + t * (b - a))
  partition_subset := by
    intro s hs
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hs
    obtain ⟨t, ht_mem, hts⟩ := hs
    have ht_in_Ioo := γ.partition_subset ht_mem
    simp only [mem_Ioo] at ht_in_Ioo
    have hba : 0 < b - a := by linarith
    subst hts
    simp only [mem_Ioo]
    refine ⟨?_, ?_⟩
    · nlinarith [ht_in_Ioo.1]
    · nlinarith [ht_in_Ioo.2]
  differentiable_off := by
    intro s hs hsn
    have h_aff_s_in_Ioo : affineToUnit a b s ∈ Ioo 0 1 := affineToUnit_mapsTo_Ioo a b hab hs
    have h_aff_s_notin : affineToUnit a b s ∉ γ.partition := by
      intro h; exact hsn (partition_image_back_unit hab γ s h)
    have h_at_g : HasDerivAt γ.toFun (deriv γ.toFun (affineToUnit a b s)) (affineToUnit a b s) :=
      (γ.differentiable_off (affineToUnit a b s) h_aff_s_in_Ioo h_aff_s_notin).hasDerivAt
    exact (HasDerivAt.scomp s h_at_g (hasDerivAt_affineToUnit a b hab s)).differentiableAt
  deriv_continuous_off := by
    intro s hs hsn
    have h_aff_s_in_Ioo : affineToUnit a b s ∈ Ioo 0 1 := affineToUnit_mapsTo_Ioo a b hab hs
    have h_aff_s_notin : affineToUnit a b s ∉ γ.partition := by
      intro h; exact hsn (partition_image_back_unit hab γ s h)
    have h_open_set : IsOpen ((Ioo 0 1 : Set ℝ) \ ↑γ.partition) :=
      isOpen_Ioo.sdiff γ.partition.finite_toSet.isClosed
    have h_pre_open : IsOpen (affineToUnit a b ⁻¹' ((Ioo 0 1 : Set ℝ) \ ↑γ.partition)) :=
      h_open_set.preimage (continuous_affineToUnit a b hab)
    have h_s_in_pre : s ∈ affineToUnit a b ⁻¹' ((Ioo 0 1 : Set ℝ) \ ↑γ.partition) :=
      ⟨h_aff_s_in_Ioo, h_aff_s_notin⟩
    have h_deriv_eq : ∀ u ∈ affineToUnit a b ⁻¹' ((Ioo 0 1 : Set ℝ) \ ↑γ.partition),
        deriv (fun v => γ.toFun (affineToUnit a b v)) u
          = (b - a)⁻¹ • deriv γ.toFun (affineToUnit a b u) := by
      intro u hu
      have h_at_g : HasDerivAt γ.toFun (deriv γ.toFun (affineToUnit a b u)) (affineToUnit a b u) :=
        (γ.differentiable_off (affineToUnit a b u) hu.1 hu.2).hasDerivAt
      exact (HasDerivAt.scomp u h_at_g (hasDerivAt_affineToUnit a b hab u)).deriv
    have h_eventually : deriv (fun v => γ.toFun (affineToUnit a b v)) =ᶠ[𝓝 s]
        (fun u => (b - a)⁻¹ • deriv γ.toFun (affineToUnit a b u)) := by
      filter_upwards [h_pre_open.mem_nhds h_s_in_pre] with u hu using h_deriv_eq u hu
    have h_rhs_cont : ContinuousAt (fun u => (b - a)⁻¹ • deriv γ.toFun (affineToUnit a b u)) s :=
      ((γ.deriv_continuous_off (affineToUnit a b s) h_aff_s_in_Ioo h_aff_s_notin).comp
        (continuous_affineToUnit a b hab).continuousAt).const_smul ((b - a)⁻¹)
    exact h_rhs_cont.congr h_eventually.symm

end PiecewiseC1PathOn
