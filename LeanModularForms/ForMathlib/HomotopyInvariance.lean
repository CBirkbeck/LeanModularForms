/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedWindingNumber
import LeanModularForms.ForMathlib.PoincareBridge

/-!
# Homotopy Invariance of Contour Integrals

This file defines piecewise homotopies between piecewise C^1 paths and proves
homotopy invariance of contour integrals in settings where a holomorphic primitive
exists (e.g., convex domains).

## Main definitions

* `PiecewiseHomotopy γ₁ γ₂ U` -- a continuous homotopy between piecewise C^1 paths
  `γ₁` and `γ₂` with image in `U`, fixing endpoints.

## Main results

* `contourIntegral_eq_of_hasPrimitive` -- if `f` has a primitive on `U` and both paths
  have image in `U`, then the contour integrals of `f` along `γ₁` and `γ₂` are equal.

* `contourIntegral_eq_of_homotopy` -- homotopy invariance: if `f` is holomorphic on a
  convex open set `U` and `γ₁`, `γ₂` are homotopic within `U`, then their contour
  integrals agree.

* `contourIntegral_eq_zero_of_nullHomotopic` -- if a closed path is null-homotopic
  in a convex domain of holomorphy, its contour integral vanishes.

## Design notes

The main homotopy invariance theorem for contour integrals of holomorphic functions on
general (non-convex) domains requires showing the integral is continuous in the homotopy
parameter and integer-valued, hence constant. That proof is 600+ lines and lives in
`GeneralizedResidueTheory/Homotopy/Invariance.lean`.

Here we provide a clean API for the convex case using the primitive/FTC approach from
`PoincareBridge.lean`. This suffices for many applications and avoids the heavy machinery.

## References

* R. B. Ash, W. P. Novinger, *Complex Variables*, Chapter 2
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

variable {x y : ℂ}

/-! ### PiecewiseHomotopy -/

/-- A homotopy between two piecewise C^1 paths within a set `U`.

The homotopy `H : [0,1] x [0,1] -> E` is continuous, interpolates between `γ₁`
(at `s = 0`) and `γ₂` (at `s = 1`), fixes the endpoints `x` and `y`, and has
image contained in `U`. -/
structure PiecewiseHomotopy (γ₁ γ₂ : PiecewiseC1Path x y) (U : Set ℂ) where
  /-- The homotopy map `(t, s) ↦ H(t, s)`. -/
  toFun : ℝ × ℝ → ℂ
  /-- The homotopy is continuous. -/
  continuous_toFun : Continuous toFun
  /-- At `s = 0`, the homotopy traces `γ₁`. -/
  map_zero : ∀ t ∈ Icc (0 : ℝ) 1, toFun (t, 0) = γ₁.toPath.extend t
  /-- At `s = 1`, the homotopy traces `γ₂`. -/
  map_one : ∀ t ∈ Icc (0 : ℝ) 1, toFun (t, 1) = γ₂.toPath.extend t
  /-- The homotopy fixes both endpoints for all `s`. -/
  endpoints_fixed : ∀ s ∈ Icc (0 : ℝ) 1, toFun (0, s) = x ∧ toFun (1, s) = y
  /-- The image of the homotopy lies in `U`. -/
  image_subset : ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, toFun p ∈ U

namespace PiecewiseHomotopy

variable {γ₁ γ₂ : PiecewiseC1Path x y} {U : Set ℂ}

/-- The image of γ₁ lies in U. -/
theorem image_γ₁_subset (H : PiecewiseHomotopy γ₁ γ₂ U) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ₁ t ∈ U := by
  intro t ht
  have hmem : (t, (0 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨ht, left_mem_Icc.mpr zero_le_one⟩
  show γ₁.toPath.extend t ∈ U
  rw [← H.map_zero t ht]
  exact H.image_subset (t, 0) hmem

/-- The image of γ₂ lies in U. -/
theorem image_γ₂_subset (H : PiecewiseHomotopy γ₁ γ₂ U) :
    ∀ t ∈ Icc (0 : ℝ) 1, γ₂ t ∈ U := by
  intro t ht
  have hmem : (t, (1 : ℝ)) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 :=
    ⟨ht, right_mem_Icc.mpr zero_le_one⟩
  show γ₂.toPath.extend t ∈ U
  rw [← H.map_one t ht]
  exact H.image_subset (t, 1) hmem

end PiecewiseHomotopy

/-! ### Homotopy invariance via primitives -/

/-- **Homotopy invariance of contour integrals via primitives.**

If `f` has a holomorphic primitive `F` on `U` (i.e., `HasDerivAt F (f z) z` for all `z ∈ U`),
and both paths have image in `U`, then the contour integrals of `f` along `γ₁` and `γ₂`
are equal. This does not require the paths to be homotopic -- only that both lie in the domain
where a primitive exists.

The proof uses FTC: `∮_γ f = F(y) - F(x)` for any path in the domain of `F`. -/
theorem contourIntegral_eq_of_hasPrimitive {f F : ℂ → ℂ} {U : Set ℂ}
    (γ₁ γ₂ : PiecewiseC1Path x y)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (hγ₁ : ∀ t ∈ Icc (0 : ℝ) 1, γ₁ t ∈ U)
    (hγ₂ : ∀ t ∈ Icc (0 : ℝ) 1, γ₂ t ∈ U)
    (h_int₁ : IntervalIntegrable
      (fun t => f (γ₁ t) * deriv γ₁.toPath.extend t) volume 0 1)
    (h_int₂ : IntervalIntegrable
      (fun t => f (γ₂ t) * deriv γ₂.toPath.extend t) volume 0 1) :
    γ₁.contourIntegral f = γ₂.contourIntegral f := by
  rw [γ₁.contourIntegral_eq_sub_of_hasDerivAt hγ₁ hF h_int₁,
      γ₂.contourIntegral_eq_sub_of_hasDerivAt hγ₂ hF h_int₂]

/-- **Homotopy invariance on convex domains.**

If `f` is holomorphic on a convex open set `U` and `γ₁`, `γ₂` are piecewise C^1 paths
(with the same endpoints) that are homotopic within `U`, then the contour integrals of `f`
along `γ₁` and `γ₂` are equal.

The proof constructs a primitive via `DifferentiableOn.hasPrimitive_of_convex` and applies
FTC to both paths. -/
theorem contourIntegral_eq_of_homotopy {f : ℂ → ℂ} {U : Set ℂ}
    {γ₁ γ₂ : PiecewiseC1Path x y}
    (H : PiecewiseHomotopy γ₁ γ₂ U)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (hUne : U.Nonempty)
    (h_int₁ : IntervalIntegrable
      (fun t => f (γ₁ t) * deriv γ₁.toPath.extend t) volume 0 1)
    (h_int₂ : IntervalIntegrable
      (fun t => f (γ₂ t) * deriv γ₂.toPath.extend t) volume 0 1) :
    γ₁.contourIntegral f = γ₂.contourIntegral f := by
  obtain ⟨F, hF⟩ := hf.hasPrimitive_of_convex hU hUo hUne
  exact contourIntegral_eq_of_hasPrimitive γ₁ γ₂ hF
    (H.image_γ₁_subset) (H.image_γ₂_subset) h_int₁ h_int₂

/-! ### Null-homotopic paths -/

/-- A closed piecewise C^1 path is null-homotopic in `U` if there exists a homotopy to
the constant path at `x`, within `U`. -/
def IsNullHomotopic (γ : PiecewiseC1Path x x) (U : Set ℂ) : Prop :=
  ∃ (γ_const : PiecewiseC1Path x x), (∀ t, γ_const t = x) ∧
    Nonempty (PiecewiseHomotopy γ γ_const U)

/-- **Cauchy's theorem for null-homotopic paths in convex domains.**

If a closed piecewise C^1 path is null-homotopic in a convex open set `U` where `f` is
holomorphic, then the contour integral of `f` along the path vanishes.

The proof uses the primitive/FTC approach: in a convex domain, `f` has a primitive `F`,
and FTC gives `∮_γ f = F(x) - F(x) = 0`. -/
theorem contourIntegral_eq_zero_of_nullHomotopic {f : ℂ → ℂ} {U : Set ℂ}
    (γ : PiecewiseC1Path x x)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (hUne : U.Nonempty)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 :=
  γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU hUo hUne hf hγ h_int

/-- **Contour integral of a closed path in a convex domain vanishes.**

This is a direct consequence of having a primitive in a convex domain, without requiring
an explicit null-homotopy witness. Every closed path in a simply-connected (hence convex)
domain is null-homotopic, so the integral vanishes. -/
theorem contourIntegral_eq_zero_of_closed_in_convex {f : ℂ → ℂ} {U : Set ℂ}
    (γ : PiecewiseC1Path x x)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (hUne : U.Nonempty)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f = 0 :=
  γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU hUo hUne hf hγ h_int

/-! ### Reflexivity and symmetry of PiecewiseHomotopy -/

/-- Every path is homotopic to itself (reflexivity). -/
def PiecewiseHomotopy.refl (γ : PiecewiseC1Path x y) (U : Set ℂ)
    (hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U) : PiecewiseHomotopy γ γ U where
  toFun p := γ.toPath.extend p.1
  continuous_toFun := γ.toPath.continuous_extend.comp continuous_fst
  map_zero _ _ := rfl
  map_one _ _ := rfl
  endpoints_fixed _ _ := ⟨γ.apply_zero, γ.apply_one⟩
  image_subset p hp := hγ p.1 hp.1

/-- Homotopy is symmetric: if γ₁ is homotopic to γ₂, then γ₂ is homotopic to γ₁. -/
def PiecewiseHomotopy.symm {γ₁ γ₂ : PiecewiseC1Path x y} {U : Set ℂ}
    (H : PiecewiseHomotopy γ₁ γ₂ U) : PiecewiseHomotopy γ₂ γ₁ U where
  toFun p := H.toFun (p.1, 1 - p.2)
  continuous_toFun := H.continuous_toFun.comp
    (continuous_fst.prodMk (continuous_const.sub continuous_snd))
  map_zero t ht := by simp [H.map_one t ht]
  map_one t ht := by simp [H.map_zero t ht]
  endpoints_fixed s hs := by
    have hs' : 1 - s ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact H.endpoints_fixed (1 - s) hs'
  image_subset p hp := by
    have hs' : 1 - p.2 ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hp.2.2], by linarith [hp.2.1]⟩
    exact H.image_subset (p.1, 1 - p.2) ⟨hp.1, hs'⟩

/-! ### Homotopy invariance for holomorphic integrands with primitives

The following theorem is the most general version available in the convex setting.
It shows that if `f` is holomorphic on a convex open set `U` and both paths lie in `U`,
then the contour integrals agree -- regardless of whether a homotopy is given. -/

/-- If `f` is holomorphic on a convex open set and both paths have image in that set,
their contour integrals agree. This is stronger than homotopy invariance in the convex case
because no homotopy witness is needed. -/
theorem contourIntegral_eq_of_paths_in_convex {f : ℂ → ℂ} {U : Set ℂ}
    (γ₁ γ₂ : PiecewiseC1Path x y)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (hUne : U.Nonempty)
    (hγ₁ : ∀ t ∈ Icc (0 : ℝ) 1, γ₁ t ∈ U)
    (hγ₂ : ∀ t ∈ Icc (0 : ℝ) 1, γ₂ t ∈ U)
    (h_int₁ : IntervalIntegrable
      (fun t => f (γ₁ t) * deriv γ₁.toPath.extend t) volume 0 1)
    (h_int₂ : IntervalIntegrable
      (fun t => f (γ₂ t) * deriv γ₂.toPath.extend t) volume 0 1) :
    γ₁.contourIntegral f = γ₂.contourIntegral f := by
  obtain ⟨F, hF⟩ := hf.hasPrimitive_of_convex hU hUo hUne
  exact contourIntegral_eq_of_hasPrimitive γ₁ γ₂ hF hγ₁ hγ₂ h_int₁ h_int₂

/-- For closed paths: if two closed paths lie in a convex domain of holomorphy, the
difference of their contour integrals is zero. -/
theorem contourIntegral_sub_eq_zero_of_paths_in_convex {f : ℂ → ℂ} {U : Set ℂ}
    (γ₁ γ₂ : PiecewiseC1Path x y)
    (hf : DifferentiableOn ℂ f U) (hU : Convex ℝ U) (hUo : IsOpen U)
    (hUne : U.Nonempty)
    (hγ₁ : ∀ t ∈ Icc (0 : ℝ) 1, γ₁ t ∈ U)
    (hγ₂ : ∀ t ∈ Icc (0 : ℝ) 1, γ₂ t ∈ U)
    (h_int₁ : IntervalIntegrable
      (fun t => f (γ₁ t) * deriv γ₁.toPath.extend t) volume 0 1)
    (h_int₂ : IntervalIntegrable
      (fun t => f (γ₂ t) * deriv γ₂.toPath.extend t) volume 0 1) :
    γ₁.contourIntegral f - γ₂.contourIntegral f = 0 := by
  rw [sub_eq_zero]
  exact contourIntegral_eq_of_paths_in_convex γ₁ γ₂ hf hU hUo hUne hγ₁ hγ₂ h_int₁ h_int₂

end
