/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Convex.Star

/-!
# Affine segments for piecewise-linear contours

Shared machinery for `RectangularContour.lean` and `TriangleContour.lean`. A
piecewise-linear contour parameterised on `[0, 1]` with breakpoints at the
fractions `k/r` traverses, on its `k`-th piece `[k/r, (k+1)/r]`, the segment

* `affineSegment r k p q : ℝ → E`, `t ↦ p + (r·t - k) • (q - p)`,

starting at `p` (at `t = k/r`), ending at `q` (at `t = (k+1)/r`), with constant
velocity `r • (q - p)`. This file provides the segment's calculus and, for any
function `γ` agreeing with the segment on a piece (the `…_of_eqOn` lemmas,
applied to `Path.extend`-style parametrisations):

* `affineSegment_contDiffOn_of_eqOn`, `affineSegment_derivWithin_of_eqOn` — the
  `C¹`-and-derivative data required by `ClosedPwC1Immersion`;
* `affineSegment_integrand_intervalIntegrable_of_eqOn` — integrability of the
  contour integrand `t ↦ f (γ t) * deriv γ t` on the piece;
* `affineSegment_integral_eq_of_eqOn` — the affine change of variables turning
  the piece integral into `∫ s in 0..1, f (p + s • (q - p)) * (q - p)`.

The two-piece gluing `ifLE τ f g` (use `f` on `(-∞, τ]`, `g` beyond) comes with
continuity, `EqOn` and `EventuallyEq` lemmas; iterating it assembles the
rectangle and triangle parametrisations.
-/

open Set Filter Topology MeasureTheory
open scoped Interval

@[expose] public section

noncomputable section

namespace LeanModularForms

section AffineSegment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The affine segment from `p` to `q` traversed at rate `r` with offset `k`:
at `t = k/r` it sits at `p`, at `t = (k+1)/r` at `q`. -/
def affineSegment (r k : ℝ) (p q : E) (t : ℝ) : E := p + (r * t - k) • (q - p)

variable {r k t₀ t₁ : ℝ} {p q : E} {γ : ℝ → E}

lemma affineSegment_contDiff (r k : ℝ) (p q : E) : ContDiff ℝ ⊤ (affineSegment r k p q) :=
  contDiff_const.add (((contDiff_const.mul contDiff_id).sub contDiff_const).smul contDiff_const)

@[fun_prop]
lemma affineSegment_continuous (r k : ℝ) (p q : E) : Continuous (affineSegment r k p q) :=
  (affineSegment_contDiff r k p q).continuous

lemma affineSegment_hasDerivAt (r k : ℝ) (p q : E) (t : ℝ) :
    HasDerivAt (affineSegment r k p q) (r • (q - p)) t := by
  simpa only [mul_one, id_eq] using
    ((((hasDerivAt_id t).const_mul r).sub_const k).smul_const (q - p)).const_add p

/-- An affine-segment point with parameter in the right range lies on the segment
from `p` to `q`; feed this to `Convex.segment_subset`. -/
lemma affineSegment_mem_segment {t : ℝ} (h0 : k ≤ r * t) (h1 : r * t ≤ k + 1) (p q : E) :
    affineSegment r k p q t ∈ segment ℝ p q := by
  rw [segment_eq_image']
  exact ⟨r * t - k, ⟨by linarith, by linarith⟩, rfl⟩

/-- A function agreeing with an affine segment on a set is `C¹` there. -/
lemma affineSegment_contDiffOn_of_eqOn {s : Set ℝ} (h : EqOn γ (affineSegment r k p q) s) :
    ContDiffOn ℝ 1 γ s :=
  ((affineSegment_contDiff r k p q).of_le le_top).contDiffOn.congr h

/-- A function agreeing with an affine segment on `[t₀, t₁]` has the segment's
velocity as derivative inside `(t₀, t₁)`. -/
lemma affineSegment_hasDerivAt_of_eqOn (h : EqOn γ (affineSegment r k p q) (Icc t₀ t₁))
    {t : ℝ} (ht : t ∈ Ioo t₀ t₁) : HasDerivAt γ (r • (q - p)) t :=
  (affineSegment_hasDerivAt r k p q t).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 ht.2) fun _ hs => h (Ioo_subset_Icc_self hs))

lemma affineSegment_deriv_of_eqOn (h : EqOn γ (affineSegment r k p q) (Icc t₀ t₁))
    {t : ℝ} (ht : t ∈ Ioo t₀ t₁) : deriv γ t = r • (q - p) :=
  (affineSegment_hasDerivAt_of_eqOn h ht).deriv

/-- A function agreeing with an affine segment on `[t₀, t₁]` has the segment's
velocity as `derivWithin` on all of `[t₀, t₁]`. -/
lemma affineSegment_derivWithin_of_eqOn (h : EqOn γ (affineSegment r k p q) (Icc t₀ t₁))
    (h01 : t₀ < t₁) {t : ℝ} (ht : t ∈ Icc t₀ t₁) :
    derivWithin γ (Icc t₀ t₁) t = r • (q - p) :=
  ((affineSegment_hasDerivAt r k p q t).hasDerivWithinAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem self_mem_nhdsWithin h) (h ht)).derivWithin
    (uniqueDiffOn_Icc h01 t ht)

lemma affineSegment_differentiableAt_of_eventuallyEq {t : ℝ}
    (h : γ =ᶠ[𝓝 t] affineSegment r k p q) : DifferentiableAt ℝ γ t :=
  (affineSegment_hasDerivAt r k p q t).differentiableAt.congr_of_eventuallyEq h

lemma affineSegment_deriv_continuousAt_of_eventuallyEq {t : ℝ}
    (h : γ =ᶠ[𝓝 t] affineSegment r k p q) : ContinuousAt (deriv γ) t :=
  (continuousAt_congr h.deriv).mpr
    ((affineSegment_contDiff r k p q).continuous_deriv le_top).continuousAt

lemma affineSegment_image_subset_of_eqOn (h : EqOn γ (affineSegment r k p q) (Icc t₀ t₁))
    (hsub : Icc t₀ t₁ ⊆ Icc 0 1) :
    affineSegment r k p q '' Icc t₀ t₁ ⊆ γ '' Icc (0 : ℝ) 1 := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, hsub ht, h ht⟩

/-! Contour-integrand lemmas, specialised to `ℂ` where the integrand is the
product `f (γ t) * deriv γ t`. -/

section Complex

variable {γ : ℝ → ℂ} {p q : ℂ}

/-- Almost everywhere on a piece where `γ` is an affine segment, the contour
integrand of `f` along `γ` is `f (segment t) * velocity`. (The endpoint `t₁`,
where `deriv γ` may differ, is null.) -/
lemma affineSegment_integrand_ae_of_eqOn (h : EqOn γ (affineSegment r k p q) (Icc t₀ t₁))
    (h01 : t₀ ≤ t₁) (f : ℂ → ℂ) :
    ∀ᵐ t, t ∈ Ι t₀ t₁ →
      f (γ t) * deriv γ t = f (affineSegment r k p q t) * (r • (q - p)) := by
  filter_upwards [MeasureTheory.Measure.ae_ne volume t₁] with t ht hI
  rw [uIoc_of_le h01] at hI
  have ht' : t ∈ Ioo t₀ t₁ := ⟨hI.1, hI.2.lt_of_ne ht⟩
  rw [affineSegment_deriv_of_eqOn h ht', h (Ioo_subset_Icc_self ht')]

/-- If `f` is continuous on the image of `γ` and `γ` is an affine segment on the
piece `[t₀, t₁] ⊆ [0, 1]`, the contour integrand of `f` along `γ` is interval
integrable on the piece. -/
lemma affineSegment_integrand_intervalIntegrable_of_eqOn
    (h : EqOn γ (affineSegment r k p q) (Icc t₀ t₁)) (h01 : t₀ ≤ t₁)
    (hsub : Icc t₀ t₁ ⊆ Icc 0 1) {f : ℂ → ℂ} (hf : ContinuousOn f (γ '' Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume t₀ t₁ := by
  rw [intervalIntegrable_congr_ae
    ((ae_restrict_iff' measurableSet_uIoc).mpr (affineSegment_integrand_ae_of_eqOn h h01 f))]
  have hc : ContinuousOn (fun t : ℝ => f (affineSegment r k p q t) * (r • (q - p)))
      (uIcc t₀ t₁) := by
    rw [uIcc_of_le h01]
    exact (hf.comp (affineSegment_continuous r k p q).continuousOn fun _ hs =>
      affineSegment_image_subset_of_eqOn h hsub (mem_image_of_mem _ hs)).mul continuousOn_const
  exact hc.intervalIntegrable

/-- **Affine change of variables for a piece integral.** If `γ` is the affine
segment from `p` to `q` on `[t₀, t₁]` (with `r·t₀ = k`, `r·t₁ = k + 1`), the
contour integral of `f` along `γ` over the piece is the standard segment
integral `∫ s in 0..1, f (p + s • (q - p)) * (q - p)`. -/
lemma affineSegment_integral_eq_of_eqOn (hr : 0 < r) (hk0 : r * t₀ = k) (hk1 : r * t₁ = k + 1)
    (h : EqOn γ (affineSegment r k p q) (Icc t₀ t₁)) (f : ℂ → ℂ) :
    (∫ t in t₀..t₁, f (γ t) * deriv γ t) =
      ∫ s in (0 : ℝ)..1, f (p + s • (q - p)) * (q - p) := by
  have h01 : t₀ < t₁ := lt_of_mul_lt_mul_left (by linarith : r * t₀ < r * t₁) hr.le
  rw [intervalIntegral.integral_congr_ae (affineSegment_integrand_ae_of_eqOn h h01.le f)]
  have h_cov := intervalIntegral.smul_integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
    (f := fun y => f (affineSegment r k p q y) * (r • (q - p))) (1 / r) t₀
  have ht1 : 1 / r * 1 + t₀ = t₁ := mul_left_cancel₀ hr.ne' <| by
    rw [mul_add, ← mul_assoc, mul_one_div_cancel hr.ne', hk0, hk1]; ring
  rw [show 1 / r * 0 + t₀ = t₀ by ring, ht1] at h_cov
  rw [← h_cov, ← intervalIntegral.integral_smul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  have harg : r * (1 / r * s + t₀) - k = s := by
    rw [mul_add, ← mul_assoc, mul_one_div_cancel hr.ne', one_mul, hk0]
    ring
  show (1 / r) • (f (affineSegment r k p q (1 / r * s + t₀)) * (r • (q - p)))
      = f (p + s • (q - p)) * (q - p)
  rw [show affineSegment r k p q (1 / r * s + t₀) = p + s • (q - p) by
        simp only [affineSegment, harg],
    mul_smul_comm, smul_smul, one_div, inv_mul_cancel₀ hr.ne', one_smul]

end Complex

end AffineSegment

/-! The two-piece gluing step. -/

section IfLE

variable {α : Type*} {τ t : ℝ} {f g : ℝ → α}

/-- Glue two functions at threshold `τ`: use `f` on `(-∞, τ]` and `g` beyond. -/
def ifLE (τ : ℝ) (f g : ℝ → α) : ℝ → α := fun t => if t ≤ τ then f t else g t

lemma ifLE_apply_of_le (h : t ≤ τ) : ifLE τ f g t = f t := if_pos h

lemma ifLE_apply_of_lt (h : τ < t) : ifLE τ f g t = g t := if_neg (not_le.mpr h)

/-- A glued function agrees with its right piece on `[τ, ∞)` provided the pieces
agree at the junction. -/
lemma ifLE_eqOn_right (hfg : f τ = g τ) : EqOn (ifLE τ f g) g (Ici τ) := fun t ht => by
  rcases eq_or_lt_of_le (mem_Ici.mp ht) with rfl | h
  · exact (if_pos le_rfl).trans hfg
  · exact ifLE_apply_of_lt h

lemma ifLE_continuous [TopologicalSpace α] (hf : Continuous f) (hg : Continuous g)
    (hfg : f τ = g τ) : Continuous (ifLE τ f g) :=
  hf.if_le hg continuous_id continuous_const fun _ ht => ht ▸ hfg

lemma ifLE_eventuallyEq_left (ht : t < τ) : ifLE τ f g =ᶠ[𝓝 t] f :=
  Filter.eventually_of_mem (Iio_mem_nhds ht) fun _ hs => if_pos (le_of_lt hs)

lemma ifLE_eventuallyEq_right (ht : τ < t) : ifLE τ f g =ᶠ[𝓝 t] g :=
  Filter.eventually_of_mem (Ioi_mem_nhds ht) fun _ hs => if_neg (not_le.mpr hs)

end IfLE

end LeanModularForms

end

end
