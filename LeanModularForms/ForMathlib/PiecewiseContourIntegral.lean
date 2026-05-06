/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Contour Integration along Piecewise C¹ Paths

This file defines the contour integral of a complex-valued function along a piecewise C¹
path and proves basic properties including linearity and the fundamental theorem of calculus.

## Main definitions

* `PiecewiseC1Path.contourIntegral f γ` — the contour integral `∫₀¹ f(γ(t)) · γ'(t) dt`

## Main results

* `contourIntegral_neg` — `∮_γ (-f) = -∮_γ f`
* `contourIntegral_add` — `∮_γ (f + g) = ∮_γ f + ∮_γ g` (under integrability)
* `contourIntegral_smul` — `∮_γ (c • f) = c • ∮_γ f`
* `contourIntegral_eq_sub_of_hasDerivAt` — if `F' = f` along the path, then
  `∮_γ f dz = F(y) - F(x)` (FTC telescope)

## Design notes

The contour integral is defined using mathlib's `intervalIntegral` over `[0, 1]`. The path
`γ : PiecewiseC1Path x y` is coerced to `ℝ → ℂ` via `Path.extend`, and the integrand is
`f(γ(t)) * deriv γ.toPath.extend t`.

The FTC telescope works by induction on the number of partition points between sub-interval
endpoints. On each smooth segment, standard FTC applies; adjacent segments telescope because
`F(γ(t_{i+1})) - F(γ(t_i))` cancels with the next segment's `F(γ(t_{i+1}))` term.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set MeasureTheory Filter Topology
open scoped Interval

noncomputable section

variable {x y : ℂ}

namespace PiecewiseC1Path

/-- The contour integral of `f` along a piecewise C¹ path `γ`:
`∮_γ f(z) dz = ∫ t in 0..1, f(γ(t)) · γ'(t) dt`. -/
def contourIntegral (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) : ℂ :=
  ∫ t in (0 : ℝ)..1, f (γ t) * deriv γ.toPath.extend t

/-- The integrand of the contour integral. -/
def contourIntegrand (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (t : ℝ) : ℂ :=
  f (γ t) * deriv γ.toPath.extend t

theorem contourIntegral_def (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) :
    contourIntegral f γ = ∫ t in (0 : ℝ)..1, contourIntegrand f γ t := rfl

/-! ### Basic linearity properties -/

/-- Negation: `∮_γ (-f) = -∮_γ f`. -/
theorem contourIntegral_neg (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) :
    contourIntegral (fun z => -f z) γ = -contourIntegral f γ := by
  simp only [contourIntegral, neg_mul, intervalIntegral.integral_neg]

/-- Addition: `∮_γ (f + g) = ∮_γ f + ∮_γ g` when both integrands are integrable. -/
theorem contourIntegral_add (f g : ℂ → ℂ) (γ : PiecewiseC1Path x y)
    (hf : IntervalIntegrable (contourIntegrand f γ) volume 0 1)
    (hg : IntervalIntegrable (contourIntegrand g γ) volume 0 1) :
    contourIntegral (fun z => f z + g z) γ =
      contourIntegral f γ + contourIntegral g γ := by
  simp only [contourIntegral, add_mul]
  exact intervalIntegral.integral_add hf hg

/-- Scalar multiplication: `∮_γ (c • f) = c • ∮_γ f`. -/
theorem contourIntegral_smul (c : ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) :
    contourIntegral (fun z => c * f z) γ = c * contourIntegral f γ := by
  simp only [contourIntegral, mul_assoc]
  exact intervalIntegral.integral_const_mul c _

/-- The contour integral of the zero function is zero. -/
theorem contourIntegral_zero (γ : PiecewiseC1Path x y) :
    contourIntegral (fun _ => 0) γ = 0 := by
  simp only [contourIntegral, zero_mul, intervalIntegral.integral_zero]

/-- Subtraction: `∮_γ (f - g) = ∮_γ f - ∮_γ g` when both integrands are integrable. -/
theorem contourIntegral_sub (f g : ℂ → ℂ) (γ : PiecewiseC1Path x y)
    (hf : IntervalIntegrable (contourIntegrand f γ) volume 0 1)
    (hg : IntervalIntegrable (contourIntegrand g γ) volume 0 1) :
    contourIntegral (fun z => f z - g z) γ =
      contourIntegral f γ - contourIntegral g γ := by
  simp only [contourIntegral, sub_mul]
  exact intervalIntegral.integral_sub hf hg

/-! ### FTC for piecewise C¹ paths

The fundamental theorem of calculus for contour integrals. If `F` is a primitive of `f`
along the image of `γ`, then `∮_γ f dz = F(y) - F(x)`.

The proof proceeds by induction on the number of partition points in a sub-interval.
On segments with no interior partition points, standard FTC applies directly.
The inductive step splits at an interior partition point and telescopes. -/

/-- On a sub-interval with no interior partition points, standard FTC applies. -/
private lemma ftc_no_partition {F f : ℂ → ℂ} (γ : PiecewiseC1Path x y)
    (a' b' : ℝ) (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1)
    (hFγ_cont : ContinuousOn (F ∘ γ.toPath.extend) (Icc 0 1))
    (hFγ_deriv : ∀ t ∈ Ioo 0 1, t ∉ γ.partition →
      HasDerivAt (F ∘ γ.toPath.extend) (f (γ t) * deriv γ.toPath.extend t) t)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅) :
    ∫ t in a'..b', f (γ t) * deriv γ.toPath.extend t =
      F (γ b') - F (γ a') := by
  have ha'_bds := hsub (left_mem_Icc.mpr ha'b')
  have hb'_bds := hsub (right_mem_Icc.mpr ha'b')
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha'b'
    (hFγ_cont.mono hsub)
  · intro t ht
    apply hFγ_deriv t ⟨lt_of_le_of_lt ha'_bds.1 ht.1, lt_of_lt_of_le ht.2 hb'_bds.2⟩
    intro ht_P
    exact Finset.notMem_empty t (hempty ▸ Finset.mem_filter.mpr ⟨ht_P, ht.1, ht.2⟩)
  · exact h_int.mono_set (uIcc_subset_uIcc
      (Set.mem_uIcc_of_le ha'_bds.1 ha'_bds.2)
      (Set.mem_uIcc_of_le hb'_bds.1 hb'_bds.2))

/-- Partition filter cardinality decreases when restricting to a left sub-interval. -/
private lemma partition_filter_card_lt_left (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => a' < t ∧ t < c)).card <
      (P.filter (fun t => a' < t ∧ t < b')).card := by
  apply Finset.card_lt_card
  constructor
  · intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1, lt_trans ht.2.2 hcb⟩
  · intro hsub
    have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.2

/-- Partition filter cardinality decreases when restricting to a right sub-interval. -/
private lemma partition_filter_card_lt_right (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => c < t ∧ t < b')).card <
      (P.filter (fun t => a' < t ∧ t < b')).card := by
  apply Finset.card_lt_card
  constructor
  · intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, lt_trans hac ht.2.1, ht.2.2⟩
  · intro hsub
    have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.1

/-- Restrict integrability from `[0,1]` to sub-intervals `[a',c]` and `[c,b']`. -/
private lemma integrability_split {f : ℂ → ℂ} (γ : PiecewiseC1Path x y)
    {a' b' c : ℝ} (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1)
    (hc_bds : c ∈ Icc 0 1)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    IntervalIntegrable (fun t => f (γ t) * deriv γ.toPath.extend t) volume a' c ∧
    IntervalIntegrable (fun t => f (γ t) * deriv γ.toPath.extend t) volume c b' :=
  ⟨h_int.mono_set (uIcc_subset_uIcc
      (Set.mem_uIcc_of_le (hsub (left_mem_Icc.mpr ha'b')).1
        (hsub (left_mem_Icc.mpr ha'b')).2)
      (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2)),
   h_int.mono_set (uIcc_subset_uIcc
      (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2)
      (Set.mem_uIcc_of_le (hsub (right_mem_Icc.mpr ha'b')).1
        (hsub (right_mem_Icc.mpr ha'b')).2))⟩

/-- FTC induction on partition cardinality: on any sub-interval `[a', b']` with
at most `n` interior partition points, the integral telescopes to `F(γ(b')) - F(γ(a'))`. -/
private lemma ftc_induction {F f : ℂ → ℂ} (γ : PiecewiseC1Path x y)
    (n : ℕ) (a' b' : ℝ)
    (hFγ_cont : ContinuousOn (F ∘ γ.toPath.extend) (Icc 0 1))
    (hFγ_deriv : ∀ t ∈ Ioo 0 1, t ∉ γ.partition →
      HasDerivAt (F ∘ γ.toPath.extend) (f (γ t) * deriv γ.toPath.extend t) t)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1)
    (hcard : (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ n)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc 0 1) :
    ∫ t in a'..b', f (γ t) * deriv γ.toPath.extend t =
      F (γ b') - F (γ a') := by
  induction n generalizing a' b' with
  | zero =>
    exact ftc_no_partition γ a' b' ha'b' hsub hFγ_cont hFγ_deriv h_int
      (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ m ih =>
    by_cases hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅
    · exact ftc_no_partition γ a' b' ha'b' hsub hFγ_cont hFγ_deriv h_int hempty
    · obtain ⟨c, hc_filt⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      simp only [Finset.mem_filter] at hc_filt
      have hc_bds : c ∈ Icc 0 1 :=
        hsub ⟨le_of_lt hc_filt.2.1, le_of_lt hc_filt.2.2⟩
      obtain ⟨h_int_ac, h_int_cb⟩ := integrability_split γ ha'b' hsub hc_bds h_int
      have hcard_ac :
          (γ.partition.filter (fun t => a' < t ∧ t < c)).card ≤ m := by
        have := partition_filter_card_lt_left γ.partition hc_filt.1 hc_filt.2.1 hc_filt.2.2
        omega
      have hcard_cb :
          (γ.partition.filter (fun t => c < t ∧ t < b')).card ≤ m := by
        have := partition_filter_card_lt_right γ.partition hc_filt.1 hc_filt.2.1 hc_filt.2.2
        omega
      have h_ac := ih a' c hcard_ac (le_of_lt hc_filt.2.1)
        (fun t ht => hsub ⟨ht.1, le_trans ht.2 (le_of_lt hc_filt.2.2)⟩)
      have h_cb := ih c b' hcard_cb (le_of_lt hc_filt.2.2)
        (fun t ht => hsub ⟨le_trans (le_of_lt hc_filt.2.1) ht.1, ht.2⟩)
      rw [← intervalIntegral.integral_add_adjacent_intervals h_int_ac h_int_cb,
          h_ac, h_cb]
      ring

/-- **Fundamental theorem of calculus for piecewise C¹ contour integrals.**

If `F` is a holomorphic primitive of `f` on a set `U` containing the image of `γ`,
then `∮_γ f(z) dz = F(y) - F(x)`.

The proof splits the integral at partition points and applies FTC on each smooth
segment; adjacent segments telescope. -/
theorem contourIntegral_eq_sub_of_hasDerivAt {F f : ℂ → ℂ}
    (γ : PiecewiseC1Path x y) {U : Set ℂ}
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    contourIntegral f γ = F y - F x := by
  unfold contourIntegral
  have hFγ_cont : ContinuousOn (F ∘ γ.toPath.extend) (Icc 0 1) := by
    apply ContinuousOn.comp _ (γ.toPath.continuous_extend.continuousOn) (fun t ht => hU t ht)
    intro z hz
    exact (hF z hz).continuousAt.continuousWithinAt
  have hFγ_deriv : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ γ.partition →
      HasDerivAt (F ∘ γ.toPath.extend)
        (f (γ t) * deriv γ.toPath.extend t) t := by
    intro t ht htp
    have hγ_diff := γ.differentiable_off t ht htp
    have ht_U := hU t (Ioo_subset_Icc_self ht)
    exact (hF (γ t) ht_U).comp_of_eq t hγ_diff.hasDerivAt rfl
  have h := ftc_induction γ _ 0 1 hFγ_cont hFγ_deriv h_int le_rfl zero_le_one (Subset.refl _)
  rwa [γ.apply_one, γ.apply_zero] at h

/-! ### Integrability from continuity -/

/-- If `f` is continuous on the image of `γ` restricted to `[0,1]`, and the derivative of
`γ.toPath.extend` is `IntervalIntegrable` on `[0,1]`, then the contour integrand
`f(γ(t)) · γ'(t)` is `IntervalIntegrable` on `[0,1]`.

The derivative integrability hypothesis is the minimal requirement: for `PwC1Immersion`
with one-sided derivative limits, it is automatic via `IntervalIntegrable` of a piecewise
continuous bounded function, but stated here as a hypothesis to cover general
`PiecewiseC1Path`. -/
theorem contourIntegrand_intervalIntegrable_of_continuousOn
    {f : ℂ → ℂ} (γ : PiecewiseC1Path x y) {K : Set ℂ}
    (hf_cont : ContinuousOn f K)
    (h_img : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ K)
    (h_deriv_int : IntervalIntegrable (deriv γ.toPath.extend) volume 0 1) :
    IntervalIntegrable (contourIntegrand f γ) volume 0 1 := by
  have h_comp : ContinuousOn (fun t => f (γ.toPath.extend t)) (Icc (0 : ℝ) 1) := by
    apply hf_cont.comp γ.toPath.continuous_extend.continuousOn
    intro t ht
    exact h_img t ht
  change IntervalIntegrable (fun t => f (γ.toPath.extend t) * deriv γ.toPath.extend t) volume 0 1
  have h_comp' : ContinuousOn (fun t => f (γ.toPath.extend t)) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le (zero_le_one' ℝ)]
    exact h_comp
  exact h_deriv_int.continuousOn_mul h_comp'

/-- **FTC for closed piecewise C¹ paths.** If `F' = f` along a closed path, then `∮_γ f = 0`. -/
theorem contourIntegral_eq_zero_of_hasDerivAt_of_closed {F f : ℂ → ℂ}
    (γ : PiecewiseC1Path x y) (hclosed : x = y) {U : Set ℂ}
    (hU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hF : ∀ z ∈ U, HasDerivAt F (f z) z)
    (h_int : IntervalIntegrable
      (fun t => f (γ t) * deriv γ.toPath.extend t) volume 0 1) :
    contourIntegral f γ = 0 := by
  rw [contourIntegral_eq_sub_of_hasDerivAt γ hU hF h_int, hclosed, sub_self]

end PiecewiseC1Path

end
