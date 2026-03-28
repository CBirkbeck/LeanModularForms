/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Basic
import LeanModularForms.GeneralizedResidueTheory.CauchyPrimitive
import LeanModularForms.GeneralizedResidueTheory.PrincipalValue
import LeanModularForms.GeneralizedResidueTheory.Homotopy.Invariance
import LeanModularForms.GeneralizedResidueTheory.Residue
import LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer.CPVExistence
import LeanModularForms.GeneralizedResidueTheory.Residue.GeneralizedTheoremBase
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Normed.Group.ZeroAtInfty
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.NormedSpace.Connected

/-!
# Null-Homologous Curves and the Cauchy Integral Theorem

A closed piecewise C^1 immersion is **null-homologous** in an open set U when its
winding number around every point outside U is zero. This is the topological
condition required by the generalized residue theorem of Hungerbuhler-Wasem.

## Main definitions

* `IsNullHomologous` -- null-homologous curve in an open set

## Main results

* `isNullHomologous_of_convex` -- every closed curve in a convex open set
  is null-homologous (bridge lemma)
-/

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped Classical

noncomputable section

/-- A closed piecewise C^1 immersion gamma is null-homologous in an open set U if:
1. gamma is a closed curve
2. gamma lies entirely in U
3. The winding number of gamma around every point outside U is zero.

This matches the definition in Hungerbuhler-Wasem (arXiv:1808.00997v2). -/
structure IsNullHomologous (γ : PiecewiseC1Immersion) (U : Set ℂ) : Prop where
  closed : γ.toPiecewiseC1Curve.IsClosed
  image_subset : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U
  winding_zero : ∀ z, z ∉ U →
    generalizedWindingNumber' γ.toFun γ.a γ.b z = 0

private lemma ftc_no_interior_partition {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (a' b' : ℝ)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b)
    (hFγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b))
    (hFγ_deriv_off : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑γ.partition : Set ℝ) →
      HasDerivAt (F ∘ γ.toFun) (f (γ.toFun t) * deriv γ.toFun t) t)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc γ.a γ.b)
    (hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅) :
    ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun b') - F (γ.toFun a') := by
  have ha'_bds := hsub (left_mem_Icc.mpr ha'b')
  have hb'_bds := hsub (right_mem_Icc.mpr ha'b')
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha'b'
    (hFγ_cont.mono hsub)
  · intro t ht
    apply hFγ_deriv_off t
      ⟨lt_of_le_of_lt ha'_bds.1 ht.1, lt_of_lt_of_le ht.2 hb'_bds.2⟩
    intro ht_P
    exact Finset.notMem_empty t (hempty ▸ Finset.mem_filter.mpr ⟨ht_P, ht.1, ht.2⟩)
  · exact h_int.mono_set (uIcc_subset_uIcc
      (Set.mem_uIcc_of_le ha'_bds.1 ha'_bds.2)
      (Set.mem_uIcc_of_le hb'_bds.1 hb'_bds.2))

private lemma partition_filter_card_lt_left (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => a' < t ∧ t < c)).card
      < (P.filter (fun t => a' < t ∧ t < b')).card := by
  apply Finset.card_lt_card
  constructor
  · intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, ht.2.1, lt_trans ht.2.2 hcb⟩
  · intro hsub
    have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.2

private lemma partition_filter_card_lt_right (P : Finset ℝ) {a' b' c : ℝ}
    (hc_part : c ∈ P) (hac : a' < c) (hcb : c < b') :
    (P.filter (fun t => c < t ∧ t < b')).card
      < (P.filter (fun t => a' < t ∧ t < b')).card := by
  apply Finset.card_lt_card
  constructor
  · intro t ht
    simp only [Finset.mem_filter] at ht ⊢
    exact ⟨ht.1, lt_trans hac ht.2.1, ht.2.2⟩
  · intro hsub
    have hcmem := hsub (Finset.mem_filter.mpr ⟨hc_part, hac, hcb⟩)
    simp only [Finset.mem_filter] at hcmem
    exact lt_irrefl c hcmem.2.1

private lemma ftc_inductive_step {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (m : ℕ) (a' b' c : ℝ)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b)
    (ih : ∀ (a' b' : ℝ),
      (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ m →
      a' ≤ b' → Icc a' b' ⊆ Icc γ.a γ.b →
      a' ∈ γ.partition → b' ∈ γ.partition →
      ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
        F (γ.toFun b') - F (γ.toFun a'))
    (hcard : (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ m + 1)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc γ.a γ.b)
    (ha'P : a' ∈ γ.partition) (hb'P : b' ∈ γ.partition)
    (hc_part : c ∈ γ.partition) (hac : a' < c) (hcb : c < b') :
    ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun b') - F (γ.toFun a') := by
  have hc_bds : c ∈ Icc γ.a γ.b := hsub ⟨le_of_lt hac, le_of_lt hcb⟩
  have h_int_ac := h_int.mono_set (uIcc_subset_uIcc
    (Set.mem_uIcc_of_le (hsub (left_mem_Icc.mpr ha'b')).1
      (hsub (left_mem_Icc.mpr ha'b')).2)
    (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2))
  have h_int_cb := h_int.mono_set (uIcc_subset_uIcc
    (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2)
    (Set.mem_uIcc_of_le (hsub (right_mem_Icc.mpr ha'b')).1
      (hsub (right_mem_Icc.mpr ha'b')).2))
  have hcard_ac : (γ.partition.filter (fun t => a' < t ∧ t < c)).card ≤ m := by
    have := partition_filter_card_lt_left γ.partition hc_part hac hcb; omega
  have hcard_cb : (γ.partition.filter (fun t => c < t ∧ t < b')).card ≤ m := by
    have := partition_filter_card_lt_right γ.partition hc_part hac hcb; omega
  have h_ac := ih a' c hcard_ac (le_of_lt hac)
    (fun t ht => hsub ⟨ht.1, le_trans ht.2 (le_of_lt hcb)⟩) ha'P hc_part
  have h_cb := ih c b' hcard_cb (le_of_lt hcb)
    (fun t ht => hsub ⟨le_trans (le_of_lt hac) ht.1, ht.2⟩) hc_part hb'P
  rw [← intervalIntegral.integral_add_adjacent_intervals h_int_ac h_int_cb, h_ac, h_cb]
  ring

/-- FTC for piecewise C¹ contours (induction on partition points): on any
sub-interval `[a', b']` whose endpoints belong to the partition and that
contains at most `n` interior partition points, the integral of
`f(γ(t)) · γ'(t)` equals `F(γ(b')) - F(γ(a'))`, provided `F ∘ γ` is
continuous, its derivative equals the integrand off the partition, and the
integrand is interval-integrable. -/
lemma ftc_piecewise_contour_induction {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (n : ℕ) (a' b' : ℝ)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b)
    (hFγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b))
    (hFγ_deriv_off : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑γ.partition : Set ℝ) →
      HasDerivAt (F ∘ γ.toFun) (f (γ.toFun t) * deriv γ.toFun t) t)
    (hcard : (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ n)
    (ha'b' : a' ≤ b') (hsub : Icc a' b' ⊆ Icc γ.a γ.b)
    (ha'P : a' ∈ γ.partition) (hb'P : b' ∈ γ.partition) :
    ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun b') - F (γ.toFun a') := by
  induction n generalizing a' b' with
  | zero =>
    exact ftc_no_interior_partition γ a' b' h_int hFγ_cont
      hFγ_deriv_off ha'b' hsub (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard))
  | succ m ih =>
    by_cases hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅
    · exact ftc_no_interior_partition γ a' b' h_int hFγ_cont hFγ_deriv_off ha'b' hsub hempty
    · obtain ⟨c, hc_filt⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      simp only [Finset.mem_filter] at hc_filt
      exact ftc_inductive_step γ m a' b' c h_int
        (fun a'' b'' hc' hab'' hsub'' haP'' hbP'' =>
          ih a'' b'' hc' hab'' hsub'' haP'' hbP'')
        hcard ha'b' hsub ha'P hb'P hc_filt.1 hc_filt.2.1 hc_filt.2.2

/- The contour integral of a derivative of a composition F circ gamma over a
piecewise C^1 curve equals F(gamma(b)) - F(gamma(a)), when F is holomorphic
on a set containing the image of gamma.

Proof strategy: split the integral along partition points and apply the
standard FTC (`integral_eq_sub_of_hasDerivAt_of_le`) on each smooth subinterval.
On each subinterval [p_i, p_{i+1}], gamma is C^1 hence differentiable, so
F circ gamma has derivative f(gamma(t)) * gamma'(t) by the chain rule, and
the sum telescopes to F(gamma(b)) - F(gamma(a)). -/
/-- Fundamental theorem of calculus for piecewise C¹ contours: if `F` is a
primitive of `f` on `U` (i.e. `HasDerivAt F (f z) z` for every `z ∈ U`) and
`γ` is a piecewise C¹ curve lying in `U`, then
`∫_γ f(z) dz = F(γ(b)) - F(γ(a))`. -/
theorem ftc_piecewise_contour {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (U : Set ℂ) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hF_prim : ∀ z ∈ U, HasDerivAt F (f z) z)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun γ.b) - F (γ.toFun γ.a) := by
  have hFγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) :=
    (ContinuousOn.comp (fun z hz => (hF_prim z hz).continuousAt.continuousWithinAt)
      γ.continuous_toFun (fun t ht => hγ_in_U t ht))
  have hFγ_deriv_off : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑γ.partition : Set ℝ) →
      HasDerivAt (F ∘ γ.toFun) (f (γ.toFun t) * deriv γ.toFun t) t := by
    intro t ht_Ioo ht_nP
    convert (hF_prim (γ.toFun t) (hγ_in_U t (Ioo_subset_Icc_self ht_Ioo))).comp_of_eq t
      (γ.smooth_off_partition t (Ioo_subset_Icc_self ht_Ioo) ht_nP).hasDerivAt rfl using 1
  exact ftc_piecewise_contour_induction γ _ γ.a γ.b h_int hFγ_cont hFγ_deriv_off
    le_rfl (le_of_lt γ.hab) (Subset.refl _)
    γ.endpoints_in_partition.1 γ.endpoints_in_partition.2

private lemma mem_Ioo_of_Icc_not_partition (γ : PiecewiseC1Curve)
    (t : ℝ) (ht_Icc : t ∈ Icc γ.a γ.b) (ht_not_part : t ∉ (γ.partition : Set ℝ)) :
    t ∈ Ioo γ.a γ.b := by
  constructor
  · by_contra h; push_neg at h
    exact ht_not_part (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1)
  · by_contra h; push_neg at h
    exact ht_not_part (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)

/-- The integrand `(γ(t) - z)⁻¹ · γ'(t)` is interval-integrable whenever `z`
is not in the image of `γ`. The proof uses compactness of `[a, b]` to bound
`‖(γ(t) - z)⁻¹‖` and the piecewise C¹ bound on `‖γ'(t)‖`. -/
theorem integrand_intervalIntegrable_of_avoids (γ : PiecewiseC1Immersion)
    (z : ℂ) (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z) :
    IntervalIntegrable
      (fun t => (γ.toFun t - z)⁻¹ * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have h_inv_cont : ContinuousOn (fun t => (γ.toFun t - z)⁻¹) (Icc γ.a γ.b) :=
    ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
      (fun t ht => sub_ne_zero.mpr (h_avoids t ht))
  obtain ⟨M_inv, hM_inv⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (h_inv_cont.norm)
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_inv * M_d) hab
  · intro t ⟨ht_Icc, ht_not_part⟩
    apply ContinuousWithinAt.mul
    · exact (h_inv_cont t ht_Icc).mono diff_subset
    · exact (γ.deriv_continuous_off_partition t
        (mem_Ioo_of_Icc_not_partition γ.toPiecewiseC1Curve t ht_Icc ht_not_part)
        ht_not_part).continuousWithinAt
  · intro t ht
    have h1 : ‖(γ.toFun t - z)⁻¹‖ ≤ M_inv := by
      have := hM_inv t ht
      simp only [Real.norm_eq_abs, abs_norm] at this
      exact this
    calc ‖(γ.toFun t - z)⁻¹ * deriv γ.toFun t‖
        = ‖(γ.toFun t - z)⁻¹‖ * ‖deriv γ.toFun t‖ := norm_mul _ _
      _ ≤ M_inv * M_d := by
          exact mul_le_mul h1 (hM_d t ht) (norm_nonneg _)
            (le_trans (norm_nonneg _) h1)

/-- Every closed curve in a convex open set is null-homologous.

The proof uses:
1. `generalizedWindingNumber_eq_classical_away` to reduce the PV winding
   number to a classical contour integral (since z is not on the curve).
2. `holomorphic_convex_primitive` to obtain a primitive F of w |-> (w - z)^{-1}
   on the convex set U.
3. The fundamental theorem of calculus to evaluate the integral as
   F(gamma(b)) - F(gamma(a)) = 0 (since gamma is closed). -/
theorem isNullHomologous_of_convex (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U)
    (hU_ne : U.Nonempty) (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    IsNullHomologous γ U where
  closed := hγ_closed
  image_subset := hγ_in_U
  winding_zero := by
    intro z hz
    have h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z :=
      fun t ht heq => hz (heq ▸ hγ_in_U t ht)
    rw [generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve z h_avoids]
    have h_ne_z : ∀ w ∈ U, w - z ≠ 0 :=
      fun w hw => sub_ne_zero.mpr (fun heq => hz (heq ▸ hw))
    have h_holo : DifferentiableOn ℂ (fun w => (w - z)⁻¹) U := fun w hw =>
      ((differentiableAt_id.sub (differentiableAt_const z)).inv
        (h_ne_z w hw)).differentiableWithinAt
    obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU hU_ne h_holo
    have h_int := integrand_intervalIntegrable_of_avoids γ z h_avoids
    rw [ftc_piecewise_contour γ.toPiecewiseC1Curve U hγ_in_U hF h_int,
      congrArg F hγ_closed.symm, sub_self, mul_zero]

/-! ## Dixon's Proof of the Homological Cauchy Theorem

The Dixon kernel `g(z, w) = (f(z) - f(w))/(z - w)` (extended to `f'(w)` at `z = w`)
is exactly mathlib's `dslope f z w`. We use this identification throughout.

Key mathlib facts:
- `dslope_same f z = deriv f z`
- `dslope_of_ne f h z = (f z - f c)/(z - c)` for `z ≠ c`
- `continuousOn_dslope`: for fixed `c`, `z ↦ dslope f c z` is continuous
  iff `f` is continuous and differentiable at `c`
- `Complex.differentiableOn_dslope`: for fixed `c`,
  `z ↦ dslope f c z` is differentiable iff `f` is differentiable
-/

section DixonProof

variable {U : Set ℂ} {f : ℂ → ℂ}

/-- The Dixon kernel is exactly `dslope`: `dixonKernel f z w = dslope f z w`.
We use `dslope` directly rather than a custom definition. -/
abbrev dixonKernel (f : ℂ → ℂ) (z w : ℂ) : ℂ := dslope f z w

/-- h₁(w) = ∮_γ dslope(f, γ(t), w) · γ'(t) dt — the Dixon integral.
Holomorphic on all of U including image(γ). -/
noncomputable def dixonH1 (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, dslope f (γ.toFun t) w * deriv γ.toFun t

/-- h₂(w) = ∮_γ f(z)/(z-w) · γ'(t) dt — the Cauchy-type integral.
Holomorphic on ℂ \ image(γ). -/
noncomputable def dixonH2 (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t

private lemma dixonH1_dslope_expansion (γ : PiecewiseC1Immersion) (w : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    ∀ t ∈ Set.uIcc γ.a γ.b,
      dslope f (γ.toFun t) w * deriv γ.toFun t =
        f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t -
          f w / (γ.toFun t - w) * deriv γ.toFun t := by
  intro t ht_ui
  have ht : t ∈ Icc γ.a γ.b := Set.uIcc_of_le (le_of_lt γ.hab) ▸ ht_ui
  have hne : γ.toFun t ≠ w := hoff t ht
  rw [dslope_of_ne _ (Ne.symm hne), slope_def_field,
    show w - γ.toFun t = -(γ.toFun t - w) from by ring]
  field_simp [sub_ne_zero.mpr hne]
  ring

private lemma dixonH1_cauchyIntegrand_integrable (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (w : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    IntervalIntegrable
      (fun t => f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have h_inv_cont : ContinuousOn (fun t => (γ.toFun t - w)⁻¹) (Icc γ.a γ.b) :=
    ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
      (fun t ht => sub_ne_zero.mpr (hoff t ht))
  obtain ⟨M_inv, hM_inv⟩ := isCompact_Icc.exists_bound_of_continuousOn h_inv_cont.norm
  simp only [norm_norm] at hM_inv
  have hf_contOn_U : ContinuousOn f U := fun z hz =>
    ((hf z hz).differentiableAt (hU.mem_nhds hz)).continuousAt.continuousWithinAt
  have hf_cont_on : ContinuousOn (f ∘ γ.toFun) (Icc γ.a γ.b) :=
    hf_contOn_U.comp γ.continuous_toFun fun t ht => hγ_in_U t ht
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont_on.norm
  simp only [Function.comp_def, norm_norm] at hM_f
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_f * M_inv * M_d) hab
  · intro t ⟨ht_Icc, ht_npart⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b := by
      constructor
      · by_contra h; push_neg at h
        exact ht_npart (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1)
      · by_contra h; push_neg at h
        exact ht_npart (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)
    apply ContinuousWithinAt.mul
    · apply ContinuousWithinAt.div
      · exact (hf_cont_on t ht_Icc).mono diff_subset
      · exact ((γ.continuous_toFun t ht_Icc).sub continuousWithinAt_const).mono diff_subset
      · exact sub_ne_zero.mpr (hoff t ht_Icc)
    · exact (γ.deriv_continuous_off_partition t ht_Ioo ht_npart).continuousWithinAt
  · intro t ht
    calc ‖f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖
        ≤ ‖f (γ.toFun t) / (γ.toFun t - w)‖ * ‖deriv γ.toFun t‖ := norm_mul_le _ _
      _ = ‖f (γ.toFun t)‖ * ‖(γ.toFun t - w)⁻¹‖ * ‖deriv γ.toFun t‖ := by
            rw [norm_div, norm_inv, div_eq_mul_inv]
      _ ≤ M_f * M_inv * M_d :=
            mul_le_mul (mul_le_mul (hM_f t ht) (hM_inv t ht) (norm_nonneg _)
              (le_trans (norm_nonneg _) (hM_f t ht)))
              (hM_d t ht) (norm_nonneg _)
              (mul_nonneg (le_trans (norm_nonneg _) (hM_f t ht))
                (le_trans (norm_nonneg _) (hM_inv t ht)))

/-- Key identity: h₁(w) = h₂(w) - 2πi · n(γ,w) · f(w) for w off the curve.
This follows from expanding dslope and splitting the integral. -/
theorem dixonH1_eq (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (w : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH1 f γ w = dixonH2 f γ w -
      2 * ↑Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w := by
  simp only [dixonH1, dixonH2]
  rw [intervalIntegral.integral_congr (dixonH1_dslope_expansion γ w hoff)]
  have h_base_int : IntervalIntegrable
      (fun t => (γ.toFun t - w)⁻¹ * deriv γ.toFun t) volume γ.a γ.b :=
    integrand_intervalIntegrable_of_avoids γ w hoff
  have h_fw_int : IntervalIntegrable
      (fun t => f w / (γ.toFun t - w) * deriv γ.toFun t) volume γ.a γ.b := by
    rw [show (fun t => f w / (γ.toFun t - w) * deriv γ.toFun t) =
        (fun t => f w * ((γ.toFun t - w)⁻¹ * deriv γ.toFun t)) from by
      ext t; rw [div_eq_mul_inv]; ring]
    exact h_base_int.const_mul _
  rw [intervalIntegral.integral_sub
    (dixonH1_cauchyIntegrand_integrable hU hf γ hγ_in_U w hoff) h_fw_int]
  congr 1
  exact integral_singular_term_eq_winding_times_coeff γ.toPiecewiseC1Curve w (f w) hoff

private lemma dixonH2_integrand_integrable (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b))
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε) (x : ℂ)
    (hdist_lb : ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖)
    (hball_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x) :
    IntervalIntegrable
      (fun t => f (γ.toFun t) / (γ.toFun t - x) * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_f * ε⁻¹ * M_d) hab
  · intro t ⟨ht_Icc, ht_npart⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b := ⟨by
      by_contra h; push_neg at h
      exact ht_npart (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1), by
      by_contra h; push_neg at h
      exact ht_npart (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)⟩
    exact ((hfγ_cont t ht_Icc).div
        ((γ.continuous_toFun t ht_Icc).sub continuousWithinAt_const)
        (sub_ne_zero.mpr (hball_avoids t ht_Icc)) |>.mono diff_subset).mul
      (γ.deriv_continuous_off_partition t ht_Ioo ht_npart).continuousWithinAt
  · intro t ht
    rw [norm_mul, norm_div]
    have hbound1 : ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖ ≤ M_f / ε :=
      calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖
          ≤ ‖f (γ.toFun t)‖ / ε :=
            div_le_div_of_nonneg_left (norm_nonneg _) hε_pos (hdist_lb t ht)
        _ ≤ M_f / ε := by gcongr; exact hM_f t ht
    calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖ * ‖deriv γ.toFun t‖
        ≤ (M_f / ε) * M_d :=
          mul_le_mul hbound1 (hM_d t ht) (norm_nonneg _) (div_nonneg hM_f_nn hε_pos.le)
      _ = M_f * ε⁻¹ * M_d := by rw [div_eq_mul_inv]

private noncomputable def dixonH2_F (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) : ℂ → ℝ → ℂ :=
  fun x t => f (γ.toFun t) * (γ.toFun t - x)⁻¹ * deriv γ.toFun t

private noncomputable def dixonH2_F' (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) : ℂ → ℝ → ℂ :=
  fun x t => f (γ.toFun t) * (γ.toFun t - x)⁻¹ ^ 2 * deriv γ.toFun t

private lemma dixonH2_pointwise_hasDerivAt (fz c z x : ℂ) (hne : z - x ≠ 0) :
    HasDerivAt (fun x => fz * (z - x)⁻¹ * c) (fz * (z - x)⁻¹ ^ 2 * c) x := by
  have h1 : HasDerivAt (fun x => z - x) (-1) x := by
    convert (hasDerivAt_const x z).sub (hasDerivAt_id x) using 1
    simp only [zero_sub]
  have h2 : HasDerivAt (fun x => (z - x)⁻¹) (-(-1) / (z - x) ^ 2) x :=
    h1.fun_inv hne
  simp only [neg_neg, one_div] at h2
  have h3 : HasDerivAt (fun x => fz * (z - x)⁻¹) (fz * ((z - x) ^ 2)⁻¹) x := by
    convert h2.const_mul fz using 1
  convert h3.mul_const c using 1
  rw [inv_pow]

private lemma dixonH2_deriv_bound (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε) (w : ℂ)
    (hdist_lb : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε,
        ‖f (γ.toFun t) * (γ.toFun t - x)⁻¹ ^ 2 * deriv γ.toFun t‖ ≤
          M_f * ε⁻¹ ^ 2 * M_d := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  filter_upwards with t _ht x hx_ball
  have ht : t ∈ Icc γ.a γ.b := by
    rw [Set.uIoc_of_le hab] at _ht; exact Set.Ioc_subset_Icc_self _ht
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  calc ‖f (γ.toFun t)‖ * ‖γ.toFun t - x‖⁻¹ ^ 2 * ‖deriv γ.toFun t‖
      ≤ M_f * ε⁻¹ ^ 2 * M_d := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact hM_f t ht
          · exact pow_le_pow_left₀ (by positivity)
              (inv_anti₀ hε_pos (hdist_lb x hx_ball t ht)) 2
          · positivity
          · exact hM_f_nn
        · exact hM_d t ht
        · positivity
        · apply mul_nonneg
          · exact hM_f_nn
          · positivity

private lemma dixonH2_hasDerivAt (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b))
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (_hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε) (w : ℂ)
    (_hdist_lb_w : ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - w‖)
    (_hball_avoids : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x)
    (_hdist_lb : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖) :
    HasDerivAt (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - w)⁻¹ * deriv γ.toFun t)
      (∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t) w := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hav_w : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := fun t ht =>
    _hball_avoids w (Metric.mem_ball_self hε_pos) t ht
  have hF_int : IntervalIntegrable (dixonH2_F f γ w) volume γ.a γ.b := by
    have heq : dixonH2_F f γ w =
        fun t => f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t := by
      ext t; simp only [dixonH2_F, div_eq_mul_inv]
    rw [heq]
    exact dixonH2_integrand_integrable f γ hfγ_cont M_f M_d ε
      hM_f hM_d _hM_f_nn hε_pos w _hdist_lb_w hav_w
  have hF_meas : ∀ᶠ x in 𝓝 w,
      AEStronglyMeasurable (dixonH2_F f γ x) (volume.restrict (Set.uIoc γ.a γ.b)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds w hε_pos)
    intro x hx
    have hint_x : IntervalIntegrable (dixonH2_F f γ x) volume γ.a γ.b := by
      have heq : dixonH2_F f γ x =
          fun t => f (γ.toFun t) / (γ.toFun t - x) * deriv γ.toFun t := by
        ext t; simp only [dixonH2_F, div_eq_mul_inv]
      rw [heq]
      exact dixonH2_integrand_integrable f γ hfγ_cont M_f M_d ε
        hM_f hM_d _hM_f_nn hε_pos x (fun t ht => _hdist_lb x hx t ht)
        (fun t ht => _hball_avoids x hx t ht)
    exact hint_x.def'.aestronglyMeasurable
  have hF'_int : IntervalIntegrable (dixonH2_F' f γ w) volume γ.a γ.b := by
    apply intervalIntegrable_of_piecewise_continuousOn_bounded
      (P := γ.partition) (M_f * ε⁻¹ ^ 2 * M_d) hab
    · intro t ⟨ht_Icc, ht_npart⟩
      change ContinuousWithinAt
          (fun t => f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t)
          (Icc γ.a γ.b \ γ.partition) t
      have ht_Ioo : t ∈ Ioo γ.a γ.b := ⟨by
        by_contra h; push_neg at h
        exact ht_npart (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1), by
        by_contra h; push_neg at h
        exact ht_npart (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)⟩
      exact ((hfγ_cont t ht_Icc).mul
          (((γ.continuous_toFun t ht_Icc).sub continuousWithinAt_const |>.inv₀
            (sub_ne_zero.mpr (hav_w t ht_Icc))).pow 2)
          |>.mono diff_subset).mul
        (γ.deriv_continuous_off_partition t ht_Ioo ht_npart).continuousWithinAt
    · intro t ht
      change ‖f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t‖ ≤ M_f * ε⁻¹ ^ 2 * M_d
      rw [norm_mul, norm_mul, norm_pow, norm_inv]
      exact mul_le_mul
        (mul_le_mul (hM_f t ht)
          (pow_le_pow_left₀ (by positivity) (inv_anti₀ hε_pos (_hdist_lb_w t ht)) 2)
          (by positivity) _hM_f_nn)
        (hM_d t ht) (by positivity) (mul_nonneg _hM_f_nn (by positivity))
  have hF'_meas : AEStronglyMeasurable (dixonH2_F' f γ w)
      (volume.restrict (Set.uIoc γ.a γ.b)) := hF'_int.def'.aestronglyMeasurable
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε, ‖dixonH2_F' f γ x t‖ ≤ M_f * ε⁻¹ ^ 2 * M_d :=
    dixonH2_deriv_bound f γ M_f M_d ε hM_f hM_d _hM_f_nn hε_pos w _hdist_lb
  have hbound_int : IntervalIntegrable (fun _ => M_f * ε⁻¹ ^ 2 * M_d)
      volume γ.a γ.b := intervalIntegral.intervalIntegrable_const
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε,
        HasDerivAt (fun x => dixonH2_F f γ x t) (dixonH2_F' f γ x t) x := by
    filter_upwards with t _ht x hx_ball
    have ht' : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    simp only [dixonH2_F, dixonH2_F']
    exact dixonH2_pointwise_hasDerivAt (f (γ.toFun t)) (deriv γ.toFun t) (γ.toFun t) x
      (sub_ne_zero.mpr (_hball_avoids x hx_ball t ht'))
  convert (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε_pos hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2 using 2

private lemma ball_avoids_curve_of_infDist_pos (γ : PiecewiseC1Immersion)
    (w : ℂ) (hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b)) :
    ∀ x ∈ Metric.ball w (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2),
      ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x := by
  intro x hx t ht heq
  linarith [Metric.infDist_le_dist_of_mem (x := w) (show x ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht, heq⟩),
    show dist w x < _ / 2 from by rw [dist_comm]; exact Metric.mem_ball.mp hx]

private lemma dist_lower_bound_at_center (γ : PiecewiseC1Immersion) (w : ℂ) :
    ∀ t ∈ Icc γ.a γ.b,
      Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ ‖γ.toFun t - w‖ := by
  intro t ht
  have hid := Metric.infDist_le_dist_of_mem (x := w)
    (show γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht, rfl⟩)
  rw [Complex.dist_eq, ← norm_neg (w - γ.toFun t), neg_sub] at hid
  linarith [Metric.infDist_nonneg (x := w) (s := γ.toFun '' Icc γ.a γ.b)]

private lemma dist_lower_bound_on_ball (γ : PiecewiseC1Immersion) (w : ℂ) :
    ∀ x ∈ Metric.ball w (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2),
      ∀ t ∈ Icc γ.a γ.b,
        Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ ‖γ.toFun t - x‖ := by
  intro x hx t ht
  have htri := dist_triangle w x (γ.toFun t)
  rw [dist_comm w x] at htri
  have h1 : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ dist x (γ.toFun t) := by
    linarith [Metric.infDist_le_dist_of_mem (x := w)
      (show γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht, rfl⟩),
      Metric.mem_ball.mp hx]
  rwa [Complex.dist_eq, ← norm_neg (x - γ.toFun t), neg_sub] at h1

private lemma dixonH2_differentiableAt_infDist_pos (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b))
    (w : ℂ) (hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b)) :
    DifferentiableAt ℂ
      (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) w := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b) :=
    hf_cont.comp γ.continuous_toFun fun t ht => ⟨t, ht, rfl⟩
  obtain ⟨M_f, hM_f_spec⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ_cont.norm
  simp only [norm_norm] at hM_f_spec
  obtain ⟨M_d, hM_d_spec⟩ := piecewiseC1Immersion_deriv_bounded γ
  exact (dixonH2_hasDerivAt f γ hfγ_cont M_f M_d
    (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2) hM_f_spec hM_d_spec
    (le_trans (norm_nonneg _) (hM_f_spec γ.a (left_mem_Icc.mpr hab))) (by linarith) w
    (dist_lower_bound_at_center γ w) (ball_avoids_curve_of_infDist_pos γ w hinfDist_pos)
    (dist_lower_bound_on_ball γ w)).differentiableAt

/-- h₂ is differentiable at every point off the curve, when f is continuous on the image. -/
theorem dixonH2_differentiableAt (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b)) (w : ℂ)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    DifferentiableAt ℂ (dixonH2 f γ) w := by
  change DifferentiableAt ℂ
      (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) w
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have himage_closed := (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed
  exact dixonH2_differentiableAt_infDist_pos f γ hf_cont w
    ((himage_closed.notMem_iff_infDist_pos
      ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr hab, rfl⟩).mp
      fun ⟨t, ht, heq⟩ => hoff t ht heq)

/-- Uniform bound on dslope: for c in a compact set K ⊂ U and w in a ball B ⊂ U,
‖dslope f c w‖ is bounded. Uses MVT on convex balls for nearby points and
triangle inequality for distant points. -/
private lemma dslope_uniform_bound (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (K : Set ℂ) (hK_compact : IsCompact K) (hK_sub : K ⊆ U) (w₀ : ℂ) (hw₀ : w₀ ∈ U) :
    ∃ C > 0, ∃ δ > 0, ∀ c ∈ K, ∀ w ∈ Metric.ball w₀ δ,
      ‖dslope f c w‖ ≤ C := by
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  have hcb_sub : Metric.closedBall w₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hr_sub
  obtain ⟨M_f, hM_f⟩ :=
    (hK_compact.union (isCompact_closedBall w₀ (r / 2))).exists_bound_of_continuousOn
      (hf.continuousOn.mono (Set.union_subset hK_sub hcb_sub) |>.norm)
  obtain ⟨C_d, hC_d⟩ :=
    (isCompact_closedBall w₀ (r / 2)).exists_bound_of_continuousOn
      (((hf.mono hr_sub).deriv Metric.isOpen_ball).continuousOn.mono
        (Metric.closedBall_subset_ball (by linarith)))
  refine ⟨max (C_d + 1) (8 * (|M_f| + 1) / r + 1), by positivity,
    r / 4, by linarith, fun c hc w hw => ?_⟩
  by_cases hcw : c = w
  · subst hcw; rw [dslope_same]
    calc ‖deriv f c‖ ≤ C_d :=
          hC_d c (Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
            (Metric.ball_subset_closedBall hw))
      _ ≤ C_d + 1 := by linarith
      _ ≤ _ := le_max_left _ _
  · have hne : w ≠ c := fun h => hcw h.symm
    rw [dslope_of_ne _ hne, slope_def_field, norm_div]
    by_cases hc_near : c ∈ Metric.closedBall w₀ (r / 2)
    · have hw_cb : w ∈ Metric.closedBall w₀ (r / 2) :=
        Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
          (Metric.ball_subset_closedBall hw)
      have h_mvt := (convex_closedBall w₀ (r / 2)).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => (hf z (hcb_sub hz)).differentiableAt (hU.mem_nhds (hcb_sub hz)))
        hC_d hc_near hw_cb
      calc ‖f w - f c‖ / ‖w - c‖
          ≤ C_d * ‖w - c‖ / ‖w - c‖ :=
            div_le_div_of_nonneg_right h_mvt (norm_nonneg _)
        _ = C_d := mul_div_cancel_right₀ C_d (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
        _ ≤ C_d + 1 := by linarith
        _ ≤ _ := le_max_left _ _
    · have h_sep : r / 4 ≤ ‖w - c‖ := by
        have : r / 2 < dist w₀ c := by
          rw [dist_comm]; rwa [Metric.mem_closedBall, not_le] at hc_near
        calc r / 4 = r / 2 - r / 4 := by ring
          _ ≤ dist w₀ c - dist w w₀ := by linarith [Metric.mem_ball.mp hw]
          _ ≤ dist w c := by
              have := dist_triangle_left c w₀ w
              rw [dist_comm w₀ c]; linarith
          _ = ‖w - c‖ := by rw [dist_eq_norm]
      simp only [norm_norm] at hM_f
      have h1 : ‖f w‖ ≤ M_f := hM_f w (Or.inr
        (Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
          (Metric.ball_subset_closedBall hw)))
      have hM_f_nn : 0 ≤ M_f := le_trans (norm_nonneg _) h1
      have h_num : ‖f w - f c‖ ≤ 2 * M_f := by
        linarith [norm_sub_le (f w) (f c), hM_f c (Or.inl hc)]
      have h_denom_pos : (0 : ℝ) < ‖w - c‖ := lt_of_lt_of_le (by linarith) h_sep
      have h_eq : 2 * M_f / (r / 4) = 8 * M_f / r := by ring
      have h_le : 8 * M_f / r ≤ 8 * (|M_f| + 1) / r + 1 := by
        rw [abs_of_nonneg hM_f_nn]
        linarith [div_nonneg (show (0:ℝ) ≤ 8 by norm_num) hr_pos.le,
          (show 8 * M_f / r + 8 / r + 1 = 8 * (M_f + 1) / r + 1 from by ring)]
      exact le_trans
        (le_trans (div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos))
          (div_le_div_of_nonneg_left (by linarith) (by linarith) h_sep))
        (le_trans (h_eq ▸ le_refl _) (le_trans h_le (le_max_right _ _)))

private theorem dixonH1_dslope_t_cont (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) (x : ℂ) :
    ContinuousOn (fun t => dslope f (γ.toFun t) x) (Icc γ.a γ.b) := by
  by_cases hx : x ∈ U
  · have h_eq : ∀ t ∈ Icc γ.a γ.b, dslope f (γ.toFun t) x = dslope f x (γ.toFun t) := by
      intro t ht
      by_cases h : γ.toFun t = x
      · subst h; simp only [dslope_same]
      · simp only [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h]
        exact slope_comm f (γ.toFun t) x
    apply ContinuousOn.congr _ h_eq
    exact ((continuousOn_dslope (hU.mem_nhds hx)).mpr
        ⟨hf.continuousOn, (hf x hx).differentiableAt (hU.mem_nhds hx)⟩).comp
      γ.continuous_toFun (fun t ht => hγ_in_U t ht)
  · have hne : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x := fun t ht heq =>
      hx (heq ▸ hγ_in_U t ht)
    have h_eq : ∀ t ∈ Icc γ.a γ.b,
        dslope f (γ.toFun t) x = (f x - f (γ.toFun t)) / (x - γ.toFun t) := by
      intro t ht
      rw [dslope_of_ne _ (Ne.symm (hne t ht)), slope_def_field]
    apply ContinuousOn.congr _ h_eq
    apply ContinuousOn.div
    · exact continuousOn_const.sub
        (hf.continuousOn.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht))
    · exact continuousOn_const.sub γ.continuous_toFun
    · intro t ht; exact sub_ne_zero.mpr (Ne.symm (hne t ht))

private theorem dixonH1_F'_aestronglyMeasurable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (w₀ : ℂ) (hw₀ : w₀ ∈ U)
    (hdslope_diff : ∀ t ∈ Icc γ.a γ.b, DifferentiableOn ℂ (dslope f (γ.toFun t)) U)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hδ₀_pos : 0 < δ₀)
    (hBd : ∀ c ∈ γ.toFun '' Icc γ.a γ.b, ∀ w ∈ Metric.ball w₀ δ₀,
      ‖dslope f c w‖ ≤ C_b)
    (_hC_pos : 0 < C_b) :
    AEStronglyMeasurable
      (fun t => deriv (dslope f (γ.toFun t)) w₀ * deriv γ.toFun t)
      (volume.restrict (Set.uIoc γ.a γ.b)) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hdslope_t_cont := dixonH1_dslope_t_cont hU hf γ hγ_in_U
  refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop (α := ℕ))
      (f := fun n t => ((↑n + 1 : ℂ)) * (dslope f (γ.toFun t) (w₀ + 1 / (↑n + 1)) -
        dslope f (γ.toFun t) w₀) * deriv γ.toFun t) ?_ ?_
  · intro n
    obtain ⟨M_n, hM_n⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hdslope_t_cont (w₀ + 1 / ((n : ℂ) + 1))).norm)
    simp only [norm_norm] at hM_n
    exact (intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition)
      (‖(n : ℂ) + 1‖ * (M_n + C_b) * M_d) hab
      (fun t ⟨ht_Icc, ht_np⟩ => by
        have ht_Ioo : t ∈ Ioo γ.a γ.b := ⟨by
          by_contra h; push_neg at h
          exact ht_np (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1), by
          by_contra h; push_neg at h
          exact ht_np (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)⟩
        exact (continuousWithinAt_const.mul
          ((hdslope_t_cont _ t ht_Icc |>.mono diff_subset).sub
            (hdslope_t_cont _ t ht_Icc |>.mono diff_subset))).mul
          (γ.deriv_continuous_off_partition t ht_Ioo ht_np).continuousWithinAt)
      (fun t ht => by
        simp only [norm_mul]
        have h1 : ‖dslope f (γ.toFun t) (w₀ + 1 / ((n : ℂ) + 1)) -
            dslope f (γ.toFun t) w₀‖ ≤ M_n + C_b :=
          le_trans (norm_sub_le _ _)
            (add_le_add (hM_n t ht) (hBd _ ⟨t, ht, rfl⟩ w₀ (Metric.mem_ball_self hδ₀_pos)))
        have h2 : ‖deriv γ.toFun t‖ ≤ M_d := hM_d t ht
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
          h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) h1))
        )).def'.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hab] at ht
    have ht_Icc : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
    have hderiv : HasDerivAt (dslope f (γ.toFun t)) (deriv (dslope f (γ.toFun t)) w₀) w₀ :=
      ((hdslope_diff t ht_Icc).differentiableAt (hU.mem_nhds hw₀)).hasDerivAt
    have h_tendsto_zero : Filter.Tendsto
        (fun n : ℕ => (1 : ℂ) / (↑n + 1)) Filter.atTop (𝓝[≠] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hR : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hC : Filter.Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) Filter.atTop (𝓝 0) := by
          have := Complex.continuous_ofReal.continuousAt.tendsto.comp hR
          simp only [Function.comp_def] at this
          exact this.congr (fun n => by push_cast; ring)
        exact hC
      · exact Filter.Eventually.of_forall (fun n => by
          apply div_ne_zero one_ne_zero
          norm_cast)
    have hGn_eq : ∀ n : ℕ, ((↑n + 1 : ℂ)) *
            (dslope f (γ.toFun t) (w₀ + 1 / (↑n + 1)) - dslope f (γ.toFun t) w₀) *
            deriv γ.toFun t =
        ((1 : ℂ) / (↑n + 1))⁻¹ •
          (dslope f (γ.toFun t) (w₀ + 1 / (↑n + 1)) - dslope f (γ.toFun t) w₀) *
        deriv γ.toFun t := by
      intro n; simp only [smul_eq_mul]
      have hn1 : (↑n + 1 : ℂ) ≠ 0 := by norm_cast
      field_simp [hn1]
    simp_rw [hGn_eq]
    exact (hderiv.tendsto_slope_zero.comp h_tendsto_zero).mul_const _

private theorem dixonH1_dslope_intervalIntegrable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (x : ℂ) (C_b M_d : ℝ) (hC_pos : 0 < C_b)
    (hBd : ∀ c ∈ γ.toFun '' Icc γ.a γ.b, ‖dslope f c x‖ ≤ C_b)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d) :
    IntervalIntegrable
      (fun t => dslope f (γ.toFun t) x * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hdslope_t_cont := dixonH1_dslope_t_cont hU hf γ hγ_in_U
  apply intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition) (C_b * M_d) hab
  · intro t ⟨ht_Icc, ht_np⟩
    have ht_Ioo : t ∈ Ioo γ.a γ.b := ⟨by
      by_contra h; push_neg at h
      exact ht_np (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1), by
      by_contra h; push_neg at h
      exact ht_np (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)⟩
    exact (hdslope_t_cont x t ht_Icc |>.mono diff_subset).mul
      (γ.deriv_continuous_off_partition t ht_Ioo ht_np).continuousWithinAt
  · intro t ht
    rw [norm_mul]
    exact mul_le_mul (hBd _ ⟨t, ht, rfl⟩) (hM_d t ht) (norm_nonneg _) hC_pos.le

/-- h₁ is differentiable on all of U, including across the curve.
Uses the Leibniz rule (parametric differentiation of the dslope integral). -/
theorem dixonH1_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    DifferentiableOn ℂ (dixonH1 f γ) U := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hdslope_diff : ∀ t ∈ Icc γ.a γ.b, DifferentiableOn ℂ (dslope f (γ.toFun t)) U :=
    fun t ht => (differentiableOn_dslope (hU.mem_nhds (hγ_in_U t ht))).mpr hf
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  intro w₀ hw₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  obtain ⟨C, hC_pos, δ₀, hδ₀_pos, hBd⟩ :=
    dslope_uniform_bound hU hf _
      (isCompact_Icc.image_of_continuousOn γ.continuous_toFun)
      (fun _ ⟨t, ht, he⟩ => he ▸ hγ_in_U t ht) w₀ hw₀
  set ε := min δ₀ r / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h2ε_le_δ₀ : 2 * ε ≤ δ₀ := by simp only [hε_def]; linarith [min_le_left δ₀ r]
  have h2ε_le_r : 2 * ε ≤ r := by simp only [hε_def]; linarith [min_le_right δ₀ r]
  have hcb_U : ∀ x ∈ Metric.ball w₀ ε, Metric.closedBall x ε ⊆ U := fun x hx y hy => by
    apply hr_sub; rw [Metric.mem_ball] at hx ⊢
    have hy' := Metric.mem_closedBall.mp hy
    linarith [dist_triangle y x w₀]
  have hCauchy : ∀ t ∈ Icc γ.a γ.b, ∀ x ∈ Metric.ball w₀ ε,
      ‖deriv (dslope f (γ.toFun t)) x‖ ≤ C / ε := by
    intro t ht x hx
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hε_pos
    · exact (hdslope_diff t ht).diffContOnCl_ball (hcb_U x hx)
    · intro z hz
      apply hBd _ ⟨t, ht, rfl⟩
      rw [Metric.mem_ball] at hx ⊢; rw [Metric.mem_sphere] at hz
      linarith [dist_triangle z x w₀]
  have hF_int := dixonH1_dslope_intervalIntegrable hU hf γ hγ_in_U w₀ C M_d hC_pos
    (fun c hc => hBd c hc w₀ (Metric.mem_ball_self hδ₀_pos)) hM_d
  have hF_meas : ∀ᶠ x in 𝓝 w₀,
      AEStronglyMeasurable (fun t => dslope f (γ.toFun t) x * deriv γ.toFun t)
        (volume.restrict (Set.uIoc γ.a γ.b)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hε_pos)
    intro x hx
    exact (dixonH1_dslope_intervalIntegrable hU hf γ hγ_in_U x C M_d hC_pos
      (fun c hc => hBd c hc x (Metric.ball_subset_ball (by linarith) hx))
      hM_d).def'.aestronglyMeasurable
  have hF'_meas := dixonH1_F'_aestronglyMeasurable hU hf γ hγ_in_U w₀ hw₀
    hdslope_diff hM_d hδ₀_pos hBd hC_pos
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w₀ ε,
        ‖deriv (dslope f (γ.toFun t)) x * deriv γ.toFun t‖ ≤ C / ε * M_d := by
    filter_upwards with t _ht x hx
    have ht_Icc : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    rw [norm_mul]
    exact mul_le_mul (hCauchy t ht_Icc x hx) (hM_d t ht_Icc) (norm_nonneg _)
      (div_nonneg hC_pos.le hε_pos.le)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w₀ ε,
        HasDerivAt (fun x => dslope f (γ.toFun t) x * deriv γ.toFun t)
          (deriv (dslope f (γ.toFun t)) x * deriv γ.toFun t) x := by
    filter_upwards with t _ht x hx
    have ht_Icc : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    have hx_U : x ∈ U := hr_sub (Metric.ball_subset_ball (by linarith : ε ≤ r) hx)
    exact ((hdslope_diff t ht_Icc).differentiableAt (hU.mem_nhds hx_U) |>.hasDerivAt).mul_const _
  exact ((@intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    ℂ _ volume ℂ _ _ _ γ.a γ.b ε (fun _ => C / ε * M_d)
    (F := fun x t => dslope f (γ.toFun t) x * deriv γ.toFun t)
    (F' := fun x t => deriv (dslope f (γ.toFun t)) x * deriv γ.toFun t) w₀
    hε_pos hF_meas hF_int hF'_meas h_bound
    intervalIntegral.intervalIntegrable_const h_diff).2).differentiableAt

/-- The Dixon function: h1 on U, h2 on C \ U. -/
noncomputable def dixonFunction (f : ℂ → ℂ) (U : Set ℂ)
    (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  if _h : w ∈ U then dixonH1 f γ w else dixonH2 f γ w

/-- The Dixon function is entire (differentiable on all of ℂ).
On U: it's h₁, holomorphic by dixonH1_differentiableOn.
On ℂ \ U: it's h₂, holomorphic by dixonH2_differentiableAt.
Patching at ∂U: null-homologous gives n(γ,w) = 0 near ∂U, so h₁ = h₂ there. -/
theorem dixonFunction_differentiable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    Differentiable ℂ (dixonFunction f U γ) := by
  intro w
  by_cases hw : w ∈ U
  · have h_eq : ∀ᶠ w' in 𝓝 w, dixonFunction f U γ w' = dixonH1 f γ w' :=
      Filter.Eventually.mono (hU.mem_nhds hw)
        (fun w' hw' => by simp only [dixonFunction]; exact if_pos hw')
    exact ((dixonH1_differentiableOn hU hf γ h_null.image_subset).differentiableAt
      (hU.mem_nhds hw)).congr_of_eventuallyEq h_eq
  · have hab : γ.a ≤ γ.b := le_of_lt γ.hab
    have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := fun t ht heq =>
      hw (heq ▸ h_null.image_subset t ht)
    have himage_closed :=
      (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed
    have hw_notmem : w ∉ γ.toFun '' Icc γ.a γ.b := fun ⟨t, ht, heq⟩ => hoff t ht heq
    have hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b) :=
      (himage_closed.notMem_iff_infDist_pos
        ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr hab, rfl⟩).mp hw_notmem
    set ε := Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 with hε_def
    have hε_pos : 0 < ε := by positivity
    have hball_avoids : ∀ t ∈ Icc γ.a γ.b, ∀ w' ∈ Metric.ball w ε, γ.toFun t ≠ w' := by
      intro t ht w' hw' heq
      linarith [Metric.infDist_le_dist_of_mem (x := w)
        (show w' ∈ γ.toFun '' Icc γ.a γ.b from ⟨t, ht, heq⟩),
        show dist w w' < ε from dist_comm w' w ▸ Metric.mem_ball.mp hw']
    have hwn_cts : ContinuousOn (fun w' => generalizedWindingNumber' γ.toFun γ.a γ.b w')
        (Metric.ball w ε) := by
      apply ContinuousOn.congr
        (f := fun w' => (2 * ↑Real.pi * I)⁻¹ *
          ∫ t in γ.a..γ.b, (γ.toFun t - w')⁻¹ * deriv γ.toFun t)
      · apply continuousOn_const.mul
        intro w' hw'
        have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' :=
          fun t ht heq => hball_avoids t ht w' hw' heq
        have hdiff2 : DifferentiableAt ℂ
            (fun w'' => ∫ t in γ.a..γ.b, (γ.toFun t - w'')⁻¹ * deriv γ.toFun t) w' := by
          have h := dixonH2_differentiableAt (fun _ => 1) γ continuousOn_const w' hoff'
          convert h using 2; simp only [dixonH2, div_eq_mul_inv, one_mul]
        exact hdiff2.continuousAt.continuousWithinAt
      · intro w' hw'
        have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' :=
          fun t ht heq => hball_avoids t ht w' hw' heq
        exact generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve w' hoff'
    have hwn_w := h_null.winding_zero w hw
    have hwn_int : ∀ w' ∈ Metric.ball w ε, ∃ n : ℤ,
        generalizedWindingNumber' γ.toFun γ.a γ.b w' = n := by
      intro w' hw'
      exact windingNumber_integer_of_piecewise_closed_avoiding γ.toFun γ.a γ.b w' γ.partition
        γ.hab h_null.closed γ.continuous_toFun
        (fun t ht hP => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hP)
        (fun _p1 _p2 _h12 hnoP hsub t ht =>
          (γ.deriv_continuous_off_partition t (hsub ht) (hnoP t ht)).continuousWithinAt)
        (fun t ht => hball_avoids t ht w' hw')
        ⟨_, fun t ht => (piecewiseC1Immersion_deriv_bounded γ).choose_spec t ht⟩
    have hwn_zero_ball : ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber' γ.toFun γ.a γ.b w' = 0 := by
      haveI hpreconn : PreconnectedSpace (Metric.ball w ε) :=
        isPreconnected_iff_preconnectedSpace.mp
          (Metric.isConnected_ball hε_pos).isPreconnected
      have hwn_cts_sub : Continuous
          (fun w'' : Metric.ball w ε =>
            generalizedWindingNumber' γ.toFun γ.a γ.b w''.val) :=
        hwn_cts.comp_continuous continuous_subtype_val (fun w'' => w''.2)
      let wn_Z : Metric.ball w ε → ℤ := fun w'' => (hwn_int w'' w''.2).choose
      have wn_Z_cast : ∀ w'' : Metric.ball w ε,
          (wn_Z w'' : ℂ) = generalizedWindingNumber' γ.toFun γ.a γ.b w''.val :=
        fun w'' => (hwn_int w'' w''.2).choose_spec.symm
      have wn_Z_cont : Continuous wn_Z := by
        rw [← IsLocallyConstant.iff_continuous, IsLocallyConstant.iff_eventually_eq]
        intro ⟨w'', hw''⟩
        have hwn_cts_at : ContinuousAt
            (fun w''' : Metric.ball w ε =>
              generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val) ⟨w'', hw''⟩ :=
          hwn_cts_sub.continuousAt
        have hev : ∀ᶠ w''' : Metric.ball w ε in 𝓝 ⟨w'', hw''⟩,
            ‖generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val -
              generalizedWindingNumber' γ.toFun γ.a γ.b w''‖ < 1 / 2 := by
          have h_nbhd : ∀ᶠ w''' : Metric.ball w ε in 𝓝 ⟨w'', hw''⟩,
              generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val ∈
                Metric.ball (generalizedWindingNumber' γ.toFun γ.a γ.b w'') (1/2) :=
            hwn_cts_at (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
          exact h_nbhd.mono fun w''' h_mem =>
            (Complex.dist_eq _ _).symm ▸ Metric.mem_ball.mp h_mem
        apply hev.mono; intro ⟨w''', hw'''⟩ h_lt
        apply Int.cast_injective (α := ℂ); rw [wn_Z_cast, wn_Z_cast]
        obtain ⟨n1, hn1⟩ := hwn_int w''' hw'''
        obtain ⟨n2, hn2⟩ := hwn_int w'' hw''
        have hm : generalizedWindingNumber' γ.toFun γ.a γ.b w''' -
            generalizedWindingNumber' γ.toFun γ.a γ.b w'' = (n1 - n2 : ℤ) := by
          push_cast [hn1, hn2]; ring
        have h_norm_m : ‖((n1 - n2 : ℤ) : ℂ)‖ < 1 / 2 := hm ▸ h_lt
        rw [Complex.norm_intCast] at h_norm_m
        have h_zero : n1 - n2 = 0 := by
          have key : (|(n1 - n2 : ℤ)| : ℝ) < 1 := by
            have := h_norm_m
            simp only [Int.cast_sub] at this
            linarith [abs_nonneg ((n1 : ℝ) - n2)]
          exact_mod_cast Int.abs_lt_one_iff.mp (by exact_mod_cast key)
        exact sub_eq_zero.mp (hm ▸ (by exact_mod_cast h_zero))
      have hwn_Z_w : wn_Z ⟨w, Metric.mem_ball_self hε_pos⟩ = 0 := by
        apply Int.cast_injective (α := ℂ); push_cast; rwa [wn_Z_cast]
      intro w' hw'
      obtain ⟨n, hn⟩ := hwn_int w' hw'
      have h_n_zero : n = (0 : ℤ) := by
        have h1 : (wn_Z ⟨w', hw'⟩ : ℂ) = n := by rwa [wn_Z_cast]
        have h2 : (wn_Z ⟨w', hw'⟩ : ℂ) = 0 := mod_cast
          (PreconnectedSpace.constant hpreconn wn_Z_cont
            (x := ⟨w', hw'⟩) (y := ⟨w, Metric.mem_ball_self hε_pos⟩)).trans hwn_Z_w
        exact_mod_cast h1.symm.trans h2
      simp only [hn, h_n_zero, Int.cast_zero]
    have heq_on_ball : ∀ᶠ w' in 𝓝 w, dixonFunction f U γ w' = dixonH2 f γ w' := by
      apply Filter.Eventually.mono (Metric.ball_mem_nhds w hε_pos)
      intro w' hw'
      simp only [dixonFunction]
      split_ifs with hw'U
      · have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' := fun t ht heq =>
          hball_avoids t ht w' hw' heq
        rw [dixonH1_eq hU hf γ h_null.image_subset w' hoff', hwn_zero_ball w' hw']; ring
      · rfl
    have h2_diff : DifferentiableAt ℂ (dixonH2 f γ) w := dixonH2_differentiableAt f γ
      (hf.continuousOn.mono fun _ ⟨t, ht, heq⟩ => heq ▸ h_null.image_subset t ht) w hoff
    exact h2_diff.congr_of_eventuallyEq heq_on_ball

private lemma curveImage_dist_lower_bound (γ : PiecewiseC1Immersion) {R : ℝ}
    (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R) (w : ℂ) {t : ℝ}
    (ht : t ∈ Icc γ.a γ.b) : ‖w‖ - R ≤ ‖γ.toFun t - w‖ := by
  have h1 : ‖w‖ - ‖γ.toFun t‖ ≤ ‖w - γ.toFun t‖ := norm_sub_norm_le w (γ.toFun t)
  rw [norm_sub_rev] at h1
  linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩]

private lemma dixonH2_norm_bound (γ : PiecewiseC1Immersion) {R M_f M_d : ℝ}
    (hM_f_nn : 0 ≤ M_f) (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    {w : ℂ} (hw : R < ‖w‖) :
    ‖dixonH2 f γ w‖ ≤ M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  simp only [dixonH2]
  have hpos : 0 < ‖w‖ - R := by linarith
  have h_ptwise : ∀ t ∈ Set.uIoc γ.a γ.b,
      ‖f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖ ≤ M_f * M_d / (‖w‖ - R) := by
    intro t ht_ui
    have ht : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self (Set.uIoc_of_le hab ▸ ht_ui)
    rw [norm_mul, norm_div]
    calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - w‖ * ‖deriv γ.toFun t‖
        ≤ (M_f / (‖w‖ - R)) * M_d :=
          mul_le_mul (div_le_div₀ hM_f_nn (hM_f t ht) hpos
            (curveImage_dist_lower_bound γ hR w ht))
            (hM_d t ht) (norm_nonneg _) (div_nonneg hM_f_nn hpos.le)
      _ = M_f * M_d / (‖w‖ - R) := by ring
  calc ‖∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖
      ≤ (M_f * M_d / (‖w‖ - R)) * |γ.b - γ.a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
    _ = M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) := by
        rw [abs_of_nonneg (by linarith : 0 ≤ γ.b - γ.a)]; ring

private lemma windingNumber_norm_lt_one (γ : PiecewiseC1Immersion) {R M_d : ℝ} {w : ℂ}
    (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w)
    (hR_lt : R < ‖w‖)
    (hw : M_d * (γ.b - γ.a) / (2 * Real.pi) < ‖w‖ - R) :
    ‖generalizedWindingNumber' γ.toFun γ.a γ.b w‖ < 1 := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hba_nn : 0 ≤ γ.b - γ.a := by linarith
  have h2pi_pos : 0 < 2 * Real.pi := Real.two_pi_pos
  have hpos : 0 < ‖w‖ - R := by linarith
  rw [generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve w hoff, norm_mul,
    norm_inv, norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  have h_ptwise : ∀ t ∈ Set.uIoc γ.a γ.b,
      ‖(γ.toFun t - w)⁻¹ * deriv γ.toFun t‖ ≤ M_d / (‖w‖ - R) := by
    intro t ht_ui
    have ht := Ioc_subset_Icc_self (Set.uIoc_of_le hab ▸ ht_ui)
    rw [norm_mul, norm_inv]
    calc ‖γ.toFun t - w‖⁻¹ * ‖deriv γ.toFun t‖
        ≤ (‖w‖ - R)⁻¹ * M_d := by
          apply mul_le_mul _ (hM_d t ht) (norm_nonneg _) (inv_nonneg.mpr hpos.le)
          exact inv_anti₀ hpos (curveImage_dist_lower_bound γ hR w ht)
      _ = M_d / (‖w‖ - R) := by rw [mul_comm, div_eq_mul_inv]
  have h_int_b : ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
      ≤ M_d / (‖w‖ - R) * (γ.b - γ.a) := by
    calc ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
        ≤ M_d / (‖w‖ - R) * |γ.b - γ.a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
      _ = M_d / (‖w‖ - R) * (γ.b - γ.a) := by rw [abs_of_nonneg hba_nn]
  calc (2 * Real.pi)⁻¹ * ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
      ≤ (2 * Real.pi)⁻¹ * (M_d / (‖w‖ - R) * (γ.b - γ.a)) :=
        mul_le_mul_of_nonneg_left h_int_b (inv_nonneg.mpr h2pi_pos.le)
    _ < 1 := by
        rw [show (2 * Real.pi)⁻¹ * (M_d / (‖w‖ - R) * (γ.b - γ.a)) =
            M_d * (γ.b - γ.a) / ((‖w‖ - R) * (2 * Real.pi)) from by field_simp]
        rw [div_lt_one (mul_pos hpos h2pi_pos)]
        linarith [(div_lt_iff₀ h2pi_pos).mp hw]

private lemma windingNumber_zero_of_large_norm (γ : PiecewiseC1Immersion) {R M_d : ℝ}
    (hM_d_nn : 0 ≤ M_d) (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hclosed : γ.toFun γ.a = γ.toFun γ.b)
    {w : ℂ} (hw : R + M_d * (γ.b - γ.a) / (2 * Real.pi) < ‖w‖) :
    generalizedWindingNumber' γ.toFun γ.a γ.b w = 0 := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have h2pi_pos : 0 < 2 * Real.pi := Real.two_pi_pos
  have hR_lt : R < ‖w‖ := by linarith [div_nonneg (mul_nonneg hM_d_nn
    (by linarith : 0 ≤ γ.b - γ.a)) h2pi_pos.le]
  have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := fun t ht heq => by
    linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩, heq ▸ hR_lt]
  obtain ⟨n, hn_eq⟩ := windingNumber_integer_of_piecewise_closed_avoiding γ.toFun γ.a γ.b w
    γ.partition γ.hab hclosed γ.continuous_toFun
    (fun t ht hP => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hP)
    (fun _p1 _p2 _h12 hnoP hsub t ht =>
      (γ.deriv_continuous_off_partition t (hsub ht) (hnoP t ht)).continuousWithinAt)
    hoff ⟨M_d, hM_d⟩
  rw [hn_eq]
  have h_norm_wn : ‖generalizedWindingNumber' γ.toFun γ.a γ.b w‖ < 1 :=
    windingNumber_norm_lt_one γ hR hM_d hoff hR_lt (by linarith)
  rw [hn_eq] at h_norm_wn
  rw [Complex.norm_intCast] at h_norm_wn
  have h_abs := abs_lt.mp h_norm_wn
  norm_cast at h_abs ⊢
  omega

private lemma dixonFunction_norm_lt_of_large (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    {R M_f M_d : ℝ} (hM_f_nn : 0 ≤ M_f) (hM_d_nn : 0 ≤ M_d)
    (hR : ∀ x ∈ γ.toFun '' Icc γ.a γ.b, ‖x‖ ≤ R)
    (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    {ε : ℝ} (hε : 0 < ε) {w : ℂ}
    (hw : max (R + M_d * (γ.b - γ.a) / (2 * Real.pi))
              (R + M_f * M_d * (γ.b - γ.a) / ε) < ‖w‖) :
    ‖dixonFunction f U γ w‖ < ε := by
  have hR_lt : R < ‖w‖ := by
    have hnn : 0 ≤ M_d * (γ.b - γ.a) / (2 * Real.pi) :=
      div_nonneg (mul_nonneg hM_d_nn (by linarith [γ.hab])) Real.two_pi_pos.le
    linarith [le_max_left (R + M_d * (γ.b - γ.a) / (2 * Real.pi))
                           (R + M_f * M_d * (γ.b - γ.a) / ε)]
  have hwn_eq_zero : generalizedWindingNumber' γ.toFun γ.a γ.b w = 0 :=
    windingNumber_zero_of_large_norm γ hM_d_nn hR hM_d h_null.closed
      (lt_of_le_of_lt (le_max_left _ _) hw)
  have h_bound_lt_ε : M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) < ε := by
    have hpos : 0 < ‖w‖ - R := by linarith
    rw [div_lt_iff₀ hpos]
    have h_div_lt : M_f * M_d * (γ.b - γ.a) / ε < ‖w‖ - R := by
      linarith [lt_of_le_of_lt (le_max_right _ _) hw]
    linarith [(div_lt_iff₀ hε).mp h_div_lt]
  have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := by
    intro t ht heq; linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩, heq ▸ hR_lt]
  by_cases hwin : w ∈ U
  · simp only [dixonFunction, dif_pos hwin]
    rw [dixonH1_eq hU hf γ h_null.image_subset w hoff, hwn_eq_zero]
    simp only [mul_zero, zero_mul, sub_zero]
    exact lt_of_le_of_lt
      (dixonH2_norm_bound γ hM_f_nn hR hM_f hM_d hR_lt) h_bound_lt_ε
  · simp only [dixonFunction, dif_neg hwin]
    exact lt_of_le_of_lt
      (dixonH2_norm_bound γ hM_f_nn hR hM_f hM_d hR_lt) h_bound_lt_ε

theorem dixonFunction_tendsto_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    Tendsto (dixonFunction f U γ) (Filter.cocompact ℂ) (𝓝 0) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  obtain ⟨R, hR⟩ :=
    (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isBounded.exists_norm_le
  have hR_nn : 0 ≤ R := le_trans (norm_nonneg _)
    (hR (γ.toFun γ.a) ⟨γ.a, left_mem_Icc.mpr hab, rfl⟩)
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hM_d_nn : 0 ≤ M_d := le_trans (norm_nonneg _) (hM_d γ.a (left_mem_Icc.mpr hab))
  have hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b) :=
    hf.continuousOn.comp γ.continuous_toFun fun t ht => h_null.image_subset t ht
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ_cont.norm
  simp only [norm_norm] at hM_f
  have hM_f_nn : 0 ≤ M_f := le_trans (norm_nonneg _) (hM_f γ.a (left_mem_Icc.mpr hab))
  exact zero_at_infty_of_norm_le _ fun ε hε => ⟨_, fun w hw =>
    dixonFunction_norm_lt_of_large hU hf γ h_null hM_f_nn hM_d_nn hR hM_f hM_d hε hw⟩

/-- h ≡ 0 by Liouville's theorem. -/
theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∀ w, dixonFunction f U γ w = 0 := by
  intro w
  exact Differentiable.apply_eq_of_tendsto_cocompact
    (dixonFunction_differentiable hU hf γ h_null) w
    (dixonFunction_tendsto_zero hU hf γ h_null)

/-- Cauchy integral formula for null-homologous curves:
∮_γ f(z)/(z-w) dz = 2πi · n(γ,w) · f(w) for w ∈ U off the curve. -/
theorem cauchyIntegralFormula_nullHomologous (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (w : ℂ) (hw : w ∈ U) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH2 f γ w =
      2 * ↑Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w := by
  have h_zero := dixonFunction_eq_zero hU hf γ h_null w
  simp only [dixonFunction, dif_pos hw] at h_zero
  have h_eq := dixonH1_eq hU hf γ h_null.image_subset w hoff
  rw [h_zero] at h_eq; linear_combination -h_eq

/-- The image of a piecewise C¹ immersion has empty interior in ℂ.
This follows from the fact that a Lipschitz map from ℝ to ℂ has image with
Hausdorff dimension at most 1, hence Lebesgue measure 0 in ℂ. -/
lemma piecewiseC1_image_interior_empty (γ : PiecewiseC1Immersion) :
    interior (γ.toFun '' Icc γ.a γ.b) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  apply dense_compl_of_dimH_lt_finrank
  have hsplit : γ.toFun '' Icc γ.a γ.b =
      γ.toFun '' (Icc γ.a γ.b \ ↑γ.partition) ∪ γ.toFun '' ↑γ.partition := by
    rw [← Set.image_union]
    congr 1
    exact (Set.diff_union_of_subset γ.partition_subset).symm
  rw [hsplit, dimH_union]
  apply max_lt
  · apply lt_of_le_of_lt
    · apply dimH_image_le_of_locally_lipschitzOn
      intro t ⟨ht_Icc, ht_npart⟩
      have ht_Ioo : t ∈ Ioo γ.a γ.b := by
        constructor
        · by_contra h; push_neg at h
          exact ht_npart (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1)
        · by_contra h; push_neg at h
          exact ht_npart (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)
      have hevt : ∀ᶠ y in 𝓝 t, HasDerivAt γ.toFun (deriv γ.toFun y) y := by
        filter_upwards [(γ.partition.finite_toSet.isClosed.isOpen_compl.inter
          (isOpen_Ioo (a := γ.a) (b := γ.b))).mem_nhds ⟨ht_npart, ht_Ioo⟩]
          with y ⟨hy_compl, hy_Ioo⟩
        exact (γ.smooth_off_partition y (Ioo_subset_Icc_self hy_Ioo) hy_compl).hasDerivAt
      have hstrict : HasStrictDerivAt γ.toFun (deriv γ.toFun t) t :=
        hasStrictDerivAt_of_hasDerivAt_of_continuousAt hevt
          (γ.deriv_continuous_off_partition t ht_Ioo ht_npart)
      obtain ⟨K, v, hv, hLip⟩ := hstrict.hasStrictFDerivAt.exists_lipschitzOnWith
      refine ⟨K, (Icc γ.a γ.b \ ↑γ.partition) ∩ v,
        inter_mem_nhdsWithin _ hv,
        hLip.mono Set.inter_subset_right⟩
    · apply lt_of_le_of_lt (dimH_mono (Set.subset_univ _))
      simp only [Real.dimH_univ]
      rw [Complex.finrank_real_complex]
      norm_cast
  · rw [(γ.partition.finite_toSet.image γ.toFun).dimH_zero]
    rw [Complex.finrank_real_complex]
    norm_cast

theorem contourIntegral_eq_zero_of_nullHomologous (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hU_ne : U.Nonempty := ⟨γ.toFun γ.a, h_null.image_subset γ.a (left_mem_Icc.mpr hab)⟩
  have h_im_int_empty := piecewiseC1_image_interior_empty γ
  obtain ⟨w₀, hw₀U, hw₀_off⟩ : ∃ w₀ ∈ U, w₀ ∉ γ.toFun '' Icc γ.a γ.b := by
    by_contra h; push_neg at h
    have : U ⊆ interior (γ.toFun '' Icc γ.a γ.b) := hU.subset_interior_iff.mpr h
    rw [h_im_int_empty] at this
    exact Set.not_nonempty_empty (hU_ne.mono this)
  have hw₀_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w₀ := fun t ht heq =>
    hw₀_off ⟨t, ht, heq⟩
  set F := fun z => f z * (z - w₀) with hF_def
  have hF_diff : DifferentiableOn ℂ F U :=
    hf.mul (differentiableOn_id.sub (differentiableOn_const w₀))
  have h_eq : ∀ t ∈ Set.uIcc γ.a γ.b,
      f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun t) / (γ.toFun t - w₀) * deriv γ.toFun t := by
    intro t ht
    have ht_Icc : t ∈ Icc γ.a γ.b := Set.uIcc_of_le hab ▸ ht
    have hne : γ.toFun t - w₀ ≠ 0 := sub_ne_zero.mpr (hw₀_avoids t ht_Icc)
    simp only [hF_def, mul_div_assoc, div_self hne, mul_one]
  rw [intervalIntegral.integral_congr h_eq]
  have hCIF := cauchyIntegralFormula_nullHomologous hU hF_diff γ h_null w₀ hw₀U hw₀_avoids
  rw [show F w₀ = 0 from by simp only [hF_def, sub_self, mul_zero], mul_zero] at hCIF
  exact hCIF

end DixonProof

end

/-! ## Downstream theorems with null-homologous hypothesis -/

/-- Null-homologous version of `integral_eq_sum_residues_of_avoids`. -/
theorem integral_eq_sum_residues_of_nullHomologous (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (hS0_in_U : ∀ s ∈ S0, s ∈ U) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (U \ S0)) (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S0, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0, ContinuousAt
      (fun z => f z - residueSimplePole f s / (z - s)) s) :
    ∫ t in γ.a..γ.b,
        f (γ.toFun t) * deriv γ.toFun t =
      2 * Real.pi * I *
        ∑ s ∈ S0,
          generalizedWindingNumber' γ.toFun γ.a γ.b s *
            residueSimplePole f s := by
  set g := fun z => f z - ∑ s ∈ S0, residueSimplePole f s / (z - s)
  have ⟨hg_diff, hf_decomp⟩ :=
    simple_poles_decomposition U hU S0 hS0_in_U f hf hSimplePoles hf_ext
  have hg_zero : ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0 :=
    contourIntegral_eq_zero_of_nullHomologous hU hg_diff γ h_null
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  have h_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U \ (S0 : Set ℂ) := fun t ht =>
    ⟨h_null.image_subset t ht, fun hs => hγ_avoids _ (Finset.mem_coe.mp hs) t ht rfl⟩
  have h_expand : ∀ t ∈ Icc γ.a γ.b,
      f (γ.toFun t) * deriv γ.toFun t =
      (∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t) +
        g (γ.toFun t) * deriv γ.toFun t := by
    intro t ht
    have := hf_decomp (γ.toFun t) (h_on_curve t ht)
    simp only at this; rw [this, add_mul, Finset.sum_mul]
  have h_eq : (fun t => f (γ.toFun t) * deriv γ.toFun t) =
      (fun t => (∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t) +
        g (γ.toFun t) * deriv γ.toFun t) := by
    funext t; simp only [g, div_eq_mul_inv, Finset.sum_mul, sub_mul, add_sub_cancel]
  have h_g_int : IntervalIntegrable
      (fun t => g (γ.toFun t) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve ⟨M_d, hM_d⟩).continuousOn_mul
      (Set.uIcc_of_le hab ▸ hg_diff.continuousOn.comp γ.toPiecewiseC1Curve.continuous_toFun
        (fun t ht => h_null.image_subset t ht))
  have h_sing_term_int : ∀ s ∈ S0, IntervalIntegrable
      (fun t => residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b := by
    intro s hs
    exact (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve ⟨M_d, hM_d⟩).continuousOn_mul
      (Set.uIcc_of_le hab ▸ (ContinuousOn.div continuousOn_const
        (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const)
        (fun t ht => sub_ne_zero.mpr (hγ_avoids s hs t ht))))
  have h_sing_int : IntervalIntegrable
      (fun t => ∑ s ∈ S0, residueSimplePole f s / (γ.toFun t - s) * deriv γ.toFun t)
      MeasureTheory.volume γ.a γ.b := by
    have h := IntervalIntegrable.sum S0 h_sing_term_int
    rwa [show (∑ i ∈ S0, fun t => residueSimplePole f i / (γ.toFun t - ↑i) * deriv γ.toFun t) =
      (fun t => ∑ i ∈ S0, residueSimplePole f i / (γ.toFun t - ↑i) * deriv γ.toFun t) from
      funext fun t => by simp only [Finset.sum_apply]] at h
  rw [h_eq, intervalIntegral.integral_add h_sing_int h_g_int, hg_zero, add_zero,
    intervalIntegral.integral_finset_sum (fun s hs =>
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve ⟨M_d, hM_d⟩).continuousOn_mul
      (Set.uIcc_of_le hab ▸ (ContinuousOn.div continuousOn_const
        (γ.toPiecewiseC1Curve.continuous_toFun.sub continuousOn_const)
        (fun t ht => sub_ne_zero.mpr (hγ_avoids s hs t ht))))), Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s hs
  rw [integral_singular_term_eq_winding_times_coeff γ.toPiecewiseC1Curve s
    (residueSimplePole f s) (fun t ht => hγ_avoids s hs t ht)]
  ring

private lemma regularPart_update_differentiableOn (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s})) (hs_in_U : s ∈ U)
    (g_an : ℂ → ℂ) (hg_an_at : AnalyticAt ℂ g_an s)
    (hg_eq : ∀ᶠ z in 𝓝[≠] s,
      f z - GeneralizedResidueTheory.meromorphicPrincipalPart f s z = g_an z) :
    DifferentiableOn ℂ
      (Function.update (fun z => f z - GeneralizedResidueTheory.meromorphicPrincipalPart f s z)
        s (g_an s)) U := by
  set pp := GeneralizedResidueTheory.meromorphicPrincipalPart f s
  set rp := fun z => f z - pp z
  set rp_nf := Function.update rp s (g_an s)
  intro z hz
  by_cases h : z = s
  · subst h
    have h_an : AnalyticAt ℂ rp_nf z := by
      apply hg_an_at.congr
      rw [Filter.eventuallyEq_iff_exists_mem]
      rw [Filter.Eventually, mem_nhdsWithin] at hg_eq
      obtain ⟨V, hV_open, hz_V, hV_eq⟩ := hg_eq
      exact ⟨V, hV_open.mem_nhds hz_V, fun w hw => by
        by_cases hwz : w = z
        · simp only [hwz, Function.update_self, rp_nf]
        · simp only [rp_nf]
          rw [Function.update_of_ne hwz]
          exact (hV_eq ⟨hw, hwz⟩).symm⟩
    exact h_an.differentiableAt.differentiableWithinAt
  · have h_rp_diff : DifferentiableAt ℂ rp z :=
      ((hf_diff z ⟨hz, Set.mem_compl_singleton_iff.mpr h⟩).differentiableAt
        ((hU.sdiff isClosed_singleton).mem_nhds ⟨hz, Set.mem_compl_singleton_iff.mpr h⟩)).sub
      ((GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s hf z
        (Set.mem_compl_singleton_iff.mpr h)).differentiableAt
        (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr h)))
    have h_ev : rp =ᶠ[𝓝 z] rp_nf := by
      apply Filter.Eventually.mono (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr h))
      intro w hw
      exact (Function.update_of_ne (Set.mem_compl_singleton_iff.mp hw) (g_an s) rp).symm
    exact (h_ev.differentiableAt_iff.mp h_rp_diff).differentiableWithinAt

private lemma contourIntegral_eq_of_agree_on_curve (f g : ℂ → ℂ)
    (γ : PiecewiseC1Immersion)
    (h_agree : ∀ t ∈ Icc γ.a γ.b, f (γ.toFun t) = g (γ.toFun t)) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
    ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (le_of_lt γ.hab)] at ht
  dsimp only
  rw [h_agree t ht]

private lemma contourIntegral_add_principalPart_regularPart (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (U : Set ℂ) (hf_diff : DifferentiableOn ℂ f (U \ {s}))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
    (∫ t in γ.a..γ.b,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t) *
        deriv γ.toFun t) +
    ∫ t in γ.a..γ.b,
      (f (γ.toFun t) - GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
        deriv γ.toFun t := by
  set pp := GeneralizedResidueTheory.meromorphicPrincipalPart f s
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  have h_decomp : ∀ t ∈ Set.uIcc γ.a γ.b,
      f (γ.toFun t) * deriv γ.toFun t =
      pp (γ.toFun t) * deriv γ.toFun t +
        (f (γ.toFun t) - pp (γ.toFun t)) * deriv γ.toFun t := by
    intro t _; ring
  rw [intervalIntegral.integral_congr h_decomp]
  have h_pp_int : IntervalIntegrable
      (fun t => pp (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
      (Set.uIcc_of_le hab ▸
        (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn
          f s hf).continuousOn.comp γ.toPiecewiseC1Curve.continuous_toFun
          (fun t ht => Set.mem_compl_singleton_iff.mpr (hγ_avoids t ht)))
  have h_rp_int : IntervalIntegrable
      (fun t => (f (γ.toFun t) - pp (γ.toFun t)) * deriv γ.toFun t) volume γ.a γ.b :=
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
      (Set.uIcc_of_le hab ▸
        (hf_diff.sub
          ((GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn
            f s hf).mono
            (fun z hz => (Set.mem_diff_singleton.mp hz).2))).continuousOn.comp
          γ.toPiecewiseC1Curve.continuous_toFun
          (fun t ht =>
            ⟨h_null.image_subset t ht,
             Set.mem_compl_singleton_iff.mpr (hγ_avoids t ht)⟩))
  convert intervalIntegral.integral_add h_pp_int h_rp_int using 1

/-- Null-homologous version: contour integral of meromorphic function with zero residue
vanishes when the curve is null-homologous and avoids the singularity. -/
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_nh (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicAt f s) (hres : residueAt f s = 0) (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ {s})) (hs_in_U : s ∈ U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  obtain ⟨g_an, hg_an_at, hg_eq⟩ :=
    GeneralizedResidueTheory.meromorphicAt_sub_principalPart_eventually f s hf
  set rp : ℂ → ℂ := fun z => f z - GeneralizedResidueTheory.meromorphicPrincipalPart f s z
  have h_pp_zero := GeneralizedResidueTheory.contourIntegral_principalPart_eq_zero_of_residue_zero
    f s hf hres γ h_null.closed hγ_avoids
  have h_rp_nf_zero := contourIntegral_eq_zero_of_nullHomologous hU
    (regularPart_update_differentiableOn f s hf U hU hf_diff hs_in_U g_an hg_an_at hg_eq) γ h_null
  have h_rp_zero := (contourIntegral_eq_of_agree_on_curve rp (Function.update rp s (g_an s)) γ
    (fun t ht => (Function.update_of_ne (hγ_avoids t ht) (g_an s) rp).symm)).trans h_rp_nf_zero
  rw [contourIntegral_add_principalPart_regularPart f s hf U hf_diff γ h_null hγ_avoids,
    h_pp_zero, h_rp_zero, add_zero]

private theorem contourIntegral_sum_principalParts_eq_zero (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (hres : ∀ s ∈ S, residueAt f s = 0)
    (γ : PiecewiseC1Immersion) (h_closed : γ.toFun γ.a = γ.toFun γ.b)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, (∑ s ∈ S,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
      deriv γ.toFun t = 0 := by
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finset_sum (fun s hs =>
    (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
      (Set.uIcc_of_le hab ▸
        (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn
          f s (hf_mero s hs)).continuousOn.comp γ.toPiecewiseC1Curve.continuous_toFun
          (fun t ht => Set.mem_compl_singleton_iff.mpr (hγ_avoids s hs t ht))))]
  exact Finset.sum_eq_zero fun s hs =>
    GeneralizedResidueTheory.contourIntegral_principalPart_eq_zero_of_residue_zero
      f s (hf_mero s hs) (hres s hs) γ h_closed (fun t ht => hγ_avoids s hs t ht)

private theorem diff_sub_principalParts_differentiableOn (S : Finset ℂ) (f : ℂ → ℂ)
    (U : Set ℂ) (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S)) :
    DifferentiableOn ℂ (fun z => f z -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z) (U \ ↑S) := by
  intro z hz
  exact (hf_diff z hz).sub (DifferentiableWithinAt.fun_sum fun s hs =>
    ((GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s
      (hf_mero s hs)).mono (fun w hw =>
        Set.mem_compl_singleton_iff.mpr (fun h =>
          hw.2 (h ▸ Finset.mem_coe.mpr hs)))) z hz)

private theorem analytic_correction_at_pole (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (g : ℂ → ℂ) (hg_def : g = fun z => f z -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z)
    (z : ℂ) (hzS : z ∈ (S : Set ℂ)) :
    ∃ g_ext : ℂ → ℂ, DifferentiableAt ℂ g_ext z ∧
      (g =ᶠ[𝓝[≠] z] g_ext) ∧
      Tendsto g (𝓝[≠] z) (𝓝 (g_ext z)) := by
  have hzS' := Finset.mem_coe.mp hzS
  obtain ⟨g_an, hg_an_at, hg_an_eq⟩ :=
    GeneralizedResidueTheory.meromorphicAt_sub_principalPart_eventually
      f z (hf_mero z hzS')
  have h_each_diff : ∀ s' ∈ S.erase z,
      DifferentiableAt ℂ (fun w =>
        GeneralizedResidueTheory.meromorphicPrincipalPart f s' w) z := by
    intro s' hs'
    have hne : z ≠ s' := (Finset.ne_of_mem_erase hs').symm
    exact (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s'
      (hf_mero s' (Finset.mem_of_mem_erase hs')) z
      (Set.mem_compl_singleton_iff.mpr hne)).differentiableAt
      (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hne))
  set g_ext : ℂ → ℂ := fun w => g_an w - ∑ s' ∈ S.erase z,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s' w with g_ext_def
  have hg_ext_diff : DifferentiableAt ℂ g_ext z := by
    apply DifferentiableAt.sub hg_an_at.differentiableAt
    convert DifferentiableAt.sum h_each_diff using 1
    ext w; exact (Finset.sum_apply w _ _).symm
  have hg_eq_ext : g =ᶠ[𝓝[≠] z] g_ext := by
    rw [hg_def]
    apply hg_an_eq.mono; intro w hw
    simp only [g_ext_def]
    rw [show ∑ s ∈ S,
          GeneralizedResidueTheory.meromorphicPrincipalPart f s w =
        GeneralizedResidueTheory.meromorphicPrincipalPart f z w +
          ∑ s' ∈ S.erase z,
            GeneralizedResidueTheory.meromorphicPrincipalPart f s' w from
        (Finset.add_sum_erase S (fun s =>
          GeneralizedResidueTheory.meromorphicPrincipalPart f s w) hzS').symm,
      ← sub_sub, hw]
  exact ⟨g_ext, hg_ext_diff, hg_eq_ext,
    (hg_ext_diff.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      hg_eq_ext.symm⟩

private theorem analytic_correction_differentiableOn (S : Finset ℂ) (f : ℂ → ℂ)
    (U : Set ℂ) (hU : IsOpen U) (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (g : ℂ → ℂ)
    (hg_def : g = fun z => f z -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z)
    (h_g_diff_off : DifferentiableOn ℂ g (U \ ↑S)) :
    ∃ g_corr : ℂ → ℂ,
      DifferentiableOn ℂ g_corr U ∧ ∀ z ∈ U \ (S : Set ℂ), g_corr z = g z := by
  refine ⟨fun z => if z ∈ (S : Set ℂ) then limUnder (𝓝[≠] z) g else g z, ?_, ?_⟩
  · intro z hz
    by_cases hzS : z ∈ (S : Set ℂ)
    · obtain ⟨g_ext, hg_ext_diff, hg_eq_ext, h_tendsto⟩ :=
        analytic_correction_at_pole S f hf_mero g hg_def z hzS
      have h_no_S_near : ∀ᶠ w in 𝓝[≠] z, w ∉ (S : Set ℂ) := by
        rw [eventually_nhdsWithin_iff]
        exact Filter.Eventually.mono ((S.erase z).finite_toSet.isClosed.isOpen_compl.mem_nhds
          (mt Finset.mem_coe.mp (Finset.notMem_erase z S)))
          fun w hw hwne hwS =>
            hw (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hwne, Finset.mem_coe.mp hwS⟩))
      have h_punc : ∀ᶠ w in 𝓝[≠] z,
          (if w ∈ (S : Set ℂ) then limUnder (𝓝[≠] w) g else g w) = g_ext w :=
        (h_no_S_near.and hg_eq_ext).mono fun w ⟨hw1, hw2⟩ => by simp only [hw1, ↓reduceIte, hw2]
      have h_at_z :
          (if z ∈ (S : Set ℂ) then limUnder (𝓝[≠] z) g else g z) = g_ext z := by
        simp only [hzS, ↓reduceIte, h_tendsto.limUnder_eq]
      rw [eventually_nhdsWithin_iff] at h_punc
      have h_ev : (fun w => if w ∈ (S : Set ℂ) then
          limUnder (𝓝[≠] w) g else g w) =ᶠ[𝓝 z] g_ext :=
        h_punc.mono fun w hw => by
          by_cases hwz : w = z
          · subst hwz; exact h_at_z
          · exact hw hwz
      exact (h_ev.differentiableAt_iff.mpr hg_ext_diff).differentiableWithinAt
    · have h_ev : (fun w => if w ∈ (S : Set ℂ) then
          limUnder (𝓝[≠] w) g else g w) =ᶠ[𝓝 z] g := by
        apply Filter.Eventually.mono (S.finite_toSet.isClosed.isOpen_compl.mem_nhds hzS)
        intro w hw
        have : w ∉ (S : Set ℂ) := hw
        simp only [this, if_false]
      exact (h_ev.differentiableAt_iff.mpr
        ((h_g_diff_off z ⟨hz, hzS⟩).differentiableAt
          ((hU.sdiff S.finite_toSet.isClosed).mem_nhds ⟨hz, hzS⟩))).differentiableWithinAt
  · intro z ⟨_, hzS⟩; simp only [if_neg hzS]

private theorem image_subset_diff_of_avoids (S : Finset ℂ) (U : Set ℂ)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    γ.toFun '' Icc γ.a γ.b ⊆ U \ ↑S :=
  fun _ ⟨t, ht, htz⟩ => ⟨htz ▸ h_null.image_subset t ht,
    fun hs => hγ_avoids _ (Finset.mem_coe.mp hs) t ht (htz ▸ rfl)⟩

private theorem remainder_integrable (S : Finset ℂ) (f : ℂ → ℂ) (U : Set ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (hf_diff : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    IntervalIntegrable (fun t => (f (γ.toFun t) -
      ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
      deriv γ.toFun t) volume γ.a γ.b := by
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  have h_g_diff_off := diff_sub_principalParts_differentiableOn S f U hf_mero hf_diff
  have h_image_off := image_subset_diff_of_avoids S U γ h_null hγ_avoids
  exact (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
    (Set.uIcc_of_le hab ▸ h_g_diff_off.continuousOn.comp
      γ.toPiecewiseC1Curve.continuous_toFun (fun t ht => h_image_off ⟨t, ht, rfl⟩))

private theorem principalParts_integrable (S : Finset ℂ) (f : ℂ → ℂ)
    (hf_mero : ∀ s ∈ S, MeromorphicAt f s) (γ : PiecewiseC1Immersion)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    IntervalIntegrable (fun t => (∑ s ∈ S,
      GeneralizedResidueTheory.meromorphicPrincipalPart f s (γ.toFun t)) *
      deriv γ.toFun t) volume γ.a γ.b := by
  have hab := le_of_lt γ.hab
  have hγ_bdd := piecewiseC1Immersion_deriv_bounded γ
  exact (piecewiseC1_deriv_intervalIntegrable γ.toPiecewiseC1Curve hγ_bdd).continuousOn_mul
    (Set.uIcc_of_le hab ▸ by
      apply continuousOn_finset_sum; intro s hs
      exact (GeneralizedResidueTheory.meromorphicPrincipalPart_differentiableOn f s
        (hf_mero s hs)).continuousOn.comp γ.toPiecewiseC1Curve.continuous_toFun
        (fun t ht => Set.mem_compl_singleton_iff.mpr (hγ_avoids s hs t ht)))

private theorem contourIntegral_correction_eq (S : Finset ℂ) (g g_corr : ℂ → ℂ)
    (U : Set ℂ) (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s)
    (h_agree : ∀ z ∈ U \ (S : Set ℂ), g_corr z = g z) :
    ∀ t ∈ Set.uIcc γ.a γ.b,
      g (γ.toFun t) * deriv γ.toFun t =
      g_corr (γ.toFun t) * deriv γ.toFun t := by
  intro t ht
  rw [Set.uIcc_of_le (le_of_lt γ.hab)] at ht
  rw [h_agree _ (image_subset_diff_of_avoids S U γ h_null hγ_avoids
    ⟨t, ht, rfl⟩)]

/-- Finset version: induction on |S| using the single-pole version. -/
theorem contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh (S : Finset ℂ)
    (f : ℂ → ℂ) (hf_mero : ∀ s ∈ S, MeromorphicAt f s)
    (hres : ∀ s ∈ S, residueAt f s = 0) (U : Set ℂ) (hU : IsOpen U)
    (hf_diff : DifferentiableOn ℂ f (U \ ↑S)) (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  set pp := fun z => ∑ s ∈ S, GeneralizedResidueTheory.meromorphicPrincipalPart f s z
  set g := fun z => f z - pp z
  obtain ⟨gc, hd, ha⟩ := analytic_correction_differentiableOn S f U hU hf_mero g rfl
    (diff_sub_principalParts_differentiableOn S f U hf_mero hf_diff)
  rw [intervalIntegral.integral_congr (show ∀ t ∈ Set.uIcc γ.a γ.b, f (γ.toFun t) *
      deriv γ.toFun t = g (γ.toFun t) * deriv γ.toFun t + pp (γ.toFun t) *
      deriv γ.toFun t from fun t _ => by simp only [g]; ring),
    intervalIntegral.integral_add (remainder_integrable S f U hf_mero hf_diff γ h_null hγ_avoids)
      (principalParts_integrable S f hf_mero γ hγ_avoids),
    show ∫ t in γ.a..γ.b, g (γ.toFun t) * deriv γ.toFun t = 0 from by
      rw [intervalIntegral.integral_congr
        (contourIntegral_correction_eq S g gc U γ h_null hγ_avoids ha)]
      exact contourIntegral_eq_zero_of_nullHomologous hU hd γ h_null,
    contourIntegral_sum_principalParts_eq_zero S f hf_mero hres γ h_null.closed hγ_avoids,
    add_zero]

open GeneralizedResidueTheory in
private theorem higherOrderCancel_assembly_nh (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0) (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    let h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s)
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) :=
  GeneralizedResidueTheory.higherOrderCancel_assembly_abstract U hU S0 f hf γ
    h_null.closed h_null.image_subset hMero hCondA hCondB _hγ_meas h_no_endpt
    h_unique_cross hS0_in_U
    (fun _ hg => contourIntegral_eq_zero_of_nullHomologous hU hg γ h_null)
    (fun T g hg_mero hg_res hg_diff _hT_in_U hg_avoids =>
      contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh T g
        hg_mero hg_res U hU hg_diff γ h_null hg_avoids)

/-! ## L5: Assembly — conditions (A')+(B) imply higher-order cancellation

The main result: combine per-term vanishing over all Laurent terms and all
crossing points to show the global PV difference tends to 0.

Note: This uses `SatisfiesConditionA'` (variable-order flatness matching the
pole order) rather than `SatisfiesConditionA` (order 1 only). The paper's
Theorem 3.3 requires flatness of the pole order, which is stronger than
flatness of order 1 for higher-order poles. -/

open GeneralizedResidueTheory in
/-- Null-homologous version of conditionsAB_imply_higherOrderCancel. -/
theorem conditionsAB_imply_higherOrderCancel_nh (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0) (hγ_meas : Measurable γ.toFun)
    (h_no_endpt : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (hS0_in_U : ∀ s ∈ S0, s ∈ U) :
    Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0) := by
  set h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s) with hh_def
  have h_integrand_eq : ∀ ε t,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t -
      cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t =
      cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t := by
    intro ε t
    exact cpvIntegrandOn_sub S0 f (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t
  suffices h_main : Tendsto
      (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) by
    apply h_main.congr'
    filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
    symm
    have h_int_f : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε) volume γ.a γ.b :=
      intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
        U S0 f hf.continuousOn γ h_null.image_subset ε hε
    have h_int_fres : IntervalIntegrable
        (cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε)
        volume γ.a γ.b := by
      have hfres_cont : ContinuousOn (fun z => ∑ s ∈ S0, residueAt f s / (z - s))
          (U \ ↑S0) := by
        apply continuousOn_finset_sum; intro s _
        apply ContinuousOn.div continuousOn_const (continuousOn_id.sub continuousOn_const)
        intro z ⟨_, hz_not_S0⟩
        exact sub_ne_zero.mpr
          (fun heq => by subst heq; exact hz_not_S0 (Finset.mem_coe.mpr ‹_›))
      exact intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
        U S0 _ hfres_cont γ h_null.image_subset ε hε
    rw [← intervalIntegral.integral_sub h_int_f h_int_fres]
    congr 1; ext t
    exact h_integrand_eq ε t
  exact higherOrderCancel_assembly_nh U hU S0 f hf γ h_null
    hMero hCondA hCondB hγ_meas h_no_endpt h_unique_cross hS0_in_U

open GeneralizedResidueTheory in
lemma pv_res_tendsto_of_immersion_nullHomologous (U : Set ℂ) (S : Set ℂ)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S) (f : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) := by
  set f_res := fun z => ∑ s ∈ S0, residueAt f s / (z - s) with hf_res_def
  have hf_res_diff := differentiableOn_sum_div_sub S0 (residueAt f) U
  have hf_ext_res : ∀ s ∈ S0, ContinuousAt
      (fun z => f_res z - residueSimplePole f_res s / (z - s)) s := fun s hs =>
    continuousAt_sum_remainder S0 (residueAt f) s hs
  have h_res_eq : ∀ s ∈ S0, residueSimplePole f_res s = residueAt f s := fun s hs =>
    residueSimplePole_sum_div_sub S0 (residueAt f) s hs
  have hPV_singular : ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f_res s / (z - s)) γ.toFun γ.a γ.b s := by
    intro s hs
    have h_eq : (fun z => residueSimplePole f_res s / (z - s)) =
        (fun z => residueSimplePole f_res s * (fun z => (z - s)⁻¹) z) := by
      ext z; simp only [div_eq_mul_inv]
    rw [h_eq]
    apply CauchyPrincipalValueExists'.const_mul
    apply cauchyPrincipalValueExists_of_singular_inv γ s
    intro ⟨t₀, ht₀, hcross⟩
    have ht₀_Ioo : t₀ ∈ Ioo γ.a γ.b := by
      refine ⟨lt_of_le_of_ne ht₀.1 (fun h => ?_), lt_of_le_of_ne ht₀.2 (fun h => ?_)⟩
      · exact (h_no_endpt_cross s hs).1 (h ▸ hcross)
      · exact (h_no_endpt_cross s hs).2 (h ▸ hcross)
    obtain ⟨a', b', ha't₀, ht₀b', ha'b'_sub, honly', _⟩ :=
      exists_isolated_crossing_interval γ s t₀ ht₀_Ioo hcross
    suffices ∃ M, Tendsto (fun ε => ∫ (t : ℝ) in γ.a..γ.b,
        if ε < ‖γ.toFun t - s‖ then (γ.toFun t - s)⁻¹ * deriv γ.toFun t else 0)
        (𝓝[>] 0) (𝓝 M) from this.choose_spec.cauchy_map
    exact cpv_exists_inv_sub_of_closed_unique γ s h_null.closed
      (h_no_endpt_cross s hs) t₀ ht₀_Ioo hcross
      (fun t ht hgt => h_unique_cross s hs t ht t₀ ht₀ hgt hcross)
  have hSimple_res : ∀ s ∈ S0, HasSimplePoleAt f_res s :=
    fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueAt f) s hs
  have hf_res_diff_univ : DifferentiableOn ℂ f_res (Set.univ \ ↑S0) :=
    differentiableOn_sum_div_sub S0 (residueAt f) Set.univ
  have h_thm := generalizedResidueTheorem' Set.univ isOpen_univ convex_univ
    S (fun s _ => Set.mem_univ s) hS_discrete hS_closed S0 hS0_subset
    f_res hf_res_diff_univ γ h_null.closed (fun t _ => Set.mem_univ _)
    (fun t ht h_mem => hS_on_curve t ht h_mem)
    hSimple_res hf_ext_res hPV_singular
  obtain ⟨h_exists, h_value⟩ := h_thm
  obtain ⟨L, hL⟩ := h_exists
  have h_limit_eq : L = 2 * Real.pi * I * ∑ s ∈ S0,
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
    have hL_eq : L = cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b :=
      hL.limUnder_eq.symm
    rw [hL_eq, h_value]; congr 1; apply Finset.sum_congr rfl
    intro s hs; rw [h_res_eq s hs]
  rw [← h_limit_eq]
  exact hL

