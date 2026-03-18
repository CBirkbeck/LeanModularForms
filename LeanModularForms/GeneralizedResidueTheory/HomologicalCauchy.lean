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
import LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer
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

/-- The contour integral of a derivative of a composition F circ gamma over a
piecewise C^1 curve equals F(gamma(b)) - F(gamma(a)), when F is holomorphic
on a set containing the image of gamma.

Proof strategy: split the integral along partition points and apply the
standard FTC (`integral_eq_sub_of_hasDerivAt_of_le`) on each smooth subinterval.
On each subinterval [p_i, p_{i+1}], gamma is C^1 hence differentiable, so
F circ gamma has derivative f(gamma(t)) * gamma'(t) by the chain rule, and
the sum telescopes to F(gamma(b)) - F(gamma(a)). -/
private theorem ftc_piecewise_contour
    {F : ℂ → ℂ} {f : ℂ → ℂ}
    (γ : PiecewiseC1Curve) (U : Set ℂ) (hU : IsOpen U)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hF_prim : ∀ z ∈ U, HasDerivAt F (f z) z)
    (h_int : IntervalIntegrable
      (fun t => f (γ.toFun t) * deriv γ.toFun t) volume γ.a γ.b) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun γ.b) - F (γ.toFun γ.a) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  -- F ∘ γ is continuous on [a,b]: chain rule for continuity
  have hF_contOn : ContinuousOn F U :=
    fun z hz => (hF_prim z hz).continuousAt.continuousWithinAt
  have hFγ_cont : ContinuousOn (F ∘ γ.toFun) (Icc γ.a γ.b) :=
    hF_contOn.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht)
  -- The chain rule gives HasDerivAt (F ∘ γ) off partition
  have hFγ_deriv_off : ∀ t ∈ Ioo γ.a γ.b, t ∉ (↑γ.partition : Set ℝ) →
      HasDerivAt (F ∘ γ.toFun) (f (γ.toFun t) * deriv γ.toFun t) t := by
    intro t ht_Ioo ht_nP
    have ht_Icc : t ∈ Icc γ.a γ.b := Ioo_subset_Icc_self ht_Ioo
    convert (hF_prim (γ.toFun t) (hγ_in_U t ht_Icc)).comp_of_eq t
      (γ.smooth_off_partition t ht_Icc ht_nP).hasDerivAt rfl using 1
  -- Key helper: prove by induction on the number of interior partition points
  -- that FTC holds for any sub-interval [a', b'] ⊆ [γ.a, γ.b] with endpoints in partition
  have h_gen : ∀ (n : ℕ) (a' b' : ℝ),
      (γ.partition.filter (fun t => a' < t ∧ t < b')).card ≤ n →
      a' ≤ b' → Icc a' b' ⊆ Icc γ.a γ.b →
      a' ∈ γ.partition → b' ∈ γ.partition →
      ∫ t in a'..b', f (γ.toFun t) * deriv γ.toFun t =
        F (γ.toFun b') - F (γ.toFun a') := by
    intro n
    induction n with
    | zero =>
      intro a' b' hcard ha'b' hsub ha'P hb'P
      have ha'_bds := hsub (left_mem_Icc.mpr ha'b')
      have hb'_bds := hsub (right_mem_Icc.mpr ha'b')
      -- No interior partition points
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha'b'
        (hFγ_cont.mono hsub)
      · intro t ht
        have ht_Ioo_full : t ∈ Ioo γ.a γ.b :=
          ⟨lt_of_le_of_lt ha'_bds.1 ht.1, lt_of_lt_of_le ht.2 hb'_bds.2⟩
        apply hFγ_deriv_off t ht_Ioo_full
        intro ht_P
        have hmem : t ∈ γ.partition.filter (fun s => a' < s ∧ s < b') := by
          simp only [Finset.mem_filter]; exact ⟨ht_P, ht.1, ht.2⟩
        exact Finset.notMem_empty t (Finset.card_eq_zero.mp (Nat.le_zero.mp hcard) ▸ hmem)
      · exact h_int.mono_set (uIcc_subset_uIcc
          (Set.mem_uIcc_of_le ha'_bds.1 ha'_bds.2)
          (Set.mem_uIcc_of_le hb'_bds.1 hb'_bds.2))
    | succ m ih =>
      intro a' b' hcard ha'b' hsub ha'P hb'P
      have ha'_bds := hsub (left_mem_Icc.mpr ha'b')
      have hb'_bds := hsub (right_mem_Icc.mpr ha'b')
      by_cases hempty : γ.partition.filter (fun t => a' < t ∧ t < b') = ∅
      · -- No interior points: apply FTC directly
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ha'b'
          (hFγ_cont.mono hsub)
        · intro t ht
          have ht_Ioo_full : t ∈ Ioo γ.a γ.b :=
            ⟨lt_of_le_of_lt ha'_bds.1 ht.1, lt_of_lt_of_le ht.2 hb'_bds.2⟩
          apply hFγ_deriv_off t ht_Ioo_full
          intro ht_P
          have hmem : t ∈ γ.partition.filter (fun s => a' < s ∧ s < b') := by
            simp only [Finset.mem_filter]; exact ⟨ht_P, ht.1, ht.2⟩
          exact Finset.notMem_empty t (hempty ▸ hmem)
        · exact h_int.mono_set (uIcc_subset_uIcc
            (Set.mem_uIcc_of_le ha'_bds.1 ha'_bds.2)
            (Set.mem_uIcc_of_le hb'_bds.1 hb'_bds.2))
      · -- Pick an interior partition point c
        obtain ⟨c, hc_filt⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
        simp only [Finset.mem_filter] at hc_filt
        obtain ⟨hc_part, hac, hcb⟩ := hc_filt
        -- Split ∫_a'^b' = ∫_a'^c + ∫_c^b'
        have hac' : a' ≤ c := le_of_lt hac
        have hcb' : c ≤ b' := le_of_lt hcb
        have hc_bds : c ∈ Icc γ.a γ.b := hsub ⟨hac', hcb'⟩
        -- Integrabilities
        have h_int_ac : IntervalIntegrable
            (fun t => f (γ.toFun t) * deriv γ.toFun t) volume a' c :=
          h_int.mono_set (uIcc_subset_uIcc
            (Set.mem_uIcc_of_le ha'_bds.1 ha'_bds.2)
            (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2))
        have h_int_cb : IntervalIntegrable
            (fun t => f (γ.toFun t) * deriv γ.toFun t) volume c b' :=
          h_int.mono_set (uIcc_subset_uIcc
            (Set.mem_uIcc_of_le hc_bds.1 hc_bds.2)
            (Set.mem_uIcc_of_le hb'_bds.1 hb'_bds.2))
        -- Cards for sub-intervals are ≤ m
        -- c is in filter(a' < · < b') and not in filter(a' < · < c), so strict subset
        have hcard_ac : (γ.partition.filter (fun t => a' < t ∧ t < c)).card ≤ m := by
          have hstrict : γ.partition.filter (fun t => a' < t ∧ t < c) ⊂
              γ.partition.filter (fun t => a' < t ∧ t < b') := by
            constructor
            · intro t ht; simp only [Finset.mem_filter] at ht ⊢
              exact ⟨ht.1, ht.2.1, lt_trans ht.2.2 hcb⟩
            · intro hsub2
              have hcmem : c ∈ γ.partition.filter (fun t => a' < t ∧ t < b') := by
                simp only [Finset.mem_filter]; exact ⟨hc_part, hac, hcb⟩
              have hcmem2 := hsub2 hcmem
              simp only [Finset.mem_filter] at hcmem2
              exact lt_irrefl c hcmem2.2.2
          have hlt : (γ.partition.filter (fun t => a' < t ∧ t < c)).card
              < (γ.partition.filter (fun t => a' < t ∧ t < b')).card :=
            Finset.card_lt_card hstrict
          omega
        have hcard_cb : (γ.partition.filter (fun t => c < t ∧ t < b')).card ≤ m := by
          have hstrict : γ.partition.filter (fun t => c < t ∧ t < b') ⊂
              γ.partition.filter (fun t => a' < t ∧ t < b') := by
            constructor
            · intro t ht; simp only [Finset.mem_filter] at ht ⊢
              exact ⟨ht.1, lt_trans hac ht.2.1, ht.2.2⟩
            · intro hsub2
              have hcmem : c ∈ γ.partition.filter (fun t => a' < t ∧ t < b') := by
                simp only [Finset.mem_filter]; exact ⟨hc_part, hac, hcb⟩
              have hcmem2 := hsub2 hcmem
              simp only [Finset.mem_filter] at hcmem2
              exact lt_irrefl c hcmem2.2.1
          have hlt : (γ.partition.filter (fun t => c < t ∧ t < b')).card
              < (γ.partition.filter (fun t => a' < t ∧ t < b')).card :=
            Finset.card_lt_card hstrict
          omega
        -- Apply IH
        have h_ac := ih a' c hcard_ac hac'
          (fun t ht => hsub ⟨ht.1, le_trans ht.2 (le_of_lt hcb)⟩)
          ha'P hc_part
        have h_cb := ih c b' hcard_cb hcb'
          (fun t ht => hsub ⟨le_trans (le_of_lt hac) ht.1, ht.2⟩)
          hc_part hb'P
        rw [← intervalIntegral.integral_add_adjacent_intervals h_int_ac h_int_cb,
            h_ac, h_cb]; ring
  -- Apply h_gen to the full interval
  exact h_gen _ γ.a γ.b le_rfl hab (Subset.refl _)
    γ.endpoints_in_partition.1 γ.endpoints_in_partition.2

/-- The integrand (gamma(t) - z)^{-1} * gamma'(t) is interval integrable when z
is bounded away from the image of gamma.

Proof strategy: gamma is continuous on [a,b] and avoids z, so
|gamma(t) - z|^{-1} is bounded by compactness. The derivative deriv gamma
is bounded on [a,b] off the finite partition (piecewise continuous and
bounded on the compact interval). The product is therefore bounded and
piecewise continuous, hence integrable. -/
private theorem integrand_intervalIntegrable_of_avoids
    (γ : PiecewiseC1Immersion) (z : ℂ)
    (h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z) :
    IntervalIntegrable
      (fun t => (γ.toFun t - z)⁻¹ * deriv γ.toFun t) volume γ.a γ.b := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  -- The inverse factor is continuous on all of [a,b] since gamma avoids z
  have h_inv_cont : ContinuousOn (fun t => (γ.toFun t - z)⁻¹) (Icc γ.a γ.b) :=
    ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
      (fun t ht => sub_ne_zero.mpr (h_avoids t ht))
  -- Get bound for the inverse factor by compactness of image
  obtain ⟨M_inv, hM_inv⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (h_inv_cont.norm)
  -- Get a bound for deriv gamma on [a,b] using piecewiseC1Immersion_deriv_bounded
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  -- Now bound the product
  apply intervalIntegrable_of_piecewise_continuousOn_bounded
    (P := γ.partition) (M_inv * M_d) hab
  · -- ContinuousOn off partition
    intro t ⟨ht_Icc, ht_not_part⟩
    apply ContinuousWithinAt.mul
    · exact (h_inv_cont t ht_Icc).mono diff_subset
    · have ht_Ioo : t ∈ Ioo γ.a γ.b := by
        refine ⟨?_, ?_⟩
        · by_contra h_not_lt
          push_neg at h_not_lt
          have : t = γ.a := le_antisymm h_not_lt ht_Icc.1
          rw [this] at ht_not_part
          exact ht_not_part (γ.endpoints_in_partition.1)
        · by_contra h_not_lt
          push_neg at h_not_lt
          have : t = γ.b := le_antisymm ht_Icc.2 h_not_lt
          rw [this] at ht_not_part
          exact ht_not_part (γ.endpoints_in_partition.2)
      exact (γ.deriv_continuous_off_partition t ht_Ioo ht_not_part).continuousWithinAt
  · -- Bound
    intro t ht
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
theorem isNullHomologous_of_convex
    (U : Set ℂ) (hU : IsOpen U) (hU_convex : Convex ℝ U) (hU_ne : U.Nonempty)
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    IsNullHomologous γ U where
  closed := hγ_closed
  image_subset := hγ_in_U
  winding_zero := by
    intro z hz
    -- Step 1: z is not on the curve (since the curve is in U and z is not in U)
    have h_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z :=
      fun t ht heq => hz (heq ▸ hγ_in_U t ht)
    -- Step 2: Reduce PV winding number to classical integral
    have h_classical := generalizedWindingNumber_eq_classical_away
      γ.toPiecewiseC1Curve z h_avoids
    rw [h_classical]
    -- Step 3: The function w -> (w - z)^{-1} is holomorphic on U
    have h_ne_z : ∀ w ∈ U, w - z ≠ 0 :=
      fun w hw => sub_ne_zero.mpr (fun heq => hz (heq ▸ hw))
    have h_holo : DifferentiableOn ℂ (fun w => (w - z)⁻¹) U := by
      intro w hw
      exact ((differentiableAt_id.sub (differentiableAt_const z)).inv
        (h_ne_z w hw)).differentiableWithinAt
    -- Step 4: Get a primitive F on U via convexity
    obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU_convex hU hU_ne h_holo
    -- Step 5: Integrability (the integrand is bounded piecewise continuous)
    have h_int := integrand_intervalIntegrable_of_avoids γ z h_avoids
    -- Step 6: By FTC, integral = F(gamma(b)) - F(gamma(a))
    have h_ftc := ftc_piecewise_contour γ.toPiecewiseC1Curve U hU
      hγ_in_U hF h_int
    -- Step 7: gamma is closed, so F(gamma(b)) = F(gamma(a))
    have h_closed_val : F (γ.toFun γ.b) = F (γ.toFun γ.a) :=
      congrArg F hγ_closed.symm
    rw [h_ftc, h_closed_val, sub_self, mul_zero]

/-! ## Dixon's Proof of the Homological Cauchy Theorem

The Dixon kernel `g(z, w) = (f(z) - f(w))/(z - w)` (extended to `f'(w)` at `z = w`)
is exactly mathlib's `dslope f z w`. We use this identification throughout.

Key mathlib facts:
- `dslope_same f z = deriv f z`
- `dslope_of_ne f h z = (f z - f c)/(z - c)` for `z ≠ c`
- `continuousOn_dslope`: for fixed `c`, `z ↦ dslope f c z` is continuous iff `f` is continuous and differentiable at `c`
- `Complex.differentiableOn_dslope`: for fixed `c`, `z ↦ dslope f c z` is differentiable iff `f` is differentiable
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

/-- Key identity: h₁(w) = h₂(w) - 2πi · n(γ,w) · f(w) for w off the curve.
This follows from expanding dslope and splitting the integral. -/
theorem dixonH1_eq (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (w : ℂ) (hw : w ∈ U) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH1 f γ w = dixonH2 f γ w -
      2 * ↑Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w := by
  simp only [dixonH1, dixonH2]
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  -- Rewrite each dslope integrand pointwise: dslope f z w = f(z)/(z-w) - f(w)/(z-w)
  have hrewrite : ∀ t ∈ Set.uIcc γ.a γ.b,
      dslope f (γ.toFun t) w * deriv γ.toFun t =
        f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t -
          f w / (γ.toFun t - w) * deriv γ.toFun t := by
    intro t ht_ui
    have ht : t ∈ Icc γ.a γ.b := Set.uIcc_of_le hab ▸ ht_ui
    have hne : γ.toFun t ≠ w := hoff t ht
    have hne' : w ≠ γ.toFun t := Ne.symm hne
    have hsub : γ.toFun t - w ≠ 0 := sub_ne_zero.mpr hne
    have hwsub : w - γ.toFun t ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    rw [dslope_of_ne _ hne', slope_def_field]
    -- (f w - f(γ t)) / (w - γ t) * γ' = f(γ t)/(γ t - w)*γ' - f(w)/(γ t - w)*γ'
    rw [show w - γ.toFun t = -(γ.toFun t - w) from by ring]
    field_simp [hsub]
    ring
  rw [intervalIntegral.integral_congr hrewrite]
  -- Integrability of f(γ(t))/(γ(t)-w)*γ'(t) and f(w)/(γ(t)-w)*γ'(t)
  have h_base_int : IntervalIntegrable
      (fun t => (γ.toFun t - w)⁻¹ * deriv γ.toFun t) volume γ.a γ.b :=
    integrand_intervalIntegrable_of_avoids γ w hoff
  have h_fw_int : IntervalIntegrable
      (fun t => f w / (γ.toFun t - w) * deriv γ.toFun t) volume γ.a γ.b := by
    have heq : (fun t => f w / (γ.toFun t - w) * deriv γ.toFun t) =
        (fun t => f w * ((γ.toFun t - w)⁻¹ * deriv γ.toFun t)) := by
      ext t; rw [div_eq_mul_inv]; ring
    rw [heq]; exact h_base_int.const_mul _
  have h_fγ_int : IntervalIntegrable
      (fun t => f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) volume γ.a γ.b := by
    -- Obtain bound for 1/(γ(t)-w): max over compact Icc
    have h_inv_cont : ContinuousOn (fun t => (γ.toFun t - w)⁻¹) (Icc γ.a γ.b) :=
      ContinuousOn.inv₀ (γ.continuous_toFun.sub continuousOn_const)
        (fun t ht => sub_ne_zero.mpr (hoff t ht))
    obtain ⟨M_inv, hM_inv⟩ := isCompact_Icc.exists_bound_of_continuousOn h_inv_cont.norm
    simp only [Function.comp_def, norm_norm] at hM_inv
    -- Obtain bound for f(γ(t)) on [a,b]
    have hf_contOn_U : ContinuousOn f U :=
      fun z hz => ((hf z hz).differentiableAt (hU.mem_nhds hz)).continuousAt.continuousWithinAt
    have hf_cont_on : ContinuousOn (f ∘ γ.toFun) (Icc γ.a γ.b) :=
      hf_contOn_U.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht)
    obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn hf_cont_on.norm
    simp only [Function.comp_def, norm_norm] at hM_f
    obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
    apply intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition)
        (M_f * M_inv * M_d) hab
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
      have hM_inv' : ‖(γ.toFun t - w)⁻¹‖ ≤ M_inv := hM_inv t ht
      have hM_f' : ‖f (γ.toFun t)‖ ≤ M_f := hM_f t ht
      have hM_d' : ‖deriv γ.toFun t‖ ≤ M_d := hM_d t ht
      calc ‖f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖
          ≤ ‖f (γ.toFun t) / (γ.toFun t - w)‖ * ‖deriv γ.toFun t‖ := norm_mul_le _ _
        _ = ‖f (γ.toFun t)‖ * ‖(γ.toFun t - w)⁻¹‖ * ‖deriv γ.toFun t‖ := by
              rw [norm_div, norm_inv, div_eq_mul_inv]
        _ ≤ M_f * M_inv * M_d :=
              mul_le_mul (mul_le_mul hM_f' hM_inv' (norm_nonneg _)
                (le_trans (norm_nonneg _) hM_f'))
                hM_d' (norm_nonneg _)
                (mul_nonneg (le_trans (norm_nonneg _) hM_f')
                  (le_trans (norm_nonneg _) hM_inv'))
  -- Split: ∫ (fγ - fw) * ... = ∫ fγ * ... - ∫ fw * ...
  rw [intervalIntegral.integral_sub h_fγ_int h_fw_int]
  -- The second integral is 2πi * n * f(w)
  congr 1
  exact integral_singular_term_eq_winding_times_coeff γ.toPiecewiseC1Curve w (f w) hoff

-- Helper: the Cauchy integrand f(γt)/(γt-x)*γ'(t) is interval integrable when x avoids γ
private lemma dixonH2_integrand_integrable (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b))
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε)
    (x : ℂ) (hdist_lb : ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖)
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
    have hε_lb := hdist_lb t ht
    rw [norm_mul, norm_div]
    have hbound1 : ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖ ≤ M_f / ε :=
      calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖
          ≤ ‖f (γ.toFun t)‖ / ε :=
            div_le_div_of_nonneg_left (norm_nonneg _) hε_pos hε_lb
        _ ≤ M_f / ε := by gcongr; exact hM_f t ht
    calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - x‖ * ‖deriv γ.toFun t‖
        ≤ (M_f / ε) * M_d :=
          mul_le_mul hbound1 (hM_d t ht) (norm_nonneg _) (div_nonneg hM_f_nn hε_pos.le)
      _ = M_f * ε⁻¹ * M_d := by rw [div_eq_mul_inv]

-- Auxiliary: the Cauchy-type integral is holomorphic off the curve.
-- Uses let-bound F, F' so the kernel's whnf can stop at the abbreviation
-- rather than fully reducing the lambda expressions.
private noncomputable def dixonH2_F (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) :
    ℂ → ℝ → ℂ :=
  fun x t => f (γ.toFun t) * (γ.toFun t - x)⁻¹ * deriv γ.toFun t

private noncomputable def dixonH2_F' (f : ℂ → ℂ) (γ : PiecewiseC1Immersion) :
    ℂ → ℝ → ℂ :=
  fun x t => f (γ.toFun t) * (γ.toFun t - x)⁻¹ ^ 2 * deriv γ.toFun t

-- Helper: pointwise HasDerivAt for the Cauchy kernel integrand.
-- For fixed z, c: HasDerivAt (fun x => f(z) * (z-x)⁻¹ * c) (f(z) * (z-x)⁻²*c) x
private lemma dixonH2_pointwise_hasDerivAt (fz c : ℂ) (z x : ℂ) (hne : z - x ≠ 0) :
    HasDerivAt (fun x => fz * (z - x)⁻¹ * c) (fz * (z - x)⁻¹ ^ 2 * c) x := by
  have h1 : HasDerivAt (fun x => z - x) (-1) x := by
    have hid := hasDerivAt_id x
    have hconst := hasDerivAt_const x z
    convert hconst.sub hid using 1
    simp
  have h2 : HasDerivAt (fun x => (z - x)⁻¹) (-(-1) / (z - x) ^ 2) x :=
    h1.fun_inv hne
  simp only [neg_neg, one_div] at h2
  -- h2 : HasDerivAt (fun x => (z-x)⁻¹) ((z-x)^2)⁻¹ x
  have h3 : HasDerivAt (fun x => fz * (z - x)⁻¹) (fz * ((z - x) ^ 2)⁻¹) x := by
    have h3a := h2.const_mul fz
    -- h3a : HasDerivAt (fun y => fz * (z-y)⁻¹) (fz * ((z-x)^2)⁻¹) x
    convert h3a using 1 <;> ring
  have h4 : HasDerivAt (fun x => fz * (z - x)⁻¹ * c) (fz * ((z - x) ^ 2)⁻¹ * c) x :=
    h3.mul_const c
  convert h4 using 1
  rw [inv_pow]

-- Helper: the derivative bound ‖F'(x,t)‖ ≤ M_f * ε⁻²  * M_d for x in the ball.
private lemma dixonH2_deriv_bound (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (M_f M_d ε : ℝ) (hM_f : ∀ t ∈ Icc γ.a γ.b, ‖f (γ.toFun t)‖ ≤ M_f)
    (hM_d : ∀ t ∈ Icc γ.a γ.b, ‖deriv γ.toFun t‖ ≤ M_d)
    (hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε)
    (w : ℂ)
    (hdist_lb : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖) :
    ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε,
        ‖f (γ.toFun t) * (γ.toFun t - x)⁻¹ ^ 2 * deriv γ.toFun t‖ ≤
          M_f * ε⁻¹ ^ 2 * M_d := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  filter_upwards with t _ht x hx_ball
  have ht : t ∈ Icc γ.a γ.b := by
    rw [Set.uIoc_of_le hab] at _ht
    exact Set.Ioc_subset_Icc_self _ht
  have hε_lb := hdist_lb x hx_ball t ht
  rw [norm_mul, norm_mul, norm_pow, norm_inv]
  have hinv_bound : ‖γ.toFun t - x‖⁻¹ ≤ ε⁻¹ :=
    inv_anti₀ hε_pos hε_lb
  calc ‖f (γ.toFun t)‖ * ‖γ.toFun t - x‖⁻¹ ^ 2 * ‖deriv γ.toFun t‖
      ≤ M_f * ε⁻¹ ^ 2 * M_d := by
        apply mul_le_mul
        · apply mul_le_mul
          · exact hM_f t ht
          · exact pow_le_pow_left₀ (by positivity) hinv_bound 2
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
    (_hM_f_nn : 0 ≤ M_f) (hε_pos : 0 < ε)
    (w : ℂ)
    (_hdist_lb_w : ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - w‖)
    (_hball_avoids : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x)
    (_hdist_lb : ∀ x ∈ Metric.ball w ε, ∀ t ∈ Icc γ.a γ.b, ε ≤ ‖γ.toFun t - x‖) :
    HasDerivAt (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - w)⁻¹ * deriv γ.toFun t)
      (∫ t in γ.a..γ.b, f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t) w := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  -- Build all hypotheses for hasDerivAt_integral_of_dominated_loc_of_deriv_le separately
  -- to avoid expensive unification in one monolithic call.
  -- Step 1: integrand F(w,·) is interval integrable
  have hav_w : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w :=
    fun t ht => _hball_avoids w (Metric.mem_ball_self hε_pos) t ht
  have hF_int : IntervalIntegrable (dixonH2_F f γ w) volume γ.a γ.b := by
    have heq : dixonH2_F f γ w =
        fun t => f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t := by
      ext t; simp [dixonH2_F, div_eq_mul_inv]
    rw [heq]
    exact dixonH2_integrand_integrable f γ hfγ_cont M_f M_d ε
      hM_f hM_d _hM_f_nn hε_pos w _hdist_lb_w hav_w
  -- Step 2: F(x,·) is AE strongly measurable for x near w
  have hF_meas : ∀ᶠ x in 𝓝 w,
      AEStronglyMeasurable (dixonH2_F f γ x) (volume.restrict (Set.uIoc γ.a γ.b)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds w hε_pos)
    intro x hx
    have hint_x : IntervalIntegrable (dixonH2_F f γ x) volume γ.a γ.b := by
      have heq : dixonH2_F f γ x =
          fun t => f (γ.toFun t) / (γ.toFun t - x) * deriv γ.toFun t := by
        ext t; simp [dixonH2_F, div_eq_mul_inv]
      rw [heq]
      exact dixonH2_integrand_integrable f γ hfγ_cont M_f M_d ε
        hM_f hM_d _hM_f_nn hε_pos x (fun t ht => _hdist_lb x hx t ht)
        (fun t ht => _hball_avoids x hx t ht)
    exact hint_x.def'.aestronglyMeasurable
  -- Step 3: F'(w,·) is interval integrable and hence AE strongly measurable
  have hF'_int : IntervalIntegrable (dixonH2_F' f γ w) volume γ.a γ.b := by
    apply intervalIntegrable_of_piecewise_continuousOn_bounded
        (P := γ.partition) (M_f * ε⁻¹ ^ 2 * M_d) hab
    · intro t ⟨ht_Icc, ht_npart⟩
      -- dixonH2_F' unfolds to the lambda by rfl
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
      -- dixonH2_F' w t unfolds to the lambda by rfl
      change ‖f (γ.toFun t) * (γ.toFun t - w)⁻¹ ^ 2 * deriv γ.toFun t‖ ≤ M_f * ε⁻¹ ^ 2 * M_d
      rw [norm_mul, norm_mul, norm_pow, norm_inv]
      exact mul_le_mul
        (mul_le_mul (hM_f t ht)
          (pow_le_pow_left₀ (by positivity) (inv_anti₀ hε_pos (_hdist_lb_w t ht)) 2)
          (by positivity) _hM_f_nn)
        (hM_d t ht) (by positivity) (mul_nonneg _hM_f_nn (by positivity))
  have hF'_meas : AEStronglyMeasurable (dixonH2_F' f γ w) (volume.restrict (Set.uIoc γ.a γ.b)) :=
    hF'_int.def'.aestronglyMeasurable
  -- Step 4: Derivative bound (via dixonH2_deriv_bound)
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε, ‖dixonH2_F' f γ x t‖ ≤ M_f * ε⁻¹ ^ 2 * M_d :=
    dixonH2_deriv_bound f γ M_f M_d ε hM_f hM_d _hM_f_nn hε_pos w _hdist_lb
  -- Step 5: Bound is interval integrable
  have hbound_int : IntervalIntegrable (fun _ => M_f * ε⁻¹ ^ 2 * M_d) volume γ.a γ.b :=
    intervalIntegral.intervalIntegrable_const
  -- Step 6: Pointwise HasDerivAt (via dixonH2_pointwise_hasDerivAt)
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w ε,
        HasDerivAt (fun x => dixonH2_F f γ x t) (dixonH2_F' f γ x t) x := by
    filter_upwards with t _ht x hx_ball
    have ht' : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Set.Ioc_subset_Icc_self _ht
    simp only [dixonH2_F, dixonH2_F']
    exact dixonH2_pointwise_hasDerivAt (f (γ.toFun t)) (deriv γ.toFun t) (γ.toFun t) x
      (sub_ne_zero.mpr (_hball_avoids x hx_ball t ht'))
  -- Step 7: Apply the parametric differentiation theorem
  have hmain := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε_pos hF_meas hF_int hF'_meas h_bound hbound_int h_diff).2
  convert hmain using 2 <;>
  · congr 1; ext t; simp [dixonH2_F, dixonH2_F', div_eq_mul_inv]

/-- h₂ is differentiable at every point off the curve, when f is continuous on the image. -/
theorem dixonH2_differentiableAt (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (hf_cont : ContinuousOn f (γ.toFun '' Icc γ.a γ.b))
    (w : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    DifferentiableAt ℂ (dixonH2 f γ) w := by
  show DifferentiableAt ℂ
      (fun w => ∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t) w
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  -- w is not in the image, so there is a positive lower distance bound
  have himage_closed : IsClosed (γ.toFun '' Icc γ.a γ.b) :=
    (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isClosed
  have himage_ne : (γ.toFun '' Icc γ.a γ.b).Nonempty :=
    ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr hab, rfl⟩
  have hw_notmem : w ∉ γ.toFun '' Icc γ.a γ.b :=
    fun ⟨t, ht, heq⟩ => hoff t ht heq
  -- Define ε as half the infimum distance
  have hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b) :=
    (himage_closed.notMem_iff_infDist_pos himage_ne).mp hw_notmem
  -- Gather all needed bounds before applying dixonH2_hasDerivAt
  have hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b) :=
    hf_cont.comp γ.continuous_toFun (fun t ht => ⟨t, ht, rfl⟩)
  obtain ⟨M_f, hM_f_spec⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ_cont.norm
  simp only [norm_norm] at hM_f_spec
  obtain ⟨M_d, hM_d_spec⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hM_f_nn : 0 ≤ M_f := le_trans (norm_nonneg _) (hM_f_spec γ.a (left_mem_Icc.mpr hab))
  have hε : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 > 0 := by linarith
  -- hdist_lb_w
  have hdist_lb_w : ∀ t ∈ Icc γ.a γ.b,
      Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ ‖γ.toFun t - w‖ := by
    intro t ht
    have hmem : γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b := ⟨t, ht, rfl⟩
    have hid : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) ≤ dist w (γ.toFun t) :=
      Metric.infDist_le_dist_of_mem hmem
    have hdist_eq : dist w (γ.toFun t) = ‖γ.toFun t - w‖ := by
      rw [Complex.dist_eq, ← norm_neg (w - γ.toFun t), neg_sub]
    have hinfDist_nn : 0 ≤ Metric.infDist w (γ.toFun '' Icc γ.a γ.b) :=
      Metric.infDist_nonneg
    linarith [hdist_eq ▸ hid]
  -- hball_avoids
  have hball_avoids : ∀ x ∈ Metric.ball w (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2),
      ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x := by
    intro x hx t ht heq
    have hmem : x ∈ γ.toFun '' Icc γ.a γ.b := ⟨t, ht, heq⟩
    have h1 : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) ≤ dist w x :=
      Metric.infDist_le_dist_of_mem hmem
    have h3 : dist w x < Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 := by
      rw [dist_comm]; exact Metric.mem_ball.mp hx
    linarith
  -- hdist_lb
  have hdist_lb : ∀ x ∈ Metric.ball w (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2),
      ∀ t ∈ Icc γ.a γ.b, Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ ‖γ.toFun t - x‖ := by
    intro x hx t ht
    have hmem : γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b := ⟨t, ht, rfl⟩
    have hid : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) ≤ dist w (γ.toFun t) :=
      Metric.infDist_le_dist_of_mem hmem
    have hx_lt : dist x w < Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 :=
      Metric.mem_ball.mp hx
    have htri := dist_triangle w x (γ.toFun t)
    rw [dist_comm w x] at htri
    have h1 : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 ≤ dist x (γ.toFun t) := by linarith
    rw [Complex.dist_eq, ← norm_neg (x - γ.toFun t), neg_sub] at h1
    exact h1
  -- Apply dixonH2_hasDerivAt
  exact (dixonH2_hasDerivAt f γ hfγ_cont M_f M_d
    (Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2)
    hM_f_spec hM_d_spec hM_f_nn hε w hdist_lb_w hball_avoids hdist_lb).differentiableAt

/-- Uniform bound on dslope: for c in a compact set K ⊂ U and w in a ball B ⊂ U,
‖dslope f c w‖ is bounded. Uses MVT on convex balls for nearby points and
triangle inequality for distant points. -/
private lemma dslope_uniform_bound (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (K : Set ℂ) (hK_compact : IsCompact K) (hK_sub : K ⊆ U)
    (w₀ : ℂ) (hw₀ : w₀ ∈ U) :
    ∃ C > 0, ∃ δ > 0, ∀ c ∈ K, ∀ w ∈ Metric.ball w₀ δ,
      ‖dslope f c w‖ ≤ C := by
  -- Choose r with ball(w₀, r) ⊂ U
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  -- Bound ‖f‖ on K ∪ closedBall(w₀, r/2)
  have hcb_sub : Metric.closedBall w₀ (r / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hr_sub
  obtain ⟨M_f, hM_f⟩ := (hK_compact.union (isCompact_closedBall w₀ (r / 2))).exists_bound_of_continuousOn
    (hf.continuousOn.mono (Set.union_subset hK_sub hcb_sub) |>.norm)
  -- Bound ‖deriv f‖ on closedBall(w₀, r/2)
  have hderiv_cont : ContinuousOn (deriv f) (Metric.closedBall w₀ (r / 2)) :=
    ((hf.mono hr_sub).deriv Metric.isOpen_ball).continuousOn.mono
      (Metric.closedBall_subset_ball (by linarith))
  obtain ⟨C_d, hC_d⟩ := (isCompact_closedBall w₀ (r / 2)).exists_bound_of_continuousOn hderiv_cont
  -- Set δ = r/4, C = max(C_d+1, 8*M_f/r + 1)
  have hr4_pos : (0 : ℝ) < r / 4 := by linarith
  refine ⟨max (C_d + 1) (8 * (|M_f| + 1) / r + 1), by positivity,
    r / 4, hr4_pos, fun c hc w hw => ?_⟩
  by_cases hcw : c = w
  · -- c = w: dslope = deriv f c
    subst hcw; rw [dslope_same]
    have hc_cb : c ∈ Metric.closedBall w₀ (r / 2) :=
      Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
        (Metric.ball_subset_closedBall hw)
    calc ‖deriv f c‖ ≤ C_d := hC_d c hc_cb
      _ ≤ C_d + 1 := by linarith
      _ ≤ _ := le_max_left _ _
  · -- c ≠ w: dslope = slope = (f w - f c)/(w - c)
    have hne : w ≠ c := fun h => hcw h.symm
    rw [dslope_of_ne _ hne, slope_def_field, norm_div]
    by_cases hc_near : c ∈ Metric.closedBall w₀ (r / 2)
    · -- Both in convex ball → MVT
      have hw_cb : w ∈ Metric.closedBall w₀ (r / 2) :=
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
    · -- c far from w₀ → ‖w - c‖ ≥ r/4
      have hc_far : r / 2 < dist c w₀ := by
        rwa [Metric.mem_closedBall, not_le] at hc_near
      have hw_dist := Metric.mem_ball.mp hw
      have h_sep : r / 4 ≤ ‖w - c‖ := by
        have : r / 2 < dist c w₀ := hc_far
        rw [dist_comm] at this
        calc r / 4 = r / 2 - r / 4 := by ring
          _ ≤ dist w₀ c - dist w w₀ := by linarith [hw_dist]
          _ ≤ dist w c := by
              have := dist_triangle_left c w₀ w
              rw [dist_comm w₀ c]; linarith
          _ = ‖w - c‖ := by rw [dist_eq_norm]
      have hw_cb : w ∈ Metric.closedBall w₀ (r / 2) :=
        Metric.closedBall_subset_closedBall (by linarith : r / 4 ≤ r / 2)
          (Metric.ball_subset_closedBall hw)
      simp only [norm_norm] at hM_f
      have h1 : ‖f w‖ ≤ M_f := hM_f w (Or.inr hw_cb)
      have h2 : ‖f c‖ ≤ M_f := hM_f c (Or.inl hc)
      have hM_f_nn : 0 ≤ M_f := le_trans (norm_nonneg _) h1
      have h_num : ‖f w - f c‖ ≤ 2 * M_f := by linarith [norm_sub_le (f w) (f c)]
      have h_denom_pos : (0 : ℝ) < ‖w - c‖ := lt_of_lt_of_le (by linarith) h_sep
      have h_step1 : ‖f w - f c‖ / ‖w - c‖ ≤ 2 * M_f / ‖w - c‖ :=
        div_le_div_of_nonneg_right h_num (le_of_lt h_denom_pos)
      have h_step2 : 2 * M_f / ‖w - c‖ ≤ 2 * M_f / (r / 4) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) h_sep
      have h_eq : 2 * M_f / (r / 4) = 8 * M_f / r := by ring
      have h_le : 8 * M_f / r ≤ 8 * (|M_f| + 1) / r + 1 := by
        rw [abs_of_nonneg hM_f_nn]
        have hr_nn : (0 : ℝ) < r := hr_pos
        have : 8 * M_f / r + 8 / r + 1 = 8 * (M_f + 1) / r + 1 := by ring
        linarith [div_nonneg (show (0:ℝ) ≤ 8 by norm_num) hr_pos.le]
      exact le_trans (le_trans h_step1 h_step2) (le_trans (h_eq ▸ le_refl _)
        (le_trans h_le (le_max_right _ _)))

set_option maxHeartbeats 8000000 in
/-- h₁ is differentiable on all of U, including across the curve.
Uses the Leibniz rule (parametric differentiation of the dslope integral). -/
theorem dixonH1_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    DifferentiableOn ℂ (dixonH1 f γ) U := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  have hdslope_diff : ∀ t ∈ Icc γ.a γ.b,
      DifferentiableOn ℂ (dslope f (γ.toFun t)) U :=
    fun t ht => (differentiableOn_dslope (hU.mem_nhds (hγ_in_U t ht))).mpr hf
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hγ_compact := isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  have hγ_sub : γ.toFun '' Icc γ.a γ.b ⊆ U :=
    fun _ ⟨t, ht, he⟩ => he ▸ hγ_in_U t ht
  -- t ↦ dslope f (γ t) x is continuous on [a,b] for any fixed x : ℂ
  have hdslope_t_cont : ∀ x : ℂ,
      ContinuousOn (fun t => dslope f (γ.toFun t) x) (Icc γ.a γ.b) := by
    intro x
    by_cases hx : x ∈ U
    · have h_eq : ∀ t ∈ Icc γ.a γ.b, dslope f (γ.toFun t) x = dslope f x (γ.toFun t) := by
        intro t ht
        by_cases h : γ.toFun t = x
        · subst h; simp
        · simp only [dslope_of_ne _ (Ne.symm h), dslope_of_ne _ h]
          exact slope_comm f (γ.toFun t) x
      apply ContinuousOn.congr _ h_eq
      have h_dslope_cont : ContinuousOn (dslope f x) U :=
        (continuousOn_dslope (hU.mem_nhds hx)).mpr
          ⟨hf.continuousOn, (hf x hx).differentiableAt (hU.mem_nhds hx)⟩
      exact h_dslope_cont.comp γ.continuous_toFun (fun t ht => hγ_in_U t ht)
    · have hne : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ x :=
        fun t ht heq => hx (heq ▸ hγ_in_U t ht)
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
  -- For each w₀ ∈ U, prove HasDerivAt (dixonH1 f γ) D w₀ via the Leibniz rule
  intro w₀ hw₀
  apply DifferentiableAt.differentiableWithinAt
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU w₀ hw₀
  obtain ⟨C, hC_pos, δ₀, hδ₀_pos, hBd⟩ :=
    dslope_uniform_bound hU hf _ hγ_compact hγ_sub w₀ hw₀
  -- ε = min(δ₀, r)/2 ensures closedBall x ε ⊆ U for all x ∈ ball w₀ ε
  set ε := min δ₀ r / 2 with hε_def
  have hε_pos : 0 < ε := by positivity
  have h2ε_le_δ₀ : 2 * ε ≤ δ₀ := by simp only [hε_def]; linarith [min_le_left δ₀ r]
  have h2ε_le_r : 2 * ε ≤ r := by simp only [hε_def]; linarith [min_le_right δ₀ r]
  have hcb_U : ∀ x ∈ Metric.ball w₀ ε, Metric.closedBall x ε ⊆ U := fun x hx y hy => by
    apply hr_sub; rw [Metric.mem_ball] at hx ⊢
    have hy' := Metric.mem_closedBall.mp hy
    linarith [dist_triangle y x w₀]
  -- Cauchy estimate: ‖deriv (dslope f (γ t)) x‖ ≤ C / ε for x ∈ ball w₀ ε
  have hCauchy : ∀ t ∈ Icc γ.a γ.b, ∀ x ∈ Metric.ball w₀ ε,
      ‖deriv (dslope f (γ.toFun t)) x‖ ≤ C / ε := by
    intro t ht x hx
    apply norm_deriv_le_of_forall_mem_sphere_norm_le hε_pos
    · exact (hdslope_diff t ht).diffContOnCl_ball (hcb_U x hx)
    · intro z hz
      apply hBd _ ⟨t, ht, rfl⟩
      rw [Metric.mem_ball] at hx ⊢; rw [Metric.mem_sphere] at hz
      linarith [dist_triangle z x w₀]
  -- Step 1: F(w₀,·) = dslope f (γ t) w₀ * γ'(t) is interval integrable
  have hF_int : IntervalIntegrable
      (fun t => dslope f (γ.toFun t) w₀ * deriv γ.toFun t) volume γ.a γ.b := by
    apply intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition) (C * M_d) hab
    · intro t ⟨ht_Icc, ht_np⟩
      have ht_Ioo : t ∈ Ioo γ.a γ.b := ⟨by
        by_contra h; push_neg at h
        exact ht_np (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1), by
        by_contra h; push_neg at h
        exact ht_np (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)⟩
      exact (hdslope_t_cont w₀ t ht_Icc |>.mono diff_subset).mul
        (γ.deriv_continuous_off_partition t ht_Ioo ht_np).continuousWithinAt
    · intro t ht
      rw [norm_mul]
      exact mul_le_mul (hBd _ ⟨t, ht, rfl⟩ w₀ (Metric.mem_ball_self hδ₀_pos))
        (hM_d t ht) (norm_nonneg _) hC_pos.le
  -- Step 2: F(x,·) is AE strongly measurable for x near w₀
  have hF_meas : ∀ᶠ x in 𝓝 w₀,
      AEStronglyMeasurable (fun t => dslope f (γ.toFun t) x * deriv γ.toFun t)
        (volume.restrict (Set.uIoc γ.a γ.b)) := by
    apply Filter.eventually_of_mem (Metric.ball_mem_nhds w₀ hε_pos)
    intro x hx
    have hx_ball_δ₀ : x ∈ Metric.ball w₀ δ₀ := Metric.ball_subset_ball (by linarith) hx
    exact (intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition) (C * M_d) hab
      (fun t ⟨ht_Icc, ht_np⟩ => by
        have ht_Ioo : t ∈ Ioo γ.a γ.b := ⟨by
          by_contra h; push_neg at h
          exact ht_np (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1), by
          by_contra h; push_neg at h
          exact ht_np (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)⟩
        exact (hdslope_t_cont x t ht_Icc |>.mono diff_subset).mul
          (γ.deriv_continuous_off_partition t ht_Ioo ht_np).continuousWithinAt)
      (fun t ht => by
        rw [norm_mul]
        exact mul_le_mul (hBd _ ⟨t, ht, rfl⟩ x hx_ball_δ₀) (hM_d t ht)
          (norm_nonneg _) hC_pos.le)).def'.aestronglyMeasurable
  -- Step 3: F'(w₀,·) = deriv(dslope f (γ t)) w₀ * γ'(t) is AE strongly measurable
  -- Use finite-difference approximants via aestronglyMeasurable_of_tendsto_ae
  have hF'_meas : AEStronglyMeasurable
      (fun t => deriv (dslope f (γ.toFun t)) w₀ * deriv γ.toFun t)
      (volume.restrict (Set.uIoc γ.a γ.b)) := by
    -- Define Gn n t = (n+1) * (dslope f (γt) (w₀ + 1/(n+1)) - dslope f (γt) w₀) * γ'(t)
    -- This is a finite-difference approximation to deriv(dslope f (γ t)) w₀ * γ'(t)
    refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop (α := ℕ))
        (f := fun n t => ((↑n + 1 : ℂ)) * (dslope f (γ.toFun t) (w₀ + 1 / (↑n + 1)) -
          dslope f (γ.toFun t) w₀) * deriv γ.toFun t) ?_ ?_
    · -- Each approximant is AE strongly measurable (piecewise continuous)
      intro n
      obtain ⟨M_n, hM_n⟩ := isCompact_Icc.exists_bound_of_continuousOn
        ((hdslope_t_cont (w₀ + 1 / ((n : ℂ) + 1))).norm)
      simp only [norm_norm] at hM_n
      exact (intervalIntegrable_of_piecewise_continuousOn_bounded (P := γ.partition)
        (‖(n : ℂ) + 1‖ * (M_n + C) * M_d) hab
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
              dslope f (γ.toFun t) w₀‖ ≤ M_n + C :=
            le_trans (norm_sub_le _ _)
              (add_le_add (hM_n t ht) (hBd _ ⟨t, ht, rfl⟩ w₀ (Metric.mem_ball_self hδ₀_pos)))
          have h2 : ‖deriv γ.toFun t‖ ≤ M_d := hM_d t ht
          exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
            h2 (norm_nonneg _) (mul_nonneg (norm_nonneg _) (le_trans (norm_nonneg _) h1))
          )).def'.aestronglyMeasurable
    · -- AE convergence: Gn n t → deriv(dslope f(γ t)) w₀ * γ'(t)
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht_Icc : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self ht
      have hderiv : HasDerivAt (dslope f (γ.toFun t)) (deriv (dslope f (γ.toFun t)) w₀) w₀ :=
        ((hdslope_diff t ht_Icc).differentiableAt (hU.mem_nhds hw₀)).hasDerivAt
      -- h_n = (1:ℂ)/(n+1) → 0, ≠ 0
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
      -- Gn n t = (1/(n+1))⁻¹ • (dslope f (γt) (w₀ + 1/(n+1)) - dslope f (γt) w₀) * γ'(t)
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
  -- Step 4: Derivative bound ‖F'‖ ≤ C/ε * M_d
  have h_bound : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w₀ ε,
        ‖deriv (dslope f (γ.toFun t)) x * deriv γ.toFun t‖ ≤ C / ε * M_d := by
    filter_upwards with t _ht x hx
    have ht_Icc : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    rw [norm_mul]
    exact mul_le_mul (hCauchy t ht_Icc x hx) (hM_d t ht_Icc) (norm_nonneg _)
      (div_nonneg hC_pos.le hε_pos.le)
  -- Step 5: Pointwise HasDerivAt (F x t) = F' x t
  have h_diff : ∀ᵐ t ∂volume, t ∈ Set.uIoc γ.a γ.b →
      ∀ x ∈ Metric.ball w₀ ε,
        HasDerivAt (fun x => dslope f (γ.toFun t) x * deriv γ.toFun t)
          (deriv (dslope f (γ.toFun t)) x * deriv γ.toFun t) x := by
    filter_upwards with t _ht x hx
    have ht_Icc : t ∈ Icc γ.a γ.b := by
      rw [Set.uIoc_of_le hab] at _ht; exact Ioc_subset_Icc_self _ht
    have hx_U : x ∈ U := hr_sub (Metric.ball_subset_ball (by linarith : ε ≤ r) hx)
    exact ((hdslope_diff t ht_Icc).differentiableAt (hU.mem_nhds hx_U) |>.hasDerivAt).mul_const _
  -- Apply Leibniz rule (dixonH1 f γ = fun w => ∫ ... by definition)
  exact ((intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε_pos hF_meas hF_int hF'_meas h_bound intervalIntegral.intervalIntegrable_const h_diff).2).differentiableAt

/-- The Dixon function: h₁ on U, h₂ on ℂ \ U. -/
noncomputable def dixonFunction (f : ℂ → ℂ) (U : Set ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  if _h : w ∈ U then dixonH1 f γ w else dixonH2 f γ w

set_option maxHeartbeats 800000 in
/-- The Dixon function is entire (differentiable on all of ℂ).
On U: it's h₁, holomorphic by dixonH1_differentiableOn.
On ℂ \ U: it's h₂, holomorphic by dixonH2_differentiableAt.
Patching at ∂U: null-homologous gives n(γ,w) = 0 near ∂U, so h₁ = h₂ there. -/
theorem dixonFunction_differentiable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    Differentiable ℂ (dixonFunction f U γ) := by
  intro w
  by_cases hw : w ∈ U
  · -- w ∈ U: dixonFunction agrees with dixonH1 on U, holomorphic by dixonH1_differentiableOn
    have h_eq : ∀ᶠ w' in 𝓝 w, dixonFunction f U γ w' = dixonH1 f γ w' :=
      Filter.Eventually.mono (hU.mem_nhds hw)
        (fun w' hw' => by simp only [dixonFunction]; exact if_pos hw')
    exact ((dixonH1_differentiableOn hU hf γ h_null.image_subset).differentiableAt
      (hU.mem_nhds hw)).congr_of_eventuallyEq h_eq
  · -- w ∉ U: w is off the curve (since image(γ) ⊆ U)
    have hab : γ.a ≤ γ.b := le_of_lt γ.hab
    have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w :=
      fun t ht heq => hw (heq ▸ h_null.image_subset t ht)
    -- Get ε > 0 with ball(w, ε) disjoint from image(γ)
    have himage_compact : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
      isCompact_Icc.image_of_continuousOn γ.continuous_toFun
    have himage_closed : IsClosed (γ.toFun '' Icc γ.a γ.b) := himage_compact.isClosed
    have himage_ne : (γ.toFun '' Icc γ.a γ.b).Nonempty :=
      ⟨γ.toFun γ.a, γ.a, left_mem_Icc.mpr hab, rfl⟩
    have hw_notmem : w ∉ γ.toFun '' Icc γ.a γ.b :=
      fun ⟨t, ht, heq⟩ => hoff t ht heq
    have hinfDist_pos : 0 < Metric.infDist w (γ.toFun '' Icc γ.a γ.b) :=
      (himage_closed.notMem_iff_infDist_pos himage_ne).mp hw_notmem
    set ε := Metric.infDist w (γ.toFun '' Icc γ.a γ.b) / 2 with hε_def
    have hε_pos : 0 < ε := by positivity
    -- ball(w, ε) avoids the curve
    have hball_avoids : ∀ t ∈ Icc γ.a γ.b, ∀ w' ∈ Metric.ball w ε, γ.toFun t ≠ w' := by
      intro t ht w' hw' heq
      have hmem : w' ∈ γ.toFun '' Icc γ.a γ.b := ⟨t, ht, heq⟩
      have h1 : Metric.infDist w (γ.toFun '' Icc γ.a γ.b) ≤ dist w w' :=
        Metric.infDist_le_dist_of_mem hmem
      have h2 : dist w' w < ε := Metric.mem_ball.mp hw'
      rw [dist_comm] at h2
      linarith
    -- Winding number on ball(w, ε) is continuous (via classical integral formula)
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
          convert h using 2; simp [dixonH2, div_eq_mul_inv]
        exact hdiff2.continuousAt.continuousWithinAt
      · intro w' hw'
        have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' :=
          fun t ht heq => hball_avoids t ht w' hw' heq
        exact generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve w' hoff'
    -- Winding number at w is 0 by h_null
    have hwn_w : generalizedWindingNumber' γ.toFun γ.a γ.b w = 0 := h_null.winding_zero w hw
    -- Winding number is ℤ-valued on the ball
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
    -- Winding number = 0 on all of ball(w, ε): integer-valued + continuous + connected + 0 at w
    have hwn_zero_ball : ∀ w' ∈ Metric.ball w ε,
        generalizedWindingNumber' γ.toFun γ.a γ.b w' = 0 := by
      haveI hpreconn : PreconnectedSpace (Metric.ball w ε) :=
        isPreconnected_iff_preconnectedSpace.mp (Metric.isConnected_ball hε_pos).isPreconnected
      have hwn_cts_sub : Continuous
          (fun w'' : Metric.ball w ε =>
            generalizedWindingNumber' γ.toFun γ.a γ.b w''.val) :=
        hwn_cts.comp_continuous continuous_subtype_val (fun w'' => w''.2)
      -- Define ℤ-valued winding number on the subtype
      let wn_Z : Metric.ball w ε → ℤ := fun w'' => (hwn_int w'' w''.2).choose
      have wn_Z_cast : ∀ w'' : Metric.ball w ε,
          (wn_Z w'' : ℂ) = generalizedWindingNumber' γ.toFun γ.a γ.b w''.val :=
        fun w'' => (hwn_int w'' w''.2).choose_spec.symm
      -- wn_Z is locally constant, hence continuous (ℤ discrete)
      have wn_Z_cont : Continuous wn_Z := by
        rw [← IsLocallyConstant.iff_continuous, IsLocallyConstant.iff_eventually_eq]
        intro ⟨w'', hw''⟩
        have hwn_cts_at : ContinuousAt
            (fun w''' : Metric.ball w ε =>
              generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val) ⟨w'', hw''⟩ :=
          hwn_cts_sub.continuousAt
        -- On a neighborhood, wn is within 1/2 of wn(w'')
        have hev : ∀ᶠ w''' : Metric.ball w ε in 𝓝 ⟨w'', hw''⟩,
            ‖generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val -
              generalizedWindingNumber' γ.toFun γ.a γ.b w''‖ < 1 / 2 := by
          have h_nbhd : ∀ᶠ w''' : Metric.ball w ε in 𝓝 ⟨w'', hw''⟩,
              generalizedWindingNumber' γ.toFun γ.a γ.b w'''.val ∈
                Metric.ball (generalizedWindingNumber' γ.toFun γ.a γ.b w'') (1/2) :=
            hwn_cts_at (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
          exact h_nbhd.mono fun w''' h_mem =>
            (Complex.dist_eq _ _).symm ▸ Metric.mem_ball.mp h_mem
        -- Integer difference has norm < 1/2, so must be 0
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
      -- wn_Z at w is 0
      have hwn_Z_w : wn_Z ⟨w, Metric.mem_ball_self hε_pos⟩ = 0 := by
        apply Int.cast_injective (α := ℂ); push_cast; rw [wn_Z_cast]; exact hwn_w
      -- By preconnectedness, wn_Z is constant
      intro w' hw'
      obtain ⟨n, hn⟩ := hwn_int w' hw'
      have h_wn_Z : wn_Z ⟨w', hw'⟩ = 0 :=
        (PreconnectedSpace.constant hpreconn wn_Z_cont
          (x := ⟨w', hw'⟩) (y := ⟨w, Metric.mem_ball_self hε_pos⟩)).trans hwn_Z_w
      have h_n_zero : n = (0 : ℤ) := by
        have h1 : (wn_Z ⟨w', hw'⟩ : ℂ) = n := by rw [wn_Z_cast]; exact hn
        have h2 : (wn_Z ⟨w', hw'⟩ : ℂ) = 0 := by exact_mod_cast h_wn_Z
        exact_mod_cast h1.symm.trans h2
      simp [hn, h_n_zero]
    -- On ball(w, ε): dixonFunction agrees with dixonH2
    have heq_on_ball : ∀ᶠ w' in 𝓝 w, dixonFunction f U γ w' = dixonH2 f γ w' := by
      apply Filter.Eventually.mono (Metric.ball_mem_nhds w hε_pos)
      intro w' hw'
      simp only [dixonFunction]
      split_ifs with hw'U
      · -- w' ∈ U: dixonH1 = dixonH2 since n = 0
        have hoff' : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w' :=
          fun t ht heq => hball_avoids t ht w' hw' heq
        rw [dixonH1_eq hU hf γ h_null.image_subset w' hw'U hoff', hwn_zero_ball w' hw']
        ring
      · rfl
    -- DifferentiableAt ℂ (dixonFunction f U γ) w via dixonH2
    have h2_diff : DifferentiableAt ℂ (dixonH2 f γ) w :=
      dixonH2_differentiableAt f γ
        (hf.continuousOn.mono (fun _ ⟨t, ht, heq⟩ => heq ▸ h_null.image_subset t ht)) w hoff
    exact h2_diff.congr_of_eventuallyEq heq_on_ball

/-- The Dixon function tends to 0 at infinity. -/
theorem dixonFunction_tendsto_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U) :
    Tendsto (dixonFunction f U γ) (Filter.cocompact ℂ) (𝓝 0) := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  obtain ⟨R, hR⟩ :=
    (isCompact_Icc.image_of_continuousOn γ.continuous_toFun).isBounded.exists_norm_le
  have hR_nn : 0 ≤ R := le_trans (norm_nonneg _)
    (hR (γ.toFun γ.a) ⟨γ.a, left_mem_Icc.mpr hab, rfl⟩)
  obtain ⟨M_d, hM_d⟩ := piecewiseC1Immersion_deriv_bounded γ
  have hM_d_nn : 0 ≤ M_d := le_trans (norm_nonneg _) (hM_d γ.a (left_mem_Icc.mpr hab))
  have hfγ_cont : ContinuousOn (fun t => f (γ.toFun t)) (Icc γ.a γ.b) :=
    hf.continuousOn.comp γ.continuous_toFun (fun t ht => h_null.image_subset t ht)
  obtain ⟨M_f, hM_f⟩ := isCompact_Icc.exists_bound_of_continuousOn hfγ_cont.norm
  simp only [norm_norm] at hM_f
  have hM_f_nn : 0 ≤ M_f := le_trans (norm_nonneg _) (hM_f γ.a (left_mem_Icc.mpr hab))
  have hclosed : γ.toFun γ.a = γ.toFun γ.b := h_null.closed
  have hba_nn : 0 ≤ γ.b - γ.a := by linarith
  -- For ‖w‖ > R, w is off the curve
  have hoff_of_large : ∀ w : ℂ, R < ‖w‖ → ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := by
    intro w hw t ht heq; linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩, heq ▸ hw]
  -- Distance lower bound: ‖γt - w‖ ≥ ‖w‖ - R
  have hdist_lb : ∀ w : ℂ, R < ‖w‖ → ∀ t ∈ Icc γ.a γ.b, ‖w‖ - R ≤ ‖γ.toFun t - w‖ := by
    intro w hw t ht
    have h1 : ‖w‖ - ‖γ.toFun t‖ ≤ ‖w - γ.toFun t‖ := norm_sub_norm_le w (γ.toFun t)
    rw [norm_sub_rev] at h1
    linarith [hR (γ.toFun t) ⟨t, ht, rfl⟩]
  -- Bound on dixonH2: ‖dixonH2 w‖ ≤ M_f * M_d * (b-a) / (‖w‖ - R)
  have h_h2_bound : ∀ w : ℂ, R < ‖w‖ →
      ‖dixonH2 f γ w‖ ≤ M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) := by
    intro w hw
    simp only [dixonH2]
    have hpos : 0 < ‖w‖ - R := by linarith
    have h_ptwise : ∀ t ∈ Set.uIoc γ.a γ.b,
        ‖f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖ ≤ M_f * M_d / (‖w‖ - R) := by
      intro t ht_ui
      have ht : t ∈ Icc γ.a γ.b := Ioc_subset_Icc_self (Set.uIoc_of_le hab ▸ ht_ui)
      rw [norm_mul, norm_div]
      have hd_lb := hdist_lb w hw t ht
      have hγt_sub_w_pos : 0 < ‖γ.toFun t - w‖ := by
        exact lt_of_lt_of_le hpos hd_lb
      calc ‖f (γ.toFun t)‖ / ‖γ.toFun t - w‖ * ‖deriv γ.toFun t‖
          ≤ (M_f / (‖w‖ - R)) * M_d :=
            mul_le_mul (div_le_div₀ hM_f_nn (hM_f t ht) hpos hd_lb)
              (hM_d t ht) (norm_nonneg _) (div_nonneg hM_f_nn hpos.le)
        _ = M_f * M_d / (‖w‖ - R) := by ring
    calc ‖∫ t in γ.a..γ.b, f (γ.toFun t) / (γ.toFun t - w) * deriv γ.toFun t‖
        ≤ (M_f * M_d / (‖w‖ - R)) * |γ.b - γ.a| :=
          intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
      _ = M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) := by
          rw [abs_of_nonneg hba_nn]; ring
  -- Winding number is integer for large w
  have hwn_int : ∀ w : ℂ, R < ‖w‖ →
      ∃ n : ℤ, generalizedWindingNumber' γ.toFun γ.a γ.b w = ↑n :=
    fun w hw =>
      windingNumber_integer_of_piecewise_closed_avoiding γ.toFun γ.a γ.b w
          γ.partition γ.hab hclosed γ.continuous_toFun
          (fun t ht hP => γ.smooth_off_partition t (Ioo_subset_Icc_self ht) hP)
          (fun _p1 _p2 _h12 hnoP hsub t ht =>
            (γ.deriv_continuous_off_partition t (hsub ht) (hnoP t ht)).continuousWithinAt)
          (hoff_of_large w hw) ⟨M_d, hM_d⟩
  -- Classical winding number for large w
  have hwn_classical : ∀ w : ℂ, R < ‖w‖ →
      generalizedWindingNumber' γ.toFun γ.a γ.b w =
        (2 * ↑Real.pi * I)⁻¹ * ∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t :=
    fun w hw =>
      generalizedWindingNumber_eq_classical_away γ.toPiecewiseC1Curve w (hoff_of_large w hw)
  -- Norm of 2πi
  have h_2pi_norm : ‖(2 * ↑Real.pi * I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_two, Complex.norm_real,
        Real.norm_of_nonneg Real.pi_pos.le, Complex.norm_I, mul_one]
  -- Winding number = 0 for ‖w‖ > R + M_d*(b-a)/(2π)
  have hwn_zero : ∀ w : ℂ, R + M_d * (γ.b - γ.a) / (2 * Real.pi) < ‖w‖ →
      generalizedWindingNumber' γ.toFun γ.a γ.b w = 0 := by
    intro w hw
    have h2pi_pos : 0 < 2 * Real.pi := Real.two_pi_pos
    have hR_lt : R < ‖w‖ := by
      linarith [div_nonneg (mul_nonneg hM_d_nn hba_nn) h2pi_pos.le]
    obtain ⟨n, hn_eq⟩ := hwn_int w hR_lt
    rw [hn_eq]
    -- Show |n| < 1, so n = 0
    have h_norm_wn : ‖generalizedWindingNumber' γ.toFun γ.a γ.b w‖ < 1 := by
      rw [hwn_classical w hR_lt, norm_mul, norm_inv, h_2pi_norm]
      have hpos : 0 < ‖w‖ - R := by linarith
      -- Bound the integral
      have h_int_b : ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
          ≤ M_d / (‖w‖ - R) * (γ.b - γ.a) := by
        have h_ptwise : ∀ t ∈ Set.uIoc γ.a γ.b,
            ‖(γ.toFun t - w)⁻¹ * deriv γ.toFun t‖ ≤ M_d / (‖w‖ - R) := by
          intro t ht_ui
          have ht := Ioc_subset_Icc_self (Set.uIoc_of_le hab ▸ ht_ui)
          rw [norm_mul, norm_inv]
          calc ‖γ.toFun t - w‖⁻¹ * ‖deriv γ.toFun t‖
              ≤ (‖w‖ - R)⁻¹ * M_d := by
                apply mul_le_mul _ (hM_d t ht) (norm_nonneg _)
                · exact inv_nonneg.mpr hpos.le
                · exact inv_anti₀ hpos (hdist_lb w hR_lt t ht)
            _ = M_d / (‖w‖ - R) := by rw [mul_comm, div_eq_mul_inv]
        calc ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
            ≤ M_d / (‖w‖ - R) * |γ.b - γ.a| :=
              intervalIntegral.norm_integral_le_of_norm_le_const h_ptwise
          _ = M_d / (‖w‖ - R) * (γ.b - γ.a) := by rw [abs_of_nonneg hba_nn]
      -- Combine: (2π)⁻¹ * ‖int‖ ≤ (2π)⁻¹ * M_d/(‖w‖-R) * (b-a) < 1
      calc (2 * Real.pi)⁻¹ * ‖∫ t in γ.a..γ.b, (γ.toFun t - w)⁻¹ * deriv γ.toFun t‖
          ≤ (2 * Real.pi)⁻¹ * (M_d / (‖w‖ - R) * (γ.b - γ.a)) :=
            mul_le_mul_of_nonneg_left h_int_b (inv_nonneg.mpr h2pi_pos.le)
        _ < 1 := by
            have h_key : M_d * (γ.b - γ.a) / (2 * Real.pi) < ‖w‖ - R := by linarith
            have h_key2 : M_d * (γ.b - γ.a) < (‖w‖ - R) * (2 * Real.pi) :=
              (div_lt_iff₀ h2pi_pos).mp h_key
            rw [show (2 * Real.pi)⁻¹ * (M_d / (‖w‖ - R) * (γ.b - γ.a)) =
                M_d * (γ.b - γ.a) / ((‖w‖ - R) * (2 * Real.pi)) from by
                  field_simp]
            rw [div_lt_one (mul_pos hpos h2pi_pos)]
            linarith
    rw [hn_eq] at h_norm_wn
    rw [Complex.norm_intCast] at h_norm_wn
    have h_abs := abs_lt.mp h_norm_wn
    norm_cast at h_abs ⊢
    omega
  -- Main goal: apply zero_at_infty_of_norm_le
  apply zero_at_infty_of_norm_le
  intro ε hε
  -- Choose threshold r: large enough that winding = 0 and bound < ε
  use max (R + M_d * (γ.b - γ.a) / (2 * Real.pi)) (R + M_f * M_d * (γ.b - γ.a) / ε)
  intro w hw
  have hR_lt : R < ‖w‖ := by
    have hle := le_max_left (R + M_d * (γ.b - γ.a) / (2 * Real.pi))
                             (R + M_f * M_d * (γ.b - γ.a) / ε)
    have hnn : 0 ≤ M_d * (γ.b - γ.a) / (2 * Real.pi) :=
      div_nonneg (mul_nonneg hM_d_nn hba_nn) Real.two_pi_pos.le
    linarith
  have hwn_eq_zero : generalizedWindingNumber' γ.toFun γ.a γ.b w = 0 :=
    hwn_zero w (lt_of_le_of_lt (le_max_left _ _) hw)
  have h_w2_lt : R + M_f * M_d * (γ.b - γ.a) / ε < ‖w‖ :=
    lt_of_le_of_lt (le_max_right _ _) hw
  -- The bound M_f * M_d * (b-a) / (‖w‖ - R) < ε
  have h_bound_lt_ε : M_f * M_d * (γ.b - γ.a) / (‖w‖ - R) < ε := by
    have hpos : 0 < ‖w‖ - R := by linarith
    rw [div_lt_iff₀ hpos]
    -- From h_w2_lt: R + M_f * M_d * (b-a) / ε < ‖w‖
    have h_div_lt : M_f * M_d * (γ.b - γ.a) / ε < ‖w‖ - R := by linarith
    have := (div_lt_iff₀ hε).mp h_div_lt
    linarith
  -- Case split: w ∈ U or w ∉ U
  by_cases hwin : w ∈ U
  · -- w ∈ U: dixonFunction = dixonH1 = dixonH2 (since n = 0)
    simp only [dixonFunction, dif_pos hwin]
    have hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w := hoff_of_large w hR_lt
    rw [dixonH1_eq hU hf γ h_null.image_subset w hwin hoff, hwn_eq_zero]
    simp only [mul_zero, zero_mul, sub_zero]
    exact lt_of_le_of_lt (h_h2_bound w hR_lt) h_bound_lt_ε
  · -- w ∉ U: dixonFunction = dixonH2
    simp only [dixonFunction, dif_neg hwin]
    exact lt_of_le_of_lt (h_h2_bound w hR_lt) h_bound_lt_ε

/-- h ≡ 0 by Liouville's theorem. -/
theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∀ w, dixonFunction f U γ w = 0 := by
  intro w
  have h_diff := dixonFunction_differentiable hU hf γ h_null
  have h_tend := dixonFunction_tendsto_zero hU hf γ h_null
  exact Differentiable.apply_eq_of_tendsto_cocompact h_diff w h_tend

/-- Cauchy integral formula for null-homologous curves:
∮_γ f(z)/(z-w) dz = 2πi · n(γ,w) · f(w) for w ∈ U off the curve. -/
theorem cauchyIntegralFormula_nullHomologous (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (w : ℂ) (hw : w ∈ U) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    dixonH2 f γ w =
      2 * ↑Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b w * f w := by
  have h_zero := dixonFunction_eq_zero hU hf γ h_null w
  simp only [dixonFunction, dif_pos hw] at h_zero
  -- h_zero : dixonH1 f γ w = 0
  -- By dixonH1_eq: h₁ = h₂ - 2πi·n·f(w), so 0 = h₂ - 2πi·n·f(w)
  have h_eq := dixonH1_eq hU hf γ h_null.image_subset w hw hoff
  -- h_eq : dixonH1 f γ w = dixonH2 f γ w - 2πi·n·f(w)
  rw [h_zero] at h_eq
  -- h_eq : 0 = dixonH2 f γ w - 2 * ↑π * I * n * f w
  linear_combination -h_eq

/-- The image of a piecewise C¹ immersion has empty interior in ℂ.
This follows from the fact that a Lipschitz map from ℝ to ℂ has image with
Hausdorff dimension at most 1, hence Lebesgue measure 0 in ℂ. -/
private lemma piecewiseC1_image_interior_empty (γ : PiecewiseC1Immersion) :
    interior (γ.toFun '' Icc γ.a γ.b) = ∅ := by
  rw [interior_eq_empty_iff_dense_compl]
  apply dense_compl_of_dimH_lt_finrank
  -- Split image into off-partition part (locally Lipschitz) and partition part (finite)
  have hsplit : γ.toFun '' Icc γ.a γ.b =
      γ.toFun '' (Icc γ.a γ.b \ ↑γ.partition) ∪ γ.toFun '' ↑γ.partition := by
    rw [← Set.image_union]
    congr 1
    exact (Set.diff_union_of_subset γ.partition_subset).symm
  rw [hsplit, dimH_union]
  apply max_lt
  · -- Off-partition part: dimH ≤ dimH(ℝ) = 1 < finrank ℝ ℂ = 2
    apply lt_of_le_of_lt
    · apply dimH_image_le_of_locally_lipschitzOn
      -- For each t ∉ partition, build local Lipschitz from differentiability
      intro t ⟨ht_Icc, ht_npart⟩
      -- t is in the open interval (endpoints are in partition)
      have ht_Ioo : t ∈ Ioo γ.a γ.b := by
        constructor
        · by_contra h; push_neg at h
          exact ht_npart (le_antisymm h ht_Icc.1 ▸ γ.endpoints_in_partition.1)
        · by_contra h; push_neg at h
          exact ht_npart (le_antisymm ht_Icc.2 h ▸ γ.endpoints_in_partition.2)
      -- ContinuousAt (deriv γ.toFun) at t (from deriv_continuous_off_partition)
      have hcont : ContinuousAt (deriv γ.toFun) t :=
        γ.deriv_continuous_off_partition t ht_Ioo ht_npart
      -- In a neighborhood of t avoiding partition, all points in Icc have HasDerivAt
      have hevt : ∀ᶠ y in 𝓝 t, HasDerivAt γ.toFun (deriv γ.toFun y) y := by
        have h_open_compl : IsOpen (↑γ.partition : Set ℝ)ᶜ :=
          γ.partition.finite_toSet.isClosed.isOpen_compl
        have h_open_Ioo : IsOpen (Ioo γ.a γ.b) := isOpen_Ioo
        -- t is in both open sets: compl(partition) and Ioo(a,b)
        have ht_mem1 : t ∈ (↑γ.partition : Set ℝ)ᶜ := ht_npart
        have ht_mem2 : t ∈ Ioo γ.a γ.b := ht_Ioo
        filter_upwards [(h_open_compl.inter h_open_Ioo).mem_nhds ⟨ht_mem1, ht_mem2⟩]
          with y ⟨hy_compl, hy_Ioo⟩
        exact (γ.smooth_off_partition y (Ioo_subset_Icc_self hy_Ioo) hy_compl).hasDerivAt
      -- Build HasStrictDerivAt from HasDerivAt + ContinuousAt of derivative
      have hstrict : HasStrictDerivAt γ.toFun (deriv γ.toFun t) t :=
        hasStrictDerivAt_of_hasDerivAt_of_continuousAt hevt hcont
      -- Get local Lipschitz from strict differentiability
      obtain ⟨K, v, hv, hLip⟩ := hstrict.hasStrictFDerivAt.exists_lipschitzOnWith
      -- Restrict to within s = Icc γ.a γ.b \ ↑γ.partition
      refine ⟨K, (Icc γ.a γ.b \ ↑γ.partition) ∩ v,
        inter_mem_nhdsWithin _ hv,
        hLip.mono Set.inter_subset_right⟩
    · -- dimH(Icc γ.a γ.b \ partition : Set ℝ) ≤ dimH(univ : Set ℝ) = 1 < 2
      apply lt_of_le_of_lt (dimH_mono (Set.subset_univ _))
      simp only [Real.dimH_univ]
      rw [Complex.finrank_real_complex]
      norm_cast
  · -- Partition part: finite set → dimH = 0 < finrank ℝ ℂ = 2
    have hfin : (γ.toFun '' ↑γ.partition).Finite :=
      γ.partition.finite_toSet.image γ.toFun
    rw [hfin.dimH_zero]
    rw [Complex.finrank_real_complex]
    norm_cast

theorem contourIntegral_eq_zero_of_nullHomologous (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  have hab : γ.a ≤ γ.b := le_of_lt γ.hab
  -- Step 1: Find w₀ ∈ U \ image(γ)
  have hU_ne : U.Nonempty :=
    ⟨γ.toFun γ.a, h_null.image_subset γ.a (left_mem_Icc.mpr hab)⟩
  have h_im_int_empty := piecewiseC1_image_interior_empty γ
  obtain ⟨w₀, hw₀U, hw₀_off⟩ : ∃ w₀ ∈ U, w₀ ∉ γ.toFun '' Icc γ.a γ.b := by
    by_contra h; push_neg at h
    have : U ⊆ interior (γ.toFun '' Icc γ.a γ.b) := hU.subset_interior_iff.mpr h
    rw [h_im_int_empty] at this
    exact Set.not_nonempty_empty (hU_ne.mono this)
  have hw₀_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w₀ :=
    fun t ht heq => hw₀_off ⟨t, ht, heq⟩
  -- Step 2: Define F(z) = f(z) * (z - w₀), holomorphic on U
  set F := fun z => f z * (z - w₀) with hF_def
  have hF_diff : DifferentiableOn ℂ F U :=
    hf.mul (differentiableOn_id.sub (differentiableOn_const w₀))
  -- Step 3: Rewrite ∫ f·γ' = ∫ F/(·-w₀)·γ' (since F(z)/(z-w₀) = f(z) for z ≠ w₀)
  have h_eq : ∀ t ∈ Set.uIcc γ.a γ.b,
      f (γ.toFun t) * deriv γ.toFun t =
      F (γ.toFun t) / (γ.toFun t - w₀) * deriv γ.toFun t := by
    intro t ht
    have ht_Icc : t ∈ Icc γ.a γ.b := Set.uIcc_of_le hab ▸ ht
    have hne : γ.toFun t - w₀ ≠ 0 := sub_ne_zero.mpr (hw₀_avoids t ht_Icc)
    simp only [hF_def, mul_div_assoc, div_self hne, mul_one]
  rw [intervalIntegral.integral_congr h_eq]
  -- Step 4: Apply CIF to F at w₀: ∫ F/(·-w₀)·γ' = 2πi·n·F(w₀) = 0
  have hCIF := cauchyIntegralFormula_nullHomologous hU hF_diff γ h_null w₀ hw₀U hw₀_avoids
  rw [show F w₀ = 0 from by simp [hF_def, sub_self, mul_zero], mul_zero] at hCIF
  exact hCIF

end DixonProof

end

/-! ## Downstream theorems with null-homologous hypothesis -/

/-- Null-homologous version of `integral_eq_sum_residues_of_avoids`. -/
theorem integral_eq_sum_residues_of_nullHomologous
    (U : Set ℂ) (hU : IsOpen U)
    (S0 : Finset ℂ) (hS0_in_U : ∀ s ∈ S0, s ∈ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
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
  -- Decompose f = Σ res/(z-s) + g where g is holomorphic.
  -- By contourIntegral_eq_zero_of_nullHomologous, ∫ g = 0.
  -- The singular sum ∫ Σ res/(z-s) = Σ winding * res by winding number computation.
  sorry

/-- **Theorem 3.3 of Hungerbühler-Wasem (arXiv:1808.00997v2)** for null-homologous curves.

Generalized residue theorem with conditions (A')+(B) for a null-homologous
immersed piecewise C¹ curve in an open set U, replacing the convexity hypothesis. -/
theorem generalizedResidueTheorem_3_3_nullHomologous
    (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hMero : ∀ s ∈ S0, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S0 (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S0)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 (2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) := by
  sorry
