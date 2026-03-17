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
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.RemovableSingularity

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

/-- h₂ is differentiable at every point off the curve. -/
theorem dixonH2_differentiableAt (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (w : ℂ) (hoff : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ w) :
    DifferentiableAt ℂ (dixonH2 f γ) w := by
  sorry

/-- h₁ is differentiable on all of U, including across the curve.
Uses `Complex.differentiableOn_dslope`: for each fixed γ(t), w ↦ dslope f (γ(t)) w
is differentiable on U iff f is differentiable on U. Combined with parametric
differentiation, the integral inherits differentiability. -/
theorem dixonH1_differentiableOn (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U) :
    DifferentiableOn ℂ (dixonH1 f γ) U := by
  sorry

/-- The Dixon function: h₁ on U, h₂ on ℂ \ U. -/
noncomputable def dixonFunction (f : ℂ → ℂ) (U : Set ℂ) (γ : PiecewiseC1Immersion) (w : ℂ) : ℂ :=
  if h : w ∈ U then dixonH1 f γ w else dixonH2 f γ w

/-- The Dixon function is entire (differentiable on all of ℂ).
On U: it's h₁, holomorphic by dixonH1_differentiableOn.
On ℂ \ U: it's h₂, holomorphic by dixonH2_differentiableAt.
Patching at ∂U: null-homologous gives n(γ,w) = 0 near ∂U, so h₁ = h₂ there. -/
theorem dixonFunction_differentiable (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    Differentiable ℂ (dixonFunction f U γ) := by
  sorry

/-- The Dixon function tends to 0 at infinity. -/
theorem dixonFunction_tendsto_zero (f : ℂ → ℂ) (γ : PiecewiseC1Immersion)
    (h_null : IsNullHomologous γ U) :
    Tendsto (dixonFunction f U γ) (Filter.cocompact ℂ) (𝓝 0) := by
  sorry

/-- h ≡ 0 by Liouville's theorem. -/
theorem dixonFunction_eq_zero (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∀ w, dixonFunction f U γ w = 0 := by
  intro w
  have h_diff := dixonFunction_differentiable hU hf γ h_null
  have h_tend := dixonFunction_tendsto_zero f γ h_null
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

/-- **The Homological Cauchy Theorem**: if f is holomorphic on open U and γ is
null-homologous in U, then ∮_γ f = 0.

Proof: Pick w₀ ∈ U \ image(γ). Apply CIF to F(z) = f(z)(z - w₀):
∮_γ f(z) dz = ∮_γ F(z)/(z-w₀) dz = 2πi · n(γ,w₀) · F(w₀) = 0
since F(w₀) = f(w₀)(w₀ - w₀) = 0. -/
theorem contourIntegral_eq_zero_of_nullHomologous (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t = 0 := by
  sorry

end DixonProof

end
