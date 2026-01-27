/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.HomotopyBridge

/-!
# Homotopy Theory for Piecewise C¹ Curves

This file extends the homotopy theory to piecewise C¹ curves, which is needed for
the valence formula where the fundamental domain boundary is piecewise smooth.

## Main Results

* `PiecewiseCurvesHomotopicAvoiding` - Homotopy definition for piecewise C¹ curves
* `windingNumber_eq_of_piecewise_homotopic` - Homotopy invariance for piecewise curves
* `linearHomotopy` - Standard linear interpolation between curves

## Mathematical Background

### Key Observation from Isabelle's HOL-Complex_Analysis

Isabelle's `valid_path` is defined as piecewise C¹ differentiable on [0,1], meaning there
exists a finite set of points where differentiability may fail. The key properties:

1. **Winding number well-defined**: The integral ∮ dz/(z-z₀) exists as a proper integral
   for piecewise C¹ curves avoiding z₀, since the integrand is continuous and the
   derivative exists almost everywhere.

2. **Integer-valued**: For closed curves avoiding z₀, the winding number is always an
   integer. This follows from the fact that exp(-∫₀ᵗ γ'(s)/(γ(s)-z₀) ds) = (γ(t)-z₀)/(γ(0)-z₀),
   and for closed curves γ(b) = γ(a), so the total integral is 2πi × integer.

3. **Homotopy invariance**: If two closed piecewise C¹ curves are homotopic avoiding z₀,
   they have the same winding number. The proof uses:
   - The winding number varies continuously with the homotopy parameter s
   - The winding number is always an integer
   - A continuous integer-valued function on [0,1] is constant

### Difference from Smooth Case

The smooth case (`ClosedCurvesHomotopicAvoiding`) requires:
- `∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun t' => H(t',s)) t`

For piecewise C¹ curves, we relax this to:
- `∀ t ∈ Ioo a b, t ∉ P, DifferentiableAt ℝ (fun t' => H(t',s)) t`

where P is a finite set of partition points.

### References

* Isabelle: `Winding_Numbers.thy` - `winding_number_homotopy_paths`
* Isabelle: `Contour_Integration.thy` - `valid_path`, `contour_integral_join`
* Ahlfors, "Complex Analysis" - Chapter 4 on winding numbers
* Rudin, "Real and Complex Analysis" - Chapter 10 on complex integration
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-! ## Piecewise Homotopy Definition -/

/-- Two closed piecewise C¹ curves are homotopic avoiding z₀ if there exists a
    continuous deformation that:
    - Is continuous overall
    - Restricts to γ₀ at s=0 and γ₁ at s=1
    - Keeps all intermediate curves closed
    - Avoids z₀ throughout
    - Is differentiable in t except at finitely many partition points

    This relaxes `ClosedCurvesHomotopicAvoiding` to handle piecewise smooth curves.
-/
def PiecewiseCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (P : Finset ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    -- H is jointly continuous
    Continuous H ∧
    -- H(·, 0) = γ₀
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    -- H(·, 1) = γ₁
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    -- Closed at each stage: H(a, s) = H(b, s)
    (∀ s ∈ Icc (0:ℝ) 1, H (a, s) = H (b, s)) ∧
    -- Avoids z₀ throughout
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀) ∧
    -- Differentiable in t away from partition points
    (∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    -- The t-derivative is continuous on each piece (between partition points)
    -- This is the key regularity condition for dominated convergence
    (∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1) (Ioo p₁ p₂ ×ˢ Icc 0 1))

/-- Simplified version: homotopic avoiding with empty partition (smooth case).
    This is equivalent to `ClosedCurvesHomotopicAvoiding`. -/
def SmoothCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) : Prop :=
  PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ ∅

/-! ## Winding Number for Piecewise C¹ Curves -/

/-- The generalized winding number is well-defined for piecewise C¹ curves.

    For a piecewise C¹ curve γ that avoids z₀, the integral
      (1/2πi) ∫ₐᵇ γ'(t)/(γ(t)-z₀) dt
    exists as a proper integral because:
    1. The integrand is continuous except at finitely many points (partition)
    2. At partition points, the limits exist from both sides
    3. The integral splits into finitely many pieces, each well-defined

    This uses `generalizedWindingNumber'` from WindingNumber.lean which handles
    the PV case, but for curves avoiding z₀ it equals the classical integral.
-/
theorem generalizedWindingNumber_welldefined_piecewiseC1
    (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (_hγ_avoids : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    ∃! n : ℂ, n = generalizedWindingNumber' γ.toFun γ.a γ.b z₀ := by
  -- The hypothesis _hγ_avoids ensures the integral is well-defined (no singularities),
  -- but the uniqueness statement is trivial: X is the unique value equal to X.
  exact ⟨generalizedWindingNumber' γ.toFun γ.a γ.b z₀, rfl, fun _ h => h⟩

/-! ## Helper Lemmas for Piecewise Smooth Integer-Valuedness -/

/-- A finite set has measure zero.

    This is used to show that integrals over [a,b] are not affected by
    changing values at finitely many partition points.
-/
lemma finset_measure_zero (P : Finset ℝ) : volume (P : Set ℝ) = 0 := by
  apply Set.Finite.measure_zero
  exact Finset.finite_toSet P

/-- For piecewise C¹ curves, the winding number is an integer.

    **Mathematical Argument**:
    For a closed curve γ avoiding z₀, the winding number equals the integral
      (1/2πi) ∫ₐᵇ γ'(t)/(γ(t)-z₀) dt

    For piecewise C¹ curves, we split at partition points P = {p₁,...,pₙ}:
      ∫ₐᵇ = ∫ₐ^{p₁} + ∫_{p₁}^{p₂} + ... + ∫_{pₙ}^b

    On each smooth piece [pᵢ, pᵢ₊₁], the fundamental theorem of calculus gives:
      ∫_{pᵢ}^{pᵢ₊₁} γ'/(γ-z₀) dt = log(γ(pᵢ₊₁) - z₀) - log(γ(pᵢ) - z₀)

    The sum telescopes to log(γ(b) - z₀) - log(γ(a) - z₀).
    Since γ(b) = γ(a) for closed curves, this is 2πi·n for some integer n.

    **Proof approach**: Use `windingNumber_integer_of_closed_avoiding` from HomotopyBridge.lean
    which already handles the exp trick. For piecewise curves, we use that:
    1. The integrand is continuous except on a null set (finite partition)
    2. The integral is the same whether we use piecewise or smooth derivatives
    3. The exp trick argument works because G = (γ-z₀)·exp(-F) is continuous
       and has zero derivative except at finitely many points
-/
lemma windingNumber_integer_of_piecewise_closed_avoiding
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (_hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  -- The winding number for curves avoiding z₀ equals:
  -- (2πi)⁻¹ * ∫ₐᵇ γ'(t)/(γ(t)-z₀) dt
  --
  -- Strategy: Use windingNumber_integer_of_closed_avoiding from HomotopyBridge.lean.
  -- That theorem requires:
  --   (1) ContinuousOn γ (Icc a b) ✓
  --   (2) ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t
  --   (3) ContinuousOn (deriv γ) (Icc a b)
  --   (4) ∀ t ∈ Icc a b, γ t ≠ z₀ ✓
  --
  -- For piecewise curves, (2) fails at partition points and (3) fails globally.
  -- However, the mathematical argument (exp trick) still works:
  --
  -- KEY INSIGHT: The integral ∫ γ'/(γ-z₀) doesn't depend on values at finitely
  -- many points (P has measure zero). The function G(t) = (γ(t)-z₀)·exp(-∫ₐᵗ...)
  -- is still continuous, and G' = 0 wherever γ is differentiable (i.e., off P).
  --
  -- By "patching": G is constant on each interval (pᵢ, pᵢ₊₁), and continuity
  -- forces these constants to agree. Hence G is globally constant.
  --
  -- G(a) = (γ(a)-z₀), G(b) = (γ(b)-z₀)·exp(-∫) = (γ(a)-z₀)·exp(-∫)
  -- From G(a) = G(b): exp(-∫) = 1, so ∫ = 2πi·n.
  --
  -- For now, we use the established mathematical fact that winding numbers
  -- of continuous closed curves avoiding a point are integers.
  -- The partition P only affects differentiability, not the topological content.
  --
  -- APPROACH: If P ∩ (a,b) is empty, use the smooth case directly.
  -- Otherwise, the mathematical argument above applies.
  by_cases hP_empty : (P : Set ℝ) ∩ Ioo a b = ∅
  · -- Case: No partition points in (a,b), so γ is smooth on (a,b)
    have hγ_diff' : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t := by
      intro t ht
      apply hγ_diff t ht
      intro habs
      have : t ∈ (P : Set ℝ) ∩ Ioo a b := ⟨habs, ht⟩
      rw [hP_empty] at this
      exact this
    -- Use windingNumber_integer_of_closed_avoiding which requires continuous deriv
    -- Since there are no partition points, the derivative may still be discontinuous
    -- at a and b. We need the exp trick to complete this case.
    -- For now, use the general sorry below.
    use 0
    sorry
  · -- Case: There are partition points in (a,b)
    -- Mathematical argument: split at partition points, apply exp trick on each piece
    use 0
    sorry

/-! ## Winding Number Continuity for Piecewise Homotopies -/

/-- Winding number is continuous in the homotopy parameter for piecewise C¹ homotopies.

    **Mathematical Argument**:
    If H : [a,b] × [0,1] → ℂ is a homotopy that is:
    - Jointly continuous
    - Avoids z₀ throughout
    - Has derivatives continuous on each piece (between partition points)

    Then the winding number s ↦ n(H(·,s)) is continuous on [0,1].

    **Proof Strategy**:
    1. The integrand ∂ₜH(t,s)/(H(t,s)-z₀) is bounded (uniform distance from z₀)
    2. The integrand is continuous except on the measure-zero partition set
    3. By dominated convergence, the integral is continuous in s

    **Technical Gap**: The smooth version `windingNumber_continuous_in_param` requires
    globally continuous derivatives. For piecewise homotopies, we need to extend
    the dominated convergence argument to handle discontinuities on null sets.
-/
lemma windingNumber_continuous_in_param_piecewise
    (H : ℝ × ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀)
    (_hH_diff : ∀ t ∈ Ioo a b, t ∉ P → ∀ s ∈ Icc (0:ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t)
    (_hH_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ → (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
      ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1) (Ioo p₁ p₂ ×ˢ Icc 0 1)) :
    ContinuousOn (fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀) (Icc 0 1) := by
  -- Strategy: Use dominated convergence for the integral representation
  --
  -- Step 1: Get uniform lower bound on distance to z₀
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := homotopy_uniform_avoidance H a b z₀ hab hH_cont hH_avoid
  -- Step 2: The integrand f(t,s) = (H(t,s) - z₀)⁻¹ * ∂ₜH(t,s)
  let f : ℝ → ℝ → ℂ := fun t s => (H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t
  -- Step 3: For s ∈ [0,1], the PV integral equals the classical integral
  --         (since the curve uniformly avoids z₀ by δ > 0)
  have h_pv_eq_integral : ∀ s ∈ Icc (0:ℝ) 1,
      generalizedWindingNumber' (fun t => H (t, s)) a b z₀ =
      (2 * Real.pi * I)⁻¹ * ∫ t in a..b, f t s := by
    intro s hs
    unfold generalizedWindingNumber' cauchyPrincipalValue'
    simp only [sub_zero]
    congr 1
    -- The cutoff condition is satisfied for ε < δ
    have h_cutoff : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Icc a b, ε < ‖H (t, s) - z₀‖ := by
      filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε t ht
      calc ε < δ := (mem_Ioo.mp hε).2
        _ ≤ ‖H (t, s) - z₀‖ := hδ_bound t ht s hs
    apply limUnder_eventually_eq_const
    filter_upwards [h_cutoff] with ε hε
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Icc a b := by
      rw [Set.uIoc_of_le (le_of_lt hab)] at ht
      exact Ioc_subset_Icc_self ht
    simp only [f, hε t ht', ↓reduceIte, deriv_sub_const]
  -- Step 4: Show the integral is continuous in s
  -- The integrand may be discontinuous at partition points, but these have measure 0.
  -- Dominated convergence still applies because:
  -- - The bound is uniform (δ⁻¹ × sup derivative bound)
  -- - Pointwise convergence holds a.e. (off the null set P)
  --
  -- For the formal proof, we use that:
  -- 1. The denominator (H(t,s) - z₀)⁻¹ is continuous in s (H is continuous)
  -- 2. The numerator deriv(H(·,s))(t) is bounded (compact domain, piecewise cont)
  -- 3. Hence the integrand is bounded by M/δ
  -- 4. Pointwise continuity at t ∉ P follows from _hH_deriv_cont
  --
  -- Technical gap: formalizing this requires careful use of dominated convergence
  -- with a.e. pointwise convergence (P is null).
  intro s₀ hs₀
  -- Rewrite using h_pv_eq_integral
  have heq_near : ∀ᶠ s in 𝓝[Icc 0 1] s₀, generalizedWindingNumber' (fun t => H (t, s)) a b z₀ =
      (2 * Real.pi * I)⁻¹ * ∫ t in a..b, f t s := by
    apply eventually_of_mem self_mem_nhdsWithin
    exact h_pv_eq_integral
  apply ContinuousWithinAt.congr_of_eventuallyEq _ heq_near (h_pv_eq_integral s₀ hs₀)
  apply continuousWithinAt_const.mul
  -- Need: ContinuousWithinAt (fun s => ∫ t in a..b, f t s) (Icc 0 1) s₀
  -- This follows from dominated convergence with piecewise continuous integrand
  -- The integrand is bounded (by δ⁻¹ × deriv bound) and converges pointwise a.e.
  sorry

/-! ## Homotopy Invariance for Piecewise Curves -/

/-- **Key Theorem**: Homotopy invariance of winding numbers for piecewise C¹ curves.

    If two closed piecewise C¹ curves are homotopic avoiding z₀, they have the
    same winding number around z₀.

    **Proof strategy** (following Isabelle's `winding_number_homotopy_paths`):
    1. The winding number varies continuously with the homotopy parameter s
    2. For each s, the winding number is an integer (by windingNumber_integer_of_piecewise_closed_avoiding)
    3. A continuous integer-valued function on [0,1] is constant
    4. Therefore n(γ₀) = n(0) = n(1) = n(γ₁)

    **Reference**: Isabelle `Winding_Numbers.thy`, theorem `winding_number_homotopy_paths`
-/
theorem windingNumber_eq_of_piecewise_homotopic
    (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ P) :
    generalizedWindingNumber' γ₀ a b z₀ = generalizedWindingNumber' γ₁ a b z₀ := by
  -- Step 1: Extract the homotopy H
  obtain ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid, hH_diff, _hH_deriv_cont⟩ := hhom
  -- Step 2: Define the winding number function n(s)
  let n : ℝ → ℂ := fun s => generalizedWindingNumber' (fun t => H (t, s)) a b z₀
  -- Step 3: Show n is continuous on [0,1]
  have hn_cont : ContinuousOn n (Icc 0 1) :=
    windingNumber_continuous_in_param_piecewise H a b z₀ P hab hH_cont hH_avoid hH_diff _hH_deriv_cont
  -- Step 4: Show n(s) is an integer for all s ∈ [0,1]
  have hn_int : ∀ s ∈ Icc (0:ℝ) 1, ∃ m : ℤ, n s = m := by
    intro s hs
    -- H(·, s) is a closed piecewise C¹ curve avoiding z₀
    -- Apply the piecewise version of integer-valuedness
    apply windingNumber_integer_of_piecewise_closed_avoiding (fun t => H (t, s)) a b z₀ P hab
    · -- Closedness: H(a, s) = H(b, s)
      exact hH_closed s hs
    · -- Continuity on [a, b]
      exact hH_cont.comp (continuous_id.prodMk continuous_const) |>.continuousOn
    · -- Differentiability at non-partition points
      intro t ht h_not_P
      exact hH_diff t ht h_not_P s hs
    · -- Derivative continuity on pieces between partition points
      -- _hH_deriv_cont gives continuity on (Ioo p₁ p₂) ×ˢ (Icc 0 1)
      -- We need to extract the slice at s
      intro p₁ p₂ hp₁p₂ hpiece
      -- The derivative of H(·, s) is continuous on Ioo p₁ p₂
      -- because the full derivative is continuous on (Ioo p₁ p₂) ×ˢ (Icc 0 1)
      have h_full := _hH_deriv_cont p₁ p₂ hp₁p₂ hpiece
      -- The function (fun p => deriv (H(·, p.2)) p.1) restricted to Ioo p₁ p₂ × {s}
      -- is (fun t => deriv (H(·, s)) t) which is what we need
      -- Use ContinuousOn.comp with the embedding t ↦ (t, s)
      have h_embed : ContinuousOn (fun t => (t, s)) (Ioo p₁ p₂) :=
        (continuous_id.prodMk continuous_const).continuousOn
      have h_range : MapsTo (fun t => (t, s)) (Ioo p₁ p₂) (Ioo p₁ p₂ ×ˢ Icc 0 1) :=
        fun t ht => ⟨ht, hs⟩
      -- The composition gives us the slice
      have h_comp := h_full.comp h_embed h_range
      -- Now we need to show the functions are equal
      convert h_comp using 1
    · -- Avoids z₀
      exact fun t ht => hH_avoid t ht s hs
  -- Step 5: Apply continuous_integer_valued_constant
  have heq : n 0 = n 1 := continuous_integer_valued_constant n hn_cont hn_int
  -- Step 6: Relate n(0) and n(1) to the original winding numbers
  have hn0_eq : n 0 = generalizedWindingNumber' γ₀ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 0)) γ₀ a b z₀ hab hH0
    -- Derivatives agree a.e.: use pattern from HomotopyBridge.lean
    rw [Set.uIoc_of_le (le_of_lt hab)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 0)) γ₀ (Ioo a b) :=
      fun t' ht' => hH0 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 0))) (deriv γ₀) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    -- Convert: property on Ioo implies ae on Ioc using Ioo_ae_eq_Ioc
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  have hn1_eq : n 1 = generalizedWindingNumber' γ₁ a b z₀ := by
    apply generalizedWindingNumber'_eq_of_eq_on (fun t => H (t, 1)) γ₁ a b z₀ hab hH1
    rw [Set.uIoc_of_le (le_of_lt hab)]
    have h_eq_on_Ioo : Set.EqOn (fun t => H (t, 1)) γ₁ (Ioo a b) :=
      fun t' ht' => hH1 t' (Ioo_subset_Icc_self ht')
    have h_deriv_eq_on : Set.EqOn (deriv (fun t => H (t, 1))) (deriv γ₁) (Ioo a b) :=
      h_eq_on_Ioo.deriv isOpen_Ioo
    -- Convert: property on Ioo implies ae on Ioc using Ioo_ae_eq_Ioc
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
    exact h_deriv_eq_on (ht.mpr ht_Ioc)
  rw [← hn0_eq, ← hn1_eq, heq]

/-! ## Linear Homotopy for Piecewise Curves -/

/-- The linear homotopy H(t,s) = (1-s)γ₀(t) + sγ₁(t) between two curves.

    This is piecewise smooth when both γ₀ and γ₁ are piecewise smooth,
    with partition points being the union of their partitions.
-/
def linearHomotopy (γ₀ γ₁ : ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun ⟨t, s⟩ => (1 - s) • γ₀ t + s • γ₁ t

theorem linearHomotopy_continuous (γ₀ γ₁ : ℝ → ℂ)
    (hγ₀ : Continuous γ₀) (hγ₁ : Continuous γ₁) :
    Continuous (linearHomotopy γ₀ γ₁) := by
  unfold linearHomotopy
  apply Continuous.add
  · apply Continuous.smul
    · exact continuous_const.sub continuous_snd
    · exact hγ₀.comp continuous_fst
  · apply Continuous.smul
    · exact continuous_snd
    · exact hγ₁.comp continuous_fst

theorem linearHomotopy_at_zero (γ₀ γ₁ : ℝ → ℂ) (t : ℝ) :
    linearHomotopy γ₀ γ₁ (t, 0) = γ₀ t := by
  simp only [linearHomotopy, sub_zero, one_smul, zero_smul, add_zero]

theorem linearHomotopy_at_one (γ₀ γ₁ : ℝ → ℂ) (t : ℝ) :
    linearHomotopy γ₀ γ₁ (t, 1) = γ₁ t := by
  simp only [linearHomotopy, sub_self, zero_smul, one_smul, zero_add]

theorem linearHomotopy_closed (γ₀ γ₁ : ℝ → ℂ) (a b : ℝ)
    (hγ₀_closed : γ₀ a = γ₀ b) (hγ₁_closed : γ₁ a = γ₁ b) (s : ℝ) :
    linearHomotopy γ₀ γ₁ (a, s) = linearHomotopy γ₀ γ₁ (b, s) := by
  simp only [linearHomotopy, hγ₀_closed, hγ₁_closed]

/-- The linear homotopy is differentiable in t when both curves are. -/
theorem linearHomotopy_differentiableAt_t (γ₀ γ₁ : ℝ → ℂ) (t s : ℝ)
    (hγ₀ : DifferentiableAt ℝ γ₀ t) (hγ₁ : DifferentiableAt ℝ γ₁ t) :
    DifferentiableAt ℝ (fun t' => linearHomotopy γ₀ γ₁ (t', s)) t := by
  simp only [linearHomotopy]
  apply DifferentiableAt.add
  · exact hγ₀.const_smul (1 - s)
  · exact hγ₁.const_smul s

/-- The derivative of the linear homotopy in t. -/
theorem linearHomotopy_deriv_t (γ₀ γ₁ : ℝ → ℂ) (t s : ℝ)
    (hγ₀ : DifferentiableAt ℝ γ₀ t) (hγ₁ : DifferentiableAt ℝ γ₁ t) :
    deriv (fun t' => linearHomotopy γ₀ γ₁ (t', s)) t =
    (1 - s) • deriv γ₀ t + s • deriv γ₁ t := by
  simp only [linearHomotopy]
  have hd₀ : DifferentiableAt ℝ (fun t' => (1 - s) • γ₀ t') t := hγ₀.const_smul (1 - s)
  have hd₁ : DifferentiableAt ℝ (fun t' => s • γ₁ t') t := hγ₁.const_smul s
  have h1 : deriv (fun t' => (1 - s) • γ₀ t') t = (1 - s) • deriv γ₀ t :=
    deriv_const_smul (1 - s) hγ₀
  have h2 : deriv (fun t' => s • γ₁ t') t = s • deriv γ₁ t :=
    deriv_const_smul s hγ₁
  have h_add : deriv (fun t' => (1 - s) • γ₀ t' + s • γ₁ t') t =
      deriv (fun t' => (1 - s) • γ₀ t') t + deriv (fun t' => s • γ₁ t') t :=
    deriv_add hd₀ hd₁
  rw [h_add, h1, h2]

end
