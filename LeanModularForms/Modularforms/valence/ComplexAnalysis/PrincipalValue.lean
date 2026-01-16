/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.HomotopyBridge

/-!
# Cauchy Principal Value Theory

This file develops the theory of Cauchy principal value integrals for complex
contour integration. The principal value approach allows contours to pass through
singularities, which is key for the generalized winding number theory.

## Main Results

### Existence and Linearity
* `cauchyPrincipalValueExists_of_simple_pole` - PV exists for simple poles
* `cauchyPrincipalValue_add` - PV is additive when both limits exist
* `cauchyPrincipalValue_smul` - PV is homogeneous

### Homotopy Invariance
* `homotopy_pv_integral_eq` - PV integral is homotopy invariant
* `windingNumber_homotopy_invariant` - Winding number is homotopy invariant

## References

* Isabelle: `Contour_Integration.thy` - `has_contour_integral_add`
* Isabelle: `Cauchy_Integral_Theorem.thy` - `Cauchy_theorem_homotopic_paths`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-! ## Basic Properties of PV Integrand -/

/-- The PV integrand is additive in f. -/
theorem cauchyPrincipalValueIntegrand_add'
    (f g : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrand' (f + g) γ z₀ ε t =
    cauchyPrincipalValueIntegrand' f γ z₀ ε t +
    cauchyPrincipalValueIntegrand' g γ z₀ ε t := by
  simp only [cauchyPrincipalValueIntegrand', Pi.add_apply]
  split_ifs with h
  · ring
  · ring

/-- The PV integrand is homogeneous in f. -/
theorem cauchyPrincipalValueIntegrand_smul'
    (c : ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) :
    cauchyPrincipalValueIntegrand' (fun z => c * f z) γ z₀ ε t =
    c * cauchyPrincipalValueIntegrand' f γ z₀ ε t := by
  simp only [cauchyPrincipalValueIntegrand']
  split_ifs with h
  · ring
  · ring

/-! ## Integrability of PV Integrand -/

/-- The PV integrand is bounded away from z₀. -/
theorem cauchyPrincipalValueIntegrand_bounded
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ M : ℝ, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := by
  -- The domain γ '' Icc a b \ ball z₀ ε might be empty; in that case f bound is 0
  by_cases h_empty : (γ '' Icc a b \ Metric.ball z₀ ε).Nonempty
  · -- Non-empty case: f has a bound on the compact set
    -- γ '' Icc a b is compact (continuous image of compact set)
    have hγ_im_compact : IsCompact (γ '' Icc a b) := isCompact_Icc.image_of_continuousOn hγ_cont
    -- γ '' Icc a b \ ball z₀ ε is a closed subset of a compact set, hence compact
    have hclosed_ball : IsClosed (Metric.ball z₀ ε)ᶜ := Metric.isOpen_ball.isClosed_compl
    have hcompact_domain : IsCompact (γ '' Icc a b \ Metric.ball z₀ ε) :=
      hγ_im_compact.inter_right hclosed_ball
    -- f is bounded on this compact set
    have hf_bound := hcompact_domain.exists_bound_of_continuousOn hf_cont.norm
    obtain ⟨Mf, hMf⟩ := hf_bound
    -- deriv γ is bounded on [a,b]
    have hγ'_bound := isCompact_Icc.exists_bound_of_continuousOn hγ'_cont.norm
    obtain ⟨Mγ, hMγ⟩ := hγ'_bound
    -- Note: hMf and hMγ give bounds on ‖‖·‖‖, but ‖‖x‖‖ = ‖x‖ for norms
    have hMf' : ∀ x ∈ γ '' Icc a b \ Metric.ball z₀ ε, ‖f x‖ ≤ Mf := fun x hx => by
      have := hMf x hx
      simp only [Real.norm_eq_abs, abs_norm] at this
      exact this
    have hMγ' : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ Mγ := fun t ht => by
      have := hMγ t ht
      simp only [Real.norm_eq_abs, abs_norm] at this
      exact this
    -- The bound is Mf * Mγ (or we add 1 to handle the 0 case)
    use Mf * Mγ + 1
    intro t ht
    unfold cauchyPrincipalValueIntegrand'
    split_ifs with h
    · -- Case: ‖γ t - z₀‖ > ε
      have hγt_in : γ t ∈ γ '' Icc a b \ Metric.ball z₀ ε := by
        constructor
        · exact ⟨t, ht, rfl⟩
        · simp only [Metric.mem_ball, not_lt]
          exact le_of_lt h
      calc ‖f (γ t) * deriv γ t‖ = ‖f (γ t)‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ Mf * Mγ := by
          have hf_le : ‖f (γ t)‖ ≤ Mf := hMf' (γ t) hγt_in
          have hγ_le : ‖deriv γ t‖ ≤ Mγ := hMγ' t ht
          exact mul_le_mul hf_le hγ_le (norm_nonneg _) (le_trans (norm_nonneg _) hf_le)
        _ ≤ Mf * Mγ + 1 := by linarith
    · -- Case: integrand is 0
      simp only [norm_zero]
      apply add_nonneg
      · apply mul_nonneg
        · exact le_trans (norm_nonneg _) (hMf' _ h_empty.some_mem)
        · -- Need to find some t' in Icc a b; use the nonempty witness from h_empty
          obtain ⟨z, ⟨t', ht', _⟩, _⟩ := h_empty
          exact le_trans (norm_nonneg _) (hMγ' _ ht')
      · norm_num
  · -- Empty case: the integrand is always 0 when γ t - z₀ > ε would be needed
    use 0
    intro t ht
    unfold cauchyPrincipalValueIntegrand'
    split_ifs with h
    · -- If ‖γ t - z₀‖ > ε, then γ t ∈ γ '' Icc a b \ ball z₀ ε, contradicting emptiness
      exfalso
      apply h_empty
      exact ⟨γ t, ⟨t, ht, rfl⟩, by simp only [Metric.mem_ball, not_lt]; exact le_of_lt h⟩
    · simp only [norm_zero, le_refl]

/-- The PV integrand is integrable for each ε > 0.

    **Proof strategy**: The integrand is bounded (by `cauchyPrincipalValueIntegrand_bounded`)
    and is AEStronglyMeasurable as a piecewise function on measurable sets.
    Bounded AEStronglyMeasurable functions on finite measure sets are integrable.

    **Technical note**: The full proof requires showing AEStronglyMeasurable for the piecewise
    integrand, which involves measurability of the indicator set {t | ε < ‖γ t - z₀‖}.
    This follows from continuity of γ and measurability of preimages of open sets.
-/
theorem cauchyPrincipalValueIntegrand_integrable
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hab : a < b)
    (hf_cont : ContinuousOn f (γ '' Icc a b \ Metric.ball z₀ ε))
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    IntervalIntegrable (cauchyPrincipalValueIntegrand' f γ z₀ ε) volume a b := by
  -- Get the bound M from cauchyPrincipalValueIntegrand_bounded
  obtain ⟨M, hM⟩ := cauchyPrincipalValueIntegrand_bounded f γ a b z₀ ε hε hf_cont hγ_cont hγ'_cont
  -- The PV integrand is bounded by max M 1 on [a, b]
  have h_le : ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ max M 1 := by
    intro t ht
    calc ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M := hM t ht
      _ ≤ max M 1 := le_max_left M 1
  -- The proof uses Integrable.mono with the bound max M 1.
  -- cauchyPrincipalValueIntegrand' is a piecewise function:
  --   if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0
  -- It is AEStronglyMeasurable and bounded ae by max M 1 (from h_le).
  --
  -- Technical completion requires:
  -- 1. Show const (max M 1) is integrable on Ioo a b
  -- 2. Show integrand is AEStronglyMeasurable via piecewise
  -- 3. Apply Integrable.mono' with the bound
  sorry

/-! ## Existence of Principal Value -/

/-- Principal value exists for simple poles.

    **Theorem**: If f(z) = c/(z - z₀) + g(z) where g is holomorphic near z₀,
    then the principal value integral of f exists.

    **Proof strategy**: Split into singular and regular parts:
    - PV ∮ (c/(z-z₀)) exists by model sector calculation
    - ∮ g exists by standard theory (g is continuous)

    The model sector calculation shows that for a curve passing through z₀ at angle α:
    PV ∮_{sector} dz/(z-z₀) = α · i

    For a general curve, we decompose near the singularity:
    1. Away from z₀: standard contour integral (no singularity)
    2. Near z₀: model sector gives contribution proportional to angle

    **Key insight**: The PV integral of 1/(z-z₀) along a curve through z₀
    equals i times the angle traversed (or half the angle for symmetric approach).
-/
theorem cauchyPrincipalValueExists_of_simple_pole
    (γ : PiecewiseC1Curve) (z₀ : ℂ) (c : ℂ)
    (g : ℂ → ℂ) (hg : ContinuousOn g (γ.toFun '' Icc γ.a γ.b))
    (hγ_immersion : ∀ t ∈ Icc γ.a γ.b, t ∉ γ.partition → deriv γ.toFun t ≠ 0) :
    CauchyPrincipalValueExists' (fun z => c / (z - z₀) + g z) γ.toFun γ.a γ.b z₀ := by
  -- The proof proceeds by showing:
  -- 1. The regular part g is continuous, so ∮ g dz exists as a standard integral
  -- 2. The singular part c/(z-z₀) has a well-defined PV by model sector analysis
  -- 3. The sum of these limits exists (limit algebra)
  --
  -- For the singular part:
  -- - Near z₀, the curve γ looks like a line segment (first-order Taylor)
  -- - The model integral ∫ dz/z along a ray gives log contributions
  -- - The symmetric ε-excision ensures the log divergences cancel
  -- - What remains is the angle contribution
  --
  -- For the regular part:
  -- - g is continuous on the image of γ
  -- - The integrand g(γ(t)) * γ'(t) is continuous on [a,b]
  -- - Hence integrable, and the limit as ε → 0 is just the full integral
  --
  -- Technical implementation requires:
  -- - Local analysis of γ near points where γ(t) = z₀
  -- - Taylor expansion of γ near these points
  -- - Evaluation of model integrals for 1/z
  --
  -- This is a substantial calculation that we defer.
  sorry

/-- The principal value integral is additive when both limits exist.

    **Isabelle parallel**: `has_contour_integral_add` in `Contour_Integration.thy`
-/
theorem cauchyPrincipalValue_add'
    (f g : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hf : CauchyPrincipalValueExists' f γ a b z₀)
    (hg : CauchyPrincipalValueExists' g γ a b z₀) :
    cauchyPrincipalValue' (f + g) γ a b z₀ =
    cauchyPrincipalValue' f γ a b z₀ + cauchyPrincipalValue' g γ a b z₀ := by
  -- Get the limits
  obtain ⟨Lf, hLf⟩ := hf
  obtain ⟨Lg, hLg⟩ := hg
  -- The integrand for f + g splits as the sum of integrands for f and g
  have h_integrand_eq : ∀ ε t, cauchyPrincipalValueIntegrand' (f + g) γ z₀ ε t =
      cauchyPrincipalValueIntegrand' f γ z₀ ε t +
      cauchyPrincipalValueIntegrand' g γ z₀ ε t := fun ε t =>
    cauchyPrincipalValueIntegrand_add' f g γ z₀ ε t
  -- The integral of f + g equals the sum of integrals (when integrands are integrable)
  -- The integrability follows from boundedness of PV integrands on finite intervals.
  -- Technical note: For the full proof, we would need explicit continuity assumptions on f, g, γ
  -- to apply cauchyPrincipalValueIntegrand_integrable. Here we use that existence of the PV limit
  -- implies integrability for small enough ε.
  have h_integral_eq : ∀ ε, ∫ t in a..b, cauchyPrincipalValueIntegrand' (f + g) γ z₀ ε t =
      (∫ t in a..b, cauchyPrincipalValueIntegrand' f γ z₀ ε t) +
      (∫ t in a..b, cauchyPrincipalValueIntegrand' g γ z₀ ε t) := fun ε => by
    simp_rw [h_integrand_eq]
    -- Apply integral_add with integrability assumptions
    -- The full proof requires showing each integrand is IntervalIntegrable,
    -- which follows from boundedness (cauchyPrincipalValueIntegrand_bounded)
    -- and measurability (piecewise continuous functions are measurable).
    -- We defer this technical step.
    sorry
  -- Show the sum converges to Lf + Lg using limit algebra
  have h_sum_tendsto : Tendsto (fun ε =>
      ∫ t in a..b, cauchyPrincipalValueIntegrand' (f + g) γ z₀ ε t)
      (𝓝[>] 0) (𝓝 (Lf + Lg)) := by
    simp_rw [h_integral_eq]
    exact hLf.add hLg
  -- The PV is the limit, and it equals Lf + Lg
  unfold cauchyPrincipalValue'
  -- limUnder of f + g equals Lf + Lg
  have h1 : limUnder (𝓝[>] 0) (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - z₀‖ then (f + g) (γ t) * deriv γ t else 0) = Lf + Lg :=
    Filter.Tendsto.limUnder_eq h_sum_tendsto
  -- limUnder of f equals Lf
  have h2 : limUnder (𝓝[>] 0) (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) = Lf :=
    Filter.Tendsto.limUnder_eq hLf
  -- limUnder of g equals Lg
  have h3 : limUnder (𝓝[>] 0) (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - z₀‖ then g (γ t) * deriv γ t else 0) = Lg :=
    Filter.Tendsto.limUnder_eq hLg
  rw [h1, h2, h3]

/-- The principal value integral is homogeneous. -/
theorem cauchyPrincipalValue_smul'
    (c : ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ)
    (hf : CauchyPrincipalValueExists' f γ a b z₀) :
    cauchyPrincipalValue' (fun z => c * f z) γ a b z₀ =
    c * cauchyPrincipalValue' f γ a b z₀ := by
  -- Get the limit for f
  obtain ⟨Lf, hLf⟩ := hf
  -- The integrand for c * f equals c * integrand for f
  have h_integrand_eq : ∀ ε t, cauchyPrincipalValueIntegrand' (fun z => c * f z) γ z₀ ε t =
      c * cauchyPrincipalValueIntegrand' f γ z₀ ε t := fun ε t =>
    cauchyPrincipalValueIntegrand_smul' c f γ z₀ ε t
  -- The integral of c * f equals c * integral of f
  have h_integral_eq : ∀ ε, ∫ t in a..b, cauchyPrincipalValueIntegrand' (fun z => c * f z) γ z₀ ε t =
      c * ∫ t in a..b, cauchyPrincipalValueIntegrand' f γ z₀ ε t := fun ε => by
    simp_rw [h_integrand_eq]
    rw [intervalIntegral.integral_const_mul]
  -- Show c * (integral of f) converges to c * Lf
  have h_smul_tendsto : Tendsto (fun ε =>
      ∫ t in a..b, cauchyPrincipalValueIntegrand' (fun z => c * f z) γ z₀ ε t)
      (𝓝[>] 0) (𝓝 (c * Lf)) := by
    simp_rw [h_integral_eq]
    exact hLf.const_mul c
  -- The PV is the limit
  unfold cauchyPrincipalValue'
  -- limUnder of c * f equals c * Lf
  have h1 : limUnder (𝓝[>] 0) (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - z₀‖ then (c * f (γ t)) * deriv γ t else 0) = c * Lf :=
    Filter.Tendsto.limUnder_eq h_smul_tendsto
  -- limUnder of f equals Lf
  have h2 : limUnder (𝓝[>] 0) (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - z₀‖ then f (γ t) * deriv γ t else 0) = Lf :=
    Filter.Tendsto.limUnder_eq hLf
  rw [h1, h2]

/-! ## Homotopy Invariance -/

/-- The principal value integral is invariant under homotopy.

    **Theorem**: If Γ and γ are homotopic via H : [a,b] × [0,1] → ℂ with:
    - H(t, 0) = Γ(t), H(t, 1) = γ(t)
    - H(a, s) = H(b, s) = z₀ for all s
    - H(t, s) ≠ z₀ for t ∈ (a, b) and all s

    Then PV ∮_Γ f = PV ∮_γ f.

    **Isabelle parallel**: `Cauchy_theorem_homotopic_paths` in `Cauchy_Integral_Theorem.thy`

    **Proof Strategy** (uses `HomotopyBridge`):
    1. Define F(s) = PV ∮_{H(·,s)} f for s ∈ [0,1]
    2. Show F is continuous using `windingNumber_continuous_in_param` pattern
       (dominated convergence for parameter-dependent integrals)
    3. Apply Cauchy's theorem (`cauchyTheorem_rectangle'` or `cauchyTheorem_circle'`)
       to show the integral is locally constant
    4. Use `continuous_integer_valued_constant` style argument:
       continuous + locally constant on connected [0,1] → constant
    5. Conclude F(0) = F(1)

    **Key mathlib ingredients**:
    - `Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`
    - `Tendsto.intervalIntegral` for continuity of parametric integrals
-/
theorem homotopy_pv_integral_eq'
    (f : ℂ → ℂ) (Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (H : ℝ × ℝ → ℂ) (hH_cont : Continuous H)
    (hH0 : ∀ t ∈ Icc a b, H (t, 0) = Γ t)
    (hH1 : ∀ t ∈ Icc a b, H (t, 1) = γ t)
    (hH_endpoints : ∀ s ∈ Icc (0:ℝ) 1, H (a, s) = z₀ ∧ H (b, s) = z₀)
    (hH_nonzero : ∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀) :
    cauchyPrincipalValue' f Γ a b z₀ = cauchyPrincipalValue' f γ a b z₀ := by
  /-
  ## Proof Strategy

  Define F : [0,1] → ℂ by F(s) = PV ∮_{H(·,s)} f dz.

  We need to show F(0) = F(1).

  Step 1: F is continuous on [0,1]
    - The homotopy H avoids z₀ on (a,b) × [0,1] (hH_nonzero)
    - This gives uniform control on the integrand away from endpoints
    - Dominated convergence for parametric integrals gives continuity

  Step 2: F is locally constant on (0,1)
    - For s₀ ∈ (0,1), the curves H(·,s) for s near s₀ are homotopic
    - Cauchy's theorem (via HomotopyBridge) shows integral is unchanged
    - This uses that f is holomorphic away from z₀

  Step 3: Continuous + locally constant on connected set → constant
    - [0,1] is connected
    - F continuous + locally constant → F constant
    - Therefore F(0) = F(1)

  The full proof requires:
  - Parametric integral continuity (from HomotopyBridge)
  - Cauchy's theorem for homotopic paths
  - Connectedness argument
  -/
  -- The proof uses the machinery from HomotopyBridge
  -- The key is that F(s) = cauchyPrincipalValue' f (H(·,s)) a b z₀ is:
  -- 1. Continuous in s (by uniform bounds on (a,b) × [0,1])
  -- 2. Locally constant (by Cauchy's theorem for nearby curves)
  -- 3. Hence constant on [0,1], giving F(0) = F(1)
  --
  -- This is a deep result requiring significant infrastructure.
  -- We defer the technical implementation.
  sorry
/-
  ## Proof Strategy (outline)

  The key insight is that the curves pass through z₀ only at endpoints (t = a, t = b),
  and the homotopy H preserves this structure:
  - H(a, s) = z₀ and H(b, s) = z₀ for all s ∈ [0,1]
  - H(t, s) ≠ z₀ for all t ∈ (a, b) and s ∈ [0,1]

  Define F : [0,1] → ℂ by F(s) = PV ∮_{H(·,s)} f dz.

  Step 1: F is continuous on [0,1] (uniform avoidance on (a,b) × [0,1])
  Step 2: F is locally constant on (0,1) (Cauchy's theorem)
  Step 3: Continuous + locally constant on connected [0,1] → constant
  Therefore F(0) = F(1), which gives the result
-/

/-- The generalized winding number is homotopy invariant.

    **Corollary** of `homotopy_pv_integral_eq'` applied to f(z) = 1/z.

    **Isabelle parallel**: `winding_number_homotopy_paths` in `Winding_Numbers.thy`
-/
theorem windingNumber_homotopy_invariant'
    (Γ γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hΓ : ContinuousOn Γ (Icc a b))
    (hγ : ContinuousOn γ (Icc a b))
    (H : ℝ × ℝ → ℂ) (hH : Continuous H)
    (hH0 : ∀ t ∈ Icc a b, H (t, 0) = Γ t)
    (hH1 : ∀ t ∈ Icc a b, H (t, 1) = γ t)
    (hH_endpoints : ∀ s ∈ Icc (0:ℝ) 1, H (a, s) = z₀ ∧ H (b, s) = z₀)
    (hH_nonzero : ∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ≠ z₀) :
    generalizedWindingNumber' Γ a b z₀ = generalizedWindingNumber' γ a b z₀ := by
  /-
  ## Proof Strategy

  The generalized winding number is:
    n_{z₀}(γ) = (1/2πi) · PV ∮_γ dz/(z - z₀)
             = (1/2πi) · PV ∫_a^b (γ(t) - z₀)⁻¹ · γ'(t) dt

  With the substitution w = γ(t) - z₀, this becomes:
    = (1/2πi) · PV ∮_{γ-z₀} dw/w
    = (1/2πi) · cauchyPrincipalValue' (·⁻¹) (γ - z₀) a b 0

  Since H(·, s) - z₀ defines a homotopy from Γ - z₀ to γ - z₀ that:
  - Passes through 0 only at t = a and t = b (where H(a,s) = H(b,s) = z₀)
  - Avoids 0 in the interior (since H(t,s) ≠ z₀ for t ∈ (a,b))

  We can apply homotopy_pv_integral_eq' to show the PV integrals are equal.
  -/
  unfold generalizedWindingNumber'
  -- The goal reduces to showing the PV integrals of (·)⁻¹ over the shifted curves are equal
  congr 1

  -- Define the shifted homotopy: H_shifted(t, s) = H(t, s) - z₀
  let H_shifted : ℝ × ℝ → ℂ := fun p => H p - z₀

  -- H_shifted is continuous
  have hH_shifted_cont : Continuous H_shifted := hH.sub continuous_const

  -- H_shifted(t, 0) = Γ(t) - z₀
  have hH_shifted_0 : ∀ t ∈ Icc a b, H_shifted (t, 0) = Γ t - z₀ := by
    intro t ht
    simp only [H_shifted]
    rw [hH0 t ht]

  -- H_shifted(t, 1) = γ(t) - z₀
  have hH_shifted_1 : ∀ t ∈ Icc a b, H_shifted (t, 1) = γ t - z₀ := by
    intro t ht
    simp only [H_shifted]
    rw [hH1 t ht]

  -- H_shifted(a, s) = 0 and H_shifted(b, s) = 0
  have hH_shifted_endpoints : ∀ s ∈ Icc (0:ℝ) 1, H_shifted (a, s) = 0 ∧ H_shifted (b, s) = 0 := by
    intro s hs
    simp only [H_shifted]
    constructor
    · rw [(hH_endpoints s hs).1]; ring
    · rw [(hH_endpoints s hs).2]; ring

  -- H_shifted(t, s) ≠ 0 for t ∈ (a, b)
  have hH_shifted_nonzero : ∀ t ∈ Ioo a b, ∀ s ∈ Icc (0:ℝ) 1, H_shifted (t, s) ≠ 0 := by
    intro t ht s hs
    simp only [H_shifted, sub_ne_zero]
    exact hH_nonzero t ht s hs

  -- Apply homotopy_pv_integral_eq' to (·)⁻¹ and the shifted curves
  exact homotopy_pv_integral_eq' (·⁻¹) (fun t => Γ t - z₀) (fun t => γ t - z₀) a b 0 hab
    H_shifted hH_shifted_cont hH_shifted_0 hH_shifted_1 hH_shifted_endpoints hH_shifted_nonzero

/-! ## Dominated Convergence for PV -/

/-- Dominated convergence theorem for principal value integrals.

    If the integrand is uniformly bounded as ε → 0, the limit exists.

    **Proof strategy**: Use dominated convergence theorem for the parametric integral.
    The key ingredients are:
    1. Uniform bound h_bound provides the dominating function
    2. Pointwise ae convergence h_ae_limit gives the limit integrand
    3. Apply dominated convergence to conclude the integral converges

    **Mathlib reference**: `MeasureTheory.tendsto_integral_of_dominated_convergence`
-/
theorem cauchyPrincipalValue_of_dominated
    (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (M : ℝ) (hM : 0 < M)
    (h_bound : ∀ ε > 0, ∀ t ∈ Icc a b, ‖cauchyPrincipalValueIntegrand' f γ z₀ ε t‖ ≤ M)
    (h_ae_limit : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∃ L, Tendsto (fun ε => cauchyPrincipalValueIntegrand' f γ z₀ ε t) (𝓝[>] 0) (𝓝 L)) :
    CauchyPrincipalValueExists' f γ a b z₀ := by
  -- The dominated convergence approach:
  -- 1. The pointwise limit L(t) exists ae by h_ae_limit
  -- 2. The bound M is integrable on [a, b] (constant function on finite interval)
  -- 3. Each integrand is bounded by M
  -- 4. By dominated convergence, ∫ integrand(ε, t) dt → ∫ L(t) dt as ε → 0⁺
  --
  -- Technical details require:
  -- - Measurability of the integrands (piecewise continuous)
  -- - The filter 𝓝[>] 0 has a countable base for dominated convergence
  -- - Conversion between interval integral and Bochner integral on [a, b]
  --
  -- The full proof uses MeasureTheory.tendsto_integral_of_dominated_convergence
  -- with the constant dominating function M.
  --
  -- We sketch the main structure:
  -- Define L : ℝ → ℂ as the ae pointwise limit
  -- Show ∫ t in a..b, cauchyPrincipalValueIntegrand' f γ z₀ ε t → ∫ t in a..b, L t
  --
  -- This is a standard application of dominated convergence for parametric integrals.
  -- The technical measurability and filter handling is deferred.
  sorry

end
