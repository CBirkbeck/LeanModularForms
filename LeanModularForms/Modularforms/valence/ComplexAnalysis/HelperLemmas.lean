/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Topology.Connected.Basic

/-!
# Helper Lemmas for Valence Formula Proofs

This file provides helper lemmas that bridge our custom definitions to mathlib's
infrastructure. These lemmas simplify filling sorries in the valence formula proof.

## Main Results

### FTC and Lipschitz Bounds
* `lipschitz_of_bounded_deriv_real_to_complex` - Lipschitz from bounded derivative
* `taylor_error_from_lipschitz` - Taylor error O(h²) from Lipschitz derivative

### Residue Theory
* `circleIntegral_inv_eq_two_pi_I` - Circle integral of 1/(z-w) is 2πi

### Connectedness
* `isPreconnected_Icc_01` - [0,1] is preconnected

## References

Uses mathlib's:
- `Convex.lipschitzOnWith_of_nnnorm_deriv_le`
- `circleIntegral.integral_sub_center_inv`
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval NNReal

noncomputable section

/-! ## FTC and Lipschitz Bounds -/

/-- If f : ℝ → ℂ is differentiable on [a,b] with bounded derivative ‖f'(t)‖ ≤ M,
    then f is Lipschitz with constant M.

    This is a direct application of `Convex.lipschitzOnWith_of_nnnorm_deriv_le`
    specialized to ℝ → ℂ functions.
-/
theorem lipschitz_of_bounded_deriv_real_to_complex {f : ℝ → ℂ} {a b : ℝ} {M : ℝ≥0}
    (hf_diff : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf_bdd : ∀ t ∈ Icc a b, ‖deriv f t‖₊ ≤ M) :
    LipschitzOnWith M f (Icc a b) := by
  have h_conv : Convex ℝ (Icc a b) := convex_Icc a b
  exact Convex.lipschitzOnWith_of_nnnorm_deriv_le hf_diff hf_bdd h_conv

/-- Same as above but with a real constant M instead of NNReal and direct bound form. -/
theorem lipschitz_bound_real_to_complex {f : ℝ → ℂ} {a b M : ℝ} (hM : 0 ≤ M)
    (hf_diff : ∀ t ∈ Icc a b, DifferentiableAt ℝ f t)
    (hf_bdd : ∀ t ∈ Icc a b, ‖deriv f t‖ ≤ M) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ‖f t - f s‖ ≤ M * |t - s| := by
  intro s hs t ht
  have h_conv : Convex ℝ (Icc a b) := convex_Icc a b
  have hf_bdd' : ∀ x ∈ Icc a b, ‖deriv f x‖₊ ≤ ⟨M, hM⟩ := fun x hx => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact hf_bdd x hx
  have h_lip := Convex.lipschitzOnWith_of_nnnorm_deriv_le hf_diff hf_bdd' h_conv
  have h := h_lip.dist_le_mul t ht s hs
  simp only [dist_eq_norm] at h
  calc ‖f t - f s‖ ≤ M * dist t s := h
    _ = M * |t - s| := by rw [Real.dist_eq]

/-- Lipschitz functions satisfy ‖f(t) - f(s)‖ ≤ M * |t - s|. -/
theorem lipschitz_bound_from_lipschitzOnWith' {f : ℝ → ℂ} {s : Set ℝ} {M : ℝ≥0}
    (hf : LipschitzOnWith M f s) :
    ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y‖ ≤ M * |x - y| := by
  intro x hx y hy
  have h := hf.dist_le_mul x hx y hy
  simp only [dist_eq_norm] at h
  calc ‖f x - f y‖ ≤ M * dist x y := h
    _ = M * |x - y| := by rw [Real.dist_eq]


lemma integral_abs_sub_eq_sq_div_two (a b : ℝ) :
    ∫ x in (min a b)..(max a b), |x - a| = |b - a|^2 / 2 := by
      cases le_total a b <;> simp +decide [ *, intervalIntegral.integral_comp_sub_right ];
      · rw [ intervalIntegral.integral_congr fun x hx => abs_of_nonneg ( by aesop ) ];
        rw [ intervalIntegral.integral_deriv_eq_sub' ];
        rotate_left;
        exacts [ fun x => x ^ 2 / 2, funext fun x => by norm_num, fun x hx => by norm_num, continuousOn_id, by ring ];
      · rw [ intervalIntegral.integral_congr fun x hx => abs_of_nonpos <| by linarith [ Set.mem_Icc.mp <| by rwa [ Set.uIcc_of_le ( by linarith ) ] at hx ] ];
        rw [ intervalIntegral.integral_neg ];
        rw [ intervalIntegral.integral_deriv_eq_sub' ] ; ring;
        rotate_left;
        exacts [ fun x => x ^ 2 / 2, funext fun x => by norm_num, fun x hx => by norm_num, continuousOn_id, by ring ]


/-- Taylor error bound: if f' is Lipschitz with constant L on [a,b], then
    ‖f(t) - f(t₀) - (t-t₀)·f'(t₀)‖ ≤ L * |t - t₀|²

    This is a weaker bound than the optimal L/2 * |t - t₀|², but sufficient
    for O(h²) asymptotic estimates. The proof uses MVT applied to the error
    function g(s) = f(s) - s·f'(t₀), whose derivative satisfies
    ‖g'(s)‖ = ‖f'(s) - f'(t₀)‖ ≤ L·|s - t₀| ≤ L·|t - t₀| on [t₀, t]. -/
theorem taylor_error_from_lipschitz_deriv {f : ℝ → ℂ} {a b t₀ : ℝ} {L : ℝ≥0}
    (ht₀ : t₀ ∈ Icc a b)
    (hf_cont : ContinuousOn f (Icc a b))
    (hf_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ f t)
    (hf'_lip : LipschitzOnWith L (deriv f) (Icc a b)) :
    ∀ t ∈ Icc a b, ‖f t - f t₀ - (t - t₀) • deriv f t₀‖ ≤ L * |t - t₀|^2 := by
  intro t ht
  by_cases h : t = t₀
  · simp [h]
  -- The proof strategy: apply MVT to g(s) = f(s) - s·f'(t₀)
  -- whose derivative g'(s) = f'(s) - f'(t₀) satisfies ‖g'(s)‖ ≤ L·|s - t₀| ≤ L·|t - t₀|
  -- by the Lipschitz condition on f'. Then MVT gives ‖g(t) - g(t₀)‖ ≤ L·|t - t₀|²
  --
  -- The full proof requires carefully handling:
  -- 1. Differentiability at boundary points (using continuity + interior differentiability)
  -- 2. The two cases t < t₀ and t > t₀
  -- 3. Converting the MVT bound to the desired form
  --
  -- This is a standard calculus result; the mathlib proof infrastructure
  -- requires explicit handling of all boundary cases.
  -- By the properties of the integral, we can factor out (t - t₀) from the integral.
  have h_integral_factor : ∫ s in t₀..t, (deriv f s - deriv f t₀) = f t - f t₀ - (t - t₀) * deriv f t₀ := by
    rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
    rotate_right;
    use fun x => f x - ( x - t₀ ) * deriv f t₀;
    · ring;
    · refine' ContinuousOn.sub ( hf_cont.mono _ ) _;
      · exact uIcc_subset_Icc ht₀ ht;
      · fun_prop;
    · intro x hx;
      convert HasDerivAt.hasDerivWithinAt ( HasDerivAt.sub ( hf_diff x ⟨ by cases max_cases t₀ t <;> cases min_cases t₀ t <;> linarith [ hx.1, hx.2, ht₀.1, ht₀.2, ht.1, ht.2 ], by cases max_cases t₀ t <;> cases min_cases t₀ t <;> linarith [ hx.1, hx.2, ht₀.1, ht₀.2, ht.1, ht.2 ] ⟩ |> DifferentiableAt.hasDerivAt ) ( HasDerivAt.mul ( HasDerivAt.sub ( hasDerivAt_id' x |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) ( hasDerivAt_const _ _ ) ) ) using 1 ; norm_num;
    · apply_rules [ ContinuousOn.intervalIntegrable ];
      refine' ContinuousOn.sub _ continuousOn_const;
      exact hf'_lip.continuousOn.mono ( by intro x hx; constructor <;> cases Set.mem_uIcc.mp hx <;> linarith [ ht₀.1, ht₀.2, ht.1, ht.2 ] );
  -- Using the Lipschitz condition on the derivative, we can bound the integral.
  have h_integral_bound : ‖∫ s in t₀..t, (deriv f s - deriv f t₀)‖ ≤ ∫ s in (min t₀ t)..(max t₀ t), L * |s - t₀| := by
    have h_integral_bound : ∀ s ∈ Set.Icc (min t₀ t) (max t₀ t), ‖deriv f s - deriv f t₀‖ ≤ L * |s - t₀| := by
      intro s hs;
      have := hf'_lip.dist_le_mul s ( show s ∈ Set.Icc a b from by cases max_cases t₀ t <;> cases min_cases t₀ t <;> constructor <;> linarith [ hs.1, hs.2, ht.1, ht.2, ht₀.1, ht₀.2 ] ) t₀ ( show t₀ ∈ Set.Icc a b from by cases max_cases t₀ t <;> cases min_cases t₀ t <;> constructor <;> linarith [ hs.1, hs.2, ht.1, ht.2, ht₀.1, ht₀.2 ] ) ; aesop;
    cases le_total t₀ t <;> simp_all  [ intervalIntegral, MeasureTheory.integral_Icc_eq_integral_Ioc ];
    · refine' h_integral_factor ▸ le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_integral_bound x hx.1.le hx.2;
    · rw [ ← h_integral_factor, norm_neg ];
      refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( MeasureTheory.integral_mono_of_nonneg _ _ _ );
      · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
      · exact Continuous.integrableOn_Ioc ( by continuity );
      · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with x hx using h_integral_bound x hx.1.le hx.2;
  -- We can simplify the integral $\int_{t₀}^{t} |s - t₀| \, ds$ using the fundamental theorem of calculus.
  have h_integral_simplify : ∫ s in (min t₀ t)..(max t₀ t), |s - t₀| = |t - t₀|^2 / 2 := by
    exact integral_abs_sub_eq_sq_div_two t₀ t;
  simp_all [ Complex.normSq, Complex.norm_def ];
  exact h_integral_bound.trans ( mul_le_mul_of_nonneg_left ( by nlinarith ) ( by positivity ) )


/-! ## Residue Theory Helper

The key mathlib lemmas for residue calculations:

* `circleIntegral.integral_sub_center_inv (c : ℂ) {R : ℝ} (hR : R ≠ 0)`:
  `∮ z in C(c, R), (z - c)⁻¹ = 2 * π * I`

* `circleIntegral.integral_sub_inv_of_mem_ball {c w : ℂ} {R : ℝ} (hw : w ∈ Metric.ball c R)`:
  `∮ z in C(c, R), (z - w)⁻¹ = 2 * π * I`

Use these lemmas directly from mathlib for residue computations.
-/

/-! ## Connectedness -/

/-- The unit interval [0,1] is preconnected. -/
theorem isPreconnected_Icc_01' : IsPreconnected (Icc (0:ℝ) 1) :=
  isPreconnected_Icc

/-- A locally constant function on a preconnected set takes the same value at any two points. -/
theorem locally_constant_on_preconnected' {α : Type*} {β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [T1Space β]
    {s : Set α} (hs : IsPreconnected s)
    {f : α → β} (hf : IsLocallyConstant f)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    f x = f y :=
  hf.apply_eq_of_isPreconnected hs hx hy

/-! ## FTC-based Zero Isolation

The key lemma for proving finiteness of zeros in GeneralizedResidueTheorem.
This captures the pattern: if γ(t₁) = γ(t₂) = z₀ and γ' is bounded away from 0,
then |t₂ - t₁| cannot be arbitrarily small.
-/

/-- FTC-based zero isolation (CORRECT VERSION): If γ' stays close to a fixed
    nonzero vector L on [t₁, t₂], then ‖γ(t₂) - γ(t₁)‖ is bounded below.

    **Key insight**: When ‖γ'(t) - L‖ < ‖L‖/2 for all t, the derivative stays
    in a half-plane centered on L, so the integral cannot cancel out.

    The proof uses the real part projection: if γ' is close to L, then
    Re⟨γ'(t), L/‖L‖⟩ > ‖L‖/2, and integrating gives the bound.

    **Isabelle parallel**: Similar to `has_integral_bound_real` arguments. -/
theorem ftc_zero_isolation_strong {γ : ℝ → ℂ} {t₁ t₂ : ℝ} {L : ℂ} (ht : t₁ < t₂)
    (hL : L ≠ 0)
    (hγ_cont : ContinuousOn γ (Icc t₁ t₂))
    (hγ_diff : ∀ t ∈ Ioo t₁ t₂, DifferentiableAt ℝ γ t)
    (hγ'_close : ∀ t ∈ Icc t₁ t₂, ‖deriv γ t - L‖ < ‖L‖ / 2) :
    ‖L‖ / 2 * (t₂ - t₁) ≤ ‖γ t₂ - γ t₁‖ := by
  /-
  Proof outline:
  1. The condition ‖γ'(t) - L‖ < ‖L‖/2 implies the derivative stays in a half-plane
  2. Using the inner product: Re⟨γ'(t), L⟩ ≥ ‖L‖² - ‖γ'(t) - L‖·‖L‖ > ‖L‖²/2
  3. By FTC: γ(t₂) - γ(t₁) = ∫_{t₁}^{t₂} γ'(t) dt
  4. Taking inner product with L and using linearity:
     Re⟨γ(t₂) - γ(t₁), L⟩ = ∫ Re⟨γ'(t), L⟩ dt ≥ (t₂-t₁)·‖L‖²/2
  5. By Cauchy-Schwarz: ‖γ(t₂) - γ(t₁)‖·‖L‖ ≥ |Re⟨γ(t₂) - γ(t₁), L⟩| ≥ (t₂-t₁)·‖L‖²/2
  6. Dividing by ‖L‖: ‖γ(t₂) - γ(t₁)‖ ≥ (t₂-t₁)·‖L‖/2

  The full proof requires the FTC for complex-valued functions and integral bounds.
  We defer the detailed verification to focus on the structure.
  -/
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL

  -- Inner product bound: Re⟨γ'(t), L⟩ > ‖L‖²/2 when ‖γ'(t) - L‖ < ‖L‖/2
  have h_inner_lb : ∀ t ∈ Icc t₁ t₂, ‖L‖^2 / 2 < (deriv γ t * starRingEnd ℂ L).re := by
    intro t ht
    have h_close := hγ'_close t ht
    have h1 : (deriv γ t * starRingEnd ℂ L).re =
        (L * starRingEnd ℂ L).re + ((deriv γ t - L) * starRingEnd ℂ L).re := by
      simp only [sub_mul, Complex.sub_re]; ring
    rw [h1]
    have h_normSq : (L * starRingEnd ℂ L).re = ‖L‖^2 := by rw [Complex.mul_conj']; norm_cast
    rw [h_normSq]
    have h_err_bound : |((deriv γ t - L) * starRingEnd ℂ L).re| ≤ ‖deriv γ t - L‖ * ‖L‖ := by
      calc |((deriv γ t - L) * starRingEnd ℂ L).re|
          ≤ ‖(deriv γ t - L) * starRingEnd ℂ L‖ := Complex.abs_re_le_norm _
        _ ≤ ‖deriv γ t - L‖ * ‖starRingEnd ℂ L‖ := norm_mul_le _ _
        _ = ‖deriv γ t - L‖ * ‖L‖ := by rw [RingHomIsometric.norm_map]
    have h_err_strict : |((deriv γ t - L) * starRingEnd ℂ L).re| < ‖L‖^2 / 2 := by
      calc |((deriv γ t - L) * starRingEnd ℂ L).re|
          ≤ ‖deriv γ t - L‖ * ‖L‖ := h_err_bound
        _ < (‖L‖ / 2) * ‖L‖ := by nlinarith
        _ = ‖L‖^2 / 2 := by ring
    linarith [neg_abs_le ((deriv γ t - L) * starRingEnd ℂ L).re]

  -- Derivative bound: ‖deriv γ t‖ ≤ 3‖L‖/2
  have h_deriv_bdd : ∀ t ∈ Icc t₁ t₂, ‖deriv γ t‖ ≤ 3 * ‖L‖ / 2 := by
    intro t ht
    have h_tri : ‖deriv γ t‖ ≤ ‖L‖ + ‖deriv γ t - L‖ := norm_le_insert' (deriv γ t) L
    linarith [hγ'_close t ht]

  -- Right derivative
  have h_hasDeriv : ∀ x ∈ Ioo t₁ t₂, HasDerivWithinAt γ (deriv γ x) (Ioi x) x := by
    intro x hx; exact (hγ_diff x hx).hasDerivAt.hasDerivWithinAt

  -- Integrability of deriv γ
  have h_int : IntervalIntegrable (deriv γ) MeasureTheory.volume t₁ t₂ := by
    rw [intervalIntegrable_iff]
    have h_uIcc : Set.uIcc t₁ t₂ = Set.Icc t₁ t₂ := Set.uIcc_of_le (le_of_lt ht)
    refine MeasureTheory.IntegrableOn.of_bound ?_ ?_ (3 * ‖L‖ / 2) ?_
    · simp only [Set.uIoc, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · exact (aestronglyMeasurable_deriv γ _).restrict
    · -- The bound holds ae on the restriction
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
      apply Filter.Eventually.of_forall
      intro t ht'
      exact h_deriv_bdd t (h_uIcc ▸ Set.uIoc_subset_uIcc ht')

  -- FTC
  have h_ftc : ∫ t in t₁..t₂, deriv γ t = γ t₂ - γ t₁ := by
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (le_of_lt ht) hγ_cont h_hasDeriv h_int]

  -- Define projection: z ↦ Re(z * conj L)
  let proj : ℂ →L[ℝ] ℝ := {
    toFun := fun z => (z * starRingEnd ℂ L).re
    map_add' := by intro x y; simp [add_mul, Complex.add_re]
    map_smul' := by
      intro c z
      rw [Complex.real_smul, mul_assoc, Complex.mul_re, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, RingHom.id_apply, smul_eq_mul]
      ring
    cont := Complex.continuous_re.comp (continuous_mul_right _)
  }

  -- Linearity of integral
  have h_proj_int : proj (∫ t in t₁..t₂, deriv γ t) = ∫ t in t₁..t₂, proj (deriv γ t) :=
    (proj.intervalIntegral_comp_comm h_int).symm

  -- Lower bound on integral
  have h_int_lb : ‖L‖^2 / 2 * (t₂ - t₁) ≤ ((γ t₂ - γ t₁) * starRingEnd ℂ L).re := by
    have h_re_eq : ((γ t₂ - γ t₁) * starRingEnd ℂ L).re =
        ∫ t in t₁..t₂, (deriv γ t * starRingEnd ℂ L).re := by
      calc ((γ t₂ - γ t₁) * starRingEnd ℂ L).re
          = proj (γ t₂ - γ t₁) := rfl
        _ = proj (∫ t in t₁..t₂, deriv γ t) := by rw [← h_ftc]
        _ = ∫ t in t₁..t₂, proj (deriv γ t) := h_proj_int
    rw [h_re_eq]
    calc ‖L‖^2 / 2 * (t₂ - t₁)
        = ∫ _ in t₁..t₂, ‖L‖^2 / 2 := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul]; ring
      _ ≤ ∫ t in t₁..t₂, (deriv γ t * starRingEnd ℂ L).re := by
          -- Integrability of composition with continuous linear map
          have h_proj_int' : IntervalIntegrable (fun t => proj (deriv γ t)) MeasureTheory.volume t₁ t₂ := by
            rw [intervalIntegrable_iff] at h_int ⊢
            exact proj.integrable_comp h_int
          -- Use integral_mono_on which takes the bound on Icc
          exact intervalIntegral.integral_mono_on (le_of_lt ht) intervalIntegrable_const h_proj_int' (fun t ht' => le_of_lt (h_inner_lb t ht'))

  -- Cauchy-Schwarz
  have h_cs : ((γ t₂ - γ t₁) * starRingEnd ℂ L).re ≤ ‖γ t₂ - γ t₁‖ * ‖L‖ := by
    calc ((γ t₂ - γ t₁) * starRingEnd ℂ L).re
        ≤ |((γ t₂ - γ t₁) * starRingEnd ℂ L).re| := le_abs_self _
      _ ≤ ‖(γ t₂ - γ t₁) * starRingEnd ℂ L‖ := Complex.abs_re_le_norm _
      _ ≤ ‖γ t₂ - γ t₁‖ * ‖starRingEnd ℂ L‖ := norm_mul_le _ _
      _ = ‖γ t₂ - γ t₁‖ * ‖L‖ := by rw [RingHomIsometric.norm_map]

  -- Combine
  calc ‖L‖ / 2 * (t₂ - t₁)
      = (‖L‖^2 / 2 * (t₂ - t₁)) / ‖L‖ := by field_simp [ne_of_gt hL_norm_pos]
    _ ≤ (‖γ t₂ - γ t₁‖ * ‖L‖) / ‖L‖ := div_le_div_of_nonneg_right (le_trans h_int_lb h_cs) (le_of_lt hL_norm_pos)
    _ = ‖γ t₂ - γ t₁‖ := by field_simp [ne_of_gt hL_norm_pos]

/-- Simplified version: derivative bounded below AND close to some direction.
    This is the version most useful for the valence formula proofs. -/
theorem ftc_zero_isolation {γ : ℝ → ℂ} {t₁ t₂ c : ℝ} {L : ℂ} (ht : t₁ < t₂) (_hc : 0 < c)
    (hL : L ≠ 0) (hL_norm : ‖L‖ / 2 = c)
    (hγ_cont : ContinuousOn γ (Icc t₁ t₂))
    (hγ_diff : ∀ t ∈ Ioo t₁ t₂, DifferentiableAt ℝ γ t)
    (hγ'_close : ∀ t ∈ Icc t₁ t₂, ‖deriv γ t - L‖ < ‖L‖ / 2) :
    c * (t₂ - t₁) ≤ ‖γ t₂ - γ t₁‖ := by
  rw [← hL_norm]
  exact ftc_zero_isolation_strong ht hL hγ_cont hγ_diff hγ'_close

/-- Corollary: If γ(t₁) = γ(t₂) and γ' is close to a fixed nonzero L on [t₁, t₂],
    then t₁ = t₂. This provides the FTC contradiction pattern. -/
theorem ftc_zeros_coincide {γ : ℝ → ℂ} {z₀ : ℂ} {t₁ t₂ : ℝ} {L : ℂ} (ht : t₁ ≤ t₂)
    (hL : L ≠ 0)
    (hγ_cont : ContinuousOn γ (Icc t₁ t₂))
    (hγ_diff : ∀ t ∈ Ioo t₁ t₂, DifferentiableAt ℝ γ t)
    (hγ'_close : ∀ t ∈ Icc t₁ t₂, ‖deriv γ t - L‖ < ‖L‖ / 2)
    (hγ_t₁ : γ t₁ = z₀) (hγ_t₂ : γ t₂ = z₀) :
    t₁ = t₂ := by
  rcases ht.lt_or_eq with hlt | heq
  · -- If t₁ < t₂, use ftc_zero_isolation_strong to derive contradiction
    have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
    have h := ftc_zero_isolation_strong hlt hL hγ_cont hγ_diff hγ'_close
    rw [hγ_t₁, hγ_t₂, sub_self, norm_zero] at h
    have h' : 0 < ‖L‖ / 2 * (t₂ - t₁) := mul_pos (half_pos hL_norm_pos) (sub_pos.mpr hlt)
    linarith
  · exact heq

/-- Zeros of a curve with derivative close to a fixed L are isolated.

    **Key Lemma for GeneralizedResidueTheorem**: If γ' stays close to some L ≠ 0
    on [a, b], then the preimage of any point z₀ under γ has at most one element.

    This is the core FTC argument used throughout the zero finiteness proofs. -/
theorem zeros_uniformly_isolated_of_deriv_close {γ : ℝ → ℂ} {z₀ : ℂ} {a b : ℝ} {L : ℂ}
    (_hab : a < b) (hL : L ≠ 0)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ'_close : ∀ t ∈ Icc a b, ‖deriv γ t - L‖ < ‖L‖ / 2) :
    ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b, γ t₁ = z₀ → γ t₂ = z₀ → t₁ = t₂ := by
  intro t₁ ht₁ t₂ ht₂ hγt₁ hγt₂
  rcases le_or_gt t₁ t₂ with h | h
  · exact ftc_zeros_coincide h hL
      (hγ_cont.mono (Icc_subset_Icc ht₁.1 ht₂.2))
      (fun t ht => hγ_diff t ⟨lt_of_le_of_lt ht₁.1 ht.1, lt_of_lt_of_le ht.2 ht₂.2⟩)
      (fun t ht => hγ'_close t ⟨le_trans ht₁.1 ht.1, le_trans ht.2 ht₂.2⟩)
      hγt₁ hγt₂
  · have : t₂ = t₁ := ftc_zeros_coincide (le_of_lt h) hL
      (hγ_cont.mono (Icc_subset_Icc ht₂.1 ht₁.2))
      (fun t ht => hγ_diff t ⟨lt_of_le_of_lt ht₂.1 ht.1, lt_of_lt_of_le ht.2 ht₁.2⟩)
      (fun t ht => hγ'_close t ⟨le_trans ht₂.1 ht.1, le_trans ht.2 ht₁.2⟩)
      hγt₂ hγt₁
    exact this.symm

/-! ## Dominated Convergence Helper -/

/-- If F_ε → F pointwise as ε → 0⁺, and |F_ε| ≤ g for all ε, with g integrable,
    then ∫ F_ε → ∫ F as ε → 0⁺.

    This is a restatement of dominated convergence for parametric integrals.
    The hypotheses use uIoc (= Ι a b = Ioc (min a b) (max a b)) to match the
    region of integration for interval integrals. -/
theorem tendsto_integral_of_dominated' {a b : ℝ}
    {F : ℝ → ℝ → ℂ} {f : ℝ → ℂ} {g : ℝ → ℝ}
    (hF_meas : ∀ ε > 0, AEStronglyMeasurable (F ε) (volume.restrict (Ι a b)))
    (hF_le : ∀ ε > 0, ∀ᵐ t ∂volume, t ∈ Ι a b → ‖F ε t‖ ≤ g t)
    (hg_int : IntervalIntegrable g volume a b)
    (hF_lim : ∀ᵐ t ∂volume, t ∈ Ι a b → Tendsto (fun ε => F ε t) (𝓝[>] 0) (𝓝 (f t))) :
    Tendsto (fun ε => ∫ t in a..b, F ε t) (𝓝[>] 0) (𝓝 (∫ t in a..b, f t)) := by
  -- Direct application of mathlib's dominated convergence theorem for interval integrals
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hg_int ?_
  · -- Measurability
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hF_meas ε hε
  · -- Bound
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact hF_le ε hε
  · -- Limit
    exact hF_lim

end
