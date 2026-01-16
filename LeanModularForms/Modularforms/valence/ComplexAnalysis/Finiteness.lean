/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d34eef7e-5854-4c7b-8077-358ddd88f2b2

The following was proved by Aristotle:

- theorem zeros_isolated_on_smooth_segment
    (c d : ℝ) (hcd : c < d)
    (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_disjoint : Disjoint (Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc c d) (hγt₀ : γ.toFun t₀ = z₀) :
    ∃ ε > 0, ∀ t ∈ Icc c d, t ≠ t₀ → |t - t₀| < ε → γ.toFun t ≠ z₀

- theorem zeros_uniformly_separated_on_smooth_segment
    (c d : ℝ) (hcd : c < d)
    (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_disjoint : Disjoint (Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ)) :
    ∃ ε > 0, ∀ t₁ t₂ : ℝ, t₁ ∈ Icc c d → t₂ ∈ Icc c d →
      γ.toFun t₁ = z₀ → γ.toFun t₂ = z₀ → t₁ ≠ t₂ → ε ≤ |t₁ - t₂|

- theorem zeros_finite_on_smooth_segment
    (c d : ℝ) (hcd : c < d)
    (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_disjoint : Disjoint (Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ)) :
    Set.Finite {t ∈ Icc c d | γ.toFun t = z₀}

- theorem zeros_isolated_left_of_partition
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : γ.a < p) :
    ∃ δ > 0, ∀ t₁ ∈ Ioo (p - δ) p, ∀ t₂ ∈ Ioo (p - δ) p,
      γ.toFun t₁ = z₀ → γ.toFun t₂ = z₀ → t₁ ≠ t₂ →
      ∃ ε > 0, ε ≤ |t₁ - t₂|

- theorem zeros_finite_left_of_partition
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : γ.a < p) :
    Set.Finite {t ∈ Icc γ.a p | t ∉ γ.toPiecewiseC1Curve.partition ∧ γ.toFun t = z₀}

- theorem zeros_finite_right_of_partition
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : p < γ.b) :
    Set.Finite {t ∈ Icc p γ.b | t ∉ γ.toPiecewiseC1Curve.partition ∧ γ.toFun t = z₀}

- theorem piecewiseC1Immersion_finite_zeros :
    Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀}
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic


/-!
# Finiteness of Zeros for Piecewise C¹ Immersions

This file proves that a piecewise C¹ immersion has only finitely many zeros
(points where γ(t) = z₀). This is a key ingredient for the winding number
decomposition theorem.

## Main Results

* `zeros_isolated_on_smooth_segment` - Zeros are isolated on smooth segments
* `zeros_finite_on_smooth_segment` - Finitely many zeros on each smooth segment
* `zeros_finite_near_partition` - Finitely many zeros near partition points
* `piecewiseC1Immersion_finite_zeros` - Total finiteness result

## Strategy

The proof proceeds by:
1. On smooth segments (away from partition points), the derivative is nonzero,
   so by the inverse function theorem, zeros are isolated.
2. Near partition points, we use the one-sided derivative limits (which are
   nonzero by the immersion condition) to show isolation from each side.
3. Combine using finiteness of the partition.

## References

* The isolation of zeros follows from the inverse function theorem
* Not directly in Isabelle (which assumes paths avoid singularities)
-/

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

noncomputable section

variable (γ : PiecewiseC1Immersion) (z₀ : ℂ)

/-! ## Isolation of Zeros on Smooth Segments -/

/-- On a smooth segment where the derivative is nonzero, zeros of γ - z₀ are isolated.
    This follows from the inverse function theorem. -/
theorem zeros_isolated_on_smooth_segment
    (c d : ℝ) (hcd : c < d)
    (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_disjoint : Disjoint (Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Icc c d) (hγt₀ : γ.toFun t₀ = z₀) :
    ∃ ε > 0, ∀ t ∈ Icc c d, t ≠ t₀ → |t - t₀| < ε → γ.toFun t ≠ z₀ := by
  -- The derivative at t₀ is nonzero
  have h_deriv_ne : deriv γ.toFun t₀ ≠ 0 := by
    apply γ.deriv_ne_zero t₀ (h_sub ht₀)
    intro h_in_partition
    exact Set.disjoint_left.mp h_disjoint ht₀ h_in_partition
  -- By continuity of deriv, |deriv γ t| > δ for t near t₀
  -- Then γ is locally injective, so zeros are isolated
  have := hasDerivAt_deriv_iff.mpr ( show DifferentiableAt ℝ γ.toFun t₀ from ( γ.smooth_off_partition t₀ ( h_sub ht₀ ) <| by intro H; exact h_disjoint.le_bot ⟨ ht₀, H ⟩ ) );
  have := this.tendsto_slope_zero;
  have := Metric.tendsto_nhdsWithin_nhds.mp this;
  obtain ⟨ δ, δ_pos, H ⟩ := this ( ‖deriv γ.toFun t₀‖ ) ( norm_pos_iff.mpr h_deriv_ne ) ; use δ, δ_pos; intro t ht ht' ht''; specialize H ( show t - t₀ ≠ 0 from sub_ne_zero.mpr ht' ) ( by simpa using ht'' ) ; simp_all +decide [ div_eq_inv_mul ] ;
  contrapose! H; simp_all +decide [ sub_eq_iff_eq_add ] ;

/-- The minimum separation between distinct zeros on a smooth segment. -/
theorem zeros_uniformly_separated_on_smooth_segment
    (c d : ℝ) (hcd : c < d)
    (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_disjoint : Disjoint (Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ)) :
    ∃ ε > 0, ∀ t₁ t₂ : ℝ, t₁ ∈ Icc c d → t₂ ∈ Icc c d →
      γ.toFun t₁ = z₀ → γ.toFun t₂ = z₀ → t₁ ≠ t₂ → ε ≤ |t₁ - t₂| := by
  have h_finite_zeros : Set.Finite {t ∈ Set.Icc c d | γ.toFun t = z₀} := by
    -- Since the zeros are isolated, the set of zeros in [c, d] is discrete.
    have h_discrete : DiscreteTopology {t ∈ Set.Icc c d | γ.toFun t = z₀} := by
      -- The set of zeros of γ - z₀ on [c, d] is discrete because it is isolated.
      have h_isolated : ∀ t ∈ {t ∈ Set.Icc c d | γ.toFun t = z₀}, ∃ ε > 0, ∀ t' ∈ Set.Icc c d, |t' - t| < ε → (γ.toFun t' = z₀ → t' = t) := by
        intro t ht;
        have := zeros_isolated_on_smooth_segment γ z₀ c d hcd h_sub h_disjoint t ht.1 ht.2;
        exact ⟨ this.choose, this.choose_spec.1, fun t' ht' ht'' ht''' => Classical.not_not.1 fun h => this.choose_spec.2 t' ht' h ht'' ht''' ⟩;
      refine' singletons_open_iff_discrete.mp _;
      rintro ⟨ t, ht ⟩ ; specialize h_isolated t ht; rcases h_isolated with ⟨ ε, ε_pos, hε ⟩ ; refine' Metric.isOpen_iff.mpr _; aesop;
    have h_compact : IsCompact {t ∈ Set.Icc c d | γ.toFun t = z₀} := by
      have h_closed : IsClosed {t ∈ Set.Icc c d | γ.toFun t = z₀} := by
        have h_closed : ContinuousOn γ.toFun (Set.Icc c d) := by
          exact γ.toPiecewiseC1Curve.continuous_toFun.mono h_sub;
        exact h_closed.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton;
      exact CompactIccSpace.isCompact_Icc.of_isClosed_subset h_closed fun x hx => hx.1;
    exact IsCompact.finite h_compact h_discrete;
  -- Since the set of zeros is finite, we can choose a minimum distance ε between any two distinct zeros.
  obtain ⟨ε, hε_pos, hε_min⟩ : ∃ ε > 0, ∀ t₁ t₂, t₁ ∈ h_finite_zeros.toFinset → t₂ ∈ h_finite_zeros.toFinset → t₁ ≠ t₂ → ε ≤ |t₁ - t₂| := by
    have h_min_dist : ∃ ε > 0, ∀ t₁ t₂, t₁ ∈ h_finite_zeros.toFinset → t₂ ∈ h_finite_zeros.toFinset → t₁ ≠ t₂ → ε ≤ |t₁ - t₂| := by
      have h_nonempty : Finset.Nonempty (Finset.offDiag h_finite_zeros.toFinset) → ∃ ε > 0, ∀ t₁ t₂, t₁ ∈ h_finite_zeros.toFinset → t₂ ∈ h_finite_zeros.toFinset → t₁ ≠ t₂ → ε ≤ |t₁ - t₂| := by
        intro h_nonempty
        obtain ⟨ε, hε_pos, hε_min⟩ : ∃ ε ∈ Finset.image (fun p : ℝ × ℝ => |p.1 - p.2|) (Finset.offDiag h_finite_zeros.toFinset), ∀ p ∈ Finset.image (fun p : ℝ × ℝ => |p.1 - p.2|) (Finset.offDiag h_finite_zeros.toFinset), ε ≤ p := by
          exact ⟨ Finset.min' _ ⟨ _, Finset.mem_image_of_mem _ h_nonempty.choose_spec ⟩, Finset.min'_mem _ _, fun p hp => Finset.min'_le _ _ hp ⟩;
        exact ⟨ ε, by obtain ⟨ p, hp₁, rfl ⟩ := Finset.mem_image.mp hε_pos; exact abs_pos.mpr ( sub_ne_zero.mpr <| by aesop ), fun t₁ t₂ ht₁ ht₂ hne => hε_min _ <| Finset.mem_image.mpr ⟨ ( t₁, t₂ ), Finset.mem_offDiag.mpr ⟨ ht₁, ht₂, hne ⟩, rfl ⟩ ⟩
      by_cases h_empty : Finset.offDiag h_finite_zeros.toFinset = ∅;
      · exact ⟨ 1, zero_lt_one, fun t₁ t₂ ht₁ ht₂ hne => False.elim <| hne <| by rw [ Finset.ext_iff ] at h_empty; specialize h_empty ( t₁, t₂ ) ; aesop ⟩;
      · exact h_nonempty <| Finset.nonempty_of_ne_empty h_empty;
    exact h_min_dist;
  exact ⟨ ε, hε_pos, fun t₁ t₂ ht₁ ht₂ ht₁' ht₂' hne => hε_min t₁ t₂ ( h_finite_zeros.mem_toFinset.mpr ⟨ ht₁, ht₁' ⟩ ) ( h_finite_zeros.mem_toFinset.mpr ⟨ ht₂, ht₂' ⟩ ) hne ⟩

/-- Finitely many zeros on a smooth segment (compact + isolated → finite). -/
theorem zeros_finite_on_smooth_segment
    (c d : ℝ) (hcd : c < d)
    (h_sub : Icc c d ⊆ Icc γ.a γ.b)
    (h_disjoint : Disjoint (Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ)) :
    Set.Finite {t ∈ Icc c d | γ.toFun t = z₀} := by
  -- Use uniform separation + compactness
  obtain ⟨ε, hε_pos, hε_sep⟩ := zeros_uniformly_separated_on_smooth_segment γ z₀ c d hcd h_sub h_disjoint
  -- A compact set with ε-separated points is finite
  have h_finite_zeros_on_segment : IsCompact {t : ℝ | t ∈ Set.Icc c d ∧ γ.toFun t = z₀} := by
    have h_closed : IsClosed {t : ℝ | t ∈ Set.Icc c d ∧ γ.toFun t = z₀} := by
      have h_continuous : ContinuousOn γ.toFun (Set.Icc c d) := by
        exact γ.toPiecewiseC1Curve.continuous_toFun.mono h_sub;
      exact h_continuous.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton;
    exact CompactIccSpace.isCompact_Icc.of_isClosed_subset h_closed fun x hx => hx.1;
  have h_finite_zeros_on_segment : DiscreteTopology {t : ℝ | t ∈ Set.Icc c d ∧ γ.toFun t = z₀} := by
    refine' singletons_open_iff_discrete.mp _;
    intro a;
    rw [ Metric.isOpen_iff ];
    norm_num +zetaDelta at *;
    exact ⟨ ε, hε_pos, fun t ht₁ ht₂ ht₃ ht₄ => Classical.not_not.1 fun ht₅ => not_lt_of_ge ( hε_sep t a.1 ht₁ ht₂ a.2.1.1 a.2.1.2 ht₃ a.2.2 <| by aesop ) <| by simpa [ Subtype.dist_eq ] using ht₄ ⟩;
  (expose_names; exact IsCompact.finite h_finite_zeros_on_segment_1 h_finite_zeros_on_segment)

/-! ## Zeros Near Partition Points -/

/-- Near a partition point p, from the left side, zeros are isolated.
    Uses the left derivative limit being nonzero. -/
theorem zeros_isolated_left_of_partition
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : γ.a < p) :
    ∃ δ > 0, ∀ t₁ ∈ Ioo (p - δ) p, ∀ t₂ ∈ Ioo (p - δ) p,
      γ.toFun t₁ = z₀ → γ.toFun t₂ = z₀ → t₁ ≠ t₂ →
      ∃ ε > 0, ε ≤ |t₁ - t₂| := by
  -- Get the left derivative limit L ≠ 0
  obtain ⟨L, hL_ne, hL_tendsto⟩ := γ.left_deriv_limit p hp_part hp_interior
  -- Near p from the left, |deriv γ| > |L|/2 > 0
  -- This gives isolation
  exact ⟨ 1, by norm_num, fun t₁ ht₁ t₂ ht₂ h₁ h₂ h₃ => ⟨ |t₁ - t₂|, abs_pos.mpr <| sub_ne_zero.mpr h₃, le_rfl ⟩ ⟩

/- Finitely many zeros to the left of a partition point. -/
noncomputable section AristotleLemmas

/-
If the difference quotient (f(t) - f(p)) / (t - p) converges to a non-zero limit L along a filter F (where t ≠ p), then f(t) ≠ f(p) eventually along F.
-/
lemma eventually_ne_of_tendsto_diff_quotient_ne_zero {f : ℝ → ℂ} {p : ℝ} {L : ℂ} {F : Filter ℝ}
    (h_deriv : Tendsto (fun t => (f t - f p) / (t - p)) F (𝓝 L))
    (hL : L ≠ 0)
    (hF : F ≤ 𝓝[≠] p) :
    ∀ᶠ t in F, f t ≠ f p := by
      have := h_deriv.eventually_ne hL;
      filter_upwards [ this ] with t ht using by aesop;

/-
If the derivative of a function f tends to L as t approaches p from the left, then the difference quotient (f(p) - f(t)) / (p - t) also tends to L.
-/
lemma tendsto_diff_quotient_of_tendsto_deriv_left
    {f : ℝ → ℂ} {p : ℝ} {L : ℂ} {a : ℝ} (hap : a < p)
    (h_cont : ContinuousOn f (Set.Icc a p))
    (h_diff : DifferentiableOn ℝ f (Set.Ioo a p))
    (h_lim : Filter.Tendsto (deriv f) (𝓝[<] p) (𝓝 L)) :
    Filter.Tendsto (fun t => (f p - f t) / (p - t)) (𝓝[<] p) (𝓝 L) := by
      have h_diff_quot : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Ioo (p - δ) p, ‖(f p - f t) / (p - t) - L‖ < ε := by
        intro ε ε_pos
        obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ t ∈ Set.Ioo (p - δ) p, ‖deriv f t - L‖ < ε / 2 := by
          have := Metric.tendsto_nhdsWithin_nhds.mp h_lim ( ε / 2 ) ( half_pos ε_pos );
          exact ⟨ this.choose, this.choose_spec.1, fun t ht => this.choose_spec.2 ht.2 ( abs_lt.mpr ⟨ by linarith [ ht.1, ht.2 ], by linarith [ ht.1, ht.2 ] ⟩ ) ⟩;
        -- Apply the Mean Value Inequality to the interval [t, p].
        have h_mvt : ∀ t ∈ Set.Ioo (max a (p - δ)) p, ‖(f p - f t) / (p - t) - L‖ ≤ ε / 2 := by
          intro t ht
          have h_mvt : ‖(f p - f t) - L * (p - t)‖ ≤ (ε / 2) * (p - t) := by
            have h_mvt : ∀ x ∈ Set.Ioo t p, ‖deriv (fun x => f x - L * x) x‖ ≤ ε / 2 := by
              intro x hx
              have h_deriv : deriv (fun x => f x - L * x) x = deriv f x - L := by
                convert HasDerivAt.deriv ( HasDerivAt.sub ( h_diff.hasDerivAt ( Ioo_mem_nhds ( by linarith [ hx.1, ht.1, le_max_left a ( p - δ ) ] ) ( by linarith [ hx.2, ht.2, le_max_right a ( p - δ ) ] ) ) ) ( HasDerivAt.const_mul L ( hasDerivAt_id x |> HasDerivAt.ofReal_comp ) ) ) using 1 ; norm_num;
              exact h_deriv.symm ▸ le_of_lt ( hδ x ⟨ by linarith [ hx.1, ht.1, le_max_right a ( p - δ ) ], by linarith [ hx.2, ht.2 ] ⟩ );
            have h_mvt : ‖(f p - f t) - L * (p - t)‖ ≤ (ε / 2) * (p - t) := by
              have h_mvt : ∀ x ∈ Set.Ioo t p, ‖deriv (fun x => f x - L * x) x‖ ≤ ε / 2 := h_mvt
              have h_mvt_integral : ‖∫ x in t..p, deriv (fun x => f x - L * x) x‖ ≤ (ε / 2) * (p - t) := by
                rw [ intervalIntegral.integral_of_le ht.2.le ];
                refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
                refine' fun x => ε / 2;
                · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
                · norm_num;
                · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc, MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton p ) ] with x hx₁ hx₂ using h_mvt x ⟨ hx₁.1, lt_of_le_of_ne hx₁.2 hx₂ ⟩;
                · norm_num [ mul_comm, ht.2.le ]
              convert h_mvt_integral using 1;
              rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
              rotate_right;
              use fun x => f x - L * x;
              · ring;
              · exact ContinuousOn.sub ( h_cont.mono ( by intro x hx; constructor <;> cases Set.mem_uIcc.mp hx <;> linarith [ ht.1, ht.2, le_max_left a ( p - δ ), le_max_right a ( p - δ ) ] ) ) ( Continuous.continuousOn ( by continuity ) );
              · intro x hx; exact DifferentiableAt.hasDerivAt ( by exact DifferentiableAt.sub ( h_diff.differentiableAt ( Ioo_mem_nhds ( by cases max_cases a ( p - δ ) <;> cases min_cases t p <;> cases max_cases t p <;> linarith [ hx.1, hx.2, ht.1, ht.2 ] ) ( by cases max_cases a ( p - δ ) <;> cases min_cases t p <;> cases max_cases t p <;> linarith [ hx.1, hx.2, ht.1, ht.2 ] ) ) ) ( DifferentiableAt.mul ( differentiableAt_const _ ) ( Complex.ofRealCLM.differentiableAt ) ) ) |> HasDerivAt.hasDerivWithinAt;
              · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le ht.2.le ];
                refine' MeasureTheory.Integrable.mono' _ _ _;
                exacts [ fun _ => ε / 2, by norm_num, by exact ( measurable_deriv _ |> Measurable.aestronglyMeasurable ), Filter.eventually_of_mem ( MeasureTheory.ae_restrict_mem measurableSet_Ioo ) fun x hx => h_mvt x hx ];
            exact h_mvt;
          rw [ div_sub' ];
          · rw [ mul_comm, norm_div ];
            rw [ div_le_iff₀ ] <;> norm_cast;
            · simpa [ abs_of_pos ( sub_pos.mpr ht.2 ) ] using h_mvt;
            · exact norm_pos_iff.mpr ( sub_ne_zero.mpr ht.2.ne' );
          · exact sub_ne_zero_of_ne ( by norm_cast; linarith [ ht.1, ht.2 ] );
        exact ⟨ Min.min ( p - Max.max a ( p - δ ) ) δ, lt_min ( sub_pos.mpr <| by cases max_cases a ( p - δ ) <;> linarith ) δ_pos, fun t ht => lt_of_le_of_lt ( h_mvt t ⟨ by linarith [ ht.1, min_le_left ( p - Max.max a ( p - δ ) ) δ ], by linarith [ ht.2, min_le_left ( p - Max.max a ( p - δ ) ) δ ] ⟩ ) <| by linarith ⟩;
      rw [ Metric.tendsto_nhdsWithin_nhds ];
      exact fun ε hε => by obtain ⟨ δ, hδ, H ⟩ := h_diff_quot ε hε; exact ⟨ δ, hδ, fun x hx₁ hx₂ => by simpa [ dist_eq_norm ] using H x ⟨ by linarith [ abs_lt.mp hx₂ ], hx₁ ⟩ ⟩ ;

/-
There exists a small interval to the left of a partition point p where γ(t) is never equal to z₀.
-/
lemma no_zeros_left_of_partition
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : γ.a < p) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (p - δ) p, γ.toFun t ≠ z₀ := by
      -- Let's split into two cases: γ(p) ≠ z₀ and γ(p) = z₀.
      by_cases h_case : γ.toFun p ≠ z₀;
      · have := Metric.continuousOn_iff.mp γ.continuous_toFun p ( show p ∈ Set.Icc γ.a γ.b from Set.mem_Icc.mpr ⟨ hp_interior.le, by linarith [ γ.partition_subset hp_part |>.2 ] ⟩ );
        obtain ⟨ δ, hδ₁, hδ₂ ⟩ := this ( Dist.dist ( γ.toFun p ) z₀ ) ( dist_pos.mpr h_case );
        exact ⟨ Min.min δ ( p - γ.a ), lt_min hδ₁ ( sub_pos.mpr hp_interior ), fun t ht => fun h => by have := hδ₂ t ⟨ by linarith [ ht.1, min_le_left δ ( p - γ.a ), min_le_right δ ( p - γ.a ) ], by linarith [ ht.2, min_le_left δ ( p - γ.a ), min_le_right δ ( p - γ.a ), γ.toPiecewiseC1Curve.partition_subset hp_part |>.2 ] ⟩ ( abs_lt.mpr ⟨ by linarith [ ht.1, min_le_left δ ( p - γ.a ), min_le_right δ ( p - γ.a ) ], by linarith [ ht.2, min_le_left δ ( p - γ.a ), min_le_right δ ( p - γ.a ) ] ⟩ ) ; simp_all +decide [ dist_comm ] ⟩;
      · -- Since γ is a PiecewiseC1Immersion, the left derivative limit at p exists and is nonzero.
        obtain ⟨L, hL_ne_zero, hL_limit⟩ : ∃ L : ℂ, L ≠ 0 ∧ Tendsto (deriv γ.toFun) (𝓝[<] p) (𝓝 L) := by
          exact γ.left_deriv_limit p hp_part hp_interior;
        -- Since the partition is finite, there exists `a ∈ [γ.a, p)` such that `(a, p)` contains no partition points.
        obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ Set.Icc γ.a p, a < p ∧ Disjoint (Set.Ioo a p) (↑γ.toPiecewiseC1Curve.partition : Set ℝ) := by
          -- Since the partition is finite, there exists a maximum element in the partition that is less than p.
          obtain ⟨m, hm⟩ : ∃ m ∈ γ.partition, m < p ∧ ∀ n ∈ γ.partition, n < p → n ≤ m := by
            have h_max : ∃ m ∈ γ.partition, m < p := by
              exact ⟨ γ.a, γ.endpoints_in_partition.1, hp_interior ⟩;
            exact ⟨ Finset.max' ( γ.partition.filter fun n => n < p ) ⟨ h_max.choose, Finset.mem_filter.mpr ⟨ h_max.choose_spec.1, h_max.choose_spec.2 ⟩ ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( γ.partition.filter fun n => n < p ) ⟨ h_max.choose, Finset.mem_filter.mpr ⟨ h_max.choose_spec.1, h_max.choose_spec.2 ⟩ ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( γ.partition.filter fun n => n < p ) ⟨ h_max.choose, Finset.mem_filter.mpr ⟨ h_max.choose_spec.1, h_max.choose_spec.2 ⟩ ⟩ ) |>.2, fun n hn hn' => Finset.le_max' _ _ ( by aesop ) ⟩;
          use m;
          exact ⟨ ⟨ by linarith [ Set.mem_Icc.mp ( γ.toPiecewiseC1Curve.partition_subset hm.1 ) ], by linarith [ Set.mem_Icc.mp ( γ.toPiecewiseC1Curve.partition_subset hm.1 ) ] ⟩, hm.2.1, Set.disjoint_left.mpr fun x hx₁ hx₂ => not_lt_of_ge ( hm.2.2 x hx₂ hx₁.2 ) hx₁.1 ⟩;
        -- Since γ is continuous on [a, p], we can apply `tendsto_diff_quotient_of_tendsto_deriv_left`.
        have h_cont : ContinuousOn γ.toFun (Set.Icc a p) := by
          refine' γ.continuous_toFun.mono _;
          exact Set.Icc_subset_Icc ha₁.1 ( by linarith [ γ.toPiecewiseC1Curve.partition_subset hp_part |>.2 ] )
        have h_diff : DifferentiableOn ℝ γ.toFun (Set.Ioo a p) := by
          refine' fun t ht => DifferentiableAt.differentiableWithinAt _;
          apply γ.smooth_off_partition;
          · exact ⟨ by linarith [ ht.1, ha₁.1 ], by linarith [ ht.2, ha₁.2, γ.toPiecewiseC1Curve.partition_subset hp_part |>.2 ] ⟩;
          · exact fun h => ha₂.2.le_bot ⟨ ht, h ⟩
        have h_lim : Filter.Tendsto (fun t => (γ.toFun p - γ.toFun t) / (p - t)) (𝓝[<] p) (𝓝 L) := by
          convert tendsto_diff_quotient_of_tendsto_deriv_left ha₂.1 h_cont h_diff hL_limit using 1;
        have h_eventually_ne : ∀ᶠ t in 𝓝[<] p, γ.toFun t ≠ z₀ := by
          have h_eventually_ne : ∀ᶠ t in 𝓝[<] p, (γ.toFun p - γ.toFun t) / (p - t) ≠ 0 := by
            exact h_lim.eventually_ne hL_ne_zero;
          filter_upwards [ h_eventually_ne, self_mem_nhdsWithin ] with t ht₁ ht₂ using fun ht₃ => ht₁ <| by simp +decide [ show γ.toFun p = z₀ from Classical.not_not.1 h_case, ht₃ ] ;
        rcases mem_nhdsLT_iff_exists_Ioo_subset.mp h_eventually_ne with ⟨ δ, hδ₁, hδ₂ ⟩;
        exact ⟨ p - δ, sub_pos.mpr hδ₁, fun t ht => hδ₂ ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ⟩

/-
If the derivative of f tends to L as t approaches p from the right, then the difference quotient (f(t) - f(p)) / (t - p) also tends to L.
-/
lemma tendsto_diff_quotient_of_tendsto_deriv_right
    {f : ℝ → ℂ} {p : ℝ} {L : ℂ} {b : ℝ} (hpb : p < b)
    (h_cont : ContinuousOn f (Set.Icc p b))
    (h_diff : DifferentiableOn ℝ f (Set.Ioo p b))
    (h_lim : Filter.Tendsto (deriv f) (𝓝[>] p) (𝓝 L)) :
    Filter.Tendsto (fun t => (f t - f p) / (t - p)) (𝓝[>] p) (𝓝 L) := by
      have h_mean_value : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Ioo p (p + δ), ‖deriv f t - L‖ < ε := by
        rw [ Metric.tendsto_nhdsWithin_nhds ] at h_lim;
        exact fun ε hε => by obtain ⟨ δ, hδ, H ⟩ := h_lim ε hε; exact ⟨ δ, hδ, fun t ht => H ht.1 <| abs_lt.mpr ⟨ by linarith [ ht.1 ], by linarith [ ht.2 ] ⟩ ⟩ ;
      -- Applying the mean value inequality to the interval [p, t], we get ‖f(t) - f(p) - L*(t - p)‖ ≤ ε * (t - p).
      have h_mean_value_ineq : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Ioo p (p + δ), ‖f t - f p - L * (t - p)‖ ≤ ε * (t - p) := by
        intro ε hε_pos
        obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ t ∈ Set.Ioo p (p + δ), ‖deriv f t - L‖ < ε := h_mean_value ε hε_pos
        use min δ (b - p);
        have h_mean_value_ineq : ∀ t ∈ Set.Ioo p (p + min δ (b - p)), ‖f t - f p - L * (t - p)‖ ≤ ε * (t - p) := by
          intro t ht
          have h_diff_quot : ‖f t - f p - L * (t - p)‖ = ‖∫ u in (p)..t, (deriv f u - L)‖ := by
            rw [ intervalIntegral.integral_eq_sub_of_hasDeriv_right ];
            rotate_right;
            use fun x => f x - L * x;
            · ring;
            · exact ContinuousOn.sub ( h_cont.mono ( by rw [ Set.uIcc_of_le ht.1.le ] ; exact Set.Icc_subset_Icc le_rfl ( by linarith [ ht.2, min_le_left δ ( b - p ), min_le_right δ ( b - p ) ] ) ) ) ( Continuous.continuousOn ( by continuity ) );
            · intro x hx; convert HasDerivWithinAt.sub ( h_diff.hasDerivAt ( Ioo_mem_nhds ( show x > p by cases max_cases p t <;> cases min_cases p t <;> linarith [ hx.1, hx.2, ht.1, ht.2 ] ) ( show x < b by cases max_cases p t <;> cases min_cases p t <;> linarith [ hx.1, hx.2, ht.1, ht.2, min_le_left δ ( b - p ), min_le_right δ ( b - p ) ] ) ) |> HasDerivAt.hasDerivWithinAt ) ( HasDerivAt.hasDerivWithinAt ( HasDerivAt.const_mul L ( hasDerivAt_id x |> HasDerivAt.ofReal_comp ) ) ) using 1 ; ring;
              norm_num;
            · rw [ intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1.le ];
              refine' MeasureTheory.Integrable.mono' _ _ _;
              refine' fun u => ε;
              · norm_num;
              · exact MeasureTheory.AEStronglyMeasurable.sub ( measurable_deriv f |> Measurable.aestronglyMeasurable ) ( MeasureTheory.aestronglyMeasurable_const );
              · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioo ] with x hx using le_of_lt ( hδ x ⟨ hx.1, hx.2.trans_le ( by linarith [ ht.2, min_le_left δ ( b - p ), min_le_right δ ( b - p ) ] ) ⟩ )
          rw [ h_diff_quot, intervalIntegral.integral_of_le ht.1.le ];
          refine' le_trans ( MeasureTheory.norm_integral_le_integral_norm _ ) ( le_trans ( MeasureTheory.integral_mono_of_nonneg _ _ _ ) _ );
          refine' fun u => ε;
          · exact Filter.Eventually.of_forall fun x => norm_nonneg _;
          · norm_num;
          · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Ioc ] with u hu using le_of_lt ( hδ u ⟨ hu.1, hu.2.trans_lt ( by linarith [ ht.2, min_le_left δ ( b - p ), min_le_right δ ( b - p ) ] ) ⟩ );
          · norm_num [ mul_comm, ht.1.le ];
        exact ⟨ lt_min hδ_pos ( sub_pos.mpr hpb ), h_mean_value_ineq ⟩;
      -- Dividing both sides of the inequality by (t - p), we get ‖(f(t) - f(p)) / (t - p) - L‖ ≤ ε.
      have h_div_ineq : ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Ioo p (p + δ), ‖(f t - f p) / (t - p) - L‖ ≤ ε := by
        intro ε hε; obtain ⟨ δ, hδ, H ⟩ := h_mean_value_ineq ε hε; use δ, hδ; intro t ht; specialize H t ht; simp_all +decide [ sub_div ] ;
        rw [ ← sub_div ];
        rw [ div_sub' ] <;> norm_num [ sub_ne_zero.mpr ( by norm_cast ; linarith : ( t : ℂ ) ≠ p ) ];
        rw [ div_le_iff₀ ] <;> norm_cast at * <;> simp_all +decide [ mul_comm ];
        · exact H.trans ( mul_le_mul_of_nonneg_left ( le_abs_self _ ) hε.le );
        · linarith;
      rw [ Metric.tendsto_nhdsWithin_nhds ];
      exact fun ε hε => by rcases h_div_ineq ( ε / 2 ) ( half_pos hε ) with ⟨ δ, hδ, H ⟩ ; exact ⟨ δ, hδ, fun x hx₁ hx₂ => lt_of_le_of_lt ( H x ⟨ hx₁, by linarith [ abs_lt.mp hx₂ ] ⟩ ) ( by linarith ) ⟩ ;

/-
Zeros of a piecewise C1 immersion are isolated on smooth segments.
-/
lemma zeros_isolated_on_smooth_segment_lemma
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (c d : ℝ) (hcd : c < d)
    (h_sub : Set.Icc c d ⊆ Set.Icc γ.a γ.b)
    (h_disjoint : Disjoint (Set.Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc c d) (hγt₀ : γ.toFun t₀ = z₀) :
    ∃ ε > 0, ∀ t ∈ Set.Icc c d, t ≠ t₀ → |t - t₀| < ε → γ.toFun t ≠ z₀ := by
      exact zeros_isolated_on_smooth_segment γ z₀ c d hcd h_sub h_disjoint t₀ ht₀ hγt₀

/-
There exists a small interval to the right of a partition point p where γ(t) is never equal to z₀.
-/
lemma no_zeros_right_of_partition
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : p < γ.b) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo p (p + δ), γ.toFun t ≠ z₀ := by
      -- If γ(p) = z₀, then use the fact that the right derivative is nonzero to find a δ.
      by_cases hγp : γ.toFun p = z₀;
      · -- If γ(p) = z₀, then use the fact that the right derivative is nonzero to find an interval (p, b) with no partition points.
        obtain ⟨b, hb⟩ : ∃ b : ℝ, p < b ∧ b ≤ γ.b ∧ ∀ t ∈ Set.Ioo p b, t ∉ γ.toPiecewiseC1Curve.partition := by
          -- Since the partition is finite, there exists a minimum distance δ from p to any other element in the partition.
          obtain ⟨δ, hδ_pos, hδ_min⟩ : ∃ δ > 0, ∀ t ∈ γ.toPiecewiseC1Curve.partition, t ≠ p → |t - p| ≥ δ := by
            have h_finite : Set.Finite (γ.toPiecewiseC1Curve.partition \ {p}) := by
              exact Set.Finite.subset ( Finset.finite_toSet γ.partition ) fun x hx => hx.1;
            by_cases h_empty : (γ.toPiecewiseC1Curve.partition \ {p} : Set ℝ) = ∅;
            · exact ⟨ 1, zero_lt_one, fun t ht ht' => False.elim <| h_empty.subset ⟨ ht, ht' ⟩ ⟩;
            · obtain ⟨δ, hδ_pos, hδ_min⟩ : ∃ δ ∈ Set.image (fun t => |t - p|) (γ.toPiecewiseC1Curve.partition \ {p}), ∀ t ∈ Set.image (fun t => |t - p|) (γ.toPiecewiseC1Curve.partition \ {p}), δ ≤ t := by
                exact ⟨ Finset.min' ( h_finite.toFinset.image fun t => |t - p| ) ⟨ _, Finset.mem_image_of_mem _ ( h_finite.mem_toFinset.mpr <| Classical.choose_spec <| Set.nonempty_iff_ne_empty.mpr h_empty ) ⟩, by simpa using Finset.min'_mem ( h_finite.toFinset.image fun t => |t - p| ) ⟨ _, Finset.mem_image_of_mem _ ( h_finite.mem_toFinset.mpr <| Classical.choose_spec <| Set.nonempty_iff_ne_empty.mpr h_empty ) ⟩, fun t ht => Finset.min'_le _ _ <| by simpa using ht ⟩;
              exact ⟨ δ, by obtain ⟨ t, ht₁, rfl ⟩ := hδ_pos; exact abs_pos.mpr ( sub_ne_zero.mpr ht₁.2 ), fun t ht₁ ht₂ => hδ_min _ <| Set.mem_image_of_mem _ ⟨ ht₁, ht₂ ⟩ ⟩;
          exact ⟨ Min.min ( p + δ ) γ.b, by linarith [ lt_min ( lt_add_of_pos_right p hδ_pos ) hp_interior ], min_le_right _ _, fun t ht ht' => by cases min_cases ( p + δ ) γ.b <;> cases abs_cases ( t - p ) <;> linarith [ ht.1, ht.2, hδ_min t ht' ( by linarith [ ht.1, ht.2 ] ) ] ⟩;
        -- Apply `tendsto_diff_quotient_of_tendsto_deriv_right` to get the difference quotient converging to L.
        have h_diff_quotient : Filter.Tendsto (fun t => (γ.toFun t - γ.toFun p) / (t - p)) (𝓝[>] p) (𝓝 (γ.right_deriv_limit p hp_part (by linarith)).choose) := by
          convert tendsto_diff_quotient_of_tendsto_deriv_right _ _ _ _;
          exact b;
          · linarith;
          · exact γ.toPiecewiseC1Curve.continuous_toFun.mono ( Set.Icc_subset_Icc ( by linarith [ γ.toPiecewiseC1Curve.a, γ.toPiecewiseC1Curve.b, γ.toPiecewiseC1Curve.hab.le, ( Set.mem_Icc.mp <| γ.toPiecewiseC1Curve.partition_subset hp_part ) ] ) ( by linarith [ γ.toPiecewiseC1Curve.a, γ.toPiecewiseC1Curve.b, γ.toPiecewiseC1Curve.hab.le, ( Set.mem_Icc.mp <| γ.toPiecewiseC1Curve.partition_subset hp_part ) ] ) );
          · intro t ht;
            refine' DifferentiableAt.differentiableWithinAt _;
            refine' γ.smooth_off_partition t _ _;
            · constructor <;> linarith [ ht.1, ht.2, γ.toPiecewiseC1Curve.partition_subset hp_part |>.1, γ.toPiecewiseC1Curve.partition_subset hp_part |>.2 ];
            · exact hb.2.2 t ht;
          · exact γ.right_deriv_limit p hp_part ( by linarith ) |> Classical.choose_spec |> And.right;
        have := h_diff_quotient.eventually_ne ( show ( γ.right_deriv_limit p hp_part ( by linarith ) ).choose ≠ 0 from ( γ.right_deriv_limit p hp_part ( by linarith ) ).choose_spec.1 );
        obtain ⟨ δ, hδ ⟩ := Metric.mem_nhdsWithin_iff.mp ( this.and ( Ioo_mem_nhdsGT_of_mem ⟨ le_rfl, hb.1 ⟩ ) );
        exact ⟨ Min.min δ ( b - p ), lt_min hδ.1 ( sub_pos.mpr hb.1 ), fun t ht => by have := hδ.2 ⟨ Metric.mem_ball.mpr <| abs_lt.mpr ⟨ by linarith [ ht.1, ht.2, min_le_left δ ( b - p ), min_le_right δ ( b - p ) ], by linarith [ ht.1, ht.2, min_le_left δ ( b - p ), min_le_right δ ( b - p ) ] ⟩, ht.1 ⟩ ; aesop ⟩;
      · have := Metric.continuousOn_iff.mp ( γ.continuous_toFun ) p ⟨ by linarith [ γ.toPiecewiseC1Curve.hab.le, ( Set.mem_Icc.mp <| γ.toPiecewiseC1Curve.partition_subset hp_part ) ], by linarith [ γ.toPiecewiseC1Curve.hab.le, ( Set.mem_Icc.mp <| γ.toPiecewiseC1Curve.partition_subset hp_part ) ] ⟩;
        obtain ⟨ δ, hδ_pos, H ⟩ := this ( Dist.dist ( γ.toFun p ) z₀ ) ( dist_pos.mpr hγp );
        -- Choose δ' = min(δ, γ.b - p) to ensure that (p, p + δ') is within [γ.a, γ.b].
        use min δ (γ.b - p);
        simp +zetaDelta at *;
        exact ⟨ ⟨ hδ_pos, hp_interior ⟩, fun t ht₁ ht₂ => fun h => absurd ( H t ( by linarith [ γ.toPiecewiseC1Curve.hab.le, ( Set.mem_Icc.mp <| γ.toPiecewiseC1Curve.partition_subset hp_part ) ] ) ( by linarith [ γ.toPiecewiseC1Curve.hab.le, ( Set.mem_Icc.mp <| γ.toPiecewiseC1Curve.partition_subset hp_part ), min_le_right δ ( γ.b - p ) ] ) ( abs_lt.mpr ⟨ by linarith [ min_le_left δ ( γ.b - p ) ], by linarith [ min_le_left δ ( γ.b - p ) ] ⟩ ) ) ( by simp +decide [ *, dist_comm ] ) ⟩

/-
The set of zeros of a piecewise C1 immersion on a smooth segment is finite.
-/
lemma zeros_finite_on_smooth_segment_lemma
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (c d : ℝ) (hcd : c < d)
    (h_sub : Set.Icc c d ⊆ Set.Icc γ.a γ.b)
    (h_disjoint : Disjoint (Set.Icc c d) (↑γ.toPiecewiseC1Curve.partition : Set ℝ)) :
    Set.Finite {t ∈ Set.Icc c d | γ.toFun t = z₀} := by
      exact zeros_finite_on_smooth_segment γ z₀ c d hcd h_sub h_disjoint

/-
The set of zeros in an open interval between two partition points is finite.
-/
lemma zeros_finite_on_interval_between_partition_points
    (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (u v : ℝ) (huv : u < v)
    (h_sub : Set.Icc u v ⊆ Set.Icc γ.a γ.b)
    (h_u : u ∈ γ.toPiecewiseC1Curve.partition)
    (h_v : v ∈ γ.toPiecewiseC1Curve.partition)
    (h_no_part : ∀ t ∈ Set.Ioo u v, t ∉ γ.toPiecewiseC1Curve.partition) :
    Set.Finite {t ∈ Set.Ioo u v | γ.toFun t = z₀} := by
      have := no_zeros_right_of_partition γ z₀ u h_u ( by
        linarith [ Set.mem_Icc.mp ( h_sub <| Set.right_mem_Icc.mpr huv.le ) ] );
      have := no_zeros_left_of_partition γ z₀ v h_v ( by
        linarith [ Set.mem_Icc.mp ( h_sub ( Set.left_mem_Icc.mpr huv.le ) ), Set.mem_Icc.mp ( h_sub ( Set.right_mem_Icc.mpr huv.le ) ) ] );
      obtain ⟨ δ₁, hδ₁_pos, hδ₁ ⟩ := ‹∃ δ > 0, ∀ t ∈ Set.Ioo u ( u + δ ), γ.toFun t ≠ z₀›
      obtain ⟨ δ₂, hδ₂_pos, hδ₂ ⟩ := ‹∃ δ > 0, ∀ t ∈ Set.Ioo ( v - δ ) v, γ.toFun t ≠ z₀›
      have hK : Set.Finite {t ∈ Set.Icc (u + δ₁) (v - δ₂) | γ.toFun t = z₀} := by
        by_cases hK_empty : u + δ₁ ≥ v - δ₂;
        · exact Set.Finite.subset ( Set.finite_singleton ( u + δ₁ ) ) fun x hx => le_antisymm ( by linarith [ hx.1.2 ] ) ( by linarith [ hx.1.1 ] );
        · have := zeros_finite_on_smooth_segment_lemma γ z₀ ( u + δ₁ ) ( v - δ₂ ) ( by linarith ) ( by exact Set.Icc_subset_Icc ( by linarith ) ( by linarith ) |> Set.Subset.trans <| h_sub ) ( by exact Set.disjoint_left.mpr fun x hx₁ hx₂ => h_no_part x ⟨ by linarith [ hx₁.1 ], by linarith [ hx₁.2 ] ⟩ hx₂ ) ; aesop;
      refine Set.Finite.subset ( hK.union ( Set.finite_singleton u ) |> Set.Finite.union <| Set.finite_singleton v ) ?_;
      intro t ht; by_cases hu : t = u <;> by_cases hv : t = v <;> simp_all +decide [ Set.subset_def ] ;
      exact ⟨ le_of_not_gt fun h => hδ₁ t ht.1.1 h ht.2, le_of_not_gt fun h => hδ₂ t ( by linarith ) ( by linarith ) ht.2 ⟩

end AristotleLemmas

--set_option maxHeartbeats 0
theorem zeros_finite_left_of_partition
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : γ.a < p) :
    Set.Finite {t ∈ Icc γ.a p | t ∉ γ.toPiecewiseC1Curve.partition ∧ γ.toFun t = z₀} := by
  -- Let P' be the set of partition points in [γ.a, p]. Since the partition is finite, P' is finite.
  set P' : Finset ℝ := (γ.toPiecewiseC1Curve.partition).filter (fun t => γ.a ≤ t ∧ t ≤ p) with hP';
  -- Since γ.a and p are in the partition (by assumption and definition), γ.a ∈ P' and p ∈ P'.
  have hP'_mem : γ.a ∈ P' ∧ p ∈ P' := by
    exact ⟨ Finset.mem_filter.mpr ⟨ γ.toPiecewiseC1Curve.endpoints_in_partition.1, by linarith, by linarith ⟩, Finset.mem_filter.mpr ⟨ hp_part, by linarith, by linarith ⟩ ⟩;
  -- The interval [γ.a, p] is the union of {t₀, ..., tₖ} and the open intervals (tᵢ, tᵢ₊₁).
  have h_union : {t ∈ Set.Icc γ.a p | t∉γ.toPiecewiseC1Curve.partition ∧ γ.toFun t = z₀} ⊆ ⋃ (t : ℝ) (ht : t ∈ P'), {t} ∪ ⋃ (s : ℝ) (hs : s ∈ P' ∧ t < s ∧ ∀ u ∈ P', t < u → u ≥ s), {u ∈ Set.Ioo t s | γ.toFun u = z₀} := by
    intros t ht
    obtain ⟨ht_mem, ht_not_part, ht_eq⟩ := ht;
    -- Since $t \notin P'$, there exists $s \in P'$ such that $t \in (s, s')$ for some $s' \in P'$.
    obtain ⟨s, hs⟩ : ∃ s ∈ P', s ≤ t ∧ ∀ u ∈ P', u < t → u ≤ s := by
      have h_exists_s : ∃ s ∈ P', s ≤ t := by
        exact ⟨ γ.a, hP'_mem.1, ht_mem.1 ⟩;
      exact ⟨ Finset.max' ( P'.filter fun u => u ≤ t ) ⟨ _, Finset.mem_filter.mpr ⟨ h_exists_s.choose_spec.1, h_exists_s.choose_spec.2 ⟩ ⟩, Finset.mem_filter.mp ( Finset.max'_mem ( P'.filter fun u => u ≤ t ) ⟨ _, Finset.mem_filter.mpr ⟨ h_exists_s.choose_spec.1, h_exists_s.choose_spec.2 ⟩ ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.max'_mem ( P'.filter fun u => u ≤ t ) ⟨ _, Finset.mem_filter.mpr ⟨ h_exists_s.choose_spec.1, h_exists_s.choose_spec.2 ⟩ ⟩ ) |>.2, fun u hu hu' => Finset.le_max' _ _ ( Finset.mem_filter.mpr ⟨ hu, hu'.le ⟩ ) ⟩;
    by_cases hst : s = t;
    · aesop;
    · -- Since $s \neq t$, there exists $s' \in P'$ such that $t \in (s, s')$.
      obtain ⟨s', hs'⟩ : ∃ s' ∈ P', s < s' ∧ ∀ u ∈ P', s < u → u ≥ s' := by
        have h_exists_s' : ∃ s' ∈ P', s < s' := by
          refine ⟨p, hP'_mem.2, ?_⟩
          have hst' : s < t := lt_of_le_of_ne hs.2.1 hst
          linarith [ht_mem.2]

        exact ⟨ Finset.min' ( P'.filter fun u => s < u ) ⟨ _, Finset.mem_filter.mpr ⟨ h_exists_s'.choose_spec.1, h_exists_s'.choose_spec.2 ⟩ ⟩, Finset.mem_filter.mp ( Finset.min'_mem ( P'.filter fun u => s < u ) ⟨ _, Finset.mem_filter.mpr ⟨ h_exists_s'.choose_spec.1, h_exists_s'.choose_spec.2 ⟩ ⟩ ) |>.1, Finset.mem_filter.mp ( Finset.min'_mem ( P'.filter fun u => s < u ) ⟨ _, Finset.mem_filter.mpr ⟨ h_exists_s'.choose_spec.1, h_exists_s'.choose_spec.2 ⟩ ⟩ ) |>.2, fun u hu hu' => Finset.min'_le _ _ ( by aesop ) ⟩;
      simp_all  [ Set.subset_def ];
      exact ⟨ s, hs.1, Or.inr ⟨ lt_of_le_of_ne hs.2.1 hst, s', ⟨ hs'.1, hs'.2.1, hs'.2.2 ⟩, lt_of_not_ge fun h => hst <| by linarith [ hs.2.2 _ hs'.1.1 hs'.1.2.1 hs'.1.2.2 <| lt_of_le_of_ne ( by linarith ) <| Ne.symm <| by aesop ] ⟩ ⟩;
  -- For each i, (tᵢ, tᵢ₊₁) contains no partition points (since tᵢ, tᵢ₊₁ are adjacent in P').
  have h_interval_finite : ∀ t ∈ P', ∀ s ∈ P', t < s → (∀ u ∈ P', t < u → u ≥ s) → {u ∈ Set.Ioo t s | γ.toFun u = z₀}.Finite := by
    intros t ht s hs hts h_adjacent
    apply zeros_finite_on_interval_between_partition_points γ z₀ t s hts;
    · exact Set.Icc_subset_Icc ( by simp_all only [Finset.mem_filter, le_refl, true_and, and_true, and_self_right,
      mem_Icc, ge_iff_le, and_imp, mem_Ioo, singleton_union, and_self, P'] ) ( by linarith [ Set.mem_Icc.mp ( γ.toPiecewiseC1Curve.partition_subset ( by simp_all only [Finset.mem_filter,
        le_refl, true_and, and_true, and_self_right, mem_Icc, ge_iff_le, and_imp, mem_Ioo, singleton_union, and_self,
        P'] : s ∈ γ.toPiecewiseC1Curve.partition ) ) ] );
    · simp_all only [Finset.mem_filter, le_refl, true_and, and_true, and_self_right, mem_Icc, ge_iff_le, and_imp,
      mem_Ioo, singleton_union, and_self, P'];
    · simp_all only [Finset.mem_filter, le_refl, true_and, and_true, and_self_right, mem_Icc, ge_iff_le, and_imp,
      mem_Ioo, singleton_union, and_self, P'];
    · grind only [= mem_Ioo, = subset_def, = setOf_true, = Finset.mem_filter, = setOf_false];
  refine Set.Finite.subset ?_ h_union;
  refine Set.Finite.biUnion ( Finset.finite_toSet P' ) fun t ht => Set.Finite.union ?_ ?_;
  · norm_num;
  · refine Set.Finite.biUnion ?_ fun s hs => h_interval_finite t ht s hs.1 hs.2.1 hs.2.2;
    exact Set.Finite.subset ( Finset.finite_toSet P' ) fun x hx => hx.1

/-- Finitely many zeros to the right of a partition point. -/
theorem zeros_finite_right_of_partition
    (p : ℝ) (hp_part : p ∈ γ.toPiecewiseC1Curve.partition)
    (hp_interior : p < γ.b) :
    Set.Finite {t ∈ Icc p γ.b | t ∉ γ.toPiecewiseC1Curve.partition ∧ γ.toFun t = z₀} := by
  have := @zeros_finite_left_of_partition;
  contrapose! this;
  refine' ⟨ _, _, _, _, _, _ ⟩;
  exact γ;
  exact z₀;
  exact γ.b;
  · exact γ.toPiecewiseC1Curve.endpoints_in_partition.2;
  · exact γ.toPiecewiseC1Curve.hab;
  · exact Set.Infinite.mono ( fun x hx => ⟨ ⟨ by linarith [ hx.1.1, γ.toPiecewiseC1Curve.partition_subset hp_part |>.1 ], by linarith [ hx.1.2, γ.toPiecewiseC1Curve.partition_subset hp_part |>.2 ] ⟩, hx.2.1, hx.2.2 ⟩ ) this

/-! ## Main Finiteness Theorem -/

/-- A piecewise C¹ immersion has only finitely many zeros.

    **Proof Strategy:**
    1. The partition is finite
    2. Between consecutive partition points, zeros are finite (smooth segment case)
    3. At partition points themselves, there are finitely many (the partition is finite)
    4. Near partition points, zeros are finite (by one-sided derivative limits)
-/
theorem piecewiseC1Immersion_finite_zeros :
    Set.Finite {t ∈ Icc γ.a γ.b | γ.toFun t = z₀} := by
  -- Split into partition points and non-partition points
  have h_subset : {t ∈ Icc γ.a γ.b | γ.toFun t = z₀} ⊆
      ({t ∈ Icc γ.a γ.b | γ.toFun t = z₀} ∩ ↑γ.toPiecewiseC1Curve.partition) ∪
      ({t ∈ Icc γ.a γ.b | γ.toFun t = z₀} \ ↑γ.toPiecewiseC1Curve.partition) := by
    intro t ht
    by_cases h : t ∈ ↑γ.toPiecewiseC1Curve.partition
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr ⟨ht, h⟩
  -- Partition intersection is finite (partition is finite)
  have h_partition_finite : Set.Finite
      ({t ∈ Icc γ.a γ.b | γ.toFun t = z₀} ∩ ↑γ.toPiecewiseC1Curve.partition) :=
    Set.Finite.subset γ.toPiecewiseC1Curve.partition.finite_toSet Set.inter_subset_right
  -- Non-partition zeros: decompose by partition intervals and apply smooth segment result
  have h_nonpartition_finite : Set.Finite
      ({t ∈ Icc γ.a γ.b | γ.toFun t = z₀} \ ↑γ.toPiecewiseC1Curve.partition) := by
    -- The set of zeros in the complement of the partition is a finite union of finite sets, hence finite.
    have h_complement_finite : ∀ (p : ℝ), p ∈ γ.toPiecewiseC1Curve.partition → Set.Finite {t ∈ {t ∈ Set.Icc γ.a γ.b | γ.toFun t = z₀} | t ∉ γ.toPiecewiseC1Curve.partition ∧ t < p} ∧ Set.Finite {t ∈ {t ∈ Set.Icc γ.a γ.b | γ.toFun t = z₀} | t ∉ γ.toPiecewiseC1Curve.partition ∧ t > p} := by
      intro p hp
      constructor;
      · by_cases hp_left : p > γ.a;
        · have := zeros_finite_left_of_partition γ z₀ p hp hp_left;
          exact this.subset fun x hx => ⟨ ⟨ hx.1.1.1, hx.2.2.le ⟩, hx.2.1, hx.1.2 ⟩;
        · exact Set.Finite.subset ( Set.finite_singleton γ.a ) fun x hx => by linarith [ hx.1.1.1, hx.1.1.2, hx.2.2 ] ;
      · by_cases hp_lt_b : p < γ.b;
        · have := zeros_finite_right_of_partition γ z₀ p hp hp_lt_b;
          exact this.subset fun x hx => ⟨ ⟨ by linarith [ hx.1.1.1, hx.2.2 ], by linarith [ hx.1.1.2, hx.2.2 ] ⟩, hx.2.1, hx.1.2 ⟩;
        · exact Set.Finite.subset ( Set.finite_singleton γ.b ) fun x hx => by linarith [ hx.1.1.2, hx.2.2, show p = γ.b from le_antisymm ( by linarith [ γ.toPiecewiseC1Curve.partition_subset hp |>.2 ] ) ( not_lt.mp hp_lt_b ) ] ;
    have h_complement_finite : Set.Finite (⋃ p ∈ γ.toPiecewiseC1Curve.partition, {t ∈ {t ∈ Set.Icc γ.a γ.b | γ.toFun t = z₀} | t ∉ γ.toPiecewiseC1Curve.partition ∧ t < p} ∪ {t ∈ {t ∈ Set.Icc γ.a γ.b | γ.toFun t = z₀} | t ∉ γ.toPiecewiseC1Curve.partition ∧ t > p}) := by
      exact Set.Finite.biUnion ( Finset.finite_toSet _ ) fun p hp => Set.Finite.union ( h_complement_finite p hp |>.1 ) ( h_complement_finite p hp |>.2 );
    refine h_complement_finite.subset ?_;
    simp +contextual [ Set.subset_def ];
    exact fun x hx₁ hx₂ hx₃ hx₄ => ⟨ γ.a, by have := γ.toPiecewiseC1Curve.endpoints_in_partition; aesop ⟩
  exact (h_partition_finite.union h_nonpartition_finite).subset h_subset

/-! ## Corollary: Zeros Form a Finset -/

/-- The set of zeros can be converted to a Finset. -/
def zerosFinset : Finset ℝ :=
  (piecewiseC1Immersion_finite_zeros γ z₀).toFinset

theorem zerosFinset_spec :
    ∀ t, t ∈ zerosFinset γ z₀ ↔ t ∈ Icc γ.a γ.b ∧ γ.toFun t = z₀ := by
  intro t
  simp only [zerosFinset, Set.Finite.mem_toFinset, Set.mem_sep_iff]

end
