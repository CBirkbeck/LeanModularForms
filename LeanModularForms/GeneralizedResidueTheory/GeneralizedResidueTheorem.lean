/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.GeneralizedResidueTheory.Residue.FlatnessTransfer

/-!
# Generalized Residue Theorem -- Public API

Clean top-level names for the generalized residue theorem and its corollaries.
All proofs delegate to the machinery in `HomologicalCauchy.lean` and
`Residue/FlatnessTransfer.lean`; this file contains no new proof work.

## Main results

* `generalizedResidueTheorem` -- the most general version: null-homologous
  curve, higher-order poles, conditions (A')+(B).
* `generalizedResidueTheorem_convex` -- corollary for convex domains (closedness
  replaces null-homologous hypothesis).
* `generalizedResidueTheorem_simplePoles` -- corollary for simple poles in
  null-homologous setting (conditions A+B drop out; uses `HasSimplePoleAt`).

## References

* Hungerbuhler-Wasem, *The generalized residue theorem*, arXiv:1808.00997v2,
  Theorem 3.3.
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

/-! ### Master theorem (null-homologous, higher-order poles, conditions A'+B) -/

set_option maxHeartbeats 800000 in
/-- **Generalized Residue Theorem** (Hungerbuhler-Wasem, Theorem 3.3).

For a meromorphic function `f` with finitely many poles `S0` on a
null-homologous piecewise C^1 immersion `gamma` in an open set `U`,
the Cauchy principal value integral converges to
`2 pi i * sum_{s in S0} n(gamma, s) * Res(f, s)`,
provided conditions (A') (flatness) and (B) (angle/Laurent compatibility)
hold at every crossing point.

This is the most general form. See `generalizedResidueTheorem_convex` for
the convex-domain specialization and `generalizedResidueTheorem_simplePoles`
for the simple-pole case where conditions A'+B are not needed. -/
theorem generalizedResidueTheorem (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
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
  open GeneralizedResidueTheory in
  -- ════════════════════════════════════════════════════════════════════════
  -- Step 1: Higher-order cancellation — CPV(f) - CPV(f_res) → 0
  --
  -- Define h = f - Σ Res(f,s)/(z-s). Apply the abstract assembly framework
  -- (higherOrderCancel_assembly_abstract) with two Dixon callbacks:
  --   (1) holomorphic contour integrals vanish (contourIntegral_eq_zero_of_nullHomologous)
  --   (2) meromorphic contour integrals with zero residues vanish
  --       (contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh)
  -- Then lift from CPV(h) → 0 to CPV(f) - CPV(f_res) → 0 via cpvIntegrandOn_sub.
  -- ════════════════════════════════════════════════════════════════════════
  have hS0_in_U : ∀ s ∈ S0, s ∈ U := fun s hs => hS_in_U s (hS0_subset s hs)
  set h : ℂ → ℂ := fun z => f z - ∑ s ∈ S0, residueAt f s / (z - s) with hh_def
  -- Assembly: CPV of h tends to 0
  have hCancel_h : Tendsto
      (fun ε => ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 h γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) :=
    higherOrderCancel_assembly_abstract U hU S0 f hf γ
      h_null.closed h_null.image_subset hMero hCondA hCondB hγ_meas h_no_endpt_cross
      h_unique_cross hS0_in_U
      (fun _ hg => contourIntegral_eq_zero_of_nullHomologous hU hg γ h_null)
      (fun T g hg_mero hg_res hg_diff _hT_in_U hg_avoids =>
        contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh T g
          hg_mero hg_res U hU hg_diff γ h_null hg_avoids)
  -- Lift: CPV(f) - CPV(f_res) → 0
  have hCancel : Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0) := by
    apply hCancel_h.congr'
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
    exact cpvIntegrandOn_sub S0 f (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t
  -- ════════════════════════════════════════════════════════════════════════
  -- Step 2: PV residue convergence — CPV(f_res) → 2πi · Σ n · Res
  --
  -- f_res = Σ Res(f,s)/(z-s) has simple poles, is holomorphic on ℂ \ S0,
  -- and its residueSimplePole at each s equals residueAt f s.
  -- Apply generalizedResidueTheorem' on (univ, convex_univ) to get the CPV formula,
  -- after establishing that CPV of each singular term exists.
  -- ════════════════════════════════════════════════════════════════════════
  set f_res := fun z => ∑ s ∈ S0, residueAt f s / (z - s) with hf_res_def
  have hSimple_res : ∀ s ∈ S0, HasSimplePoleAt f_res s :=
    fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueAt f) s hs
  have hf_res_diff_univ : DifferentiableOn ℂ f_res (Set.univ \ ↑S0) :=
    differentiableOn_sum_div_sub S0 (residueAt f) Set.univ
  have hf_ext_res : ∀ s ∈ S0, ContinuousAt
      (fun z => f_res z - residueSimplePole f_res s / (z - s)) s :=
    fun s hs => continuousAt_sum_remainder S0 (residueAt f) s hs
  have h_res_eq : ∀ s ∈ S0,
      residueSimplePole f_res s = residueAt f s :=
    fun s hs => residueSimplePole_sum_div_sub S0 (residueAt f) s hs
  -- CPV of each singular term Res(f,s)/(z-s) exists
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
    have honly : ∀ t ∈ Set.Icc γ.a γ.b, γ.toFun t = s → t = t₀ :=
      fun t ht hgt => h_unique_cross s hs t ht t₀ ht₀ hgt hcross
    suffices ∃ M, Tendsto (fun ε => ∫ (t : ℝ) in γ.a..γ.b,
        if ε < ‖γ.toFun t - s‖ then (γ.toFun t - s)⁻¹ * deriv γ.toFun t else 0)
        (𝓝[>] 0) (𝓝 M) from this.choose_spec.cauchy_map
    exact cpv_exists_inv_sub_of_closed_unique γ s h_null.closed
      (h_no_endpt_cross s hs) t₀ ht₀_Ioo hcross honly
  -- Apply the simple-pole residue theorem on (univ, convex_univ) to f_res
  have h_thm := generalizedResidueTheorem' Set.univ isOpen_univ convex_univ
    S (fun s _ => Set.mem_univ s) hS_discrete hS_closed S0 hS0_subset
    f_res hf_res_diff_univ γ h_null.closed (fun t _ => Set.mem_univ _)
    (fun t ht h_mem => hS_on_curve t ht h_mem)
    hSimple_res hf_ext_res hPV_singular
  obtain ⟨h_exists, h_value⟩ := h_thm
  obtain ⟨L, hL⟩ := h_exists
  -- Rewrite residueSimplePole(f_res) to residueAt(f)
  have h_limit_eq : L = 2 * Real.pi * I * ∑ s ∈ S0,
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
    have hL_eq : L = cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b :=
      (hL.limUnder_eq).symm
    rw [hL_eq, h_value]
    congr 1; apply Finset.sum_congr rfl
    intro s hs; rw [h_res_eq s hs]
  rw [← h_limit_eq]
  have hPV_res_tendsto : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0
        (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 L) := hL
  -- ════════════════════════════════════════════════════════════════════════
  -- Step 3: Combine — CPV(f) → L
  --
  -- Write CPV(f)(ε) = (CPV(f)(ε) - CPV(f_res)(ε)) + CPV(f_res)(ε).
  -- The first summand → 0 (Step 1), the second → L (Step 2).
  -- ════════════════════════════════════════════════════════════════════════
  have h_eq : (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) =
    (fun ε =>
      ((∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
       (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
         (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)) +
      (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
         (fun z => ∑ s ∈ S0, residueAt f s / (z - s)) γ.toFun ε t)) := by
    ext ε; ring
  rw [h_eq, show L = 0 + L from (zero_add _).symm]
  exact hCancel.add hPV_res_tendsto

/-! ### Convex-domain corollary -/

/-- **Generalized Residue Theorem** (convex domain).

Specialization of `generalizedResidueTheorem` to convex open sets, where
null-homologousness is automatic for any closed curve contained in `U`.
Requires the curve to be closed and contained in `U`. -/
theorem generalizedResidueTheorem_convex (U : Set ℂ) (hU : IsOpen U)
    (hU_convex : Convex ℝ U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion)
    (hγ_closed : γ.toPiecewiseC1Curve.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
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
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s)) :=
  generalizedResidueTheorem U hU S hS_in_U hS_discrete hS_closed S0 hS0_subset
    f hf γ
    (isNullHomologous_of_convex U hU hU_convex
      ⟨γ.toFun γ.a, hγ_in_U γ.a (left_mem_Icc.mpr γ.hab.le)⟩ γ hγ_closed hγ_in_U)
    hS_on_curve hMero hCondA hCondB hγ_meas h_no_endpt_cross h_unique_cross

/-! ### Simple-pole corollary -/

/-- **Generalized Residue Theorem for simple poles** (null-homologous).

When every singularity in `S0` is a simple pole, conditions (A') and (B) are
not needed: condition (A') is automatic because every piecewise C^1 immersion
is flat of order 1 (`isFlatOfOrder_one`), and the Laurent compatibility in
condition (B) is vacuously satisfied (no higher-order terms). The conclusion
is an equality (CPV exists), not just `Tendsto`, and uses `residueAt` in place
of `residueSimplePole`.

**Hypotheses compared to `generalizedResidueTheorem`:**
- Replaces `hCondA`, `hCondB` with `hSimplePoles` (simple pole at each `s`)
  and `hf_ext` (continuity of the regular part `f(z) - Res/(z-s)`).
- Requires `DifferentiableOn` of `f` on `U \ S0`. -/
theorem generalizedResidueTheorem_simplePoles (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) (S0 : Finset ℂ) (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hf_ext : ∀ s ∈ S0,
      ContinuousAt (fun z => f z - residueSimplePole f s / (z - s)) s)
    (hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s :=
  generalizedResidueTheorem_higher_order_simple_nullHomologous U hU S hS_in_U
    hS_discrete hS_closed S0 hS0_subset f hf γ h_null hS_on_curve
    hSimplePoles hf_ext hγ_meas h_no_endpt_cross h_unique_cross
