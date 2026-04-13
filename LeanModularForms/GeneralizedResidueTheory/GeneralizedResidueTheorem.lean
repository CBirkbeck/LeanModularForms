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
* `generalizedResidueTheorem_simplePoles` -- corollary for simple poles in
  null-homologous setting (conditions A+B drop out; uses `HasSimplePoleAt`).

## References

* Hungerbuhler-Wasem, *The generalized residue theorem*, arXiv:1808.00997v2,
  Theorem 3.3.
-/

open Complex MeasureTheory Set Filter Topology Finset Real
open scoped Interval

open GeneralizedResidueTheory

/-! ### Shared helpers for both theorems -/

/-- CPV of each singular term `c(s)/(z - s)` exists when the curve has unique crossings
and avoids endpoints. -/
private theorem cpv_singular_terms_exist {U : Set ℂ}
    (S : Set ℂ) (_hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (_hS_closed : IsClosed S) (S0 : Finset ℂ) (_hS0_subset : ∀ s ∈ S0, s ∈ S)
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (_hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂)
    (c : ℂ → ℂ)
    (f_sing : ℂ → ℂ := fun z => ∑ s ∈ S0, c s / (z - s)) :
    ∀ s ∈ S0, CauchyPrincipalValueExists'
      (fun z => residueSimplePole f_sing s / (z - s)) γ.toFun γ.a γ.b s := by
  intro s hs
  have h_eq : (fun z => residueSimplePole f_sing s / (z - s)) =
      (fun z => residueSimplePole f_sing s * (fun z => (z - s)⁻¹) z) := by
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

/-- Lift CPV(h) → 0 to CPV(f) - CPV(f_res) → 0 via the CPV integrand subtraction lemma. -/
private theorem cpv_cancel_lift (U : Set ℂ)
    (S0 : Finset ℂ) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (c : ℂ → ℂ)
    (hCancel_h : Tendsto
      (fun ε => ∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
        (fun z => f z - ∑ s ∈ S0, c s / (z - s)) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0
          (fun z => ∑ s ∈ S0, c s / (z - s)) γ.toFun ε t))
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
        (fun z => ∑ s ∈ S0, c s / (z - s)) γ.toFun ε)
      volume γ.a γ.b := by
    have hfres_cont : ContinuousOn (fun z => ∑ s ∈ S0, c s / (z - s))
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
  exact cpvIntegrandOn_sub S0 f (fun z => ∑ s ∈ S0, c s / (z - s)) γ.toFun ε t

/-- Combine CPV(f) - CPV(f_res) → 0 with CPV(f_res) → L to get CPV(f) → L. -/
private theorem cpv_combine (S0 : Finset ℂ) (f f_res : ℂ → ℂ)
    (γ : PiecewiseC1Immersion) (L : ℂ)
    (hCancel : Tendsto
      (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_res γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0))
    (hL : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 f_res γ.toFun ε t)
      (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t)
      (𝓝[>] 0) (𝓝 L) := by
  have h_eq : (fun ε => ∫ t in γ.a..γ.b,
      cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) =
    (fun ε =>
      ((∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
       (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_res γ.toFun ε t)) +
      (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_res γ.toFun ε t)) := by
    ext ε; ring
  rw [h_eq, show L = 0 + L from (zero_add _).symm]
  exact hCancel.add hL

/-! ### Master theorem (null-homologous, higher-order poles, conditions A'+B) -/

/-- **Generalized Residue Theorem** (Hungerbuhler-Wasem, Theorem 3.3).

For a meromorphic function `f` with finitely many poles `S0` on a
null-homologous piecewise C^1 immersion `gamma` in an open set `U`,
the Cauchy principal value integral converges to
`2 pi i * sum_{s in S0} n(gamma, s) * Res(f, s)`,
provided conditions (A') (flatness) and (B) (angle/Laurent compatibility)
hold at every crossing point.

This is the most general form. See `generalizedResidueTheorem_simplePoles`
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
  -- Step 1: Higher-order cancellation — CPV(f) - CPV(f_res) → 0
  have hCancel := cpv_cancel_lift U S0 f hf γ h_null (residueAt f)
    (higherOrderCancel_assembly_abstract U hU S0 f hf γ
      h_null.closed h_null.image_subset hMero hCondA hCondB hγ_meas h_no_endpt_cross
      h_unique_cross (fun s hs => hS_in_U s (hS0_subset s hs))
      (fun _ hg => contourIntegral_eq_zero_of_nullHomologous hU hg γ h_null)
      (fun T g hg_mero hg_res hg_diff _hT_in_U hg_avoids =>
        contourIntegral_eq_zero_of_meromorphic_residue_zero_finset_nh T g
          hg_mero hg_res U hU hg_diff γ h_null hg_avoids))
  -- Step 2: PV residue convergence — CPV(f_res) → 2πi · Σ n · Res
  set f_res := fun z => ∑ s ∈ S0, residueAt f s / (z - s) with hf_res_def
  have hPV_singular := cpv_singular_terms_exist S hS_discrete hS_closed S0 hS0_subset
    γ h_null hS_on_curve h_no_endpt_cross h_unique_cross (residueAt f)
  have h_thm := generalizedResidueTheorem' Set.univ isOpen_univ convex_univ
    S (fun s _ => Set.mem_univ s) hS_discrete hS_closed S0 hS0_subset
    f_res (differentiableOn_sum_div_sub S0 (residueAt f) Set.univ) γ h_null.closed
    (fun t _ => Set.mem_univ _) (fun t ht h_mem => hS_on_curve t ht h_mem)
    (fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueAt f) s hs)
    (fun s hs => continuousAt_sum_remainder S0 (residueAt f) s hs) hPV_singular
  obtain ⟨⟨L, hL⟩, h_value⟩ := h_thm
  have h_res_eq : ∀ s ∈ S0, residueSimplePole f_res s = residueAt f s :=
    fun s hs => residueSimplePole_sum_div_sub S0 (residueAt f) s hs
  have h_limit_eq : L = 2 * Real.pi * I * ∑ s ∈ S0,
      generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
    have hL_eq : L = cauchyPrincipalValueOn S0 f_res γ.toFun γ.a γ.b :=
      (hL.limUnder_eq).symm
    rw [hL_eq, h_value]; congr 1; apply Finset.sum_congr rfl
    intro s hs; rw [h_res_eq s hs]
  rw [← h_limit_eq]
  -- Step 3: Combine — CPV(f) → L
  exact cpv_combine S0 f f_res γ L hCancel hL

/-- Lift CPV(g) → 0 to CPV(f) - CPV(f_sing) → 0 for the simple-poles case,
where `g = f - f_sing` and `f_sing` is holomorphic on `univ \ S0`. -/
private theorem cpv_cancel_simple_poles (U : Set ℂ) (S0 : Finset ℂ)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S0))
    (f_sing : ℂ → ℂ) (hf_sing_diff : DifferentiableOn ℂ f_sing (Set.univ \ ↑S0))
    (γ : PiecewiseC1Immersion) (h_null : IsNullHomologous γ U)
    (hg_cpv_zero : Tendsto
      (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (fun z => f z - f_sing z) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε =>
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f γ.toFun ε t) -
        (∫ t in γ.a..γ.b, cauchyPrincipalValueIntegrandOn S0 f_sing γ.toFun ε t))
      (𝓝[>] 0) (𝓝 0) := by
  apply hg_cpv_zero.congr'
  filter_upwards [self_mem_nhdsWithin] with ε (hε : (0 : ℝ) < ε)
  symm
  rw [← intervalIntegral.integral_sub
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
      U S0 f hf.continuousOn γ h_null.image_subset ε hε)
    (intervalIntegrable_cpvIntegrandOn_of_continuousOn_diff
      Set.univ S0 f_sing hf_sing_diff.continuousOn γ
      (fun t _ => Set.mem_univ _) ε hε)]
  congr 1; ext t; exact cpvIntegrandOn_sub S0 f f_sing γ.toFun ε t

/-! ### Simple-pole corollary -/

/-- **Generalized Residue Theorem for simple poles** (null-homologous).

When every singularity in `S0` is a simple pole, conditions (A') and (B) are
not needed: condition (A') is automatic because every piecewise C^1 immersion
is flat of order 1 (`isFlatOfOrder_one`), and the Laurent compatibility in
condition (B) is vacuously satisfied (no higher-order terms). The conclusion
is an equality (CPV exists), not just `Tendsto`, and uses `residueAt` in place
of `residueSimplePole`.

**Self-contained proof.** Decomposes `f = g + Σ res/(z-s)` where `g` is
holomorphic on `U`. Dixon gives `∮ g dz = 0`, so `CPV(g) → 0`. The convex
theorem on `(univ, convex_univ)` gives `CPV(f_sing) = 2πi · Σ n · Res`.
Adding the two yields `CPV(f) = CPV(f_sing)`.

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
    (_hγ_meas : Measurable γ.toFun)
    (h_no_endpt_cross : ∀ s ∈ S0, γ.toFun γ.a ≠ s ∧ γ.toFun γ.b ≠ s)
    (h_unique_cross : ∀ s ∈ S0, ∀ t₁ ∈ Icc γ.a γ.b, ∀ t₂ ∈ Icc γ.a γ.b,
      γ.toFun t₁ = s → γ.toFun t₂ = s → t₁ = t₂) :
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0,
        generalizedWindingNumber' γ.toFun γ.a γ.b s * residueAt f s := by
  have hS0_in_U : ∀ s ∈ S0, s ∈ U := fun s hs => hS_in_U s (hS0_subset s hs)
  -- Step 1: Decompose f = g + f_sing where g is holomorphic on U
  set f_sing := fun z => ∑ s ∈ S0, residueSimplePole f s / (z - s) with hf_sing_def
  have hg_diff : DifferentiableOn ℂ (fun z => f z - f_sing z) U :=
    (simple_poles_decomposition U hU S0 hS0_in_U f hf hSimplePoles hf_ext).1
  -- Step 2: Dixon gives ∮_γ g dz = 0, hence CPV(g, ε) → 0
  have hg_cpv_zero : Tendsto
      (fun ε => ∫ t in γ.a..γ.b,
        cauchyPrincipalValueIntegrandOn S0 (fun z => f z - f_sing z) γ.toFun ε t)
      (𝓝[>] 0) (𝓝 0) :=
    tendsto_cpv_of_continuousOn_zero_integral S0 _ γ
      (hg_diff.continuousOn.mono (fun z ⟨t, ht, htz⟩ => htz ▸ h_null.image_subset t ht))
      (contourIntegral_eq_zero_of_nullHomologous hU hg_diff γ h_null)
  -- Step 3: CPV(f_sing) via simple-pole theorem on (univ, convex_univ)
  have hf_sing_diff := differentiableOn_sum_div_sub S0 (residueSimplePole f) Set.univ
  have hPV_singular_sing := cpv_singular_terms_exist S hS_discrete hS_closed S0 hS0_subset
    γ h_null hS_on_curve h_no_endpt_cross h_unique_cross (residueSimplePole f)
  have h_sing_thm := generalizedResidueTheorem' Set.univ isOpen_univ convex_univ
    S (fun s _ => Set.mem_univ s) hS_discrete hS_closed S0 hS0_subset
    f_sing hf_sing_diff γ h_null.closed (fun t _ => Set.mem_univ _)
    (fun t ht h_mem => hS_on_curve t ht h_mem)
    (fun s hs => hasSimplePoleAt_sum_div_sub S0 (residueSimplePole f) s hs)
    (fun s hs => continuousAt_sum_remainder S0 (residueSimplePole f) s hs)
    hPV_singular_sing
  have h_res_sing_eq : ∀ s ∈ S0,
      residueSimplePole f_sing s = residueSimplePole f s :=
    fun s hs => residueSimplePole_sum_div_sub S0 (residueSimplePole f) s hs
  -- Step 4–5: Combine via CPV(f) - CPV(f_sing) → 0
  obtain ⟨L, hL⟩ := h_sing_thm.1
  have hT := cpv_combine S0 f f_sing γ L
    (cpv_cancel_simple_poles U S0 f hf f_sing hf_sing_diff γ h_null hg_cpv_zero) hL
  rw [show cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b = L from hT.limUnder_eq,
    show L = cauchyPrincipalValueOn S0 f_sing γ.toFun γ.a γ.b from hL.limUnder_eq.symm,
    h_sing_thm.2]; congr 1; apply Finset.sum_congr rfl
  intro s hs; rw [h_res_sing_eq s hs, residueAt_eq_residueSimplePole f s (hSimplePoles s hs)]

