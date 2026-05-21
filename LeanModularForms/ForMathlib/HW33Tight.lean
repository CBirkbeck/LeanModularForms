/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HigherOrderCancel
import LeanModularForms.ForMathlib.ExitTime
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.HungerbuhlerWasem.ExitTimeExcision
import LeanModularForms.ForMathlib.HW33MultiPole
import LeanModularForms.ForMathlib.GeneralizedResidueTheorem
import LeanModularForms.ForMathlib.HW33LaurentPolarPart
import LeanModularForms.ForMathlib.ResidueLinearity

/-!
# HW Theorem 3.3 — tight (paper-style) form and assembled closures

This file consolidates the final assembly of HW Theorem 3.3:

* the **odd transverse case** wrappers around `firstExitTimeRight` /
  `firstExitTimeLeft` (formerly `HW33ExitTimeWrapper.lean`);
* the **assembled single-pole transverse closure** in `HasCauchyPVOn` form
  (formerly `HW33Final.lean`);
* the **`hCancel` discharge** from a Laurent decomposition under condition (B)
  and the end-of-line user-facing closed form
  (formerly `HW33Closed.lean`);
* the **tight (paper-style) `hw_3_3_tight`** theorem that uses the Laurent
  polar-part extraction so the user no longer supplies `h_decomp`, `h_polar`,
  `h_holo` — those are extracted from condition (B)'s `laurent_compatible` data.

## Main results

* `hw_theorem_3_3_odd_transverse_bundled` / `_concrete`: the `k`-odd transverse
  case using `HW33ExitData` and `firstExitTime{Right,Left}` directly.
* `hasCauchyPVOn_singleton_pow_of_transverse_assembled`: the fully assembled
  single-pole transverse closure in `HasCauchyPVOn` form.
* `hCancel_of_higherOrder_decomposition_under_B`: discharges the `hCancel`
  hypothesis of `generalizedResidueTheorem` from a Laurent decomposition.
* `generalizedResidueTheorem_higherOrder_under_B_closed`: end-of-line
  user-facing form combining all of the above.
* `hw_3_3_tight`: the paper-style form of HW Theorem 3.3, using the
  Laurent polar-part extraction. This is closer to the paper's statement
  than `generalizedResidueTheorem_higherOrder_under_B_closed`.
-/

open Filter Topology Set Complex MeasureTheory HungerbuhlerWasem
open scoped Real

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## Odd transverse case: bundled and concrete forms

(Formerly `HW33ExitTimeWrapper.lean`.)
-/

section OddTransverseWrappers

variable {γ γ' : ℝ → ℂ} {a b t₀ : ℝ} {s L : ℂ} {n k : ℕ}

/-- **HW Theorem 3.3 — odd transverse, bundled form.** Same as
`hw_theorem_3_3_odd_transverse_parametric`, but the four asymptotic hypotheses
on the exit-time functions are packaged into a single `HW33ExitData` value. -/
theorem hw_theorem_3_3_odd_transverse_bundled
    (h_close : γ a = γ b)
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (data : HW33ExitData γ t₀ s)
    (h_minus_smooth : ∀ ε > 0, ∀ t ∈ Set.uIcc a (data.tMinus ε), HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ ε > 0, ∀ t ∈ Set.uIcc a (data.tMinus ε), γ t ≠ s)
    (h_minus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume a (data.tMinus ε))
    (h_plus_smooth : ∀ ε > 0, ∀ t ∈ Set.uIcc (data.tPlus ε) b, HasDerivAt γ (γ' t) t)
    (h_plus_avoids : ∀ ε > 0, ∀ t ∈ Set.uIcc (data.tPlus ε) b, γ t ≠ s)
    (h_plus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume (data.tPlus ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(data.tMinus ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (data.tPlus ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  hw_theorem_3_3_odd_transverse_parametric
    h_close h_flat hL h_deriv_right h_deriv_left hL_right hL_left
    h_s hk hk_odd hkn hn1
    data.tPlus data.tMinus
    data.plus_to data.plus_radius data.minus_to data.minus_radius
    h_minus_smooth h_minus_avoids h_minus_int
    h_plus_smooth h_plus_avoids h_plus_int

/-- **HW Theorem 3.3 — odd transverse, fully concrete form.** Uses
`firstExitTimeRight` and `firstExitTimeLeft` directly. The user supplies:

* The crossing data: γ flat of order n, derivative L ≠ 0 from each side, and
  γ(t₀) = s, with k odd ∈ [2, n].
* Continuity of γ on `[t₀ - δMinus, t₀ + δPlus]`.
* The "γ leaves `s` away from `t₀`" hypothesis on each side.
* The smoothness / avoidance / integrability hypotheses on the punctured
  outer intervals (these are already needed for the Phase 3 PV theorem).

The conclusion is the CPV vanishing as ε → 0⁺. -/
theorem hw_theorem_3_3_odd_transverse_concrete
    {δPlus δMinus : ℝ} (hδPlus : 0 < δPlus) (hδMinus : 0 < δMinus)
    (h_close : γ a = γ b)
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (hγ_cont_right : ContinuousOn γ (Set.Icc t₀ (t₀ + δPlus)))
    (hγ_cont_left : ContinuousOn γ (Set.Icc (t₀ - δMinus) t₀))
    (h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + δPlus), γ t ≠ s)
    (h_leave_left : ∀ t ∈ Set.Ico (t₀ - δMinus) t₀, γ t ≠ s)
    (h_minus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc a (firstExitTimeLeft γ t₀ δMinus s ε), HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc a (firstExitTimeLeft γ t₀ δMinus s ε), γ t ≠ s)
    (h_minus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume a (firstExitTimeLeft γ t₀ δMinus s ε))
    (h_plus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (firstExitTimeRight γ t₀ δPlus s ε) b, HasDerivAt γ (γ' t) t)
    (h_plus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (firstExitTimeRight γ t₀ δPlus s ε) b, γ t ≠ s)
    (h_plus_int : ∀ ε > 0, IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k)
      MeasureTheory.volume (firstExitTimeRight γ t₀ δPlus s ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(firstExitTimeLeft γ t₀ δMinus s ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (firstExitTimeRight γ t₀ δPlus s ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  hw_theorem_3_3_odd_transverse_bundled
    h_close h_flat hL h_deriv_right h_deriv_left hL_right hL_left
    h_s hk hk_odd hkn hn1
    (HW33ExitData.ofExitTimes hδPlus hδMinus
      hγ_cont_right hγ_cont_left h_s h_leave_right h_leave_left)
    h_minus_smooth h_minus_avoids h_minus_int
    h_plus_smooth h_plus_avoids h_plus_int

end OddTransverseWrappers

/-! ## Assembled single-pole transverse closure (`HasCauchyPVOn` form)

(Formerly `HW33Final.lean`.)
-/

/-- **HW Theorem 3.3 — k-odd transverse case (single pole, `HasCauchyPVOn` form).**

For a closed Lipschitz `γ : PiecewiseC1Path x x` with a single transverse
crossing at `t₀ ∈ (0, 1)` of pole `s`, where `γ' (t₀) = L ≠ 0` from both sides,
γ is flat of order `n ≥ k` (with `k` odd), strict (anti-)monotonicity of
`‖γ - s‖` near `t₀`, and avoidance margins / integrability outside, the CPV
along γ vanishes:

  `HasCauchyPVOn {s} (fun z => 1 / (z - s)^k) γ 0`.

This is the **fully assembled HW 3.3 closure for the k-odd transverse case**
in the `HasCauchyPVOn` form, composing:

* `hw_theorem_3_3_odd_transverse_concrete` (parametric symmetric-excision PV)
* `shape_eventually_of_strict_mono` (shape hypothesis)
* `hasCauchyPVOn_singleton_of_exitTime_excision` (bridge to `HasCauchyPVOn`).

All lower-level machinery (exit times, strict mono from transverse, integral
splitting under shape) closes cleanly with no new sorries.

The strict (anti-)monotonicity hypotheses can be derived from the more basic
transverse data via `exists_strictMonoOn_norm_right_of_transverse` and
`exists_strictAntiOn_norm_left_of_transverse` from `HW33Monotonicity.lean`. -/
theorem hasCauchyPVOn_singleton_pow_of_transverse_assembled
    {γ : PiecewiseC1Path x x} {s L : ℂ}
    {t₀ δMinus δPlus : ℝ} {n k : ℕ}
    (h_t₀_minus_pos : 0 ≤ t₀ - δMinus) (h_t₀_plus_le : t₀ + δPlus ≤ 1)
    (hδMinus : 0 < δMinus) (hδPlus : 0 < δPlus)
    (h_close : γ.toPath.extend 0 = γ.toPath.extend 1)
    (h_flat : IsFlatOfOrder γ.toPath.extend t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ.toPath.extend L (Set.Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ.toPath.extend L (Set.Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ.toPath.extend) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ.toPath.extend) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ.toPath.extend t₀ = s)
    (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (hγ_cont_right : ContinuousOn γ.toPath.extend (Set.Icc t₀ (t₀ + δPlus)))
    (hγ_cont_left : ContinuousOn γ.toPath.extend (Set.Icc (t₀ - δMinus) t₀))
    (h_leave_right : ∀ t ∈ Set.Ioc t₀ (t₀ + δPlus), γ.toPath.extend t ≠ s)
    (h_leave_left : ∀ t ∈ Set.Ico (t₀ - δMinus) t₀, γ.toPath.extend t ≠ s)
    (hγ_anti : StrictAntiOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc (t₀ - δMinus) t₀))
    (hγ_mono : StrictMonoOn (fun t => ‖γ.toPath.extend t - s‖)
      (Set.Icc t₀ (t₀ + δPlus)))
    {δ_avoid_left δ_avoid_right : ℝ}
    (h_avoid_left_pos : 0 < δ_avoid_left)
    (h_avoid_right_pos : 0 < δ_avoid_right)
    (h_avoid_left : ∀ t ∈ Set.Icc (0 : ℝ) (t₀ - δMinus),
      δ_avoid_left ≤ ‖γ.toPath.extend t - s‖)
    (h_avoid_right : ∀ t ∈ Set.Icc (t₀ + δPlus) (1 : ℝ),
      δ_avoid_right ≤ ‖γ.toPath.extend t - s‖)
    (h_minus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_minus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc (0 : ℝ)
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε),
      γ.toPath.extend t ≠ s)
    (h_minus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume 0
        (firstExitTimeLeft γ.toPath.extend t₀ δMinus s ε))
    (h_plus_smooth : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      HasDerivAt γ.toPath.extend (deriv γ.toPath.extend t) t)
    (h_plus_avoids : ∀ ε > 0,
      ∀ t ∈ Set.uIcc
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ),
      γ.toPath.extend t ≠ s)
    (h_plus_int : ∀ ε > 0,
      IntervalIntegrable
        (fun t => deriv γ.toPath.extend t / (γ.toPath.extend t - s) ^ k)
        MeasureTheory.volume
        (firstExitTimeRight γ.toPath.extend t₀ δPlus s ε) (1 : ℝ))
    (h_int_full : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => cpvIntegrandOn {s}
        (fun z => (1 : ℂ) / (z - s) ^ k) γ.toPath.extend ε t)
      MeasureTheory.volume 0 1) :
    HasCauchyPVOn {s} (fun z => (1 : ℂ) / (z - s) ^ k) γ 0 :=
  hasCauchyPVOn_singleton_of_exitTime_excision γ s
    (fun z => (1 : ℂ) / (z - s) ^ k)
    (shape_eventually_of_strict_mono h_t₀_minus_pos h_t₀_plus_le hδMinus hδPlus
      hγ_cont_left hγ_cont_right hγ_anti hγ_mono h_s
      h_avoid_left_pos h_avoid_right_pos h_avoid_left h_avoid_right) h_int_full
    ((hw_theorem_3_3_odd_transverse_concrete (γ := γ.toPath.extend)
      (γ' := deriv γ.toPath.extend) (s := s) (L := L) (n := n) (k := k)
      (a := 0) (b := 1) (t₀ := t₀) (δMinus := δMinus) (δPlus := δPlus)
      hδPlus hδMinus h_close h_flat hL h_deriv_right h_deriv_left
      hL_right hL_left h_s hk hk_odd hkn hn1
      hγ_cont_right hγ_cont_left h_leave_right h_leave_left
      h_minus_smooth h_minus_avoids h_minus_int
      h_plus_smooth h_plus_avoids h_plus_int).congr fun ε => by
        congr 1 <;> exact intervalIntegral.integral_congr fun t _ => by ring)

/-! ## `hCancel` discharge and closed user-facing form

(Formerly `HW33Closed.lean`.)
-/

/-- **Discharge `hCancel` from Laurent decomposition + (B)-closure.**

If the remainder `f - principalPartSum` decomposes as
`(higher-order polar terms) + (holomorphic remainder)` where:
* The higher-order polar terms have CPV zero (e.g., by the (B)-closure
  `hasCauchyPVOn_multipole_pow_of_conditionB_assembled`),
* The holomorphic remainder has CPV zero (by Cauchy along null-hom γ),

then `hCancel` holds. -/
theorem hCancel_of_higherOrder_decomposition_under_B
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (h_polar h_holo : ℂ → ℂ)
    (h_decomp : ∀ z,
      f z - principalPartSum S (fun s => residue f s) z =
        h_polar z + h_holo z)
    (h_polar_cancel : HasCauchyPVOn S h_polar γ 0)
    (h_holo_cancel : HasCauchyPVOn S h_holo γ 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_polar γ.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_holo γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_decomposition S f γ h_holo h_polar
    (fun z => (h_decomp z).trans (add_comm _ _))
    h_holo_cancel h_polar_cancel hI_holo hI_polar

/-- **HW Theorem 3.3 — fully closed under condition (B).**

The end-of-line user-facing form: combines
* `hCancel_of_higherOrder_decomposition_under_B` (hCancel discharge)
* `hPV_sing` from a singular-part PV computation (often
  `hasCauchyPVOn_simplePoles_nullHomologous_closed_full` for null-hom γ)

to produce the closed residue formula.

This is the intended end-state for the higher-order generalized residue
theorem under condition (B), bridging the (B)-closure machinery in
`HW33SectorEven.lean` to the abstract `generalizedResidueTheorem`. -/
theorem generalizedResidueTheorem_higherOrder_under_B_closed
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S)
    (h_polar h_holo : ℂ → ℂ)
    (h_decomp : ∀ z,
      f z - principalPartSum S (fun s => residue f s) z =
        h_polar z + h_holo z)
    (h_polar_cancel : HasCauchyPVOn S h_polar γ.toPiecewiseC1Path 0)
    (h_holo_cancel : HasCauchyPVOn S h_holo γ.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_polar γ.toPiecewiseC1Path.toPath.extend ε t)
      volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_holo γ.toPiecewiseC1Path.toPath.extend ε t)
      volume 0 1)
    (hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s))
    (hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (principalPartSum S (fun s => residue f s))
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) := by
  have hI_rem : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => f z - principalPartSum S (fun s => residue f s) z)
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1 := by
    intro ε hε
    refine ((hI_polar ε hε).add (hI_holo ε hε)).congr ?_
    intro t _
    simp only [cpvIntegrandOn]
    split_ifs with h <;> simp [h_decomp, add_mul]
  exact generalizedResidueTheorem hU S hS_in_U f hf γ h_null hMero hCondA hCondB
    (hCancel_of_higherOrder_decomposition_under_B S f γ.toPiecewiseC1Path
      h_polar h_holo h_decomp h_polar_cancel h_holo_cancel hI_polar hI_holo)
    hPV_sing hI_sing hI_rem

/-! ## Tight (paper-style) form

The tight `hw_3_3` theorem using the Laurent polar-part extraction from
`HW33LaurentPolarPart.lean`. Compared to
`generalizedResidueTheorem_higherOrder_under_B_closed` above, the user no longer
supplies `h_decomp`, `h_polar`, `h_holo` — these are extracted from condition
(B)'s `laurent_compatible` data.

The user still supplies:
* The CPV-vanishing of the higher-order polar part (`h_polar_cancel`):
  derivable from per-pole `hasCauchyPVOn_singleton_pow_of_conditionB_assembled`
  + multi-pole composition.
* The CPV-vanishing of the holomorphic remainder (`h_holo_cancel`):
  derivable from Cauchy along null-homologous γ for analytic functions.
* Integrability hypotheses.
* The simple-pole `hPV_sing` (typically from `B-6` closure).

Compared to the original `generalizedResidueTheorem`, we eliminate:
- 4 functions (`h_polar`, `h_holo`, plus the implicit residue function args)
- 1 decomposition equation hypothesis (`h_decomp` — now definitional)
-/

/-- **HW Theorem 3.3 — tight (paper-style) form.**

For meromorphic `f` on `U` with poles at `S`, closed null-homologous
piecewise-C¹ immersion `γ` in `U`, conditions (A')+(B), the CPV equals
the winding-number-weighted residue formula.

Compared to `generalizedResidueTheorem_higherOrder_under_B_closed`, the
Laurent decomposition is **definitional** (extracted from condition (B)),
so the user need not supply `h_decomp`, `h_polar`, `h_holo` separately.

The hypotheses still required (until full automation):
* `h_polar_cancel`: the higher-order polar part `laurentHigherOrderPolar`
  has CPV zero. Discharged via per-pole (B)-closure + multi-pole composition.
* `h_holo_cancel`: the holomorphic remainder has CPV zero. Discharged via
  Cauchy + null-homology for the now-analytic `f - laurentPolarPartTotal`.
* Standard integrability conditions on the cpvIntegrandOn at each ε.
* `hPV_sing` for the simple-pole part (typically from `B-6`). -/
theorem hw_3_3_tight {U : Set ℂ} (hU : IsOpen U) (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S)) (γ : PwC1Immersion x x)
    (h_null : IsNullHomologous γ U) (hMero : ∀ s ∈ S, MeromorphicAt f s)
    (hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (hCondB : SatisfiesConditionB γ f S)
    (h_polar_cancel : HasCauchyPVOn S (laurentHigherOrderPolar hCondB) γ.toPiecewiseC1Path 0)
    (h_holo_cancel : HasCauchyPVOn S (laurentHolomorphicRemainder hCondB) γ.toPiecewiseC1Path 0)
    (hI_polar : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S
      (laurentHigherOrderPolar hCondB) γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_holo : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S
      (laurentHolomorphicRemainder hCondB) γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hPV_sing : HasCauchyPVOn S (principalPartSum S (fun s => residue f s)) γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s))
    (hI_sing : ∀ ε > 0, IntervalIntegrable (fun t => cpvIntegrandOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path (2 * ↑Real.pi * I *
      ∑ s ∈ S, generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) :=
  generalizedResidueTheorem_higherOrder_under_B_closed hU S hS_in_U f hf γ h_null hMero hCondA
    hCondB (laurentHigherOrderPolar hCondB) (laurentHolomorphicRemainder hCondB)
    (f_minus_pp_eq_higherOrder_plus_holo hCondB) h_polar_cancel h_holo_cancel hI_polar hI_holo
    hPV_sing hI_sing

end LeanModularForms

end
