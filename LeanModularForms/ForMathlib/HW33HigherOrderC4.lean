/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33HigherOrderC3
import LeanModularForms.ForMathlib.HigherOrderAssembly

/-!
# C-4 — Closed residue theorem for higher-order poles (avoidance case)

This file composes the B-6 closed simple-pole residue theorem with the C-3
higher-order polar avoidance cancellation. The result is a closed residue
theorem for functions of the form `f_simple + (higher-order Laurent corrections)`
in the avoidance case.

## Main results

* `hasCauchyPVOn_add_higherOrderPolar_of_avoids`: closure of `HasCauchyPVOn`
  under adding a single higher-order polar term `∑ s ∈ S, c s / (z - s)^k`
  (k ≥ 2), in the avoidance case.

* `generalizedResidueTheorem_higherOrder_avoids_closed`: the C-4 statement —
  closed-form residue theorem for `f_simple + (higher-order polar corrections)`
  in the avoidance case, with γ closed null-homologous and Lipschitz.

The k-odd transverse case (γ crossing poles transversally) is handled by
`hw_theorem_3_3_odd_transverse_concrete` from `HW33ExitTimeWrapper.lean`.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Classical Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- **Adding a single higher-order polar term preserves `HasCauchyPVOn`.**
If `f` has CPV `L` along `γ` avoiding `S`, and we add a higher-order polar term
`∑ s ∈ S, c s / (z - s)^k` with `k ≥ 2`, the CPV stays `L`.

Both the simple-pole CPV (which gives the residue formula) and the higher-order
polar correction's CPV (which is zero) require interval integrability of their
respective CPV integrands. -/
theorem hasCauchyPVOn_add_higherOrderPolar_of_avoids
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_f : HasCauchyPVOn S f γ L)
    (h_f_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ)
    (h_int_HO : ∀ s ∈ S, IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1)
    (h_HO_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ.toPath.extend ε t)
      volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z + ∑ s ∈ S, c s / (z - s) ^ k) γ L := by
  simpa only [add_zero] using HasCauchyPVOn.add h_f
    (hasCauchyPVOn_finset_pow_inv_of_avoids S k hk c γ hδ h_int_HO) h_f_int h_HO_int

/-- **Adding a sum of higher-order polar terms over a power range.** Iterates
`hasCauchyPVOn_add_higherOrderPolar_of_avoids` over `k ∈ Finset.Ico 2 (M + 1)`. -/
theorem hasCauchyPVOn_add_higherOrderPolarSum_of_avoids
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_f : HasCauchyPVOn S f γ L)
    (h_f_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (M : ℕ) (c_HO : ℕ → ℂ → ℂ)
    (h_int_HO : ∀ k ∈ Finset.Ico 2 (M + 1), ∀ s ∈ S, IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1)
    (h_HO_int : ∀ k ∈ Finset.Ico 2 (M + 1), ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, c_HO k s / (z - s) ^ k) γ.toPath.extend ε t)
      volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z +
        ∑ k ∈ Finset.Ico 2 (M + 1), ∑ s ∈ S, c_HO k s / (z - s) ^ k) γ L := by
  have h_HOsum :
      HasCauchyPVOn S
        (fun z => ∑ k ∈ Finset.Ico 2 (M + 1), ∑ s ∈ S, c_HO k s / (z - s) ^ k)
        γ 0 := by
    simpa only [Finset.sum_const_zero] using
      HasCauchyPVOn.finset_sum (Finset.Ico 2 (M + 1))
        (fun k hk_mem => hasCauchyPVOn_finset_pow_inv_of_avoids S k
          (Finset.mem_Ico.mp hk_mem).left (c_HO k) γ hδ (h_int_HO k hk_mem))
        h_HO_int
  simpa only [add_zero] using
    HasCauchyPVOn.add h_f h_HOsum h_f_int
      (fun ε hε => cpvIntegrandOn_finset_sum_intervalIntegrable
        (Finset.Ico 2 (M + 1)) S (h_HO_int · · ε hε))

/-- **C-4 closure (avoidance).** Given:

* a function `f_simple` with simple poles at `S` (handled via B-6 closure),
* higher-order corrections `∑ k ∈ Finset.Ico 2 (M + 1), ∑ s ∈ S, c_HO k s / (z - s)^k`
  (handled via C-3 avoidance),
* a closed null-homologous Lipschitz curve `γ` avoiding `S`,

the CPV of the combined function `f_simple + HOPP` along `γ` equals the
simple-pole residue formula `2πi · ∑ s, w(γ, s) · res(f_simple, s)`. The
higher-order corrections contribute zero by C-3.

This is the **closed C-4 in the avoidance case**, composing the B-6 closed
simple-pole residue theorem with the C-3 higher-order avoidance cancellation. -/
theorem generalizedResidueTheorem_higherOrder_avoids_closed
    {U : Set ℂ} (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (γ : PwC1Immersion x x) (h_null : IsNullHomologous γ U)
    (f_simple : ℂ → ℂ) (hf_simple : DifferentiableOn ℂ f_simple (U \ ↑S))
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f_simple s)
    (M : ℕ) (c_HO : ℕ → ℂ → ℂ)
    (h_int_HO : ∀ k ∈ Finset.Ico 2 (M + 1), ∀ s ∈ S, IntervalIntegrable
      (fun t => (1 / (γ.toPiecewiseC1Path.toPath.extend t - s) ^ k) *
        deriv γ.toPiecewiseC1Path.toPath.extend t) volume 0 1)
    (h_HO_int : ∀ k ∈ Finset.Ico 2 (M + 1), ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (fun z => ∑ s ∈ S, c_HO k s / (z - s) ^ k)
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (h_simple_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f_simple
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ.toPiecewiseC1Path t ≠ s)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => f_simple z +
        ∑ k ∈ Finset.Ico 2 (M + 1), ∑ s ∈ S, c_HO k s / (z - s) ^ k)
      γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f_simple s) := by
  have hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1,
      δ ≤ ‖γ.toPiecewiseC1Path t - s‖ :=
    avoids_finset_delta_bound γ.toPiecewiseC1Path S hγ_avoids
  exact hasCauchyPVOn_add_higherOrderPolarSum_of_avoids
    S f_simple γ.toPiecewiseC1Path hδ
    (generalizedResidueTheorem_simplePoles_nullHomologous_closed hU_open hU_ne
      hU_bounded S hS_in_U f_simple hf_simple γ h_null hSimplePoles hγ_avoids
      hδ hLip)
    h_simple_int M c_HO h_int_HO h_HO_int

end LeanModularForms

end
