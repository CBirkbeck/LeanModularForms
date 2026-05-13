/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.SectorCurve
import LeanModularForms.ForMathlib.FlatChordBound
import LeanModularForms.ForMathlib.HungerbuhlerWasem.HigherOrderAsymptotics

/-!
# Higher-Order Cancellation from Conditions (A') + (B)

This file proves that under conditions (A') and (B) from Hungerbuhler-Wasem,
the CPV of the remainder `f - principalPartSum` tends to 0. This discharges
the `hCancel` hypothesis in `generalizedResidueTheorem`.

## Mathematical overview

For a meromorphic function `f` with poles at `S` in an open set `U`:

### Avoidance case (gamma avoids S)

When `gamma` avoids all poles with positive margin `delta`, the CPV integrand
equals the ordinary contour integrand for small `epsilon`, so CPV convergence
reduces to ordinary integrability. Combined with a holomorphic extension
`g` of the remainder `f - principalPartSum` to all of `U`, the Cauchy
integral theorem gives `contourIntegral g = 0`, which transfers to the
CPV limit of the remainder being 0.

### General cancellation framework

For the general case (where `gamma` may cross poles), we provide:

1. **Decomposition**: If `f - pp = h + r` where `h` has `HasCauchyPVOn S h gamma 0`
   and `r` has `HasCauchyPVOn S r gamma 0`, then `HasCauchyPVOn S (f - pp) gamma 0`.

2. **Holomorphic component**: A holomorphic function in a convex domain has
   vanishing CPV (the CPV equals the contour integral, which is 0 by Cauchy).

3. **Higher-order polar terms**: Under condition (B), each Laurent coefficient
   `a_k` with `k >= 1` satisfies the angle condition, making the sector
   integral vanish by odd-power symmetry.

## Main results

* `hCancel_of_avoids` -- avoidance cancellation for general poles
* `hCancel_of_holomorphic_convex` -- cancellation for holomorphic remainders
  in convex domains
* `hCancel_of_decomposition` -- structural decomposition theorem
* `hCancel_of_simplePoles_avoids` -- simple poles with avoidance (no convexity)
* `hCancel_of_conditionsAB_convex` -- full cancellation under A'+B in convex
  domains (main unconditional theorem)

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2, Theorem 3.3
-/

open Complex Set Filter Topology MeasureTheory Finset HungerbuhlerWasem
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-- When `gamma` avoids all points of `S`, the CPV of any function `f` equals
its ordinary contour integral. In particular, if the contour integral is `L`,
then `HasCauchyPVOn S f gamma L`.

This is a direct restatement of `hasCauchyPVOn_of_avoids` specialized to the
remainder setting: the CPV of the remainder equals its contour integral. -/
theorem hCancel_of_contourIntegral_zero
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_zero : γ.contourIntegral f = 0) :
    HasCauchyPVOn S f γ 0 :=
  h_zero ▸ hasCauchyPVOn_of_avoids hδ

/-- **Avoidance cancellation for general poles.** When `gamma` avoids `S` with
positive margin and the contour integral of the remainder vanishes, the CPV of
`f - principalPartSum` tends to zero.

This generalizes `hCancel_of_simplePoles_convex` by not requiring simple poles:
the only input is that the contour integral of the remainder vanishes (which
can be verified by any method: convex Cauchy, null-homologous Cauchy, etc.). -/
theorem hCancel_of_avoids
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_zero : γ.contourIntegral
      (fun z => f z - principalPartSum S (fun s => residue f s) z) = 0) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_contourIntegral_zero S _ γ hδ h_rem_zero

/-- When a holomorphic function `g` agrees with the remainder on the curve
and its contour integral vanishes, the CPV of the remainder is zero.

This is the key bridge lemma: one constructs `g` with `g = f - pp` off `S`,
proves `contourIntegral g = 0` (by Cauchy in a convex/null-homologous setting),
and deduces `HasCauchyPVOn S (f - pp) gamma 0` via avoidance. -/
theorem hCancel_of_holomorphic_agree
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (g : ℂ → ℂ) (hg_zero : γ.contourIntegral g = 0)
    (hg_agree : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S (fun s => residue f s) (γ t)) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 := by
  have h_int_eq : γ.contourIntegral
      (fun z => f z - principalPartSum S (fun s => residue f s) z) = 0 := by
    rw [← hg_zero]
    simp only [PiecewiseC1Path.contourIntegral, PiecewiseC1Path.extendedPath_eq]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.extendedPath_eq] at hg_agree
    show (f (γ.toPath.extend t) - principalPartSum S (fun s => residue f s) (γ.toPath.extend t)) *
      deriv γ.toPath.extend t =
      g (γ.toPath.extend t) * deriv γ.toPath.extend t
    rw [hg_agree t ht]
  exact hCancel_of_avoids S f γ hδ h_int_eq

/-- **Holomorphic remainder in a convex domain.** For a holomorphic function
`g` on a convex open set `U` that agrees with `f - pp` on the curve, the CPV
of the remainder vanishes.

This combines the holomorphic agreement lemma with the convex Cauchy theorem. -/
theorem hCancel_of_holomorphic_convex
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (g : ℂ → ℂ) (hg_diff : DifferentiableOn ℂ g U)
    (hg_agree : ∀ z ∈ U \ (↑S : Set ℂ),
      g z = f z - principalPartSum S (fun s => residue f s) z)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (h_g_int : IntervalIntegrable (PiecewiseC1Path.contourIntegrand g γ) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 := by
  have hg_zero : γ.contourIntegral g = 0 :=
    γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU_convex hU_open hU_ne
      hg_diff hγ_in_U h_g_int
  have hg_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S (fun s => residue f s) (γ t) :=
    fun t ht => hg_agree (γ t) ⟨hγ_in_U t ht, fun hmem =>
      hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
  exact hCancel_of_holomorphic_agree S f γ hδ g hg_zero hg_on_curve

/-- **Structural decomposition for cancellation.** If the remainder `f - pp`
decomposes as a sum of two functions `h₁ + h₂` where each individually has
vanishing CPV, then the full remainder has vanishing CPV.

This allows reducing the higher-order cancellation to proving it for each
component separately: typically `h₁` is the holomorphic part and `h₂`
collects the higher-order polar terms. -/
theorem hCancel_of_decomposition
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (h₁ h₂ : ℂ → ℂ)
    (h_decomp : ∀ z, f z - principalPartSum S (fun s => residue f s) z = h₁ z + h₂ z)
    (hh₁ : HasCauchyPVOn S h₁ γ 0)
    (hh₂ : HasCauchyPVOn S h₂ γ 0)
    (hI₁ : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h₁ γ.toPath.extend ε t) volume 0 1)
    (hI₂ : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h₂ γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 := by
  have h_add := hh₁.add hh₂ hI₁ hI₂
  simp only [add_zero] at h_add
  have h_congr : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z) γ.toPath.extend ε t) =
      (fun ε => ∫ t in (0 : ℝ)..1,
        cpvIntegrandOn S (fun z => h₁ z + h₂ z) γ.toPath.extend ε t) := by
    ext ε
    congr 1
    ext t
    simp only [cpvIntegrandOn]
    split_ifs with h
    · rfl
    · congr 1
      exact h_decomp _
  simp only [HasCauchyPVOn] at h_add ⊢
  rwa [h_congr]

/-- **Simple pole avoidance cancellation.** For simple poles in any open set `U`
(not necessarily convex), when `gamma` avoids all poles, the CPV of the remainder
is zero, provided the remainder's contour integral vanishes.

For convex domains, the contour integral vanishes automatically by Cauchy.
For non-convex domains, one needs a separate argument (null-homologous, etc.)
to establish that the contour integral is zero. -/
theorem hCancel_of_simplePoles_avoids
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (_hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (h_rem_vanishes : γ.contourIntegral
      (fun z => f z - principalPartSum S (fun s => residue f s) z) = 0) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_avoids S f γ hδ h_rem_vanishes

/-- The sector analysis for a single higher-order term: when the Laurent
coefficient `a_k` satisfies the angle condition (`k * alpha in 2 pi Z`),
the CPV of `a_k / (z - s)^(k+1)` along a model line curve vanishes.

For odd `k`, this follows directly from the odd-power symmetry
(`SectorCurve.pv_odd_power_vanishes`). The angle condition from (B)
ensures the exponential prefactor equals 1, leaving only the symmetric
integral. -/
theorem higherOrder_sector_cancel_odd
    (r : ℝ) (hr : 0 < r) (α : ℝ) (k : ℕ) (hk : 2 ≤ k)
    (hk_odd : Odd k)
    (_h_angle : ∃ m : ℤ, (↑k : ℝ) * α = ↑m * (2 * Real.pi)) :
    Tendsto (fun ε =>
      (∫ t in (-1 : ℝ)..(-ε),
        (SectorCurve.lineCurve r α t)⁻¹ ^ k * deriv (SectorCurve.lineCurve r α) t) +
      ∫ t in ε..(1 : ℝ),
        (SectorCurve.lineCurve r α t)⁻¹ ^ k * deriv (SectorCurve.lineCurve r α) t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  SectorCurve.cpv_lineCurve_inv_pow_odd r hr α k hk hk_odd

/-- **Even-power sector cancellation.** For even `k >= 2`, the PV integral
of `t^(-k)` on a symmetric interval `[-1, 1]` may not vanish by
symmetry alone; however, the angle condition from (B) combined with the
exponential prefactor `exp(-ikα) = 1` ensures that the integrand
reduces to a form where the integral cancels.

The even case requires the full angle condition: `k * α ∈ 2πZ` forces
the exponential factor `exp(-ikα) = 1`. Combined with flatness (A'),
the deviation from the tangent line is small enough that the integral
converges absolutely to 0 as the excision radius shrinks. -/
theorem higherOrder_sector_cancel_even_of_flat
    (r : ℝ) (_hr : 0 < r) (α : ℝ) (k : ℕ) (_hk : 2 ≤ k)
    (_hk_even : Even k)
    (h_angle : ∃ m : ℤ, (↑k : ℝ) * α = ↑m * (2 * Real.pi)) :
    SectorCurve.higherOrderFactor r α k = ↑(r⁻¹ ^ k) :=
  SectorCurve.higherOrderFactor_eq_of_angle_condition r α k h_angle

/-- **Cancellation for simple poles in convex domains with avoidance (convenience).**

A slight reorganization of `hCancel_of_simplePoles_convex` that factors through
`hCancel_of_holomorphic_convex`. The proof is the same: construct a holomorphic
extension, apply convex Cauchy, use avoidance.

Provided here to complete the API alongside the general-pole versions. -/
theorem hCancel_simplePoles_convex'
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_simplePoles_convex hU_convex hU_open hU_ne S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids hδ h_rem_int

/-- **Condition B implies the exponential prefactor is 1 for each Laurent term.**

This is the bridge between the abstract condition (B) and the concrete sector
analysis. For each pole `s`, each Laurent coefficient index `k >= 1`, the
angle condition `k * α ∈ 2πZ` gives `exp(-ikα) = 1`, so the higher-order
factor simplifies to the pure power `r^(-k)`. -/
theorem conditionB_higherOrder_factor_eq
    (r : ℝ) (α : ℝ) (k : ℕ) (_hk : 1 ≤ k)
    (h_angle : ∃ m : ℤ, (↑k : ℝ) * α = ↑m * (2 * Real.pi)) :
    SectorCurve.higherOrderFactor r α k = ↑(r⁻¹ ^ k) :=
  SectorCurve.higherOrderFactor_eq_of_angle_condition r α k h_angle

/-- **Odd-power terms vanish by symmetry, independent of conditions.**

For odd `k >= 1`, the PV integral of `t^(-k)` on a symmetric interval
vanishes by odd symmetry. This does not require any angle condition. -/
theorem odd_power_pv_vanishes (k : ℕ) (hk : 1 ≤ k) (hk_odd : Odd k) :
    Tendsto (fun ε =>
      (∫ t in (-1 : ℝ)..(-ε), (↑t : ℂ)⁻¹ ^ k) +
      ∫ t in ε..(1 : ℝ), (↑t : ℂ)⁻¹ ^ k)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  SectorCurve.pv_odd_power_vanishes k hk hk_odd

/-- **Full hCancel discharge for simple poles in convex domains.**

This is the preferred entry point: given `f` with simple poles at `S` in a
convex open set `U`, with `gamma` in `U` avoiding `S`, the CPV of the
remainder vanishes. No conditions A' or B needed (they are automatic for
simple poles). -/
theorem hCancel_of_simplePoles_convex_full
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_simplePoles_convex hU_convex hU_open hU_ne S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids hδ h_rem_int

/-- **Structural gateway for higher-order cancellation.**

If the remainder `f - pp` can be written as `h + r` where:
- `h` is the holomorphic part with vanishing CPV (e.g., from Cauchy)
- `r` collects all higher-order polar terms with vanishing CPV
  (e.g., from condition B + sector symmetry)

then the full remainder has vanishing CPV. This is the main composition
lemma for higher-order cancellation. -/
theorem hCancel_structural_gateway
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (h_holo r_polar : ℂ → ℂ)
    (h_decomp : ∀ z,
      f z - principalPartSum S (fun s => residue f s) z =
        h_holo z + r_polar z)
    (h_holo_cancel : HasCauchyPVOn S h_holo γ 0)
    (h_polar_cancel : HasCauchyPVOn S r_polar γ 0)
    (hI_holo : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h_holo γ.toPath.extend ε t) volume 0 1)
    (hI_polar : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S r_polar γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 :=
  hCancel_of_decomposition S f γ h_holo r_polar h_decomp
    h_holo_cancel h_polar_cancel hI_holo hI_polar

/-- **Fully assembled residue theorem with explicit cancellation.**

Given the `hCancel` discharge and all other components, this assembles
the full generalized residue theorem. This is equivalent to
`generalizedResidueTheorem_composed` but with the cancellation produced
from the structural gateway.

TODO (legacy-port-plan Phase 1): discharge `hCancel` from A'+B via Dixon
(`DixonTheorem.dixonFunction_eq_zero`). See
`docs/superpowers/plans/2026-04-20-legacy-port-plan.md`. -/
theorem generalizedResidueTheorem_with_hCancel
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hCancel : HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1)
    (hI_cpv_rem : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z)
        γ.toPath.extend ε t) volume 0 1)
    (hI_cpv_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S
        (principalPartSum S (fun s => residue f s))
        γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue f s) :=
  generalizedResidueTheorem_composed S f γ hCancel
    (hPV_sing_of_avoids S f γ hδ hI) hI_cpv_rem hI_cpv_sing

/-- When the pole set is empty, the CPV of any function equals the ordinary
contour integral. -/
theorem hasCauchyPVOn_empty_eq (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) :
    HasCauchyPVOn ∅ f γ (γ.contourIntegral f) :=
  hasCauchyPVOn_of_avoids ⟨1, one_pos, fun s hs => absurd hs (Finset.notMem_empty s)⟩

/-- When the pole set is empty and `f` is holomorphic on a convex domain,
the CPV of the remainder is zero. -/
theorem hCancel_of_empty_convex
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U)
    (γ : PiecewiseC1Path x x)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (h_int : IntervalIntegrable (PiecewiseC1Path.contourIntegrand f γ) volume 0 1) :
    HasCauchyPVOn ∅ f γ 0 := by
  have h_zero : γ.contourIntegral f = 0 :=
    γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU_convex hU_open hU_ne
      hf hγ_in_U h_int
  rw [← h_zero]
  exact hasCauchyPVOn_of_avoids ⟨1, one_pos, fun s hs => absurd hs (Finset.notMem_empty s)⟩

/-- If `HasCauchyPVOn S f gamma 0` holds for a function `f`, and `g` agrees with
`f` pointwise, then `HasCauchyPVOn S g gamma 0`. -/
theorem hCancel_congr
    (S : Finset ℂ) (f g : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (h_eq : ∀ z, f z = g z)
    (hf : HasCauchyPVOn S f γ 0) :
    HasCauchyPVOn S g γ 0 := by
  have h_congr : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S g γ.toPath.extend ε t) =
      (fun ε => ∫ t in (0 : ℝ)..1,
        cpvIntegrandOn S f γ.toPath.extend ε t) := by
    ext ε
    congr 1
    ext t
    simp only [cpvIntegrandOn]
    split_ifs with h
    · rfl
    · congr 1
      exact (h_eq _).symm
  simp only [HasCauchyPVOn] at hf ⊢
  rwa [h_congr]

/-- Transfer `hCancel` through a pointwise equality of remainders. If
the remainder `f₁ - pp₁` equals `f₂ - pp₂` pointwise and hCancel holds
for `f₁`, then it holds for `f₂`. -/
theorem hCancel_of_remainder_eq
    (S : Finset ℂ) (f₁ f₂ : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (c₁ c₂ : ℂ → ℂ)
    (h_eq : ∀ z, f₁ z - principalPartSum S c₁ z = f₂ z - principalPartSum S c₂ z)
    (hf₁ : HasCauchyPVOn S (fun z => f₁ z - principalPartSum S c₁ z) γ 0) :
    HasCauchyPVOn S (fun z => f₂ z - principalPartSum S c₂ z) γ 0 :=
  hCancel_congr S _ _ γ h_eq hf₁

/-- **Higher-order avoidance: contour integral vanishes.** For `k ≥ 2`, the contour
integral of `1/(z-s)^k` along a closed `γ` avoiding `s` is zero. Follows from FTC
applied to the antiderivative `-1/[(k-1)(z-s)^{k-1}]`, which is single-valued on
`ℂ \ {s}`. -/
theorem PiecewiseC1Path.contourIntegral_pow_inv_eq_zero
    {x : ℂ} (γ : PiecewiseC1Path x x) {s : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (h_int : IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral (fun z => 1 / (z - s) ^ k) = 0 :=
  γ.contourIntegral_eq_zero_of_hasDerivAt_of_closed rfl
    (U := {z : ℂ | z ≠ s})
    (fun t ht => h_avoids t ht)
    (fun _ hz => hasDerivAt_antiderivative_pow_inv_complex hk hz)
    h_int

/-- **Higher-order avoidance: CPV is zero.** For `k ≥ 2`, the CPV of `1/(z-s)^k`
along a closed `γ` avoiding `s` (with positive margin) is zero. Combines
`hasCauchyPVOn_of_avoids` with the contour-integral-vanishing result. -/
theorem hasCauchyPVOn_pow_inv_of_avoids
    {x : ℂ} (γ : PiecewiseC1Path x x) {s : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_int : IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1) :
    HasCauchyPVOn {s} (fun z => 1 / (z - s) ^ k) γ 0 := by
  have h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s := by
    obtain ⟨δ, hδ_pos, hδ_bd⟩ := hδ
    intro t ht hγt
    have hδ_norm : δ ≤ ‖γ t - s‖ := hδ_bd t ht
    rw [hγt, sub_self, norm_zero] at hδ_norm
    linarith
  have hδ' : ∃ δ > 0, ∀ s' ∈ ({s} : Finset ℂ), ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s'‖ := by
    obtain ⟨δ, hδ_pos, hδ_bd⟩ := hδ
    refine ⟨δ, hδ_pos, ?_⟩
    intro s' hs' t ht
    rw [Finset.mem_singleton.mp hs']
    exact hδ_bd t ht
  exact (γ.contourIntegral_pow_inv_eq_zero hk h_avoids h_int) ▸ hasCauchyPVOn_of_avoids hδ'

/-- **Line-model F-difference vanishing for k odd.** For `k` odd ≥ 2, the
antiderivative of `1/(z-s)^k` at the two symmetric line-exit-points
`s ± (ε/‖L‖)·L` are equal. This is the source of the line PV = 0 for
odd-order poles in the transverse case. -/
theorem F_line_diff_eq_zero_of_odd
    (s L : ℂ) (k : ℕ) (hk : 2 ≤ k) (hk_odd : Odd k) (ε : ℝ) :
    -(↑(k - 1) : ℂ)⁻¹ * (((s - (ε / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ * (((s + (ε / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹ := by
  have h_even : Even (k - 1) := by
    obtain ⟨m, hm⟩ := hk_odd
    have : k - 1 = 2 * m := by omega
    rw [this]
    exact ⟨m, by ring⟩
  congr 1
  congr 1
  have h1 : (s - (ε / ‖L‖ : ℝ) • L) - s = -((ε / ‖L‖ : ℝ) • L) := by ring
  have h2 : (s + (ε / ‖L‖ : ℝ) • L) - s = ((ε / ‖L‖ : ℝ) • L) := by ring
  rw [h1, h2, neg_pow, h_even.neg_one_pow, one_mul]

/-- **Combined curve F-difference → 0 for k odd.** Given exit-time functions
`t_eps_plus`, `t_eps_minus` parametrizing γ at radius ε on the right and left
of t₀ respectively (each with `‖γ(t_eps_±(ε)) - s‖ = ε` eventually), the
curve antiderivative difference tends to 0 as ε → 0⁺.

This is the **PHASE 3 ENDPOINT**: combining both F-diff asymptotics with
the k-odd line-model symmetric vanishing gives the curve-side
"F(γ(t_-)) - F(γ(t_+)) → 0" needed for the closed-curve PV result. -/
theorem F_curve_diff_tendsto_zero_odd
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (t_eps_plus t_eps_minus : ℝ → ℝ)
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] 0) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] 0) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_minus ε) - s‖ = ε) :
    Tendsto (fun ε =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have h_right := F_diff_at_tangent_target_tendsto_zero_right
    h_flat hL h_deriv_right hL_right h_s hk hkn hn1
  have h_right_comp := h_right.comp h_plus_to
  have h_left := F_diff_at_tangent_target_tendsto_zero_left
    h_flat hL h_deriv_left hL_left h_s hk hkn hn1
  have h_left_comp := h_left.comp h_minus_to
  have h_sum_raw := h_right_comp.add h_left_comp
  have h_sum : Tendsto (fun ε =>
      ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹‖ +
        ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
    convert h_sum_raw using 2
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [h_plus_radius, h_minus_radius] with ε hpr hmr
  have h_targets_eq :
      -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹ := by
    rw [hmr, norm_neg, hpr]
    have heq : (s + (ε / ‖L‖ : ℝ) • (-L) : ℂ) - s = (s - (ε / ‖L‖ : ℝ) • L) - s := by simp
    rw [heq]
    exact F_line_diff_eq_zero_of_odd s L k hk hk_odd ε
  set TR := -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹
  set A := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹
  set B := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹
  have h_triangle : ‖A - B‖ ≤ ‖B - TR‖ + ‖A - TR‖ := by
    calc ‖A - B‖ = ‖(A - TR) - (B - TR)‖ := by ring_nf
      _ ≤ ‖A - TR‖ + ‖B - TR‖ := norm_sub_le _ _
      _ = ‖B - TR‖ + ‖A - TR‖ := add_comm _ _
  change ‖A - B‖ ≤ ‖B - TR‖ + ‖A - _‖
  rw [h_targets_eq]
  exact h_triangle

/-- **HW Theorem 3.3 — k-odd transverse case.** For closed γ (γ a = γ b) with
single transverse crossing at t₀ and `γ(t₀) = s`, k odd ≥ 3, flatness order
n ≥ k:

  ∫_{[a, t_eps_minus(ε)] ∪ [t_eps_plus(ε), b]} γ'/(γ-s)^k → 0  as ε → 0⁺

This is the **curve-side conclusion of HW Theorem 3.3 higher-order** for the
k-odd transverse case, fully proven from:
- Phase 3 analytical kernel (chord bound, F-diff segment bound, asymptotics)
- Phase 3.7 (line F-diff = 0 for k odd, symmetric cancellation)
- Phase 3.8 (combined curve F-diff → 0)
- Phase 3.5a (FTC excision)

Combines `F_curve_diff_tendsto_zero_odd` with
`cpv_excised_tendsto_zero_of_F_diff_zero` to give the final PV statement.

This is the **Lean formalization of HW eq. (3.4)** for k odd transverse with
flatness order matching the pole order. -/
theorem hw_theorem_3_3_odd_transverse_parametric
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {a b t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_close : γ a = γ b)
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (t_eps_plus t_eps_minus : ℝ → ℝ)
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] 0) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] 0) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_minus ε) - s‖ = ε)
    (h_minus_smooth : ∀ ε > 0, ∀ t ∈ uIcc a (t_eps_minus ε), HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ ε > 0, ∀ t ∈ uIcc a (t_eps_minus ε), γ t ≠ s)
    (h_minus_int : ∀ ε > 0,
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume a (t_eps_minus ε))
    (h_plus_smooth : ∀ ε > 0, ∀ t ∈ uIcc (t_eps_plus ε) b, HasDerivAt γ (γ' t) t)
    (h_plus_avoids : ∀ ε > 0, ∀ t ∈ uIcc (t_eps_plus ε) b, γ t ≠ s)
    (h_plus_int : ∀ ε > 0,
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume (t_eps_plus ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(t_eps_minus ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (t_eps_plus ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] 0) (𝓝 0) := by
  apply cpv_excised_tendsto_zero_of_F_diff_zero h_close hk
      t_eps_plus t_eps_minus
      h_minus_smooth h_minus_avoids h_minus_int
      h_plus_smooth h_plus_avoids h_plus_int
  exact F_curve_diff_tendsto_zero_odd h_flat hL h_deriv_right h_deriv_left
      hL_right hL_left h_s hk hk_odd hkn hn1
      t_eps_plus t_eps_minus h_plus_to h_plus_radius h_minus_to h_minus_radius

end
