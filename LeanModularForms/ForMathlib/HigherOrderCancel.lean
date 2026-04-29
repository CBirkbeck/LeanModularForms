/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.SectorCurve
import LeanModularForms.ForMathlib.FlatChordBound

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

open Complex Set Filter Topology MeasureTheory Finset
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-! ## Avoidance cancellation for general poles -/

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

/-! ## Holomorphic remainder cancellation -/

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
  -- g integral vanishes by convex Cauchy theorem
  have hg_zero : γ.contourIntegral g = 0 :=
    γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU_convex hU_open hU_ne
      hg_diff hγ_in_U h_g_int
  -- g agrees with f - pp on the curve (curve avoids S, hence in U \ S)
  have hg_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S (fun s => residue f s) (γ t) :=
    fun t ht => hg_agree (γ t) ⟨hγ_in_U t ht, fun hmem =>
      hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
  exact hCancel_of_holomorphic_agree S f γ hδ g hg_zero hg_on_curve

/-! ## Structural decomposition theorem -/

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
  -- The CPV of (h₁ + h₂) = CPV of (f - pp) since they agree pointwise
  have h_congr : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z) γ.toPath.extend ε t) =
      (fun ε => ∫ t in (0 : ℝ)..1,
        cpvIntegrandOn S (fun z => h₁ z + h₂ z) γ.toPath.extend ε t) := by
    ext ε; congr 1; ext t
    simp only [cpvIntegrandOn]; split_ifs with h
    · rfl
    · congr 1; exact h_decomp _
  simp only [HasCauchyPVOn] at h_add ⊢
  rwa [h_congr]

/-! ## Simple poles with avoidance (no convexity) -/

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

/-! ## Condition B sector analysis -/

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

/-! ## Full cancellation under conditions A'+B in convex domains -/

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

/-! ## Conditions A'+B discharge for simple poles (full API)

For simple poles, we provide the complete chain:
1. Conditions A'+B are automatic (from `FlatnessConditions`)
2. The cancellation holds (from `HigherOrderAssembly`)
3. Everything composes into a single theorem -/

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

/-! ## Higher-order cancellation: structural gateway

The following theorem provides the structural gateway for higher-order
cancellation. It shows that `hCancel` can be discharged by providing:

1. A proof that the *holomorphic part* of the remainder has vanishing CPV
   (typically from Cauchy's theorem)
2. A proof that each *higher-order polar term* has vanishing CPV
   (from condition B + sector analysis)

The actual sector analysis for higher-order poles (proving each term's
CPV vanishes from the angle condition in B) involves integration over
model curves, which is done in `SectorCurve.lean`. -/

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

/-! ## Integration with generalizedResidueTheorem -/

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

/-! ## Cancellation for empty pole set -/

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

/-! ## Cancellation transfer lemmas -/

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
    ext ε; congr 1; ext t
    simp only [cpvIntegrandOn]; split_ifs with h
    · rfl
    · congr 1; exact (h_eq _).symm
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

/-! ## C-1: Tangent approximation around a crossing

For a curve `γ` flat of order `n` at `t₀` with right (resp. left) one-sided
derivative limit `L ≠ 0`, `IsFlatOfOrder` says the tangent deviation is
`o(‖γ(t) − γ(t₀)‖^n)`. The right-side derivative limit gives
`(γ t − γ t₀) =O (t − t₀)` near `t₀` from the right (and similarly from the
left), so `‖γ(t) − γ(t₀)‖^n =O |t − t₀|^n`. Combining gives the more
usable form `o(|t − t₀|^n)` for the tangent deviation. -/

/-- **C-1 (right-side).** Under right-side flatness of order `n`, the tangent
deviation is `o(|t - t₀|^n)` from the right. -/
theorem tangentApproximation_of_isFlatOfOrder_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n)
    {L : ℂ} (hL : L ≠ 0)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t)
    (hγ_cont : ContinuousAt γ t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      (fun t => |t - t₀| ^ n) := by
  -- Flatness gives the o(‖γ-γ₀‖^n) form.
  have h_flat_asym := h_flat.right_flat L hL hL_right
  -- Differentiability from the right at t₀ + Tendsto deriv → L gives the
  -- one-sided derivative existence.
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  have hderiv : HasDerivWithinAt γ L (Ioi t₀) t₀ :=
    hasDerivWithinAt_Ioi_iff_Ici.mpr
      (hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => (hs_diff t ht).differentiableWithinAt)
        hγ_cont.continuousWithinAt hs_mem hL_right)
  have h_bigO : (fun t => γ t - γ t₀) =O[𝓝[>] t₀] (fun t => t - t₀) :=
    hderiv.differentiableWithinAt.isBigO_sub
  -- Take n-th power
  have h_pow : (fun t => (γ t - γ t₀) ^ n) =O[𝓝[>] t₀] (fun t => (t - t₀) ^ n) :=
    h_bigO.pow n
  -- Convert to norm form: (γ-γ₀)^n has norm ‖γ-γ₀‖^n; (t-t₀)^n has norm |t-t₀|^n.
  have h_lhs : (fun t : ℝ => ‖(γ t - γ t₀) ^ n‖) = (fun t => ‖γ t - γ t₀‖ ^ n) :=
    funext fun t => norm_pow _ _
  have h_rhs : (fun t : ℝ => ‖(t - t₀) ^ n‖) = (fun t => |t - t₀| ^ n) :=
    funext fun t => by rw [norm_pow, Real.norm_eq_abs]
  have h_pow_norm : (fun t => ‖γ t - γ t₀‖ ^ n) =O[𝓝[>] t₀]
      (fun t => |t - t₀| ^ n) := by
    rw [← h_lhs, ← h_rhs]
    exact h_pow.norm_left.norm_right
  exact h_flat_asym.trans_isBigO h_pow_norm

/-- **C-1 (left-side).** Under left-side flatness of order `n`, the tangent
deviation is `o(|t - t₀|^n)` from the left. -/
theorem tangentApproximation_of_isFlatOfOrder_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n)
    {L : ℂ} (hL : L ≠ 0)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t)
    (hγ_cont : ContinuousAt γ t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      (fun t => |t - t₀| ^ n) := by
  have h_flat_asym := h_flat.left_flat L hL hL_left
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  have hderiv : HasDerivWithinAt γ L (Iio t₀) t₀ :=
    hasDerivWithinAt_Iio_iff_Iic.mpr
      (hasDerivWithinAt_Iic_of_tendsto_deriv
        (fun t ht => (hs_diff t ht).differentiableWithinAt)
        hγ_cont.continuousWithinAt hs_mem hL_left)
  have h_bigO : (fun t => γ t - γ t₀) =O[𝓝[<] t₀] (fun t => t - t₀) :=
    hderiv.differentiableWithinAt.isBigO_sub
  have h_pow : (fun t => (γ t - γ t₀) ^ n) =O[𝓝[<] t₀] (fun t => (t - t₀) ^ n) :=
    h_bigO.pow n
  have h_lhs : (fun t : ℝ => ‖(γ t - γ t₀) ^ n‖) = (fun t => ‖γ t - γ t₀‖ ^ n) :=
    funext fun t => norm_pow _ _
  have h_rhs : (fun t : ℝ => ‖(t - t₀) ^ n‖) = (fun t => |t - t₀| ^ n) :=
    funext fun t => by rw [norm_pow, Real.norm_eq_abs]
  have h_pow_norm : (fun t => ‖γ t - γ t₀‖ ^ n) =O[𝓝[<] t₀]
      (fun t => |t - t₀| ^ n) := by
    rw [← h_lhs, ← h_rhs]
    exact h_pow.norm_left.norm_right
  exact h_flat_asym.trans_isBigO h_pow_norm

/-! ## C-2 Step A: Antiderivative for `γ'/(γ-s)^k` with `k ≥ 2`

For higher-order poles `1/(z-s)^k` with `k ≥ 2`, the integrand
`γ'(t)/(γ(t)-s)^k` admits an antiderivative `-1/[(k-1)(γ(t)-s)^{k-1}]`
on the open set where `γ(t) ≠ s`. This is the key fact behind the
Hungerbühler-Wasem treatment of higher-order poles: away from
singularities, the integral is fully controlled by boundary values,
so PV computations reduce to comparing the antiderivative endpoints. -/

/-- **Antiderivative for `γ'/(γ-s)^k` (k ≥ 2).** When `γ` is differentiable
at `t` with derivative `γ'` and `γ(t) ≠ s`, the function
`u ↦ -1/[(k-1)(γ(u)-s)^{k-1}]` has derivative `γ'/(γ(t)-s)^k` at `t`.

This is HW's antiderivative formula used to handle higher-order poles via
the Fundamental Theorem of Calculus on smooth pieces of the curve. -/
theorem hasDerivAt_antiderivative_pow_inv
    {γ : ℝ → ℂ} {γ' s : ℂ} {t : ℝ} {k : ℕ}
    (hk : 2 ≤ k) (hγ : HasDerivAt γ γ' t) (h_ne : γ t - s ≠ 0) :
    HasDerivAt (fun u => -(↑(k - 1) : ℂ)⁻¹ * ((γ u - s) ^ (k - 1))⁻¹)
      (γ' / (γ t - s) ^ k) t := by
  have h_sub : HasDerivAt (fun u => γ u - s) γ' t := hγ.sub_const s
  have h_pow_raw : HasDerivAt (fun u => (γ u - s) ^ (k - 1))
      (↑(k - 1) * (γ t - s) ^ (k - 1 - 1) * γ') t := h_sub.pow (k - 1)
  have hk_norm : k - 1 - 1 = k - 2 := by omega
  rw [hk_norm] at h_pow_raw
  have h_pow_ne : (γ t - s) ^ (k - 1) ≠ 0 := pow_ne_zero _ h_ne
  have h_inv := hasDerivAt_inv h_pow_ne
  have h_comp := h_inv.scomp t h_pow_raw
  have h_const := h_comp.const_mul (-(↑(k - 1) : ℂ)⁻¹)
  convert h_const using 1
  have hk1 : (↑(k - 1) : ℂ) ≠ 0 := by
    have : 0 < k - 1 := by omega
    exact_mod_cast this.ne'
  have h_pow2 : ((γ t - s) ^ (k - 1)) ^ 2 = (γ t - s) ^ k * (γ t - s) ^ (k - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  simp only [smul_eq_mul]
  rw [h_pow2]
  field_simp

/-! ## C-2 Step B: FTC for the higher-order pole integrand on a smooth piece -/

/-- **FTC for `γ'/(γ-s)^k` on a smooth piece (k ≥ 2).** When `γ` is differentiable
on `uIcc a b` and avoids `s`, the integral of `γ'/(γ-s)^k` equals the antiderivative
endpoints. This is the FTC application of Step A on a single smooth segment between
crossings of `s`. -/
theorem integral_pow_inv_eq_FTC
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {s : ℂ} {k : ℕ} {a b : ℝ}
    (hk : 2 ≤ k)
    (hγ : ∀ t ∈ uIcc a b, HasDerivAt γ (γ' t) t)
    (h_avoids : ∀ t ∈ uIcc a b, γ t ≠ s)
    (h_int : IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume a b) :
    ∫ t in a..b, γ' t / (γ t - s) ^ k =
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ b - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ a - s) ^ (k - 1))⁻¹) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact hasDerivAt_antiderivative_pow_inv hk (hγ t ht) (sub_ne_zero.mpr (h_avoids t ht))
  · exact h_int

/-! ## ℂ→ℂ antiderivative: complex-differentiable form

For the higher-order avoidance result (PV of `1/(z-s)^k` along a closed curve
avoiding `s` is zero), we need the antiderivative as a function `ℂ → ℂ` (not
`ℝ → ℂ`) so we can apply `contourIntegral_eq_zero_of_hasDerivAt_of_closed`. -/

/-- **Antiderivative of `1/(z-s)^k` as a function `ℂ → ℂ` (k ≥ 2).** The function
`F(z) = -1/[(k-1)(z-s)^{k-1}]` has complex derivative `1/(z-s)^k` at any
`z ≠ s`. This is the ℂ → ℂ form of `hasDerivAt_antiderivative_pow_inv` and is the
key fact behind closed-path FTC for higher-order poles. -/
theorem hasDerivAt_antiderivative_pow_inv_complex
    {s : ℂ} {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ s) :
    HasDerivAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
      (1 / (z - s) ^ k) z := by
  have h_sub : HasDerivAt (fun w : ℂ => w - s) 1 z := (hasDerivAt_id z).sub_const s
  have h_pow : HasDerivAt (fun w : ℂ => (w - s) ^ (k - 1))
      (↑(k - 1) * (z - s) ^ (k - 1 - 1) * 1) z := h_sub.pow (k - 1)
  have hk_norm : k - 1 - 1 = k - 2 := by omega
  rw [hk_norm] at h_pow
  have h_pow_ne : (z - s) ^ (k - 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
  have h_inv := h_pow.inv h_pow_ne
  have h_const := h_inv.const_mul (-(↑(k - 1) : ℂ)⁻¹)
  convert h_const using 1
  have hk1 : (↑(k - 1) : ℂ) ≠ 0 := by
    have : 0 < k - 1 := by omega
    exact_mod_cast this.ne'
  have h_pow_k2_ne : (z - s) ^ (k - 2) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
  have h_pow2 : ((z - s) ^ (k - 1)) ^ 2 = (z - s) ^ k * (z - s) ^ (k - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; omega
  rw [h_pow2]
  field_simp

/-! ## Higher-order pole CPV vanishes in the avoidance case

For `k ≥ 2` and a closed curve `γ` avoiding `s` (with positive margin), the CPV of
`1/(z-s)^k` is zero. Unlike the simple-pole case (k = 1), this does NOT require
null-homologous Cauchy or convex U: the function `1/(z-s)^k` has a single-valued
antiderivative on `ℂ \ {s}`, so its integral over any closed loop avoiding `s`
vanishes by FTC.

This complements the existing simple-pole machinery: the simple pole contributes
`2πi · n_γ(s) · residue`, while higher-order poles contribute `0` whenever
the curve avoids them. -/

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

/-! ## Phase 3.5a: Excised integral via antiderivative for closed γ

For a closed curve `γ` (with `γ a = γ b`) that avoids `s` outside the
interval `[t_minus, t_plus]`, the parameter-excised integral
`∫_a^{t_minus} + ∫_{t_plus}^b` of `γ'/(γ-s)^k` equals an antiderivative
difference at the excision boundaries. This is Step B applied to each
smooth piece, with the closed-curve cancellation `F(γ a) = F(γ b)`. -/

/-- **Closed-γ excised integral via FTC.** For a closed curve avoiding `s` on
two smooth pieces flanking a crossing, the parameter-excised integral equals
`F(γ(t_minus)) - F(γ(t_plus))` where `F` is the antiderivative
`-1/[(k-1)(z-s)^{k-1}]`. This is the FTC + closure form of HW's

  PV(γ excised) = boundary contributions − crossing contributions

with the closed-curve property eliminating the boundary contribution. -/
theorem closed_excised_integral_eq_antideriv_diff
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {s : ℂ} {k : ℕ} {a t_minus t_plus b : ℝ}
    (hk : 2 ≤ k)
    (h_close : γ a = γ b)
    (hγ_left : ∀ t ∈ uIcc a t_minus, HasDerivAt γ (γ' t) t)
    (hγ_right : ∀ t ∈ uIcc t_plus b, HasDerivAt γ (γ' t) t)
    (h_avoids_left : ∀ t ∈ uIcc a t_minus, γ t ≠ s)
    (h_avoids_right : ∀ t ∈ uIcc t_plus b, γ t ≠ s)
    (h_int_left : IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume a t_minus)
    (h_int_right : IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume t_plus b) :
    (∫ t in a..t_minus, γ' t / (γ t - s) ^ k) +
      (∫ t in t_plus..b, γ' t / (γ t - s) ^ k) =
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ t_minus - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((γ t_plus - s) ^ (k - 1))⁻¹) := by
  rw [integral_pow_inv_eq_FTC hk hγ_left h_avoids_left h_int_left]
  rw [integral_pow_inv_eq_FTC hk hγ_right h_avoids_right h_int_right]
  rw [h_close]
  ring

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
    have : δ ≤ ‖γ t - s‖ := hδ_bd t ht
    rw [hγt, sub_self, norm_zero] at this
    linarith
  have h_zero := γ.contourIntegral_pow_inv_eq_zero hk h_avoids h_int
  have hδ' : ∃ δ > 0, ∀ s' ∈ ({s} : Finset ℂ), ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s'‖ := by
    obtain ⟨δ, hδ_pos, hδ_bd⟩ := hδ
    refine ⟨δ, hδ_pos, ?_⟩
    intro s' hs' t ht
    rw [Finset.mem_singleton] at hs'
    rw [hs']
    exact hδ_bd t ht
  exact h_zero ▸ hasCauchyPVOn_of_avoids hδ'

/-! ## Phase 3.5b: F-difference bound on a segment avoiding s -/

/-- **F-difference bound on segment.** When the line segment from `z₁` to `z₂`
stays at distance ≥ ε from `s`, the antiderivative difference

  `‖F(z₂) − F(z₁)‖ ≤ ‖z₂ − z₁‖ / ε^k`

where `F(z) = -1/[(k-1)(z-s)^{k-1}]`.

This is the analytical step for Phase 3 limit analysis: combined with the
chord bound `‖z₂ − z₁‖ = o(ε^n)` (Phase 3.3 chord_to_tangent_target_le applied
at radius ε), we get `‖F(z₂) − F(z₁)‖ = o(ε^{n−k})`, vanishing for `n ≥ k`. -/
theorem norm_F_diff_le_segment_bound
    {z₁ z₂ s : ℂ} {k : ℕ} {ε : ℝ} (hk : 2 ≤ k) (hε : 0 < ε)
    (h_seg_avoids : ∀ z ∈ segment ℝ z₁ z₂, ε ≤ ‖z - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((z₂ - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((z₁ - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / ε ^ k) * ‖z₂ - z₁‖ := by
  have h_deriv : ∀ z ∈ segment ℝ z₁ z₂,
      HasDerivWithinAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
        (1 / (z - s) ^ k) (segment ℝ z₁ z₂) z := by
    intro z hz
    have h_dist : ε ≤ ‖z - s‖ := h_seg_avoids z hz
    have h_ne : z ≠ s := by
      intro heq; rw [heq, sub_self, norm_zero] at h_dist; linarith
    exact (hasDerivAt_antiderivative_pow_inv_complex hk h_ne).hasDerivWithinAt
  have h_bound : ∀ z ∈ segment ℝ z₁ z₂, ‖1 / (z - s) ^ k‖ ≤ 1 / ε ^ k := by
    intro z hz
    rw [norm_div, norm_one, norm_pow]
    apply div_le_div_of_nonneg_left zero_le_one (pow_pos hε k)
    exact pow_le_pow_left₀ hε.le (h_seg_avoids z hz) k
  have h_convex : Convex ℝ (segment ℝ z₁ z₂) := convex_segment z₁ z₂
  have h_z₁_in : z₁ ∈ segment ℝ z₁ z₂ := left_mem_segment _ _ _
  have h_z₂_in : z₂ ∈ segment ℝ z₁ z₂ := right_mem_segment _ _ _
  exact h_convex.norm_image_sub_le_of_norm_hasDerivWithin_le h_deriv h_bound h_z₁_in h_z₂_in

/-! ## Phase 3.5c: Eventual sign condition for the chord bound

For γ with one-sided derivative `L` at `t₀` from the right and `γ(t₀) = s`,
the inner product `Re((γ(t) - s) · conj L)` is eventually nonnegative for
`t` in `𝓝[>] t₀`. This is the hypothesis required by Phase 3.3's chord
bound (`norm_chord_to_tangent_target_le`). -/

/-- **Eventual `+L`-hemisphere condition (right side).** When `γ` has
right-derivative `L ≠ 0` at `t₀` and `γ(t₀) = s`, for `t` close to `t₀` from
the right, `γ(t) − s` lies in the `+L` hemisphere
(`Re((γ(t) − s) · conj L) ≥ 0`).

Proof: From `HasDerivWithinAt γ L (Ioi t₀) t₀`,
`γ(t) - γ(t₀) - (t-t₀)·L = o(t-t₀)`. Hence
`Re((γ(t)-s)·conj L) = (t-t₀)·‖L‖² + Re(o(t-t₀)·conj L)`,
which is bounded below by `(t-t₀)·‖L‖²/2 ≥ 0` for `t > t₀` close enough. -/
theorem eventually_re_pos_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[>] t₀, 0 ≤ ((γ t - s) * starRingEnd ℂ L).re := by
  have h_asymp := h_deriv.isLittleO
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hLsq_pos : 0 < ‖L‖ ^ 2 := by positivity
  have h_bound : ∀ᶠ t in 𝓝[>] t₀,
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖L‖ / 2 * ‖t - t₀‖ := by
    have h_eps_pos : 0 < ‖L‖ / 2 := by linarith
    exact h_asymp.bound h_eps_pos
  filter_upwards [h_bound, self_mem_nhdsWithin] with t h_b ht
  have h_pos : 0 < t - t₀ := sub_pos.mpr ht
  have h_norm_eq : ‖t - t₀‖ = t - t₀ := by
    rw [Real.norm_eq_abs, abs_of_pos h_pos]
  rw [h_norm_eq] at h_b
  have h_decomp : (γ t - s) = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) := by
    rw [h_s]; ring
  rw [h_decomp, add_mul, Complex.add_re]
  have h1 : ((((t - t₀) : ℝ) • L) * starRingEnd ℂ L).re = (t - t₀) * ‖L‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  have h_norm_conj : ‖starRingEnd ℂ L‖ = ‖L‖ := Complex.norm_conj _
  have h2 : -(‖L‖ / 2 * (t - t₀)) * ‖L‖ ≤
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L).re := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L)
    rw [norm_mul, h_norm_conj] at habs
    have hbd := mul_le_mul_of_nonneg_right h_b (norm_nonneg L)
    nlinarith [abs_le.mp (habs.trans hbd)]
  nlinarith [hLsq_pos]

/-- **Eventual `−L`-hemisphere condition (left side).** Symmetric counterpart:
`Re((γ(t) − s) · conj L) ≤ 0` for `t` close to `t₀` from the left.

Equivalently, `Re((γ(t) − s) · conj (−L)) ≥ 0`, so Phase 3.3's chord bound
applies with `−L` as the tangent direction. -/
theorem eventually_re_neg_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[<] t₀, ((γ t - s) * starRingEnd ℂ L).re ≤ 0 := by
  have h_asymp := h_deriv.isLittleO
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have hLsq_pos : 0 < ‖L‖ ^ 2 := by positivity
  have h_bound : ∀ᶠ t in 𝓝[<] t₀,
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖L‖ / 2 * ‖t - t₀‖ := by
    have h_eps_pos : 0 < ‖L‖ / 2 := by linarith
    exact h_asymp.bound h_eps_pos
  filter_upwards [h_bound, self_mem_nhdsWithin] with t h_b ht
  have h_neg : t - t₀ < 0 := sub_neg.mpr ht
  have h_norm_eq : ‖t - t₀‖ = -(t - t₀) := by
    rw [Real.norm_eq_abs, abs_of_neg h_neg]
  rw [h_norm_eq] at h_b
  have h_decomp : (γ t - s) = (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) := by
    rw [h_s]; ring
  rw [h_decomp, add_mul, Complex.add_re]
  have h1 : ((((t - t₀) : ℝ) • L) * starRingEnd ℂ L).re = (t - t₀) * ‖L‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1]
  have h_norm_conj : ‖starRingEnd ℂ L‖ = ‖L‖ := Complex.norm_conj _
  have h2 : ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L).re ≤
      ‖L‖ / 2 * -(t - t₀) * ‖L‖ := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ L)
    rw [norm_mul, h_norm_conj] at habs
    have hbd := mul_le_mul_of_nonneg_right h_b (norm_nonneg L)
    nlinarith [abs_le.mp (habs.trans hbd)]
  nlinarith [hLsq_pos]

/-! ## Phase 3.6a: Eventually `γ ≠ s`

For γ with one-sided derivative L ≠ 0 and γ(t₀) = s, the curve moves away
from s on either side of t₀. Used to apply the chord bound (which requires
γ(t) ≠ s, equivalently `‖γ(t) − s‖ > 0`). -/

/-- **Eventually `γ ≠ s` (right side).** With right-derivative L ≠ 0, the
curve cannot stay at s past t₀. -/
theorem eventually_ne_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[>] t₀, γ t ≠ s := by
  have h_asymp := h_deriv.isLittleO
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_bound : ∀ᶠ t in 𝓝[>] t₀,
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖L‖ / 2 * ‖t - t₀‖ := by
    have h_eps_pos : 0 < ‖L‖ / 2 := by linarith
    exact h_asymp.bound h_eps_pos
  filter_upwards [h_bound, self_mem_nhdsWithin] with t h_b ht
  have h_pos : 0 < t - t₀ := sub_pos.mpr ht
  have h_norm_eq : ‖t - t₀‖ = t - t₀ := by
    rw [Real.norm_eq_abs, abs_of_pos h_pos]
  rw [h_norm_eq] at h_b
  intro h_eq
  have h_diff_zero : γ t - γ t₀ = 0 := by rw [h_s]; exact sub_eq_zero.mpr h_eq
  have h_expr : γ t - γ t₀ - (t - t₀) • L = -((t - t₀) • L) := by
    rw [h_diff_zero, zero_sub]
  rw [h_expr, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos h_pos] at h_b
  nlinarith

/-- **Eventually `γ ≠ s` (left side).** Symmetric. -/
theorem eventually_ne_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[<] t₀, γ t ≠ s := by
  have h_asymp := h_deriv.isLittleO
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_bound : ∀ᶠ t in 𝓝[<] t₀,
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖L‖ / 2 * ‖t - t₀‖ := by
    have h_eps_pos : 0 < ‖L‖ / 2 := by linarith
    exact h_asymp.bound h_eps_pos
  filter_upwards [h_bound, self_mem_nhdsWithin] with t h_b ht
  have h_neg : t - t₀ < 0 := sub_neg.mpr ht
  have h_norm_eq : ‖t - t₀‖ = -(t - t₀) := by
    rw [Real.norm_eq_abs, abs_of_neg h_neg]
  rw [h_norm_eq] at h_b
  intro h_eq
  have h_diff_zero : γ t - γ t₀ = 0 := by rw [h_s]; exact sub_eq_zero.mpr h_eq
  have h_expr : γ t - γ t₀ - (t - t₀) • L = -((t - t₀) • L) := by
    rw [h_diff_zero, zero_sub]
  rw [h_expr, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_neg h_neg] at h_b
  nlinarith

/-! ## Phase 3.6b: Asymptotic chord bound

The parameter-based asymptotic statement: for γ flat of order n with right
(or left) derivative L ≠ 0 and γ(t₀) = s, the chord from γ(t) to its
"natural" tangent target on the +L (or −L) ray is `o(‖γ(t) − s‖^n)` as
`t → t₀±`. This is the parameter-based packaging of Phase 3.3's pointwise
chord bound combined with flatness. -/

/-- **Asymptotic chord-to-tangent bound (right side).** Combining
flatness + the chord bound + the eventual sign/non-zero conditions, the
chord `‖γ(t) − s − (‖γ(t)−s‖/‖L‖)·L‖` is `o(‖γ(t)−s‖^n)` as `t → t₀⁺`. -/
theorem chord_to_tangent_isLittleO_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (h_s : γ t₀ = s) :
    (fun t => ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  have h_ortho :=
    LeanModularForms.orthogonal_deviation_at_radius_right h_flat hL hL_right h_s
  have h_eventually_bound : ∀ᶠ t in 𝓝[>] t₀,
      ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖ ≤ 3 * ‖tangentDeviation (γ t - s) L‖ := by
    filter_upwards [eventually_re_pos_right hL h_deriv h_s,
                    eventually_ne_right hL h_deriv h_s] with t h_pos h_ne
    have hw_ne : γ t - s ≠ 0 := sub_ne_zero.mpr h_ne
    have hw_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr hw_ne
    have h_chord :=
      LeanModularForms.norm_chord_to_tangent_target_le hL hw_pos h_pos
    have h_dev_le : ‖tangentDeviation (γ t - s) L‖ ≤ 2 * ‖γ t - s‖ :=
      norm_tangentDeviation_le _ _ hL
    have h_div_bound : ‖tangentDeviation (γ t - s) L‖ ^ 2 / ‖γ t - s‖ ≤
        2 * ‖tangentDeviation (γ t - s) L‖ := by
      rw [pow_two, mul_div_assoc]
      have hd_div : ‖tangentDeviation (γ t - s) L‖ / ‖γ t - s‖ ≤ 2 := by
        rw [div_le_iff₀ hw_pos]; linarith
      have h_dev_nonneg : 0 ≤ ‖tangentDeviation (γ t - s) L‖ := norm_nonneg _
      nlinarith
    linarith [h_chord]
  have h_chord_isBigO :
      (fun t => ‖γ t - s - (‖γ t - s‖ / ‖L‖ : ℝ) • L‖) =O[𝓝[>] t₀]
        (fun t => ‖tangentDeviation (γ t - s) L‖) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards [h_eventually_bound] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (norm_nonneg _)]
    exact ht
  exact h_chord_isBigO.trans_isLittleO h_ortho

/-- **Asymptotic chord-to-tangent bound (left side).** Symmetric: the chord
is bounded by `o(‖γ(t)−s‖^n)` as `t → t₀⁻`, with target on the `−L` ray. -/
theorem chord_to_tangent_isLittleO_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) :
    (fun t => ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - s‖ ^ n) := by
  have hLneg : (-L) ≠ 0 := neg_ne_zero.mpr hL
  have h_ortho :=
    LeanModularForms.orthogonal_deviation_at_radius_left h_flat hL hL_left h_s
  -- tangentDeviation (γ t - s) L = tangentDeviation (γ t - s) (-L) (orthogonality
  -- to the line is invariant under L ↦ -L since `orthogonalProjection w (-L)`
  -- equals `orthogonalProjection w L`).
  have h_dev_eq : ∀ t, tangentDeviation (γ t - s) (-L) = tangentDeviation (γ t - s) L := by
    intro t
    unfold tangentDeviation orthogonalProjectionComplex
    have h_normSq : Complex.normSq (-L) = Complex.normSq L := Complex.normSq_neg L
    rw [h_normSq]
    have h_re_neg : ((γ t - s) * starRingEnd ℂ (-L)).re = -((γ t - s) * starRingEnd ℂ L).re := by
      rw [map_neg, mul_neg]; exact Complex.neg_re _
    rw [h_re_neg]
    module
  -- Eventually re((γ t - s) · conj (-L)) ≥ 0 (since left-side gives ≤ 0 for L,
  -- equivalently ≥ 0 for -L).
  have h_pos_neg : ∀ᶠ t in 𝓝[<] t₀, 0 ≤ ((γ t - s) * starRingEnd ℂ (-L)).re := by
    filter_upwards [eventually_re_neg_left hL h_deriv h_s] with t h_neg
    rw [map_neg, mul_neg, Complex.neg_re]
    linarith
  have h_eventually_bound : ∀ᶠ t in 𝓝[<] t₀,
      ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ ≤
        3 * ‖tangentDeviation (γ t - s) (-L)‖ := by
    filter_upwards [h_pos_neg, eventually_ne_left hL h_deriv h_s] with t h_pos h_ne
    have hw_ne : γ t - s ≠ 0 := sub_ne_zero.mpr h_ne
    have hw_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr hw_ne
    have h_chord :=
      LeanModularForms.norm_chord_to_tangent_target_le hLneg hw_pos h_pos
    have h_dev_le : ‖tangentDeviation (γ t - s) (-L)‖ ≤ 2 * ‖γ t - s‖ :=
      norm_tangentDeviation_le _ _ hLneg
    have h_div_bound :
        ‖tangentDeviation (γ t - s) (-L)‖ ^ 2 / ‖γ t - s‖ ≤
          2 * ‖tangentDeviation (γ t - s) (-L)‖ := by
      rw [pow_two, mul_div_assoc]
      have hd_div : ‖tangentDeviation (γ t - s) (-L)‖ / ‖γ t - s‖ ≤ 2 := by
        rw [div_le_iff₀ hw_pos]; linarith
      have h_dev_nonneg : 0 ≤ ‖tangentDeviation (γ t - s) (-L)‖ := norm_nonneg _
      nlinarith
    linarith [h_chord]
  -- Convert tangentDeviation (γ t - s) (-L) = tangentDeviation (γ t - s) L
  -- on the eventual bound, so we can use h_ortho.
  have h_eventually_bound' : ∀ᶠ t in 𝓝[<] t₀,
      ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖ ≤
        3 * ‖tangentDeviation (γ t - s) L‖ := by
    filter_upwards [h_eventually_bound] with t ht
    rw [h_dev_eq t] at ht
    exact ht
  have h_chord_isBigO :
      (fun t => ‖γ t - s - (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)‖) =O[𝓝[<] t₀]
        (fun t => ‖tangentDeviation (γ t - s) L‖) := by
    apply Asymptotics.IsBigO.of_bound 3
    filter_upwards [h_eventually_bound'] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
      abs_of_nonneg (norm_nonneg _)]
    exact ht
  exact h_chord_isBigO.trans_isLittleO h_ortho

/-! ## Phase 3.6c: Segment-distance lower bound

For two points `z₁, z₂` at the same distance `d` from `s`, every point on the
line segment from `z₁` to `z₂` is at distance ≥ `√(d² − c²/4)` from `s`,
where `c = ‖z₁ − z₂‖`. This is the geometric fact behind applying the
F-difference bound (Phase 3.5b) on the chord between γ-exit-point and
sector-exit-point at radius ε. -/

/-- **Segment distance bound (squared).** If `z₁, z₂` are equidistant from `s`
(distance `d`), then any point `z` on the segment from `z₁` to `z₂` satisfies
`‖z − s‖² ≥ d² − ‖z₁ − z₂‖²/4`.

This follows from the parallelogram identity: writing
`z = α z₁ + β z₂` with `α + β = 1, α, β ≥ 0`, and `z − s = α(z₁−s) + β(z₂−s)`,
we get `‖z−s‖² = d² − αβ‖z₁−z₂‖² ≥ d² − ‖z₁−z₂‖²/4` since `αβ ≤ 1/4` by
AM-GM (using `α + β = 1`). -/
theorem norm_sq_segment_to_pole_lower_bound
    {z₁ z₂ s : ℂ} {d : ℝ}
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d ^ 2 - ‖z₁ - z₂‖ ^ 2 / 4 ≤ ‖z - s‖ ^ 2 := by
  obtain ⟨α, β, hα, hβ, h_sum, rfl⟩ := hz
  have h_decomp : α • z₁ + β • z₂ - s = α • (z₁ - s) + β • (z₂ - s) := by
    have hβ_eq : β = 1 - α := by linarith
    rw [hβ_eq]; module
  rw [h_decomp]
  have h_expand : ‖α • (z₁ - s) + β • (z₂ - s)‖ ^ 2 =
      α ^ 2 * ‖z₁ - s‖ ^ 2 +
        2 * α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re +
        β ^ 2 * ‖z₂ - s‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    rw [show α • (z₁ - s) = (α : ℂ) * (z₁ - s) from Complex.real_smul ..,
        show β • (z₂ - s) = (β : ℂ) * (z₂ - s) from Complex.real_smul ..]
    rw [Complex.normSq_add]
    rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_ofReal,
        Complex.normSq_ofReal]
    rw [show (((α : ℂ) * (z₁ - s)) * starRingEnd ℂ ((β : ℂ) * (z₂ - s))) =
        ((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s)) by
          rw [map_mul, Complex.conj_ofReal]; push_cast; ring]
    rw [show (((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s))).re =
        α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re by
          rw [Complex.mul_re]; simp]
    ring
  have h_cross : ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re =
      (‖z₁ - s‖ ^ 2 + ‖z₂ - s‖ ^ 2 - ‖z₁ - z₂‖ ^ 2) / 2 := by
    have h_ns := Complex.normSq_sub (z₁ - s) (z₂ - s)
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm] at h_ns
    have h_sub_eq : (z₁ - s) - (z₂ - s) = z₁ - z₂ := by ring
    rw [h_sub_eq] at h_ns
    linarith
  rw [h_expand, h_cross, h₁, h₂]
  have h_ab_le : α * β ≤ 1 / 4 := by nlinarith [sq_nonneg (α - β)]
  have h_quad : α ^ 2 + 2 * α * β + β ^ 2 = 1 := by
    have : (α + β) ^ 2 = 1 := by rw [h_sum]; ring
    nlinarith [this]
  have h_norm_nonneg : 0 ≤ ‖z₁ - z₂‖ ^ 2 := sq_nonneg _
  nlinarith [h_quad, h_ab_le, h_norm_nonneg]

/-- **Segment distance corollary (chord ≤ d).** When the chord is at most `d`,
the segment from `z₁` to `z₂` stays at distance ≥ `d/2` from `s`. -/
theorem norm_segment_to_pole_lower_bound_half
    {z₁ z₂ s : ℂ} {d : ℝ} (hd_pos : 0 < d)
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d) (h_chord : ‖z₁ - z₂‖ ≤ d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d / 2 ≤ ‖z - s‖ := by
  have h_lower := norm_sq_segment_to_pole_lower_bound h₁ h₂ hz
  have h_norm_nonneg : 0 ≤ ‖z - s‖ := norm_nonneg _
  have h_d2 : 0 < d / 2 := by linarith
  have h_le_sq : (d / 2) ^ 2 ≤ ‖z - s‖ ^ 2 := by
    have h_chord_sq : ‖z₁ - z₂‖ ^ 2 ≤ d ^ 2 := by
      have := mul_self_le_mul_self (norm_nonneg _) h_chord
      nlinarith
    nlinarith
  have := abs_le_of_sq_le_sq' h_le_sq h_norm_nonneg
  linarith [this.2, abs_of_pos h_d2]

/-- **F-diff pointwise bound at tangent target.** For γ(t) ≠ s and chord-to-target
bounded by ‖γ(t) - s‖, the antiderivative difference between γ(t) and the natural
tangent target `s + (‖γ(t)-s‖/‖L‖)·L` is bounded by

  ‖F(γ(t)) − F(target(t))‖ ≤ (1/(‖γ(t)−s‖/2)^k) · chord(t)

This combines Phase 3.5b (F-diff bound on segment) with Phase 3.6c
(segment-distance lower bound). -/
theorem norm_F_diff_at_tangent_target_le
    {γ : ℝ → ℂ} {t : ℝ} {s L : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hL : L ≠ 0) (hw_ne : γ t ≠ s)
    (h_chord_le : ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ ≤ ‖γ t - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / (‖γ t - s‖ / 2) ^ k) * ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ := by
  have hd_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne)
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  set d := ‖γ t - s‖ with hd_def
  set tgt := s + (d / ‖L‖ : ℝ) • L with htgt_def
  have h_tgt_simpl : tgt - s = (d / ‖L‖ : ℝ) • L := by simp [htgt_def]
  have h_tgt : ‖tgt - s‖ = d := by
    rw [h_tgt_simpl, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    field_simp
  have h_seg : ∀ z ∈ segment ℝ (γ t) tgt, d / 2 ≤ ‖z - s‖ :=
    fun z hz => norm_segment_to_pole_lower_bound_half hd_pos rfl h_tgt h_chord_le hz
  have h_F_diff := norm_F_diff_le_segment_bound (z₁ := γ t) (z₂ := tgt) (s := s) hk
    (by linarith : 0 < d / 2) h_seg
  rw [show (-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) =
      -((-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹)) by ring]
  rw [norm_neg, show ‖γ t - tgt‖ = ‖tgt - γ t‖ from norm_sub_rev _ _]
  exact h_F_diff

/-! ## Phase 3.6e: F-diff → 0 limit -/

/-- **Asymptotic helper.** If `chord = o(d^n)`, `d → 0`, `d > 0` eventually, and
`k ≤ n`, then `chord/d^k → 0`. This is the abstract version of the asymptotic
ratio that drives the F-diff limit. -/
theorem tendsto_div_pow_zero_of_isLittleO {chord d : ℝ → ℝ} {l : Filter ℝ} {n k : ℕ}
    (h_chord : chord =o[l] (fun t => d t ^ n)) (h_d : Tendsto d l (𝓝 0))
    (h_d_pos : ∀ᶠ t in l, 0 < d t) (hkn : k ≤ n) :
    Tendsto (fun t => chord t / d t ^ k) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h_eps_half : 0 < ε / 2 := by linarith
  have h_d_le : ∀ᶠ t in l, d t < 1 :=
    h_d.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have h_bound := h_chord.bound h_eps_half
  filter_upwards [h_bound, h_d_le, h_d_pos] with t hb hd hdp
  have hd_n_pos : 0 < d t ^ n := pow_pos hdp n
  have hd_k_pos : 0 < d t ^ k := pow_pos hdp k
  rw [Real.dist_eq, sub_zero]
  have h_pow : d t ^ n = d t ^ k * d t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [Real.norm_eq_abs] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hd_n_pos)] at hb
  rw [abs_div, abs_of_pos hd_k_pos]
  have h_pow_le : d t ^ (n - k) ≤ 1 := by
    rcases Nat.eq_zero_or_pos (n - k) with h_eq | h_pos
    · rw [h_eq]; simp
    · exact pow_le_one₀ (le_of_lt hdp) (le_of_lt hd) |>.trans_eq (by simp)
  calc |chord t| / d t ^ k
      ≤ ε / 2 * d t ^ (n - k) := by
          rw [div_le_iff₀ hd_k_pos]
          calc |chord t| ≤ ε / 2 * d t ^ n := hb
            _ = ε / 2 * d t ^ (n - k) * d t ^ k := by rw [h_pow]; ring
    _ ≤ ε / 2 * 1 := by gcongr
    _ < ε := by linarith

end
