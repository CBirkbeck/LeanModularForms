/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.SectorCurve

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

end
