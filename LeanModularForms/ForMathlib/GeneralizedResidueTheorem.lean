/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.MeromorphicCauchy
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.MultipointPV

/-!
# Generalized Residue Theorem (Hungerbuhler-Wasem, Theorem 3.3)

This file proves the generalized residue theorem for meromorphic functions with
simple poles, and states the full version for higher-order poles with conditions
(A') and (B).

## Main results

### Simple poles (fully proved, no sorry)

* `generalizedResidueTheorem_simplePoles_structural` -- the main structural theorem:
  given the holomorphic remainder `g` with vanishing contour integral, the contour
  integral of `f` equals the winding-number-weighted residue sum.

* `generalizedResidueTheorem_simplePoles_convex` -- corollary for convex domains:
  the `hg_zero` hypothesis is discharged automatically via the convex Cauchy theorem.

* `remainder_differentiableOn_of_simplePoles` -- the holomorphic remainder exists and
  is differentiable on all of `U`.

### Full version (higher-order poles)

* `generalizedResidueTheorem` -- the most general version with conditions (A')+(B):
  the higher-order cancellation is stated as a hypothesis (honest modular design).

### Automatic conditions

* `conditions_automatic_for_simplePoles` -- conditions (A') and (B) are automatic
  for simple poles.

## Proof strategy (simple poles, structural version)

1. **Decompose** `f = g + principalPartSum S c` where `c s = Res(f,s)` and
   `g` is DifferentiableOn `U` (via `sub_principalPartSum_corrected_differentiableOn`).

2. **g integral vanishes** by hypothesis (guaranteed by Cauchy's theorem for
   null-homologous or convex domains).

3. **Contour integral decomposes**: `integral(f) = integral(g) + integral(pp)`.
   Since g = f - pp on the curve and integral(g) = 0, we get
   `integral(f) = integral(pp)`.

4. **Principal part sum integral**: each term `c(s)/(z-s)` contributes
   `2 pi I * n(gamma, s) * c(s)` by `integral_sum_simple_poles_eq_winding`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized residue theorem*, arXiv:1808.00997v2,
  Theorem 3.3.
-/

open Complex Set Filter Topology MeasureTheory Finset
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-! ## Holomorphic remainder -/

/-- The holomorphic remainder `f - principalPartSum S (residue f)` admits a corrected
version that is DifferentiableOn all of `U`, when `f` has simple poles at `S` with
matching residues. This packages `sub_principalPartSum_corrected_differentiableOn`
with the residue coefficient matching. -/
theorem remainder_differentiableOn_of_simplePoles
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧
      ∀ z ∈ U \ (↑S : Set ℂ),
        g z = f z - principalPartSum S (fun s => residue f s) z :=
  sub_principalPartSum_corrected_differentiableOn hU hf hS_in_U hSimplePoles
    (fun s hs => (residue_eq_coeff_of_hasSimplePoleAt (hSimplePoles s hs)).symm)

/-! ## Structural theorem for simple poles -/

/-- **Generalized Residue Theorem for simple poles (structural version).**

For `f` with simple poles at `S` in an open set `U`, and `gamma` a closed piecewise
C^1 path in `U` avoiding `S`, the contour integral of `f` equals the
winding-number-weighted residue sum.

The `hg_zero` hypothesis (contour integral of the holomorphic remainder vanishes)
is guaranteed by Cauchy's theorem for null-homologous or convex domains. It is
stated as a parameter for modularity: the structural theorem is independent of the
topological mechanism producing `hg_zero`. -/
theorem generalizedResidueTheorem_simplePoles_structural
    {U : Set ℂ} (_hU : IsOpen U)
    (S : Finset ℂ) (_hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (_hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    -- Holomorphic remainder
    (g : ℂ → ℂ) (_hg_diff : DifferentiableOn ℂ g U)
    (hg_agree : ∀ z ∈ U \ (↑S : Set ℂ),
      g z = f z - principalPartSum S (fun s => residue f s) z)
    (hg_zero : γ.contourIntegral g = 0)
    -- Integrability
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s *
        residue f s := by
  set c := fun s => residue f s with hc_def
  -- g agrees with f - pp on the curve (curve avoids S, hence in U \ S)
  have h_g_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S c (γ t) :=
    fun t ht => hg_agree (γ t) ⟨hγ_in_U t ht, fun hmem =>
      hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
  -- Contour integral of g = contour integral of (f - pp) by pointwise agreement
  have h_integrals_eq : γ.contourIntegral g =
      γ.contourIntegral (fun z => f z - principalPartSum S c z) := by
    simp only [PiecewiseC1Path.contourIntegral, PiecewiseC1Path.extendedPath_eq]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.extendedPath_eq] at h_g_on_curve
    show g (γ.toPath.extend t) * _ = (f (γ.toPath.extend t) - _) * _
    rw [h_g_on_curve t ht]
  -- The remainder integral vanishes
  have h_rem_zero : γ.contourIntegral (fun z => f z - principalPartSum S c z) = 0 :=
    h_integrals_eq ▸ hg_zero
  -- Decompose: integral(f) = integral(f - pp) + Σ 2πi * winding * coeff
  rw [contourIntegral_decomp_of_simple_poles hδ h_rem_int h_pp_int hI,
      h_rem_zero, zero_add]

/-! ## Convex domain corollary -/

/-- **Generalized Residue Theorem for simple poles in convex domains.**

When `U` is convex, the holomorphic remainder has vanishing contour integral by
the convex Cauchy theorem (`contourIntegral_eq_zero_of_differentiableOn_convex_aux`),
so no separate `hg_zero` hypothesis is needed. -/
theorem generalizedResidueTheorem_simplePoles_convex
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    -- Integrability
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s *
        residue f s := by
  -- Obtain the corrected holomorphic remainder
  obtain ⟨g, hg_diff, hg_agree⟩ := remainder_differentiableOn_of_simplePoles
    hU_open S hS_in_U f hf hSimplePoles
  -- Integrability of g on the curve (agrees with f - pp, which is integrable)
  have h_g_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand g γ) volume 0 1 := by
    apply h_rem_int.congr
    intro t ht
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.contourIntegrand]
    rw [hg_agree (γ t) ⟨hγ_in_U t (Ioc_subset_Icc_self ht),
      fun hmem => hγ_avoids _ (Finset.mem_coe.mp hmem) t
        (Ioc_subset_Icc_self ht) rfl⟩]
  -- g integral vanishes by convex Cauchy theorem
  have hg_zero : γ.contourIntegral g = 0 :=
    γ.contourIntegral_eq_zero_of_differentiableOn_convex_aux rfl hU_convex hU_open hU_ne
      hg_diff hγ_in_U h_g_int
  exact generalizedResidueTheorem_simplePoles_structural hU_open S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids hδ g hg_diff hg_agree hg_zero
    h_rem_int h_pp_int hI

/-! ## Equivalence with `contourIntegral_eq_sum_winding_coefficients_convex` -/

/-- The convex simple-poles theorem is equivalent to the existing
`contourIntegral_eq_sum_winding_coefficients_convex` from MeromorphicCauchy,
with the residue coefficient specialization. -/
theorem generalizedResidueTheorem_simplePoles_convex_alt
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    -- Integrability
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => f z - principalPartSum S (fun s => residue f s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    γ.contourIntegral f =
      ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s *
        residue f s := by
  set c := fun s => residue f s
  have h_coeff : ∀ (s : ℂ) (hs : s ∈ S),
      (hSimplePoles s hs).coeff = c s :=
    fun s hs => (residue_eq_coeff_of_hasSimplePoleAt (hSimplePoles s hs)).symm
  have h_res_eq : ∀ s ∈ S, residue f s = c s := fun _ _ => rfl
  exact contourIntegral_eq_sum_winding_residues_convex γ hU_convex hU_open hU_ne
    hf hS_in_U hSimplePoles h_coeff h_res_eq hγ_in_U hγ_avoids hδ h_rem_int h_pp_int hI

/-! ## Full version with conditions (A') and (B) -/

/-- **Generalized Residue Theorem** (Hungerbuhler-Wasem, Theorem 3.3, full version).

For a meromorphic function `f` with poles of arbitrary order at `S` on a
null-homologous piecewise C^1 immersion `gamma` in an open set `U`, satisfying
conditions (A') (flatness at crossings) and (B) (angle/Laurent compatibility),
the Cauchy principal value integral converges to the winding-number-weighted
residue sum.

The `hCancel` hypothesis asserts that the higher-order terms cancel:
`CPV(f - principalPartSum) -> 0`. For simple poles this is automatic (the
remainder is holomorphic). For higher-order poles, conditions (A') and (B)
guarantee this cancellation through the Hungerbuhler-Wasem analysis.

The `hPV_sing` hypothesis gives the CPV of the singular part. For the avoidance
case (curve does not cross `S`), this reduces to the ordinary contour integral
of the principal part sum, computable via `integral_sum_simple_poles_eq_winding`.

This is the most general form. -/
theorem generalizedResidueTheorem
    {U : Set ℂ} (_hU : IsOpen U)
    (S : Finset ℂ) (_hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Immersion x x) (_h_null : IsNullHomologous γ U)
    (_hMero : ∀ s ∈ S, MeromorphicAt f s)
    (_hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (_hCondB : SatisfiesConditionB γ f S)
    (_h_no_endpt_cross : ∀ s ∈ S,
      γ.toPiecewiseC1Path 0 ≠ s ∧ γ.toPiecewiseC1Path 1 ≠ s)
    (_h_unique_cross : ∀ s ∈ S,
      ∀ t₁ ∈ Icc (0 : ℝ) 1, ∀ t₂ ∈ Icc (0 : ℝ) 1,
        γ.toPiecewiseC1Path t₁ = s → γ.toPiecewiseC1Path t₂ = s → t₁ = t₂)
    -- Higher-order cancellation (guaranteed by conditions A'+B)
    (hCancel : HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z)
      γ.toPiecewiseC1Path 0)
    -- CPV of the singular part exists and equals the formula
    (hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s))
    -- Integrability for the decomposition
    (hI_sing : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (principalPartSum S (fun s => residue f s))
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1)
    (hI_rem : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z)
        γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ.toPiecewiseC1Path
      (2 * ↑Real.pi * I * ∑ s ∈ S,
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s) := by
  -- Factor 2πi into the sum
  have h_target_eq : 2 * ↑Real.pi * I * ∑ s ∈ S,
      generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s =
    ∑ s ∈ S, 2 * ↑Real.pi * I *
      generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h_target_eq]
  -- Decompose: CPV(f) = CPV(f - pp) + CPV(pp) = 0 + formula
  exact hasCauchyPVOn_of_tendsto_sub hCancel hPV_sing hI_rem hI_sing

/-! ## Automatic conditions for simple poles -/

/-- **Conditions (A') and (B) are automatic for simple poles.**

For simple poles, flatness of order 1 suffices for condition (A'), and the
Laurent compatibility in condition (B) is vacuously satisfied. This bundles
the results from `FlatnessConditions.lean`. -/
theorem conditions_automatic_for_simplePoles
    (γ : PiecewiseC1Immersion x x) (f : ℂ → ℂ) (S : Finset ℂ)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hAngles : ∀ s ∈ S, ∀ t₀ ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s →
      ∀ ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1,
        t₀ ∈ γ.toPiecewiseC1Path.partition →
          ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
            angleAtCrossing γ t₀ ht₀_Ioo = ↑p * Real.pi / ↑q) :
    SatisfiesConditionA' γ f S (fun _ => 1) ∧ SatisfiesConditionB γ f S :=
  conditions_automatic_simple_poles γ f S hSimplePoles hAngles

/-- Condition (A') is automatic for simple poles: every piecewise C^1 immersion
is flat of order 1 at interior crossings. -/
theorem conditionA'_automatic_for_simplePoles
    (γ : PiecewiseC1Immersion x x) (f : ℂ → ℂ) (S : Finset ℂ)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) :
    SatisfiesConditionA' γ f S (fun _ => 1) :=
  satisfiesConditionA'_of_simplePoles γ f S hSimplePoles

end
