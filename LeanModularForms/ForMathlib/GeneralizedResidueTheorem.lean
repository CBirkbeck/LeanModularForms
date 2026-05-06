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
    (g : ℂ → ℂ) (_hg_diff : DifferentiableOn ℂ g U)
    (hg_agree : ∀ z ∈ U \ (↑S : Set ℂ),
      g z = f z - principalPartSum S (fun s => residue f s) z)
    (hg_zero : γ.contourIntegral g = 0)
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
  have h_g_on_curve : ∀ t ∈ Icc (0 : ℝ) 1,
      g (γ t) = f (γ t) - principalPartSum S c (γ t) :=
    fun t ht => hg_agree (γ t) ⟨hγ_in_U t ht, fun hmem =>
      hγ_avoids _ (Finset.mem_coe.mp hmem) t ht rfl⟩
  have h_integrals_eq : γ.contourIntegral g =
      γ.contourIntegral (fun z => f z - principalPartSum S c z) := by
    simp only [PiecewiseC1Path.contourIntegral, PiecewiseC1Path.extendedPath_eq]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.extendedPath_eq] at h_g_on_curve
    change g (γ.toPath.extend t) * _ = (f (γ.toPath.extend t) - _) * _
    rw [h_g_on_curve t ht]
  have h_rem_zero : γ.contourIntegral (fun z => f z - principalPartSum S c z) = 0 :=
    h_integrals_eq ▸ hg_zero
  rw [contourIntegral_decomp_of_simple_poles hδ h_rem_int h_pp_int hI, h_rem_zero, zero_add]

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
  obtain ⟨g, hg_diff, hg_agree⟩ := remainder_differentiableOn_of_simplePoles
    hU_open S hS_in_U f hf hSimplePoles
  have h_g_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand g γ) volume 0 1 := by
    apply h_rem_int.congr
    intro t ht
    rw [uIoc_of_le (zero_le_one' ℝ)] at ht
    simp only [PiecewiseC1Path.contourIntegrand]
    rw [hg_agree (γ t) ⟨hγ_in_U t (Ioc_subset_Icc_self ht),
      fun hmem => hγ_avoids _ (Finset.mem_coe.mp hmem) t
        (Ioc_subset_Icc_self ht) rfl⟩]
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

This is the most general form.

## Status of oracle hypotheses

**Simple poles case (fully closed):** see
`hasCauchyPVOn_simplePoles_convex_closed` in `HigherOrderAssembly.lean`.
For simple poles in a convex domain with avoidance, no oracle hypotheses
are needed — they are all discharged internally:
* `hI_sing` / `hI_rem` are derived from continuity of `f` on `U \ S`
  via `contourIntegrand_intervalIntegrable_of_continuousOn`.
* `hPV_sing` is derived via `hPV_sing_of_avoids`.
* `hCancel` is derived via `hCancel_of_simplePoles_convex` using
  `contourIntegral_eq_zero_of_differentiableOn_convex_aux`.

**Simple poles, null-homologous case (fully closed for convex U):** see
`generalizedResidueTheorem_simplePoles_nullHomologous_closed` in
`HigherOrderAssembly.lean`. For convex bounded open `U` with γ Lipschitz,
no oracle hypotheses are needed — `hCancel` is discharged via the Dixon
mechanism (`dixonFunction_eq_zero_of_nullHomologous_convex_full`) applied
to the holomorphic twist `g(z) = (z − w₀) · (f − pp)(z)` for `w₀ ∈ U`
(supplied by A-2). The Dixon-zero hypothesis `h_winding_zero_near` is in
turn discharged by W-5
(`IsNullHomologous.winding_zero_nhds_of_not_mem_of_closed`) using the
continuous arg lift + integer-valued winding chain in
`ForMathlib/WindingArgDiff.lean`. Non-convex `U` is also handled: the
non-convex `dixonFunction_eq_zero_of_nullHomologous_open_full` (built on
`continuousOn_dslope_prod_open` and `dixonH1_differentiableOn_of_regular_open_full`)
discharges the same Dixon-zero oracle without requiring `Convex ℝ U`.

**Higher-order poles case (pending):** the A'/B closure via sector
curves and Laurent compatibility is the genuine remaining work.
Applies only to poles of order > 1; not needed for the valence formula. -/
theorem generalizedResidueTheorem
    {U : Set ℂ} (_hU : IsOpen U)
    (S : Finset ℂ) (_hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (_hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PwC1Immersion x x) (_h_null : IsNullHomologous γ U)
    (_hMero : ∀ s ∈ S, MeromorphicAt f s)
    (_hCondA : SatisfiesConditionA' γ f S (fun s => poleOrderAt f s))
    (_hCondB : SatisfiesConditionB γ f S)
    (hCancel : HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z)
      γ.toPiecewiseC1Path 0)
    (hPV_sing : HasCauchyPVOn S
      (principalPartSum S (fun s => residue f s))
      γ.toPiecewiseC1Path
      (∑ s ∈ S, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s))
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
  have h_target_eq : 2 * ↑Real.pi * I * ∑ s ∈ S,
      generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s =
    ∑ s ∈ S, 2 * ↑Real.pi * I *
      generalizedWindingNumber γ.toPiecewiseC1Path s * residue f s := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [h_target_eq]
  exact hasCauchyPVOn_of_tendsto_sub hCancel hPV_sing hI_rem hI_sing

/-! ## CPV version (avoidance case) -/

/-- **Generalized Residue Theorem, CPV form (simple poles, convex domain, avoidance).**

When `γ` avoids all poles `S`, the multi-point Cauchy principal value coincides with
the ordinary contour integral, and the classical residue theorem on a convex domain
gives the winding-number-weighted residue sum as the value.

This is the `HasCauchyPVOn` variant of `generalizedResidueTheorem_simplePoles_convex`,
suitable for applications where the CPV predicate is the desired output. -/
theorem generalizedResidueTheorem_simplePoles_convex_CPV
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
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S (fun s => residue f s)) γ) volume 0 1)
    (hI : ∀ s ∈ S, IntervalIntegrable
      (fun t => (residue f s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s *
        residue f s) := by
  have h_contour := generalizedResidueTheorem_simplePoles_convex
    hU_convex hU_open hU_ne S hS_in_U f hf γ hSimplePoles
    hγ_in_U hγ_avoids hδ h_rem_int h_pp_int hI
  exact h_contour ▸ hasCauchyPVOn_of_avoids hδ

/-- **Generalized Residue Theorem, CPV form (simple poles, avoidance,
abstract Cauchy-vanishing).**

Factored form of the residue theorem that takes the holomorphic remainder's
contour-integral vanishing as a hypothesis. Callers supply this from the
ambient topology (convex, null-homologous via Dixon, etc.).

This is the CPV analogue of `generalizedResidueTheorem_simplePoles_structural`. -/
theorem generalizedResidueTheorem_simplePoles_CPV_structural
    {U : Set ℂ} (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ ↑S))
    (γ : PiecewiseC1Path x x)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (g : ℂ → ℂ) (hg_diff : DifferentiableOn ℂ g U)
    (hg_agree : ∀ z ∈ U \ (↑S : Set ℂ),
      g z = f z - principalPartSum S (fun s => residue f s) z)
    (hg_zero : γ.contourIntegral g = 0)
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
    HasCauchyPVOn S f γ
      (∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s *
        residue f s) := by
  have h_contour := generalizedResidueTheorem_simplePoles_structural hU S hS_in_U f hf γ
    hSimplePoles hγ_in_U hγ_avoids hδ g hg_diff hg_agree hg_zero h_rem_int h_pp_int hI
  exact h_contour ▸ hasCauchyPVOn_of_avoids hδ

/-! ## Automatic conditions for simple poles -/

/-- **Conditions (A') and (B) are automatic for simple poles.**

For simple poles, flatness of order 1 suffices for condition (A'), and the
Laurent compatibility in condition (B) is vacuously satisfied. This bundles
the results from `FlatnessConditions.lean`. -/
theorem conditions_automatic_for_simplePoles
    (γ : PwC1Immersion x x) (f : ℂ → ℂ) (S : Finset ℂ)
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
    (γ : PwC1Immersion x x) (f : ℂ → ℂ) (S : Finset ℂ)
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f s) :
    SatisfiesConditionA' γ f S (fun _ => 1) :=
  satisfiesConditionA'_of_simplePoles γ f S hSimplePoles

end
