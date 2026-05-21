/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HigherOrderCancel
import LeanModularForms.ForMathlib.MultipointPV
import LeanModularForms.ForMathlib.HigherOrderAssembly

/-!
# Higher-order polar cancellation, closure, and auto-discharge wrappers

This file consolidates the three-file C-3/C-4/Auto chain for the higher-order
polar avoidance case of HW Theorem 3.3:

* **C-3** (formerly `HW33HigherOrderC3.lean`): higher-order polar cancellation
  `higherOrder_cancel_of_avoids` — when `γ` avoids all poles in `S` with positive
  margin, the CPV of any sum of higher-order polar terms
  `∑ s ∈ S, c s / (z - s)^k` (with `k ≥ 2`) vanishes.
* **C-4** (formerly `HW33HigherOrderC4.lean`): composing the B-6 closed
  simple-pole residue theorem with the C-3 cancellation gives a closed residue
  theorem for `f_simple + (higher-order Laurent corrections)` in the avoidance
  case.
* **Auto-discharge** (formerly `HW33HigherOrderAuto.lean`): user-friendly
  wrappers that auto-discharge the integrability hypotheses when `γ` is
  Lipschitz and avoids the pole set with positive margin.

The k-odd transverse case (γ crossing poles transversally) is handled by
`hw_theorem_3_3_odd_transverse_concrete` from `HW33Tight.lean`.

## Main results

### C-3 (cancellation in the avoidance case)

* `contourIntegral_finset_sum`: contour integral commutes with finite sums when
  each term is integrable.
* `HasCauchyPVOn.finset_sum`: `HasCauchyPVOn` is closed under finite sums.
* `hasCauchyPVOn_finset_pow_inv_of_avoids`: the finite sum
  `∑ s ∈ S, c s / (z - s)^k` has CPV zero along any closed `γ` avoiding `S`,
  for any `k ≥ 2`.

### C-4 (closure)

* `hasCauchyPVOn_add_higherOrderPolar_of_avoids`: closure of `HasCauchyPVOn`
  under adding a single higher-order polar term `∑ s ∈ S, c s / (z - s)^k`
  (k ≥ 2), in the avoidance case.
* `generalizedResidueTheorem_higherOrder_avoids_closed`: the C-4 statement —
  closed-form residue theorem for `f_simple + (higher-order polar corrections)`
  in the avoidance case, with γ closed null-homologous and Lipschitz.

### Auto-discharge

* `intervalIntegrable_pow_inv_mul_deriv_of_avoids`: integrability of
  `1/(γ - s)^k · γ'` for Lipschitz γ avoiding `s` with positive margin.
* `generalizedResidueTheorem_higherOrder_avoids_closed_lip`: fully
  auto-discharged closed C-4 form.
-/

open Filter Topology MeasureTheory Set Complex
open scoped Classical Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## C-3 — Higher-order polar cancellation in the avoidance case

(Formerly `HW33HigherOrderC3.lean`.)
-/

/-- **Finset sum linearity for contour integrals.** When each integrand
`contourIntegrand (f i) γ` is interval-integrable on `[0, 1]`,

  `∮_γ (∑ i ∈ ι, f i z) = ∑ i ∈ ι, ∮_γ f i z`. -/
theorem contourIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    {y : ℂ} (γ : PiecewiseC1Path x y)
    (hf : ∀ i ∈ s, IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (f i) γ) volume 0 1) :
    γ.contourIntegral (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, γ.contourIntegral (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact PiecewiseC1Path.contourIntegral_zero γ
  | @insert j t hi ih =>
    have h_j : IntervalIntegrable
        (PiecewiseC1Path.contourIntegrand (f j) γ) volume 0 1 :=
      hf j (Finset.mem_insert_self _ _)
    have h_t : ∀ i ∈ t, IntervalIntegrable
        (PiecewiseC1Path.contourIntegrand (f i) γ) volume 0 1 :=
      fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h_t_int : IntervalIntegrable
        (PiecewiseC1Path.contourIntegrand
          (fun z => ∑ i ∈ t, f i z) γ) volume 0 1 := by
      have h_sum := IntervalIntegrable.sum t h_t
      have hfun : (∑ i ∈ t, PiecewiseC1Path.contourIntegrand (f i) γ) =
          PiecewiseC1Path.contourIntegrand (fun z => ∑ i ∈ t, f i z) γ := by
        funext u
        simp [PiecewiseC1Path.contourIntegrand, Finset.sum_apply, Finset.sum_mul]
      rwa [hfun] at h_sum
    rw [Finset.sum_insert hi,
        show (fun z => ∑ i ∈ insert j t, f i z) =
             (fun z => f j z + ∑ i ∈ t, f i z) from
          funext (fun z => Finset.sum_insert hi),
        PiecewiseC1Path.contourIntegral_add (f j) (fun z => ∑ i ∈ t, f i z) γ
          h_j h_t_int,
        ih h_t]

/-- **Sum-closure preliminary**: integrability of the CPV integrand transfers
through finite sums when each term is integrable. -/
theorem cpvIntegrandOn_finset_sum_intervalIntegrable
    {ι : Type*} (ι_set : Finset ι) (S : Finset ℂ) {f : ι → ℂ → ℂ}
    {γ : PiecewiseC1Path x x} {ε : ℝ}
    (hf : ∀ i ∈ ι_set, IntervalIntegrable
      (fun t => cpvIntegrandOn S (f i) γ.toPath.extend ε t) volume 0 1) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => ∑ i ∈ ι_set, f i z) γ.toPath.extend ε t)
      volume 0 1 := by
  convert IntervalIntegrable.sum ι_set hf using 1
  funext t
  simp only [cpvIntegrandOn, Finset.sum_apply]
  split_ifs with h
  · rw [Finset.sum_const_zero]
  · rw [Finset.sum_mul]

/-- **Finset sum closure of `HasCauchyPVOn`.** If `HasCauchyPVOn S (f i) γ (L i)`
holds for each `i ∈ ι`, with appropriate integrability of the CPV integrands
of each `f i`, then the sum has `HasCauchyPVOn S (∑ i, f i) γ (∑ i, L i)`. -/
theorem HasCauchyPVOn.finset_sum {ι : Type*} (ι_set : Finset ι)
    {S : Finset ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ}
    {γ : PiecewiseC1Path x x}
    (hf : ∀ i ∈ ι_set, HasCauchyPVOn S (f i) γ (L i))
    (hf_int : ∀ i ∈ ι_set, ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (f i) γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S (fun z => ∑ i ∈ ι_set, f i z) γ (∑ i ∈ ι_set, L i) := by
  induction ι_set using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change HasCauchyPVOn S (fun _ => 0) γ 0
    simp only [HasCauchyPVOn]
    apply Filter.Tendsto.congr' (f₁ := fun _ => (0 : ℂ)) _ tendsto_const_nhds
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨univ, univ_mem, ?_⟩
    intro ε _
    have h1 : (fun t : ℝ => cpvIntegrandOn S (fun (_ : ℂ) => (0 : ℂ))
        γ.toPath.extend ε t) = fun _ => (0 : ℂ) := by
      funext t
      simp only [cpvIntegrandOn]
      split_ifs <;> simp
    change (0 : ℂ) = ∫ (t : ℝ) in (0 : ℝ)..1,
        cpvIntegrandOn S (fun (_ : ℂ) => (0 : ℂ)) γ.toPath.extend ε t
    rw [h1, intervalIntegral.integral_zero]
  | @insert j t j_t_disj ih =>
    have hf_j : HasCauchyPVOn S (f j) γ (L j) := hf j (Finset.mem_insert_self _ _)
    have hf_t : ∀ i ∈ t, HasCauchyPVOn S (f i) γ (L i) :=
      fun i him => hf i (Finset.mem_insert_of_mem him)
    have hf_int_j : ∀ ε > 0, IntervalIntegrable
        (fun u => cpvIntegrandOn S (f j) γ.toPath.extend ε u) volume 0 1 :=
      hf_int j (Finset.mem_insert_self _ _)
    have hf_int_t : ∀ i ∈ t, ∀ ε > 0, IntervalIntegrable
        (fun u => cpvIntegrandOn S (f i) γ.toPath.extend ε u) volume 0 1 :=
      fun i him => hf_int i (Finset.mem_insert_of_mem him)
    have hf_int_sum : ∀ ε > 0, IntervalIntegrable
        (fun u => cpvIntegrandOn S
          (fun z => ∑ i ∈ t, f i z) γ.toPath.extend ε u) volume 0 1 := fun ε hε =>
      cpvIntegrandOn_finset_sum_intervalIntegrable t S
        (fun i him => hf_int_t i him ε hε)
    rw [Finset.sum_insert j_t_disj, show (fun z => ∑ i ∈ insert j t, f i z) =
        (fun z => f j z + ∑ i ∈ t, f i z) from funext (fun z => Finset.sum_insert j_t_disj)]
    exact hf_j.add (ih hf_t hf_int_t) hf_int_j hf_int_sum

/-- **Higher-order polar single-power avoidance.** For `k ≥ 2`, the CPV of
`∑ s ∈ S, c s / (z - s)^k` along a closed curve avoiding `S` vanishes.

This generalizes `hasCauchyPVOn_pow_inv_of_avoids` from a single pole `s`
to a finite sum over `S`, with arbitrary coefficients `c s`.

The hypothesis `h_int` requires interval-integrability of the contour
integrand for each individual term `c s / (z - s)^k`; this is automatic when
`γ` is Lipschitz, but stated explicitly here for generality. -/
theorem hasCauchyPVOn_finset_pow_inv_of_avoids
    (S : Finset ℂ) (k : ℕ) (hk : 2 ≤ k) (c : ℂ → ℂ)
    (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_int : ∀ s ∈ S, IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1) :
    HasCauchyPVOn S
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 := by
  have h_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s := fun s hs t ht hγt => by
    obtain ⟨δ, hδ_pos, hδ_bd⟩ := hδ
    have := hδ_bd s hs t ht
    rw [hγt, sub_self, norm_zero] at this
    linarith
  have h_term_int : ∀ s ∈ S, IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => c s / (z - s) ^ k) γ) volume 0 1 := fun s hs => by
    convert (h_int s hs).const_mul (c s) using 1
    funext t
    simp [PiecewiseC1Path.contourIntegrand]; ring
  have h_zero_each : ∀ s ∈ S, γ.contourIntegral
      (fun z => c s / (z - s) ^ k) = 0 := fun s hs => by
    rw [show (fun z => c s / (z - s) ^ k) = (fun z => c s * (1 / (z - s) ^ k)) from
      funext fun z => by ring, PiecewiseC1Path.contourIntegral_smul,
      γ.contourIntegral_pow_inv_eq_zero hk (h_avoids s hs) (h_int s hs), mul_zero]
  refine hCancel_of_contourIntegral_zero S _ γ hδ ?_
  rw [contourIntegral_finset_sum S (fun s z => c s / (z - s) ^ k) γ h_term_int]
  exact Finset.sum_eq_zero h_zero_each

/-! ## C-4 — Closed residue theorem for higher-order poles (avoidance case)

(Formerly `HW33HigherOrderC4.lean`.)
-/

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

/-! ## Auto-discharge wrappers (Lipschitz + avoidance)

(Formerly `HW33HigherOrderAuto.lean`.)
-/

/-- Convert avoidance bound stated via `γ t` to one stated via `γ.toPath.extend t`. -/
private lemma delta_bd_extend_aux {y : ℂ} {S : Finset ℂ} (γ : PiecewiseC1Path x y) {δ : ℝ}
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (s : ℂ) (hs : s ∈ S) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    δ ≤ ‖γ.toPath.extend t - s‖ := by
  have := hδ_bd s hs t ht
  rwa [PiecewiseC1Path.extendedPath_eq] at this

/-- **Integrability of `1/(γ - s)^k · γ'` from Lipschitz + avoidance.** When `γ`
is Lipschitz and avoids `s` with positive margin `δ > 0`, the integrand
`1/(γ(t) - s)^k · γ'(t)` is interval-integrable on `[0, 1]`.

Proof: `1/(γ - s)^k` is `ContinuousOn (Icc 0 1)` (since `γ - s` is continuous and
nonzero by avoidance) hence essentially bounded by `1/δ^k`. The Lipschitz
hypothesis gives integrability of `deriv γ` on `Ioc 0 1` (via the Lipschitz
norm bound `K`). Combining via `Integrable.bdd_mul`. -/
theorem intervalIntegrable_pow_inv_mul_deriv_of_avoids (γ : PiecewiseC1Path x x)
    (s : ℂ) (k : ℕ) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ.toPath.extend t - s‖) {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) :
    IntervalIntegrable
      (fun t => 1 / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)]
  have h_deriv_int : IntegrableOn (deriv γ.toPath.extend) (Ioc (0 : ℝ) 1) volume :=
    MeasureTheory.Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (stronglyMeasurable_deriv _).aestronglyMeasurable
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun _ => norm_deriv_le_of_lipschitz hLip)))
  have h_meas : AEStronglyMeasurable
      (fun t => (1 : ℂ) / (γ.toPath.extend t - s) ^ k)
      (volume.restrict (Ioc (0 : ℝ) 1)) :=
    ((continuousOn_const.div
        ((γ.toPath.continuous_extend.continuousOn.sub continuousOn_const).pow k)
        (fun t ht => pow_ne_zero _ fun hzero => by
          have := hδ_bd t ht; rw [hzero, norm_zero] at this; linarith)).mono
      Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound_ae : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖(1 : ℂ) / (γ.toPath.extend t - s) ^ k‖ ≤ 1 / δ ^ k := by
    refine (ae_restrict_iff' measurableSet_Ioc).mpr <| .of_forall fun t ht => ?_
    rw [norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left zero_le_one (pow_pos hδ_pos k)
      (pow_le_pow_left₀ hδ_pos.le (hδ_bd t (Ioc_subset_Icc_self ht)) k)
  exact h_deriv_int.bdd_mul h_meas h_bound_ae

/-- The "ε-ball" set `{t | ∃ s ∈ S, ‖γ(t) - s‖ ≤ ε}` is measurable. -/
theorem measurableSet_cpvIntegrandOn_zero
    {y : ℂ} (S : Finset ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) :
    MeasurableSet {t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε} := by
  suffices {t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε} =
      ⋃ s ∈ (S : Set ℂ), {t | ‖γ.toPath.extend t - s‖ ≤ ε} by
    rw [this]
    exact S.finite_toSet.measurableSet_biUnion fun s _ =>
      (γ.toPath.continuous_extend.measurable.sub_const s).norm measurableSet_Iic
  ext t; simp

/-- **CPV integrand is dominated by the contour integrand.** Pointwise:
`‖cpvIntegrandOn S f γ ε t‖ ≤ ‖contourIntegrand f γ t‖`, since the CPV integrand
is either 0 or equal to the contour integrand. This is the pointwise step
toward dominated-convergence integrability arguments for `cpvIntegrandOn`. -/
theorem norm_cpvIntegrandOn_le_norm_contourIntegrand
    {y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ) (t : ℝ) :
    ‖cpvIntegrandOn S f γ.toPath.extend ε t‖ ≤
      ‖PiecewiseC1Path.contourIntegrand f γ t‖ := by
  simp only [cpvIntegrandOn, PiecewiseC1Path.contourIntegrand,
    PiecewiseC1Path.extendedPath_eq]
  split_ifs <;>
  first | (rw [norm_zero]; exact norm_nonneg _) | rfl

/-- **CPV integrand AEStronglyMeasurable from contour integrand AEStronglyMeasurable.**
The CPV integrand `cpvIntegrandOn S f γ ε` is `Set.piecewise A 0 (contourIntegrand f γ)`
where `A = {t | ∃ s ∈ S, ‖γ(t) - s‖ ≤ ε}` is measurable. -/
theorem aestronglyMeasurable_cpvIntegrandOn
    {y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ)
    {μ : MeasureTheory.Measure ℝ}
    (h_contour_meas : AEStronglyMeasurable
      (PiecewiseC1Path.contourIntegrand f γ) μ) :
    AEStronglyMeasurable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) μ := by
  suffices (fun t : ℝ => cpvIntegrandOn S f γ.toPath.extend ε t) =
      ({t : ℝ | ∃ s ∈ S, ‖γ.toPath.extend t - s‖ ≤ ε}).piecewise
        (fun _ => 0) (PiecewiseC1Path.contourIntegrand f γ) by
    rw [this]
    exact .piecewise (measurableSet_cpvIntegrandOn_zero S γ ε)
      aestronglyMeasurable_const
      (h_contour_meas.mono_measure Measure.restrict_le_self)
  funext t
  simp only [cpvIntegrandOn, Set.piecewise, PiecewiseC1Path.contourIntegrand,
    PiecewiseC1Path.extendedPath_eq, Set.mem_setOf_eq]

/-- **CPV integrand interval-integrability from contour integrand integrability.**
For any `ε`, if the contour integrand `f(γ(t)) · γ'(t)` is interval-integrable
on `[0, 1]`, so is the CPV integrand `cpvIntegrandOn S f γ ε`. The proof uses
the pointwise norm bound (`norm_cpvIntegrandOn_le_norm_contourIntegrand`)
and `IntervalIntegrable.mono_fun`. -/
theorem cpvIntegrandOn_intervalIntegrable_of_contourIntegrand
    {y : ℂ} (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (ε : ℝ)
    (h_contour_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand f γ) volume 0 1) :
    IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1 := by
  refine h_contour_int.mono_fun ?_
    (ae_of_all _ <| norm_cpvIntegrandOn_le_norm_contourIntegrand S f γ ε)
  have h := h_contour_int.aestronglyMeasurable
  rw [show Ioc (0 : ℝ) 1 = Ι (0 : ℝ) 1 from (uIoc_of_le (zero_le_one' ℝ)).symm] at h
  exact aestronglyMeasurable_cpvIntegrandOn S f γ ε h

/-- **C-3 single-power avoidance, integrability auto-derived (Lipschitz form).**
For `γ` Lipschitz avoiding `S` with positive margin, the higher-order polar sum
`∑ s ∈ S, c s / (z - s)^k` (`k ≥ 2`) has CPV zero. The interval-integrability
hypothesis of `hasCauchyPVOn_finset_pow_inv_of_avoids` is auto-discharged via
`intervalIntegrable_pow_inv_mul_deriv_of_avoids`. -/
theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip (S : Finset ℂ) (k : ℕ)
    (hk : 2 ≤ k) (c : ℂ → ℂ) (γ : PiecewiseC1Path x x) {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 := by
  refine hasCauchyPVOn_finset_pow_inv_of_avoids S k hk c γ ⟨δ, hδ_pos, hδ_bd⟩ fun s hs =>
    intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
      (delta_bd_extend_aux γ hδ_bd s hs) hLip

/-- **C-3 single-power avoidance, δ-free + Lipschitz form.** Same as
`hasCauchyPVOn_finset_pow_inv_of_avoids_lip` but with the positive margin
auto-derived from pointwise avoidance via `avoids_finset_delta_bound`. -/
theorem hasCauchyPVOn_finset_pow_inv_of_avoids_lip_avoids (S : Finset ℂ) (k : ℕ)
    (hk : 2 ≤ k) (c : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hγ_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s) {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ 0 :=
  let ⟨_, hδ_pos, hδ_bd⟩ := avoids_finset_delta_bound γ S hγ_avoids
  hasCauchyPVOn_finset_pow_inv_of_avoids_lip S k hk c γ hδ_pos hδ_bd hLip

/-- **Contour integrand integrability for the higher-order polar sum.** When `γ`
is Lipschitz and avoids `S` with positive margin, the contour integrand
`(∑ s ∈ S, c s / (γ(t) - s)^k) · γ'(t)` is interval-integrable on `[0, 1]`. -/
theorem contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip
    (S : Finset ℂ) (k : ℕ) (c : ℂ → ℂ) (γ : PiecewiseC1Path x x) {δ : ℝ}
    (hδ_pos : 0 < δ) (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    {K : NNReal} (hLip : LipschitzWith K γ.toPath.extend) :
    IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ) volume 0 1 := by
  have h_each : ∀ s ∈ S, IntervalIntegrable
      (fun t => c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1 := fun s hs => by
    rw [show (fun t : ℝ =>
        c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t) =
        fun t => c s *
          (1 / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t) by
      funext t; ring]
    exact (intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
      (delta_bd_extend_aux γ hδ_bd s hs) hLip).const_mul (c s)
  have heq : PiecewiseC1Path.contourIntegrand
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) γ =
      fun t => ∑ s ∈ S,
        c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t := by
    funext t
    simp only [PiecewiseC1Path.contourIntegrand, PiecewiseC1Path.extendedPath_eq,
      Finset.sum_mul]
  rw [heq, ← Finset.sum_fn]
  exact IntervalIntegrable.sum S h_each

/-- **`hasCauchyPVOn_add_higherOrderPolar_of_avoids` with all integrability
auto-discharged from Lipschitz + avoidance.** -/
theorem hasCauchyPVOn_add_higherOrderPolar_of_avoids_lip (S : Finset ℂ)
    (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_f : HasCauchyPVOn S f γ L)
    (h_f_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1) (k : ℕ)
    (hk : 2 ≤ k) (c : ℂ → ℂ) {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => f z + ∑ s ∈ S, c s / (z - s) ^ k) γ L :=
  hasCauchyPVOn_add_higherOrderPolar_of_avoids S f γ
    ⟨δ, hδ_pos, hδ_bd⟩ h_f h_f_int k hk c
    (fun s hs => intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
      (delta_bd_extend_aux γ hδ_bd s hs) hLip)
    (fun ε _ =>
      cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S _ γ ε
        (contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip
          S k c γ hδ_pos hδ_bd hLip))

/-- **`hasCauchyPVOn_add_higherOrderPolarSum_of_avoids` with all integrability
auto-discharged from Lipschitz + avoidance (multi-power version).** -/
theorem hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip (S : Finset ℂ)
    (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ} {δ : ℝ} (hδ_pos : 0 < δ)
    (hδ_bd : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_f : HasCauchyPVOn S f γ L)
    (h_f_int : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1) (M : ℕ)
    (c_HO : ℕ → ℂ → ℂ) {K : NNReal}
    (hLip : LipschitzWith K γ.toPath.extend) :
    HasCauchyPVOn S
      (fun z => f z +
        ∑ k ∈ Finset.Ico 2 (M + 1), ∑ s ∈ S, c_HO k s / (z - s) ^ k) γ L :=
  hasCauchyPVOn_add_higherOrderPolarSum_of_avoids S f γ
    ⟨δ, hδ_pos, hδ_bd⟩ h_f h_f_int M c_HO
    (fun k _ s hs => intervalIntegrable_pow_inv_mul_deriv_of_avoids γ s k hδ_pos
      (delta_bd_extend_aux γ hδ_bd s hs) hLip)
    (fun k _ ε _ =>
      cpvIntegrandOn_intervalIntegrable_of_contourIntegrand S _ γ ε
        (contourIntegrand_finset_pow_inv_intervalIntegrable_of_avoids_lip
          S k (c_HO k) γ hδ_pos hδ_bd hLip))

/-- **C-4 closed avoidance form, fully auto-discharged.** Same as
`generalizedResidueTheorem_higherOrder_avoids_closed` but with the higher-order
integrability hypotheses (`h_int_HO` and `h_HO_int`) auto-discharged from the
Lipschitz + avoidance assumptions already present.

The user supplies only:
* `f_simple` differentiable with simple poles at `S`,
* the higher-order coefficients `c_HO`,
* `f_simple`'s CPV-integrand integrability (a single hypothesis on f_simple
  alone — much smaller than the original four),
* γ closed null-homologous Lipschitz avoiding `S`.

The conclusion is the same residue formula as the simple-pole case:
the higher-order terms contribute zero. -/
theorem generalizedResidueTheorem_higherOrder_avoids_closed_lip {U : Set ℂ}
    (hU_open : IsOpen U) (hU_ne : U.Nonempty) (hU_bounded : Bornology.IsBounded U)
    (S : Finset ℂ) (hS_in_U : ↑S ⊆ U) (γ : PwC1Immersion x x)
    (h_null : IsNullHomologous γ U) (f_simple : ℂ → ℂ)
    (hf_simple : DifferentiableOn ℂ f_simple (U \ ↑S))
    (hSimplePoles : ∀ s ∈ S, HasSimplePoleAt f_simple s) (M : ℕ)
    (c_HO : ℕ → ℂ → ℂ) (h_simple_int : ∀ ε > 0, IntervalIntegrable
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
  obtain ⟨δ, hδ_pos, hδ_bd⟩ :=
    avoids_finset_delta_bound γ.toPiecewiseC1Path S hγ_avoids
  exact hasCauchyPVOn_add_higherOrderPolarSum_of_avoids_lip
    S f_simple γ.toPiecewiseC1Path hδ_pos hδ_bd
    (generalizedResidueTheorem_simplePoles_nullHomologous_closed hU_open hU_ne
      hU_bounded S hS_in_U f_simple hf_simple γ h_null hSimplePoles hγ_avoids
      ⟨δ, hδ_pos, hδ_bd⟩ hLip)
    h_simple_int M c_HO hLip

end LeanModularForms

end
