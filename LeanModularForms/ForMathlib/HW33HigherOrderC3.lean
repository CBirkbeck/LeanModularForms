/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HigherOrderCancel
import LeanModularForms.ForMathlib.MultipointPV

/-!
# C-3 — Higher-order polar cancellation in the avoidance case

This file proves the higher-order polar cancellation `higherOrder_cancel_of_avoids`:
when `γ` avoids all poles in `S` with positive margin, the CPV of any sum of
higher-order polar terms `∑ s ∈ S, c s / (z - s)^k` (with `k ≥ 2`) vanishes.

This is the **avoidance form of C-3** (i.e., the case where `γ` does not cross
the pole set, so condition A' on transverse crossings is vacuous and condition
B is automatic). The transverse k-odd case is handled separately by
`hw_theorem_3_3_odd_transverse_concrete` in `HW33ExitTimeWrapper.lean`.

## Main results

* `contourIntegral_finset_sum`: contour integral commutes with finite sums when
  each term is integrable.

* `HasCauchyPVOn.finset_sum`: `HasCauchyPVOn` is closed under finite sums.

* `hasCauchyPVOn_finset_pow_inv_of_avoids`: the finite sum
  `∑ s ∈ S, c s / (z - s)^k` has CPV zero along any closed `γ` avoiding `S`,
  for any `k ≥ 2`.
-/

open Filter Topology MeasureTheory Set
open scoped Classical Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## Finset.sum closure for contour integrals -/

/-- **Finset sum linearity for contour integrals.** When each integrand
`contourIntegrand (f i) γ` is interval-integrable on `[0, 1]`,

  `∮_γ (∑ i ∈ ι, f i z) = ∑ i ∈ ι, ∮_γ f i z`. -/
theorem contourIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    {y : ℂ} (γ : PiecewiseC1Path x y)
    (hf : ∀ i ∈ s, IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand (f i) γ) volume 0 1) :
    γ.contourIntegral (fun z => ∑ i ∈ s, f i z) =
      ∑ i ∈ s, γ.contourIntegral (f i) := by
  classical
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
      have heq : (fun u : ℝ =>
          (∑ i ∈ t, f i (γ.toPath.extend u)) * deriv γ.toPath.extend u) =
          fun u => ∑ i ∈ t, f i (γ.toPath.extend u) * deriv γ.toPath.extend u := by
        funext u
        rw [Finset.sum_mul]
      show IntervalIntegrable
        (fun u => (∑ i ∈ t, f i (γ.toPath.extend u)) * deriv γ.toPath.extend u)
        volume 0 1
      rw [heq]
      have h_sum := IntervalIntegrable.sum t h_t
      have hfun : (∑ i ∈ t, PiecewiseC1Path.contourIntegrand (f i) γ) =
          fun u => ∑ i ∈ t, f i (γ.toPath.extend u) * deriv γ.toPath.extend u := by
        funext u
        rw [Finset.sum_apply]
        rfl
      rw [hfun] at h_sum
      exact h_sum
    rw [Finset.sum_insert hi,
        show (fun z => ∑ i ∈ insert j t, f i z) =
             (fun z => f j z + ∑ i ∈ t, f i z) from
          funext (fun z => Finset.sum_insert hi),
        PiecewiseC1Path.contourIntegral_add (f j) (fun z => ∑ i ∈ t, f i z) γ
          h_j h_t_int,
        ih h_t]

/-! ## Finset.sum closure for HasCauchyPVOn -/

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
  classical
  have heq : (fun t : ℝ =>
      cpvIntegrandOn S (fun z => ∑ i ∈ ι_set, f i z) γ.toPath.extend ε t) =
      fun t => ∑ i ∈ ι_set, cpvIntegrandOn S (f i) γ.toPath.extend ε t := by
    funext t
    simp only [cpvIntegrandOn]
    split_ifs with h
    · rw [Finset.sum_const_zero]
    · rw [Finset.sum_mul]
  rw [heq]
  have h_sum := IntervalIntegrable.sum ι_set hf
  have hfun : (∑ i ∈ ι_set, fun t : ℝ =>
      cpvIntegrandOn S (f i) γ.toPath.extend ε t) =
      fun t => ∑ i ∈ ι_set, cpvIntegrandOn S (f i) γ.toPath.extend ε t := by
    funext t
    rw [Finset.sum_apply]
  rw [hfun] at h_sum
  exact h_sum

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
  classical
  induction ι_set using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    show HasCauchyPVOn S (fun _ => 0) γ 0
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
    show (0 : ℂ) = ∫ (t : ℝ) in (0 : ℝ)..1,
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
          (fun z => ∑ i ∈ t, f i z) γ.toPath.extend ε u) volume 0 1 := by
      intro ε hε
      exact cpvIntegrandOn_finset_sum_intervalIntegrable t S
        (fun i him => hf_int_t i him ε hε)
    have ih_app := ih hf_t hf_int_t
    rw [Finset.sum_insert j_t_disj]
    have heq : (fun z => ∑ i ∈ insert j t, f i z) =
        (fun z => f j z + ∑ i ∈ t, f i z) :=
      funext (fun z => Finset.sum_insert j_t_disj)
    rw [heq]
    exact hf_j.add ih_app hf_int_j hf_int_sum

/-! ## Higher-order polar cancellation: avoidance case -/

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
  classical
  have h_avoids : ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s := by
    obtain ⟨δ, hδ_pos, hδ_bd⟩ := hδ
    intro s hs t ht hγt
    have : δ ≤ ‖γ t - s‖ := hδ_bd s hs t ht
    rw [hγt, sub_self, norm_zero] at this
    linarith
  have h_term_int : ∀ s ∈ S, IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => c s / (z - s) ^ k) γ) volume 0 1 := by
    intro s hs
    show IntervalIntegrable
      (fun t => c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t)
      volume 0 1
    have h_eq : (fun t : ℝ =>
        c s / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t) =
        fun t => c s *
          (1 / (γ.toPath.extend t - s) ^ k * deriv γ.toPath.extend t) := by
      funext t; ring
    rw [h_eq]
    exact (h_int s hs).const_mul (c s)
  have h_zero_each : ∀ s ∈ S, γ.contourIntegral
      (fun z => c s / (z - s) ^ k) = 0 := by
    intro s hs
    have h_avoids_s : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s := h_avoids s hs
    have h_zero : γ.contourIntegral (fun z => 1 / (z - s) ^ k) = 0 :=
      γ.contourIntegral_pow_inv_eq_zero hk h_avoids_s (h_int s hs)
    have h_eq : γ.contourIntegral (fun z => c s / (z - s) ^ k) =
        c s * γ.contourIntegral (fun z => 1 / (z - s) ^ k) := by
      have heq : (fun z => c s / (z - s) ^ k) =
          (fun z => c s * (1 / (z - s) ^ k)) := by
        funext z; ring
      rw [heq, PiecewiseC1Path.contourIntegral_smul]
    rw [h_eq, h_zero, mul_zero]
  have h_sum_zero : γ.contourIntegral
      (fun z => ∑ s ∈ S, c s / (z - s) ^ k) = 0 := by
    rw [contourIntegral_finset_sum S (fun s z => c s / (z - s) ^ k) γ h_term_int]
    exact Finset.sum_eq_zero h_zero_each
  exact hCancel_of_contourIntegral_zero S _ γ hδ h_sum_zero

end LeanModularForms

end
