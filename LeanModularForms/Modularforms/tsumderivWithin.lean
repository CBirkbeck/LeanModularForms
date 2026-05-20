/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.ContinuousMap.Compact
public import LeanModularForms.Modularforms.exp_lems
public import LeanModularForms.Modularforms.iteratedderivs

/-!
# Termwise differentiation of `tsum` over the upper half plane

This file proves results enabling termwise differentiation of locally uniformly convergent
series of complex-valued functions, with a focus on the exponential series
`fun z ↦ ∑' n, exp (2π i n z)` on the upper half plane.

## Main results

* `derivWithin_tsum_fun'`: differentiation commutes with `tsum` on an open set when the
  partial sums of the derivative are locally uniformly bounded.
* `hasDerivAt_tsum_fun` / `hasDerivWithinAt_tsum_fun`: variants stating the derivative of
  the tsum as a `HasDerivAt` / `HasDerivWithinAt` predicate.
* `iter_deriv_comp_bound2` / `iter_deriv_comp_bound3`: summable bounds for the iterated
  derivatives of `exp (2π i n z)` on a compact subset of the upper half plane.
-/

@[expose] public section

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

/-- The (open) upper half plane as a subset of `ℂ`. -/
abbrev ℍ' := {z : ℂ | 0 < z.im}

lemma upper_half_plane_isOpen : IsOpen ℍ' :=
  isOpen_lt (by fun_prop) (by fun_prop)

theorem derivWithin_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ} (hs : IsOpen s) (x : ℂ)
    (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n : α => f n y)
    (hu : ∀ K ⊆ s, IsCompact K →
        ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ n (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  apply HasDerivWithinAt.derivWithin
  · apply HasDerivAt.hasDerivWithinAt
    have A : ∀ x : ℂ, x ∈ s → Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
        (𝓝 (∑' n : α, (fun z => f n z) x)) :=
      fun y hy ↦ Summable.hasSum <| hf y hy
    apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
    · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
    · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
      intro K hK1 hK2
      obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
      apply tendstoUniformlyOn_tsum hu1
      intro n x hx
      exact hu2 n ⟨x, hx⟩
    filter_upwards
    intro t r hr
    apply HasDerivAt.fun_sum
    intro q _
    apply HasDerivWithinAt.hasDerivAt
    · exact (hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt
    exact hs.mem_nhds hr
  exact hs.uniqueDiffWithinAt hx

theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ℍ') :
    DifferentiableAt ℂ (fun z : ℂ =>
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' z) ↑r := by
  have hh : DifferentiableOn ℂ (fun t => (2 * ↑π * Complex.I * n) ^ k *
      Complex.exp (2 * ↑π * Complex.I * n * t)) ℍ' := by
    apply Differentiable.differentiableOn
    fun_prop
  apply DifferentiableOn.differentiableAt
  · apply hh.congr
    intro x hx
    exact exp_iter_deriv_within k n hx
  exact upper_half_plane_isOpen.mem_nhds r.2

theorem der_iter_eq_der2 (k n : ℕ) (r : ℍ') :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
        ℍ' ↑r := by
  symm
  apply DifferentiableAt.derivWithin
  · exact der_iter_eq_der_aux2 k n r
  exact upper_half_plane_isOpen.uniqueDiffOn _ r.2

theorem der_iter_eq_der2' (k n : ℕ) (r : ℍ') :
    derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
        ℍ' ↑r =
      iteratedDerivWithin (k + 1) (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' ↑r := by
  rw [iteratedDerivWithin_succ]

/-- The continuous map `r ↦ exp (2π i r)` on a subset `K ⊆ ℂ`. -/
noncomputable def cts_exp_two_pi_n (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)

theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (n : ℕ) (r : K),
      ‖derivWithin (iteratedDerivWithin k
          (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' r‖ ≤ u n := by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff, ← isCompact_iff_isCompact_univ]
    exact hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖ < 1 := by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact (by linarith)]
    intro x
    rw [BoundedContinuousFunction.mkOfCompact_apply]
    simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk]
    exact exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
  have hr2 : 0 ≤ r := by positivity
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖ := by
    have h_eq : ∀ (n : ℕ), ((2 * ↑π) ^ (k + 1)) * ‖((n) ^ (k + 1) * (r ^ n))‖ =
        ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖ := by
      intro n
      norm_cast
      simp only [Nat.cast_pow, norm_mul, norm_pow, Real.norm_eq_abs, ofReal_mul, ofReal_ofNat,
        ofReal_pow, norm_ofNat, norm_real, norm_I, mul_one, _root_.norm_natCast]
      norm_cast
      simp only [Nat.cast_pow, abs_of_pos Real.pi_pos]
      ring
    apply Summable.congr _ h_eq
    rw [summable_mul_left_iff]
    · apply summable_norm_pow_mul_geometric_of_norm_lt_one
      convert hr
      rw [norm_norm]
    norm_cast
    exact pow_ne_zero _ (mul_ne_zero (by linarith) Real.pi_ne_zero)
  use fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖, hu
  intro n t
  have go := der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩
  simp at *
  simp_rw [go]
  have h1 := exp_iter_deriv_within (k + 1) n (hK1 t.2)
  norm_cast at *
  simp at *
  rw [h1]
  simp
  have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n := by
    have hw1 :
        ‖(Complex.exp (2 * π * Complex.I * n * t))‖ =
          ‖(Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
      norm_cast
      rw [← Complex.norm_pow]
      congr
      rw [← exp_nat_mul]
      ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left₀
    · simp only [norm_nonneg]
    have := BoundedContinuousFunction.norm_coe_le_norm
      (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    rw [norm_norm]
    simpa using this
  apply mul_le_mul
  · simp
  · simp at ineqe
    convert ineqe
  · positivity
  · positivity

theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ} (hs : IsOpen s) (x : ℂ)
    (hx : x ∈ s) (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu : ∀ K ⊆ s, IsCompact K →
        ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x := by
  have A : ∀ x : ℂ, x ∈ s → Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
      (𝓝 (∑' n : α, (fun z => f n z) x)) := by
    intro y hy
    apply Summable.hasSum
    simpa using hf y hy
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
    apply tendstoUniformlyOn_tsum hu1
    intro n x hx
    exact hu2 n ⟨x, hx⟩
  filter_upwards
  intro t r hr
  apply HasDerivAt.fun_sum
  intro q _
  apply HasDerivWithinAt.hasDerivAt
  · exact (hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt
  exact hs.mem_nhds hr

theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ} (hs : IsOpen s) (x : ℂ)
    (hx : x ∈ s) (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu : ∀ K ⊆ s, IsCompact K →
        ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z)
      (∑' n : α, derivWithin (fun z => f n z) s x) s x :=
  (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt

theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (n : ℕ) (r : K),
      (2 * |π| * n) ^ k * ‖(Complex.exp (2 * ↑π * Complex.I * n * r))‖ ≤ u n := by
  have : CompactSpace K := by
    rw [← isCompact_univ_iff, ← isCompact_iff_isCompact_univ]
    exact hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)‖ < 1 := by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact (by linarith)]
    intro x
    rw [BoundedContinuousFunction.mkOfCompact_apply]
    simp_rw [cts_exp_two_pi_n]
    simp only [ContinuousMap.coe_mk]
    exact exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
  have hr2 : 0 ≤ r := by positivity
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ k * r ^ n)‖ := by
    have h_eq : ∀ (n : ℕ), ((2 * ↑π) ^ k) * ‖((n) ^ k * (r ^ n))‖ =
        ‖((2 * ↑π * Complex.I * n) ^ k * r ^ n)‖ := by
      intro n
      norm_cast
      simp only [Nat.cast_pow, norm_mul, norm_pow, Real.norm_eq_abs, ofReal_mul, ofReal_ofNat,
        ofReal_pow, norm_ofNat, norm_real, norm_I, mul_one, _root_.norm_natCast]
      norm_cast
      simp only [Nat.cast_pow, abs_of_pos Real.pi_pos]
      ring
    apply Summable.congr _ h_eq
    rw [summable_mul_left_iff]
    · apply summable_norm_pow_mul_geometric_of_norm_lt_one
      convert hr
      rw [norm_norm]
    norm_cast
    exact pow_ne_zero _ (mul_ne_zero (by linarith) Real.pi_ne_zero)
  use fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ k * r ^ n)‖, hu
  intro n t
  simp
  have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n := by
    have hw1 :
        ‖(Complex.exp (2 * π * Complex.I * n * t))‖ =
          ‖(Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
      norm_cast
      rw [← Complex.norm_pow]
      congr
      rw [← exp_nat_mul]
      ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left₀
    · simp only [norm_nonneg]
    have := BoundedContinuousFunction.norm_coe_le_norm
      (BoundedContinuousFunction.mkOfCompact (cts_exp_two_pi_n K)) t
    rw [norm_norm]
    simpa using this
  apply mul_le_mul
  · simp
  · simp at ineqe
    convert ineqe
  · positivity
  · positivity
