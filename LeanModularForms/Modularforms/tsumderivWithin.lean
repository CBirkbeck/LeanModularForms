/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
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

@[expose] public section

/-!
# Term-wise differentiation of `tsum`s on the upper half-plane

This file proves termwise differentiation lemmas of the form
`derivWithin (∑' n, f n) s = ∑' n, derivWithin (f n) s` and the analogous
`HasDerivAt`/`HasDerivWithinAt` statements, together with concrete bounds on
iterated derivatives of `n ↦ exp (2π i n z)` on the upper half-plane `ℍ'`.

## Main definitions

* `ℍ'`: the upper half-plane viewed as a subset of `ℂ`.
* `ctsExpTwoPiN`: the continuous function `r ↦ exp (2π i r)` on a set `K`.

## Main results

* `derivWithin_tsum_fun'`, `hasDerivAt_tsum_fun`, `hasDerivWithinAt_tsum_fun`:
  termwise differentiation of a `tsum` under a uniform-on-compacts summable bound
  on the derivatives.
* `iter_deriv_comp_bound2`, `iter_deriv_comp_bound3`: summable upper bounds for
  iterated derivatives of `n ↦ exp (2π i n z)` on compact subsets of `ℍ'`.
-/

open UpperHalfPlane TopologicalSpace Set Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

abbrev ℍ' := {z : ℂ | 0 < z.im}

lemma upper_half_plane_isOpen : IsOpen ℍ' :=
  isOpen_lt (by fun_prop) (by fun_prop)

theorem derivWithin_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ} (hs : IsOpen s) (x : ℂ)
    (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n : α ↦ f n y)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ,
      Summable u ∧ ∀ n (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ n (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z ↦ ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z ↦ f n z) s x := by
  refine (HasDerivAt.hasDerivWithinAt ?_).derivWithin (hs.uniqueDiffWithinAt hx)
  apply hasDerivAt_of_tendstoLocallyUniformlyOn (f := fun n z ↦ ∑ i ∈ n, f i z)
    (f' := fun n a ↦ ∑ i ∈ n, derivWithin (f i) s a) hs ?_ ?_
    (fun y hy ↦ (hf y hy).hasSum) hx
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
    exact tendstoUniformlyOn_tsum hu1 fun n y hy ↦ hu2 n ⟨y, hy⟩
  filter_upwards with t r hr
  refine HasDerivAt.fun_sum fun q _ ↦ ?_
  exact ((hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt).hasDerivAt (hs.mem_nhds hr)

theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ℍ') :
    DifferentiableAt ℂ (fun z : ℂ ↦
      iteratedDerivWithin k (fun s : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' z) ↑r := by
  have hh : DifferentiableOn ℂ
      (fun t ↦ (2 * ↑π * Complex.I * n) ^ k * Complex.exp (2 * ↑π * Complex.I * n * t)) ℍ' := by
    fun_prop
  refine ((hh.congr fun x hx ↦ exp_iter_deriv_within k n hx).differentiableAt
    (upper_half_plane_isOpen.mem_nhds r.2))

private theorem der_iter_eq_der2 (k n : ℕ) (r : ℍ') :
    deriv (iteratedDerivWithin k (fun s : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k
        (fun s : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' ↑r :=
  ((der_iter_eq_der_aux2 k n r).derivWithin (upper_half_plane_isOpen.uniqueDiffOn _ r.2)).symm

theorem der_iter_eq_der2' (k n : ℕ) (r : ℍ') :
    derivWithin (iteratedDerivWithin k (fun s : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
      ℍ' ↑r =
      iteratedDerivWithin (k + 1) (fun s : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' ↑r := by
  rw [iteratedDerivWithin_succ]

private noncomputable def ctsExpTwoPiN (K : Set ℂ) : ContinuousMap K ℂ where
  toFun r := Complex.exp (2 * ↑π * Complex.I * r)

theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (n : ℕ) (r : K),
      (2 * |π| * n) ^ k * ‖(Complex.exp (2 * ↑π * Complex.I * n * r))‖ ≤ u n := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK2
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K)‖ with hr_def
  have hr : r < 1 := by
    rw [hr_def, BoundedContinuousFunction.norm_lt_iff_of_compact (by norm_num)]
    intro x
    simpa [BoundedContinuousFunction.mkOfCompact_apply, ctsExpTwoPiN]
      using exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
  have hr2 : 0 ≤ r := norm_nonneg _
  have habs : |π| = π := abs_of_nonneg Real.pi_pos.le
  have hu : Summable fun n : ℕ ↦ ‖((2 * ↑π * Complex.I * n) ^ k * r ^ n)‖ := by
    have heq : ∀ n : ℕ, (2 * ↑π) ^ k * ‖((n : ℝ) ^ k * r ^ n)‖ =
        ‖((2 * ↑π * Complex.I * n) ^ k * r ^ n)‖ := fun n ↦ by
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, norm_ofNat, norm_real, norm_I,
        mul_one, _root_.norm_natCast, habs, abs_of_nonneg hr2]; ring
    refine (Summable.congr ?_ heq)
    rw [summable_mul_left_iff (by positivity)]
    exact summable_norm_pow_mul_geometric_of_norm_lt_one k (by rwa [norm_norm])
  refine ⟨_, hu, fun n t ↦ ?_⟩
  have ineqe : ‖Complex.exp (2 * π * Complex.I * n * t)‖ ≤ r ^ n := by
    rw [show Complex.exp (2 * π * Complex.I * n * t) =
        Complex.exp (2 * π * Complex.I * t) ^ n by rw [← exp_nat_mul]; ring_nf, norm_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ n
    simpa using BoundedContinuousFunction.norm_coe_le_norm
      (BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K)) t
  calc (2 * |π| * (n : ℝ)) ^ k * ‖Complex.exp (2 * ↑π * Complex.I * n * t)‖
      ≤ (2 * |π| * (n : ℝ)) ^ k * r ^ n :=
        mul_le_mul_of_nonneg_left ineqe (by positivity)
    _ = ‖((2 * ↑π * Complex.I * n) ^ k * r ^ n)‖ := by
        simp [norm_pow, habs, abs_of_nonneg hr2]

theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ} (hs : IsOpen s) (x : ℂ)
    (hx : x ∈ s) (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α ↦ f n y)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ,
      Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z ↦ ∑' n : α, f n z) (∑' n : α, derivWithin (fun z ↦ f n z) s x) x := by
  apply hasDerivAt_of_tendstoLocallyUniformlyOn (f := fun n z ↦ ∑ i ∈ n, f i z)
    (f' := fun n a ↦ ∑ i ∈ n, derivWithin (f i) s a) hs ?_ ?_
    (fun y hy ↦ (hf y hy).hasSum) hx
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
    exact tendstoUniformlyOn_tsum hu1 fun n y hy ↦ hu2 n ⟨y, hy⟩
  filter_upwards with t r hr
  refine HasDerivAt.fun_sum fun q _ ↦ ?_
  exact ((hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt).hasDerivAt (hs.mem_nhds hr)

theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ} (hs : IsOpen s) (x : ℂ)
    (hx : x ∈ s) (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α ↦ f n y)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ,
      Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z ↦ ∑' n : α, f n z) (∑' n : α, derivWithin (fun z ↦ f n z) s x) s x :=
  (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt

theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ (n : ℕ) (r : K),
      ‖(derivWithin (iteratedDerivWithin k
        (fun s : ℂ ↦ Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' r)‖ ≤ u n := by
  obtain ⟨u, hu, hbound⟩ := iter_deriv_comp_bound3 K hK1 hK2 (k + 1)
  refine ⟨u, hu, fun n t ↦ ?_⟩
  have habs : |π| = π := abs_of_nonneg Real.pi_pos.le
  rw [der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩, exp_iter_deriv_within (k + 1) n (hK1 t.2)]
  have hcalc : ‖(2 * ↑π * Complex.I * (n : ℂ)) ^ (k + 1) *
      Complex.exp (2 * ↑π * Complex.I * n * ↑t)‖ =
      (2 * |π| * (n : ℝ)) ^ (k + 1) * ‖Complex.exp (2 * ↑π * Complex.I * n * t)‖ := by
    simp [norm_pow, habs]
  rw [hcalc]
  exact hbound n t
