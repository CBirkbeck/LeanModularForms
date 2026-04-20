/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.CauchyPrincipalValue

/-!
# Multi-Point Cauchy Principal Value Infrastructure

Algebraic lemmas for multi-point Cauchy principal values and minimum separation
of finite sets. These are the building blocks for the generalized residue theorem.

## Main results

### Finite set separation

* `finset_discrete_min_sep` -- positive minimum separation in a finite set of distinct
  complex numbers.
* `finset_discrete_min_sep'` -- variant with `S.card > 1` hypothesis.
* `disjoint_balls_of_small_epsilon` -- disjoint balls for sufficiently small epsilon.

### Algebraic operations on `cpvIntegrandOn`

* `cpvIntegrandOn_sub` -- pointwise subtraction of CPV integrands
* `cpvIntegrandOn_add` -- pointwise addition of CPV integrands
* `cpvIntegrandOn_neg` -- pointwise negation of CPV integrands

### Algebraic operations on `HasCauchyPVOn`

* `HasCauchyPVOn.sub` -- subtraction of multi-point CPV limits
* `HasCauchyPVOn.add` -- addition of multi-point CPV limits
* `hasCauchyPVOn_of_tendsto_sub` -- transfer via vanishing difference

### Connection between single-point and multi-point CPV

* `hasCauchyPVOn_singleton_of_hasCauchyPV` -- single-point to multi-point
* `hasCauchyPV_of_hasCauchyPVOn_singleton` -- multi-point (singleton) to single-point

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-! ## Finite Set Separation -/

/-- Positive minimum separation in a finite set of distinct complex numbers. Given a
nonempty finite set `S` where all distinct pairs have positive distance, there exists
a uniform lower bound `δ > 0` on pairwise distances. -/
theorem finset_discrete_min_sep (S : Finset ℂ) (hS_nonempty : S.Nonempty)
    (hS_discrete : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 0 < ‖s' - s‖) :
    ∃ δ > 0, ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → δ ≤ ‖s' - s‖ := by
  by_cases h_singleton : S.card ≤ 1
  · refine ⟨1, one_pos, fun s hs s' hs' hne => ?_⟩
    have h_card_eq : S.card = 1 := by have := hS_nonempty.card_pos; omega
    obtain ⟨a, hS_eq⟩ := Finset.card_eq_one.mp h_card_eq
    have hs_eq : s = a := by rw [hS_eq] at hs; exact Finset.mem_singleton.mp hs
    have hs'_eq : s' = a := by rw [hS_eq] at hs'; exact Finset.mem_singleton.mp hs'
    exact (hne (hs_eq.trans hs'_eq.symm)).elim
  · push Not at h_singleton
    classical
    let dists : Finset ℝ := S.biUnion (fun s =>
      S.filter (· ≠ s) |>.image (fun s' => ‖s' - s‖))
    have h_nonempty : dists.Nonempty := by
      obtain ⟨a, ha⟩ := hS_nonempty
      have h_exists_b : ∃ b ∈ S, b ≠ a := by
        by_contra h_all; push Not at h_all
        have : S.card ≤ 1 := (Finset.card_le_card
          (fun z hz => Finset.mem_singleton.mpr (h_all z hz))).trans
          (by simp only [Finset.card_singleton, le_refl])
        omega
      obtain ⟨b, hb, hne⟩ := h_exists_b; refine ⟨‖b - a‖, ?_⟩
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      exact ⟨a, ha, b, ⟨hb, hne⟩, rfl⟩
    let δ := dists.min' h_nonempty
    have hδ_pos : 0 < δ := by
      have h_mem := Finset.min'_mem dists h_nonempty
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at h_mem
      obtain ⟨s, hs, s', ⟨hs', hne⟩, heq⟩ := h_mem
      have h_pos : 0 < ‖s' - s‖ := hS_discrete s hs s' hs' hne.symm
      calc δ = ‖s' - s‖ := heq.symm
        _ > 0 := h_pos
    refine ⟨δ, hδ_pos, fun s hs s' hs' hne => ?_⟩
    have h_in : ‖s' - s‖ ∈ dists := by
      simp only [dists, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
      exact ⟨s, hs, s', ⟨hs', hne.symm⟩, rfl⟩
    exact Finset.min'_le dists _ h_in

/-- Variant of `finset_discrete_min_sep` with the more natural hypothesis that
`S.card > 1`. The conclusion uses `‖s₁ - s₂‖` (forward subtraction). -/
theorem finset_discrete_min_sep' {S : Finset ℂ} (hS : 1 < S.card) :
    ∃ δ > 0, ∀ s₁ ∈ S, ∀ s₂ ∈ S, s₁ ≠ s₂ → δ ≤ ‖s₁ - s₂‖ := by
  have hS_nonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨δ, hδ_pos, h_sep⟩ := finset_discrete_min_sep S hS_nonempty
    (fun s _ s' _ hne => norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
  exact ⟨δ, hδ_pos, fun s₁ hs₁ s₂ hs₂ hne =>
    h_sep s₂ hs₂ s₁ hs₁ hne.symm⟩

/-- Disjoint balls for sufficiently small epsilon. If all pairs in `S` are separated by
at least `δ`, then for `ε < δ / 2` the `ε`-balls around distinct points are disjoint. -/
theorem disjoint_balls_of_small_epsilon (S : Finset ℂ) (ε : ℝ) (δ : ℝ)
    (hε_small : ε < δ / 2)
    (h_sep : ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → δ ≤ ‖s' - s‖) :
    ∀ s ∈ S, ∀ s' ∈ S, s ≠ s' →
      Disjoint (Metric.ball s ε) (Metric.ball s' ε) := by
  intro s hs s' hs' hne; apply Metric.ball_disjoint_ball
  have h_sep' := h_sep s hs s' hs' hne
  have h2 : δ ≤ dist s s' := by rw [dist_eq_norm, norm_sub_rev]; exact h_sep'
  linarith

/-! ## Algebraic Operations on `cpvIntegrandOn` -/

/-- The multi-point CPV integrand distributes over subtraction pointwise. -/
theorem cpvIntegrandOn_sub (S : Finset ℂ) (f g : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S (fun z => f z - g z) γ ε t =
      cpvIntegrandOn S f γ ε t - cpvIntegrandOn S g γ ε t := by
  simp only [cpvIntegrandOn]; split_ifs <;> ring

/-- The multi-point CPV integrand distributes over addition pointwise. -/
theorem cpvIntegrandOn_add (S : Finset ℂ) (f g : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S (fun z => f z + g z) γ ε t =
      cpvIntegrandOn S f γ ε t + cpvIntegrandOn S g γ ε t := by
  simp only [cpvIntegrandOn]; split_ifs <;> ring

/-- The multi-point CPV integrand commutes with negation pointwise. -/
theorem cpvIntegrandOn_neg (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S (fun z => -f z) γ ε t = -cpvIntegrandOn S f γ ε t := by
  simp only [cpvIntegrandOn]; split_ifs <;> ring

/-- If there are no singularities near `γ(t)` for the larger set `T ⊇ S`,
then there are none for `S` either, so both integrands equal the full integrand. -/
theorem cpvIntegrandOn_subset_eq {S T : Finset ℂ} (hST : S ⊆ T) (f : ℂ → ℂ)
    (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ)
    (h_far : ∀ s ∈ T, ε < ‖γ t - s‖) :
    cpvIntegrandOn S f γ ε t = cpvIntegrandOn T f γ ε t := by
  have h_far_S : ∀ s ∈ S, ε < ‖γ t - s‖ := fun s hs => h_far s (hST hs)
  simp [cpvIntegrandOn_of_forall_gt h_far_S, cpvIntegrandOn_of_forall_gt h_far]

/-- Scalar multiplication distributes through the multi-point CPV integrand. -/
theorem cpvIntegrandOn_const_mul (S : Finset ℂ) (c : ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ)
    (ε : ℝ) (t : ℝ) :
    cpvIntegrandOn S (fun z => c * f z) γ ε t =
      c * cpvIntegrandOn S f γ ε t := by
  simp only [cpvIntegrandOn]
  split_ifs with h
  · simp
  · ring

/-! ## Algebraic Operations on `HasCauchyPVOn`

The algebra lemmas below require `IntervalIntegrable` hypotheses for the individual
CPV integrands. This is needed because `intervalIntegral.integral_sub` and
`intervalIntegral.integral_add` require integrability of both summands.

In practice, the downstream code (generalized residue theorem) will provide these
via continuity of the integrand away from the singular set, combined with boundedness
on compact sets.
-/

/-- Subtraction of multi-point CPV limits: if `HasCauchyPVOn S f γ L₁` and
`HasCauchyPVOn S g γ L₂`, then `HasCauchyPVOn S (f - g) γ (L₁ - L₂)`.

The integrability hypotheses are needed to split the integral of the difference
into a difference of integrals. -/
theorem HasCauchyPVOn.sub {S : Finset ℂ} {f g : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {L₁ L₂ : ℂ}
    (hf : HasCauchyPVOn S f γ L₁) (hg : HasCauchyPVOn S g γ L₂)
    (hfi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (hgi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S g γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S (fun z => f z - g z) γ (L₁ - L₂) := by
  simp only [HasCauchyPVOn] at hf hg ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => f z - g z) γ.toPath.extend ε t) =ᶠ[𝓝[>] 0]
      (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) -
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S g γ.toPath.extend ε t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [show (fun t => cpvIntegrandOn S (fun z => f z - g z) γ.toPath.extend ε t) =
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t -
        cpvIntegrandOn S g γ.toPath.extend ε t) from by
      ext t; simp only [cpvIntegrandOn]; split_ifs <;> ring]
    exact intervalIntegral.integral_sub (hfi ε hε) (hgi ε hε)
  exact (hf.sub hg).congr' heq.symm

/-- Addition of multi-point CPV limits: if `HasCauchyPVOn S f γ L₁` and
`HasCauchyPVOn S g γ L₂`, then `HasCauchyPVOn S (f + g) γ (L₁ + L₂)`. -/
theorem HasCauchyPVOn.add {S : Finset ℂ} {f g : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {L₁ L₂ : ℂ}
    (hf : HasCauchyPVOn S f γ L₁) (hg : HasCauchyPVOn S g γ L₂)
    (hfi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) volume 0 1)
    (hgi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S g γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S (fun z => f z + g z) γ (L₁ + L₂) := by
  simp only [HasCauchyPVOn] at hf hg ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => f z + g z) γ.toPath.extend ε t) =ᶠ[𝓝[>] 0]
      (fun ε => (∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) +
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S g γ.toPath.extend ε t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [show (fun t => cpvIntegrandOn S (fun z => f z + g z) γ.toPath.extend ε t) =
      (fun t => cpvIntegrandOn S f γ.toPath.extend ε t +
        cpvIntegrandOn S g γ.toPath.extend ε t) from by
      ext t; simp only [cpvIntegrandOn]; split_ifs <;> ring]
    exact intervalIntegral.integral_add (hfi ε hε) (hgi ε hε)
  exact (hf.add hg).congr' heq.symm

/-- Transfer via vanishing difference: if the multi-point CPV of `f - g` tends to `0`
and the multi-point CPV of `g` exists with limit `L`, then the multi-point CPV of `f`
exists with limit `L`.

This is the key composition lemma for the generalized residue theorem: decompose
`f = g + (f - g)` where `g` is an explicit residue sum with known CPV, and show the
difference `f - g` has vanishing CPV. -/
theorem hasCauchyPVOn_of_tendsto_sub {S : Finset ℂ} {f g : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {L : ℂ}
    (hfg : HasCauchyPVOn S (fun z => f z - g z) γ 0)
    (hg : HasCauchyPVOn S g γ L)
    (hfgi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S (fun z => f z - g z) γ.toPath.extend ε t) volume 0 1)
    (hgi : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S g γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S f γ L := by
  simp only [HasCauchyPVOn] at hfg hg ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) =ᶠ[𝓝[>] 0]
      (fun ε =>
        (∫ t in (0 : ℝ)..1,
          cpvIntegrandOn S (fun z => f z - g z) γ.toPath.extend ε t) +
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S g γ.toPath.extend ε t)) := by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    rw [show (fun t => cpvIntegrandOn S f γ.toPath.extend ε t) =
      (fun t => cpvIntegrandOn S (fun z => f z - g z) γ.toPath.extend ε t +
        cpvIntegrandOn S g γ.toPath.extend ε t) from by
      ext t; simp only [cpvIntegrandOn]; split_ifs <;> ring]
    exact intervalIntegral.integral_add (hfgi ε hε) (hgi ε hε)
  have h_sum : Tendsto
      (fun ε =>
        (∫ t in (0 : ℝ)..1,
          cpvIntegrandOn S (fun z => f z - g z) γ.toPath.extend ε t) +
        (∫ t in (0 : ℝ)..1, cpvIntegrandOn S g γ.toPath.extend ε t))
      (𝓝[>] 0) (𝓝 L) := by
    convert hfg.add hg using 1; simp only [zero_add]
  exact h_sum.congr' heq.symm

/-! ## Connection between single-point and multi-point CPV -/

/-- A `HasCauchyPV` at a single point implies `HasCauchyPVOn` for the singleton set. -/
theorem hasCauchyPVOn_singleton_of_hasCauchyPV {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV f γ z₀ L) : HasCauchyPVOn {z₀} f γ L := by
  simp only [HasCauchyPV, HasCauchyPVOn] at h ⊢
  refine h.congr (fun ε => ?_)
  apply intervalIntegral.integral_congr
  intro t _
  rw [← cpvIntegrand_eq_cpvIntegrandOn_singleton]

/-- A `HasCauchyPVOn` for a singleton set implies `HasCauchyPV` at that point. -/
theorem hasCauchyPV_of_hasCauchyPVOn_singleton {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVOn {z₀} f γ L) : HasCauchyPV f γ z₀ L := by
  simp only [HasCauchyPV, HasCauchyPVOn] at h ⊢
  refine h.congr (fun ε => ?_)
  apply intervalIntegral.integral_congr
  intro t _
  exact cpvIntegrand_eq_cpvIntegrandOn_singleton.symm

end
