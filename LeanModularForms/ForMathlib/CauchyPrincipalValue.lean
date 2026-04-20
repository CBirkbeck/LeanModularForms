/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Mathlib.Topology.Order.DenselyOrdered

/-!
# Cauchy Principal Value Integrals along Piecewise C¹ Paths

This file defines the Cauchy principal value (CPV) of a contour integral along a
piecewise C¹ path, both for a single singularity and for a finite set of singularities.

## Main definitions

### Single-point CPV

* `cpvIntegrand f γ z₀ ε t` — the ε-cutoff integrand: equals `f(γ(t)) · γ'(t)` when
  `‖γ(t) - z₀‖ > ε`, and `0` otherwise.

* `HasCauchyPV f γ z₀ L` — the **primary API predicate**: the limit of the cutoff integral
  as `ε → 0⁺` exists and equals `L`. Defined via `Tendsto`.

* `cauchyPV f γ z₀` — the CPV value, defined via `limUnder`. Returns junk when the limit
  does not exist.

* `HasCauchyPV.cauchyPV_eq` — bridge: `HasCauchyPV f γ z₀ L → cauchyPV f γ z₀ = L`.

### Multi-point CPV

* `cpvIntegrandOn S f γ ε t` — zero near any `s ∈ S`, otherwise `f(γ(t)) · γ'(t)`.

* `HasCauchyPVOn S f γ L` — multi-point Tendsto predicate.

* `cauchyPVOn S f γ` — multi-point CPV value via `limUnder`.

* `HasCauchyPVOn.cauchyPVOn_eq` — bridge for the multi-point case.

### Basic API

* `HasCauchyPV.neg` — `HasCauchyPV f γ z₀ L → HasCauchyPV (-f) γ z₀ (-L)`
* `HasCauchyPV.smul` — scalar multiplication
* `hasCauchyPV_of_avoids` — if `γ` avoids `z₀`, CPV equals the ordinary contour integral

## Design notes

The `HasCauchyPV` predicate (Tendsto-based) is the **primary API**. All downstream
theorems should be stated using it. The `cauchyPV` value (limUnder-based) is secondary —
only used when extracting a concrete value is needed.

## References

* K. Hungerbühler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology MeasureTheory Complex
open scoped Interval

noncomputable section

variable {x y : ℂ}

/-! ### Single-point CPV integrand -/

/-- The ε-cutoff integrand for the Cauchy principal value at a single point `z₀`.
Returns `f(γ(t)) · γ'(t)` when `‖γ(t) - z₀‖ > ε`, and `0` otherwise. -/
def cpvIntegrand (f : ℂ → ℂ) (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

@[simp]
theorem cpvIntegrand_of_gt {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ}
    (h : ε < ‖γ t - z₀‖) :
    cpvIntegrand f γ z₀ ε t = f (γ t) * deriv γ t := by
  simp only [cpvIntegrand, h, ite_true]

@[simp]
theorem cpvIntegrand_of_le {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε : ℝ} {t : ℝ}
    (h : ‖γ t - z₀‖ ≤ ε) :
    cpvIntegrand f γ z₀ ε t = 0 := by
  simp only [cpvIntegrand, not_lt.mpr h, ite_false]

theorem cpvIntegrand_nonneg_eps {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ} {ε₁ ε₂ : ℝ} {t : ℝ}
    (hε : ε₂ ≤ ε₁) (h : cpvIntegrand f γ z₀ ε₁ t ≠ 0) :
    cpvIntegrand f γ z₀ ε₂ t = cpvIntegrand f γ z₀ ε₁ t := by
  have h₁ : ε₁ < ‖γ t - z₀‖ := by
    simp only [cpvIntegrand] at h; split_ifs at h with hgt <;> [exact hgt; exact absurd rfl h]
  simp only [cpvIntegrand, lt_of_le_of_lt hε h₁, ite_true, h₁, ite_true]

/-! ### HasCauchyPV: the primary Tendsto-based predicate -/

/-- The Cauchy principal value of `∮_γ f(z) dz` exists and equals `L`, where the integral
is computed by excluding ε-neighborhoods of `z₀` and taking the limit as `ε → 0⁺`.

This is the **primary API predicate** for CPV integrals. -/
def HasCauchyPV (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (z₀ : ℂ) (L : ℂ) : Prop :=
  Tendsto (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t)
    (𝓝[>] 0) (𝓝 L)

/-- The Cauchy principal value of `∮_γ f(z) dz`, excluding ε-neighborhoods of `z₀`.
Returns junk when the limit does not exist. -/
def cauchyPV (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t

/-- Bridge theorem: if `HasCauchyPV f γ z₀ L`, then `cauchyPV f γ z₀ = L`. -/
theorem HasCauchyPV.cauchyPV_eq {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV f γ z₀ L) : cauchyPV f γ z₀ = L :=
  h.limUnder_eq

/-! ### Basic API for HasCauchyPV -/

/-- Negation: `HasCauchyPV f γ z₀ L → HasCauchyPV (-f) γ z₀ (-L)`. -/
theorem HasCauchyPV.neg {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPV f γ z₀ L) : HasCauchyPV (fun z => -f z) γ z₀ (-L) := by
  simp only [HasCauchyPV] at h ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrand (fun z => -f z) γ.toPath.extend z₀ ε t) =
      fun ε => -(∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t) := by
    ext ε
    simp only [cpvIntegrand, neg_mul, ← intervalIntegral.integral_neg]
    congr 1; ext t; split_ifs <;> simp only [neg_zero]
  rw [heq]
  exact h.neg

/-- Scalar multiplication: `HasCauchyPV f γ z₀ L → HasCauchyPV (c • f) γ z₀ (c * L)`. -/
theorem HasCauchyPV.smul {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ} {L : ℂ}
    (c : ℂ) (h : HasCauchyPV f γ z₀ L) :
    HasCauchyPV (fun z => c * f z) γ z₀ (c * L) := by
  simp only [HasCauchyPV] at h ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrand (fun z => c * f z) γ.toPath.extend z₀ ε t) =
      fun ε => c * (∫ t in (0 : ℝ)..1, cpvIntegrand f γ.toPath.extend z₀ ε t) := by
    ext ε
    rw [show (fun t => cpvIntegrand (fun z => c * f z) γ.toPath.extend z₀ ε t) =
      (fun t => c * cpvIntegrand f γ.toPath.extend z₀ ε t)
      from funext fun t => by simp only [cpvIntegrand]; split_ifs <;> ring]
    exact intervalIntegral.integral_const_mul c _
  rw [heq]
  exact h.const_mul c

/-- If `γ` avoids `z₀` (minimum distance `δ > 0`), then the CPV equals the ordinary
contour integral, since the cutoff integrand equals the full integrand for small `ε`. -/
theorem hasCauchyPV_of_avoids {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - z₀‖) :
    HasCauchyPV f γ z₀ (γ.contourIntegral f) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  simp only [HasCauchyPV, PiecewiseC1Path.contourIntegral]
  apply Tendsto.congr' _ tendsto_const_nhds
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Ioo 0 δ, Ioo_mem_nhdsGT hδ_pos,
    fun ε hε => by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have h_gt : ε < ‖γ.toPath.extend t - z₀‖ :=
        lt_of_lt_of_le hε.2 (hδ_bound t ht)
      exact (cpvIntegrand_of_gt h_gt).symm⟩

/-! ### Multi-point CPV integrand -/

/-- Multi-point CPV integrand: zero near any `s ∈ S`, else `f(γ(t)) · γ'(t)`. -/
def cpvIntegrandOn (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0
  else f (γ t) * deriv γ t

@[simp]
theorem cpvIntegrandOn_of_forall_gt {S : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {ε : ℝ} {t : ℝ}
    (h : ∀ s ∈ S, ε < ‖γ t - s‖) :
    cpvIntegrandOn S f γ ε t = f (γ t) * deriv γ t := by
  simp only [cpvIntegrandOn]
  rw [if_neg]
  push Not
  exact h

@[simp]
theorem cpvIntegrandOn_of_exists_le {S : Finset ℂ} {f : ℂ → ℂ} {γ : ℝ → ℂ} {ε : ℝ} {t : ℝ}
    (h : ∃ s ∈ S, ‖γ t - s‖ ≤ ε) :
    cpvIntegrandOn S f γ ε t = 0 := by
  simp only [cpvIntegrandOn, h, ite_true]

theorem cpvIntegrandOn_empty {f : ℂ → ℂ} {γ : ℝ → ℂ} {ε : ℝ} {t : ℝ} :
    cpvIntegrandOn ∅ f γ ε t = f (γ t) * deriv γ t := by
  simp [cpvIntegrandOn]

/-- Single-point CPV integrand agrees with multi-point CPV integrand for a singleton. -/
theorem cpvIntegrand_eq_cpvIntegrandOn_singleton {f : ℂ → ℂ} {γ : ℝ → ℂ} {z₀ : ℂ}
    {ε : ℝ} {t : ℝ} :
    cpvIntegrand f γ z₀ ε t = cpvIntegrandOn {z₀} f γ ε t := by
  simp only [cpvIntegrand, cpvIntegrandOn, Finset.mem_singleton, exists_eq_left]
  split_ifs with h1 h2 <;> first | rfl | linarith

/-! ### HasCauchyPVOn: multi-point Tendsto predicate -/

/-- The multi-point Cauchy principal value of `∮_γ f(z) dz` exists and equals `L`,
where the integral is computed by excluding ε-neighborhoods of all points in `S`
and taking the limit as `ε → 0⁺`. -/
def HasCauchyPVOn (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) (L : ℂ) : Prop :=
  Tendsto (fun ε => ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t)
    (𝓝[>] 0) (𝓝 L)

/-- The multi-point Cauchy principal value of `∮_γ f(z) dz`.
Returns junk when the limit does not exist. -/
def cauchyPVOn (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x y) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t

/-- Bridge theorem: if `HasCauchyPVOn S f γ L`, then `cauchyPVOn S f γ = L`. -/
theorem HasCauchyPVOn.cauchyPVOn_eq {S : Finset ℂ} {f : ℂ → ℂ}
    {γ : PiecewiseC1Path x y} {L : ℂ}
    (h : HasCauchyPVOn S f γ L) : cauchyPVOn S f γ = L :=
  h.limUnder_eq

/-! ### Basic API for HasCauchyPVOn -/

/-- Negation for multi-point CPV. -/
theorem HasCauchyPVOn.neg {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {L : ℂ}
    (h : HasCauchyPVOn S f γ L) : HasCauchyPVOn S (fun z => -f z) γ (-L) := by
  simp only [HasCauchyPVOn] at h ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => -f z) γ.toPath.extend ε t) =
      fun ε => -(∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) := by
    ext ε
    simp only [cpvIntegrandOn, neg_mul, ← intervalIntegral.integral_neg]
    congr 1; ext t; split_ifs <;> simp only [neg_zero]
  rw [heq]
  exact h.neg

/-- Scalar multiplication for multi-point CPV. -/
theorem HasCauchyPVOn.smul {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {L : ℂ}
    (c : ℂ) (h : HasCauchyPVOn S f γ L) :
    HasCauchyPVOn S (fun z => c * f z) γ (c * L) := by
  simp only [HasCauchyPVOn] at h ⊢
  have heq : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => c * f z) γ.toPath.extend ε t) =
      fun ε => c * (∫ t in (0 : ℝ)..1, cpvIntegrandOn S f γ.toPath.extend ε t) := by
    ext ε
    rw [show (fun t => cpvIntegrandOn S (fun z => c * f z) γ.toPath.extend ε t) =
      (fun t => c * cpvIntegrandOn S f γ.toPath.extend ε t)
      from funext fun t => by simp only [cpvIntegrandOn]; split_ifs <;> ring]
    exact intervalIntegral.integral_const_mul c _
  rw [heq]
  exact h.const_mul c

/-- If `γ` avoids all points in `S`, the multi-point CPV equals the ordinary
contour integral. -/
theorem hasCauchyPVOn_of_avoids {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x y}
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖) :
    HasCauchyPVOn S f γ (γ.contourIntegral f) := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  simp only [HasCauchyPVOn, PiecewiseC1Path.contourIntegral]
  apply Tendsto.congr' _ tendsto_const_nhds
  rw [Filter.eventuallyEq_iff_exists_mem]
  exact ⟨Ioo 0 δ, Ioo_mem_nhdsGT hδ_pos,
    fun ε hε => by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      have h_forall : ∀ s ∈ S, ε < ‖γ.toPath.extend t - s‖ :=
        fun s hs => lt_of_lt_of_le hε.2 (hδ_bound s hs t ht)
      exact (cpvIntegrandOn_of_forall_gt h_forall).symm⟩

/-- The multi-point CPV for an empty set equals the ordinary contour integral. -/
theorem hasCauchyPVOn_empty {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} :
    HasCauchyPVOn ∅ f γ (γ.contourIntegral f) := by
  simp only [HasCauchyPVOn, PiecewiseC1Path.contourIntegral]
  apply Tendsto.congr _ tendsto_const_nhds
  intro ε
  apply intervalIntegral.integral_congr
  intro t _
  exact cpvIntegrandOn_empty.symm

/-! ### Uniqueness -/

/-- The limit in `HasCauchyPV` is unique. -/
theorem HasCauchyPV.unique {f : ℂ → ℂ} {γ : PiecewiseC1Path x y} {z₀ : ℂ}
    {L₁ L₂ : ℂ} (h₁ : HasCauchyPV f γ z₀ L₁) (h₂ : HasCauchyPV f γ z₀ L₂) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

/-- The limit in `HasCauchyPVOn` is unique. -/
theorem HasCauchyPVOn.unique {S : Finset ℂ} {f : ℂ → ℂ} {γ : PiecewiseC1Path x y}
    {L₁ L₂ : ℂ} (h₁ : HasCauchyPVOn S f γ L₁) (h₂ : HasCauchyPVOn S f γ L₂) :
    L₁ = L₂ :=
  tendsto_nhds_unique h₁ h₂

end
