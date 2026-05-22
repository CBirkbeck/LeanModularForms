/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.SlashActionAuxil
import LeanModularForms.Eigenforms.ConductorTheorem
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import LeanModularForms.HeckeRIngs.GL2.Newforms.FrickeTwist

/-!
# Newforms: Fricke slash-equality input and completed Mellin-Dirichlet bridges

The per-newform full Dirichlet-zero data, the Fricke slash-equality structured input and its H1 consumers, the corrected completed Mellin-Dirichlet bridge (T133), the corrected Fricke / completed Mellin data (T134), and the Euler-stripping arithmetic / Hecke-multiplicative-structure inputs.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-- **Per-newform full T111 Dirichlet-zero data (T132 H2 named structure).**

Packages the per-newform classical inputs needed by
`Newform.full_pole_witness_data_of_dirichletZero` as a single named
structure with explicit fields, eliminating the bulky multi-clause
hypothesis at SMO consumer call sites.

**Fields.**

* `T : Finset Nat.Primes` — exceptional primes coprime to `N`
  (typically the primes in `S` coprime to `N`).
* `s₀ : ℂ` — the pole point in the strip `Re < 1`.
* `h_zero` — the irreducible classical Dirichlet-L-zero input.
* `h_num_LF_ne` — squared-character L-value non-cancellation.
* `h_factors_ne` — per-prime non-vanishing in finite Euler factors.
* `h_num_an`, `h_den_an` — local analyticity at `s₀`.
* `h_den_finite` — finite analytic order of full denominator.
* `h_clause` — universal-F clause from T111 + extension uniqueness.

**Use.**  Downstream SMO consumers can take a single
`PerNewformFullDirichletData f χ S` value per `(f, χ, S)` instead of
the giant existential `∃ T s₀, ...` hypothesis cluster, keeping the
SMO-facing API compact.  See
`Newform.full_pole_witness_data_of_PerNewformFullDirichletData` for
the bridge to the inner `∃` shape required by upstream consumers. -/
structure Newform.PerNewformFullDirichletData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) where
  /-- Exceptional primes finset (coprime to `N`). -/
  T : Finset Nat.Primes
  /-- Pole point — a Dirichlet zero of `LFunction χ̃` in the critical strip. -/
  s₀ : ℂ
  /-- The Dirichlet zero (the single irreducible classical input). -/
  h_zero : DirichletCharacter.LFunction
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0
  /-- Squared-character L-value non-cancellation at the doubled image point. -/
  h_num_LF_ne : DirichletCharacter.LFunction
    (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0
  /-- Per-prime non-vanishing of finite Euler-factor numerator entries. -/
  h_factors_ne : ∀ p ∈ T,
    Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
    (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0
  /-- Analyticity of the full T111 numerator at `s₀`. -/
  h_num_an : AnalyticAt ℂ
    (fun s =>
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
      ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀
  /-- Analyticity of the full T111 denominator at `s₀`. -/
  h_den_an : AnalyticAt ℂ
    (fun s =>
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s - k + 1) *
      ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀
  /-- Finite analytic order of full T111 denominator at `s₀`. -/
  h_den_finite : meromorphicOrderAt
    (fun s =>
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s - k + 1) *
      ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤
  /-- Universal-F clause from T111 + extension uniqueness. -/
  h_clause : Newform.FullDirichletQuotientUniversalFClause f χ S T s₀

/-- **Bridge: per-newform structured Dirichlet data ⇒ inner `∃`-shape
witness for full pole-witness data (T132 H2 step).**

Packages `Newform.PerNewformFullDirichletData f χ S` into the
existential-data shape consumed by
`Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate`
and the SMO consumer chain. -/
theorem Newform.full_pole_witness_data_of_PerNewformFullDirichletData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (D : Newform.PerNewformFullDirichletData f χ S) :
    ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
      AnalyticAt ℂ
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
          ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
      AnalyticAt ℂ
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
      (DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
        (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
      (DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s₀ - k + 1) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
      meromorphicOrderAt
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
      Newform.FullDirichletQuotientUniversalFClause f χ S T s₀ :=
  Newform.full_pole_witness_data_of_dirichletZero f χ S D.T D.s₀
    D.h_zero D.h_num_LF_ne D.h_factors_ne D.h_num_an D.h_den_an
    D.h_den_finite D.h_clause

/-- **`T = ∅` PerNewformFullDirichletData constructor from purely
classical inputs (T132 H2 sub-reduction).**

For the `T = ∅` specialization (no exceptional primes coprime to `N`),
the per-newform `Newform.PerNewformFullDirichletData f χ S` reduces to
the truly irreducible classical inputs:

* character non-trivialities `χ̃ ≠ 1`, `χ̃² ≠ 1`,
* the Dirichlet zero `LFunction χ̃ (2 s₀ - k + 1) = 0`,
* the squared-character L-value non-cancellation
  `LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0`,
* the universal-F clause.

The `T = ∅` finite Euler-factor products collapse to `1`, so:

* `h_factors_ne` is vacuous,
* `h_num_an` reduces to `LFunction χ̃² ∘ (s ↦ 2(2s-k+1))` analytic,
  derived from `differentiable_LFunction h_chi_sq_ne_one` + composition,
* `h_den_an` reduces to `LFunction χ̃ ∘ (s ↦ 2s-k+1)` analytic, derived
  from `differentiable_LFunction h_χ_ne_one` + composition,
* `h_den_finite` is derived from non-triviality of `LFunction χ̃` (it
  equals `LSeries χ̃ ≠ 0` on `Re > 1`), using
  `AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected` on `ℂ`. -/
noncomputable def Newform.PerNewformFullDirichletData_T_empty_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_LF_ne : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_clause : Newform.FullDirichletQuotientUniversalFClause f χ S ∅ s₀) :
    Newform.PerNewformFullDirichletData f χ S where
  T := ∅
  s₀ := s₀
  h_zero := h_zero
  h_num_LF_ne := h_num_LF_ne
  h_factors_ne := fun p hp => absurd hp (Finset.notMem_empty p)
  h_num_an := by
    -- For T = ∅, the finite product is 1, so num = LFunction χ̃² ∘ affine.
    have h_diff : Differentiable ℂ (fun s : ℂ =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        ∏ p ∈ (∅ : Finset Nat.Primes), Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) := by
      simp only [Finset.prod_empty, mul_one]
      exact (DirichletCharacter.differentiable_LFunction h_chi_sq_ne_one).comp (by fun_prop)
    exact Complex.analyticOnNhd_univ_iff_differentiable.mpr h_diff s₀ (Set.mem_univ _)
  h_den_an := by
    have h_diff : Differentiable ℂ (fun s : ℂ =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) *
        ∏ p ∈ (∅ : Finset Nat.Primes),
          (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) := by
      simp only [Finset.prod_empty, mul_one]
      exact (DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop)
    exact Complex.analyticOnNhd_univ_iff_differentiable.mpr h_diff s₀ (Set.mem_univ _)
  h_den_finite := by
    -- den (T = ∅) = LFunction χ̃ ∘ (s ↦ 2 s - k + 1) (the finite product is 1).
    -- Since LFunction χ̃ is non-trivial entire (equals LSeries χ̃ ≠ 0 on Re > 1),
    -- it has finite analytic order everywhere, hence so does the affine
    -- composition.
    set den_fn : ℂ → ℂ := fun s =>
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) *
      ∏ p ∈ (∅ : Finset Nat.Primes),
        (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ with hden
    have h_diff : Differentiable ℂ den_fn := by
      simp only [den_fn, Finset.prod_empty, mul_one]
      exact (DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop)
    have h_an_univ : AnalyticOnNhd ℂ den_fn Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr h_diff
    set s' : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ) with hs'_def
    have h_re : (2 * s' - (k : ℂ) + 1).re = 5 := by
      simp [s', Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.intCast_re, Complex.intCast_im]
      ring
    have h_re_gt_one : (1 : ℝ) < (2 * s' - (k : ℂ) + 1).re := by rw [h_re]; norm_num
    have h_value_ne_at_s' : den_fn s' ≠ 0 := by
      simp only [den_fn, Finset.prod_empty, mul_one]
      rw [DirichletCharacter.LFunction_eq_LSeries _ h_re_gt_one]
      exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ h_re_gt_one
    have h_an_s' : AnalyticAt ℂ den_fn s' := h_an_univ s' (Set.mem_univ _)
    have h_an_s₀ : AnalyticAt ℂ den_fn s₀ := h_an_univ s₀ (Set.mem_univ _)
    have h_order_s' : analyticOrderAt den_fn s' = 0 :=
      h_an_s'.analyticOrderAt_eq_zero.mpr h_value_ne_at_s'
    have h_order_s'_ne_top : analyticOrderAt den_fn s' ≠ ⊤ := by
      rw [h_order_s']; exact ENat.zero_ne_top
    have h_order_s₀_ne_top : analyticOrderAt den_fn s₀ ≠ ⊤ :=
      AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected h_an_univ
        isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) h_order_s'_ne_top
    rw [h_an_s₀.meromorphicOrderAt_eq]
    intro h
    rcases ENat.ne_top_iff_exists.mp h_order_s₀_ne_top with ⟨n, hn⟩
    rw [← hn] at h
    simp at h
  h_clause := h_clause

/-- **Per-prime denominator-factor analyticity (T132 H2 helper).**

The denominator-side per-prime factor in `FullDirichletQuotientUniversalFClause`
and `PerNewformFullDirichletData` —
`s ↦ (1 - χ̃²(p) · p^{-(2(2s-k+1))})⁻¹` — is analytic at any point `s₀`
where the underlying `1 - χ̃²(p) · p^{-(2(2s₀-k+1))}` does not vanish.

**Proof.**  The base function `s ↦ p^{-(2(2s-k+1))}` is analytic
everywhere via `AnalyticAt.cpow` (constant base in `slitPlane` since
`(p : ℂ) ≠ 0` for any prime).  Combined with constant ring operations,
`s ↦ 1 - χ̃²(p) · p^{-(2(2s-k+1))}` is entire.  At `s₀` where the value
is nonzero, the inverse is analytic via `AnalyticAt.inv`. -/
theorem Newform.den_factor_analytic_at
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ) (s₀ : ℂ) (p : Nat.Primes)
    (h_ne : (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) :
    AnalyticAt ℂ
      (fun (s : ℂ) => (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ := by
  have h_p_slit : ((p : ℕ) : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.natCast_mem_slitPlane]
    exact (p.prop.pos).ne'
  have h_cpow : AnalyticAt ℂ
      (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))) s₀ := by
    refine AnalyticAt.cpow analyticAt_const ?_ h_p_slit
    fun_prop
  have h_full : AnalyticAt ℂ
      (fun (s : ℂ) => 1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))) s₀ :=
    analyticAt_const.sub (analyticAt_const.mul h_cpow)
  exact h_full.inv h_ne

/-- **General-`T` classical-inputs constructor for `PerNewformFullDirichletData`
(T132 H2 step).**

The general-`T` analogue of
`Newform.PerNewformFullDirichletData_T_empty_of_classicalInputs`.  The
mechanical analyticity fields `h_num_an`, `h_den_an` are assembled from
per-prime factor analyticity hypotheses via `AnalyticAt.mul` and
`Finset.analyticAt_fun_prod` (the LFunction piece is automatic from
`differentiable_LFunction`).  `h_den_finite` remains explicit since for
general `T` it requires non-vanishing of the denominator's finite
product at a witness point with `Re > 1`.

**Per-prime explicit factor-analyticity hypotheses** (avoid the
`Complex.cpow` analyticity API lookup; cusp-form callers can
discharge each via local computation):

* `h_num_factor_an : ∀ p ∈ T, AnalyticAt ℂ (combined num factor) s₀`.
* `h_den_factor_an : ∀ p ∈ T, AnalyticAt ℂ (den correction factor) s₀`. -/
noncomputable def Newform.PerNewformFullDirichletData_of_classicalInputs
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_LF_ne : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_factors_ne : ∀ p ∈ T,
      Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_num_factor_an : ∀ p ∈ T, AnalyticAt ℂ
      (fun s => Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_factor_an : ∀ p ∈ T, AnalyticAt ℂ
      (fun (s : ℂ) => (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀)
    (h_den_finite :
      meromorphicOrderAt
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤)
    (h_clause : Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    Newform.PerNewformFullDirichletData f χ S where
  T := T
  s₀ := s₀
  h_zero := h_zero
  h_num_LF_ne := h_num_LF_ne
  h_factors_ne := h_factors_ne
  h_num_an := by
    refine AnalyticAt.mul ?_ ?_
    · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        ((DirichletCharacter.differentiable_LFunction h_chi_sq_ne_one).comp
          (by fun_prop))) s₀ (Set.mem_univ _)
    · exact Finset.analyticAt_fun_prod _ h_num_factor_an
  h_den_an := by
    refine AnalyticAt.mul ?_ ?_
    · exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr
        ((DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp
          (by fun_prop))) s₀ (Set.mem_univ _)
    · exact Finset.analyticAt_fun_prod _ h_den_factor_an
  h_den_finite := h_den_finite
  h_clause := h_clause

/-- **General-`T` classical-inputs constructor — reduced denominator-side
analyticity hypothesis (T132 H2 helper).**

A reduction of `Newform.PerNewformFullDirichletData_of_classicalInputs`
that **drops the per-prime denominator-factor analyticity hypothesis**
`h_den_factor_an`, deriving it instead from the per-prime non-vanishing
hypothesis `h_factors_ne` via `Newform.den_factor_analytic_at`.

The numerator-side per-prime analyticity hypothesis `h_num_factor_an`
remains explicit because the cusp-form-specific
`Newform.eulerFactor_stripped` term (in the `(p : ℕ) ∈ S` branch) is a
tail-sum whose analyticity is not a simple `cpow`-side computation.

This is the first reduction in the H2 chain that uses Mathlib's
`AnalyticAt.cpow` to discharge a previously-explicit per-prime
hypothesis automatically. -/
noncomputable def Newform.PerNewformFullDirichletData_of_classicalInputs_redDen
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_LF_ne : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_factors_ne : ∀ p ∈ T,
      Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_den_factors_ne : ∀ p ∈ T,
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0)
    (h_num_factor_an : ∀ p ∈ T, AnalyticAt ℂ
      (fun s => Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_finite :
      meromorphicOrderAt
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤)
    (h_clause : Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    Newform.PerNewformFullDirichletData f χ S :=
  Newform.PerNewformFullDirichletData_of_classicalInputs f χ S T s₀
    h_χ_ne_one h_chi_sq_ne_one h_zero h_num_LF_ne h_factors_ne
    h_num_factor_an
    (fun p hp => Newform.den_factor_analytic_at χ s₀ p (h_den_factors_ne p hp))
    h_den_finite h_clause

/-- **General-`T` PerNewformFullDirichletData constructor that derives the
universal-F clause from T111 (T132 H2 SMO consumer step).**

Drops the explicit `h_clause : FullDirichletQuotientUniversalFClause`
hypothesis from `Newform.PerNewformFullDirichletData_of_classicalInputs_redDen`,
deriving it instead from
`Newform.FullDirichletQuotientUniversalFClause_of_T111` using the
classical T111 ingredients (cusp-form character eigenspace membership,
bad-prime-zero, finset characterisation of T, abscissa bound, Euler-
factor product entirety).

This is the SMO-pole-witness consumer that uses the new T111 universal-
F-clause bridge in place of the previously-arbitrary clause hypothesis. -/
noncomputable def Newform.PerNewformFullDirichletData_of_classicalInputs_T111
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    (T : Finset Nat.Primes)
    (hT_iff : ∀ p : Nat.Primes, p ∈ T ↔
      (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped <
      (((k : ℝ) / 2 + 1 : ℝ) : EReal))
    (h_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_LF_ne : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_factors_ne : ∀ p ∈ T,
      Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_den_factors_ne : ∀ p ∈ T,
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0)
    (h_EFP_diff : Differentiable ℂ
      (fun s : ℂ => ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p))
    (h_num_factor_an : ∀ p ∈ T, AnalyticAt ℂ
      (fun s => Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_finite :
      meromorphicOrderAt
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤) :
    Newform.PerNewformFullDirichletData f χ S :=
  Newform.PerNewformFullDirichletData_of_classicalInputs_redDen
    f χ S T s₀ h_χ_ne_one h_chi_sq_ne_one h_zero h_num_LF_ne h_factors_ne
    h_den_factors_ne h_num_factor_an h_den_finite
    (Newform.FullDirichletQuotientUniversalFClause_of_T111 f χ hfχ S h_bad T hT_iff s₀
      h_χ_ne_one h_chi_sq_ne_one h_abscissa_lt h_EFP_diff
      (fun p hp => (h_factors_ne p hp).2)
      h_den_factors_ne)

/-- **Strong Multiplicity One via per-newform Dirichlet-zero data
+ Hecke continuation + newform_unique (T132 H2 reduction, SMO-facing).**

Replaces the giant `h_data` blob of
`strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique`
with the smallest currently-formalisable per-newform classical
hypothesis cluster (Dirichlet zero in the strip + local non-cancellation
+ analyticity + universal-F clause).  The hypothesis is now expressed
as named individual fields per newform-character pair, derived from
the underlying Dirichlet-zero certificate via
`Newform.full_pole_witness_data_of_dirichletZero`.

This is the strongest SMO-facing consumer of T132's analytic chain
that does **not** assume a yet-unformalised classical theorem beyond
the Dirichlet-zero existence in the strip `Re < 1`. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZero_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_hecke : Newform.HeckeEntireExtension)
    (h_dirZero : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          (∀ p ∈ T,
            Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0) ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique
    h_unique h_hecke ?_ f g χ hfχ hgχ S h
  intro N _ k f χ hfχ S h_bad
  obtain ⟨T, s₀, h_zero, h_num_LF_ne, h_factors, h_num_an, h_den_an, h_den_finite, h_clause⟩ :=
    h_dirZero f χ hfχ S h_bad
  exact Newform.full_pole_witness_data_of_dirichletZero f χ S T s₀
    h_zero h_num_LF_ne h_factors h_num_an h_den_an h_den_finite h_clause

/-- **Strong Multiplicity One via per-newform `HeckeFEData` + per-newform
Dirichlet-zero data + `newform_unique` (T132 H1+H2 reduction, SMO-facing).**

Replaces the global black-box `h_hecke : Newform.HeckeEntireExtension`
hypothesis with the per-newform structured `Newform.HeckeFEData` data
(Mathlib `StrongFEPair` + bridge equation), and chains through the
per-newform Dirichlet-zero hypothesis cluster of
`strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZero_of_newformUnique`.

This is the strongest SMO-facing consumer of T132's analytic chain
that uses Mathlib's Mellin / functional-equation infrastructure
(`StrongFEPair.differentiable_Λ`) directly, plus the per-newform
Dirichlet-zero classical input. -/
theorem strongMultiplicityOne_of_HeckeFEData_of_dirichletZero_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_dirZero : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          (∀ p ∈ T,
            Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0) ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZero_of_newformUnique
    h_unique (Newform.HeckeEntireExtension_of_HeckeFEData h_FE) h_dirZero
    f g χ hfχ hgχ S h

/-- **Strong Multiplicity One via per-newform `HeckeFEData`
+ per-newform `PerNewformFullDirichletData` + `newform_unique`
(T132 H1 + H2 endpoint).**

The SMO-facing endpoint that consumers should target.  Takes:

* `h_unique` — Atkin-Lehner uniqueness (standard);
* `h_FE` — per-newform `Newform.HeckeFEData` (Mathlib `StrongFEPair` +
  bridge equation, packaging Hecke 1936 entire continuation);
* `h_data` — per-newform `Newform.PerNewformFullDirichletData`
  (named-field Dirichlet-zero data: pole point `s₀`, the irreducible
  classical Dirichlet zero, finite Euler-factor non-cancellation,
  local analyticity, universal-F clause).

The conclusion is `f.toCuspForm = g.toCuspForm` for any two newforms
agreeing on cofinite-coprime eigenvalues.

**Remaining classical obligation.**  The single field
`Newform.PerNewformFullDirichletData.h_zero` carries the irreducible
Dirichlet-L-zero existence (in `Re < 1`) — the precise Miyake
§4.5.15 / Diamond-Shurman §5.9 input that is not yet a single
named lemma in Mathlib.  All other hypotheses are mechanical local
analytic facts. -/
theorem strongMultiplicityOne_of_HeckeFEData_of_PerNewformFullDirichletData_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  have h_no_ext : Newform.NoEntireExtensionUnderBadPrime :=
    Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
      (fun N _ k f χ hfχ S h_bad =>
        Newform.full_pole_witness_data_of_PerNewformFullDirichletData f χ S
          (h_data f χ hfχ S h_bad))
  have h_hecke : Newform.HeckeEntireExtension :=
    Newform.HeckeEntireExtension_of_HeckeFEData h_FE
  have h_ana : Newform.AnalyticContradiction :=
    Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
      h_hecke h_no_ext
  exact strongMultiplicityOne_of_analyticContradiction_of_newformUnique
    h_unique h_ana f g χ hfχ hgχ S h

/-- **SMO endpoint via `HeckeFEData` + classical T111 inputs +
`newform_unique` (T132 H2 SMO endpoint, T111-direct).**

Strongest SMO-facing endpoint that **drops** the explicit per-newform
`Newform.PerNewformFullDirichletData` hypothesis (and therefore the
arbitrary `FullDirichletQuotientUniversalFClause` inside it), replacing
it with the strictly-classical T111 ingredients per `(f, χ, S, h_bad)`
quadruple.

Inputs:

* `h_unique` — Atkin-Lehner uniqueness (standard).
* `h_FE` — per-newform `Newform.HeckeFEData` (the H1 obligation).
* `h_T111_data` — per-newform/per-character/per-S existential providing
  the **classical T111 ingredients** (the finset `T` with its
  characterisation, the pole point `s₀`, character non-trivialities,
  abscissa bound, Dirichlet zero, and per-prime non-vanishing /
  analyticity / meromorphic-finiteness fields).  The universal-F clause
  is no longer required as an input; it is derived internally via
  `Newform.FullDirichletQuotientUniversalFClause_of_T111`.

The conclusion is `f.toCuspForm = g.toCuspForm` for any two newforms
agreeing on cofinite-coprime eigenvalues.

References: Diamond–Shurman §5.9, Miyake §4.5.15–4.5.16. -/
theorem strongMultiplicityOne_of_HeckeFEData_of_classicalInputs_T111_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_T111_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          (∀ p : Nat.Primes, p ∈ T ↔
            (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N) ∧
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) ≠ 1 ∧
          LSeries.abscissaOfAbsConv f.lCoeff_stripped <
            (((k : ℝ) / 2 + 1 : ℝ) : EReal) ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          (∀ p ∈ T,
            Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0) ∧
          (∀ p ∈ T,
            (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) ∧
          Differentiable ℂ
            (fun s : ℂ => ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) ∧
          (∀ p ∈ T, AnalyticAt ℂ
            (fun s => Newform.eulerFactor_stripped f χ S s p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀) ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine strongMultiplicityOne_of_HeckeFEData_of_PerNewformFullDirichletData_of_newformUnique
    h_unique h_FE ?_ f g χ hfχ hgχ S h
  intro N _ k f χ hfχ S h_bad
  -- The T111-ingredient hypothesis is a Prop existential; extract data via
  -- `Classical.choose` (the surrounding theorem is Prop-valued so this is fine),
  -- then destructure the resulting `And`-chain (`And.casesOn` allows
  -- large elimination since both sides live in `Prop`).
  let h_ex := h_T111_data f χ hfχ S h_bad
  let T : Finset Nat.Primes := h_ex.choose
  let s₀ : ℂ := h_ex.choose_spec.choose
  have h_specs := h_ex.choose_spec.choose_spec
  obtain ⟨hT_iff, h_χ_ne_one, h_chi_sq_ne_one, h_abscissa_lt, h_zero,
    h_num_LF_ne, h_factors_ne, h_den_factors_ne, h_EFP_diff, h_num_factor_an,
    h_den_finite⟩ := h_specs
  exact Newform.PerNewformFullDirichletData_of_classicalInputs_T111
    f χ hfχ S h_bad T hT_iff s₀ h_χ_ne_one h_chi_sq_ne_one h_abscissa_lt
    h_zero h_num_LF_ne h_factors_ne h_den_factors_ne h_EFP_diff
    h_num_factor_an h_den_finite

/-- **Direct bridge: `HeckeFEData` + `PerNewformFullDirichletData` ⇒
`Newform.AnalyticContradiction` (T132 H1+H2 intermediate consumer).**

Without going through `newform_unique`/SMO, callers wanting just the
analytic-contradiction conclusion can use this direct consumer
chaining `Newform.HeckeFEData` (Mellin) and per-newform
`Newform.PerNewformFullDirichletData` (Dirichlet zero data) into
`Newform.AnalyticContradiction`. -/
theorem Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction := by
  have h_no_ext : Newform.NoEntireExtensionUnderBadPrime :=
    Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
      (fun N _ k f χ hfχ S h_bad =>
        Newform.full_pole_witness_data_of_PerNewformFullDirichletData f χ S
          (h_data f χ hfχ S h_bad))
  exact Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    (Newform.HeckeEntireExtension_of_HeckeFEData h_FE) h_no_ext

/-- **Direct bridge: `HeckeFEData` + `PerNewformFullDirichletData` ⇒
`exists_nonzero_prime_eigenvalue` (T132 H1+H2 intermediate consumer).**

Composes the AnalyticContradiction bridge through
`Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction` for
callers needing the prime-nonvanishing conclusion. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_HeckeFEData_of_PerNewformFullDirichletData
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 :=
  Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    (Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData
      h_FE h_data) f χ hfχ S

/-- **`HeckeEntireExtension` from per-newform `MellinPairData` (T132 H1).**

Reduces `Newform.HeckeEntireExtension` (the global Hecke 1936 entire-
continuation predicate) to per-newform structured Mellin-pair data.
Each `Newform.MellinPairData f` packages explicit named fields
(Mellin-side functions `F, G : ℝ → ℂ`, root number `ε`, integrability,
weight positivity, FE involution, decay, Mellin–Dirichlet bridge) and
chains through `Newform.HeckeFEData.ofMellinData →
Newform.HeckeEntireExtension_of_HeckeFEData`.

This is the deepest H1 reduction currently available: the Hecke 1936
entire-continuation theorem now lives entirely in the explicit fields
of `MellinPairData`. -/
theorem Newform.HeckeEntireExtension_of_MellinPairData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.MellinPairData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_HeckeFEData
    (fun _N _ _k f => Newform.HeckeFEData.ofMellinData (h f))

/-- **Direct bridge: `MellinPairData` + `PerNewformFullDirichletData` ⇒
`Newform.AnalyticContradiction` (T132 H1+H2 intermediate consumer).**

Specialization of
`Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData`
that consumes the deeper-layer `Newform.MellinPairData` structure
instead of `Newform.HeckeFEData`.  The H1 obligation is now expressed
entirely through explicit Mellin-pair fields. -/
theorem Newform.analyticContradiction_of_MellinPairData_of_PerNewformFullDirichletData
    (h_mellin : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.MellinPairData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData
    (fun _N _ _k f => Newform.HeckeFEData.ofMellinData (h_mellin f)) h_data

/-- **Direct bridge: `MellinPairData` + `PerNewformFullDirichletData` ⇒
`exists_nonzero_prime_eigenvalue` (T132 H1+H2 intermediate consumer).**

Composes the AnalyticContradiction bridge through
`exists_nonzero_prime_eigenvalue_of_analyticContradiction`. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_MellinPairData_of_PerNewformFullDirichletData
    (h_mellin : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.MellinPairData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 :=
  Newform.exists_nonzero_prime_eigenvalue_of_HeckeFEData_of_PerNewformFullDirichletData
    (fun _N _ _k f => Newform.HeckeFEData.ofMellinData (h_mellin f)) h_data
    f χ hfχ S

/-- **SMO via per-newform `MellinPairData` + `PerNewformFullDirichletData`
+ `newform_unique` (T132 H1+H2 endpoint, deeper-layer variant).**

The deepest-layer SMO consumer.  Inputs:

* `h_unique` — Atkin-Lehner uniqueness (standard);
* `h_mellin` — per-newform `Newform.MellinPairData` (explicit Mellin-
  pair fields packaging Hecke 1936 entire continuation);
* `h_data` — per-newform `Newform.PerNewformFullDirichletData`
  (named-field Dirichlet-zero data).

The H1 obligation is now expressed entirely through structured
`MellinPairData` fields rather than the abstract `StrongFEPair`-
wrapped `HeckeFEData`. -/
theorem strongMultiplicityOne_of_MellinPairData_of_PerNewformFullDirichletData_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_mellin : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.MellinPairData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeFEData_of_PerNewformFullDirichletData_of_newformUnique
    h_unique
    (fun _N _ _k f => Newform.HeckeFEData.ofMellinData (h_mellin f))
    h_data f g χ hfχ hgχ S h

/-- **Direct bridge: `ImAxisMellinData` + `PerNewformFullDirichletData` ⇒
`Newform.AnalyticContradiction` (T132 H1+H2 intermediate consumer).**

Without going through `newform_unique`/SMO, callers wanting the
analytic-contradiction conclusion can use this consumer chaining
imAxis-side Mellin data and per-newform Dirichlet-zero data. -/
theorem Newform.analyticContradiction_of_ImAxisMellinData_of_PerNewformFullDirichletData
    (h_imAxis : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.ImAxisMellinData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData
    (fun _N _ _k f => Newform.HeckeFEData.ofImAxisData (h_imAxis f)) h_data

/-- **SMO endpoint: `ImAxisMellinData` + `PerNewformFullDirichletData` +
`newform_unique` ⇒ `f.toCuspForm = g.toCuspForm` (T132 H1+H2 endpoint).**

The strongest SMO-facing endpoint via the imAxis-side Mellin-data
interface.  Inputs:

* `h_unique` — Atkin-Lehner uniqueness (standard).
* `h_imAxis` — per-newform `Newform.ImAxisMellinData` (the H1 obligation
  expressed as named imAxis-side analytic fields).
* `h_data` — per-newform `Newform.PerNewformFullDirichletData`
  (the H2 Dirichlet-zero obligation).

The H1 obligation is now expressed entirely through the imAxis-side
Mellin-pair structure with `F` already canonicalised, replacing the
abstract `StrongFEPair`-wrapped `HeckeFEData` interface used in the
`_of_HeckeFEData_of_PerNewformFullDirichletData_of_newformUnique`
endpoint. -/
theorem strongMultiplicityOne_of_ImAxisMellinData_of_PerNewformFullDirichletData_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_imAxis : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.ImAxisMellinData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeFEData_of_PerNewformFullDirichletData_of_newformUnique
    h_unique
    (fun _N _ _k f => Newform.HeckeFEData.ofImAxisData (h_imAxis f))
    h_data f g χ hfχ hgχ S h

/-! ### Fricke slash-equality structured input + downstream H1 consumers (T132 H1) -/

/-- **Per-newform Fricke slash-equality data (T132 H1).**

The classical Atkin-Lehner Hecke 1936 input expressed as a single named
structure: a CuspForm `twist` whose imaginary axis represents the
Fricke slash image, plus the Mellin-Dirichlet bridge.

All other H1 fields (rapid decay of `Newform.imAxis f` and of `twist`,
local integrability, weight positivity ε ≠ 0, ...) are mechanical via
the existing imAxis pipeline (`Newform.hasImAxisExponentialDecay`,
`continuousOn_imAxis`, etc).

Consumers chain via `Newform.ImAxisMellinData.ofFrickeSlashData →
Newform.HeckeEntireExtension_of_ImAxisMellinData →
Newform.AnalyticContradiction → SMO`. -/
structure Newform.FrickeSlashData {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) where
  /-- CuspForm-valued Fricke slash image: `f|W_N` as a `Γ₁(N)`-cusp form. -/
  twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- The slash equality on `ℍ → ℂ`: `⇑twist = ⇑f ∣[k] frickeMatrix N`. -/
  slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
    ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N
  /-- Cusp-form weight is positive (cast to ℝ). -/
  hk_pos : 0 < (k : ℝ)
  /-- Mellin–Dirichlet bridge on the abscissa half-plane. -/
  h_bridge : ∀ {s : ℂ},
    LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s

/-- **Build `Newform.ImAxisMellinData` from `FrickeSlashData` (T132 H1).** -/
noncomputable def Newform.ImAxisMellinData.ofFrickeSlashData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (data : Newform.FrickeSlashData f) :
    Newform.ImAxisMellinData f :=
  Newform.ImAxisMellinData.ofSlashEq f data.twist data.slash_eq
    data.hk_pos data.h_bridge

/-- **Global `HeckeEntireExtension` from per-newform `FrickeSlashData`
(T132 H1 deepest reduction).**

Reduces `Newform.HeckeEntireExtension` to the **single** classical
analytic input: a CuspForm-valued Fricke slash image and Mellin-
Dirichlet bridge, per newform. -/
theorem Newform.HeckeEntireExtension_of_FrickeSlashData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_ImAxisMellinData
    (fun _N _ _k f => Newform.ImAxisMellinData.ofFrickeSlashData f (h f))

/-- **`Newform.AnalyticContradiction` from per-newform `FrickeSlashData` +
`PerNewformFullDirichletData` (T132 H1+H2 consumer).**

The H1 obligation is now a single named structure
`Newform.FrickeSlashData` per newform; the H2 obligation remains
`PerNewformFullDirichletData`. -/
theorem Newform.analyticContradiction_of_FrickeSlashData_of_PerNewformFullDirichletData
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_ImAxisMellinData_of_PerNewformFullDirichletData
    (fun _N _ _k f => Newform.ImAxisMellinData.ofFrickeSlashData f (h_slash f)) h_data

/-- **Existence of nonzero prime-eigenvalue from per-newform `FrickeSlashData`
+ `PerNewformFullDirichletData` (T132 H1+H2 consumer).**

Specialises `analyticContradiction_of_FrickeSlashData_of_PerNewformFullDirichletData`
through `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`
to the prime-nonvanishing conclusion needed by SMO. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_FrickeSlashData_of_PerNewformFullDirichletData
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 :=
  Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    (Newform.analyticContradiction_of_FrickeSlashData_of_PerNewformFullDirichletData
      h_slash h_data) f χ hfχ S

/-- **SMO endpoint: per-newform `FrickeSlashData` + `PerNewformFullDirichletData`
+ `newform_unique` (T132 H1+H2 endpoint, deepest H1 reduction).**

The strongest SMO-facing endpoint speaking entirely in terms of
**classical Atkin-Lehner Fricke slash-equality input** rather than
abstract `HeckeFEData` / `ImAxisMellinData` structures.  Inputs:

* `h_unique` — Atkin-Lehner uniqueness (standard).
* `h_slash` — per-newform `Newform.FrickeSlashData` (the classical Hecke
  1936 input expressed as the slash equality `⇑twist = ⇑f ∣[k] W_N`
  plus the Mellin-Dirichlet bridge).
* `h_data` — per-newform `Newform.PerNewformFullDirichletData`. -/
theorem strongMultiplicityOne_of_FrickeSlashData_of_PerNewformFullDirichletData_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_ImAxisMellinData_of_PerNewformFullDirichletData_of_newformUnique
    h_unique
    (fun _N _ _k f => Newform.ImAxisMellinData.ofFrickeSlashData f (h_slash f))
    h_data f g χ hfχ hgχ S h

/-- **Direct full-quotient bridge: `FrickeSlashData` + full data ⇒
`Newform.AnalyticContradiction` (T132 H1+H2 consumer, classical-Fricke H1).**

Replaces the global `HeckeEntireExtension` / structured `HeckeFEData`
H1 input of
`Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`
with the per-newform classical Atkin-Lehner Fricke slash-equality data
`Newform.FrickeSlashData`.  The `h_data` Dirichlet-zero side remains the
giant T111 full-data signature (preserved verbatim from the
`HeckeEntireExtension` variant). -/
theorem Newform.analyticContradiction_of_FrickeSlashData_of_full_dirichletZeroCertificate
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_FrickeSlashData h_slash) h_data

/-- **Direct full-quotient bridge: `FrickeSlashData` + full data ⇒
`exists_nonzero_prime_eigenvalue` (T132 H1+H2 consumer, classical-Fricke H1).**

Specialises `Newform.analyticContradiction_of_FrickeSlashData_of_full_dirichletZeroCertificate`
through `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`
to the prime-nonvanishing conclusion needed by SMO. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_FrickeSlashData_of_full_dirichletZeroCertificate
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 :=
  Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    (Newform.analyticContradiction_of_FrickeSlashData_of_full_dirichletZeroCertificate
      h_slash h_data) f χ hfχ S

/-- **SMO endpoint: `FrickeSlashData` + full Dirichlet-zero data +
`newform_unique` (T132 H1+H2 endpoint, classical-Fricke H1).**

The strongest SMO-facing endpoint pairing per-newform classical
Atkin-Lehner Fricke slash-equality data `Newform.FrickeSlashData` with
the full T111 Dirichlet-zero data block (verbatim from the
`HeckeEntireExtension` consumer at
`strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique`).

The H1 obligation is now expressed entirely through the slash-equality
identity `⇑twist = ⇑f ∣[k] W_N` (plus Mellin-Dirichlet bridge), rather
than a `StrongFEPair`-wrapped abstract `HeckeFEData` or the global
`HeckeEntireExtension` Prop. -/
theorem strongMultiplicityOne_of_FrickeSlashData_of_full_dirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique
    h_unique (Newform.HeckeEntireExtension_of_FrickeSlashData h_slash) h_data
    f g χ hfχ hgχ S h

/-- **SMO endpoint: `FrickeSlashData` + per-newform Dirichlet-zero data
+ `newform_unique` (T132 H1+H2 reduction, classical-Fricke H1, smaller H2).**

The smaller Dirichlet-zero variant of
`strongMultiplicityOne_of_FrickeSlashData_of_full_dirichletZeroCertificate_of_newformUnique`,
matching `strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZero_of_newformUnique`
(no `FullDirichletQuotientUniversalFClause` field on its own — the
universal-F clause is supplied as the last conjunct of `h_dirZero`). -/
theorem strongMultiplicityOne_of_FrickeSlashData_of_dirichletZero_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_dirZero : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          (∀ p ∈ T,
            Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0) ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZero_of_newformUnique
    h_unique (Newform.HeckeEntireExtension_of_FrickeSlashData h_slash) h_dirZero
    f g χ hfχ hgχ S h

/-- **SMO endpoint via `FrickeSlashData` + classical T111 inputs +
`newform_unique` (T132 H1+H2 endpoint, classical-Fricke H1, T111-direct).**

Strongest classical-Fricke H1 SMO-facing endpoint that **drops** the
explicit per-newform `Newform.PerNewformFullDirichletData` hypothesis
(and therefore the arbitrary `FullDirichletQuotientUniversalFClause`
inside it), replacing it with the strictly-classical T111 ingredients
per `(f, χ, S, h_bad)` quadruple.

Mirrors `strongMultiplicityOne_of_HeckeFEData_of_classicalInputs_T111_of_newformUnique`
with the `HeckeFEData` H1 input replaced by `FrickeSlashData` (the
classical Atkin-Lehner Fricke slash-equality data).

Inputs:

* `h_unique` — Atkin-Lehner uniqueness (standard).
* `h_slash` — per-newform `Newform.FrickeSlashData` (the H1 obligation).
* `h_T111_data` — per-newform/per-character/per-S existential providing
  the **classical T111 ingredients** (the finset `T` with its
  characterisation, the pole point `s₀`, character non-trivialities,
  abscissa bound, Dirichlet zero, and per-prime non-vanishing /
  analyticity / meromorphic-finiteness fields).  The universal-F clause
  is no longer required as an input; it is derived internally via
  `Newform.FullDirichletQuotientUniversalFClause_of_T111`. -/
theorem strongMultiplicityOne_of_FrickeSlashData_of_classicalInputs_T111_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_T111_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          (∀ p : Nat.Primes, p ∈ T ↔
            (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N) ∧
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) ≠ 1 ∧
          LSeries.abscissaOfAbsConv f.lCoeff_stripped <
            (((k : ℝ) / 2 + 1 : ℝ) : EReal) ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          (∀ p ∈ T,
            Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0) ∧
          (∀ p ∈ T,
            (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) ∧
          Differentiable ℂ
            (fun s : ℂ => ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) ∧
          (∀ p ∈ T, AnalyticAt ℂ
            (fun s => Newform.eulerFactor_stripped f χ S s p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀) ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine strongMultiplicityOne_of_FrickeSlashData_of_PerNewformFullDirichletData_of_newformUnique
    h_unique h_slash ?_ f g χ hfχ hgχ S h
  intro N _ k f χ hfχ S h_bad
  let h_ex := h_T111_data f χ hfχ S h_bad
  let T : Finset Nat.Primes := h_ex.choose
  let s₀ : ℂ := h_ex.choose_spec.choose
  have h_specs := h_ex.choose_spec.choose_spec
  obtain ⟨hT_iff, h_χ_ne_one, h_chi_sq_ne_one, h_abscissa_lt, h_zero,
    h_num_LF_ne, h_factors_ne, h_den_factors_ne, h_EFP_diff, h_num_factor_an,
    h_den_finite⟩ := h_specs
  exact Newform.PerNewformFullDirichletData_of_classicalInputs_T111
    f χ hfχ S h_bad T hT_iff s₀ h_χ_ne_one h_chi_sq_ne_one h_abscissa_lt
    h_zero h_num_LF_ne h_factors_ne h_den_factors_ne h_EFP_diff
    h_num_factor_an h_den_finite

/-! ### Corrected completed Mellin–Dirichlet bridge (T133)

The `h_bridge` field of `Newform.MellinPairData` / `Newform.ImAxisMellinData` /
`Newform.HeckeFEData.bridge` / `Newform.FrickeSlashData.h_bridge` (T132) asserts
the literal identity
```
mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s
```
which is **mathematically false** for canonical `imAxis f` with Mathlib's standard
`mellin` and `LSeries` (the audit in T129 confirmed this).  The honest classical
Hecke 1936 identity carries the Gamma factor:
```
mellin (Newform.imAxis f) s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s
```
on the convergence half-plane `Re s > k/2 + 1`, with the bad-prime stripping
`lCoeff` ↔ `lCoeff_stripped` handled separately via finite Euler-factor algebra.

This section provides:

* `Newform.HasCompletedMellinIdentity` — newform-side specialisation of
  `ModularForms.HasCompletedMellinIdentity`, the corrected classical Mellin–
  Dirichlet identity for the underlying cusp form.
* `Newform.CompletedMellinData` — replacement bundle for `MellinPairData`/
  `HeckeFEData`, with the `completed_bridge` field carrying the Gamma factor
  and the **full** (not stripped) coefficient sequence, plus a separate
  finite Euler-stripping field.
* `Newform.HeckeEntireExtension_of_CompletedMellinData` — consumer theorem
  chaining the corrected bundle into the existing `Newform.HeckeEntireExtension`
  predicate (and hence into the T132 SMO consumer chain) via Mathlib's
  `Complex.differentiable_one_div_Gamma`, `differentiable_const_cpow_of_neZero`,
  and the analytic identity principle on the convergence half-plane. -/

/-- **Newform-side completed Mellin–Dirichlet identity (T133).**

Specialises `ModularForms.HasCompletedMellinIdentity` to the underlying cusp form
of a `Newform`: states the corrected classical Hecke 1936 identity
```
mellin (Newform.imAxis f) s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s
```
on `Re s > k/2 + 1` (Diamond–Shurman §5.9 / Miyake Theorem 4.5.16). -/
def Newform.HasCompletedMellinIdentity {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Prop :=
  ModularForms.HasCompletedMellinIdentity f.toCuspForm

/-- **`Newform.HasCompletedMellinIdentity` is now sorry-free for any newform**
(T135).

The classical Hecke 1936 completed Mellin–Dirichlet identity holds for every
weight-`k` newform on `Γ₁(N)` with `0 < (k : ℝ)`:
```
mellin (Newform.imAxis f) s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s
```
on the half-plane `Re s > k/2 + 1`.

The previously-required coefficient-tail summability hypothesis has been
discharged downstream by
`ModularForms.hasCompletedMellinIdentity_Gamma1_mapGL`, itself a
consequence of `CuspFormClass.qExpansion_isBigO` plus the real `p`-series
summability test (see
`ModularForms.summable_lCoeff_mul_rpow_of_cuspForm_Gamma1_mapGL`).  Note
this only requires `0 < (k : ℝ)`; the cusp-form structure plus arithmeticity
are encoded in the `Newform N k` data.

This is the consumer-ready form intended for the
`Newform.CompletedFrickeData.completed_bridge` chain: a `CompletedFrickeData`
construction that picks `pair.f := imAxis f.toCuspForm` (so
`pair.Λ := mellin (imAxis f.toCuspForm)`) can fill the `completed_bridge`
field by directly applying this theorem.  The remaining analytic content
in `CompletedFrickeData` (the `StrongFEPair` functional-equation data and
the finite Euler-stripping triple) is **not** provided by this theorem —
that requires the full Hecke functional equation plus the bad-prime
Euler-factor algebra. -/
theorem Newform.hasCompletedMellinIdentity {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) (hk_pos : 0 < (k : ℝ)) :
    Newform.HasCompletedMellinIdentity f :=
  ModularForms.hasCompletedMellinIdentity_Gamma1_mapGL f.toCuspForm hk_pos

/-- **Corrected completed Mellin–LSeries data for newforms (T133).**

Replaces the mathematically false `MellinPairData.h_bridge` (which asserts the
literal `mellin = LSeries`) with the **honest** completed Mellin–Dirichlet
identity, expressed in terms of a Mathlib `StrongFEPair` (giving an entire
extension `pair.Λ` of `mellin pair.f`).  Bad-prime stripping (`lCoeff` ↔
`lCoeff_stripped`) is now a **separate** named hypothesis, captured by an
entire multiplier `stripping : ℂ → ℂ` and a half-plane bridge equation.

**Fields.**

* `pair : StrongFEPair ℂ` — Mathlib `StrongFEPair`; provides an entire `pair.Λ`.
* `completed_bridge` — the corrected classical Hecke identity:
  `pair.Λ s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on `Re s > k/2 + 1`.
  Together with the canonical choice `pair.f = Newform.imAxis f` (whose Mellin
  is `pair.Λ`), this is exactly the Diamond–Shurman §5.9 / Miyake §4.3.5
  classical identity.
* `stripping`, `stripping_diff`, `stripping_bridge` — finite Euler-stripping
  multiplier: an entire `stripping : ℂ → ℂ` with
  `LSeries f.lCoeff_stripped s = stripping s · LSeries f.lCoeff s` on the
  convergence half-plane.  Mathematically `stripping s = ∏_{p|N} L_p(f, s)⁻¹`,
  a finite product of polynomials in `p^{-s}`, hence entire.

**Status as a reduction.**  Replaces the false raw bridge of `MellinPairData`/
`HeckeFEData`/`FrickeSlashData` with the honest completed identity.  Consumers
chain through `Newform.HeckeEntireExtension_of_CompletedMellinData` to recover
the existing `Newform.HeckeEntireExtension` predicate (and hence the entire
T132 SMO consumer chain).

References: Diamond–Shurman §5.9 Theorem 5.9.2; Miyake Theorem 4.3.5 / 4.5.16. -/
structure Newform.CompletedMellinData {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) where
  /-- Mathlib `StrongFEPair`; provides an entire `pair.Λ = mellin pair.f`. -/
  pair : StrongFEPair ℂ
  /-- The cusp-form weight is positive (cast to ℝ).  Standard for cusp forms
  on `Γ₁(N)`; needed for `Complex.Gamma_ne_zero_of_re_pos` on `Re s > k/2 + 1`. -/
  hk_pos : 0 < (k : ℝ)
  /-- The **corrected** classical Hecke 1936 Mellin–Dirichlet identity
  (Diamond–Shurman §5.9 / Miyake Theorem 4.3.5):
  `pair.Λ s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on `Re s > k/2 + 1`. -/
  completed_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    pair.Λ s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries f.lCoeff s
  /-- Finite Euler-stripping multiplier (entire). -/
  stripping : ℂ → ℂ
  /-- The stripping multiplier is entire. -/
  stripping_diff : Differentiable ℂ stripping
  /-- Finite Euler-stripping bridge:
  `LSeries f.lCoeff_stripped s = stripping s · LSeries f.lCoeff s` on the
  half-plane `Re s > k/2 + 1` (where both LSeries converge for cusp forms,
  by Hecke's bound).  Mathematically `stripping = ∏_{p|N} L_p(f, s)⁻¹`. -/
  stripping_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    LSeries f.lCoeff_stripped s = stripping s * LSeries f.lCoeff s

/-- **`HeckeEntireExtension` from per-newform `CompletedMellinData` (T133).**

Consumer theorem: given per-newform `Newform.CompletedMellinData` (the
corrected completed Mellin–Dirichlet bridge plus finite Euler-stripping data),
produce the global `Newform.HeckeEntireExtension` predicate (used by the T132
analytic-contradiction / SMO consumer chain).

**Construction.**  For each newform `f`, the candidate entire extension is
```
Λ s := stripping s · (2π)^s · (Γ s)⁻¹ · pair.Λ s
```
which is differentiable on `ℂ` because:
* `stripping` is differentiable (`stripping_diff`);
* `(2π)^s` is differentiable (`Mathlib.differentiable_const_cpow_of_neZero`,
  using `2π ≠ 0`);
* `(Γ s)⁻¹` is differentiable (`Complex.differentiable_one_div_Gamma`);
* `pair.Λ` is differentiable (`StrongFEPair.differentiable_Λ`).

On the half-plane `Re s > k/2 + 1`, the `completed_bridge` and
`stripping_bridge` together give
```
Λ s = stripping s · LSeries f.lCoeff s = LSeries f.lCoeff_stripped s,
```
so `Λ` agrees with `LSeries f.lCoeff_stripped` on this open subset of the
convergence half-plane.  By the analytic identity principle
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) the agreement extends
to the full convergence half-plane `Re s > abscissaOfAbsConv f.lCoeff_stripped`.

References: Diamond–Shurman §5.9; Miyake Theorem 4.5.16. -/
theorem Newform.HeckeEntireExtension_of_CompletedMellinData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.CompletedMellinData f) :
    Newform.HeckeEntireExtension := by
  intro N _ k f
  obtain ⟨pair, hk_pos, h_completed, stripping, h_strip_diff, h_strip_bridge⟩ := h f
  -- (2π : ℂ) ≠ 0
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    have hπ_ℂ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hmul : (2 * Real.pi : ℂ) = (2 : ℂ) * (Real.pi : ℂ) := by ring
    rw [hmul]; exact mul_ne_zero h2 hπ_ℂ
  haveI : NeZero (2 * Real.pi : ℂ) := ⟨h2π⟩
  have h_2pi_diff : Differentiable ℂ (fun s : ℂ => (2 * Real.pi : ℂ) ^ s) :=
    differentiable_const_cpow_of_neZero (2 * Real.pi : ℂ)
  -- The candidate entire extension function
  let Λ : ℂ → ℂ := fun s =>
    stripping s * ((2 * Real.pi : ℂ) ^ s) * (Complex.Gamma s)⁻¹ * pair.Λ s
  have h_Λ_diff : Differentiable ℂ Λ :=
    ((h_strip_diff.mul h_2pi_diff).mul Complex.differentiable_one_div_Gamma).mul
      pair.differentiable_Λ
  -- Direct agreement on `Re s > k/2 + 1`.
  have h_direct :
      ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
        Λ s = LSeries f.lCoeff_stripped s := by
    intro s hs
    -- For `Re s > k/2 + 1 > 0`, `Γ s ≠ 0` (positive real part).
    have hs_re_pos : 0 < s.re := by
      have h_kbound_pos : (0 : ℝ) < (k : ℝ) / 2 + 1 := by linarith
      linarith
    have hΓ_ne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs_re_pos
    have h_2pi_cancel :
        ((2 * Real.pi : ℂ) ^ s) * ((2 * Real.pi : ℂ) ^ (-s)) = 1 := by
      rw [← Complex.cpow_add _ _ h2π, add_neg_cancel, Complex.cpow_zero]
    have hΓ_cancel : (Complex.Gamma s)⁻¹ * Complex.Gamma s = 1 :=
      inv_mul_cancel₀ hΓ_ne
    have h_pair := h_completed hs
    have h_strip := h_strip_bridge hs
    show stripping s * ((2 * Real.pi : ℂ) ^ s) * (Complex.Gamma s)⁻¹ * pair.Λ s
        = LSeries f.lCoeff_stripped s
    rw [h_pair, h_strip]
    have hRHS_rewrite :
        stripping s * ((2 * Real.pi : ℂ) ^ s) * (Complex.Gamma s)⁻¹ *
          ((2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries f.lCoeff s) =
        stripping s *
          (((2 * Real.pi : ℂ) ^ s) * ((2 * Real.pi : ℂ) ^ (-s))) *
          ((Complex.Gamma s)⁻¹ * Complex.Gamma s) * LSeries f.lCoeff s := by
      ring
    rw [hRHS_rewrite, h_2pi_cancel, hΓ_cancel]
    ring
  -- Promote agreement to `Re s > abscissaOfAbsConv f.lCoeff_stripped` via the
  -- analytic identity principle on a half-plane.
  refine ⟨Λ, h_Λ_diff, ?_⟩
  intro s₀ hs₀
  -- Pick a real σ strictly between abscissa(lCoeff_stripped) and s₀.re.
  obtain ⟨σ, hσ_abs, hσ_s⟩ :=
    EReal.exists_between_coe_real (show (LSeries.abscissaOfAbsConv f.lCoeff_stripped)
      < ((s₀.re : ℝ) : EReal) by exact_mod_cast hs₀)
  -- The open half-plane U := {s | σ < s.re} is convex (preconnected).
  let U : Set ℂ := {s | (σ : ℝ) < s.re}
  have hU_pre : IsPreconnected U := (convex_halfSpace_re_gt σ).isPreconnected
  have hs₀_in_U : s₀ ∈ U := by
    show (σ : ℝ) < s₀.re
    exact_mod_cast hσ_s
  -- Both Λ and LSeries f.lCoeff_stripped are analytic on U.
  have hΛ_an : AnalyticOnNhd ℂ Λ U := fun z _ =>
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr h_Λ_diff) z (Set.mem_univ _)
  have hL_an : AnalyticOnNhd ℂ (LSeries f.lCoeff_stripped) U := by
    intro z hz
    apply LSeries_analyticOnNhd f.lCoeff_stripped
    show LSeries.abscissaOfAbsConv f.lCoeff_stripped < (z.re : EReal)
    refine lt_trans hσ_abs ?_
    exact_mod_cast (hz : (σ : ℝ) < z.re)
  -- Witness z₀ ∈ U with Re z₀ > max(σ, k/2 + 1) so direct agreement applies.
  let zRe : ℝ := max σ ((k : ℝ) / 2 + 1) + 1
  let z₀ : ℂ := (zRe : ℝ)
  have hz₀_re : z₀.re = zRe := Complex.ofReal_re _
  have hzRe_gt_σ : σ < zRe := by
    have := le_max_left σ ((k : ℝ) / 2 + 1); linarith
  have hzRe_gt_kbound : ((k : ℝ) / 2 + 1) < zRe := by
    have := le_max_right σ ((k : ℝ) / 2 + 1); linarith
  have hz₀_in_U : z₀ ∈ U := by
    show (σ : ℝ) < z₀.re
    rw [hz₀_re]; exact hzRe_gt_σ
  have h_eq_nhds : Λ =ᶠ[nhds z₀] (LSeries f.lCoeff_stripped) := by
    let V : Set ℂ := {s | ((k : ℝ) / 2 + 1 : ℝ) < s.re}
    have hV_open : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
    have hz₀_in_V : z₀ ∈ V := by
      show ((k : ℝ) / 2 + 1 : ℝ) < z₀.re
      rw [hz₀_re]; exact hzRe_gt_kbound
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨V, hV_open.mem_nhds hz₀_in_V, ?_⟩
    intro w hw
    exact h_direct hw
  exact (hΛ_an.eqOn_of_preconnected_of_eventuallyEq hL_an hU_pre hz₀_in_U h_eq_nhds)
    hs₀_in_U

/-! ### End of corrected completed Mellin–Dirichlet bridge (T133) -/

/-! ### Corrected Fricke / completed Mellin data (T134)

Parallel to T132's `Newform.FrickeSlashData` (which routes through the
mathematically false raw bridge `mellin = LSeries f.lCoeff_stripped`), this
section provides a corrected Fricke-side bundle whose analytic content is
honest:

* `Newform.CompletedFrickeData` — combines the Atkin-Lehner / Fricke
  slash-equality data (`twist`, `slash_eq`) with the corrected completed
  Mellin–Dirichlet bridge (Gamma factor and full `lCoeff`) and a finite
  Euler-stripping triple, all needed to construct
  `Newform.CompletedMellinData`.
* `Newform.CompletedMellinData.ofCompletedFrickeData` — projection
  constructor.
* `Newform.HeckeEntireExtension_of_CompletedFrickeData` — chain through
  the T133 consumer.
* `Newform.analyticContradiction_of_CompletedFrickeData_of_PerNewformFullDirichletData`
  — H1+H2 endpoint mirroring the existing
  `analyticContradiction_of_FrickeSlashData_of_PerNewformFullDirichletData`
  but with honest H1 input.
* `Newform.exists_nonzero_prime_eigenvalue_of_CompletedFrickeData_of_PerNewformFullDirichletData`
  — prime-nonvanishing endpoint.
* `strongMultiplicityOne_of_CompletedFrickeData_of_PerNewformFullDirichletData_of_newformUnique`
  — top SMO endpoint, replacing
  `strongMultiplicityOne_of_FrickeSlashData_of_PerNewformFullDirichletData_of_newformUnique`
  with honest H1 input.

The older `FrickeSlashData` chain is left intact for continuity. -/

/-- **Corrected Fricke / completed Mellin data for newforms (T134).**

Replaces the mathematically false `Newform.FrickeSlashData.h_bridge` with
the honest classical Hecke 1936 Mellin–Dirichlet identity (Gamma factor,
full `lCoeff`) plus a separate finite Euler-stripping triple.  Carries the
Atkin-Lehner / Fricke slash-equality data (`twist`, `slash_eq`) for shape
correspondence with `FrickeSlashData`.

**Fields.**

* `twist`, `slash_eq` — the CuspForm-valued Fricke slash image
  `f|_k W_N : CuspForm (Γ₁(N).map ℝ) k` and the slash-equality identity
  on `ℍ → ℂ` (matches `FrickeSlashData`).
* `pair`, `hk_pos`, `completed_bridge`, `stripping`, `stripping_diff`,
  `stripping_bridge` — the analytic content needed to construct
  `Newform.CompletedMellinData` (the corrected completed Mellin bridge plus
  finite Euler stripping).

References: Diamond–Shurman §5.9; Miyake Theorem 4.5.16. -/
structure Newform.CompletedFrickeData {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) where
  /-- CuspForm-valued Fricke slash image: `f|W_N` as a `Γ₁(N)`-cusp form. -/
  twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- The slash equality on `ℍ → ℂ`: `⇑twist = ⇑f ∣[k] frickeMatrix N`. -/
  slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
    ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N
  /-- Mathlib `StrongFEPair` providing an entire `pair.Λ = mellin pair.f`. -/
  pair : StrongFEPair ℂ
  /-- The cusp-form weight is positive (cast to ℝ). -/
  hk_pos : 0 < (k : ℝ)
  /-- The **corrected** classical Hecke 1936 Mellin–Dirichlet identity
  (Diamond–Shurman §5.9 / Miyake Theorem 4.3.5):
  `pair.Λ s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on `Re s > k/2 + 1`. -/
  completed_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    pair.Λ s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries f.lCoeff s
  /-- Finite Euler-stripping multiplier (entire). -/
  stripping : ℂ → ℂ
  /-- The stripping multiplier is entire. -/
  stripping_diff : Differentiable ℂ stripping
  /-- Finite Euler-stripping bridge:
  `LSeries f.lCoeff_stripped s = stripping s · LSeries f.lCoeff s` on the
  half-plane `Re s > k/2 + 1`. -/
  stripping_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    LSeries f.lCoeff_stripped s = stripping s * LSeries f.lCoeff s

/-- **`Newform.CompletedFrickeData` from a CuspForm-supplied Atkin-Lehner
twist plus an Euler-stripping multiplier (T136 substantial reduction).**

Strongest constructor for the corrected `CompletedFrickeData` bundle.
Caller-supplied fields collapse to the **two genuinely-classical
analytic inputs** of the Hecke 1936 / Diamond–Shurman §5.9 / Miyake
§4.5.16 chain:

1. **Atkin-Lehner / Fricke twist as a CuspForm** (`twist`, `slash_eq`).
   The data `twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k` together with
   the slash-equality identity
   `⇑twist = ⇑f.toCuspForm.toModularForm' ∣[k] frickeMatrix N`
   captures the classical Atkin-Lehner Fricke involution `f ↦ f|W_N`.
   Mathlib does not (yet) provide this involution as a CuspForm-valued
   operator; once it does, the entire `(twist, slash_eq)` pair becomes
   automatic.

2. **Euler-stripping multiplier** (`stripping`, `stripping_diff`,
   `stripping_bridge`).  The stripping multiplier
   `stripping s = ∏_{p|N} L_p(f, s)⁻¹` is a **finite product of
   polynomials** in `p^{-s}`, hence entire; the bridge equation
   `LSeries f.lCoeff_stripped s = stripping s · LSeries f.lCoeff s`
   is **algebraic** (Euler-product factorisation of the local
   coefficient sequences), without any analytic input.  Once Mathlib
   has the cusp-form Euler product, the entire stripping triple
   becomes automatic.

The remaining `pair`, `completed_bridge` fields are **mechanically
discharged**:

* `pair : StrongFEPair ℂ` is built from `imAxis f.toCuspForm` and the
  scaled twist `t ↦ imAxis twist (t / N)`, with `ε := N^{1-k} · I^k`,
  using the existing `imAxis` infrastructure
  (`Newform.locallyIntegrableOn_imAxis`, `Newform.imAxis_rapidDecay`,
  `Newform.cuspForm_Gamma1_hasImAxisExponentialDecay` for the twist
  side, and `Newform.imAxis_feq_of_slashEq` for the functional
  equation).
* `completed_bridge` is discharged by T135's
  `Newform.hasCompletedMellinIdentity`, which gives the corrected
  classical Hecke 1936 Mellin–Dirichlet identity
  `pair.Λ s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on the
  half-plane `Re s > k/2 + 1` directly from `CuspFormClass.qExpansion_isBigO`.

This isolates the **exact remaining classical analytic inputs** for
the `CompletedFrickeData`-route to `exists_nonzero_prime_eigenvalue`:

* the existence of a CuspForm-valued Atkin-Lehner Fricke twist
  satisfying the slash equality on `Γ₁(N)`;
* the algebraic Euler-stripping factorisation
  `lCoeff_stripped = stripping · lCoeff` at the LSeries level.

References: Diamond–Shurman §5.9 Theorem 5.9.2; Miyake Theorem 4.3.5 / 4.5.16. -/
noncomputable def Newform.CompletedFrickeData.ofSlashEqWithStripping
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N)
    (hk_pos : 0 < (k : ℝ))
    (stripping : ℂ → ℂ)
    (stripping_diff : Differentiable ℂ stripping)
    (stripping_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      LSeries f.lCoeff_stripped s = stripping s * LSeries f.lCoeff s) :
    Newform.CompletedFrickeData f := by
  -- Numerical setup.
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN_ne : (N : ℂ) ≠ 0 := by
    have : (N : ℝ) ≠ 0 := hN_pos.ne'
    exact_mod_cast this
  have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  -- The scaled twist function `G(t) := imAxis twist (t / N)`.
  let G : ℝ → ℂ := fun t => _root_.ModularForms.imAxis twist (t / (N : ℝ))
  -- Root number `ε := (N : ℂ)^{1-k} * I^k`.
  let ε : ℂ := (N : ℂ) ^ (1 - k) * Complex.I ^ k
  have hε_ne : ε ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ hN_ne) (zpow_ne_zero _ hI_ne)
  -- Local integrability of `G` on `Ioi 0`.
  have hG_continuousOn : ContinuousOn G (Set.Ioi (0 : ℝ)) := by
    have h_div_cts : ContinuousOn
        (fun t : ℝ => t / (N : ℝ)) (Set.Ioi (0 : ℝ)) :=
      Continuous.continuousOn (by fun_prop)
    have h_maps : Set.MapsTo (fun t : ℝ => t / (N : ℝ))
        (Set.Ioi 0) (Set.Ioi 0) := fun t ht => div_pos ht hN_pos
    exact (_root_.ModularForms.continuousOn_imAxis twist).comp h_div_cts h_maps
  have hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi (0 : ℝ)) :=
    hG_continuousOn.locallyIntegrableOn measurableSet_Ioi
  -- Rapid decay of `G` via composition with `t / N`.
  have hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r) := by
    intro r
    have h_twist_decay :=
      (_root_.ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay
        twist (Newform.cuspForm_Gamma1_hasImAxisExponentialDecay twist)) r
    have h_tendsto : Filter.Tendsto (fun t : ℝ => t / (N : ℝ))
        Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_div_const hN_pos
    refine (h_twist_decay.comp_tendsto h_tendsto).trans ?_
    refine Asymptotics.IsBigO.of_bound (((N : ℝ) ^ (-r))) ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    simp only [Function.comp_apply]
    have h_div_rpow : (t / (N : ℝ)) ^ r = (N : ℝ) ^ (-r) * t ^ r := by
      rw [Real.div_rpow ht.le hN_pos.le, Real.rpow_neg hN_pos.le, div_eq_mul_inv]
      ring
    rw [h_div_rpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hN_pos (-r))]
  -- Functional equation, derived from `imAxis_feq_of_slashEq`.
  have h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      Newform.imAxis f (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x := by
    intro x hx
    have h := Newform.imAxis_feq_of_slashEq f twist slash_eq hx
    have h_cast : ((x ^ (k : ℝ) : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ k := by
      rw [Real.rpow_intCast x k, Complex.ofReal_zpow]
    show Newform.imAxis f (1 / x) =
      (((N : ℂ) ^ (1 - k) * Complex.I ^ k) * ((x ^ (k : ℝ) : ℝ) : ℂ)) •
        _root_.ModularForms.imAxis twist (x / (N : ℝ))
    rw [h, h_cast, smul_eq_mul]
  -- Build the StrongFEPair.
  let pair : StrongFEPair ℂ :=
    { f := Newform.imAxis f
      g := G
      k := (k : ℝ)
      ε := ε
      f₀ := 0
      g₀ := 0
      hf_int := Newform.locallyIntegrableOn_imAxis f
      hg_int := hG_int
      hk := hk_pos
      hε := hε_ne
      h_feq := h_feq
      hf_top := Newform.imAxis_rapidDecay f
      hg_top := hG_top
      hf₀ := rfl
      hg₀ := rfl }
  -- Now build the CompletedFrickeData.  The completed_bridge is discharged
  -- by T135's Newform.hasCompletedMellinIdentity, after rewriting
  -- `LSeries (ModularForms.lCoeff f.toCuspForm) = LSeries f.lCoeff` via
  -- `Newform.lCoeff_eq_modularForms_lCoeff_funext`.
  refine
    { twist := twist
      slash_eq := slash_eq
      pair := pair
      hk_pos := hk_pos
      completed_bridge := ?_
      stripping := stripping
      stripping_diff := stripping_diff
      stripping_bridge := stripping_bridge }
  intro s hs
  have h_T135 := Newform.hasCompletedMellinIdentity f hk_pos hs
  rw [← Newform.lCoeff_eq_modularForms_lCoeff_funext f] at h_T135
  exact h_T135

/-- **Atkin-Lehner Fricke twist as a Γ₁(N)-CuspForm — named residual H1a (T136).**

Existence of a CuspForm-valued Atkin-Lehner Fricke involution image
`twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k` whose underlying
`ℍ → ℂ` map equals the slash `⇑f.toCuspForm.toModularForm' ∣[k] W_N`.

Mathematical content: classical Atkin-Lehner involution `f ↦ f|W_N`
(Diamond–Shurman §5.5 / Miyake §4.6) — the Fricke matrix `W_N` normalises
`Γ₁(N)`, so `f|W_N` transforms under `Γ₁(N)` by the same automorphy
factor and inherits the cusp condition.  Mathlib does not yet provide
a CuspForm-valued slash action for arbitrary `GL (Fin 2) ℝ` matrices;
the cleanest target is to define such an action specifically for
`frickeMatrix N` on `(Gamma1 N).map (mapGL ℝ)`, with an instance lemma
identifying its `⇑` with the raw slash.

Once `HasFrickeTwistAsCuspForm` is proven for every newform, the
Fricke side of `Newform.CompletedFrickeData` is fully closed via
`Newform.CompletedFrickeData.ofSlashEqWithStripping`. -/
def Newform.HasFrickeTwistAsCuspForm
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) : Prop :=
  ∃ twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N

/-- **Cusp-form L-series Euler-stripping factorisation — named residual H1b (T136).**

Existence of an entire multiplier `stripping : ℂ → ℂ` such that the
stripped Newform L-series factors as `stripping(s) · LSeries f.lCoeff s`
on the absolute-convergence half-plane `Re s > k/2 + 1`.

Mathematical content (Diamond–Shurman §5.9 / Miyake §4.5.16): the
multiplier is the **finite product over primes dividing `N`** of the
local Euler factors at those primes,
```
stripping s = ∏_{p | N} (1 - (f.lCoeff p) · p^{-s})
```
which is a finite product of Dirichlet polynomials in `p^{-s}`, hence
entire on `ℂ`.  The factorisation
`LSeries f.lCoeff_stripped s = stripping s · LSeries f.lCoeff s` on
the absolute-convergence half-plane is the standard Euler-product
identity for a Hecke eigenform.

The local API has the structural Euler product
`Newform.lSeries_stripped_hasProd` (T097) and the per-prime
identification `Newform.lSeries_stripped_hasProd_eulerFactor` (T099),
both indexed by `(χ, S)`; the cleanest target for `HasEulerStrippingMultiplier`
is to extract a `χ`/`S`-independent multiplier from those, plus
explicit entirety of the finite product.

Once `HasEulerStrippingMultiplier` is proven for every newform, the
Euler-stripping side of `Newform.CompletedFrickeData` is fully closed
via `Newform.CompletedFrickeData.ofSlashEqWithStripping`. -/
def Newform.HasEulerStrippingMultiplier
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) : Prop :=
  ∃ stripping : ℂ → ℂ,
    Differentiable ℂ stripping ∧
    ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      LSeries f.lCoeff_stripped s = stripping s * LSeries f.lCoeff s

/-- **Coprime-strip / Newform-strip translation (T137 helper).**

The generic `LSeries.coprimeStrip S` operator (LFunction.lean §`coprimeStrip`),
applied to a Newform's full Fourier coefficient sequence with `S` parameterising
the prime divisors of the level `N`, recovers the level-aware
`Newform.lCoeff_stripped` sequence.

Concretely, when `S : Finset Nat.Primes` satisfies the bad-prime characterisation
`hS : ∀ p, p ∈ S ↔ (p : ℕ) ∣ N`, then
`LSeries.coprimeStrip S f.lCoeff = f.lCoeff_stripped` as functions `ℕ → ℂ`.

This is the bridge that lets the LFunction.lean Euler-stripping assembly
theorem `LSeries.hasEulerStrippingMultiplier_of_eulerProduct` (which produces
its output in terms of `coprimeStrip`) be applied to the Newform's
level-aware stripped Dirichlet series. -/
lemma Newform.coprimeStrip_lCoeff_eq_lCoeff_stripped
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℕ) ∣ N) :
    LSeries.coprimeStrip S f.lCoeff = f.lCoeff_stripped := by
  funext n
  unfold LSeries.coprimeStrip Newform.lCoeff_stripped
  by_cases h : n.Coprime N
  · rw [if_pos h, if_pos]
    intro p hp h_p_n
    have hp_N : (p : ℕ) ∣ N := (hS p).mp hp
    have hp_dvd_gcd : (p : ℕ) ∣ Nat.gcd n N := Nat.dvd_gcd h_p_n hp_N
    rw [show Nat.gcd n N = 1 from h] at hp_dvd_gcd
    exact p.prop.one_lt.ne' (Nat.dvd_one.mp hp_dvd_gcd)
  · rw [if_neg h]
    rw [if_neg]
    push_neg
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · -- `n = 0`: `¬ Nat.Coprime 0 N` forces `N ≠ 1` (since `gcd 0 N = N`).
      have hN_ne_one : N ≠ 1 := by
        intro hN1; apply h; rw [hN1]; exact Nat.coprime_one_right 0
      obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN_ne_one
      exact ⟨⟨p, hp⟩, (hS ⟨p, hp⟩).mpr hpN, dvd_zero _⟩
    · -- `n > 0`: `gcd n N > 1`, so some prime divides both.
      have hgcd_pos : 0 < Nat.gcd n N := Nat.gcd_pos_of_pos_left N hn_pos
      have hgcd_ne_one : Nat.gcd n N ≠ 1 := h
      obtain ⟨p, hp, hp_dvd_gcd⟩ := Nat.exists_prime_and_dvd hgcd_ne_one
      refine ⟨⟨p, hp⟩, (hS ⟨p, hp⟩).mpr (dvd_trans hp_dvd_gcd
        (Nat.gcd_dvd_right _ _)), dvd_trans hp_dvd_gcd (Nat.gcd_dvd_left _ _)⟩

/-- **`Newform.HasEulerStrippingMultiplier` from the full Newform Euler product
plus bad-prime local Euler-factor identification (T137 strict reduction).**

Strict reduction of H1b (the `Newform.HasEulerStrippingMultiplier f` predicate)
to the **single named missing arithmetic input**: the full Hecke-eigenform
Euler product
```
HasProd (fun p ↦ ∑' e, LSeries.term f.lCoeff s (p^e)) (LSeries f.lCoeff s)
```
on the absolute-convergence half-plane `Re s > k/2 + 1`, together with the
classical bad-prime local Euler factor identification at primes `p ∣ N`:
```
∑' e, LSeries.term f.lCoeff s (p^e) = (1 - a_p · p^{-s})⁻¹
```
(Diamond–Shurman §5.9 / Miyake §4.5.16).

**Proof shape.**  Apply `LSeries.hasEulerStrippingMultiplier_of_eulerProduct`
(LFunction.lean) with `f := f.lCoeff`, `a := fun p ↦ f.lCoeff (p : ℕ)`,
`H s := (k : ℝ) / 2 + 1 < s.re`, and `S` the bad-prime Finset; the stripped
Euler product (`hg_euler`) is supplied by `Newform.lSeries_stripped_hasProd`
after translation through `Newform.coprimeStrip_lCoeff_eq_lCoeff_stripped`.

**Output multiplier** (from the LFunction.lean assembly):
`stripping s = ∏ p ∈ S, (1 - f.lCoeff p · p^{-s})`,
the explicit finite Dirichlet polynomial of Diamond–Shurman §5.9, entire by
`differentiable_eulerFactor_polynomial_finset`.

**Remaining missing input.** This theorem reduces H1b to:
1. `hf_full_euler`: the full `f.lCoeff` Euler product over ALL primes
   (not just primes coprime to `N`).  Currently the file proves only the
   stripped version (`Newform.lSeries_stripped_hasProd`); the full version
   requires extending coprime multiplicativity beyond the both-coprime-to-`N`
   restriction in `Newform.lCoeff_mul_of_coprime`.  This is automatic for
   normalised Hecke eigenforms by Diamond–Shurman §5.8 / Miyake §4.5.16
   (the eigenvalue character extends multiplicatively to all coprime
   arguments without level-coprimality), but is not yet packaged in
   the existing API.
2. `h_bad_local_inv`: the bad-prime local Euler factor at `p ∣ N`.  Follows
   from the bad-prime Hecke recurrence `f(p^{r+1}) = a_p · f(p^r)` (Diamond–
   Shurman §5.8 Prop 5.8.5; recurrence at `p ∣ N` collapses since `χ(p) = 0`)
   plus the standard geometric series identity.
3. `h_bad_local_ne_zero`: typically follows from absolute convergence on
   the half-plane and the standard `‖a_p p^{-s}‖ < 1` Hecke bound.

The character/eigenform context `(χ, hfχ)` is needed only to invoke
`Newform.lSeries_stripped_hasProd` for `hg_euler`; the rest of the chain
is purely about the L-series at coefficient level. -/
theorem Newform.hasEulerStrippingMultiplier_of_fullEulerProduct
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℕ) ∣ N)
    (hf_full_euler : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      HasProd
        (fun p : Nat.Primes =>
          ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e))
        (LSeries f.lCoeff s))
    (h_bad_local_inv : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      ∀ p ∈ S,
        ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e) =
          (1 - f.lCoeff (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
    (h_bad_local_ne_zero : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      ∀ p ∈ S,
        1 - f.lCoeff (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s) ≠ 0) :
    Newform.HasEulerStrippingMultiplier f := by
  have h_strip_eq : LSeries.coprimeStrip S f.lCoeff = f.lCoeff_stripped :=
    f.coprimeStrip_lCoeff_eq_lCoeff_stripped S hS
  -- Pull the stripped Euler product back to the `coprimeStrip` form expected
  -- by the LFunction.lean assembly theorem.
  have hg_euler : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      HasProd
        (fun p : Nat.Primes =>
          ∑' e : ℕ,
            LSeries.term (LSeries.coprimeStrip S f.lCoeff) s ((p : ℕ) ^ e))
        (LSeries (LSeries.coprimeStrip S f.lCoeff) s) := by
    intro s hs
    have h := f.lSeries_stripped_hasProd χ hfχ hs
    rw [← h_strip_eq] at h
    exact h
  obtain ⟨stripping, h_diff, h_bridge⟩ :=
    LSeries.hasEulerStrippingMultiplier_of_eulerProduct
      S (fun p : Nat.Primes => f.lCoeff (p : ℕ)) f.lCoeff
      (fun s : ℂ => ((k : ℝ) / 2 + 1 : ℝ) < s.re)
      f.lCoeff_one hf_full_euler hg_euler h_bad_local_inv h_bad_local_ne_zero
  refine ⟨stripping, h_diff, ?_⟩
  intro s hs
  have h := h_bridge hs
  rw [h_strip_eq] at h
  exact h

/-- **Bundled arithmetic input for `Newform.HasEulerStrippingMultiplier`
(T137 named residual input).**

The single named arithmetic input that
`Newform.hasEulerStrippingMultiplier_of_arithmeticInput` consumes to produce
H1b (`Newform.HasEulerStrippingMultiplier f`).  Bundles together:

* the character/eigenform context `(χ, hfχ)`;
* the bad-prime Finset `S` plus its characterisation
  `hS : ∀ p, p ∈ S ↔ (p : ℕ) ∣ N`;
* the **full Newform Euler product** at every `s` on the
  absolute-convergence half-plane (`hf_full_euler`);
* the **bad-prime local Euler factor identification**
  `∑' e, LSeries.term f.lCoeff s (p^e) = (1 - a_p · p^{-s})⁻¹` at primes
  `p ∈ S` (`h_bad_local_inv`), per Diamond–Shurman §5.9 / Miyake §4.5.16;
* the **bad-prime local Euler factor non-vanishing**
  `1 - a_p · p^{-s} ≠ 0` at primes `p ∈ S` (`h_bad_local_ne_zero`).

This is the **single named residual input** that closes H1b: once an instance
is supplied, `Newform.hasEulerStrippingMultiplier_of_arithmeticInput` produces
`Newform.HasEulerStrippingMultiplier f` mechanically.

The follow-up arithmetic ticket should construct an instance of this
structure for every newform `f : Newform N k` (with character `χ`) by:

1. Extending `Newform.lCoeff_mul_of_coprime` past the both-coprime-to-`N`
   restriction, providing full multiplicativity on all coprime arguments
   (Diamond–Shurman §5.8 Prop 5.8.5; automatic for normalised Hecke
   eigenforms via the bad-prime recurrence `f(p^{r+1}) = a_p · f(p^r)`
   when `χ(p) = 0`).
2. Discharging `hf_full_euler` by `EulerProduct.eulerProduct_hasProd` with
   the strengthened multiplicativity.
3. Discharging `h_bad_local_inv` by the bad-prime recurrence + standard
   geometric series.
4. Discharging `h_bad_local_ne_zero` by absolute convergence on the
   half-plane and the Hecke `‖a_p p^{-s}‖ < 1` bound. -/
structure Newform.EulerStrippingArithmeticInput
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ) where
  /-- Character/eigenform compatibility. -/
  hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ
  /-- The bad-prime Finset (primes dividing the level `N`). -/
  S : Finset Nat.Primes
  /-- Characterisation of the bad-prime Finset. -/
  hS : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℕ) ∣ N
  /-- Full Newform Euler product over `Nat.Primes` on the
  absolute-convergence half-plane. -/
  hf_full_euler : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    HasProd
      (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e))
      (LSeries f.lCoeff s)
  /-- Bad-prime local Euler factor identification:
  `∑' e, term f.lCoeff s (p^e) = (1 - a_p · p^{-s})⁻¹` at every `p ∈ S`. -/
  h_bad_local_inv : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    ∀ p ∈ S,
      ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e) =
        (1 - f.lCoeff (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s))⁻¹
  /-- Bad-prime local Euler factor non-vanishing:
  `1 - a_p · p^{-s} ≠ 0` at every `p ∈ S`. -/
  h_bad_local_ne_zero : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    ∀ p ∈ S,
      1 - f.lCoeff (p : ℕ) * ((p : ℕ) : ℂ) ^ (-s) ≠ 0

/-- **`Newform.HasEulerStrippingMultiplier` from the bundled arithmetic input
(T137 named-input wrapper).**

Strict reduction of H1b to a **single named residual input**
`Newform.EulerStrippingArithmeticInput f χ`: once that instance is supplied,
the Euler-stripping multiplier predicate `Newform.HasEulerStrippingMultiplier f`
follows mechanically by chaining through
`Newform.hasEulerStrippingMultiplier_of_fullEulerProduct` (the low-level
consumer that takes the four arithmetic hypotheses individually).

Downstream consumers of `Newform.HasEulerStrippingMultiplier` (notably
`Newform.completedFrickeData_of_classicalInputs` for H1b) only need to remember
this **single named bundle** rather than the four constituent hypotheses,
keeping the Newform-side analytic API ergonomic for the strong-multiplicity-one
chain. -/
theorem Newform.hasEulerStrippingMultiplier_of_arithmeticInput
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (input : Newform.EulerStrippingArithmeticInput f χ) :
    Newform.HasEulerStrippingMultiplier f :=
  f.hasEulerStrippingMultiplier_of_fullEulerProduct χ input.hfχ
    input.S input.hS input.hf_full_euler
    input.h_bad_local_inv input.h_bad_local_ne_zero

/-- **Hecke multiplicative structure of a Newform's Fourier coefficients
(T138 single named arithmetic input).**

Bundles the two classical arithmetic facts about a Newform's Fourier
coefficient sequence that suffice to construct
`Newform.EulerStrippingArithmeticInput f χ` mechanically:

* `full_coprime_mul` — full coprime multiplicativity
  `f.lCoeff (m * n) = f.lCoeff m · f.lCoeff n` for **any** coprime pair
  `m, n` (no level-coprime restriction; this strengthens the existing
  `Newform.lCoeff_mul_of_coprime` past the both-coprime-to-`N` constraint).
* `bad_prime_pow` — bad-prime closed form `f.lCoeff (p^r) = a_p^r` at every
  prime `p ∣ N` (equivalent to the bad-prime Hecke recurrence
  `f.lCoeff (p^{r+1}) = a_p · f.lCoeff (p^r)` plus normalisation).

Mathematical content (Diamond–Shurman §5.8 Prop 5.8.5 / Miyake §4.5.16):
both facts are automatic for normalised Hecke eigenforms.  Full
coprime multiplicativity follows from the fact that the eigenvalue
character extends multiplicatively to all coprime arguments via the prime
factorisation; the bad-prime closed form follows from the bad-prime
recurrence at primes dividing the level (where `χ(p) = 0` because `p` is
non-unit modulo `N`, killing the `χ(p) · p^{k-1}` term in the Hecke
recurrence).

This is the **single named bundled hypothesis** that T138's constructor
`Newform.eulerStrippingArithmeticInput_of_heckeStruct` consumes to produce
`Newform.EulerStrippingArithmeticInput f χ`.  Together with T137's wrapper
`Newform.hasEulerStrippingMultiplier_of_arithmeticInput`, this reduces the
H1b chain
```
HasHeckeMultiplicativeStructure f χ
  ⟹ EulerStrippingArithmeticInput f χ
  ⟹ HasEulerStrippingMultiplier f
```
to a single named arithmetic predicate. -/
structure Newform.HasHeckeMultiplicativeStructure
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ) : Prop where
  /-- Character/eigenform compatibility. -/
  hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ
  /-- Full coprime multiplicativity (no level-coprime restriction):
  `f.lCoeff (m * n) = f.lCoeff m · f.lCoeff n` for **any** coprime pair. -/
  full_coprime_mul : ∀ {m n : ℕ}, Nat.Coprime m n →
    f.lCoeff (m * n) = f.lCoeff m * f.lCoeff n
  /-- Bad-prime closed form: `f.lCoeff (p^r) = a_p^r` for every prime
  `p ∣ N` and every exponent `r`. -/
  bad_prime_pow : ∀ {p : ℕ}, p.Prime → p ∣ N → ∀ r : ℕ,
    f.lCoeff (p ^ r) = f.lCoeff p ^ r

/-- **Period-1 Newform bridge for the bad-prime Hecke operator (T139 helper).**

For a `Newform N k` and a prime `p ∣ N` (`hpN : ¬ Nat.Coprime p N`), the
period-1 Fourier coefficient of `heckeT_p_divN k p hp hpN
f.toCuspForm.toModularForm'` at index `m` equals the Newform's `f.lCoeff (p * m)`.

Direct Newform-side reading of the existing `qExpansion_one_heckeT_p_divN_coeff`
in `LeanModularForms/Modularforms/QExpansionSlash.lean`; the only reindexing
is the `Newform.lCoeff` ⟶ `qExpansion (1 : ℝ) f.toCuspForm` definitional
unfolding from `Newform.lCoeff_apply`.  Used in the bad-prime closed-form
construction `Newform.lCoeff_pow_at_bad_prime`. -/
lemma Newform.lCoeff_heckeT_p_divN_apply
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) ((heckeT_p_divN k p hp hpN)
        f.toCuspForm.toModularForm')).coeff m =
      f.lCoeff (p * m) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  rw [qExpansion_one_heckeT_p_divN_coeff hp hpN f.toCuspForm.toModularForm' m]
  rfl

/-- **Iterated period-1 Newform bridge for the bad-prime Hecke operator
(T139 helper).**

For a `Newform N k`, a prime `p ∣ N`, and an exponent `r`, applying
`heckeT_p_divN k p hp hpN` (as a function via `Function.iterate`) to
`f.toCuspForm.toModularForm'` exactly `r` times gives a ModularForm whose
`m`-th period-1 Fourier coefficient equals `f.lCoeff (p^r * m)`.

The proof inducts on `r` using `qExpansion_one_heckeT_p_divN_coeff` per step;
the recurrence `p ^ (r + 1) * m = p ^ r * (p * m)` lets the induction step
identify `qExpansion 1 (T_p_divN^{r+1} g) (m)` with
`f.lCoeff (p^(r+1) * m)` after a single bridge application. -/
lemma Newform.lCoeff_heckeT_p_divN_iterate_apply
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) (r m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        (((fun g => heckeT_p_divN k p hp hpN g) : ModularForm _ k → ModularForm _ k)^[r]
          f.toCuspForm.toModularForm')).coeff m =
      f.lCoeff (p ^ r * m) := by
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  induction r generalizing m with
  | zero =>
    simp only [pow_zero, Function.iterate_zero_apply, one_mul]
    rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',
      qExpansion_one_heckeT_p_divN_coeff hp hpN _ m, ih (p * m)]
    congr 1
    ring

/-- **Bad-prime Hecke operator preserves the new subspace, modulo the bad-prime
Petersson adjoint with old-subspace stability (T140 strict reduction).**

For a prime `p ∣ N` (so `¬ Nat.Coprime p N`) and a cusp form `f ∈ S_k^new`,
the Hecke operator `heckeT_n_cusp k p f` (which at `p ∣ N` reduces to the
bad-prime / `U_p`-style operator via `heckeT_p_all_divN`) lies in `S_k^new`,
**given** an explicit Petersson-adjoint operator `T_adj` for `T_p` at level
`Γ_1(N)` that preserves the old-subspace `cuspFormsOld N k`.

This mirrors the coprime proof template (`heckeT_n_preserves_cuspFormsNew`):

```
intro g hg
rw [h_adj f g]
exact hf _ (h_old g hg)
```

with the coprime adjoint-formula+`diamondOp`-preserves-old chain
(`heckeT_n_adjoint` + `diamondOp_preserves_cuspFormsOld` + the coprime
`heckeT_n_preserves_cuspFormsOld`) replaced by the explicit bad-prime
`(T_adj, h_adj, h_old)` triple.

**The single named missing classical input** for unconditional bad-prime
newspace preservation is the **bad-prime Petersson adjoint of `T_p` at level
`Γ_1(N)` preserving the old-subspace**: explicitly, an operator
`T_adj : CuspForm _ k →ₗ[ℂ] CuspForm _ k` satisfying
* `petN (T_p f) g = petN f (T_adj g)` for all `f, g : CuspForm _ k`
  (Petersson-adjoint formula at `p ∣ N`);
* `T_adj (cuspFormsOld N k) ⊆ cuspFormsOld N k` (oldspace preservation).

The natural choice in Diamond–Shurman / Miyake theory is
`T_adj = W_N · T_p · W_N⁻¹` where `W_N` is the **Atkin–Lehner / Fricke
involution** at level `N`; the involution `W_N` is itself the named missing
infrastructure (entirely analogous to `Newform.HasFrickeTwistAsCuspForm` from
T136 — the H1a track). Once `W_N` and its key properties (`W_N · T_p · W_N⁻¹`
preserves the old-subspace; the Petersson adjoint formula
`pet (T_p f) g = pet f (W_N T_p W_N⁻¹ g)`) are landed, an instance of
`(T_adj, h_adj, h_old)` is mechanical and the unconditional bad-prime
newspace preservation follows by directly applying this theorem.

Mathematical references: Diamond–Shurman §5.5 Prop 5.5.1 (Atkin–Lehner
involutions), §5.6 Prop 5.6.2 (T_p preserves new/old subspaces); Miyake
§4.6.5 (Atkin–Lehner) and §4.6.6 (Hecke operators on the new subspace). -/
theorem heckeT_n_cusp_preserves_cuspFormsNew_at_divN_of_petersson_adjoint
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p] (_hp : p.Prime)
    (_hpN : ¬ Nat.Coprime p N)
    (T_adj : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
             CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_adj : ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      petN (heckeT_n_cusp k p f) g = petN f (T_adj g))
    (h_old : ∀ (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      g ∈ cuspFormsOld N k → T_adj g ∈ cuspFormsOld N k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k p f ∈ cuspFormsNew N k := by
  intro g hg
  rw [h_adj f g]
  exact hf _ (h_old g hg)


end HeckeRing.GL2
