/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms.FrickeTwist
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Newforms: Fricke slash-equality input and completed Mellin-Dirichlet bridges

Per-newform Dirichlet-zero data, the Fricke slash-equality structured input and its
strong-multiplicity-one consumers, the completed Mellin-Dirichlet bridge, and the
Euler-stripping arithmetic / Hecke-multiplicative-structure inputs.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The `T = ∅` specialization of `Newform.PerNewformFullDirichletData`, built from
the irreducible classical inputs (character non-trivialities, the Dirichlet zero,
the squared-character L-value non-cancellation, and the universal-F clause). -/
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
  h_factors_ne := fun p hp ↦ absurd hp (Finset.notMem_empty p)
  h_num_an := by
    simp only [Finset.prod_empty, mul_one]
    exact Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((DirichletCharacter.differentiable_LFunction h_chi_sq_ne_one).comp (by fun_prop))
      s₀ (Set.mem_univ _)
  h_den_an := by
    simp only [Finset.prod_empty, mul_one]
    exact Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop))
      s₀ (Set.mem_univ _)
  h_den_finite := by
    set den_fn : ℂ → ℂ := fun s ↦
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) *
      ∏ p ∈ (∅ : Finset Nat.Primes),
        (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹
    have h_an_univ : AnalyticOnNhd ℂ den_fn Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr <| by
        simp only [den_fn, Finset.prod_empty, mul_one]
        exact (DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop)
    set s' : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ)
    have h_re_gt_one : (1 : ℝ) < (2 * s' - (k : ℂ) + 1).re := by
      have h_re : (2 * s' - (k : ℂ) + 1).re = 5 := by
        simp [s', Complex.add_re, Complex.sub_re, Complex.mul_re,
          Complex.intCast_re, Complex.intCast_im]
        ring
      rw [h_re]; norm_num
    have h_order_s'_ne_top : analyticOrderAt den_fn s' ≠ ⊤ := by
      rw [(h_an_univ s' (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr <| by
        simp only [den_fn, Finset.prod_empty, mul_one]
        rw [DirichletCharacter.LFunction_eq_LSeries _ h_re_gt_one]
        exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ h_re_gt_one]
      exact ENat.zero_ne_top
    rw [(h_an_univ s₀ (Set.mem_univ _)).meromorphicOrderAt_eq]
    intro h
    rcases ENat.ne_top_iff_exists.mp (AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
      h_an_univ isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) h_order_s'_ne_top)
      with ⟨n, hn⟩
    rw [← hn] at h
    simp at h
  h_clause := h_clause

/-- The denominator-side per-prime factor
`s ↦ (1 - χ̃²(p) · p^{-(2(2s-k+1))})⁻¹` is analytic at any point `s₀` where the
underlying `1 - χ̃²(p) · p^{-(2(2s₀-k+1))}` does not vanish. -/
theorem Newform.den_factor_analytic_at
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ) (s₀ : ℂ) (p : Nat.Primes)
    (h_ne : (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) :
    AnalyticAt ℂ
      (fun (s : ℂ) ↦ (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ :=
  (analyticAt_const.sub (analyticAt_const.mul (AnalyticAt.cpow analyticAt_const (by fun_prop)
    (Complex.natCast_mem_slitPlane.mpr p.prop.pos.ne')))).inv h_ne

/-- The general-`T` analogue of
`Newform.PerNewformFullDirichletData_T_empty_of_classicalInputs`, taking per-prime
factor-analyticity hypotheses `h_num_factor_an`, `h_den_factor_an` explicitly. -/
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
      (fun s ↦ Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_factor_an : ∀ p ∈ T, AnalyticAt ℂ
      (fun (s : ℂ) ↦ (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀)
    (h_den_finite :
      meromorphicOrderAt
        (fun s ↦
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
  h_num_an :=
    AnalyticAt.mul ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((DirichletCharacter.differentiable_LFunction h_chi_sq_ne_one).comp (by fun_prop)))
      s₀ (Set.mem_univ _)) (Finset.analyticAt_fun_prod _ h_num_factor_an)
  h_den_an :=
    AnalyticAt.mul ((Complex.analyticOnNhd_univ_iff_differentiable.mpr
      ((DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop)))
      s₀ (Set.mem_univ _)) (Finset.analyticAt_fun_prod _ h_den_factor_an)
  h_den_finite := h_den_finite
  h_clause := h_clause

/-- A reduction of `Newform.PerNewformFullDirichletData_of_classicalInputs` that
drops the per-prime denominator-factor analyticity hypothesis, deriving it from the
per-prime non-vanishing hypothesis via `Newform.den_factor_analytic_at`. -/
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
      (fun s ↦ Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_finite :
      meromorphicOrderAt
        (fun s ↦
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
    (fun p hp ↦ Newform.den_factor_analytic_at χ s₀ p (h_den_factors_ne p hp))
    h_den_finite h_clause

/-- Drops the explicit `h_clause` hypothesis from
`Newform.PerNewformFullDirichletData_of_classicalInputs_redDen`, deriving it from
`Newform.FullDirichletQuotientUniversalFClause_of_T111`. -/
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
      (fun s : ℂ ↦ ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p))
    (h_num_factor_an : ∀ p ∈ T, AnalyticAt ℂ
      (fun s ↦ Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_finite :
      meromorphicOrderAt
        (fun s ↦
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
      (fun p hp ↦ (h_factors_ne p hp).2)
      h_den_factors_ne)

/-- Strong multiplicity one via per-newform Dirichlet-zero data, Hecke continuation,
and newform uniqueness, replacing the giant `h_data` blob of
`strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique`
with the per-newform Dirichlet-zero hypothesis cluster. -/
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
        Newform.PerNewformFullDirichletData f χ S)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique
    h_unique h_hecke h_dirZero f g χ hfχ hgχ S h

/-- Strong multiplicity one replacing the global `Newform.HeckeEntireExtension`
hypothesis with per-newform structured `Newform.HeckeFEData`, chaining through
`strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZero_of_newformUnique`. -/
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
        Newform.PerNewformFullDirichletData f χ S)
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

/-- Strong multiplicity one from per-newform `Newform.HeckeFEData` and
`Newform.PerNewformFullDirichletData` plus newform uniqueness: the SMO-facing
endpoint that consumers should target. -/
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
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_analyticContradiction_of_newformUnique h_unique
    (Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
      (Newform.HeckeEntireExtension_of_HeckeFEData h_FE)
      (Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
        fun _ _ _ f χ hfχ S h_bad ↦
          Newform.full_pole_witness_data_of_PerNewformFullDirichletData f χ S
            (h_data f χ hfχ S h_bad)))
    f g χ hfχ hgχ S h

/-- Strong multiplicity one endpoint that drops the explicit
`Newform.PerNewformFullDirichletData` hypothesis in favour of the classical T111
ingredients per `(f, χ, S, h_bad)`, deriving the universal-F clause internally. -/
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
            (fun s : ℂ ↦ ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) ∧
          (∀ p ∈ T, AnalyticAt ℂ
            (fun s ↦ Newform.eulerFactor_stripped f χ S s p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀) ∧
          meromorphicOrderAt
            (fun s ↦
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
  let h_ex := h_T111_data f χ hfχ S h_bad
  let T : Finset Nat.Primes := h_ex.choose
  let s₀ : ℂ := h_ex.choose_spec.choose
  obtain ⟨hT_iff, h_χ_ne_one, h_chi_sq_ne_one, h_abscissa_lt, h_zero,
    h_num_LF_ne, h_factors_ne, h_den_factors_ne, h_EFP_diff, h_num_factor_an,
    h_den_finite⟩ := h_ex.choose_spec.choose_spec
  exact Newform.PerNewformFullDirichletData_of_classicalInputs_T111
    f χ hfχ S h_bad T hT_iff s₀ h_χ_ne_one h_chi_sq_ne_one h_abscissa_lt
    h_zero h_num_LF_ne h_factors_ne h_den_factors_ne h_EFP_diff
    h_num_factor_an h_den_finite

/-- Direct bridge `Newform.HeckeFEData` + `Newform.PerNewformFullDirichletData` ⇒
`Newform.AnalyticContradiction`, without going through newform uniqueness / SMO. -/
theorem Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    (Newform.HeckeEntireExtension_of_HeckeFEData h_FE)
    (Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
      fun _ _ _ f χ hfχ S h_bad ↦
        Newform.full_pole_witness_data_of_PerNewformFullDirichletData f χ S
          (h_data f χ hfχ S h_bad))

/-- Composes `Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData`
through `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`. -/
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

/-- Reduces `Newform.HeckeEntireExtension` to per-newform structured
`Newform.MellinPairData`, chaining through `Newform.HeckeFEData.ofMellinData`. -/
theorem Newform.HeckeEntireExtension_of_MellinPairData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.MellinPairData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_HeckeFEData
    (fun _N _ _k f ↦ Newform.HeckeFEData.ofMellinData (h f))

/-- Specialization of
`Newform.analyticContradiction_of_HeckeFEData_of_PerNewformFullDirichletData`
consuming `Newform.MellinPairData` instead of `Newform.HeckeFEData`. -/
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
    (fun _N _ _k f ↦ Newform.HeckeFEData.ofMellinData (h_mellin f)) h_data

/-- Composes `Newform.analyticContradiction_of_MellinPairData_of_PerNewformFullDirichletData`
through `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`. -/
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
    (fun _N _ _k f ↦ Newform.HeckeFEData.ofMellinData (h_mellin f)) h_data
    f χ hfχ S

/-- Strong multiplicity one via per-newform `Newform.MellinPairData`,
`Newform.PerNewformFullDirichletData`, and newform uniqueness. -/
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
    (fun _N _ _k f ↦ Newform.HeckeFEData.ofMellinData (h_mellin f))
    h_data f g χ hfχ hgχ S h

/-- Direct bridge `Newform.ImAxisMellinData` + `Newform.PerNewformFullDirichletData`
⇒ `Newform.AnalyticContradiction`, without going through newform uniqueness / SMO. -/
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
    (fun _N _ _k f ↦ Newform.HeckeFEData.ofImAxisData (h_imAxis f)) h_data

/-- Strong multiplicity one endpoint via the imAxis-side `Newform.ImAxisMellinData`
interface, plus `Newform.PerNewformFullDirichletData` and newform uniqueness. -/
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
    (fun _N _ _k f ↦ Newform.HeckeFEData.ofImAxisData (h_imAxis f))
    h_data f g χ hfχ hgχ S h

/-- The classical Atkin-Lehner input as a single named structure: a CuspForm `twist`
whose imaginary axis represents the Fricke slash image, plus the Mellin-Dirichlet
bridge. -/
@[ext]
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

/-- Reduces `Newform.HeckeEntireExtension` to per-newform `Newform.FrickeSlashData`:
a CuspForm-valued Fricke slash image and Mellin-Dirichlet bridge. -/
theorem Newform.HeckeEntireExtension_of_FrickeSlashData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_ImAxisMellinData
    (fun _N _ _k f ↦ Newform.ImAxisMellinData.ofFrickeSlashData f (h f))

/-- `Newform.AnalyticContradiction` from per-newform `Newform.FrickeSlashData` and
`Newform.PerNewformFullDirichletData`. -/
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
    (fun _N _ _k f ↦ Newform.ImAxisMellinData.ofFrickeSlashData f (h_slash f)) h_data

/-- Specialises
`Newform.analyticContradiction_of_FrickeSlashData_of_PerNewformFullDirichletData`
through `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`. -/
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

/-- Strong multiplicity one endpoint stated in terms of the classical Atkin-Lehner
Fricke slash-equality input `Newform.FrickeSlashData`, plus
`Newform.PerNewformFullDirichletData` and newform uniqueness. -/
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
    (fun _N _ _k f ↦ Newform.ImAxisMellinData.ofFrickeSlashData f (h_slash f))
    h_data f g χ hfχ hgχ S h

/-- `Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`
with its H1 input replaced by per-newform `Newform.FrickeSlashData`. -/
theorem Newform.analyticContradiction_of_FrickeSlashData_of_full_dirichletZeroCertificate
    (h_slash : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.FrickeSlashData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_FrickeSlashData h_slash) h_data

/-- Specialises
`Newform.analyticContradiction_of_FrickeSlashData_of_full_dirichletZeroCertificate`
through `Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`. -/
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
            (fun s ↦
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s ↦
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
            (fun s ↦
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

/-- Strong multiplicity one endpoint pairing per-newform `Newform.FrickeSlashData`
with the full T111 Dirichlet-zero data block and newform uniqueness. -/
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
            (fun s ↦
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s ↦
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
            (fun s ↦
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

/-- The smaller Dirichlet-zero variant of
`strongMultiplicityOne_of_FrickeSlashData_of_full_dirichletZeroCertificate_of_newformUnique`,
with the universal-F clause supplied as the last conjunct of `h_dirZero`. -/
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
            (fun s ↦
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s ↦
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          meromorphicOrderAt
            (fun s ↦
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

/-- `strongMultiplicityOne_of_HeckeFEData_of_classicalInputs_T111_of_newformUnique`
with the `Newform.HeckeFEData` H1 input replaced by `Newform.FrickeSlashData`,
deriving the universal-F clause internally. -/
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
            (fun s : ℂ ↦ ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) ∧
          (∀ p ∈ T, AnalyticAt ℂ
            (fun s ↦ Newform.eulerFactor_stripped f χ S s p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀) ∧
          meromorphicOrderAt
            (fun s ↦
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
  obtain ⟨hT_iff, h_χ_ne_one, h_chi_sq_ne_one, h_abscissa_lt, h_zero,
    h_num_LF_ne, h_factors_ne, h_den_factors_ne, h_EFP_diff, h_num_factor_an,
    h_den_finite⟩ := h_ex.choose_spec.choose_spec
  exact Newform.PerNewformFullDirichletData_of_classicalInputs_T111
    f χ hfχ S h_bad T hT_iff s₀ h_χ_ne_one h_chi_sq_ne_one h_abscissa_lt
    h_zero h_num_LF_ne h_factors_ne h_den_factors_ne h_EFP_diff
    h_num_factor_an h_den_finite

/-- The classical Hecke 1936 identity
`mellin (Newform.imAxis f) s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on
`Re s > k/2 + 1`, specialising `ModularForms.HasCompletedMellinIdentity`. -/
def Newform.HasCompletedMellinIdentity {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Prop :=
  ModularForms.HasCompletedMellinIdentity f.toCuspForm

/-- The classical Hecke 1936 completed Mellin–Dirichlet identity holds for every
weight-`k` newform on `Γ₁(N)` with `0 < (k : ℝ)`. -/
theorem Newform.hasCompletedMellinIdentity {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) (hk_pos : 0 < (k : ℝ)) :
    Newform.HasCompletedMellinIdentity f :=
  ModularForms.hasCompletedMellinIdentity_Gamma1_mapGL f.toCuspForm hk_pos

/-- The completed Mellin–LSeries data for a newform: a Mathlib `StrongFEPair`
carrying the honest completed Mellin–Dirichlet identity (Gamma factor, full
`lCoeff`) plus a separate finite Euler-stripping triple. -/
@[ext]
structure Newform.CompletedMellinData {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) where
  /-- Mathlib `StrongFEPair`; provides an entire `pair.Λ = mellin pair.f`. -/
  pair : StrongFEPair ℂ
  /-- The cusp-form weight is positive (cast to ℝ). -/
  hk_pos : 0 < (k : ℝ)
  /-- The completed Hecke 1936 Mellin–Dirichlet identity
  `pair.Λ s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on `Re s > k/2 + 1`. -/
  completed_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    pair.Λ s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries f.lCoeff s
  /-- Finite Euler-stripping multiplier (entire). -/
  stripping : ℂ → ℂ
  /-- The stripping multiplier is entire. -/
  stripping_diff : Differentiable ℂ stripping
  /-- Finite Euler-stripping bridge
  `LSeries f.lCoeff_stripped s = stripping s · LSeries f.lCoeff s` on
  `Re s > k/2 + 1`. -/
  stripping_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    LSeries f.lCoeff_stripped s = stripping s * LSeries f.lCoeff s

private lemma stripping_completion_factors_cancel {p : ℂ} (hp : p ≠ 0)
    {g : ℂ} (hg : g ≠ 0) (a L s : ℂ) :
    a * p ^ s * g⁻¹ * (p ^ (-s) * g * L) = a * L := by
  have h1 : p ^ s * p ^ (-s) = 1 := by
    rw [← Complex.cpow_add _ _ hp, add_neg_cancel, Complex.cpow_zero]
  field_simp
  linear_combination (a * L) * h1

private lemma eqOn_LSeries_of_entire_of_eqOn_halfPlane {c : ℕ → ℂ} {Λ : ℂ → ℂ}
    {b : ℝ} (hΛ : Differentiable ℂ Λ)
    (h_direct : ∀ {s : ℂ}, b < s.re → Λ s = LSeries c s)
    {s₀ : ℂ} (hs₀ : LSeries.abscissaOfAbsConv c < (s₀.re : EReal)) :
    Λ s₀ = LSeries c s₀ := by
  obtain ⟨σ, hσ_abs, hσ_s⟩ := EReal.exists_between_coe_real hs₀
  let U : Set ℂ := {s | (σ : ℝ) < s.re}
  have hs₀_in_U : s₀ ∈ U := by exact_mod_cast hσ_s
  have hΛ_an : AnalyticOnNhd ℂ Λ U := fun z _ ↦
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hΛ) z (Set.mem_univ _)
  have hL_an : AnalyticOnNhd ℂ (LSeries c) U := fun z hz ↦
    LSeries_analyticOnNhd c z (hσ_abs.trans (by exact_mod_cast (hz : (σ : ℝ) < z.re)))
  let z₀ : ℂ := ((max σ b + 1 : ℝ) : ℂ)
  have hz₀_re : z₀.re = max σ b + 1 := Complex.ofReal_re _
  have hzRe_gt_σ : σ < z₀.re := by rw [hz₀_re]; linarith [le_max_left σ b]
  have hzRe_gt_b : b < z₀.re := by rw [hz₀_re]; linarith [le_max_right σ b]
  have h_eq_nhds : Λ =ᶠ[nhds z₀] (LSeries c) :=
    Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨{s | b < s.re}, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzRe_gt_b,
        fun _ ↦ h_direct⟩
  exact (hΛ_an.eqOn_of_preconnected_of_eventuallyEq hL_an
    (convex_halfSpace_re_gt σ).isPreconnected hzRe_gt_σ h_eq_nhds) hs₀_in_U

/-- Produces the global `Newform.HeckeEntireExtension` predicate from per-newform
`Newform.CompletedMellinData`, via the analytic identity principle. -/
theorem Newform.HeckeEntireExtension_of_CompletedMellinData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.CompletedMellinData f) :
    Newform.HeckeEntireExtension := by
  intro N _ k f
  obtain ⟨pair, hk_pos, h_completed, stripping, h_strip_diff, h_strip_bridge⟩ := h f
  have h2π : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have : NeZero (2 * Real.pi : ℂ) := ⟨h2π⟩
  let Λ : ℂ → ℂ := fun s ↦
    stripping s * ((2 * Real.pi : ℂ) ^ s) * (Complex.Gamma s)⁻¹ * pair.Λ s
  have h_Λ_diff : Differentiable ℂ Λ :=
    ((h_strip_diff.mul (differentiable_const_cpow_of_neZero (2 * Real.pi : ℂ))).mul
      Complex.differentiable_one_div_Gamma).mul pair.differentiable_Λ
  have h_direct :
      ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
        Λ s = LSeries f.lCoeff_stripped s := by
    intro s hs
    have hs_re_pos : 0 < s.re := by linarith
    show stripping s * ((2 * Real.pi : ℂ) ^ s) * (Complex.Gamma s)⁻¹ * pair.Λ s
        = LSeries f.lCoeff_stripped s
    rw [h_completed hs, h_strip_bridge hs]
    exact stripping_completion_factors_cancel h2π
      (Complex.Gamma_ne_zero_of_re_pos hs_re_pos) (stripping s) (LSeries f.lCoeff s) s
  exact ⟨Λ, h_Λ_diff, fun {_} hs₀ ↦
    eqOn_LSeries_of_entire_of_eqOn_halfPlane h_Λ_diff h_direct hs₀⟩

/-- The corrected Fricke / completed Mellin data for a newform: the Atkin-Lehner /
Fricke slash-equality data (`twist`, `slash_eq`) together with the analytic content
needed to construct `Newform.CompletedMellinData`. -/
@[ext]
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
  /-- The completed Hecke 1936 Mellin–Dirichlet identity
  `pair.Λ s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on `Re s > k/2 + 1`. -/
  completed_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    pair.Λ s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries f.lCoeff s
  /-- Finite Euler-stripping multiplier (entire). -/
  stripping : ℂ → ℂ
  /-- The stripping multiplier is entire. -/
  stripping_diff : Differentiable ℂ stripping
  /-- Finite Euler-stripping bridge
  `LSeries f.lCoeff_stripped s = stripping s · LSeries f.lCoeff s` on
  `Re s > k/2 + 1`. -/
  stripping_bridge : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    LSeries f.lCoeff_stripped s = stripping s * LSeries f.lCoeff s

private lemma imAxis_scaled_locallyIntegrableOn {N : ℕ} [NeZero N] {k : ℤ}
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MeasureTheory.LocallyIntegrableOn
      (fun t : ℝ ↦ _root_.ModularForms.imAxis twist (t / (N : ℝ)))
      (Set.Ioi (0 : ℝ)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have h_div_cts : ContinuousOn (fun t : ℝ ↦ t / (N : ℝ)) (Set.Ioi (0 : ℝ)) :=
    Continuous.continuousOn (by fun_prop)
  exact ((_root_.ModularForms.continuousOn_imAxis twist).comp h_div_cts
    fun t ht ↦ div_pos ht hN_pos).locallyIntegrableOn measurableSet_Ioi

private lemma imAxis_scaled_rapidDecay {N : ℕ} [NeZero N] {k : ℤ}
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ _root_.ModularForms.imAxis twist (x / (N : ℝ)) - 0)
      (fun x : ℝ ↦ x ^ r) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have h_twist_decay :=
    (_root_.ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay
      twist (Newform.cuspForm_Gamma1_hasImAxisExponentialDecay twist)) r
  have h_tendsto : Filter.Tendsto (fun t : ℝ ↦ t / (N : ℝ))
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

private lemma imAxis_scaled_feq {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N)
    {x : ℝ} (hx : x ∈ Set.Ioi (0 : ℝ)) :
    Newform.imAxis f (1 / x) =
      (((N : ℂ) ^ (1 - k) * Complex.I ^ k) * ((x ^ (k : ℝ) : ℝ) : ℂ)) •
        _root_.ModularForms.imAxis twist (x / (N : ℝ)) := by
  have h_cast : ((x ^ (k : ℝ) : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ k := by
    rw [Real.rpow_intCast x k, Complex.ofReal_zpow]
  rw [Newform.imAxis_feq_of_slashEq f twist slash_eq hx, h_cast, smul_eq_mul]

/-- Constructs `Newform.CompletedFrickeData` from a CuspForm-supplied Atkin-Lehner
twist and an Euler-stripping multiplier, with `pair` built from the `imAxis`
infrastructure and `completed_bridge` discharged by
`Newform.hasCompletedMellinIdentity`. -/
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
    Newform.CompletedFrickeData f where
  twist := twist
  slash_eq := slash_eq
  pair :=
    { f := Newform.imAxis f
      g := fun t ↦ _root_.ModularForms.imAxis twist (t / (N : ℝ))
      k := (k : ℝ)
      ε := (N : ℂ) ^ (1 - k) * Complex.I ^ k
      f₀ := 0
      g₀ := 0
      hf_int := Newform.locallyIntegrableOn_imAxis f
      hg_int := imAxis_scaled_locallyIntegrableOn twist
      hk := hk_pos
      hε := mul_ne_zero (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N)))
        (zpow_ne_zero _ Complex.I_ne_zero)
      h_feq := fun _ hx ↦ imAxis_scaled_feq f twist slash_eq hx
      hf_top := Newform.imAxis_rapidDecay f
      hg_top := imAxis_scaled_rapidDecay twist
      hf₀ := rfl
      hg₀ := rfl }
  hk_pos := hk_pos
  completed_bridge := fun {_} hs ↦ by
    rw [Newform.lCoeff_eq_modularForms_lCoeff_funext f]
    exact Newform.hasCompletedMellinIdentity f hk_pos hs
  stripping := stripping
  stripping_diff := stripping_diff
  stripping_bridge := stripping_bridge

/-- Existence of a CuspForm-valued Atkin-Lehner Fricke involution image
`twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k` whose underlying `ℍ → ℂ` map
equals the slash `⇑f.toCuspForm.toModularForm' ∣[k] W_N`. -/
def Newform.HasFrickeTwistAsCuspForm
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) : Prop :=
  ∃ twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N

/-- Existence of an entire multiplier `stripping : ℂ → ℂ` such that the stripped
Newform L-series factors as `stripping(s) · LSeries f.lCoeff s` on the
absolute-convergence half-plane `Re s > k/2 + 1`. -/
def Newform.HasEulerStrippingMultiplier
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) : Prop :=
  ∃ stripping : ℂ → ℂ,
    Differentiable ℂ stripping ∧
    ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      LSeries f.lCoeff_stripped s = stripping s * LSeries f.lCoeff s

/-- When `S` is the bad-prime Finset (`hS : ∀ p, p ∈ S ↔ (p : ℕ) ∣ N`),
`LSeries.coprimeStrip S f.lCoeff` recovers the level-aware `Newform.lCoeff_stripped`
sequence. -/
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
    have hp_dvd_gcd : (p : ℕ) ∣ Nat.gcd n N := Nat.dvd_gcd h_p_n ((hS p).mp hp)
    rw [show Nat.gcd n N = 1 from h] at hp_dvd_gcd
    exact p.prop.one_lt.ne' (Nat.dvd_one.mp hp_dvd_gcd)
  · rw [if_neg h, if_neg]
    push Not
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · have hN_ne_one : N ≠ 1 := fun hN1 ↦ h (hN1 ▸ Nat.coprime_one_right 0)
      obtain ⟨p, hp, hpN⟩ := Nat.exists_prime_and_dvd hN_ne_one
      exact ⟨⟨p, hp⟩, (hS ⟨p, hp⟩).mpr hpN, dvd_zero _⟩
    · obtain ⟨p, hp, hp_dvd_gcd⟩ := Nat.exists_prime_and_dvd (h : Nat.gcd n N ≠ 1)
      exact ⟨⟨p, hp⟩, (hS ⟨p, hp⟩).mpr (hp_dvd_gcd.trans (Nat.gcd_dvd_right _ _)),
        hp_dvd_gcd.trans (Nat.gcd_dvd_left _ _)⟩

/-- Reduces `Newform.HasEulerStrippingMultiplier f` to the full Hecke-eigenform Euler
product plus the bad-prime local Euler-factor identification and non-vanishing at
primes `p ∣ N`, via `LSeries.hasEulerStrippingMultiplier_of_eulerProduct`. -/
theorem Newform.hasEulerStrippingMultiplier_of_fullEulerProduct
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset Nat.Primes)
    (hS : ∀ p : Nat.Primes, p ∈ S ↔ (p : ℕ) ∣ N)
    (hf_full_euler : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      HasProd
        (fun p : Nat.Primes ↦
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
  have hg_euler : ∀ ⦃s : ℂ⦄, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      HasProd
        (fun p : Nat.Primes ↦
          ∑' e : ℕ,
            LSeries.term (LSeries.coprimeStrip S f.lCoeff) s ((p : ℕ) ^ e))
        (LSeries (LSeries.coprimeStrip S f.lCoeff) s) := by
    intro s hs
    rw [h_strip_eq]
    exact f.lSeries_stripped_hasProd χ hfχ hs
  obtain ⟨stripping, h_diff, h_bridge⟩ :=
    LSeries.hasEulerStrippingMultiplier_of_eulerProduct
      S (fun p : Nat.Primes ↦ f.lCoeff (p : ℕ)) f.lCoeff
      (fun s : ℂ ↦ ((k : ℝ) / 2 + 1 : ℝ) < s.re)
      f.lCoeff_one hf_full_euler hg_euler h_bad_local_inv h_bad_local_ne_zero
  refine ⟨stripping, h_diff, ?_⟩
  intro s hs
  rw [← h_strip_eq]
  exact h_bridge hs

/-- The bundled arithmetic input that
`Newform.hasEulerStrippingMultiplier_of_arithmeticInput` consumes: the
character/eigenform context, the bad-prime Finset, the full Newform Euler product,
and the bad-prime local Euler-factor identification and non-vanishing. -/
@[ext]
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
      (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term f.lCoeff s ((p : ℕ) ^ e))
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

/-- Produces `Newform.HasEulerStrippingMultiplier f` from a bundled
`Newform.EulerStrippingArithmeticInput f χ`, via
`Newform.hasEulerStrippingMultiplier_of_fullEulerProduct`. -/
theorem Newform.hasEulerStrippingMultiplier_of_arithmeticInput
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (input : Newform.EulerStrippingArithmeticInput f χ) :
    Newform.HasEulerStrippingMultiplier f :=
  f.hasEulerStrippingMultiplier_of_fullEulerProduct χ input.hfχ
    input.S input.hS input.hf_full_euler
    input.h_bad_local_inv input.h_bad_local_ne_zero

/-- Bundles the two classical arithmetic facts about a Newform's Fourier coefficient
sequence — full coprime multiplicativity and the bad-prime closed form — that
suffice to construct `Newform.EulerStrippingArithmeticInput f χ`. -/
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

/-- For a prime `p ∣ N`, the period-1 Fourier coefficient of
`heckeT_p_divN k p hp hpN f.toCuspForm.toModularForm'` at index `m` equals
`f.lCoeff (p * m)`. -/
lemma Newform.lCoeff_heckeT_p_divN_apply
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) ((heckeT_p_divN k p hp hpN)
        f.toCuspForm.toModularForm')).coeff m =
      f.lCoeff (p * m) := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  rw [qExpansion_one_heckeT_p_divN_coeff hp hpN f.toCuspForm.toModularForm' m]
  rfl

/-- For a prime `p ∣ N` and exponent `r`, applying `heckeT_p_divN k p hp hpN` `r`
times to `f.toCuspForm.toModularForm'` gives a ModularForm whose `m`-th period-1
Fourier coefficient equals `f.lCoeff (p^r * m)`. -/
lemma Newform.lCoeff_heckeT_p_divN_iterate_apply
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) (r m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        (((fun g ↦ heckeT_p_divN k p hp hpN g) : ModularForm _ k → ModularForm _ k)^[r]
          f.toCuspForm.toModularForm')).coeff m =
      f.lCoeff (p ^ r * m) := by
  have : NeZero p := ⟨hp.pos.ne'⟩
  induction r generalizing m with
  | zero =>
    simp only [pow_zero, Function.iterate_zero_apply, one_mul]
    rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply',
      qExpansion_one_heckeT_p_divN_coeff hp hpN _ m, ih (p * m)]
    congr 1
    ring

/-- For a prime `p ∣ N` and `f ∈ S_k^new`, `heckeT_n_cusp k p f` lies in `S_k^new`,
given an explicit Petersson-adjoint operator `T_adj` for `T_p` at level `Γ₁(N)`
that preserves the old-subspace `cuspFormsOld N k`. -/
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
    heckeT_n_cusp k p f ∈ cuspFormsNew N k :=
  fun g hg ↦ h_adj f g ▸ hf _ (h_old g hg)

end HeckeRing.GL2
