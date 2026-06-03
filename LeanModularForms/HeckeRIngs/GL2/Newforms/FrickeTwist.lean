/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms.Fricke
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: Dirichlet-quotient pole-witness chain and full T111 certificate

The downstream Dirichlet-quotient pole-witness chain up to the per-newform full
Dirichlet-zero data (`Newform.PerNewformFullDirichletData_pre`) feeding the
Strong Multiplicity One bridge.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.

## Main definitions

* `Newform.NoEntireExtensionUnderBadPrime`: bad-prime-zero ⇒ no entire extension.
* `Newform.DirichletQuotientHasPoleUnderBadPrime`: per-newform Dirichlet pole witness.
* `Newform.HasDirichletZeroCertificate`: per-newform Dirichlet-zero certificate.
* `Newform.DirichletQuotientUniversalFClause`, `Newform.FullDirichletQuotientUniversalFClause`:
  analytic-continuation universal-`F` clauses (simplified / full T111 quotient).
* `Newform.PerNewformFullDirichletData_pre`: bundled per-newform full T111
  Dirichlet-zero ingredients (import-cycle-avoiding twin of the canonical
  `Newform.PerNewformFullDirichletData` in `MellinBridges.lean`).

## Main results

* `strongMultiplicityOne_of_HeckeEntireExtension_of_HasDirichletZeroCertificate_of_newformUnique`:
  reduces Strong Multiplicity One to the Hecke entire extension and a Dirichlet-zero certificate.
* `Newform.analyticContradiction_of_HeckeFEData_of_full_dirichletZeroCertificate`:
  full-quotient bridge from Hecke FE data + Dirichlet-zero certificate to the analytic
  contradiction used downstream.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}



/-- For every newform `f` in a Nebentypus character eigenspace and every finite
exceptional set `S`, the bad-prime-zero hypothesis forces the stripped Dirichlet
series `LSeries f.lCoeff_stripped` to *not* admit an entire extension to `ℂ`. -/
def Newform.NoEntireExtensionUnderBadPrime : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
    f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
    ∀ (S : Finset ℕ),
      (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
        q ∉ S → f.lCoeff q = 0) →
      ¬ LSeries.HasEntireExtension f.lCoeff_stripped

/-- Combining `Newform.HeckeEntireExtension` and
`Newform.NoEntireExtensionUnderBadPrime` produces
`Newform.AnalyticContradiction`. -/
theorem Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    (h_hecke : Newform.HeckeEntireExtension)
    (h_no : Newform.NoEntireExtensionUnderBadPrime) :
    Newform.AnalyticContradiction :=
  fun _ _ _ f χ hfχ S h_bad ↦ h_no f χ hfχ S h_bad (h_hecke f)

/-- If every newform's stripped Dirichlet series admits a meromorphic extension
with a pole under the bad-prime hypothesis, then
`Newform.NoEntireExtensionUnderBadPrime` follows. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_meromorphicPole
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        LSeries.HasMeromorphicExtensionWithPole f.lCoeff_stripped) :
    Newform.NoEntireExtensionUnderBadPrime :=
  fun _ _ _ f χ hfχ S h_bad ↦
    LSeries.HasMeromorphicExtensionWithPole.not_hasEntireExtension (h f χ hfχ S h_bad)

/-- For every newform-character pair and exceptional set satisfying the bad-prime
hypothesis, the existence of a Dirichlet quotient `num/den` that is a
meromorphic-extension witness for `LSeries f.lCoeff_stripped` with a strict
order inequality at a pole point `s₀`. -/
def Newform.DirichletQuotientHasPoleUnderBadPrime : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
    f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
    ∀ (S : Finset ℕ),
      (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
        q ∉ S → f.lCoeff q = 0) →
      ∃ (num den : ℂ → ℂ) (s₀ : ℂ),
        MeromorphicAt num s₀ ∧
        MeromorphicAt den s₀ ∧
        meromorphicOrderAt num s₀ ≠ ⊤ ∧
        meromorphicOrderAt den s₀ ≠ ⊤ ∧
        meromorphicOrderAt num s₀ < meromorphicOrderAt den s₀ ∧
        ∀ F : ℂ → ℂ, Differentiable ℂ F →
          (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
            F s = LSeries f.lCoeff_stripped s) →
          F =ᶠ[nhdsWithin s₀ {s₀}ᶜ] (num / den)

/-- `Newform.DirichletQuotientHasPoleUnderBadPrime` implies
`Newform.NoEntireExtensionUnderBadPrime`. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole
    (h : Newform.DirichletQuotientHasPoleUnderBadPrime) :
    Newform.NoEntireExtensionUnderBadPrime := by
  apply Newform.noEntireExtensionUnderBadPrime_of_meromorphicPole
  intro N _ k f χ hfχ S h_bad
  obtain ⟨num, den, s₀, h_num_mero, h_den_mero, h_num_finite, h_den_finite,
          h_lt, h_punc⟩ := h f χ hfχ S h_bad
  refine ⟨num / den, s₀, h_num_mero.div h_den_mero, ?_, h_punc⟩
  exact meromorphicOrderAt_div_neg_of_orderAt_lt h_num_mero h_den_mero
    h_num_finite h_den_finite h_lt

private lemma meromorphicOrderAt_ne_top_of_analyticAt_ne_zero {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) : meromorphicOrderAt g z ≠ ⊤ := by
  simp [hg.meromorphicOrderAt_eq, hg.analyticOrderAt_eq_zero.mpr hgz]

private lemma meromorphicOrderAt_ne_top_of_ne_zero_somewhere {g : ℂ → ℂ}
    (hg_diff : Differentiable ℂ g) (z w : ℂ) (hgw : g w ≠ 0) :
    meromorphicOrderAt g z ≠ ⊤ := by
  have hg_an : AnalyticOnNhd ℂ g Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg_diff
  rw [(hg_an z (Set.mem_univ _)).meromorphicOrderAt_eq]
  have h_w : analyticOrderAt g w ≠ ⊤ :=
    ((hg_an w (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hgw).symm ▸ by simp
  intro h
  rw [ENat.map_eq_top_iff] at h
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected hg_an
    isPreconnected_univ (Set.mem_univ _) (Set.mem_univ _) h_w h

private lemma meromorphicOrderAt_lt_of_ne_zero_of_zero {num den : ℂ → ℂ} {z : ℂ}
    (hnum : AnalyticAt ℂ num z) (hden : AnalyticAt ℂ den z)
    (hnum_ne : num z ≠ 0) (hden_zero : den z = 0)
    (hden_fin : meromorphicOrderAt den z ≠ ⊤) :
    meromorphicOrderAt num z < meromorphicOrderAt den z := by
  rw [hnum.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq,
    hnum.analyticOrderAt_eq_zero.mpr hnum_ne]
  have h_den_ne_top : analyticOrderAt den z ≠ ⊤ := by
    rw [hden.meromorphicOrderAt_eq] at hden_fin; simpa using hden_fin
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp h_den_ne_top
  have h_m_ge_one : 1 ≤ m := by
    rcases m with _ | m'
    · exact absurd (by rw [← hm]; rfl) (hden.analyticOrderAt_ne_zero.mpr hden_zero)
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
  rw [← hm]
  simpa using h_m_ge_one

private lemma LFunction_dirichletLift_ne_zero_of_one_lt_re
    {N : ℕ} [NeZero N] {ψ : DirichletCharacter ℂ N} {z : ℂ} (hz : 1 < z.re) :
    DirichletCharacter.LFunction ψ z ≠ 0 := by
  simpa [DirichletCharacter.LFunction_eq_LSeries _ hz] using
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hz

private lemma differentiable_LFunction_comp {N : ℕ} [NeZero N]
    {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {g : ℂ → ℂ} (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun s ↦ DirichletCharacter.LFunction ψ (g s)) :=
  (DirichletCharacter.differentiable_LFunction hψ).comp hg



private lemma t111_re_conditions {k : ℤ} {s : ℂ} (hs_re : (k : ℝ) / 2 + 1 < s.re) :
    1 < (2 * s - k + 1).re ∧ 1 < (2 * (2 * s - k + 1)).re := by
  have h1 : (2 * s - (k : ℂ) + 1).re = 2 * s.re - k + 1 := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re]
  have h2 : (2 * (2 * s - (k : ℂ) + 1)).re = 4 * s.re - 2 * k + 2 := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re]; ring
  exact ⟨by rw [h1]; linarith, by rw [h2]; linarith⟩

private lemma t111_geom_bound {N : ℕ} [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ) {k : ℤ} {s : ℂ}
    (hs_re : (k : ℝ) / 2 + 1 < s.re) {q : ℕ} (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
      ((q : ℂ) ^ (-s)) ^ 2‖ < 1 :=
  Newform.norm_eulerFactor_argument_lt_one χ k hq.two_le hqN _ (by linarith)

private lemma t111_one_pm_ne {N : ℕ} [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ) {k : ℤ} {s : ℂ}
    (hs_re : (k : ℝ) / 2 + 1 < s.re) {q : ℕ} (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 ∧
    (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 := by
  have h_norm_lt : ‖(χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (-(2 * s - k + 1))‖ < 1 :=
    Newform.norm_chi_q_cpow_neg_lt_one_of_re_pos χ hq.two_le hqN (by
      have : (2 * s - (k : ℂ) + 1).re = 2 * s.re - k + 1 := by
        simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re]
      rw [this]; linarith)
  exact ⟨Newform.one_add_ne_zero_of_norm_lt_one h_norm_lt,
         Newform.one_sub_ne_zero_of_norm_lt_one h_norm_lt⟩

private lemma differentiable_prod_linearFactor {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (T : Finset Nat.Primes) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) :
    Differentiable ℂ (fun s : ℂ ↦
      ∏ p ∈ T, (1 - ψ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-(g s)))) := by
  refine Differentiable.fun_finset_prod fun p _ ↦
    (differentiable_const _).sub <| Differentiable.const_mul (fun s ↦
      (AnalyticAt.cpow analyticAt_const
          (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg s (Set.mem_univ _)).neg
        (Complex.natCast_mem_slitPlane.mpr p.prop.pos.ne')).differentiableAt) _

private lemma prod_linearFactor_eventually_ne_zero {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) (T : Finset Nat.Primes) {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (s₀ : ℂ)
    (h : ∀ p ∈ T, (1 - ψ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-(g s₀))) ≠ 0) :
    ∀ᶠ s in nhdsWithin s₀ {s₀}ᶜ,
      (∏ p ∈ T, (1 - ψ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-(g s)))) ≠ 0 :=
  ((differentiable_prod_linearFactor ψ T hg).continuous.continuousAt.eventually_ne
    (Finset.prod_ne_zero_iff.mpr h)).filter_mono nhdsWithin_le_nhds

private lemma linearFactor_ne_zero_of_one_lt_re {N : ℕ} [NeZero N]
    (ψ : DirichletCharacter ℂ N) {p : ℕ} (hp : Nat.Prime p) {z : ℂ} (hz : 1 < z.re) :
    (1 - ψ (p : ZMod N) * (p : ℂ) ^ (-z)) ≠ 0 :=
  fun h_zero ↦ Newform.dirichletLift_eulerFactor_ne_zero ψ hp hz (by rw [h_zero, inv_zero])

private lemma mul_eq_mul_of_mul_inv_eq {A B C D E F : ℂ}
    (h : A * B * C⁻¹ = D * (E * F⁻¹)) (hC : C ≠ 0) (hF : F ≠ 0) :
    A * B * F = D * E * C := by
  field_simp at h
  linear_combination h

private lemma eq_div_prod_inv_of_mul_prod_eq {T : Finset Nat.Primes} {Fs A B : ℂ}
    {e l₁ l₂ : Nat.Primes → ℂ}
    (h_id : Fs * A * (∏ p ∈ T, l₁ p) = B * (∏ p ∈ T, e p) * ∏ p ∈ T, l₂ p)
    (hA : A ≠ 0) (h_l₁ : (∏ p ∈ T, l₁ p) ≠ 0) (h_l₂ : (∏ p ∈ T, l₂ p) ≠ 0) :
    Fs = B * (∏ p ∈ T, e p * (l₁ p)⁻¹) / (A * ∏ p ∈ T, (l₂ p)⁻¹) := by
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib,
    eq_div_iff (mul_ne_zero hA (inv_ne_zero h_l₂))]
  field_simp [h_l₁]
  linear_combination h_id

/-- From a newform-character pair, an explicit pole point `s₀`, a Dirichlet
L-function zero at `2 s₀ - k + 1`, the corresponding non-cancellation, and the
analytic-continuation clause, exhibit the inner pole witness `(num, den, s₀)` of
`Newform.DirichletQuotientHasPoleUnderBadPrime`. -/
theorem Newform.dirichletQuotient_pole_witness_of_dirichletZero
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_den_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_ne_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
      (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_univ_F : ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
        F s = LSeries f.lCoeff_stripped s) →
      F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
        ((fun s ↦ DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
          (2 * (2 * s - k + 1))) /
        (fun s ↦ DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))) :
    ∃ (num den : ℂ → ℂ) (s₀' : ℂ),
      MeromorphicAt num s₀' ∧
      MeromorphicAt den s₀' ∧
      meromorphicOrderAt num s₀' ≠ ⊤ ∧
      meromorphicOrderAt den s₀' ≠ ⊤ ∧
      meromorphicOrderAt num s₀' < meromorphicOrderAt den s₀' ∧
      ∀ F : ℂ → ℂ, Differentiable ℂ F →
        (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
          F s = LSeries f.lCoeff_stripped s) →
        F =ᶠ[nhdsWithin s₀' {s₀'}ᶜ] (num / den) := by
  set num : ℂ → ℂ := fun s ↦ DirichletCharacter.LFunction
    (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
    (2 * (2 * s - k + 1))
  set den : ℂ → ℂ := fun s ↦ DirichletCharacter.LFunction
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)
  have h_den_diff : Differentiable ℂ den := differentiable_LFunction_comp h_χ_ne_one (by fun_prop)
  have h_num_an : AnalyticAt ℂ num s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (differentiable_LFunction_comp h_chi_sq_ne_one (by fun_prop)) s₀ (Set.mem_univ _)
  have h_den_an : AnalyticAt ℂ den s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_den_diff s₀ (Set.mem_univ _)
  set s' : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ)
  have h_re_gt_one : (1 : ℝ) < (2 * s' - (k : ℂ) + 1).re := by
    have : (2 * s' - (k : ℂ) + 1).re = 5 := by
      simp [s', Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.intCast_re, Complex.intCast_im]; ring
    rw [this]; norm_num
  have h_den_fin : meromorphicOrderAt den s₀ ≠ ⊤ :=
    meromorphicOrderAt_ne_top_of_ne_zero_somewhere h_den_diff s₀ s'
      (LFunction_dirichletLift_ne_zero_of_one_lt_re h_re_gt_one)
  exact ⟨num, den, s₀, h_num_an.meromorphicAt, h_den_an.meromorphicAt,
    meromorphicOrderAt_ne_top_of_analyticAt_ne_zero h_num_an h_num_ne_zero, h_den_fin,
    meromorphicOrderAt_lt_of_ne_zero_of_zero h_num_an h_den_an h_num_ne_zero h_den_zero h_den_fin,
    h_univ_F⟩

/-- Given, for every newform-character pair satisfying the bad-prime hypothesis,
a per-newform pole certificate (pole point, character non-trivialities, Dirichlet
zero, non-cancellation, analytic-continuation clause), conclude
`Newform.NoEntireExtensionUnderBadPrime`. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (s₀ : ℂ),
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) ≠ 1 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)
            (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          ∀ F : ℂ → ℂ, Differentiable ℂ F →
            (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
              F s = LSeries f.lCoeff_stripped s) →
            F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
              ((fun s ↦ DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N)
                (2 * (2 * s - k + 1))) /
              (fun s ↦ DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1)))) :
    Newform.NoEntireExtensionUnderBadPrime := by
  apply Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole
  intro N _ k f χ hfχ S h_bad
  obtain ⟨s₀, h_χ_ne, h_χ_sq_ne, h_den_zero, h_num_ne, h_univ⟩ :=
    h_cert f χ hfχ S h_bad
  exact Newform.dirichletQuotient_pole_witness_of_dirichletZero f χ s₀
    h_χ_ne h_χ_sq_ne h_den_zero h_num_ne h_univ

/-- The per-newform analytic certificate consumed by the SMO chain: an explicit
pole point `s₀`, the character non-trivialities `χ̃ ≠ 1` and `χ̃² ≠ 1`, the
Dirichlet zero `LFunction χ̃ (2 s₀ - k + 1) = 0`, the non-cancellation
`LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0`, and the analytic-continuation
universal-F clause. -/
def Newform.HasDirichletZeroCertificate
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) :
    Prop :=
  ∃ (s₀ : ℂ),
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
    (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1 ∧
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)
      (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
    ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
        F s = LSeries f.lCoeff_stripped s) →
      F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
        ((fun s ↦ DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)
          (2 * (2 * s - k + 1))) /
        (fun s ↦ DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))



/-- The analytic-continuation universal-F hypothesis for the simplified Dirichlet
quotient `LFunction χ̃² (2(2s-k+1)) / LFunction χ̃ (2s-k+1)` (no finite Euler-factor
corrections; the `T = ∅` specialisation of
`Newform.FullDirichletQuotientUniversalFClause`). -/
def Newform.DirichletQuotientUniversalFClause
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ) : Prop :=
  ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      F s = LSeries f.lCoeff_stripped s) →
    F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
      ((fun s ↦ DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)
        (2 * (2 * s - k + 1))) /
      (fun s ↦ DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))



/-- The analytic-continuation universal-F hypothesis matching the full T111
Dirichlet quotient, including the finite Euler-factor correction products over the
exceptional set `S` and its primes `T` coprime to `N`. -/
def Newform.FullDirichletQuotientUniversalFClause
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ) : Prop :=
  ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      F s = LSeries f.lCoeff_stripped s) →
    F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
      ((fun s ↦
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) /
      (fun s ↦
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          (2 * s - k + 1) *
        ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹))






/-- The full-clause analogue of
`Newform.dirichletQuotient_pole_witness_of_dirichletZero`, consuming the full
T111 quotient (with finite Euler-factor correction products) plus explicit
analyticity / nonzero / zero / finite-order hypotheses at `s₀`. -/
theorem Newform.dirichletQuotient_pole_witness_of_dirichletZero_full
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_num_an : AnalyticAt ℂ
      (fun s ↦
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_an : AnalyticAt ℂ
      (fun s ↦
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          (2 * s - k + 1) *
        ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀)
    (h_num_ne_zero :
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
      (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹) ≠ 0)
    (h_den_zero :
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s₀ - k + 1) *
      (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹) = 0)
    (h_den_finite :
      meromorphicOrderAt
        (fun s ↦
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤)
    (h_full_clause : Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    ∃ (num den : ℂ → ℂ) (s₀' : ℂ),
      MeromorphicAt num s₀' ∧
      MeromorphicAt den s₀' ∧
      meromorphicOrderAt num s₀' ≠ ⊤ ∧
      meromorphicOrderAt den s₀' ≠ ⊤ ∧
      meromorphicOrderAt num s₀' < meromorphicOrderAt den s₀' ∧
      ∀ F : ℂ → ℂ, Differentiable ℂ F →
        (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
          F s = LSeries f.lCoeff_stripped s) →
        F =ᶠ[nhdsWithin s₀' {s₀'}ᶜ] (num / den) := by
  set num : ℂ → ℂ := fun s ↦
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
    ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹
  set den : ℂ → ℂ := fun s ↦
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) *
    ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹
  exact ⟨num, den, s₀, h_num_an.meromorphicAt, h_den_an.meromorphicAt,
    meromorphicOrderAt_ne_top_of_analyticAt_ne_zero h_num_an h_num_ne_zero, h_den_finite,
    meromorphicOrderAt_lt_of_ne_zero_of_zero h_num_an h_den_an h_num_ne_zero h_den_zero
      h_den_finite, h_full_clause⟩

/-- Per-newform classical inputs to the full-quotient FrickeTwist consumer
chain, packaged as a single named structure with explicit fields.

This `_pre` variant lives in `FrickeTwist.lean` so that the FrickeTwist consumers
of the full-quotient ∃-clause shape can accept the bundled form without
upward-importing `MellinBridges.lean`. The canonical
`Newform.PerNewformFullDirichletData` (in `MellinBridges.lean`) is field-by-field
identical and converts via
`Newform.PerNewformFullDirichletData.ofPre`. -/
@[ext]
structure Newform.PerNewformFullDirichletData_pre
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
    (fun s ↦
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
      ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀
  /-- Analyticity of the full T111 denominator at `s₀`. -/
  h_den_an : AnalyticAt ℂ
    (fun s ↦
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s - k + 1) *
      ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀
  /-- Finite analytic order of full T111 denominator at `s₀`. -/
  h_den_finite : meromorphicOrderAt
    (fun s ↦
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s - k + 1) *
      ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤
  /-- Universal-F clause from T111 + extension uniqueness. -/
  h_clause : Newform.FullDirichletQuotientUniversalFClause f χ S T s₀

/-- The full-quotient analogue of
`Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate`: per-newform
full T111 numerator/denominator data plus the full universal-F clause imply
`Newform.NoEntireExtensionUnderBadPrime`.

Takes the bundled `Newform.PerNewformFullDirichletData_pre`; downstream callers
holding the canonical `Newform.PerNewformFullDirichletData` can supply
`D.toPre` (defined in `MellinBridges.lean`). -/
theorem Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData_pre f χ S) :
    Newform.NoEntireExtensionUnderBadPrime := by
  apply Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole
  intro N _ k f χ hfχ S h_bad
  let D := h_data f χ hfχ S h_bad
  exact Newform.dirichletQuotient_pole_witness_of_dirichletZero_full f χ S D.T D.s₀
    D.h_num_an D.h_den_an
    (mul_ne_zero D.h_num_LF_ne <| Finset.prod_ne_zero_iff.mpr fun p hp ↦
      mul_ne_zero (D.h_factors_ne p hp).1 (inv_ne_zero (D.h_factors_ne p hp).2))
    (by rw [D.h_zero, zero_mul]) D.h_den_finite D.h_clause

/-- **Direct full-quotient bridge to `Newform.AnalyticContradiction` (T132 step).**

Composes the full T111 chain into a direct
`HeckeEntireExtension + full-data ⇒ AnalyticContradiction` consumer,
sparing callers the intermediate `NoEntireExtensionUnderBadPrime` step.

Takes the bundled `Newform.PerNewformFullDirichletData_pre`; downstream callers
holding the canonical `Newform.PerNewformFullDirichletData` can supply
`D.toPre` (defined in `MellinBridges.lean`). -/
theorem Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (h_hecke : Newform.HeckeEntireExtension)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData_pre f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    h_hecke (Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate h_data)

/-- The `Newform.HeckeFEData` analogue of
`Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`,
taking a per-newform `Newform.HeckeFEData` instead of the global
`HeckeEntireExtension` Prop.

Takes the bundled `Newform.PerNewformFullDirichletData_pre`; downstream callers
holding the canonical `Newform.PerNewformFullDirichletData` can supply
`D.toPre` (defined in `MellinBridges.lean`). -/
theorem Newform.analyticContradiction_of_HeckeFEData_of_full_dirichletZeroCertificate
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData_pre f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_HeckeFEData h_FE) h_data


end HeckeRing.GL2
