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
# Newforms: Atkin-Lehner / Fricke twist as a structured hypothesis

The Atkin-Lehner / Fricke twist packaged as the structured hypothesis
`Newform.FrickeTwistData` and the downstream Dirichlet-quotient pole-witness
chain up to the per-newform full Dirichlet-zero data feeding Strong
Multiplicity One.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.

## Main definitions

* `Newform.FrickeTwistData`: bundled Atkin-Lehner / Fricke twist hypothesis.
* `Newform.NoEntireExtensionUnderBadPrime`: bad-prime-zero ⇒ no entire extension.
* `Newform.DirichletQuotientHasPoleUnderBadPrime`: per-newform Dirichlet pole witness.
* `Newform.HasDirichletZeroCertificate`: per-newform Dirichlet-zero certificate.
* `Newform.DirichletQuotientUniversalFClause`, `Newform.FullDirichletQuotientUniversalFClause`:
  analytic-continuation universal-`F` clauses (simplified / full T111 quotient).

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

/-- **Atkin-Lehner / Fricke twist data for a Newform.**

Bundle of the classical Atkin-Lehner / Fricke twist data needed to
discharge the `h_feq` (functional equation) and `h_bridge`
(Mellin–Dirichlet) fields of `Newform.ImAxisMellinData`. -/
@[ext]
structure Newform.FrickeTwistData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) where
  /-- Atkin-Lehner / Fricke image of `f` as a CuspForm on `Γ₁(N)`. -/
  twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- Root number (eigenvalue of the Atkin-Lehner involution). -/
  ε : ℂ
  /-- Cusp-form weight is positive (cast to ℝ from `(k : ℤ)`). -/
  hk_pos : 0 < (k : ℝ)
  /-- Root number is nonzero. -/
  hε_ne : ε ≠ 0
  /-- **Functional equation on the imaginary axis.**  The classical
  Atkin-Lehner FE relates `f(i/x)` and the twist evaluated on the
  imaginary axis modulo a root-number/weight scalar. -/
  h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
    (Newform.imAxis f) (1 / x) =
      (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • _root_.ModularForms.imAxis twist x
  /-- **Mellin–Dirichlet bridge.** -/
  h_bridge : ∀ {s : ℂ},
    LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s

/-- Build `Newform.ImAxisMellinData f` from the structured Atkin-Lehner /
Fricke twist hypothesis `Newform.FrickeTwistData f`. -/
noncomputable def Newform.ImAxisMellinData.ofFrickeTwistData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (data : Newform.FrickeTwistData f) :
    Newform.ImAxisMellinData f :=
  Newform.ImAxisMellinData.ofData_withTwist f data.twist data.ε
    data.hk_pos data.hε_ne data.h_feq data.h_bridge

private lemma imAxis_div_const_isBigO_rpow {N : ℕ} [NeZero N] {k : ℤ}
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {c : ℝ} (hc : 0 < c) (r : ℝ) :
    Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ _root_.ModularForms.imAxis twist (x / c) - 0)
      (fun x : ℝ ↦ x ^ r) := by
  refine (((_root_.ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay
    twist (Newform.cuspForm_Gamma1_hasImAxisExponentialDecay twist)) r).comp_tendsto
    (Filter.tendsto_id.atTop_div_const hc)).trans
    (Asymptotics.IsBigO.of_bound (c ^ (-r)) ?_)
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  simp only [Function.comp_apply, id_eq]
  have h_div_rpow : (t / c) ^ r = c ^ (-r) * t ^ r := by
    rw [Real.div_rpow ht.le hc.le, Real.rpow_neg hc.le, div_eq_mul_inv]; ring
  rw [h_div_rpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.rpow_pos_of_pos hc (-r))]

/-- Build `Newform.ImAxisMellinData f` from a CuspForm-valued twist whose
underlying function equals the Fricke slash
`⇑f.toCuspForm.toModularForm' ∣[k] frickeMatrix N`, the weight positivity,
and the Mellin–Dirichlet bridge. -/
noncomputable def Newform.ImAxisMellinData.ofSlashEq
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N)
    (hk_pos : 0 < (k : ℝ))
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s) :
    Newform.ImAxisMellinData f := by
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN_ne : (N : ℂ) ≠ 0 := mod_cast hN_pos.ne'
  let G : ℝ → ℂ := fun t ↦ _root_.ModularForms.imAxis twist (t / (N : ℝ))
  let ε : ℂ := (N : ℂ) ^ (1 - k) * Complex.I ^ k
  have hG_continuousOn : ContinuousOn G (Set.Ioi (0 : ℝ)) :=
    (_root_.ModularForms.continuousOn_imAxis twist).comp
      (Continuous.continuousOn (by fun_prop)) (fun t ht ↦ div_pos ht hN_pos)
  have h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      Newform.imAxis f (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x := by
    intro x hx
    have h_cast : ((x ^ (k : ℝ) : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ k := by
      rw [Real.rpow_intCast x k, Complex.ofReal_zpow]
    change Newform.imAxis f (1 / x) =
      (((N : ℂ) ^ (1 - k) * Complex.I ^ k) * ((x ^ (k : ℝ) : ℝ) : ℂ)) •
        _root_.ModularForms.imAxis twist (x / (N : ℝ))
    rw [Newform.imAxis_feq_of_slashEq f twist slash_eq hx, h_cast, smul_eq_mul]
  exact {
    G := G
    ε := ε
    hG_int := hG_continuousOn.locallyIntegrableOn measurableSet_Ioi
    hk_pos := hk_pos
    hε_ne := mul_ne_zero (zpow_ne_zero _ hN_ne) (zpow_ne_zero _ Complex.I_ne_zero)
    h_feq := h_feq
    hF_top := Newform.imAxis_rapidDecay f
    hG_top := imAxis_div_const_isBigO_rpow twist hN_pos
    h_bridge := h_bridge
  }

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

private lemma eq_of_eqOn_halfPlane {F G : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) (σ : ℝ) (h : ∀ s : ℂ, σ < s.re → F s = G s) :
    F = G := by
  have hz₀ : σ < ((σ + 1 : ℝ) : ℂ).re := by rw [Complex.ofReal_re]; linarith
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG)
    (((isOpen_lt continuous_const Complex.continuous_re).eventually_mem hz₀).mono
      (fun s hs ↦ h s hs))

private lemma LFunction_comp_affine_punctured_ne_zero {N : ℕ} [NeZero N]
    {ψ : DirichletCharacter ℂ N} (hψ : ψ ≠ 1) {k : ℤ} (s₀ : ℂ) :
    ∀ᶠ s in nhdsWithin s₀ {s₀}ᶜ,
      DirichletCharacter.LFunction ψ (2 * s - k + 1) ≠ 0 := by
  set g : ℂ → ℂ := fun s ↦ DirichletCharacter.LFunction ψ (2 * s - k + 1)
  have hg_diff : Differentiable ℂ g :=
    differentiable_LFunction_comp hψ (by fun_prop)
  have hg_an : AnalyticAt ℂ g s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg_diff s₀ (Set.mem_univ _)
  set s' : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ)
  have h_re : (1 : ℝ) < (2 * s' - (k : ℂ) + 1).re := by
    have : (2 * s' - (k : ℂ) + 1).re = 5 := by
      simp [s', Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.intCast_re, Complex.intCast_im]; ring
    rw [this]; norm_num
  refine hg_an.eventually_eq_zero_or_eventually_ne_zero.resolve_left (fun h_ev ↦ ?_)
  exact LFunction_dirichletLift_ne_zero_of_one_lt_re h_re
    (congrFun ((Complex.analyticOnNhd_univ_iff_differentiable.mpr hg_diff).eq_of_eventuallyEq
      (fun _ _ ↦ analyticAt_const) (h_ev.mono (fun _ h ↦ h))) s')

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
  have hg_an : ∀ s, AnalyticAt ℂ g s := fun s ↦
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hg s (Set.mem_univ _)
  refine Differentiable.fun_finset_prod (fun p _ ↦ ?_)
  have h_pow : Differentiable ℂ (fun s : ℂ ↦ ((p : ℕ) : ℂ) ^ (-(g s))) := fun s ↦
    (AnalyticAt.cpow analyticAt_const (hg_an s).neg
      (Complex.natCast_mem_slitPlane.mpr p.prop.pos.ne')).differentiableAt
  exact (differentiable_const _).sub (h_pow.const_mul _)

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

/-- Combines `Newform.HeckeEntireExtension` and the pointwise Dirichlet-zero
certificate family into Strong Multiplicity One. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate
    (h_hecke : Newform.HeckeEntireExtension)
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
                (2 * s - k + 1))))
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_analyticContradiction
    (Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
      h_hecke (Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate h_cert))
    f g χ hfχ hgχ S h

/-- Mirrors `strongMultiplicityOne_of_analyticContradiction` but takes the
uniqueness content as an explicit hypothesis `h_unique`, isolating the analytic
chain from the upstream `newform_unique`. -/
theorem strongMultiplicityOne_of_analyticContradiction_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_ana : Newform.AnalyticContradiction)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine h_unique f g χ hfχ hgχ ?_
  intro n hn
  by_cases hn_S : n.val ∈ S
  · have hn_pos : 0 < n.val := n.pos
    let bad : Finset ℕ := S ∪ S.image (· / n.val) ∪ n.val.primeFactors
    obtain ⟨q, hq_prime, hq_N, hq_notin, hq_ne⟩ :=
      Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
        h_ana f χ hfχ bad
    have hq_pos : 0 < q := hq_prime.pos
    have hq_notin_S : q ∉ S := fun hqS ↦ hq_notin <| by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inl hqS)
    have hq_notin_img : q ∉ S.image (· / n.val) := fun h' ↦ hq_notin <| by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inr h')
    have hq_nd_n : ¬ q ∣ n.val := fun hqn ↦ hq_notin <| by
      simp only [bad, Finset.mem_union, Nat.mem_primeFactors]
      exact Or.inr ⟨hq_prime, hqn, hn_pos.ne'⟩
    have hn_coprime_q : Nat.Coprime n.val q :=
      ((hq_prime.coprime_iff_not_dvd).mpr hq_nd_n).symm
    have hnq_notin_S : n.val * q ∉ S := fun hnqS ↦ hq_notin_img <| by
      refine Finset.mem_image.mpr ⟨n.val * q, hnqS, ?_⟩
      exact Nat.mul_div_cancel_left _ hn_pos
    let q_pnat : ℕ+ := ⟨q, hq_pos⟩
    let nq_pnat : ℕ+ := ⟨n.val * q, Nat.mul_pos hn_pos hq_pos⟩
    have hnq_eq : f.eigenvalue nq_pnat = g.eigenvalue nq_pnat :=
      h nq_pnat (hn.mul_left hq_N) hnq_notin_S
    have hmul_f : f.eigenvalue nq_pnat = f.eigenvalue n * f.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul f n q_pnat hn hq_N hn_coprime_q χ hfχ
    have hmul_g : g.eigenvalue nq_pnat = g.eigenvalue n * g.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul g n q_pnat hn hq_N hn_coprime_q χ hgχ
    have hcomb :
        f.eigenvalue n * f.eigenvalue q_pnat = g.eigenvalue n * f.eigenvalue q_pnat := by
      rw [← hmul_f, hnq_eq, hmul_g, h q_pnat hq_N hq_notin_S]
    exact mul_right_cancel₀ hq_ne hcomb
  · exact h n hn hn_S

/-- Combines `Newform.HeckeEntireExtension`, the pointwise Dirichlet-zero
certificate family, and the explicit `h_unique` hypothesis to produce Strong
Multiplicity One. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_hecke : Newform.HeckeEntireExtension)
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
                (2 * s - k + 1))))
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_analyticContradiction_of_newformUnique h_unique
    (Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
      h_hecke (Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate h_cert))
    f g χ hfχ hgχ S h

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

/-- `Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate` with the
per-newform certificate hypothesis written as `Newform.HasDirichletZeroCertificate`. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_HasDirichletZeroCertificate
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.HasDirichletZeroCertificate f χ) :
    Newform.NoEntireExtensionUnderBadPrime :=
  Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate h_cert

/-- `strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate_of_newformUnique`
with the per-newform certificate hypothesis written as
`Newform.HasDirichletZeroCertificate`. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_HasDirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_hecke : Newform.HeckeEntireExtension)
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.HasDirichletZeroCertificate f χ)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate_of_newformUnique
    h_unique h_hecke h_cert f g χ hfχ hgχ S h

/-- Build `Newform.HasDirichletZeroCertificate f χ` directly from the explicit
pole point, character non-trivialities, Dirichlet zero, non-cancellation, and
universal-F clause. -/
theorem Newform.HasDirichletZeroCertificate_of_dirichletZero
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
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)
          (2 * (2 * s - k + 1))) /
        (fun s ↦ DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))) :
    Newform.HasDirichletZeroCertificate f χ :=
  ⟨s₀, h_χ_ne_one, h_chi_sq_ne_one, h_den_zero, h_num_ne_zero, h_univ_F⟩

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

/-- `Newform.HasDirichletZeroCertificate_of_dirichletZero` taking the universal-F
clause via the named Prop `Newform.DirichletQuotientUniversalFClause f χ s₀`. -/
theorem Newform.HasDirichletZeroCertificate_of_dirichletZero_of_clause
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
    (h_clause : Newform.DirichletQuotientUniversalFClause f χ s₀) :
    Newform.HasDirichletZeroCertificate f χ :=
  Newform.HasDirichletZeroCertificate_of_dirichletZero f χ s₀
    h_χ_ne_one h_chi_sq_ne_one h_den_zero h_num_ne_zero h_clause

/-- `Newform.DirichletQuotientUniversalFClause` unfolds definitionally to the raw
`∀ F` analytic-continuation clause. -/
theorem Newform.DirichletQuotientUniversalFClause_iff
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ) :
    Newform.DirichletQuotientUniversalFClause f χ s₀ ↔
      ∀ F : ℂ → ℂ, Differentiable ℂ F →
        (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
          F s = LSeries f.lCoeff_stripped s) →
        F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
          ((fun s ↦ DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)
            (2 * (2 * s - k + 1))) /
          (fun s ↦ DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1))) :=
  Iff.rfl

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

/-- At `T = ∅` the finite Euler-factor products collapse to `1`, so the full
universal-F clause reduces to the simplified one. -/
theorem Newform.simplified_eq_full_DirichletQuotientUniversalFClause_T_empty
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (s₀ : ℂ) :
    Newform.FullDirichletQuotientUniversalFClause f χ S ∅ s₀ ↔
      Newform.DirichletQuotientUniversalFClause f χ s₀ := by
  unfold Newform.FullDirichletQuotientUniversalFClause
    Newform.DirichletQuotientUniversalFClause
  simp only [Finset.prod_empty, mul_one]

/-- Reduce `Newform.DirichletQuotientUniversalFClause f χ s₀` to a half-plane
multiplicative identity hypothesis `LSeries f.lCoeff_stripped s · LFunction χ̃
(2s-k+1) = LFunction χ̃² (2(2s-k+1))` valid above some abscissa `σ`. -/
theorem Newform.DirichletQuotientUniversalFClause_of_halfPlane_identity
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (σ : ℝ)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped < (σ : EReal))
    (h_halfPlane_id : ∀ s : ℂ, σ < s.re →
      LSeries f.lCoeff_stripped s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) =
        DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s - k + 1))) :
    Newform.DirichletQuotientUniversalFClause f χ s₀ := by
  intro F hF h_F_eq
  set num : ℂ → ℂ := fun s ↦ DirichletCharacter.LFunction
    (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
    (2 * (2 * s - k + 1))
  set den : ℂ → ℂ := fun s ↦ DirichletCharacter.LFunction
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)
  have h_F_den_eq_num : ∀ s : ℂ, F s * den s = num s :=
    congrFun (eq_of_eqOn_halfPlane
      (hF.mul (differentiable_LFunction_comp h_χ_ne_one (by fun_prop)))
      (differentiable_LFunction_comp h_chi_sq_ne_one (by fun_prop)) σ (fun s hs ↦ by
        rw [h_F_eq (lt_of_lt_of_le h_abscissa_lt (mod_cast hs.le))]
        exact h_halfPlane_id s hs))
  refine (LFunction_comp_affine_punctured_ne_zero (k := k) h_χ_ne_one s₀).mono
    (fun s h_den_s_ne ↦ ?_)
  change F s = num s / den s
  rw [eq_div_iff h_den_s_ne]
  exact h_F_den_eq_num s

/-- Discharge the half-plane identity of
`Newform.DirichletQuotientUniversalFClause_of_halfPlane_identity` from the
pointwise T111 theorem `Newform.lSeries_stripped_eq_dirichlet_quotient_value` at
`T = ∅`. -/
theorem Newform.DirichletQuotientUniversalFClause_of_T111_T_empty
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    (h_T_empty : ∀ p : Nat.Primes, ¬ ((p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N))
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped <
      (((k : ℝ) / 2 + 1 : ℝ) : EReal)) :
    Newform.DirichletQuotientUniversalFClause f χ s₀ := by
  refine Newform.DirichletQuotientUniversalFClause_of_halfPlane_identity f χ s₀
    h_χ_ne_one h_chi_sq_ne_one ((k : ℝ) / 2 + 1) h_abscissa_lt ?_
  intro s hs_re
  obtain ⟨hs', hs''⟩ := t111_re_conditions hs_re
  have h_T111 := f.lSeries_stripped_eq_dirichlet_quotient_value χ hfχ S h_bad
    hs_re hs' hs'' (fun q hq hqN _ ↦ t111_geom_bound χ hs_re hq hqN) ∅
    (fun p ↦ iff_of_false (Finset.notMem_empty p) (h_T_empty p))
    (fun q hq hqN _ ↦ t111_one_pm_ne χ hs_re hq hqN)
  simp only [Finset.prod_empty, mul_one] at h_T111
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs',
    DirichletCharacter.LFunction_eq_LSeries _ hs'']
  rwa [eq_div_iff (DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hs')] at h_T111

/-- Reduce `Newform.FullDirichletQuotientUniversalFClause f χ S T s₀` to a
half-plane multiplicative entire identity (inverses cleared by
cross-multiplication), the entirety of the Euler-factor product, and pointwise
non-vanishing of the linear factors at `s₀`. -/
theorem Newform.FullDirichletQuotientUniversalFClause_of_halfPlane_multIdentity
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (σ : ℝ)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped < (σ : EReal))
    (h_EFP_diff : Differentiable ℂ
      (fun s : ℂ ↦ ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p))
    (h_halfPlane_id : ∀ s : ℂ, σ < s.re →
      LSeries f.lCoeff_stripped s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) *
        (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) =
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))))
    (h_LinFP1_factor_ne_s₀ : ∀ p ∈ T,
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_LinFP2_factor_ne_s₀ : ∀ p ∈ T,
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) :
    Newform.FullDirichletQuotientUniversalFClause f χ S T s₀ := by
  intro F hF h_F_eq
  have h_LF_chi_diff : Differentiable ℂ (fun s : ℂ ↦
      DirichletCharacter.LFunction (Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * s - k + 1)) :=
    differentiable_LFunction_comp h_χ_ne_one (by fun_prop)
  have h_LF_chi_sq_diff : Differentiable ℂ (fun s : ℂ ↦
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1))) :=
    differentiable_LFunction_comp h_chi_sq_ne_one (by fun_prop)
  have h_LinFP1_diff := differentiable_prod_linearFactor
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) T (g := fun s ↦ 2 * s - k + 1) (by fun_prop)
  have h_LinFP2_diff := differentiable_prod_linearFactor
    (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N) T
    (g := fun s ↦ 2 * (2 * s - k + 1)) (by fun_prop)
  have h_global := eq_of_eqOn_halfPlane
    (F := fun s ↦ F s *
      DirichletCharacter.LFunction (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s - k + 1) *
      ∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))))
    (G := fun s ↦
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
      (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
      ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))))
    ((hF.mul h_LF_chi_diff).mul h_LinFP1_diff)
    ((h_LF_chi_sq_diff.mul h_EFP_diff).mul h_LinFP2_diff) σ (fun s hs ↦ by
      simp only [h_F_eq (lt_of_lt_of_le h_abscissa_lt (mod_cast hs.le))]
      exact h_halfPlane_id s hs)
  filter_upwards [prod_linearFactor_eventually_ne_zero
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) T (g := fun s ↦ 2 * s - k + 1)
      (by fun_prop) s₀ h_LinFP1_factor_ne_s₀,
    prod_linearFactor_eventually_ne_zero
      (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N) T
      (g := fun s ↦ 2 * (2 * s - k + 1)) (by fun_prop) s₀ h_LinFP2_factor_ne_s₀,
    LFunction_comp_affine_punctured_ne_zero (k := k) h_χ_ne_one s₀]
    with s h_LP1_ne h_LP2_ne h_LF_ne
  exact eq_div_prod_inv_of_mul_prod_eq (congrFun h_global s) h_LF_ne h_LP1_ne h_LP2_ne

/-- Discharge the half-plane identity of
`Newform.FullDirichletQuotientUniversalFClause_of_halfPlane_multIdentity` from the
pointwise T111 theorem `Newform.lSeries_stripped_value_identity`. -/
theorem Newform.FullDirichletQuotientUniversalFClause_of_T111
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
    (h_EFP_diff : Differentiable ℂ
      (fun s : ℂ ↦ ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p))
    (h_LinFP1_factor_ne_s₀ : ∀ p ∈ T,
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_LinFP2_factor_ne_s₀ : ∀ p ∈ T,
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) :
    Newform.FullDirichletQuotientUniversalFClause f χ S T s₀ := by
  refine Newform.FullDirichletQuotientUniversalFClause_of_halfPlane_multIdentity
    f χ S T s₀ h_χ_ne_one h_chi_sq_ne_one ((k : ℝ) / 2 + 1)
    h_abscissa_lt h_EFP_diff ?_ h_LinFP1_factor_ne_s₀ h_LinFP2_factor_ne_s₀
  intro s hs_re
  obtain ⟨hs', hs''⟩ := t111_re_conditions hs_re
  have h_T111_mult := f.lSeries_stripped_value_identity χ hfχ S h_bad
    hs_re hs' hs'' (fun q hq hqN _ ↦ t111_geom_bound χ hs_re hq hqN) T hT_iff
    (fun q hq hqN _ ↦ t111_one_pm_ne χ hs_re hq hqN)
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs',
    DirichletCharacter.LFunction_eq_LSeries _ hs'']
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Finset.prod_inv_distrib]
    at h_T111_mult
  exact mul_eq_mul_of_mul_inv_eq h_T111_mult
    (Finset.prod_ne_zero_iff.mpr fun p _ ↦ linearFactor_ne_zero_of_one_lt_re _ p.prop hs'')
    (Finset.prod_ne_zero_iff.mpr fun p _ ↦ linearFactor_ne_zero_of_one_lt_re _ p.prop hs')

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

/-- Per-newform classical inputs needed by
`Newform.full_pole_witness_data_of_dirichletZero`, packaged as a single named
structure with explicit fields. -/
@[ext]
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
`Newform.NoEntireExtensionUnderBadPrime`. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.NoEntireExtensionUnderBadPrime := by
  apply Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole
  intro N _ k f χ hfχ S h_bad
  set D := h_data f χ hfχ S h_bad
  refine Newform.dirichletQuotient_pole_witness_of_dirichletZero_full
    f χ S D.T D.s₀ D.h_num_an D.h_den_an ?_ ?_ D.h_den_finite D.h_clause
  · exact mul_ne_zero D.h_num_LF_ne <| Finset.prod_ne_zero_iff.mpr fun p hp ↦
      mul_ne_zero (D.h_factors_ne p hp).1 (inv_ne_zero (D.h_factors_ne p hp).2)
  · rw [D.h_zero, zero_mul]

/-- The full-quotient analogue of
`strongMultiplicityOne_of_HeckeEntireExtension_of_HasDirichletZeroCertificate_of_newformUnique`,
combining `h_unique`, `Newform.HeckeEntireExtension`, and the per-newform full
T111 data into Strong Multiplicity One for arbitrary exceptional sets `S`. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_hecke : Newform.HeckeEntireExtension)
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
      h_hecke (Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate h_data))
    f g χ hfχ hgχ S h

/-- **Direct full-quotient bridge to `Newform.AnalyticContradiction` (T132 step).**

Composes the full T111 chain into a direct
`HeckeEntireExtension + full-data ⇒ AnalyticContradiction` consumer,
sparing callers the intermediate `NoEntireExtensionUnderBadPrime` step. -/
theorem Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (h_hecke : Newform.HeckeEntireExtension)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    h_hecke (Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate h_data)

/-- **Direct full-quotient bridge to `exists_nonzero_prime_eigenvalue` (T132 step).**

Composes the full T111 chain through `AnalyticContradiction` into a direct
`HeckeEntireExtension + full-data ⇒ ∃ nonzero-prime-eigenvalue` consumer
for callers needing the prime-nonvanishing conclusion (rather than full SMO). -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (h_hecke : Newform.HeckeEntireExtension)
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
    (Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
      h_hecke h_data) f χ hfχ S

/-- The `Newform.HeckeFEData` analogue of
`Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`,
taking a per-newform `Newform.HeckeFEData` instead of the global
`HeckeEntireExtension` Prop. -/
theorem Newform.analyticContradiction_of_HeckeFEData_of_full_dirichletZeroCertificate
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.PerNewformFullDirichletData f χ S) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_HeckeFEData h_FE) h_data

/-- The `Newform.HeckeFEData` analogue of
`Newform.exists_nonzero_prime_eigenvalue_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`,
taking a per-newform `Newform.HeckeFEData` instead of the global
`HeckeEntireExtension` Prop. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_HeckeFEData_of_full_dirichletZeroCertificate
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
  Newform.exists_nonzero_prime_eigenvalue_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_HeckeFEData h_FE) h_data f χ hfχ S

/-- Reduce the per-newform `h_data` hypothesis of the full-quotient consumer
chain to a named cluster of Dirichlet-zero ingredients at one explicit pole point
`s₀`: the Dirichlet zero, the non-cancellation, local non-vanishing of the
correction factors, analyticity, finite order, and the full universal-F clause. -/
theorem Newform.full_pole_witness_data_of_dirichletZero
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_LF_ne : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_num_factors_ne : ∀ p ∈ T,
      Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
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
    ∃ (T' : Finset Nat.Primes) (s₀' : ℂ),
      AnalyticAt ℂ
        (fun s ↦
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
          ∏ p ∈ T', Newform.eulerFactor_stripped f χ S s p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀' ∧
      AnalyticAt ℂ
        (fun s ↦
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T', (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀' ∧
      (DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s₀' - k + 1)) *
        (∏ p ∈ T', Newform.eulerFactor_stripped f χ S s₀' p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s₀' - k + 1)))⁻¹)) ≠ 0 ∧
      (DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s₀' - k + 1) *
        (∏ p ∈ T', (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀' - k + 1))))⁻¹)) = 0 ∧
      meromorphicOrderAt
        (fun s ↦
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T', (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀' ≠ ⊤ ∧
      Newform.FullDirichletQuotientUniversalFClause f χ S T' s₀' := by
  refine ⟨T, s₀, h_num_an, h_den_an, ?_, ?_, h_den_finite, h_clause⟩
  · exact mul_ne_zero h_num_LF_ne <| Finset.prod_ne_zero_iff.mpr fun p hp ↦
      mul_ne_zero (h_num_factors_ne p hp).1 (inv_ne_zero (h_num_factors_ne p hp).2)
  · rw [h_zero, zero_mul]


end HeckeRing.GL2
