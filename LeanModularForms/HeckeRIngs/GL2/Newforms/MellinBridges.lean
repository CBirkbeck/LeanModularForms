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
/-- Per-newform classical inputs needed by the FrickeTwist full-quotient consumer
chain, packaged as a single named structure with explicit fields. Field-by-field
identical to the import-cycle-avoiding `Newform.PerNewformFullDirichletData_pre`
in `FrickeTwist.lean`; converters in both directions are provided by `.ofPre`
and `.toPre` below. -/
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

/-- Convert `Newform.PerNewformFullDirichletData_pre` (defined in FrickeTwist for
import-cycle reasons) into the canonical `Newform.PerNewformFullDirichletData`.
The two structures are field-by-field identical. -/
@[simps]
noncomputable def Newform.PerNewformFullDirichletData.ofPre
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (D : Newform.PerNewformFullDirichletData_pre f χ S) :
    Newform.PerNewformFullDirichletData f χ S where
  T := D.T
  s₀ := D.s₀
  h_zero := D.h_zero
  h_num_LF_ne := D.h_num_LF_ne
  h_factors_ne := D.h_factors_ne
  h_num_an := D.h_num_an
  h_den_an := D.h_den_an
  h_den_finite := D.h_den_finite
  h_clause := D.h_clause

/-- Convert the canonical `Newform.PerNewformFullDirichletData` back into the
`_pre` form that FrickeTwist consumers accept. Field-by-field identical. -/
@[simps]
noncomputable def Newform.PerNewformFullDirichletData.toPre
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k} {χ : (ZMod N)ˣ →* ℂˣ}
    {S : Finset ℕ} (D : Newform.PerNewformFullDirichletData f χ S) :
    Newform.PerNewformFullDirichletData_pre f χ S where
  T := D.T
  s₀ := D.s₀
  h_zero := D.h_zero
  h_num_LF_ne := D.h_num_LF_ne
  h_factors_ne := D.h_factors_ne
  h_num_an := D.h_num_an
  h_den_an := D.h_den_an
  h_den_finite := D.h_den_finite
  h_clause := D.h_clause









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



/-- The classical Hecke 1936 identity
`mellin (Newform.imAxis f) s = (2π)^{-s} · Γ(s) · LSeries f.lCoeff s` on
`Re s > k/2 + 1`, specialising `ModularForms.HasCompletedMellinIdentity`. -/
def Newform.HasCompletedMellinIdentity {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Prop :=
  ModularForms.HasCompletedMellinIdentity f.toCuspForm


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




end HeckeRing.GL2
