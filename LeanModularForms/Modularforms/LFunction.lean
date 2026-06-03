/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.Modular
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Cusps

import LeanModularForms.Modularforms.ResToImagAxis

/-!
# L-functions of modular forms

For a weight-`k` modular form `f` with `q`-expansion `f(τ) = Σ_{n≥0} aₙ qⁿ`,
the **L-function** is the Dirichlet series `L(s, f) = Σ_{n ≥ 1} aₙ · n^{-s}`,
built on mathlib's `LSeries` / `LSeriesSummable` infrastructure.

## Main definitions

* `ModularForms.lCoeff f` — the `ℕ → ℂ` coefficient sequence built from the
  `q`-expansion of `f` at the strict width at `∞` of its level.
* `ModularForms.lSeries f` — the associated L-function `fun s ↦ LSeries (lCoeff f) s`.

## Main results

* `ModularForms.abscissaOfAbsConv_lCoeff_le` /
  `ModularForms.abscissaOfAbsConv_lCoeff_le_cuspForm` — Hecke's abscissa bounds
  `≤ k + 1` (modular forms) and `≤ k/2 + 1` (cusp forms).
* `ModularForms.lSeriesSummable_of_modularForm` /
  `ModularForms.lSeriesSummable_of_cuspForm` — absolute convergence on the
  corresponding half-planes.
* `ModularForms.lSeries_eq_iff_cuspForm` / `ModularForms.lSeries_eq_zero_iff_cuspForm`
  — LSeries injectivity and non-vanishing for cusp forms.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9.
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16.
-/

open Filter LSeries UpperHalfPlane
open scoped UpperHalfPlane

namespace ModularForms

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
variable {F : Type*} [FunLike F ℍ ℂ]

/-- The coefficient sequence `n ↦ (q-expansion of f).coeff n`, viewed as `ℕ → ℂ`,
the natural input to mathlib's `LSeries`. -/
noncomputable def lCoeff [ModularFormClass F Γ k] (f : F) : ℕ → ℂ :=
  fun n ↦ (ModularFormClass.qExpansion Γ.strictWidthInfty f).coeff n

/-- The **L-function** of a modular form,
`L(·, f) = Σ_{n≥1} (lCoeff f) n · n^{-·}`. -/
noncomputable def lSeries [ModularFormClass F Γ k] (f : F) : ℂ → ℂ :=
  LSeries (lCoeff f)

@[simp]
lemma lCoeff_apply [ModularFormClass F Γ k] (f : F) (n : ℕ) :
    lCoeff f n = (ModularFormClass.qExpansion Γ.strictWidthInfty f).coeff n := rfl

@[simp]
lemma lSeries_apply [ModularFormClass F Γ k] (f : F) (s : ℂ) :
    lSeries f s = LSeries (lCoeff f) s := rfl

/-- **Hecke's crude bound**: for a weight-`k` modular form (`0 ≤ k`) on an
arithmetic subgroup, the abscissa of absolute convergence of the associated
L-function is at most `k + 1`. -/
lemma abscissaOfAbsConv_lCoeff_le [Γ.IsArithmetic] [ModularFormClass F Γ k]
    (hk : 0 ≤ k) (f : F) :
    abscissaOfAbsConv (lCoeff f) ≤ ((k : ℝ) + 1 : ℝ) := by
  have h_bigO : (fun n : ℕ ↦ lCoeff f n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ (k : ℝ) := by
    simpa [lCoeff, Real.rpow_intCast]
      using ModularFormClass.qExpansion_isBigO hk f
  simpa using LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (f := lCoeff f)
    (x := (k : ℝ)) h_bigO

/-- **Hecke's bound for cusp forms**: for a weight-`k` cusp form on an
arithmetic subgroup, the abscissa of absolute convergence of the associated
L-function is at most `k/2 + 1`. -/
lemma abscissaOfAbsConv_lCoeff_le_cuspForm [Γ.IsArithmetic]
    [CuspFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (lCoeff f) ≤ ((k : ℝ) / 2 + 1 : ℝ) := by
  have h_bigO :
      (fun n : ℕ ↦ lCoeff f n) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
    simpa [lCoeff] using CuspFormClass.qExpansion_isBigO f
  simpa using LSeries.abscissaOfAbsConv_le_of_isBigO_rpow
    (f := lCoeff f) (x := ((k : ℝ) / 2)) h_bigO

/-- Convergence of `LSeries (lCoeff f) s` on the half-plane `Re s > k + 1` for
a weight-`k` modular form of non-negative weight. -/
lemma lSeriesSummable_of_modularForm [Γ.IsArithmetic] [ModularFormClass F Γ k]
    (hk : 0 ≤ k) (f : F) {s : ℂ} (hs : (k : ℝ) + 1 < s.re) :
    LSeriesSummable (lCoeff f) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((abscissaOfAbsConv_lCoeff_le hk f).trans_lt (by exact_mod_cast hs))

/-- Convergence of `LSeries (lCoeff f) s` on the half-plane `Re s > k/2 + 1` for
a weight-`k` cusp form.  This is the standard absolute-convergence region. -/
lemma lSeriesSummable_of_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (lCoeff f) s :=
  LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((abscissaOfAbsConv_lCoeff_le_cuspForm f).trans_lt (by exact_mod_cast hs))

/-- For a cusp form, the `0`-th `q`-expansion coefficient vanishes. -/
lemma lCoeff_zero_of_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) :
    lCoeff f 0 = 0 := by
  simp only [lCoeff,
    ModularFormClass.qExpansion_coeff_zero (F := F) (Γ := Γ) (k := k) (f := f)
      (Γ.strictWidthInfty_pos_iff.mpr Fact.out) Γ.strictWidthInfty_mem_strictPeriods,
    (CuspFormClass.zero_at_infty f).valueAtInfty_eq_zero]

/-- Finite abscissa of absolute convergence for a cusp form. -/
lemma abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm [Γ.IsArithmetic]
    [CuspFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (lCoeff f) < ⊤ :=
  lt_of_le_of_lt (abscissaOfAbsConv_lCoeff_le_cuspForm f) (EReal.coe_lt_top _)

/-- **LSeries injectivity for cusp forms.**  Two cusp forms have equal
L-functions iff their `q`-expansion coefficients agree at every `n ≠ 0`. -/
lemma lSeries_eq_iff_cuspForm [Γ.IsArithmetic]
    {F' : Type*} [FunLike F' ℍ ℂ]
    [CuspFormClass F Γ k] [CuspFormClass F' Γ k]
    (f : F) (g : F') :
    lSeries f = lSeries g ↔ ∀ n ≠ 0, lCoeff f n = lCoeff g n := by
  unfold lSeries
  exact LSeries_eq_iff_of_abscissaOfAbsConv_lt_top
    (abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm f)
    (abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm g)

/-- **LSeries non-vanishing for cusp forms.**  The L-function of a cusp form
is identically zero iff all its `q`-expansion coefficients vanish. -/
lemma lSeries_eq_zero_iff_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) :
    lSeries f = 0 ↔ lCoeff f = 0 := by
  unfold lSeries
  rw [LSeries_eq_zero_iff (lCoeff_zero_of_cuspForm f),
    or_iff_left (abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm f).ne]


open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **Strict width at infinity of the GL₂(ℝ) image of Γ₁(N) is `1`.** -/
@[simp]
lemma strictWidthInfty_Gamma1_mapGL (N : ℕ) :
    ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1 :=
  CongruenceSubgroup.strictWidthInfty_Gamma1 N

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **`ModularForms.lCoeff` on a `Γ₁(N)` form reduces to `qExpansion 1`.** -/
lemma lCoeff_Gamma1_mapGL_eq (N : ℕ)
    {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) (n : ℕ) :
    lCoeff f n = (ModularFormClass.qExpansion (1 : ℝ) f).coeff n := by
  rw [lCoeff_apply, strictWidthInfty_Gamma1_mapGL]

/-- **Formal local Euler factor identity.**  For complex `c, x` with
`‖c · x²‖ < 1`, the alternating-power series
`Σᵣ (if r % 2 = 0 then (-c)^(r/2) · x^r else 0)` sums to `(1 + c · x²)⁻¹`. -/
theorem tsum_alternating_pow_eq (c x : ℂ) (h : ‖c * x ^ 2‖ < 1) :
    ∑' (r : ℕ), (if r % 2 = 0 then ((-c) ^ (r / 2) * x ^ r) else 0) =
      (1 + c * x ^ 2)⁻¹ := by
  have h_neg : ‖(-c) * x ^ 2‖ < 1 := by
    rw [show (-c) * x ^ 2 = -(c * x ^ 2) by ring, norm_neg]; exact h
  have h_even_term : ∀ k : ℕ,
      (if (2 * k) % 2 = 0 then ((-c) ^ ((2 * k) / 2) * x ^ (2 * k)) else 0) =
        ((-c) * x ^ 2) ^ k := fun k ↦ by
    rw [if_pos (by omega : (2 * k) % 2 = 0), show (2 * k) / 2 = k by omega]; ring
  have h_odd_term : ∀ k : ℕ,
      (if (2 * k + 1) % 2 = 0 then
          ((-c) ^ ((2 * k + 1) / 2) * x ^ (2 * k + 1))
        else 0) = 0 := fun k ↦ if_neg (by omega)
  have h_summ_even : Summable fun k : ℕ ↦
      (if (2 * k) % 2 = 0 then ((-c) ^ ((2 * k) / 2) * x ^ (2 * k)) else 0) := by
    refine Summable.congr (summable_geometric_of_norm_lt_one h_neg) (fun k ↦ ?_)
    rw [h_even_term k]
  have h_summ_odd : Summable fun k : ℕ ↦
      (if (2 * k + 1) % 2 = 0 then
          ((-c) ^ ((2 * k + 1) / 2) * x ^ (2 * k + 1))
        else 0) := by
    refine Summable.congr summable_zero (fun k ↦ ?_); rw [h_odd_term k]
  have h_split :=
    tsum_even_add_odd
      (f := fun r ↦ if r % 2 = 0 then ((-c) ^ (r / 2) * x ^ r) else 0)
      h_summ_even h_summ_odd
  rw [tsum_congr h_even_term, tsum_congr h_odd_term, tsum_zero, add_zero,
    tsum_geometric_of_norm_lt_one h_neg] at h_split
  rw [← h_split, show (1 : ℂ) - (-c) * x ^ 2 = 1 + c * x ^ 2 by ring]

/-- **Modular form on the positive imaginary axis.**

Maps `t > 0` to `f` evaluated at `i · t ∈ ℍ`, and `t ≤ 0` to `0`. -/
noncomputable def imAxis [ModularFormClass F Γ k] (f : F) (t : ℝ) : ℂ :=
  if h : 0 < t then
    f ⟨Complex.I * (t : ℂ), by
      show 0 < (Complex.I * (t : ℂ)).im
      rw [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im]
      simpa using h⟩
  else 0

@[simp]
lemma imAxis_apply_of_pos [ModularFormClass F Γ k] (f : F) {t : ℝ} (ht : 0 < t) :
    imAxis f t = f ⟨Complex.I * (t : ℂ), by
      show 0 < (Complex.I * (t : ℂ)).im
      rw [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im]
      simpa using ht⟩ := by
  unfold imAxis; rw [dif_pos ht]


/-- **Continuity of `imAxis f` on `Ioi 0`.** -/
lemma continuousOn_imAxis [ModularFormClass F Γ k] (f : F) :
    ContinuousOn (imAxis f) (Set.Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  have h_pos : ∀ t : Set.Ioi (0 : ℝ),
      0 < (Complex.I * (((t : ℝ) : ℂ))).im := fun t ↦ by
    have ht : (0 : ℝ) < (t : ℝ) := t.prop
    show 0 < (Complex.I * ((t : ℝ) : ℂ)).im
    rw [Complex.mul_im, Complex.I_im, Complex.I_re,
      Complex.ofReal_re, Complex.ofReal_im]
    simpa using ht
  refine ((ModularFormClass.continuous f).comp ((continuous_const.mul
    (Complex.continuous_ofReal.comp continuous_subtype_val)).upperHalfPlaneMk
      h_pos)).congr (fun t ↦ ?_)
  exact (imAxis_apply_of_pos f t.prop).symm

/-- **Local integrability of `imAxis f` on `Ioi 0`.** -/
lemma locallyIntegrableOn_imAxis [ModularFormClass F Γ k] (f : F) :
    MeasureTheory.LocallyIntegrableOn (imAxis f) (Set.Ioi (0 : ℝ)) :=
  (continuousOn_imAxis f).locallyIntegrableOn measurableSet_Ioi

/-- **Rapid polynomial decay of `imAxis f` at infinity (named hypothesis):**
`∀ r : ℝ, (imAxis f x) =O[atTop] (x ^ r)`. -/
def HasImAxisRapidDecay [ModularFormClass F Γ k] (f : F) : Prop :=
  ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ imAxis f x - 0) (fun x : ℝ ↦ x ^ r)

/-- **Exponential decay of `imAxis f` at infinity (named hypothesis):**
`∃ a > 0, (imAxis f x) =O[atTop] (exp (-a * x))`. -/
def HasImAxisExponentialDecay [ModularFormClass F Γ k] (f : F) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ imAxis f x - 0) (fun x : ℝ ↦ Real.exp (-a * x))

/-- **Exponential decay implies rapid polynomial decay.** -/
theorem HasImAxisRapidDecay_of_HasImAxisExponentialDecay
    [ModularFormClass F Γ k] (f : F) (h : HasImAxisExponentialDecay f) :
    HasImAxisRapidDecay f := by
  obtain ⟨a, ha_pos, h_exp⟩ := h
  intro r
  exact h_exp.trans (isLittleO_exp_neg_mul_rpow_atTop ha_pos r).isBigO

/-- **`imAxis` agrees with `ResToImagAxis ⇑f`.** -/
lemma imAxis_eq_resToImagAxis [ModularFormClass F Γ k] (f : F) :
    imAxis f = ResToImagAxis (⇑f) := by
  funext t
  simp only [imAxis, ResToImagAxis]

/-- **`atImInfty` exponential decay ⇒ `HasImAxisExponentialDecay`.**

A bridge from the standard cusp-form decay statement
`f =O[atImInfty] (fun τ => exp (-c · τ.im))` to the imaginary-axis-side
`HasImAxisExponentialDecay f` predicate. -/
theorem hasImAxisExponentialDecay_of_atImInfty_decay [ModularFormClass F Γ k]
    (f : F) {c : ℝ} (hc : 0 < c)
    (hf : (⇑f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ ↦ Real.exp (-c * τ.im)) :
    HasImAxisExponentialDecay f := by
  refine ⟨c, hc, (Asymptotics.IsBigO.congr'
    (isBigO_resToImagAxis_of_isBigO_atImInfty hc hf) ?_ .rfl).mono le_rfl⟩
  refine .of_forall fun x ↦ ?_
  rw [imAxis_eq_resToImagAxis f]
  show ResToImagAxis (⇑f) x = ResToImagAxis (⇑f) x - 0
  ring

/-- **Cusp-form-side `HasImAxisExponentialDecay` from a strict period.**

Reduces `HasImAxisExponentialDecay f` to the strict-period hypothesis
`h ∈ Γ.strictPeriods` (with `0 < h`) via `CuspFormClass.exp_decay_atImInfty`. -/
theorem hasImAxisExponentialDecay_of_strictPeriod
    [CuspFormClass F Γ k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    HasImAxisExponentialDecay f := by
  haveI : Fact (IsCusp OnePoint.infty Γ) :=
    ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hc : (0 : ℝ) < 2 * Real.pi / h := by positivity
  refine hasImAxisExponentialDecay_of_atImInfty_decay f hc ?_
  refine (CuspFormClass.exp_decay_atImInfty f hh hΓ).congr_right fun τ ↦ ?_
  congr 1
  field_simp

/-- **The classical Hecke 1936 completed Mellin–Dirichlet identity for cusp forms**
(Diamond–Shurman §5.9 Theorem 5.9.2 / Miyake Theorem 4.3.5 / 4.5.16):
```
mellin (imAxis f) s = (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries (lCoeff f) s
```
on the convergence half-plane `Re s > k/2 + 1`. -/
def HasCompletedMellinIdentity [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) : Prop :=
  ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    mellin (imAxis f) s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries (lCoeff f) s

/-- **Termwise Mellin transform of `t ↦ exp(-(c·t))` for `c > 0`**:
```
mellin (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) s = (c : ℂ) ^ (-s) * Complex.Gamma s
```
on `Re s > 0`. -/
theorem mellin_realExp_neg_const_mul {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) s =
      (c : ℂ) ^ (-s) * Complex.Gamma s := by
  show mellin (fun t : ℝ ↦ (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) (c * t)) s = _
  rw [mellin_comp_mul_left (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) s hc,
    ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs, smul_eq_mul]

/-- **Identification of `Function.Periodic.qParam` on the imaginary axis with a real
exponential**:
```
Function.Periodic.qParam h (Complex.I * t) = (Real.exp (-(2 * π * t / h)) : ℂ).
``` -/
lemma qParam_imAxis_eq_realExp (h : ℝ) (t : ℝ) :
    Function.Periodic.qParam h (Complex.I * (t : ℂ)) =
      (Real.exp (-(2 * Real.pi * t / h)) : ℂ) := by
  unfold Function.Periodic.qParam
  rw [Complex.ofReal_exp]
  congr 1
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (t : ℂ)) =
        2 * (Real.pi : ℂ) * (Complex.I * Complex.I) * (t : ℂ) by ring,
      Complex.I_mul_I]
  push_cast
  ring

/-- **q-expansion termwise Mellin identity**.

For period `h > 0` and `m ≥ 1`,
```
mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * t) ^ m) s =
  (2 * π * m / h : ℂ) ^ (-s) * Complex.Gamma s
```
on `Re s > 0`. -/
theorem mellin_qParam_pow_imAxis {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 1 ≤ m)
    {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
      ((2 * Real.pi * m / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := by
  have h_eq :
      (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) =
        (fun t : ℝ ↦ (Real.exp (-(2 * Real.pi * m / h * t)) : ℂ)) := by
    funext t
    rw [qParam_imAxis_eq_realExp h t,
        show ((Real.exp (-(2 * Real.pi * t / h)) : ℝ) : ℂ) ^ m =
            (((Real.exp (-(2 * Real.pi * t / h)))^m : ℝ) : ℂ) by push_cast; rfl,
        show (Real.exp (-(2 * Real.pi * t / h)))^m =
            Real.exp (-(2 * Real.pi * m / h * t)) by
          rw [← Real.exp_nat_mul]; congr 1; ring]
  rw [h_eq, mellin_realExp_neg_const_mul (by
    have : (0 : ℝ) < m := by exact_mod_cast hm.trans_lt' Nat.zero_lt_one
    positivity) hs]

/-- **Factored q-expansion termwise Mellin identity**.

For period `h > 0` and `m ≥ 1`,
```
mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * t) ^ m) s =
  (2 * π / h : ℂ) ^ (-s) * Complex.Gamma s * (m : ℂ) ^ (-s)
```
on `Re s > 0`. -/
theorem mellin_qParam_pow_imAxis_split {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 1 ≤ m)
    {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
      ((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * ((m : ℕ) : ℂ) ^ (-s) := by
  rw [mellin_qParam_pow_imAxis hh hm hs,
      show ((2 * Real.pi * (m : ℕ) / h : ℝ) : ℂ) =
          ((2 * Real.pi / h : ℝ) : ℂ) * (((m : ℕ) : ℝ) : ℂ) by
        rw [← Complex.ofReal_mul]; push_cast; ring_nf,
      Complex.mul_cpow_ofReal_nonneg
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi / h)
        (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ)),
      Complex.ofReal_natCast]
  ring

/-- **Conditional sum-swap for the Mellin transform of a tsum**.

If a function `g : ℝ → ℂ` decomposes as a `tsum` of functions `fᵢ` a.e. on
`Ioi 0`, and if each weighted-by-`t^{s-1}` term is a.e. strongly measurable
on `Ioi 0` with overall finite L¹-norm sum, then the Mellin transform of
`g` equals the tsum of termwise Mellin transforms. -/
theorem mellin_eq_tsum_mellin_of_hasSum_of_integrable
    {ι : Type*} [Countable ι] (g : ℝ → ℂ) (f : ι → ℝ → ℂ) {s : ℂ}
    (h_decomp : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      HasSum (fun i ↦ f i t) (g t))
    (h_meas : ∀ i, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • f i t)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h_summ : (∑' i, MeasureTheory.lintegral
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (fun t : ℝ ↦ ‖(t : ℂ) ^ (s - 1) • f i t‖ₑ)) ≠ (⊤ : ENNReal)) :
    mellin g s = ∑' i, mellin (f i) s := by
  unfold mellin
  have h_ae_eq :
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • g t) =ᶠ[
          MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))]
        fun t : ℝ ↦ ∑' i, (t : ℂ) ^ (s - 1) • f i t := by
    filter_upwards [h_decomp] with t ht
    rw [(ht.const_smul ((t : ℂ) ^ (s - 1))).tsum_eq]
  rw [MeasureTheory.integral_congr_ae h_ae_eq,
      MeasureTheory.integral_tsum h_meas h_summ]

/-- **Scalar-pullout for Mellin (ℂ)**, the `*`-form of `mellin_const_smul`:
```
mellin (fun t : ℝ ↦ c * f t) s = c * mellin f s.
``` -/
lemma mellin_const_mul (f : ℝ → ℂ) (s : ℂ) (c : ℂ) :
    mellin (fun t : ℝ ↦ c * f t) s = c * mellin f s :=
  mellin_const_smul f s c

/-- **Algebraic normalization: termwise Mellin tsum = `(2π/h)^{-s} · Γ(s) · LSeries`**.

Given a coefficient sequence `a : ℕ → ℂ` with `a 0 = 0` (matching the cusp-form
constraint `lCoeff f 0 = 0`), the tsum of `a m · mellin (qParam^m) s` factors as
```
∑' m, a m · mellin (qParam h (I·t)^m) s
  = (2π/h)^(-s) · Γ(s) · LSeries a s
```
on `Re s > 0`. -/
theorem tsum_mellin_qParam_pow_imAxis_eq_LSeries
    {h : ℝ} (hh : 0 < h) (a : ℕ → ℂ) (h_a0 : a 0 = 0)
    {s : ℂ} (hs : 0 < s.re) :
    ∑' m : ℕ, a m * mellin (fun t : ℝ ↦
        Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
      ((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * LSeries a s := by
  have h_each : ∀ m : ℕ,
      a m * mellin (fun t : ℝ ↦
          Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
        (((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) * LSeries.term a s m := fun m ↦ by
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · rw [LSeries.term_zero, h_a0, zero_mul, mul_zero]
    · rw [mellin_qParam_pow_imAxis_split hh hm_pos hs, LSeries.term_def₀ h_a0]
      ring
  rw [tsum_congr h_each, tsum_mul_left]
  rfl

/-- **Conditional consumer theorem: q-expansion ⇒ completed L-series identity**.

Width-`h` conditional version of the classical Hecke 1936 Mellin–Dirichlet identity:
under the period-`h` q-expansion decomposition, measurability and summability
hypotheses, `mellin g s = (2π/h)^{-s} · Γ(s) · LSeries a s`. -/
theorem mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses
    {h : ℝ} (hh : 0 < h) {g : ℝ → ℂ} {a : ℕ → ℂ} (h_a0 : a 0 = 0) {s : ℂ}
    (hs : 0 < s.re)
    (h_decomp : ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      HasSum (fun m : ℕ ↦
        a m * Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) (g t))
    (h_meas : ∀ m, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h_summ : (∑' m : ℕ, MeasureTheory.lintegral
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (fun t : ℝ ↦ ‖(t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m)‖ₑ)) ≠
        (⊤ : ENNReal)) :
    mellin g s =
      ((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * LSeries a s := by
  rw [mellin_eq_tsum_mellin_of_hasSum_of_integrable
      g (fun m t ↦ a m * Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m)
      h_decomp h_meas h_summ]
  rw [show (fun m : ℕ ↦ mellin (fun t : ℝ ↦
        a m * Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s) =
      fun m : ℕ ↦ a m * mellin (fun t : ℝ ↦
        Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s from
      funext (fun m ↦
        mellin_const_mul (fun t : ℝ ↦
          Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s (a m))]
  exact tsum_mellin_qParam_pow_imAxis_eq_LSeries hh a h_a0 hs

/-- **Period-one corollary**.

Specialisation of `mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses` to
`h = 1`, matching the scalar `(2π)^{-s} · Γ(s)` in `HasCompletedMellinIdentity`.
-/
theorem mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses_one
    {g : ℝ → ℂ} {a : ℕ → ℂ} (h_a0 : a 0 = 0) {s : ℂ} (hs : 0 < s.re)
    (h_decomp : ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      HasSum (fun m : ℕ ↦
        a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m) (g t))
    (h_meas : ∀ m, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h_summ : (∑' m : ℕ, MeasureTheory.lintegral
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (fun t : ℝ ↦ ‖(t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ)) ≠
        (⊤ : ENNReal)) :
    mellin g s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries a s := by
  have h := mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses
    (h := 1) one_pos h_a0 hs h_decomp h_meas h_summ
  rwa [show ((2 * Real.pi / 1 : ℝ) : ℂ) = (2 * Real.pi : ℂ) by push_cast; ring] at h

/-- **Continuity on `Ioi 0` of the period-one weighted Mellin integrand**
`t ↦ (t : ℂ)^{s-1} • (a m · qParam 1 (I·t)^m)`. -/
lemma continuousOn_qParam_pow_imAxis_term {a : ℕ → ℂ} (m : ℕ) (s : ℂ) :
    ContinuousOn
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m))
      (Set.Ioi (0 : ℝ)) := by
  have h_cpow : ContinuousOn (fun t : ℝ ↦ ((t : ℝ) : ℂ) ^ (s - 1)) (Set.Ioi 0) :=
    (Complex.continuous_ofReal.continuousOn (s := Set.Ioi (0 : ℝ))).cpow_const
      fun _ ht ↦ Complex.ofReal_mem_slitPlane.mpr ht
  exact h_cpow.smul (by fun_prop)

/-- **AE strong measurability of the period-one weighted Mellin integrand**. -/
lemma aestronglyMeasurable_qParam_pow_imAxis_term {a : ℕ → ℂ} (m : ℕ) (s : ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  (continuousOn_qParam_pow_imAxis_term m s).aestronglyMeasurable measurableSet_Ioi

/-- **Predicate-level consumer: `HasCompletedMellinIdentity` from period-one
q-expansion swap hypotheses**.

Promotes `mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses_one` to the
`HasCompletedMellinIdentity` predicate level for a positive-weight cusp form. -/
theorem hasCompletedMellinIdentity_of_qExpansion_swap_hypotheses_one
    [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) (hk_pos : 0 < (k : ℝ))
    (h_decomp : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        HasSum (fun m : ℕ ↦
          lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)
          (imAxis f t))
    (h_meas : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      ∀ m, MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
          (lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m))
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h_summ : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      (∑' m : ℕ, MeasureTheory.lintegral
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun t : ℝ ↦ ‖(t : ℂ) ^ (s - 1) •
          (lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ)) ≠
          (⊤ : ENNReal)) :
    HasCompletedMellinIdentity f := by
  intro s hs
  have hs_re : 0 < s.re := by linarith [show (0 : ℝ) < (k : ℝ) / 2 + 1 by linarith]
  exact mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses_one
    (lCoeff_zero_of_cuspForm f) hs_re (h_decomp hs) (h_meas hs) (h_summ hs)


open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **Pointwise q-expansion decomposition of `imAxis f` for `(Gamma1 N).map (mapGL ℝ)`**.

For a modular form `f` on `(Gamma1 N).map (mapGL ℝ)` of weight `k` and any
`t > 0`, the imaginary-axis function `imAxis f t = f(it)` has the period-one
q-expansion
```
imAxis f t = ∑' m, lCoeff f m · qParam 1 (I·t)^m.
``` -/
theorem hasSum_qExpansion_imAxis_Gamma1_mapGL_of_pos
    {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ ↦
      lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)
      (imAxis f t) := by
  have h_im : 0 < (Complex.I * ((t : ℝ) : ℂ)).im := by
    rw [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im]
    simpa using ht
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [← strictWidthInfty_Gamma1_mapGL N]
    exact ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods
  rw [imAxis_apply_of_pos f ht]
  refine (ModularFormClass.hasSum_qExpansion (f := f) one_pos h1_period
    ⟨Complex.I * (t : ℂ), h_im⟩).congr_fun fun m ↦ ?_
  rw [smul_eq_mul, ← lCoeff_Gamma1_mapGL_eq N f]

open CongruenceSubgroup Matrix.SpecialLinearGroup in

/-- **Pointwise norm of the period-one Mellin integrand on `Ioi 0`**.

For any `t > 0`, complex `s`, coefficient `a : ℂ`, and `m : ℕ`,
```
‖(t : ℂ) ^ (s - 1) • (a * qParam 1 (I·t) ^ m)‖
  = t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t)).
``` -/
lemma norm_qParam_pow_imAxis_term (a : ℂ) (m : ℕ) (s : ℂ)
    {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • (a * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖
      = t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t)) := by
  rw [norm_smul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      show (s - 1).re = s.re - 1 by simp [Complex.sub_re, Complex.one_re],
      qParam_imAxis_eq_realExp,
      show ((Real.exp (-(2 * Real.pi * t / 1)) : ℝ) : ℂ) ^ m
          = (((Real.exp (-(2 * Real.pi * t / 1))) ^ m : ℝ) : ℂ) by push_cast; rfl,
      show ((Real.exp (-(2 * Real.pi * t / 1)))) ^ m
          = Real.exp (-(2 * Real.pi * m * t)) by
        rw [← Real.exp_nat_mul]; congr 1; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

/-- **Pointwise enorm of the period-one Mellin integrand on `Ioi 0`**, the
ENNReal-form of `norm_qParam_pow_imAxis_term`:
```
‖(t : ℂ) ^ (s - 1) • (a * qParam 1 (I·t) ^ m)‖ₑ
  = ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t))).
``` -/
lemma enorm_qParam_pow_imAxis_term_of_pos (a : ℂ) (m : ℕ) (s : ℂ)
    {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • (a * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ
      = ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t))) := by
  rw [← ofReal_norm_eq_enorm, norm_qParam_pow_imAxis_term a m s ht]

/-- **lintegral congruence for the period-one Mellin `h_summ` summand**.

For each `m : ℕ`, complex `s`, and `a : ℂ`, the `enorm`-lintegral of the
period-one weighted Mellin integrand on `Ioi 0` equals the `lintegral` of the
real expression
```
ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t))).
``` -/
lemma lintegral_enorm_qParam_pow_imAxis_term (a : ℂ) (m : ℕ) (s : ℂ) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) • (a * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ
      = ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t))) := by
  exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi fun _ ht ↦
    enorm_qParam_pow_imAxis_term_of_pos a m s ht

private lemma ofReal_rpow_mul_norm_mul_exp_ae_eq (a : ℂ) (m : ℕ) (s : ℂ) :
    ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ENNReal.ofReal
            (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * (m : ℝ) * t)))
          = ENNReal.ofReal ‖a‖ *
              ENNReal.ofReal
                (t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t))) := by
  filter_upwards with t
  rw [show t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * (m : ℝ) * t)) =
        ‖a‖ * (t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t))) by ring]
  exact ENNReal.ofReal_mul (norm_nonneg _)

/-- **One-term Gamma evaluation of the period-one Mellin `h_summ` summand**.

For `1 ≤ m` and `0 < s.re`,
```
∫⁻ t in Ioi 0, ENNReal.ofReal (t^(s.re-1) * ‖a‖ * Real.exp (-(2π m t)))
  = ENNReal.ofReal (‖a‖ * (2π m)^(-s.re) * Γ(s.re)).
``` -/
theorem lintegral_real_qExpansion_term_eq_Gamma {a : ℂ} {m : ℕ} (hm : 1 ≤ m)
    {s : ℂ} (hs : 0 < s.re) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t)))
      = ENNReal.ofReal
          (‖a‖ * (2 * Real.pi * m : ℝ) ^ (-s.re) * Real.Gamma s.re) := by
  have hb_pos : (0 : ℝ) < 2 * Real.pi * (m : ℝ) := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm.trans_lt' Nat.zero_lt_one
    positivity
  have hq : -1 < s.re - 1 := by linarith
  let f_mathlib : ℝ → ℝ := fun x : ℝ ↦
    x ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ)) * x ^ (1 : ℝ))
  have h_align : ∀ t : ℝ, 0 < t →
      f_mathlib t = t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t)) := fun t _ ↦ by
    show t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ)) * t ^ (1 : ℝ))
        = t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t))
    rw [Real.rpow_one]; ring_nf
  rw [MeasureTheory.lintegral_congr_ae (ofReal_rpow_mul_norm_mul_exp_ae_eq a m s),
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
        (fun t ht ↦ congrArg ENNReal.ofReal (h_align t ht).symm)]
  have h_nn : ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      0 ≤ f_mathlib t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1)
          (b := 2 * Real.pi * (m : ℝ)) hq le_rfl hb_pos) h_nn,
      integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s.re - 1)
        (b := 2 * Real.pi * (m : ℝ)) one_pos hq hb_pos,
      show -(s.re - 1 + 1) / 1 = -s.re by ring,
      show (s.re - 1 + 1) / 1 = s.re by ring,
      show (1 : ℝ) / 1 = 1 by norm_num, mul_one,
      ← ENNReal.ofReal_mul (norm_nonneg _)]
  congr 1; ring

end ModularForms

namespace LSeries


/-- **Hecke entire-continuation predicate.**  A coefficient sequence
`a : ℕ → ℂ` *has an entire extension* if there exists an entire
function `F : ℂ → ℂ` agreeing with `LSeries a` on the
absolute-convergence half-plane `abscissaOfAbsConv a < s.re`.

When it exists, the entire extension is unique on `ℂ`
(`HasEntireExtension.unique`). -/
def HasEntireExtension (a : ℕ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s

namespace HasEntireExtension

variable {a : ℕ → ℂ}

/-- **Uniqueness of entire extension.**  Two entire functions
`F, G : ℂ → ℂ` that both extend `LSeries a` on the absolute-
convergence half-plane are equal everywhere on `ℂ`. -/
theorem unique {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h_finite : abscissaOfAbsConv a < ⊤)
    (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s)
    (hGa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → G s = LSeries a s) :
    F = G := by
  obtain ⟨σ, hσ_abs, _⟩ := EReal.exists_between_coe_real h_finite
  let U : Set ℂ := {s : ℂ | (σ : ℝ) < s.re}
  have hU_sub : ∀ s ∈ U, abscissaOfAbsConv a < (s.re : EReal) := fun s hs ↦
    lt_of_lt_of_le hσ_abs (by exact_mod_cast (hs : (σ : ℝ) < s.re).le)
  obtain ⟨z₀, hz₀⟩ : U.Nonempty := ⟨((σ + 1 : ℝ) : ℂ), by
    show (σ : ℝ) < ((σ + 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith⟩
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG)
    (Filter.eventuallyEq_iff_exists_mem.mpr
      ⟨U, (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀,
        fun s hs ↦ (hFa (hU_sub s hs)).trans (hGa (hU_sub s hs)).symm⟩)


end HasEntireExtension

namespace HasMeromorphicExtensionWithPole

/-- **Quotient pole sufficient condition.**

If `num, den : 𝕜 → 𝕜` are meromorphic at `x`, both with finite
(`≠ ⊤`) order, and `meromorphicOrderAt num x < meromorphicOrderAt den x`,
then `fun s ↦ num s / den s` has **negative** meromorphic order at `x`
— i.e., the quotient has a pole at `x`. -/
theorem _root_.meromorphicOrderAt_div_neg_of_orderAt_lt
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {num den : 𝕜 → 𝕜} {x : 𝕜}
    (h_num : MeromorphicAt num x) (h_den : MeromorphicAt den x)
    (h_num_finite : meromorphicOrderAt num x ≠ ⊤)
    (h_den_finite : meromorphicOrderAt den x ≠ ⊤)
    (h_lt : meromorphicOrderAt num x < meromorphicOrderAt den x) :
    meromorphicOrderAt (num / den) x < 0 := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul h_num h_den.inv, meromorphicOrderAt_inv]
  lift meromorphicOrderAt num x to ℤ using h_num_finite with n hn
  lift meromorphicOrderAt den x to ℤ using h_den_finite with m hm
  rw [WithTop.coe_lt_coe] at h_lt
  rw [show -((m : ℤ) : WithTop ℤ) = (((-m) : ℤ) : WithTop ℤ) from rfl,
      ← WithTop.coe_add, show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl,
      WithTop.coe_lt_coe]
  lia

end HasMeromorphicExtensionWithPole

/-- **Meromorphic extension with a pole — analytic obligation Prop.**

A coefficient sequence `a : ℕ → ℂ` *has a meromorphic extension with a pole*
if there exist a witness function `g : ℂ → ℂ` and a witness pole point
`s₀ : ℂ` such that:

* `g` is meromorphic at `s₀`;
* `g` has *negative* meromorphic order at `s₀` (a pole);
* every entire extension `F : ℂ → ℂ` of `LSeries a` coincides with
  `g` on a punctured neighbourhood of `s₀`. -/
def HasMeromorphicExtensionWithPole (a : ℕ → ℂ) : Prop :=
  ∃ (g : ℂ → ℂ) (s₀ : ℂ),
    MeromorphicAt g s₀ ∧
    meromorphicOrderAt g s₀ < 0 ∧
    ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s) →
      F =ᶠ[nhdsWithin s₀ {s₀}ᶜ] g

namespace HasMeromorphicExtensionWithPole

/-- **Bridge: meromorphic extension with a pole forbids entire extension.**

A coefficient sequence `a : ℕ → ℂ` cannot admit both an entire extension
and a meromorphic extension with a pole. -/
theorem not_hasEntireExtension {a : ℕ → ℂ}
    (h_pole : LSeries.HasMeromorphicExtensionWithPole a) :
    ¬ LSeries.HasEntireExtension a := by
  rintro ⟨F, hF_diff, hF_eq⟩
  obtain ⟨g, s₀, hg_mero, hg_order, h_punc⟩ := h_pole
  have h_F_order_nonneg : 0 ≤ meromorphicOrderAt F s₀ :=
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF_diff s₀
      (Set.mem_univ _)).meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_congr (h_punc F hF_diff @hF_eq)] at h_F_order_nonneg
  exact absurd h_F_order_nonneg (not_le.mpr hg_order)

end HasMeromorphicExtensionWithPole

/-- **Coprime-stripped coefficient sequence at a Finset of primes.**

The S-stripped version of `f : ℕ → ℂ`: zeroed at every positive
integer `n` divisible by some prime in `S`, equal to `f n` elsewhere. -/
def coprimeStrip (S : Finset Nat.Primes) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if ∀ p ∈ S, ¬ (p : ℕ) ∣ n then f n else 0

/-- **`coprimeStrip S f 1 = f 1`** (since no prime divides `1`). -/
@[simp]
lemma coprimeStrip_one (S : Finset Nat.Primes) (f : ℕ → ℂ) :
    coprimeStrip S f 1 = f 1 := by
  unfold coprimeStrip
  rw [if_pos (fun p _ h_dvd ↦ p.prop.one_lt.ne' (Nat.dvd_one.mp h_dvd))]


/-- **`coprimeStrip` value on a positive prime power at a prime in `S`**:
`coprimeStrip S f (p^e) = 0` for `p ∈ S` and `e ≥ 1`. -/
lemma coprimeStrip_prime_pow_at_S (S : Finset Nat.Primes) (f : ℕ → ℂ)
    {p : Nat.Primes} (hp : p ∈ S) {e : ℕ} (he : 1 ≤ e) :
    coprimeStrip S f ((p : ℕ) ^ e) = 0 := by
  unfold coprimeStrip
  rw [if_neg]
  push Not
  exact ⟨p, hp, dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp he)⟩

/-- **`coprimeStrip` value on a prime power at a prime not in `S`**:
`coprimeStrip S f (p^e) = f (p^e)` for `p ∉ S` and any `e : ℕ`. -/
lemma coprimeStrip_prime_pow_off_S (S : Finset Nat.Primes) (f : ℕ → ℂ)
    {p : Nat.Primes} (hp : p ∉ S) (e : ℕ) :
    coprimeStrip S f ((p : ℕ) ^ e) = f ((p : ℕ) ^ e) := by
  unfold coprimeStrip
  rw [if_pos]
  intro q hq h_dvd
  exact hp (Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp
    (q.prop.dvd_of_dvd_pow h_dvd)) ▸ hq)

/-- **Local Euler factor of the coprimeStrip sequence at a prime in `S`.**

If `f 1 = 1`, then for `p ∈ S` the local Euler factor of `coprimeStrip S f`
at `p` collapses to `1`. -/
lemma coprimeStrip_eulerFactor_at_S
    (S : Finset Nat.Primes) {f : ℕ → ℂ} (hf₁ : f 1 = 1)
    (s : ℂ) {p : Nat.Primes} (hp : p ∈ S) :
    ∑' e : ℕ, LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e) = 1 := by
  have h_term_zero : ∀ e : ℕ, 1 ≤ e →
      LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e) = 0 := fun e he ↦ by
    rw [LSeries.term_def, if_neg (pow_pos p.prop.pos e).ne',
      coprimeStrip_prime_pow_at_S S f hp he, zero_div]
  rw [tsum_eq_single 0 fun e he_ne_zero ↦
    h_term_zero e (Nat.one_le_iff_ne_zero.mpr he_ne_zero)]
  show LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ 0) = 1
  rw [pow_zero, LSeries.term_def, if_neg one_ne_zero, coprimeStrip_one S f, hf₁,
      Nat.cast_one, Complex.one_cpow, div_one]

/-- **Local Euler factor of the coprimeStrip sequence at a prime not in `S`**:
for `p ∉ S` it equals the local Euler factor of `f` at `p`. -/
lemma coprimeStrip_eulerFactor_off_S
    (S : Finset Nat.Primes) (f : ℕ → ℂ)
    (s : ℂ) {p : Nat.Primes} (hp : p ∉ S) :
    ∑' e : ℕ, LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e) =
      ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e) := by
  refine tsum_congr fun e ↦ ?_
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [coprimeStrip_one S f]
  · have h_pow_ne : ((p : ℕ) ^ e : ℕ) ≠ 0 := (pow_pos p.prop.pos e).ne'
    rw [LSeries.term_def, LSeries.term_def, if_neg h_pow_ne,
      if_neg h_pow_ne, coprimeStrip_prime_pow_off_S S f hp e]

/-- **Euler-stripping bridge from named `HasProd` Euler-product hypotheses.**

Under named Euler-product hypotheses for `f` and `coprimeStrip S f`,
```
LSeries f s = (∏ p ∈ S, ∑' e, LSeries.term f s (p^e)) · LSeries (coprimeStrip S f) s
``` -/
theorem eulerStripping_bridge_via_eulerProduct
    {f : ℕ → ℂ} {s : ℂ} (S : Finset Nat.Primes)
    (hf₁ : f 1 = 1)
    (hf_euler : HasProd
      (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e))
      (LSeries f s))
    (hg_euler : HasProd
      (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term (coprimeStrip S f) s
        ((p : ℕ) ^ e))
      (LSeries (coprimeStrip S f) s)) :
    LSeries f s = (∏ p ∈ S, ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e)) *
                    LSeries (coprimeStrip S f) s := by
  set φ_f : Nat.Primes → ℂ :=
    fun p ↦ ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e)
  set φ_g : Nat.Primes → ℂ :=
    fun p ↦ ∑' e : ℕ, LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e)
  have h_φ_g_eq : ∀ p : Nat.Primes,
      φ_g p = if p ∈ S then 1 else φ_f p := fun p ↦ by
    by_cases hp : p ∈ S
    · rw [if_pos hp]; exact coprimeStrip_eulerFactor_at_S S hf₁ s hp
    · rw [if_neg hp]; exact coprimeStrip_eulerFactor_off_S S f s hp
  set ψ : Nat.Primes → ℂ := fun p ↦ if p ∈ S then 1 else φ_f p
  set r : Nat.Primes → ℂ := fun p ↦ if p ∈ S then φ_f p else 1
  have h_r_HasProd : HasProd r (∏ p ∈ S, φ_f p) :=
    Finset.prod_congr rfl (fun p hp ↦ by
        show (if p ∈ S then φ_f p else 1) = φ_f p; rw [if_pos hp]) ▸
      hasProd_prod_of_ne_finset_one (s := S)
        fun p hp ↦ by show (if p ∈ S then φ_f p else 1) = 1; rw [if_neg hp]
  have h_mul : HasProd (fun p ↦ ψ p * r p)
      ((LSeries (coprimeStrip S f) s) * ∏ p ∈ S, φ_f p) :=
    (hg_euler.congr_fun fun p ↦ (h_φ_g_eq p).symm).mul h_r_HasProd
  have h_ψr_eq_φf : ∀ p : Nat.Primes, ψ p * r p = φ_f p := fun p ↦ by
    show (if p ∈ S then (1 : ℂ) else φ_f p) * (if p ∈ S then φ_f p else 1) = φ_f p
    by_cases hp : p ∈ S
    · rw [if_pos hp, if_pos hp, one_mul]
    · rw [if_neg hp, if_neg hp, mul_one]
  rw [hf_euler.unique (h_mul.congr_fun fun p ↦ (h_ψr_eq_φf p).symm)]; ring

/-- **Inverted Euler-stripping bridge: `coprimeStrip` LSeries factors as a
polynomial multiplier times the original LSeries.**

Under the Euler-product `HasProd` hypotheses for both `f` and `coprimeStrip S f`,
plus a representation of each local Euler factor of `f` at `p ∈ S` as `(poly p)⁻¹`
(with `poly p ≠ 0`):
```
LSeries (coprimeStrip S f) s = (∏ p ∈ S, poly p) * LSeries f s.
``` -/
theorem coprimeStrip_LSeries_eq_polynomial_mul_LSeries
    {f : ℕ → ℂ} {s : ℂ} (S : Finset Nat.Primes)
    (hf₁ : f 1 = 1)
    (hf_euler : HasProd
      (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e))
      (LSeries f s))
    (hg_euler : HasProd
      (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term (coprimeStrip S f) s
        ((p : ℕ) ^ e))
      (LSeries (coprimeStrip S f) s))
    (poly : Nat.Primes → ℂ)
    (h_poly_ne_zero : ∀ p ∈ S, poly p ≠ 0)
    (h_poly_inv : ∀ p ∈ S,
      ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e) = (poly p)⁻¹) :
    LSeries (coprimeStrip S f) s = (∏ p ∈ S, poly p) * LSeries f s := by
  have h_bridge := eulerStripping_bridge_via_eulerProduct S hf₁ hf_euler hg_euler
  rwa [Finset.prod_congr rfl h_poly_inv, Finset.prod_inv_distrib,
    eq_inv_mul_iff_mul_eq₀ (Finset.prod_ne_zero_iff.mpr h_poly_ne_zero), eq_comm] at h_bridge

/-- **Entirety of the explicit finite-Euler-factor polynomial multiplier.**

For any finite `Finset` of primes `S` and any `a : Nat.Primes → ℂ`, the function
```
s ↦ ∏ p ∈ S, (1 - a p * ((p : ℕ) : ℂ) ^ (-s))
```
is entire on `ℂ`. -/
theorem differentiable_eulerFactor_polynomial_finset
    (S : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    Differentiable ℂ (fun s : ℂ ↦
      ∏ p ∈ S, (1 - a p * ((p : ℕ) : ℂ) ^ (-s))) := by
  refine Differentiable.fun_finset_prod fun p _ ↦ ?_
  haveI : NeZero (((p : ℕ) : ℂ)) := ⟨by exact_mod_cast p.prop.pos.ne'⟩
  fun_prop

/-- **Euler-stripping multiplier as an entire function plus pointwise bridge.**

Assembles `coprimeStrip_LSeries_eq_polynomial_mul_LSeries` and
`differentiable_eulerFactor_polynomial_finset` into the explicit triple shape
```
∃ stripping : ℂ → ℂ,
  Differentiable ℂ stripping ∧
  ∀ ⦃s : ℂ⦄, H s →
    LSeries (coprimeStrip S f) s = stripping s * LSeries f s
```
where `H : ℂ → Prop` describes the half-plane on which all hypotheses hold. -/
theorem hasEulerStrippingMultiplier_of_eulerProduct
    (S : Finset Nat.Primes) (a : Nat.Primes → ℂ)
    (f : ℕ → ℂ) (H : ℂ → Prop)
    (hf₁ : f 1 = 1)
    (hf_euler : ∀ ⦃s : ℂ⦄, H s →
      HasProd
        (fun p : Nat.Primes ↦ ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e))
        (LSeries f s))
    (hg_euler : ∀ ⦃s : ℂ⦄, H s →
      HasProd
        (fun p : Nat.Primes ↦ ∑' e : ℕ,
          LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e))
        (LSeries (coprimeStrip S f) s))
    (h_local_inv : ∀ ⦃s : ℂ⦄, H s → ∀ p ∈ S,
      ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e) =
        (1 - a p * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
    (h_local_ne_zero : ∀ ⦃s : ℂ⦄, H s → ∀ p ∈ S,
      1 - a p * ((p : ℕ) : ℂ) ^ (-s) ≠ 0) :
    ∃ stripping : ℂ → ℂ,
      Differentiable ℂ stripping ∧
      ∀ ⦃s : ℂ⦄, H s →
        LSeries (coprimeStrip S f) s = stripping s * LSeries f s := by
  refine ⟨fun s ↦ ∏ p ∈ S, (1 - a p * ((p : ℕ) : ℂ) ^ (-s)),
    differentiable_eulerFactor_polynomial_finset S a, ?_⟩
  intro s hs
  exact coprimeStrip_LSeries_eq_polynomial_mul_LSeries S hf₁ (hf_euler hs)
    (hg_euler hs)
    (fun p ↦ 1 - a p * ((p : ℕ) : ℂ) ^ (-s))
    (h_local_ne_zero hs)
    (h_local_inv hs)

end LSeries
