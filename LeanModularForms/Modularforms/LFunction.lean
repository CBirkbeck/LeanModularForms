/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.Modular
import LeanModularForms.Modularforms.ResToImagAxis

/-!
# L-functions of modular forms

For a weight-`k` modular form `f` with `q`-expansion `f(τ) = Σ_{n≥0} aₙ qⁿ`,
the **L-function** is the Dirichlet series

  `L(s, f) = Σ_{n ≥ 1} aₙ · n^{-s}`.

This file sets up the definition and basic convergence properties of `L(s, f)`,
building on mathlib's `LSeries` / `LSeriesSummable` infrastructure
(`Mathlib.NumberTheory.LSeries.Basic`).  The aim is to give a reusable
coefficient-sequence-level API that any later consumer — including the
normalised-eigenform / Newform theory — can specialise.

The file does **not** introduce any eigenform/newform/character-form
definitions.  A downstream normalised-eigenform predicate (to live in
Newforms.lean or a follow-up file) can apply mathlib's
`eulerProduct_hasProd` / `eulerProduct_completely_multiplicative_hasProd`
(`Mathlib.NumberTheory.EulerProduct.Basic`) directly to the `lCoeff`
sequence once multiplicativity and absolute summability are established.
This file only provides the `LSeries`-side machinery, so it does not
import `EulerProduct` itself.

## Main definitions

* `ModularForms.lCoeff f` — the `ℕ → ℂ` coefficient sequence built from the
  `q`-expansion of `f` at the strict width at `∞` of its level.  Agrees with
  `(ModularFormClass.qExpansion Γ.strictWidthInfty f).coeff n` for every `n`.
* `ModularForms.lSeries f` — the associated L-function,
  `fun s ↦ LSeries (lCoeff f) s`.

## Main results

* `ModularForms.abscissaOfAbsConv_lCoeff_le` — for any modular form of
  non-negative weight, `abscissaOfAbsConv (lCoeff f) ≤ k + 1`
  (Hecke's crude bound, via `ModularFormClass.qExpansion_isBigO`).
* `ModularForms.abscissaOfAbsConv_lCoeff_le_cuspForm` — the sharper bound
  `abscissaOfAbsConv (lCoeff f) ≤ k/2 + 1` for cusp forms, via
  `CuspFormClass.qExpansion_isBigO`.
* `ModularForms.lSeriesSummable_of_modularForm` /
  `ModularForms.lSeriesSummable_of_cuspForm` — absolute convergence of
  `LSeries (lCoeff f)` on the corresponding half-planes.
* `ModularForms.lCoeff_zero_of_cuspForm` — for a cusp form, the `0`-th
  coefficient vanishes (the hypothesis needed by `LSeries_eq_zero_iff` /
  `LSeries_injOn`).
* `ModularForms.lSeries_eq_iff_cuspForm` — two cusp forms have the same
  L-function iff their `q`-expansion coefficients agree at every `n ≠ 0`
  (the key injectivity tool for later uniqueness/non-vanishing arguments).
* `ModularForms.lSeries_eq_zero_iff_cuspForm` — specialisation of
  `LSeries_eq_zero_iff` to cusp-form coefficient sequences: the L-function
  vanishes identically iff every coefficient does.

## Euler product

Any multiplicative coefficient sequence `a : ℕ → ℂ` with `a 0 = 0`, `a 1 = 1`,
and `Summable (‖a ·‖)` admits an Euler product via mathlib's
`eulerProduct_hasProd` / `eulerProduct_completely_multiplicative_hasProd`.
A normalised Hecke eigenform's `lCoeff` satisfies all these hypotheses in
the region of absolute convergence given by `lSeriesSummable_of_cuspForm`,
but the **eigenform predicate itself is deliberately not defined here**;
Newforms.lean / a later file owns the eigenform API.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.9.
* [Miy] Miyake, *Modular Forms*, Thm 4.5.16.
-/

open Filter LSeries UpperHalfPlane
open scoped UpperHalfPlane

namespace ModularForms

variable {k : ℤ} {Γ : Subgroup (GL (Fin 2) ℝ)}
variable {F : Type*} [FunLike F ℍ ℂ]

/-! ### The coefficient sequence and L-function -/

/-- The coefficient sequence `n ↦ (q-expansion of f).coeff n`, viewed as `ℕ → ℂ`.

This is the natural input to mathlib's `LSeries`:
`LSeries (lCoeff f) s = Σ_{n≥1} aₙ n^{-s}`. -/
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

/-! ### Convergence abscissa -/

/-- **Hecke's crude bound**: for a weight-`k` modular form (`0 ≤ k`) on an
arithmetic subgroup, the abscissa of absolute convergence of the associated
L-function is at most `k + 1`.

The `0 ≤ k` hypothesis is exactly the one from
`ModularFormClass.qExpansion_isBigO`; the sharper bound `(k-1)/2 + ε` for
congruence levels is not proved here. -/
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
L-function is at most `k/2 + 1`.  This is the standard bound used throughout
modular-form theory; the sharper `(k-1)/2 + ε` requires the Ramanujan–Deligne
bound. -/
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
    LSeriesSummable (lCoeff f) s := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  refine lt_of_le_of_lt (abscissaOfAbsConv_lCoeff_le hk f) ?_
  exact_mod_cast hs

/-- Convergence of `LSeries (lCoeff f) s` on the half-plane `Re s > k/2 + 1` for
a weight-`k` cusp form.  This is the standard absolute-convergence region. -/
lemma lSeriesSummable_of_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable (lCoeff f) s := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  refine lt_of_le_of_lt (abscissaOfAbsConv_lCoeff_le_cuspForm f) ?_
  exact_mod_cast hs

/-! ### Cusp-form zeroth coefficient -/

/-- For a cusp form, the `0`-th `q`-expansion coefficient vanishes.  This is
the hypothesis required by `LSeries_eq_zero_iff` and `LSeries_injOn`. -/
lemma lCoeff_zero_of_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) :
    lCoeff f 0 = 0 := by
  have hh : 0 < Γ.strictWidthInfty := Γ.strictWidthInfty_pos_iff.mpr Fact.out
  have hΓ : Γ.strictWidthInfty ∈ Γ.strictPeriods :=
    Γ.strictWidthInfty_mem_strictPeriods
  have hcusp : IsZeroAtImInfty (⇑f) := CuspFormClass.zero_at_infty f
  simp only [lCoeff,
    ModularFormClass.qExpansion_coeff_zero (F := F) (Γ := Γ) (k := k) (f := f) hh hΓ,
    hcusp.valueAtInfty_eq_zero]

/-! ### Injectivity / non-vanishing on the cusp-form coefficient sequence -/

/-- Finite abscissa of absolute convergence for a cusp form.  Packages
`abscissaOfAbsConv_lCoeff_le_cuspForm` with `< ⊤`, as required by
`LSeries_eq_iff_of_abscissaOfAbsConv_lt_top` and `LSeries_eq_zero_iff`. -/
lemma abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm [Γ.IsArithmetic]
    [CuspFormClass F Γ k] (f : F) :
    abscissaOfAbsConv (lCoeff f) < ⊤ :=
  lt_of_le_of_lt (abscissaOfAbsConv_lCoeff_le_cuspForm f) (EReal.coe_lt_top _)

/-- **LSeries injectivity for cusp forms.**  Two cusp forms have equal
L-functions iff their `q`-expansion coefficients agree at every `n ≠ 0`.

This is the specialisation of mathlib's
`LSeries_eq_iff_of_abscissaOfAbsConv_lt_top` to cusp-form coefficient
sequences, using the finite abscissa bound
`abscissaOfAbsConv_lCoeff_le_cuspForm`. -/
lemma lSeries_eq_iff_cuspForm [Γ.IsArithmetic]
    {F' : Type*} [FunLike F' ℍ ℂ]
    [CuspFormClass F Γ k] [CuspFormClass F' Γ k]
    (f : F) (g : F') :
    lSeries f = lSeries g ↔ ∀ n ≠ 0, lCoeff f n = lCoeff g n := by
  have hf := abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm f
  have hg := abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm g
  unfold lSeries
  exact LSeries_eq_iff_of_abscissaOfAbsConv_lt_top hf hg

/-- **LSeries non-vanishing for cusp forms.**  The L-function of a cusp form
is identically zero iff all its `q`-expansion coefficients vanish. -/
lemma lSeries_eq_zero_iff_cuspForm [Γ.IsArithmetic] [CuspFormClass F Γ k]
    (f : F) :
    lSeries f = 0 ↔ lCoeff f = 0 := by
  have habs := abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm f
  unfold lSeries
  rw [LSeries_eq_zero_iff (lCoeff_zero_of_cuspForm f), or_iff_left habs.ne]

/-- Contrapositive form: a cusp form with some non-zero `q`-expansion
coefficient has a non-identically-zero L-function. -/
lemma lSeries_ne_zero_of_lCoeff_ne_zero [Γ.IsArithmetic] [CuspFormClass F Γ k]
    {f : F} (h : lCoeff f ≠ 0) :
    lSeries f ≠ 0 :=
  (lSeries_eq_zero_iff_cuspForm f).not.mpr h

/-! ### `Gamma1 N` bridge: strict width equals `1`

For a `Γ₁(N)` form the canonical period is `1` (not `N`), because
`ModularGroup.T ∈ Γ₁(N)` for every `N`.  This is mathlib's
`strictWidthInfty_Gamma1`; the following small wrapper phrases it in
terms of the `Γ = (Gamma1 N).map (mapGL ℝ)` shape used in the
`Eigenform`/`Newform` structures in
`LeanModularForms.HeckeRIngs.GL2.Newforms`.

Via `lCoeff_Gamma1_mapGL_eq` below, `ModularForms.lCoeff f.toCuspForm`
agrees with `Newform.lCoeff f` at every index. -/

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **Strict width at infinity of the GL₂(ℝ) image of Γ₁(N) is `1`.**

Immediate consequence of mathlib's `strictWidthInfty_Gamma1` plus the
definitional identification
`(Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ))`. -/
@[simp]
lemma strictWidthInfty_Gamma1_mapGL (N : ℕ) :
    ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1 := by
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl]
  exact CongruenceSubgroup.strictWidthInfty_Gamma1 N

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **`ModularForms.lCoeff` on a `Γ₁(N)` form reduces to `qExpansion 1`.**

Routes any cusp-form tool from this file through the canonical
period-`1` `q`-expansion when `Γ = (Gamma1 N).map (mapGL ℝ)`.  This is
the reusable consumer of `strictWidthInfty_Gamma1_mapGL`. -/
lemma lCoeff_Gamma1_mapGL_eq (N : ℕ)
    {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) (n : ℕ) :
    lCoeff f n = (ModularFormClass.qExpansion (1 : ℝ) f).coeff n := by
  rw [lCoeff_apply, strictWidthInfty_Gamma1_mapGL]

/-! ### Local Euler factor at a "bad-prime" Hecke eigenform

The local Euler factor at a prime `q` for a normalised Hecke eigenform
whose `q`-th Fourier coefficient vanishes collapses to a quadratic
reciprocal in `q^{-s}` (Diamond–Shurman §5.9 Case A, Miyake §4.5.16).
Concretely: combined with the closed-form
`coeff_prime_pow_eq_of_a_p_zero` in `Newforms.lean`, the abstract
identity below identifies the local Euler factor at `q` as
`(1 + χ(q) · q^{k-1-2s})⁻¹`, the inverse of `1 + c · x²` at
`(c, x) = (χ(q) · q^{k-1}, q^{-s})`.

This is the analytic half of the Dirichlet quotient identification: at
each "bad prime" (i.e. one where `a q = 0`), the local Euler factor is
a single rational expression in `q^{-s}`, suitable for assembling into
a global quotient of Dirichlet L-functions via `eulerProduct_hasProd`. -/

/-- **Formal local Euler factor identity.**  For complex `c, x` with
`‖c · x²‖ < 1`, the alternating-power series
`Σᵣ (if r % 2 = 0 then (-c)^(r/2) · x^r else 0)` (which is the local
Euler factor at a prime where the eigenform's linear coefficient
vanishes, after the prime-power closed form) sums to
`(1 + c · x²)⁻¹`.

Specialise via `c = (χ q : ℂ) · (q : ℂ)^(k-1)` and `x = (q : ℂ)^(-s)`
to obtain the local Dirichlet-quotient Euler factor at a "bad prime"
of a normalised eigenform.  We phrase the parity condition as
`r % 2 = 0` (rather than the equivalent `Even r`) for faster
elaboration; consumers using `Even` can convert via
`Nat.even_iff`. -/
theorem tsum_alternating_pow_eq (c x : ℂ) (h : ‖c * x ^ 2‖ < 1) :
    ∑' (r : ℕ), (if r % 2 = 0 then ((-c) ^ (r / 2) * x ^ r) else 0) =
      (1 + c * x ^ 2)⁻¹ := by
  have h_neg : ‖(-c) * x ^ 2‖ < 1 := by
    rw [show (-c) * x ^ 2 = -(c * x ^ 2) by ring, norm_neg]; exact h
  have h_summ_geom : Summable (fun k : ℕ ↦ ((-c) * x ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one h_neg
  have h_geom_sum : ∑' (k : ℕ), ((-c) * x ^ 2) ^ k = (1 - (-c) * x ^ 2)⁻¹ :=
    tsum_geometric_of_norm_lt_one h_neg
  have h_even_term : ∀ k : ℕ,
      (if (2 * k) % 2 = 0 then ((-c) ^ ((2 * k) / 2) * x ^ (2 * k)) else 0) =
        ((-c) * x ^ 2) ^ k := by
    intro k
    have h_mod : (2 * k) % 2 = 0 := by omega
    have h_div : (2 * k) / 2 = k := by omega
    rw [if_pos h_mod, h_div]; ring
  have h_odd_term : ∀ k : ℕ,
      (if (2 * k + 1) % 2 = 0 then
          ((-c) ^ ((2 * k + 1) / 2) * x ^ (2 * k + 1))
        else 0) = 0 := by
    intro k
    have h_mod : (2 * k + 1) % 2 ≠ 0 := by omega
    rw [if_neg h_mod]
  have h_summ_even : Summable fun k : ℕ ↦
      (if (2 * k) % 2 = 0 then ((-c) ^ ((2 * k) / 2) * x ^ (2 * k)) else 0) := by
    refine Summable.congr h_summ_geom (fun k ↦ ?_); rw [h_even_term k]
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
    h_geom_sum] at h_split
  rw [← h_split, show (1 : ℂ) - (-c) * x ^ 2 = 1 + c * x ^ 2 by ring]

/-! ### Imaginary-axis function `t ↦ f(it)` (Mellin-side API)

For a modular form `f` (or a cusp form via `CuspFormClass`), the
classical Mellin-side function in the Mellin-Dirichlet correspondence
(Diamond–Shurman §5.9, Miyake §4.3.5) is `t ↦ f(it)` for `t > 0`.  The
inputs to `Newform.MellinPairData.F` and friends require a function
`ℝ → ℂ`, so we lift via an `if`-extension by `0` outside `Ioi 0`.

The lift uses Mathlib's `UpperHalfPlane.mk` together with the
elementary positivity `(Complex.I * (t : ℂ)).im = t > 0`. -/

/-- **Modular form on the positive imaginary axis.**

Maps `t > 0` to `f` evaluated at `i · t ∈ ℍ`, and `t ≤ 0` to `0`.
This is the canonical Mellin-side function used in the cusp-form
Mellin–Dirichlet correspondence.  The dependent `if`-extension by `0`
outside `Ioi 0` allows the definition to live in `ℝ → ℂ`, the form
required by `Newform.MellinPairData.F`. -/
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

lemma imAxis_apply_of_nonpos [ModularFormClass F Γ k] (f : F) {t : ℝ}
    (ht : ¬ 0 < t) :
    imAxis f t = 0 := by
  unfold imAxis; rw [dif_neg ht]

/-- **Continuity of `imAxis f` on `Ioi 0`.**

`ModularForms.imAxis f` is continuous on the positive reals because

* `t ↦ Complex.I * (t : ℂ)` is continuous (`Complex.continuous_ofReal` +
  multiplication by a constant);
* on `Ioi 0`, the result has positive imaginary part, lifting via
  `Continuous.upperHalfPlaneMk` to a continuous map into `ℍ`;
* `f : ℍ → ℂ` is continuous (`ModularFormClass.continuous`).

The `if`-extension is harmless on `Ioi 0` since the positivity branch
is taken by definition. -/
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
  have h_complex_cts : Continuous
      (fun t : Set.Ioi (0 : ℝ) ↦ Complex.I * (((t : ℝ) : ℂ))) :=
    continuous_const.mul (Complex.continuous_ofReal.comp continuous_subtype_val)
  have h_lift_cts : Continuous (fun t : Set.Ioi (0 : ℝ) ↦
      UpperHalfPlane.mk (Complex.I * (((t : ℝ) : ℂ))) (h_pos t)) :=
    h_complex_cts.upperHalfPlaneMk h_pos
  have h_lifted_cts : Continuous (fun t : Set.Ioi (0 : ℝ) ↦
      f (UpperHalfPlane.mk (Complex.I * (((t : ℝ) : ℂ))) (h_pos t))) :=
    (ModularFormClass.continuous f).comp h_lift_cts
  refine h_lifted_cts.congr ?_
  intro t
  exact (imAxis_apply_of_pos f t.prop).symm

/-- **Local integrability of `imAxis f` on `Ioi 0`.**

Direct consequence of `continuousOn_imAxis`: a function continuous on
a measurable set is locally integrable on that set, with respect to
any locally finite measure (here the standard Lebesgue measure on `ℝ`).

This is the `Newform.MellinPairData.hF_int` field-level theorem, ready
for use with `F := ModularForms.imAxis f.toCuspForm.toModularForm'` (or
the equivalent for any `Γ`-arithmetic cusp form). -/
lemma locallyIntegrableOn_imAxis [ModularFormClass F Γ k] (f : F) :
    MeasureTheory.LocallyIntegrableOn (imAxis f) (Set.Ioi (0 : ℝ)) :=
  (continuousOn_imAxis f).locallyIntegrableOn measurableSet_Ioi

/-- **Rapid polynomial decay of `imAxis f` at infinity (named hypothesis).**

The classical cusp-form-decay statement
`∀ r : ℝ, (imAxis f x) =O[atTop] (x ^ r)`
captures the fact that `f(it) = O(t^(-N))` as `t → ∞` for every `N`,
following from the q-expansion `f(it) = ∑ aₙ e^{-2πnt/h}` and the
exponential decay of each term.

For cusp forms, this is the genuine analytic content of Hecke 1936
(Diamond–Shurman §5.9 / Miyake §4.3.5).  We expose it as a **named
predicate** on `ModularFormClass` so consumers can take it as an
explicit hypothesis without further qExpansion bookkeeping. -/
def HasImAxisRapidDecay [ModularFormClass F Γ k] (f : F) : Prop :=
  ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ imAxis f x - 0) (fun x : ℝ ↦ x ^ r)

/-- **Exponential decay of `imAxis f` at infinity (named hypothesis).**

The strictly-stronger cusp-form-decay statement
`∃ a > 0, (imAxis f x) =O[atTop] (exp (-a * x))`,
i.e., `imAxis f` decays at exponential rate at `t → ∞`.  Holds for any
holomorphic cusp form via the q-expansion `f(it) = ∑_{n≥1} aₙ e^{-2πnt/h}`,
where the leading-term decay rate is governed by `2π / h` (with `h`
the strict width at `∞`).

This is the natural and most-easily-formalisable cusp-form-decay
hypothesis (the bound at `n = 1`); rapid polynomial decay
(`HasImAxisRapidDecay`) follows from it via
`HasImAxisRapidDecay_of_HasImAxisExponentialDecay`. -/
def HasImAxisExponentialDecay [ModularFormClass F Γ k] (f : F) : Prop :=
  ∃ a : ℝ, 0 < a ∧ Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ imAxis f x - 0) (fun x : ℝ ↦ Real.exp (-a * x))

/-- **Exponential decay implies rapid polynomial decay.**

Reduces the cusp-form rapid-decay obligation
(`HasImAxisRapidDecay f`, the `hF_top`-shape statement) to the
strictly-stronger but more elementary **exponential decay**
(`HasImAxisExponentialDecay f`).

The proof transitively chains the hypothesis decay rate
`f =O[atTop] (exp (-a · x))` through the classical asymptotic
`exp (-a · x) =o[atTop] (x ^ r)` (Mathlib's
`isLittleO_exp_neg_mul_rpow_atTop`) for every real `r`, yielding the
rapid polynomial decay `f =O[atTop] (x ^ r)`.

The remaining analytic blocker is `HasImAxisExponentialDecay` itself
— the q-expansion-based exponential bound at the cusp `∞`. -/
theorem HasImAxisRapidDecay_of_HasImAxisExponentialDecay
    [ModularFormClass F Γ k] (f : F) (h : HasImAxisExponentialDecay f) :
    HasImAxisRapidDecay f := by
  obtain ⟨a, ha_pos, h_exp⟩ := h
  intro r
  exact h_exp.trans (isLittleO_exp_neg_mul_rpow_atTop ha_pos r).isBigO

/-- **`imAxis` agrees with `ResToImagAxis ⇑f`.**

The `ModularForms.imAxis` extension and the
`ResToImagAxis (⇑f)` from `LeanModularForms.Modularforms.ResToImagAxis`
have the same definitional shape (both `if 0 < t then f ⟨I·t, ...⟩ else 0`),
differing only by proof terms in the upper-half-plane lift.  By proof
irrelevance the values agree pointwise. -/
lemma imAxis_eq_resToImagAxis [ModularFormClass F Γ k] (f : F) :
    imAxis f = ResToImagAxis (⇑f) := by
  funext t
  by_cases ht : 0 < t
  · simp only [imAxis, ResToImagAxis, dif_pos ht]
  · simp only [imAxis, ResToImagAxis, dif_neg ht]

/-- **`atImInfty` exponential decay ⇒ `HasImAxisExponentialDecay`.**

A bridge from the standard cusp-form decay statement
`f =O[atImInfty] (fun τ => exp (-c · τ.im))` (the form in which Mathlib's
`CuspFormClass.exp_decay_atImInfty` is stated) to the imaginary-axis-side
`HasImAxisExponentialDecay f` predicate.

Internally chains
`isBigO_resToImagAxis_of_isBigO_atImInfty` from `ResToImagAxis.lean`,
then transports the conclusion to `imAxis f` via
`imAxis_eq_resToImagAxis`. -/
theorem hasImAxisExponentialDecay_of_atImInfty_decay [ModularFormClass F Γ k]
    (f : F) {c : ℝ} (hc : 0 < c)
    (hf : (⇑f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ => Real.exp (-c * τ.im)) :
    HasImAxisExponentialDecay f := by
  refine ⟨c, hc, ?_⟩
  have h_resToImagAxis :=
    isBigO_resToImagAxis_of_isBigO_atImInfty hc hf
  have h_eq : imAxis f = ResToImagAxis (⇑f) := imAxis_eq_resToImagAxis f
  refine (Asymptotics.IsBigO.congr' (h_resToImagAxis) ?_ ?_).mono le_rfl
  · refine Filter.Eventually.of_forall (fun x ↦ ?_)
    rw [h_eq]; show ResToImagAxis (⇑f) x = ResToImagAxis (⇑f) x - 0; ring
  · exact Filter.EventuallyEq.refl _ _

/-- **Cusp-form-side `HasImAxisExponentialDecay` from a strict period.**

Reduces `HasImAxisExponentialDecay f` to the **strict-period
hypothesis** `h ∈ Γ.strictPeriods` (with `0 < h`) via Mathlib's
`CuspFormClass.exp_decay_atImInfty`, which provides the standard
`f =O[atImInfty] (exp (-2π τ.im / h))` decay rate at rate `c = 2π / h`.

This is the substantive H1 reduction: for a `CuspFormClass`-typed `f`
on an arithmetic subgroup `Γ` with a known strict period (e.g.,
`(Gamma1 N).map (mapGL ℝ)` has strict period `1`), the rapid-decay
input to `Newform.MellinPairData.hF_top` is now mechanically derived. -/
theorem hasImAxisExponentialDecay_of_strictPeriod
    [CuspFormClass F Γ k] (f : F) {h : ℝ} (hh : 0 < h)
    (hΓ : h ∈ Γ.strictPeriods) :
    HasImAxisExponentialDecay f := by
  haveI : Fact (IsCusp OnePoint.infty Γ) :=
    ⟨Γ.isCusp_of_mem_strictPeriods hh hΓ⟩
  have hc : (0 : ℝ) < 2 * Real.pi / h := by positivity
  have h_decay : (⇑f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ ↦ Real.exp (-2 * Real.pi * τ.im / h) :=
    CuspFormClass.exp_decay_atImInfty f hh hΓ
  have h_decay' : (⇑f : ℍ → ℂ) =O[UpperHalfPlane.atImInfty]
      fun τ : ℍ ↦ Real.exp (-(2 * Real.pi / h) * τ.im) := by
    refine h_decay.congr_right (fun τ ↦ ?_)
    congr 1
    field_simp
  exact hasImAxisExponentialDecay_of_atImInfty_decay f hc h_decay'

/-! ### Completed Mellin–Dirichlet identity for cusp forms

The **classical Hecke 1936 Mellin–Dirichlet identity** for a weight-`k`
cusp form `f` with period-1 q-expansion `f(τ) = ∑_{n≥1} aₙ e^{2πi n τ}`:

```
∫₀^∞ f(it) · t^{s-1} dt = (2π)^{-s} · Γ(s) · ∑_{n≥1} aₙ / nˢ
```

on the convergence half-plane `Re s > k/2 + 1`.  In Mathlib's notation,
this reads
```
mellin (imAxis f) s = (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries (lCoeff f) s.
```

Diamond–Shurman §5.9 (Theorem 5.9.2); Miyake Theorem 4.3.5 / 4.5.16. -/

/-- **The classical Hecke 1936 completed Mellin–Dirichlet identity for cusp forms**
(Diamond–Shurman §5.9 Theorem 5.9.2 / Miyake Theorem 4.3.5 / 4.5.16):
```
mellin (imAxis f) s = (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries (lCoeff f) s
```
on the convergence half-plane `Re s > k/2 + 1`.

The Gamma factor `(2π)^{-s} · Γ(s)` is the standard "completion" linking
the Mellin integral to the Dirichlet L-series. -/
def HasCompletedMellinIdentity [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) : Prop :=
  ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
    mellin (imAxis f) s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries (lCoeff f) s

/-! ### Termwise Mellin transform of a single exponential q-term

The classical Hecke 1936 Mellin–Dirichlet identity (Diamond–Shurman §5.9 /
Miyake Theorem 4.5.16) is proved by substituting the q-expansion
`f(it) = ∑_{n≥1} aₙ exp(-(2π n t))` into `∫₀^∞ f(it) tˢ⁻¹ dt`, swapping the
sum and the integral via dominated convergence, and applying the
**termwise** Mellin identity
```
∫₀^∞ tˢ⁻¹ exp(-(c · t)) dt = c⁻ˢ · Γ(s)
```
to each term (with `c = 2π n`).  The latter is the `mellin_realExp_neg_const_mul`
lemma below: a direct corollary of `mellin_comp_mul_left` applied to
`Real.exp ∘ Neg.neg` plus `Complex.GammaIntegral_eq_mellin`. -/

/-- **Termwise Mellin transform of `t ↦ exp(-(c·t))` for `c > 0`**:
```
mellin (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) s = (c : ℂ) ^ (-s) * Complex.Gamma s
```
on `Re s > 0`.

Proof: `mellin_comp_mul_left` reduces this to `mellin (fun t ↦ (Real.exp (-t) : ℂ)) s`,
which equals `Complex.GammaIntegral s = Complex.Gamma s` by `GammaIntegral_eq_mellin`
and `Complex.Gamma_eq_integral`. -/
theorem mellin_realExp_neg_const_mul {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) s =
      (c : ℂ) ^ (-s) * Complex.Gamma s := by
  have h_fun_eq :
      (fun t : ℝ ↦ (Real.exp (-(c * t)) : ℂ)) =
        (fun t : ℝ ↦ (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) (c * t)) := by
    funext t; rfl
  rw [h_fun_eq, mellin_comp_mul_left (fun u : ℝ ↦ (Real.exp (-u) : ℂ)) s hc,
    ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs, smul_eq_mul]

/-- **Identification of `Function.Periodic.qParam` on the imaginary axis with a real
exponential**:
```
Function.Periodic.qParam h (Complex.I * t) = (Real.exp (-(2 * π * t / h)) : ℂ).
```
Used to convert q-expansion terms `qParam h (I·τ)^m` into exponential decay
factors `Real.exp(-(2π m t / h))` for the termwise Mellin computation.
-/
lemma qParam_imAxis_eq_realExp (h : ℝ) (t : ℝ) :
    Function.Periodic.qParam h (Complex.I * (t : ℂ)) =
      (Real.exp (-(2 * Real.pi * t / h)) : ℂ) := by
  unfold Function.Periodic.qParam
  rw [Complex.ofReal_exp]
  congr 1
  have h_I2 : (Complex.I : ℂ) * Complex.I = -1 := Complex.I_mul_I
  have rearrange :
      2 * (Real.pi : ℂ) * Complex.I * (Complex.I * (t : ℂ)) =
        2 * (Real.pi : ℂ) * (Complex.I * Complex.I) * (t : ℂ) := by ring
  rw [rearrange, h_I2]
  push_cast
  ring

/-- **q-expansion termwise Mellin identity**.

For period `h > 0` and `m ≥ 1`,
```
mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * t) ^ m) s =
  (2 * π * m / h : ℂ) ^ (-s) * Complex.Gamma s
```
on `Re s > 0`.

Combines `qParam_imAxis_eq_realExp` (q-expansion identification) with
`mellin_realExp_neg_const_mul` (the basic termwise Mellin lemma) at
`c = 2π m / h > 0`. -/
theorem mellin_qParam_pow_imAxis {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 1 ≤ m)
    {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
      ((2 * Real.pi * m / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s := by
  have h_eq :
      (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) =
        (fun t : ℝ ↦ (Real.exp (-(2 * Real.pi * m / h * t)) : ℂ)) := by
    funext t
    rw [qParam_imAxis_eq_realExp h t]
    rw [show ((Real.exp (-(2 * Real.pi * t / h)) : ℝ) : ℂ) ^ m =
            (((Real.exp (-(2 * Real.pi * t / h)))^m : ℝ) : ℂ) by push_cast; rfl]
    rw [show (Real.exp (-(2 * Real.pi * t / h)))^m =
            Real.exp (-(2 * Real.pi * m / h * t)) by
        rw [← Real.exp_nat_mul]; congr 1; ring]
  have hc_pos : 0 < 2 * Real.pi * m / h := by
    have hm_pos : (0 : ℝ) < m := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
    positivity
  rw [h_eq, mellin_realExp_neg_const_mul hc_pos hs]

/-- **Factored q-expansion termwise Mellin identity**.

For period `h > 0` and `m ≥ 1`,
```
mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * t) ^ m) s =
  (2 * π / h : ℂ) ^ (-s) * Complex.Gamma s * (m : ℂ) ^ (-s)
```
on `Re s > 0`.  This factors the basic termwise Mellin identity into the
"per-prime" form needed for the LSeries identification:
```
∑' m ≥ 1, aₘ · mellin (qParam^m) s = (2π/h)^{-s} · Γ(s) · ∑' m ≥ 1, aₘ · m^{-s}
```
-/
theorem mellin_qParam_pow_imAxis_split {h : ℝ} (hh : 0 < h) {m : ℕ} (hm : 1 ≤ m)
    {s : ℂ} (hs : 0 < s.re) :
    mellin (fun t : ℝ ↦ Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
      ((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * ((m : ℕ) : ℂ) ^ (-s) := by
  rw [mellin_qParam_pow_imAxis hh hm hs]
  have h_arg : (2 * Real.pi * (m : ℕ) / h : ℝ) = (2 * Real.pi / h : ℝ) * ((m : ℕ) : ℝ) := by
    ring
  have h_split : ((2 * Real.pi * (m : ℕ) / h : ℝ) : ℂ) ^ (-s) =
                 ((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * ((m : ℕ) : ℂ) ^ (-s) := by
    rw [show ((2 * Real.pi * (m : ℕ) / h : ℝ) : ℂ) =
          ((2 * Real.pi / h : ℝ) : ℂ) * (((m : ℕ) : ℝ) : ℂ) by
        rw [← Complex.ofReal_mul]; exact_mod_cast congrArg ((↑) : ℝ → ℂ) h_arg]
    rw [Complex.mul_cpow_ofReal_nonneg
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi / h)
        (by positivity : (0 : ℝ) ≤ ((m : ℕ) : ℝ))]
    rw [Complex.ofReal_natCast]
  rw [h_split]
  ring

/-! ### Conditional sum-swap for Mellin transform of a tsum

The classical Mellin–Dirichlet bridge proof requires interchanging the Mellin
integral with the q-expansion sum:
```
∫_{Ioi 0} t^{s-1} • (∑' i, fᵢ t) dt = ∑' i, ∫_{Ioi 0} t^{s-1} • fᵢ t dt
```
This is justified by `MeasureTheory.integral_tsum` under a uniform
integrability/summability hypothesis.  The lemma below packages this swap
at the `mellin` level under explicit, honest hypotheses. -/

/-- **Conditional sum-swap for the Mellin transform of a tsum**.

If a function `g : ℝ → ℂ` decomposes as a `tsum` of functions `fᵢ` a.e. on
`Ioi 0`, and if each weighted-by-`t^{s-1}` term is a.e. strongly measurable
on `Ioi 0` with overall finite L¹-norm sum, then the Mellin transform of
`g` equals the tsum of termwise Mellin transforms.

This is the key bridge identity that, together with `mellin_qParam_pow_imAxis_split`
and the LSeries algebraic identification, yields the classical Hecke 1936
completed Mellin–Dirichlet identity. -/
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

/-- **Scalar-pullout for Mellin (ℂ)**.

Specialisation of `mellin_const_smul` to `ℂ`:
```
mellin (fun t : ℝ ↦ c * f t) s = c * mellin f s.
```

Lemma `mellin_const_smul` (Mathlib `Mathlib.Analysis.MellinTransform:109`)
already proves the general scalar-multiplication case `c • f`; this wrapper
states it in `*` form for direct downstream use. -/
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
    ∑' m : ℕ, a m * mellin (fun t : ℝ =>
        Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
      ((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * LSeries a s := by
  have h_each : ∀ m : ℕ,
      a m * mellin (fun t : ℝ =>
          Function.Periodic.qParam h (Complex.I * (t : ℂ)) ^ m) s =
        (((2 * Real.pi / h : ℝ) : ℂ) ^ (-s) * Complex.Gamma s) * LSeries.term a s m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · rw [LSeries.term_zero, h_a0, zero_mul, mul_zero]
    · rw [mellin_qParam_pow_imAxis_split hh hm_pos hs, LSeries.term_def₀ h_a0]
      ring
  rw [tsum_congr h_each, tsum_mul_left]
  rfl

/-- **Conditional consumer theorem: q-expansion ⇒ completed L-series identity**.

Width-`h` conditional version of the classical Hecke 1936 Mellin–Dirichlet identity.
Given:

* `h > 0`: the period.
* `a : ℕ → ℂ` with `a 0 = 0` (matches the cusp-form constraint
  `lCoeff f 0 = 0` from `lCoeff_zero_of_cuspForm`).
* `0 < s.re`: the Mellin half-plane condition.
* **Decomposition** `h_decomp`: a.e. on `Ioi 0`, `g t = ∑' m, a m · qParam h (I·t)^m`
  (this is the q-expansion has-sum at `τ = I·t`, supplied by
  `ModularFormClass.hasSum_qExpansion` for cusp-form-side `a := lCoeff f`).
* **Measurability** `h_meas`: each weighted termwise integrand is a.e. strongly
  measurable on `Ioi 0` (automatic from continuity + `aestronglyMeasurable`).
* **Summability** `h_summ`: the sum of L¹-norms of the weighted termwise integrands
  is finite (the genuinely-classical bound; for cusp forms it follows from
  Hecke's polynomial bound `|aₘ| ≤ C · m^k` on the absolute-convergence
  half-plane `Re s > k/2 + 1`).

Conclusion:
```
mellin g s = (2π/h)^{-s} · Γ(s) · LSeries a s.
``` -/
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
      HasSum (fun m : ℕ =>
        a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m) (g t))
    (h_meas : ∀ m, MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ => (t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))))
    (h_summ : (∑' m : ℕ, MeasureTheory.lintegral
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
      (fun t : ℝ => ‖(t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ)) ≠
        (⊤ : ENNReal)) :
    mellin g s =
      (2 * Real.pi : ℂ) ^ (-s) * Complex.Gamma s * LSeries a s := by
  have h := mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses
    (h := 1) (by norm_num : (0 : ℝ) < 1) h_a0 hs h_decomp h_meas h_summ
  rw [show ((2 * Real.pi / 1 : ℝ) : ℂ) = (2 * Real.pi : ℂ) by push_cast; ring] at h
  exact h

/-! ### Measurability helper for the period-one Mellin consumer

The `h_meas` hypothesis of `mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses_one`
asks for AE strong measurability on `volume.restrict (Ioi 0)` of each weighted
termwise integrand
```
fun t : ℝ ↦ (t : ℂ) ^ (s - 1) • (a m * qParam 1 (I·t) ^ m).
```
The weighted termwise integrand is continuous on `Ioi 0`, hence AE strongly
measurable on `volume.restrict (Ioi 0)`. -/

/-- **Continuity on `Ioi 0` of the period-one weighted Mellin integrand**.

Per-`s`, per-`m`, per-`a` the function `t ↦ (t : ℂ)^{s-1} • (a m · qParam 1 (I·t)^m)`
is continuous on `Set.Ioi 0`. -/
lemma continuousOn_qParam_pow_imAxis_term {a : ℕ → ℂ} (m : ℕ) (s : ℂ) :
    ContinuousOn
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m))
      (Set.Ioi (0 : ℝ)) := by
  have h_cpow : ContinuousOn (fun t : ℝ ↦ ((t : ℝ) : ℂ) ^ (s - 1)) (Set.Ioi 0) := by
    apply (Complex.continuous_ofReal.continuousOn (s := Set.Ioi (0 : ℝ))).cpow_const
    intro t ht; rw [Complex.ofReal_mem_slitPlane]; exact ht
  have h_rest :
      Continuous (fun t : ℝ ↦
        a m * Function.Periodic.qParam 1 (Complex.I * ((t : ℝ) : ℂ)) ^ m) := by
    fun_prop
  exact h_cpow.smul h_rest.continuousOn

/-- **AE strong measurability of the period-one weighted Mellin integrand**.

Direct corollary of `continuousOn_qParam_pow_imAxis_term` plus
`ContinuousOn.aestronglyMeasurable` on the measurable open set `Set.Ioi 0`.
This packages the exact `h_meas` argument expected by
`mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses_one`. -/
lemma aestronglyMeasurable_qParam_pow_imAxis_term {a : ℕ → ℂ} (m : ℕ) (s : ℂ) :
    MeasureTheory.AEStronglyMeasurable
      (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) •
        (a m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m))
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
  (continuousOn_qParam_pow_imAxis_term m s).aestronglyMeasurable measurableSet_Ioi

/-- **Predicate-level consumer: `HasCompletedMellinIdentity` from period-one
q-expansion swap hypotheses**.

Promotes `mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses_one` to the
`HasCompletedMellinIdentity` predicate level: given a cusp form `f` of positive
weight together with the explicit a.e. period-one q-expansion decomposition of
`imAxis f` plus the per-`s` measurability/summability hypotheses required by
`mellin_eq_completedLSeries_of_qExpansion_swap_hypotheses_one`, conclude
`HasCompletedMellinIdentity f`.

`lCoeff_zero_of_cuspForm` discharges the `a 0 = 0` field automatically. -/
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

/-- **Predicate-level consumer: `HasCompletedMellinIdentity` from period-one
q-expansion decomposition + summability**.

Specialisation of `hasCompletedMellinIdentity_of_qExpansion_swap_hypotheses_one`
that **discharges** the per-`s` `h_meas` hypothesis automatically via
`aestronglyMeasurable_qParam_pow_imAxis_term`.  Future work only needs to
supply `h_decomp` (q-expansion decomposition of `imAxis f` from
`ModularFormClass.hasSum_qExpansion`) and `h_summ` (the genuinely-classical
Hecke L¹-norm-sum bound). -/
theorem hasCompletedMellinIdentity_of_qExpansion_decomp_and_summ_one
    [Γ.IsArithmetic] [CuspFormClass F Γ k] (f : F) (hk_pos : 0 < (k : ℝ))
    (h_decomp : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        HasSum (fun m : ℕ ↦
          lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)
          (imAxis f t))
    (h_summ : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      (∑' m : ℕ, MeasureTheory.lintegral
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun t : ℝ ↦ ‖(t : ℂ) ^ (s - 1) •
          (lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ)) ≠
          (⊤ : ENNReal)) :
    HasCompletedMellinIdentity f :=
  hasCompletedMellinIdentity_of_qExpansion_swap_hypotheses_one f hk_pos
    h_decomp
    (fun _ _ ↦ aestronglyMeasurable_qParam_pow_imAxis_term _ _)
    h_summ

/-! ### q-expansion decomposition of `imAxis` for `Γ₁(N)`-mapGL setting

The `h_decomp` hypothesis of
`hasCompletedMellinIdentity_of_qExpansion_decomp_and_summ_one` is the
period-one q-expansion decomposition of `imAxis f` on `Ioi 0`.  For the
`(Gamma1 N).map (mapGL ℝ)` setting (where `strictWidthInfty = 1`), this is a
direct corollary of `ModularFormClass.hasSum_qExpansion` evaluated at
`τ = ⟨I·t, _⟩`, plus `lCoeff_Gamma1_mapGL_eq` and `imAxis_apply_of_pos` to
reconcile `(qExpansion 1 f).coeff` with `lCoeff f` and `f τ` with `imAxis f t`. -/

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **Pointwise q-expansion decomposition of `imAxis f` for `(Gamma1 N).map (mapGL ℝ)`**.

For a modular form `f` on `(Gamma1 N).map (mapGL ℝ)` of weight `k` and any
`t > 0`, the imaginary-axis function `imAxis f t = f(it)` has the period-one
q-expansion
```
imAxis f t = ∑' m, lCoeff f m · qParam 1 (I·t)^m.
```
This is the direct application of `ModularFormClass.hasSum_qExpansion` at
`τ = ⟨I·t, …⟩`, period `h := 1` (using
`((Gamma1 N).map (mapGL ℝ)).strictWidthInfty = 1`), unfolded via
`lCoeff_Gamma1_mapGL_eq` and `imAxis_apply_of_pos`. -/
theorem hasSum_qExpansion_imAxis_Gamma1_mapGL_of_pos
    {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun m : ℕ =>
      lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)
      (imAxis f t) := by
  have h_im : 0 < (Complex.I * ((t : ℝ) : ℂ)).im := by
    rw [Complex.mul_im, Complex.I_im, Complex.I_re,
        Complex.ofReal_re, Complex.ofReal_im]
    simpa using ht
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [← strictWidthInfty_Gamma1_mapGL N]
    exact ((Gamma1 N).map (mapGL ℝ)).strictWidthInfty_mem_strictPeriods
  have h_qexp :=
    ModularFormClass.hasSum_qExpansion (f := f) one_pos h1_period
      ⟨Complex.I * (t : ℂ), h_im⟩
  have h_fun_eq :
      (fun m : ℕ ↦ (ModularFormClass.qExpansion 1 f).coeff m •
          Function.Periodic.qParam 1
            ((⟨Complex.I * (t : ℂ), h_im⟩ : ℍ) : ℂ) ^ m) =
        (fun m : ℕ ↦
          lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m) := by
    funext m
    rw [smul_eq_mul, ← lCoeff_Gamma1_mapGL_eq N f]
  rw [imAxis_apply_of_pos f ht]
  rw [h_fun_eq] at h_qexp
  exact h_qexp

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **a.e. q-expansion decomposition of `imAxis f` for `(Gamma1 N).map (mapGL ℝ)`**.

Direct AE wrapper of `hasSum_qExpansion_imAxis_Gamma1_mapGL_of_pos`: the
pointwise decomposition holds for **every** `t > 0`, and `volume.restrict
(Set.Ioi 0)` is supported on `Ioi 0`, so the a.e. version is automatic. -/
theorem hasSum_qExpansion_imAxis_Gamma1_mapGL_ae
    {N : ℕ} {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [ModularFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) :
    ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
      HasSum (fun m : ℕ ↦
        lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)
        (imAxis f t) := by
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards with t ht
  exact hasSum_qExpansion_imAxis_Gamma1_mapGL_of_pos f ht

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **`HasCompletedMellinIdentity` for `(Gamma1 N).map (mapGL ℝ)`-cusp forms,
modulo summability**.

Specialisation of `hasCompletedMellinIdentity_of_qExpansion_decomp_and_summ_one`
to `(Gamma1 N).map (mapGL ℝ)`-cusp forms, **discharging both** the `h_meas`
(via `aestronglyMeasurable_qParam_pow_imAxis_term`) and `h_decomp`
(via `hasSum_qExpansion_imAxis_Gamma1_mapGL_ae`) hypotheses automatically.

Only the **summability** hypothesis `h_summ` (the genuinely-classical Hecke
L¹-norm-sum bound for `Re s > k/2 + 1`) is left explicit; future work
discharges this from `CuspFormClass.qExpansion_isBigO`. -/
theorem hasCompletedMellinIdentity_of_qExpansion_summ_Gamma1_mapGL
    {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) (hk_pos : 0 < (k : ℝ))
    (h_summ : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      (∑' m : ℕ, MeasureTheory.lintegral
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))
        (fun t : ℝ ↦ ‖(t : ℂ) ^ (s - 1) •
          (lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ)) ≠
          (⊤ : ENNReal)) :
    HasCompletedMellinIdentity f :=
  hasCompletedMellinIdentity_of_qExpansion_decomp_and_summ_one f hk_pos
    (fun _ ↦ hasSum_qExpansion_imAxis_Gamma1_mapGL_ae f)
    h_summ

/-- **Pointwise norm of the period-one Mellin integrand on `Ioi 0`**.

For any `t > 0`, complex `s`, coefficient `a : ℂ`, and `m : ℕ`,
```
‖(t : ℂ) ^ (s - 1) • (a * qParam 1 (I·t) ^ m)‖
  = t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t)).
```

Combines `Complex.norm_cpow_eq_rpow_re_of_pos` and `qParam_imAxis_eq_realExp`
to express the integrand norm in real-valued form. -/
lemma norm_qParam_pow_imAxis_term (a : ℂ) (m : ℕ) (s : ℂ)
    {t : ℝ} (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • (a * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖
      = t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t)) := by
  rw [norm_smul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  rw [show (s - 1).re = s.re - 1 by simp [Complex.sub_re, Complex.one_re]]
  rw [qParam_imAxis_eq_realExp]
  rw [show ((Real.exp (-(2 * Real.pi * t / 1)) : ℝ) : ℂ) ^ m
        = (((Real.exp (-(2 * Real.pi * t / 1))) ^ m : ℝ) : ℂ) by push_cast; rfl]
  rw [show ((Real.exp (-(2 * Real.pi * t / 1)))) ^ m
        = Real.exp (-(2 * Real.pi * m * t)) by
      rw [← Real.exp_nat_mul]; congr 1; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  ring

/-- **Pointwise enorm of the period-one Mellin integrand on `Ioi 0`**.

ENNReal-form of `norm_qParam_pow_imAxis_term`: for any `t > 0`,
```
‖(t : ℂ) ^ (s - 1) • (a * qParam 1 (I·t) ^ m)‖ₑ
  = ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t))).
```

Reuses `norm_qParam_pow_imAxis_term` plus `ofReal_norm_eq_enorm`.  This is
the exact form needed to rewrite the lintegrand of the `h_summ` summand. -/
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
```
This is the per-term lintegral identity directly usable inside the `h_summ`
expression of `hasCompletedMellinIdentity_of_qExpansion_summ_Gamma1_mapGL`. -/
lemma lintegral_enorm_qParam_pow_imAxis_term (a : ℂ) (m : ℕ) (s : ℂ) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
      ‖(t : ℂ) ^ (s - 1) • (a * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ
      = ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t))) := by
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  exact enorm_qParam_pow_imAxis_term_of_pos a m s ht

/-- **One-term Gamma evaluation of the period-one Mellin `h_summ` summand**.

For `1 ≤ m` and `0 < s.re`,
```
∫⁻ t in Ioi 0, ENNReal.ofReal (t^(s.re-1) * ‖a‖ * Real.exp (-(2π m t)))
  = ENNReal.ofReal (‖a‖ * (2π m)^(-s.re) * Γ(s.re)).
```

Uses `integral_rpow_mul_exp_neg_mul_rpow` at `q = s.re - 1, b = 2πm`. -/
theorem lintegral_real_qExpansion_term_eq_Gamma {a : ℂ} {m : ℕ} (hm : 1 ≤ m)
    {s : ℂ} (hs : 0 < s.re) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * m * t)))
      = ENNReal.ofReal
          (‖a‖ * (2 * Real.pi * m : ℝ) ^ (-s.re) * Real.Gamma s.re) := by
  have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm
  have hb_pos : (0 : ℝ) < 2 * Real.pi * (m : ℝ) := by positivity
  have hq : -1 < s.re - 1 := by linarith
  have h_norm_nn : (0 : ℝ) ≤ ‖a‖ := norm_nonneg _
  let f_mathlib : ℝ → ℝ := fun x : ℝ ↦
    x ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ)) * x ^ (1 : ℝ))
  have h_align : ∀ t : ℝ, 0 < t →
      f_mathlib t = t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t)) := by
    intro t _ht
    show t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ)) * t ^ (1 : ℝ))
        = t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t))
    rw [Real.rpow_one]; ring_nf
  have h_ext :
      ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))),
        ENNReal.ofReal
            (t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * (m : ℝ) * t)))
          = ENNReal.ofReal ‖a‖ *
              ENNReal.ofReal
                (t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t))) := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with t _ht
    rw [show t ^ (s.re - 1) * ‖a‖ * Real.exp (-(2 * Real.pi * (m : ℝ) * t)) =
          ‖a‖ * (t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t))) by ring]
    exact ENNReal.ofReal_mul h_norm_nn
  rw [MeasureTheory.lintegral_congr_ae h_ext,
      MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h_lintegrand_eq :
      ∫⁻ t in Set.Ioi (0 : ℝ),
          ENNReal.ofReal
            (t ^ (s.re - 1) * Real.exp (-(2 * Real.pi * (m : ℝ) * t)))
        = ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_mathlib t) :=
    MeasureTheory.setLIntegral_congr_fun measurableSet_Ioi
      (fun t ht ↦ congrArg ENNReal.ofReal (h_align t ht).symm)
  rw [h_lintegrand_eq]
  have h_intble : MeasureTheory.IntegrableOn f_mathlib (Set.Ioi (0 : ℝ)) MeasureTheory.volume :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1)
      (b := 2 * Real.pi * (m : ℝ)) hq (le_refl 1) hb_pos
  have h_nn :
      ∀ᵐ (t : ℝ) ∂(MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))), 0 ≤ f_mathlib t := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    filter_upwards with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_intble h_nn]
  have h_int_eq :
      ∫ t in Set.Ioi (0 : ℝ), f_mathlib t =
        (2 * Real.pi * (m : ℝ)) ^ (-(s.re - 1 + 1) / 1) * (1 / 1) *
          Real.Gamma ((s.re - 1 + 1) / 1) :=
    integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := s.re - 1)
      (b := 2 * Real.pi * (m : ℝ)) (by norm_num : (0 : ℝ) < 1) hq hb_pos
  rw [h_int_eq, show -(s.re - 1 + 1) / 1 = -s.re by ring,
      show (s.re - 1 + 1) / 1 = s.re by ring,
      show (1 : ℝ) / 1 = 1 by norm_num, mul_one,
      ← ENNReal.ofReal_mul h_norm_nn]
  congr 1; ring

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **`m = 0` summand vanishes for cusp forms**.

For a cusp form `f` on `(Gamma1 N).map (mapGL ℝ)` and any `s : ℂ`, the
`m = 0` term of the period-one Mellin `h_summ` lintegrand is zero, because
`lCoeff f 0 = 0` (`lCoeff_zero_of_cuspForm`) makes the integrand identically
zero on `Ioi 0`. -/
lemma lintegral_qExpansion_term_zero_of_cuspForm
    {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) (s : ℂ) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s - 1) •
            (lCoeff f 0 * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ 0)‖ₑ = 0 := by
  simp_rw [lCoeff_zero_of_cuspForm f, zero_mul, smul_zero, enorm_zero,
    MeasureTheory.lintegral_zero]

/-- **`m = n + 1` summand has Gamma expression for the period-one Mellin
`h_summ` integrand**.

Combines `lintegral_enorm_qParam_pow_imAxis_term` (norm rewrite) with
`lintegral_real_qExpansion_term_eq_Gamma` (Gamma evaluation, valid for `m ≥ 1`)
into a single per-`(n+1)` evaluation, ready for the `tsum`-shift step in the
final summability bridge. -/
lemma lintegral_qExpansion_term_eq_Gamma_of_succ
    {a : ℂ} (n : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ∫⁻ t in Set.Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s - 1) •
            (a * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ (n + 1))‖ₑ
      = ENNReal.ofReal
          (‖a‖ * (2 * Real.pi * ((n : ℝ) + 1)) ^ (-s.re) * Real.Gamma s.re) := by
  have hm : (1 : ℕ) ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le _)
  rw [lintegral_enorm_qParam_pow_imAxis_term a (n + 1) s,
      lintegral_real_qExpansion_term_eq_Gamma (a := a) hm hs]
  congr 2
  push_cast
  ring

open CongruenceSubgroup Matrix.SpecialLinearGroup in
set_option maxHeartbeats 400000 in
/-- **`h_summ` of period-one Mellin lintegrand reduces to coefficient-tail
summability**.

Reducer: under the half-plane hypothesis `(k : ℝ) / 2 + 1 < s.re` (with
`0 < (k : ℝ)`), the per-`s` `h_summ` non-top condition expected by
`hasCompletedMellinIdentity_of_qExpansion_summ_Gamma1_mapGL` follows from
finiteness of the **coefficient-tail summability bound**
```
∑' n : ℕ, ENNReal.ofReal (‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re)) ≠ ⊤.
```

-/
theorem h_summ_of_tail_summable_Gamma1_mapGL
    {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) (hk_pos : 0 < (k : ℝ))
    {s : ℂ} (hs : ((k : ℝ) / 2 + 1 : ℝ) < s.re)
    (h_tail : (∑' n : ℕ,
      ENNReal.ofReal (‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re))) ≠ ⊤) :
    (∑' m : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ),
        ‖(t : ℂ) ^ (s - 1) •
          (lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ) ≠
      ⊤ := by
  have hs_re : 0 < s.re := by linarith [show (0 : ℝ) < (k : ℝ) / 2 + 1 by linarith]
  have h2π_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hΓ_pos : (0 : ℝ) < Real.Gamma s.re := Real.Gamma_pos_of_pos hs_re
  have h_shift :
      (∑' m : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ),
          ‖(t : ℂ) ^ (s - 1) •
            (lCoeff f m * Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ m)‖ₑ) =
        ∑' n : ℕ, ∫⁻ t in Set.Ioi (0 : ℝ),
            ‖(t : ℂ) ^ (s - 1) •
              (lCoeff f (n + 1) *
                Function.Periodic.qParam 1 (Complex.I * (t : ℂ)) ^ (n + 1))‖ₑ := by
    rw [tsum_eq_zero_add' ENNReal.summable,
        lintegral_qExpansion_term_zero_of_cuspForm f s, zero_add]
  rw [h_shift, tsum_congr (fun n ↦ lintegral_qExpansion_term_eq_Gamma_of_succ n hs_re)]
  have h_per_term : ∀ n : ℕ,
      ENNReal.ofReal
          (‖lCoeff f (n + 1)‖ * (2 * Real.pi * ((n : ℝ) + 1)) ^ (-s.re) *
            Real.Gamma s.re) =
        ENNReal.ofReal (Real.Gamma s.re * (2 * Real.pi) ^ (-s.re)) *
          ENNReal.ofReal (‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re)) := by
    intro n
    have h_2π_n1 : (2 * Real.pi * ((n : ℝ) + 1)) ^ (-s.re) =
        (2 * Real.pi) ^ (-s.re) * ((n : ℝ) + 1) ^ (-s.re) :=
      Real.mul_rpow (by positivity) (by positivity)
    have h_const_nn : (0 : ℝ) ≤ Real.Gamma s.re * (2 * Real.pi) ^ (-s.re) :=
      mul_nonneg hΓ_pos.le (Real.rpow_nonneg h2π_pos.le _)
    rw [h_2π_n1,
        show ‖lCoeff f (n + 1)‖ * ((2 * Real.pi) ^ (-s.re) * ((n : ℝ) + 1) ^ (-s.re))
            * Real.Gamma s.re =
          (Real.Gamma s.re * (2 * Real.pi) ^ (-s.re)) *
            (‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re)) by ring]
    exact ENNReal.ofReal_mul h_const_nn
  rw [tsum_congr h_per_term, ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h_tail

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **`HasCompletedMellinIdentity` from coefficient-tail summability for
`(Gamma1 N).map (mapGL ℝ)`-cusp forms**.

Combines `h_summ_of_tail_summable_Gamma1_mapGL` (per-`s` `h_summ` reducer)
with `hasCompletedMellinIdentity_of_qExpansion_summ_Gamma1_mapGL` (the
generic consumer that already discharges `h_decomp` and `h_meas`). The only
remaining hypothesis is the **coefficient-tail summability** bound
```
∀ {s : ℂ}, (k : ℝ)/2 + 1 < s.re →
  ∑' n : ℕ, ENNReal.ofReal (‖lCoeff f (n+1)‖ * ((n : ℝ) + 1) ^ (-s.re)) ≠ ⊤,
```
which is the genuinely-classical Hecke L¹-bound input that follows from
`CuspFormClass.qExpansion_isBigO`. -/
theorem hasCompletedMellinIdentity_of_tail_summable_Gamma1_mapGL
    {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F) (hk_pos : 0 < (k : ℝ))
    (h_tail : ∀ {s : ℂ}, ((k : ℝ) / 2 + 1 : ℝ) < s.re →
      (∑' n : ℕ,
          ENNReal.ofReal (‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re))) ≠ ⊤) :
    HasCompletedMellinIdentity f :=
  hasCompletedMellinIdentity_of_qExpansion_summ_Gamma1_mapGL f hk_pos
    (fun hs => h_summ_of_tail_summable_Gamma1_mapGL f hk_pos hs (h_tail hs))

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **Coefficient-tail summability for `Γ₁(N)` cusp forms**.

Hecke's polynomial bound `|aₙ| ≤ C · n^(k/2)` (the cusp-form variant of
`CuspFormClass.qExpansion_isBigO`) combined with the real `p`-series test
`Real.summable_nat_rpow` (with exponent `(k : ℝ)/2 - s.re < -1`, valid on
the half-plane `(k : ℝ)/2 + 1 < s.re`) yields absolute summability of the
shifted-index tail
```
fun n : ℕ ↦ ‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re).
```
This is the genuinely-classical Hecke L¹-bound, packaged in a form
directly consumable by `h_summ_of_tail_summable_Gamma1_mapGL`. -/
theorem summable_lCoeff_mul_rpow_of_cuspForm_Gamma1_mapGL
    {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F)
    {s : ℂ} (hs : ((k : ℝ) / 2 + 1 : ℝ) < s.re) :
    Summable (fun n : ℕ ↦ ‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re)) := by
  have hp_lt : ((k : ℝ) / 2 - s.re) < -1 := by linarith
  have h_bigO : (fun n : ℕ ↦ lCoeff f n) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2) := by
    simpa [lCoeff] using CuspFormClass.qExpansion_isBigO f
  obtain ⟨C, hCev⟩ := h_bigO.bound
  rw [Filter.eventually_atTop] at hCev
  obtain ⟨N₀, hC⟩ := hCev
  have h_target_bigO :
      (fun n : ℕ ↦ ‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re)) =O[atTop]
        fun n : ℕ ↦ ((n : ℝ) + 1) ^ ((k : ℝ) / 2 - s.re) := by
    refine Asymptotics.IsBigO.of_bound |C| ?_
    rw [Filter.eventually_atTop]
    refine ⟨N₀, fun n hn ↦ ?_⟩
    have h_n1_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h_n1_nn : (0 : ℝ) ≤ (n : ℝ) + 1 := h_n1_pos.le
    have h_pow_neg_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (-s.re) :=
      Real.rpow_nonneg h_n1_nn _
    have h_pow_k_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ ((k : ℝ) / 2) :=
      Real.rpow_nonneg h_n1_nn _
    have h_pow_diff_nn : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ ((k : ℝ) / 2 - s.re) :=
      Real.rpow_nonneg h_n1_nn _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) h_pow_neg_nn),
        Real.norm_eq_abs, abs_of_nonneg h_pow_diff_nn]
    have hN₀_le : N₀ ≤ n + 1 := Nat.le_succ_of_le hn
    have h_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have h_norm_bound : ‖lCoeff f (n + 1)‖ ≤ C * ((n : ℝ) + 1) ^ ((k : ℝ) / 2) := by
      have h0 := hC (n + 1) hN₀_le
      rw [h_cast, Real.norm_eq_abs, abs_of_nonneg h_pow_k_nn] at h0
      exact h0
    have h_combine :
        ((n : ℝ) + 1) ^ ((k : ℝ) / 2) * ((n : ℝ) + 1) ^ (-s.re) =
          ((n : ℝ) + 1) ^ ((k : ℝ) / 2 - s.re) := by
      rw [← Real.rpow_add h_n1_pos]; ring_nf
    calc ‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re)
        ≤ (C * ((n : ℝ) + 1) ^ ((k : ℝ) / 2)) * ((n : ℝ) + 1) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right h_norm_bound h_pow_neg_nn
      _ = C * ((n : ℝ) + 1) ^ ((k : ℝ) / 2 - s.re) := by rw [mul_assoc, h_combine]
      _ ≤ |C| * ((n : ℝ) + 1) ^ ((k : ℝ) / 2 - s.re) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h_pow_diff_nn
  have h_sum_pow :
      Summable (fun n : ℕ ↦ ((n : ℝ) + 1) ^ ((k : ℝ) / 2 - s.re)) := by
    have h_eq : (fun n : ℕ ↦ ((n : ℝ) + 1) ^ ((k : ℝ) / 2 - s.re)) =
        fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ) ^ ((k : ℝ) / 2 - s.re) := by
      funext n; push_cast; ring_nf
    rw [h_eq]
    exact (summable_nat_add_iff
        (f := fun n : ℕ ↦ (n : ℝ) ^ ((k : ℝ) / 2 - s.re)) 1).mpr
      (Real.summable_nat_rpow.mpr hp_lt)
  exact summable_of_isBigO_nat h_sum_pow h_target_bigO

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **ENNReal-form coefficient-tail summability for `Γ₁(N)` cusp forms**.

ENNReal repackaging of `summable_lCoeff_mul_rpow_of_cuspForm_Gamma1_mapGL`:
the term-by-term `ENNReal.ofReal` sum of the (nonneg-real) coefficient-tail
is finite.  This is the precise form consumed by
`hasCompletedMellinIdentity_of_tail_summable_Gamma1_mapGL`. -/
theorem ennreal_tsum_lCoeff_mul_rpow_ne_top_of_cuspForm_Gamma1_mapGL
    {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F)
    {s : ℂ} (hs : ((k : ℝ) / 2 + 1 : ℝ) < s.re) :
    (∑' n : ℕ,
      ENNReal.ofReal (‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re))) ≠ ⊤ := by
  have h_summ := summable_lCoeff_mul_rpow_of_cuspForm_Gamma1_mapGL f hs
  have h_nn : ∀ n : ℕ, 0 ≤ ‖lCoeff f (n + 1)‖ * ((n : ℝ) + 1) ^ (-s.re) :=
    fun n ↦ mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (by positivity) _)
  rw [← ENNReal.ofReal_tsum_of_nonneg h_nn h_summ]
  exact ENNReal.ofReal_ne_top

open CongruenceSubgroup Matrix.SpecialLinearGroup in
/-- **`HasCompletedMellinIdentity` for `(Gamma1 N).map (mapGL ℝ)` cusp forms**.

The full classical Hecke 1936 completed Mellin–Dirichlet identity for any
weight-`k` cusp form on `(Gamma1 N).map (mapGL ℝ)` (with `0 < (k : ℝ)`):
on the half-plane `(k : ℝ)/2 + 1 < s.re`,
```
mellin (imAxis f) s = (2π)^(-s) · Γ(s) · LSeries (lCoeff f) s.
```

-/
theorem hasCompletedMellinIdentity_Gamma1_mapGL
    {N : ℕ} [NeZero N] {k : ℤ} {F : Type*} [FunLike F ℍ ℂ]
    [CuspFormClass F ((Gamma1 N).map (mapGL ℝ)) k] (f : F)
    (hk_pos : 0 < (k : ℝ)) :
    HasCompletedMellinIdentity f :=
  hasCompletedMellinIdentity_of_tail_summable_Gamma1_mapGL f hk_pos
    (fun {_s} hs => ennreal_tsum_lCoeff_mul_rpow_ne_top_of_cuspForm_Gamma1_mapGL f hs)

end ModularForms

/-! ### Hecke entire-continuation predicate -/

namespace LSeries

/-! ### Abscissa monotonicity under pointwise norm bounds -/

/-- **Pointwise-norm domination ⇒ abscissa monotonicity.**

If `b : ℕ → ℂ` is dominated by `a : ℕ → ℂ` pointwise in norm
(`‖b n‖ ≤ ‖a n‖` for every `n : ℕ`), then the abscissa of absolute
convergence of `LSeries b` is at most that of `LSeries a`:

`abscissaOfAbsConv b ≤ abscissaOfAbsConv a`. -/
lemma abscissaOfAbsConv_le_of_norm_le {a b : ℕ → ℂ}
    (h : ∀ n, ‖b n‖ ≤ ‖a n‖) :
    abscissaOfAbsConv b ≤ abscissaOfAbsConv a := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' ?_
  intro y hy
  have h_summ_a : LSeriesSummable a (y : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hy)
  exact Summable.of_norm_bounded (g := fun n ↦ ‖LSeries.term a (y : ℂ) n‖)
    h_summ_a.norm (fun n ↦ LSeries.norm_term_le _ (h n))

/-- **Hecke entire-continuation predicate.**  A coefficient sequence
`a : ℕ → ℂ` *has an entire extension* if there exists an entire
function `F : ℂ → ℂ` agreeing with `LSeries a` on the
absolute-convergence half-plane `abscissaOfAbsConv a < s.re`.

The named-Prop form of the classical Hecke / Riemann analytic
continuation property:

* For cusp-form L-series this is Hecke 1936 (Diamond–Shurman §5.9 /
  Miyake §4.3.5).
* For Dirichlet character L-series this is `DirichletCharacter.LFunction`
  via `differentiable_completedLFunction`.
* For the Riemann ζ this is Riemann 1859.

The entire extension, when it exists, is **unique** on `ℂ`
(`HasEntireExtension.unique`). -/
def HasEntireExtension (a : ℕ → ℂ) : Prop :=
  ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
    ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s

namespace HasEntireExtension

variable {a : ℕ → ℂ}

/-- **Uniqueness of entire extension.**  Two entire functions
`F, G : ℂ → ℂ` that both extend `LSeries a` on the absolute-
convergence half-plane are equal everywhere on `ℂ`.

The hypothesis `abscissaOfAbsConv a < ⊤` is the standard finite-
abscissa requirement of `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`
(`Mathlib.NumberTheory.LSeries.Injectivity`); for cusp forms it is
discharged by `abscissaOfAbsConv_lCoeff_lt_top_of_cuspForm`. -/
theorem unique {F G : ℂ → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h_finite : abscissaOfAbsConv a < ⊤)
    (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s)
    (hGa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → G s = LSeries a s) :
    F = G := by
  obtain ⟨σ, hσ_abs, _⟩ := EReal.exists_between_coe_real h_finite
  let U : Set ℂ := {s : ℂ | (σ : ℝ) < s.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_sub : ∀ s ∈ U, abscissaOfAbsConv a < (s.re : EReal) := fun s hs ↦
    lt_of_lt_of_le hσ_abs (by exact_mod_cast (hs : (σ : ℝ) < s.re).le)
  have hF_eq_G_on_U : ∀ s ∈ U, F s = G s := fun s hs ↦
    (hFa (hU_sub s hs)).trans (hGa (hU_sub s hs)).symm
  have hU_ne : U.Nonempty := ⟨((σ + 1 : ℝ) : ℂ), by
    show (σ : ℝ) < ((σ + 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith⟩
  obtain ⟨z₀, hz₀⟩ := hU_ne
  have hF_eq_G_nhd : F =ᶠ[nhds z₀] G :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU_open.mem_nhds hz₀, hF_eq_G_on_U⟩
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG) hF_eq_G_nhd

/-- **Equality of entire extensions when underlying L-series agree.**
If two coefficient sequences `a, b : ℕ → ℂ` both have entire
extensions and their `LSeries` agree on the joint absolute-convergence
half-plane, then their entire extensions are equal everywhere on `ℂ`.

This is the cleanest "consumer" form: under matching analytic-
continuation hypotheses on both sides, half-plane agreement of
L-series propagates to global agreement of extensions. -/
theorem extension_eq_of_lSeries_eq_on_halfPlane
    {a b : ℕ → ℂ} {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (h_finite_a : abscissaOfAbsConv a < ⊤)
    (h_finite_b : abscissaOfAbsConv b < ⊤)
    (hFa : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re → F s = LSeries a s)
    (hGb : ∀ {s : ℂ}, abscissaOfAbsConv b < s.re → G s = LSeries b s)
    (h_eq : ∀ {s : ℂ}, abscissaOfAbsConv a < s.re →
        abscissaOfAbsConv b < s.re → LSeries a s = LSeries b s) :
    F = G := by
  have h_max_top : max (abscissaOfAbsConv a) (abscissaOfAbsConv b) < ⊤ :=
    max_lt h_finite_a h_finite_b
  obtain ⟨σ, hσ_max, _⟩ := EReal.exists_between_coe_real h_max_top
  have hσ_a : abscissaOfAbsConv a < (σ : EReal) :=
    lt_of_le_of_lt (le_max_left _ _) hσ_max
  have hσ_b : abscissaOfAbsConv b < (σ : EReal) :=
    lt_of_le_of_lt (le_max_right _ _) hσ_max
  let U : Set ℂ := {s : ℂ | (σ : ℝ) < s.re}
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_sub_a : ∀ s ∈ U, abscissaOfAbsConv a < (s.re : EReal) := fun s hs ↦
    lt_of_lt_of_le hσ_a (by exact_mod_cast (hs : (σ : ℝ) < s.re).le)
  have hU_sub_b : ∀ s ∈ U, abscissaOfAbsConv b < (s.re : EReal) := fun s hs ↦
    lt_of_lt_of_le hσ_b (by exact_mod_cast (hs : (σ : ℝ) < s.re).le)
  have hF_eq_G_on_U : ∀ s ∈ U, F s = G s := fun s hs ↦ by
    rw [hFa (hU_sub_a s hs), h_eq (hU_sub_a s hs) (hU_sub_b s hs), ← hGb (hU_sub_b s hs)]
  have hU_ne : U.Nonempty := ⟨((σ + 1 : ℝ) : ℂ), by
    show (σ : ℝ) < ((σ + 1 : ℝ) : ℂ).re; rw [Complex.ofReal_re]; linarith⟩
  obtain ⟨z₀, hz₀⟩ := hU_ne
  have hF_eq_G_nhd : F =ᶠ[nhds z₀] G :=
    Filter.eventuallyEq_iff_exists_mem.mpr ⟨U, hU_open.mem_nhds hz₀, hF_eq_G_on_U⟩
  exact (Complex.analyticOnNhd_univ_iff_differentiable.mpr hF).eq_of_eventuallyEq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hG) hF_eq_G_nhd

end HasEntireExtension

/-! ### Meromorphic-order quotient helper -/

namespace HasMeromorphicExtensionWithPole

/-- **Quotient pole sufficient condition.**

If `num, den : 𝕜 → 𝕜` are meromorphic at `x`, both with finite
(`≠ ⊤`) order, and `meromorphicOrderAt num x < meromorphicOrderAt den x`,
then `fun s ↦ num s / den s` has **negative** meromorphic order at `x`
— i.e., the quotient has a pole at `x`.

-/
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
  have h_neg_eq : -((m : ℤ) : WithTop ℤ) = (((-m) : ℤ) : WithTop ℤ) := rfl
  rw [h_neg_eq, ← WithTop.coe_add,
      show (0 : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) from rfl, WithTop.coe_lt_coe]
  omega

end HasMeromorphicExtensionWithPole

/-! ### Meromorphic-extension-with-pole predicate -/

/-- **Meromorphic extension with a pole — analytic obligation Prop.**

A coefficient sequence `a : ℕ → ℂ` *has a meromorphic extension with a pole*
if there exist a witness function `g : ℂ → ℂ` and a witness pole point
`s₀ : ℂ` such that:

* `g` is meromorphic at `s₀`;
* `g` has *negative* meromorphic order at `s₀` — i.e., `g` blows up at `s₀`
  (the precise mathlib formulation of "pole");
* every entire extension `F : ℂ → ℂ` of `LSeries a` must coincide with
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

Given any coefficient sequence `a : ℕ → ℂ` admitting both an entire
extension (`HasEntireExtension a`) and a meromorphic extension with a
pole (`HasMeromorphicExtensionWithPole a`), False follows.

-/
theorem not_hasEntireExtension {a : ℕ → ℂ}
    (h_pole : LSeries.HasMeromorphicExtensionWithPole a) :
    ¬ LSeries.HasEntireExtension a := by
  rintro ⟨F, hF_diff, hF_eq⟩
  obtain ⟨g, s₀, hg_mero, hg_order, h_punc⟩ := h_pole
  have h_F_g_punc : F =ᶠ[nhdsWithin s₀ {s₀}ᶜ] g := h_punc F hF_diff @hF_eq
  have hF_an_s₀ : AnalyticAt ℂ F s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hF_diff s₀ (Set.mem_univ _)
  have h_order_eq : meromorphicOrderAt F s₀ = meromorphicOrderAt g s₀ :=
    meromorphicOrderAt_congr h_F_g_punc
  have h_F_order_nonneg : 0 ≤ meromorphicOrderAt F s₀ :=
    hF_an_s₀.meromorphicOrderAt_nonneg
  rw [h_order_eq] at h_F_order_nonneg
  exact absurd h_F_order_nonneg (not_le.mpr hg_order)

end HasMeromorphicExtensionWithPole

/-! ### Euler-stripping bridge for multiplicative Dirichlet series

For multiplicative `f : ℕ → ℂ` and a finite Finset `S` of primes, the
coprime-stripped sequence `coprimeStrip S f` zeroes out any positive
integer sharing a factor with a prime in `S`, so that
```
LSeries f s = (∏ p ∈ S, ∑' e, LSeries.term f s (p^e)) · LSeries (coprimeStrip S f) s
```
on the absolute-convergence half-plane (Diamond–Shurman §5.9 / Miyake §4.5.16). -/

/-- **Coprime-stripped coefficient sequence at a Finset of primes.**

The S-stripped version of `f : ℕ → ℂ`: zeroed at every positive
integer `n` divisible by some prime in `S`, equal to `f n` elsewhere.

For `n = 0`: every prime divides `0`, so the condition `(∀ p ∈ S, ¬ p ∣ 0)`
is `False` for nonempty `S` (giving `0`) and vacuously `True` for empty
`S` (giving `f 0`).  The intended use case is `S` covering at least one
prime, and the user supplies `f 0 = 0` separately for Dirichlet series
applications. -/
def coprimeStrip (S : Finset Nat.Primes) (f : ℕ → ℂ) : ℕ → ℂ :=
  fun n ↦ if ∀ p ∈ S, ¬ (p : ℕ) ∣ n then f n else 0

/-- **`coprimeStrip S f 1 = f 1`** (since no prime divides `1`). -/
@[simp]
lemma coprimeStrip_one (S : Finset Nat.Primes) (f : ℕ → ℂ) :
    coprimeStrip S f 1 = f 1 := by
  unfold coprimeStrip
  have h_no_dvd : ∀ p ∈ S, ¬ (p : ℕ) ∣ 1 :=
    fun p _ h_dvd ↦ p.prop.one_lt.ne' (Nat.dvd_one.mp h_dvd)
  rw [if_pos h_no_dvd]

/-- **`coprimeStrip` preserves multiplicativity on coprime arguments.**

If `f m * f n = f (m * n)` whenever `gcd m n = 1`, then the same holds
for `coprimeStrip S f`.  The "stripping" indicator (zero at multiples
of any `p ∈ S`) is itself multiplicative on coprime arguments: the
condition "no prime in `S` divides `m * n`" is equivalent to "no prime
in `S` divides `m`" AND "no prime in `S` divides `n`" (when
`gcd m n = 1`, since a prime dividing the product divides at least
one factor — and by coprimality, exactly one). -/
lemma coprimeStrip_mul_of_coprime (S : Finset Nat.Primes) (f : ℕ → ℂ)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    {m n : ℕ} (hmn : Nat.Coprime m n) :
    coprimeStrip S f (m * n) = coprimeStrip S f m * coprimeStrip S f n := by
  unfold coprimeStrip
  by_cases hmn_strip : ∀ p ∈ S, ¬ (p : ℕ) ∣ m * n
  · rw [if_pos hmn_strip]
    have hm_strip : ∀ p ∈ S, ¬ (p : ℕ) ∣ m := fun p hp h_dvd ↦
      hmn_strip p hp (h_dvd.mul_right n)
    have hn_strip : ∀ p ∈ S, ¬ (p : ℕ) ∣ n := fun p hp h_dvd ↦
      hmn_strip p hp (h_dvd.mul_left m)
    rw [if_pos hm_strip, if_pos hn_strip]
    exact hmul hmn
  · rw [if_neg hmn_strip]
    push_neg at hmn_strip
    obtain ⟨p, hp, hp_dvd⟩ := hmn_strip
    rcases (p.prop.dvd_mul.mp hp_dvd) with h_dvd_m | h_dvd_n
    · have hm_neg : ¬ ∀ p ∈ S, ¬ (p : ℕ) ∣ m :=
        fun h => h p hp h_dvd_m
      rw [if_neg hm_neg, zero_mul]
    · have hn_neg : ¬ ∀ p ∈ S, ¬ (p : ℕ) ∣ n :=
        fun h => h p hp h_dvd_n
      rw [if_neg hn_neg, mul_zero]

/-- **`coprimeStrip` value on a positive prime power at a prime in `S`.**

For `p ∈ S` and `e ≥ 1`, the prime `p` divides `p ^ e`, so the
stripping condition fails and `coprimeStrip S f (p^e) = 0`. -/
lemma coprimeStrip_prime_pow_at_S (S : Finset Nat.Primes) (f : ℕ → ℂ)
    {p : Nat.Primes} (hp : p ∈ S) {e : ℕ} (he : 1 ≤ e) :
    coprimeStrip S f ((p : ℕ) ^ e) = 0 := by
  unfold coprimeStrip
  rw [if_neg]
  push_neg
  exact ⟨p, hp, dvd_pow_self _ (Nat.one_le_iff_ne_zero.mp he)⟩

/-- **`coprimeStrip` value on a prime power at a prime not in `S`.**

For `p ∉ S` and any `e : ℕ`, the unique prime dividing `p^e` is `p`
(when `e ≥ 1`) or no prime divides `1` (when `e = 0`); in either case,
no prime in `S` divides `p^e`, so the stripping condition holds and
`coprimeStrip S f (p^e) = f (p^e)`. -/
lemma coprimeStrip_prime_pow_off_S (S : Finset Nat.Primes) (f : ℕ → ℂ)
    {p : Nat.Primes} (hp : p ∉ S) (e : ℕ) :
    coprimeStrip S f ((p : ℕ) ^ e) = f ((p : ℕ) ^ e) := by
  unfold coprimeStrip
  rw [if_pos]
  intro q hq h_dvd
  have h_q_eq_p : (q : ℕ) = (p : ℕ) :=
    (Nat.prime_dvd_prime_iff_eq q.prop p.prop).mp
      (q.prop.dvd_of_dvd_pow h_dvd)
  have h_q_eq : q = p := Subtype.ext h_q_eq_p
  exact hp (h_q_eq ▸ hq)

/-- **Local Euler factor of the coprimeStrip sequence at a prime in `S`.**

If `f 0 = 0` and `f 1 = 1`, then for `p ∈ S`, the local Euler factor
of `coprimeStrip S f` at `p` collapses to `1`: the only contributing
exponent is `e = 0` (since `coprimeStrip S f (p^e) = 0` for `e ≥ 1`)
and `LSeries.term (coprimeStrip S f) s 1 = 1`. -/
lemma coprimeStrip_eulerFactor_at_S
    (S : Finset Nat.Primes) {f : ℕ → ℂ} (hf₁ : f 1 = 1)
    (s : ℂ) {p : Nat.Primes} (hp : p ∈ S) :
    ∑' e : ℕ, LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e) = 1 := by
  have h_term_zero : ∀ e : ℕ, 1 ≤ e →
      LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e) = 0 := by
    intro e he
    have h_pow_pos : 0 < (p : ℕ) ^ e := pow_pos p.prop.pos e
    rw [LSeries.term_def, if_neg h_pow_pos.ne',
      coprimeStrip_prime_pow_at_S S f hp he, zero_div]
  rw [tsum_eq_single 0 (fun e he_ne_zero =>
    h_term_zero e (Nat.one_le_iff_ne_zero.mpr he_ne_zero))]
  show LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ 0) = 1
  rw [pow_zero, LSeries.term_def, if_neg one_ne_zero]
  have h_strip_one : coprimeStrip S f 1 = 1 := by
    rw [coprimeStrip_one S f, hf₁]
  rw [h_strip_one, Nat.cast_one, Complex.one_cpow, div_one]

/-- **Local Euler factor of the coprimeStrip sequence at a prime not in `S`.**

If `f 0 = 0` and `f 1 = 1`, then for `p ∉ S` the local Euler factor of
`coprimeStrip S f` at `p` equals the local Euler factor of `f` at `p`:
the strip condition is vacuous on prime powers of `p ∉ S`, so each
term `LSeries.term (coprimeStrip S f) s (p^e) = LSeries.term f s (p^e)`. -/
lemma coprimeStrip_eulerFactor_off_S
    (S : Finset Nat.Primes) (f : ℕ → ℂ)
    (s : ℂ) {p : Nat.Primes} (hp : p ∉ S) :
    ∑' e : ℕ, LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e) =
      ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e) := by
  apply tsum_congr
  intro e
  by_cases he : e = 0
  · subst he
    simp [coprimeStrip_one S f]
  · have h_pow_pos : 0 < (p : ℕ) ^ e := pow_pos p.prop.pos e
    rw [LSeries.term_def, LSeries.term_def, if_neg h_pow_pos.ne',
      if_neg h_pow_pos.ne', coprimeStrip_prime_pow_off_S S f hp e]

/-- **Euler-stripping bridge from named `HasProd` Euler-product hypotheses.**

Strict reduction theorem: under named Euler-product hypotheses for `f`
and `coprimeStrip S f`, the L-series of `f` factors as the product
over `S` of `f`'s local Euler factors times the L-series of the
S-stripped sequence:
```
LSeries f s = (∏ p ∈ S, ∑' e, LSeries.term f s (p^e)) · LSeries (coprimeStrip S f) s
```

-/
theorem eulerStripping_bridge_via_eulerProduct
    {f : ℕ → ℂ} {s : ℂ} (S : Finset Nat.Primes)
    (hf₁ : f 1 = 1)
    (hf_euler : HasProd
      (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e))
      (LSeries f s))
    (hg_euler : HasProd
      (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term (coprimeStrip S f) s
        ((p : ℕ) ^ e))
      (LSeries (coprimeStrip S f) s)) :
    LSeries f s = (∏ p ∈ S, ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e)) *
                    LSeries (coprimeStrip S f) s := by
  set φ_f : Nat.Primes → ℂ :=
    fun p ↦ ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e) with hφ_f_def
  set φ_g : Nat.Primes → ℂ :=
    fun p ↦ ∑' e : ℕ, LSeries.term (coprimeStrip S f) s ((p : ℕ) ^ e) with hφ_g_def
  have h_φ_g_eq : ∀ p : Nat.Primes,
      φ_g p = if p ∈ S then 1 else φ_f p := by
    intro p
    by_cases hp : p ∈ S
    · rw [if_pos hp]; exact coprimeStrip_eulerFactor_at_S S hf₁ s hp
    · rw [if_neg hp]; exact coprimeStrip_eulerFactor_off_S S f s hp
  set ψ : Nat.Primes → ℂ := fun p ↦ if p ∈ S then 1 else φ_f p with hψ_def
  have hg_euler' : HasProd ψ (LSeries (coprimeStrip S f) s) :=
    hg_euler.congr_fun (fun p ↦ (h_φ_g_eq p).symm)
  set r : Nat.Primes → ℂ := fun p ↦ if p ∈ S then φ_f p else 1 with hr_def
  have h_r_support : ∀ p : Nat.Primes, p ∉ S → r p = 1 :=
    fun p hp ↦ by show (if p ∈ S then φ_f p else 1) = 1; rw [if_neg hp]
  have h_r_HasProd_raw : HasProd r (∏ p ∈ S, r p) :=
    hasProd_prod_of_ne_finset_one (s := S) h_r_support
  have h_prod_S_eq : ∏ p ∈ S, r p = ∏ p ∈ S, φ_f p :=
    Finset.prod_congr rfl (fun p hp ↦ by
      show (if p ∈ S then φ_f p else 1) = φ_f p; rw [if_pos hp])
  have h_r_HasProd : HasProd r (∏ p ∈ S, φ_f p) := h_prod_S_eq ▸ h_r_HasProd_raw
  have h_mul : HasProd (fun p ↦ ψ p * r p)
      ((LSeries (coprimeStrip S f) s) * ∏ p ∈ S, φ_f p) :=
    hg_euler'.mul h_r_HasProd
  have h_ψr_eq_φf : ∀ p : Nat.Primes, ψ p * r p = φ_f p := by
    intro p
    show (if p ∈ S then (1 : ℂ) else φ_f p) * (if p ∈ S then φ_f p else 1) = φ_f p
    by_cases hp : p ∈ S
    · rw [if_pos hp, if_pos hp, one_mul]
    · rw [if_neg hp, if_neg hp, mul_one]
  have h_mul' : HasProd φ_f
      ((LSeries (coprimeStrip S f) s) * ∏ p ∈ S, φ_f p) :=
    h_mul.congr_fun (fun p ↦ (h_ψr_eq_φf p).symm)
  rw [hf_euler.unique h_mul']; ring

/-- **Inverted Euler-stripping bridge: `coprimeStrip` LSeries factors as a
polynomial multiplier times the original LSeries.**

Strict reduction theorem: under the named Euler-product `HasProd` hypotheses
for both `f` and `coprimeStrip S f`, plus a representation of each local
Euler factor of `f` at `p ∈ S` as `(poly p)⁻¹` (with `poly p ≠ 0`), the
L-series of the S-stripped sequence factors as
```
LSeries (coprimeStrip S f) s = (∏ p ∈ S, poly p) * LSeries f s.
```

Substituting `local_factor_p = (poly p)⁻¹` in
`eulerStripping_bridge_via_eulerProduct` and inverting gives this form. -/
theorem coprimeStrip_LSeries_eq_polynomial_mul_LSeries
    {f : ℕ → ℂ} {s : ℂ} (S : Finset Nat.Primes)
    (hf₁ : f 1 = 1)
    (hf_euler : HasProd
      (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e))
      (LSeries f s))
    (hg_euler : HasProd
      (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term (coprimeStrip S f) s
        ((p : ℕ) ^ e))
      (LSeries (coprimeStrip S f) s))
    (poly : Nat.Primes → ℂ)
    (h_poly_ne_zero : ∀ p ∈ S, poly p ≠ 0)
    (h_poly_inv : ∀ p ∈ S,
      ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e) = (poly p)⁻¹) :
    LSeries (coprimeStrip S f) s = (∏ p ∈ S, poly p) * LSeries f s := by
  have h_bridge :=
    eulerStripping_bridge_via_eulerProduct S hf₁ hf_euler hg_euler
  have h_prod_eq : (∏ p ∈ S, ∑' e : ℕ, LSeries.term f s ((p : ℕ) ^ e)) =
      ∏ p ∈ S, (poly p)⁻¹ :=
    Finset.prod_congr rfl (fun p hp ↦ h_poly_inv p hp)
  rw [h_prod_eq, Finset.prod_inv_distrib] at h_bridge
  have h_prod_ne_zero : (∏ p ∈ S, poly p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr h_poly_ne_zero
  rw [eq_inv_mul_iff_mul_eq₀ h_prod_ne_zero] at h_bridge
  exact h_bridge.symm

/-- **Entirety of the explicit finite-Euler-factor polynomial multiplier.**

For any finite `Finset` of primes `S` and any complex coefficient sequence
`a : Nat.Primes → ℂ`, the function
```
s ↦ ∏ p ∈ S, (1 - a p * ((p : ℕ) : ℂ) ^ (-s))
```
is **entire on `ℂ`**.

This is the differentiability obligation for the standard cusp-form
Euler-stripping multiplier (Diamond–Shurman §5.9 / Miyake §4.5.16):
each factor `1 - a p * p^{-s}` is a Dirichlet polynomial in `p^{-s}`,
entire since each factor `1 - a p * p^{-s}` is differentiable
(via `differentiable_const_cpow_of_neZero`) and finite products
preserve entirety. -/
theorem differentiable_eulerFactor_polynomial_finset
    (S : Finset Nat.Primes) (a : Nat.Primes → ℂ) :
    Differentiable ℂ (fun s : ℂ ↦
      ∏ p ∈ S, (1 - a p * ((p : ℕ) : ℂ) ^ (-s))) := by
  refine Differentiable.fun_finset_prod (fun p _ ↦ ?_)
  have hp_ne : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.prop.pos.ne'
  haveI : NeZero (((p : ℕ) : ℂ)) := ⟨hp_ne⟩
  fun_prop

/-- **Euler-stripping multiplier as an entire function plus pointwise bridge.**

Strict reduction theorem assembling `coprimeStrip_LSeries_eq_polynomial_mul_LSeries`
(per-point algebraic factorisation) and `differentiable_eulerFactor_polynomial_finset`
(global entirety) into the **explicit triple shape consumed by
`Newform.HasEulerStrippingMultiplier`**:

```
∃ stripping : ℂ → ℂ,
  Differentiable ℂ stripping ∧
  ∀ ⦃s : ℂ⦄, H s →
    LSeries (coprimeStrip S f) s = stripping s * LSeries f s
```

where `H : ℂ → Prop` is the abstract predicate describing the half-plane on
which all hypotheses hold (typically `((k : ℝ) / 2 + 1 : ℝ) < s.re` for a
weight-`k` Hecke eigenform).

-/
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
