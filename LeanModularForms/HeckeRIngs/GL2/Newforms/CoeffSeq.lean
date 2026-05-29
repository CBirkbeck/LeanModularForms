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
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: Strong Multiplicity One inputs, coefficient sequences, and L-series

Strong Multiplicity One, the coefficient-sequence view of a newform, the
`IsHeckeCoefficientSequence` predicate, closed forms at bad primes, the newform
L-series, the stripped Hecke sequence and its Euler product, Dirichlet-quotient
identifications, and the final value identities.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The underlying modular form of a `Newform` is a period-1 normalised
eigenform (`IsNormalisedEigenform_one`) at the `ModularForm` level. -/
theorem Newform.isNormalisedEigenform (f : Newform N k) :
    IsNormalisedEigenform_one k f.toCuspForm.toModularForm' := by
  refine ⟨?_, ?_⟩
  · intro n' hn'
    haveI : NeZero n'.val := ⟨n'.pos.ne'⟩
    refine ⟨f.eigenvalue n', ?_⟩
    have h_lift : (heckeT_n_cusp k n'.val f.toCuspForm).toModularForm' =
        (f.eigenvalue n' • f.toCuspForm).toModularForm' := by rw [f.isEigen n' hn']
    rw [heckeT_n_cusp_toModularForm'] at h_lift
    exact h_lift
  · exact f.isNorm

/-- **Coprime multiplicativity of eigenvalues**: if `f` is a newform in the
character eigenspace `modFormCharSpace k χ` and `gcd(m, n) = 1`, then
`λ_{mn} = λ_m · λ_n`. -/
theorem Newform.eigenvalue_coprime_mul (f : Newform N k) (m n : ℕ+)
    (hm : Nat.Coprime m.val N) (hn : Nat.Coprime n.val N)
    (hmn : Nat.Coprime m.val n.val) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.eigenvalue ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩ =
      f.eigenvalue m * f.eigenvalue n := by
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have hmn_N : Nat.Coprime (m.val * n.val) N := hm.mul_left hn
  rw [Newform.eigenvalue_eq_coeff f ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩
        hmn_N χ hf_char,
      Newform.eigenvalue_eq_coeff f m hm χ hf_char,
      Newform.eigenvalue_eq_coeff f n hn χ hf_char]
  change (ModularFormClass.qExpansion (1 : ℝ)
        f.toCuspForm.toModularForm').coeff (m.val * n.val) =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff m.val *
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff n.val
  have h := eigenform_coeff_multiplicative_one k m n hm hn χ hf_char
    f.isNormalisedEigenform
  have hgcd : Nat.gcd m.val n.val = 1 := hmn
  rw [hgcd, Nat.divisors_one, Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] at h
  exact h.symm

/-- Coefficient sequence of a newform: `n ↦ aₙ(f)` via the canonical
period-1 q-expansion (the standard Fourier coefficients of `f` as a
`Γ₁(N)`-cusp form). -/
noncomputable def Newform.lCoeff (f : Newform N k) : ℕ → ℂ :=
  fun n ↦ (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n

@[simp]
lemma Newform.lCoeff_apply (f : Newform N k) (n : ℕ) :
    f.lCoeff n = (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n := rfl

/-- `a₀(f) = 0` for a newform (cusp forms vanish at infinity). -/
lemma Newform.lCoeff_zero (f : Newform N k) : f.lCoeff 0 = 0 := by
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  simp [Newform.lCoeff,
    ModularFormClass.qExpansion_coeff_zero (f := f.toCuspForm) one_pos h1_period,
    (CuspFormClass.zero_at_infty f.toCuspForm).valueAtInfty_eq_zero]

/-- **Normalisation**: `a₁(f) = 1` for a newform, directly from `f.isNorm`
(which is stated at the canonical period 1). -/
@[simp]
lemma Newform.lCoeff_one (f : Newform N k) : f.lCoeff 1 = 1 := f.isNorm

/-- **Coprime multiplicativity** of the newform coefficient sequence at
the canonical period 1: for `m, n ≥ 1` coprime to `N` with `gcd m n = 1`,
`a_{m n}(f) = a_m(f) · a_n(f)`. -/
lemma Newform.lCoeff_mul_of_coprime (f : Newform N k) (m n : ℕ)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) (hmn : Nat.Coprime m n)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.lCoeff (m * n) = f.lCoeff m * f.lCoeff n := by
  have h_m : f.eigenvalue ⟨m, hm_pos⟩ =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff m :=
    Newform.eigenvalue_eq_coeff (f := f) ⟨m, hm_pos⟩ hm χ hf_char
  have h_n : f.eigenvalue ⟨n, hn_pos⟩ =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n :=
    Newform.eigenvalue_eq_coeff (f := f) ⟨n, hn_pos⟩ hn χ hf_char
  have h_mn : f.eigenvalue ⟨m * n, Nat.mul_pos hm_pos hn_pos⟩ =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff (m * n) :=
    Newform.eigenvalue_eq_coeff (f := f) ⟨m * n, Nat.mul_pos hm_pos hn_pos⟩
      (hm.mul_left hn) χ hf_char
  simp only [Newform.lCoeff_apply]
  rw [← h_mn, ← h_m, ← h_n]
  exact Newform.eigenvalue_coprime_mul f ⟨m, hm_pos⟩ ⟨n, hn_pos⟩ hm hn hmn χ hf_char

/-- **A Hecke coefficient sequence** `a : ℕ → ℂ` at level `N`, weight `k`,
with Nebentypus character `χ : (ZMod N)ˣ →* ℂˣ`: the four arithmetic
properties shared by every Fourier coefficient sequence of a normalised
Hecke eigenform in `S_k(Γ₁(N), χ)`.

These four fields are **strictly weaker than the cusp-form analytic input**:
the sequence with `a p = 0` at every prime coprime to `N` satisfies them all
yet has every prime coefficient zero, so prime-nonvanishing needs an extra
analytic hypothesis (see `Newform.exists_nonzero_prime_eigenvalue`).

References: Miyake Thm 4.5.16, Diamond–Shurman §5.8. -/
structure IsHeckeCoefficientSequence (N : ℕ) (k : ℤ)
    (χ : (ZMod N)ˣ →* ℂˣ) (a : ℕ → ℂ) : Prop where
  /-- The coefficient at `0` vanishes (cusp condition). -/
  zero : a 0 = 0
  /-- Normalisation: the coefficient at `1` equals `1`. -/
  one : a 1 = 1
  /-- Coprime multiplicativity: `a_{mn} = a_m · a_n` when `m`, `n` are coprime
  to each other and both coprime to `N`. -/
  mul_coprime : ∀ {m n : ℕ}, Nat.Coprime m N → Nat.Coprime n N →
    Nat.Coprime m n → a (m * n) = a m * a n
  /-- Hecke recurrence at primes coprime to `N`:
  `a_{p^{r+2}} = a_p · a_{p^{r+1}} − χ(p) · p^{k-1} · a_{p^r}`. -/
  recur : ∀ {p : ℕ} (_hp : p.Prime) (hpN : Nat.Coprime p N) (r : ℕ),
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) -
      (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) * a (p ^ r)

/-- **Odd-prime-power vanishing.**  If a Hecke coefficient sequence
satisfies `a q = 0` at a prime `q` coprime to the level, then by the
Hecke recurrence every odd power `q ^ (2 j + 1)` also has zero
coefficient. -/
theorem IsHeckeCoefficientSequence.coeff_prime_pow_odd_eq_zero_of_a_p_zero
    {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {a : ℕ → ℂ}
    (h : IsHeckeCoefficientSequence N k χ a)
    {q : ℕ} (hq : q.Prime) (hqN : Nat.Coprime q N)
    (h_zero : a q = 0) (j : ℕ) :
    a (q ^ (2 * j + 1)) = 0 := by
  induction j with
  | zero => simpa using h_zero
  | succ j ih =>
    have h_eq : 2 * (j + 1) + 1 = (2 * j + 1) + 2 := by ring
    rw [h_eq, h.recur hq hqN (2 * j + 1), h_zero, ih]
    ring

/-- **Even-prime-power closed form.**  If a Hecke coefficient sequence
satisfies `a q = 0` at a prime `q` coprime to the level, then by the
Hecke recurrence every even power has the explicit closed form
`a (q ^ (2 j)) = (-χ(q) · q^{k-1}) ^ j`. -/
theorem IsHeckeCoefficientSequence.coeff_prime_pow_even_eq_of_a_p_zero
    {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {a : ℕ → ℂ}
    (h : IsHeckeCoefficientSequence N k χ a)
    {q : ℕ} (hq : q.Prime) (hqN : Nat.Coprime q N)
    (h_zero : a q = 0) (j : ℕ) :
    a (q ^ (2 * j)) =
      (-((χ (ZMod.unitOfCoprime q hqN) : ℂ)) * (q : ℂ) ^ (k - 1)) ^ j := by
  induction j with
  | zero => simp [h.one]
  | succ j ih =>
    have h_eq : 2 * (j + 1) = 2 * j + 2 := by ring
    rw [h_eq, h.recur hq hqN (2 * j), h_zero, ih, pow_succ]
    ring

/-- **Combined closed form.**  Joint statement: under `a q = 0` (with `q`
prime coprime to the level), every prime-power coefficient at `q` is given
by the alternating-power closed form indexed by `Even / Odd`. -/
theorem IsHeckeCoefficientSequence.coeff_prime_pow_eq_of_a_p_zero
    {N : ℕ} {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {a : ℕ → ℂ}
    (h : IsHeckeCoefficientSequence N k χ a)
    {q : ℕ} (hq : q.Prime) (hqN : Nat.Coprime q N)
    (h_zero : a q = 0) (r : ℕ) :
    a (q ^ r) =
      if Even r then
        (-((χ (ZMod.unitOfCoprime q hqN) : ℂ)) * (q : ℂ) ^ (k - 1)) ^ (r / 2)
      else 0 := by
  rcases Nat.even_or_odd r with hr | hr
  · obtain ⟨j, rfl⟩ := hr
    have h_even : Even (j + j) := ⟨j, rfl⟩
    have h_two_j : j + j = 2 * j := by ring
    rw [if_pos h_even, h_two_j, h.coeff_prime_pow_even_eq_of_a_p_zero hq hqN h_zero j]
    have hj_div : (2 * j) / 2 = j := by
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hj_div]
  · obtain ⟨j, rfl⟩ := hr
    rw [if_neg (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩)]
    exact h.coeff_prime_pow_odd_eq_zero_of_a_p_zero hq hqN h_zero j

private lemma Newform.lCoeff_recur (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    {p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N) (r : ℕ) :
    f.lCoeff (p ^ (r + 2)) = f.lCoeff p * f.lCoeff (p ^ (r + 1)) -
      (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) * f.lCoeff (p ^ r) := by
  have hp_pos : 0 < p := hp.pos
  haveI : NeZero p := ⟨hp_pos.ne'⟩
  have hpow_pos : 0 < p ^ (r + 1) := pow_pos hp_pos _
  haveI : NeZero (p ^ (r + 1)) := ⟨hpow_pos.ne'⟩
  have h := eigenform_coeff_multiplicative_one (N := N) k
    ⟨p ^ (r + 1), hpow_pos⟩ ⟨p, hp_pos⟩ (hpN.pow_left _) hpN χ hfχ
    f.isNormalisedEigenform
  simp only [PNat.mk_coe] at h
  have h_mn : p ^ (r + 1) * p = p ^ (r + 2) := by ring
  rw [Nat.gcd_eq_right (dvd_pow_self p (Nat.succ_ne_zero r)), hp.divisors,
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hp.ne_one.symm),
      Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] at h
  rw [dif_pos hpN] at h
  have h_div : p ^ (r + 1) * p / (p * p) = p ^ r := by
    rw [show p ^ (r + 1) * p = p ^ r * (p * p) by ring]
    exact Nat.mul_div_cancel _ (by positivity)
  rw [h_div, h_mn] at h
  simp only [Newform.lCoeff_apply]
  change (ModularFormClass.qExpansion (1 : ℝ)
        f.toCuspForm.toModularForm').coeff (p ^ (r + 2)) =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff p *
      (ModularFormClass.qExpansion (1 : ℝ)
        f.toCuspForm.toModularForm').coeff (p ^ (r + 1)) -
      (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff (p ^ r)
  linear_combination -h

/-- **Bridge**: the Fourier coefficient sequence of a `Newform` living in a
character eigenspace `modFormCharSpace k χ` satisfies
`IsHeckeCoefficientSequence`, the four arithmetic axioms required by the
Euler-product / Dirichlet-series machinery. -/
theorem Newform.lCoeff_isHeckeCoefficientSequence (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    IsHeckeCoefficientSequence N k χ f.lCoeff where
  zero := f.lCoeff_zero
  one := f.lCoeff_one
  mul_coprime := by
    intro m n hmN hnN hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hn1 : n = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_left] at hmn
      subst hn1
      change f.lCoeff (0 * 1) = f.lCoeff 0 * f.lCoeff 1
      rw [Nat.zero_mul, f.lCoeff_zero, zero_mul]
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · have hm1 : m = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_right] at hmn
        subst hm1
        change f.lCoeff (1 * 0) = f.lCoeff 1 * f.lCoeff 0
        rw [Nat.mul_zero, f.lCoeff_zero, mul_zero]
      · exact f.lCoeff_mul_of_coprime m n hm hn hmN hnN hmn χ hfχ
  recur := f.lCoeff_recur χ hfχ

/-- **Bridge to `ModularForms.lCoeff`.**  The `Newform.lCoeff` sequence is
the same as the generic `ModularForms.lCoeff f.toCuspForm` sequence built
from the strict-width-at-`∞` `q`-expansion. -/
lemma Newform.lCoeff_eq_modularForms_lCoeff (f : Newform N k) (n : ℕ) :
    f.lCoeff n = ModularForms.lCoeff f.toCuspForm n := by
  rw [Newform.lCoeff_apply,
    ← ModularForms.lCoeff_Gamma1_mapGL_eq (N := N) (k := k) (F := CuspForm _ k)
      f.toCuspForm n]

/-- Function-level form of `Newform.lCoeff_eq_modularForms_lCoeff`. -/
lemma Newform.lCoeff_eq_modularForms_lCoeff_funext (f : Newform N k) :
    f.lCoeff = ModularForms.lCoeff f.toCuspForm :=
  funext (Newform.lCoeff_eq_modularForms_lCoeff f)

/-- **Absolute summability** of the Dirichlet series `LSeries f.lCoeff` on
the half-plane `Re s > k/2 + 1`. -/
lemma Newform.lSeriesSummable (f : Newform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable f.lCoeff s := by
  rw [Newform.lCoeff_eq_modularForms_lCoeff_funext]
  exact ModularForms.lSeriesSummable_of_cuspForm
    (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (F := CuspForm _ k) f.toCuspForm hs

/-- **L-series injectivity for newforms.**  Two newforms have the same
Dirichlet L-series iff their `lCoeff` sequences agree at every positive
index. -/
lemma Newform.lSeries_eq_iff (f g : Newform N k) :
    LSeries f.lCoeff = LSeries g.lCoeff ↔ ∀ n ≠ 0, f.lCoeff n = g.lCoeff n := by
  rw [Newform.lCoeff_eq_modularForms_lCoeff_funext f,
      Newform.lCoeff_eq_modularForms_lCoeff_funext g]
  exact ModularForms.lSeries_eq_iff_cuspForm
    (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k)
    (F := CuspForm _ k) (F' := CuspForm _ k) f.toCuspForm g.toCuspForm

/-- **L-series non-vanishing** for a newform: since `f.lCoeff 1 = 1 ≠ 0`,
the Dirichlet series `LSeries f.lCoeff` is not identically zero. -/
lemma Newform.lSeries_ne_zero (f : Newform N k) :
    LSeries f.lCoeff ≠ 0 := by
  rw [Newform.lCoeff_eq_modularForms_lCoeff_funext]
  apply ModularForms.lSeries_ne_zero_of_lCoeff_ne_zero
    (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (F := CuspForm _ k)
    (f := f.toCuspForm)
  intro habs
  have h1 : ModularForms.lCoeff f.toCuspForm 1 = 0 := by rw [habs]; rfl
  rw [← Newform.lCoeff_eq_modularForms_lCoeff f 1, Newform.lCoeff_one] at h1
  exact one_ne_zero h1

/-- **Stripped Newform Fourier sequence.**  `n ↦ f.lCoeff n` if `n` is
coprime to `N`, else `0`.  Unlike `f.lCoeff` this is fully multiplicative
on coprime arguments, as required by the Mathlib Euler-product machinery. -/
noncomputable def Newform.lCoeff_stripped (f : Newform N k) (n : ℕ) : ℂ :=
  if n.Coprime N then f.lCoeff n else 0

@[simp]
lemma Newform.lCoeff_stripped_zero (f : Newform N k) :
    f.lCoeff_stripped 0 = 0 := by
  unfold lCoeff_stripped
  split_ifs with h
  · exact f.lCoeff_zero
  · rfl

@[simp]
lemma Newform.lCoeff_stripped_one (f : Newform N k) :
    f.lCoeff_stripped 1 = 1 := by
  unfold lCoeff_stripped
  rw [if_pos (Nat.coprime_one_left N), f.lCoeff_one]

/-- **Pointwise norm domination**: `|f.lCoeff_stripped n| ≤ |f.lCoeff n|`
for every `n`. -/
lemma Newform.norm_lCoeff_stripped_le (f : Newform N k) (n : ℕ) :
    ‖f.lCoeff_stripped n‖ ≤ ‖f.lCoeff n‖ := by
  unfold lCoeff_stripped
  split_ifs
  · exact le_refl _
  · simp

/-- **Full coprime multiplicativity** of the stripped sequence: for
arbitrary `m, n` coprime to each other (not requiring coprime to `N`),
`f.lCoeff_stripped (m * n) = f.lCoeff_stripped m * f.lCoeff_stripped n`. -/
lemma Newform.lCoeff_stripped_mul_coprime (f : Newform N k)
    {m n : ℕ} (hmn : Nat.Coprime m n)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.lCoeff_stripped (m * n) = f.lCoeff_stripped m * f.lCoeff_stripped n := by
  unfold lCoeff_stripped
  by_cases hmn_cop : (m * n).Coprime N
  · rw [if_pos hmn_cop]
    have ⟨hmN, hnN⟩ := Nat.coprime_mul_iff_left.mp hmn_cop
    rw [if_pos hmN, if_pos hnN]
    rcases Nat.eq_zero_or_pos m with rfl | hm_pos
    · have hn1 : n = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_left] at hmn
      subst hn1
      change f.lCoeff (0 * 1) = f.lCoeff 0 * f.lCoeff 1
      rw [Nat.zero_mul, f.lCoeff_zero, zero_mul]
    · rcases Nat.eq_zero_or_pos n with rfl | hn_pos
      · have hm1 : m = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_right] at hmn
        subst hm1
        change f.lCoeff (1 * 0) = f.lCoeff 1 * f.lCoeff 0
        rw [Nat.mul_zero, f.lCoeff_zero, mul_zero]
      · exact f.lCoeff_mul_of_coprime m n hm_pos hn_pos hmN hnN hmn χ hf_char
  · rw [if_neg hmn_cop]
    rw [Nat.coprime_mul_iff_left, not_and_or] at hmn_cop
    rcases hmn_cop with hm_not | hn_not
    · rw [if_neg hm_not, zero_mul]
    · rw [if_neg hn_not, mul_zero]

/-- **Stripped L-series summability.**  The stripped sequence's
L-series is summable on the same half-plane `Re s > k/2 + 1` as the
full `Newform.lCoeff` L-series, by pointwise domination. -/
lemma Newform.lSeriesSummable_stripped (f : Newform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable f.lCoeff_stripped s := by
  refine Summable.of_norm_bounded (g := fun n ↦ ‖LSeries.term f.lCoeff s n‖)
    (f.lSeriesSummable hs).norm ?_
  intro n
  exact LSeries.norm_term_le s (f.norm_lCoeff_stripped_le n)

/-- **Cusp-form abscissa bound for the stripped coefficient sequence.**
The abscissa of absolute convergence of `f.lCoeff_stripped` is at most
`(k : ℝ) / 2 + 1`, the standard Hecke / cusp-form bound (Diamond–Shurman
§5.9 / Miyake §4.3.5). -/
lemma Newform.abscissaOfAbsConv_lCoeff_stripped_le_cuspForm
    (f : Newform N k) :
    LSeries.abscissaOfAbsConv f.lCoeff_stripped ≤ (((k : ℝ) / 2 + 1 : ℝ) : EReal) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' ?_
  intro y hy
  refine f.lSeriesSummable_stripped ?_
  have hy_real : (k : ℝ) / 2 + 1 < y := by exact_mod_cast hy
  show (k : ℝ) / 2 + 1 < ((y : ℝ) : ℂ).re
  simpa using hy_real

/-- **Per-prime local Euler factor at a vanishing prime.**  For a `Newform`
`f` in `modFormCharSpace k χ` and a prime `q` coprime to the level with
`f.lCoeff q = 0`, the local Euler factor collapses to a quadratic reciprocal
`∑ᵣ f.lCoeff (qʳ) · xʳ = (1 + χ(q) · q^{k-1} · x²)⁻¹`, provided
`‖χ(q) · q^{k-1} · x²‖ < 1` (Diamond–Shurman §5.9, Miyake §4.5.16). -/
theorem Newform.tsum_lCoeff_pow_mul_eq_eulerFactor (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    {q : ℕ} (hq : q.Prime) (hqN : Nat.Coprime q N) (h_zero : f.lCoeff q = 0)
    (x : ℂ)
    (hs : ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) * x ^ 2‖ < 1) :
    ∑' (r : ℕ), f.lCoeff (q ^ r) * x ^ r =
      (1 + (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) * x ^ 2)⁻¹ := by
  have h_seq : IsHeckeCoefficientSequence N k χ f.lCoeff :=
    f.lCoeff_isHeckeCoefficientSequence χ hfχ
  have h_pointwise : ∀ r : ℕ,
      f.lCoeff (q ^ r) * x ^ r =
        (if r % 2 = 0 then
            ((-((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1))) ^ (r / 2) * x ^ r)
          else 0) := by
    intro r
    rw [h_seq.coeff_prime_pow_eq_of_a_p_zero hq hqN h_zero r]
    rcases Nat.even_or_odd r with hr | hr
    · rw [if_pos hr, if_pos (Nat.even_iff.mp hr)]
      ring
    · have h_not : ¬ Even r := Nat.not_even_iff_odd.mpr hr
      have h_mod : r % 2 ≠ 0 := fun heq ↦ h_not (Nat.even_iff.mpr heq)
      rw [if_neg h_not, if_neg h_mod, zero_mul]
  rw [tsum_congr h_pointwise]
  exact ModularForms.tsum_alternating_pow_eq
    ((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) x hs

/-- **Global Euler product** for the stripped Newform Fourier sequence.
The Dirichlet series `LSeries f.lCoeff_stripped` factorises as a product of
local Euler factors `∑ᵣ (LSeries.term f.lCoeff_stripped s) (pʳ)` over the
primes, on the half-plane of absolute convergence `Re s > k/2 + 1`. -/
theorem Newform.lSeries_stripped_hasProd (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦
        ∑' (e : ℕ), LSeries.term f.lCoeff_stripped s ((p : ℕ) ^ e))
      (LSeries f.lCoeff_stripped s) := by
  have h_zero : LSeries.term f.lCoeff_stripped s 0 = 0 := rfl
  have h_one : LSeries.term f.lCoeff_stripped s 1 = 1 := by
    rw [LSeries.term_def, if_neg one_ne_zero, f.lCoeff_stripped_one,
      Nat.cast_one, Complex.one_cpow, div_one]
  have h_mul : ∀ {m n : ℕ}, m.Coprime n →
      LSeries.term f.lCoeff_stripped s (m * n) =
        LSeries.term f.lCoeff_stripped s m * LSeries.term f.lCoeff_stripped s n := by
    intro m n hmn
    rw [LSeries.term_def₀ f.lCoeff_stripped_zero,
      LSeries.term_def₀ f.lCoeff_stripped_zero,
      LSeries.term_def₀ f.lCoeff_stripped_zero,
      f.lCoeff_stripped_mul_coprime hmn χ hfχ]
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  exact EulerProduct.eulerProduct_hasProd h_one h_mul
    (f.lSeriesSummable_stripped hs).norm h_zero

/-- **Trivial local Euler factor at a prime dividing the level.**  For a
prime `p | N`, the stripped sequence vanishes at every positive power
`p ^ (e + 1)` (since `p ^ (e + 1)` shares the factor `p` with `N`),
so the local Euler factor reduces to the `e = 0` term, which is `1`. -/
theorem Newform.tsum_term_lCoeff_stripped_pow_of_dvd (f : Newform N k)
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ N) (s : ℂ) :
    ∑' (e : ℕ), LSeries.term f.lCoeff_stripped s (p ^ e) = 1 := by
  have h_term_zero : ∀ e, e ≥ 1 →
      LSeries.term f.lCoeff_stripped s (p ^ e) = 0 := by
    intro e he_pos
    rw [LSeries.term_def, if_neg (pow_pos hp.pos e).ne']
    have h_not_cop : ¬ Nat.Coprime (p ^ e) N := by
      intro h_cop
      have h_p_cop : Nat.Coprime p N := Nat.Coprime.coprime_dvd_left
        (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp he_pos)) h_cop
      rw [Nat.Coprime, Nat.gcd_eq_left hp_dvd] at h_p_cop
      exact hp.one_lt.ne' h_p_cop
    rw [show f.lCoeff_stripped (p ^ e) = 0 from if_neg h_not_cop, zero_div]
  rw [tsum_eq_single 0 fun e he_ne_zero ↦
      h_term_zero e (Nat.one_le_iff_ne_zero.mpr he_ne_zero),
    pow_zero, LSeries.term_def, if_neg one_ne_zero, f.lCoeff_stripped_one,
    Nat.cast_one, Complex.one_cpow, div_one]

/-- **Local Euler factor at a "good" prime.**  For a prime `q` coprime to
the level with `f.lCoeff q = 0`, the local Euler factor in the stripped
Dirichlet series collapses to the explicit Dirichlet-quotient form
`(1 + χ(q) · q^{k-1-2s})⁻¹`. -/
theorem Newform.tsum_term_lCoeff_stripped_pow_of_good_prime (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    {q : ℕ} (hq : q.Prime) (hqN : Nat.Coprime q N) (h_zero : f.lCoeff q = 0)
    (s : ℂ)
    (hs : ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-s)) ^ 2‖ < 1) :
    ∑' (e : ℕ), LSeries.term f.lCoeff_stripped s (q ^ e) =
      (1 + (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) *
        ((q : ℂ) ^ (-s)) ^ 2)⁻¹ := by
  have h_strip_eq : ∀ e, f.lCoeff_stripped (q ^ e) = f.lCoeff (q ^ e) := fun e ↦ by
    unfold Newform.lCoeff_stripped
    exact if_pos (hqN.pow_left e)
  have h_term : ∀ e, LSeries.term f.lCoeff_stripped s (q ^ e) =
      f.lCoeff (q ^ e) * ((q : ℂ) ^ (-s)) ^ e := by
    intro e
    rw [LSeries.term_def₀ f.lCoeff_stripped_zero, h_strip_eq e]
    push_cast
    rw [← Complex.natCast_cpow_natCast_mul q e (-s),
      show ((e : ℂ) * (-s)) = (-s) * (e : ℂ) from by ring, Complex.cpow_mul_nat]
  rw [tsum_congr h_term]
  exact f.tsum_lCoeff_pow_mul_eq_eulerFactor χ hfχ hq hqN h_zero ((q : ℂ) ^ (-s)) hs

/-- **Identified local Euler factor** at a prime `p` for the
`Newform.lCoeff_stripped` Dirichlet series under the bad-primes-zero
hypothesis.  Three cases:

* `p ∣ N`: trivial factor `1`.
* `p ∈ S` and `p` coprime to `N`: residual local factor
  `∑ᵣ LSeries.term f.lCoeff_stripped s (pʳ)`.
* `p ∉ S` and `p` coprime to `N` ("good" prime, where `f.lCoeff p = 0`):
  explicit Dirichlet-quotient form `(1 + χ(p) · p^{k-1} · (p^{-s})²)⁻¹`. -/
noncomputable def Newform.eulerFactor_stripped (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ) (S : Finset ℕ) (s : ℂ) (p : Nat.Primes) : ℂ :=
  if h_dvd : (p : ℕ) ∣ N then 1
  else
    have hpN : Nat.Coprime (p : ℕ) N :=
      (Nat.Prime.coprime_iff_not_dvd p.prop).mpr h_dvd
    if (p : ℕ) ∈ S then
      ∑' (e : ℕ), LSeries.term f.lCoeff_stripped s ((p : ℕ) ^ e)
    else
      (1 + (χ (ZMod.unitOfCoprime (p : ℕ) hpN) : ℂ) *
         ((p : ℕ) : ℂ) ^ (k - 1) * (((p : ℕ) : ℂ) ^ (-s)) ^ 2)⁻¹

/-- **Combined Dirichlet quotient identification.**  Under the
bad-primes-zero hypothesis (`f.lCoeff q = 0` for every prime `q`
coprime to `N`, `q ∉ S`), the stripped Newform L-series factorises as
the convergent product over `Nat.Primes` of the identified local
factors `Newform.eulerFactor_stripped`.  The hypothesis `h_geom`
packages the geometric-series convergence condition at each good prime. -/
theorem Newform.lSeries_stripped_hasProd_eulerFactor
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re)
    (h_geom : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-s)) ^ 2‖ < 1) :
    HasProd (Newform.eulerFactor_stripped f χ S s)
      (LSeries f.lCoeff_stripped s) := by
  refine (f.lSeries_stripped_hasProd χ hfχ hs).congr_fun ?_
  intro p
  unfold Newform.eulerFactor_stripped
  by_cases h_dvd : (p : ℕ) ∣ N
  · rw [dif_pos h_dvd]
    exact (f.tsum_term_lCoeff_stripped_pow_of_dvd p.prop h_dvd s).symm
  · rw [dif_neg h_dvd]
    have hpN : Nat.Coprime (p : ℕ) N :=
      (Nat.Prime.coprime_iff_not_dvd p.prop).mpr h_dvd
    by_cases h_S : (p : ℕ) ∈ S
    · rw [if_pos h_S]
    · rw [if_neg h_S]
      exact (f.tsum_term_lCoeff_stripped_pow_of_good_prime χ hfχ p.prop hpN
        (h_bad _ p.prop hpN h_S) s (h_geom _ p.prop hpN h_S)).symm

/-- **Dirichlet character lift.**  The Newform character
`χ : (ZMod N)ˣ →* ℂˣ` lifts to a Mathlib `DirichletCharacter ℂ N` via
the canonical extension by zero on non-units (`MulChar.ofUnitHom`). -/
noncomputable def Newform.dirichletLift (χ : (ZMod N)ˣ →* ℂˣ) :
    DirichletCharacter ℂ N := MulChar.ofUnitHom χ

omit [NeZero N] in
@[simp]
lemma Newform.dirichletLift_apply_unit (χ : (ZMod N)ˣ →* ℂˣ) (a : (ZMod N)ˣ) :
    (Newform.dirichletLift χ) (a : ZMod N) = (χ a : ℂ) :=
  MulChar.ofUnitHom_coe χ a

omit [NeZero N] in
/-- **Norm of a character value at a unit equals 1**: the image `χ a : ℂˣ`
is a finite-order unit in ℂ, hence a root of unity. -/
lemma Newform.norm_chi_unit_eq_one [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
    (a : (ZMod N)ˣ) :
    ‖((χ a : ℂˣ) : ℂ)‖ = 1 := by
  have h_pow : (χ a) ^ Fintype.card ((ZMod N)ˣ) = 1 := by
    rw [← map_pow]; convert map_one χ; exact pow_card_eq_one
  have h_pow_C : ((χ a : ℂˣ) : ℂ) ^ Fintype.card ((ZMod N)ˣ) = 1 := by
    rw [show ((χ a : ℂˣ) : ℂ) ^ Fintype.card ((ZMod N)ˣ) =
        (((χ a) ^ Fintype.card ((ZMod N)ˣ) : ℂˣ) : ℂ) from by push_cast; rfl,
      h_pow, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h_pow_C Fintype.card_pos.ne'

omit [NeZero N] in
/-- **Geometric convergence of the good-prime Euler factor argument.**  For
any prime `q ≥ 2` coprime to `N` and `s ∈ ℂ` with `Re s > (k-1)/2`, the
geometric ratio `χ(q) · q^{k-1} · (q^{-s})²` has norm `< 1`. -/
lemma Newform.norm_eulerFactor_argument_lt_one [NeZero N]
    (χ : (ZMod N)ˣ →* ℂˣ) (k : ℤ)
    {q : ℕ} (hq : 2 ≤ q) (hqN : Nat.Coprime q N)
    (s : ℂ) (hs : ((k : ℝ) - 1) / 2 < s.re) :
    ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ)) * (q : ℂ) ^ (k - 1) *
      ((q : ℂ) ^ (-s)) ^ 2‖ < 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hq
  rw [norm_mul, norm_mul, norm_pow,
    Newform.norm_chi_unit_eq_one χ (ZMod.unitOfCoprime q hqN), one_mul,
    show ((q : ℂ) ^ (-s)) = ((q : ℝ) : ℂ) ^ (-s) from by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hq_pos,
    show ((q : ℂ) ^ (k - 1)) = ((q : ℝ) : ℂ) ^ (k - 1) from by push_cast; rfl,
    show (((q : ℝ) : ℂ) ^ (k - 1)) = ((q : ℝ) : ℂ) ^ ((k - 1 : ℤ) : ℂ) from by
      rw [Complex.cpow_intCast],
    Complex.norm_cpow_eq_rpow_re_of_pos hq_pos,
    show (-s).re = -s.re from by simp,
    show ((k - 1 : ℤ) : ℂ).re = (k - 1 : ℤ) from by simp,
    show (((q : ℝ) ^ (-s.re : ℝ)) ^ 2) = (q : ℝ) ^ ((-s.re) * 2) from by
      rw [← Real.rpow_natCast ((q : ℝ) ^ (-s.re : ℝ)) 2, ← Real.rpow_mul hq_pos.le]
      norm_num,
    ← Real.rpow_add hq_pos,
    show ((↑(k - 1 : ℤ) : ℝ) + (-s.re) * 2) = ((k : ℝ) - 1) - 2 * s.re from by
      push_cast; ring]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (by linarith)

/-- **Algebraic Dirichlet-quotient rewrite of the good-prime Euler
factor.**  The local Euler factor `(1 + x)⁻¹` decomposes as the ratio
`(1 - x) · (1 - x²)⁻¹`, exhibiting the formal Dirichlet-quotient shape
`1/L(s', χ̃) · L(2s', χ̃²)` at each prime.  Requires `1 ± x ≠ 0`. -/
lemma Newform.eulerFactor_dirichlet_quotient_form (x : ℂ)
    (hx_pos : (1 : ℂ) + x ≠ 0) (hx_neg : (1 : ℂ) - x ≠ 0) :
    (1 + x)⁻¹ = (1 - x) * (1 - x ^ 2)⁻¹ := by
  have hx_sq : (1 : ℂ) - x ^ 2 ≠ 0 := by
    rw [show (1 : ℂ) - x ^ 2 = (1 - x) * (1 + x) from by ring]
    exact mul_ne_zero hx_neg hx_pos
  field_simp
  ring

/-- **Stripped L-series non-vanishing.**  The Dirichlet series for
`f.lCoeff_stripped` is not identically zero, since
`f.lCoeff_stripped 1 = 1 ≠ 0`. -/
lemma Newform.lSeries_stripped_ne_zero (f : Newform N k) :
    LSeries f.lCoeff_stripped ≠ 0 := by
  have h_lCoeff_ne : f.lCoeff_stripped ≠ 0 := fun habs ↦ by
    have h1 : f.lCoeff_stripped 1 = 0 := by rw [habs]; rfl
    rw [f.lCoeff_stripped_one] at h1
    exact one_ne_zero h1
  have h_abscissa_lt_top : LSeries.abscissaOfAbsConv f.lCoeff_stripped < ⊤ := by
    have h_summ : LSeriesSummable f.lCoeff_stripped (((k : ℝ) / 2 + 2 : ℝ) : ℂ) :=
      f.lSeriesSummable_stripped (by simp)
    exact lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le h_summ) (EReal.coe_lt_top _)
  intro habs
  rcases (LSeries_eq_zero_iff f.lCoeff_stripped_zero).mp habs with h | h
  · exact h_lCoeff_ne h
  · exact h_abscissa_lt_top.ne h

/-- **Local good-prime Euler factor as a Dirichlet quotient.**  For a
prime `q` coprime to `N` with `f.lCoeff q = 0`, the local Euler factor
`(1 + χ(q) · q^{k-1} · (q^{-s})²)⁻¹` coincides with the Dirichlet-quotient
form `(1 - χ(q) · q^{-s'}) · (1 - χ²(q) · q^{-2s'})⁻¹` at `s' = 2s - k + 1`.
Hypotheses `h_pos`, `h_neg` ensure `1 ± x ≠ 0`. -/
theorem Newform.eulerFactor_good_prime_eq_dirichlet_quotient
    {q : ℕ} (hq_pos : 0 < q) (k : ℤ) (s : ℂ) (χ : ℂ)
    (h_pos : (1 : ℂ) + χ * (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0)
    (h_neg : (1 : ℂ) - χ * (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0) :
    (1 + χ * (q : ℂ) ^ (k - 1) * ((q : ℂ) ^ (-s)) ^ 2)⁻¹ =
      (1 - χ * (q : ℂ) ^ (-(2 * s - k + 1))) *
      (1 - χ ^ 2 * (q : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ := by
  have hq_ne : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq_pos.ne'
  have h_pow : (q : ℂ) ^ (k - 1) * ((q : ℂ) ^ (-s)) ^ 2 =
      (q : ℂ) ^ (-(2 * s - k + 1)) := by
    rw [show ((q : ℂ) ^ (-s)) ^ 2 = (q : ℂ) ^ (-s * 2) from by
        rw [← Complex.cpow_mul_nat]; rfl,
      show ((q : ℂ) ^ (k - 1) : ℂ) = (q : ℂ) ^ ((k - 1 : ℤ) : ℂ) from
        (Complex.cpow_intCast _ _).symm,
      ← Complex.cpow_add _ _ hq_ne]
    congr 1; push_cast; ring
  have h_sq : (χ ^ 2 : ℂ) * (q : ℂ) ^ (-(2 * (2 * s - k + 1))) =
      (χ * (q : ℂ) ^ (-(2 * s - k + 1))) ^ 2 := by
    rw [mul_pow,
      show ((q : ℂ) ^ (-(2 * s - k + 1))) ^ 2 = (q : ℂ) ^ (-(2 * s - k + 1) * 2) from by
        rw [← Complex.cpow_mul_nat]; rfl]
    congr 2; ring
  rw [show (1 + χ * (q : ℂ) ^ (k - 1) * ((q : ℂ) ^ (-s)) ^ 2 : ℂ) =
      1 + χ * ((q : ℂ) ^ (k - 1) * ((q : ℂ) ^ (-s)) ^ 2) from by ring,
    h_pow, h_sq]
  exact Newform.eulerFactor_dirichlet_quotient_form
    (χ * (q : ℂ) ^ (-(2 * s - k + 1))) h_pos h_neg

/-- **Compound HasProd identity** combining the stripped Euler product
with the Mathlib Dirichlet Euler product for the lifted character
`χ̃ = dirichletLift χ` at the substituted point `s' = 2s - k + 1`.

This is the global bridge consumed by the final Dirichlet-quotient
contradiction: at good primes the compound factor reduces to the Mathlib
χ̃² Euler factor `(1 - χ̃²(p) · p^{-2s'})⁻¹`; at `p ∣ N` both factors are
`1`; at `p ∈ S` coprime to `N` the compound is the finite "S correction". -/
theorem Newform.lSeries_stripped_mul_dirichlet_hasProd
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re)
    (hs' : 1 < (2 * s - k + 1).re)
    (h_geom : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-s)) ^ 2‖ < 1) :
    HasProd
      (fun p : Nat.Primes ↦
        Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹)
      (LSeries f.lCoeff_stripped s *
        LSeries (fun n ↦ (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1)) :=
  (f.lSeries_stripped_hasProd_eulerFactor χ hfχ S h_bad hs h_geom).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) hs')

/-- **Pointwise factor identification at good primes.**  The compound
factor `eulerFactor_stripped p · (1 - χ̃(p) · p^{-s'})⁻¹` reduces, at every
prime `q.Prime` coprime to `N` with `q ∉ S` and `f.lCoeff q = 0`, to
the Mathlib χ̃² Euler factor `(1 - χ̃²(q) · q^{-2s'})⁻¹`. -/
theorem Newform.eulerFactor_stripped_mul_dirichlet_at_good_prime
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (_hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (_h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    {q : ℕ} (hq : q.Prime) (hqN : Nat.Coprime q N) (hqS : q ∉ S)
    (s : ℂ)
    (h_pos : (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0)
    (h_neg : (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0) :
    Newform.eulerFactor_stripped f χ S s ⟨q, hq⟩ *
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((q : ℕ) : ZMod N) *
        ((q : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹ =
      (1 - ((Newform.dirichletLift χ : DirichletCharacter ℂ N) ((q : ℕ) : ZMod N)) ^ 2 *
        ((q : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ := by
  unfold Newform.eulerFactor_stripped
  rw [dif_neg (fun h_div ↦ absurd ((Nat.Prime.coprime_iff_not_dvd hq).mp hqN)
        (not_not.mpr h_div)),
    if_neg hqS,
    Newform.eulerFactor_good_prime_eq_dirichlet_quotient hq.pos k s
      (χ (ZMod.unitOfCoprime q hqN) : ℂ) h_pos h_neg,
    show (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((q : ℕ) : ZMod N) =
        (χ (ZMod.unitOfCoprime q hqN) : ℂ) by
      rw [show (((q : ℕ) : ZMod N)) =
          ((ZMod.unitOfCoprime q hqN : (ZMod N)ˣ) : ZMod N) from by
        simp [ZMod.coe_unitOfCoprime]]
      exact MulChar.ofUnitHom_coe χ (ZMod.unitOfCoprime q hqN)]
  field_simp

/-- **Pointwise factor identification at primes dividing the level.**  For
a prime `p ∣ N`, the compound factor `eulerFactor_stripped p · (1 - χ̃(p) ·
p^{-s'})⁻¹` equals `1`, since `eulerFactor_stripped p = 1` and `χ̃(p) = 0`. -/
theorem Newform.eulerFactor_stripped_mul_dirichlet_at_dvd (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ) (S : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ N) (s : ℂ) :
    Newform.eulerFactor_stripped f χ S s ⟨p, hp⟩ *
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹ = 1 := by
  unfold Newform.eulerFactor_stripped
  rw [dif_pos hp_dvd,
    show (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) = 0 by
      apply (Newform.dirichletLift χ : DirichletCharacter ℂ N).map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      exact fun h_cop ↦ (hp.coprime_iff_not_dvd.mp h_cop) hp_dvd,
    zero_mul, sub_zero, inv_one, mul_one]

omit [NeZero N] in
/-- **Pointwise factor identification at primes dividing the level
(squared character).**  For a prime `p ∣ N`, the squared Mathlib
χ̃² Euler factor `(1 - χ̃²(p) · p^{-2s'})⁻¹` equals `1`. -/
theorem Newform.dirichletLift_sq_euler_factor_at_dvd (χ : (ZMod N)ˣ →* ℂˣ)
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ N) (s : ℂ) :
    (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ = 1 := by
  rw [show ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) =
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) from
        MulChar.mul_apply _ _ _,
    show (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) = 0 by
      apply (Newform.dirichletLift χ : DirichletCharacter ℂ N).map_nonunit
      rw [ZMod.isUnit_iff_coprime]
      exact fun h_cop ↦ (hp.coprime_iff_not_dvd.mp h_cop) hp_dvd,
    mul_zero, zero_mul, sub_zero, inv_one]

private lemma hasProd_mul_finset_prod_comm {ι : Type*} {g₁ g₂ : ι → ℂ} {a b : ℂ}
    (h₁ : HasProd g₁ a) (h₂ : HasProd g₂ b) (T : Finset ι)
    (h_eq : ∀ p ∉ T, g₁ p = g₂ p) :
    a * ∏ p ∈ T, g₂ p = b * ∏ p ∈ T, g₁ p := by
  classical
  let corr₁ : ι → ℂ := fun p ↦ if p ∈ T then g₂ p else 1
  let corr₂ : ι → ℂ := fun p ↦ if p ∈ T then g₁ p else 1
  have h_corr₁_prod : HasProd corr₁ (∏ p ∈ T, corr₁ p) :=
    hasProd_prod_of_ne_finset_one fun p hp ↦ if_neg hp
  have h_corr₂_prod : HasProd corr₂ (∏ p ∈ T, corr₂ p) :=
    hasProd_prod_of_ne_finset_one fun p hp ↦ if_neg hp
  have h_corr₁_eq : (∏ p ∈ T, corr₁ p) = ∏ p ∈ T, g₂ p :=
    Finset.prod_congr rfl fun p hp ↦ if_pos hp
  have h_corr₂_eq : (∏ p ∈ T, corr₂ p) = ∏ p ∈ T, g₁ p :=
    Finset.prod_congr rfl fun p hp ↦ if_pos hp
  have h_left : HasProd (fun p ↦ g₁ p * corr₁ p) (a * ∏ p ∈ T, corr₁ p) :=
    h₁.mul h_corr₁_prod
  have h_right : HasProd (fun p ↦ g₂ p * corr₂ p) (b * ∏ p ∈ T, corr₂ p) :=
    h₂.mul h_corr₂_prod
  have h_pointwise : (fun p ↦ g₁ p * corr₁ p) = (fun p ↦ g₂ p * corr₂ p) := by
    funext p
    by_cases hp : p ∈ T
    · show g₁ p * (if p ∈ T then g₂ p else 1) = g₂ p * (if p ∈ T then g₁ p else 1)
      rw [if_pos hp, if_pos hp]; ring
    · show g₁ p * (if p ∈ T then g₂ p else 1) = g₂ p * (if p ∈ T then g₁ p else 1)
      rw [if_neg hp, if_neg hp, mul_one, mul_one]
      exact h_eq p hp
  rw [h_pointwise] at h_left
  have h_unique := h_left.unique h_right
  rwa [h_corr₁_eq, h_corr₂_eq] at h_unique

private lemma Newform.eulerFactor_stripped_mul_dirichlet_eq_chiSq_factor_of_not_mem
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    {s : ℂ} (T : Finset Nat.Primes)
    (hT_iff : ∀ p : Nat.Primes, p ∈ T ↔
      (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N)
    (h_pos_neg : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 ∧
      (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0)
    {p : Nat.Primes} (hp_notT : p ∉ T) :
    Newform.eulerFactor_stripped f χ S s p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹ =
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ := by
  have h_p_eq : Newform.eulerFactor_stripped f χ S s p =
      Newform.eulerFactor_stripped f χ S s ⟨(p : ℕ), p.prop⟩ := by
    rw [Subtype.eta _ _]
  by_cases h_dvd : (p : ℕ) ∣ N
  · rw [h_p_eq, Newform.eulerFactor_stripped_mul_dirichlet_at_dvd f χ S p.prop h_dvd s,
      Newform.dirichletLift_sq_euler_factor_at_dvd χ p.prop h_dvd s]
  · have hpN : Nat.Coprime (p : ℕ) N :=
      (Nat.Prime.coprime_iff_not_dvd p.prop).mpr h_dvd
    have hp_notS : (p : ℕ) ∉ S := fun hpS ↦ hp_notT ((hT_iff p).mpr ⟨hpS, hpN⟩)
    obtain ⟨h_pos, h_neg⟩ := h_pos_neg (p : ℕ) p.prop hpN hp_notS
    rw [h_p_eq,
      f.eulerFactor_stripped_mul_dirichlet_at_good_prime χ hfχ S h_bad p.prop hpN
        hp_notS s h_pos h_neg,
      show ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) =
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) ^ 2 from by
          rw [pow_two]; exact MulChar.mul_apply _ _ _]

/-- **Final value identity.**  Under the bad-prime-zero hypothesis
(`f.lCoeff q = 0` for every prime `q.Coprime N` with `q ∉ S`), the
compound HasProd identifies against the Mathlib χ̃² Dirichlet Euler
product, with the discrepancy at `S`-primes captured as an explicit
Finset correction over `T : Finset Nat.Primes` (the primes in `S` coprime
to `N`, characterised by `hT_iff`).  This is the algebraic value identity
of Diamond–Shurman §5.9 / Miyake §4.5.16, with the analytic ingredients
supplied as hypotheses. -/
theorem Newform.lSeries_stripped_value_identity
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re)
    (hs' : 1 < (2 * s - k + 1).re)
    (hs'' : 1 < (2 * (2 * s - k + 1)).re)
    (h_geom : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-s)) ^ 2‖ < 1)
    (T : Finset Nat.Primes)
    (hT_iff : ∀ p : Nat.Primes, p ∈ T ↔
      (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N)
    (h_pos_neg : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 ∧
      (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0) :
    (LSeries f.lCoeff_stripped s) *
        (LSeries (fun n ↦
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) n) (2 * s - k + 1)) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) =
      (LSeries (fun n ↦ ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) n) (2 * (2 * s - k + 1))) *
        (∏ p ∈ T,
          Newform.eulerFactor_stripped f χ S s p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) := by
  have h_compound :=
    f.lSeries_stripped_mul_dirichlet_hasProd χ hfχ S h_bad hs hs' h_geom
  have h_chi_sq := DirichletCharacter.LSeries_eulerProduct_hasProd
    ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) hs''
  exact hasProd_mul_finset_prod_comm h_compound h_chi_sq T fun p hp_notT ↦
    f.eulerFactor_stripped_mul_dirichlet_eq_chiSq_factor_of_not_mem χ hfχ S h_bad T
      hT_iff h_pos_neg hp_notT

/-- **Local Dirichlet Euler factor non-vanishing.**  For a Mathlib
`DirichletCharacter ℂ N`, every prime `p`, and every `s' ∈ ℂ` with
`Re s' > 1`, the local Euler factor `(1 - χ(p) · p^{-s'})⁻¹` is non-zero. -/
lemma Newform.dirichletLift_eulerFactor_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) {s' : ℂ}
    (hs' : 1 < s'.re) :
    (1 - χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s'))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  have hp_pos : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have h_norm : ‖χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s')‖ < 1 := by
    rw [norm_mul,
      show ‖((p : ℕ) : ℂ) ^ (-s')‖ = (p : ℝ) ^ (-s'.re) by
        rw [show ((p : ℕ) : ℂ) ^ (-s') = ((p : ℝ) : ℂ) ^ (-s') from by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos (lt_trans one_pos hp_pos)]
        simp]
    calc ‖χ ((p : ℕ) : ZMod N)‖ * (p : ℝ) ^ (-s'.re)
        ≤ 1 * (p : ℝ) ^ (-s'.re) := by
          apply mul_le_mul_of_nonneg_right (DirichletCharacter.norm_le_one χ _); positivity
      _ = (p : ℝ) ^ (-s'.re) := one_mul _
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_pos (by linarith)
  intro h_eq
  rw [show χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s') = 1 by
    rw [sub_eq_zero.mp h_eq]] at h_norm
  simp at h_norm

/-- **Finite product of χ̃² Mathlib-Dirichlet local Euler factors over a
finite Finset of primes is non-zero**, on `Re s' > 1`. -/
lemma Newform.prod_dirichletLift_sq_eulerFactor_ne_zero
    (χ : (ZMod N)ˣ →* ℂˣ) (T : Finset Nat.Primes) {s : ℂ}
    (hs'' : 1 < (2 * (2 * s - k + 1)).re) :
    (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
      DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p _
  exact Newform.dirichletLift_eulerFactor_ne_zero
    (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
    p.prop hs''

/-- **Divided form of the value identity.**  Combining the value identity
with non-vanishing of `LSeries χ̃ s'` and of the finite χ̃² Euler product
correction, the cusp-form L-series is explicitly determined by the
Dirichlet quotient modulo the finite `S`-correction.

Math caveat: this single-point value identity does not by itself yield
`Newform.exists_nonzero_prime_eigenvalue`; the classical contradiction
(Diamond–Shurman §5.9 / Miyake Thm 4.5.16) requires Hecke's analytic
continuation of the cusp-form L-series, which is not yet in Mathlib. -/
theorem Newform.lSeries_stripped_eq_dirichlet_quotient_value
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re)
    (hs' : 1 < (2 * s - k + 1).re)
    (hs'' : 1 < (2 * (2 * s - k + 1)).re)
    (h_geom : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-s)) ^ 2‖ < 1)
    (T : Finset Nat.Primes)
    (hT_iff : ∀ p : Nat.Primes, p ∈ T ↔
      (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N)
    (h_pos_neg : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 ∧
      (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0) :
    LSeries f.lCoeff_stripped s =
      (LSeries (fun n ↦ ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) n) (2 * (2 * s - k + 1)) *
       (∏ p ∈ T,
          Newform.eulerFactor_stripped f χ S s p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹)) /
      (LSeries (fun n ↦ (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1) *
       (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹)) := by
  have h_BC_ne :
      LSeries (fun n ↦ (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
            DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) ≠ 0 :=
    mul_ne_zero (DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hs')
      (Newform.prod_dirichletLift_sq_eulerFactor_ne_zero χ T hs'')
  rw [eq_div_iff h_BC_ne, ← mul_assoc]
  exact f.lSeries_stripped_value_identity χ hfχ S h_bad hs hs' hs''
    h_geom T hT_iff h_pos_neg

/-- **Special evaluation point** `s₀ = ((k : ℝ) / 2 + 2 : ℂ)` for the
Dirichlet-quotient value identity, at which the real-part and
non-vanishing side conditions all discharge automatically. -/
noncomputable def Newform.specialPoint (k : ℤ) : ℂ :=
  (((k : ℝ) / 2 + 2 : ℝ) : ℂ)

@[simp] lemma Newform.specialPoint_re (k : ℤ) :
    (Newform.specialPoint k).re = (k : ℝ) / 2 + 2 := Complex.ofReal_re _

@[simp] lemma Newform.specialPoint_im (k : ℤ) :
    (Newform.specialPoint k).im = 0 := Complex.ofReal_im _

/-- Real part of the image point `s' = 2 · s₀ - k + 1` is `5`. -/
lemma Newform.two_specialPoint_sub_k_add_one_re (k : ℤ) :
    (2 * Newform.specialPoint k - (k : ℂ) + 1).re = 5 := by
  have h₁ : ((k : ℂ)).re = (k : ℝ) := by simp
  have h₂ : ((2 : ℂ) * Newform.specialPoint k).re = (k : ℝ) + 4 := by
    rw [Complex.mul_re]
    simp [Newform.specialPoint_re, Newform.specialPoint_im]
    ring
  rw [Complex.add_re, Complex.sub_re, h₂, h₁]
  simp
  ring

/-- Real part of the doubled image point `2s' = 2 · (2 · s₀ - k + 1)` is `10`. -/
lemma Newform.two_two_specialPoint_sub_k_add_one_re (k : ℤ) :
    (2 * (2 * Newform.specialPoint k - (k : ℂ) + 1)).re = 10 := by
  rw [show (2 * (2 * Newform.specialPoint k - (k : ℂ) + 1) : ℂ).re =
    2 * (2 * Newform.specialPoint k - (k : ℂ) + 1).re from by
      rw [Complex.mul_re]; simp]
  rw [Newform.two_specialPoint_sub_k_add_one_re]; norm_num

omit [NeZero N] in
/-- **Geometric convergence at the special point.**  For any prime `q ≥ 2`
coprime to `N`, the argument `χ(q) · q^{-(2·s₀-k+1)} = χ(q) · q^{-5}` has
norm `q^{-5} ≤ 2^{-5} = 1/32 < 1`. -/
lemma Newform.norm_chi_q_cpow_neg_lt_one_of_re_pos [NeZero N]
    (χ : (ZMod N)ˣ →* ℂˣ) {q : ℕ} (hq : 2 ≤ q) (hqN : Nat.Coprime q N)
    {s' : ℂ} (hs' : (0 : ℝ) < s'.re) :
    ‖(χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (-s')‖ < 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hq_one : (1 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  rw [norm_mul, Newform.norm_chi_unit_eq_one, one_mul,
    show ((q : ℂ) ^ (-s')) = ((q : ℝ) : ℂ) ^ (-s') from by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hq_pos]
  have hneg : (-s').re < 0 := by rw [Complex.neg_re]; linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg hq_one hneg

/-- `1 + x ≠ 0` whenever `‖x‖ < 1`: otherwise `x = -1` and `‖x‖ = 1`. -/
lemma Newform.one_add_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) :
    (1 : ℂ) + x ≠ 0 := by
  intro h
  have hxeq : x = -1 := by linear_combination h
  rw [hxeq] at hx
  simp at hx

/-- `1 - x ≠ 0` whenever `‖x‖ < 1`: otherwise `x = 1` and `‖x‖ = 1`. -/
lemma Newform.one_sub_ne_zero_of_norm_lt_one {x : ℂ} (hx : ‖x‖ < 1) :
    (1 : ℂ) - x ≠ 0 := by
  intro h
  have hxeq : x = 1 := by linear_combination -h
  rw [hxeq] at hx
  simp at hx

/-- **Value identity specialised at the special point `s₀ = k/2 + 2`.**
Discharges the real-part and geometric / pole non-vanishing side
conditions of `Newform.lSeries_stripped_eq_dirichlet_quotient_value`,
leaving only `h_bad` and the finset characterisation `hT_iff` as consumer
obligations.  A single-point identity does not close the full contradiction
(which requires Hecke's analytic continuation, not yet in Mathlib). -/
theorem Newform.lSeries_stripped_eq_dirichlet_quotient_value_at_special_point
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    (T : Finset Nat.Primes)
    (hT_iff : ∀ p : Nat.Primes, p ∈ T ↔
      (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N) :
    LSeries f.lCoeff_stripped (Newform.specialPoint k) =
      (LSeries (fun n ↦ ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) n)
          (2 * (2 * Newform.specialPoint k - (k : ℂ) + 1)) *
       (∏ p ∈ T,
          Newform.eulerFactor_stripped f χ S (Newform.specialPoint k) p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * Newform.specialPoint k - (k : ℂ) + 1)))⁻¹)) /
      (LSeries (fun n ↦ (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * Newform.specialPoint k - (k : ℂ) + 1) *
       (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * Newform.specialPoint k - (k : ℂ) + 1))))⁻¹)) := by
  have hs : (k : ℝ) / 2 + 1 < (Newform.specialPoint k).re := by
    rw [Newform.specialPoint_re]; linarith
  have hs' : 1 < (2 * Newform.specialPoint k - (k : ℂ) + 1).re := by
    rw [Newform.two_specialPoint_sub_k_add_one_re]; norm_num
  have hs'' : 1 < (2 * (2 * Newform.specialPoint k - (k : ℂ) + 1)).re := by
    rw [Newform.two_two_specialPoint_sub_k_add_one_re]; norm_num
  have h_geom : ∀ q : ℕ, ∀ (hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-Newform.specialPoint k)) ^ 2‖ < 1 := by
    intro q hq hqN _
    have hs_ge : ((k : ℝ) - 1) / 2 < (Newform.specialPoint k).re := by
      rw [Newform.specialPoint_re]; linarith
    exact Newform.norm_eulerFactor_argument_lt_one χ k hq.two_le hqN _ hs_ge
  have h_pos_neg : ∀ q : ℕ, ∀ (hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * Newform.specialPoint k - (k : ℂ) + 1)) ≠ 0 ∧
      (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * Newform.specialPoint k - (k : ℂ) + 1)) ≠ 0 := by
    intro q hq hqN _
    have h_norm_lt :
        ‖(χ (ZMod.unitOfCoprime q hqN) : ℂ) *
          (q : ℂ) ^ (-(2 * Newform.specialPoint k - (k : ℂ) + 1))‖ < 1 := by
      apply Newform.norm_chi_q_cpow_neg_lt_one_of_re_pos χ hq.two_le hqN
      rw [Newform.two_specialPoint_sub_k_add_one_re]; norm_num
    exact ⟨Newform.one_add_ne_zero_of_norm_lt_one h_norm_lt,
           Newform.one_sub_ne_zero_of_norm_lt_one h_norm_lt⟩
  exact f.lSeries_stripped_eq_dirichlet_quotient_value χ hfχ S h_bad
    hs hs' hs'' h_geom T hT_iff h_pos_neg

/-- **Newform prime-nonvanishing** (Miyake Thm 4.5.16, Diamond–Shurman §5.9).
For a `Newform f` lying in the character eigenspace
`modFormCharSpace k χ` and any finite exceptional set `S : Finset ℕ`,
there is a prime `q` coprime to `N`, outside `S`, with
`f.eigenvalue q ≠ 0`.

Current status (`sorry`).  **This statement requires genuine analytic
input beyond `IsHeckeCoefficientSequence` alone.**  The counterexample
sequence `a 0 = 0, a 1 = 1, a p = 0` for every prime `p`, extended by
`mul_coprime` / `recur`, satisfies all four fields of
`IsHeckeCoefficientSequence` yet has every prime coefficient zero; the
abstract predicate therefore does **not** imply prime-nonvanishing.  A
correct proof must use the fact that `f` is an honest cusp form.

The per-prime closed forms, stripped Euler product, and Dirichlet-quotient
value identity developed above are all sorry-free; the remaining gap is
Hecke's analytic continuation of the cusp-form L-series, not yet in
Mathlib (see `Newform.lSeries_stripped_eq_dirichlet_quotient_value`). -/
theorem Newform.exists_nonzero_prime_eigenvalue (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 := by
  sorry

/-- **Strong Multiplicity One**: a newform in `S_k(Γ₁(N), χ)` is uniquely
determined by its Hecke eigenvalues at almost all primes (any cofinite set of
primes coprime to N).

This strengthens `newform_unique` by allowing finitely many exceptional primes,
via coprime multiplicativity of eigenvalues and cancellation.  Depends on
`exists_nonzero_prime_eigenvalue`, which is currently sorry'd (see its
docstring). -/
theorem strongMultiplicityOne
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine newform_unique f g χ hfχ hgχ ?_
  intro n hn
  by_cases hn_S : n.val ∈ S
  · have hn_pos : 0 < n.val := n.pos
    let bad : Finset ℕ := S ∪ S.image (· / n.val) ∪ n.val.primeFactors
    obtain ⟨q, hq_prime, hq_N, hq_notin, hq_ne⟩ :=
      Newform.exists_nonzero_prime_eigenvalue f χ hfχ bad
    have hq_pos : 0 < q := hq_prime.pos
    have hq_notin_S : q ∉ S := fun hqS ↦ hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inl hqS))
    have hq_notin_img : q ∉ S.image (· / n.val) := fun h' ↦ hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inr h'))
    have hq_nd_n : ¬ q ∣ n.val := fun hqn ↦ hq_notin (by
      simp only [bad, Finset.mem_union, Nat.mem_primeFactors]
      exact Or.inr ⟨hq_prime, hqn, hn_pos.ne'⟩)
    have hn_coprime_q : Nat.Coprime n.val q :=
      ((hq_prime.coprime_iff_not_dvd).mpr hq_nd_n).symm
    have hnq_notin_S : n.val * q ∉ S := fun hnqS ↦ hq_notin_img <| by
      refine Finset.mem_image.mpr ⟨n.val * q, hnqS, ?_⟩
      exact Nat.mul_div_cancel_left _ hn_pos
    let q_pnat : ℕ+ := ⟨q, hq_pos⟩
    let nq_pnat : ℕ+ := ⟨n.val * q, Nat.mul_pos hn_pos hq_pos⟩
    have hnq_N : Nat.Coprime (n.val * q) N := hn.mul_left hq_N
    have hq_eq : f.eigenvalue q_pnat = g.eigenvalue q_pnat := h q_pnat hq_N hq_notin_S
    have hnq_eq : f.eigenvalue nq_pnat = g.eigenvalue nq_pnat := h nq_pnat hnq_N hnq_notin_S
    have hmul_f : f.eigenvalue nq_pnat = f.eigenvalue n * f.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul f n q_pnat hn hq_N hn_coprime_q χ hfχ
    have hmul_g : g.eigenvalue nq_pnat = g.eigenvalue n * g.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul g n q_pnat hn hq_N hn_coprime_q χ hgχ
    have hcomb :
        f.eigenvalue n * f.eigenvalue q_pnat = g.eigenvalue n * f.eigenvalue q_pnat := by
      rw [← hmul_f, hnq_eq, hmul_g, hq_eq]
    exact mul_right_cancel₀ hq_ne hcomb
  · exact h n hn hn_S


end HeckeRing.GL2
