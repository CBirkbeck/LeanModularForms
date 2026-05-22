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
import LeanModularForms.HeckeRIngs.GL2.Newforms.MainLemma

/-!
# Newforms: Strong Multiplicity One inputs, coefficient sequences, and L-series

Strong Multiplicity One (the project goal), the coefficient-sequence view of a newform, the `IsHeckeCoefficientSequence` predicate, closed forms at bad primes, the newform L-series, the stripped Hecke sequence and its Euler product, Dirichlet-quotient identifications, and the T108/T111/T129 value identities.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### Strong Multiplicity One (the goal of the project) -/

/-- **Coprime multiplicativity of eigenvalues**: if `f` is a newform in the
character eigenspace `modFormCharSpace k χ` and `gcd(m, n) = 1`, then
`λ_{mn} = λ_m · λ_n`.

This follows from the period-1 multiplicativity
`HeckeRing.GL2.eigenform_coeff_multiplicative_one` (FourierHecke.lean,
T082) via the period-1 bridge `Newform.eigenvalue_eq_coeff`. -/
theorem Newform.eigenvalue_coprime_mul (f : Newform N k) (m n : ℕ+)
    (hm : Nat.Coprime m.val N) (hn : Nat.Coprime n.val N)
    (hmn : Nat.Coprime m.val n.val) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.eigenvalue ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩ =
      f.eigenvalue m * f.eigenvalue n := by
  haveI : NeZero m.val := ⟨m.pos.ne'⟩
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have hmn_N : Nat.Coprime (m.val * n.val) N := hm.mul_left hn
  -- Convert all three eigenvalues to canonical Fourier coefficients (period 1).
  rw [Newform.eigenvalue_eq_coeff f ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩
        hmn_N χ hf_char,
      Newform.eigenvalue_eq_coeff f m hm χ hf_char,
      Newform.eigenvalue_eq_coeff f n hn χ hf_char]
  -- Goal (after rewrites): a_{mn}(f) = a_m(f) · a_n(f) with period-1 coefficients.
  -- Rewrite in terms of the underlying ModularForm.
  change (ModularFormClass.qExpansion (1 : ℝ) (⇑f.toCuspForm)).coeff (m.val * n.val) =
      (ModularFormClass.qExpansion (1 : ℝ) (⇑f.toCuspForm)).coeff m.val *
      (ModularFormClass.qExpansion (1 : ℝ) (⇑f.toCuspForm)).coeff n.val
  rw [show (⇑f.toCuspForm : UpperHalfPlane → ℂ) = ⇑f.toCuspForm.toModularForm' from rfl]
  -- Promote the Newform data to the **period-1** `IsNormalisedEigenform_one` at
  -- the ModularForm level.
  have hf_eigen : IsNormalisedEigenform_one k f.toCuspForm.toModularForm' := by
    refine ⟨?_, ?_⟩
    · intro n' hn'
      haveI : NeZero n'.val := ⟨n'.pos.ne'⟩
      refine ⟨f.eigenvalue n', ?_⟩
      have h_cusp := f.isEigen n' hn'
      have h_lift : (heckeT_n_cusp k n'.val f.toCuspForm).toModularForm' =
          (f.eigenvalue n' • f.toCuspForm).toModularForm' := by rw [h_cusp]
      rw [heckeT_n_cusp_toModularForm'] at h_lift
      exact h_lift
    · -- Period-1 normalisation is exactly `f.isNorm`.
      change (ModularFormClass.qExpansion (1 : ℝ)
          (⇑f.toCuspForm.toModularForm')).coeff 1 = 1
      rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) =
          ⇑f.toCuspForm from rfl]
      exact f.isNorm
  -- Apply the period-1 multiplicativity and collapse at `gcd(m,n) = 1`.
  have h := eigenform_coeff_multiplicative_one k m n hm hn χ hf_char hf_eigen
  have hgcd : Nat.gcd m.val n.val = 1 := hmn
  rw [hgcd, Nat.divisors_one, Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] at h
  exact h.symm

/-! ### Coefficient-sequence view of a newform

A convenient `ℕ → ℂ` coefficient sequence for a newform, suitable as the
direct input to the L-series / Dirichlet-series machinery in
`LeanModularForms/Modularforms/LFunction.lean` and to the Euler-product tools
in `Mathlib.NumberTheory.EulerProduct.Basic`.

The three basic properties proved here — vanishing at `0`, normalisation at
`1`, and multiplicativity on coprime arguments both coprime to `N` — are
exactly what `eulerProduct_hasProd` needs on the coefficient side.  A full
`IsHeckeCoefficientSequence` predicate (including the Hecke recurrence at
primes) is deferred to a follow-up; see the docstring of
`Newform.exists_nonzero_prime_eigenvalue` for the exact missing theorem. -/

/-- Coefficient sequence of a newform: `n ↦ aₙ(f)` via the **canonical
period-1** q-expansion (the standard Fourier coefficients of `f` as a
`Γ₁(N)`-cusp form).  This is the sequence consumed by the L-series /
Dirichlet-series machinery (`LFunction.lean`) and the Euler-product
tools. -/
noncomputable def Newform.lCoeff (f : Newform N k) : ℕ → ℂ :=
  fun n => (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n

@[simp]
lemma Newform.lCoeff_apply (f : Newform N k) (n : ℕ) :
    f.lCoeff n = (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n := rfl

/-- `a₀(f) = 0` for a newform (cusp forms vanish at infinity). -/
lemma Newform.lCoeff_zero (f : Newform N k) : f.lCoeff 0 = 0 := by
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have hcusp := CuspFormClass.zero_at_infty f.toCuspForm
  simp [Newform.lCoeff,
    ModularFormClass.qExpansion_coeff_zero (f := f.toCuspForm) h1_pos h1_period,
    hcusp.valueAtInfty_eq_zero]

/-- **Normalisation**: `a₁(f) = 1` for a newform, directly from `f.isNorm`
(which is stated at the canonical period 1). -/
@[simp]
lemma Newform.lCoeff_one (f : Newform N k) : f.lCoeff 1 = 1 := f.isNorm

/-- **Coprime multiplicativity** of the newform coefficient sequence at
the canonical period 1: for `m, n ≥ 1` coprime to `N` with `gcd m n = 1`,

  `a_{m n}(f) = a_m(f) · a_n(f)`.

This is the main consumer of the already-proved
`Newform.eigenvalue_coprime_mul` / `Newform.eigenvalue_eq_coeff` bridge. -/
lemma Newform.lCoeff_mul_of_coprime (f : Newform N k) (m n : ℕ)
    (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hm : Nat.Coprime m N) (hn : Nat.Coprime n N) (hmn : Nat.Coprime m n)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.lCoeff (m * n) = f.lCoeff m * f.lCoeff n := by
  -- Convert to eigenvalues via the period-1 `eigenvalue_eq_coeff`,
  -- then apply `eigenvalue_coprime_mul`.
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
  have h_mul := Newform.eigenvalue_coprime_mul f ⟨m, hm_pos⟩ ⟨n, hn_pos⟩
    hm hn hmn χ hf_char
  simp only [Newform.lCoeff_apply]
  rw [← h_mn, ← h_m, ← h_n]
  exact h_mul

/-! ### `IsHeckeCoefficientSequence` predicate

The four arithmetic axioms of the Fourier coefficient sequence of a
normalised Hecke eigenform, abstracted away from the modular-form
structure.  This is a useful combinatorial bundle for sequence-level
manipulation (e.g. the prime-power recurrence collapse, divisor-sum
identities), but it is **strictly weaker than the cusp-form analytic
input** — the four fields admit formal "Euler-factor" sequences with
`a p = 0` at every prime coprime to `N`, which satisfy all four fields
via `a (p^{2j+1}) = 0` and `a (p^{2j}) = (−χ(p))^j p^{j(k-1)}` from the
recurrence.  Such sequences violate prime-nonvanishing, so any
`exists_prime_coeff_ne_zero`-style consequence requires an additional
analytic hypothesis (L-series convergence + modular-form nontriviality);
see the docstring of `Newform.exists_nonzero_prime_eigenvalue` for the
concrete analytic blocker. -/

/-- **A Hecke coefficient sequence** `a : ℕ → ℂ` at level `N`, weight `k`,
with Nebentypus character `χ : (ZMod N)ˣ →* ℂˣ`.  Captures the four
arithmetic properties shared by every Fourier coefficient sequence of a
normalised Hecke eigenform in `S_k(Γ₁(N), χ)`:

* `zero`: vanishing at `0` (cusp condition);
* `one`: normalisation `a₁ = 1`;
* `mul_coprime`: coprime-multiplicativity `a_{mn} = a_m · a_n` whenever
  `m`, `n` are coprime to each other and both coprime to the level;
* `recur`: Hecke recurrence at primes coprime to `N`:
  `a_{p^{r+2}} = a_p · a_{p^{r+1}} − χ(p) · p^{k-1} · a_{p^r}`.

**Warning.**  These four fields do **not** by themselves imply
prime-nonvanishing (`∃ q prime coprime to N, a q ≠ 0`).  The sequence
`a 0 = 0`, `a 1 = 1`, `a p = 0` for every prime `p` coprime to `N`,
extended multiplicatively to coprime arguments and via the recurrence to
prime powers, satisfies all four fields yet has every prime coefficient
(coprime to `N`) equal to zero.  A genuine proof of prime-nonvanishing
requires the additional analytic input that the sequence `a` is the
Fourier coefficient sequence of an actual non-zero cusp form (so that
its `LSeries` is summable, entire, and does not coincide with the
Dirichlet L-function quotient that a counterexample sequence would
yield).

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

/-! ### Closed form at a prime where `a q` vanishes (T089 / DS §5.9 case A) -/

/-- **Odd-prime-power vanishing.**  If a Hecke coefficient sequence
satisfies `a q = 0` at a prime `q` coprime to the level, then by the
Hecke recurrence every odd power `q ^ (2 j + 1)` also has zero
coefficient.

This is the sequence-level half of the Dirichlet quotient analysis
(Diamond–Shurman §5.9 case A).  Combined with
`coeff_prime_pow_even_eq_of_a_p_zero`, the local Euler factor at `q`
collapses to a quadratic-in-`q^{-s}` reciprocal — see
`ModularForms.tsum_alternating_pow_eq` for the formal sum identity. -/
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
`a (q ^ (2 j)) = (-χ(q) · q^{k-1}) ^ j`.

This is the explicit Dirichlet quotient sequence at `q` referenced in
Diamond–Shurman §5.9 case A and Miyake §4.5.16. -/
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
  · -- `r` even: `r = 2 * j`; goal collapses to the even closed form.
    obtain ⟨j, rfl⟩ := hr
    have h_even : Even (j + j) := ⟨j, rfl⟩
    have h_two_j : j + j = 2 * j := by ring
    rw [if_pos h_even, h_two_j, h.coeff_prime_pow_even_eq_of_a_p_zero hq hqN h_zero j]
    have hj_div : (2 * j) / 2 = j := by
      rw [Nat.mul_div_cancel_left _ (by norm_num)]
    rw [hj_div]
  · -- `r` odd: `r = 2 * j + 1`; goal collapses to `0`.
    obtain ⟨j, rfl⟩ := hr
    rw [if_neg (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩)]
    exact h.coeff_prime_pow_odd_eq_zero_of_a_p_zero hq hqN h_zero j

/-- **Promotion helper**: the underlying modular form of a `Newform` is a
period-1 normalised eigenform (`IsNormalisedEigenform_one`) at the
`ModularForm` level.  This repackages `f.isEigen` through
`heckeT_n_cusp_toModularForm'` and bundles it with `f.isNorm`, both at
the canonical Fourier period. -/
theorem Newform.isNormalisedEigenform (f : Newform N k) :
    IsNormalisedEigenform_one k f.toCuspForm.toModularForm' := by
  refine ⟨?_, ?_⟩
  · intro n' hn'
    haveI : NeZero n'.val := ⟨n'.pos.ne'⟩
    refine ⟨f.eigenvalue n', ?_⟩
    have h_cusp := f.isEigen n' hn'
    have h_lift : (heckeT_n_cusp k n'.val f.toCuspForm).toModularForm' =
        (f.eigenvalue n' • f.toCuspForm).toModularForm' := by rw [h_cusp]
    rw [heckeT_n_cusp_toModularForm'] at h_lift
    exact h_lift
  · change (ModularFormClass.qExpansion (1 : ℝ)
        (⇑f.toCuspForm.toModularForm')).coeff 1 = 1
    rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) =
        ⇑f.toCuspForm from rfl]
    exact f.isNorm

/-- **Bridge**: the Fourier coefficient sequence of a `Newform` living in a
character eigenspace `modFormCharSpace k χ` satisfies
`IsHeckeCoefficientSequence`, i.e. the four arithmetic axioms required by the
Euler-product / Dirichlet-series machinery.

The four fields collect:
* `zero` from `Newform.lCoeff_zero`;
* `one` from `Newform.lCoeff_one`;
* `mul_coprime` from `Newform.lCoeff_mul_of_coprime` (with trivial
  handling of the degenerate `m = 0` / `n = 0` corners forced by
  coprimality);
* `recur` from `HeckeRing.GL2.eigenform_coeff_multiplicative_one`
  (FourierHecke.lean, T082) specialised at `(p^{r+1}, p)` and the
  collapse of the period-1 divisor sum over `gcd(p^{r+1}, p) = p`. -/
theorem Newform.lCoeff_isHeckeCoefficientSequence (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    IsHeckeCoefficientSequence N k χ f.lCoeff where
  zero := f.lCoeff_zero
  one := f.lCoeff_one
  mul_coprime := by
    intro m n hmN hnN hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · -- `m = 0`: `Nat.Coprime 0 n` forces `n = 1`.
      have hn1 : n = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_left] at hmn
      subst hn1
      change f.lCoeff (0 * 1) = f.lCoeff 0 * f.lCoeff 1
      rw [Nat.zero_mul, f.lCoeff_zero, zero_mul]
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · -- `n = 0`: `Nat.Coprime m 0` forces `m = 1`.
        have hm1 : m = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_right] at hmn
        subst hm1
        change f.lCoeff (1 * 0) = f.lCoeff 1 * f.lCoeff 0
        rw [Nat.mul_zero, f.lCoeff_zero, mul_zero]
      · exact f.lCoeff_mul_of_coprime m n hm hn hmN hnN hmn χ hfχ
  recur := by
    intro p hp hpN r
    -- Specialise the period-1 `eigenform_coeff_multiplicative_one` at
    -- `(p^{r+1}, p)` and collapse the divisor sum over `gcd(p^{r+1}, p) = p`.
    have hp_pos : 0 < p := hp.pos
    haveI : NeZero p := ⟨hp_pos.ne'⟩
    have hpow_pos : 0 < p ^ (r + 1) := pow_pos hp_pos _
    haveI : NeZero (p ^ (r + 1)) := ⟨hpow_pos.ne'⟩
    have hpow_cop : Nat.Coprime (p ^ (r + 1)) N := hpN.pow_left _
    have hf_eigen : IsNormalisedEigenform_one k f.toCuspForm.toModularForm' :=
      f.isNormalisedEigenform
    have h := eigenform_coeff_multiplicative_one (N := N) k
      ⟨p ^ (r + 1), hpow_pos⟩ ⟨p, hp_pos⟩ hpow_cop hpN χ hfχ hf_eigen
    -- Normalise the `ℕ+` coercions on the left so subsequent rewrites match.
    simp only [PNat.mk_coe] at h
    -- `m * n = p^{r+2}`.
    have h_mn : p ^ (r + 1) * p = p ^ (r + 2) := by ring
    -- `gcd(p^{r+1}, p) = p` (since `p` is prime and `r + 1 ≥ 1`).
    have h_gcd : Nat.gcd (p ^ (r + 1)) p = p :=
      Nat.gcd_eq_right (dvd_pow_self p (Nat.succ_ne_zero r))
    -- `p.divisors = {1, p}`; split the sum.
    rw [h_gcd, hp.divisors,
        Finset.sum_insert (by
          simp only [Finset.mem_singleton]; exact hp.ne_one.symm),
        Finset.sum_singleton] at h
    -- Simplify the `d = 1` term: `χ(1) = 1`, `1^{k-1} = 1`, `div 1 = id`.
    have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
      ext; simp [ZMod.coe_unitOfCoprime]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
      h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] at h
    -- Resolve the `dite` at `d = p` via `hpN`.
    rw [dif_pos hpN] at h
    -- `p^{r+1} * p / (p * p) = p^r`.
    have h_div : p ^ (r + 1) * p / (p * p) = p ^ r := by
      rw [show p ^ (r + 1) * p = p ^ r * (p * p) by ring]
      exact Nat.mul_div_cancel _ (by positivity)
    rw [h_div, h_mn] at h
    -- `h : lCoeff (p^{r+1}) * lCoeff p = lCoeff (p^{r+2}) + p^{k-1} * χ(p) * lCoeff (p^r)`
    -- (all coefficients at period 1; defeq through `toModularForm'`).
    simp only [Newform.lCoeff_apply]
    -- Align the CuspForm-level and ModularForm-level period-1 `qExpansion` terms.
    show (ModularFormClass.qExpansion (1 : ℝ)
          f.toCuspForm.toModularForm').coeff (p ^ (r + 2)) =
        (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff p *
        (ModularFormClass.qExpansion (1 : ℝ)
          f.toCuspForm.toModularForm').coeff (p ^ (r + 1)) -
        (χ (ZMod.unitOfCoprime p hpN) : ℂ) * (p : ℂ) ^ (k - 1) *
        (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff (p ^ r)
    linear_combination -h

/-! ### L-series of a newform

Bridge `Newform.lCoeff` and the cusp-form L-series API of
`LeanModularForms.Modularforms.LFunction`.  The strict width at `i∞` of
`(Gamma1 N).map (mapGL ℝ)` is `1` (`ModularForms.strictWidthInfty_Gamma1_mapGL`),
so the canonical period-1 Fourier sequence `n ↦ (qExpansion 1 f.toCuspForm).coeff n`
that defines `Newform.lCoeff` is definitionally the `ModularForms.lCoeff`
sequence used by every cusp-form L-series tool.  This is the
`Newforms`-side packaging of those tools, used by
`Newform.exists_nonzero_prime_eigenvalue`. -/

/-- **Bridge to `ModularForms.lCoeff`.**  The `Newform.lCoeff` sequence is
the same as the generic `ModularForms.lCoeff f.toCuspForm` sequence built
from the strict-width-at-`∞` `q`-expansion. -/
lemma Newform.lCoeff_eq_modularForms_lCoeff (f : Newform N k) (n : ℕ) :
    f.lCoeff n = ModularForms.lCoeff f.toCuspForm n := by
  rw [Newform.lCoeff_apply,
    ← ModularForms.lCoeff_Gamma1_mapGL_eq (N := N) (k := k) (F := CuspForm _ k)
      f.toCuspForm n]

/-- **Function-level form of `Newform.lCoeff_eq_modularForms_lCoeff`**, useful
for substituting the whole sequence under an `LSeries` / `LSeriesSummable`
predicate via `rw`. -/
lemma Newform.lCoeff_eq_modularForms_lCoeff_funext (f : Newform N k) :
    f.lCoeff = ModularForms.lCoeff f.toCuspForm :=
  funext (Newform.lCoeff_eq_modularForms_lCoeff f)

/-- **Absolute summability** of the Dirichlet series `LSeries f.lCoeff` on
the half-plane `Re s > k/2 + 1`.  Direct specialisation of the cusp-form
bound `ModularForms.lSeriesSummable_of_cuspForm` to a `Newform`. -/
lemma Newform.lSeriesSummable (f : Newform N k) {s : ℂ}
    (hs : (k : ℝ) / 2 + 1 < s.re) :
    LSeriesSummable f.lCoeff s := by
  rw [Newform.lCoeff_eq_modularForms_lCoeff_funext]
  exact ModularForms.lSeriesSummable_of_cuspForm
    (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (F := CuspForm _ k) f.toCuspForm hs

/-- **L-series injectivity for newforms** (specialisation of
`ModularForms.lSeries_eq_iff_cuspForm`).  Two newforms have the same
Dirichlet L-series iff their `lCoeff` sequences agree at every positive
index. -/
lemma Newform.lSeries_eq_iff (f g : Newform N k) :
    LSeries f.lCoeff = LSeries g.lCoeff ↔ ∀ n ≠ 0, f.lCoeff n = g.lCoeff n := by
  rw [Newform.lCoeff_eq_modularForms_lCoeff_funext f,
      Newform.lCoeff_eq_modularForms_lCoeff_funext g]
  exact ModularForms.lSeries_eq_iff_cuspForm
    (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k)
    (F := CuspForm _ k) (F' := CuspForm _ k) f.toCuspForm g.toCuspForm

/-- **L-series non-vanishing** for a newform.  Since `f.lCoeff 1 = 1 ≠ 0`
(`Newform.lCoeff_one`), the Dirichlet series `LSeries f.lCoeff` is not
identically zero. -/
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

/-! ### Stripped Hecke coefficient sequence (T093)

The "stripped" Fourier coefficient sequence `n ↦ if n.Coprime N then
f.lCoeff n else 0` is FULLY multiplicative on coprime arguments
(unlike `f.lCoeff` itself, whose multiplicativity bridge
`Newform.lCoeff_mul_of_coprime` requires both factors coprime to `N`).
This is the Mathlib-`eulerProduct_hasProd`-compatible reformulation of
the Newform L-series; the local Euler factor at primes dividing `N` is
trivially `1` after stripping, while the factor at primes coprime to
`N` is the genuine local Euler factor of `f`.

Combined with `Newform.tsum_lCoeff_pow_mul_eq_eulerFactor` below, the
stripped sequence enables the full Dirichlet quotient identification
in DS §5.9 / Miyake §4.5.16. -/

/-- **Stripped Newform Fourier sequence.**  `n ↦ f.lCoeff n` if `n` is
coprime to `N`, else `0`.  This is the part of `f.lCoeff` consumed by
the Mathlib Euler-product machinery. -/
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
`f.lCoeff_stripped (m * n) = f.lCoeff_stripped m * f.lCoeff_stripped n`.

The case where `m` or `n` shares a factor with `N` is handled
automatically: the stripped value is `0`, killing the product. -/
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
    · -- `m = 0`: hmn forces `n = 1`.
      have hn1 : n = 1 := by rwa [Nat.Coprime, Nat.gcd_zero_left] at hmn
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
  refine Summable.of_norm_bounded (g := fun n => ‖LSeries.term f.lCoeff s n‖)
    (f.lSeriesSummable hs).norm ?_
  intro n
  exact LSeries.norm_term_le s (f.norm_lCoeff_stripped_le n)

/-- **Cusp-form abscissa bound for the stripped coefficient sequence
(T132 H1 helper).**

The abscissa of absolute convergence of the stripped coefficient
sequence `f.lCoeff_stripped` is at most `(k : ℝ) / 2 + 1`, the standard
Hecke / cusp-form bound (Diamond–Shurman §5.9 / Miyake §4.3.5).

This is the natural cusp-form-specific specialisation supporting the
T132 H1 chain (`Newform.HeckeFEData`, `Newform.MellinPairData`,
`_classicalInputs_T111`): the strict abscissa bound
`abscissaOfAbsConv f.lCoeff_stripped < (((k : ℝ) / 2 + 1 : ℝ) : EReal)`
is then a small refinement that callers can establish under specific
cusp-form-side decay hypotheses (e.g., from Hecke-eigenform
multiplicativity giving sub-`k/2`-bounds on `aₙ`).

**Proof.**  Combines the generic abscissa-monotonicity lemma
`LSeries.abscissaOfAbsConv_le_of_norm_le` (via the pointwise bound
`‖f.lCoeff_stripped n‖ ≤ ‖f.lCoeff n‖`) with `Newform.lSeriesSummable`'s
cusp-form summability on the half-plane `Re s > k/2 + 1`. -/
lemma Newform.abscissaOfAbsConv_lCoeff_stripped_le_cuspForm
    (f : Newform N k) :
    LSeries.abscissaOfAbsConv f.lCoeff_stripped ≤ (((k : ℝ) / 2 + 1 : ℝ) : EReal) := by
  refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable' ?_
  intro y hy
  refine f.lSeriesSummable_stripped ?_
  -- `hy : ((k : ℝ) / 2 + 1 : EReal) < (y : EReal)`; descend to `ℝ` and apply
  -- `((y : ℝ) : ℂ).re = y`.
  have hy_real : (k : ℝ) / 2 + 1 < y := by exact_mod_cast hy
  show (k : ℝ) / 2 + 1 < ((y : ℝ) : ℂ).re
  simpa using hy_real

/-! ### Per-prime local Euler factor at a "bad" prime (T093) -/

/-- **Per-prime local Euler factor at a vanishing prime.**  For a `Newform`
`f` in the character eigenspace `modFormCharSpace k χ` and a prime `q`
coprime to the level with `f.lCoeff q = 0`, the local Euler factor in
the Dirichlet series for `f.lCoeff` collapses to a quadratic reciprocal:

```
∑ᵣ f.lCoeff (qʳ) · xʳ = (1 + χ(q) · q^{k-1} · x²)⁻¹
```

provided `‖χ(q) · q^{k-1} · x²‖ < 1` (the convergence condition).
For the Dirichlet-series application set `x = (q : ℂ)^(-s)`; the
right-hand side becomes the standard local Euler factor
`(1 + χ(q) · q^{k-1-2s})⁻¹` (Diamond–Shurman §5.9, Miyake §4.5.16).

This combines the T089 closed form
(`IsHeckeCoefficientSequence.coeff_prime_pow_eq_of_a_p_zero`) with the
abstract analytic identity `ModularForms.tsum_alternating_pow_eq`. -/
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
  -- Identify each summand with the alternating-power form.
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
      have h_mod : r % 2 ≠ 0 := fun heq => h_not (Nat.even_iff.mpr heq)
      rw [if_neg h_not, if_neg h_mod, zero_mul]
  rw [tsum_congr h_pointwise]
  exact ModularForms.tsum_alternating_pow_eq
    ((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) x hs

/-! ### Global Euler product collapse for the stripped sequence (T097) -/

/-- **Global Euler product** for the stripped Newform Fourier sequence.
The Dirichlet series `LSeries f.lCoeff_stripped` factorises into a product
of local Euler factors at each prime, on the half-plane `Re s > k/2 + 1`
of absolute convergence:

```
LSeries f.lCoeff_stripped s = ∏ p (∑ᵣ (LSeries.term f.lCoeff_stripped s) (pʳ))
```

Direct application of `EulerProduct.eulerProduct_hasProd` (Mathlib
`Mathlib.NumberTheory.EulerProduct.Basic`) to the sequence
`g n := LSeries.term f.lCoeff_stripped s n`, using the four hypotheses
provided by the T093 stripped-sequence machinery:

* `g 1 = 1` from `lCoeff_stripped_one`;
* `g 0 = 0` from the `LSeries.term` definition (vanishes at `0`);
* coprime multiplicativity from `lCoeff_stripped_mul_coprime` plus the
  `Complex.natCast_mul_natCast_cpow` distributivity of complex powers
  on natural-number bases;
* absolute summability of `‖g·‖` from `lSeriesSummable_stripped`.

Per-prime identification of each local factor proceeds via
`Newform.tsum_lCoeff_pow_mul_eq_eulerFactor` at "good" primes (where
`f.lCoeff q = 0`) and the trivial factor `1` at primes dividing `N`
(stripped `(p^r) = 0` for `r ≥ 1`); see follow-up lemmas. -/
theorem Newform.lSeries_stripped_hasProd (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    {s : ℂ} (hs : (k : ℝ) / 2 + 1 < s.re) :
    HasProd (fun p : Nat.Primes =>
        ∑' (e : ℕ), LSeries.term f.lCoeff_stripped s ((p : ℕ) ^ e))
      (LSeries f.lCoeff_stripped s) := by
  set g : ℕ → ℂ := LSeries.term f.lCoeff_stripped s with hg_def
  have h_g_zero : g 0 = 0 := by
    show LSeries.term f.lCoeff_stripped s 0 = 0
    rfl
  have h_g_one : g 1 = 1 := by
    show LSeries.term f.lCoeff_stripped s 1 = 1
    rw [LSeries.term_def, if_neg one_ne_zero, f.lCoeff_stripped_one,
      Nat.cast_one, Complex.one_cpow, div_one]
  have h_g_mul : ∀ {m n : ℕ}, m.Coprime n → g (m * n) = g m * g n := by
    intro m n hmn
    show LSeries.term f.lCoeff_stripped s (m * n) =
      LSeries.term f.lCoeff_stripped s m * LSeries.term f.lCoeff_stripped s n
    rw [LSeries.term_def₀ f.lCoeff_stripped_zero,
      LSeries.term_def₀ f.lCoeff_stripped_zero,
      LSeries.term_def₀ f.lCoeff_stripped_zero,
      f.lCoeff_stripped_mul_coprime hmn χ hfχ]
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have h_g_summ : Summable fun n => ‖g n‖ := (f.lSeriesSummable_stripped hs).norm
  exact EulerProduct.eulerProduct_hasProd h_g_one h_g_mul h_g_summ h_g_zero

/-- **Trivial local Euler factor at a prime dividing the level.**  For a
prime `p | N`, the stripped sequence vanishes at every positive power
`p ^ (e + 1)` (since `p ^ (e + 1)` shares the factor `p` with `N`),
so the local Euler factor reduces to the `e = 0` term, which is `1`. -/
theorem Newform.tsum_term_lCoeff_stripped_pow_of_dvd (f : Newform N k)
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ N) (s : ℂ) :
    ∑' (e : ℕ), LSeries.term f.lCoeff_stripped s (p ^ e) = 1 := by
  have hp_pos : 0 < p := hp.pos
  have h_term_zero : ∀ e, e ≥ 1 →
      LSeries.term f.lCoeff_stripped s (p ^ e) = 0 := by
    intro e he_pos
    have h_pow_pos : 0 < p ^ e := pow_pos hp_pos e
    have h_pow_ne : p ^ e ≠ 0 := h_pow_pos.ne'
    rw [LSeries.term_def, if_neg h_pow_ne]
    have h_not_cop : ¬ Nat.Coprime (p ^ e) N := by
      intro h_cop
      have h_p_cop : Nat.Coprime p N := Nat.Coprime.coprime_dvd_left
        (dvd_pow_self p (Nat.one_le_iff_ne_zero.mp he_pos)) h_cop
      have hp_gcd : Nat.gcd p N = p := Nat.gcd_eq_left hp_dvd
      rw [Nat.Coprime, hp_gcd] at h_p_cop
      exact hp.one_lt.ne' h_p_cop
    have h_strip_zero : f.lCoeff_stripped (p ^ e) = 0 := by
      unfold Newform.lCoeff_stripped
      exact if_neg h_not_cop
    rw [h_strip_zero, zero_div]
  rw [tsum_eq_single 0 (fun e he_ne_zero =>
    h_term_zero e (Nat.one_le_iff_ne_zero.mpr he_ne_zero))]
  show LSeries.term f.lCoeff_stripped s (p ^ 0) = 1
  rw [pow_zero, LSeries.term_def, if_neg one_ne_zero, f.lCoeff_stripped_one,
    Nat.cast_one, Complex.one_cpow, div_one]

/-- **Local Euler factor at a "good" prime.**  For a prime `q` coprime to
the level with `f.lCoeff q = 0`, the local Euler factor in the stripped
Dirichlet series collapses to the explicit Dirichlet-quotient form
`(1 + χ(q) · q^{k-1-2s})⁻¹`, on the half-plane `Re s > k/2 + 1` (where
the convergence hypothesis `‖χ(q) · q^{k-1} · ((q : ℂ)^(-s))^2‖ < 1`
is automatic; not enforced in this signature, supplied externally). -/
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
  -- Each summand: stripped(q^e) = lCoeff(q^e) since q^e is coprime to N.
  have hqe_cop : ∀ e, Nat.Coprime (q ^ e) N := fun e => hqN.pow_left e
  have h_strip_eq : ∀ e, f.lCoeff_stripped (q ^ e) = f.lCoeff (q ^ e) := by
    intro e
    unfold Newform.lCoeff_stripped
    exact if_pos (hqe_cop e)
  have hq_pos : 0 < q := hq.pos
  have h_cpow_swap : ∀ e : ℕ,
      ((q : ℂ) ^ e) ^ (-s) = ((q : ℂ) ^ (-s)) ^ e := by
    intro e
    rw [← Complex.natCast_cpow_natCast_mul q e (-s),
      show ((e : ℂ) * (-s)) = (-s) * (e : ℂ) from by ring,
      Complex.cpow_mul_nat]
  have h_term : ∀ e, LSeries.term f.lCoeff_stripped s (q ^ e) =
      f.lCoeff (q ^ e) * ((q : ℂ) ^ (-s)) ^ e := by
    intro e
    rw [LSeries.term_def₀ f.lCoeff_stripped_zero, h_strip_eq e]
    push_cast
    rw [h_cpow_swap e]
  rw [tsum_congr h_term]
  exact f.tsum_lCoeff_pow_mul_eq_eulerFactor χ hfχ hq hqN h_zero
    ((q : ℂ) ^ (-s)) hs

/-! ### Combined Dirichlet quotient identification (T099)

Combine `Newform.lSeries_stripped_hasProd` (T097) with the per-prime
local-factor identifications
(`Newform.tsum_term_lCoeff_stripped_pow_of_dvd` for `p ∣ N`,
`Newform.tsum_term_lCoeff_stripped_pow_of_good_prime` for "good"
primes) into a single `HasProd` whose factor function is the explicit
case-split.  This is the algebraic packaging that the final Dirichlet
non-vanishing contradiction (POST-3f / next ticket) consumes. -/

/-- **Identified local Euler factor** at a prime `p` for the
`Newform.lCoeff_stripped` Dirichlet series under the bad-primes-zero
hypothesis.  Three cases (selected by decidable predicates on `p`):

* `p ∣ N`: trivial factor `1` (stripped sequence vanishes at every
  positive power of `p`).
* `p ∈ S` and `p` coprime to `N`: residual local factor
  `∑ᵣ LSeries.term f.lCoeff_stripped s (pʳ)` (no special form).
* `p ∉ S` and `p` coprime to `N` ("good" prime, where
  `f.lCoeff p = 0` by hypothesis): explicit Dirichlet-quotient form
  `(1 + χ(p) · p^{k-1} · (p^{-s})²)⁻¹`.

The character lookup `χ (ZMod.unitOfCoprime p hpN)` requires the
coprimality witness `hpN`, which is derived from `p.Prime` plus
`¬ p ∣ N` via `Nat.Prime.coprime_iff_not_dvd`. -/
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
factors `Newform.eulerFactor_stripped`.

The convergence hypothesis `h_geom` packages the geometric-series
condition `‖χ(q) · q^{k-1} · (q^{-s})²‖ < 1` for every good prime `q`;
this is automatic when `Re s > (k-1)/2` (in particular, on the
absolute-convergence half-plane `Re s > k/2 + 1`), but is supplied
externally here for flexibility.

Proof: apply `HasProd.congr_fun` to the bare T097
`lSeries_stripped_hasProd` Euler product, then case-split each prime
into the three cases handled by T097's local-factor lemmas. -/
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
      have h_zero : f.lCoeff (p : ℕ) = 0 := h_bad _ p.prop hpN h_S
      have h_geom_p := h_geom _ p.prop hpN h_S
      exact (f.tsum_term_lCoeff_stripped_pow_of_good_prime χ hfχ p.prop hpN
        h_zero s h_geom_p).symm

/-! ### Dirichlet character lift and analytic bridges (T101)

These lemmas package the algebraic and analytic ingredients consumed by
the final Dirichlet-quotient contradiction proof for
`Newform.exists_nonzero_prime_eigenvalue` (Diamond–Shurman §5.9 / Miyake
§4.5.16).  Each is small and reusable. -/

/-- **Dirichlet character lift.**  The Newform character
`χ : (ZMod N)ˣ →* ℂˣ` lifts to a Mathlib `DirichletCharacter ℂ N` via
the canonical extension by zero on non-units (`MulChar.ofUnitHom`).
Used to apply Mathlib's Dirichlet L-function API
(`DirichletCharacter.LSeries_eulerProduct_hasProd`,
`LFunction_ne_zero_of_one_le_re`) to the Newform eigenvalue character. -/
noncomputable def Newform.dirichletLift (χ : (ZMod N)ˣ →* ℂˣ) :
    DirichletCharacter ℂ N := MulChar.ofUnitHom χ

omit [NeZero N] in
@[simp]
lemma Newform.dirichletLift_apply_unit (χ : (ZMod N)ˣ →* ℂˣ) (a : (ZMod N)ˣ) :
    (Newform.dirichletLift χ) (a : ZMod N) = (χ a : ℂ) :=
  MulChar.ofUnitHom_coe χ a

omit [NeZero N] in
/-- **Norm of a character value at a unit equals 1.**  Since `(ZMod N)ˣ`
is finite, every element has finite order; therefore the image
`χ a : ℂˣ` is a finite-order unit in ℂ — i.e. a root of unity — and so
has norm `1`. -/
lemma Newform.norm_chi_unit_eq_one [NeZero N] (χ : (ZMod N)ˣ →* ℂˣ)
    (a : (ZMod N)ˣ) :
    ‖((χ a : ℂˣ) : ℂ)‖ = 1 := by
  haveI : Fintype ((ZMod N)ˣ) := inferInstance
  have h_pow : (χ a) ^ Fintype.card ((ZMod N)ˣ) = 1 := by
    rw [← map_pow]; convert map_one χ; exact pow_card_eq_one
  have h_card_pos : 0 < Fintype.card ((ZMod N)ˣ) := Fintype.card_pos
  have h_pow_C : ((χ a : ℂˣ) : ℂ) ^ Fintype.card ((ZMod N)ˣ) = 1 := by
    have : ((χ a : ℂˣ) : ℂ) ^ Fintype.card ((ZMod N)ˣ) =
        (((χ a) ^ Fintype.card ((ZMod N)ˣ) : ℂˣ) : ℂ) := by push_cast; rfl
    rw [this, h_pow, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h_pow_C h_card_pos.ne'

omit [NeZero N] in
/-- **Geometric convergence of the good-prime Euler factor argument.**  For
any prime `q ≥ 2` coprime to `N` and `s ∈ ℂ` with `Re s > (k-1)/2`, the
geometric ratio `χ(q) · q^{k-1} · (q^{-s})²` has norm `< 1`.  In
particular, on the absolute-convergence half-plane `Re s > k/2 + 1` of
the cusp-form L-series, the hypothesis of `Newform.tsum_lCoeff_pow_mul_eq_eulerFactor`
and the T099 `Newform.lSeries_stripped_hasProd_eulerFactor` is automatic.

The norm calculation: `‖χ(q)‖ = 1` (units have unit norm),
`‖q^(k-1)‖ = q^(k-1)`, `‖q^(-s)‖² = q^(-2 Re s)`; total norm
`q^(k-1-2 Re s) < 1` iff `Re s > (k-1)/2`. -/
lemma Newform.norm_eulerFactor_argument_lt_one [NeZero N]
    (χ : (ZMod N)ˣ →* ℂˣ) (k : ℤ)
    {q : ℕ} (hq : 2 ≤ q) (hqN : Nat.Coprime q N)
    (s : ℂ) (hs : ((k : ℝ) - 1) / 2 < s.re) :
    ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ)) * (q : ℂ) ^ (k - 1) *
      ((q : ℂ) ^ (-s)) ^ 2‖ < 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hq
  rw [norm_mul, norm_mul, norm_pow]
  rw [Newform.norm_chi_unit_eq_one χ (ZMod.unitOfCoprime q hqN), one_mul]
  rw [show ((q : ℂ) ^ (-s)) = ((q : ℝ) : ℂ) ^ (-s) from by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hq_pos]
  rw [show ((q : ℂ) ^ (k - 1)) = ((q : ℝ) : ℂ) ^ (k - 1) from by push_cast; rfl,
    show (((q : ℝ) : ℂ) ^ (k - 1)) = ((q : ℝ) : ℂ) ^ ((k - 1 : ℤ) : ℂ) from by
      rw [Complex.cpow_intCast],
    Complex.norm_cpow_eq_rpow_re_of_pos hq_pos]
  rw [show (-s).re = -s.re from by simp,
    show ((k - 1 : ℤ) : ℂ).re = (k - 1 : ℤ) from by simp]
  rw [show (((q : ℝ) ^ (-s.re : ℝ)) ^ 2) = (q : ℝ) ^ ((-s.re) * 2) from by
    rw [← Real.rpow_natCast ((q : ℝ) ^ (-s.re : ℝ)) 2, ← Real.rpow_mul hq_pos.le]
    norm_num]
  rw [← Real.rpow_add hq_pos,
    show ((↑(k - 1 : ℤ) : ℝ) + (-s.re) * 2) = ((k : ℝ) - 1) - 2 * s.re from by
      push_cast; ring]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq) (by linarith)

/-- **Algebraic Dirichlet-quotient rewrite of the good-prime Euler
factor.**  The local Euler factor `(1 + x)⁻¹` (with `x = χ(q) ·
q^{k-1-2s}` at a good prime) decomposes as the ratio
`(1 - x) · (1 - x²)⁻¹`, exhibiting the formal "Dirichlet quotient"
shape `1/L(s', χ̃) · L(2s', χ̃²)` at each prime.  Requires both
`1 + x ≠ 0` (so the LHS makes sense) and `1 - x ≠ 0` (so `1 - x²`
splits as `(1-x)(1+x) ≠ 0`).

When `x = χ(q) · q^{k-1-2s}` and `‖x‖ < 1` (the convergence regime),
`1 ± x ≠ 0` holds automatically since `‖±x‖ < 1` keeps `1 ± x` away
from `0`. -/
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
`f.lCoeff_stripped 1 = 1 ≠ 0` (`Newform.lCoeff_stripped_one`).  This is
the stripped-sequence analogue of T031's `Newform.lSeries_ne_zero`,
proved via Mathlib's `LSeries_eq_zero_iff` plus the finite abscissa of
absolute convergence from `Newform.lSeriesSummable_stripped`. -/
lemma Newform.lSeries_stripped_ne_zero (f : Newform N k) :
    LSeries f.lCoeff_stripped ≠ 0 := by
  have h_lCoeff_ne : f.lCoeff_stripped ≠ 0 := by
    intro habs
    have h1 : f.lCoeff_stripped 1 = 0 := by rw [habs]; rfl
    rw [f.lCoeff_stripped_one] at h1
    exact one_ne_zero h1
  -- Abscissa of absolute convergence is finite: bounded above by any
  -- single summability point.  Take `s = (k/2 + 2 : ℝ)` (above the
  -- absolute-convergence boundary `k/2 + 1`) and use
  -- `Newform.lSeriesSummable_stripped`.
  have h_abscissa_lt_top : LSeries.abscissaOfAbsConv f.lCoeff_stripped < ⊤ := by
    have h_summ : LSeriesSummable f.lCoeff_stripped (((k : ℝ) / 2 + 2 : ℝ) : ℂ) := by
      apply f.lSeriesSummable_stripped
      simp
    refine lt_of_le_of_lt (LSeriesSummable.abscissaOfAbsConv_le h_summ) ?_
    exact EReal.coe_lt_top _
  intro habs
  rcases (LSeries_eq_zero_iff f.lCoeff_stripped_zero).mp habs with h | h
  · exact h_lCoeff_ne h
  · exact h_abscissa_lt_top.ne h

/-! ### Local Dirichlet-quotient identification (T103) -/

/-- **Local good-prime Euler factor as a Dirichlet quotient.**  For a
prime `q` coprime to `N` with `f.lCoeff q = 0`, the local Euler factor
`(1 + χ(q) · q^{k-1} · (q^{-s})²)⁻¹` (as in
`Newform.eulerFactor_stripped` good-prime branch) coincides with the
Dirichlet-quotient form
`(1 - χ(q) · q^{-s'}) · (1 - χ²(q) · q^{-2s'})⁻¹` at `s' = 2s - k + 1`.

This is the pointwise step that identifies each good-prime factor of
`Newform.lSeries_stripped_hasProd_eulerFactor` with a ratio of two
Mathlib-Dirichlet Euler factors (from
`DirichletCharacter.LSeries_eulerProduct_hasProd`), opening the door
to the global Dirichlet-quotient expression.

Proof: rearrange powers using `Complex.cpow_mul_nat` +
`Complex.cpow_add` to fold `q^{k-1} · (q^{-s})² = q^{-s'}`, then apply
`Newform.eulerFactor_dirichlet_quotient_form` (T101) with
`x = χ(q) · q^{-s'}`.

Hypotheses `h_pos`, `h_neg` ensure `1 ± x ≠ 0` (automatic when
`‖x‖ < 1`, e.g. from `Newform.norm_eulerFactor_argument_lt_one`). -/
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
    have h1 : ((q : ℂ) ^ (-s)) ^ 2 = (q : ℂ) ^ (-s * 2) := by
      rw [← Complex.cpow_mul_nat]; rfl
    rw [h1,
      show ((q : ℂ) ^ (k - 1) : ℂ) = (q : ℂ) ^ ((k - 1 : ℤ) : ℂ) from
        (Complex.cpow_intCast _ _).symm,
      ← Complex.cpow_add _ _ hq_ne]
    congr 1; push_cast; ring
  have h_sq : (χ ^ 2 : ℂ) * (q : ℂ) ^ (-(2 * (2 * s - k + 1))) =
      (χ * (q : ℂ) ^ (-(2 * s - k + 1))) ^ 2 := by
    rw [mul_pow,
      show ((q : ℂ) ^ (-(2 * s - k + 1))) ^ 2 = (q : ℂ) ^ (-(2 * s - k + 1) * 2) from by
        rw [← Complex.cpow_mul_nat]; rfl]
    congr 1; ring
  rw [show (1 + χ * (q : ℂ) ^ (k - 1) * ((q : ℂ) ^ (-s)) ^ 2 : ℂ) =
      1 + χ * ((q : ℂ) ^ (k - 1) * ((q : ℂ) ^ (-s)) ^ 2) from by ring,
    h_pow, h_sq]
  -- Now goal: (1 + y)⁻¹ = (1 - y) * (1 - y²)⁻¹ where y = χ * q^{-s'}.
  exact Newform.eulerFactor_dirichlet_quotient_form
    (χ * (q : ℂ) ^ (-(2 * s - k + 1))) h_pos h_neg

/-! ### Compound HasProd: stripped × Dirichlet (T103, second deliverable)

The cleanest way to bridge T099's `lSeries_stripped_hasProd_eulerFactor`
and Mathlib's `DirichletCharacter.LSeries_eulerProduct_hasProd` (without
the `CommGroup` requirement of `HasProd.div`) is to **multiply** them:
the resulting compound HasProd has factor function
`eulerFactor_stripped p · (1 - χ̃(p) · p^{-s'})⁻¹`, which **telescopes**
at good primes via `Newform.eulerFactor_good_prime_eq_dirichlet_quotient`
into the Mathlib χ̃² Euler factor `(1 - χ̃²(p) · p^{-2s'})⁻¹`. -/

/-- **Compound HasProd identity** combining the T099 stripped Euler
product with the Mathlib Dirichlet Euler product for the lifted
character `χ̃ = dirichletLift χ` at the substituted point
`s' = 2s - k + 1`.

This is the global bridge consumed by the final Dirichlet-quotient
contradiction: at "good" primes (i.e. `p` coprime to `N` and `p ∉ S`),
the compound factor reduces to the Mathlib χ̃² Euler factor
`(1 - χ̃²(p) · p^{-2s'})⁻¹` (Diamond–Shurman §5.9, via the local
identification `Newform.eulerFactor_good_prime_eq_dirichlet_quotient`).
At `p ∣ N`, both factors are `1`.  At `p ∈ S` coprime to `N`, the
compound is the residual product times the local Dirichlet factor —
this is the finite "S correction" that must be tracked in the final
contradiction step.

Hypotheses inherited from T099 + the Mathlib Dirichlet Euler product
hypothesis `1 < (2*s - k + 1).re`. -/
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
      (fun p : Nat.Primes =>
        Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹)
      (LSeries f.lCoeff_stripped s *
        LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1)) :=
  (f.lSeries_stripped_hasProd_eulerFactor χ hfχ S h_bad hs h_geom).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) hs')

/-- **Pointwise factor identification at good primes.**  The compound
factor `eulerFactor_stripped p · (1 - χ̃(p) · p^{-s'})⁻¹` from
`Newform.lSeries_stripped_mul_dirichlet_hasProd` reduces, at every
prime `q.Prime` coprime to `N` with `q ∉ S` and `f.lCoeff q = 0`, to
the Mathlib χ̃² Euler factor `(1 - χ̃²(q) · q^{-2s'})⁻¹` — exactly the
local Euler factor of `LSeries χ̃² (2s')`.

Proof: chain T103's
`Newform.eulerFactor_good_prime_eq_dirichlet_quotient` (local Dirichlet
quotient form `(1 - x) · (1 - x²)⁻¹`) with the algebraic collapse
`(1 - x) · (1 - x²)⁻¹ · (1 - x)⁻¹ = (1 - x²)⁻¹ = (1 - x)⁻¹ · (1 + x)⁻¹`,
i.e. `(1 + x)⁻¹ · (1 - x)⁻¹ = (1 - x²)⁻¹`. -/
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
  -- Unfold eulerFactor_stripped at the good-prime branch.
  unfold Newform.eulerFactor_stripped
  have h_dvd : ¬ ((⟨q, hq⟩ : Nat.Primes) : ℕ) ∣ N := by
    intro h_div
    exact absurd ((Nat.Prime.coprime_iff_not_dvd hq).mp hqN) (not_not.mpr h_div)
  rw [dif_neg h_dvd, if_neg hqS]
  -- Now goal: (1 + χ(q) · q^{k-1} · (q^{-s})²)⁻¹ * (1 - χ̃(q) · q^{-s'})⁻¹
  --         = (1 - χ̃²(q) · q^{-2s'})⁻¹.
  -- Apply T103's Dirichlet-quotient form to the LHS first factor.
  rw [Newform.eulerFactor_good_prime_eq_dirichlet_quotient hq.pos k s
        (χ (ZMod.unitOfCoprime q hqN) : ℂ) h_pos h_neg]
  -- Goal: (1 - χ · q^{-s'}) · (1 - χ² · q^{-2s'})⁻¹ · (1 - χ̃(q) · q^{-s'})⁻¹
  --     = (1 - χ̃²(q) · q^{-2s'})⁻¹
  -- The first (1 - χ · q^{-s'}) cancels with the third (1 - χ̃(q) · q^{-s'})⁻¹,
  -- since χ̃(q) = χ a where a = ZMod.unitOfCoprime q hqN.
  have h_chi_eq : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((q : ℕ) : ZMod N) =
      (χ (ZMod.unitOfCoprime q hqN) : ℂ) := by
    rw [show (((q : ℕ) : ZMod N)) =
        ((ZMod.unitOfCoprime q hqN : (ZMod N)ˣ) : ZMod N) from by
      simp [ZMod.coe_unitOfCoprime]]
    exact MulChar.ofUnitHom_coe χ (ZMod.unitOfCoprime q hqN)
  rw [h_chi_eq]
  -- Now: (1 - x) · (1 - x²)⁻¹ · (1 - x)⁻¹ = (1 - x²)⁻¹ where x = χ(...) · q^{-s'}.
  have h_ne : (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
      ((q : ℕ) : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 := h_neg
  field_simp

/-- **Pointwise factor identification at primes dividing the level.**  For
a prime `p ∣ N`, the compound factor `eulerFactor_stripped p · (1 - χ̃(p) ·
p^{-s'})⁻¹` equals `1`, since `eulerFactor_stripped p = 1`
(`Newform.tsum_term_lCoeff_stripped_pow_of_dvd`) and
`χ̃(p) = 0` (the lift `MulChar.ofUnitHom χ` extends by zero on
non-units, and `(p : ZMod N)` is non-unit when `p ∣ N`).

Combined with `eulerFactor_stripped_mul_dirichlet_at_good_prime`, this
covers the two "non-`S`" branches of the case split in the value
identity. -/
theorem Newform.eulerFactor_stripped_mul_dirichlet_at_dvd (f : Newform N k)
    (χ : (ZMod N)ˣ →* ℂˣ) (S : Finset ℕ)
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ N) (s : ℂ) :
    Newform.eulerFactor_stripped f χ S s ⟨p, hp⟩ *
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹ = 1 := by
  -- Unfold eulerFactor_stripped at the dvd branch.
  unfold Newform.eulerFactor_stripped
  rw [dif_pos hp_dvd]
  -- Show dirichletLift χ ((p : ℕ) : ZMod N) = 0.
  have h_chi_zero : (Newform.dirichletLift χ : DirichletCharacter ℂ N)
      ((p : ℕ) : ZMod N) = 0 := by
    apply (Newform.dirichletLift χ : DirichletCharacter ℂ N).map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    intro h_cop
    exact (hp.coprime_iff_not_dvd.mp h_cop) hp_dvd
  rw [h_chi_zero, zero_mul, sub_zero, inv_one, mul_one]

omit [NeZero N] in
/-- **Pointwise factor identification at primes dividing the level
(squared character).**  For a prime `p ∣ N`, the squared Mathlib
χ̃² Euler factor `(1 - χ̃²(p) · p^{-2s'})⁻¹` equals `1`. -/
theorem Newform.dirichletLift_sq_euler_factor_at_dvd (χ : (ZMod N)ˣ →* ℂˣ)
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ N) (s : ℂ) :
    (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ = 1 := by
  have h_chi_zero : (Newform.dirichletLift χ : DirichletCharacter ℂ N)
      ((p : ℕ) : ZMod N) = 0 := by
    apply (Newform.dirichletLift χ : DirichletCharacter ℂ N).map_nonunit
    rw [ZMod.isUnit_iff_coprime]
    intro h_cop
    exact (hp.coprime_iff_not_dvd.mp h_cop) hp_dvd
  -- (χ * χ) p = (χ p) * (χ p) = 0 * 0 = 0.
  rw [show ((Newform.dirichletLift χ * Newform.dirichletLift χ :
      DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) =
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) from
      MulChar.mul_apply _ _ _]
  rw [h_chi_zero, mul_zero, zero_mul, sub_zero, inv_one]

/-! ### T108 final value identity -/

/-- **T108 — final value identity.**  Under the bad-prime-zero hypothesis
(`f.lCoeff q = 0` for every prime `q.Coprime N` with `q ∉ S`), the
T103 compound HasProd identifies via `HasProd.unique` against the Mathlib
χ̃² Dirichlet Euler product, with the discrepancy at `S`-primes captured
as an explicit Finset correction:

```
(LSeries f.lCoeff_stripped s · LSeries χ̃ s') ·
  (∏ p ∈ T, (1 - χ̃²(p) · p^{-2s'})⁻¹) =
LSeries χ̃² (2s') ·
  (∏ p ∈ T, eulerFactor_stripped p · (1 - χ̃(p) · p^{-s'})⁻¹)
```

with `s' = 2s - k + 1` and `T : Finset Nat.Primes` the set of primes in
`S` coprime to `N`.

This is the algebraic value identity called for by Diamond–Shurman §5.9
and Miyake §4.5.16, with the analytic ingredients (Mathlib Dirichlet
Euler products on `Re s' > 1` and `Re (2s') > 1`) supplied as
hypotheses.  The remaining contradiction step (POST-3i) plugs in
`Mathlib.NumberTheory.LSeries.Nonvanishing.LFunction_ne_zero_of_one_le_re`
to dispose of the `LSeries χ̃ s'` and `LSeries χ̃² (2s')` factors and
extracts a coefficient contradiction against `f.lCoeff_stripped 1 = 1`
(via `Newform.lSeries_stripped_ne_zero` from T101).

The hypothesis `hT_iff` characterises `T` as exactly the primes in `S`
coprime to `N`. -/
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
        (LSeries (fun n =>
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) n) (2 * s - k + 1)) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) =
      (LSeries (fun n => ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) n) (2 * (2 * s - k + 1))) *
        (∏ p ∈ T,
          Newform.eulerFactor_stripped f χ S s p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) := by
  classical
  -- Unpack the two HasProds.
  have h_compound :=
    f.lSeries_stripped_mul_dirichlet_hasProd χ hfχ S h_bad hs hs' h_geom
  have h_chi_sq := DirichletCharacter.LSeries_eulerProduct_hasProd
    ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) hs''
  -- Define the two correction functions, supported on T.
  set g₁ : Nat.Primes → ℂ := fun p =>
    Newform.eulerFactor_stripped f χ S s p *
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹ with hg₁_def
  set g₂ : Nat.Primes → ℂ := fun p =>
    (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ with hg₂_def
  -- g₁ = g₂ outside T.
  have h_eq_outside_T : ∀ p ∉ T, g₁ p = g₂ p := by
    intro p hp_notT
    -- Convert p to ⟨↑p, p.prop⟩ for compatibility with helper lemmas.
    have h_p_eq : (⟨(p : ℕ), p.prop⟩ : Nat.Primes) = p := Subtype.eta _ _
    -- Either p ∣ N or p ∉ S coprime to N.
    by_cases h_dvd : (p : ℕ) ∣ N
    · -- p ∣ N case: both = 1.
      rw [hg₁_def, hg₂_def]
      simp only
      rw [show Newform.eulerFactor_stripped f χ S s p =
          Newform.eulerFactor_stripped f χ S s ⟨(p : ℕ), p.prop⟩ from by rw [h_p_eq]]
      rw [Newform.eulerFactor_stripped_mul_dirichlet_at_dvd f χ S p.prop h_dvd s,
        Newform.dirichletLift_sq_euler_factor_at_dvd χ p.prop h_dvd s]
    · -- p coprime to N: p ∉ S (else p ∈ T contradiction).
      have hpN : Nat.Coprime (p : ℕ) N :=
        (Nat.Prime.coprime_iff_not_dvd p.prop).mpr h_dvd
      have hp_notS : (p : ℕ) ∉ S := by
        intro hpS
        exact hp_notT ((hT_iff p).mpr ⟨hpS, hpN⟩)
      have ⟨h_pos, h_neg⟩ := h_pos_neg (p : ℕ) p.prop hpN hp_notS
      rw [hg₁_def, hg₂_def]
      simp only
      have h_good := f.eulerFactor_stripped_mul_dirichlet_at_good_prime χ hfχ S h_bad
        p.prop hpN hp_notS s h_pos h_neg
      -- Translate from ⟨↑p, p.prop⟩ form to p form using Subtype.eta.
      rw [show Newform.eulerFactor_stripped f χ S s p =
          Newform.eulerFactor_stripped f χ S s ⟨(p : ℕ), p.prop⟩ from by rw [h_p_eq]]
      rw [h_good]
      -- Now: (1 - (dirichletLift χ) ↑↑p ^ 2 * ...)⁻¹
      --    = (1 - (dirichletLift χ * dirichletLift χ) ↑↑p * ...)⁻¹
      rw [show ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) =
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) ^ 2 from by
          rw [pow_two]; exact MulChar.mul_apply _ _ _]
  -- Define the two corrections (each supported on T).
  let corr₁ : Nat.Primes → ℂ := fun p => if p ∈ T then g₂ p else 1
  let corr₂ : Nat.Primes → ℂ := fun p => if p ∈ T then g₁ p else 1
  have h_corr₁_supp : ∀ p ∉ T, corr₁ p = 1 := fun p hp => if_neg hp
  have h_corr₂_supp : ∀ p ∉ T, corr₂ p = 1 := fun p hp => if_neg hp
  have h_corr₁_prod : HasProd corr₁ (∏ p ∈ T, corr₁ p) :=
    hasProd_prod_of_ne_finset_one h_corr₁_supp
  have h_corr₂_prod : HasProd corr₂ (∏ p ∈ T, corr₂ p) :=
    hasProd_prod_of_ne_finset_one h_corr₂_supp
  have h_corr₁_eq : (∏ p ∈ T, corr₁ p) = ∏ p ∈ T, g₂ p :=
    Finset.prod_congr rfl (fun p hp => if_pos hp)
  have h_corr₂_eq : (∏ p ∈ T, corr₂ p) = ∏ p ∈ T, g₁ p :=
    Finset.prod_congr rfl (fun p hp => if_pos hp)
  -- Combine via HasProd.mul.
  have h_left : HasProd (fun p => g₁ p * corr₁ p)
      (LSeries f.lCoeff_stripped s *
        LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1) *
        (∏ p ∈ T, corr₁ p)) := h_compound.mul h_corr₁_prod
  have h_right : HasProd (fun p => g₂ p * corr₂ p)
      (LSeries (fun n => ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) n) (2 * (2 * s - k + 1)) *
        (∏ p ∈ T, corr₂ p)) := h_chi_sq.mul h_corr₂_prod
  -- Pointwise equality of the corrected functions.
  have h_pointwise : (fun p => g₁ p * corr₁ p) = (fun p => g₂ p * corr₂ p) := by
    funext p
    by_cases hp : p ∈ T
    · show g₁ p * (if p ∈ T then g₂ p else 1) =
        g₂ p * (if p ∈ T then g₁ p else 1)
      rw [if_pos hp, if_pos hp]; ring
    · show g₁ p * (if p ∈ T then g₂ p else 1) =
        g₂ p * (if p ∈ T then g₁ p else 1)
      rw [if_neg hp, if_neg hp, mul_one, mul_one]
      exact h_eq_outside_T p hp
  rw [h_pointwise] at h_left
  have h_unique := h_left.unique h_right
  rw [h_corr₁_eq, h_corr₂_eq] at h_unique
  exact h_unique

/-! ### T111 non-vanishing helpers and divided value identity -/

/-- **Local Dirichlet Euler factor non-vanishing.**  For a Mathlib
`DirichletCharacter ℂ N`, every prime `p`, and every `s' ∈ ℂ` with
`Re s' > 1`, the local Euler factor `(1 - χ(p) · p^{-s'})⁻¹` is non-zero.

Proof: `‖χ(p) · p^{-s'}‖ ≤ ‖χ(p)‖ · p^{-Re s'} ≤ 1 · p^{-Re s'} < 1`
(using `DirichletCharacter.norm_le_one` and
`Real.rpow_lt_one_of_one_lt_of_neg`), so `1 - χ(p) · p^{-s'} ≠ 0`. -/
lemma Newform.dirichletLift_eulerFactor_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) {s' : ℂ}
    (hs' : 1 < s'.re) :
    (1 - χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s'))⁻¹ ≠ 0 := by
  apply inv_ne_zero
  have hp_pos : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpr_pos : (0 : ℝ) < (p : ℝ) := lt_trans one_pos hp_pos
  have h_norm : ‖χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s')‖ < 1 := by
    rw [norm_mul]
    have h_chi : ‖χ ((p : ℕ) : ZMod N)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have h_pow : ‖((p : ℕ) : ℂ) ^ (-s')‖ = (p : ℝ) ^ (-s'.re) := by
      rw [show ((p : ℕ) : ℂ) ^ (-s') = ((p : ℝ) : ℂ) ^ (-s') from by push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hpr_pos]
      simp
    rw [h_pow]
    calc ‖χ ((p : ℕ) : ZMod N)‖ * (p : ℝ) ^ (-s'.re)
        ≤ 1 * (p : ℝ) ^ (-s'.re) := by
          apply mul_le_mul_of_nonneg_right h_chi; positivity
      _ = (p : ℝ) ^ (-s'.re) := one_mul _
      _ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_pos (by linarith)
  intro h_eq
  have h_eq_one : χ ((p : ℕ) : ZMod N) * ((p : ℕ) : ℂ) ^ (-s') = 1 := by
    have := sub_eq_zero.mp h_eq; rw [this]
  rw [h_eq_one] at h_norm
  simp at h_norm

/-- **Finite product of χ̃² Mathlib-Dirichlet local Euler factors over a
finite Finset of primes is non-zero**, on `Re s' > 1` (hence
`Re (2s') > 2 > 1` for the χ̃² Mathlib Euler factor).  Direct
consequence of `Newform.dirichletLift_eulerFactor_ne_zero` applied to
each factor. -/
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

/-- **Divided form of the T108 value identity.**  Combining the T108
identity `(LSeries f.lCoeff_stripped s) · (LSeries χ̃ s') ·
(∏ T χ̃²-factor) = (LSeries χ̃² (2s')) · (∏ T compound-factor)` with
non-vanishing of both `LSeries χ̃ s'` (via Mathlib's
`DirichletCharacter.LSeries_ne_zero_of_one_lt_re`) and the finite
χ̃² Euler product correction (via
`Newform.prod_dirichletLift_sq_eulerFactor_ne_zero`), the cusp form
L-series is **explicitly determined** by the Dirichlet quotient
modulo the finite `S`-correction:

```
LSeries f.lCoeff_stripped s =
  (LSeries χ̃² (2s') · ∏ T compound-factor) /
  (LSeries χ̃ s' · ∏ T χ̃²-factor)
```

This is the analytic form in which the bad-primes-zero hypothesis
constrains `LSeries f.lCoeff_stripped s` to be a specific Dirichlet-
quotient expression.

**Important math caveat.**  This value identity at any single `s` does
not by itself yield `Newform.exists_nonzero_prime_eigenvalue`: the LHS
and RHS both being nonzero (or both zero) at `s` is consistent — a
single point identity is unforced by either function's structure.  The
classical contradiction (Diamond–Shurman §5.9 / Miyake Thm 4.5.16)
requires comparing the **analytic continuation** of the LHS (the
cusp-form L-series, which extends to an entire function on ℂ via
Hecke 1936) against the meromorphic continuation of the RHS Dirichlet
quotient.  Hecke's analytic continuation of cusp-form L-series is
**not yet in Mathlib**; landing it (or an equivalent functional
equation / pole-tracking statement for `LSeries f.lCoeff_stripped`)
is the precise remaining gap. -/
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
      (LSeries (fun n => ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) n) (2 * (2 * s - k + 1)) *
       (∏ p ∈ T,
          Newform.eulerFactor_stripped f χ S s p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹)) /
      (LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1) *
       (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹)) := by
  have h_id := f.lSeries_stripped_value_identity χ hfχ S h_bad hs hs' hs''
    h_geom T hT_iff h_pos_neg
  have h_LB_ne : LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
      (2 * s - k + 1) ≠ 0 :=
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hs'
  have h_C_ne :
    (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
        DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) ≠ 0 :=
    Newform.prod_dirichletLift_sq_eulerFactor_ne_zero χ T hs''
  -- A · B · C = D · E ⟹ A = D · E / (B · C).
  have h_BC_ne :
    LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
        (2 * s - k + 1) *
      (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) ≠ 0 :=
    mul_ne_zero h_LB_ne h_C_ne
  rw [eq_div_iff h_BC_ne]
  -- Goal: LSeries f.lCoeff_stripped s * (LSeries χ̃ s' * ∏ T χ̃²-factor) = ...
  -- h_id: LSeries f.lCoeff_stripped s * LSeries χ̃ s' * ∏ T χ̃²-factor = ...
  -- These differ by associativity.
  rw [← mul_assoc]
  exact h_id

/-! ### T129 special-point specialization of T111 -/

/-- **Special evaluation point** `s₀ = ((k : ℝ) / 2 + 2 : ℂ)` for the
T111 Dirichlet-quotient value identity.  At this concrete real point,
the three real-part hypotheses `hs`, `hs'`, `hs''` of
`Newform.lSeries_stripped_eq_dirichlet_quotient_value` reduce to
`2 > 1`, `Re (2 · s₀ - k + 1) = 5 > 1`, `Re (2 · (2 · s₀ - k + 1)) = 10 > 1`
respectively, and the geometric / pole non-vanishing hypotheses
`h_geom` / `h_pos_neg` hold for every prime `q ≥ 2` coprime to `N`
(since `‖χ(q) · q^{-5}‖ ≤ q^{-5} ≤ 1/32 < 1`). -/
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

/-- **T129 — T111 value identity specialised at the special point
`s₀ = k/2 + 2`.**  Discharges the three real-part hypotheses together
with the geometric / pole non-vanishing side conditions of
`Newform.lSeries_stripped_eq_dirichlet_quotient_value`, leaving only
the bad-prime-zero hypothesis `h_bad` and the finset characterisation
`hT_iff` as consumer obligations.

The evaluation at `s₀ = k/2 + 2` gives image point `s' = 5` (real) and
doubled point `2s' = 10`, both with real part `> 1`, so the Mathlib
Dirichlet non-vanishing `LSeries_ne_zero_of_one_lt_re` applies.  The
geometric bound `‖χ(q) · q^{-5}‖ ≤ q^{-5} < 1` for `q ≥ 2` is
automatic, so the quotient form of T111 specialises to a concrete
single-point value identity.

This is a **strictly reducing** helper toward
`Newform.exists_nonzero_prime_eigenvalue`: per the T111 docstring, a
single-point identity is mathematically not enough to close the full
contradiction (that requires Hecke's analytic continuation of the
cusp-form L-series, not yet in Mathlib).  The helper is retained for
reuse by any downstream approach that combines this value identity
with analytic-continuation / pole-tracking input. -/
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
      (LSeries (fun n => ((Newform.dirichletLift χ * Newform.dirichletLift χ :
          DirichletCharacter ℂ N)) n)
          (2 * (2 * Newform.specialPoint k - (k : ℂ) + 1)) *
       (∏ p ∈ T,
          Newform.eulerFactor_stripped f χ S (Newform.specialPoint k) p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * Newform.specialPoint k - (k : ℂ) + 1)))⁻¹)) /
      (LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
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

Signature.  The explicit `χ` and `hfχ` arguments route `f.lCoeff`
multiplicativity / recurrence (`Newform.lCoeff_isHeckeCoefficientSequence`,
`Newform.eigenvalue_eq_coeff`) through the Fourier-coefficient bridge
that requires a specific Nebentypus.  Downstream callers
(`strongMultiplicityOne`) already have both in scope.

Current status (`sorry`).  **This statement requires genuine analytic
input beyond `IsHeckeCoefficientSequence` alone.**  The counterexample
sequence `a 0 = 0, a 1 = 1, a p = 0` for every prime `p`, extended by
`mul_coprime` / `recur` (giving `a (p^{2j+1}) = 0`,
`a (p^{2j}) = (−χ(p))^j p^{j(k-1)}`), satisfies all four fields of
`IsHeckeCoefficientSequence` yet has every prime coefficient equal to
zero; the abstract predicate therefore does **not** imply
prime-nonvanishing.  A correct proof must use the fact that `f` is an
honest cusp form.

Available reusable infrastructure (T031 slice; this file):
* `Newform.lCoeff_eq_modularForms_lCoeff` — `f.lCoeff` is the
  generic period-1 cusp-form Fourier sequence
  `ModularForms.lCoeff f.toCuspForm`.  Identifies the strict-width-at-
  `∞` `1` (via `ModularForms.strictWidthInfty_Gamma1_mapGL`) with the
  `qExpansion 1` convention used by `Newform.lCoeff`, dissolving the
  earlier `strictWidthInfty = N` confusion.
* `Newform.lSeriesSummable` — absolute summability of `LSeries f.lCoeff`
  on `Re s > k/2 + 1` (`ModularForms.lSeriesSummable_of_cuspForm`).
* `Newform.lSeries_eq_iff` — coefficient injectivity for the L-series of
  newforms (`ModularForms.lSeries_eq_iff_cuspForm`).
* `Newform.lSeries_ne_zero` — `LSeries f.lCoeff ≠ 0`, from
  `f.lCoeff 1 = 1` and `ModularForms.lSeries_ne_zero_of_lCoeff_ne_zero`.

Sequence-level data (combinatorial bundle, retained):
* `Newform.lCoeff_isHeckeCoefficientSequence` — the four arithmetic
  fields `zero`, `one`, `mul_coprime`, `recur` of `f.lCoeff`.

Expected proof route (Diamond–Shurman §5.9 / Miyake §4.5):

1. Assume for contradiction `f.lCoeff q = 0` for every prime
   `q.Coprime N` with `q ∉ S`.
2. Use `Newform.lCoeff_isHeckeCoefficientSequence.recur` to compute the
   prime-power coefficients explicitly: for such `q`,
   `f.lCoeff (q ^ (2j + 1)) = 0` and
   `f.lCoeff (q ^ (2j)) = (-χ(q))^j · q^{j(k-1)}`.  Combined with
   `mul_coprime`, this expresses the formal Euler product
   `∑ f.lCoeff n / n^s` as a rational quotient of Dirichlet
   L-functions (`DirichletCharacter.LSeries_eulerProduct_hasProd` from
   `Mathlib.NumberTheory.EulerProduct.DirichletLSeries`).
3. Compare against `LSeries f.lCoeff` via `Newform.lSeries_eq_iff` /
   `Newform.lSeries_ne_zero`: the rational quotient of Dirichlet
   L-functions is not identically zero on its domain of analytic
   continuation, but it has poles / zeros pattern incompatible with the
   entire cusp-form L-series of a non-zero newform.

T089 sequence-level + analytic-level slice (this file +
`LFunction.lean`).  After T089 the local pieces are landed sorry-free:

* `IsHeckeCoefficientSequence.coeff_prime_pow_odd_eq_zero_of_a_p_zero`
  — odd prime-power coefficients vanish.
* `IsHeckeCoefficientSequence.coeff_prime_pow_even_eq_of_a_p_zero` —
  even prime-power closed form
  `a (q^(2j)) = (-χ(q) · q^{k-1})^j`.
* `IsHeckeCoefficientSequence.coeff_prime_pow_eq_of_a_p_zero` —
  combined `if Even r` form (consumed downstream).
* `ModularForms.tsum_alternating_pow_eq` — the analytic identity
  `Σ_r [r % 2 = 0] (-c)^(r/2) · x^r = (1 + c · x²)⁻¹` on
  `‖c · x²‖ < 1`.  Specialised at `c = (χ q : ℂ) · (q : ℂ)^(k-1)`,
  `x = (q : ℂ)^(-s)` this is the formal local Euler factor at a
  bad prime.

T093 stripped-sequence + per-prime Euler factor slice (this file):

* `Newform.lCoeff_stripped` — `n ↦ if n.Coprime N then f.lCoeff n
  else 0`, the part of `f.lCoeff` consumable by Mathlib's
  `EulerProduct.eulerProduct_hasProd` (which requires FULL coprime
  multiplicativity, not the "both coprime to N" restricted form).
* `Newform.lCoeff_stripped_zero` / `_one` — boundary conditions.
* `Newform.lCoeff_stripped_mul_coprime` — full coprime multiplicativity
  (works at arbitrary `m, n` with `m.Coprime n`, automatically zero
  on the off-coprime-to-`N` half by definition).
* `Newform.norm_lCoeff_stripped_le` — pointwise norm domination.
* `Newform.lSeriesSummable_stripped` — absolute summability of
  `LSeries f.lCoeff_stripped` on `Re s > k/2 + 1` by domination.
* `Newform.tsum_lCoeff_pow_mul_eq_eulerFactor` — per-prime local
  Euler factor at a "bad" prime `q` (where `f.lCoeff q = 0`):
  `∑ᵣ f.lCoeff (qʳ) · xʳ = (1 + χ(q) · q^{k-1} · x²)⁻¹`.

T097 global Euler product collapse (this file):

* `Newform.lSeries_stripped_hasProd` — bare Euler product
  `LSeries f.lCoeff_stripped s = ∏_p (∑ᵣ LSeries.term s (pʳ))`
  on `Re s > k/2 + 1`, via `EulerProduct.eulerProduct_hasProd` with
  the four T093 hypotheses (`lCoeff_stripped_one`, `_zero`,
  `_mul_coprime`, `lSeriesSummable_stripped`).
* `Newform.tsum_term_lCoeff_stripped_pow_of_dvd` — local Euler factor
  at a prime `p ∣ N` is identically `1`, since the stripped sequence
  vanishes at every positive power of `p`.
* `Newform.tsum_term_lCoeff_stripped_pow_of_good_prime` — local Euler
  factor at a "good" prime `q` (prime, coprime to `N`, `f.lCoeff q = 0`)
  is `(1 + χ(q) · q^{k-1-2s})⁻¹`, via
  `Newform.tsum_lCoeff_pow_mul_eq_eulerFactor` plus the cpow swap
  `((q : ℂ)^e)^(-s) = ((q : ℂ)^(-s))^e`.

T099 combined Dirichlet quotient identification (this file):

* `Newform.eulerFactor_stripped` — definitional case-split for the
  identified local factor at each prime: `1` if `p ∣ N`, the residual
  `∑ᵣ LSeries.term s (pʳ)` if `p ∈ S` coprime to `N`, and the
  Dirichlet-quotient form `(1 + χ(p) · p^{k-1} · (p^{-s})²)⁻¹` if
  `p ∉ S` coprime to `N` (the "good" case).
* `Newform.lSeries_stripped_hasProd_eulerFactor` — the combined
  HasProd identification:
  `HasProd (eulerFactor_stripped f χ S s) (LSeries f.lCoeff_stripped s)`.
  Direct application of `HasProd.congr_fun` to T097's
  `lSeries_stripped_hasProd`, dispatching to T097's three local-factor
  lemmas in each case.

T101 Dirichlet character lift and analytic bridges (this file):

* `Newform.dirichletLift` — `MulChar.ofUnitHom χ : DirichletCharacter ℂ N`,
  the lift of χ that connects to Mathlib's
  `DirichletCharacter.LSeries_eulerProduct_hasProd` /
  `LFunction_ne_zero_of_one_le_re` API.
* `Newform.dirichletLift_apply_unit` — value formula on units.
* `Newform.norm_chi_unit_eq_one` — `‖(χ a : ℂ)‖ = 1` for `a : (ZMod N)ˣ`,
  via finite-order ⇒ root of unity.
* `Newform.norm_eulerFactor_argument_lt_one` — geometric convergence
  `‖χ(q) · q^{k-1} · (q^{-s})²‖ < 1` for `q.Prime` coprime to `N` and
  `Re s > (k-1)/2` (in particular on `Re s > k/2 + 1`).
* `Newform.eulerFactor_dirichlet_quotient_form` — the algebraic identity
  `(1 + x)⁻¹ = (1 - x) · (1 - x²)⁻¹` (in ℂ, requiring `1 ± x ≠ 0`),
  the local rewrite that exhibits the formal Dirichlet quotient
  `1/L(s', χ̃) · L(2s', χ̃²)` shape at each good prime.
* `Newform.lSeries_stripped_ne_zero` — stripped-sequence analogue of
  T031's `Newform.lSeries_ne_zero`, via Mathlib's `LSeries_eq_zero_iff`
  plus the finite abscissa from `Newform.lSeriesSummable_stripped`.

T103 local Dirichlet quotient identification (this file):

* `Newform.eulerFactor_good_prime_eq_dirichlet_quotient` —
  pointwise rewrite of the good-prime Euler factor as a ratio of
  Mathlib-Dirichlet local Euler factors:
  `(1 + χ(q) · q^{k-1} · (q^{-s})²)⁻¹ = (1 - χ(q) · q^{-s'}) ·
   (1 - χ²(q) · q^{-2s'})⁻¹`, where `s' = 2s - k + 1`.  Pure
  algebraic + `Complex.cpow_mul_nat`/`cpow_add` rearrangement, plus
  `Newform.eulerFactor_dirichlet_quotient_form` (T101).

Remaining blocker (next ticket): **Global Dirichlet quotient + final
contradiction.**

T103's identification is per-prime (for a single q).  Lifting to a
global `HasProd` against Mathlib's
`DirichletCharacter.LSeries_eulerProduct_hasProd` is **blocked at the
Mathlib API level**: the cleanest route requires `HasProd.div` /
`HasProd.inv` (`L(2s', χ̃²) / L(s', χ̃)` as a HasProd), but Mathlib's
`HasProd.div` / `HasProd.inv` (`Mathlib.Topology.Algebra.InfiniteSum.Group`)
require `[CommGroup α]` — and `α = ℂ` is a `CommGroupWithZero`, not a
`CommGroup`.

Workarounds (all ~150–250 LOC; suited to a follow-up ticket):

* **(a) ℂˣ-lifting**: lift each non-zero local factor to `ℂˣ`, do the
  division there, then map back.  Requires showing each factor is
  non-zero (from `‖xₚ‖ < 1` ⇒ `1 ± xₚ ≠ 0`) and threading `ℂˣ`-valued
  HasProds.
* **(b) `Multipliable` + `tprod` algebra**: prove
  `Multipliable (fun p => (1 + χ̃(p) · p^{-s'})⁻¹)` (via convergence
  of `∑ ‖xₚ‖`), then equate `tprod`s using `tprod_mul`,
  `Multipliable.tprod_eq` rather than `HasProd.div`.
* **(c) Direct contradiction at a finite point**: rather than the
  global infinite product, evaluate both sides of T099's
  `lSeries_stripped_hasProd_eulerFactor` at a specific `s` with
  `Re s = k/2 + 2` and use `HasProd.unique` to extract a value
  identity, then compare with `Newform.lSeries_stripped_ne_zero`.

After whichever workaround: choose `s` real with `Re s = k/2 + 2` (so
`Re s' = 3 > 1`), then `LSeries χ̃ 3` and `LSeries χ̃² 6` are non-zero
by Mathlib `LSeries_ne_zero_of_one_lt_re`.  Combined with the T097/T099
identification, this forces `LSeries f.lCoeff_stripped s = 0` (or a
matching coefficient identity), contradicting
`Newform.lSeries_stripped_ne_zero`.

**T132 conditional interface.**  The exact missing analytic input is
Hecke's analytic continuation / functional equation for the cusp-form
L-series (not yet available in Mathlib).  This obligation is
packaged as the named proposition `Newform.AnalyticContradiction`
(below, T132); any proof of that proposition closes this theorem via
`Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction`,
and the downstream SMO theorem is likewise available conditionally as
`strongMultiplicityOne_of_analyticContradiction`. -/
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

This strengthens `newform_unique` by allowing finitely many exceptional primes.
The proof reduces to `newform_unique` using coprime multiplicativity of
eigenvalues and cancellation: for each `n ∈ S`, pick a suitable prime `q ∉ S`
with `λ_q ≠ 0`, then `λ_{nq}(f) = λ_n(f) λ_q(f) = λ_n(g) λ_q(g) = λ_{nq}(g)`,
and cancel `λ_q`.

**Dependencies**: `newform_unique`, `eigenvalue_coprime_mul`,
`exists_nonzero_prime_eigenvalue` (the last is sorry'd pending an L-function
non-vanishing argument; see its docstring). -/
theorem strongMultiplicityOne
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)  -- finite exceptional set
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  -- Reduce to newform_unique by extending eigenvalue agreement from
  -- "all coprime n outside S" to "all coprime n".
  refine newform_unique f g χ hfχ hgχ ?_
  intro n hn
  by_cases hn_S : n.val ∈ S
  · -- Strategy: pick a prime `q` avoiding `S`, the divisors `s / n` for `s ∈ S`,
    -- and the prime factors of `n`. Then `q` is coprime to `n`, `q ∉ S`,
    -- `n * q ∉ S`, and `λ_q(f) ≠ 0`. Coprime multiplicativity + cancellation
    -- transfers `λ_{nq}(f) = λ_{nq}(g)` into `λ_n(f) = λ_n(g)`.
    have hn_pos : 0 < n.val := n.pos
    -- Exclusion set: anything whose presence would break the argument.
    let bad : Finset ℕ := S ∪ S.image (· / n.val) ∪ n.val.primeFactors
    obtain ⟨q, hq_prime, hq_N, hq_notin, hq_ne⟩ :=
      Newform.exists_nonzero_prime_eigenvalue f χ hfχ bad
    have hq_pos : 0 < q := hq_prime.pos
    -- Unpack the exclusions.
    have hq_notin_S : q ∉ S := fun hqS => hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inl hqS))
    have hq_notin_img : q ∉ S.image (· / n.val) := fun h' => hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inr h'))
    have hq_nd_n : ¬ q ∣ n.val := fun hqn => hq_notin (by
      simp only [bad, Finset.mem_union, Nat.mem_primeFactors]
      exact Or.inr ⟨hq_prime, hqn, hn_pos.ne'⟩)
    have hn_coprime_q : Nat.Coprime n.val q :=
      ((hq_prime.coprime_iff_not_dvd).mpr hq_nd_n).symm
    -- `n * q ∉ S`: otherwise `q = (n*q)/n ∈ S.image (·/n)`.
    have hnq_notin_S : n.val * q ∉ S := fun hnqS => hq_notin_img <| by
      refine Finset.mem_image.mpr ⟨n.val * q, hnqS, ?_⟩
      exact Nat.mul_div_cancel_left _ hn_pos
    -- Package `q` and `n*q` as `ℕ+`.
    let q_pnat : ℕ+ := ⟨q, hq_pos⟩
    let nq_pnat : ℕ+ := ⟨n.val * q, Nat.mul_pos hn_pos hq_pos⟩
    have hnq_N : Nat.Coprime (n.val * q) N := hn.mul_left hq_N
    -- Apply the hypothesis at `q` and `n*q`.
    have hq_eq : f.eigenvalue q_pnat = g.eigenvalue q_pnat := h q_pnat hq_N hq_notin_S
    have hnq_eq : f.eigenvalue nq_pnat = g.eigenvalue nq_pnat := h nq_pnat hnq_N hnq_notin_S
    -- Multiplicativity: λ_{nq}(f) = λ_n(f) · λ_q(f); similarly for g.
    have hmul_f : f.eigenvalue nq_pnat = f.eigenvalue n * f.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul f n q_pnat hn hq_N hn_coprime_q χ hfχ
    have hmul_g : g.eigenvalue nq_pnat = g.eigenvalue n * g.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul g n q_pnat hn hq_N hn_coprime_q χ hgχ
    -- Combine and cancel `f.eigenvalue q_pnat ≠ 0`.
    have hcomb :
        f.eigenvalue n * f.eigenvalue q_pnat = g.eigenvalue n * f.eigenvalue q_pnat := by
      rw [← hmul_f, hnq_eq, hmul_g, hq_eq]
    exact mul_right_cancel₀ hq_ne hcomb
  · exact h n hn hn_S


end HeckeRing.GL2
