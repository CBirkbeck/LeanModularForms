/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.Modularforms.QExpansionSlash
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Miyake Theorem 4.6.5 — coprime sieving (POST-6c scaffold)

This file develops the **coprime sieving** construction of Miyake
§4.6.5, the third and final of the three sub-results feeding into
Miyake's Main Lemma 4.6.8 (which in turn is the engine of the Strong
Multiplicity One theorem 4.6.12).

## Mathematical statement

Given `f ∈ M_k(N, χ)` with `q`-expansion `f(τ) = Σ_{n ≥ 0} a_n qₙ(τ)`,
and a positive integer `L`, define the **coprime-sieved** series

  `g(τ) := Σ_{(n, L) = 1} a_n qₙ(τ)`,

keeping only the coefficients at indices coprime to `L`.  Miyake
Theorem 4.6.5 asserts that `g` is itself a modular form of weight `k`
at level `N · L²` (with the same Nebentypus character `χ` suitably
transported to the higher level).

The proof is by Möbius inversion over divisors of `L`:

  `g(τ) = Σ_{d ∣ L} μ(d) · a_d · f(d τ)`

(up to normalisation), and each summand `f(d τ) = f ∣[k] diag(d, 1)`
scales to a modular form at level `N · d² ∣ N · L²`, so the Möbius
combination stays at level `N · L²`.

## POST-6c deliverables (this scaffold)

* `sievedQExpansion` — the coefficient-filter at the `PowerSeries`
  level, kept independent of modular-form structure for easy reuse.
* `sievedQExpansion_coeff_coprime` and `_not_coprime` — coefficient
  identities (simp lemmas).
* `coprime_indicator_eq_sum_moebius` — the **Möbius indicator identity**
  for `[Nat.Coprime n L]` in terms of a divisor sum over
  `(gcd n L).divisors`, the arithmetic heart of Miyake 4.6.5.
* Full Miyake 4.6.5 target statement documented in a docstring block;
  proof deferred pending level-raise / Möbius-sum modular-form
  infrastructure.

## References

* Miyake, *Modular Forms*, Theorem 4.6.5.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.6.
-/

open scoped ModularForm ArithmeticFunction MatrixGroups
open ModularFormClass CongruenceSubgroup Matrix.SpecialLinearGroup

namespace HeckeRing.GL2.MainLemma

/-! ### Subgroup containment along `mapGL ℝ` (T131 own-route α)

The inclusion `Γ₁(M) ⊆ Γ₁(N)` (for `N ∣ M`, via `Gamma1_le_of_dvd`)
maps to a subgroup containment in `GL(2, ℝ)` after applying `mapGL ℝ`.
This is the bare structural lemma underlying the trace operator
`traceGamma1` (see `LeanModularForms/Eigenforms/TraceOperator.lean`)
and is used at numerous call sites in this file (descent of
`q`-expansion vanishing, level-raise q-expansion formulas,
inductive level-down arguments).  Packaging it as a single named
lemma both shortens those call sites and makes the
finite-relative-index instance
`Gamma1_mapGL_isFiniteRelIndex_of_dvd` more transparent — the
relative-index hypothesis required by `ModularForm.trace` decomposes
canonically as

  `(Γ₁(M).map (mapGL ℝ)) ≤ (Γ₁(N).map (mapGL ℝ))`     (this lemma)
  `+ relIndex finiteness`                              (the instance).

The proof is a one-line `Subgroup.map_mono` over `Gamma1_le_of_dvd`. -/

/-- **Containment of `Γ₁(M)` in `Γ₁(N)` after `mapGL ℝ`.**
For `N ∣ M`, the image `(Γ₁(M)).map (mapGL ℝ)` is contained in
`(Γ₁(N)).map (mapGL ℝ)` inside `GL(2, ℝ)`. -/
theorem Gamma1_mapGL_le_of_dvd {M N : ℕ} (h : N ∣ M) :
    (Gamma1 M).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
  Subgroup.map_mono (HeckeRing.GL2.Gamma1_le_of_dvd h)

/-- **Specialisation to `N ∣ p · N`.**  Convenience corollary of
`Gamma1_mapGL_le_of_dvd` for the most frequent use case in this file
(level-raising along a single prime `p`). -/
theorem Gamma1_mapGL_le_mul_left (N p : ℕ) :
    (Gamma1 (p * N)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
  Gamma1_mapGL_le_of_dvd (Dvd.intro_left p rfl)

/-- **Coprime-sieved `q`-expansion.**  For a function `f : ℍ → ℂ` with
level-`N` `q`-expansion `Σ aₙ qⁿ` and an integer filter `L`, returns
the formal power series whose `n`-th coefficient is `aₙ` when
`Nat.Coprime n L` and `0` otherwise.

Packaged at the `PowerSeries ℂ` level (not as a modular form); the
modular-form upgrade — Miyake Theorem 4.6.5 — is the main theorem in
this file. -/
noncomputable def sievedQExpansion (N L : ℕ) (f : UpperHalfPlane → ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk fun n =>
    if Nat.Coprime n L then (qExpansion (N : ℝ) f).coeff n else 0

@[simp] lemma sievedQExpansion_coeff_coprime
    (N L : ℕ) (f : UpperHalfPlane → ℂ) {n : ℕ} (h : Nat.Coprime n L) :
    (sievedQExpansion N L f).coeff n = (qExpansion (N : ℝ) f).coeff n := by
  simp [sievedQExpansion, PowerSeries.coeff_mk, h]

@[simp] lemma sievedQExpansion_coeff_not_coprime
    (N L : ℕ) (f : UpperHalfPlane → ℂ) {n : ℕ} (h : ¬ Nat.Coprime n L) :
    (sievedQExpansion N L f).coeff n = 0 := by
  simp [sievedQExpansion, PowerSeries.coeff_mk, h]

/-- **Möbius characterisation of coprimality.**  For any `n, L : ℕ`,

  `[Nat.Coprime n L] = Σ d ∈ (Nat.gcd n L).divisors, μ d`

as an `ℤ`-valued indicator.

**Role in Miyake 4.6.5.**  This identity is the arithmetic ingredient
that *would* collapse a Möbius sum `Σ_d μ(d) · c` (with a fixed scalar
`c`) to `c · [Nat.Coprime n L]`.  It does **not** apply when the
summand's coefficient depends on `d`, which is the case for the naive
level-raise sum `Σ_d μ(d) · ι_d f`; see the scope note near the end of
the file.  Miyake's actual argument uses this identity only after a
Hecke-operator / sub-series construction has already reduced the
problem to a fixed scalar.

Derived from Mathlib's `moebius_mul_coe_zeta : (μ * ζ : ArithmeticFunction
ℤ) = 1` at `(gcd n L)`, unfolding via `coe_mul_zeta_apply` and
`one_apply`. -/
lemma coprime_indicator_eq_sum_moebius (n L : ℕ) :
    (if Nat.Coprime n L then (1 : ℤ) else 0) =
      ∑ d ∈ (Nat.gcd n L).divisors,
        ArithmeticFunction.moebius d := by
  have h_apply :
      (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ))
          (Nat.gcd n L) =
        (1 : ArithmeticFunction ℤ) (Nat.gcd n L) := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h_apply
  rw [← h_apply]

/-! ### T079 — Finite-prime coefficient sieve scaffold

Coefficient-level infrastructure for iterating single-prime sieves over
a finite set of primes.  Purely combinatorial (no modular forms); uses
the canonical period-1 / Miyake coefficient convention, so it meshes
directly with `(qExpansion (1 : ℝ) f).coeff` rather than the old
period-`N` normalisation.

Consumed by the POST-6d square-free decomposition (Miyake §4.6.7 /
§4.6.8): once the single-prime sieve theorems (T070/T076's
`miyake_4_6_5_prime_sieve_*_one`) instantiate via the analytic no-diamond
coefficient formula, iterating them over the prime factors of a
square-free `L` produces the full `L`-coprime sieve at the corresponding
deeper level.

## API overview

* `primeCoeffSieve p A` — zero at multiples of `p`, else `A`.
* `finsetPrimeCoeffSieve S A` — zero when some `p ∈ S` divides `n`,
  else `A n`; iterates `primeCoeffSieve` over `S`.
* `finite_prime_coeff_sieve_iteration` — the pointwise formula,
  suitable for directly reading off coefficients.
* `finsetPrimeCoeffSieve_insert` — recursion step: the sieve over
  `insert p S` composes `primeCoeffSieve p` with the sieve over `S`.
* `finsetPrimeCoeffSieve_eq_coprime` — under `∀ p ∈ S, Nat.Prime p`, the
  "no `p ∈ S` divides `n`" condition is equivalent to
  `Nat.Coprime n (∏ p ∈ S, p)`.
* `sievedQExpansion_eq_finsetPrimeCoeffSieve` — bridge from the existing
  `sievedQExpansion N L` (using `Nat.Coprime n L`) to the new Finset API
  (using `S := L.primeFactors`). -/

/-- **Single-prime coefficient sieve.**  Zeros out the coefficient at
every index divisible by `p`; other coefficients are unchanged.  Works
over any `Zero`-pointed target type (`ℂ`, `ℝ`, any module, etc.). -/
def primeCoeffSieve {α : Type*} [Zero α] (p : ℕ) (A : ℕ → α) (n : ℕ) : α :=
  if p ∣ n then 0 else A n

@[simp] lemma primeCoeffSieve_of_dvd {α : Type*} [Zero α] {p n : ℕ}
    (A : ℕ → α) (h : p ∣ n) : primeCoeffSieve p A n = 0 := by
  simp [primeCoeffSieve, h]

@[simp] lemma primeCoeffSieve_of_not_dvd {α : Type*} [Zero α] {p n : ℕ}
    (A : ℕ → α) (h : ¬ p ∣ n) : primeCoeffSieve p A n = A n := by
  simp [primeCoeffSieve, h]

/-- **Finite-set prime coefficient sieve.**  Pointwise, returns `A n`
when **no** element of `S` divides `n`, and `0` otherwise.  For a Finset
of primes this is the "coprime sieve" with respect to `∏ p ∈ S, p`
(see `finsetPrimeCoeffSieve_eq_coprime`). -/
def finsetPrimeCoeffSieve {α : Type*} [Zero α] (S : Finset ℕ) (A : ℕ → α)
    (n : ℕ) : α :=
  if ∀ p ∈ S, ¬ p ∣ n then A n else 0

/-- **Pointwise formula** for `finsetPrimeCoeffSieve` — identical to the
definition, named for downstream rewriting. -/
theorem finite_prime_coeff_sieve_iteration {α : Type*} [Zero α] (S : Finset ℕ)
    (A : ℕ → α) (n : ℕ) :
    finsetPrimeCoeffSieve S A n =
      if ∀ p ∈ S, ¬ p ∣ n then A n else 0 := rfl

@[simp] lemma finsetPrimeCoeffSieve_empty {α : Type*} [Zero α]
    (A : ℕ → α) (n : ℕ) : finsetPrimeCoeffSieve ∅ A n = A n := by
  simp [finsetPrimeCoeffSieve]

lemma finsetPrimeCoeffSieve_of_forall_not_dvd {α : Type*} [Zero α]
    {S : Finset ℕ} (A : ℕ → α) {n : ℕ} (h : ∀ p ∈ S, ¬ p ∣ n) :
    finsetPrimeCoeffSieve S A n = A n := if_pos h

lemma finsetPrimeCoeffSieve_of_exists_dvd {α : Type*} [Zero α]
    {S : Finset ℕ} (A : ℕ → α) {n : ℕ} (h : ∃ p ∈ S, p ∣ n) :
    finsetPrimeCoeffSieve S A n = 0 := by
  refine if_neg ?_
  push_neg
  exact h

/-- **Insert recursion** for the iterated sieve: at `insert p S`, the
sieve composes `primeCoeffSieve p` with the sieve over `S`.  This is the
natural inductive step driving `Finset.induction_on` proofs and makes
`finsetPrimeCoeffSieve` literally the "iteration" of single-prime
sieves over the underlying Finset. -/
lemma finsetPrimeCoeffSieve_insert {α : Type*} [Zero α] (p : ℕ) (S : Finset ℕ)
    (A : ℕ → α) :
    finsetPrimeCoeffSieve (insert p S) A =
      primeCoeffSieve p (finsetPrimeCoeffSieve S A) := by
  funext n
  show (if ∀ q ∈ insert p S, ¬ q ∣ n then A n else 0) =
    (if p ∣ n then 0 else if ∀ q ∈ S, ¬ q ∣ n then A n else 0)
  by_cases hdvd : p ∣ n
  · -- RHS = 0; LHS = 0 (since p ∈ insert p S and p ∣ n violate `∀ q, ¬ q ∣ n`).
    have hfail : ¬ ∀ q ∈ insert p S, ¬ q ∣ n := fun h =>
      h p (Finset.mem_insert_self p S) hdvd
    rw [if_neg hfail, if_pos hdvd]
  · rw [if_neg hdvd]
    have hiff : (∀ q ∈ insert p S, ¬ q ∣ n) ↔ (∀ q ∈ S, ¬ q ∣ n) := by
      constructor
      · intro h q hqS
        exact h q (Finset.mem_insert.mpr (Or.inr hqS))
      · intro h q hq
        rcases Finset.mem_insert.mp hq with rfl | hqS
        · exact hdvd
        · exact h q hqS
    by_cases h : ∀ q ∈ S, ¬ q ∣ n
    · rw [if_pos (hiff.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

/-- **Coprime characterisation.**  When every element of `S` is prime,
the "no `p ∈ S` divides `n`" condition is equivalent to
`Nat.Coprime n (∏ p ∈ S, p)`.  No distinctness or squarefreeness
hypothesis is needed: `S`'s elements are automatically distinct as a
`Finset`, and primality of each element gives
`Coprime n p ↔ ¬ p ∣ n` via `Nat.Prime.coprime_iff_not_dvd`. -/
theorem finsetPrimeCoeffSieve_eq_coprime {α : Type*} [Zero α] {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (A : ℕ → α) (n : ℕ) :
    finsetPrimeCoeffSieve S A n =
      if Nat.Coprime n (∏ p ∈ S, p) then A n else 0 := by
  show (if ∀ p ∈ S, ¬ p ∣ n then A n else 0) =
    (if Nat.Coprime n (∏ p ∈ S, p) then A n else 0)
  have hiff : (∀ p ∈ S, ¬ p ∣ n) ↔ Nat.Coprime n (∏ p ∈ S, p) := by
    rw [Nat.coprime_prod_right_iff]
    refine ⟨fun h p hp => ?_, fun h p hp => ?_⟩
    · exact ((hS p hp).coprime_iff_not_dvd.mpr (h p hp)).symm
    · exact (hS p hp).coprime_iff_not_dvd.mp (h p hp).symm
  by_cases h : ∀ p ∈ S, ¬ p ∣ n
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- **PowerSeries wrapper.**  Bundles `finsetPrimeCoeffSieve` as a
`PowerSeries` operation: the `n`-th coefficient of the sieved series is
the sieved value of the original's `n`-th coefficient. -/
noncomputable def finsetPrimeSievedSeries {R : Type*} [Semiring R]
    (S : Finset ℕ) (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk
    (finsetPrimeCoeffSieve S (fun n => A.coeff n))

@[simp] lemma finsetPrimeSievedSeries_coeff {R : Type*} [Semiring R]
    (S : Finset ℕ) (A : PowerSeries R) (n : ℕ) :
    (finsetPrimeSievedSeries S A).coeff n =
      finsetPrimeCoeffSieve S (fun n' => A.coeff n') n := by
  simp [finsetPrimeSievedSeries]

/-- **Bridge to existing `sievedQExpansion`.**  For a nonzero level
filter `L`, the `n`-th coefficient of `sievedQExpansion N L f` coincides
with `finsetPrimeCoeffSieve L.primeFactors` applied to `f`'s period-`N`
q-expansion coefficients.  Consequence of the `Finset`-level bridge
`Coprime n L ↔ ∀ p ∈ L.primeFactors, ¬ p ∣ n`, which in turn uses
Mathlib's `Nat.disjoint_primeFactors` and the fact that coprimality is
determined by the set of prime divisors of `L`. -/
lemma sievedQExpansion_eq_finsetPrimeCoeffSieve
    (N L : ℕ) (hL : L ≠ 0) (f : UpperHalfPlane → ℂ) (n : ℕ) :
    (sievedQExpansion N L f).coeff n =
      finsetPrimeCoeffSieve L.primeFactors
        (fun n' => (qExpansion (N : ℝ) f).coeff n') n := by
  -- `Coprime n L ↔ ∀ p ∈ L.primeFactors, ¬ p ∣ n`
  have hiff : Nat.Coprime n L ↔ ∀ p ∈ L.primeFactors, ¬ p ∣ n := by
    constructor
    · intro hcop p hp
      have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd_L : p ∣ L := Nat.dvd_of_mem_primeFactors hp
      have hcop_np : Nat.Coprime n p := hcop.coprime_dvd_right hp_dvd_L
      exact hp_prime.coprime_iff_not_dvd.mp hcop_np.symm
    · intro h
      by_contra hcop
      have hgcd_ne : Nat.gcd n L ≠ 1 := hcop
      obtain ⟨p, hp_prime, hp_dvd_gcd⟩ :=
        Nat.exists_prime_and_dvd hgcd_ne
      have hp_dvd_n : p ∣ n := hp_dvd_gcd.trans (Nat.gcd_dvd_left n L)
      have hp_dvd_L : p ∣ L := hp_dvd_gcd.trans (Nat.gcd_dvd_right n L)
      exact h p (Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd_L, hL⟩) hp_dvd_n
  by_cases h : Nat.Coprime n L
  · rw [sievedQExpansion_coeff_coprime N L f h,
      finsetPrimeCoeffSieve_of_forall_not_dvd _ (hiff.mp h)]
  · have hex : ∃ p ∈ L.primeFactors, p ∣ n := by
      by_contra hall
      push_neg at hall
      exact h (hiff.mpr hall)
    rw [sievedQExpansion_coeff_not_coprime N L f h,
      finsetPrimeCoeffSieve_of_exists_dvd _ hex]

/-- **Coprime-product form of the bridge.**  For a nonzero level filter
`L`, combining `sievedQExpansion_eq_finsetPrimeCoeffSieve` with
`finsetPrimeCoeffSieve_eq_coprime` shows that the sieve condition
`Nat.Coprime n L` is equivalent (at the coefficient level) to
`Nat.Coprime n (∏ p ∈ L.primeFactors, p)`, i.e., coprimality is
determined by the **radical** of `L` (product of distinct prime
divisors).  This connects the integer-level filter `L` to the Finset-of-
primes filter and explains why the Miyake sieve construction is
insensitive to multiplicities in `L`. -/
lemma sievedQExpansion_eq_coprime_radical
    (N L : ℕ) (hL : L ≠ 0) (f : UpperHalfPlane → ℂ) (n : ℕ) :
    (sievedQExpansion N L f).coeff n =
      if Nat.Coprime n (∏ p ∈ L.primeFactors, p) then
        (qExpansion (N : ℝ) f).coeff n
      else 0 := by
  rw [sievedQExpansion_eq_finsetPrimeCoeffSieve N L hL f n,
      finsetPrimeCoeffSieve_eq_coprime
        (fun _ hp => Nat.prime_of_mem_primeFactors hp) _ n]

/-! ### Miyake 4.6.5 — prime-case construction (T070)

**Miyake's actual single-prime construction (§4.6.5, case `L = p` prime).**
Let `N' := N` if `p ∣ N` and `N' := pN` if `p ∤ N`.  Miyake uses the
Hecke operator `T(p)` at level `Γ₀(N')` (a level *divisible* by `p`):

```
  g_p(τ) := f(τ) − (f ∣ T(p)^{Γ₀(N')})(p · τ),
```

and `g_p ∈ M_k(p · N', χ)` is the `p`-coprime sieve of `f`, i.e.
`g_p(τ) = Σ_{p ∤ n} a_n q^n`.  The essential feature that makes this
work is the **no-diamond** coefficient formula of the Γ₀(N')-level
Hecke operator,

```
  coeff m (f ∣ T(p)^{Γ₀(N')}) = a_{p · m}                    (†)
```

(no `χ(p) · [p ∣ m] · a_{m/p}` term), so that
`(f ∣ T(p)^{Γ₀(N')})(p · τ) = Σ_{p ∣ n} a_n q^n` exactly and the
difference gives the pure sieve.

**API gap reported by T070.**  The Hecke operator provided by this
repository, `HeckeRing.GL2.heckeT_p k p hp hpN f`, is the
**Diamond–Shurman operator at level `Γ₁(N)` with `p ∤ N`** and satisfies
`coeff m (heckeT_p f) = a_{p · m} + p^{k-1} · χ(p) · [p ∣ m] · a_{m/p}`
(the DS formula *with* diamond, via `fourierCoeff_heckeT_p`).  The
Γ₀(pN)-level operator with `p ∣ pN` and no-diamond formula `(†)` is
**not** currently in the repository, so Miyake's single-prime sieve
cannot be assembled from `heckeT_p` as-is — the extra diamond term
produces a non-zero residual on the `p² · ℕ` support.

**T070 content.**  The reusable theorem below captures Miyake's actual
argument at the coefficient level by **abstracting over** the
no-diamond hypothesis `(†)`: for *any* `g ∈ M_k(Γ₁(N))` whose
coefficients match `(†)`, the combination `f − ι_p(g)` at level
`Γ₁(p · N)` has the exact coprime-sieve q-expansion.  T068
(`qExpansion_modularFormLevelRaise_coeff`) supplies the d-dilation
ingredient for `ι_p(g)`.  The remaining obligation for a faithful
Miyake 4.6.5 formalisation is to **construct** such a `g` — either by
introducing the Γ₀(pN)-level `T(p)` operator with its no-diamond
coefficient formula, or by any other witness satisfying `(†)`. -/

/-- **T070 — Miyake 4.6.5 single-prime sieve from the no-diamond
hypothesis.**

Given a modular form `f : M_k(Γ₁(N))` with period-`N` q-expansion
`Σ a_n q^n`, and **any** second modular form `g : M_k(Γ₁(N))` satisfying
the "no-diamond" sub-series condition

```
  ∀ m : ℕ, (qExpansion N g).coeff m = (qExpansion N f).coeff (p · m),
```

the Fourier coefficients of `f − ι_p(g) : ℍ → ℂ` at period `N` are
exactly the `p`-coprime sieve of `f`:

```
  (qExpansion N f).coeff n − (qExpansion N (ι_p g)).coeff n
    = if p ∣ n then 0 else (qExpansion N f).coeff n,
```

where `ι_p g := modularFormLevelRaise N p k g : M_k(Γ₁(p · N))`.

**Proof.**  For `p ∣ n`, T068 gives
`coeff n (ι_p g) = (qExpansion N g).coeff (n / p) = a_{p · (n/p)} = a_n`
by the hypothesis and `Nat.mul_div_cancel' h`, so the difference is
`a_n − a_n = 0`.  For `p ∤ n`, T068 gives `coeff n (ι_p g) = 0`, so
the difference is `a_n − 0 = a_n`.

**Role in Miyake 4.6.5.**  The "no-diamond hypothesis"
`coeff m g = a_{p · m}` is precisely what Miyake's Γ₀(pN)-level `T(p)`
(with `p ∣ pN`) provides; substituting any such `g` into this theorem
yields Miyake's single-prime sieve.  The current repository's
`heckeT_p` does **not** satisfy the hypothesis (it has an extra diamond
term); constructing a compliant `g` is the remaining API gap,
tracked as a separate infrastructure ticket. -/
theorem miyake_4_6_5_prime_sieve_from_no_diamond
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_no_diamond : ∀ m : ℕ,
      (qExpansion (N : ℝ) g).coeff m = (qExpansion (N : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion (N : ℝ) f).coeff n -
        (qExpansion (N : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise N p k g)).coeff n =
      (if p ∣ n then 0 else (qExpansion (N : ℝ) f).coeff n) := by
  have hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) =
      (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
    exact ⟨(N : ℤ), by simp⟩
  rw [HeckeRing.GL2.qExpansion_modularFormLevelRaise_coeff hN_period g n]
  by_cases h : p ∣ n
  · rw [if_pos h, if_pos h, hg_no_diamond (n / p), Nat.mul_div_cancel' h, sub_self]
  · rw [if_neg h, if_neg h, sub_zero]

/-- **T070 — auxiliary reformulation as a pointwise coprime-sieve
identity.**  Under the same hypotheses as
`miyake_4_6_5_prime_sieve_from_no_diamond`, the Fourier coefficients of
`f − ι_p(g)` are **exactly** the `p`-coprime-filtered coefficients of
`f`:

```
  (qExpansion N f).coeff n − (qExpansion N (ι_p g)).coeff n
    = if ¬ p ∣ n then (qExpansion N f).coeff n else 0.
```

This is `miyake_4_6_5_prime_sieve_from_no_diamond` rewritten with the
condition flipped, matching the shape of `sievedQExpansion_coeff_*`. -/
theorem miyake_4_6_5_prime_sieve_indicator
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_no_diamond : ∀ m : ℕ,
      (qExpansion (N : ℝ) g).coeff m = (qExpansion (N : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion (N : ℝ) f).coeff n -
        (qExpansion (N : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise N p k g)).coeff n =
      (if ¬ p ∣ n then (qExpansion (N : ℝ) f).coeff n else 0) := by
  rw [miyake_4_6_5_prime_sieve_from_no_diamond f g hg_no_diamond n]
  by_cases h : p ∣ n
  · rw [if_pos h, if_neg (not_not_intro h)]
  · rw [if_neg h, if_pos h]

/-! ### T073 — Miyake's Γ₀(pN)-level T_p witness at the deeper level

The repository already provides `HeckeRing.GL2.heckeT_p_divN` (in
`HeckeT_n.lean`), an **endomorphism** of `M_k(Γ₁(M))` for `M` with
`¬ Nat.Coprime p M` (i.e., `p ∣ M`), defined by the upper-triangular
sum `Σ_{b=0}^{p-1} f ∣[k] [[1,b],[0,p]]`.  This is exactly the **no-diamond**
Hecke operator `T(p)^{Γ₀(M)}` that Miyake §4.6.5 uses at a level
divisible by `p`.  For Miyake's single-prime sieve starting from `f`
at level `Γ₁(N)` with `p ∤ N`, the natural level for the witness is
`M := p · N` (so that `p ∣ M`):

```
  witness_Miyake(f) := heckeT_p_divN k p hp hpN_not_coprime_pN
                        (ModularForm.restrictSubgroup h_le f)
    : ModularForm ((Gamma1 (p · N)).map (mapGL ℝ)) k.
```

The **coefficient formula** for this witness,
`(qExpansion ((p · N : ℕ) : ℝ) (heckeT_p_divN _ f_pN)).coeff m =
  (qExpansion ((p · N : ℕ) : ℝ) f).coeff (p · m)`,
is **not** landed in T073 — see "Remaining API gap" at the end of this
section.

T073 lands `miyake_4_6_5_prime_sieve_witness_at_pN` below: a T070 variant
that accepts the witness at level `Γ₁(p · N)` (rather than T070's
same-level Γ₁(N)), matching the landing level of
`heckeT_p_divN`.  Once the coefficient formula for `heckeT_p_divN`
lands (currently blocked by T067's in-progress
`QExpansionSlash.lean`), this theorem fires directly to produce
Miyake's actual single-prime sieve as an instantiation. -/

/-- **T073 — Miyake single-prime sieve with witness at level `Γ₁(p · N)`.**

Variant of `miyake_4_6_5_prime_sieve_from_no_diamond` where the witness
`g` lives at the **deeper** level `Γ₁(p · N)`, which is the natural type
of Miyake's Γ₀(pN)-level Hecke operator
`HeckeRing.GL2.heckeT_p_divN` applied to a restricted copy of `f`.
The q-expansion is evaluated at period `p · N`.

**Proof.**  Restrict `f : M_k(Γ₁(N))` to `M_k(Γ₁(p · N))` via
`ModularForm.restrictSubgroup` along `Gamma1_le_of_dvd (N ∣ p · N)`
(both lifted through `Subgroup.map` with `mapGL ℝ`).  The restricted
form's q-expansion coincides with the original's (same underlying
function), so the no-diamond hypothesis transports unchanged, and
`miyake_4_6_5_prime_sieve_from_no_diamond` (T070) at level `p · N`
concludes. -/
theorem miyake_4_6_5_prime_sieve_witness_at_pN
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k)
    (hg_no_diamond : ∀ m : ℕ,
      (qExpansion ((p * N : ℕ) : ℝ) g).coeff m =
      (qExpansion ((p * N : ℕ) : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion ((p * N : ℕ) : ℝ) f).coeff n -
        (qExpansion ((p * N : ℕ) : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise (p * N) p k g)).coeff n =
      (if p ∣ n then 0 else (qExpansion ((p * N : ℕ) : ℝ) f).coeff n) := by
  have h_dvd : N ∣ p * N := ⟨p, mul_comm _ _⟩
  have h_le : (Gamma1 (p * N)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
    Gamma1_mapGL_le_of_dvd (h_dvd)
  -- Restrict f to level Γ₁(p · N). The underlying function is unchanged,
  -- so the period-(p·N) q-expansion is identical.
  set f_pN : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    ModularForm.restrictSubgroup h_le f with hf_pN_def
  have hf_qex : (qExpansion ((p * N : ℕ) : ℝ) f_pN) =
      (qExpansion ((p * N : ℕ) : ℝ) f) := rfl
  -- Apply T070 at level p · N with the restricted f_pN.
  have hg' : ∀ m : ℕ,
      (qExpansion ((p * N : ℕ) : ℝ) g).coeff m =
      (qExpansion ((p * N : ℕ) : ℝ) f_pN).coeff (p * m) := by
    intro m; rw [hf_qex]; exact hg_no_diamond m
  have := miyake_4_6_5_prime_sieve_from_no_diamond f_pN g hg' n
  rw [← hf_qex]; exact this

/-- **T073 — indicator form** of `miyake_4_6_5_prime_sieve_witness_at_pN`,
matching the shape of `sievedQExpansion_coeff_*`. -/
theorem miyake_4_6_5_prime_sieve_witness_at_pN_indicator
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k)
    (hg_no_diamond : ∀ m : ℕ,
      (qExpansion ((p * N : ℕ) : ℝ) g).coeff m =
      (qExpansion ((p * N : ℕ) : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion ((p * N : ℕ) : ℝ) f).coeff n -
        (qExpansion ((p * N : ℕ) : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise (p * N) p k g)).coeff n =
      (if ¬ p ∣ n then (qExpansion ((p * N : ℕ) : ℝ) f).coeff n else 0) := by
  rw [miyake_4_6_5_prime_sieve_witness_at_pN f g hg_no_diamond n]
  by_cases h : p ∣ n
  · rw [if_pos h, if_neg (not_not_intro h)]
  · rw [if_neg h, if_pos h]

/-! ### T076 — period-1 Miyake sieve (correct formulation)

**Mathematical correction reported by T076.**  The formulation of the
no-diamond hypothesis at period `p · N` used in T073's
`miyake_4_6_5_prime_sieve_witness_at_pN` — namely
`(qExpansion ((p * N : ℕ) : ℝ) g).coeff m = (qExpansion ((p * N : ℕ) : ℝ) f).coeff (p * m)` —
is **not satisfied** by the natural Miyake witness `heckeT_p_divN f_pN`.
Reason: for a form `f` of true period `1` at level `Γ₁(M)` with `p ∣ M`,
the period-`M` q-expansion is sparse (`coeff j = 0` unless `M ∣ j`), so
the LHS is `0` at `M ∤ m` whereas the RHS can be non-zero at the "finer
sparsity" `M/p ∣ m, M ∤ m`.  Concretely, at `M = 2, p = 2, m = 1`:
`(qExpansion 2 (heckeT_p_divN f)).coeff 1 = 0` but
`(qExpansion 2 f).coeff 2 = (qExpansion 1 f).coeff 1 = a_1` is generically
non-zero.  T073's theorem is still logically valid ("if the hypothesis
holds, then the sieve follows"), but the hypothesis is **vacuous** for
the natural witness.

The correct period for Miyake's formula is the **canonical Fourier
period `h = 1`**: there, `(qExpansion 1 g).coeff m = a_m` for the
usual Fourier coefficients `a_m`, so Miyake (4.6.6) reads simply
`a_m(T_p f) = a_{p·m}`.  T076 therefore lands the **period-1** variants
of T068/T070/T073, all correctly formulated.  The single remaining
analytic lemma is then the period-1 no-diamond coefficient formula for
`heckeT_p_divN`, stated below. -/

/-- **T076 — period-1 single-prime sieve (T070 variant).**  Abstract
period-1 sieve theorem: for any prime `p`, modular forms
`f, g : M_k(Γ₁(N))`, and a no-diamond hypothesis at period `1`,
`f − modularFormLevelRaise N p k g` has its period-`1` Fourier
coefficient equal to `a_n` at `p ∤ n` and `0` at `p ∣ n`.

This is the mathematically-correct analog of
`miyake_4_6_5_prime_sieve_from_no_diamond` (T070) at period 1.  Proof
delegates to `qExpansion_one_modularFormLevelRaise_coeff` (T068 period-1
variant) plus pure arithmetic on `if-then-else`. -/
theorem miyake_4_6_5_prime_sieve_from_no_diamond_one
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_no_diamond_one : ∀ m : ℕ,
      (qExpansion (1 : ℝ) g).coeff m = (qExpansion (1 : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion (1 : ℝ) f).coeff n -
        (qExpansion (1 : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise N p k g)).coeff n =
      (if p ∣ n then 0 else (qExpansion (1 : ℝ) f).coeff n) := by
  rw [HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff g n]
  by_cases h : p ∣ n
  · rw [if_pos h, if_pos h,
      hg_no_diamond_one (n / p), Nat.mul_div_cancel' h, sub_self]
  · rw [if_neg h, if_neg h, sub_zero]

/-- **T076 — period-1 sieve with witness at deeper level `Γ₁(p · N)`.**
Variant of `miyake_4_6_5_prime_sieve_witness_at_pN` (T073) at period 1,
where the no-diamond hypothesis is correctly stated (and satisfiable by
`heckeT_p_divN (f_pN)`, once its coefficient formula lands).  The
q-expansion is evaluated at the canonical period `h = 1`.

**Proof.**  Restrict `f` to level `Γ₁(p · N)` via
`ModularForm.restrictSubgroup`; the underlying function is unchanged, so
period-1 q-expansions coincide; delegate to
`miyake_4_6_5_prime_sieve_from_no_diamond_one` at level `p · N`. -/
theorem miyake_4_6_5_prime_sieve_witness_at_pN_one
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k)
    (hg_no_diamond_one : ∀ m : ℕ,
      (qExpansion (1 : ℝ) g).coeff m = (qExpansion (1 : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion (1 : ℝ) f).coeff n -
        (qExpansion (1 : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise (p * N) p k g)).coeff n =
      (if p ∣ n then 0 else (qExpansion (1 : ℝ) f).coeff n) := by
  have h_dvd : N ∣ p * N := ⟨p, mul_comm _ _⟩
  have h_le : (Gamma1 (p * N)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
    Gamma1_mapGL_le_of_dvd (h_dvd)
  set f_pN : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    ModularForm.restrictSubgroup h_le f
  have hf_qex : (qExpansion (1 : ℝ) f_pN) = (qExpansion (1 : ℝ) f) := rfl
  have hg' : ∀ m : ℕ,
      (qExpansion (1 : ℝ) g).coeff m =
      (qExpansion (1 : ℝ) f_pN).coeff (p * m) := fun m => by
    rw [hf_qex]; exact hg_no_diamond_one m
  have := miyake_4_6_5_prime_sieve_from_no_diamond_one f_pN g hg' n
  rw [← hf_qex]; exact this

/-! ### Concrete period-1 sieve wrapper — T076 closure (via T081)

The analytic no-diamond coefficient formula
`HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff` is now available in
`LeanModularForms/Modularforms/QExpansionSlash.lean` (T081), so
instantiating `miyake_4_6_5_prime_sieve_from_no_diamond_one` with the
concrete witness `g := heckeT_p_divN k p hp hpM f` gives the final T076
same-level sieve identity directly. -/

/-- **T076 — period-1 same-level single-prime sieve with the concrete
`heckeT_p_divN` witness** (Miyake 4.6.5 / Diamond–Shurman Prop 5.9).

For a prime `p` dividing `M` and any `f ∈ M_k(Γ₁(M))`, the difference
between `f` and the level-raised image of `heckeT_p_divN k p hp hpM f`
has its `n`-th period-`1` Fourier coefficient equal to `a_n(f)` when
`p ∤ n` and `0` when `p ∣ n`:

  `a_n(f) − a_n(modularFormLevelRaise M p k (heckeT_p_divN k p hp hpM f))
    = [p ∤ n] · a_n(f)`.

This is the concrete T076 instantiation of
`miyake_4_6_5_prime_sieve_from_no_diamond_one`, using the period-1
no-diamond coefficient formula `qExpansion_one_heckeT_p_divN_coeff`
from `QExpansionSlash.lean` as the witness hypothesis.  The level-`M`
hypothesis `¬ Nat.Coprime p M` is exactly what `heckeT_p_divN` requires
to be well-defined. -/
theorem miyake_4_6_5_prime_sieve_heckeT_p_divN_one
    {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpM : ¬ Nat.Coprime p M)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ) f).coeff n -
        (qExpansion (1 : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise M p k
            (HeckeRing.GL2.heckeT_p_divN k p hp hpM f))).coeff n =
      (if p ∣ n then 0 else (qExpansion (1 : ℝ) f).coeff n) :=
  miyake_4_6_5_prime_sieve_from_no_diamond_one f
    (HeckeRing.GL2.heckeT_p_divN k p hp hpM f)
    (fun m => HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff hp hpM f m) n

/-- **Miyake 4.6.7 — finite-prime iteration of the period-1 single-prime
`heckeT_p_divN` sieve at level aware of each prime.**

Given `f ∈ M_k(Γ₁(M))` and a finite set of primes `S` with each `p ∈ S`
dividing `M`, there exists a modular form `g` at level
`Γ₁(M · ∏_{p ∈ S} p)` whose period-`1` Fourier coefficients are the
`S`-sieved coefficients of `f`:

  `a_n(g) = if ∃ p ∈ S, p ∣ n then 0 else a_n(f)`,

equivalently `a_n(g) = a_n(f) · [∀ p ∈ S, p ∤ n]`.

The witness `g` is constructed by iterating
`miyake_4_6_5_prime_sieve_heckeT_p_divN_one` (T083) over the primes in
`S`: at each step we subtract the level-raised `heckeT_p_divN` image,
restricting the running witness to the new (deeper) level via
`ModularForm.restrictSubgroup`.  The level grows by a factor of `p` at
each step, yielding the full `∏ S` multiplier.  The hypothesis
`p ∣ M` at each inductive step persists automatically since `M`
divides every intermediate level.

This is the POST-6d finite-prime scaffold for Miyake Theorem 4.6.5 /
Lemma 4.6.7 (Diamond–Shurman §5.9) over a square-free modulus:
specialising `S` to the prime factors of a square-free `L` (with all
primes dividing `M`) yields the full `L`-coprime sieve at level
`M · L`.  POST-6e will lift the level hypothesis `∀ p ∈ S, p ∣ M`
via an initial `ModularForm.restrictSubgroup` to level `M · rad(L)`
and package the conclusion as Miyake Theorem 4.6.8. -/
theorem miyake_4_6_5_finset_sieve_heckeT_p_divN_one
    {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ∃ (M' : ℕ) (_ : NeZero M'), M' = M * S.prod id ∧
    ∃ g : ModularForm ((Gamma1 M').map (mapGL ℝ)) k,
      ∀ n : ℕ, (qExpansion (1 : ℝ) g).coeff n =
        (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) f).coeff n) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨M, inferInstance, ?_, f, ?_⟩
    · simp
    · intro n; simp
  | @insert p₀ S' hp₀_notin IH =>
    have hS' : ∀ p ∈ S', p.Prime ∧ p ∣ M :=
      fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hp₀_prime : p₀.Prime := (hS p₀ (Finset.mem_insert_self p₀ S')).1
    have hp₀_M : p₀ ∣ M := (hS p₀ (Finset.mem_insert_self p₀ S')).2
    obtain ⟨M_prev, hM_prev_ne, hM_prev_eq, g_prev, hg_prev⟩ := IH hS'
    -- p₀ divides every intermediate level since p₀ ∣ M and M ∣ M_prev.
    have hp₀_M_prev : p₀ ∣ M_prev := hM_prev_eq ▸ hp₀_M.mul_right _
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ M_prev :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime, dvd_refl _, hp₀_M_prev⟩
    haveI : NeZero p₀ := ⟨hp₀_prime.ne_zero⟩
    haveI hM_new_ne : NeZero (p₀ * M_prev) :=
      ⟨Nat.mul_ne_zero hp₀_prime.ne_zero hM_prev_ne.out⟩
    -- New level `p₀ * M_prev = M * (insert p₀ S').prod id`.
    have hM_new_eq : p₀ * M_prev = M * (insert p₀ S').prod id := by
      rw [hM_prev_eq, Finset.prod_insert hp₀_notin]
      simp; ring
    -- Subgroup inclusion `Gamma1 (p₀ * M_prev) ≤ Gamma1 M_prev`.
    have h_le : (Gamma1 (p₀ * M_prev)).map (mapGL ℝ) ≤ (Gamma1 M_prev).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    -- Construct witness: `restrictSubgroup g_prev - levelRaise (heckeT_p_divN g_prev)`.
    refine ⟨p₀ * M_prev, hM_new_ne, hM_new_eq,
      ModularForm.restrictSubgroup h_le g_prev -
        HeckeRing.GL2.modularFormLevelRaise M_prev p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g_prev), ?_⟩
    intro n
    -- Expand the coefficient of the difference at period 1.
    have h1_pos : (0 : ℝ) < 1 := one_pos
    have h1_period : (1 : ℝ) ∈ ((Gamma1 (p₀ * M_prev)).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 (p₀ * M_prev)).map (mapGL ℝ) =
            (Gamma1 (p₀ * M_prev) : Subgroup (GL (Fin 2) ℝ)) from rfl,
        CongruenceSubgroup.strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    rw [show ⇑(ModularForm.restrictSubgroup h_le g_prev -
          HeckeRing.GL2.modularFormLevelRaise M_prev p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g_prev)) =
        ⇑(ModularForm.restrictSubgroup h_le g_prev) -
        ⇑(HeckeRing.GL2.modularFormLevelRaise M_prev p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g_prev)) from
      ModularForm.coe_sub _ _]
    rw [qExpansion_sub h1_pos h1_period, map_sub]
    -- `qExpansion 1 (restrictSubgroup h_le g_prev) = qExpansion 1 g_prev` at the
    -- coefficient level (same underlying function via `coe_restrictSubgroup`).
    have h_restrict_coeff :
        (qExpansion (1 : ℝ)
          (ModularForm.restrictSubgroup h_le g_prev)).coeff n =
        (qExpansion (1 : ℝ) g_prev).coeff n := rfl
    rw [h_restrict_coeff]
    -- T083 at prime `p₀` applied to the running witness `g_prev`.
    have hT83 :=
      miyake_4_6_5_prime_sieve_heckeT_p_divN_one hp₀_prime hp₀_not_coprime g_prev n
    rw [hT83, hg_prev n]
    -- Finish by splitting on `p₀ ∣ n` and `∃ q ∈ S', q ∣ n`.
    by_cases hn_p₀ : p₀ ∣ n
    · have h_ex : ∃ p ∈ insert p₀ S', p ∣ n :=
        ⟨p₀, Finset.mem_insert_self _ _, hn_p₀⟩
      rw [if_pos hn_p₀, if_pos h_ex]
    · rw [if_neg hn_p₀]
      by_cases hn_S' : ∃ q ∈ S', q ∣ n
      · have h_ex : ∃ p ∈ insert p₀ S', p ∣ n := by
          obtain ⟨q, hqS', hqn⟩ := hn_S'
          exact ⟨q, Finset.mem_insert_of_mem hqS', hqn⟩
        rw [if_pos hn_S', if_pos h_ex]
      · rw [if_neg hn_S']
        have h_nex : ¬ ∃ p ∈ insert p₀ S', p ∣ n := by
          rintro ⟨p, hp_mem, hpn⟩
          rcases Finset.mem_insert.mp hp_mem with rfl | hp_S'
          · exact hn_p₀ hpn
          · exact hn_S' ⟨p, hp_S', hpn⟩
        rw [if_neg h_nex]

/-! ### POST-6e — Miyake 4.6.5 / 4.6.8 square-free `L` specialisation

For a **square-free** sieve modulus `L` whose distinct prime factors all
divide the base level `M`, instantiating the POST-6d level-aware
iteration `miyake_4_6_5_finset_sieve_heckeT_p_divN_one` at the Finset
`S := L.primeFactors` produces a modular form `g` at level
`Γ₁(M · L)` whose period-`1` Fourier coefficients coincide with the
`L`-coprime sieve of `f`'s coefficients — i.e., `g`'s `q`-expansion
matches `sievedQExpansion 1 L ⇑f` pointwise.

This is the natural square-free specialisation of Miyake Lemma 4.6.7 /
Theorem 4.6.8 on the coefficient side.  Iterating over each prime
`p ∈ L.primeFactors` consumes the single-prime Γ₀(pN)-level Hecke
witness (T083) once per factor; `Squarefree L` ensures the Finset
product `L.primeFactors.prod id` collapses to `L` itself via
`Nat.prod_primeFactors_of_squarefree`, and
`sievedQExpansion_eq_finsetPrimeCoeffSieve` bridges the T085
`∃ p ∈ L.primeFactors, p ∣ n` indicator to the canonical
`Nat.Coprime n L` sieve.

The Nebentypus pullback along the level inclusion
`Γ₀(M · L) ⊆ Γ₀(M)` is packaged separately as
`miyake_main_lemma_4_6_8_squarefree` below, which extends this
coefficient-only statement to the full Miyake Theorem 4.6.8 by
additionally tracking the pulled-back character. -/
theorem miyake_4_6_5_squarefree_sieve_heckeT_p_divN_one
    {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    {L : ℕ} (hL : Squarefree L) (hL_M : ∀ p ∈ L.primeFactors, p ∣ M) :
    ∃ (_ : NeZero (M * L)) (g : ModularForm ((Gamma1 (M * L)).map (mapGL ℝ)) k),
      ∀ n : ℕ, (qExpansion (1 : ℝ) g).coeff n =
        (sievedQExpansion 1 L ⇑f).coeff n := by
  -- Package prime/divisibility hypotheses at `S := L.primeFactors`.
  have hS_prime_dvd : ∀ p ∈ L.primeFactors, p.Prime ∧ p ∣ M :=
    fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hL_M p hp⟩
  -- Squarefree L ⟹ product of distinct prime factors collapses to L.
  have h_prod : L.primeFactors.prod id = L := by
    show ∏ p ∈ L.primeFactors, p = L
    exact Nat.prod_primeFactors_of_squarefree hL
  have hL_ne : L ≠ 0 := hL.ne_zero
  -- Invoke T085 at S := L.primeFactors.
  obtain ⟨M', hM'_ne, hM'_eq, g, hg⟩ :=
    miyake_4_6_5_finset_sieve_heckeT_p_divN_one f L.primeFactors hS_prime_dvd
  -- Rewrite M' = M * L via the square-free prime-product collapse.
  rw [h_prod] at hM'_eq
  subst hM'_eq
  refine ⟨hM'_ne, g, ?_⟩
  intro n
  rw [hg n, sievedQExpansion_eq_finsetPrimeCoeffSieve 1 L hL_ne ⇑f n]
  -- Match the T085 `∃`-indicator with the Finset-sieve `∀`-indicator.
  by_cases h_ex : ∃ p ∈ L.primeFactors, p ∣ n
  · rw [if_pos h_ex, finsetPrimeCoeffSieve_of_exists_dvd _ h_ex]
  · rw [if_neg h_ex]
    push_neg at h_ex
    rw [finsetPrimeCoeffSieve_of_forall_not_dvd _ h_ex, Nat.cast_one]

/-! ### Character-space pullback along a level inclusion

For a modular form `f` at level `Γ₁(M).map mapGL ℝ` in the Nebentypus
character space `modFormCharSpace k χ`, and a divisibility `M ∣ N`,
the restriction of `f` along the subgroup inclusion
`Γ₁(N).map mapGL ≤ Γ₁(M).map mapGL` (from `Gamma1_le_of_dvd`) lies in
the pulled-back character space
`modFormCharSpace k (χ.comp (ZMod.unitsMap h))`, where
`ZMod.unitsMap : (ZMod N)ˣ →* (ZMod M)ˣ` is the natural reduction
on units.

This is the local character-change-of-level ingredient for Miyake
Theorem 4.6.8 / Main Lemma: given the square-free sieve
`miyake_4_6_5_squarefree_sieve_heckeT_p_divN_one` placing `g` at level
`Γ₁(M · L)`, pairing with this pullback accounts for the Nebentypus
transport from `χ` to `χ ∘ ZMod.unitsMap` at the higher level. -/
theorem restrictSubgroup_mem_modFormCharSpace
    {M N : ℕ} [NeZero M] [NeZero N] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (h : M ∣ N) (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ) :
    ModularForm.restrictSubgroup
        (Gamma1_mapGL_le_of_dvd (h)) f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap h)) := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  have hg_M : (g : SL(2, ℤ)) ∈ Gamma0 M := Gamma0_le_of_dvd h g.property
  suffices h_units :
      Gamma0MapUnits (⟨(g : SL(2, ℤ)), hg_M⟩ : ↥(Gamma0 M)) =
        ZMod.unitsMap h (Gamma0MapUnits g) by
    rw [ModularForm.coe_restrictSubgroup, hf ⟨(g : SL(2, ℤ)), hg_M⟩,
      MonoidHom.comp_apply, h_units]
  apply Units.ext
  rw [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0MapUnits_val]
  exact (ZMod.cast_intCast h (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)).symm

/-! ### POST-6f — Hecke and level-raise compatibility with the Nebentypus

Two reusable character-space compatibility lemmas required to lift the
coefficient sieve to Miyake Main Lemma 4.6.8 at the modular-form
level. -/

/-- **Hecke `T_p` (level-`N` no-diamond case) preserves the Nebentypus.**

For `p ∣ N`, the upper-triangular Hecke sum `heckeT_p_divN` at level
`Γ₁(N)` commutes with the Γ₀(N)-slash action on `⇑f`, hence preserves
every `modFormCharSpace k χ` at level `Γ₁(N).map mapGL ℝ`.  Proof
via `heckeT_p_ut_orbit_comm_gamma0_fun` (which moves the slash
inside the Hecke sum as a diamond twist on `⇑f`), followed by `hf` at
the chosen `Γ₀(N)`-representative and the linearity of
`heckeT_p_divN`. -/
theorem heckeT_p_divN_preserves_modFormCharSpace
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    HeckeRing.GL2.heckeT_p_divN k p hp hpN f ∈ modFormCharSpace k χ := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  show (HeckeRing.GL2.heckeT_p_ut k p hp.pos ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    ↑(χ (Gamma0MapUnits g)) • HeckeRing.GL2.heckeT_p_ut k p hp.pos ⇑f
  rw [HeckeRing.GL2.heckeT_p_ut_orbit_comm_gamma0_fun k p hp hpN f g]
  show HeckeRing.GL2.heckeT_p_ut k p hp.pos (⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) = _
  rw [hf g]
  set c : ℂ := ↑(χ (Gamma0MapUnits g))
  change HeckeRing.GL2.heckeT_p_ut k p hp.pos (c • ⇑f) =
    c • HeckeRing.GL2.heckeT_p_ut k p hp.pos ⇑f
  ext z
  exact DFunLike.congr_fun
    ((HeckeRing.GL2.heckeT_p_divN k p hp hpN).map_smul c f) z

/-- **Level-raise pulls back the Nebentypus.**

For `f ∈ modFormCharSpace_M(k, χ)` and `d ≥ 1`, the level-raised form
`modularFormLevelRaise M d k f` at level `Γ₁(d·M)` lies in
`modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d)))`.
The slash action of a `Γ₀(d·M)` element `γ'` on `levelRaiseFun d k ⇑f`
transports through `α_d` to a slash by the conjugate
`levelRaiseConjOfDvd d γ' _ ∈ Γ₀(M)` via `slash_mapGL_levelRaiseFun`;
applying `hf` to this conjugate and matching characters (both are
determined by the same `γ'.val 1 1 : ℤ`) closes the proof. -/
theorem modularFormLevelRaise_mem_modFormCharSpace
    (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) (χ : (ZMod M)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    HeckeRing.GL2.modularFormLevelRaise M d k f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro γ'
  have hdvd : (d : ℤ) ∣ ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    HeckeRing.GL2.Gamma0_dmul_lower_left_dvd d M _ γ'.property
  rw [HeckeRing.GL2.coe_modularFormLevelRaise,
    HeckeRing.GL2.slash_mapGL_levelRaiseFun d k _ hdvd]
  have h_conj_G0 :
      (HeckeRing.GL2.levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd : SL(2, ℤ)) ∈
        Gamma0 M :=
    HeckeRing.GL2.levelRaiseConjOfDvd_mem_Gamma0 d M _ γ'.property
  rw [hf ⟨_, h_conj_G0⟩]
  have h_char_eq :
      χ (Gamma0MapUnits (⟨_, h_conj_G0⟩ : ↥(Gamma0 M))) =
      (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) (Gamma0MapUnits γ') := by
    rw [MonoidHom.comp_apply]
    congr 1
    apply Units.ext
    rw [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0MapUnits_val]
    show (((HeckeRing.GL2.levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd
      : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M) = _
    rw [HeckeRing.GL2.levelRaiseConjOfDvd_lower_right]
    exact (ZMod.cast_intCast (Nat.dvd_mul_left M d)
      (((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)).symm
  rw [h_char_eq]
  set c : ℂ :=
    ↑((χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) (Gamma0MapUnits γ'))
  change HeckeRing.GL2.levelRaiseFun d k (c • ⇑f) =
    c • HeckeRing.GL2.levelRaiseFun d k ⇑f
  ext z
  exact DFunLike.congr_fun
    ((HeckeRing.GL2.modularFormLevelRaise M d k).map_smul c f) z

/-! ### Miyake Main Lemma 4.6.8 — Nebentypus-aware sieve (Finset version)

Strengthens `miyake_4_6_5_finset_sieve_heckeT_p_divN_one` (T085) by
additionally tracking the Nebentypus character at each intermediate
level.  For a prime `p₀` divisor step from level `M_prev` to
`p₀ · M_prev`:

* `restrictSubgroup g_prev` stays in the pulled-back character space
  (by `restrictSubgroup_mem_modFormCharSpace`).
* `heckeT_p_divN k p₀ … g_prev` preserves the character space at
  level `M_prev` (by `heckeT_p_divN_preserves_modFormCharSpace`).
* `modularFormLevelRaise M_prev p₀ k` pulls back the character along
  `ZMod.unitsMap (M_prev ∣ p₀ · M_prev)` (by
  `modularFormLevelRaise_mem_modFormCharSpace`).

Composing all three pullbacks yields the final character
`χ.comp (ZMod.unitsMap (M ∣ M · S.prod id))` at the Finset-product
level.  `Submodule.sub_mem` closes out the difference construction. -/
theorem miyake_main_lemma_4_6_8_finset
    {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ∃ (M' : ℕ) (_ : NeZero M') (_ : M' = M * S.prod id) (hdvd : M ∣ M')
      (g : ModularForm ((Gamma1 M').map (mapGL ℝ)) k),
      g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd)) ∧
      ∀ n : ℕ, (qExpansion (1 : ℝ) g).coeff n =
        (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) f).coeff n) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨M, inferInstance, by simp, dvd_refl M, f, ?_, ?_⟩
    · convert hf using 2
      rw [ZMod.unitsMap_self, MonoidHom.comp_id]
    · intro n; simp
  | @insert p₀ S' hp₀_notin IH =>
    have hS' : ∀ p ∈ S', p.Prime ∧ p ∣ M :=
      fun p hp => hS p (Finset.mem_insert_of_mem hp)
    have hp₀_prime : p₀.Prime := (hS p₀ (Finset.mem_insert_self p₀ S')).1
    have hp₀_M : p₀ ∣ M := (hS p₀ (Finset.mem_insert_self p₀ S')).2
    obtain ⟨M_prev, hM_prev_ne, hM_prev_eq, hdvd_prev, g_prev, hg_prev_char, hg_prev⟩ :=
      IH hS'
    have hp₀_M_prev : p₀ ∣ M_prev := hM_prev_eq ▸ hp₀_M.mul_right _
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ M_prev :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime, dvd_refl _, hp₀_M_prev⟩
    haveI : NeZero p₀ := ⟨hp₀_prime.ne_zero⟩
    haveI hM_new_ne : NeZero (p₀ * M_prev) :=
      ⟨Nat.mul_ne_zero hp₀_prime.ne_zero hM_prev_ne.out⟩
    have hM_new_eq : p₀ * M_prev = M * (insert p₀ S').prod id := by
      rw [hM_prev_eq, Finset.prod_insert hp₀_notin]
      simp; ring
    have h_mp_dvd : M_prev ∣ p₀ * M_prev := ⟨p₀, by ring⟩
    have hdvd_new : M ∣ p₀ * M_prev := hdvd_prev.trans h_mp_dvd
    have h_le : (Gamma1 (p₀ * M_prev)).map (mapGL ℝ) ≤ (Gamma1 M_prev).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (h_mp_dvd)
    refine ⟨p₀ * M_prev, hM_new_ne, hM_new_eq, hdvd_new,
      ModularForm.restrictSubgroup h_le g_prev -
        HeckeRing.GL2.modularFormLevelRaise M_prev p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g_prev),
      ?_, ?_⟩
    · -- Character-space membership of the new form.
      have h_comp_eq :
          (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_mp_dvd) =
            χ.comp (ZMod.unitsMap hdvd_new) := by
        rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
      refine Submodule.sub_mem _ ?_ ?_
      · have := restrictSubgroup_mem_modFormCharSpace
          (χ.comp (ZMod.unitsMap hdvd_prev)) h_mp_dvd g_prev hg_prev_char
        rwa [h_comp_eq] at this
      · have h_ht := heckeT_p_divN_preserves_modFormCharSpace hp₀_prime
          hp₀_not_coprime (χ.comp (ZMod.unitsMap hdvd_prev)) hg_prev_char
        have h_lr := modularFormLevelRaise_mem_modFormCharSpace M_prev p₀ k
          (χ.comp (ZMod.unitsMap hdvd_prev)) h_ht
        rwa [h_comp_eq] at h_lr
    · -- Coefficient formula: mirrors the T085 induction step.
      intro n
      have h1_pos : (0 : ℝ) < 1 := one_pos
      have h1_period :
          (1 : ℝ) ∈ ((Gamma1 (p₀ * M_prev)).map (mapGL ℝ)).strictPeriods := by
        rw [show (Gamma1 (p₀ * M_prev)).map (mapGL ℝ) =
              (Gamma1 (p₀ * M_prev) : Subgroup (GL (Fin 2) ℝ)) from rfl,
          CongruenceSubgroup.strictPeriods_Gamma1]
        exact ⟨1, by simp⟩
      rw [show ⇑(ModularForm.restrictSubgroup h_le g_prev -
            HeckeRing.GL2.modularFormLevelRaise M_prev p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g_prev)) =
          ⇑(ModularForm.restrictSubgroup h_le g_prev) -
          ⇑(HeckeRing.GL2.modularFormLevelRaise M_prev p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g_prev)) from
        ModularForm.coe_sub _ _]
      rw [qExpansion_sub h1_pos h1_period, map_sub]
      have h_restrict_coeff :
          (qExpansion (1 : ℝ)
            (ModularForm.restrictSubgroup h_le g_prev)).coeff n =
          (qExpansion (1 : ℝ) g_prev).coeff n := rfl
      rw [h_restrict_coeff]
      have hT83 :=
        miyake_4_6_5_prime_sieve_heckeT_p_divN_one hp₀_prime hp₀_not_coprime g_prev n
      rw [hT83, hg_prev n]
      by_cases hn_p₀ : p₀ ∣ n
      · have h_ex : ∃ p ∈ insert p₀ S', p ∣ n :=
          ⟨p₀, Finset.mem_insert_self _ _, hn_p₀⟩
        rw [if_pos hn_p₀, if_pos h_ex]
      · rw [if_neg hn_p₀]
        by_cases hn_S' : ∃ q ∈ S', q ∣ n
        · have h_ex : ∃ p ∈ insert p₀ S', p ∣ n := by
            obtain ⟨q, hqS', hqn⟩ := hn_S'
            exact ⟨q, Finset.mem_insert_of_mem hqS', hqn⟩
          rw [if_pos hn_S', if_pos h_ex]
        · rw [if_neg hn_S']
          have h_nex : ¬ ∃ p ∈ insert p₀ S', p ∣ n := by
            rintro ⟨p, hp_mem, hpn⟩
            rcases Finset.mem_insert.mp hp_mem with rfl | hp_S'
            · exact hn_p₀ hpn
            · exact hn_S' ⟨p, hp_S', hpn⟩
          rw [if_neg h_nex]

/-- **Miyake Main Lemma 4.6.8 (square-free case).**

For a square-free sieve modulus `L` whose distinct prime factors all
divide `M`, and `f ∈ modFormCharSpace_M(k, χ)`, there is a modular
form `g` at level `Γ₁(M · L)` lying in the pulled-back character
space `modFormCharSpace k (χ.comp (ZMod.unitsMap (M ∣ M · L)))` whose
period-`1` Fourier coefficients coincide with the `L`-coprime sieve
`sievedQExpansion 1 L ⇑f` of `f`'s coefficients.

This is Miyake Theorem 4.6.8 at the modular-form level for square-free
`L`.  Consumes `miyake_main_lemma_4_6_8_finset` (T095 Finset-induction)
at `S := L.primeFactors`, collapsing `L.primeFactors.prod id = L` via
`Nat.prod_primeFactors_of_squarefree`, and bridging the
`∃ p ∈ L.primeFactors, p ∣ n` indicator to `Nat.Coprime n L` via
`sievedQExpansion_eq_finsetPrimeCoeffSieve`. -/
theorem miyake_main_lemma_4_6_8_squarefree
    {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ)
    {L : ℕ} (hL : Squarefree L) (hL_M : ∀ p ∈ L.primeFactors, p ∣ M) :
    ∃ (_ : NeZero (M * L)) (g : ModularForm ((Gamma1 (M * L)).map (mapGL ℝ)) k),
      g ∈ modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L))) ∧
      ∀ n : ℕ, (qExpansion (1 : ℝ) g).coeff n =
        (sievedQExpansion 1 L ⇑f).coeff n := by
  have hS_prime_dvd : ∀ p ∈ L.primeFactors, p.Prime ∧ p ∣ M :=
    fun p hp => ⟨Nat.prime_of_mem_primeFactors hp, hL_M p hp⟩
  have h_prod : L.primeFactors.prod id = L := by
    show ∏ p ∈ L.primeFactors, p = L
    exact Nat.prod_primeFactors_of_squarefree hL
  have hL_ne : L ≠ 0 := hL.ne_zero
  obtain ⟨M', hM'_ne, hM'_eq, hdvd', g, hg_char, hg⟩ :=
    miyake_main_lemma_4_6_8_finset χ f hf L.primeFactors hS_prime_dvd
  rw [h_prod] at hM'_eq
  subst hM'_eq
  refine ⟨hM'_ne, g, ?_, ?_⟩
  · -- Both `hdvd'` (from the Finset theorem) and `Nat.dvd_mul_right M L`
    -- are proofs of `M ∣ M * L`, hence definitionally equal in Lean 4.
    exact hg_char
  · intro n
    rw [hg n, sievedQExpansion_eq_finsetPrimeCoeffSieve 1 L hL_ne ⇑f n]
    by_cases h_ex : ∃ p ∈ L.primeFactors, p ∣ n
    · rw [if_pos h_ex, finsetPrimeCoeffSieve_of_exists_dvd _ h_ex]
    · rw [if_neg h_ex]
      push_neg at h_ex
      rw [finsetPrimeCoeffSieve_of_forall_not_dvd _ h_ex, Nat.cast_one]

/-- **Miyake Main Lemma 4.6.8 — general `L ≠ 0` via radical reduction.**

Generalises `miyake_main_lemma_4_6_8_squarefree` from square-free `L`
to arbitrary nonzero `L` by replacing `L` with its **radical**
`L_rad := L.primeFactors.prod id = ∏ p ∈ L.primeFactors, p`
(the product of distinct prime divisors of `L`, always square-free).

At the coefficient level, `Nat.Coprime n L` is determined solely by
the prime divisors of `L` (i.e. by `L_rad`), so the `L`-sieved
`q`-expansion and the `L_rad`-sieved `q`-expansion coincide —
captured exactly by `sievedQExpansion_eq_coprime_radical`.

The result lives at the natural minimal level `Γ₁(M · L_rad)`:
multiplicities in `L` do not affect the sieve, so the extra `p²`
factors in `L` need not appear in the target level.  Callers who
need a form at the caller-facing level `Γ₁(M · L)` should use the
convenience corollary `miyake_main_lemma_4_6_8_level_L` instead,
which does the `restrictSubgroup_mem_modFormCharSpace` composition
automatically. -/
theorem miyake_main_lemma_4_6_8_radical
    {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ)
    {L : ℕ} (hL_ne : L ≠ 0) (hL_M : ∀ p ∈ L.primeFactors, p ∣ M) :
    ∃ (_ : NeZero (M * L.primeFactors.prod id))
      (g : ModularForm
        ((Gamma1 (M * L.primeFactors.prod id)).map (mapGL ℝ)) k),
      g ∈ modFormCharSpace k
          (χ.comp (ZMod.unitsMap
            (Nat.dvd_mul_right M (L.primeFactors.prod id)))) ∧
      ∀ n : ℕ, (qExpansion (1 : ℝ) g).coeff n =
        (sievedQExpansion 1 L ⇑f).coeff n := by
  -- The radical `L_rad := L.primeFactors.prod id` is square-free.
  have hL_rad_sf : Squarefree (L.primeFactors.prod id) := by
    show Squarefree (∏ p ∈ L.primeFactors, p)
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro p hp q hq hpq
      show IsRelPrime p q
      rw [← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp)
        (Nat.prime_of_mem_primeFactors hq)).mpr hpq
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).prime.squarefree
  -- `L_rad.primeFactors = L.primeFactors`, so the divisibility hypothesis
  -- transfers.
  have hL_rad_pf : (L.primeFactors.prod id).primeFactors = L.primeFactors := by
    show (∏ p ∈ L.primeFactors, p).primeFactors = L.primeFactors
    exact Nat.primeFactors_prod (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  have hL_rad_M : ∀ p ∈ (L.primeFactors.prod id).primeFactors, p ∣ M := by
    rw [hL_rad_pf]; exact hL_M
  -- Apply the square-free case at `L_rad`.
  obtain ⟨hne, g, hg_char, hg_coeff⟩ :=
    miyake_main_lemma_4_6_8_squarefree χ f hf hL_rad_sf hL_rad_M
  refine ⟨hne, g, hg_char, ?_⟩
  intro n
  rw [hg_coeff n, sievedQExpansion_eq_coprime_radical 1 L hL_ne ⇑f n]
  -- `L.primeFactors.prod id = ∏ p ∈ L.primeFactors, p` definitionally;
  -- normalize to the Finset-product form on both sides.
  show (sievedQExpansion 1 (L.primeFactors.prod id) ⇑f).coeff n =
    if Nat.Coprime n (L.primeFactors.prod id) then
      (qExpansion ((1 : ℕ) : ℝ) ⇑f).coeff n else 0
  by_cases h : Nat.Coprime n (L.primeFactors.prod id)
  · rw [sievedQExpansion_coeff_coprime _ _ _ h, if_pos h]
  · rw [sievedQExpansion_coeff_not_coprime _ _ _ h, if_neg h]

/-- **Miyake Main Lemma 4.6.8 at the caller-facing level `Γ₁(M · L)`.**

Convenience corollary of `miyake_main_lemma_4_6_8_radical`: if the
sieve form is needed at level `Γ₁(M · L)` rather than the minimal
radical level `Γ₁(M · L.primeFactors.prod id)`, restrict along the
inclusion `Γ₁(M · L) ⊆ Γ₁(M · L.primeFactors.prod id)` (which holds
because `L.primeFactors.prod id ∣ L` by `Nat.prod_primeFactors_dvd`).

The character transports through the composed pullback:
`(χ.comp (ZMod.unitsMap (M ∣ M · L_rad))).comp (ZMod.unitsMap (M · L_rad ∣ M · L))`
equals `χ.comp (ZMod.unitsMap (M ∣ M · L))` by
`MonoidHom.comp_assoc` + `ZMod.unitsMap_comp`.  The `q`-expansion
coefficient equality is preserved because `ModularForm.restrictSubgroup`
does not change the underlying function. -/
theorem miyake_main_lemma_4_6_8_level_L
    {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ)
    {L : ℕ} (hL_ne : L ≠ 0) (hL_M : ∀ p ∈ L.primeFactors, p ∣ M) :
    ∃ (_ : NeZero (M * L))
      (g : ModularForm ((Gamma1 (M * L)).map (mapGL ℝ)) k),
      g ∈ modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L))) ∧
      ∀ n : ℕ, (qExpansion (1 : ℝ) g).coeff n =
        (sievedQExpansion 1 L ⇑f).coeff n := by
  haveI hML : NeZero (M * L) := ⟨Nat.mul_ne_zero (NeZero.ne M) hL_ne⟩
  -- Radical theorem gives a witness at level `Γ₁(M · L_rad)`.
  obtain ⟨_, g0, hg0_char, hg0_coeff⟩ :=
    miyake_main_lemma_4_6_8_radical χ f hf hL_ne hL_M
  -- `L_rad ∣ L` ⟹ `M · L_rad ∣ M · L`.
  have hL_rad_dvd_L : L.primeFactors.prod id ∣ L := by
    show ∏ p ∈ L.primeFactors, p ∣ L
    exact Nat.prod_primeFactors_dvd L
  have hM_dvd : M * L.primeFactors.prod id ∣ M * L :=
    Nat.mul_dvd_mul_left M hL_rad_dvd_L
  -- Restrict `g0` from level `Γ₁(M · L_rad)` to `Γ₁(M · L)`.
  have h_restrict := restrictSubgroup_mem_modFormCharSpace
    (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (L.primeFactors.prod id))))
    hM_dvd g0 hg0_char
  refine ⟨inferInstance,
    ModularForm.restrictSubgroup
      (Gamma1_mapGL_le_of_dvd (hM_dvd)) g0, ?_, ?_⟩
  · -- Character: compose the two pullbacks via `MonoidHom.comp_assoc`
    -- + `ZMod.unitsMap_comp` to land at the direct pullback by
    -- `Nat.dvd_mul_right M L`.
    have h_comp_eq :
        (χ.comp (ZMod.unitsMap
            (Nat.dvd_mul_right M (L.primeFactors.prod id)))).comp
          (ZMod.unitsMap hM_dvd) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L)) := by
      rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
    exact h_comp_eq ▸ h_restrict
  · -- Coefficient: `restrictSubgroup` preserves `⇑` at period 1, so
    -- `qExpansion 1 (restrictSubgroup _ g0) = qExpansion 1 g0` as
    -- `PowerSeries`; the coefficient identity transports from T100.
    intro n
    exact hg0_coeff n

/-! ### T131 — Coprime-vanishing strengthening of the level-L Miyake witness -/

/-- **T131 strengthening**: under the coprime-to-`L` Fourier vanishing
hypothesis on `f`, the level-`Γ₁(M·L)` Miyake witness `g` produced by
`miyake_main_lemma_4_6_8_level_L` has **identically zero** period-1
`q`-expansion.

The conclusion `qExpansion 1 g = 0 (as PowerSeries ℂ)` is the
"strictly reducing" intermediate step toward expressing the original
form as a finite sum of level-raised pieces: combined with q-expansion
injectivity for `ModularForm Γ k` (Mathlib
`qExpansion_eq_zero_iff` for general `Γ` with the appropriate strict-
period and arithmetic instances) this would give `g = 0`, and
unrolling the recursive sieve construction would express
`restrictSubgroup f` as a sum of level-raised correction terms.

Proof: the Miyake-witness coefficient identity from
`miyake_main_lemma_4_6_8_level_L` reduces each coefficient of `g` to a
`sievedQExpansion 1 L ⇑f` coefficient, which is `0` either by
`sievedQExpansion_coeff_not_coprime` (non-coprime indices) or by the
coprime-vanishing hypothesis (coprime indices), in both cases yielding
`0`. -/
theorem miyake_main_lemma_4_6_8_level_L_witness_qExpansion_zero
    {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ)
    {L : ℕ} (hL_ne : L ≠ 0) (hL_M : ∀ p ∈ L.primeFactors, p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    ∃ (_ : NeZero (M * L))
      (g : ModularForm ((Gamma1 (M * L)).map (mapGL ℝ)) k),
      g ∈ modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L))) ∧
      (qExpansion (1 : ℝ) g) = (0 : PowerSeries ℂ) := by
  obtain ⟨hML, g, hg_char, hg_coeff⟩ :=
    miyake_main_lemma_4_6_8_level_L χ f hf hL_ne hL_M
  refine ⟨hML, g, hg_char, ?_⟩
  ext n
  rw [hg_coeff n]
  by_cases h : Nat.Coprime n L
  · rw [sievedQExpansion_coeff_coprime _ _ _ h]
    -- Goal: (qExpansion ((1 : ℕ) : ℝ) ⇑f).coeff n = (PowerSeries.coeff n) 0
    rw [show ((1 : ℕ) : ℝ) = (1 : ℝ) from Nat.cast_one, h_vanish n h]
    simp
  · rw [sievedQExpansion_coeff_not_coprime _ _ _ h]
    simp

/-- **q-expansion injectivity at level `Γ₁(N)`**.  Specialisation of
Mathlib's `qExpansion_eq_zero_iff` to the `Γ₁(N).map (mapGL ℝ)`
flavor at canonical Miyake period `h = 1`.  The strict-period membership
`(1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods` follows from
`CongruenceSubgroup.strictPeriods_Gamma1`. -/
private theorem qExpansion_one_Gamma1_eq_zero_iff
    {N : ℕ} [NeZero N] {k : ℤ}
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion (1 : ℝ) g = 0 ↔ g = 0 := by
  apply qExpansion_eq_zero_iff one_pos
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    CongruenceSubgroup.strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

/-- **T131 zero-witness consumer**: composes the q-expansion-zero
corollary with q-expansion injectivity (`qExpansion_one_Gamma1_eq_zero_iff`)
to conclude that the level-`Γ₁(M·L)` Miyake witness `g` is the zero
modular form when `f` satisfies coprime-to-`L` Fourier vanishing. -/
theorem miyake_main_lemma_4_6_8_level_L_witness_eq_zero
    {M : ℕ} [NeZero M] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ)
    {L : ℕ} (hL_ne : L ≠ 0) (hL_M : ∀ p ∈ L.primeFactors, p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    ∃ (_ : NeZero (M * L))
      (g : ModularForm ((Gamma1 (M * L)).map (mapGL ℝ)) k),
      g ∈ modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L))) ∧
      g = 0 := by
  obtain ⟨hML, g, hg_char, hg_qzero⟩ :=
    miyake_main_lemma_4_6_8_level_L_witness_qExpansion_zero χ f hf hL_ne hL_M h_vanish
  exact ⟨hML, g, hg_char, (qExpansion_one_Gamma1_eq_zero_iff g).mp hg_qzero⟩

/-! ### T131 — Recursive `iteratedSieveWitnessOnList` (data-level Miyake sieve) -/

/-- **Recursive Miyake-sieve witness, list backbone (T131)**.  Given a
base modular form `f ∈ M_k(Γ₁(M))` and a list `L : List ℕ` of primes
each dividing `M`, produces the modular form at the deeper level
`Γ₁(M · ∏ L)` constructed by iteratively subtracting level-raised
`heckeT_p_divN` corrections, exactly mirroring the proof of
`miyake_4_6_5_finset_sieve_heckeT_p_divN_one`.

Empty case: returns `f` (level `M = M · ∏ []`).  Cons case: at
`p₀ :: L'` with prior witness `g_prev` at level `M · ∏ L'`, returns
`restrictSubgroup g_prev − modularFormLevelRaise (M · ∏ L') p₀ k
  (heckeT_p_divN k p₀ _ _ g_prev)`,
restricted to level `Γ₁(p₀ · M · ∏ L') = Γ₁(M · ∏ (p₀ :: L'))`. -/
private noncomputable def iteratedSieveWitnessOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k
  | [], _ =>
    (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL' p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
      hL' p₀ (List.mem_cons_self)
    let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_M_prev : p₀ ∣ M * L'.prod :=
      hp₀_prime_M.2.mul_right _
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    let g_new : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      ModularForm.restrictSubgroup h_le g_prev -
        HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    hM_eq ▸ g_new

/-- **Empty-list unfolding of `iteratedSieveWitnessOnList`** (T131 step
identity).  The witness at `L = []` is just `f` cast through the
trivial `M = M · 1` level identity. -/
private theorem iteratedSieveWitnessOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveWitnessOnList f [] h =
      (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f :=
  rfl

/-- **Cons-step unfolding of `iteratedSieveWitnessOnList`** (T131 step
identity).  Exposes the recursive structure: the witness at `p₀ :: L'`
equals the type-level cast through `p₀ · (M · ∏ L') = M · ∏ (p₀ :: L')`
of `restrictSubgroup g_prev − modularFormLevelRaise (M · ∏ L') p₀ k
  (heckeT_p_divN k p₀ _ _ g_prev)`, where `g_prev` is the recursive
witness on `L'`.  Proved by `rfl` against the def body. -/
private theorem iteratedSieveWitnessOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL' : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    iteratedSieveWitnessOnList f (p₀ :: L') hL' =
      (let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp => hL' p (List.mem_cons_of_mem _ hp)
       let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
        hL' p₀ List.mem_cons_self
       let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props
       haveI hM_prev_ne : NeZero (M * L'.prod) := by
         have hL'_pos : 0 < L'.prod := by
           apply List.prod_pos
           intro p hp
           exact (hL'_props p hp).1.pos
         exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
       haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
       have hp₀_M_prev : p₀ ∣ M * L'.prod :=
         hp₀_prime_M.2.mul_right _
       have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
         Nat.Prime.not_coprime_iff_dvd.mpr
           ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
       have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
           (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
         Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
       have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
         rw [List.prod_cons]; ring
       hM_eq ▸ (ModularForm.restrictSubgroup h_le g_prev -
         HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
           (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
             g_prev))) :=
  rfl

/-- **Level-cast preservation of q-expansion coefficient** (T131 helper).
For `h : M = N`, the period-1 q-expansion coefficient of the cast
`h ▸ g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k` agrees with that of
the original `g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k`.  Proof
`subst h; rfl` works because `M` and `N` are independent local
variables; the q-expansion only depends on the underlying function. -/
private theorem qExpansion_coeff_cast_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ)
        ((h ▸ g) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n =
      (qExpansion (1 : ℝ) g).coeff n := by
  subst h
  rfl

/-- **Coefficient identity for `iteratedSieveWitnessOnList`** (T131
List-level coefficient theorem).  At every period-1 Fourier index `n`,
the witness's coefficient is the `L`-prime-set sieve of `f`'s
coefficient: zero if any prime in `L` divides `n`, else the original
coefficient of `f` at `n`.

Proof: `List.rec` with the nil case from
`iteratedSieveWitnessOnList_nil` and the cons case from
`iteratedSieveWitnessOnList_cons`, plus the helper-decoupled
`qExpansion_coeff_cast_Gamma1` for level-cast reduction, plus
`miyake_4_6_5_prime_sieve_heckeT_p_divN_one` (T083) for the per-prime
single-step sieve, mirroring the existing Finset proof of
`miyake_4_6_5_finset_sieve_heckeT_p_divN_one`. -/
private theorem iteratedSieveWitnessOnList_qExpansion_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M) (n : ℕ),
    (qExpansion (1 : ℝ) (iteratedSieveWitnessOnList f L hL)).coeff n =
      (if ∃ p ∈ L, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n)
  | [], _, n => by
    rw [iteratedSieveWitnessOnList_nil,
      qExpansion_coeff_cast_Gamma1 (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) f n]
    simp
  | p₀ :: L', hL', n => by
    rw [iteratedSieveWitnessOnList_cons]
    -- Build the auxiliary terms (matching the def's let/have block).
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
    set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL' p₀ List.mem_cons_self with hp₀_def
    set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props with hg_prev_def
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    haveI hM_new_ne : NeZero (p₀ * (M * L'.prod)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
    -- Apply the helper to reduce the cast.
    rw [qExpansion_coeff_cast_Gamma1 hM_eq _ n]
    -- Expand the difference into restrictSubgroup g_prev - levelRaise(...).
    have h1_pos : (0 : ℝ) < 1 := one_pos
    have h1_period : (1 : ℝ) ∈
        ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) =
            (Gamma1 (p₀ * (M * L'.prod)) : Subgroup (GL (Fin 2) ℝ)) from rfl,
        CongruenceSubgroup.strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    rw [show ⇑(ModularForm.restrictSubgroup h_le g_prev -
          HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
              g_prev)) =
        ⇑(ModularForm.restrictSubgroup h_le g_prev) -
        ⇑(HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
              g_prev)) from
      ModularForm.coe_sub _ _]
    rw [qExpansion_sub h1_pos h1_period, map_sub]
    -- `qExpansion 1 (restrictSubgroup g_prev) = qExpansion 1 g_prev` (rfl).
    have h_restrict_coeff :
        (qExpansion (1 : ℝ)
          (ModularForm.restrictSubgroup h_le g_prev)).coeff n =
        (qExpansion (1 : ℝ) g_prev).coeff n := rfl
    rw [h_restrict_coeff]
    -- T083 at prime `p₀`.
    have hT83 :=
      miyake_4_6_5_prime_sieve_heckeT_p_divN_one hp₀_prime_M.1
        hp₀_not_coprime g_prev n
    rw [hT83]
    -- Inductive hypothesis on `L'`.
    rw [iteratedSieveWitnessOnList_qExpansion_coeff f L' hL'_props n]
    -- Case split.
    by_cases hn_p₀ : p₀ ∣ n
    · have h_ex : ∃ p ∈ p₀ :: L', p ∣ n :=
        ⟨p₀, List.mem_cons_self, hn_p₀⟩
      rw [if_pos hn_p₀, if_pos h_ex]
    · rw [if_neg hn_p₀]
      by_cases hn_L' : ∃ q ∈ L', q ∣ n
      · have h_ex : ∃ p ∈ p₀ :: L', p ∣ n := by
          obtain ⟨q, hqL', hqn⟩ := hn_L'
          exact ⟨q, List.mem_cons_of_mem _ hqL', hqn⟩
        rw [if_pos hn_L', if_pos h_ex]
      · rw [if_neg hn_L']
        have h_nex : ¬ ∃ p ∈ p₀ :: L', p ∣ n := by
          rintro ⟨p, hp_mem, hpn⟩
          rcases List.mem_cons.mp hp_mem with rfl | hp_L'
          · exact hn_p₀ hpn
          · exact hn_L' ⟨p, hp_L', hpn⟩
        rw [if_neg h_nex]

/-- **Coprime-to-prod vanishing implies zero q-expansion of the
iterated witness** (T131 zero-q-expansion bridge).  Combines the
List-level coefficient theorem with the case split: if every prime in
`L` divides `n` (or some does), the witness coefficient is `0` directly;
otherwise `n` is coprime to `L.prod` so the hypothesis `h_vanish`
gives `0` for `f`'s coefficient. -/
private theorem iteratedSieveWitnessOnList_qExpansion_zero_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    qExpansion (1 : ℝ) (iteratedSieveWitnessOnList f L hL) = 0 := by
  ext n
  rw [iteratedSieveWitnessOnList_qExpansion_coeff f L hL n]
  by_cases hdiv : ∃ p ∈ L, p ∣ n
  · rw [if_pos hdiv]; simp
  · rw [if_neg hdiv]
    have hcop : Nat.Coprime n L.prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro p hpL
      exact ((hL p hpL).1.coprime_iff_not_dvd.mpr
        (fun hpn => hdiv ⟨p, hpL, hpn⟩)).symm
    rw [h_vanish n hcop]; simp

/-- **Iterated sieve witness is zero under coprime-to-prod vanishing**
(T131 zero-witness bridge).  Form-level conclusion: under coprime-to-`L.prod`
Fourier vanishing of `f`, the recursive iterated sieve witness equals
the zero modular form.  Proof: q-expansion-zero corollary above plus
the existing private `qExpansion_one_Gamma1_eq_zero_iff` wrapper around
Mathlib's `qExpansion_eq_zero_iff`. -/
private theorem iteratedSieveWitnessOnList_eq_zero_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    iteratedSieveWitnessOnList f L hL = 0 := by
  haveI hML_ne : NeZero (M * L.prod) := by
    have hL_pos : 0 < L.prod := by
      apply List.prod_pos
      intro p hp
      exact (hL p hp).1.pos
    exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  exact (qExpansion_one_Gamma1_eq_zero_iff
    (iteratedSieveWitnessOnList f L hL)).mp
    (iteratedSieveWitnessOnList_qExpansion_zero_of_coprime_prod_vanish
      f L hL h_vanish)

/-- **Level-cast preservation of zero modular form** (T131 helper).
For `h : M = N`, the cast `h ▸ g` is the zero modular form iff `g` is.
Proof `subst h; rfl` works because `M, N` are independent binders. -/
private theorem cast_eq_zero_iff_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ((h ▸ g) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 ↔ g = 0 := by
  subst h
  rfl

/-- **One-cons-step unrolling** (T131).  Flat-hypothesis form: from
`iteratedSieveWitnessOnList f (p₀ :: L') hL = 0`, derive that the
restricted previous-step witness equals the one level-raised
`heckeT_p_divN` correction.  All auxiliary instances and inequalities
are passed as explicit theorem parameters, with no `let`/`haveI` in the
conclusion. -/
private theorem iteratedSieveWitnessOnList_cons_zero_step
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M)
    [NeZero (M * L'.prod)] [NeZero p₀]
    (hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod))
    (h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ))
    (h_zero : iteratedSieveWitnessOnList f (p₀ :: L') hL = 0) :
    ModularForm.restrictSubgroup h_le
        (iteratedSieveWitnessOnList f L'
          (fun p hp => hL p (List.mem_cons_of_mem _ hp))) =
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ (hL p₀ List.mem_cons_self).1
          hp₀_not_coprime
          (iteratedSieveWitnessOnList f L'
            (fun p hp => hL p (List.mem_cons_of_mem _ hp)))) := by
  rw [iteratedSieveWitnessOnList_cons] at h_zero
  have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
    rw [List.prod_cons]; ring
  haveI : NeZero (p₀ * (M * L'.prod)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
  -- Strip the cast: `hM_eq ▸ X = 0 ↔ X = 0`.
  rw [cast_eq_zero_iff_Gamma1 hM_eq _] at h_zero
  -- `h_zero : restrictSubgroup _ _ - levelRaise _ ... = 0`.
  exact sub_eq_zero.mp h_zero

/-! ### Why the ticket's period-M formula was mathematically incorrect

For completeness and to document a subtle pitfall encountered during
T076: the ticket originally asked for

```
(qExpansion (M : ℝ) (heckeT_p_divN k p hp hpM f)).coeff m =
  (qExpansion (M : ℝ) f).coeff (p * m)   -- INCORRECT in general
```

This **fails** when `p ∣ M` and there exists `m` with `M/p ∣ m` and
`M ∤ m` (concrete counterexample: `M = 2, p = 2, m = 1`, generic `f`).
The reason: at period `M`, the q-expansion of a period-`1` form is
sparse — it vanishes at non-multiples of `M` — so the LHS is `0` but the
RHS queries `(qExpansion M f).coeff (p · m)` which can be non-zero
whenever `M ∣ p · m`, i.e., whenever `M/gcd(M, p) ∣ m`.  When `p ∣ M`,
`gcd(M, p) = p` and the RHS sparsity condition is strictly weaker than
the LHS sparsity.

The **correct** period-`M` formula carries an extra `[M ∣ m]` indicator:

```
(qExpansion (M : ℝ) (heckeT_p_divN k p hp hpM f)).coeff m =
  if M ∣ m then (qExpansion (M : ℝ) f).coeff (p * m) else 0
```

At the canonical period `h = 1` (the Miyake convention), no such
indicator is needed and the formula reads simply as T076 above. -/

/-! ### Miyake Theorems 4.6.5 / 4.6.7 / 4.6.8 — API index

The Miyake Main Lemma at modular-form level is now available in four
flavours of increasing generality, all consuming the POST-6
infrastructure below:

* `miyake_4_6_5_squarefree_sieve_heckeT_p_divN_one` (POST-6e, T091) —
  coefficient-only square-free sieve: for `L` square-free with all
  prime factors dividing `M`, produces `g` at level `Γ₁(M · L)`
  matching `sievedQExpansion 1 L ⇑f` coefficient-wise.
* `miyake_main_lemma_4_6_8_squarefree` (POST-6f, T095) — the
  Nebentypus-aware extension of T091: additionally places `g` in
  `modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L)))`
  when `f ∈ modFormCharSpace_M(k, χ)`, still for square-free `L`.
* `miyake_main_lemma_4_6_8_radical` (POST-6g, T100) — generalises
  T095 from square-free `L` to arbitrary `L ≠ 0` by radical
  reduction (`L_rad := L.primeFactors.prod id` is square-free and
  has the same prime factors as `L`).  Places `g` at the minimal
  level `Γ₁(M · L_rad)`.
* `miyake_main_lemma_4_6_8_level_L` (POST-6h, T102) — caller-facing
  convenience corollary of T100 at the user-provided level
  `Γ₁(M · L)`, obtained by restricting from `Γ₁(M · L_rad)` via
  `restrictSubgroup_mem_modFormCharSpace`.

T091/T095 are specialisations of the underlying Finset-induction
theorems `miyake_4_6_5_finset_sieve_heckeT_p_divN_one` (T085,
coefficient-only) and `miyake_main_lemma_4_6_8_finset` (T095,
coefficient + Nebentypus).  T100 reduces to T095 on `L_rad`; T102
then composes T100 with `restrictSubgroup_mem_modFormCharSpace`.

**Proof strategy** (Miyake §4.6.5, faithful; now fully implemented).

The target is a level-`N · Π_{p ∣ L, p ∤ N} p²` (or `N · L` in the
square-free case) modular form `g_L` whose `n`-th Fourier coefficient
is `a_n · [gcd(n, L) = 1]`, with `a_n = (qExpansion 1 f).coeff n` at
the canonical period-1 Miyake convention.  Ingredients:

1. **Single-prime sieve** (T070,
   `miyake_4_6_5_prime_sieve_from_no_diamond_one`).  For any prime
   `p`, given a modular form `gp : M_k(Γ₁(N))` whose period-`1`
   coefficients satisfy the no-diamond condition
   `coeff m gp = a_{p · m}` for all `m`, the combination
   `f − modularFormLevelRaise N p k gp` at level `Γ₁(p · N)` has
   coefficients equal to the `p`-coprime sieve of `f`.
2. **No-diamond witness** — landed as T081
   (`qExpansion_one_heckeT_p_divN_coeff` in `QExpansionSlash.lean`):
   the Γ₀(pN)-level Hecke operator `heckeT_p_divN k p hp _` at level
   `M` with `p ∣ M` satisfies the no-diamond coefficient formula
   `(qExpansion 1 (heckeT_p_divN k p hp _ f)).coeff m =
    (qExpansion 1 f).coeff (p · m)` at period `1`.  T083
   (`miyake_4_6_5_prime_sieve_heckeT_p_divN_one`) packages this as
   the concrete single-prime sieve consumed by the iteration.
3. **Iteration over square-free `L`** — landed as T085
   (`miyake_4_6_5_finset_sieve_heckeT_p_divN_one`, Finset induction
   over prime factors) and T091
   (`miyake_4_6_5_squarefree_sieve_heckeT_p_divN_one`, square-free
   specialisation).  Pure induction on the prime factorisation of
   `L`, consuming T083 once per prime.
4. **Nebentypus transport** — landed as T095 via the three reusable
   character-space compatibility lemmas
   `restrictSubgroup_mem_modFormCharSpace`,
   `modularFormLevelRaise_mem_modFormCharSpace`, and
   `heckeT_p_divN_preserves_modFormCharSpace`; assembled in
   `miyake_main_lemma_4_6_8_finset` / `miyake_main_lemma_4_6_8_squarefree`.

All four steps are now concrete theorems; no remaining POST-6 API
gaps.  Steps 1–4 cover square-free `L`; the radical-reduction
theorem `miyake_main_lemma_4_6_8_radical` (POST-6g, T100) extends
this to arbitrary `L ≠ 0`, and `miyake_main_lemma_4_6_8_level_L`
(POST-6h, T102) exposes the result at the caller-provided level.

**Infrastructure status** (as of POST-6h T102).

* ✅ Level-raising bundle `modularFormLevelRaise M d k` (LevelRaise.lean,
  T066): the ModularForm analog of the existing CuspForm `levelRaise`,
  together with the pointwise evaluation lemmas
  `modularFormLevelRaise_apply` and `modularFormLevelRaise_apply_mul`.
* ✅ `ModularForm.restrictSubgroup` along a subgroup inclusion
  `Γ' ≤ Γ` (LevelRaise.lean, T066).  Combined with
  `Gamma1_le_of_dvd`, gives the restriction `M_k(Γ₁(N · d)) →
  M_k(Γ₁(N · L))` for `d ∣ L`.
* ✅ q-expansion **d-dilation** coefficient formula for
  `modularFormLevelRaise` (LevelRaise.lean, T068).  **T068 supplies
  the dilation formula only**; it is not a collapse of the Möbius
  sum to `sievedQExpansion` (see the scope note below).
* ✅ **Miyake 4.6.5 single-prime sieve from the no-diamond hypothesis**
  (MainLemma.lean, T070 / T076 period-1 variant
  `miyake_4_6_5_prime_sieve_from_no_diamond_one`).  Given any `g`
  satisfying the no-diamond condition, the difference
  `f − modularFormLevelRaise N p k g` has period-`1` Fourier
  coefficients equal to the exact `p`-coprime sieve of `f`.
* ✅ **Miyake Γ₀(pN)-level Hecke operator witness** (T073/T076),
  reusing `HeckeRing.GL2.heckeT_p_divN` from `HeckeT_n.lean` and
  landing the period-1 witness lemma
  `miyake_4_6_5_prime_sieve_witness_at_pN_one`.
* ✅ **Period-1 no-diamond coefficient formula for `heckeT_p_divN`**
  (T081, `qExpansion_one_heckeT_p_divN_coeff` in `QExpansionSlash.lean`):
  `(qExpansion (1 : ℝ) (heckeT_p_divN k p hp hpM f)).coeff m =
   (qExpansion (1 : ℝ) f).coeff (p * m)`, at the canonical Miyake
  period.  T083 bundles this into the concrete single-prime sieve
  `miyake_4_6_5_prime_sieve_heckeT_p_divN_one`.
* ✅ **Iteration over square-free `L`** (Miyake Lemma 4.6.7 / Theorem
  4.6.8, T085 `miyake_4_6_5_finset_sieve_heckeT_p_divN_one` +
  T091 `miyake_4_6_5_squarefree_sieve_heckeT_p_divN_one`):
  `Finset.induction_on` over prime factors yields the full
  `L`-coprime sieve at level `Γ₁(M · L)`.
* ✅ **Nebentypus pullback along `Γ₀(N · L) ⊆ Γ₀(N)`** (T095):
  `restrictSubgroup_mem_modFormCharSpace` (pullback by
  `ZMod.unitsMap` for `restrictSubgroup`),
  `modularFormLevelRaise_mem_modFormCharSpace` (pullback for level
  raising), and `heckeT_p_divN_preserves_modFormCharSpace` (Hecke
  preserves the same-level character), assembled into
  `miyake_main_lemma_4_6_8_finset` / `_squarefree`.
* ✅ **Radical reduction to arbitrary `L ≠ 0`** (T100,
  `miyake_main_lemma_4_6_8_radical`): `Nat.Coprime n L` depends only
  on the prime divisors of `L`, so the square-free case at
  `L_rad := L.primeFactors.prod id` via
  `sievedQExpansion_eq_coprime_radical`, `Nat.primeFactors_prod`, and
  `Finset.squarefree_prod_of_pairwise_isCoprime` lifts directly to
  arbitrary `L ≠ 0` at the minimal level `Γ₁(M · L_rad)`.
* ✅ **Caller-facing level `Γ₁(M · L)`** (T102,
  `miyake_main_lemma_4_6_8_level_L`): composes T100 with
  `restrictSubgroup_mem_modFormCharSpace` along `M · L_rad ∣ M · L`
  (from `Nat.prod_primeFactors_dvd` + `Nat.mul_dvd_mul_left`);
  characters combine via `MonoidHom.comp_assoc` + `ZMod.unitsMap_comp`.

## Scope note — Miyake's actual construction vs. the naive Möbius sum

The **naive** Möbius-weighted level-raise sum
`g₀ := Σ_{d ∣ L} μ(d) · (modularFormLevelRaise N d k f |_{Γ₁(N·L)})`
has `n`-th period-`N` Fourier coefficient
`Σ_{d ∣ gcd(n, L)} μ(d) · (qExpansion N f).coeff (n / d)` (via T068,
applied to each summand).  This is **not** in general equal to
`(qExpansion N f).coeff n · [gcd(n, L) = 1]
  = (sievedQExpansion N L ⇑f).coeff n`,
because the shifted coefficient `(qExpansion N f).coeff (n / d)` depends
on `d` and cannot be factored out of the Möbius sum.  The identity
`coprime_indicator_eq_sum_moebius` applies to a fixed scalar, not to a
varying sequence of Fourier coefficients.

Miyake §4.6.5's actual construction is **not** the naive Möbius sum.
For a prime `p`, Miyake forms `g_p := f − (f ∣ T(p)^{Γ₀(pN)})(p · τ)`,
where `T(p)^{Γ₀(pN)}` is the Γ₀(pN)-level Hecke operator (with
`p ∣ pN`), whose coefficients satisfy the no-diamond formula
`coeff m (f ∣ T(p)^{Γ₀(pN)}) = a_{p · m}`.  T070's
`miyake_4_6_5_prime_sieve_from_no_diamond` captures this construction
faithfully at the coefficient level, abstracted over any witness
satisfying the no-diamond hypothesis.  For general square-free `L`,
Miyake iterates this single-prime construction over prime factors
`p ∣ L` (Lemma 4.6.7 / Theorem 4.6.8); the Möbius identity
`coprime_indicator_eq_sum_moebius` appears only **inside** each
single-prime step, applied to a fixed scalar `a_n` after the sub-series
reduction has been performed, never to the varying shifted
coefficients. -/

/-! ### T131 — Recursive `iteratedSieveCorrectionsOnList` and decomposition -/

/-- **Recursive Miyake-sieve corrections, list backbone (T131).** Mirrors
`iteratedSieveWitnessOnList`: at each cons step it carries the sum of
all previously level-raised `heckeT_p_divN` corrections plus the new
one for `p₀`.  The decomposition `restrictSubgroup f = witness +
corrections` lands in `iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep`. -/
private noncomputable def iteratedSieveCorrectionsOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k
  | [], _ => 0
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL' p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
      hL' p₀ (List.mem_cons_self)
    let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    let c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveCorrectionsOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_M_prev : p₀ ∣ M * L'.prod :=
      hp₀_prime_M.2.mul_right _
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    let c_new : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      ModularForm.restrictSubgroup h_le c_prev +
        HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    hM_eq ▸ c_new

/-- **Empty-list unfolding of `iteratedSieveCorrectionsOnList`** — equals 0. -/
private theorem iteratedSieveCorrectionsOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionsOnList f [] h = 0 := rfl

/-- **Cons-step unfolding of `iteratedSieveCorrectionsOnList`** — mirrors
`iteratedSieveWitnessOnList_cons` with `+` rather than `-`. -/
private theorem iteratedSieveCorrectionsOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL' : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionsOnList f (p₀ :: L') hL' =
      (let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp => hL' p (List.mem_cons_of_mem _ hp)
       let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
        hL' p₀ List.mem_cons_self
       let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props
       let c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveCorrectionsOnList f L' hL'_props
       haveI hM_prev_ne : NeZero (M * L'.prod) := by
         have hL'_pos : 0 < L'.prod := by
           apply List.prod_pos
           intro p hp
           exact (hL'_props p hp).1.pos
         exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
       haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
       have hp₀_M_prev : p₀ ∣ M * L'.prod :=
         hp₀_prime_M.2.mul_right _
       have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
         Nat.Prime.not_coprime_iff_dvd.mpr
           ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
       have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
           (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
         Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
       have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
         rw [List.prod_cons]; ring
       hM_eq ▸ (ModularForm.restrictSubgroup h_le c_prev +
         HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
           (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
             g_prev))) :=
  rfl

/-- **Restrict-restrict composes** (T131 helper). -/
private theorem ModularForm_restrictSubgroup_restrictSubgroup
    {Γ Γ' Γ'' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (h₁ : Γ' ≤ Γ) (h₂ : Γ'' ≤ Γ')
    (f : ModularForm Γ k) :
    ModularForm.restrictSubgroup h₂ (ModularForm.restrictSubgroup h₁ f) =
      ModularForm.restrictSubgroup (le_trans h₂ h₁) f := rfl

/-- **Cast distributes over `+` for `ModularForm` along a level cast** (T131
helper).  For `h : M = N`, `h ▸ (x + y) = (h ▸ x) + (h ▸ y)`. -/
private theorem cast_add_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (x y : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ((h ▸ (x + y)) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (h ▸ x) + (h ▸ y) := by
  subst h; rfl

/-- **Restriction commutes with level cast** (T131 helper).  Given an
equation `h : A = B` of natural numbers and a base inclusion
`h_le : (Gamma1 A).map ≤ Γ`, the restriction along the cast equals the
cast of the restriction. -/
private theorem restrictSubgroup_cast_eq_of_level_eq
    {A B : ℕ} {k : ℤ} (h : A = B)
    {Γ : Subgroup (GL (Fin 2) ℝ)}
    (h_le_A : (Gamma1 A).map (mapGL ℝ) ≤ Γ)
    (h_le_B : (Gamma1 B).map (mapGL ℝ) ≤ Γ)
    (f : ModularForm Γ k) :
    ((h ▸ ModularForm.restrictSubgroup h_le_A f) :
        ModularForm ((Gamma1 B).map (mapGL ℝ)) k) =
      ModularForm.restrictSubgroup h_le_B f := by
  subst h; rfl

/-- **Cast distributes over `restrictSubgroup` for the trivial level
identity `M = M · 1 = M · ([].prod)`** (T131 nil case helper). -/
private theorem restrictSubgroup_cast_nil_eq
    {M : ℕ} [NeZero M] {k : ℤ}
    (h_le_full : (Gamma1 (M * ([] : List ℕ).prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ModularForm.restrictSubgroup h_le_full f =
      ((show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f) := by
  have hM_eq : M = M * ([] : List ℕ).prod := by simp
  -- View `f` as `restrictSubgroup (le_refl _) f` and use the cast helper.
  have h_self : f = ModularForm.restrictSubgroup (le_refl _) f := rfl
  rw [show ((hM_eq ▸ f) : ModularForm ((Gamma1 (M * ([] : List ℕ).prod)).map
    (mapGL ℝ)) k) =
      hM_eq ▸ ModularForm.restrictSubgroup (le_refl
        ((Gamma1 M).map (mapGL ℝ))) f from by rw [← h_self]]
  exact (restrictSubgroup_cast_eq_of_level_eq hM_eq (le_refl _) h_le_full f).symm

/-- **Decomposition (T131).** The deep restriction of `f` decomposes as the
recursive sieve witness plus the recursive sieve corrections. -/
private theorem iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
      (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
        (Gamma1 M).map (mapGL ℝ)),
      ModularForm.restrictSubgroup h_le_full f =
        iteratedSieveWitnessOnList f L hL +
          iteratedSieveCorrectionsOnList f L hL
  | [], hL, h_le_full => by
    rw [iteratedSieveWitnessOnList_nil, iteratedSieveCorrectionsOnList_nil,
      add_zero]
    exact restrictSubgroup_cast_nil_eq h_le_full f
  | p₀ :: L', hL, h_le_full => by
    rw [iteratedSieveWitnessOnList_cons, iteratedSieveCorrectionsOnList_cons]
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp) with hL'_props_def
    set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
      with hp₀_def
    set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props with hg_prev_def
    set c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveCorrectionsOnList f L' hL'_props with hc_prev_def
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    set lr : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
      with hlr_def
    -- Sum of cast witness and cast corrections collapses via `cast_add_Gamma1`.
    rw [← cast_add_Gamma1 hM_eq
      (ModularForm.restrictSubgroup h_le g_prev - lr)
      (ModularForm.restrictSubgroup h_le c_prev + lr)]
    -- Inside the cast: (R(g_prev) - lr) + (R(c_prev) + lr) = R(g_prev) + R(c_prev)
    have h_inner : (ModularForm.restrictSubgroup h_le g_prev - lr) +
        (ModularForm.restrictSubgroup h_le c_prev + lr) =
        ModularForm.restrictSubgroup h_le (g_prev + c_prev) := by
      -- restrictSubgroup is additive (rfl) and the lr's cancel.
      have h_radd : ModularForm.restrictSubgroup h_le (g_prev + c_prev) =
          ModularForm.restrictSubgroup h_le g_prev +
            ModularForm.restrictSubgroup h_le c_prev := rfl
      rw [h_radd]; abel
    rw [h_inner]
    -- IH: at the source level `M * L'.prod`, with restriction h_le_prev.
    have h_le_prev : (Gamma1 (M * L'.prod)).map (mapGL ℝ) ≤
        (Gamma1 M).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨L'.prod, rfl⟩)
    have h_ih := iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep
      f L' hL'_props h_le_prev
    rw [← h_ih, ModularForm_restrictSubgroup_restrictSubgroup]
    -- Goal: restrictSubgroup h_le_full f = hM_eq ▸ restrictSubgroup _ f.
    exact (restrictSubgroup_cast_eq_of_level_eq hM_eq
      (le_trans h_le h_le_prev) h_le_full f).symm

/-- **Restriction equals the iterated sieve corrections** (T131).  Direct
consequence of the decomposition theorem combined with vanishing of the
witness when all `Coprime _ L.prod` Fourier coefficients vanish. -/
private theorem restrictSubgroup_eq_iteratedSieveCorrectionsOnList_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ModularForm.restrictSubgroup h_le_full f =
      iteratedSieveCorrectionsOnList f L hL := by
  rw [iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep f L hL h_le_full,
    iteratedSieveWitnessOnList_eq_zero_of_coprime_prod_vanish f L hL h_vanish,
    zero_add]

/-- **Flat-hypothesis cons consumer** (T131).  Specialization of the
decomposition theorem at `(p₀ :: L')` together with vanishing of the
`Coprime _ (p₀ :: L').prod` Fourier coefficients yields an explicit
formula for the deep restriction in terms of the previous-step
corrections plus a level-raised `heckeT_p_divN` correction. -/
private theorem restrictSubgroup_eq_corrections_cons_step_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M)
    (hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M)
    [NeZero (M * L'.prod)] [NeZero p₀]
    (hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod))
    (h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ))
    (h_le_full : (Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ) ≤
        (Gamma1 M).map (mapGL ℝ))
    (hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p₀ :: L').prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    ModularForm.restrictSubgroup h_le_full f =
      hM_eq ▸ (ModularForm.restrictSubgroup h_le
          (iteratedSieveCorrectionsOnList f L' hL'_props) +
        HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ (hL p₀ List.mem_cons_self).1
            hp₀_not_coprime
            (iteratedSieveWitnessOnList f L' hL'_props))) := by
  rw [restrictSubgroup_eq_iteratedSieveCorrectionsOnList_of_coprime_prod_vanish
        f (p₀ :: L') hL h_vanish h_le_full,
      iteratedSieveCorrectionsOnList_cons f p₀ L' hL]

/-! ### T131 — List-of-pieces decomposition (oldform-span hand-off) -/

/-- **List of deep-level oldform pieces (T131).**  Each entry is a level-raised
image of `heckeT_p_divN` cast/restricted up to the deep level
`Γ₁(M · L.prod)`.  The cons step appends the new piece for `p₀` to the
list of previous-step pieces, after restricting each previous piece
along `Γ₁(p₀ · M · L'.prod) ≤ Γ₁(M · L'.prod)` and casting through the
level identity `p₀ · (M · L'.prod) = M · (p₀ :: L').prod`.

The accompanying lemma `iteratedSieveCorrectionsOnList_eq_pieces_sum`
exhibits `iteratedSieveCorrectionsOnList f L hL` as the sum of this
list, providing the structural decomposition needed by the
oldform / TraceDescent lane: each piece lies in the image of
`modularFormLevelRaise _ p k ∘ heckeT_p_divN k p _ _` (after the
deep-level restriction). -/
private noncomputable def iteratedSieveCorrectionPiecesOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k)
  | [], _ => []
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL' p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
      hL' p₀ List.mem_cons_self
    let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    let prev_pieces : List (ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k) :=
      iteratedSieveCorrectionPiecesOnList f L' hL'_props
    let lifted_prev : List (ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k) :=
      prev_pieces.map (fun x => hM_eq ▸ ModularForm.restrictSubgroup h_le x)
    let new_piece : ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k :=
      hM_eq ▸ HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    lifted_prev ++ [new_piece]

/-- **Empty-list pieces** (T131). -/
private theorem iteratedSieveCorrectionPiecesOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionPiecesOnList f [] h = [] := rfl

/-- **Cast distributes over list `.sum` for `ModularForm`** (T131 helper). -/
private theorem cast_sum_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (xs : List (ModularForm ((Gamma1 M).map (mapGL ℝ)) k)) :
    ((h ▸ xs.sum) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (xs.map (fun x => (h ▸ x : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).sum := by
  subst h; simp

/-- **Restriction commutes with list `.sum`** (T131 helper).  Restriction
is additive (definitionally), hence preserves finite sums. -/
private theorem restrictSubgroup_sum_eq
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (h_le : Γ' ≤ Γ)
    (xs : List (ModularForm Γ k)) :
    ModularForm.restrictSubgroup h_le xs.sum =
      (xs.map (ModularForm.restrictSubgroup h_le)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons]
    -- restrictSubgroup is additive (rfl) over `+`.
    show ModularForm.restrictSubgroup h_le (x + xs.sum) =
      ModularForm.restrictSubgroup h_le x + (xs.map _).sum
    have h_add : ModularForm.restrictSubgroup h_le (x + xs.sum) =
        ModularForm.restrictSubgroup h_le x +
          ModularForm.restrictSubgroup h_le xs.sum := rfl
    rw [h_add, ih]

/-- **Decomposition: corrections equals sum of pieces** (T131).  By
induction on `L`, the iterated sieve corrections equal the sum of the
list of deep-level oldform pieces. -/
private theorem iteratedSieveCorrectionsOnList_eq_pieces_sum
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      iteratedSieveCorrectionsOnList f L hL =
        (iteratedSieveCorrectionPiecesOnList f L hL).sum
  | [], hL => by
    rw [iteratedSieveCorrectionsOnList_nil, iteratedSieveCorrectionPiecesOnList_nil,
      List.sum_nil]
  | p₀ :: L', hL => by
    rw [iteratedSieveCorrectionsOnList_cons f p₀ L' hL]
    -- Unfold the pieces definition for the cons case and reduce to the IH.
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp) with hL'_props_def
    set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
      with hp₀_def
    set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    set c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveCorrectionsOnList f L' hL'_props with hc_prev_def
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    set prev_pieces :
        List (ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k) :=
      iteratedSieveCorrectionPiecesOnList f L' hL'_props with hpp_def
    set lr : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
      with hlr_def
    -- IH on L'.
    have h_ih : c_prev = prev_pieces.sum :=
      iteratedSieveCorrectionsOnList_eq_pieces_sum f L' hL'_props
    -- Unfold pieces on the RHS and compute the sum of the appended list.
    show (hM_eq ▸ (ModularForm.restrictSubgroup h_le c_prev + lr) :
        ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k) =
      (iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL).sum
    have h_pieces_unfold :
        iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL =
          (prev_pieces.map
            (fun x => (hM_eq ▸ ModularForm.restrictSubgroup h_le x :
              ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k))) ++
            [(hM_eq ▸ lr :
              ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k)] := rfl
    rw [h_pieces_unfold, List.sum_append, List.sum_singleton]
    -- Cast distributes over the binary sum.
    rw [cast_add_Gamma1 hM_eq (ModularForm.restrictSubgroup h_le c_prev) lr]
    -- For the prev-pieces summand: rewrite via IH, then push cast through sum.
    rw [h_ih, restrictSubgroup_sum_eq h_le prev_pieces,
      cast_sum_Gamma1 hM_eq
        (prev_pieces.map (ModularForm.restrictSubgroup h_le)),
      List.map_map]
    rfl

/-- **Cons unfolding for `iteratedSieveCorrectionPiecesOnList`** (T131).
The list of pieces for `p₀ :: L'` is the previous-step pieces (each
restricted to the deeper level and cast through the level identity)
followed by a single new head-of-step piece coming from
`modularFormLevelRaise … ∘ heckeT_p_divN k p₀ …` applied to the
previous-step witness.  This is the structural cons-unfolding that
shows the new piece is exactly the level-raised Hecke image of the
sieve witness on `L'`. -/
private theorem iteratedSieveCorrectionPiecesOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
    haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
      have hL'_pos : 0 < L'.prod :=
        List.prod_pos (fun p hp => (hL'_props p hp).1.pos)
      exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL =
      ((iteratedSieveCorrectionPiecesOnList f L' hL'_props).map
        (fun x => (hM_eq ▸ ModularForm.restrictSubgroup h_le x :
          ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k))) ++
        [(hM_eq ▸
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                (iteratedSieveWitnessOnList f L' hL'_props)) :
          ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k)] := by
  rfl

/-- **Head-piece extraction for `iteratedSieveCorrectionPiecesOnList`**
(T131).  The last entry of the cons-step pieces list is exactly the
deep-level cast of `modularFormLevelRaise … ∘ heckeT_p_divN k p₀ …`
applied to the previous-step witness — i.e. the new oldform piece
introduced at this sieve step.  This is the explicit witness needed
to identify each piece in the decomposition with an oldform image. -/
private theorem iteratedSieveCorrectionPiecesOnList_getLast_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp => hL p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
    haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
      have hL'_pos : 0 < L'.prod :=
        List.prod_pos (fun p hp => (hL'_props p hp).1.pos)
      exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    ∃ h_ne : iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL ≠ [],
      (iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL).getLast h_ne =
        (hM_eq ▸
          HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
              (iteratedSieveWitnessOnList f L' hL'_props)) :
        ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k) := by
  rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL]
  refine ⟨?_, ?_⟩
  · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  · rw [List.getLast_append_right (List.cons_ne_nil _ _)]
    rfl

/-- **Headline T131 decomposition (oldform-span hand-off).**  Under the
coprime-product Fourier vanishing hypothesis, the deep restriction of
`f` to level `Γ₁(M · L.prod)` decomposes as a finite sum of pieces, each
of which is a deep-level cast of a restriction of
`modularFormLevelRaise (M · L'.prod) pᵢ k (heckeT_p_divN k pᵢ _ _ _)`
applied to a previous-step witness.  This exhibits the deep restriction
as lying in the span of oldforms produced by
`modularFormLevelRaise ∘ heckeT_p_divN`. -/
private theorem restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ModularForm.restrictSubgroup h_le_full f =
      (iteratedSieveCorrectionPiecesOnList f L hL).sum := by
  rw [restrictSubgroup_eq_iteratedSieveCorrectionsOnList_of_coprime_prod_vanish
        f L hL h_vanish h_le_full,
      iteratedSieveCorrectionsOnList_eq_pieces_sum f L hL]

/-! ### T131 — Concrete oldform-image membership predicate -/

/-- **`IsOldformImageAtDeep`** (T131 oldform-span hand-off predicate).
At ambient deep level `Mfull`, a form `g : ModularForm Γ₁(Mfull) k`
is an *oldform image at depth* of `f : ModularForm Γ₁(M) k`
if there exist a prime `p`, an intermediate level `M'`, a previous
suffix `Lprev ⊆ primes-dvd-M`, and an inclusion of subgroups
`Γ₁(Mfull) ≤ Γ₁(p · M')`, such that `g` is the deep restriction of
`modularFormLevelRaise M' p k (heckeT_p_divN k p hp hpM' (witness Lprev))`.
This is the concrete witness predicate consumed by the downstream
TraceDescent / Atkin–Lehner consumer. -/
private def IsOldformImageAtDeep
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (Mfull : ℕ) [NeZero Mfull]
    (g : ModularForm ((Gamma1 Mfull).map (mapGL ℝ)) k) : Prop :=
  ∃ (p : ℕ) (Lprev : List ℕ) (hLprev : ∀ q ∈ Lprev, q.Prime ∧ q ∣ M)
    (_ : NeZero p) (_ : NeZero (M * Lprev.prod)) (hp : p.Prime)
    (hpM' : ¬ Nat.Coprime p (M * Lprev.prod))
    (h_le' : (Gamma1 Mfull).map (mapGL ℝ) ≤
      (Gamma1 (p * (M * Lprev.prod))).map (mapGL ℝ)),
    g = ModularForm.restrictSubgroup h_le'
          (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
            (HeckeRing.GL2.heckeT_p_divN k p hp hpM'
              (iteratedSieveWitnessOnList f Lprev hLprev)))

/-- **Membership theorem (T131): every piece is an oldform image at depth.**
By induction on `L`, every entry of `iteratedSieveCorrectionPiecesOnList f L hL`
satisfies `IsOldformImageAtDeep f (M * L.prod)`.  The `nil` case is vacuous,
and the `cons` case splits via `iteratedSieveCorrectionPiecesOnList_cons`
into (a) a previously-restricted IH piece, where the IH-supplied inclusion
composes with the new restriction, or (b) the freshly-introduced last piece
for `p₀` at intermediate level `M * L'.prod`. -/
private theorem iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      ∀ g ∈ iteratedSieveCorrectionPiecesOnList f L hL,
        @IsOldformImageAtDeep M _ k f (M * L.prod)
          (by
            have hL_pos : 0 < L.prod := List.prod_pos (fun p hp => (hL p hp).1.pos)
            exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩) g
  | [], _ => by
      intro g hg
      rw [iteratedSieveCorrectionPiecesOnList_nil] at hg
      simp at hg
  | p₀ :: L', hL => by
      intro g hg
      -- Ambient instance synthesis.
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp => hL p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self with hp₀_def
      haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
        have hL'_pos : 0 < L'.prod :=
          List.prod_pos (fun p hp => (hL'_props p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
      haveI hp₀_ne : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) := ⟨by
        have hL_pos : 0 < (p₀ :: L').prod :=
          List.prod_pos (fun p hp => (hL p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
      have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
          (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
        Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
      have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
        rw [List.prod_cons]; ring
      -- Split membership into mapped-IH list vs. last new piece.
      rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL,
          List.mem_append] at hg
      rcases hg with hg_mapped | hg_last
      · -- Case (a): g comes from the mapped IH list.
        rw [List.mem_map] at hg_mapped
        obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := hg_mapped
        -- Apply IH to g₀.
        have hIH :=
          iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
            f L' hL'_props g₀ hg₀_mem
        obtain ⟨p, Lprev, hLprev, hpNe, hMLprevNe, hp, hpM', h_le_inner, hg₀_form⟩
          := hIH
        refine ⟨p, Lprev, hLprev, hpNe, hMLprevNe, hp, hpM', ?_, ?_⟩
        · -- Compose inclusions: Γ₁(M*(p₀::L').prod) ≤ Γ₁(p*(M*Lprev.prod)).
          intro x hx
          refine h_le_inner (h_le ?_)
          rw [show M * (p₀ :: L').prod = p₀ * (M * L'.prod) from hM_eq.symm] at hx
          exact hx
        · -- Equality: rewrite g via hg₀_eq, then use the cast helper.
          rw [← hg₀_eq, hg₀_form, ModularForm_restrictSubgroup_restrictSubgroup]
          -- Now goal: hM_eq ▸ restrictSubgroup (h_le_inner ∘ h_le) core
          --            = restrictSubgroup composed core
          exact restrictSubgroup_cast_eq_of_level_eq hM_eq _ _ _
      · -- Case (b): g is the last new piece.
        rw [List.mem_singleton] at hg_last
        refine ⟨p₀, L', hL'_props, hp₀_ne, hM_prev_ne, hp₀_prime_M.1,
          hp₀_not_coprime, ?_, ?_⟩
        · -- The inclusion is reflexivity modulo hM_eq.
          intro x hx
          rw [show M * (p₀ :: L').prod = p₀ * (M * L'.prod) from hM_eq.symm] at hx
          exact hx
        · -- Equality up to the cast hM_eq ▸.  Use the helper after viewing
          -- `lr` as `restrictSubgroup (le_refl _) lr`.
          rw [hg_last]
          set lr : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                (iteratedSieveWitnessOnList f L' hL'_props)) with hlr_def
          have h_self : lr = ModularForm.restrictSubgroup (le_refl _) lr := rfl
          conv_lhs => rw [h_self]
          exact restrictSubgroup_cast_eq_of_level_eq hM_eq _ _ _

/-- **TraceDescent / mainLemma consumer** (T131).  Packages the corrections
decomposition into the existential shape expected by the
TraceDescent / `mainLemma_charSpace_of_TraceDescent` lane: under the
coprime-`L.prod` vanishing of period-1 Fourier coefficients, the deep
restriction of `f` is the `List.sum` of a finite list of modular forms,
each of which is an oldform image (a deep restriction of
`modularFormLevelRaise M' p k (heckeT_p_divN k p hp hpM' (witness Lprev))`
for some prime `p`, intermediate level `M' = M * Lprev.prod`, and prior
sieve witness).  Concrete witness: the list
`iteratedSieveCorrectionPiecesOnList f L hL`. -/
theorem exists_oldform_pieces_decomposition_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ∀ g ∈ pieces,
          @IsOldformImageAtDeep M _ k f (M * L.prod)
            (⟨Nat.mul_ne_zero (NeZero.ne M)
              (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩) g :=
  ⟨iteratedSieveCorrectionPiecesOnList f L hL,
    restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish
      f L hL h_vanish h_le_full,
    iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage f L hL⟩

/-! ### T131 — Nebentypus-aware decomposition for TraceDescent

The recursive sieve constructions inherit Nebentypus characters at the
deeper level via the `restrictSubgroup_mem_modFormCharSpace`,
`heckeT_p_divN_preserves_modFormCharSpace`, and
`modularFormLevelRaise_mem_modFormCharSpace` compatibility lemmas; the
character at deep level `M · L.prod` is
`χ.comp (ZMod.unitsMap (M ∣ M · L.prod))`. -/

/-- **Cast helper** (T131): membership in `modFormCharSpace` transports
through a level-cast `h : A = B` together with the corresponding pair of
divisibility witnesses by `subst`.  After `subst h` the two `unitsMap`
arguments are propositionally equal, so the two pulled-back characters
coincide. -/
private theorem cast_mem_modFormCharSpace_Gamma1
    {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ} {M : ℕ} [NeZero M]
    (χ : (ZMod M)ˣ →* ℂˣ)
    (h : A = B) (hA : M ∣ A) (hB : M ∣ B)
    {f : ModularForm ((Gamma1 A).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hA))) :
    ((h ▸ f) : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap hB)) := by
  subst h
  -- `hA` and `hB` are both `M ∣ A`, hence propositionally equal.
  have h_eq : hA = hB := rfl
  exact h_eq ▸ hf

/-- **Witness inherits Nebentypus** (T131).  By induction on `L`, the
recursive sieve witness `iteratedSieveWitnessOnList f L hL` lies in the
character space `modFormCharSpace k (χ.comp (ZMod.unitsMap (M ∣ M·L.prod)))`. -/
private theorem iteratedSieveWitnessOnList_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
      iteratedSieveWitnessOnList f L hL ∈
        modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      -- `iteratedSieveWitnessOnList f [] _ = (M = M·1) ▸ f`.
      haveI : NeZero (M * ([] : List ℕ).prod) := by simpa using (inferInstance : NeZero M)
      rw [iteratedSieveWitnessOnList_nil]
      have hM_eq : (M : ℕ) = M * ([] : List ℕ).prod := by simp
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq (dvd_refl M)
        (Nat.dvd_mul_right M ([] : List ℕ).prod)
        (by rw [ZMod.unitsMap_self, MonoidHom.comp_id]; exact hf_χ)
  | p₀ :: L', hL' => by
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp => hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL' p₀ List.mem_cons_self
      haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
        have hL'_pos : 0 < L'.prod :=
          List.prod_pos (fun p hp => (hL'_props p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) := ⟨by
        have hL_pos : 0 < (p₀ :: L').prod :=
          List.prod_pos (fun p hp => (hL' p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
      haveI hp₀M'_ne : NeZero (p₀ * (M * L'.prod)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
      have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
          (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
        Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
      have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
        rw [List.prod_cons]; ring
      have hdvd_prev : M ∣ M * L'.prod := Nat.dvd_mul_right M L'.prod
      have h_mp_dvd : (M * L'.prod) ∣ p₀ * (M * L'.prod) := ⟨p₀, by ring⟩
      have hdvd_inner : M ∣ p₀ * (M * L'.prod) := hdvd_prev.trans h_mp_dvd
      -- IH on L'.
      have hIH := iteratedSieveWitnessOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props with hg_prev_def
      -- Restrict piece lives in pulled-back character space at p₀ * (M * L'.prod).
      have h_comp_eq :
          (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_mp_dvd) =
            χ.comp (ZMod.unitsMap hdvd_inner) := by
        rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
      have h_restr : ModularForm.restrictSubgroup h_le g_prev ∈
          modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
        have := restrictSubgroup_mem_modFormCharSpace
          (χ.comp (ZMod.unitsMap hdvd_prev)) h_mp_dvd g_prev hIH
        rwa [h_comp_eq] at this
      -- Hecke + level-raise piece also lives in same character space.
      have h_ht := heckeT_p_divN_preserves_modFormCharSpace
        hp₀_prime_M.1 hp₀_not_coprime
        (χ.comp (ZMod.unitsMap hdvd_prev)) hIH
      have h_lr := modularFormLevelRaise_mem_modFormCharSpace
        (M * L'.prod) p₀ k (χ.comp (ZMod.unitsMap hdvd_prev)) h_ht
      -- `modularFormLevelRaise` lifts to `Γ₁(p₀ * (M * L'.prod))`; pull back
      -- character along `M * L'.prod ∣ p₀ * (M * L'.prod)`.
      have h_lr_inner : HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
            ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
        rwa [h_comp_eq] at h_lr
      -- Subtraction stays in submodule.
      have h_sub :
          ModularForm.restrictSubgroup h_le g_prev -
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                g_prev) ∈
            modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) :=
        Submodule.sub_mem _ h_restr h_lr_inner
      -- Unfold the cons step and transport via `cast_mem_modFormCharSpace_Gamma1`.
      rw [iteratedSieveWitnessOnList_cons]
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
        (Nat.dvd_mul_right M (p₀ :: L').prod) h_sub

/-- **Corrections inherit Nebentypus** (T131).  Mirrors the witness lemma,
with `+` instead of `-` in the cons step. -/
private theorem iteratedSieveCorrectionsOnList_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
      iteratedSieveCorrectionsOnList f L hL ∈
        modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      rw [iteratedSieveCorrectionsOnList_nil]
      exact Submodule.zero_mem _
  | p₀ :: L', hL' => by
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp => hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL' p₀ List.mem_cons_self
      haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
        have hL'_pos : 0 < L'.prod :=
          List.prod_pos (fun p hp => (hL'_props p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) := ⟨by
        have hL_pos : 0 < (p₀ :: L').prod :=
          List.prod_pos (fun p hp => (hL' p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
      haveI hp₀M'_ne : NeZero (p₀ * (M * L'.prod)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
      have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
          (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
        Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
      have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
        rw [List.prod_cons]; ring
      have hdvd_prev : M ∣ M * L'.prod := Nat.dvd_mul_right M L'.prod
      have h_mp_dvd : (M * L'.prod) ∣ p₀ * (M * L'.prod) := ⟨p₀, by ring⟩
      have hdvd_inner : M ∣ p₀ * (M * L'.prod) := hdvd_prev.trans h_mp_dvd
      -- IH on L' for both witness and corrections.
      have hIH_w := iteratedSieveWitnessOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      have hIH_c := iteratedSieveCorrectionsOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props with hg_prev_def
      set c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveCorrectionsOnList f L' hL'_props with hc_prev_def
      have h_comp_eq :
          (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_mp_dvd) =
            χ.comp (ZMod.unitsMap hdvd_inner) := by
        rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
      have h_restr : ModularForm.restrictSubgroup h_le c_prev ∈
          modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
        have := restrictSubgroup_mem_modFormCharSpace
          (χ.comp (ZMod.unitsMap hdvd_prev)) h_mp_dvd c_prev hIH_c
        rwa [h_comp_eq] at this
      have h_ht := heckeT_p_divN_preserves_modFormCharSpace
        hp₀_prime_M.1 hp₀_not_coprime
        (χ.comp (ZMod.unitsMap hdvd_prev)) hIH_w
      have h_lr := modularFormLevelRaise_mem_modFormCharSpace
        (M * L'.prod) p₀ k (χ.comp (ZMod.unitsMap hdvd_prev)) h_ht
      have h_lr_inner : HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
            ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
        rwa [h_comp_eq] at h_lr
      have h_add :
          ModularForm.restrictSubgroup h_le c_prev +
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                g_prev) ∈
            modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) :=
        Submodule.add_mem _ h_restr h_lr_inner
      rw [iteratedSieveCorrectionsOnList_cons]
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
        (Nat.dvd_mul_right M (p₀ :: L').prod) h_add

/-- **Pieces inherit Nebentypus** (T131).  Every entry of
`iteratedSieveCorrectionPiecesOnList f L hL` lies in the deep-level
character space `modFormCharSpace k (χ.comp (ZMod.unitsMap (M ∣ M·L.prod)))`. -/
private theorem iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
      ∀ g ∈ iteratedSieveCorrectionPiecesOnList f L hL,
        g ∈ modFormCharSpace k
              (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      intro g hg
      rw [iteratedSieveCorrectionPiecesOnList_nil] at hg
      simp at hg
  | p₀ :: L', hL' => by
      intro g hg
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp => hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL' p₀ List.mem_cons_self
      haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
        have hL'_pos : 0 < L'.prod :=
          List.prod_pos (fun p hp => (hL'_props p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) := ⟨by
        have hL_pos : 0 < (p₀ :: L').prod :=
          List.prod_pos (fun p hp => (hL' p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
      haveI hp₀M'_ne : NeZero (p₀ * (M * L'.prod)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
      have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
          (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
        Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
      have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
        rw [List.prod_cons]; ring
      have hdvd_prev : M ∣ M * L'.prod := Nat.dvd_mul_right M L'.prod
      have h_mp_dvd : (M * L'.prod) ∣ p₀ * (M * L'.prod) := ⟨p₀, by ring⟩
      have hdvd_inner : M ∣ p₀ * (M * L'.prod) := hdvd_prev.trans h_mp_dvd
      have h_comp_eq :
          (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_mp_dvd) =
            χ.comp (ZMod.unitsMap hdvd_inner) := by
        rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
      rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL',
          List.mem_append] at hg
      rcases hg with hg_mapped | hg_last
      · -- Mapped previous piece.
        rw [List.mem_map] at hg_mapped
        obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := hg_mapped
        have hIH := iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
          f hf_χ L' hL'_props g₀ hg₀_mem
        -- Restrict from level `M * L'.prod` to level `p₀ * (M * L'.prod)`.
        have h_restr : ModularForm.restrictSubgroup h_le g₀ ∈
            modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
          have := restrictSubgroup_mem_modFormCharSpace
            (χ.comp (ZMod.unitsMap hdvd_prev)) h_mp_dvd g₀ hIH
          rwa [h_comp_eq] at this
        rw [← hg₀_eq]
        exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
          (Nat.dvd_mul_right M (p₀ :: L').prod) h_restr
      · -- New head piece: levelRaise ∘ heckeT_p_divN of previous witness.
        rw [List.mem_singleton] at hg_last
        have hIH_w := iteratedSieveWitnessOnList_mem_modFormCharSpace
          f hf_χ L' hL'_props
        have h_ht := heckeT_p_divN_preserves_modFormCharSpace
          hp₀_prime_M.1 hp₀_not_coprime
          (χ.comp (ZMod.unitsMap hdvd_prev)) hIH_w
        have h_lr := modularFormLevelRaise_mem_modFormCharSpace
          (M * L'.prod) p₀ k (χ.comp (ZMod.unitsMap hdvd_prev)) h_ht
        have h_lr_inner : HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
              (iteratedSieveWitnessOnList f L' hL'_props))
              ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
          rwa [h_comp_eq] at h_lr
        rw [hg_last]
        exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
          (Nat.dvd_mul_right M (p₀ :: L').prod) h_lr_inner

/-- **TraceDescent / Nebentypus-aware mainLemma consumer** (T131).
Strengthening of `exists_oldform_pieces_decomposition_of_coprime_prod_vanish`
that additionally tracks Nebentypus characters: if `f` lies in
`modFormCharSpace k χ` at level `Γ₁(M)`, then under the coprime-`L.prod`
vanishing of period-1 Fourier coefficients, the deep restriction of `f`
is the `List.sum` of a list of modular forms each lying in the deep-level
character space `modFormCharSpace k (χ.comp (ZMod.unitsMap (M ∣ M·L.prod)))`
and each being an oldform image at depth.  This is the directly-consumable
shape for the TraceDescent lane operating inside a fixed character space. -/
theorem exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
      (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
    ∃ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
          @IsOldformImageAtDeep M _ k f (M * L.prod)
            (⟨Nat.mul_ne_zero (NeZero.ne M)
              (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩) g := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
  refine ⟨iteratedSieveCorrectionPiecesOnList f L hL,
    restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish
      f L hL h_vanish h_le_full, ?_, ?_⟩
  · -- The deep restriction of `f` itself lies in the pulled-back character space.
    exact restrictSubgroup_mem_modFormCharSpace χ
      (Nat.dvd_mul_right M L.prod) f hf_χ
  · intro g hg
    refine ⟨?_, ?_⟩
    · exact iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
        f hf_χ L hL g hg
    · exact iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
        f L hL g hg

/-! ### T131 — Oldform-image pieces are q-expansion supported on a prime divisor

Each piece `g` produced by `IsOldformImageAtDeep f Mfull` is, by construction,
the deep restriction of `modularFormLevelRaise M' p k _`.  Combining
`qExpansion_one_modularFormLevelRaise_coeff` (which forces the period-1 Fourier
coefficients of a level-raise image to vanish off multiples of the raising
modulus `p`) with the `rfl`-level transparency of `restrictSubgroup` on
`qExpansion (1 : ℝ)` yields the prime-divisor support property for every
`IsOldformImageAtDeep` witness.  This is the directly-consumable input for
the same-level / `qSupportedOnDvdSubmodule` lane downstream of T131. -/

private lemma IsOldformImageAtDeep.exists_prime_qExpansion_support
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (Mfull : ℕ) [NeZero Mfull]
    {g : ModularForm ((Gamma1 Mfull).map (mapGL ℝ)) k}
    (hg : IsOldformImageAtDeep f Mfull g) :
    ∃ p : ℕ, p.Prime ∧
      ∀ n : ℕ, ¬ p ∣ n → (qExpansion (1 : ℝ) ⇑g).coeff n = 0 := by
  obtain ⟨p, Lprev, _hLprev, hpNe, hMLprevNe, hp, _hpM', h_le', hg_eq⟩ := hg
  refine ⟨p, hp, ?_⟩
  intro n hn
  -- `qExpansion 1 (restrictSubgroup h g') = qExpansion 1 g'` at the coefficient
  -- level is `rfl` (same underlying function via `coe_restrictSubgroup`,
  -- cf. line 745 of this file).
  rw [hg_eq]
  show (qExpansion (1 : ℝ)
      (ModularForm.restrictSubgroup h_le'
        (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
          (HeckeRing.GL2.heckeT_p_divN k p hp _hpM'
            (iteratedSieveWitnessOnList f Lprev _hLprev))))).coeff n = 0
  have h_restrict_coeff :
      (qExpansion (1 : ℝ)
        (ModularForm.restrictSubgroup h_le'
          (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
            (HeckeRing.GL2.heckeT_p_divN k p hp _hpM'
              (iteratedSieveWitnessOnList f Lprev _hLprev))))).coeff n =
        (qExpansion (1 : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
            (HeckeRing.GL2.heckeT_p_divN k p hp _hpM'
              (iteratedSieveWitnessOnList f Lprev _hLprev)))).coeff n := rfl
  rw [h_restrict_coeff, qExpansion_one_modularFormLevelRaise_coeff, if_neg hn]

/-- **TraceDescent / mainLemma consumer with prime-support data** (T131).
Strengthening of `exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish`
that, in addition to the deep-level character-space membership and oldform-image
predicate, attaches to each piece an explicit prime `p` and a witness that the
piece's period-1 Fourier coefficients vanish off multiples of `p`.

This is the directly-consumable shape for the `qSupportedOnDvdSubmodule` lane
of the TraceDescent / `mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule_divisors`
machinery downstream: each piece is now equipped with both the character-space
data and the divisor-support data needed to feed the existing T130 / T133
consumers (modulo the `ModularForm` ↔ `CuspForm` and deep-vs-same-level
adapters).  The genuine remaining blocker for closing the composite-`N`
character-space `mainLemma` is the same-level (i.e. at level `Γ₁(M)`) trace /
projection back-down, which is the T132–T134 obligation and is **not** present
in the current decomposition (the pieces here live at the deep level
`Γ₁(M · L.prod)`). -/
theorem exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
      (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
    ∃ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
          (@IsOldformImageAtDeep M _ k f (M * L.prod)
            (⟨Nat.mul_ne_zero (NeZero.ne M)
              (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩) g) ∧
          ∃ p : ℕ, p.Prime ∧
            ∀ n : ℕ, ¬ p ∣ n →
              (qExpansion (1 : ℝ) ⇑g).coeff n = 0 := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  refine ⟨pieces, h_sum, h_restr_char, ?_⟩
  intro g hg
  obtain ⟨h_char, h_old⟩ := h_pieces g hg
  refine ⟨h_char, h_old, ?_⟩
  exact IsOldformImageAtDeep.exists_prime_qExpansion_support f (M * L.prod) h_old

/-! ### T132 — Same-level collapse of the deep oldform-image decomposition

The T131 theorem `exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish`
produces, from a coprime-`L.prod`-vanishing `f ∈ modFormCharSpace k χ` at level `Γ₁(M)`,
deep-level pieces `pieces : List (ModularForm Γ₁(M·L.prod) k)` summing to the deep
restriction of `f`, each in the pulled-back character space, each an oldform image,
and each q-supported on multiples of some prime divisor of `M`.

The genuine remaining obligation for the composite-`N` character-space `mainLemma`
is to **descend** these deep-level pieces back to `Γ₁(M)` along a bridge that
preserves both the Möbius / divisor-support structure and the character-space
membership.  No general bridge of this form exists in the current repository —
it is the T132–T134 obligation, and its concrete instantiations are
(a) a refined trace operator with cusp-stabiliser correction,
(b) an Atkin–Lehner–Li Petersson-orthogonality argument, or
(c) a `U_p`-eigenspace decomposition argument.

To produce a directly-consumable, axiom-clean handoff, we abstract the bridge as
an explicit, well-typed hypothesis `h_bridge`: given the deep pieces returned by
T131, the bridge yields a same-level family `samePiece : ℕ → ModularForm Γ₁(M) k`
indexed by the proper divisors `d ∈ M.divisors.filter (1 < ·)`, together with
the divisor q-support and character-space membership, summing to `f`.

The theorem then becomes a clean compositional plumbing of T131 into the
bridge.  Any worker who supplies the bridge — for any of the three concrete
routes above — closes the same-level collapse without further refactoring of the
upstream T131 infrastructure. -/

/-- **T132 same-level collapse of deep oldform image** (bridge form).
For `f ∈ modFormCharSpace k χ` at level `Γ₁(M)` with coprime-to-`L.prod`
Fourier vanishing (the T131 hypothesis), and an explicit bridge hypothesis
`h_bridge` that converts the deep-level pieces returned by T131 into a
same-level divisor-indexed family at `Γ₁(M)` summing to `f` with per-divisor
q-support and character-space membership, conclude the same-level divisor
decomposition.

The bridge hypothesis encapsulates the genuine remaining classical content
(refined trace / Petersson orthogonality / `U_p`-eigenspace) and is taken as
an explicit, well-typed parameter — not a black-box axiom.  The theorem
itself is a pure compositional plumbing: T131 produces deep pieces, the
bridge converts them, and the conclusion is read off.

The output shape — `∃ samePiece : ℕ → ModularForm Γ₁(M) k`, summing over
`M.divisors.filter (1 < ·)` with per-divisor q-support and char-space
membership — is exactly the data needed to construct the analogous
`TraceDescent`-style witness at the `ModularForm` level (compare
`TraceDescent` in `AtkinLehner.lean`, which is the `CuspForm` analogue). -/
theorem same_level_collapse_of_deep_oldform_image
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (h_bridge :
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
      ∀ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
        ModularForm.restrictSubgroup h_le_full f = pieces.sum →
        (∀ g ∈ pieces, ∃ p : ℕ, p.Prime ∧
          ∀ n : ℕ, ¬ p ∣ n → (qExpansion (1 : ℝ) ⇑g).coeff n = 0) →
        ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
          f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
          (∀ d ∈ M.divisors.filter (1 < ·),
            samePiece d ∈ modFormCharSpace k χ ∧
            ∀ n : ℕ, ¬ d ∣ n →
              (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0)) :
    ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        samePiece d ∈ modFormCharSpace k χ ∧
        ∀ n : ℕ, ¬ d ∣ n →
          (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, _h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  refine h_bridge pieces h_sum ?_
  intro g hg
  exact (h_pieces g hg).2.2

/-! ### T132 — Same-level divisor projections (Strategy D structure)

The bridge hypothesis of `same_level_collapse_of_deep_oldform_image` packages
the genuine remaining classical content of the same-level collapse (refined
trace / Petersson orthogonality / `U_p`-eigenspace).  To narrow that
hypothesis to a reusable, type-checked bundle, we abstract it as the
structure `ModularFormSameLevelDivisorProjections`.

A term of this structure is exactly the data required to discharge the
bridge of `same_level_collapse_of_deep_oldform_image`: given the deep-level
pieces produced by T131 (each carrying a prime q-support certificate),
return a same-level divisor-indexed family with the divisor q-support and
character-space membership.

This is **not** an axiomatisation of the bridge: providing a term of the
structure requires producing the same-level family with proofs.  The
purpose is purely organisational — to expose a single, named consumer that
discharges the bridge once a constructor is supplied (via any of the three
classical routes A/B/C). -/

/-- **`ModularFormSameLevelDivisorProjections`** (T132 / Strategy D).
A bundle of same-level divisor projections at level `Γ₁(M)` for a fixed
target form `f ∈ modFormCharSpace k χ`, a prime-list `L` of primes
dividing `M`, and the level inclusion `Γ₁(M·L.prod) ≤ Γ₁(M)`.

Given any list of deep-level pieces summing to `restrictSubgroup h_le_full f`,
each carrying a prime q-support certificate, the bundle produces a
same-level divisor-indexed family `samePiece : ℕ → ModularForm Γ₁(M) k`
satisfying the three required properties.

This structure abstracts the "same-level collapse" content of T132 as a
reusable bundle.  Concrete instances are produced by classical methods —
refined trace + cusp-stabilization, Atkin–Lehner–Li / Petersson
orthogonality, or `U_p`-eigenspace decomposition — and are consumed by
`same_level_collapse_of_deep_oldform_image_of_projections` below. -/
structure ModularFormSameLevelDivisorProjections
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (_hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) where
  /-- Same-level collapse data: from deep pieces with prime q-supports
  summing to `restrictSubgroup h_le_full f`, produce a divisor-indexed
  same-level family with the per-divisor q-support, character-space
  membership, and per-piece cusp-vanishing at every cusp of `Γ₁(M)`,
  summing to `f`. -/
  collapse :
    haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
      (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
    ∀ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum →
      (∀ g ∈ pieces, ∃ p : ℕ, p.Prime ∧
        ∀ n : ℕ, ¬ p ∣ n → (qExpansion (1 : ℝ) ⇑g).coeff n = 0) →
      ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
        f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
        (∀ d ∈ M.divisors.filter (1 < ·),
          samePiece d ∈ modFormCharSpace k χ ∧
          ∀ n : ℕ, ¬ d ∣ n →
            (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) ∧
        (∀ d ∈ M.divisors.filter (1 < ·),
          ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 M).map (mapGL ℝ)) →
            c.IsZeroAt (samePiece d).toFun k)

/-- **T132 same-level collapse, structure form** (Strategy D consumer).
Given a `ModularFormSameLevelDivisorProjections` bundle and the T131
hypotheses, produce the same-level divisor decomposition of `f`.

This is a `_bridge`-free reformulation of
`same_level_collapse_of_deep_oldform_image`: the bridge hypothesis is
supplied via the structure field `collapse`, so any caller who can
construct a `ModularFormSameLevelDivisorProjections` instance closes the
chain.  Suitable concrete constructors come from:
* a refined trace operator with cusp-stabilization,
* an Atkin–Lehner–Li / Petersson orthogonality projection, or
* a `U_p`-eigenspace decomposition. -/
theorem same_level_collapse_of_deep_oldform_image_of_projections
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (proj : ModularFormSameLevelDivisorProjections f hf_χ L hL h_le_full) :
    ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        samePiece d ∈ modFormCharSpace k χ ∧
        ∀ n : ℕ, ¬ d ∣ n →
          (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 M).map (mapGL ℝ)) →
          c.IsZeroAt (samePiece d).toFun k) := by
  -- `same_level_collapse_of_deep_oldform_image` returns the qSupp/charSpace data;
  -- the cusp-vanishing piece is provided by `proj.collapse` directly.
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp => (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, _h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  obtain ⟨samePiece, h_sum_same, h_data, h_cusp⟩ :=
    proj.collapse pieces h_sum (fun g hg => (h_pieces g hg).2.2)
  exact ⟨samePiece, h_sum_same, h_data, h_cusp⟩

/-! ### T131 — Finset-level `iteratedSieveWitness` (Miyake §4.6.5 sieve) -/

/-- **Recursive Miyake-sieve witness, Finset backbone (T131)**.  Mirrors
`iteratedSieveWitnessOnList` on `Finset ℕ` so the API matches
`miyake_4_6_5_finset_sieve_heckeT_p_divN_one`.  Implementation: delegate
to the List version on `S.toList`, casting through
`Finset.prod_toList`. -/
noncomputable def iteratedSieveWitness
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k :=
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp => (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  (show M * S.toList.prod = M * ∏ p ∈ S, p by rw [Finset.prod_toList]) ▸
    iteratedSieveWitnessOnList f S.toList
      (fun p hp => hS p (Finset.mem_toList.mp hp))

/-- **Coefficient identity for `iteratedSieveWitness`** (T131 Finset-level
coefficient theorem).  Mirrors `iteratedSieveWitnessOnList_qExpansion_coeff`
on `Finset ℕ`: the witness's period-1 Fourier coefficient is the
`S`-prime-set sieve of `f`'s coefficient.  This restates the existential
`g` of `miyake_4_6_5_finset_sieve_heckeT_p_divN_one` as the concrete
named witness `iteratedSieveWitness f S hS`. -/
theorem qExpansion_iteratedSieveWitness_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) (n : ℕ) :
    (qExpansion (1 : ℝ) (iteratedSieveWitness f S hS)).coeff n =
      (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n) := by
  unfold iteratedSieveWitness
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp => (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  rw [qExpansion_coeff_cast_Gamma1
      (show M * S.toList.prod = M * ∏ p ∈ S, p by rw [Finset.prod_toList]) _ n,
    iteratedSieveWitnessOnList_qExpansion_coeff f S.toList _ n]
  -- Translate `∃ p ∈ S.toList, p ∣ n ↔ ∃ p ∈ S, p ∣ n`.
  congr 1
  apply propext
  refine ⟨?_, ?_⟩
  · rintro ⟨p, hp_mem, hpn⟩
    exact ⟨p, Finset.mem_toList.mp hp_mem, hpn⟩
  · rintro ⟨p, hp_mem, hpn⟩
    exact ⟨p, Finset.mem_toList.mpr hp_mem, hpn⟩

/-- **Insert-step coefficient identity for `iteratedSieveWitness`**
(T131 Finset insert step).  Mirrors the cons step of
`iteratedSieveWitnessOnList`: at `insert p₀ S`, the witness's period-1
Fourier coefficient at `n` collapses to `0` when `p₀ ∣ n`, and otherwise
agrees with the witness for `S` at `n`.  Stated at the coefficient level
to avoid type-cast issues between
`Gamma1 (M * ∏ (insert p₀ S))` and `Gamma1 (p₀ * (M * ∏ S))`. -/
theorem qExpansion_iteratedSieveWitness_insert_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (p₀ : ℕ) (hp₀ : p₀ ∉ S)
    (hS : ∀ p ∈ insert p₀ S, p.Prime ∧ p ∣ M) (n : ℕ) :
    (qExpansion (1 : ℝ)
        (iteratedSieveWitness f (insert p₀ S) hS)).coeff n =
      (if p₀ ∣ n then 0
        else (qExpansion (1 : ℝ)
          (iteratedSieveWitness f S
            (fun p hp => hS p (Finset.mem_insert_of_mem hp)))).coeff n) := by
  rw [qExpansion_iteratedSieveWitness_coeff,
    qExpansion_iteratedSieveWitness_coeff]
  by_cases hn_p₀ : p₀ ∣ n
  · have h_ex : ∃ p ∈ insert p₀ S, p ∣ n :=
      ⟨p₀, Finset.mem_insert_self _ _, hn_p₀⟩
    rw [if_pos h_ex, if_pos hn_p₀]
  · rw [if_neg hn_p₀]
    by_cases hn_S : ∃ q ∈ S, q ∣ n
    · have h_ex : ∃ p ∈ insert p₀ S, p ∣ n := by
        obtain ⟨q, hqS, hqn⟩ := hn_S
        exact ⟨q, Finset.mem_insert_of_mem hqS, hqn⟩
      rw [if_pos h_ex, if_pos hn_S]
    · have h_nex : ¬ ∃ p ∈ insert p₀ S, p ∣ n := by
        rintro ⟨p, hp_mem, hpn⟩
        rcases Finset.mem_insert.mp hp_mem with rfl | hp_S
        · exact hn_p₀ hpn
        · exact hn_S ⟨p, hp_S, hpn⟩
      rw [if_neg h_nex, if_neg hn_S]

/-- **Iterated sieve Finset witness is zero under coprime-to-`∏ S` vanishing**
(T131 Finset zero theorem).  Form-level conclusion: under coprime-to-`∏ p ∈ S, p`
Fourier vanishing of `f`, the named Finset witness `iteratedSieveWitness f S hS`
equals the zero modular form.  Strategy: by `qExpansion_iteratedSieveWitness_coeff`
every coefficient of the witness's q-expansion vanishes, then apply
`qExpansion_one_Gamma1_eq_zero_iff`. -/
theorem iteratedSieveWitness_eq_zero_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    haveI hL_pos : 0 < S.toList.prod :=
      List.prod_pos (fun p hp => (hS p (Finset.mem_toList.mp hp)).1.pos)
    haveI : NeZero (M * ∏ p ∈ S, p) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (by
        rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
    iteratedSieveWitness f S hS = 0 := by
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp => (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI hML_ne : NeZero (M * ∏ p ∈ S, p) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) (by
      rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
  -- Reduce form-level zero to q-expansion-zero via injectivity.
  refine (qExpansion_one_Gamma1_eq_zero_iff
    (iteratedSieveWitness f S hS)).mp ?_
  ext n
  rw [qExpansion_iteratedSieveWitness_coeff f S hS n]
  by_cases hdiv : ∃ p ∈ S, p ∣ n
  · rw [if_pos hdiv]; simp
  · rw [if_neg hdiv]
    have hcop : Nat.Coprime n (∏ p ∈ S, p) := by
      rw [show (∏ p ∈ S, p) = S.toList.prod from (Finset.prod_toList S).symm,
        Nat.coprime_list_prod_right_iff]
      intro p hpL
      have hpS : p ∈ S := Finset.mem_toList.mp hpL
      exact ((hS p hpS).1.coprime_iff_not_dvd.mpr
        (fun hpn => hdiv ⟨p, hpS, hpn⟩)).symm
    rw [h_vanish n hcop]; simp

/-- **Iterated sieve Finset witness inherits Nebentypus** (T131 Finset
charSpace theorem).  The named Finset witness `iteratedSieveWitness f S hS`
lies in `modFormCharSpace k (χ.comp (ZMod.unitsMap (M ∣ M · ∏ S)))`.
Strategy: transport the List-level
`iteratedSieveWitnessOnList_mem_modFormCharSpace` through the level-cast
`M * S.toList.prod = M * ∏ p ∈ S, p` via `cast_mem_modFormCharSpace_Gamma1`. -/
theorem iteratedSieveWitness_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    haveI hL_pos : 0 < S.toList.prod :=
      List.prod_pos (fun p hp => (hS p (Finset.mem_toList.mp hp)).1.pos)
    haveI : NeZero (M * ∏ p ∈ S, p) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (by
        rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
    iteratedSieveWitness f S hS ∈
      modFormCharSpace k
        (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) := by
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp => (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI hML_ne_list : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  haveI hML_ne : NeZero (M * ∏ p ∈ S, p) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) (by
      rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
  -- IH on the underlying list.
  have hIH := iteratedSieveWitnessOnList_mem_modFormCharSpace
    f hf_χ S.toList (fun p hp => hS p (Finset.mem_toList.mp hp))
  -- Transport across the level cast `M * S.toList.prod = M * ∏ p ∈ S, p`.
  have hM_eq : M * S.toList.prod = M * ∏ p ∈ S, p := by rw [Finset.prod_toList]
  unfold iteratedSieveWitness
  exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq
    (Nat.dvd_mul_right M S.toList.prod)
    (Nat.dvd_mul_right M (∏ p ∈ S, p)) hIH

/-- **Named-witness restatement of `miyake_4_6_5_finset_sieve_heckeT_p_divN_one`**
(T131 downstream API).  Restates the existential coefficient identity
of `miyake_4_6_5_finset_sieve_heckeT_p_divN_one` as a clean equation on
the explicit named witness `iteratedSieveWitness f S hS`, eliminating
the existential `g` and matching the Finset-level Nebentypus and zero
APIs above.  This is just a renaming of `qExpansion_iteratedSieveWitness_coeff`
with the precise sieve formula form. -/
theorem qExpansion_iteratedSieveWitness_coeff_sieve
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ∀ n : ℕ, (qExpansion (1 : ℝ) (iteratedSieveWitness f S hS)).coeff n =
      (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n) :=
  fun n => qExpansion_iteratedSieveWitness_coeff f S hS n

/-- **Helper:** the depth product `M * ∏ p ∈ S, p` is non-zero whenever `M`
is non-zero and every element of `S` is a positive prime divisor of `M`.
Used to provide the `NeZero` instance argument of `IsOldformImageAtDeep`
in the Finset wrappers below.  Hiding the proof behind this helper
prevents `Finset.prod_pos` from leaking into goal-type proofs and
blocking later `rw`s. -/
private lemma neZero_mul_finset_prod_of_prime_dvd
    {M : ℕ} [NeZero M] {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    NeZero (M * ∏ p ∈ S, p) :=
  ⟨Nat.mul_ne_zero (NeZero.ne M)
    (Finset.prod_pos (fun p hp => (hS p hp).1.pos)).ne'⟩

/-! ### T131 — Finset wrappers for the downstream decomposition / collapse pipeline

The List-level decomposition theorems
`exists_oldform_pieces_decomposition_of_coprime_prod_vanish`,
`exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish`,
`exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish`,
and the same-level collapse consumer
`same_level_collapse_of_deep_oldform_image_of_projections`
all parameterize their depth product by `L : List ℕ` via `L.prod`.  The new
`iteratedSieveWitness` API (and its calling convention via
`miyake_4_6_5_finset_sieve_heckeT_p_divN_one`) phrases the prime set as a
`Finset ℕ` with depth product `∏ p ∈ S, p`.

The wrappers below transport each List theorem to the Finset world by taking
`L := S.toList` and rewriting `S.toList.prod = ∏ p ∈ S, p` via
`Finset.prod_toList`.  The transport is purely cast-level — no new
mathematical content is added — and is the canonical glue between the
Finset-indexed sieve API and the List-indexed downstream consumers. -/

/-- **Finset wrapper for `exists_oldform_pieces_decomposition_of_coprime_prod_vanish`**
(T131).  Mirrors the basic List-level decomposition theorem on `Finset ℕ`,
phrasing the depth product as `∏ p ∈ S, p`.  Pure delegation: take
`L := S.toList`, apply the List theorem, and transport via
`Finset.prod_toList`. -/
theorem exists_oldform_pieces_decomposition_of_coprime_prod_vanish_finset
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    [hNZ : NeZero (M * ∏ p ∈ S, p)]
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ∀ g ∈ pieces, IsOldformImageAtDeep f (M * ∏ p ∈ S, p) g := by
  -- Generalize `∏ p ∈ S, p` to a free variable `Q` everywhere in scope;
  -- then `hprod : S.toList.prod = Q` lets us `subst Q` to align the goal
  -- with the List-version conclusion.
  generalize hQ : (∏ p ∈ S, p) = Q at hNZ h_vanish h_le_full ⊢
  have hprod : S.toList.prod = Q := hQ ▸ Finset.prod_toList S
  subst hprod
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp =>
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_of_coprime_prod_vanish
    f S.toList hL h_vanish h_le_full

/-- **Finset wrapper for
`exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish`** (T131).
Mirrors the Nebentypus-aware decomposition on `Finset ℕ`. -/
theorem exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish_finset
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    [hNZ : NeZero (M * ∏ p ∈ S, p)]
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
          IsOldformImageAtDeep f (M * ∏ p ∈ S, p) g := by
  generalize hQ : (∏ p ∈ S, p) = Q at hNZ h_vanish h_le_full ⊢
  have hprod : S.toList.prod = Q := hQ ▸ Finset.prod_toList S
  subst hprod
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp =>
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
    f hf_χ S.toList hL h_vanish h_le_full

/-- **Finset wrapper for
`exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish`**
(T131).  Mirrors the strongest decomposition theorem (Nebentypus-aware,
prime-q-support tagged) on `Finset ℕ`.  This is the directly-consumable
shape for the TraceDescent / `qSupportedOnDvdSubmodule` lane when the
prime-set comes from a Finset (e.g. from
`miyake_4_6_5_finset_sieve_heckeT_p_divN_one`). -/
theorem exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish_finset
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    [hNZ : NeZero (M * ∏ p ∈ S, p)]
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
          IsOldformImageAtDeep f (M * ∏ p ∈ S, p) g ∧
          ∃ p : ℕ, p.Prime ∧
            ∀ n : ℕ, ¬ p ∣ n →
              (qExpansion (1 : ℝ) ⇑g).coeff n = 0 := by
  generalize hQ : (∏ p ∈ S, p) = Q at hNZ h_vanish h_le_full ⊢
  have hprod : S.toList.prod = Q := hQ ▸ Finset.prod_toList S
  subst hprod
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp =>
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
    f hf_χ S.toList hL h_vanish h_le_full

/-- **Finset wrapper for `same_level_collapse_of_deep_oldform_image_of_projections`**
(T132).  Mirrors the Strategy-D same-level collapse consumer on `Finset ℕ`:
given a `ModularFormSameLevelDivisorProjections` bundle phrased on
`L := S.toList` and the Finset-level coprime-vanishing hypothesis, produce
the same-level divisor decomposition of `f`. -/
theorem same_level_collapse_of_deep_oldform_image_of_projections_finset
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (proj : ModularFormSameLevelDivisorProjections f hf_χ S.toList
      (fun p hp => hS p (Finset.mem_toList.mp hp))
      ((Finset.prod_toList S).symm ▸ h_le_full)) :
    ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        samePiece d ∈ modFormCharSpace k χ ∧
        ∀ n : ℕ, ¬ d ∣ n →
          (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 M).map (mapGL ℝ)) →
          c.IsZeroAt (samePiece d).toFun k) := by
  have hprod : S.toList.prod = ∏ p ∈ S, p := Finset.prod_toList S
  set L : List ℕ := S.toList with hL_def
  have hL : ∀ p ∈ L, p.Prime ∧ p ∣ M := fun p hp =>
    hS p (Finset.mem_toList.mp hp)
  have h_vanish_L : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0 := by
    intro n hn; exact h_vanish n (hprod ▸ hn)
  have h_le_full_L : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ) := by rw [hprod]; exact h_le_full
  exact same_level_collapse_of_deep_oldform_image_of_projections
    f hf_χ L hL h_vanish_L h_le_full_L proj

end HeckeRing.GL2.MainLemma
