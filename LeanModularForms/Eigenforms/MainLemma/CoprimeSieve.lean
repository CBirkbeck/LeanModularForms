/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Coprime sieve API

Pure number-theoretic helpers for the Miyake main lemma: the coprime-sieved
`q`-expansion `sievedQExpansion`, the underlying `primeCoeffSieve` and
`finsetPrimeCoeffSieve`, their `PowerSeries` repackaging, and the Möbius
indicator identity that drives the inversion argument.

These definitions do not depend on `Gamma1`, `mapGL`, or any modular-form
structure, so they live in a self-contained module.

## Main definitions

* `sievedQExpansion N L f` — the `q`-expansion of `f` with coefficients at
  indices not coprime to `L` zeroed out.
* `primeCoeffSieve p A` — zero out `A n` whenever `p ∣ n`.
* `finsetPrimeCoeffSieve S A` — zero out `A n` when some `p ∈ S` divides `n`.
* `finsetPrimeSievedSeries S A` — `PowerSeries` repackaging of
  `finsetPrimeCoeffSieve S`.

## References

* Miyake, *Modular Forms*, Theorem 4.6.5.
-/

open scoped ModularForm

open ModularFormClass

namespace HeckeRing.GL2.MainLemma

/-- The coprime-sieved `q`-expansion: for a function `f : ℍ → ℂ` with
level-`N` `q`-expansion `Σ aₙ qⁿ` and an integer filter `L`, the formal
power series whose `n`-th coefficient is `aₙ` when `Nat.Coprime n L` and
`0` otherwise. -/
noncomputable def sievedQExpansion (N L : ℕ) (f : UpperHalfPlane → ℂ) :
    PowerSeries ℂ :=
  PowerSeries.mk fun n ↦
    if Nat.Coprime n L then (qExpansion (N : ℝ) f).coeff n else 0

@[simp] lemma sievedQExpansion_coeff_coprime
    (N L : ℕ) (f : UpperHalfPlane → ℂ) {n : ℕ} (h : Nat.Coprime n L) :
    (sievedQExpansion N L f).coeff n = (qExpansion (N : ℝ) f).coeff n := by
  simp [sievedQExpansion, PowerSeries.coeff_mk, h]

@[simp] lemma sievedQExpansion_coeff_not_coprime
    (N L : ℕ) (f : UpperHalfPlane → ℂ) {n : ℕ} (h : ¬ Nat.Coprime n L) :
    (sievedQExpansion N L f).coeff n = 0 := by
  simp [sievedQExpansion, PowerSeries.coeff_mk, h]

/-- Möbius characterisation of coprimality: for any `n, L : ℕ`, the
`ℤ`-valued indicator `[Nat.Coprime n L]` equals
`Σ d ∈ (Nat.gcd n L).divisors, μ d`. -/
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

/-- Single-prime coefficient sieve: zeros out the coefficient at every
index divisible by `p`, leaving other coefficients unchanged. -/
def primeCoeffSieve {α : Type*} [Zero α] (p : ℕ) (A : ℕ → α) (n : ℕ) : α :=
  if p ∣ n then 0 else A n

@[simp] lemma primeCoeffSieve_of_dvd {α : Type*} [Zero α] {p n : ℕ}
    (A : ℕ → α) (h : p ∣ n) : primeCoeffSieve p A n = 0 := by
  simp [primeCoeffSieve, h]

@[simp] lemma primeCoeffSieve_of_not_dvd {α : Type*} [Zero α] {p n : ℕ}
    (A : ℕ → α) (h : ¬ p ∣ n) : primeCoeffSieve p A n = A n := by
  simp [primeCoeffSieve, h]

/-- Finite-set prime coefficient sieve: returns `A n` when no element of
`S` divides `n`, and `0` otherwise.  For a Finset of primes this is the
coprime sieve with respect to `∏ p ∈ S, p`. -/
def finsetPrimeCoeffSieve {α : Type*} [Zero α] (S : Finset ℕ) (A : ℕ → α)
    (n : ℕ) : α :=
  if ∀ p ∈ S, ¬ p ∣ n then A n else 0

/-- Pointwise formula for `finsetPrimeCoeffSieve`, named for rewriting. -/
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
    finsetPrimeCoeffSieve S A n = 0 := by simp [finsetPrimeCoeffSieve, h]

/-- Insert recursion for the iterated sieve: at `insert p S`, the sieve
composes `primeCoeffSieve p` with the sieve over `S`. -/
lemma finsetPrimeCoeffSieve_insert {α : Type*} [Zero α] (p : ℕ) (S : Finset ℕ)
    (A : ℕ → α) :
    finsetPrimeCoeffSieve (insert p S) A =
      primeCoeffSieve p (finsetPrimeCoeffSieve S A) := by
  funext n
  show (if ∀ q ∈ insert p S, ¬ q ∣ n then A n else 0) =
    (if p ∣ n then 0 else if ∀ q ∈ S, ¬ q ∣ n then A n else 0)
  by_cases hdvd : p ∣ n
  · have hfail : ¬ ∀ q ∈ insert p S, ¬ q ∣ n := fun h ↦
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
    · rw [if_neg (fun h' ↦ h (hiff.mp h')), if_neg h]

/-- When every element of `S` is prime, the "no `p ∈ S` divides `n`"
condition is equivalent to `Nat.Coprime n (∏ p ∈ S, p)`. -/
theorem finsetPrimeCoeffSieve_eq_coprime {α : Type*} [Zero α] {S : Finset ℕ}
    (hS : ∀ p ∈ S, Nat.Prime p) (A : ℕ → α) (n : ℕ) :
    finsetPrimeCoeffSieve S A n =
      if Nat.Coprime n (∏ p ∈ S, p) then A n else 0 := by
  show (if ∀ p ∈ S, ¬ p ∣ n then A n else 0) =
    (if Nat.Coprime n (∏ p ∈ S, p) then A n else 0)
  have hiff : (∀ p ∈ S, ¬ p ∣ n) ↔ Nat.Coprime n (∏ p ∈ S, p) := by
    rw [Nat.coprime_prod_right_iff]
    refine ⟨fun h p hp ↦ ?_, fun h p hp ↦ ?_⟩
    · exact ((hS p hp).coprime_iff_not_dvd.mpr (h p hp)).symm
    · exact (hS p hp).coprime_iff_not_dvd.mp (h p hp).symm
  by_cases h : ∀ p ∈ S, ¬ p ∣ n
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' ↦ h (hiff.mpr h'))]

/-- `finsetPrimeCoeffSieve` packaged as a `PowerSeries` operation: the
`n`-th coefficient of the sieved series is the sieved value of the
original's `n`-th coefficient. -/
noncomputable def finsetPrimeSievedSeries {R : Type*} [Semiring R]
    (S : Finset ℕ) (A : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk
    (finsetPrimeCoeffSieve S (fun n ↦ A.coeff n))

@[simp] lemma finsetPrimeSievedSeries_coeff {R : Type*} [Semiring R]
    (S : Finset ℕ) (A : PowerSeries R) (n : ℕ) :
    (finsetPrimeSievedSeries S A).coeff n =
      finsetPrimeCoeffSieve S (fun n' ↦ A.coeff n') n := by
  simp [finsetPrimeSievedSeries]

/-- For a nonzero level filter `L`, the `n`-th coefficient of
`sievedQExpansion N L f` coincides with `finsetPrimeCoeffSieve
L.primeFactors` applied to `f`'s period-`N` q-expansion coefficients. -/
lemma sievedQExpansion_eq_finsetPrimeCoeffSieve
    (N L : ℕ) (hL : L ≠ 0) (f : UpperHalfPlane → ℂ) (n : ℕ) :
    (sievedQExpansion N L f).coeff n =
      finsetPrimeCoeffSieve L.primeFactors
        (fun n' ↦ (qExpansion (N : ℝ) f).coeff n') n := by
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

/-- Coprime-product form of the bridge: for a nonzero level filter `L`,
the `n`-th coefficient of `sievedQExpansion N L f` is `aₙ` exactly when
`Nat.Coprime n (∏ p ∈ L.primeFactors, p)`, so the sieve depends only on
the radical of `L`. -/
lemma sievedQExpansion_eq_coprime_radical
    (N L : ℕ) (hL : L ≠ 0) (f : UpperHalfPlane → ℂ) (n : ℕ) :
    (sievedQExpansion N L f).coeff n =
      if Nat.Coprime n (∏ p ∈ L.primeFactors, p) then
        (qExpansion (N : ℝ) f).coeff n
      else 0 := by
  rw [sievedQExpansion_eq_finsetPrimeCoeffSieve N L hL f n,
      finsetPrimeCoeffSieve_eq_coprime
        (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp) _ n]

end HeckeRing.GL2.MainLemma
