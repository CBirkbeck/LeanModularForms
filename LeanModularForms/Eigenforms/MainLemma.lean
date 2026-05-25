/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Miyake Theorem 4.6.5 — coprime sieving

Given `f ∈ M_k(N, χ)` with `q`-expansion `f(τ) = Σ_{n ≥ 0} a_n qₙ(τ)`,
and a positive integer `L`, the **coprime-sieved** series

  `g(τ) := Σ_{(n, L) = 1} a_n qₙ(τ)`

keeps only the coefficients at indices coprime to `L`.  Miyake
Theorem 4.6.5 asserts that `g` is itself a modular form of weight `k`
at level `N · L²` (with the same Nebentypus character `χ` suitably
transported to the higher level), via Möbius inversion over divisors
of `L`.

## References

* Miyake, *Modular Forms*, Theorem 4.6.5.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.6.
-/

open scoped ModularForm ArithmeticFunction MatrixGroups
open ModularFormClass CongruenceSubgroup Matrix.SpecialLinearGroup

namespace HeckeRing.GL2.MainLemma

private theorem ite_dvd_insert_eq_ite_exists
    {α : Type*} (p₀ n : ℕ) (S' : Finset ℕ) (a b : α) :
    (if p₀ ∣ n then a else if ∃ q ∈ S', q ∣ n then a else b) =
      if ∃ p ∈ insert p₀ S', p ∣ n then a else b := by
  simp only [Finset.exists_mem_insert]
  split <;> simp_all

private theorem ite_dvd_cons_eq_ite_exists
    {α : Type*} (p₀ n : ℕ) (L' : List ℕ) (a b : α) :
    (if p₀ ∣ n then a else if ∃ q ∈ L', q ∣ n then a else b) =
      if ∃ p ∈ p₀ :: L', p ∣ n then a else b := by
  simp only [List.exists_mem_cons_iff]
  split <;> simp_all

private theorem neZero_mul_list_prod_of_prime_dvd
    {M : ℕ} [NeZero M] {L : List ℕ} (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M) :
    NeZero (M * L.prod) :=
  ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩

/-- For `N ∣ M`, the image `(Γ₁(M)).map (mapGL ℝ)` is contained in
`(Γ₁(N)).map (mapGL ℝ)` inside `GL(2, ℝ)`. -/
theorem Gamma1_mapGL_le_of_dvd {M N : ℕ} (h : N ∣ M) :
    (Gamma1 M).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
  Subgroup.map_mono (HeckeRing.GL2.Gamma1_le_of_dvd h)

/-- Specialisation of `Gamma1_mapGL_le_of_dvd` to `N ∣ p · N`. -/
theorem Gamma1_mapGL_le_mul_left (N p : ℕ) :
    (Gamma1 (p * N)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
  Gamma1_mapGL_le_of_dvd (Dvd.intro_left p rfl)

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

/-- Miyake 4.6.5 single-prime sieve from the no-diamond hypothesis.
Given `f : M_k(Γ₁(N))` and any `g : M_k(Γ₁(N))` satisfying the
"no-diamond" condition `(qExpansion N g).coeff m = (qExpansion N f).coeff
(p · m)`, the Fourier coefficients of `f − modularFormLevelRaise N p k g`
at period `N` are exactly the `p`-coprime sieve of `f`. -/
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

/-- Indicator form of `miyake_4_6_5_prime_sieve_from_no_diamond`, with
the divisibility condition flipped to match `sievedQExpansion_coeff_*`. -/
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
  rw [miyake_4_6_5_prime_sieve_from_no_diamond f g hg_no_diamond n]; split_ifs <;> simp_all

/-- Miyake single-prime sieve with witness at level `Γ₁(p · N)`.  Variant
of `miyake_4_6_5_prime_sieve_from_no_diamond` where the witness `g` lives
at the deeper level `Γ₁(p · N)` and the q-expansion is evaluated at period
`p · N`. -/
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
  have h_le : (Gamma1 (p * N)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
    Gamma1_mapGL_le_of_dvd ⟨p, mul_comm _ _⟩
  set f_pN : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    ModularForm.restrictSubgroup h_le f
  exact miyake_4_6_5_prime_sieve_from_no_diamond f_pN g
    (fun m ↦ hg_no_diamond m) n

/-- Indicator form of `miyake_4_6_5_prime_sieve_witness_at_pN`, matching
the shape of `sievedQExpansion_coeff_*`. -/
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
  rw [miyake_4_6_5_prime_sieve_witness_at_pN f g hg_no_diamond n]; split_ifs <;> simp_all

/-- Period-1 variant of `miyake_4_6_5_prime_sieve_from_no_diamond`: under
a no-diamond hypothesis at period `1`, `f − modularFormLevelRaise N p k g`
has its period-`1` Fourier coefficient equal to `a_n` at `p ∤ n` and `0`
at `p ∣ n`. -/
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
  · simp [h, hg_no_diamond_one (n / p), Nat.mul_div_cancel' h]
  · simp [h]

/-- Period-1 variant of `miyake_4_6_5_prime_sieve_witness_at_pN`, with the
witness `g` at the deeper level `Γ₁(p · N)` and the q-expansion evaluated
at period `1`. -/
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
  have h_le : (Gamma1 (p * N)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
    Gamma1_mapGL_le_of_dvd ⟨p, mul_comm _ _⟩
  exact miyake_4_6_5_prime_sieve_from_no_diamond_one
    (ModularForm.restrictSubgroup h_le f) g hg_no_diamond_one n

/-- Period-1 same-level single-prime sieve with the concrete
`heckeT_p_divN` witness (Miyake 4.6.5 / Diamond–Shurman Prop 5.9).  For a
prime `p ∣ M` and `f ∈ M_k(Γ₁(M))`, the difference between `f` and the
level-raised image of `heckeT_p_divN k p hp hpM f` has its `n`-th period-1
Fourier coefficient equal to `a_n(f)` when `p ∤ n` and `0` when `p ∣ n`. -/
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
    (fun m ↦ HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff hp hpM f m) n

private theorem qExpansion_coeff_sieve_step
    {M : ℕ} [NeZero M] {k : ℤ} {p₀ : ℕ} [NeZero p₀]
    (hp₀_prime : p₀.Prime) (hp₀_not_coprime : ¬ Nat.Coprime p₀ M)
    (h_le : (Gamma1 (p₀ * M)).map (mapGL ℝ) ≤ (Gamma1 M).map (mapGL ℝ))
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ)
        (ModularForm.restrictSubgroup h_le g -
          HeckeRing.GL2.modularFormLevelRaise M p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g))).coeff n =
      (if p₀ ∣ n then 0 else (qExpansion (1 : ℝ) g).coeff n) := by
  haveI : NeZero (p₀ * M) := ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne M)⟩
  have h1_period : (1 : ℝ) ∈ ((Gamma1 (p₀ * M)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (p₀ * M)).map (mapGL ℝ) =
          (Gamma1 (p₀ * M) : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h_restrict_coeff :
      (qExpansion (1 : ℝ) (ModularForm.restrictSubgroup h_le g)).coeff n =
      (qExpansion (1 : ℝ) g).coeff n := rfl
  rw [qExpansion_sub one_pos h1_period, map_sub, h_restrict_coeff,
    miyake_4_6_5_prime_sieve_heckeT_p_divN_one hp₀_prime hp₀_not_coprime g n]

/-- Miyake 4.6.7: finite-prime iteration of the period-1 single-prime
`heckeT_p_divN` sieve.  Given `f ∈ M_k(Γ₁(M))` and a finite set of primes
`S` each dividing `M`, there exists a modular form `g` at level
`Γ₁(M · ∏_{p ∈ S} p)` whose period-1 Fourier coefficients are the
`S`-sieved coefficients of `f`. -/
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
      fun p hp ↦ hS p (Finset.mem_insert_of_mem hp)
    have hp₀_prime : p₀.Prime := (hS p₀ (Finset.mem_insert_self p₀ S')).1
    have hp₀_M : p₀ ∣ M := (hS p₀ (Finset.mem_insert_self p₀ S')).2
    obtain ⟨M_prev, hM_prev_ne, hM_prev_eq, g_prev, hg_prev⟩ := IH hS'
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
    have h_le : (Gamma1 (p₀ * M_prev)).map (mapGL ℝ) ≤ (Gamma1 M_prev).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
    refine ⟨p₀ * M_prev, hM_new_ne, hM_new_eq,
      ModularForm.restrictSubgroup h_le g_prev -
        HeckeRing.GL2.modularFormLevelRaise M_prev p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g_prev), ?_⟩
    intro n
    rw [ModularForm.coe_sub,
      qExpansion_coeff_sieve_step hp₀_prime hp₀_not_coprime h_le g_prev n, hg_prev n]
    exact ite_dvd_insert_eq_ite_exists p₀ n S' 0 _

theorem miyake_4_6_5_squarefree_sieve_heckeT_p_divN_one
    {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    {L : ℕ} (hL : Squarefree L) (hL_M : ∀ p ∈ L.primeFactors, p ∣ M) :
    ∃ (_ : NeZero (M * L)) (g : ModularForm ((Gamma1 (M * L)).map (mapGL ℝ)) k),
      ∀ n : ℕ, (qExpansion (1 : ℝ) g).coeff n =
        (sievedQExpansion 1 L ⇑f).coeff n := by
  have hS_prime_dvd : ∀ p ∈ L.primeFactors, p.Prime ∧ p ∣ M :=
    fun p hp ↦ ⟨Nat.prime_of_mem_primeFactors hp, hL_M p hp⟩
  have h_prod : L.primeFactors.prod id = L := by
    show ∏ p ∈ L.primeFactors, p = L
    exact Nat.prod_primeFactors_of_squarefree hL
  have hL_ne : L ≠ 0 := hL.ne_zero
  obtain ⟨M', hM'_ne, hM'_eq, g, hg⟩ :=
    miyake_4_6_5_finset_sieve_heckeT_p_divN_one f L.primeFactors hS_prime_dvd
  rw [h_prod] at hM'_eq
  subst hM'_eq
  refine ⟨hM'_ne, g, ?_⟩
  intro n
  rw [hg n, sievedQExpansion_eq_finsetPrimeCoeffSieve 1 L hL_ne ⇑f n]
  by_cases h_ex : ∃ p ∈ L.primeFactors, p ∣ n
  · rw [if_pos h_ex, finsetPrimeCoeffSieve_of_exists_dvd _ h_ex]
  · rw [if_neg h_ex]
    push_neg at h_ex
    rw [finsetPrimeCoeffSieve_of_forall_not_dvd _ h_ex, Nat.cast_one]

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

/-- The Hecke operator `heckeT_p_divN` (level-`N` no-diamond case,
`p ∣ N`) preserves every `modFormCharSpace k χ` at level
`Γ₁(N).map mapGL ℝ`. -/
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

/-- Level-raising pulls back the Nebentypus: for `f ∈ modFormCharSpace k χ`
at level `Γ₁(M)` and `d ≥ 1`, the level-raised form
`modularFormLevelRaise M d k f` at level `Γ₁(d·M)` lies in
`modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d)))`. -/
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

private theorem restrictSubgroup_mem_modFormCharSpace_comp
    {M N N' : ℕ} [NeZero M] [NeZero N] [NeZero N'] {k : ℤ}
    (χ : (ZMod M)ˣ →* ℂˣ) (hdvd_prev : M ∣ N) (h_nn' : N ∣ N') (hdvd_inner : M ∣ N')
    (h_le : (Gamma1 N').map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ))
    {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg : g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_prev))) :
    ModularForm.restrictSubgroup h_le g ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
  have h_comp_eq :
      (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_nn') =
        χ.comp (ZMod.unitsMap hdvd_inner) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  have h := restrictSubgroup_mem_modFormCharSpace
    (χ.comp (ZMod.unitsMap hdvd_prev)) h_nn' g hg
  rwa [h_comp_eq] at h

private theorem levelRaise_heckeT_mem_modFormCharSpace_comp
    {M N : ℕ} [NeZero M] [NeZero N] {k : ℤ} {p₀ : ℕ} [NeZero p₀]
    (hp₀_prime : p₀.Prime) (hp₀_not_coprime : ¬ Nat.Coprime p₀ N)
    (χ : (ZMod M)ˣ →* ℂˣ) (hdvd_prev : M ∣ N) (hdvd_inner : M ∣ p₀ * N)
    {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg : g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_prev))) :
    HeckeRing.GL2.modularFormLevelRaise N p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g) ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
  have h_mp_dvd : N ∣ p₀ * N := Nat.dvd_mul_left N p₀
  have h_comp_eq :
      (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_mp_dvd) =
        χ.comp (ZMod.unitsMap hdvd_inner) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  have h_ht := heckeT_p_divN_preserves_modFormCharSpace
    hp₀_prime hp₀_not_coprime (χ.comp (ZMod.unitsMap hdvd_prev)) hg
  have h_lr := modularFormLevelRaise_mem_modFormCharSpace
    N p₀ k (χ.comp (ZMod.unitsMap hdvd_prev)) h_ht
  rwa [h_comp_eq] at h_lr

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
      fun p hp ↦ hS p (Finset.mem_insert_of_mem hp)
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
    · exact Submodule.sub_mem _
        (restrictSubgroup_mem_modFormCharSpace_comp χ hdvd_prev h_mp_dvd hdvd_new h_le
          hg_prev_char)
        (levelRaise_heckeT_mem_modFormCharSpace_comp hp₀_prime hp₀_not_coprime χ hdvd_prev
          hdvd_new hg_prev_char)
    · intro n
      rw [ModularForm.coe_sub,
        qExpansion_coeff_sieve_step hp₀_prime hp₀_not_coprime h_le g_prev n, hg_prev n]
      exact ite_dvd_insert_eq_ite_exists p₀ n S' 0 _

/-- Miyake Main Lemma 4.6.8 (square-free case).  For a square-free sieve
modulus `L` whose distinct prime factors all divide `M`, and
`f ∈ modFormCharSpace k χ`, there is a modular form `g` at level
`Γ₁(M · L)` in the pulled-back character space whose period-1 Fourier
coefficients coincide with the `L`-coprime sieve `sievedQExpansion 1 L ⇑f`. -/
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
    fun p hp ↦ ⟨Nat.prime_of_mem_primeFactors hp, hL_M p hp⟩
  have h_prod : L.primeFactors.prod id = L := by
    show ∏ p ∈ L.primeFactors, p = L
    exact Nat.prod_primeFactors_of_squarefree hL
  have hL_ne : L ≠ 0 := hL.ne_zero
  obtain ⟨M', hM'_ne, hM'_eq, hdvd', g, hg_char, hg⟩ :=
    miyake_main_lemma_4_6_8_finset χ f hf L.primeFactors hS_prime_dvd
  rw [h_prod] at hM'_eq
  subst hM'_eq
  refine ⟨hM'_ne, g, ?_, ?_⟩
  · exact hg_char
  · intro n
    rw [hg n, sievedQExpansion_eq_finsetPrimeCoeffSieve 1 L hL_ne ⇑f n]
    by_cases h_ex : ∃ p ∈ L.primeFactors, p ∣ n
    · rw [if_pos h_ex, finsetPrimeCoeffSieve_of_exists_dvd _ h_ex]
    · rw [if_neg h_ex]
      push_neg at h_ex
      rw [finsetPrimeCoeffSieve_of_forall_not_dvd _ h_ex, Nat.cast_one]

/-- Miyake Main Lemma 4.6.8 for general `L ≠ 0`, obtained from the
square-free case by replacing `L` with its radical
`∏ p ∈ L.primeFactors, p`.  The result lives at the minimal level
`Γ₁(M · L.primeFactors.prod id)`. -/
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
  have hL_rad_pf : (L.primeFactors.prod id).primeFactors = L.primeFactors := by
    show (∏ p ∈ L.primeFactors, p).primeFactors = L.primeFactors
    exact Nat.primeFactors_prod (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp)
  have hL_rad_M : ∀ p ∈ (L.primeFactors.prod id).primeFactors, p ∣ M := by
    rw [hL_rad_pf]; exact hL_M
  obtain ⟨hne, g, hg_char, hg_coeff⟩ :=
    miyake_main_lemma_4_6_8_squarefree χ f hf hL_rad_sf hL_rad_M
  refine ⟨hne, g, hg_char, ?_⟩
  intro n
  rw [hg_coeff n, sievedQExpansion_eq_coprime_radical 1 L hL_ne ⇑f n]
  show (sievedQExpansion 1 (L.primeFactors.prod id) ⇑f).coeff n =
    if Nat.Coprime n (L.primeFactors.prod id) then
      (qExpansion ((1 : ℕ) : ℝ) ⇑f).coeff n else 0
  by_cases h : Nat.Coprime n (L.primeFactors.prod id)
  · rw [sievedQExpansion_coeff_coprime _ _ _ h, if_pos h]
  · rw [sievedQExpansion_coeff_not_coprime _ _ _ h, if_neg h]

/-- Miyake Main Lemma 4.6.8 at the caller-facing level `Γ₁(M · L)`,
obtained from `miyake_main_lemma_4_6_8_radical` by restricting along the
inclusion `Γ₁(M · L) ⊆ Γ₁(M · L.primeFactors.prod id)`. -/
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
  obtain ⟨_, g0, hg0_char, hg0_coeff⟩ :=
    miyake_main_lemma_4_6_8_radical χ f hf hL_ne hL_M
  have hL_rad_dvd_L : L.primeFactors.prod id ∣ L := by
    show ∏ p ∈ L.primeFactors, p ∣ L
    exact Nat.prod_primeFactors_dvd L
  have hM_dvd : M * L.primeFactors.prod id ∣ M * L :=
    Nat.mul_dvd_mul_left M hL_rad_dvd_L
  have h_restrict := restrictSubgroup_mem_modFormCharSpace
    (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (L.primeFactors.prod id))))
    hM_dvd g0 hg0_char
  refine ⟨inferInstance,
    ModularForm.restrictSubgroup
      (Gamma1_mapGL_le_of_dvd (hM_dvd)) g0, ?_, ?_⟩
  · have h_comp_eq :
        (χ.comp (ZMod.unitsMap
            (Nat.dvd_mul_right M (L.primeFactors.prod id)))).comp
          (ZMod.unitsMap hM_dvd) =
        χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L)) := by
      rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
    exact h_comp_eq ▸ h_restrict
  · intro n
    exact hg0_coeff n

/-- Under the coprime-to-`L` Fourier vanishing hypothesis on `f`, the
level-`Γ₁(M·L)` Miyake witness `g` produced by
`miyake_main_lemma_4_6_8_level_L` has identically zero period-1
`q`-expansion. -/
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
  · simp [sievedQExpansion_coeff_coprime _ _ _ h, h_vanish n h, Nat.cast_one]
  · simp [sievedQExpansion_coeff_not_coprime _ _ _ h]

private theorem qExpansion_one_Gamma1_eq_zero_iff
    {N : ℕ} [NeZero N] {k : ℤ}
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion (1 : ℝ) g = 0 ↔ g = 0 := by
  apply qExpansion_eq_zero_iff one_pos
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    CongruenceSubgroup.strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

/-- When `f` satisfies coprime-to-`L` Fourier vanishing, the
level-`Γ₁(M·L)` Miyake witness `g` is the zero modular form. -/
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

private noncomputable def iteratedSieveWitnessOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k
  | [], _ =>
    (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
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

private theorem iteratedSieveWitnessOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveWitnessOnList f [] h =
      (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f :=
  rfl

private theorem iteratedSieveWitnessOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL' : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    iteratedSieveWitnessOnList f (p₀ :: L') hL' =
      (let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
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

private theorem qExpansion_coeff_cast_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ)
        ((h ▸ g) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n =
      (qExpansion (1 : ℝ) g).coeff n := by
  subst h
  rfl

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
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
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
    rw [qExpansion_coeff_cast_Gamma1 hM_eq _ n, ModularForm.coe_sub,
      qExpansion_coeff_sieve_step hp₀_prime_M.1 hp₀_not_coprime h_le g_prev n,
      iteratedSieveWitnessOnList_qExpansion_coeff f L' hL'_props n]
    exact ite_dvd_cons_eq_ite_exists p₀ n L' 0 _

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
        (fun hpn ↦ hdiv ⟨p, hpL, hpn⟩)).symm
    rw [h_vanish n hcop]; simp

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

private theorem cast_eq_zero_iff_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ((h ▸ g) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 ↔ g = 0 := by
  subst h
  rfl

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
          (fun p hp ↦ hL p (List.mem_cons_of_mem _ hp))) =
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ (hL p₀ List.mem_cons_self).1
          hp₀_not_coprime
          (iteratedSieveWitnessOnList f L'
            (fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)))) := by
  rw [iteratedSieveWitnessOnList_cons] at h_zero
  have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
    rw [List.prod_cons]; ring
  haveI : NeZero (p₀ * (M * L'.prod)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
  rw [cast_eq_zero_iff_Gamma1 hM_eq _] at h_zero
  exact sub_eq_zero.mp h_zero

private noncomputable def iteratedSieveCorrectionsOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k
  | [], _ => 0
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
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

private theorem iteratedSieveCorrectionsOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionsOnList f [] h = 0 := rfl

private theorem iteratedSieveCorrectionsOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL' : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionsOnList f (p₀ :: L') hL' =
      (let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
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

private theorem ModularForm_restrictSubgroup_restrictSubgroup
    {Γ Γ' Γ'' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (h₁ : Γ' ≤ Γ) (h₂ : Γ'' ≤ Γ')
    (f : ModularForm Γ k) :
    ModularForm.restrictSubgroup h₂ (ModularForm.restrictSubgroup h₁ f) =
      ModularForm.restrictSubgroup (le_trans h₂ h₁) f := rfl

private theorem cast_add_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (x y : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ((h ▸ (x + y)) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (h ▸ x) + (h ▸ y) := by
  subst h; rfl

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

private theorem restrictSubgroup_cast_nil_eq
    {M : ℕ} [NeZero M] {k : ℤ}
    (h_le_full : (Gamma1 (M * ([] : List ℕ).prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ModularForm.restrictSubgroup h_le_full f =
      ((show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f) := by
  have hM_eq : M = M * ([] : List ℕ).prod := by simp
  have h_self : f = ModularForm.restrictSubgroup (le_refl _) f := rfl
  rw [show ((hM_eq ▸ f) : ModularForm ((Gamma1 (M * ([] : List ℕ).prod)).map
    (mapGL ℝ)) k) =
      hM_eq ▸ ModularForm.restrictSubgroup (le_refl
        ((Gamma1 M).map (mapGL ℝ))) f from by rw [← h_self]]
  exact (restrictSubgroup_cast_eq_of_level_eq hM_eq (le_refl _) h_le_full f).symm

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
      fun p hp ↦ hL p (List.mem_cons_of_mem _ hp) with hL'_props_def
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
    rw [← cast_add_Gamma1 hM_eq
      (ModularForm.restrictSubgroup h_le g_prev - lr)
      (ModularForm.restrictSubgroup h_le c_prev + lr)]
    have h_inner : (ModularForm.restrictSubgroup h_le g_prev - lr) +
        (ModularForm.restrictSubgroup h_le c_prev + lr) =
        ModularForm.restrictSubgroup h_le (g_prev + c_prev) := by
      have h_radd : ModularForm.restrictSubgroup h_le (g_prev + c_prev) =
          ModularForm.restrictSubgroup h_le g_prev +
            ModularForm.restrictSubgroup h_le c_prev := rfl
      rw [h_radd]; abel
    rw [h_inner]
    have h_le_prev : (Gamma1 (M * L'.prod)).map (mapGL ℝ) ≤
        (Gamma1 M).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd (⟨L'.prod, rfl⟩)
    have h_ih := iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep
      f L' hL'_props h_le_prev
    rw [← h_ih, ModularForm_restrictSubgroup_restrictSubgroup]
    exact (restrictSubgroup_cast_eq_of_level_eq hM_eq
      (le_trans h_le h_le_prev) h_le_full f).symm

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

private noncomputable def iteratedSieveCorrectionPiecesOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k)
  | [], _ => []
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
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
      prev_pieces.map (fun x ↦ hM_eq ▸ ModularForm.restrictSubgroup h_le x)
    let new_piece : ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k :=
      hM_eq ▸ HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    lifted_prev ++ [new_piece]

private theorem iteratedSieveCorrectionPiecesOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionPiecesOnList f [] h = [] := rfl

private theorem cast_sum_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (xs : List (ModularForm ((Gamma1 M).map (mapGL ℝ)) k)) :
    ((h ▸ xs.sum) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (xs.map (fun x ↦ (h ▸ x : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).sum := by
  subst h; simp

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
    show ModularForm.restrictSubgroup h_le (x + xs.sum) =
      ModularForm.restrictSubgroup h_le x + (xs.map _).sum
    have h_add : ModularForm.restrictSubgroup h_le (x + xs.sum) =
        ModularForm.restrictSubgroup h_le x +
          ModularForm.restrictSubgroup h_le xs.sum := rfl
    rw [h_add, ih]

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
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL p (List.mem_cons_of_mem _ hp) with hL'_props_def
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
    have h_ih : c_prev = prev_pieces.sum :=
      iteratedSieveCorrectionsOnList_eq_pieces_sum f L' hL'_props
    show (hM_eq ▸ (ModularForm.restrictSubgroup h_le c_prev + lr) :
        ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k) =
      (iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL).sum
    have h_pieces_unfold :
        iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL =
          (prev_pieces.map
            (fun x ↦ (hM_eq ▸ ModularForm.restrictSubgroup h_le x :
              ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k))) ++
            [(hM_eq ▸ lr :
              ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k)] := rfl
    rw [h_pieces_unfold, List.sum_append, List.sum_singleton]
    rw [cast_add_Gamma1 hM_eq (ModularForm.restrictSubgroup h_le c_prev) lr]
    rw [h_ih, restrictSubgroup_sum_eq h_le prev_pieces,
      cast_sum_Gamma1 hM_eq
        (prev_pieces.map (ModularForm.restrictSubgroup h_le)),
      List.map_map]
    rfl

private theorem iteratedSieveCorrectionPiecesOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
    haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
      have hL'_pos : 0 < L'.prod :=
        List.prod_pos (fun p hp ↦ (hL'_props p hp).1.pos)
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
        (fun x ↦ (hM_eq ▸ ModularForm.restrictSubgroup h_le x :
          ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k))) ++
        [(hM_eq ▸
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                (iteratedSieveWitnessOnList f L' hL'_props)) :
          ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k)] := by
  rfl

private theorem iteratedSieveCorrectionPiecesOnList_getLast_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
    haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
      have hL'_pos : 0 < L'.prod :=
        List.prod_pos (fun p hp ↦ (hL'_props p hp).1.pos)
      exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have _h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
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

private theorem head_piece_isOldformImageAtDeep
    {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) [NeZero p₀] (L' : List ℕ) (hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M)
    [NeZero (M * L'.prod)] (hp₀_prime : p₀.Prime)
    (hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod))
    (hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod)
    [NeZero (M * (p₀ :: L').prod)]
    {g : ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k}
    (hg : g = hM_eq ▸ HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime
          (iteratedSieveWitnessOnList f L' hL'_props))) :
    IsOldformImageAtDeep f (M * (p₀ :: L').prod) g := by
  refine ⟨p₀, L', hL'_props, ‹_›, ‹_›, hp₀_prime, hp₀_not_coprime, ?_, ?_⟩
  · intro x hx
    rwa [show M * (p₀ :: L').prod = p₀ * (M * L'.prod) from hM_eq.symm] at hx
  · rw [hg]
    set lr : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime
          (iteratedSieveWitnessOnList f L' hL'_props))
    conv_lhs => rw [show lr = ModularForm.restrictSubgroup (le_refl _) lr from rfl]
    exact restrictSubgroup_cast_eq_of_level_eq hM_eq _ _ _

private theorem mapped_piece_isOldformImageAtDeep
    {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    [NeZero (M * L'.prod)] [NeZero (M * (p₀ :: L').prod)]
    (h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
      (Gamma1 (M * L'.prod)).map (mapGL ℝ))
    (hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod)
    {g₀ : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k}
    (hg₀ : IsOldformImageAtDeep f (M * L'.prod) g₀)
    {g : ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k}
    (hg : hM_eq ▸ ModularForm.restrictSubgroup h_le g₀ = g) :
    IsOldformImageAtDeep f (M * (p₀ :: L').prod) g := by
  obtain ⟨p, Lprev, hLprev, hpNe, hMLprevNe, hp, hpM', h_le_inner, hg₀_form⟩ := hg₀
  refine ⟨p, Lprev, hLprev, hpNe, hMLprevNe, hp, hpM', ?_, ?_⟩
  · intro x hx
    refine h_le_inner (h_le ?_)
    rwa [show M * (p₀ :: L').prod = p₀ * (M * L'.prod) from hM_eq.symm] at hx
  · rw [← hg, hg₀_form, ModularForm_restrictSubgroup_restrictSubgroup]
    exact restrictSubgroup_cast_eq_of_level_eq hM_eq _ _ _

private theorem iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      ∀ g ∈ iteratedSieveCorrectionPiecesOnList f L hL,
        @IsOldformImageAtDeep M _ k f (M * L.prod)
          (by
            have hL_pos : 0 < L.prod := List.prod_pos (fun p hp ↦ (hL p hp).1.pos)
            exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩) g
  | [], _ => by
      intro g hg
      rw [iteratedSieveCorrectionPiecesOnList_nil] at hg
      simp at hg
  | p₀ :: L', hL => by
      intro g hg
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp ↦ hL p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self with hp₀_def
      haveI hM_prev_ne : NeZero (M * L'.prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'_props
      haveI hp₀_ne : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) :=
        neZero_mul_list_prod_of_prime_dvd hL
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        Nat.Prime.not_coprime_iff_dvd.mpr
          ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
      have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
          (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
        Gamma1_mapGL_le_of_dvd (⟨p₀, by ring⟩)
      have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
        rw [List.prod_cons]; ring
      rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL,
          List.mem_append] at hg
      rcases hg with hg_mapped | hg_last
      · rw [List.mem_map] at hg_mapped
        obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := hg_mapped
        exact mapped_piece_isOldformImageAtDeep f p₀ L' h_le hM_eq
          (iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
            f L' hL'_props g₀ hg₀_mem) hg₀_eq
      · rw [List.mem_singleton] at hg_last
        exact head_piece_isOldformImageAtDeep f p₀ L' hL'_props hp₀_prime_M.1
          hp₀_not_coprime hM_eq hg_last

/-- Under the coprime-`L.prod` vanishing of period-1 Fourier coefficients,
the deep restriction of `f` is the `List.sum` of a finite list of modular
forms, each an oldform image at depth. -/
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
              (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩) g :=
  ⟨iteratedSieveCorrectionPiecesOnList f L hL,
    restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish
      f L hL h_vanish h_le_full,
    iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage f L hL⟩

private theorem cast_mem_modFormCharSpace_Gamma1
    {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ} {M : ℕ} [NeZero M]
    (χ : (ZMod M)ˣ →* ℂˣ)
    (h : A = B) (hA : M ∣ A) (hB : M ∣ B)
    {f : ModularForm ((Gamma1 A).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hA))) :
    ((h ▸ f) : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap hB)) := by
  subst h; exact (show hA = hB from rfl) ▸ hf

private theorem iteratedSieveWitnessOnList_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
      iteratedSieveWitnessOnList f L hL ∈
        modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      haveI : NeZero (M * ([] : List ℕ).prod) := by simpa using (inferInstance : NeZero M)
      rw [iteratedSieveWitnessOnList_nil]
      have hM_eq : (M : ℕ) = M * ([] : List ℕ).prod := by simp
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq (dvd_refl M)
        (Nat.dvd_mul_right M ([] : List ℕ).prod)
        (by rw [ZMod.unitsMap_self, MonoidHom.comp_id]; exact hf_χ)
  | p₀ :: L', hL' => by
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL' p₀ List.mem_cons_self
      haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
        have hL'_pos : 0 < L'.prod :=
          List.prod_pos (fun p hp ↦ (hL'_props p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) := ⟨by
        have hL_pos : 0 < (p₀ :: L').prod :=
          List.prod_pos (fun p hp ↦ (hL' p hp).1.pos)
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
      have hIH := iteratedSieveWitnessOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props with hg_prev_def
      have h_sub :
          ModularForm.restrictSubgroup h_le g_prev -
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                g_prev) ∈
            modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) :=
        Submodule.sub_mem _
          (restrictSubgroup_mem_modFormCharSpace_comp χ hdvd_prev h_mp_dvd hdvd_inner h_le hIH)
          (levelRaise_heckeT_mem_modFormCharSpace_comp hp₀_prime_M.1 hp₀_not_coprime χ
            hdvd_prev hdvd_inner hIH)
      rw [iteratedSieveWitnessOnList_cons]
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
        (Nat.dvd_mul_right M (p₀ :: L').prod) h_sub

private theorem iteratedSieveCorrectionsOnList_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
      iteratedSieveCorrectionsOnList f L hL ∈
        modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      rw [iteratedSieveCorrectionsOnList_nil]
      exact Submodule.zero_mem _
  | p₀ :: L', hL' => by
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL' p₀ List.mem_cons_self
      haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
        have hL'_pos : 0 < L'.prod :=
          List.prod_pos (fun p hp ↦ (hL'_props p hp).1.pos)
        exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) := ⟨by
        have hL_pos : 0 < (p₀ :: L').prod :=
          List.prod_pos (fun p hp ↦ (hL' p hp).1.pos)
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
      have hIH_w := iteratedSieveWitnessOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      have hIH_c := iteratedSieveCorrectionsOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props with hg_prev_def
      set c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveCorrectionsOnList f L' hL'_props with hc_prev_def
      have h_add :
          ModularForm.restrictSubgroup h_le c_prev +
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                g_prev) ∈
            modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) :=
        Submodule.add_mem _
          (restrictSubgroup_mem_modFormCharSpace_comp χ hdvd_prev h_mp_dvd hdvd_inner h_le hIH_c)
          (levelRaise_heckeT_mem_modFormCharSpace_comp hp₀_prime_M.1 hp₀_not_coprime χ
            hdvd_prev hdvd_inner hIH_w)
      rw [iteratedSieveCorrectionsOnList_cons]
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
        (Nat.dvd_mul_right M (p₀ :: L').prod) h_add

private theorem iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
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
        fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp) with hL'_props_def
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL' p₀ List.mem_cons_self
      haveI hM_prev_ne : NeZero (M * L'.prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'_props
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'
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
      rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL',
          List.mem_append] at hg
      rcases hg with hg_mapped | hg_last
      · rw [List.mem_map] at hg_mapped
        obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := hg_mapped
        have hIH := iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
          f hf_χ L' hL'_props g₀ hg₀_mem
        rw [← hg₀_eq]
        exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
          (Nat.dvd_mul_right M (p₀ :: L').prod)
          (restrictSubgroup_mem_modFormCharSpace_comp χ hdvd_prev h_mp_dvd hdvd_inner h_le hIH)
      · rw [List.mem_singleton] at hg_last
        have hIH_w := iteratedSieveWitnessOnList_mem_modFormCharSpace
          f hf_χ L' hL'_props
        rw [hg_last]
        exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
          (Nat.dvd_mul_right M (p₀ :: L').prod)
          (levelRaise_heckeT_mem_modFormCharSpace_comp hp₀_prime_M.1 hp₀_not_coprime χ
            hdvd_prev hdvd_inner hIH_w)

/-- Nebentypus-aware strengthening of
`exists_oldform_pieces_decomposition_of_coprime_prod_vanish`: the deep
restriction of `f` is the `List.sum` of modular forms each lying in the
deep-level character space and each an oldform image at depth. -/
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
      (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
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
              (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩) g := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  refine ⟨iteratedSieveCorrectionPiecesOnList f L hL,
    restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish
      f L hL h_vanish h_le_full, ?_, ?_⟩
  · exact restrictSubgroup_mem_modFormCharSpace χ
      (Nat.dvd_mul_right M L.prod) f hf_χ
  · intro g hg
    refine ⟨?_, ?_⟩
    · exact iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
        f hf_χ L hL g hg
    · exact iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
        f L hL g hg

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
  rw [hg_eq]
  show (qExpansion (1 : ℝ)
      (ModularForm.restrictSubgroup h_le'
        (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
          (HeckeRing.GL2.heckeT_p_divN k p hp _hpM'
            (iteratedSieveWitnessOnList f Lprev _hLprev))))).coeff n = 0
  change (qExpansion (1 : ℝ)
      (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
        (HeckeRing.GL2.heckeT_p_divN k p hp _hpM'
          (iteratedSieveWitnessOnList f Lprev _hLprev)))).coeff n = 0
  rw [qExpansion_one_modularFormLevelRaise_coeff, if_neg hn]

/-- Strengthening of
`exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish` that
additionally attaches to each piece an explicit prime `p` and a witness
that the piece's period-1 Fourier coefficients vanish off multiples of `p`. -/
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
      (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
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
              (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩) g) ∧
          ∃ p : ℕ, p.Prime ∧
            ∀ n : ℕ, ¬ p ∣ n →
              (qExpansion (1 : ℝ) ⇑g).coeff n = 0 := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  refine ⟨pieces, h_sum, h_restr_char, ?_⟩
  intro g hg
  obtain ⟨h_char, h_old⟩ := h_pieces g hg
  refine ⟨h_char, h_old, ?_⟩
  exact IsOldformImageAtDeep.exists_prime_qExpansion_support f (M * L.prod) h_old

/-- Same-level collapse of deep oldform image (bridge form).  Given the
coprime-to-`L.prod` Fourier vanishing hypothesis and an explicit bridge
hypothesis `h_bridge` converting the deep-level pieces into a same-level
divisor-indexed family at `Γ₁(M)` summing to `f`, conclude the same-level
divisor decomposition. -/
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
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
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
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, _h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  refine h_bridge pieces h_sum ?_
  intro g hg
  exact (h_pieces g hg).2.2

/-- A bundle of same-level divisor projections at level `Γ₁(M)` for a fixed
target form `f`, a prime-list `L` of primes dividing `M`, and the level
inclusion `Γ₁(M·L.prod) ≤ Γ₁(M)`.  Given deep-level pieces summing to
`restrictSubgroup h_le_full f` with prime q-support certificates, it
produces a same-level divisor-indexed family `samePiece : ℕ → ModularForm
Γ₁(M) k`. -/
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
      (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
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

/-- Same-level collapse in structure form: given a
`ModularFormSameLevelDivisorProjections` bundle and the coprime-vanishing
hypothesis, produce the same-level divisor decomposition of `f`.  A
`_bridge`-free reformulation of `same_level_collapse_of_deep_oldform_image`. -/
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
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, _h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  obtain ⟨samePiece, h_sum_same, h_data, h_cusp⟩ :=
    proj.collapse pieces h_sum (fun g hg ↦ (h_pieces g hg).2.2)
  exact ⟨samePiece, h_sum_same, h_data, h_cusp⟩

/-- Recursive Miyake-sieve witness on `Finset ℕ`, the Finset analogue of
`iteratedSieveWitnessOnList` (delegating to it on `S.toList`). -/
noncomputable def iteratedSieveWitness
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k :=
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  (show M * S.toList.prod = M * ∏ p ∈ S, p by rw [Finset.prod_toList]) ▸
    iteratedSieveWitnessOnList f S.toList
      (fun p hp ↦ hS p (Finset.mem_toList.mp hp))

/-- Coefficient identity for `iteratedSieveWitness`: its period-1 Fourier
coefficient is the `S`-prime-set sieve of `f`'s coefficient. -/
theorem qExpansion_iteratedSieveWitness_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) (n : ℕ) :
    (qExpansion (1 : ℝ) (iteratedSieveWitness f S hS)).coeff n =
      (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n) := by
  unfold iteratedSieveWitness
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  rw [qExpansion_coeff_cast_Gamma1
      (show M * S.toList.prod = M * ∏ p ∈ S, p by rw [Finset.prod_toList]) _ n,
    iteratedSieveWitnessOnList_qExpansion_coeff f S.toList _ n]
  simp [Finset.mem_toList]

/-- Insert-step coefficient identity for `iteratedSieveWitness`: at
`insert p₀ S`, the period-1 Fourier coefficient at `n` collapses to `0`
when `p₀ ∣ n`, and otherwise agrees with the witness for `S` at `n`. -/
theorem qExpansion_iteratedSieveWitness_insert_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (p₀ : ℕ) (_hp₀ : p₀ ∉ S)
    (hS : ∀ p ∈ insert p₀ S, p.Prime ∧ p ∣ M) (n : ℕ) :
    (qExpansion (1 : ℝ)
        (iteratedSieveWitness f (insert p₀ S) hS)).coeff n =
      (if p₀ ∣ n then 0
        else (qExpansion (1 : ℝ)
          (iteratedSieveWitness f S
            (fun p hp ↦ hS p (Finset.mem_insert_of_mem hp)))).coeff n) := by
  rw [qExpansion_iteratedSieveWitness_coeff, qExpansion_iteratedSieveWitness_coeff]
  split_ifs with hn_p₀ h_ex hn_S h_nex <;> simp_all [Finset.mem_insert]

/-- Under coprime-to-`∏ p ∈ S, p` Fourier vanishing of `f`, the named
Finset witness `iteratedSieveWitness f S hS` equals the zero modular form. -/
theorem iteratedSieveWitness_eq_zero_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    haveI hL_pos : 0 < S.toList.prod :=
      List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
    haveI : NeZero (M * ∏ p ∈ S, p) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (by
        rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
    iteratedSieveWitness f S hS = 0 := by
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI hML_ne : NeZero (M * ∏ p ∈ S, p) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) (by
      rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
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
        (fun hpn ↦ hdiv ⟨p, hpS, hpn⟩)).symm
    rw [h_vanish n hcop]; simp

/-- The named Finset witness `iteratedSieveWitness f S hS` lies in
`modFormCharSpace k (χ.comp (ZMod.unitsMap (M ∣ M · ∏ S)))`. -/
theorem iteratedSieveWitness_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    haveI hL_pos : 0 < S.toList.prod :=
      List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
    haveI : NeZero (M * ∏ p ∈ S, p) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (by
        rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
    iteratedSieveWitness f S hS ∈
      modFormCharSpace k
        (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) := by
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI hML_ne_list : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  haveI hML_ne : NeZero (M * ∏ p ∈ S, p) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) (by
      rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
  have hIH := iteratedSieveWitnessOnList_mem_modFormCharSpace
    f hf_χ S.toList (fun p hp ↦ hS p (Finset.mem_toList.mp hp))
  have hM_eq : M * S.toList.prod = M * ∏ p ∈ S, p := by rw [Finset.prod_toList]
  unfold iteratedSieveWitness
  exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq
    (Nat.dvd_mul_right M S.toList.prod)
    (Nat.dvd_mul_right M (∏ p ∈ S, p)) hIH

/-- Named-witness restatement of the coefficient identity of
`miyake_4_6_5_finset_sieve_heckeT_p_divN_one` on the explicit witness
`iteratedSieveWitness f S hS`, eliminating the existential `g`. -/
theorem qExpansion_iteratedSieveWitness_coeff_sieve
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ∀ n : ℕ, (qExpansion (1 : ℝ) (iteratedSieveWitness f S hS)).coeff n =
      (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n) :=
  fun n ↦ qExpansion_iteratedSieveWitness_coeff f S hS n

private lemma neZero_mul_finset_prod_of_prime_dvd
    {M : ℕ} [NeZero M] {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    NeZero (M * ∏ p ∈ S, p) :=
  ⟨Nat.mul_ne_zero (NeZero.ne M)
    (Finset.prod_pos (fun p hp ↦ (hS p hp).1.pos)).ne'⟩

/-- Finset wrapper for
`exists_oldform_pieces_decomposition_of_coprime_prod_vanish`, phrasing the
depth product as `∏ p ∈ S, p`. -/
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
  generalize hQ : (∏ p ∈ S, p) = Q at hNZ h_vanish h_le_full ⊢
  have hprod : S.toList.prod = Q := hQ ▸ Finset.prod_toList S
  subst hprod
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_of_coprime_prod_vanish
    f S.toList hL h_vanish h_le_full

/-- Finset wrapper for
`exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish`. -/
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
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
    f hf_χ S.toList hL h_vanish h_le_full

/-- Finset wrapper for
`exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish`
(Nebentypus-aware, prime-q-support tagged). -/
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
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
    f hf_χ S.toList hL h_vanish h_le_full

/-- Finset wrapper for
`same_level_collapse_of_deep_oldform_image_of_projections`, taking the
projection bundle phrased on `L := S.toList`. -/
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
      (fun p hp ↦ hS p (Finset.mem_toList.mp hp))
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
  have hL : ∀ p ∈ L, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  have h_vanish_L : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0 := by
    intro n hn; exact h_vanish n (hprod ▸ hn)
  have h_le_full_L : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ) := by rw [hprod]; exact h_le_full
  exact same_level_collapse_of_deep_oldform_image_of_projections
    f hf_χ L hL h_vanish_L h_le_full_L proj

end HeckeRing.GL2.MainLemma
