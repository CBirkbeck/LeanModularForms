/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Coprime
import Mathlib.Tactic.LinearCombination
import Mathlib.RingTheory.Int.Basic

/-!
# Surjectivity of the reduction map SL₂(ℤ) → SL₂(ℤ/dℤ)

This file proves that the natural reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective
(strong approximation for SL₂). This is a fundamental result in the theory of
congruence subgroups and Hecke operators.

## Main results

* `SL2_reduction_surjective` — the map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective.

## Proof strategy

Given `g = !![a, b; c, d] ∈ SL₂(ℤ/dℤ)` with `a * d - b * c = 1`:

1. **Coprime lifting**: Lift `a, c` to integers `a₁, c₀` with `a₁ ≡ a (mod d)`,
   `c₀ ≡ c (mod d)`, and `gcd(a₁, c₀) = 1`. This uses the stable range property of `ℤ`:
   since `gcd(a₀, c₀, d) = 1` for arbitrary lifts, we can adjust `a₀` by multiples of `d`
   to eliminate common factors with `c₀`.

2. **Bezout completion**: By `IsCoprime.exists_SL2_col`, find `σ ∈ SL₂(ℤ)` whose
   first column is `(a₁, c₀)`.

3. **Upper triangular remainder**: The matrix `map(σ)⁻¹ * g` has first column `(1, 0)`
   by direct computation, so it equals `!![1, t; 0, 1]` for some `t ∈ ℤ/dℤ`.

4. **Lift upper triangular**: `!![1, t; 0, 1]` is the image of `!![1, t'; 0, 1] ∈ SL₂(ℤ)`
   for any integer lift `t'` of `t`.

5. **Combine**: `g = map(σ) * !![1, t; 0, 1] = map(σ * !![1, t'; 0, 1])`.

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §1.6
* Serre, *A Course in Arithmetic*, Ch. VII, Lemma 15
-/

open Matrix SpecialLinearGroup

namespace SL2Reduction

/-! ### Coprime lifting -/

/-- **Coprime lifting (stable range of ℤ)**: If `(a : ZMod d)` and `(c : ZMod d)` are coprime,
then there exist integer lifts `a'` and `c'` that are coprime in `ℤ`.

This is equivalent to the assertion that `ℤ` has stable range 2: for any `a₀, c₀, m ∈ ℤ`
with `gcd(a₀, c₀, m) = 1`, there exists `k` such that `gcd(a₀ + k * m, c₀) = 1`.

Proof sketch: Pick arbitrary lifts `a₀, c₀`. From `IsCoprime a c` in `ZMod d`, we get
`gcd(a₀, c₀, d) = 1`. We want `k` with `gcd(a₀ + k * d, c₀) = 1`. For each prime
`p | c₀`: if `p | a₀` then `p ∤ d` (from the triple gcd condition), so `p ∤ (a₀ + k * d)`
iff `p ∤ k * d` iff `p ∤ k`; if `p ∤ a₀` and `p | d` then `p ∤ (a₀ + k * d)` automatically;
if `p ∤ a₀` and `p ∤ d` then `p | (a₀ + k * d)` iff `k ≡ -a₀ * d⁻¹ (mod p)`. In each case,
at most one residue class modulo `p` is excluded. Since the relevant primes are distinct
divisors of `c₀` (a finite set), by the Chinese Remainder Theorem a valid `k` exists. -/
private lemma natAbs_emod_lt (a c : ℤ) (hc : c ≠ 0) : (a % c).natAbs < c.natAbs := by
  rw [Int.natAbs_emod a hc]
  split
  case isTrue => exact Nat.mod_lt _ (Int.natAbs_pos.mpr hc)
  case isFalse h =>
    push_neg at h
    have : a.natAbs % c.natAbs ≠ 0 := by
      intro heq; exact h.2 (Int.natAbs_dvd_natAbs.mp (Nat.dvd_of_mod_eq_zero heq))
    omega

private lemma isCoprime_emod {d : ℕ} [NeZero d] {a₁ c₁ : ℤ}
    (hac : IsCoprime (a₁ : ZMod d) (c₁ : ZMod d)) :
    IsCoprime (c₁ : ZMod d) ((a₁ % c₁ : ℤ) : ZMod d) := by
  have h : (a₁ % c₁ : ℤ) = a₁ + c₁ * (-(a₁ / c₁)) := by rw [Int.emod_def]; ring
  rw [h]; push_cast; exact hac.symm.add_mul_left_right _

/-- **Coprime lifting (stable range of ℤ)**: the proof uses Euclidean descent.
Given `IsCoprime a₁ c₁` in `ZMod d`, apply the extended Euclidean algorithm to
`(a₁, c₁)` in `ℤ`, swapping at each step. The coprimality in `ZMod d` is preserved
under the Euclidean step `(a₁, c₁) ↦ (c₁, a₁ % c₁)`, and the back-substitution
`a₀ = r₀ + q * c₀` recovers the correct congruence class modulo `d`. -/
theorem IsCoprime.lift_to_int {d : ℕ} [NeZero d] {a c : ZMod d}
    (hac : IsCoprime a c) :
    ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a ∧ (c₀ : ZMod d) = c ∧ IsCoprime a₀ c₀ := by
  obtain ⟨a₁, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨c₁, rfl⟩ := ZMod.intCast_surjective c
  suffices h : ∀ n, ∀ a₁ c₁ : ℤ, c₁.natAbs ≤ n →
      IsCoprime (a₁ : ZMod d) (c₁ : ZMod d) →
      ∃ a₀ c₀ : ℤ, (a₀ : ZMod d) = a₁ ∧ (c₀ : ZMod d) = c₁ ∧ IsCoprime a₀ c₀ from
    h c₁.natAbs a₁ c₁ le_rfl hac
  intro n; induction n with
  | zero =>
    intro a₁ c₁ hle hac
    have hc₁ : c₁ = 0 := by omega
    subst hc₁; simp only [Int.cast_zero] at hac ⊢
    have hunit : IsUnit (a₁ : ZMod d) := by rwa [isCoprime_zero_right] at hac
    rw [ZMod.coe_int_isUnit_iff_isCoprime] at hunit
    exact ⟨a₁, d, rfl, by simp, hunit.symm⟩
  | succ n ih =>
    intro a₁ c₁ hle hac
    by_cases hc₁ : c₁ = 0
    · subst hc₁; simp only [Int.cast_zero] at hac ⊢
      have hunit : IsUnit (a₁ : ZMod d) := by rwa [isCoprime_zero_right] at hac
      rw [ZMod.coe_int_isUnit_iff_isCoprime] at hunit
      exact ⟨a₁, d, rfl, by simp, hunit.symm⟩
    · -- Euclidean step: recurse with (c₁, a₁ % c₁), then back-substitute
      have hr_le : (a₁ % c₁).natAbs ≤ n :=
        Nat.lt_succ_iff.mp ((natAbs_emod_lt a₁ c₁ hc₁).trans_le hle)
      obtain ⟨c₀, r₀, hc₀, hr₀, hcop⟩ := ih c₁ (a₁ % c₁) hr_le (isCoprime_emod hac)
      refine ⟨r₀ + a₁ / c₁ * c₀, c₀, ?_, hc₀, hcop.symm.add_mul_right_left _⟩
      show ((r₀ + a₁ / c₁ * c₀ : ℤ) : ZMod d) = (a₁ : ZMod d)
      conv_rhs => rw [show a₁ = a₁ % c₁ + a₁ / c₁ * c₁ from by
        have := Int.mul_ediv_add_emod a₁ c₁; linarith]
      push_cast; rw [hr₀, hc₀]

/-! ### Determinant and coprimality -/

/-- The first column of an SL₂ matrix is coprime (from the determinant condition). -/
theorem isCoprime_of_det_eq_one {R : Type*} [CommRing R]
    {a b c d : R} (h : a * d - b * c = 1) : IsCoprime a c :=
  ⟨d, -b, by linear_combination h⟩

/-! ### Upper triangular matrices -/

/-- An SL₂ element with first column `(1, 0)` is upper unitriangular. -/
theorem SL2_eq_upperUniTri {R : Type*} [CommRing R]
    (h : SpecialLinearGroup (Fin 2) R)
    (h00 : h 0 0 = 1) (h10 : h 1 0 = 0) :
    h = ⟨!![1, h 0 1; 0, 1], by
      rw [det_fin_two]; simp [cons_val_zero, cons_val_one]⟩ := by
  ext i j
  induction h using fin_two_induction with
  | _ a b c dd hdet =>
    simp at h00 h10
    subst h00; subst h10
    fin_cases i <;> fin_cases j <;> simp [cons_val_zero, cons_val_one]
    linear_combination hdet

/-- An upper unitriangular matrix in SL₂(ℤ/dℤ) is in the range of the reduction map. -/
theorem upperUniTri_mem_range (d : ℕ) [NeZero d] (t : ZMod d) :
    ∃ σ : SpecialLinearGroup (Fin 2) ℤ,
      SpecialLinearGroup.map (Int.castRingHom (ZMod d)) σ =
      (⟨!![1, t; 0, 1], by
        rw [det_fin_two]; simp [cons_val_zero, cons_val_one]⟩ :
        SpecialLinearGroup (Fin 2) (ZMod d)) := by
  obtain ⟨t₀, rfl⟩ := ZMod.intCast_surjective t
  exact ⟨⟨!![1, t₀; 0, 1], by
      rw [det_fin_two]; simp [cons_val_zero, cons_val_one]⟩, by
    ext i j
    simp [map_apply_coe, RingHom.mapMatrix_apply, map_apply]
    fin_cases i <;> fin_cases j <;> simp⟩

/-! ### Column matching implies upper triangular quotient -/

/-- If two SL₂ elements share the same first column, their quotient has
`(1, 0)` entry equal to `0`. -/
theorem inv_mul_10_eq_zero {R : Type*} [CommRing R]
    (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) :
    (M⁻¹ * g) 1 0 = 0 := by
  induction M using fin_two_induction with
  | _ a₁ b₁ c₁ d₁ hdet₁ =>
  induction g using fin_two_induction with
  | _ a₂ b₂ c₂ d₂ hdet₂ =>
    simp at h0 h1
    subst h0; subst h1
    simp [coe_inv, adjugate_fin_two, mul_apply, Fin.sum_univ_two, of_apply,
      cons_val_zero, cons_val_one]
    ring

/-- If two SL₂ elements share the same first column, their quotient has
`(0, 0)` entry equal to `1`. -/
theorem inv_mul_00_eq_one {R : Type*} [CommRing R]
    (M g : SpecialLinearGroup (Fin 2) R)
    (h0 : M 0 0 = g 0 0) (h1 : M 1 0 = g 1 0) :
    (M⁻¹ * g) 0 0 = 1 := by
  induction M using fin_two_induction with
  | _ a₁ b₁ c₁ d₁ hdet₁ =>
  induction g using fin_two_induction with
  | _ a₂ b₂ c₂ d₂ hdet₂ =>
    simp at h0 h1
    subst h0; subst h1
    simp [coe_inv, adjugate_fin_two, mul_apply, Fin.sum_univ_two, of_apply,
      cons_val_zero, cons_val_one]
    linear_combination hdet₁

/-! ### Main theorem -/

/-- **Strong approximation for SL₂**: The reduction map `SL₂(ℤ) → SL₂(ℤ/dℤ)` is surjective.

For any element of `SL₂(ℤ/dℤ)`, there exists a preimage in `SL₂(ℤ)` under the
natural ring homomorphism `ℤ → ℤ/dℤ`. -/
theorem SL2_reduction_surjective (d : ℕ) [NeZero d] :
    Function.Surjective (SpecialLinearGroup.map (Int.castRingHom (ZMod d)) :
      SpecialLinearGroup (Fin 2) ℤ →* SpecialLinearGroup (Fin 2) (ZMod d)) := by
  intro g
  -- Decompose g into its entries
  induction g using fin_two_induction with
  | _ a b c dd hdet =>
    -- Step 1: The first column (a, c) is coprime in ZMod d
    have hcop_mod : IsCoprime a c := isCoprime_of_det_eq_one hdet
    -- Step 2: Lift to coprime integers
    obtain ⟨a₀, c₀, ha₀, hc₀, hcop⟩ := IsCoprime.lift_to_int hcop_mod
    -- Step 3: Complete to an SL₂(ℤ) matrix with first column (a₀, c₀)
    obtain ⟨σ, hσ0, hσ1⟩ := hcop.exists_SL2_col (0 : Fin 2)
    -- Step 4: The image of σ in SL₂(ZMod d) has first column (a, c)
    set M := SpecialLinearGroup.map (Int.castRingHom (ZMod d)) σ
    have hM0 : M 0 0 = a := by
      simp [M, map_apply_coe, RingHom.mapMatrix_apply, map_apply, hσ0, ha₀]
    have hM1 : M 1 0 = c := by
      simp [M, map_apply_coe, RingHom.mapMatrix_apply, map_apply, hσ1, hc₀]
    -- Step 5: Form the target element as an SL₂ matrix
    have hdet' : (!![a, b; c, dd] : Matrix (Fin 2) (Fin 2) (ZMod d)).det = 1 := by
      rw [det_fin_two]; show a * dd - b * c = 1; exact hdet
    set g₀ : SpecialLinearGroup (Fin 2) (ZMod d) := ⟨!![a, b; c, dd], hdet'⟩
    -- Step 6: M⁻¹ * g₀ is upper unitriangular
    have hg0_col0 : g₀ 0 0 = a := by simp [g₀, cons_val_zero]
    have hg0_col1 : g₀ 1 0 = c := by simp [g₀, cons_val_zero, cons_val_one]
    have h_10 : (M⁻¹ * g₀) 1 0 = 0 :=
      inv_mul_10_eq_zero M g₀ (by rw [hM0, hg0_col0]) (by rw [hM1, hg0_col1])
    have h_00 : (M⁻¹ * g₀) 0 0 = 1 :=
      inv_mul_00_eq_one M g₀ (by rw [hM0, hg0_col0]) (by rw [hM1, hg0_col1])
    -- Step 7: So M⁻¹ * g₀ = !![1, t; 0, 1] for some t
    set t := (M⁻¹ * g₀) 0 1
    have hQ : M⁻¹ * g₀ = ⟨!![1, t; 0, 1], by
        rw [det_fin_two]; simp [cons_val_zero, cons_val_one]⟩ :=
      SL2_eq_upperUniTri _ h_00 h_10
    -- Step 8: Lift the upper unitriangular matrix
    obtain ⟨τ, hτ⟩ := upperUniTri_mem_range d t
    -- Step 9: g₀ = M * (M⁻¹ * g₀) = map(σ) * map(τ) = map(σ * τ)
    refine ⟨σ * τ, ?_⟩
    change _ = g₀
    have hg₀_eq : g₀ = M * (M⁻¹ * g₀) := by group
    rw [map_mul, hg₀_eq, hQ, ← hτ]

end SL2Reduction
