/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.Coprime.Basic

/-!
# Support lemmas for the 2×2 Smith decomposition (POST-6a)

Three groups of small support lemmas for the Smith-normal-form route of
Miyake Lemma 4.6.3 (POST-6a):

## Content lemmas

* `Matrix.isUnit_of_dvd_entries_of_primitive2` — if `d : ℤ` divides every
  entry of a primitive 2×2 integer matrix `A` (where primitivity is stated
  in the `Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs) (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) = 1`
  form), then `IsUnit d` (equivalently, `d = ±1`).
* `Matrix.dvd_entries_of_mul_diag_mul_of_dvd` — if `d₀ ∣ d₁`, then `d₀`
  divides every entry of the product `U * !![d₀, 0; 0, d₁] * Q` for any
  2×2 integer matrices `U, Q`.

## Sign-flip and GL → SL normalisation

* `Matrix.signFlip2` — the 2×2 sign-flip matrix `!![-1, 0; 0, 1]`, used to
  absorb a determinant sign during the GL(2, ℤ) → SL(2, ℤ) normalisation.
* `Matrix.signFlip2_det`, `Matrix.signFlip2_mul_self` — basic properties.
* `Matrix.signFlip2_mul_diag_mul_signFlip2` — the **key identity**
  `signFlip2 · !![1, 0; 0, d] · signFlip2 = !![1, 0; 0, d]`, which is what
  makes the both-negative-GL case of the Smith decomposition land back in
  `SL(2, ℤ) × SL(2, ℤ)` without disturbing the diagonal.
* `Matrix.det_mul_signFlip2`, `Matrix.det_signFlip2_mul` — determinant
  flips under right/left multiplication by `signFlip2`.
* `Matrix.det_mul_signFlip2_eq_one`, `Matrix.det_signFlip2_mul_eq_one` —
  packaged consequences: if `U.det = -1`, then `(U · signFlip2).det = 1`
  (and dually for `Q`), so the GL witnesses become SL witnesses.

Together with `isUnit_of_dvd_entries_of_primitive2` +
`dvd_entries_of_mul_diag_mul_of_dvd`, these lemmas provide the full bridge
from Mathlib's Smith-normal-form data to the matrix-level factorisation
required by Miyake 4.6.3.

No custom axioms, no `native_decide`, no sorries.  Deliberately kept
independent of the `HeckeRIngs` / `Newforms` chain.
-/

namespace Matrix

variable {A : Matrix (Fin 2) (Fin 2) ℤ}

/-- **Primitive-content lemma for 2×2 integer matrices.**  If `d : ℤ` divides
every entry of a primitive 2×2 integer matrix `A`, then `d` is a unit in `ℤ`.

Primitivity is stated as
`Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs) (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) = 1`.
The conclusion `IsUnit d` in `ℤ` is equivalent (via `Int.isUnit_iff`) to
`d = 1 ∨ d = -1`.

This is the content lemma behind the Miyake 4.6.3 reduction: once the SNF
factorisation `A = U · !![d₀, 0; 0, d₁] · Q` with `d₀ ∣ d₁` gives "every entry
of `A` is divisible by `d₀`" (via `dvd_entries_of_mul_diag_mul_of_dvd`),
primitivity forces `IsUnit d₀`, and the sign-normalisation downstream yields
`d₀ = 1`. -/
lemma isUnit_of_dvd_entries_of_primitive2
    (hprim : Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
      (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) = 1)
    {d : ℤ} (h00 : d ∣ A 0 0) (h01 : d ∣ A 0 1) (h10 : d ∣ A 1 0) (h11 : d ∣ A 1 1) :
    IsUnit d := by
  have h_all : d.natAbs ∣ Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
      (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) :=
    Nat.dvd_gcd
      (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr h00) (Int.natAbs_dvd_natAbs.mpr h01))
      (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr h10) (Int.natAbs_dvd_natAbs.mpr h11))
  rw [hprim] at h_all
  exact Int.isUnit_iff_natAbs_eq.mpr (Nat.dvd_one.mp h_all)

/-- **Diagonal content lemma.**  For any 2×2 integer matrices `U, Q` and
integers `d₀, d₁` with `d₀ ∣ d₁`, the element `d₀` divides every entry of
the matrix product `U · !![d₀, 0; 0, d₁] · Q`.

This is the "SNF-factorisation ⇒ `d₀` is a common divisor of `A`'s entries"
half of the Miyake 4.6.3 reduction.  The companion lemma
`isUnit_of_dvd_entries_of_primitive2` then converts that common divisor into
a unit, given primitivity. -/
lemma dvd_entries_of_mul_diag_mul_of_dvd
    (U Q : Matrix (Fin 2) (Fin 2) ℤ) {d₀ d₁ : ℤ} (h : d₀ ∣ d₁) (i j : Fin 2) :
    d₀ ∣ (U * !![d₀, 0; 0, d₁] * Q) i j := by
  have h_prod : (U * !![d₀, 0; 0, d₁] * Q) i j =
      U i 0 * d₀ * Q 0 j + U i 1 * d₁ * Q 1 j := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h_prod]
  exact dvd_add ⟨U i 0 * Q 0 j, by ring⟩ ((h.mul_left (U i 1)).mul_right (Q 1 j))

/-- The 2×2 sign-flip matrix `!![-1, 0; 0, 1]`.  Used to absorb a
determinant sign during the GL(2, ℤ) → SL(2, ℤ) normalisation of the Smith
decomposition: when the ambient SNF factorisation `A = U · diag(1, d) · Q`
has `U.det = Q.det = -1`, right-multiplying `U` by `signFlip2` and
left-multiplying `Q` by `signFlip2` turns both into `SL(2, ℤ)` witnesses
while preserving the middle diagonal (see
`signFlip2_mul_diag_mul_signFlip2`). -/
def signFlip2 : Matrix (Fin 2) (Fin 2) ℤ := !![-1, 0; 0, 1]

@[simp]
lemma signFlip2_det : signFlip2.det = -1 := by
  simp [signFlip2, Matrix.det_fin_two_of]

@[simp]
lemma signFlip2_mul_self : signFlip2 * signFlip2 = 1 := by decide

/-- **Key identity for GL → SL sign normalisation.**  Conjugating the
diagonal matrix `!![1, 0; 0, d]` by `signFlip2` yields the same diagonal
matrix.  This is the essential fact that makes the both-`det = −1`
case of the Smith decomposition land back in `SL(2, ℤ) × SL(2, ℤ)`
without disturbing the central diagonal. -/
lemma signFlip2_mul_diag_mul_signFlip2 (d : ℤ) :
    signFlip2 * !![(1 : ℤ), 0; 0, d] * signFlip2 = !![(1 : ℤ), 0; 0, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [signFlip2, Matrix.mul_apply, Fin.sum_univ_two]

/-- Right-multiplying by `signFlip2` negates the determinant. -/
lemma det_mul_signFlip2 (U : Matrix (Fin 2) (Fin 2) ℤ) :
    (U * signFlip2).det = -U.det := by
  rw [Matrix.det_mul, signFlip2_det, mul_neg_one]

/-- Left-multiplying by `signFlip2` negates the determinant. -/
lemma det_signFlip2_mul (Q : Matrix (Fin 2) (Fin 2) ℤ) :
    (signFlip2 * Q).det = -Q.det := by
  rw [Matrix.det_mul, signFlip2_det, neg_one_mul]

/-- **GL → SL normalisation (right factor)**: if `U.det = -1`, then
`(U · signFlip2).det = 1`, so `U · signFlip2 ∈ SL(2, ℤ)`. -/
lemma det_mul_signFlip2_eq_one {U : Matrix (Fin 2) (Fin 2) ℤ} (hU : U.det = -1) :
    (U * signFlip2).det = 1 := by
  rw [det_mul_signFlip2, hU, neg_neg]

/-- **GL → SL normalisation (left factor)**: if `Q.det = -1`, then
`(signFlip2 · Q).det = 1`, so `signFlip2 · Q ∈ SL(2, ℤ)`. -/
lemma det_signFlip2_mul_eq_one {Q : Matrix (Fin 2) (Fin 2) ℤ} (hQ : Q.det = -1) :
    (signFlip2 * Q).det = 1 := by
  rw [det_signFlip2_mul, hQ, neg_neg]

/-- **Bezout column reduction.**  For integers `a, b` not both zero, there
exists `B ∈ SL(2, ℤ)` whose `mulVec` action on the column `![a, b]` zeros
the second entry and leaves `Int.gcd a b` in the first entry:

  `B · (a, b)ᵀ = (gcd(a, b), 0)ᵀ`.

The matrix is built from Bezout coefficients `Int.gcdA` / `Int.gcdB` and
the quotients `a / gcd`, `b / gcd`.  This is the core row-reduction step
used throughout the 2×2 Smith-decomposition algorithm. -/
lemma sl2Bezout_col_zero_out (a b : ℤ) (h_ne : a ≠ 0 ∨ b ≠ 0) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (B : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  have hd_ne : (Int.gcd a b : ℤ) ≠ 0 := by
    rw [Ne, Nat.cast_eq_zero, Int.gcd_eq_zero_iff]
    rintro ⟨ha, hb⟩
    exact h_ne.elim (· ha) (· hb)
  obtain ⟨a', ha'⟩ : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right a b
  have hbez : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b :=
    Int.gcd_eq_gcd_ab a b
  have h_det : Int.gcdA a b * a' + Int.gcdB a b * b' = 1 := by
    apply mul_left_cancel₀ hd_ne
    calc (Int.gcd a b : ℤ) * (Int.gcdA a b * a' + Int.gcdB a b * b')
        = Int.gcdA a b * ((Int.gcd a b : ℤ) * a') +
            Int.gcdB a b * ((Int.gcd a b : ℤ) * b') := by ring
      _ = a * Int.gcdA a b + b * Int.gcdB a b := by rw [← ha', ← hb']; ring
      _ = (Int.gcd a b : ℤ) * 1 := by rw [mul_one]; exact hbez.symm
  refine ⟨⟨!![Int.gcdA a b, Int.gcdB a b; -b', a'], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; linarith
  · have h0 : Int.gcdA a b * a + Int.gcdB a b * b = (Int.gcd a b : ℤ) := by
      rw [mul_comm (Int.gcdA a b) a, mul_comm (Int.gcdB a b) b, ← hbez]
    have h1 : -b' * a + a' * b = 0 := by
      have step : -b' * ((Int.gcd a b : ℤ) * a') + a' * ((Int.gcd a b : ℤ) * b') = 0 := by ring
      rw [← ha', ← hb'] at step; exact step
    ext i
    fin_cases i <;> (simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]; linarith)

/-- **Bezout row reduction.**  For integers `a, b` not both zero, there
exists `C ∈ SL(2, ℤ)` whose `vecMul` action on the row `![a, b]` zeros
the second entry and leaves `Int.gcd a b` in the first entry:

  `(a, b) · C = (gcd(a, b), 0)`.

Dual of `sl2Bezout_col_zero_out`; used for right-Bezout column clearing. -/
lemma sl2Bezout_row_zero_out (a b : ℤ) (h_ne : a ≠ 0 ∨ b ≠ 0) :
    ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ![a, b] ᵥ* (C : Matrix (Fin 2) (Fin 2) ℤ) = ![(Int.gcd a b : ℤ), 0] := by
  obtain ⟨B, hB⟩ := sl2Bezout_col_zero_out a b h_ne
  refine ⟨⟨(B : Matrix (Fin 2) (Fin 2) ℤ).transpose, ?_⟩, ?_⟩
  · rw [Matrix.det_transpose]; exact B.2
  · ext i
    have h := congr_fun hB i
    fin_cases i <;>
      simpa [Matrix.vecMul, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.transpose_apply, mul_comm] using h

/-- **Common-divisor-of-row-combination divides the 2×2 determinant.**
If `p ∣ a + k·c` and `p ∣ b + k·d`, then `p ∣ a·d − b·c`.  This is the key
observation behind the CRT existence of `k` making the row combination
coprime: common divisors of `(a + k·c, b + k·d)` are restricted to divisors
of the determinant, which is fixed and non-zero. -/
lemma dvd_det_of_dvd_row_combination {a b c d k p : ℤ}
    (hac : p ∣ a + k * c) (hbd : p ∣ b + k * d) :
    p ∣ a * d - b * c := by
  have h : p ∣ (a + k * c) * d - (b + k * d) * c := (hac.mul_right d).sub (hbd.mul_right c)
  simpa [show (a + k * c) * d - (b + k * d) * c = a * d - b * c from by ring] using h

/-- **Per-prime good residue over `ZMod p` (core).**  If `(a, b, c, d) : (ZMod p)⁴`
is not identically zero, then some residue `r : ZMod p` makes the pair
`(a + r·c, b + r·d)` not simultaneously zero.

Proof by contrapositive: if every `r` makes both components zero, then
applying `r = 0` gives `a = 0 ∧ b = 0` and `r = 1` gives `c = 0 ∧ d = 0`,
contradicting non-identical-zero.  No primality of `p` needed (the
statement is purely algebraic over an arbitrary commutative ring with
at least two elements; `ZMod p` works for all `p ≥ 2`). -/
lemma exists_good_residue_mod_prime_zmod
    {p : ℕ} [NeZero p] {a b c d : ZMod p}
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    ∃ r : ZMod p, ¬ (a + r * c = 0 ∧ b + r * d = 0) := by
  by_contra hall
  push Not at hall
  have h0 := hall 0
  have h1 := hall 1
  simp only [zero_mul, add_zero] at h0
  simp only [h0.1, h0.2, zero_add, one_mul] at h1
  exact hne ⟨h0.1, h0.2, h1.1, h1.2⟩

/-- **Per-prime good residue over `ℤ` (integer wrapper).**  For a quadruple
`(a, b, c, d) : ℤ⁴` whose entries are not all divisible by the prime `p`,
there is a non-negative integer `r < p` such that the row combination
`(a + r·c, b + r·d)` is not simultaneously divisible by `p`.

Transported from `exists_good_residue_mod_prime_zmod` via
`ZMod.intCast_zmod_eq_zero_iff_dvd`. -/
lemma exists_good_residue_mod_prime {a b c d : ℤ} {p : ℕ} [Fact p.Prime]
    (hne : ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c ∧ (p : ℤ) ∣ d)) :
    ∃ r : ℕ, r < p ∧
      ¬ ((p : ℤ) ∣ a + (r : ℤ) * c ∧ (p : ℤ) ∣ b + (r : ℤ) * d) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hne' : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧
      (c : ZMod p) = 0 ∧ (d : ZMod p) = 0) := by
    simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd] using hne
  obtain ⟨r, hr⟩ := exists_good_residue_mod_prime_zmod (p := p) hne'
  refine ⟨r.val, ZMod.val_lt r, fun ⟨h_ac, h_bd⟩ ↦ hr ⟨?_, ?_⟩⟩
  · have : ((a + (r.val : ℤ) * c : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h_ac
    simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id] using this
  · have : ((b + (r.val : ℤ) * d : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h_bd
    simpa [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_val, ZMod.cast_id] using this

/-- **Per-prime non-divisibility for primitive quadruples.**  If
`(a, b, c, d)` is primitive (nested `Nat.gcd` of `natAbs` is `1`), then no
prime can simultaneously divide all four entries. -/
private lemma not_all_dvd_of_primitive {a b c d : ℤ} {p : ℕ}
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) (Nat.gcd c.natAbs d.natAbs) = 1)
    (hp : p.Prime) :
    ¬ ((p : ℤ) ∣ a ∧ (p : ℤ) ∣ b ∧ (p : ℤ) ∣ c ∧ (p : ℤ) ∣ d) := by
  rintro ⟨h_a, h_b, h_c, h_d⟩
  have h_all : p ∣ Nat.gcd (Nat.gcd a.natAbs b.natAbs) (Nat.gcd c.natAbs d.natAbs) :=
    Nat.dvd_gcd
      (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr h_a) (Int.natAbs_dvd_natAbs.mpr h_b))
      (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr h_c) (Int.natAbs_dvd_natAbs.mpr h_d))
  rw [hprim] at h_all
  exact hp.one_lt.ne' (Nat.dvd_one.mp h_all)

/-- **Row combination zero forces zero determinant.**  If
`a + k·c = 0` and `b + k·d = 0`, then `a·d − b·c = 0`. -/
private lemma det_eq_zero_of_row_combination_zero {a b c d k : ℤ}
    (h1 : a + k * c = 0) (h2 : b + k * d = 0) :
    a * d - b * c = 0 := by
  have hcomb : (a + k * c) * d - (b + k * d) * c = 0 := by rw [h1, h2]; ring
  linarith [hcomb,
    show (a + k * c) * d - (b + k * d) * c = a * d - b * c from by ring]

/-- **CRT contradiction core.**  Given `k_nat` from the CRT construction
with the residue compatibility `hk_cong` against `r_nat` chosen to avoid
joint divisibility by primes of `(a·d − b·c).natAbs`, and a prime `q`
dividing both `a + k_nat·c` and `b + k_nat·d` (hence dividing the
determinant), derive `False`. -/
private lemma crt_contradiction_of_prime_div {a b c d : ℤ} {k_nat : ℕ} {r_nat : ℕ → ℕ}
    {M : ℕ} (hM_def : M = (a * d - b * c).natAbs) (hM_ne : M ≠ 0)
    (hr_good : ∀ p (_ : p ∈ M.primeFactors),
      ¬ ((p : ℤ) ∣ a + (r_nat p : ℤ) * c ∧ (p : ℤ) ∣ b + (r_nat p : ℤ) * d))
    (hk_cong : ∀ p ∈ M.primeFactors, k_nat ≡ r_nat p [MOD p])
    {q : ℕ} (hq_prime : q.Prime)
    (hq_dvd_ac : (q : ℤ) ∣ a + (k_nat : ℤ) * c)
    (hq_dvd_bd : (q : ℤ) ∣ b + (k_nat : ℤ) * d) :
    False := by
  have hq_mem : q ∈ M.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, hM_ne⟩
    rw [hM_def]
    exact_mod_cast Int.natAbs_dvd_natAbs.mpr (dvd_det_of_dvd_row_combination hq_dvd_ac hq_dvd_bd)
  have h_cong : k_nat ≡ r_nat q [MOD q] := hk_cong q hq_mem
  have h_sub_dvd : (q : ℤ) ∣ (k_nat : ℤ) - (r_nat q : ℤ) := by
    have := (Int.modEq_iff_dvd (a := (r_nat q : ℤ)) (b := (k_nat : ℤ))).mp
      (Int.natCast_modEq_iff.mpr h_cong.symm)
    simpa [sub_eq_neg_add, neg_sub] using this
  refine hr_good q hq_mem ⟨?_, ?_⟩
  · have h_eq : a + (k_nat : ℤ) * c - (a + (r_nat q : ℤ) * c) =
        ((k_nat : ℤ) - (r_nat q : ℤ)) * c := by ring
    exact (dvd_sub_right hq_dvd_ac).mp (h_eq ▸ h_sub_dvd.mul_right c)
  · have h_eq : b + (k_nat : ℤ) * d - (b + (r_nat q : ℤ) * d) =
        ((k_nat : ℤ) - (r_nat q : ℤ)) * d := by ring
    exact (dvd_sub_right hq_dvd_bd).mp (h_eq ▸ h_sub_dvd.mul_right d)

/-- **Primitive implies coprime linear row combination exists.**  For a
primitive quadruple `(a, b, c, d) : ℤ⁴` with non-zero "determinant"
`a·d − b·c ≠ 0`, there exists an integer `k` such that
`IsCoprime (a + k·c) (b + k·d)`.

This is the CRT-shortcut path to the 2×2 Smith decomposition: once such a
`k` is found, the row combination `(a + k·c, b + k·d)` has `Bezout`
coefficients allowing `sl2Bezout_row_zero_out`-style reduction to
`(1, 0)`, after which a single row operation clears the bottom row to
`(0, det A)` giving `diag(1, det A)`.

The proof uses Mathlib's `Nat.chineseRemainderOfFinset` over the prime
factors of `(a·d − b·c).natAbs`, combining the per-prime good residues
from `exists_good_residue_mod_prime`. -/
lemma exists_k_coprime_of_primitive {a b c d : ℤ}
    (hprim : Nat.gcd (Nat.gcd a.natAbs b.natAbs) (Nat.gcd c.natAbs d.natAbs) = 1)
    (hdet : a * d - b * c ≠ 0) :
    ∃ k : ℤ, IsCoprime (a + k * c) (b + k * d) := by
  set M : ℕ := (a * d - b * c).natAbs with hM_def
  have hM_ne : M ≠ 0 := Int.natAbs_ne_zero.mpr hdet
  have hP_prime : ∀ p ∈ M.primeFactors, p.Prime :=
    fun _ hp ↦ Nat.prime_of_mem_primeFactors hp
  classical
  have hP_exists : ∀ p ∈ M.primeFactors, ∃ r : ℕ, r < p ∧
      ¬ ((p : ℤ) ∣ a + (r : ℤ) * c ∧ (p : ℤ) ∣ b + (r : ℤ) * d) := fun p hp ↦
    haveI : Fact p.Prime := ⟨hP_prime p hp⟩
    exists_good_residue_mod_prime (a := a) (b := b) (c := c) (d := d) (p := p)
      (not_all_dvd_of_primitive hprim (hP_prime p hp))
  let r_nat : ℕ → ℕ := fun p ↦
    if h : p ∈ M.primeFactors then (hP_exists p h).choose else 0
  have hr_good : ∀ p (hp : p ∈ M.primeFactors),
      ¬ ((p : ℤ) ∣ a + (r_nat p : ℤ) * c ∧ (p : ℤ) ∣ b + (r_nat p : ℤ) * d) := by
    intro p hp
    simp only [r_nat, dif_pos hp]
    exact (hP_exists p hp).choose_spec.2
  have hP_ne_zero : ∀ p ∈ M.primeFactors, p ≠ 0 := fun p hp ↦ (hP_prime p hp).pos.ne'
  have hP_coprime : Set.Pairwise (↑M.primeFactors : Set ℕ)
      (fun p q : ℕ ↦ Nat.Coprime (id p) (id q)) := by
    intro p hp q hq hpq
    simpa using (Nat.coprime_primes (hP_prime p hp) (hP_prime q hq)).mpr hpq
  set k_nat := (Nat.chineseRemainderOfFinset r_nat id M.primeFactors hP_ne_zero hP_coprime : ℕ)
  have hk_cong : ∀ p ∈ M.primeFactors, k_nat ≡ r_nat p [MOD p] :=
    (Nat.chineseRemainderOfFinset r_nat id M.primeFactors hP_ne_zero hP_coprime).prop
  refine ⟨(k_nat : ℤ), ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra h_not_one
  set G := Int.gcd (a + (k_nat : ℤ) * c) (b + (k_nat : ℤ) * d) with hG_def
  rcases eq_or_ne G 0 with hG_zero | hG_ne
  · obtain ⟨h1, h2⟩ := Int.gcd_eq_zero_iff.mp (hG_def ▸ hG_zero)
    exact hdet (det_eq_zero_of_row_combination_zero h1 h2)
  have hG_gt_one : 1 < G := by
    rcases Nat.lt_or_ge G 1 with h_lt | _
    · interval_cases G; exact (hG_ne rfl).elim
    · omega
  obtain ⟨q, hq_prime, hq_dvd_G⟩ := Nat.exists_prime_and_dvd hG_gt_one.ne'
  have hq_dvd_G_int : (q : ℤ) ∣ (G : ℤ) := by exact_mod_cast hq_dvd_G
  exact crt_contradiction_of_prime_div hM_def hM_ne hr_good hk_cong hq_prime
    (hq_dvd_G_int.trans (Int.gcd_dvd_left _ _))
    (hq_dvd_G_int.trans (Int.gcd_dvd_right _ _))

/-- **Smith decomposition, 2×2 primitive, positive determinant.**
Given `A : Matrix (Fin 2) (Fin 2) ℤ` primitive (nested `Nat.gcd` of entries
equals `1`) with `0 < A.det`, there exist `U V ∈ SL(2, ℤ)` such that
`U * A * V = !![1, 0; 0, A.det]`.

Concrete Smith-decomposition form of Miyake Lemma 4.6.3 for 2×2 matrices,
assembled from `exists_k_coprime_of_primitive` (CRT existence of a coprime
row combination), `sl2Bezout_row_zero_out` (SL row-Bezout reduction), and
a trailing elementary row operation to clear the bottom-left entry. -/
theorem smith_decomp_of_primitive_posDet {A : Matrix (Fin 2) (Fin 2) ℤ}
    (hprim : Nat.gcd (Nat.gcd (A 0 0).natAbs (A 0 1).natAbs)
      (Nat.gcd (A 1 0).natAbs (A 1 1).natAbs) = 1)
    (hdet_pos : 0 < A.det) :
    ∃ U V : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (U : Matrix (Fin 2) (Fin 2) ℤ) * A * (V : Matrix (Fin 2) (Fin 2) ℤ) =
        !![1, 0; 0, A.det] := by
  have hdet_ne : A 0 0 * A 1 1 - A 0 1 * A 1 0 ≠ 0 := by
    rw [show A 0 0 * A 1 1 - A 0 1 * A 1 0 = A.det from (Matrix.det_fin_two A).symm]
    exact hdet_pos.ne'
  obtain ⟨k, hcop⟩ := exists_k_coprime_of_primitive hprim hdet_ne
  have hgcd_one : Int.gcd (A 0 0 + k * A 1 0) (A 0 1 + k * A 1 1) = 1 :=
    Int.isCoprime_iff_gcd_eq_one.mp hcop
  have hne : (A 0 0 + k * A 1 0) ≠ 0 ∨ (A 0 1 + k * A 1 1) ≠ 0 := by
    by_contra! h
    have : Int.gcd (A 0 0 + k * A 1 0) (A 0 1 + k * A 1 1) = 0 := by rw [h.1, h.2]; rfl
    omega
  let Ek : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, k; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩
  obtain ⟨V, hV⟩ := sl2Bezout_row_zero_out (A 0 0 + k * A 1 0) (A 0 1 + k * A 1 1) hne
  have hV' : ![A 0 0 + k * A 1 0, A 0 1 + k * A 1 1] ᵥ*
      (V : Matrix (Fin 2) (Fin 2) ℤ) = ![1, 0] := by
    rw [hV]; ext j; fin_cases j <;> simp [hgcd_one]
  have hV00 : (A 0 0 + k * A 1 0) * (V : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      (A 0 1 + k * A 1 1) * (V : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using congr_fun hV' 0
  have hV01 : (A 0 0 + k * A 1 0) * (V : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
      (A 0 1 + k * A 1 1) * (V : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 0 := by
    simpa [Matrix.vecMul, dotProduct, Fin.sum_univ_two] using congr_fun hV' 1
  set B : Matrix (Fin 2) (Fin 2) ℤ :=
    (Ek : Matrix (Fin 2) (Fin 2) ℤ) * A * (V : Matrix (Fin 2) (Fin 2) ℤ) with hB_def
  have hB_00 : B 0 0 = 1 := by
    show ((!![1, k; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * A *
      (V : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = 1
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linarith [hV00]
  have hB_01 : B 0 1 = 0 := by
    show ((!![1, k; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * A *
      (V : Matrix (Fin 2) (Fin 2) ℤ)) 0 1 = 0
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    linarith [hV01]
  have hB_det : B.det = A.det := by
    show ((Ek : Matrix (Fin 2) (Fin 2) ℤ) * A * (V : Matrix (Fin 2) (Fin 2) ℤ)).det = A.det
    rw [Matrix.det_mul, Matrix.det_mul, Ek.2, V.2]; ring
  have hB_11 : B 1 1 = A.det := by
    have h1 : B.det = B 0 0 * B 1 1 - B 0 1 * B 1 0 := Matrix.det_fin_two B
    rw [hB_00, hB_01] at h1
    linarith [hB_det, h1]
  let U₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![1, 0; -(B 1 0), 1], by rw [Matrix.det_fin_two_of]; ring⟩
  refine ⟨U₂ * Ek, V, ?_⟩
  show ((U₂ : Matrix (Fin 2) (Fin 2) ℤ) * (Ek : Matrix (Fin 2) (Fin 2) ℤ)) * A *
      (V : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; 0, A.det]
  rw [show (U₂ : Matrix (Fin 2) (Fin 2) ℤ) * (Ek : Matrix (Fin 2) (Fin 2) ℤ) * A *
        (V : Matrix (Fin 2) (Fin 2) ℤ) = (U₂ : Matrix (Fin 2) (Fin 2) ℤ) * B from by
    rw [mul_assoc (U₂ : Matrix (Fin 2) (Fin 2) ℤ),
      mul_assoc (U₂ : Matrix (Fin 2) (Fin 2) ℤ), ← hB_def]]
  show (!![1, 0; -(B 1 0), 1] : Matrix (Fin 2) (Fin 2) ℤ) * B = !![1, 0; 0, A.det]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hB_00, hB_01, hB_11]

end Matrix
