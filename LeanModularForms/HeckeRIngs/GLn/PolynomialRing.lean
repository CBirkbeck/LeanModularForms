/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.PrimeDecomposition
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial Ring Structure of the p-local Hecke Ring

Shimura's Theorem 3.20: the p-local Hecke ring `R_p^{(n)}` is isomorphic to a polynomial
ring `ℤ[X₁,...,Xₙ]` in `n` variables.

## Main definitions

* `T_gen_diag` — the diagonal for the k-th generator `T(1,...,1,p,...,p)`
* `T_gen` — the k-th generator of `R_p`: `T_gen k = T(1,...,1,p,...,p)` with `k+1` entries of `p`
* `ppowWeight` — weight of a p-power diagonal: sum of exponents

## Main results

* `divChain_T_gen` — the T_gen diagonal satisfies the divisibility chain condition
* `T_gen_mem_R_p` — each generator lies in `R_p`
* `T_gen_generates_R_p` — the generators generate `R_p` (surjectivity)
* `T_gen_algebraically_independent` — the generators are algebraically independent (injectivity)
* `R_p_isPolynomialRing` — Theorem 3.20: `R_p ≅ ℤ[X₁,...,Xₙ]`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2, Theorem 3.20
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ) [NeZero n]

/-! ### Generator diagonals -/

section TGen

variable (p : ℕ) (hp : p.Prime)

/-- The diagonal for the k-th generator: `(1,...,1,p,...,p)` with `n-1-k` ones
    followed by `k+1` entries of `p`. Here `k : Fin n`, giving `n` generators. -/
def T_gen_diag (k : Fin n) : Fin n → ℕ :=
  fun i => if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p

omit [NeZero n] in
@[simp]
lemma T_gen_diag_val (k : Fin n) (i : Fin n) :
    T_gen_diag n p k i =
    if (i : ℕ) < n - 1 - (k : ℕ) then 1 else p := rfl

omit [NeZero n] in
lemma T_gen_diag_pos (hp : p.Prime) (k : Fin n) : ∀ i, 0 < T_gen_diag n p k i := by
  intro i; simp only [T_gen_diag]; split_ifs with h
  · omega
  · exact hp.pos

omit [NeZero n] in
/-- The T_gen diagonal satisfies the divisibility chain condition. -/
lemma divChain_T_gen (k : Fin n) :
    DivChain n (T_gen_diag n p k) := by
  intro i hi
  simp only [T_gen_diag_val]
  by_cases h1 : i < n - 1 - (k : ℕ)
  · by_cases h2 : i + 1 < n - 1 - (k : ℕ)
    · simp [h1, h2]
    · simp [h1, h2]
  · have h2 : ¬ (i + 1 < n - 1 - (k : ℕ)) := by omega
    simp [h1, h2]

/-- The k-th generator of R_p: `T(1,...,1,p,...,p)` with `k+1` entries of `p`. -/
noncomputable def T_gen (k : Fin n) : HeckeAlgebra n :=
  T_elem n (T_gen_diag n p k) (T_gen_diag_pos n p hp k) (divChain_T_gen n p k)

omit [NeZero n] in
/-- The T_gen diagonal has p-power entries (each entry is 1 = p^0 or p = p^1). -/
lemma T_gen_diag_is_ppow (k : Fin n) :
    T_gen_diag n p k =
    ppowDiag n p (fun i => if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  funext i
  simp only [T_gen_diag, ppowDiag]
  split_ifs <;> simp

omit [NeZero n] in
/-- The exponent function for T_gen is monotone. -/
lemma T_gen_exp_monotone (k : Fin n) :
    Monotone (fun i : Fin n => if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1) := by
  intro i j hij
  simp only
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact le_rfl

/-- Each T_gen lies in R_p. -/
lemma T_gen_mem_R_p (k : Fin n) : T_gen n p hp k ∈ R_p n p hp := by
  have h_eq : T_gen n p hp k =
      T_elem n (ppowDiag n p (fun i => if (i : ℕ) < n - 1 - (k : ℕ) then 0 else 1))
        (ppowDiag_pos n p hp _)
        (divChain_ppow n p _ (T_gen_exp_monotone n k)) :=
    T_elem_congr_diag n (T_gen_diag_is_ppow n p k) _ _ _ _
  rw [h_eq]
  exact T_elem_ppow_mem_R_p n p hp _ (T_gen_exp_monotone n k)

end TGen

/-! ### Weight of a p-power diagonal -/

section Weight

omit [NeZero n] in
/-- Weight of a p-power diagonal: the sum of all exponents. -/
def ppowWeight (e : Fin n → ℕ) : ℕ := ∑ i, e i

omit [NeZero n] in
/-- Weight is zero iff all exponents are zero. -/
lemma ppowWeight_eq_zero_iff (e : Fin n → ℕ) :
    ppowWeight n e = 0 ↔ ∀ i, e i = 0 := by
  simp [ppowWeight, Finset.sum_eq_zero_iff]

end Weight

/-! ### Polynomial ring isomorphism (Theorem 3.20) -/

section PolynomialRing

variable (p : ℕ) (hp : p.Prime)

/-- Evaluation homomorphism: `Xₖ ↦ T_gen k`.
    Maps `ℤ[X₁,...,Xₙ]` into the Hecke algebra. -/
noncomputable def evalHom : MvPolynomial (Fin n) ℤ →+* HeckeAlgebra n :=
  MvPolynomial.eval₂Hom (Int.castRingHom (HeckeAlgebra n)) (fun k => T_gen n p hp k)

/-- Every element of R_p is in the image of evalHom (surjectivity). -/
theorem T_gen_generates_R_p :
    ∀ f ∈ R_p n p hp, f ∈ (evalHom n p hp).range := by
  sorry

/-- Shimura Theorem 3.20: the p-local Hecke ring is isomorphic to a polynomial ring.
    `R_p^{(n)} ≅ ℤ[X₁,...,Xₙ]`. -/
noncomputable def R_p_isPolynomialRing :
    MvPolynomial (Fin n) ℤ ≃+* R_p n p hp := by
  sorry

end PolynomialRing

end HeckeRing.GLn
