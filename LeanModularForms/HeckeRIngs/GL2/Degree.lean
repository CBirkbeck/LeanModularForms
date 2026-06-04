/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.MultiplicationTable

/-!
# Degree formulas for GL₂ Hecke operators

Shimura Theorem 3.24, identities 6 and 7: degree formulas for the GL₂ Hecke algebra.

## Main results

* `deg_T_diag_ppow` — `deg(T(pⁱ, p^{i+k})) = p^{k−1}(p+1)` for k > 0
* `deg_T_diag_scalar` — `deg(T(c,c)) = 1`
* `deg_T_sum_prime_pow` — `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ`
* `deg_T_sum` — `deg(T(m)) = σ₁(m)`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Theorem 3.24
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2
open scoped ArithmeticFunction.sigma

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

include hp in
/-- Theorem 3.24(6): `deg(T(pⁱ, p^{i+k})) = p^{k-1}(p+1)` for k > 0. -/
theorem deg_T_diag_ppow (i k : ℕ) (hk : 0 < k) :
    HeckeCoset_deg (GL_pair 2) (T_diag (![p ^ i, p ^ (i + k)])) =
    ↑(p ^ (k - 1) * (p + 1)) :=
  HeckeCoset_deg_T_diag_two_prime p hp (![p ^ i, p ^ (i + k)])
    (fun j ↦ by fin_cases j <;> exact pow_pos hp.pos _)
    (fun j hj ↦ by
      obtain rfl : j = 0 := by omega
      simpa using Nat.pow_dvd_pow p (Nat.le_add_right i k))
    k hk (by simp [Nat.pow_div (Nat.le_add_right i k) hp.pos])

/-- Scalar case: `deg(T(c, c)) = 1`. -/
theorem deg_T_diag_scalar (c : ℕ) (hc : 0 < c) :
    HeckeCoset_deg (GL_pair 2) (T_diag (fun _ ↦ c)) = 1 :=
  HeckeCoset_deg_T_diag_two_scalar (fun _ ↦ c) (fun _ ↦ hc) (divChain_const 2 c) rfl

private lemma deg_T_ad_of_pos (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (hdvd : a ∣ d) :
    deg (GL_pair 2) (T_ad a d) = HeckeCoset_deg (GL_pair 2) (T_diag ![a, d]) := by
  simp [deg, T_ad_of_pos a d ha hd hdvd, T_elem]

include hp in
private lemma deg_ppow_term_lt (i k : ℕ) (h2i : 2 * i < k) :
    deg (GL_pair 2) (T_ad (p ^ i) (p ^ (k - i))) =
    ↑(p ^ (k - 2 * i - 1) * (p + 1)) := by
  have h_exp_eq : k - i = i + (k - 2 * i) := by omega
  rw [deg_T_ad_of_pos (p ^ i) (p ^ (k - i)) (pow_pos hp.pos i) (pow_pos hp.pos (k - i))
      (Nat.pow_dvd_pow p (by omega)),
    show (![p ^ i, p ^ (k - i)] : Fin 2 → ℕ) = ![p ^ i, p ^ (i + (k - 2 * i))] by
      ext j; fin_cases j <;> simp [h_exp_eq]]
  exact deg_T_diag_ppow p hp i (k - 2 * i) (by omega)

include hp in
private lemma deg_ppow_term_eq (i k : ℕ) (h2i : 2 * i = k) :
    deg (GL_pair 2) (T_ad (p ^ i) (p ^ (k - i))) = 1 := by
  rw [show k - i = i by omega,
    deg_T_ad_of_pos (p ^ i) (p ^ i) (pow_pos hp.pos i) (pow_pos hp.pos i) (dvd_refl _),
    show T_diag (![p ^ i, p ^ i]) = T_diag (fun _ ↦ p ^ i) by
      congr 1; ext j; fin_cases j <;> rfl]
  exact deg_T_diag_scalar (p ^ i) (pow_pos hp.pos i)

end HeckeRing.GL2
