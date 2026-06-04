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

include hp in
private lemma deg_ppow_shift (i k : ℕ) (hi : i < k / 2 + 1) :
    deg (GL_pair 2) (T_ad (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
    deg (GL_pair 2) (T_ad (p ^ i) (p ^ (k - i))) := by
  by_cases h2i : 2 * i < k
  · rw [deg_ppow_term_lt p hp (i + 1) (k + 2) (by omega),
      show k + 2 - 2 * (i + 1) - 1 = k - 2 * i - 1 by omega,
      (deg_ppow_term_lt p hp i k h2i).symm]
  · rw [deg_ppow_term_eq p hp (i + 1) (k + 2) (by omega),
      deg_ppow_term_eq p hp i k (by omega)]

/-- `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ`.
    Proof by strong induction: for k >= 2, split the expansion at i=0 to get
    `deg = p^{k-1}(p+1) + deg_tail`, where the tail's degree equals `deg(T_sum(p^{k-2}))`
    by a shift argument (the degree of `T_ad(p^{i+1}, p^{k-i-1})` equals that of
    `T_ad(p^i, p^{k-2-i})` since both have the same diagonal ratio). -/
theorem deg_T_sum_prime_pow (k : ℕ) :
    deg (GL_pair 2) (T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
    ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
  rw [T_sum_ppow_expansion p hp k, map_sum]
  match k with
  | 0 =>
    simp only [Nat.zero_div, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    exact deg_ppow_term_eq p hp 0 0 rfl
  | 1 =>
    simp only [show (1 : ℕ) / 2 = 0 from rfl, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    convert deg_ppow_term_lt p hp 0 1 (by omega) using 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    push_cast; ring
  | k + 2 =>
    have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
    rw [hdiv, Finset.sum_range_succ']
    have h_tail : ∑ i ∈ Finset.range (k / 2 + 1),
        (deg (GL_pair 2)) (T_ad (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
        ∑ i ∈ Finset.range (k / 2 + 1), (deg (GL_pair 2)) (T_ad (p ^ i) (p ^ (k - i))) :=
      Finset.sum_congr rfl fun i hi ↦ by
        rw [Finset.mem_range] at hi; exact deg_ppow_shift p hp i k hi
    rw [h_tail, show deg (GL_pair 2) (T_ad (p ^ 0) (p ^ (k + 2 - 0))) =
        ↑(p ^ (k + 1) * (p + 1)) by
      simpa [show k + 2 - 0 - 1 = k + 1 by omega] using
        deg_ppow_term_lt p hp 0 (k + 2) (by omega)]
    have ih_k := ih k (by omega)
    rw [T_sum_ppow_expansion p hp k, map_sum] at ih_k; rw [ih_k]
    conv_rhs =>
      rw [show k + 2 + 1 = (k + 1 + 1) + 1 by omega,
        Finset.sum_range_succ,
        show k + 1 + 1 = (k + 1) + 1 by omega,
        Finset.sum_range_succ]
    push_cast; ring

private lemma deg_T_sum_one : deg (GL_pair 2) (T_sum 1) = 1 := by
  change deg (GL_pair 2) (∑ a ∈ Nat.divisors 1, T_ad a (1 / a)) = 1
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  rw [deg_T_ad_of_pos 1 1 one_pos one_pos (dvd_refl 1),
    show T_diag (![1, 1]) = T_diag (fun _ ↦ (1 : ℕ)) by
      congr 1; ext j; fin_cases j <;> rfl]
  exact deg_T_diag_scalar 1 one_pos

/-- Theorem 3.24(7): `deg(T(m)) = σ₁(m)`.
    By prime factorization + coprime multiplicativity + prime-power case. -/
theorem deg_T_sum (m : ℕ+) :
    deg (GL_pair 2) (T_sum m) = (σ 1) (m : ℕ) := by
  obtain ⟨n, hn⟩ := m
  revert hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one =>
    intro hn
    rw [show (⟨1, hn⟩ : ℕ+) = (1 : ℕ+) from rfl, deg_T_sum_one]
    simp
  | @prime_pow p k hp hk =>
    intro hn
    rw [deg_T_sum_prime_pow p hp k]; simp only [ArithmeticFunction.sigma_one_apply]
    have h := @Nat.sum_divisors_prime_pow ℕ _ k p id hp; simp only [id] at h
    exact_mod_cast h.symm
  | @coprime a b ha hb hcop iha ihb =>
    intro hn
    have ha_pos : 0 < a := by omega
    have hb_pos : 0 < b := by omega
    rw [show T_sum ⟨a * b, hn⟩ = T_sum ⟨a, ha_pos⟩ * T_sum ⟨b, hb_pos⟩ from
      (T_sum_mul_coprime ⟨a, ha_pos⟩ ⟨b, hb_pos⟩ hcop).symm,
      map_mul, iha ha_pos, ihb hb_pos]
    simp only [ArithmeticFunction.sigma_one_apply]
    exact_mod_cast (Nat.Coprime.sum_divisors_mul hcop).symm

end HeckeRing.GL2
