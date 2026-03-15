/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Basic
import LeanModularForms.HeckeRIngs.GLn.Degree
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction

/-!
# Shimura Theorem 3.24: Multiplication Table for GL₂ Hecke Algebra

The 7 multiplication identities for the n=2 Hecke algebra.

## Main results

* `thm324_2` — `T(1,pᵏ) = T(pᵏ) − T(p,p) · T(p^{k−2})` for k ≥ 2
* `thm324_3` — `T(m) · T(n) = Σ d · T(d,d) · T(mn/d²)`
* `thm324_4` — `T(pʳ) · T(pˢ) = Σ pⁱ · T(pⁱ,pⁱ) · T(p^{r+s−2i})` for r ≤ s
* `thm324_5` — `T(p) · T(1,pᵏ) = T(1,p^{k+1}) + m · T(p,pᵏ)` (key computation)
* `thm324_6` — `deg(T(pⁱ, p^{i+k})) = p^{k−1}(p+1)` (wrapping existing)
* `thm324_6_scalar` — `deg(T(c,c)) = 1` (wrapping existing)
* `thm324_7` — `deg(T(m)) = σ₁(m)`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Theorem 3.24
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2

namespace HeckeRing.GL2

variable (p : ℕ) (hp : p.Prime)

/-! ### Identity 1: T(m) = Σ T(a,d) — definitional

Shimura's T(m) is defined as `T_sum m`, which is exactly the sum
`Σ_{a ∣ m, a²∣m} T(a, m/a)`. This identity is the definition itself. -/

/-! ### Identity 2: Telescoping -/

section Telescoping

/-- `T_ad'(p^i, p^d)` unfolds to `T_ad` when `i ≤ d`. -/
private lemma T_ad'_ppow (i d : ℕ) (hid : i ≤ d) :
    T_ad' (p ^ i) (p ^ d) =
    T_ad ⟨p ^ i, pow_pos hp.pos i⟩ ⟨p ^ d, pow_pos hp.pos d⟩
      (Nat.pow_dvd_pow p hid) := by
  unfold T_ad'
  rw [dif_pos ⟨pow_pos hp.pos i, pow_pos hp.pos d, Nat.pow_dvd_pow p hid⟩]

/-- `T_ad'(1, p^k)` equals `T_ad 1 ⟨p^k, ...⟩ ...`. -/
private lemma T_ad'_one_ppow (k : ℕ) :
    T_ad' 1 (p ^ k) =
    T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) := by
  have := T_ad'_ppow p hp 0 k (Nat.zero_le k)
  simp only [pow_zero] at this
  convert this using 2 <;> exact (PNat.eq rfl).symm

/-- Key shift: `T_pp(p) * T_ad'(p^j, p^d) = T_ad'(p^{j+1}, p^{d+1})` when `j ≤ d`. -/
private lemma T_pp_mul_T_ad'_ppow (j d : ℕ) (hjd : j ≤ d) :
    T_pp p hp * T_ad' (p ^ j) (p ^ d) =
    T_ad' (p ^ (j + 1)) (p ^ (d + 1)) := by
  rw [T_ad'_ppow p hp j d hjd, T_ad'_ppow p hp (j + 1) (d + 1) (by omega)]
  unfold T_ad
  rw [T_pp_comm_T_elem p hp (mk2 ⟨p ^ j, pow_pos hp.pos j⟩ ⟨p ^ d, pow_pos hp.pos d⟩)
    (divChain_mk2 _ _ (Nat.pow_dvd_pow p hjd))]
  unfold T_pp
  rw [T_elem_mul_scalar (mk2 ⟨p ^ j, pow_pos hp.pos j⟩ ⟨p ^ d, pow_pos hp.pos d⟩)
    (divChain_mk2 _ _ (Nat.pow_dvd_pow p hjd)) ⟨p, hp.pos⟩]
  apply T_elem_congr_diag
  ext i; fin_cases i <;> simp [pnatMul, mk2, pow_succ, mul_comm]

/-- Theorem 3.24(2): `T(1, pᵏ) = T(pᵏ) − T(p,p) · T(p^{k−2})` for k ≥ 2.
    Proof strategy: T(pᵏ) = Σ T(pⁱ,p^{k-i}) and T(p,p)·T(p^{k-2}) shifts
    the index, giving a telescoping cancellation. -/
theorem thm324_2 (k : ℕ) (hk : 2 ≤ k) :
    T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) =
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    T_pp p hp * T_sum ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ := by
  -- It suffices to show T_ad(1,p^k) + T_pp * T_sum(p^{k-2}) = T_sum(p^k)
  suffices h : T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) +
      T_pp p hp * T_sum ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ =
      T_sum ⟨p ^ k, pow_pos hp.pos k⟩ by
    rw [eq_sub_iff_add_eq]; exact h
  -- Expand T_sum using prime-power expansion
  rw [T_sum_ppow_expansion p hp k, T_sum_ppow_expansion p hp (k - 2)]
  -- Distribute T_pp over the sum
  rw [Finset.mul_sum]
  -- Apply the shift lemma to each term in the multiplied sum
  have h_range_eq : (k - 2) / 2 + 1 = k / 2 := by omega
  have shift : ∀ j ∈ Finset.range ((k - 2) / 2 + 1),
      T_pp p hp * T_ad' (p ^ j) (p ^ (k - 2 - j)) =
      T_ad' (p ^ (j + 1)) (p ^ (k - (j + 1))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjk : j ≤ k - 2 - j := by omega
    have : k - 2 - j + 1 = k - (j + 1) := by omega
    rw [T_pp_mul_T_ad'_ppow p hp j (k - 2 - j) hjk]
    congr 2 <;> omega
  rw [Finset.sum_congr rfl shift]
  -- Now rewrite the range to match k/2
  rw [show Finset.range ((k - 2) / 2 + 1) = Finset.range (k / 2) from by
    simp only [show (k - 2) / 2 + 1 = k / 2 from by omega]]
  -- Rewrite T_ad using T_ad'
  rw [← T_ad'_one_ppow p hp k]
  -- Split the first sum at i=0
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero]
  -- Now both sides are: T_ad'(1, p^k) + sum = sum + T_ad'(1, p^k)
  abel

end Telescoping

/-! ### Identity 5: The key recursion -/

-- Sub-lemma A: SNF support restriction
private lemma mulSupport_pp_subset (k : ℕ) (_hk : 0 < k) (A : T' (GL_pair 2))
    (hA : A ∈ HeckeRing.mulSupport (GL_pair 2)
      (T_diag 2 (mk2 1 ⟨p, hp.pos⟩) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩)
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _)))) :
    A = T_diag 2 (mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩)
        (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _)) ∨
    A = T_diag 2 (mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩)
        (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega))) := by
  sorry

-- Sub-lemma B: Witness construction
private lemma D_out1_pp_in_mulSupport (k : ℕ) (_hk : 0 < k) :
    T_diag 2 (mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩)
      (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _)) ∈
    HeckeRing.mulSupport (GL_pair 2)
      (T_diag 2 (mk2 1 ⟨p, hp.pos⟩) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩)
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))) := by
  sorry

-- Sub-lemma C: Degree pinning (combined m'(D_out1) = 1 and m'(D_out2) = c)
set_option maxHeartbeats 800000 in
private lemma m'_values (k : ℕ) (hk : 0 < k) :
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 (mk2 1 ⟨p, hp.pos⟩) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩)
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _)))
      (T_diag 2 (mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩)
        (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _))) = 1 ∧
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 (mk2 1 ⟨p, hp.pos⟩) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩)
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _)))
      (T_diag 2 (mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩)
        (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩
          (dvd_pow_self p (by omega)))) =
      if k = 1 then ↑(p + 1) else ↑p := by
  set D1 := T_diag 2 (mk2 1 ⟨p, hp.pos⟩) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))
  set D2 := T_diag 2 (mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩)
    (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))
  set D_out1 := T_diag 2 (mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩)
    (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _))
  set D_out2 := T_diag 2 (mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩)
    (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)))
  set m1 := HeckeRing.m' (GL_pair 2) D1 D2 D_out1
  set m2 := HeckeRing.m' (GL_pair 2) D1 D2 D_out2
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have := diagonal_representative_unique 2 _ _ _ _ heq
    have := congr_fun this 0; simp only [mk2_zero] at this
    exact absurd (congr_arg PNat.val this).symm (Nat.Prime.one_lt hp).ne'
  -- Zero outside support
  have h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 → HeckeRing.m' (GL_pair 2) D1 D2 A = 0 := by
    intro A h1 h2; apply HeckeRing.m'_eq_zero_of_nmem_mulSupport
    intro hmem; exact (mulSupport_pp_subset p hp k hk A hmem).elim h1 h2
  -- Degree equation via Finsupp.sum directly
  -- Since m'(A) = 0 for A ∉ {D_out1, D_out2}, the sum reduces to two terms.
  -- Degree equation via deg ring homomorphism
  have h_deg : m1 * T'_deg (GL_pair 2) D_out1 + m2 * T'_deg (GL_pair 2) D_out2 =
      T'_deg (GL_pair 2) D1 * T'_deg (GL_pair 2) D2 := by
    -- deg(m(D1,D2)) = deg(D1) * deg(D2) since deg is a ring hom
    have h1 : HeckeRing.deg (GL_pair 2) (HeckeRing.m (GL_pair 2) D1 D2) =
        T'_deg (GL_pair 2) D1 * T'_deg (GL_pair 2) D2 := by
      rw [← HeckeRing.T_single_one_mul_T_single_one, HeckeRing.deg_mul,
          HeckeRing.deg_T_single, HeckeRing.deg_T_single]; ring
    -- deg(m(D1,D2)) = Σ_A m'(A) * deg(A)
    -- Since m'(A) = 0 for A ∉ {D_out1, D_out2}, only two terms contribute
    have h2 : HeckeRing.deg (GL_pair 2) (HeckeRing.m (GL_pair 2) D1 D2) =
        m1 * T'_deg (GL_pair 2) D_out1 + m2 * T'_deg (GL_pair 2) D_out2 := by
      sorry
    linarith
  have hm1_nn := HeckeRing.m'_nonneg (GL_pair 2) D1 D2 D_out1
  have hm2_nn := HeckeRing.m'_nonneg (GL_pair 2) D1 D2 D_out2
  have hm1_pos : 1 ≤ m1 := by
    have hne : (HeckeRing.m (GL_pair 2) D1 D2) D_out1 ≠ 0 := by
      rw [← Finsupp.mem_support_iff, HeckeRing.m_support]
      exact D_out1_pp_in_mulSupport p hp k hk
    exact Int.lt_iff_add_one_le.mp (lt_of_le_of_ne hm1_nn (Ne.symm hne))
  -- Degree values
  have hd1 : T'_deg (GL_pair 2) D1 = ↑(p + 1) := by
    have := T'_deg_T_diag_two_prime p hp (mk2 1 ⟨p, hp.pos⟩)
      (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)) 1 one_pos (by simp [mk2_one, mk2_zero, pow_one])
    simpa using this
  have hd2 : T'_deg (GL_pair 2) D2 = ↑(p ^ (k - 1) * (p + 1)) :=
    T'_deg_T_diag_two_prime p hp _ _ k hk (by show p ^ k / 1 = p ^ k; simp)
  have hd_o1 : T'_deg (GL_pair 2) D_out1 = ↑(p ^ k * (p + 1)) :=
    T'_deg_T_diag_two_prime p hp _ _ (k + 1) (by omega)
      (by show p ^ (k + 1) / 1 = p ^ (k + 1); simp)
  rw [hd1, hd2, hd_o1] at h_deg
  by_cases hk1 : k = 1
  · subst hk1; simp only [ite_true, show 1 - 1 = 0 from rfl, pow_zero, one_mul] at h_deg ⊢
    have hd_o2 : T'_deg (GL_pair 2) D_out2 = 1 := by
      apply T'_deg_T_diag_two_scalar
      show (mk2 ⟨p, hp.pos⟩ ⟨p ^ 1, pow_pos hp.pos 1⟩) 0 =
        (mk2 ⟨p, hp.pos⟩ ⟨p ^ 1, pow_pos hp.pos 1⟩) 1
      simp [mk2, pow_one]
    rw [hd_o2] at h_deg; push_cast at h_deg ⊢
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    -- h_deg : m1 * (p * (p + 1)) + m2 = (p + 1) * (p + 1)  [roughly]
    -- From m1 ≥ 1, m2 ≥ 0, p ≥ 2: m1 = 1 and m2 = p + 1
    constructor <;> sorry
  · simp only [show k ≠ 1 from hk1, ite_false]; have hk2 : 2 ≤ k := by omega
    have hd_o2 : T'_deg (GL_pair 2) D_out2 = ↑(p ^ (k - 2) * (p + 1)) :=
      T'_deg_T_diag_two_prime p hp _ _ (k - 1) (by omega)
        (by show p ^ k / p = p ^ (k - 1)
            have : p ^ k = p ^ (k - 1) * p := by
              rw [← pow_succ]; congr 1; omega
            rw [this, Nat.mul_div_cancel _ hp.pos])
    rw [hd_o2] at h_deg; push_cast at h_deg ⊢
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hpk : (0 : ℤ) < p ^ k := by positivity
    have hpk1 : (0 : ℤ) < p ^ (k - 1) := by positivity
    have hpk2 : (0 : ℤ) < p ^ (k - 2) := by positivity
    constructor <;> sorry

/-- Theorem 3.24(5): `T(p) · T(1, pᵏ) = T(1, p^{k+1}) + m · T(p, pᵏ)` -/
theorem thm324_5 (k : ℕ) (hk : 0 < k) :
    T_sum ⟨p, hp.pos⟩ *
    T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) =
    T_ad 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _) +
    (if k = 1 then (↑(p + 1) : ℤ) else (↑p : ℤ)) •
      T_ad ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩
        (dvd_pow_self p (by omega)) := by
  rw [T_sum_prime p hp]
  set D1 := T_diag 2 (mk2 1 ⟨p, hp.pos⟩) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))
  set D2 := T_diag 2 (mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩)
    (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))
  set D_out1 := T_diag 2 (mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩)
    (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _))
  set D_out2 := T_diag 2 (mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩)
    (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)))
  set c := (if k = 1 then (↑(p + 1) : ℤ) else (↑p : ℤ))
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have := diagonal_representative_unique 2 _ _ _ _ heq
    have h0 : (mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ : Fin 2 → ℕ+) 0 = 1 := rfl
    have h0' : (mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ : Fin 2 → ℕ+) 0 = ⟨p, hp.pos⟩ := rfl
    have := congr_fun this 0; rw [h0, h0'] at this
    exact absurd (congr_arg PNat.val this).symm (Nat.Prime.one_lt hp).ne'
  have h_mul : T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) *
      T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) =
      HeckeRing.m (GL_pair 2) D1 D2 :=
    HeckeRing.T_single_one_mul_T_single_one (GL_pair 2) D1 D2
  have h_rhs : T_ad 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _) +
      c • T_ad ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)) =
      Finsupp.single D_out1 1 + c • Finsupp.single D_out2 1 := rfl
  rw [h_mul, h_rhs, Finsupp.smul_single', mul_one]
  apply Finsupp.ext; intro A
  show HeckeRing.m' (GL_pair 2) D1 D2 A =
    (Finsupp.single D_out1 (1 : ℤ) + Finsupp.single D_out2 c) A
  rw [Finsupp.add_apply]
  by_cases h1 : A = D_out1
  · subst h1
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h_ne, add_zero]
    exact (m'_values p hp k hk).1
  · by_cases h2 : A = D_out2
    · subst h2
      rw [Finsupp.single_eq_of_ne (Ne.symm h_ne), Finsupp.single_eq_same, zero_add]
      exact (m'_values p hp k hk).2
    · rw [Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2, add_zero]
      apply HeckeRing.m'_eq_zero_of_nmem_mulSupport
      intro hmem
      exact (mulSupport_pp_subset p hp k hk A hmem).elim h1 h2
/-- `T_sum(1) = 1`: the sum over divisor pairs of 1 is the identity. -/
private lemma T_sum_one : T_sum 1 = (1 : HeckeAlgebra 2) := by
  show ∑ a ∈ Nat.divisors 1, T_ad' a (1 / a) = 1
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  unfold T_ad'
  rw [dif_pos ⟨one_pos, one_pos, dvd_refl 1⟩]
  exact T_ad_one_one

/-- `T_ad(p, p^k) = T_pp * T_ad(1, p^{k-1})` for `k ≥ 1`.
    Consequence of `T_pp_mul_T_ad'_ppow` with j=0. -/
private lemma T_ad_p_ppow_eq (k : ℕ) (hk : 0 < k) :
    T_ad ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)) =
    T_pp p hp * T_ad 1 ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩ (one_dvd _) := by
  have h0 := T_pp_mul_T_ad'_ppow p hp 0 (k - 1) (Nat.zero_le _)
  simp only [pow_zero, zero_add] at h0
  have hk1 : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  rw [hk1] at h0
  -- h0 : T_pp * T_ad'(1, p^{k-1}) = T_ad'(p, p^k)
  -- Need to unfold T_ad' on both sides
  rw [T_ad'_one_ppow p hp (k - 1)] at h0
  rw [T_ad'_ppow p hp 1 k (by omega)] at h0
  -- h0 : T_pp * T_ad ⟨1, ...⟩ ... = T_ad ⟨p^1, ...⟩ ...
  -- Need to convert p^1 to p and match PNat wrappers
  have h_p1 : (⟨p ^ 1, pow_pos hp.pos 1⟩ : ℕ+) = ⟨p, hp.pos⟩ := PNat.eq (pow_one p)
  -- Convert T_ad(p^1, p^k) to T_ad(p, p^k) via diagonal congr
  have h_rhs_congr : T_ad ⟨p ^ 1, pow_pos hp.pos 1⟩ ⟨p ^ k, pow_pos hp.pos k⟩
    (Nat.pow_dvd_pow p (by omega : 1 ≤ k)) =
    T_ad ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)) := by
      unfold T_ad; exact T_elem_congr_diag 2 (by ext i; fin_cases i <;> simp [mk2, pow_one]) _ _
  rw [h_rhs_congr] at h0
  exact h0.symm

/-- The prime-power recurrence: `T(p^{k+1}) = T(p) · T(pᵏ) − p · T(p,p) · T(p^{k−1})`.
    Follows from Identity 5 + Identity 2 by strong induction.
    Base cases k=1,2 are direct; k ≥ 3 uses IH at k-2. -/
-- Helper: T_pp commutes with T_ad(1,p) (used in the recurrence proof)
private lemma T_pp_comm_T_ad_one_p :
    T_pp p hp * T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) =
    T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) * T_pp p hp :=
  T_pp_comm_T_elem p hp (mk2 1 ⟨p, hp.pos⟩) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))

theorem T_sum_ppow_recurrence : ∀ k : ℕ, 0 < k →
    T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ =
    T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    (p : ℤ) • (T_pp p hp * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro hk
  -- Common helper facts
  have h_p0_pnat : (⟨p ^ 0, pow_pos hp.pos 0⟩ : ℕ+) = 1 := by
    ext; simp [pow_zero]
  have h_tsum_0 : T_sum ⟨p ^ 0, pow_pos hp.pos 0⟩ = 1 := by
    rw [h_p0_pnat]; exact T_sum_one
  have h_tad_0 : T_ad 1 ⟨p ^ 0, pow_pos hp.pos 0⟩ (one_dvd _) = 1 := by
    rw [show T_ad 1 ⟨p ^ 0, pow_pos hp.pos 0⟩ (one_dvd _) = T_ad 1 1 (one_dvd _) from
      by rw [h_p0_pnat]]
    exact T_ad_one_one
  have h_p1_tad : T_ad 1 ⟨p ^ 1, pow_pos hp.pos 1⟩ (one_dvd _) =
      T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) := by
    show T_elem 2 (mk2 1 ⟨p ^ 1, pow_pos hp.pos 1⟩) _ = T_elem 2 (mk2 1 ⟨p, hp.pos⟩) _
    exact T_elem_congr_diag 2 (by ext i; fin_cases i <;> simp [mk2, pow_one]) _ _
  -- Key identity from thm324_5 + substitutions
  have h5 := thm324_5 p hp k hk
  rw [T_ad_p_ppow_eq p hp k hk] at h5
  have h2 := thm324_2 p hp (k + 1) (by omega)
  conv at h2 => rhs; rw [show (k + 1) - 2 = k - 1 from by omega]
  rw [h2] at h5
  -- Case analysis
  match k, hk, ih with
  | 1, _, _ =>
    simp only [show (1 : ℕ) - 1 = 0 from rfl, ite_true] at h5 ⊢
    rw [h_tsum_0, h_tad_0, mul_one] at h5; rw [h_tsum_0, mul_one]
    have h_p1 : (⟨p ^ 1, pow_pos hp.pos 1⟩ : ℕ+) = ⟨p, hp.pos⟩ := by ext; simp [pow_one]
    rw [show T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ from by rw [h_p1]]
    rw [h_p1_tad] at h5
    have hp1 := T_sum_prime p hp
    rw [hp1] at h5 ⊢
    rw [show (↑(p + 1) : ℤ) • T_pp p hp = (↑p : ℤ) • T_pp p hp + T_pp p hp from by
      rw [show (↑(p + 1) : ℤ) = (↑p : ℤ) + 1 from by push_cast; ring, add_smul, one_smul]] at h5
    rw [eq_sub_iff_add_eq]; have h5' := h5; abel_nf at h5' ⊢; exact h5'.symm
  | k + 2, _, ih =>
    simp only [show k + 2 ≠ 1 from by omega, ite_false,
               show k + 2 - 1 = k + 1 from by omega] at h5 ⊢
    -- Substitute T_ad(1,p^{k+2}) via thm324_2
    have h2k := thm324_2 p hp (k + 2) (by omega)
    rw [h2k] at h5; rw [mul_sub] at h5
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.zero_add] at h5 ⊢
      rw [h_tsum_0, mul_one] at h5
      rw [h_p1_tad, T_sum_prime p hp] at h5
      have h_p1_pnat : (⟨p ^ 1, pow_pos hp.pos 1⟩ : ℕ+) = ⟨p, hp.pos⟩ := by ext; simp [pow_one]
      rw [show T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ from
        by rw [h_p1_pnat]] at h5 ⊢
      rw [T_sum_prime p hp] at h5 ⊢
      have hcomm := (T_pp_comm_T_ad_one_p p hp).symm
      rw [hcomm] at h5
      rw [sub_eq_iff_eq_add] at h5; rw [eq_sub_iff_add_eq]
      have h5' := h5; abel_nf at h5' ⊢; exact h5'.symm
    · -- k ≥ 1: use IH at k (recurrence for T_sum(p^{k+1}))
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      -- Substitute T_ad(1,p^{k+1}) via thm324_2
      have h2k1 := thm324_2 p hp (k + 1) (by omega)
      conv at h2k1 => rhs; rw [show (k + 1) - 2 = k - 1 from by omega]
      rw [h2k1] at h5
      -- Normalize k+2-2 to k in h5
      conv at h5 => lhs; rw [show k + 2 - 2 = k from by omega]
      -- h5: T_sum(p) * T_sum(p^{k+2}) - T_sum(p)*(T_pp*T_sum(p^k)) =
      --   T_sum(p^{k+3}) - T_pp*T_sum(p^{k+1}) + p•(T_pp*(T_sum(p^{k+1})-T_pp*T_sum(p^{k-1})))
      -- Step 1: Distribute T_pp * (A - B) = T_pp*A - T_pp*B inside the smul
      conv at h5 => rhs; rw [show T_pp p hp *
          (T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ -
           T_pp p hp * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) =
          T_pp p hp * T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ -
          T_pp p hp * (T_pp p hp * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩)
        from mul_sub _ _ _]
      -- Step 2: Distribute smul over subtraction
      rw [smul_sub] at h5
      -- Step 3: Rewrite T_sum(p)*(T_pp*T_sum(p^k)) via mul_assoc + commutativity
      rw [← mul_assoc (T_sum ⟨p, hp.pos⟩) (T_pp p hp)
          (T_sum ⟨p ^ k, pow_pos hp.pos k⟩)] at h5
      have hcomm : T_sum ⟨p, hp.pos⟩ * T_pp p hp =
          T_pp p hp * T_sum ⟨p, hp.pos⟩ := by
        rw [T_sum_prime p hp]; exact (T_pp_comm_T_ad_one_p p hp).symm
      rw [hcomm] at h5
      rw [mul_assoc (T_pp p hp) (T_sum ⟨p, hp.pos⟩)
          (T_sum ⟨p ^ k, pow_pos hp.pos k⟩)] at h5
      -- Step 4: Use IH at k
      have ih_k := ih k (by omega) hk_pos
      have ih_k' : T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
          T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ +
          (↑p : ℤ) • (T_pp p hp *
            T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
        rw [ih_k]; abel
      rw [ih_k'] at h5
      -- Step 5: Distribute T_pp*(A + B) = T_pp*A + T_pp*B
      rw [mul_add (T_pp p hp)] at h5
      -- Step 6: Move smul through multiplication: T_pp*(p•X) = p•(T_pp*X)
      rw [mul_smul_comm (↑p : ℤ)] at h5
      -- Step 7: Use mul_assoc for T_pp*(T_pp*X)
      rw [← mul_assoc (T_pp p hp) (T_pp p hp)] at h5
      -- Cancel matching terms from both sides of h5
      rw [sub_eq_iff_eq_add] at h5
      -- h5: A = (D - B + (E - C)) + (B + C), simplify to A = D + E by abel
      have h6 : T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩ =
          T_sum ⟨p ^ (k + 2 + 1), pow_pos hp.pos (k + 2 + 1)⟩ +
          (↑p : ℤ) • (T_pp p hp * T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩) := by
        rw [h5]; abel
      exact eq_sub_iff_add_eq.mpr h6.symm

/-! ### Identity 4: General prime-power product -/

/-- Theorem 3.24(4): `T(pʳ) · T(pˢ) = Σ_{i=0}^{r} pⁱ · T(pⁱ,pⁱ) · T(p^{r+s−2i})`
    for r ≤ s. Proved by induction on r using `T_sum_ppow_recurrence`. -/
-- Helper: T_pp commutes with T_sum(p^k).
private lemma T_pp_comm_T_sum_ppow (k : ℕ) :
    T_pp p hp * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ * T_pp p hp := by
  rw [T_sum_ppow_expansion p hp k, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  unfold T_ad'
  split
  · rename_i h
    unfold T_ad
    exact T_pp_comm_T_elem p hp _ _
  · simp [mul_zero, zero_mul]

-- Helper: T_pp^i commutes with T_sum(p^k).
private lemma T_pp_pow_comm_T_sum_ppow (i k : ℕ) :
    T_pp p hp ^ i * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ * T_pp p hp ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ']
    rw [mul_assoc, ih, ← mul_assoc]
    rw [T_pp_comm_T_sum_ppow p hp k]
    rw [mul_assoc, ← pow_succ']

-- Helper: T_sum(p) commutes with T_pp^i.
private lemma T_sum_p_comm_T_pp_pow (i : ℕ) :
    T_sum ⟨p, hp.pos⟩ * T_pp p hp ^ i =
    T_pp p hp ^ i * T_sum ⟨p, hp.pos⟩ := by
  have h1 : (⟨p ^ 1, pow_pos hp.pos 1⟩ : ℕ+) = ⟨p, hp.pos⟩ := PNat.eq (pow_one p)
  rw [show T_sum ⟨p, hp.pos⟩ = T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ from by congr 1; exact h1.symm]
  exact (T_pp_pow_comm_T_sum_ppow p hp i 1).symm

-- Helper: T_sum(p) commutes with T_pp^i * T_sum(p^k).
private lemma T_sum_p_comm_T_pp_pow_T_sum (i k : ℕ) :
    T_sum ⟨p, hp.pos⟩ * (T_pp p hp ^ i * T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
    T_pp p hp ^ i * (T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩) := by
  rw [← mul_assoc, T_sum_p_comm_T_pp_pow p hp i, mul_assoc]

set_option maxHeartbeats 800000 in
theorem thm324_4 : ∀ r s : ℕ, r ≤ s →
    T_sum ⟨p ^ r, pow_pos hp.pos r⟩ * T_sum ⟨p ^ s, pow_pos hp.pos s⟩ =
    ∑ i ∈ Finset.range (r + 1),
      (p : ℤ) ^ i •
        (T_pp p hp ^ i *
         T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro s hrs
  match r with
  | 0 =>
    rw [Finset.sum_range_one]
    simp only [Nat.zero_add, pow_zero, one_smul, one_mul]
    -- Goal: T_sum ⟨1, ...⟩ * T_sum ⟨p^s, ...⟩ = T_sum ⟨p^(s-0), ...⟩
    -- T_sum ⟨1, ...⟩ = T_sum 1 = 1
    have h1 : T_sum (⟨1, pow_pos hp.pos 0⟩ : ℕ+) = 1 := by
      rw [show (⟨1, pow_pos hp.pos 0⟩ : ℕ+) = (1 : ℕ+) from PNat.eq rfl]
      exact T_sum_one
    rw [h1, one_mul]
    show T_sum ⟨p ^ s, _⟩ = T_sum ⟨p ^ (s - 2 * 0), _⟩
    simp
  | 1 =>
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, one_smul, one_mul, pow_one]
    have hs_pos : 0 < s := by omega
    have h_rec := T_sum_ppow_recurrence p hp s hs_pos
    rw [eq_sub_iff_add_eq] at h_rec
    conv_rhs =>
      rw [show 1 + s - 2 * 0 = s + 1 from by omega,
          show 1 + s - 2 * 1 = s - 1 from by omega]
    exact h_rec.symm
  | r + 2 =>
    have h_rec := T_sum_ppow_recurrence p hp (r + 1) (by omega)
    simp only [show r + 1 - 1 = r from by omega] at h_rec
    rw [show r + 1 + 1 = r + 2 from by omega] at h_rec
    rw [h_rec, sub_mul]
    have ih1 := ih (r + 1) (by omega) s (by omega)
    have ih0 := ih r (by omega) s (by omega)
    rw [mul_assoc, ih1]
    rw [smul_mul_assoc, mul_assoc (T_pp p hp), ih0]
    -- Abbreviate for readability
    set Tp := T_sum ⟨p, hp.pos⟩ with Tp_def
    set Tpp := T_pp p hp with Tpp_def
    -- Define the sums
    set S1 := ∑ i ∈ Finset.range (r + 1 + 1),
      (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)
    set S2 := ∑ i ∈ Finset.range (r + 1),
      (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)
    -- Goal: Tp * S1 - ↑p • (Tpp * S2) = target_sum
    -- Step 1: Distribute Tp over S1
    have h_lhs1 : Tp * S1 = ∑ i ∈ Finset.range (r + 1 + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [mul_smul_comm, T_sum_p_comm_T_pp_pow_T_sum p hp i _, ← mul_assoc]
    -- Step 2: Distribute (↑p • Tpp) over S2
    have h_lhs2 : (p : ℤ) • (Tpp * S2) = ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
      rw [Finset.mul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [mul_smul_comm, smul_smul, mul_comm ((p : ℤ)) ((p : ℤ) ^ i), ← pow_succ]
      congr 1; rw [← mul_assoc, ← pow_succ']
    -- Step 3: Peel off last term from first sum
    have h_peel1 : ∑ i ∈ Finset.range (r + 1 + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
      (∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩))) +
      (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩)) :=
      Finset.sum_range_succ _ _
    -- Step 4: Apply recurrence T_sum(p)*T_sum(p^k) = T_sum(p^{k+1}) + p•Tpp*T_sum(p^{k-1})
    -- for each i in range(r+1) where k = r+1+s-2i ≥ 1
    have h_split : ∀ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
        (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩) +
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
      intro i hi; rw [Finset.mem_range] at hi
      have h_pos : 0 < r + 1 + s - 2 * i := by omega
      have h_rec_i := T_sum_ppow_recurrence p hp (r + 1 + s - 2 * i) h_pos
      rw [show (r + 1 + s - 2 * i) + 1 = r + 2 + s - 2 * i from by omega,
          show r + 1 + s - 2 * i - 1 = r + s - 2 * i from by omega] at h_rec_i
      have h_eq : Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩ =
          T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩ +
          (p : ℤ) • (Tpp * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
        rw [eq_sub_iff_add_eq] at h_rec_i; exact h_rec_i.symm
      rw [h_eq, mul_add, smul_add]
      congr 1
      rw [mul_smul_comm, smul_smul]
      rw [show (p : ℤ) ^ i * (p : ℤ) = (p : ℤ) ^ (i + 1) from by ring]
      congr 1
      rw [← mul_assoc, ← pow_succ]
    -- Step 5: Compute the first sum after splitting
    have h_sum_split :
      ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
      (∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩)) +
      (∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl h_split
    -- Step 6: Combine
    rw [h_lhs1, h_peel1, h_sum_split]
    rw [h_lhs2]
    -- Goal: (A + B + C) - B = target
    -- where A = Σ_{0..r} A_i (the "good" terms)
    --       B = Σ_{0..r} B_{i+1} (cancels with h_lhs2)
    --       C = last term at i = r+1
    -- Simplify: (A + B + C) - B = A + C
    -- (A + B + C) - B = A + C
    set A := ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩)
    set B := ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)
    set C := (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩))
    -- Need: A + B + C - B = target
    -- Simplify: (A + B) + C - B = A + C
    show A + B + C - B = _
    rw [add_assoc, add_comm B C, ← add_assoc, add_sub_cancel_right]
    -- Now LHS = Σ_{i=0}^r A_i + last_term
    -- RHS = Σ_{i=0}^{r+2} p^i • Tpp^i * T_sum(p^{r+2+s-2i})
    -- Peel off i=r+2 and i=r+1 from RHS
    rw [show r + 2 + 1 = (r + 1) + 1 + 1 from by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    -- RHS = Σ_{i=0}^r A_i + term(r+1) + term(r+2)
    -- So we need: last_term = term(r+1) + term(r+2)
    rw [add_assoc]
    congr 1
    -- C = p^{r+1} • Tpp^{r+1} * (Tp * T_sum(p^{r+1+s-2(r+1)}))
    -- Need: C = p^{r+1} • Tpp^{r+1} * T_sum(p^{r+2+s-2(r+1)})
    --         + p^{r+2} • Tpp^{r+2} * T_sum(p^{r+2+s-2(r+2)})
    -- Simplify exponents in C
    have hexp_C : r + 1 + s - 2 * (r + 1) = s - r - 1 := by omega
    have hexp1 : r + 2 + s - 2 * (r + 1) = s - r := by omega
    have hexp2 : r + 2 + s - 2 * (r + 2) = s - r - 2 := by omega
    -- Apply recurrence: Tp * T_sum(p^{s-r-1}) = T_sum(p^{s-r}) + p•Tpp*T_sum(p^{s-r-2})
    have h_sr_pos : 0 < s - r - 1 := by omega
    have h_rec_final := T_sum_ppow_recurrence p hp (s - r - 1) h_sr_pos
    rw [show (s - r - 1) + 1 = s - r from by omega,
        show s - r - 1 - 1 = s - r - 2 from by omega] at h_rec_final
    have h_expand : Tp * T_sum ⟨p ^ (s - r - 1), pow_pos hp.pos _⟩ =
        T_sum ⟨p ^ (s - r), pow_pos hp.pos _⟩ +
        (p : ℤ) • (Tpp * T_sum ⟨p ^ (s - r - 2), pow_pos hp.pos _⟩) := by
      rw [eq_sub_iff_add_eq] at h_rec_final; exact h_rec_final.symm
    -- Unfold C
    -- C = p^{r+1} • Tpp^{r+1} * (Tp * T_sum(p^{r+1+s-2(r+1)}))
    -- Use hexp_C to simplify exponent in T_sum argument, then h_expand to split
    -- Goal: C = p^{r+1} • Tpp^{r+1} * T_sum(p^{s-r})
    --         + p^{r+2} • Tpp^{r+2} * T_sum(p^{s-r-2})
    -- with exponents in RHS as r+2+s-2*(r+1) and r+2+s-2*(r+2)
    -- Unfold C via rfl (avoids whnf timeout from show)
    have hC_def : C = (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) *
        (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩)) := rfl
    rw [hC_def, hexp_C, h_expand, mul_add, smul_add, mul_smul_comm, smul_smul,
        show (p : ℤ) ^ (r + 1) * (p : ℤ) = (p : ℤ) ^ (r + 2) from by ring,
        ← mul_assoc, show Tpp ^ (r + 1) * Tpp = Tpp ^ (r + 2) from (pow_succ Tpp (r + 1)).symm]
    -- Match PNat exponents via congr_arg (avoids heavy whnf from congr/convert)
    have hnat2 : s - r - 2 = r + 2 + s - 2 * (r + 2) := by omega
    have hnat1 : s - r = r + 2 + s - 2 * (r + 1) := by omega
    rw [hnat2, hnat1]

/-! ### Identity 3: General multiplicativity -/

section CoprimeMultiplicativity

open Finset in
/-- `diagDet 2 (mk2 a d) = a * d`. -/
private lemma diagDet_mk2 (a d : ℕ+) :
    diagDet 2 (mk2 a d) = a * d := by
  simp [diagDet, Fin.prod_univ_two, mk2]

/-- For coprime divisor pairs, the `T_ad'` product equals `T_ad'` of the products. -/
private lemma T_ad'_mul_of_coprime (a b da db : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hda : 0 < da) (hdb : 0 < db)
    (hdva : a ∣ da) (hdvb : b ∣ db)
    (hcop : Nat.Coprime (a * da) (b * db)) :
    T_ad' a da * T_ad' b db = T_ad' (a * b) (da * db) := by
  -- Unfold T_ad' for the inputs
  have lhs_a : T_ad' a da = T_ad ⟨a, ha⟩ ⟨da, hda⟩ hdva := by
    unfold T_ad'; rw [dif_pos ⟨ha, hda, hdva⟩]
  have lhs_b : T_ad' b db = T_ad ⟨b, hb⟩ ⟨db, hdb⟩ hdvb := by
    unfold T_ad'; rw [dif_pos ⟨hb, hdb, hdvb⟩]
  have hab_pos : 0 < a * b := Nat.mul_pos ha hb
  have dab_pos : 0 < da * db := Nat.mul_pos hda hdb
  have hdvab : a * b ∣ da * db := Nat.mul_dvd_mul hdva hdvb
  have rhs : T_ad' (a * b) (da * db) = T_ad ⟨a * b, hab_pos⟩ ⟨da * db, dab_pos⟩ hdvab := by
    unfold T_ad'; rw [dif_pos ⟨hab_pos, dab_pos, hdvab⟩]
  rw [lhs_a, lhs_b, rhs]
  -- Now use T_diag_mul_coprime from GLn/CoprimeMul.lean
  unfold T_ad
  rw [T_diag_mul_coprime 2 (mk2 ⟨a, ha⟩ ⟨da, hda⟩) (mk2 ⟨b, hb⟩ ⟨db, hdb⟩)
    (divChain_mk2 _ _ hdva) (divChain_mk2 _ _ hdvb)
    (by rw [diagDet_mk2, diagDet_mk2]; exact hcop)]
  apply T_elem_congr_diag
  ext i; fin_cases i <;> simp [pnatMul, mk2]

/-- When `T_ad'` conditions fail, the product is zero and so is the RHS. -/
private lemma T_ad'_mul_zero_of_not_dvd (a da : ℕ) (h : ¬(0 < a ∧ 0 < da ∧ a ∣ da)) (x : HeckeAlgebra 2) :
    T_ad' a da * x = 0 := by
  have : T_ad' a da = 0 := by unfold T_ad'; rw [dif_neg h]
  rw [this, zero_mul]

private lemma T_ad'_mul_zero_of_not_dvd' (b db : ℕ) (h : ¬(0 < b ∧ 0 < db ∧ b ∣ db)) (x : HeckeAlgebra 2) :
    x * T_ad' b db = 0 := by
  have : T_ad' b db = 0 := by unfold T_ad'; rw [dif_neg h]
  rw [this, mul_zero]

/-- The map `(a, b) ↦ a * b` from `m.divisors ×ˢ n.divisors` to `(m*n).divisors`
    is injective when `m` and `n` are coprime. -/
private lemma mul_injOn_coprime_divisors (m n : ℕ) (hcop : Nat.Coprime m n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (↑(m.divisors ×ˢ n.divisors)) := by
  intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
  simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors] at h₁ h₂
  simp only at heq
  have ha₁ : a₁ ∣ m := h₁.1.1
  have hb₁ : b₁ ∣ n := h₁.2.1
  have ha₂ : a₂ ∣ m := h₂.1.1
  have hb₂ : b₂ ∣ n := h₂.2.1
  -- a₁ is coprime to b₁ (and similarly a₂ to b₂)
  have hcop₁₂ : Nat.Coprime a₁ b₂ :=
    Nat.Coprime.coprime_dvd_left ha₁ (Nat.Coprime.coprime_dvd_right hb₂ hcop)
  have hcop₂₁ : Nat.Coprime a₂ b₁ :=
    Nat.Coprime.coprime_dvd_left ha₂ (Nat.Coprime.coprime_dvd_right hb₁ hcop)
  -- From a₁ * b₁ = a₂ * b₂ and coprimality, deduce a₁ = a₂ and b₁ = b₂
  -- a₁ | a₂ * b₂ and coprime(a₁, b₂) => a₁ | a₂
  have ha₁_dvd_a₂ : a₁ ∣ a₂ := by
    have : a₁ ∣ a₂ * b₂ := heq ▸ dvd_mul_right a₁ b₁
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop₁₂ this)
  -- a₂ | a₁ * b₁ and coprime(a₂, b₁) => a₂ | a₁
  have ha₂_dvd_a₁ : a₂ ∣ a₁ := by
    have : a₂ ∣ a₁ * b₁ := heq ▸ dvd_mul_right a₂ b₂
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop₂₁ this)
  have haeq : a₁ = a₂ := Nat.dvd_antisymm ha₁_dvd_a₂ ha₂_dvd_a₁
  have ha_pos : 0 < a₁ := Nat.pos_of_ne_zero (fun h => by simp [h] at ha₁; exact h₁.1.2 ha₁)
  have hbeq : b₁ = b₂ := Nat.eq_of_mul_eq_mul_left ha_pos (haeq ▸ heq)
  exact Prod.ext haeq hbeq

/-- Coprime multiplicativity: `T(m) · T(n) = T(mn)` when `gcd(m,n) = 1`. -/
theorem T_sum_mul_coprime (m n : ℕ+) (hcop : Nat.Coprime m n) :
    T_sum m * T_sum n = T_sum ⟨m * n, Nat.mul_pos m.pos n.pos⟩ := by
  open scoped Pointwise in
  -- Unfold T_sum on both sides
  -- LHS = (∑ a ∈ m.divisors, T_ad'(a, m/a)) * (∑ b ∈ n.divisors, T_ad'(b, n/b))
  -- RHS = ∑ c ∈ (mn).divisors, T_ad'(c, mn/c)
  -- Suffices to prove at the level of the underlying sums
  set M := (m : ℕ) with hM
  set N := (n : ℕ) with hN
  -- T_sum m = ∑ a ∈ M.divisors, T_ad' a (M / a)
  -- T_sum n = ∑ b ∈ N.divisors, T_ad' b (N / b)
  -- T_sum ⟨M*N, _⟩ = ∑ c ∈ (M*N).divisors, T_ad' c ((M*N) / c)
  change (∑ a ∈ M.divisors, T_ad' a (M / a)) * (∑ b ∈ N.divisors, T_ad' b (N / b)) =
    ∑ c ∈ (M * N).divisors, T_ad' c ((M * N) / c)
  -- Distribute the product of sums
  rw [Finset.sum_mul_sum]
  -- Rewrite divisors of M*N using Nat.divisors_mul
  open scoped Pointwise in
  rw [Nat.divisors_mul]
  -- Now RHS sums over (M.divisors * N.divisors) which is Finset.image₂ (· * ·)
  open scoped Pointwise in
  rw [show (Nat.divisors M * Nat.divisors N) =
    (Nat.divisors M ×ˢ Nat.divisors N).image (fun p => p.1 * p.2) from rfl]
  rw [Finset.sum_image (mul_injOn_coprime_divisors M N hcop)]
  -- Now both sides sum over M.divisors ×ˢ N.divisors
  -- LHS: ∑ a ∈ M.divisors, ∑ b ∈ N.divisors, T_ad' a (M/a) * T_ad' b (N/b)
  -- RHS: ∑ x ∈ M.divisors ×ˢ N.divisors, T_ad' (x.1*x.2) ((M*N)/(x.1*x.2))
  -- Rewrite LHS using Finset.sum_product'
  rw [← Finset.sum_product']
  -- Now both sides are ∑ x ∈ M.divisors ×ˢ N.divisors, ...
  apply Finset.sum_congr rfl
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_product, Nat.mem_divisors] at hab
  have ha_dvd := hab.1.1
  have hb_dvd := hab.2.1
  have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => by simp [h] at hab)
  have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h => by simp [h] at hab)
  -- Show (M * N) / (a * b) = (M / a) * (N / b)
  have hdiv_eq : (M * N) / (a * b) = M / a * (N / b) :=
    (Nat.div_mul_div_comm ha_dvd hb_dvd).symm
  rw [hdiv_eq]
  -- Now apply the coprime T_ad' multiplication lemma
  by_cases hca : a ∣ (M / a)
  · by_cases hcb : b ∣ (N / b)
    · apply T_ad'_mul_of_coprime a b (M / a) (N / b) ha_pos hb_pos
        (Nat.div_pos (Nat.le_of_dvd (by omega) ha_dvd) ha_pos)
        (Nat.div_pos (Nat.le_of_dvd (by omega) hb_dvd) hb_pos)
        hca hcb
      -- Coprimality: a * (M/a) = M and b * (N/b) = N
      rwa [hM, hN, Nat.mul_div_cancel' ha_dvd, Nat.mul_div_cancel' hb_dvd]
    · -- T_ad'(b, N/b) = 0
      rw [T_ad'_mul_zero_of_not_dvd' b (N / b)
        (by push_neg; intro _ _; exact hcb) (T_ad' a (M / a))]
      -- T_ad'(a*b, (M/a)*(N/b)) = 0 since a*b does not divide (M/a)*(N/b)
      symm; unfold T_ad'; rw [dif_neg]; push_neg
      intro _ _; intro hdvd; apply hcb
      -- hdvd : a * b ∣ M / a * (N / b)
      -- b | a * b | (M/a) * (N/b), and Coprime(b, M/a) => b | N/b
      have hb_dvd_prod : b ∣ M / a * (N / b) := dvd_trans (dvd_mul_left b a) hdvd
      have hcop_b_ma : Nat.Coprime b (M / a) :=
        Nat.Coprime.coprime_dvd_left hb_dvd (hcop.symm.coprime_dvd_right (Nat.div_dvd_of_dvd ha_dvd))
      exact hcop_b_ma.dvd_of_dvd_mul_left hb_dvd_prod
  · -- T_ad'(a, M/a) = 0
    rw [T_ad'_mul_zero_of_not_dvd a (M / a)
      (by push_neg; intro _ _; exact hca)]
    symm; unfold T_ad'; rw [dif_neg]; push_neg
    intro _ _; intro hdvd; apply hca
    -- hdvd : a * b ∣ M / a * (N / b)
    -- a | a * b | (M/a) * (N/b), and Coprime(a, N/b) => a | M/a
    have ha_dvd_prod : a ∣ M / a * (N / b) := dvd_trans (dvd_mul_right a b) hdvd
    have hcop_a_nb : Nat.Coprime a (N / b) :=
      Nat.Coprime.coprime_dvd_left ha_dvd (hcop.coprime_dvd_right (Nat.div_dvd_of_dvd hb_dvd))
    exact hcop_a_nb.dvd_of_dvd_mul_right ha_dvd_prod

end CoprimeMultiplicativity

/-- T_sum extended to ℕ: agrees with `T_sum` for positive arguments, zero for 0. -/
private noncomputable def T_sum_nat (k : ℕ) : HeckeAlgebra 2 :=
  ∑ a ∈ k.divisors, T_ad' a (k / a)

private lemma T_sum_nat_eq (k : ℕ+) : T_sum_nat (k : ℕ) = T_sum k := rfl

/-- Theorem 3.24(3): `T(m) · T(n) = Σ_{d∣gcd(m,n)} d · T(d,d) · T(mn/d²)`.
    From Identity 4 at each prime + coprime multiplicativity. -/
theorem thm324_3 (m n : ℕ+) :
    T_sum m * T_sum n =
    ∑ d ∈ (Nat.gcd m n).divisors,
      (d : ℤ) • (T_ad' d d * T_sum_nat (↑m * ↑n / (d * d))) := by
  sorry

/-! ### Identity 6: Degree formulas (wrapping existing results) -/

/-- Theorem 3.24(6): `deg(T(pⁱ, p^{i+k})) = p^{k-1}(p+1)` for k > 0. -/
theorem thm324_6 (i k : ℕ) (hk : 0 < k) :
    T'_deg (GL_pair 2) (T_diag 2 (mk2 ⟨p ^ i, pow_pos hp.pos i⟩
      ⟨p ^ (i + k), pow_pos hp.pos (i + k)⟩)
      (divChain_mk2 _ _ (Nat.pow_dvd_pow p (by omega)))) =
    ↑(p ^ (k - 1) * (p + 1)) := by
  exact T'_deg_T_diag_two_prime p hp _ _ k hk (by
    change p ^ (i + k) / p ^ i = p ^ k
    rw [Nat.pow_div (by omega) hp.pos]; congr 1; omega)

/-- Scalar case: `deg(T(c, c)) = 1`. -/
theorem thm324_6_scalar (c : ℕ+) :
    T'_deg (GL_pair 2) (T_diag 2 (fun _ => c) (divChain_const 2 c)) = 1 :=
  T'_deg_T_diag_two_scalar (fun _ => c) (divChain_const 2 c) rfl

/-! ### Identity 7: Degree of T(m) -/

/-- The divisor sum function σ₁(m) = Σ_{d∣m} d. -/
noncomputable def sigma1 (m : ℕ+) : ℕ := ∑ d ∈ (m : ℕ).divisors, d

/-- `deg` of a `T_ad` equals the `T'_deg` of its underlying double coset. -/
private lemma deg_T_ad' (a d : ℕ+) (h : (a : ℕ) ∣ (d : ℕ)) :
    deg (GL_pair 2) (T_ad a d h) =
    T'_deg (GL_pair 2) (T_diag 2 (mk2 a d) (divChain_mk2 a d h)) := by
  show deg (GL_pair 2) (Finsupp.single (T_diag 2 (mk2 a d) (divChain_mk2 a d h)) 1) = _
  rw [HeckeRing.deg_T_single]; ring

/-- `deg` of `T_ad'` when conditions hold. -/
private lemma deg_T_ad'_of_pos' (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (hdvd : a ∣ d) :
    deg (GL_pair 2) (T_ad' a d) =
    deg (GL_pair 2) (T_ad ⟨a, ha⟩ ⟨d, hd⟩ hdvd) := by
  unfold T_ad'; rw [dif_pos ⟨ha, hd, hdvd⟩]

include hp in
/-- Non-scalar case: `deg(T_ad'(pⁱ, p^{k-i})) = p^{k-2i-1}(p+1)` when `2i < k`. -/
private lemma deg_ppow_term_lt' (i k : ℕ) (h2i : 2 * i < k) :
    deg (GL_pair 2) (T_ad' (p ^ i) (p ^ (k - i))) =
    ↑(p ^ (k - 2 * i - 1) * (p + 1)) := by
  have h_exp_eq : k - i = i + (k - 2 * i) := by omega
  rw [deg_T_ad'_of_pos' _ _ (pow_pos hp.pos i) (pow_pos hp.pos (k - i))
    (Nat.pow_dvd_pow p (by omega)), deg_T_ad']
  show T'_deg (GL_pair 2) (T_diag 2 (mk2 ⟨p ^ i, pow_pos hp.pos i⟩ ⟨p ^ (k - i), pow_pos hp.pos (k - i)⟩)
    (divChain_mk2 _ _ (Nat.pow_dvd_pow p (by omega)))) = ↑(p ^ (k - 2 * i - 1) * (p + 1))
  have h_mk2_eq : mk2 ⟨p ^ i, pow_pos hp.pos i⟩ ⟨p ^ (k - i), pow_pos hp.pos (k - i)⟩ =
      mk2 ⟨p ^ i, pow_pos hp.pos i⟩ ⟨p ^ (i + (k - 2 * i)), pow_pos hp.pos (i + (k - 2 * i))⟩ := by
    ext j; fin_cases j <;> simp only [mk2, h_exp_eq]
  simp only [h_mk2_eq]
  exact thm324_6 p hp i (k - 2 * i) (by omega)

include hp in
/-- Scalar case: `deg(T_ad'(p^i, p^i)) = 1` when `2i = k`. -/
private lemma deg_ppow_term_eq' (i k : ℕ) (h2i : 2 * i = k) :
    deg (GL_pair 2) (T_ad' (p ^ i) (p ^ (k - i))) = 1 := by
  have hki : k - i = i := by omega
  rw [hki, deg_T_ad'_of_pos' _ _ (pow_pos hp.pos i) (pow_pos hp.pos i) (dvd_refl _), deg_T_ad']
  set c : ℕ+ := ⟨p ^ i, pow_pos hp.pos i⟩
  show T'_deg (GL_pair 2) (T_diag 2 (mk2 c c) (divChain_mk2 c c (dvd_refl _))) = 1
  have hmk2 : mk2 c c = (fun (_ : Fin 2) => c) := funext fun j => by fin_cases j <;> rfl
  have h_diag_eq : T_diag 2 (mk2 c c) (divChain_mk2 c c (dvd_refl _)) =
      T_diag 2 (fun _ => c) (divChain_const 2 c) := by simp [hmk2]
  rw [h_diag_eq]
  exact thm324_6_scalar c

include hp in
/-- For i in the shifted tail, degree of the (k+2)-expansion term equals the k-expansion term.
    Key fact: both have the same "gap" (ratio d/a), so their degrees coincide. -/
private lemma deg_ppow_shift' (i k : ℕ) (hi : i < k / 2 + 1) :
    deg (GL_pair 2) (T_ad' (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
    deg (GL_pair 2) (T_ad' (p ^ i) (p ^ (k - i))) := by
  by_cases h2i : 2 * i < k
  · -- Non-scalar for both
    have h_deg_lhs := deg_ppow_term_lt' p hp (i + 1) (k + 2) (by omega)
    have h_deg_rhs := deg_ppow_term_lt' p hp i k h2i
    have h_exp_eq : k + 2 - 2 * (i + 1) - 1 = k - 2 * i - 1 := by omega
    rw [h_deg_lhs, h_exp_eq, h_deg_rhs.symm]
  · -- Scalar for both: 2i = k, 2(i+1) = k+2
    have h2i_eq : 2 * i = k := by omega
    have h_deg_lhs := deg_ppow_term_eq' p hp (i + 1) (k + 2) (by omega)
    have h_deg_rhs := deg_ppow_term_eq' p hp i k h2i_eq
    rw [h_deg_lhs, h_deg_rhs]

/-- `deg(T(pᵏ)) = 1 + p + ⋯ + pᵏ`.
    Proof by strong induction: for k >= 2, split the expansion at i=0 to get
    `deg = p^{k-1}(p+1) + deg_tail`, where the tail's degree equals `deg(T_sum(p^{k-2}))`
    by a shift argument (the degree of `T_ad'(p^{i+1}, p^{k-i-1})` equals that of
    `T_ad'(p^i, p^{k-2-i})` since both have the same diagonal ratio). -/
theorem deg_T_sum_prime_pow (k : ℕ) :
    deg (GL_pair 2) (T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
    ∑ j ∈ Finset.range (k + 1), (p : ℤ) ^ j := by
  induction k using Nat.strongRecOn with
  | _ k ih =>
  -- Rewrite T_sum using the prime-power expansion
  rw [T_sum_ppow_expansion p hp k, map_sum]
  match k with
  | 0 =>
    -- k=0: single term T_ad'(p^0, p^0), deg = 1
    simp only [Nat.zero_div, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    -- Goal has T_ad'(p^0)(p^0) which simp normalizes; use helper via have
    have h0 := deg_ppow_term_eq' p hp 0 0 rfl
    simp only [pow_zero, Nat.sub_zero] at h0
    exact h0
  | 1 =>
    -- k=1: single term T_ad'(p^0, p^1), deg = p+1
    simp only [show (1 : ℕ) / 2 = 0 from rfl, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    -- Use convert since simp may normalize T_ad' arguments differently
    convert deg_ppow_term_lt' p hp 0 1 (by omega) using 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    push_cast; ring
  | k + 2 =>
    -- Inductive step: k+2 from k
    have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
    rw [hdiv, Finset.sum_range_succ']
    -- After sum_range_succ', we have [tail] + [i=0 term]
    -- where tail has indices in range(k/2+1) and i=0 term is T_ad'(p^0, p^(k+2))
    -- Apply shift to tail to match ih_k's indices
    have h_tail : ∑ i ∈ Finset.range (k / 2 + 1),
        (deg (GL_pair 2)) (T_ad' (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
        ∑ i ∈ Finset.range (k / 2 + 1), (deg (GL_pair 2)) (T_ad' (p ^ i) (p ^ (k - i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      exact deg_ppow_shift' p hp i k hi
    -- Compute the i=0 term using deg_ppow_term_lt'
    have h_i0 : deg (GL_pair 2) (T_ad' (p ^ 0) (p ^ (k + 2 - 0))) =
        ↑(p ^ (k + 1) * (p + 1)) := by
      have h_raw := deg_ppow_term_lt' p hp 0 (k + 2) (by omega)
      have : k + 2 - 0 - 1 = k + 1 := by omega
      simp only [this] at h_raw
      exact h_raw
    rw [h_tail, h_i0]
    -- Now ih_k gives us the sum part
    have ih_k := ih k (by omega)
    rw [T_sum_ppow_expansion p hp k, map_sum] at ih_k
    simp only [Nat.zero_div, Nat.zero_add] at ih_k
    rw [ih_k]
    -- Algebra: p^{k+1}*(p+1) + ∑_{j=0}^{k} p^j = ∑_{j=0}^{k+2} p^j
    -- Unfold ∑ range(k+2+1) by peeling off the top two terms on the RHS only
    conv_rhs =>
      rw [show k + 2 + 1 = (k + 1 + 1) + 1 from by omega]
      rw [Finset.sum_range_succ]
      rw [show k + 1 + 1 = (k + 1) + 1 from by omega]
      rw [Finset.sum_range_succ]
    -- Now RHS = p^(k+1+1) + (p^(k+1) + ∑ range(k+1))
    -- LHS = ↑(p^(k+1)*(p+1)) + ∑ range(k+1)
    push_cast; ring
/-- `deg(T_sum(1)) = 1`, used as base case for thm324_7. -/
private lemma deg_T_sum_one : deg (GL_pair 2) (T_sum 1) = 1 := by
  change deg (GL_pair 2) (∑ a ∈ Nat.divisors 1, T_ad' a (1 / a)) = 1
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  rw [deg_T_ad'_of_pos' 1 1 one_pos one_pos (dvd_refl 1), deg_T_ad']
  set c : ℕ+ := ⟨1, one_pos⟩
  show T'_deg (GL_pair 2) (T_diag 2 (mk2 c c) (divChain_mk2 c c (dvd_refl _))) = 1
  have hmk2 : mk2 c c = (fun (_ : Fin 2) => c) := funext fun j => by fin_cases j <;> rfl
  have h_diag_eq : T_diag 2 (mk2 c c) (divChain_mk2 c c (dvd_refl _)) =
      T_diag 2 (fun _ => c) (divChain_const 2 c) := by simp [hmk2]
  rw [h_diag_eq]
  exact thm324_6_scalar c

/-- Theorem 3.24(7): `deg(T(m)) = σ₁(m)`.
    By prime factorization + coprime multiplicativity + prime-power case. -/
theorem thm324_7 (m : ℕ+) :
    deg (GL_pair 2) (T_sum m) = sigma1 m := by
  obtain ⟨n, hn⟩ := m
  revert hn
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => intro h; omega
  | one =>
    intro hn
    rw [show (⟨1, hn⟩ : ℕ+) = (1 : ℕ+) from rfl, deg_T_sum_one]
    simp [sigma1, Nat.divisors_one]
  | @prime_pow p k hp hk =>
    intro hn
    rw [deg_T_sum_prime_pow p hp k]
    simp only [sigma1]
    have h := @Nat.sum_divisors_prime_pow ℕ _ k p id hp
    simp only [id] at h
    exact_mod_cast h.symm
  | @coprime a b ha hb hcop iha ihb =>
    intro hn
    have ha_pos : 0 < a := by omega
    have hb_pos : 0 < b := by omega
    rw [show T_sum ⟨a * b, hn⟩ = T_sum ⟨a, ha_pos⟩ * T_sum ⟨b, hb_pos⟩ from
      (T_sum_mul_coprime ⟨a, ha_pos⟩ ⟨b, hb_pos⟩ hcop).symm]
    rw [map_mul, iha ha_pos, ihb hb_pos]
    simp only [sigma1]
    exact_mod_cast (Nat.Coprime.sum_divisors_mul hcop).symm

end HeckeRing.GL2
