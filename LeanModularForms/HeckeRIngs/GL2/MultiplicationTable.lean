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
open scoped ArithmeticFunction.sigma

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
  convert this using 2

/-- Key shift: `T_pp(p) * T_ad'(p^j, p^d) = T_ad'(p^{j+1}, p^{d+1})` when `j ≤ d`. -/
private lemma T_pp_mul_T_ad'_ppow (j d : ℕ) (hjd : j ≤ d) :
    T_pp p hp * T_ad' (p ^ j) (p ^ d) =
    T_ad' (p ^ (j + 1)) (p ^ (d + 1)) := by
  rw [T_ad'_ppow p hp j d hjd, T_ad'_ppow p hp (j + 1) (d + 1) (by omega)]
  unfold T_ad
  rw [T_pp_comm_T_elem p hp (![⟨p ^ j, pow_pos hp.pos j⟩, ⟨p ^ d, pow_pos hp.pos d⟩])
    (divChain_mk2 _ _ (Nat.pow_dvd_pow p hjd))]
  unfold T_pp
  rw [T_elem_mul_scalar (![⟨p ^ j, pow_pos hp.pos j⟩, ⟨p ^ d, pow_pos hp.pos d⟩])
    (divChain_mk2 _ _ (Nat.pow_dvd_pow p hjd)) ⟨p, hp.pos⟩]
  apply T_elem_congr_diag
  ext i; fin_cases i <;> simp [pnatMul, pow_succ, mul_comm]

/-- Theorem 3.24(2): `T(1, pᵏ) = T(pᵏ) − T(p,p) · T(p^{k−2})` for k ≥ 2.
    Proof strategy: T(pᵏ) = Σ T(pⁱ,p^{k-i}) and T(p,p)·T(p^{k-2}) shifts
    the index, giving a telescoping cancellation. -/
theorem thm324_2 (k : ℕ) (hk : 2 ≤ k) :
    T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) =
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    T_pp p hp * T_sum ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ := by
  suffices h : T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) +
      T_pp p hp * T_sum ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ =
      T_sum ⟨p ^ k, pow_pos hp.pos k⟩ by
    rw [eq_sub_iff_add_eq]; exact h
  rw [T_sum_ppow_expansion p hp k, T_sum_ppow_expansion p hp (k - 2), Finset.mul_sum]
  have h_range_eq : (k - 2) / 2 + 1 = k / 2 := by omega
  have shift : ∀ j ∈ Finset.range ((k - 2) / 2 + 1),
      T_pp p hp * T_ad' (p ^ j) (p ^ (k - 2 - j)) =
      T_ad' (p ^ (j + 1)) (p ^ (k - (j + 1))) := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hjk : j ≤ k - 2 - j := by omega
    have : k - 2 - j + 1 = k - (j + 1) := by omega
    rw [T_pp_mul_T_ad'_ppow p hp j (k - 2 - j) hjk, this]
  rw [Finset.sum_congr rfl shift]
  rw [show Finset.range ((k - 2) / 2 + 1) = Finset.range (k / 2) from by
    simp only [show (k - 2) / 2 + 1 = k / 2 from by omega]]
  rw [← T_ad'_one_ppow p hp k, Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero]
  abel

end Telescoping

/-! ### Identity 5: The key recursion -/

private lemma first_invariant_dvd_p_of_product
    (S : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (a : Fin 2 → ℕ+) (hdiv : DivChain 2 a)
    (L R : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (k : ℕ) (_hk : 0 < k)
    (heq : (L : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.diagonal (fun m => ((![1, ⟨p, hp.pos⟩] : Fin 2 → ℕ+) m : ℤ)) *
      (S : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.diagonal (fun m => ((![1, ⟨p ^ k, pow_pos hp.pos k⟩] : Fin 2 → ℕ+) m : ℤ)) *
      (R : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.diagonal (fun i => (a i : ℤ))) :
    (a 0 : ℕ) ∣ p := by
  set dp := Matrix.diagonal (fun m => ((![1, ⟨p, hp.pos⟩] : Fin 2 → ℕ+) m : ℤ))
  set dpk := Matrix.diagonal (fun m => ((![1, ⟨p ^ k, pow_pos hp.pos k⟩] : Fin 2 → ℕ+) m : ℤ))
  set S_ℤ := (↑S : Matrix (Fin 2) (Fin 2) ℤ)
  set M := dp * S_ℤ * dpk
  set L_ℤ := (↑L : Matrix (Fin 2) (Fin 2) ℤ)
  set R_ℤ := (↑R : Matrix (Fin 2) (Fin 2) ℤ)
  have hLadj : L_ℤ.adjugate * L_ℤ = 1 := by rw [Matrix.adjugate_mul, L.prop, one_smul]
  have hRadj : R_ℤ * R_ℤ.adjugate = 1 := by rw [Matrix.mul_adjugate, R.prop, one_smul]
  have heq_LMR : L_ℤ * M * R_ℤ = Matrix.diagonal (fun i => (a i : ℤ)) := by
    have : L_ℤ * M * R_ℤ = L_ℤ * dp * S_ℤ * dpk * R_ℤ := by
      ext i j; simp only [M, S_ℤ, Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [this]; exact heq
  have hM_eq : M = L_ℤ.adjugate * Matrix.diagonal (fun i => (a i : ℤ)) * R_ℤ.adjugate := by
    ext i j
    have h1 := congr_arg (L_ℤ.adjugate * · * R_ℤ.adjugate) heq_LMR; simp only at h1
    have h2 : L_ℤ.adjugate * (L_ℤ * M * R_ℤ) * R_ℤ.adjugate = M := by
      have : L_ℤ.adjugate * (L_ℤ * M * R_ℤ) * R_ℤ.adjugate =
          (L_ℤ.adjugate * L_ℤ) * M * (R_ℤ * R_ℤ.adjugate) := by
        ext r s; simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
      rw [this, hLadj, hRadj, one_mul, mul_one]
    exact congr_arg (· i j) (h2 ▸ h1)
  have h_dvd_entry : ∀ i j : Fin 2, (a 0 : ℤ) ∣ M i j := by
    intro i j; rw [hM_eq]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply dvd_add
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
        (show (a 0 : ℤ) ∣ (a 1 : ℤ) from by exact_mod_cast hdiv 0 (by omega)) _) _
  have hfin10 : (1 : Fin 2) ≠ 0 := by decide
  have hfin01 : (0 : Fin 2) ≠ 1 := by decide
  have h_M00 : M 0 0 = S_ℤ 0 0 := by
    simp only [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hfin10, if_false, if_true,
      mul_zero, add_zero, Matrix.cons_val_fin_one]; norm_num
  have h_M10 : M 1 0 = (p : ℤ) * S_ℤ 1 0 := by
    simp only [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.diagonal_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hfin10, if_false, if_true,
      mul_zero, zero_mul, add_zero, Matrix.cons_val_fin_one]; norm_num
  have h_cop : IsCoprime (S_ℤ 0 0) (S_ℤ 1 0) :=
    ⟨S.val 1 1, -(S.val 0 1), by
      have := S.prop; rw [Matrix.det_fin_two] at this; linarith⟩
  have h1 : (a 0 : ℤ) ∣ S_ℤ 0 0 := h_M00 ▸ h_dvd_entry 0 0
  have h2 : (a 0 : ℤ) ∣ (p : ℤ) * S_ℤ 1 0 := h_M10 ▸ h_dvd_entry 1 0
  have h_cop2 : IsCoprime (↑(a 0) : ℤ) (S_ℤ 1 0) := by
    obtain ⟨u, v, huv⟩ := h_cop; obtain ⟨t, ht⟩ := h1
    exact ⟨u * t, v, by
      rw [show u * t * ↑(a 0) = u * (↑(a 0) * t) from by ring, ← ht]; exact huv⟩
  exact_mod_cast h_cop2.dvd_of_dvd_mul_right h2

private lemma mulSupport_pp_det_eq (k : ℕ) (a : Fin 2 → ℕ+)
    (g₁ g₂ g₃ g₄ : GL (Fin 2) ℚ)
    (h1 : (↑g₁ : Matrix (Fin 2) (Fin 2) ℚ).det = 1)
    (h2 : (↑g₂ : Matrix (Fin 2) (Fin 2) ℚ).det = (p : ℚ))
    (h3 : (↑g₃ : Matrix (Fin 2) (Fin 2) ℚ).det = 1)
    (h4 : (↑g₄ : Matrix (Fin 2) (Fin 2) ℚ).det = (p : ℚ) ^ k)
    (SL_La SL_Ra : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_eq : g₁ * g₂ * (g₃ * g₄) =
        SLnZ_to_GLnQ 2 SL_La * diagMat 2 a * SLnZ_to_GLnQ 2 SL_Ra) :
    (a 0 : ℕ) * (a 1 : ℕ) = p ^ (k + 1) := by
  have h_lhs : (↑(g₁ * g₂ * (g₃ * g₄)) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (p : ℚ) ^ (k + 1) := by
    simp only [Units.val_mul, Matrix.det_mul, h1, h2, h3, h4]; ring
  have h_rhs : (↑(g₁ * g₂ * (g₃ * g₄)) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (a 0 : ℚ) * (a 1 : ℚ) := by
    rw [h_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      SLnZ_to_GLnQ_det, SLnZ_to_GLnQ_det, diagMat_det]; simp [Fin.prod_univ_two]
  exact_mod_cast show (a 0 : ℚ) * (a 1 : ℚ) = (p : ℚ) ^ (k + 1) by linarith

private lemma mulSupport_pp_dvd_p (k : ℕ) (_hk : 0 < k)
    (a : Fin 2 → ℕ+) (hdiv : DivChain 2 a)
    (D1c D2c i₀_gl j₀_gl : GL (Fin 2) ℚ)
    (SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀ SL_j₀ :
        Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hD1_eq : D1c = SLnZ_to_GLnQ 2 SL_L₁ * diagMat 2 (![1, ⟨p, hp.pos⟩]) *
        SLnZ_to_GLnQ 2 SL_R₁)
    (hD2_eq : D2c = SLnZ_to_GLnQ 2 SL_L₂ * diagMat 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩]) *
        SLnZ_to_GLnQ 2 SL_R₂)
    (hi₀ : i₀_gl = SLnZ_to_GLnQ 2 SL_i₀)
    (hj₀ : j₀_gl = SLnZ_to_GLnQ 2 SL_j₀)
    (h_prod_eq_a : i₀_gl * D1c * (j₀_gl * D2c) =
        SLnZ_to_GLnQ 2 SL_La * diagMat 2 a * SLnZ_to_GLnQ 2 SL_Ra) :
    (a 0 : ℕ) ∣ p := by
  set S_mid := SL_R₁ * SL_j₀ * SL_L₂
  set L' := SL_La⁻¹ * SL_i₀ * SL_L₁
  set R' := SL_R₂ * SL_Ra⁻¹
  have h_gl : SLnZ_to_GLnQ 2 L' * diagMat 2 (![1, ⟨p, hp.pos⟩]) *
      SLnZ_to_GLnQ 2 S_mid * diagMat 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩]) *
      SLnZ_to_GLnQ 2 R' = diagMat 2 a := by
    set dp := diagMat 2 (![1, ⟨p, hp.pos⟩])
    set dpk := diagMat 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
    set da := diagMat 2 a
    have hprod : SLnZ_to_GLnQ 2 SL_i₀ * (SLnZ_to_GLnQ 2 SL_L₁ * dp *
        SLnZ_to_GLnQ 2 SL_R₁) * (SLnZ_to_GLnQ 2 SL_j₀ *
        (SLnZ_to_GLnQ 2 SL_L₂ * dpk * SLnZ_to_GLnQ 2 SL_R₂)) =
        SLnZ_to_GLnQ 2 SL_La * da * SLnZ_to_GLnQ 2 SL_Ra := by
      rw [← hi₀, ← hj₀, ← hD1_eq, ← hD2_eq]; exact h_prod_eq_a
    have := congr_arg₂ (· * ·) (congr_arg ((SLnZ_to_GLnQ 2 SL_La)⁻¹ * ·) hprod)
      (show (SLnZ_to_GLnQ 2 SL_Ra)⁻¹ = (SLnZ_to_GLnQ 2 SL_Ra)⁻¹ from rfl)
    simp only [mul_assoc, inv_mul_cancel_left] at this
    simp only [L', R', S_mid, map_mul, map_inv] at this ⊢
    convert this using 1; group
  have h_int_5 : (↑L' : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.diagonal (fun m => ((![1, ⟨p, hp.pos⟩] : Fin 2 → ℕ+) m : ℤ)) *
      (↑S_mid : Matrix (Fin 2) (Fin 2) ℤ) *
      Matrix.diagonal (fun m => ((![1, ⟨p ^ k, pow_pos hp.pos k⟩] : Fin 2 → ℕ+) m : ℤ)) *
      (↑R' : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.diagonal (fun i => (a i : ℤ)) := by
    ext i j
    have h := congr_arg (fun (g : GL (Fin 2) ℚ) => (↑g : Matrix _ _ ℚ) i j) h_gl
    simp only [diagMat_val, Matrix.diagonal_apply, Units.val_mul, SLnZ_to_GLnQ_val,
      Matrix.mul_apply, Matrix.map_apply] at h
    simp only [Matrix.diagonal_apply, Matrix.mul_apply]
    exact_mod_cast h
  exact first_invariant_dvd_p_of_product p hp S_mid a hdiv L' R' k _hk h_int_5

private lemma mulSupport_pp_case_split (k : ℕ) (_hk : 0 < k)
    (a : Fin 2 → ℕ+) (hdiv : DivChain 2 a)
    (h_det_prod : (a 0 : ℕ) * (a 1 : ℕ) = p ^ (k + 1))
    (h_dvd_p : (a 0 : ℕ) ∣ p) :
    T_diag 2 a hdiv =
      T_diag 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])
        (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _)) ∨
    T_diag 2 a hdiv =
      T_diag 2 (![⟨p, hp.pos⟩, ⟨p ^ k, pow_pos hp.pos k⟩])
        (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩
          (dvd_pow_self p (by omega))) := by
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (a 0) h_dvd_p with ha0_1 | ha0_p
  · left; congr 1; ext i; fin_cases i
    · exact PNat.eq ha0_1
    · exact PNat.eq (by rw [ha0_1, one_mul] at h_det_prod; exact h_det_prod)
  · right; congr 1; ext i; fin_cases i
    · exact PNat.eq ha0_p
    · apply PNat.eq; show (a 1 : ℕ) = _; dsimp
      have h1 : p * (a 1 : ℕ) = p ^ (k + 1) := by rwa [ha0_p] at h_det_prod
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h1, pow_succ]; ring)

private lemma mulSupport_pp_subset (k : ℕ) (_hk : 0 < k) (A : T' (GL_pair 2))
    (hA : A ∈ HeckeRing.mulSupport (GL_pair 2)
      (T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _)))) :
    A = T_diag 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])
        (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _)) ∨
    A = T_diag 2 (![⟨p, hp.pos⟩, ⟨p ^ k, pow_pos hp.pos k⟩])
        (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega))) := by
  obtain ⟨a, hdiv, hrep⟩ := exists_diagonal_representative 2 A.eql.choose
  have hA_eq : A = T_diag 2 a hdiv := by
    rw [← hrep]; exact (T'_ext _ _ _ A.eql.choose_spec.symm).symm
  set D1 := T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))
  set D2 := T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
    (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))
  rw [HeckeRing.mulSupport] at hA
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
    Prod.exists] at hA
  obtain ⟨i₀, j₀, hmap⟩ := hA
  have hD1_spec := D1.eql.choose_spec
  simp only [D1, T_diag, HeckeRing.T_mk, diagMat_delta] at hD1_spec
  have hD1_mem := hD1_spec ▸ DoubleCoset.mem_doubleCoset_self (GL_pair 2).H
    (GL_pair 2).H (D1.eql.choose : GL (Fin 2) ℚ)
  rw [DoubleCoset.mem_doubleCoset] at hD1_mem
  obtain ⟨L₁, ⟨SL_L₁, rfl⟩, R₁, ⟨SL_R₁, rfl⟩, hD1_eq⟩ := hD1_mem
  have hD2_spec := D2.eql.choose_spec
  simp only [D2, T_diag, HeckeRing.T_mk, diagMat_delta] at hD2_spec
  have hD2_mem := hD2_spec ▸ DoubleCoset.mem_doubleCoset_self (GL_pair 2).H
    (GL_pair 2).H (D2.eql.choose : GL (Fin 2) ℚ)
  rw [DoubleCoset.mem_doubleCoset] at hD2_mem
  obtain ⟨L₂, ⟨SL_L₂, rfl⟩, R₂, ⟨SL_R₂, rfl⟩, hD2_eq⟩ := hD2_mem
  have h_prod_in_A : (↑i₀.out : GL (Fin 2) ℚ) * D1.eql.choose *
      ((↑j₀.out : GL (Fin 2) ℚ) * D2.eql.choose) ∈ A.set := by
    rw [← hmap]; simp only [HeckeRing.mulMap, HeckeRing.T_mk]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [hA_eq] at h_prod_in_A
  simp only [T_diag, HeckeRing.T_mk, diagMat_delta] at h_prod_in_A
  rw [DoubleCoset.mem_doubleCoset] at h_prod_in_A
  obtain ⟨L_a, ⟨SL_La, rfl⟩, R_a, ⟨SL_Ra, rfl⟩, h_prod_eq⟩ := h_prod_in_A
  obtain ⟨SL_i₀, hSL_i₀⟩ := (i₀.out : ↥(GL_pair 2).H).2
  obtain ⟨SL_j₀, hSL_j₀⟩ := (j₀.out : ↥(GL_pair 2).H).2
  have h_det := mulSupport_pp_det_eq p k a (↑i₀.out) D1.eql.choose (↑j₀.out)
    D2.eql.choose
    (by rw [show (↑i₀.out : GL _ ℚ) = SLnZ_to_GLnQ 2 SL_i₀ from hSL_i₀.symm]
        exact SLnZ_to_GLnQ_det 2 SL_i₀)
    (by rw [hD1_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          SLnZ_to_GLnQ_det, SLnZ_to_GLnQ_det, diagMat_det]
        simp [Fin.prod_univ_two])
    (by rw [show (↑j₀.out : GL _ ℚ) = SLnZ_to_GLnQ 2 SL_j₀ from hSL_j₀.symm]
        exact SLnZ_to_GLnQ_det 2 SL_j₀)
    (by rw [hD2_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          SLnZ_to_GLnQ_det, SLnZ_to_GLnQ_det, diagMat_det]
        simp [Fin.prod_univ_two])
    SL_La SL_Ra h_prod_eq
  have h_dvd := mulSupport_pp_dvd_p p hp k _hk a hdiv D1.eql.choose D2.eql.choose
    (↑i₀.out) (↑j₀.out) SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀ SL_j₀
    hD1_eq hD2_eq hSL_i₀.symm hSL_j₀.symm h_prod_eq
  rw [hA_eq]; exact mulSupport_pp_case_split p hp k _hk a hdiv h_det h_dvd

private lemma D_out1_pp_in_mulSupport (k : ℕ) (_hk : 0 < k) :
    T_diag 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])
      (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _)) ∈
    HeckeRing.mulSupport (GL_pair 2)
      (T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))) := by
  set D1 := T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))
  set D2 := T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
    (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))
  set D_out1 := T_diag 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])
    (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _))
  set α := (D1.eql.choose : GL (Fin 2) ℚ)
  set β := (D2.eql.choose : GL (Fin 2) ℚ)
  have hα_mem : α ∈ DoubleCoset.doubleCoset (diagMat 2 (![1, ⟨p, hp.pos⟩]) : GL (Fin 2) ℚ)
      (GL_pair 2).H (GL_pair 2).H := by
    have := D1.eql.choose_spec
    simp only [D1, T_diag, HeckeRing.T_mk, diagMat_delta] at this
    rw [this]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hα_mem
  obtain ⟨L₁, hL₁, R₁, hR₁, hα_eq⟩ := hα_mem
  have hβ_mem : β ∈ DoubleCoset.doubleCoset
      (diagMat 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩]) : GL (Fin 2) ℚ)
      (GL_pair 2).H (GL_pair 2).H := by
    have := D2.eql.choose_spec
    simp only [D2, T_diag, HeckeRing.T_mk, diagMat_delta] at this
    rw [this]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hβ_mem
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ_eq⟩ := hβ_mem
  set i₀ : decompQuot (GL_pair 2) D1 := ⟦⟨L₁⁻¹, (GL_pair 2).H.inv_mem hL₁⟩⟧
  open scoped Pointwise in
  obtain ⟨κ₁, hκ₁_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (D1.eql.choose : GL (Fin 2) ℚ) • (GL_pair 2).H).subgroupOf (GL_pair 2).H)
    ⟨L₁⁻¹, (GL_pair 2).H.inv_mem hL₁⟩
  have hi₀ : (↑i₀.out : GL (Fin 2) ℚ) = L₁⁻¹ * (κ₁ : (GL_pair 2).H) := by
    have h := hκ₁_eq; apply_fun (↑· : ↥(GL_pair 2).H → GL (Fin 2) ℚ) at h
    simp only [Subgroup.coe_mul] at h; exact h
  have hκ₁_conj : α⁻¹ * (κ₁.val : GL (Fin 2) ℚ) * α ∈ (GL_pair 2).H := by
    have := κ₁.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct] using this
  set τ₀ : GL (Fin 2) ℚ := (α⁻¹ * (κ₁.val : GL (Fin 2) ℚ) * α)⁻¹ * R₁⁻¹ * L₂⁻¹
  have hτ₀_mem : τ₀ ∈ (GL_pair 2).H :=
    (GL_pair 2).H.mul_mem ((GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hκ₁_conj)
      ((GL_pair 2).H.inv_mem hR₁)) ((GL_pair 2).H.inv_mem hL₂)
  set j₀ : decompQuot (GL_pair 2) D2 := ⟦⟨τ₀, hτ₀_mem⟩⟧
  open scoped Pointwise in
  obtain ⟨κ₂, hκ₂_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (D2.eql.choose : GL (Fin 2) ℚ) • (GL_pair 2).H).subgroupOf (GL_pair 2).H)
    ⟨τ₀, hτ₀_mem⟩
  have hj₀ : (↑j₀.out : GL (Fin 2) ℚ) = τ₀ * (κ₂ : (GL_pair 2).H) := by
    have h := hκ₂_eq; apply_fun (↑· : ↥(GL_pair 2).H → GL (Fin 2) ℚ) at h
    simp only [Subgroup.coe_mul] at h; exact h
  have hκ₂_conj : β⁻¹ * (κ₂.val : GL (Fin 2) ℚ) * β ∈ (GL_pair 2).H := by
    have := κ₂.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct] using this
  have h_product_mem : (↑i₀.out : GL (Fin 2) ℚ) * α *
      ((↑j₀.out : GL (Fin 2) ℚ) * β) ∈
      DoubleCoset.doubleCoset
        (diagMat 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩]) : GL (Fin 2) ℚ)
        (GL_pair 2).H (GL_pair 2).H := by
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨1, (GL_pair 2).H.one_mem, R₂ * (β⁻¹ * (κ₂.val : GL (Fin 2) ℚ) * β),
            (GL_pair 2).H.mul_mem hR₂ hκ₂_conj, ?_⟩
    rw [hi₀, hj₀, show α = L₁ * diagMat 2 (![1, ⟨p, hp.pos⟩]) * R₁ from hα_eq,
        show β = L₂ * diagMat 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩]) * R₂ from hβ_eq]
    set D₁_mat := diagMat 2 (![1, ⟨p, hp.pos⟩])
    set D₂_mat := diagMat 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
    have h_D_mul : D₁_mat * D₂_mat =
        diagMat 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩]) := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;>
        simp [D₁_mat, D₂_mat, diagMat, pow_succ, mul_comm]
    rw [one_mul, ← h_D_mul]
    simp only [show τ₀ =
      (α⁻¹ * (κ₁.val : GL (Fin 2) ℚ) * α)⁻¹ * R₁⁻¹ * L₂⁻¹ from rfl,
               show α = L₁ * D₁_mat * R₁ from hα_eq]
    group
  rw [HeckeRing.mulSupport]
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists]
  exact ⟨i₀, j₀, by
    apply HeckeRing.T'_ext (GL_pair 2)
    show (HeckeRing.mulMap (GL_pair 2) D1 D2 (i₀, j₀)).set = D_out1.set
    rw [HeckeRing.mulMap, HeckeRing.T_mk]
    simp only
    conv_rhs => rw [show D_out1 = HeckeRing.T_mk (GL_pair 2)
        (diagMat_delta 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])) from rfl,
      HeckeRing.T_mk]
    simp only
    exact DoubleCoset.doubleCoset_eq_of_mem h_product_mem⟩

private lemma m'_values (k : ℕ) (hk : 0 < k) :
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _)))
      (T_diag 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])
        (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _))) = 1 ∧
    HeckeRing.m' (GL_pair 2)
      (T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)))
      (T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
        (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _)))
      (T_diag 2 (![⟨p, hp.pos⟩, ⟨p ^ k, pow_pos hp.pos k⟩])
        (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩
          (dvd_pow_self p (by omega)))) =
      if k = 1 then ↑(p + 1) else ↑p := by
  set D1 := T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))
  set D2 := T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
    (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))
  set D_out1 := T_diag 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])
    (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _))
  set D_out2 := T_diag 2 (![⟨p, hp.pos⟩, ⟨p ^ k, pow_pos hp.pos k⟩])
    (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)))
  set m1 := HeckeRing.m' (GL_pair 2) D1 D2 D_out1
  set m2 := HeckeRing.m' (GL_pair 2) D1 D2 D_out2
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have := diagonal_representative_unique 2 _ _ _ _ heq
    have := congr_fun this 0; simp only [Matrix.cons_val_zero] at this
    exact absurd (congr_arg PNat.val this).symm (Nat.Prime.one_lt hp).ne'
  have h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 → HeckeRing.m' (GL_pair 2) D1 D2 A = 0 := by
    intro A h1 h2; apply HeckeRing.m'_eq_zero_of_nmem_mulSupport
    intro hmem; exact (mulSupport_pp_subset p hp k hk A hmem).elim h1 h2
  have h_deg : m1 * T'_deg (GL_pair 2) D_out1 + m2 * T'_deg (GL_pair 2) D_out2 =
      T'_deg (GL_pair 2) D1 * T'_deg (GL_pair 2) D2 := by
    have h1 : HeckeRing.deg (GL_pair 2) (HeckeRing.m (GL_pair 2) D1 D2) =
        T'_deg (GL_pair 2) D1 * T'_deg (GL_pair 2) D2 := by
      rw [← HeckeRing.T_single_one_mul_T_single_one, HeckeRing.deg_mul,
          HeckeRing.deg_T_single, HeckeRing.deg_T_single]; ring
    have h2 : HeckeRing.deg (GL_pair 2) (HeckeRing.m (GL_pair 2) D1 D2) =
        m1 * T'_deg (GL_pair 2) D_out1 + m2 * T'_deg (GL_pair 2) D_out2 := by
      open Classical in
      simp only [HeckeRing.deg, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, HeckeRing.deg_fun]
      have hsub : (HeckeRing.m (GL_pair 2) D1 D2).support ⊆
          ({D_out1, D_out2} : Finset _) := by
        intro A hA; simp only [Finset.mem_insert, Finset.mem_singleton]
        rw [Finsupp.mem_support_iff] at hA
        exact (or_iff_not_imp_left.mpr fun h1 =>
          (Classical.em (A = D_out2)).elim id fun h2 => absurd (h_zero A h1 h2) hA)
      exact Finset.sum_subset hsub (by
        intro A _ hA; rw [Finsupp.notMem_support_iff.mp hA]; simp) |>.trans
        (Finset.sum_pair h_ne)
    linarith
  have hm1_nn := HeckeRing.m'_nonneg (GL_pair 2) D1 D2 D_out1
  have hm2_nn := HeckeRing.m'_nonneg (GL_pair 2) D1 D2 D_out2
  have hm1_pos : 1 ≤ m1 := by
    have hne : (HeckeRing.m (GL_pair 2) D1 D2) D_out1 ≠ 0 := by
      rw [← Finsupp.mem_support_iff, HeckeRing.m_support]
      exact D_out1_pp_in_mulSupport p hp k hk
    exact Int.lt_iff_add_one_le.mp (lt_of_le_of_ne hm1_nn (Ne.symm hne))
  have hd1 : T'_deg (GL_pair 2) D1 = ↑(p + 1) := by
    have := T'_deg_T_diag_two_prime p hp (![1, ⟨p, hp.pos⟩])
      (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _)) 1 one_pos (by simp [pow_one])
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
      show (![⟨p, hp.pos⟩, ⟨p ^ 1, pow_pos hp.pos 1⟩] : Fin 2 → ℕ+) 0 =
        (![⟨p, hp.pos⟩, ⟨p ^ 1, pow_pos hp.pos 1⟩] : Fin 2 → ℕ+) 1
      simp [pow_one]
    rw [hd_o2] at h_deg; push_cast at h_deg ⊢
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have h_m1_le : m1 * ((p : ℤ) * (↑p + 1)) ≤ (↑p + 1) * (↑p + 1) := by linarith
    have h_m1_eq : m1 = 1 := by nlinarith [mul_self_nonneg ((p : ℤ) - 1)]
    constructor
    · exact h_m1_eq
    · have := h_deg; rw [h_m1_eq] at this; linarith
  · simp only [show k ≠ 1 from hk1, ite_false]; have hk2 : 2 ≤ k := by omega
    have hd_o2 : T'_deg (GL_pair 2) D_out2 = ↑(p ^ (k - 2) * (p + 1)) :=
      T'_deg_T_diag_two_prime p hp _ _ (k - 1) (by omega)
        (by show p ^ k / p = p ^ (k - 1)
            have : p ^ k = p ^ (k - 1) * p := by
              rw [← pow_succ]; congr 1; omega
            rw [this, Nat.mul_div_cancel _ hp.pos])
    rw [hd_o2] at h_deg
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hpk : (p : ℤ) ^ k = (p : ℤ) ^ (k - 2) * (p : ℤ) ^ 2 := by
      have : (p : ℕ) ^ k = p ^ (k - 2) * p ^ 2 := by rw [← pow_add]; congr 1; omega
      exact_mod_cast this
    have hpk1 : (p : ℤ) ^ (k - 1) = (p : ℤ) ^ (k - 2) * (p : ℤ) ^ 1 := by
      have : (p : ℕ) ^ (k - 1) = p ^ (k - 2) * p ^ 1 := by rw [← pow_add]; congr 1; omega
      exact_mod_cast this
    have hpk2_pos : (0 : ℤ) < (p : ℤ) ^ (k - 2) := by positivity
    push_cast at h_deg ⊢
    rw [pow_one] at hpk1
    have h_eq : m1 * (p : ℤ) ^ 2 + m2 = (p : ℤ) * ((p : ℤ) + 1) := by
      have h := h_deg
      rw [hpk, hpk1] at h
      have key : (p : ℤ) ^ (k - 2) * ((p : ℤ) + 1) ≠ 0 := by positivity
      have := mul_right_cancel₀ key (show
        (m1 * (p : ℤ) ^ 2 + m2) * ((p : ℤ) ^ (k - 2) * ((p : ℤ) + 1)) =
        ((p : ℤ) * ((p : ℤ) + 1)) * ((p : ℤ) ^ (k - 2) * ((p : ℤ) + 1)) by nlinarith)
      linarith
    have hp2 := hp.two_le
    have h_m1_eq : m1 = 1 := by
      have h_le : m1 * (p : ℤ) ^ 2 ≤ (p : ℤ) ^ 2 + p := by linarith [h_eq]
      have h_lt_2 : m1 < 2 := by
        by_contra h
        push_neg at h
        have : 2 * (p : ℤ) ^ 2 ≤ m1 * (p : ℤ) ^ 2 := by nlinarith
        nlinarith [show (p : ℤ) ^ 2 ≥ 4 by nlinarith [show (2 : ℤ) ≤ p by exact_mod_cast hp2]]
      have hm1_le : m1 ≤ 1 := by
        rcases le_or_gt m1 1 with h | h
        · exact h
        · exfalso; linarith [show m1 ≥ 2 from h]
      exact le_antisymm hm1_le hm1_pos
    refine ⟨h_m1_eq, ?_⟩
    have := h_eq; rw [h_m1_eq] at this; linarith [this]

/-- Theorem 3.24(5): `T(p) · T(1, pᵏ) = T(1, p^{k+1}) + m · T(p, pᵏ)` -/
theorem thm324_5 (k : ℕ) (hk : 0 < k) :
    T_sum ⟨p, hp.pos⟩ *
    T_ad 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _) =
    T_ad 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _) +
    (if k = 1 then (↑(p + 1) : ℤ) else (↑p : ℤ)) •
      T_ad ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩
        (dvd_pow_self p (by omega)) := by
  rw [T_sum_prime p hp]
  set D1 := T_diag 2 (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))
  set D2 := T_diag 2 (![1, ⟨p ^ k, pow_pos hp.pos k⟩])
    (divChain_mk2 1 ⟨p ^ k, pow_pos hp.pos k⟩ (one_dvd _))
  set D_out1 := T_diag 2 (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩])
    (divChain_mk2 1 ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ (one_dvd _))
  set D_out2 := T_diag 2 (![⟨p, hp.pos⟩, ⟨p ^ k, pow_pos hp.pos k⟩])
    (divChain_mk2 ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)))
  set c := (if k = 1 then (↑(p + 1) : ℤ) else (↑p : ℤ))
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have := diagonal_representative_unique 2 _ _ _ _ heq
    have h0 : (![1, ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩] : Fin 2 → ℕ+) 0 = 1 := rfl
    have h0' : (![⟨p, hp.pos⟩, ⟨p ^ k, pow_pos hp.pos k⟩] : Fin 2 → ℕ+) 0 = ⟨p, hp.pos⟩ := rfl
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
  rw [hk1, T_ad'_one_ppow p hp (k - 1), T_ad'_ppow p hp 1 k (by omega)] at h0
  have h_p1 : (⟨p ^ 1, pow_pos hp.pos 1⟩ : ℕ+) = ⟨p, hp.pos⟩ := PNat.eq (pow_one p)
  have h_rhs_congr : T_ad ⟨p ^ 1, pow_pos hp.pos 1⟩ ⟨p ^ k, pow_pos hp.pos k⟩
    (Nat.pow_dvd_pow p (by omega : 1 ≤ k)) =
    T_ad ⟨p, hp.pos⟩ ⟨p ^ k, pow_pos hp.pos k⟩ (dvd_pow_self p (by omega)) := by
      unfold T_ad; exact T_elem_congr_diag 2 (by ext i; fin_cases i <;> simp [pow_one]) _ _
  rw [h_rhs_congr] at h0
  exact h0.symm

/-- The prime-power recurrence: `T(p^{k+1}) = T(p) · T(pᵏ) − p · T(p,p) · T(p^{k−1})`.
    Follows from Identity 5 + Identity 2 by strong induction.
    Base cases k=1,2 are direct; k ≥ 3 uses IH at k-2. -/
private lemma T_pp_comm_T_ad_one_p :
    T_pp p hp * T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) =
    T_ad 1 ⟨p, hp.pos⟩ (one_dvd _) * T_pp p hp :=
  T_pp_comm_T_elem p hp (![1, ⟨p, hp.pos⟩]) (divChain_mk2 1 ⟨p, hp.pos⟩ (one_dvd _))

theorem T_sum_ppow_recurrence : ∀ k : ℕ, 0 < k →
    T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ =
    T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    (p : ℤ) • (T_pp p hp * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro hk
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
    show T_elem 2 (![1, ⟨p ^ 1, pow_pos hp.pos 1⟩]) _ = T_elem 2 (![1, ⟨p, hp.pos⟩]) _
    exact T_elem_congr_diag 2 (by ext i; fin_cases i <;> simp [pow_one]) _ _
  have h5 := thm324_5 p hp k hk
  rw [T_ad_p_ppow_eq p hp k hk] at h5
  have h2 := thm324_2 p hp (k + 1) (by omega)
  conv at h2 => rhs; rw [show (k + 1) - 2 = k - 1 from by omega]
  rw [h2] at h5
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
    have h2k := thm324_2 p hp (k + 2) (by omega)
    rw [h2k] at h5; rw [mul_sub] at h5
    by_cases hk0 : k = 0
    · subst hk0; simp only [Nat.zero_add] at h5 ⊢
      rw [h_tsum_0, mul_one, h_p1_tad, T_sum_prime p hp] at h5
      have h_p1_pnat : (⟨p ^ 1, pow_pos hp.pos 1⟩ : ℕ+) = ⟨p, hp.pos⟩ := by ext; simp [pow_one]
      rw [show T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ from
        by rw [h_p1_pnat]] at h5 ⊢
      rw [T_sum_prime p hp] at h5 ⊢
      have hcomm := (T_pp_comm_T_ad_one_p p hp).symm
      rw [hcomm] at h5
      rw [sub_eq_iff_eq_add] at h5; rw [eq_sub_iff_add_eq]
      have h5' := h5; abel_nf at h5' ⊢; exact h5'.symm
    ·
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
      have h2k1 := thm324_2 p hp (k + 1) (by omega)
      conv at h2k1 => rhs; rw [show (k + 1) - 2 = k - 1 from by omega]
      rw [h2k1] at h5
      conv at h5 => lhs; rw [show k + 2 - 2 = k from by omega]
      conv at h5 => rhs; rw [show T_pp p hp *
          (T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ -
           T_pp p hp * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) =
          T_pp p hp * T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ -
          T_pp p hp * (T_pp p hp * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩)
        from mul_sub _ _ _]
      rw [smul_sub] at h5
      rw [← mul_assoc (T_sum ⟨p, hp.pos⟩) (T_pp p hp)
          (T_sum ⟨p ^ k, pow_pos hp.pos k⟩)] at h5
      have hcomm : T_sum ⟨p, hp.pos⟩ * T_pp p hp =
          T_pp p hp * T_sum ⟨p, hp.pos⟩ := by
        rw [T_sum_prime p hp]; exact (T_pp_comm_T_ad_one_p p hp).symm
      rw [hcomm] at h5
      rw [mul_assoc (T_pp p hp) (T_sum ⟨p, hp.pos⟩)
          (T_sum ⟨p ^ k, pow_pos hp.pos k⟩)] at h5
      have ih_k := ih k (by omega) hk_pos
      have ih_k' : T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
          T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ +
          (↑p : ℤ) • (T_pp p hp *
            T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
        rw [ih_k]; abel
      rw [ih_k'] at h5
      rw [mul_add (T_pp p hp)] at h5
      rw [mul_smul_comm (↑p : ℤ)] at h5
      rw [← mul_assoc (T_pp p hp) (T_pp p hp)] at h5
      rw [sub_eq_iff_eq_add] at h5
      have h6 : T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩ =
          T_sum ⟨p ^ (k + 2 + 1), pow_pos hp.pos (k + 2 + 1)⟩ +
          (↑p : ℤ) • (T_pp p hp * T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩) := by
        rw [h5]; abel
      exact eq_sub_iff_add_eq.mpr h6.symm

/-! ### Identity 4: General prime-power product -/

/-- Theorem 3.24(4): `T(pʳ) · T(pˢ) = Σ_{i=0}^{r} pⁱ · T(pⁱ,pⁱ) · T(p^{r+s−2i})`
    for r ≤ s. Proved by induction on r using `T_sum_ppow_recurrence`. -/
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

private lemma T_pp_pow_comm_T_sum_ppow (i k : ℕ) :
    T_pp p hp ^ i * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ * T_pp p hp ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, T_pp_comm_T_sum_ppow p hp k, mul_assoc, ← pow_succ']

private lemma T_sum_p_comm_T_pp_pow (i : ℕ) :
    T_sum ⟨p, hp.pos⟩ * T_pp p hp ^ i =
    T_pp p hp ^ i * T_sum ⟨p, hp.pos⟩ := by
  have h1 : (⟨p ^ 1, pow_pos hp.pos 1⟩ : ℕ+) = ⟨p, hp.pos⟩ := PNat.eq (pow_one p)
  rw [show T_sum ⟨p, hp.pos⟩ = T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ from by congr 1; exact h1.symm]
  exact (T_pp_pow_comm_T_sum_ppow p hp i 1).symm

private lemma T_sum_p_comm_T_pp_pow_T_sum (i k : ℕ) :
    T_sum ⟨p, hp.pos⟩ * (T_pp p hp ^ i * T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
    T_pp p hp ^ i * (T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩) := by
  rw [← mul_assoc, T_sum_p_comm_T_pp_pow p hp i, mul_assoc]

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
    rw [mul_assoc, ih1, smul_mul_assoc, mul_assoc (T_pp p hp), ih0]
    set Tp := T_sum ⟨p, hp.pos⟩ with Tp_def
    set Tpp := T_pp p hp with Tpp_def
    set S1 := ∑ i ∈ Finset.range (r + 1 + 1),
      (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)
    set S2 := ∑ i ∈ Finset.range (r + 1),
      (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)
    have h_lhs1 : Tp * S1 = ∑ i ∈ Finset.range (r + 1 + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [mul_smul_comm, T_sum_p_comm_T_pp_pow_T_sum p hp i _, ← mul_assoc]
    have h_lhs2 : (p : ℤ) • (Tpp * S2) = ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
      rw [Finset.mul_sum, Finset.smul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [mul_smul_comm, smul_smul, mul_comm ((p : ℤ)) ((p : ℤ) ^ i), ← pow_succ]
      congr 1; rw [← mul_assoc, ← pow_succ']
    have h_peel1 : ∑ i ∈ Finset.range (r + 1 + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
      (∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩))) +
      (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩)) :=
      Finset.sum_range_succ _ _
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
      rw [mul_smul_comm, smul_smul, show (p : ℤ) ^ i * (p : ℤ) = (p : ℤ) ^ (i + 1) from by ring]
      congr 1
      rw [← mul_assoc, ← pow_succ]
    have h_sum_split :
      ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
      (∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩)) +
      (∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl h_split
    rw [h_lhs1, h_peel1, h_sum_split, h_lhs2]
    set A := ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩)
    set B := ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)
    set C := (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) * (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩))
    show A + B + C - B = _
    rw [add_assoc, add_comm B C, ← add_assoc, add_sub_cancel_right]
    rw [show r + 2 + 1 = (r + 1) + 1 + 1 from by omega]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    rw [add_assoc]
    congr 1
    have hexp_C : r + 1 + s - 2 * (r + 1) = s - r - 1 := by omega
    have hexp1 : r + 2 + s - 2 * (r + 1) = s - r := by omega
    have hexp2 : r + 2 + s - 2 * (r + 2) = s - r - 2 := by omega
    have h_sr_pos : 0 < s - r - 1 := by omega
    have h_rec_final := T_sum_ppow_recurrence p hp (s - r - 1) h_sr_pos
    rw [show (s - r - 1) + 1 = s - r from by omega,
        show s - r - 1 - 1 = s - r - 2 from by omega] at h_rec_final
    have h_expand : Tp * T_sum ⟨p ^ (s - r - 1), pow_pos hp.pos _⟩ =
        T_sum ⟨p ^ (s - r), pow_pos hp.pos _⟩ +
        (p : ℤ) • (Tpp * T_sum ⟨p ^ (s - r - 2), pow_pos hp.pos _⟩) := by
      rw [eq_sub_iff_add_eq] at h_rec_final; exact h_rec_final.symm
    have hC_def : C = (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) *
        (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩)) := rfl
    rw [hC_def, hexp_C, h_expand, mul_add, smul_add, mul_smul_comm, smul_smul,
        show (p : ℤ) ^ (r + 1) * (p : ℤ) = (p : ℤ) ^ (r + 2) from by ring,
        ← mul_assoc, show Tpp ^ (r + 1) * Tpp = Tpp ^ (r + 2) from (pow_succ Tpp (r + 1)).symm]
    have hnat2 : s - r - 2 = r + 2 + s - 2 * (r + 2) := by omega
    have hnat1 : s - r = r + 2 + s - 2 * (r + 1) := by omega
    rw [hnat2, hnat1]

/-! ### Identity 3: General multiplicativity -/

section CoprimeMultiplicativity

open Finset in
/-- `diagDet 2 (![a, d]) = a * d`. -/
private lemma diagDet_mk2 (a d : ℕ+) :
    diagDet 2 (![a, d]) = a * d := by
  simp [diagDet, Fin.prod_univ_two]

/-- For coprime divisor pairs, the `T_ad'` product equals `T_ad'` of the products. -/
private lemma T_ad'_mul_of_coprime (a b da db : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hda : 0 < da) (hdb : 0 < db)
    (hdva : a ∣ da) (hdvb : b ∣ db)
    (hcop : Nat.Coprime (a * da) (b * db)) :
    T_ad' a da * T_ad' b db = T_ad' (a * b) (da * db) := by
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
  unfold T_ad
  rw [T_diag_mul_coprime 2 (![⟨a, ha⟩, ⟨da, hda⟩]) (![⟨b, hb⟩, ⟨db, hdb⟩])
    (divChain_mk2 _ _ hdva) (divChain_mk2 _ _ hdvb)
    (by rw [diagDet_mk2, diagDet_mk2]; exact hcop)]
  apply T_elem_congr_diag
  ext i; fin_cases i <;> simp [pnatMul]

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
  have hcop₁₂ : Nat.Coprime a₁ b₂ :=
    Nat.Coprime.coprime_dvd_left ha₁ (Nat.Coprime.coprime_dvd_right hb₂ hcop)
  have hcop₂₁ : Nat.Coprime a₂ b₁ :=
    Nat.Coprime.coprime_dvd_left ha₂ (Nat.Coprime.coprime_dvd_right hb₁ hcop)
  have ha₁_dvd_a₂ : a₁ ∣ a₂ := by
    have : a₁ ∣ a₂ * b₂ := heq ▸ dvd_mul_right a₁ b₁
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop₁₂ this)
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
  set M := (m : ℕ) with hM
  set N := (n : ℕ) with hN
  change (∑ a ∈ M.divisors, T_ad' a (M / a)) * (∑ b ∈ N.divisors, T_ad' b (N / b)) =
    ∑ c ∈ (M * N).divisors, T_ad' c ((M * N) / c)
  rw [Finset.sum_mul_sum]
  open scoped Pointwise in
  rw [Nat.divisors_mul]
  open scoped Pointwise in
  rw [show (Nat.divisors M * Nat.divisors N) =
    (Nat.divisors M ×ˢ Nat.divisors N).image (fun p => p.1 * p.2) from rfl]
  rw [Finset.sum_image (mul_injOn_coprime_divisors M N hcop), ← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_product, Nat.mem_divisors] at hab
  have ha_dvd := hab.1.1
  have hb_dvd := hab.2.1
  have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => by simp [h] at hab)
  have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h => by simp [h] at hab)
  have hdiv_eq : (M * N) / (a * b) = M / a * (N / b) :=
    (Nat.div_mul_div_comm ha_dvd hb_dvd).symm
  rw [hdiv_eq]
  by_cases hca : a ∣ (M / a)
  · by_cases hcb : b ∣ (N / b)
    · apply T_ad'_mul_of_coprime a b (M / a) (N / b) ha_pos hb_pos
        (Nat.div_pos (Nat.le_of_dvd (by omega) ha_dvd) ha_pos)
        (Nat.div_pos (Nat.le_of_dvd (by omega) hb_dvd) hb_pos)
        hca hcb
      rwa [hM, hN, Nat.mul_div_cancel' ha_dvd, Nat.mul_div_cancel' hb_dvd]
    ·
      rw [T_ad'_mul_zero_of_not_dvd' b (N / b)
        (by push_neg; intro _ _; exact hcb) (T_ad' a (M / a))]
      symm; unfold T_ad'; rw [dif_neg]; push_neg
      intro _ _ hdvd; apply hcb
      have hb_dvd_prod : b ∣ M / a * (N / b) := dvd_trans (dvd_mul_left b a) hdvd
      have hcop_b_ma : Nat.Coprime b (M / a) :=
        Nat.Coprime.coprime_dvd_left hb_dvd (hcop.symm.coprime_dvd_right (Nat.div_dvd_of_dvd ha_dvd))
      exact hcop_b_ma.dvd_of_dvd_mul_left hb_dvd_prod
  ·
    rw [T_ad'_mul_zero_of_not_dvd a (M / a)
      (by push_neg; intro _ _; exact hca)]
    symm; unfold T_ad'; rw [dif_neg]; push_neg
    intro _ _ hdvd; apply hca
    have ha_dvd_prod : a ∣ M / a * (N / b) := dvd_trans (dvd_mul_right a b) hdvd
    have hcop_a_nb : Nat.Coprime a (N / b) :=
      Nat.Coprime.coprime_dvd_left ha_dvd (hcop.coprime_dvd_right (Nat.div_dvd_of_dvd hb_dvd))
    exact hcop_a_nb.dvd_of_dvd_mul_right ha_dvd_prod

end CoprimeMultiplicativity

/-- T_sum extended to ℕ: agrees with `T_sum` for positive arguments, zero for 0. -/
private noncomputable def T_sum_nat (k : ℕ) : HeckeAlgebra 2 :=
  ∑ a ∈ k.divisors, T_ad' a (k / a)

private lemma T_sum_nat_eq (k : ℕ+) : T_sum_nat (k : ℕ) = T_sum k := rfl

private lemma T_ad'_one_one : T_ad' 1 1 = 1 := by
  unfold T_ad'; rw [dif_pos ⟨one_pos, one_pos, dvd_refl 1⟩]
  exact T_ad_one_one

private lemma T_ad'_self_eq_T_ad (c : ℕ) (hc : 0 < c) :
    T_ad' c c = T_ad ⟨c, hc⟩ ⟨c, hc⟩ (dvd_refl _) := by
  unfold T_ad'; rw [dif_pos ⟨hc, hc, dvd_refl c⟩]

private lemma T_ad_self_eq_T_elem (c : ℕ+) :
    T_ad c c (dvd_refl _) =
    T_elem 2 (fun _ => c) (divChain_const 2 c) := by
  unfold T_ad
  have hmk2 : ![c, c] = (fun (_ : Fin 2) => c) := funext fun j => by fin_cases j <;> rfl
  exact T_elem_congr_diag 2 hmk2 _ _

private lemma T_pp_pow_eq_T_ad' (q : ℕ) (hq : q.Prime) (i : ℕ) :
    T_pp q hq ^ i = T_ad' (q ^ i) (q ^ i) := by
  rw [T_ad'_self_eq_T_ad _ (pow_pos hq.pos i), T_ad_self_eq_T_elem, T_pp_pow q hq i]

private lemma gcd_pow_pow_of_le (q : ℕ) (r s : ℕ) (hrs : r ≤ s) :
    Nat.gcd (q ^ r) (q ^ s) = q ^ r := by
  apply Nat.dvd_antisymm (Nat.gcd_dvd_left _ _)
  exact Nat.dvd_gcd (dvd_refl _) (Nat.pow_dvd_pow q hrs)

/-- Prime-power product in divisor-sum form. -/
private lemma T_sum_mul_prime_pow_aux (q : ℕ) (hq : q.Prime) (r s : ℕ) (hrs : r ≤ s) :
    T_sum ⟨q ^ r, pow_pos hq.pos r⟩ * T_sum ⟨q ^ s, pow_pos hq.pos s⟩ =
    ∑ d ∈ (Nat.gcd (q ^ r) (q ^ s)).divisors,
      (d : ℤ) • (T_ad' d d * T_sum_nat (q ^ r * q ^ s / (d * d))) := by
  rw [thm324_4 q hq r s hrs, gcd_pow_pow_of_le q r s hrs, Nat.sum_divisors_prime_pow hq]
  apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
  congr 1
  · push_cast; ring
  · congr 1
    · rw [T_pp_pow_eq_T_ad' q hq i]
    · rw [← pow_add, ← pow_add, show i + i = 2 * i from by ring, Nat.pow_div (by omega) hq.pos]
      rfl

/-- Coprime base case for the divisor sum formula. -/
private lemma T_sum_mul_of_coprime_aux (m n : ℕ+) (hcop : Nat.Coprime m n) :
    T_sum m * T_sum n =
    ∑ d ∈ (Nat.gcd m n).divisors,
      (d : ℤ) • (T_ad' d d * T_sum_nat (↑m * ↑n / (d * d))) := by
  have hg : Nat.gcd m n = 1 := hcop
  rw [hg, Nat.divisors_one, Finset.sum_singleton]
  simp only [Nat.cast_one, one_smul, one_mul, T_ad'_one_one, one_mul, Nat.div_one]
  rw [T_sum_mul_coprime m n hcop]; rfl

/-- GCD factoring: `gcd(q^a * m', q^b * n') = q^(min a b) * gcd(m', n')`. -/
private lemma gcd_factor_prime_pow (q : ℕ) (hq : q.Prime)
    (a b : ℕ) (m' n' : ℕ+) (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ)) :
    Nat.gcd (q ^ a * m') (q ^ b * n') = q ^ min a b * Nat.gcd m' n' := by
  have hcop_qm : Nat.Coprime (q ^ a) m' := (Nat.Prime.coprime_pow_of_not_dvd hq hqm).symm
  have hcop_qn : Nat.Coprime (q ^ b) n' := (Nat.Prime.coprime_pow_of_not_dvd hq hqn).symm
  have hcop_rg : Nat.Coprime (q ^ min a b) (Nat.gcd m' n') :=
    (Nat.Prime.coprime_pow_of_not_dvd hq
      (fun h => hqm (dvd_trans h (Nat.gcd_dvd_left _ _)))).symm
  apply Nat.eq_of_factorization_eq
    (Nat.gcd_pos_of_pos_left _ (Nat.mul_pos (pow_pos hq.pos a) m'.pos)).ne'
    (Nat.mul_pos (pow_pos hq.pos (min a b)) (Nat.gcd_pos_of_pos_left _ m'.pos)).ne'
  intro p'
  rw [Nat.factorization_gcd (Nat.mul_pos (pow_pos hq.pos a) m'.pos).ne'
      (Nat.mul_pos (pow_pos hq.pos b) n'.pos).ne',
    Nat.factorization_mul_of_coprime hcop_qm, Nat.factorization_mul_of_coprime hcop_qn,
    Nat.factorization_mul_of_coprime hcop_rg,
    Nat.factorization_gcd m'.pos.ne' n'.pos.ne']
  simp only [Finsupp.inf_apply, Finsupp.add_apply]
  by_cases hpq : p' = q
  · subst hpq
    rw [Nat.Prime.factorization_pow hq, Nat.Prime.factorization_pow hq,
        Nat.Prime.factorization_pow hq]
    simp only [Finsupp.single_apply,
      Nat.factorization_eq_zero_of_not_dvd hqm,
      Nat.factorization_eq_zero_of_not_dvd hqn]
    simp only [add_zero, min_zero]; rfl
  · rw [Nat.Prime.factorization_pow hq, Nat.Prime.factorization_pow hq,
      Nat.Prime.factorization_pow hq]
    simp only [Finsupp.single_apply, show q ≠ p' from Ne.symm hpq, if_false, zero_add]

/-- RHS computation for the inner summand: T_sum_nat product equals the combined quotient. -/
private lemma T_sum_mul_peel_prime_summand_rhs (q : ℕ) (hq : q.Prime)
    (a b : ℕ) (m' n' : ℕ+) (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ))
    (r s : ℕ) (hr : r = min a b) (hs : s = max a b)
    (i : ℕ) (hi : i < r + 1) (d' : ℕ)
    (hd'_dvd : d' ∣ Nat.gcd (m' : ℕ) n')
    (_hqd' : ¬ q ∣ d') (_hcop_qi_d' : Nat.Coprime (q ^ i) d') (hd'_pos : 0 < d') :
    T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ *
      T_sum_nat (↑m' * ↑n' / (d' * d')) =
    T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (q ^ i * d' * (q ^ i * d'))) := by
  have hq_ndvd_mn : ¬ q ∣ ↑m' * ↑n' :=
    fun h => hqm ((hq.dvd_mul.mp h).elim id (fun h' => absurd h' hqn))
  have hq_ndvd_quot : ¬ q ∣ ↑m' * ↑n' / (d' * d') :=
    fun h => hq_ndvd_mn (dvd_trans h (Nat.div_dvd_of_dvd (Nat.mul_dvd_mul
      (dvd_trans hd'_dvd (Nat.gcd_dvd_left _ _)) (dvd_trans hd'_dvd (Nat.gcd_dvd_right _ _)))))
  have h_quot_pos : 0 < ↑m' * ↑n' / (d' * d') :=
    Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos m'.pos n'.pos) (Nat.mul_dvd_mul
      (dvd_trans hd'_dvd (Nat.gcd_dvd_left _ _)) (dvd_trans hd'_dvd (Nat.gcd_dvd_right _ _))))
      (Nat.mul_pos hd'_pos hd'_pos)
  change T_sum_nat ↑(⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ : ℕ+) *
    T_sum_nat (↑m' * ↑n' / (d' * d')) =
    T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (q ^ i * d' * (q ^ i * d')))
  rw [show (⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ : ℕ+).val = q ^ (r + s - 2 * i) from rfl]
  rw [show T_sum_nat (q ^ (r + s - 2 * i)) * T_sum_nat (↑m' * ↑n' / (d' * d')) =
    T_sum_nat (q ^ (r + s - 2 * i) * (↑m' * ↑n' / (d' * d'))) from by
      change T_sum ⟨_, pow_pos hq.pos _⟩ * T_sum ⟨_, h_quot_pos⟩ = _
      rw [T_sum_mul_coprime _ _ ((Nat.Prime.coprime_pow_of_not_dvd hq hq_ndvd_quot).symm)]
      rfl]
  congr 1
  have hrs_eq : r + s = a + b := by subst hr; subst hs; simp [min_def, max_def]; split <;> ring
  rw [hrs_eq, show q ^ i * d' * (q ^ i * d') = q ^ (2 * i) * (d' * d') from by ring,
    show q ^ a * ↑m' * (q ^ b * ↑n') = q ^ (a + b) * (↑m' * ↑n') from by ring,
    show q ^ (a + b) = q ^ (a + b - 2 * i) * q ^ (2 * i) from by
      rw [← pow_add]; congr 1; omega,
    show q ^ (a + b - 2 * i) * q ^ (2 * i) * (↑m' * ↑n') =
      q ^ (2 * i) * (q ^ (a + b - 2 * i) * (↑m' * ↑n')) from by ring,
    show q ^ (2 * i) * (d' * d') = q ^ (2 * i) * (d' * d') from rfl,
    Nat.mul_div_mul_left _ _ (pow_pos hq.pos (2 * i)),
    Nat.mul_div_assoc _ (Nat.mul_dvd_mul
      (dvd_trans hd'_dvd (Nat.gcd_dvd_left _ _)) (dvd_trans hd'_dvd (Nat.gcd_dvd_right _ _)))]

/-- Inner summand factoring for the peel-off-a-prime step. -/
private lemma T_sum_mul_peel_prime_summand (q : ℕ) (hq : q.Prime)
    (a b : ℕ) (m' n' : ℕ+) (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ))
    (r s : ℕ) (hr : r = min a b) (hs : s = max a b)
    (i : ℕ) (hi : i < r + 1) (d' : ℕ) (hd' : d' ∈ (Nat.gcd (m' : ℕ) n').divisors) :
    (↑(q ^ i) : ℤ) • ((T_pp q hq ^ i *
      T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩) *
      ((d' : ℤ) • (T_ad' d' d' * T_sum_nat (↑m' * ↑n' / (d' * d'))))) =
    (↑(q ^ i * d') : ℤ) • (T_ad' (q ^ i * d') (q ^ i * d') *
      T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (q ^ i * d' * (q ^ i * d')))) := by
  have hd'_dvd : d' ∣ Nat.gcd (m' : ℕ) n' := (Nat.mem_divisors.mp hd').1
  have hqd' : ¬ q ∣ d' :=
    fun h => hqm (dvd_trans h (dvd_trans hd'_dvd (Nat.gcd_dvd_left _ _)))
  have hcop_qi_d' : Nat.Coprime (q ^ i) d' :=
    (Nat.Prime.coprime_pow_of_not_dvd hq hqd').symm
  have hd'_pos : 0 < d' := by
    rcases Nat.eq_zero_or_pos d' with rfl | h
    · exact absurd (Nat.eq_zero_of_zero_dvd hd'_dvd) (Nat.gcd_pos_of_pos_left _ m'.pos).ne'
    · exact h
  rw [mul_smul_comm, smul_smul, show (↑(q ^ i) : ℤ) * ↑d' = ↑(q ^ i * d') from by push_cast; ring]
  congr 1
  rw [T_pp_pow_eq_T_ad' q hq i]
  rw [show T_ad' (q ^ i) (q ^ i) * T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ *
    (T_ad' d' d' * T_sum_nat (↑m' * ↑n' / (d' * d'))) =
    (T_ad' (q ^ i) (q ^ i) * T_ad' d' d') *
    (T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ *
      T_sum_nat (↑m' * ↑n' / (d' * d')))
    from by ring]
  have hcop_sq : Nat.Coprime (q ^ i * (q ^ i)) (d' * d') :=
    (hcop_qi_d'.mul_right hcop_qi_d').mul_left (hcop_qi_d'.mul_right hcop_qi_d')
  congr 1
  · rw [T_ad'_mul_of_coprime _ d' _ d' (pow_pos hq.pos i) hd'_pos (pow_pos hq.pos i) hd'_pos
      (dvd_refl _) (dvd_refl _) hcop_sq]
  · exact T_sum_mul_peel_prime_summand_rhs q hq a b m' n' hqm hqn r s hr hs i hi d'
      hd'_dvd hqd' hcop_qi_d' hd'_pos

/-- Peel-off-a-prime step for the divisor sum formula. -/
private lemma T_sum_mul_peel_prime_aux (q : ℕ) (hq : q.Prime)
    (a b : ℕ) (_ha : 0 < a) (_hb : 0 < b)
    (m' n' : ℕ+) (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ))
    (ih : T_sum m' * T_sum n' = ∑ d ∈ (Nat.gcd m' n').divisors,
      (d : ℤ) • (T_ad' d d * T_sum_nat (↑m' * ↑n' / (d * d)))) :
    T_sum ⟨q ^ a * m', Nat.mul_pos (pow_pos hq.pos a) m'.pos⟩ *
    T_sum ⟨q ^ b * n', Nat.mul_pos (pow_pos hq.pos b) n'.pos⟩ =
    ∑ d ∈ (Nat.gcd (q ^ a * m') (q ^ b * n')).divisors,
      (d : ℤ) • (T_ad' d d *
        T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (d * d))) := by
  have hcop_qm : Nat.Coprime (q ^ a) m' := (Nat.Prime.coprime_pow_of_not_dvd hq hqm).symm
  have hcop_qn : Nat.Coprime (q ^ b) n' := (Nat.Prime.coprime_pow_of_not_dvd hq hqn).symm
  set qa : ℕ+ := ⟨q ^ a, pow_pos hq.pos a⟩; set qb : ℕ+ := ⟨q ^ b, pow_pos hq.pos b⟩
  rw [show T_sum ⟨q ^ a * m', _⟩ = T_sum qa * T_sum m' from
    (T_sum_mul_coprime qa m' hcop_qm).symm,
    show T_sum ⟨q ^ b * n', _⟩ = T_sum qb * T_sum n' from
    (T_sum_mul_coprime qb n' hcop_qn).symm,
    show T_sum qa * T_sum m' * (T_sum qb * T_sum n') =
      (T_sum qa * T_sum qb) * (T_sum m' * T_sum n') from by ring]
  set r := min a b with hr_def; set g := Nat.gcd (m' : ℕ) n' with hg_def
  have hcop_rg : Nat.Coprime (q ^ r) g :=
    (Nat.Prime.coprime_pow_of_not_dvd hq (fun h => hqm (dvd_trans h (Nat.gcd_dvd_left _ _)))).symm
  rw [gcd_factor_prime_pow q hq a b m' n' hqm hqn]
  open scoped Pointwise in
  rw [Nat.divisors_mul]
  rw [show (Nat.divisors (q ^ r) * Nat.divisors g) =
    (Nat.divisors (q ^ r) ×ˢ Nat.divisors g).image (fun p => p.1 * p.2) from rfl]
  rw [ih]; set s := max a b with hs_def; have hrs : r ≤ s := min_le_max
  rw [show T_sum qa * T_sum qb =
    T_sum ⟨q ^ r, pow_pos hq.pos r⟩ * T_sum ⟨q ^ s, pow_pos hq.pos s⟩
    from by simp only [r, s, min_def, max_def]; split <;> [rfl; rw [mul_comm]]]
  rw [thm324_4 q hq r s hrs, Finset.sum_mul]
  simp_rw [smul_mul_assoc, Finset.mul_sum]
  rw [Finset.sum_image (mul_injOn_coprime_divisors _ _ hcop_rg)]
  rw [show ∑ x ∈ (q ^ r).divisors ×ˢ g.divisors,
    (↑(x.1 * x.2) : ℤ) • (T_ad' (x.1 * x.2) (x.1 * x.2) *
      T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (x.1 * x.2 * (x.1 * x.2)))) =
    ∑ d₁ ∈ (q ^ r).divisors, ∑ d₂ ∈ g.divisors,
      (↑(d₁ * d₂) : ℤ) • (T_ad' (d₁ * d₂) (d₁ * d₂) *
        T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (d₁ * d₂ * (d₁ * d₂)))) from
    by rw [← Finset.sum_product']]
  rw [Nat.sum_divisors_prime_pow hq]
  apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
  rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro d' hd'
  rw [show (↑q : ℤ) ^ i = (↑(q ^ i) : ℤ) from by push_cast; ring]
  exact T_sum_mul_peel_prime_summand q hq a b m' n' hqm hqn r s hr_def hs_def i hi d' hd'

/-- Theorem 3.24(3): `T(m) · T(n) = Σ_{d∣gcd(m,n)} d · T(d,d) · T(mn/d²)`.
    From Identity 4 at each prime + coprime multiplicativity. -/
theorem thm324_3 (m n : ℕ+) :
    T_sum m * T_sum n =
    ∑ d ∈ (Nat.gcd m n).divisors,
      (d : ℤ) • (T_ad' d d * T_sum_nat (↑m * ↑n / (d * d))) := by
  suffices h_ind : ∀ (g : ℕ) (m n : ℕ+), Nat.gcd m n = g →
    T_sum m * T_sum n =
    ∑ d ∈ g.divisors, (d : ℤ) • (T_ad' d d * T_sum_nat (↑m * ↑n / (d * d))) from
    h_ind _ m n rfl
  intro g; induction g using Nat.strongRecOn with | _ g ih =>
  intro m n h_gcd
  by_cases hg1 : g = 1
  · subst hg1; rw [Nat.divisors_one, Finset.sum_singleton]
    have := T_sum_mul_of_coprime_aux m n h_gcd
    rw [h_gcd, Nat.divisors_one, Finset.sum_singleton] at this; exact this
  · obtain ⟨q, hq, hq_dvd_g⟩ := Nat.exists_prime_and_dvd (by omega : g ≠ 1)
    have hq_dvd_m : q ∣ (m : ℕ) := dvd_trans hq_dvd_g (h_gcd ▸ Nat.gcd_dvd_left m n)
    have hq_dvd_n : q ∣ (n : ℕ) := dvd_trans hq_dvd_g (h_gcd ▸ Nat.gcd_dvd_right m n)
    set a_ord := m.val.factorization q; set b_ord := n.val.factorization q
    set m' : ℕ+ := ⟨ordCompl[q] m, Nat.ordCompl_pos q m.pos.ne'⟩
    set n' : ℕ+ := ⟨ordCompl[q] n, Nat.ordCompl_pos q n.pos.ne'⟩
    have hm_eq : (m : ℕ) = q ^ a_ord * m' := (Nat.ordProj_mul_ordCompl_eq_self m q).symm
    have hn_eq : (n : ℕ) = q ^ b_ord * n' := (Nat.ordProj_mul_ordCompl_eq_self n q).symm
    have ha : 0 < a_ord := (Nat.Prime.dvd_iff_one_le_factorization hq m.pos.ne').mp hq_dvd_m
    have hb : 0 < b_ord := (Nat.Prime.dvd_iff_one_le_factorization hq n.pos.ne').mp hq_dvd_n
    have hqm' : ¬ q ∣ (m' : ℕ) := Nat.not_dvd_ordCompl hq m.pos.ne'
    have hqn' : ¬ q ∣ (n' : ℕ) := Nat.not_dvd_ordCompl hq n.pos.ne'
    have h_smaller : Nat.gcd m' n' < g := by
      have hg_pos : 0 < g := h_gcd ▸ Nat.gcd_pos_of_pos_left _ m.pos
      have h1 : Nat.gcd (m' : ℕ) (n' : ℕ) ∣ g := h_gcd ▸ Nat.dvd_gcd
        ((Nat.gcd_dvd_left _ _).trans (Nat.ordCompl_dvd m q))
        ((Nat.gcd_dvd_right _ _).trans (Nat.ordCompl_dvd n q))
      have h2 : ¬ q ∣ Nat.gcd (m' : ℕ) (n' : ℕ) :=
        fun h => hqm' (h.trans (Nat.gcd_dvd_left _ _))
      exact lt_of_le_of_lt
        (Nat.le_of_dvd (Nat.div_pos (Nat.le_of_dvd hg_pos hq_dvd_g) hq.pos)
          (((Nat.Prime.coprime_iff_not_dvd hq).mpr h2).symm.dvd_of_dvd_mul_right
            ((Nat.div_mul_cancel hq_dvd_g).symm ▸ h1)))
        (Nat.div_lt_self hg_pos hq.one_lt)
    have ih_mn' := ih _ h_smaller m' n' rfl
    have h_peel := T_sum_mul_peel_prime_aux q hq a_ord b_ord ha hb m' n' hqm' hqn' ih_mn'
    have hm_pnat : m = ⟨q ^ a_ord * m', Nat.mul_pos (pow_pos hq.pos a_ord) m'.pos⟩ :=
      Subtype.ext hm_eq
    have hn_pnat : n = ⟨q ^ b_ord * n', Nat.mul_pos (pow_pos hq.pos b_ord) n'.pos⟩ :=
      Subtype.ext hn_eq
    rw [hm_pnat, hn_pnat,
      show g = Nat.gcd (q ^ a_ord * ↑m') (q ^ b_ord * ↑n') from by
        rw [← h_gcd, ← hm_eq, ← hn_eq]]
    convert h_peel using 2

/-! ### Identity 6: Degree formulas (wrapping existing results) -/

/-- Theorem 3.24(6): `deg(T(pⁱ, p^{i+k})) = p^{k-1}(p+1)` for k > 0. -/
theorem thm324_6 (i k : ℕ) (hk : 0 < k) :
    T'_deg (GL_pair 2) (T_diag 2 (![⟨p ^ i, pow_pos hp.pos i⟩,
      ⟨p ^ (i + k), pow_pos hp.pos (i + k)⟩])
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

/-- `deg` of a `T_ad` equals the `T'_deg` of its underlying double coset. -/
private lemma deg_T_ad' (a d : ℕ+) (h : (a : ℕ) ∣ (d : ℕ)) :
    deg (GL_pair 2) (T_ad a d h) =
    T'_deg (GL_pair 2) (T_diag 2 (![a, d]) (divChain_mk2 a d h)) := by
  show deg (GL_pair 2) (Finsupp.single (T_diag 2 (![a, d]) (divChain_mk2 a d h)) 1) = _
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
  show T'_deg (GL_pair 2) (T_diag 2 (![⟨p ^ i, pow_pos hp.pos i⟩, ⟨p ^ (k - i), pow_pos hp.pos (k - i)⟩] : Fin 2 → ℕ+)
    (divChain_mk2 _ _ (Nat.pow_dvd_pow p (by omega)))) = ↑(p ^ (k - 2 * i - 1) * (p + 1))
  have h_mk2_eq : (![⟨p ^ i, pow_pos hp.pos i⟩, ⟨p ^ (k - i), pow_pos hp.pos (k - i)⟩] : Fin 2 → ℕ+) =
      (![⟨p ^ i, pow_pos hp.pos i⟩, ⟨p ^ (i + (k - 2 * i)), pow_pos hp.pos (i + (k - 2 * i))⟩] : Fin 2 → ℕ+) := by
    ext j; fin_cases j <;> simp only [h_exp_eq]
  simp only [h_mk2_eq]
  exact thm324_6 p hp i (k - 2 * i) (by omega)

include hp in
/-- Scalar case: `deg(T_ad'(p^i, p^i)) = 1` when `2i = k`. -/
private lemma deg_ppow_term_eq' (i k : ℕ) (h2i : 2 * i = k) :
    deg (GL_pair 2) (T_ad' (p ^ i) (p ^ (k - i))) = 1 := by
  have hki : k - i = i := by omega
  rw [hki, deg_T_ad'_of_pos' _ _ (pow_pos hp.pos i) (pow_pos hp.pos i) (dvd_refl _), deg_T_ad']
  set c : ℕ+ := ⟨p ^ i, pow_pos hp.pos i⟩
  show T'_deg (GL_pair 2) (T_diag 2 (![c, c]) (divChain_mk2 c c (dvd_refl _))) = 1
  have hmk2 : ![c, c] = (fun (_ : Fin 2) => c) := funext fun j => by fin_cases j <;> rfl
  have h_diag_eq : T_diag 2 (![c, c]) (divChain_mk2 c c (dvd_refl _)) =
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
  ·
    have h_deg_lhs := deg_ppow_term_lt' p hp (i + 1) (k + 2) (by omega)
    have h_deg_rhs := deg_ppow_term_lt' p hp i k h2i
    have h_exp_eq : k + 2 - 2 * (i + 1) - 1 = k - 2 * i - 1 := by omega
    rw [h_deg_lhs, h_exp_eq, h_deg_rhs.symm]
  ·
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
  rw [T_sum_ppow_expansion p hp k, map_sum]
  match k with
  | 0 =>
    simp only [Nat.zero_div, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    have h0 := deg_ppow_term_eq' p hp 0 0 rfl
    simp only [pow_zero, Nat.sub_zero] at h0
    exact h0
  | 1 =>
    simp only [show (1 : ℕ) / 2 = 0 from rfl, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero]
    convert deg_ppow_term_lt' p hp 0 1 (by omega) using 1
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
    push_cast; ring
  | k + 2 =>
    have hdiv : (k + 2) / 2 = k / 2 + 1 := by omega
    rw [hdiv, Finset.sum_range_succ']
    have h_tail : ∑ i ∈ Finset.range (k / 2 + 1),
        (deg (GL_pair 2)) (T_ad' (p ^ (i + 1)) (p ^ (k + 2 - (i + 1)))) =
        ∑ i ∈ Finset.range (k / 2 + 1), (deg (GL_pair 2)) (T_ad' (p ^ i) (p ^ (k - i))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      exact deg_ppow_shift' p hp i k hi
    have h_i0 : deg (GL_pair 2) (T_ad' (p ^ 0) (p ^ (k + 2 - 0))) =
        ↑(p ^ (k + 1) * (p + 1)) := by
      have h_raw := deg_ppow_term_lt' p hp 0 (k + 2) (by omega)
      have : k + 2 - 0 - 1 = k + 1 := by omega
      simp only [this] at h_raw
      exact h_raw
    rw [h_tail, h_i0]
    have ih_k := ih k (by omega)
    rw [T_sum_ppow_expansion p hp k, map_sum] at ih_k
    simp only [] at ih_k
    rw [ih_k]
    conv_rhs =>
      rw [show k + 2 + 1 = (k + 1 + 1) + 1 from by omega]
      rw [Finset.sum_range_succ]
      rw [show k + 1 + 1 = (k + 1) + 1 from by omega]
      rw [Finset.sum_range_succ]
    push_cast; ring
/-- `deg(T_sum(1)) = 1`, used as base case for thm324_7. -/
private lemma deg_T_sum_one : deg (GL_pair 2) (T_sum 1) = 1 := by
  change deg (GL_pair 2) (∑ a ∈ Nat.divisors 1, T_ad' a (1 / a)) = 1
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  rw [deg_T_ad'_of_pos' 1 1 one_pos one_pos (dvd_refl 1), deg_T_ad']
  set c : ℕ+ := ⟨1, one_pos⟩
  show T'_deg (GL_pair 2) (T_diag 2 (![c, c]) (divChain_mk2 c c (dvd_refl _))) = 1
  have hmk2 : ![c, c] = (fun (_ : Fin 2) => c) := funext fun j => by fin_cases j <;> rfl
  have h_diag_eq : T_diag 2 (![c, c]) (divChain_mk2 c c (dvd_refl _)) =
      T_diag 2 (fun _ => c) (divChain_const 2 c) := by simp [hmk2]
  rw [h_diag_eq]
  exact thm324_6_scalar c

/-- Theorem 3.24(7): `deg(T(m)) = σ₁(m)`.
    By prime factorization + coprime multiplicativity + prime-power case. -/
theorem thm324_7 (m : ℕ+) :
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
    rw [deg_T_sum_prime_pow p hp k]
    simp only [ArithmeticFunction.sigma_one_apply]
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
    simp only [ArithmeticFunction.sigma_one_apply]
    exact_mod_cast (Nat.Coprime.sum_divisors_mul hcop).symm

end HeckeRing.GL2
