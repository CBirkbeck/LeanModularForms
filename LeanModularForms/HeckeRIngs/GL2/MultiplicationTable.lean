/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.Basic
import LeanModularForms.HeckeRIngs.GLn.Degree
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Shimura Theorem 3.24: Multiplication Table for GL₂ Hecke Algebra

The multiplication identities for the n=2 Hecke algebra (identities 1--5).
Degree formulas (identities 6--7) are in `GL2.Degree`.

## Main results

* `T_ad_one_ppow_eq` — `T(1,pᵏ) = T(pᵏ) − T(p,p) · T(p^{k−2})` for k ≥ 2
* `T_sum_mul` — `T(m) · T(n) = Σ d · T(d,d) · T(mn/d²)`
* `T_sum_ppow_mul` — `T(pʳ) · T(pˢ) = Σ pⁱ · T(pⁱ,pⁱ) · T(p^{r+s−2i})` for r ≤ s
* `T_sum_prime_mul_T_ad` — `T(p) · T(1,pᵏ) = T(1,p^{k+1}) + m · T(p,pᵏ)` (key computation)

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, Theorem 3.24
-/

open HeckeRing HeckeRing.GLn HeckeRing.GL2
open scoped ArithmeticFunction.sigma

namespace HeckeRing.GL2

/-- `SL_n(ℤ) → GL_n(ℚ)` has determinant 1 (replaces removed `SLnZ_to_GLnQ_det`). -/
@[simp]
lemma SLnZ_to_GLnQ_det {n : ℕ} [NeZero n] (S : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    (S : GL (Fin n) ℚ).val.det = 1 := by
  show (Matrix.SpecialLinearGroup.mapGL ℚ S).val.det = 1
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  exact_mod_cast (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ) S).prop

/-- `SL_n(ℤ) → GL_n(ℚ)` coercion as a matrix (replaces removed `SLnZ_to_GLnQ_val`). -/
@[simp]
lemma SLnZ_to_GLnQ_val {n : ℕ} [NeZero n] (S : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    ((S : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = (S.val).map (algebraMap ℤ ℚ) := by
  show (Matrix.SpecialLinearGroup.mapGL ℚ S).val = _
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]; rfl

variable (p : ℕ) (hp : p.Prime)

/-! ### Identity 1: T(m) = Σ T(a,d) — definitional

Shimura's T(m) is defined as `T_sum m`, which is exactly the sum
`Σ_{a ∣ m, a²∣m} T(a, m/a)`. This identity is the definition itself. -/

/-! ### Identity 2: Telescoping -/

section Telescoping

include hp in
/-- `T_ad(p^i, p^d)` unfolds to `T_ad` when `i ≤ d`. -/
private lemma T_ad_ppow (i d : ℕ) (hid : i ≤ d) :
    T_ad (p ^ i) (p ^ d) = T_elem ![p ^ i, p ^ d] := by
  rw [T_ad_of_pos _ _ (pow_pos hp.pos i) (pow_pos hp.pos d) (Nat.pow_dvd_pow p hid)]

include hp in
/-- `T_ad(1, p^k)` equals `T_ad 1 (p^k)`. -/
private lemma T_ad_one_ppow (k : ℕ) : T_ad 1 (p ^ k) = T_elem ![1, p ^ k] := by
  rw [T_ad_of_pos 1 (p ^ k) Nat.one_pos (pow_pos hp.pos k) (one_dvd _)]

include hp in
/-- Key shift: `T_pp(p) * T_ad(p^j, p^d) = T_ad(p^{j+1}, p^{d+1})` when `j ≤ d`. -/
private lemma T_pp_mul_T_ad_ppow (j d : ℕ) (hjd : j ≤ d) :
    T_pp p * T_ad (p ^ j) (p ^ d) = T_ad (p ^ (j + 1)) (p ^ (d + 1)) := by
  rw [T_ad_of_pos _ _ (pow_pos hp.pos j) (pow_pos hp.pos d) (Nat.pow_dvd_pow p hjd),
    T_ad_of_pos _ _ (pow_pos hp.pos (j + 1)) (pow_pos hp.pos (d + 1))
      (Nat.pow_dvd_pow p (by omega)),
    T_pp_comm_T_elem p hp (![p ^ j, p ^ d])
      (fun i => by fin_cases i <;> first | exact pow_pos hp.pos j | exact pow_pos hp.pos d)
      (fun i hi => by
        (have : i = 0 := by omega); subst this; simpa using Nat.pow_dvd_pow p hjd),
    T_pp_of_pos p hp,
    T_elem_mul_scalar (![p ^ j, p ^ d])
      (fun i => by fin_cases i <;> first | exact pow_pos hp.pos j | exact pow_pos hp.pos d)
      (fun i hi => by
        (have : i = 0 := by omega); subst this; simpa using Nat.pow_dvd_pow p hjd) p hp.pos]
  apply T_elem_congr_diag
  ext i; fin_cases i <;> simp [Pi.mul_apply, pow_succ, mul_comm]

/-- Theorem 3.24(2): `T(1, pᵏ) = T(pᵏ) − T(p,p) · T(p^{k−2})` for k ≥ 2.
    Proof strategy: T(pᵏ) = Σ T(pⁱ,p^{k-i}) and T(p,p)·T(p^{k-2}) shifts
    the index, giving a telescoping cancellation. -/
theorem T_ad_one_ppow_eq (k : ℕ) (hk : 2 ≤ k) :
    T_ad 1 (p ^ k) = T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    T_pp p * T_sum ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ := by
  suffices h : T_ad 1 (p ^ k) +
      T_pp p * T_sum ⟨p ^ (k - 2), pow_pos hp.pos (k - 2)⟩ =
      T_sum ⟨p ^ k, pow_pos hp.pos k⟩ by
    rw [eq_sub_iff_add_eq]; exact h
  rw [T_sum_ppow_expansion p hp k, T_sum_ppow_expansion p hp (k - 2), Finset.mul_sum]
  have shift : ∀ j ∈ Finset.range ((k - 2) / 2 + 1),
      T_pp p * T_ad (p ^ j) (p ^ (k - 2 - j)) =
      T_ad (p ^ (j + 1)) (p ^ (k - (j + 1))) := fun j hj => by
    rw [Finset.mem_range] at hj
    rw [T_pp_mul_T_ad_ppow p hp j (k - 2 - j) (by omega),
      show k - 2 - j + 1 = k - (j + 1) from by omega]
  rw [Finset.sum_congr rfl shift,
    show Finset.range ((k - 2) / 2 + 1) = Finset.range (k / 2) from by congr 1; omega,
    Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero]
  abel

end Telescoping

/-! ### Identity 5: The key recursion -/

/-- If `L * M * R = D` with `L`, `R` having determinant 1, then `M = L.adj * D * R.adj`. -/
lemma matrix_isolate_middle (L_ℤ M R_ℤ D : Matrix (Fin 2) (Fin 2) ℤ)
    (hLadj : L_ℤ.adjugate * L_ℤ = 1) (hRadj : R_ℤ * R_ℤ.adjugate = 1)
    (heq_LMR : L_ℤ * M * R_ℤ = D) : M = L_ℤ.adjugate * D * R_ℤ.adjugate := by
  ext i j
  have h1 := congr_arg (L_ℤ.adjugate * · * R_ℤ.adjugate) heq_LMR; simp only at h1
  have h2 : L_ℤ.adjugate * (L_ℤ * M * R_ℤ) * R_ℤ.adjugate = M := by
    have : L_ℤ.adjugate * (L_ℤ * M * R_ℤ) * R_ℤ.adjugate =
        (L_ℤ.adjugate * L_ℤ) * M * (R_ℤ * R_ℤ.adjugate) := by
      ext r s; simp only [Matrix.mul_apply, Fin.sum_univ_two]; ring
    rw [this, hLadj, hRadj, one_mul, mul_one]
  exact congr_arg (· i j) (h2 ▸ h1)

private lemma first_invariant_dvd_p_of_product (S : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (a : Fin 2 → ℕ) (_ha_pos : ∀ i, 0 < a i) (hdiv : DivChain 2 a)
    (L R : Matrix.SpecialLinearGroup (Fin 2) ℤ) (k : ℕ) (_hk : 0 < k)
    (heq : (L : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p] : Fin 2 → ℤ) *
      (S : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p ^ k] : Fin 2 → ℤ) *
      (R : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.diagonal (fun i => (a i : ℤ))) : a 0 ∣ p := by
  set dp := Matrix.diagonal (![1, p] : Fin 2 → ℤ)
  set dpk := Matrix.diagonal (fun m => ((![1, p ^ k] : Fin 2 → ℕ) m : ℤ))
  set S_ℤ := (↑S : Matrix (Fin 2) (Fin 2) ℤ)
  set M := dp * S_ℤ * dpk
  set L_ℤ := (↑L : Matrix (Fin 2) (Fin 2) ℤ)
  set R_ℤ := (↑R : Matrix (Fin 2) (Fin 2) ℤ)
  have hLadj : L_ℤ.adjugate * L_ℤ = 1 := by rw [Matrix.adjugate_mul, L.prop, one_smul]
  have hRadj : R_ℤ * R_ℤ.adjugate = 1 := by rw [Matrix.mul_adjugate, R.prop, one_smul]
  have hM_eq : M = L_ℤ.adjugate * Matrix.diagonal (fun i => (a i : ℤ)) * R_ℤ.adjugate :=
    matrix_isolate_middle L_ℤ M R_ℤ _ hLadj hRadj (by
      have : L_ℤ * M * R_ℤ = L_ℤ * dp * S_ℤ * dpk * R_ℤ := by
        ext i j; simp only [M, S_ℤ, Matrix.mul_apply, Fin.sum_univ_two]; ring
      rw [this]; exact heq)
  have h_dvd_entry : ∀ i j : Fin 2, (a 0 : ℤ) ∣ M i j := by
    intro i j; rw [hM_eq]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Fin.sum_univ_two,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply dvd_add
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (dvd_refl _) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
        (show (a 0 : ℤ) ∣ (a 1 : ℤ) from by exact_mod_cast hdiv 0 (by omega)) _) _
  have h_M00 : M 0 0 = S_ℤ 0 0 := by
    simp only [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 2) ≠ 0 from by decide,
      if_false, if_true, mul_zero, add_zero, Matrix.cons_val_fin_one]; norm_num
  have h_M10 : M 1 0 = (p : ℤ) * S_ℤ 1 0 := by
    simp only [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, show (1 : Fin 2) ≠ 0 from by decide,
      if_false, if_true, mul_zero, zero_mul, add_zero, Matrix.cons_val_fin_one]; norm_num
  have h_cop : IsCoprime (S_ℤ 0 0) (S_ℤ 1 0) :=
    ⟨S.val 1 1, -(S.val 0 1), by
      have := S.prop; rw [Matrix.det_fin_two] at this; linarith⟩
  have h1 : (a 0 : ℤ) ∣ S_ℤ 0 0 := h_M00 ▸ h_dvd_entry 0 0
  have h2 : (a 0 : ℤ) ∣ (p : ℤ) * S_ℤ 1 0 := h_M10 ▸ h_dvd_entry 1 0
  exact_mod_cast (by
    obtain ⟨u, v, huv⟩ := h_cop; obtain ⟨t, ht⟩ := h1
    exact ⟨u * t, v, by
      rw [show u * t * ↑(a 0) = u * (↑(a 0) * t) from by ring, ← ht]; exact huv⟩
    : IsCoprime (↑(a 0) : ℤ) (S_ℤ 1 0)).dvd_of_dvd_mul_right h2

private lemma mulSupport_pp_det_eq (k : ℕ) (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
    (g₁ g₂ g₃ g₄ : GL (Fin 2) ℚ) (h1 : g₁.val.det = 1) (h2 : g₂.val.det = (p : ℚ))
    (h3 : g₃.val.det = 1) (h4 : g₄.val.det = (p : ℚ) ^ k)
    (SL_La SL_Ra : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_eq : g₁ * g₂ * (g₃ * g₄) =
      (SL_La : GL (Fin 2) ℚ) * diagMat 2 a * (SL_Ra : GL (Fin 2) ℚ)) :
    a 0 * a 1 = p ^ (k + 1) := by
  have h_lhs : (g₁ * g₂ * (g₃ * g₄)).val.det = (p : ℚ) ^ (k + 1) := by
    simp only [Units.val_mul, Matrix.det_mul, h1, h2, h3, h4]; ring
  have h_rhs : (g₁ * g₂ * (g₃ * g₄)).val.det = (a 0 : ℚ) * (a 1 : ℚ) := by
    rw [h_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul]
    simp only [SLnZ_to_GLnQ_det, diagMat_det 2 _ ha_pos, Fin.prod_univ_two, one_mul, mul_one]
  exact_mod_cast show (a 0 : ℚ) * (a 1 : ℚ) = (p : ℚ) ^ (k + 1) by linarith

include hp in
private lemma mulSupport_pp_dvd_p_aux
    (S_mid L' R' : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (hdiv : DivChain 2 a) (k : ℕ) (_hk : 0 < k)
    (h_gl : (L' : GL (Fin 2) ℚ) * diagMat 2 (![1, p]) * (S_mid : GL (Fin 2) ℚ) *
      diagMat 2 (![1, p ^ k]) * (R' : GL (Fin 2) ℚ) = diagMat 2 a) : a 0 ∣ p := by
  have h_int_5 : (↑L' : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p] : Fin 2 → ℤ) *
      (↑S_mid : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p ^ k] : Fin 2 → ℤ) *
      (↑R' : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.diagonal (fun i => (a i : ℤ)) := by
    ext i j
    have h := congr_arg
      (fun (g : GL (Fin 2) ℚ) => (↑g : Matrix _ _ ℚ) i j) h_gl
    have h1p : ∀ i : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) i := by
      intro i; fin_cases i <;> simp [hp.pos]
    have h1pk : ∀ i : Fin 2, 0 < (![1, p ^ k] : Fin 2 → ℕ) i := by
      intro i; fin_cases i <;> simp [pow_pos hp.pos k]
    simp only [diagMat_val 2 _ ha_pos, diagMat_val 2 _ h1p, diagMat_val 2 _ h1pk,
      Matrix.diagonal_apply, Units.val_mul, SLnZ_to_GLnQ_val, Matrix.mul_apply,
      Matrix.map_apply, algebraMap_int_eq, Int.coe_castRingHom] at h
    simp only [Matrix.diagonal_apply, Matrix.mul_apply]
    exact_mod_cast h
  exact first_invariant_dvd_p_of_product p S_mid a ha_pos hdiv L' R' k _hk h_int_5

include hp in
private lemma mulSupport_pp_dvd_p (k : ℕ) (_hk : 0 < k) (a : Fin 2 → ℕ)
    (ha_pos : ∀ i, 0 < a i) (hdiv : DivChain 2 a) (D1c D2c i₀_gl j₀_gl : GL (Fin 2) ℚ)
    (SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀ SL_j₀ :
      Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hD1_eq : D1c = (SL_L₁ : GL (Fin 2) ℚ) * diagMat 2 (![1, p]) * (SL_R₁ : GL (Fin 2) ℚ))
    (hD2_eq : D2c = (SL_L₂ : GL (Fin 2) ℚ) * diagMat 2 (![1, p ^ k]) *
      (SL_R₂ : GL (Fin 2) ℚ))
    (hi₀ : i₀_gl = (SL_i₀ : GL (Fin 2) ℚ)) (hj₀ : j₀_gl = (SL_j₀ : GL (Fin 2) ℚ))
    (h_prod_eq_a : i₀_gl * D1c * (j₀_gl * D2c) =
      (SL_La : GL (Fin 2) ℚ) * diagMat 2 a * (SL_Ra : GL (Fin 2) ℚ)) : a 0 ∣ p := by
  set S_mid := SL_R₁ * SL_j₀ * SL_L₂
  set L' := SL_La⁻¹ * SL_i₀ * SL_L₁
  set R' := SL_R₂ * SL_Ra⁻¹
  apply @mulSupport_pp_dvd_p_aux p hp S_mid L' R' a ha_pos
    hdiv k _hk
  set dp := diagMat 2 (![1, p])
  set dpk := diagMat 2 (![1, p ^ k])
  set da := diagMat 2 a
  have hprod : (SL_i₀ : GL (Fin 2) ℚ) *
      ((SL_L₁ : GL (Fin 2) ℚ) * dp * (SL_R₁ : GL (Fin 2) ℚ)) *
      ((SL_j₀ : GL (Fin 2) ℚ) *
        ((SL_L₂ : GL (Fin 2) ℚ) * dpk * (SL_R₂ : GL (Fin 2) ℚ))) =
      (SL_La : GL (Fin 2) ℚ) * da * (SL_Ra : GL (Fin 2) ℚ) := by
    rw [← hi₀, ← hj₀, ← hD1_eq, ← hD2_eq]
    exact h_prod_eq_a
  have := congr_arg₂ (· * ·) (congr_arg ((SL_La : GL (Fin 2) ℚ)⁻¹ * ·) hprod)
    (show (SL_Ra : GL (Fin 2) ℚ)⁻¹ = (SL_Ra : GL (Fin 2) ℚ)⁻¹ from rfl)
  simp only [mul_assoc, inv_mul_cancel_left] at this
  simp only [L', R', S_mid, map_mul, map_inv] at this ⊢
  convert this using 1; group

include hp in
private lemma mulSupport_pp_case_split (k : ℕ) (_hk : 0 < k) (a : Fin 2 → ℕ)
    (_ha_pos : ∀ i, 0 < a i) (_hdiv : DivChain 2 a)
    (h_det_prod : a 0 * a 1 = p ^ (k + 1)) (h_dvd_p : a 0 ∣ p) :
    T_diag a = T_diag (![1, p ^ (k + 1)]) ∨
    T_diag a = T_diag (![p, p ^ k]) := by
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (a 0) h_dvd_p with ha0_1 | ha0_p
  · left; congr 1; ext i; fin_cases i
    · exact ha0_1
    · simp; rw [ha0_1, one_mul] at h_det_prod; exact h_det_prod
  · right; congr 1; ext i; fin_cases i
    · exact ha0_p
    · simp
      have h1 : p * a 1 = p ^ (k + 1) := by rwa [ha0_p] at h_det_prod
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h1, pow_succ]; ring)

include hp in
private lemma mulSupport_pp_subset (k : ℕ) (_hk : 0 < k) (A : HeckeCoset (GL_pair 2))
    (hA : A ∈ HeckeRing.mulSupport (GL_pair 2) (T_diag (![1, p]))
      (T_diag (![1, p ^ k]))) :
    A = T_diag (![1, p ^ (k + 1)]) ∨ A = T_diag (![p, p ^ k]) := by
  obtain ⟨a, ha_pos, hdiv, hrep⟩ := exists_diagonal_representative 2 A.doubleCoset_eq.choose
  have hA_eq : A = T_diag a := by
    rw [← hrep]; exact (HeckeCoset_ext _ _ _ A.doubleCoset_eq.choose_spec.symm).symm
  set D1 := T_diag (![1, p])
  set D2 := T_diag (![1, p ^ k])
  rw [HeckeRing.mulSupport] at hA
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists] at hA
  obtain ⟨i₀, j₀, hmap⟩ := hA
  obtain ⟨L₁, ⟨SL_L₁, rfl⟩, R₁, ⟨SL_R₁, rfl⟩, hD1_eq⟩ := T_diag_rep_decompose (![1, p])
    (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact hp.pos)
  obtain ⟨L₂, ⟨SL_L₂, rfl⟩, R₂, ⟨SL_R₂, rfl⟩, hD2_eq⟩ := T_diag_rep_decompose (![1, p ^ k])
    (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos k)
  have h_prod_in_A : (↑i₀.out : GL (Fin 2) ℚ) * D1.doubleCoset_eq.choose *
      ((↑j₀.out : GL (Fin 2) ℚ) * D2.doubleCoset_eq.choose) ∈ A.carrier := by
    rw [← hmap]; simp only [HeckeRing.mulMap, HeckeRing.HeckeCoset.mk']
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [hA_eq] at h_prod_in_A
  simp only [T_diag, HeckeRing.HeckeCoset.mk', diagMat_delta_val _ _ ha_pos] at h_prod_in_A
  rw [DoubleCoset.mem_doubleCoset] at h_prod_in_A
  obtain ⟨L_a, ⟨SL_La, rfl⟩, R_a, ⟨SL_Ra, rfl⟩, h_prod_eq⟩ := h_prod_in_A
  obtain ⟨SL_i₀, hSL_i₀⟩ := (i₀.out : ↥(GL_pair 2).H).2
  obtain ⟨SL_j₀, hSL_j₀⟩ := (j₀.out : ↥(GL_pair 2).H).2
  have h_det := mulSupport_pp_det_eq p k a ha_pos (↑i₀.out) D1.doubleCoset_eq.choose (↑j₀.out)
    D2.doubleCoset_eq.choose
    (by rw [show (↑i₀.out : GL _ ℚ) = (SL_i₀ : GL (Fin 2) ℚ) from hSL_i₀.symm]
        exact SLnZ_to_GLnQ_det SL_i₀)
    (by rw [hD1_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          SLnZ_to_GLnQ_det, SLnZ_to_GLnQ_det]
        rw [diagMat_det 2 (![1, p])
          (by intro ⟨i, hi⟩; interval_cases i <;> simp [hp.pos])]
        simp [Fin.prod_univ_two])
    (by rw [show (↑j₀.out : GL _ ℚ) = (SL_j₀ : GL (Fin 2) ℚ) from hSL_j₀.symm]
        exact SLnZ_to_GLnQ_det SL_j₀)
    (by rw [hD2_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          SLnZ_to_GLnQ_det, SLnZ_to_GLnQ_det]
        rw [diagMat_det 2 (![1, p ^ k])
          (by intro ⟨i, hi⟩; interval_cases i <;> simp [pow_pos hp.pos k])]
        simp [Fin.prod_univ_two])
    SL_La SL_Ra h_prod_eq
  have h_dvd := mulSupport_pp_dvd_p p hp k _hk a ha_pos hdiv D1.doubleCoset_eq.choose
    D2.doubleCoset_eq.choose (↑i₀.out) (↑j₀.out) SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀
    SL_j₀ hD1_eq hD2_eq hSL_i₀.symm hSL_j₀.symm h_prod_eq
  rw [hA_eq]; exact mulSupport_pp_case_split p hp k _hk a ha_pos hdiv h_det h_dvd

include hp in
/-- `diagMat 2 (![1, p]) * diagMat 2 (![1, p^k]) = diagMat 2 (![1, p^{k+1}])` -/
private lemma diagMat_mul_ppow (k : ℕ) :
    (diagMat 2 (![1, p]) : GL (Fin 2) ℚ) * diagMat 2 (![1, p ^ k]) =
      diagMat 2 (![1, p ^ (k + 1)]) := by
  rw [diagMat_mul 2 (![1, p]) (![1, p ^ k])
    (by intro i; fin_cases i <;> simp [hp.pos])
    (by intro i; fin_cases i <;> simp [pow_pos hp.pos k])]
  congr 1; ext i; fin_cases i <;> simp [Pi.mul_apply, pow_succ, mul_comm]

include hp in
private lemma D_out1_pp_in_mulSupport (k : ℕ) (_hk : 0 < k) :
    T_diag (![1, p ^ (k + 1)]) ∈ HeckeRing.mulSupport (GL_pair 2)
      (T_diag (![1, p])) (T_diag (![1, p ^ k])) := by
  set D1 := T_diag (![1, p])
  set D2 := T_diag (![1, p ^ k])
  set D_out1 := T_diag (![1, p ^ (k + 1)])
  set α := (D1.doubleCoset_eq.choose : GL (Fin 2) ℚ)
  set β := (D2.doubleCoset_eq.choose : GL (Fin 2) ℚ)
  obtain ⟨L₁, hL₁, R₁, hR₁, hα_eq⟩ := T_diag_rep_decompose (![1, p])
    (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact hp.pos)
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ_eq⟩ := T_diag_rep_decompose (![1, p ^ k])
    (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos k)
  set i₀ : decompQuot (GL_pair 2) D1 := ⟦⟨L₁⁻¹, (GL_pair 2).H.inv_mem hL₁⟩⟧
  open scoped Pointwise in
  obtain ⟨κ₁, hκ₁_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (D1.doubleCoset_eq.choose : GL (Fin 2) ℚ) •
      (GL_pair 2).H).subgroupOf (GL_pair 2).H)
    ⟨L₁⁻¹, (GL_pair 2).H.inv_mem hL₁⟩
  have hi₀ : (↑i₀.out : GL (Fin 2) ℚ) = L₁⁻¹ * (κ₁ : (GL_pair 2).H) := by
    apply_fun (↑· : ↥(GL_pair 2).H → GL (Fin 2) ℚ) at hκ₁_eq
    simpa [Subgroup.coe_mul] using hκ₁_eq
  have hκ₁_conj : α⁻¹ * (κ₁.val : GL (Fin 2) ℚ) * α ∈ (GL_pair 2).H := by
    have := κ₁.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this; simpa [ConjAct.ofConjAct_toConjAct] using this
  set τ₀ : GL (Fin 2) ℚ :=
    (α⁻¹ * (κ₁.val : GL (Fin 2) ℚ) * α)⁻¹ * R₁⁻¹ * L₂⁻¹
  have hτ₀_mem : τ₀ ∈ (GL_pair 2).H :=
    (GL_pair 2).H.mul_mem ((GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hκ₁_conj)
      ((GL_pair 2).H.inv_mem hR₁)) ((GL_pair 2).H.inv_mem hL₂)
  set j₀ : decompQuot (GL_pair 2) D2 := ⟦⟨τ₀, hτ₀_mem⟩⟧
  open scoped Pointwise in
  obtain ⟨κ₂, hκ₂_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (D2.doubleCoset_eq.choose : GL (Fin 2) ℚ) •
      (GL_pair 2).H).subgroupOf (GL_pair 2).H)
    ⟨τ₀, hτ₀_mem⟩
  have hj₀ : (↑j₀.out : GL (Fin 2) ℚ) = τ₀ * (κ₂ : (GL_pair 2).H) := by
    apply_fun (↑· : ↥(GL_pair 2).H → GL (Fin 2) ℚ) at hκ₂_eq
    simpa [Subgroup.coe_mul] using hκ₂_eq
  have hκ₂_conj : β⁻¹ * (κ₂.val : GL (Fin 2) ℚ) * β ∈ (GL_pair 2).H := by
    have := κ₂.2; rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this; simpa [ConjAct.ofConjAct_toConjAct] using this
  have h_product_mem : (↑i₀.out : GL (Fin 2) ℚ) * α *
      ((↑j₀.out : GL (Fin 2) ℚ) * β) ∈ DoubleCoset.doubleCoset
        ((diagMat 2 (![1, p ^ (k + 1)])) : GL (Fin 2) ℚ)
        (GL_pair 2).H (GL_pair 2).H := by
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨1, (GL_pair 2).H.one_mem,
      R₂ * (β⁻¹ * (κ₂.val : GL (Fin 2) ℚ) * β),
      (GL_pair 2).H.mul_mem hR₂ hκ₂_conj, ?_⟩
    rw [hi₀, hj₀, show α = L₁ * diagMat 2 (![1, p]) * R₁ from hα_eq,
        show β = L₂ * diagMat 2 (![1, p ^ k]) * R₂ from hβ_eq]
    set D₁_mat := diagMat 2 (![1, p])
    set D₂_mat := diagMat 2 (![1, p ^ k])
    have h_D_mul : D₁_mat * D₂_mat = diagMat 2 (![1, p ^ (k + 1)]) := diagMat_mul_ppow p hp k
    rw [one_mul, ← h_D_mul]
    simp only [show τ₀ =
      (α⁻¹ * (κ₁.val : GL (Fin 2) ℚ) * α)⁻¹ * R₁⁻¹ * L₂⁻¹ from rfl,
               show α = L₁ * D₁_mat * R₁ from hα_eq]
    group
  rw [HeckeRing.mulSupport]; simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and, Prod.exists]
  exact ⟨i₀, j₀, by
    apply HeckeRing.HeckeCoset_ext (GL_pair 2)
    show (HeckeRing.mulMap (GL_pair 2) D1 D2 (i₀, j₀)).carrier = D_out1.carrier
    rw [HeckeRing.mulMap, HeckeRing.HeckeCoset.mk']
    simp only
    conv_rhs => rw [show D_out1 = HeckeRing.HeckeCoset.mk' (GL_pair 2)
        (diagMat_delta 2 (![1, p ^ (k + 1)])) from rfl,
      HeckeRing.HeckeCoset.mk']
    simp only
    rw [show (diagMat_delta 2 (![1, p ^ (k + 1)]) : GL (Fin 2) ℚ) =
      diagMat 2 (![1, p ^ (k + 1)]) from diagMat_delta_val _ _
        (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos (k + 1))]
    exact DoubleCoset.doubleCoset_eq_of_mem h_product_mem⟩

/-- The degree sum `m1 * deg(D_out1) + m2 * deg(D_out2) = deg(D1) * deg(D2)` when
    the mulSupport of `D1 * D2` is contained in `{D_out1, D_out2}`. -/
private lemma heckeMultiplicity_deg_sum_eq (D1 D2 D_out1 D_out2 : HeckeCoset (GL_pair 2))
    (h_ne : D_out1 ≠ D_out2) (h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 A = 0) :
    HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 D_out1 * HeckeCoset_deg (GL_pair 2) D_out1 +
      HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 D_out2 * HeckeCoset_deg (GL_pair 2) D_out2 =
      HeckeCoset_deg (GL_pair 2) D1 * HeckeCoset_deg (GL_pair 2) D2 := by
  have h1 : HeckeRing.deg (GL_pair 2) (HeckeRing.m (GL_pair 2) D1 D2) =
      HeckeCoset_deg (GL_pair 2) D1 * HeckeCoset_deg (GL_pair 2) D2 := by
    rw [← HeckeRing.T_single_one_mul_T_single_one, HeckeRing.deg_mul,
      HeckeRing.deg_T_single, HeckeRing.deg_T_single]; ring
  have h2 : HeckeRing.deg (GL_pair 2) (HeckeRing.m (GL_pair 2) D1 D2) =
      HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 D_out1 * HeckeCoset_deg (GL_pair 2) D_out1 +
        HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 D_out2 *
          HeckeCoset_deg (GL_pair 2) D_out2 := by
    open scoped Classical in
    simp only [HeckeRing.deg, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      HeckeRing.deg_fun]
    have hsub : (HeckeRing.m (GL_pair 2) D1 D2).support ⊆ ({D_out1, D_out2} : Finset _) := by
      intro A hA; simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [Finsupp.mem_support_iff] at hA
      exact (or_iff_not_imp_left.mpr fun h1 =>
        (Classical.em (A = D_out2)).elim id fun h2 => absurd (h_zero A h1 h2) hA)
    exact Finset.sum_subset hsub (by
      intro A _ hA; rw [Finsupp.notMem_support_iff.mp hA]; simp) |>.trans
      (Finset.sum_pair h_ne)
  linarith

include hp in
private lemma heckeMultiplicity_values (k : ℕ) (hk : 0 < k) :
    HeckeRing.heckeMultiplicity (GL_pair 2) (T_diag (![1, p])) (T_diag (![1, p ^ k]))
      (T_diag (![1, p ^ (k + 1)])) = 1 ∧
    HeckeRing.heckeMultiplicity (GL_pair 2) (T_diag (![1, p])) (T_diag (![1, p ^ k]))
      (T_diag (![p, p ^ k])) = if k = 1 then ↑(p + 1) else ↑p := by
  set D1 := T_diag (![1, p])
  set D2 := T_diag (![1, p ^ k])
  set D_out1 := T_diag (![1, p ^ (k + 1)])
  set D_out2 := T_diag (![p, p ^ k])
  set m1 := HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 D_out1
  set m2 := HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 D_out2
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have h1_pos : ∀ i : Fin 2, 0 < (![1, p ^ (k + 1)]) i := by
      intro i; fin_cases i <;> simp [pow_pos hp.pos]
    have h2_pos : ∀ i : Fin 2, 0 < (![p, p ^ k]) i := by
      intro i; fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
    have h1_div : DivChain 2 (![1, p ^ (k + 1)]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simp
    have h2_div : DivChain 2 (![p, p ^ k]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega)
    have := diagonal_representative_unique 2 _ _ h1_pos h2_pos h1_div h2_div heq
    have := congr_fun this 0; simp only [Matrix.cons_val_zero] at this
    exact absurd this.symm (Nat.Prime.one_lt hp).ne'
  have h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 A = 0 := by
    intro A h1 h2; apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport
    intro hmem; exact (mulSupport_pp_subset p hp k hk A hmem).elim h1 h2
  have h_deg : m1 * HeckeCoset_deg (GL_pair 2) D_out1 + m2 * HeckeCoset_deg (GL_pair 2) D_out2 =
      HeckeCoset_deg (GL_pair 2) D1 * HeckeCoset_deg (GL_pair 2) D2 :=
    heckeMultiplicity_deg_sum_eq D1 D2 D_out1 D_out2 h_ne h_zero
  have hm1_nn := HeckeRing.heckeMultiplicity_nonneg (GL_pair 2) D1 D2 D_out1
  have hm2_nn := HeckeRing.heckeMultiplicity_nonneg (GL_pair 2) D1 D2 D_out2
  have hm1_pos : 1 ≤ m1 := by
    have hne : (HeckeRing.m (GL_pair 2) D1 D2) D_out1 ≠ 0 := by
      rw [← Finsupp.mem_support_iff, HeckeRing.m_support]
      exact D_out1_pp_in_mulSupport p hp k hk
    exact Int.lt_iff_add_one_le.mp (lt_of_le_of_ne hm1_nn (Ne.symm hne))
  rw [show HeckeCoset_deg (GL_pair 2) D1 = ↑(p + 1) from by
      simpa using HeckeCoset_deg_T_diag_two_prime p hp (![1, p])
        (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact hp.pos)
        (fun i hi => by (have : i = 0 := by omega); subst this; simp) 1 one_pos (by simp [pow_one]),
    show HeckeCoset_deg (GL_pair 2) D2 = ↑(p ^ (k - 1) * (p + 1)) from
      HeckeCoset_deg_T_diag_two_prime p hp _
        (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos k)
        (fun i hi => by (have : i = 0 := by omega); subst this; simp) k hk (by simp),
    show HeckeCoset_deg (GL_pair 2) D_out1 = ↑(p ^ k * (p + 1)) from
      HeckeCoset_deg_T_diag_two_prime p hp _
        (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos (k + 1))
        (fun i hi => by (have : i = 0 := by omega); subst this; simp) (k + 1) (by omega) (by simp)] at h_deg
  by_cases hk1 : k = 1
  · subst hk1; simp only [ite_true, show 1 - 1 = 0 from rfl, pow_zero, one_mul] at h_deg ⊢
    have hd_o2 : HeckeCoset_deg (GL_pair 2) D_out2 = 1 := HeckeCoset_deg_T_diag_two_scalar _
        (fun i => by fin_cases i <;> first | exact hp.pos | exact pow_pos hp.pos 1)
        (fun i hi => by (have : i = 0 := by omega); subst this; simp [pow_one])
        (by show (![p, p ^ 1] : Fin 2 → ℕ) 0 = (![p, p ^ 1] : Fin 2 → ℕ) 1; simp [pow_one])
    rw [hd_o2] at h_deg; push_cast at h_deg ⊢
    have h_m1_eq : m1 = 1 := by
      nlinarith [mul_self_nonneg ((p : ℤ) - 1), show (2 : ℤ) ≤ p from by exact_mod_cast hp.two_le]
    exact ⟨h_m1_eq, by rw [h_m1_eq] at h_deg; linarith⟩
  · simp only [show k ≠ 1 from hk1, ite_false]; have hk2 : 2 ≤ k := by omega
    have hd_o2 : HeckeCoset_deg (GL_pair 2) D_out2 = ↑(p ^ (k - 2) * (p + 1)) :=
      HeckeCoset_deg_T_diag_two_prime p hp _
        (by intro i; fin_cases i <;> first | exact hp.pos | exact pow_pos hp.pos k)
        (fun i hi => by
          have hi0 : i = 0 := by omega
          subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega))
        (k - 1) (by omega)
        (by show p ^ k / p = p ^ (k - 1)
            have : p ^ k = p ^ (k - 1) * p := by
              rw [← pow_succ]; congr 1; omega
            rw [this, Nat.mul_div_cancel _ hp.pos])
    rw [hd_o2] at h_deg
    have hp2 : (2 : ℤ) ≤ p := by exact_mod_cast hp.two_le
    have hpk : (p : ℤ) ^ k = (p : ℤ) ^ (k - 2) * (p : ℤ) ^ 2 := by
      exact_mod_cast show (p : ℕ) ^ k = p ^ (k - 2) * p ^ 2 by rw [← pow_add]; congr 1; omega
    have hpk1 : (p : ℤ) ^ (k - 1) = (p : ℤ) ^ (k - 2) * p := by
      have : (p : ℕ) ^ (k - 1) = p ^ (k - 2) * p ^ 1 := by rw [← pow_add]; congr 1; omega
      simp only [pow_one] at this; exact_mod_cast this
    push_cast at h_deg ⊢
    have h_eq : m1 * (p : ℤ) ^ 2 + m2 = (p : ℤ) * ((p : ℤ) + 1) := by
      have h := h_deg; rw [hpk, hpk1] at h
      have key : (p : ℤ) ^ (k - 2) * ((p : ℤ) + 1) ≠ 0 := by positivity
      have := mul_right_cancel₀ key (show
        (m1 * (p : ℤ) ^ 2 + m2) * ((p : ℤ) ^ (k - 2) * ((p : ℤ) + 1)) =
        ((p : ℤ) * ((p : ℤ) + 1)) * ((p : ℤ) ^ (k - 2) * ((p : ℤ) + 1)) by nlinarith)
      linarith
    have h_m1_eq : m1 = 1 := by
      have h_le : m1 * (p : ℤ) ^ 2 ≤ (p : ℤ) ^ 2 + p := by linarith [h_eq, hm2_nn]
      nlinarith [show (p : ℤ) ^ 2 ≥ 4 by nlinarith]
    exact ⟨h_m1_eq, by rw [h_m1_eq] at h_eq; linarith⟩

/-- Theorem 3.24(5): `T(p) · T(1, pᵏ) = T(1, p^{k+1}) + m · T(p, pᵏ)` -/
theorem T_sum_prime_mul_T_ad (k : ℕ) (hk : 0 < k) :
    T_sum ⟨p, hp.pos⟩ * T_ad 1 (p ^ k) = T_ad 1 (p ^ (k + 1)) +
      (if k = 1 then (↑(p + 1) : ℤ) else (↑p : ℤ)) • T_ad p (p ^ k) := by
  rw [T_sum_prime p hp]
  set D1 := T_diag (![1, p])
  set D2 := T_diag (![1, p ^ k])
  set D_out1 := T_diag (![1, p ^ (k + 1)])
  set D_out2 := T_diag (![p, p ^ k])
  set c : ℤ := (if k = 1 then (↑(p + 1) : ℤ) else (↑p : ℤ))
  have h_ne : D_out1 ≠ D_out2 := by
    intro heq
    have h1_pos : ∀ i : Fin 2, 0 < (![1, p ^ (k + 1)]) i := by
      intro i; fin_cases i <;> simp [pow_pos hp.pos]
    have h2_pos : ∀ i : Fin 2, 0 < (![p, p ^ k]) i := by
      intro i; fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
    have h1_div : DivChain 2 (![1, p ^ (k + 1)]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simp
    have h2_div : DivChain 2 (![p, p ^ k]) := fun i hi => by
      have hi0 : i = 0 := by omega
      subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega)
    have := congr_fun (diagonal_representative_unique 2 _ _
      h1_pos h2_pos h1_div h2_div heq) 0
    exact absurd this.symm (Nat.Prime.one_lt hp).ne'
  have h_ad_1p : T_ad 1 p = T_elem (![1, p]) := T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)
  have h_ad_1pk : T_ad 1 (p ^ k) = T_elem (![1, p ^ k]) :=
    T_ad_of_pos 1 (p ^ k) Nat.one_pos (pow_pos hp.pos k) (one_dvd _)
  have h_ad_1pk1 : T_ad 1 (p ^ (k + 1)) = T_elem (![1, p ^ (k + 1)]) :=
    T_ad_of_pos 1 (p ^ (k + 1)) Nat.one_pos (pow_pos hp.pos (k + 1)) (one_dvd _)
  have h_ad_ppk : T_ad p (p ^ k) = T_elem (![p, p ^ k]) :=
    T_ad_of_pos p (p ^ k) hp.pos (pow_pos hp.pos k) (dvd_pow_self p (by omega))
  rw [h_ad_1p, h_ad_1pk, h_ad_1pk1, h_ad_ppk]
  have h_mul : T_elem (![1, p]) * T_elem (![1, p ^ k]) =
      HeckeRing.m (GL_pair 2) D1 D2 := HeckeRing.T_single_one_mul_T_single_one (GL_pair 2) D1 D2
  have h_rhs : T_elem (![1, p ^ (k + 1)]) + c • T_elem (![p, p ^ k]) =
      Finsupp.single D_out1 1 + c • Finsupp.single D_out2 1 := rfl
  rw [h_mul, h_rhs, Finsupp.smul_single', mul_one]
  apply Finsupp.ext; intro A
  show HeckeRing.heckeMultiplicity (GL_pair 2) D1 D2 A =
    (Finsupp.single D_out1 (1 : ℤ) + Finsupp.single D_out2 c) A
  rw [Finsupp.add_apply]
  by_cases h1 : A = D_out1
  · subst h1
    rw [Finsupp.single_eq_same, Finsupp.single_eq_of_ne h_ne, add_zero]
    exact (heckeMultiplicity_values p hp k hk).1
  · by_cases h2 : A = D_out2
    · subst h2
      rw [Finsupp.single_eq_of_ne (Ne.symm h_ne), Finsupp.single_eq_same, zero_add]
      exact (heckeMultiplicity_values p hp k hk).2
    · rw [Finsupp.single_eq_of_ne h1, Finsupp.single_eq_of_ne h2, add_zero]
      apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport
      intro hmem
      exact (mulSupport_pp_subset p hp k hk A hmem).elim h1 h2

/-- `T_sum(1) = 1`: the sum over divisor pairs of 1 is the identity. -/
lemma T_sum_one : T_sum 1 = (1 : HeckeAlgebra 2) := by
  show ∑ a ∈ Nat.divisors 1, T_ad a (1 / a) = 1
  simp only [Nat.divisors_one, Finset.sum_singleton, Nat.div_self one_pos]
  unfold T_ad
  rw [dif_pos ⟨one_pos, one_pos, dvd_refl 1⟩]
  exact T_ad_one_one

include hp in
/-- `T_ad(p, p^k) = T_pp * T_ad(1, p^{k-1})` for `k ≥ 1`.
    Consequence of `T_pp_mul_T_ad_ppow` with j=0. -/
private lemma T_ad_p_ppow_eq (k : ℕ) (hk : 0 < k) :
    T_ad p (p ^ k) = T_pp p * T_ad 1 (p ^ (k - 1)) := by
  have h0 := T_pp_mul_T_ad_ppow p hp 0 (k - 1) (Nat.zero_le _)
  simp only [pow_zero, zero_add, pow_one] at h0
  rw [show k - 1 + 1 = k from Nat.succ_pred_eq_of_pos hk] at h0
  exact h0.symm

include hp in
private lemma T_pp_comm_T_ad_one_p : T_pp p * T_ad 1 p = T_ad 1 p * T_pp p := by
  rw [T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)]
  exact T_pp_comm_T_elem p hp _
    (fun i => by fin_cases i <;> first | exact Nat.one_pos | exact hp.pos)
    (fun i hi => by (have : i = 0 := by omega); subst this; simp)

/-- `T_sum(p^0) = 1`. -/
private lemma T_sum_ppow_zero : T_sum ⟨p ^ 0, pow_pos hp.pos 0⟩ = 1 := by
  show T_sum 1 = 1; exact T_sum_one

/-- `T_ad(1, p^0) = 1`. -/
private lemma T_ad_one_ppow_zero : T_ad 1 (p ^ 0) = 1 := by simp only [pow_zero]; exact T_ad_one_one

/-- `T_ad(1, p^1) = T_ad(1, p)`: normalize `p^1` to `p`. -/
private lemma T_ad_one_ppow_one : T_ad 1 (p ^ 1) = T_ad 1 p := by simp only [pow_one]

/-- The `k+2` inductive step of `T_sum_ppow_recurrence` when `k ≥ 1`.
    Uses the IH at `k` to substitute the recurrence, then concludes by algebra. -/
private lemma T_sum_ppow_recurrence_step (k : ℕ) (hk_pos : 0 < k)
    (ih : ∀ j : ℕ, j < k + 2 → 0 < j →
      T_sum ⟨p ^ (j + 1), pow_pos hp.pos (j + 1)⟩ = T_sum ⟨p, hp.pos⟩ *
        T_sum ⟨p ^ j, pow_pos hp.pos j⟩ -
        (p : ℤ) • (T_pp p * T_sum ⟨p ^ (j - 1), pow_pos hp.pos (j - 1)⟩)) :
    T_sum ⟨p ^ (k + 2 + 1), pow_pos hp.pos (k + 2 + 1)⟩ = T_sum ⟨p, hp.pos⟩ *
      T_sum ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩ -
      (p : ℤ) • (T_pp p * T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩) := by
  have h5 := T_sum_prime_mul_T_ad p hp (k + 2) (by omega)
  rw [T_ad_p_ppow_eq p hp (k + 2) (by omega)] at h5
  have h2 := T_ad_one_ppow_eq p hp (k + 2 + 1) (by omega)
  conv at h2 => rhs; rw [show (k + 2 + 1) - 2 = k + 1 from by omega]
  rw [h2] at h5
  simp only [show k + 2 ≠ 1 from by omega, ite_false,
             show k + 2 - 1 = k + 1 from by omega] at h5
  rw [T_ad_one_ppow_eq p hp (k + 2) (by omega), mul_sub] at h5
  have h2k1 := T_ad_one_ppow_eq p hp (k + 1) (by omega)
  conv at h2k1 => rhs; rw [show (k + 1) - 2 = k - 1 from by omega]
  rw [h2k1] at h5
  conv at h5 => lhs; rw [show k + 2 - 2 = k from by omega]
  conv at h5 => rhs; rw [show T_pp p *
      (T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ -
       T_pp p * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) =
      T_pp p * T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ -
      T_pp p * (T_pp p * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩)
    from mul_sub _ _ _]
  rw [smul_sub,
    ← mul_assoc (T_sum ⟨p, hp.pos⟩) (T_pp p)
      (T_sum ⟨p ^ k, pow_pos hp.pos k⟩),
    show T_sum ⟨p, hp.pos⟩ * T_pp p = T_pp p * T_sum ⟨p, hp.pos⟩ from by
    rw [T_sum_prime p hp]; exact (T_pp_comm_T_ad_one_p p hp).symm,
    mul_assoc (T_pp p) (T_sum ⟨p, hp.pos⟩)
      (T_sum ⟨p ^ k, pow_pos hp.pos k⟩),
    show T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
      T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ +
      (↑p : ℤ) • (T_pp p *
        T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) from by
    rw [ih k (by omega) hk_pos]; abel,
    mul_add (T_pp p), mul_smul_comm (↑p : ℤ),
    ← mul_assoc (T_pp p) (T_pp p), sub_eq_iff_eq_add] at h5
  have h6 : T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩ =
      T_sum ⟨p ^ (k + 2 + 1), pow_pos hp.pos (k + 2 + 1)⟩ +
      (↑p : ℤ) • (T_pp p * T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩) := by
    rw [h5]; abel
  exact eq_sub_iff_add_eq.mpr h6.symm

/-- Theorem 3.24(6 recurrence): `T(p^{k+1}) = T(p) T(p^k) - p T(p,p) T(p^{k-1})` for k >= 1. -/
theorem T_sum_ppow_recurrence : ∀ k : ℕ, 0 < k →
    T_sum ⟨p ^ (k + 1), pow_pos hp.pos (k + 1)⟩ =
    T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ -
    (p : ℤ) • (T_pp p * T_sum ⟨p ^ (k - 1), pow_pos hp.pos (k - 1)⟩) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro hk
  have h5 := T_sum_prime_mul_T_ad p hp k hk
  rw [T_ad_p_ppow_eq p hp k hk] at h5
  have h2 := T_ad_one_ppow_eq p hp (k + 1) (by omega)
  conv at h2 => rhs; rw [show (k + 1) - 2 = k - 1 from by omega]
  rw [h2] at h5
  match k, hk, ih with
  | 1, _, _ =>
    simp only [show (1 : ℕ) - 1 = 0 from rfl, ite_true] at h5 ⊢
    rw [T_sum_ppow_zero p hp, T_ad_one_ppow_zero, mul_one] at h5
    rw [T_sum_ppow_zero p hp, mul_one,
      show T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ from
      by congr 1; exact Subtype.ext (pow_one p)]
    rw [T_ad_one_ppow_one, T_sum_prime p hp] at h5
    rw [T_sum_prime p hp]
    rw [show (↑(p + 1) : ℤ) • T_pp p = (↑p : ℤ) • T_pp p + T_pp p from by
      rw [show (↑(p + 1) : ℤ) = (↑p : ℤ) + 1 from by push_cast; ring,
        add_smul, one_smul]] at h5
    rw [eq_sub_iff_add_eq]; have h5' := h5; abel_nf at h5' ⊢; exact h5'.symm
  | 2, _, _ =>
    simp only [show (2 : ℕ) ≠ 1 from by omega, ite_false,
               show (2 : ℕ) - 1 = 1 from by omega] at h5 ⊢
    rw [T_ad_one_ppow_eq p hp 2 (by omega), mul_sub] at h5
    simp only [show 2 - 2 = 0 from rfl] at h5 ⊢
    rw [T_sum_ppow_zero p hp, mul_one, T_ad_one_ppow_one, T_sum_prime p hp] at h5
    rw [show T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ from
      by congr 1; exact Subtype.ext (pow_one p)] at h5 ⊢
    rw [T_sum_prime p hp] at h5 ⊢
    rw [(T_pp_comm_T_ad_one_p p hp).symm] at h5
    rw [sub_eq_iff_eq_add] at h5; rw [eq_sub_iff_add_eq]
    have h5' := h5; abel_nf at h5' ⊢; exact h5'.symm
  | k + 3, _, ih =>
    exact T_sum_ppow_recurrence_step p hp (k + 1) (by omega) ih

/-! ### Identity 4: General prime-power product -/

/-- Theorem 3.24(4): `T(pʳ) · T(pˢ) = Σ_{i=0}^{r} pⁱ · T(pⁱ,pⁱ) · T(p^{r+s−2i})`
    for r ≤ s. Proved by induction on r using `T_sum_ppow_recurrence`. -/
private lemma T_pp_comm_T_sum_ppow (k : ℕ) : T_pp p * T_sum ⟨p ^ k, pow_pos hp.pos k⟩ =
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ * T_pp p := by
  rw [T_sum_ppow_expansion p hp k, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro i _
  by_cases h : 0 < p ^ i ∧ 0 < p ^ (k - i) ∧ p ^ i ∣ p ^ (k - i)
  · obtain ⟨_, _, hdvd⟩ := h
    rw [T_ad_of_pos (p ^ i) (p ^ (k - i)) (pow_pos hp.pos i) (pow_pos hp.pos (k - i)) hdvd]
    exact T_pp_comm_T_elem p hp _
      (fun i' => by fin_cases i' <;> first | exact pow_pos hp.pos i | exact pow_pos hp.pos (k - i))
      (fun i' hi' => by (have : i' = 0 := by omega); subst this; simpa using hdvd)
  · simp [T_ad_eq_zero h, mul_zero, zero_mul]

private lemma T_pp_pow_comm_T_sum_ppow (i k : ℕ) : T_pp p ^ i *
    T_sum ⟨p ^ k, pow_pos hp.pos k⟩ = T_sum ⟨p ^ k, pow_pos hp.pos k⟩ * T_pp p ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ', mul_assoc, ih, ← mul_assoc, T_pp_comm_T_sum_ppow p hp k,
      mul_assoc, ← pow_succ']

private lemma T_sum_p_comm_T_pp_pow (i : ℕ) : T_sum ⟨p, hp.pos⟩ * T_pp p ^ i =
    T_pp p ^ i * T_sum ⟨p, hp.pos⟩ := by
  rw [show T_sum ⟨p, hp.pos⟩ =
    T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ from by congr 1; exact (Subtype.ext (pow_one p)).symm]
  exact (T_pp_pow_comm_T_sum_ppow p hp i 1).symm

private lemma T_sum_p_comm_T_pp_pow_T_sum (i k : ℕ) : T_sum ⟨p, hp.pos⟩ *
    (T_pp p ^ i * T_sum ⟨p ^ k, pow_pos hp.pos k⟩) =
    T_pp p ^ i * (T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ k, pow_pos hp.pos k⟩) := by
  rw [← mul_assoc, T_sum_p_comm_T_pp_pow p hp i, mul_assoc]

/-- Each summand of `Tp * S1` splits into two terms via the recurrence. -/
private lemma T_sum_ppow_mul_summand_split (r s i : ℕ) (hi : i ≤ r) (hrs : r ≤ s) :
    (p : ℤ) ^ i • (T_pp p ^ i *
      (T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
    (p : ℤ) ^ i • (T_pp p ^ i *
      T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩) +
    (p : ℤ) ^ (i + 1) • (T_pp p ^ (i + 1) *
      T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
  have h_pos : 0 < r + 1 + s - 2 * i := by omega
  have h_rec_i := T_sum_ppow_recurrence p hp (r + 1 + s - 2 * i) h_pos
  rw [show (r + 1 + s - 2 * i) + 1 = r + 2 + s - 2 * i from by omega,
      show r + 1 + s - 2 * i - 1 = r + s - 2 * i from by omega] at h_rec_i
  have h_eq : T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩ =
      T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩ +
      (p : ℤ) • (T_pp p * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
    rw [eq_sub_iff_add_eq] at h_rec_i; exact h_rec_i.symm
  rw [h_eq, mul_add, smul_add]
  congr 1
  rw [mul_smul_comm, smul_smul, show (p : ℤ) ^ i * (p : ℤ) = (p : ℤ) ^ (i + 1) from by ring]
  congr 1
  rw [← mul_assoc, ← pow_succ]

/-- Distribute `T(p)` into each summand of S1 using commutativity. -/
private lemma T_sum_ppow_mul_lhs1_distrib (r s : ℕ) :
    T_sum ⟨p, hp.pos⟩ *
      (∑ i ∈ Finset.range (r + 1 + 1),
        (p : ℤ) ^ i • (T_pp p ^ i *
          T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
    ∑ i ∈ Finset.range (r + 1 + 1),
      (p : ℤ) ^ i • (T_pp p ^ i *
        (T_sum ⟨p, hp.pos⟩ *
          T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [mul_smul_comm, T_sum_p_comm_T_pp_pow_T_sum p hp i _, ← mul_assoc]

/-- Distribute `p • (Tpp * S2)` into a shifted-index sum. -/
private lemma T_sum_ppow_mul_lhs2_shift (r s : ℕ) : (p : ℤ) • (T_pp p *
      ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (T_pp p ^ i *
          T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)) =
    ∑ i ∈ Finset.range (r + 1),
      (p : ℤ) ^ (i + 1) • (T_pp p ^ (i + 1) *
        T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
  rw [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [mul_smul_comm, smul_smul, mul_comm ((p : ℤ)) ((p : ℤ) ^ i), ← pow_succ]
  congr 1; rw [← mul_assoc, ← pow_succ']

/-- The last two summands of `T_sum_ppow_mul` for the `r + 2` case: expand the top-index term
    using the recurrence for `T(p^{s-r-1})`. -/
private lemma T_sum_ppow_mul_last_two_terms (r s : ℕ) (hrs : r + 2 ≤ s) :
    (p : ℤ) ^ (r + 1) • (T_pp p ^ (r + 1) *
      (T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩)) =
    (p : ℤ) ^ (r + 1) • (T_pp p ^ (r + 1) *
      T_sum ⟨p ^ (r + 2 + s - 2 * (r + 1)), pow_pos hp.pos _⟩) +
    (p : ℤ) ^ (r + 2) • (T_pp p ^ (r + 2) *
      T_sum ⟨p ^ (r + 2 + s - 2 * (r + 2)), pow_pos hp.pos _⟩) := by
  have hexp_C : r + 1 + s - 2 * (r + 1) = s - r - 1 := by omega
  have h_sr_pos : 0 < s - r - 1 := by omega
  have h_rec_final := T_sum_ppow_recurrence p hp (s - r - 1) h_sr_pos
  rw [show (s - r - 1) + 1 = s - r from by omega,
      show s - r - 1 - 1 = s - r - 2 from by omega] at h_rec_final
  have h_expand : T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (s - r - 1), pow_pos hp.pos _⟩ =
      T_sum ⟨p ^ (s - r), pow_pos hp.pos _⟩ +
      (p : ℤ) • (T_pp p * T_sum ⟨p ^ (s - r - 2), pow_pos hp.pos _⟩) := by
    rw [eq_sub_iff_add_eq] at h_rec_final; exact h_rec_final.symm
  rw [hexp_C, h_expand, mul_add, smul_add, mul_smul_comm, smul_smul,
      show (p : ℤ) ^ (r + 1) * (p : ℤ) = (p : ℤ) ^ (r + 2) from by ring,
      ← mul_assoc,
      show T_pp p ^ (r + 1) * T_pp p = T_pp p ^ (r + 2) from
        (pow_succ (T_pp p) (r + 1)).symm]
  have hnat2 : s - r - 2 = r + 2 + s - 2 * (r + 2) := by omega
  have hnat1 : s - r = r + 2 + s - 2 * (r + 1) := by omega
  rw [hnat2, hnat1]

/-- Theorem 3.24(4): `T(p^r) T(p^s) = sum_{i=0}^{r} p^i T(p^i,p^i) T(p^{r+s-2i})` for r <= s. -/
theorem T_sum_ppow_mul : ∀ r s : ℕ, r ≤ s →
    T_sum ⟨p ^ r, pow_pos hp.pos r⟩ * T_sum ⟨p ^ s, pow_pos hp.pos s⟩ =
    ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i •
      (T_pp p ^ i * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
  intro s hrs
  match r with
  | 0 =>
    rw [Finset.sum_range_one]
    simp only [Nat.zero_add, pow_zero, one_smul, one_mul]
    rw [show T_sum (⟨1, pow_pos hp.pos 0⟩ : ℕ+) = 1 from by
      rw [show (⟨1, pow_pos hp.pos 0⟩ : ℕ+) = (1 : ℕ+) from
        Subtype.ext rfl]; exact T_sum_one, one_mul]; simp
  | 1 =>
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp only [pow_zero, one_smul, one_mul, pow_one]
    conv_rhs =>
      rw [show 1 + s - 2 * 0 = s + 1 from by omega,
          show 1 + s - 2 * 1 = s - 1 from by omega]
    exact (eq_sub_iff_add_eq.mp (T_sum_ppow_recurrence p hp s (by omega))).symm
  | r + 2 =>
    have h_rec := T_sum_ppow_recurrence p hp (r + 1) (by omega)
    simp only [show r + 1 - 1 = r from by omega] at h_rec
    rw [show r + 1 + 1 = r + 2 from by omega] at h_rec
    rw [h_rec, sub_mul]
    have ih1 := ih (r + 1) (by omega) s (by omega)
    have ih0 := ih r (by omega) s (by omega)
    rw [mul_assoc, ih1, smul_mul_assoc, mul_assoc (T_pp p), ih0]
    set Tp := T_sum ⟨p, hp.pos⟩ with Tp_def
    set Tpp := T_pp p with Tpp_def
    set S1 := ∑ i ∈ Finset.range (r + 1 + 1),
      (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)
    set S2 := ∑ i ∈ Finset.range (r + 1),
      (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)
    have h_lhs1 : Tp * S1 = ∑ i ∈ Finset.range (r + 1 + 1), (p : ℤ) ^ i • (Tpp ^ i *
          (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) :=
      T_sum_ppow_mul_lhs1_distrib p hp r s
    have h_lhs2 : (p : ℤ) • (Tpp * S2) = ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ (i + 1) •
          (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩) :=
      T_sum_ppow_mul_lhs2_shift p hp r s
    have h_peel1 : ∑ i ∈ Finset.range (r + 1 + 1), (p : ℤ) ^ i • (Tpp ^ i *
          (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
      (∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (Tpp ^ i *
          (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩))) +
      (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) *
        (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩)) :=
      Finset.sum_range_succ _ _
    have h_sum_split : ∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (Tpp ^ i *
          (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * i), pow_pos hp.pos _⟩)) =
      (∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ i • (Tpp ^ i *
          T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩)) +
      (∑ i ∈ Finset.range (r + 1), (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) *
          T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i hi => by
        rw [Finset.mem_range] at hi
        exact T_sum_ppow_mul_summand_split p hp r s i (by omega) (by omega)
    rw [h_lhs1, h_peel1, h_sum_split, h_lhs2]
    set A := ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ i • (Tpp ^ i * T_sum ⟨p ^ (r + 2 + s - 2 * i), pow_pos hp.pos _⟩)
    set B := ∑ i ∈ Finset.range (r + 1),
        (p : ℤ) ^ (i + 1) • (Tpp ^ (i + 1) * T_sum ⟨p ^ (r + s - 2 * i), pow_pos hp.pos _⟩)
    set C := (p : ℤ) ^ (r + 1) • (Tpp ^ (r + 1) *
      (Tp * T_sum ⟨p ^ (r + 1 + s - 2 * (r + 1)), pow_pos hp.pos _⟩))
    show A + B + C - B = _
    rw [add_assoc, add_comm B C, ← add_assoc, add_sub_cancel_right,
      show r + 2 + 1 = (r + 1) + 1 + 1 from by omega,
      Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    congr 1
    exact T_sum_ppow_mul_last_two_terms p hp r s hrs

/-! ### Identity 3: General multiplicativity -/

section CoprimeMultiplicativity

open Finset in
/-- `∏ i, (![a, d]) i (![a, d]) = a * d`. -/
private lemma prod_mk2 (a d : ℕ) :
    ∏ i, (![a, d]) i = a * d := by
  simp [Fin.prod_univ_two]

/-- Coprime factoring: `T(a,da) T(b,db) = T(ab,da*db)` when `a*da` and `b*db` are coprime. -/
lemma T_ad_mul_of_coprime (a b da db : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hda : 0 < da) (hdb : 0 < db) (hdva : a ∣ da) (hdvb : b ∣ db)
    (hcop : Nat.Coprime (a * da) (b * db)) :
    T_ad a da * T_ad b db = T_ad (a * b) (da * db) := by
  rw [T_ad_of_pos a da ha hda hdva, T_ad_of_pos b db hb hdb hdvb,
      T_ad_of_pos (a * b) (da * db) (Nat.mul_pos ha hb)
        (Nat.mul_pos hda hdb) (Nat.mul_dvd_mul hdva hdvb)]
  have ha_pos : ∀ i, 0 < ![a, da] i := fun i => by fin_cases i <;> first | exact ha | exact hda
  have hb_pos : ∀ i, 0 < ![b, db] i := fun i => by fin_cases i <;> first | exact hb | exact hdb
  have ha_div : DivChain 2 (![a, da]) := fun i hi => by
    (have : i = 0 := by omega); subst this; simpa using hdva
  have hb_div : DivChain 2 (![b, db]) := fun i hi => by
    (have : i = 0 := by omega); subst this; simpa using hdvb
  have hab_pos : ∀ i, 0 < ![a * b, da * db] i := fun i => by
    fin_cases i <;> first | exact Nat.mul_pos ha hb | exact Nat.mul_pos hda hdb
  have hab_div_mul : DivChain 2 ((![a, da]) * (![b, db])) := fun i hi => by
    simp only [Pi.mul_apply]; (have : i = 0 := by omega); subst this; exact Nat.mul_dvd_mul hdva hdvb
  have hab_div : DivChain 2 (![a * b, da * db]) := fun i hi => by
    (have : i = 0 := by omega); subst this; exact Nat.mul_dvd_mul hdva hdvb
  have mul_eq : (![a, da]) * (![b, db]) = ![a * b, da * db] := by
    ext i; fin_cases i <;> simp [Pi.mul_apply]
  rw [← show T_elem ((![a, da]) * (![b, db])) = T_elem ![a * b, da * db] by simp only [mul_eq]]
  exact T_diag_mul_coprime 2 (![a, da]) (![b, db]) ha_pos hb_pos ha_div hb_div
    (by rw [prod_mk2, prod_mk2]; exact hcop)

/-- When `T_ad` conditions fail, the product is zero and so is the RHS. -/
private lemma T_ad_mul_zero_of_not_dvd (a da : ℕ) (h : ¬(0 < a ∧ 0 < da ∧ a ∣ da))
    (x : HeckeAlgebra 2) : T_ad a da * x = 0 := by rw [show T_ad a da = 0 from dif_neg h, zero_mul]

private lemma T_ad_mul_zero_of_not_dvd' (b db : ℕ) (h : ¬(0 < b ∧ 0 < db ∧ b ∣ db))
    (x : HeckeAlgebra 2) : x * T_ad b db = 0 := by rw [show T_ad b db = 0 from dif_neg h, mul_zero]

/-- The multiplication map on `m.divisors ×ˢ n.divisors` is injective when `m` and `n`
    are coprime. -/
lemma mul_injOn_coprime_divisors (m n : ℕ) (hcop : Nat.Coprime m n) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 * p.2) (↑(m.divisors ×ˢ n.divisors)) := by
  intro ⟨a₁, b₁⟩ h₁ ⟨a₂, b₂⟩ h₂ heq
  simp only [Finset.mem_coe, Finset.mem_product, Nat.mem_divisors] at h₁ h₂
  simp only at heq
  have hcop₁₂ : Nat.Coprime a₁ b₂ :=
    (hcop.coprime_dvd_left h₁.1.1).coprime_dvd_right h₂.2.1
  have hcop₂₁ : Nat.Coprime a₂ b₁ :=
    (hcop.coprime_dvd_left h₂.1.1).coprime_dvd_right h₁.2.1
  have haeq : a₁ = a₂ := Nat.dvd_antisymm
    (hcop₁₂.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a₁ b₁))
    (hcop₂₁.dvd_of_dvd_mul_right (heq ▸ dvd_mul_right a₂ b₂))
  have ha_pos : 0 < a₁ := Nat.pos_of_ne_zero fun h => by simp [h] at h₁
  exact Prod.ext haeq (Nat.eq_of_mul_eq_mul_left ha_pos (haeq ▸ heq))

/-- Theorem 3.24(3a): coprime multiplicativity `T(m) T(n) = T(mn)` when `gcd(m,n) = 1`. -/
theorem T_sum_mul_coprime (m n : ℕ+) (hcop : Nat.Coprime m n) :
    T_sum m * T_sum n = T_sum ⟨m * n, Nat.mul_pos m.pos n.pos⟩ := by
  open scoped Pointwise in
  set M := (m : ℕ) with hM; set N := (n : ℕ) with hN
  change (∑ a ∈ M.divisors, T_ad a (M / a)) * (∑ b ∈ N.divisors, T_ad b (N / b)) =
    ∑ c ∈ (M * N).divisors, T_ad c ((M * N) / c)
  open scoped Pointwise in
  rw [Finset.sum_mul_sum, Nat.divisors_mul,
    show (Nat.divisors M * Nat.divisors N) =
    (Nat.divisors M ×ˢ Nat.divisors N).image (fun p => p.1 * p.2) from rfl,
    Finset.sum_image (mul_injOn_coprime_divisors M N hcop), ← Finset.sum_product']
  apply Finset.sum_congr rfl
  intro ⟨a, b⟩ hab
  simp only [Finset.mem_product, Nat.mem_divisors] at hab
  have ha_pos : 0 < a := Nat.pos_of_ne_zero (fun h => by simp [h] at hab)
  have hb_pos : 0 < b := Nat.pos_of_ne_zero (fun h => by simp [h] at hab)
  rw [(Nat.div_mul_div_comm hab.1.1 hab.2.1).symm]
  by_cases hca : a ∣ (M / a)
  · by_cases hcb : b ∣ (N / b)
    · apply T_ad_mul_of_coprime a b (M / a) (N / b) ha_pos hb_pos
        (Nat.div_pos (Nat.le_of_dvd (by omega) hab.1.1) ha_pos)
        (Nat.div_pos (Nat.le_of_dvd (by omega) hab.2.1) hb_pos)
        hca hcb
      rwa [hM, hN, Nat.mul_div_cancel' hab.1.1, Nat.mul_div_cancel' hab.2.1]
    ·
      rw [T_ad_mul_zero_of_not_dvd' b (N / b)
        (by push_neg; intro _ _; exact hcb) (T_ad a (M / a))]
      symm; unfold T_ad; rw [dif_neg]; push_neg
      intro _ _ hdvd; apply hcb
      exact ((hcop.symm.coprime_dvd_left hab.2.1).coprime_dvd_right
        (Nat.div_dvd_of_dvd hab.1.1)).dvd_of_dvd_mul_left
        (dvd_trans (dvd_mul_left b a) hdvd)
  ·
    rw [T_ad_mul_zero_of_not_dvd a (M / a)
      (by push_neg; intro _ _; exact hca)]
    symm; unfold T_ad; rw [dif_neg]; push_neg
    intro _ _ hdvd; apply hca
    exact ((hcop.coprime_dvd_left hab.1.1).coprime_dvd_right
      (Nat.div_dvd_of_dvd hab.2.1)).dvd_of_dvd_mul_right
      (dvd_trans (dvd_mul_right a b) hdvd)

end CoprimeMultiplicativity

/-- T_sum extended to ℕ: agrees with `T_sum` for positive arguments, zero for 0. -/
noncomputable def T_sum_nat (k : ℕ) : HeckeAlgebra 2 :=
  ∑ a ∈ k.divisors, T_ad a (k / a)

/-- `T_sum_nat` agrees with `T_sum` on positive naturals. -/
lemma T_sum_nat_eq (k : ℕ+) : T_sum_nat (k : ℕ) = T_sum k := rfl

private lemma T_ad_self_eq_T_elem (c : ℕ) (hc : 0 < c) : T_ad c c = T_elem (fun _ => c) := by
  rw [T_ad_of_pos c c hc hc (dvd_refl c)]
  exact T_elem_congr_diag 2 (funext fun j => by fin_cases j <;> rfl)

/-- `T_pp q ^ i = T_ad (q^i) (q^i)` : the `i`-th power of `T(p,p)` equals `T_ad(p^i, p^i)`. -/
private lemma T_pp_pow_eq_T_ad (q : ℕ) (hq : q.Prime) (i : ℕ) : T_pp q ^ i =
    T_ad (q ^ i) (q ^ i) := by
  rw [T_ad_self_eq_T_elem _ (pow_pos hq.pos i), T_pp_pow q hq i]

/-- `gcd(q^r, q^s) = q^r` when `r <= s`. -/
lemma gcd_pow_pow_of_le (q : ℕ) (r s : ℕ) (hrs : r ≤ s) : Nat.gcd (q ^ r) (q ^ s) = q ^ r :=
  Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd (dvd_refl _) (Nat.pow_dvd_pow q hrs))

/-- Prime-power product in divisor-sum form. -/
private lemma T_sum_mul_prime_pow_aux (q : ℕ) (hq : q.Prime) (r s : ℕ) (hrs : r ≤ s) :
    T_sum ⟨q ^ r, pow_pos hq.pos r⟩ * T_sum ⟨q ^ s, pow_pos hq.pos s⟩ = ∑ d ∈
      (Nat.gcd (q ^ r) (q ^ s)).divisors, (d : ℤ) • (T_ad d d *
        T_sum_nat (q ^ r * q ^ s / (d * d))) := by
  rw [T_sum_ppow_mul q hq r s hrs, gcd_pow_pow_of_le q r s hrs, Nat.sum_divisors_prime_pow hq]
  apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
  rw [show (q ^ i : ℤ) = (↑(q ^ i) : ℤ) by push_cast; ring, T_pp_pow_eq_T_ad q hq i]
  congr 2
  rw [← pow_add, ← pow_add,
    show i + i = 2 * i from by ring,
    Nat.pow_div (by omega) hq.pos]
  exact (T_sum_nat_eq ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩).symm

/-- Coprime base case for the divisor sum formula. -/
private lemma T_sum_mul_of_coprime_aux (m n : ℕ+) (hcop : Nat.Coprime m n) :
    T_sum m * T_sum n = ∑ d ∈ (Nat.gcd m n).divisors,
      (d : ℤ) • (T_ad d d * T_sum_nat (↑m * ↑n / (d * d))) := by
  rw [show Nat.gcd m n = 1 from hcop, Nat.divisors_one, Finset.sum_singleton]
  simp only [Nat.cast_one, one_smul, one_mul, T_ad_one_one, one_mul, Nat.div_one]
  rw [T_sum_mul_coprime m n hcop]; rfl

/-- GCD factoring: `gcd(q^a * m', q^b * n') = q^(min a b) * gcd(m', n')`. -/
lemma gcd_factor_prime_pow (q : ℕ) (hq : q.Prime) (a b : ℕ) (m' n' : ℕ+)
    (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ)) :
    Nat.gcd (q ^ a * m') (q ^ b * n') = q ^ min a b * Nat.gcd m' n' := by
  have hcop_qm : Nat.Coprime (q ^ a) m' := (Nat.Prime.coprime_pow_of_not_dvd hq hqm).symm
  have hcop_qn : Nat.Coprime (q ^ b) n' := (Nat.Prime.coprime_pow_of_not_dvd hq hqn).symm
  have hcop_rg : Nat.Coprime (q ^ min a b) (Nat.gcd m' n') :=
    (Nat.Prime.coprime_pow_of_not_dvd hq (fun h => hqm (dvd_trans h (Nat.gcd_dvd_left _ _)))).symm
  apply Nat.eq_of_factorization_eq (Nat.gcd_pos_of_pos_left _
      (Nat.mul_pos (pow_pos hq.pos a) m'.pos)).ne'
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
    simp only [Finsupp.single_apply, Nat.factorization_eq_zero_of_not_dvd hqm,
      Nat.factorization_eq_zero_of_not_dvd hqn, add_zero, min_zero]; rfl
  · rw [Nat.Prime.factorization_pow hq, Nat.Prime.factorization_pow hq,
      Nat.Prime.factorization_pow hq]; simp only [Finsupp.single_apply,
      show q ≠ p' from Ne.symm hpq, if_false, zero_add]

/-- RHS computation for the inner summand: T_sum_nat product equals the combined quotient. -/
private lemma T_sum_mul_peel_prime_summand_rhs (q : ℕ) (hq : q.Prime) (a b : ℕ) (m' n' : ℕ+)
    (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ)) (r s : ℕ) (hr : r = min a b)
    (hs : s = max a b) (i : ℕ) (hi : i < r + 1) (d' : ℕ) (hd'_dvd : d' ∣ Nat.gcd (m' : ℕ) n')
    (_hqd' : ¬ q ∣ d') (_hcop_qi_d' : Nat.Coprime (q ^ i) d') (hd'_pos : 0 < d') :
    T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ *
      T_sum_nat (↑m' * ↑n' / (d' * d')) =
    T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (q ^ i * d' * (q ^ i * d'))) := by
  have hq_ndvd_mn : ¬ q ∣ ↑m' * ↑n' := fun h =>
    hqm ((hq.dvd_mul.mp h).elim id (fun h' => absurd h' hqn))
  have hq_ndvd_quot : ¬ q ∣ ↑m' * ↑n' / (d' * d') := fun h => hq_ndvd_mn (dvd_trans h
    (Nat.div_dvd_of_dvd (Nat.mul_dvd_mul (dvd_trans hd'_dvd (Nat.gcd_dvd_left _ _))
      (dvd_trans hd'_dvd (Nat.gcd_dvd_right _ _)))))
  have h_quot_pos : 0 < ↑m' * ↑n' / (d' * d') := Nat.div_pos
    (Nat.le_of_dvd (Nat.mul_pos m'.pos n'.pos) (Nat.mul_dvd_mul
      (dvd_trans hd'_dvd (Nat.gcd_dvd_left _ _))
      (dvd_trans hd'_dvd (Nat.gcd_dvd_right _ _)))) (Nat.mul_pos hd'_pos hd'_pos)
  change T_sum_nat ↑(⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ : ℕ+) *
    T_sum_nat (↑m' * ↑n' / (d' * d')) =
    T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (q ^ i * d' * (q ^ i * d')))
  rw [show (⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ : ℕ+).val = q ^ (r + s - 2 * i) from rfl,
    show T_sum_nat (q ^ (r + s - 2 * i)) * T_sum_nat (↑m' * ↑n' / (d' * d')) =
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
private lemma T_sum_mul_peel_prime_summand (q : ℕ) (hq : q.Prime) (a b : ℕ) (m' n' : ℕ+)
    (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ)) (r s : ℕ) (hr : r = min a b)
    (hs : s = max a b) (i : ℕ) (hi : i < r + 1) (d' : ℕ)
    (hd' : d' ∈ (Nat.gcd (m' : ℕ) n').divisors) :
    (↑(q ^ i) : ℤ) • ((T_pp q ^ i * T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩) *
      ((d' : ℤ) • (T_ad d' d' * T_sum_nat (↑m' * ↑n' / (d' * d'))))) =
    (↑(q ^ i * d') : ℤ) • (T_ad (q ^ i * d') (q ^ i * d') *
      T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (q ^ i * d' * (q ^ i * d')))) := by
  have hd'_dvd : d' ∣ Nat.gcd (m' : ℕ) n' := (Nat.mem_divisors.mp hd').1
  have hqd' : ¬ q ∣ d' := fun h => hqm (dvd_trans h (dvd_trans hd'_dvd (Nat.gcd_dvd_left _ _)))
  have hcop_qi_d' : Nat.Coprime (q ^ i) d' := (Nat.Prime.coprime_pow_of_not_dvd hq hqd').symm
  have hd'_pos : 0 < d' := Nat.pos_of_ne_zero fun h => by simp [h] at hd'_dvd
  rw [mul_smul_comm, smul_smul,
    show (↑(q ^ i) : ℤ) * ↑d' = ↑(q ^ i * d') from by push_cast; ring]
  congr 1
  rw [T_pp_pow_eq_T_ad q hq i,
    show T_ad (q ^ i) (q ^ i) * T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ *
      (T_ad d' d' * T_sum_nat (↑m' * ↑n' / (d' * d'))) =
      (T_ad (q ^ i) (q ^ i) * T_ad d' d') * (T_sum ⟨q ^ (r + s - 2 * i), pow_pos hq.pos _⟩ *
        T_sum_nat (↑m' * ↑n' / (d' * d'))) from by ring]
  have hcop_sq : Nat.Coprime (q ^ i * (q ^ i)) (d' * d') :=
    (hcop_qi_d'.mul_right hcop_qi_d').mul_left (hcop_qi_d'.mul_right hcop_qi_d')
  congr 1
  · rw [T_ad_mul_of_coprime _ d' _ d' (pow_pos hq.pos i) hd'_pos (pow_pos hq.pos i) hd'_pos
      (dvd_refl _) (dvd_refl _) hcop_sq]
  · exact T_sum_mul_peel_prime_summand_rhs q hq a b m' n' hqm hqn r s hr hs i hi d'
      hd'_dvd hqd' hcop_qi_d' hd'_pos

/-- Peel-off-a-prime step for the divisor sum formula. -/
private lemma T_sum_mul_peel_prime_aux (q : ℕ) (hq : q.Prime) (a b : ℕ) (_ha : 0 < a)
    (_hb : 0 < b) (m' n' : ℕ+) (hqm : ¬ q ∣ (m' : ℕ)) (hqn : ¬ q ∣ (n' : ℕ))
    (ih : T_sum m' * T_sum n' = ∑ d ∈ (Nat.gcd m' n').divisors,
      (d : ℤ) • (T_ad d d * T_sum_nat (↑m' * ↑n' / (d * d)))) :
    T_sum ⟨q ^ a * m', Nat.mul_pos (pow_pos hq.pos a) m'.pos⟩ *
      T_sum ⟨q ^ b * n', Nat.mul_pos (pow_pos hq.pos b) n'.pos⟩ =
    ∑ d ∈ (Nat.gcd (q ^ a * m') (q ^ b * n')).divisors,
      (d : ℤ) • (T_ad d d * T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (d * d))) := by
  have hcop_qm : Nat.Coprime (q ^ a) m' := (Nat.Prime.coprime_pow_of_not_dvd hq hqm).symm
  have hcop_qn : Nat.Coprime (q ^ b) n' := (Nat.Prime.coprime_pow_of_not_dvd hq hqn).symm
  set qa : ℕ+ := ⟨q ^ a, pow_pos hq.pos a⟩; set qb : ℕ+ := ⟨q ^ b, pow_pos hq.pos b⟩
  rw [show T_sum ⟨q ^ a * m', _⟩ = T_sum qa * T_sum m' from (T_sum_mul_coprime qa m' hcop_qm).symm,
    show T_sum ⟨q ^ b * n', _⟩ = T_sum qb * T_sum n' from (T_sum_mul_coprime qb n' hcop_qn).symm,
    show T_sum qa * T_sum m' * (T_sum qb * T_sum n') =
      (T_sum qa * T_sum qb) * (T_sum m' * T_sum n') from by ring]
  set r := min a b with hr_def; set g := Nat.gcd (m' : ℕ) n'
  have hcop_rg : Nat.Coprime (q ^ r) g :=
    (Nat.Prime.coprime_pow_of_not_dvd hq (fun h => hqm (dvd_trans h (Nat.gcd_dvd_left _ _)))).symm
  rw [gcd_factor_prime_pow q hq a b m' n' hqm hqn]
  open scoped Pointwise in
  rw [Nat.divisors_mul,
    show (Nat.divisors (q ^ r) * Nat.divisors g) =
    (Nat.divisors (q ^ r) ×ˢ Nat.divisors g).image (fun p => p.1 * p.2) from rfl]
  rw [ih]; set s := max a b with hs_def; have hrs : r ≤ s := min_le_max
  rw [show T_sum qa * T_sum qb =
    T_sum ⟨q ^ r, pow_pos hq.pos r⟩ * T_sum ⟨q ^ s, pow_pos hq.pos s⟩
    from by simp only [r, s, min_def, max_def]; split <;> [rfl; rw [mul_comm]],
    T_sum_ppow_mul q hq r s hrs, Finset.sum_mul]
  simp_rw [smul_mul_assoc, Finset.mul_sum]
  rw [Finset.sum_image (mul_injOn_coprime_divisors _ _ hcop_rg),
    show ∑ x ∈ (q ^ r).divisors ×ˢ g.divisors,
    (↑(x.1 * x.2) : ℤ) • (T_ad (x.1 * x.2) (x.1 * x.2) *
      T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (x.1 * x.2 * (x.1 * x.2)))) =
    ∑ d₁ ∈ (q ^ r).divisors, ∑ d₂ ∈ g.divisors,
      (↑(d₁ * d₂) : ℤ) • (T_ad (d₁ * d₂) (d₁ * d₂) *
        T_sum_nat (q ^ a * ↑m' * (q ^ b * ↑n') / (d₁ * d₂ * (d₁ * d₂)))) from
    by rw [← Finset.sum_product']]
  rw [Nat.sum_divisors_prime_pow hq]
  apply Finset.sum_congr rfl; intro i hi; rw [Finset.mem_range] at hi
  rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro d' hd'
  rw [show (↑q : ℤ) ^ i = (↑(q ^ i) : ℤ) from by push_cast; ring]
  exact T_sum_mul_peel_prime_summand q hq a b m' n' hqm hqn r s hr_def hs_def i hi d' hd'

/-- Theorem 3.24(3): `T(m) · T(n) = Σ_{d∣gcd(m,n)} d · T(d,d) · T(mn/d²)`.
    From Identity 4 at each prime + coprime multiplicativity. -/
theorem T_sum_mul (m n : ℕ+) : T_sum m * T_sum n =
    ∑ d ∈ (Nat.gcd m n).divisors, (d : ℤ) • (T_ad d d * T_sum_nat (↑m * ↑n / (d * d))) := by
  suffices h_ind : ∀ (g : ℕ) (m n : ℕ+), Nat.gcd m n = g → T_sum m * T_sum n =
      ∑ d ∈ g.divisors, (d : ℤ) • (T_ad d d * T_sum_nat (↑m * ↑n / (d * d))) from h_ind _ m n rfl
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
    rw [show m = ⟨q ^ a_ord * m', Nat.mul_pos (pow_pos hq.pos a_ord) m'.pos⟩ from
        Subtype.ext hm_eq,
      show n = ⟨q ^ b_ord * n', Nat.mul_pos (pow_pos hq.pos b_ord) n'.pos⟩ from
        Subtype.ext hn_eq,
      show g = Nat.gcd (q ^ a_ord * ↑m') (q ^ b_ord * ↑n') from by
        rw [← h_gcd, ← hm_eq, ← hn_eq]]
    convert T_sum_mul_peel_prime_aux q hq a_ord b_ord ha hb m' n' hqm' hqn'
      (ih _ h_smaller m' n' rfl) using 2

end HeckeRing.GL2
