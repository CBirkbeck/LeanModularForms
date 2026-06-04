/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.Finset.NatDivisors
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import LeanModularForms.HeckeRIngs.GL2.Basic
import LeanModularForms.HeckeRIngs.GLn.Degree
import LeanModularForms.HeckeRIngs.GLn.TransposeAntiInvolution

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
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  exact_mod_cast (Matrix.SpecialLinearGroup.map (algebraMap ℤ ℚ) S).prop

/-- `SL_n(ℤ) → GL_n(ℚ)` coercion as a matrix (replaces removed `SLnZ_to_GLnQ_val`). -/
@[simp]
lemma SLnZ_to_GLnQ_val {n : ℕ} [NeZero n] (S : Matrix.SpecialLinearGroup (Fin n) ℤ) :
    ((S : GL (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℚ) = (S.val).map (algebraMap ℤ ℚ) := by
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]; rfl

variable (p : ℕ) (hp : p.Prime)

section Telescoping

include hp in
/-- Key shift: `T_pp(p) * T_ad(p^j, p^d) = T_ad(p^{j+1}, p^{d+1})` when `j ≤ d`. -/
private lemma T_pp_mul_T_ad_ppow (j d : ℕ) (hjd : j ≤ d) :
    T_pp p * T_ad (p ^ j) (p ^ d) = T_ad (p ^ (j + 1)) (p ^ (d + 1)) := by
  rw [T_ad_of_pos _ _ (pow_pos hp.pos j) (pow_pos hp.pos d) (Nat.pow_dvd_pow p hjd),
    T_ad_of_pos _ _ (pow_pos hp.pos (j + 1)) (pow_pos hp.pos (d + 1))
      (Nat.pow_dvd_pow p (by omega)),
    T_pp_comm_T_elem p hp (![p ^ j, p ^ d])
      (fun i ↦ by fin_cases i <;> first | exact pow_pos hp.pos j | exact pow_pos hp.pos d)
      (fun i hi ↦ by
        obtain rfl : i = 0 := by omega
        simpa using Nat.pow_dvd_pow p hjd),
    T_pp_of_pos p hp,
    T_elem_mul_scalar (![p ^ j, p ^ d])
      (fun i ↦ by fin_cases i <;> first | exact pow_pos hp.pos j | exact pow_pos hp.pos d)
      (fun i hi ↦ by
        obtain rfl : i = 0 := by omega
        simpa using Nat.pow_dvd_pow p hjd) p hp.pos]
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
      T_sum ⟨p ^ k, pow_pos hp.pos k⟩ from eq_sub_iff_add_eq.mpr h
  rw [T_sum_ppow_expansion p hp k, T_sum_ppow_expansion p hp (k - 2), Finset.mul_sum]
  have shift : ∀ j ∈ Finset.range ((k - 2) / 2 + 1),
      T_pp p * T_ad (p ^ j) (p ^ (k - 2 - j)) =
      T_ad (p ^ (j + 1)) (p ^ (k - (j + 1))) := fun j hj ↦ by
    rw [Finset.mem_range] at hj
    rw [T_pp_mul_T_ad_ppow p hp j (k - 2 - j) (by omega),
      show k - 2 - j + 1 = k - (j + 1) by omega]
  rw [Finset.sum_congr rfl shift,
    show Finset.range ((k - 2) / 2 + 1) = Finset.range (k / 2) by congr 1; omega,
    Finset.sum_range_succ']
  simp only [pow_zero, Nat.sub_zero]
  abel

end Telescoping

/-- If `L * M * R = D` with `L`, `R` having determinant 1, then `M = L.adj * D * R.adj`. -/
private lemma matrix_isolate_middle (L_ℤ M R_ℤ D : Matrix (Fin 2) (Fin 2) ℤ)
    (hLadj : L_ℤ.adjugate * L_ℤ = 1) (hRadj : R_ℤ * R_ℤ.adjugate = 1)
    (heq_LMR : L_ℤ * M * R_ℤ = D) : M = L_ℤ.adjugate * D * R_ℤ.adjugate := by
  rw [← heq_LMR, show L_ℤ.adjugate * (L_ℤ * M * R_ℤ) * R_ℤ.adjugate =
    L_ℤ.adjugate * L_ℤ * M * (R_ℤ * R_ℤ.adjugate) by simp [mul_assoc],
    hLadj, hRadj, one_mul, mul_one]

private lemma first_invariant_dvd_p_of_product (S : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (a : Fin 2 → ℕ) (_ha_pos : ∀ i, 0 < a i) (hdiv : DivChain 2 a)
    (L R : Matrix.SpecialLinearGroup (Fin 2) ℤ) (k : ℕ) (_hk : 0 < k)
    (heq : (L : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p] : Fin 2 → ℤ) *
      (S : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p ^ k] : Fin 2 → ℤ) *
      (R : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.diagonal (fun i ↦ (a i : ℤ))) : a 0 ∣ p := by
  set dp := Matrix.diagonal (![1, p] : Fin 2 → ℤ)
  set dpk := Matrix.diagonal (fun m ↦ ((![1, p ^ k] : Fin 2 → ℕ) m : ℤ))
  set S_ℤ := (↑S : Matrix (Fin 2) (Fin 2) ℤ)
  set M := dp * S_ℤ * dpk
  set L_ℤ := (↑L : Matrix (Fin 2) (Fin 2) ℤ)
  set R_ℤ := (↑R : Matrix (Fin 2) (Fin 2) ℤ)
  have hLadj : L_ℤ.adjugate * L_ℤ = 1 := by rw [Matrix.adjugate_mul, L.prop, one_smul]
  have hRadj : R_ℤ * R_ℤ.adjugate = 1 := by rw [Matrix.mul_adjugate, R.prop, one_smul]
  have hM_eq : M = L_ℤ.adjugate * Matrix.diagonal (fun i ↦ (a i : ℤ)) * R_ℤ.adjugate :=
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
        (show (a 0 : ℤ) ∣ (a 1 : ℤ) by exact_mod_cast hdiv 0 (by omega)) _) _
  have h_M00 : M 0 0 = S_ℤ 0 0 := by
    simp [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two]
  have h_M10 : M 1 0 = (p : ℤ) * S_ℤ 1 0 := by
    simp [M, S_ℤ, dp, dpk, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
  have h_cop : IsCoprime (S_ℤ 0 0) (S_ℤ 1 0) := S.isCoprime_col 0
  have h1 : (a 0 : ℤ) ∣ S_ℤ 0 0 := h_M00 ▸ h_dvd_entry 0 0
  have h2 : (a 0 : ℤ) ∣ (p : ℤ) * S_ℤ 1 0 := h_M10 ▸ h_dvd_entry 1 0
  exact_mod_cast (by
    obtain ⟨u, v, huv⟩ := h_cop; obtain ⟨t, ht⟩ := h1
    exact ⟨u * t, v, by
      rw [show u * t * ↑(a 0) = u * (↑(a 0) * t) by ring, ← ht]; exact huv⟩
    : IsCoprime (↑(a 0) : ℤ) (S_ℤ 1 0)).dvd_of_dvd_mul_right h2

/-- Determinant balance for a `T(1,p) * T(1,pᵏ)` product: if the product lies in the
double coset of a diagonal matrix `diag a`, then `a 0 * a 1 = p^(k+1)`. -/
lemma mulSupport_pp_det_eq (k : ℕ) (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i)
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
  exact_mod_cast h_rhs.symm.trans h_lhs

include hp in
private lemma mulSupport_pp_dvd_p_aux
    (S_mid L' R' : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (a : Fin 2 → ℕ) (ha_pos : ∀ i, 0 < a i) (hdiv : DivChain 2 a) (k : ℕ) (_hk : 0 < k)
    (h_gl : (L' : GL (Fin 2) ℚ) * diagMat 2 (![1, p]) * (S_mid : GL (Fin 2) ℚ) *
      diagMat 2 (![1, p ^ k]) * (R' : GL (Fin 2) ℚ) = diagMat 2 a) : a 0 ∣ p := by
  have h_int_5 : (↑L' : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p] : Fin 2 → ℤ) *
      (↑S_mid : Matrix (Fin 2) (Fin 2) ℤ) * Matrix.diagonal (![1, p ^ k] : Fin 2 → ℤ) *
      (↑R' : Matrix (Fin 2) (Fin 2) ℤ) = Matrix.diagonal (fun i ↦ (a i : ℤ)) := by
    ext i j
    have h := congr_arg
      (fun (g : GL (Fin 2) ℚ) ↦ (↑g : Matrix _ _ ℚ) i j) h_gl
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
/-- Divisibility constraint for a `T(1,p) * T(1,pᵏ)` product: if the product lies in the
double coset of `diag a`, then the first invariant `a 0` divides `p`. -/
lemma mulSupport_pp_dvd_p (k : ℕ) (_hk : 0 < k) (a : Fin 2 → ℕ)
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
  apply mulSupport_pp_dvd_p_aux p hp S_mid L' R' a ha_pos
    hdiv k _hk
  set dp := diagMat 2 (![1, p])
  set dpk := diagMat 2 (![1, p ^ k])
  set da := diagMat 2 a
  have hprod : (SL_i₀ : GL (Fin 2) ℚ) *
      ((SL_L₁ : GL (Fin 2) ℚ) * dp * (SL_R₁ : GL (Fin 2) ℚ)) *
      ((SL_j₀ : GL (Fin 2) ℚ) *
        ((SL_L₂ : GL (Fin 2) ℚ) * dpk * (SL_R₂ : GL (Fin 2) ℚ))) =
      (SL_La : GL (Fin 2) ℚ) * da * (SL_Ra : GL (Fin 2) ℚ) := by
    rwa [← hi₀, ← hj₀, ← hD1_eq, ← hD2_eq]
  have := congr_arg (· * (SL_Ra : GL (Fin 2) ℚ)⁻¹) (congr_arg
    ((SL_La : GL (Fin 2) ℚ)⁻¹ * ·) hprod)
  simp only [mul_assoc, inv_mul_cancel_left] at this
  simp only [L', R', S_mid, map_mul, map_inv] at this ⊢
  convert this using 1; group

include hp in
/-- Two-way case split for `T(1,p) * T(1,pᵏ)` support: combining `a 0 * a 1 = p^(k+1)`
with `a 0 ∣ p` forces `T_diag a` to equal either `T_diag (![1,p^(k+1)])` or
`T_diag (![p,pᵏ])`. -/
lemma mulSupport_pp_case_split (k : ℕ) (_hk : 0 < k) (a : Fin 2 → ℕ)
    (_ha_pos : ∀ i, 0 < a i) (_hdiv : DivChain 2 a)
    (h_det_prod : a 0 * a 1 = p ^ (k + 1)) (h_dvd_p : a 0 ∣ p) :
    T_diag a = T_diag (![1, p ^ (k + 1)]) ∨
    T_diag a = T_diag (![p, p ^ k]) := by
  rcases Nat.Prime.eq_one_or_self_of_dvd hp (a 0) h_dvd_p with ha0_1 | ha0_p
  · left; congr 1; ext i; fin_cases i
    · exact ha0_1
    · rw [ha0_1, one_mul] at h_det_prod; simpa using h_det_prod
  · right; congr 1; ext i; fin_cases i
    · exact ha0_p
    · show a 1 = p ^ k
      have h1 : p * a 1 = p ^ (k + 1) := by rwa [ha0_p] at h_det_prod
      exact Nat.eq_of_mul_eq_mul_left hp.pos (by rw [h1, pow_succ]; ring)

include hp in
private lemma mulSupport_pp_subset (k : ℕ) (_hk : 0 < k) (A : HeckeCoset (GL_pair 2))
    (hA : A ∈ HeckeRing.mulSupport (GL_pair 2) (HeckeCoset.rep (T_diag (![1, p])))
      (HeckeCoset.rep (T_diag (![1, p ^ k])))) :
    A = T_diag (![1, p ^ (k + 1)]) ∨ A = T_diag (![p, p ^ k]) := by
  obtain ⟨a, ha_pos, hdiv, hrep⟩ := exists_diagonal_representative 2 (HeckeCoset.rep A)
  have hA_eq : A = T_diag a := HeckeCoset_ext_toSet (P := GL_pair 2) (by
    rw [HeckeCoset.toSet_eq_rep]; exact congr_arg HeckeCoset.toSet hrep)
  set D1 := T_diag (![1, p]); set D2 := T_diag (![1, p ^ k])
  rw [HeckeRing.mulSupport] at hA
  simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and, Prod.exists] at hA
  obtain ⟨i₀, j₀, hmap⟩ := hA
  obtain ⟨L₁, ⟨SL_L₁, rfl⟩, R₁, ⟨SL_R₁, rfl⟩, hD1_eq⟩ := T_diag_rep_decompose (![1, p])
    (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | exact hp.pos)
  obtain ⟨L₂, ⟨SL_L₂, rfl⟩, R₂, ⟨SL_R₂, rfl⟩, hD2_eq⟩ := T_diag_rep_decompose (![1, p ^ k])
    (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos k)
  have h_prod_in_A : (↑i₀.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D1 : GL (Fin 2) ℚ) *
      ((↑j₀.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D2 : GL (Fin 2) ℚ)) ∈
      DoubleCoset.doubleCoset (diagMat 2 a : GL (Fin 2) ℚ) (GL_pair 2).H (GL_pair 2).H := by
    have h1 : (↑i₀.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D1 : GL (Fin 2) ℚ) *
        ((↑j₀.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D2 : GL (Fin 2) ℚ)) ∈
        HeckeCoset.toSet (HeckeRing.mulMap (GL_pair 2) (HeckeCoset.rep D1)
          (HeckeCoset.rep D2) (i₀, j₀)) := by
      rw [HeckeRing.mulMap, HeckeCoset.toSet_mk]; exact DoubleCoset.mem_doubleCoset_self _ _ _
    rw [hmap, hA_eq, T_diag, HeckeCoset.toSet_mk, diagMat_delta_val _ _ ha_pos] at h1; exact h1
  rw [DoubleCoset.mem_doubleCoset] at h_prod_in_A
  obtain ⟨L_a, ⟨SL_La, rfl⟩, R_a, ⟨SL_Ra, rfl⟩, h_prod_eq⟩ := h_prod_in_A
  obtain ⟨SL_i₀, hSL_i₀⟩ := (i₀.out : ↥(GL_pair 2).H).2
  obtain ⟨SL_j₀, hSL_j₀⟩ := (j₀.out : ↥(GL_pair 2).H).2
  have h_det := mulSupport_pp_det_eq p k a ha_pos (↑i₀.out)
    (HeckeCoset.rep D1 : GL (Fin 2) ℚ) (↑j₀.out) (HeckeCoset.rep D2 : GL (Fin 2) ℚ)
    (by rw [show (↑i₀.out : GL _ ℚ) = (SL_i₀ : GL (Fin 2) ℚ) from hSL_i₀.symm]
        exact SLnZ_to_GLnQ_det SL_i₀)
    (by rw [hD1_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          SLnZ_to_GLnQ_det, SLnZ_to_GLnQ_det, diagMat_det 2 (![1, p])
          (by intro ⟨i, hi⟩; interval_cases i <;> simp [hp.pos])]; simp [Fin.prod_univ_two])
    (by rw [show (↑j₀.out : GL _ ℚ) = (SL_j₀ : GL (Fin 2) ℚ) from hSL_j₀.symm]
        exact SLnZ_to_GLnQ_det SL_j₀)
    (by rw [hD2_eq, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
          SLnZ_to_GLnQ_det, SLnZ_to_GLnQ_det, diagMat_det 2 (![1, p ^ k])
          (by intro ⟨i, hi⟩; interval_cases i <;> simp [pow_pos hp.pos k])]
        simp [Fin.prod_univ_two])
    SL_La SL_Ra h_prod_eq
  have h_dvd := mulSupport_pp_dvd_p p hp k _hk a ha_pos hdiv (HeckeCoset.rep D1)
    (HeckeCoset.rep D2) (↑i₀.out) (↑j₀.out) SL_L₁ SL_R₁ SL_L₂ SL_R₂ SL_La SL_Ra SL_i₀
    SL_j₀ hD1_eq hD2_eq hSL_i₀.symm hSL_j₀.symm h_prod_eq
  rw [hA_eq]; exact mulSupport_pp_case_split p hp k _hk a ha_pos hdiv h_det h_dvd

include hp in
private lemma D_out1_pp_in_mulSupport (k : ℕ) (_hk : 0 < k) :
    T_diag (![1, p ^ (k + 1)]) ∈ HeckeRing.mulSupport (GL_pair 2)
      (HeckeCoset.rep (T_diag (![1, p]))) (HeckeCoset.rep (T_diag (![1, p ^ k]))) := by
  obtain ⟨L₁, hL₁, R₁, hR₁, hα_eq⟩ := T_diag_rep_decompose (![1, p])
    (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | exact hp.pos)
  obtain ⟨L₂, hL₂, R₂, hR₂, hβ_eq⟩ := T_diag_rep_decompose (![1, p ^ k])
    (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos k)
  apply HeckeRing.mem_mulSupport_of_product_mem _ _ _ (diagMat_delta 2 (![1, p ^ (k + 1)]))
    ⟨L₁⁻¹, (GL_pair 2).H.inv_mem hL₁⟩
    ⟨R₁⁻¹ * L₂⁻¹,
      (GL_pair 2).H.mul_mem ((GL_pair 2).H.inv_mem hR₁) ((GL_pair 2).H.inv_mem hL₂)⟩
  rw [hα_eq, hβ_eq, DoubleCoset.mem_doubleCoset]
  refine ⟨1, (GL_pair 2).H.one_mem, R₂, hR₂, ?_⟩
  simp only [one_mul, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
  rw [diagMat_delta_val 2 (![1, p ^ (k + 1)])
    (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos (k + 1))]
  rw [← mul_assoc, diagMat_mul 2 (![1, p]) (![1, p ^ k])
    (by intro i; fin_cases i <;> simp [hp.pos])
    (by intro i; fin_cases i <;> simp [pow_pos hp.pos k])]
  congr 2; ext i; fin_cases i <;> simp [Pi.mul_apply, pow_succ, mul_comm]

private lemma heckeMultiplicity_deg_sum_eq (D1 D2 D_out1 D_out2 : HeckeCoset (GL_pair 2))
    (h_ne : D_out1 ≠ D_out2) (h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep A) = 0) :
    HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)
      (HeckeCoset.rep D_out1) * HeckeCoset_deg (GL_pair 2) D_out1 +
      HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep D_out2) * HeckeCoset_deg (GL_pair 2) D_out2 =
      HeckeCoset_deg (GL_pair 2) D1 * HeckeCoset_deg (GL_pair 2) D2 := by
  have h1 : HeckeRing.deg (GL_pair 2)
      (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)) =
      HeckeCoset_deg (GL_pair 2) D1 * HeckeCoset_deg (GL_pair 2) D2 := by
    rw [← HeckeRing.T_single_one_mul_T_single_one, HeckeRing.deg_mul,
      HeckeRing.deg_T_single, HeckeRing.deg_T_single]; ring
  have h2 : HeckeRing.deg (GL_pair 2)
      (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)) =
      HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep D_out1) * HeckeCoset_deg (GL_pair 2) D_out1 +
        HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)
          (HeckeCoset.rep D_out2) *
          HeckeCoset_deg (GL_pair 2) D_out2 := by
    open scoped Classical in
    simp only [HeckeRing.deg, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
      HeckeRing.deg_fun]
    have hsub : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D1)
        (HeckeCoset.rep D2)).support ⊆ ({D_out1, D_out2} : Finset _) := by
      intro A hA; simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [Finsupp.mem_support_iff] at hA
      exact (or_iff_not_imp_left.mpr fun h1 ↦
        (Classical.em (A = D_out2)).elim id fun h2 ↦ absurd (h_zero A h1 h2) hA)
    exact Finset.sum_subset hsub (by
      intro A _ hA; rw [Finsupp.notMem_support_iff.mp hA]; simp) |>.trans
      (Finset.sum_pair h_ne)
  linarith

include hp in
/-- The degree of the diagonal coset `T(1, pʲ)` is `p^{j-1}(p+1)` for `j ≥ 1`. -/
private lemma HeckeCoset_deg_T_diag_one_ppow (j : ℕ) (hj : 0 < j) :
    HeckeCoset_deg (GL_pair 2) (T_diag (![1, p ^ j])) = ↑(p ^ (j - 1) * (p + 1)) :=
  HeckeCoset_deg_T_diag_two_prime p hp _
    (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | exact pow_pos hp.pos j)
    (fun i hi ↦ by (have : i = 0 := by omega); subst this; simp) j hj (by simp)

include hp in
/-- The degree of the diagonal coset `T(p, pᵏ)` is `p^{k-2}(p+1)` for `k ≥ 2`. -/
private lemma HeckeCoset_deg_T_diag_p_ppow (k : ℕ) (hk2 : 2 ≤ k) :
    HeckeCoset_deg (GL_pair 2) (T_diag (![p, p ^ k])) = ↑(p ^ (k - 2) * (p + 1)) := by
  have := HeckeCoset_deg_T_diag_two_prime p hp (![p, p ^ k])
    (by intro i; fin_cases i <;> first | exact hp.pos | exact pow_pos hp.pos k)
    (fun i hi ↦ by
      have hi0 : i = 0 := by omega
      subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega))
    (k - 1) (by omega)
    (by show p ^ k / p = p ^ (k - 1)
        have : p ^ k = p ^ (k - 1) * p := by rw [← pow_succ]; congr 1; omega
        rw [this, Nat.mul_div_cancel _ hp.pos])
  rwa [show k - 1 - 1 = k - 2 by omega] at this

include hp in
/-- Scalar case: the degree of `T(p, p)` is `1`. -/
private lemma HeckeCoset_deg_T_diag_p_p_eq_one :
    HeckeCoset_deg (GL_pair 2) (T_diag (![p, p ^ 1])) = 1 :=
  HeckeCoset_deg_T_diag_two_scalar _
    (fun i ↦ by fin_cases i <;> first | exact hp.pos | exact pow_pos hp.pos 1)
    (fun i hi ↦ by (have : i = 0 := by omega); subst this; simp [pow_one])
    (by show (![p, p ^ 1] : Fin 2 → ℕ) 0 = (![p, p ^ 1] : Fin 2 → ℕ) 1; simp [pow_one])

include hp in
/-- The diagonal cosets `T(1, p^{k+1})` and `T(p, pᵏ)` are distinct: a uniqueness argument on
    elementary divisors, since the leading divisors `1` and `p` differ. -/
private lemma T_diag_one_ppow_succ_ne_T_diag_p_ppow (k : ℕ) (hk : 0 < k) :
    T_diag (![1, p ^ (k + 1)]) ≠ T_diag (![p, p ^ k]) := by
  intro heq
  have h1_pos : ∀ i : Fin 2, 0 < (![1, p ^ (k + 1)]) i := by
    intro i; fin_cases i <;> simp [pow_pos hp.pos]
  have h2_pos : ∀ i : Fin 2, 0 < (![p, p ^ k]) i := by
    intro i; fin_cases i <;> simp [hp.pos, pow_pos hp.pos]
  have h1_div : DivChain 2 (![1, p ^ (k + 1)]) := fun i hi ↦ by
    have hi0 : i = 0 := by omega
    subst hi0; simp
  have h2_div : DivChain 2 (![p, p ^ k]) := fun i hi ↦ by
    have hi0 : i = 0 := by omega
    subst hi0; simpa using dvd_pow_self p (show k ≠ 0 by omega)
  exact absurd (congr_fun (diagonal_representative_unique 2 _ _
    h1_pos h2_pos h1_div h2_div heq) 0).symm (Nat.Prime.one_lt hp).ne'

/-- Arithmetic core of the `k ≥ 2` branch: from the degree balance `m₁·pᵏ(p+1) +
    m₂·p^{k-2}(p+1) = (p+1)·p^{k-1}(p+1)` with `1 ≤ m₁`, `0 ≤ m₂`, deduce `m₁ = 1` and `m₂ = P`. -/
private lemma m1_eq_one_and_m2_eq_of_deg_two_le (P m1 m2 : ℤ) (k : ℕ) (hk2 : 2 ≤ k)
    (hP : 2 ≤ P) (hm1 : 1 ≤ m1) (hm2 : 0 ≤ m2)
    (h_deg : m1 * (P ^ k * (P + 1)) + m2 * (P ^ (k - 2) * (P + 1)) =
      (P + 1) * (P ^ (k - 1) * (P + 1))) :
    m1 = 1 ∧ m2 = P := by
  have hpk : P ^ k = P ^ (k - 2) * P ^ 2 := by rw [← pow_add]; congr 1; omega
  have hpk1 : P ^ (k - 1) = P ^ (k - 2) * P := by
    rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]
  have h_eq : m1 * P ^ 2 + m2 = P * (P + 1) := by
    have h := h_deg; rw [hpk, hpk1] at h
    have key : P ^ (k - 2) * (P + 1) ≠ 0 := by positivity
    have := mul_right_cancel₀ key (show
      (m1 * P ^ 2 + m2) * (P ^ (k - 2) * (P + 1)) =
      (P * (P + 1)) * (P ^ (k - 2) * (P + 1)) by nlinarith)
    linarith
  have h_m1_eq : m1 = 1 := by
    have h_le : m1 * P ^ 2 ≤ P ^ 2 + P := by linarith [h_eq, hm2]
    nlinarith [show P ^ 2 ≥ 4 by nlinarith]
  exact ⟨h_m1_eq, by rw [h_m1_eq] at h_eq; linarith⟩

/-- Arithmetic core of the `k = 1` branch: from the degree balance `m₁·p(p+1) + m₂ =
    (p+1)²` with `1 ≤ m₁`, `0 ≤ m₂`, deduce `m₁ = 1` and `m₂ = P + 1`. -/
private lemma m1_eq_one_and_m2_eq_of_deg_eq_one (P m1 m2 : ℤ) (hP : 2 ≤ P)
    (hm1 : 1 ≤ m1) (hm2 : 0 ≤ m2)
    (h_deg : m1 * (P ^ 1 * (P + 1)) + m2 * 1 = (P + 1) * (P + 1)) :
    m1 = 1 ∧ m2 = P + 1 := by
  have h_m1_eq : m1 = 1 := by nlinarith [mul_self_nonneg (P - 1)]
  exact ⟨h_m1_eq, by rw [h_m1_eq] at h_deg; nlinarith⟩

include hp in
private lemma heckeMultiplicity_values (k : ℕ) (hk : 0 < k) :
    HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep (T_diag (![1, p])))
      (HeckeCoset.rep (T_diag (![1, p ^ k])))
      (HeckeCoset.rep (T_diag (![1, p ^ (k + 1)]))) = 1 ∧
    HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep (T_diag (![1, p])))
      (HeckeCoset.rep (T_diag (![1, p ^ k])))
      (HeckeCoset.rep (T_diag (![p, p ^ k]))) = if k = 1 then ↑(p + 1) else ↑p := by
  set D1 := T_diag (![1, p])
  set D2 := T_diag (![1, p ^ k])
  set D_out1 := T_diag (![1, p ^ (k + 1)])
  set D_out2 := T_diag (![p, p ^ k])
  set m1 := HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1)
    (HeckeCoset.rep D2) (HeckeCoset.rep D_out1)
  set m2 := HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1)
    (HeckeCoset.rep D2) (HeckeCoset.rep D_out2)
  have h_ne : D_out1 ≠ D_out2 := T_diag_one_ppow_succ_ne_T_diag_p_ppow p hp k hk
  have h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep A) = 0 := by
    intro A h1 h2; apply HeckeRing.heckeMultiplicity_eq_zero_of_nmem_mulSupport
    intro hmem; exact (mulSupport_pp_subset p hp k hk A hmem).elim h1 h2
  have h_deg : m1 * HeckeCoset_deg (GL_pair 2) D_out1 +
      m2 * HeckeCoset_deg (GL_pair 2) D_out2 =
      HeckeCoset_deg (GL_pair 2) D1 * HeckeCoset_deg (GL_pair 2) D2 :=
    heckeMultiplicity_deg_sum_eq D1 D2 D_out1 D_out2 h_ne h_zero
  have hm2_nn := HeckeRing.heckeMultiplicity_nonneg (GL_pair 2) (HeckeCoset.rep D1)
    (HeckeCoset.rep D2) (HeckeCoset.rep D_out2)
  have hm1_pos : 1 ≤ m1 := by
    have hne : (HeckeRing.m (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2))
        D_out1 ≠ 0 := by
      rw [← Finsupp.mem_support_iff, HeckeRing.m_support]
      exact D_out1_pp_in_mulSupport p hp k hk
    exact Int.lt_iff_add_one_le.mp (lt_of_le_of_ne
      (HeckeRing.heckeMultiplicity_nonneg ..) (Ne.symm hne))
  rw [show HeckeCoset_deg (GL_pair 2) D1 = ↑(p + 1) from by
        simpa using HeckeCoset_deg_T_diag_one_ppow p hp 1 one_pos,
    show HeckeCoset_deg (GL_pair 2) D2 = ↑(p ^ (k - 1) * (p + 1)) from
      HeckeCoset_deg_T_diag_one_ppow p hp k hk,
    show HeckeCoset_deg (GL_pair 2) D_out1 = ↑(p ^ k * (p + 1)) from by
      simpa using HeckeCoset_deg_T_diag_one_ppow p hp (k + 1) (by omega)] at h_deg
  have hp2 : (2 : ℤ) ≤ p := mod_cast hp.two_le
  by_cases hk1 : k = 1
  · subst hk1; simp only [ite_true, show 1 - 1 = 0 by rfl, pow_zero, one_mul] at h_deg ⊢
    rw [HeckeCoset_deg_T_diag_p_p_eq_one p hp] at h_deg; push_cast at h_deg ⊢
    exact m1_eq_one_and_m2_eq_of_deg_eq_one (p : ℤ) m1 m2 hp2 hm1_pos hm2_nn h_deg
  · simp only [show k ≠ 1 from hk1, ite_false]; have hk2 : 2 ≤ k := by omega
    rw [HeckeCoset_deg_T_diag_p_ppow p hp k hk2] at h_deg; push_cast at h_deg ⊢
    exact m1_eq_one_and_m2_eq_of_deg_two_le (p : ℤ) m1 m2 k hk2 hp2 hm1_pos hm2_nn h_deg

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
  have h_ne : D_out1 ≠ D_out2 := T_diag_one_ppow_succ_ne_T_diag_p_ppow p hp k hk
  rw [T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _),
    T_ad_of_pos 1 (p ^ k) Nat.one_pos (pow_pos hp.pos k) (one_dvd _),
    T_ad_of_pos 1 (p ^ (k + 1)) Nat.one_pos (pow_pos hp.pos (k + 1)) (one_dvd _),
    T_ad_of_pos p (p ^ k) hp.pos (pow_pos hp.pos k) (dvd_pow_self p (by omega))]
  have h_mul : T_elem (![1, p]) * T_elem (![1, p ^ k]) =
      HeckeRing.m (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2) :=
    HeckeRing.T_single_one_mul_T_single_one (GL_pair 2) D1 D2
  have h_rhs : T_elem (![1, p ^ (k + 1)]) + c • T_elem (![p, p ^ k]) =
      Finsupp.single D_out1 1 + c • Finsupp.single D_out2 1 := rfl
  rw [h_mul, h_rhs, Finsupp.smul_single', mul_one]
  apply Finsupp.ext; intro A
  show HeckeRing.heckeMultiplicity (GL_pair 2) (HeckeCoset.rep D1) (HeckeCoset.rep D2)
    (HeckeCoset.rep A) =
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
  rw [T_ad, dif_pos ⟨one_pos, one_pos, dvd_refl 1⟩]; exact T_ad_one_one

include hp in
/-- `T_ad(p, p^k) = T_pp * T_ad(1, p^{k-1})` for `k ≥ 1`.
    Consequence of `T_pp_mul_T_ad_ppow` with j=0. -/
private lemma T_ad_p_ppow_eq (k : ℕ) (hk : 0 < k) :
    T_ad p (p ^ k) = T_pp p * T_ad 1 (p ^ (k - 1)) := by
  have h0 := T_pp_mul_T_ad_ppow p hp 0 (k - 1) (Nat.zero_le _)
  rw [show k - 1 + 1 = k from Nat.succ_pred_eq_of_pos hk] at h0
  simpa [pow_zero, zero_add, pow_one] using h0.symm

include hp in
private lemma T_pp_comm_T_ad_one_p : T_pp p * T_ad 1 p = T_ad 1 p * T_pp p := by
  rw [T_ad_of_pos 1 p Nat.one_pos hp.pos (one_dvd _)]
  exact T_pp_comm_T_elem p hp _
    (fun i ↦ by fin_cases i <;> first | exact Nat.one_pos | exact hp.pos)
    (fun i hi ↦ by (have : i = 0 := by omega); subst this; simp)

/-- `T_sum(p^0) = 1`. -/
private lemma T_sum_ppow_zero : T_sum ⟨p ^ 0, pow_pos hp.pos 0⟩ = 1 := T_sum_one

/-- `T_ad(1, p^0) = 1`. -/
private lemma T_ad_one_ppow_zero : T_ad 1 (p ^ 0) = 1 := by simp [T_ad_one_one]

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
  conv at h2 => rhs; rw [show (k + 2 + 1) - 2 = k + 1 by omega]
  rw [h2] at h5
  simp only [show k + 2 ≠ 1 by omega, ite_false,
             show k + 2 - 1 = k + 1 by omega] at h5
  rw [T_ad_one_ppow_eq p hp (k + 2) (by omega)] at h5
  rw [show T_sum ⟨p, hp.pos⟩ *
        (T_sum ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩ -
          T_pp p * T_sum ⟨p ^ (k + 2 - 2), pow_pos hp.pos (k + 2 - 2)⟩) =
      T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ (k + 2), pow_pos hp.pos (k + 2)⟩ -
        T_sum ⟨p, hp.pos⟩ * (T_pp p * T_sum ⟨p ^ (k + 2 - 2), pow_pos hp.pos (k + 2 - 2)⟩)
    from mul_sub _ _ _] at h5
  have h2k1 := T_ad_one_ppow_eq p hp (k + 1) (by omega)
  conv at h2k1 => rhs; rw [show (k + 1) - 2 = k - 1 by omega]
  rw [h2k1] at h5
  conv at h5 => lhs; rw [show k + 2 - 2 = k by omega]
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
  linear_combination (norm := module) -h5

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
  conv at h2 => rhs; rw [show (k + 1) - 2 = k - 1 by omega]
  rw [h2] at h5
  match k, hk, ih with
  | 1, _, _ =>
    simp only [show (1 : ℕ) - 1 = 0 by rfl, ite_true] at h5 ⊢
    rw [T_sum_ppow_zero p hp, T_ad_one_ppow_zero, mul_one] at h5
    rw [T_sum_ppow_zero p hp, mul_one,
      show T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ from
      by congr 1; exact Subtype.ext (pow_one p)]
    rw [T_ad_one_ppow_one, T_sum_prime p hp] at h5
    rw [T_sum_prime p hp]
    rw [show (↑(p + 1) : ℤ) • T_pp p = (↑p : ℤ) • T_pp p + T_pp p from by
      rw [show (↑(p + 1) : ℤ) = (↑p : ℤ) + 1 by push_cast; ring,
        add_smul, one_smul]] at h5
    linear_combination (norm := module) -h5
  | 2, _, _ =>
    simp only [show (2 : ℕ) ≠ 1 by omega, ite_false,
               show (2 : ℕ) - 1 = 1 by omega] at h5 ⊢
    rw [T_ad_one_ppow_eq p hp 2 (by omega)] at h5
    rw [show T_sum ⟨p, hp.pos⟩ *
          (T_sum ⟨p ^ 2, pow_pos hp.pos 2⟩ -
            T_pp p * T_sum ⟨p ^ (2 - 2), pow_pos hp.pos (2 - 2)⟩) =
        T_sum ⟨p, hp.pos⟩ * T_sum ⟨p ^ 2, pow_pos hp.pos 2⟩ -
          T_sum ⟨p, hp.pos⟩ * (T_pp p * T_sum ⟨p ^ (2 - 2), pow_pos hp.pos (2 - 2)⟩)
      from mul_sub _ _ _] at h5
    simp only [show 2 - 2 = 0 by rfl] at h5 ⊢
    rw [T_sum_ppow_zero p hp, mul_one, T_ad_one_ppow_one, T_sum_prime p hp] at h5
    rw [show T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ = T_sum ⟨p, hp.pos⟩ from
      by congr 1; exact Subtype.ext (pow_one p)] at h5 ⊢
    rw [T_sum_prime p hp] at h5 ⊢
    rw [(T_pp_comm_T_ad_one_p p hp).symm] at h5
    linear_combination (norm := module) -h5
  | k + 3, _, ih =>
    exact T_sum_ppow_recurrence_step p hp (k + 1) (by omega) ih

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
      (fun i' ↦ by fin_cases i' <;> first | exact pow_pos hp.pos i | exact pow_pos hp.pos (k - i))
      (fun i' hi' ↦ by (have : i' = 0 := by omega); subst this; simpa using hdvd)
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
    T_sum ⟨p ^ 1, pow_pos hp.pos 1⟩ by congr 1; exact (Subtype.ext (pow_one p)).symm]
  exact (T_pp_pow_comm_T_sum_ppow p hp i 1).symm

section CoprimeMultiplicativity

end CoprimeMultiplicativity

end HeckeRing.GL2
