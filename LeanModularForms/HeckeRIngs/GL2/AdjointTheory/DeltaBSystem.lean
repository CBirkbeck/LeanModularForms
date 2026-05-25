/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.SummandAdjoint

/-!
# Hecke adjoint theory: DS-standard `δ_b` representative system.

Third module of the split of `AdjointTheoryPetersson`. Covers the T128
DS-standard `δ_b` representative-system helpers and the associated
fundamental-domain swap machinery.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

/-! ### T128 DS-standard `δ_b` representative-system helpers

The `δ_b ∈ Γ₁(N)` matrix realizing `γ₀ · T_p_upper(b) = T_p_lower · δ_b` for
`γ₀ = adjointGamma0Rep`.  These are the candidates for a complete
representative system of `H_L \ Γ₁(N)` where
`H_L := Γ₁(N) ∩ T_p_lower⁻¹ · Γ₁(N) · T_p_lower`. -/

noncomputable def gamma0_T_p_upper_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) : SL(2, ℤ) :=
  ⟨!![1, (b : ℤ) - Int.gcdB p N;
      (N : ℤ), (N : ℤ) * b + (p : ℤ) * Int.gcdA p N],
    by
      have hbez := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
      rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
      rw [Matrix.det_fin_two_of]; linarith⟩

theorem gamma0_T_p_upper_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (b : ℕ) :
    gamma0_T_p_upper_Gamma1_factor N p hpN b ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have hbez := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
  have hN_zmod : ((N : ℕ) : ZMod N) = 0 := ZMod.natCast_self N
  have hpgcdA_mod : ((p : ZMod N) : ZMod N) * ((Int.gcdA p N : ℤ) : ZMod N) = 1 := by
    have := congr_arg ((↑) : ℤ → ZMod N) hbez.symm
    push_cast at this
    rw [hN_zmod, zero_mul, add_zero] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · change ((1 : ℤ) : ZMod N) = 1
    push_cast; rfl
  · change (((N : ℤ) * b + (p : ℤ) * Int.gcdA p N : ℤ) : ZMod N) = 1
    push_cast
    rw [hN_zmod]
    simp only [zero_mul, zero_add]
    exact hpgcdA_mod
  · change (((N : ℤ) : ℤ) : ZMod N) = 0
    push_cast
    exact ZMod.natCast_self N

theorem mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (b : ℕ) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  have hbez : (Int.gcdA p N : ℤ) * p + (Int.gcdB p N : ℤ) * N = 1 := by
    have h := Int.gcd_eq_gcd_ab (p : ℤ) (N : ℤ)
    rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at h
    linarith
  have h_gamma0_mat : (((mapGL ℝ : SL(2, ℤ) →* _)
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), -((Int.gcdB p N : ℤ) : ℝ); (N : ℝ), ((Int.gcdA p N : ℤ) : ℝ)] := by
    ext i' j'
    fin_cases i' <;> fin_cases j' <;>
      simp [adjointGamma0Rep, mapGL_coe_matrix, algebraMap_int_eq, Matrix.of_apply]
  have h_Tu_mat : ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.of_apply]
  have h_Tl_mat : ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(p : ℝ), 0; 0, 1] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [glMap, T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.of_apply]
  have h_delta_mat : (((mapGL ℝ : SL(2, ℤ) →* _)
      (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), ((b : ℝ) - ((Int.gcdB p N : ℤ) : ℝ));
         (N : ℝ), ((N : ℝ) * b + (p : ℝ) * ((Int.gcdA p N : ℤ) : ℝ))] := by
    ext i' j'; fin_cases i' <;> fin_cases j' <;>
      simp [mapGL_coe_matrix, gamma0_T_p_upper_Gamma1_factor, algebraMap_int_eq,
        Matrix.of_apply]
  show ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : GL (Fin 2) ℝ).val i j =
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ)).val i j
  rw [Units.val_mul, Units.val_mul, h_gamma0_mat, h_Tu_mat, h_Tl_mat, h_delta_mat]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply] <;> ring

theorem mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) := by
  have h_M_infty_eq : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp hpN 0,
      mul_inv_cancel_left]
  rw [h_M_infty_eq, ← mul_assoc,
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp hpN 0,
    mul_assoc, ← map_mul]

theorem gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0 ∈
      Gamma1 N :=
  mul_mem (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN 0)
    (M_infty_Gamma1_factor_mem_Gamma1 N p hpN 0)

private noncomputable def ds_p_plus_one_family_Gamma1_factor
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Option (Fin p) → SL(2, ℤ)
  | none => gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0
  | some b => gamma0_T_p_upper_Gamma1_factor N p hpN b.val

private theorem ds_p_plus_one_family_Gamma1_factor_mem_Gamma1
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (i : Option (Fin p)) :
    ds_p_plus_one_family_Gamma1_factor N p hpN i ∈ Gamma1 N := by
  match i with
  | none =>
    exact gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
      N p hpN
  | some b =>
    exact gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b.val

private theorem mapGL_gamma0_mul_ds_family_eq_T_p_lower_mul_mapGL_factor
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      (match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* _)
        (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) := by
  match i with
  | none =>
    exact mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp hpN
  | some b =>
    exact mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp hpN b.val

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem gamma0_smul_ds_family_eq_T_p_lower_smul_gamma_X
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) (D : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
      ((match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      (((mapGL ℝ : SL(2, ℤ) →* _)
        (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D) := by
  rw [← mul_smul, ← mul_smul,
    mapGL_gamma0_mul_ds_family_eq_T_p_lower_mul_mapGL_factor N p hp hpN i]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem gamma0_smul_Hecke_FD_eq_T_p_lower_smul_iUnion
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (D : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* _)
          (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D) := by
  rw [Set.smul_set_iUnion, Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i ↦ ?_
  exact gamma0_smul_ds_family_eq_T_p_lower_smul_gamma_X (N := N) p hp hpN i D

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_gamma0_smul_Hecke_FD_eq_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* _)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      F G =
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ)) :=
  peterssonInner_mapGL_smul_eq_slash _
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_gamma0_smul_Hecke_FD_eq_T_p_lower_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* _)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      F G =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          ((mapGL ℝ : SL(2, ℤ) →* _)
            (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D))
      F G := by
  rw [gamma0_smul_Hecke_FD_eq_T_p_lower_smul_iUnion (N := N) p hp hpN D]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_smul_eq_gamma0_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          ((mapGL ℝ : SL(2, ℤ) →* _)
            (ds_p_plus_one_family_Gamma1_factor N p hpN i) : GL (Fin 2) ℝ) • D))
      F G =
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
  rw [← peterssonInner_gamma0_smul_Hecke_FD_eq_T_p_lower_smul (N := N) p hp hpN D]
  exact peterssonInner_gamma0_smul_Hecke_FD_eq_slash (N := N) p hp hpN D F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_Hecke_FD_T_p_lower_slot2_slash_adjoint
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      F (G ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      (F ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) G := by
  have hα : 0 < (glMap (T_p_lower p hp) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_lower p hp : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_lower p hp : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp
  have h := peterssonInner_slash_adjoint_right (k := k)
    (⋃ i : Option (Fin p),
      (match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) hα F G
  rw [peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero] at h
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_Hecke_FD_T_p_lower_slot1_slash_adjoint
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (F ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) G =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      F (G ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) := by
  have hα : 0 < (glMap (T_p_lower p hp) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_lower p hp : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_lower p hp : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_lower p hp : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp
  have h := peterssonInner_slash_adjoint (k := k)
    (⋃ i : Option (Fin p),
      (match i with
        | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) hα F G
  rw [peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero] at h
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_Hecke_FD_T_p_lower_residual_iff
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (D : Set ℍ) (f g : ℍ → ℂ) (g' : ℍ → ℂ) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      f (g ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) =
    peterssonInner k
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D)
      (g' ∣[k] (glMap (T_p_lower p hp) : GL (Fin 2) ℝ)) g ↔
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      (f ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) g =
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p),
          (match i with
            | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)) • D))
      g' (g ∣[k] (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ)) := by
  rw [peterssonInner_Hecke_FD_T_p_lower_slot2_slash_adjoint
        (N := N) p hp hpN D f g,
      peterssonInner_Hecke_FD_T_p_lower_slot1_slash_adjoint
        (N := N) p hp hpN D g' g]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma UpperHalfPlane_smul_eq_of_matrix_smul_eq
    (α β : GL (Fin 2) ℝ) (hα : 0 < α.det.val) (hβ : 0 < β.det.val)
    (c : ℝ) (hc : c ≠ 0)
    (hMat : (α : Matrix (Fin 2) (Fin 2) ℝ) = c • (β : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    α • τ = β • τ := by
  rw [UpperHalfPlane.ext_iff,
      UpperHalfPlane.coe_smul_of_det_pos hα,
      UpperHalfPlane.coe_smul_of_det_pos hβ]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom]
  have h00 : (α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h01 : (α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h10 : (α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  have h11 : (α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
      c * (β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by
    rw [hMat, Matrix.smul_apply, smul_eq_mul]
  rw [show ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) by
    exact_mod_cast h00,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) by
      exact_mod_cast h01,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) by
      exact_mod_cast h10,
    show ((α : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
        (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) by
      exact_mod_cast h11]
  have hc_ne_zero : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have h_num : (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (τ : ℂ) +
      (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ) =
      (c : ℂ) * (((β : Matrix (Fin 2) (Fin 2) ℝ) 0 0 : ℂ) * (τ : ℂ) +
        ((β : Matrix (Fin 2) (Fin 2) ℝ) 0 1 : ℂ)) := by ring
  have h_den : (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (τ : ℂ) +
      (c : ℂ) * ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ) =
      (c : ℂ) * (((β : Matrix (Fin 2) (Fin 2) ℝ) 1 0 : ℂ) * (τ : ℂ) +
        ((β : Matrix (Fin 2) (Fin 2) ℝ) 1 1 : ℂ)) := by ring
  rw [h_num, h_den, mul_div_mul_left _ _ hc_ne_zero]

/-- The real image `mapGL ℝ γ` of `γ ∈ SL₂(ℤ)` has unit determinant. -/
private theorem mapGL_SL_det_val_eq_one (γ : SL(2, ℤ)) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ).det.val = 1 := by
  show ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1
  rw [show ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Int.castRingHom ℝ).mapMatrix γ.val) by rw [mapGL_coe_matrix]; rfl,
    ← RingHom.map_det, γ.property, map_one]

/-- The real image `glMap (T_p_lower p hp)` has positive determinant `(= p)`. -/
private theorem glMap_T_p_lower_det_val_pos (p : ℕ) (hp : 0 < p) :
    0 < (glMap (T_p_lower p hp) : GL (Fin 2) ℝ).det.val :=
  glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp)

/-- The real image `glMap (T_p_upper p hp b)` has positive determinant `(= p)`. -/
private theorem glMap_T_p_upper_det_val_pos (p : ℕ) (hp : 0 < p) (b : ℕ) :
    0 < (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ).det.val :=
  glMap_det_pos_of_rat_det_pos _ (T_p_upper_det_pos p hp b)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_T_p_upper_smul_eq_shift_smul
    (p : ℕ) (hp : 0 < p) (b : ℕ) (τ : ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • τ =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • τ := by
  have h_det_pos_LHS : 0 <
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos (glMap_T_p_lower_det_val_pos p hp)
      (glMap_T_p_upper_det_val_pos p hp b)
  have h_det_pos_RHS : 0 <
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b : ℤ)) :
        GL (Fin 2) ℝ).det.val := by
    rw [mapGL_SL_det_val_eq_one]; exact one_pos
  refine UpperHalfPlane_smul_eq_of_matrix_smul_eq _ _ h_det_pos_LHS h_det_pos_RHS
    (p : ℝ) (by exact_mod_cast hp.ne') ?_ τ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glMap, T_p_lower, T_p_upper, mapGL_coe_matrix, shiftSL_loc,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.map,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Units.val_mul,
      algebraMap_int_eq, Matrix.smul_apply] <;>
    ring

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_M_infty_smul_eq_M_infty_Gamma1_factor_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (τ : ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)) • τ =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • τ := by
  have h_M_infty_eq : (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (M_infty_Gamma1_factor N p hpN 0)) := by
    rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp hpN 0,
      mul_inv_cancel_left]
  rw [h_M_infty_eq, ← mul_assoc, mul_smul]
  rw [T_p_lower_mul_T_p_upper_smul_eq_shift_smul p hp 0]
  show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc ((0 : ℕ) : ℤ))
    : GL (Fin 2) ℝ) • _ = _
  rw [show shiftSL_loc ((0 : ℕ) : ℤ) = (1 : SL(2, ℤ)) by
    apply Subtype.ext; ext i j
    fin_cases i <;> fin_cases j <;>
      simp [shiftSL_loc, Matrix.of_apply]]
  simp [MonoidHom.map_one, one_smul]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma smul_set_eq_of_smul_eq
    {α β : GL (Fin 2) ℝ} (hsmul : ∀ τ : ℍ, α • τ = β • τ) (S : Set ℍ) :
    α • S = β • S := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, (hsmul σ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    exact ⟨σ, hσ, hsmul σ⟩

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_T_p_upper_smul_set_eq_shift_smul
    (p : ℕ) (hp : 0 < p) (b : ℕ) (S : Set ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) • S =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (shiftSL_loc (b : ℤ)) : GL (Fin 2) ℝ) • S :=
  smul_set_eq_of_smul_eq (T_p_lower_mul_T_p_upper_smul_eq_shift_smul p hp b) S

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_mul_M_infty_smul_set_eq_M_infty_Gamma1_factor_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) *
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)) • S =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • S :=
  smul_set_eq_of_smul_eq
    (T_p_lower_mul_M_infty_smul_eq_M_infty_Gamma1_factor_smul (N := N) p hp hpN) S

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma mapGL_sigma_p_smul_T_p_lower_smul_set_eq_M_infty_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ) •
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) • S) =
    (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) • S := by
  rw [smul_smul,
    ← glMap_M_infty_eq_mapGL_sigma_p_mul_glMap_T_p_lower (N := N) p hp hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma mapGL_sigma_p_inv_smul_M_infty_smul_set_eq_T_p_lower_smul
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ) •
      ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) • S) =
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) • S := by
  rw [← mapGL_sigma_p_smul_T_p_lower_smul_set_eq_M_infty_smul (N := N) p hp hpN S,
    smul_smul, smul_smul, ← map_mul, inv_mul_cancel, map_one, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem M_infty_iUnion_eq_mapGL_sigma_p_smul_T_p_lower_iUnion
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ))) =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ) •
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun q ↦ ?_
  rw [mapGL_sigma_p_smul_T_p_lower_smul_set_eq_M_infty_smul (N := N) p hp hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_M_infty_iUnion_eq_sigma_p_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      F G =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ)) := by
  rw [M_infty_iUnion_eq_mapGL_sigma_p_smul_T_p_lower_iUnion (N := N) p hp hpN]
  exact peterssonInner_mapGL_smul_eq_slash _ _ F G

open UpperHalfPlane ModularGroup MeasureTheory in
theorem peterssonInner_LHS_M_infty_residual_after_sigma_p
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (G : ℍ → ℂ) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) G =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      ⇑f
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ)) := by
  rw [peterssonInner_M_infty_iUnion_eq_sigma_p_slash (N := N) p hp hpN,
    slash_sigma_p_diamond_inv_cusp_eq p hp hpN f]

open UpperHalfPlane ModularGroup MeasureTheory in
theorem peterssonInner_RHS_M_infty_residual_after_sigma_p
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (F : ℍ → ℂ) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      F ⇑g =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ))
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) := by
  rw [peterssonInner_M_infty_iUnion_eq_sigma_p_slash (N := N) p hp hpN,
    ← coe_diamondOp_cusp_eq_slash_sigma_p p hp hpN g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_iUnion_eq_mapGL_sigma_p_inv_smul_M_infty_iUnion
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ))) =
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ) •
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun q ↦ ?_
  rw [mapGL_sigma_p_inv_smul_M_infty_smul_set_eq_T_p_lower_smul (N := N) p hp hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_iUnion_eq_sigma_p_inv_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      F G =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ)) := by
  rw [T_p_lower_iUnion_eq_mapGL_sigma_p_inv_smul_M_infty_iUnion (N := N) p hp hpN]
  exact peterssonInner_mapGL_smul_eq_slash _ _ F G

private noncomputable def T_p_lower_tile_family
    (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    Option (Fin p) → SL(2, ℤ)
  | none => M_infty_Gamma1_factor N p hpN 0
  | some b => shiftSL_loc (b.val : ℤ)

private noncomputable def Hecke_rep_family
    (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    Option (Fin p) → GL (Fin 2) ℝ
  | none => (glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ)
  | some b => (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_lower_smul_Hecke_FD_eq_iUnion_tile
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) (S : Set ℍ) :
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      (⋃ i : Option (Fin p), Hecke_rep_family N p hp hpN i • S) =
    ⋃ i : Option (Fin p),
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S := by
  rw [Set.smul_set_iUnion]
  refine Set.iUnion_congr fun i ↦ ?_
  match i with
  | none =>
    show (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      ((glMap (M_infty N p hp hpN) : GL (Fin 2) ℝ) • S) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) • S
    rw [← mul_smul]
    exact T_p_lower_mul_M_infty_smul_set_eq_M_infty_Gamma1_factor_smul
      (N := N) p hp hpN S
  | some b =>
    show (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
      ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) • S) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (shiftSL_loc (b.val : ℤ)) : GL (Fin 2) ℝ) • S
    rw [← mul_smul]
    exact T_p_lower_mul_T_p_upper_smul_set_eq_shift_smul p hp b.val S

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_tile_eq_slash
    (p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (S : Set ℍ) (F G : ℍ → ℂ)
    (i : Option (Fin p)) :
    peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) F G =
    peterssonInner k S
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) :=
  peterssonInner_mapGL_smul_eq_slash _ (T_p_lower_tile_family N p hpN i) F G

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_iUnion_tile_eq_sum
    (p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) (S : Set ℍ) (F G : ℍ → ℂ)
    (hm : ∀ i : Option (Fin p), NullMeasurableSet
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp)
    (hd : Pairwise (fun i j : Option (Fin p) ↦ AEDisjoint μ_hyp
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S)
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN j) : GL (Fin 2) ℝ) • S)))
    (hfi : IntegrableOn (fun τ ↦ petersson k F G τ)
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp) :
    peterssonInner k
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) F G =
    ∑ i : Option (Fin p), peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) F G :=
  peterssonInner_iUnion_finite_aedisjoint _ hm hd F G hfi

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_lower_Hecke_FD_eq_sum_tile_slash
    (p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N)
    (S : Set ℍ) (F G : ℍ → ℂ)
    (hm : ∀ i : Option (Fin p), NullMeasurableSet
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp)
    (hd : Pairwise (fun i j : Option (Fin p) ↦ AEDisjoint μ_hyp
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S)
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN j) : GL (Fin 2) ℝ) • S)))
    (hfi : IntegrableOn (fun τ ↦ petersson k F G τ)
      (⋃ i : Option (Fin p),
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) • S) μ_hyp) :
    peterssonInner k
      ((glMap (T_p_lower p hp) : GL (Fin 2) ℝ) •
        (⋃ i : Option (Fin p), Hecke_rep_family N p hp hpN i • S)) F G =
    ∑ i : Option (Fin p), peterssonInner k S
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) := by
  rw [T_p_lower_smul_Hecke_FD_eq_iUnion_tile (N := N) p hp hpN S,
      peterssonInner_T_p_lower_iUnion_tile_eq_sum (N := N) p hpN S F G hm hd hfi]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact peterssonInner_T_p_lower_tile_eq_slash (N := N) p hpN S F G i

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem mapGL_tile_mul_peterssonAdj_Hecke_rep_eq_glMap_T_p_lower
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ) *
      peterssonAdj (Hecke_rep_family N p hp.pos hpN i) =
    (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
  match i with
  | none =>
    show ((mapGL ℝ : SL(2, ℤ) →* _) (M_infty_Gamma1_factor N p hpN 0)
      : GL (Fin 2) ℝ) *
      peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)
    rw [show (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) =
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0)) by
      rw [← glMap_T_p_upper_inv_mul_M_infty_eq_mapGL_Gamma1 N p hp.pos hpN 0,
        mul_inv_cancel_left]]
    rw [peterssonAdj_mul, peterssonAdj_mapGL_SL_eq_inv,
      peterssonAdj_glMap_T_p_upper_zero_eq_glMap_T_p_lower]
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0)) *
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0))⁻¹ *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (M_infty_Gamma1_factor N p hpN 0))⁻¹) *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) by group]
    rw [mul_inv_cancel, one_mul]
  | some b =>
    show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b.val : ℤ))
      : GL (Fin 2) ℝ) *
      peterssonAdj (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) =
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)
    rw [peterssonAdj_T_p_upper_eq_shift_mul_lower p hp.pos b.val]
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b.val : ℤ))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b.val : ℤ))) *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (b.val : ℤ)) *
          (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (shiftSL_loc (-(b.val : ℤ)))) *
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) by group]
    rw [← map_mul]
    rw [show shiftSL_loc (b.val : ℤ) * shiftSL_loc (-(b.val : ℤ)) =
        (1 : SL(2, ℤ)) by
      apply Subtype.ext; ext i j
      fin_cases i <;> fin_cases j <;>
        simp [shiftSL_loc, Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply]]
    rw [map_one, one_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_swap_via_uniform_adj
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) (i : Option (Fin p)) :
    peterssonInner k (fd : Set ℍ)
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (G ∣[k] (Hecke_rep_family N p hp.pos hpN i)) =
    peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      (F ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) G := by
  have hα : 0 < (Hecke_rep_family N p hp.pos hpN i).det.val := by
    match i with
    | none =>
      exact glMap_M_infty_det_pos N p hp.pos hpN
    | some b =>
      show 0 < ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det
      rw [show ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
          ((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
      rw [show (((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ)).det =
          (algebraMap ℚ ℝ) (((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).det) from
            (RingHom.map_det _ _).symm]
      rw [show ((T_p_upper p hp.pos b.val : GL (Fin 2) ℚ).val).det = (p : ℚ) by
        simp [T_p_upper, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.det_fin_two, Matrix.of_apply]]
      show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
      rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
      exact_mod_cast hp.pos
  rw [peterssonInner_slash_adjoint_right _ _ hα]
  rw [show (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) ∣[k]
        peterssonAdj (Hecke_rep_family N p hp.pos hpN i) =
        F ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) by
    rw [← SlashAction.slash_mul,
      mapGL_tile_mul_peterssonAdj_Hecke_rep_eq_glMap_T_p_lower (N := N) p hp hpN i]]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_swap_via_uniform_adj_slot1
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (F G : ℍ → ℂ) (i : Option (Fin p)) :
    peterssonInner k (fd : Set ℍ)
      (G ∣[k] (Hecke_rep_family N p hp.pos hpN i))
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) =
    peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) G
      (F ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [← peterssonInner_conj_symm,
      peterssonInner_swap_via_uniform_adj (N := N) p hp hpN F G i,
      peterssonInner_conj_symm]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_per_X_sum_iff_Hecke_FD_residual
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : ℍ → ℂ)
    (hm : ∀ i : Option (Fin p), NullMeasurableSet
      (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) μ_hyp)
    (hd : Pairwise (fun i j : Option (Fin p) ↦ AEDisjoint μ_hyp
      (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      (Hecke_rep_family N p hp.pos hpN j • (fd : Set ℍ))))
    (hfi_LHS : IntegrableOn (fun τ ↦ petersson k f
        (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) μ_hyp)
    (hfi_RHS : IntegrableOn (fun τ ↦ petersson k
        (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g τ)
      (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ)) μ_hyp) :
    (∑ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
      (f ∣[k] (Hecke_rep_family N p hp.pos hpN i))
      (g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))) =
      peterssonInner k
        (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
        f (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∧
    (∑ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
      (f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
      (g ∣[k] (Hecke_rep_family N p hp.pos hpN i))) =
      peterssonInner k
        (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
        (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g := by
  refine ⟨?_, ?_⟩
  ·
    have h_per_X : ∀ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
        (f ∣[k] (Hecke_rep_family N p hp.pos hpN i))
        (g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ)) =
        peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
          f (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := fun i ↦ peterssonInner_swap_via_uniform_adj_slot1 (N := N) p hp hpN g f i
    rw [Finset.sum_congr rfl (fun i _ ↦ h_per_X i)]
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun i : Option (Fin p) ↦ Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      hm hd f (g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) hfi_LHS).symm
  ·
    have h_per_X : ∀ i : Option (Fin p), peterssonInner k (fd : Set ℍ)
        (f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (T_p_lower_tile_family N p hpN i) : GL (Fin 2) ℝ))
        (g ∣[k] (Hecke_rep_family N p hp.pos hpN i)) =
        peterssonInner k (Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
          (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g := fun i ↦ peterssonInner_swap_via_uniform_adj (N := N) p hp hpN f g i
    rw [Finset.sum_congr rfl (fun i _ ↦ h_per_X i)]
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun i : Option (Fin p) ↦ Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
      hm hd (f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) g hfi_RHS).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_smul_eq_of_matrix_proportional
    {α β : GL (Fin 2) ℝ} (hα : 0 < α.det.val) (hβ : 0 < β.det.val)
    (c : ℝ) (hc : c ≠ 0)
    (hMat : (α : Matrix (Fin 2) (Fin 2) ℝ) = c • (β : Matrix (Fin 2) (Fin 2) ℝ))
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k (α • D) F G = peterssonInner k (β • D) F G := by
  congr 1
  exact smul_set_eq_of_smul_eq
    (UpperHalfPlane_smul_eq_of_matrix_smul_eq α β hα hβ c hc hMat) D

open UpperHalfPlane ModularGroup MeasureTheory in
private def Hecke_FD_integral_residual
    (p : ℕ) [NeZero N] (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
    (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
    ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
  peterssonInner k
    (⋃ i : Option (Fin p), Hecke_rep_family N p hp.pos hpN i • (fd : Set ℍ))
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_smul_set_GL_pos
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (D : Set ℍ) (F G : ℍ → ℂ) :
    peterssonInner k (α • D) F G =
      ∫ τ in D, petersson k F G ((⟨α, hα⟩ : GL(2, ℝ)⁺) • τ) ∂μ_hyp := by
  simp only [peterssonInner]
  set α' : GL(2, ℝ)⁺ := ⟨α, hα⟩
  rw [show (α • D : Set ℍ) = (fun τ ↦ α' • τ) '' D by
    rw [Set.image_smul]; rfl]
  exact (measurePreserving_smul α' μ_hyp).setIntegral_image_emb
    (measurableEmbedding_const_smul α') _ D

open UpperHalfPlane ModularGroup MeasureTheory in
lemma peterssonInner_slash_adj_M_infty_q_summand_eq
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] (mapGL ℝ q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ q⁻¹ : GL (Fin 2) ℝ) • (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_slash_adjoint_coset (glMap (M_infty N p hp.pos hpN))
        (glMap_M_infty_det_pos N p hp.pos hpN) q ⇑f ⇑g]
  rw [slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
    p hp hpN g]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_ds_p_plus_one_family_union_collapse_per_q_split
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) =
    peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_slash_adj_M_infty_q_summand_eq p hp hpN q f g]
  congr 1
  exact sum_peterssonInner_upper_family_per_b_rewrite p hp hpN q f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_M_infty_plus_upper_union_tile_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfi_upper : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) =
    peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) +
      peterssonInner k
        (⋃ b ∈ Finset.range p,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
              (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_ds_p_plus_one_family_union_collapse_per_q_split p hp hpN q f g]; congr 1
  rw [show (∑ b ∈ Finset.range p,
        peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))) =
      ∑ b ∈ Finset.range p,
        peterssonInner k (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
          ⇑f
          ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) from
    Finset.sum_congr rfl fun b _ ↦ by rw [mul_smul]]
  exact peterssonInner_T_p_upper_family_union_collapse_per_q hp hpN q f g hfi_upper

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_glQ_then_mapGL_SL_eq_combinedGL
    (F : UpperHalfPlane → ℂ) (α : GL (Fin 2) ℚ) (δ : SL(2, ℤ)) :
    ((F ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) =
    F ∣[k] ((glMap α : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) := by
  rw [← SlashAction.slash_mul]
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_glQ_mapGLSL_to_combinedGL
    (F : UpperHalfPlane → ℂ) (α : GL (Fin 2) ℚ) (δ : SL(2, ℤ)) :
    ((F ∣[k] (α : GL (Fin 2) ℚ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) =
    F ∣[k] ((glMap α : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) := by
  change ((F ∣[k] (glMap α : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ)) =
    F ∣[k] ((glMap α : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) δ))
  rw [← SlashAction.slash_mul]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Integrability over `fd` of the per-tile combined-`GL` Petersson integrand
`petersson (f' ∣[k] q⁻¹) (g' ∣[k] (glMap α · q⁻¹))` arising in the per-`q`
coset-sum distribution; the combined slash is unfolded back to a `GL(2,ℚ)`
slash followed by the `q⁻¹` twist, which `integrableOn_petersson_cuspform_mixed_slash_on_fd`
discharges. -/
private lemma integrableOn_petersson_combinedGL_tile_on_fd
    (f' g' : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (α : GL (Fin 2) ℚ)
    (q : SL(2, ℤ)) :
    IntegrableOn (fun τ ↦ petersson k
        (⇑f' ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑g' ∣[k] ((glMap α : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) τ)
      (ModularGroup.fd : Set ℍ) μ_hyp := by
  rw [show (⇑g' ∣[k] ((glMap α : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
      (⇑g' ∣[k] ((α.map (Rat.castHom ℝ)) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) from
    (slash_glQ_then_mapGL_SL_eq_combinedGL (k := k) ⇑g' α q⁻¹).symm]
  exact integrableOn_petersson_cuspform_mixed_slash_on_fd f' g' α q⁻¹

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_LHS_per_q_distribute
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) := by
  have h_Tpf : (⇑(heckeT_p_cusp k p hp hpN f) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos ⇑f.toModularForm' +
        ⇑f.toModularForm' ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN f.toModularForm'
  rw [h_Tpf, SlashAction.add_slash]
  rw [show heckeT_p_ut k p hp.pos ⇑f.toModularForm' =
      ∑ b ∈ Finset.range p,
        ⇑f.toModularForm' ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl]
  rw [SlashAction.sum_slash]
  simp_rw [slash_glQ_mapGLSL_to_combinedGL]
  rw [add_comm]
  set G : UpperHalfPlane → ℂ :=
    ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) with hG_def
  set F0 : UpperHalfPlane → ℂ :=
    ⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hF0_def
  set F : ℕ → UpperHalfPlane → ℂ := fun b ↦ ⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hF_def
  have h0 : IntegrableOn (fun τ ↦ petersson k G F0 τ) ModularGroup.fd μ_hyp :=
    integrableOn_petersson_combinedGL_tile_on_fd g f (M_infty N p hp.pos hpN) q
  have hF : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ petersson k G (F b) τ) ModularGroup.fd μ_hyp := fun b _ ↦
    integrableOn_petersson_combinedGL_tile_on_fd g f (T_p_upper p hp.pos b) q
  exact peterssonInner_add_finset_sum_left (Finset.range p) F0 F G ModularGroup.fd h0 hF

open UpperHalfPlane in
/-- Pointwise AM-GM bound for the Petersson integrand: the off-diagonal product
is controlled by the average of the two diagonal products. -/
private lemma norm_petersson_le_half_add_diag (a b : ℍ → ℂ) (τ : ℍ) :
    ‖petersson k a b τ‖ ≤ (‖petersson k a a τ‖ + ‖petersson k b b τ‖) / 2 := by
  simp only [petersson, norm_mul, Complex.norm_conj]
  have h_im_nn : (0 : ℝ) ≤ ‖((τ.im : ℂ) ^ k)‖ := norm_nonneg _
  nlinarith [mul_nonneg (sq_nonneg (‖a τ‖ - ‖b τ‖)) h_im_nn,
    sq_nonneg (‖a τ‖ - ‖b τ‖), norm_nonneg (a τ), norm_nonneg (b τ), h_im_nn]

open UpperHalfPlane MeasureTheory in
/-- The fundamental domain `fd` is null-measurable for the hyperbolic measure
(it is closed, being an intersection of two closed half-spaces). -/
private lemma nullMeasurableSet_modularGroup_fd :
    NullMeasurableSet (ModularGroup.fd : Set ℍ) μ_hyp :=
  ((isClosed_le continuous_const
      (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)).inter
    (isClosed_le (continuous_abs.comp UpperHalfPlane.continuous_re)
      continuous_const)).measurableSet.nullMeasurableSet

open UpperHalfPlane MeasureTheory ConjAct Pointwise in
/-- Integrability of `petersson f (g ∣[k] glMap σ)` over any finite-measure set.
The translated form `g ∣[k] glMap σ` is a cusp form for the arithmetic conjugate
group, giving a global self-bound; AM-GM then yields a uniform integrand bound,
which combines with the finite measure of `S`. -/
private lemma integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (σ : GL (Fin 2) ℚ)
    {S : Set ℍ} (hS : μ_hyp S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k ⇑f
      (⇑g ∣[k] (glMap σ : GL (Fin 2) ℝ)) τ) S μ_hyp := by
  haveI hArith : (toConjAct (glMap σ : GL (Fin 2) ℝ)⁻¹ •
      ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
    have h := Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) σ⁻¹
    have h_inv : (((σ⁻¹ : GL (Fin 2) ℚ).map (Rat.castHom ℝ)) : GL (Fin 2) ℝ) =
        (glMap σ : GL (Fin 2) ℝ)⁻¹ := by rw [map_inv]; rfl
    rwa [h_inv] at h
  let g_tr : CuspForm
      (toConjAct (glMap σ : GL (Fin 2) ℝ)⁻¹ • ((Gamma1 N).map (mapGL ℝ))) k :=
    CuspForm.translate g (glMap σ : GL (Fin 2) ℝ)
  have h_gtr_coe : (⇑g_tr : ℍ → ℂ) = ⇑g ∣[k] (glMap σ : GL (Fin 2) ℝ) := rfl
  obtain ⟨C_f, hC_f⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f f
  obtain ⟨C_gtr, hC_gtr⟩ := CuspFormClass.petersson_bounded_left k _ g_tr g_tr
  have h_AM_GM : ∀ τ, ‖petersson k ⇑f
      (⇑g ∣[k] (glMap σ : GL (Fin 2) ℝ)) τ‖ ≤ (C_f + C_gtr) / 2 := fun τ ↦ by
    rw [← h_gtr_coe]
    have hh := norm_petersson_le_half_add_diag (k := k) ⇑f ⇑g_tr τ
    linarith [hC_f τ, hC_gtr τ, hh]
  refine IntegrableOn.of_bound hS ?_ ((C_f + C_gtr) / 2) (ae_of_all _ h_AM_GM)
  refine (petersson_continuous k (ModularFormClass.continuous f.toModularForm') ?_
    ).aestronglyMeasurable.restrict
  rw [← h_gtr_coe]; exact ModularFormClass.continuous g_tr

open UpperHalfPlane ModularGroup MeasureTheory ConjAct Pointwise in
private lemma integrableOn_petersson_upper_union_uniform_gslot_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp := by
  set σ : GL (Fin 2) ℚ :=
    T_p_upper p hp.pos 0 *
      ((mapGL ℚ : SL(2, ℤ) →* _)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) with hσ_def
  have h_σ_eq : (glMap σ : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    rw [hσ_def, map_mul, glMap_mapGL_Q_eq_mapGL_R]
  rw [show (fun τ ↦ petersson k ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ) =
      (fun τ ↦ petersson k ⇑f (⇑g ∣[k] (glMap σ : GL (Fin 2) ℝ)) τ) from
    funext fun τ ↦ by rw [h_σ_eq, SlashAction.slash_mul]]
  have h_α_det_pos : ∀ b,
      0 < ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* _) q⁻¹ : GL (Fin 2) ℝ)).det.val := fun b ↦ by
    rw [map_mul, Units.val_mul, mapGL_SL_det_val_eq_one, mul_one]
    exact glMap_T_p_upper_det_val_pos p hp.pos b
  refine integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g σ ?_
  refine lt_of_le_of_lt (measure_biUnion_finset_le _ _)
    (ENNReal.sum_lt_top.mpr fun b _ ↦ ?_)
  rw [measure_glPos_smul_eq _ (h_α_det_pos b) nullMeasurableSet_modularGroup_fd]
  exact hyperbolicMeasure_fd_lt_top

open UpperHalfPlane ModularGroup MeasureTheory in
lemma peterssonInner_heckeT_p_LHS_per_q_to_union_tiles
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) +
    peterssonInner k
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := by
  rw [peterssonInner_heckeT_p_LHS_per_q_distribute p hp hpN q f g]
  exact peterssonInner_M_infty_plus_upper_union_tile_per_q p hp hpN q f g
    (integrableOn_petersson_upper_union_uniform_gslot_per_q p hp hpN q f g)

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_LHS_per_q_to_union_tiles_T_p_lower_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k
      (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
        (ModularGroup.fd : Set UpperHalfPlane))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
    peterssonInner k
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [peterssonInner_heckeT_p_LHS_per_q_to_union_tiles p hp hpN q f g,
    show (⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) =
      ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) from
        (slash_T_p_lower_eq_T_p_upper_zero_slash_gamma0 p hp hpN g).symm,
    ← mul_smul]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_eq_per_q_T_p_lower_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
       peterssonInner k
        (⋃ b ∈ Finset.range p,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  change peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
        GL (Fin 2) ℝ)) = _
  exact peterssonInner_heckeT_p_LHS_per_q_to_union_tiles_T_p_lower_form
    p hp hpN (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `T_p`-upper part of the per-`q` Petersson coset sum: summing the per-`q`
`b`-biUnion tiles equals summing, over `b`, the `q`-biUnion tiles.  Expand each
per-`q` biUnion into a `b`-sum, swap the order of summation, then collapse each
`b`-fixed `q`-biUnion. -/
private theorem petN_T_p_upper_tiles_sum_q_eq_sum_b
    (p : ℕ) (hp : Nat.Prime p)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_upper_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_disj : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((Finset.range p : Finset ℕ) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b₁) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b₂) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_per_q_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k
          (⋃ b ∈ Finset.range p,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [Finset.sum_congr rfl fun q _ ↦ peterssonInner_biUnion_finset_ae (Finset.range p)
      (fun b hb ↦ h_upper_per_q_meas q b hb) (h_upper_per_q_disj q) ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) (h_upper_per_q_int q),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  exact (peterssonInner_iUnion_finite_aedisjoint
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
    (h_upper_meas b hb) (h_upper_disj b hb) ⇑f
    (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
    (h_upper_int b hb)).symm

open UpperHalfPlane ModularGroup MeasureTheory in
theorem petN_heckeT_p_eq_per_alpha_HeckeFD_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_M_infty_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_disj : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((Finset.range p : Finset ℕ) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b₁) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b₂) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_per_q_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
    ∑ b ∈ Finset.range p,
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  rw [petN_heckeT_p_eq_per_q_T_p_lower_form p hp hpN f g, Finset.sum_add_distrib]
  congr 1
  ·
    exact (peterssonInner_iUnion_finite_aedisjoint
      (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
      h_M_infty_meas h_M_infty_disj ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) h_M_infty_int).symm
  · exact petN_T_p_upper_tiles_sum_q_eq_sum_b p hp f g h_upper_disj h_upper_meas
      h_upper_int h_upper_per_q_disj h_upper_per_q_meas h_upper_per_q_int

open UpperHalfPlane ModularGroup MeasureTheory in
theorem petN_diamond_heckeT_p_eq_per_alpha_HeckeFD_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_M_infty_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_disj : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((Finset.range p : Finset ℕ) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b₁) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b₂) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_per_q_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
    ∑ b ∈ Finset.range p,
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g := by
  rw [← petN_conj_symm]
  rw [petN_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN g
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
    h_M_infty_disj h_M_infty_meas h_M_infty_int
    h_upper_disj h_upper_meas h_upper_int
    h_upper_per_q_disj h_upper_per_q_meas h_upper_per_q_int]
  rw [map_add, map_sum]
  congr 1
  · exact peterssonInner_conj_symm k _ _ _
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    exact peterssonInner_conj_symm k _ _ _

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_RHS_per_q_distribute
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(heckeT_p_cusp k p hp hpN
            (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) := by
  have h_Tp_ug : (⇑(heckeT_p_cusp k p hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) :
      UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' +
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' ∣[k]
        (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm'
  rw [h_Tp_ug, SlashAction.add_slash]
  rw [show heckeT_p_ut k p hp.pos
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' =
      ∑ b ∈ Finset.range p,
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g).toModularForm' ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl]
  rw [SlashAction.sum_slash]
  simp_rw [slash_glQ_mapGLSL_to_combinedGL]
  rw [add_comm]
  set F : UpperHalfPlane → ℂ :=
    ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) with hF_def
  set G0 : UpperHalfPlane → ℂ :=
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG0_def
  set G : ℕ → UpperHalfPlane → ℂ := fun b ↦ ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG_def
  have h0 : IntegrableOn (fun τ ↦ petersson k F G0 τ) ModularGroup.fd μ_hyp :=
    integrableOn_petersson_combinedGL_tile_on_fd f
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) (M_infty N p hp.pos hpN) q
  have hG_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ petersson k F (G b) τ) ModularGroup.fd μ_hyp := fun b _ ↦
    integrableOn_petersson_combinedGL_tile_on_fd f
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) (T_p_upper p hp.pos b) q
  exact peterssonInner_add_finset_sum_right (Finset.range p) F G0 G ModularGroup.fd h0 hG_int

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_distribute
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(heckeT_p_cusp k p hp hpN g) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) := by
  rw [coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f]
  have h_Tp_g : (⇑(heckeT_p_cusp k p hp hpN g) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos ⇑g.toModularForm' +
      ⇑g.toModularForm' ∣[k]
        (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
    heckeT_p_fun_eq_coset_sum k hp hpN g.toModularForm'
  rw [h_Tp_g, SlashAction.add_slash]
  rw [show heckeT_p_ut k p hp.pos ⇑g.toModularForm' =
      ∑ b ∈ Finset.range p,
        ⇑g.toModularForm' ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl]
  rw [SlashAction.sum_slash]
  simp_rw [slash_glQ_mapGLSL_to_combinedGL]
  rw [add_comm]
  set F : UpperHalfPlane → ℂ :=
    (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
      GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹) with hF_def
  set G0 : UpperHalfPlane → ℂ :=
    ⇑g ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG0_def
  set G : ℕ → UpperHalfPlane → ℂ := fun b ↦ ⇑g ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹)) with hG_def
  have h0 : IntegrableOn (fun τ ↦ petersson k F G0 τ) ModularGroup.fd μ_hyp := by
    rw [hF_def, ← coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f]
    exact integrableOn_petersson_combinedGL_tile_on_fd
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) g (M_infty N p hp.pos hpN) q
  have hG_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ petersson k F (G b) τ) ModularGroup.fd μ_hyp := fun b _ ↦ by
    rw [hF_def, ← coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f]
    exact integrableOn_petersson_combinedGL_tile_on_fd
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) g (T_p_upper p hp.pos b) q
  exact peterssonInner_add_finset_sum_right (Finset.range p) F G0 G ModularGroup.fd h0 hG_int

open UpperHalfPlane ModularGroup in
lemma slash_diamond_inv_T_p_upper_eq_T_p_lower_delta
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) (q : SL(2, ℤ))
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    ⇑g ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h_diamond : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [h_diamond, ← SlashAction.slash_mul, ← mul_assoc,
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp.pos hpN b]

open UpperHalfPlane ModularGroup in
lemma slash_diamond_inv_M_infty_eq_T_p_lower_epsilon
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (q : SL(2, ℤ))
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    ⇑g ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  have h_diamond : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  rw [h_diamond, ← SlashAction.slash_mul, ← mul_assoc,
    mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp.pos hpN]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_RHS_per_q_normalized
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑(heckeT_p_cusp k p hp hpN
            (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
                GL (Fin 2) ℝ))) := by
  rw [peterssonInner_heckeT_p_RHS_per_q_distribute p hp hpN q f g]
  congr 1
  · rw [slash_diamond_inv_M_infty_eq_T_p_lower_epsilon p hp hpN q g]
  · refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b q g]

open UpperHalfPlane ModularGroup MeasureTheory in
lemma peterssonInner_SL_inv_eq_mapGL_inv
    (F G : UpperHalfPlane → ℂ) (q : SL(2, ℤ)) :
    peterssonInner k ModularGroup.fd
      (F ∣[k] (q⁻¹ : SL(2, ℤ)))
      (G ∣[k] (q⁻¹ : SL(2, ℤ))) =
    peterssonInner k ModularGroup.fd
      (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
      (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
lemma petN_diamond_heckeT_p_symm_RHS_sum_distributed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑(heckeT_p_cusp k p hp hpN g) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_SL_inv_eq_mapGL_inv]
  exact peterssonInner_heckeT_p_symm_RHS_per_q_distribute p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_f_heckeT_p_RHS_sum_normalized
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        (⇑(heckeT_p_cusp k p hp hpN
            (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_SL_inv_eq_mapGL_inv]
  exact peterssonInner_heckeT_p_RHS_per_q_normalized p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))
        (⇑g ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q * γ⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        ⇑g := by
  have hq'_inv : ((q * γ⁻¹)⁻¹ : SL(2, ℤ)) = γ * q⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  have h_slash_γ : (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ :
      GL (Fin 2) ℝ)) = ⇑f := by
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) =
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl, ← ModularForm.SL_slash]
    exact slash_Gamma1_eq f γ hγ
  have h_g_slash_chain :
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ((q * γ⁻¹)⁻¹ : SL(2, ℤ)) :
          GL (Fin 2) ℝ) := by
    rw [hq'_inv, map_mul, ← mul_assoc]
  have h_f_slash_eq :
      (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) =
      (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) ((q * γ⁻¹)⁻¹ : SL(2, ℤ)) :
        GL (Fin 2) ℝ)) := by
    rw [hq'_inv, map_mul, SlashAction.slash_mul, h_slash_γ]
  rw [h_g_slash_chain, h_f_slash_eq]
  rw [peterssonInner_slash_adjoint_coset_right
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)
        (glMap_T_p_lower_det_val_pos p hp.pos) (q * γ⁻¹) ⇑f ⇑g]
  rw [peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero p hp.pos]

private lemma glMap_M_infty_mul_mapGL_inv_eq_gamma0_inv_mul_shifted
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (q : SL(2, ℤ)) :
    (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ)⁻¹ *
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
            GL (Fin 2) ℝ)) := by
  have h_core :=
    mapGL_gamma0_mul_M_infty_eq_T_p_lower_mul_mapGL_epsilon N p hp.pos hpN
  have h_inv_rewrite :
      ((q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : SL(2, ℤ)) =
      (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0) * q⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [h_inv_rewrite, map_mul,
    ← mul_assoc (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ), ← h_core]
  group

private lemma peterssonInner_LHS_M_infty_tile_g_slot_to_peterssonAdj
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    UpperHalfPlane.peterssonInner k
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
    UpperHalfPlane.peterssonInner k
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      (⇑g ∣[k]
        peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) := by
  rw [← slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_upper_zero_slash_gamma0
      p hp hpN g]

private lemma glMap_T_p_upper_mul_mapGL_inv_eq_gamma0_inv_mul_shifted
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ) (q : SL(2, ℤ)) :
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ)⁻¹ *
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
            GL (Fin 2) ℝ)) := by
  have h_core :=
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp.pos hpN b
  have h_inv_rewrite :
      ((q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ : SL(2, ℤ)) =
      gamma0_T_p_upper_Gamma1_factor N p hpN b * q⁻¹ := by
    rw [mul_inv_rev, inv_inv]
  rw [h_inv_rewrite, map_mul,
    ← mul_assoc (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ), ← h_core]
  group

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_RHS_per_q_normalized_shifted_tile
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
              GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ :
                GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          ⇑g := by
  rw [peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0)
        (gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
          N p hpN) f g]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  exact peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
    (gamma0_T_p_upper_Gamma1_factor N p hpN b)
    (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b) f g

open UpperHalfPlane ModularGroup MeasureTheory in
open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_M_infty_branch_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) := by
  have h := peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
    (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
      M_infty_Gamma1_factor N p hpN 0)
    (gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
      N p hpN)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)
  rw [coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f,
      coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN g] at h
  conv_lhs =>
    rw [glMap_M_infty_mul_mapGL_inv_eq_gamma0_inv_mul_shifted p hp hpN q,
      SlashAction.slash_mul,
      show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))⁻¹ =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) from (map_inv _ _).symm,
      show ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ)) =
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) by
        rw [mul_inv_rev, inv_inv, map_mul, ← mul_assoc]]
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_upper_branch_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
              GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) := by
  have h := peterssonInner_T_p_lower_slash_adj_coset_right_Gamma1_twist p hp hpN q
    (gamma0_T_p_upper_Gamma1_factor N p hpN b)
    (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)
  rw [coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN f,
      coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv p hp hpN g] at h
  conv_lhs =>
    rw [glMap_T_p_upper_mul_mapGL_inv_eq_gamma0_inv_mul_shifted p hp hpN b q,
      SlashAction.slash_mul,
      show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ))⁻¹ =
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) from (map_inv _ _).symm,
      show ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
            GL (Fin 2) ℝ)) =
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b) :
            GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) by
        rw [mul_inv_rev, inv_inv, map_mul, ← mul_assoc]]
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_heckeT_p_symm_RHS_per_q_distribute_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k ModularGroup.fd
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
    peterssonInner k
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q * (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q * (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) := by
  rw [peterssonInner_heckeT_p_symm_RHS_per_q_M_infty_branch_shifted_tile_residual
      p hp hpN q f g]
  congr 1
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  exact peterssonInner_heckeT_p_symm_RHS_per_q_upper_branch_shifted_tile_residual
    p hp hpN b q f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_diamond_heckeT_p_symm_RHS_sum_shifted_tile_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ))) := by
  rw [petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  exact peterssonInner_heckeT_p_symm_RHS_per_q_distribute_shifted_tile_residual
    p hp hpN (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_f_heckeT_p_RHS_sum_shifted_tiles
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          ⇑g +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            ⇑g) := by
  rw [petN_f_heckeT_p_RHS_sum_normalized p hp hpN f g]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  exact peterssonInner_heckeT_p_RHS_per_q_normalized_shifted_tile p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma petN_symm_residual_sum_eq_standard_shifted_tiles
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
            GL (Fin 2) ℝ)) +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            ((⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
                GL (Fin 2) ℝ)) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
              GL (Fin 2) ℝ)))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ)) *
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)⁻¹)⁻¹ :
                GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
          ⇑g +
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((q.out : SL(2, ℤ)) *
                    (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹)⁻¹ :
                  GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            (⇑f ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
            ⇑g) := by
  rw [← petN_diamond_heckeT_p_symm_RHS_sum_shifted_tile_residual p hp hpN f g,
      ← petN_f_heckeT_p_RHS_sum_shifted_tiles p hp hpN f g]
  have h := petN_f_heckeT_p_adjointGamma0Rep_reindex p hp hpN
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) g
  rw [show (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f by
    show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f) = f
    rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f) =
        ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹).comp
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN))) f from rfl,
      ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one]
    rfl] at h
  exact h

private lemma petN_diamond_heckeT_p_eq_canonical_RHS
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
      petN f (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) := by
  rw [petN_diamond_heckeT_p_symm_RHS_sum_shifted_tile_residual p hp hpN f g,
      petN_symm_residual_sum_eq_standard_shifted_tiles p hp hpN f g,
      ← petN_f_heckeT_p_RHS_sum_shifted_tiles p hp hpN f g]

private lemma heckeT_p_cusp_comm_diamondOp_private
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (d : (ZMod N)ˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_p_cusp k p hp hpN (diamondOp_cusp k d g) =
      diamondOp_cusp k d (heckeT_p_cusp k p hp hpN g) := by
  apply CuspForm.ext; intro τ
  show ((heckeT_p k p hp hpN) (diamondOp k d g.toModularForm')).toFun τ =
    ((diamondOp k d) (heckeT_p k p hp hpN g.toModularForm')).toFun τ
  have h := LinearMap.congr_fun
    (heckeT_p_comm_diamondOp (N := N) k p hp hpN d) g.toModularForm'
  simp only [LinearMap.comp_apply] at h
  exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ)
    h.symm

open UpperHalfPlane ModularGroup MeasureTheory in
lemma petN_T_p_heckeT_p_LHS_sum_distributed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹)) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) = _
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_SL_inv_eq_mapGL_inv]
  exact peterssonInner_heckeT_p_LHS_per_q_distribute p hp hpN
    (q.out : SL(2, ℤ)) f g

open UpperHalfPlane ModularGroup MeasureTheory in
lemma petN_T_p_heckeT_p_LHS_sum_diamond_distributed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k]
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k]
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  rw [petN_heckeT_p_adjointGamma0Rep_reindex p hp hpN f g]
  rw [petN_T_p_heckeT_p_LHS_sum_distributed p hp hpN
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h_diamond_g : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
      UpperHalfPlane → ℂ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) := by
    show ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) = _
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  congr 1
  ·
    rw [slash_diamond_inv_M_infty_eq_T_p_lower_epsilon p hp hpN
      (q.out : SL(2, ℤ)) f]
    rw [show (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) =
      ⇑g ∣[k]
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) by
      rw [h_diamond_g, ← SlashAction.slash_mul]]
  ·
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b
      (q.out : SL(2, ℤ)) f]
    rw [show (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹)) =
      ⇑g ∣[k]
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) by
      rw [h_diamond_g, ← SlashAction.slash_mul]]

lemma petN_diamond_heckeT_p_eq_unsymm_RHS
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  rw [petN_diamond_heckeT_p_eq_canonical_RHS p hp hpN f g,
      heckeT_p_cusp_comm_diamondOp_private p hp hpN
        (ZMod.unitOfCoprime p hpN)⁻¹ g]

end HeckeRing.GL2
