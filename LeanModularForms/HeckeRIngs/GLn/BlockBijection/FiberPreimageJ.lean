/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.StabFiberIBlock

/-!
# Block Embedding Bijection: j-side preimage construction (`fiber_block_form_preimage`)
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

private lemma slSuccEmbed_H_mk_coe_eq {k : ℕ}
    (σ : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    (slSuccEmbed_H ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩ : GL (Fin (k + 2)) ℚ) =
      mapGL ℚ (slSuccEmbed σ) := by
  show mapGL ℚ (slSuccEmbed (toSL ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩)) = _
  rw [show toSL ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩ = σ from
    SpecialLinearGroup.mapGL_injective (S := ℚ) (by rw [toSL_spec])]

private lemma decompQuot_slSuccEmbed_eq_of_inv_block_stab {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (σ_H : (GL_pair (k + 1)).H)
    (g : (GL_pair (k + 2)).H) (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_GL_val : (((slSuccEmbed_H σ_H)⁻¹ * g : (GL_pair (k + 2)).H) :
        GL (Fin (k + 2)) ℚ) = (mapGL ℚ M)⁻¹)
    (h_M_stab : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H) :
    (⟦slSuccEmbed_H σ_H⟧ :
        decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a))) =
      ⟦g⟧ := by
  apply Quotient.sound
  change QuotientGroup.leftRel _ (slSuccEmbed_H σ_H) g
  rw [QuotientGroup.leftRel_apply, mem_diagMat_cons_stabilizer_subgroupOf_iff a ha,
    h_GL_val, show (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 a) =
      ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ * (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a))⁻¹ from by group]
  exact inv_mem h_M_stab

private lemma decompQuot_slSuccEmbed_diagMat_mk_eq_of_block {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (g : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block : toSL g.out * M = slSuccEmbed σ)
    (h_stab : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H) :
    decompQuot_slSuccEmbed_diagMat a ha
      (⟦(⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩ : (GL_pair (k + 1)).H)⟧ :
        decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) = g := by
  rw [show g = ⟦g.out⟧ from (Quotient.out_eq g).symm]
  change ⟦slSuccEmbed_H ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩⟧ = (⟦g.out⟧ : decompQuot _ _)
  refine decompQuot_slSuccEmbed_eq_of_inv_block_stab a ha
    ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩ g.out M ?_ h_stab
  push_cast
  rw [slSuccEmbed_H_mk_coe_eq, ← h_block, map_mul, toSL_spec]
  group

private lemma exists_j_m_X_block_class_eq_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M_i N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) := by
  obtain ⟨M_i, N_i, M_X, τ_X, h_stab_i, h_int_conj, h_X_block, h_M_X_stab⟩ :=
    exists_stab_with_block_form_of_X_fiber a b c ha hb hc hda hdb i j hfib
  set τ_X_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩
  set N_i_inv_H : (GL_pair (k + 2)).H :=
    ⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩
  set j_corrected : (GL_pair (k + 2)).H := N_i_inv_H * j.out
  refine ⟨M_i, N_i, ⟦τ_X_H⟧, h_stab_i, h_int_conj, ?_⟩
  change (⟦slSuccEmbed_H τ_X_H⟧ :
    decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
    (⟦j_corrected⟧ : decompQuot _ _)
  refine decompQuot_slSuccEmbed_eq_of_inv_block_stab b hb τ_X_H j_corrected M_X ?_
    h_M_X_stab
  push_cast
  rw [slSuccEmbed_H_mk_coe_eq, ← h_X_block, map_mul, map_mul, toSL_spec]
  show (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X)⁻¹ *
    (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ)) = _
  group

private lemma eq_slSuccEmbed_of_first_row_col_e0 {k : ℕ}
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col : ∀ r : Fin (k + 2),
      N.val r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0)
    (h_row : ∀ l : Fin (k + 1), N.val 0 l.succ = 0) :
    ∃ τ : SpecialLinearGroup (Fin (k + 1)) ℤ, N = slSuccEmbed τ := by
  have hN_00 : N.val 0 0 = 1 := by
    simpa [Matrix.one_apply_eq] using h_col 0
  have hN_succ0 : ∀ I : Fin (k + 1), N.val I.succ 0 = 0 := fun I ↦ by
    simpa [Matrix.one_apply_ne (Fin.succ_ne_zero I)] using h_col I.succ
  set τ_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N.val I.succ J.succ
  have h_det : τ_raw.det = 1 := by
    have h_det_N : N.val.det = 1 := N.2
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Finset.sum_eq_zero (fun j _ ↦ by rw [h_row j]; ring), add_zero, hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    rw [show N.val.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = τ_raw from by
      ext I J; show N.val I.succ ((0 : Fin (k + 2)).succAbove J) = τ_raw I J
      rw [Fin.succAbove_zero]] at h_det_N
    exact h_det_N
  refine ⟨⟨τ_raw, h_det⟩, ?_⟩
  apply Subtype.ext
  ext I J
  show N.val I J = (slSuccEmbed ⟨τ_raw, h_det⟩).val I J
  refine Fin.cases ?_ ?_ I
  · refine Fin.cases ?_ ?_ J
    · rw [hN_00, slSuccEmbed_val_zero_zero]
    · intro J'; rw [h_row J', slSuccEmbed_val_zero_succ]
  · intro I'
    refine Fin.cases ?_ ?_ J
    · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
    · intro J'; rw [slSuccEmbed_val_succ_succ]

private lemma sl_block_form_clearing_first_col_of_col_div {k : ℕ}
    (b : Fin (k + 1) → ℕ) (hb : ∀ i, 0 < b i) (hdb : DivChain (k + 1) b)
    (X : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_div : ∀ r : Fin (k + 1),
      (b r : ℤ) ∣ (X⁻¹ : SpecialLinearGroup _ ℤ).val r.succ 0) :
    ∃ (M_X : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ),
      X * M_X = slSuccEmbed τ_X ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨M_0_X, hM_0_X_col, hM_0_X_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      (sl_first_col_primitive X⁻¹) h_div
  have h_col_e0 : ∀ r : Fin (k + 2),
      (X * M_0_X).val r 0 =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    have h_to_inv :
        (X * M_0_X).val r 0 = (X * X⁻¹ : SpecialLinearGroup _ ℤ).val r 0 := by
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      refine Finset.sum_congr rfl (fun p _ ↦ ?_)
      rw [hM_0_X_col p]
    rw [h_to_inv, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 b hb (X * M_0_X) h_col_e0 Finset.univ
  set M_X : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0_X * T_clear with hM_X_def
  have hM_X_assoc : X * M_X = (X * M_0_X) * T_clear := (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      (X * M_X).val r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    rw [hM_X_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), (X * M_X).val 0 l.succ = 0 := by
    intro l
    rw [hM_X_assoc]
    exact hT_S l (Finset.mem_univ l)
  obtain ⟨τ_X, h_block⟩ := eq_slSuccEmbed_of_first_row_col_e0 (X * M_X) hN_col0 hN_row0
  refine ⟨M_X, τ_X, h_block, ?_⟩
  have h_split : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) =
      ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_0_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b)) *
      ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ T_clear : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b)) := by
    rw [hM_X_def, map_mul]; group
  rw [h_split]
  exact mul_mem hM_0_X_stab hT_stab

private lemma diagMat_cons_mapGL_conj_of_int_conj {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (M_i N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) :
    diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
  have hcons_pos : ∀ q, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) q := cons_one_pos ha
  have h := congr_arg
    (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦ M.map (algebraMap ℤ ℚ)) h_int_conj
  simp only [Matrix.map_mul] at h
  apply Units.ext
  simp only [Units.val_mul, mapGL_coe_matrix, diagMat_val (k + 2) _ hcons_pos]
  rw [show (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) =
      Matrix.diagonal
        (fun r : Fin (k + 2) ↦ (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℚ)) from by
    rw [Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1] at h
  convert h using 1

private lemma slSuccEmbed_block_witnesses_lifted_mem_H {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (M_i N_i M_X : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (h_X_block : N_i⁻¹ * toSL j.out * M_X = slSuccEmbed τ_X)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (h_M_X_stab : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H)
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        (slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) *
        (slSuccEmbed_H ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  have h_slSucc_σ_GL :
      (slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ : GL (Fin (k + 2)) ℚ) =
      (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
    rw [slSuccEmbed_H_mk_coe_eq, ← h_block_i, map_mul, toSL_spec]
  have h_slSucc_τ_GL :
      (slSuccEmbed_H ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
    rw [slSuccEmbed_H_mk_coe_eq, ← h_X_block, map_mul, map_mul, toSL_spec]
  have h_cancel :
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
        (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) := by
    rw [show (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) = (mapGL ℚ N_i)⁻¹ from by rw [← map_inv],
      ← diagMat_cons_mapGL_conj_of_int_conj a ha M_i N_i h_int_conj]
    group
  have h_main :
      (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        (slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) *
        (slSuccEmbed_H ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) =
      ((diagMat (k + 2) (Fin.cons 1 c))⁻¹ * (i.out : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) * (j.out : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b)) *
      ((diagMat (k + 2) (Fin.cons 1 b))⁻¹ * (mapGL ℚ M_X) *
        diagMat (k + 2) (Fin.cons 1 b)) := by
    rw [h_slSucc_σ_GL, h_slSucc_τ_GL,
      show (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
          ((i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i) *
          diagMat (k + 2) (Fin.cons 1 a) *
          ((mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X) *
          diagMat (k + 2) (Fin.cons 1 b) =
        (diagMat (k + 2) (Fin.cons 1 c))⁻¹ * (i.out : GL (Fin (k + 2)) ℚ) *
          ((mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
            (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ)) *
          (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X *
          diagMat (k + 2) (Fin.cons 1 b) from by group, h_cancel]
    group
  rw [h_main]
  exact mul_mem (hfib_to_mem_H a b c ha hb hc i j hfib) h_M_X_stab

private lemma fiber_block_form_preimage_corrected_j_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i_H τ_X_H : (GL_pair (k + 1)).H),
      decompQuot_slSuccEmbed_diagMat a ha
        (⟦σ_i_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) = i ∧
      decompQuot_slSuccEmbed_diagMat b hb
        (⟦τ_X_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)) =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      (diagMat (k + 1) c)⁻¹ * (σ_i_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) a *
        (τ_X_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) b ∈ (GL_pair (k + 1)).H := by
  obtain ⟨_ν, _, _, h_div⟩ :=
    hfib_col_div_b_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  set X : SpecialLinearGroup (Fin (k + 2)) ℤ := N_i⁻¹ * toSL j.out with hX_def
  obtain ⟨M_X, τ_X, h_X_block, h_M_X_stab⟩ :=
    sl_block_form_clearing_first_col_of_col_div b hb hdb X h_div
  have h_X_block' : N_i⁻¹ * toSL j.out * M_X = slSuccEmbed τ_X := hX_def ▸ h_X_block
  refine ⟨⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩,
    ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩, ?_, ?_, ?_⟩
  · rw [show i = ⟦i.out⟧ from (Quotient.out_eq i).symm]
    refine decompQuot_slSuccEmbed_eq_of_inv_block_stab a ha
      ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ i.out M_i ?_ h_stab_i
    push_cast
    rw [slSuccEmbed_H_mk_coe_eq, ← h_block_i, map_mul, toSL_spec]
    group
  · refine decompQuot_slSuccEmbed_eq_of_inv_block_stab b hb
      ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩
      (⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ * j.out) M_X ?_ h_M_X_stab
    push_cast
    rw [slSuccEmbed_H_mk_coe_eq, ← h_X_block', map_mul, map_mul, toSL_spec]
    show (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X)⁻¹ *
      (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ)) = _
    group
  · exact slSuccEmbed_H_fiber_transfer_converse a b c ha hb hc _ _
      (slSuccEmbed_block_witnesses_lifted_mem_H a b c ha hb hc i j M_i N_i M_X σ_i τ_X
        h_block_i h_X_block' h_int_conj h_M_X_stab hfib)

/-- Corrected-representative fiber descent (j-side via X): combines the i-side and
X-side block witnesses with the integer conjugation identity `M_i · D_a = D_a · N_i`
to produce dim-`(k+1)` data `(i_m, j_m, σ_i_H, τ_X_H)`, the canonical i-side class
equality, the `N_i⁻¹`-corrected j-side class equality, and the dim-`(k+1)` fiber
set-form for the explicit representatives `(σ_i_H, τ_X_H)`. -/
lemma fiber_block_form_preimage_corrected_j {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (M_i N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (σ_i_H τ_X_H : (GL_pair (k + 1)).H),
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      decompQuot_slSuccEmbed_diagMat a ha
        (⟦σ_i_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) = i ∧
      decompQuot_slSuccEmbed_diagMat b hb
        (⟦τ_X_H⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)) =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      (diagMat (k + 1) c)⁻¹ * (σ_i_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) a *
        (τ_X_H : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) b ∈ (GL_pair (k + 1)).H := by
  obtain ⟨σ_i, M_i, N_i, _, h_block_i, h_stab_i, h_int_conj, _, _, _⟩ :=
    hfib_col_div_b_via_i_block a b c ha hb hc hda i j hfib
  obtain ⟨σ_i_H, τ_X_H, h_i_class, h_j_class, h_dim1_fib⟩ :=
    fiber_block_form_preimage_corrected_j_explicit a b c ha hb hc hdb i M_i σ_i
      h_block_i h_stab_i N_i h_int_conj j hfib
  exact ⟨M_i, N_i, σ_i_H, τ_X_H, h_stab_i, h_int_conj, h_i_class, h_j_class,
    h_dim1_fib⟩

private lemma mem_doubleCoset_of_setForm {n : ℕ} [NeZero n]
    (g₁ g₂ d : (GL_pair n).Δ) (σ τ : (GL_pair n).H)
    (h_set : ({(σ : GL (Fin n) ℚ) * (g₁ : GL (Fin n) ℚ)} : Set _) *
        {(τ : GL (Fin n) ℚ) * (g₂ : GL (Fin n) ℚ)} *
        ((GL_pair n).H : Set (GL (Fin n) ℚ)) =
        {(d : GL (Fin n) ℚ)} * ((GL_pair n).H : Set (GL (Fin n) ℚ))) :
    (σ : GL (Fin n) ℚ) * g₁ * ((τ : GL (Fin n) ℚ) * g₂) ∈
      DoubleCoset.doubleCoset ((d : GL (Fin n) ℚ)) (GL_pair n).H (GL_pair n).H := by
  rw [Set.singleton_mul_singleton] at h_set
  have h_in : (σ : GL (Fin n) ℚ) * g₁ * ((τ : GL (Fin n) ℚ) * g₂) ∈
      ({(d : GL (Fin n) ℚ)} : Set _) * ((GL_pair n).H : Set (GL (Fin n) ℚ)) := by
    rw [← h_set]
    exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by simp⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_in
  rw [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨1, (GL_pair n).H.one_mem, h, hh, by simpa only [one_mul] using hprod.symm⟩

private lemma exists_stab_shift_of_decompQuot_out {n : ℕ} [NeZero n]
    (g : (GL_pair n).Δ) (σ : (GL_pair n).H) :
    ∃ s : (GL_pair n).H,
      ((⟦σ⟧ : decompQuot (GL_pair n) g).out : GL (Fin n) ℚ) =
        (σ : GL (Fin n) ℚ) * (s : GL (Fin n) ℚ) ∧
      (g : GL (Fin n) ℚ)⁻¹ * (s : GL (Fin n) ℚ) * g ∈ (GL_pair n).H := by
  obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (g : GL (Fin n) ℚ) • (GL_pair n).H).subgroupOf
      (GL_pair n).H) σ
  refine ⟨s, ?_, ?_⟩
  · have := congr_arg (Subtype.val : (GL_pair n).H → GL (Fin n) ℚ) hs
    simpa [Subgroup.coe_mul]
  · have := s.2
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at this
    simpa [ConjAct.ofConjAct_toConjAct]

private lemma mulMap_eq_of_setForm_specific_reps {n : ℕ} [NeZero n]
    (g₁ g₂ d : (GL_pair n).Δ) (σ τ : (GL_pair n).H)
    (h_set : ({(σ : GL (Fin n) ℚ) * (g₁ : GL (Fin n) ℚ)} : Set _) *
        {(τ : GL (Fin n) ℚ) * (g₂ : GL (Fin n) ℚ)} *
        ((GL_pair n).H : Set (GL (Fin n) ℚ)) =
        {(d : GL (Fin n) ℚ)} *
          ((GL_pair n).H : Set (GL (Fin n) ℚ))) :
    HeckeRing.mulMap (GL_pair n) g₁ g₂ ⟨⟦σ⟧, ⟦τ⟧⟩ =
      (⟦d⟧ : HeckeRing.HeckeCoset (GL_pair n)) := by
  have h_prod_mem := mem_doubleCoset_of_setForm g₁ g₂ d σ τ h_set
  unfold HeckeRing.mulMap
  rw [HeckeRing.HeckeCoset.eq_iff]
  dsimp only
  apply HeckeRing.HeckeCoset.doubleCoset_eq_of_mem
  obtain ⟨n_a, hi_out, hn_a_conj⟩ := exists_stab_shift_of_decompQuot_out g₁ σ
  obtain ⟨n_b, hj_out, hn_b_conj⟩ := exists_stab_shift_of_decompQuot_out g₂ τ
  rw [hi_out, hj_out]
  rw [DoubleCoset.mem_doubleCoset] at h_prod_mem
  obtain ⟨a', ha', b', hb', habp⟩ := h_prod_mem
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨(σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
      (σ : GL (Fin n) ℚ)⁻¹ * a',
    (GL_pair n).H.mul_mem
      ((GL_pair n).H.mul_mem
        ((GL_pair n).H.mul_mem σ.2 n_a.2)
        ((GL_pair n).H.inv_mem σ.2))
      ha',
    b' * ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂),
    (GL_pair n).H.mul_mem hb' hn_b_conj, ?_⟩
  have h_eq : ((σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
        (σ : GL (Fin n) ℚ)⁻¹ * a') * (d : GL (Fin n) ℚ) *
        (b' * ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂)) =
      (σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) * g₁ *
        ((τ : GL (Fin n) ℚ) * (n_b : GL (Fin n) ℚ) * g₂) := by
    have h1 : ((σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
          (σ : GL (Fin n) ℚ)⁻¹ * a') * (d : GL (Fin n) ℚ) *
          (b' * ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂)) =
        ((σ : GL (Fin n) ℚ) * (n_a : GL (Fin n) ℚ) *
          (σ : GL (Fin n) ℚ)⁻¹) *
          ((a' : GL (Fin n) ℚ) * d * b') *
          ((g₂ : GL (Fin n) ℚ)⁻¹ * (n_b : GL (Fin n) ℚ) * g₂) := by group
    rw [h1, ← habp]
    group
  exact h_eq.symm

/-- Corrected-j mulMap-form descent with explicit i-side block witnesses
`(M_i, σ_i, N_i, h_block_i, h_stab_i, h_int_conj)`: returns the dim-`(k+1)` class
pair `(i_m, j_m)`, the canonical i-side class equality, the `N_i⁻¹`-corrected j-side
class equality, and the rep-invariant evaluation `mulMap ⟨i_m, j_m⟩ = ⟦D_c⟧`. -/
lemma fiber_block_form_preimage_corrected_j_mulMap_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_int_conj :
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      HeckeRing.mulMap (GL_pair (k + 1))
          (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
        (⟦diagMat_delta (k + 1) c⟧ :
          HeckeRing.HeckeCoset (GL_pair (k + 1))) := by
  obtain ⟨σ_i_H, τ_X_H, h_class_i, h_class_j, h_fiber⟩ :=
    fiber_block_form_preimage_corrected_j_explicit a b c ha hb hc hdb i M_i σ_i
      h_block_i h_stab_i N_i h_int_conj j hfib
  refine ⟨⟦σ_i_H⟧, ⟦τ_X_H⟧, h_class_i, h_class_j, ?_⟩
  haveI : NeZero (k + 1) := ⟨Nat.succ_ne_zero k⟩
  exact mulMap_eq_of_setForm_specific_reps
    (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
    (diagMat_delta (k + 1) c) σ_i_H τ_X_H
    (by simp only [diagMat_delta_val (k + 1) a ha, diagMat_delta_val (k + 1) b hb,
          diagMat_delta_val (k + 1) c hc]
        exact (fiber_diagMat_iff_mem_H a b c ha hb hc σ_i_H τ_X_H).mpr h_fiber)

/-- See `fiber_block_form_preimage_corrected_j_mulMap_explicit` for the active
explicit-input mulMap descent; this is now a thin wrapper that extracts the
i-side block witnesses via `exists_stab_with_block_form_of_fiber` and
`exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
lemma fiber_block_form_preimage_corrected_j_mulMap {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
      HeckeRing.mulMap (GL_pair (k + 1))
          (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
        (⟦diagMat_delta (k + 1) c⟧ :
          HeckeRing.HeckeCoset (GL_pair (k + 1))) := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨i_m, j_m, h_class_i, h_class_j, h_mulMap⟩ :=
    fiber_block_form_preimage_corrected_j_mulMap_explicit a b c ha hb hc hdb i
      M_i σ_i h_block_i h_stab_i N_i h_int_conj j hfib
  exact ⟨N_i, i_m, j_m, h_class_i, h_class_j, h_mulMap⟩

/-- GL-level reduction for the witness-specific `j.out`-conjugated `b`-stabilizer:
from the fiber equation `i.out · D_a · j.out · D_b = D_c · mapGL ν`, the
integer-conjugate identity `D_a · mapGL N_i = mapGL M_i · D_a`, and the
`c`-stabilizer condition `D_c⁻¹ · (i.out · mapGL M_i · i.out⁻¹) · D_c ∈ H`, deduce
`D_b⁻¹ · (j.out⁻¹ · mapGL N_i · j.out) · D_b ∈ H`. -/
lemma jout_conj_N_i_stab_of_iMi_c_stab {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_fib_GL :
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
        (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) =
      diagMat (k + 2) (Fin.cons 1 c) * (mapGL ℚ ν : GL (Fin (k + 2)) ℚ))
    (h_int_conj_GL :
      diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a))
    (h_iMi_c_stab :
      (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        ((i.out : GL (Fin (k + 2)) ℚ) * (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
          (i.out : GL (Fin (k + 2)) ℚ)⁻¹) *
        diagMat (k + 2) (Fin.cons 1 c) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
          (j.out : GL (Fin (k + 2)) ℚ)) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  let _ := ha; let _ := hb; let _ := hc
  set i_g : GL (Fin (k + 2)) ℚ := (i.out : GL (Fin (k + 2)) ℚ)
  set j_g : GL (Fin (k + 2)) ℚ := (j.out : GL (Fin (k + 2)) ℚ)
  set D_a : GL (Fin (k + 2)) ℚ := diagMat (k + 2) (Fin.cons 1 a)
  set D_b : GL (Fin (k + 2)) ℚ := diagMat (k + 2) (Fin.cons 1 b)
  set D_c : GL (Fin (k + 2)) ℚ := diagMat (k + 2) (Fin.cons 1 c)
  set N_g : GL (Fin (k + 2)) ℚ := (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ)
  set M_g : GL (Fin (k + 2)) ℚ := (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ)
  set ν_g : GL (Fin (k + 2)) ℚ := (mapGL ℚ ν : GL (Fin (k + 2)) ℚ)
  have h_fwd : j_g * D_b = D_a⁻¹ * i_g⁻¹ * D_c * ν_g := by
    have hcong :
        (D_a⁻¹ * i_g⁻¹) * (i_g * D_a * j_g * D_b) =
          (D_a⁻¹ * i_g⁻¹) * (D_c * ν_g) := by
      rw [h_fib_GL]
    calc j_g * D_b
        = (D_a⁻¹ * i_g⁻¹) * (i_g * D_a * j_g * D_b) := by group
      _ = (D_a⁻¹ * i_g⁻¹) * (D_c * ν_g) := hcong
      _ = D_a⁻¹ * i_g⁻¹ * D_c * ν_g := by group
  have h_inv : D_b⁻¹ * j_g⁻¹ = ν_g⁻¹ * D_c⁻¹ * i_g * D_a := by
    have hinv_eq : (j_g * D_b)⁻¹ = (D_a⁻¹ * i_g⁻¹ * D_c * ν_g)⁻¹ :=
      congr_arg (·⁻¹) h_fwd
    rw [show (j_g * D_b)⁻¹ = D_b⁻¹ * j_g⁻¹ by group,
        show (D_a⁻¹ * i_g⁻¹ * D_c * ν_g)⁻¹ = ν_g⁻¹ * D_c⁻¹ * i_g * D_a from
          by group] at hinv_eq
    exact hinv_eq
  have h_int : D_a * N_g * D_a⁻¹ = M_g := by
    calc D_a * N_g * D_a⁻¹
        = (M_g * D_a) * D_a⁻¹ := by rw [h_int_conj_GL]
      _ = M_g := by group
  have h_goal_eq :
      D_b⁻¹ * (j_g⁻¹ * N_g * j_g) * D_b =
        ν_g⁻¹ * (D_c⁻¹ * (i_g * M_g * i_g⁻¹) * D_c) * ν_g := by
    calc D_b⁻¹ * (j_g⁻¹ * N_g * j_g) * D_b
        = (D_b⁻¹ * j_g⁻¹) * N_g * (j_g * D_b) := by group
      _ = (ν_g⁻¹ * D_c⁻¹ * i_g * D_a) * N_g *
            (D_a⁻¹ * i_g⁻¹ * D_c * ν_g) := by rw [h_inv, h_fwd]
      _ = ν_g⁻¹ * D_c⁻¹ * i_g * (D_a * N_g * D_a⁻¹) * i_g⁻¹ * D_c * ν_g := by
            group
      _ = ν_g⁻¹ * D_c⁻¹ * i_g * M_g * i_g⁻¹ * D_c * ν_g := by rw [h_int]
      _ = ν_g⁻¹ * (D_c⁻¹ * (i_g * M_g * i_g⁻¹) * D_c) * ν_g := by group
  rw [h_goal_eq]
  have h_ν_in_H : ν_g ∈ (GL_pair (k + 2)).H := coe_mem_SLnZ (k + 2) ν
  exact (GL_pair (k + 2)).H.mul_mem
    ((GL_pair (k + 2)).H.mul_mem ((GL_pair (k + 2)).H.inv_mem h_ν_in_H) h_iMi_c_stab)
    h_ν_in_H

private lemma jout_conj_N_i_stab_for_X_fiber_of_iMi_c_stab {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _))
    (h_iMi_c_stab :
      ∀ M_i : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
          ((i.out : GL (Fin (k + 2)) ℚ) *
            (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
            (i.out : GL (Fin (k + 2)) ℚ)⁻¹) *
          diagMat (k + 2) (Fin.cons 1 c) ∈ (GL_pair (k + 2)).H) :
    ∃ N_i : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
          (j.out : GL (Fin (k + 2)) ℚ)) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨M_i, N_i, _M_X, _τ_X, _h_M_i_stab, h_int_conj, _h_block, _h_M_X_stab⟩ :=
    exists_stab_with_block_form_of_X_fiber a b c ha hb hc hda hdb i j hfib
  refine ⟨N_i, ?_⟩
  obtain ⟨ν, h_fib_GL⟩ := hfib_GL_eq a b c ha hb hc i j hfib
  have h_int_conj_GL := h_int_conj_GL_of_int_mat a ha M_i N_i h_int_conj
  exact jout_conj_N_i_stab_of_iMi_c_stab a b c ha hb hc i j M_i N_i ν
    h_fib_GL h_int_conj_GL (h_iMi_c_stab M_i)

private lemma fiber_block_form_preimage_canonical_j_witness_specific {k : ℕ}
    (a b : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b))
    (h_j_m_corrected :
      decompQuot_slSuccEmbed_diagMat b hb j_m =
        (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out⟧ :
          decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))))
    (h_jout_conj_N_i_stab :
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
          (j.out : GL (Fin (k + 2)) ℚ)) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    decompQuot_slSuccEmbed_diagMat b hb j_m = j := by
  let _ := a; let _ := ha
  rw [h_j_m_corrected]
  conv_rhs => rw [show j = ⟦j.out⟧ from (Quotient.out_eq j).symm]
  apply Quotient.sound
  change QuotientGroup.leftRel _
    ((⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) * j.out)
    j.out
  rw [QuotientGroup.leftRel_apply, mem_diagMat_cons_stabilizer_subgroupOf_iff b hb]
  have h_GL_val :
      (((⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
            j.out)⁻¹ * j.out : (GL_pair (k + 2)).H) =
        ⟨(j.out : GL (Fin (k + 2)) ℚ)⁻¹ * (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
            (j.out : GL (Fin (k + 2)) ℚ),
          (GL_pair (k + 2)).H.mul_mem
            ((GL_pair (k + 2)).H.mul_mem
              ((GL_pair (k + 2)).H.inv_mem j.out.2)
              (coe_mem_SLnZ (k + 2) N_i))
            j.out.2⟩ := by
    apply Subtype.ext
    show (((⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
        j.out)⁻¹ * j.out : (GL_pair (k + 2)).H).val =
        (j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) * (j.out : GL (Fin (k + 2)) ℚ)
    push_cast
    rw [show (mapGL ℚ N_i⁻¹ : GL (Fin (k + 2)) ℚ) =
          (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ)⁻¹ from
        map_inv (mapGL ℚ : SpecialLinearGroup (Fin (k + 2)) ℤ →* _) N_i]
    group
  rw [h_GL_val]
  exact h_jout_conj_N_i_stab

private lemma fiber_block_form_preimage_canonical_j_from_existential_witness {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a) (_ : DivChain (k + 1) b)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _))
    (h_witness_jout_conj_stab :
      ∃ (N_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
        (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
        (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
        decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
        decompQuot_slSuccEmbed_diagMat b hb j_m =
          (⟦(⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ : (GL_pair (k + 2)).H) *
              j.out⟧ :
            decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) ∧
        HeckeRing.mulMap (GL_pair (k + 1))
            (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
          (⟦diagMat_delta (k + 1) c⟧ :
            HeckeRing.HeckeCoset (GL_pair (k + 1))) ∧
        (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
          ((j.out : GL (Fin (k + 2)) ℚ)⁻¹ *
            (mapGL ℚ N_i : GL (Fin (k + 2)) ℚ) *
            (j.out : GL (Fin (k + 2)) ℚ)) *
          diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      HeckeRing.mulMap (GL_pair (k + 1))
          (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b) ⟨i_m, j_m⟩ =
        (⟦diagMat_delta (k + 1) c⟧ :
          HeckeRing.HeckeCoset (GL_pair (k + 1))) := by
  let _ := hfib; let _ := hc; let _ := hda
  obtain ⟨N_i, i_m, j_m, h_i_m_canon, h_j_m_corrected, h_mulMap, h_stab⟩ :=
    h_witness_jout_conj_stab
  exact ⟨i_m, j_m, h_i_m_canon,
    fiber_block_form_preimage_canonical_j_witness_specific a b ha hb j N_i j_m
      h_j_m_corrected h_stab,
    h_mulMap⟩

/-- i-side class-preimage bridge: from `exists_stab_with_block_form_of_fiber`
(which produces `M ∈ stab` and `σ_m ∈ SL_(k+1)(ℤ)` with
`toSL i.out * M = slSuccEmbed σ_m`), construct the dim-`(k+1)` quotient class
`i_m := ⟦σ_m_H⟧` and prove `decompQuot_slSuccEmbed_diagMat a ha i_m = i`. -/
lemma exists_i_m_block_class_eq_of_fiber {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i := by
  obtain ⟨M, σ_m, h_eq, h_M_stab⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  exact ⟨⟦⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩⟧,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block a ha i M σ_m h_eq h_M_stab⟩

private lemma fiber_class_preimages_from_joint_block_witnesses {k : ℕ}
    (a b : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_m)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_j : toSL j.out * M_j = slSuccEmbed τ_m)
    (h_stab_j : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j :=
  ⟨⟦⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩⟧, ⟦⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩⟧,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block a ha i M_i σ_m h_block_i h_stab_i,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block b hb j M_j τ_m h_block_j h_stab_j⟩

/-- Existential-representative form of `fiber_has_block_form_preimages`: given the
joint i-side and j-side block witnesses and the dim-`(k+1)` integer matrix equation
`h_joint`, produces `(i_m, j_m)` together with explicit representatives
`(rep_i, rep_j)` in those classes satisfying the lifted dim-`(k+2)` `mem_H` condition
for those specific representatives. -/
lemma fiber_has_block_form_preimages_existential_reps {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_m)
    (h_stab_i : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H)
    (M_j : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (τ_m : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_j : toSL j.out * M_j = slSuccEmbed τ_m)
    (h_stab_j : (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
      (mapGL ℚ M_j : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H)
    (h_joint : (diagMat (k + 1) c)⁻¹ *
      ((⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩ : (GL_pair (k + 1)).H) :
        GL (Fin (k + 1)) ℚ) *
      diagMat (k + 1) a *
      ((⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩ : (GL_pair (k + 1)).H) :
        GL (Fin (k + 1)) ℚ) *
      diagMat (k + 1) b ∈ (GL_pair (k + 1)).H) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b))
      (rep_i : (GL_pair (k + 1)).H) (rep_j : (GL_pair (k + 1)).H),
      (⟦rep_i⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a)) = i_m ∧
      (⟦rep_j⟧ : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)) = j_m ∧
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        (slSuccEmbed_H rep_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) *
        (slSuccEmbed_H rep_j : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  set σ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩
  set τ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩
  refine ⟨⟦σ_m_H⟧, ⟦τ_m_H⟧, σ_m_H, τ_m_H, rfl, rfl,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block a ha i M_i σ_m h_block_i h_stab_i,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block b hb j M_j τ_m h_block_j h_stab_j, ?_⟩
  exact slSuccEmbed_H_fiber_transfer a b c ha hb hc σ_m_H τ_m_H h_joint

/-- Combinatorial core of Shimura L.3.19: every fiber pair at dim `k+2` with
`Fin.cons 1 _` diagonals has dim-`k+1` class preimages under the
`decompQuot_slSuccEmbed_diagMat` block embedding, with the lifted `mem_H` condition
at dim `k+2` holding for `slSuccEmbed_H i_m.out` and `slSuccEmbed_H j_m.out`.
The hypothesis `hk : 1 ≤ k` is required: at `k = 0` the conclusion is false, with
counterexample `A_i = [[1, 0], [2, 1]]`, `A_j = [[1, 0], [1, 1]]`, `a = b = (2)`,
`c = (4)` (the downstream `heckeMultiplicity_block_embed` imposes `2 ≤ m`). -/
lemma fiber_has_block_form_preimages {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
        (slSuccEmbed_H i_m.out : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) *
        (slSuccEmbed_H j_m.out : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  sorry

/-- Set-form version of the fiber block-preimage statement, derived from
`fiber_has_block_form_preimages` via `slSuccEmbed_H_fiber_transfer_converse` and
`fiber_diagMat_iff_mem_H`. Inherits the `hk : 1 ≤ k` restriction. -/
lemma fiber_block_form_preimage {k : ℕ} (hk : 1 ≤ k)
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (hda : DivChain (k + 1) a) (hdb : DivChain (k + 1) b) (hdc : DivChain (k + 1) c)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (i_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a))
      (j_m : decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) b)),
      decompQuot_slSuccEmbed_diagMat a ha i_m = i ∧
      decompQuot_slSuccEmbed_diagMat b hb j_m = j ∧
      ({(i_m.out : GL (Fin (k + 1)) ℚ) *
          (diagMat_delta (k + 1) a : GL (Fin (k + 1)) ℚ)} : Set _) *
        {(j_m.out : GL (Fin (k + 1)) ℚ) *
          (diagMat_delta (k + 1) b : GL (Fin (k + 1)) ℚ)} *
        ((GL_pair (k + 1)).H : Set _) =
      {(diagMat_delta (k + 1) c : GL (Fin (k + 1)) ℚ)} *
        ((GL_pair (k + 1)).H : Set _) := by
  obtain ⟨i_m, j_m, h1, h2, h_lifted⟩ :=
    fiber_has_block_form_preimages hk a b c ha hb hc hda hdb hdc i j hfib
  refine ⟨i_m, j_m, h1, h2, ?_⟩
  simpa only [diagMat_delta_val (k + 1) a ha, diagMat_delta_val (k + 1) b hb,
    diagMat_delta_val (k + 1) c hc] using
    (fiber_diagMat_iff_mem_H a b c ha hb hc i_m.out j_m.out).mpr
      (slSuccEmbed_H_fiber_transfer_converse a b c ha hb hc i_m.out j_m.out h_lifted)

end HeckeRing.GLn
