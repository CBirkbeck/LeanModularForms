/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.TrailingHNF

/-!
# Block Embedding Bijection: stabilizer and fiber block-form lemmas

This file develops the i-side block-reduction step of the block-embedding bijection used in
the Hecke-ring construction for GL(n+2). Given a class `i` in the `Fin.cons 1 a`-diagonal
fiber, it produces a stabilizer matrix `M ∈ SL(k+2, ℤ)` and a `(k+1)`-block factor `σ_m`
with `toSL i.out * M = slSuccEmbed σ_m`, then packages the matching integer-conjugation and
adjugate-rearrangement identities. The j-side analogue (`exists_stab_with_block_form_of_X_fiber`)
is obtained by applying the i-side reduction to `X := N_i⁻¹ * toSL j.out`.

## Main results

* `exists_stab_with_block_form_of_fiber`: i-side block-form witness from the fiber relation.
* `fiber_int_mat_eq_via_i_block`: integer-matrix equation in i-substituted form.
* `hfib_col_div_b_via_i_block`: i-side block witnesses plus j-side column-divisibility.
* `exists_stab_with_block_form_of_X_fiber`: X-side block-form witness from the substituted fiber.
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

private lemma toSL_val_cast {k : ℕ} (σ : (GL_pair (k + 2)).H) (r c : Fin (k + 2)) :
    ((toSL σ).val r c : ℚ) = (σ : GL (Fin (k + 2)) ℚ).val r c := by
  have h_units := congr_arg Units.val (toSL_spec σ)
  rw [mapGL_coe_matrix] at h_units
  simpa only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, algebraMap_int_eq, eq_intCast] using congrFun (congrFun h_units r) c

/-- Membership of `σ : (GL_pair (k+2)).H` in the `subgroupOf`-style stabilizer for
`diagMat_delta (k+2) (Fin.cons 1 a)` is equivalent to the matrix-conjugation condition
`D⁻¹ * σ * D ∈ (GL_pair (k+2)).H` (where `D = diagMat (k+2) (Fin.cons 1 a)`). -/
lemma mem_diagMat_cons_stabilizer_subgroupOf_iff {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (σ : (GL_pair (k + 2)).H) :
    σ ∈ (ConjAct.toConjAct ((diagMat_delta (k + 2) (Fin.cons 1 a) :
            (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ) • (GL_pair (k + 2)).H).subgroupOf
          (GL_pair (k + 2)).H ↔
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (σ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv,
    diagMat_delta_val (k + 2) (Fin.cons 1 a) (cons_one_pos ha)]

/-- Integer-level conjugation identity for a `Fin.cons 1 _`-stabilizer SL matrix: given
`M : SL_(k+2)(ℤ)` whose `mapGL ℚ`-image lies in the diag-conjugation stabilizer of
`Fin.cons 1 a`, there exists `N : SL_(k+2)(ℤ)` with `diagonal (Fin.cons 1 a) * N = M *
diagonal (Fin.cons 1 a)`. -/
lemma exists_stab_int_conjugate_diagMat_cons_one {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hM_stab : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          ((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℤ)) * N.val =
        M.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          ((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℤ)) := by
  obtain ⟨N, hN⟩ := hM_stab
  refine ⟨N, ?_⟩
  have h_GL_eq : diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
    rw [hN]; group
  have h_mat := congr_arg
    (fun g : GL (Fin (k + 2)) ℚ ↦ (g : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)) h_GL_eq
  simp only [Units.val_mul] at h_mat
  have h_D : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        ((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ (cons_one_pos ha),
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  rw [show ((mapGL ℚ N : GL _ ℚ) : Matrix _ _ ℚ) = N.1.map (algebraMap ℤ ℚ) from rfl,
      show ((mapGL ℚ M : GL _ ℚ) : Matrix _ _ ℚ) = M.1.map (algebraMap ℤ ℚ) from rfl,
      h_D, ← Matrix.map_mul, ← Matrix.map_mul] at h_mat
  exact Matrix.map_injective (algebraMap ℤ ℚ).injective_int h_mat

private lemma stabilizer_implies_first_col_div_chain {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 2)).H)
    (hσ_stab : σ ∈ (ConjAct.toConjAct ((diagMat_delta (k + 2) (Fin.cons 1 a) :
            (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ) • (GL_pair (k + 2)).H).subgroupOf
          (GL_pair (k + 2)).H) :
    ∀ i : Fin (k + 1), (a i : ℤ) ∣ (toSL σ).val i.succ 0 := by
  rw [mem_diagMat_cons_stabilizer_subgroupOf_iff a ha] at hσ_stab
  obtain ⟨N, hN⟩ := hσ_stab
  intro i
  refine ⟨N.val i.succ 0, ?_⟩
  have h_GL_eq :
      diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N) =
      (σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
    rw [hN]; group
  have h_entry :
      ((diagMat (k + 2) (Fin.cons 1 a)).val *
        (mapGL ℚ N).val : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ) i.succ 0 =
      ((σ : GL (Fin (k + 2)) ℚ).val *
        (diagMat (k + 2) (Fin.cons 1 a)).val : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)
          i.succ 0 :=
    congrFun
      (congrFun (by simpa only [Units.val_mul] using congr_arg Units.val h_GL_eq) i.succ) 0
  rw [diagMat_val _ _ (cons_one_pos ha), Matrix.diagonal_mul, Matrix.mul_diagonal,
    mapGL_coe_matrix] at h_entry
  simp only [Fin.cons_succ, Fin.cons_zero, Nat.cast_one, mul_one,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, algebraMap_int_eq, eq_intCast] at h_entry
  rw [← toSL_val_cast σ i.succ 0] at h_entry
  exact_mod_cast h_entry.symm

private lemma exists_stab_with_inv_first_col_of_fiber {k : ℕ}
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
    ∃ M : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ r : Fin (k + 2), M.1 r 0 = ((toSL i.out)⁻¹ :
        SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  exact sl_exists_col_stab_divChain a ha hda _
    (sl_first_col_primitive (toSL i.out)⁻¹)
    (hfib_col_div_a a b c ha hb hc i j hfib)

private lemma mul_first_col_eq_e0_of_col_eq_inv {k : ℕ}
    (Y M_0 : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hM_col : ∀ r : Fin (k + 2),
      M_0.1 r 0 = (Y⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0)
    (r : Fin (k + 2)) :
    (Y * M_0).1 r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
  have h_to_inv : (Y * M_0).1 r 0 =
      (Y * Y⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 := by
    simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun p _ ↦ by rw [hM_col p]
  rw [h_to_inv, mul_inv_cancel, SpecialLinearGroup.coe_one]

private lemma exists_stab_with_first_col_e0_of_fiber {k : ℕ}
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
    ∃ M : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ r : Fin (k + 2),
        (toSL i.out * M : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 =
          (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨M, hM_col, hM_stab⟩ :=
    exists_stab_with_inv_first_col_of_fiber a b c ha hb hc hda i j hfib
  exact ⟨M, mul_first_col_eq_e0_of_col_eq_inv (toSL i.out) M hM_col, hM_stab⟩

private lemma diagMat_cons_conj_mapGL_mem_H_mul {k : ℕ} (d : Fin (k + 1) → ℕ)
    (A B : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hA : (diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
      (mapGL ℚ A : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 d) ∈ (GL_pair (k + 2)).H)
    (hB : (diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
      (mapGL ℚ B : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 d) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
      (mapGL ℚ (A * B) : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 d) ∈ (GL_pair (k + 2)).H := by
  have h_split : (diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
      (mapGL ℚ (A * B) : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 d) =
      ((diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
        (mapGL ℚ A : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 d)) *
      ((diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
        (mapGL ℚ B : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 d)) := by
    rw [map_mul]; group
  rw [h_split]
  exact mul_mem hA hB

private lemma slTransvec_zero_succ_stab {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (l : Fin (k + 1)) (c : ℤ) :
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ (slTransvecG (0 : Fin (k + 2)) l.succ (Fin.succ_ne_zero l).symm c)
        : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  apply diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd a ha
  intro i' j'
  by_cases hi : i' = 0
  · subst hi
    show ((Fin.cons 1 a : Fin (k + 2) → ℕ) 0 : ℤ) ∣ _
    simp
  · rw [show (slTransvecG (0 : Fin (k + 2)) l.succ (Fin.succ_ne_zero l).symm c).1 i' j' =
          if i' = j' then 1 else 0 from by
        show (Matrix.transvection (0 : Fin (k + 2)) l.succ c) i' j' = _
        simp [Matrix.transvection, Matrix.one_apply,
          show ¬ (0 = i' ∧ l.succ = j') from fun ⟨h0, _⟩ ↦ hi h0.symm]]
    by_cases h_diag : i' = j'
    · subst h_diag; simp
    · simp [h_diag]

private lemma sl_first_row_clear_insert_step {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (W : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col0_zero : W.1 0 0 = 1)
    (h_col0_succ_zero : ∀ r' : Fin (k + 1), W.1 r'.succ 0 = 0)
    (l₀ : Fin (k + 1)) (S' : Finset (Fin (k + 1))) (hl₀_notin : l₀ ∉ S')
    (T' : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hT'_col0 : ∀ r : Fin (k + 2), (W * T').1 r 0 = W.1 r 0)
    (hT'_S : ∀ l : Fin (k + 1), l ∈ S' → (W * T').1 0 l.succ = 0)
    (hT'_outside : ∀ l : Fin (k + 1), l ∉ S' → (W * T').1 0 l.succ = W.1 0 l.succ)
    (hT'_block : ∀ i j : Fin (k + 1), (W * T').1 i.succ j.succ = W.1 i.succ j.succ)
    (hT'_stab : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ T' : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H) :
    ∃ T : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ r : Fin (k + 2), (W * T).1 r 0 = W.1 r 0) ∧
      (∀ l : Fin (k + 1), l ∈ insert l₀ S' → (W * T).1 0 l.succ = 0) ∧
      (∀ l : Fin (k + 1), l ∉ insert l₀ S' → (W * T).1 0 l.succ = W.1 0 l.succ) ∧
      (∀ i j : Fin (k + 1), (W * T).1 i.succ j.succ = W.1 i.succ j.succ) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ T : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  set c_l₀ : ℤ := -(W.1 0 l₀.succ) with hc_l₀_def
  set T_l₀ : SpecialLinearGroup (Fin (k + 2)) ℤ :=
    slTransvecG (0 : Fin (k + 2)) l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ with hT_l₀_def
  have h_assoc : W * (T' * T_l₀) = (W * T') * T_l₀ := (mul_assoc _ _ _).symm
  refine ⟨T' * T_l₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    rw [h_assoc, hT_l₀_def, sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀
        (W * T') r (Fin.succ_ne_zero l₀).symm]
    exact hT'_col0 r
  · intro l hl
    rw [h_assoc, hT_l₀_def]
    obtain h_eq | hl_S' := Finset.mem_insert.mp hl
    · subst h_eq
      rw [sl_addCol_target_col 0 l.succ (Fin.succ_ne_zero l).symm c_l₀ (W * T') 0,
        hT'_outside l hl₀_notin, show (W * T').1 0 0 = 1 from hT'_col0 0 ▸ h_col0_zero]
      show W.1 0 l.succ + c_l₀ * 1 = 0
      rw [hc_l₀_def]; ring
    · rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') 0
          (fun h ↦ hl₀_notin (Fin.succ_injective _ h ▸ hl_S'))]
      exact hT'_S l hl_S'
  · intro l hl_notin
    rw [h_assoc, hT_l₀_def,
        sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') 0
        (fun h ↦ hl_notin (Fin.succ_injective _ h ▸ Finset.mem_insert_self _ _))]
    exact hT'_outside l (fun h ↦ hl_notin (Finset.mem_insert_of_mem h))
  · intro i' j'
    rw [h_assoc, hT_l₀_def]
    by_cases h_eq : j'.succ = l₀.succ
    · obtain rfl : j' = l₀ := Fin.succ_injective _ h_eq
      rw [sl_addCol_target_col 0 j'.succ (Fin.succ_ne_zero j').symm c_l₀ (W * T') i'.succ,
        show (W * T').1 i'.succ 0 = 0 from hT'_col0 i'.succ ▸ h_col0_succ_zero i',
        mul_zero, add_zero]
      exact hT'_block i' j'
    · rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') i'.succ
          h_eq]
      exact hT'_block i' j'
  · rw [hT_l₀_def]
    exact diagMat_cons_conj_mapGL_mem_H_mul a T' _ hT'_stab
      (slTransvec_zero_succ_stab a ha l₀ c_l₀)

/-- Row-clearance via upper transvections with stabilizer membership: given `W ∈ SL(k+2, ℤ)`
whose first column equals `e₀` and a finset `S` of columns to clear, produce a transvection
product `T` such that `W * T` fixes column `0`, zeroes the `(0, l.succ)` entries for `l ∈ S`,
leaves other first-row entries and the bottom-right block unchanged, and stays in the
diag-conjugation stabilizer. -/
lemma sl_first_row_clear_with_col0_e0 {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (W : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col0 : ∀ r : Fin (k + 2),
      W.1 r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0)
    (S : Finset (Fin (k + 1))) :
    ∃ T : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ r : Fin (k + 2), (W * T).1 r 0 = W.1 r 0) ∧
      (∀ l : Fin (k + 1), l ∈ S → (W * T).1 0 l.succ = 0) ∧
      (∀ l : Fin (k + 1), l ∉ S → (W * T).1 0 l.succ = W.1 0 l.succ) ∧
      (∀ i j : Fin (k + 1), (W * T).1 i.succ j.succ = W.1 i.succ j.succ) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ T : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  have h_col0_zero : W.1 0 0 = 1 := by simpa using h_col0 0
  have h_col0_succ_zero : ∀ r' : Fin (k + 1), W.1 r'.succ 0 = 0 := fun r' ↦ by
    simpa using h_col0 r'.succ
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_, ?_, ?_, ?_⟩
      · intro r; simp
      · intro l hl; exact absurd hl (Finset.notMem_empty _)
      · intro l _; simp
      · intro i j; simp
      · simp
  | insert l₀ S' hl₀_notin ih =>
      obtain ⟨T', hT'_col0, hT'_S, hT'_outside, hT'_block, hT'_stab⟩ := ih
      exact sl_first_row_clear_insert_step a ha W h_col0_zero h_col0_succ_zero
        l₀ S' hl₀_notin T' hT'_col0 hT'_S hT'_outside hT'_block hT'_stab

private lemma adjugate_adjugate_of_det_one {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (h_card : Fintype.card (Fin n) ≠ 1)
    (hdet : A.det = 1) : Matrix.adjugate (Matrix.adjugate A) = A := by
  rw [Matrix.adjugate_adjugate _ h_card, hdet, one_pow, one_smul]

private lemma adjugate_rearr_cancel {n : ℕ} (h_card : Fintype.card (Fin n) ≠ 1)
    (Da X Db Dc Bm νm : Matrix (Fin n) (Fin n) ℤ)
    (hν : νm.det = 1) (hB : Bm.det = 1)
    (h : Da * X * Db * Matrix.adjugate νm = Matrix.adjugate Bm * Dc) :
    Matrix.adjugate Db * Matrix.adjugate X * Matrix.adjugate Da =
      Matrix.adjugate νm * (Matrix.adjugate Dc * Bm) := by
  have h_rearr_adj := congr_arg Matrix.adjugate h
  rw [show Matrix.adjugate (Da * X * Db * Matrix.adjugate νm) =
        Matrix.adjugate (Matrix.adjugate νm) *
          (Matrix.adjugate Db * (Matrix.adjugate X * Matrix.adjugate Da)) by
      rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
          Matrix.adjugate_mul_distrib],
    show Matrix.adjugate (Matrix.adjugate Bm * Dc) =
        Matrix.adjugate Dc * Matrix.adjugate (Matrix.adjugate Bm) by
      rw [Matrix.adjugate_mul_distrib],
    adjugate_adjugate_of_det_one _ h_card hν,
    adjugate_adjugate_of_det_one _ h_card hB] at h_rearr_adj
  have h_premul : Matrix.adjugate νm *
        (νm * (Matrix.adjugate Db * (Matrix.adjugate X * Matrix.adjugate Da))) =
      Matrix.adjugate νm * (Matrix.adjugate Dc * Bm) := by rw [h_rearr_adj]
  rw [show Matrix.adjugate νm *
        (νm * (Matrix.adjugate Db * (Matrix.adjugate X * Matrix.adjugate Da))) =
      (Matrix.adjugate νm * νm) *
        (Matrix.adjugate Db * (Matrix.adjugate X * Matrix.adjugate Da)) by
      simp only [Matrix.mul_assoc],
    Matrix.adjugate_mul, hν, one_smul, Matrix.one_mul,
    show Matrix.adjugate Db * (Matrix.adjugate X * Matrix.adjugate Da) =
      Matrix.adjugate Db * Matrix.adjugate X * Matrix.adjugate Da by
      simp only [Matrix.mul_assoc]] at h_premul
  exact h_premul

private lemma det_block_eq_one_of_row0_e0 {k : ℕ}
    (N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (hN_det : N.det = 1)
    (hN_00 : N 0 0 = 1) (hN_row0 : ∀ l : Fin (k + 1), N 0 l.succ = 0) :
    Matrix.det (Matrix.of fun I J : Fin (k + 1) ↦ N I.succ J.succ) = 1 := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Finset.sum_eq_zero (fun j _ ↦ by rw [hN_row0 j]; ring), add_zero, hN_00] at hN_det
  simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at hN_det
  rwa [show N.submatrix Fin.succ (0 : Fin (k + 2)).succAbove =
      Matrix.of fun I J : Fin (k + 1) ↦ N I.succ J.succ by
    ext I J; rw [Fin.succAbove_zero]; rfl] at hN_det

private lemma exists_block_form_of_col0_e0 {k : ℕ}
    (d : Fin (k + 1) → ℕ) (hd : ∀ i, 0 < d i)
    (Y M_0 : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col_e0 : ∀ r : Fin (k + 2),
      (Y * M_0).1 r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0)
    (hM_0_stab : (diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
      (mapGL ℚ M_0 : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 d) ∈ (GL_pair (k + 2)).H) :
    ∃ (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (σ : SpecialLinearGroup (Fin (k + 1)) ℤ),
      Y * M = slSuccEmbed σ ∧
      (diagMat (k + 2) (Fin.cons 1 d))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 d) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 d hd (Y * M_0) h_col_e0 Finset.univ
  set M : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0 * T_clear with hM_def
  set N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (Y * M).1 with hN_def
  have hM_assoc : Y * M = (Y * M_0) * T_clear := by rw [hM_def, mul_assoc]
  have hN_col0 : ∀ r : Fin (k + 2),
      N r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (Y * M).1 r 0 = _
    rw [hM_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), N 0 l.succ = 0 := by
    intro l
    show (Y * M).1 0 l.succ = _
    rw [hM_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N 0 0 = 1 := by simpa using hN_col0 0
  have hN_succ0 : ∀ I : Fin (k + 1), N I.succ 0 = 0 := fun I ↦ by
    simpa using hN_col0 I.succ
  refine ⟨M, ⟨Matrix.of fun I J ↦ N I.succ J.succ,
    det_block_eq_one_of_row0_e0 N (hN_def ▸ (Y * M).2) hN_00 hN_row0⟩, ?_, ?_⟩
  · apply Subtype.ext
    ext I J
    show N I J = (slSuccEmbed _).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'; rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'; rw [slSuccEmbed_val_succ_succ]; rfl
  · rw [hM_def]
    exact diagMat_cons_conj_mapGL_mem_H_mul d M_0 T_clear hM_0_stab hT_stab

/-- i-side block-form witness from the fiber: produce `M ∈ SL(k+2, ℤ)` in the
diag-conjugation stabilizer and `σ_m ∈ SL(k+1, ℤ)` such that
`toSL i.out * M = slSuccEmbed σ_m`, identifying `i.out` (modulo stabilizer) with the
block-embedding image of a dim-`(k+1)` class. -/
lemma exists_stab_with_block_form_of_fiber {k : ℕ}
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
    ∃ (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ),
      toSL i.out * M = slSuccEmbed σ_m ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨M_0, hM_0_col, hM_0_stab⟩ :=
    exists_stab_with_first_col_e0_of_fiber a b c ha hb hc hda i j hfib
  exact exists_block_form_of_col0_e0 a ha (toSL i.out) M_0 hM_0_col hM_0_stab

private lemma fiber_int_mat_eq_via_i_block_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
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
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (slSuccEmbed σ_i).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
          (N_i⁻¹ * toSL j.out).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) =
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * ν.val := by
  obtain ⟨ν, hν⟩ := hfib_int_mat_eq a b c ha hb hc i j hfib
  refine ⟨ν, ?_⟩
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))
  have h_M_inv_M_val :
      (M_i⁻¹).val * M_i.val = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) :=
    show ((M_i⁻¹) * M_i).val = (1 : SpecialLinearGroup (Fin (k + 2)) ℤ).val by
      rw [inv_mul_cancel]
  have h_N_N_inv_val :
      N_i.val * (N_i⁻¹).val = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) :=
    show (N_i * N_i⁻¹).val = (1 : SpecialLinearGroup (Fin (k + 2)) ℤ).val by
      rw [mul_inv_cancel]
  have h_inv_conj : (M_i⁻¹).val * D_a = D_a * (N_i⁻¹).val := by
    have step2 : (M_i⁻¹).val * D_a * N_i.val * (N_i⁻¹).val = D_a * (N_i⁻¹).val := by
      rw [show (M_i⁻¹).val * D_a * N_i.val = D_a by
        rw [Matrix.mul_assoc, h_int_conj, ← Matrix.mul_assoc, h_M_inv_M_val, Matrix.one_mul]]
    rwa [Matrix.mul_assoc, h_N_N_inv_val, Matrix.mul_one] at step2
  have h_block_i_inv_val : (toSL i.out).val =
      (slSuccEmbed σ_i).val * (M_i⁻¹).val :=
    show ((toSL i.out)).val = ((slSuccEmbed σ_i) * M_i⁻¹).val by
      rw [show toSL i.out = slSuccEmbed σ_i * M_i⁻¹ by
        rw [← h_block_i, mul_inv_cancel_right]]
  rw [show (N_i⁻¹ * toSL j.out).val = (N_i⁻¹).val * (toSL j.out).val from rfl,
    show (slSuccEmbed σ_i).val * D_a * ((N_i⁻¹).val * (toSL j.out).val) * D_b =
      ((slSuccEmbed σ_i).val * (D_a * (N_i⁻¹).val)) * (toSL j.out).val * D_b by
      simp only [Matrix.mul_assoc], ← h_inv_conj,
    show (slSuccEmbed σ_i).val * ((M_i⁻¹).val * D_a) * (toSL j.out).val * D_b =
      ((slSuccEmbed σ_i).val * (M_i⁻¹).val) * D_a * (toSL j.out).val * D_b by
      simp only [← Matrix.mul_assoc], ← h_block_i_inv_val]
  exact hν

/-- Substituted integer matrix equation via the i-side block form: packages the i-side
block witnesses `(M_i, σ_i, N_i)` together with `ν` satisfying the substituted equation
`slSuccEmbed σ_i · D_a · (N_i⁻¹ · toSL j.out) · D_b = D_c · ν`. -/
lemma fiber_int_mat_eq_via_i_block {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      (slSuccEmbed σ_i).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
          (N_i⁻¹ * toSL j.out).val *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) =
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * ν.val := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_subst⟩ :=
    fiber_int_mat_eq_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_subst⟩

private lemma fiber_int_mat_eq_via_i_block_rearr_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
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
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) := by
  obtain ⟨ν, h_subst⟩ :=
    fiber_int_mat_eq_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  refine ⟨ν, ?_⟩
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))
  set X : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (N_i⁻¹ * toSL j.out).val
  have h_adj_block_block :
      Matrix.adjugate (slSuccEmbed σ_i).val * (slSuccEmbed σ_i).val =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    rw [Matrix.adjugate_mul, show (slSuccEmbed σ_i).val.det = 1 from
      (slSuccEmbed σ_i).2, one_smul]
  have h_ν_adj_ν :
      ν.val * Matrix.adjugate ν.val =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    rw [Matrix.mul_adjugate, show ν.val.det = 1 from ν.2, one_smul]
  have h_premul : D_a * X * D_b = Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) := by
    have h : Matrix.adjugate (slSuccEmbed σ_i).val *
        ((slSuccEmbed σ_i).val * D_a * X * D_b) =
        Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) := by rw [h_subst]
    rw [show Matrix.adjugate (slSuccEmbed σ_i).val *
            ((slSuccEmbed σ_i).val * D_a * X * D_b) =
          (Matrix.adjugate (slSuccEmbed σ_i).val * (slSuccEmbed σ_i).val) *
            D_a * X * D_b by simp only [Matrix.mul_assoc],
      h_adj_block_block, Matrix.one_mul] at h
    exact h
  have h : D_a * X * D_b * Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) *
        Matrix.adjugate ν.val := by rw [h_premul]
  rw [show Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val * D_c * (ν.val * Matrix.adjugate ν.val) by
      simp only [Matrix.mul_assoc], h_ν_adj_ν, Matrix.mul_one] at h
  exact h

private lemma fiber_int_mat_eq_via_i_block_rearr {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_rearr⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_rearr⟩

private lemma fiber_int_mat_eq_via_i_block_rearr_adj_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
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
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) := by
  obtain ⟨ν, h_rearr⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  refine ⟨ν, h_rearr, ?_⟩
  have h_card : Fintype.card (Fin (k + 2)) ≠ 1 := by simp [Fintype.card_fin]
  exact adjugate_rearr_cancel h_card _ (N_i⁻¹ * toSL j.out).val _ _
    (slSuccEmbed σ_i).val ν.val ν.2 (slSuccEmbed σ_i).2 h_rearr

private lemma fiber_int_mat_eq_via_i_block_rearr_adj {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_rearr, h_adj⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_adj_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_rearr, h_adj⟩

private lemma det_diagMat_cons_one_prod {k : ℕ} (d : Fin (k + 1) → ℕ) :
    (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 d : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).det =
      ∏ q : Fin (k + 1), (d q : ℤ) := by
  rw [Matrix.det_diagonal, Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

private lemma prod_cons_one_erase_succ_mul {k : ℕ} (d : Fin (k + 1) → ℕ)
    (r : Fin (k + 1)) :
    (∏ x ∈ Finset.univ.erase r.succ,
        (((Fin.cons 1 d : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) * (d r : ℤ) =
      ∏ q : Fin (k + 1), (d q : ℤ) := by
  have h := Finset.mul_prod_erase (Finset.univ : Finset (Fin (k + 2)))
    (fun x : Fin (k + 2) ↦ (((Fin.cons 1 d : Fin (k + 2) → ℕ) x : ℕ) : ℤ))
    (Finset.mem_univ r.succ)
  simp only at h
  have h_full :
      ∏ x : Fin (k + 2), (((Fin.cons 1 d : Fin (k + 2) → ℕ) x : ℕ) : ℤ) =
      ∏ q : Fin (k + 1), (d q : ℤ) := by
    rw [Fin.prod_univ_succ, show
        (((Fin.cons 1 d : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℕ) : ℤ) = 1 from by
        simp [Fin.cons_zero], one_mul]
    exact Finset.prod_congr rfl fun i _ ↦ by simp [Fin.cons_succ]
  rw [show (((Fin.cons 1 d : Fin (k + 2) → ℕ) r.succ : ℕ) : ℤ) = (d r : ℤ) from by
      simp [Fin.cons_succ], h_full] at h
  linarith [h]

private lemma mul_adjugate_diagMat_cons_block_col0 {k : ℕ} (c : Fin (k + 1) → ℕ)
    (σ : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (L : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) (r : Fin (k + 1)) :
    (L * (Matrix.adjugate (Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) *
        (slSuccEmbed σ).val)) r.succ 0 =
      L r.succ 0 * ∏ q : Fin (k + 1), (c q : ℤ) := by
  have hcol0 : ∀ p : Fin (k + 2),
      (Matrix.adjugate (Matrix.diagonal (fun s : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) * (slSuccEmbed σ).val) p 0 =
        if p = 0 then (∏ q : Fin (k + 1), (c q : ℤ)) else 0 := by
    intro p
    rw [Matrix.adjugate_diagonal, Matrix.diagonal_mul]
    refine Fin.cases ?_ ?_ p
    · rw [slSuccEmbed_val_zero_zero, mul_one, if_pos rfl,
        Finset.prod_erase (Finset.univ : Finset (Fin (k + 2)))
          (show (((Fin.cons 1 c : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℕ) : ℤ) = 1 from by
            simp [Fin.cons_zero]), Fin.prod_univ_succ]
      simp [Fin.cons_zero, Fin.cons_succ]
    · intro p'; rw [slSuccEmbed_val_succ_zero, mul_zero, if_neg (Fin.succ_ne_zero p')]
  rw [Matrix.mul_apply,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_univ _) (fun p _ hp ↦ by
      rw [hcol0 p, if_neg hp, mul_zero]), hcol0 0, if_pos rfl]

private lemma adj_rearr_col0_entry {k : ℕ} (a b c : Fin (k + 1) → ℕ)
    (X : SpecialLinearGroup (Fin (k + 2)) ℤ) (σ : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (νm : SpecialLinearGroup (Fin (k + 2)) ℤ) (r : Fin (k + 1))
    (h_adj :
      Matrix.adjugate (Matrix.diagonal (fun s : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) *
        Matrix.adjugate X.val *
        Matrix.adjugate (Matrix.diagonal (fun s : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) =
      Matrix.adjugate νm.val *
        (Matrix.adjugate (Matrix.diagonal (fun s : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) * (slSuccEmbed σ).val)) :
    (∏ q : Fin (k + 1), (a q : ℤ)) *
        ((∏ x ∈ Finset.univ.erase r.succ,
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
          Matrix.adjugate X.val r.succ 0) =
      Matrix.adjugate νm.val r.succ 0 * ∏ q : Fin (k + 1), (c q : ℤ) := by
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun s : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) with hD_a_def
  have h_postmul :
      (∏ q : Fin (k + 1), (a q : ℤ)) •
        (Matrix.adjugate (Matrix.diagonal (fun s : Fin (k + 2) ↦
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) * Matrix.adjugate X.val) =
      Matrix.adjugate νm.val *
        (Matrix.adjugate (Matrix.diagonal (fun s : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) * (slSuccEmbed σ).val) * D_a := by
    have h := congr_arg (· * D_a) h_adj
    simp only [Matrix.mul_assoc, Matrix.adjugate_mul, hD_a_def ▸ det_diagMat_cons_one_prod a,
      Matrix.mul_one, Matrix.mul_smul] at h ⊢
    exact h
  have h_entry := congrFun (congrFun h_postmul r.succ) 0
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.adjugate_diagonal, Matrix.diagonal_mul,
    hD_a_def, Matrix.mul_diagonal, show
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℕ) : ℤ) = 1 from by
      simp [Fin.cons_zero], mul_one,
    mul_adjugate_diagMat_cons_block_col0 c σ (Matrix.adjugate νm.val) r] at h_entry
  exact h_entry

/-- j-side col-divisibility on `X := N_i⁻¹ · toSL j.out` from explicit i-side block witnesses:
packages the rearranged and adjugate-rearranged equations together with the col-divisibility
`∀ r, (b r : ℤ) ∣ (X⁻¹).val r.succ 0`. -/
lemma hfib_col_div_b_via_i_block_explicit {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (M_i : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (h_block_i : toSL i.out * M_i = slSuccEmbed σ_i)
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
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) ∧
      ∀ r : Fin (k + 1),
        (b r : ℤ) ∣ ((N_i⁻¹ * toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 := by
  obtain ⟨ν, h_rearr, h_adj⟩ :=
    fiber_int_mat_eq_via_i_block_rearr_adj_explicit a b c ha hb hc i M_i σ_i
      h_block_i N_i h_int_conj j hfib
  refine ⟨ν, h_rearr, h_adj, ?_⟩
  intro r
  have hprod_eq :
      (∏ q : Fin (k + 1), (a q : ℤ)) * (∏ q : Fin (k + 1), (b q : ℤ)) =
      ∏ q : Fin (k + 1), (c q : ℤ) := by
    have h := congr_arg Matrix.det h_rearr
    simp only [Matrix.det_mul, Matrix.det_adjugate, (slSuccEmbed σ_i).2,
      (N_i⁻¹ * toSL j.out).2, ν.2, det_diagMat_cons_one_prod a,
      det_diagMat_cons_one_prod b, det_diagMat_cons_one_prod c,
      one_pow, mul_one, one_mul] at h
    exact h
  have h_mul_b_r := congr_arg (· * (b r : ℤ))
    (adj_rearr_col0_entry a b c (N_i⁻¹ * toSL j.out) σ_i ν r h_adj)
  simp only at h_mul_b_r
  have h_LHS_b :
      (∏ q : Fin (k + 1), (a q : ℤ)) *
          ((∏ x ∈ Finset.univ.erase r.succ,
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
            Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) * (b r : ℤ) =
      (∏ q : Fin (k + 1), (c q : ℤ)) *
          Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 := by
    rw [show (∏ q : Fin (k + 1), (a q : ℤ)) *
            ((∏ x ∈ Finset.univ.erase r.succ,
              (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
              Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) * (b r : ℤ) =
          (∏ q : Fin (k + 1), (a q : ℤ)) *
            (((∏ x ∈ Finset.univ.erase r.succ,
              (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) * (b r : ℤ)) *
              Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) by ring,
      prod_cons_one_erase_succ_mul b r, ← mul_assoc, hprod_eq]
  rw [h_LHS_b, show Matrix.adjugate ν.val r.succ 0 *
        (∏ q : Fin (k + 1), (c q : ℤ)) * (b r : ℤ) =
      (∏ q : Fin (k + 1), (c q : ℤ)) *
        ((b r : ℤ) * Matrix.adjugate ν.val r.succ 0) from by ring] at h_mul_b_r
  refine ⟨Matrix.adjugate ν.val r.succ 0, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_inv]
  exact mul_left_cancel₀ (Finset.prod_pos fun q _ ↦ by exact_mod_cast hc q).ne' h_mul_b_r

/-- From the fiber relation, packages the i-side block witnesses `(σ_i, M_i, N_i, ν)` together
with the j-side col-divisibility `∀ r, (b r : ℤ) ∣ ((N_i⁻¹ · toSL j.out)⁻¹).1 r.succ 0`. -/
lemma hfib_col_div_b_via_i_block {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hc : ∀ i, 0 < c i) (hda : DivChain (k + 1) a)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ (σ_i : SpecialLinearGroup (Fin (k + 1)) ℤ)
      (M_i N_i ν : SpecialLinearGroup (Fin (k + 2)) ℤ),
      toSL i.out * M_i = slSuccEmbed σ_i ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        (N_i⁻¹ * toSL j.out).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate (Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))) *
        (slSuccEmbed σ_i).val) ∧
      ∀ r : Fin (k + 1),
        (b r : ℤ) ∣ ((N_i⁻¹ * toSL j.out)⁻¹ :
          SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 := by
  obtain ⟨M_i, σ_i, h_block_i, h_stab_i⟩ :=
    exists_stab_with_block_form_of_fiber a b c ha hb hc hda i j hfib
  obtain ⟨N_i, h_int_conj⟩ :=
    exists_stab_int_conjugate_diagMat_cons_one a ha M_i h_stab_i
  obtain ⟨ν, h_rearr, h_adj, h_div⟩ :=
    hfib_col_div_b_via_i_block_explicit a b c ha hb hc i M_i σ_i h_block_i
      N_i h_int_conj j hfib
  exact ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_rearr, h_adj, h_div⟩

/-- X-side block-form witness from the substituted fiber: the j-side analog of
`exists_stab_with_block_form_of_fiber` for `X := N_i⁻¹ * toSL j.out`. Produces
`M_X ∈ SL(k+2, ℤ)` in the `Fin.cons 1 b`-diagonal-conjugation stabilizer and
`τ_X ∈ SL(k+1, ℤ)` with `(N_i⁻¹ * toSL j.out) * M_X = slSuccEmbed τ_X`, alongside the
i-side witnesses `M_i, N_i` and their integer conjugation identity. -/
lemma exists_stab_with_block_form_of_X_fiber {k : ℕ}
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
    ∃ (M_i N_i M_X : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ),
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M_i : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H ∧
      Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * N_i.val =
        M_i.val *
        Matrix.diagonal (fun r : Fin (k + 2) ↦
          (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) ∧
      (N_i⁻¹ * toSL j.out) * M_X = slSuccEmbed τ_X ∧
      (diagMat (k + 2) (Fin.cons 1 b))⁻¹ *
        (mapGL ℚ M_X : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨_, M_i, N_i, _, _, h_stab_i, h_int_conj, _, _, h_div⟩ :=
    hfib_col_div_b_via_i_block a b c ha hb hc hda i j hfib
  set X : SpecialLinearGroup (Fin (k + 2)) ℤ := N_i⁻¹ * toSL j.out
  obtain ⟨M_0_X, hM_0_X_col, hM_0_X_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      (fun d hd ↦ sl_first_col_primitive X⁻¹ d hd) h_div
  obtain ⟨M_X, τ_X, h_block_X, h_stab_X⟩ :=
    exists_block_form_of_col0_e0 b hb X M_0_X
      (mul_first_col_eq_e0_of_col_eq_inv X M_0_X hM_0_X_col) hM_0_X_stab
  exact ⟨M_i, N_i, M_X, τ_X, h_stab_i, h_int_conj, h_block_X, h_stab_X⟩

end HeckeRing.GLn
