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

/-- **Class equality in `decompQuot` from an in-stabilizer inverse block witness.**
If `σ_H : (GL_pair (k+1)).H` and `g : (GL_pair (k+2)).H` satisfy
`(slSuccEmbed_H σ_H)⁻¹ · g = (mapGL ℚ M)⁻¹` for some `M ∈ SL_(k+2)(ℤ)` whose
`diagMat (Fin.cons 1 a)`-conjugate lies in `H_{k+2}`, then `slSuccEmbed_H σ_H`
and `g` represent the same class in `decompQuot ... (diagMat_delta (Fin.cons 1 a))`.

This is the rep-equivalence tail shared by all four block-witness class equalities
(`exists_i_m_block_class_eq_of_fiber`, `exists_j_m_X_block_class_eq_of_fiber`, and
both class goals of `fiber_block_form_preimage_corrected_j_explicit`): the left
relation reduces to `((slSuccEmbed_H σ_H)⁻¹ · g)`'s `D_a`-conjugate lying in
`H_{k+2}`, which by the witness equals `(mapGL ℚ M)⁻¹`'s `D_a`-conjugate, in
`H_{k+2}` by `inv_mem` applied to the assumed stabilizer membership. -/
private lemma decompQuot_slSuccEmbed_eq_of_inv_block_stab {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ_H : (GL_pair (k + 1)).H) (g : (GL_pair (k + 2)).H)
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
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
    h_GL_val]
  have h_inv_form : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ)⁻¹ * diagMat (k + 2) (Fin.cons 1 a) =
      ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ * (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a))⁻¹ := by group
  rw [h_inv_form]
  exact inv_mem h_M_stab

/-- **Canonical class equality from a direct block witness.**  If `M ∈ SL_(k+2)(ℤ)`
satisfies the block identity `toSL g.out · M = slSuccEmbed σ` and its `D_a`-conjugate
lies in `H_{k+2}`, then the class `⟦⟨mapGL σ,_⟩⟧` descends under
`decompQuot_slSuccEmbed_diagMat` back to `g`.

This wraps `decompQuot_slSuccEmbed_eq_of_inv_block_stab` together with the GL-level
computation of `(slSuccEmbed_H σ_H)⁻¹ · g.out = (mapGL M)⁻¹` from the block identity;
it is the i/j-side class-equality step shared by `exists_i_m_block_class_eq_of_fiber`,
`fiber_class_preimages_from_joint_block_witnesses`, and
`fiber_has_block_form_preimages_existential_reps`. -/
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
  have h_slSuccEmbed_GL :
      (slSuccEmbed_H ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩ : GL (Fin (k + 2)) ℚ) =
      (g.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M := by
    show mapGL ℚ (slSuccEmbed (toSL ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩)) = _
    rw [show toSL ⟨mapGL ℚ σ, coe_mem_SLnZ (k + 1) σ⟩ = σ from
      SpecialLinearGroup.mapGL_injective (S := ℚ) (by rw [toSL_spec]),
      ← h_block, map_mul, toSL_spec]
  push_cast
  rw [h_slSuccEmbed_GL]; group

/-- **j-side X-class-preimage bridge (corrected representative).**
From `exists_stab_with_block_form_of_X_fiber` (which produces `M_X ∈ stab(D_b)`
and `τ_X ∈ SL_(k+1)(ℤ)` with `(N_i⁻¹ * toSL j.out) * M_X = slSuccEmbed τ_X`),
construct the dim-(k+1) quotient class `j_m := ⟦τ_X_H⟧` and prove the
**corrected** class equality at dim (k+2):

  `decompQuot_slSuccEmbed_diagMat b hb j_m = ⟦j_corrected⟧`

where `j_corrected : (GL_pair (k+2)).H := ⟨mapGL ℚ N_i⁻¹, _⟩ * j.out`.

This is the j-side analog of `exists_i_m_block_class_eq_of_fiber`, but with
the `N_i`-corrected representative instead of `j.out` directly. The class
`⟦j_corrected⟧` differs from `j` by the i-side conjugation factor
`mapGL ℚ N_i⁻¹`; in general these are NOT the same class in
`decompQuot ... (Fin.cons 1 b)`, since `mapGL ℚ N_i⁻¹` need not be in the
`Fin.cons 1 b` stabilizer.

Closing the residual `fiber_has_block_form_preimages` from this corrected
class bridge requires either:
* a sibling of `fiber_has_block_form_preimages_existential_reps` that
  accepts the corrected representative `j_corrected` (delegating the
  N_i-correction to the consumer); or
* a separate proof that `⟦j_corrected⟧ = j` in
  `decompQuot ... (Fin.cons 1 b)`, which would require
  `mapGL ℚ N_i⁻¹ ∈ stab(D_b)` — generally FALSE since N_i comes from
  the `D_a`-stab, not `D_b`-stab.

This lemma is therefore the strongest build-clean X-side bridge available
without modifying the consumer or assuming additional structure on N_i. -/
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
    with hτ_X_H_def
  set N_i_inv_H : (GL_pair (k + 2)).H :=
    ⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ with hN_i_inv_H_def
  set j_corrected : (GL_pair (k + 2)).H := N_i_inv_H * j.out with hj_corr_def
  refine ⟨M_i, N_i, ⟦τ_X_H⟧, h_stab_i, h_int_conj, ?_⟩
  change (⟦slSuccEmbed_H τ_X_H⟧ :
    decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b))) =
    (⟦j_corrected⟧ : decompQuot _ _)
  have h_toSL : toSL τ_X_H = τ_X := by
    apply SpecialLinearGroup.mapGL_injective (S := ℚ)
    rw [toSL_spec]
  refine decompQuot_slSuccEmbed_eq_of_inv_block_stab b hb τ_X_H j_corrected M_X ?_
    h_M_X_stab
  have h_slSuccEmbed_GL : (slSuccEmbed_H τ_X_H : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
    show mapGL ℚ (slSuccEmbed (toSL τ_X_H)) = _
    rw [h_toSL, ← h_X_block, map_mul, map_mul, toSL_spec]
  push_cast
  rw [h_slSuccEmbed_GL]
  show (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X)⁻¹ *
    (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ)) = _
  group

/-- **An `SL_(k+2)` matrix with first row and column `e₀` is a block embedding.**
If `N ∈ SL_(k+2)(ℤ)` has first column `e₀` (`N_{r,0} = δ_{r,0}`) and vanishing
first row off the corner (`N_{0, l.succ} = 0`), then `N = slSuccEmbed τ` where `τ`
is the lower-right `(k+1)×(k+1)` block `N_{·.succ, ·.succ}`.

The block matrix has determinant `1` (Laplace expansion along row 0 collapses to
the corner entry times the block determinant, and the corner is `1`), so the block
defines an element of `SL_(k+1)(ℤ)`; the four `slSuccEmbed_val_*` corner lemmas
then match `N` entrywise with `slSuccEmbed τ` via a double `Fin.cases`. -/
private lemma eq_slSuccEmbed_of_first_row_col_e0 {k : ℕ}
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_col : ∀ r : Fin (k + 2),
      N.val r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0)
    (h_row : ∀ l : Fin (k + 1), N.val 0 l.succ = 0) :
    ∃ τ : SpecialLinearGroup (Fin (k + 1)) ℤ, N = slSuccEmbed τ := by
  have hN_00 : N.val 0 0 = 1 := by
    have h := h_col 0; rwa [Matrix.one_apply_eq] at h
  have hN_succ0 : ∀ I : Fin (k + 1), N.val I.succ 0 = 0 := fun I ↦ by
    have h := h_col I.succ; rwa [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
  set τ_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N.val I.succ J.succ with hτ_raw_def
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

/-- **Block-form column-clearing matrix from column divisibility.**
Given `X ∈ SL_(k+2)(ℤ)` whose inverse satisfies the DivChain-forced first-column
divisibility `b_r ∣ (X⁻¹)_{r.succ, 0}`, construct `M_X ∈ SL_(k+2)(ℤ)` clearing the
first column/row of `X` so that `X · M_X = slSuccEmbed τ_X` for some
`τ_X ∈ SL_(k+1)(ℤ)`, with `M_X` lying in the `diagMat (Fin.cons 1 b)`-stabilizer
(at the GL level).

The construction is a two-step Hermite-normal-form reduction: first
`sl_exists_col_stab_divChain` produces `M_0_X` realizing `X⁻¹`'s first column
(so `X · M_0_X` has first column `e₀`); then `sl_first_row_clear_with_col0_e0`
clears the first row, leaving a block matrix `slSuccEmbed τ_X`. Both factors lie
in the `D_b`-stabilizer, hence so does `M_X := M_0_X · T_clear`. The shared
X-side machinery of `fiber_block_form_preimage_corrected_j_explicit`. -/
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
  have hw_primitive :
      ∀ d : ℤ, (∀ r : Fin (k + 2), d ∣ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0) →
        IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (X⁻¹) d hd
  obtain ⟨M_0_X, hM_0_X_col, hM_0_X_stab⟩ :=
    sl_exists_col_stab_divChain b hb hdb
      (fun r ↦ (X⁻¹ : SpecialLinearGroup _ ℤ).val r 0)
      hw_primitive h_div
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
  have hM_X_assoc : X * M_X = (X * M_0_X) * T_clear := by
    rw [hM_X_def]; exact (mul_assoc _ _ _).symm
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

/-- **GL-level lift of the integer conjugation identity `D_a · N_i = M_i · D_a`.**
The `ℤ`-matrix conjugation hypothesis `diagonal(Fin.cons 1 a) · N_i = M_i ·
diagonal(Fin.cons 1 a)` lifts, under `mapGL ℚ`, to the `GL_(k+2)(ℚ)` identity
`diagMat (Fin.cons 1 a) · mapGL N_i = mapGL M_i · diagMat (Fin.cons 1 a)`. The
`diagMat`-conjugation absorption used in `fiber_block_form_preimage_corrected_j_explicit`. -/
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

/-- **Lifted dim-(k+2) fiber membership from i-side and X-side block witnesses.**
Given the i-side block identity `toSL i.out · M_i = slSuccEmbed σ_i`, the X-side
block identity `(N_i⁻¹ · toSL j.out) · M_X = slSuccEmbed τ_X`, the integer
conjugation `D_a · N_i = M_i · D_a`, the GL-level `D_b`-stabilizer membership of
`M_X`, and the original dim-(k+2) fiber set-form, the conjugated product
`(D_c')⁻¹ · slSuccEmbed_H σ_i_H · D_a' · slSuccEmbed_H τ_X_H · D_b'` lies in
`H_{k+2}` (for `σ_i_H = ⟨mapGL σ_i,_⟩`, `τ_X_H = ⟨mapGL τ_X,_⟩`).

The `N_i`-correction in the X-side witness cancels against the i-side `M_i`
through the conjugation identity (`mapGL M_i · D_a' · mapGL N_i⁻¹ = D_a'`), so
the product factors as `[fiber product] · [M_X-conjugate]`; the first factor is
in `H_{k+2}` by `hfib_to_mem_H`, the second by `h_M_X_stab`. -/
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
    show mapGL ℚ (slSuccEmbed (toSL ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩)) = _
    rw [show toSL ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ = σ_i from
      SpecialLinearGroup.mapGL_injective (S := ℚ) (by rw [toSL_spec]),
      ← h_block_i, map_mul, toSL_spec]
  have h_slSucc_τ_GL :
      (slSuccEmbed_H ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
    show mapGL ℚ (slSuccEmbed (toSL ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩)) = _
    rw [show toSL ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ = τ_X from
      SpecialLinearGroup.mapGL_injective (S := ℚ) (by rw [toSL_spec]),
      ← h_X_block, map_mul, map_mul, toSL_spec]
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

/-- **Corrected-j fiber descent, EXPLICIT-input.**

Same algebraic content as `fiber_block_form_preimage_corrected_j` but
parameterized by explicit i-side block witnesses
`(M_i, σ_i, N_i, h_block_i, h_stab_i, h_int_conj)`.  Returns the corrected
j-class equality referencing the **caller's** `N_i` (rather than
extracting one from a j-dependent existential).

**Use site.**  Combined with i-only `Classical.choose` extraction of
`(M_i, σ_i, N_i)` via `exists_stab_with_block_form_of_fiber` (i-only body)
and `exists_stab_int_conjugate_diagMat_cons_one` (i-only body given
`M_i`), the caller obtains an i-functional `N_i` and the corresponding
i-functional corrected-j descent output.  This is the fifth and main
step in the explicit-parameter Route A chain.

The body is a parameterized version of `fiber_block_form_preimage_corrected_j`'s
proof: it skips the `hfib_col_div_b_via_i_block` extraction (replaced by the
explicit inputs), then uses `hfib_col_div_b_via_i_block_explicit` to get
`h_div`, after which the X-side block construction proceeds identically. -/
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
  · -- i-side class equality.
    rw [show i = ⟦i.out⟧ from (Quotient.out_eq i).symm]
    refine decompQuot_slSuccEmbed_eq_of_inv_block_stab a ha
      ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ i.out M_i ?_ h_stab_i
    have h_slSuccEmbed_GL :
        (slSuccEmbed_H ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ : GL (Fin (k + 2)) ℚ) =
        (i.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_i := by
      show mapGL ℚ (slSuccEmbed (toSL ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩)) = _
      rw [show toSL ⟨mapGL ℚ σ_i, coe_mem_SLnZ (k + 1) σ_i⟩ = σ_i from
        SpecialLinearGroup.mapGL_injective (S := ℚ) (by rw [toSL_spec]),
        ← h_block_i, map_mul, toSL_spec]
    push_cast
    rw [h_slSuccEmbed_GL]; group
  · -- corrected j-side class equality.
    refine decompQuot_slSuccEmbed_eq_of_inv_block_stab b hb
      ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩
      (⟨mapGL ℚ N_i⁻¹, coe_mem_SLnZ (k + 2) N_i⁻¹⟩ * j.out) M_X ?_ h_M_X_stab
    have h_slSuccEmbed_GL :
        (slSuccEmbed_H ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ : GL (Fin (k + 2)) ℚ) =
        (mapGL ℚ N_i⁻¹) * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X := by
      show mapGL ℚ (slSuccEmbed (toSL ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩)) = _
      rw [show toSL ⟨mapGL ℚ τ_X, coe_mem_SLnZ (k + 1) τ_X⟩ = τ_X from
        SpecialLinearGroup.mapGL_injective (S := ℚ) (by rw [toSL_spec]),
        ← h_X_block', map_mul, map_mul, toSL_spec]
    push_cast
    rw [h_slSuccEmbed_GL]
    show (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ) * mapGL ℚ M_X)⁻¹ *
      (mapGL ℚ N_i⁻¹ * (j.out : GL (Fin (k + 2)) ℚ)) = _
    group
  · -- dim-(k+1) fiber mem_H for (σ_i_H, τ_X_H).
    exact slSuccEmbed_H_fiber_transfer_converse a b c ha hb hc _ _
      (slSuccEmbed_block_witnesses_lifted_mem_H a b c ha hb hc i j M_i N_i M_X σ_i τ_X
        h_block_i h_X_block' h_int_conj h_M_X_stab hfib)

/-- **Corrected-representative fiber descent (j-side via X).**
Combine the i-side block witness from `exists_stab_with_block_form_of_fiber`
with the X-side block witness from `exists_stab_with_block_form_of_X_fiber`
plus the integer conjugation identity `M_i · D_a = D_a · N_i` to produce the
dim-(k+1) data `(i_m, j_m, σ_i_H, τ_X_H)` plus:
1. canonical i-side class equality `decompQuot_slSuccEmbed_diagMat a ha i_m = i`;
2. corrected j-side class equality
   `decompQuot_slSuccEmbed_diagMat b hb j_m = ⟦j_corrected⟧` where
   `j_corrected := ⟨mapGL ℚ N_i⁻¹, _⟩ * j.out`;
3. dim-(k+1) fiber set-form for the explicit reps `(σ_i_H, τ_X_H)` of
   `(i_m, j_m)`:
     `{σ_i_H · D_a} * {τ_X_H · D_b} * H_{k+1} = {D_c} * H_{k+1}`.

**Algebraic core.** The dim-(k+2) lifted mem_H expression
`(D_c')⁻¹ · slSuccEmbed_H σ_i_H · D_a' · slSuccEmbed_H τ_X_H · D_b'` simplifies
via the GL-level forms of the i-side and X-side block witnesses to
`((D_c')⁻¹ · i.out · D_a' · j.out · D_b') · (mapGL ℚ M_X-conjugate)`. The
first factor is in `H_{k+2}` by the original fiber condition; the second is in
`H_{k+2}` by `M_X ∈ stab(D_b)`'s GL-image lying in the H subgroup-of-stab.
The product is in `H_{k+2}`, which by `slSuccEmbed_H_fiber_transfer_converse`
descends to the dim-(k+1) mem_H form, and by `fiber_diagMat_iff_mem_H`
to the set-form on `(σ_i_H, τ_X_H)`. The j-side correction `mapGL ℚ N_i⁻¹`
appears in the class equality output (via
`exists_j_m_X_block_class_eq_of_fiber`), but it CANCELS in the dim-(k+2)
mem_H computation through the integer conjugation identity (since
`mapGL M_i · D_a' · mapGL N_i⁻¹ = D_a'`).

**Note on canonical-rep set-form.** The set-form output uses `σ_i_H, τ_X_H`
(specific representatives of `i_m, j_m`), NOT the canonical
`i_m.out, j_m.out`. The joint set-form is rep-DEPENDENT in general, so this
is the strongest statement provable without additional rep-control input
(see the documented dim-2 counterexample at the docstring of
`fiber_has_block_form_preimages`). -/
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

/-- **Set-form left-coset identity gives double-coset membership.**  If the
left-coset set-form fiber identity `{σ·g₁}·{τ·g₂}·H = {d}·H` holds, then the
product `σ·g₁·(τ·g₂)` lies in the double coset `H · d · H`. (`σ·g₁·(τ·g₂)` is in
the left-coset `{d}·H` by reflexivity, hence in the double coset.) -/
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

/-- **Stabilizer-coset shift relating a representative to the canonical out.**
For `σ : (GL_pair n).H`, there is a stabilizer shift `s : (GL_pair n).H` with
`(⟦σ⟧).out = σ · s` (at the GL level) and `g⁻¹ · s · g ∈ H` (the defining
membership of `s` in the `g`-conjugated stabilizer subgroup). This packages
`QuotientGroup.mk_out_eq_mul` for the `decompQuot` relation together with the
unfolded `subgroupOf`/`pointwise_smul` membership of the shift. -/
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

/-- **`mulMap` rep-invariance from a specific-rep set-form.**  If specific
representatives `σ τ : (GL_pair n).H` satisfy the left-coset (set-form) fiber
identity for `(g₁, g₂, d)`, then the rep-invariant `mulMap` value at the
corresponding classes `(⟦σ⟧, ⟦τ⟧)` equals `⟦d⟧` in `HeckeCoset`.

This is the bridge from rep-DEPENDENT set-form predicates (which the corrected
descent helper produces in the form mem_H ↔ set-form for `σ_i_H, τ_X_H`) to the
rep-INVARIANT `mulMap` value (which `heckeMultiplicityMulMap` consumes).

The proof technique mirrors the inline computation inside
`HeckeRing.mem_mulSupport_of_product_mem`: extract the stabilizer-coset shifts
relating `σ` to `(⟦σ⟧).out` (via `QuotientGroup.mk_out_eq_mul`), absorb the
shift into the H-flanks of the double coset, and conclude via
`HeckeCoset.doubleCoset_eq_of_mem`. -/
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

/-- **Corrected-j mulMap-form descent, EXPLICIT-input.**

Same as `fiber_block_form_preimage_corrected_j_mulMap` but parameterized by
explicit i-side block witnesses `(M_i, σ_i, N_i, h_block_i, h_stab_i, h_int_conj)`.
Returns the dim-(k+1) class pair `(i_m, j_m)` plus canonical i-side class
equality, **corrected** j-side class equality (with caller's `N_i⁻¹`-twist),
and the rep-invariant `mulMap` evaluation `mulMap ⟨i_m, j_m⟩ = ⟦D_c_(k+1)⟧`.

This is the final step in the explicit-parameter Route A chain.  Combined
with i-only `Classical.choose` extraction of `(M_i, σ_i, N_i)` at the call
site, the output's corrected j-class equality references the i-functional
`N_i`, exactly the form consumed by
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`'s
`h_iFunctional` hypothesis. -/
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
  have h_set := (fiber_diagMat_iff_mem_H a b c ha hb hc σ_i_H τ_X_H).mpr h_fiber
  have h_dval_a : ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) a := diagMat_delta_val (k + 1) a ha
  have h_dval_b : ((diagMat_delta (k + 1) b : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) b := diagMat_delta_val (k + 1) b hb
  have h_dval_c : ((diagMat_delta (k + 1) c : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) c := diagMat_delta_val (k + 1) c hc
  exact mulMap_eq_of_setForm_specific_reps
    (diagMat_delta (k + 1) a) (diagMat_delta (k + 1) b)
    (diagMat_delta (k + 1) c) σ_i_H τ_X_H
    (by simp only [h_dval_a, h_dval_b, h_dval_c]; exact h_set)

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

/-- **GL-level reduction for the witness-specific j.out-conjugated b-stabilizer
(T192 helper).**

Given the GL-level fiber equation `i.out · D_a · j.out · D_b = D_c · mapGL ν`,
the GL-level integer-conjugate identity `D_a · mapGL N_i = mapGL M_i · D_a`,
and the c-stabilizer condition
`D_c⁻¹ · (i.out · mapGL M_i · i.out⁻¹) · D_c ∈ H`,
deduce the j.out-conjugated b-stabilizer condition that
`fiber_block_form_preimage_canonical_j_witness_specific` consumes:
```
D_b⁻¹ · (j.out⁻¹ · mapGL N_i · j.out) · D_b ∈ H.
```

**Proof idea.** From `h_fib_GL` derive
`D_b⁻¹ · j.out⁻¹ = (mapGL ν)⁻¹ · D_c⁻¹ · i.out · D_a` and the matching
`j.out · D_b = D_a⁻¹ · i.out⁻¹ · D_c · mapGL ν`. Substituting into the goal
collapses (via `D_a · mapGL N_i · D_a⁻¹ = mapGL M_i` from `h_int_conj_GL`) to
`(mapGL ν)⁻¹ · (D_c⁻¹ · (i.out · mapGL M_i · i.out⁻¹) · D_c) · mapGL ν`,
which lies in `H` by `h_iMi_c_stab` plus subgroup closure
(since `mapGL ν ∈ H`).

This isolates the remaining substantive arithmetic into the c-stabilizer
hypothesis `h_iMi_c_stab`; the GL-level chain of substitutions is mechanical.
The reduction does **not** prove `h_iMi_c_stab` itself — that is the precise
remaining out-of-T001-scope arithmetic input
(`A_i · mapGL M_i · A_i⁻¹ ∈ stab(D_c)`, requiring SNF/multi-modular Bezout
infrastructure flagged in the architectural-blocker docblock below). -/
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
  have h_ν_inv_in_H : ν_g⁻¹ ∈ (GL_pair (k + 2)).H :=
    (GL_pair (k + 2)).H.inv_mem h_ν_in_H
  exact (GL_pair (k + 2)).H.mul_mem
    ((GL_pair (k + 2)).H.mul_mem h_ν_inv_in_H h_iMi_c_stab) h_ν_in_H

/-- **T193 chain consumer: witness-specific b-stabilizer from the c-stab
hypothesis.**

Combines the three T192/T193 bridges (`hfib_GL_eq`, `h_int_conj_GL_of_int_mat`,
`jout_conj_N_i_stab_of_iMi_c_stab`) and `exists_stab_with_block_form_of_X_fiber`
into a single conditional consumer: given the universal c-stab hypothesis on
the i.out-conjugate of any `M_i ∈ SL(ℤ)`, produce an `N_i` and the
witness-specific j.out-conjugated b-stabilizer condition consumed by
`fiber_block_form_preimage_canonical_j_witness_specific`.

This isolates the sole remaining substantive obligation
(`h_iMi_c_stab : ∀ M_i, ...`) and demonstrates the three bridges chain
mechanically through the corrected-j route. The `h_iMi_c_stab` quantifier
captures the exact "for the specific M_i extracted by
`exists_stab_with_block_form_of_X_fiber`" semantics — instantiation at the
extracted M_i is the only consumer-side step.

The `h_iMi_c_stab` obligation itself remains the SNF/multi-modular Bezout
arithmetic flagged in the architectural-blocker docblock at lines 8617-8623,
out of T001 prototype scope. -/
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

/-- **T001 Layer 2 witness-specific bridge — corrected j-class upgrades to
canonical for a specific `(N_i, i_m, j_m)` tuple.**

Takes the explicit corrected-j tuple `(N_i, i_m, j_m)` as already produced by
`fiber_block_form_preimage_corrected_j_mulMap`, plus the **single witness-specific
hypothesis** that the j.out-conjugation of `mapGL ℚ N_i` is in the b-stabilizer.
Returns the canonical (i_m, j_m) package with full canonical class equalities
and `mulMap = ⟦diagMat_delta (k+1) c⟧`.

**Why witness-specific.**  The naive bare claim "if `N_i⁻¹` satisfies the
b-stabilizer condition" is mathematically incorrect: the canonical equality
`decompQuot_slSuccEmbed_diagMat b hb j_m = j` reduces (via `Quotient.sound` +
`mem_diagMat_cons_stabilizer_subgroupOf_iff`) to
`D_b⁻¹ · (j.out⁻¹ · mapGL ℚ N_i · j.out) · D_b ∈ H`, which is the j.out-twisted
form (subgroupOf D_b is not normal in H, so bare N_i stabilizer does not give
this).  This lemma exposes the precise required form as a single hypothesis;
the **universal-in-N_i version** (rejected by manager) was too strong.

**Use site (T001 ≤ direction).**  Combined with
`fiber_block_form_preimage_corrected_j_mulMap`, this gives the canonical
`(i_m, j_m)` + `mulMap` package needed by `heckeMultiplicity_block_embed_le_diagMat`.
The remaining T001 deliverable becomes producing the j.out-conjugated stabilizer
hypothesis for the **specific N_i** returned by the corrected descent — which
is a witness-specific algebraic fact derivable (in principle) from the
`D_a · N_i = M_i · D_a` integer-conjugate identity (`h_int_conj` in the
corrected_j output) plus the fiber equation. -/
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
  let _ := a
  let _ := ha
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

/-- **T001 Layer 2 sufficiency consumer — existential j.out-conjugated stabilizer.**

Combines `fiber_block_form_preimage_corrected_j_mulMap` with the witness-specific
bridge `fiber_block_form_preimage_canonical_j_witness_specific` under the
existential premise `∃ N_i ..., (corrected output for N_i) ∧ (j.out-conjugated
stabilizer for N_i)`.

This phrases the rep-control bridge as an existential rather than a universal:
the hypothesis only needs to hold for the specific N_i produced by the corrected
descent, not for all N_i.  If a future worker can produce that single
witness-specific stabilizer (e.g. via the `D_a · N_i = M_i · D_a` integer-conjugate
identity and the fiber equation), this consumer immediately yields the canonical
`(i_m, j_m)` + `mulMap` package.

The hypothesis form `∃ N_i, (the corrected_j_mulMap output package for THAT N_i)
∧ (j.out-conj stab for THAT N_i)` is the **smallest sufficient existential
form** for the ≤ direction. -/
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

/-- **i-side class-preimage bridge.** From `exists_stab_with_block_form_of_fiber`
(which produces `M ∈ stab` and `σ_m ∈ SL_(k+1)(ℤ)` with
`toSL i.out * M = slSuccEmbed σ_m`), construct the dim-(k+1) quotient class
`i_m := ⟦σ_m_H⟧` and prove `decompQuot_slSuccEmbed_diagMat a ha i_m = i`. The
proof shows the equivalence `slSuccEmbed_H σ_m_H ≈ i.out` reduces to the
in-stabilizer condition for `M⁻¹`, which follows from `M ∈ stab` plus subgroup
closure under inverses. -/
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

/-- **Joint i/j class-preimage helper.** Symmetrising the i-side bridge
`exists_i_m_block_class_eq_of_fiber`, given block witnesses on BOTH sides
(`M_i, σ_m` for `i.out` and `M_j, τ_m` for `j.out`), produce the dim-(k+1)
quotient classes `i_m := ⟦σ_m_H⟧, j_m := ⟦τ_m_H⟧` that satisfy the two
`decompQuot_slSuccEmbed_diagMat` class equalities of
`fiber_has_block_form_preimages`. This is strictly stronger than the i-side-only
result: it produces both sides in a single sorry-free reduction.

The third conjunct of `fiber_has_block_form_preimages` (the lifted dim-(k+2)
mem_H for `slSuccEmbed_H i_m.out, slSuccEmbed_H j_m.out`) is NOT derivable from
independent i-side and j-side block witnesses because of a fundamental rep
dependence of the lifted mem_H expression under `Quotient.out`: replacing
`σ_m_H` with the canonical `i_m.out` introduces a stab_a (dim-(k+1)) factor
`t = σ_m_H⁻¹ * i_m.out` that, when transported through `D_a`, `slSuccEmbed_H τ_m_H`,
`D_b`, requires `σ_m_H * t * σ_m_H⁻¹ ∈ stab_c (dim-(k+1))`. For arbitrary
`(σ_m, τ_m, M_i, M_j)` this conjugation-into-stab_c condition fails (since
stab_a and stab_c differ when `a ≠ c`). The full lifted mem_H requires a
genuinely coordinated Smith-NF-style construction that simultaneously controls
the rep-difference behavior — this is the residual algebra blocker for
`fiber_has_block_form_preimages`. -/
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
      decompQuot_slSuccEmbed_diagMat b hb j_m = j := by
  exact ⟨⟦⟨mapGL ℚ σ_m, coe_mem_SLnZ (k + 1) σ_m⟩⟧, ⟦⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩⟧,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block a ha i M_i σ_m h_block_i h_stab_i,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block b hb j M_j τ_m h_block_j h_stab_j⟩

/-- **Existential-rep form of `fiber_has_block_form_preimages`.** Given the
joint block witnesses (i-side and j-side together) AND the dim-(k+1) integer
matrix equation `h_joint`, produces `(i_m, j_m)` plus EXPLICIT existential
representatives `(rep_i = σ_m_H, rep_j = τ_m_H)` in the dim-(k+1) classes
satisfying the lifted dim-(k+2) mem_H for the SPECIFIC reps `σ_m_H, τ_m_H`
(not `Quotient.out i_m, Quotient.out j_m`).

This is strictly stronger than `fiber_class_preimages_from_joint_block_witnesses`
(which only produces the two class equalities) and is a clean reduction of
`fiber_has_block_form_preimages` to the **rep-control bridge** —
the precise named missing piece needed to bridge from `σ_m_H, τ_m_H` reps to
canonical `Quotient.out` reps. Specifically, the only remaining gap is:
given lifted mem_H for `(slSuccEmbed_H σ_m_H, slSuccEmbed_H τ_m_H)`, derive
lifted mem_H for `(slSuccEmbed_H i_m.out, slSuccEmbed_H j_m.out)` where
`i_m = ⟦σ_m_H⟧, j_m = ⟦τ_m_H⟧`. This bridge is rep-dependent under
`Quotient.out` and refuted by the dim-2 counterexample at
`a = (1, 4), c = (1, 8), t = [[1, 0], [4, 1]]` (Round 4 analysis), so it
genuinely requires either a coordinated Smith-NF construction or a refactor
of the abstract `heckeMultiplicity` to use existential reps. -/
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
    with hσ_m_H_def
  set τ_m_H : (GL_pair (k + 1)).H := ⟨mapGL ℚ τ_m, coe_mem_SLnZ (k + 1) τ_m⟩
    with hτ_m_H_def
  refine ⟨⟦σ_m_H⟧, ⟦τ_m_H⟧, σ_m_H, τ_m_H, rfl, rfl,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block a ha i M_i σ_m h_block_i h_stab_i,
    decompQuot_slSuccEmbed_diagMat_mk_eq_of_block b hb j M_j τ_m h_block_j h_stab_j, ?_⟩
  -- The lifted dim-(k+2) mem_H for (slSuccEmbed_H σ_m_H, slSuccEmbed_H τ_m_H).
  exact slSuccEmbed_H_fiber_transfer a b c ha hb hc σ_m_H τ_m_H h_joint

/-- **Combinatorial core of Shimura L.3.19**: every fiber pair at dim `k+2` with
`Fin.cons 1 _` diagonals has dim-`k+1` class preimages under the
`decompQuot_slSuccEmbed_diagMat` block embedding, and moreover the lifted
mem_H condition at dim `k+2` holds for `slSuccEmbed_H i_m.out` and
`slSuccEmbed_H j_m.out`. The lifted mem_H is exactly what
`slSuccEmbed_H_fiber_transfer_converse` consumes, so
`fiber_block_form_preimage` reduces cleanly to this helper plus a single
application of the converse fiber transfer.

The hypothesis `hk : 1 ≤ k` is required: at `k = 0` (dim 2 → dim 1) the
conclusion is mathematically false — explicit counterexample
`A_i = [[1, 0], [2, 1]]`, `A_j = [[1, 0], [1, 1]]`, `ν = [[1, 0], [1, 1]]`,
`a = b = (2)`, `c = (4)` satisfies `hfib` but `[A_j] ≠ [I]` in `SL(2, ℤ) / Γ_0(2)`
while the only image of `decompQuot_slSuccEmbed_diagMat` from the trivial
dim-1 quotient is `[I]`. The downstream user
`heckeMultiplicity_block_embed` imposes `2 ≤ m`, which forces `k ≥ 1`. -/
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

/-- `fiber_block_form_preimage` follows from `fiber_has_block_form_preimages`:
the first two conjuncts are the class-match identities, and the third (dim-`k+1`
fiber condition) follows by applying `slSuccEmbed_H_fiber_transfer_converse`
to the lifted mem_H hypothesis and re-packaging via `fiber_diagMat_iff_mem_H`.
Inherits the `hk : 1 ≤ k` restriction from `fiber_has_block_form_preimages`. -/
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
  have h_k1_mem := slSuccEmbed_H_fiber_transfer_converse a b c ha hb hc
    i_m.out j_m.out h_lifted
  have h_dval_a : ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) a := diagMat_delta_val (k + 1) a ha
  have h_dval_b : ((diagMat_delta (k + 1) b : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) b := diagMat_delta_val (k + 1) b hb
  have h_dval_c : ((diagMat_delta (k + 1) c : (GL_pair (k + 1)).Δ) :
      GL (Fin (k + 1)) ℚ) = diagMat (k + 1) c := diagMat_delta_val (k + 1) c hc
  simpa only [h_dval_a, h_dval_b, h_dval_c] using
    (fiber_diagMat_iff_mem_H a b c ha hb hc i_m.out j_m.out).mpr h_k1_mem

end HeckeRing.GLn
