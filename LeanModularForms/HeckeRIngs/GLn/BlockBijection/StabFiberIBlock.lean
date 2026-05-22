/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.TrailingHNF

/-!
# Block Embedding Bijection: stabilizer and fiber block-form lemmas (i-side block reduction)
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

/-- **Sorry-free translation helper for the dim-`(k+2)` stabilizer subgroup.**
Membership of `σ : (GL_pair (k+2)).H` in the abstract `subgroupOf`-style
stabilizer for `diagMat_delta (k+2) (Fin.cons 1 a)` is equivalent to the concrete
matrix-conjugation condition `D⁻¹ * σ * D ∈ (GL_pair (k+2)).H` (where
`D = diagMat (k+2) (Fin.cons 1 a)`).  This bridges the `decompQuot` quotient
representation (used by `fiber_has_block_form_preimages` in its hypothesis
on `i.out`, `j.out`) and the matrix-conjugation form consumed by
`slSuccEmbed_H_fiber_transfer` and `slSuccEmbed_H_stab_diagMat`.  The proof is
just unfolding `Subgroup.mem_subgroupOf` and the pointwise smul / `ConjAct`
definitions, then identifying the two diagonal forms via `diagMat_delta_val`. -/
lemma mem_diagMat_cons_stabilizer_subgroupOf_iff {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (σ : (GL_pair (k + 2)).H) :
    σ ∈ (ConjAct.toConjAct ((diagMat_delta (k + 2) (Fin.cons 1 a) :
            (GL_pair (k + 2)).Δ) : GL (Fin (k + 2)) ℚ) • (GL_pair (k + 2)).H).subgroupOf
          (GL_pair (k + 2)).H ↔
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (σ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [show ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
        GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) from
      diagMat_delta_val (k + 2) (Fin.cons 1 a) (cons_one_pos ha)]

/-- **Integer-level conjugation identity for a `Fin.cons 1 _`-stabilizer SL matrix.**
Given `M : SL_(k+2)(ℤ)` whose `mapGL ℚ`-image lies in the diag-conjugation stabilizer of
`Fin.cons 1 a` (i.e., `D⁻¹ * mapGL ℚ M * D ∈ (GL_pair (k+2)).H` where
`D = diagMat (k+2) (Fin.cons 1 a)`), there exists an integer SL matrix `N : SL_(k+2)(ℤ)`
satisfying the integer-matrix identity
`Matrix.diagonal (Fin.cons 1 a · ↑) * N.val = M.val * Matrix.diagonal (Fin.cons 1 a · ↑)`.

This is the integer-level translation of the stabilizer condition: the GL-conjugation
`D⁻¹ * (mapGL ℚ M) * D = mapGL ℚ N` is equivalent to `D * mapGL ℚ N = mapGL ℚ M * D` in
`GL (Fin (k+2)) ℚ`, which descends to an integer-matrix identity `D · N = M · D` (no
rational `D⁻¹` factor). It is the natural input for any subsequent algebraic substitution
of the i-side / j-side block-form factor `M` into the integer matrix equation
`A_i · D_a · A_j · D_b = D_c · ν` produced by `hfib_int_mat_eq`, since the stab condition
on `M` lets us replace `M⁻¹ · D_a` by `D_a · N⁻¹` (a corollary at integer level via
`M⁻¹ · D = D · N⁻¹` from this identity).

Reusable helper for any future j-side or coordinated rep-construction work that needs
to rewrite a stab-conjugated factor as a left- or right-diagonal-times-integer-SL form. -/
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
  have hcons_pos : ∀ j, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) j := cons_one_pos ha
  have h_GL_eq : diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N : GL (Fin (k + 2)) ℚ) =
      (mapGL ℚ M : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
    rw [hN]; group
  have h_mat := congr_arg
    (fun g : GL (Fin (k + 2)) ℚ ↦ (g : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)) h_GL_eq
  simp only [Units.val_mul] at h_mat
  have h_N : ((mapGL ℚ N : GL _ ℚ) : Matrix _ _ ℚ) = N.1.map (algebraMap ℤ ℚ) := rfl
  have h_M : ((mapGL ℚ M : GL _ ℚ) : Matrix _ _ ℚ) = M.1.map (algebraMap ℤ ℚ) := rfl
  have h_D : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        ((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_pos,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  rw [h_N, h_M, h_D] at h_mat
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h_mat
  exact (Matrix.map_injective (algebraMap ℤ ℚ).injective_int h_mat)

/-- **Sorry-free first-column divisibility extraction from the `Fin.cons 1 _`
stabilizer condition.**  If `σ : (GL_pair (k+2)).H` lies in the
`subgroupOf`-style stabilizer for `diagMat_delta (k+2) (Fin.cons 1 a)`, then the
underlying integer matrix `toSL σ` has its first column entries (below row 0)
divisible by the chain `a` — concretely, `a i ∣ (toSL σ) (i.succ) 0` for every
`i : Fin (k+1)`.  This is exactly the `hw_col_div` hypothesis required by
`sl_exists_col_stab_divChain`, so combining this lemma with
`mem_diagMat_cons_stabilizer_subgroupOf_iff` lets a stabilizer-element `σ`
feed directly into the SL-stabilizer-existence machinery used by the
column-HNF iteration.

Proof:  `mem_diagMat_cons_stabilizer_subgroupOf_iff` rewrites the abstract
membership to `D⁻¹ * σ * D ∈ (GL_pair (k+2)).H`, hence equal to `mapGL ℚ N`
for some `N : SL_(k+2)(ℤ)`.  Multiplying by `D` on the left gives the matrix
identity `D * mapGL N = σ * D`; reading off the `(i.succ, 0)` entry uses the
diagonal structure of `D` to collapse the sums to
`(a i : ℚ) * (N.val (i.succ) 0 : ℚ) = ((toSL σ).val (i.succ) 0 : ℚ)`, after
which integer divisibility is `exact_mod_cast`. -/
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
  have hcons_pos : ∀ j, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) j := cons_one_pos ha
  have h_GL_eq :
      diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N) =
      (σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) := by
    rw [hN]; group
  have h_entry :
      ((diagMat (k + 2) (Fin.cons 1 a)).val *
        (mapGL ℚ N).val : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ) i.succ 0 =
      ((σ : GL (Fin (k + 2)) ℚ).val *
        (diagMat (k + 2) (Fin.cons 1 a)).val : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)
          i.succ 0 := by
    have h_units := congr_arg Units.val h_GL_eq
    simp only [Units.val_mul] at h_units
    exact congrFun (congrFun h_units i.succ) 0
  rw [diagMat_val _ _ hcons_pos, Matrix.diagonal_mul, Matrix.mul_diagonal] at h_entry
  have hcons_succ : ((Fin.cons 1 a : Fin (k + 2) → ℕ) i.succ : ℚ) = (a i : ℚ) := by
    simp [Fin.cons_succ]
  have hcons_zero : ((Fin.cons 1 a : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℚ) = 1 := by
    simp [Fin.cons_zero]
  rw [hcons_succ, hcons_zero, mul_one, mapGL_coe_matrix] at h_entry
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, algebraMap_int_eq, eq_intCast] at h_entry
  have h_toSL_val :
      ((toSL σ).val i.succ 0 : ℚ) = (σ : GL (Fin (k + 2)) ℚ).val i.succ 0 := by
    have h_units := congr_arg Units.val (toSL_spec σ)
    rw [mapGL_coe_matrix] at h_units
    have := congrFun (congrFun h_units i.succ) 0
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, algebraMap_int_eq, eq_intCast] at this
    exact this
  rw [← h_toSL_val] at h_entry
  exact_mod_cast h_entry.symm

/-- **Sorry-free `i`-side stabilizer SL matrix from the fiber relation.**
Given the fiber condition `hfib` and a positive divisor chain `a` (`hda`), the
chain-divisibility of `(toSL i.out)⁻¹`'s first column (provided by
`hfib_col_div_a`) plus its primitivity (provided by `sl_first_col_primitive`,
since `(toSL i.out)⁻¹ ∈ SL_(k+2)(ℤ)`) feeds directly into
`sl_exists_col_stab_divChain` to produce an `M : SL_(k+2)(ℤ)` satisfying:
  * `M.1 r 0 = ((toSL i.out)⁻¹).1 r 0` for every `r : Fin (k + 2)` — `M`'s
    first column matches the inverse-column we want to absorb;
  * `D⁻¹ * mapGL ℚ M * D ∈ (GL_pair (k+2)).H` — `M` lies in the
    `Fin.cons 1 a` diagonal-conjugation stabilizer.

This is the right-multiplication factor for the i-side block-form
decomposition: `(toSL i.out) * M` has first column equal to
`(toSL i.out) * ((toSL i.out)⁻¹).1 _ 0 = e_0`, the first step of the block
form `1 ⊕ σ_m`.  Sorry-free because every input has been previously closed. -/
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
  have h_div := hfib_col_div_a a b c ha hb hc i j hfib
  set w : Fin (k + 2) → ℤ :=
    fun r ↦ ((toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 with hw_def
  have hw_primitive : ∀ d : ℤ, (∀ r, d ∣ w r) → IsUnit d :=
    fun d hd ↦ sl_first_col_primitive (toSL i.out)⁻¹ d hd
  have hw_col_div : ∀ i' : Fin (k + 1), (a i' : ℤ) ∣ w i'.succ := h_div
  exact sl_exists_col_stab_divChain a ha hda w hw_primitive hw_col_div

/-- **First-column-`e_0` reduction of `i.out` from the fiber relation.**  Given
the fiber condition `hfib`, there exists a stabilizer SL matrix `M` (built from
`exists_stab_with_inv_first_col_of_fiber`) such that `(toSL i.out) * M` has
first column equal to `e_0` (i.e., the first column of the identity matrix):
`(toSL i.out * M).1 r 0 = (1 : Matrix _ _ ℤ) r 0` for every `r : Fin (k + 2)`.

Direct computation: `M`'s first column matches `(toSL i.out)⁻¹`'s first
column, so `(toSL i.out * M)`'s first column equals
`(toSL i.out * (toSL i.out)⁻¹)`'s first column = `(1 : SL).1`'s first
column = the first standard basis vector.  This is the second step of the
i-side block-form decomposition (after the stabilizer-extraction step
`exists_stab_with_inv_first_col_of_fiber`); the next step is clearing the
first row of `toSL i.out * M` by upper transvections (which are automatically
in the stabilizer, since their only non-identity entry sits in the
strict-upper triangle). -/
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
  refine ⟨M, ?_, hM_stab⟩
  intro r
  have h_to_inv :
      (toSL i.out * M : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 =
      (toSL i.out * (toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r 0 := by
    simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl (fun k _ ↦ ?_)
    rw [hM_col k]
  rw [h_to_inv, mul_inv_cancel, SpecialLinearGroup.coe_one]

/-- **Transvection at `(0, l.succ)` lies in the diag-conjugation stabilizer**
for diagonals of the form `Fin.cons 1 a`. Conjugation by `diag` sends a
transvection with donor row `0` to another integer transvection (the constant
`c` is multiplied by `a_l`), so the conjugate is automatically in
`SLnZ_subgroup`. This is the "upper-row transvection stays integer" fact used
when clearing the first row of a matrix that already has first column equal to
the first standard basis vector. -/
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
  · -- (cons 1 a) 0 = 1, so the LHS divisor is 1.
    subst hi
    show ((Fin.cons 1 a : Fin (k + 2) → ℕ) 0 : ℤ) ∣ _
    simp
  · -- i' ≠ 0: the c contribution at entry (i', j') vanishes (it requires `0 = i'`).
    have h_no_c : ¬ (0 = i' ∧ l.succ = j') := fun ⟨h0, _⟩ ↦ hi h0.symm
    have h_entry :
        (slTransvecG (0 : Fin (k + 2)) l.succ (Fin.succ_ne_zero l).symm c).1 i' j' =
          if i' = j' then 1 else 0 := by
      show (Matrix.transvection (0 : Fin (k + 2)) l.succ c) i' j' = _
      simp [Matrix.transvection, Matrix.one_apply, h_no_c]
    rw [h_entry]
    by_cases h_diag : i' = j'
    · subst h_diag
      simp
    · simp [h_diag]

/-- **Row-clearance via upper transvections** with stabilizer membership.
Given a matrix `W ∈ SL(k+2, ℤ)` whose first column equals `e₀` and a finset
`S : Finset (Fin (k+1))` of "columns to clear", produce a transvection product
`T ∈ SL(k+2, ℤ)` such that `W * T` keeps column `0` fixed, zeroes the
`(0, l.succ)` entry for every `l ∈ S`, leaves other first-row entries
unchanged, leaves the bottom-right `(k+1) × (k+1)` block unchanged, and
satisfies the diag-conjugation stabilizer condition. The proof inducts on `S`
using `slTransvec_zero_succ_stab` for stabilizer closure. -/
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
  have h_col0_zero : W.1 0 0 = 1 := by
    have h := h_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have h_col0_succ_zero : ∀ r' : Fin (k + 1), W.1 r'.succ 0 = 0 := by
    intro r'
    have h := h_col0 r'.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero r')] at h
    exact h
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_, ?_, ?_, ?_⟩
      · intro r; simp
      · intro l hl; exact absurd hl (Finset.notMem_empty _)
      · intro l _; simp
      · intro i j; simp
      · -- 1 conjugated by anything is 1, in H trivially
        show (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ (1 : SpecialLinearGroup (Fin (k + 2)) ℤ) : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H
        rw [map_one, mul_one, inv_mul_cancel]
        exact one_mem _
  | insert l₀ S' hl₀_notin ih =>
      obtain ⟨T', hT'_col0, hT'_S, hT'_outside, hT'_block, hT'_stab⟩ := ih
      set c_l₀ : ℤ := -(W.1 0 l₀.succ) with hc_l₀_def
      set T_l₀ : SpecialLinearGroup (Fin (k + 2)) ℤ :=
        slTransvecG (0 : Fin (k + 2)) l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ with hT_l₀_def
      have h_WT'_00 : (W * T').1 0 0 = 1 := by rw [hT'_col0 0]; exact h_col0_zero
      refine ⟨T' * T_l₀, ?_, ?_, ?_, ?_, ?_⟩
      · -- column 0 still W's column 0
        intro r
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def,
          sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') r
              (Fin.succ_ne_zero l₀).symm]
        exact hT'_col0 r
      · -- Columns in `insert l₀ S'` are cleared.
        intro l hl
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def]
        obtain h_eq | hl_S' := Finset.mem_insert.mp hl
        · -- After `subst h_eq` (h_eq : l = l₀), `l₀` is replaced by `l` everywhere.
          subst h_eq
          rw [sl_addCol_target_col 0 l.succ (Fin.succ_ne_zero l).symm c_l₀ (W * T') 0,
            hT'_outside l hl₀_notin, h_WT'_00]
          show W.1 0 l.succ + c_l₀ * 1 = 0
          rw [hc_l₀_def]; ring
        · have hl_ne_l₀ : l ≠ l₀ := fun h ↦ hl₀_notin (h ▸ hl_S')
          have hsucc_ne : l.succ ≠ l₀.succ := fun h ↦ hl_ne_l₀ (Fin.succ_injective _ h)
          rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') 0
              hsucc_ne]
          exact hT'_S l hl_S'
      · intro l hl_notin
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def]
        have hl_ne_l₀ : l ≠ l₀ := fun h ↦ hl_notin (h ▸ Finset.mem_insert_self _ _)
        have hl_notin_S' : l ∉ S' := fun h ↦ hl_notin (Finset.mem_insert_of_mem h)
        have hsucc_ne : l.succ ≠ l₀.succ := fun h ↦ hl_ne_l₀ (Fin.succ_injective _ h)
        rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') 0
            hsucc_ne]
        exact hT'_outside l hl_notin_S'
      · intro i' j'
        rw [show W * (T' * T_l₀) = (W * T') * T_l₀ from (mul_assoc _ _ _).symm, hT_l₀_def]
        by_cases h_eq : j'.succ = l₀.succ
        · -- j'.succ = l₀.succ → j' = l₀ by injectivity, substitute first.
          have hj'_eq : j' = l₀ := Fin.succ_injective _ h_eq
          subst hj'_eq
          rw [sl_addCol_target_col 0 j'.succ (Fin.succ_ne_zero j').symm c_l₀ (W * T') i'.succ]
          have hcol0_succ : (W * T').1 i'.succ 0 = 0 := by
            rw [hT'_col0 i'.succ]; exact h_col0_succ_zero i'
          rw [hcol0_succ, mul_zero, add_zero]
          exact hT'_block i' j'
        · rw [sl_addCol_preserves_col 0 l₀.succ (Fin.succ_ne_zero l₀).symm c_l₀ (W * T') i'.succ
              h_eq]
          exact hT'_block i' j'
      · -- Stabilizer: factor through map_mul.
        have h_T_l₀_stab : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
            (mapGL ℚ T_l₀ : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
          rw [hT_l₀_def]
          exact slTransvec_zero_succ_stab a ha l₀ c_l₀
        have h_split : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
            (mapGL ℚ (T' * T_l₀) : GL (Fin (k + 2)) ℚ) *
            diagMat (k + 2) (Fin.cons 1 a) =
            ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
              (mapGL ℚ T' : GL (Fin (k + 2)) ℚ) *
              diagMat (k + 2) (Fin.cons 1 a)) *
            ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
              (mapGL ℚ T_l₀ : GL (Fin (k + 2)) ℚ) *
              diagMat (k + 2) (Fin.cons 1 a)) := by
          rw [map_mul]; group
        rw [h_split]
        exact mul_mem hT'_stab h_T_l₀_stab

/-- **i-side block-form witness from the fiber.** Combining
`exists_stab_with_first_col_e0_of_fiber` with `sl_first_row_clear_with_col0_e0`,
produce `M ∈ SL(k+2, ℤ)` in the diag-conjugation stabilizer and
`σ_m ∈ SL(k+1, ℤ)` such that `toSL i.out * M = slSuccEmbed σ_m`. This is the
i-side bridge: it identifies `i.out` (modulo stabilizer) with the
block-embedding image of a dim-(k+1) class. -/
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
  obtain ⟨T_clear, hT_col0, hT_S, _, _, hT_stab⟩ :=
    sl_first_row_clear_with_col0_e0 a ha (toSL i.out * M_0) hM_0_col Finset.univ
  set M : SpecialLinearGroup (Fin (k + 2)) ℤ := M_0 * T_clear with hM_def
  set N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (toSL i.out * M).1 with hN_def
  have hM_assoc : toSL i.out * M = (toSL i.out * M_0) * T_clear := by
    rw [hM_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (toSL i.out * M).1 r 0 = _
    rw [hM_assoc, hT_col0 r]
    exact hM_0_col r
  have hN_row0 : ∀ l : Fin (k + 1), N 0 l.succ = 0 := by
    intro l
    show (toSL i.out * M).1 0 l.succ = _
    rw [hM_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N 0 0 = 1 := by
    have h := hN_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have hN_succ0 : ∀ I : Fin (k + 1), N I.succ 0 = 0 := by
    intro I
    have h := hN_col0 I.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
    exact h
  set σ_m_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N I.succ J.succ with hσ_raw_def
  have h_det : σ_m_raw.det = 1 := by
    have h_det_N : N.det = 1 := by
      rw [hN_def]; exact (toSL i.out * M).2
    rw [Matrix.det_succ_row_zero] at h_det_N
    rw [Fin.sum_univ_succ] at h_det_N
    have h_zero_terms :
        ∀ j : Fin (k + 1),
          (-1 : ℤ) ^ (j.succ : ℕ) * N 0 j.succ *
            (N.submatrix Fin.succ j.succ.succAbove).det = 0 := by
      intro j
      rw [hN_row0 j]; ring
    rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero, hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    have h_submat : N.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = σ_m_raw := by
      ext I J
      show N I.succ ((0 : Fin (k + 2)).succAbove J) = σ_m_raw I J
      rw [Fin.succAbove_zero]
    rw [h_submat] at h_det_N
    exact h_det_N
  set σ_m : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨σ_m_raw, h_det⟩ with hσ_def
  refine ⟨M, σ_m, ?_, ?_⟩
  · apply Subtype.ext
    ext I J
    show N I J = (slSuccEmbed σ_m).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · -- (0, 0)
        rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'
        rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'
        rw [slSuccEmbed_val_succ_succ]
  · -- Stabilizer: M = M_0 * T_clear, both in stabilizer.
    have h_split : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ M : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) =
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ M_0 : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a)) *
        ((diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
          (mapGL ℚ T_clear : GL (Fin (k + 2)) ℚ) *
          diagMat (k + 2) (Fin.cons 1 a)) := by
      rw [hM_def, map_mul]; group
    rw [h_split]
    exact mul_mem hM_0_stab hT_stab

/-- **Substituted integer matrix equation via the i-side block form, EXPLICIT-input form.**

Same algebraic content as `fiber_int_mat_eq_via_i_block` but parameterized by
explicit i-side block witnesses `(M_i, σ_i, h_block_i, N_i, h_int_conj)`.
Returns just the substituted integer matrix equation
`block(σ_i) · D_a · (N_i⁻¹ · A_j) · D_b = D_c · ν`, where `A_j := toSL j.out`
and `block(σ_i) := slSuccEmbed σ_i`.

**Why the explicit-input form.**  When the caller supplies `(M_i, σ_i, N_i)`
extracted via `Classical.choose` on the **i-only** existentials
`exists_stab_with_block_form_of_fiber` and `exists_stab_int_conjugate_diagMat_cons_one`
(both with i-only existential bodies), Lean 4's proof irrelevance makes those
witnesses i-functional (independent of `(j, hfib)`).  The combined j-dependent
output of `fiber_int_mat_eq_via_i_block` (which packages all four witnesses
σ_i, M_i, N_i, ν into a single existential whose body has j-dependent
conjuncts) does **not** preserve i-functionality through `Classical.choose`,
which is the architectural blocker to closing
`heckeMultiplicity_block_embed_le_diagMat_target_mulMap_via_iFunctional`'s
`h_iFunctional` hypothesis.  Threading explicit i-functional witnesses
through this lemma (and the downstream chain) keeps i-functionality intact.

**Use site.**  Together with the (planned) explicit-input variants of
`_rearr`, `_rearr_adj`, `hfib_col_div_b_via_i_block`,
`fiber_block_form_preimage_corrected_j`, and `_mulMap`, this gives a
parameterized chain whose final mulMap output's `N_i` matches the caller's
i-functional `N_i`. -/
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
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  have h_M_inv_M_val :
      (M_i⁻¹).val * M_i.val = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    show ((M_i⁻¹) * M_i).val = (1 : SpecialLinearGroup (Fin (k + 2)) ℤ).val
    rw [inv_mul_cancel]
  have h_N_N_inv_val :
      N_i.val * (N_i⁻¹).val = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    show (N_i * N_i⁻¹).val = (1 : SpecialLinearGroup (Fin (k + 2)) ℤ).val
    rw [mul_inv_cancel]
  have h_inv_conj : (M_i⁻¹).val * D_a = D_a * (N_i⁻¹).val := by
    have step1 : (M_i⁻¹).val * D_a * N_i.val = D_a := by
      rw [Matrix.mul_assoc, h_int_conj, ← Matrix.mul_assoc, h_M_inv_M_val,
          Matrix.one_mul]
    have step2 :
        (M_i⁻¹).val * D_a * N_i.val * (N_i⁻¹).val = D_a * (N_i⁻¹).val := by
      rw [step1]
    rw [Matrix.mul_assoc, h_N_N_inv_val, Matrix.mul_one] at step2
    exact step2
  have h_block_i_inv : toSL i.out = slSuccEmbed σ_i * M_i⁻¹ := by
    rw [← h_block_i, mul_inv_cancel_right]
  have h_block_i_inv_val : (toSL i.out).val =
      (slSuccEmbed σ_i).val * (M_i⁻¹).val := by
    show ((toSL i.out)).val = ((slSuccEmbed σ_i) * M_i⁻¹).val
    rw [← h_block_i_inv]
  have h_unfold_prod : (N_i⁻¹ * toSL j.out).val =
      (N_i⁻¹).val * (toSL j.out).val := rfl
  rw [h_unfold_prod]
  rw [show (slSuccEmbed σ_i).val * D_a * ((N_i⁻¹).val * (toSL j.out).val) * D_b =
      ((slSuccEmbed σ_i).val * (D_a * (N_i⁻¹).val)) * (toSL j.out).val * D_b from by
    simp only [Matrix.mul_assoc]]
  rw [← h_inv_conj]
  rw [show (slSuccEmbed σ_i).val * ((M_i⁻¹).val * D_a) * (toSL j.out).val * D_b =
      ((slSuccEmbed σ_i).val * (M_i⁻¹).val) * D_a * (toSL j.out).val * D_b from by
    simp only [← Matrix.mul_assoc]]
  rw [← h_block_i_inv_val]
  exact hν

/-- **Substituted integer matrix equation via the i-side block form.**
Combines `exists_stab_with_block_form_of_fiber` (i-side block form),
`exists_stab_int_conjugate_diagMat_cons_one` (integer conjugation
identity), and `hfib_int_mat_eq` (raw integer matrix equation) into a
single packaging that produces:

* the i-side block witnesses `M_i, σ_i` with `toSL i.out * M_i =
  slSuccEmbed σ_i` and `M_i ∈ stab(D_a)`;
* the integer conjugate `N_i` with `D_a · N_i = M_i · D_a`;
* the matrix-equation witness `ν` with the substituted equation
  `block(σ_i) · D_a · (N_i⁻¹ · A_j) · D_b = D_c · ν`,
  where `A_j := toSL j.out` and `block(σ_i) := slSuccEmbed σ_i`.

This is the natural setup for any future j-side block-form construction
(or a coordinated Smith-NF / lattice-descent producing both block witnesses
together): the i-side has been absorbed into the `slSuccEmbed σ_i` factor
on the left, so the j-side construction need only operate on the rest of
the equation. The `N_i⁻¹ · A_j` factor in the substituted equation is the
SL element whose first column controls the j-side col-divisibility
question (the exact next missing arithmetic input — see the docstring at
`fiber_has_block_form_preimages` for the dim-2 counterexample at k = 0
showing the canonical j-side col-divisibility is rep-dependent for k = 0;
the corresponding question at k ≥ 1 remains open and is the named missing
lemma `hfib_col_div_b_via_i_block`).

**Implementation note.** This is now a thin wrapper around
`fiber_int_mat_eq_via_i_block_explicit`: extract `(M_i, σ_i, h_block_i,
h_stab_i)` via `exists_stab_with_block_form_of_fiber`, then `(N_i, h_int_conj)`
via `exists_stab_int_conjugate_diagMat_cons_one`, then call the explicit
form for the substituted matrix equation.  Keeping the existing API
preserves all downstream call sites; the explicit form is used directly
by Route A's i-functional consumers. -/
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

/-- **Adjugate-rearrangement of the substituted integer matrix equation,
EXPLICIT-input.**

Same algebraic content as `fiber_int_mat_eq_via_i_block_rearr` but
parameterized by explicit i-side block witnesses
`(M_i, σ_i, N_i, h_block_i, h_int_conj)`.  Returns just the
adjugate-rearranged equation
`D_a · (N_i⁻¹ · A_j) · D_b · adjugate(ν) = adjugate(slSuccEmbed σ_i) · D_c`,
where `A_j := toSL j.out` and the `ν` witness comes from the substituted
integer matrix equation produced by `fiber_int_mat_eq_via_i_block_explicit`.

**Why the explicit-input form.**  See the docblock at
`fiber_int_mat_eq_via_i_block_explicit` for the architectural rationale
(preserving i-functionality of `(M_i, σ_i, N_i)` through the chain).  This
lemma is the second step in the explicit-parameter chain after the
substituted matrix equation. -/
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
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c_def
  set X : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (N_i⁻¹ * toSL j.out).val
    with hX_def
  have h_adj_block_block :
      Matrix.adjugate (slSuccEmbed σ_i).val * (slSuccEmbed σ_i).val =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    rw [Matrix.adjugate_mul, show (slSuccEmbed σ_i).val.det = 1 from
      (slSuccEmbed σ_i).2, one_smul]
  have h_ν_adj_ν :
      ν.val * Matrix.adjugate ν.val =
        (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) := by
    rw [Matrix.mul_adjugate, show ν.val.det = 1 from ν.2, one_smul]
  have h_premul :
      D_a * X * D_b =
        Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) := by
    have h : Matrix.adjugate (slSuccEmbed σ_i).val *
        ((slSuccEmbed σ_i).val * D_a * X * D_b) =
        Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) := by
      rw [h_subst]
    rw [show Matrix.adjugate (slSuccEmbed σ_i).val *
            ((slSuccEmbed σ_i).val * D_a * X * D_b) =
          (Matrix.adjugate (slSuccEmbed σ_i).val * (slSuccEmbed σ_i).val) *
            D_a * X * D_b from by
        simp only [Matrix.mul_assoc]] at h
    rw [h_adj_block_block, Matrix.one_mul] at h
    exact h
  have h : D_a * X * D_b * Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) *
        Matrix.adjugate ν.val := by
    rw [h_premul]
  rw [show Matrix.adjugate (slSuccEmbed σ_i).val * (D_c * ν.val) *
        Matrix.adjugate ν.val =
      Matrix.adjugate (slSuccEmbed σ_i).val * D_c * (ν.val * Matrix.adjugate ν.val)
      by simp only [Matrix.mul_assoc]] at h
  rw [h_ν_adj_ν, Matrix.mul_one] at h
  exact h

/-- See `fiber_int_mat_eq_via_i_block_rearr_explicit` for the active
explicit-input rearrangement; this is now a thin wrapper that extracts
the i-side block witnesses via `exists_stab_with_block_form_of_fiber` and
`exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
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

/-- **j-side adjugate-rearranged equation, EXPLICIT-input.**

Same algebraic content as `fiber_int_mat_eq_via_i_block_rearr_adj` but
parameterized by explicit i-side block witnesses
`(M_i, σ_i, N_i, h_block_i, h_int_conj)`.  Derives the premultiplied
adjugate-rearranged form
`adjugate(D_b) · adjugate(X.val) · adjugate(D_a) =
  adjugate(ν.val) · adjugate(D_c) · slSuccEmbed σ_i.val`
from the rearranged equation produced by
`fiber_int_mat_eq_via_i_block_rearr_explicit`.

**Why the explicit-input form.**  See the docblock at
`fiber_int_mat_eq_via_i_block_explicit`.  This is the third step in the
explicit-parameter chain after `_rearr_explicit`. -/
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
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c_def
  have hdet_block : (slSuccEmbed σ_i).val.det = 1 := (slSuccEmbed σ_i).2
  have hdet_ν : ν.val.det = 1 := ν.2
  have h_card : Fintype.card (Fin (k + 2)) ≠ 1 := by
    simp [Fintype.card_fin]
  have h_rearr_adj := congr_arg Matrix.adjugate h_rearr
  rw [show Matrix.adjugate (D_a * (N_i⁻¹ * toSL j.out).val * D_b *
        Matrix.adjugate ν.val) =
      Matrix.adjugate (Matrix.adjugate ν.val) *
        (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a)) from by
      rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib,
          Matrix.adjugate_mul_distrib]] at h_rearr_adj
  rw [show Matrix.adjugate (Matrix.adjugate (slSuccEmbed σ_i).val * D_c) =
      Matrix.adjugate D_c *
        Matrix.adjugate (Matrix.adjugate (slSuccEmbed σ_i).val) from by
      rw [Matrix.adjugate_mul_distrib]] at h_rearr_adj
  have h_adj_adj_ν : Matrix.adjugate (Matrix.adjugate ν.val) = ν.val := by
    rw [Matrix.adjugate_adjugate _ h_card, hdet_ν, one_pow, one_smul]
  have h_adj_adj_block :
      Matrix.adjugate (Matrix.adjugate (slSuccEmbed σ_i).val) =
        (slSuccEmbed σ_i).val := by
    rw [Matrix.adjugate_adjugate _ h_card, hdet_block, one_pow, one_smul]
  rw [h_adj_adj_ν, h_adj_adj_block] at h_rearr_adj
  have h_adj_ν_ν : Matrix.adjugate ν.val * ν.val = (1 : Matrix _ _ ℤ) := by
    rw [Matrix.adjugate_mul, hdet_ν, one_smul]
  have h_premul :
      Matrix.adjugate ν.val *
        (ν.val * (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a))) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) := by
    rw [h_rearr_adj]
  rw [show Matrix.adjugate ν.val *
        (ν.val * (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a))) =
      (Matrix.adjugate ν.val * ν.val) *
        (Matrix.adjugate D_b *
          (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a)) from by
      simp only [Matrix.mul_assoc]] at h_premul
  rw [h_adj_ν_ν, Matrix.one_mul] at h_premul
  rw [show Matrix.adjugate D_b *
        (Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
          Matrix.adjugate D_a) =
      Matrix.adjugate D_b *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
        Matrix.adjugate D_a from by
      simp only [Matrix.mul_assoc]] at h_premul
  exact h_premul

/-- See `fiber_int_mat_eq_via_i_block_rearr_adj_explicit` for the active
explicit-input adjugate-rearrangement; this is now a thin wrapper that
extracts the i-side block witnesses via `exists_stab_with_block_form_of_fiber`
and `exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
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

/-- **j-side col-divisibility on `X := N_i⁻¹ · toSL j.out`, EXPLICIT-input.**

Same algebraic content as `hfib_col_div_b_via_i_block` but parameterized by
explicit i-side block witnesses `(M_i, σ_i, N_i, h_block_i, h_int_conj)`.
Returns the substituted matrix equation, the rearranged form, the
adjugate-rearranged form, and the col-divisibility
`∀ r : Fin (k + 1), (b r : ℤ) ∣ (X⁻¹).val r.succ 0`, all packaged in an
existential `∃ ν, ...` witness.

**Why the explicit-input form.**  See the docblock at
`fiber_int_mat_eq_via_i_block_explicit`.  This is the fourth step in the
explicit-parameter chain after `_rearr_adj_explicit`. -/
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
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a_def
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b_def
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c_def
  have hdet_block : (slSuccEmbed σ_i).val.det = 1 := (slSuccEmbed σ_i).2
  have hdet_X : (N_i⁻¹ * toSL j.out).val.det = 1 := (N_i⁻¹ * toSL j.out).2
  have hdet_ν : ν.val.det = 1 := ν.2
  have hdet_D_a : D_a.det = ∏ q : Fin (k + 1), (a q : ℤ) := by
    rw [hD_a_def, Matrix.det_diagonal, Fin.prod_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  have hdet_D_b : D_b.det = ∏ q : Fin (k + 1), (b q : ℤ) := by
    rw [hD_b_def, Matrix.det_diagonal, Fin.prod_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  have hdet_D_c : D_c.det = ∏ q : Fin (k + 1), (c q : ℤ) := by
    rw [hD_c_def, Matrix.det_diagonal, Fin.prod_univ_succ]
    simp [Fin.cons_zero, Fin.cons_succ]
  have hprod_eq :
      (∏ q : Fin (k + 1), (a q : ℤ)) * (∏ q : Fin (k + 1), (b q : ℤ)) =
      ∏ q : Fin (k + 1), (c q : ℤ) := by
    have h := congr_arg Matrix.det h_rearr
    simp only [Matrix.det_mul, Matrix.det_adjugate, hdet_block, hdet_X,
      hdet_ν, hdet_D_a, hdet_D_b, hdet_D_c, one_pow, mul_one, one_mul] at h
    exact h
  have hpc_pos : 0 < ∏ q : Fin (k + 1), (c q : ℤ) := by
    apply Finset.prod_pos
    intro q _
    exact_mod_cast hc q
  have hpc_ne : (∏ q : Fin (k + 1), (c q : ℤ)) ≠ 0 := hpc_pos.ne'
  have h_postmul :
      (∏ q : Fin (k + 1), (a q : ℤ)) •
        (Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val) =
      Matrix.adjugate ν.val *
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a := by
    have h : Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
          Matrix.adjugate D_a * D_a =
        Matrix.adjugate ν.val *
          (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a := by
      rw [show Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
              Matrix.adjugate D_a * D_a =
            (Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
              Matrix.adjugate D_a) * D_a from rfl,
          h_adj]
    rw [show Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            Matrix.adjugate D_a * D_a =
          Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val *
            (Matrix.adjugate D_a * D_a) by simp only [Matrix.mul_assoc]] at h
    rw [Matrix.adjugate_mul, hdet_D_a, Matrix.mul_smul, Matrix.mul_one] at h
    exact h
  have h_entry := congrFun (congrFun h_postmul r.succ) 0
  have h_LHS_simp :
      ((∏ q : Fin (k + 1), (a q : ℤ)) •
          (Matrix.adjugate D_b *
            Matrix.adjugate (N_i⁻¹ * toSL j.out).val)) r.succ 0 =
      (∏ q : Fin (k + 1), (a q : ℤ)) *
        ((∏ x ∈ Finset.univ.erase r.succ,
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
          Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) := by
    show (∏ q, (a q : ℤ)) *
        (Matrix.adjugate D_b * Matrix.adjugate (N_i⁻¹ * toSL j.out).val) r.succ 0 =
      _
    rw [hD_b_def, Matrix.adjugate_diagonal]
    rw [show
        (Matrix.diagonal (fun i : Fin (k + 2) ↦
          ∏ x ∈ Finset.univ.erase i,
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
          Matrix.adjugate (N_i⁻¹ * toSL j.out).val) r.succ 0 =
        (∏ x ∈ Finset.univ.erase r.succ,
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
        Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 from by
      rw [Matrix.diagonal_mul]]
  have h_RHS_simp :
      (Matrix.adjugate ν.val *
          (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a) r.succ 0 =
      Matrix.adjugate ν.val r.succ 0 * (∏ q : Fin (k + 1), (c q : ℤ)) := by
    have h1 :
        (Matrix.adjugate ν.val *
            (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) * D_a) r.succ 0 =
          (Matrix.adjugate ν.val *
            (Matrix.adjugate D_c * (slSuccEmbed σ_i).val)) r.succ 0 := by
      rw [hD_a_def, Matrix.mul_diagonal]
      simp [Fin.cons_zero]
    rw [h1]
    have hadjDc_block_p0 : ∀ p : Fin (k + 2),
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) p 0 =
        if p = 0 then (∏ q : Fin (k + 1), (c q : ℤ)) else 0 := by
      intro p
      rw [hD_c_def, Matrix.adjugate_diagonal, Matrix.diagonal_mul]
      refine Fin.cases ?_ ?_ p
      · rw [slSuccEmbed_val_zero_zero, mul_one, if_pos rfl]
        have hf0 : (((Fin.cons 1 c : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℕ) : ℤ) = 1 := by
          simp [Fin.cons_zero]
        rw [Finset.prod_erase (Finset.univ : Finset (Fin (k + 2))) hf0]
        rw [Fin.prod_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]
      · intro p'
        rw [slSuccEmbed_val_succ_zero, mul_zero, if_neg (Fin.succ_ne_zero p')]
    rw [Matrix.mul_apply]
    have hsum : ∀ (f : Fin (k + 2) → ℤ),
        (∀ p : Fin (k + 2), p ≠ 0 → f p = 0) →
        (∑ p : Fin (k + 2), f p) = f 0 := by
      intro f hf
      rw [show (∑ p, f p) = f 0 + ∑ p ∈ Finset.univ.erase 0, f p from
            (Finset.add_sum_erase _ _ (Finset.mem_univ _)).symm]
      rw [Finset.sum_eq_zero (fun p hp ↦ hf p (Finset.ne_of_mem_erase hp))]
      ring
    rw [hsum (fun p ↦ Matrix.adjugate ν.val r.succ p *
        (Matrix.adjugate D_c * (slSuccEmbed σ_i).val) p 0)]
    · rw [hadjDc_block_p0 0, if_pos rfl]
    · intro p hp
      rw [hadjDc_block_p0 p, if_neg hp, mul_zero]
  rw [h_LHS_simp, h_RHS_simp] at h_entry
  have h_b_in_set : r.succ ∈ (Finset.univ : Finset (Fin (k + 2))) :=
    Finset.mem_univ _
  have h_prod_b_fold :
      (∏ x ∈ Finset.univ.erase r.succ,
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) *
      ((b r : ℤ)) =
      ∏ q : Fin (k + 1), (b q : ℤ) := by
    have h := Finset.mul_prod_erase (Finset.univ : Finset (Fin (k + 2)))
      (fun x : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ)) h_b_in_set
    simp only at h
    have hfb_succ :
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) r.succ : ℕ) : ℤ) = (b r : ℤ) := by
      simp [Fin.cons_succ]
    have h_full :
        ∏ x : Fin (k + 2), (((Fin.cons 1 b : Fin (k + 2) → ℕ) x : ℕ) : ℤ) =
        ∏ q : Fin (k + 1), (b q : ℤ) := by
      rw [Fin.prod_univ_succ]
      have h0 :
          (((Fin.cons 1 b : Fin (k + 2) → ℕ) (0 : Fin (k + 2)) : ℕ) : ℤ) = 1 := by
        simp [Fin.cons_zero]
      rw [h0, one_mul]
      refine Finset.prod_congr rfl (fun i _ ↦ ?_)
      simp [Fin.cons_succ]
    rw [hfb_succ, h_full] at h
    linarith [h]
  have h_mul_b_r := congr_arg (· * (b r : ℤ)) h_entry
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
              Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0) by ring]
    rw [h_prod_b_fold, ← mul_assoc, hprod_eq]
  have h_RHS_b :
      Matrix.adjugate ν.val r.succ 0 * (∏ q : Fin (k + 1), (c q : ℤ)) * (b r : ℤ) =
      (∏ q : Fin (k + 1), (c q : ℤ)) *
        ((b r : ℤ) * Matrix.adjugate ν.val r.succ 0) := by
    ring
  rw [h_LHS_b, h_RHS_b] at h_mul_b_r
  have h_X_eq :
      Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 =
        (b r : ℤ) * Matrix.adjugate ν.val r.succ 0 :=
    mul_left_cancel₀ hpc_ne h_mul_b_r
  refine ⟨Matrix.adjugate ν.val r.succ 0, ?_⟩
  have h_inv_eq : ((N_i⁻¹ * toSL j.out)⁻¹ :
      SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 =
      Matrix.adjugate (N_i⁻¹ * toSL j.out).val r.succ 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv]
  rw [h_inv_eq, h_X_eq]

/-- See `hfib_col_div_b_via_i_block_explicit` for the active explicit-input
col-divisibility chain; this is now a thin wrapper that extracts the i-side
block witnesses via `exists_stab_with_block_form_of_fiber` and
`exists_stab_int_conjugate_diagMat_cons_one`, then delegates. -/
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

/-- **X-side block-form witness from the substituted fiber.**
Mirror of `exists_stab_with_block_form_of_fiber` but for the SUBSTITUTED
matrix `X := N_i⁻¹ * toSL j.out`, where `N_i` is the integer-conjugate
companion of the i-side stabilizer factor `M_i` (both extracted from
`hfib_col_div_b_via_i_block`).

Produces `M_X ∈ SL(k+2, ℤ)` in the `Fin.cons 1 b`-diagonal-conjugation
stabilizer plus `τ_X ∈ SL(k+1, ℤ)` such that
  `(N_i⁻¹ * toSL j.out) * M_X = slSuccEmbed τ_X`.

This is the j-side analog of the i-side block form. The proof mirrors
the i-side template:
1. Apply `hfib_col_div_b_via_i_block` to obtain `N_i` and the chain
   divisibility `b r ∣ X⁻¹.{r.succ, 0}`.
2. Apply `sl_first_col_primitive (X⁻¹)` for primitivity of X⁻¹'s first
   column.
3. Feed both into `sl_exists_col_stab_divChain b hb hdb` to obtain
   `M_0_X ∈ stab(D_b)` with first column matching X⁻¹'s first column.
4. Compute `(X * M_0_X).first_col = (X * X⁻¹).first_col = e_0`.
5. Apply `sl_first_row_clear_with_col0_e0 b hb` to clear the first row.
6. Combine into `M_X := M_0_X * T_clear` (in stab(D_b) by mul-closure).
7. The product `(X * M_X)` has first row and first column = e_0, hence
   equals `slSuccEmbed τ_X` for `τ_X` the bottom-right block.

The exposed `M_i`, `N_i`, plus the integer conjugation identity
`D_a · N_i = M_i · D_a`, support the eventual N_i-bridge to a canonical
j-side block form on `toSL j.out` (the next-stint deliverable). -/
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
  obtain ⟨σ_i, M_i, N_i, ν, h_block_i, h_stab_i, h_int_conj, h_subst, h_rearr_adj, h_div⟩ :=
    hfib_col_div_b_via_i_block a b c ha hb hc hda i j hfib
  set X : SpecialLinearGroup (Fin (k + 2)) ℤ := N_i⁻¹ * toSL j.out with hX_def
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
  set N : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ := (X * M_X).val with hN_def
  have hM_X_assoc : X * M_X = (X * M_0_X) * T_clear := by
    rw [hM_X_def]; exact (mul_assoc _ _ _).symm
  have hN_col0 : ∀ r : Fin (k + 2),
      N r 0 = (1 : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ) r 0 := by
    intro r
    show (X * M_X).val r 0 = _
    rw [hM_X_assoc, hT_col0 r]
    exact h_col_e0 r
  have hN_row0 : ∀ l : Fin (k + 1), N 0 l.succ = 0 := by
    intro l
    show (X * M_X).val 0 l.succ = _
    rw [hM_X_assoc]
    exact hT_S l (Finset.mem_univ l)
  have hN_00 : N 0 0 = 1 := by
    have h := hN_col0 0
    rw [Matrix.one_apply_eq] at h
    exact h
  have hN_succ0 : ∀ I : Fin (k + 1), N I.succ 0 = 0 := by
    intro I
    have h := hN_col0 I.succ
    rw [Matrix.one_apply_ne (Fin.succ_ne_zero I)] at h
    exact h
  set τ_X_raw : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun I J ↦ N I.succ J.succ with hτ_raw_def
  have h_det : τ_X_raw.det = 1 := by
    have h_det_N : N.det = 1 := by
      rw [hN_def]; exact (X * M_X).2
    rw [Matrix.det_succ_row_zero] at h_det_N
    rw [Fin.sum_univ_succ] at h_det_N
    have h_zero_terms :
        ∀ j : Fin (k + 1),
          (-1 : ℤ) ^ (j.succ : ℕ) * N 0 j.succ *
            (N.submatrix Fin.succ j.succ.succAbove).det = 0 := by
      intro j
      rw [hN_row0 j]; ring
    rw [Finset.sum_eq_zero (fun j _ ↦ h_zero_terms j), add_zero, hN_00] at h_det_N
    simp only [Fin.val_zero, pow_zero, one_mul, mul_one] at h_det_N
    have h_submat : N.submatrix Fin.succ (0 : Fin (k + 2)).succAbove = τ_X_raw := by
      ext I J
      show N I.succ ((0 : Fin (k + 2)).succAbove J) = τ_X_raw I J
      rw [Fin.succAbove_zero]
    rw [h_submat] at h_det_N
    exact h_det_N
  set τ_X : SpecialLinearGroup (Fin (k + 1)) ℤ := ⟨τ_X_raw, h_det⟩ with hτ_X_def
  refine ⟨M_i, N_i, M_X, τ_X, h_stab_i, h_int_conj, ?_, ?_⟩
  · -- (X * M_X) = slSuccEmbed τ_X.
    apply Subtype.ext
    ext I J
    show N I J = (slSuccEmbed τ_X).val I J
    refine Fin.cases ?_ ?_ I
    · refine Fin.cases ?_ ?_ J
      · rw [hN_00, slSuccEmbed_val_zero_zero]
      · intro J'
        rw [hN_row0 J', slSuccEmbed_val_zero_succ]
    · intro I'
      refine Fin.cases ?_ ?_ J
      · rw [hN_succ0 I', slSuccEmbed_val_succ_zero]
      · intro J'
        rw [slSuccEmbed_val_succ_succ]
  · -- M_X ∈ stab(D_b).
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

end HeckeRing.GLn
