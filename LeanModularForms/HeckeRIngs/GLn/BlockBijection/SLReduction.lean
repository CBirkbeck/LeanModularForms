/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.HeckeMultBridge

/-!
# Block Embedding Bijection: SL row/column primitivity, Bezout, and divChain reduction (Shimura Lemma 3.19)
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

/-- **First column of `SL_n(ℤ)` is primitive.** Any common integer divisor of
the entries of column 0 of an `SL_n(ℤ)` matrix is a unit (`±1`). Follows from
Laplace expansion of the determinant along column 0. -/
lemma sl_first_col_primitive {n : ℕ} [NeZero n]
    (N : SpecialLinearGroup (Fin n) ℤ) (d : ℤ)
    (hd : ∀ i, d ∣ N.1 i 0) : IsUnit d := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have h_dvd_det : d ∣ N.1.det := by
    rw [Matrix.det_succ_column_zero]
    exact Finset.dvd_sum fun i _ ↦ ((hd i).mul_left _).mul_right _
  exact isUnit_of_dvd_one (N.2 ▸ h_dvd_det)

private lemma sl_row_primitive {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (d : ℤ) (hd : ∀ k : Fin n.succ, d ∣ N.1 r k) : IsUnit d := by
  have h_dvd_det : d ∣ N.1.det := by
    rw [Matrix.det_succ_row N.1 r]
    exact Finset.dvd_sum fun j _ ↦ ((hd j).mul_left _).mul_right _
  exact isUnit_of_dvd_one (N.2 ▸ h_dvd_det)

private lemma sl_row_exists_not_dvd {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (p : ℤ) (hp_not_unit : ¬ IsUnit p) :
    ∃ k : Fin n.succ, ¬ p ∣ N.1 r k := by
  by_contra! h
  exact hp_not_unit (sl_row_primitive N r p h)

private lemma sl_row_exists_not_dvd_of_prime {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ) (r : Fin n.succ)
    (p : ℕ) (hp : p.Prime) :
    ∃ k : Fin n.succ, ¬ (p : ℤ) ∣ N.1 r k := by
  refine sl_row_exists_not_dvd N r (p : ℤ) fun h_unit ↦ ?_
  rcases Int.isUnit_iff.mp h_unit with h | h
  · exact hp.one_lt.ne' (by exact_mod_cast h)
  · have hpos : (p : ℤ) > 0 := by exact_mod_cast hp.pos
    linarith

private lemma sl_row_bezout {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) :
    ∃ c : Fin n.succ → ℤ, ∑ k, c k * N.1 r k = 1 := by
  refine ⟨fun k ↦ (-1) ^ ((r : ℕ) + (k : ℕ)) *
    (N.1.submatrix r.succAbove k.succAbove).det, ?_⟩
  have hdet : N.1.det = 1 := N.2
  rw [Matrix.det_succ_row N.1 r] at hdet
  have h_eq : ∑ k : Fin n.succ, ((-1) ^ ((r : ℕ) + (k : ℕ)) *
      (N.1.submatrix r.succAbove k.succAbove).det) * N.1 r k =
      ∑ j : Fin n.succ, (-1) ^ ((r : ℕ) + (j : ℕ)) * N.1 r j *
        (N.1.submatrix r.succAbove j.succAbove).det :=
    Finset.sum_congr rfl fun j _ ↦ by ring
  rw [h_eq, hdet]

private lemma sl_row_clear_mod {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (x m : ℤ) :
    ∃ c : Fin n.succ → ℤ, m ∣ x + ∑ k, c k * N.1 r k := by
  obtain ⟨c₀, hc₀⟩ := sl_row_bezout N r
  refine ⟨fun k ↦ -x * c₀ k, ?_⟩
  have h_sum : ∑ k, (-x * c₀ k) * N.1 r k = -x := by
    simp only [mul_assoc, ← Finset.mul_sum, hc₀, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero m

private lemma sl_row_clear_mod_avoiding {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (k₀ : Fin n.succ)
    (h_redundant : ∃ c₀ : Fin n.succ → ℤ,
      c₀ k₀ = 0 ∧ ∑ k, c₀ k * N.1 r k = 1)
    (x m : ℤ) :
    ∃ c : Fin n.succ → ℤ, c k₀ = 0 ∧ m ∣ x + ∑ k, c k * N.1 r k := by
  obtain ⟨c₀, hc₀_zero, hc₀_sum⟩ := h_redundant
  refine ⟨fun k ↦ -x * c₀ k, by simp [hc₀_zero], ?_⟩
  have h_sum : ∑ k, (-x * c₀ k) * N.1 r k = -x := by
    simp only [mul_assoc, ← Finset.mul_sum, hc₀_sum, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero m

private lemma sl2_bezout_zero_out (a b : ℤ) (h_ne : a ≠ 0 ∨ b ≠ 0) :
    ∃ B : SpecialLinearGroup (Fin 2) ℤ,
      B.1 *ᵥ ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  have hd_ne : (Int.gcd a b : ℤ) ≠ 0 := by
    intro h
    have h_nat : Int.gcd a b = 0 := by exact_mod_cast h
    rcases Int.gcd_eq_zero_iff.mp h_nat with ⟨ha, hb⟩
    rcases h_ne with ha' | hb'
    · exact ha' ha
    · exact hb' hb
  obtain ⟨a', ha'⟩ : (Int.gcd a b : ℤ) ∣ a := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right a b
  have hbez : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b :=
    Int.gcd_eq_gcd_ab a b
  have h_det : Int.gcdA a b * a' + Int.gcdB a b * b' = 1 := by
    have hprod : (Int.gcd a b : ℤ) * (Int.gcdA a b * a' + Int.gcdB a b * b') =
        (Int.gcd a b : ℤ) * 1 := by
      calc (Int.gcd a b : ℤ) * (Int.gcdA a b * a' + Int.gcdB a b * b')
          = Int.gcdA a b * ((Int.gcd a b : ℤ) * a') +
              Int.gcdB a b * ((Int.gcd a b : ℤ) * b') := by ring
        _ = a * Int.gcdA a b + b * Int.gcdB a b := by rw [← ha', ← hb']; ring
        _ = (Int.gcd a b : ℤ) := hbez.symm
        _ = (Int.gcd a b : ℤ) * 1 := by ring
    exact mul_left_cancel₀ hd_ne hprod
  refine ⟨⟨!![Int.gcdA a b, Int.gcdB a b; -b', a'], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; linarith
  · have hentries : (!![Int.gcdA a b, Int.gcdB a b; -b', a'] *ᵥ ![a, b] : Fin 2 → ℤ) =
        ![Int.gcdA a b * a + Int.gcdB a b * b, -b' * a + a' * b] := by
      ext i
      fin_cases i <;>
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    show (!![Int.gcdA a b, Int.gcdB a b; -b', a'] *ᵥ ![a, b] : Fin 2 → ℤ) =
      ![(Int.gcd a b : ℤ), 0]
    rw [hentries]
    have h0 : Int.gcdA a b * a + Int.gcdB a b * b = (Int.gcd a b : ℤ) := by
      rw [mul_comm (Int.gcdA a b) a, mul_comm (Int.gcdB a b) b]
      exact hbez.symm
    have h1 : -b' * a + a' * b = 0 := by
      have step : -b' * ((Int.gcd a b : ℤ) * a') + a' * ((Int.gcd a b : ℤ) * b') = 0 := by ring
      rwa [← ha', ← hb'] at step
    ext i
    fin_cases i
    · exact h0
    · exact h1

private noncomputable def sl2_row_embed_01 {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ) :
    SpecialLinearGroup (Fin (n + 3)) ℤ :=
  let e : Fin (n + 3) ≃ Fin 2 ⊕ Fin (n + 1) :=
    (Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  ⟨(Matrix.fromBlocks (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)).submatrix e e, by
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one, B.2]⟩

private lemma sl2_row_embed_01_val_eq {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ) :
    (sl2_row_embed_01 (n := n) B).1 =
      (Matrix.fromBlocks (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)).submatrix
        ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
          finSumFinEquiv.symm)
        ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
          finSumFinEquiv.symm) := rfl

private lemma sl2_row_embed_01_equiv_lt_2 {n : ℕ} (i : Fin (n + 3)) (h : i.val < 2) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm) i = Sum.inl ⟨i.val, h⟩ := by
  have hcast :
      ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv) i =
        Fin.castAdd (n + 1) ⟨i.val, h⟩ := by
    ext; simp [Fin.castAdd]
  rw [Equiv.trans_apply, hcast, finSumFinEquiv_symm_apply_castAdd]

private lemma sl2_row_embed_01_equiv_ge_2 {n : ℕ} (i : Fin (n + 3)) (h : 2 ≤ i.val) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm) i = Sum.inr ⟨i.val - 2, by omega⟩ := by
  have hcast :
      ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv) i =
        Fin.natAdd 2 ⟨i.val - 2, by omega⟩ := by
    ext; simp [Fin.natAdd]; omega
  rw [Equiv.trans_apply, hcast, finSumFinEquiv_symm_apply_natAdd]

private lemma sl2_row_embed_01_equiv_symm_inl {n : ℕ} (j : Fin 2) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm).symm (Sum.inl j) = ⟨j.val, by omega⟩ := by
  apply Fin.ext
  simp [Equiv.trans, Equiv.symm, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
    Fin.castAdd]

private lemma sl2_row_embed_01_equiv_symm_inr {n : ℕ} (j : Fin (n + 1)) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm).symm (Sum.inr j) = ⟨j.val + 2, by omega⟩ := by
  apply Fin.ext
  simp [Equiv.trans, Equiv.symm, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
    Fin.natAdd]
  omega

private lemma sl2_row_embed_01_mulVec {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ)
    (v : Fin (n + 3) → ℤ) (i : Fin (n + 3)) :
    ((sl2_row_embed_01 B).1 *ᵥ v) i =
      if h : i.val < 2 then (B.1 *ᵥ ![v 0, v 1]) ⟨i.val, h⟩ else v i := by
  rw [sl2_row_embed_01_val_eq, Matrix.submatrix_mulVec_equiv]
  by_cases h : i.val < 2
  · simp only [h, dite_true, Function.comp_apply]
    rw [sl2_row_embed_01_equiv_lt_2 i h, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Matrix.zero_mulVec, add_zero]
    have h_restrict : ((v ∘ ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm).symm) ∘ Sum.inl : Fin 2 → ℤ) = ![v 0, v 1] := by
      funext j
      fin_cases j <;>
        · simp only [Function.comp_apply]
          rw [sl2_row_embed_01_equiv_symm_inl]
          rfl
    rw [h_restrict]
  · simp only [h, dite_false, Function.comp_apply]
    have h' : 2 ≤ i.val := Nat.not_lt.mp h
    rw [sl2_row_embed_01_equiv_ge_2 i h', Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inr, Matrix.zero_mulVec, zero_add,
      Matrix.one_mulVec, Function.comp_apply]
    rw [sl2_row_embed_01_equiv_symm_inr]
    exact congr_arg v (Fin.ext (show (i.val - 2) + 2 = i.val by omega))

private lemma sl_bezout_reduce_dim {n : ℕ} (w : Fin (n + 3) → ℤ)
    (h_ne : w 0 ≠ 0 ∨ w 1 ≠ 0) :
    ∃ E : SpecialLinearGroup (Fin (n + 3)) ℤ,
      (E.1 *ᵥ w) 0 = (Int.gcd (w 0) (w 1) : ℤ) ∧
      (E.1 *ᵥ w) 1 = 0 ∧
      (∀ i : Fin (n + 1), (E.1 *ᵥ w) ⟨i.val + 2, by omega⟩ =
        w ⟨i.val + 2, by omega⟩) := by
  obtain ⟨B, hB⟩ := sl2_bezout_zero_out (w 0) (w 1) h_ne
  refine ⟨sl2_row_embed_01 (n := n) B, ?_, ?_, ?_⟩
  · rw [sl2_row_embed_01_mulVec]
    have h0 : (0 : Fin (n + 3)).val < 2 := by show 0 < 2; omega
    simp only [h0, dite_true]
    rw [hB]
    rfl
  · rw [sl2_row_embed_01_mulVec]
    have h1 : (1 : Fin (n + 3)).val < 2 := by show 1 < 2; omega
    simp only [h1, dite_true]
    rw [hB]
    rfl
  · intro i
    rw [sl2_row_embed_01_mulVec]
    have hge : ¬ (⟨i.val + 2, by omega⟩ : Fin (n + 3)).val < 2 := by
      show ¬ (i.val + 2 < 2); omega
    simp only [hge, dite_false]

private lemma sl_dvd_of_mulVec_dvd {m : ℕ} (M : SpecialLinearGroup (Fin m) ℤ)
    (v : Fin m → ℤ) (d : ℤ) (h : ∀ i, d ∣ (M.1 *ᵥ v) i) (i : Fin m) : d ∣ v i := by
  have h_inv_mul : (M⁻¹).1 * M.1 = (1 : Matrix (Fin m) (Fin m) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
        Matrix.SpecialLinearGroup.coe_one]
  have hv_eq : v i = ((M⁻¹).1 *ᵥ (M.1 *ᵥ v)) i := by
    rw [Matrix.mulVec_mulVec, h_inv_mul, Matrix.one_mulVec]
  rw [hv_eq]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum (fun k _ ↦ (h k).mul_left _)

private noncomputable def sl_extend_at_1 {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ) :
    SpecialLinearGroup (Fin (n + 3)) ℤ :=
  ⟨(slSuccEmbed M).1.submatrix (Equiv.swap (0 : Fin (n + 3)) 1) (Equiv.swap 0 1), by
    rw [det_submatrix_equiv_self]; exact (slSuccEmbed M).2⟩

private lemma sl_extend_at_1_col_0_zero {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ) :
    (sl_extend_at_1 M).1 0 0 = M.1 0 0 := by
  show (slSuccEmbed M).1 (Equiv.swap 0 1 0) (Equiv.swap 0 1 0) = M.1 0 0
  rw [Equiv.swap_apply_left]
  exact slSuccEmbed_val_succ_succ M 0 0

private lemma sl_extend_at_1_col_0_one {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ) :
    (sl_extend_at_1 M).1 1 0 = 0 := by
  show (slSuccEmbed M).1 (Equiv.swap (0 : Fin (n + 3)) 1 1) (Equiv.swap (0 : Fin (n + 3)) 1 0) = 0
  rw [Equiv.swap_apply_right, Equiv.swap_apply_left]
  exact slSuccEmbed_val_zero_succ M 0

private lemma sl_extend_at_1_col_0_ge_2 {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ)
    (i : Fin (n + 1)) :
    (sl_extend_at_1 M).1 ⟨i.val + 2, by omega⟩ 0 = M.1 ⟨i.val + 1, by omega⟩ 0 := by
  show (slSuccEmbed M).1 (Equiv.swap 0 1 ⟨i.val + 2, by omega⟩) (Equiv.swap 0 1 0) = _
  have h_ne_0 : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) ≠ 0 := by
    apply Fin.ne_of_val_ne; simp
  have h_ne_1 : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) ≠ 1 := by
    apply Fin.ne_of_val_ne; show i.val + 2 ≠ 1; omega
  rw [Equiv.swap_apply_of_ne_of_ne h_ne_0 h_ne_1, Equiv.swap_apply_left]
  have : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) =
      (⟨i.val + 1, by omega⟩ : Fin (n + 2)).succ := Fin.ext rfl
  rw [this, show (1 : Fin (n + 3)) = (0 : Fin (n + 2)).succ from rfl,
      slSuccEmbed_val_succ_succ]

private lemma sl_extend_at_1_col_0_matches_reduce {n : ℕ}
    (w_ok : Fin (n + 3) → ℤ) (w' : Fin (n + 2) → ℤ)
    (N' : SpecialLinearGroup (Fin (n + 2)) ℤ)
    (hN' : ∀ i, N'.1 i 0 = w' i)
    (hw'_0 : w' 0 = (Int.gcd (w_ok 0) (w_ok 1) : ℤ))
    (hw'_succ : ∀ i : Fin (n + 1), w' ⟨i.val + 1, by omega⟩ =
      w_ok ⟨i.val + 2, by omega⟩)
    (E : SpecialLinearGroup (Fin (n + 3)) ℤ)
    (hE0 : (E.1 *ᵥ w_ok) 0 = (Int.gcd (w_ok 0) (w_ok 1) : ℤ))
    (hE1 : (E.1 *ᵥ w_ok) 1 = 0)
    (hErest : ∀ i : Fin (n + 1), (E.1 *ᵥ w_ok) ⟨i.val + 2, by omega⟩ =
      w_ok ⟨i.val + 2, by omega⟩) :
    ∀ i : Fin (n + 3), (sl_extend_at_1 N').1 i 0 = (E.1 *ᵥ w_ok) i := by
  intro i
  by_cases h0 : i.val = 0
  · rw [(Fin.ext h0 : i = 0), sl_extend_at_1_col_0_zero, hE0, hN' 0, hw'_0]
  · by_cases h1 : i.val = 1
    · rw [(Fin.ext h1 : i = 1), sl_extend_at_1_col_0_one, hE1]
    · have h_ge : 2 ≤ i.val := by omega
      have h_lt : i.val < n + 3 := i.isLt
      let i' : Fin (n + 1) := ⟨i.val - 2, by omega⟩
      have hi_eq : i = ⟨i'.val + 2, by omega⟩ := by
        apply Fin.ext
        show i.val = i.val - 2 + 2
        omega
      rw [hi_eq, sl_extend_at_1_col_0_ge_2 N' i', hErest i',
          hN' ⟨i'.val + 1, by omega⟩, hw'_succ i']

private lemma sl_exists_col_of_primitive_fin_2 (w : Fin 2 → ℤ)
    (hw : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d) :
    ∃ N : SpecialLinearGroup (Fin 2) ℤ, ∀ i, N.1 i 0 = w i := by
  have hcop : IsCoprime (w 0) (w 1) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h_dvd : ∀ i : Fin 2, (Int.gcd (w 0) (w 1) : ℤ) ∣ w i := by
      intro i
      fin_cases i
      · exact Int.gcd_dvd_left _ _
      · exact Int.gcd_dvd_right _ _
    rcases Int.isUnit_iff.mp (hw _ h_dvd) with hpos | hneg
    · exact_mod_cast hpos
    · exfalso
      have hnn : (0 : ℤ) ≤ (Int.gcd (w 0) (w 1) : ℤ) := Int.natCast_nonneg _
      omega
  obtain ⟨g, hg0, hg1⟩ := IsCoprime.exists_SL2_col hcop 0
  refine ⟨g, ?_⟩
  intro i
  fin_cases i
  · exact hg0
  · exact hg1

private lemma sl_exists_transvection_first_two_ne {n : ℕ} (w : Fin (n + 3) → ℤ)
    (hw : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d) :
    ∃ T : SpecialLinearGroup (Fin (n + 3)) ℤ,
      (T.1 *ᵥ w) 0 ≠ 0 ∨ (T.1 *ᵥ w) 1 ≠ 0 := by
  have h_has_ne : ∃ j : Fin (n + 3), w j ≠ 0 := by
    by_contra! h_all_zero
    have : IsUnit (2 : ℤ) := hw 2 (fun i ↦ by rw [h_all_zero i]; exact dvd_zero _)
    rw [Int.isUnit_iff] at this; omega
  by_cases h_ne : w 0 ≠ 0 ∨ w 1 ≠ 0
  · refine ⟨1, ?_⟩
    rcases h_ne with h0 | h1
    · left; rwa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    · right; rwa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  · push Not at h_ne
    obtain ⟨hw0, hw1⟩ := h_ne
    obtain ⟨j, hj_ne⟩ := h_has_ne
    have hj_ge : 2 ≤ j.val := by
      by_contra! hlt
      rcases (by omega : j.val = 0 ∨ j.val = 1) with h0 | h1
      · exact hj_ne ((Fin.ext h0 : j = 0).symm ▸ hw0)
      · exact hj_ne ((Fin.ext h1 : j = 1).symm ▸ hw1)
    have hj_ne_1 : (1 : Fin (n + 3)) ≠ j := by
      apply Fin.ne_of_val_ne; show 1 ≠ j.val; omega
    have h_det : (Matrix.transvection (1 : Fin (n + 3)) j (1 : ℤ)).det = 1 :=
      Matrix.det_transvection_of_ne (1 : Fin (n + 3)) j hj_ne_1 (1 : ℤ)
    refine ⟨⟨Matrix.transvection (1 : Fin (n + 3)) j (1 : ℤ), h_det⟩, ?_⟩
    right
    show (Matrix.transvection (1 : Fin (n + 3)) j (1 : ℤ) *ᵥ w) 1 ≠ 0
    simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec, Pi.add_apply, Function.update_self]
    rw [hw1]; simpa using hj_ne

private lemma sl_reduced_vector_primitive {n : ℕ}
    (w_ok : Fin (n + 3) → ℤ) (w' : Fin (n + 2) → ℤ)
    (hw_ok_prim : ∀ d : ℤ, (∀ i, d ∣ w_ok i) → IsUnit d)
    (hw'_0 : w' 0 = (Int.gcd (w_ok 0) (w_ok 1) : ℤ))
    (hw'_succ : ∀ i : Fin (n + 1), w' ⟨i.val + 1, by omega⟩ =
      w_ok ⟨i.val + 2, by omega⟩) :
    ∀ d : ℤ, (∀ i, d ∣ w' i) → IsUnit d := by
  intro d hd
  apply hw_ok_prim
  intro k
  by_cases hk0 : k.val = 0
  · rw [show k = (⟨0, by omega⟩ : Fin (n + 3)) from Fin.ext hk0]
    exact (hw'_0 ▸ hd 0 : d ∣ (Int.gcd (w_ok 0) (w_ok 1) : ℤ)).trans (Int.gcd_dvd_left _ _)
  · by_cases hk1 : k.val = 1
    · rw [show k = (⟨1, by omega⟩ : Fin (n + 3)) from Fin.ext hk1]
      exact (hw'_0 ▸ hd 0 : d ∣ (Int.gcd (w_ok 0) (w_ok 1) : ℤ)).trans (Int.gcd_dvd_right _ _)
    · have h_ge : 2 ≤ k.val := by omega
      have h_lt : k.val < n + 3 := k.isLt
      let k' : Fin (n + 1) := ⟨k.val - 2, by omega⟩
      rw [show k = ⟨k'.val + 2, by omega⟩ from
        Fin.ext (by show k.val = k.val - 2 + 2; omega)]
      rw [← hw'_succ k']
      exact hd ⟨k'.val + 1, by omega⟩

/-- **Primitive-column completion helper (general dim ≥ 2)**: Given a primitive
integer vector `w : Fin (n + 2) → ℤ` (any common integer divisor of all entries
is a unit), there exists `N ∈ SL(Fin (n + 2), ℤ)` whose first column equals `w`. -/
lemma sl_exists_col_of_primitive : ∀ {n : ℕ} (w : Fin (n + 2) → ℤ)
    (_hw : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d),
    ∃ N : SpecialLinearGroup (Fin (n + 2)) ℤ, ∀ i, N.1 i 0 = w i
  | 0, w, hw => sl_exists_col_of_primitive_fin_2 w hw
  | n + 1, w, hw => by
    obtain ⟨T, hT_ne⟩ := sl_exists_transvection_first_two_ne w hw
    set w_ok := T.1 *ᵥ w with hw_ok_def
    obtain ⟨E, hE0, hE1, hErest⟩ := sl_bezout_reduce_dim w_ok hT_ne
    let w' : Fin (n + 2) → ℤ := fun i ↦
      if i.val = 0 then (Int.gcd (w_ok 0) (w_ok 1) : ℤ)
      else w_ok ⟨i.val + 1, by omega⟩
    have hw'_0 : w' 0 = (Int.gcd (w_ok 0) (w_ok 1) : ℤ) := by simp [w']
    have hw'_succ : ∀ i : Fin (n + 1), w' ⟨i.val + 1, by omega⟩ =
        w_ok ⟨i.val + 2, by omega⟩ := by
      intro i
      show (if ((⟨i.val + 1, by omega⟩ : Fin (n + 2)).val = 0) then _ else _) = _
      rw [if_neg (by show i.val + 1 ≠ 0; omega)]
    have hw'_prim : ∀ d : ℤ, (∀ i, d ∣ w' i) → IsUnit d :=
      sl_reduced_vector_primitive w_ok w'
        (fun d hd ↦ hw d (sl_dvd_of_mulVec_dvd T w d hd)) hw'_0 hw'_succ
    obtain ⟨N', hN'⟩ := sl_exists_col_of_primitive w' hw'_prim
    refine ⟨T⁻¹ * (E⁻¹ * sl_extend_at_1 N'), ?_⟩
    intro i
    have h_inv_mul_E : E⁻¹.1 * E.1 = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
    have h_inv_mul_T : T⁻¹.1 * T.1 = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
    have h_col_inner : (sl_extend_at_1 N').1 *ᵥ (Pi.single 0 (1 : ℤ)) = E.1 *ᵥ w_ok := by
      funext k
      rw [Matrix.mulVec_single_one]
      exact sl_extend_at_1_col_0_matches_reduce w_ok w' N' hN' hw'_0 hw'_succ E hE0 hE1 hErest k
    have h_N_col0 : (T⁻¹ * (E⁻¹ * sl_extend_at_1 N')).1 *ᵥ (Pi.single 0 (1 : ℤ)) = w := by
      show (T⁻¹.1 * (E⁻¹.1 * (sl_extend_at_1 N').1)) *ᵥ (Pi.single 0 (1 : ℤ)) = w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h_col_inner]
      have h_E_cancel : E⁻¹.1 *ᵥ (E.1 *ᵥ w_ok) = w_ok := by
        rw [Matrix.mulVec_mulVec, h_inv_mul_E, Matrix.one_mulVec]
      rw [h_E_cancel]
      show T⁻¹.1 *ᵥ w_ok = w
      rw [hw_ok_def, Matrix.mulVec_mulVec, h_inv_mul_T, Matrix.one_mulVec]
    have := congr_fun h_N_col0 i
    rwa [Matrix.mulVec_single_one] at this

/-- **Fiber ⟹ mem_H bridge.** The dim-`k+2` set-form fiber condition on
`(i.out, j.out)` with `diagMat_delta` entries rewrites to the `diagMat`-shaped
H-membership condition consumed by `slSuccEmbed_H_fiber_transfer`-family
lemmas and by `hfib_col_div_a/b`. -/
lemma hfib_to_mem_H {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
      (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) ∈
        (GL_pair (k + 2)).H := by
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  simp only [diagMat_delta_val (k + 2) (Fin.cons 1 a) hcons_a,
      diagMat_delta_val (k + 2) (Fin.cons 1 b) hcons_b,
      diagMat_delta_val (k + 2) (Fin.cons 1 c) hcons_c] at hfib
  exact (fiber_diagMat_iff_mem_H (Fin.cons 1 a) (Fin.cons 1 b) (Fin.cons 1 c)
    hcons_a hcons_b hcons_c i.out j.out).mp hfib

/-- **GL-level integer-conjugate identity.**
Lifts the integer-matrix identity `D_a · N_i.val = M_i.val · D_a` to the GL ℚ
form `D_a_GL · mapGL N_i = mapGL M_i · D_a_GL` via `Matrix.map (algebraMap ℤ ℚ)`. -/
lemma h_int_conj_GL_of_int_mat {k : ℕ}
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
  apply Units.ext
  show ((diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL _ ℚ)).val :
        Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ) =
      ((mapGL ℚ M_i : GL _ ℚ) * diagMat (k + 2) (Fin.cons 1 a)).val
  simp only [Units.val_mul]
  have h_Da : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ).val : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ (cons_one_pos ha),
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_N : ((mapGL ℚ N_i : GL _ ℚ).val : Matrix _ _ ℚ) =
      N_i.val.map (algebraMap ℤ ℚ) := rfl
  have h_M : ((mapGL ℚ M_i : GL _ ℚ).val : Matrix _ _ ℚ) =
      M_i.val.map (algebraMap ℤ ℚ) := rfl
  rw [h_Da, h_N, h_M, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congr_arg (fun M : Matrix _ _ ℤ ↦ M.map (algebraMap ℤ ℚ)) h_int_conj

/-- **GL-level fiber equation from the fiber condition.**
GL ℚ form of `hfib_int_mat_eq`: directly produces
`i.out · D_a · j.out · D_b = D_c · mapGL ν` in `GL (Fin (k+2)) ℚ`. -/
lemma hfib_GL_eq {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
          (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) =
        diagMat (k + 2) (Fin.cons 1 c) * (mapGL ℚ ν : GL (Fin (k + 2)) ℚ) := by
  obtain ⟨ν, hν⟩ := hfib_to_mem_H a b c ha hb hc i j hfib
  refine ⟨ν, ?_⟩
  rw [eq_comm, hν]; group

/-- **Integer matrix equation from the fiber condition**. The H-membership from
`hfib_to_mem_H` is witnessed by some `ν : SL_{k+2}(ℤ)`; because every factor on
both sides is the `Int.cast` image of an integer matrix, the equation descends
to the integer level `A · D_a · B · D_b = D_c · ν`, where `A := toSL i.out`,
`B := toSL j.out` and `D_x := Matrix.diagonal (Fin.cons 1 x)`. -/
lemma hfib_int_mat_eq {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (toSL i.out).1 *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) *
          (toSL j.out).1 *
          Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) =
        Matrix.diagonal (fun r : Fin (k + 2) ↦
            (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) * ν.1 := by
  obtain ⟨ν, hν⟩ := hfib_to_mem_H a b c ha hb hc i j hfib
  refine ⟨ν, ?_⟩
  have hmul : diagMat (k + 2) (Fin.cons 1 c) *
      (mapGL ℚ ν : GL (Fin (k + 2)) ℚ) =
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
          (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) := by
    rw [hν]; group
  have hmat := congr_arg
    (fun g : GL (Fin (k + 2)) ℚ ↦ (g : Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ)) hmul
  simp only [Units.val_mul] at hmat
  have h_i : ((i.out : GL (Fin (k + 2)) ℚ) : Matrix _ _ ℚ) =
      (toSL i.out).1.map (algebraMap ℤ ℚ) := by
    rw [← toSL_spec i.out]; rfl
  have h_j : ((j.out : GL (Fin (k + 2)) ℚ) : Matrix _ _ ℚ) =
      (toSL j.out).1.map (algebraMap ℤ ℚ) := by
    rw [← toSL_spec j.out]; rfl
  have h_ν : ((mapGL ℚ ν : GL _ ℚ) : Matrix _ _ ℚ) = ν.1.map (algebraMap ℤ ℚ) := rfl
  have h_Da : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ (cons_one_pos ha),
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_Db : ((diagMat (k + 2) (Fin.cons 1 b) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ (cons_one_pos hb),
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_Dc : ((diagMat (k + 2) (Fin.cons 1 c) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ (cons_one_pos hc),
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  rw [h_i, h_j, h_ν, h_Da, h_Db, h_Dc, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, ← Matrix.map_mul] at hmat
  exact (Matrix.map_injective (algebraMap ℤ ℚ).injective_int hmat).symm

private lemma adjugate_rearrange_of_matrix_eq {p : ℕ}
    (A B Da Db Dc ν : Matrix (Fin p) (Fin p) ℤ)
    (hdetA : A.det = 1) (hdetν : ν.det = 1)
    (heq : A * Da * B * Db = Dc * ν) :
    Da * B * Db * Matrix.adjugate ν = Matrix.adjugate A * Dc := by
  have h1 : Matrix.adjugate A * (A * Da * B * Db) * Matrix.adjugate ν =
      Matrix.adjugate A * (Dc * ν) * Matrix.adjugate ν := by
    rw [heq]
  have hAA : Matrix.adjugate A * A = 1 := by
    rw [Matrix.adjugate_mul, hdetA, one_smul]
  have hνν : ν * Matrix.adjugate ν = 1 := by
    rw [Matrix.mul_adjugate, hdetν, one_smul]
  rw [show Matrix.adjugate A * (A * Da * B * Db) * Matrix.adjugate ν =
          (Matrix.adjugate A * A) * Da * B * Db * Matrix.adjugate ν by
        simp only [← Matrix.mul_assoc]] at h1
  rw [hAA, Matrix.one_mul] at h1
  rw [show Matrix.adjugate A * (Dc * ν) * Matrix.adjugate ν =
          Matrix.adjugate A * Dc * (ν * Matrix.adjugate ν) by
        simp only [← Matrix.mul_assoc]] at h1
  rw [hνν, Matrix.mul_one] at h1
  exact h1

private lemma diagonal_dvd_adjugate_entry {p : ℕ}
    (da dc : Fin (p + 1) → ℤ) (R Adj : Matrix (Fin (p + 1)) (Fin (p + 1)) ℤ)
    (s : Fin (p + 1)) (hdc0 : dc 0 = 1)
    (heq : Matrix.diagonal da * R = Adj * Matrix.diagonal dc) :
    da s ∣ Adj s 0 := by
  have h_mul : ((Matrix.diagonal da * R).mulVec (Pi.single 0 (1 : ℤ))) s =
      ((Adj * Matrix.diagonal dc).mulVec (Pi.single 0 (1 : ℤ))) s := by rw [heq]
  have hRHS : ((Adj * Matrix.diagonal dc).mulVec (Pi.single 0 (1 : ℤ))) s = Adj s 0 := by
    rw [← Matrix.mulVec_mulVec, Matrix.diagonal_mulVec_single, hdc0, mul_one,
      Matrix.mulVec_single_one, Matrix.col_apply]
  have hLHS : ((Matrix.diagonal da * R).mulVec (Pi.single 0 (1 : ℤ))) s =
      da s * ((R.mulVec (Pi.single 0 (1 : ℤ))) s) := by
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
  rw [hLHS, hRHS] at h_mul
  exact ⟨_, h_mul.symm⟩

/-- **Column-zero divisibility for `(toSL i.out)⁻¹`**. From the integer matrix
equation `A · D_a · B · D_b = D_c · ν` supplied by `hfib_int_mat_eq`, the entry
`((toSL i.out)⁻¹).1 r.succ 0` is divisible by `a r` for every `r : Fin (k+1)`. -/
lemma hfib_col_div_a {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∀ r : Fin (k + 1),
      (a r : ℤ) ∣ ((toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0 := by
  obtain ⟨ν, hν⟩ := hfib_int_mat_eq a b c ha hb hc i j hfib
  set A_i := (toSL i.out).1 with hA_i
  set A_j := (toSL j.out).1 with hA_j
  set D_a : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_a
  set D_b : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_b
  set D_c : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ :=
    Matrix.diagonal (fun r : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ)) with hD_c
  intro r
  rw [show ((toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0
        = Matrix.adjugate A_i r.succ 0 by rw [SpecialLinearGroup.coe_inv],
    show (a r : ℤ) = (((Fin.cons 1 a : Fin (k + 2) → ℕ) r.succ : ℕ) : ℤ) by rw [Fin.cons_succ]]
  refine diagonal_dvd_adjugate_entry
    (fun s ↦ (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ))
    (fun s ↦ (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ))
    (A_j * D_b * Matrix.adjugate ν.1) (Matrix.adjugate A_i) r.succ (by simp [Fin.cons_zero]) ?_
  rw [← hD_a, ← hD_c, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact adjugate_rearrange_of_matrix_eq A_i A_j D_a D_b D_c ν.1 (toSL i.out).2 ν.2 hν

private lemma hfib_row_div_b_nu_top_row {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (i : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)))
    (j : decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 b)))
    (hfib : ({(i.out : GL (Fin (k + 2)) ℚ) *
        (diagMat_delta (k + 2) (Fin.cons 1 a) : GL (Fin (k + 2)) ℚ)} : Set _) *
        {(j.out : GL (Fin (k + 2)) ℚ) *
          (diagMat_delta (k + 2) (Fin.cons 1 b) : GL (Fin (k + 2)) ℚ)} *
        ((GL_pair (k + 2)).H : Set _) =
        {(diagMat_delta (k + 2) (Fin.cons 1 c) : GL (Fin (k + 2)) ℚ)} *
          ((GL_pair (k + 2)).H : Set _)) :
    ∀ r : Fin (k + 1),
      ∃ ν : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (b r : ℤ) ∣ ν.1 0 r.succ := by
  obtain ⟨ν, hν⟩ := hfib_int_mat_eq a b c ha hb hc i j hfib
  refine fun r ↦ ⟨ν, ?_⟩
  have h_entry : ((toSL i.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) *
      (toSL j.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) 0 r.succ =
      (Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) * ν.1) 0 r.succ :=
    congr_fun (congr_fun hν 0) r.succ
  have h_RHS : (Matrix.diagonal (fun s : Fin (k + 2) ↦
      (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) * ν.1) 0 r.succ =
      ν.1 0 r.succ := by
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_apply]
    simp [Fin.cons_zero]
  have h_LHS : ((toSL i.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) *
      (toSL j.out).1 *
      Matrix.diagonal (fun s : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) s : ℕ) : ℤ))) 0 r.succ =
      (b r : ℤ) *
        ((toSL i.out).1 *
          Matrix.diagonal (fun s : Fin (k + 2) ↦
            (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ)) *
          (toSL j.out).1) 0 r.succ := by
    rw [Matrix.mul_apply]
    simp only [Matrix.diagonal_apply]
    simp [Fin.cons_succ, mul_comm]
  rw [h_LHS, h_RHS] at h_entry
  exact ⟨_, h_entry.symm⟩

/-- **SL elementary column op**: right-multiplication by `slTransvecG i j hij c`
adds `c` times column `i` to column `j` and leaves all other columns unchanged.
At column `j`, the new entry is the original `(a, j)` plus `c` times `(a, i)`. -/
lemma sl_addCol_target_col {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (c : ℤ) (M : SpecialLinearGroup (Fin m) ℤ) (a : Fin m) :
    (M * slTransvecG i j hij c).1 a j = M.1 a j + c * M.1 a i := by
  have hcoe : (M * slTransvecG i j hij c).1 = M.1 * Matrix.transvection i j c := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, slTransvecG]
  rw [hcoe]
  simp [Matrix.transvection, Matrix.mul_add, mul_comm]

/-- **SL elementary column op preserves untouched columns**: at any column
`k ≠ j`, the entry is unchanged. -/
lemma sl_addCol_preserves_col {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (c : ℤ) (M : SpecialLinearGroup (Fin m) ℤ) (a : Fin m) {k : Fin m} (hk : k ≠ j) :
    (M * slTransvecG i j hij c).1 a k = M.1 a k := by
  have hcoe : (M * slTransvecG i j hij c).1 = M.1 * Matrix.transvection i j c := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, slTransvecG]
  rw [hcoe]
  simp [Matrix.transvection, Matrix.mul_add, hk]

private lemma sl_addCol_finset_target_aux {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (k₀ : Fin n.succ) (c : Fin n.succ → ℤ)
    (S : Finset (Fin n.succ)) (hS : k₀ ∉ S) :
    ∃ U : SpecialLinearGroup (Fin n.succ) ℤ,
      (∀ a (k : Fin n.succ), k ≠ k₀ → (N * U).1 a k = N.1 a k) ∧
      (∀ a, (N * U).1 a k₀ = N.1 a k₀ + ∑ k ∈ S, c k * N.1 a k) := by
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_⟩
      · intro a k _; simp
      · intro a; simp
  | insert k T hkT ih =>
      have hk_ne_k₀ : k ≠ k₀ := fun h ↦ hS (h ▸ Finset.mem_insert_self k T)
      obtain ⟨U, hU_pres, hU_target⟩ := ih (fun h ↦ hS (Finset.mem_insert_of_mem h))
      refine ⟨U * slTransvecG k k₀ hk_ne_k₀ (c k), ?_, ?_⟩
      · intro a k' hk'
        rw [← mul_assoc, sl_addCol_preserves_col k k₀ hk_ne_k₀ (c k) (N * U) a hk']
        exact hU_pres a k' hk'
      · intro a
        rw [← mul_assoc, sl_addCol_target_col k k₀ hk_ne_k₀ (c k) (N * U) a]
        rw [hU_target a, hU_pres a k hk_ne_k₀]
        rw [Finset.sum_insert hkT]
        ring

private lemma sl_addCol_finset_target {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (k₀ : Fin n.succ) (c : Fin n.succ → ℤ) (h_zero : c k₀ = 0) :
    ∃ U : SpecialLinearGroup (Fin n.succ) ℤ,
      (∀ a (k : Fin n.succ), k ≠ k₀ → (N * U).1 a k = N.1 a k) ∧
      (∀ a, (N * U).1 a k₀ = N.1 a k₀ + ∑ k, c k * N.1 a k) := by
  obtain ⟨U, hU_pres, hU_target⟩ :=
    sl_addCol_finset_target_aux N k₀ c (Finset.univ.erase k₀) (Finset.notMem_erase _ _)
  refine ⟨U, hU_pres, ?_⟩
  intro a
  rw [hU_target a]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k₀)]
  rw [h_zero, zero_mul, add_zero]

private lemma sl_clear_row_modular {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (k₀ : Fin n.succ) (m : ℤ)
    (h_redundant : ∃ c₀ : Fin n.succ → ℤ,
      c₀ k₀ = 0 ∧ ∑ k, c₀ k * N.1 r k = 1) :
    ∃ U : SpecialLinearGroup (Fin n.succ) ℤ,
      (∀ a (k : Fin n.succ), k ≠ k₀ → (N * U).1 a k = N.1 a k) ∧
      m ∣ (N * U).1 r k₀ := by
  obtain ⟨c, hc_zero, hc_dvd⟩ :=
    sl_row_clear_mod_avoiding N r k₀ h_redundant (N.1 r k₀) m
  obtain ⟨U, hU_pres, hU_target⟩ := sl_addCol_finset_target N k₀ c hc_zero
  refine ⟨U, hU_pres, ?_⟩
  rw [hU_target r]
  exact hc_dvd

private lemma sl_addCol_emod_step {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r : Fin m) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (M * U).1 r j = M.1 r j % M.1 r i := by
  refine ⟨slTransvecG i j hij (-(M.1 r j / M.1 r i)), ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · rw [sl_addCol_target_col i j hij _ M r]
    linarith [Int.emod_def (M.1 r j) (M.1 r i)]

private lemma dvd_entry_add_mul_of_shift {d e c c₀ p : ℤ}
    (h₀ : d ∣ e + c₀ * p) (hshift : d ∣ c - c₀) : d ∣ e + c * p := by
  rw [show e + c * p = (e + c₀ * p) + (c - c₀) * p by ring]
  exact dvd_add h₀ (hshift.mul_right p)

private lemma sl_addCol_make_dvd {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r : Fin m) (d : ℤ)
    (h_cop : IsCoprime (M.1 r i) d) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      d ∣ (M * U).1 r j := by
  obtain ⟨s, t, hst⟩ := h_cop
  refine ⟨slTransvecG i j hij (-(M.1 r j) * s), ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · rw [sl_addCol_target_col i j hij _ M r]
    refine ⟨M.1 r j * t, ?_⟩
    have : M.1 r j * (s * M.1 r i + t * d) = M.1 r j * 1 := by rw [hst]
    linarith [this]

private lemma sl_addCol_make_dvd_two_coprime {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r₁ r₂ : Fin m) (d₁ d₂ : ℤ)
    (h_cop₁ : IsCoprime (M.1 r₁ i) d₁) (h_cop₂ : IsCoprime (M.1 r₂ i) d₂)
    (h_cop_d : IsCoprime d₁ d₂) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (d₁ ∣ (M * U).1 r₁ j) ∧ (d₂ ∣ (M * U).1 r₂ j) := by
  obtain ⟨s₁, t₁, hst₁⟩ := h_cop₁
  obtain ⟨s₂, t₂, hst₂⟩ := h_cop₂
  obtain ⟨u, v, huv⟩ := h_cop_d
  set c₁ : ℤ := -(M.1 r₁ j) * s₁ with hc₁_def
  set c₂ : ℤ := -(M.1 r₂ j) * s₂ with hc₂_def
  set c : ℤ := v * d₂ * c₁ + u * d₁ * c₂ with hc_def
  refine ⟨slTransvecG i j hij c, ?_, ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · rw [sl_addCol_target_col i j hij _ M r₁]
    have hvd₂ : v * d₂ = 1 - u * d₁ := by linarith [huv]
    have key : M.1 r₁ j * (s₁ * M.1 r₁ i + t₁ * d₁) = M.1 r₁ j * 1 := by rw [hst₁]
    have hfirst : d₁ ∣ M.1 r₁ j + c₁ * M.1 r₁ i :=
      ⟨M.1 r₁ j * t₁, by rw [hc₁_def]; linarith [key]⟩
    have hshift : d₁ ∣ c - c₁ := ⟨u * c₂ - u * c₁, by
      rw [hc_def, show v * d₂ * c₁ + u * d₁ * c₂ - c₁ =
        (v * d₂ - 1) * c₁ + u * d₁ * c₂ from by ring, hvd₂]; ring⟩
    exact dvd_entry_add_mul_of_shift hfirst hshift
  · rw [sl_addCol_target_col i j hij _ M r₂]
    have hud₁ : u * d₁ = 1 - v * d₂ := by linarith [huv]
    have key : M.1 r₂ j * (s₂ * M.1 r₂ i + t₂ * d₂) = M.1 r₂ j * 1 := by rw [hst₂]
    have hfirst : d₂ ∣ M.1 r₂ j + c₂ * M.1 r₂ i :=
      ⟨M.1 r₂ j * t₂, by rw [hc₂_def]; linarith [key]⟩
    have hshift : d₂ ∣ c - c₂ := ⟨v * c₁ - v * c₂, by
      rw [hc_def, show v * d₂ * c₁ + u * d₁ * c₂ - c₂ =
        v * d₂ * c₁ + (u * d₁ - 1) * c₂ from by ring, hud₁]; ring⟩
    exact dvd_entry_add_mul_of_shift hfirst hshift

private lemma sl_addCol_make_dvd_two_compat {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r₁ r₂ : Fin m) (d₁ d₂ : ℤ)
    (c₁ c₂ : ℤ)
    (h₁ : d₁ ∣ M.1 r₁ j + c₁ * M.1 r₁ i)
    (h₂ : d₂ ∣ M.1 r₂ j + c₂ * M.1 r₂ i)
    (h_compat : (Int.gcd d₁ d₂ : ℤ) ∣ c₁ - c₂) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (d₁ ∣ (M * U).1 r₁ j) ∧ (d₂ ∣ (M * U).1 r₂ j) := by
  set u : ℤ := Int.gcdA d₁ d₂ with hu_def
  set v : ℤ := Int.gcdB d₁ d₂ with hv_def
  have hbezout : (Int.gcd d₁ d₂ : ℤ) = d₁ * u + d₂ * v := Int.gcd_eq_gcd_ab d₁ d₂
  obtain ⟨δ, hδ⟩ := h_compat
  set c : ℤ := c₁ - u * d₁ * δ with hc_def
  refine ⟨slTransvecG i j hij c, ?_, ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · rw [sl_addCol_target_col i j hij _ M r₁]
    exact dvd_entry_add_mul_of_shift h₁ ⟨-(u * δ), by rw [hc_def]; ring⟩
  · rw [sl_addCol_target_col i j hij _ M r₂]
    refine dvd_entry_add_mul_of_shift h₂ ⟨v * δ, ?_⟩
    have hkey : c - c₂ = (c₁ - c₂) - u * d₁ * δ := by rw [hc_def]; ring
    rw [hkey, hδ, hbezout]; ring

private lemma entry_add_prod_coeff_eq {D s t p q e : ℤ}
    (hst : s * (D * p) + t * q = 1) :
    e + D * (-e * s) * p = q * (e * t) := by
  have key : e * (s * (D * p) + t * q) = e * 1 := by rw [hst]
  linarith [key]

private lemma sl_addCol_make_dvd_finset_insert_step {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r₀ : Fin m) (R : Finset (Fin m)) (d : Fin m → ℤ)
    (hr₀ : r₀ ∉ R)
    (h_cop : ∀ r ∈ insert r₀ R, IsCoprime (M.1 r i) (d r))
    (h_pairwise : ∀ r₁ ∈ insert r₀ R, ∀ r₂ ∈ insert r₀ R,
      r₁ ≠ r₂ → IsCoprime (d r₁) (d r₂))
    (U_R : SpecialLinearGroup (Fin m) ℤ)
    (hU_R_pres : ∀ a (k : Fin m), k ≠ j → (M * U_R).1 a k = M.1 a k)
    (hU_R_div : ∀ r ∈ R, d r ∣ (M * U_R).1 r j) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (∀ r ∈ insert r₀ R, d r ∣ (M * U).1 r j) := by
  have h_cop_prod : IsCoprime (∏ r ∈ R, d r) (d r₀) := by
    refine (IsCoprime.prod_right (fun r hr ↦ ?_)).symm
    exact h_pairwise r₀ (Finset.mem_insert_self _ _) r
      (Finset.mem_insert_of_mem hr) (fun h ↦ hr₀ (h ▸ hr))
  obtain ⟨s, t, hst⟩ :=
    h_cop_prod.mul_left (h_cop r₀ (Finset.mem_insert_self _ _))
  set D : ℤ := ∏ r ∈ R, d r with hD_def
  set v : ℤ := -((M * U_R).1 r₀ j) * s with hv_def
  set c' : ℤ := D * v with hc'_def
  refine ⟨U_R * slTransvecG i j hij c', ?_, ?_⟩
  · intro a k hk
    rw [← mul_assoc, sl_addCol_preserves_col i j hij c' (M * U_R) a hk]
    exact hU_R_pres a k hk
  · intro r hr
    rcases Finset.mem_insert.mp hr with hr_eq | hr_mem
    · subst hr_eq
      rw [← mul_assoc, sl_addCol_target_col i j hij c' (M * U_R) r, hU_R_pres r i hij]
      exact ⟨(M * U_R).1 r j * t, by rw [hc'_def, hv_def]; exact entry_add_prod_coeff_eq hst⟩
    · rw [← mul_assoc, sl_addCol_target_col i j hij c' (M * U_R) r, hU_R_pres r i hij]
      have h_dr_div_D : d r ∣ D := hD_def ▸ Finset.dvd_prod_of_mem d hr_mem
      have h_dr_div_c' : d r ∣ c' := hc'_def ▸ h_dr_div_D.mul_right _
      exact dvd_add (hU_R_div r hr_mem) (h_dr_div_c'.mul_right _)

private lemma sl_addCol_make_dvd_finset
    {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ)
    (R : Finset (Fin m)) (d : Fin m → ℤ)
    (h_cop : ∀ r ∈ R, IsCoprime (M.1 r i) (d r))
    (h_pairwise : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ r₂ → IsCoprime (d r₁) (d r₂)) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (∀ r ∈ R, d r ∣ (M * U).1 r j) := by
  classical
  induction R using Finset.induction_on with
  | empty =>
      refine ⟨1, ?_, ?_⟩
      · intro a k _; simp
      · intro r hr; exact absurd hr (Finset.notMem_empty r)
  | insert r₀ R hr₀ IH =>
      obtain ⟨U_R, hU_R_pres, hU_R_div⟩ := IH
        (fun r hr ↦ h_cop r (Finset.mem_insert_of_mem hr))
        (fun r₁ hr₁ r₂ hr₂ hne ↦ h_pairwise r₁ (Finset.mem_insert_of_mem hr₁) r₂
          (Finset.mem_insert_of_mem hr₂) hne)
      exact sl_addCol_make_dvd_finset_insert_step i j hij M r₀ R d hr₀ h_cop h_pairwise
        U_R hU_R_pres hU_R_div

private lemma sl_addCol_make_dvd_common
    {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ)
    (R : Finset (Fin m)) (d : Fin m → ℤ) (c : ℤ)
    (h_dvd : ∀ r ∈ R, d r ∣ M.1 r j + c * M.1 r i) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (∀ r ∈ R, d r ∣ (M * U).1 r j) := by
  refine ⟨slTransvecG i j hij c, ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij c M a hk
  · intro r hr
    rw [sl_addCol_target_col i j hij c M r]
    exact h_dvd r hr

private lemma sl_addCol_make_dvd_chain_top
    {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ)
    (R : Finset (Fin m)) (d : Fin m → ℤ) (c : Fin m → ℤ)
    (h_dvd : ∀ r ∈ R, d r ∣ M.1 r j + c r * M.1 r i)
    {r_top : Fin m} (_ : r_top ∈ R)
    (_ : ∀ r ∈ R, d r ∣ d r_top)
    (h_chain : ∀ r ∈ R, d r ∣ c r_top - c r) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (∀ r ∈ R, d r ∣ (M * U).1 r j) := by
  refine sl_addCol_make_dvd_common i j hij M R d (c r_top) ?_
  intro r hr
  have h_sum : d r ∣ (M.1 r j + c r * M.1 r i) + (c r_top - c r) * M.1 r i :=
    dvd_add (h_dvd r hr) ((h_chain r hr).mul_right _)
  rw [show (M.1 r j + c r * M.1 r i) + (c r_top - c r) * M.1 r i
      = M.1 r j + c r_top * M.1 r i by ring] at h_sum
  exact h_sum

private lemma sl_exists_col_stab_divChain_of_lower_clearance {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol : ∀ i, N.1 i 0 = w i)
    (h_lower : ∀ i j : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ)) :
    ∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N'.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N' : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  refine ⟨N, hcol, ?_⟩
  apply diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd a ha N
  intro i j
  refine Fin.cases ?_ ?_ i
  · simp
  · intro i'
    refine Fin.cases ?_ ?_ j
    · simp only [Fin.cons_succ, Fin.cons_zero, Nat.cast_one, mul_one]
      rw [hcol i'.succ]
      exact hw_col_div i'
    · intro j'
      simp only [Fin.cons_succ]
      by_cases hij : j' < i'
      · have hcancel_int : ((a i' / a j' : ℕ) : ℤ) * (a j' : ℤ) = (a i' : ℤ) := by
          exact_mod_cast Nat.div_mul_cancel (divChain_dvd (n := k + 1) hda (le_of_lt hij))
        rw [← hcancel_int]
        exact mul_dvd_mul_right (h_lower i' j' hij) _
      · exact ((by exact_mod_cast divChain_dvd (n := k + 1) hda (not_lt.mp hij) :
          (a i' : ℤ) ∣ (a j' : ℤ))).mul_left _

private lemma sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (c : ℤ)
    (h_clear : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c * N.1 i.succ i_don)) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  let R : Finset (Fin (k + 2)) :=
    (Finset.univ.filter (fun i : Fin (k + 1) ↦ j < i)).image Fin.succ
  let d : Fin (k + 2) → ℤ := fun r ↦
    Fin.cases (0 : ℤ) (fun i' ↦ if j < i' then ((a i' / a j : ℕ) : ℤ) else 0) r
  obtain ⟨U, hU_pres, hU_div⟩ :=
    sl_addCol_make_dvd_common (m := k + 2) i_don j.succ h_don_ne N R d c
      (by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨i, hi_mem, hi_eq⟩
        rcases Finset.mem_filter.mp hi_mem with ⟨_, hi_lt⟩
        subst hi_eq
        have hd_eq : d i.succ = ((a i / a j : ℕ) : ℤ) := by
          simp [d, Fin.cases_succ, hi_lt]
        rw [hd_eq]
        exact h_clear i hi_lt)
  refine ⟨U, hU_pres, ?_⟩
  intro i hi_lt
  have hi_mem : i.succ ∈ R := by
    refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi_lt⟩
  have hd_eq : d i.succ = ((a i / a j : ℕ) : ℤ) := by
    simp [d, Fin.cases_succ, hi_lt]
  have := hU_div i.succ hi_mem
  rwa [hd_eq] at this

private lemma sl_clear_one_column_lower_divChain_of_compatible_residues
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (h_solvable : ∃ c : ℤ, ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c * N.1 i.succ i_don)) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  obtain ⟨c, h_clear⟩ := h_solvable
  exact sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue
    a ha hda j N i_don h_don_ne c h_clear

private lemma exists_chain_solution_iff_compatible
    {n : ℕ} (d : Fin n → ℤ) (_h_chain : ∀ i j : Fin n, i ≤ j → d i ∣ d j)
    (b m : Fin n → ℤ) :
    (∃ c : ℤ, ∀ i : Fin n, d i ∣ c * m i + b i) ↔
      (∃ c_per : Fin n → ℤ,
        (∀ i : Fin n, d i ∣ c_per i * m i + b i) ∧
        (∀ i j : Fin n, i ≤ j → d i ∣ c_per j - c_per i)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, hc⟩
    exact ⟨fun _ ↦ c, hc, fun i j _ ↦ by simp⟩
  · rintro ⟨c_per, h_row, h_compat⟩
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · refine ⟨0, ?_⟩
      intro i
      exact absurd i.isLt (by simp [hn0])
    · set last : Fin n := ⟨n - 1, by omega⟩
      refine ⟨c_per last, ?_⟩
      intro i
      have hi_le : i ≤ last := by
        refine Fin.mk_le_of_le_val ?_
        have : i.val ≤ n - 1 := by have := i.isLt; omega
        simpa using this
      have hsum := (h_row i).add ((h_compat i last hi_le).mul_right (m i))
      rw [show c_per i * m i + b i + (c_per last - c_per i) * m i =
          c_per last * m i + b i by ring] at hsum
      exact hsum

private lemma sl_clear_one_column_lower_divChain_of_chain_residues
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (c : Fin (k + 1) → ℤ)
    (h_per_row : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don))
    (h_chain_compat : ∀ i i' : Fin (k + 1), j < i → i ≤ i' →
      (((a i / a j : ℕ) : ℤ) ∣ c i' - c i)) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  refine sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue
    a ha hda j N i_don h_don_ne (c (Fin.last k)) ?_
  intro i hi_lt
  have hsum := (h_per_row i hi_lt).add
    ((h_chain_compat i (Fin.last k) hi_lt (Fin.le_last _)).mul_right (N.1 i.succ i_don))
  rw [show N.1 i.succ j.succ + c i * N.1 i.succ i_don +
      (c (Fin.last k) - c i) * N.1 i.succ i_don =
      N.1 i.succ j.succ + c (Fin.last k) * N.1 i.succ i_don by ring] at hsum
  exact hsum

private lemma sl_clear_one_column_step
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol : ∀ i, N.1 i 0 = w i)
    (h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
      (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ))
    (i_don : Fin (k + 2)) (h_don_ne : i_don ≠ j.succ)
    (c : Fin (k + 1) → ℤ)
    (h_per_row : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don))
    (h_chain_compat : ∀ i i' : Fin (k + 1), j < i → i ≤ i' →
      (((a i / a j : ℕ) : ℤ) ∣ c i' - c i)) :
    ∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N'.1 i 0 = w i) ∧
      (∀ i j' : Fin (k + 1), j' ≤ j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N'.1 i.succ j'.succ)) := by
  obtain ⟨U, hU_pres, hU_clear⟩ :=
    sl_clear_one_column_lower_divChain_of_chain_residues
      a ha hda j N i_don h_don_ne c h_per_row h_chain_compat
  refine ⟨N * U, ?_, ?_⟩
  · intro i
    rw [hU_pres i 0 (Fin.succ_ne_zero j).symm]
    exact hcol i
  · intro i j' hj'_le_j hj'_lt_i
    rcases lt_or_eq_of_le hj'_le_j with hlt | heq
    · have hne : j'.succ ≠ j.succ := fun h ↦ (ne_of_lt hlt) (Fin.succ_inj.mp h)
      rw [hU_pres i.succ j'.succ hne]
      exact h_prev i j' hlt hj'_lt_i
    · subst heq
      exact hU_clear i hj'_lt_i

private lemma sl_clear_all_columns_of_donor_supply
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol₀ : ∀ i, N₀.1 i 0 = w i)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ)
        (c : Fin (k + 1) → ℤ),
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don)) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ c i' - c i))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (∀ i j : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ)) := by
  suffices h : ∀ j_max : ℕ, j_max ≤ k + 1 →
      ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (∀ i, N.1 i 0 = w i) ∧
        (∀ i j' : Fin (k + 1), j'.val < j_max → j' < i →
          (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)) by
    obtain ⟨N, hcolN, hclear⟩ := h (k + 1) le_rfl
    refine ⟨N, hcolN, ?_⟩
    intro i j' hj'_lt_i
    exact hclear i j' j'.isLt hj'_lt_i
  intro j_max
  induction j_max with
  | zero =>
    intro _
    refine ⟨N₀, hcol₀, ?_⟩
    intro i j' hj' _
    exact absurd hj' (Nat.not_lt_zero _)
  | succ j_max ih =>
    intro hj_max_le
    obtain ⟨N, hcolN, hclear_prev⟩ := ih (Nat.le_of_succ_le hj_max_le)
    set j : Fin (k + 1) := ⟨j_max, Nat.lt_of_succ_le hj_max_le⟩ with hj_def
    have h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ) :=
      fun i j' hj'_lt_j hj'_lt_i ↦ hclear_prev i j' hj'_lt_j hj'_lt_i
    obtain ⟨i_don, h_don_ne, c, h_per_row, h_chain_compat⟩ :=
      h_supply j N hcolN h_prev
    obtain ⟨N', hcolN', hclear_new⟩ :=
      sl_clear_one_column_step a ha hda w j N hcolN h_prev
        i_don h_don_ne c h_per_row h_chain_compat
    refine ⟨N', hcolN', ?_⟩
    intro i j' hj'_lt_succ hj'_lt_i
    exact hclear_new i j' (Nat.lt_succ_iff.mp hj'_lt_succ) hj'_lt_i

private lemma sl_exists_col_stab_divChain_of_donor_supply {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ)
        (c : Fin (k + 1) → ℤ),
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don)) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ c i' - c i))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  obtain ⟨N, hcol_N, h_lower⟩ :=
    sl_clear_all_columns_of_donor_supply a ha hda w N₀ hcol₀ h_supply
  exact sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N hcol_N h_lower

private lemma h_supply_of_common_c {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ) (c0 : ℤ),
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c0 * N.1 i.succ i_don)) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ)
        (c : Fin (k + 1) → ℤ),
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c i * N.1 i.succ i_don)) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ c i' - c i)) := by
  intro j N hcol h_prev
  obtain ⟨i_don, h_don_ne, c0, h_clear⟩ := h_common j N hcol h_prev
  exact ⟨i_don, h_don_ne, fun _ ↦ c0, h_clear, fun _ _ _ _ ↦ by simp⟩

private lemma sl_exists_col_stab_divChain_of_common_c {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (i_don : Fin (k + 2)) (_h_don_ne : i_don ≠ j.succ) (c0 : ℤ),
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + c0 * N.1 i.succ i_don)) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
  sl_exists_col_stab_divChain_of_donor_supply a ha hda w hw_primitive hw_col_div
    (h_supply_of_common_c a ha hda w h_common)

private lemma sl_clear_one_column_lower_divChain_of_multi_donor
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (c : Fin (k + 2) → ℤ)
    (h_zero : c j.succ = 0)
    (h_clear : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ U : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ a (k' : Fin (k + 2)), k' ≠ j.succ → (N * U).1 a k' = N.1 a k') ∧
      (∀ i : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ (N * U).1 i.succ j.succ)) := by
  obtain ⟨U, hU_pres, hU_target⟩ :=
    sl_addCol_finset_target N j.succ c h_zero
  refine ⟨U, hU_pres, ?_⟩
  intro i hi_lt
  rw [hU_target i.succ]
  exact h_clear i hi_lt

private lemma sl_clear_one_column_step_multi_donor
    {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (j : Fin (k + 1))
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol : ∀ i, N.1 i 0 = w i)
    (h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
      (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ))
    (c : Fin (k + 2) → ℤ)
    (h_zero : c j.succ = 0)
    (h_clear : ∀ i : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N'.1 i 0 = w i) ∧
      (∀ i j' : Fin (k + 1), j' ≤ j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N'.1 i.succ j'.succ)) := by
  obtain ⟨U, hU_pres, hU_clear⟩ :=
    sl_clear_one_column_lower_divChain_of_multi_donor
      a ha hda j N c h_zero h_clear
  refine ⟨N * U, ?_, ?_⟩
  · intro i
    rw [hU_pres i 0 (Fin.succ_ne_zero j).symm]
    exact hcol i
  · intro i j' hj'_le_j hj'_lt_i
    rcases lt_or_eq_of_le hj'_le_j with hlt | heq
    · have hne : j'.succ ≠ j.succ := fun h ↦ (ne_of_lt hlt) (Fin.succ_inj.mp h)
      rw [hU_pres i.succ j'.succ hne]
      exact h_prev i j' hlt hj'_lt_i
    · subst heq
      exact hU_clear i hj'_lt_i

private lemma sl_clear_all_columns_of_multi_donor_supply {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hcol₀ : ∀ i, N₀.1 i 0 = w i)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c : Fin (k + 2) → ℤ), c j.succ = 0 ∧
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (∀ i j : Fin (k + 1), j < i →
        (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ)) := by
  suffices h : ∀ j_max : ℕ, j_max ≤ k + 1 →
      ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
        (∀ i, N.1 i 0 = w i) ∧
        (∀ i j' : Fin (k + 1), j'.val < j_max → j' < i →
          (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)) by
    obtain ⟨N, hcolN, hclear⟩ := h (k + 1) le_rfl
    refine ⟨N, hcolN, ?_⟩
    intro i j' hj'_lt_i
    exact hclear i j' j'.isLt hj'_lt_i
  intro j_max
  induction j_max with
  | zero =>
    intro _
    refine ⟨N₀, hcol₀, ?_⟩
    intro i j' hj' _
    exact absurd hj' (Nat.not_lt_zero _)
  | succ j_max ih =>
    intro hj_max_le
    obtain ⟨N, hcolN, hclear_prev⟩ := ih (Nat.le_of_succ_le hj_max_le)
    set j : Fin (k + 1) := ⟨j_max, Nat.lt_of_succ_le hj_max_le⟩ with hj_def
    have h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ) :=
      fun i j' hj'_lt_j hj'_lt_i ↦ hclear_prev i j' hj'_lt_j hj'_lt_i
    obtain ⟨c, h_zero, h_clear⟩ := h_supply j N hcolN h_prev
    obtain ⟨N', hcolN', hclear_new⟩ :=
      sl_clear_one_column_step_multi_donor a ha hda w j N hcolN h_prev
        c h_zero h_clear
    refine ⟨N', hcolN', ?_⟩
    intro i j' hj'_lt_succ hj'_lt_i
    exact hclear_new i j' (Nat.lt_succ_iff.mp hj'_lt_succ) hj'_lt_i

private lemma sl_exists_col_stab_divChain_of_multi_donor_supply {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_supply : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c : Fin (k + 2) → ℤ), c j.succ = 0 ∧
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k')) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  obtain ⟨N, hcol_N, h_lower⟩ :=
    sl_clear_all_columns_of_multi_donor_supply a ha hda w N₀ hcol₀ h_supply
  exact sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N hcol_N h_lower

private lemma exists_vector_chain_solution
    {n n' : ℕ} (d : Fin (n + 1) → ℤ)
    (_h_chain : ∀ a b : Fin (n + 1), a ≤ b → d a ∣ d b)
    (c_per : Fin (n + 1) → Fin n' → ℤ)
    (h_compat : ∀ a b : Fin (n + 1), a ≤ b → ∀ k : Fin n',
      d a ∣ c_per b k - c_per a k) :
    ∃ c : Fin n' → ℤ, ∀ a : Fin (n + 1), ∀ k : Fin n',
      d a ∣ c k - c_per a k := by
  exact ⟨fun k ↦ c_per (Fin.last n) k, fun a k ↦ h_compat a (Fin.last n) (Fin.le_last _) k⟩

private lemma row_clear_avoiding_of_bezout
    {n : ℕ} (x : Fin n → ℤ) (j : Fin n)
    (u : Fin n → ℤ) (h_zero : u j = 0) (h_bez : ∑ k, u k * x k = 1)
    (xj d : ℤ) :
    ∃ c : Fin n → ℤ, c j = 0 ∧ d ∣ xj + ∑ k, c k * x k := by
  refine ⟨fun k ↦ -xj * u k, by simp [h_zero], ?_⟩
  have h_sum : ∑ k, (-xj * u k) * x k = -xj := by
    simp only [mul_assoc, ← Finset.mul_sum, h_bez, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero d

private lemma h_per_row_via_avoiding_bezout {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_avoiding_compat : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (u : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, u i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', u i k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣
            (-(N.1 i'.succ j.succ) * u i' k') -
              (-(N.1 i.succ j.succ) * u i k')))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k')) := by
  intro j N hcol h_prev
  obtain ⟨u, hu_zero, hu_bez, hu_compat⟩ :=
    h_avoiding_compat j N hcol h_prev
  refine ⟨fun i k' ↦ -(N.1 i.succ j.succ) * u i k', ?_, ?_, ?_⟩
  · intro i
    simp [hu_zero i]
  · intro i hi_lt
    have h_sum : ∑ k', (-(N.1 i.succ j.succ) * u i k') * N.1 i.succ k' =
        -(N.1 i.succ j.succ) := by
      simp only [mul_assoc, ← Finset.mul_sum, hu_bez i hi_lt, mul_one]
    rw [h_sum, add_neg_cancel]
    exact dvd_zero _
  · exact hu_compat

private lemma h_supply_of_row_residues {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_per_row : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k'))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c : Fin (k + 2) → ℤ), c j.succ = 0 ∧
        ∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k') := by
  intro j N hcol h_prev
  obtain ⟨c_per, h_zero_per, h_clear_per, h_compat⟩ :=
    h_per_row j N hcol h_prev
  refine ⟨fun k' ↦ c_per (Fin.last k) k', h_zero_per (Fin.last k), ?_⟩
  intro i hi_lt
  have hdiff_sum : (((a i / a j : ℕ) : ℤ)) ∣
      ∑ k', (c_per (Fin.last k) k' - c_per i k') * N.1 i.succ k' :=
    Finset.dvd_sum fun k' _ ↦
      (h_compat i (Fin.last k) hi_lt (Fin.le_last _) k').mul_right _
  have hsum := (h_clear_per i hi_lt).add hdiff_sum
  have heq : N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k' +
      ∑ k', (c_per (Fin.last k) k' - c_per i k') * N.1 i.succ k' =
      N.1 i.succ j.succ +
        ∑ k', c_per (Fin.last k) k' * N.1 i.succ k' := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro k' _
    ring
  rw [heq] at hsum
  exact hsum

private lemma sl_exists_col_stab_divChain_of_row_residues {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_per_row : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k'))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
  sl_exists_col_stab_divChain_of_multi_donor_supply a ha hda w
    hw_primitive hw_col_div
    (h_supply_of_row_residues a ha hda w h_per_row)

private lemma h_avoiding_compat_of_common_nu {k : ℕ}
    (a : Fin (k + 1) → ℕ) (_ha : ∀ i, 0 < a i) (_hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (ν : Fin (k + 2) → ℤ),
        ν j.succ = 0 ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', ν k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (u : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, u i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', u i k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣
            (-(N.1 i'.succ j.succ) * u i' k') -
              (-(N.1 i.succ j.succ) * u i k'))) := by
  intro j N hcol h_prev
  obtain ⟨ν, hν_zero, hν_bez, hν_col⟩ := h_common j N hcol h_prev
  refine ⟨fun _ k' ↦ ν k', fun _ ↦ hν_zero, hν_bez, ?_⟩
  intro i i' hi_lt hi_le k'
  rw [show (-(N.1 i'.succ j.succ) * ν k') - (-(N.1 i.succ j.succ) * ν k')
      = -((N.1 i'.succ j.succ - N.1 i.succ j.succ) * ν k') by ring]
  exact ((hν_col i i' hi_lt hi_le).mul_right _).neg_right

private lemma h_per_row_of_common_nu {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (ν : Fin (k + 2) → ℤ),
        ν j.succ = 0 ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', ν k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ))) :
    ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (c_per : Fin (k + 1) → Fin (k + 2) → ℤ),
        (∀ i, c_per i j.succ = 0) ∧
        (∀ i : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            N.1 i.succ j.succ + ∑ k', c_per i k' * N.1 i.succ k')) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' → ∀ k' : Fin (k + 2),
          (((a i / a j : ℕ) : ℤ) ∣ c_per i' k' - c_per i k')) :=
  h_per_row_via_avoiding_bezout a ha hda w
    (h_avoiding_compat_of_common_nu a ha hda w h_common)

private lemma sl_exists_col_stab_divChain_of_common_nu {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_common : ∀ (j : Fin (k + 1))
      (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
      (_hcol : ∀ i, N.1 i 0 = w i)
      (_h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ)),
      ∃ (ν : Fin (k + 2) → ℤ),
        ν j.succ = 0 ∧
        (∀ i : Fin (k + 1), j < i → ∑ k', ν k' * N.1 i.succ k' = 1) ∧
        (∀ i i' : Fin (k + 1), j < i → i ≤ i' →
          (((a i / a j : ℕ) : ℤ) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ))) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H :=
  sl_exists_col_stab_divChain_of_row_residues a ha hda w hw_primitive hw_col_div
    (h_per_row_of_common_nu a ha hda w h_common)

/-- **Base case `k = 0`.** At dim 2, the lower-clearance condition is vacuous
(no `i, j : Fin 1` with `j < i`), so the conclusion follows immediately from
`sl_exists_col_of_primitive` and `sl_exists_col_stab_divChain_of_lower_clearance`. -/
lemma sl_exists_col_stab_divChain_zero
    (a : Fin 1 → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain 1 a)
    (w : Fin 2 → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin 1, (a i : ℤ) ∣ w i.succ) :
    ∃ N : SpecialLinearGroup (Fin 2) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat 2 (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin 2) ℚ) *
        diagMat 2 (Fin.cons 1 a) ∈ (GL_pair 2).H := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  refine sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N₀ hcol₀ ?_
  intro i j hji
  simp only [Fin.lt_def, Nat.lt_one_iff.mp j.isLt, Nat.lt_one_iff.mp i.isLt,
    lt_irrefl] at hji

/-- **Strengthened completion target.**  An `N ∈ SL_{k+2}(ℤ)` with prescribed
first column `w` AND with strictly-lower-triangular entries (below the leading
column) satisfying the `a i / a j` divisibility chain.  This is exactly the
data consumed by `sl_exists_col_stab_divChain_of_lower_clearance`. -/
def StrengthenedCompletionTarget {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ) : Prop :=
  ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
    (∀ i, N.1 i 0 = w i) ∧
    (∀ i j : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣ N.1 i.succ j.succ))

/-- **Conditional reduction.**  If a `StrengthenedCompletionTarget` exists for
`(a, w)`, then the desired stabilizer-membership conclusion of
`sl_exists_col_stab_divChain` holds.  This isolates the remaining blocker as
the structured-completion existence problem. -/
lemma sl_exists_col_stab_divChain_of_strengthened_completion {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h_completion : StrengthenedCompletionTarget a w) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨N, hcol, h_lower⟩ := h_completion
  exact sl_exists_col_stab_divChain_of_lower_clearance a ha hda w hw_col_div
    N hcol h_lower

private lemma exists_diagonal_of_posdet_for_lower_block {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ) (d : Fin n → ℤ),
      (∀ i, 0 < d i) ∧
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
        Matrix.diagonal d := by
  obtain ⟨d, hd_pos, L, R, hLR⟩ := exists_diagonal_of_posdet (n := n) A hdet
  exact ⟨L, R, d, hd_pos, hLR⟩

end HeckeRing.GLn
