/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.SLReduction

/-!
# Block Embedding Bijection: trailing-block HNF and column-HNF construction (`sl_exists_col_stab_divChain`)
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

private lemma slSuccEmbed_preserves_col_zero {k : ℕ}
    (R : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ) (i : Fin (k + 2)) :
    (N₀ * slSuccEmbed R).1 i 0 = N₀.1 i 0 := by
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  rw [slSuccEmbed_val_zero_zero, mul_one]
  have hzero : ∀ j : Fin (k + 1),
      N₀.1 i j.succ * (slSuccEmbed R).1 j.succ 0 = 0 := by
    intro j; rw [slSuccEmbed_val_succ_zero]; ring
  simp [hzero]

private def bezout2 (x y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (Int.gcd x y : ℤ) = 0 then 1 else
  !![Int.gcdA x y, -y / (Int.gcd x y : ℤ);
     Int.gcdB x y,  x / (Int.gcd x y : ℤ)]

private lemma bezout2_action_col0 (x y : ℤ) :
    x * (bezout2 x y) 0 0 + y * (bezout2 x y) 1 0 = (Int.gcd x y : ℤ) := by
  unfold bezout2
  by_cases hg : (Int.gcd x y : ℤ) = 0
  · rw [if_pos hg]
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at hg
    simp [hg.1, hg.2]
  · rw [if_neg hg]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
    have := Int.gcd_eq_gcd_ab x y
    linarith

private lemma bezout2_action_col1 (x y : ℤ) :
    x * (bezout2 x y) 0 1 + y * (bezout2 x y) 1 1 = 0 := by
  unfold bezout2
  by_cases hg : (Int.gcd x y : ℤ) = 0
  · rw [if_pos hg]
    rw [Int.natCast_eq_zero, Int.gcd_eq_zero_iff] at hg
    simp [hg.1, hg.2]
  · rw [if_neg hg]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
    have hxg : (Int.gcd x y : ℤ) ∣ x := Int.gcd_dvd_left x y
    have hyg : (Int.gcd x y : ℤ) ∣ y := Int.gcd_dvd_right x y
    set g : ℤ := (Int.gcd x y : ℤ) with hg_def
    obtain ⟨a, ha⟩ := hxg
    obtain ⟨b, hb⟩ := hyg
    rw [ha, hb, show -(g * b) = g * (-b) by ring,
        Int.mul_ediv_cancel_left _ hg, Int.mul_ediv_cancel_left _ hg]
    ring

private lemma bezout2_det (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    (bezout2 x y).det = 1 := by
  unfold bezout2
  rw [if_neg hg, Matrix.det_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
  have hxg : (Int.gcd x y : ℤ) ∣ x := Int.gcd_dvd_left x y
  have hyg : (Int.gcd x y : ℤ) ∣ y := Int.gcd_dvd_right x y
  have hbez := Int.gcd_eq_gcd_ab x y
  set g : ℤ := (Int.gcd x y : ℤ) with hg_def
  obtain ⟨a, ha⟩ := hxg
  obtain ⟨b, hb⟩ := hyg
  have hbez' : g * (Int.gcdA x y * a + Int.gcdB x y * b) = g * 1 := by
    rw [mul_one, mul_add]
    calc g * (Int.gcdA x y * a) + g * (Int.gcdB x y * b)
        = (g * a) * Int.gcdA x y + (g * b) * Int.gcdB x y := by ring
      _ = x * Int.gcdA x y + y * Int.gcdB x y := by rw [← ha, ← hb]
      _ = g := by linarith [hbez]
  have h1 : Int.gcdA x y * a + Int.gcdB x y * b = 1 := mul_left_cancel₀ hg hbez'
  rw [ha, hb, show -(g * b) = g * (-b) by ring,
      Int.mul_ediv_cancel_left _ hg, Int.mul_ediv_cancel_left _ hg]
  rw [← ha, ← hb]
  linarith

private noncomputable def bezout2SL (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    SpecialLinearGroup (Fin 2) ℤ :=
  ⟨bezout2 x y, bezout2_det x y hg⟩

private noncomputable def bezout2TrailingSL : (r : ℕ) → (x y : ℤ) →
    ((Int.gcd x y : ℤ) ≠ 0) → SpecialLinearGroup (Fin (r + 2)) ℤ
  | 0,     x, y, hg => bezout2SL x y hg
  | r + 1, x, y, hg => slSuccEmbed (bezout2TrailingSL r x y hg)

private lemma bezout2TrailingSL_zero (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    bezout2TrailingSL 0 x y hg = bezout2SL x y hg := rfl

private lemma bezout2TrailingSL_succ (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) :
    bezout2TrailingSL (r + 1) x y hg =
      slSuccEmbed (bezout2TrailingSL r x y hg) := rfl

private lemma bezout2TrailingSL_val_natAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i j : Fin 2) :
    (bezout2TrailingSL r x y hg).val (Fin.natAdd r i) (Fin.natAdd r j) =
      bezout2 x y i j := by
  induction r with
  | zero =>
    have hi : (Fin.natAdd 0 i : Fin (0 + 2)) = i := by ext; simp [Fin.natAdd]
    have hj : (Fin.natAdd 0 j : Fin (0 + 2)) = j := by ext; simp [Fin.natAdd]
    rw [hi, hj, bezout2TrailingSL_zero]
    rfl
  | succ r ih =>
    have hi : (Fin.natAdd (r + 1) i : Fin (r + 1 + 2)) = (Fin.natAdd r i).succ := by
      ext; simp [Fin.natAdd, Fin.succ]; ring
    have hj : (Fin.natAdd (r + 1) j : Fin (r + 1 + 2)) = (Fin.natAdd r j).succ := by
      ext; simp [Fin.natAdd, Fin.succ]; ring
    rw [bezout2TrailingSL_succ, hi, hj, slSuccEmbed_val_succ_succ, ih]

private lemma bezout2TrailingSL_val_castAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i j : Fin r) :
    (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 i) (Fin.castAdd 2 j) =
      if i = j then 1 else 0 := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
    · rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        show (slSuccEmbed _).val (Fin.castAdd 2 (0 : Fin (r+1)))
          (Fin.castAdd 2 (0 : Fin (r+1))) = _
        have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
          ext; simp [Fin.castAdd]
        rw [h0, slSuccEmbed_val_zero_zero]
        simp
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
          ext; simp [Fin.castAdd]
        have hsucc : (Fin.castAdd 2 j'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 j').succ := by ext; simp [Fin.castAdd, Fin.succ]
        rw [h0, hsucc, slSuccEmbed_val_zero_succ]
        exact (if_neg (Fin.succ_ne_zero j').symm).symm
    · rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
          ext; simp [Fin.castAdd]
        have hsucc : (Fin.castAdd 2 i'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 i').succ := by ext; simp [Fin.castAdd, Fin.succ]
        rw [h0, hsucc, slSuccEmbed_val_succ_zero]
        have : i'.succ ≠ 0 := Fin.succ_ne_zero _
        simp [this]
      · subst hi; subst hj
        rw [bezout2TrailingSL_succ]
        have hsucci : (Fin.castAdd 2 i'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 i').succ := by ext; simp [Fin.castAdd, Fin.succ]
        have hsuccj : (Fin.castAdd 2 j'.succ : Fin (r + 1 + 2)) =
            (Fin.castAdd 2 j').succ := by ext; simp [Fin.castAdd, Fin.succ]
        rw [hsucci, hsuccj, slSuccEmbed_val_succ_succ, ih]
        by_cases h : i' = j' <;> simp [h, Fin.succ_inj]

private lemma bezout2TrailingSL_val_castAdd_natAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i : Fin r) (j : Fin 2) :
    (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 i) (Fin.natAdd r j) = 0 := by
  induction r with
  | zero => exact i.elim0
  | succ r ih =>
    rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
    · subst hi
      rw [bezout2TrailingSL_succ]
      have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
        ext; simp [Fin.castAdd]
      have hjs : (Fin.natAdd (r + 1) j : Fin (r + 1 + 2)) = (Fin.natAdd r j).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [h0, hjs, slSuccEmbed_val_zero_succ]
    · subst hi
      rw [bezout2TrailingSL_succ]
      have hsucci : (Fin.castAdd 2 i'.succ : Fin (r + 1 + 2)) =
          (Fin.castAdd 2 i').succ := by ext; simp [Fin.castAdd, Fin.succ]
      have hjs : (Fin.natAdd (r + 1) j : Fin (r + 1 + 2)) = (Fin.natAdd r j).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [hsucci, hjs, slSuccEmbed_val_succ_succ, ih]

private lemma bezout2TrailingSL_val_natAdd_castAdd (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) (i : Fin 2) (j : Fin r) :
    (bezout2TrailingSL r x y hg).val (Fin.natAdd r i) (Fin.castAdd 2 j) = 0 := by
  induction r with
  | zero => exact j.elim0
  | succ r ih =>
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
    · subst hj
      rw [bezout2TrailingSL_succ]
      have h0 : (Fin.castAdd 2 (0 : Fin (r + 1)) : Fin (r + 1 + 2)) = 0 := by
        ext; simp [Fin.castAdd]
      have his : (Fin.natAdd (r + 1) i : Fin (r + 1 + 2)) = (Fin.natAdd r i).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [h0, his, slSuccEmbed_val_succ_zero]
    · subst hj
      rw [bezout2TrailingSL_succ]
      have hsuccj : (Fin.castAdd 2 j'.succ : Fin (r + 1 + 2)) =
          (Fin.castAdd 2 j').succ := by ext; simp [Fin.castAdd, Fin.succ]
      have his : (Fin.natAdd (r + 1) i : Fin (r + 1 + 2)) = (Fin.natAdd r i).succ := by
        ext; simp [Fin.natAdd, Fin.succ]; ring
      rw [hsuccj, his, slSuccEmbed_val_succ_succ, ih]

private lemma row_mul_bezout2TrailingSL_natAdd_zero {n r : ℕ} (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ) (i : Fin n)
    (hxx : M i (Fin.natAdd r 0) = x) (hyy : M i (Fin.natAdd r 1) = y) :
    (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 0) =
      (Int.gcd x y : ℤ) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have hcast : ∑ k : Fin r,
      M i (Fin.castAdd 2 k) *
        (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
  have hnat : ∑ k : Fin 2,
      M i (Fin.natAdd r k) *
        (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 0) =
        (Int.gcd x y : ℤ) := by
    rw [Fin.sum_univ_two]
    rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd, hxx, hyy]
    exact bezout2_action_col0 x y
  rw [hcast, hnat, zero_add]

private lemma row_mul_bezout2TrailingSL_natAdd_one {n r : ℕ} (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ) (i : Fin n)
    (hxx : M i (Fin.natAdd r 0) = x) (hyy : M i (Fin.natAdd r 1) = y) :
    (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 1) = 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have hcast : ∑ k : Fin r,
      M i (Fin.castAdd 2 k) *
        (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 1) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
  have hnat : ∑ k : Fin 2,
      M i (Fin.natAdd r k) *
        (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 1) = 0 := by
    rw [Fin.sum_univ_two]
    rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd, hxx, hyy]
    exact bezout2_action_col1 x y
  rw [hcast, hnat, zero_add]

private lemma col_mul_bezout2TrailingSL_castAdd {n r : ℕ} (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ) (i : Fin n) (j : Fin r) :
    (M * (bezout2TrailingSL r x y hg).val) i (Fin.castAdd 2 j) =
      M i (Fin.castAdd 2 j) := by
  rw [Matrix.mul_apply, Fin.sum_univ_add]
  have hcast : ∑ k : Fin r,
      M i (Fin.castAdd 2 k) *
        (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.castAdd 2 j) =
        M i (Fin.castAdd 2 j) := by
    rw [Finset.sum_eq_single j]
    · rw [bezout2TrailingSL_val_castAdd, if_pos rfl, mul_one]
    · intro k _ hk
      rw [bezout2TrailingSL_val_castAdd, if_neg hk, mul_zero]
    · intro hj
      exact (hj (Finset.mem_univ _)).elim
  have hnat : ∑ k : Fin 2,
      M i (Fin.natAdd r k) *
        (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.castAdd 2 j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [bezout2TrailingSL_val_natAdd_castAdd, mul_zero]
  rw [hcast, hnat, add_zero]

private def TrailingBlockHNFData {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ) : Prop :=
  ∃ (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (R : SpecialLinearGroup (Fin (k + 1)) ℤ),
    (∀ i, N₀.1 i 0 = w i) ∧
    (∀ i j : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣
        ∑ k' : Fin (k + 1), N₀.1 i.succ k'.succ * R.1 k' j))

private lemma strengthenedCompletionTarget_of_trailing_hnf_data {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ)
    (h : TrailingBlockHNFData a w) :
    StrengthenedCompletionTarget a w := by
  obtain ⟨N₀, R, hcol₀, h_div⟩ := h
  refine ⟨N₀ * slSuccEmbed R, ?_, ?_⟩
  · intro i
    rw [slSuccEmbed_preserves_col_zero R N₀ i]
    exact hcol₀ i
  · intro i j hji
    have hentry :
        (N₀ * slSuccEmbed R).1 i.succ j.succ =
          ∑ k' : Fin (k + 1), N₀.1 i.succ k'.succ * R.1 k' j := by
      simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      rw [Fin.sum_univ_succ]
      rw [slSuccEmbed_val_zero_succ, mul_zero, zero_add]
      refine Finset.sum_congr rfl ?_
      intro k' _
      rw [slSuccEmbed_val_succ_succ]
    rw [hentry]
    exact h_div i j hji

private lemma sl_exists_col_stab_divChain_of_trailing_hnf_data {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ)
    (h : TrailingBlockHNFData a w) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  exact sl_exists_col_stab_divChain_of_strengthened_completion a ha hda w hw_col_div
    (strengthenedCompletionTarget_of_trailing_hnf_data a w h)

private lemma trailingBlockHNFData_of_strengthenedCompletionTarget {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ)
    (h : StrengthenedCompletionTarget a w) :
    TrailingBlockHNFData a w := by
  obtain ⟨N, hcol, h_div⟩ := h
  refine ⟨N, 1, hcol, ?_⟩
  intro i j hji
  have hsum :
      ∑ k' : Fin (k + 1), N.1 i.succ k'.succ *
          (1 : SpecialLinearGroup (Fin (k + 1)) ℤ).1 k' j =
        N.1 i.succ j.succ := by
    simp [SpecialLinearGroup.coe_one, Matrix.one_apply, Finset.sum_ite_eq']
  rw [hsum]
  exact h_div i j hji

private lemma trailingBlockHNFData_of_R_existence {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (h_R : ∀ N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N₀.1 i 0 = w i) →
      ∃ R : SpecialLinearGroup (Fin (k + 1)) ℤ,
        ∀ i j : Fin (k + 1), j < i →
          (((a i / a j : ℕ) : ℤ) ∣
            ∑ k' : Fin (k + 1), N₀.1 i.succ k'.succ * R.1 k' j)) :
    TrailingBlockHNFData a w := by
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
  obtain ⟨R, hR⟩ := h_R N₀ hcol₀
  exact ⟨N₀, R, hcol₀, hR⟩

private lemma matrix_mul_bezout2TrailingSL_apply {n r : ℕ}
    (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0)
    (M : Matrix (Fin n) (Fin (r + 2)) ℤ)
    (i_target : Fin n)
    (hxx : M i_target (Fin.natAdd r 0) = x)
    (hyy : M i_target (Fin.natAdd r 1) = y) :
    (M * (bezout2TrailingSL r x y hg).val) i_target (Fin.natAdd r 0) =
        (Int.gcd x y : ℤ) ∧
    (M * (bezout2TrailingSL r x y hg).val) i_target (Fin.natAdd r 1) = 0 ∧
    (∀ i : Fin n, ∀ j : Fin r,
      (M * (bezout2TrailingSL r x y hg).val) i (Fin.castAdd 2 j) =
        M i (Fin.castAdd 2 j)) ∧
    (∀ i : Fin n,
      (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 0) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 0 +
        M i (Fin.natAdd r 1) * (bezout2 x y) 1 0) ∧
    (∀ i : Fin n,
      (M * (bezout2TrailingSL r x y hg).val) i (Fin.natAdd r 1) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 1 +
        M i (Fin.natAdd r 1) * (bezout2 x y) 1 1) := by
  refine ⟨row_mul_bezout2TrailingSL_natAdd_zero x y hg M i_target hxx hyy,
          row_mul_bezout2TrailingSL_natAdd_one  x y hg M i_target hxx hyy,
          fun i j ↦ col_mul_bezout2TrailingSL_castAdd x y hg M i j,
          ?_, ?_⟩
  · intro i
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    have hcast : ∑ k : Fin r,
        M i (Fin.castAdd 2 k) *
          (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 0) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
    have hnat : ∑ k : Fin 2,
        M i (Fin.natAdd r k) *
          (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 0) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 0 +
          M i (Fin.natAdd r 1) * (bezout2 x y) 1 0 := by
      rw [Fin.sum_univ_two]
      rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd]
    rw [hcast, hnat, zero_add]
  · intro i
    rw [Matrix.mul_apply, Fin.sum_univ_add]
    have hcast : ∑ k : Fin r,
        M i (Fin.castAdd 2 k) *
          (bezout2TrailingSL r x y hg).val (Fin.castAdd 2 k) (Fin.natAdd r 1) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [bezout2TrailingSL_val_castAdd_natAdd, mul_zero]
    have hnat : ∑ k : Fin 2,
        M i (Fin.natAdd r k) *
          (bezout2TrailingSL r x y hg).val (Fin.natAdd r k) (Fin.natAdd r 1) =
        M i (Fin.natAdd r 0) * (bezout2 x y) 0 1 +
          M i (Fin.natAdd r 1) * (bezout2 x y) 1 1 := by
      rw [Fin.sum_univ_two]
      rw [bezout2TrailingSL_val_natAdd, bezout2TrailingSL_val_natAdd]
    rw [hcast, hnat, zero_add]

private lemma N₀_mul_slSuccEmbed_apply_succ_succ {r : ℕ}
    (N₀ : SpecialLinearGroup (Fin (r + 3)) ℤ)
    (U : SpecialLinearGroup (Fin (r + 2)) ℤ)
    (i j : Fin (r + 2)) :
    (N₀ * slSuccEmbed U).1 i.succ j.succ =
      ∑ k' : Fin (r + 2), N₀.1 i.succ k'.succ * U.val k' j := by
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  rw [Fin.sum_univ_succ]
  rw [slSuccEmbed_val_zero_succ, mul_zero, zero_add]
  refine Finset.sum_congr rfl ?_
  intro k' _
  rw [slSuccEmbed_val_succ_succ]

private lemma sl_mul_slSuccEmbed_bezout2TrailingSL_apply {r : ℕ}
    (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0)
    (N₀ : SpecialLinearGroup (Fin (r + 3)) ℤ)
    (i_target : Fin (r + 2))
    (hxx : N₀.1 i_target.succ (Fin.natAdd r 0).succ = x)
    (hyy : N₀.1 i_target.succ (Fin.natAdd r 1).succ = y) :
    let N₁ := N₀ * slSuccEmbed (bezout2TrailingSL r x y hg)
    (∀ i : Fin (r + 3), N₁.1 i 0 = N₀.1 i 0) ∧
    (∀ i : Fin (r + 2), ∀ j : Fin r,
      N₁.1 i.succ (Fin.castAdd 2 j).succ = N₀.1 i.succ (Fin.castAdd 2 j).succ) ∧
    N₁.1 i_target.succ (Fin.natAdd r 0).succ = (Int.gcd x y : ℤ) ∧
    N₁.1 i_target.succ (Fin.natAdd r 1).succ = 0 ∧
    (∀ i : Fin (r + 2),
      N₁.1 i.succ (Fin.natAdd r 0).succ =
        N₀.1 i.succ (Fin.natAdd r 0).succ * (bezout2 x y) 0 0 +
        N₀.1 i.succ (Fin.natAdd r 1).succ * (bezout2 x y) 1 0) ∧
    (∀ i : Fin (r + 2),
      N₁.1 i.succ (Fin.natAdd r 1).succ =
        N₀.1 i.succ (Fin.natAdd r 0).succ * (bezout2 x y) 0 1 +
        N₀.1 i.succ (Fin.natAdd r 1).succ * (bezout2 x y) 1 1) := by
  set M : Matrix (Fin (r + 2)) (Fin (r + 2)) ℤ :=
    Matrix.of (fun i j ↦ N₀.1 i.succ j.succ) with hM_def
  have hbridge : ∀ i j : Fin (r + 2),
      (N₀ * slSuccEmbed (bezout2TrailingSL r x y hg)).1 i.succ j.succ =
        (M * (bezout2TrailingSL r x y hg).val) i j := by
    intro i j
    rw [N₀_mul_slSuccEmbed_apply_succ_succ]
    simp [Matrix.mul_apply, hM_def]
  have hxx' : M i_target (Fin.natAdd r 0) = x := by simpa [hM_def] using hxx
  have hyy' : M i_target (Fin.natAdd r 1) = y := by simpa [hM_def] using hyy
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    matrix_mul_bezout2TrailingSL_apply x y hg M i_target hxx' hyy'
  refine ⟨?col0, ?cast, ?nat0, ?nat1, ?lin0, ?lin1⟩
  · intro i
    exact slSuccEmbed_preserves_col_zero (bezout2TrailingSL r x y hg) N₀ i
  · intro i j
    have := h3 i j
    rw [hbridge i (Fin.castAdd 2 j)]
    simpa [hM_def] using this
  · rw [hbridge i_target (Fin.natAdd r 0)]; exact h1
  · rw [hbridge i_target (Fin.natAdd r 1)]; exact h2
  · intro i
    have := h4 i
    rw [hbridge i (Fin.natAdd r 0)]
    simpa [hM_def] using this
  · intro i
    have := h5 i
    rw [hbridge i (Fin.natAdd r 1)]
    simpa [hM_def] using this

private lemma exists_sl2_first_col_orthogonal (x y : ℤ) :
    ∃ R : SpecialLinearGroup (Fin 2) ℤ, x * R.1 0 0 + y * R.1 1 0 = 0 := by
  by_cases hxy : x = 0 ∧ y = 0
  · refine ⟨1, ?_⟩
    obtain ⟨hx, hy⟩ := hxy
    rw [hx, hy]; ring
  · push_neg at hxy
    have hg_pos_nat : 0 < Int.gcd x y := by
      rcases Nat.eq_zero_or_pos (Int.gcd x y) with h0 | hpos
      · rw [Int.gcd_eq_zero_iff] at h0
        exact absurd h0.2 (hxy h0.1)
      · exact hpos
    set g : ℤ := (Int.gcd x y : ℤ) with hg_def
    have hg_ne : g ≠ 0 := by
      show (Int.gcd x y : ℤ) ≠ 0
      exact_mod_cast hg_pos_nat.ne'
    have hg_dvd_x : g ∣ x := Int.gcd_dvd_left _ _
    have hg_dvd_y : g ∣ y := Int.gcd_dvd_right _ _
    obtain ⟨p, hxp⟩ := hg_dvd_x
    obtain ⟨q, hyq⟩ := hg_dvd_y
    have hpq_cop : Int.gcd p q = 1 := by
      have h1 : x / g = p := by rw [hxp]; exact Int.mul_ediv_cancel_left _ hg_ne
      have h2 : y / g = q := by rw [hyq]; exact Int.mul_ediv_cancel_left _ hg_ne
      have hkey := Int.gcd_div_gcd_div_gcd hg_pos_nat
      rw [h1, h2] at hkey
      exact hkey
    have hcop_pq : IsCoprime p q := Int.isCoprime_iff_gcd_eq_one.mpr hpq_cop
    have hcop : IsCoprime q (-p) := hcop_pq.symm.neg_right
    obtain ⟨R, hR0, hR1⟩ := IsCoprime.exists_SL2_col hcop 0
    refine ⟨R, ?_⟩
    have h_R0 : R.1 0 0 = q := hR0
    have h_R1 : R.1 1 0 = -p := hR1
    rw [h_R0, h_R1, hxp, hyq]; ring

private lemma sl_exists_col_stab_divChain_one
    (a : Fin 2 → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain 2 a)
    (w : Fin 3 → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin 2, (a i : ℤ) ∣ w i.succ) :
    ∃ N : SpecialLinearGroup (Fin 3) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat 3 (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin 3) ℚ) *
        diagMat 3 (Fin.cons 1 a) ∈ (GL_pair 3).H := by
  refine sl_exists_col_stab_divChain_of_trailing_hnf_data a ha hda w hw_col_div ?_
  obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive (n := 1) w hw_primitive
  obtain ⟨R, hR_eq⟩ :=
    exists_sl2_first_col_orthogonal (N₀.1 2 1) (N₀.1 2 2)
  refine ⟨N₀, R, hcol₀, ?_⟩
  intro i j hji
  have hi_one : i = 1 := by
    fin_cases i
    · exact absurd hji (Fin.not_lt_zero _)
    · rfl
  subst hi_one
  have hj_zero : j = 0 := by
    fin_cases j
    · rfl
    · exact absurd hji (lt_irrefl _)
  subst hj_zero
  have h_sum : ∑ k' : Fin 2, N₀.1 ((1 : Fin 2).succ) k'.succ * R.1 k' 0 =
      N₀.1 2 1 * R.1 0 0 + N₀.1 2 2 * R.1 1 0 := by
    rw [Fin.sum_univ_two]; rfl
  rw [h_sum, hR_eq]
  exact dvd_zero _

private lemma exists_nonzero_kernel_vec {m : ℕ}
    (N : Matrix (Fin (m + 1)) (Fin (m + 2)) ℤ) :
    ∃ v : Fin (m + 2) → ℤ,
      v ≠ 0 ∧ (∀ i : Fin (m + 1), ∑ j, N i j * v j = 0) := by
  let L : (Fin (m + 2) → ℤ) →ₗ[ℤ] (Fin (m + 1) → ℤ) := N.mulVecLin
  have hker_ne : LinearMap.ker L ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective L := LinearMap.ker_eq_bot.mp hbot
    have h_le : Module.finrank ℤ (Fin (m + 2) → ℤ) ≤
        Module.finrank ℤ (Fin (m + 1) → ℤ) :=
      LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_fin_fun, Module.finrank_fin_fun] at h_le
    omega
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker_ne
  refine ⟨v, hv_ne, ?_⟩
  intro i
  have h_Lv : L v = 0 := LinearMap.mem_ker.mp hv_mem
  have h_app : (N *ᵥ v) i = (0 : Fin (m + 1) → ℤ) i := by
    show (L v) i = (0 : Fin (m + 1) → ℤ) i
    exact congrFun h_Lv i
  simpa [Matrix.mulVec, dotProduct] using h_app

private lemma exists_primitive_kernel_vec {m : ℕ}
    (N : Matrix (Fin (m + 1)) (Fin (m + 2)) ℤ) :
    ∃ v : Fin (m + 2) → ℤ,
      (∀ d : ℤ, (∀ i, d ∣ v i) → IsUnit d) ∧
      (∀ i : Fin (m + 1), ∑ j, N i j * v j = 0) := by
  obtain ⟨v, hv_ne, hv_kernel⟩ := exists_nonzero_kernel_vec N
  set g : ℤ := Finset.univ.gcd v with hg_def
  have hg_dvd : ∀ j, g ∣ v j := fun j ↦ Finset.gcd_dvd (Finset.mem_univ j)
  have hg_ne_zero : g ≠ 0 := by
    intro hg0
    apply hv_ne
    funext j
    have hgvj : g ∣ v j := hg_dvd j
    rw [hg0] at hgvj
    exact zero_dvd_iff.mp hgvj
  refine ⟨fun j ↦ v j / g, ?_, ?_⟩
  · intro d hd
    have hdg_dvd_v : ∀ j, d * g ∣ v j := by
      intro j
      have hvj_eq : v j = g * (v j / g) := (Int.mul_ediv_cancel' (hg_dvd j)).symm
      rw [hvj_eq, mul_comm d g]
      exact mul_dvd_mul_left g (hd j)
    have hdg_dvd_g : d * g ∣ g :=
      Finset.dvd_gcd (fun j _ ↦ hdg_dvd_v j)
    have hd_dvd_one : d ∣ 1 := by
      have hone : d * g ∣ 1 * g := by rwa [one_mul]
      exact (mul_dvd_mul_iff_right hg_ne_zero).mp hone
    exact isUnit_of_dvd_one hd_dvd_one
  · intro i
    show ∑ j : Fin (m + 2), N i j * (v j / g) = 0
    have hLHS_g :
        g * (∑ j, N i j * (v j / g)) = 0 := by
      rw [Finset.mul_sum]
      have h_term : ∀ j ∈ (Finset.univ : Finset (Fin (m + 2))),
          g * (N i j * (v j / g)) = N i j * v j := by
        intro j _
        have h_cancel : g * (v j / g) = v j := Int.mul_ediv_cancel' (hg_dvd j)
        calc g * (N i j * (v j / g))
            = N i j * (g * (v j / g)) := by ring
          _ = N i j * v j := by rw [h_cancel]
      rw [Finset.sum_congr rfl h_term]
      exact hv_kernel i
    have h_eq : g * (∑ j, N i j * (v j / g)) = g * 0 := by rw [mul_zero]; exact hLHS_g
    exact mul_left_cancel₀ hg_ne_zero h_eq

private lemma exists_sl_clear_col_zero {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) ℤ) :
    ∃ R : SpecialLinearGroup (Fin (n + 2)) ℤ,
      ∀ i : Fin (n + 1), (M * R.val) i.succ 0 = 0 := by
  obtain ⟨v, hv_prim, hv_kernel⟩ :=
    exists_primitive_kernel_vec (fun (i : Fin (n + 1)) (j : Fin (n + 2)) ↦ M i.succ j)
  obtain ⟨R, hR⟩ := sl_exists_col_of_primitive v hv_prim
  refine ⟨R, ?_⟩
  intro i
  rw [Matrix.mul_apply]
  have h_sum_eq :
      ∑ k : Fin (n + 2), M i.succ k * R.val k 0 =
      ∑ k : Fin (n + 2), M i.succ k * v k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hR k]
  rw [h_sum_eq]
  exact hv_kernel i

private lemma exists_sl_upperTri_two (M : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ R : SpecialLinearGroup (Fin 2) ℤ,
      ∀ i j : Fin 2, j < i → (M * R.val) i j = 0 := by
  obtain ⟨R, hR⟩ := exists_sl2_first_col_orthogonal (M 1 0) (M 1 1)
  refine ⟨R, ?_⟩
  intro i j hji
  have hi : i = 1 := by
    fin_cases i
    · exact absurd hji (Fin.not_lt_zero _)
    · rfl
  subst hi
  have hj : j = 0 := by
    fin_cases j
    · rfl
    · exact absurd hji (lt_irrefl _)
  subst hj
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact hR

private lemma exists_sl_upperTri_succ_of_clear_tail {n : ℕ}
    (M : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ)
    (R₁ : SpecialLinearGroup (Fin (n + 3)) ℤ)
    (hR₁ : ∀ i : Fin (n + 2), (M * R₁.val) i.succ 0 = 0)
    (R' : SpecialLinearGroup (Fin (n + 2)) ℤ)
    (hR' : ∀ i j : Fin (n + 2), j < i →
      (Matrix.of (fun (i k' : Fin (n + 2)) ↦ (M * R₁.val) i.succ k'.succ) * R'.val) i j = 0) :
    ∃ R : SpecialLinearGroup (Fin (n + 3)) ℤ,
      ∀ i j : Fin (n + 3), j < i → (M * R.val) i j = 0 := by
  refine ⟨R₁ * slSuccEmbed R', ?_⟩
  intro i j hji
  show (M * (R₁ * slSuccEmbed R').val) i j = 0
  rw [SpecialLinearGroup.coe_mul, ← Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
  rcases Fin.eq_zero_or_eq_succ i with hi | ⟨i', hi⟩
  · subst hi; exact absurd hji (Fin.not_lt_zero _)
  · subst hi
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
    · subst hj
      simp only [slSuccEmbed_val_zero_zero, mul_one, slSuccEmbed_val_succ_zero,
        mul_zero, Finset.sum_const_zero, add_zero]
      exact hR₁ i'
    · subst hj
      simp only [slSuccEmbed_val_zero_succ, mul_zero, zero_add,
        slSuccEmbed_val_succ_succ]
      have hji_sub : j' < i' := by
        have h1 : j'.succ.val < i'.succ.val := hji
        simp only [Fin.val_succ] at h1
        exact Fin.lt_def.mpr (by omega)
      have h_sum_eq :
          ∑ k' : Fin (n + 2),
            (M * R₁.val) i'.succ k'.succ * R'.val k' j' =
          (Matrix.of (fun (i k' : Fin (n + 2)) ↦ (M * R₁.val) i.succ k'.succ) * R'.val) i' j' := by
        simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [h_sum_eq, hR' i' j' hji_sub]

private lemma sl_upperTri_for_matrix : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ),
    ∃ R : SpecialLinearGroup (Fin n) ℤ,
      ∀ i j : Fin n, j < i → (M * R.val) i j = 0
  | 0, _M => ⟨1, fun i _ _ ↦ i.elim0⟩
  | 1, _M => ⟨1, by
      intro i j hji
      have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
      have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
      have : ¬ j < i := by
        rw [Fin.lt_def, hi, hj]; exact lt_irrefl _
      exact absurd hji this⟩
  | 2, M => exists_sl_upperTri_two M
  | n + 3, M => by
      obtain ⟨R₁, hR₁⟩ := exists_sl_clear_col_zero M
      obtain ⟨R', hR'⟩ :=
        sl_upperTri_for_matrix (Matrix.of (fun (i k' : Fin (n + 2)) ↦ (M * R₁.val) i.succ k'.succ))
      exact exists_sl_upperTri_succ_of_clear_tail M R₁ hR₁ R' hR'

/-- Given a primitive integer vector `w : Fin (k+2) → ℤ` whose entries satisfy
the DivChain-forced column-0 divisibility `a_{i-1} ∣ w_{i.succ}`, there exists
`N ∈ SL_{k+2}(ℤ)` with first column `w` lying in the stabilizer of
`diagMat (Fin.cons 1 a)`. -/
lemma sl_exists_col_stab_divChain {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hda : DivChain (k + 1) a)
    (w : Fin (k + 2) → ℤ)
    (hw_primitive : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d)
    (hw_col_div : ∀ i : Fin (k + 1), (a i : ℤ) ∣ w i.succ) :
    ∃ N : SpecialLinearGroup (Fin (k + 2)) ℤ,
      (∀ i, N.1 i 0 = w i) ∧
      (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  rcases k with _ | _ | k
  · exact sl_exists_col_stab_divChain_zero a ha hda w hw_primitive hw_col_div
  · exact sl_exists_col_stab_divChain_one a ha hda w hw_primitive hw_col_div
  · refine sl_exists_col_stab_divChain_of_trailing_hnf_data a ha hda w hw_col_div ?_
    obtain ⟨N₀, hcol₀⟩ := sl_exists_col_of_primitive w hw_primitive
    let Mtail : Matrix (Fin (k + 3)) (Fin (k + 3)) ℤ :=
      fun i k' ↦ N₀.1 i.succ k'.succ
    obtain ⟨R, hR⟩ := sl_upperTri_for_matrix Mtail
    refine ⟨N₀, R, hcol₀, ?_⟩
    intro i j hji
    have h_sum :
        ∑ k' : Fin (k + 3), N₀.1 i.succ k'.succ * R.val k' j =
        (Mtail * R.val) i j := by
      rw [Matrix.mul_apply]
    rw [h_sum, hR i j hji]
    exact dvd_zero _

end HeckeRing.GLn
