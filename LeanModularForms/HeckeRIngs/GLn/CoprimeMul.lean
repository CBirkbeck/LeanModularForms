/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanModularForms.HeckeRIngs.GLn.CosetDecomposition
import LeanModularForms.HeckeRIngs.GLn.Degree
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Ring

/-!
# Coprime Product and Scalar Multiplication in the Hecke Ring

Shimura Propositions 3.16 and 3.17: when determinants are coprime,
the product of double cosets is a single double coset with multiplicity 1.
Scalar double cosets T(c,...,c) act by scaling.

## Main results

* `T_diag_scalar_mul` — `T(c,...,c) · T(b₁,...,bₙ) = T(cb₁,...,cbₙ)`
* `T_diag_mul_coprime` — `T(a) · T(b) = T(a·b)` when `(∏aᵢ, ∏bᵢ) = 1`

## References

* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.2
-/

private def slTransvecG {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
    Matrix.SpecialLinearGroup (Fin m) ℤ :=
  ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j hij c⟩

private def IsTransvec {m : ℕ} (E : Matrix.SpecialLinearGroup (Fin m) ℤ) : Prop :=
  ∃ (i j : Fin m) (hij : i ≠ j) (c : ℤ), E = slTransvecG i j hij c

private lemma slTransvecG_mul {m : ℕ} (i j : Fin m) (hij : i ≠ j) (a b : ℤ) :
    slTransvecG i j hij a * slTransvecG i j hij b = slTransvecG i j hij (a + b) :=
  Subtype.ext (Matrix.transvection_mul_transvection_same i j hij a b)

private lemma slTransvecG_zero {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    slTransvecG i j hij 0 = 1 :=
  Subtype.ext (by simp [slTransvecG, Matrix.transvection_zero])

private lemma slTransvecG_mul_entry {m : ℕ} [NeZero m] (i j : Fin m) (hij : i ≠ j) (c : ℤ)
    (σ : Matrix.SpecialLinearGroup (Fin m) ℤ) (a b : Fin m) :
    (slTransvecG i j hij c * σ).1 a b =
    if a = i then σ.1 i b + c * σ.1 j b else σ.1 a b := by
  have hcoe : (slTransvecG i j hij c * σ).1 = Matrix.transvection i j c * σ.1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, slTransvecG]
  rw [hcoe]
  split_ifs with hai
  · subst hai; simp [Matrix.transvection, Matrix.add_mul]
  · simp [Matrix.transvection, Matrix.add_mul, hai]

private lemma slTransvecG_mul_right_entry {m : ℕ}
    [NeZero m] (i j : Fin m) (hij : i ≠ j) (c : ℤ) (σ : Matrix.SpecialLinearGroup (Fin m) ℤ)
    (a b : Fin m) : (σ * slTransvecG i j hij c).1 a b =
    if b = j then σ.1 a j + c * σ.1 a i else σ.1 a b := by
  have hcoe : (σ * slTransvecG i j hij c).1 = σ.1 * Matrix.transvection i j c := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, slTransvecG]
  rw [hcoe]
  split_ifs with hbj
  · subst hbj; simp [Matrix.transvection, Matrix.mul_add, mul_comm]
  · simp [Matrix.transvection, Matrix.mul_add, hbj]

private lemma isTransvec_append {m : ℕ} (L₁ L₂ : List (Matrix.SpecialLinearGroup (Fin m) ℤ))
    (h₁ : ∀ E ∈ L₁, IsTransvec E) (h₂ : ∀ E ∈ L₂, IsTransvec E) :
    ∀ E ∈ L₁ ++ L₂, IsTransvec E :=
  fun E hE => (List.mem_append.mp hE).elim (h₁ E) (h₂ E)

private def liftTransvec {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ :=
  slTransvecG i.castSucc j.castSucc (Fin.castSucc_injective m |>.ne hij) c

private lemma liftTransvec_isTransvec {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
    IsTransvec (liftTransvec i j hij c) :=
  ⟨i.castSucc, j.castSucc, Fin.castSucc_injective m |>.ne hij, c, rfl⟩

private def col0Sum {m : ℕ} (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ) : ℕ :=
  ∑ i : Fin (m+1), (σ.1 i 0).natAbs

private lemma slTransvecG_col0 {m : ℕ} (i j : Fin (m+1)) (hij : i ≠ j) (c : ℤ)
    (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ) (a : Fin (m+1)) :
    (slTransvecG i j hij c * σ).1 a 0 =
    if a = i then σ.1 i 0 + c * σ.1 j 0 else σ.1 a 0 := by
  have : (slTransvecG i j hij c * σ).1 = Matrix.transvection i j c * σ.1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, slTransvecG]
  rw [this]; split_ifs with hai
  · subst hai; simp [Matrix.transvection, Matrix.add_mul]
  · simp [Matrix.transvection, Matrix.add_mul, hai]

private lemma col0_ne_zero {m : ℕ} (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ) :
    ∃ i, σ.1 i 0 ≠ 0 := by
  by_contra h; push_neg at h
  have : σ.1.det = 0 := Matrix.det_eq_zero_of_column_eq_zero 0 (fun i => h i)
  linarith [σ.2]

private def nzCount {m : ℕ} (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ) : ℕ :=
  (Finset.univ.filter fun i : Fin (m+1) => σ.1 i 0 ≠ 0).card

private lemma exists_two_nz {m : ℕ} (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)
    (h : 2 ≤ nzCount σ) :
    ∃ (i j : Fin (m+1)), i ≠ j ∧ σ.1 i 0 ≠ 0 ∧ σ.1 j 0 ≠ 0 := by
  simp only [nzCount] at h
  have h1 : 1 < (Finset.univ.filter fun i : Fin (m+1) => σ.1 i 0 ≠ 0).card := by omega
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h1
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi hj
  exact ⟨i, j, hij, hi, hj⟩

private lemma col0_euclidean_step {m : ℕ} (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)
    (h : 2 ≤ nzCount σ) :
    ∃ (i j : Fin (m+1)) (hij : i ≠ j) (c : ℤ),
      col0Sum (slTransvecG i j hij c * σ) < col0Sum σ := by
  obtain ⟨i₀, j₀, hij₀, hi₀, hj₀⟩ := exists_two_nz σ h
  by_cases hge : (σ.1 j₀ 0).natAbs ≤ (σ.1 i₀ 0).natAbs
  · refine ⟨i₀, j₀, hij₀, -(σ.1 i₀ 0 / σ.1 j₀ 0), ?_⟩
    set q := σ.1 i₀ 0 / σ.1 j₀ 0
    have h_new : (slTransvecG i₀ j₀ hij₀ (-q) * σ).1 i₀ 0 = σ.1 i₀ 0 % σ.1 j₀ 0 := by
      rw [slTransvecG_col0]; simp only [ite_true]
      linarith [(Int.mul_ediv_add_emod (σ.1 i₀ 0) (σ.1 j₀ 0)).symm]
    have h_oth : ∀ a, a ≠ i₀ → (slTransvecG i₀ j₀ hij₀ (-q) * σ).1 a 0 = σ.1 a 0 :=
      fun a ha => by rw [slTransvecG_col0]; simp [ha]
    have h_rem : (σ.1 i₀ 0 % σ.1 j₀ 0).natAbs < (σ.1 j₀ 0).natAbs := by
      have h1 := Int.emod_nonneg (σ.1 i₀ 0) hj₀
      have h2 : σ.1 i₀ 0 % σ.1 j₀ 0 < |σ.1 j₀ 0| := by
        rw [← Int.emod_abs]; exact Int.emod_lt_of_pos _ (abs_pos.mpr hj₀)
      exact_mod_cast show ((σ.1 i₀ 0 % σ.1 j₀ 0).natAbs : ℤ) < (σ.1 j₀ 0).natAbs from by
        rw [Int.natAbs_of_nonneg h1, Int.natCast_natAbs]; exact h2
    simp only [col0Sum]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₀),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ i₀)]
    have h_rest : ∑ k ∈ Finset.univ.erase i₀,
        ((slTransvecG i₀ j₀ hij₀ (-q) * σ).1 k 0).natAbs =
        ∑ k ∈ Finset.univ.erase i₀, (σ.1 k 0).natAbs :=
      Finset.sum_congr rfl fun k hk => by rw [h_oth k (Finset.mem_erase.mp hk).1]
    rw [h_rest, h_new]; linarith [Nat.lt_of_lt_of_le h_rem hge]
  · push_neg at hge
    refine ⟨j₀, i₀, Ne.symm hij₀, -(σ.1 j₀ 0 / σ.1 i₀ 0), ?_⟩
    set q := σ.1 j₀ 0 / σ.1 i₀ 0
    have h_new : (slTransvecG j₀ i₀ (Ne.symm hij₀) (-q) * σ).1 j₀ 0 =
        σ.1 j₀ 0 % σ.1 i₀ 0 := by
      rw [slTransvecG_col0]; simp only [ite_true]
      linarith [(Int.mul_ediv_add_emod (σ.1 j₀ 0) (σ.1 i₀ 0)).symm]
    have h_oth : ∀ a, a ≠ j₀ →
        (slTransvecG j₀ i₀ (Ne.symm hij₀) (-q) * σ).1 a 0 =
        σ.1 a 0 :=
      fun a ha => by rw [slTransvecG_col0]; simp [ha]
    have h_rem : (σ.1 j₀ 0 % σ.1 i₀ 0).natAbs < (σ.1 i₀ 0).natAbs := by
      have h1 := Int.emod_nonneg (σ.1 j₀ 0) hi₀
      have h2 : σ.1 j₀ 0 % σ.1 i₀ 0 < |σ.1 i₀ 0| := by
        rw [← Int.emod_abs]; exact Int.emod_lt_of_pos _ (abs_pos.mpr hi₀)
      exact_mod_cast show ((σ.1 j₀ 0 % σ.1 i₀ 0).natAbs : ℤ) < (σ.1 i₀ 0).natAbs from by
        rw [Int.natAbs_of_nonneg h1, Int.natCast_natAbs]; exact h2
    simp only [col0Sum]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
    have h_rest : ∑ k ∈ Finset.univ.erase j₀,
        ((slTransvecG j₀ i₀ (Ne.symm hij₀) (-q) * σ).1 k 0).natAbs =
        ∑ k ∈ Finset.univ.erase j₀, (σ.1 k 0).natAbs :=
      Finset.sum_congr rfl fun k hk => by rw [h_oth k (Finset.mem_erase.mp hk).1]
    rw [h_rest, h_new]; linarith [Nat.lt_of_lt_of_le h_rem (Nat.le_of_lt hge)]

private lemma col0_reduce {m : ℕ} (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ) :
    ∃ (L : List (Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)),
      (∀ E ∈ L, IsTransvec E) ∧ nzCount (L.prod * σ) ≤ 1 := by
  suffices key : ∀ (k : ℕ) (τ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ),
      col0Sum τ ≤ k → ∃ (L : List (Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)),
        (∀ E ∈ L, IsTransvec E) ∧ nzCount (L.prod * τ) ≤ 1 from
    key (col0Sum σ) σ le_rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro τ hk
  by_cases hn : nzCount τ ≤ 1
  · exact ⟨[], fun _ h => absurd h (by simp), by simp; exact hn⟩
  · push_neg at hn
    obtain ⟨i, j, hij, c, hlt⟩ := col0_euclidean_step τ hn
    set τ' := slTransvecG i j hij c * τ with hτ'_def
    have hlt' : col0Sum τ' < k := Nat.lt_of_lt_of_le hlt hk
    obtain ⟨L, hL, hL_nz⟩ := ihk (col0Sum τ') hlt' τ' le_rfl
    exact ⟨L ++ [slTransvecG i j hij c], fun E hE => by
      simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hE
      exact hE.elim (hL E) (fun h => h ▸ ⟨i, j, hij, c, rfl⟩),
      by rw [List.prod_append, List.prod_cons, List.prod_nil, mul_one, mul_assoc]; exact hL_nz⟩

private lemma slTransvecG_inv {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
    (slTransvecG i j hij c)⁻¹ = slTransvecG i j hij (-c) := by
  apply mul_left_cancel (a := slTransvecG i j hij c)
  rw [mul_inv_cancel, slTransvecG_mul, add_neg_cancel, slTransvecG_zero]

private lemma isTransvec_inv {m : ℕ} {E : Matrix.SpecialLinearGroup (Fin m) ℤ}
    (hE : IsTransvec E) : IsTransvec E⁻¹ := by
  obtain ⟨i, j, hij, c, rfl⟩ := hE; rw [slTransvecG_inv]; exact ⟨i, j, hij, -c, rfl⟩

private lemma transvec_list_inv {m : ℕ} (L : List (Matrix.SpecialLinearGroup (Fin m) ℤ))
    (hL : ∀ E ∈ L, IsTransvec E) :
    ∃ L' : List (Matrix.SpecialLinearGroup (Fin m) ℤ),
      (∀ E ∈ L', IsTransvec E) ∧ L.prod⁻¹ = L'.prod := by
  refine ⟨(L.map (·⁻¹)).reverse, fun E hE => ?_, List.prod_inv_reverse L⟩
  rw [List.mem_reverse, List.mem_map] at hE
  obtain ⟨F, hF, rfl⟩ := hE; exact isTransvec_inv (hL F hF)

private def blockLift {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ :=
  slTransvecG i.succ j.succ (fun h => hij (Fin.succ_injective m h)) c

private lemma blockLift_isTransvec {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ) :
    IsTransvec (blockLift i j hij c) :=
  ⟨i.succ, j.succ, fun h => hij (Fin.succ_injective m h), c, rfl⟩

private lemma blockLift_entry {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ)
    (τ : Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ) (a b : Fin (m + 1)) :
    (blockLift i j hij c * τ).1 a b =
    if a = i.succ then τ.1 i.succ b + c * τ.1 j.succ b else τ.1 a b := by
  unfold blockLift; exact slTransvecG_mul_entry i.succ j.succ _ c τ a b

private lemma blockLift_row0 {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ)
    (τ : Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ) (b : Fin (m + 1)) :
    (blockLift i j hij c * τ).1 0 b = τ.1 0 b := by
  rw [blockLift_entry]; split_ifs with h
  · exact absurd h.symm (Fin.succ_ne_zero i)
  · rfl

private lemma blockLift_col0 {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ)
    (τ : Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ)
    (hcol : ∀ k : Fin (m + 1), k ≠ 0 → τ.1 k 0 = 0) (a : Fin (m + 1)) :
    (blockLift i j hij c * τ).1 a 0 = τ.1 a 0 := by
  rw [blockLift_entry]; split_ifs with ha
  · subst ha; rw [hcol j.succ (Fin.succ_ne_zero j), mul_zero, add_zero]
  · rfl

private lemma det_lowerRight {m : ℕ} (τ : Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ)
    (h00 : τ.1 0 0 = 1) (h0j : ∀ j : Fin (m + 1), j ≠ 0 → τ.1 0 j = 0) :
    (Matrix.of fun (i : Fin m) (j : Fin m) => τ.1 i.succ j.succ).det = 1 := by
  suffices h : (τ.1.submatrix Fin.succ Fin.succ).det = 1 by
    rwa [show (Matrix.of fun i j => τ.1 i.succ j.succ) = τ.1.submatrix Fin.succ Fin.succ from
      by ext i j; rfl]
  have hdet : τ.1.det = 1 := τ.2
  rw [Matrix.det_succ_row_zero, Finset.sum_eq_single (0 : Fin (m + 1))
    (fun j _ hj => by simp [h0j j hj])
    (fun h => absurd (Finset.mem_univ _) h)] at hdet
  simpa [Fin.succAbove_zero, h00] using hdet

private def extractBlock {m : ℕ} (τ : Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ)
    (h00 : τ.1 0 0 = 1) (h0j : ∀ j : Fin (m + 1), j ≠ 0 → τ.1 0 j = 0)
    (_hi0 : ∀ i : Fin (m + 1), i ≠ 0 → τ.1 i 0 = 0) :
    Matrix.SpecialLinearGroup (Fin m) ℤ :=
  ⟨Matrix.of fun i j => τ.1 i.succ j.succ, det_lowerRight τ h00 h0j⟩

private lemma extractBlock_blockLift {m : ℕ} (i j : Fin m) (hij : i ≠ j) (c : ℤ)
    (τ : Matrix.SpecialLinearGroup (Fin (m + 1)) ℤ)
    (h00 : τ.1 0 0 = 1) (h0j : ∀ j, j ≠ 0 → τ.1 0 j = 0)
    (hi0 : ∀ i, i ≠ 0 → τ.1 i 0 = 0) :
    extractBlock (blockLift i j hij c * τ)
      (by rw [blockLift_row0]; exact h00)
      (by intro k hk; rw [blockLift_row0]; exact h0j k hk)
      (by intro k hk; rw [blockLift_col0 _ _ _ _ _ hi0]; exact hi0 k hk) =
    slTransvecG i j hij c * extractBlock τ h00 h0j hi0 := by
  haveI : NeZero m := ⟨by rintro rfl; exact i.elim0⟩
  apply Subtype.ext; ext a b
  change (blockLift i j hij c * τ).1 a.succ b.succ =
    (slTransvecG i j hij c * extractBlock τ h00 h0j hi0).1 a b
  rw [blockLift_entry i j hij c τ a.succ b.succ,
      slTransvecG_mul_entry i j hij c (extractBlock τ h00 h0j hi0) a b]
  simp only [Fin.succ_inj, extractBlock, Matrix.of_apply]

private def row0Sum {m : ℕ} (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ) : ℕ :=
  ∑ j : Fin (m+1), if (j : ℕ) = 0 then 0 else (σ.1 0 j).natAbs

private lemma row0_clear {m : ℕ} (τ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)
    (h00 : τ.1 0 0 = 1) (hi0 : ∀ i : Fin (m+1), i ≠ 0 → τ.1 i 0 = 0) :
    ∃ (L : List (Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)),
      (∀ E ∈ L, IsTransvec E) ∧
      (τ * L.prod).1 0 0 = 1 ∧
      (∀ j : Fin (m+1), j ≠ 0 → (τ * L.prod).1 0 j = 0) ∧
      (∀ i : Fin (m+1), i ≠ 0 → (τ * L.prod).1 i 0 = 0) := by
  suffices key : ∀ (k : ℕ) (σ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ),
      σ.1 0 0 = 1 → (∀ i, i ≠ 0 → σ.1 i 0 = 0) → row0Sum σ ≤ k →
      ∃ (L : List (Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)),
        (∀ E ∈ L, IsTransvec E) ∧
        (σ * L.prod).1 0 0 = 1 ∧
        (∀ j, j ≠ 0 → (σ * L.prod).1 0 j = 0) ∧
        (∀ i, i ≠ 0 → (σ * L.prod).1 i 0 = 0) from
    key (row0Sum τ) τ h00 hi0 le_rfl
  intro k; induction k using Nat.strongRecOn with
  | _ k ihk =>
  intro σ hσ00 hσi0 hk
  by_cases hzero : row0Sum σ = 0
  · refine ⟨[], fun _ h => absurd h (by simp), by simp [hσ00], fun j hj => ?_,
      fun i hi => by simp [hσi0 i hi]⟩
    simp only [List.prod_nil, mul_one]
    have h_le : (if (j : ℕ) = 0 then 0 else (σ.1 0 j).natAbs) ≤ row0Sum σ :=
      Finset.single_le_sum
        (f := fun (j : Fin (m + 1)) =>
          if (j : ℕ) = 0 then 0 else (σ.1 0 j).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    simp only [hzero, show ¬(j : ℕ) = 0 from fun h₀ => hj (Fin.ext h₀), ↓reduceIte] at h_le
    exact Int.natAbs_eq_zero.mp (Nat.eq_zero_of_le_zero h_le)
  · have hpos : 0 < row0Sum σ := by omega
    have ⟨j₀, hj₀_nz⟩ : ∃ j : Fin (m + 1),
        (if (j : ℕ) = 0 then 0 else (σ.1 0 j).natAbs) ≠ 0 := by
      by_contra h; push_neg at h
      exact hzero (Finset.sum_eq_zero (fun j _ => h j))
    have hj₀ : j₀ ≠ 0 := by
      intro h; subst h; simp at hj₀_nz
    have hj₀_entry : σ.1 0 j₀ ≠ 0 := by
      intro h; simp [h, show ¬(j₀ : ℕ) = 0 from fun h₀ => hj₀ (Fin.ext h₀)] at hj₀_nz
    set E := slTransvecG (0 : Fin (m+1)) j₀ (Ne.symm hj₀) (-σ.1 0 j₀)
    set σ' := σ * E with hσ'_def
    haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
    have hσ'00 : σ'.1 0 0 = 1 := by
      rw [hσ'_def,
        show (σ * E).1 0 0 =
          (σ * slTransvecG 0 j₀ (Ne.symm hj₀) (-σ.1 0 j₀)).1 0 0
          from rfl,
        slTransvecG_mul_right_entry]
      simp [hj₀.symm, hσ00]
    have hσ'i0 : ∀ i, i ≠ 0 → σ'.1 i 0 = 0 := by
      intro i hi; rw [hσ'_def]
      show (σ * slTransvecG 0 j₀ (Ne.symm hj₀) (-σ.1 0 j₀)).1 i 0 = 0
      rw [slTransvecG_mul_right_entry]; simp [hj₀.symm, hσi0 i hi]
    have hσ'_clear : σ'.1 0 j₀ = 0 := by
      rw [hσ'_def]
      show (σ * slTransvecG 0 j₀ (Ne.symm hj₀) (-σ.1 0 j₀)).1 0 j₀ = 0
      rw [slTransvecG_mul_right_entry]; simp [hσ00]
    have hσ'_other : ∀ k, k ≠ j₀ → σ'.1 0 k = σ.1 0 k := by
      intro k hk; rw [hσ'_def]
      show (σ * slTransvecG 0 j₀ (Ne.symm hj₀) (-σ.1 0 j₀)).1 0 k = σ.1 0 k
      rw [slTransvecG_mul_right_entry]; simp [hk]
    have hlt : row0Sum σ' < row0Sum σ := by
      simp only [row0Sum]
      have h_eq : ∀ j, j ≠ j₀ → (if (j : ℕ) = 0 then 0 else (σ'.1 0 j).natAbs) =
          (if (j : ℕ) = 0 then 0 else (σ.1 0 j).natAbs) := by
        intro j hj; by_cases h0 : (j : ℕ) = 0 <;> simp [h0, hσ'_other j hj]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
      have h_rest : ∑ k ∈ Finset.univ.erase j₀,
          (if (k : ℕ) = 0 then 0 else (σ'.1 0 k).natAbs) =
          ∑ k ∈ Finset.univ.erase j₀,
          (if (k : ℕ) = 0 then 0 else (σ.1 0 k).natAbs) :=
        Finset.sum_congr rfl fun k hk => h_eq k (Finset.mem_erase.mp hk).1
      rw [h_rest, hσ'_clear, show (if (j₀ : ℕ) = 0 then 0 else (0 : ℤ).natAbs) = 0 from by
        simp]
      simp only [show ¬(j₀ : ℕ) = 0 from fun h₀ => hj₀ (Fin.ext h₀),
        ↓reduceIte, zero_add]
      omega
    obtain ⟨L', hL'_tv, hL'_00, hL'_0j, hL'_i0⟩ :=
      ihk (row0Sum σ') (by omega) σ' hσ'00 hσ'i0 le_rfl
    refine ⟨E :: L', fun F hF => ?_, ?_, ?_, ?_⟩
    · simp only [List.mem_cons] at hF
      exact hF.elim (fun h => h ▸ ⟨0, j₀, Ne.symm hj₀, _, rfl⟩) (hL'_tv F)
    · simp only [List.prod_cons, ← mul_assoc]; exact hL'_00
    · intro j hj; simp only [List.prod_cons, ← mul_assoc]; exact hL'_0j j hj
    · intro i hi; simp only [List.prod_cons, ← mul_assoc]; exact hL'_i0 i hi

private lemma nzCount_le_one_unique_nonzero {m : ℕ}
    (τ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)
    (i₀ : Fin (m+1)) (hi₀ : τ.1 i₀ 0 ≠ 0) (h_nz : nzCount τ ≤ 1) :
    ∀ k, k ≠ i₀ → τ.1 k 0 = 0 := by
  intro k hk; by_contra hne
  have : 2 ≤ nzCount τ := by
    simp only [nzCount]
    calc 2 = ({i₀, k} : Finset _).card := (Finset.card_pair hk.symm).symm
      _ ≤ (Finset.univ.filter fun i => τ.1 i 0 ≠ 0).card :=
          Finset.card_le_card fun x hx => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hx
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact hx.elim (· ▸ hi₀) (· ▸ hne)
  linarith

private lemma sole_nonzero_col0_is_unit {m : ℕ} (τ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)
    (i₀ : Fin (m+1)) (h_others : ∀ k, k ≠ i₀ → τ.1 k 0 = 0) :
    τ.1 i₀ 0 = 1 ∨ τ.1 i₀ 0 = -1 := by
  set M := τ.1 with hM_def
  have hdet : M.det = 1 := τ.2
  rw [← Int.isUnit_iff]; apply isUnit_of_dvd_one; rw [← hdet, Matrix.det_apply]
  apply Finset.dvd_sum; intro σ _
  show M i₀ 0 ∣ (↑(Equiv.Perm.sign σ) : ℤ) * ∏ i, M (σ i) i
  have hp : ∏ i : Fin (m + 1), M (σ i) i =
      M (σ 0) 0 * ∏ i : Fin m, M (σ i.succ) i.succ := Fin.prod_univ_succ _
  by_cases hσ : σ 0 = i₀
  · rw [hp, hσ, ← mul_assoc]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  · rw [hp, show M (σ 0) 0 = 0 from h_others (σ 0) hσ, zero_mul, mul_zero]
    exact dvd_zero _

private lemma block_form_transvec_lift {m : ℕ} (M : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)
    (H00 : M.1 0 0 = 1) (H0j : ∀ j, j ≠ 0 → M.1 0 j = 0)
    (Hi0 : ∀ i, i ≠ 0 → M.1 i 0 = 0)
    (L : List (Matrix.SpecialLinearGroup (Fin m) ℤ)) (hL : ∀ E ∈ L, IsTransvec E)
    (hL_eq : extractBlock M H00 H0j Hi0 = L.prod) :
    ∃ (L' : List (Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)),
      (∀ E ∈ L', IsTransvec E) ∧ M = L'.prod := by
  induction L generalizing M with
  | nil =>
    refine ⟨[], fun _ h => absurd h (by simp), ?_⟩
    simp only [List.prod_nil] at hL_eq ⊢
    apply Subtype.ext; ext a b
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    by_cases ha : a = 0
    · subst ha; by_cases hb : b = 0
      · subst hb; exact H00
      · rw [H0j b hb, if_neg (Ne.symm hb)]
    · by_cases hb : b = 0
      · subst hb; rw [Hi0 a ha, if_neg ha]
      · obtain ⟨a', rfl⟩ := Fin.exists_succ_eq.mpr ha
        obtain ⟨b', rfl⟩ := Fin.exists_succ_eq.mpr hb
        have h := congr_fun (congr_fun (congr_arg Subtype.val hL_eq) a') b'
        simp only [extractBlock, Matrix.of_apply, Matrix.SpecialLinearGroup.coe_one,
          Matrix.one_apply] at h
        simpa using h
  | cons E L' ihL' =>
    simp only [List.prod_cons] at hL_eq
    obtain ⟨i, j, hij, c, rfl⟩ := hL E (List.mem_cons.mpr (Or.inl rfl))
    have H00' : (blockLift i j hij (-c) * M).1 0 0 = 1 := by
      rw [blockLift_row0]; exact H00
    have H0j' : ∀ k, k ≠ 0 → (blockLift i j hij (-c) * M).1 0 k = 0 := by
      intro k hk; rw [blockLift_row0]; exact H0j k hk
    have Hi0' : ∀ k, k ≠ 0 → (blockLift i j hij (-c) * M).1 k 0 = 0 := by
      intro k hk; rw [blockLift_col0 _ _ _ _ _ Hi0]; exact Hi0 k hk
    have hext' : extractBlock (blockLift i j hij (-c) * M) H00' H0j' Hi0' = L'.prod :=
      (extractBlock_blockLift i j hij (-c) M H00 H0j Hi0).trans
        (by rw [hL_eq, ← mul_assoc, slTransvecG_mul, neg_add_cancel, slTransvecG_zero, one_mul])
    obtain ⟨L'', hL''_tv, hL''_eq⟩ := ihL'
      (blockLift i j hij (-c) * M) H00' H0j' Hi0'
      (fun F hF => hL F (List.mem_cons_of_mem _ hF)) hext'
    refine ⟨blockLift i j hij c :: L'',
      fun F hF => (List.mem_cons.mp hF).elim
        (fun h => h ▸ blockLift_isTransvec i j hij c) (hL''_tv F), ?_⟩
    simp only [List.prod_cons]; rw [← hL''_eq, ← mul_assoc]
    unfold blockLift; rw [slTransvecG_mul, add_neg_cancel, slTransvecG_zero, one_mul]

private lemma to_block_form {m : ℕ} (τ : Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)
    (i₀ : Fin (m+1)) (hi₀ : τ.1 i₀ 0 ≠ 0) (h_others : ∀ k, k ≠ i₀ → τ.1 k 0 = 0)
    (h_unit : τ.1 i₀ 0 = 1 ∨ τ.1 i₀ 0 = -1) :
    ∃ (L_left L_right : List (Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)),
      (∀ E ∈ L_left, IsTransvec E) ∧ (∀ E ∈ L_right, IsTransvec E) ∧
      (L_left.prod * τ * L_right.prod).1 0 0 = 1 ∧
      (∀ j : Fin (m+1), j ≠ 0 → (L_left.prod * τ * L_right.prod).1 0 j = 0) ∧
      (∀ i : Fin (m+1), i ≠ 0 → (L_left.prod * τ * L_right.prod).1 i 0 = 0) := by
  haveI : NeZero (m + 1) := ⟨Nat.succ_ne_zero m⟩
  suffices h_col : ∃ (L₁ : List (Matrix.SpecialLinearGroup (Fin (m+1)) ℤ)),
      (∀ E ∈ L₁, IsTransvec E) ∧
      (L₁.prod * τ).1 0 0 = 1 ∧
      (∀ i, i ≠ 0 → (L₁.prod * τ).1 i 0 = 0) by
    obtain ⟨L₁, hL₁, h₁_00, h₁_i0⟩ := h_col
    obtain ⟨L₂, hL₂, h₂_00, h₂_0j, h₂_i0⟩ :=
      row0_clear (L₁.prod * τ) h₁_00 h₁_i0
    exact ⟨L₁, L₂, hL₁, hL₂, h₂_00,
      fun j hj => h₂_0j j hj,
      fun i hi => h₂_i0 i hi⟩
  by_cases hi₀_zero : i₀ = 0
  · subst hi₀_zero
    rcases h_unit with h1 | h_neg1
    · exact ⟨[], fun _ h => absurd h (by simp), by simp [h1],
        fun i hi => by simp [h_others i hi]⟩
    · rcases m with _ | m'
      · exact absurd (show τ.1.det = -1 by simp [Matrix.det_unique, h_neg1])
          (by rw [τ.2]; norm_num)
      · have h10 : (1 : Fin (m' + 2)) ≠ 0 := by simp
        have h01 : (0 : Fin (m' + 2)) ≠ 1 := h10.symm
        set σ₁ := slTransvecG (1 : Fin (m' + 2)) 0 h10 1 * τ
        have hσ₁_00 : σ₁.1 0 0 = -1 := by
          show (slTransvecG 1 0 h10 1 * τ).1 0 0 = -1
          rw [slTransvecG_mul_entry]; simp [h01, h_neg1]
        have hσ₁_10 : σ₁.1 1 0 = -1 := by
          show (slTransvecG 1 0 h10 1 * τ).1 1 0 = -1
          rw [slTransvecG_mul_entry]; simp [h_neg1, h_others 1 h10]
        have hσ₁_i0 : ∀ i, i ≠ 0 → i ≠ 1 → σ₁.1 i 0 = 0 := by
          intro i hi0 hi1
          show (slTransvecG 1 0 h10 1 * τ).1 i 0 = 0
          rw [slTransvecG_mul_entry]; simp [hi1, h_others i hi0]
        set σ₂ := slTransvecG (0 : Fin (m' + 2)) 1 h01 (-2) * σ₁
        have hσ₂_00 : σ₂.1 0 0 = 1 := by
          show (slTransvecG 0 1 h01 (-2) * σ₁).1 0 0 = 1
          rw [slTransvecG_mul_entry]; simp [hσ₁_00, hσ₁_10]
        have hσ₂_10 : σ₂.1 1 0 = -1 := by
          show (slTransvecG 0 1 h01 (-2) * σ₁).1 1 0 = -1
          rw [slTransvecG_mul_entry]; simp [h10, hσ₁_10]
        have hσ₂_i0 : ∀ i, i ≠ 0 → i ≠ 1 → σ₂.1 i 0 = 0 := by
          intro i hi0 hi1
          show (slTransvecG 0 1 h01 (-2) * σ₁).1 i 0 = 0
          rw [slTransvecG_mul_entry]; simp [hi0, hσ₁_i0 i hi0 hi1]
        set σ₃ := slTransvecG (1 : Fin (m' + 2)) 0 h10 1 * σ₂
        have hσ₃_00 : σ₃.1 0 0 = 1 := by
          show (slTransvecG 1 0 h10 1 * σ₂).1 0 0 = 1
          rw [slTransvecG_mul_entry]; simp [h01, hσ₂_00]
        have hσ₃_i0 : ∀ i, i ≠ 0 → σ₃.1 i 0 = 0 := by
          intro i hi
          show (slTransvecG 1 0 h10 1 * σ₂).1 i 0 = 0
          rw [slTransvecG_mul_entry]
          rcases eq_or_ne i 1 with rfl | hi1
          · simp [hσ₂_00, hσ₂_10]
          · simp [hi1, hσ₂_i0 i hi hi1]
        have hprod : [slTransvecG 1 0 h10 1, slTransvecG 0 1 h01 (-2),
            slTransvecG 1 0 h10 1].prod * τ = σ₃ := by
          simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc, σ₃, σ₂, σ₁]
        exact ⟨[slTransvecG 1 0 h10 1, slTransvecG 0 1 h01 (-2), slTransvecG 1 0 h10 1],
          fun E hE => by
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hE
            rcases hE with rfl | rfl | rfl <;> exact ⟨_, _, _, _, rfl⟩,
          by rw [hprod]; exact hσ₃_00,
          fun i hi => by rw [hprod]; exact hσ₃_i0 i hi⟩
  · have hi₀0 : (0 : Fin (m+1)) ≠ i₀ := fun h => hi₀_zero h.symm
    set v := τ.1 i₀ 0 with hv_def
    have hv2 : v * v = 1 := by rcases h_unit with h | h <;> simp [v, h]
    set σ₁ := slTransvecG (0 : Fin (m+1)) i₀ hi₀0 v * τ
    have hσ₁_00 : σ₁.1 0 0 = 1 := by
      show (slTransvecG 0 i₀ hi₀0 v * τ).1 0 0 = 1
      rw [slTransvecG_mul_entry]; simp [h_others 0 hi₀0, ← hv_def, hv2]
    have hσ₁_i₀0 : σ₁.1 i₀ 0 = v := by
      show (slTransvecG 0 i₀ hi₀0 v * τ).1 i₀ 0 = v
      rw [slTransvecG_mul_entry]; simp [hi₀_zero, ← hv_def]
    have hσ₁_other : ∀ k, k ≠ 0 → k ≠ i₀ → σ₁.1 k 0 = 0 := by
      intro k hk0 hki₀
      show (slTransvecG 0 i₀ hi₀0 v * τ).1 k 0 = 0
      rw [slTransvecG_mul_entry]; simp [hk0, h_others k hki₀]
    set σ₂ := slTransvecG i₀ (0 : Fin (m+1)) hi₀_zero (-v) * σ₁
    have hσ₂_00 : σ₂.1 0 0 = 1 := by
      show (slTransvecG i₀ 0 hi₀_zero (-v) * σ₁).1 0 0 = 1
      rw [slTransvecG_mul_entry]; simp [hi₀0, hσ₁_00]
    have hσ₂_i0 : ∀ i, i ≠ 0 → σ₂.1 i 0 = 0 := by
      intro i hi
      show (slTransvecG i₀ 0 hi₀_zero (-v) * σ₁).1 i 0 = 0
      rw [slTransvecG_mul_entry]
      rcases eq_or_ne i i₀ with rfl | hne
      · simp [hσ₁_i₀0, hσ₁_00, add_neg_cancel]
      · simp [hne, hσ₁_other i hi hne]
    have hprod : [slTransvecG i₀ 0 hi₀_zero (-v),
        slTransvecG 0 i₀ hi₀0 v].prod * τ = σ₂ := by
      simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc, σ₂, σ₁]
    exact ⟨[slTransvecG i₀ 0 hi₀_zero (-v), slTransvecG 0 i₀ hi₀0 v],
      fun E hE => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hE
        rcases hE with rfl | rfl <;> exact ⟨_, _, _, _, rfl⟩,
      by rw [hprod]; exact hσ₂_00,
      fun i hi => by rw [hprod]; exact hσ₂_i0 i hi⟩

private theorem SLnZ_transvec_gen (m : ℕ) (σ : Matrix.SpecialLinearGroup (Fin m) ℤ) :
    ∃ (L : List (Matrix.SpecialLinearGroup (Fin m) ℤ)),
      (∀ E ∈ L, IsTransvec E) ∧ σ = L.prod := by
  induction m with
  | zero =>
    refine ⟨[], fun _ h => absurd h (by simp), ?_⟩
    apply Subtype.ext; ext i; exact i.elim0
  | succ m ih =>
    obtain ⟨L_col, hL_col, h_nz⟩ := col0_reduce σ
    set τ := L_col.prod * σ with hτ_def
    have hσ_eq : σ = L_col.prod⁻¹ * τ := by rw [hτ_def]; simp
    obtain ⟨L_inv, hL_inv_tv, hL_inv_eq⟩ := transvec_list_inv L_col hL_col
    obtain ⟨i₀, hi₀⟩ := col0_ne_zero τ
    have h_others := nzCount_le_one_unique_nonzero τ i₀ hi₀ h_nz
    have h_unit := sole_nonzero_col0_is_unit τ i₀ h_others
    obtain ⟨L_left, L_right, hL_left, hL_right, h00, h0j, hhi0⟩ :=
      to_block_form τ i₀ hi₀ h_others h_unit
    set τ' := L_left.prod * τ * L_right.prod
    obtain ⟨L_B, hL_B_tv, hL_B_eq⟩ := ih (extractBlock τ' h00 h0j hhi0)
    obtain ⟨L_block, hL_block_tv, hL_block_eq⟩ :=
      block_form_transvec_lift τ' h00 h0j hhi0 L_B hL_B_tv hL_B_eq
    obtain ⟨L_left_inv, hL_left_inv_tv, hL_left_inv_eq⟩ := transvec_list_inv L_left hL_left
    obtain ⟨L_right_inv, hL_right_inv_tv, hL_right_inv_eq⟩ := transvec_list_inv L_right hL_right
    refine ⟨L_inv ++ L_left_inv ++ L_block ++ L_right_inv,
      isTransvec_append _ _ (isTransvec_append _ _
        (isTransvec_append _ _ hL_inv_tv hL_left_inv_tv) hL_block_tv) hL_right_inv_tv, ?_⟩
    rw [List.prod_append, List.prod_append, List.prod_append,
        ← hL_inv_eq, ← hL_left_inv_eq, ← hL_right_inv_eq,
        ← hL_block_eq, hσ_eq]
    show L_col.prod⁻¹ * τ =
      L_col.prod⁻¹ * L_left.prod⁻¹ * (L_left.prod * τ * L_right.prod) * L_right.prod⁻¹
    group

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset

open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ) [NeZero n]

section DiagMul

/-- Pointwise multiplication of two positive-valued sequences. -/
def diagMul (a b : Fin n → ℕ) : Fin n → ℕ :=
  fun i => a i * b i

omit [NeZero n] in
lemma diagMul_pos (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    ∀ i, 0 < diagMul n a b i :=
  fun i => Nat.mul_pos (ha i) (hb i)

omit [NeZero n] in
@[simp] lemma diagMul_apply (a b : Fin n → ℕ) (i : Fin n) :
    diagMul n a b i = a i * b i := rfl

omit [NeZero n] in
lemma DivChain_mul (a b : Fin n → ℕ) (ha : DivChain n a) (hb : DivChain n b) :
    DivChain n (diagMul n a b) := by
  intro i hi
  simp only [diagMul_apply]
  exact Nat.mul_dvd_mul (ha i hi) (hb i hi)

omit [NeZero n] in
lemma diagMat_mul (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
    diagMat n a ha * diagMat n b hb = diagMat n (diagMul n a b) (diagMul_pos n a b ha hb) := by
  apply Units.ext
  simp only [Units.val_mul, diagMat_val, diagMul_apply]
  ext i j
  simp only [Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i]
    · simp
    · intro b' _ hb'; simp [hb']
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp only [hij, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hik : i = k
    · subst hik; simp [hij]
    · simp [hik]

lemma T_diag_eq_T_mk_mul (a b : Fin n → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hab : DivChain n (diagMul n a b)) :
    T_diag n (diagMul n a b) (diagMul_pos n a b ha hb) hab =
    T_mk (GL_pair n) ⟨diagMat n a ha * diagMat n b hb,
      (diagMat_mul n a b ha hb).symm ▸ diagMat_mem_posDetInt n (diagMul n a b)
        (diagMul_pos n a b ha hb)⟩ := by
  apply T'_ext
  simp only [T_diag, T_mk, diagMat_delta]
  congr 1
  exact (diagMat_mul n a b ha hb).symm

end DiagMul

private lemma doubleCoset_eq_of_mem' (g δ : GL (Fin n) ℚ)
    (h : g ∈ DoubleCoset.doubleCoset δ (SLnZ_subgroup n) (SLnZ_subgroup n)) :
    DoubleCoset.doubleCoset g (SLnZ_subgroup n) (SLnZ_subgroup n) =
    DoubleCoset.doubleCoset δ (SLnZ_subgroup n) (SLnZ_subgroup n) := by
  rw [DoubleCoset.mem_doubleCoset] at h
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := h
  rw [heq]
  exact (DoubleCoset.doubleCoset_mul_right_eq_self (GL_pair n) ⟨h₂, hh₂⟩ (h₁ * δ)).trans
    (doset_mul_left_eq_self (GL_pair n) ⟨h₁, hh₁⟩ δ)

section Scalar
open Classical

omit [NeZero n] in
lemma diagMat_scalar_eq (c : ℕ) (hc : 0 < c) :
    (↑(diagMat n (fun _ => c) (fun _ => hc)) : Matrix (Fin n) (Fin n) ℚ) = (c : ℚ) • 1 := by
  simp only [diagMat_val, ← Matrix.smul_one_eq_diagonal]

omit [NeZero n] in
lemma diagMat_scalar_comm (c : ℕ) (hc : 0 < c) (g : GL (Fin n) ℚ) :
    diagMat n (fun _ => c) (fun _ => hc) * g = g * diagMat n (fun _ => c) (fun _ => hc) := by
  apply Units.ext
  simp only [Units.val_mul, diagMat_scalar_eq, smul_one_mul, mul_smul_one]

omit [NeZero n] in
lemma diagMat_scalar_conj_eq (c : ℕ) (hc : 0 < c) (x : GL (Fin n) ℚ) :
    (diagMat n (fun _ => c) (fun _ => hc))⁻¹ * x *
      diagMat n (fun _ => c) (fun _ => hc) = x := by
  rw [mul_assoc, ← diagMat_scalar_comm n c hc x, ← mul_assoc, inv_mul_cancel, one_mul]

lemma conjAct_scalar_smul_eq (c : ℕ) (hc : 0 < c) :
    ConjAct.toConjAct (diagMat n (fun _ => c) (fun _ => hc)) • (GL_pair n).H =
      (GL_pair n).H := by
  ext x
  constructor
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at hx
    rwa [diagMat_scalar_conj_eq] at hx
  · intro hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.smul_def, map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
    rwa [diagMat_scalar_conj_eq]

private lemma conjAct_mem_smul_eq (h : GL (Fin n) ℚ) (hh : h ∈ (GL_pair n).H) :
    ConjAct.toConjAct h • (GL_pair n).H = (GL_pair n).H := by
  ext x
  simp only [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def,
    map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  constructor
  · intro hx
    have : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
    rw [this]; exact (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem hh hx) ((GL_pair n).H.inv_mem hh)
  · intro hx
    exact (GL_pair n).H.mul_mem ((GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem hh) hx) hh

lemma T'_deg_scalar (c : ℕ) (hc : 0 < c) :
    T'_deg (GL_pair n) (T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)) = 1 := by
  set D := T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)
  set δ := (D : T' (GL_pair n)).eql.choose
  set H := (GL_pair n).H
  suffices hsmul : ConjAct.toConjAct (δ : GL (Fin n) ℚ) • H = H by
    have h_def : T'_deg (GL_pair n) D =
        ↑((ConjAct.toConjAct (δ : GL (Fin n) ℚ) • H).relIndex H) := by
      simp only [T'_deg, Subgroup.relIndex, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    rw [h_def, hsmul, Subgroup.relIndex_self]; simp
  have hδ_mem : (δ : GL (Fin n) ℚ) ∈ DoubleCoset.doubleCoset
      (↑(diagMat_delta n (fun _ => c) (fun _ => hc))) H H := by
    have h1 : D.set = DoubleCoset.doubleCoset
        (↑(diagMat_delta n (fun _ => c) (fun _ => hc))) H H := rfl
    rw [← h1, D.eql.choose_spec]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hδ_mem
  obtain ⟨h₁, hh₁, h₂, hh₂, hδ_eq⟩ := hδ_mem
  have hδ_simp : (δ : GL (Fin n) ℚ) =
      (h₁ * h₂) * diagMat n (fun _ => c) (fun _ => hc) := by
    rw [hδ_eq,
      show (↑(diagMat_delta n (fun _ => c) (fun _ => hc)) : GL (Fin n) ℚ) =
        diagMat n (fun _ => c) (fun _ => hc) from rfl]
    rw [mul_assoc, diagMat_scalar_comm n c hc h₂, ← mul_assoc]
  rw [hδ_simp, map_mul, MulAction.mul_smul, conjAct_scalar_smul_eq]
  exact conjAct_mem_smul_eq n (h₁ * h₂) (H.mul_mem hh₁ hh₂)

private lemma mulMap_scalar_eq (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain n b) (hcb : DivChain n (diagMul n (fun _ => c) b))
    (p : decompQuot (GL_pair n) (T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)) ×
         decompQuot (GL_pair n) (T_diag n b hb_pos hb)) :
    mulMap (GL_pair n) (T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c))
      (T_diag n b hb_pos hb) p =
    T_diag n (diagMul n (fun _ => c) b) (diagMul_pos n _ b (fun _ => hc) hb_pos) hcb := by
  set H := (GL_pair n).H
  have hδc_mem : ((T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)).eql.choose :
      GL (Fin n) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat n (fun _ => c) (fun _ => hc) : GL (Fin n) ℚ) H H := by
    have h_spec := (T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδc_mem
  obtain ⟨h₁c, hh₁c, h₂c, hh₂c, hδc_eq⟩ := hδc_mem
  have hδb_mem : ((T_diag n b hb_pos hb).eql.choose : GL (Fin n) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat n b hb_pos : GL (Fin n) ℚ) H H := by
    have h_spec := (T_diag n b hb_pos hb).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδb_mem
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := hδb_mem
  have h_product_mem : (p.1.out : GL (Fin n) ℚ) *
      ((T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)).eql.choose :
        GL (Fin n) ℚ) *
      ((p.2.out : GL (Fin n) ℚ) * ((T_diag n b hb_pos hb).eql.choose : GL (Fin n) ℚ)) ∈
      DoubleCoset.doubleCoset (diagMat n (diagMul n (fun _ => c) b)
        (diagMul_pos n _ b (fun _ => hc) hb_pos) : GL (Fin n) ℚ) H H := by
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨(p.1.out : GL (Fin n) ℚ) * h₁c * h₂c * p.2.out * h₁b,
            H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (SetLike.coe_mem p.1.out) hh₁c) hh₂c)
              (SetLike.coe_mem p.2.out)) hh₁b,
            h₂b, hh₂b, ?_⟩
    set x1 := (↑(Quotient.out p.1) : GL (Fin n) ℚ)
    set dc := ((T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)).eql.choose :
        GL (Fin n) ℚ)
    set x2 := (↑(Quotient.out p.2) : GL (Fin n) ℚ)
    set db := ((T_diag n b hb_pos hb).eql.choose : GL (Fin n) ℚ)
    rw [show dc = h₁c * diagMat n (fun _ => c) (fun _ => hc) * h₂c from hδc_eq,
        show db = h₁b * diagMat n b hb_pos * h₂b from hδb_eq]
    have h_comm : diagMat n (fun _ => c) (fun _ => hc) * (h₂c * x2 * h₁b) =
        (h₂c * x2 * h₁b) * diagMat n (fun _ => c) (fun _ => hc) :=
      diagMat_scalar_comm n c hc _
    calc x1 * (h₁c * diagMat n (fun _ => c) (fun _ => hc) * h₂c) *
        (x2 * (h₁b * diagMat n b hb_pos * h₂b))
        = x1 * h₁c * (diagMat n (fun _ => c) (fun _ => hc) * (h₂c * x2 * h₁b)) *
          (diagMat n b hb_pos * h₂b) := by group
      _ = x1 * h₁c * ((h₂c * x2 * h₁b) * diagMat n (fun _ => c) (fun _ => hc)) *
          (diagMat n b hb_pos * h₂b) := by rw [h_comm]
      _ = x1 * h₁c * h₂c * x2 * h₁b *
          (diagMat n (fun _ => c) (fun _ => hc) * diagMat n b hb_pos) * h₂b := by group
      _ = x1 * h₁c * h₂c * x2 * h₁b *
          diagMat n (diagMul n (fun _ => c) b)
            (diagMul_pos n _ b (fun _ => hc) hb_pos) * h₂b := by
          rw [diagMat_mul]
  apply HeckeRing.T'_ext (GL_pair n)
  exact doubleCoset_eq_of_mem' n _ _ h_product_mem

private lemma m'_scalar_eq_one (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain n b) (hab : DivChain n (diagMul n (fun _ => c) b)) :
    HeckeRing.m' (GL_pair n)
      (T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c))
      (T_diag n b hb_pos hb)
      (T_diag n (diagMul n (fun _ => c) b) (diagMul_pos n _ b (fun _ => hc) hb_pos) hab) = 1 := by
  set D_c := T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)
  set D_b := T_diag n b hb_pos hb
  set D_cb := T_diag n (diagMul n (fun _ => c) b) (diagMul_pos n _ b (fun _ => hc) hb_pos) hab
  have h_card : Fintype.card (decompQuot (GL_pair n) D_c) = 1 := by
    have := T'_deg_scalar n c hc; simp only [HeckeRing.T'_deg] at this; exact_mod_cast this
  haveI : Subsingleton (decompQuot (GL_pair n) D_c) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq h_card)
  have h_le : HeckeRing.m' (GL_pair n) D_c D_b D_cb ≤ 1 := by
    classical
    simp only [HeckeRing.m']; norm_cast; rw [Nat.card_eq_fintype_card]
    apply Fintype.card_le_one_iff_subsingleton.mpr
    constructor; intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
    have hi : i₁ = i₂ := Subsingleton.elim i₁ i₂; subst hi
    simp only [Set.mem_setOf_eq] at h₁ h₂
    have hj : j₁ = j₂ := by
      by_contra hne
      exact HeckeRing.decompQuot_coset_diff (GL_pair n) D_b j₁ j₂ hne
        (HeckeRing.set_singleton_mul_left_cancel _ (by
          have := h₁.trans h₂.symm; rwa [mul_assoc, mul_assoc] at this))
    subst hj; rfl
  have h_pos : 0 < HeckeRing.m' (GL_pair n) D_c D_b D_cb := by
    have h_mem : D_cb ∈ HeckeRing.mulSupport (GL_pair n) D_c D_b := by
      simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
        true_and, Prod.exists]
      have ⟨i₀⟩ : Nonempty (decompQuot (GL_pair n) D_c) :=
        Fintype.card_pos_iff.mp (h_card ▸ Nat.one_pos)
      have ⟨j₀⟩ : Nonempty (decompQuot (GL_pair n) D_b) :=
        Fintype.card_pos_iff.mp (by
          have := HeckeRing.T'_deg_pos (GL_pair n) D_b
          simp only [HeckeRing.T'_deg] at this; omega)
      exact ⟨i₀, j₀, mulMap_scalar_eq n c hc b hb_pos hb hab (i₀, j₀)⟩
    have h_ne := HeckeRing.m'_pos_of_mem_mulSupport (GL_pair n) D_c D_b D_cb h_mem
    have : (0 : ℤ) ≤ HeckeRing.m' (GL_pair n) D_c D_b D_cb := by
      simp only [HeckeRing.m']; exact Nat.cast_nonneg _
    omega
  omega

private lemma m'_scalar_eq_zero (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ)
    (hb_pos : ∀ i, 0 < b i) (hb : DivChain n b)
    (hab : DivChain n (diagMul n (fun _ => c) b)) (A : T' (GL_pair n))
    (hA : A ≠ T_diag n (diagMul n (fun _ => c) b)
      (diagMul_pos n _ b (fun _ => hc) hb_pos) hab) :
    HeckeRing.m' (GL_pair n)
      (T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c))
      (T_diag n b hb_pos hb) A = 0 := by
  apply HeckeRing.m'_eq_zero_of_nmem_mulSupport
  intro h_mem
  simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
    true_and] at h_mem
  obtain ⟨⟨i, j⟩, heq⟩ := h_mem
  exact hA (heq.symm.trans (mulMap_scalar_eq n c hc b hb_pos hb hab (i, j)))

/-- Scalar multiplication in the Hecke ring (Shimura Proposition 3.17). -/
theorem T_diag_scalar_mul (c : ℕ) (hc : 0 < c) (b : Fin n → ℕ) (hb_pos : ∀ i, 0 < b i)
    (hb : DivChain n b) :
    T_elem n (fun _ => c) (fun _ => hc) (divChain_const n c) *
      T_elem n b hb_pos hb =
    T_elem n (diagMul n (fun _ => c) b) (diagMul_pos n _ b (fun _ => hc) hb_pos)
      (DivChain_mul n _ _ (divChain_const n c) hb) := by
  change HeckeRing.T_single (GL_pair n) ℤ
      (T_diag n (fun _ => c) (fun _ => hc) (divChain_const n c)) 1 *
    HeckeRing.T_single (GL_pair n) ℤ (T_diag n b hb_pos hb) 1 =
    HeckeRing.T_single (GL_pair n) ℤ
      (T_diag n (diagMul n (fun _ => c) b) (diagMul_pos n _ b (fun _ => hc) hb_pos)
        (DivChain_mul n _ _ (divChain_const n c) hb)) 1
  rw [HeckeRing.T_single_one_mul_T_single_one]
  apply Finsupp.ext; intro A
  simp only [HeckeRing.m, Finsupp.coe_mk, Finsupp.single_apply]
  split_ifs with h1
  · rw [← h1]; exact m'_scalar_eq_one n c hc b hb_pos hb
      (DivChain_mul n _ _ (divChain_const n c) hb)
  · exact m'_scalar_eq_zero n c hc b hb_pos hb
      (DivChain_mul n _ _ (divChain_const n c) hb) A (Ne.symm h1)

end Scalar


section Coprime
open Classical

noncomputable def diagDet (a : Fin n → ℕ) : ℕ := ∏ i, a i

private def congMod (d : ℕ) (σ : SpecialLinearGroup (Fin n) ℤ) : Prop :=
  ∀ i j, (d : ℤ) ∣ (σ.1 i j - if i = j then 1 else 0)

private def slTransvec (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    SpecialLinearGroup (Fin n) ℤ :=
  ⟨(Matrix.TransvectionStruct.mk i j hij c).toMatrix,
   (Matrix.TransvectionStruct.mk i j hij c).det⟩

omit [NeZero n] in
private lemma slTransvec_mul (i j : Fin n) (hij : i ≠ j) (a b : ℤ) :
    slTransvec n i j hij a * slTransvec n i j hij b =
    slTransvec n i j hij (a + b) := by
  apply Subtype.ext; show (Matrix.TransvectionStruct.mk i j hij a).toMatrix *
    (Matrix.TransvectionStruct.mk i j hij b).toMatrix =
    (Matrix.TransvectionStruct.mk i j hij (a + b)).toMatrix
  simp only [Matrix.TransvectionStruct.toMatrix]
  exact Matrix.transvection_mul_transvection_same (n := Fin n) (i := i) (j := j) hij a b

omit [NeZero n] in
private lemma slTransvec_congMod (d : ℕ) (i j : Fin n) (hij : i ≠ j) (c : ℤ)
    (hdc : (d : ℤ) ∣ c) : congMod n d (slTransvec n i j hij c) := by
  intro k l
  simp only [slTransvec, Matrix.TransvectionStruct.toMatrix, Matrix.transvection,
    Matrix.add_apply, Matrix.one_apply, Matrix.single, Matrix.of_apply, add_sub_cancel_left]
  split_ifs with h
  · exact hdc
  · exact dvd_zero _

omit [NeZero n] in
private lemma slTransvec_CRT (d d' : ℕ) (hcop : Nat.Coprime d d')
    (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    ∃ τ₁ τ₂ : SpecialLinearGroup (Fin n) ℤ,
      slTransvec n i j hij c = τ₁ * τ₂ ∧
      congMod n d τ₁ ∧ congMod n d' τ₂ := by
  have hbez : ↑(Nat.gcd d d') = (d : ℤ) * Nat.gcdA d d' + ↑d' * Nat.gcdB d d' :=
    Nat.gcd_eq_gcd_ab d d'
  rw [hcop.gcd_eq_one, Nat.cast_one] at hbez
  refine ⟨slTransvec n i j hij (c * d * Nat.gcdA d d'),
         slTransvec n i j hij (c * d' * Nat.gcdB d d'), ?_, ?_, ?_⟩
  · rw [slTransvec_mul]; congr 1; linear_combination c * hbez
  · exact slTransvec_congMod n d i j hij _ ⟨c * Nat.gcdA d d', by ring⟩
  · exact slTransvec_congMod n d' i j hij _ ⟨c * Nat.gcdB d d', by ring⟩

omit [NeZero n] in
private lemma congMod_one (d : ℕ) : congMod n d 1 :=
  fun i j => by simp [SpecialLinearGroup.coe_one, Matrix.one_apply]

omit [NeZero n] in
private lemma congMod_mul (d : ℕ) (a b : SpecialLinearGroup (Fin n) ℤ)
    (ha : congMod n d a) (hb : congMod n d b) : congMod n d (a * b) := by
  intro i j
  simp only [SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h1 : ∑ k : Fin n, (if i = k then (1 : ℤ) else 0) * b.1 k j = b.1 i j := by
    simp [Finset.mem_univ]
  have h2 : ∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j =
      (∑ k, a.1 i k * b.1 k j) - b.1 i j := by
    rw [← h1, ← Finset.sum_sub_distrib]; congr 1; ext k; ring
  have h_decomp : (∑ k, a.1 i k * b.1 k j) - (if i = j then 1 else 0) =
      (∑ k, (a.1 i k - if i = k then 1 else 0) * b.1 k j) +
      (b.1 i j - if i = j then 1 else 0) := by linarith [h2]
  rw [h_decomp]
  exact dvd_add (Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_left (ha i k) _)) (hb i j)

omit [NeZero n] in
private lemma congMod_inv (d : ℕ) (a : SpecialLinearGroup (Fin n) ℤ)
    (ha : congMod n d a) : congMod n d a⁻¹ := by
  intro i j
  have h_mul_inv : a.1 * (a⁻¹).1 = 1 := by
    rw [← SpecialLinearGroup.coe_mul, ← SpecialLinearGroup.coe_one]
    exact congr_arg Subtype.val (mul_inv_cancel a)
  have h_entry : ∑ k : Fin n, a.1 i k * (a⁻¹).1 k j = if i = j then 1 else 0 := by
    have := congr_fun (congr_fun h_mul_inv i) j
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  have h_div : (d : ℤ) ∣ ∑ k : Fin n, (a.1 i k - if i = k then 1 else 0) * (a⁻¹).1 k j :=
    Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_left (ha i k) _)
  have h_sum_eq : ∑ k : Fin n, (a.1 i k - if i = k then 1 else 0) * (a⁻¹).1 k j =
      (if i = j then 1 else 0) - (a⁻¹).1 i j := by
    trans (∑ k, a.1 i k * (a⁻¹).1 k j) -
        (∑ k, (if i = k then (1 : ℤ) else 0) * (a⁻¹).1 k j)
    · rw [← Finset.sum_sub_distrib]; congr 1; ext k; ring
    · rw [h_entry]; simp [Finset.mem_univ]
  rw [show (a⁻¹).1 i j - (if i = j then 1 else 0) =
      -(∑ k : Fin n, (a.1 i k - if i = k then 1 else 0) * (a⁻¹).1 k j) from by
    linarith [h_sum_eq]]
  exact dvd_neg.mpr h_div

omit [NeZero n] in
private lemma congMod_conj (d : ℕ) (σ τ : SpecialLinearGroup (Fin n) ℤ)
    (hτ : congMod n d τ) : congMod n d (σ⁻¹ * τ * σ) := by
  intro i j
  simp only [show σ⁻¹ * τ * σ = σ⁻¹ * (τ * σ) from by group,
    SpecialLinearGroup.coe_mul, Matrix.mul_apply]
  have h_inv : ∀ i' j', ∑ k : Fin n, (σ⁻¹).1 i' k * σ.1 k j' =
      if i' = j' then 1 else 0 := by
    intro i' j'
    have h := congr_fun (congr_fun (show (σ⁻¹).1 * σ.1 = 1 from by
      rw [← SpecialLinearGroup.coe_mul, ← SpecialLinearGroup.coe_one]
      exact congr_arg Subtype.val (inv_mul_cancel σ)) i') j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have h_inner : ∀ k, ∑ l : Fin n, τ.1 k l * σ.1 l j =
      (∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) + σ.1 k j := by
    intro k
    have h1 : ∑ l : Fin n, (if k = l then (1 : ℤ) else 0) * σ.1 l j = σ.1 k j := by
      simp [Finset.mem_univ]
    have h2 : ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j =
        (∑ l, τ.1 k l * σ.1 l j) - σ.1 k j := by
      rw [← h1, ← Finset.sum_sub_distrib]; congr 1; ext l; ring
    linarith [h2]
  have h_eq : (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) -
      (if i = j then 1 else 0) =
      ∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j := by
    have h3 : (∑ k, (σ⁻¹).1 i k * ∑ l, τ.1 k l * σ.1 l j) =
        (∑ k, (σ⁻¹).1 i k * ∑ l, (τ.1 k l - if k = l then 1 else 0) * σ.1 l j) +
        (∑ k, (σ⁻¹).1 i k * σ.1 k j) := by
      rw [← Finset.sum_add_distrib]; congr 1; ext k; rw [h_inner k]; ring
    rw [h3, h_inv]; ring
  rw [h_eq]
  exact Finset.dvd_sum (fun k _ => dvd_mul_of_dvd_right
    (Finset.dvd_sum (fun l _ => dvd_mul_of_dvd_left (hτ k l) _)) _)

omit [NeZero n] in
private lemma CRTProd_mul' (d d' : ℕ) (a b : SpecialLinearGroup (Fin n) ℤ)
    (ha : ∃ p q, a = p * q ∧ congMod n d p ∧ congMod n d' q)
    (hb : ∃ p q, b = p * q ∧ congMod n d p ∧ congMod n d' q) :
    ∃ p q, a * b = p * q ∧ congMod n d p ∧ congMod n d' q := by
  obtain ⟨p₁, q₁, rfl, hp₁, hq₁⟩ := ha
  obtain ⟨p₂, q₂, rfl, hp₂, hq₂⟩ := hb
  refine ⟨p₁ * (q₁ * p₂ * q₁⁻¹), q₁ * q₂, ?_, ?_, ?_⟩
  · group
  · have h := congMod_conj n d q₁⁻¹ p₂ hp₂; rw [inv_inv] at h
    exact congMod_mul n d _ _ hp₁ h
  · exact congMod_mul n d' _ _ hq₁ hq₂

omit [NeZero n] in
private lemma slTransvec_in_CRTProd (d d' : ℕ) (hcop : Nat.Coprime d d')
    (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      slTransvec n i j hij c = p * q ∧ congMod n d p ∧ congMod n d' q :=
  slTransvec_CRT n d d' hcop i j hij c

omit [NeZero n] in
private lemma one_in_CRTProd (d d' : ℕ) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      (1 : SpecialLinearGroup (Fin n) ℤ) = p * q ∧
      congMod n d p ∧ congMod n d' q :=
  ⟨1, 1, (one_mul 1).symm, congMod_one n d, congMod_one n d'⟩

omit [NeZero n] in
private lemma slTransvecG_eq_slTransvec (i j : Fin n) (hij : i ≠ j) (c : ℤ) :
    slTransvecG i j hij c = slTransvec n i j hij c :=
  Subtype.ext rfl

omit [NeZero n] in
private lemma isTransvec_in_CRTProd (d d' : ℕ) (hcop : Nat.Coprime d d')
    (E : SpecialLinearGroup (Fin n) ℤ) (hE : IsTransvec E) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      E = p * q ∧ congMod n d p ∧ congMod n d' q := by
  obtain ⟨i, j, hij, c, rfl⟩ := hE
  rw [slTransvecG_eq_slTransvec]
  exact slTransvec_in_CRTProd n d d' hcop i j hij c

omit [NeZero n] in
private lemma list_prod_in_CRTProd (d d' : ℕ) (_hcop : Nat.Coprime d d')
    (L : List (SpecialLinearGroup (Fin n) ℤ))
    (hL : ∀ E ∈ L, ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      E = p * q ∧ congMod n d p ∧ congMod n d' q) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      L.prod = p * q ∧ congMod n d p ∧ congMod n d' q := by
  induction L with
  | nil => exact one_in_CRTProd n d d'
  | cons E L ihL =>
    simp only [List.prod_cons]
    have hE : ∃ p q, E = p * q ∧ congMod n d p ∧ congMod n d' q :=
      hL E (by simp)
    have hprod : ∃ p q, L.prod = p * q ∧ congMod n d p ∧ congMod n d' q :=
      ihL (fun F hF => hL F (by simp [hF]))
    exact CRTProd_mul' n d d' E L.prod hE hprod

omit [NeZero n] in
private lemma SLnZ_in_CRTProd (d d' : ℕ) (_hd : 0 < d) (_hd' : 0 < d') (hcop : Nat.Coprime d d')
    (σ : SpecialLinearGroup (Fin n) ℤ) :
    ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      σ = p * q ∧ congMod n d p ∧ congMod n d' q := by
  obtain ⟨L, hL_transvec, hL_prod⟩ := SLnZ_transvec_gen n σ
  have hL_CRT : ∀ E ∈ L, ∃ p q : SpecialLinearGroup (Fin n) ℤ,
      E = p * q ∧ congMod n d p ∧ congMod n d' q := by
    intro E hE
    exact isTransvec_in_CRTProd n d d' hcop E (hL_transvec E hE)
  rw [hL_prod]
  exact list_prod_in_CRTProd n d d' hcop L hL_CRT

omit [NeZero n] in
/-- Chinese Remainder Theorem for `SL_n(ℤ)`: every element
decomposes as a product of congruence classes
when gcd(d, d') = 1. -/
lemma SLnZ_CRT_decomposition (d d' : ℕ) (hd : 0 < d) (hd' : 0 < d') (hcop : Nat.Coprime d d')
    (τ : SpecialLinearGroup (Fin n) ℤ) :
    ∃ (τ₁ τ₂ : SpecialLinearGroup (Fin n) ℤ),
      τ = τ₁ * τ₂ ∧
      (∀ i j, (d : ℤ) ∣
        ((τ₁ : Matrix (Fin n) (Fin n) ℤ) i j -
          if i = j then 1 else 0)) ∧
      (∀ i j, (d' : ℤ) ∣
        ((τ₂ : Matrix (Fin n) (Fin n) ℤ) i j -
          if i = j then 1 else 0)) :=
  SLnZ_in_CRTProd n d d' hd hd' hcop τ

omit [NeZero n] in
lemma conjugate_congruent_mem_SLnZ (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) (_hdiv : DivChain n a)
    (τ : SpecialLinearGroup (Fin n) ℤ) (hcong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      SLnZ_to_GLnQ n σ = diagMat n a ha * SLnZ_to_GLnQ n τ * (diagMat n a ha)⁻¹ := by
  have hdvd : ∀ i j, (a j : ℤ) ∣ (a i : ℤ) * τ.val i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact dvd_mul_right _ _
    · have h1 : (∏ k, (a k : ℤ)) ∣ τ.val i j := by
        have := hcong i j; simp [hij] at this; exact this
      exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j)) h1) _
  set M : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => (a i : ℤ) * τ.val i j / (a j : ℤ)
  set diag_a := Matrix.diagonal (fun i => (a i : ℤ))
  have h_int_eq : diag_a * τ.val = M * diag_a := by
    ext i j
    simp only [diag_a, M, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
    exact (Int.ediv_mul_cancel (hdvd i j)).symm
  have h_det_ne : diag_a.det ≠ 0 := by
    simp only [diag_a, Matrix.det_diagonal]
    exact ne_of_gt (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (ha i)))
  have hM_det : M.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, mul_one] at h
    have h' : diag_a.det * 1 = diag_a.det * M.det := by rw [mul_one, mul_comm]; exact h
    exact (mul_left_cancel₀ h_det_ne h').symm
  refine ⟨⟨M, hM_det⟩, ?_⟩
  have h_Q_eq : (diagMat n a ha : GL (Fin n) ℚ) * SLnZ_to_GLnQ n τ =
      SLnZ_to_GLnQ n ⟨M, hM_det⟩ * diagMat n a ha := by
    apply Units.ext
    simp only [Units.val_mul, SLnZ_to_GLnQ_val, diagMat_val]
    have h_mul_map : ∀ (A B : Matrix (Fin n) (Fin n) ℤ),
        (A * B).map (Int.cast : ℤ → ℚ) = A.map Int.cast * B.map Int.cast := by
      intro A B; ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
    have h_diag_map : (Matrix.diagonal (fun i => (a i : ℤ))).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal (fun i => (a i : ℚ)) := by
      ext i j; simp [Matrix.map_apply, Matrix.diagonal_apply]
    rw [← h_diag_map, ← h_mul_map, ← h_mul_map, h_int_eq]
  exact eq_mul_inv_iff_mul_eq.mpr h_Q_eq.symm

omit [NeZero n] in
lemma inv_conjugate_congruent_mem_SLnZ (b : Fin n → ℕ)
    (hb : ∀ i, 0 < b i) (_hdiv : DivChain n b)
    (τ : SpecialLinearGroup (Fin n) ℤ) (hcong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      SLnZ_to_GLnQ n σ = (diagMat n b hb)⁻¹ * SLnZ_to_GLnQ n τ * diagMat n b hb := by
  have hdvd : ∀ i j, (b i : ℤ) ∣ (b j : ℤ) * τ.val i j := by
    intro i j
    by_cases hij : i = j
    · subst hij; exact dvd_mul_right _ _
    · have h1 : (∏ k, (b k : ℤ)) ∣ τ.val i j := by
        have := hcong i j; simp [hij] at this; exact this
      exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) h1) _
  set N : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => (b j : ℤ) * τ.val i j / (b i : ℤ)
  set diag_b := Matrix.diagonal (fun i => (b i : ℤ))
  have h_int_eq : τ.val * diag_b = diag_b * N := by
    ext i j
    simp only [diag_b, N, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    calc τ.val i j * (b j : ℤ)
        = (b j : ℤ) * τ.val i j := mul_comm _ _
      _ = (b j : ℤ) * τ.val i j / (b i : ℤ) * (b i : ℤ) :=
          (Int.ediv_mul_cancel (hdvd i j)).symm
      _ = (b i : ℤ) * ((b j : ℤ) * τ.val i j / (b i : ℤ)) := mul_comm _ _
  have h_det_ne : diag_b.det ≠ 0 := by
    simp only [diag_b, Matrix.det_diagonal]
    exact ne_of_gt (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (hb i)))
  have hN_det : N.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, one_mul] at h
    have h' : diag_b.det * 1 = diag_b.det * N.det := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ h_det_ne h').symm
  refine ⟨⟨N, hN_det⟩, ?_⟩
  have h_Q_eq : (diagMat n b hb : GL (Fin n) ℚ) * SLnZ_to_GLnQ n ⟨N, hN_det⟩ =
      SLnZ_to_GLnQ n τ * diagMat n b hb := by
    apply Units.ext
    simp only [Units.val_mul, SLnZ_to_GLnQ_val, diagMat_val]
    have h_mul_map : ∀ (A B : Matrix (Fin n) (Fin n) ℤ),
        (A * B).map (Int.cast : ℤ → ℚ) = A.map Int.cast * B.map Int.cast := by
      intro A B; ext i j; simp [Matrix.mul_apply, Matrix.map_apply]
    have h_diag_map : (Matrix.diagonal (fun i => (b i : ℤ))).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal (fun i => (b i : ℚ)) := by
      ext i j; simp [Matrix.map_apply, Matrix.diagonal_apply]
    rw [← h_diag_map, ← h_mul_map, ← h_mul_map, h_int_eq]
  calc SLnZ_to_GLnQ n ⟨N, hN_det⟩
      = (diagMat n b hb)⁻¹ * (diagMat n b hb * SLnZ_to_GLnQ n ⟨N, hN_det⟩) := by
        rw [inv_mul_cancel_left]
    _ = (diagMat n b hb)⁻¹ * (SLnZ_to_GLnQ n τ * diagMat n b hb) := by rw [h_Q_eq]
    _ = (diagMat n b hb)⁻¹ * SLnZ_to_GLnQ n τ * diagMat n b hb := by rw [mul_assoc]

omit [NeZero n] in
/-- Set-level coprime product (Shimura Proposition 3.16, key step). -/
lemma doubleCoset_mul_coprime_mem (a b : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha : DivChain n a) (hb : DivChain n b) (hcop : Nat.Coprime (diagDet n a) (diagDet n b))
    (τ : SpecialLinearGroup (Fin n) ℤ) :
    diagMat n a ha_pos * SLnZ_to_GLnQ n τ * diagMat n b hb_pos ∈
    DoubleCoset.doubleCoset (diagMat n (diagMul n a b)
      (diagMul_pos n a b ha_pos hb_pos) : GL (Fin n) ℚ)
      (SLnZ_subgroup n) (SLnZ_subgroup n) := by
  obtain ⟨τ₁, τ₂, hτ, hτ₁, hτ₂⟩ := SLnZ_CRT_decomposition n
    (diagDet n a) (diagDet n b)
    (Finset.prod_pos (fun i _ => ha_pos i))
    (Finset.prod_pos (fun i _ => hb_pos i))
    hcop τ
  have hτ₁_cong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ₁ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := by
    intro i j
    convert hτ₁ i j using 1
    simp [diagDet]
  obtain ⟨σ₁, hσ₁⟩ := conjugate_congruent_mem_SLnZ n a ha_pos ha τ₁ hτ₁_cong
  have hτ₂_cong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ₂ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := by
    intro i j
    convert hτ₂ i j using 1
    simp [diagDet]
  obtain ⟨σ₂, hσ₂⟩ := inv_conjugate_congruent_mem_SLnZ n b hb_pos hb τ₂ hτ₂_cong
  rw [DoubleCoset.mem_doubleCoset]
  refine ⟨SLnZ_to_GLnQ n σ₁, ⟨σ₁, rfl⟩,
          SLnZ_to_GLnQ n σ₂, ⟨σ₂, rfl⟩, ?_⟩
  have hσ₁' : diagMat n a ha_pos * SLnZ_to_GLnQ n τ₁ =
      SLnZ_to_GLnQ n σ₁ * diagMat n a ha_pos := by
    rw [hσ₁]; group
  have hσ₂' : SLnZ_to_GLnQ n τ₂ * diagMat n b hb_pos =
      diagMat n b hb_pos * SLnZ_to_GLnQ n σ₂ := by
    rw [hσ₂]; group
  rw [hτ, map_mul]
  calc diagMat n a ha_pos * (SLnZ_to_GLnQ n τ₁ * SLnZ_to_GLnQ n τ₂) *
        diagMat n b hb_pos
      = diagMat n a ha_pos * SLnZ_to_GLnQ n τ₁ *
        (SLnZ_to_GLnQ n τ₂ * diagMat n b hb_pos) := by group
    _ = diagMat n a ha_pos * SLnZ_to_GLnQ n τ₁ *
        (diagMat n b hb_pos * SLnZ_to_GLnQ n σ₂) := by
        rw [hσ₂']
    _ = SLnZ_to_GLnQ n σ₁ * diagMat n a ha_pos *
        (diagMat n b hb_pos * SLnZ_to_GLnQ n σ₂) := by
        rw [hσ₁']
    _ = SLnZ_to_GLnQ n σ₁ * (diagMat n a ha_pos * diagMat n b hb_pos) *
        SLnZ_to_GLnQ n σ₂ := by group
    _ = SLnZ_to_GLnQ n σ₁ * diagMat n (diagMul n a b)
        (diagMul_pos n a b ha_pos hb_pos) * SLnZ_to_GLnQ n σ₂ := by
        rw [diagMat_mul]

lemma mulMap_coprime_eq (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha : DivChain n a) (hb : DivChain n b) (hab : DivChain n (diagMul n a b))
    (hcop : Nat.Coprime (diagDet n a) (diagDet n b))
    (p : decompQuot (GL_pair n) (T_diag n a ha_pos ha) ×
         decompQuot (GL_pair n) (T_diag n b hb_pos hb)) :
    mulMap (GL_pair n) (T_diag n a ha_pos ha) (T_diag n b hb_pos hb) p =
    T_diag n (diagMul n a b) (diagMul_pos n a b ha_pos hb_pos) hab := by
  set H := (GL_pair n).H
  have hδa_mem : ((T_diag n a ha_pos ha).eql.choose : GL (Fin n) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat n a ha_pos : GL (Fin n) ℚ) H H := by
    have h_spec := (T_diag n a ha_pos ha).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδa_mem
  obtain ⟨h₁a, hh₁a, h₂a, hh₂a, hδa_eq⟩ := hδa_mem
  have hδb_mem : ((T_diag n b hb_pos hb).eql.choose : GL (Fin n) ℚ) ∈
      DoubleCoset.doubleCoset (diagMat n b hb_pos : GL (Fin n) ℚ) H H := by
    have h_spec := (T_diag n b hb_pos hb).eql.choose_spec
    simp only [T_diag, T_mk, diagMat_delta] at h_spec
    rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
  rw [DoubleCoset.mem_doubleCoset] at hδb_mem
  obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := hδb_mem
  have hσ_mem : h₂a * (p.2.out : GL (Fin n) ℚ) * h₁b ∈ (SLnZ_to_GLnQ n).range :=
    (SLnZ_to_GLnQ n).range.mul_mem
      ((SLnZ_to_GLnQ n).range.mul_mem hh₂a (SetLike.coe_mem p.2.out)) hh₁b
  obtain ⟨σ, hσ⟩ := hσ_mem
  have h_cop := doubleCoset_mul_coprime_mem n a b ha_pos hb_pos ha hb hcop σ
  rw [hσ, DoubleCoset.mem_doubleCoset] at h_cop
  obtain ⟨hc₁, hhc₁, hc₂, hhc₂, h_eq⟩ := h_cop
  have h_product_mem : (p.1.out : GL (Fin n) ℚ) *
      ((T_diag n a ha_pos ha).eql.choose : GL (Fin n) ℚ) *
      ((p.2.out : GL (Fin n) ℚ) * ((T_diag n b hb_pos hb).eql.choose : GL (Fin n) ℚ)) ∈
      DoubleCoset.doubleCoset (diagMat n (diagMul n a b)
        (diagMul_pos n a b ha_pos hb_pos) : GL (Fin n) ℚ) H H := by
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨(p.1.out : GL (Fin n) ℚ) * h₁a * hc₁,
            H.mul_mem (H.mul_mem (SetLike.coe_mem p.1.out) hh₁a) hhc₁,
            hc₂ * h₂b,
            H.mul_mem hhc₂ hh₂b,
            ?_⟩
    set x1 := (↑(Quotient.out p.1) : GL (Fin n) ℚ)
    set da := ((T_diag n a ha_pos ha).eql.choose : GL (Fin n) ℚ)
    set x2 := (↑(Quotient.out p.2) : GL (Fin n) ℚ)
    set db := ((T_diag n b hb_pos hb).eql.choose : GL (Fin n) ℚ)
    rw [show da = h₁a * diagMat n a ha_pos * h₂a from hδa_eq,
        show db = h₁b * diagMat n b hb_pos * h₂b from hδb_eq]
    have h_mid : x1 * (h₁a * diagMat n a ha_pos * h₂a) *
        (x2 * (h₁b * diagMat n b hb_pos * h₂b)) =
        x1 * h₁a * (diagMat n a ha_pos * (h₂a * x2 * h₁b) *
          diagMat n b hb_pos) * h₂b := by
      group
    rw [h_mid, h_eq]; group
  apply HeckeRing.T'_ext (GL_pair n)
  exact doubleCoset_eq_of_mem' n _ _ h_product_mem

omit [NeZero n] in
private lemma GLnQ_mem_SLnZ_of_coprime_scaling (C : GL (Fin n) ℚ)
    (pa pb : ℕ) (hcop : Nat.Coprime pa pb) (h_det : (↑C : Matrix (Fin n) (Fin n) ℚ).det = 1)
    (h_a : ∀ i j, ∃ z : ℤ, (pa : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z)
    (h_b : ∀ i j, ∃ z : ℤ, (pb : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z) :
    C ∈ SLnZ_subgroup n := by
  have hcop_int : IsCoprime (pa : ℤ) (pb : ℤ) := by
    exact_mod_cast Nat.Coprime.isCoprime hcop
  obtain ⟨s, t, hst⟩ := hcop_int
  have h_int : ∀ i j, ∃ z : ℤ, (↑C : Matrix (Fin n) (Fin n) ℚ) i j = (z : ℚ) := by
    intro i j
    obtain ⟨za, hza⟩ := h_a i j
    obtain ⟨zb, hzb⟩ := h_b i j
    refine ⟨s * za + t * zb, ?_⟩
    have h1 : (↑C : Matrix (Fin n) (Fin n) ℚ) i j =
        s * ((pa : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) +
        t * ((pb : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) := by
      have hst_Q : (s : ℚ) * (pa : ℚ) + (t : ℚ) * (pb : ℚ) = 1 := by exact_mod_cast hst
      have := congr_arg (· * (↑C : Matrix (Fin n) (Fin n) ℚ) i j) hst_Q
      simp only [add_mul, one_mul] at this; linarith
    rw [h1, hza, hzb]; push_cast; ring
  set N : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => (h_int i j).choose
  have hN_eq : ∀ i j, (↑C : Matrix (Fin n) (Fin n) ℚ) i j = ((N i j : ℤ) : ℚ) := by
    intro i j; exact (h_int i j).choose_spec
  have hN_det : N.det = 1 := by
    have hN_cast : (↑C : Matrix (Fin n) (Fin n) ℚ) = N.map (Int.cast : ℤ → ℚ) := by
      ext i j; simp only [N, Matrix.of_apply, Matrix.map_apply]; exact hN_eq i j
    have : (N.det : ℚ) = 1 := by
      have h1 : (N.map (Int.cast : ℤ → ℚ)).det = (N.det : ℚ) := by
        exact (Int.cast_det N).symm
      rw [← h1, ← hN_cast, h_det]
    exact_mod_cast this
  rw [SLnZ_subgroup, MonoidHom.mem_range]
  refine ⟨⟨N, hN_det⟩, ?_⟩
  apply Units.ext
  simp only [SLnZ_to_GLnQ_val]
  ext i j
  simp only [Matrix.map_apply]
  exact (hN_eq i j).symm

omit [NeZero n] in
private lemma diagConj_scaling (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (σ : SpecialLinearGroup (Fin n) ℤ) (i j : Fin n) :
    ∃ z : ℤ, (∏ k, (a k : ℚ)) *
      ((↑((diagMat n a ha)⁻¹ * SLnZ_to_GLnQ n σ * diagMat n a ha) :
        Matrix (Fin n) (Fin n) ℚ) i j) = z := by
  set C := (diagMat n a ha)⁻¹ * SLnZ_to_GLnQ n σ * diagMat n a ha
  have h_mul : diagMat n a ha * C = SLnZ_to_GLnQ n σ * diagMat n a ha := by
    simp only [C, mul_assoc]; rw [mul_inv_cancel_left]
  have h_entry := congr_arg (fun (g : GL (Fin n) ℚ) => (↑g : Matrix _ _ ℚ) i j) h_mul
  simp only [Units.val_mul, diagMat_val, SLnZ_to_GLnQ_val,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply] at h_entry
  have h_dvd : (a i : ℤ) ∣ ∏ k, (a k : ℤ) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  refine ⟨(∏ k, (a k : ℤ)) / (a i : ℤ) * σ.val i j * (a j : ℤ), ?_⟩
  have hai_ne : (a i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (ha i).ne'
  have : (∏ k, (a k : ℚ)) * (↑C : Matrix _ _ ℚ) i j =
      (∏ k, (a k : ℚ)) / (a i : ℚ) * ((a i : ℚ) * (↑C : Matrix _ _ ℚ) i j) := by
    field_simp
  rw [this, h_entry]
  have hai_pos : (0 : ℤ) < (a i : ℤ) := Int.natCast_pos.mpr (ha i)
  have hai_ne_int : (a i : ℤ) ≠ 0 := ne_of_gt hai_pos
  rw [show ((∏ k, (a k : ℤ)) / (a i : ℤ) * σ.val i j * (a j : ℤ) : ℤ) =
      (∏ k, (a k : ℤ)) / (a i : ℤ) * ((σ.val i j : ℤ) * (a j : ℤ)) from by ring]
  push_cast [Int.cast_div h_dvd
    (show ((a i : ℤ) : ℚ) ≠ 0 from Int.cast_ne_zero.mpr hai_ne_int)]
  ring

omit [NeZero n] in
private lemma diagSandwich_scaling (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (F G E : SpecialLinearGroup (Fin n) ℤ) (i j : Fin n) :
    ∃ z : ℤ, (∏ k, (b k : ℚ)) *
      ((↑(SLnZ_to_GLnQ n F * diagMat n b hb * SLnZ_to_GLnQ n G *
        (diagMat n b hb)⁻¹ * SLnZ_to_GLnQ n E) :
        Matrix (Fin n) (Fin n) ℚ) i j) = z := by
  set C := SLnZ_to_GLnQ n F * diagMat n b hb * SLnZ_to_GLnQ n G *
    (diagMat n b hb)⁻¹ * SLnZ_to_GLnQ n E
  set D := diagMat n b hb * SLnZ_to_GLnQ n G * (diagMat n b hb)⁻¹
  have h_C_eq : C = SLnZ_to_GLnQ n F * D * SLnZ_to_GLnQ n E := by
    simp only [C, D, mul_assoc]
  set F_GL := SLnZ_to_GLnQ n F
  set E_GL := SLnZ_to_GLnQ n E
  have h_C_entry : (↑C : Matrix (Fin n) (Fin n) ℚ) i j = ∑ p, ∑ q,
      (↑F_GL : Matrix (Fin n) (Fin n) ℚ) i p *
      (↑D : Matrix (Fin n) (Fin n) ℚ) p q *
      (↑E_GL : Matrix (Fin n) (Fin n) ℚ) q j := by
    have := congr_arg (fun (g : GL (Fin n) ℚ) => (↑g : Matrix (Fin n) (Fin n) ℚ) i j) h_C_eq
    simp only [Units.val_mul, Matrix.mul_apply] at this
    rw [this]; simp only [Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  set D_mat := (↑D : Matrix (Fin n) (Fin n) ℚ)
  have h_D_scale : ∀ p q, ∃ z : ℤ, (∏ k, (b k : ℚ)) * D_mat p q = z := by
    intro p q
    have h_D_entry : D_mat p q =
        (b p : ℚ) * (↑(G.val p q) : ℚ) * ((b q : ℚ)⁻¹) := by
      have h_Db : D * diagMat n b hb = diagMat n b hb * SLnZ_to_GLnQ n G := by
        simp only [D, mul_assoc, inv_mul_cancel, mul_one]
      have h_entry := congr_arg
        (fun (g : GL (Fin n) ℚ) => (↑g : Matrix (Fin n) (Fin n) ℚ) p q) h_Db
      simp only [Units.val_mul, diagMat_val, SLnZ_to_GLnQ_val,
        Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply] at h_entry
      have hbq_ne : (b q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hb q).ne'
      field_simp at h_entry ⊢
      linarith
    rw [h_D_entry]
    have h_dvd : (b q : ℤ) ∣ ∏ k, (b k : ℤ) := Finset.dvd_prod_of_mem _ (Finset.mem_univ q)
    have hbq_ne : (b q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hb q).ne'
    have hbq_ne_int : (b q : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (hb q).ne'
    refine ⟨(∏ k, (b k : ℤ)) / (b q : ℤ) * (b p : ℤ) * G.val p q, ?_⟩
    have h_div_eq : (∏ k, (b k : ℚ)) * ((b p : ℚ) * ↑(G.val p q) * ((b q : ℚ)⁻¹)) =
        (∏ k, (b k : ℚ)) / (b q : ℚ) * ((b p : ℚ) * ↑(G.val p q)) := by
      rw [div_eq_mul_inv]; ring
    rw [h_div_eq]
    push_cast [Int.cast_div h_dvd
      (show ((b q : ℤ) : ℚ) ≠ 0 from
        Int.cast_ne_zero.mpr hbq_ne_int)]
    ring
  rw [h_C_entry, Finset.mul_sum]
  simp_rw [Finset.mul_sum, mul_assoc]
  refine ⟨∑ p, ∑ q, (F.val i p) * (h_D_scale p q).choose * (E.val q j), ?_⟩
  push_cast
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro q _
  have hDpq := (h_D_scale p q).choose_spec
  simp only [F_GL, E_GL, SLnZ_to_GLnQ_val, Matrix.map_apply]
  set z := (h_D_scale p q).choose with hz_def
  have hDpq' : (∏ k, (b k : ℚ)) * D_mat p q = (z : ℚ) := hDpq
  have h1 : (∏ k, (b k : ℚ)) *
      ((↑(F.val i p) : ℚ) * (D_mat p q * (↑(E.val q j) : ℚ))) =
      (↑(F.val i p) : ℚ) * ((∏ k, (b k : ℚ)) * D_mat p q) *
      (↑(E.val q j) : ℚ) := by ring
  rw [h1, hDpq']

omit [NeZero n] in
private lemma coprime_coupling_mem_H (a b : Fin n → ℕ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (_hda : DivChain n a) (_hdb : DivChain n b) (hcop : Nat.Coprime (diagDet n a) (diagDet n b))
    (σ F G E : SpecialLinearGroup (Fin n) ℤ)
    (h_eq : (diagMat n a ha)⁻¹ * SLnZ_to_GLnQ n σ * diagMat n a ha =
      SLnZ_to_GLnQ n F * diagMat n b hb * SLnZ_to_GLnQ n G *
      (diagMat n b hb)⁻¹ * SLnZ_to_GLnQ n E) :
    (diagMat n a ha)⁻¹ * SLnZ_to_GLnQ n σ * diagMat n a ha ∈ SLnZ_subgroup n := by
  set C := (diagMat n a ha)⁻¹ * SLnZ_to_GLnQ n σ * diagMat n a ha
  have h_det : (↑C : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
    simp only [C, Units.val_mul, Matrix.det_mul]
    rw [SLnZ_to_GLnQ_det, mul_one, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel]
    simp only [Units.val_one, Matrix.det_one]
  have h_scale_a : ∀ i j, ∃ z : ℤ,
      (↑(diagDet n a) : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z := by
    intro i j
    have := diagConj_scaling n a ha σ i j
    simp only [C, diagDet]
    convert this using 2
    push_cast; ring
  have h_scale_b : ∀ i j, ∃ z : ℤ,
      (↑(diagDet n b) : ℚ) * (↑C : Matrix (Fin n) (Fin n) ℚ) i j = z := by
    intro i j
    have h_C_rhs : C = SLnZ_to_GLnQ n F * diagMat n b hb * SLnZ_to_GLnQ n G *
      (diagMat n b hb)⁻¹ * SLnZ_to_GLnQ n E := h_eq
    rw [h_C_rhs]
    have := diagSandwich_scaling n b hb F G E i j
    simp only [diagDet]
    convert this using 2
    push_cast; ring
  exact GLnQ_mem_SLnZ_of_coprime_scaling n C (diagDet n a) (diagDet n b) hcop h_det
    h_scale_a h_scale_b

/-- Coprime product in the Hecke ring (Shimura Proposition 3.16). -/
theorem T_diag_mul_coprime (a b : Fin n → ℕ) (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (ha : DivChain n a) (hb : DivChain n b) (hcop : Nat.Coprime (diagDet n a) (diagDet n b)) :
    T_elem n a ha_pos ha * T_elem n b hb_pos hb =
    T_elem n (diagMul n a b) (diagMul_pos n a b ha_pos hb_pos)
      (DivChain_mul n a b ha hb) := by
  set D_a := T_diag n a ha_pos ha
  set D_b := T_diag n b hb_pos hb
  set hab := DivChain_mul n a b ha hb
  set D_ab := T_diag n (diagMul n a b) (diagMul_pos n a b ha_pos hb_pos) hab
  change HeckeRing.T_single (GL_pair n) ℤ D_a 1 * HeckeRing.T_single (GL_pair n) ℤ D_b 1 =
    HeckeRing.T_single (GL_pair n) ℤ D_ab 1
  rw [HeckeRing.T_single_one_mul_T_single_one]
  apply Finsupp.ext; intro A
  simp only [HeckeRing.m, Finsupp.coe_mk, Finsupp.single_apply]
  split_ifs with h1
  · rw [← h1]
    have h_le : HeckeRing.m' (GL_pair n) D_a D_b D_ab ≤ 1 := by
      classical
      simp only [HeckeRing.m']; norm_cast; rw [Nat.card_eq_fintype_card]
      apply Fintype.card_le_one_iff_subsingleton.mpr
      constructor; intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩
      simp only [Set.mem_setOf_eq] at h₁ h₂
      set H := (GL_pair n).H
      set δ_a' := (D_a.eql.choose : GL (Fin n) ℚ) with hδ_a_def
      set δ_b' := (D_b.eql.choose : GL (Fin n) ℚ) with hδ_b_def
      have h12 := h₁.trans h₂.symm
      have hi : i₁ = i₂ := by
        by_contra hne
        apply HeckeRing.decompQuot_coset_diff (GL_pair n) D_a i₁ i₂ hne
        have hδa_mem : δ_a' ∈ DoubleCoset.doubleCoset
            (diagMat n a ha_pos : GL (Fin n) ℚ) H H := by
          have h_spec := D_a.eql.choose_spec
          simp only [D_a, T_diag, T_mk, diagMat_delta] at h_spec
          rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
        rw [DoubleCoset.mem_doubleCoset] at hδa_mem
        obtain ⟨h₁a, hh₁a, h₂a, hh₂a, hδa_eq⟩ := hδa_mem
        have hδb_mem : δ_b' ∈ DoubleCoset.doubleCoset
            (diagMat n b hb_pos : GL (Fin n) ℚ) H H := by
          have h_spec := D_b.eql.choose_spec
          simp only [D_b, T_diag, T_mk, diagMat_delta] at h_spec
          rw [h_spec]; exact DoubleCoset.mem_doubleCoset_self H H _
        rw [DoubleCoset.mem_doubleCoset] at hδb_mem
        obtain ⟨h₁b, hh₁b, h₂b, hh₂b, hδb_eq⟩ := hδb_mem
        have hσ'_mem :
            h₁a⁻¹ * ((i₂.out : GL (Fin n) ℚ)⁻¹ *
            (i₁.out : GL (Fin n) ℚ)) *
            h₁a ∈ (SLnZ_to_GLnQ n).range :=
          show _ ∈ H from H.mul_mem (H.mul_mem (H.inv_mem hh₁a)
            (H.mul_mem (H.inv_mem (SetLike.coe_mem i₂.out)) (SetLike.coe_mem i₁.out))) hh₁a
        obtain ⟨σ', hσ'⟩ := hσ'_mem
        have hmem12 :
            (i₁.out : GL (Fin n) ℚ) * δ_a' *
            ((j₁.out : GL (Fin n) ℚ) * δ_b') ∈
            ({(i₂.out : GL (Fin n) ℚ) * δ_a' *
            ((j₂.out : GL (Fin n) ℚ) * δ_b')} : Set _) *
            (H : Set _) := by
          have h12' : ({(i₁.out : GL (Fin n) ℚ) * δ_a' *
              ((j₁.out : GL (Fin n) ℚ) * δ_b')} : Set _) * (H : Set _) =
              ({(i₂.out : GL (Fin n) ℚ) * δ_a' *
              ((j₂.out : GL (Fin n) ℚ) * δ_b')} : Set _) * (H : Set _) := by
            have := h12
            rw [Set.singleton_mul_singleton, Set.singleton_mul_singleton] at this
            exact this
          rw [← h12']
          exact ⟨_, Set.mem_singleton _, 1, H.one_mem, by simp⟩
        obtain ⟨_, h_sing, κ, hκ, hκ_eq⟩ := hmem12
        rw [Set.mem_singleton_iff] at h_sing; subst h_sing
        have h_beta_eq :
            δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ *
            (i₁.out : GL (Fin n) ℚ) * δ_a' =
            (j₂.out : GL (Fin n) ℚ) * δ_b' * κ *
            δ_b'⁻¹ * (j₁.out : GL (Fin n) ℚ)⁻¹ := by
          have hκ_eq' :
              (i₂.out : GL (Fin n) ℚ) * δ_a' *
              ((j₂.out : GL (Fin n) ℚ) * δ_b') * κ =
              (i₁.out : GL (Fin n) ℚ) * δ_a' *
              ((j₁.out : GL (Fin n) ℚ) * δ_b') := by
            exact hκ_eq
          apply mul_left_cancel (a := (i₂.out : GL (Fin n) ℚ) * δ_a')
          apply mul_right_cancel (b := (j₁.out : GL (Fin n) ℚ) * δ_b')
          simp only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, inv_mul_cancel,
            mul_one]
          simp only [mul_assoc] at hκ_eq'
          exact hκ_eq'.symm
        have h_lhs_eq :
            δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ *
            (i₁.out : GL (Fin n) ℚ) * δ_a' =
            h₂a⁻¹ * ((diagMat n a ha_pos)⁻¹ *
            SLnZ_to_GLnQ n σ' * diagMat n a ha_pos) * h₂a := by
          rw [hσ', hδa_eq]
          simp only [_root_.mul_inv_rev, mul_assoc]
        have hF_mem : (j₂.out : GL (Fin n) ℚ) * h₁b ∈ (SLnZ_to_GLnQ n).range :=
          show _ ∈ H from H.mul_mem (SetLike.coe_mem j₂.out) hh₁b
        obtain ⟨F_pre, hF_pre⟩ := hF_mem
        have hG_mem : h₂b * κ * h₂b⁻¹ ∈ (SLnZ_to_GLnQ n).range :=
          show _ ∈ H from H.mul_mem (H.mul_mem hh₂b hκ) (H.inv_mem hh₂b)
        obtain ⟨G_pre, hG_pre⟩ := hG_mem
        have hE_mem : h₁b⁻¹ * (j₁.out : GL (Fin n) ℚ)⁻¹ ∈ (SLnZ_to_GLnQ n).range :=
          show _ ∈ H from H.mul_mem (H.inv_mem hh₁b) (H.inv_mem (SetLike.coe_mem j₁.out))
        obtain ⟨E_pre, hE_pre⟩ := hE_mem
        have h_rhs_eq : (j₂.out : GL (Fin n) ℚ) * δ_b' * κ * δ_b'⁻¹ *
            (j₁.out : GL (Fin n) ℚ)⁻¹ =
            SLnZ_to_GLnQ n F_pre * diagMat n b hb_pos * SLnZ_to_GLnQ n G_pre *
            (diagMat n b hb_pos)⁻¹ * SLnZ_to_GLnQ n E_pre := by
          rw [hF_pre, hG_pre, hE_pre, hδb_eq]
          simp only [_root_.mul_inv_rev, mul_assoc]
        have hFF_mem : h₂a * SLnZ_to_GLnQ n F_pre ∈ (SLnZ_to_GLnQ n).range :=
          show _ ∈ H from H.mul_mem hh₂a ⟨F_pre, rfl⟩
        obtain ⟨FF, hFF⟩ := hFF_mem
        have hEE_mem : SLnZ_to_GLnQ n E_pre * h₂a⁻¹ ∈ (SLnZ_to_GLnQ n).range :=
          show _ ∈ H from H.mul_mem ⟨E_pre, rfl⟩ (H.inv_mem hh₂a)
        obtain ⟨EE, hEE⟩ := hEE_mem
        have h_C_eq : (diagMat n a ha_pos)⁻¹ * SLnZ_to_GLnQ n σ' *
            diagMat n a ha_pos =
            SLnZ_to_GLnQ n FF * diagMat n b hb_pos * SLnZ_to_GLnQ n G_pre *
            (diagMat n b hb_pos)⁻¹ * SLnZ_to_GLnQ n EE := by
          have h_combined := h_beta_eq
          rw [h_lhs_eq, h_rhs_eq] at h_combined
          apply mul_left_cancel (a := h₂a⁻¹)
          apply mul_right_cancel (b := h₂a)
          rw [hFF, hEE]
          simp only [mul_assoc, inv_mul_cancel, mul_one,
            inv_mul_cancel_left]
          simp only [mul_assoc] at h_combined
          exact h_combined
        have h_C_in_H :=
          coprime_coupling_mem_H n a b ha_pos hb_pos ha hb hcop σ' FF G_pre EE h_C_eq
        have h_beta_in_H : δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ *
            (i₁.out : GL (Fin n) ℚ) * δ_a' ∈ H := by
          rw [h_lhs_eq]
          exact H.mul_mem (H.mul_mem (H.inv_mem hh₂a) h_C_in_H) hh₂a
        exact HeckeRing.leftCoset_eq_of_not_disjoint (H := (GL_pair n).H) _ _ (by
          rw [Set.not_disjoint_iff]
          exact ⟨(i₁.out : GL (Fin n) ℚ) * δ_a',
            ⟨1, H.one_mem, mul_one _⟩,
            ⟨δ_a'⁻¹ * (i₂.out : GL (Fin n) ℚ)⁻¹ *
              (i₁.out : GL (Fin n) ℚ) * δ_a', h_beta_in_H, by
                simp only [smul_eq_mul, ← hδ_a_def]; group⟩⟩)
      subst hi
      have hj : j₁ = j₂ := by
        by_contra hne
        exact HeckeRing.decompQuot_coset_diff (GL_pair n) D_b j₁ j₂ hne
          (HeckeRing.set_singleton_mul_left_cancel _ (by
            have := h₁.trans h₂.symm; rwa [mul_assoc, mul_assoc] at this))
      subst hj; rfl
    have h_pos : 0 < HeckeRing.m' (GL_pair n) D_a D_b D_ab := by
      have h_mem : D_ab ∈ HeckeRing.mulSupport (GL_pair n) D_a D_b := by
        simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
          true_and, Prod.exists]
        have ⟨i₀⟩ : Nonempty (decompQuot (GL_pair n) D_a) :=
          Fintype.card_pos_iff.mp (by
            have := HeckeRing.T'_deg_pos (GL_pair n) D_a
            simp only [HeckeRing.T'_deg] at this; omega)
        have ⟨j₀⟩ : Nonempty (decompQuot (GL_pair n) D_b) :=
          Fintype.card_pos_iff.mp (by
            have := HeckeRing.T'_deg_pos (GL_pair n) D_b
            simp only [HeckeRing.T'_deg] at this; omega)
        exact ⟨i₀, j₀, mulMap_coprime_eq n a b ha_pos hb_pos ha hb hab hcop (i₀, j₀)⟩
      have h_ne := HeckeRing.m'_pos_of_mem_mulSupport (GL_pair n) D_a D_b D_ab h_mem
      have : (0 : ℤ) ≤ HeckeRing.m' (GL_pair n) D_a D_b D_ab := by
        simp only [HeckeRing.m']; exact Nat.cast_nonneg _
      omega
    omega
  · apply HeckeRing.m'_eq_zero_of_nmem_mulSupport
    intro h_mem
    simp only [HeckeRing.mulSupport, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ,
      true_and] at h_mem
    obtain ⟨⟨i, j⟩, heq⟩ := h_mem
    exact (Ne.symm h1) (heq.symm.trans
      (mulMap_coprime_eq n a b ha_pos hb_pos ha hb hab hcop (i, j)))

end Coprime

end HeckeRing.GLn
