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

/-! ### Trailing-block HNF interface (column-HNF route)

The remaining open theorem `sl_exists_col_stab_divChain` at `k ≥ 1` reduces to the
construction of an `SL_{k+1}(ℤ)` matrix `R` that puts the trailing
`(k+2) × (k+1)` block of an arbitrary `SL_{k+2}(ℤ)` extension `N₀` of `w` into
"column-HNF" form satisfying the `a i / a j` divisibility chain. The interface
below packages this as `TrailingBlockHNFData a w` and provides the structural
consumer producing a `StrengthenedCompletionTarget`. The remaining open piece —
the existence of such an `R` — is exactly the trailing-block HNF construction
(an SL-version of column-Hermite-normal-form preserving the divisibility chain).

The block matrix `slSuccEmbed R` (already developed above) gives the SL-version
of the block diagonal `[[1, 0], [0, R]] ∈ SL_{k+2}(ℤ)`. Its right-action on
`N₀ ∈ SL_{k+2}(ℤ)` preserves column 0 (because column 0 of `slSuccEmbed R` is
`e₀`) and reshapes the trailing block via right-multiplication by `R`. -/

/-- **Right-multiplication by `slSuccEmbed R` preserves column 0** of any
`SL_{k+2}(ℤ)` matrix. This is the structural property that ordinary square SNF
lacked: it lets us improve the trailing block of an extension `N₀` of a vector
`w` without disturbing the prescribed first column. -/
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

/-! ### 2-column Bezout reduction helper (T001)

The `bezout2` matrix below is the elementary 2-column operation that, embedded
into `SL (Fin (k+1)) ℤ` via a block scheme and then via `slSuccEmbed` into
`SL (Fin (k+2)) ℤ`, reduces a single pair of columns of the trailing block.
Iterating column-by-column produces a column-HNF for the trailing block.

Right-multiplying the row vector `[x, y]` by `bezout2 x y` yields the row
`[Int.gcd x y, 0]`. When `Int.gcd x y = 0` (equivalently `x = y = 0`) the
matrix collapses to the identity.
-/

/-- The 2×2 Bezout reduction matrix. Right-multiplication by this matrix sends
the row `[x, y]` to `[Int.gcd x y, 0]`. -/
private def bezout2 (x y : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (Int.gcd x y : ℤ) = 0 then 1 else
  !![Int.gcdA x y, -y / (Int.gcd x y : ℤ);
     Int.gcdB x y,  x / (Int.gcd x y : ℤ)]

/-- Row action of `bezout2` on the first column gives `Int.gcd x y`. -/
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

/-- Row action of `bezout2` on the second column gives `0`. -/
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

/-- The 2×2 Bezout reduction matrix has determinant `1` whenever
`Int.gcd x y ≠ 0`. -/
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

/-- `SL₂(ℤ)` packaging of the 2×2 Bezout reduction matrix, valid when
`Int.gcd x y ≠ 0`. -/
private noncomputable def bezout2SL (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    SpecialLinearGroup (Fin 2) ℤ :=
  ⟨bezout2 x y, bezout2_det x y hg⟩

/-! ### Trailing-pair Bezout embedding into `SL(Fin (r + 2)) ℤ`

The 2×2 Bezout reduction matrix `bezout2SL x y hg` lifts to an
`SL(Fin (r + 2)) ℤ` matrix that acts as `bezout2 x y` on the last two
indices and as the identity on the leading `r × r` block. The
construction is by recursion on `r`, using the block embedding
`slSuccEmbed` which prepends a `1`-row/column to the front. -/

/-- The trailing-pair Bezout embedding: an `SL(Fin (r + 2)) ℤ` matrix that
acts as `bezout2 x y` on the trailing `2 × 2` block (indices
`Fin.natAdd r i` for `i : Fin 2`) and as the identity on the leading
`r × r` block. -/
private noncomputable def bezout2TrailingSL : (r : ℕ) → (x y : ℤ) →
    ((Int.gcd x y : ℤ) ≠ 0) → SpecialLinearGroup (Fin (r + 2)) ℤ
  | 0,     x, y, hg => bezout2SL x y hg
  | r + 1, x, y, hg => slSuccEmbed (bezout2TrailingSL r x y hg)

/-- Defining equation for `bezout2TrailingSL` at `r = 0`. -/
private lemma bezout2TrailingSL_zero (x y : ℤ) (hg : (Int.gcd x y : ℤ) ≠ 0) :
    bezout2TrailingSL 0 x y hg = bezout2SL x y hg := rfl

/-- Defining equation for `bezout2TrailingSL` at `r + 1`: prepend a `1`-row
and `1`-column via `slSuccEmbed`. -/
private lemma bezout2TrailingSL_succ (r : ℕ) (x y : ℤ)
    (hg : (Int.gcd x y : ℤ) ≠ 0) :
    bezout2TrailingSL (r + 1) x y hg =
      slSuccEmbed (bezout2TrailingSL r x y hg) := rfl

/-- **Trailing block entries.** The `(Fin.natAdd r i, Fin.natAdd r j)` entry
of `bezout2TrailingSL r x y hg` is exactly the `(i, j)` entry of the
underlying `2 × 2` Bezout matrix `bezout2 x y`. This is the central
action lemma describing the trailing-pair behavior. -/
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

/-- **Top-left identity block.** On the leading `r × r` block (indices
`Fin.castAdd 2 i` and `Fin.castAdd 2 j` for `i j : Fin r`), the matrix
`bezout2TrailingSL r x y hg` agrees with the identity. -/
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

/-- **Mixed top-right block: identity rows are zero past the diagonal.**
On the leading-row / trailing-column block, the matrix is zero. -/
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

/-- **Mixed bottom-left block: identity columns are zero past the diagonal.**
On the trailing-row / leading-column block, the matrix is zero. -/
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

/-- **Row action of `bezout2TrailingSL` on the trailing column 0.**
For a row `i` of `M` whose trailing pair is `(x, y)`, right-multiplication by
`bezout2TrailingSL r x y hg` produces `Int.gcd x y` at the `Fin.natAdd r 0`
position. -/
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

/-- **Row action of `bezout2TrailingSL` on the trailing column 1.**
For a row `i` of `M` whose trailing pair is `(x, y)`, right-multiplication by
`bezout2TrailingSL r x y hg` produces `0` at the `Fin.natAdd r 1`
position. -/
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

/-- **Preservation of leading columns by `bezout2TrailingSL`.**
Right-multiplication by `bezout2TrailingSL r x y hg` does not alter the
leading `r` columns of `M` (those indexed by `Fin.castAdd 2 j` for `j : Fin r`). -/
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


/-- **Trailing-block HNF data** for `(a, w)`. This packages exactly the data
needed to build a `StrengthenedCompletionTarget`: an arbitrary SL-extension `N₀`
of `w` (col 0 = `w`) together with an `SL_{k+1}(ℤ)` transformation `R` whose
right-action on the trailing `(k+2) × (k+1)` block of `N₀` produces the
`a i / a j` divisibility chain. The block diagonal `slSuccEmbed R` preserves col 0
(`slSuccEmbed_preserves_col_zero`), so the product `N₀ * slSuccEmbed R` is the
desired strengthened completion. -/
private def TrailingBlockHNFData {k : ℕ}
    (a : Fin (k + 1) → ℕ) (w : Fin (k + 2) → ℤ) : Prop :=
  ∃ (N₀ : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (R : SpecialLinearGroup (Fin (k + 1)) ℤ),
    (∀ i, N₀.1 i 0 = w i) ∧
    (∀ i j : Fin (k + 1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣
        ∑ k' : Fin (k + 1), N₀.1 i.succ k'.succ * R.1 k' j))

/-- **Conditional consumer.** From `TrailingBlockHNFData a w`, build a
`StrengthenedCompletionTarget a w`. The construction is `N := N₀ * slSuccEmbed R`:
column 0 is preserved by `slSuccEmbed_preserves_col_zero`, and the trailing
divisibility comes from the `R`-witness in `TrailingBlockHNFData`. -/
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

/-- **Conditional consumer for `TrailingBlockHNFData`.** Composing
`strengthenedCompletionTarget_of_trailing_hnf_data` with
`sl_exists_col_stab_divChain_of_strengthened_completion` gives the desired
SL stabilizer-membership statement directly from a `TrailingBlockHNFData`
witness. This is the named clean target for downstream HNF-construction work.
Note: `hw_primitive` is absorbed into the `N₀` field of `TrailingBlockHNFData`
(any SL-extension of `w` exists iff `w` is primitive). -/
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

/-- **Bridge: `StrengthenedCompletionTarget` implies `TrailingBlockHNFData`.**
The trailing-block HNF route with `R = 1` (identity in `SL_{k+1}(ℤ)`) is sufficient
to recover any `StrengthenedCompletionTarget`: take `N₀ := N` (the strengthened
completion) and `R := 1`. The trailing-block sum `∑ k', N.1 i.succ k'.succ * R.1 k' j`
collapses to `N.1 i.succ j.succ` since the identity matrix is supported on the
diagonal, and the strengthened completion's lower-triangular divisibility supplies
the divisibility witness.

This makes explicit that `StrengthenedCompletionTarget` and `TrailingBlockHNFData`
are equivalent (the forward direction is `strengthenedCompletionTarget_of_trailing_hnf_data`),
isolating the open existence question to either of the two equivalent forms. -/
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

/-! ### Column-HNF iteration: explicit remaining gap

The construction of `TrailingBlockHNFData a w` from `hw_primitive` + `hw_col_div`
reduces — via `sl_exists_col_of_primitive` — to producing, for any chosen SL
completion `N₀` of `w` (col 0 = `w`), a transformation `R : SL_{k+1}(ℤ)` whose
right-action on the trailing `(k+2) × (k+1)` block of `N₀` enforces the
`(a i / a j)`-divisibility chain on strict-lower entries.

The honest remaining theorem is:

```
∀ (a : Fin (k+1) → ℕ) (hda : DivChain (k+1) a)
  (N₀ : SpecialLinearGroup (Fin (k+2)) ℤ),
  ∃ R : SpecialLinearGroup (Fin (k+1)) ℤ,
    ∀ i j : Fin (k+1), j < i →
      (((a i / a j : ℕ) : ℤ) ∣
        ∑ k' : Fin (k+1), N₀.1 i.succ k'.succ * R.1 k' j)
```

The construction is column-HNF iteration on the trailing block: iterate the
one-step Bezout adapter `sl_mul_slSuccEmbed_bezout2TrailingSL_apply` to clear
above-diagonal entries within each column while preserving lower divisibility,
producing a finite product of `slSuccEmbed (bezout2TrailingSL …)` factors whose
combined right-action delivers `R`.

The conditional helper `trailingBlockHNFData_of_R_existence` below converts
this hypothesis into a `TrailingBlockHNFData` witness, isolating the remaining
arithmetic content. -/

/-- **Conditional helper for `TrailingBlockHNFData`.** Given the existence,
for **every** SL completion `N₀` of `w` (col 0 = `w`), of an
`R : SL_{k+1}(ℤ)` such that the right-action of `R` on the trailing block of
`N₀` enforces the `(a i / a j)`-divisibility chain on strict-lower entries,
package the resulting data into `TrailingBlockHNFData a w`.

The proof obtains a canonical `N₀` from `sl_exists_col_of_primitive`, applies
the hypothesis to extract `R`, and packages the pair into a
`TrailingBlockHNFData` witness.

This helper expresses cleanly the column-HNF iteration content as the only
remaining open piece: the existence of `R` is the genuine remaining
mathematics. The hypothesis is stated "for every `N₀`" (rather than for the
specific witness of `sl_exists_col_of_primitive`) because the existence of
the column-HNF reduction is a generic statement about SL extensions, not
tied to a particular completion. -/
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

/-- **Honest one-step trailing-pair update.** Right-multiplication of `M` by
`bezout2TrailingSL r x y hg` (with `(x, y)` chosen as the trailing pair of a
target row `i_target`) has exactly five effects:

1. The target row's final pair becomes `(gcd x y, 0)`.
2. The first `r` columns are preserved for **every** row.
3-5. Other rows' final two entries become explicit linear combinations of their
     own trailing pair via the `bezout2 x y` entries — they are **not**
     preserved in general. -/
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
  · -- Trailing column 0, arbitrary row: linear combination via bezout2.
    intro i
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
  · -- Trailing column 1, arbitrary row: linear combination via bezout2.
    intro i
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

/-- **Bridge: trailing-block product through `slSuccEmbed`.** For
`N₀ : SL_{r+3}(ℤ)` and `U : SL_{r+2}(ℤ)`, the `(i.succ, j.succ)` entry of
`N₀ * slSuccEmbed U` equals the `(i, j)` entry of `M * U.val`, where `M` is the
trailing `(r+2) × (r+2)` block of `N₀` (`M i j := N₀.1 i.succ j.succ`).

This is the structural identity that lets `matrix_mul_bezout2TrailingSL_apply`
be transported from the bare matrix level to the `SL` product
`N₀ * slSuccEmbed (bezout2TrailingSL r x y hg)`. -/
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

/-- **Matrix-level Bezout one-step transported to `N₀ * slSuccEmbed U`.**
Given `N₀ : SL_{r+3}(ℤ)` and a target trailing row `i_target : Fin (r+2)` whose
final pair `(N₀.1 i_target.succ (Fin.natAdd r 0).succ,
N₀.1 i_target.succ (Fin.natAdd r 1).succ)` equals `(x, y)`, right-multiplication
by `slSuccEmbed (bezout2TrailingSL r x y hg)` has the four expected effects:
column 0 preserved, the first `r` trailing columns preserved on every trailing
row, the target trailing pair becomes `(gcd, 0)`, and every other trailing row's
final pair is the `bezout2`-linear combination of its old final pair. -/
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
  · -- (1) column 0 preserved.
    intro i
    exact slSuccEmbed_preserves_col_zero (bezout2TrailingSL r x y hg) N₀ i
  · -- (2) first `r` trailing columns preserved on every trailing row.
    intro i j
    have := h3 i j
    rw [hbridge i (Fin.castAdd 2 j)]
    simpa [hM_def] using this
  · -- (3) target trailing column 0 becomes `gcd`.
    rw [hbridge i_target (Fin.natAdd r 0)]; exact h1
  · -- (3') target trailing column 1 becomes `0`.
    rw [hbridge i_target (Fin.natAdd r 1)]; exact h2
  · -- (4) trailing column 0 linear combination on every trailing row.
    intro i
    have := h4 i
    rw [hbridge i (Fin.natAdd r 0)]
    simpa [hM_def] using this
  · -- (4') trailing column 1 linear combination on every trailing row.
    intro i
    have := h5 i
    rw [hbridge i (Fin.natAdd r 1)]
    simpa [hM_def] using this

/-- **Trailing-pair `SL₂(ℤ)` orthogonalizer.** For any integer pair `(x, y)`,
there exists `R ∈ SL_2(ℤ)` whose first column gives a ℤ-linear combination of
`(x, y)` equal to zero: `x * R.1 0 0 + y * R.1 1 0 = 0`. The construction is
`R := 1` for the degenerate case `(x, y) = (0, 0)`, and otherwise extends the
primitive pair `(y / g, -(x / g))` (where `g = Int.gcd x y > 0`) to an
`SL_2(ℤ)` matrix via `IsCoprime.exists_SL2_col`. This is the structural
content underlying the `k = 1` case of the trailing-block column-HNF
reduction. -/
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

/-- **`k = 1` case of `sl_exists_col_stab_divChain`.**
The trailing block has size `2 × 2`, with a single divisibility constraint at
`(i, j) = (1, 0)`. Pick `N₀ : SL_3(ℤ)` extending `w` via
`sl_exists_col_of_primitive`; pick `R : SL_2(ℤ)` orthogonalizing the trailing
pair `(N₀.1 2 1, N₀.1 2 2)` via `exists_sl2_first_col_orthogonal`. The
trailing-block sum at `(1, 0)` then evaluates to `0`, which is divisible by
`(a 1 / a 0)`. The general `k ≥ 2` case (column-HNF iteration) is the remaining
content of `sl_exists_col_stab_divChain` and is left as a focused gap. -/
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

/-- **Existence of a non-zero kernel vector via rank-nullity.**  Any
`(m + 1) × (m + 2)` integer matrix `N` has a non-zero integer vector in its
right kernel (column-vector orientation): there exists `v : Fin (m + 2) → ℤ`
with `v ≠ 0` and `∀ i, ∑ j, N i j * v j = 0`.

Proof:  view `N` as the linear map `N.mulVecLin : ℤ^{m+2} → ℤ^{m+1}`.  If its
kernel were `⊥`, the map would be injective, forcing
`finrank ℤ (Fin (m + 2) → ℤ) ≤ finrank ℤ (Fin (m + 1) → ℤ)` via
`LinearMap.finrank_le_finrank_of_injective`, i.e. `m + 2 ≤ m + 1`, a
contradiction.  Hence the kernel is non-`⊥`; `Submodule.exists_mem_ne_zero_of_ne_bot`
extracts a non-zero element, and translation through `Matrix.mulVecLin_apply` /
`Matrix.mulVec` yields the component-wise sum equation. -/
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

/-- **Primitive-kernel-vector lemma.**  Any `(m + 1) × (m + 2)` integer matrix
`N` has a primitive integer vector in its right kernel.  Proven by composing
`exists_nonzero_kernel_vec` (a non-zero kernel vector) with a gcd-normalisation
step:  divide each entry by the gcd of all entries to obtain a primitive vector
that is still in the kernel (since the kernel of a linear map between free
`ℤ`-modules is closed under integer division when the result is integer). -/
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
  · -- Primitivity:  any common divisor `d` of `v j / g` satisfies `d * g ∣ g`,
    intro d hd
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
  · -- Kernel:  multiply by `g` to reduce to the original kernel relation.
    intro i
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

/-- **Single-column clearing for the column-HNF inductive step.**  For any
`(n + 2) × (n + 2)` integer matrix `M`, there exists `R ∈ SL_(n+2)(ℤ)` such
that the first column of `M * R` has zero in every row below row 0, i.e.,
`(M * R)[i.succ][0] = 0` for all `i : Fin (n + 1)`.

Proven from the strictly-smaller `exists_primitive_kernel_vec` blocker:
extract a primitive vector `v` in the right kernel of `M`'s rows `1, …, n + 1`,
then use `sl_exists_col_of_primitive` to lift `v` to an `SL_(n+2)(ℤ)` matrix
whose first column equals `v`.  The kernel-vector condition then exactly
matches `(M * R)[i.succ][0] = 0`. -/
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

/-- **Upper-triangularization base case, `n = 2`.**  Right-multiplication by the
trailing-pair orthogonalizer `exists_sl2_first_col_orthogonal (M 1 0) (M 1 1)`
zeroes the unique strict-lower entry `(1, 0)`. -/
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

/-- **Upper-triangularization inductive assembly.**  Combines a column-0 clearer
`R₁` (zeroing entries below row 0 of `M * R₁`) with an upper-triangularizer `R'`
for the trailing `(n + 2) × (n + 2)` block of `M * R₁` (rows/cols past index 0).
Embedding `R'` via `slSuccEmbed`, the product `R₁ * slSuccEmbed R'` makes
`M * (R₁ * slSuccEmbed R')` upper triangular.  Stated with the tail-solution
hypothesis explicit so it is independent of the recursion in
`sl_upperTri_for_matrix`. -/
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
  · -- `i = 0`:  vacuous (`j < 0` impossible).
    subst hi; exact absurd hji (Fin.not_lt_zero _)
  · subst hi
    rcases Fin.eq_zero_or_eq_succ j with hj | ⟨j', hj⟩
    · -- `j = 0`:  goal reduces to `(M * R₁.val) i'.succ 0 = 0`.
      subst hj
      simp only [slSuccEmbed_val_zero_zero, mul_one, slSuccEmbed_val_succ_zero,
        mul_zero, Finset.sum_const_zero, add_zero]
      exact hR₁ i'
    · -- `j = j'.succ`:  goal reduces to `(Mtail * R'.val) i' j' = 0` via the tail solution.
      subst hj
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

/-- **Trailing-block column upper-triangularization (general dim).**  For any
`n × n` integer matrix `M`, there exists `R ∈ SL_n(ℤ)` such that the
strict-lower entries of `M * R` are zero (i.e., `M * R` is upper triangular).
This is the column-HNF iteration for arbitrary square integer matrices.

Fully proven via:  the trivial cases `n ≤ 1` (vacuous constraint), the
`n = 2` base case (`exists_sl_upperTri_two`), and an inductive step for `n + 3`
that combines `exists_sl_clear_col_zero` (clears column 0 below row 0) with the
recursive IH applied to the `(n + 2) × (n + 2)` trailing submatrix below row 0 /
column 0, assembled by `exists_sl_upperTri_succ_of_clear_tail`.  The
single-column clearer is itself proven from the strictly-smaller
`exists_primitive_kernel_vec`, which is the only remaining algebraic blocker. -/
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

/-- **Primitive vector completion with DivChain-respecting stabilizer
membership** — the isolated combinatorial core behind
`fiber_has_block_form_preimages`. Given a primitive integer vector
`w : Fin (k+2) → ℤ` whose entries satisfy the DivChain-forced column-0
divisibility `a_{i-1} ∣ w_{i.succ}`, there exists `N ∈ SL_{k+2}(ℤ)` with
first column `w` and with `N` in the stabilizer of `diagMat (Fin.cons 1 a)`
(equivalently: the lower-triangular entries of `N` satisfy the
`a_{i-1}/a_{j-1}` divisibility for `i > j > 0`). The proof is a classical
Smith-normal-form / column-by-column Bezout construction; it does not depend
on the specific Shimura fiber context. -/
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
  · -- k + 2 case: build a TrailingBlockHNFData via `sl_upperTri_for_matrix`.
    refine sl_exists_col_stab_divChain_of_trailing_hnf_data a ha hda w hw_col_div ?_
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
