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

/-! ### Diagonal-level ≤ direction (Shimura Lemma 3.19 hard half)

The harder half of Shimura's Lemma 3.19: injection `Fiber_{k+2}^{cons1} → Fiber_{k+1}`.
Proof requires the lattice projection `M' ↦ M = M' ∩ L'` via the quotient-level
normalization: any fiber pair at dim `k+2` has `slSuccEmbed_H`-preimages satisfying
the dim-`k+1` fiber condition. Formally isolated as `fiber_block_form_preimage`
below; currently stated but not proved.

The mathematical core (Shimura p. 59, bottom): given `σ, τ ∈ SL_{k+2}(ℤ)` in a fiber
pair at dim `k+2` with `Fin.cons 1 _` diagonals, there exist equivalent representatives
`σ̃ ~ σ`, `τ̃ ~ τ` (mod the respective stabilizers) such that `σ̃, τ̃` both have
block form `1 ⊕ σ_m`, `1 ⊕ τ_m`, and `(σ_m, τ_m)` forms a fiber pair at dim `k+1`. -/

/-- **First column of `SL_n(ℤ)` is primitive.** Any common integer divisor of
the entries of column 0 of an `SL_n(ℤ)` matrix is a unit (`±1`). Follows from
Laplace expansion of the determinant along column 0. -/
lemma sl_first_col_primitive {n : ℕ} [NeZero n]
    (N : SpecialLinearGroup (Fin n) ℤ) (d : ℤ)
    (hd : ∀ i, d ∣ N.1 i 0) : IsUnit d := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  have h_dvd_det : d ∣ N.1.det := by
    rw [Matrix.det_succ_column_zero]
    refine Finset.dvd_sum fun i _ ↦ ?_
    exact ((hd i).mul_left _).mul_right _
  rw [show N.1.det = 1 from N.2] at h_dvd_det
  exact isUnit_of_dvd_one h_dvd_det

/-- **Row primitivity for `SL_n(ℤ)`.** Any common integer divisor of the entries
of an arbitrary row `r` of an `SL_n(ℤ)` matrix is a unit (`±1`). Follows from
Laplace expansion of the determinant along row `r`. -/
private lemma sl_row_primitive {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (d : ℤ) (hd : ∀ k : Fin n.succ, d ∣ N.1 r k) : IsUnit d := by
  have h_dvd_det : d ∣ N.1.det := by
    rw [Matrix.det_succ_row N.1 r]
    refine Finset.dvd_sum fun j _ ↦ ?_
    exact ((hd j).mul_left _).mul_right _
  rw [show N.1.det = 1 from N.2] at h_dvd_det
  exact isUnit_of_dvd_one h_dvd_det

/-- **Row non-divisibility by a non-unit.** If `p : ℤ` is not a unit, then for
any row `r` of `N ∈ SL_n(ℤ)` there is some column `k` with `p ∤ N.1 r k`.
Direct contrapositive of `sl_row_primitive`. -/
private lemma sl_row_exists_not_dvd {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (p : ℤ) (hp_not_unit : ¬ IsUnit p) :
    ∃ k : Fin n.succ, ¬ p ∣ N.1 r k := by
  by_contra h
  push_neg at h
  exact hp_not_unit (sl_row_primitive N r p h)

/-- **Row non-divisibility by a prime divisor of `m`.** If `p : ℕ` is a prime
dividing `m.natAbs`, then for any row `r` of `N ∈ SL_n(ℤ)` there is some column
`k` with `(p : ℤ) ∤ N.1 r k`. -/
private lemma sl_row_exists_not_dvd_of_prime {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ) (r : Fin n.succ)
    (p : ℕ) (hp : p.Prime) :
    ∃ k : Fin n.succ, ¬ (p : ℤ) ∣ N.1 r k := by
  refine sl_row_exists_not_dvd N r (p : ℤ) ?_
  intro h_unit
  have h := Int.isUnit_iff.mp h_unit
  rcases h with h | h
  · have hp1 : p = 1 := by exact_mod_cast h
    exact hp.one_lt.ne' hp1
  · have : (p : ℤ) ≥ 0 := Int.natCast_nonneg _
    have hpos : (p : ℤ) > 0 := by exact_mod_cast hp.pos
    linarith

/-- **Row Bezout coefficients for `SL_n(ℤ)`.** For any row `r` of an
`SL_n(ℤ)` matrix, there exist integer coefficients `c k` such that
`∑ k, c k * N.1 r k = 1`. Take `c k` to be the signed `(r,k)`-minor; then
the sum is exactly the Laplace expansion of `det N = 1` along row `r`. -/
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

/-- **Row clearing modulo `m`.** From `sl_row_bezout`, for any target value
`x` and modulus `m` we can find coefficients `c` with
`m ∣ x + ∑ k, c k * N.1 r k`. The construction takes `c k := -x · c₀ k`
where `c₀` are the Bezout coefficients, making the sum `-x` so that
`x + (-x) = 0` is divisible by any `m`. -/
private lemma sl_row_clear_mod {n : ℕ} (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (r : Fin n.succ) (x m : ℤ) :
    ∃ c : Fin n.succ → ℤ, m ∣ x + ∑ k, c k * N.1 r k := by
  obtain ⟨c₀, hc₀⟩ := sl_row_bezout N r
  refine ⟨fun k ↦ -x * c₀ k, ?_⟩
  have h_sum : ∑ k, (-x * c₀ k) * N.1 r k = -x := by
    have : ∑ k, (-x * c₀ k) * N.1 r k = -x * ∑ k, c₀ k * N.1 r k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [this, hc₀, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero m

/-- **Row clearing modulo `m`, avoiding column `k₀`.** When the row entries
of `N` excluding column `k₀` already generate the unit ideal (hypothesis
`h_redundant`), we can pick Bezout coefficients with `c k₀ = 0`. The proof
constructs a modified matrix-style argument by passing through any
unit-witness from the redundant entries. -/
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
    have : ∑ k, (-x * c₀ k) * N.1 r k = -x * ∑ k, c₀ k * N.1 r k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [this, hc₀_sum, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero m

/-- **SL(2)-Bezout row operation**: Given integers `a, b` not both zero, there
exists `B ∈ SL(2, ℤ)` whose `mulVec` action on `![a, b]` zeros the second
entry, leaving `Int.gcd a b` in the first entry. The explicit construction uses
Bezout coefficients `Int.gcdA`, `Int.gcdB` and the quotients `a / gcd`,
`b / gcd`. The `a ≠ 0 ∨ b ≠ 0` hypothesis rules out the degenerate zero-gcd
case where the quotient-by-gcd formula is invalid. -/
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
  · -- Compute both entries of `B.1 *ᵥ ![a, b]` via `Matrix.mulVec_cons` unfolding.
    have hentries : (!![Int.gcdA a b, Int.gcdB a b; -b', a'] *ᵥ ![a, b] : Fin 2 → ℤ) =
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
      rw [← ha', ← hb'] at step
      exact step
    ext i
    fin_cases i
    · change Int.gcdA a b * a + Int.gcdB a b * b = (Int.gcd a b : ℤ); exact h0
    · change -b' * a + a' * b = 0; exact h1

/-- **Row-embedding helper**: a `2 × 2` SL matrix `B` is lifted into
`SL(Fin (n + 3), ℤ)` acting as `B` on the first two rows/columns and as the
identity on the remaining `n + 1` rows/columns. Follows the `slSuccEmbed`
pattern using `Matrix.fromBlocks` + `submatrix` over the equivalence
`Fin (n + 3) ≃ Fin 2 ⊕ Fin (n + 1)`. -/
private noncomputable def sl2_row_embed_01 {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ) :
    SpecialLinearGroup (Fin (n + 3)) ℤ :=
  let e : Fin (n + 3) ≃ Fin 2 ⊕ Fin (n + 1) :=
    (Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  ⟨(Matrix.fromBlocks (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)).submatrix e e, by
    rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, mul_one, B.2]⟩

/-- Explicit underlying-matrix form for `sl2_row_embed_01 B`, parameterised
over the reindex equivalence `e`. -/
private lemma sl2_row_embed_01_val_eq {n : ℕ} (B : SpecialLinearGroup (Fin 2) ℤ) :
    (sl2_row_embed_01 (n := n) B).1 =
      (Matrix.fromBlocks (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)).submatrix
        ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
          finSumFinEquiv.symm)
        ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
          finSumFinEquiv.symm) := rfl

/-- For `i : Fin (n + 3)` with `i.val < 2`, the block-split equivalence sends `i`
to `Sum.inl ⟨i.val, h⟩`. -/
private lemma sl2_row_embed_01_equiv_lt_2 {n : ℕ} (i : Fin (n + 3)) (h : i.val < 2) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm) i = Sum.inl ⟨i.val, h⟩ := by
  have hcast :
      ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv) i =
        Fin.castAdd (n + 1) ⟨i.val, h⟩ := by
    ext; simp [Fin.castAdd]
  rw [Equiv.trans_apply, hcast, finSumFinEquiv_symm_apply_castAdd]

/-- For `i : Fin (n + 3)` with `2 ≤ i.val`, the block-split equivalence sends `i`
to `Sum.inr ⟨i.val - 2, _⟩`. -/
private lemma sl2_row_embed_01_equiv_ge_2 {n : ℕ} (i : Fin (n + 3)) (h : 2 ≤ i.val) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm) i = Sum.inr ⟨i.val - 2, by omega⟩ := by
  have hcast :
      ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv) i =
        Fin.natAdd 2 ⟨i.val - 2, by omega⟩ := by
    ext; simp [Fin.natAdd]; omega
  rw [Equiv.trans_apply, hcast, finSumFinEquiv_symm_apply_natAdd]

/-- Helper for entry-access of the inverse of the embedding equivalence at
`Sum.inl` indices. -/
private lemma sl2_row_embed_01_equiv_symm_inl {n : ℕ} (j : Fin 2) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm).symm (Sum.inl j) = ⟨j.val, by omega⟩ := by
  apply Fin.ext
  simp [Equiv.trans, Equiv.symm, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
    Fin.castAdd]

/-- Helper for entry-access of the inverse of the embedding equivalence at
`Sum.inr` indices. -/
private lemma sl2_row_embed_01_equiv_symm_inr {n : ℕ} (j : Fin (n + 1)) :
    ((Fin.castOrderIso (show n + 3 = 2 + (n + 1) by omega)).toEquiv.trans
      finSumFinEquiv.symm).symm (Sum.inr j) = ⟨j.val + 2, by omega⟩ := by
  apply Fin.ext
  simp [Equiv.trans, Equiv.symm, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
    Fin.natAdd]
  omega

/-- **`mulVec` action of `sl2_row_embed_01 B`**: The `SL(Fin (n+3), ℤ)` matrix
acts as `B` on the first two entries of `v` and as the identity on entries of
index `≥ 2`. -/
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
    apply congr_arg
    apply Fin.ext
    show (i.val - 2) + 2 = i.val
    omega


/-- **Bezout reduction at dim `n + 3`**: given a primitive-ready vector
`w : Fin (n + 3) → ℤ` with `w 0` or `w 1` nonzero, there exists an
`SL(Fin (n + 3), ℤ)` matrix `E` such that `E *ᵥ w` has the form
`(gcd (w 0) (w 1), 0, w 2, w 3, …, w_{n+2})` — second entry zeroed, first
entry is the gcd, and entries from index 2 onward are unchanged. This bundles
the Bezout `SL(2)` move + row embedding into the form used by the Helper A
induction step to descend to dim `n + 2`. -/
private lemma sl_bezout_reduce_dim {n : ℕ} (w : Fin (n + 3) → ℤ)
    (h_ne : w 0 ≠ 0 ∨ w 1 ≠ 0) :
    ∃ E : SpecialLinearGroup (Fin (n + 3)) ℤ,
      (E.1 *ᵥ w) 0 = (Int.gcd (w 0) (w 1) : ℤ) ∧
      (E.1 *ᵥ w) 1 = 0 ∧
      (∀ i : Fin (n + 1), (E.1 *ᵥ w) ⟨i.val + 2, by omega⟩ =
        w ⟨i.val + 2, by omega⟩) := by
  obtain ⟨B, hB⟩ := sl2_bezout_zero_out (w 0) (w 1) h_ne
  refine ⟨sl2_row_embed_01 (n := n) B, ?_, ?_, ?_⟩
  · -- (E *ᵥ w) 0 = (B *ᵥ ![w 0, w 1]) 0 = (![gcd, 0]) 0 = gcd
    rw [sl2_row_embed_01_mulVec]
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

/-- **Primitivity transfer through SL action**: if `d` divides every entry of
`M.1 *ᵥ v`, then `d` divides every entry of `v`. Follows from `M⁻¹ * M = 1`
and the fact that `M⁻¹` has integer entries. -/
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

/-- **Extension helper**: lift `M : SL(Fin (n + 2), ℤ)` to `SL(Fin (n + 3), ℤ)`
by inserting an identity row and column at index 1. Built from `slSuccEmbed M`
(which inserts identity at index 0) plus the swap permutation on 0, 1. -/
private noncomputable def sl_extend_at_1 {n : ℕ} (M : SpecialLinearGroup (Fin (n + 2)) ℤ) :
    SpecialLinearGroup (Fin (n + 3)) ℤ :=
  ⟨(slSuccEmbed M).1.submatrix (Equiv.swap (0 : Fin (n + 3)) 1) (Equiv.swap 0 1), by
    rw [det_submatrix_equiv_self]; exact (slSuccEmbed M).2⟩

/-- Entry-0 column values of `sl_extend_at_1 M`: at row 0, get `M.1 0 0`;
at row 1, get 0; at row `i+2` (for `i : Fin (n+1)`), get `M.1 (i.val + 1) 0`. -/
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
      (⟨i.val + 1, by omega⟩ : Fin (n + 2)).succ := by
    apply Fin.ext; rfl
  rw [this, show (1 : Fin (n + 3)) = (0 : Fin (n + 2)).succ from rfl,
      slSuccEmbed_val_succ_succ]

/-- **Vector/column comparison**: connects `sl_extend_at_1 N'` to a
`sl_bezout_reduce_dim` output. Given an IH-supplied `N' : SL(Fin (n+2), ℤ)`
with first column `w'` (where `w' 0 = gcd(w_ok 0, w_ok 1)` and
`w' ⟨i+1, _⟩ = w_ok ⟨i+2, _⟩`), the col-0 entry of `sl_extend_at_1 N'` at any
`i : Fin (n+3)` matches the `i`-th entry of `E.1 *ᵥ w_ok` from
`sl_bezout_reduce_dim`. -/
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
  · have hi_eq : i = 0 := Fin.ext h0
    rw [hi_eq, sl_extend_at_1_col_0_zero, hE0, hN' 0, hw'_0]
  · by_cases h1 : i.val = 1
    · have hi_eq : i = 1 := Fin.ext h1
      rw [hi_eq, sl_extend_at_1_col_0_one, hE1]
    · have h_ge : 2 ≤ i.val := by omega
      have h_lt : i.val < n + 3 := i.isLt
      let i' : Fin (n + 1) := ⟨i.val - 2, by omega⟩
      have hi_eq : i = ⟨i'.val + 2, by omega⟩ := by
        apply Fin.ext
        show i.val = i.val - 2 + 2
        omega
      rw [hi_eq, sl_extend_at_1_col_0_ge_2 N' i', hErest i',
          hN' ⟨i'.val + 1, by omega⟩, hw'_succ i']

/-- **Primitive 2-vector completion to `SL(2, ℤ)`**. Given a primitive integer
vector `w : Fin 2 → ℤ` (any common divisor is a unit), there exists
`N ∈ SL(2, ℤ)` with `N.col 0 = w`. The `Fin 2` base case of the general
primitive-column-completion helper, derived from `IsCoprime.exists_SL2_col`. -/
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
    have hunit := hw _ h_dvd
    rcases Int.isUnit_iff.mp hunit with hpos | hneg
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

/-- **Nonzero first-two-entry normalization**: a primitive vector `w` of dimension
`≥ 3` can be moved by some `T ∈ SL` so that one of the first two coordinates of
`T *ᵥ w` is nonzero. If `w 0` or `w 1` is already nonzero use `T = 1`; otherwise
primitivity yields a nonzero entry `w j` with `j ≥ 2`, and the transvection adding
row `j` into row `1` makes coordinate `1` nonzero. -/
private lemma sl_exists_transvection_first_two_ne {n : ℕ} (w : Fin (n + 3) → ℤ)
    (hw : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d) :
    ∃ T : SpecialLinearGroup (Fin (n + 3)) ℤ,
      (T.1 *ᵥ w) 0 ≠ 0 ∨ (T.1 *ᵥ w) 1 ≠ 0 := by
  have h_has_ne : ∃ j : Fin (n + 3), w j ≠ 0 := by
    by_contra h_all_zero
    push_neg at h_all_zero
    have : IsUnit (2 : ℤ) := hw 2 (fun i ↦ by rw [h_all_zero i]; exact dvd_zero _)
    rw [Int.isUnit_iff] at this; omega
  by_cases h_ne : w 0 ≠ 0 ∨ w 1 ≠ 0
  · refine ⟨1, ?_⟩
    rcases h_ne with h0 | h1
    · left; rwa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    · right; rwa [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  · push_neg at h_ne
    obtain ⟨hw0, hw1⟩ := h_ne
    obtain ⟨j, hj_ne⟩ := h_has_ne
    have hj_ge : 2 ≤ j.val := by
      by_contra hlt
      push_neg at hlt
      have h_01 : j.val = 0 ∨ j.val = 1 := by omega
      rcases h_01 with h0 | h1
      · apply hj_ne
        have : j = 0 := Fin.ext h0
        rw [this]; exact hw0
      · apply hj_ne
        have : j = 1 := Fin.ext h1
        rw [this]; exact hw1
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

/-- **Primitivity transfer to the Bezout-reduced vector**: the dimension-`n+2`
vector `w'` built from `w_ok` (with `w' 0 = gcd(w_ok 0, w_ok 1)` and
`w' ⟨i+1, _⟩ = w_ok ⟨i+2, _⟩`) is primitive whenever `w_ok` is. Any common divisor
`d` of the `w'` entries divides `gcd(w_ok 0, w_ok 1)` (hence `w_ok 0` and `w_ok 1`)
and every later entry of `w_ok`, so `d` is a unit. -/
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
    have h_d_dvd_gcd : d ∣ (Int.gcd (w_ok 0) (w_ok 1) : ℤ) := hw'_0 ▸ hd 0
    exact h_d_dvd_gcd.trans (Int.gcd_dvd_left _ _)
  · by_cases hk1 : k.val = 1
    · rw [show k = (⟨1, by omega⟩ : Fin (n + 3)) from Fin.ext hk1]
      have h_d_dvd_gcd : d ∣ (Int.gcd (w_ok 0) (w_ok 1) : ℤ) := hw'_0 ▸ hd 0
      exact h_d_dvd_gcd.trans (Int.gcd_dvd_right _ _)
    · have h_ge : 2 ≤ k.val := by omega
      have h_lt : k.val < n + 3 := k.isLt
      let k' : Fin (n + 1) := ⟨k.val - 2, by omega⟩
      rw [show k = ⟨k'.val + 2, by omega⟩ from
        Fin.ext (by show k.val = k.val - 2 + 2; omega)]
      rw [← hw'_succ k']
      exact hd ⟨k'.val + 1, by omega⟩

/-- **Primitive-column completion helper (general dim ≥ 2)**: Given a primitive
integer vector `w : Fin (n + 2) → ℤ` (any common integer divisor of all entries
is a unit), there exists `N ∈ SL(Fin (n + 2), ℤ)` whose first column equals `w`.
Proved by induction on `n`: base case via `sl_exists_col_of_primitive_fin_2`;
inductive step via `sl_bezout_reduce_dim` + `sl_extend_at_1` + degenerate-case
transvection, using `sl_dvd_of_mulVec_dvd` for primitivity transfer. -/
lemma sl_exists_col_of_primitive : ∀ {n : ℕ} (w : Fin (n + 2) → ℤ)
    (_hw : ∀ d : ℤ, (∀ i, d ∣ w i) → IsUnit d),
    ∃ N : SpecialLinearGroup (Fin (n + 2)) ℤ, ∀ i, N.1 i 0 = w i
  | 0, w, hw => sl_exists_col_of_primitive_fin_2 w hw
  | n + 1, w, hw => by
    obtain ⟨T, hT_ne⟩ := sl_exists_transvection_first_two_ne w hw
    set w_ok := T.1 *ᵥ w with hw_ok_def
    have hw_ok_prim : ∀ d : ℤ, (∀ i, d ∣ w_ok i) → IsUnit d := fun d hd ↦
      hw d (sl_dvd_of_mulVec_dvd T w d hd)
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
      sl_reduced_vector_primitive w_ok w' hw_ok_prim hw'_0 hw'_succ
    obtain ⟨N', hN'⟩ := sl_exists_col_of_primitive w' hw'_prim
    refine ⟨T⁻¹ * (E⁻¹ * sl_extend_at_1 N'), ?_⟩
    intro i
    have h_col0_eq : ∀ (j : Fin (n + 3)),
        (sl_extend_at_1 N').1 j 0 = (E.1 *ᵥ w_ok) j :=
      sl_extend_at_1_col_0_matches_reduce w_ok w' N' hN' hw'_0 hw'_succ E hE0 hE1 hErest
    have h_inv_mul_E : E⁻¹.1 * E.1 = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
    have h_inv_mul_T : T⁻¹.1 * T.1 = (1 : Matrix (Fin (n + 3)) (Fin (n + 3)) ℤ) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one]
    have h_col_inner : (sl_extend_at_1 N').1 *ᵥ (Pi.single 0 (1 : ℤ)) = E.1 *ᵥ w_ok := by
      funext k
      rw [Matrix.mulVec_single_one]
      exact h_col0_eq k
    have h_N_col0 : (T⁻¹ * (E⁻¹ * sl_extend_at_1 N')).1 *ᵥ (Pi.single 0 (1 : ℤ)) = w := by
      show (T⁻¹.1 * (E⁻¹.1 * (sl_extend_at_1 N').1)) *ᵥ (Pi.single 0 (1 : ℤ)) = w
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h_col_inner]
      have h_E_cancel : E⁻¹.1 *ᵥ (E.1 *ᵥ w_ok) = w_ok := by
        rw [Matrix.mulVec_mulVec, h_inv_mul_E, Matrix.one_mulVec]
      rw [h_E_cancel]
      show T⁻¹.1 *ᵥ w_ok = w
      rw [hw_ok_def, Matrix.mulVec_mulVec, h_inv_mul_T, Matrix.one_mulVec]
    have := congr_fun h_N_col0 i
    rw [Matrix.mulVec_single_one] at this
    exact this


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

/-- **GL-level integer-conjugate identity (T193 bridge).**
Lifts the integer-matrix identity `D_a · N_i.val = M_i.val · D_a` (as produced by
`exists_stab_with_block_form_of_X_fiber`'s `h_int_conj` output) to the GL ℚ
form `D_a_GL · mapGL N_i = mapGL M_i · D_a_GL` required by the T192 helper
`jout_conj_N_i_stab_of_iMi_c_stab`. The lift is mechanical via
`Matrix.map (algebraMap ℤ ℚ)`. -/
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
  have hcons_pos : ∀ j, 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) j := cons_one_pos ha
  apply Units.ext
  show ((diagMat (k + 2) (Fin.cons 1 a) * (mapGL ℚ N_i : GL _ ℚ)).val :
        Matrix (Fin (k + 2)) (Fin (k + 2)) ℚ) =
      ((mapGL ℚ M_i : GL _ ℚ) * diagMat (k + 2) (Fin.cons 1 a)).val
  simp only [Units.val_mul]
  have h_Da : ((diagMat (k + 2) (Fin.cons 1 a) : GL _ ℚ).val : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 a : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_pos,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_N : ((mapGL ℚ N_i : GL _ ℚ).val : Matrix _ _ ℚ) =
      N_i.val.map (algebraMap ℤ ℚ) := rfl
  have h_M : ((mapGL ℚ M_i : GL _ ℚ).val : Matrix _ _ ℚ) =
      M_i.val.map (algebraMap ℤ ℚ) := rfl
  rw [h_Da, h_N, h_M]
  rw [← Matrix.map_mul, ← Matrix.map_mul]
  exact congr_arg (fun M : Matrix _ _ ℤ ↦ M.map (algebraMap ℤ ℚ)) h_int_conj

/-- **GL-level fiber equation from the fiber condition (T193 bridge).**
GL ℚ form of `hfib_int_mat_eq`: directly produces
`i.out · D_a · j.out · D_b = D_c · mapGL ν` in `GL (Fin (k+2)) ℚ`, the input
required by the T192 helper `jout_conj_N_i_stab_of_iMi_c_stab`. -/
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
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  obtain ⟨ν, hν⟩ := hfib_to_mem_H a b c ha hb hc i j hfib
  refine ⟨ν, ?_⟩
  have h_eq : diagMat (k + 2) (Fin.cons 1 c) *
      (mapGL ℚ ν : GL (Fin (k + 2)) ℚ) =
      (i.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) *
          (j.out : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 b) := by
    rw [hν]; group
  exact h_eq.symm

/-- **Integer matrix equation from the fiber condition**. The H-membership from
`hfib_to_mem_H` is witnessed by some `ν : SL_{k+2}(ℤ)`; because every factor on
both sides is the `Int.cast` image of an integer matrix, the equation descends
to the integer level:
`A · D_a · B · D_b = D_c · ν`, where `A := toSL i.out`, `B := toSL j.out` and
`D_x := Matrix.diagonal (Fin.cons 1 x)` (entries cast to `ℤ`). This is the
clean integer handle used by the divisibility extraction lemmas. -/
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
  have hcons_a := cons_one_pos ha
  have hcons_b := cons_one_pos hb
  have hcons_c := cons_one_pos hc
  have h_mem := hfib_to_mem_H a b c ha hb hc i j hfib
  obtain ⟨ν, hν⟩ := h_mem
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
    rw [diagMat_val (k + 2) _ hcons_a,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_Db : ((diagMat (k + 2) (Fin.cons 1 b) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 b : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_b,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  have h_Dc : ((diagMat (k + 2) (Fin.cons 1 c) : GL _ ℚ) : Matrix _ _ ℚ) =
      (Matrix.diagonal (fun r : Fin (k + 2) ↦
        (((Fin.cons 1 c : Fin (k + 2) → ℕ) r : ℕ) : ℤ))).map (algebraMap ℤ ℚ) := by
    rw [diagMat_val (k + 2) _ hcons_c,
        Matrix.diagonal_map (map_zero (algebraMap ℤ ℚ))]
    congr 1
  rw [h_i, h_j, h_ν, h_Da, h_Db, h_Dc] at hmat
  rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul] at hmat
  exact (Matrix.map_injective (algebraMap ℤ ℚ).injective_int hmat).symm

/-- **Adjugate rearrangement of a determinant-one matrix equation.** From
`A * Da * B * Db = Dc * ν` with `det A = det ν = 1`, premultiplying by
`adjugate A` (which left-inverts `A`) and postmultiplying by `adjugate ν`
(which right-inverts `ν`) yields `Da * B * Db * adjugate ν = adjugate A * Dc`. -/
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

/-- **Diagonal-scaling divisibility on a column-zero entry.** If
`diagonal da * R = Adj * diagonal dc` with `dc 0 = 1`, then `da s ∣ Adj s 0`
for every `s`. Applying both sides to `e₀`: the right side reads off column `0`
of `Adj` (since `dc 0 = 1`), while the left side scales the `s`-entry by `da s`. -/
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
`((toSL i.out)⁻¹).1 r.succ 0` is divisible by `a r` for every `r : Fin (k+1)`.
Proof strategy: premultiply the equation by `adjugate A` and postmultiply by
`adjugate ν`, apply to `Pi.single 0 (1 : ℤ)` via `mulVec`, and read off the
diagonal entry. -/
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
  have hdetA : A_i.det = 1 := (toSL i.out).2
  have hdetν : ν.1.det = 1 := ν.2
  have h_rearr : D_a * A_j * D_b * Matrix.adjugate ν.1 =
      Matrix.adjugate A_i * D_c :=
    adjugate_rearrange_of_matrix_eq A_i A_j D_a D_b D_c ν.1 hdetA hdetν hν
  intro r
  rw [show ((toSL i.out)⁻¹ : SpecialLinearGroup (Fin (k + 2)) ℤ).1 r.succ 0
        = Matrix.adjugate A_i r.succ 0 by rw [SpecialLinearGroup.coe_inv],
    show (a r : ℤ) = (((Fin.cons 1 a : Fin (k + 2) → ℕ) r.succ : ℕ) : ℤ) by rw [Fin.cons_succ]]
  refine diagonal_dvd_adjugate_entry
    (fun s ↦ (((Fin.cons 1 a : Fin (k + 2) → ℕ) s : ℕ) : ℤ))
    (fun s ↦ (((Fin.cons 1 c : Fin (k + 2) → ℕ) s : ℕ) : ℤ))
    (A_j * D_b * Matrix.adjugate ν.1) (Matrix.adjugate A_i) r.succ (by simp [Fin.cons_zero]) ?_
  rw [← hD_a, ← hD_c, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  exact h_rearr

/-- **Row-zero divisibility for `ν` (T001 Layer 1 precursor).** From the integer
matrix equation `A_i · D_a · A_j · D_b = D_c · ν` (`hfib_int_mat_eq`), the
entry `ν_{0, r.succ}` is divisible by `b r` for every `r : Fin (k+1)`.

**Derivation.** Look at row 0, column `r.succ` of both sides. With `(D_c)_{0, 0}
= 1` and `(D_b)_{r.succ, r.succ} = b r`, row 0 col `r.succ` of `D_c · ν` equals
`ν_{0, r.succ}`, while row 0 col `r.succ` of `A_i · D_a · A_j · D_b` carries an
explicit `b r` factor (the right-multiplication by `D_b` scales col `r.succ`
by `b r`).

**Use site (T001 Layer 1 reduction).** This is the single direct divisibility
constraint extracted from the fiber equation that survives the structural
asymmetry obstruction documented at `hfib_col_div_b_canonical_stmt`.  It is
strictly weaker than `hfib_col_div_b_canonical_stmt` (which asks for
divisibility on `(toSL j.out)⁻¹` = `adj A_j`), but is provable in Lean and
isolates the next step needed: a lattice-descent / cofactor argument bridging
`b r ∣ ν_{0, r.succ}` to `b r ∣ adj(A_j)_{r.succ, 0}` via the SL determinant
constraint on `ν` and the structure of the equation. -/
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
Specialised entry formula: at column `j`, the new entry is the original `(a, j)`
plus `c` times the original `(a, i)`. This is the unbundled form used by the
column-by-column Bezout reduction. -/
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

/-- **Multi-transvection column accumulation (Finset version).** Iterating a
family of transvections `slTransvecG k k₀ (h_ne k) (c k)` over `k ∈ S` (where
`S` avoids `k₀`) right-multiplies `N` by some `U ∈ SL` whose net effect adds
`∑ k ∈ S, c k * (column k)` to column `k₀` and leaves all columns `k ≠ k₀`
unchanged. Crucially, the donor columns `k ∈ S` are not modified during the
process (each transvection touches only column `k₀`), so the cumulative sum is
the original sum, not a telescoped one. -/
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
      have hk_ne_k₀ : k ≠ k₀ := by
        intro h; apply hS; rw [h]; exact Finset.mem_insert_self _ _
      have hT_no_k₀ : k₀ ∉ T :=
        fun h ↦ hS (Finset.mem_insert_of_mem h)
      obtain ⟨U, hU_pres, hU_target⟩ := ih hT_no_k₀
      refine ⟨U * slTransvecG k k₀ hk_ne_k₀ (c k), ?_, ?_⟩
      · intro a k' hk'
        rw [← mul_assoc, sl_addCol_preserves_col k k₀ hk_ne_k₀ (c k) (N * U) a hk']
        exact hU_pres a k' hk'
      · intro a
        rw [← mul_assoc, sl_addCol_target_col k k₀ hk_ne_k₀ (c k) (N * U) a]
        rw [hU_target a, hU_pres a k hk_ne_k₀]
        rw [Finset.sum_insert hkT]
        ring

/-- **Multi-transvection column accumulation, full sum form.** Specialisation
of `sl_addCol_finset_target_aux` to `S = Finset.univ.erase k₀`: when the
coefficient at the target column `c k₀ = 0`, the cumulative effect is the
full sum `∑ k, c k * N.1 a k` (since the `k = k₀` term contributes zero). -/
private lemma sl_addCol_finset_target {n : ℕ}
    (N : SpecialLinearGroup (Fin n.succ) ℤ)
    (k₀ : Fin n.succ) (c : Fin n.succ → ℤ) (h_zero : c k₀ = 0) :
    ∃ U : SpecialLinearGroup (Fin n.succ) ℤ,
      (∀ a (k : Fin n.succ), k ≠ k₀ → (N * U).1 a k = N.1 a k) ∧
      (∀ a, (N * U).1 a k₀ = N.1 a k₀ + ∑ k, c k * N.1 a k) := by
  have hS : k₀ ∉ Finset.univ.erase k₀ := Finset.notMem_erase _ _
  obtain ⟨U, hU_pres, hU_target⟩ :=
    sl_addCol_finset_target_aux N k₀ c (Finset.univ.erase k₀) hS
  refine ⟨U, hU_pres, ?_⟩
  intro a
  rw [hU_target a]
  congr 1
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k₀)]
  rw [h_zero, zero_mul, add_zero]

/-- **One-row modular clearance.** If the row-`r` entries of `N`, with column
`k₀` excluded, already generate the unit ideal (`h_redundant`), then for any
modulus `m` there is a single SL elementary product `U` (composition of
transvections with donors `k ≠ k₀`) such that `m ∣ (N * U).1 r k₀` and all
columns `k ≠ k₀` are preserved. Combines `sl_row_clear_mod_avoiding`
(produces Bezout coefficients `c` with `c k₀ = 0` and
`m ∣ N.1 r k₀ + ∑ c k * N.1 r k`) with `sl_addCol_finset_target` (realises
the cumulative column-effect as a product of transvections). -/
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

/-- **Bezout column reduction**: given a matrix `M` and two distinct columns
`i ≠ j`, with `M_{r, i}` non-zero (or jointly with `M_{r, j}`), there exists
a determinant-1 elementary column operation (right-multiplication by an SL
transvection) modifying only column `j` so that the entry `M_{r, j}` is
reduced modulo `M_{r, i}`. Concretely: choose `c = -(M_{r, j} / M_{r, i})`,
giving new `(r, j)`-entry equal to `M_{r, j} % M_{r, i}` (the Euclidean
remainder). All other columns are unchanged.

This is the primitive column-op step used in the column-by-column Smith
reduction toward the DivChain stabilizer form. -/
private lemma sl_addCol_emod_step {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    (M : SpecialLinearGroup (Fin m) ℤ) (r : Fin m) :
    ∃ U : SpecialLinearGroup (Fin m) ℤ,
      (∀ a (k : Fin m), k ≠ j → (M * U).1 a k = M.1 a k) ∧
      (M * U).1 r j = M.1 r j % M.1 r i := by
  refine ⟨slTransvecG i j hij (-(M.1 r j / M.1 r i)), ?_, ?_⟩
  · intro a k hk
    exact sl_addCol_preserves_col i j hij _ M a hk
  · rw [sl_addCol_target_col i j hij _ M r]
    have := Int.emod_def (M.1 r j) (M.1 r i)
    linarith [this]

/-- **Shift-invariance of the column-target divisibility.** If `d` divides the
target entry `e + c₀ * p` for one coefficient `c₀`, and `d` divides the shift
`c - c₀`, then `d` divides the target entry for the coefficient `c`. This is the
core step shared by the simultaneous two-row column reductions: a transvection
coefficient may be replaced by any other in the same residue class mod `d`. -/
private lemma dvd_entry_add_mul_of_shift {d e c c₀ p : ℤ}
    (h₀ : d ∣ e + c₀ * p) (hshift : d ∣ c - c₀) : d ∣ e + c * p := by
  have : e + c * p = (e + c₀ * p) + (c - c₀) * p := by ring
  rw [this]
  exact dvd_add h₀ (hshift.mul_right p)

/-- **Bezout column reduction making `d` divide the entry**: given a matrix
`M`, two distinct columns `i ≠ j`, a row `r`, and a divisor `d`, if the pivot
`M.1 r i` is coprime to `d`, there is an SL transvection adding a multiple of
column `i` to column `j` so that `d ∣ (M * U).1 r j`. All columns `k ≠ j` are
preserved. -/
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

/-- **Two-row simultaneous Bezout column reduction (CRT case)**: given a
matrix `M`, two distinct columns `i ≠ j`, two distinct rows `r₁ ≠ r₂`, and two
divisors `d₁, d₂` with `IsCoprime d₁ d₂`, if the pivot entries `M.1 r₁ i` and
`M.1 r₂ i` are coprime to their respective divisors, there is a single SL
transvection adding a multiple of column `i` to column `j` so that
`d₁ ∣ (M * U).1 r₁ j` AND `d₂ ∣ (M * U).1 r₂ j`. All columns `k ≠ j` are
preserved.

The construction is an explicit CRT lift of the per-row Bezout coefficients:
from `s₁·M.1 r₁ i + t₁·d₁ = 1` and `s₂·M.1 r₂ i + t₂·d₂ = 1` and
`u·d₁ + v·d₂ = 1`, set `c₁ := -M.1 r₁ j · s₁`, `c₂ := -M.1 r₂ j · s₂`, and
`c := v·d₂·c₁ + u·d₁·c₂`. Then `c ≡ c₁ [MOD d₁]` and `c ≡ c₂ [MOD d₂]`,
solving both congruences simultaneously. -/
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
  · -- Show d₁ ∣ M.1 r₁ j + c * M.1 r₁ i.
    rw [sl_addCol_target_col i j hij _ M r₁]
    have hvd₂ : v * d₂ = 1 - u * d₁ := by linarith [huv]
    have key : M.1 r₁ j * (s₁ * M.1 r₁ i + t₁ * d₁) = M.1 r₁ j * 1 := by rw [hst₁]
    have hfirst : d₁ ∣ M.1 r₁ j + c₁ * M.1 r₁ i :=
      ⟨M.1 r₁ j * t₁, by rw [hc₁_def]; linarith [key]⟩
    have hshift : d₁ ∣ c - c₁ := ⟨u * c₂ - u * c₁, by
      rw [hc_def, show v * d₂ * c₁ + u * d₁ * c₂ - c₁ =
        (v * d₂ - 1) * c₁ + u * d₁ * c₂ from by ring, hvd₂]; ring⟩
    exact dvd_entry_add_mul_of_shift hfirst hshift
  · -- Symmetric argument with d₂.
    rw [sl_addCol_target_col i j hij _ M r₂]
    have hud₁ : u * d₁ = 1 - v * d₂ := by linarith [huv]
    have key : M.1 r₂ j * (s₂ * M.1 r₂ i + t₂ * d₂) = M.1 r₂ j * 1 := by rw [hst₂]
    have hfirst : d₂ ∣ M.1 r₂ j + c₂ * M.1 r₂ i :=
      ⟨M.1 r₂ j * t₂, by rw [hc₂_def]; linarith [key]⟩
    have hshift : d₂ ∣ c - c₂ := ⟨v * c₁ - v * c₂, by
      rw [hc_def, show v * d₂ * c₁ + u * d₁ * c₂ - c₂ =
        v * d₂ * c₁ + (u * d₁ - 1) * c₂ from by ring, hud₁]; ring⟩
    exact dvd_entry_add_mul_of_shift hfirst hshift

/-- **Two-row simultaneous Bezout column reduction (CRT compatibility case)**:
NOT requiring pairwise-coprime divisors. Given pre-supplied per-row Bezout
residues `c₁, c₂` with `d₁ ∣ M.1 r₁ j + c₁ * M.1 r₁ i` and
`d₂ ∣ M.1 r₂ j + c₂ * M.1 r₂ i`, plus the CRT compatibility
`(Int.gcd d₁ d₂ : ℤ) ∣ c₁ - c₂`, there is an SL transvection adding a multiple
of column `i` to column `j` so that simultaneously
`d₁ ∣ (M * U).1 r₁ j` and `d₂ ∣ (M * U).1 r₂ j`. All columns `k ≠ j` are
preserved.

The construction takes the unified coefficient `c := c₁ - u * d₁ * δ` where
`u := Int.gcdA d₁ d₂`, `v := Int.gcdB d₁ d₂`, `g := (Int.gcd d₁ d₂ : ℤ)`, and
`δ` is the witness `c₁ - c₂ = g * δ`. Then
`c - c₁ = -u * d₁ * δ` (divisible by `d₁`) and `c - c₂ = v * d₂ * δ`
(divisible by `d₂`), giving the simultaneous solution.

This generalises `sl_addCol_make_dvd_two_coprime`: when `IsCoprime d₁ d₂`, the
gcd is a unit so the compatibility hypothesis is trivial. The natural use case
is a divisibility-chain `d₁ ∣ d₂` (then `Int.gcd d₁ d₂ = |d₁|` divides any
multiple, in particular `c₁ - c₂` whenever the system is consistent). -/
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
  · -- Show d₁ ∣ M.1 r₁ j + c * M.1 r₁ i.
    rw [sl_addCol_target_col i j hij _ M r₁]
    exact dvd_entry_add_mul_of_shift h₁ ⟨-(u * δ), by rw [hc_def]; ring⟩
  · -- Show d₂ ∣ M.1 r₂ j + c * M.1 r₂ i.
    rw [sl_addCol_target_col i j hij _ M r₂]
    refine dvd_entry_add_mul_of_shift h₂ ⟨v * δ, ?_⟩
    have hkey : c - c₂ = (c₁ - c₂) - u * d₁ * δ := by rw [hc_def]; ring
    rw [hkey, hδ, hbezout]; ring

/-- **Bezout target identity for the running-product coefficient.** With the
coprimality witness `s·(D·p) + t·q = 1`, the transvection coefficient
`c' = D·(-e·s)` solves the column-target congruence exactly: `e + c'·p = q·(e·t)`,
so `q ∣ e + c'·p`. This is the inserted-row algebra of the finite-row CRT
induction (`p` is the pivot, `e` the current `j`-entry, `q` the divisor). -/
private lemma entry_add_prod_coeff_eq {D s t p q e : ℤ}
    (hst : s * (D * p) + t * q = 1) :
    e + D * (-e * s) * p = q * (e * t) := by
  have key : e * (s * (D * p) + t * q) = e * 1 := by rw [hst]
  linarith [key]

/-- **Inductive step of the finite-row CRT column reduction.** Given a reduction
`U_R` already solving the divisibilities over `R` (and preserving columns `≠ j`),
adjoin the transvection with coefficient `c' = D · v`, `D = ∏_{r ∈ R} d r`,
`v = -((M·U_R) r₀ j)·s`. Multiplying by `D` keeps every previous divisibility
(`d r ∣ D` for `r ∈ R`), while the Bezout coefficient `s` (from coprimality of
`D·(M r₀ i)` with `d r₀`) lands the inserted row `r₀`. -/
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
    have hr_ne : r₀ ≠ r := fun h ↦ hr₀ (h ▸ hr)
    exact h_pairwise r₀ (Finset.mem_insert_self _ _) r
      (Finset.mem_insert_of_mem hr) hr_ne
  have h_cop_r₀ : IsCoprime (M.1 r₀ i) (d r₀) := h_cop r₀ (Finset.mem_insert_self _ _)
  obtain ⟨s, t, hst⟩ := h_cop_prod.mul_left h_cop_r₀
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

/-- **Finite-row simultaneous Bezout column reduction (CRT wrapper)**: given a
matrix `M`, two distinct columns `i ≠ j`, a finite set of rows `R` with a
divisor `d r` for each `r ∈ R` such that the pivots `M.1 r i` are coprime to
`d r` and the divisors are pairwise coprime, there is a single SL matrix
(product of transvections in column `j`, leaving every column `k ≠ j`
unchanged) so that `d r ∣ (M * U).1 r j` for every `r ∈ R`.

The proof is by induction on `R`, dispatching the inductive step to
`sl_addCol_make_dvd_finset_insert_step`. -/
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

/-- **Common-residue finite-row CRT wrapper.** When a SINGLE coefficient `c`
already simultaneously solves the divisibility `d r ∣ M.1 r j + c * M.1 r i`
for every row `r ∈ R`, a single transvection `slTransvecG i j hij c` suffices
to land all rows. This is the trivial pre-aligned case, useful when the
caller has already produced a common Bezout coefficient. -/
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

/-- **Chain-compatible finite-row CRT wrapper.** Given per-row residues `c r`
solving `d r ∣ M.1 r j + c r * M.1 r i`, plus a "top element" `r_top ∈ R`
whose modulus `d r_top` is divisible by every `d r` (`r ∈ R`), and a chain
compatibility `d r ∣ c r_top - c r` for all `r ∈ R`, a single transvection
with coefficient `c r_top` lands all rows simultaneously. The compatibility
hypothesis is the precise content of "the per-row residues agree mod the
smaller moduli of the chain". -/
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
  have h_diff : d r ∣ (c r_top - c r) * M.1 r i :=
    Dvd.dvd.mul_right (h_chain r hr) _
  have h_sum : d r ∣ (M.1 r j + c r * M.1 r i) + (c r_top - c r) * M.1 r i :=
    dvd_add (h_dvd r hr) h_diff
  have h_eq :
      (M.1 r j + c r * M.1 r i) + (c r_top - c r) * M.1 r i
        = M.1 r j + c r_top * M.1 r i := by ring
  rw [h_eq] at h_sum
  exact h_sum

/-- **Lower-clearance reduction.** If we already have an `N ∈ SL_{k+2}(ℤ)` with
the desired first column `w` and whose strictly-lower-triangular entries
`N i.succ j.succ` (for `j < i`) satisfy the `a i / a j` divisibility, then `N`
already lies in the diag-conjugation stabilizer. This packages the entry-wise
divisibility check via `diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd`. -/
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
  · -- i = 0: LHS = 1
    simp
  · intro i'
    refine Fin.cases ?_ ?_ j
    · -- j = 0, i = i'.succ
      simp only [Fin.cons_succ, Fin.cons_zero, Nat.cast_one, mul_one]
      have hcol_i := hcol i'.succ
      rw [hcol_i]
      exact hw_col_div i'
    · intro j'
      simp only [Fin.cons_succ]
      by_cases hij : j' < i'
      · -- Use h_lower i' j' hij
        have hdvd_q : ((a i' / a j' : ℕ) : ℤ) ∣ N.1 i'.succ j'.succ :=
          h_lower i' j' hij
        have hji_le : j' ≤ i' := le_of_lt hij
        have ha_dvd : a j' ∣ a i' := divChain_dvd (n := k + 1) hda hji_le
        have hmul : (((a i' / a j' : ℕ) : ℤ) * (a j' : ℤ)) ∣
            N.1 i'.succ j'.succ * (a j' : ℤ) :=
          mul_dvd_mul_right hdvd_q _
        have hcancel : (a i' / a j') * a j' = a i' :=
          Nat.div_mul_cancel ha_dvd
        have hcancel_int : ((a i' / a j' : ℕ) : ℤ) * (a j' : ℤ) = (a i' : ℤ) := by
          have := congr_arg (fun n : ℕ ↦ (n : ℤ)) hcancel
          push_cast at this
          exact this
        rw [hcancel_int] at hmul
        exact hmul
      · -- ¬ j' < i', i.e. i' ≤ j'.  Then a i' ∣ a j' by divChain.
        push_neg at hij
        have ha_dvd : a i' ∣ a j' := divChain_dvd (n := k + 1) hda hij
        have ha_dvd_int : (a i' : ℤ) ∣ (a j' : ℤ) := by exact_mod_cast ha_dvd
        exact Dvd.dvd.mul_left ha_dvd_int _

/-- **Donor-coprime + residue-aligned column clearance.** This is the precise
reduction of "clear column `j.succ` below row `j+1` against the DivChain
moduli `(a i / a j)` using donor column `i_don ≠ j.succ`" to the existence
of a SINGLE Bezout coefficient `c` that simultaneously aligns all the lower
rows. It is `sl_addCol_make_dvd_common` specialised to the row set
`{i.succ : i > j}` and the DivChain modulus pattern. The donor-coprime
hypothesis `h_don_ne` is consumed only to invoke the underlying transvection.
The caller is responsible for producing `c` and the joint residue
hypothesis `h_clear` (typically via Smith-style reduction or row-by-row
Bezout combined with chain compatibility). -/
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

/-- **Compatible-residues wrapper** for column clearance. Packages the
solvability hypothesis as an existential, hiding the explicit Bezout
coefficient `c` from the caller. One-line reduction to
`sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue`. -/
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

/-- **Pure-arithmetic CRT compatibility for chain moduli.** For a tower of
moduli `d : Fin n → ℤ` totally ordered by divisibility (`i ≤ j → d i ∣ d j`)
and per-row data `b, m : Fin n → ℤ`, the existence of a single coefficient
`c` simultaneously satisfying `d i ∣ c * m i + b i` for all rows `i` is
equivalent to the existence of per-row coefficients `c_per i` satisfying
each row, together with the chain compatibility `d i ∣ c_per j - c_per i`
whenever `i ≤ j`. The forward direction uses `c_per i := c` (and chain
compatibility is then trivial). The backward direction takes
`c := c_per ⟨n-1, _⟩` (or `0` when `n = 0`); the difference
`(c - c_per i) * m i` is divisible by `d i` exactly because of the chain
compatibility hypothesis. -/
private lemma exists_chain_solution_iff_compatible
    {n : ℕ} (d : Fin n → ℤ) (_h_chain : ∀ i j : Fin n, i ≤ j → d i ∣ d j)
    (b m : Fin n → ℤ) :
    (∃ c : ℤ, ∀ i : Fin n, d i ∣ c * m i + b i) ↔
      (∃ c_per : Fin n → ℤ,
        (∀ i : Fin n, d i ∣ c_per i * m i + b i) ∧
        (∀ i j : Fin n, i ≤ j → d i ∣ c_per j - c_per i)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨c, hc⟩
    refine ⟨fun _ ↦ c, hc, ?_⟩
    intro i j _hij
    simp
  · rintro ⟨c_per, h_row, h_compat⟩
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · -- vacuous: no rows
      refine ⟨0, ?_⟩
      intro i
      exact absurd i.isLt (by simp [hn0])
    · -- take c := c_per (last)
      set last : Fin n := ⟨n - 1, by omega⟩
      refine ⟨c_per last, ?_⟩
      intro i
      have hi_le : i ≤ last := by
        refine Fin.mk_le_of_le_val ?_
        have : i.val ≤ n - 1 := by have := i.isLt; omega
        simpa using this
      have hcompat : d i ∣ c_per last - c_per i := h_compat i last hi_le
      have hdvd_diff : d i ∣ (c_per last - c_per i) * m i := hcompat.mul_right _
      have hsum := (h_row i).add hdvd_diff
      have heq : c_per i * m i + b i + (c_per last - c_per i) * m i =
          c_per last * m i + b i := by ring
      rw [heq] at hsum
      exact hsum

/-- **Chain-residues wrapper** for column clearance. Given per-row Bezout
coefficients `c i` and a chain-compatibility hypothesis (the residues
`c i'` and `c i` agree modulo `(a i / a j)` whenever `i ≤ i'`), we can
collapse to a single coefficient `c (Fin.last k)` that simultaneously
clears all rows. The chain compatibility is exactly the divisibility
needed to absorb the difference `(c (Fin.last) - c i) * N.1 i.succ i_don`
into the modulus. -/
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
  have hrow := h_per_row i hi_lt
  have hcompat := h_chain_compat i (Fin.last k) hi_lt (Fin.le_last _)
  have hdiff : (((a i / a j : ℕ) : ℤ)) ∣
      (c (Fin.last k) - c i) * N.1 i.succ i_don :=
    hcompat.mul_right _
  have hsum := hrow.add hdiff
  have heq : N.1 i.succ j.succ + c i * N.1 i.succ i_don +
      (c (Fin.last k) - c i) * N.1 i.succ i_don =
      N.1 i.succ j.succ + c (Fin.last k) * N.1 i.succ i_don := by ring
  rw [heq] at hsum
  exact hsum

/-- **One-column induction step (first nonzero-donor completion).**

Given an `SL` matrix `N` with first column `w` and previously-cleared
columns `1, …, j` (lower-triangular `DivChain` divisibilities at each
column `j' ≤ j`, restricted to rows below the diagonal), together with
a donor column `i_don` distinct from the target column `j.succ` and
chain-compatible per-row residue data `c` for the target column,
produce `N'` with the same first column and with cleared columns
`1, …, j.succ`.

The proof composes `N` with the elementary clearance unit
`U` from `sl_clear_one_column_lower_divChain_of_chain_residues`.
Since `U` only modifies column `j.succ`, all columns `j'.succ` with
`j' ≤ j` are preserved (including column 0): for `j' < j` use
`(j'.succ ≠ j.succ)` from `Fin.succ_inj`, and for `j' = j` we
get the new clearance directly from the chain-residues output. -/
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
  · -- Column 0 is preserved by U (0 ≠ j.succ).
    intro i
    have h0_ne : (0 : Fin (k + 2)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    have := hU_pres i 0 h0_ne
    rw [this]
    exact hcol i
  · intro i j' hj'_le_j hj'_lt_i
    rcases lt_or_eq_of_le hj'_le_j with hlt | heq
    · -- j' < j: column j'.succ preserved by U, divisibility from h_prev.
      have hne : j'.succ ≠ j.succ := by
        intro h
        exact (ne_of_lt hlt) (Fin.succ_inj.mp h)
      have hpres := hU_pres i.succ j'.succ hne
      rw [hpres]
      exact h_prev i j' hlt hj'_lt_i
    · -- j' = j: new clearance from chain-residues output.
      subst heq
      exact hU_clear i hj'_lt_i

/- **Strengthened completion invariant (signature only — not yet proved).**

For the next stint, we will need a stronger one-column step that *also*
preserves a chosen donor column `i_don'` for the *next* target column
`j.succ.succ`. The strengthened statement would read roughly:

```
∃ N' : SpecialLinearGroup (Fin (k + 2)) ℤ,
  (∀ i, N'.1 i 0 = w i) ∧
  (∀ i j' : Fin (k + 1), j' ≤ j → j' < i →
    (((a i / a j' : ℕ) : ℤ) ∣ N'.1 i.succ j'.succ)) ∧
  (∀ i, N'.1 i i_don' = N.1 i i_don')
```

i.e. the output also leaves column `i_don'` untouched, so that the next
induction step can reuse `i_don'` as its own donor. Since the
underlying clearance `U` only modifies column `j.succ`, this is true
whenever `i_don' ≠ j.succ`. The corresponding lemma
`sl_exists_col_with_chain_compat_donor` would then iterate this
preservation across the whole chain `j = 0, 1, …, k`, threading a
fixed donor column (or a small family of donors) through every step.

We do not land it in this file; the present `sl_clear_one_column_step`
is sufficient to drive the induction once a donor-selection lemma is
available. -/

/-- **Full lower-clearance induction under explicit donor-supply hypothesis.**

Assuming a donor-supply oracle `h_supply` that, for any column `j : Fin (k+1)`
and any partially-cleared `SL` matrix `N` (matching `w` on column 0 and
satisfying lower DivChain divisibilities for columns `j' < j`), produces a
donor index `i_don ≠ j.succ` and chain-compatible per-row residues `c`
sufficient for `sl_clear_one_column_step`, iterate that step across columns
`j = 0, 1, …, k` to obtain a single matrix `N` with first column `w` and
the full lower DivChain clearance.

Proof: induct on `j_max : ℕ` ranging over `0, …, k+1`, producing partial
clearance `j'.val < j_max → j' < i → … ∣ …`. The inductive step at
`j_max < k+1` invokes `h_supply` with `j := ⟨j_max, _⟩` to obtain donor and
residues, then applies `sl_clear_one_column_step`. The conclusion at
`j_max = k+1` is the full lower clearance. -/
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
    have hj_max_lt : j_max < k + 1 := Nat.lt_of_succ_le hj_max_le
    obtain ⟨N, hcolN, hclear_prev⟩ := ih (Nat.le_of_succ_le hj_max_le)
    set j : Fin (k + 1) := ⟨j_max, hj_max_lt⟩ with hj_def
    have h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ) := by
      intro i j' hj'_lt_j hj'_lt_i
      have : j'.val < j_max := hj'_lt_j
      exact hclear_prev i j' this hj'_lt_i
    obtain ⟨i_don, h_don_ne, c, h_per_row, h_chain_compat⟩ :=
      h_supply j N hcolN h_prev
    obtain ⟨N', hcolN', hclear_new⟩ :=
      sl_clear_one_column_step a ha hda w j N hcolN h_prev
        i_don h_don_ne c h_per_row h_chain_compat
    refine ⟨N', hcolN', ?_⟩
    intro i j' hj'_lt_succ hj'_lt_i
    have hj'_le_j : j' ≤ j := by
      show j'.val ≤ j.val
      exact Nat.lt_succ_iff.mp hj'_lt_succ
    exact hclear_new i j' hj'_le_j hj'_lt_i

/-- **Conditional consumer.** Bridges `sl_exists_col_of_primitive`,
`sl_clear_all_columns_of_donor_supply`, and
`sl_exists_col_stab_divChain_of_lower_clearance` into one statement: under an
explicit donor-supply oracle (parameterized in the same `(j, N, hcol, h_prev)`
shape as `sl_clear_all_columns_of_donor_supply`), there exists `N` with first
column `w` whose diagonal-conjugate lies in the `GL_pair (k + 2)` stabilizer.

Note (redundancy): superseded by `sl_exists_col_stab_divChain_of_multi_donor_supply`
below, which exposes the more general multi-donor (`c : Fin (k+2) → ℤ`) oracle
shape. The single-donor variant remains available for callers that already
package their column-clearing data in `(i_don, c i)` form. -/
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

/-- **Common-`c` reduction.** When the donor-supply oracle can be satisfied
with a single common Bezout coefficient `c0` at each column, the chain
compatibility condition is automatic: take `c i := c0` for all `i`, so
`c i' - c i = 0` is divisible by anything. -/
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
  refine ⟨i_don, h_don_ne, fun _ ↦ c0, h_clear, ?_⟩
  intro _ _ _ _
  simp

/-- **Common-`c` bridge.** Specializes `sl_exists_col_stab_divChain_of_donor_supply`
to the case where the donor-supply oracle returns a single common Bezout
coefficient `c0` per column, deferring the chain-compatibility step to
`h_supply_of_common_c`. -/
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

/-- **Conditional multi-row, multi-donor column-clearance.** Given a residue
function `c : Fin (k+2) → ℤ` with `c j.succ = 0` and per-row joint divisibility
`(a i / a j) ∣ N i.succ j.succ + ∑ k', c k' * N i.succ k'` for all `i > j`,
realise the cumulative column-effect as a single SL elementary product `U`,
yielding `(N * U)` whose column `j.succ` is now divisible by `(a i / a j)` on
every row `i.succ` with `j < i`, and whose other columns are preserved. This
is the multi-donor analogue of
`sl_clear_one_column_lower_divChain_of_donor_coprime_and_residue`. -/
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

/-- **One-column induction-step wrapper, multi-donor variant.** Mirrors
`sl_clear_one_column_step` but consumes a single residue function `c` (a
combination of all columns) instead of a fixed donor column with chain
compatibility. -/
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
    have h0_ne : (0 : Fin (k + 2)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    have := hU_pres i 0 h0_ne
    rw [this]
    exact hcol i
  · intro i j' hj'_le_j hj'_lt_i
    rcases lt_or_eq_of_le hj'_le_j with hlt | heq
    · have hne : j'.succ ≠ j.succ := by
        intro h
        exact (ne_of_lt hlt) (Fin.succ_inj.mp h)
      have hpres := hU_pres i.succ j'.succ hne
      rw [hpres]
      exact h_prev i j' hlt hj'_lt_i
    · subst heq
      exact hU_clear i hj'_lt_i

/-- **Full lower-clearance induction under multi-donor supply oracle.** The
multi-donor analogue of `sl_clear_all_columns_of_donor_supply`. Iterates
`sl_clear_one_column_step_multi_donor` across columns `j = 0, 1, …, k`. -/
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
    have hj_max_lt : j_max < k + 1 := Nat.lt_of_succ_le hj_max_le
    obtain ⟨N, hcolN, hclear_prev⟩ := ih (Nat.le_of_succ_le hj_max_le)
    set j : Fin (k + 1) := ⟨j_max, hj_max_lt⟩ with hj_def
    have h_prev : ∀ i j' : Fin (k + 1), j' < j → j' < i →
        (((a i / a j' : ℕ) : ℤ) ∣ N.1 i.succ j'.succ) := by
      intro i j' hj'_lt_j hj'_lt_i
      have : j'.val < j_max := hj'_lt_j
      exact hclear_prev i j' this hj'_lt_i
    obtain ⟨c, h_zero, h_clear⟩ := h_supply j N hcolN h_prev
    obtain ⟨N', hcolN', hclear_new⟩ :=
      sl_clear_one_column_step_multi_donor a ha hda w j N hcolN h_prev
        c h_zero h_clear
    refine ⟨N', hcolN', ?_⟩
    intro i j' hj'_lt_succ hj'_lt_i
    have hj'_le_j : j' ≤ j := by
      show j'.val ≤ j.val
      exact Nat.lt_succ_iff.mp hj'_lt_succ
    exact hclear_new i j' hj'_le_j hj'_lt_i

/-- **Conditional consumer (multi-donor).** Multi-donor analogue of
`sl_exists_col_stab_divChain_of_donor_supply`: bridges
`sl_exists_col_of_primitive`, `sl_clear_all_columns_of_multi_donor_supply`, and
`sl_exists_col_stab_divChain_of_lower_clearance` into one statement. Under a
multi-donor supply oracle (returning a full coefficient vector
`c : Fin (k+2) → ℤ` with `c j.succ = 0` instead of a single donor index), there
exists `N` with first column `w` whose diagonal-conjugate lies in the
`GL_pair (k + 2)` stabilizer.

The remaining mathematical content is the oracle hypothesis `h_supply` itself:
for each target column `j : Fin (k+1)` and each cleared matrix `N`
(satisfying first-column = `w` and the previously-cleared-columns divisibilities
`(a i / a j') ∣ N.1 i.succ j'.succ` for `j' < j < i`), one must produce a
coefficient vector `c : Fin (k+2) → ℤ` with `c j.succ = 0` such that
`(a i / a j) ∣ N.1 i.succ j.succ + ∑ k', c k' * N.1 i.succ k'` for every
`i > j`. This is the precise classical multi-row Bezout / SNF arithmetic
oracle that the rest of `sl_exists_col_stab_divChain` reduces to; it is left
as a separate ticket and is *not* discharged here. -/
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

/-- **Coordinatewise vector chain CRT.** A vector-valued analogue of
`exists_chain_solution_iff_compatible`: given a chain-ordered modulus
`d : Fin (n + 1) → ℤ` (`d a ∣ d b` for `a ≤ b`) and per-row vectors
`c_per : Fin (n + 1) → Fin n' → ℤ` whose coordinatewise differences satisfy
the chain compatibility `d a ∣ c_per b k - c_per a k` for every coordinate
`k` and every `a ≤ b`, we obtain a single vector `c : Fin n' → ℤ` with
`d a ∣ c k - c_per a k` for every `a` and `k`. The construction simply
takes `c k := c_per (Fin.last n) k`; chain compatibility against the top
index discharges every row simultaneously. -/
private lemma exists_vector_chain_solution
    {n n' : ℕ} (d : Fin (n + 1) → ℤ)
    (_h_chain : ∀ a b : Fin (n + 1), a ≤ b → d a ∣ d b)
    (c_per : Fin (n + 1) → Fin n' → ℤ)
    (h_compat : ∀ a b : Fin (n + 1), a ≤ b → ∀ k : Fin n',
      d a ∣ c_per b k - c_per a k) :
    ∃ c : Fin n' → ℤ, ∀ a : Fin (n + 1), ∀ k : Fin n',
      d a ∣ c k - c_per a k := by
  refine ⟨fun k ↦ c_per (Fin.last n) k, ?_⟩
  intro a k
  exact h_compat a (Fin.last n) (Fin.le_last _) k

/-- **Generic vector avoiding-Bezout to residue.** Given a vector `x : Fin n → ℤ`,
a target index `j` to avoid, and an avoiding Bezout witness `u : Fin n → ℤ` with
`u j = 0` and `∑ k, u k * x k = 1`, we can produce, for any `xj d : ℤ`, a
coefficient vector `c : Fin n → ℤ` with `c j = 0` and `d ∣ xj + ∑ k, c k * x k`.
The construction is `c k := -xj * u k`; then the inner sum equals `-xj`, so the
outer sum is `0`, and any `d` divides `0`. This is the generic linear-algebraic
content underlying `sl_row_clear_mod_avoiding`. -/
private lemma row_clear_avoiding_of_bezout
    {n : ℕ} (x : Fin n → ℤ) (j : Fin n)
    (u : Fin n → ℤ) (h_zero : u j = 0) (h_bez : ∑ k, u k * x k = 1)
    (xj d : ℤ) :
    ∃ c : Fin n → ℤ, c j = 0 ∧ d ∣ xj + ∑ k, c k * x k := by
  refine ⟨fun k ↦ -xj * u k, by simp [h_zero], ?_⟩
  have h_sum : ∑ k, (-xj * u k) * x k = -xj := by
    have h1 : ∑ k, (-xj * u k) * x k = -xj * ∑ k, u k * x k := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [h1, h_bez, mul_one]
  rw [h_sum, add_neg_cancel]
  exact dvd_zero d

/-- **Conditional consumer (row-wise avoiding Bezout to per-row residues).**
Given, for every target column `j`, every cleared matrix `N` with first column
`w`, an externally supplied family `u : Fin (k+1) → Fin (k+2) → ℤ` of avoiding
Bezout witnesses (`u i j.succ = 0`, `∑ k', u i k' * N.1 i.succ k' = 1` for
`j < i`) plus chain compatibility on the constructed family
`c_per_constructed i k' := -(N.1 i.succ j.succ) * u i k'`, we obtain the
`h_per_row` shape consumed by `h_supply_of_row_residues`. The chain
compatibility is asserted on the constructed family rather than on the raw
witnesses because `u_i` and `u_{i'}` are chosen independently per row, and
chain compatibility on `c_per_constructed` is *not* automatic from chain
compatibility on `u`. -/
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
      have h1 : ∑ k', (-(N.1 i.succ j.succ) * u i k') * N.1 i.succ k' =
          -(N.1 i.succ j.succ) * ∑ k', u i k' * N.1 i.succ k' := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k' _ ↦ ?_
        ring
      rw [h1, hu_bez i hi_lt, mul_one]
    rw [h_sum, add_neg_cancel]
    exact dvd_zero _
  · intro i i' hi_lt hi_le k'
    exact hu_compat i i' hi_lt hi_le k'

/-- **Per-row residue oracle reduction.** Packages the per-row data
(coordinate vectors `c_per i : Fin (k + 2) → ℤ`, each annihilating the
target column `j.succ`, each clearing its own row, plus the chain
compatibility `(a i / a j) ∣ c_per i' k' - c_per i k'` for `j < i ≤ i'`)
into the single-vector multi-donor `h_supply` shape consumed by
`sl_exists_col_stab_divChain_of_multi_donor_supply`. The construction takes
`c := c_per (Fin.last k)` and absorbs the row-by-row corrections via the
chain compatibility. -/
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
  have hrow := h_clear_per i hi_lt
  have hcompat_k : ∀ k' : Fin (k + 2),
      (((a i / a j : ℕ) : ℤ) ∣ c_per (Fin.last k) k' - c_per i k') := by
    intro k'
    exact h_compat i (Fin.last k) hi_lt (Fin.le_last _) k'
  have hdiff_sum : (((a i / a j : ℕ) : ℤ)) ∣
      ∑ k', (c_per (Fin.last k) k' - c_per i k') * N.1 i.succ k' :=
    Finset.dvd_sum (fun k' _ ↦ (hcompat_k k').mul_right _)
  have hsum := hrow.add hdiff_sum
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

/-- **Conditional consumer (per-row residues).** Direct composition of
`h_supply_of_row_residues` with `sl_exists_col_stab_divChain_of_multi_donor_supply`:
under a per-row residue oracle (yielding row-indexed coefficient vectors
satisfying coordinatewise chain compatibility), there exists `N` with first
column `w` whose diagonal-conjugate lies in the `GL_pair (k + 2)` stabilizer. -/
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

/-- **Common-ν conditional helper.** Assume a SINGLE avoiding Bezout vector `ν`
good for all rows simultaneously, together with a target-column congruence
condition. We derive the `h_avoiding_compat` package shape consumed by
`h_per_row_via_avoiding_bezout`. The construction takes `u i := ν` (the common
witness) for every row; chain compatibility on the constructed family
`c_per i k' := -(N.1 i.succ j.succ) * ν k'` follows because the differences of
target-column entries `N.1 i'.succ j.succ - N.1 i.succ j.succ` are divisible
by `(a i / a j)` by hypothesis, and divisibility is preserved under
multiplication by `-ν k'`. -/
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
  refine ⟨fun _ k' ↦ ν k', ?_, ?_, ?_⟩
  · intro _; exact hν_zero
  · intro i hi_lt; exact hν_bez i hi_lt
  · intro i i' hi_lt hi_le k'
    have hdvd : (((a i / a j : ℕ) : ℤ)) ∣
        N.1 i'.succ j.succ - N.1 i.succ j.succ := hν_col i i' hi_lt hi_le
    have heq : (-(N.1 i'.succ j.succ) * ν k') - (-(N.1 i.succ j.succ) * ν k')
        = -((N.1 i'.succ j.succ - N.1 i.succ j.succ) * ν k') := by ring
    rw [heq]
    exact (hdvd.mul_right _).neg_right

/-- **Conditional consumer (common-ν to per-row residues).** Direct composition
of `h_avoiding_compat_of_common_nu` with `h_per_row_via_avoiding_bezout`. -/
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

/-- **Final conditional consumer (common-ν to H-membership).** Direct composition
of `h_per_row_of_common_nu` with `sl_exists_col_stab_divChain_of_row_residues`. -/
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

/- **Remaining oracle (precise statement of the open arithmetic content).**
The two outstanding `sorry`s in this file (`sl_exists_col_stab_divChain` at
~L4178 and `fiber_has_block_form_preimages` at ~L4206) both reduce, via
`sl_exists_col_stab_divChain_of_multi_donor_supply`, to the following
self-contained classical arithmetic claim:

  Given:
    * `k : ℕ`,
    * a positive divisor chain `a : Fin (k+1) → ℕ` with `a i ∣ a (i+1)`,
    * a primitive vector `w : Fin (k+2) → ℤ` with `(a i) ∣ w i.succ`,
    * a target column index `j : Fin (k+1)`,
    * an `SL_{k+2}(ℤ)` matrix `N` with first column `w` and with the previous
      columns already cleared:
        `∀ i j' : Fin (k+1), j' < j → j' < i → (a i / a j') ∣ N.1 i.succ j'.succ`,

  Find a coefficient vector `c : Fin (k+2) → ℤ` with `c j.succ = 0` and
        `∀ i : Fin (k+1), j < i → (a i / a j) ∣ N.1 i.succ j.succ +
                                   ∑ k', c k' * N.1 i.succ k'`.

This is a multi-row simultaneous Bezout / SNF column-reduction problem on the
columns ≠ `j.succ` of `N` (the `c j.succ = 0` constraint forbids touching the
target column itself). The natural proof packages a finite-row CRT step
(cf. `sl_addCol_make_dvd_finset`) with the divisor-chain compatibility
`(a i / a j) ∣ (a i' / a j)` for `i ≤ i'`, exploiting that the rows below `j`
form a `det = ±1` block whose entries can be made coprime to the target moduli
`(a i / a j)`. It is the *only* remaining mathematical content needed to
discharge `sl_exists_col_stab_divChain` (and, transitively,
`fiber_has_block_form_preimages`) — every other reduction in this section is
already in place. The oracle is intentionally left open here; downstream
infrastructure (`sl_clear_all_columns_of_multi_donor_supply`,
`sl_exists_col_stab_divChain_of_multi_donor_supply`,
`sl_exists_col_stab_divChain_of_lower_clearance`) consumes it directly. -/

/- **T001 diagnosis (2026-04-25): the `h_common` reduction route is too strong.**

The conditional consumer `sl_exists_col_stab_divChain_of_common_nu` reduces the
oracle to a "common avoiding-Bezout vector" hypothesis `h_common` (cf.
`h_avoiding_compat_of_common_nu`, `h_per_row_of_common_nu`). For an arbitrary
`SL_{k+2}(ℤ)` matrix `N` with first column `w` and previous columns `j' < j`
cleared, `h_common` demands a SINGLE coefficient vector `ν : Fin (k + 2) → ℤ`
with `ν j.succ = 0` such that *for every row* `i > j`,
  `∑ k', ν k' * N.1 i.succ k' = 1`,
PLUS a target-column congruence
  `(a i / a j) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ`  for `j < i ≤ i'`.

Both conjuncts are FALSE for generic `N`:

(A) **No common Bezout-`1` vector across rows in general.** Writing `M` for the
    `((k + 1 - j) × (k + 2))` submatrix of rows `i > j` of `N.1.succ`, the
    constraint `M · ν = 𝟙` with `ν j.succ = 0` is a ℤ-linear system on the
    `(k + 1)`-dimensional subspace `{ν : ν j.succ = 0}`. For `j = 0` and
    `k ≥ 1` (so at least 2 rows below), choose `N` whose lower rows are linearly
    dependent modulo a prime `p` (always achievable inside `SL_{k+2}(ℤ)` by row
    operations *on rows above* `0` — those rows are free for the consumer to
    pick). Then `M ν ≡ (c, c, …)ᵀ (mod p)` for a single scalar `c`, so
    `(1, 1, …, 1)ᵀ` is unreachable mod `p`. This is precisely the Smith normal
    form obstruction: the gcd of the maximal minors of `M` (excluding column
    `j.succ`) need not be `1`.

(B) **The target-column congruence is not maintained by the iterative loop.**
    `sl_clear_all_columns_of_multi_donor_supply` enters column `j` with
    `N.1 i.succ j.succ` already mutated by the previous `j' < j` clearing
    steps; those steps perform unrestricted row-additions among rows
    `j' < i ≤ k`, and have no mechanism to enforce
    `(a i / a j) ∣ N.1 i'.succ j.succ - N.1 i.succ j.succ`. Concretely, the
    column-`j` clearing step uses `sl_clear_one_column_step_multi_donor`, which
    is silent about column `j.succ`.

Conclusion: the `_of_common_nu` reduction layer is a CONVENIENCE wrapper for
the case where `N` happens to admit a common Bezout vector — it is NOT a
sufficient route to discharge the open oracle.

**Recommended next-stint approach (does not pass through `h_common`):**

1. Build `N₀` not from generic `sl_exists_col_of_primitive`, but from a
   Smith- or Hermite-normal-form construction: produce `N₀ ∈ SL_{k+2}(ℤ)` with
   first column `w` AND with the lower `(k + 1) × (k + 1)` block `B` already
   in column-Hermite form. Then for each `j`, the `j`-th column of `B` is
   `(a j / a 0, …)ᵀ`-aligned, and the per-row Bezout step reduces to a
   one-row coprimality fact (`gcd(B i j, …) = 1`) inherited from
   `det B = ±1`.

2. Alternatively, replace the oracle entirely by an iterative refinement
   `N_j ∈ SL_{k+2}(ℤ)` (one per `j`) maintaining the explicit invariant
   "lower block is Hermite-reduced through column `j - 1`". This bypasses the
   need for any per-step Bezout common vector: the SNF/HNF reduction supplies
   the divisor-chain divisibility directly via column operations.

3. Either approach uses `sl_addCol_make_dvd_finset` only as a single-row
   tool, never asking it to satisfy a multi-row simultaneous constraint.

The current file's `_of_common_nu`/`_of_row_residues`/`_of_multi_donor_supply`
chain is preserved as scaffolding (its other consumers may still be useful),
but the open `sl_exists_col_stab_divChain` (k ≥ 1) cannot be discharged
through `h_common`. A future stint should target the HNF approach above. -/

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
  have hi : i.val = 0 := Nat.lt_one_iff.mp i.isLt
  have hj : j.val = 0 := Nat.lt_one_iff.mp j.isLt
  simp only [Fin.lt_def, hj, hi, lt_irrefl] at hji

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

/-- **SNF bridge for a square integer matrix with positive determinant.**
A repackaging of `exists_diagonal_of_posdet`: every `A : Matrix (Fin n) (Fin n) ℤ`
with `0 < det A` is `SL_n(ℤ)`-equivalent (on both sides) to a positive diagonal.
Exposed in `(L, R, d)` form for downstream completion-construction use. -/
private lemma exists_diagonal_of_posdet_for_lower_block {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    ∃ (L R : SpecialLinearGroup (Fin n) ℤ) (d : Fin n → ℤ),
      (∀ i, 0 < d i) ∧
      (L : Matrix (Fin n) (Fin n) ℤ) * A * (R : Matrix (Fin n) (Fin n) ℤ) =
        Matrix.diagonal d := by
  obtain ⟨d, hd_pos, L, R, hLR⟩ := exists_diagonal_of_posdet (n := n) A hdet
  exact ⟨L, R, d, hd_pos, hLR⟩

end HeckeRing.GLn
