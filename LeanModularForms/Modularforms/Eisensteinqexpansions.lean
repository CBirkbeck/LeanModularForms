/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

public import LeanModularForms.Modularforms.Delta

@[expose] public section

/-!
# `q`-expansions of Eisenstein series

This file develops the `q`-expansion of the (normalised) level-one Eisenstein series `E k`
for an even integer `k ≥ 3`. The key identity proved here is `E_k_q_expansion`, which
realises `E k` as `1` plus an explicit series in `q = cexp (2 π i z)`.

## Main definitions

* `E k hk` : the normalised level-one Eisenstein series of weight `k`.
* `gammaSetN N` : the homothetic copies of `gammaSet 1 1 0` scaled by `N`.

## Main results

* `E_k_q_expansion` : the standard `q`-expansion of `E k` for even `k ≥ 3`.
-/

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

noncomputable section Definitions

/-- The standard zero congruence condition on `Fin 2 → ZMod 1` used for level-one
Eisenstein series. -/
def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

/-- The normalised level-one Eisenstein series of weight `k`, where the `1/2` accounts for
summing over coprime integers rather than primitive lattice vectors. -/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeriesMF hk standardcongruencecondition

open Pointwise

def gammaSetN (N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 1 0

/-- For `v` in `gammaSetN N`, the underlying primitive vector in `gammaSet 1 1 0`. -/
def gammaSetN_map (N : ℕ) (v : gammaSetN N) : gammaSet 1 1 0 := by
  have hv2 : v.1 ∈ ({N} : Set ℕ) • gammaSet 1 1 0 := v.2
  rw [singleton_smul, mem_smul_set] at hv2
  exact ⟨hv2.choose, hv2.choose_spec.1⟩

lemma gammaSet_top_mem (v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  simp [gammaSet, ← Int.isCoprime_iff_gcd_eq_one, Subsingleton.eq_zero (Int.cast ∘ v)]

lemma gammaSetN_map_eq (N : ℕ) (v : gammaSetN N) : v.1 = N • gammaSetN_map N v := by
  have hv2 : v.1 ∈ ({N} : Set ℕ) • gammaSet 1 1 0 := v.2
  rw [singleton_smul, mem_smul_set] at hv2
  exact hv2.choose_spec.2.symm

/-- For `N ≠ 0`, scaling by `N` gives a bijection between `gammaSet 1 1 0` and its
homothetic copy `gammaSetN N`. -/
def gammaSetN_Equiv (N : ℕ) (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 1 0 where
  toFun v := gammaSetN_map N v
  invFun v := by
    use N • v
    simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
    use v
    simp
  left_inv v := by
    simp_rw [← gammaSetN_map_eq N v]
  right_inv v := by
    simp
    have H : N • v.1 ∈ gammaSetN N := by
      simp [gammaSetN]
      rw [@mem_smul_set]
      use v.1
      simp
    rw [gammaSetN] at H
    simp at H
    rw [@mem_smul_set] at H
    simp at H
    let x := H.choose
    have hx := H.choose_spec
    have hxv : ⟨x, hx.1⟩ = v := by
      ext i
      have hhxi := congr_fun hx.2 i
      simp [hN] at hhxi
      exact hhxi
    simp_rw [← hxv]
    rw [gammaSetN_map]
    simp_all only [ne_eq, nsmul_eq_mul, x]

lemma gammaSetN_eisSummand (k : ℤ) (z : ℍ) (n : ℕ) (v : gammaSetN n) :
    eisSummand k v z = ((n : ℂ) ^ k)⁻¹ * eisSummand k (gammaSetN_map n v) z := by
  simp only [eisSummand, gammaSetN_map_eq n v, Fin.isValue, Pi.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, zpow_neg, ← mul_inv]
  congr
  rw [← mul_zpow]
  ring_nf

/-- Sigma-type decomposition of integer pairs by their gcd. -/
def GammaSet_one_Equiv : (Fin 2 → ℤ) ≃ (Σ n : ℕ, gammaSetN n) where
  toFun v := ⟨(v 0).gcd (v 1),
    ⟨(v 0).gcd (v 1) • ![(v 0) / (v 0).gcd (v 1), (v 1) / (v 0).gcd (v 1)], by
      by_cases hn : 0 < (v 0).gcd (v 1)
      · refine Set.smul_mem_smul ?_ ?_
        · simp only [Fin.isValue, mem_singleton_iff]
        · rw [gammaSet_top_mem, Int.isCoprime_iff_gcd_eq_one]
          exact Int.gcd_div_gcd_div_gcd hn
      simp only [Fin.isValue, not_lt, nonpos_iff_eq_zero] at hn
      rw [hn]
      simp only [singleton_smul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        CharP.cast_eq_zero, EuclideanDomain.div_zero, zero_smul, gammaSetN]
      refine ⟨![1, 1], ?_, ?_⟩
      · simp only [gammaSet_top_mem, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
        exact Int.isCoprime_iff_gcd_eq_one.mpr rfl
      · simp⟩⟩
  invFun v := v.2
  left_inv v := by
    ext i
    fin_cases i
    · exact Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
    · exact Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))
  right_inv v := by
    ext i
    · have hv2 := v.2.2
      simp only [gammaSetN, singleton_smul, mem_smul_set] at hv2
      obtain ⟨x, hx⟩ := hv2
      simp_rw [← hx.2]
      simp only [Fin.isValue, Pi.smul_apply, nsmul_eq_mul]
      rw [Int.gcd_mul_left, hx.1.2]
      omega
    · fin_cases i
      · refine Int.mul_ediv_cancel' ?_
        simpa using Int.gcd_dvd_left _ _
      · simpa using Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)


theorem q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k =
      2 * (riemannZeta (k)) + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * (z : ℂ) + d) ^ k := by
  have hkk : 1 < k := by linarith
  have hkz : 3 ≤ (k : ℤ) := by linarith
  have hsumm : Summable fun v : Fin 2 → ℤ => ‖1 / ((v 0 : ℂ) * z + v 1) ^ k‖ := by
    apply (EisensteinSeries.summable_norm_eisSummand hkz z).congr
    intro v
    simp_rw [eisSummand]
    simp only [Fin.isValue, zpow_neg, zpow_natCast, norm_inv, norm_pow, one_div]
  rw [Summable.tsum_prod, sum_int_even]
  · simp only [Int.cast_zero, zero_mul, zero_add, one_div, Int.cast_natCast, add_left_inj]
    rw [sum_int_even]
    · simp only [Int.cast_zero, Int.cast_natCast]
      have h0 : ((0 : ℂ) ^ k)⁻¹ = 0 := by simp; omega
      norm_cast at *
      rw [h0]
      simp [zero_add, mul_eq_mul_left_iff]
      norm_cast
      simp only [PNat.pow_coe, Nat.cast_pow]
      rw [zeta_nat_eq_tsum_of_gt_one hkk, ← tsum_pNat _ (by simp; omega)]
      simp only [one_div]
    · intro n
      simp only [Int.cast_neg, inv_inj]
      rw [Even.neg_pow hk2]
    have := (Complex.summable_one_div_nat_cpow (p := k)).mpr (by simp [hkk])
    simp only [one_div] at *
    norm_cast at *
    apply Summable.of_nat_of_neg_add_one
    · exact this.congr (by intro b; simp)
    rw [← summable_nat_add_iff 1] at this
    apply this.congr
    intro b
    congr
    rw [Even.neg_pow hk2]
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Int.cast_pow, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
  · intro n
    simp only [one_div, Int.cast_neg, neg_mul]
    apply symm
    rw [int_sum_neg]
    congr
    funext d
    simp only [Int.cast_neg, inv_inj]
    ring_nf
    have := Even.neg_pow hk2 (n * (z : ℂ) + d)
    rw [← this]
    ring
  · refine Summable.prod (f := fun x : ℤ × ℤ => 1 / ((x.1 : ℂ) * z + x.2) ^ k) ?_
    rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
    exact Summable.of_norm hsumm
  · rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
    exact Summable.of_norm hsumm

lemma EQ0 (k : ℕ) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), 1 / (x 0 * (z : ℂ) + x 1) ^ ↑k =
      ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k := by
  rw [← (piFinTwoEquiv fun _ => ℤ).tsum_eq]
  exact tsum_congr fun _ => by simp

lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), 1 / (x 0 * (z : ℂ) + x 1) ^ ↑k =
      2 * riemannZeta ↑k + 2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) *
        ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) := by
  rw [EQ0, q_exp_iden_2 k (by linarith) hk2]
  simp
  have h1 (c : ℕ+) := q_exp_iden k (by linarith) (c • z)
  simp [natPosSMul_apply] at *
  conv => enter [1, 2, 1]; ext c; rw [h1 c]
  rw [tsum_mul_left, ← mul_assoc]
  congr 1
  rw [Summable.tsum_comm]
  · rw [← tsum_sigma_eqn2, ← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq, Summable.tsum_prod']
    · simp
      congr
      ext i
      congr
      ext j
      ring_nf
    · simp
      rw [← sigmaAntidiagonalEquivProd.summable_iff]
      simp [sigmaAntidiagonalEquivProd]
      apply (summable_auxil_1 (k - 1) z).congr
      intro b
      simp [divisorsAntidiagonalFactors]
    simp
    intro b
    exact (a1 k b z).subtype _
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  simp [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
  apply (summable_auxil_1 (k - 1) z).congr
  intro b
  simp
  left
  ring_nf


lemma EQ22 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), eisSummand k x z =
    (riemannZeta (k)) * ∑' (c : gammaSet 1 1 0), eisSummand k c z := by
  rw [← GammaSet_one_Equiv.symm.tsum_eq]
  have hk1 : 1 < k := by omega
  have hr := zeta_nat_eq_tsum_of_gt_one hk1
  rw [Summable.tsum_sigma, GammaSet_one_Equiv, hr,
    tsum_mul_tsum_of_summable_norm (by simp [hk1])
      (by apply (EisensteinSeries.summable_norm_eisSummand hk z).subtype)]
  · simp
    rw [Summable.tsum_prod']
    · refine tsum_congr fun b => ?_
      by_cases hb : b = 0
      · rw [hb]
        simp only [CharP.cast_eq_zero]
        conv =>
          enter [2, 1]; ext c
          rw [show ((0 : ℂ) ^ k)⁻¹ = 0 by simp; omega]
          simp
        conv =>
          enter [1, 1]; ext c
          rw [gammaSetN_eisSummand k z, show (((0 : ℕ) : ℂ) ^ (k : ℤ))⁻¹ = 0 by simp; omega]
          simp
        simp
      conv => enter [1, 1]; ext c; rw [gammaSetN_eisSummand k z]
      have := (gammaSetN_Equiv b hb).tsum_eq (fun v => eisSummand k v z)
      simp_rw [tsum_mul_left]
      simp only [zpow_natCast, mul_eq_mul_left_iff, inv_eq_zero, pow_eq_zero_iff', Nat.cast_eq_zero,
        ne_eq]
      exact Or.inl this
    · apply summable_mul_of_summable_norm (f := fun (n : ℕ) => ((n : ℂ) ^ k)⁻¹)
        (g := fun (v : gammaSet 1 1 0) => eisSummand k v z)
      · simp only [norm_inv, norm_pow, norm_natCast, Real.summable_nat_pow_inv, hk1]
      apply (EisensteinSeries.summable_norm_eisSummand hk z).subtype
    intro b
    simp only
    apply Summable.mul_left
    apply Summable.of_norm
    apply (EisensteinSeries.summable_norm_eisSummand hk z).subtype
  have := (GammaSet_one_Equiv.symm.summable_iff (f := fun v => eisSummand k v z)).mpr ?_
  · exact this.congr fun _ => by simp
  exact (EisensteinSeries.summable_norm_eisSummand hk z).of_norm

lemma EQ2 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), 1 / (x 0 * (z : ℂ) + x 1) ^ ↑k =
      (riemannZeta (k)) * ∑' (c : gammaSet 1 1 0), 1 / ((c.1 0) * (z : ℂ) + (c.1 1)) ^ k := by
  have := EQ22 k hk z
  simp_rw [eisSummand] at this
  simp at *
  convert this


/-- The `q`-expansion of the normalised level-one Eisenstein series `E k` for even `k ≥ 3`. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
      (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [_root_.E]
  show (1 / 2 : ℂ) • (eisensteinSeriesMF hk standardcongruencecondition) z = _
  have hmf : (ModularForm.eisensteinSeriesMF hk standardcongruencecondition) z =
      (eisensteinSeriesSIF standardcongruencecondition k) z := rfl
  rw [hmf]
  have hsif := eisensteinSeriesSIF_apply standardcongruencecondition k z
  rw [hsif, eisensteinSeries, standardcongruencecondition]
  simp
  simp_rw [eisSummand]
  have HE1 := EQ1 k hk hk2 z
  have HE2 := EQ2 k hk z
  have z2 : (riemannZeta (k)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp
    omega
  rw [← inv_mul_eq_iff_eq_mul₀ z2] at HE2
  simp at HE1 HE2 ⊢
  have step := congrArg (2⁻¹ * ·) HE2.symm
  dsimp only at step
  suffices h : 2⁻¹ * ((riemannZeta ↑k)⁻¹ *
      ∑' (x : Fin 2 → ℤ), ((↑(x 0) * (↑z : ℂ) + ↑(x 1)) ^ k)⁻¹) =
      1 + (riemannZeta ↑k)⁻¹ * ((-(2 * ↑π * Complex.I)) ^ k / ↑(k - 1)!) *
        ∑' (n : ℕ+), ↑((σ (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) by
    convert step.symm ▸ h
  simp_rw [← mul_assoc]
  rw [HE1, mul_add]
  have : 2⁻¹ * (riemannZeta (k))⁻¹ * (2 * riemannZeta (k)) = 1 := by field_simp
  rw [this]
  ring
