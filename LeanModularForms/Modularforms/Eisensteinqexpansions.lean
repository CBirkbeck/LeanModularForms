module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

public import LeanModularForms.Modularforms.Delta

/-!
# `q`-expansions of level-one Eisenstein series

This file packages the level-one Eisenstein modular form `E k` and proves its
`q`-expansion `E_k_q_expansion`.

## Main definitions

* `standardCongruenceCondition`: the trivial congruence condition at level `1`.
* `E`: the normalized level-one Eisenstein series of weight `k ≥ 3` as a modular form.

## Main results

* `E_k_q_expansion`: the `q`-expansion of `E k` for `k ≥ 3` even.
-/

@[expose] public section

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

open scoped ArithmeticFunction.sigma

noncomputable section Definitions

/-- The trivial congruence condition at level `1`. -/
def standardCongruenceCondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

/-- The normalized level-one Eisenstein series of weight `k ≥ 3` as a modular form. The factor
`1/2` makes the sum (over coprime integers) match the standard normalization. -/
def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeriesMF hk standardCongruenceCondition

open Pointwise

private def gammaSetN (N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 1 0

private def gammaSetNMap (N : ℕ) (v : gammaSetN N) : gammaSet 1 1 0 := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set] at hv2
  exact ⟨hv2.choose, hv2.choose_spec.1⟩

private lemma gammaSet_top_mem (v : Fin 2 → ℤ) : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  simp only [gammaSet, Fin.isValue, mem_setOf_eq, ← Int.isCoprime_iff_gcd_eq_one,
    and_iff_right_iff_imp]
  exact fun _ ↦ Subsingleton.eq_zero (Int.cast ∘ v)

private lemma gammaSetNMap_eq (N : ℕ) (v : gammaSetN N) : v.1 = N • gammaSetNMap N v := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set] at hv2
  exact hv2.choose_spec.2.symm

private def gammaSetNEquiv (N : ℕ) (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 1 0 where
  toFun v := gammaSetNMap N v
  invFun v := ⟨N • v, by
    simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
    exact ⟨v, by simp⟩⟩
  left_inv v := by simp_rw [← gammaSetNMap_eq N v]
  right_inv v := by
    simp only
    have H : N • v.1 ∈ gammaSetN N := by
      simp only [gammaSetN, singleton_smul, mem_smul_set]
      exact ⟨v.1, by simp⟩
    rw [gammaSetN] at H
    simp only [singleton_smul, mem_smul_set] at H
    let x := H.choose
    have hx := H.choose_spec
    have hxv : (⟨x, hx.1⟩ : gammaSet 1 1 0) = v := by
      ext i
      have hhxi := congr_fun hx.2 i
      simpa [hN] using hhxi
    simp_rw [← hxv]
    rw [gammaSetNMap]
    simp_all only [ne_eq, nsmul_eq_mul, x]

private lemma gammaSetN_eisSummand (k : ℤ) (z : ℍ) (n : ℕ) (v : gammaSetN n) :
    eisSummand k v z = ((n : ℂ) ^ k)⁻¹ * eisSummand k (gammaSetNMap n v) z := by
  simp only [eisSummand, gammaSetNMap_eq n v, Fin.isValue, Pi.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, zpow_neg, ← mul_inv]
  congr
  rw [← mul_zpow]
  ring_nf

private def gammaSetOneEquiv : (Fin 2 → ℤ) ≃ (Σ n : ℕ, gammaSetN n) where
  toFun v := ⟨(v 0).gcd (v 1), ⟨(v 0).gcd (v 1) • ![v 0 / (v 0).gcd (v 1), v 1 / (v 0).gcd (v 1)],
    by
      by_cases hn : 0 < (v 0).gcd (v 1)
      · refine Set.smul_mem_smul (by simp only [Fin.isValue, mem_singleton_iff]) ?_
        rw [gammaSet_top_mem, Int.isCoprime_iff_gcd_eq_one]
        exact Int.gcd_div_gcd_div_gcd hn
      simp only [Fin.isValue, not_lt, nonpos_iff_eq_zero] at hn
      rw [hn]
      simp only [singleton_smul, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
        CharP.cast_eq_zero, EuclideanDomain.div_zero, zero_smul, gammaSetN]
      refine ⟨![1, 1], ?_, by simp⟩
      simp only [gammaSet_top_mem, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      exact Int.isCoprime_iff_gcd_eq_one.mpr rfl⟩⟩
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
      · exact Int.mul_ediv_cancel' (by simpa using Int.gcd_dvd_left _ _)
      · simpa using Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _)

private theorem q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k =
      2 * (riemannZeta k) + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * (z : ℂ) + d) ^ k := by
  have hkk : 1 < k := by linarith
  have hkz : 3 ≤ (k : ℤ) := by linarith
  have hsum : Summable (fun v : Fin 2 → ℤ ↦ ‖1 / ((v 0 : ℂ) * z + v 1) ^ k‖) :=
    (EisensteinSeries.summable_norm_eisSummand hkz z).congr fun v ↦ by simp [eisSummand]
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
    · exact this.congr fun b ↦ by simp
    rw [← summable_nat_add_iff 1] at this
    apply this.congr
    intro b
    congr
    rw [Even.neg_pow hk2]
    simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Int.cast_pow, Int.cast_add,
      Int.cast_natCast, Int.cast_one]
  · intro n
    simp only [one_div, Int.cast_neg, neg_mul]
    rw [eq_comm, int_sum_neg]
    congr
    funext d
    simp only [Int.cast_neg, inv_inj]
    ring_nf
    rw [← Even.neg_pow hk2 (n * (z : ℂ) + d)]
    ring
  · refine Summable.prod (f := fun x : ℤ × ℤ ↦ 1 / ((x.1 : ℂ) * z + x.2) ^ k) ?_
    rw [← (piFinTwoEquiv fun _ ↦ ℤ).summable_iff]
    exact .of_norm <| hsum.congr fun v ↦ by simp [piFinTwoEquiv_apply]
  · rw [← (piFinTwoEquiv fun _ ↦ ℤ).summable_iff]
    exact .of_norm <| hsum.congr fun v ↦ by simp [piFinTwoEquiv_apply]

private lemma tsum_fin2_eq_tsum_prod (k : ℕ) (z : ℍ) :
    ∑' x : Fin 2 → ℤ, 1 / (x 0 * (z : ℂ) + x 1) ^ (k : ℤ) =
      ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k := by
  rw [← (piFinTwoEquiv fun _ ↦ ℤ).tsum_eq]
  exact tsum_congr fun x ↦ by simp

private lemma tsum_one_div_pow_fin2_eq (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    ∑' x : Fin 2 → ℤ, 1 / (x 0 * (z : ℂ) + x 1) ^ (k : ℤ) =
      2 * riemannZeta k + 2 * ((-2 * π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, ((σ (k - 1)) n : ℂ) * cexp (2 * π * Complex.I * z * n) := by
  rw [tsum_fin2_eq_tsum_prod, q_exp_iden_2 k (by linarith) hk2]
  simp
  have h1 (c : ℕ+) := q_exp_iden k (by linarith) (c • z)
  simp [natPosSMul_apply] at *
  conv => enter [1, 2, 1]; ext c; rw [h1 c]
  rw [tsum_mul_left, ← mul_assoc]
  congr 1
  rw [Summable.tsum_comm]
  · rw [← tsum_sigma_eqn2, ← (piFinTwoEquiv fun _ ↦ ℕ+).symm.tsum_eq, Summable.tsum_prod']
    · simp
      congr
      ext i
      congr
      ext j
      ring_nf
    · simp
      rw [← sigmaAntidiagonalEquivProd.summable_iff]
      simp [sigmaAntidiagonalEquivProd]
      exact (summable_auxil_1 (k - 1) z).congr fun b ↦ by simp [divisorsAntidiagonalFactors]
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

private lemma tsum_eisSummand_eq_zeta_mul (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    ∑' x : Fin 2 → ℤ, eisSummand k x z =
      riemannZeta k * ∑' c : gammaSet 1 1 0, eisSummand k c z := by
  rw [← gammaSetOneEquiv.symm.tsum_eq]
  have hk1 : 1 < k := by omega
  have hr := zeta_nat_eq_tsum_of_gt_one hk1
  rw [Summable.tsum_sigma, gammaSetOneEquiv, hr, tsum_mul_tsum_of_summable_norm (by simp [hk1])
    ((EisensteinSeries.summable_norm_eisSummand hk z).subtype _)]
  · simp
    rw [Summable.tsum_prod']
    · apply tsum_congr
      intro b
      by_cases hb : b = 0
      · rw [hb]
        simp only [CharP.cast_eq_zero]
        conv => enter [2, 1]; ext c; rw [show ((0 : ℂ) ^ k)⁻¹ = 0 by simp; omega]; simp
        conv =>
          enter [1, 1]
          ext c
          rw [gammaSetN_eisSummand k z, show (((0 : ℕ) : ℂ) ^ (k : ℤ))⁻¹ = 0 by simp; omega]
          simp
        simp
      conv => enter [1, 1]; ext c; rw [gammaSetN_eisSummand k z]
      have := (gammaSetNEquiv b hb).tsum_eq (fun v ↦ eisSummand k v z)
      simp_rw [tsum_mul_left]
      simp only [zpow_natCast, mul_eq_mul_left_iff, inv_eq_zero, pow_eq_zero_iff', Nat.cast_eq_zero,
        ne_eq]
      exact .inl this
    · refine summable_mul_of_summable_norm (f := fun n : ℕ ↦ ((n : ℂ) ^ k)⁻¹)
        (g := fun v : gammaSet 1 1 0 ↦ eisSummand k v z) ?_ ?_
      · simp only [norm_inv, norm_pow, norm_natCast, Real.summable_nat_pow_inv, hk1]
      · exact (EisensteinSeries.summable_norm_eisSummand hk z).subtype _
    intro b
    simp only
    exact (((EisensteinSeries.summable_norm_eisSummand hk z).subtype _).of_norm).mul_left _
  have := (gammaSetOneEquiv.symm.summable_iff (f := fun v ↦ eisSummand k v z)).mpr ?_
  · exact this.congr fun b ↦ by simp
  exact (EisensteinSeries.summable_norm_eisSummand hk z).of_norm

private lemma tsum_one_div_pow_eq_zeta_mul (k : ℕ) (hk : 3 ≤ (k : ℤ)) (z : ℍ) :
    ∑' x : Fin 2 → ℤ, 1 / (x 0 * (z : ℂ) + x 1) ^ (k : ℤ) =
      riemannZeta k * ∑' c : gammaSet 1 1 0, 1 / ((c.1 0) * (z : ℂ) + c.1 1) ^ k := by
  have := tsum_eisSummand_eq_zeta_mul k hk z
  simp_rw [eisSummand] at this
  simp at *
  convert this

lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) :
    (E k hk) z = 1 +
      (1 / riemannZeta k) * ((-2 * π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, σ (k - 1) n * Complex.exp (2 * π * Complex.I * z * n) := by
  rw [_root_.E, IsGLPos.smul_apply]
  have hmf : (ModularForm.eisensteinSeriesMF hk standardCongruenceCondition) z =
      (eisensteinSeriesSIF standardCongruenceCondition k) z := rfl
  rw [hmf]
  have hsif := eisensteinSeriesSIF_apply standardCongruenceCondition k z
  rw [hsif, eisensteinSeries, standardCongruenceCondition]
  simp
  simp_rw [eisSummand]
  have HE1 := tsum_one_div_pow_fin2_eq k hk hk2 z
  have HE2 := tsum_one_div_pow_eq_zeta_mul k hk z
  have z2 : riemannZeta k ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp
    omega
  rw [← inv_mul_eq_iff_eq_mul₀ z2] at HE2
  simp at *
  conv => enter [1, 2]; rw [← HE2]
  simp_rw [← mul_assoc]
  rw [HE1, mul_add]
  have : 2⁻¹ * (riemannZeta k)⁻¹ * (2 * riemannZeta k) = 1 := by field_simp
  rw [this]
  ring
