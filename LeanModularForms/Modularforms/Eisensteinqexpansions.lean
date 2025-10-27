import LeanModularForms.Modularforms.Delta
import Mathlib

open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat Classical

open ArithmeticFunction

noncomputable section Definitions

/- def standardcongruencecondition : Fin 2 → ZMod ((1 : ℕ+) : ℕ) := 0

def E (k : ℤ) (hk : 3 ≤ k) : ModularForm (CongruenceSubgroup.Gamma ↑1) k :=
  (1/2 : ℂ) • eisensteinSeries_MF hk standardcongruencecondition /-they need  1/2 for the
    normalization to match up (since the sum here is taken over coprime integers).-/
 -/
open Pointwise
/-
def gammaSetN (N : ℕ) : Set (Fin 2 → ℤ) := ({N} : Set ℕ) • gammaSet 1 1 0

def gammaSetN_map (N : ℕ) (v : gammaSetN N) : gammaSet 1 1 0 := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
  refine ⟨hv2.choose, hv2.choose_spec.1⟩

lemma gammaSet_top_mem (v : Fin 2 → ℤ)  : v ∈ gammaSet 1 1 0 ↔ IsCoprime (v 0) (v 1) := by
  rw [gammaSet]
  simp only [Fin.isValue, mem_setOf_eq, and_iff_right_iff_imp]
  exact fun h ↦ Subsingleton.eq_zero (Int.cast ∘ v)

lemma gammaSetN_map_eq (N : ℕ) (v : gammaSetN N) : v.1 = N • gammaSetN_map N v := by
  have hv2 := v.2
  simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
  exact (hv2.choose_spec.2).symm

def gammaSetN_Equiv (N : ℕ) (hN : N ≠ 0) : gammaSetN N ≃ gammaSet 1 0 where
  toFun v := gammaSetN_map N v
  invFun v := by
    use N • v
    simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
    refine ⟨v, by simp⟩
  left_inv v := by
    simp_rw [← gammaSetN_map_eq N v]
  right_inv v := by
    have H : N • v.1 ∈ gammaSetN N := by
      simp only [gammaSetN, singleton_smul, nsmul_eq_mul, mem_smul_set]
      refine ⟨v.1, by simp⟩
    simp [gammaSetN, mem_smul_set] at *
    let x := H.choose
    have hx := H.choose_spec
    have hxv : ⟨H.choose, H.choose_spec.1⟩ = v := by
      ext i
      simpa [hN] using (congr_fun H.choose_spec.2 i)
    simp_all only [gammaSetN_map] -/

lemma gammaSetN_eisSummand (k : ℤ) (z : ℍ) {n : ℕ} (v : gammaSet 1 n 0) : eisSummand k v z =
  ((n : ℂ) ^ k)⁻¹ * eisSummand k (divIntMap n v) z := by
  have := gammaSet_eq_gcd_mul_divIntMap v.2
  simp_rw [eisSummand]
  nth_rw 1 2 [this]
  simp only [Fin.isValue, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, zpow_neg, ←
    mul_inv, ← mul_zpow, inv_inj]
  ring_nf
/-
private def Fin_to_GammaSetN (v : Fin 2 → ℤ) : Σ n : ℕ, gammaSetN n := by
  refine ⟨(v 0).gcd (v 1), ⟨(v 0).gcd (v 1) • ![(v 0)/(v 0).gcd (v 1), (v 1)/(v 0).gcd (v 1)], ?_⟩⟩
  by_cases hn : 0 < (v 0).gcd (v 1)
  · apply Set.smul_mem_smul (by aesop)
    rw [gammaSet_top_mem, Int.isCoprime_iff_gcd_eq_one]
    apply Int.gcd_div_gcd_div_gcd hn
  · simp only [gammaSetN, Fin.isValue, (nonpos_iff_eq_zero.mp (not_lt.mp hn)), singleton_smul,
      Nat.succ_eq_add_one, Nat.reduceAdd, CharP.cast_eq_zero, EuclideanDomain.div_zero, zero_nsmul]
    refine ⟨![1,1], by simpa [gammaSet_top_mem] using Int.isCoprime_iff_gcd_eq_one.mpr rfl⟩

def GammaSet_one_Equiv : (Fin 2 → ℤ) ≃ (Σ n : ℕ, gammaSetN n) where
  toFun v := Fin_to_GammaSetN v
  invFun v := v.2
  left_inv v := by
            ext i
            fin_cases i
            · refine Int.mul_ediv_cancel' (Int.gcd_dvd_left (v 0) (v 1))
            · refine Int.mul_ediv_cancel' (Int.gcd_dvd_right (v 0) (v 1))
  right_inv v := by
          ext i
          · have hv2 := v.2.2
            simp only [gammaSetN, singleton_smul, mem_smul_set, nsmul_eq_mul] at hv2
            obtain ⟨x, hx⟩ := hv2
            simp [← hx.2, Fin_to_GammaSetN, Fin.isValue, Int.gcd_mul_left,
              Int.isCoprime_iff_gcd_eq_one.mp hx.1.2]
          · fin_cases i
            · refine Int.mul_ediv_cancel'  ?_
              simpa using Int.gcd_dvd_left _ _
            · refine Int.mul_ediv_cancel' (Int.gcd_dvd_right _ _) -/


theorem q_exp_iden_2 (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k =
      2 * (riemannZeta (k)) + 2 * ∑' c : ℕ+, ∑' d : ℤ, 1 / (c * (z : ℂ) + d) ^ k :=
  by
  have hkk : 1 < (k ) := by
    linarith
  rw [Summable.tsum_prod, sum_int_even]
  · simp only [Int.cast_zero, zero_mul, zero_add, one_div, Int.cast_natCast, add_left_inj]
    rw [sum_int_even]
    simp
    have h0 : ((0 : ℂ) ^ k)⁻¹ = 0 := by simp; omega
    have h00 : ((0 ^ k : ℕ) : ℝ)⁻¹ = 0 := by simp; omega
    norm_cast at *
    rw [h0]
    simp [zero_add, mul_eq_mul_left_iff]
    norm_cast
    simp only [PNat.pow_coe, Nat.cast_pow]
    rw [zeta_nat_eq_tsum_of_gt_one hkk, ← tsum_pNat _ (by simp; omega)]
    simp only [one_div]
    intro n
    simp only [Int.cast_neg, inv_inj]
    rw [Even.neg_pow hk2]
    have := (Complex.summable_one_div_nat_cpow  (p := k)).mpr (by simp [hkk])
    simp only [one_div] at *
    norm_cast at *
    apply  Summable.of_nat_of_neg_add_one
    apply this.congr
    intro b
    simp
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
    have := Even.neg_pow hk2 (n* (z : ℂ)  + d)
    rw [←this]
    ring
  · have hkz : 3 ≤ (k : ℤ) := by linarith
    have:= Summable.prod  (f := fun x : ℤ × ℤ => 1 / ((x.1 : ℂ) * z + x.2) ^ k) ?_
    apply this
    rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
    apply Summable.of_norm
    apply (EisensteinSeries.summable_norm_eisSummand hkz z).congr
    intro v
    simp_rw [eisSummand]
    simp only [Fin.isValue, zpow_neg, zpow_natCast, norm_inv, norm_pow, UpperHalfPlane.coe, one_div,
      piFinTwoEquiv_apply, comp_apply]
  · have hkz : 3 ≤ (k : ℤ) := by linarith
    rw [← (piFinTwoEquiv fun _ => ℤ).summable_iff]
    apply Summable.of_norm
    apply (EisensteinSeries.summable_norm_eisSummand hkz z).congr
    intro v
    simp_rw [eisSummand]
    simp only [Fin.isValue, zpow_neg, zpow_natCast, norm_inv, norm_pow, UpperHalfPlane.coe, one_div,
      piFinTwoEquiv_apply, comp_apply]

lemma EQ0 (k : ℕ) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = ∑' x : ℤ × ℤ, 1 / ((x.1 : ℂ) * z + x.2) ^ k := by
  rw [← (piFinTwoEquiv fun _ => ℤ).tsum_eq]
  apply tsum_congr
  intro x
  simp

lemma EQ1 (k : ℕ) (hk : 3 ≤ (k : ℤ)) (hk2 : Even k) (z : ℍ) : ∑' (x : Fin 2 → ℤ),
    1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = 2 * riemannZeta ↑k +
    2 * ((-2 * ↑π * Complex.I) ^ k / ↑(k - 1)!) *
     ∑' (n : ℕ+), ↑((sigma (k - 1)) ↑n) * cexp (2 * ↑π * Complex.I * ↑z * ↑↑n) := by
  rw [EQ0,  q_exp_iden_2 k (by linarith) hk2]
  simp
  have h1 (c : ℕ+) := q_exp_iden k (by linarith) (c • z)
  simp [natPosSMul_apply] at *
  conv =>
    enter [1,2,1]
    ext c
    rw [h1 c]
  rw [tsum_mul_left]
  rw [← mul_assoc]
  congr 1
  rw [Summable.tsum_comm]
  rw [← tsum_sigma_eqn2]
  rw [← (piFinTwoEquiv fun _ => ℕ+).symm.tsum_eq]
  rw [Summable.tsum_prod']
  simp
  congr
  ext i
  congr
  ext j
  ring_nf
  simp
  rw [← sigmaAntidiagonalEquivProd.summable_iff]
  simp [sigmaAntidiagonalEquivProd]
  apply (summable_auxil_1 (k - 1) z).congr
  intro b
  simp [divisorsAntidiagonalFactors]
  simp
  intro b
  have A3 := a1 k b z
  apply A3.subtype
  rw [sigmaAntidiagonalEquivProd.summable_iff.symm]
  simp [sigmaAntidiagonalEquivProd, divisorsAntidiagonalFactors]
  apply (summable_auxil_1 (k - 1) z).congr
  intro b
  simp
  left
  ring_nf

@[simp]
lemma gammaSetDivGcdEquiv_eq (r : ℕ) [NeZero r] (v : gammaSet 1 r 0) :
    (gammaSetDivGcdEquiv r) v = divIntMap r v.1 := rfl

lemma tsum_prod_eisSummand_eq_riemannZeta_eisensteinSeries {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), eisSummand k x z =
    (riemannZeta (k)) * (eisensteinSeries (N := 1) 0 k z) := by
  rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq]
  have hk1 : 1 < k := by omega
  conv =>
    enter [1,1]
    ext c
    rw [gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries, Summable.tsum_sigma, zeta_nat_eq_tsum_of_gt_one hk1,
    tsum_mul_tsum_of_summable_norm (by simp [hk1])
    (by apply (summable_norm_eisSummand (by omega) z).subtype)]
  · simp only [one_div]
    rw [Summable.tsum_prod']
    · apply tsum_congr
      intro b
      by_cases hb : b = 0
      · simp [hb, CharP.cast_eq_zero, gammaSetN_eisSummand k z, show ((0 : ℂ) ^ k)⁻¹ = 0 by aesop]
      · haveI : NeZero b := ⟨by simp [hb]⟩
        simpa [gammaSetN_eisSummand k z, zpow_natCast, tsum_mul_left, hb]
         using (gammaSetDivGcdEquiv b).tsum_eq (fun v ↦ eisSummand k v z)
    · apply summable_mul_of_summable_norm (f:= fun (n : ℕ) ↦ ((n : ℂ) ^ k)⁻¹)
        (g := fun (v : gammaSet 1 1 0) ↦ eisSummand k v z) (by simp [hk1])
      apply (EisensteinSeries.summable_norm_eisSummand (by omega) z).subtype
    · exact fun b => by simpa using (Summable.of_norm (by apply
      (summable_norm_eisSummand (by omega) z).subtype)).mul_left (a := ((b : ℂ) ^ k)⁻¹)
  · apply ((gammaSetDivGcdSigmaEquiv.symm.summable_iff (f := fun v ↦ eisSummand k v z)).mpr
      (EisensteinSeries.summable_norm_eisSummand (by omega) z).of_norm).congr
    simp

lemma EQ22 {k : ℕ} (hk : 3 ≤ k) (z : ℍ) :
    ∑' (x : Fin 2 → ℤ), eisSummand k x z =
    (riemannZeta (k)) * (eisensteinSeries (N := 1) 0 k z) := by
  rw [← gammaSetDivGcdSigmaEquiv.symm.tsum_eq]
  have hk1 : 1 < k := by omega
  conv =>
    enter [1,1]
    ext c
    rw [gammaSetDivGcdSigmaEquiv_symm_eq]
  rw [eisensteinSeries, Summable.tsum_sigma, zeta_nat_eq_tsum_of_gt_one hk1,
    tsum_mul_tsum_of_summable_norm (by simp [hk1])
    (by apply (summable_norm_eisSummand (by omega) z).subtype)]
  · simp only [one_div]
    rw [Summable.tsum_prod']
    · apply tsum_congr
      intro b
      by_cases hb : b = 0
      · simp [hb, CharP.cast_eq_zero, gammaSetN_eisSummand k z, show ((0 : ℂ) ^ k)⁻¹ = 0 by aesop]
      · haveI : NeZero b := ⟨by simp [hb]⟩
        simpa [gammaSetN_eisSummand k z, zpow_natCast, tsum_mul_left, hb]
         using (gammaSetDivGcdEquiv b).tsum_eq (fun v ↦ eisSummand k v z)
    · apply summable_mul_of_summable_norm (f:= fun (n : ℕ) ↦ ((n : ℂ) ^ k)⁻¹)
        (g := fun (v : gammaSet 1 1 0) ↦ eisSummand k v z) (by simp [hk1])
      apply (EisensteinSeries.summable_norm_eisSummand (by omega) z).subtype
    · exact fun b => by simpa using (Summable.of_norm (by apply
      (summable_norm_eisSummand (by omega) z).subtype)).mul_left (a := ((b : ℂ) ^ k)⁻¹)
  · apply ((gammaSetDivGcdSigmaEquiv.symm.summable_iff (f := fun v ↦ eisSummand k v z)).mpr
      (EisensteinSeries.summable_norm_eisSummand (by omega) z).of_norm).congr
    simp

lemma EQ2 (k : ℕ) (hk : 3 ≤ k)  (z : ℍ) : ∑' (x : Fin 2 → ℤ),
  1 / (x 0 * (z : ℂ) + x 1) ^ ↑k = (riemannZeta (k)) * ∑' (c : gammaSet 1 1 0), 1 / ((c.1 0) * (z : ℂ) + (c.1 1)) ^ k := by
  have := EQ22 hk z
  simp_rw [eisSummand] at this
  simp [ UpperHalfPlane.coe] at *
  convert this
  simp [eisensteinSeries, eisSummand, UpperHalfPlane.coe]



/-This result is already proven in the modular forms repo and being PRed (slowly) into mathlib, so
we can use it freely here. -/
lemma E_k_q_expansion (k : ℕ) (hk : 3 ≤ k) (hk2 : Even k) (z : ℍ) :
    (E hk) z = 1 +
        (1 / (riemannZeta (k))) * ((-2 * ↑π * Complex.I) ^ k / (k - 1)!) *
        ∑' n : ℕ+, sigma (k - 1) n * Complex.exp (2 * ↑π * Complex.I * z * n) := by
  rw [E]
  rw [ModularForm.IsGLPos.smul_apply]
  have : (eisensteinSeries_MF (k := k) (by omega) 0) z =
    (eisensteinSeries_SIF (N := 1) 0 k) z := rfl
  rw [ this, eisensteinSeries_SIF_apply 0 k z,
    eisensteinSeries]
  simp
  simp_rw [eisSummand]
  have HE1 := EQ1 k (by norm_cast at *) hk2 z
  have HE2 := EQ2 k hk z
  have z2 : (riemannZeta (k)) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_lt_re ?_
    simp
    omega
  rw [← inv_mul_eq_iff_eq_mul₀ z2 ] at HE2
  simp [UpperHalfPlane.coe] at *
  conv =>
    enter [1,2]
    rw [← HE2]
  simp_rw [← mul_assoc]
  rw [HE1, mul_add]
  have : 2⁻¹ * (riemannZeta (k))⁻¹ * (2 * riemannZeta (k)) = 1 := by
    field_simp
  rw [this]
  ring
