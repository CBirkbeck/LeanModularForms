/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

/-!
# Index of Congruence Subgroups

Computes the index `[SL₂(ℤ) : Γ₀(pᵏ)] = pᵏ⁻¹(p + 1)` for prime `p` and `k ≥ 1`.

## Main results

* `Gamma0_prime_index` : `(Gamma0 p).index = p + 1` for prime `p`
* `Gamma0_relindex_step` : `(Gamma0 (p^(k+1))).relIndex (Gamma0 (p^k)) = p`
* `Gamma0_prime_power_index` : `(Gamma0 (p^k)).index = p^(k-1) * (p + 1)` for `k ≥ 1`

## References

* Shimura, Theorem 3.24
-/

open Matrix.SpecialLinearGroup Matrix ModularGroup CongruenceSubgroup

open scoped MatrixGroups

namespace HeckeRing.GL2

private lemma ZMod_inv_mul_cancel (p : ℕ) (hp : Nat.Prime p) (a : ℤ)
    (h : (a : ZMod p) ≠ 0) : (a : ZMod p)⁻¹ * (a : ZMod p) = 1 := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  refine ZMod.coe_int_inv_mul_eq_one ?_
  rw [isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]
  show Nat.Coprime p a.natAbs
  rw [hp.coprime_iff_not_dvd]
  exact fun hdvd ↦ h ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mpr
    ((Int.natCast_dvd_natCast.mpr hdvd).trans (Int.natAbs_dvd.mpr dvd_rfl)))

private lemma SL2_entry_mul (A B : SL(2, ℤ)) (i j : Fin 2) :
    (A * B).1 i j = A.1 i 0 * B.1 0 j + A.1 i 1 * B.1 1 j := by
  show (A.1 * B.1) i j = _; rw [Matrix.mul_apply, Fin.sum_univ_two]

private lemma TjS_inv_10 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 0 = -1 := by
  simp [coe_T_zpow, coe_S, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]

private lemma TjS_inv_11 (j : ℤ) : ((T ^ j * S)⁻¹).1 1 1 = j := by
  simp [coe_T_zpow, coe_S, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]

private lemma TjS_00 (j : ℤ) : (T ^ j * S).1 0 0 = j := by
  simp [coe_T_zpow, coe_S]

private lemma TjS_10 (j : ℤ) : (T ^ j * S).1 1 0 = 1 := by
  simp [coe_S]

private lemma TjS_inv_mul_10 (j : ℤ) (σ : SL(2, ℤ)) :
    ((T ^ j * S)⁻¹ * σ).1 1 0 = j * σ.1 1 0 - σ.1 0 0 := by
  rw [SL2_entry_mul, TjS_inv_10, TjS_inv_11]; ring

private lemma rep_diff_10 (i j : ℤ) :
    ((T ^ j * S)⁻¹ * (T ^ i * S)).1 1 0 = j - i := by
  rw [TjS_inv_mul_10, TjS_10, TjS_00]; ring

section BaseCase

variable (p : ℕ) (hp : Nat.Prime p)
include hp

private noncomputable def Gamma0Rep (j : Fin (p + 1)) : SL(2, ℤ) :=
  if j.val < p then T ^ (j.val : ℤ) * S else 1

private lemma Gamma0_prime_index_inj :
    Function.Injective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro ⟨j₁, hj₁⟩ ⟨j₂, hj₂⟩ hf
  rw [QuotientGroup.eq, Gamma0_mem] at hf
  simp only [Gamma0Rep] at hf
  split_ifs at hf with h1 h2
  · rw [rep_diff_10, ZMod.intCast_zmod_eq_zero_iff_dvd] at hf
    obtain ⟨k, hk⟩ := hf
    have hk0 : k = 0 := by
      rcases lt_trichotomy k 0 with hk_neg | rfl | hk_pos
      · nlinarith [hp.pos, Int.natCast_nonneg j₁]
      · rfl
      · nlinarith [hp.pos, (mod_cast h2 : (j₂ : ℤ) < p)]
    subst hk0; simp only [Fin.mk.injEq]; omega
  · rw [mul_one, TjS_inv_10] at hf
    exact absurd hf (by norm_num)
  · rw [inv_one, one_mul, TjS_10] at hf
    exact absurd hf (by norm_num)
  · simp only [Fin.mk.injEq]; omega

private lemma Gamma0_prime_index_surj :
    Function.Surjective (fun j : Fin (p + 1) ↦ QuotientGroup.mk (Gamma0Rep p j) :
      Fin (p + 1) → SL(2, ℤ) ⧸ (Gamma0 p)) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  intro x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective x
  by_cases h : ((σ 1 0 : ℤ) : ZMod p) = 0
  · refine ⟨⟨p, Nat.lt_succ_iff.mpr le_rfl⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simp only [Gamma0Rep, show ¬(p < p) from lt_irrefl p, ite_false, inv_one, one_mul]
    exact h
  · set j₀ := ((σ.1 0 0 : ℤ) : ZMod p) * ((σ.1 1 0 : ℤ) : ZMod p)⁻¹ with hj₀_def
    refine ⟨⟨j₀.val, Nat.lt_succ_of_lt (ZMod.val_lt j₀)⟩, ?_⟩
    rw [QuotientGroup.eq, Gamma0_mem]
    simp only [Gamma0Rep, show j₀.val < p from ZMod.val_lt _, ite_true]
    rw [TjS_inv_mul_10]
    push_cast
    rw [ZMod.natCast_zmod_val, hj₀_def]
    simp [mul_assoc, ZMod_inv_mul_cancel p hp (σ.1 1 0) h]

/-- `[SL₂(ℤ) : Γ₀(p)] = p + 1` for prime `p`. -/
theorem Gamma0_prime_index : (Gamma0 p).index = p + 1 := by
  rw [Subgroup.index, ← Nat.card_congr (Equiv.ofBijective _
    ⟨Gamma0_prime_index_inj p hp, Gamma0_prime_index_surj p hp⟩), Nat.card_fin]

end BaseCase

section InductiveStep

variable (p : ℕ) (hp : Nat.Prime p)
include hp

private def lowerTriRep (k : ℕ) (c : Fin p) : SL(2, ℤ) :=
  ⟨!![1, 0; (c : ℤ) * (p : ℤ) ^ k, 1], by simp [det_fin_two_of]⟩

omit hp in
private lemma lowerTriRep_mem_Gamma0 (k : ℕ) (_hk : 0 < k) (c : Fin p) :
    (lowerTriRep p k c : SL(2, ℤ)) ∈ Gamma0 (p ^ k) := by
  rw [Gamma0_mem, show (lowerTriRep p k c).1 1 0 = (c : ℤ) * (p : ℤ) ^ k from by
    simp [lowerTriRep], ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact_mod_cast dvd_mul_left (p ^ k : ℕ) (c.val)

omit hp in
private lemma lowerTriRep_diff_entry (k : ℕ) (c₁ c₂ : Fin p) :
    ((lowerTriRep p k c₁)⁻¹ * lowerTriRep p k c₂).1 1 0 =
    ((c₂ : ℤ) - (c₁ : ℤ)) * (p : ℤ) ^ k := by
  simp [lowerTriRep, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]
  ring

omit hp in
private lemma lowerTriRep_inv_mul_10 (k : ℕ) (c : Fin p) (σ : SL(2, ℤ)) :
    ((lowerTriRep p k c)⁻¹ * σ).1 1 0 =
    σ.1 1 0 - (c : ℤ) * (p : ℤ) ^ k * σ.1 0 0 := by
  rw [SL2_entry_mul]
  simp [lowerTriRep, Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two_of]
  ring

private noncomputable def relindexRep (k : ℕ) (hk : 0 < k) (c : Fin p) :
    ↥(Gamma0 (p ^ k)) :=
  ⟨lowerTriRep p k c, lowerTriRep_mem_Gamma0 p k hk c⟩

private lemma Gamma0_relindex_step_inj (k : ℕ) (hk : 0 < k) :
    Function.Injective (fun c : Fin p ↦
      (QuotientGroup.mk (relindexRep p k hk c) :
        ↥(Gamma0 (p ^ k)) ⧸ (Gamma0 (p ^ (k + 1))).subgroupOf (Gamma0 (p ^ k)))) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ hf
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Gamma0_mem] at hf
  simp only [InvMemClass.coe_inv, MulMemClass.coe_mul, relindexRep] at hf
  change (((lowerTriRep p k ⟨c₁, hc₁⟩)⁻¹ * lowerTriRep p k ⟨c₂, hc₂⟩).1 1 0 :
    ZMod (p ^ (k + 1))) = 0 at hf
  rw [lowerTriRep_diff_entry p, ZMod.intCast_zmod_eq_zero_iff_dvd] at hf
  rw [show (↑(p ^ (k + 1)) : ℤ) = (p : ℤ) ^ k * (p : ℤ) from by push_cast; rw [pow_succ],
    mul_comm ((↑c₂ : ℤ) - ↑c₁) ((p : ℤ) ^ k),
    mul_dvd_mul_iff_left (pow_ne_zero k (Int.natCast_ne_zero.mpr hp.ne_zero))] at hf
  obtain ⟨m, hm⟩ := hf
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hm_neg | rfl | hm_pos
    · nlinarith [hp.pos, Int.natCast_nonneg c₂, (mod_cast hc₁ : (c₁ : ℤ) < p)]
    · rfl
    · nlinarith [hp.pos, Int.natCast_nonneg c₁, (mod_cast hc₂ : (c₂ : ℤ) < p)]
  subst hm0; simp only [mul_zero, sub_eq_zero] at hm
  simp only [Fin.mk.injEq]; exact_mod_cast hm.symm

private lemma Gamma0_relindex_step_surj (k : ℕ) (hk : 0 < k) :
    Function.Surjective (fun c : Fin p ↦
      (QuotientGroup.mk (relindexRep p k hk c) :
        ↥(Gamma0 (p ^ k)) ⧸ (Gamma0 (p ^ (k + 1))).subgroupOf (Gamma0 (p ^ k)))) := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro x
  obtain ⟨⟨σ, hσ_K⟩, rfl⟩ := QuotientGroup.mk_surjective x
  have h_dvd : (↑(p ^ k) : ℤ) ∣ σ.1 1 0 := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd, ← Gamma0_mem]
  obtain ⟨q, hq⟩ := h_dvd
  push_cast at hq
  have h00_ne : ((σ.1 0 0 : ℤ) : ZMod p) ≠ 0 := by
    intro h_zero
    have h00_dvd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h_zero
    have h10_dvd : (p : ℤ) ∣ σ.1 1 0 :=
      hq ▸ dvd_mul_of_dvd_left (dvd_pow_self _ (Nat.pos_iff_ne_zero.mp hk)) q
    have hdet : σ.1 0 0 * σ.1 1 1 - σ.1 0 1 * σ.1 1 0 = 1 :=
      Matrix.det_fin_two σ.1 ▸ σ.2
    have h1_dvd : (p : ℤ) ∣ 1 :=
      hdet ▸ dvd_sub (dvd_mul_of_dvd_left h00_dvd _) (dvd_mul_of_dvd_right h10_dvd _)
    linarith [Int.le_of_dvd one_pos h1_dvd, (mod_cast hp.one_lt : (1 : ℤ) < p)]
  set c₀ := ((q : ℤ) : ZMod p) * ((σ.1 0 0 : ℤ) : ZMod p)⁻¹ with hc₀_def
  have hc_lt : c₀.val < p := ZMod.val_lt c₀
  refine ⟨⟨c₀.val, hc_lt⟩, ?_⟩
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp only [InvMemClass.coe_inv, MulMemClass.coe_mul]
  rw [Gamma0_mem]
  have h_p_dvd : (p : ℤ) ∣ (q - ↑c₀.val * σ.1 0 0) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, hc₀_def]
    simp [mul_assoc, ZMod_inv_mul_cancel p hp (σ.1 0 0) h00_ne]
  show (((lowerTriRep p k ⟨c₀.val, hc_lt⟩)⁻¹ * σ).1 1 0 : ZMod (p ^ (k + 1))) = 0
  rw [lowerTriRep_inv_mul_10 p k ⟨c₀.val, hc_lt⟩ σ, hq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [pow_succ]
  calc (p : ℤ) ^ k * (p : ℤ)
      ∣ (p : ℤ) ^ k * (q - ↑c₀.val * σ.1 0 0) := mul_dvd_mul_left _ h_p_dvd
    _ = ((p : ℤ) ^ k * q - ↑c₀.val * (p : ℤ) ^ k * σ.1 0 0) := by ring

/-- `[Γ₀(pᵏ) : Γ₀(p^{k+1})] = p` for `k >= 1`. -/
theorem Gamma0_relindex_step (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ (k + 1))).relIndex (Gamma0 (p ^ k)) = p := by
  rw [Subgroup.relIndex, Subgroup.index, ← Nat.card_congr (Equiv.ofBijective _
    ⟨Gamma0_relindex_step_inj p hp k hk, Gamma0_relindex_step_surj p hp k hk⟩), Nat.card_fin]

end InductiveStep

/-- `[SL₂(ℤ) : Γ₀(pᵏ)] = p^(k-1) * (p + 1)` for prime `p` and `k >= 1`. -/
theorem Gamma0_prime_power_index (p : ℕ) (hp : Nat.Prime p) (k : ℕ) (hk : 0 < k) :
    (Gamma0 (p ^ k)).index = p ^ (k - 1) * (p + 1) := by
  induction k with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm'
    · simp [Gamma0_prime_index p hp]
    · have h_le : Gamma0 (p ^ (m + 1)) ≤ Gamma0 (p ^ m) := fun σ hσ ↦ by
        rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ ⊢
        exact (Int.natCast_dvd_natCast.mpr (pow_dvd_pow p (Nat.le_succ m))).trans hσ
      rw [Nat.succ_sub_one, ← Subgroup.relIndex_mul_index h_le,
        Gamma0_relindex_step p hp m hm', ih hm', ← mul_assoc,
        show p * p ^ (m - 1) = p ^ m by rw [mul_comm, ← pow_succ]; congr 1; omega]

end HeckeRing.GL2
