/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations.Lemma4_6_14

/-!
# Strong Multiplicity One via Miyake §4.6 — Main Lemma (4.6.8)

The descent witness, the inductive step, and the subset-indexed helper for
Miyake Theorem 4.6.8. Part of a multi-file split of `SMOObligations.lean`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

private theorem miyake_descent_witness_exists
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f_lower : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k,
      f_lower ∈ cuspFormCharSpace k χ' ∧
      ∀ m : ℕ, Nat.Coprime m l' →
        (ModularFormClass.qExpansion (1 : ℝ) f_lower).coeff m =
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff (p * m) := by
  have hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ f).mpr hfχ
  have h_cnt_pos : 0 < descendCosetCount p N := by
    have := hp.pos
    unfold descendCosetCount; split_ifs <;> lia
  set c : ℂ := (p : ℂ) / (descendCosetCount p N : ℂ) with hc_def
  let Φ : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k :=
    descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod
  have hΦ_char : Φ ∈ cuspFormCharSpace k χ' :=
    descendSlashSumCuspForm_mem_charSpace χ f p hp hpN χ' hχ_eq hfχ_mod
  refine ⟨c • Φ, Submodule.smul_mem _ c hΦ_char, fun m hm_cop ↦ ?_⟩
  rw [show (ModularFormClass.qExpansion (1 : ℝ) ⇑(c • Φ)).coeff m =
        c * (ModularFormClass.qExpansion (1 : ℝ) Φ).coeff m from
      qExpansion_smul_cuspForm_coeff_aux c Φ m]
  haveI : NeZero (l' * (N / p)) := ⟨Nat.mul_ne_zero hl'_pos.ne' (NeZero.ne _)⟩
  obtain ⟨_χ_low, g_low, _hg_low_χ, hg_low_qexp, hg_low_full_qexp⟩ :=
    miyake_V_p_descend_identity_with_char χ f hfχ p hp hpN l' hl'_pos hl'_sqfree hpl'
      hl'_dvd hp_not_in h_vanish
  rw [Φ_qExp_coeff_eq_count_div_p_mul_g_low_coeff χ f hfχ p hp hpN χ' hχ_eq hfχ_mod
      hl'_pos hl'_sqfree hpl' hl'_dvd hp_not_in h_vanish g_low hg_low_qexp
      hg_low_full_qexp m hm_cop,
    show (ModularFormClass.qExpansion (1 : ℝ) f).coeff (p * m) =
      (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m by
        have := hg_low_qexp (p * m) (dvd_mul_right p m)
          (Nat.coprime_mul_iff_left.mpr ⟨hpl', hm_cop⟩)
        rwa [Nat.mul_div_cancel_left m hp.pos] at this, hc_def]
  have : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have : (descendCosetCount p N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr h_cnt_pos.ne'
  field_simp

/-- **M8: Inductive step for Miyake 4.6.8.** For `f ∈ S_k(Γ_1(N), χ)` with
coprime-vanishing on the prime-subset `S` and `p ∈ S`, there exists
`f_p ∈ qSupportedOnDvdSubmodule N k p ∩ cuspFormCharSpace` such that
`f - f_p` has coprime-vanishing on `S.erase p`. -/
theorem miyake_4_6_8_inductive_step
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (S.prod id) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    {p : ℕ} (hp_in : p ∈ S)
    [hNp_NeZero : NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap
      (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors (hS hp_in))))) :
    ∃ f_p : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f_p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p ∧
      f_p ∈ cuspFormCharSpace k χ ∧
      ∀ n : ℕ, Nat.Coprime n ((S.erase p).prod id) →
        (ModularFormClass.qExpansion (1 : ℝ) (f - f_p)).coeff n = 0 := by
  set l' := (S.erase p).prod id with hl'_def
  have h_prod_eq : S.prod id = p * l' := by
    rw [hl'_def, ← Finset.mul_prod_erase S id hp_in]
    simp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (hS hp_in)
  have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors (hS hp_in)
  have h_vanish' : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0 :=
    fun n hn ↦ h_vanish n (h_prod_eq ▸ hn)
  haveI hp_NeZero : NeZero p := ⟨hp_prime.ne_zero⟩
  have hl'_pos : 0 < l' :=
    Finset.prod_pos fun q hq ↦
      (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))).pos
  have hpl' : Nat.Coprime p l' :=
    Nat.Coprime.prod_right fun q hq ↦ (Nat.coprime_primes hp_prime
      (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq)))).mpr
      (Finset.ne_of_mem_erase hq).symm
  have hl'_sqfree : Squarefree l' := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun q₁ hq₁ q₂ hq₂ hne ↦ ?_)
      fun q hq ↦
        (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))).squarefree
    have hq₁_prime : q₁.Prime :=
      Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq₁))
    have hq₂_prime : q₂.Prime :=
      Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq₂))
    show IsRelPrime (id q₁) (id q₂)
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes hq₁_prime hq₂_prime).mpr hne
  have hl'_dvd_N : l' ∣ N :=
    Finset.prod_primes_dvd N
      (fun _ hq ↦ (Nat.prime_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))).prime)
      fun _ hq ↦ Nat.dvd_of_mem_primeFactors (hS (Finset.mem_of_mem_erase hq))
  have hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors :=
    fun _ hq ↦ Nat.primeFactors_mono hl'_dvd_N (NeZero.ne N) hq
  have hp_not_in_l' : p ∉ l'.primeFactors := fun hp_in_l' ↦
    (hp_prime.coprime_iff_not_dvd.mp hpl') (Nat.dvd_of_mem_primeFactors hp_in_l')
  obtain ⟨f_lower, hf_lower_char, hf_lower_qexp⟩ :=
    miyake_descent_witness_exists χ f hfχ p hp_prime hpN χ' hχ_eq l' hl'_pos
      hl'_sqfree hpl' hl'_dvd hp_not_in_l' h_vanish'
  have h_lift : p * (N / p) = N := Nat.mul_div_cancel' hpN
  let f_p : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower
  have h_M8_construct :
      ∃ f_p : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
        f_p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p ∧
        f_p ∈ cuspFormCharSpace k χ ∧
        ∀ n : ℕ, Nat.Coprime n l' →
          (ModularFormClass.qExpansion (1 : ℝ) f_p).coeff n =
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n := by
    refine ⟨f_p, ?_, ?_, ?_⟩
    · exact HeckeRing.GL2.AtkinLehner.range_castLevelRaise_le_qSupportedOnDvdSubmodule
        hpN k ⟨f_lower, rfl⟩
    · have h_lr_char :
          HeckeRing.GL2.levelRaise (N / p) p k f_lower ∈
            cuspFormCharSpace k (χ'.comp (ZMod.unitsMap (Nat.dvd_mul_left (N / p) p))) :=
        cuspForm_levelRaise_mem_cuspFormCharSpace (N / p) p k χ' hf_lower_char
      show HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower ∈
        cuspFormCharSpace k χ
      rw [HeckeRing.GL2.AtkinLehner.castLevelRaise_apply, hχ_eq]
      have key : ∀ (M : ℕ) [NeZero M] (heq : p * (N / p) = M) (h₁ : (N / p) ∣ M),
          (heq ▸ HeckeRing.GL2.levelRaise (N / p) p k f_lower :
              CuspForm ((Gamma1 M).map (mapGL ℝ)) k) ∈
            cuspFormCharSpace k (χ'.comp (ZMod.unitsMap h₁)) := by
        rintro M _ rfl h₁
        convert h_lr_char using 2
      exact key N h_lift _
    · intro n hn
      show (ModularFormClass.qExpansion (1 : ℝ)
          (HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower)).coeff n = _
      have h_cast_coe :
          (⇑(HeckeRing.GL2.AtkinLehner.castLevelRaise N p hpN k f_lower) :
              UpperHalfPlane → ℂ) =
            ⇑(HeckeRing.GL2.levelRaise (N / p) p k f_lower) := by
        rw [HeckeRing.GL2.AtkinLehner.castLevelRaise_apply]
        have : ∀ {A B : ℕ} (heq : A = B) (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k),
            (⇑(heq ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) :
                UpperHalfPlane → ℂ) = ⇑x := fun heq x ↦ by cases heq; rfl
        exact this h_lift _
      have h_lr_coe : (⇑(HeckeRing.GL2.levelRaise (N / p) p k f_lower) :
              UpperHalfPlane → ℂ) =
            ⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k
                f_lower.toModularForm') := rfl
      rw [qExpansion_ext2 _ _ h_cast_coe, qExpansion_ext2 _ _ h_lr_coe,
        HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff f_lower.toModularForm' n]
      by_cases hpn : p ∣ n
      · rw [if_pos hpn]
        show (ModularFormClass.qExpansion (1 : ℝ) f_lower).coeff (n / p) =
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        rw [hf_lower_qexp (n / p) (hn.coprime_div_left hpn), Nat.mul_div_cancel' hpn]
      · rw [if_neg hpn]
        exact (h_vanish' n (Nat.Coprime.mul_right
          (hp_prime.coprime_iff_not_dvd.mpr hpn).symm hn)).symm
  obtain ⟨f_p, h_supp, h_char, h_qexp_eq⟩ := h_M8_construct
  refine ⟨f_p, h_supp, h_char, fun n hn ↦ ?_⟩
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h_sub : ModularFormClass.qExpansion (1 : ℝ) (f - f_p) =
      ModularFormClass.qExpansion (1 : ℝ) f -
      ModularFormClass.qExpansion (1 : ℝ) f_p := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← qExpansion_neg one_pos h1_period f_p]
    exact qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ)) (h := 1) (a := k) (b := k)
      one_pos h1_period f (- f_p)
  rw [h_sub, map_sub, h_qexp_eq n hn, sub_self]

/-- **M9: The subset-indexed inductive helper for Miyake 4.6.8.**

For `f ∈ S_k(Γ_1(N), χ)` with coprime-vanishing wrt `S.prod id`
(where `S ⊆ N.primeFactors`):
there is a decomposition `f = ∑_{p ∈ S} f_p` with each `f_p` in
`qSupportedOnDvdSubmodule N k p ∩ cuspFormCharSpace`.

Proven by induction on `S.card` using M8 at each step. -/
theorem miyake_4_6_8_subset_helper
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (S.prod id) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    ∃ f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ p ∈ S, f_p p ∧
      (∀ p ∈ S, f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p) ∧
      (∀ p ∈ S, f_p p ∈ cuspFormCharSpace k χ) := by
  induction hSc : S.card generalizing f S with
  | zero =>
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hSc
    subst hS_empty
    refine ⟨fun _ ↦ 0, ?_, ?_, ?_⟩
    · have hf_zero : f = 0 := by
        have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
          rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
            strictPeriods_Gamma1]
          exact ⟨1, by simp⟩
        have h_qExp_zero : ModularFormClass.qExpansion (1 : ℝ) f.toModularForm' = 0 := by
          refine PowerSeries.ext fun n ↦ ?_
          show (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ)
            f.toModularForm') = (PowerSeries.coeff n) (0 : PowerSeries ℂ)
          rw [map_zero]
          exact h_vanish n (by simp [Nat.Coprime, Finset.prod_empty])
        refine DFunLike.coe_injective ?_
        show (⇑f : UpperHalfPlane → ℂ) = 0
        rw [show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl,
          (qExpansion_eq_zero_iff one_pos h1_period f.toModularForm').mp h_qExp_zero]; rfl
      rw [hf_zero, Finset.sum_empty]
    · exact fun p hp ↦ absurd hp (Finset.notMem_empty p)
    · exact fun p hp ↦ absurd hp (Finset.notMem_empty p)
  | succ n ih =>
    have hS_nonempty : S.Nonempty := Finset.card_pos.mp (hSc ▸ Nat.succ_pos n)
    obtain ⟨p, hp_in⟩ := hS_nonempty
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (hS hp_in)
    have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors (hS hp_in)
    haveI hNp_NeZero : NeZero (N / p) := ⟨by
      have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
      exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
    obtain ⟨χ', hχ_eq⟩ := h_chi_factor p (hS hp_in)
    obtain ⟨f_p, h_supp, h_char, h_diff_vanish⟩ :=
      miyake_4_6_8_inductive_step χ S hS f hfχ h_vanish hp_in χ' hχ_eq
    have h_erase_sub : S.erase p ⊆ N.primeFactors := fun q hq ↦
      hS (Finset.mem_of_mem_erase hq)
    have h_erase_card : (S.erase p).card = n := by
      rw [Finset.card_erase_of_mem hp_in, hSc]; lia
    have h_diff_char : f - f_p ∈ cuspFormCharSpace k χ :=
      Submodule.sub_mem _ hfχ h_char
    obtain ⟨f_q, h_sum, h_supp_q, h_char_q⟩ :=
      ih (S.erase p) h_erase_sub (f - f_p) h_diff_char h_diff_vanish
        h_erase_card
    refine ⟨fun q ↦ if q = p then f_p else f_q q, ?_, ?_, ?_⟩
    · have h_split : ∑ q ∈ S, (if q = p then f_p else f_q q) =
          f_p + ∑ q ∈ S.erase p, f_q q := by
        rw [← Finset.sum_erase_add _ _ hp_in, add_comm]
        congr 1
        · simp
        · refine Finset.sum_congr rfl ?_
          intro q hq
          have hq_ne_p : q ≠ p := Finset.ne_of_mem_erase hq
          simp [hq_ne_p]
      rw [h_split, ← h_sum]
      abel
    · intro q hq
      by_cases hqp : q = p
      · subst hqp
        simpa only [if_true] using h_supp
      · simp only [hqp, if_false]
        exact h_supp_q q (Finset.mem_erase.mpr ⟨hqp, hq⟩)
    · intro q hq
      by_cases hqp : q = p
      · subst hqp
        simpa only [if_true] using h_char
      · simp only [hqp, if_false]
        exact h_char_q q (Finset.mem_erase.mpr ⟨hqp, hq⟩)

end HeckeRing.GL2
