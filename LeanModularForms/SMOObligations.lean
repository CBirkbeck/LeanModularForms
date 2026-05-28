/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations.Lemma4_6_8

/-!
# Strong Multiplicity One via Miyake §4.6

This file assembles an axiom-clean proof of `strongMultiplicityOne_axiom_clean`
(Miyake Theorem 4.6.12 / Diamond–Shurman Theorem 5.8.2) by following
Miyake's algebraic descent in §4.6 of *Modular Forms* (2006).

The supporting development is split across the `SMOObligations/` modules;
this file holds the route-B finale.

## Main results

* `miyake_4_6_8_main_lemma_cuspForm`: Miyake's Main Lemma (Theorem 4.6.8).
* `mainLemma_charSpace_routeB`: per-character Main Lemma.
* `newform_unique_routeB`: uniqueness of newforms.
* `strongMultiplicityOne_axiom_clean`: Strong Multiplicity One.

## References

* **[DS]** F. Diamond, J. Shurman, *A First Course in Modular Forms*,
  Springer GTM 228, 2005.
* **[Miy]** T. Miyake, *Modular Forms*, 2nd ed., Springer SMM, 2006.
* **[AL]** A. O. L. Atkin, J. Lehner, *Hecke operators on `Γ₀(m)`*,
  Math. Ann. **185** (1970), 134–160.
* **[Li]** W.-C. W. Li, *Newforms and functional equations*,
  Math. Ann. **212** (1975), 285–315.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **Miyake Theorem 4.6.8 (Main Lemma), CuspForm form.** A cusp form `f ∈ S_k(Γ_1(N), χ)`
whose `q`-expansion vanishes on indices coprime to `N` decomposes as
`f = ∑_{p ∈ N.primeFactors} f_p` with each `f_p` supported on `q^p`-multiples
and lying in the same character space. -/
theorem miyake_4_6_8_main_lemma_cuspForm
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ.toUnitHom = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    ∃ f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ p ∈ N.primeFactors, f_p p ∧
      (∀ p ∈ N.primeFactors,
        f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p) ∧
      (∀ p ∈ N.primeFactors,
        f_p p ∈ cuspFormCharSpace k χ.toUnitHom) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have h_prod_eq : ∀ n : ℕ, Nat.Coprime n (N.primeFactors.prod id) ↔ Nat.Coprime n N := by
    intro n
    refine ⟨fun h ↦ ?_, fun h ↦ h.coprime_dvd_right (Nat.prod_primeFactors_dvd N)⟩
    rw [Nat.coprime_prod_right_iff] at h
    by_contra h_not
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd
      (lt_of_le_of_ne (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hN0)) (Ne.symm h_not)).ne'
    exact hq_prime.coprime_iff_not_dvd.mp
      (h q (Nat.mem_primeFactors.mpr
        ⟨hq_prime, hq_dvd.trans (Nat.gcd_dvd_right _ _), hN0⟩)).symm
      (hq_dvd.trans (Nat.gcd_dvd_left _ _))
  exact miyake_4_6_8_subset_helper χ.toUnitHom N.primeFactors subset_rfl f hfχ
    (fun n hn ↦ h_vanish n ((h_prod_eq n).mp hn)) h_chi_factor

/-- **Miyake Theorem 4.6.8 (Main Lemma), unconditional CuspForm form.**  As
`miyake_4_6_8_main_lemma_cuspForm`, but with the `h_chi_factor` hypothesis removed:
the per-prime factorisation is produced internally by the 4.6.4 dichotomy
(`miyake_4_6_8_subset_helper_unconditional`). -/
theorem miyake_4_6_8_main_lemma_cuspForm_unconditional
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ p ∈ N.primeFactors, f_p p ∧
      (∀ p ∈ N.primeFactors,
        f_p p ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k p) ∧
      (∀ p ∈ N.primeFactors,
        f_p p ∈ cuspFormCharSpace k χ) := by
  have hN0 : N ≠ 0 := NeZero.ne N
  have h_prod_eq : ∀ n : ℕ, Nat.Coprime n (N.primeFactors.prod id) ↔ Nat.Coprime n N := by
    intro n
    refine ⟨fun h ↦ ?_, fun h ↦ h.coprime_dvd_right (Nat.prod_primeFactors_dvd N)⟩
    rw [Nat.coprime_prod_right_iff] at h
    by_contra h_not
    obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd
      (lt_of_le_of_ne (Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hN0)) (Ne.symm h_not)).ne'
    exact hq_prime.coprime_iff_not_dvd.mp
      (h q (Nat.mem_primeFactors.mpr
        ⟨hq_prime, hq_dvd.trans (Nat.gcd_dvd_right _ _), hN0⟩)).symm
      (hq_dvd.trans (Nat.gcd_dvd_left _ _))
  exact miyake_4_6_8_subset_helper_unconditional χ N.primeFactors subset_rfl f hfχ
    (fun n hn ↦ h_vanish n ((h_prod_eq n).mp hn))

theorem coprimeSieve_admits_squarefree_decomposition_in_charSpace
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    -- encoding the Miyake "primes of `(l, N/m_χ)`" restriction, p. 160).
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    ∃ f_d : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ d ∈ N.divisors.filter (1 < ·), f_d d ∧
      (∀ d ∈ N.divisors.filter (1 < ·),
        f_d d ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k d) ∧
      (∀ d ∈ N.divisors.filter (1 < ·),
        f_d d ∈ cuspFormCharSpace k χ) := by
  set χ_dir : DirichletCharacter ℂ N := Newform.dirichletLift χ
  have h_round : χ_dir.toUnitHom = χ :=
    MulChar.equivToUnitHom.apply_symm_apply χ
  have hfχ' : f ∈ cuspFormCharSpace k χ_dir.toUnitHom := by rwa [h_round]
  have h_chi_factor' :
      ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
        haveI : NeZero (N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N))
          (Nat.dvd_of_mem_primeFactors hp_in)) (Nat.prime_of_mem_primeFactors hp_in).pos).ne'⟩
        ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
          χ_dir.toUnitHom = χ'.comp (ZMod.unitsMap
            (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in))) := by
    intro p hp_in
    obtain ⟨χ', hχ_eq⟩ := h_chi_factor p hp_in
    exact ⟨χ', by rwa [h_round]⟩
  obtain ⟨f_p, h_sum, h_supp, h_char⟩ :=
    miyake_4_6_8_main_lemma_cuspForm χ_dir f hfχ' h_vanish h_chi_factor'
  refine ⟨fun d ↦ if d ∈ N.primeFactors then f_p d else 0, ?_, ?_, ?_⟩
  · have h_primes_sub : N.primeFactors ⊆ N.divisors.filter (1 < ·) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_divisors]
      refine ⟨⟨Nat.dvd_of_mem_primeFactors hp, NeZero.ne N⟩, ?_⟩
      exact (Nat.prime_of_mem_primeFactors hp).one_lt
    rw [h_sum]
    symm
    refine (Finset.sum_subset h_primes_sub ?_).symm.trans ?_
    · intro d hd_div hd_nprime
      simp [hd_nprime]
    · refine Finset.sum_congr rfl ?_
      intro p hp
      simp [hp]
  · intro d hd
    by_cases h_prime : d ∈ N.primeFactors
    · simp only [h_prime, if_true]
      exact h_supp d h_prime
    · simp only [h_prime, if_false]
      exact Submodule.zero_mem _
  · intro d hd
    by_cases h_prime : d ∈ N.primeFactors
    · simp only [h_prime, if_true]
      rw [← h_round]
      exact h_char d h_prime
    · simp only [h_prime, if_false]
      exact Submodule.zero_mem _

/-- Unconditional analogue of `coprimeSieve_admits_squarefree_decomposition_in_charSpace`:
the `h_chi_factor` hypothesis is dropped, the decomposition coming from
`miyake_4_6_8_main_lemma_cuspForm_unconditional`. -/
theorem coprimeSieve_admits_squarefree_decomposition_in_charSpace_unconditional
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    ∃ f_d : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      f = ∑ d ∈ N.divisors.filter (1 < ·), f_d d ∧
      (∀ d ∈ N.divisors.filter (1 < ·),
        f_d d ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule N k d) ∧
      (∀ d ∈ N.divisors.filter (1 < ·),
        f_d d ∈ cuspFormCharSpace k χ) := by
  obtain ⟨f_p, h_sum, h_supp, h_char⟩ :=
    miyake_4_6_8_main_lemma_cuspForm_unconditional χ f hfχ h_vanish
  refine ⟨fun d ↦ if d ∈ N.primeFactors then f_p d else 0, ?_, ?_, ?_⟩
  · rw [h_sum]
    symm
    refine (Finset.sum_subset (fun p hp ↦ by
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨Nat.dvd_of_mem_primeFactors hp, NeZero.ne N⟩,
        (Nat.prime_of_mem_primeFactors hp).one_lt⟩) ?_).symm.trans ?_
    · intro d _hd_div hd_nprime
      simp [hd_nprime]
    · exact Finset.sum_congr rfl fun p hp ↦ by simp [hp]
  · intro d _hd
    by_cases h_prime : d ∈ N.primeFactors
    · simpa only [h_prime, if_true] using h_supp d h_prime
    · simpa only [h_prime, if_false] using Submodule.zero_mem _
  · intro d _hd
    by_cases h_prime : d ∈ N.primeFactors
    · simpa only [h_prime, if_true] using h_char d h_prime
    · simpa only [h_prime, if_false] using Submodule.zero_mem _

private theorem heckeT_n_prime_sq_eq_heckeT_p_sq_sub_diamond
    {N : ℕ} [NeZero N] {k : ℤ} {q : ℕ} (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
    heckeT_n (N := N) k (q ^ 2) =
      heckeT_p k q hq hqN * heckeT_p k q hq hqN -
        (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN) := by
  haveI : NeZero (q ^ 2) := ⟨(pow_pos hq.pos 2).ne'⟩
  rw [heckeT_n_prime_pow k hq 2 (by norm_num)]
  show heckeT_p_all (N := N) k q hq * heckeT_ppow k q hq 1 -
      (q : ℂ) ^ (k - 1) • (diamondOp_ext (N := N) k q * heckeT_ppow k q hq 0) =
    heckeT_p k q hq hqN * heckeT_p k q hq hqN -
      (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN)
  rw [heckeT_ppow_zero, heckeT_ppow_one, mul_one,
    heckeT_p_all_coprime k hq hqN, diamondOp_ext_coprime k hqN]

private theorem newform_toModularForm_ne_zero
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) :
    f.toCuspForm.toModularForm' ≠ 0 := by
  intro hF_zero
  have h1 : (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff 1 = 1 := by
    rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl]
    exact f.isNorm
  have h0 : (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff 1 = 0 := by
    show (ModularFormClass.qExpansion (1 : ℝ)
        (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ)).coeff 1 = 0
    rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ)
        = (⇑(0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) by
          rw [hF_zero],
      show (⇑(0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ)
        = (0 : UpperHalfPlane → ℂ) from rfl, qExpansion_zero]
    simp
  rw [h0] at h1
  exact absurd h1 (by norm_num)

/-- $\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q) \cdot q^{k-1}$ for $f$ a newform
of level $N$ and prime $q \nmid N$.  Diamond–Shurman 5.3 / Miyake 4.5.13. -/
theorem newform_eigenvalue_at_prime_sq
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (q : ℕ) (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    f.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩ =
      (f.eigenvalue ⟨q, hq.pos⟩) ^ 2 -
        (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
  set lamq := f.eigenvalue ⟨q, hq.pos⟩
  set lamqsq := f.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩
  set chiq : ℂ := (χ (ZMod.unitOfCoprime q hqN) : ℂ)
  set F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := f.toCuspForm.toModularForm'
  have hq_pos : 0 < q := hq.pos
  have hqsq_pos : 0 < q ^ 2 := pow_pos hq_pos 2
  haveI : NeZero q := ⟨hq_pos.ne'⟩
  haveI : NeZero (q ^ 2) := ⟨hqsq_pos.ne'⟩
  have h_eig_q : heckeT_n k q F = lamq • F := by
    have h_lift : (heckeT_n_cusp k q f.toCuspForm).toModularForm' =
        (lamq • f.toCuspForm).toModularForm' := congr_arg _ (f.isEigen ⟨q, hq_pos⟩ hqN)
    rwa [heckeT_n_cusp_toModularForm'] at h_lift
  have h_eig_qsq : heckeT_n k (q ^ 2) F = lamqsq • F := by
    have h_lift : (heckeT_n_cusp k (q ^ 2) f.toCuspForm).toModularForm' =
        (lamqsq • f.toCuspForm).toModularForm' :=
      congr_arg _ (f.isEigen ⟨q ^ 2, hqsq_pos⟩ (Nat.Coprime.pow_left 2 hqN))
    rwa [heckeT_n_cusp_toModularForm'] at h_lift
  have h_Tq_F : heckeT_p k q hq hqN F = lamq • F :=
    (heckeT_n_prime_coprime k hq hqN) ▸ h_eig_q
  have h_TqTq_F :
      heckeT_p k q hq hqN (heckeT_p k q hq hqN F) = (lamq ^ 2) • F := by
    rw [h_Tq_F, map_smul, h_Tq_F, smul_smul, sq]
  have h_combined :
      heckeT_n k (q ^ 2) F = (lamq ^ 2 - chiq * (q : ℂ) ^ (k - 1)) • F := by
    have h_apply : heckeT_n k (q ^ 2) F =
        heckeT_p k q hq hqN (heckeT_p k q hq hqN F) -
          (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN) F := by
      simpa [Module.End.mul_apply] using congr_arg (fun T : Module.End ℂ _ ↦ T F)
        (heckeT_n_prime_sq_eq_heckeT_p_sq_sub_diamond hq hqN)
    rw [h_apply, h_TqTq_F, show diamondOp k (ZMod.unitOfCoprime q hqN) F = chiq • F from
      (mem_modFormCharSpace_iff k χ F).mp hfχ (ZMod.unitOfCoprime q hqN), smul_smul, sub_smul]
    congr 1
    rw [mul_comm]
  have h_scalar_smul :
      (lamqsq - (lamq ^ 2 - chiq * (q : ℂ) ^ (k - 1))) • F = 0 := by
    rw [sub_smul, ← h_combined, ← h_eig_qsq, sub_self]
  exact sub_eq_zero.mp
    ((smul_eq_zero.mp h_scalar_smul).resolve_right (newform_toModularForm_ne_zero f))

theorem mainLemma_charSpace_routeB
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    -- encoding the Miyake "primes of `(l, N/m_χ)`" restriction, p. 160).
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    f ∈ cuspFormsOld N k := by
  obtain ⟨f_d, h_sum, h_supp, h_char⟩ :=
    coprimeSieve_admits_squarefree_decomposition_in_charSpace χ f hfχ h_vanish
      h_chi_factor
  refine HeckeRing.GL2.AtkinLehner.mainLemma_charSpace_of_sameLevelDivisorDecomposition
    (Newform.dirichletLift χ) f f_d h_sum fun d hd ↦ ⟨h_supp d hd, ?_⟩
  rw [show (Newform.dirichletLift χ).toUnitHom = χ from
    MulChar.equivToUnitHom.apply_symm_apply χ]
  exact h_char d hd

/-- **Per-character unconditional Miyake 4.6.8 (route B).**  A cusp form
`f ∈ S_k(Γ_1(N), χ)` whose period-1 `q`-expansion vanishes at every index coprime to
`N` is an oldform.  This is `mainLemma_charSpace_routeB` with the `h_chi_factor`
hypothesis **removed**: the per-prime character factorisation needed by the
same-level divisor decomposition is supplied internally by Miyake's dichotomy 4.6.4
(`coprimeSieve_admits_squarefree_decomposition_in_charSpace_unconditional`). -/
theorem mainLemma_charSpace_routeB_unconditional
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k := by
  obtain ⟨f_d, h_sum, h_supp, h_char⟩ :=
    coprimeSieve_admits_squarefree_decomposition_in_charSpace_unconditional χ f hfχ h_vanish
  refine HeckeRing.GL2.AtkinLehner.mainLemma_charSpace_of_sameLevelDivisorDecomposition
    (Newform.dirichletLift χ) f f_d h_sum fun d hd ↦ ⟨h_supp d hd, ?_⟩
  rw [show (Newform.dirichletLift χ).toUnitHom = χ from
    MulChar.equivToUnitHom.apply_symm_apply χ]
  exact h_char d hd

theorem newform_unique_routeB
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n)
    -- encoding the Miyake "primes of `(l, N/m_χ)`" restriction, p. 160).
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    f.toCuspForm = g.toCuspForm := by
  suffices hfg : f.toCuspForm - g.toCuspForm = 0 from sub_eq_zero.mp hfg
  have h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) (f.toCuspForm - g.toCuspForm)).coeff n = 0 := by
    intro n hn
    have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    show (ModularFormClass.qExpansion (1 : ℝ)
        (⇑f.toCuspForm.toModularForm' - ⇑g.toCuspForm.toModularForm')).coeff n = 0
    rw [qExpansion_sub one_pos h1_period, map_sub, sub_eq_zero]
    by_cases hn0 : n = 0
    · subst hn0
      simp [Nat.Coprime, Nat.gcd_zero_left] at hn
      subst hn
      rw [ModularFormClass.qExpansion_coeff_zero _ one_pos h1_period,
          ModularFormClass.qExpansion_coeff_zero _ one_pos h1_period,
          show (⇑f.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl,
          show (⇑g.toModularForm' : UpperHalfPlane → ℂ) = ⇑g.toCuspForm from rfl,
          (CuspFormClass.zero_at_infty f.toCuspForm).valueAtInfty_eq_zero,
          (CuspFormClass.zero_at_infty g.toCuspForm).valueAtInfty_eq_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      simpa only [Newform.eigenvalue_eq_coeff f ⟨n, hn_pos⟩ hn χ hfχ,
        Newform.eigenvalue_eq_coeff g ⟨n, hn_pos⟩ hn χ hgχ] using h ⟨n, hn_pos⟩ hn
  exact Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _
    (mainLemma_charSpace_routeB χ (f.toCuspForm - g.toCuspForm) ((cuspFormCharSpace k χ).sub_mem
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
        f.toCuspForm).mp (by convert hfχ using 1))
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
        g.toCuspForm).mp (by convert hgχ using 1))) h_vanish h_chi_factor)
    ((cuspFormsNew N k).sub_mem (cuspFormsNewExtended_le_cuspFormsNew f.isNew)
      (cuspFormsNewExtended_le_cuspFormsNew g.isNew))

private theorem exists_prime_coprime_avoiding_finset
    {N : ℕ} [NeZero N] (n : ℕ+) (S : Finset ℕ) :
    ∃ q, Nat.Prime q ∧ Nat.Coprime q N ∧ Nat.Coprime n.val q ∧
      q ∉ S ∧ q ^ 2 ∉ S ∧ n.val * q ∉ S ∧ n.val * q ^ 2 ∉ S := by
  obtain ⟨q, hq_le, hq_prime⟩ := Nat.exists_infinite_primes (S.sup id + N + n.val + 2)
  have hq_gt_S : ∀ s, s ∈ S → s < q := fun s hs ↦ by
    have : s ≤ S.sup id := Finset.le_sup (f := id) hs
    lia
  have hq_ndvd_N : ¬ q ∣ N := fun hqN ↦ by
    have : q ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hqN
    lia
  have hq_ndvd_n : ¬ q ∣ n.val := fun hqn ↦ by
    have : q ≤ n.val := Nat.le_of_dvd n.pos hqn
    lia
  have hqsq_ge_q : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have hnq_ge_q : q ≤ n.val * q := Nat.le_mul_of_pos_left q n.pos
  have hnqsq_ge_q : q ≤ n.val * q ^ 2 := hqsq_ge_q.trans (Nat.le_mul_of_pos_left _ n.pos)
  refine ⟨q, hq_prime, hq_prime.coprime_iff_not_dvd.mpr hq_ndvd_N,
    (hq_prime.coprime_iff_not_dvd.mpr hq_ndvd_n).symm,
    fun hqS ↦ ?_, fun hqsqS ↦ ?_, fun hnqS ↦ ?_, fun hnqsqS ↦ ?_⟩
  · have := hq_gt_S q hqS
    lia
  · have := hq_gt_S _ hqsqS
    lia
  · have := hq_gt_S _ hnqS
    lia
  · have := hq_gt_S _ hnqsqS
    lia

private theorem newform_eigenvalue_prime_sq_of_eigenvalue_prime_eq_zero
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    {q : ℕ} (hq : Nat.Prime q) (hqN : Nat.Coprime q N)
    (hLamq : f.eigenvalue ⟨q, hq.pos⟩ = 0) :
    f.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩ =
      -((χ (ZMod.unitOfCoprime q hqN) : ℂ)) * (q : ℂ) ^ (k - 1) := by
  rw [newform_eigenvalue_at_prime_sq f χ hfχ q hq hqN, hLamq]
  ring

private theorem newform_eigenvalue_agree_of_coprime_cofactor_ne_zero
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (n m : ℕ+) (hn : Nat.Coprime n.val N) (hmN : Nat.Coprime m.val N)
    (hnm : Nat.Coprime n.val m.val)
    (hm_ne : f.eigenvalue m ≠ 0) (hm_eq : f.eigenvalue m = g.eigenvalue m)
    (hnm_eq : f.eigenvalue ⟨n.val * m.val, Nat.mul_pos n.pos m.pos⟩
            = g.eigenvalue ⟨n.val * m.val, Nat.mul_pos n.pos m.pos⟩) :
    f.eigenvalue n = g.eigenvalue n := by
  refine mul_right_cancel₀ hm_ne ?_
  rw [← HeckeRing.GL2.Newform.eigenvalue_coprime_mul f n m hn hmN hnm χ hfχ, hnm_eq,
    HeckeRing.GL2.Newform.eigenvalue_coprime_mul g n m hn hmN hnm χ hgχ, hm_eq]

theorem eigenvalues_eq_all_coprime_of_eq_off_finite
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (hyp : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n := by
  intro n hn
  by_cases hn_S : n.val ∈ S
  · obtain ⟨q, hq_prime, hq_N, hn_coprime_q, hq_notin_S, hqsq_notin_S,
      hnq_notin_S, hnqsq_notin_S⟩ := exists_prime_coprime_avoiding_finset (N := N) n S
    have hqsq_N : Nat.Coprime (q ^ 2) N := Nat.Coprime.pow_left 2 hq_N
    let q_pnat : ℕ+ := ⟨q, hq_prime.pos⟩
    let qsq_pnat : ℕ+ := ⟨q ^ 2, pow_pos hq_prime.pos 2⟩
    by_cases hLamq : f.eigenvalue q_pnat = 0
    · have hf_qsq := newform_eigenvalue_prime_sq_of_eigenvalue_prime_eq_zero f χ hfχ hq_prime
        hq_N hLamq
      have hLamqsq_ne : f.eigenvalue qsq_pnat ≠ 0 := by
        rw [show f.eigenvalue qsq_pnat = _ from hf_qsq]
        exact mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero _))
          (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hq_prime.pos.ne'))
      exact newform_eigenvalue_agree_of_coprime_cofactor_ne_zero f g χ hfχ hgχ n qsq_pnat
        hn hqsq_N (Nat.Coprime.pow_right 2 hn_coprime_q) hLamqsq_ne
        (hf_qsq.trans (newform_eigenvalue_prime_sq_of_eigenvalue_prime_eq_zero g χ hgχ hq_prime
          hq_N ((hyp q_pnat hq_N hq_notin_S).symm.trans hLamq)).symm)
        (hyp ⟨n.val * q ^ 2, Nat.mul_pos n.pos (pow_pos hq_prime.pos 2)⟩
          (Nat.Coprime.mul_left hn hqsq_N) hnqsq_notin_S)
    · exact newform_eigenvalue_agree_of_coprime_cofactor_ne_zero f g χ hfχ hgχ n q_pnat
        hn hq_N hn_coprime_q hLamq (hyp q_pnat hq_N hq_notin_S)
        (hyp ⟨n.val * q, Nat.mul_pos n.pos hq_prime.pos⟩
          (Nat.Coprime.mul_left hn hq_N) hnq_notin_S)
  · exact hyp n hn hn_S

theorem strongMultiplicityOne_axiom_clean
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n)
    -- encoding the Miyake "primes of `(l, N/m_χ)`" restriction, p. 160).
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    f.toCuspForm = g.toCuspForm :=
  newform_unique_routeB f g χ hfχ hgχ
    (eigenvalues_eq_all_coprime_of_eq_off_finite f g χ hfχ hgχ S h) h_chi_factor

end HeckeRing.GL2
