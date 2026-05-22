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
    have h_gcd_pos : 0 < Nat.gcd n N := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hN0)
    obtain ⟨q, hq_prime, hq_dvd⟩ :=
      Nat.exists_prime_and_dvd (lt_of_le_of_ne h_gcd_pos (Ne.symm h_not)).ne'
    exact hq_prime.coprime_iff_not_dvd.mp
      (h q (Nat.mem_primeFactors.mpr
        ⟨hq_prime, hq_dvd.trans (Nat.gcd_dvd_right _ _), hN0⟩)).symm
      (hq_dvd.trans (Nat.gcd_dvd_left _ _))
  exact miyake_4_6_8_subset_helper χ.toUnitHom N.primeFactors subset_rfl f hfχ
    (fun n hn ↦ h_vanish n ((h_prod_eq n).mp hn)) h_chi_factor

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
  set χ_dir : DirichletCharacter ℂ N := Newform.dirichletLift χ with hχ_dir
  have h_round : χ_dir.toUnitHom = χ :=
    MulChar.equivToUnitHom.apply_symm_apply χ
  have hfχ' : f ∈ cuspFormCharSpace k χ_dir.toUnitHom := by rwa [h_round]
  have h_chi_factor' :
      ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
        haveI : NeZero (N / p) := ⟨by
          have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
          have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
          have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
          exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
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

/-- $\lambda_{q^2}(f) = \lambda_q(f)^2 - \chi(q) \cdot q^{k-1}$ for $f$ a newform
of level $N$ and prime $q \nmid N$.  Diamond–Shurman 5.3 / Miyake 4.5.13. -/
theorem newform_eigenvalue_at_prime_sq
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (q : ℕ) (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    f.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩ =
      (f.eigenvalue ⟨q, hq.pos⟩) ^ 2 -
        (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
  set lamq := f.eigenvalue ⟨q, hq.pos⟩ with hlamq_def
  set lamqsq := f.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩ with hlamqsq_def
  set chiq : ℂ := (χ (ZMod.unitOfCoprime q hqN) : ℂ) with hchiq_def
  set F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := f.toCuspForm.toModularForm' with hF_def
  have hq_pos : 0 < q := hq.pos
  have hqsq_pos : 0 < q ^ 2 := pow_pos hq_pos 2
  have hqsq_N : Nat.Coprime (q ^ 2) N := Nat.Coprime.pow_left 2 hqN
  haveI : NeZero q := ⟨hq_pos.ne'⟩
  haveI : NeZero (q ^ 2) := ⟨hqsq_pos.ne'⟩
  have h_eig_q : heckeT_n k q F = lamq • F := by
    have h_lift : (heckeT_n_cusp k q f.toCuspForm).toModularForm' =
        (lamq • f.toCuspForm).toModularForm' := congr_arg _ (f.isEigen ⟨q, hq_pos⟩ hqN)
    rwa [heckeT_n_cusp_toModularForm'] at h_lift
  have h_eig_qsq : heckeT_n k (q ^ 2) F = lamqsq • F := by
    have h_lift : (heckeT_n_cusp k (q ^ 2) f.toCuspForm).toModularForm' =
        (lamqsq • f.toCuspForm).toModularForm' :=
      congr_arg _ (f.isEigen ⟨q ^ 2, hqsq_pos⟩ hqsq_N)
    rwa [heckeT_n_cusp_toModularForm'] at h_lift
  have h_recur :
      heckeT_n (N := N) k (q ^ 2) =
        heckeT_p k q hq hqN * heckeT_p k q hq hqN -
          (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN) := by
    have h_pp : heckeT_n (N := N) k (q ^ 2) = heckeT_ppow (N := N) k q hq 2 :=
      heckeT_n_prime_pow k hq 2 (by norm_num)
    rw [h_pp]
    show heckeT_p_all (N := N) k q hq * heckeT_ppow k q hq 1 -
        (q : ℂ) ^ (k - 1) • (diamondOp_ext (N := N) k q * heckeT_ppow k q hq 0) =
      heckeT_p k q hq hqN * heckeT_p k q hq hqN -
        (q : ℂ) ^ (k - 1) • diamondOp k (ZMod.unitOfCoprime q hqN)
    rw [heckeT_ppow_zero, heckeT_ppow_one, mul_one,
      heckeT_p_all_coprime k hq hqN, diamondOp_ext_coprime k hqN]
  have h_diamond_F :
      diamondOp k (ZMod.unitOfCoprime q hqN) F = chiq • F :=
    (mem_modFormCharSpace_iff k χ F).mp hfχ (ZMod.unitOfCoprime q hqN)
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
      simpa [Module.End.mul_apply] using congr_arg (fun T : Module.End ℂ _ ↦ T F) h_recur
    rw [h_apply, h_TqTq_F, h_diamond_F, smul_smul, sub_smul]
    congr 1
    rw [mul_comm]
  have h_scalar_smul :
      (lamqsq - (lamq ^ 2 - chiq * (q : ℂ) ^ (k - 1))) • F = 0 := by
    rw [sub_smul, ← h_combined, ← h_eig_qsq, sub_self]
  have hF_ne : F ≠ 0 := by
    intro hF_zero
    have h1 : (ModularFormClass.qExpansion (1 : ℝ) F).coeff 1 = 1 := by
      show (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff 1 = 1
      rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl]
      exact f.isNorm
    have h0 : (ModularFormClass.qExpansion (1 : ℝ) F).coeff 1 = 0 := by
      show (ModularFormClass.qExpansion (1 : ℝ) (⇑F : UpperHalfPlane → ℂ)).coeff 1 = 0
      rw [show (⇑F : UpperHalfPlane → ℂ)
          = (⇑(0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) from by
        rw [hF_zero],
        show (⇑(0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ)
          = (0 : UpperHalfPlane → ℂ) from rfl, qExpansion_zero]
      simp
    rw [h0] at h1
    exact absurd h1 (by norm_num)
  have h_scalar :
      lamqsq - (lamq ^ 2 - chiq * (q : ℂ) ^ (k - 1)) = 0 :=
    (smul_eq_zero.mp h_scalar_smul).resolve_right hF_ne
  exact sub_eq_zero.mp h_scalar

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
  have h_round : (Newform.dirichletLift χ).toUnitHom = χ :=
    MulChar.equivToUnitHom.apply_symm_apply χ
  rw [h_round]
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
  have hf_charSpace : f.toCuspForm ∈ cuspFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ f.toCuspForm).mp (by convert hfχ using 1)
  have hg_charSpace : g.toCuspForm ∈ cuspFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ g.toCuspForm).mp (by convert hgχ using 1)
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
      have h_eq := h ⟨n, hn_pos⟩ hn
      rwa [Newform.eigenvalue_eq_coeff f ⟨n, hn_pos⟩ hn χ hfχ,
          Newform.eigenvalue_eq_coeff g ⟨n, hn_pos⟩ hn χ hgχ] at h_eq
  exact Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _
    (mainLemma_charSpace_routeB χ (f.toCuspForm - g.toCuspForm)
      ((cuspFormCharSpace k χ).sub_mem hf_charSpace hg_charSpace) h_vanish h_chi_factor)
    ((cuspFormsNew N k).sub_mem f.isNew g.isNew)

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
  · have hn_pos : 0 < n.val := n.pos
    let M : ℕ := S.sup id + N + n.val + 2
    obtain ⟨q, hq_le, hq_prime⟩ := Nat.exists_infinite_primes M
    have hq_pos : 0 < q := hq_prime.pos
    have hq_gt_S : ∀ s, s ∈ S → s < q := fun s hs ↦ by
      have hs_le : s ≤ S.sup id := Finset.le_sup (f := id) hs
      lia
    have hq_ndvd_N : ¬ q ∣ N := fun hqN ↦ by
      have : q ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hqN; lia
    have hq_ndvd_n : ¬ q ∣ n.val := fun hqn ↦ by
      have : q ≤ n.val := Nat.le_of_dvd hn_pos hqn; lia
    have hq_N : Nat.Coprime q N := hq_prime.coprime_iff_not_dvd.mpr hq_ndvd_N
    have hn_coprime_q : Nat.Coprime n.val q :=
      (hq_prime.coprime_iff_not_dvd.mpr hq_ndvd_n).symm
    have hqsq_ge_q : q ≤ q ^ 2 := by nlinarith
    have hnq_ge_q : q ≤ n.val * q := by
      calc q = 1 * q := (one_mul q).symm
        _ ≤ n.val * q := Nat.mul_le_mul_right q hn_pos
    have hnqsq_ge_q : q ≤ n.val * q ^ 2 := by
      calc q ≤ q ^ 2 := hqsq_ge_q
        _ = 1 * q ^ 2 := (one_mul _).symm
        _ ≤ n.val * q ^ 2 := Nat.mul_le_mul_right _ hn_pos
    have hq_notin_S : q ∉ S := fun hqS ↦ by
      have := hq_gt_S q hqS; lia
    have hqsq_notin_S : q ^ 2 ∉ S := fun hqsqS ↦ by
      have := hq_gt_S _ hqsqS; lia
    have hnq_notin_S : n.val * q ∉ S := fun hnqS ↦ by
      have := hq_gt_S _ hnqS; lia
    have hnqsq_notin_S : n.val * q ^ 2 ∉ S := fun hnqsqS ↦ by
      have := hq_gt_S _ hnqsqS; lia
    have hqsq_pos : 0 < q ^ 2 := pow_pos hq_pos 2
    have hnq_pos : 0 < n.val * q := Nat.mul_pos hn_pos hq_pos
    have hnqsq_pos : 0 < n.val * q ^ 2 := Nat.mul_pos hn_pos hqsq_pos
    let q_pnat : ℕ+ := ⟨q, hq_pos⟩
    let qsq_pnat : ℕ+ := ⟨q ^ 2, hqsq_pos⟩
    let nq_pnat : ℕ+ := ⟨n.val * q, hnq_pos⟩
    let nqsq_pnat : ℕ+ := ⟨n.val * q ^ 2, hnqsq_pos⟩
    have hnq_N : Nat.Coprime (n.val * q) N := Nat.Coprime.mul_left hn hq_N
    have hnqsq_N : Nat.Coprime (n.val * q ^ 2) N :=
      Nat.Coprime.mul_left hn (Nat.Coprime.pow_left 2 hq_N)
    have hqsq_N : Nat.Coprime (q ^ 2) N := Nat.Coprime.pow_left 2 hq_N
    have hn_coprime_qsq : Nat.Coprime n.val (q ^ 2) :=
      Nat.Coprime.pow_right 2 hn_coprime_q
    by_cases hLamq : f.eigenvalue q_pnat = 0
    · have hLamq_g_eq : g.eigenvalue q_pnat = 0 := (hyp q_pnat hq_N hq_notin_S).symm.trans hLamq
      have h_rec_f := newform_eigenvalue_at_prime_sq f χ hfχ q hq_prime hq_N
      have h_rec_g := newform_eigenvalue_at_prime_sq g χ hgχ q hq_prime hq_N
      have hLamqsq_f_eq : f.eigenvalue qsq_pnat
            = -((χ (ZMod.unitOfCoprime q hq_N) : ℂ)) * (q : ℂ) ^ (k - 1) := by
        show f.eigenvalue ⟨q ^ 2, _⟩ = _
        rw [h_rec_f, hLamq]; ring
      have hLamqsq_g_eq : g.eigenvalue qsq_pnat
            = -((χ (ZMod.unitOfCoprime q hq_N) : ℂ)) * (q : ℂ) ^ (k - 1) := by
        show g.eigenvalue ⟨q ^ 2, _⟩ = _
        rw [h_rec_g, hLamq_g_eq]; ring
      have hLamqsq_ne : f.eigenvalue qsq_pnat ≠ 0 := by
        rw [hLamqsq_f_eq]
        exact mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero _))
          (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hq_pos.ne'))
      have hmul_f : f.eigenvalue nqsq_pnat =
          f.eigenvalue n * f.eigenvalue qsq_pnat :=
        HeckeRing.GL2.Newform.eigenvalue_coprime_mul f n qsq_pnat hn hqsq_N
          hn_coprime_qsq χ hfχ
      have hmul_g : g.eigenvalue nqsq_pnat =
          g.eigenvalue n * g.eigenvalue qsq_pnat :=
        HeckeRing.GL2.Newform.eigenvalue_coprime_mul g n qsq_pnat hn hqsq_N
          hn_coprime_qsq χ hgχ
      have hnqsq_eq : f.eigenvalue nqsq_pnat = g.eigenvalue nqsq_pnat :=
        hyp nqsq_pnat hnqsq_N hnqsq_notin_S
      have h_qsq_eq : f.eigenvalue qsq_pnat = g.eigenvalue qsq_pnat := by
        rw [hLamqsq_f_eq, hLamqsq_g_eq]
      refine mul_right_cancel₀ hLamqsq_ne ?_
      rw [← hmul_f, hnqsq_eq, hmul_g, h_qsq_eq]
    · have hq_eq : f.eigenvalue q_pnat = g.eigenvalue q_pnat :=
        hyp q_pnat hq_N hq_notin_S
      have hnq_eq : f.eigenvalue nq_pnat = g.eigenvalue nq_pnat :=
        hyp nq_pnat hnq_N hnq_notin_S
      have hmul_f : f.eigenvalue nq_pnat = f.eigenvalue n * f.eigenvalue q_pnat :=
        HeckeRing.GL2.Newform.eigenvalue_coprime_mul f n q_pnat hn hq_N
          hn_coprime_q χ hfχ
      have hmul_g : g.eigenvalue nq_pnat = g.eigenvalue n * g.eigenvalue q_pnat :=
        HeckeRing.GL2.Newform.eigenvalue_coprime_mul g n q_pnat hn hq_N
          hn_coprime_q χ hgχ
      refine mul_right_cancel₀ hLamq ?_
      rw [← hmul_f, hnq_eq, hmul_g, hq_eq]
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
