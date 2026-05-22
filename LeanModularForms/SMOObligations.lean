/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.Eigenforms.AtkinLehner
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.Eigenforms.MainLemma
import LeanModularForms.HeckeRIngs.GL2.Newforms
import LeanModularForms.HeckeRIngs.GL2.Prop334_HeckeSlash

/-!
# Strong Multiplicity One via Miyake §4.6

This file assembles an axiom-clean proof of `strongMultiplicityOne_axiom_clean`
(Miyake Theorem 4.6.12 / Diamond–Shurman Theorem 5.8.2) by following
Miyake's algebraic descent in §4.6 of *Modular Forms* (2006).

## Main results

* `miyake_4_6_5_coprime_filter_cuspForm`: Miyake Lemma 4.6.5, single-prime case.
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

/-- CuspForm-level subgroup-restriction preserves the Nebentypus
character space (with the natural pullback of `χ` along the unit map).

Derived from `restrictSubgroup_mem_modFormCharSpace` (ModularForm
version) via the CuspForm ↔ ModularForm character-space iff. -/
private lemma cuspForm_restrictSubgroup_mem_cuspFormCharSpace
    {M N : ℕ} [NeZero M] [NeZero N] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ) (h : M ∣ N)
    {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd h) f ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap h)) := by
  rw [← cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace,
    show cuspFormToModularForm
          (CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd h) f) =
        ModularForm.restrictSubgroup (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd h)
          (cuspFormToModularForm f) from ModularForm.ext fun _ => rfl]
  exact HeckeRing.GL2.MainLemma.restrictSubgroup_mem_modFormCharSpace χ h _
    ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ f).mpr hf)

/-- CuspForm-level `V_p` (`levelRaise`) preserves the Nebentypus
character space, with the lifted character on the higher level.

Derived from `modularFormLevelRaise_mem_modFormCharSpace` via the
CuspForm ↔ ModularForm character-space iff. -/
private lemma cuspForm_levelRaise_mem_cuspFormCharSpace
    (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) (χ : (ZMod M)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    HeckeRing.GL2.levelRaise M d k f ∈
      cuspFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) := by
  rw [← cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace,
    show cuspFormToModularForm (HeckeRing.GL2.levelRaise M d k f) =
        HeckeRing.GL2.modularFormLevelRaise M d k (cuspFormToModularForm f)
      from ModularForm.ext fun _ => rfl]
  exact HeckeRing.GL2.MainLemma.modularFormLevelRaise_mem_modFormCharSpace M d k χ
    ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ f).mpr hf)

/-- Bad-prime variant of `heckeT_n_cusp_preserves_cuspFormCharSpace`:
for prime `p ∣ N`, the operator `heckeT_n_cusp k p` (which equals
`heckeT_p_divN` at the function level) preserves the cusp-form
character space `cuspFormCharSpace k χ`. -/
private lemma heckeT_n_cusp_preserves_cuspFormCharSpace_divN
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeT_n_cusp k p f ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff] at hf ⊢
  intro d
  have hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ := by
    rw [mem_modFormCharSpace_iff]
    intro d'
    refine ModularForm.ext fun τ => ?_
    show ((diamondOp k d') f.toModularForm').toFun τ = ↑(χ d') • f.toModularForm'.toFun τ
    exact congr_arg (fun (g : CuspForm _ k) => g.toFun τ) (hf d')
  have h_diamond := ((mem_modFormCharSpace_iff k χ _).mp
    (HeckeRing.GL2.MainLemma.heckeT_p_divN_preserves_modFormCharSpace hp hpN χ hfχ_mod)) d
  refine CuspForm.ext fun τ => ?_
  show ((diamondOp k d) (heckeT_n k p f.toModularForm')).toFun τ =
    ↑(χ d) • (heckeT_n k p f.toModularForm').toFun τ
  rw [show heckeT_n k p = HeckeRing.GL2.heckeT_p_divN k p hp hpN by
    rw [heckeT_n_prime k hp]; exact dif_neg hpN]
  exact congr_arg (fun (m : ModularForm _ k) => m.toFun τ) h_diamond

/-- **Single-prime case of Miyake 4.6.5** (helper for the general `L` case).

For a prime `p ∣ N`, the coprime-to-`p` filter is
`g = f − V_p(U_p f) ∈ M_k(Γ_1(p·N), χ_lifted)`.  See the section
docstring above for the construction recipe.

**Construction (CuspForm level)**:
```
U_p f := heckeT_n_cusp k p f                  -- CuspForm Γ_1(N)
V_p (U_p f) := levelRaise N p k (U_p f)       -- CuspForm Γ_1(p · N)
f_at_pN := CuspForm.restrictSubgroup _ f      -- CuspForm Γ_1(p · N)
g := f_at_pN - V_p (U_p f)                    -- CuspForm Γ_1(p · N)
```

Character preservation uses the bad-prime `heckeT_n_cusp` preservation
helper above plus the project's existing
`levelRaise_mem_cuspFormCharSpace` and a CuspForm restriction lemma. -/
private theorem miyake_4_6_5_single_prime_dvd_N
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    let M := p * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N p
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
        if ¬ p ∣ n then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  haveI : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
  have hNM : N ∣ p * N := Nat.dvd_mul_left N p
  let f_res : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hNM) f
  let V_p_U_p_f : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    HeckeRing.GL2.levelRaise N p k (heckeT_n_cusp k p f)
  refine ⟨f_res - V_p_U_p_f, Submodule.sub_mem _
    (cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM hfχ)
    (cuspForm_levelRaise_mem_cuspFormCharSpace N p k χ
      (heckeT_n_cusp_preserves_cuspFormCharSpace_divN hp hpN χ hfχ)), ?_⟩
  intro n
  have h1_period : (1 : ℝ) ∈ ((Gamma1 (p * N)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (p * N)).map (mapGL ℝ) =
        (Gamma1 (p * N) : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h_VUp_fun :
      (⇑V_p_U_p_f : UpperHalfPlane → ℂ) =
        ⇑(HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hpN f.toModularForm') := by
    show (HeckeRing.GL2.modularFormLevelRaise N p k
        (heckeT_n k p f.toModularForm')).toFun = _
    rw [show heckeT_n k p = HeckeRing.GL2.heckeT_p_divN k p hp hpN by
      rw [heckeT_n_prime k hp]; exact dif_neg hpN]
    rfl
  have h_coe_sub : (⇑(f_res - V_p_U_p_f) : UpperHalfPlane → ℂ) =
      ⇑f - ⇑(HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hpN f.toModularForm') := by
    show (⇑f_res - ⇑V_p_U_p_f : UpperHalfPlane → ℂ) = _
    rw [h_VUp_fun]; rfl
  show (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ)
    (⇑(f_res - V_p_U_p_f))) = _
  rw [h_coe_sub]
  set raised : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hpN f.toModularForm'
  set f_pN : ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    ModularForm.restrictSubgroup (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hNM)
      f.toModularForm'
  rw [show (⇑f - ⇑raised : UpperHalfPlane → ℂ) = ⇑(f_pN - raised) from rfl,
    show ModularFormClass.qExpansion (1 : ℝ) (⇑(f_pN - raised)) =
      ModularFormClass.qExpansion (1 : ℝ) (f_pN - raised) from rfl,
    qExpansion_sub one_pos h1_period f_pN raised, map_sub,
    HeckeRing.GL2.AtkinLehner.qExpansion_one_pSupportedRaise_coeff hp hpN
      f.toModularForm' n]
  have h_toMF : (⇑f.toModularForm' : UpperHalfPlane → ℂ) = ⇑f := rfl
  by_cases hpn : p ∣ n <;> simp [hpn, f_pN, h_toMF]

/-- The single-prime case of Miyake 4.6.5 exposed as a public lemma, in the
form `miyake_4_6_8_main_lemma_cuspForm` needs.  The general `L` case
(iterating over primes of `L`) reduces to this by induction on
`L.primeFactors.card` and is omitted here; only the single-prime case is
on the SMO critical path. -/
theorem miyake_4_6_5_coprime_filter_cuspForm
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    let M := p * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N p
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
        if ¬ p ∣ n then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 :=
  miyake_4_6_5_single_prime_dvd_N χ f hfχ p hp hpN

/-- **T1a: Generalized inductive helper for M1.**

The induction in M1's proof varies the level (`M → q·M`) and the
character (`χ_M → χ_M ∘ unitsMap`) at each step.  This helper is
parameterised by `(M, χ_M)` and the induction parameter is `S.card`
where `S ⊆ M.primeFactors`.

* **Base** `S = ∅`: `g := f`, `M' := M`, trivial.
* **Step**: pick `q ∈ S`, apply `miyake_4_6_5_single_prime_dvd_N` at
  level `M` with `q` to get `h` at level `q·M` with q-coprime filter,
  recurse with `(q·M, χ_M.comp ..., S.erase q)`.

Strong induction on `S.card`. -/
private theorem miyake_4_6_5_iterated_helper
    (n_iter : ℕ) :
    ∀ {M : ℕ} [NeZero M] {k : ℤ}
      (χ_M : (ZMod M)ˣ →* ℂˣ)
      (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
      (_ : g ∈ cuspFormCharSpace k χ_M)
      (S : Finset ℕ) (_ : S ⊆ M.primeFactors)
      (_ : S.card = n_iter)
      (_ : Squarefree (S.prod id)),
      ∃ (M' : ℕ) (_ : NeZero M') (hMM' : M ∣ M') (_ : M' = M * S.prod id)
        (g' : CuspForm ((Gamma1 M').map (mapGL ℝ)) k),
        g' ∈ cuspFormCharSpace k (χ_M.comp (ZMod.unitsMap hMM')) ∧
        ∀ n : ℕ,
          (ModularFormClass.qExpansion (1 : ℝ) g').coeff n =
          if Nat.Coprime n (S.prod id) then
            (ModularFormClass.qExpansion (1 : ℝ) g).coeff n
          else 0 := by
  induction n_iter with
  | zero =>
    intro M _ k χ_M g hgχ S hS_sub hS_card _
    obtain rfl := Finset.card_eq_zero.mp hS_card
    refine ⟨M, ‹NeZero M›, dvd_refl M, by simp, g, ?_, fun _ ↦ by
      simp [Nat.Coprime, Finset.prod_empty]⟩
    simpa [ZMod.unitsMap] using hgχ
  | succ k ih =>
    intro M _ k_int χ_M g hgχ S hS_sub hS_card hS_sqfree
    obtain ⟨q, hq_in⟩ := Finset.card_pos.mp (by lia : 0 < S.card)
    have hq_prime_factor : q ∈ M.primeFactors := hS_sub hq_in
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_prime_factor
    have hq_dvd_M : q ∣ M := Nat.dvd_of_mem_primeFactors hq_prime_factor
    haveI : NeZero q := ⟨hq_prime.ne_zero⟩
    have hq_not_coprime : ¬ Nat.Coprime q M := fun h ↦
      hq_prime.coprime_iff_not_dvd.mp h hq_dvd_M
    obtain ⟨g_step, hg_step_χ, hg_step_qexp⟩ :=
      miyake_4_6_5_single_prime_dvd_N χ_M g hgχ q hq_prime hq_not_coprime
    haveI hqM_NeZero : NeZero (q * M) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M)⟩
    have hM_dvd_qM : M ∣ q * M := Nat.dvd_mul_left M q
    have hS_erase_sub : S.erase q ⊆ (q * M).primeFactors := by
      intro r hr
      have hr_in_M : r ∈ M.primeFactors := hS_sub (Finset.mem_of_mem_erase hr)
      rw [Nat.mem_primeFactors] at hr_in_M ⊢
      exact ⟨hr_in_M.1, hr_in_M.2.1.mul_left q, NeZero.ne _⟩
    have hS_erase_card : (S.erase q).card = k := by
      rw [Finset.card_erase_of_mem hq_in, hS_card]; lia
    have h_prod_eq : S.prod id = q * (S.erase q).prod id := by
      rw [← Finset.mul_prod_erase _ _ hq_in]; rfl
    have hS_erase_sqfree : Squarefree ((S.erase q).prod id) := by
      rw [h_prod_eq] at hS_sqfree
      exact hS_sqfree.of_mul_right
    obtain ⟨M', hM'_NeZero, hqM_dvd_M', hM'_eq, g', hg'_χ, hg'_qexp⟩ :=
      ih (χ_M.comp (ZMod.unitsMap hM_dvd_qM)) g_step hg_step_χ
        (S.erase q) hS_erase_sub hS_erase_card hS_erase_sqfree
    refine ⟨M', hM'_NeZero, dvd_trans hM_dvd_qM hqM_dvd_M',
        by rw [hM'_eq, h_prod_eq]; ring, g', ?_, ?_⟩
    · rw [show χ_M.comp (ZMod.unitsMap (dvd_trans hM_dvd_qM hqM_dvd_M')) =
          (χ_M.comp (ZMod.unitsMap hM_dvd_qM)).comp (ZMod.unitsMap hqM_dvd_M') by
        rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]]
      exact hg'_χ
    · intro n
      rw [hg'_qexp n, hg_step_qexp n, h_prod_eq]
      have h_cop_q : Nat.Coprime n q ↔ ¬ q ∣ n :=
        ⟨fun h ↦ hq_prime.coprime_iff_not_dvd.mp h.symm,
         fun h ↦ (hq_prime.coprime_iff_not_dvd.mpr h).symm⟩
      have h_cop_split : Nat.Coprime n (q * (S.erase q).prod id) ↔
          (¬ q ∣ n) ∧ Nat.Coprime n ((S.erase q).prod id) := by
        rw [Nat.coprime_mul_iff_right]
        exact and_congr_left fun _ ↦ h_cop_q
      simp only [h_cop_split]
      split_ifs with h1 h2 <;> simp_all

/-- **M1: Iterated single-prime coprime filter.**

For `f ∈ S_k(Γ_1(N), χ)` and `L ∣ N` squarefree, there is a form `g`
at level `Γ_1(L · N)` (one factor of each prime of `L` added) with
`q`-expansion `aₙ(g) = aₙ(f) · [(n, L) = 1]`. -/
theorem miyake_4_6_5_iterated_L
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (L : ℕ) (hL_pos : 0 < L) (hL_sqfree : Squarefree L)
    (hL_dvd : ∀ p ∈ L.primeFactors, p ∈ N.primeFactors) :
    let M := L * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hL_pos) (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N L
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n L then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  have hS_prod : L.primeFactors.prod id = L := by
    simp [Nat.prod_primeFactors_of_squarefree hL_sqfree]
  have hS_sqfree : Squarefree (L.primeFactors.prod id) := hS_prod.symm ▸ hL_sqfree
  obtain ⟨M', hM'_NeZero, hNM', hM'_eq, g', hg'_χ, hg'_qexp⟩ :=
    miyake_4_6_5_iterated_helper L.primeFactors.card χ f hfχ
      L.primeFactors hL_dvd rfl hS_sqfree
  have hM'_eq_LN : M' = L * N := by rw [hM'_eq, hS_prod, mul_comm]
  subst hM'_eq_LN
  refine ⟨g', by convert hg'_χ using 2, fun n ↦ ?_⟩
  have h := hg'_qexp n
  rwa [hS_prod] at h

private theorem miyake_4_6_5_single_prime_coprime_to_N
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) :
    let M := N * p ^ 2
    haveI : NeZero M :=
      ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hp.ne_zero)⟩
    have hNM : N ∣ M := Nat.dvd_mul_right N (p ^ 2)
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
        if ¬ p ∣ n then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  haveI hM_NeZero : NeZero (N * p ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hp.ne_zero)⟩
  have hN_dvd_pN : N ∣ p * N := Nat.dvd_mul_left N p
  haveI hpN_NeZero : NeZero (p * N) := ⟨Nat.mul_ne_zero hp.ne_zero (NeZero.ne N)⟩
  have hp_not_coprime_pN : ¬ Nat.Coprime p (p * N) := fun h ↦
    hp.coprime_iff_not_dvd.mp h (Nat.dvd_mul_right p N)
  have hM_eq' : p * (p * N) = N * p ^ 2 := by ring
  haveI hppN_NeZero : NeZero (p * (p * N)) := ⟨by rw [hM_eq']; exact hM_NeZero.ne⟩
  have hN_dvd_ppN : N ∣ p * (p * N) := by rw [hM_eq']; exact Nat.dvd_mul_right N (p ^ 2)
  let f_pN : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hN_dvd_pN) f
  let f_ppN : CuspForm ((Gamma1 (p * (p * N))).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hN_dvd_ppN) f
  let raised : ModularForm ((Gamma1 (p * (p * N))).map (mapGL ℝ)) k :=
    HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hp_not_coprime_pN
      f_pN.toModularForm'
  let U_p_f_pN : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
    heckeT_n_cusp k p f_pN
  let V_p_U_p_f_pN : CuspForm ((Gamma1 (p * (p * N))).map (mapGL ℝ)) k :=
    HeckeRing.GL2.levelRaise (p * N) p k U_p_f_pN
  let g_ppN : CuspForm ((Gamma1 (p * (p * N))).map (mapGL ℝ)) k :=
    f_ppN - V_p_U_p_f_pN
  have h_f_ppN_χ : f_ppN ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hN_dvd_ppN)) :=
    cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hN_dvd_ppN hfχ
  have h_f_pN_χ : f_pN ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hN_dvd_pN)) :=
    cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hN_dvd_pN hfχ
  have h_U_p_f_pN_χ : U_p_f_pN ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hN_dvd_pN)) :=
    heckeT_n_cusp_preserves_cuspFormCharSpace_divN hp hp_not_coprime_pN
      (χ.comp (ZMod.unitsMap hN_dvd_pN)) h_f_pN_χ
  have h_V_p_U_p_f_pN_χ' : V_p_U_p_f_pN ∈
      cuspFormCharSpace k
        ((χ.comp (ZMod.unitsMap hN_dvd_pN)).comp
          (ZMod.unitsMap (Nat.dvd_mul_left (p * N) p))) :=
    cuspForm_levelRaise_mem_cuspFormCharSpace (p * N) p k
      (χ.comp (ZMod.unitsMap hN_dvd_pN)) h_U_p_f_pN_χ
  have h_dvd_comp : (χ.comp (ZMod.unitsMap hN_dvd_pN)).comp
          (ZMod.unitsMap (Nat.dvd_mul_left (p * N) p)) =
        χ.comp (ZMod.unitsMap hN_dvd_ppN) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  rw [h_dvd_comp] at h_V_p_U_p_f_pN_χ'
  have h_g_ppN_χ : g_ppN ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hN_dvd_ppN)) :=
    Submodule.sub_mem _ h_f_ppN_χ h_V_p_U_p_f_pN_χ'
  have h_g_ppN_qexp : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) g_ppN).coeff n =
        if ¬ p ∣ n then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
    intro n
    have h1_period : (1 : ℝ) ∈ ((Gamma1 (p * (p * N))).map (mapGL ℝ)).strictPeriods := by
      simp [strictPeriods_Gamma1]
    have h_VUp_fun :
        (⇑V_p_U_p_f_pN : UpperHalfPlane → ℂ) =
          ⇑(HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hp_not_coprime_pN
              f_pN.toModularForm') := by
      change (HeckeRing.GL2.modularFormLevelRaise (p * N) p k
          (heckeT_n k p f_pN.toModularForm')).toFun =
        (HeckeRing.GL2.modularFormLevelRaise (p * N) p k
          (HeckeRing.GL2.heckeT_p_divN k p hp hp_not_coprime_pN f_pN.toModularForm')).toFun
      rw [heckeT_n_prime k hp, heckeT_p_all, dif_neg hp_not_coprime_pN]
    have h_coe_sub : (⇑g_ppN : UpperHalfPlane → ℂ) =
        ⇑f -
          ⇑(HeckeRing.GL2.AtkinLehner.pSupportedRaise k p hp hp_not_coprime_pN
            f_pN.toModularForm') := by
      change (⇑f_ppN - ⇑V_p_U_p_f_pN : UpperHalfPlane → ℂ) = _
      rw [h_VUp_fun]
      rfl
    rw [h_coe_sub]
    set f_ppN_mod : ModularForm ((Gamma1 (p * (p * N))).map (mapGL ℝ)) k :=
      ModularForm.restrictSubgroup (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hN_dvd_ppN)
        f.toModularForm'
    rw [show (⇑f - ⇑raised : UpperHalfPlane → ℂ) = ⇑(f_ppN_mod - raised) from rfl,
      show ModularFormClass.qExpansion (1 : ℝ) (⇑(f_ppN_mod - raised)) =
        ModularFormClass.qExpansion (1 : ℝ) (f_ppN_mod - raised) from rfl,
      qExpansion_sub one_pos h1_period f_ppN_mod raised, map_sub,
      show (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) f_ppN_mod) =
        (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f) from rfl,
      show (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) raised) =
        (ModularFormClass.qExpansion (1 : ℝ) raised).coeff n from rfl,
      HeckeRing.GL2.AtkinLehner.qExpansion_one_pSupportedRaise_coeff hp hp_not_coprime_pN
        f_pN.toModularForm' n,
      show (ModularFormClass.qExpansion (1 : ℝ) f_pN.toModularForm').coeff n =
        (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f) from rfl]
    split_ifs <;> simp
  clear_value g_ppN f_ppN V_p_U_p_f_pN U_p_f_pN raised
  clear h_V_p_U_p_f_pN_χ' h_f_ppN_χ h_dvd_comp V_p_U_p_f_pN f_ppN raised
  revert g_ppN h_g_ppN_χ h_g_ppN_qexp hN_dvd_ppN hppN_NeZero
  generalize p * (p * N) = M_alt at hM_eq'
  intro hppN_NeZero hN_dvd_ppN g_ppN h_g_ppN_χ h_g_ppN_qexp
  subst hM_eq'
  exact ⟨g_ppN, by convert h_g_ppN_χ using 2, h_g_ppN_qexp⟩

private theorem miyake_4_6_5_iterated_helper_general (n_iter : ℕ) :
    ∀ {N : ℕ} [NeZero N] {k : ℤ}
      (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ cuspFormCharSpace k χ)
      (S : Finset ℕ) (_ : ∀ p ∈ S, p.Prime)
      (_ : S.card = n_iter)
      (_ : Squarefree (S.prod id))
      {M : ℕ} (_ : NeZero M) (hNM : N ∣ M) (_ : S.prod id ∣ M)
      (_ : ∀ p ∈ S, (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)),
      ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
        ∀ n : ℕ,
          (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
          if Nat.Coprime n (S.prod id) then
            (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
          else 0 := by
  induction n_iter with
  | zero =>
    intro N _ k χ f hfχ S _hS_prime hS_card _hS_sqfree M _hM hNM _hSM _h_pf_dvd
    have hS_empty : S = ∅ := Finset.card_eq_zero.mp hS_card
    subst hS_empty
    refine ⟨CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hNM) f,
      cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM hfχ, fun n ↦ ?_⟩
    simp only [Finset.prod_empty, Nat.coprime_one_right_eq_true, if_true]
    rfl
  | succ k ih =>
    intro N _ k_int χ f hfχ S hS_prime hS_card hS_sqfree M hM_NeZero hNM hSM h_pf_dvd
    have hS_nonempty : S.Nonempty := Finset.card_pos.mp (hS_card ▸ Nat.succ_pos k)
    obtain ⟨q, hq_in⟩ := hS_nonempty
    have hq_prime : q.Prime := hS_prime q hq_in
    haveI : NeZero q := ⟨hq_prime.ne_zero⟩
    have h_S_prod_split : S.prod id = q * (S.erase q).prod id :=
      (Finset.mul_prod_erase _ _ hq_in).symm
    have hS_erase_prime : ∀ p ∈ S.erase q, p.Prime :=
      fun p hp ↦ hS_prime p (Finset.mem_of_mem_erase hp)
    have hS_erase_card : (S.erase q).card = k := by
      rw [Finset.card_erase_of_mem hq_in, hS_card]
      lia
    have hS_erase_sqfree : Squarefree ((S.erase q).prod id) := by
      rw [h_S_prod_split] at hS_sqfree
      exact hS_sqfree.of_mul_right
    have h_S_erase_prod_dvd_M : (S.erase q).prod id ∣ M :=
      (h_S_prod_split ▸ Dvd.intro_left _ rfl).trans hSM
    obtain ⟨hq_pf_not_dvd, hq_pf_dvd⟩ := h_pf_dvd q hq_in
    have h_cop_distinct : ∀ r ∈ S, ∀ s ∈ S, r ≠ s → Nat.Coprime r s :=
      fun r hr s hs hrs ↦ (Nat.coprime_primes (hS_prime r hr) (hS_prime s hs)).mpr hrs
    by_cases hqN : q ∣ N
    · obtain ⟨g_int, hg_int_χ, hg_int_qexp⟩ :=
        miyake_4_6_5_single_prime_dvd_N χ f hfχ q hq_prime
          (fun h ↦ hq_prime.coprime_iff_not_dvd.mp h hqN)
      haveI : NeZero (q * N) :=
        ⟨Nat.mul_ne_zero hq_prime.ne_zero (NeZero.ne N)⟩
      have hN_dvd_qN : N ∣ q * N := Nat.dvd_mul_left N q
      have hqN_dvd_M : q * N ∣ M := by
        calc q * N = N * q := by ring
          _ ∣ N * (M / N) := Nat.mul_dvd_mul_left N (hq_pf_dvd hqN)
          _ = M := Nat.mul_div_cancel' hNM
      have h_pf_dvd_new : ∀ p ∈ S.erase q,
          (¬ p ∣ (q * N) → p ^ 2 ∣ M) ∧ (p ∣ (q * N) → p ∣ M / (q * N)) := by
        intro r hr
        have hr_in_S : r ∈ S := Finset.mem_of_mem_erase hr
        have hr_ne_q : r ≠ q := Finset.ne_of_mem_erase hr
        have hr_prime : r.Prime := hS_prime r hr_in_S
        obtain ⟨hr_pf_not_dvd, hr_pf_dvd⟩ := h_pf_dvd r hr_in_S
        refine ⟨?_, ?_⟩
        · intro hr_ndvd_qN
          exact hr_pf_not_dvd fun hrN ↦ hr_ndvd_qN (hrN.mul_left q)
        · intro hr_dvd_qN
          have hr_dvd_N : r ∣ N := by
            rcases hr_prime.dvd_mul.mp hr_dvd_qN with h | h
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp h) hr_ne_q
            · exact h
          have h_div_eq : M / (q * N) = (M / N) / q := by
            rw [mul_comm q N, Nat.div_div_eq_div_mul]
          rw [h_div_eq]
          rcases (h_cop_distinct r hr_in_S q hq_in hr_ne_q).mul_dvd_of_dvd_of_dvd
              (hr_pf_dvd hr_dvd_N) (hq_pf_dvd hqN) with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          rw [hc, show r * q * c = (r * c) * q by ring,
            Nat.mul_div_cancel _ hq_prime.pos]
      obtain ⟨g', hg'_χ, hg'_qexp⟩ :=
        ih (χ.comp (ZMod.unitsMap hN_dvd_qN)) g_int hg_int_χ
          (S.erase q) hS_erase_prime hS_erase_card hS_erase_sqfree
          hM_NeZero hqN_dvd_M h_S_erase_prod_dvd_M h_pf_dvd_new
      refine ⟨g', ?_, ?_⟩
      · rw [show χ.comp (ZMod.unitsMap hNM) =
            (χ.comp (ZMod.unitsMap hN_dvd_qN)).comp (ZMod.unitsMap hqN_dvd_M) by
          rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]]
        exact hg'_χ
      · intro n
        rw [hg'_qexp n, hg_int_qexp n, h_S_prod_split]
        have h_cop_split : Nat.Coprime n (q * (S.erase q).prod id) ↔
            (¬ q ∣ n) ∧ Nat.Coprime n ((S.erase q).prod id) := by
          rw [Nat.coprime_mul_iff_right]
          exact and_congr_left fun _ ↦
            ⟨fun h ↦ hq_prime.coprime_iff_not_dvd.mp h.symm,
             fun h ↦ (hq_prime.coprime_iff_not_dvd.mpr h).symm⟩
        by_cases h_rest : Nat.Coprime n ((S.erase q).prod id)
        · by_cases h_q_div : q ∣ n
          · rw [if_pos h_rest, if_neg (not_not_intro h_q_div),
                if_neg fun h ↦ (h_cop_split.mp h).1 h_q_div]
          · rw [if_pos h_rest, if_pos h_q_div,
                if_pos (h_cop_split.mpr ⟨h_q_div, h_rest⟩)]
        · rw [if_neg h_rest, if_neg fun h ↦ h_rest (h_cop_split.mp h).2]
    · have hqN_coprime : Nat.Coprime q N :=
        hq_prime.coprime_iff_not_dvd.mpr hqN
      obtain ⟨g_int, hg_int_χ, hg_int_qexp⟩ :=
        miyake_4_6_5_single_prime_coprime_to_N χ f hfχ q hq_prime
      haveI : NeZero (N * q ^ 2) :=
        ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hq_prime.ne_zero)⟩
      have hN_dvd_Nq2 : N ∣ N * q ^ 2 := Nat.dvd_mul_right N (q ^ 2)
      have hNq2_dvd_M : N * q ^ 2 ∣ M :=
        (hqN_coprime.symm.pow_right 2).mul_dvd_of_dvd_of_dvd hNM (hq_pf_not_dvd hqN)
      have h_pf_dvd_new : ∀ p ∈ S.erase q,
          (¬ p ∣ (N * q ^ 2) → p ^ 2 ∣ M) ∧
          (p ∣ (N * q ^ 2) → p ∣ M / (N * q ^ 2)) := by
        intro r hr
        have hr_in_S : r ∈ S := Finset.mem_of_mem_erase hr
        have hr_ne_q : r ≠ q := Finset.ne_of_mem_erase hr
        have hr_prime : r.Prime := hS_prime r hr_in_S
        obtain ⟨hr_pf_not_dvd, hr_pf_dvd⟩ := h_pf_dvd r hr_in_S
        refine ⟨?_, ?_⟩
        · intro hr_ndvd_Nq2
          exact hr_pf_not_dvd fun hrN ↦ hr_ndvd_Nq2 (hrN.mul_right (q ^ 2))
        · intro hr_dvd_Nq2
          have hr_dvd_N : r ∣ N := by
            rcases hr_prime.dvd_mul.mp hr_dvd_Nq2 with h | h
            · exact h
            · exact absurd ((Nat.prime_dvd_prime_iff_eq hr_prime hq_prime).mp
                  (hr_prime.dvd_of_dvd_pow h)) hr_ne_q
          have hq2_dvd_MN : q ^ 2 ∣ M / N := by
            have hq2_dvd_M : q ^ 2 ∣ M := hq_pf_not_dvd hqN
            rw [(Nat.mul_div_cancel' hNM).symm] at hq2_dvd_M
            exact Nat.Coprime.dvd_of_dvd_mul_left (hqN_coprime.pow_left 2) hq2_dvd_M
          have h_div_eq : M / (N * q ^ 2) = (M / N) / (q ^ 2) := by
            rw [Nat.div_div_eq_div_mul]
          rw [h_div_eq]
          rcases (h_cop_distinct r hr_in_S q hq_in hr_ne_q |>.pow_right 2).mul_dvd_of_dvd_of_dvd
              (hr_pf_dvd hr_dvd_N) hq2_dvd_MN with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          rw [hc, show r * q ^ 2 * c = (r * c) * q ^ 2 by ring,
            Nat.mul_div_cancel _ (pow_pos hq_prime.pos 2)]
      obtain ⟨g', hg'_χ, hg'_qexp⟩ :=
        ih (χ.comp (ZMod.unitsMap hN_dvd_Nq2)) g_int hg_int_χ
          (S.erase q) hS_erase_prime hS_erase_card hS_erase_sqfree
          hM_NeZero hNq2_dvd_M h_S_erase_prod_dvd_M h_pf_dvd_new
      refine ⟨g', ?_, ?_⟩
      · rw [show χ.comp (ZMod.unitsMap hNM) =
            (χ.comp (ZMod.unitsMap hN_dvd_Nq2)).comp (ZMod.unitsMap hNq2_dvd_M) by
          rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]]
        exact hg'_χ
      · intro n
        rw [hg'_qexp n, hg_int_qexp n, h_S_prod_split]
        have h_cop_split : Nat.Coprime n (q * (S.erase q).prod id) ↔
            (¬ q ∣ n) ∧ Nat.Coprime n ((S.erase q).prod id) := by
          rw [Nat.coprime_mul_iff_right]
          exact and_congr_left fun _ ↦
            ⟨fun h ↦ hq_prime.coprime_iff_not_dvd.mp h.symm,
             fun h ↦ (hq_prime.coprime_iff_not_dvd.mpr h).symm⟩
        by_cases h_rest : Nat.Coprime n ((S.erase q).prod id)
        · by_cases h_q_div : q ∣ n
          · rw [if_pos h_rest, if_neg (not_not_intro h_q_div),
                if_neg fun h ↦ (h_cop_split.mp h).1 h_q_div]
          · rw [if_pos h_rest, if_pos h_q_div,
                if_pos (h_cop_split.mpr ⟨h_q_div, h_rest⟩)]
        · rw [if_neg h_rest, if_neg fun h ↦ h_rest (h_cop_split.mp h).2]

/-- **Generalized iterated single-prime peeling** (no `L ⊆ N.primeFactors`
hypothesis).

For squarefree positive `L`, the coprime-to-`L` filter exists at level
`L_N · L_coprime² · N`, where `L_N := L.gcd N` (the part of `L` dividing
`N`) and `L_coprime := L / L_N` (the part coprime to `N`).  Equivalently,
at level `L * (L_coprime) * N`.

Combines:
* For each prime `p ∈ L.primeFactors` with `p ∣ N`: use
  `miyake_4_6_5_single_prime_dvd_N` (level `N → N · p`).
* For each prime `p ∈ L.primeFactors` with `p ∤ N`: use
  `miyake_4_6_5_single_prime_coprime_to_N` (level `N → N · p²`).

This corresponds to Miyake Lemma 4.6.5 *in full generality* (allowing
primes of `L` that need not divide `N`). -/
private theorem miyake_4_6_5_iterated_L_general
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (L : ℕ) (hL_pos : 0 < L) (hL_sqfree : Squarefree L) (M : ℕ) [NeZero M]
    (hNM : N ∣ M) (hLM : L ∣ M)
    (h_pf_dvd : ∀ p ∈ L.primeFactors,
      (¬ p ∣ N → p ^ 2 ∣ M) ∧ (p ∣ N → p ∣ M / N)) :
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n L then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  have hS_prime : ∀ p ∈ L.primeFactors, p.Prime :=
    fun _ hp ↦ Nat.prime_of_mem_primeFactors hp
  have hS_prod : L.primeFactors.prod id = L := by
    simp [Nat.prod_primeFactors_of_squarefree hL_sqfree]
  have hS_sqfree : Squarefree (L.primeFactors.prod id) := hS_prod.symm ▸ hL_sqfree
  have hS_dvd_M : L.primeFactors.prod id ∣ M := hS_prod.symm ▸ hLM
  obtain ⟨g, hg_χ, hg_qexp⟩ :=
    miyake_4_6_5_iterated_helper_general L.primeFactors.card χ f hfχ
      L.primeFactors hS_prime rfl hS_sqfree ‹NeZero M› hNM hS_dvd_M h_pf_dvd
  exact ⟨g, hg_χ, fun n ↦ by simpa only [hS_prod] using hg_qexp n⟩

/-- **Generalized `h_form`** (no `l' ⊆ N.primeFactors` hypothesis).

For `f ∈ S_k(Γ_1(N), χ)` and `l'` squarefree positive, there exists
`h_form` at level `Γ_1(l'² · N)` with `q`-expansion supported on
`(n, l') ≠ 1`, *regardless* of whether the primes of `l'` divide `N`. -/
theorem miyake_h_form_general
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l') :
    let M := N * l' ^ 2
    haveI : NeZero M := ⟨Nat.mul_ne_zero (NeZero.ne N)
      (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp hl'_pos))⟩
    have hNM : N ∣ M := Nat.dvd_mul_right N (l' ^ 2)
    ∃ h_form : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      h_form ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) h_form).coeff n =
        if ¬ Nat.Coprime n l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  haveI hM_NeZero : NeZero (N * l' ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne N)
      (pow_ne_zero 2 (Nat.pos_iff_ne_zero.mp hl'_pos))⟩
  have hNM : N ∣ N * l' ^ 2 := Nat.dvd_mul_right N (l' ^ 2)
  have hl'M : l' ∣ N * l' ^ 2 := dvd_mul_of_dvd_right (dvd_pow_self l' two_ne_zero) N
  have h_pf_dvd : ∀ p ∈ l'.primeFactors,
      (¬ p ∣ N → p ^ 2 ∣ (N * l' ^ 2)) ∧
      (p ∣ N → p ∣ (N * l' ^ 2) / N) := by
    intro p hp_in
    have hp_dvd_l' : p ∣ l' := Nat.dvd_of_mem_primeFactors hp_in
    refine ⟨fun _ ↦ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hp_dvd_l' 2) N, fun _ ↦ ?_⟩
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne N))]
    exact dvd_pow hp_dvd_l' two_ne_zero
  obtain ⟨g, hg_char, hg_qexp⟩ :=
    miyake_4_6_5_iterated_L_general χ f hfχ l' hl'_pos hl'_sqfree
      (N * l' ^ 2) hNM hl'M h_pf_dvd
  let f_at_M : CuspForm ((Gamma1 (N * l' ^ 2)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup
      (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hNM) f
  refine ⟨f_at_M - g, Submodule.sub_mem _
    (cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM hfχ) hg_char, ?_⟩
  intro n
  have h1_period : (1 : ℝ) ∈ ((Gamma1 (N * l' ^ 2)).map (mapGL ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  have h_sub :
      ModularFormClass.qExpansion (1 : ℝ) (f_at_M - g) =
        ModularFormClass.qExpansion (1 : ℝ) f_at_M -
        ModularFormClass.qExpansion (1 : ℝ) g := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← qExpansion_neg one_pos h1_period g]
    exact qExpansion_add (Γ := (Gamma1 (N * l' ^ 2)).map (mapGL ℝ))
      (h := (1 : ℝ)) (a := k) (b := k) one_pos h1_period f_at_M (- g)
  rw [show ModularFormClass.qExpansion (1 : ℝ) (⇑(f_at_M - g) : UpperHalfPlane → ℂ) =
        ModularFormClass.qExpansion (1 : ℝ) (f_at_M - g) from rfl, h_sub, map_sub,
      show ModularFormClass.qExpansion (1 : ℝ) f_at_M =
        ModularFormClass.qExpansion (1 : ℝ) f from rfl, hg_qexp n]
  split_ifs <;> simp

/-- **M2: The form `h(z) := Σ_{(n, l') ≠ 1} aₙ qⁿ`** (Miyake Eq. 4.6.10).

For `f ∈ S_k(Γ_1(N), χ)` and `l' ∣ N` squarefree, the form `f − g` where
`g` is from M1 (with `L := l'`) has `q`-expansion supported on `(n, l') ≠ 1`. -/
theorem miyake_h_form
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors) :
    let M := l' * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N l'
    ∃ h_form : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      h_form ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) h_form).coeff n =
        if ¬ Nat.Coprime n l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  have hM_NeZero : NeZero (l' * N) :=
    ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne N)⟩
  have hNM : N ∣ l' * N := Nat.dvd_mul_left N l'
  obtain ⟨g, hg_char, hg_qexp⟩ :=
    miyake_4_6_5_iterated_L χ f hfχ l' hl'_pos hl'_sqfree hl'_dvd
  let f_at_M : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup
      (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hNM) f
  refine ⟨f_at_M - g,
    Submodule.sub_mem _ (cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM hfχ) hg_char, ?_⟩
  intro n
  have h1_period : (1 : ℝ) ∈ ((Gamma1 (l' * N)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (l' * N)).map (mapGL ℝ) =
        (Gamma1 (l' * N) : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h_sub :
      ModularFormClass.qExpansion (1 : ℝ) (f_at_M - g) =
        ModularFormClass.qExpansion (1 : ℝ) f_at_M -
        ModularFormClass.qExpansion (1 : ℝ) g := by
    rw [sub_eq_add_neg, sub_eq_add_neg, ← qExpansion_neg one_pos h1_period g]
    exact qExpansion_add (Γ := (Gamma1 (l' * N)).map (mapGL ℝ))
      (h := (1 : ℝ)) (a := k) (b := k) one_pos h1_period f_at_M (- g)
  rw [show ModularFormClass.qExpansion (1 : ℝ) (⇑(f_at_M - g) : UpperHalfPlane → ℂ) =
        ModularFormClass.qExpansion (1 : ℝ) (f_at_M - g) from rfl, h_sub, map_sub,
      show ModularFormClass.qExpansion (1 : ℝ) f_at_M =
        ModularFormClass.qExpansion (1 : ℝ) f from rfl, hg_qexp n]
  by_cases hcop : Nat.Coprime n l'
  · rw [if_pos hcop, if_neg (not_not_intro hcop)]
    ring
  · rw [if_neg hcop, if_pos hcop]
    ring

/-- **M3: The form `g := f − h` is `p`-supported when `f` has the
coprime-vanishing hypothesis for `l = p · l'`** (Miyake Eq. 4.6.11).

When `f` satisfies `aₙ(f) = 0` for `(n, p · l') = 1`, the form
`g := f − h_form` at level `Γ_1(l' · N)` has
`aₙ(g) = aₙ(f) · [Coprime n l']` (i.e., `g` is the coprime-to-`l'`
filter of `f`).  In particular `g` is `p`-supported: when `(n, p) = 1`
*and* `Coprime n l'`, `aₙ(g) = aₙ(f) = 0` by hypothesis. -/
theorem miyake_g_p_supported
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    let M := l' * N
    haveI : NeZero M := ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne N)⟩
    have hNM : N ∣ M := Nat.dvd_mul_left N l'
    ∃ g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) ∧
      g ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule M k p ∧
      ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) g).coeff n =
        if Nat.Coprime n l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0 := by
  obtain ⟨g, hg_char, hg_qexp⟩ :=
    miyake_4_6_5_iterated_L χ f hfχ l' hl'_pos hl'_sqfree hl'_dvd
  refine ⟨g, hg_char, ?_, hg_qexp⟩
  intro n hn_no_p
  by_cases hcop_l' : Nat.Coprime n l'
  · rw [hg_qexp n, if_pos hcop_l']
    exact h_vanish n (Nat.Coprime.mul_right (hp.coprime_iff_not_dvd.mpr hn_no_p).symm hcop_l')
  · rw [hg_qexp n, if_neg hcop_l']

/-- **M4: Miyake 4.6.4 dichotomy.**

For `g ∈ qSupportedOnDvdSubmodule M k p ∩ cuspFormCharSpace`, with `p ∣ M`
and `NeZero (M / p)`: either `g = 0`, or there is `g_p` at level `Γ_1(M/p)`
in the lifted character space, such that `V_p g_p = g` as functions on `ℍ`. -/
theorem miyake_4_6_4_dichotomy
    {M : ℕ} [NeZero M] {k : ℤ}
    (χ_M : DirichletCharacter ℂ M)
    (p : ℕ) [NeZero p] [NeZero (M / p)]
    (hp : p.Prime) (hpM : p ∣ M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hgχ : g ∈ cuspFormCharSpace k χ_M.toUnitHom)
    (hg_supp : g ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule M k p) :
    g = 0 ∨ ∃ g_p : CuspForm ((Gamma1 (M / p)).map (mapGL ℝ)) k,
      (⇑(HeckeRing.GL2.levelRaise (M / p) p k g_p) : UpperHalfPlane → ℂ) = ⇑g :=
  HeckeRing.GL2.AtkinLehner.qSupportedOnDvd_eq_zero_or_exists_levelRaise_preimage_of_char
    hp.one_lt hpM χ_M g hgχ hg_supp

/-- **M4-strong: strengthened Miyake 4.6.4 dichotomy** (with character info).

Identical to `miyake_4_6_4_dichotomy`, but in the non-zero case ALSO exposes:
* The fact that `χ_M` factors through `(ZMod (M/p))ˣ` (`h_fac`).
* The character `g_p ∈ cuspFormCharSpace k (loweredCharacter h_fac).toUnitHom`. -/
theorem miyake_4_6_4_dichotomy_strong
    {M : ℕ} [NeZero M] {k : ℤ}
    (χ_M : DirichletCharacter ℂ M)
    (p : ℕ) [NeZero p] [NeZero (M / p)]
    (hp : p.Prime) (hpM : p ∣ M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hgχ : g ∈ cuspFormCharSpace k χ_M.toUnitHom)
    (hg_supp : g ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule M k p) :
    g = 0 ∨ ∃ (h_fac : χ_M.FactorsThrough (M / p))
              (g_p : CuspForm ((Gamma1 (M / p)).map (mapGL ℝ)) k),
      g_p ∈ cuspFormCharSpace k
        (HeckeRing.GL2.loweredCharacter h_fac).toUnitHom ∧
      (⇑(HeckeRing.GL2.levelRaise (M / p) p k g_p) : UpperHalfPlane → ℂ) = ⇑g := by
  obtain ⟨φ, h_eq, h_period⟩ :=
    HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
      hp.one_lt hpM g hg_supp
  rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
      p M hpM k χ_M φ g hgχ h_eq h_period with
    ⟨h_fac, F, hF_char, hF_eq⟩ | hφ_zero
  · right
    refine ⟨h_fac, F, hF_char, ?_⟩
    change (HeckeRing.GL2.levelRaiseFun p k ⇑F : UpperHalfPlane → ℂ) = ⇑g
    rw [hF_eq, ← h_eq]
  · left
    exact DFunLike.ext _ _ (fun τ ↦ by simp [h_eq, hφ_zero, HeckeRing.GL2.levelRaiseFun])

private lemma matrix_int_cast_factor_aux {n : Type*} {a m : ℕ} (hm : a ∣ m)
    (M : Matrix n n ℤ) :
    M.map (Int.cast : ℤ → ZMod a) =
      (M.map (Int.cast : ℤ → ZMod m)).map (ZMod.castHom hm (ZMod a)) := by
  rw [Matrix.map_map]
  congr 1
  ext x
  simp

/-- **T5a-0: Existence of the extra coset representative `γ_p^(p)`
in Miyake's Lemma 4.5.11 (p. 143-144).**

For prime `p` and positive integer `N` with `p ∣ N` and `p² ∤ N`
(so `gcd(p, N/p) = 1`), there exists `γ ∈ Γ_0(N/p)` with
* `γ ≡ [0, -1; 1, 0]  (mod p)` (matching Miyake's `[0, -a⁻¹; a, 0]` with `a = 1`),
* `γ ≡ I  (mod N/p)`. -/
theorem descendExtraGamma_exists
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (N : ℕ) [NeZero N] (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N) [NeZero (N / p)] :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ ∈ Gamma0 (N / p) ∧
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
        = !![(0 : ZMod p), -1; 1, 0]) ∧
      ((γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) := by
  have hcop : Nat.Coprime p (N / p) := hp.coprime_iff_not_dvd.mpr fun h => hp_sq <| by
    simpa [sq] using (Nat.mul_div_cancel' hpN) ▸ Nat.mul_dvd_mul_left p h
  obtain ⟨u, v, h_bez⟩ := hcop.isCoprime
  let a : ℤ := (p : ℤ)
  let b : ℤ := ((N / p : ℕ) : ℤ)
  have h_ab : a * b = (N : ℤ) := by
    change (p : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ)
    exact_mod_cast Nat.mul_div_cancel' hpN
  let γ_mat : Matrix (Fin 2) (Fin 2) ℤ := !![u * a, -(v * b); v * b, u * a]
  have h_ua_p : ((u * a : ℤ) : ZMod p) = 0 := by simp [a]
  have h_vb_p : ((v * b : ℤ) : ZMod p) = 1 := by
    have h' : ((u * a + v * b : ℤ) : ZMod p) = 1 := by
      rw [h_bez]
      simp
    rwa [Int.cast_add, h_ua_p, zero_add] at h'
  have h_vb_Np : ((v * b : ℤ) : ZMod (N / p)) = 0 := by
    have hb : ((b : ℤ) : ZMod (N / p)) = 0 := by
      show (((N / p : ℕ) : ℤ) : ZMod (N / p)) = 0
      exact_mod_cast ZMod.natCast_self (N / p)
    rw [Int.cast_mul, hb, mul_zero]
  have h_ua_Np : ((u * a : ℤ) : ZMod (N / p)) = 1 := by
    have h' : ((u * a + v * b : ℤ) : ZMod (N / p)) = 1 := by
      rw [h_bez]
      simp
    rwa [Int.cast_add, h_vb_Np, add_zero] at h'
  have h_mat_p : γ_mat.map (Int.cast : ℤ → ZMod p) = !![(0 : ZMod p), -1; 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ_mat, h_vb_p, h_ua_p]
  have h_mat_Np : γ_mat.map (Int.cast : ℤ → ZMod (N / p)) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [γ_mat, h_vb_Np, h_ua_Np]
  have hdet_N : (γ_mat.map (Int.cast : ℤ → ZMod N)).det = 1 := by
    have hmap_eq : γ_mat.map (Int.cast : ℤ → ZMod N) =
        (Int.castRingHom (ZMod N)).mapMatrix γ_mat := by
      ext
      simp [γ_mat, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hmap_eq, ← RingHom.map_det]
    have hdet : γ_mat.det = (u * a) ^ 2 + (v * b) ^ 2 := by
      simp only [γ_mat, Matrix.det_fin_two_of]
      ring
    rw [hdet, map_add, map_pow, map_pow]
    set x := (Int.castRingHom (ZMod N)) (u * a)
    set y := (Int.castRingHom (ZMod N)) (v * b)
    have h_sum : x + y = 1 := by
      rw [← map_add, h_bez]
      simp
    have h_prd : x * y = 0 := by
      rw [← map_mul, show u * a * (v * b) = u * v * (a * b) by ring, h_ab,
        map_mul, map_natCast, ZMod.natCast_self, mul_zero]
    rw [show x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) by ring, h_sum, h_prd]
    ring
  obtain ⟨γ, hγ⟩ := SL2Reduction.SL2_reduction_surjective N
    ⟨γ_mat.map (Int.cast : ℤ → ZMod N), hdet_N⟩
  have h_γ_mat_N : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) =
      γ_mat.map (Int.cast : ℤ → ZMod N) := (hγ ▸ coe_matrix_coe (R := ZMod N) γ).symm
  have h_mod_p : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) =
      !![(0 : ZMod p), -1; 1, 0] := by
    rw [matrix_int_cast_factor_aux hpN, h_γ_mat_N, ← matrix_int_cast_factor_aux hpN, h_mat_p]
  have h_mod_Np : (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 := by
    rw [matrix_int_cast_factor_aux (Nat.div_dvd_of_dvd hpN), h_γ_mat_N,
        ← matrix_int_cast_factor_aux (Nat.div_dvd_of_dvd hpN), h_mat_Np]
  have h_mem : γ ∈ Gamma0 (N / p) := by
    rw [Gamma0_mem]
    simpa using congr_fun (congr_fun h_mod_Np 1) 0
  exact ⟨γ, h_mem, h_mod_p, h_mod_Np⟩

/-- **T5a-0a-coprime-adjust**: number-theoretic adjustment lemma.

For integers `c, d, N` with `d ≠ 0` and `Nat.gcd (Int.gcd c d) N.toNat = 1`
(i.e., no prime divides all of `c, d, N`), there exists `t : ℤ` such that
`gcd(c + tN, d) = 1`.

**AUDIT NOTE (2026-05-17, pass 6)**: added `d ≠ 0` hypothesis.  The
previous version was FALSE for `d = 0`: counterexample `c=3, d=0, N=5`:
hypothesis `gcd(gcd(3,0), 5) = gcd(3, 5) = 1` holds, but the conclusion
`∃ t, |3 + 5t| = 1` has no integer solution.  For `d = 0`, the
conclusion `gcd(c + tN, 0) = 1` requires `c + tN = ±1`, which needs
`c ≡ ±1 (mod N)` — not implied by `gcd(c, N) = 1` alone.  The consumer
T5a-0a lifts `d̄ ∈ ZMod N` to `d ∈ ℤ`; the lift can always be chosen
nonzero (lift `d̄ ≡ 0` as `d = N`, not `0`), so `d ≠ 0` is freely
satisfiable downstream.

**Proof recipe**: For each prime `q ∣ d.natAbs`:
* If `q ∤ N.toNat`: since `N ≢ 0 mod q`, `N` is invertible mod `q`,
  so we can pick `t mod q` with `c + tN ≢ 0 mod q` (any `t ≢ -c·N⁻¹ mod q`,
  which is `q - 1 ≥ 1` residues).
* If `q ∣ N.toNat`: then `c + tN ≡ c mod q`, so we need `c ≢ 0 mod q` —
  forced by hypothesis: `q ∣ Int.gcd c d` (since `q ∣ c` and `q ∣ d`)
  combined with `q ∣ N.toNat` would contradict `gcd(Int.gcd c d, N.toNat) = 1`.

By CRT (the residue conditions are over pairwise coprime primes), combine
the `t mod q` constraints (only for `q ∤ N`) into a single `t ∈ ℤ`. -/
theorem int_exists_coprime_adjust
    (c d N : ℤ) (hd_ne : d ≠ 0)
    (h_gcd : Nat.Coprime (Int.gcd c d) N.toNat) :
    ∃ t : ℤ, Int.gcd (c + t * N) d = 1 := by
  classical
  have hn_pos : 0 < d.natAbs := Int.natAbs_pos.mpr hd_ne
  let a_fn : ℕ → ℕ := fun q => if (q : ℤ) ∣ c then 1 else 0
  have h_pairwise : (d.natAbs.primeFactors : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    grind [Nat.coprime_primes, Nat.prime_of_mem_primeFactors]
  have h_nonzero : ∀ q ∈ d.natAbs.primeFactors, id q ≠ 0 := fun q hq =>
    (Nat.prime_of_mem_primeFactors hq).ne_zero
  obtain ⟨t_nat, h_t_modeq⟩ := Nat.chineseRemainderOfFinset
    a_fn id d.natAbs.primeFactors h_nonzero h_pairwise
  refine ⟨(t_nat : ℤ), ?_⟩
  change Nat.gcd (c + (t_nat : ℤ) * N).natAbs d.natAbs = 1
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro q hq_prime hq_dvd_d hq_dvd_ctN
  have hq_in_pf : q ∈ d.natAbs.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq_prime, hq_dvd_d, hn_pos.ne'⟩
  have h_t_mod_int : ((t_nat : ℤ)) ≡ ((a_fn q : ℕ) : ℤ) [ZMOD (q : ℤ)] :=
    by exact_mod_cast h_t_modeq q hq_in_pf
  have hq_dvd_aN : (q : ℤ) ∣ c + ((a_fn q : ℕ) : ℤ) * N := by
    have h_diff : (q : ℤ) ∣ (c + (t_nat : ℤ) * N) - (c + ((a_fn q : ℕ) : ℤ) * N) := by
      rw [show (c + (t_nat : ℤ) * N) - (c + ((a_fn q : ℕ) : ℤ) * N) =
          ((t_nat : ℤ) - (a_fn q : ℤ)) * N from by ring]
      exact (Int.modEq_iff_dvd.mp h_t_mod_int.symm).mul_right N
    have hq_dvd_sub_swap := (Int.natCast_dvd.mpr hq_dvd_ctN).sub h_diff
    rwa [show (c + (t_nat : ℤ) * N) -
        ((c + (t_nat : ℤ) * N) - (c + ((a_fn q : ℕ) : ℤ) * N)) =
        (c + ((a_fn q : ℕ) : ℤ) * N) from by ring] at hq_dvd_sub_swap
  by_cases hqc : (q : ℤ) ∣ c
  · have h_afn_eq : a_fn q = 1 := by simp [a_fn, hqc]
    have hq_dvd_cN : (q : ℤ) ∣ c + N := by simpa [h_afn_eq] using hq_dvd_aN
    have hq_dvd_Ntn : q ∣ N.toNat := by
      have hN_natAbs : q ∣ N.natAbs :=
        Int.natCast_dvd.mp (by simpa using hq_dvd_cN.sub hqc)
      by_cases hN_sign : 0 ≤ N
      · rwa [← Int.natAbs_of_nonneg hN_sign, ← Int.toNat_of_nonneg hN_sign] at hN_natAbs
      · push Not at hN_sign; simp [Int.toNat_of_nonpos hN_sign.le]
    exact hq_prime.one_lt.not_ge (Nat.le_of_dvd Nat.one_pos
      (h_gcd ▸ Nat.dvd_gcd (Nat.dvd_gcd (Int.natCast_dvd.mp hqc) hq_dvd_d) hq_dvd_Ntn))
  · exact hqc (by simpa [show a_fn q = 0 from by simp [a_fn, hqc]] using hq_dvd_aN)

/-- The reduction-mod-`N` map `SL₂(ℤ) → SL₂(ZMod N)` is surjective (strong approximation
for `SL₂`). See `SL2Reduction.SL2_reduction_surjective` for the full proof. -/
theorem SL2Z_to_SL2_ZMod_surjective (N : ℕ) [NeZero N] :
    Function.Surjective
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod N))) :
        Matrix.SpecialLinearGroup (Fin 2) ℤ →
        Matrix.SpecialLinearGroup (Fin 2) (ZMod N)) :=
  SL2Reduction.SL2_reduction_surjective N

/-- Number of coset representatives for the Hecke descent operator: `p` when `p² ∣ N`,
`p + 1` when `p² ∤ N` (Miyake's `d + 1`). -/
def descendCosetCount (p N : ℕ) : ℕ := if p ^ 2 ∣ N then p else p + 1

/-- A fixed element of `Γ_0(N/p)` satisfying `γ ≡ [0,-1;1,0] (mod p)` and
`γ ≡ I (mod N/p)`, used as the extra coset representative when `p² ∤ N`.
Returns `1` when the primality/divisibility conditions fail. -/
noncomputable def descendExtraGamma
    (p : ℕ) [NeZero p] (N : ℕ) [NeZero N] :
    Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  if h : p.Prime ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N ∧ N / p ≠ 0 then
    haveI : NeZero (N / p) := ⟨h.2.2.2⟩
    (descendExtraGamma_exists p h.1 N h.2.1 h.2.2.1).choose
  else 1

/-- Coset matrices for the Hecke descent operator `Γ_0(N) → Γ_0(N/p)`
(Miyake Lemma 4.5.11, pp. 143–144).

For `v < p`: the upper-triangular representative `[1, v; 0, p]`.
For `v = p` (only when `p² ∤ N`): the product `[1, 0; 0, p] · descendExtraGamma p N`. -/
noncomputable def descendCosetList (p N : ℕ) [NeZero p] [NeZero N] (hp : p.Prime) :
    Fin (descendCosetCount p N) → GL (Fin 2) ℝ :=
  fun v ↦
    if h_v : v.val < p then
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
    else
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)) *
      mapGL ℝ (descendExtraGamma p N)

/-- Given `p · a01 = B + v · D - (A + v · C) · v'`, the matrix identity
`[1, v; 0, p] · [A, B; C, D] = [A+vC, a01; pC, D-Cv'] · [1, v'; 0, p]`
holds in `Matrix (Fin 2) (Fin 2) ℤ`. (Miyake p. 144.) -/
lemma descend_upper_tri_raw_matrix_identity
    (p : ℕ) (A B C D : ℤ) (v v' a01 : ℤ)
    (ha01 : (p : ℤ) * a01 = B + v * D - (A + v * C) * v') :
    (!![(1 : ℤ), v; 0, (p : ℤ)] * !![A, B; C, D] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A + v * C, a01; (p : ℤ) * C, D - C * v'] *
        !![(1 : ℤ), v'; 0, (p : ℤ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    lia

/-- Raw integer matrix identity for the extra-coset case.

Given `had : a*d - b*c = 1` (det γ_p = 1) and the integrality condition
`p * α01 = a*(B+v*D) - b*(A+v*C)`, we have
`[1,v;0,p] * [A,B;C,D] = [[Ad-Bc+v(Cd-Dc), α01]; [p(Cd-Dc), Da-Cb]] * [a,b;pc,pd]`
in `Matrix (Fin 2) (Fin 2) ℤ`.

This is the integer-side core of the extra-coset branch of
`descendCosetList_action_upper_tri_extra`.  The RHS multiplies α_mat by
`[1,0;0,p] * [a,b;c,d]` (= `[a,b;pc,pd]`), which is `[1,0;0,p] * γ_p_mat`. -/
private lemma descend_extra_raw_matrix_identity (p : ℕ) (A B C D a b c d : ℤ)
    (v α01 : ℤ) (had : a * d - b * c = 1)
    (h01 : (p : ℤ) * α01 = a * (B + v * D) - b * (A + v * C)) :
    (!![(1 : ℤ), v; 0, (p : ℤ)] * !![A, B; C, D] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A * d - B * c + v * (C * d - D * c), α01;
         (p : ℤ) * (C * d - D * c), D * a - C * b] *
        !![(a : ℤ), b; (p : ℤ) * c, (p : ℤ) * d] := by
  have hL : (!![(1 : ℤ), v; 0, (p : ℤ)] * !![A, B; C, D] : Matrix (Fin 2) (Fin 2) ℤ) =
      !![A + v * C, B + v * D; (p : ℤ) * C, (p : ℤ) * D] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hR : !![A * d - B * c + v * (C * d - D * c), α01;
         (p : ℤ) * (C * d - D * c), D * a - C * b] *
        !![(a : ℤ), b; (p : ℤ) * c, (p : ℤ) * d] =
      !![A + v * C, B + v * D; (p : ℤ) * C, (p : ℤ) * D] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · have : α01 * ((p : ℤ) * c) = ((p : ℤ) * α01) * c := by ring
      rw [this, h01]; linear_combination (A + v * C) * had
    · have : α01 * ((p : ℤ) * d) = ((p : ℤ) * α01) * d := by ring
      rw [this, h01]; linear_combination (B + v * D) * had
    · linear_combination (p : ℤ) * C * had
    · linear_combination (p : ℤ) * D * had
  rw [hL, hR]

/-- **T5a-2:** Every matrix in `descendCosetList p N hp` has determinant `p`. -/
theorem descendCosetList_det (p N : ℕ) [NeZero p] [NeZero N] (hp : p.Prime) :
    ∀ v : Fin (descendCosetCount p N),
      (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ) := by
  intro v
  unfold descendCosetList
  split_ifs with h_v
  · simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_fin_two]
  · rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.det_mul,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe,
        RingHom.mapMatrix_apply]
    have h_det : ((descendExtraGamma p N).val.map (algebraMap ℤ ℝ)).det = 1 := by
      simp [← Int.cast_det, (descendExtraGamma p N).property]
    rw [h_det]
    simp [Matrix.det_fin_two]

/-- Miyake Lemma 4.5.11 (`p ∣ M` case, p. 144): when `p² ∣ N`, the action of
`γ' ∈ Γ_0(N/p)` on `[1, m; 0, p]` stays within the upper-triangular coset
representatives. The canonical target `m'` is pinned by
`a · m' ≡ b + m · d (mod p)`. -/
theorem descendCosetList_action_upper_tri_clean
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p) :
    ∃ (m' : Fin p) (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) * (m'.val : ZMod p) =
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
         (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α *
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m'.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set A := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set B := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set C := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set D := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ C := by
    have h := CongruenceSubgroup.Gamma0_mem.mp h_γ'
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hp_dvd_C : (p : ℤ) ∣ C := dvd_trans
    (by exact_mod_cast (Nat.dvd_div_iff_mul_dvd hpN).mpr (by rwa [← sq])) h_C_dvd_Np
  have h_C_mod_p : (C : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd_C
  have hdet : A * D - B * C = 1 := by
    have h := γ'.property
    rwa [Matrix.det_fin_two] at h
  have h_AD_mod_p : (A : ZMod p) * (D : ZMod p) = 1 := by
    have h := congr_arg (Int.cast : ℤ → ZMod p) hdet
    push_cast [h_C_mod_p] at h
    simpa using h
  have h_A_unit : IsUnit ((A : ZMod p)) :=
    ⟨⟨(A : ZMod p), (D : ZMod p), h_AD_mod_p, by rw [mul_comm]; exact h_AD_mod_p⟩, rfl⟩
  set u_A : (ZMod p)ˣ := h_A_unit.unit
  let m'_zmod : ZMod p := (u_A⁻¹ : (ZMod p)ˣ).val *
    ((B : ZMod p) + (m.val : ZMod p) * (D : ZMod p))
  let m' : Fin p := ⟨m'_zmod.val, ZMod.val_lt _⟩
  have h_moebius : (A : ZMod p) * (m'.val : ZMod p) =
      (B : ZMod p) + (m.val : ZMod p) * (D : ZMod p) := by
    show (A : ZMod p) * (m'_zmod.val : ZMod p) = _
    rw [ZMod.natCast_zmod_val m'_zmod, ← mul_assoc, ← IsUnit.unit_spec h_A_unit,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  obtain ⟨α01_int, hα01⟩ : (p : ℤ) ∣
      (B + (m.val : ℤ) * D - (A + (m.val : ℤ) * C) * (m'.val : ℤ)) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h_C_mod_p]
    linear_combination -h_moebius
  let α_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![A + (m.val : ℤ) * C, α01_int; (p : ℤ) * C, D - C * (m'.val : ℤ)]
  have hα01' : (p : ℤ) * α01_int =
      B + (m.val : ℤ) * D - (A + (m.val : ℤ) * C) * (m'.val : ℤ) := by linarith
  have h_det_α : α_mat.det = 1 := by
    rw [show α_mat.det = (A + (m.val : ℤ) * C) * (D - C * (m'.val : ℤ)) -
      α01_int * ((p : ℤ) * C) from Matrix.det_fin_two_of _ _ _ _]
    linear_combination hdet - C * hα01'
  let α : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨α_mat, h_det_α⟩
  have h_α_in_Γ0 : α ∈ Gamma0 N := by
    rw [CongruenceSubgroup.Gamma0_mem, show ((α : Matrix (Fin 2) (Fin 2) ℤ) 1 0) = (p : ℤ) * C
      from by simp [α, α_mat]]
    obtain ⟨c_int, hC_eq⟩ := h_C_dvd_Np
    have hpNp_eq_N : (p : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hpN
    rw [hC_eq, show ((p : ℤ) * (((N / p : ℕ) : ℤ) * c_int)) =
      ((p : ℤ) * ((N / p : ℕ) : ℤ)) * c_int from by ring, hpNp_eq_N, Int.cast_mul]
    simp
  refine ⟨m', α, h_α_in_Γ0, h_moebius, ?_⟩
  have h_raw : (!![(1 : ℤ), (m.val : ℤ); 0, (p : ℤ)] *
      (γ' : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      α_mat * !![(1 : ℤ), (m'.val : ℤ); 0, (p : ℤ)] := by
    rw [show (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![A, B; C, D] from by
      ext i j; fin_cases i <;> fin_cases j <;> rfl]
    exact descend_upper_tri_raw_matrix_identity p A B C D
      (m.val : ℤ) (m'.val : ℤ) α01_int hα01'
  refine Units.ext ?_
  change (!![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)] *
      (γ' : Matrix _ _ ℤ).map (algebraMap ℤ ℝ) : Matrix _ _ ℝ) =
      ((α : Matrix _ _ ℤ).map (algebraMap ℤ ℝ) *
        !![(1 : ℝ), (m'.val : ℝ); 0, (p : ℝ)] : Matrix _ _ ℝ)
  have hlit (v : ℕ) :
      (!![(1 : ℝ), (v : ℝ); 0, (p : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(1 : ℤ), (v : ℤ); 0, (p : ℤ)] :
        Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  rw [hlit m.val, hlit m'.val, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congr_arg (·.map (algebraMap ℤ ℝ)) h_raw

private lemma descendExtraGamma_spec
    {p N : ℕ} [NeZero p] [NeZero N]
    (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N) [NeZero (N / p)] :
    descendExtraGamma p N ∈ Gamma0 (N / p) ∧
    ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
      = !![(0 : ZMod p), -1; 1, 0]) ∧
    ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ).map
      (Int.cast : ℤ → ZMod (N / p)) = 1) := by
  have h_eq : descendExtraGamma p N =
      (descendExtraGamma_exists p hp N hpN hp_sq).choose := by
    change (if h : p.Prime ∧ p ∣ N ∧ ¬ p ^ 2 ∣ N ∧ N / p ≠ 0 then
            have : NeZero (N / p) := ⟨h.2.2.2⟩
            (descendExtraGamma_exists p h.1 N h.2.1 h.2.2.1).choose
          else 1) = _
    rw [dif_pos ⟨hp, hpN, hp_sq, NeZero.ne _⟩]
  exact h_eq ▸ (descendExtraGamma_exists p hp N hpN hp_sq).choose_spec

private lemma descend_aux_lit_real_eq_map_int (p v : ℕ) :
    (!![(1 : ℝ), (v : ℝ); 0, (p : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(1 : ℤ), (v : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

private lemma descend_aux_α_mat_in_Gamma0
    {p N : ℕ} [NeZero N] (hpN : p ∣ N) {α : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {x : ℤ} (hα_10 : (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (p : ℤ) * x)
    (hx : ((N / p : ℕ) : ℤ) ∣ x) : α ∈ Gamma0 N := by
  rw [CongruenceSubgroup.Gamma0_mem, hα_10]
  obtain ⟨y, hy⟩ := hx
  have hpNp : (p : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hpN
  rw [hy, show ((p : ℤ) * (((N / p : ℕ) : ℤ) * y)) =
    ((p : ℤ) * ((N / p : ℕ) : ℤ)) * y from by ring, hpNp]
  simp

private lemma descend_aux_lift_int_eq_to_GL
    {p : ℕ} [NeZero p] (hp : p.Prime) (m : ℕ)
    {γ' α : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    {X : GL (Fin 2) ℝ} {M_R : Matrix (Fin 2) (Fin 2) ℤ}
    (hX : (X : Matrix (Fin 2) (Fin 2) ℝ) = M_R.map (algebraMap ℤ ℝ))
    (h_int : (!![(1 : ℤ), (m : ℤ); 0, (p : ℤ)] *
        (γ' : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      (α : Matrix (Fin 2) (Fin 2) ℤ) * M_R) :
    (Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), (m : ℝ); 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
      : GL (Fin 2) ℝ) * mapGL ℝ γ' = mapGL ℝ α * X := by
  apply Units.ext
  show (!![(1 : ℝ), (m : ℝ); 0, (p : ℝ)] *
      (γ' : Matrix _ _ ℤ).map (algebraMap ℤ ℝ) : Matrix _ _ ℝ) =
      ((α : Matrix _ _ ℤ).map (algebraMap ℤ ℝ) *
        (X : Matrix _ _ ℝ) : Matrix _ _ ℝ)
  rw [hX, descend_aux_lit_real_eq_map_int p m, ← Matrix.map_mul, ← Matrix.map_mul]
  exact congr_arg (·.map (algebraMap ℤ ℝ)) h_int

private lemma descendCosetList_action_upper_tri_extra_unit_aux
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p)
    (h_unit : IsUnit ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p))) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (let A : ZMod p :=
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p)
       (target.val < p →
         A * (target.val : ZMod p) =
           ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
           (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
       (target.val = p → A = 0)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Aint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set Bint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set Cint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set Dint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ Cint := by
    have h := CongruenceSubgroup.Gamma0_mem.mp h_γ'
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hdet : Aint * Dint - Bint * Cint = 1 := by
    have h := γ'.property; rwa [Matrix.det_fin_two] at h
  set A_ext : ZMod p := (Aint : ZMod p) + (m.val : ZMod p) * (Cint : ZMod p)
    with hA_ext_def
  set u_ext : (ZMod p)ˣ := h_unit.unit
  let m'_zmod : ZMod p := (u_ext⁻¹ : (ZMod p)ˣ).val *
    ((Bint : ZMod p) + (m.val : ZMod p) * (Dint : ZMod p))
  let m' : Fin p := ⟨m'_zmod.val, ZMod.val_lt _⟩
  have h_u_val : (u_ext : ZMod p) = A_ext := IsUnit.unit_spec h_unit
  have h_moebius : A_ext * (m'.val : ZMod p) =
      (Bint : ZMod p) + (m.val : ZMod p) * (Dint : ZMod p) := by
    show A_ext * ((m'_zmod.val : ℕ) : ZMod p) = _
    rw [ZMod.natCast_zmod_val m'_zmod, ← mul_assoc, ← h_u_val, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, one_mul]
  obtain ⟨α01_int, hα01⟩ : (p : ℤ) ∣
      Bint + (m.val : ℤ) * Dint - (Aint + (m.val : ℤ) * Cint) * (m'.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination -h_moebius
  have hα01' : (p : ℤ) * α01_int =
      Bint + (m.val : ℤ) * Dint - (Aint + (m.val : ℤ) * Cint) * (m'.val : ℤ) := by lia
  let α_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![Aint + (m.val : ℤ) * Cint, α01_int;
       (p : ℤ) * Cint, Dint - Cint * (m'.val : ℤ)]
  have h_det_α : α_mat.det = 1 := by
    rw [show α_mat.det = (Aint + (m.val : ℤ) * Cint) * (Dint - Cint * (m'.val : ℤ)) -
        α01_int * ((p : ℤ) * Cint) from Matrix.det_fin_two_of _ _ _ _]
    linear_combination hdet - Cint * hα01'
  let α : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨α_mat, h_det_α⟩
  have h_α_in_Γ0 : α ∈ Gamma0 N :=
    descend_aux_α_mat_in_Gamma0 (x := Cint) hpN
      (show α_mat 1 0 = (p : ℤ) * Cint by simp [α_mat]) h_C_dvd_Np
  have h_m_lt_dccn : m'.val < descendCosetCount p N := by
    have := m'.isLt; simp [descendCosetCount, hp_sq]
  refine ⟨⟨m'.val, h_m_lt_dccn⟩, α, h_α_in_Γ0,
    ⟨fun _ ↦ h_moebius, fun h_eq ↦ by have := m'.isLt; simp at h_eq; lia⟩, ?_⟩
  rw [show descendCosetList p N hp ⟨m'.val, h_m_lt_dccn⟩ = _ from
    dif_pos (show (⟨m'.val, h_m_lt_dccn⟩ : Fin _).val < p from m'.isLt)]
  refine descend_aux_lift_int_eq_to_GL hp m.val (M_R := !![(1:ℤ), (m'.val:ℤ); 0, (p:ℤ)])
    (descend_aux_lit_real_eq_map_int p m'.val) ?_
  have h_γ'_eq : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![Aint, Bint; Cint, Dint] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [h_γ'_eq]
  exact descend_upper_tri_raw_matrix_identity p Aint Bint Cint Dint
    (m.val : ℤ) (m'.val : ℤ) α01_int hα01'

private lemma descendCosetList_action_upper_tri_extra_zero_aux
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p)
    (h_A_ext_zero : ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p) = 0) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (let A : ZMod p :=
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p)
       (target.val < p →
         A * (target.val : ZMod p) =
           ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
           (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
       (target.val = p → A = 0)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target) := by
  haveI : Fact p.Prime := ⟨hp⟩
  set Aint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set Bint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set Cint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set Dint := (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_C_dvd_Np : ((N / p : ℕ) : ℤ) ∣ Cint := by
    have h := CongruenceSubgroup.Gamma0_mem.mp h_γ'
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have hdet : Aint * Dint - Bint * Cint = 1 := by
    have h := γ'.property; rwa [Matrix.det_fin_two] at h
  set γ_p := descendExtraGamma p N
  obtain ⟨h_γ_p_mem, h_γ_p_modp, _⟩ := descendExtraGamma_spec hp hpN hp_sq
  set aint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set bint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  set cint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set dint := (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_a_p : (aint : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_modp 0) 0
  have h_b_p : (bint : ZMod p) = -1 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_modp 0) 1
  have h_c_dvd_Np : ((N / p : ℕ) : ℤ) ∣ cint := by
    have h := CongruenceSubgroup.Gamma0_mem.mp h_γ_p_mem
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  have h_det_γp : aint * dint - bint * cint = 1 := by
    have h := γ_p.property; rwa [Matrix.det_fin_two] at h
  obtain ⟨α01_int, hα01⟩ : (p : ℤ) ∣
      aint * (Bint + (m.val : ℤ) * Dint) - bint * (Aint + (m.val : ℤ) * Cint) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h_a_p, h_b_p]
    linear_combination h_A_ext_zero
  have hα01' : (p : ℤ) * α01_int =
      aint * (Bint + (m.val : ℤ) * Dint) - bint * (Aint + (m.val : ℤ) * Cint) := by lia
  let α_mat : Matrix (Fin 2) (Fin 2) ℤ :=
    !![Aint * dint - Bint * cint + (m.val : ℤ) * (Cint * dint - Dint * cint), α01_int;
       (p : ℤ) * (Cint * dint - Dint * cint), Dint * aint - Cint * bint]
  have h_det_α : α_mat.det = 1 := by
    rw [show α_mat.det = (Aint * dint - Bint * cint + (m.val : ℤ) * (Cint * dint - Dint * cint)) *
        (Dint * aint - Cint * bint) - α01_int * ((p : ℤ) * (Cint * dint - Dint * cint))
        from Matrix.det_fin_two_of _ _ _ _,
      show α01_int * ((p : ℤ) * (Cint * dint - Dint * cint)) =
        (p : ℤ) * α01_int * (Cint * dint - Dint * cint) from by ring, hα01']
    nlinarith [hdet, h_det_γp, mul_comm Aint Dint, mul_comm Bint Cint,
      mul_comm aint dint, mul_comm bint cint]
  let α : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨α_mat, h_det_α⟩
  have h_α_in_Γ0 : α ∈ Gamma0 N :=
    descend_aux_α_mat_in_Gamma0 (x := Cint * dint - Dint * cint) hpN
      (show α_mat 1 0 = (p : ℤ) * (Cint * dint - Dint * cint) by simp [α_mat])
      (by obtain ⟨C', hC'⟩ := h_C_dvd_Np
          obtain ⟨c', hc'⟩ := h_c_dvd_Np
          exact ⟨C' * dint - Dint * c', by rw [hC', hc']; ring⟩)
  have h_p_lt_dccn : p < descendCosetCount p N := by simp [descendCosetCount, hp_sq]
  refine ⟨⟨p, h_p_lt_dccn⟩, α, h_α_in_Γ0,
    ⟨fun h_lt ↦ by simp at h_lt, fun _ ↦ h_A_ext_zero⟩, ?_⟩
  rw [show descendCosetList p N hp ⟨p, h_p_lt_dccn⟩ = _ from dif_neg (lt_irrefl p)]
  have h_γ'_eq : (γ' : Matrix (Fin 2) (Fin 2) ℤ) = !![Aint, Bint; Cint, Dint] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h_γ_p_eq : (γ_p : Matrix (Fin 2) (Fin 2) ℤ) = !![aint, bint; cint, dint] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  have h_raw : (!![(1 : ℤ), (m.val : ℤ); 0, (p : ℤ)] *
      (γ' : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) =
      α_mat * (!![(1 : ℤ), 0; 0, (p : ℤ)] * (γ_p : Matrix (Fin 2) (Fin 2) ℤ)) := by
    have h10p_γp : (!![(1 : ℤ), 0; 0, (p : ℤ)] * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) :
          Matrix (Fin 2) (Fin 2) ℤ) =
        !![aint, bint; (p : ℤ) * cint, (p : ℤ) * dint] := by
      rw [h_γ_p_eq]
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h10p_γp, h_γ'_eq]
    exact descend_extra_raw_matrix_identity p Aint Bint Cint Dint
      aint bint cint dint (m.val : ℤ) α01_int h_det_γp hα01'
  refine descend_aux_lift_int_eq_to_GL hp m.val
    (M_R := !![(1:ℤ), 0; 0, (p:ℤ)] * (γ_p : Matrix (Fin 2) (Fin 2) ℤ)) ?_ h_raw
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.map_mul,
    show (!![(1:ℝ), 0; 0, (p:ℝ)] : Matrix (Fin 2) (Fin 2) ℝ) =
        (!![(1:ℤ), 0; 0, (p:ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) by
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]]
  rfl

/-- **T5a-3a-extra** (Miyake Lemma 4.5.11, p. 144, p∤M case): given `γ' ∈ Γ_0(N/p)` and
`m : Fin p`, produces a target index in `Fin (descendCosetCount p N)` and `α ∈ Γ_0(N)`
satisfying the double-coset factorisation `[1, m; 0, p] · γ' = α · descendCosetList p N hp target`.
When `A := a + m·c ≠ 0 mod p` the target lies in `Fin p`; when `A = 0 mod p` the target is
the extra coset `p`. -/
theorem descendCosetList_action_upper_tri_extra
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (let A : ZMod p :=
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
        (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p)
       (target.val < p →
         A * (target.val : ZMod p) =
           ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) +
           (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) ∧
       (target.val = p → A = 0)) ∧
      ((Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rcases Classical.em (IsUnit (((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) +
      (m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod p))) with h | h
  · exact descendCosetList_action_upper_tri_extra_unit_aux p hp hpN hp_sq γ' h_γ' m h
  · exact descendCosetList_action_upper_tri_extra_zero_aux p hp hpN hp_sq γ' h_γ' m
      (by rwa [isUnit_iff_ne_zero, ne_eq, not_not] at h)

/-- **T5a-3a: Matrix identity for the upper-triangular case**
(`γ_v = [1, m; 0, p]` with `m < p`, i.e. `v ∈ Fin p ⊂ Fin (descendCosetCount p N)`).

For `γ' = [a, b; c·(N/p), d] ∈ Γ_0(N/p)`:
`[1, m; 0, p] · γ' = [a + m·c·(N/p), b + m·d; c·N, p·d]`.

There exists a target index `target : Fin (descendCosetCount p N)` and an integer matrix
`α ∈ Γ_0(N)` such that
`[1, m; 0, p] · mapGL γ' = mapGL α · descendCosetList p N hp target`. -/
theorem descendCosetList_action_upper_tri
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (m : Fin p) :
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : α ∈ Gamma0 N),
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (m.val : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ) * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target := by
  by_cases hp_sq : p ^ 2 ∣ N
  · obtain ⟨m', α, h_mem, _h_canonical, h_eq⟩ :=
      descendCosetList_action_upper_tri_clean p hp hpN hp_sq γ' h_γ' m
    have h_count : descendCosetCount p N = p := by
      simp [descendCosetCount, hp_sq]
    have h_lt : m'.val < descendCosetCount p N := by lia
    refine ⟨⟨m'.val, h_lt⟩, α, h_mem, ?_⟩
    rw [h_eq]
    exact congr_arg _ (by simp [descendCosetList, m'.isLt])
  · obtain ⟨target, α, h_mem, _, h_eq⟩ :=
      descendCosetList_action_upper_tri_extra p hp hpN hp_sq γ' h_γ' m
    exact ⟨target, α, h_mem, h_eq⟩

/-- **T5a-3b: Matrix identity for the extra rep case** (only `p² ∤ N`).

The extra rep is `descendCosetList p N hp ⟨p, hpExtra⟩` where
`hpExtra : p < descendCosetCount p N` follows from `¬ p² ∣ N`.
Concretely, this rep is `[1, 0; 0, p] · mapGL ℝ γ_p^(p)` (NOT `[p,0;0,1]`,
which is outside the descent double coset).

For `γ' ∈ Γ_0(N/p)`, there exist a target index in `Fin (descendCosetCount p N)`
and `α ∈ Γ_0(N)` such that
`(extra rep) · mapGL γ' = mapGL α · descendCosetList p N hp target`. -/
theorem descendCosetList_action_extra
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (hp_sq : ¬ p ^ 2 ∣ N)
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p)) :
    let hpExtra : p < descendCosetCount p N := by
      simp [descendCosetCount, hp_sq]
    ∃ (target : Fin (descendCosetCount p N))
      (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) (_ : α ∈ Gamma0 N),
      descendCosetList p N hp ⟨p, hpExtra⟩ * mapGL ℝ γ' =
      mapGL ℝ α * descendCosetList p N hp target := by
  intro hpExtra
  obtain ⟨target, α, hα_mem, h_eq⟩ :=
    descendCosetList_action_upper_tri p hp hpN (descendExtraGamma p N * γ')
      (Subgroup.mul_mem _ (descendExtraGamma_spec hp hpN hp_sq).1 h_γ') ⟨0, hp.pos⟩
  exact ⟨target, α, hα_mem, by grind [descendCosetList]⟩

/-- **T5a-3c: Möbius-type permutation is injective at level `Γ_0(N/p)`**.

For `γ' = [a, b; c·(N/p), d] ∈ Γ_0(N/p)`, the map `m → m · d mod p` on
`Fin p` is injective.  Reason: from `det γ' = 1`, we have
`a·d − b·c·(N/p) = 1`, which forces `gcd(d, p) = 1` (else `p | 1`),
hence `d` is invertible mod `p`.

This is the building block for the permutation `σ` in `descendCosetList_action`
(`m ↦ m·d mod p` extended to the proper Möbius via affine shift).
Analogous to the existing project's `moebiusFin'_injective` at
`HeckeT_n.lean:117`. -/
theorem descendCosetList_moebius_inj
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : p ^ 2 ∣ N)
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p)) :
    Function.Injective (fun m : Fin p =>
      ((m.val : ZMod p) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdet : (γ' : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := γ'.property
  rw [Matrix.det_fin_two] at hdet
  have h_c_dvd : ((N / p : ℕ) : ℤ) ∣ (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp h_γ')
  have hp_dvd_Np : (p : ℤ) ∣ ((N / p : ℕ) : ℤ) := by
    obtain ⟨k, hk⟩ := hp_sq
    refine ⟨k, ?_⟩
    exact_mod_cast by rw [hk, sq, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  have h_a_d_mod_p :
      (((γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) *
       ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod p)) = 1 := by
    have := congr_arg (Int.cast : ℤ → ZMod p) hdet
    push_cast at this
    rwa [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (dvd_trans hp_dvd_Np h_c_dvd),
      mul_zero, sub_zero] at this
  intro m₁ m₂ h_eq
  simp only at h_eq
  exact Fin.ext (ZMod.val_natCast_of_lt m₁.isLt ▸ ZMod.val_natCast_of_lt m₂.isLt ▸
    congr_arg ZMod.val (mul_right_cancel₀
      (IsUnit.ne_zero (IsUnit.of_mul_eq_one_right _ h_a_d_mod_p)) h_eq))

private lemma descendCosetList_apply_lt {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : v.val < p) :
    descendCosetList p N hp v =
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) := by
  unfold descendCosetList
  exact dif_pos hv

private lemma descendCosetList_apply_extra {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) :
    descendCosetList p N hp v =
      Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℝ), 0; 0, (p : ℝ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) *
        mapGL ℝ (descendExtraGamma p N) := by
  unfold descendCosetList
  exact dif_neg hv

private lemma descendCosetList_lt_matrix {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : v.val < p) :
    (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)] := by
  rw [descendCosetList_apply_lt hp hv]
  simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private lemma descendCosetCount_val_eq_p {p N : ℕ}
    (v : Fin (descendCosetCount p N)) (hv : ¬ v.val < p) : v.val = p := by
  have hlt := v.isLt
  simp only [descendCosetCount] at hlt
  split_ifs at hlt <;> lia

private lemma not_p_sq_dvd_of_not_lt {p N : ℕ}
    {v : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) : ¬ p ^ 2 ∣ N := by
  intro h
  have hlt := v.isLt
  simp only [descendCosetCount, h, ite_true] at hlt
  lia

private lemma p_lt_descendCosetCount_of_not_p_sq_dvd {p N : ℕ}
    (hp_sq : ¬ p ^ 2 ∣ N) : p < descendCosetCount p N := by
  simp [descendCosetCount, hp_sq]

private lemma isUnit_p_zmod_of_not_p_sq_dvd {p N : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N) :
    IsUnit (p : ZMod (N / p)) := by
  rw [ZMod.isUnit_prime_iff_not_dvd hp]
  intro h_dvd
  exact hp_sq <| (Nat.mul_div_cancel' hpN).symm ▸ pow_two p ▸ Nat.mul_dvd_mul_left _ h_dvd

/-- For `β ∈ Γ_0(N)` and target index `t.val < p`, if the GL₂(ℝ) equation
`[1, v; 0, p] · γ' = β · [1, t; 0, p]` holds, then `β 1 1 ≡ γ' 1 1 (mod N/p)`. -/
private lemma descend_diamond_compat_upper_target
    {N : ℕ} [NeZero N]
    {p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {γ' β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N)
    (t : ℕ)
    (h_11 : (p : ℤ) * (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
        (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (t : ℤ) +
        (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (p : ℤ)) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) := by
  have h_β_10_dvd_N : (N : ℤ) ∣ (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by exact_mod_cast CongruenceSubgroup.Gamma0_mem.mp hβ)
  obtain ⟨k, hk⟩ := h_β_10_dvd_N
  have hpNp : (p : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hpN
  have hβ11_sub : (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -((N / p : ℕ) : ℤ) * k * (t : ℤ) := by
    apply mul_left_cancel₀ (by exact_mod_cast hp.ne_zero : (p : ℤ) ≠ 0)
    rw [hk] at h_11
    linear_combination -h_11 + k * (t : ℤ) * hpNp
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, hβ11_sub]
  exact ⟨-(k * (t : ℤ)), by ring⟩

/-- For β ∈ Γ_0(N), if `(p : ZMod (N/p)) * γ' 1 1 = β 1 1 * p` and p is invertible
mod N/p (i.e. `¬ p² ∣ N`), then `β 1 1 ≡ γ' 1 1 (mod N/p)`. -/
private lemma descend_diamond_compat_from_zmod
    {N p : ℕ} [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    {β γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (h_zmod : (p : ZMod (N / p)) * ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) * (p : ZMod (N / p))) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) :=
  ((isUnit_p_zmod_of_not_p_sq_dvd hp hpN hp_sq).mul_left_cancel
    (h_zmod.trans (mul_comm _ _))).symm

private lemma beta_10_zmod_eq_zero
    {N p : ℕ} [NeZero N] (hpN : p ∣ N)
    {β : Matrix.SpecialLinearGroup (Fin 2) ℤ} (hβ : β ∈ Gamma0 N) :
    ((β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (N / p)) = 0 := by
  have h_N_dvd : (N : ℤ) ∣ (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by exact_mod_cast CongruenceSubgroup.Gamma0_mem.mp hβ)
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr ?_
  exact_mod_cast dvd_trans
    (by exact_mod_cast Nat.div_dvd_of_dvd hpN : ((N / p : ℕ) : ℤ) ∣ N) h_N_dvd

/-- Matrix coercion equality from `mapGL` over ℤ to ℝ. -/
private lemma mapGL_coe_matrix_apply (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) (i j : Fin 2) :
    ((mapGL ℝ α : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
      ((α : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) := by
  simp only [Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply, algebraMap_int_eq, eq_intCast]

/-- Matrix entries of `descendCosetList p N hp ⟨p, _⟩` (the extra rep). -/
private lemma descendCosetList_extra_matrix_entry
    {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : ¬ v.val < p) (i j : Fin 2) :
    (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ) i j =
      (!![(1 : ℝ), 0; 0, (p : ℝ)] *
        ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℝ))) i j := by
  rw [descendCosetList_apply_extra hp hv]
  simp [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, mapGL, toGL, map_apply_coe,
    RingHom.mapMatrix_apply]

private lemma descendCosetList_per_v_witness
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p))
    (v : Fin (descendCosetCount p N)) :
    ∃ (t : Fin (descendCosetCount p N))
      (β : Matrix.SpecialLinearGroup (Fin 2) ℤ) (_ : β ∈ Gamma0 N),
      (descendCosetList p N hp v * mapGL ℝ γ' =
        mapGL ℝ β * descendCosetList p N hp t) ∧
      (((β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
        ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p))) := by
  by_cases hv : v.val < p
  · by_cases hp_sq : p ^ 2 ∣ N
    · obtain ⟨m', β, hβ, _, heq⟩ :=
        descendCosetList_action_upper_tri_clean p hp hpN hp_sq γ' h_γ' ⟨v.val, hv⟩
      have h_dcc_eq : descendCosetCount p N = p := by simp [descendCosetCount, hp_sq]
      have h_m'lt : m'.val < descendCosetCount p N := h_dcc_eq.symm ▸ m'.isLt
      have h_m'lt_p : (⟨m'.val, h_m'lt⟩ : Fin (descendCosetCount p N)).val < p := m'.isLt
      refine ⟨⟨m'.val, h_m'lt⟩, β, hβ, ?_, ?_⟩
      · rwa [descendCosetList_apply_lt hp hv, descendCosetList_apply_lt hp h_m'lt_p]
      · refine descend_diamond_compat_upper_target hp hpN hβ m'.val ?_
        have h_ℝ := congr_arg Units.val heq
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.SpecialLinearGroup.mapGL_coe_matrix,
          Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
        have h_11r := congr_fun (congr_fun h_ℝ 1) 1
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at h_11r
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
        exact_mod_cast h_11r
    · obtain ⟨t, β, hβ, _, heq⟩ :=
        descendCosetList_action_upper_tri_extra p hp hpN hp_sq γ' h_γ' ⟨v.val, hv⟩
      refine ⟨t, β, hβ, by rwa [descendCosetList_apply_lt hp hv], ?_⟩
      by_cases ht : t.val < p
      · refine descend_diamond_compat_upper_target hp hpN hβ t.val ?_
        have h_ℝ := congr_arg Units.val heq
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.SpecialLinearGroup.mapGL_coe_matrix,
          Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
        have h_11r := congr_fun (congr_fun h_ℝ 1) 1
        have hdcl_t11 : (descendCosetList p N hp t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p := by
          rw [descendCosetList_lt_matrix hp ht]
          simp
        have hdcl_t01 : (descendCosetList p N hp t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
            (t.val : ℝ) := by
          rw [descendCosetList_lt_matrix hp ht]
          simp
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
          hdcl_t01, hdcl_t11, algebraMap_int_eq] at h_11r
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
        exact_mod_cast h_11r
      · refine descend_diamond_compat_from_zmod hp hpN hp_sq ?_
        set γ_p := descendExtraGamma p N
        have h_γ_p_spec := (descendExtraGamma_spec hp hpN hp_sq).2.2
        rw [descendCosetList_apply_extra hp ht] at heq
        have h_ℝ := congr_arg Units.val heq
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
          Matrix.SpecialLinearGroup.mapGL_coe_matrix,
          Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
        have h_11r := congr_fun (congr_fun h_ℝ 1) 1
        simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at h_11r
        have h_11 : (p : ℤ) * (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
            (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
            (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
              (p * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
          norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
          exact_mod_cast h_11r
        have hγ_p_01 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod (N/p)) = 0 := by
          simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 0) 1
        have hγ_p_11 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N/p)) = 1 := by
          simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 1
        have h_β_10_mod := beta_10_zmod_eq_zero (p := p) hpN hβ
        have h_zmod := congr_arg (Int.cast : ℤ → ZMod (N/p)) h_11
        push_cast at h_zmod
        rw [hγ_p_01, hγ_p_11, h_β_10_mod] at h_zmod
        linear_combination h_zmod
  · have hp_sq : ¬ p ^ 2 ∣ N := not_p_sq_dvd_of_not_lt hv
    have hpExtra : p < descendCosetCount p N := p_lt_descendCosetCount_of_not_p_sq_dvd hp_sq
    have hv_extra : v = ⟨p, hpExtra⟩ := Fin.ext (descendCosetCount_val_eq_p v hv)
    have h_extra_not_lt :
        ¬ (⟨p, hpExtra⟩ : Fin (descendCosetCount p N)).val < p := lt_irrefl p
    obtain ⟨t, β, hβ, heq⟩ :=
      descendCosetList_action_extra p hp hpN hp_sq γ' h_γ'
    refine ⟨t, β, hβ, by rwa [hv_extra], ?_⟩
    refine descend_diamond_compat_from_zmod hp hpN hp_sq ?_
    set γ_p := descendExtraGamma p N
    have h_γ_p_spec := (descendExtraGamma_spec hp hpN hp_sq).2.2
    rw [descendCosetList_apply_extra hp h_extra_not_lt] at heq
    have hγ_p_10 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod (N/p)) = 0 := by
      simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 0
    have hγ_p_11 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N/p)) = 1 := by
      simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 1) 1
    have hγ_p_01 : ((γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod (N/p)) = 0 := by
      simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_p_spec 0) 1
    have h_β_10_mod := beta_10_zmod_eq_zero (p := p) hpN hβ
    by_cases ht : t.val < p
    · have hdcl_t11 : (descendCosetList p N hp t : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = p := by
        rw [descendCosetList_lt_matrix hp ht]
        simp
      have hdcl_t01 : (descendCosetList p N hp t : Matrix (Fin 2) (Fin 2) ℝ) 0 1 =
          (t.val : ℝ) := by
        rw [descendCosetList_lt_matrix hp ht]
        simp
      have h_ℝ := congr_arg Units.val heq
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
      have h_11r := congr_fun (congr_fun h_ℝ 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
        hdcl_t01, hdcl_t11, algebraMap_int_eq] at h_11r
      have h_11 : (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
            (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
          (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
            (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
          (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * t.val +
          (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * p := by
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
        exact_mod_cast h_11r
      have h_zmod := congr_arg (Int.cast : ℤ → ZMod (N/p)) h_11
      push_cast at h_zmod
      rw [hγ_p_10, hγ_p_11, h_β_10_mod] at h_zmod
      linear_combination h_zmod
    · rw [descendCosetList_apply_extra hp ht] at heq
      have h_ℝ := congr_arg Units.val heq
      simp only [Units.val_mul, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.SpecialLinearGroup.mapGL_coe_matrix,
        Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h_ℝ
      have h_11r := congr_fun (congr_fun h_ℝ 1) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] at h_11r
      have h_11 : (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 0 *
            (γ' : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
          (p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
            (γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 =
          (β : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 0 1 +
          (β : Matrix (Fin 2) (Fin 2) ℤ) 1 1 *
            ((p : ℤ) * (γ_p : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h_11r
        exact_mod_cast h_11r
      have h_zmod := congr_arg (Int.cast : ℤ → ZMod (N/p)) h_11
      push_cast at h_zmod
      rw [hγ_p_10, hγ_p_11, h_β_10_mod, hγ_p_01] at h_zmod
      linear_combination h_zmod

private lemma descendCosetList_cross_regular_extra_aux
    {N : ℕ} [NeZero N] (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    {va vb : Fin (descendCosetCount p N)} (hva : va.val < p) (hvb : ¬ vb.val < p)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) ≠
      (mapGL ℝ α : GL (Fin 2) ℝ) * descendCosetList p N hp vb := by
  intro heq_cross
  have hp_sq : ¬ p ^ 2 ∣ N := not_p_sq_dvd_of_not_lt hvb
  have hpExtra : p < descendCosetCount p N := p_lt_descendCosetCount_of_not_p_sq_dvd hp_sq
  have h_γp_spec := (descendExtraGamma_spec hp hpN hp_sq).2.1
  have h_γp_00 : ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γp_spec 0) 0
  have h_vb_eq_fin : vb = ⟨p, hpExtra⟩ := Fin.ext (descendCosetCount_val_eq_p vb hvb)
  have hLHS_00 : (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = 1 := by
    rw [descendCosetList_lt_matrix hp hva]
    simp
  have hdcl_extra_00 : (descendCosetList p N hp ⟨p, hpExtra⟩ : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) := by
    rw [descendCosetList_extra_matrix_entry hp (lt_irrefl p) 0 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdcl_extra_10 : (descendCosetList p N hp ⟨p, hpExtra⟩ : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      (p : ℝ) * ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) := by
    rw [descendCosetList_extra_matrix_entry hp (lt_irrefl p) 1 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hRHS_00 := congr_fun (congr_fun heq_cross 0) 0
  rw [hLHS_00, h_vb_eq_fin, Matrix.mul_apply, Fin.sum_univ_two,
    hdcl_extra_00, hdcl_extra_10,
    mapGL_coe_matrix_apply _ 0 0, mapGL_coe_matrix_apply _ 0 1] at hRHS_00
  have h1_int : (1 : ℤ) =
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
        (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 +
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
        (p * (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    have : (1 : ℝ) =
        ((α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) *
          ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) +
        ((α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) *
          ((p : ℝ) * ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ)) := by
      linarith
    exact_mod_cast this
  have h_γp_00_dvd : (p : ℤ) ∣ (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast h_γp_00)
  have hp_dvd_one : (p : ℤ) ∣ 1 := by
    rw [h1_int]
    exact dvd_add (dvd_mul_of_dvd_right h_γp_00_dvd _)
      ⟨(α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 *
        (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by ring⟩
  linarith [Int.le_of_dvd one_pos hp_dvd_one, show (2 : ℤ) ≤ p by exact_mod_cast hp.two_le]

private lemma descendCosetList_cross_extra_regular_aux
    {N : ℕ} [NeZero N] (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    {va vb : Fin (descendCosetCount p N)} (hva : ¬ va.val < p) (hvb : vb.val < p)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) ≠
      (mapGL ℝ α : GL (Fin 2) ℝ) * descendCosetList p N hp vb := by
  intro h_mat
  have hp_sq : ¬ p ^ 2 ∣ N := not_p_sq_dvd_of_not_lt hva
  have hpExtra : p < descendCosetCount p N := p_lt_descendCosetCount_of_not_p_sq_dvd hp_sq
  have hva_extra : va = ⟨p, hpExtra⟩ := Fin.ext (descendCosetCount_val_eq_p va hva)
  have h_γp_spec := (descendExtraGamma_spec hp hpN hp_sq).2.1
  have h_γp_00 : ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γp_spec 0) 0
  have hdcl_va_00 : (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) 0 0 =
      ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℝ) := by
    rw [hva_extra, descendCosetList_extra_matrix_entry hp (lt_irrefl p) 0 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdcl_va_10 : (descendCosetList p N hp va : Matrix (Fin 2) (Fin 2) ℝ) 1 0 =
      (p : ℝ) * ((descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℝ) := by
    rw [hva_extra, descendCosetList_extra_matrix_entry hp (lt_irrefl p) 1 0]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h00 := congr_fun (congr_fun h_mat 0) 0
  have h10 := congr_fun (congr_fun h_mat 1) 0
  rw [hdcl_va_00, descendCosetList_lt_matrix hp hvb] at h00
  rw [hdcl_va_10, descendCosetList_lt_matrix hp hvb] at h10
  simp only [Matrix.mul_apply, Fin.sum_univ_two,
    mapGL_coe_matrix_apply _ 0 0, mapGL_coe_matrix_apply _ 0 1,
    mapGL_coe_matrix_apply _ 1 0, mapGL_coe_matrix_apply _ 1 1,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h10
  have hα00_eq : (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
      (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    have : (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
        (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * 1 +
        (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * 0 := by exact_mod_cast h00
    lia
  have hα10_eq : (p : ℤ) * (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h10' : (p : ℤ) * (descendExtraGamma p N : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
        (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * 1 +
        (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * 0 := by exact_mod_cast h10
    lia
  have hα00_dvd : (p : ℤ) ∣ (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [hα00_eq]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by exact_mod_cast h_γp_00)
  have hα10_dvd : (p : ℤ) ∣ (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := ⟨_, hα10_eq.symm⟩
  have hdet : (α : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (α : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (α : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact α.property
  have hp_dvd_one : (p : ℤ) ∣ 1 := by
    rw [← hdet]
    exact dvd_sub (dvd_mul_of_dvd_left hα00_dvd _) (dvd_mul_of_dvd_right hα10_dvd _)
  linarith [Int.le_of_dvd one_pos hp_dvd_one, show (2 : ℤ) ≤ p by exact_mod_cast hp.two_le]

private lemma descendCosetList_sigma_aux_injective
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (α_fn : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (σ_fn : Fin (descendCosetCount p N) → Fin (descendCosetCount p N))
    (h_eq_fn : ∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ (α_fn v) * descendCosetList p N hp (σ_fn v)) :
    Function.Injective σ_fn := by
  intro v₁ v₂ h_σ
  have heq₁ := h_eq_fn v₁
  have heq₂ := h_eq_fn v₂
  rw [h_σ] at heq₁
  have h_gl : descendCosetList p N hp v₁ =
      mapGL ℝ (α_fn v₁ * (α_fn v₂)⁻¹) * descendCosetList p N hp v₂ :=
    mul_right_cancel (b := mapGL ℝ γ') <| by
      rw [mul_assoc, heq₂, ← mul_assoc, ← map_mul]
      simp [heq₁]
  have h_mat : (descendCosetList p N hp v₁ : Matrix (Fin 2) (Fin 2) ℝ) =
      (mapGL ℝ (α_fn v₁ * (α_fn v₂)⁻¹) : GL (Fin 2) ℝ) *
      descendCosetList p N hp v₂ := congr_arg Units.val h_gl
  by_cases hv₁ : v₁.val < p
  · by_cases hv₂ : v₂.val < p
    · set ξ := (α_fn v₁ * (α_fn v₂)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      rw [descendCosetList_lt_matrix hp hv₁, descendCosetList_lt_matrix hp hv₂] at h_mat
      have h00 := congr_fun (congr_fun h_mat 0) 0
      have h01 := congr_fun (congr_fun h_mat 0) 1
      simp only [Matrix.mul_apply, Fin.sum_univ_two,
        mapGL_coe_matrix_apply ξ 0 0, mapGL_coe_matrix_apply ξ 0 1,
        Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h00 h01
      have hcast00 : (1 : ℤ) = (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * 1 +
          (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * 0 := by exact_mod_cast h00
      have hcast01 : (v₁.val : ℤ) = (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * v₂.val +
          (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * p := by exact_mod_cast h01
      have hξ00 : (ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 := by lia
      rw [hξ00, one_mul] at hcast01
      have hv1z : (v₁.val : ℤ) < p := by exact_mod_cast hv₁
      have hv2z : (v₂.val : ℤ) < p := by exact_mod_cast hv₂
      have hdvd : (p : ℤ) ∣ ((v₁.val : ℤ) - v₂.val) :=
        ⟨(ξ : Matrix (Fin 2) (Fin 2) ℤ) 0 1, by linarith⟩
      have habs : |((v₁.val : ℤ) - v₂.val)| < p := abs_lt.mpr
        ⟨by linarith [Int.natCast_nonneg v₂.val],
          by linarith [Int.natCast_nonneg v₁.val]⟩
      exact Fin.ext <| by
        exact_mod_cast (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hdvd habs))
    · exact absurd h_mat (descendCosetList_cross_regular_extra_aux p hp hpN hv₁ hv₂ _)
  · by_cases hv₂ : v₂.val < p
    · exact absurd h_mat (descendCosetList_cross_extra_regular_aux p hp hpN hv₁ hv₂ _)
    · exact Fin.ext (by
        have := descendCosetCount_val_eq_p v₁ hv₁
        have := descendCosetCount_val_eq_p v₂ hv₂
        lia)

/-- **T5a-3: Action property of the descent cosets at Γ_0(N/p) → Γ_0(N)**.

For every `γ' ∈ Γ_0(N/p)`, there exist a permutation `σ` of the coset
index set `Fin (descendCosetCount p N)` and matrices `α_v ∈ Γ_0(N)`
such that
`descendCosetList p N hp v · mapGL γ' = mapGL (α_v) · descendCosetList p N hp (σ v)`
as products in `GL_2(ℝ)`, together with the diamond compatibility
`ZMod.unitsMap (Gamma0MapUnits α_v) = Gamma0MapUnits γ'`. -/
theorem descendCosetList_action
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma0 (N / p)) :
    ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
      (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (h_mem : ∀ v, α v ∈ Gamma0 N),
      (∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
            mapGL ℝ (α v) * descendCosetList p N hp (σ v)) ∧
      (∀ v, ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)
          (Gamma0MapUnits (N := N) ⟨α v, h_mem v⟩) =
          Gamma0MapUnits (N := N / p) ⟨γ', h_γ'⟩) := by
  let per_v := descendCosetList_per_v_witness p hp hpN γ' h_γ'
  let σ_fn : Fin (descendCosetCount p N) → Fin (descendCosetCount p N) :=
    fun v ↦ (per_v v).choose
  let α_fn : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    fun v ↦ (per_v v).choose_spec.choose
  have h_mem_fn : ∀ v, α_fn v ∈ Gamma0 N :=
    fun v ↦ (per_v v).choose_spec.choose_spec.choose
  have h_eq_fn : ∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
      mapGL ℝ (α_fn v) * descendCosetList p N hp (σ_fn v) :=
    fun v ↦ (per_v v).choose_spec.choose_spec.choose_spec.1
  have h_diamond_fn : ∀ v,
      ((α_fn v : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) :=
    fun v ↦ (per_v v).choose_spec.choose_spec.choose_spec.2
  have h_inj : Function.Injective σ_fn :=
    descendCosetList_sigma_aux_injective p hp hpN γ' α_fn σ_fn h_eq_fn
  let σ : Equiv.Perm (Fin (descendCosetCount p N)) :=
    Equiv.ofBijective σ_fn ⟨h_inj, Finite.injective_iff_surjective.mp h_inj⟩
  refine ⟨σ, α_fn, h_mem_fn, h_eq_fn, fun v ↦ ?_⟩
  apply Units.ext
  simp only [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpN)]
  exact h_diamond_fn v

/-- For `g : GL (Fin 2) ℝ` with positive determinant, `UpperHalfPlane.σ g` is the identity. -/
lemma multipass_sigma_eq_id_of_det_pos (g : GL (Fin 2) ℝ)
    (hg : 0 < g.det.val) : UpperHalfPlane.σ g = RingHom.id ℂ := by
  simp only [UpperHalfPlane.σ, if_pos hg]

/-- Any two ring homomorphisms `ℤ →+* R` are equal. -/
lemma multipass_int_castRingHom_unique {R : Type*} [NonAssocSemiring R]
    (φ ψ : ℤ →+* R) : φ = ψ := Subsingleton.elim _ _

/-- `(if p² ∣ N then p - 1 else p) + 1 = descendCosetCount p N`. -/
lemma multipass_d_succ_eq_descendCosetCount (p N : ℕ) [NeZero p]
    (hp : p.Prime) :
    (if p ^ 2 ∣ N then p - 1 else p) + 1 = descendCosetCount p N := by
  unfold descendCosetCount
  split_ifs
  · exact Nat.sub_add_cancel hp.pos
  · rfl

/-- For `γ ∈ Γ₁(N)`, there exists `hγ' : γ ∈ Γ₀(N)` with `Gamma0MapUnits ⟨γ, hγ'⟩ = 1`. -/
lemma multipass_char_trivial_on_Gamma1 {N : ℕ} [NeZero N]
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hγ : γ ∈ Gamma1 N) :
    ∃ hγ' : γ ∈ Gamma0 N,
      Gamma0MapUnits (N := N) ⟨γ, hγ'⟩ = 1 := by
  rw [Gamma1_mem] at hγ
  obtain ⟨_h00, h11, h10⟩ := hγ
  exact ⟨Gamma0_mem.mpr h10, by ext; simpa [Gamma0MapUnits_val, Gamma0Map] using h11⟩

/-- For `a b d : ZMod p` and `m : Fin p`, `(a⁻¹ * (b + m.val * d)).val < p`. -/
lemma multipass_moebius_fin_p_well_defined (p : ℕ) [Fact p.Prime]
    (a b d : ZMod p) (m : Fin p) :
    (a⁻¹ * (b + (m.val : ZMod p) * d)).val < p :=
  ZMod.val_lt _

/-- If `p² ∣ N` and `a * m' ≡ b + m * d (mod p)`, then `p ∣ b + m·d − (a + m·c·(N/p))·m'`. -/
lemma multipass_alpha_integer_entries_p_sq_dvd_N
    (p N : ℕ) [NeZero p] (hp : p.Prime)
    (hp_sq : p ^ 2 ∣ N)
    (a b c d : ℤ) (m m' : Fin p)
    (h_moebius :
      ((a : ZMod p) * (m'.val : ZMod p) =
        (b : ZMod p) + (m.val : ZMod p) * (d : ZMod p))) :
    (p : ℤ) ∣ (b + m.val * d - (a + m.val * (c * (N / p : ℕ))) * m'.val) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  rcases hp_sq with ⟨k, hk⟩
  have h_int_div : ((N : ℤ) / (p : ℤ)) = (p : ℤ) * (k : ℤ) := by
    norm_cast
    rw [hk, sq, mul_assoc, Nat.mul_div_cancel_left _ hp.pos]
  push_cast
  rw [h_int_div]
  push_cast
  rw [show ((p : ZMod p) : ZMod p) = 0 from ZMod.natCast_self p]
  linear_combination -h_moebius

/-- `descendExtraGamma p N` is invertible in `SL₂(ℤ)`. -/
lemma multipass_descendExtraGamma_inverse
    (p N : ℕ) [NeZero p] [NeZero N] [NeZero (N / p)] :
    ∃ ζ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ζ * descendExtraGamma p N = 1 ∧
      descendExtraGamma p N * ζ = 1 :=
  ⟨(descendExtraGamma p N)⁻¹, inv_mul_cancel _, mul_inv_cancel _⟩

/-- For `f ∈ modFormCharSpace k χ` and `α ∈ Γ₀(N)`, `f ∣[k] mapGL ℝ α = χ(α) • f`. -/
lemma multipass_modFormCharSpace_slash_apply
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hfχ : f ∈ modFormCharSpace k χ)
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hα : α ∈ Gamma0 N) :
    (⇑f ∣[k] (mapGL ℝ α : GL (Fin 2) ℝ) : UpperHalfPlane → ℂ) =
      ((χ (Gamma0MapUnits ⟨α, hα⟩) : ℂ) • ⇑f) :=
  (modFormCharSpace_iff_nebentypus k χ f).mp hfχ ⟨α, hα⟩

private lemma multipass_slash_eq_of_diamond_eq
    {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (hfχ : f ∈ modFormCharSpace k χ)
    (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_γ₁_mem : γ₁ ∈ Gamma0 N) (h_γ₂_mem : γ₂ ∈ Gamma0 N)
    (h_diamond_eq : Gamma0MapUnits (N := N) ⟨γ₁, h_γ₁_mem⟩ =
                    Gamma0MapUnits (N := N) ⟨γ₂, h_γ₂_mem⟩) :
    ⇑f ∣[k] (mapGL ℝ γ₁ : GL (Fin 2) ℝ) = ⇑f ∣[k] (mapGL ℝ γ₂ : GL (Fin 2) ℝ) := by
  rw [multipass_modFormCharSpace_slash_apply χ hfχ γ₁ h_γ₁_mem,
      multipass_modFormCharSpace_slash_apply χ hfχ γ₂ h_γ₂_mem,
      h_diamond_eq]

private lemma modularFormLevelRaise_slash_gamma1
    {N : ℕ} [NeZero N] (l : ℕ) [NeZero l] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (hγ : γ ∈ Gamma1 (l * N)) :
    ⇑(modularFormLevelRaise N l k f) ∣[k] (mapGL ℝ γ : GL (Fin 2) ℝ) =
      ⇑(modularFormLevelRaise N l k f) :=
  (modularFormLevelRaise N l k f).slash_action_eq' _ (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)

/-- The descent slash-sum operator as a function on `ℍ`, defined by
`z ↦ Σ_v (⇑f ∣[k] descendCosetList p N hp v) z`. -/
noncomputable def multipass_slashSumOp {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    UpperHalfPlane → ℂ :=
  fun z ↦ ∑ v : Fin (descendCosetCount p N),
    (⇑f ∣[k] descendCosetList p N hp v) z

/-- If the image of `α ∈ SL(2, ℤ)` under reduction mod `N` equals the identity, then
`α ∈ Γ_1(N)`. -/
lemma multipass_gamma1_conjugate_in_gamma1
    {N : ℕ} [NeZero N]
    (α : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_α_mod_N : ((α : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1)) :
    α ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have h : ∀ i j : Fin 2, Int.cast (α i j) = (1 : Matrix (Fin 2) (Fin 2) (ZMod N)) i j :=
    fun i j => congr_fun (congr_fun h_α_mod_N i) j ▸ by simp [Matrix.map_apply]
  simp only [Matrix.one_apply] at h
  exact ⟨h 0 0, h 1 1, h 1 0⟩

/-- When `l` is coprime to prime `p`, there exists a permutation `σ` of `Fin p`
satisfying `(σ m).val = (l * m.val) % p` for all `m`. -/
lemma multipass_mul_mod_p_perm_exists {p l : ℕ} [NeZero p] (hp : p.Prime) (hpl : Nat.Coprime p l) :
    ∃ σ : Equiv.Perm (Fin p), ∀ m : Fin p, (σ m).val = (l * m.val) % p := by
  have : Fact p.Prime := ⟨hp⟩
  let f : Fin p → Fin p := fun m ↦ ⟨(l * m.val) % p, Nat.mod_lt _ hp.pos⟩
  have hl_ne : (l : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hp.coprime_iff_not_dvd.mp hpl
  have hf_inj : Function.Injective f := by
    intro a b hab
    have hab_val : (l * a.val) % p = (l * b.val) % p := congr_arg Fin.val hab
    have h_zmod : ((l : ZMod p) * (a.val : ZMod p)) = ((l : ZMod p) * (b.val : ZMod p)) := by
      simpa [ZMod.natCast_mod] using congr_arg (Nat.cast : ℕ → ZMod p) hab_val
    exact Fin.val_injective (by rw [← ZMod.val_natCast_of_lt a.isLt, ← ZMod.val_natCast_of_lt b.isLt,
        mul_left_cancel₀ hl_ne h_zmod])
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj), fun _ ↦ rfl⟩

private lemma m6_2_extra_rep_levelRaise_bridge
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (l : ℕ) [NeZero l] (hpl : Nat.Coprime p l) (hlNp : l ∣ N / p)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ)
    [NeZero (l * N)] [NeZero ((l * N) / p)] (hpN_lN : p ∣ l * N)
    (hp_sq_lN : ¬ p ^ 2 ∣ l * N)
    (hdvd_lN : (l : ℤ) ∣ (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∀ z : UpperHalfPlane,
      ((⇑f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) ∣[k]
          (mapGL ℝ (HeckeRing.GL2.levelRaiseConjOfDvd l (descendExtraGamma p (l * N)) hdvd_lN)
            : GL (Fin 2) ℝ)) z =
      ((⇑f ∣[k] (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) ∣[k]
          (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ)) z := by
  intro z
  set γ_lN := descendExtraGamma p (l * N) with hγ_lN_def
  set γtilde : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    HeckeRing.GL2.levelRaiseConjOfDvd l γ_lN hdvd_lN with hγtilde_def
  set γ_N := descendExtraGamma p N with hγ_N_def
  have h_γ_N_spec := descendExtraGamma_spec hp hpN hp_sq
  have h_γ_lN_spec := descendExtraGamma_spec (p := p) (N := l * N) hp hpN_lN hp_sq_lN
  have h_Np_dvd_lNp : N / p ∣ (l * N) / p := by
    rcases hpN with ⟨c, hc⟩
    refine ⟨l, ?_⟩
    rw [hc, show l * (p * c) = p * (l * c) by ring,
        Nat.mul_div_cancel_left _ hp.pos,
        Nat.mul_div_cancel_left _ hp.pos, mul_comm]
  have h_γ_lN_mod_Np :
      ((γ_lN : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) := by
    have h_stronger := h_γ_lN_spec.2.2
    have h_factor : ∀ a : ℤ, ((a : ZMod (N / p))) =
        (ZMod.castHom h_Np_dvd_lNp (ZMod (N / p))) ((a : ZMod ((l * N) / p))) := by
      intro a
      have hh : (Int.castRingHom (ZMod (N / p)) : ℤ →+* ZMod (N / p)) =
          (ZMod.castHom h_Np_dvd_lNp (ZMod (N / p))).comp
            (Int.castRingHom (ZMod ((l * N) / p))) :=
        Subsingleton.elim _ _
      exact congr_fun (congr_arg DFunLike.coe hh) a
    ext i j
    have h_entry : ((((γ_lN : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) :
                      ZMod ((l * N) / p))) =
        ((1 : Matrix (Fin 2) (Fin 2) (ZMod ((l * N) / p))) i j) := by
      have := congr_fun (congr_fun h_stronger i) j
      simpa [Matrix.map_apply] using this
    simp only [Matrix.map_apply]
    rw [h_factor, h_entry]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]
  have hl_ne : (l : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have h_γ_lN_10_eq : (γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      (l : ℤ) * ((γtilde : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    show _ = (l : ℤ) * ((γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / (l : ℤ))
    rw [mul_comm, Int.ediv_mul_cancel hdvd_lN]
  have h_lNp_eq : (l * N) / p = l * (N / p) := by
    rcases hpN with ⟨c, hc⟩
    rw [hc, show l * (p * c) = p * (l * c) by ring,
        Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]
  have h_γ_lN_10_dvd_lNp : ((l * (N / p) : ℕ) : ℤ) ∣
      (γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have := h_γ_lN_spec.1
    have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp this)
    have hLN : (((l * N) / p : ℕ) : ℤ) = ((l * (N / p) : ℕ) : ℤ) := by
      exact_mod_cast h_lNp_eq
    exact hLN ▸ hh
  have h_γtilde_10_dvd_Np : ((N / p : ℕ) : ℤ) ∣ ((γtilde : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    obtain ⟨j, hj⟩ := h_γ_lN_10_dvd_lNp
    refine ⟨j, mul_left_cancel₀ hl_ne ?_⟩
    rw [← h_γ_lN_10_eq, hj]
    push_cast
    ring
  have h_γtilde_mod_Np :
      ((γtilde : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) := by
    ext i j
    have h_γ_lN_00 := congr_fun (congr_fun h_γ_lN_mod_Np 0) 0
    have h_γ_lN_01 := congr_fun (congr_fun h_γ_lN_mod_Np 0) 1
    have h_γ_lN_11 := congr_fun (congr_fun h_γ_lN_mod_Np 1) 1
    simp only [Matrix.map_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h_γ_lN_00 h_γ_lN_01 h_γ_lN_11
    have h_γtilde_val : ∀ a b : Fin 2,
        (γtilde : Matrix (Fin 2) (Fin 2) ℤ) a b =
        !![γ_lN.val 0 0, l * γ_lN.val 0 1;
           γ_lN.val 1 0 / l, γ_lN.val 1 1] a b := fun _ _ ↦ rfl
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.map_apply, Matrix.one_apply, Fin.zero_eta, Fin.mk_one,
        h_γtilde_val, ite_true, Fin.isValue]
    · show ((γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod (N / p)) = 1
      exact h_γ_lN_00
    · show (((l : ℤ) * (γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod (N / p)) = 0
      push_cast
      rw [h_γ_lN_01, mul_zero]
    · show (((γtilde : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod (N / p)) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact h_γtilde_10_dvd_Np
    · show ((γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) = 1
      exact h_γ_lN_11
  set δ : Matrix.SpecialLinearGroup (Fin 2) ℤ := γtilde * γ_N⁻¹ with hδ_def
  have h_γ_N_mod_Np :
      ((γ_N : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) :=
    h_γ_N_spec.2.2
  have hδ_mod_Np : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 := by
    let φ : Matrix.SpecialLinearGroup (Fin 2) ℤ →*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod (N / p)) :=
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (N / p)))
    have h_φ_def : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
        (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = (φ γ).val := by
      intro γ
      ext i j
      rw [map_apply_coe]
      simp [RingHom.mapMatrix_apply]
    rw [h_φ_def, show φ δ = φ γtilde * (φ γ_N)⁻¹ from by rw [hδ_def, map_mul, map_inv]]
    have hEq : φ γtilde = φ γ_N := by
      apply Matrix.SpecialLinearGroup.ext
      intros i j
      simp only [← h_φ_def]
      exact congr_fun (congr_fun (h_γtilde_mod_Np.trans h_γ_N_mod_Np.symm) i) j
    rw [hEq, mul_inv_cancel]
    rfl
  have h_γ_lN_mod_p := h_γ_lN_spec.2.1
  have h_γtilde_00_p : ((γtilde : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ZMod p) = 0 := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_lN_mod_p 0) 0
  have h_γtilde_01_p : ((γtilde : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ZMod p) = -(l : ZMod p) := by
    have h := congr_fun (congr_fun h_γ_lN_mod_p 0) 1
    simp [Matrix.map_apply] at h
    show (((l : ℤ) * (γ_lN : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℤ) : ZMod p) = -(l : ZMod p)
    push_cast
    rw [h]
    ring
  have h_γ_N_inv_p_11 : ((γ_N⁻¹).val 1 1 : ZMod p) = 0 := by
    rw [show ((γ_N⁻¹).val 1 1 : ℤ) =
        ((γ_N : Matrix (Fin 2) (Fin 2) ℤ).adjugate 1 1) from
      congr_fun (congr_fun (Matrix.SpecialLinearGroup.coe_inv γ_N) 1) 1,
      Matrix.adjugate_fin_two]
    simpa [Matrix.map_apply] using congr_fun (congr_fun h_γ_N_spec.2.1 0) 0
  have hδ_01_p : (p : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h_mul_apply : (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 =
        (γtilde : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ_N⁻¹).val 0 1 +
        (γtilde : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ_N⁻¹).val 1 1 := by
      show (γtilde.val * γ_N⁻¹.val) 0 1 = _
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [h_mul_apply]
    push_cast
    rw [h_γtilde_00_p, h_γtilde_01_p, h_γ_N_inv_p_11]
    ring
  obtain ⟨k', hk'⟩ := hδ_01_p
  let a := (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let c := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_det_β : (!![a, k'; (p : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by exact_mod_cast δ.det_coe
    simp only [Matrix.det_fin_two] at hdet
    lia
  let β : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![a, k'; (p : ℤ) * c, d], h_det_β⟩
  have hδ_10_Np : ((N / p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congr_fun (congr_fun hδ_mod_Np 1) 0
    simpa [Matrix.map_apply,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] using this
  have hβ_mem : β ∈ Gamma0 N := by
    rw [Gamma0_mem]
    show (((p : ℤ) * c : ℤ) : ZMod N) = 0
    obtain ⟨c', hc'⟩ := hδ_10_Np
    have hpNp_eq_N : ((p : ℤ)) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
      exact_mod_cast Nat.mul_div_cancel' hpN
    rw [show c = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl, hc',
      show (p : ℤ) * (((N / p : ℕ) : ℤ) * c') = (N : ℤ) * c' by rw [← mul_assoc, hpNp_eq_N],
      Int.cast_mul]
    simp
  have h_unitsMap_β :
      ZMod.unitsMap (Nat.div_dvd_of_dvd hpN) (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1 := by
    apply Units.ext
    simp only [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0Map, MonoidHom.coe_mk,
      OneHom.coe_mk, Units.val_one]
    rw [ZMod.cast_intCast (Nat.div_dvd_of_dvd hpN)]
    show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod (N / p)) = 1
    simpa [Matrix.map_apply, Matrix.one_apply_eq] using congr_fun (congr_fun hδ_mod_Np 1) 1
  have h_chi_β : χ (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1 := by
    rw [hχ_eq]
    show (χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) (Gamma0MapUnits ⟨β, hβ_mem⟩) = 1
    simp only [MonoidHom.comp_apply]
    rw [h_unitsMap_β, map_one]
  let D : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
  have hD_δ : D * mapGL ℝ δ = mapGL ℝ β * D := by
    apply Units.ext
    simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply]
    have hDval : (D : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)] := rfl
    have hβval : (β : Matrix (Fin 2) (Fin 2) ℤ) = !![a, k'; (p : ℤ) * c, d] := rfl
    rw [hDval]
    simp only [hβval]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
            show a = (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 from rfl,
            show c = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl,
            show d = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from rfl] <;>
      linarith [hk', mul_comm (p : ℝ) (k' : ℝ),
                show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) = (p : ℝ) * k' by exact_mod_cast hk']
  change ((⇑f ∣[k] D) ∣[k] (mapGL ℝ γtilde : GL (Fin 2) ℝ)) z =
      ((⇑f ∣[k] D) ∣[k] (mapGL ℝ γ_N : GL (Fin 2) ℝ)) z
  have h_γtilde_eq : mapGL ℝ γtilde = mapGL ℝ δ * mapGL ℝ γ_N := by
    simp [hδ_def]
  simp_rw [← SlashAction.slash_mul]
  rw [h_γtilde_eq, ← mul_assoc, hD_δ, mul_assoc, SlashAction.slash_mul,
    multipass_modFormCharSpace_slash_apply χ hfχ β hβ_mem]
  simp [h_chi_β]

private lemma multipass_V_p_slash_upper_aux
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (j : ℕ) (w : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
      (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
        : GL (Fin 2) ℝ)) w = (p : ℂ)⁻¹ * g_low w := by
  have h_glMap_eq : (Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℝ), (j : ℝ); 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
      : GL (Fin 2) ℝ) = glMap (T_p_upper p hp.pos j) := by
    apply Units.ext
    ext i k'
    fin_cases i <;> fin_cases k' <;>
      simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.GeneralLinearGroup.map, Matrix.map_apply]
  rw [h_glMap_eq]
  change ((⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)) ∣[k]
      (T_p_upper p hp.pos j : GL (Fin 2) ℚ)) w = _
  rw [HeckeRing.GL2.slash_T_p_upper_eval k p hp j _ w]
  congr 1
  rw [HeckeRing.GL2.modularFormLevelRaise_apply (N / p) p k g_low]
  have h_uhp_eq :
      (HeckeRing.GL2.levelRaiseMatrix p • (⟨(↑w + ↑j) / ↑p,
        by simpa using div_pos (by linarith [w.im_pos]) (Nat.cast_pos.mpr hp.pos)⟩
          : UpperHalfPlane)) =
        (j : ℝ) +ᵥ w := by
    apply UpperHalfPlane.ext
    rw [HeckeRing.GL2.coe_levelRaiseMatrix_smul, UpperHalfPlane.coe_vadd]
    push_cast
    field_simp [Nat.cast_ne_zero.mpr hp.ne_zero]
    ring
  rw [h_uhp_eq]
  apply SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
  rw [show (Gamma1 (N / p)).map (mapGL ℝ) = (Gamma1 (N / p) : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨(j : ℤ), by simp⟩

/-- For each `v` in the descent coset list, the slash of `V_p g_low` by the corresponding
coset matrix equals `p⁻¹ * g_low(z)` pointwise. -/
lemma multipass_V_p_slash_descendCoset
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (v : Fin (descendCosetCount p N)) (z : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
      (descendCosetList p N hp v)) z = (p : ℂ)⁻¹ * g_low z := by
  unfold descendCosetList
  split_ifs with h_v
  · exact multipass_V_p_slash_upper_aux p hp g_low v.val z
  · have h_p_sq : ¬ p ^ 2 ∣ N := not_p_sq_dvd_of_not_lt h_v
    rw [SlashAction.slash_mul]
    have h_inner_fun : ((⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)) ∣[k]
        (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ)) = ((p : ℂ)⁻¹ • ⇑g_low : UpperHalfPlane → ℂ) := by
      ext w
      simpa using multipass_V_p_slash_upper_aux p hp g_low 0 w
    have h_γ_in_Γ1 : descendExtraGamma p N ∈ Gamma1 (N / p) := by
      have h_mod := (descendExtraGamma_spec hp hpN h_p_sq).2.2
      rw [Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩ <;>
        · simpa [Matrix.map_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
            using congr_fun (congr_fun h_mod _) _
    have h_g_low_inv : (⇑g_low : UpperHalfPlane → ℂ) ∣[k]
        (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ) = ⇑g_low :=
      g_low.slash_action_eq' _ ⟨descendExtraGamma p N, h_γ_in_Γ1, rfl⟩
    have h_σ : UpperHalfPlane.σ (mapGL ℝ (descendExtraGamma p N) : GL (Fin 2) ℝ) =
        RingHom.id ℂ :=
      multipass_sigma_eq_id_of_det_pos _ (by simp)
    rw [h_inner_fun, ModularForm.smul_slash, h_σ, RingHom.id_apply, h_g_low_inv]
    simp [Pi.smul_apply, smul_eq_mul]

/-- **H31 (audit-multipass descendCosetList_lift_eq_glMap)**: every coset
matrix `descendCosetList p N hp v : GL (Fin 2) ℝ` admits a rational lift
`A_v : GL (Fin 2) ℚ` with `glMap A_v = descendCosetList p N hp v`.

This is exactly what makes the cusp transport lemma
`glMap_smul_isCusp_Gamma1` (and the inner Hecke operators) applicable to
the descent operator: the lift's existence is the algebraic reason that
the slash sum of a cusp form again has cusp-form-like behaviour.

The lift mirrors the definition of `descendCosetList` entry-wise:
* For `v.val < p`: `[1, v.val; 0, p]` over `ℚ`.
* For the extra rep: `[1, 0; 0, p] · mapGL ℚ γ_p^(p)` over `ℚ`. -/
lemma descendCosetList_lift_eq_glMap
    {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    (v : Fin (descendCosetCount p N)) :
    ∃ A : GL (Fin 2) ℚ, glMap A = descendCosetList p N hp v := by
  unfold descendCosetList
  split_ifs with h_v
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(1 : ℚ), (v.val : ℚ); 0, (p : ℚ)]
        (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero), ?_⟩
    apply Units.ext
    rw [show (glMap (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℚ), (v.val : ℚ); 0, (p : ℚ)] _)).val =
          (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℚ), (v.val : ℚ); 0, (p : ℚ)] _).val.map (algebraMap ℚ ℝ) from rfl,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, algebraMap]
  · refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero
          !![(1 : ℚ), 0; 0, (p : ℚ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) *
        mapGL ℚ (descendExtraGamma p N), ?_⟩
    rw [map_mul, glMap_mapGL_eq]
    congr 1
    apply Units.ext
    rw [show (glMap (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℚ), 0; 0, (p : ℚ)] _)).val =
          (Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℚ), 0; 0, (p : ℚ)] _).val.map (algebraMap ℚ ℝ) from rfl,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.map_apply, algebraMap]

/-- **M5a: Explicit GL₂(ℝ) coset reps with the action property** (Miyake,
p. 161, Lemma 4.5.6 and 4.5.11).

For `p` prime dividing `N` with `NeZero (N/p)`, set `d := p − 1` if `p² ∣ N`,
else `d := p`. There exists a `(d+1)`-element list of matrices `γ_v ∈ GL_2(ℝ)`,
each with determinant `p`, satisfying:

* **(Action property at Γ_0(N/p) → Γ_0(N))**: for every
  `γ' ∈ Γ_0(N/p) ⊂ SL_2(ℤ)` (viewed in `GL_2(ℝ)` via `mapGL ℝ`), there
  exist a permutation `σ` of `Fin (d+1)` and matrices `α_v ∈ Γ_0(N)`
  such that `γ_v * mapGL ℝ γ' = mapGL ℝ (α_v) * γ_{σ v}` in `GL_2(ℝ)`.

* **(Diamond compatibility)**: with the action witnesses above, the
  Γ_0(N)-character `Gamma0MapUnits α_v ∈ (ZMod N)ˣ` factors through
  `(ZMod (N/p))ˣ` and equals (the image of) `Gamma0MapUnits γ'` for
  every `v`. -/
theorem miyake_hecke_descend_cosets
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)] :
    (∀ v : Fin (descendCosetCount p N),
      (descendCosetList p N hp v : Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ)) ∧
    ∀ γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ∀ (h_γ' : γ' ∈ Gamma0 (N / p)),
      ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
        (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (h_mem : ∀ v, α v ∈ Gamma0 N),
        (∀ v, descendCosetList p N hp v * mapGL ℝ γ' =
              mapGL ℝ (α v) * descendCosetList p N hp (σ v)) ∧
        (∀ v, ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)
            (Gamma0MapUnits (N := N) ⟨α v, h_mem v⟩) =
            Gamma0MapUnits (N := N / p) ⟨γ', h_γ'⟩) :=
  ⟨descendCosetList_det p N hp, descendCosetList_action p hp hpN⟩

/-- **M5b**: The slash sum on a `V_p`-lifted form equals the underlying lower-level form
times `p / (descendCosetCount p N)` (Miyake (4.6.12)). -/
theorem miyake_hecke_descend_qexp
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)] :
    ∃ c : ℂ, c ≠ 0 ∧
      ∀ (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) (n : ℕ),
        (ModularFormClass.qExpansion (1 : ℝ)
          (fun z => c * ∑ v : Fin (descendCosetCount p N),
            (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low)
              ∣[k] (descendCosetList p N hp v)) z)).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff n := by
  have hp_pos : 0 < p := hp.pos
  have hp_ne_C : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h_cnt_pos : 0 < descendCosetCount p N := by
    unfold descendCosetCount; split_ifs <;> omega
  have h_cnt_ne_C : (descendCosetCount p N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp h_cnt_pos)
  refine ⟨(p : ℂ) / (descendCosetCount p N : ℂ),
    div_ne_zero hp_ne_C h_cnt_ne_C, fun g_low n ↦ ?_⟩
  suffices h_fun_eq : (fun z : UpperHalfPlane ↦
      (p : ℂ) / (descendCosetCount p N : ℂ) *
      ∑ v : Fin (descendCosetCount p N),
        (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
          (descendCosetList p N hp v)) z) = (⇑g_low : UpperHalfPlane → ℂ) by
    rw [h_fun_eq]
  funext z
  rw [Finset.mul_sum]
  have h_each : ∀ v : Fin (descendCosetCount p N),
      (p : ℂ) / (descendCosetCount p N : ℂ) *
        (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
          (descendCosetList p N hp v)) z =
      (descendCosetCount p N : ℂ)⁻¹ * g_low z := by
    intro v
    rw [multipass_V_p_slash_descendCoset p hp hpN g_low v z]
    field_simp
  simp_rw [h_each]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma miyake_descent_upper_tri_qExpansion
    {M : ℕ} [NeZero M] (p : ℕ) [NeZero p] (hp : p.Prime) (hpM : p ∣ M)
    {k : ℤ}
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        (fun z => ∑ v ∈ Finset.range p,
          (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z)).coeff m =
      (ModularFormClass.qExpansion (1 : ℝ) g).coeff (p * m) := by
  have hpM_not_coprime : ¬ Nat.Coprime p M := fun h ↦ hp.coprime_iff_not_dvd.mp h hpM
  have h_fun_eq : (fun z : UpperHalfPlane ↦
      ∑ v ∈ Finset.range p,
        (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z) =
      (⇑(heckeT_p_divN k p hp hpM_not_coprime g) : UpperHalfPlane → ℂ) := by
    funext z
    show ∑ v ∈ Finset.range p,
        (⇑g ∣[k] (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z =
      heckeT_p_ut k p hp.pos (⇑g) z
    rw [heckeT_p_ut, Finset.sum_apply]
  rw [h_fun_eq]
  exact qExpansion_one_heckeT_p_divN_coeff hp hpM_not_coprime g m

/-- **M5c**: The slash sum `Σ_v ⇑f ∣[k] (descendCosetList p N hp v)` of any cusp form `f`
vanishes at every cusp of `Γ_1(N/p)` (Miyake p. 158). -/
theorem miyake_hecke_descend_cusp
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 (N / p)).map (mapGL ℝ)) →
      c.IsZeroAt
        (fun z => ∑ v : Fin (descendCosetCount p N),
          (⇑f ∣[k] (descendCosetList p N hp v)) z) k := by
  intro c hc
  have hc_N : IsCusp c ((Gamma1 N).map (mapGL ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((Gamma1 N).map (mapGL ℝ))).mpr
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z ((Gamma1 (N / p)).map (mapGL ℝ))).mp hc)
  rw [show (fun z => ∑ v : Fin (descendCosetCount p N),
              (⇑f ∣[k] (descendCosetList p N hp v)) z) =
        ∑ v : Fin (descendCosetCount p N),
              (⇑f ∣[k] (descendCosetList p N hp v)) by
          ext z; rw [Finset.sum_apply]]
  refine Finset.sum_induction _ (fun g => c.IsZeroAt g k)
    (fun _ _ ha hb ↦ ha.add hb)
    ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc_N) fun v _ ↦ ?_
  obtain ⟨A, hA⟩ := descendCosetList_lift_eq_glMap hp v
  rw [← hA]
  exact OnePoint.IsZeroAt.smul_iff.mp
    (f.zero_at_cusps' (glMap_smul_isCusp_Gamma1 A hc_N))

/-- The orbit identity for the slash sum: slashing the coset sum by `γ_d ∈ Γ₀(N/p)` produces
the reindexed sum `Σ_v (f ∣ α_v) ∣ γ_{σ(v)}` for some permutation `σ` and `Γ₀(N)`-elements
`α_v ∈ Γ₀(N)`. -/
theorem descendCosetList_orbit_identity
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] [NeZero (N / p)]
    (γ : Fin (descendCosetCount p N) → GL (Fin 2) ℝ)
    (h_action : ∀ γ_d : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      γ_d ∈ Gamma0 (N / p) →
      ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
        (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
        (_ : ∀ v, α v ∈ Gamma0 N),
        ∀ v, γ v * mapGL ℝ γ_d = mapGL ℝ (α v) * γ (σ v))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ_d : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h_γ_d : γ_d ∈ Gamma0 (N / p)) :
    ∃ (σ : Equiv.Perm (Fin (descendCosetCount p N)))
      (α : Fin (descendCosetCount p N) → Matrix.SpecialLinearGroup (Fin 2) ℤ)
      (_ : ∀ v, α v ∈ Gamma0 N),
      (∀ v, γ v * mapGL ℝ γ_d = mapGL ℝ (α v) * γ (σ v)) ∧
      ((fun z ↦ ∑ v, (⇑f ∣[k] (γ v)) z) ∣[k]
          (mapGL ℝ γ_d : GL (Fin 2) ℝ) : UpperHalfPlane → ℂ) =
        fun z ↦ ∑ v, ((⇑f ∣[k] (mapGL ℝ (α v) : GL (Fin 2) ℝ)) ∣[k] (γ (σ v))) z := by
  obtain ⟨σ, α, h_mem, h_eq⟩ := h_action γ_d h_γ_d
  refine ⟨σ, α, h_mem, h_eq, ?_⟩
  ext z
  rw [show (fun z ↦ ∑ v, (⇑f ∣[k] γ v) z) = ∑ v, ((⇑f) ∣[k] γ v) by
        ext z
        rw [Finset.sum_apply],
      SlashAction.sum_slash, Finset.sum_apply]
  exact Finset.sum_congr rfl fun v _ ↦ by
    rw [← SlashAction.slash_mul, h_eq v, SlashAction.slash_mul]

/-- For `f ∈ modFormCharSpace k χ` with `χ = χ'.comp (ZMod.unitsMap h)`, slashing the coset sum
by `γ_d ∈ Γ₀(N/p)` scales it by `χ'(Gamma0MapUnits ⟨γ_d, _⟩)`. -/
theorem miyake_hecke_descend_char
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ modFormCharSpace k χ) :
    ∀ (γ_d_pair : { γ_d : Matrix.SpecialLinearGroup (Fin 2) ℤ //
                     γ_d ∈ Gamma0 (N / p) }),
      (fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v)) z) ∣[k]
        (mapGL ℝ γ_d_pair.val : GL (Fin 2) ℝ) =
      ((χ' (Gamma0MapUnits ⟨γ_d_pair.val, γ_d_pair.property⟩) : ℂ) •
        (fun z ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑f ∣[k] (descendCosetList p N hp v)) z) : UpperHalfPlane → ℂ) := by
  intro γ_d_pair
  obtain ⟨γ_d, h_γ_d⟩ := γ_d_pair
  obtain ⟨σ, α, h_α_mem, h_action_eq, h_diamond⟩ :=
      descendCosetList_action p hp hpN γ_d h_γ_d
  have h_chi_eq : ∀ v,
      (χ (Gamma0MapUnits ⟨α v, h_α_mem v⟩) : ℂ) =
        (χ' (Gamma0MapUnits ⟨γ_d, h_γ_d⟩) : ℂ) := by
    intro v
    have : χ (Gamma0MapUnits ⟨α v, h_α_mem v⟩) =
        χ' (Gamma0MapUnits ⟨γ_d, h_γ_d⟩) := by
      rw [hχ_eq, MonoidHom.comp_apply, h_diamond v]
    exact_mod_cast congr_arg ((↑·) : ℂˣ → ℂ) this
  have h_det_pos : ∀ w : Fin (descendCosetCount p N),
      (0 : ℝ) < (descendCosetList p N hp w).det.val := by
    intro w
    have h := descendCosetList_det p N hp w
    rw [Matrix.GeneralLinearGroup.val_det_apply, h]
    exact_mod_cast hp.pos
  ext z
  have h_sum_form : (fun z' : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z') =
      (∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v)) := by
    ext z'
    rw [Finset.sum_apply]
  rw [h_sum_form, SlashAction.sum_slash, Pi.smul_apply, Finset.sum_apply, Finset.sum_apply]
  rw [(Equiv.sum_comp σ (fun v ↦ (⇑f ∣[k] descendCosetList p N hp v) z)).symm]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [(SlashAction.slash_mul k _ _ _).symm, h_action_eq v, SlashAction.slash_mul,
      multipass_modFormCharSpace_slash_apply χ hfχ (α v) (h_α_mem v),
      ModularForm.smul_slash, multipass_sigma_eq_id_of_det_pos _ (h_det_pos (σ v)),
      RingHom.id_apply]
  simp only [Pi.smul_apply, smul_eq_mul, h_chi_eq v]

private lemma miyake_hecke_descend_Gamma1_inv
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k} (hfχ : f ∈ modFormCharSpace k χ)
    (γ' : Matrix.SpecialLinearGroup (Fin 2) ℤ) (h_γ' : γ' ∈ Gamma1 (N / p)) :
    (fun z ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z) ∣[k] (mapGL ℝ γ' : GL (Fin 2) ℝ) =
    fun z ↦ ∑ v : Fin (descendCosetCount p N),
      (⇑f ∣[k] descendCosetList p N hp v) z := by
  obtain ⟨h_γ'_Gamma0, h_units_one⟩ := multipass_char_trivial_on_Gamma1 γ' h_γ'
  have h_char := miyake_hecke_descend_char p hp hpN χ χ' hχ_eq hfχ ⟨γ', h_γ'_Gamma0⟩
  rw [h_units_one, map_one] at h_char
  simpa only [Units.val_one, one_smul] using h_char

private lemma miyake_descend_slash_holo
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v)) :=
  MDifferentiable.sum fun _ _ ↦ (ModularFormClass.holo f).slash k _

private lemma miyake_descend_slash_bddCusps
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {cusp : OnePoint ℝ} (hc : IsCusp cusp ((Gamma1 (N / p)).map (mapGL ℝ))) :
    cusp.IsBoundedAt
      (∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v)) k := by
  have hc_N : IsCusp cusp ((Gamma1 N).map (mapGL ℝ)) :=
    (Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mpr
      ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)
  refine Finset.sum_induction _ (fun g ↦ cusp.IsBoundedAt g k)
    (fun _ _ ha hb ↦ ha.add hb)
    ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).bdd_at_cusps' hc_N) fun v _ ↦ ?_
  obtain ⟨A, hA⟩ := descendCosetList_lift_eq_glMap hp v
  rw [← hA]
  exact OnePoint.IsBoundedAt.smul_iff.mp (f.bdd_at_cusps' (glMap_smul_isCusp_Gamma1 A hc_N))

private lemma miyake_descend_slash_smul
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (s : ℂ) (f : UpperHalfPlane → ℂ)
    (v : Fin (descendCosetCount p N)) :
    (s • f) ∣[k] descendCosetList p N hp v = s • (f ∣[k] descendCosetList p N hp v) := by
  have h_det : (0 : ℝ) < (descendCosetList p N hp v).det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, descendCosetList_det p N hp v]
    exact_mod_cast hp.pos
  rw [ModularForm.smul_slash, multipass_sigma_eq_id_of_det_pos _ h_det, RingHom.id_apply]

/-- Existence of the Hecke descent linear map `Φ : modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ'`
(Miyake §4.6), together with cusp-form preservation and the `Φ ∘ V_p = c · id` identity. -/
theorem miyake_hecke_descend
    {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ) (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))) :
    ∃ (Φ : modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ')
      (c : ℂ),
      (∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
          (hfχ : f.toModularForm' ∈ modFormCharSpace k χ)
          {cusp : OnePoint ℝ},
            IsCusp cusp ((Gamma1 (N / p)).map (mapGL ℝ)) →
            cusp.IsZeroAt (Φ ⟨f.toModularForm', hfχ⟩).val.toFun k) ∧
      c ≠ 0 ∧
      ∀ (g_low : modFormCharSpace k χ') (n : ℕ)
        (h_lift_eq : p * (N / p) = N) (h_mem : h_lift_eq ▸
            HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low.val ∈ modFormCharSpace k χ),
        (ModularFormClass.qExpansion (1 : ℝ)
          (Φ ⟨h_lift_eq ▸ HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low.val,
               h_mem⟩).val).coeff n =
        c * (ModularFormClass.qExpansion (1 : ℝ) g_low.val).coeff n := by
  obtain ⟨c_qexp, hc_qexp_ne, h_qexp⟩ := miyake_hecke_descend_qexp (N := N) p hp hpN
  have hΦ_slash_inv : ∀ (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ modFormCharSpace k χ)
      (γ : GL (Fin 2) ℝ), γ ∈ (Gamma1 (N / p)).map (mapGL ℝ) →
      (fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] descendCosetList p N hp v) z) ∣[k] γ =
      fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] descendCosetList p N hp v) z :=
      fun f hfχ _ hγ ↦ by
    obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
    exact miyake_hecke_descend_Gamma1_inv p hp hpN χ χ' hχ_eq hfχ γ' h_γ'_Gamma1
  have h_sum_form : ∀ (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k),
      (fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] descendCosetList p N hp v) z) =
      ∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v) :=
    fun _ ↦ funext fun _ ↦ (Finset.sum_apply _ _ _).symm
  let hΦ_mkMF : ∀ (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      (hfχ : f ∈ modFormCharSpace k χ),
      ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k := fun f hfχ ↦
    { toSlashInvariantForm :=
      { toFun := fun z ↦ ∑ v : Fin (descendCosetCount p N),
            (⇑f ∣[k] descendCosetList p N hp v) z
        slash_action_eq' := hΦ_slash_inv f hfχ }
      holo' := by
        simp only [SlashInvariantForm.coe_mk, h_sum_form]
        exact miyake_descend_slash_holo p hp f
      bdd_at_cusps' := fun {_} hc ↦ by
        rw [h_sum_form]
        exact miyake_descend_slash_bddCusps p hp f hc }
  have hΦ_char : ∀ (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
      (hfχ : f ∈ modFormCharSpace k χ),
      hΦ_mkMF f hfχ ∈ modFormCharSpace k χ' := fun f hfχ ↦ by
    rw [mem_modFormCharSpace_iff]
    intro d
    obtain ⟨g_rep, h_g_rep⟩ := HeckeRing.GL2.Gamma0MapUnits_surjective (N := N / p) d
    have h_char := miyake_hecke_descend_char p hp hpN χ χ' hχ_eq hfχ ⟨g_rep, g_rep.property⟩
    have h_char_g_rep : HeckeRing.GL2.Gamma0MapUnits
        ⟨(g_rep : Matrix.SpecialLinearGroup (Fin 2) ℤ), g_rep.property⟩ = d := by
      simpa [HeckeRing.GL2.Gamma0MapUnits] using h_g_rep
    rw [show HeckeRing.GL2.diamondOpHom (N := N / p) k d (hΦ_mkMF f hfχ) =
        HeckeRing.GL2.diamondOpAux (N := N / p) k g_rep (hΦ_mkMF f hfχ) by
      congr 1
      exact HeckeRing.GL2.diamondOp_eq_diamondOpAux (N := N / p) k d g_rep h_g_rep]
    rw [h_char_g_rep] at h_char
    ext z
    exact congrFun h_char z
  let Φ : modFormCharSpace k χ →ₗ[ℂ] modFormCharSpace k χ' :=
  { toFun := fun ⟨f, hfχ⟩ ↦ ⟨hΦ_mkMF f hfχ, hΦ_char f hfχ⟩
    map_add' := fun ⟨f, _⟩ ⟨g, _⟩ ↦ by
      apply Subtype.val_injective
      ext z
      simp only [Submodule.coe_add]
      change ∑ v : Fin (descendCosetCount p N), (⇑(f + g) ∣[k] descendCosetList p N hp v) z =
          ∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v) z +
          ∑ v : Fin (descendCosetCount p N), (⇑g ∣[k] descendCosetList p N hp v) z
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      exact congrFun (SlashAction.add_slash k (descendCosetList p N hp v) (⇑f) (⇑g)) z
    map_smul' := fun s ⟨f, _⟩ ↦ by
      apply Subtype.val_injective
      ext z
      simp only [Submodule.coe_smul, RingHom.id_apply]
      change ∑ v : Fin (descendCosetCount p N), (⇑(s • f) ∣[k] descendCosetList p N hp v) z =
          s • ∑ v : Fin (descendCosetCount p N), (⇑f ∣[k] descendCosetList p N hp v) z
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      exact congrFun (miyake_descend_slash_smul p hp s (⇑f) v) z }
  refine ⟨Φ, c_qexp⁻¹,
    fun f _ {_} hc ↦ miyake_hecke_descend_cusp p hp hpN f hc,
    inv_ne_zero hc_qexp_ne, ?_⟩
  · intro ⟨g_low, _⟩ n h_lift_eq h_mem
    set G := HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low
    set g_lifted := h_lift_eq ▸ G with hg_lifted_def
    set S : UpperHalfPlane → ℂ :=
      fun z ↦ ∑ v : Fin (descendCosetCount p N), (⇑G ∣[k] descendCosetList p N hp v) z
    have hcoe : (⇑g_lifted : UpperHalfPlane → ℂ) = ⇑G := by
      funext z
      simp only [hg_lifted_def]
      congr 1
      · exact congrArg (fun n ↦ ModularForm ((Gamma1 n).map (mapGL ℝ)) k) h_lift_eq.symm
      · exact congr_arg_heq (fun n ↦ ModularForm.funLike ((Gamma1 n).map (mapGL ℝ)) k)
          h_lift_eq.symm
      · exact eqRec_heq (φ := fun n ↦ ModularForm ((Gamma1 n).map (mapGL ℝ)) k) h_lift_eq G
    have hRHS : S = ⇑(Φ ⟨g_lifted, h_mem⟩).val := by
      change (fun z ↦ ∑ v, (⇑G ∣[k] descendCosetList p N hp v) z) =
        fun z ↦ ∑ v, (⇑g_lifted ∣[k] descendCosetList p N hp v) z
      simp only [hcoe]
    have h1_period : (1 : ℝ) ∈ ((Gamma1 (N / p)).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 (N / p)).map (mapGL ℝ) =
          (Gamma1 (N / p) : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    have h_factor : (PowerSeries.coeff n)
        (ModularFormClass.qExpansion 1 (c_qexp • S)) =
        c_qexp * (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 S) := by
      rw [hRHS, qExpansion_smul one_pos h1_period, PowerSeries.coeff_smul, smul_eq_mul]
    have h_key : c_qexp * (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 S) =
        (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 ⇑g_low) :=
      h_factor.symm.trans (h_qexp g_low n)
    change (PowerSeries.coeff n)
        (ModularFormClass.qExpansion 1 ⇑(Φ ⟨g_lifted, h_mem⟩).val) = _
    rw [← hRHS]
    field_simp [hc_qexp_ne]
    linear_combination h_key

/-- **T6a: Coset agreement across levels** (M6's combinatorial input).

For `p` prime with `(p, l) = 1`, the explicit coset list
`descendCosetList p N hp` and `descendCosetList p (l·N) hp` give
**identical matrix lists** (up to the `Fin (descendCosetCount p _)` type
adjustment).  The matrices `[1, m; 0, p]` are intrinsically independent
of the level.  The extra rep `[1,0;0,p] · mapGL γ_p^(p)` (when `p² ∤ N`)
depends on `descendExtraGamma`, which itself is chosen at each level;
however, since `(l, p) = 1`, the congruence conditions defining `γ_p^(p)`
at level `N` and at level `l·N` produce compatible choices (any such
γ_p^(p) works).  `descendCosetCount p N = descendCosetCount p (l·N)` since
`(l, p) = 1` means `p² ∣ N ↔ p² ∣ l·N`.

This is the combinatorial step in Miyake Lemma 4.6.6's proof
(p. 158, in the diagram setup). -/
theorem descendCosetList_level_agree
    {N : ℕ} [NeZero N] (l : ℕ) [NeZero l]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hpl : Nat.Coprime p l) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    descendCosetCount p N = descendCosetCount p (l * N) := by
  unfold descendCosetCount
  congr 1
  refine propext ⟨fun h => ?_, fun h => ?_⟩
  · exact h.mul_left l
  · exact (hpl.pow_left 2).dvd_of_dvd_mul_left h

private lemma SL2_diff_map_eq_one_aux {R : Type*} [CommRing R]
    (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h : (γ₁ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) =
          (γ₂ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R)) :
    ((γ₁ * γ₂⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) = 1 := by
  let φ : Matrix.SpecialLinearGroup (Fin 2) ℤ →*
      Matrix.SpecialLinearGroup (Fin 2) R :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom R)
  have h_φ_def : ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → R) = (φ γ).val := fun γ => by
    ext i j
    rw [map_apply_coe]
    simp [RingHom.mapMatrix_apply]
  rw [h_φ_def,
    show φ (γ₁ * γ₂⁻¹) = φ γ₁ * (φ γ₂)⁻¹ from map_mul_inv φ γ₁ γ₂]
  have hEq : φ γ₁ = φ γ₂ :=
    Matrix.SpecialLinearGroup.ext _ _ fun i j => by
      simpa [← h_φ_def] using congr_fun (congr_fun h i) j
  rw [hEq, mul_inv_cancel]
  rfl

private lemma SL2_map_eq_one_of_mod_aux
    {N : ℕ} [NeZero N] {p : ℕ} [NeZero p] [NeZero (N / p)] (hpN : p ∣ N)
    (hcop_int : IsCoprime ((p : ℕ) : ℤ) ((N / p : ℕ) : ℤ))
    (δ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hp : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = 1)
    (hNp : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1) :
    (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1 := by
  have hpNp_eq : ((p : ℕ) : ℤ) * ((N / p : ℕ) : ℤ) = (N : ℤ) := by
    exact_mod_cast Nat.mul_div_cancel' hpN
  have hN_of_dvd : ∀ x : ℤ,
      ((p : ℕ) : ℤ) ∣ x → ((N / p : ℕ) : ℤ) ∣ x → (N : ℤ) ∣ x :=
    fun _ h₁ h₂ => hpNp_eq ▸ hcop_int.mul_dvd h₁ h₂
  ext i j
  simp only [Matrix.map_apply, Matrix.one_apply]
  have h_ij_p : ((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod p) = if i = j then 1 else 0 := by
    simpa [Matrix.map_apply, Matrix.one_apply] using congr_fun (congr_fun hp i) j
  have h_ij_Np : ((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ZMod (N / p)) =
      if i = j then 1 else 0 := by
    simpa [Matrix.map_apply, Matrix.one_apply] using congr_fun (congr_fun hNp i) j
  split_ifs with h
  · subst h
    simp only [if_true] at h_ij_p h_ij_Np
    have hp_dvd : ((p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i i - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp [h_ij_p]
    have hNp_dvd : ((N / p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i i - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simp [h_ij_Np]
    have hN_dvd := hN_of_dvd _ hp_dvd hNp_dvd
    have hmodeq : (δ : Matrix (Fin 2) (Fin 2) ℤ) i i ≡ 1 [ZMOD (N : ℤ)] := by
      rw [Int.modEq_iff_dvd, show 1 - (δ : Matrix (Fin 2) (Fin 2) ℤ) i i =
        -((δ : Matrix (Fin 2) (Fin 2) ℤ) i i - 1) by ring]
      exact dvd_neg.mpr hN_dvd
    simpa using (ZMod.intCast_eq_intCast_iff _ 1 N).mpr hmodeq
  · simp only [if_neg h] at h_ij_p h_ij_Np
    have hp_dvd : ((p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i j := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h_ij_p
    have hNp_dvd : ((N / p : ℕ) : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) i j := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast h_ij_Np
    have hN_dvd := hN_of_dvd _ hp_dvd hNp_dvd
    have hmodeq : (δ : Matrix (Fin 2) (Fin 2) ℤ) i j ≡ 0 [ZMOD (N : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      simpa using hN_dvd
    simpa using (ZMod.intCast_eq_intCast_iff _ 0 N).mpr hmodeq

/-- **T6b-coset-invariance**: the slash sum is invariant under choice of extra coset
representative `γ_p^(p)` (within the CRT congruence class), provided `f` is a
`χ`-eigenform under `Γ_0(N)`. -/
theorem descendCosetList_slash_sum_rep_invariance
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hp_sq : ¬ p ^ 2 ∣ N)
    [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ)
    (γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (h₁_mem : γ₁ ∈ Gamma0 (N / p)) (h₂_mem : γ₂ ∈ Gamma0 (N / p))
    (h₁_mod_p : ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
                  = !![(0 : ZMod p), -1; 1, 0]))
    (h₂_mod_p : ((γ₂ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p)
                  = !![(0 : ZMod p), -1; 1, 0]))
    (h₁_mod_Np : ((γ₁ : Matrix (Fin 2) (Fin 2) ℤ).map
                    (Int.cast : ℤ → ZMod (N / p)) = 1))
    (h₂_mod_Np : ((γ₂ : Matrix (Fin 2) (Fin 2) ℤ).map
                    (Int.cast : ℤ → ZMod (N / p)) = 1)) :
    ∀ z : UpperHalfPlane,
      (⇑f ∣[k]
        ((Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ) * mapGL ℝ γ₁)) z =
      (⇑f ∣[k]
        ((Matrix.GeneralLinearGroup.mkOfDetNeZero
            !![(1 : ℝ), 0; 0, (p : ℝ)]
            (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
          : GL (Fin 2) ℝ) * mapGL ℝ γ₂)) z := by
  let δ := γ₁ * γ₂⁻¹
  have hδ_mod_p : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod p) = 1 :=
    SL2_diff_map_eq_one_aux γ₁ γ₂ (h₁_mod_p.trans h₂_mod_p.symm)
  have hδ_mod_Np : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod (N / p)) = 1 :=
    SL2_diff_map_eq_one_aux γ₁ γ₂ (h₁_mod_Np.trans h₂_mod_Np.symm)
  have hcop : Nat.Coprime p (N / p) := by
    rw [hp.coprime_iff_not_dvd]
    intro h_dvd
    apply hp_sq
    have : p ^ 2 ∣ p * (N / p) := by
      rw [pow_two]
      exact Nat.mul_dvd_mul_left p h_dvd
    rwa [Nat.mul_div_cancel' hpN] at this
  have hcop_int : IsCoprime ((p : ℕ) : ℤ) ((N / p : ℕ) : ℤ) := by
    exact_mod_cast hcop.isCoprime
  have hδ_mod_N : (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod N) = 1 :=
    SL2_map_eq_one_of_mod_aux hpN hcop_int δ hδ_mod_p hδ_mod_Np
  have hδ_Gamma1 : δ ∈ Gamma1 N :=
    multipass_gamma1_conjugate_in_gamma1 δ hδ_mod_N
  have hδ_01_N : (N : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congr_fun (congr_fun hδ_mod_N 0) 1
    simpa [Matrix.map_apply, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] using this
  have hδ_01_p : (p : ℤ) ∣ (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 :=
    (show (p : ℤ) ∣ N by exact_mod_cast hpN).trans hδ_01_N
  obtain ⟨k', hk'⟩ := hδ_01_p
  let a := (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  let c := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  let d := (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  have h_det_α' : (!![a, k'; (p : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    rw [Matrix.det_fin_two_of]
    have hdet : (δ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by exact_mod_cast δ.det_coe
    simp only [Matrix.det_fin_two] at hdet
    linarith [hk'.symm ▸ hdet]
  let α' : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![a, k'; (p : ℤ) * c, d], h_det_α'⟩
  rw [Gamma1_mem] at hδ_Gamma1
  obtain ⟨_, h22, h10⟩ := hδ_Gamma1
  have hα'_mem : α' ∈ Gamma0 N := by
    rw [Gamma0_mem]
    change ((!![a, k'; (p : ℤ) * c, d] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
    simp [Matrix.cons_val_one, show c = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl, h10]
  have h_chi_α' : χ (Gamma0MapUnits ⟨α', hα'_mem⟩) = 1 := by
    have hd : Gamma0MapUnits ⟨α', hα'_mem⟩ = 1 := Units.ext <| by
      simpa [Gamma0MapUnits_val, Gamma0Map] using h22
    rw [hd, map_one]
  let D : GL (Fin 2) ℝ := Matrix.GeneralLinearGroup.mkOfDetNeZero
      !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero)
  have hD_δ : D * mapGL ℝ δ = mapGL ℝ α' * D := by
    apply Units.ext
    simp only [Units.val_mul, mapGL_coe_matrix, map_apply_coe, RingHom.mapMatrix_apply,
      show (D : Matrix (Fin 2) (Fin 2) ℝ) = !![1, 0; 0, (p : ℝ)] from rfl,
      show (α' : Matrix (Fin 2) (Fin 2) ℤ) = !![a, k'; (p : ℤ) * c, d] from rfl]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply,
            show a = (δ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 from rfl,
            show c = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 from rfl,
            show d = (δ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from rfl] <;>
      linarith [hk', mul_comm (p : ℝ) (k' : ℝ),
                show ((δ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℝ) = (p : ℝ) * k' by
                  exact_mod_cast hk']
  have hγ₁_eq : mapGL ℝ γ₁ = mapGL ℝ δ * mapGL ℝ γ₂ := by
    simp [δ]
  have h_split : D * mapGL ℝ γ₁ = mapGL ℝ α' * (D * mapGL ℝ γ₂) := by
    rw [hγ₁_eq, ← mul_assoc, ← mul_assoc, hD_δ, mul_assoc]
  intro z
  rw [h_split, SlashAction.slash_mul,
    multipass_modFormCharSpace_slash_apply χ hfχ α' hα'_mem]
  simp [h_chi_α', one_smul]
  rfl

private lemma map_intCast_eq_one_of_dvd_aux {m₁ m₂ : ℕ} (hdvd : m₂ ∣ m₁)
    (M : Matrix (Fin 2) (Fin 2) ℤ)
    (hM : M.map (Int.cast : ℤ → ZMod m₁) = 1) :
    M.map (Int.cast : ℤ → ZMod m₂) = 1 := by
  have h_factor : ∀ a : ℤ, ((a : ZMod m₂)) =
      (ZMod.castHom hdvd (ZMod m₂)) ((a : ZMod m₁)) :=
    fun a ↦ congr_fun (congr_arg DFunLike.coe
      (Subsingleton.elim (Int.castRingHom (ZMod m₂))
        ((ZMod.castHom hdvd (ZMod m₂)).comp (Int.castRingHom (ZMod m₁)))) : _) a
  ext i j
  have h_entry : ((M i j : ZMod m₁)) = ((1 : Matrix (Fin 2) (Fin 2) (ZMod m₁)) i j) := by
    simpa [Matrix.map_apply] using congr_fun (congr_fun hM i) j
  simp only [Matrix.map_apply]
  rw [h_factor, h_entry]
  rcases eq_or_ne i j with rfl | hij
  · rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, map_zero]

/-- Function-level commutation of the slash sum across levels (Miyake Lemma 4.6.6(1)). -/
theorem descendCosetList_slash_sum_commute
    {N : ℕ} [NeZero N] (l : ℕ) [NeZero l] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) (hpl : Nat.Coprime p l)
    [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    ∀ z : UpperHalfPlane,
      (∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v)) z) =
      (∑ v : Fin (descendCosetCount p (l * N)),
        (⇑f ∣[k] (descendCosetList p (l * N) hp v)) z) := by
  haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
  intro z
  have h_count_eq : descendCosetCount p N = descendCosetCount p (l * N) :=
    descendCosetList_level_agree l p hp hpN hpl
  symm
  refine Fintype.sum_equiv (finCongr h_count_eq.symm) _ _ fun v ↦ ?_
  by_cases h_v_lt : v.val < p
  · rw [descendCosetList_apply_lt hp h_v_lt,
        descendCosetList_apply_lt hp
          (show (finCongr h_count_eq.symm v).val < p from h_v_lt)]
    rfl
  have hp_sq_lN := not_p_sq_dvd_of_not_lt h_v_lt
  have hp_sq : ¬ p ^ 2 ∣ N := fun h ↦ hp_sq_lN (h.mul_left l)
  have hpN_lN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
  haveI : NeZero ((l * N) / p) := ⟨(Nat.div_pos
    (Nat.le_of_dvd (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne l))
      (Nat.pos_of_ne_zero (NeZero.ne N))) hpN_lN) hp.pos).ne'⟩
  obtain ⟨-, h_γ_lN_one, h_γ_lN_stronger⟩ :=
    descendExtraGamma_spec hp hpN_lN hp_sq_lN (p := p) (N := l * N)
  obtain ⟨h_γ_N_pos, h_γ_N_one, h_γ_N_mod⟩ :=
    descendExtraGamma_spec hp hpN hp_sq (p := p) (N := N)
  have h_Np_dvd_lNp : N / p ∣ (l * N) / p := by
    obtain ⟨c, hc⟩ := hpN
    refine ⟨l, ?_⟩
    rw [hc, show l * (p * c) = p * (l * c) by ring,
        Nat.mul_div_cancel_left _ hp.pos,
        Nat.mul_div_cancel_left _ hp.pos, mul_comm]
  have h_γ_lN_mod_Np :=
    map_intCast_eq_one_of_dvd_aux h_Np_dvd_lNp _ h_γ_lN_stronger
  have h_γ_lN_mem_Np : descendExtraGamma p (l * N) ∈ Gamma0 (N / p) := by
    rw [CongruenceSubgroup.Gamma0_mem]
    simpa [Matrix.map_apply, show (1 : Fin 2) ≠ 0 by decide] using
      congr_fun (congr_fun h_γ_lN_mod_Np 1) 0
  rw [descendCosetList_apply_extra hp h_v_lt,
      descendCosetList_apply_extra hp (show ¬ (finCongr h_count_eq.symm v).val < p from h_v_lt)]
  exact descendCosetList_slash_sum_rep_invariance p hp hpN hp_sq χ f hfχ
    (descendExtraGamma p (l * N)) (descendExtraGamma p N)
    h_γ_lN_mem_Np h_γ_N_pos h_γ_lN_one h_γ_N_one h_γ_lN_mod_Np h_γ_N_mod z

/-- **M6: Miyake Lemma 4.6.6 — level commutation of the Hecke descent
operator** (Miyake p. 158).

For `p` prime dividing `N`, `l > 0` with `Nat.Coprime l p`, set
`M := l · N`.  Then for any choice of Hecke descent operators `Φ_N`
(at level `N`) and `Φ_M` (at level `M`) from M5, the diagram

```
M_k(Γ_1(N)) ─Φ_N→ M_k(Γ_1(N/p))
   ↓ incl              ↓ incl
M_k(Γ_1(M)) ─Φ_M→ M_k(Γ_1(M/p))
```

commutes at the function level on `ℍ`. -/
theorem miyake_4_6_6_level_commute
    {N l : ℕ} [NeZero N] [NeZero l] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    (hpl : Nat.Coprime p l) [NeZero (N / p)]
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    ∀ z : UpperHalfPlane,
      (∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v)) z) =
      (∑ v : Fin (descendCosetCount p (l * N)),
        (⇑f ∣[k] (descendCosetList p (l * N) hp v)) z) := by
  intro z
  exact descendCosetList_slash_sum_commute l p hp hpN hpl χ f hfχ z

private lemma descendCosetList_upper_tri_eq_glMap_T_p_upper
    {p N : ℕ} [NeZero p] [NeZero N] (hp : p.Prime)
    {v : Fin (descendCosetCount p N)} (hv : v.val < p) :
    descendCosetList p N hp v = glMap (T_p_upper p hp.pos v.val) := by
  rw [descendCosetList_apply_lt hp hv]
  ext1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [glMap, T_p_upper, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.GeneralLinearGroup.map]

private lemma m6_2_delta_period_aux
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (m : ℕ) (w : UpperHalfPlane) :
    f ((m : ℝ) +ᵥ w) = f w := by
  apply SlashInvariantForm.vAdd_apply_of_mem_strictPeriods
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨(m : ℤ), by simp⟩

private lemma m6_2_delta_div_p_im_pos
    {p : ℕ} (hp : p.Prime) (z : UpperHalfPlane) (b : ℕ) :
    0 < (((z : ℂ) + (b : ℂ)) / (p : ℂ)).im := by
  have : (p : ℂ) = ((p : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.div_ofReal]
  simp [Complex.add_im]
  exact div_pos z.im_pos (Nat.cast_pos.mpr hp.pos)

private lemma m6_2_delta_slash_V_l_upper_tri
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (l : ℕ) [NeZero l] (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    [NeZero (l * N)]
    {v : Fin (descendCosetCount p (l * N))} (hv : v.val < p) (z : UpperHalfPlane) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        descendCosetList p (l * N) hp v) z =
      (p : ℂ)⁻¹ * f (HeckeRing.GL2.levelRaiseMatrix l •
        (⟨((z : ℂ) + v.val) / p, m6_2_delta_div_p_im_pos hp z v.val⟩ :
          UpperHalfPlane)) := by
  rw [descendCosetList_upper_tri_eq_glMap_T_p_upper hp hv,
    show ((⇑(HeckeRing.GL2.modularFormLevelRaise N l k f)) ∣[k]
        (glMap (T_p_upper p hp.pos v.val) : GL (Fin 2) ℝ)) z =
      ((⇑(HeckeRing.GL2.modularFormLevelRaise N l k f)) ∣[k]
        (T_p_upper p hp.pos v.val : GL (Fin 2) ℚ)) z from rfl,
    HeckeRing.GL2.slash_T_p_upper_eval k p hp v.val _ z]
  congr 1
  exact HeckeRing.GL2.modularFormLevelRaise_apply N l k f _

private lemma m6_2_delta_period_shift
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (l : ℕ) [NeZero l] (hpl : Nat.Coprime p l)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ_perm : Equiv.Perm (Fin p))
    (hσ : ∀ m : Fin p, (σ_perm m).val = (l * m.val) % p)
    (z : UpperHalfPlane) (v : Fin p) :
    f (HeckeRing.GL2.levelRaiseMatrix l •
        (⟨((z : ℂ) + v.val) / p, m6_2_delta_div_p_im_pos hp z v.val⟩ :
          UpperHalfPlane)) =
      f (⟨(((HeckeRing.GL2.levelRaiseMatrix l • z : UpperHalfPlane) : ℂ) +
          (σ_perm v).val) / (p : ℂ),
        m6_2_delta_div_p_im_pos hp _ (σ_perm v).val⟩ : UpperHalfPlane) := by
  set n := l * v.val / p with hn_def
  set lhs_pt : UpperHalfPlane :=
    ⟨((z : ℂ) + v.val) / p, m6_2_delta_div_p_im_pos hp z v.val⟩
  set rhs_pt : UpperHalfPlane :=
    ⟨(((HeckeRing.GL2.levelRaiseMatrix l • z : UpperHalfPlane) : ℂ) +
      (σ_perm v).val) / (p : ℂ), m6_2_delta_div_p_im_pos hp _ (σ_perm v).val⟩
  have h_arith : l * v.val = p * n + (σ_perm v).val := by
    rw [hn_def, hσ]
    exact (Nat.div_add_mod (l * v.val) p).symm
  have h_pt_eq : HeckeRing.GL2.levelRaiseMatrix l • lhs_pt = (n : ℝ) +ᵥ rhs_pt := by
    apply UpperHalfPlane.ext
    simp only [lhs_pt, rhs_pt, HeckeRing.GL2.coe_levelRaiseMatrix_smul,
      UpperHalfPlane.coe_vadd]
    have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have h_arith_C : (l : ℂ) * v.val = p * n + (σ_perm v).val := by exact_mod_cast h_arith
    field_simp [hp_ne]
    linear_combination h_arith_C
  rw [h_pt_eq]
  exact m6_2_delta_period_aux f n _

private lemma m6_2_delta_diag_commute
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (l : ℕ) [NeZero l] (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) =
      HeckeRing.GL2.levelRaiseFun l k (⇑f ∣[k]
        (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
          (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)) := by
  have hσ_D := multipass_sigma_eq_id_of_det_pos
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
      (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ)
    (by simp [Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two]; exact_mod_cast hp.pos)
  simp only [HeckeRing.GL2.coe_modularFormLevelRaise, HeckeRing.GL2.levelRaiseFun,
    ModularForm.smul_slash, hσ_D, RingHom.id_apply, ← SlashAction.slash_mul]
  congr 2
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [HeckeRing.GL2.levelRaiseMatrix, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

private lemma m6_2_delta_upper_tri_match
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime)
    (l : ℕ) [NeZero l] (hpl : Nat.Coprime p l)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (σ_perm : Equiv.Perm (Fin p))
    (hσ : ∀ m : Fin p, (σ_perm m).val = (l * m.val) % p)
    (z : UpperHalfPlane) [NeZero (l * N)]
    {v : Fin (descendCosetCount p (l * N))} (hv : v.val < p)
    {w : Fin (descendCosetCount p N)} (hw : w.val < p)
    (hvw : w.val = (σ_perm ⟨v.val, hv⟩).val) :
    (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
        descendCosetList p (l * N) hp v) z =
      (⇑f ∣[k] descendCosetList p N hp w) (HeckeRing.GL2.levelRaiseMatrix l • z) := by
  rw [m6_2_delta_slash_V_l_upper_tri p hp l f hv z,
    descendCosetList_upper_tri_eq_glMap_T_p_upper hp hw,
    show ((⇑f) ∣[k] (glMap (T_p_upper p hp.pos w.val) : GL (Fin 2) ℝ))
          (HeckeRing.GL2.levelRaiseMatrix l • z) =
        ((⇑f) ∣[k] (T_p_upper p hp.pos w.val : GL (Fin 2) ℚ))
          (HeckeRing.GL2.levelRaiseMatrix l • z) from rfl,
    HeckeRing.GL2.slash_T_p_upper_eval k p hp w.val (⇑f) _, hvw]
  congr 1
  exact m6_2_delta_period_shift p hp l hpl f σ_perm hσ z ⟨v.val, hv⟩

private lemma m6_2_delta_l_dvd_extra
    {N : ℕ} [NeZero N]
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    (l : ℕ) [NeZero l] [NeZero (l * N)] (hpN_lN : p ∣ l * N) (hp_sq_lN : ¬ p ^ 2 ∣ l * N) :
    (l : ℤ) ∣ (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  haveI : NeZero (l * N / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) hpN_lN) hp.pos).ne'⟩
  have h_dvd_lNp : ((l * N / p : ℕ) : ℤ) ∣
      (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (Gamma0_mem.mp (descendExtraGamma_spec hp hpN_lN hp_sq_lN).1)
  have h_l_dvd_lNp : (l : ℤ) ∣ ((l * N / p : ℕ) : ℤ) := by
    rcases hpN with ⟨c, hc⟩
    refine ⟨(N / p : ℕ), ?_⟩
    push_cast [show l * N / p = l * (N / p) by
      rw [hc, show l * (p * c) = p * (l * c) by ring,
        Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]]
    ring
  exact h_l_dvd_lNp.trans h_dvd_lNp

/-- **M6(2): Miyake Lemma 4.6.6 part (2)** — descent commutes with `δ_l = V_l`
(p. 158).

For prime `p` dividing `N`, `l > 0` with `(p, l) = 1`, Miyake's diagram (2):

```
G_k(Γ_1(N), χ) ──── T_p ────→ G_k(Γ_1(N/p), χ)
       │ δ_l                          │ δ_l
       ↓                              ↓
G_k(Γ_1(lN), χ) ──── T_p ────→ G_k(Γ_1(lN/p), χ)
```

commutes, where `T_p` is the descent slash-sum operator
`f ↦ Σ_v f|[1,0;0,p]γ_v` (Miyake Eq. 4.6.13, `descendCosetList`)
and `δ_l(g)(z) = g(l·z)` is the level-raising operator
(`modularFormLevelRaise`).

Requires `f ∈ modFormCharSpace k χ` because at p² ∤ N the level-`N` and
level-`lN` coset representatives (`descendExtraGamma`) differ and must be
reconciled via `descendCosetList_slash_sum_rep_invariance`.

Requires `l ∣ N/p` to ensure the level-`lN` extra representative satisfies
the level-`N` congruence mod `N/p`, as needed by rep-invariance. -/
theorem miyake_4_6_6_level_commute_delta
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (l : ℕ) [NeZero l] (hpl : Nat.Coprime p l) (hlNp : l ∣ N / p)
    (χ : (ZMod N)ˣ →* ℂˣ)
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ modFormCharSpace k χ) :
    haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
    ∀ z : UpperHalfPlane,
      (∑ v : Fin (descendCosetCount p (l * N)),
        (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
          (descendCosetList p (l * N) hp v)) z) =
      (∑ v : Fin (descendCosetCount p N),
        (⇑f ∣[k] (descendCosetList p N hp v))
          (HeckeRing.GL2.levelRaiseMatrix l • z)) := by
  haveI : NeZero (l * N) := ⟨Nat.mul_ne_zero (NeZero.ne l) (NeZero.ne N)⟩
  intro z
  obtain ⟨σ_perm, hσ⟩ := multipass_mul_mod_p_perm_exists hp hpl
  by_cases hp_sq : p ^ 2 ∣ N
  · have h_cnt_N : descendCosetCount p N = p := by simp [descendCosetCount, hp_sq]
    have h_cnt_lN : descendCosetCount p (l * N) = p := by
      simp [descendCosetCount, hp_sq.mul_left l]
    apply Fintype.sum_equiv
      ((finCongr h_cnt_lN).trans (σ_perm.trans (finCongr h_cnt_N.symm)))
    intro v
    have hv_lt : v.val < p := by have := v.isLt; simpa [h_cnt_lN] using this
    have h_bij_val : ((finCongr h_cnt_lN).trans (σ_perm.trans (finCongr h_cnt_N.symm)) v).val =
        (σ_perm ⟨v.val, hv_lt⟩).val := by
      simp only [Equiv.trans_apply, finCongr_apply, Fin.val_cast]
      have : Fin.cast h_cnt_lN v = (⟨v.val, hv_lt⟩ : Fin p) := by ext; simp
      rw [this]
    exact m6_2_delta_upper_tri_match p hp l hpl f σ_perm hσ z hv_lt
      (h_bij_val ▸ (σ_perm ⟨v.val, hv_lt⟩).isLt) h_bij_val
  · have h_cnt_N : descendCosetCount p N = p + 1 := by simp [descendCosetCount, hp_sq]
    have hp_sq_lN : ¬ p ^ 2 ∣ l * N := fun h ↦
      hp_sq ((hpl.pow_left 2).dvd_of_dvd_mul_left h)
    have h_cnt_lN : descendCosetCount p (l * N) = p + 1 := by
      simp [descendCosetCount, hp_sq_lN]
    rw [Fintype.sum_equiv (finCongr h_cnt_lN) _
        (fun v ↦ (⇑(HeckeRing.GL2.modularFormLevelRaise N l k f) ∣[k]
            descendCosetList p (l * N) hp (finCongr h_cnt_lN.symm v)) z)
        (fun v ↦ by simp [finCongr_apply]),
      Fintype.sum_equiv (finCongr h_cnt_N) _
        (fun v ↦ (⇑f ∣[k] descendCosetList p N hp (finCongr h_cnt_N.symm v))
            (HeckeRing.GL2.levelRaiseMatrix l • z))
        (fun v ↦ by simp [finCongr_apply]),
      Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    congr 1
    · apply Fintype.sum_equiv σ_perm
      intro i
      have hi_lN : i.val < descendCosetCount p (l * N) := by
        rw [h_cnt_lN]; exact Nat.lt_succ_of_lt i.isLt
      have hsi_N : (σ_perm i).val < descendCosetCount p N := by
        rw [h_cnt_N]; exact Nat.lt_succ_of_lt (σ_perm i).isLt
      have h_lhs_eq : descendCosetList p (l * N) hp (finCongr h_cnt_lN.symm i.castSucc) =
          descendCosetList p (l * N) hp ⟨i.val, hi_lN⟩ := by congr 1
      have h_rhs_eq : descendCosetList p N hp (finCongr h_cnt_N.symm (σ_perm i).castSucc) =
          descendCosetList p N hp ⟨(σ_perm i).val, hsi_N⟩ := by congr 1
      rw [h_lhs_eq, h_rhs_eq]
      exact m6_2_delta_upper_tri_match p hp l hpl f σ_perm hσ z i.isLt
        (σ_perm i).isLt (by simp)
    · have h_lhs_eq : descendCosetList p (l * N) hp (finCongr h_cnt_lN.symm (Fin.last p)) =
          (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
              (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ) *
            mapGL ℝ (descendExtraGamma p (l * N)) :=
        descendCosetList_apply_extra hp (by simp [finCongr_apply])
      have h_rhs_eq : descendCosetList p N hp (finCongr h_cnt_N.symm (Fin.last p)) =
          (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℝ), 0; 0, (p : ℝ)]
              (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne_zero) : GL (Fin 2) ℝ) *
            mapGL ℝ (descendExtraGamma p N) :=
        descendCosetList_apply_extra hp (by simp [finCongr_apply])
      have hpN_lN : p ∣ l * N := dvd_mul_of_dvd_right hpN l
      haveI : NeZero (l * N / p) := ⟨(Nat.div_pos (Nat.le_of_dvd
        (Nat.pos_of_ne_zero (NeZero.ne _)) hpN_lN) hp.pos).ne'⟩
      have hdvd_lN : (l : ℤ) ∣
          (descendExtraGamma p (l * N) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
        m6_2_delta_l_dvd_extra p hp hpN l hpN_lN hp_sq_lN
      rw [h_lhs_eq, h_rhs_eq, SlashAction.slash_mul, SlashAction.slash_mul,
        m6_2_delta_diag_commute p hp l f,
        HeckeRing.GL2.slash_mapGL_levelRaiseFun l k (descendExtraGamma p (l * N)) hdvd_lN,
        HeckeRing.GL2.levelRaiseFun_apply]
      exact m6_2_extra_rep_levelRaise_bridge p hp hpN hp_sq l hpl hlNp
        χ χ' hχ_eq f hfχ hpN_lN hp_sq_lN hdvd_lN _

private lemma m7_N_dvd_div_prime {N l q : ℕ} (hq_prime : q.Prime) (hq_dvd_l : q ∣ l) :
    N ∣ N * l ^ 2 / q := by
  have hq_dvd_l2 : q ∣ l ^ 2 := hq_dvd_l.trans (dvd_pow_self l two_ne_zero)
  rcases hq_dvd_l2 with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [show N * l ^ 2 = N * (q * c) from by rw [hc],
    show N * (q * c) = q * (N * c) by ring,
    Nat.mul_div_cancel_left _ hq_prime.pos]

private lemma m7_gHelper_char_restrict {N M₁ M₂ M : ℕ}
    [NeZero N] [NeZero M₁] [NeZero M₂] [NeZero M] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ) (hNM₁ : N ∣ M₁) (h_inner_dvd : M₁ ∣ M₂) (h_lvl_dvd : M₂ ∣ M)
    (hNM : N ∣ M)
    {g : CuspForm ((Gamma1 M₂).map (mapGL ℝ)) k}
    (hg : g ∈ cuspFormCharSpace k ((χ.comp (ZMod.unitsMap hNM₁)).comp
      (ZMod.unitsMap h_inner_dvd)))
    (h_le : (Gamma1 M).map (mapGL ℝ) ≤ (Gamma1 M₂).map (mapGL ℝ)) :
    CuspForm.restrictSubgroup h_le g ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM)) := by
  have h_collapse :
      ((χ.comp (ZMod.unitsMap hNM₁)).comp (ZMod.unitsMap h_inner_dvd)).comp
        (ZMod.unitsMap h_lvl_dvd) = χ.comp (ZMod.unitsMap hNM) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp,
      MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  rw [← h_collapse]
  exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace _ h_lvl_dvd hg

private lemma m7_chiFHelper_chain {N M₁ M₂ M N₂ : ℕ}
    [NeZero N] [NeZero M₁] [NeZero M₂] [NeZero N₂] [NeZero M]
    (χ : (ZMod N)ˣ →* ℂˣ) (hNM₁ : N ∣ M₁) (h_inner_dvd : M₁ ∣ M₂) (hNM : N ∣ M)
    (h_dvd_outer : M₂ ∣ M) {χ_F : (ZMod N₂)ˣ →* ℂˣ} (h_N₂_dvd_M₂ : N₂ ∣ M₂)
    (h_rel : χ_F.comp (ZMod.unitsMap h_N₂_dvd_M₂) =
      (χ.comp (ZMod.unitsMap hNM₁)).comp (ZMod.unitsMap h_inner_dvd)) :
    χ_F.comp (ZMod.unitsMap (h_N₂_dvd_M₂.trans h_dvd_outer)) =
      χ.comp (ZMod.unitsMap hNM) := by
  rw [← ZMod.unitsMap_comp h_N₂_dvd_M₂ h_dvd_outer, ← MonoidHom.comp_assoc, h_rel,
    MonoidHom.comp_assoc, ZMod.unitsMap_comp,
    MonoidHom.comp_assoc, ZMod.unitsMap_comp]

private lemma m7_q_dvd_Nl2 {N l q : ℕ} (hq : q ∈ l.primeFactors) :
    q ∣ N * l ^ 2 :=
  dvd_mul_of_dvd_right
    ((Nat.dvd_of_mem_primeFactors hq).trans (dvd_pow_self l two_ne_zero)) N

private lemma m7_divq_dvd_Nl2 {N l q : ℕ} (hq : q ∈ l.primeFactors) :
    (N * l ^ 2) / q ∣ N * l ^ 2 :=
  Nat.div_dvd_of_dvd (m7_q_dvd_Nl2 (N := N) hq)

private lemma m7_NeZero_Nl2_div_q {N l q : ℕ} [NeZero (N * l ^ 2)]
    (hq : q ∈ l.primeFactors) :
    NeZero ((N * l ^ 2) / q) :=
  ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _))
    (m7_q_dvd_Nl2 (N := N) hq)) (Nat.prime_of_mem_primeFactors hq).pos).ne'⟩

private lemma m7_levelRaiseFun_zero (q : ℕ) [NeZero q] (k : ℤ) :
    (levelRaiseFun q k (0 : UpperHalfPlane → ℂ)) = 0 := by
  ext τ; rw [levelRaiseFun]; simp

private lemma m7_qExp_coeff_levelRaise_case_A {M q : ℕ} [NeZero M] [NeZero q] {k : ℤ}
    {Γ : Subgroup (GL (Fin 2) ℝ)}
    (g : CuspForm Γ k) (F : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑(HeckeRing.GL2.levelRaise M q k F)) (n : ℕ) :
    (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑g) =
      if q ∣ n then (PowerSeries.coeff (n / q))
        (ModularFormClass.qExpansion (1 : ℝ) ⇑F)
      else 0 := by
  rw [show (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑g) =
    (ModularFormClass.qExpansion (1 : ℝ)
      (HeckeRing.GL2.modularFormLevelRaise M q k F.toModularForm')).coeff n by
      rw [h_eq]; rfl,
    HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff]
  split_ifs with hqn <;> rfl

private lemma m7_qExp_coeff_of_fun_eq_zero {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    {g : CuspForm Γ k} (hg : (⇑g : UpperHalfPlane → ℂ) = 0) (n : ℕ) :
    (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑g) = 0 := by
  rw [hg, qExpansion_zero (1 : ℝ)]; simp

private lemma m7_qExp_zero_branch {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (q n : ℕ) :
    (if q ∣ n then
        (PowerSeries.coeff (n / q))
          (ModularFormClass.qExpansion (1 : ℝ) (⇑(0 : CuspForm Γ k)))
      else (0 : ℂ)) = 0 := by
  split_ifs with hqn
  · exact m7_qExp_coeff_of_fun_eq_zero (g := (0 : CuspForm Γ k)) rfl (n / q)
  · rfl

private lemma m7_eq_q_of_mem_factors_one_eq_l {l l' q q' : ℕ} (hl'_eq1 : 1 = l')
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors)
    (hq' : q' ∈ l.primeFactors) : q' = q := by
  rw [h_pf_eq, ← hl'_eq1, Nat.primeFactors_one] at hq'
  simpa using hq'

private lemma m7_mem_l'_of_ne_q {l l' q q' : ℕ}
    (h_pf_eq : l.primeFactors = insert q l'.primeFactors)
    (hq' : q' ∈ l.primeFactors) (hq'_ne : q' ≠ q) : q' ∈ l'.primeFactors :=
  (Finset.mem_insert.mp (h_pf_eq ▸ hq')).resolve_left hq'_ne

private lemma m7_one_mem_strictPeriods_Gamma1_map (M : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods := by
  rw [show (Gamma1 M).map (mapGL ℝ) =
      (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

private lemma m7_qExp_split_f_eq_f'_plus_hform {ϕ_f ϕ_f' ϕ_h : PowerSeries ℂ} {q : ℕ}
    (hf'_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) ϕ_f' = if n.Coprime q then (PowerSeries.coeff n) ϕ_f else 0)
    (h_form_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) ϕ_h = if ¬ n.Coprime q then (PowerSeries.coeff n) ϕ_f else 0)
    (n : ℕ) :
    (PowerSeries.coeff n) ϕ_f =
      (PowerSeries.coeff n) ϕ_f' + (PowerSeries.coeff n) ϕ_h := by
  have h := hf'_qexp n
  have h2 := h_form_qexp n
  by_cases hcop : n.Coprime q
  · rw [if_pos hcop] at h
    rw [if_neg (not_not_intro hcop)] at h2
    rw [h, h2, add_zero]
  · rw [if_neg hcop] at h
    rw [if_pos hcop] at h2
    rw [h, h2, zero_add]

/-- **Strengthened M7-sqfree** (Miyake p. 159-160) — same as
`miyake_4_6_7_squarefree_decomp` but ALSO exposes, for each prime `q ∣ l`, a
companion `F q` at the natural lower level `Γ_1((N·l²)/q)` whose underlying
function on `ℍ` agrees with `⇑(g q)`.  This is the level where the V_q
preimage of `g q` naturally lives (Miyake's `g_p ∈ G_k(N·l/p, χ)` when `p ∣ l`).

The g and F outputs share the same underlying function — F is g viewed at the
lower level (one factor of q peeled off), and g is F restricted/lifted along
the inclusion `Γ_1(N·l²) ≤ Γ_1((N·l²)/q)`.  Concretely the relationship is
`⇑(F q hq) = ⇑(g q)` (definitionally, after restrictSubgroup).

Helper consumers that need to invoke M6(2) (smaller level (l·N)/q) on the
V_q-preimage of each `g q` should use F here rather than g, then the inclusion
witness comes for free. -/
theorem miyake_4_6_7_squarefree_decomp_with_lower_level
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l : ℕ) (hl_gt : 1 < l) (hl_sqfree : Squarefree l)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n l →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    haveI hM_NeZero : NeZero (N * l ^ 2) :=
      ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (by lia : l ≠ 0))⟩
    have hNM : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
    ∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
      (F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
            CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k)
      (χ_F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
            (ZMod ((N * l ^ 2) / q))ˣ →* ℂˣ),
      (∀ q ∈ l.primeFactors,
        g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM))) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
        F q hq ∈ cuspFormCharSpace k (χ_F q hq)) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        (⇑(F q hq) : UpperHalfPlane → ℂ) = ⇑(g q)) ∧
      (∀ q (hq : q ∈ l.primeFactors),
        haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
        (χ_F q hq).comp (ZMod.unitsMap (m7_divq_dvd_Nl2 (N := N) hq)) =
          χ.comp (ZMod.unitsMap hNM)) ∧
      ∀ n : ℕ,
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        ∑ q ∈ l.primeFactors,
          if q ∣ n then (ModularFormClass.qExpansion (1 : ℝ) (g q)).coeff (n / q)
          else 0 := by
  suffices key : ∀ (m : ℕ) (l : ℕ) (_ : l.primeFactors.card = m)
      (N : ℕ) [NeZero N] (k : ℤ)
      (χ : (ZMod N)ˣ →* ℂˣ)
      (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (_ : f ∈ cuspFormCharSpace k χ)
      (_ : 1 < l) (_ : Squarefree l)
      (_ : ∀ n : ℕ, Nat.Coprime n l → (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0),
      haveI : NeZero (N * l ^ 2) := ⟨Nat.mul_ne_zero (NeZero.ne N)
        (pow_ne_zero 2 (by lia : l ≠ 0))⟩
      have hNM' : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
      ∃ (g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k)
        (F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
              haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
              CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k)
        (χ_F : (q : ℕ) → (hq : q ∈ l.primeFactors) →
              haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
              (ZMod ((N * l ^ 2) / q))ˣ →* ℂˣ),
        (∀ q ∈ l.primeFactors, g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM'))) ∧
        (∀ q (hq : q ∈ l.primeFactors),
          haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
          F q hq ∈ cuspFormCharSpace k (χ_F q hq)) ∧
        (∀ q (hq : q ∈ l.primeFactors),
          (⇑(F q hq) : UpperHalfPlane → ℂ) = ⇑(g q)) ∧
        (∀ q (hq : q ∈ l.primeFactors),
          haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq
          (χ_F q hq).comp (ZMod.unitsMap (m7_divq_dvd_Nl2 (N := N) hq)) =
            χ.comp (ZMod.unitsMap hNM')) ∧
        ∀ n : ℕ, (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
          ∑ q ∈ l.primeFactors,
            if q ∣ n then (ModularFormClass.qExpansion (1 : ℝ) (g q)).coeff (n / q)
            else 0 by
    exact key l.primeFactors.card l rfl N k χ f hfχ hl_gt hl_sqfree h_vanish
  intro m
  induction m with
  | zero =>
    intro l hl_card _ _ _ _ _ _ hl_gt _ _
    have h_empty : l.primeFactors = ∅ := Finset.card_eq_zero.mp hl_card
    rw [Nat.primeFactors_eq_empty] at h_empty
    rcases h_empty with rfl | rfl <;> lia
  | succ n ih =>
    intro l hl_card N _ k χ f hfχ hl_gt hl_sqfree h_vanish
    have hl_nonempty : l.primeFactors.Nonempty :=
      Finset.card_pos.mp (hl_card ▸ Nat.succ_pos n)
    obtain ⟨q, hq_in⟩ := hl_nonempty
    have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_in
    have hq_dvd_l : q ∣ l := Nat.dvd_of_mem_primeFactors hq_in
    haveI hq_ne : NeZero q := ⟨hq_prime.ne_zero⟩
    set l' := l / q with hl'_def
    have hq_dvd_l' : q * l' = l := Nat.mul_div_cancel' hq_dvd_l
    have hl'_pos : 0 < l' := Nat.div_pos (Nat.le_of_dvd (by lia) hq_dvd_l) hq_prime.pos
    have hl'_sqfree : Squarefree l' := hl_sqfree.squarefree_of_dvd (Nat.div_dvd_of_dvd hq_dvd_l)
    have h_pf_eq : l.primeFactors = insert q l'.primeFactors := by
      rw [← hq_dvd_l', Nat.primeFactors_mul hq_prime.ne_zero hl'_pos.ne',
          hq_prime.primeFactors, Finset.singleton_union]
    have hq_not_in_l' : q ∉ l'.primeFactors := by
      intro hq_in_l'
      have hq_dvd_l'_val : q ∣ l' := Nat.dvd_of_mem_primeFactors hq_in_l'
      have hqq_dvd_l : q * q ∣ l := hq_dvd_l' ▸ Nat.mul_dvd_mul_left q hq_dvd_l'_val
      exact (Nat.squarefree_iff_prime_squarefree.mp hl_sqfree q hq_prime) hqq_dvd_l
    have hl'_pf_card : l'.primeFactors.card = n := by
      have := hl_card
      rw [h_pf_eq, Finset.card_insert_of_notMem hq_not_in_l'] at this
      lia
    haveI hNl2_ne : NeZero (N * l ^ 2) :=
      ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 (by lia : l ≠ 0))⟩
    have hNM' : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hl'_pos)) with
      hl'_eq1 | hl'_gt1
    · have hl_eq_q : l = q := by
        rw [← hq_dvd_l', ← hl'_eq1, mul_one]
      have hq_dvd_Nl2 : q ∣ N * l ^ 2 := by
        rw [hl_eq_q, sq]; exact dvd_mul_of_dvd_right (Nat.dvd_mul_left q q) N
      have h_Nl2_div_q : N * l ^ 2 / q = N * q := by
        rw [hl_eq_q, sq, ← mul_assoc, Nat.mul_div_cancel _ hq_prime.pos]
      haveI hNl2_div_q_ne : NeZero (N * l ^ 2 / q) := by
        rw [h_Nl2_div_q]
        exact ⟨Nat.mul_ne_zero (NeZero.ne N) hq_prime.ne_zero⟩
      let χ_M : DirichletCharacter ℂ (N * l ^ 2) :=
        MulChar.ofUnitHom (χ.comp (ZMod.unitsMap hNM'))
      have h_χ_M_toUnit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNM') :=
        MulChar.equivToUnitHom.apply_symm_apply _
      have h_sub : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
        Gamma1_map_le_Gamma1_map_of_dvd hNM'
      let f_res : CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k :=
        CuspForm.restrictSubgroup h_sub f
      have hf_res_char : f_res ∈ cuspFormCharSpace k χ_M.toUnitHom := by
        rw [h_χ_M_toUnit]
        exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNM' hfχ
      have hf_res_supp : f_res ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule
          (N * l ^ 2) k q := fun n hn ↦
        h_vanish n (hl_eq_q ▸ (hq_prime.coprime_iff_not_dvd.mpr hn).symm)
      have h_period_one : (1 : ℝ) ∈ ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)).strictPeriods :=
        m7_one_mem_strictPeriods_Gamma1_map _
      obtain ⟨φ, h_eq, h_period⟩ :=
        HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
          hq_prime.one_lt hq_dvd_Nl2 f_res (fun n hn ↦ hf_res_supp n hn)
      have h_divq_dvd_M : (N * l ^ 2) / q ∣ N * l ^ 2 := by
        rw [h_Nl2_div_q, hl_eq_q, sq, ← mul_assoc]
        exact Nat.dvd_mul_right (N * q) q
      have h_sub_q : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤
          (Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ) :=
        Gamma1_map_le_Gamma1_map_of_dvd h_divq_dvd_M
      rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
          q (N * l ^ 2) hq_dvd_Nl2 k χ_M φ f_res hf_res_char h_eq h_period with
        ⟨h_fac, F, hF_char, hF_eq⟩ | hφ_zero
      · let g_q : CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k :=
          CuspForm.restrictSubgroup h_sub_q F
        refine ⟨fun q' ↦ if q' = q then g_q else 0,
          fun q' hq' ↦ if hq'_eq : q' = q then
              hq'_eq ▸ F
            else 0,
          fun q' hq' ↦ if hq'_eq : q' = q then
              hq'_eq ▸ (loweredCharacter h_fac).toUnitHom
            else 1, ?_, ?_, ?_, ?_, ?_⟩
        · intro q' hq'
          rw [m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq']
          simp only [if_true]
          have h_char_eq : (loweredCharacter h_fac).toUnitHom.comp
              (ZMod.unitsMap h_divq_dvd_M) = χ.comp (ZMod.unitsMap hNM') := by
            rw [← toUnitHom_loweredCharacter h_fac, h_χ_M_toUnit]
          rw [← h_char_eq]
          exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace
            (loweredCharacter h_fac).toUnitHom h_divq_dvd_M hF_char
        · intro q' hq'
          obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
          simpa using hF_char
        · intro q' hq'
          obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
          simp only [↓reduceDIte, ↓reduceIte]
          rfl
        · intro q' hq'
          obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
          simp only [↓reduceDIte]
          convert (toUnitHom_loweredCharacter h_fac).symm.trans h_χ_M_toUnit
        · intro n
          rw [h_pf_eq, ← hl'_eq1, Nat.primeFactors_one]
          simp only [Finset.sum_insert, Finset.notMem_empty,
            not_false_eq_true, Finset.sum_empty, add_zero, if_true]
          have h_fres_eq : (⇑f_res : UpperHalfPlane → ℂ) =
              ⇑(HeckeRing.GL2.levelRaise ((N * l ^ 2) / q) q k F) := by
            rw [h_eq, ← hF_eq]; rfl
          exact m7_qExp_coeff_levelRaise_case_A f_res F h_fres_eq n
      · have hf_res_zero : (⇑f_res : UpperHalfPlane → ℂ) = 0 := by
          rw [h_eq, hφ_zero]; exact m7_levelRaiseFun_zero q k
        refine ⟨fun _ ↦ 0, fun _ _ ↦ 0,
          fun q' hq' ↦ χ.comp (ZMod.unitsMap (m7_N_dvd_div_prime
            (Nat.prime_of_mem_primeFactors hq') (Nat.dvd_of_mem_primeFactors hq'))),
          fun _ _ ↦ Submodule.zero_mem _, fun _ _ ↦ Submodule.zero_mem _,
          fun _ _ ↦ rfl, ?_, ?_⟩
        · intro q' hq'
          obtain rfl := m7_eq_q_of_mem_factors_one_eq_l hl'_eq1 h_pf_eq hq'
          dsimp only
          rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
        · intro n
          have h_an_f_zero : (PowerSeries.coeff n)
              (ModularFormClass.qExpansion (1 : ℝ) ⇑f) =
              (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f_res) := rfl
          rw [h_an_f_zero, m7_qExp_coeff_of_fun_eq_zero hf_res_zero,
            h_pf_eq, ← hl'_eq1, Nat.primeFactors_one]
          simp only [Finset.sum_insert, Finset.notMem_empty,
            not_false_eq_true, Finset.sum_empty, add_zero]
          exact (m7_qExp_zero_branch q n).symm
    · haveI hq_l'_sqfree : Squarefree q := hq_prime.squarefree
      have hl_eq_ql' : l = q * l' := hq_dvd_l'.symm
      have h_inst_aux : NeZero (N * q ^ 2) :=
        ⟨Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hq_prime.ne_zero)⟩
      haveI := h_inst_aux
      have hNNq2 : N ∣ N * q ^ 2 := Nat.dvd_mul_right N _
      obtain ⟨h_form, h_form_char, h_form_qexp⟩ :=
        miyake_h_form_general (N := N) (k := k) χ f hfχ q hq_prime.pos hq_l'_sqfree
      have h_sub_Nq2 : (Gamma1 (N * q ^ 2)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
        Gamma1_map_le_Gamma1_map_of_dvd hNNq2
      let f_at_Nq2 : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k :=
        CuspForm.restrictSubgroup h_sub_Nq2 f
      have hf_at_Nq2_char : f_at_Nq2 ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)) :=
        cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hNNq2 hfχ
      let f' : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k := f_at_Nq2 - h_form
      have hf'_char : f' ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)) :=
        Submodule.sub_mem _ hf_at_Nq2_char h_form_char
      have h1_period_Nq2 :
          (1 : ℝ) ∈ ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)).strictPeriods :=
        m7_one_mem_strictPeriods_Gamma1_map _
      have hf'_qexp : ∀ n : ℕ,
          (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f') =
          if n.Coprime q then
            (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f)
          else 0 := by
        intro n
        have h_sub_qexp :
            ModularFormClass.qExpansion (1 : ℝ) (f_at_Nq2 - h_form) =
              ModularFormClass.qExpansion (1 : ℝ) f_at_Nq2 -
              ModularFormClass.qExpansion (1 : ℝ) h_form := by
          rw [sub_eq_add_neg, sub_eq_add_neg,
            ← qExpansion_neg one_pos h1_period_Nq2 h_form]
          exact qExpansion_add (Γ := (Gamma1 (N * q ^ 2)).map (mapGL ℝ))
            (h := (1 : ℝ)) (a := k) (b := k) one_pos h1_period_Nq2 f_at_Nq2 (- h_form)
        have h_class :
            ModularFormClass.qExpansion (1 : ℝ) (⇑f' : UpperHalfPlane → ℂ) =
              ModularFormClass.qExpansion (1 : ℝ) (f_at_Nq2 - h_form) := rfl
        show (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) (⇑f')) = _
        rw [h_class, h_sub_qexp, map_sub]
        have h_f_at_coeff :
            (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) f_at_Nq2) =
              (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f) := rfl
        rw [h_f_at_coeff, h_form_qexp n]
        by_cases hcop : n.Coprime q
        · rw [if_pos hcop, if_neg (not_not_intro hcop)]; ring
        · rw [if_neg hcop, if_pos hcop]; ring
      have hf'_vanish : ∀ n : ℕ, n.Coprime l' →
          (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f') = 0 := by
        intro n hn_cop_l'
        rw [hf'_qexp n]
        by_cases hcop_q : n.Coprime q
        · rw [if_pos hcop_q]
          apply h_vanish n
          rw [← hq_dvd_l']
          exact Nat.Coprime.mul_right hcop_q hn_cop_l'
        · rw [if_neg hcop_q]
      obtain ⟨g_helper, F_helper, χ_F_helper, g_helper_char, F_helper_char,
          F_helper_eq, χ_F_helper_rel, g_helper_qexp⟩ :=
        ih l' hl'_pf_card (N * q ^ 2) k (χ.comp (ZMod.unitsMap hNNq2))
          f' hf'_char hl'_gt1 hl'_sqfree hf'_vanish
      haveI hNq2l'2_ne : NeZero ((N * q ^ 2) * l' ^ 2) :=
        ⟨Nat.mul_ne_zero (NeZero.ne _) (pow_ne_zero 2 hl'_pos.ne')⟩
      have h_level_eq : (N * q ^ 2) * l' ^ 2 = N * l ^ 2 := by
        rw [hl_eq_ql', mul_pow]; ring
      have h_lvl_dvd : (N * q ^ 2) * l' ^ 2 ∣ N * l ^ 2 := by rw [h_level_eq]
      have hh_form_supp : h_form ∈ HeckeRing.GL2.AtkinLehner.qSupportedOnDvdSubmodule
          (N * q ^ 2) k q := fun n hn_not_dvd ↦ by
        rw [h_form_qexp n, if_neg (not_not_intro
          (hq_prime.coprime_iff_not_dvd.mpr hn_not_dvd).symm)]
      let χ_M : DirichletCharacter ℂ (N * q ^ 2) :=
        MulChar.ofUnitHom (χ.comp (ZMod.unitsMap hNNq2))
      have h_χ_M_toUnit : χ_M.toUnitHom = χ.comp (ZMod.unitsMap hNNq2) :=
        MulChar.equivToUnitHom.apply_symm_apply _
      have hh_form_char_χ_M : h_form ∈ cuspFormCharSpace k χ_M.toUnitHom := by
        rw [h_χ_M_toUnit]; exact h_form_char
      have hq_dvd_Nq2 : q ∣ N * q ^ 2 := by
        rw [sq, ← mul_assoc]; exact Nat.dvd_mul_left q (N * q)
      have h_Nq2_div_q : N * q ^ 2 / q = N * q := by
        rw [sq, ← mul_assoc, Nat.mul_div_cancel _ hq_prime.pos]
      haveI hNq2_div_q_ne : NeZero (N * q ^ 2 / q) := by
        rw [h_Nq2_div_q]
        exact ⟨Nat.mul_ne_zero (NeZero.ne N) hq_prime.ne_zero⟩
      obtain ⟨φ, hφ_eq, hφ_period⟩ :=
        HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
          hq_prime.one_lt hq_dvd_Nq2 h_form (fun n hn ↦ hh_form_supp n hn)
      have h_divq_dvd_Nq2 : (N * q ^ 2) / q ∣ N * q ^ 2 := by
        rw [h_Nq2_div_q, sq, ← mul_assoc]
        exact Nat.dvd_mul_right (N * q) q
      have h_sub_q : (Gamma1 (N * q ^ 2)).map (mapGL ℝ) ≤
          (Gamma1 ((N * q ^ 2) / q)).map (mapGL ℝ) :=
        Gamma1_map_le_Gamma1_map_of_dvd h_divq_dvd_Nq2
      have hNq2_dvd_Nl2 : N * q ^ 2 ∣ N * l ^ 2 := by
        rw [hl_eq_ql', mul_pow]
        exact ⟨l' ^ 2, by ring⟩
      have h_sub_Nl2_Nq2 : (Gamma1 (N * l ^ 2)).map (mapGL ℝ) ≤
          (Gamma1 (N * q ^ 2)).map (mapGL ℝ) :=
        Gamma1_map_le_Gamma1_map_of_dvd hNq2_dvd_Nl2
      have h_Nl2_div_q_eq : (N * l ^ 2) / q = (N * q ^ 2 / q) * l' ^ 2 := by
        rw [h_Nq2_div_q, hl_eq_ql', mul_pow,
          show N * (q ^ 2 * l' ^ 2) = (N * q * l' ^ 2) * q by ring,
          Nat.mul_div_cancel _ hq_prime.pos]
      have hNq_dvd_Nl2divq : (N * q ^ 2 / q) ∣ (N * l ^ 2) / q := by
        rw [h_Nl2_div_q_eq]
        exact Nat.dvd_mul_right _ _
      haveI hNl2_div_q_ne : NeZero ((N * l ^ 2) / q) := by
        have hq_dvd_l2 : q ∣ l ^ 2 :=
          hq_dvd_l.trans (dvd_pow_self l two_ne_zero)
        have hq_dvd : q ∣ N * l ^ 2 := dvd_mul_of_dvd_right hq_dvd_l2 N
        have hl_ne : l ≠ 0 := by lia
        have hNl2_pos : 0 < N * l ^ 2 := Nat.pos_of_ne_zero
          (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hl_ne))
        exact ⟨(Nat.div_pos (Nat.le_of_dvd hNl2_pos hq_dvd) hq_prime.pos).ne'⟩
      have h_sub_lift_q : (Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ) ≤
          (Gamma1 (N * q ^ 2 / q)).map (mapGL ℝ) :=
        Gamma1_map_le_Gamma1_map_of_dvd hNq_dvd_Nl2divq
      rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
          q (N * q ^ 2) hq_dvd_Nq2 k χ_M φ h_form hh_form_char_χ_M hφ_eq hφ_period with
        ⟨h_fac, F, hF_char, hF_eq⟩ | hφ_zero
      · let F_at_Nq2 : CuspForm ((Gamma1 (N * q ^ 2)).map (mapGL ℝ)) k :=
          CuspForm.restrictSubgroup h_sub_q F
        let g_q : CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k :=
          CuspForm.restrictSubgroup h_sub_Nl2_Nq2 F_at_Nq2
        let F_q_low : CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k :=
          CuspForm.restrictSubgroup h_sub_lift_q F
        refine ⟨fun q' ↦ if q' = q then g_q else
          CuspForm.restrictSubgroup
            (le_of_eq_of_le (by rw [h_level_eq]) (le_refl _)) (g_helper q'),
          fun q' hq' ↦ if hq'_eq : q' = q then
              hq'_eq ▸ F_q_low
            else
              CuspForm.restrictSubgroup
                (show (Gamma1 ((N * l ^ 2) / q')).map (mapGL ℝ) ≤
                    (Gamma1 (((N * q ^ 2) * l' ^ 2) / q')).map (mapGL ℝ) by
                  rw [h_level_eq])
                (F_helper q' (m7_mem_l'_of_ne_q h_pf_eq hq' hq'_eq)),
          fun q' hq' ↦ if hq'_eq : q' = q then
              hq'_eq ▸ ((loweredCharacter h_fac).toUnitHom.comp
                (ZMod.unitsMap hNq_dvd_Nl2divq))
            else
              (χ_F_helper q'
                  (m7_mem_l'_of_ne_q h_pf_eq hq' hq'_eq)).comp
                (ZMod.unitsMap
                  (show ((N * q ^ 2) * l' ^ 2) / q' ∣ (N * l ^ 2) / q' by
                    rw [h_level_eq])),
          ?_, ?_, ?_, ?_, ?_⟩
        · intro q' hq'_in
          show (if q' = q then g_q else CuspForm.restrictSubgroup _ (g_helper q')) ∈ _
          split_ifs with hq'_eq
          · have h_char_eq : (loweredCharacter h_fac).toUnitHom.comp
                (ZMod.unitsMap h_divq_dvd_Nq2) = χ.comp (ZMod.unitsMap hNNq2) := by
              rw [← toUnitHom_loweredCharacter h_fac, h_χ_M_toUnit]
            have hF_at_Nq2 : F_at_Nq2 ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNNq2)) :=
              h_char_eq ▸ cuspForm_restrictSubgroup_mem_cuspFormCharSpace
                (loweredCharacter h_fac).toUnitHom h_divq_dvd_Nq2 hF_char
            have h_chain : (χ.comp (ZMod.unitsMap hNNq2)).comp
                (ZMod.unitsMap hNq2_dvd_Nl2) = χ.comp (ZMod.unitsMap hNM') := by
              rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
            exact h_chain ▸ cuspForm_restrictSubgroup_mem_cuspFormCharSpace
              (χ.comp (ZMod.unitsMap hNNq2)) hNq2_dvd_Nl2 hF_at_Nq2
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            exact m7_gHelper_char_restrict χ hNNq2 (Nat.dvd_mul_right _ _) h_lvl_dvd hNM'
              (g_helper_char q' hq'_in_l')
              (Gamma1_map_le_Gamma1_map_of_dvd h_lvl_dvd)
        · intro q' hq'_in
          by_cases hq'_eq : q' = q
          · subst hq'_eq
            simp only [↓reduceDIte]
            exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace
              (loweredCharacter h_fac).toUnitHom hNq_dvd_Nl2divq hF_char
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq'_in
            haveI : NeZero (((N * q ^ 2) * l' ^ 2) / q') := by rw [h_level_eq]; infer_instance
            have h_div_dvd : ((N * q ^ 2) * l' ^ 2) / q' ∣ (N * l ^ 2) / q' := by rw [h_level_eq]
            simp only [dif_neg hq'_eq]
            exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace
              (χ_F_helper q' hq'_in_l') h_div_dvd (F_helper_char q' hq'_in_l')
        · intro q' hq'_in
          by_cases hq'_eq : q' = q
          · subst hq'_eq
            simp only [↓reduceDIte, ↓reduceIte]
            rfl
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            simp only [dif_neg hq'_eq, if_neg hq'_eq]
            change (⇑(F_helper q' hq'_in_l') : UpperHalfPlane → ℂ) = ⇑(g_helper q')
            exact F_helper_eq q' hq'_in_l'
        · intro q' hq'_in
          by_cases hq'_eq : q' = q
          · subst hq'_eq
            have h_chain : (loweredCharacter h_fac).toUnitHom.comp
                (ZMod.unitsMap (h_divq_dvd_Nq2.trans hNq2_dvd_Nl2)) =
                χ.comp (ZMod.unitsMap hNM') := by
              rw [← ZMod.unitsMap_comp h_divq_dvd_Nq2 hNq2_dvd_Nl2,
                ← MonoidHom.comp_assoc, ← toUnitHom_loweredCharacter h_fac, h_χ_M_toUnit,
                MonoidHom.comp_assoc, ZMod.unitsMap_comp]
            dsimp only
            rw [dif_pos rfl, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
            convert h_chain using 2
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq'_in
            haveI : NeZero (((N * q ^ 2) * l' ^ 2) / q') := by rw [h_level_eq]; infer_instance
            have h_dvd_inner : ((N * q ^ 2) * l' ^ 2) / q' ∣ (N * q ^ 2) * l' ^ 2 :=
              Nat.div_dvd_of_dvd (by rw [h_level_eq]; exact m7_q_dvd_Nl2 (N := N) hq'_in)
            have h_chain := m7_chiFHelper_chain χ hNNq2 (Nat.dvd_mul_right _ _) hNM'
              h_lvl_dvd h_dvd_inner (χ_F_helper_rel q' hq'_in_l')
            dsimp only
            rw [dif_neg hq'_eq, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
            convert h_chain using 2
        · intro n
          rw [h_pf_eq, Finset.sum_insert hq_not_in_l']
          simp only [if_true]
          rw [m7_qExp_split_f_eq_f'_plus_hform hf'_qexp h_form_qexp n]
          have h_IH := g_helper_qexp n
          have h_hform_eq : (⇑h_form : UpperHalfPlane → ℂ) =
              ⇑(HeckeRing.GL2.levelRaise ((N * q ^ 2) / q) q k F) := by
            rw [hφ_eq, ← hF_eq]; rfl
          rw [m7_qExp_coeff_levelRaise_case_A h_form F h_hform_eq, h_IH, add_comm]
          congr 1
          apply Finset.sum_congr rfl
          intro q' hq'_in_l'
          have hq'_ne_q : q' ≠ q := fun h ↦ hq_not_in_l' (h ▸ hq'_in_l')
          rw [if_neg hq'_ne_q]
          rfl
      · have hh_form_zero : (⇑h_form : UpperHalfPlane → ℂ) = 0 := by
          rw [hφ_eq, hφ_zero]; exact m7_levelRaiseFun_zero q k
        have h_an_hform_zero : ∀ n,
            (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑h_form) = 0 :=
          m7_qExp_coeff_of_fun_eq_zero hh_form_zero
        have h_an_f'_eq_f : ∀ n,
            (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f') =
            (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f) := fun n ↦ by
          rw [m7_qExp_split_f_eq_f'_plus_hform hf'_qexp h_form_qexp n,
            h_an_hform_zero n, add_zero]
        have hN_dvd_divq_indB : N ∣ (N * l ^ 2) / q := m7_N_dvd_div_prime hq_prime hq_dvd_l
        refine ⟨fun q' ↦ if q' = q then 0 else
          CuspForm.restrictSubgroup
            (le_of_eq_of_le (by rw [h_level_eq]) (le_refl _)) (g_helper q'),
          fun q' hq' ↦ if hq'_eq : q' = q then
              hq'_eq ▸ (0 : CuspForm ((Gamma1 ((N * l ^ 2) / q)).map (mapGL ℝ)) k)
            else
              CuspForm.restrictSubgroup
                (show (Gamma1 ((N * l ^ 2) / q')).map (mapGL ℝ) ≤
                    (Gamma1 (((N * q ^ 2) * l' ^ 2) / q')).map (mapGL ℝ) by
                  rw [h_level_eq])
                (F_helper q' (m7_mem_l'_of_ne_q h_pf_eq hq' hq'_eq)),
          fun q' hq' ↦ if hq'_eq : q' = q then
              hq'_eq ▸ (χ.comp (ZMod.unitsMap hN_dvd_divq_indB))
            else
              (χ_F_helper q'
                  (m7_mem_l'_of_ne_q h_pf_eq hq' hq'_eq)).comp
                (ZMod.unitsMap
                  (show ((N * q ^ 2) * l' ^ 2) / q' ∣ (N * l ^ 2) / q' by
                    rw [h_level_eq])),
          ?_, ?_, ?_, ?_, ?_⟩
        · intro q' hq'_in
          show (if q' = q then (0 : CuspForm _ k) else
            CuspForm.restrictSubgroup _ (g_helper q')) ∈ _
          split_ifs with hq'_eq
          · exact Submodule.zero_mem _
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            exact m7_gHelper_char_restrict χ hNNq2 (Nat.dvd_mul_right _ _) h_lvl_dvd hNM'
              (g_helper_char q' hq'_in_l')
              (Gamma1_map_le_Gamma1_map_of_dvd h_lvl_dvd)
        · intro q' hq'_in
          by_cases hq'_eq : q' = q
          · subst hq'_eq
            simp only [↓reduceDIte]
            exact Submodule.zero_mem _
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq'_in
            haveI : NeZero (((N * q ^ 2) * l' ^ 2) / q') := by rw [h_level_eq]; infer_instance
            have h_div_dvd : ((N * q ^ 2) * l' ^ 2) / q' ∣ (N * l ^ 2) / q' := by rw [h_level_eq]
            simp only [dif_neg hq'_eq]
            exact cuspForm_restrictSubgroup_mem_cuspFormCharSpace
              (χ_F_helper q' hq'_in_l') h_div_dvd (F_helper_char q' hq'_in_l')
        · intro q' hq'_in
          by_cases hq'_eq : q' = q
          · subst hq'_eq
            simp only [↓reduceDIte, ↓reduceIte]
            rfl
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            simp only [dif_neg hq'_eq, if_neg hq'_eq]
            change (⇑(F_helper q' hq'_in_l') : UpperHalfPlane → ℂ) = ⇑(g_helper q')
            exact F_helper_eq q' hq'_in_l'
        · intro q' hq'_in
          by_cases hq'_eq : q' = q
          · subst hq'_eq
            dsimp only
            rw [dif_pos rfl, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
          · have hq'_in_l' : q' ∈ l'.primeFactors :=
              m7_mem_l'_of_ne_q h_pf_eq hq'_in hq'_eq
            haveI := m7_NeZero_Nl2_div_q (N := N) (l := l) hq'_in
            haveI : NeZero (((N * q ^ 2) * l' ^ 2) / q') := by rw [h_level_eq]; infer_instance
            have h_dvd_inner : ((N * q ^ 2) * l' ^ 2) / q' ∣ (N * q ^ 2) * l' ^ 2 :=
              Nat.div_dvd_of_dvd (by rw [h_level_eq]; exact m7_q_dvd_Nl2 (N := N) hq'_in)
            have h_chain := m7_chiFHelper_chain χ hNNq2 (Nat.dvd_mul_right _ _) hNM'
              h_lvl_dvd h_dvd_inner (χ_F_helper_rel q' hq'_in_l')
            dsimp only
            rw [dif_neg hq'_eq, MonoidHom.comp_assoc, ZMod.unitsMap_comp]
            convert h_chain using 2
        · intro n
          rw [h_pf_eq, Finset.sum_insert hq_not_in_l']
          simp only [if_true]
          rw [← h_an_f'_eq_f n, g_helper_qexp n, m7_qExp_zero_branch q n, zero_add]
          apply Finset.sum_congr rfl
          intro q' hq'_in_l'
          have hq'_ne_q : q' ≠ q := fun h ↦ hq_not_in_l' (h ▸ hq'_in_l')
          rw [if_neg hq'_ne_q]
          rfl

/-- **Miyake Lemma 4.6.7, p. 159**: squarefree decomposition of cusp forms.

For `l > 1` squarefree and `f ∈ G_k(N, χ)` a cusp form with `aₙ(f) = 0` for all `n`
coprime to `l`, there exist cusp forms `g_p ∈ G_k(Nl², χ)` for each prime `p ∣ l` such
that `aₙ(f) = Σ_{p ∣ l} aₙ/p(g_p)` (equivalently `f(z) = Σ_{p ∣ l} g_p(p·z)`). -/
theorem miyake_4_6_7_squarefree_decomp
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (l : ℕ) (hl_gt : 1 < l) (hl_sqfree : Squarefree l)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n l →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    haveI hM_NeZero : NeZero (N * l ^ 2) := ⟨by
      have hl_ne : l ≠ 0 := by lia
      exact Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero 2 hl_ne)⟩
    have hNM : N ∣ N * l ^ 2 := Nat.dvd_mul_right N (l ^ 2)
    ∃ g : ℕ → CuspForm ((Gamma1 (N * l ^ 2)).map (mapGL ℝ)) k,
      (∀ q ∈ l.primeFactors,
        g q ∈ cuspFormCharSpace k (χ.comp (ZMod.unitsMap hNM))) ∧
      ∀ n : ℕ,
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        ∑ q ∈ l.primeFactors,
          if q ∣ n then (ModularFormClass.qExpansion (1 : ℝ) (g q)).coeff (n / q)
          else 0 := by
  obtain ⟨g, _F, _χ_F, h_g_char, _, _, _, h_qexp⟩ :=
    miyake_4_6_7_squarefree_decomp_with_lower_level χ f hfχ l hl_gt hl_sqfree h_vanish
  exact ⟨g, h_g_char, h_qexp⟩

private lemma qExpansion_one_coe_zero_coeff (f : UpperHalfPlane → ℂ) (hf : f = 0) (n : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0 := by
  subst hf
  rw [qExpansion_zero]
  simp

private lemma qExpansion_one_cuspForm_cast_coeff {A B : ℕ} {k : ℤ} (h : A = B)
    (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k) (n : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        ⇑(h ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k)).coeff n =
      (ModularFormClass.qExpansion (1 : ℝ) ⇑x).coeff n := by
  cases h
  rfl

private lemma cuspFormCharSpace_mem_cast {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (h : A = B) (χ₀ : (ZMod A)ˣ →* ℂˣ) (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k)
    (hx : x ∈ cuspFormCharSpace k χ₀) :
    (h ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) ∈
      cuspFormCharSpace k (h ▸ χ₀ : (ZMod B)ˣ →* ℂˣ) := by
  cases h
  exact hx

private lemma qExpansion_one_levelRaise_coeff {M : ℕ} [NeZero M] {k : ℤ} (p : ℕ) [NeZero p]
    (g_p : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        ⇑(HeckeRing.GL2.levelRaise M p k g_p)).coeff n =
      if p ∣ n then (ModularFormClass.qExpansion (1 : ℝ) ⇑g_p).coeff (n / p) else 0 :=
  HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff g_p.toModularForm' n

/-- **M7: The `q`-expansion identity** (Miyake Eq. 4.6.12). For `f ∈ S_k(Γ_1(N), χ)`
with coprime-vanishing wrt `p · l'`, there exists a cusp form `g_low` at level
`Γ_1(l' · (N/p))` with `a_n(f) = a_{n/p}(g_low)` for every `n` with `p ∣ n` and
`Coprime n l'`. -/
theorem miyake_V_p_descend_identity
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    haveI : NeZero (l' * (N / p)) := ⟨Nat.mul_ne_zero
      (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne _)⟩
    ∃ g_low : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k,
      ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff (n / p) := by
  haveI : NeZero (l' * (N / p)) := ⟨Nat.mul_ne_zero
    (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne _)⟩
  obtain ⟨g, hg_char, hg_supp, hg_qexp⟩ :=
    miyake_g_p_supported χ f hfχ p hp l' hl'_pos hl'_sqfree hl'_dvd h_vanish
  haveI : NeZero (l' * N) :=
    ⟨Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne N)⟩
  have hpM : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have h_Mp_eq : (l' * N) / p = l' * (N / p) := Nat.mul_div_assoc l' hpN
  haveI : NeZero ((l' * N) / p) := h_Mp_eq ▸ inferInstance
  let χ_M : DirichletCharacter ℂ (l' * N) :=
    MulChar.ofUnitHom (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l')))
  have hg_χM : g ∈ cuspFormCharSpace k χ_M.toUnitHom := by
    rw [show χ_M.toUnitHom = χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l')) from
      MulChar.equivToUnitHom.apply_symm_apply _]
    exact hg_char
  rcases miyake_4_6_4_dichotomy χ_M p hp hpM g hg_χM hg_supp with hg_zero | ⟨g_p, hg_p_eq⟩
  · refine ⟨0, fun n _ hn_cop_l' ↦ ?_⟩
    have h_g_zero : (⇑g : UpperHalfPlane → ℂ) = 0 := by rw [hg_zero]; rfl
    have := hg_qexp n
    rw [if_pos hn_cop_l', qExpansion_one_coe_zero_coeff _ h_g_zero n] at this
    rw [← this, qExpansion_one_coe_zero_coeff
      (⇑(0 : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k)) rfl (n / p)]
  · refine ⟨h_Mp_eq ▸ g_p, fun n hpn hn_cop_l' ↦ ?_⟩
    have h_qExp_Vp_eq_g :
        ModularFormClass.qExpansion (1 : ℝ)
          ⇑(HeckeRing.GL2.levelRaise ((l' * N) / p) p k g_p) =
        ModularFormClass.qExpansion (1 : ℝ) ⇑g :=
      qExpansion_ext2 _ _ hg_p_eq
    have h_an_g_eq_f : (ModularFormClass.qExpansion (1 : ℝ) ⇑g).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) ⇑f).coeff n := by
      simpa [if_pos hn_cop_l'] using hg_qexp n
    rw [qExpansion_one_cuspForm_cast_coeff h_Mp_eq g_p (n / p), ← h_an_g_eq_f,
      ← h_qExp_Vp_eq_g, qExpansion_one_levelRaise_coeff p g_p n, if_pos hpn]

/-- **M-V_p-descend-strong: strengthened V_p descent identity with character info.**

Like `miyake_V_p_descend_identity`, but additionally exposes a character `χ_low`
on `(ZMod (l' * (N/p)))ˣ` with `g_low ∈ cuspFormCharSpace k χ_low`, derived from
M4-strong's lowered character `(loweredCharacter h_fac).toUnitHom` at level
`(l'·N)/p` and transported across `(l'·N)/p = l' · (N/p)`. -/
theorem miyake_V_p_descend_identity_with_char
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (l' : ℕ) (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    haveI : NeZero (l' * (N / p)) := ⟨Nat.mul_ne_zero
      (Nat.pos_iff_ne_zero.mp hl'_pos) (NeZero.ne _)⟩
    ∃ (χ_low : (ZMod (l' * (N / p)))ˣ →* ℂˣ)
      (g_low : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k),
      g_low ∈ cuspFormCharSpace k χ_low ∧
      (∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff (n / p)) ∧
      (∀ m : ℕ,
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0) := by
  haveI : NeZero l' := ⟨hl'_pos.ne'⟩
  obtain ⟨g, hg_char, hg_supp, hg_qexp⟩ :=
    miyake_g_p_supported χ f hfχ p hp l' hl'_pos hl'_sqfree hl'_dvd h_vanish
  have hpM : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have h_Mp_eq : (l' * N) / p = l' * (N / p) := Nat.mul_div_assoc l' hpN
  haveI : NeZero ((l' * N) / p) := h_Mp_eq ▸ inferInstance
  let χ_M_homU : (ZMod (l' * N))ˣ →* ℂˣ := χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l'))
  let χ_M : DirichletCharacter ℂ (l' * N) := MulChar.ofUnitHom χ_M_homU
  have hg_χM : g ∈ cuspFormCharSpace k χ_M.toUnitHom := by
    rw [show χ_M.toUnitHom = χ_M_homU from MulChar.equivToUnitHom.apply_symm_apply _]
    exact hg_char
  have h_cop_iff : ∀ m : ℕ, Nat.Coprime (p * m) l' ↔ Nat.Coprime m l' := fun m =>
    ⟨fun h => (Nat.coprime_mul_iff_left.mp h).2,
      fun h => Nat.coprime_mul_iff_left.mpr ⟨hpl', h⟩⟩
  rcases miyake_4_6_4_dichotomy_strong χ_M p hp hpM g hg_χM hg_supp with
    hg_zero | ⟨h_fac, g_p, hg_p_char, hg_p_eq⟩
  · have h_g_zero : (⇑g : UpperHalfPlane → ℂ) = 0 := by
      rw [hg_zero]
      rfl
    have h_zero_low : (⇑(0 : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k) :
        UpperHalfPlane → ℂ) = 0 := rfl
    have h_an_g (n : ℕ) : (ModularFormClass.qExpansion (1 : ℝ) ⇑g).coeff n = 0 :=
      qExpansion_one_coe_zero_coeff _ h_g_zero n
    refine ⟨1, 0, Submodule.zero_mem _, ?_, ?_⟩
    · intro n _ hn_cop_l'
      have := hg_qexp n
      rw [if_pos hn_cop_l', h_an_g n] at this
      rw [qExpansion_one_coe_zero_coeff _ h_zero_low (n / p), ← this]
    · intro m
      rw [qExpansion_one_coe_zero_coeff _ h_zero_low m]
      by_cases hcop : Nat.Coprime m l'
      · have := hg_qexp (p * m)
        rw [if_pos ((h_cop_iff m).mpr hcop), h_an_g (p * m)] at this
        rw [if_pos hcop, ← this]
      · rw [if_neg hcop]
  · have h_qExp_Vp_eq_g :
        ModularFormClass.qExpansion (1 : ℝ)
          ⇑(HeckeRing.GL2.levelRaise ((l' * N) / p) p k g_p) =
        ModularFormClass.qExpansion (1 : ℝ) ⇑g :=
      qExpansion_ext2 _ _ hg_p_eq
    refine ⟨h_Mp_eq ▸ (HeckeRing.GL2.loweredCharacter h_fac).toUnitHom, h_Mp_eq ▸ g_p,
      cuspFormCharSpace_mem_cast h_Mp_eq _ g_p hg_p_char, ?_, ?_⟩
    · intro n hpn hn_cop_l'
      have h_an_g_eq_f : (ModularFormClass.qExpansion (1 : ℝ) ⇑g).coeff n =
          (ModularFormClass.qExpansion (1 : ℝ) ⇑f).coeff n := by
        have := hg_qexp n
        rwa [if_pos hn_cop_l'] at this
      rw [qExpansion_one_cuspForm_cast_coeff h_Mp_eq g_p (n / p), ← h_an_g_eq_f,
        ← h_qExp_Vp_eq_g, qExpansion_one_levelRaise_coeff p g_p n, if_pos hpn]
    · intro m
      have h_g_p_eq : (ModularFormClass.qExpansion (1 : ℝ) ⇑g_p).coeff m =
          (ModularFormClass.qExpansion (1 : ℝ) ⇑g).coeff (p * m) := by
        rw [← h_qExp_Vp_eq_g, qExpansion_one_levelRaise_coeff p g_p (p * m),
          if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.pos]
      rw [qExpansion_one_cuspForm_cast_coeff h_Mp_eq g_p m, h_g_p_eq, hg_qexp (p * m)]
      simp only [h_cop_iff]

private lemma modularForm_fun_eq_of_qExp_eq_at_period_one
    {M : ℕ} [NeZero M] {k : ℤ}
    (h_period : (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods)
    (f g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h_qExp_eq : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g).coeff n) :
    (⇑f : UpperHalfPlane → ℂ) = ⇑g := by
  have h_diff_qExp_zero : ModularFormClass.qExpansion (1 : ℝ) (f - g) = 0 := by
    rw [qExpansion_sub one_pos h_period f g]
    ext n
    simp [map_sub, h_qExp_eq n]
  have h_diff_zero : f - g = 0 :=
    (qExpansion_eq_zero_iff one_pos h_period (f - g)).mp h_diff_qExp_zero
  funext z
  exact sub_eq_zero.mp (DFunLike.congr_fun h_diff_zero z)

private lemma miyake_descent_l_prime_eq_one_helper
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {p : ℕ} [NeZero p]
    {M : ℕ} [NeZero M]
    (g_low_cast : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hp_M_eq_N : p * M = N)
    (h_Fourier_eq : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) ⇑f).coeff n =
      (ModularFormClass.qExpansion (1 : ℝ)
        ⇑(HeckeRing.GL2.modularFormLevelRaise M p k g_low_cast.toModularForm')).coeff n) :
    (⇑f.toModularForm' : UpperHalfPlane → ℂ) =
    ⇑(HeckeRing.GL2.modularFormLevelRaise M p k g_low_cast.toModularForm') := by
  have hN_dvd_pM : N ∣ p * M := by rw [hp_M_eq_N]
  have h1_period_pM : (1 : ℝ) ∈ ((Gamma1 (p * M)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (p * M)).map (mapGL ℝ) =
        (Gamma1 (p * M) : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have : NeZero (p * M) := by rw [hp_M_eq_N]; infer_instance
  exact modularForm_fun_eq_of_qExp_eq_at_period_one (M := p * M)
    (k := k) h1_period_pM
    (ModularForm.restrictSubgroup
      (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hN_dvd_pM)
      f.toModularForm')
    (HeckeRing.GL2.modularFormLevelRaise M p k g_low_cast.toModularForm')
    h_Fourier_eq

private lemma qExp_z_to_qz_zero_of_not_dvd
    {L : ℕ} [NeZero L] {k : ℤ}
    (q : ℕ) [NeZero q]
    (G : ModularForm ((Gamma1 L).map (mapGL ℝ)) k)
    (m : ℕ) (hq_not_m : ¬ q ∣ m) :
    (ModularFormClass.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦
        (⇑(HeckeRing.GL2.modularFormLevelRaise L q k G) :
          UpperHalfPlane → ℂ) z)).coeff m = 0 := by
  simp only [HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff G m, if_neg hq_not_m]

private noncomputable def slash_sum_V_q_cuspForm_descend
    {M_q : ℕ} [NeZero M_q] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpM_q : p ∣ M_q) [NeZero (M_q / p)]
    (q : ℕ) [NeZero q]
    (χ_F : (ZMod M_q)ˣ →* ℂˣ)
    (χ_F_low : (ZMod (M_q / p))ˣ →* ℂˣ)
    (h_χ_F_factor : χ_F = χ_F_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM_q)))
    (F_q : CuspForm ((Gamma1 M_q).map (mapGL ℝ)) k)
    (hF_q_char : F_q ∈ cuspFormCharSpace k χ_F) :
    haveI : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
    have h_qMp_dvd : p ∣ q * M_q := dvd_mul_of_dvd_right hpM_q q
    haveI : NeZero ((q * M_q) / p) := ⟨Nat.ne_of_gt (Nat.div_pos
        (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q) (NeZero.pos M_q)) h_qMp_dvd) hp.pos)⟩
    CuspForm ((Gamma1 ((q * M_q) / p)).map (mapGL ℝ)) k :=
  have : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
  have h_qMp_dvd : p ∣ q * M_q := dvd_mul_of_dvd_right hpM_q q
  have : NeZero ((q * M_q) / p) := ⟨Nat.ne_of_gt (Nat.div_pos
      (Nat.le_of_dvd (Nat.mul_pos (NeZero.pos q) (NeZero.pos M_q)) h_qMp_dvd) hp.pos)⟩
  let V_q_F_q : CuspForm ((Gamma1 (q * M_q)).map (mapGL ℝ)) k :=
    HeckeRing.GL2.levelRaise M_q q k F_q
  have hV_q_F_q_char : V_q_F_q ∈ cuspFormCharSpace k
      (χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q))) :=
    cuspForm_levelRaise_mem_cuspFormCharSpace M_q q k χ_F hF_q_char
  have hV_q_F_q_mod : V_q_F_q.toModularForm' ∈ modFormCharSpace k
      (χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q))) :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) _ V_q_F_q).mpr hV_q_F_q_char
  have h_Mq_div_p_dvd_qMq_div_p : M_q / p ∣ (q * M_q) / p := by
    rcases hpM_q with ⟨a, ha⟩
    subst ha
    simp [Nat.mul_div_cancel_left _ hp.pos, mul_comm q, mul_assoc]
  let χ_F_low_lifted : (ZMod ((q * M_q) / p))ˣ →* ℂˣ :=
    χ_F_low.comp (ZMod.unitsMap h_Mq_div_p_dvd_qMq_div_p)
  have h_χ_F_lifted_factor :
      χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q)) =
      χ_F_low_lifted.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd h_qMp_dvd)) := by
    change χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q)) =
      (χ_F_low.comp (ZMod.unitsMap h_Mq_div_p_dvd_qMq_div_p)).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd h_qMp_dvd))
    rw [h_χ_F_factor, MonoidHom.comp_assoc _ _ χ_F_low, ZMod.unitsMap_comp,
        MonoidHom.comp_assoc _ _ χ_F_low, ZMod.unitsMap_comp]
  { toFun := fun z ↦ ∑ v : Fin (descendCosetCount p (q * M_q)),
      ((⇑V_q_F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
        descendCosetList p (q * M_q) hp v) z
    slash_action_eq' := fun γ hγ => by
      obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
      exact miyake_hecke_descend_Gamma1_inv p hp h_qMp_dvd
        (χ_F.comp (ZMod.unitsMap (Nat.dvd_mul_left M_q q)))
        χ_F_low_lifted h_χ_F_lifted_factor
        hV_q_F_q_mod γ' h_γ'_Gamma1
    holo' := by
      change MDifferentiable _ _ (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p (q * M_q)),
          ((⇑V_q_F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p (q * M_q) hp v) z)
      rw [show (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (q * M_q)),
              ((⇑V_q_F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
                descendCosetList p (q * M_q) hp v) z) =
            ∑ v : Fin (descendCosetCount p (q * M_q)),
              ((⇑V_q_F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
                descendCosetList p (q * M_q) hp v) from
          funext fun z ↦ (Finset.sum_apply _ _ _).symm]
      exact MDifferentiable.sum
        (fun v _ => (ModularFormClass.holo V_q_F_q.toModularForm').slash k _)
    zero_at_cusps' := fun {cusp} hc => miyake_hecke_descend_cusp p hp h_qMp_dvd V_q_F_q hc }

private lemma per_q_slash_sum_at_deep_qexp_zero
    {M_q : ℕ} [NeZero M_q] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpM_q : p ∣ M_q) [NeZero (M_q / p)]
    (q : ℕ) [NeZero q] (hpq : Nat.Coprime p q) (hq_dvd_Mq_div_p : q ∣ M_q / p)
    (χ_F : (ZMod M_q)ˣ →* ℂˣ)
    (χ_F_low : (ZMod (M_q / p))ˣ →* ℂˣ)
    (h_χ_F_factor : χ_F = χ_F_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM_q)))
    (F_q : CuspForm ((Gamma1 M_q).map (mapGL ℝ)) k)
    (hF_q_char : F_q ∈ cuspFormCharSpace k χ_F)
    (m : ℕ) (hq_not_m : ¬ q ∣ m) :
    haveI : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
    (ModularFormClass.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (q * M_q)),
        ((⇑(HeckeRing.GL2.modularFormLevelRaise M_q q k F_q.toModularForm') :
          UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p (q * M_q) hp v) z)).coeff m = 0 := by
  haveI : NeZero (q * M_q) := ⟨Nat.mul_ne_zero (NeZero.ne q) (NeZero.ne M_q)⟩
  have hF_q_mod : F_q.toModularForm' ∈ modFormCharSpace k χ_F :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
      (k := k) χ_F F_q).mpr hF_q_char
  have h_M6_2 := miyake_4_6_6_level_commute_delta (N := M_q) (l := q) (k := k)
    p hp hpM_q hpq hq_dvd_Mq_div_p χ_F χ_F_low h_χ_F_factor
    F_q.toModularForm' hF_q_mod
  let G_q : CuspForm ((Gamma1 (M_q / p)).map (mapGL ℝ)) k :=
    { toFun := fun z => ∑ v : Fin (descendCosetCount p M_q),
        ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p M_q hp v) z
      slash_action_eq' := fun γ hγ => by
        obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
        exact miyake_hecke_descend_Gamma1_inv p hp hpM_q χ_F χ_F_low h_χ_F_factor
          hF_q_mod γ' h_γ'_Gamma1
      holo' := by
        change MDifferentiable _ _ (fun z : UpperHalfPlane ↦
          ∑ v : Fin (descendCosetCount p M_q),
            ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
              descendCosetList p M_q hp v) z)
        rw [show (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p M_q),
              ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
                descendCosetList p M_q hp v) z) =
            ∑ v : Fin (descendCosetCount p M_q),
              ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
                descendCosetList p M_q hp v) from
          funext fun z => (Finset.sum_apply _ _ _).symm]
        exact MDifferentiable.sum
          (fun v _ => (ModularFormClass.holo F_q.toModularForm').slash k _)
      zero_at_cusps' := fun {cusp} hc => miyake_hecke_descend_cusp p hp hpM_q F_q hc }
  have h_fun_eq_V_q_G : (fun z : UpperHalfPlane ↦
      ∑ v : Fin (descendCosetCount p M_q),
        ((⇑F_q.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p M_q hp v) (HeckeRing.GL2.levelRaiseMatrix q • z)) =
      (fun z : UpperHalfPlane ↦
        (⇑(HeckeRing.GL2.modularFormLevelRaise (M_q / p) q k G_q.toModularForm') :
          UpperHalfPlane → ℂ) z) := by
    funext z
    change _ = (⇑(HeckeRing.GL2.modularFormLevelRaise _ _ _ _)) z
    rw [HeckeRing.GL2.modularFormLevelRaise_apply]
    rfl
  have h_slash_sum_eq : (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (q * M_q)),
      ((⇑(HeckeRing.GL2.modularFormLevelRaise M_q q k F_q.toModularForm') :
        UpperHalfPlane → ℂ) ∣[k]
        descendCosetList p (q * M_q) hp v) z) =
    (fun z : UpperHalfPlane ↦
      (⇑(HeckeRing.GL2.modularFormLevelRaise (M_q / p) q k G_q.toModularForm') :
        UpperHalfPlane → ℂ) z) := by
    funext z
    rw [h_M6_2 z]
    exact congr_fun h_fun_eq_V_q_G z
  rw [h_slash_sum_eq]
  exact qExp_z_to_qz_zero_of_not_dvd q G_q.toModularForm' m hq_not_m

private lemma slash_sum_at_M_eq_of_function_eq
    (p M : ℕ) [NeZero p] [NeZero M] (hp : p.Prime)
    (k : ℤ) (f g : UpperHalfPlane → ℂ) (hfg : f = g) :
    (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p M),
      (f ∣[k] descendCosetList p M hp v) z) =
    (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p M),
      (g ∣[k] descendCosetList p M hp v) z) := by
  subst hfg; rfl

private lemma slash_sum_linear_over_Finset_sum
    {α : Type*}
    (p M : ℕ) [NeZero p] [NeZero M] (hp : p.Prime) (k : ℤ)
    (s : Finset α) (h : α → UpperHalfPlane → ℂ) :
    (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p M),
      ((fun w : UpperHalfPlane => ∑ a ∈ s, h a w) ∣[k]
        descendCosetList p M hp v) z) =
    (fun z : UpperHalfPlane ↦ ∑ a ∈ s,
      ∑ v : Fin (descendCosetCount p M),
        (h a ∣[k] descendCosetList p M hp v) z) := by
  funext z
  have h_pi_sum : (fun w : UpperHalfPlane => ∑ a ∈ s, h a w) =
      (∑ a ∈ s, h a : UpperHalfPlane → ℂ) := by
    funext w; rw [Finset.sum_apply]
  rw [h_pi_sum]
  have h_inner : ∀ v : Fin (descendCosetCount p M),
      ((∑ a ∈ s, h a : UpperHalfPlane → ℂ) ∣[k] descendCosetList p M hp v) z =
      ∑ a ∈ s, (h a ∣[k] descendCosetList p M hp v) z := by
    intro v
    rw [SlashAction.sum_slash, Finset.sum_apply]
  simp_rw [h_inner]
  rw [Finset.sum_comm]

private lemma function_identity_Δ_eq_sum_V_q_F
    {L : ℕ} [NeZero L] {k : ℤ}
    (Δ : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (l : ℕ) [NeZero l]
    (g_q_fam : ℕ → CuspForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k)
    (hL_dvd : L ∣ L * l ^ 2)
    (h_q_NeZero : ∀ q ∈ l.primeFactors, NeZero ((L * l ^ 2) / q))
    (h_q_dvd_Ll2 : ∀ q ∈ l.primeFactors, q ∣ L * l ^ 2)
    (F_q_fam : (q : ℕ) → (hq : q ∈ l.primeFactors) →
      letI := h_q_NeZero q hq
      CuspForm ((Gamma1 ((L * l ^ 2) / q)).map (mapGL ℝ)) k)
    (hF_eq_g : ∀ q (hq : q ∈ l.primeFactors),
      letI := h_q_NeZero q hq
      (⇑(F_q_fam q hq) : UpperHalfPlane → ℂ) = ⇑(g_q_fam q))
    (h_qexp_eq : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) Δ).coeff n =
      ∑ q ∈ l.primeFactors,
        if q ∣ n then (ModularFormClass.qExpansion (1 : ℝ) (g_q_fam q)).coeff (n / q)
        else 0) :
    haveI : NeZero (L * l ^ 2) :=
      ⟨Nat.mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 (NeZero.ne l))⟩
    (⇑(CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hL_dvd) Δ) :
      UpperHalfPlane → ℂ) =
    fun z => ∑ q ∈ l.primeFactors.attach,
      (haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
       haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
       (⇑(HeckeRing.GL2.modularFormLevelRaise ((L * l ^ 2) / q.val) q.val k
         (F_q_fam q.val q.property).toModularForm') :
         UpperHalfPlane → ℂ) z) := by
  haveI hLl2_NeZero : NeZero (L * l ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne L) (pow_ne_zero 2 (NeZero.ne l))⟩
  have h1_period_Ll2 := m7_one_mem_strictPeriods_Gamma1_map (L * l ^ 2)
  let φ : (q : l.primeFactors) → ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k :=
    fun q =>
      haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
      haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
      have h_eq : q.val * ((L * l ^ 2) / q.val) = L * l ^ 2 :=
        Nat.mul_div_cancel' (h_q_dvd_Ll2 q.val q.property)
      h_eq ▸ HeckeRing.GL2.modularFormLevelRaise
        ((L * l ^ 2) / q.val) q.val k (F_q_fam q.val q.property).toModularForm'
  let RHS_sum : ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k :=
    ∑ q ∈ l.primeFactors.attach, φ q
  let Δ_lifted : ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k :=
    ModularForm.restrictSubgroup
      (HeckeRing.GL2.MainLemma.Gamma1_mapGL_le_of_dvd hL_dvd) Δ.toModularForm'
  have h_φ_fun : ∀ q : l.primeFactors, ∀ z : UpperHalfPlane,
      (φ q : UpperHalfPlane → ℂ) z =
      (haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
       haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
       (⇑(HeckeRing.GL2.modularFormLevelRaise ((L * l ^ 2) / q.val) q.val k
         (F_q_fam q.val q.property).toModularForm') :
         UpperHalfPlane → ℂ) z) := by
    intro q z
    haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
    haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
    have h_eq : q.val * ((L * l ^ 2) / q.val) = L * l ^ 2 :=
      Nat.mul_div_cancel' (h_q_dvd_Ll2 q.val q.property)
    change (h_eq ▸ HeckeRing.GL2.modularFormLevelRaise
            ((L * l ^ 2) / q.val) q.val k
            (F_q_fam q.val q.property).toModularForm' :
        ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k) z = _
    have h_gen : ∀ {A B : ℕ} [NeZero A] [NeZero B] (h : A = B)
        (f₀ : ModularForm ((Gamma1 A).map (mapGL ℝ)) k) (z₀ : UpperHalfPlane),
        ((h ▸ f₀ : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) :
          UpperHalfPlane → ℂ) z₀ =
        (f₀ : UpperHalfPlane → ℂ) z₀ := by intros; subst_vars; rfl
    exact h_gen h_eq _ z
  have h_φ_qexp : ∀ q : l.primeFactors, ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) (φ q)).coeff n =
      (if q.val ∣ n then
        (ModularFormClass.qExpansion (1 : ℝ) (g_q_fam q.val)).coeff (n / q.val)
       else 0) := by
    intro q n
    haveI : NeZero ((L * l ^ 2) / q.val) := h_q_NeZero q.val q.property
    haveI : NeZero q.val := ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
    have h_eq : q.val * ((L * l ^ 2) / q.val) = L * l ^ 2 :=
      Nat.mul_div_cancel' (h_q_dvd_Ll2 q.val q.property)
    change (ModularFormClass.qExpansion (1 : ℝ)
        (h_eq ▸ HeckeRing.GL2.modularFormLevelRaise
          ((L * l ^ 2) / q.val) q.val k
          (F_q_fam q.val q.property).toModularForm' :
            ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k)).coeff n = _
    have h_gen_qe : ∀ {A B : ℕ} [NeZero A] [NeZero B] (h : A = B)
        (f₀ : ModularForm ((Gamma1 A).map (mapGL ℝ)) k),
        ModularFormClass.qExpansion (1 : ℝ)
          (h ▸ f₀ : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) =
        ModularFormClass.qExpansion (1 : ℝ) f₀ := by intros; subst_vars; rfl
    rw [h_gen_qe h_eq _,
      HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff
        (F_q_fam q.val q.property).toModularForm' n,
      qExpansion_ext2 (F_q_fam q.val q.property).toModularForm' (g_q_fam q.val)
        (hF_eq_g q.val q.property)]
  suffices h_main : (⇑Δ_lifted : UpperHalfPlane → ℂ) = ⇑RHS_sum by
    change (⇑Δ_lifted : UpperHalfPlane → ℂ) = _
    rw [h_main]
    funext z
    have h_coe_sum : ∀ s : Finset l.primeFactors,
        ((∑ q ∈ s, φ q : ModularForm ((Gamma1 (L * l ^ 2)).map (mapGL ℝ)) k) :
          UpperHalfPlane → ℂ) z =
        ∑ q ∈ s, (⇑(φ q) : UpperHalfPlane → ℂ) z := by
      intro s
      refine Finset.induction_on s ?_ fun q s hqs ih => ?_
      · simp
      · rw [Finset.sum_insert hqs, Finset.sum_insert hqs,
          ModularForm.coe_add, Pi.add_apply, ih]
    rw [show (⇑RHS_sum : UpperHalfPlane → ℂ) z = _ from h_coe_sum l.primeFactors.attach]
    exact Finset.sum_congr rfl fun q _ => h_φ_fun q z
  apply modularForm_fun_eq_of_qExp_eq_at_period_one h1_period_Ll2
  intro n
  change (PowerSeries.coeff (R := ℂ) n) (ModularFormClass.qExpansion 1 ⇑Δ) = _
  rw [h_qexp_eq n,
    show ModularFormClass.qExpansion (1 : ℝ) RHS_sum =
        ∑ q ∈ l.primeFactors.attach, ModularFormClass.qExpansion (1 : ℝ) (φ q) from
      map_sum (qExpansionAddHom (Γ := (Gamma1 (L * l ^ 2)).map (mapGL ℝ))
        (h := (1 : ℝ)) one_pos h1_period_Ll2 k) φ l.primeFactors.attach,
    map_sum (PowerSeries.coeff (R := ℂ) n) _ l.primeFactors.attach,
    show ∑ q ∈ l.primeFactors.attach,
          (ModularFormClass.qExpansion (1 : ℝ) (φ q)).coeff n =
        ∑ q ∈ l.primeFactors.attach,
          (if q.val ∣ n then
            (ModularFormClass.qExpansion (1 : ℝ) (g_q_fam q.val)).coeff (n / q.val)
           else 0) from
      Finset.sum_congr rfl fun q _ => h_φ_qexp q n]
  exact (Finset.sum_attach l.primeFactors
    (fun q => if q ∣ n then
        (ModularFormClass.qExpansion (1 : ℝ) (g_q_fam q)).coeff (n / q)
      else 0)).symm

private lemma prime_in_factors_p_dvd_div_q {N p l' : ℕ}
    (hp : p.Prime) (hpN : p ∣ N) (hp_not_in : p ∉ l'.primeFactors)
    (q : ℕ) (hq_mem : q ∈ l'.primeFactors)
    (hq_dvd_Ll2 : q ∣ (l' * N) * l' ^ 2) :
    p ∣ ((l' * N) * l' ^ 2) / q := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hpq_cop : Nat.Coprime p q := by
    rw [hp.coprime_iff_not_dvd]
    intro hpq
    exact hp_not_in <| (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq ▸ hq_mem
  have hp_dvd_full : p ∣ (l' * N) * l' ^ 2 :=
    dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpN l') _
  rcases hp_dvd_full with ⟨c1, hc1⟩
  have : q ∣ c1 := hpq_cop.symm.dvd_of_dvd_mul_left (hc1 ▸ hq_dvd_Ll2)
  rcases this with ⟨c2, hc2⟩
  refine ⟨c2, ?_⟩
  rw [hc1, hc2, show p * (q * c2) = q * (p * c2) by ring,
    Nat.mul_div_cancel_left _ hq_prime.pos]

private lemma prime_in_factors_q_dvd_div_q_div_p {N p l' : ℕ}
    (hp : p.Prime) (hpN : p ∣ N)
    (q : ℕ) (hq_mem : q ∈ l'.primeFactors)
    (hq_dvd_Ll2 : q ∣ (l' * N) * l' ^ 2) :
    q ∣ ((l' * N) * l' ^ 2) / q / p := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_dvd_l' : q ∣ l' := Nat.dvd_of_mem_primeFactors hq_mem
  have hq_dvd_l'2 : q ∣ l' ^ 2 := hq_dvd_l'.trans (dvd_pow_self l' two_ne_zero)
  have hq2p_dvd : q * (q * p) ∣ (l' * N) * l' ^ 2 := by
    have h1 : q * q ∣ l' ^ 2 := by rw [sq]; exact mul_dvd_mul hq_dvd_l' hq_dvd_l'
    have h2 : (q * q) * p ∣ l' ^ 2 * N := mul_dvd_mul h1 hpN
    have h_reorg : l' ^ 2 * N ∣ (l' * N) * l' ^ 2 := ⟨l', by ring⟩
    rw [show q * (q * p) = q * q * p by ring]
    exact h2.trans h_reorg
  have hM_q_eq : q * (((l' * N) * l' ^ 2) / q) = (l' * N) * l' ^ 2 :=
    Nat.mul_div_cancel' hq_dvd_Ll2
  have hqp_dvd_Mq : q * p ∣ ((l' * N) * l' ^ 2) / q := by
    rcases hq2p_dvd with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have h_extract : q * (q * p * c) = (l' * N) * l' ^ 2 := by rw [hc]; ring
    exact Nat.eq_of_mul_eq_mul_left hq_prime.pos (by rw [hM_q_eq, ← h_extract])
  rcases hqp_dvd_Mq with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw [hc, show q * p * c = p * (q * c) by ring, Nat.mul_div_cancel_left _ hp.pos]

private lemma prime_in_factors_lN_div_p_dvd_div_q_div_p {N p l' : ℕ}
    (hp : p.Prime) (hpN : p ∣ N)
    (q : ℕ) (hq_mem : q ∈ l'.primeFactors) :
    (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q / p := by
  have hq_prime : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
  have hq_dvd_l' : q ∣ l' := Nat.dvd_of_mem_primeFactors hq_mem
  have hq_dvd_l'2 : q ∣ l' ^ 2 := hq_dvd_l'.trans (dvd_pow_self l' two_ne_zero)
  have h_lN_dvd_Mq : l' * N ∣ ((l' * N) * l' ^ 2) / q := by
    rcases hq_dvd_l'2 with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have : (l' * N) * l' ^ 2 = (l' * N) * (q * c) := by rw [hc]
    rw [this, show (l' * N) * (q * c) = q * (l' * N * c) by ring,
      Nat.mul_div_cancel_left _ hq_prime.pos]
  rcases h_lN_dvd_Mq with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rcases hpN with ⟨d, hd⟩
  have h_lN : l' * N = p * (l' * d) := by rw [hd]; ring
  rw [hc, h_lN, show p * (l' * d) * c = p * (l' * d * c) by ring,
    Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]

private lemma χ_F_factor_via_χ_M_unit_low
    {N l' p : ℕ} [NeZero (l' * N)] [NeZero (l' * N * l' ^ 2)]
    (hpN : p ∣ N)
    (q : ℕ) (hq_dvd_Ll2 : q ∣ (l' * N) * l' ^ 2)
    [NeZero ((l' * N * l' ^ 2) / q)]
    (hp_dvd_Mq : p ∣ ((l' * N) * l' ^ 2) / q)
    (h_lN_div_p_dvd_Mq_div_p : (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q / p)
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ)
    (hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right hpN l'))))
    (χ_F_q : (ZMod ((l' * N) * l' ^ 2 / q))ˣ →* ℂˣ)
    (hχ_F_q : χ_F_q.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hq_dvd_Ll2)) =
      χ_M_unit.comp (ZMod.unitsMap (Nat.dvd_mul_right (l' * N) (l' ^ 2)))) :
    χ_F_q = (χ_M_unit_low.comp (ZMod.unitsMap h_lN_div_p_dvd_Mq_div_p)).comp
      (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_Mq)) := by
  have h_M_q_dvd_full : ((l' * N) * l' ^ 2) / q ∣ (l' * N) * l' ^ 2 :=
    Nat.div_dvd_of_dvd hq_dvd_Ll2
  have h_surj : Function.Surjective (ZMod.unitsMap h_M_q_dvd_full) :=
    ZMod.unitsMap_surjective h_M_q_dvd_full
  rw [← MonoidHom.cancel_right h_surj, hχ_F_q, hχ_M_unit_eq,
    MonoidHom.comp_assoc _ _ χ_M_unit_low, ZMod.unitsMap_comp,
    MonoidHom.comp_assoc _ _ χ_M_unit_low,
    MonoidHom.comp_assoc _ _ χ_M_unit_low,
    ZMod.unitsMap_comp, ZMod.unitsMap_comp]

private lemma slash_sum_descendCoset_level_recast
    {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (h_eq : A = B) (g : UpperHalfPlane → ℂ) :
    (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p A), (g ∣[k] descendCosetList p A hp v) z) =
    (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p B), (g ∣[k] descendCosetList p B hp v) z) := by
  cases h_eq
  rfl

private lemma cuspForm_level_recast_coe_apply {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ}
    (h_eq : A = B) (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (⇑(h_eq ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) z =
    (⇑x : UpperHalfPlane → ℂ) z := by
  cases h_eq
  rfl

private lemma cuspForm_finsetSum_coe_apply {α : Type*} [DecidableEq α]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (s : Finset α) (F : α → CuspForm Γ k) (z : UpperHalfPlane) :
    (⇑(∑ q ∈ s, F q) : UpperHalfPlane → ℂ) z =
      ∑ q ∈ s, (⇑(F q) : UpperHalfPlane → ℂ) z := by
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro q s hqs ih
    rw [Finset.sum_insert hqs, Finset.sum_insert hqs, CuspForm.coe_add, Pi.add_apply, ih]

private lemma cuspForm_finsetSum_toModularForm' {α : Type*} [DecidableEq α]
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (s : Finset α) (F : α → CuspForm Γ k) :
    (∑ q ∈ s, F q : CuspForm Γ k).toModularForm' =
    ∑ q ∈ s, (F q).toModularForm' := by
  refine Finset.induction_on s ?_ ?_
  · simp [Finset.sum_empty]
    rfl
  · intro q s hqs ih
    rw [Finset.sum_insert hqs, Finset.sum_insert hqs, ← ih]
    rfl

private lemma delta_slash_sum_coeff_zero_sq_case
    {L : ℕ} [NeZero L] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpL : p ∣ L) (hp_sq : p ^ 2 ∣ L)
    (Δ_form : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) (m : ℕ)
    (h_apm_zero : (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ_form).coeff (p * m) = 0) :
    (ModularFormClass.qExpansion (1 : ℝ)
      (fun z => ∑ v : Fin (descendCosetCount p L),
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p L hp v) z)).coeff m = 0 := by
  have h_cnt : descendCosetCount p L = p := by simp [descendCosetCount, hp_sq]
  have h_slash_eq_ut : (fun z : UpperHalfPlane ↦
      ∑ v : Fin (descendCosetCount p L),
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k] descendCosetList p L hp v) z) =
      (fun z : UpperHalfPlane ↦
        ∑ v ∈ Finset.range p,
          ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
            (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z) := by
    funext z
    have h_each_eq : ∀ v : Fin p,
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p L hp (Fin.cast h_cnt.symm v)) z =
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          (T_p_upper p hp.pos v.val : GL (Fin 2) ℚ)) z := by
      intro v
      have h_v_lt : (Fin.cast h_cnt.symm v).val < p := v.isLt
      have h_mat : descendCosetList p L hp (Fin.cast h_cnt.symm v) =
          glMap (T_p_upper p hp.pos v.val) := by
        unfold descendCosetList
        rw [dif_pos h_v_lt]
        apply Units.ext
        show (Matrix.GeneralLinearGroup.mkOfDetNeZero _ _).val = (glMap _).val
        rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
        show !![(1 : ℝ), (v.val : ℝ); 0, (p : ℝ)] =
            (T_p_upper p hp.pos v.val).val.map (algebraMap ℚ ℝ)
        rw [T_p_upper_coe]
        ext i j; fin_cases i <;> fin_cases j <;>
          simp [Matrix.map_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [h_mat]
      rfl
    rw [show ∑ v : Fin (descendCosetCount p L),
            ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k] descendCosetList p L hp v) z =
          ∑ v : Fin p,
            ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
              descendCosetList p L hp (Fin.cast h_cnt.symm v)) z from
      (Fintype.sum_equiv (finCongr h_cnt.symm) _ _ (fun _ => rfl)).symm]
    rw [show ∑ v : Fin p,
          ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p L hp (Fin.cast h_cnt.symm v)) z =
        ∑ v : Fin p,
          ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
            (T_p_upper p hp.pos v.val : GL (Fin 2) ℚ)) z from
      Finset.sum_congr rfl (fun v _ ↦ h_each_eq v)]
    exact Fin.sum_univ_eq_sum_range
      (f := fun n ↦ ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
        (T_p_upper p hp.pos n : GL (Fin 2) ℚ)) z) p
  rw [h_slash_eq_ut]
  have h_to_mod_eq : (⇑Δ_form : UpperHalfPlane → ℂ) =
      (⇑Δ_form.toModularForm' : UpperHalfPlane → ℂ) := rfl
  rw [show (fun z : UpperHalfPlane ↦ ∑ v ∈ Finset.range p,
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z) =
      (fun z : UpperHalfPlane ↦ ∑ v ∈ Finset.range p,
        ((⇑Δ_form.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
          (T_p_upper p hp.pos v : GL (Fin 2) ℚ)) z) by rw [h_to_mod_eq]]
  rw [miyake_descent_upper_tri_qExpansion p hp hpL Δ_form.toModularForm' m]
  exact h_apm_zero

private lemma delta_slash_sum_per_q_inner_fun_coeff_zero
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {l' : ℕ} (hp_not_in : p ∉ l'.primeFactors)
    [NeZero l'] [NeZero (l' * N)] [NeZero (l' * N / p)]
    [hLl2_NeZero : NeZero ((l' * N) * l' ^ 2)]
    (h_q_NeZero_aux : ∀ q ∈ l'.primeFactors, NeZero ((l' * N * l' ^ 2) / q))
    (h_q_dvd_Ll2_aux : ∀ q ∈ l'.primeFactors, q ∣ (l' * N) * l' ^ 2)
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ)
    (hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right hpN l'))))
    (F_q_fam : (q : ℕ) → (hq : q ∈ l'.primeFactors) →
      haveI := h_q_NeZero_aux q hq
      CuspForm ((Gamma1 (((l' * N) * l' ^ 2) / q)).map (mapGL ℝ)) k)
    (χ_F_fam : (q : ℕ) → (hq : q ∈ l'.primeFactors) →
      haveI := h_q_NeZero_aux q hq
      (ZMod ((l' * N * l' ^ 2) / q))ˣ →* ℂˣ)
    (hF_q_char : ∀ q (hq : q ∈ l'.primeFactors),
      haveI := h_q_NeZero_aux q hq
      F_q_fam q hq ∈ cuspFormCharSpace k (χ_F_fam q hq))
    (hχ_F_fam_rel : ∀ q (hq : q ∈ l'.primeFactors),
      haveI := h_q_NeZero_aux q hq
      (χ_F_fam q hq).comp (ZMod.unitsMap (Nat.div_dvd_of_dvd (h_q_dvd_Ll2_aux q hq))) =
        χ_M_unit.comp (ZMod.unitsMap (Nat.dvd_mul_right (l' * N) (l' ^ 2))))
    (q : l'.primeFactors) (m : ℕ) (hm_cop : Nat.Coprime m l') :
    haveI := h_q_NeZero_aux q.val q.property
    haveI hq_NeZero : NeZero q.val :=
      ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
    (ModularFormClass.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p ((l' * N) * l' ^ 2)),
          ((⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
            (F_q_fam q.val q.property).toModularForm') : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p ((l' * N) * l' ^ 2) hp v) z)).coeff m = 0 := by
  have hq_prime : q.val.Prime := Nat.prime_of_mem_primeFactors q.property
  have hq_dvd_l' : q.val ∣ l' := Nat.dvd_of_mem_primeFactors q.property
  haveI hq_NeZero : NeZero q.val := ⟨hq_prime.ne_zero⟩
  haveI hM_q_NeZero : NeZero ((l' * N * l' ^ 2) / q.val) :=
    h_q_NeZero_aux q.val q.property
  have hpq_cop : Nat.Coprime p q.val := by
    rw [hp.coprime_iff_not_dvd]
    intro hpq
    exact hp_not_in <| (Nat.prime_dvd_prime_iff_eq hp hq_prime).mp hpq ▸ q.property
  have hp_dvd_Mq : p ∣ ((l' * N) * l' ^ 2) / q.val :=
    prime_in_factors_p_dvd_div_q hp hpN hp_not_in q.val q.property
      (h_q_dvd_Ll2_aux q.val q.property)
  haveI hMq_div_p_NeZero : NeZero (((l' * N) * l' ^ 2) / q.val / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM_q_NeZero.out) hp_dvd_Mq)
      hp.pos).ne'⟩
  have hq_dvd_Mq_div_p : q.val ∣ ((l' * N) * l' ^ 2) / q.val / p :=
    prime_in_factors_q_dvd_div_q_div_p hp hpN q.val q.property
      (h_q_dvd_Ll2_aux q.val q.property)
  have h_lN_div_p_dvd_Mq_div_p : (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q.val / p :=
    prime_in_factors_lN_div_p_dvd_div_q_div_p hp hpN q.val q.property
  let χ_F_low_q : (ZMod (((l' * N) * l' ^ 2) / q.val / p))ˣ →* ℂˣ :=
    χ_M_unit_low.comp (ZMod.unitsMap h_lN_div_p_dvd_Mq_div_p)
  have h_χ_F_factor : χ_F_fam q.val q.property =
      χ_F_low_q.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_Mq)) :=
    χ_F_factor_via_χ_M_unit_low (p := p) hpN q.val
      (h_q_dvd_Ll2_aux q.val q.property) hp_dvd_Mq h_lN_div_p_dvd_Mq_div_p
      χ_M_unit χ_M_unit_low hχ_M_unit_eq (χ_F_fam q.val q.property)
      (hχ_F_fam_rel q.val q.property)
  have hq_not_m : ¬ q.val ∣ m := fun hqm =>
    hq_prime.one_lt.ne' (Nat.dvd_one.mp (hm_cop ▸ Nat.dvd_gcd hqm hq_dvd_l'))
  have h_q_M_q_eq : q.val * (((l' * N) * l' ^ 2) / q.val) = (l' * N) * l' ^ 2 :=
    Nat.mul_div_cancel' (h_q_dvd_Ll2_aux q.val q.property)
  haveI : NeZero (q.val * (((l' * N) * l' ^ 2) / q.val)) := by
    rw [h_q_M_q_eq]; infer_instance
  rw [show (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p ((l' * N) * l' ^ 2)),
          ((⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
            (F_q_fam q.val q.property).toModularForm') : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p ((l' * N) * l' ^ 2) hp v) z) =
      (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p (q.val * (((l' * N) * l' ^ 2) / q.val))),
          ((⇑(HeckeRing.GL2.modularFormLevelRaise (((l' * N) * l' ^ 2) / q.val) q.val k
              (F_q_fam q.val q.property).toModularForm') :
            UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p (q.val * (((l' * N) * l' ^ 2) / q.val)) hp v) z) from
    slash_sum_descendCoset_level_recast p hp h_q_M_q_eq.symm _]
  exact per_q_slash_sum_at_deep_qexp_zero
    (M_q := ((l' * N) * l' ^ 2) / q.val) (k := k) p hp hp_dvd_Mq q.val hpq_cop
    hq_dvd_Mq_div_p (χ_F_fam q.val q.property) χ_F_low_q h_χ_F_factor
    (F_q_fam q.val q.property) (hF_q_char q.val q.property) m hq_not_m

private lemma miyake_4_6_14_delta_slash_sum_coeff_zero
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N)
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hp_not_in : p ∉ l'.primeFactors)
    [hl'_NeZero : NeZero l']
    [NeZero (l' * N)]
    [NeZero (l' * N / p)]
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ)
    (hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd
        (dvd_mul_of_dvd_right hpN l'))))
    (Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit)
    (hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (ModularFormClass.qExpansion (1 : ℝ)
      (fun z => ∑ v : Fin (descendCosetCount p (l' * N)),
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p (l' * N) hp v) z)).coeff m = 0 := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have h_apm_zero : (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ_form).coeff (p * m) = 0 :=
    hΔ_form_vanish (p * m) (Nat.coprime_mul_iff_left.mpr ⟨hpl', hm_cop⟩)
  obtain ⟨g_q_fam, F_q_fam, χ_F_fam, hg_q_char, hF_q_char, hF_eq_g,
      hχ_F_fam_rel, hg_q_qexp⟩ :=
    miyake_4_6_7_squarefree_decomp_with_lower_level χ_M_unit Δ_form hΔ_form_χ l'
      hl1_gt hl'_sqfree hΔ_form_vanish
  haveI hLl2_NeZero : NeZero ((l' * N) * l' ^ 2) :=
    ⟨Nat.mul_ne_zero (NeZero.ne (l' * N)) (pow_ne_zero 2 (NeZero.ne l'))⟩
  have hL_dvd : (l' * N) ∣ (l' * N) * l' ^ 2 := Nat.dvd_mul_right _ _
  have h_q_dvd_Ll2_aux : ∀ q ∈ l'.primeFactors, q ∣ (l' * N) * l' ^ 2 := fun q hq =>
    dvd_mul_of_dvd_right ((Nat.dvd_of_mem_primeFactors hq).trans
      (dvd_pow_self l' two_ne_zero)) _
  have h_q_NeZero_aux : ∀ q ∈ l'.primeFactors, NeZero ((l' * N * l' ^ 2) / q) := fun q hq =>
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hLl2_NeZero.out) (h_q_dvd_Ll2_aux q hq))
      (Nat.prime_of_mem_primeFactors hq).pos).ne'⟩
  have h_qexp_eq : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) Δ_form).coeff n =
      ∑ q ∈ l'.primeFactors,
        if q ∣ n then (ModularFormClass.qExpansion (1 : ℝ) (g_q_fam q)).coeff (n / q)
        else 0 := hg_q_qexp
  have h_Δ_fun_eq :=
    function_identity_Δ_eq_sum_V_q_F (L := l' * N) (k := k) Δ_form l' g_q_fam
      hL_dvd h_q_NeZero_aux h_q_dvd_Ll2_aux F_q_fam hF_eq_g h_qexp_eq
  by_cases hp_sq : p ^ 2 ∣ l' * N
  · exact delta_slash_sum_coeff_zero_sq_case p hp hp_dvd_lN hp_sq Δ_form m h_apm_zero
  ·
    have h_M6_1_pt := miyake_4_6_6_level_commute (N := l' * N) (l := l' ^ 2) (k := k)
      p hp hp_dvd_lN (hpl'.pow_right 2) χ_M_unit Δ_form.toModularForm'
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        (k := k) χ_M_unit Δ_form).mpr hΔ_form_χ)
    have hLevel_eq : l' ^ 2 * (l' * N) = l' * N * l' ^ 2 := by ring
    have h_combined_fun : (⇑Δ_form.toModularForm' : UpperHalfPlane → ℂ) =
        fun z ↦ ∑ q ∈ l'.primeFactors.attach,
          (haveI : NeZero ((l' * N * l' ^ 2) / q.val) :=
            h_q_NeZero_aux q.val q.property
           haveI : NeZero q.val :=
            ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
           (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
             (F_q_fam q.val q.property).toModularForm') :
             UpperHalfPlane → ℂ) z) := h_Δ_fun_eq
    rw [show (fun z : UpperHalfPlane ↦
        ∑ v : Fin (descendCosetCount p (l' * N)),
          ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
            descendCosetList p (l' * N) hp v) z) =
        (fun z : UpperHalfPlane ↦
          ∑ v : Fin (descendCosetCount p (l' ^ 2 * (l' * N))),
            ((⇑Δ_form.toModularForm' : UpperHalfPlane → ℂ) ∣[k]
              descendCosetList p (l' ^ 2 * (l' * N)) hp v) z) from funext h_M6_1_pt,
      slash_sum_descendCoset_level_recast p hp hLevel_eq (⇑Δ_form.toModularForm'),
      slash_sum_at_M_eq_of_function_eq p ((l' * N) * l' ^ 2) hp k _ _ h_combined_fun,
      slash_sum_linear_over_Finset_sum p ((l' * N) * l' ^ 2) hp k
        l'.primeFactors.attach (fun q ↦ fun z ↦
          (haveI : NeZero ((l' * N * l' ^ 2) / q.val) :=
            h_q_NeZero_aux q.val q.property
           haveI : NeZero q.val :=
            ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
           (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
             (F_q_fam q.val q.property).toModularForm') :
             UpperHalfPlane → ℂ) z))]
    set inner_fun : (q : l'.primeFactors) → UpperHalfPlane → ℂ := fun q ↦
      fun z ↦
        ∑ v : Fin (descendCosetCount p ((l' * N) * l' ^ 2)),
          (haveI : NeZero ((l' * N * l' ^ 2) / q.val) := h_q_NeZero_aux q.val q.property
           haveI : NeZero q.val :=
            ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
           (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N * l' ^ 2) / q.val) q.val k
             (F_q_fam q.val q.property).toModularForm') : UpperHalfPlane → ℂ) ∣[k]
              descendCosetList p ((l' * N) * l' ^ 2) hp v) z
    show (ModularFormClass.qExpansion (1 : ℝ)
        (fun z : UpperHalfPlane ↦ ∑ q ∈ l'.primeFactors.attach, inner_fun q z)).coeff m = 0
    have h_per_q_zero : ∀ q : l'.primeFactors,
        (ModularFormClass.qExpansion (1 : ℝ) (inner_fun q)).coeff m = 0 := fun q =>
      delta_slash_sum_per_q_inner_fun_coeff_zero p hp hpN hp_not_in
        h_q_NeZero_aux h_q_dvd_Ll2_aux χ_M_unit χ_M_unit_low hχ_M_unit_eq
        F_q_fam χ_F_fam hF_q_char hχ_F_fam_rel q m hm_cop
    have h_q_M_q_eq : ∀ q : l'.primeFactors,
        q.val * (((l' * N) * l' ^ 2) / q.val) = (l' * N) * l' ^ 2 := fun q ↦
      Nat.mul_div_cancel' (h_q_dvd_Ll2_aux q.val q.property)
    haveI hq_NeZero_inst : ∀ q : l'.primeFactors, NeZero q.val := fun q ↦
      ⟨(Nat.prime_of_mem_primeFactors q.property).ne_zero⟩
    haveI hM_q_NeZero_inst : ∀ q : l'.primeFactors, NeZero ((l' * N * l' ^ 2) / q.val) :=
      fun q ↦ h_q_NeZero_aux q.val q.property
    have hp_dvd_Mq_inst : ∀ q : l'.primeFactors, p ∣ ((l' * N) * l' ^ 2) / q.val := fun q ↦
      prime_in_factors_p_dvd_div_q hp hpN hp_not_in q.val q.property
        (h_q_dvd_Ll2_aux q.val q.property)
    have h_lN_div_p_dvd_Mq_div_p_inst : ∀ q : l'.primeFactors,
        (l' * N) / p ∣ ((l' * N) * l' ^ 2) / q.val / p := fun q ↦
      prime_in_factors_lN_div_p_dvd_div_q_div_p hp hpN q.val q.property
    let χ_F_low_q : (q : l'.primeFactors) →
        (ZMod (((l' * N) * l' ^ 2) / q.val / p))ˣ →* ℂˣ := fun q ↦
      χ_M_unit_low.comp (ZMod.unitsMap (h_lN_div_p_dvd_Mq_div_p_inst q))
    have h_Mq_div_p_eq : ∀ q : l'.primeFactors,
        (q.val * (((l' * N) * l' ^ 2) / q.val)) / p = ((l' * N) * l' ^ 2) / p := fun q ↦ by
      rw [h_q_M_q_eq q]
    haveI hMfull_div_p_NeZero : NeZero (((l' * N) * l' ^ 2) / p) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hLl2_NeZero.out)
        (dvd_mul_of_dvd_left hp_dvd_lN _)) hp.pos).ne'⟩
    haveI hMq_div_p_NeZero_inst : ∀ q : l'.primeFactors,
        NeZero (((l' * N) * l' ^ 2) / q.val / p) := fun q ↦
      ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (hM_q_NeZero_inst q).out)
        (hp_dvd_Mq_inst q)) hp.pos).ne'⟩
    have h_per_q_factor : ∀ q : l'.primeFactors,
        (χ_F_fam q.val q.property) = (χ_F_low_q q).comp
          (ZMod.unitsMap (Nat.div_dvd_of_dvd (hp_dvd_Mq_inst q))) := fun q ↦
      χ_F_factor_via_χ_M_unit_low (p := p) hpN q.val
        (h_q_dvd_Ll2_aux q.val q.property) (hp_dvd_Mq_inst q)
        (h_lN_div_p_dvd_Mq_div_p_inst q) χ_M_unit χ_M_unit_low hχ_M_unit_eq
        (χ_F_fam q.val q.property) (hχ_F_fam_rel q.val q.property)
    let Φ_pre : (q : l'.primeFactors) →
        CuspForm ((Gamma1 ((q.val * (((l' * N) * l' ^ 2) / q.val)) / p)).map (mapGL ℝ)) k :=
      fun q ↦
      haveI := hq_NeZero_inst q
      haveI := hM_q_NeZero_inst q
      slash_sum_V_q_cuspForm_descend p hp (hp_dvd_Mq_inst q) q.val
        (χ_F_fam q.val q.property) (χ_F_low_q q) (h_per_q_factor q)
        (F_q_fam q.val q.property) (hF_q_char q.val q.property)
    let Φ_q : (q : l'.primeFactors) →
        CuspForm ((Gamma1 (((l' * N) * l' ^ 2) / p)).map (mapGL ℝ)) k := fun q ↦
      haveI := hq_NeZero_inst q
      haveI := hM_q_NeZero_inst q
      haveI := hMq_div_p_NeZero_inst q
      h_Mq_div_p_eq q ▸ Φ_pre q
    have hΦ_q_fun : ∀ q : l'.primeFactors, ∀ z : UpperHalfPlane,
        (⇑(Φ_q q) : UpperHalfPlane → ℂ) z = inner_fun q z := by
      intro q z
      haveI := hq_NeZero_inst q
      haveI := hM_q_NeZero_inst q
      haveI : NeZero (q.val * (((l' * N) * l' ^ 2) / q.val) / p) := by
        rw [h_Mq_div_p_eq q]; exact hMfull_div_p_NeZero
      haveI : NeZero (q.val * (((l' * N) * l' ^ 2) / q.val)) := by
        rw [h_q_M_q_eq q]; infer_instance
      rw [show (⇑(Φ_q q) : UpperHalfPlane → ℂ) z =
        (⇑(h_Mq_div_p_eq q ▸ Φ_pre q :
          CuspForm ((Gamma1 (((l' * N) * l' ^ 2) / p)).map (mapGL ℝ)) k) :
            UpperHalfPlane → ℂ) z from rfl,
        cuspForm_level_recast_coe_apply (h_Mq_div_p_eq q) (Φ_pre q) z]
      exact congr_fun
        (slash_sum_descendCoset_level_recast p hp (h_q_M_q_eq q)
          (⇑(HeckeRing.GL2.modularFormLevelRaise (((l' * N) * l' ^ 2) / q.val) q.val k
            (F_q_fam q.val q.property).toModularForm') : UpperHalfPlane → ℂ)) z
    let Φ_total : CuspForm ((Gamma1 (((l' * N) * l' ^ 2) / p)).map (mapGL ℝ)) k :=
      ∑ q ∈ l'.primeFactors.attach, Φ_q q
    have hΦ_total_fun : (⇑Φ_total : UpperHalfPlane → ℂ) =
        fun z : UpperHalfPlane ↦ ∑ q ∈ l'.primeFactors.attach, inner_fun q z := by
      funext z
      rw [show (⇑Φ_total : UpperHalfPlane → ℂ) z =
        (⇑(∑ q ∈ l'.primeFactors.attach, Φ_q q) : UpperHalfPlane → ℂ) z from rfl,
        cuspForm_finsetSum_coe_apply l'.primeFactors.attach Φ_q z]
      exact Finset.sum_congr rfl (fun q _ => hΦ_q_fun q z)
    have h1_period_full_div_p :
        (1 : ℝ) ∈ ((Gamma1 (((l' * N) * l' ^ 2) / p)).map (mapGL ℝ)).strictPeriods := by
      simp [strictPeriods_Gamma1]
    have h_qexp_sum : ModularFormClass.qExpansion (1 : ℝ)
        (fun z : UpperHalfPlane => ∑ q ∈ l'.primeFactors.attach, inner_fun q z) =
        ∑ q ∈ l'.primeFactors.attach,
          ModularFormClass.qExpansion (1 : ℝ) (Φ_q q).toModularForm' := by
      rw [show (fun z : UpperHalfPlane => ∑ q ∈ l'.primeFactors.attach, inner_fun q z) =
          (⇑Φ_total.toModularForm' : UpperHalfPlane → ℂ) from hΦ_total_fun.symm,
        show Φ_total.toModularForm' =
          ∑ q ∈ l'.primeFactors.attach, (Φ_q q).toModularForm' from
            cuspForm_finsetSum_toModularForm' l'.primeFactors.attach Φ_q]
      exact map_sum (qExpansionAddHom (Γ := (Gamma1 (((l' * N) * l' ^ 2) / p)).map (mapGL ℝ))
        (h := (1 : ℝ)) one_pos h1_period_full_div_p k) (fun q => (Φ_q q).toModularForm')
        l'.primeFactors.attach
    rw [h_qexp_sum, map_sum]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [show (ModularFormClass.qExpansion (1 : ℝ) (Φ_q q).toModularForm').coeff m =
        (ModularFormClass.qExpansion (1 : ℝ) (inner_fun q)).coeff m from
      congrArg (fun ps : PowerSeries ℂ => ps.coeff m)
        (qExpansion_ext2 (⇑(Φ_q q) : UpperHalfPlane → ℂ) (inner_fun q)
          (funext (hΦ_q_fun q)))]
    exact h_per_q_zero q

private lemma one_mem_strictPeriods_Gamma1_map (M : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 M).map (mapGL ℝ)).strictPeriods := by
  rw [show (Gamma1 M).map (mapGL ℝ) = (Gamma1 M : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

private noncomputable def descendSlashSumCuspForm
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ) :
    CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k where
  toFun := fun z ↦ ∑ v : Fin (descendCosetCount p N),
    (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z
  slash_action_eq' γ hγ := by
    obtain ⟨γ', h_γ'_Gamma1, rfl⟩ := Subgroup.mem_map.mp hγ
    exact miyake_hecke_descend_Gamma1_inv p hp hpN χ χ' hχ_eq hfχ_mod γ' h_γ'_Gamma1
  holo' := by
    show MDifferentiable _ _ (fun z : UpperHalfPlane ↦
      ∑ v : Fin (descendCosetCount p N),
        (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z)
    rw [show (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z) =
        ∑ v : Fin (descendCosetCount p N),
          (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) from
      funext fun z ↦ (Finset.sum_apply _ _ _).symm]
    exact MDifferentiable.sum fun v _ ↦
      (ModularFormClass.holo f.toModularForm').slash k _
  zero_at_cusps' {cusp} hc := miyake_hecke_descend_cusp p hp hpN f hc

private lemma descendSlashSumCuspForm_mem_charSpace
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ) :
    descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod ∈ cuspFormCharSpace k χ' :=
  (cuspFormCharSpace_iff_nebentypus k χ' _).mpr fun γ ↦
    miyake_hecke_descend_char p hp hpN χ χ' hχ_eq hfχ_mod ⟨γ.val, γ.property⟩

private lemma slash_sum_V_p_pointwise_eq_smul_g_low
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (g_low : ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    (∑ v : Fin (descendCosetCount p N),
        (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k g_low) ∣[k]
          descendCosetList p N hp v) z) =
      (descendCosetCount p N : ℂ) / (p : ℂ) * g_low z := by
  simp_rw [fun v ↦ multipass_V_p_slash_descendCoset p hp hpN g_low v z]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private lemma slash_sum_V_p_qExp_coeff_eq
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (g_low_cast : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
          (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k
            g_low_cast.toModularForm') ∣[k] descendCosetList p N hp v) z)).coeff m =
      (descendCosetCount p N : ℂ) / (p : ℂ) *
        (ModularFormClass.qExpansion (1 : ℝ)
          (⇑g_low_cast.toModularForm' : UpperHalfPlane → ℂ)).coeff m := by
  set D : ℂ := (descendCosetCount p N : ℂ) / (p : ℂ)
  set f : UpperHalfPlane → ℂ := fun z ↦ ∑ v : Fin (descendCosetCount p N),
    (⇑(HeckeRing.GL2.modularFormLevelRaise (N / p) p k
      g_low_cast.toModularForm') ∣[k] descendCosetList p N hp v) z
  have h_pt : f = ⇑(D • g_low_cast.toModularForm') :=
    funext fun z ↦ slash_sum_V_p_pointwise_eq_smul_g_low p hp hpN
      g_low_cast.toModularForm' z
  have h_qexp : ModularFormClass.qExpansion (1 : ℝ) f =
      ModularFormClass.qExpansion (1 : ℝ) (D • g_low_cast.toModularForm') :=
    qExpansion_ext2 (f : UpperHalfPlane → ℂ) (D • g_low_cast.toModularForm') h_pt
  rw [h_qexp,
    qExpansion_smul (F := ModularForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
      one_pos (one_mem_strictPeriods_Gamma1_map (N / p)) D g_low_cast.toModularForm',
    PowerSeries.coeff_smul, smul_eq_mul]

private lemma slash_sum_Δ_form_qExp_coeff_zero
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l') (hp_not_in : p ∉ l'.primeFactors)
    [NeZero l'] [NeZero (l' * N)] [NeZero (l' * N / p)]
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (hχ_M_unit_eq_chi : χ_M_unit = χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l')))
    (Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit)
    (hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (ModularFormClass.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k]
          descendCosetList p (l' * N) hp v) z)).coeff m = 0 := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have hNp_dvd_l'Np : N / p ∣ l' * N / p := by
    rw [Nat.mul_div_assoc l' hpN]; exact Nat.dvd_mul_left (N / p) l'
  let χ_lifted_low : (ZMod (l' * N / p))ˣ →* ℂˣ :=
    χ'.comp (ZMod.unitsMap hNp_dvd_l'Np)
  have hχ_M_unit_eq : χ_M_unit =
      χ_lifted_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_lN)) := by
    rw [hχ_M_unit_eq_chi, hχ_eq]
    show (χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN))).comp
        (ZMod.unitsMap (Nat.dvd_mul_left N l')) =
        (χ'.comp (ZMod.unitsMap hNp_dvd_l'Np)).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_lN))
    rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc,
      ZMod.unitsMap_comp, ZMod.unitsMap_comp]
  exact miyake_4_6_14_delta_slash_sum_coeff_zero p hp hpN hl1_gt hl'_sqfree hpl'
    hp_not_in χ_M_unit χ_lifted_low hχ_M_unit_eq Δ_form hΔ_form_χ
    hΔ_form_vanish m hm_cop

private lemma slash_sum_qExp_split_via_cuspForm
    {N : ℕ} [NeZero N] {k : ℤ}
    (p : ℕ) [NeZero p] (hp : p.Prime) [NeZero (N / p)]
    (Φ_RHS Φ_Δ : CuspForm ((Gamma1 (N / p)).map (mapGL ℝ)) k)
    (V_p_g_low_fun Δ_form_slash : UpperHalfPlane → ℂ)
    (hΦ_RHS_eq : (⇑Φ_RHS : UpperHalfPlane → ℂ) =
      fun z ↦ ∑ v : Fin (descendCosetCount p N),
        (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z)
    (hΦ_Δ_eq : (⇑Φ_Δ : UpperHalfPlane → ℂ) = Δ_form_slash) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ)
        ((fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
          (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z) + Δ_form_slash)).coeff m =
      (ModularFormClass.qExpansion (1 : ℝ)
          (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p N),
            (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z)).coeff m +
        (ModularFormClass.qExpansion (1 : ℝ) Δ_form_slash).coeff m := by
  set lhs_fn : UpperHalfPlane → ℂ := fun z : UpperHalfPlane ↦
    ∑ v : Fin (descendCosetCount p N), (V_p_g_low_fun ∣[k] descendCosetList p N hp v) z
  have h_sum_eq_fn : (lhs_fn + Δ_form_slash : UpperHalfPlane → ℂ) =
      (⇑(Φ_RHS.toModularForm' + Φ_Δ.toModularForm') : UpperHalfPlane → ℂ) := by
    funext z
    show lhs_fn z + Δ_form_slash z =
      (⇑Φ_RHS.toModularForm' : UpperHalfPlane → ℂ) z +
        (⇑Φ_Δ.toModularForm' : UpperHalfPlane → ℂ) z
    show lhs_fn z + Δ_form_slash z = (⇑Φ_RHS : UpperHalfPlane → ℂ) z + (⇑Φ_Δ) z
    rw [hΦ_RHS_eq, hΦ_Δ_eq]
  have h_bridge : ModularFormClass.qExpansion (1 : ℝ)
        ((lhs_fn + Δ_form_slash) : UpperHalfPlane → ℂ) =
      ModularFormClass.qExpansion (1 : ℝ)
        (Φ_RHS.toModularForm' + Φ_Δ.toModularForm') :=
    qExpansion_ext2 ((lhs_fn + Δ_form_slash) : UpperHalfPlane → ℂ)
      (Φ_RHS.toModularForm' + Φ_Δ.toModularForm') h_sum_eq_fn
  rw [h_bridge,
    qExpansion_add (Γ := (Gamma1 (N / p)).map (mapGL ℝ)) (h := (1 : ℝ))
      (a := k) (b := k) one_pos (one_mem_strictPeriods_Gamma1_map (N / p))
      Φ_RHS.toModularForm' Φ_Δ.toModularForm', map_add,
    qExpansion_ext2 Φ_RHS.toModularForm' (lhs_fn : UpperHalfPlane → ℂ) hΦ_RHS_eq,
    qExpansion_ext2 Φ_Δ.toModularForm' (Δ_form_slash : UpperHalfPlane → ℂ) hΦ_Δ_eq]
  rfl

private lemma miyake_descent_l_prime_gt_one_helper
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    [hl'_NeZero : NeZero l']
    [NeZero (l' * N)]
    [NeZero (l' * N / p)]
    (g_low_cast : CuspForm ((Gamma1 (l' * N / p)).map (mapGL ℝ)) k)
    (h_delta_Fourier_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑f).coeff n =
      (ModularFormClass.qExpansion (1 : ℝ)
        ⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm')).coeff n)
    (χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ)
    (hχ_M_unit_eq_chi : χ_M_unit = χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l')))
    (Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit)
    (hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0)
    (hΔ_form_fun_eq : (⇑Δ_form : UpperHalfPlane → ℂ) =
      fun z ↦ ⇑f.toModularForm' z -
        ⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') z)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (PowerSeries.coeff m) (ModularFormClass.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)) =
    (PowerSeries.coeff m) (ModularFormClass.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z)) := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  set V_p_g_low_fun : UpperHalfPlane → ℂ :=
    ⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
      g_low_cast.toModularForm')
  set D_lifted : ℂ := (descendCosetCount p (l' * N) : ℂ) / (p : ℂ)
  set Δ_form_slash : UpperHalfPlane → ℂ :=
    fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
      ((⇑Δ_form : UpperHalfPlane → ℂ) ∣[k] descendCosetList p (l' * N) hp v) z
  have hNp_dvd_l'Np : N / p ∣ l' * N / p := by
    rw [Nat.mul_div_assoc l' hpN]; exact Nat.dvd_mul_left (N / p) l'
  let χ_M_unit_low : (ZMod (l' * N / p))ˣ →* ℂˣ :=
    χ'.comp (ZMod.unitsMap hNp_dvd_l'Np)
  have hχ_M_unit_eq : χ_M_unit =
      χ_M_unit_low.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hp_dvd_lN)) := by
    rw [hχ_M_unit_eq_chi, hχ_eq, MonoidHom.comp_assoc, MonoidHom.comp_assoc,
      ZMod.unitsMap_comp, ZMod.unitsMap_comp]
  let Φ_RHS_cusp : CuspForm ((Gamma1 (l' * N / p)).map (mapGL ℝ)) k :=
    D_lifted • g_low_cast
  let Φ_Δ : CuspForm ((Gamma1 (l' * N / p)).map (mapGL ℝ)) k :=
    descendSlashSumCuspForm χ_M_unit Δ_form p hp hp_dvd_lN χ_M_unit_low
      hχ_M_unit_eq
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace
        (k := k) χ_M_unit Δ_form).mpr hΔ_form_χ)
  have hΦ_RHS_cusp_fun_eq : (⇑Φ_RHS_cusp : UpperHalfPlane → ℂ) =
      fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (V_p_g_low_fun ∣[k] descendCosetList p (l' * N) hp v) z :=
    funext fun z ↦
      (slash_sum_V_p_pointwise_eq_smul_g_low p hp hp_dvd_lN
        g_low_cast.toModularForm' z).symm
  have h_f_eq : (⇑f.toModularForm' : UpperHalfPlane → ℂ) =
      V_p_g_low_fun + (⇑Δ_form : UpperHalfPlane → ℂ) := by
    funext w
    have hΔw : (⇑Δ_form : UpperHalfPlane → ℂ) w =
        (⇑f.toModularForm' : UpperHalfPlane → ℂ) w - V_p_g_low_fun w :=
      congr_fun hΔ_form_fun_eq w
    simp [Pi.add_apply, hΔw]
  have h_LHS_fun_eq : (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
      (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z) =
      ((fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (V_p_g_low_fun ∣[k] descendCosetList p (l' * N) hp v) z) +
        Δ_form_slash : UpperHalfPlane → ℂ) := by
    simp_rw [h_f_eq]
    funext z
    simp only [SlashAction.add_slash, Finset.sum_add_distrib, Pi.add_apply]
    rfl
  rw [h_LHS_fun_eq,
    slash_sum_qExp_split_via_cuspForm p hp Φ_RHS_cusp Φ_Δ V_p_g_low_fun
      Δ_form_slash hΦ_RHS_cusp_fun_eq rfl m,
    slash_sum_V_p_qExp_coeff_eq p hp hp_dvd_lN g_low_cast m,
    slash_sum_Δ_form_qExp_coeff_zero χ p hp hpN χ' hχ_eq hl1_gt hl'_sqfree hpl'
      hp_not_in χ_M_unit hχ_M_unit_eq_chi Δ_form hΔ_form_χ hΔ_form_vanish m hm_cop,
    add_zero]

private lemma cuspForm_cast_coe {A B : ℕ} {k : ℤ} (h : A = B)
    (x : CuspForm ((Gamma1 A).map (mapGL ℝ)) k) :
    (⇑(h ▸ x : CuspForm ((Gamma1 B).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) = ⇑x := by
  cases h; rfl

private lemma modularForm_cast_coe {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ} (h : A = B)
    (x : ModularForm ((Gamma1 A).map (mapGL ℝ)) k) :
    (⇑(h ▸ x : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) :
      UpperHalfPlane → ℂ) = ⇑x := by
  cases h; rfl

private lemma descendCosetCount_mul_left_of_coprime
    {p l N : ℕ} (hpl : Nat.Coprime p l) :
    descendCosetCount p (l * N) = descendCosetCount p N := by
  unfold descendCosetCount
  have h_iff : p ^ 2 ∣ l * N ↔ p ^ 2 ∣ N :=
    ⟨fun h_sq ↦ (hpl.pow_left 2).dvd_of_dvd_mul_left h_sq, fun h ↦ h.mul_left l⟩
  split_ifs <;> tauto

private lemma qExpansion_smul_cuspForm_coeff_aux
    {M : ℕ} [NeZero M] {k : ℤ} (c : ℂ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (m : ℕ) :
    (ModularFormClass.qExpansion (1 : ℝ) (c • f)).coeff m =
      c * (ModularFormClass.qExpansion (1 : ℝ) f).coeff m := by
  show (ModularFormClass.qExpansion (1 : ℝ) (c • (⇑f : UpperHalfPlane → ℂ))).coeff m =
    c * (ModularFormClass.qExpansion (1 : ℝ) (⇑f : UpperHalfPlane → ℂ)).coeff m
  rw [show ModularFormClass.qExpansion (1 : ℝ) (c • (⇑f : UpperHalfPlane → ℂ)) =
        ModularFormClass.qExpansion (1 : ℝ) (c • f.toModularForm') from rfl,
    qExpansion_smul (F := ModularForm ((Gamma1 M).map (mapGL ℝ)) k) one_pos
      (one_mem_strictPeriods_Gamma1_map M) c f.toModularForm',
    PowerSeries.coeff_smul, smul_eq_mul]
  rfl

private lemma f_qExp_eq_levelRaise_qExp_at_coprime
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    {l' : ℕ}
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    {Mp : ℕ} [NeZero Mp]
    (g_low_cast : CuspForm ((Gamma1 Mp).map (mapGL ℝ)) k)
    {L : ℕ} [NeZero L]
    (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_qexp : ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff (n / p)) :
    ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑f).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ)
          ⇑(HeckeRing.GL2.modularFormLevelRaise Mp p k
            g_low_cast.toModularForm')).coeff n := by
  intro n hn_cop
  have h_Vp : (ModularFormClass.qExpansion (1 : ℝ)
      ⇑(HeckeRing.GL2.modularFormLevelRaise Mp p k g_low_cast.toModularForm')).coeff n =
      if p ∣ n then
        (ModularFormClass.qExpansion (1 : ℝ) g_low_cast.toModularForm').coeff (n / p)
      else 0 :=
    HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff _ n
  rw [h_Vp]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn, hg_low_qexp n hpn hn_cop,
      show ModularFormClass.qExpansion (1 : ℝ) g_low_cast.toModularForm' =
        ModularFormClass.qExpansion (1 : ℝ) (⇑g_low : UpperHalfPlane → ℂ) from
        h_cast_fun ▸ rfl]
  · rw [if_neg hpn]
    exact h_vanish n
      (Nat.Coprime.mul_right ((hp.coprime_iff_not_dvd).mpr hpn).symm hn_cop)

private lemma g_bundled_qExp_eq_levelRaise_qExp
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {p : ℕ} [NeZero p] (hp : p.Prime)
    {l' : ℕ} [NeZero l'] (hpl' : Nat.Coprime p l')
    [NeZero (l' * N)] [NeZero ((l' * N) / p)]
    (g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k)
    {L : ℕ} [NeZero L]
    (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_full_qexp : ∀ m : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    (g_bundled : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k)
    (hg_bundled_qexp : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) g_bundled).coeff n =
        if Nat.Coprime n l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff n
        else 0)
    (hpM_eq : p * ((l' * N) / p) = l' * N) :
    (⇑g_bundled : UpperHalfPlane → ℂ) =
      ⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
        g_low_cast.toModularForm') := by
  haveI hpMp_NeZero : NeZero (p * ((l' * N) / p)) := by rw [hpM_eq]; infer_instance
  have h_qExp_eq : ∀ n : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) ⇑g_bundled).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ)
          ⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
            g_low_cast.toModularForm')).coeff n := by
    intro n
    rw [hg_bundled_qexp n,
      HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff _ n]
    have h_qe_g_low_cast :
        ModularFormClass.qExpansion (1 : ℝ) g_low_cast.toModularForm' =
          ModularFormClass.qExpansion (1 : ℝ) (⇑g_low : UpperHalfPlane → ℂ) :=
      h_cast_fun ▸ rfl
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, h_qe_g_low_cast, hg_low_full_qexp (n / p)]
      have h_cop_iff : Nat.Coprime n l' ↔ Nat.Coprime (n / p) l' := by
        rcases hpn with ⟨q_idx, hq_idx_eq⟩
        rw [hq_idx_eq, Nat.mul_div_cancel_left _ hp.pos, Nat.coprime_mul_iff_left]
        exact ⟨fun h ↦ h.2, fun h ↦ ⟨hpl', h⟩⟩
      by_cases hcop : Nat.Coprime n l'
      · rw [if_pos hcop, if_pos (h_cop_iff.mp hcop),
          show p * (n / p) = n from Nat.mul_div_cancel' hpn]
      · rw [if_neg hcop, if_neg (mt h_cop_iff.mpr hcop)]
    · rw [if_neg hpn]
      by_cases hcop : Nat.Coprime n l'
      · rw [if_pos hcop]
        exact h_vanish n (Nat.Coprime.mul_right
          ((hp.coprime_iff_not_dvd).mpr hpn).symm hcop)
      · rw [if_neg hcop]
  let Vp_form : ModularForm ((Gamma1 (p * ((l' * N) / p))).map (mapGL ℝ)) k :=
    HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k g_low_cast.toModularForm'
  let Vp_form_cast : ModularForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k :=
    hpM_eq ▸ Vp_form
  have h_Vp_form_cast_fun : (⇑Vp_form_cast : UpperHalfPlane → ℂ) = ⇑Vp_form :=
    modularForm_cast_coe hpM_eq Vp_form
  have h_eq := modularForm_fun_eq_of_qExp_eq_at_period_one (M := l' * N) (k := k)
    (one_mem_strictPeriods_Gamma1_map (l' * N))
    g_bundled.toModularForm' Vp_form_cast (by
      intro n
      have h_V : ModularFormClass.qExpansion (1 : ℝ) Vp_form_cast =
          ModularFormClass.qExpansion (1 : ℝ) Vp_form := by
        show ModularFormClass.qExpansion (1 : ℝ) (⇑Vp_form_cast : UpperHalfPlane → ℂ) =
          ModularFormClass.qExpansion (1 : ℝ) (⇑Vp_form : UpperHalfPlane → ℂ)
        rw [h_Vp_form_cast_fun]
      rw [h_V]
      exact h_qExp_eq n)
  rw [show (⇑g_bundled : UpperHalfPlane → ℂ) =
        (⇑g_bundled.toModularForm' : UpperHalfPlane → ℂ) from rfl, h_eq,
    h_Vp_form_cast_fun]

private lemma descent_l_prime_gt_one_apply
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl1_gt : 1 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    [NeZero l'] [NeZero (l' * N)] [NeZero ((l' * N) / p)]
    {L : ℕ} [NeZero L] (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_full_qexp : ∀ m : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (h_delta_Fourier_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑f).coeff n =
      (ModularFormClass.qExpansion (1 : ℝ)
        ⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
          g_low_cast.toModularForm')).coeff n)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (PowerSeries.coeff m) (ModularFormClass.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)) =
    (PowerSeries.coeff m) (ModularFormClass.qExpansion (1 : ℝ)
      (fun z ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z)) := by
  have hl'_pos : 0 < l' := lt_trans Nat.zero_lt_one hl1_gt
  let χ_M_unit : (ZMod (l' * N))ˣ →* ℂˣ :=
    χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N l'))
  obtain ⟨g_bundled, hg_bundled_χ, _hg_bundled_supp, hg_bundled_qexp⟩ :=
    miyake_g_p_supported χ f hfχ p hp l' hl'_pos hl'_sqfree hl'_dvd h_vanish
  have hN_dvd_lN : N ∣ l' * N := Nat.dvd_mul_left N l'
  let f_restricted : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k :=
    CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hN_dvd_lN) f
  have hf_restricted_χ : f_restricted ∈ cuspFormCharSpace k χ_M_unit :=
    cuspForm_restrictSubgroup_mem_cuspFormCharSpace χ hN_dvd_lN hfχ
  let Δ_form : CuspForm ((Gamma1 (l' * N)).map (mapGL ℝ)) k :=
    f_restricted - g_bundled
  have hΔ_form_χ : Δ_form ∈ cuspFormCharSpace k χ_M_unit :=
    Submodule.sub_mem _ hf_restricted_χ hg_bundled_χ
  have h1_period_lN := one_mem_strictPeriods_Gamma1_map (l' * N)
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  have hpM_eq : p * ((l' * N) / p) = l' * N := Nat.mul_div_cancel' hp_dvd_lN
  have h_Δ_form_sub_qexp : ∀ n : ℕ,
      (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ_form) =
      (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f_restricted) -
      (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑g_bundled) := by
    intro n
    have h_sub_qexp :
        ModularFormClass.qExpansion (1 : ℝ) (f_restricted - g_bundled) =
          ModularFormClass.qExpansion (1 : ℝ) f_restricted -
          ModularFormClass.qExpansion (1 : ℝ) g_bundled := by
      rw [sub_eq_add_neg, sub_eq_add_neg,
        ← qExpansion_neg one_pos h1_period_lN g_bundled]
      exact qExpansion_add (Γ := (Gamma1 (l' * N)).map (mapGL ℝ))
        (h := (1 : ℝ)) (a := k) (b := k) one_pos h1_period_lN f_restricted (- g_bundled)
    show (PowerSeries.coeff n)
        (ModularFormClass.qExpansion (1 : ℝ) (⇑Δ_form)) = _
    rw [show ModularFormClass.qExpansion (1 : ℝ) (⇑Δ_form : UpperHalfPlane → ℂ) =
      ModularFormClass.qExpansion (1 : ℝ) (f_restricted - g_bundled) from rfl,
      h_sub_qexp, map_sub]
  have hΔ_form_vanish : ∀ n : ℕ, Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑Δ_form).coeff n = 0 := fun n hn ↦ by
    rw [h_Δ_form_sub_qexp n,
      show (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f_restricted) =
        (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑f) from rfl,
      hg_bundled_qexp n, if_pos hn, sub_self]
  have h_g_bundled_eq_Vp :=
    g_bundled_qExp_eq_levelRaise_qExp f hp hpl' g_low_cast g_low h_cast_fun
      hg_low_full_qexp h_vanish g_bundled hg_bundled_qexp hpM_eq
  have hΔ_form_fun_eq : (⇑Δ_form : UpperHalfPlane → ℂ) =
      fun z ↦ ⇑f.toModularForm' z -
        ⇑((HeckeRing.GL2.modularFormLevelRaise (l' * N / p) p k)
          g_low_cast.toModularForm') z := by
    funext z
    show (⇑f_restricted - ⇑g_bundled : UpperHalfPlane → ℂ) z = _
    rw [show (⇑f_restricted - ⇑g_bundled : UpperHalfPlane → ℂ) z =
      (⇑f_restricted : UpperHalfPlane → ℂ) z - (⇑g_bundled) z from rfl,
      h_g_bundled_eq_Vp]
    rfl
  exact miyake_descent_l_prime_gt_one_helper χ f hfχ p hp hpN χ' hχ_eq
    hl1_gt hl'_sqfree hpl' hl'_dvd hp_not_in h_vanish g_low_cast
    h_delta_Fourier_vanish χ_M_unit rfl Δ_form hΔ_form_χ
    hΔ_form_vanish hΔ_form_fun_eq m hm_cop

private lemma descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    {l' : ℕ} (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    [NeZero l'] [NeZero (l' * N)] [NeZero ((l' * N) / p)]
    {L : ℕ} [NeZero L] (g_low : CuspForm ((Gamma1 L).map (mapGL ℝ)) k)
    (g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k)
    (h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low)
    (hg_low_qexp : ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff (n / p))
    (hg_low_full_qexp : ∀ m : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (ModularFormClass.qExpansion (1 : ℝ)
      (fun z : UpperHalfPlane ↦ ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z)).coeff m =
      (descendCosetCount p (l' * N) : ℂ) / (p : ℂ) *
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m := by
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  set Ψ_fun : UpperHalfPlane → ℂ := fun z ↦
      ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z with hΨ_fun_def
  set Vp_slash_lifted_fun : UpperHalfPlane → ℂ := fun z ↦
    ∑ v : Fin (descendCosetCount p (l' * N)),
      (⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
        g_low_cast.toModularForm') ∣[k] descendCosetList p (l' * N) hp v) z
    with hVp_slash_lifted_fun_def
  set Dp_g_low : UpperHalfPlane → ℂ := fun z ↦
    (descendCosetCount p (l' * N) : ℂ) / (p : ℂ) * g_low z
  have h_Vp_slash_lifted : ∀ z : UpperHalfPlane, Vp_slash_lifted_fun z = Dp_g_low z := fun z ↦ by
    simp_rw [hVp_slash_lifted_fun_def, fun v ↦ multipass_V_p_slash_descendCoset p hp hp_dvd_lN
      g_low_cast.toModularForm' v z]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (g_low_cast.toModularForm' : UpperHalfPlane → ℂ) z = g_low z by
        show (⇑g_low_cast : UpperHalfPlane → ℂ) z = ⇑g_low z; rw [h_cast_fun]]
    ring
  have h_Vp_qexp_eq : ModularFormClass.qExpansion (1 : ℝ) Vp_slash_lifted_fun =
      ModularFormClass.qExpansion (1 : ℝ) Dp_g_low :=
    qExpansion_ext2 Vp_slash_lifted_fun Dp_g_low (funext h_Vp_slash_lifted)
  have h_Dp_g_low_qexp :
      (ModularFormClass.qExpansion (1 : ℝ) Dp_g_low).coeff m =
        (descendCosetCount p (l' * N) : ℂ) / (p : ℂ) *
          (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m := by
    have : Dp_g_low = ((descendCosetCount p (l' * N) : ℂ) / (p : ℂ)) •
        (⇑g_low : UpperHalfPlane → ℂ) := rfl
    rw [this]
    exact qExpansion_smul_cuspForm_coeff_aux _ g_low m
  have h_delta_Fourier_vanish :=
    f_qExp_eq_levelRaise_qExp_at_coprime f hp h_vanish g_low_cast g_low h_cast_fun hg_low_qexp
  have h_Psi_eq_Vp_coeff :
      (ModularFormClass.qExpansion (1 : ℝ) Ψ_fun).coeff m =
        (ModularFormClass.qExpansion (1 : ℝ) Vp_slash_lifted_fun).coeff m := by
    rcases Nat.lt_or_ge 1 l' with hl1_gt | hl1_le
    · exact descent_l_prime_gt_one_apply χ f hfχ p hp hpN χ' hχ_eq
        hl1_gt hl'_sqfree hpl' hl'_dvd hp_not_in h_vanish g_low g_low_cast
        h_cast_fun hg_low_full_qexp h_delta_Fourier_vanish m hm_cop
    · have hl'_eq_1 : l' = 1 := by lia
      have h_all_cop : ∀ n : ℕ, Nat.Coprime n l' := fun n ↦
        hl'_eq_1 ▸ Nat.coprime_one_right n
      have hp_M_eq_N : p * ((l' * N) / p) = N := by
        rw [Nat.mul_div_cancel' hp_dvd_lN, hl'_eq_1, one_mul]
      have h_fun_eq : (⇑f.toModularForm' : UpperHalfPlane → ℂ) =
          ⇑(HeckeRing.GL2.modularFormLevelRaise ((l' * N) / p) p k
            g_low_cast.toModularForm') :=
        miyake_descent_l_prime_eq_one_helper f g_low_cast hp_M_eq_N
          (fun n ↦ h_delta_Fourier_vanish n (h_all_cop n))
      have h_Psi_eq_Vp_fun : Ψ_fun = Vp_slash_lifted_fun := by
        funext z
        simp only [hΨ_fun_def, hVp_slash_lifted_fun_def]
        exact Finset.sum_congr rfl fun v _ ↦ by rw [h_fun_eq]
      have h_qe_eq : ModularFormClass.qExpansion (1 : ℝ) Ψ_fun =
          ModularFormClass.qExpansion (1 : ℝ) Vp_slash_lifted_fun :=
        qExpansion_ext2 Ψ_fun Vp_slash_lifted_fun h_Psi_eq_Vp_fun
      rw [h_qe_eq]
  rw [h_Psi_eq_Vp_coeff, h_Vp_qexp_eq, h_Dp_g_low_qexp]

private lemma Φ_qExp_coeff_eq_count_div_p_mul_g_low_coeff
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ)
    (p : ℕ) [NeZero p] (hp : p.Prime) (hpN : p ∣ N) [NeZero (N / p)]
    (χ' : (ZMod (N / p))ˣ →* ℂˣ)
    (hχ_eq : χ = χ'.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)))
    (hfχ_mod : f.toModularForm' ∈ modFormCharSpace k χ)
    {l' : ℕ} (hl'_pos : 0 < l') (hl'_sqfree : Squarefree l')
    (hpl' : Nat.Coprime p l')
    (hl'_dvd : ∀ q ∈ l'.primeFactors, q ∈ N.primeFactors)
    (hp_not_in : p ∉ l'.primeFactors)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p * l') →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    [NeZero (l' * (N / p))]
    (g_low : CuspForm ((Gamma1 (l' * (N / p))).map (mapGL ℝ)) k)
    (hg_low_qexp : ∀ n : ℕ, p ∣ n → Nat.Coprime n l' →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff (n / p))
    (hg_low_full_qexp : ∀ m : ℕ,
      (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m =
        if Nat.Coprime m l' then
          (ModularFormClass.qExpansion (1 : ℝ) f).coeff (p * m)
        else 0)
    (m : ℕ) (hm_cop : Nat.Coprime m l') :
    (ModularFormClass.qExpansion (1 : ℝ)
      (descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod)).coeff m =
      (descendCosetCount p N : ℂ) / (p : ℂ) *
        (ModularFormClass.qExpansion (1 : ℝ) g_low).coeff m := by
  haveI hl'_NeZero : NeZero l' := ⟨hl'_pos.ne'⟩
  haveI : NeZero (l' * N) := ⟨Nat.mul_ne_zero hl'_pos.ne' (NeZero.ne N)⟩
  have hp_dvd_lN : p ∣ l' * N := dvd_mul_of_dvd_right hpN l'
  haveI hlN_div_NeZero : NeZero ((l' * N) / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.mul_pos hl'_pos (NeZero.pos N)) hp_dvd_lN)
      hp.pos).ne'⟩
  have h_D_eq : descendCosetCount p (l' * N) = descendCosetCount p N :=
    descendCosetCount_mul_left_of_coprime hpl'
  set Φ_fun : UpperHalfPlane → ℂ := fun z ↦
      ∑ v : Fin (descendCosetCount p N),
        (⇑f.toModularForm' ∣[k] descendCosetList p N hp v) z
  set Ψ_fun : UpperHalfPlane → ℂ := fun z ↦
      ∑ v : Fin (descendCosetCount p (l' * N)),
        (⇑f.toModularForm' ∣[k] descendCosetList p (l' * N) hp v) z
  have hΦ_eq_Ψ : Φ_fun = Ψ_fun :=
    funext fun z ↦
      miyake_4_6_6_level_commute p hp hpN hpl' χ f.toModularForm' hfχ_mod z
  have h_Mp_eq : (l' * N) / p = l' * (N / p) := by
    rcases hpN with ⟨d, hd⟩
    rw [hd, show l' * (p * d) = p * (l' * d) by ring,
      Nat.mul_div_cancel_left _ hp.pos, Nat.mul_div_cancel_left _ hp.pos]
  let g_low_cast : CuspForm ((Gamma1 ((l' * N) / p)).map (mapGL ℝ)) k :=
    h_Mp_eq.symm ▸ g_low
  have h_cast_fun : (⇑g_low_cast : UpperHalfPlane → ℂ) = ⇑g_low :=
    cuspForm_cast_coe h_Mp_eq.symm g_low
  have h_slash_sum_lifted_qexp :=
    descent_slashSum_qExp_coeff_eq_Dp_g_low_coeff χ f hfχ p hp hpN χ' hχ_eq
      hl'_pos hl'_sqfree hpl' hl'_dvd hp_not_in h_vanish g_low g_low_cast
      h_cast_fun hg_low_qexp hg_low_full_qexp m hm_cop
  rw [show ModularFormClass.qExpansion (1 : ℝ)
      (descendSlashSumCuspForm χ f p hp hpN χ' hχ_eq hfχ_mod) =
      ModularFormClass.qExpansion (1 : ℝ) Ψ_fun from
    qExpansion_ext2 Φ_fun Ψ_fun hΦ_eq_Ψ,
    h_slash_sum_lifted_qexp, h_D_eq]

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
