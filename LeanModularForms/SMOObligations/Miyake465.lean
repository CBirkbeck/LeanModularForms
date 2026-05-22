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
# Strong Multiplicity One via Miyake §4.6 — Lemma 4.6.5

CuspForm-level preservation lemmas and Miyake's Lemma 4.6.5 (single-prime
coprime filter and its iterated forms). Part of a multi-file split of
`SMOObligations.lean`.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- CuspForm-level subgroup-restriction preserves the Nebentypus
character space (with the natural pullback of `χ` along the unit map).

Derived from `restrictSubgroup_mem_modFormCharSpace` (ModularForm
version) via the CuspForm ↔ ModularForm character-space iff. -/
lemma cuspForm_restrictSubgroup_mem_cuspFormCharSpace
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
lemma cuspForm_levelRaise_mem_cuspFormCharSpace
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

end HeckeRing.GL2
