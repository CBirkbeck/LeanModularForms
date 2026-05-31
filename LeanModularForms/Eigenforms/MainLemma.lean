/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.Eigenforms.MainLemma.CoprimeSieve
import LeanModularForms.HeckeRIngs.GL2.Gamma1Pair
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Miyake Theorem 4.6.5 — coprime sieving

Given `f ∈ M_k(N, χ)` with `q`-expansion `f(τ) = Σ_{n ≥ 0} a_n qₙ(τ)`,
and a positive integer `L`, the **coprime-sieved** series

  `g(τ) := Σ_{(n, L) = 1} a_n qₙ(τ)`

keeps only the coefficients at indices coprime to `L`.  Miyake
Theorem 4.6.5 asserts that `g` is itself a modular form of weight `k`
at level `N · L²` (with the same Nebentypus character `χ` suitably
transported to the higher level), via Möbius inversion over divisors
of `L`.

## References

* Miyake, *Modular Forms*, Theorem 4.6.5.
* Diamond–Shurman, *A First Course in Modular Forms*, §5.6.
-/

open scoped ModularForm ArithmeticFunction MatrixGroups
open ModularFormClass CongruenceSubgroup Matrix.SpecialLinearGroup

namespace HeckeRing.GL2.MainLemma

private theorem ite_dvd_cons_eq_ite_exists
    {α : Type*} (p₀ n : ℕ) (L' : List ℕ) (a b : α) :
    (if p₀ ∣ n then a else if ∃ q ∈ L', q ∣ n then a else b) =
      if ∃ p ∈ p₀ :: L', p ∣ n then a else b := by
  simp only [List.exists_mem_cons_iff]
  split <;> simp_all

private theorem neZero_mul_list_prod_of_prime_dvd
    {M : ℕ} [NeZero M] {L : List ℕ} (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M) :
    NeZero (M * L.prod) :=
  ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩

private theorem consTail_prime_dvd
    {M p₀ : ℕ} {L' : List ℕ}
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    ∀ p ∈ L', p.Prime ∧ p ∣ M :=
  fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)

private theorem consHead_prime_dvd
    {M p₀ : ℕ} {L' : List ℕ}
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    p₀.Prime ∧ p₀ ∣ M :=
  hL p₀ List.mem_cons_self

/-- For `N ∣ M`, the image `(Γ₁(M)).map (mapGL ℝ)` is contained in
`(Γ₁(N)).map (mapGL ℝ)` inside `GL(2, ℝ)`. -/
theorem Gamma1_mapGL_le_of_dvd {M N : ℕ} (h : N ∣ M) :
    (Gamma1 M).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
  Subgroup.map_mono (HeckeRing.GL2.Gamma1_le_of_dvd h)

private theorem consPrime_not_coprime
    {M p₀ : ℕ} {L' : List ℕ}
    (hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M) :
    ¬ Nat.Coprime p₀ (M * L'.prod) :=
  Nat.Prime.not_coprime_iff_dvd.mpr
    ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩

private theorem consGamma1_le
    (p₀ M : ℕ) (L' : List ℕ) :
    (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
      (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
  Gamma1_mapGL_le_of_dvd ⟨p₀, by ring⟩

private theorem consLevel_eq (p₀ M : ℕ) (L' : List ℕ) :
    p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
  rw [List.prod_cons]; ring

/-- Specialisation of `Gamma1_mapGL_le_of_dvd` to `N ∣ p · N`. -/
theorem Gamma1_mapGL_le_mul_left (N p : ℕ) :
    (Gamma1 (p * N)).map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ) :=
  Gamma1_mapGL_le_of_dvd (Dvd.intro_left p rfl)

/-- Miyake 4.6.5 single-prime sieve from the no-diamond hypothesis.
Given `f : M_k(Γ₁(N))` and any `g : M_k(Γ₁(N))` satisfying the
"no-diamond" condition `(qExpansion N g).coeff m = (qExpansion N f).coeff
(p · m)`, the Fourier coefficients of `f − modularFormLevelRaise N p k g`
at period `N` are exactly the `p`-coprime sieve of `f`. -/
theorem miyake_4_6_5_prime_sieve_from_no_diamond
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_no_diamond : ∀ m : ℕ,
      (qExpansion (N : ℝ) g).coeff m = (qExpansion (N : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion (N : ℝ) f).coeff n -
        (qExpansion (N : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise N p k g)).coeff n =
      (if p ∣ n then 0 else (qExpansion (N : ℝ) f).coeff n) := by
  have hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) =
      (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl, strictPeriods_Gamma1]
    exact ⟨(N : ℤ), by simp⟩
  rw [HeckeRing.GL2.qExpansion_modularFormLevelRaise_coeff hN_period g n]
  by_cases h : p ∣ n
  · rw [if_pos h, if_pos h, hg_no_diamond (n / p), Nat.mul_div_cancel' h, sub_self]
  · rw [if_neg h, if_neg h, sub_zero]

/-- Period-1 variant of `miyake_4_6_5_prime_sieve_from_no_diamond`: under
a no-diamond hypothesis at period `1`, `f − modularFormLevelRaise N p k g`
has its period-`1` Fourier coefficient equal to `a_n` at `p ∤ n` and `0`
at `p ∣ n`. -/
theorem miyake_4_6_5_prime_sieve_from_no_diamond_one
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_no_diamond_one : ∀ m : ℕ,
      (qExpansion (1 : ℝ) g).coeff m = (qExpansion (1 : ℝ) f).coeff (p * m))
    (n : ℕ) :
    (qExpansion (1 : ℝ) f).coeff n -
        (qExpansion (1 : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise N p k g)).coeff n =
      (if p ∣ n then 0 else (qExpansion (1 : ℝ) f).coeff n) := by
  rw [HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff g n]
  by_cases h : p ∣ n
  · simp [h, hg_no_diamond_one (n / p), Nat.mul_div_cancel' h]
  · simp [h]

/-- Period-1 same-level single-prime sieve with the concrete
`heckeT_p_divN` witness (Miyake 4.6.5 / Diamond–Shurman Prop 5.9).  For a
prime `p ∣ M` and `f ∈ M_k(Γ₁(M))`, the difference between `f` and the
level-raised image of `heckeT_p_divN k p hp hpM f` has its `n`-th period-1
Fourier coefficient equal to `a_n(f)` when `p ∤ n` and `0` when `p ∣ n`. -/
theorem miyake_4_6_5_prime_sieve_heckeT_p_divN_one
    {M : ℕ} [NeZero M] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpM : ¬ Nat.Coprime p M)
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ) f).coeff n -
        (qExpansion (1 : ℝ)
          (HeckeRing.GL2.modularFormLevelRaise M p k
            (HeckeRing.GL2.heckeT_p_divN k p hp hpM f))).coeff n =
      (if p ∣ n then 0 else (qExpansion (1 : ℝ) f).coeff n) :=
  miyake_4_6_5_prime_sieve_from_no_diamond_one f
    (HeckeRing.GL2.heckeT_p_divN k p hp hpM f)
    (HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff hp hpM f) n

private theorem qExpansion_coeff_sieve_step
    {M : ℕ} [NeZero M] {k : ℤ} {p₀ : ℕ} [NeZero p₀]
    (hp₀_prime : p₀.Prime) (hp₀_not_coprime : ¬ Nat.Coprime p₀ M)
    (h_le : (Gamma1 (p₀ * M)).map (mapGL ℝ) ≤ (Gamma1 M).map (mapGL ℝ))
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ)
        (ModularForm.restrictSubgroup h_le g -
          HeckeRing.GL2.modularFormLevelRaise M p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g))).coeff n =
      (if p₀ ∣ n then 0 else (qExpansion (1 : ℝ) g).coeff n) := by
  haveI : NeZero (p₀ * M) := ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne M)⟩
  have h1_period : (1 : ℝ) ∈ ((Gamma1 (p₀ * M)).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 (p₀ * M)).map (mapGL ℝ) =
          (Gamma1 (p₀ * M) : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h_restrict_coeff :
      (qExpansion (1 : ℝ) (ModularForm.restrictSubgroup h_le g)).coeff n =
      (qExpansion (1 : ℝ) g).coeff n := rfl
  rw [qExpansion_sub one_pos h1_period, map_sub, h_restrict_coeff,
    miyake_4_6_5_prime_sieve_heckeT_p_divN_one hp₀_prime hp₀_not_coprime g n]

/-- Restriction along `Γ₁(N) ≤ Γ₁(M)` (for `M ∣ N`) carries
`modFormCharSpace k χ` into `modFormCharSpace k (χ.comp (ZMod.unitsMap h))`,
i.e. the Nebentypus pulls back along the natural map `(ZMod N)ˣ → (ZMod M)ˣ`. -/
theorem restrictSubgroup_mem_modFormCharSpace
    {M N : ℕ} [NeZero M] [NeZero N] {k : ℤ} (χ : (ZMod M)ˣ →* ℂˣ)
    (h : M ∣ N) (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf : f ∈ modFormCharSpace k χ) :
    ModularForm.restrictSubgroup
        (Gamma1_mapGL_le_of_dvd h) f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap h)) := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  have hg_M : (g : SL(2, ℤ)) ∈ Gamma0 M := Gamma0_le_of_dvd h g.property
  suffices h_units :
      Gamma0MapUnits (⟨(g : SL(2, ℤ)), hg_M⟩ : ↥(Gamma0 M)) =
        ZMod.unitsMap h (Gamma0MapUnits g) by
    rw [ModularForm.coe_restrictSubgroup, hf ⟨(g : SL(2, ℤ)), hg_M⟩,
      MonoidHom.comp_apply, h_units]
  apply Units.ext
  rw [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0MapUnits_val]
  exact (ZMod.cast_intCast h (((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)).symm

/-- The Hecke operator `heckeT_p_divN` (level-`N` no-diamond case,
`p ∣ N`) preserves every `modFormCharSpace k χ` at level
`Γ₁(N).map mapGL ℝ`. -/
theorem heckeT_p_divN_preserves_modFormCharSpace
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) (χ : (ZMod N)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    HeckeRing.GL2.heckeT_p_divN k p hp hpN f ∈ modFormCharSpace k χ := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro g
  show (HeckeRing.GL2.heckeT_p_ut k p hp.pos ⇑f) ∣[k] mapGL ℝ (g : SL(2, ℤ)) =
    ↑(χ (Gamma0MapUnits g)) • HeckeRing.GL2.heckeT_p_ut k p hp.pos ⇑f
  rw [HeckeRing.GL2.heckeT_p_ut_orbit_comm_gamma0_fun k p hp hpN f g]
  show HeckeRing.GL2.heckeT_p_ut k p hp.pos (⇑f ∣[k] mapGL ℝ (g : SL(2, ℤ))) = _
  rw [hf g]
  set c : ℂ := ↑(χ (Gamma0MapUnits g))
  change HeckeRing.GL2.heckeT_p_ut k p hp.pos (c • ⇑f) =
    c • HeckeRing.GL2.heckeT_p_ut k p hp.pos ⇑f
  ext z
  exact DFunLike.congr_fun
    ((HeckeRing.GL2.heckeT_p_divN k p hp hpN).map_smul c f) z

private theorem levelRaise_conj_char_eq
    (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (χ : (ZMod M)ˣ →* ℂˣ)
    (γ' : ↥(Gamma0 (d * M)))
    (hdvd : (d : ℤ) ∣ ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (h_conj_G0 :
      (HeckeRing.GL2.levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd : SL(2, ℤ)) ∈
        Gamma0 M) :
    χ (Gamma0MapUnits (⟨_, h_conj_G0⟩ : ↥(Gamma0 M))) =
      (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) (Gamma0MapUnits γ') := by
  rw [MonoidHom.comp_apply]
  congr 1
  apply Units.ext
  rw [ZMod.unitsMap_val, Gamma0MapUnits_val, Gamma0MapUnits_val]
  show (((HeckeRing.GL2.levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd
    : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ZMod M) = _
  rw [HeckeRing.GL2.levelRaiseConjOfDvd_lower_right]
  exact (ZMod.cast_intCast (Nat.dvd_mul_left M d)
    (((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1)).symm

/-- Level-raising pulls back the Nebentypus: for `f ∈ modFormCharSpace k χ`
at level `Γ₁(M)` and `d ≥ 1`, the level-raised form
`modularFormLevelRaise M d k f` at level `Γ₁(d·M)` lies in
`modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d)))`. -/
theorem modularFormLevelRaise_mem_modFormCharSpace
    (M : ℕ) [NeZero M] (d : ℕ) [NeZero d] (k : ℤ) (χ : (ZMod M)ˣ →* ℂˣ)
    {f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    HeckeRing.GL2.modularFormLevelRaise M d k f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) := by
  rw [modFormCharSpace_iff_nebentypus] at hf ⊢
  intro γ'
  have hdvd : (d : ℤ) ∣ ((γ' : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    HeckeRing.GL2.Gamma0_dmul_lower_left_dvd d M _ γ'.property
  rw [HeckeRing.GL2.coe_modularFormLevelRaise,
    HeckeRing.GL2.slash_mapGL_levelRaiseFun d k _ hdvd]
  have h_conj_G0 :
      (HeckeRing.GL2.levelRaiseConjOfDvd d (γ' : SL(2, ℤ)) hdvd : SL(2, ℤ)) ∈
        Gamma0 M :=
    HeckeRing.GL2.levelRaiseConjOfDvd_mem_Gamma0 d M _ γ'.property
  rw [hf ⟨_, h_conj_G0⟩]
  rw [levelRaise_conj_char_eq M d χ γ' hdvd h_conj_G0]
  set c : ℂ :=
    ↑((χ.comp (ZMod.unitsMap (Nat.dvd_mul_left M d))) (Gamma0MapUnits γ'))
  change HeckeRing.GL2.levelRaiseFun d k (c • ⇑f) =
    c • HeckeRing.GL2.levelRaiseFun d k ⇑f
  ext z
  exact DFunLike.congr_fun
    ((HeckeRing.GL2.modularFormLevelRaise M d k).map_smul c f) z

private theorem restrictSubgroup_mem_modFormCharSpace_comp
    {M N N' : ℕ} [NeZero M] [NeZero N] [NeZero N'] {k : ℤ}
    (χ : (ZMod M)ˣ →* ℂˣ) (hdvd_prev : M ∣ N) (h_nn' : N ∣ N') (hdvd_inner : M ∣ N')
    (h_le : (Gamma1 N').map (mapGL ℝ) ≤ (Gamma1 N).map (mapGL ℝ))
    {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg : g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_prev))) :
    ModularForm.restrictSubgroup h_le g ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
  have h_comp_eq :
      (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_nn') =
        χ.comp (ZMod.unitsMap hdvd_inner) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  have h := restrictSubgroup_mem_modFormCharSpace
    (χ.comp (ZMod.unitsMap hdvd_prev)) h_nn' g hg
  rwa [h_comp_eq] at h

private theorem levelRaise_heckeT_mem_modFormCharSpace_comp
    {M N : ℕ} [NeZero M] [NeZero N] {k : ℤ} {p₀ : ℕ} [NeZero p₀]
    (hp₀_prime : p₀.Prime) (hp₀_not_coprime : ¬ Nat.Coprime p₀ N)
    (χ : (ZMod M)ˣ →* ℂˣ) (hdvd_prev : M ∣ N) (hdvd_inner : M ∣ p₀ * N)
    {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg : g ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_prev))) :
    HeckeRing.GL2.modularFormLevelRaise N p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime g) ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) := by
  have h_mp_dvd : N ∣ p₀ * N := Nat.dvd_mul_left N p₀
  have h_comp_eq :
      (χ.comp (ZMod.unitsMap hdvd_prev)).comp (ZMod.unitsMap h_mp_dvd) =
        χ.comp (ZMod.unitsMap hdvd_inner) := by
    rw [MonoidHom.comp_assoc, ZMod.unitsMap_comp]
  have h_ht := heckeT_p_divN_preserves_modFormCharSpace
    hp₀_prime hp₀_not_coprime (χ.comp (ZMod.unitsMap hdvd_prev)) hg
  have h_lr := modularFormLevelRaise_mem_modFormCharSpace
    N p₀ k (χ.comp (ZMod.unitsMap hdvd_prev)) h_ht
  rwa [h_comp_eq] at h_lr

private theorem qExpansion_one_Gamma1_eq_zero_iff
    {N : ℕ} [NeZero N] {k : ℤ}
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    qExpansion (1 : ℝ) g = 0 ↔ g = 0 := by
  apply qExpansion_eq_zero_iff one_pos
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    CongruenceSubgroup.strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

private noncomputable def iteratedSieveWitnessOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k
  | [], _ =>
    (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
      hL' p₀ (List.mem_cons_self)
    let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_M_prev : p₀ ∣ M * L'.prod :=
      hp₀_prime_M.2.mul_right _
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd ⟨p₀, by ring⟩
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    let g_new : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      ModularForm.restrictSubgroup h_le g_prev -
        HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    hM_eq ▸ g_new

private theorem iteratedSieveWitnessOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveWitnessOnList f [] h =
      (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f :=
  rfl

private theorem iteratedSieveWitnessOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL' : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    iteratedSieveWitnessOnList f (p₀ :: L') hL' =
      (let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
       let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
        hL' p₀ List.mem_cons_self
       let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props
       haveI hM_prev_ne : NeZero (M * L'.prod) := by
         have hL'_pos : 0 < L'.prod := by
           apply List.prod_pos
           intro p hp
           exact (hL'_props p hp).1.pos
         exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
       haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
       have hp₀_M_prev : p₀ ∣ M * L'.prod :=
         hp₀_prime_M.2.mul_right _
       have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
         Nat.Prime.not_coprime_iff_dvd.mpr
           ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
       have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
           (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
         Gamma1_mapGL_le_of_dvd ⟨p₀, by ring⟩
       have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
         rw [List.prod_cons]; ring
       hM_eq ▸ (ModularForm.restrictSubgroup h_le g_prev -
         HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
           (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
             g_prev))) :=
  rfl

private theorem qExpansion_coeff_cast_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ)
        ((h ▸ g) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n =
      (qExpansion (1 : ℝ) g).coeff n := by
  subst h; rfl

private theorem iteratedSieveWitnessOnList_qExpansion_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M) (n : ℕ),
    (qExpansion (1 : ℝ) (iteratedSieveWitnessOnList f L hL)).coeff n =
      (if ∃ p ∈ L, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n)
  | [], _, n => by
    rw [iteratedSieveWitnessOnList_nil,
      qExpansion_coeff_cast_Gamma1 (show (M : ℕ) = M * ([] : List ℕ).prod from by simp) f n]
    simp
  | p₀ :: L', hL', n => by
    rw [iteratedSieveWitnessOnList_cons]
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M := consTail_prime_dvd hL'
    set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := consHead_prime_dvd hL'
    set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) :=
      neZero_mul_list_prod_of_prime_dvd hL'_props
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      consPrime_not_coprime hp₀_prime_M
    have h_le := consGamma1_le p₀ M L'
    have hM_eq := consLevel_eq p₀ M L'
    haveI hM_new_ne : NeZero (p₀ * (M * L'.prod)) :=
      ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
    rw [qExpansion_coeff_cast_Gamma1 hM_eq _ n, ModularForm.coe_sub,
      qExpansion_coeff_sieve_step hp₀_prime_M.1 hp₀_not_coprime h_le g_prev n,
      iteratedSieveWitnessOnList_qExpansion_coeff f L' hL'_props n]
    exact ite_dvd_cons_eq_ite_exists p₀ n L' 0 _

private theorem iteratedSieveWitnessOnList_qExpansion_zero_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    qExpansion (1 : ℝ) (iteratedSieveWitnessOnList f L hL) = 0 := by
  ext n
  rw [iteratedSieveWitnessOnList_qExpansion_coeff f L hL n]
  by_cases hdiv : ∃ p ∈ L, p ∣ n
  · rw [if_pos hdiv]; simp
  · rw [if_neg hdiv]
    have hcop : Nat.Coprime n L.prod := by
      rw [Nat.coprime_list_prod_right_iff]
      intro p hpL
      exact ((hL p hpL).1.coprime_iff_not_dvd.mpr
        (fun hpn ↦ hdiv ⟨p, hpL, hpn⟩)).symm
    rw [h_vanish n hcop]; simp

private theorem iteratedSieveWitnessOnList_eq_zero_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    iteratedSieveWitnessOnList f L hL = 0 := by
  haveI hML_ne : NeZero (M * L.prod) := by
    have hL_pos : 0 < L.prod := by
      apply List.prod_pos
      intro p hp
      exact (hL p hp).1.pos
    exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  exact (qExpansion_one_Gamma1_eq_zero_iff
    (iteratedSieveWitnessOnList f L hL)).mp
    (iteratedSieveWitnessOnList_qExpansion_zero_of_coprime_prod_vanish
      f L hL h_vanish)

private theorem cast_eq_zero_iff_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ((h ▸ g) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 ↔ g = 0 := by
  subst h; rfl

private theorem iteratedSieveWitnessOnList_cons_zero_step
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M)
    [NeZero (M * L'.prod)] [NeZero p₀]
    (hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod))
    (h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ))
    (h_zero : iteratedSieveWitnessOnList f (p₀ :: L') hL = 0) :
    ModularForm.restrictSubgroup h_le
        (iteratedSieveWitnessOnList f L'
          (fun p hp ↦ hL p (List.mem_cons_of_mem _ hp))) =
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ (hL p₀ List.mem_cons_self).1
          hp₀_not_coprime
          (iteratedSieveWitnessOnList f L'
            (fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)))) := by
  rw [iteratedSieveWitnessOnList_cons] at h_zero
  have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
    rw [List.prod_cons]; ring
  haveI : NeZero (p₀ * (M * L'.prod)) :=
    ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
  rw [cast_eq_zero_iff_Gamma1 hM_eq _] at h_zero
  exact sub_eq_zero.mp h_zero

private noncomputable def iteratedSieveCorrectionsOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k
  | [], _ => 0
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
      hL' p₀ (List.mem_cons_self)
    let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    let c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveCorrectionsOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_M_prev : p₀ ∣ M * L'.prod :=
      hp₀_prime_M.2.mul_right _
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd ⟨p₀, by ring⟩
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    let c_new : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      ModularForm.restrictSubgroup h_le c_prev +
        HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    hM_eq ▸ c_new

private theorem iteratedSieveCorrectionsOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionsOnList f [] h = 0 := rfl

private theorem iteratedSieveCorrectionsOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL' : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionsOnList f (p₀ :: L') hL' =
      (let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
        fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
       let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
        hL' p₀ List.mem_cons_self
       let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props
       let c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveCorrectionsOnList f L' hL'_props
       haveI hM_prev_ne : NeZero (M * L'.prod) := by
         have hL'_pos : 0 < L'.prod := by
           apply List.prod_pos
           intro p hp
           exact (hL'_props p hp).1.pos
         exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
       haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
       have hp₀_M_prev : p₀ ∣ M * L'.prod :=
         hp₀_prime_M.2.mul_right _
       have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
         Nat.Prime.not_coprime_iff_dvd.mpr
           ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_M_prev⟩
       have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
           (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
         Gamma1_mapGL_le_of_dvd ⟨p₀, by ring⟩
       have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
         rw [List.prod_cons]; ring
       hM_eq ▸ (ModularForm.restrictSubgroup h_le c_prev +
         HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
           (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
             g_prev))) :=
  rfl

private theorem ModularForm_restrictSubgroup_restrictSubgroup
    {Γ Γ' Γ'' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (h₁ : Γ' ≤ Γ) (h₂ : Γ'' ≤ Γ')
    (f : ModularForm Γ k) :
    ModularForm.restrictSubgroup h₂ (ModularForm.restrictSubgroup h₁ f) =
      ModularForm.restrictSubgroup (le_trans h₂ h₁) f := rfl

private theorem cast_add_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (x y : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ((h ▸ (x + y)) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (h ▸ x) + (h ▸ y) := by
  subst h; rfl

private theorem restrictSubgroup_cast_eq_of_level_eq
    {A B : ℕ} {k : ℤ} (h : A = B)
    {Γ : Subgroup (GL (Fin 2) ℝ)}
    (h_le_A : (Gamma1 A).map (mapGL ℝ) ≤ Γ)
    (h_le_B : (Gamma1 B).map (mapGL ℝ) ≤ Γ)
    (f : ModularForm Γ k) :
    ((h ▸ ModularForm.restrictSubgroup h_le_A f) :
        ModularForm ((Gamma1 B).map (mapGL ℝ)) k) =
      ModularForm.restrictSubgroup h_le_B f := by
  subst h; rfl

private theorem restrictSubgroup_cast_nil_eq
    {M : ℕ} [NeZero M] {k : ℤ}
    (h_le_full : (Gamma1 (M * ([] : List ℕ).prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ModularForm.restrictSubgroup h_le_full f =
      ((show (M : ℕ) = M * ([] : List ℕ).prod from by simp) ▸ f) := by
  have hM_eq : M = M * ([] : List ℕ).prod := by simp
  have h_self : f = ModularForm.restrictSubgroup (le_refl _) f := rfl
  rw [show ((hM_eq ▸ f) : ModularForm ((Gamma1 (M * ([] : List ℕ).prod)).map
    (mapGL ℝ)) k) =
      hM_eq ▸ ModularForm.restrictSubgroup (le_refl
        ((Gamma1 M).map (mapGL ℝ))) f from by rw [← h_self]]
  exact (restrictSubgroup_cast_eq_of_level_eq hM_eq (le_refl _) h_le_full f).symm

private theorem iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
      (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
        (Gamma1 M).map (mapGL ℝ)),
      ModularForm.restrictSubgroup h_le_full f =
        iteratedSieveWitnessOnList f L hL +
          iteratedSieveCorrectionsOnList f L hL
  | [], hL, h_le_full => by
    rw [iteratedSieveWitnessOnList_nil, iteratedSieveCorrectionsOnList_nil,
      add_zero]
    exact restrictSubgroup_cast_nil_eq h_le_full f
  | p₀ :: L', hL, h_le_full => by
    rw [iteratedSieveWitnessOnList_cons, iteratedSieveCorrectionsOnList_cons]
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M := consTail_prime_dvd hL
    set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := consHead_prime_dvd hL
    set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    set c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveCorrectionsOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) :=
      neZero_mul_list_prod_of_prime_dvd hL'_props
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      consPrime_not_coprime hp₀_prime_M
    have h_le := consGamma1_le p₀ M L'
    have hM_eq := consLevel_eq p₀ M L'
    set lr : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    rw [← cast_add_Gamma1 hM_eq
      (ModularForm.restrictSubgroup h_le g_prev - lr)
      (ModularForm.restrictSubgroup h_le c_prev + lr)]
    have h_inner : (ModularForm.restrictSubgroup h_le g_prev - lr) +
        (ModularForm.restrictSubgroup h_le c_prev + lr) =
        ModularForm.restrictSubgroup h_le (g_prev + c_prev) := by
      have h_radd : ModularForm.restrictSubgroup h_le (g_prev + c_prev) =
          ModularForm.restrictSubgroup h_le g_prev +
            ModularForm.restrictSubgroup h_le c_prev := rfl
      rw [h_radd]; abel
    rw [h_inner]
    have h_le_prev : (Gamma1 (M * L'.prod)).map (mapGL ℝ) ≤
        (Gamma1 M).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd ⟨L'.prod, rfl⟩
    have h_ih := iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep
      f L' hL'_props h_le_prev
    rw [← h_ih, ModularForm_restrictSubgroup_restrictSubgroup]
    exact (restrictSubgroup_cast_eq_of_level_eq hM_eq
      (le_trans h_le h_le_prev) h_le_full f).symm

private theorem restrictSubgroup_eq_iteratedSieveCorrectionsOnList_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ModularForm.restrictSubgroup h_le_full f =
      iteratedSieveCorrectionsOnList f L hL := by
  rw [iteratedSieveWitnessOnList_add_corrections_eq_restrictDeep f L hL h_le_full,
    iteratedSieveWitnessOnList_eq_zero_of_coprime_prod_vanish f L hL h_vanish,
    zero_add]

private theorem restrictSubgroup_eq_corrections_cons_step_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M)
    (hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M)
    [NeZero (M * L'.prod)] [NeZero p₀]
    (hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod))
    (h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ))
    (h_le_full : (Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ) ≤
        (Gamma1 M).map (mapGL ℝ))
    (hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p₀ :: L').prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    ModularForm.restrictSubgroup h_le_full f =
      hM_eq ▸ (ModularForm.restrictSubgroup h_le
          (iteratedSieveCorrectionsOnList f L' hL'_props) +
        HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
          (HeckeRing.GL2.heckeT_p_divN k p₀ (hL p₀ List.mem_cons_self).1
            hp₀_not_coprime
            (iteratedSieveWitnessOnList f L' hL'_props))) := by
  rw [restrictSubgroup_eq_iteratedSieveCorrectionsOnList_of_coprime_prod_vanish
        f (p₀ :: L') hL h_vanish h_le_full,
      iteratedSieveCorrectionsOnList_cons f p₀ L' hL]

private noncomputable def iteratedSieveCorrectionPiecesOnList
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (L : List ℕ) → (∀ p ∈ L, p.Prime ∧ p ∣ M) →
    List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k)
  | [], _ => []
  | p₀ :: L', hL' =>
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL' p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M :=
      hL' p₀ List.mem_cons_self
    let g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) := by
      have hL'_pos : 0 < L'.prod := by
        apply List.prod_pos
        intro p hp
        exact (hL'_props p hp).1.pos
      exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd ⟨p₀, by ring⟩
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    let prev_pieces : List (ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k) :=
      iteratedSieveCorrectionPiecesOnList f L' hL'_props
    let lifted_prev : List (ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k) :=
      prev_pieces.map (fun x ↦ hM_eq ▸ ModularForm.restrictSubgroup h_le x)
    let new_piece : ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k :=
      hM_eq ▸ HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    lifted_prev ++ [new_piece]

private theorem iteratedSieveCorrectionPiecesOnList_nil
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (h : ∀ p ∈ ([] : List ℕ), p.Prime ∧ p ∣ M) :
    iteratedSieveCorrectionPiecesOnList f [] h = [] := rfl

private theorem cast_sum_Gamma1
    {M N : ℕ} [NeZero M] {k : ℤ}
    (h : M = N)
    (xs : List (ModularForm ((Gamma1 M).map (mapGL ℝ)) k)) :
    ((h ▸ xs.sum) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (xs.map (fun x ↦ (h ▸ x : ModularForm ((Gamma1 N).map (mapGL ℝ)) k))).sum := by
  subst h; simp

private theorem restrictSubgroup_sum_eq
    {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (h_le : Γ' ≤ Γ)
    (xs : List (ModularForm Γ k)) :
    ModularForm.restrictSubgroup h_le xs.sum =
      (xs.map (ModularForm.restrictSubgroup h_le)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.sum_cons, List.map_cons]
    show ModularForm.restrictSubgroup h_le (x + xs.sum) =
      ModularForm.restrictSubgroup h_le x + (xs.map _).sum
    have h_add : ModularForm.restrictSubgroup h_le (x + xs.sum) =
        ModularForm.restrictSubgroup h_le x +
          ModularForm.restrictSubgroup h_le xs.sum := rfl
    rw [h_add, ih]

private theorem iteratedSieveCorrectionsOnList_eq_pieces_sum
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      iteratedSieveCorrectionsOnList f L hL =
        (iteratedSieveCorrectionPiecesOnList f L hL).sum
  | [], hL => by
    rw [iteratedSieveCorrectionsOnList_nil, iteratedSieveCorrectionPiecesOnList_nil,
      List.sum_nil]
  | p₀ :: L', hL => by
    rw [iteratedSieveCorrectionsOnList_cons f p₀ L' hL]
    set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M := consTail_prime_dvd hL
    set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := consHead_prime_dvd hL
    set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveWitnessOnList f L' hL'_props
    set c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
      iteratedSieveCorrectionsOnList f L' hL'_props
    haveI hM_prev_ne : NeZero (M * L'.prod) :=
      neZero_mul_list_prod_of_prime_dvd hL'_props
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      consPrime_not_coprime hp₀_prime_M
    have h_le := consGamma1_le p₀ M L'
    have hM_eq := consLevel_eq p₀ M L'
    set prev_pieces :
        List (ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k) :=
      iteratedSieveCorrectionPiecesOnList f L' hL'_props
    set lr : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime g_prev)
    have h_ih : c_prev = prev_pieces.sum :=
      iteratedSieveCorrectionsOnList_eq_pieces_sum f L' hL'_props
    show (hM_eq ▸ (ModularForm.restrictSubgroup h_le c_prev + lr) :
        ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k) =
      (iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL).sum
    have h_pieces_unfold :
        iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL =
          (prev_pieces.map
            (fun x ↦ (hM_eq ▸ ModularForm.restrictSubgroup h_le x :
              ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k))) ++
            [(hM_eq ▸ lr :
              ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k)] := rfl
    rw [h_pieces_unfold, List.sum_append, List.sum_singleton,
      cast_add_Gamma1 hM_eq (ModularForm.restrictSubgroup h_le c_prev) lr,
      h_ih, restrictSubgroup_sum_eq h_le prev_pieces,
      cast_sum_Gamma1 hM_eq (prev_pieces.map (ModularForm.restrictSubgroup h_le)),
      List.map_map]
    rfl

private theorem iteratedSieveCorrectionPiecesOnList_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
    haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
      have hL'_pos : 0 < L'.prod :=
        List.prod_pos (fun p hp ↦ (hL'_props p hp).1.pos)
      exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
        (Gamma1 (M * L'.prod)).map (mapGL ℝ) :=
      Gamma1_mapGL_le_of_dvd ⟨p₀, by ring⟩
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL =
      ((iteratedSieveCorrectionPiecesOnList f L' hL'_props).map
        (fun x ↦ (hM_eq ▸ ModularForm.restrictSubgroup h_le x :
          ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k))) ++
        [(hM_eq ▸
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                (iteratedSieveWitnessOnList f L' hL'_props)) :
          ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k)] :=
  rfl

private theorem iteratedSieveCorrectionPiecesOnList_getLast_cons
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    (hL : ∀ p ∈ p₀ :: L', p.Prime ∧ p ∣ M) :
    let hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M :=
      fun p hp ↦ hL p (List.mem_cons_of_mem _ hp)
    let hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := hL p₀ List.mem_cons_self
    haveI hM_prev_ne : NeZero (M * L'.prod) := ⟨by
      have hL'_pos : 0 < L'.prod :=
        List.prod_pos (fun p hp ↦ (hL'_props p hp).1.pos)
      exact Nat.mul_ne_zero (NeZero.ne M) hL'_pos.ne'⟩
    haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
    have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
      Nat.Prime.not_coprime_iff_dvd.mpr
        ⟨p₀, hp₀_prime_M.1, dvd_refl _, hp₀_prime_M.2.mul_right _⟩
    have hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod := by
      rw [List.prod_cons]; ring
    ∃ h_ne : iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL ≠ [],
      (iteratedSieveCorrectionPiecesOnList f (p₀ :: L') hL).getLast h_ne =
        (hM_eq ▸
          HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
            (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
              (iteratedSieveWitnessOnList f L' hL'_props)) :
        ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k) := by
  rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL]
  refine ⟨?_, ?_⟩
  · exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _)
  · rw [List.getLast_append_right (List.cons_ne_nil _ _)]
    rfl

private theorem restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ModularForm.restrictSubgroup h_le_full f =
      (iteratedSieveCorrectionPiecesOnList f L hL).sum := by
  rw [restrictSubgroup_eq_iteratedSieveCorrectionsOnList_of_coprime_prod_vanish
        f L hL h_vanish h_le_full,
      iteratedSieveCorrectionsOnList_eq_pieces_sum f L hL]

private def IsOldformImageAtDeep
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (Mfull : ℕ) [NeZero Mfull]
    (g : ModularForm ((Gamma1 Mfull).map (mapGL ℝ)) k) : Prop :=
  ∃ (p : ℕ) (Lprev : List ℕ) (hLprev : ∀ q ∈ Lprev, q.Prime ∧ q ∣ M)
    (_ : NeZero p) (_ : NeZero (M * Lprev.prod)) (hp : p.Prime)
    (hpM' : ¬ Nat.Coprime p (M * Lprev.prod))
    (h_le' : (Gamma1 Mfull).map (mapGL ℝ) ≤
      (Gamma1 (p * (M * Lprev.prod))).map (mapGL ℝ)),
    g = ModularForm.restrictSubgroup h_le'
          (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
            (HeckeRing.GL2.heckeT_p_divN k p hp hpM'
              (iteratedSieveWitnessOnList f Lprev hLprev)))

private theorem head_piece_isOldformImageAtDeep
    {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) [NeZero p₀] (L' : List ℕ) (hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M)
    [NeZero (M * L'.prod)] (hp₀_prime : p₀.Prime)
    (hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod))
    (hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod)
    [NeZero (M * (p₀ :: L').prod)]
    {g : ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k}
    (hg : g = hM_eq ▸ HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime
          (iteratedSieveWitnessOnList f L' hL'_props))) :
    IsOldformImageAtDeep f (M * (p₀ :: L').prod) g := by
  refine ⟨p₀, L', hL'_props, ‹_›, ‹_›, hp₀_prime, hp₀_not_coprime, ?_, ?_⟩
  · intro x hx
    rwa [show M * (p₀ :: L').prod = p₀ * (M * L'.prod) from hM_eq.symm] at hx
  · rw [hg]
    set lr : ModularForm ((Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ)) k :=
      HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
        (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime hp₀_not_coprime
          (iteratedSieveWitnessOnList f L' hL'_props))
    conv_lhs => rw [show lr = ModularForm.restrictSubgroup (le_refl _) lr from rfl]
    exact restrictSubgroup_cast_eq_of_level_eq hM_eq _ _ _

private theorem mapped_piece_isOldformImageAtDeep
    {M : ℕ} [NeZero M] {k : ℤ} (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (p₀ : ℕ) (L' : List ℕ)
    [NeZero (M * L'.prod)] [NeZero (M * (p₀ :: L').prod)]
    (h_le : (Gamma1 (p₀ * (M * L'.prod))).map (mapGL ℝ) ≤
      (Gamma1 (M * L'.prod)).map (mapGL ℝ))
    (hM_eq : p₀ * (M * L'.prod) = M * (p₀ :: L').prod)
    {g₀ : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k}
    (hg₀ : IsOldformImageAtDeep f (M * L'.prod) g₀)
    {g : ModularForm ((Gamma1 (M * (p₀ :: L').prod)).map (mapGL ℝ)) k}
    (hg : hM_eq ▸ ModularForm.restrictSubgroup h_le g₀ = g) :
    IsOldformImageAtDeep f (M * (p₀ :: L').prod) g := by
  obtain ⟨p, Lprev, hLprev, hpNe, hMLprevNe, hp, hpM', h_le_inner, hg₀_form⟩ := hg₀
  refine ⟨p, Lprev, hLprev, hpNe, hMLprevNe, hp, hpM', ?_, ?_⟩
  · intro x hx
    refine h_le_inner (h_le ?_)
    rwa [show M * (p₀ :: L').prod = p₀ * (M * L'.prod) from hM_eq.symm] at hx
  · rw [← hg, hg₀_form, ModularForm_restrictSubgroup_restrictSubgroup]
    exact restrictSubgroup_cast_eq_of_level_eq hM_eq _ _ _

private theorem iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      ∀ g ∈ iteratedSieveCorrectionPiecesOnList f L hL,
        @IsOldformImageAtDeep M _ k f (M * L.prod)
          (by
            have hL_pos : 0 < L.prod := List.prod_pos (fun p hp ↦ (hL p hp).1.pos)
            exact ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩) g
  | [], _ => by
      intro g hg
      rw [iteratedSieveCorrectionPiecesOnList_nil] at hg
      simp at hg
  | p₀ :: L', hL => by
      intro g hg
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M := consTail_prime_dvd hL
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := consHead_prime_dvd hL
      haveI hM_prev_ne : NeZero (M * L'.prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'_props
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) :=
        neZero_mul_list_prod_of_prime_dvd hL
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        consPrime_not_coprime hp₀_prime_M
      have h_le := consGamma1_le p₀ M L'
      have hM_eq := consLevel_eq p₀ M L'
      rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL,
          List.mem_append] at hg
      rcases hg with hg_mapped | hg_last
      · rw [List.mem_map] at hg_mapped
        obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := hg_mapped
        exact mapped_piece_isOldformImageAtDeep f p₀ L' h_le hM_eq
          (iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage
            f L' hL'_props g₀ hg₀_mem) hg₀_eq
      · rw [List.mem_singleton] at hg_last
        exact head_piece_isOldformImageAtDeep f p₀ L' hL'_props hp₀_prime_M.1
          hp₀_not_coprime hM_eq hg_last

/-- Under the coprime-`L.prod` vanishing of period-1 Fourier coefficients,
the deep restriction of `f` is the `List.sum` of a finite list of modular
forms, each an oldform image at depth. -/
theorem exists_oldform_pieces_decomposition_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ∀ g ∈ pieces,
          @IsOldformImageAtDeep M _ k f (M * L.prod)
            (⟨Nat.mul_ne_zero (NeZero.ne M)
              (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩) g :=
  ⟨iteratedSieveCorrectionPiecesOnList f L hL,
    restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish
      f L hL h_vanish h_le_full,
    iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage f L hL⟩

private theorem cast_mem_modFormCharSpace_Gamma1
    {A B : ℕ} [NeZero A] [NeZero B] {k : ℤ} {M : ℕ} [NeZero M]
    (χ : (ZMod M)ˣ →* ℂˣ)
    (h : A = B) (hA : M ∣ A) (hB : M ∣ B)
    {f : ModularForm ((Gamma1 A).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k (χ.comp (ZMod.unitsMap hA))) :
    ((h ▸ f) : ModularForm ((Gamma1 B).map (mapGL ℝ)) k) ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap hB)) := by
  subst h; exact (show hA = hB from rfl) ▸ hf

private theorem iteratedSieveWitnessOnList_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
      iteratedSieveWitnessOnList f L hL ∈
        modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      haveI : NeZero (M * ([] : List ℕ).prod) := by simpa using (inferInstance : NeZero M)
      rw [iteratedSieveWitnessOnList_nil]
      have hM_eq : (M : ℕ) = M * ([] : List ℕ).prod := by simp
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq (dvd_refl M)
        (Nat.dvd_mul_right M ([] : List ℕ).prod)
        (by rw [ZMod.unitsMap_self, MonoidHom.comp_id]; exact hf_χ)
  | p₀ :: L', hL' => by
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M := consTail_prime_dvd hL'
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := consHead_prime_dvd hL'
      haveI hM_prev_ne : NeZero (M * L'.prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'_props
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'
      haveI hp₀M'_ne : NeZero (p₀ * (M * L'.prod)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        consPrime_not_coprime hp₀_prime_M
      have h_le := consGamma1_le p₀ M L'
      have hM_eq := consLevel_eq p₀ M L'
      have hdvd_prev : M ∣ M * L'.prod := Nat.dvd_mul_right M L'.prod
      have h_mp_dvd : (M * L'.prod) ∣ p₀ * (M * L'.prod) := ⟨p₀, by ring⟩
      have hdvd_inner : M ∣ p₀ * (M * L'.prod) := hdvd_prev.trans h_mp_dvd
      have hIH := iteratedSieveWitnessOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props
      have h_sub :
          ModularForm.restrictSubgroup h_le g_prev -
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                g_prev) ∈
            modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) :=
        Submodule.sub_mem _
          (restrictSubgroup_mem_modFormCharSpace_comp χ hdvd_prev h_mp_dvd hdvd_inner h_le hIH)
          (levelRaise_heckeT_mem_modFormCharSpace_comp hp₀_prime_M.1 hp₀_not_coprime χ
            hdvd_prev hdvd_inner hIH)
      rw [iteratedSieveWitnessOnList_cons]
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
        (Nat.dvd_mul_right M (p₀ :: L').prod) h_sub

private theorem iteratedSieveCorrectionsOnList_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
      iteratedSieveCorrectionsOnList f L hL ∈
        modFormCharSpace k
          (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      rw [iteratedSieveCorrectionsOnList_nil]
      exact Submodule.zero_mem _
  | p₀ :: L', hL' => by
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M := consTail_prime_dvd hL'
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := consHead_prime_dvd hL'
      haveI hM_prev_ne : NeZero (M * L'.prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'_props
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'
      haveI hp₀M'_ne : NeZero (p₀ * (M * L'.prod)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        consPrime_not_coprime hp₀_prime_M
      have h_le := consGamma1_le p₀ M L'
      have hM_eq := consLevel_eq p₀ M L'
      have hdvd_prev : M ∣ M * L'.prod := Nat.dvd_mul_right M L'.prod
      have h_mp_dvd : (M * L'.prod) ∣ p₀ * (M * L'.prod) := ⟨p₀, by ring⟩
      have hdvd_inner : M ∣ p₀ * (M * L'.prod) := hdvd_prev.trans h_mp_dvd
      have hIH_w := iteratedSieveWitnessOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      have hIH_c := iteratedSieveCorrectionsOnList_mem_modFormCharSpace
        f hf_χ L' hL'_props
      set g_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveWitnessOnList f L' hL'_props
      set c_prev : ModularForm ((Gamma1 (M * L'.prod)).map (mapGL ℝ)) k :=
        iteratedSieveCorrectionsOnList f L' hL'_props
      have h_add :
          ModularForm.restrictSubgroup h_le c_prev +
            HeckeRing.GL2.modularFormLevelRaise (M * L'.prod) p₀ k
              (HeckeRing.GL2.heckeT_p_divN k p₀ hp₀_prime_M.1 hp₀_not_coprime
                g_prev) ∈
            modFormCharSpace k (χ.comp (ZMod.unitsMap hdvd_inner)) :=
        Submodule.add_mem _
          (restrictSubgroup_mem_modFormCharSpace_comp χ hdvd_prev h_mp_dvd hdvd_inner h_le hIH_c)
          (levelRaise_heckeT_mem_modFormCharSpace_comp hp₀_prime_M.1 hp₀_not_coprime χ
            hdvd_prev hdvd_inner hIH_w)
      rw [iteratedSieveCorrectionsOnList_cons]
      exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
        (Nat.dvd_mul_right M (p₀ :: L').prod) h_add

private theorem iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ) :
    ∀ (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M),
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
      ∀ g ∈ iteratedSieveCorrectionPiecesOnList f L hL,
        g ∈ modFormCharSpace k
              (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod)))
  | [], _ => by
      intro g hg
      rw [iteratedSieveCorrectionPiecesOnList_nil] at hg
      simp at hg
  | p₀ :: L', hL' => by
      intro g hg
      set hL'_props : ∀ p ∈ L', p.Prime ∧ p ∣ M := consTail_prime_dvd hL'
      set hp₀_prime_M : p₀.Prime ∧ p₀ ∣ M := consHead_prime_dvd hL'
      haveI hM_prev_ne : NeZero (M * L'.prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'_props
      haveI : NeZero p₀ := ⟨hp₀_prime_M.1.ne_zero⟩
      haveI hM_full_ne : NeZero (M * (p₀ :: L').prod) :=
        neZero_mul_list_prod_of_prime_dvd hL'
      haveI hp₀M'_ne : NeZero (p₀ * (M * L'.prod)) :=
        ⟨Nat.mul_ne_zero (NeZero.ne p₀) (NeZero.ne (M * L'.prod))⟩
      have hp₀_not_coprime : ¬ Nat.Coprime p₀ (M * L'.prod) :=
        consPrime_not_coprime hp₀_prime_M
      have h_le := consGamma1_le p₀ M L'
      have hM_eq := consLevel_eq p₀ M L'
      have hdvd_prev : M ∣ M * L'.prod := Nat.dvd_mul_right M L'.prod
      have h_mp_dvd : (M * L'.prod) ∣ p₀ * (M * L'.prod) := ⟨p₀, by ring⟩
      have hdvd_inner : M ∣ p₀ * (M * L'.prod) := hdvd_prev.trans h_mp_dvd
      rw [iteratedSieveCorrectionPiecesOnList_cons f p₀ L' hL',
          List.mem_append] at hg
      rcases hg with hg_mapped | hg_last
      · rw [List.mem_map] at hg_mapped
        obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := hg_mapped
        have hIH := iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace
          f hf_χ L' hL'_props g₀ hg₀_mem
        rw [← hg₀_eq]
        exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
          (Nat.dvd_mul_right M (p₀ :: L').prod)
          (restrictSubgroup_mem_modFormCharSpace_comp χ hdvd_prev h_mp_dvd hdvd_inner h_le hIH)
      · rw [List.mem_singleton] at hg_last
        have hIH_w := iteratedSieveWitnessOnList_mem_modFormCharSpace
          f hf_χ L' hL'_props
        rw [hg_last]
        exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq hdvd_inner
          (Nat.dvd_mul_right M (p₀ :: L').prod)
          (levelRaise_heckeT_mem_modFormCharSpace_comp hp₀_prime_M.1 hp₀_not_coprime χ
            hdvd_prev hdvd_inner hIH_w)

/-- Nebentypus-aware strengthening of
`exists_oldform_pieces_decomposition_of_coprime_prod_vanish`: the deep
restriction of `f` is the `List.sum` of modular forms each lying in the
deep-level character space and each an oldform image at depth. -/
theorem exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
      (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
    ∃ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
          @IsOldformImageAtDeep M _ k f (M * L.prod)
            (⟨Nat.mul_ne_zero (NeZero.ne M)
              (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩) g := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  exact ⟨iteratedSieveCorrectionPiecesOnList f L hL,
    restrictSubgroup_eq_sum_oldform_pieces_of_coprime_prod_vanish f L hL h_vanish h_le_full,
    restrictSubgroup_mem_modFormCharSpace χ (Nat.dvd_mul_right M L.prod) f hf_χ,
    fun g hg ↦
      ⟨iteratedSieveCorrectionPiecesOnList_forall_mem_modFormCharSpace f hf_χ L hL g hg,
        iteratedSieveCorrectionPiecesOnList_forall_mem_isOldformImage f L hL g hg⟩⟩

private lemma IsOldformImageAtDeep.exists_prime_qExpansion_support
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (Mfull : ℕ) [NeZero Mfull]
    {g : ModularForm ((Gamma1 Mfull).map (mapGL ℝ)) k}
    (hg : IsOldformImageAtDeep f Mfull g) :
    ∃ p : ℕ, p.Prime ∧
      ∀ n : ℕ, ¬ p ∣ n → (qExpansion (1 : ℝ) ⇑g).coeff n = 0 := by
  obtain ⟨p, Lprev, _hLprev, hpNe, hMLprevNe, hp, _hpM', h_le', hg_eq⟩ := hg
  refine ⟨p, hp, ?_⟩
  intro n hn
  rw [hg_eq]
  show (qExpansion (1 : ℝ)
      (ModularForm.restrictSubgroup h_le'
        (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
          (HeckeRing.GL2.heckeT_p_divN k p hp _hpM'
            (iteratedSieveWitnessOnList f Lprev _hLprev))))).coeff n = 0
  change (qExpansion (1 : ℝ)
      (HeckeRing.GL2.modularFormLevelRaise (M * Lprev.prod) p k
        (HeckeRing.GL2.heckeT_p_divN k p hp _hpM'
          (iteratedSieveWitnessOnList f Lprev _hLprev)))).coeff n = 0
  rw [qExpansion_one_modularFormLevelRaise_coeff, if_neg hn]

/-- Strengthening of
`exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish` that
additionally attaches to each piece an explicit prime `p` and a witness
that the piece's period-1 Fourier coefficients vanish off multiples of `p`. -/
theorem exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
      (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
    ∃ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M L.prod))) ∧
          (@IsOldformImageAtDeep M _ k f (M * L.prod)
            (⟨Nat.mul_ne_zero (NeZero.ne M)
              (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩) g) ∧
          ∃ p : ℕ, p.Prime ∧
            ∀ n : ℕ, ¬ p ∣ n →
              (qExpansion (1 : ℝ) ⇑g).coeff n = 0 := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  refine ⟨pieces, h_sum, h_restr_char, fun g hg ↦ ?_⟩
  obtain ⟨h_char, h_old⟩ := h_pieces g hg
  exact ⟨h_char, h_old, IsOldformImageAtDeep.exists_prime_qExpansion_support
    f (M * L.prod) h_old⟩

/-- Same-level collapse of deep oldform image (bridge form).  Given the
coprime-to-`L.prod` Fourier vanishing hypothesis and an explicit bridge
hypothesis `h_bridge` converting the deep-level pieces into a same-level
divisor-indexed family at `Γ₁(M)` summing to `f`, conclude the same-level
divisor decomposition. -/
theorem same_level_collapse_of_deep_oldform_image
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (h_bridge :
      haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
        (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
      ∀ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
        ModularForm.restrictSubgroup h_le_full f = pieces.sum →
        (∀ g ∈ pieces, ∃ p : ℕ, p.Prime ∧
          ∀ n : ℕ, ¬ p ∣ n → (qExpansion (1 : ℝ) ⇑g).coeff n = 0) →
        ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
          f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
          (∀ d ∈ M.divisors.filter (1 < ·),
            samePiece d ∈ modFormCharSpace k χ ∧
            ∀ n : ℕ, ¬ d ∣ n →
              (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0)) :
    ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        samePiece d ∈ modFormCharSpace k χ ∧
        ∀ n : ℕ, ¬ d ∣ n →
          (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, _h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  exact h_bridge pieces h_sum fun g hg ↦ (h_pieces g hg).2.2

/-- A bundle of same-level divisor projections at level `Γ₁(M)` for a fixed
target form `f`, a prime-list `L` of primes dividing `M`, and the level
inclusion `Γ₁(M·L.prod) ≤ Γ₁(M)`.  Given deep-level pieces summing to
`restrictSubgroup h_le_full f` with prime q-support certificates, it
produces a same-level divisor-indexed family `samePiece : ℕ → ModularForm
Γ₁(M) k`. -/
@[ext]
structure ModularFormSameLevelDivisorProjections
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (_hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) where
  /-- Same-level collapse data: from deep pieces with prime q-supports
  summing to `restrictSubgroup h_le_full f`, produce a divisor-indexed
  same-level family with the per-divisor q-support, character-space
  membership, and per-piece cusp-vanishing at every cusp of `Γ₁(M)`,
  summing to `f`. -/
  collapse :
    haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
      (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
    ∀ pieces : List (ModularForm ((Gamma1 (M * L.prod)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum →
      (∀ g ∈ pieces, ∃ p : ℕ, p.Prime ∧
        ∀ n : ℕ, ¬ p ∣ n → (qExpansion (1 : ℝ) ⇑g).coeff n = 0) →
      ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
        f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
        (∀ d ∈ M.divisors.filter (1 < ·),
          samePiece d ∈ modFormCharSpace k χ ∧
          ∀ n : ℕ, ¬ d ∣ n →
            (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) ∧
        (∀ d ∈ M.divisors.filter (1 < ·),
          ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 M).map (mapGL ℝ)) →
            c.IsZeroAt (samePiece d).toFun k)

/-- Same-level collapse in structure form: given a
`ModularFormSameLevelDivisorProjections` bundle and the coprime-vanishing
hypothesis, produce the same-level divisor decomposition of `f`.  A
`_bridge`-free reformulation of `same_level_collapse_of_deep_oldform_image`. -/
theorem same_level_collapse_of_deep_oldform_image_of_projections
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (proj : ModularFormSameLevelDivisorProjections f hf_χ L hL h_le_full) :
    ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        samePiece d ∈ modFormCharSpace k χ ∧
        ∀ n : ℕ, ¬ d ∣ n →
          (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 M).map (mapGL ℝ)) →
          c.IsZeroAt (samePiece d).toFun k) := by
  haveI : NeZero (M * L.prod) := ⟨Nat.mul_ne_zero (NeZero.ne M)
    (List.prod_pos (fun p hp ↦ (hL p hp).1.pos)).ne'⟩
  obtain ⟨pieces, h_sum, _h_restr_char, h_pieces⟩ :=
    exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
      f hf_χ L hL h_vanish h_le_full
  exact proj.collapse pieces h_sum fun g hg ↦ (h_pieces g hg).2.2

/-- Recursive Miyake-sieve witness on `Finset ℕ`, the Finset analogue of
`iteratedSieveWitnessOnList` (delegating to it on `S.toList`). -/
noncomputable def iteratedSieveWitness
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k :=
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  (show M * S.toList.prod = M * ∏ p ∈ S, p by rw [Finset.prod_toList]) ▸
    iteratedSieveWitnessOnList f S.toList
      (fun p hp ↦ hS p (Finset.mem_toList.mp hp))

/-- Coefficient identity for `iteratedSieveWitness`: its period-1 Fourier
coefficient is the `S`-prime-set sieve of `f`'s coefficient. -/
theorem qExpansion_iteratedSieveWitness_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) (n : ℕ) :
    (qExpansion (1 : ℝ) (iteratedSieveWitness f S hS)).coeff n =
      (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n) := by
  unfold iteratedSieveWitness
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  rw [qExpansion_coeff_cast_Gamma1
      (show M * S.toList.prod = M * ∏ p ∈ S, p by rw [Finset.prod_toList]) _ n,
    iteratedSieveWitnessOnList_qExpansion_coeff f S.toList _ n]
  simp [Finset.mem_toList]

/-- Insert-step coefficient identity for `iteratedSieveWitness`: at
`insert p₀ S`, the period-1 Fourier coefficient at `n` collapses to `0`
when `p₀ ∣ n`, and otherwise agrees with the witness for `S` at `n`. -/
theorem qExpansion_iteratedSieveWitness_insert_coeff
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (p₀ : ℕ) (_hp₀ : p₀ ∉ S)
    (hS : ∀ p ∈ insert p₀ S, p.Prime ∧ p ∣ M) (n : ℕ) :
    (qExpansion (1 : ℝ)
        (iteratedSieveWitness f (insert p₀ S) hS)).coeff n =
      (if p₀ ∣ n then 0
        else (qExpansion (1 : ℝ)
          (iteratedSieveWitness f S
            (fun p hp ↦ hS p (Finset.mem_insert_of_mem hp)))).coeff n) := by
  rw [qExpansion_iteratedSieveWitness_coeff, qExpansion_iteratedSieveWitness_coeff]
  split_ifs with hn_p₀ h_ex hn_S h_nex <;> simp_all [Finset.mem_insert]

/-- Under coprime-to-`∏ p ∈ S, p` Fourier vanishing of `f`, the named
Finset witness `iteratedSieveWitness f S hS` equals the zero modular form. -/
theorem iteratedSieveWitness_eq_zero_of_coprime_prod_vanish
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0) :
    haveI hL_pos : 0 < S.toList.prod :=
      List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
    haveI : NeZero (M * ∏ p ∈ S, p) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (by
        rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
    iteratedSieveWitness f S hS = 0 := by
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI hML_ne : NeZero (M * ∏ p ∈ S, p) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) (by
      rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
  refine (qExpansion_one_Gamma1_eq_zero_iff
    (iteratedSieveWitness f S hS)).mp ?_
  ext n
  rw [qExpansion_iteratedSieveWitness_coeff f S hS n]
  by_cases hdiv : ∃ p ∈ S, p ∣ n
  · rw [if_pos hdiv]; simp
  · rw [if_neg hdiv]
    have hcop : Nat.Coprime n (∏ p ∈ S, p) := by
      rw [show (∏ p ∈ S, p) = S.toList.prod from (Finset.prod_toList S).symm,
        Nat.coprime_list_prod_right_iff]
      intro p hpL
      have hpS : p ∈ S := Finset.mem_toList.mp hpL
      exact ((hS p hpS).1.coprime_iff_not_dvd.mpr
        (fun hpn ↦ hdiv ⟨p, hpS, hpn⟩)).symm
    rw [h_vanish n hcop]; simp

/-- The named Finset witness `iteratedSieveWitness f S hS` lies in
`modFormCharSpace k (χ.comp (ZMod.unitsMap (M ∣ M · ∏ S)))`. -/
theorem iteratedSieveWitness_mem_modFormCharSpace
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    haveI hL_pos : 0 < S.toList.prod :=
      List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
    haveI : NeZero (M * ∏ p ∈ S, p) :=
      ⟨Nat.mul_ne_zero (NeZero.ne M) (by
        rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
    iteratedSieveWitness f S hS ∈
      modFormCharSpace k
        (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) := by
  haveI hL_pos : 0 < S.toList.prod :=
    List.prod_pos (fun p hp ↦ (hS p (Finset.mem_toList.mp hp)).1.pos)
  haveI hML_ne_list : NeZero (M * S.toList.prod) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) hL_pos.ne'⟩
  haveI hML_ne : NeZero (M * ∏ p ∈ S, p) :=
    ⟨Nat.mul_ne_zero (NeZero.ne M) (by
      rw [← Finset.prod_toList]; exact hL_pos.ne')⟩
  have hIH := iteratedSieveWitnessOnList_mem_modFormCharSpace
    f hf_χ S.toList (fun p hp ↦ hS p (Finset.mem_toList.mp hp))
  have hM_eq : M * S.toList.prod = M * ∏ p ∈ S, p := by rw [Finset.prod_toList]
  unfold iteratedSieveWitness
  exact cast_mem_modFormCharSpace_Gamma1 χ hM_eq
    (Nat.dvd_mul_right M S.toList.prod)
    (Nat.dvd_mul_right M (∏ p ∈ S, p)) hIH

/-- Named-witness restatement of the coefficient identity for the explicit witness
`iteratedSieveWitness f S hS`, eliminating the existential `g`. -/
theorem qExpansion_iteratedSieveWitness_coeff_sieve
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M) :
    ∀ n : ℕ, (qExpansion (1 : ℝ) (iteratedSieveWitness f S hS)).coeff n =
      (if ∃ p ∈ S, p ∣ n then 0 else (qExpansion (1 : ℝ) ⇑f).coeff n) :=
  qExpansion_iteratedSieveWitness_coeff f S hS

/-- Finset wrapper for
`exists_oldform_pieces_decomposition_of_coprime_prod_vanish`, phrasing the
depth product as `∏ p ∈ S, p`. -/
theorem exists_oldform_pieces_decomposition_of_coprime_prod_vanish_finset
    {M : ℕ} [NeZero M] {k : ℤ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    [hNZ : NeZero (M * ∏ p ∈ S, p)]
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ∀ g ∈ pieces, IsOldformImageAtDeep f (M * ∏ p ∈ S, p) g := by
  generalize hQ : (∏ p ∈ S, p) = Q at hNZ h_vanish h_le_full ⊢
  have hprod : S.toList.prod = Q := hQ ▸ Finset.prod_toList S
  subst hprod
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_of_coprime_prod_vanish
    f S.toList hL h_vanish h_le_full

/-- Finset wrapper for
`exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish`. -/
theorem exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish_finset
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    [hNZ : NeZero (M * ∏ p ∈ S, p)]
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
          IsOldformImageAtDeep f (M * ∏ p ∈ S, p) g := by
  generalize hQ : (∏ p ∈ S, p) = Q at hNZ h_vanish h_le_full ⊢
  have hprod : S.toList.prod = Q := hQ ▸ Finset.prod_toList S
  subst hprod
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_charSpace_of_coprime_prod_vanish
    f hf_χ S.toList hL h_vanish h_le_full

/-- Finset wrapper for
`exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish`
(Nebentypus-aware, prime-q-support tagged). -/
theorem exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish_finset
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    [hNZ : NeZero (M * ∏ p ∈ S, p)]
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ)) :
    ∃ pieces : List (ModularForm ((Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ)) k),
      ModularForm.restrictSubgroup h_le_full f = pieces.sum ∧
        ModularForm.restrictSubgroup h_le_full f ∈
          modFormCharSpace k
            (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
        ∀ g ∈ pieces,
          g ∈ modFormCharSpace k
                (χ.comp (ZMod.unitsMap (Nat.dvd_mul_right M (∏ p ∈ S, p)))) ∧
          IsOldformImageAtDeep f (M * ∏ p ∈ S, p) g ∧
          ∃ p : ℕ, p.Prime ∧
            ∀ n : ℕ, ¬ p ∣ n →
              (qExpansion (1 : ℝ) ⇑g).coeff n = 0 := by
  generalize hQ : (∏ p ∈ S, p) = Q at hNZ h_vanish h_le_full ⊢
  have hprod : S.toList.prod = Q := hQ ▸ Finset.prod_toList S
  subst hprod
  have hL : ∀ p ∈ S.toList, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  exact exists_oldform_pieces_decomposition_charSpace_qSupp_of_coprime_prod_vanish
    f hf_χ S.toList hL h_vanish h_le_full

/-- Finset wrapper for
`same_level_collapse_of_deep_oldform_image_of_projections`, taking the
projection bundle phrased on `L := S.toList`. -/
theorem same_level_collapse_of_deep_oldform_image_of_projections_finset
    {M : ℕ} [NeZero M] {k : ℤ} {χ : (ZMod M)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hf_χ : f ∈ modFormCharSpace k χ)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ∣ M)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (∏ p ∈ S, p) →
      (qExpansion (1 : ℝ) ⇑f).coeff n = 0)
    (h_le_full : (Gamma1 (M * ∏ p ∈ S, p)).map (mapGL ℝ) ≤
      (Gamma1 M).map (mapGL ℝ))
    (proj : ModularFormSameLevelDivisorProjections f hf_χ S.toList
      (fun p hp ↦ hS p (Finset.mem_toList.mp hp))
      ((Finset.prod_toList S).symm ▸ h_le_full)) :
    ∃ samePiece : ℕ → ModularForm ((Gamma1 M).map (mapGL ℝ)) k,
      f = ∑ d ∈ M.divisors.filter (1 < ·), samePiece d ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        samePiece d ∈ modFormCharSpace k χ ∧
        ∀ n : ℕ, ¬ d ∣ n →
          (qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0) ∧
      (∀ d ∈ M.divisors.filter (1 < ·),
        ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 M).map (mapGL ℝ)) →
          c.IsZeroAt (samePiece d).toFun k) := by
  have hprod : S.toList.prod = ∏ p ∈ S, p := Finset.prod_toList S
  set L : List ℕ := S.toList
  have hL : ∀ p ∈ L, p.Prime ∧ p ∣ M := fun p hp ↦
    hS p (Finset.mem_toList.mp hp)
  exact same_level_collapse_of_deep_oldform_image_of_projections f hf_χ L hL
    (fun n hn ↦ h_vanish n (hprod ▸ hn)) (hprod ▸ h_le_full) proj

end HeckeRing.GL2.MainLemma
