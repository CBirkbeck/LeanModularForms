/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.Eigenforms.MainLemma
import LeanModularForms.HeckeRIngs.GL2.HeckeT_n
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Atkin-Lehner same-level `p`-supported projection API

This file develops the Atkin-Lehner projection API for `Newforms.mainLemma`: any cusp
form `f ∈ S_k(Γ₁(N))` whose Fourier coefficients vanish at every index coprime to `N`
is an oldform.  The framework captures "support on multiples of `d`":

* `IsSupportedOnDvd d P` — the power-series support predicate, with its algebraic
  closure lemmas.
* `QExpansionSupportedOnDvd d f` and `qSupportedOnDvdSubmodule N k d` — the same
  condition on the canonical period-1 `q`-expansion of a cusp form, packaged as a
  submodule.
* `qExpansion_levelRaise_isSupportedOnDvd` / `levelRaise_mem_qSupportedOnDvdSubmodule` —
  the forward direction: level-raise images are supported on multiples of `d`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.7.
* Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970).
* Miyake, *Modular Forms*, §4.6.
-/

open scoped ModularForm
open ModularFormClass CongruenceSubgroup Matrix.SpecialLinearGroup

namespace HeckeRing.GL2.AtkinLehner

/-- A power series is **supported on multiples of `d`** if its
coefficient at every index not divisible by `d` is zero. -/
def IsSupportedOnDvd (d : ℕ) (P : PowerSeries ℂ) : Prop :=
  ∀ n : ℕ, ¬ d ∣ n → (PowerSeries.coeff n) P = 0

namespace IsSupportedOnDvd

@[simp] lemma zero (d : ℕ) : IsSupportedOnDvd d (0 : PowerSeries ℂ) := by
  intro n _
  simp

lemma add {d : ℕ} {P Q : PowerSeries ℂ}
    (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P + Q) := by
  intro n hn
  rw [map_add, hP n hn, hQ n hn, zero_add]

lemma smul {d : ℕ} (c : ℂ) {P : PowerSeries ℂ} (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (c • P) := by
  intro n hn
  rw [show (PowerSeries.coeff n) (c • P) = c * (PowerSeries.coeff n) P by
    simp [smul_eq_mul], hP n hn, mul_zero]

lemma neg {d : ℕ} {P : PowerSeries ℂ} (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (-P) := by
  intro n hn
  rw [map_neg, hP n hn, neg_zero]

lemma sub {d : ℕ} {P Q : PowerSeries ℂ}
    (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P - Q) := by
  rw [sub_eq_add_neg]
  exact hP.add hQ.neg

/-- The constant power series `1 : PowerSeries ℂ` is supported on multiples of any `d`. -/
lemma one (d : ℕ) : IsSupportedOnDvd d (1 : PowerSeries ℂ) := by
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact absurd (dvd_zero d) hn
  · rw [PowerSeries.coeff_one, if_neg hpos.ne']

end IsSupportedOnDvd

variable {N : ℕ} [NeZero N] {k : ℤ} {d : ℕ}

/-- A cusp form `f ∈ S_k(Γ₁(N))` is **q-supported on multiples of `d`**
if its canonical period-1 `q`-expansion is supported on multiples of
`d`. -/
def QExpansionSupportedOnDvd (d : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  IsSupportedOnDvd d (qExpansion (1 : ℝ) f)

omit [NeZero N] in
private lemma h1_period_Gamma1 :
    (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

/-- The submodule of cusp forms `f ∈ S_k(Γ₁(N))` whose canonical
period-1 `q`-expansion is supported on multiples of `d`. -/
noncomputable def qSupportedOnDvdSubmodule (N : ℕ) [NeZero N] (k : ℤ) (d : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  carrier := {f | QExpansionSupportedOnDvd d f}
  zero_mem' := by intro n _; simp [qExpansion_zero]
  add_mem' {f g} hf hg := by
    intro n hn
    have h_eq : qExpansion (1 : ℝ) (⇑(f + g) : UpperHalfPlane → ℂ) =
        qExpansion (1 : ℝ) ⇑f + qExpansion (1 : ℝ) ⇑g := by
      convert qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ)) (h := 1) (a := k) (b := k)
        one_pos h1_period_Gamma1 f g using 2
    show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(f + g)) = 0
    rw [h_eq, map_add, hf n hn, hg n hn, zero_add]
  smul_mem' c f hf := by
    intro n hn
    have h_eq : qExpansion (1 : ℝ) (⇑(c • f) : UpperHalfPlane → ℂ) =
        c • qExpansion (1 : ℝ) ⇑f := by
      convert qExpansion_smul (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (h := 1) one_pos
        h1_period_Gamma1 c f using 2
    show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(c • f)) = 0
    rw [h_eq, show (PowerSeries.coeff n) (c • qExpansion (1 : ℝ) ⇑f) =
      c * (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑f) by simp [smul_eq_mul],
      hf n hn, mul_zero]

@[simp] lemma mem_qSupportedOnDvdSubmodule
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ qSupportedOnDvdSubmodule N k d ↔ QExpansionSupportedOnDvd d f :=
  Iff.rfl

/-- Level-raise q-expansion forward direction (modular form): for
`g : ModularForm Γ₁(M) k`, the image `modularFormLevelRaise M d k g`
has period-1 `q`-expansion supported on multiples of `d`. -/
lemma qExpansion_modularFormLevelRaise_isSupportedOnDvd
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] {k : ℤ}
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d (qExpansion (1 : ℝ) (modularFormLevelRaise M d k g)) := by
  intro n hn
  rw [qExpansion_one_modularFormLevelRaise_coeff g n, if_neg hn]

/-- Level-raise q-expansion forward direction (cusp form): for any cusp form
`g : CuspForm Γ₁(M) k`, the level-raise `levelRaise M d k g` has period-1
`q`-expansion supported on multiples of `d`. -/
lemma qExpansion_levelRaise_isSupportedOnDvd
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] {k : ℤ}
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d (qExpansion (1 : ℝ) (levelRaise M d k g)) := by
  intro n hn
  let g_mf : ModularForm ((Gamma1 M).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := g.toSlashInvariantForm
      holo' := g.holo'
      bdd_at_cusps' := fun {c} hc γ hγ => (g.zero_at_cusps' hc γ hγ).isBoundedAtImInfty }
  have h_fun_eq :
      (⇑(levelRaise M d k g) : UpperHalfPlane → ℂ) =
        ⇑(modularFormLevelRaise M d k g_mf) := by
    rw [coe_modularFormLevelRaise]
    rfl
  rw [show (qExpansion (1 : ℝ) (levelRaise M d k g)) =
      qExpansion (1 : ℝ) (modularFormLevelRaise M d k g_mf) from
    qExpansion_ext2 _ _ h_fun_eq]
  exact qExpansion_modularFormLevelRaise_isSupportedOnDvd _ n hn

/-- Forward Atkin–Lehner correspondence (submodule form): any cusp form obtained by
level-raising lies in the `qSupportedOnDvdSubmodule`. -/
theorem levelRaise_mem_qSupportedOnDvdSubmodule
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d]
    (heq : d * M = N) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (heq ▸ levelRaise M d k g) ∈ qSupportedOnDvdSubmodule N k d := by
  subst heq
  show QExpansionSupportedOnDvd d (levelRaise M d k g)
  exact qExpansion_levelRaise_isSupportedOnDvd g

private lemma cuspForm_coe_eq_of_cast {M N : ℕ} {k : ℤ} (h : M = N)
    (x : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(h ▸ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) =
      ⇑x := by
  cases h
  rfl

private lemma isOldformGenerator_of_funeq
    {N d : ℕ} [NeZero d] (hd : 1 < d) (hdN : d ∣ N) [NeZero N] [NeZero (N / d)]
    {k : ℤ}
    (F : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_funeq : (⇑(levelRaise (N / d) d k F) : UpperHalfPlane → ℂ) = ⇑f) :
    IsOldformGenerator f := by
  have h_dvd_eq : d * (N / d) = N := Nat.mul_div_cancel' hdN
  refine ⟨N / d, d, ⟨NeZero.ne (N / d)⟩, ‹_›, hd, h_dvd_eq, F, ?_⟩
  apply DFunLike.coe_injective
  show (⇑(h_dvd_eq ▸ levelRaise (N / d) d k F :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) = ⇑f
  rwa [cuspForm_coe_eq_of_cast h_dvd_eq]

/-- Reverse Atkin-Lehner bridge (with Nebentypus character): a cusp form
`f ∈ S_k(Γ₁(N), χ)` whose period-1 `q`-expansion is supported on multiples of a
proper divisor `d` of `N` (`1 < d`, `d ∣ N`) is an oldform, `f ∈ cuspFormsOld N k`. -/
theorem qSupportedOnDvd_mem_cuspFormsOld_of_char
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (hfsupp : f ∈ qSupportedOnDvdSubmodule N k d) :
    f ∈ cuspFormsOld N k := by
  obtain ⟨φ, h_eq, h_period⟩ :=
    HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
      hd hdN f (fun n hn => hfsupp n hn)
  rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
      d N hdN k χ φ f hfχ h_eq h_period with
    ⟨_h_fac, F, _hF_char, hF_eq⟩ | h_zero
  · apply Submodule.subset_span
    have h_funeq : (⇑(levelRaise (N / d) d k F) : UpperHalfPlane → ℂ) = ⇑f := by
      show levelRaiseFun d k ⇑F = ⇑f
      rw [hF_eq, ← h_eq]
    exact isOldformGenerator_of_funeq hd hdN F f h_funeq
  · have h_f_zero : f = 0 := by
      apply DFunLike.coe_injective
      show (⇑f : UpperHalfPlane → ℂ) = 0
      rw [h_eq, h_zero]
      simp [levelRaiseFun]
    rw [h_f_zero]
    exact Submodule.zero_mem _

/-- Reverse Atkin-Lehner explicit preimage (character-space): for a cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` at level `Γ₁(N)` whose period-1 `q`-expansion is
supported on multiples of a proper divisor `d ∣ N` (`1 < d`), either `f` is the zero
form or `f` equals (as a function on `ℍ`) the level-raise of some cusp form at level
`Γ₁(N/d)`. -/
theorem qSupportedOnDvd_eq_zero_or_exists_levelRaise_preimage_of_char
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (hfsupp : f ∈ qSupportedOnDvdSubmodule N k d) :
    f = 0 ∨ ∃ (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k),
      (⇑(levelRaise (N / d) d k g) : UpperHalfPlane → ℂ) = ⇑f := by
  obtain ⟨φ, h_eq, h_period⟩ :=
    HeckeRing.GL2.exists_levelRaise_preimage_of_coeff_support_multiples
      hd hdN f (fun n hn => hfsupp n hn)
  rcases HeckeRing.GL2.conductor_theorem_dichotomy_cuspForm_strong
      d N hdN k χ φ f hfχ h_eq h_period with
    ⟨_h_fac, F, _hF_char, hF_eq⟩ | h_zero
  · right
    refine ⟨F, ?_⟩
    show levelRaiseFun d k ⇑F = ⇑f
    rw [hF_eq, ← h_eq]
  · left
    apply DFunLike.coe_injective
    show (⇑f : UpperHalfPlane → ℂ) = 0
    rw [h_eq, h_zero]
    simp [levelRaiseFun]

/-- Reverse Atkin-Lehner character-space iff: for a cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` at level `Γ₁(N)` and a proper divisor `d ∣ N`
(`1 < d`), `f` is supported on multiples of `d` iff `f = 0` or `f` equals (as a
function on `ℍ`) the level-raise of some cusp form at level `Γ₁(N/d)`. -/
theorem qSupportedOnDvdSubmodule_mem_iff_eq_zero_or_exists_levelRaise_preimage_of_char
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ qSupportedOnDvdSubmodule N k d ↔
      f = 0 ∨ ∃ (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k),
        (⇑(levelRaise (N / d) d k g) : UpperHalfPlane → ℂ) = ⇑f := by
  refine ⟨fun hfsupp =>
    qSupportedOnDvd_eq_zero_or_exists_levelRaise_preimage_of_char
      hd hdN χ f hfχ hfsupp, ?_⟩
  rintro (rfl | ⟨g, hg⟩)
  · exact Submodule.zero_mem _
  · have heq : d * (N / d) = N := Nat.mul_div_cancel' hdN
    have h_f_eq : f = heq ▸ levelRaise (N / d) d k g := by
      apply DFunLike.coe_injective
      show (⇑f : UpperHalfPlane → ℂ) =
        ⇑(heq ▸ levelRaise (N / d) d k g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      rw [cuspForm_coe_eq_of_cast heq]
      exact hg.symm
    rw [h_f_eq]
    exact levelRaise_mem_qSupportedOnDvdSubmodule heq g

/-- Reverse Atkin-Lehner character-space iff, single existential: under the
character-space/proper-divisor hypotheses, `f` is supported on multiples of `d` iff `f`
equals (as a function on `ℍ`) the level-raise of some cusp form at level `Γ₁(N/d)`. -/
theorem qSupportedOnDvdSubmodule_mem_iff_exists_levelRaise_preimage_of_char
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ qSupportedOnDvdSubmodule N k d ↔
      ∃ (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k),
        (⇑(levelRaise (N / d) d k g) : UpperHalfPlane → ℂ) = ⇑f := by
  rw [qSupportedOnDvdSubmodule_mem_iff_eq_zero_or_exists_levelRaise_preimage_of_char
      hd hdN χ f hfχ]
  refine ⟨?_, fun ⟨g, hg⟩ => Or.inr ⟨g, hg⟩⟩
  rintro (rfl | ⟨g, hg⟩)
  · exact ⟨0, by simp⟩
  · exact ⟨g, hg⟩

/-- Reverse Atkin-Lehner character-space iff, CuspForm-transported: the
single-existential iff upgraded through the cast `heq : d * (N/d) = N`, so `f` is
supported on multiples of `d` iff `f` equals (as a cusp form at level `Γ₁(N)`) the cast
`heq ▸ levelRaise (N/d) d k g` of some lower-level cusp form `g`. -/
theorem qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ qSupportedOnDvdSubmodule N k d ↔
      ∃ (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k),
        f = (Nat.mul_div_cancel' hdN) ▸ levelRaise (N / d) d k g := by
  rw [qSupportedOnDvdSubmodule_mem_iff_exists_levelRaise_preimage_of_char
      hd hdN χ f hfχ]
  have heq : d * (N / d) = N := Nat.mul_div_cancel' hdN
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply DFunLike.coe_injective
    show (⇑f : UpperHalfPlane → ℂ) =
      ⇑(heq ▸ levelRaise (N / d) d k g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    rw [cuspForm_coe_eq_of_cast heq]
    exact hg.symm
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    rw [hg, cuspForm_coe_eq_of_cast heq]

/-- Submodule-level forward bridge: the `heq`-cast of every level-raise image lies in
`qSupportedOnDvdSubmodule N k d`. -/
theorem cast_levelRaise_mem_qSupportedOnDvdSubmodule
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hdN : d ∣ N) {k : ℤ}
    (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k) :
    ((Nat.mul_div_cancel' hdN) ▸ levelRaise (N / d) d k g :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      qSupportedOnDvdSubmodule N k d :=
  levelRaise_mem_qSupportedOnDvdSubmodule (Nat.mul_div_cancel' hdN) g

/-- Submodule-level intersection bridge: under the character hypothesis `hfχ`, `f` sits
in `qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom` iff `f` is the cast
of a level-raise of some `g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k`. -/
theorem mem_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_iff_exists_cuspForm_levelRaise_preimage_of_char
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom ↔
      ∃ (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k),
        f = (Nat.mul_div_cancel' hdN) ▸ levelRaise (N / d) d k g := by
  rw [Submodule.mem_inf]
  constructor
  · rintro ⟨hsup, _⟩
    exact
      (qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char
        hd hdN χ f hfχ).mp hsup
  · intro h
    refine ⟨?_, hfχ⟩
    exact
      (qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char
        hd hdN χ f hfχ).mpr h

/-- For `h : M = N` a type-level equality of levels, the identity cast `(h ▸ ·)` is a
`ℂ`-linear equivalence between the two CuspForm spaces. -/
def castCuspFormLinearEquiv {M N : ℕ} (h : M = N) (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k ≃ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun x := (h ▸ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  invFun x := (h.symm ▸ x : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
  map_add' x y := by subst h; rfl
  map_smul' c x := by subst h; rfl
  left_inv x := by subst h; rfl
  right_inv x := by subst h; rfl

@[simp] lemma castCuspFormLinearEquiv_apply {M N : ℕ} (h : M = N) (k : ℤ)
    (x : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    castCuspFormLinearEquiv h k x =
      (h ▸ x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- The Atkin-Lehner level-raise operator packaged at the same-level target `Γ₁(N)`:
the composition of `levelRaise (N/d) d k` with `castCuspFormLinearEquiv`. -/
noncomputable def castLevelRaise (N : ℕ) [NeZero N] (d : ℕ) [NeZero d]
    [NeZero (N / d)] (hdN : d ∣ N) (k : ℤ) :
    CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (castCuspFormLinearEquiv (Nat.mul_div_cancel' hdN) k).toLinearMap.comp
    (levelRaise (N / d) d k)

@[simp] lemma castLevelRaise_apply {N : ℕ} [NeZero N] {d : ℕ} [NeZero d]
    [NeZero (N / d)] (hdN : d ∣ N) (k : ℤ)
    (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k) :
    castLevelRaise N d hdN k g =
      ((Nat.mul_div_cancel' hdN) ▸ levelRaise (N / d) d k g :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl

/-- Every image of `castLevelRaise` at level `Γ₁(N)` lies in
`qSupportedOnDvdSubmodule N k d`. -/
theorem range_castLevelRaise_le_qSupportedOnDvdSubmodule
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] [NeZero (N / d)]
    (hdN : d ∣ N) (k : ℤ) :
    LinearMap.range (castLevelRaise N d hdN k) ≤
      qSupportedOnDvdSubmodule N k d := by
  rintro _ ⟨g, rfl⟩
  rw [castLevelRaise_apply]
  exact cast_levelRaise_mem_qSupportedOnDvdSubmodule hdN g

/-- Character-space Atkin-Lehner identification at the `Submodule` level: the range of
`castLevelRaise`, intersected with the Nebentypus character space, equals
`qSupportedOnDvdSubmodule N k d` intersected with the character space. -/
theorem range_castLevelRaise_inf_cuspFormCharSpace_eq_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (χ : DirichletCharacter ℂ N) :
    LinearMap.range (castLevelRaise N d hdN k) ⊓
        cuspFormCharSpace k χ.toUnitHom =
      qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom := by
  ext f
  rw [Submodule.mem_inf, Submodule.mem_inf]
  refine ⟨fun ⟨hrange, hchar⟩ => ⟨?_, hchar⟩,
          fun ⟨hsup, hchar⟩ => ⟨?_, hchar⟩⟩
  · exact range_castLevelRaise_le_qSupportedOnDvdSubmodule hdN k hrange
  · obtain ⟨g, hg⟩ :=
      (mem_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_iff_exists_cuspForm_levelRaise_preimage_of_char
        hd hdN χ f hchar).mp ⟨hsup, hchar⟩
    exact ⟨g, by rw [castLevelRaise_apply]; exact hg.symm⟩

/-- Character-decomposition reverse bridge: if a cusp form `f : CuspForm Γ₁(N) k`
decomposes as a finite sum `f = ∑ χ ∈ S, f_χ χ` with each summand `f_χ χ` lying in
`qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom`, then `f` admits an
explicit level-raise preimage `g : CuspForm Γ₁(N/d) k` with
`f = castLevelRaise N d hdN k g`. -/
theorem exists_cuspForm_levelRaise_preimage_of_qSupported_of_char_decomposition
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hd : 1 < d) (hdN : d ∣ N) {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (S : Finset (DirichletCharacter ℂ N))
    (f_χ : DirichletCharacter ℂ N → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_mem : ∀ χ ∈ S, f_χ χ ∈
      qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom)
    (h_decomp : f = ∑ χ ∈ S, f_χ χ) :
    ∃ g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k,
      f = castLevelRaise N d hdN k g := by
  have h_per_χ : ∀ χ ∈ S, ∃ g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k,
      f_χ χ = castLevelRaise N d hdN k g := by
    intro χ hχ
    obtain ⟨hsupp, hchar⟩ := Submodule.mem_inf.mp (h_mem χ hχ)
    obtain ⟨g, hg⟩ :=
      (qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char
        hd hdN χ (f_χ χ) hchar).mp hsupp
    exact ⟨g, by rw [castLevelRaise_apply]; exact hg⟩
  choose g_χ hg_χ using h_per_χ
  refine ⟨∑ χ ∈ S.attach, g_χ χ.val χ.property, ?_⟩
  rw [map_sum, h_decomp, ← Finset.sum_attach S (fun χ => f_χ χ)]
  exact Finset.sum_congr rfl (fun χ _ => hg_χ χ.val χ.property)

/-- Character-space mainLemma at prime-power level: for `N = p^r` with `p` prime and
`r ≥ 1`, a cusp form `f ∈ S_k(Γ₁(p^r), χ)` whose Fourier coefficients vanish at every
index coprime to `p^r` is an oldform, `f ∈ cuspFormsOld (p^r) k`. -/
theorem mainLemma_charSpace_primePower
    {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 0 < r) {k : ℤ}
    (χ : DirichletCharacter ℂ (p ^ r))
    (f : CuspForm ((Gamma1 (p ^ r)).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h : ∀ n : ℕ, Nat.Coprime n (p ^ r) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld (p ^ r) k := by
  have hp_prime : p.Prime := hp.out
  have h_pr : p ^ r = p ^ (r - 1) * p := by
    conv_lhs => rw [show r = (r - 1) + 1 from (Nat.sub_add_cancel hr).symm]
    rw [pow_succ]
  have h_div_eq : p ^ r / p = p ^ (r - 1) := by
    rw [h_pr, Nat.mul_div_cancel _ hp_prime.pos]
  haveI : NeZero (p ^ r / p) := by
    rw [h_div_eq]; exact ⟨pow_ne_zero _ hp_prime.ne_zero⟩
  have h_supp : f ∈ qSupportedOnDvdSubmodule (p ^ r) k p := by
    intro n hn
    apply h
    rw [Nat.coprime_pow_right_iff hr]
    exact ((hp_prime.coprime_iff_not_dvd).mpr hn).symm
  exact qSupportedOnDvd_mem_cuspFormsOld_of_char hp_prime.one_lt
    (dvd_pow_self p hr.ne') χ f hfχ h_supp

/-- Composite-level mainLemma from a prime-supported decomposition: if
`f : CuspForm Γ₁(N) k` decomposes as `f = ∑ p ∈ S, f_p p` with `S ⊆ N.primeFactors` and
each `f_p p` simultaneously in `cuspFormCharSpace k χ` and `qSupportedOnDvdSubmodule N k p`,
then `f ∈ cuspFormsOld N k`. -/
theorem mainLemma_charSpace_of_prime_decomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : S ⊆ N.primeFactors)
    (f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_decomp : f = ∑ p ∈ S, f_p p)
    (h_char : ∀ p ∈ S, f_p p ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_supp : ∀ p ∈ S, f_p p ∈ qSupportedOnDvdSubmodule N k p) :
    f ∈ cuspFormsOld N k := by
  rw [h_decomp]
  refine Submodule.sum_mem _ (fun p hp => ?_)
  have hp_pf := hS hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_pf
  have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_pf
  haveI : NeZero p := ⟨hp_prime.ne_zero⟩
  haveI : NeZero (N / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hpN) hp_prime.pos).ne'⟩
  exact qSupportedOnDvd_mem_cuspFormsOld_of_char hp_prime.one_lt hpN χ
    (f_p p) (h_char p hp) (h_supp p hp)

/-- Composite-level mainLemma at the full set of prime divisors: any cusp form `f` that
decomposes as `f = ∑ p ∈ N.primeFactors, f_p p` with each `f_p` in the character space
and `p`-supported is an oldform. -/
theorem mainLemma_charSpace_of_primeFactors_decomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (f_p : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_decomp : f = ∑ p ∈ N.primeFactors, f_p p)
    (h_char : ∀ p ∈ N.primeFactors, f_p p ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_supp : ∀ p ∈ N.primeFactors, f_p p ∈ qSupportedOnDvdSubmodule N k p) :
    f ∈ cuspFormsOld N k :=
  mainLemma_charSpace_of_prime_decomposition χ f N.primeFactors subset_rfl
    f_p h_decomp h_char h_supp

/-- **Higher-level `p`-supported projection.**  The composition
`V_p ∘ U_p` at modular-form level, mapping
`ModularForm Γ₁(N) k →ₗ[ℂ] ModularForm Γ₁(p · N) k`. -/
noncomputable def pSupportedRaise {N : ℕ} [NeZero N] (k : ℤ)
    (p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
  (HeckeRing.GL2.modularFormLevelRaise N p k).comp
    (HeckeRing.GL2.heckeT_p_divN k p hp hpN)

/-- `q`-expansion formula for `pSupportedRaise`: at period 1,
`a_n(pSupportedRaise f) = a_n(f)` if `p ∣ n`, else `0`. -/
theorem qExpansion_one_pSupportedRaise_coeff {N : ℕ} [NeZero N] {k : ℤ}
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) (n : ℕ) :
    (qExpansion (1 : ℝ) (pSupportedRaise k p hp hpN f)).coeff n =
      if p ∣ n then (qExpansion (1 : ℝ) f).coeff n else 0 := by
  show (qExpansion (1 : ℝ) (HeckeRing.GL2.modularFormLevelRaise N p k
    (HeckeRing.GL2.heckeT_p_divN k p hp hpN f))).coeff n = _
  rw [HeckeRing.GL2.qExpansion_one_modularFormLevelRaise_coeff]
  split_ifs with h
  · rw [HeckeRing.GL2.qExpansion_one_heckeT_p_divN_coeff hp hpN f (n / p),
      Nat.mul_div_cancel' h]
  · rfl

/-- Character-space preservation for `pSupportedRaise`: if `f` lies in the Nebentypus
space `M_k(Γ₁(N), χ)`, then `pSupportedRaise k p hp hpN f` lies in
`M_k(Γ₁(p · N), χ.comp (ZMod.unitsMap (N ∣ p · N)))`, the natural lift of `χ` to level
`p · N`. -/
theorem pSupportedRaise_mem_modFormCharSpace {N : ℕ} [NeZero N] {k : ℤ}
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    pSupportedRaise k p hp hpN f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) :=
  HeckeRing.GL2.MainLemma.modularFormLevelRaise_mem_modFormCharSpace N p k χ
    (HeckeRing.GL2.MainLemma.heckeT_p_divN_preserves_modFormCharSpace hp hpN χ hf)

/-- Prime-supported character submodule is contained in oldforms: for any prime divisor
`p ∣ N`, the intersection `qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom`
lies in `cuspFormsOld N k`. -/
theorem qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    {p : ℕ} (hp : Nat.Prime p) (hpN : p ∣ N) :
    qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOld N k := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (N / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hpN) hp.pos).ne'⟩
  intro f hf
  exact qSupportedOnDvd_mem_cuspFormsOld_of_char hp.one_lt hpN χ f hf.2 hf.1

/-- Composite-`N` supremum-to-oldform bridge: the supremum over the prime divisors of
`N` of the prime-supported character submodules is contained in `cuspFormsOld N k`. -/
theorem iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N) :
    ⨆ p ∈ N.primeFactors,
        qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOld N k := by
  refine iSup₂_le (fun p hp => ?_)
  exact qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld χ
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- Composite-`N` character-space `mainLemma` from supremum membership: any cusp form
`f` in the supremum of the prime-supported character submodules is an oldform. -/
theorem mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ ⨆ p ∈ N.primeFactors,
        qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k :=
  iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld χ hf

/-- General-`d` character-space support-to-oldform reverse bridge: for any proper
divisor `d ∣ N` with `1 < d`, the intersection
`qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom` lies in
`cuspFormsOld N k`. -/
theorem qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_of_dvd
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    {d : ℕ} (hd : 1 < d) (hdN : d ∣ N) :
    qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOld N k := by
  haveI : NeZero d := ⟨by lia⟩
  haveI : NeZero (N / d) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hdN) (by lia : 0 < d)).ne'⟩
  intro f hf
  exact qSupportedOnDvd_mem_cuspFormsOld_of_char hd hdN χ f hf.2 hf.1

/-- Composite-`N` reverse bridge iSup over proper divisors: the supremum over
`d ∈ N.divisors` with `1 < d` of the support-intersect-character submodules is contained
in `cuspFormsOld N k`. -/
theorem iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_divisors
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N) :
    ⨆ d ∈ N.divisors.filter (1 < ·),
        qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOld N k := by
  refine iSup₂_le (fun d hd => ?_)
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdN, _⟩, hd_gt⟩ := hd
  exact qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_of_dvd
    χ hd_gt hdN

/-- Any cusp form `f` lying in the supremum over `d ∈ N.divisors, 1 < d` of the
support-intersect-character submodules is an oldform. -/
theorem mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule_divisors
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ ⨆ d ∈ N.divisors.filter (1 < ·),
        qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k :=
  iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_divisors
    χ hf

/-- Forward inclusion: every oldform lies in the iSup of proper-divisor support
submodules, i.e. `cuspFormsOld N k ≤ ⨆ d ∈ N.divisors, 1 < d, qSupportedOnDvdSubmodule N k d`. -/
theorem cuspFormsOld_le_iSup_qSupportedOnDvdSubmodule_divisors
    {N : ℕ} [NeZero N] {k : ℤ} :
    cuspFormsOld N k ≤
      ⨆ d ∈ N.divisors.filter (1 < ·), qSupportedOnDvdSubmodule N k d := by
  apply Submodule.span_le.mpr
  rintro f ⟨M, d, hM_ne, hd_ne, hd_gt, heq, g, rfl⟩
  haveI := hM_ne
  haveI := hd_ne
  have hd_mem : d ∈ N.divisors.filter (1 < ·) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨⟨M, heq.symm⟩, NeZero.ne N⟩, hd_gt⟩
  refine Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd_mem ?_)
  exact levelRaise_mem_qSupportedOnDvdSubmodule heq g

/-- Prime-power bridge: for `N = p^r` with `p` prime and `r ≥ 1`, any cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` at level `Γ₁(p^r)` satisfying the coprime-to-`p^r`
Fourier vanishing hypothesis lies in the divisor-iSup of the support-intersect-character
submodules. -/
theorem mem_iSup_divisor_qSupportedOnDvdSubmodule_inf_charSpace_of_coprime_vanishing_primePower
    {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 0 < r) {k : ℤ}
    (χ : DirichletCharacter ℂ (p ^ r))
    (f : CuspForm ((Gamma1 (p ^ r)).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p ^ r) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ ⨆ d ∈ (p ^ r).divisors.filter (1 < ·),
        qSupportedOnDvdSubmodule (p ^ r) k d ⊓
          cuspFormCharSpace k χ.toUnitHom := by
  have hp_prime : p.Prime := hp.out
  have hp_dvd : p ∣ p ^ r := dvd_pow_self p hr.ne'
  have hf_supp : f ∈ qSupportedOnDvdSubmodule (p ^ r) k p := by
    intro n hn
    apply h_vanish
    rw [Nat.coprime_pow_right_iff hr]
    exact ((hp_prime.coprime_iff_not_dvd).mpr hn).symm
  have hp_mem : p ∈ (p ^ r).divisors.filter (1 < ·) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hp_dvd, pow_ne_zero r hp_prime.ne_zero⟩, hp_prime.one_lt⟩
  refine Submodule.mem_iSup_of_mem p (Submodule.mem_iSup_of_mem hp_mem ?_)
  exact ⟨hf_supp, hfχ⟩

/-- Aggregation helper: if `f : CuspForm Γ₁(N) k` admits a finite decomposition
`f = ∑ d ∈ S, f_d d` with `S ⊆ N.divisors.filter (1 < ·)` and each `f_d d` simultaneously
in `qSupportedOnDvdSubmodule N k d` and `cuspFormCharSpace k χ.toUnitHom`, then `f` lies
in the divisor-iSup of the support-intersect-character submodules. -/
theorem mem_iSup_divisor_qSupportedOnDvdSubmodule_inf_charSpace_of_sum_decomp
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (S : Finset ℕ) (hS : S ⊆ N.divisors.filter (1 < ·))
    (f_d : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_decomp : f = ∑ d ∈ S, f_d d)
    (h_mem : ∀ d ∈ S, f_d d ∈ qSupportedOnDvdSubmodule N k d ⊓
      cuspFormCharSpace k χ.toUnitHom) :
    f ∈ ⨆ d ∈ N.divisors.filter (1 < ·),
        qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom := by
  rw [h_decomp]
  refine Submodule.sum_mem _ (fun d hd => ?_)
  exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem (hS hd) (h_mem d hd))

/-- Prime-power `mainLemma` routed through the divisor-iSup bridge: for `N = p^r`, a cusp
form in the character space satisfying the coprime-to-`p^r` vanishing hypothesis is an
oldform. -/
theorem mainLemma_charSpace_primePower_via_divisor_iSup
    {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 0 < r) {k : ℤ}
    (χ : DirichletCharacter ℂ (p ^ r))
    (f : CuspForm ((Gamma1 (p ^ r)).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p ^ r) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld (p ^ r) k :=
  mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule_divisors χ
    (mem_iSup_divisor_qSupportedOnDvdSubmodule_inf_charSpace_of_coprime_vanishing_primePower
      hr χ f hfχ h_vanish)

/-- A `TraceDescent N k χ f` is a witness that `f` admits a same-level `Γ₁(N)` divisor
decomposition whose pieces each lie in a `d`-supported `χ`-character subspace. -/
structure TraceDescent {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  /-- Finite set of proper divisors participating in the decomposition. -/
  divisors : Finset ℕ
  /-- The divisors are proper divisors of `N` strictly greater than `1`. -/
  divisors_subset : divisors ⊆ N.divisors.filter (1 < ·)
  /-- The same-level descent piece at each divisor, a cusp form at
  `Γ₁(N)`. -/
  piece : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- **Finite-sum reconstruction**: `f` equals the sum of its pieces. -/
  reconstructs : f = ∑ d ∈ divisors, piece d
  /-- **Coefficient support**: each piece is supported on multiples of
  its divisor at period-1 Fourier expansion. -/
  piece_supp : ∀ d ∈ divisors, piece d ∈ qSupportedOnDvdSubmodule N k d
  /-- **Character preservation**: each piece lies in the Nebentypus
  `χ`-character space. -/
  piece_char : ∀ d ∈ divisors,
    piece d ∈ cuspFormCharSpace k χ.toUnitHom

/-- A trace-descent witness `W : TraceDescent N k χ f` produces the composite-`N`
character-space `mainLemma` conclusion `f ∈ cuspFormsOld N k`. -/
theorem mainLemma_charSpace_of_TraceDescent
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (W : TraceDescent χ f) :
    f ∈ cuspFormsOld N k := by
  refine mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule_divisors χ ?_
  refine mem_iSup_divisor_qSupportedOnDvdSubmodule_inf_charSpace_of_sum_decomp χ f
    W.divisors W.divisors_subset W.piece W.reconstructs ?_
  intro d hd
  exact ⟨W.piece_supp d hd, W.piece_char d hd⟩

/-- Single-divisor constructor: a cusp form `f ∈ cuspFormCharSpace k χ.toUnitHom` known
to be `q`-supported on multiples of a single proper divisor `d ∣ N` with `1 < d` admits a
canonical `TraceDescent` with divisor set `{d}` and piece `piece d = f`. -/
noncomputable def TraceDescent.ofSingleDivisor
    {N : ℕ} [NeZero N] {k : ℤ}
    {χ : DirichletCharacter ℂ N}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    {d : ℕ} (hd : d ∈ N.divisors.filter (1 < ·))
    (hf_supp : f ∈ qSupportedOnDvdSubmodule N k d)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom) :
    TraceDescent χ f where
  divisors := {d}
  divisors_subset := by simpa using hd
  piece := fun _ => f
  reconstructs := by simp
  piece_supp := fun _ he => by obtain rfl := Finset.mem_singleton.mp he; exact hf_supp
  piece_char := fun _ _ => hfχ

/-- Prime-power constructor: for `N = p^r` with `p` prime and `r ≥ 1`, any
`f ∈ cuspFormCharSpace k χ.toUnitHom` satisfying the coprime-to-`p^r` Fourier vanishing
hypothesis admits a canonical `TraceDescent` with divisor set `{p}` and piece `piece p = f`. -/
noncomputable def TraceDescent.ofPrimePower
    {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 0 < r) {k : ℤ}
    {χ : DirichletCharacter ℂ (p ^ r)}
    {f : CuspForm ((Gamma1 (p ^ r)).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p ^ r) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    TraceDescent χ f :=
  TraceDescent.ofSingleDivisor (d := p)
    (by
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨dvd_pow_self p hr.ne', pow_ne_zero r hp.out.ne_zero⟩, hp.out.one_lt⟩)
    (by
      intro n hn
      apply h_vanish
      rw [Nat.coprime_pow_right_iff hr]
      exact ((hp.out.coprime_iff_not_dvd).mpr hn).symm)
    hfχ

/-- Prime-power `mainLemma` via `TraceDescent`: for `N = p^r`, a cusp form in the
character space satisfying the coprime-to-`p^r` vanishing hypothesis is an oldform. -/
theorem mainLemma_charSpace_primePower_via_TraceDescent
    {p : ℕ} [hp : Fact p.Prime] {r : ℕ} (hr : 0 < r) {k : ℤ}
    (χ : DirichletCharacter ℂ (p ^ r))
    (f : CuspForm ((Gamma1 (p ^ r)).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n (p ^ r) →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld (p ^ r) k :=
  mainLemma_charSpace_of_TraceDescent χ
    (TraceDescent.ofPrimePower hr hfχ h_vanish)

/-- Single-divisor consumer: for arbitrary `N`, any cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` known to be `q`-supported on multiples of a single
proper divisor `d ∣ N` with `1 < d` lies in `cuspFormsOld N k`. -/
theorem mainLemma_charSpace_of_singleDivisorSupport
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {d : ℕ} (hd : d ∈ N.divisors.filter (1 < ·))
    (hf_supp : f ∈ qSupportedOnDvdSubmodule N k d)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k :=
  mainLemma_charSpace_of_TraceDescent χ
    (TraceDescent.ofSingleDivisor hd hf_supp hfχ)

/-- Operator-level interface for same-level divisor projections: a family of `ℂ`-linear
endomorphisms `P : ℕ → (CuspForm (Γ₁ N) k →ₗ[ℂ] CuspForm (Γ₁ N) k)` with `d`-support of
each image, preservation of every Nebentypus character space, and a Möbius-type
finite-sum reconstruction for cusp forms satisfying the coprime-to-`N` vanishing
hypothesis. -/
structure SameLevelDivisorProjections (N : ℕ) [NeZero N] (k : ℤ) where
  /-- The per-divisor linear projection operator at level `Γ₁(N)`. -/
  P : ℕ → (CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
  /-- **Coefficient-support axiom.**  Each operator `P d` maps any cusp
  form to a form with period-1 Fourier support on multiples of `d`. -/
  P_supp : ∀ d ∈ N.divisors.filter (1 < ·),
    ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    P d f ∈ qSupportedOnDvdSubmodule N k d
  /-- **Character-preservation axiom.**  Each operator `P d` preserves
  every Nebentypus character space.  Equivalent to `P d` commuting
  with all diamond operators on `CuspForm (Γ₁ N) k`. -/
  P_char : ∀ d ∈ N.divisors.filter (1 < ·),
    ∀ (χ : (ZMod N)ˣ →* ℂˣ),
    ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    f ∈ cuspFormCharSpace k χ →
    P d f ∈ cuspFormCharSpace k χ
  /-- **Möbius finite-sum reconstruction axiom.**  Every cusp form
  satisfying the coprime-to-`N` Fourier vanishing hypothesis decomposes
  as the sum of its per-divisor projections. -/
  mobius_reconstruction : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    (∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) →
    f = ∑ d ∈ N.divisors.filter (1 < ·), P d f

/-- Given a `SameLevelDivisorProjections N k` datum and a cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` satisfying the coprime-to-`N` Fourier vanishing
hypothesis, build the `TraceDescent χ f` witness whose `piece d = Op.P d f`. -/
noncomputable def TraceDescent.ofSameLevelDivisorProjections
    {N : ℕ} [NeZero N] {k : ℤ}
    (Op : SameLevelDivisorProjections N k)
    {χ : DirichletCharacter ℂ N}
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    TraceDescent χ f where
  divisors := N.divisors.filter (1 < ·)
  divisors_subset := subset_rfl
  piece := fun d => Op.P d f
  reconstructs := Op.mobius_reconstruction f h_vanish
  piece_supp := fun d hd => Op.P_supp d hd f
  piece_char := fun d hd => Op.P_char d hd χ.toUnitHom f hfχ

/-- End-to-end consumer: a `SameLevelDivisorProjections N k` datum plus the
coprime-to-`N` vanishing hypothesis produces the composite-`N` character-space
`mainLemma`, `f ∈ cuspFormsOld N k`. -/
theorem mainLemma_charSpace_of_SameLevelDivisorProjections
    {N : ℕ} [NeZero N] {k : ℤ}
    (Op : SameLevelDivisorProjections N k)
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k :=
  mainLemma_charSpace_of_TraceDescent χ
    (TraceDescent.ofSameLevelDivisorProjections Op hfχ h_vanish)

/-- Same-level divisor decomposition consumer: a cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` together with a same-level divisor decomposition
into pieces with per-divisor `q`-support and character-space membership gives
`f ∈ cuspFormsOld N k`. -/
theorem mainLemma_charSpace_of_sameLevelDivisorDecomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (samePiece : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sum : f = ∑ d ∈ N.divisors.filter (1 < ·), samePiece d)
    (h_pieces : ∀ d ∈ N.divisors.filter (1 < ·),
      samePiece d ∈ qSupportedOnDvdSubmodule N k d ∧
      samePiece d ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k :=
  mainLemma_charSpace_of_TraceDescent χ
    { divisors := N.divisors.filter (1 < ·)
      divisors_subset := subset_rfl
      piece := samePiece
      reconstructs := h_sum
      piece_supp := fun d hd => (h_pieces d hd).1
      piece_char := fun d hd => (h_pieces d hd).2 }

private def cuspFormOfModularForm
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (g : ModularForm Γ k)
    (h : ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsZeroAt g.toFun k) :
    CuspForm Γ k where
  toFun := g
  slash_action_eq' := g.slash_action_eq'
  holo' := g.holo'
  zero_at_cusps' := h

@[simp] private lemma cuspFormOfModularForm_coe
    {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}
    (g : ModularForm Γ k)
    (h : ∀ {c : OnePoint ℝ}, IsCusp c Γ → c.IsZeroAt g.toFun k) :
    (⇑(cuspFormOfModularForm g h) : UpperHalfPlane → ℂ) = ⇑g := rfl

private lemma mem_cuspFormCharSpace_of_funeq_modForm
    {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)
    (g_cf : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g_mf : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_coe : (⇑g_cf : UpperHalfPlane → ℂ) = ⇑g_mf)
    (h_mf : g_mf ∈ modFormCharSpace k χ) :
    g_cf ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff]
  intro u
  obtain ⟨γ, hγ⟩ := Gamma0MapUnits_surjective (N := N) u
  apply DFunLike.ext
  intro z
  have h_cf_slash : (⇑(diamondOpCuspHom k u g_cf) : UpperHalfPlane → ℂ) z =
      (⇑g_mf ∣[k] (mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        GL (Fin 2) ℝ)) z := by
    show (⇑(diamondOpCusp k u g_cf) : UpperHalfPlane → ℂ) z = _
    rw [diamondOpCusp_eq k u γ hγ, ← h_coe]; rfl
  have h_mf_slash : (⇑g_mf ∣[k] (mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
        GL (Fin 2) ℝ)) z =
      ((↑(χ u) : ℂ) • (⇑g_mf : UpperHalfPlane → ℂ)) z := by
    rw [← show (⇑(diamondOp k u g_mf) : UpperHalfPlane → ℂ) z =
        (⇑g_mf ∣[k] (mapGL ℝ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
          GL (Fin 2) ℝ)) z by
      rw [diamondOp_eq_diamondOpAux k u γ hγ]; rfl]
    simpa using congrFun (congrArg (fun F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k =>
      (⇑F : UpperHalfPlane → ℂ)) ((mem_modFormCharSpace_iff k χ g_mf).mp h_mf u)) z
  rw [h_cf_slash, h_mf_slash]
  simp [h_coe]

private lemma cuspForm_eq_sum_of_toModularForm_eq_sum
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (samePiece : ℕ → ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (lifted : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (S : Finset ℕ)
    (h_sum : f.toModularForm' = ∑ d ∈ S, samePiece d)
    (h_coe : ∀ d ∈ S, (⇑(lifted d) : UpperHalfPlane → ℂ) = ⇑(samePiece d)) :
    f = ∑ d ∈ S, lifted d := by
  apply DFunLike.ext
  intro z
  have h_mf_sum : ∀ T : Finset ℕ,
      (⇑(∑ d ∈ T, samePiece d) : UpperHalfPlane → ℂ) z =
        ∑ d ∈ T, ⇑(samePiece d) z := by
    intro T
    induction T using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => simp only [Finset.sum_cons, ModularForm.coe_add, Pi.add_apply, ih]
  have h_cf_sum : ∀ T : Finset ℕ,
      (⇑(∑ d ∈ T, lifted d) : UpperHalfPlane → ℂ) z = ∑ d ∈ T, ⇑(lifted d) z := by
    intro T
    induction T using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => simp only [Finset.sum_cons, CuspForm.coe_add, Pi.add_apply, ih]
  rw [h_cf_sum, show (f z : ℂ) = (⇑f.toModularForm' : UpperHalfPlane → ℂ) z from rfl,
    h_sum, h_mf_sum]
  exact Finset.sum_congr rfl (fun d hd => by rw [h_coe d hd])

/-- SMO bridge consumer (ModularForm-input): a `CuspForm` `f` with a `ModularForm`-typed
same-level divisor decomposition `f.toModularForm' = ∑ d, samePiece d`, per-piece
`q`-support and character-space membership, plus a per-piece cusp-vanishing witness
`h_cusp` (the ingredient lost when moving from `CuspForm` input to `ModularForm` pieces),
gives `f ∈ cuspFormsOld N k`. -/
theorem mainLemma_charSpace_of_modularFormSameLevelDivisorDecomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (samePiece : ℕ → ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sum : f.toModularForm' = ∑ d ∈ N.divisors.filter (1 < ·), samePiece d)
    (h_pieces_qsupp : ∀ d ∈ N.divisors.filter (1 < ·),
      ∀ n : ℕ, ¬ d ∣ n →
        (ModularFormClass.qExpansion (1 : ℝ) ⇑(samePiece d)).coeff n = 0)
    (h_pieces_char : ∀ d ∈ N.divisors.filter (1 < ·),
      samePiece d ∈ modFormCharSpace k χ.toUnitHom)
    (h_cusp : ∀ d ∈ N.divisors.filter (1 < ·),
      ∀ {c : OnePoint ℝ}, IsCusp c ((Gamma1 N).map (mapGL ℝ)) →
        c.IsZeroAt (samePiece d).toFun k) :
    f ∈ cuspFormsOld N k := by
  classical
  let lifted : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k := fun d =>
    if hd : d ∈ N.divisors.filter (1 < ·) then
      cuspFormOfModularForm (samePiece d) (h_cusp d hd)
    else 0
  have h_pieces_lifted : ∀ d ∈ N.divisors.filter (1 < ·),
      lifted d ∈ qSupportedOnDvdSubmodule N k d ∧
      lifted d ∈ cuspFormCharSpace k χ.toUnitHom := by
    intro d hd
    have h_coe : (⇑(lifted d) : UpperHalfPlane → ℂ) = ⇑(samePiece d) := by
      simp only [lifted, dif_pos hd, cuspFormOfModularForm_coe]
    refine ⟨?_, ?_⟩
    · intro n hn
      show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(lifted d)) = 0
      rw [show (qExpansion (1 : ℝ) ⇑(lifted d)) =
          qExpansion (1 : ℝ) ⇑(samePiece d) by rw [h_coe]]
      exact h_pieces_qsupp d hd n hn
    · exact mem_cuspFormCharSpace_of_funeq_modForm χ.toUnitHom (lifted d)
        (samePiece d) h_coe (h_pieces_char d hd)
  exact mainLemma_charSpace_of_sameLevelDivisorDecomposition χ f lifted
    (cuspForm_eq_sum_of_toModularForm_eq_sum f samePiece lifted _ h_sum
      (fun d hd => by simp only [lifted, dif_pos hd, cuspFormOfModularForm_coe]))
    h_pieces_lifted

/-- SMO bridge composer (Projections-input): a `ModularFormSameLevelDivisorProjections`
bundle for `f.toModularForm'` gives `f ∈ cuspFormsOld N k`.  The cusp-vanishing input is
bundled inside the structure, so callers need not supply a separate cusp callback. -/
theorem mainLemma_charSpace_of_modularFormSameLevelDivisorProjections
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_χ_modularForm : f.toModularForm' ∈ modFormCharSpace k χ.toUnitHom)
    (L : List ℕ) (hL : ∀ p ∈ L, p.Prime ∧ p ∣ N)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n L.prod →
      (ModularFormClass.qExpansion (1 : ℝ) ⇑f.toModularForm').coeff n = 0)
    (h_le_full : (Gamma1 (N * L.prod)).map (mapGL ℝ) ≤
      (Gamma1 N).map (mapGL ℝ))
    (proj : HeckeRing.GL2.MainLemma.ModularFormSameLevelDivisorProjections
      f.toModularForm' hf_χ_modularForm L hL h_le_full) :
    f ∈ cuspFormsOld N k := by
  classical
  obtain ⟨samePiece, h_sum, h_pieces, h_cusp_pieces⟩ :=
    HeckeRing.GL2.MainLemma.same_level_collapse_of_deep_oldform_image_of_projections
      f.toModularForm' hf_χ_modularForm L hL h_vanish h_le_full proj
  refine mainLemma_charSpace_of_modularFormSameLevelDivisorDecomposition χ f
    samePiece h_sum ?_ ?_ h_cusp_pieces
  · intro d hd; exact (h_pieces d hd).2
  · intro d hd; exact (h_pieces d hd).1

/-- The per-divisor local field of `SameLevelDivisorProjections`: a single linear
endomorphism `P : CuspForm Γ₁(N) k →ₗ CuspForm Γ₁(N) k` with the local `P_supp` and
`P_char` axioms (the global `mobius_reconstruction` is not part of the local field). -/
structure SameLevelDivisorProjectionsLocalField (N : ℕ) [NeZero N] (k : ℤ)
    (d : ℕ) where
  /-- The per-divisor projection operator at level `Γ₁(N)`. -/
  P : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- **Local coefficient-support axiom.**  `P` maps every cusp form to
  one with period-1 Fourier support on multiples of `d`. -/
  P_supp : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    P f ∈ qSupportedOnDvdSubmodule N k d
  /-- **Local character-preservation axiom.**  `P` preserves every
  Nebentypus character space. -/
  P_char : ∀ (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    f ∈ cuspFormCharSpace k χ → P f ∈ cuspFormCharSpace k χ

/-- The trivial projection `P = 0` is a `SameLevelDivisorProjectionsLocalField` instance.
It is only a structural witness: it does not satisfy the global `mobius_reconstruction`
axiom of `SameLevelDivisorProjections`. -/
noncomputable def SameLevelDivisorProjectionsLocalField.zero
    (N : ℕ) [NeZero N] (k : ℤ) (d : ℕ) :
    SameLevelDivisorProjectionsLocalField N k d where
  P := 0
  P_supp := fun _ => by
    simpa only [LinearMap.zero_apply] using (qSupportedOnDvdSubmodule N k d).zero_mem
  P_char := fun χ _ _ => by
    simpa only [LinearMap.zero_apply] using (cuspFormCharSpace k χ).zero_mem

/-- Assemble a family of per-divisor local fields plus a single global Möbius
reconstruction hypothesis into a `SameLevelDivisorProjections N k`.  For divisors `d`
outside `N.divisors.filter (1 < ·)`, `P d` is set to `0`, which is harmless since
`P_supp` and `P_char` quantify only over that filter. -/
noncomputable def SameLevelDivisorProjections.ofLocalFields
    {N : ℕ} [NeZero N] {k : ℤ}
    (loc : ∀ d ∈ N.divisors.filter (1 < ·),
      SameLevelDivisorProjectionsLocalField N k d)
    (mobius : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) →
      f = ∑ d ∈ N.divisors.filter (1 < ·),
        (if hd : d ∈ N.divisors.filter (1 < ·) then (loc d hd).P else 0) f) :
    SameLevelDivisorProjections N k where
  P := fun d =>
    if hd : d ∈ N.divisors.filter (1 < ·) then (loc d hd).P else 0
  P_supp := fun d hd f => by simpa only [dif_pos hd] using (loc d hd).P_supp f
  P_char := fun d hd χ f hfχ => by simpa only [dif_pos hd] using (loc d hd).P_char χ f hfχ
  mobius_reconstruction := mobius

/-- Construction of a `SameLevelDivisorProjections N k` from the zero local-field family,
supplied with a global Möbius reconstruction hypothesis. -/
noncomputable def SameLevelDivisorProjections.ofZeroLocalFields
    (N : ℕ) [NeZero N] (k : ℤ)
    (mobius : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) →
      f = ∑ _d ∈ N.divisors.filter (1 < ·),
        (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) :
    SameLevelDivisorProjections N k :=
  SameLevelDivisorProjections.ofLocalFields
    (fun d _ => SameLevelDivisorProjectionsLocalField.zero N k d)
    (fun f hf => by
      convert mobius f hf using 1
      refine Finset.sum_congr rfl (fun d hd => ?_)
      simp only [dif_pos hd, SameLevelDivisorProjectionsLocalField.zero,
        LinearMap.zero_apply])

/-- Per-prime trace correction structure: a candidate same-level operator `core`, a
cusp-stabilizer `correction`, and the support and character-preservation obligations for
the difference `core - correction`.  Slots into `SameLevelDivisorProjections.ofLocalFields`
via `toLocalField`. -/
structure TraceCorrectionPrime (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) where
  /-- The candidate same-level operator at level `Γ₁(N)`. -/
  core : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- The cusp-stabilizer corrector: subtract this from `core` to obtain
  a genuinely `p`-supported, character-preserving operator. -/
  correction : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- **Support axiom for the corrected operator.**  The difference
  `core - correction`, applied to any cusp form, yields a form whose
  period-1 Fourier expansion is supported on multiples of `p`. -/
  core_minus_correction_supp : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
    (core - correction) f ∈ qSupportedOnDvdSubmodule N k p
  /-- **Character-preservation axiom for the corrected operator.**  The
  difference `core - correction` preserves every Nebentypus character
  space. -/
  core_minus_correction_char : ∀ (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    f ∈ cuspFormCharSpace k χ →
    (core - correction) f ∈ cuspFormCharSpace k χ

/-- Every `TraceCorrectionPrime N k p` produces a
`SameLevelDivisorProjectionsLocalField N k p` whose `P` field is `core - correction`. -/
noncomputable def TraceCorrectionPrime.toLocalField
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T : TraceCorrectionPrime N k p) :
    SameLevelDivisorProjectionsLocalField N k p where
  P := T.core - T.correction
  P_supp := T.core_minus_correction_supp
  P_char := T.core_minus_correction_char

/-- The trivial choice `core = 0`, `correction = 0` is a `TraceCorrectionPrime` instance.
It does not provide a non-trivial Möbius reconstruction. -/
noncomputable def TraceCorrectionPrime.zero
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) :
    TraceCorrectionPrime N k p where
  core := 0
  correction := 0
  core_minus_correction_supp := fun _ => by
    simpa only [sub_self, LinearMap.zero_apply] using (qSupportedOnDvdSubmodule N k p).zero_mem
  core_minus_correction_char := fun χ _ _ => by
    simpa only [sub_self, LinearMap.zero_apply] using (cuspFormCharSpace k χ).zero_mem

/-- The `P` field of the local-field produced by `TraceCorrectionPrime.zero` is the zero
linear map. -/
@[simp]
theorem TraceCorrectionPrime.toLocalField_zero_P
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) :
    (TraceCorrectionPrime.zero N k p).toLocalField.P = 0 := by
  show (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k) - 0 = 0
  rw [sub_zero]

/-- A same-level operator `Q` that is unconditionally `p`-supported and
character-preserving constitutes a `TraceCorrectionPrime N k p` with `core = Q` and
`correction = 0`. -/
noncomputable def TraceCorrectionPrime.ofCore
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (Q : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_supp : ∀ f, Q f ∈ qSupportedOnDvdSubmodule N k p)
    (h_char : ∀ (χ : (ZMod N)ˣ →* ℂˣ) f,
      f ∈ cuspFormCharSpace k χ → Q f ∈ cuspFormCharSpace k χ) :
    TraceCorrectionPrime N k p where
  core := Q
  correction := 0
  core_minus_correction_supp := fun f => by
    simpa [sub_zero] using h_supp f
  core_minus_correction_char := fun χ f hf => by
    simpa [sub_zero] using h_char χ f hf

/-- The `core - correction` of `ofCore Q h_supp h_char` is exactly `Q`. -/
@[simp]
theorem TraceCorrectionPrime.ofCore_diff
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (Q : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_supp : ∀ f, Q f ∈ qSupportedOnDvdSubmodule N k p)
    (h_char : ∀ (χ : (ZMod N)ˣ →* ℂˣ) f,
      f ∈ cuspFormCharSpace k χ → Q f ∈ cuspFormCharSpace k χ) :
    (TraceCorrectionPrime.ofCore Q h_supp h_char).core -
        (TraceCorrectionPrime.ofCore Q h_supp h_char).correction = Q := by
  show Q - 0 = Q
  rw [sub_zero]

/-- Pointwise addition of trace corrections: adds the `core` and `correction` fields. -/
noncomputable def TraceCorrectionPrime.add
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T₁ T₂ : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p where
  core := T₁.core + T₂.core
  correction := T₁.correction + T₂.correction
  core_minus_correction_supp := fun f => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, add_sub_add_comm]
    exact (qSupportedOnDvdSubmodule N k p).add_mem (T₁.core_minus_correction_supp f)
      (T₂.core_minus_correction_supp f)
  core_minus_correction_char := fun χ f hf => by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, add_sub_add_comm]
    exact (cuspFormCharSpace k χ).add_mem (T₁.core_minus_correction_char χ f hf)
      (T₂.core_minus_correction_char χ f hf)

/-- Pointwise negation of trace corrections: negates the `core` and `correction` fields. -/
noncomputable def TraceCorrectionPrime.neg
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p where
  core := -T.core
  correction := -T.correction
  core_minus_correction_supp := fun f => by
    have heq : ((-T.core) - (-T.correction)) f = -((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.neg_apply]; abel
    rw [heq]
    exact (qSupportedOnDvdSubmodule N k p).neg_mem (T.core_minus_correction_supp f)
  core_minus_correction_char := fun χ f hf => by
    have heq : ((-T.core) - (-T.correction)) f = -((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.neg_apply]; abel
    rw [heq]
    exact (cuspFormCharSpace k χ).neg_mem (T.core_minus_correction_char χ f hf)

/-- Scalar action on trace corrections: scales the `core` and `correction` fields. -/
noncomputable def TraceCorrectionPrime.smul
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (c : ℂ) (T : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p where
  core := c • T.core
  correction := c • T.correction
  core_minus_correction_supp := fun f => by
    have heq : ((c • T.core) - (c • T.correction)) f = c • ((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply]; rw [smul_sub]
    rw [heq]
    exact (qSupportedOnDvdSubmodule N k p).smul_mem c (T.core_minus_correction_supp f)
  core_minus_correction_char := fun χ f hf => by
    have heq : ((c • T.core) - (c • T.correction)) f = c • ((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply]; rw [smul_sub]
    rw [heq]
    exact (cuspFormCharSpace k χ).smul_mem c (T.core_minus_correction_char χ f hf)

/-- **Subtraction of trace corrections.**  Defined as `T₁ + (-T₂)`. -/
noncomputable def TraceCorrectionPrime.sub
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T₁ T₂ : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p :=
  T₁.add T₂.neg

/-- The `P`-field (`core - correction`) of `add` is the sum of the two `P`-fields. -/
@[simp]
theorem TraceCorrectionPrime.add_toLocalField_P
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T₁ T₂ : TraceCorrectionPrime N k p) :
    (T₁.add T₂).toLocalField.P = T₁.toLocalField.P + T₂.toLocalField.P := by
  show (T₁.core + T₂.core) - (T₁.correction + T₂.correction) =
    (T₁.core - T₁.correction) + (T₂.core - T₂.correction)
  abel

/-- The `P`-field of `neg` is the negation of the `P`-field. -/
@[simp]
theorem TraceCorrectionPrime.neg_toLocalField_P
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T : TraceCorrectionPrime N k p) :
    T.neg.toLocalField.P = -T.toLocalField.P := by
  show (-T.core) - (-T.correction) = -(T.core - T.correction)
  abel

/-- The `P`-field of `smul` is the scalar multiple of the `P`-field. -/
@[simp]
theorem TraceCorrectionPrime.smul_toLocalField_P
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (c : ℂ) (T : TraceCorrectionPrime N k p) :
    (T.smul c).toLocalField.P = c • T.toLocalField.P := by
  show (c • T.core) - (c • T.correction) = c • (T.core - T.correction)
  rw [smul_sub]

/-- A family of trace-correction witnesses (one per proper divisor
`d ∈ N.divisors.filter (1 < ·)`) plus a single global Möbius reconstruction hypothesis
produces a `SameLevelDivisorProjections N k` datum. -/
noncomputable def SameLevelDivisorProjections.ofTraceCorrections
    {N : ℕ} [NeZero N] {k : ℤ}
    (T : ∀ d ∈ N.divisors.filter (1 < ·), TraceCorrectionPrime N k d)
    (mobius : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) →
      f = ∑ d ∈ N.divisors.filter (1 < ·),
        (if hd : d ∈ N.divisors.filter (1 < ·) then
          (T d hd).toLocalField.P else 0) f) :
    SameLevelDivisorProjections N k :=
  SameLevelDivisorProjections.ofLocalFields
    (fun d hd => (T d hd).toLocalField) mobius

/-- End-to-end consumer: a per-divisor family of trace-correction witnesses, a global
Möbius reconstruction hypothesis, and a cusp form `f ∈ cuspFormCharSpace k χ.toUnitHom`
satisfying the coprime-to-`N` Fourier vanishing hypothesis give `f ∈ cuspFormsOld N k`. -/
theorem mainLemma_charSpace_of_traceCorrections
    {N : ℕ} [NeZero N] {k : ℤ}
    (T : ∀ d ∈ N.divisors.filter (1 < ·), TraceCorrectionPrime N k d)
    (mobius : ∀ f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) →
      f = ∑ d ∈ N.divisors.filter (1 < ·),
        (if hd : d ∈ N.divisors.filter (1 < ·) then
          (T d hd).toLocalField.P else 0) f)
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hfχ : f ∈ cuspFormCharSpace k χ.toUnitHom)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k :=
  mainLemma_charSpace_of_SameLevelDivisorProjections
    (SameLevelDivisorProjections.ofTraceCorrections T mobius)
    χ f hfχ h_vanish

end HeckeRing.GL2.AtkinLehner
