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

@[simp] lemma zero (d : ℕ) : IsSupportedOnDvd d (0 : PowerSeries ℂ) := fun _ _ ↦ by simp

lemma add {d : ℕ} {P Q : PowerSeries ℂ}
    (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P + Q) := fun n hn ↦ by
  rw [map_add, hP n hn, hQ n hn, zero_add]

lemma smul {d : ℕ} (c : ℂ) {P : PowerSeries ℂ} (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (c • P) := fun n hn ↦ by simp [smul_eq_mul, hP n hn]

lemma neg {d : ℕ} {P : PowerSeries ℂ} (hP : IsSupportedOnDvd d P) :
    IsSupportedOnDvd d (-P) := fun n hn ↦ by rw [map_neg, hP n hn, neg_zero]

lemma sub {d : ℕ} {P Q : PowerSeries ℂ}
    (hP : IsSupportedOnDvd d P) (hQ : IsSupportedOnDvd d Q) :
    IsSupportedOnDvd d (P - Q) := by
  rw [sub_eq_add_neg]; exact hP.add hQ.neg

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
        one_pos (one_mem_strictPeriods_Gamma1_map N) f g using 2
    show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(f + g)) = 0
    rw [h_eq, map_add, hf n hn, hg n hn, zero_add]
  smul_mem' c f hf := by
    intro n hn
    have h_eq : qExpansion (1 : ℝ) (⇑(c • f) : UpperHalfPlane → ℂ) =
        c • qExpansion (1 : ℝ) ⇑f := by
      convert qExpansion_smul (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (h := 1) one_pos
        (one_mem_strictPeriods_Gamma1_map N) c f using 2
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
      bdd_at_cusps' := fun {c} hc γ hγ ↦ (g.zero_at_cusps' hc γ hγ).isBoundedAtImInfty }
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
  cases h; rfl

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
      hd hdN f (fun n hn ↦ hfsupp n hn)
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
      rw [h_eq, h_zero]; simp [levelRaiseFun]
    exact h_f_zero ▸ Submodule.zero_mem _

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
      hd hdN f (fun n hn ↦ hfsupp n hn)
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
    rw [h_eq, h_zero]; simp [levelRaiseFun]

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
  refine ⟨fun hfsupp ↦
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
  refine ⟨?_, fun ⟨g, hg⟩ ↦ Or.inr ⟨g, hg⟩⟩
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
  refine ⟨fun ⟨hsup, _⟩ ↦
    (qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char
      hd hdN χ f hfχ).mp hsup, fun h ↦ ⟨?_, hfχ⟩⟩
  exact (qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char
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
  refine ⟨fun ⟨hrange, hchar⟩ ↦ ⟨?_, hchar⟩,
          fun ⟨hsup, hchar⟩ ↦ ⟨?_, hchar⟩⟩
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
  rw [map_sum, h_decomp, ← Finset.sum_attach S (fun χ ↦ f_χ χ)]
  exact Finset.sum_congr rfl (fun χ _ ↦ hg_χ χ.val χ.property)

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
  refine Submodule.sum_mem _ (fun p hp ↦ ?_)
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

/-- **Same-level divisor decomposition consumer** (`mainLemma_charSpace`, the headline
output of this file): given a Dirichlet character `χ` mod `N`, a cusp form
`f : CuspForm Γ₁(N) k`, and a same-level divisor decomposition
`f = ∑ d ∈ N.divisors.filter (1 < ·), samePiece d` whose pieces simultaneously lie in
`qSupportedOnDvdSubmodule N k d` and `cuspFormCharSpace k χ.toUnitHom`, conclude
`f ∈ cuspFormsOld N k`.  Each piece is handled by
`qSupportedOnDvd_mem_cuspFormsOld_of_char`, and the conclusion follows by `sum_mem`. -/
theorem mainLemma_charSpace_of_sameLevelDivisorDecomposition
    {N : ℕ} [NeZero N] {k : ℤ}
    (χ : DirichletCharacter ℂ N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (samePiece : ℕ → CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sum : f = ∑ d ∈ N.divisors.filter (1 < ·), samePiece d)
    (h_pieces : ∀ d ∈ N.divisors.filter (1 < ·),
      samePiece d ∈ qSupportedOnDvdSubmodule N k d ∧
      samePiece d ∈ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k := by
  rw [h_sum]
  refine Submodule.sum_mem _ (fun d hd ↦ ?_)
  rw [Finset.mem_filter, Nat.mem_divisors] at hd
  obtain ⟨⟨hdN, _⟩, hd_gt⟩ := hd
  have hd_pos : 0 < d := by omega
  haveI : NeZero d := ⟨hd_pos.ne'⟩
  haveI : NeZero (N / d) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_neZero N) hdN) hd_pos).ne'⟩
  have hd_mem : d ∈ N.divisors.filter (1 < ·) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdN, NeZero.ne N⟩, hd_gt⟩
  exact qSupportedOnDvd_mem_cuspFormsOld_of_char hd_gt hdN χ
    (samePiece d) (h_pieces d hd_mem).2 (h_pieces d hd_mem).1

end HeckeRing.GL2.AtkinLehner
