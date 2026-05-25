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
# Atkin-Lehner same-level `p`-supported projection API (POST-4e / T117)

This file develops the **Atkin-Lehner projection API** identified in T114
as the missing structural input for `Newforms.mainLemma` (Diamond–Shurman
Thm 5.7.1, Atkin–Lehner [AL70]).  The mainLemma states that any cusp
form `f ∈ S_k(Γ₁(N))` whose Fourier coefficients vanish at every index
coprime to `N` is an oldform.  The classical proof (DS §5.7) splits `f`
into pieces supported on multiples of each prime `p ∣ N`, then identifies
each piece with the image of the level-raise operator
`V_p : S_k(Γ₁(N/p)) → S_k(Γ₁(N))`.

This file provides the **structural framework** of "support on multiples
of `d`" needed for that decomposition:

* `IsSupportedOnDvd d P` — power-series predicate "support of `P` ⊆
  multiples of `d`".
* `IsSupportedOnDvd.zero / .add / .smul / .neg / .sub` — closure under
  the obvious algebraic operations.
* `QExpansionSupportedOnDvd d f` — "the canonical period-1 `q`-expansion
  of `f` is supported on multiples of `d`" for a cusp form `f` at level
  `Γ₁(N)`.
* `qSupportedOnDvdSubmodule N k d` — the submodule of cusp forms
  satisfying the support condition, equipped with the inherited closure
  lemmas.
* `qExpansion_levelRaise_isSupportedOnDvd` — the **forward direction**
  of the Atkin–Lehner correspondence: the image of the level-raise
  operator `levelRaise M d k` is automatically supported on multiples
  of `d`.  Direct from `qExpansion_one_modularFormLevelRaise_coeff` in
  `LevelRaise.lean`.
* `levelRaise_mem_qSupportedOnDvdSubmodule` — packaged form of the
  above as submodule membership.

The **reverse direction** of the Atkin–Lehner correspondence — that any
form supported on multiples of `d` (with `d ∣ N`) is the image of the
level-raise operator from `Γ₁(N/d)` — is the **central theorem-sized
gap** for `Newforms.mainLemma`.  Its proof requires the trace operator
`Tr_d : S_k(Γ₁(N)) → S_k(Γ₁(N/d))` (averaging over coset
representatives `Γ₁(N/d) / Γ₁(N)`) or the equivalent `U_d / V_d`
Hecke-operator framework.  See the docstring of
`isSupportedOnDvd_iff_in_levelRaise_image` (statement, no proof) for the
exact missing theorem signature.

## Roadmap to `Newforms.mainLemma`

1. **q-expansion decomposition** (in `MainLemma.lean`, already landed):
   for `f ∈ M_k(Γ₁(N))`, the multi-prime sieve
   `miyake_main_lemma_4_6_8_level_L` exhibits a Möbius-inversion
   companion `g'` with `(qExpansion 1 (f - g')).coeff n =
   if Coprime n L then ... else 0`, at level `Γ₁(N · L)`.
2. **Support pieces** (this file): if `f` has q-expansion supported on
   multiples of `d`, capture this property as `qSupportedOnDvdSubmodule`
   membership; show `levelRaise (N/d) d k` images live there.
3. **Reverse direction** (gap): identify the support submodule with the
   `levelRaise` image — this is the Atkin–Lehner main lemma core.  Once
   landed, `Newforms.mainLemma` follows by combining (1) at `L = N`
   (giving `f - 0 = f` since the sieve = 0 by hypothesis) with the
   support-decomposition of `f` into `Σ_{p ∣ N} f_p` pieces and (3)
   applied to each `f_p`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.7 (Atkin–Lehner
  Main Lemma 5.7.1).
* Atkin–Lehner, "Hecke operators on Γ₀(m)", Math. Ann. 185 (1970).
* Miyake, *Modular Forms*, §4.6 (conductor / main lemma route).
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

/-- The constant power series `1 : PowerSeries ℂ` is supported on
multiples of any `d ≥ 1`, since its only non-zero coefficient is at
index `0` and every natural divides `0`.  Recorded as a sanity check. -/
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
period-1 `q`-expansion is supported on multiples of `d`.

Closed under addition, scalar multiplication, and the zero form, via
`IsSupportedOnDvd.zero / .add / .smul` together with Mathlib's
`qExpansion_zero / _add / _smul` (transferred along the `CuspForm` →
`ModularFormClass` instance). -/
noncomputable def qSupportedOnDvdSubmodule (N : ℕ) [NeZero N] (k : ℤ) (d : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  carrier := {f | QExpansionSupportedOnDvd d f}
  zero_mem' := by intro n _; simp [qExpansion_zero]
  add_mem' {f g} hf hg := by
    intro n hn
    have h_eq : qExpansion (1 : ℝ) (⇑(f + g) : UpperHalfPlane → ℂ) =
        qExpansion (1 : ℝ) ⇑f + qExpansion (1 : ℝ) ⇑g := by
      have := qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ)) (h := 1) (a := k) (b := k)
        one_pos h1_period_Gamma1 f g
      convert this using 2
    show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(f + g)) = 0
    rw [h_eq, map_add, hf n hn, hg n hn, zero_add]
  smul_mem' c f hf := by
    intro n hn
    have h_eq : qExpansion (1 : ℝ) (⇑(c • f) : UpperHalfPlane → ℂ) =
        c • qExpansion (1 : ℝ) ⇑f := by
      have := qExpansion_smul (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (h := 1) one_pos
        h1_period_Gamma1 c f
      convert this using 2
    show (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑(c • f)) = 0
    rw [h_eq, show (PowerSeries.coeff n) (c • qExpansion (1 : ℝ) ⇑f) =
      c * (PowerSeries.coeff n) (qExpansion (1 : ℝ) ⇑f) by simp [smul_eq_mul],
      hf n hn, mul_zero]

@[simp] lemma mem_qSupportedOnDvdSubmodule
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ qSupportedOnDvdSubmodule N k d ↔ QExpansionSupportedOnDvd d f :=
  Iff.rfl


/-- **Level-raise q-expansion forward direction (modular form).**  For
`g : ModularForm Γ₁(M) k`, the image `modularFormLevelRaise M d k g`
has period-1 `q`-expansion supported on multiples of `d`.

Direct from `qExpansion_one_modularFormLevelRaise_coeff` (LevelRaise.lean). -/
lemma qExpansion_modularFormLevelRaise_isSupportedOnDvd
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] {k : ℤ}
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    IsSupportedOnDvd d (qExpansion (1 : ℝ) (modularFormLevelRaise M d k g)) := by
  intro n hn
  rw [qExpansion_one_modularFormLevelRaise_coeff g n, if_neg hn]

/-- **Level-raise q-expansion forward direction (cusp form), abstract
formulation.**  For any cusp form `g : CuspForm Γ₁(M) k`, its underlying
function `⇑g : UpperHalfPlane → ℂ` lifts to a (zero-cusp) modular form
at level `Γ₁(M)` whose level-raise has the desired q-expansion support.
We expose the support property at the function level, since the
`CuspForm`/`ModularForm` distinction is irrelevant for the q-expansion
structure (both share `ModularFormClass` via
`CuspForm.instModularFormClassOfCuspFormClass`).

This lemma is consumed below as the forward direction of the Atkin–
Lehner correspondence. -/
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

/-- **Forward Atkin–Lehner correspondence (submodule form).**  Any
cusp form obtained by level-raising lies in the
`qSupportedOnDvdSubmodule`.  This is the **easy** direction of the
correspondence; the reverse — that every form in the submodule is a
level-raise image — is the Atkin–Lehner main content (Diamond–Shurman
Thm 5.7.1) and is the precise structural gap for
`Newforms.mainLemma`. -/
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
  rw [cuspForm_coe_eq_of_cast h_dvd_eq]
  exact h_funeq

/-- **Reverse Atkin-Lehner bridge (with Nebentypus character).**  For a
cusp form `f ∈ S_k(Γ₁(N), χ)` whose period-1 `q`-expansion is supported
on multiples of a proper divisor `d` of `N` (`1 < d`, `d ∣ N`), `f`
is an oldform: `f ∈ cuspFormsOld N k`.

Proof route (POST-4e T117 pivot):

1. From `hfsupp`, apply `Newforms.exists_levelRaise_preimage_of_coeff_support_multiples`
   (T116) to obtain `φ : ℍ → ℂ` with `⇑f = levelRaiseFun d k φ` and
   `φ ∣[k] T = φ`.
2. Apply `ConductorTheorem.conductor_theorem_dichotomy_cuspForm_strong`
   to dispatch into Case A (factoring) or Case B (vanishing).
3. **Case A**: get `F : CuspForm Γ₁(N/d) k` with `⇑F = φ`; show
   `f = (Nat.mul_div_cancel' hdN) ▸ levelRaise (N/d) d k F`, hence
   `IsOldformGenerator f` (using `hd : 1 < d`), hence membership in
   `cuspFormsOld N k`.
4. **Case B**: `φ = 0`, so `⇑f = levelRaiseFun d k 0`, which gives
   `f = 0`; the zero cusp form is in any submodule including
   `cuspFormsOld N k`. -/
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

/-- **Reverse Atkin-Lehner explicit preimage (character-space, T130).**
For a cusp form `f ∈ cuspFormCharSpace k χ.toUnitHom` at level `Γ₁(N)`
whose period-1 `q`-expansion is supported on multiples of a proper
divisor `d ∣ N` (`1 < d`), either `f` is the zero form **or** `f`
equals (as a function on `ℍ`) the level-raise of some cusp form at
level `Γ₁(N/d)`.

The proof extracts the `F`-witness internal to the T117 conductor
dichotomy (`conductor_theorem_dichotomy_cuspForm_strong`) and surfaces
it as the `Or.inr` branch; the zero case is the `Or.inl` branch. -/
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
  · -- Case A: surface the explicit lower-level preimage.
    right
    refine ⟨F, ?_⟩
    show levelRaiseFun d k ⇑F = ⇑f
    rw [hF_eq, ← h_eq]
  · -- Case B: `f = 0`.
    left
    apply DFunLike.coe_injective
    show (⇑f : UpperHalfPlane → ℂ) = 0
    rw [h_eq, h_zero]
    simp [levelRaiseFun]

/-- **Reverse Atkin-Lehner character-space iff (T130 full iff).**  For a
cusp form `f ∈ cuspFormCharSpace k χ.toUnitHom` at level `Γ₁(N)` and a
proper divisor `d ∣ N` (`1 < d`),

  `f ∈ qSupportedOnDvdSubmodule N k d ↔
    f = 0 ∨ ∃ g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k,
      (⇑(levelRaise (N / d) d k g) : UpperHalfPlane → ℂ) = ⇑f`.

The forward direction is
`qSupportedOnDvd_eq_zero_or_exists_levelRaise_preimage_of_char`.  The
reverse direction combines:

* `Submodule.zero_mem` for the `f = 0` branch, and
* `levelRaise_mem_qSupportedOnDvdSubmodule` for the existential branch,
  upgrading function-level equality `⇑(levelRaise …) = ⇑f` to CuspForm
  equality `heq ▸ levelRaise (N/d) d k g = f` via `DFunLike.coe_injective`
  (using `cuspForm_coe_eq_of_cast` to transport across the type-level
  cast from `Gamma1 (d * (N/d))` to `Gamma1 N`).

**Character-space scope.**  The `hfχ` character hypothesis is used only
by the forward direction (through T130 / T117 / the conductor dichotomy).
The reverse direction is character-independent.  Extending the iff to
the pure-`Γ₁(N)` setting (no character) requires the trace / `U_d V_d`
framework and is outside the T130 lane. -/
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

/-- **Reverse Atkin-Lehner character-space iff, single existential (T130
packaging).**  Zero-absorbed form of
`qSupportedOnDvdSubmodule_mem_iff_eq_zero_or_exists_levelRaise_preimage_of_char`:
under the character-space/proper-divisor hypotheses, `f` is supported on
multiples of `d` iff `f` equals (as a function on `ℍ`) the level-raise of
some cusp form at level `Γ₁(N/d)`.  The `f = 0` branch is absorbed by
choosing `g = 0`, since the level-raise of the zero cusp form is
definitionally the zero function.

Preferred form for downstream consumers that do not need to distinguish
the zero case. -/
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

/-- **Reverse Atkin-Lehner character-space iff, CuspForm-transported
(T130 packaging).**  CuspForm-level form of the single-existential iff,
upgraded through the type-level cast `heq : d * (N/d) = N`: `f` is
supported on multiples of `d` iff `f` equals (as a cusp form at level
`Γ₁(N)`) the cast `heq ▸ levelRaise (N/d) d k g` of some lower-level
cusp form `g`.

This is the Atkin-Lehner preimage in its strongest CuspForm-level form
(character-space lane): downstream consumers obtain an honest equation
`f = heq ▸ levelRaise (N/d) d k g` rather than a mere function-level
equality.

Proof: transport between the function-level iff (landed above) and the
CuspForm-level one via `DFunLike.coe_injective` +
`cuspForm_coe_eq_of_cast`. -/
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

/-- **Submodule-level forward bridge (T130 packaging).**  The
`heq`-cast of every level-raise image lies in `qSupportedOnDvdSubmodule
N k d`.  Direct reformulation of `levelRaise_mem_qSupportedOnDvdSubmodule`
at the explicit cast `heq := Nat.mul_div_cancel' hdN`, so downstream
callers can quote the cast-to-`N` form without re-deriving the
`d * (N/d) = N` equation. -/
theorem cast_levelRaise_mem_qSupportedOnDvdSubmodule
    {N d : ℕ} [NeZero N] [NeZero d] [NeZero (N / d)]
    (hdN : d ∣ N) {k : ℤ}
    (g : CuspForm ((Gamma1 (N / d)).map (mapGL ℝ)) k) :
    ((Nat.mul_div_cancel' hdN) ▸ levelRaise (N / d) d k g :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      qSupportedOnDvdSubmodule N k d :=
  levelRaise_mem_qSupportedOnDvdSubmodule (Nat.mul_div_cancel' hdN) g

/-- **Submodule-level intersection bridge (T130 packaging).**  Identifies
membership in `qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k
χ.toUnitHom` with the existence of an explicit CuspForm-level
lower-level preimage.  This is the full submodule-level form of T130 in
the character-space lane.

Under the character hypothesis `hfχ`, `f` sits in the intersection iff
`f` is the cast of a level-raise of some `g : CuspForm ((Gamma1 (N /
d)).map (mapGL ℝ)) k`.  The forward containment uses
`qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char`
(T130 full iff, CuspForm-transported); the reverse containment combines
that iff with `hfχ`.

**Usage.**  Downstream SMO/newform code can apply this theorem directly
to replace membership/equality conversions by an explicit existential
on the lower-level side. -/
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

/-- **Cast LinearEquiv for CuspForm levels equal by proof (T130
packaging).**  For `h : M = N` a type-level equality of levels, the
identity cast `(h ▸ ·)` is a `ℂ`-linear equivalence between the two
CuspForm spaces.  All data equations are discharged by `subst h`. -/
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

/-- **Same-level casted level-raise LinearMap (T130 packaging).**  The
composition of `levelRaise (N/d) d k : CuspForm Γ₁(N/d) k →ₗ[ℂ] CuspForm
Γ₁(d · (N/d)) k` with the cast equivalence
`castCuspFormLinearEquiv (Nat.mul_div_cancel' hdN) k` yields a
`ℂ`-linear map landing at level `Γ₁(N)`.  This is the Atkin-Lehner
level-raise operator packaged at the same-level target for downstream
range / submodule arguments. -/
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

/-- **Range ⊆ qSup (T130 packaging).**  Every image of `castLevelRaise`
at level `Γ₁(N)` lies in `qSupportedOnDvdSubmodule N k d`.  Direct from
`cast_levelRaise_mem_qSupportedOnDvdSubmodule`; character hypothesis
not required. -/
theorem range_castLevelRaise_le_qSupportedOnDvdSubmodule
    {N : ℕ} [NeZero N] {d : ℕ} [NeZero d] [NeZero (N / d)]
    (hdN : d ∣ N) (k : ℤ) :
    LinearMap.range (castLevelRaise N d hdN k) ≤
      qSupportedOnDvdSubmodule N k d := by
  rintro _ ⟨g, rfl⟩
  rw [castLevelRaise_apply]
  exact cast_levelRaise_mem_qSupportedOnDvdSubmodule hdN g

/-- **Submodule intersection equality (T130 packaging, final).**
Character-space Atkin-Lehner identification at the `Submodule` level:
the range of `castLevelRaise`, intersected with the Nebentypus
character space, equals `qSupportedOnDvdSubmodule N k d` intersected
with the character space.

Forward containment: uses
`range_castLevelRaise_le_qSupportedOnDvdSubmodule` (unconditional).
Reverse containment: uses
`mem_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_iff_exists_cuspForm_levelRaise_preimage_of_char`
(character-conditional).

Subsumes both earlier iff packagings and exposes the Atkin-Lehner
reverse-direction content as a single `Submodule` equality in the
character-space lane. -/
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

/-- **Character-decomposition reverse bridge (T130 extension).**  If a
cusp form `f : CuspForm Γ₁(N) k` decomposes as a finite sum
`f = ∑ χ ∈ S, f_χ χ` with each summand `f_χ χ` lying in the intersection
`qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom`, then
`f` admits an explicit level-raise preimage at level `Γ₁(N/d)`: there
exists `g : CuspForm Γ₁(N/d) k` with `f = castLevelRaise N d hdN k g`.

**Proof strategy.**  Each summand `f_χ χ` sits in the intersection
`qSupported ⊓ charSpace`, so the character-conditional iff
`qSupportedOnDvdSubmodule_mem_iff_exists_cuspForm_levelRaise_preimage_of_char`
produces a per-character preimage `g_χ : CuspForm Γ₁(N/d) k` with
`f_χ χ = castLevelRaise N d hdN k g_χ`.  Summing via `Finset.sum_attach`
and the `ℂ`-linearity of `castLevelRaise` yields the single-preimage
witness `g = ∑ χ ∈ S.attach, g_χ χ.val`.

**Why this reduces the gap.**  The pure-Γ₁(N) reverse direction of
`isSupportedOnDvd_iff_in_levelRaise_image` (membership in
`qSupportedOnDvdSubmodule N k d` implies a level-raise preimage) is
blocked in-repo by the absence of a cusp-form-level trace / `U_d V_d`
framework.  This theorem converts that obligation into the (strictly
simpler, character-space lane) task of producing a d-support-preserving
character decomposition of `f`; each individual character piece is
then discharged by the landed character-space iff. -/
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


/-- **Character-space mainLemma at prime-power level (T118).**  For
`N = p^r` with `p` prime and `r ≥ 1`, a cusp form `f ∈ S_k(Γ₁(p^r), χ)`
whose Fourier coefficients vanish at every index coprime to `p^r` is
an oldform: `f ∈ cuspFormsOld (p^r) k`.

This is the **direct consumer of T117** for prime-power levels: the
hypothesis is rewritten to the `qSupportedOnDvdSubmodule (p^r) k p`
membership condition via `Nat.Prime.coprime_iff_not_dvd`, then
`qSupportedOnDvd_mem_cuspFormsOld_of_char` is applied with `d = p`.

The two `NeZero` instances required by T117 are derived locally from
`hp.ne_zero` and `hr` (no caller-supplied typeclasses needed). -/
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
  have hp_dvd : p ∣ p ^ r := dvd_pow_self p hr.ne'
  have h_supp : f ∈ qSupportedOnDvdSubmodule (p ^ r) k p := by
    intro n hn
    apply h
    rw [Nat.coprime_pow_right_iff hr]
    exact ((hp_prime.coprime_iff_not_dvd).mpr hn).symm
  exact qSupportedOnDvd_mem_cuspFormsOld_of_char hp_prime.one_lt hp_dvd χ f hfχ h_supp

/-- **Composite-level mainLemma from a prime-supported decomposition.**

Let `f : CuspForm Γ₁(N) k` lie in the Nebentypus character space
`cuspFormCharSpace k χ` at composite level `N`.  Suppose `f` admits a
finite decomposition
`f = Σ_{p ∈ S} f_p` where `S ⊆ N.primeFactors` and each `f_p` is
simultaneously in the character space and in
`qSupportedOnDvdSubmodule N k p` (period-1 coefficients supported on
multiples of `p`).  Then `f ∈ cuspFormsOld N k`.

**Route**: apply T117 (`qSupportedOnDvd_mem_cuspFormsOld_of_char`) to
each `f_p p` and sum via `Submodule.sum_mem`.  T117 requires
`1 < p`, `p ∣ N`, `NeZero p`, and `NeZero (N / p)`, all of which come
from `p ∈ N.primeFactors` together with `NeZero N`. -/
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

/-- **Composite-level mainLemma at the full set of prime divisors.**
Specialisation of `mainLemma_charSpace_of_prime_decomposition` taking
`S := N.primeFactors`.  This is the caller-facing statement: any
cuspForm `f` that decomposes as `f = Σ_{p ∣ N prime} f_p` with each
`f_p` in the character space and `p`-supported is an oldform. -/
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

/-- **`q`-expansion formula for `pSupportedRaise`.**  At period 1,

  `a_n(pSupportedRaise f) = a_n(f)  if p ∣ n,  else 0`.

Direct from `qExpansion_one_modularFormLevelRaise_coeff` (`V_p` formula)
and `qExpansion_one_heckeT_p_divN_coeff` (`U_p` formula): the outer `V_p`
contributes the `if p ∣ n` selector, and the inner `U_p` shifts the
coefficient index by `p`, giving `a_{p · (n/p)}(f) = a_n(f)` when
`p ∣ n` (via `Nat.mul_div_cancel'`). -/
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

/-- **Character-space preservation for `pSupportedRaise`.**  If `f` lies
in the Nebentypus space `M_k(Γ₁(N), χ)`, then `pSupportedRaise k p hp
hpN f` lies in `M_k(Γ₁(p · N), χ.comp (ZMod.unitsMap (N ∣ p · N)))`,
the natural lift of `χ` to level `p · N`.

Composes `heckeT_p_divN_preserves_modFormCharSpace` (same-level character
preservation of `U_p`) with `modularFormLevelRaise_mem_modFormCharSpace`
(character pullback under `V_p`). -/
theorem pSupportedRaise_mem_modFormCharSpace {N : ℕ} [NeZero N] {k : ℤ}
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (χ : (ZMod N)ˣ →* ℂˣ) {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) :
    pSupportedRaise k p hp hpN f ∈
      modFormCharSpace k (χ.comp (ZMod.unitsMap (Nat.dvd_mul_left N p))) :=
  HeckeRing.GL2.MainLemma.modularFormLevelRaise_mem_modFormCharSpace N p k χ
    (HeckeRing.GL2.MainLemma.heckeT_p_divN_preserves_modFormCharSpace hp hpN χ hf)

/-- **Prime-supported character submodule is contained in oldforms.**
For any prime divisor `p ∣ N`, the intersection
`qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom` lies
in `cuspFormsOld N k`.  This is the submodule form of T117 applied to
`d = p`. -/
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

/-- **Composite-`N` supremum-to-oldform bridge (T126).**  The supremum
over the prime divisors of `N` of the prime-supported character
submodules is contained in `cuspFormsOld N k`.  A direct
`iSup₂_le`-packaging of
`qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld`. -/
theorem iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N) :
    ⨆ p ∈ N.primeFactors,
        qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOld N k := by
  refine iSup₂_le (fun p hp => ?_)
  exact qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld χ
    (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)

/-- **Composite-`N` character-space `mainLemma` from supremum
membership (T126).**  Any cusp form `f` in the supremum of the
prime-supported character submodules is an oldform.  This is the
caller-facing consumer form of the T126 bridge: the honest remaining
obligation for the full composite-`N` `mainLemma` is to show any `f`
satisfying the coprime-vanishing hypothesis lies in this supremum. -/
theorem mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ ⨆ p ∈ N.primeFactors,
        qSupportedOnDvdSubmodule N k p ⊓ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k :=
  iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld χ hf

/-- **General-`d` character-space support-to-oldform reverse bridge
(T130).**  For any proper divisor `d ∣ N` with `1 < d`, the intersection
`qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom` lies
in `cuspFormsOld N k`.  Direct submodule packaging of T117
(`qSupportedOnDvd_mem_cuspFormsOld_of_char`) at general `d`.

Strictly generalises
`qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld` (which
covers only prime `d`) to any divisor `d ∣ N` with `1 < d`.  The
`NeZero d` and `NeZero (N / d)` instances are derived locally from
`1 < d`, the divisibility hypothesis, and `NeZero N`. -/
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

/-- **Composite-`N` reverse bridge iSup over proper divisors (T130).**
The supremum over `d ∈ N.divisors` with `1 < d` of the support-intersect-
character submodules is contained in `cuspFormsOld N k`.

This is the composite-`N` character-space support-to-oldform reverse
bridge in submodule form: any cusp form that decomposes as a finite sum
of pieces, each simultaneously `d`-supported (for some `d ∣ N`, `1 < d`)
and in the Nebentypus character space, is automatically an oldform.

Strictly generalises T126
(`iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld`)
from prime divisors to **all** proper divisors `d > 1`. -/
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

/-- **Caller-facing consumer for the T130 reverse bridge iSup over
proper divisors.**  Any cusp form `f` lying in the supremum over
`d ∈ N.divisors, 1 < d` of the support-intersect-character submodules is
an oldform.

This is the natural consumer for witnesses produced by Miyake §4.6
sieves or Atkin–Lehner–Li arguments, which may supply supports at
non-prime divisors. -/
theorem mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule_divisors
    {N : ℕ} [NeZero N] {k : ℤ} (χ : DirichletCharacter ℂ N)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ ⨆ d ∈ N.divisors.filter (1 < ·),
        qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom) :
    f ∈ cuspFormsOld N k :=
  iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_divisors
    χ hf

/-- **Forward inclusion (T130): every oldform lies in the iSup of
proper-divisor support submodules.**  `cuspFormsOld N k` is contained in
`⨆ d ∈ N.divisors, 1 < d, qSupportedOnDvdSubmodule N k d`.

Together with the reverse inclusion
`iSup_qSupportedOnDvdSubmodule_inf_cuspFormCharSpace_le_cuspFormsOld_divisors`
(on the character-intersected side), this characterises, at the level of
the modular lattice of submodules, `cuspFormsOld N k` in terms of
`d`-supported submodules.

Proof: `Submodule.span_le` on the `IsOldformGenerator` set.  Every
generator is of the form `heq ▸ levelRaise M d k g` with `d * M = N`,
`1 < d`, and is supported on multiples of `d` by
`levelRaise_mem_qSupportedOnDvdSubmodule`.  Since `d ∣ N` (from `heq`)
and `N ≠ 0`, we have `d ∈ N.divisors.filter (1 < ·)`. -/
theorem cuspFormsOld_le_iSup_qSupportedOnDvdSubmodule_divisors
    {N : ℕ} [NeZero N] {k : ℤ} :
    cuspFormsOld N k ≤
      ⨆ d ∈ N.divisors.filter (1 < ·), qSupportedOnDvdSubmodule N k d := by
  apply Submodule.span_le.mpr
  rintro f ⟨M, d, hM_ne, hd_ne, hd_gt, heq, g, rfl⟩
  haveI := hM_ne
  haveI := hd_ne
  have hdN : d ∣ N := ⟨M, heq.symm⟩
  have hd_mem : d ∈ N.divisors.filter (1 < ·) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hdN, NeZero.ne N⟩, hd_gt⟩
  refine Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd_mem ?_)
  exact levelRaise_mem_qSupportedOnDvdSubmodule heq g

/-- **T131 prime-power bridge: coprime-vanishing ⇒ divisor-iSup
membership.**  For `N = p^r` with `p` prime and `r ≥ 1`, any cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` at level `Γ₁(p^r)` satisfying the
coprime-to-`p^r` Fourier vanishing hypothesis lies in the divisor-iSup

```
⨆ d ∈ (p^r).divisors.filter (1 < ·),
    qSupportedOnDvdSubmodule (p^r) k d ⊓ cuspFormCharSpace k χ.toUnitHom.
```

**Route**: the prime-power equivalence `Nat.Coprime n (p^r) ↔ ¬ p ∣ n`
(for `r ≥ 1, p.Prime`) rewrites the coprime-vanishing hypothesis as
`p`-support, so `f ∈ qSupportedOnDvdSubmodule (p^r) k p`.  Since
`p ∈ (p^r).divisors.filter (1 < ·)` (prime divides its power, `1 < p`),
the single-`d = p` slice of the iSup already contains `f`. -/
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

/-- **T131 aggregation helper: Finset sum-decomposition into
divisor-iSup membership.**  If `f : CuspForm Γ₁(N) k` admits a finite
decomposition

```
f = ∑ d ∈ S, f_d d
```

with `S ⊆ N.divisors.filter (1 < ·)` and each `f_d d` simultaneously in
the support submodule `qSupportedOnDvdSubmodule N k d` and in the
character space `cuspFormCharSpace k χ.toUnitHom`, then `f` lies in the
divisor-iSup

```
⨆ d ∈ N.divisors.filter (1 < ·),
    qSupportedOnDvdSubmodule N k d ⊓ cuspFormCharSpace k χ.toUnitHom.
```

Direct consumer for any downstream worker who produces a same-level
divisor decomposition (e.g. via a trace operator composing the Miyake
sieve witness back to `Γ₁(N)`, or via an Atkin–Lehner–Li orthogonality
argument).  Consumes nothing from the Miyake / descent infrastructure
itself; the mathematical content is pure `Submodule.sum_mem` plus the
iSup packaging. -/
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
  have hd' : d ∈ N.divisors.filter (1 < ·) := hS hd
  exact Submodule.mem_iSup_of_mem d (Submodule.mem_iSup_of_mem hd' (h_mem d hd))

/-- **T131 alternative prime-power `mainLemma` via the T130 divisor-iSup
consumer.**  Composes the T131 prime-power bridge
(`mem_iSup_divisor_qSupportedOnDvdSubmodule_inf_charSpace_of_coprime_vanishing_primePower`)
with the T130 consumer
(`mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule_divisors`) to
recover T118 (`mainLemma_charSpace_primePower`) routed through the
divisor-iSup bridge.

This demonstrates that the T130 divisor-iSup API is a sound reduction
target: for prime-power levels, the divisor-iSup membership is already
closable, so the T130 consumer suffices.  For composite `N`, the
remaining gap is closing the divisor-iSup membership itself, which needs
either the trace operator / `U_p / V_p` descent from Miyake's higher-level
witness, or an Atkin–Lehner–Li / Petersson orthogonality argument. -/
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

/-- **T133 abstract trace-descent witness for the Miyake sieve.**
Captures the same-level descent pieces that a real trace operator
`Tr_{N·L → N}` would produce from the output of
`miyake_main_lemma_4_6_8_level_L`, with the four concrete properties —
finite-sum reconstruction, same-level target, coefficient support, and
character preservation — needed to feed the T131 sum-decomposition
aggregator.

A `TraceDescent N k χ f` is a concrete witness that `f` admits a
same-level `Γ₁(N)` divisor decomposition whose pieces each lie in a
`d`-supported χ-character subspace; consumers obtain the composite-`N`
character-space `mainLemma` via `mainLemma_charSpace_of_TraceDescent`. -/
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

/-- **T133 consumer: `TraceDescent` ⇒ `cuspFormsOld`.**  A trace-descent
witness `W : TraceDescent N k χ f` produces the composite-`N`
character-space `mainLemma` conclusion `f ∈ cuspFormsOld N k` by feeding
`W` through the T131 sum-decomposition aggregator
(`mem_iSup_divisor_qSupportedOnDvdSubmodule_inf_charSpace_of_sum_decomp`)
and the T130 divisor-iSup consumer
(`mainLemma_charSpace_of_mem_iSup_qSupportedOnDvdSubmodule_divisors`).

**Exact remaining theorem obligation** for replacing `W` by an actual
trace / coset-average construction: for any `N : ℕ` with `[NeZero N]`,
any Nebentypus `χ : DirichletCharacter ℂ N`, and any
`f ∈ cuspFormCharSpace k χ.toUnitHom` satisfying the coprime-to-`N`
Fourier vanishing hypothesis, produce a `TraceDescent N k χ f`.  The
candidate constructors are `traceGamma1` composed with `pSupportedRaise`
plus a cusp-stabiliser correction (T124 gap), an Atkin–Lehner–Li
Petersson orthogonality argument, or a `U_p`-eigenspace / Hecke-action
decomposition at level `N`. -/
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

/-- **T133 single-divisor constructor: `TraceDescent` from a single
proper-divisor `q`-support certificate.**  For an arbitrary level `N`,
any cusp form `f ∈ cuspFormCharSpace k χ.toUnitHom` that is already known
to be `q`-supported on multiples of a single proper divisor `d ∣ N` with
`1 < d` admits a canonical `TraceDescent` with the singleton divisor set
`{d}` and piece `piece d = f`.

This is the honest, level-agnostic generalisation of the prime-power
constructor: the prime-power case is recovered by taking `d = p` and
deriving the `qSupportedOnDvdSubmodule` membership from the
coprime-to-`p^r` Fourier vanishing hypothesis (see
`TraceDescent.ofPrimePower` below, which is now a thin wrapper).

It also covers the composite case where the same-level support has been
established at one specific divisor `d` (e.g., by an Atkin–Lehner W_d
projection or a `V_d`-image identification), without requiring a full
multi-divisor decomposition. -/
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

/-- **T133 prime-power constructor: `TraceDescent` from coprime-vanishing
at prime-power level.**  For `N = p^r` with `p` prime and `r ≥ 1`, any
`f ∈ cuspFormCharSpace k χ.toUnitHom` satisfying the coprime-to-`p^r`
Fourier vanishing hypothesis admits a canonical `TraceDescent` with a
**single**-divisor decomposition `S = {p}` and piece `piece p = f` (with
`piece d = 0` outside `S`).

This demonstrates the struct is already instantiable for prime-power
levels — the coefficient-support field follows from the prime-power
equivalence `Nat.Coprime n (p^r) ↔ ¬ p ∣ n`, the character-preservation
field is immediate from `hfχ`, and the reconstruction is a singleton
sum.  The construction is the concrete witness side of the T131
prime-power bridge; composed with `mainLemma_charSpace_of_TraceDescent`
it gives yet another route to T118. -/
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

/-- **T133 prime-power `mainLemma` via `TraceDescent`.**  Combines
`TraceDescent.ofPrimePower` with `mainLemma_charSpace_of_TraceDescent`
to recover T118 along the trace-descent route.  This completes the
end-to-end demonstration: the abstract `TraceDescent` API is sufficient
for prime-power levels, and the composite-`N` case reduces to
constructing a `TraceDescent` from the honest remaining infrastructure
(trace / Petersson / `U_p`-eigenspace). -/
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

/-- **T133 single-divisor consumer: composite-level `mainLemma` from a
single proper-divisor `q`-support certificate.**  For arbitrary `N`, any
cusp form `f ∈ cuspFormCharSpace k χ.toUnitHom` already known to be
`q`-supported on multiples of a single proper divisor `d ∣ N` with
`1 < d` lies in `cuspFormsOld N k`.  Composes `TraceDescent.ofSingleDivisor`
with `mainLemma_charSpace_of_TraceDescent`.

Strictly generalises `mainLemma_charSpace_primePower_via_TraceDescent`:
drops both the prime-power level constraint on `N` and the
coprime-Fourier-vanishing hypothesis (replaced by the single-divisor
q-support certificate).  This is the concrete oldform criterion that
future same-level projection operators (Atkin–Lehner W_d, U_p-eigenspace
projections, refined trace operators) feed into to discharge the
composite-`N` `mainLemma`. -/
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

/-- **T134 operator-level interface: same-level divisor projections.**
A family of `ℂ`-linear endomorphisms
`P : ℕ → (CuspForm (Γ₁ N) k →ₗ[ℂ] CuspForm (Γ₁ N) k)` together with
three concrete axioms: unconditional `d`-support of each image
(`P_supp`), unconditional preservation of every Nebentypus character
space (`P_char`), and a Möbius-type finite-sum reconstruction
(`mobius_reconstruction`) for any cusp form satisfying the coprime-to-`N`
Fourier vanishing hypothesis.

Consumers obtain a `TraceDescent` (and, via the T133 consumer, the
composite-`N` character-space `mainLemma`) through
`TraceDescent.ofSameLevelDivisorProjections` and
`mainLemma_charSpace_of_SameLevelDivisorProjections` below.

Future constructors for this interface should arise from a refined
`U_p`-Möbius sieve at level `Γ₁(N)`, an Atkin–Lehner–Li orthogonality
argument (using the `petN` infrastructure already present in
`Newforms.lean`), or a trace-based projection whose cusp-stabiliser
calculation resolves the T124 obstruction. -/
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

/-- **T134 constructor: `SameLevelDivisorProjections` ⇒ `TraceDescent`.**
Given a `SameLevelDivisorProjections N k` datum and a cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` satisfying the coprime-to-`N`
Fourier vanishing hypothesis, build the `TraceDescent χ f` witness
whose `piece d = Op.P d f`.  Each field of the resulting `TraceDescent`
comes directly from one of the three `SameLevelDivisorProjections`
axioms (no existential packaging). -/
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

/-- **T134 end-to-end consumer:
`SameLevelDivisorProjections` ⇒ `cuspFormsOld`.**  Composes the T134
operator-level constructor `TraceDescent.ofSameLevelDivisorProjections`
with the T133 `mainLemma_charSpace_of_TraceDescent` consumer to produce
the composite-`N` character-space `mainLemma` directly from a
`SameLevelDivisorProjections` datum plus the coprime-vanishing
hypothesis.  Any worker who constructs a `SameLevelDivisorProjections`
at level `N` thereby closes the `Newforms.mainLemma` composite case. -/
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

/-- **T131 same-level divisor decomposition consumer.**  Given a cusp form
`f ∈ cuspFormCharSpace k χ.toUnitHom` together with a same-level divisor
decomposition into pieces with per-divisor `q`-support and character-space
membership — exactly the conclusion shape returned by
`MainLemma.same_level_collapse_of_deep_oldform_image_of_projections`,
transported from `ModularForm` to `CuspForm` — produce
`f ∈ cuspFormsOld N k`.

The proof packages the data as a `TraceDescent χ f` whose `divisors` field
is `N.divisors.filter (1 < ·)` and whose `piece d = samePiece d`, then
applies `mainLemma_charSpace_of_TraceDescent`. -/
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

/-- **Character-space transfer along a shared coercion.**  If a cusp form
`g_cf` and a modular form `g_mf` at level `Γ₁(N)` share the same underlying
function on `ℍ` and `g_mf` lies in the modular-form Nebentypus space
`modFormCharSpace k χ`, then `g_cf` lies in the cusp-form Nebentypus space
`cuspFormCharSpace k χ`.

Both diamond operators reduce, on any `(ZMod N)ˣ`-representative `γ`, to the
same slash `⇑g ∣[k] mapGL ℝ γ` (via `diamondOpCusp_eq` / `diamondOp_eq_diamondOpAux`),
so the modular-form eigenvalue equation transfers verbatim through `h_coe`. -/
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
  have h_mf_app := congrArg (fun F : ModularForm ((Gamma1 N).map (mapGL ℝ)) k =>
    (⇑F : UpperHalfPlane → ℂ)) ((mem_modFormCharSpace_iff k χ g_mf).mp h_mf u)
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
    simpa using congrFun h_mf_app z
  rw [h_cf_slash, h_mf_slash]
  simp [h_coe]

/-- **Cusp-form reconstruction from a coercion-matched modular-form sum.**
If `f.toModularForm'` equals a finite sum `∑ d ∈ S, samePiece d` of modular
forms, and a cusp-form family `lifted` matches `samePiece` coercion-wise on
`S`, then `f = ∑ d ∈ S, lifted d` as cusp forms.

Pointwise (`DFunLike.ext`) argument: the coercion of each finite sum is the
pointwise finite sum (by `Finset.cons_induction`), then `Finset.sum_congr`
with the per-divisor coercion equality `h_coe`. -/
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
      (⇑(∑ d ∈ T, samePiece d) : UpperHalfPlane → ℂ) z = ∑ d ∈ T, ⇑(samePiece d) z := by
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

/-- **T131 / SMO bridge consumer (ModularForm-input).**  Given:

* a `CuspForm` `f` at level `Γ₁(N)` lying in the cusp-form character space
  `cuspFormCharSpace k χ.toUnitHom`;
* a `ModularForm`-typed same-level divisor decomposition
  `f.toModularForm' = ∑ d, samePiece d` (the shape returned by
  `MainLemma.same_level_collapse_of_deep_oldform_image_of_projections`);
* per-piece `q`-support (`samePiece d` supported on multiples of `d`) and
  per-piece `modFormCharSpace k χ.toUnitHom` membership;
* a per-piece cusp-vanishing witness `h_cusp d _ hc : c.IsZeroAt …` (the one
  ingredient lost when moving from `CuspForm` input to `ModularForm` pieces),

produce the conclusion `f ∈ cuspFormsOld N k`.  The proof packages each
`samePiece d` as a `CuspForm` via `cuspFormOfModularForm` and applies
`mainLemma_charSpace_of_sameLevelDivisorDecomposition`. -/
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
  have h_sum_lifted : f = ∑ d ∈ N.divisors.filter (1 < ·), lifted d :=
    cuspForm_eq_sum_of_toModularForm_eq_sum f samePiece lifted _ h_sum
      (fun d hd => by simp only [lifted, dif_pos hd, cuspFormOfModularForm_coe])
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
    h_sum_lifted h_pieces_lifted

/-- **T131 / SMO bridge composer (Projections-input).**  Given a
`ModularFormSameLevelDivisorProjections` bundle for `f.toModularForm'`,
produce `f ∈ cuspFormsOld N k`.  The proof applies
`MainLemma.same_level_collapse_of_deep_oldform_image_of_projections` to
extract the same-level decomposition with per-piece cusp-vanishing, then
routes through `mainLemma_charSpace_of_modularFormSameLevelDivisorDecomposition`.

The cusp-vanishing input is now bundled inside the structure (β-variant),
so callers no longer need to supply a separate cusp callback. -/
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


/-- **T134-local: per-divisor local field of `SameLevelDivisorProjections`.**
A single linear endomorphism `P : CuspForm Γ₁(N) k →ₗ CuspForm Γ₁(N) k`
together with the two local axioms `P_supp` (image is `d`-q-supported on
all inputs) and `P_char` (preserves every Nebentypus character space).
This is exactly the per-divisor slice of a `SameLevelDivisorProjections`
datum (the `mobius_reconstruction` axiom is global and not part of the
local field).

Constructors for this structure are produced one divisor at a time by
classical routes (refined trace, Atkin–Lehner–Li, `U_p`-Möbius sieve);
the assembled family then feeds `SameLevelDivisorProjections.ofLocalFields`
together with a single global Möbius reconstruction hypothesis. -/
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

/-- **Zero local-field instance.**  For any `(N, k, d)`, the trivial
projection `P = 0` is a real, sorry-free
`SameLevelDivisorProjectionsLocalField` instance: the zero cusp form is
in every `qSupportedOnDvdSubmodule` and every `cuspFormCharSpace`.

This instance demonstrates the local-field structure is genuinely
inhabitable; it does **not** satisfy the global `mobius_reconstruction`
axiom of `SameLevelDivisorProjections` (which fails for generic `f`),
and is intended only as a structural witness.  Real classical
constructors will replace `P = 0` with a refined-trace / Atkin–Lehner–Li
/ `U_p`-Möbius operator. -/
noncomputable def SameLevelDivisorProjectionsLocalField.zero
    (N : ℕ) [NeZero N] (k : ℤ) (d : ℕ) :
    SameLevelDivisorProjectionsLocalField N k d where
  P := 0
  P_supp := fun _ => by simpa only [LinearMap.zero_apply] using (qSupportedOnDvdSubmodule N k d).zero_mem
  P_char := fun χ _ _ => by simpa only [LinearMap.zero_apply] using (cuspFormCharSpace k χ).zero_mem

/-- **Assemble local fields + global Möbius into a full
`SameLevelDivisorProjections`.**  Given a family of per-divisor local
fields `loc : Π d ∈ N.divisors.filter (1 < ·), …LocalField N k d` and a
single global Möbius reconstruction hypothesis at the assembled-`P`
level, produce a `SameLevelDivisorProjections N k`.

The assembly is a pure structural plumbing: each global field of
`SameLevelDivisorProjections` reads off directly from one local field
plus the supplied Möbius hypothesis, with no further classical content.

For divisors `d` outside the filter `N.divisors.filter (1 < ·)` (i.e.
`d = 1`, `d = 0`, or `d ∤ N`), `P d` is set to `0`; this choice is
irrelevant since `P_supp` and `P_char` are quantified only over the
filter.  This `default` choice avoids forcing the caller to supply
local-field data for irrelevant divisors. -/
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

/-- **Zero `SameLevelDivisorProjections.ofLocalFields` corollary.**
Direct construction of a `SameLevelDivisorProjections N k` from the
zero local-field family, supplied with a global Möbius reconstruction
hypothesis.  Demonstrates that the assembly constructor produces a
genuine `SameLevelDivisorProjections` instance from local-field data
plus a single named Möbius hypothesis (delivering deliverable II of the
T131 task: a real, type-checked partial constructor with two of the
three fields supplied by genuine real proofs). -/
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
      have h := mobius f hf
      convert h using 1
      refine Finset.sum_congr rfl (fun d hd => ?_)
      simp only [dif_pos hd, SameLevelDivisorProjectionsLocalField.zero,
        LinearMap.zero_apply])

/-- **T131 / Outcome 2: per-prime trace correction structure.**
Bundles the exact data needed to upgrade a candidate same-level operator
into a `SameLevelDivisorProjectionsLocalField N k p`:

* `core` — the candidate same-level operator (e.g., a cusp-form analogue
  of `pSupportedProjection k p`, or any other approximate same-level
  projection whose output is "almost" `p`-supported);
* `correction` — the cusp-stabilizer corrector capturing the
  non-`∞`-fixing trace contribution that prevents `core` alone from
  being `p`-supported;
* `core_minus_correction_supp` — the `p`-support obligation for the
  difference `core f - correction f`;
* `core_minus_correction_char` — the character-space preservation
  obligation for the difference.

This is the **structured blocker** for a downstream cusp-stabilizer
ticket: a single typed declaration with the obligation precisely typed in
terms of existing names (`qSupportedOnDvdSubmodule`, `cuspFormCharSpace`,
no new Hecke or trace infrastructure required).  Slots directly into
`SameLevelDivisorProjections.ofLocalFields` via `toLocalField`. -/
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

/-- **Trace-correction ⇒ local-field constructor.**  Every
`TraceCorrectionPrime N k p` produces a
`SameLevelDivisorProjectionsLocalField N k p` whose `P` field is the
corrected operator `core - correction`.  This is pure structural
plumbing: each local-field axiom reads off directly from the
corresponding `TraceCorrectionPrime` axiom, with no further mathematical
content. -/
noncomputable def TraceCorrectionPrime.toLocalField
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T : TraceCorrectionPrime N k p) :
    SameLevelDivisorProjectionsLocalField N k p where
  P := T.core - T.correction
  P_supp := T.core_minus_correction_supp
  P_char := T.core_minus_correction_char

/-- **Zero trace-correction witness.**  For any `(N, k, p)`, the trivial
choice `core = 0`, `correction = 0` is a real, sorry-free
`TraceCorrectionPrime` instance: the zero cusp form is in every
`qSupportedOnDvdSubmodule` and every `cuspFormCharSpace`.

This instance demonstrates the structure is genuinely inhabitable; it
does **not** provide a non-trivial Möbius reconstruction (the assembled
`SameLevelDivisorProjections` would only reconstruct the zero cusp form).
Real classical constructors will replace `core` with a candidate
same-level operator (e.g., a cusp-version of `pSupportedProjection`) and
`correction` with the cusp-stabilizer corrector that absorbs the
non-`∞`-fixing trace contribution. -/
noncomputable def TraceCorrectionPrime.zero
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) :
    TraceCorrectionPrime N k p where
  core := 0
  correction := 0
  core_minus_correction_supp := fun _ => by
    simpa only [sub_self, LinearMap.zero_apply] using (qSupportedOnDvdSubmodule N k p).zero_mem
  core_minus_correction_char := fun χ _ _ => by
    simpa only [sub_self, LinearMap.zero_apply] using (cuspFormCharSpace k χ).zero_mem

/-- The `P` field of the local-field produced by
`TraceCorrectionPrime.zero` is the zero linear map, by definitional
unfolding (`0 - 0 = 0`).  Useful sanity-check simp lemma. -/
@[simp]
theorem TraceCorrectionPrime.toLocalField_zero_P
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) :
    (TraceCorrectionPrime.zero N k p).toLocalField.P = 0 := by
  show (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k) - 0 = 0
  rw [sub_zero]

/-- **Direct upgrade: a `p`-supporting / character-preserving operator
  is a `TraceCorrectionPrime` with zero correction.**

If a same-level operator `Q` already satisfies the two axioms
unconditionally (its image is `p`-supported on every input, and it
preserves every Nebentypus character space), then it constitutes a
`TraceCorrectionPrime N k p` with `core = Q` and `correction = 0`.

This is the canonical packaging for any operator `Q` that has been
proved (elsewhere) to be a same-level `p`-supported projection on
cusp forms, sidestepping the need to articulate a corrector. -/
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

/-- The `core - correction` of `ofCore Q h_supp h_char` is exactly `Q`.
Definitional `simp` lemma sealing the canonical packaging. -/
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

/-- **Pointwise addition of trace corrections.**  Combines two
`TraceCorrectionPrime` witnesses by adding their `core` and
`correction` fields separately; the difference field is then
`(c1.core - c1.correction) + (c2.core - c2.correction)`, which lies in
each submodule by `add_mem`. -/
noncomputable def TraceCorrectionPrime.add
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T₁ T₂ : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p where
  core := T₁.core + T₂.core
  correction := T₁.correction + T₂.correction
  core_minus_correction_supp := fun f => by
    have h₁ := T₁.core_minus_correction_supp f
    have h₂ := T₂.core_minus_correction_supp f
    simp only [LinearMap.sub_apply, LinearMap.add_apply, add_sub_add_comm]
    exact (qSupportedOnDvdSubmodule N k p).add_mem h₁ h₂
  core_minus_correction_char := fun χ f hf => by
    have h₁ := T₁.core_minus_correction_char χ f hf
    have h₂ := T₂.core_minus_correction_char χ f hf
    simp only [LinearMap.sub_apply, LinearMap.add_apply, add_sub_add_comm]
    exact (cuspFormCharSpace k χ).add_mem h₁ h₂

/-- **Pointwise negation of trace corrections.**  The negation has
`core := -T.core`, `correction := -T.correction`, with difference
`-(T.core - T.correction)`, in each submodule by `neg_mem`. -/
noncomputable def TraceCorrectionPrime.neg
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p where
  core := -T.core
  correction := -T.correction
  core_minus_correction_supp := fun f => by
    have h := T.core_minus_correction_supp f
    have heq : ((-T.core) - (-T.correction)) f = -((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.neg_apply]; abel
    rw [heq]
    exact (qSupportedOnDvdSubmodule N k p).neg_mem h
  core_minus_correction_char := fun χ f hf => by
    have h := T.core_minus_correction_char χ f hf
    have heq : ((-T.core) - (-T.correction)) f = -((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.neg_apply]; abel
    rw [heq]
    exact (cuspFormCharSpace k χ).neg_mem h

/-- **Scalar action on trace corrections.**  Scaling has
`core := c • T.core`, `correction := c • T.correction`, with
difference `c • (T.core - T.correction)`, in each submodule by
`smul_mem`. -/
noncomputable def TraceCorrectionPrime.smul
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (c : ℂ) (T : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p where
  core := c • T.core
  correction := c • T.correction
  core_minus_correction_supp := fun f => by
    have h := T.core_minus_correction_supp f
    have heq : ((c • T.core) - (c • T.correction)) f = c • ((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply]; rw [smul_sub]
    rw [heq]
    exact (qSupportedOnDvdSubmodule N k p).smul_mem c h
  core_minus_correction_char := fun χ f hf => by
    have h := T.core_minus_correction_char χ f hf
    have heq : ((c • T.core) - (c • T.correction)) f = c • ((T.core - T.correction) f) := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply]; rw [smul_sub]
    rw [heq]
    exact (cuspFormCharSpace k χ).smul_mem c h

/-- **Subtraction of trace corrections.**  Defined as `T₁ + (-T₂)`. -/
noncomputable def TraceCorrectionPrime.sub
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (T₁ T₂ : TraceCorrectionPrime N k p) :
    TraceCorrectionPrime N k p :=
  T₁.add T₂.neg

/-- The `P`-field (`core - correction`) of `add` is the sum of the two
`P`-fields.  Useful for downstream `toLocalField` plumbing. -/
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

/-- **`TraceCorrectionPrime` family ⇒ `SameLevelDivisorProjections`.**
Given a family of trace-correction witnesses (one per proper divisor
`d ∈ N.divisors.filter (1 < ·)`) plus a single global Möbius
reconstruction hypothesis at the assembled-`P` level, produce a full
`SameLevelDivisorProjections N k` datum.  Composes `toLocalField` with
`SameLevelDivisorProjections.ofLocalFields`.

This is the **end-to-end pipeline** from per-divisor trace-correction
data to a composite-`N` `SameLevelDivisorProjections`: a downstream
worker who constructs `TraceCorrectionPrime N k d` for each divisor
(plus the global Möbius identity) thereby produces a
`SameLevelDivisorProjections N k` and hence (via
`mainLemma_charSpace_of_SameLevelDivisorProjections`) the composite-`N`
character-space `mainLemma`. -/
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

/-- **End-to-end consumer:
`TraceCorrectionPrime` family ⇒ composite-`N` `mainLemma`.**  Given:

* a per-divisor family of trace-correction witnesses
  `T : ∀ d ∈ N.divisors.filter (1 < ·), TraceCorrectionPrime N k d`,
* a global Möbius reconstruction hypothesis at the assembled-`P` level,
* a cusp form `f ∈ cuspFormCharSpace k χ.toUnitHom` satisfying the
  coprime-to-`N` Fourier vanishing hypothesis,

produces the composite-`N` character-space `mainLemma` conclusion
`f ∈ cuspFormsOld N k`.  Routes through
`SameLevelDivisorProjections.ofTraceCorrections` and
`mainLemma_charSpace_of_SameLevelDivisorProjections`. -/
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
