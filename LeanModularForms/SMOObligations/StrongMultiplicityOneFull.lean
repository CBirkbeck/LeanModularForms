/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations
import LeanModularForms.HeckeRIngs.GL2.Unified.EigenformFromRing

/-!
# Strong Multiplicity One, full constant-multiple form (Miyake Theorem 4.6.12)

This file develops the **full** form of Strong Multiplicity One as stated by Miyake
(*Modular Forms*, 2nd ed., Springer SMM, 2006, Theorem 4.6.12, p. 163):

> Let `f` and `g` be elements of `S_k^♯(N, χ)` (the new subspace) and `S_k(N, χ)`
> (the full space), respectively. If `f` and `g` are common eigenfunctions of `T(n)`
> with the same eigenvalue for each `n` prime to some integer `L`, then `g` is a
> constant multiple of `f`.

Neither `f` nor `g` is assumed normalised; the conclusion is `g = c • f` for some
`c ∈ ℂ`.

This **builds on** the same-level normalised-newform uniqueness theorem
`HeckeRing.GL2.strongMultiplicityOne_axiom_clean` (Miyake Theorem 4.6.8 +
Atkin–Lehner uniqueness, route B) and **never modifies it**.

## Proof outline (Miyake pp. 163–164)

Normalise `a₁(f) = 1` (`Lemma 4.6.11`) and assume `N ∣ L`.  Decompose
`g = g⁽¹⁾ + g⁽²⁾` with `g⁽¹⁾ ∈ S_k^♯(N,χ)` (new) and `g⁽²⁾ ∈ S_k^♭(N,χ)` (old).
Both are common eigenfunctions with eigenvalue `aₙ` for `(n,L)=1` (`Lemma 4.6.10`).

* **New part.** If `g⁽¹⁾ ≠ 0`, its leading coefficient `b₁ ≠ 0` (`Lemma 4.6.11`); then
  `g⁽¹⁾ - b₁ • f` has vanishing coprime coefficients (`Lemma 4.5.15(1)`), so it lies in
  the old space (`Theorem 4.6.8`).  Being also new, it is `0`, hence `g⁽¹⁾ = b₁ • f`.
* **Old part is zero.** If `N = m_χ`, the old space is `0` (`Lemma 4.6.9(1)`).  Otherwise
  one descends `g⁽²⁾` to a nonzero new eigenform `h ∈ S_k^♯(M,χ)` at a proper divisor
  `M` (`Lemma 4.6.9(3)`, `Lemma 4.6.2`, linear independence of distinct-eigenvalue
  eigenforms), then `h - c₁' • f ∈ old(N)` and `h ∈ old(N)` force `f ∈ old(N)`,
  contradicting `f` new and nonzero.  Hence `g⁽²⁾ = 0` and `g = b₁ • f`.

## API gap (flagged)

Miyake's old space `S_k^♭(N,χ)` is, by definition, the span of `V_l`-images of the
**new** spaces `S_k^♯(M,χ)` over `m_χ ∣ M ∣ N`, `M ≠ N`, `l ∣ (N/M)` (p. 162).  The
project's `cuspFormsOld N k` (`Newforms/Basic.lean`) is instead the span of `levelRaise`
images of the **full** cusp spaces `S_k(Γ₁(M))` over all proper divisors `M` — a
character-agnostic, Diamond–Shurman-style definition.  Bridging the two (especially
`Lemma 4.6.9(1)`: old `= 0` for primitive `χ`) is the central API gap; see
`.mathlib-quality/decomposition.md` (gap #4) and `cuspFormsOldChar` below.

## References

* **[Miy]** T. Miyake, *Modular Forms*, 2nd ed., Springer SMM, 2006, §4.6.
* **[DS]**  F. Diamond, J. Shurman, *A First Course in Modular Forms*, GTM 228, 2005.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ}

/-! ## Lemma 4.5.15(1): `aₙ = a₁ · λₙ` for an un-normalised eigenform

Gap #1.  The normalised case (`a₁ = 1 ⟹ aₙ = λₙ`) is `Newform.eigenvalue_eq_coeff`
and `eigenvalue_eq_fourierCoeff_one`.  Here we need the un-normalised statement for an
`Eigenform` whose leading coefficient need not be `1`. -/

omit [NeZero N] in
/-- Period-1 strict-period membership for `Γ₁(N)` (local copy of the building block used
throughout the Fourier-coefficient API). -/
private lemma one_mem_strictPeriods_Gamma1_map_local :
    (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

omit [NeZero N] in
/-- `a₁(c • f) = c · a₁(f)` for the canonical (period-1) `q`-expansion of a cusp form, with
**no normalisation** assumption.  Un-normalised analogue of the `private`
`qExpansion_one_coeff_one_smul_of_norm` of `Newforms/MainLemma.lean`. -/
private lemma qExpansion_one_coeff_one_smul_local
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (c : ℂ) :
    (ModularFormClass.qExpansion (1 : ℝ) (c • f)).coeff 1 =
      c * (ModularFormClass.qExpansion (1 : ℝ) f).coeff 1 := by
  show (ModularFormClass.qExpansion (1 : ℝ) (⇑(c • f : CuspForm _ k))).coeff 1 =
      c * (ModularFormClass.qExpansion (1 : ℝ) (⇑f)).coeff 1
  rw [show (⇑(c • f : CuspForm _ k) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl,
    qExpansion_smul one_pos one_mem_strictPeriods_Gamma1_map_local, PowerSeries.coeff_smul,
    smul_eq_mul]

/-- `a₁(T_n f) = a_n(f)` for the canonical (period-1) `q`-expansion of a cusp form lying in a
single Nebentypus eigenspace, `(n, N) = 1`.  Local copy of the `private`
`qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff` of `Newforms/MainLemma.lean`. -/
private lemma qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff_local
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_char : f.toModularForm' ∈ modFormCharSpace k χ) :
    (ModularFormClass.qExpansion (1 : ℝ) (heckeT_n_cusp k n f)).coeff 1 =
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n := by
  rw [show (⇑(heckeT_n_cusp k n f) : UpperHalfPlane → ℂ) =
        ⇑(heckeT_n_cusp k n f).toModularForm' from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl,
    heckeT_n_cusp_toModularForm']
  have h := fourierCoeff_heckeT_n_period_one (N := N) k n hn χ hf_char 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] at h
  exact h

/-- **Miyake Lemma 4.5.15(1)** (un-normalised form, period 1).  For an `Eigenform g`
lying in the Nebentypus space `χ` and `n` coprime to the level, the `n`-th Fourier
coefficient equals the leading coefficient times the classical Hecke eigenvalue:
`aₙ(g) = a₁(g) · λₙ(g)`. -/
theorem Eigenform.coeff_eq_coeff_one_mul_eigenvalue
    (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (n : ℕ+) (hn : Nat.Coprime n.val N) :
    (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff n.val =
      (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 * g.eigenvalue n := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  -- `a₁(T_n g) = a₁(λₙ • g) = λₙ · a₁(g)`; combined with `a₁(T_n g) = a_n(g)`:
  have h_lhs : (ModularFormClass.qExpansion (1 : ℝ)
      (heckeT_n_cusp k n.val g.toCuspForm)).coeff 1 =
      g.eigenvalue n * (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 := by
    rw [g.isEigen n hn]
    exact qExpansion_one_coeff_one_smul_local g.toCuspForm _
  rw [← qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff_local n.val hn χ g.toCuspForm hgχ,
    h_lhs, mul_comm]

/-! ## Lemma 4.6.11: a nonzero new eigenform has `a₁ ≠ 0`

Gap #2.  Proof: if `a₁ = 0`, then `aₙ = 0` for all `(n,L)=1` by 4.5.15(1), so the form
lies in the old space by Theorem 4.6.8; being also new and nonzero contradicts
`cuspFormsOld_disjoint_cuspFormsNew`. -/

/-- **Miyake Lemma 4.6.11** (`Eigenform`/`cuspFormsNew` form).  A nonzero common
eigenfunction in the new subspace has nonvanishing leading Fourier coefficient.

The `h_chi_factor` hypothesis encodes Miyake's character-conductor restriction (p. 160)
and is required by the route-B Main Lemma (`mainLemma_charSpace_routeB`). -/
theorem coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen
    (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hg_new : g.toCuspForm ∈ cuspFormsNew N k)
    (hg_ne : g.toCuspForm ≠ 0)
    (L : ℕ)
    (hNL : N ∣ L)
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 ≠ 0 := by
  -- Contrapositive: if `a₁(g) = 0` then `aₙ(g) = 0` for all `(n,N)=1` (Lemma 4.5.15(1)),
  -- so `g ∈ cuspFormsOld N k` (Theorem 4.6.8, route B); but `g` is new and nonzero,
  -- contradicting `cuspFormsOld_disjoint_cuspFormsNew`.
  intro h1
  have hgχ_cusp : g.toCuspForm ∈ cuspFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
      g.toCuspForm).mp (by convert hgχ using 1)
  have h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      rw [ModularFormClass.qExpansion_coeff_zero _ one_pos
            one_mem_strictPeriods_Gamma1_map_local,
        (CuspFormClass.zero_at_infty g.toCuspForm).valueAtInfty_eq_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hcoeff := Eigenform.coeff_eq_coeff_one_mul_eigenvalue g χ hgχ ⟨n, hn_pos⟩ hn
      rw [h1, zero_mul] at hcoeff
      exact hcoeff
  have h_old : g.toCuspForm ∈ cuspFormsOld N k :=
    mainLemma_charSpace_routeB χ g.toCuspForm hgχ_cusp h_vanish h_chi_factor
  exact hg_ne (Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _ h_old hg_new)

/-- **Miyake Lemma 4.6.11, unconditional `Eigenform`/`cuspFormsNew` form.**  As
`coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen`, but with the `h_chi_factor`
hypothesis **removed**: it relies on the per-character unconditional Main Lemma
`mainLemma_charSpace_routeB_unconditional` (Deliverable 1).

A nonzero common eigenfunction in the new subspace has nonvanishing leading Fourier
coefficient.  Proof: if `a₁(g) = 0` then `aₙ(g) = 0` for all `(n,N)=1` (Lemma 4.5.15(1)),
so `g ∈ cuspFormsOld N k`; being also new and nonzero, this contradicts
`cuspFormsOld_disjoint_cuspFormsNew`. -/
theorem coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen_unconditional
    (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hg_new : g.toCuspForm ∈ cuspFormsNew N k)
    (hg_ne : g.toCuspForm ≠ 0) :
    (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 ≠ 0 := by
  intro h1
  have hgχ_cusp : g.toCuspForm ∈ cuspFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
      g.toCuspForm).mp (by convert hgχ using 1)
  have h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      rw [ModularFormClass.qExpansion_coeff_zero _ one_pos
            one_mem_strictPeriods_Gamma1_map_local,
        (CuspFormClass.zero_at_infty g.toCuspForm).valueAtInfty_eq_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hcoeff := Eigenform.coeff_eq_coeff_one_mul_eigenvalue g χ hgχ ⟨n, hn_pos⟩ hn
      rw [h1, zero_mul] at hcoeff
      exact hcoeff
  have h_old : g.toCuspForm ∈ cuspFormsOld N k :=
    mainLemma_charSpace_routeB_unconditional χ g.toCuspForm hgχ_cusp h_vanish
  exact hg_ne (Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _ h_old hg_new)

/-! ## Lemma 4.6.2: `V_l` preserves common eigenfunctions and their eigenvalues

Gap #3.  `levelRaise M l k` is Miyake's `V_l : f ↦ f(l·)`.  The Hecke commutation
`heckeT_n_levelRaise_comm` already holds (`Newforms/LevelRaiseComm.lean`); this lemma is
its eigenvalue corollary. -/

/-- **Miyake Lemma 4.6.2** (eigenvalue-preservation form).  If `h` is a `T_n`-eigenform
at level `M` with eigenvalue `λ` for some `(n, l*M) = 1`, then its level-raise
`V_l h = h(l·)` is a `T_n`-eigenform at level `l*M` with the same eigenvalue. -/
theorem heckeT_n_levelRaise_eigen
    {M : ℕ} [NeZero M] {l : ℕ} [NeZero l] (heq : l * M = N)
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (lam : ℂ)
    (h_eig : haveI : NeZero n := ⟨(NeZero.ne n)⟩
      heckeT_n_cusp k n h = lam • h) :
    heckeT_n_cusp k n (heq ▸ levelRaise M l k h) = lam • (heq ▸ levelRaise M l k h) := by
  subst heq
  rw [heckeT_n_levelRaise_comm n hn M l rfl h, h_eig, map_smul]

/-! ## Lemma 4.6.9: the character-refined old space `S_k^♭(N,χ)`  — API GAP #4

This is the structurally hardest part.  Miyake's old space is **not** the project's
`cuspFormsOld N k`; it is the χ-refined, new-subspace-based span below. -/

/-- **Miyake's old space** `S_k^♭(N,χ)` (p. 162): the submodule of `cuspFormCharSpace k χ`
spanned by `V_l`-images of the **new** subspaces at proper divisor levels `M` that are
multiples of the conductor `m_χ`.

This is the character-conductor-refined analogue of the project's `cuspFormsOld N k`;
relating the two is gap #4 (see `cuspFormsOldChar_le_cuspFormsOld`). -/
def cuspFormsOldChar (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (m_χ : ℕ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ
    {f | ∃ (M : ℕ) (l : ℕ) (_ : NeZero M) (_ : NeZero l)
        (_hcond : m_χ ∣ M) (_hML : M ≠ N) (heq : l * M = N)
        (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
      g ∈ cuspFormsNew M k ∧ heq ▸ levelRaise M l k g = f}

/-- **Miyake Lemma 4.6.9(2)**: the new space at a proper divisor level `M` (multiple of
the conductor) embeds into the old space at level `N` via `V_l`. -/
theorem levelRaise_cuspFormsNew_le_cuspFormsOldChar
    (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    {M : ℕ} [NeZero M] {l : ℕ} [NeZero l]
    (hcond : m_χ ∣ M) (hML : M ≠ N) (heq : l * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hg_new : g ∈ cuspFormsNew M k) :
    (heq ▸ levelRaise M l k g) ∈ cuspFormsOldChar N k χ m_χ :=
  Submodule.subset_span
    ⟨M, l, ‹NeZero M›, ‹NeZero l›, hcond, hML, heq, g, hg_new, rfl⟩

/-- **Miyake Lemma 4.6.9(1)**: if `χ` is primitive of conductor `N` (`m_χ = N`), then the
old space is trivial, equivalently the whole χ-space is new.  (The new∩old decomposition
then forces `S_k^♭(N,χ) = 0`.) -/
theorem cuspFormsOldChar_eq_bot_of_conductor_eq
    (χ : DirichletCharacter ℂ N)
    (hcond : χ.conductor = N) :
    cuspFormsOldChar N k χ.toUnitHom χ.conductor = ⊥ := by
  rw [hcond, cuspFormsOldChar, Submodule.span_eq_bot]
  rintro f ⟨M, l, _, _, hMdvd, hMne, heq, g, -, rfl⟩
  exact absurd (Nat.dvd_antisymm hMdvd ⟨l, by rw [← heq, Nat.mul_comm]⟩).symm hMne

/-! ## New eigenform decomposition (spectral input for step (i))

Every **new** cusp form lying in a Nebentypus space `S_k(Γ₁(N),χ)` is a finite sum of
common Hecke eigenforms that are **themselves new**.  This is the spectral input consumed
by Theorem 4.6.12's descent: T008 `span_induction`s over the `cuspFormsOldChar`
generators `Vₗ(g)`, applies this lemma per generator `g`, and `Vₗ`-distributes the
resulting eigenforms via Lemma 4.6.2 (`heckeT_n_levelRaise_eigen`). -/

/-- **New eigenbasis decomposition.**  A new cusp form `g ∈ S_k^♯(N)` whose underlying
modular form lies in the Nebentypus space `M_k(Γ₁(N),χ)` is a finite sum of common Hecke
eigenforms, each of which is again **new** (lies in `S_k^♯(N)`).

Proof: the new subspace is `T_n`-invariant (`heckeT_n_preserves_cuspFormsNew`), so the
simultaneous Hecke diagonalisation of `S_k(Γ₁(N),χ)`
(`exists_eigenform_decomposition_of_invariant`) restricts to it, yielding eigenform
summands that remain new. -/
theorem exists_eigenform_decomposition_mem_cuspFormsNew
    (χ : (ZMod N)ˣ →* ℂˣ)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_new : g ∈ cuspFormsNew N k)
    (hgχ : g.toModularForm' ∈ modFormCharSpace k χ) :
    ∃ (ι : Type) (_ : Fintype ι) (h : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      (∀ i, h i ∈ cuspFormsNew N k) ∧ (∀ i, h i ∈ cuspFormCharSpace k χ) ∧
        (∀ i, IsEigenform (h i)) ∧ g = ∑ i, h i := by
  have hg_char : g ∈ cuspFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ g).mp
      (by convert hgχ using 1)
  obtain ⟨ι, hι, h, h_new, h_char, h_eigen, h_sum⟩ :=
    exists_eigenform_decomposition_of_invariant χ (cuspFormsNew N k)
      (fun n _ hn f hf ↦ heckeT_n_preserves_cuspFormsNew n hn f hf) g hg_char hg_new
  exact ⟨ι, hι, h, h_new, h_char, fun i ↦ (isEigenform_iff (h i)).mpr (h_eigen i), h_sum⟩

/-- The level-raise of a single-character cusp form lands in the lifted character space at the
deeper level (Atkin–Lehner; the diamond operator commutes with `V_d` up to the unit map). -/
private theorem levelRaise_mem_cuspFormCharSpace_comp {M : ℕ} [NeZero M] {d : ℕ} [NeZero d]
    {k : ℤ} {N : ℕ} [NeZero N] (heq : d * M = N) (ψ : (ZMod M)ˣ →* ℂˣ)
    {g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hg : g ∈ cuspFormCharSpace k ψ) :
    (heq ▸ levelRaise M d k g) ∈
      cuspFormCharSpace k (ψ.comp (ZMod.unitsMap (heq ▸ Nat.dvd_mul_left M d))) := by
  rw [mem_cuspFormCharSpace_iff]
  intro a
  rw [show diamondOpCuspHom k a (heq ▸ levelRaise M d k g) =
        diamondOp_cusp k a (heq ▸ levelRaise M d k g) from rfl,
    diamondOp_levelRaise_eq a M d heq g,
    show diamondOpCusp k (ZMod.unitsMap (heq ▸ Nat.dvd_mul_left M d) a) g =
        diamondOpCuspHom k (ZMod.unitsMap (heq ▸ Nat.dvd_mul_left M d) a) g from rfl,
    diamondOpCusp_apply_charSpace k ψ _ hg, map_smul]
  subst heq; rfl

/-- Diamond/level-inclusion commutation: `⟨a⟩_N (ι_{M∣N} g) = ι_{M∣N} (⟨a'⟩_M g)`,
where `a' = unitsMap a` is the cast of `a` from `(ZMod N)ˣ` to `(ZMod M)ˣ`.  This is the
trivial-inclusion analogue of `diamondOp_levelRaise_eq`: since `ι_{M∣N}` does not change
the underlying function, both diamond operators slash by the **same** `Γ₀(N) ⊆ Γ₀(M)`
representative of `a`. -/
private theorem diamondOpCusp_levelInclude_cusp_eq {M : ℕ} [NeZero M] {N : ℕ} [NeZero N]
    {k : ℤ} (hMN : M ∣ N) (a : (ZMod N)ˣ)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    diamondOpCusp k a (levelInclude_cusp hMN k g) =
      levelInclude_cusp hMN k (diamondOpCusp k (ZMod.unitsMap hMN a) g) := by
  -- A common representative `g_N ∈ Γ₀(N)` of `a`, also lying in `Γ₀(M)` (since `M ∣ N`).
  obtain ⟨g_N, hg_N⟩ := Gamma0MapUnits_surjective (N := N) a
  have hg_N_M : (g_N : SL(2, ℤ)) ∈ Gamma0 M := by
    rw [Gamma0_mem]
    have hN0 : ((g_N : SL(2, ℤ)).val 1 0 : ZMod N) = 0 := Gamma0_mem.mp g_N.property
    have hNdvd : (N : ℤ) ∣ (g_N : SL(2, ℤ)).val 1 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp (by exact_mod_cast hN0)
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr
      (dvd_trans (Int.natCast_dvd_natCast.mpr hMN) hNdvd)
  -- At level `M`, the same representative carries `unitsMap a`.
  have h_units : Gamma0MapUnits (⟨(g_N : SL(2, ℤ)), hg_N_M⟩ : ↥(Gamma0 M)) =
      ZMod.unitsMap hMN a := by
    apply Units.ext
    rw [Gamma0MapUnits_val, ZMod.unitsMap_val, ← hg_N, Gamma0MapUnits_val]
    exact (ZMod.cast_intCast hMN ((g_N : SL(2, ℤ)).val 1 1)).symm
  -- Both sides equal `⇑g ∣[k] mapGL ℝ g_N` as functions.
  have hL : ⇑(diamondOpCusp k a (levelInclude_cusp hMN k g)) =
      ⇑(levelInclude_cusp hMN k g) ∣[k] mapGL ℝ (g_N : SL(2, ℤ)) := by
    rw [diamondOpCusp_eq k a g_N hg_N]; rfl
  have hR : ⇑(diamondOpCusp k (ZMod.unitsMap hMN a) g) =
      ⇑g ∣[k] mapGL ℝ (g_N : SL(2, ℤ)) := by
    rw [diamondOpCusp_eq k (ZMod.unitsMap hMN a) ⟨(g_N : SL(2, ℤ)), hg_N_M⟩ h_units]; rfl
  apply CuspForm.ext; intro z
  have hgoalL : (diamondOpCusp k a (levelInclude_cusp hMN k g)) z =
      (⇑g ∣[k] mapGL ℝ (g_N : SL(2, ℤ))) z := DFunLike.congr_fun hL z
  have hgoalR : (levelInclude_cusp hMN k (diamondOpCusp k (ZMod.unitsMap hMN a) g)) z =
      (⇑g ∣[k] mapGL ℝ (g_N : SL(2, ℤ))) z := by
    rw [show (levelInclude_cusp hMN k (diamondOpCusp k (ZMod.unitsMap hMN a) g) :
        UpperHalfPlane → ℂ) z = (diamondOpCusp k (ZMod.unitsMap hMN a) g) z from
      congr_fun (levelInclude_cusp_coe hMN k _) z]
    exact DFunLike.congr_fun hR z
  rw [hgoalL, hgoalR]

/-- The trivial level inclusion of a single-character cusp form lands in the lifted character
space (Miyake Lemma 4.6.9(2): the trivial inclusion preserves Nebentypus). -/
private theorem levelInclude_cusp_mem_cuspFormCharSpace_comp {M : ℕ} [NeZero M] {N : ℕ}
    [NeZero N] {k : ℤ} (hMN : M ∣ N) (ψ : (ZMod M)ˣ →* ℂˣ)
    {g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hg : g ∈ cuspFormCharSpace k ψ) :
    levelInclude_cusp hMN k g ∈ cuspFormCharSpace k (ψ.comp (ZMod.unitsMap hMN)) := by
  rw [mem_cuspFormCharSpace_iff]
  intro a
  rw [show diamondOpCuspHom k a (levelInclude_cusp hMN k g) =
        diamondOpCusp k a (levelInclude_cusp hMN k g) from rfl,
    diamondOpCusp_levelInclude_cusp_eq hMN a g,
    show diamondOpCusp k (ZMod.unitsMap hMN a) g =
        diamondOpCuspHom k (ZMod.unitsMap hMN a) g from rfl,
    diamondOpCusp_apply_charSpace k ψ _ hg, map_smul]
  rfl

/-- The "level-raise eigen-decomposition" predicate carried through the `span_induction` of
`exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar` (Miyake 4.6.9(3)): `f` is a
finite sum of `V_l`-images of **new eigenforms** at proper divisor levels that are multiples
of `m_χ`.

Each summand additionally carries the level-`Mᵢ` Nebentypus character `χM i` of `hᵢ`
(so `hᵢ ∈ S_k(Γ₁(Mᵢ), χM i)`).  This is the character-tracking refinement needed for
Theorem 4.6.12 step (i): the level-`N` character of `Vₗᵢ(hᵢ)` is the pullback
`(χM i)∘unitsMap`, and combined with `charSpace_finset_sum_filter_eq`, the `χ`-isotypic
collapse drops the summands whose pulled-back character differs from `f`'s, leaving summands
in `cuspFormCharSpace k χ` on which the Petersson orthogonality engine applies. -/
private def LevelRaiseEigenDecomp (N : ℕ) [NeZero N] (k : ℤ) (m_χ : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (M : ι → ℕ) (l : ι → ℕ)
    (_ : ∀ i, NeZero (M i)) (_ : ∀ i, NeZero (l i))
    (_ : ∀ i, m_χ ∣ M i) (_ : ∀ i, M i ≠ N) (heq : ∀ i, l i * M i = N)
    (h : ∀ i, CuspForm ((Gamma1 (M i)).map (mapGL ℝ)) k)
    (χM : ∀ i, ((ZMod (M i))ˣ →* ℂˣ)),
    (∀ i, h i ∈ cuspFormsNew (M i) k) ∧
    (∀ i, IsEigenform (h i)) ∧
    (∀ i, h i ∈ cuspFormCharSpace k (χM i)) ∧
    f = ∑ i, (heq i ▸ levelRaise (M i) (l i) k (h i))

private theorem LevelRaiseEigenDecomp.zero (m_χ : ℕ) :
    LevelRaiseEigenDecomp N k m_χ (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, fun i ↦ i.elim, fun i ↦ i.elim,
    fun i ↦ i.elim, fun i ↦ i.elim, fun i ↦ i.elim, fun i ↦ i.elim, fun i ↦ i.elim,
    fun i ↦ i.elim, fun i ↦ i.elim, fun i ↦ i.elim, by simp⟩

private theorem LevelRaiseEigenDecomp.add (m_χ : ℕ)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : LevelRaiseEigenDecomp N k m_χ f) (hg : LevelRaiseEigenDecomp N k m_χ g) :
    LevelRaiseEigenDecomp N k m_χ (f + g) := by
  obtain ⟨ι₁, _, M₁, l₁, hM₁, hl₁, hc₁, hne₁, heq₁, h₁, χM₁, hnew₁, heig₁, hchar₁, hsum₁⟩ := hf
  obtain ⟨ι₂, _, M₂, l₂, hM₂, hl₂, hc₂, hne₂, heq₂, h₂, χM₂, hnew₂, heig₂, hchar₂, hsum₂⟩ := hg
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim M₁ M₂, Sum.elim l₁ l₂,
    Sum.rec hM₁ hM₂, Sum.rec hl₁ hl₂, Sum.rec hc₁ hc₂, Sum.rec hne₁ hne₂, Sum.rec heq₁ heq₂,
    Sum.rec h₁ h₂, Sum.rec χM₁ χM₂, Sum.rec hnew₁ hnew₂, Sum.rec heig₁ heig₂,
    Sum.rec hchar₁ hchar₂, ?_⟩
  rw [Fintype.sum_sum_type]
  exact congr_arg₂ (· + ·) hsum₁ hsum₂

private theorem LevelRaiseEigenDecomp.smul (m_χ : ℕ) (c : ℂ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : LevelRaiseEigenDecomp N k m_χ f) :
    LevelRaiseEigenDecomp N k m_χ (c • f) := by
  obtain ⟨ι, _, M, l, hM, hl, hc, hne, heq, h, χM, hnew, heig, hchar, hsum⟩ := hf
  refine ⟨ι, inferInstance, M, l, hM, hl, hc, hne, heq, fun i ↦ c • h i, χM,
    fun i ↦ (cuspFormsNew (M i) k).smul_mem c (hnew i), fun i ↦ ?_,
    fun i ↦ (cuspFormCharSpace k (χM i)).smul_mem c (hchar i), ?_⟩
  · obtain ⟨a, ha⟩ := heig i
    refine ⟨a, fun n hn ↦ ?_⟩
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    rw [heckeT_n_cusp_smul, ha n hn, smul_comm]
  · rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    rw [map_smul]
    haveI := hM i
    haveI := hl i
    generalize heq i = e
    subst e
    rfl

/-- **Miyake Lemma 4.6.9(3) (generation)**: every element of the χ-refined old space is a
finite sum of `V_l`-images of **eigenforms** in new spaces at proper divisor levels that
are multiples of `m_χ`.  This is the descent normal form used in step (i) of 4.6.12.

Each summand `hᵢ` additionally carries its level-`Mᵢ` Nebentypus character `χM i`
(`hᵢ ∈ cuspFormCharSpace k (χM i)`); this character-tracking is consumed by
4.6.12 step (i) (the `χ`-isotypic collapse of the orthogonality argument, via the level-`N`
pullback `(χM i)∘unitsMap`). -/
theorem exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar
    (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsOldChar N k χ m_χ) :
    ∃ (ι : Type) (_ : Fintype ι) (M : ι → ℕ) (l : ι → ℕ)
      (_ : ∀ i, NeZero (M i)) (_ : ∀ i, NeZero (l i))
      (_ : ∀ i, m_χ ∣ M i) (_ : ∀ i, M i ≠ N) (heq : ∀ i, l i * M i = N)
      (h : ∀ i, CuspForm ((Gamma1 (M i)).map (mapGL ℝ)) k)
      (χM : ∀ i, ((ZMod (M i))ˣ →* ℂˣ)),
      (∀ i, h i ∈ cuspFormsNew (M i) k) ∧
      (∀ i, IsEigenform (h i)) ∧
      (∀ i, h i ∈ cuspFormCharSpace k (χM i)) ∧
      f = ∑ i, (heq i ▸ levelRaise (M i) (l i) k (h i)) := by
  -- `cuspFormsOldChar` is spanned by `V_l`-images of new forms `g ∈ cuspFormsNew M`.
  -- Induct over the span: each generator `V_l(g)` is `χ`-decomposed into pieces
  -- `g_ψ ∈ cuspFormsNew M ⊓ S_k(Γ₁(M),ψ)`, each split into new eigenforms via T008a;
  -- `add`/`smul`/`zero` close by `LevelRaiseEigenDecomp.{add,smul,zero}`.
  suffices hP : LevelRaiseEigenDecomp N k m_χ f from hP
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨M, l, hM, hl, hcond, hMne, heq, g, hg_new, rfl⟩ := hx
    haveI : NeZero M := hM
    haveI : NeZero l := hl
    -- `χ`-decompose `g` into homogeneous pieces, then split each via the new eigenbasis.
    obtain ⟨cfs, hcfs_mem, hcfs_sum⟩ := exists_finsupp_charSpace_of_cuspFormsNew (N := M) k hg_new
    rw [← hcfs_sum]
    have hpush : (heq ▸ levelRaise M l k (cfs.sum fun _ y => y) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        ∑ ψ ∈ cfs.support, (heq ▸ levelRaise M l k (cfs ψ)) := by
      rw [Finsupp.sum, map_sum]
      subst heq; rfl
    rw [hpush]
    refine Finset.sum_induction _ (LevelRaiseEigenDecomp N k m_χ)
      (fun _ _ ↦ LevelRaiseEigenDecomp.add m_χ)
      (LevelRaiseEigenDecomp.zero m_χ) (fun ψ _ ↦ ?_)
    -- single homogeneous piece `g_ψ`: split into new eigenforms via T008a, then `V_l`-raise.
    have hgψ_new : cfs ψ ∈ cuspFormsNew M k := (hcfs_mem ψ).1
    have hgψ_char : (cfs ψ).toModularForm' ∈ modFormCharSpace k ψ :=
      (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) ψ
        (cfs ψ)).mpr (hcfs_mem ψ).2
    obtain ⟨ι, hι, hh, hh_new, hh_char, hh_eig, hh_sum⟩ :=
      exists_eigenform_decomposition_mem_cuspFormsNew ψ (cfs ψ) hgψ_new hgψ_char
    refine ⟨ι, hι, fun _ ↦ M, fun _ ↦ l, fun _ ↦ hM, fun _ ↦ hl, fun _ ↦ hcond,
      fun _ ↦ hMne, fun _ ↦ heq, hh, fun _ ↦ ψ, hh_new, hh_eig, hh_char, ?_⟩
    rw [hh_sum, map_sum]
    subst heq; rfl
  | zero => exact LevelRaiseEigenDecomp.zero m_χ
  | add _ _ _ _ ihx ihy => exact LevelRaiseEigenDecomp.add m_χ ihx ihy
  | smul c _ _ ihx => exact LevelRaiseEigenDecomp.smul m_χ c ihx

/-- **Gap #4 bridge.**  The χ-refined old space is contained in the project's
character-agnostic `cuspFormsOld N k`.  This lets the new-part argument and the
final contradiction in 4.6.12 reuse the existing `cuspFormsOld_disjoint_cuspFormsNew`
and route-B Main Lemma without re-deriving them for `cuspFormsOldChar`.

(One inclusion suffices for the proof of 4.6.12; the reverse inclusion — that every
project-oldform in the χ-space is a Miyake-oldform — is NOT needed and is harder.) -/
theorem cuspFormsOldChar_le_cuspFormsOld
    (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ) :
    cuspFormsOldChar N k χ m_χ ≤ cuspFormsOld N k := by
  -- `χ` records the intended Nebentypus of the source spaces; it is currently
  -- not referenced by `cuspFormsOldChar`'s body (the project's `cuspFormsNew`
  -- is character-agnostic) — see decomposition.md gap #4.
  rw [cuspFormsOldChar, cuspFormsOld]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨M, l, hM, hl, -, hMne, heq, g, -, rfl⟩
  -- Each `cuspFormsOldChar` generator is a `cuspFormsOld` generator once we know `1 < l`.
  have hl1 : 1 < l := by
    rcases Nat.lt_or_ge 1 l with h | h
    · exact h
    · interval_cases l
      · exact absurd heq.symm (by simpa using (NeZero.ne N))
      · exact absurd (by simpa using heq) hMne
  exact Submodule.subset_span ⟨M, l, hM, hl, hl1, heq, g, rfl⟩

/-! ## Gap #4, reverse inclusion (T012): `cuspFormsOld ⊓ charSpace χ ≤ cuspFormsOldChar`

This is the **Atkin–Lehner–Li** new/old structure theorem: the project's
character-agnostic Diamond–Shurman old space, intersected with the `χ`-Nebentypus space,
sits inside Miyake's `χ`-refined old space `S_k^♭(N,χ)`.  Together with the proven forward
`cuspFormsOldChar_le_cuspFormsOld` it makes `strongMultiplicityOne_constMul` unconditional.

Proof strategy (two phases):

* **Phase 1 (character-agnostic recursion).**  `cuspFormsOld N k ≤ oldNewGenSpan N k`, where
  `oldNewGenSpan` is spanned by `V_l`-images of the **new** spaces at proper divisor levels.
  By strong induction on `N`: each generator `V_d(g)` splits as `V_d(oldPart g) + V_d(newPart g)`;
  the new piece is directly a generator, the old piece descends by the induction hypothesis at
  level `M = N/d < N` and folds back via level-raise associativity `V_d ∘ V_e = V_{d·e}`
  (`levelRaise_levelRaise`, Diamond–Shurman §5.6 Exercise 5.6.2 / Miyake 4.6.8 induction engine).

* **Phase 2 (the character).**  Refine the generators to be `χ`-homogeneous at the source
  (`oldNewGenSpan ≤ oldNewGenCharSpan`), then expand `f = Σ c_i · V_{l_i}(g_i)` with each
  `g_i ∈ cuspFormsNew M_i ⊓ S_k(Γ₁(M_i), ψ_i)`.  Each summand lies in the level-`N` character
  space `S_k(Γ₁(N), ψ_i∘unitsMap)`, so by character-space independence
  (`CuspForm_Gamma1_iSupIndep_charSpace`) the pieces with `ψ_i∘unitsMap ≠ χ` vanish in the sum.
  For a surviving piece, `χ` factors through `M_i`, forcing `m_χ = χ.conductor ∣ M_i`
  (Miyake 4.6.4 / `DirichletCharacter.conductor_dvd_of_mem_conductorSet`); hence each surviving
  `V_{l_i}(g_i)` is a generator of `cuspFormsOldChar` (`levelRaise_cuspFormsNew_le_cuspFormsOldChar`,
  Miyake 4.6.9(2)). -/

/-- Phase 1 target: the character-agnostic span of `V_l`-images of the **new** spaces at proper
divisor levels.  The recursive normal form of `cuspFormsOld` (Diamond–Shurman §5.6). -/
private noncomputable def oldNewGenSpan (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ
    {f | ∃ (M : ℕ) (l : ℕ) (_ : NeZero M) (_ : NeZero l) (_ : 1 < l) (heq : l * M = N)
        (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
      g ∈ cuspFormsNew M k ∧ heq ▸ levelRaise M l k g = f}

/-- Level-raising maps `oldNewGenSpan` into `oldNewGenSpan` at the deeper level, folding the two
iterated level-raises into one via `levelRaise_levelRaise`. -/
private theorem levelRaise_oldNewGenSpan_le {M : ℕ} [NeZero M] {d : ℕ} [NeZero d] {k : ℤ}
    {N : ℕ} [NeZero N] (hd1 : 1 < d) (heq : d * M = N)
    {y : CuspForm ((Gamma1 M).map (mapGL ℝ)) k} (hy : y ∈ oldNewGenSpan M k) :
    (heq ▸ levelRaise M d k y) ∈ oldNewGenSpan N k := by
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨M', e, hM', he, he1, heqM, h, hh_new, rfl⟩ := hz
    haveI : NeZero M' := hM'
    haveI : NeZero e := he
    have heq3 : (d * e) * M' = d * M := by rw [mul_assoc, heqM]
    have heq' : (d * e) * M' = N := by rw [heq3, heq]
    have hfold : (heq ▸ levelRaise M d k (heqM ▸ levelRaise M' e k h)) =
        heq' ▸ levelRaise M' (d * e) k h := by
      rw [levelRaise_levelRaise h heqM heq3]
      apply CuspForm.ext; intro τ
      rw [eqRec_cuspForm_apply, eqRec_cuspForm_apply, eqRec_cuspForm_apply]
    rw [hfold]
    exact Submodule.subset_span
      ⟨M', d * e, hM', ⟨Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne e)⟩,
        lt_of_lt_of_le hd1 (Nat.le_mul_of_pos_right d (Nat.pos_of_neZero e)),
        heq', h, hh_new, rfl⟩
  | zero =>
    have : (heq ▸ levelRaise M d k (0 : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
      rw [map_zero]; subst heq; rfl
    rw [this]
    exact (oldNewGenSpan N k).zero_mem
  | add z₁ z₂ _ _ ih₁ ih₂ =>
    rw [map_add]
    have : (heq ▸ ((levelRaise M d k) z₁ + (levelRaise M d k) z₂) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        (heq ▸ levelRaise M d k z₁) + (heq ▸ levelRaise M d k z₂) := by
      subst heq; rfl
    rw [this]
    exact Submodule.add_mem _ ih₁ ih₂
  | smul c z _ ih =>
    rw [map_smul]
    have : (heq ▸ (c • (levelRaise M d k) z) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = c • (heq ▸ levelRaise M d k z) := by
      subst heq; rfl
    rw [this]
    exact Submodule.smul_mem _ c ih

/-- Phase 1, auxiliary form for strong induction on the level `N` (the `NeZero N` instance is
threaded explicitly through the recursion). -/
private theorem cuspFormsOld_le_oldNewGenSpan_aux (k : ℤ) :
    ∀ N : ℕ, ∀ inst : NeZero N, @cuspFormsOld N inst k ≤ @oldNewGenSpan N inst k := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro inst
  rw [cuspFormsOld, Submodule.span_le]
  rintro f ⟨M, d, hM, hd, hd1, heq, g, rfl⟩
  haveI : NeZero M := hM
  haveI : NeZero d := hd
  have hMltN : M < N := by
    rw [← heq]; exact lt_mul_left (Nat.pos_of_neZero M) hd1
  have hsplit : g = oldPart g + newPart g := (oldPart_add_newPart g).symm
  have hraise : (heq ▸ levelRaise M d k g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      (heq ▸ levelRaise M d k (oldPart g)) + (heq ▸ levelRaise M d k (newPart g)) := by
    conv_lhs => rw [hsplit]
    rw [map_add]
    subst heq; rfl
  rw [hraise]
  refine Submodule.add_mem _ ?_ ?_
  · -- old piece: descend `oldPart g ∈ cuspFormsOld M k` via IH, then fold by associativity
    have hold : oldPart g ∈ oldNewGenSpan M k := IH M hMltN hM (oldPart_mem_cuspFormsOld g)
    exact levelRaise_oldNewGenSpan_le hd1 heq hold
  · -- new piece: `newPart g ∈ cuspFormsNew M k` is directly a generator
    exact Submodule.subset_span
      ⟨M, d, hM, hd, hd1, heq, newPart g, newPart_mem_cuspFormsNew g, rfl⟩

/-- **Phase 1 (Diamond–Shurman recursive old-space normal form).**  The project's
character-agnostic old space is spanned by `V_l`-images of the **new** subspaces at proper
divisor levels. -/
private theorem cuspFormsOld_le_oldNewGenSpan (N : ℕ) [NeZero N] (k : ℤ) :
    cuspFormsOld N k ≤ oldNewGenSpan N k :=
  cuspFormsOld_le_oldNewGenSpan_aux k N ‹NeZero N›

/-- The character-homogeneous refinement of `oldNewGenSpan`: spanned by `V_l`-images of
**single-character** new forms `g ∈ cuspFormsNew M k ⊓ S_k(Γ₁(M), ψ)`. -/
private noncomputable def oldNewGenCharSpan (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ
    {f | ∃ (M : ℕ) (l : ℕ) (_ : NeZero M) (_ : NeZero l) (_ : 1 < l) (heq : l * M = N)
        (ψ : (ZMod M)ˣ →* ℂˣ) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
      (g ∈ cuspFormsNew M k ∧ g ∈ cuspFormCharSpace k ψ) ∧
      heq ▸ levelRaise M l k g = f}

/-- Every `oldNewGenSpan` generator refines to a sum of character-homogeneous generators, by
`χ`-decomposing the source new form at its own level. -/
private theorem oldNewGenSpan_le_oldNewGenCharSpan (N : ℕ) [NeZero N] (k : ℤ) :
    oldNewGenSpan N k ≤ oldNewGenCharSpan N k := by
  rw [oldNewGenSpan, Submodule.span_le]
  rintro f ⟨M, l, hM, hl, hl1, heq, g, hg_new, rfl⟩
  haveI : NeZero M := hM
  haveI : NeZero l := hl
  obtain ⟨c, hc_mem, hc_sum⟩ := exists_finsupp_charSpace_of_cuspFormsNew (N := M) k hg_new
  rw [← hc_sum]
  have hpush : (heq ▸ levelRaise M l k (c.sum fun _ y => y) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      ∑ ψ ∈ c.support, (heq ▸ levelRaise M l k (c ψ)) := by
    rw [Finsupp.sum, map_sum]
    subst heq; rfl
  rw [hpush]
  refine Submodule.sum_mem _ (fun ψ _ => ?_)
  exact Submodule.subset_span
    ⟨M, l, hM, hl, hl1, heq, ψ, c ψ, ⟨(hc_mem ψ).1, (hc_mem ψ).2⟩, rfl⟩

open Classical in
/-- **Character-space isotypic collapse.**  If `f ∈ S_k(Γ₁(N), χ)` is a finite sum of pieces
each in some character space `S_k(Γ₁(N), ψ i)`, then `f` equals the sum of just the
`χ`-isotypic pieces; the others cancel by character-space independence. -/
private theorem charSpace_finset_sum_filter_eq {ι : Type} (s : Finset ι)
    (x : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (ψ : ι → (ZMod N)ˣ →* ℂˣ)
    (χ : (ZMod N)ˣ →* ℂˣ) (hx : ∀ i ∈ s, x i ∈ cuspFormCharSpace k (ψ i))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf_sum : f = ∑ i ∈ s, x i)
    (hf_char : f ∈ cuspFormCharSpace k χ) :
    f = ∑ i ∈ s.filter (fun i => ψ i = χ), x i := by
  have hdisj := (CuspForm_Gamma1_iSupIndep_charSpace (N := N) k).disjoint_biSup
    (x := χ) (y := {ψ' | ψ' ≠ χ}) (by simp)
  have hsplit : f = (∑ i ∈ s.filter (fun i => ψ i = χ), x i) +
      ∑ i ∈ s.filter (fun i => ψ i ≠ χ), x i := by
    rw [hf_sum, Finset.sum_filter_add_sum_filter_not s (fun i => ψ i = χ)]
  set a := ∑ i ∈ s.filter (fun i => ψ i = χ), x i with ha
  set b := ∑ i ∈ s.filter (fun i => ψ i ≠ χ), x i with hb
  have ha_char : a ∈ cuspFormCharSpace k χ :=
    Submodule.sum_mem _ (fun i hi => by
      obtain ⟨his, hiχ⟩ := Finset.mem_filter.mp hi; rw [← hiχ]; exact hx i his)
  have hb_sup : b ∈ ⨆ ψ' ∈ {ψ' | ψ' ≠ χ}, cuspFormCharSpace k ψ' :=
    Submodule.sum_mem _ (fun i hi => by
      obtain ⟨his, hiχ⟩ := Finset.mem_filter.mp hi
      exact Submodule.mem_iSup_of_mem (ψ i) (Submodule.mem_iSup_of_mem hiχ (hx i his)))
  have hb_char : b ∈ cuspFormCharSpace k χ := by
    have hbfa : b = f - a := by rw [hsplit]; abel
    rw [hbfa]; exact Submodule.sub_mem _ hf_char ha_char
  have hb0 : b = 0 := (Submodule.disjoint_def.mp hdisj) b hb_char hb_sup
  rw [hsplit, hb0, add_zero]

open Classical in
/-- **Phase 2.**  A character-homogeneous-generated old form in `S_k(Γ₁(N), χ)` lies in Miyake's
`χ`-refined old space, by the isotypic collapse plus the conductor divisibility from
Miyake 4.6.4. -/
private theorem oldNewGenCharSpan_inf_charSpace_le_cuspFormsOldChar
    (N : ℕ) [NeZero N] (k : ℤ) (χ : DirichletCharacter ℂ N) :
    oldNewGenCharSpan N k ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOldChar N k χ.toUnitHom χ.conductor := by
  rintro f ⟨hf_span, hf_char⟩
  obtain ⟨c, hc_sub, hc_sum⟩ := Submodule.mem_span_set.mp hf_span
  -- For each generator `mi` in the support, package the witness as: a level-N character
  -- `Ψ` carried by `mi`, with `mi ∈ S_k(Γ₁(N), Ψ)` and `Ψ = χ` forcing `mi` into `cuspFormsOldChar`.
  have key : ∀ mi ∈ c.support, ∃ Ψ : (ZMod N)ˣ →* ℂˣ,
      mi ∈ cuspFormCharSpace k Ψ ∧
      (Ψ = χ.toUnitHom → mi ∈ cuspFormsOldChar N k χ.toUnitHom χ.conductor) := by
    intro mi hmi
    obtain ⟨M, l, hM, hl, hl1, heq, ψ, g, ⟨hg_new, hg_char⟩, rfl⟩ := hc_sub hmi
    haveI : NeZero M := hM
    haveI : NeZero l := hl
    have hMdvd : M ∣ N := ⟨l, by rw [← heq, Nat.mul_comm]⟩
    refine ⟨ψ.comp (ZMod.unitsMap (heq ▸ Nat.dvd_mul_left M l)),
      levelRaise_mem_cuspFormCharSpace_comp heq ψ hg_char, fun hΨ => ?_⟩
    have hcomp : χ.toUnitHom = ψ.comp (ZMod.unitsMap hMdvd) := hΨ.symm
    have hcond : χ.conductor ∣ M := by
      have hfac : χ.FactorsThrough M := by
        rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hMdvd]
        intro u hu
        rw [MonoidHom.mem_ker] at hu ⊢
        rw [hcomp, MonoidHom.comp_apply, hu, map_one]
      exact χ.conductor_dvd_of_mem_conductorSet (NeZero.ne N)
        ((DirichletCharacter.mem_conductorSet_iff χ).mpr hfac)
    have hMne : M ≠ N := by
      rintro rfl
      have : l * M = 1 * M := by rw [one_mul]; exact heq
      exact absurd (mul_right_cancel₀ (NeZero.ne M) this) (Nat.ne_of_gt hl1)
    exact Submodule.subset_span ⟨M, l, hM, hl, hcond, hMne, heq, g, hg_new, rfl⟩
  set Ψ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k → ((ZMod N)ˣ →* ℂˣ) :=
    fun mi => if h : mi ∈ c.support then (key mi h).choose else 1 with hΨ_def
  have hΨ_char : ∀ mi ∈ c.support, c mi • mi ∈ cuspFormCharSpace k (Ψ mi) := by
    intro mi hmi
    simp only [hΨ_def, dif_pos hmi]
    exact Submodule.smul_mem _ _ (key mi hmi).choose_spec.1
  have hΨ_old : ∀ mi ∈ c.support, Ψ mi = χ.toUnitHom →
      c mi • mi ∈ cuspFormsOldChar N k χ.toUnitHom χ.conductor := by
    intro mi hmi hmiχ
    simp only [hΨ_def, dif_pos hmi] at hmiχ ⊢
    exact Submodule.smul_mem _ _ ((key mi hmi).choose_spec.2 hmiχ)
  have hf_sum : f = ∑ mi ∈ c.support, c mi • mi := by rw [← hc_sum, Finsupp.sum]
  have hcollapse := charSpace_finset_sum_filter_eq c.support (fun mi => c mi • mi) Ψ
    χ.toUnitHom hΨ_char hf_sum hf_char
  rw [hcollapse]
  exact Submodule.sum_mem _ (fun mi hmi =>
    hΨ_old mi (Finset.mem_filter.mp hmi).1 (Finset.mem_filter.mp hmi).2)

/-- **Gap #4, reverse inclusion (Miyake 4.6.12, T012).**  Every project-oldform in the
`χ`-Nebentypus space is a Miyake `χ`-oldform.  This is the reverse of the proven forward
`cuspFormsOldChar_le_cuspFormsOld`; together they identify the two old spaces on the
`χ`-isotypic part, making `strongMultiplicityOne_constMul` (Theorem 4.6.12) **unconditional**.

Proof: Phase 1 (`cuspFormsOld_le_oldNewGenSpan`, the Diamond–Shurman recursive normal form via
level-raise associativity) ∘ generator refinement (`oldNewGenSpan_le_oldNewGenCharSpan`) ∘
Phase 2 (`oldNewGenCharSpan_inf_charSpace_le_cuspFormsOldChar`, the isotypic collapse with the
conductor divisibility from Miyake 4.6.4). -/
theorem cuspFormsOld_inf_charSpace_le_cuspFormsOldChar
    (χ : DirichletCharacter ℂ N) :
    cuspFormsOld N k ⊓ cuspFormCharSpace k χ.toUnitHom ≤
      cuspFormsOldChar N k χ.toUnitHom χ.conductor := by
  refine le_trans (inf_le_inf_right _ (cuspFormsOld_le_oldNewGenSpan N k)) ?_
  refine le_trans (inf_le_inf_right _ (oldNewGenSpan_le_oldNewGenCharSpan N k)) ?_
  exact oldNewGenCharSpan_inf_charSpace_le_cuspFormsOldChar N k χ

/-! ## Linear independence of distinct-eigenvalue eigenforms (step (i) helper)

Public restatement of the orthogonality fact `eigenforms_orthogonal_of_ne_eigenvalues`
(currently `private` in `AdjointTheoryPetersson.lean`), used to drop the
wrong-eigenvalue summands in 4.6.9(3)'s decomposition. -/

/-- Two nonzero common eigenfunctions in the same Nebentypus space with **different**
`T_n`-eigenvalues at some `(n,N)=1` are Petersson-orthogonal (hence linearly
independent).  Public form of `eigenforms_orthogonal_of_ne_eigenvalues`. -/
theorem petN_eq_zero_of_ne_eigenvalues
    (χ : (ZMod N)ˣ →* ℂˣ)
    {f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ cuspFormCharSpace k χ) (hg_char : g ∈ cuspFormCharSpace k χ)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    {n : ℕ} [NeZero n] (hn : Nat.Coprime n N) {a b : ℂ}
    (hf_eig : heckeT_n_cusp k n f = a • f)
    (hg_eig : heckeT_n_cusp k n g = b • g)
    (h_diff_ab : a ≠ b) :
    petN f g = 0 :=
  eigenforms_orthogonal_of_ne_eigenvalues χ hf_char hg_char hf_ne hg_ne hn hf_eig hg_eig
    h_diff_ab

/-! ## Lemma 4.6.10: old/new subspaces (hence the projections) are Hecke-stable

Miyake Lemma 4.6.10 — the old and new subspaces are stable under `T(n)` and the diamond
operators (`heckeT_n_preserves_cuspFormsOld`/`…cuspFormsNew`,
`diamondOp_preserves_cuspFormsOld`/`…cuspFormsNew`).  Consequently the projections
`oldPart`/`newPart` (along the orthogonal `IsCompl`) **commute** with `T(n)` and the diamond
operators, and they preserve every Nebentypus character space.  This makes the projection of
an eigenform an eigenform with the same eigenvalues — the structural input that lets
Theorem 4.6.12 feed `oldPart g`/`newPart g` into the new-part (T004) and old-part (T010)
arguments. -/

/-- The old projection commutes with `T(n)` for `(n,N)=1` (Miyake 4.6.10): both `cuspFormsOld`
and `cuspFormsNew` are `T(n)`-stable, so `oldPart` commutes with `heckeT_n_cusp`. -/
theorem oldPart_heckeT_n_cusp_comm
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    oldPart (heckeT_n_cusp k n x) = heckeT_n_cusp k n (oldPart x) := by
  conv_lhs => rw [← oldPart_add_newPart x, heckeT_n_cusp_add]
  have hlin : oldPart (heckeT_n_cusp k n (oldPart x) + heckeT_n_cusp k n (newPart x)) =
      oldPart (heckeT_n_cusp k n (oldPart x)) + oldPart (heckeT_n_cusp k n (newPart x)) :=
    map_add _ _ _
  rw [hlin,
    oldPart_of_mem_cuspFormsOld
      (heckeT_n_preserves_cuspFormsOld n hn _ (oldPart_mem_cuspFormsOld x)),
    oldPart_of_mem_cuspFormsNew
      (heckeT_n_preserves_cuspFormsNew n hn _ (newPart_mem_cuspFormsNew x)),
    add_zero]

/-- The old projection commutes with the diamond operators (Miyake 4.6.10): both subspaces are
diamond-stable, so `oldPart` commutes with `diamondOpCuspHom`. -/
theorem oldPart_diamondOpCuspHom_comm
    (a : (ZMod N)ˣ) (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    oldPart (diamondOpCuspHom k a x) = diamondOpCuspHom k a (oldPart x) := by
  have hsplit : diamondOpCuspHom k a x =
      diamondOpCuspHom k a (oldPart x) + diamondOpCuspHom k a (newPart x) := by
    conv_lhs => rw [← oldPart_add_newPart x]
    exact map_add _ _ _
  rw [hsplit]
  have hlin : oldPart (diamondOpCuspHom k a (oldPart x) + diamondOpCuspHom k a (newPart x)) =
      oldPart (diamondOpCuspHom k a (oldPart x)) +
        oldPart (diamondOpCuspHom k a (newPart x)) :=
    map_add _ _ _
  rw [hlin,
    oldPart_of_mem_cuspFormsOld
      (diamondOpCuspHom_preserves_cuspFormsOld a _ (oldPart_mem_cuspFormsOld x)),
    oldPart_of_mem_cuspFormsNew
      (diamondOpCuspHom_preserves_cuspFormsNew a _ (newPart_mem_cuspFormsNew x)),
    add_zero]

/-- The old projection preserves every Nebentypus character space (Miyake 4.6.10). -/
theorem oldPart_mem_cuspFormCharSpace
    (χ : (ZMod N)ˣ →* ℂˣ) {x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hx : x ∈ cuspFormCharSpace k χ) :
    oldPart x ∈ cuspFormCharSpace k χ := by
  rw [mem_cuspFormCharSpace_iff]
  intro a
  rw [← oldPart_diamondOpCuspHom_comm a x, diamondOpCusp_apply_charSpace k χ a hx]
  exact map_smul _ _ _

/-- Packaging input for T004/T010: the old projection of an `Eigenform` `g` is a `T(n)`-eigenform
with **the same eigenvalues** as `g` for `(n,N)=1` (Miyake 4.6.10), since `oldPart` commutes with
`T(n)`.  Symmetrically for `newPart`. -/
theorem oldPart_isEigen_of_eigenform
    (g : Eigenform N k) (n : ℕ+) (hn : Nat.Coprime n.val N) :
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp k n.val (oldPart g.toCuspForm) =
      g.eigenvalue n • oldPart g.toCuspForm := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  rw [← oldPart_heckeT_n_cusp_comm n.val hn g.toCuspForm, g.isEigen n hn]
  exact map_smul _ _ _

theorem newPart_isEigen_of_eigenform
    (g : Eigenform N k) (n : ℕ+) (hn : Nat.Coprime n.val N) :
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp k n.val (newPart g.toCuspForm) =
      g.eigenvalue n • newPart g.toCuspForm := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have hcomm : newPart (heckeT_n_cusp k n.val g.toCuspForm) =
      heckeT_n_cusp k n.val (newPart g.toCuspForm) := by
    conv_lhs => rw [← oldPart_add_newPart g.toCuspForm, heckeT_n_cusp_add]
    have hlin : newPart (heckeT_n_cusp k n.val (oldPart g.toCuspForm) +
          heckeT_n_cusp k n.val (newPart g.toCuspForm)) =
        newPart (heckeT_n_cusp k n.val (oldPart g.toCuspForm)) +
          newPart (heckeT_n_cusp k n.val (newPart g.toCuspForm)) :=
      map_add _ _ _
    rw [hlin,
      newPart_of_mem_cuspFormsOld
        (heckeT_n_preserves_cuspFormsOld n.val hn _ (oldPart_mem_cuspFormsOld g.toCuspForm)),
      newPart_of_mem_cuspFormsNew
        (heckeT_n_preserves_cuspFormsNew n.val hn _ (newPart_mem_cuspFormsNew g.toCuspForm)),
      zero_add]
  rw [← hcomm, g.isEigen n hn]
  exact map_smul _ _ _

/-! ## Step: the new part equals `b₁ • f`

Close to the existing same-level uniqueness, but stated for an *un-normalised* new
eigenform `g_new`.  Since `g_new ∈ cuspFormsNew` (the classical newspace) need not lie in
`cuspFormsNewExtended`, it cannot be packaged as a (now-genuine) `Newform`; the argument
therefore proceeds by *direct disjointness* (`mainLemma_charSpace_routeB` + new∩old=0),
mirroring `newform_unique_routeB`.  The eigenvalue agreement off the finite set `S` is
upgraded to *all* coprime indices via Hecke multiplicativity (Miyake 4.6.13), with
`g_new`'s eigenvalue facts derived from the renormalised form `b₁⁻¹ • g_new`. -/

/-- The period-1 `q`-coefficients of the renormalised form `b₁⁻¹ • g_new` recover the
classical eigenvalues of `g_new`: `aₙ(b₁⁻¹ • g_new) = λₙ(g_new)` for `(n, N) = 1`,
`b₁ = a₁(g_new) ≠ 0`.  (Lemma 4.5.15(1) after normalising `a₁` to `1`.) -/
private theorem coeff_smul_inv_eq_eigenvalue
    (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    {b₁ : ℂ} (hb₁_def : b₁ = (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1)
    (hb₁_ne : b₁ ≠ 0) (n : ℕ+) (hn : Nat.Coprime n.val N) :
    (ModularFormClass.qExpansion (1 : ℝ) (b₁⁻¹ • g_new.toCuspForm)).coeff n.val =
      g_new.eigenvalue n := by
  have h_smul_coeff : (ModularFormClass.qExpansion (1 : ℝ) (b₁⁻¹ • g_new.toCuspForm)).coeff n.val =
      b₁⁻¹ * (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff n.val := by
    show (ModularFormClass.qExpansion (1 : ℝ) (⇑(b₁⁻¹ • g_new.toCuspForm : CuspForm _ k))).coeff n.val =
      b₁⁻¹ * (ModularFormClass.qExpansion (1 : ℝ) (⇑g_new.toCuspForm)).coeff n.val
    rw [show (⇑(b₁⁻¹ • g_new.toCuspForm : CuspForm _ k) : UpperHalfPlane → ℂ) = b₁⁻¹ • ⇑g_new.toCuspForm
        from rfl,
      show (⇑g_new.toCuspForm : UpperHalfPlane → ℂ) = ⇑g_new.toCuspForm.toModularForm' from rfl,
      qExpansion_smul one_pos one_mem_strictPeriods_Gamma1_map_local, PowerSeries.coeff_smul,
      smul_eq_mul]
  rw [h_smul_coeff, Eigenform.coeff_eq_coeff_one_mul_eigenvalue g_new χ hgχ n hn, ← hb₁_def,
    ← mul_assoc, inv_mul_cancel₀ hb₁_ne, one_mul]

/-- The renormalised form `b₁⁻¹ • g_new` is a period-1 normalised eigenform. -/
private theorem isNormalisedEigenform_one_smul_inv
    (g_new : Eigenform N k)
    {b₁ : ℂ} (hb₁_def : b₁ = (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1)
    (hb₁_ne : b₁ ≠ 0) :
    IsNormalisedEigenform_one k (b₁⁻¹ • g_new.toCuspForm).toModularForm' := by
  refine ⟨?_, ?_⟩
  · intro n hn
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    refine ⟨g_new.eigenvalue n, ?_⟩
    have h_cusp : heckeT_n_cusp k n.val (b₁⁻¹ • g_new.toCuspForm) =
        g_new.eigenvalue n • (b₁⁻¹ • g_new.toCuspForm) := by
      rw [heckeT_n_cusp_smul, g_new.isEigen n hn, smul_comm]
    have h_lift : (heckeT_n_cusp k n.val (b₁⁻¹ • g_new.toCuspForm)).toModularForm' =
        (g_new.eigenvalue n • (b₁⁻¹ • g_new.toCuspForm)).toModularForm' := by rw [h_cusp]
    rw [heckeT_n_cusp_toModularForm'] at h_lift
    exact h_lift
  · show (ModularFormClass.qExpansion (1 : ℝ) (b₁⁻¹ • g_new.toCuspForm)).coeff 1 = 1
    rw [qExpansion_one_coeff_one_smul_local g_new.toCuspForm b₁⁻¹, ← hb₁_def,
      inv_mul_cancel₀ hb₁_ne]

/-- **Coprime multiplicativity of the classical eigenvalues** of an `Eigenform`
`g_new ∈ cuspFormsNew` with `a₁(g_new) ≠ 0`: `λ_{mn}(g_new) = λ_m(g_new) · λ_n(g_new)` for
`gcd(m, n) = 1`.  Derived from coefficient multiplicativity of the normalised form. -/
private theorem eigenvalue_coprime_mul_of_coeff_one_ne_zero
    (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hb₁_ne : (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 ≠ 0)
    (m n : ℕ+) (hm : Nat.Coprime m.val N) (hn : Nat.Coprime n.val N)
    (hmn : Nat.Coprime m.val n.val) :
    g_new.eigenvalue ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩ =
      g_new.eigenvalue m * g_new.eigenvalue n := by
  set b₁ := (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 with hb₁_def
  set F₁ : ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
    (b₁⁻¹ • g_new.toCuspForm).toModularForm' with hF₁_def
  have hF₁_char : F₁ ∈ modFormCharSpace k χ :=
    (modFormCharSpace k χ).smul_mem b₁⁻¹ hgχ
  have hF₁_eigen : IsNormalisedEigenform_one k F₁ :=
    isNormalisedEigenform_one_smul_inv g_new hb₁_def hb₁_ne
  have hmn_N : Nat.Coprime (m.val * n.val) N := hm.mul_left hn
  -- coefficient multiplicativity at coprime `m, n` (the `gcd = 1` divisor sum collapses).
  have h := eigenform_coeff_multiplicative_one (N := N) k m n hm hn χ hF₁_char hF₁_eigen
  have hgcd : Nat.gcd m.val n.val = 1 := hmn
  rw [hgcd, Nat.divisors_one, Finset.sum_singleton, dif_pos (Nat.coprime_one_left N)] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  rw [h_unit_one] at h
  simp only [Nat.cast_one, one_zpow, map_one, Units.val_one, one_mul, mul_one, Nat.div_one] at h
  -- align the `F₁` coefficients (functions) with the renormalised cusp-form coefficients.
  rw [show (⇑F₁ : UpperHalfPlane → ℂ) = b₁⁻¹ • ⇑g_new.toCuspForm from rfl] at h
  -- convert the three coefficients to eigenvalues of `g_new`.
  have hcm := coeff_smul_inv_eq_eigenvalue g_new χ hgχ hb₁_def hb₁_ne m hm
  have hcn := coeff_smul_inv_eq_eigenvalue g_new χ hgχ hb₁_def hb₁_ne n hn
  have hcmn := coeff_smul_inv_eq_eigenvalue g_new χ hgχ hb₁_def hb₁_ne
    ⟨m.val * n.val, Nat.mul_pos m.pos n.pos⟩ hmn_N
  simp only [PNat.mk_coe] at hcmn
  rw [hcm, hcn, hcmn] at h
  exact h.symm

/-- **Prime-square eigenvalue relation** for an `Eigenform` `g_new ∈ cuspFormsNew` with
`a₁(g_new) ≠ 0`: `λ_{q²}(g_new) = λ_q(g_new)² - χ(q) · q^{k-1}` for a prime `q ∤ N`.
Diamond–Shurman 5.3 / Miyake 4.5.13, via coefficient multiplicativity at `m = n = q`. -/
private theorem eigenvalue_at_prime_sq_of_coeff_one_ne_zero
    (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hb₁_ne : (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 ≠ 0)
    {q : ℕ} (hq : Nat.Prime q) (hqN : Nat.Coprime q N) :
    g_new.eigenvalue ⟨q ^ 2, pow_pos hq.pos 2⟩ =
      g_new.eigenvalue ⟨q, hq.pos⟩ ^ 2 -
        (χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1) := by
  set b₁ := (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 with hb₁_def
  set F₁ : ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
    (b₁⁻¹ • g_new.toCuspForm).toModularForm' with hF₁_def
  have hF₁_char : F₁ ∈ modFormCharSpace k χ :=
    (modFormCharSpace k χ).smul_mem b₁⁻¹ hgχ
  have hF₁_eigen : IsNormalisedEigenform_one k F₁ :=
    isNormalisedEigenform_one_smul_inv g_new hb₁_def hb₁_ne
  have hq_pos : 0 < q := hq.pos
  let q_pnat : ℕ+ := ⟨q, hq_pos⟩
  -- coefficient multiplicativity at `m = n = q` (`gcd = q`, divisors `{1, q}`).
  have h := eigenform_coeff_multiplicative_one (N := N) k q_pnat q_pnat hqN hqN χ
    hF₁_char hF₁_eigen
  simp only [q_pnat, PNat.mk_coe] at h
  rw [Nat.gcd_self, hq.divisors,
      Finset.sum_insert (by simp only [Finset.mem_singleton]; exact hq.ne_one.symm),
      Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  have h_div_one : q * q / (1 * 1) = q ^ 2 := by rw [mul_one, Nat.div_one, sq]
  have h_div_qsq : q * q / (q * q) = 1 := Nat.div_self (by positivity)
  rw [dif_pos (Nat.coprime_one_left N), dif_pos hqN, h_div_one, h_div_qsq] at h
  simp only [h_unit_one, map_one, Units.val_one, one_mul,
    Nat.cast_one, one_zpow] at h
  -- align the `F₁` coefficients (functions) with the renormalised cusp-form coefficients.
  rw [show (⇑F₁ : UpperHalfPlane → ℂ) = b₁⁻¹ • ⇑g_new.toCuspForm from rfl] at h
  -- convert coefficients to eigenvalues of `g_new`.
  have hcq := coeff_smul_inv_eq_eigenvalue g_new χ hgχ hb₁_def hb₁_ne q_pnat hqN
  have hcqsq := coeff_smul_inv_eq_eigenvalue g_new χ hgχ hb₁_def hb₁_ne
    ⟨q ^ 2, pow_pos hq_pos 2⟩ (Nat.Coprime.pow_left 2 hqN)
  have hc1 : (ModularFormClass.qExpansion (1 : ℝ) (b₁⁻¹ • ⇑g_new.toCuspForm)).coeff 1 = 1 := by
    have := hF₁_eigen.2
    rwa [hF₁_def, show (⇑(b₁⁻¹ • g_new.toCuspForm).toModularForm' : UpperHalfPlane → ℂ)
      = b₁⁻¹ • ⇑g_new.toCuspForm from rfl] at this
  simp only [q_pnat, PNat.mk_coe] at hcq hcqsq
  rw [hcq, hcqsq, hc1, mul_one] at h
  -- `λ_q² = λ_q² - χ(q) q^{k-1}`; rearrange `h : λ_q · λ_q = λ_q² + χ(q) q^{k-1}`.
  linear_combination -h

/-- Existence of a prime `q ∤ N` with `q`, `q²`, `n·q`, `n·q²` all avoiding a finite set
`S` and coprime to `n` (the index used in the multiplicativity bootstrap). -/
private theorem exists_prime_coprime_avoiding_finset_local
    (n : ℕ+) (S : Finset ℕ) :
    ∃ q, Nat.Prime q ∧ Nat.Coprime q N ∧ Nat.Coprime n.val q ∧
      q ∉ S ∧ q ^ 2 ∉ S ∧ n.val * q ∉ S ∧ n.val * q ^ 2 ∉ S := by
  obtain ⟨q, hq_le, hq_prime⟩ := Nat.exists_infinite_primes (S.sup id + N + n.val + 2)
  have hq_gt_S : ∀ s, s ∈ S → s < q := fun s hs ↦ by
    have : s ≤ S.sup id := Finset.le_sup (f := id) hs
    omega
  have hq_ndvd_N : ¬ q ∣ N := fun hqN ↦ by
    have : q ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hqN
    omega
  have hq_ndvd_n : ¬ q ∣ n.val := fun hqn ↦ by
    have : q ≤ n.val := Nat.le_of_dvd n.pos hqn
    omega
  have hq_N : Nat.Coprime q N := hq_prime.coprime_iff_not_dvd.mpr hq_ndvd_N
  have hn_q : Nat.Coprime n.val q :=
    (hq_prime.coprime_iff_not_dvd.mpr hq_ndvd_n).symm
  refine ⟨q, hq_prime, hq_N, hn_q, ?_, ?_, ?_, ?_⟩
  · exact fun hqS ↦ by have := hq_gt_S q hqS; omega
  · exact fun hqsqS ↦ by
      have := hq_gt_S _ hqsqS
      have hle : q ≤ q ^ 2 := by nlinarith [hq_prime.pos]
      omega
  · exact fun hnqS ↦ by
      have := hq_gt_S _ hnqS
      have hle : q ≤ n.val * q := Nat.le_mul_of_pos_left q n.pos
      omega
  · exact fun hnqsqS ↦ by
      have := hq_gt_S _ hnqsqS
      have h1 : q ≤ q ^ 2 := by nlinarith [hq_prime.pos]
      have h2 : q ^ 2 ≤ n.val * q ^ 2 := Nat.le_mul_of_pos_left _ n.pos
      omega

/-- Helper: from the prime-`q` cofactor relation, agreement at `n·q` (or `n·q²`) plus a
nonzero cofactor eigenvalue propagates eigenvalue agreement to `n`. -/
private theorem eigenvalue_agree_of_cofactor_ne_zero
    (f : Newform N k) (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hb₁_ne : (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 ≠ 0)
    (n m : ℕ+) (hn : Nat.Coprime n.val N) (hmN : Nat.Coprime m.val N)
    (hnm : Nat.Coprime n.val m.val)
    (hm_ne : f.eigenvalue m ≠ 0) (hm_eq : f.eigenvalue m = g_new.eigenvalue m)
    (hnm_eq : f.eigenvalue ⟨n.val * m.val, Nat.mul_pos n.pos m.pos⟩
            = g_new.eigenvalue ⟨n.val * m.val, Nat.mul_pos n.pos m.pos⟩) :
    f.eigenvalue n = g_new.eigenvalue n := by
  refine mul_right_cancel₀ hm_ne ?_
  rw [← HeckeRing.GL2.Newform.eigenvalue_coprime_mul f n m hn hmN hnm χ hfχ, hnm_eq,
    eigenvalue_coprime_mul_of_coeff_one_ne_zero g_new χ hgχ hb₁_ne n m hn hmN hnm, hm_eq]

/-- **Eigenvalue agreement off a finite set ⟹ agreement at all coprime indices** for a
`Newform` `f` and an `Eigenform` `g_new ∈ cuspFormsNew` with `a₁(g_new) ≠ 0` (Miyake
4.6.13).  The `Eigenform`-side analogue of `eigenvalues_eq_all_coprime_of_eq_off_finite`. -/
private theorem eigenvalues_eq_all_coprime_of_eq_off_finite_eigenform
    (f : Newform N k) (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hb₁_ne : (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 ≠ 0)
    (S : Finset ℕ)
    (hyp : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g_new.eigenvalue n) :
    ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g_new.eigenvalue n := by
  intro n hn
  by_cases hn_S : n.val ∈ S
  · obtain ⟨q, hq_prime, hq_N, hn_coprime_q, hq_notin_S, hqsq_notin_S,
      hnq_notin_S, hnqsq_notin_S⟩ := exists_prime_coprime_avoiding_finset_local (N := N) n S
    have hqsq_N : Nat.Coprime (q ^ 2) N := Nat.Coprime.pow_left 2 hq_N
    let q_pnat : ℕ+ := ⟨q, hq_prime.pos⟩
    let qsq_pnat : ℕ+ := ⟨q ^ 2, pow_pos hq_prime.pos 2⟩
    by_cases hLamq : f.eigenvalue q_pnat = 0
    · -- `λ_q(f) = 0 ⟹ λ_{q²}(f) ≠ 0`; use the `q²` cofactor.
      have hf_qsq := newform_eigenvalue_at_prime_sq f χ hfχ q hq_prime hq_N
      have hf_qsq0 : f.eigenvalue qsq_pnat =
          -((χ (ZMod.unitOfCoprime q hq_N) : ℂ)) * (q : ℂ) ^ (k - 1) := by
        rw [show f.eigenvalue qsq_pnat = _ from hf_qsq, hLamq]; ring
      have hLamqsq_ne : f.eigenvalue qsq_pnat ≠ 0 := by
        rw [hf_qsq0]
        exact mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero _))
          (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hq_prime.pos.ne'))
      have hg_q0 : g_new.eigenvalue q_pnat = 0 :=
        (hyp q_pnat hq_N hq_notin_S).symm.trans hLamq
      have hg_qsq := eigenvalue_at_prime_sq_of_coeff_one_ne_zero g_new χ hgχ hb₁_ne hq_prime hq_N
      have hqsq_eq : f.eigenvalue qsq_pnat = g_new.eigenvalue qsq_pnat := by
        rw [hf_qsq0, show g_new.eigenvalue qsq_pnat = _ from hg_qsq, hg_q0]; ring
      exact eigenvalue_agree_of_cofactor_ne_zero f g_new χ hfχ hgχ hb₁_ne n qsq_pnat
        hn hqsq_N (Nat.Coprime.pow_right 2 hn_coprime_q) hLamqsq_ne hqsq_eq
        (hyp ⟨n.val * q ^ 2, Nat.mul_pos n.pos (pow_pos hq_prime.pos 2)⟩
          (Nat.Coprime.mul_left hn hqsq_N) hnqsq_notin_S)
    · exact eigenvalue_agree_of_cofactor_ne_zero f g_new χ hfχ hgχ hb₁_ne n q_pnat
        hn hq_N hn_coprime_q hLamq (hyp q_pnat hq_N hq_notin_S)
        (hyp ⟨n.val * q, Nat.mul_pos n.pos hq_prime.pos⟩
          (Nat.Coprime.mul_left hn hq_N) hnq_notin_S)
  · exact hyp n hn hn_S

/-! ### Cross-level eigenvalue upgrade (for the descended summand `h` of level `M ∣ N`)

For Theorem 4.6.12 step (ii) the eigenvalue agreement off `S` must be upgraded to all
coprime indices, comparing a level-`N` `Newform f` (Nebentypus `χ`) with the descended
level-`M` matching summand `h` (Nebentypus `ψ`, `ψ ∘ unitsMap = χ`).  The same-level
upgrade `eigenvalues_eq_all_coprime_of_eq_off_finite_eigenform` does not apply; we redo
the multiplicativity bootstrap with the second form at its own level `M`, using the
character compatibility `χ(q) = ψ(q)` at indices `q` coprime to `N`. -/

omit [NeZero N] in
/-- Character compatibility at a coprime index: if `ψ ∘ unitsMap (M ∣ N) = χ` and
`q` is coprime to `N` (hence to `M`), then `χ⟨q⟩ = ψ⟨q⟩` as unit values. -/
private theorem char_comp_unitsMap_unitOfCoprime
    {M : ℕ} [NeZero M] {q : ℕ} (hMN : M ∣ N) (χ : (ZMod N)ˣ →* ℂˣ)
    (ψ : (ZMod M)ˣ →* ℂˣ) (hψχ : ψ.comp (ZMod.unitsMap hMN) = χ)
    (hqN : Nat.Coprime q N) (hqM : Nat.Coprime q M) :
    (χ (ZMod.unitOfCoprime q hqN) : ℂ) = (ψ (ZMod.unitOfCoprime q hqM) : ℂ) := by
  rw [← hψχ, MonoidHom.comp_apply]
  congr 2
  refine Units.ext ?_
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  show ZMod.castHom hMN (ZMod M) (ZMod.unitOfCoprime q hqN : ZMod N) = (q : ZMod M)
  rw [ZMod.coe_unitOfCoprime, map_natCast]

/-- Cross-level cofactor propagation: the level-`M` analogue of
`eigenvalue_agree_of_cofactor_ne_zero`, comparing `f.eigenvalue` (level `N`) and
`g.eigenvalue` (level `M`, character `ψ`) via the level-`M` multiplicativity. -/
private theorem eigenvalue_cross_agree_of_cofactor_ne_zero
    {M : ℕ} [NeZero M] (f : Newform N k) (g : Eigenform M k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (ψ : (ZMod M)ˣ →* ℂˣ)
    (hgψ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k ψ)
    (hb₁_ne : (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 ≠ 0)
    (hMN : M ∣ N)
    (n m : ℕ+) (hn : Nat.Coprime n.val N) (hmN : Nat.Coprime m.val N)
    (hnm : Nat.Coprime n.val m.val)
    (hm_ne : f.eigenvalue m ≠ 0) (hm_eq : f.eigenvalue m = g.eigenvalue m)
    (hnm_eq : f.eigenvalue ⟨n.val * m.val, Nat.mul_pos n.pos m.pos⟩
            = g.eigenvalue ⟨n.val * m.val, Nat.mul_pos n.pos m.pos⟩) :
    f.eigenvalue n = g.eigenvalue n := by
  refine mul_right_cancel₀ hm_ne ?_
  rw [← HeckeRing.GL2.Newform.eigenvalue_coprime_mul f n m hn hmN hnm χ hfχ, hnm_eq,
    eigenvalue_coprime_mul_of_coeff_one_ne_zero g ψ hgψ hb₁_ne n m
      (hn.coprime_dvd_right hMN) (hmN.coprime_dvd_right hMN) hnm, hm_eq]

/-- **Cross-level eigenvalue agreement off a finite set ⟹ agreement at all coprime
indices** (Miyake 4.6.13, descended form).  As
`eigenvalues_eq_all_coprime_of_eq_off_finite_eigenform`, but the eigenform `g` lives at
a divisor level `M ∣ N` with character `ψ` satisfying `ψ ∘ unitsMap = χ`. -/
private theorem eigenvalues_eq_all_coprime_cross_level
    {M : ℕ} [NeZero M] (f : Newform N k) (g : Eigenform M k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (ψ : (ZMod M)ˣ →* ℂˣ)
    (hgψ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k ψ)
    (hb₁_ne : (ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1 ≠ 0)
    (hMN : M ∣ N) (hψχ : ψ.comp (ZMod.unitsMap hMN) = χ)
    (S : Finset ℕ)
    (hyp : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n := by
  intro n hn
  by_cases hn_S : n.val ∈ S
  · obtain ⟨q, hq_prime, hq_N, hn_coprime_q, hq_notin_S, hqsq_notin_S,
      hnq_notin_S, hnqsq_notin_S⟩ := exists_prime_coprime_avoiding_finset_local (N := N) n S
    have hqsq_N : Nat.Coprime (q ^ 2) N := Nat.Coprime.pow_left 2 hq_N
    have hq_M : Nat.Coprime q M := hq_N.coprime_dvd_right hMN
    let q_pnat : ℕ+ := ⟨q, hq_prime.pos⟩
    let qsq_pnat : ℕ+ := ⟨q ^ 2, pow_pos hq_prime.pos 2⟩
    -- prime-square relations for `f` (level `N`, `χ`) and `g` (level `M`, `ψ`) agree at `q ∤ N`.
    have h_chi_psi : (χ (ZMod.unitOfCoprime q hq_N) : ℂ) = (ψ (ZMod.unitOfCoprime q hq_M) : ℂ) :=
      char_comp_unitsMap_unitOfCoprime hMN χ ψ hψχ hq_N hq_M
    by_cases hLamq : f.eigenvalue q_pnat = 0
    · have hf_qsq := newform_eigenvalue_at_prime_sq f χ hfχ q hq_prime hq_N
      have hf_qsq0 : f.eigenvalue qsq_pnat =
          -((χ (ZMod.unitOfCoprime q hq_N) : ℂ)) * (q : ℂ) ^ (k - 1) := by
        rw [show f.eigenvalue qsq_pnat = _ from hf_qsq, hLamq]; ring
      have hLamqsq_ne : f.eigenvalue qsq_pnat ≠ 0 := by
        rw [hf_qsq0]
        exact mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero _))
          (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hq_prime.pos.ne'))
      have hg_q0 : g.eigenvalue q_pnat = 0 :=
        (hyp q_pnat hq_N hq_notin_S).symm.trans hLamq
      have hg_qsq := eigenvalue_at_prime_sq_of_coeff_one_ne_zero g ψ hgψ hb₁_ne hq_prime hq_M
      have hqsq_eq : f.eigenvalue qsq_pnat = g.eigenvalue qsq_pnat := by
        rw [hf_qsq0, show g.eigenvalue qsq_pnat = _ from hg_qsq, hg_q0, h_chi_psi]; ring
      exact eigenvalue_cross_agree_of_cofactor_ne_zero f g χ hfχ ψ hgψ hb₁_ne hMN n qsq_pnat
        hn hqsq_N (Nat.Coprime.pow_right 2 hn_coprime_q) hLamqsq_ne hqsq_eq
        (hyp ⟨n.val * q ^ 2, Nat.mul_pos n.pos (pow_pos hq_prime.pos 2)⟩
          (Nat.Coprime.mul_left hn hqsq_N) hnqsq_notin_S)
    · exact eigenvalue_cross_agree_of_cofactor_ne_zero f g χ hfχ ψ hgψ hb₁_ne hMN n q_pnat
        hn hq_N hn_coprime_q hLamq (hyp q_pnat hq_N hq_notin_S)
        (hyp ⟨n.val * q, Nat.mul_pos n.pos hq_prime.pos⟩
          (Nat.Coprime.mul_left hn hq_N) hnq_notin_S)
  · exact hyp n hn hn_S

/-- **New-part identity** (Miyake 4.6.12, new part, p. 163).  If `f` is a normalised
newform and `g_new` is a common eigenfunction in the new subspace sharing `f`'s
eigenvalues off `S`, then `g_new = b₁ • f` where `b₁ = a₁(g_new)`.

Proved by direct disjointness (route B): the normalised difference
`b₁⁻¹ • g_new - f` has vanishing `q`-coefficients at every index coprime to `N` (both
forms are normalised eigenforms with the same eigenvalues there, the off-`S` agreement
having been upgraded to all coprime indices), so it lies in `cuspFormsOld N k`; it also
lies in `cuspFormsNew N k`, so it is `0`.

This is the **unconditional** form: the per-prime character factorisation is supplied
internally by the dichotomy-based `mainLemma_charSpace_routeB_unconditional` (Deliverable 1)
and `coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen_unconditional` (Deliverable 2). -/
theorem newPart_eq_smul_of_shared_eigenvalues
    (f : Newform N k) (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hg_new : g_new.toCuspForm ∈ cuspFormsNew N k)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g_new.eigenvalue n) :
    g_new.toCuspForm =
      (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 • f.toCuspForm := by
  set b₁ := (ModularFormClass.qExpansion (1 : ℝ) g_new.toCuspForm).coeff 1 with hb₁_def
  by_cases hg0 : g_new.toCuspForm = 0
  · have hb₁0 : b₁ = 0 := by
      have hsmul0 :
          (ModularFormClass.qExpansion (1 : ℝ) ((0 : ℂ) • g_new.toCuspForm)).coeff 1 = 0 := by
        rw [qExpansion_one_coeff_one_smul_local, zero_mul]
      have hbridge : (⇑g_new.toCuspForm : UpperHalfPlane → ℂ) =
          (0 : ℂ) • (⇑g_new.toCuspForm : UpperHalfPlane → ℂ) := by
        rw [zero_smul, hg0]; rfl
      rw [hb₁_def, hbridge]
      exact hsmul0
    rw [hg0, hb₁0, zero_smul]
  · -- `b₁ ≠ 0` by Lemma 4.6.11 (unconditional).  Reduce to `b₁⁻¹ • g_new = f`, then disjointness.
    have hb₁_ne : b₁ ≠ 0 :=
      coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen_unconditional g_new χ hgχ hg_new hg0
    set g₁ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := b₁⁻¹ • g_new.toCuspForm with hg₁_def
    -- eigenvalue agreement at *all* coprime indices (off-`S` upgraded via 4.6.13).
    have h_eig_all : ∀ n : ℕ+, Nat.Coprime n.val N →
        f.eigenvalue n = g_new.eigenvalue n :=
      eigenvalues_eq_all_coprime_of_eq_off_finite_eigenform f g_new χ hfχ hgχ hb₁_ne S h_eig
    -- the difference `g₁ - f` lies in the χ-cuspform space.
    have hg₁_char : g₁.toModularForm' ∈ modFormCharSpace k χ :=
      (modFormCharSpace k χ).smul_mem b₁⁻¹ hgχ
    have h_diff_char : g₁ - f.toCuspForm ∈ cuspFormCharSpace k χ :=
      (cuspFormCharSpace k χ).sub_mem
        ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
          g₁).mp (by convert hg₁_char using 1))
        ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
          f.toCuspForm).mp (by convert hfχ using 1))
    -- coefficient vanishing at every coprime index.
    have h_vanish : ∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) (g₁ - f.toCuspForm)).coeff n = 0 := by
      intro n hn
      show (ModularFormClass.qExpansion (1 : ℝ)
          (⇑g₁.toModularForm' - ⇑f.toCuspForm.toModularForm')).coeff n = 0
      rw [qExpansion_sub one_pos one_mem_strictPeriods_Gamma1_map_local, map_sub, sub_eq_zero]
      by_cases hn0 : n = 0
      · subst hn0
        rw [ModularFormClass.qExpansion_coeff_zero _ one_pos one_mem_strictPeriods_Gamma1_map_local,
            ModularFormClass.qExpansion_coeff_zero _ one_pos one_mem_strictPeriods_Gamma1_map_local,
            show (⇑g₁.toModularForm' : UpperHalfPlane → ℂ) = ⇑g₁ from rfl,
            show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl,
            (CuspFormClass.zero_at_infty g₁).valueAtInfty_eq_zero,
            (CuspFormClass.zero_at_infty f.toCuspForm).valueAtInfty_eq_zero]
      · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
        have hL : (ModularFormClass.qExpansion (1 : ℝ) (⇑g₁.toModularForm')).coeff n =
            g_new.eigenvalue ⟨n, hn_pos⟩ :=
          coeff_smul_inv_eq_eigenvalue g_new χ hgχ hb₁_def hb₁_ne ⟨n, hn_pos⟩ hn
        have hR : (ModularFormClass.qExpansion (1 : ℝ)
            (⇑f.toCuspForm.toModularForm')).coeff n = f.eigenvalue ⟨n, hn_pos⟩ :=
          (Newform.eigenvalue_eq_coeff f ⟨n, hn_pos⟩ hn χ hfχ).symm
        rw [hL, hR, h_eig_all ⟨n, hn_pos⟩ hn]
    -- route B (unconditional): the difference is old; it is also new; hence zero.
    have h_old : g₁ - f.toCuspForm ∈ cuspFormsOld N k :=
      mainLemma_charSpace_routeB_unconditional χ (g₁ - f.toCuspForm) h_diff_char h_vanish
    have h_new : g₁ - f.toCuspForm ∈ cuspFormsNew N k :=
      (cuspFormsNew N k).sub_mem ((cuspFormsNew N k).smul_mem b₁⁻¹ hg_new)
        (cuspFormsNewExtended_le_cuspFormsNew f.isNew)
    have hkey : g₁ = f.toCuspForm :=
      sub_eq_zero.mp (Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _ h_old h_new)
    rw [← hkey, hg₁_def, smul_smul, mul_inv_cancel₀ hb₁_ne, one_smul]

/-! ## Step: the old part is zero (the descent argument, steps (i)+(ii))

This is where gap #4 (4.6.9) and gap #3 (4.6.2) are consumed. -/

/-- A nonzero `Newform` at level `N` does not lie in the **extended** old space
`cuspFormsOldExtended N k` (the faithful old space of Miyake p.162 / Diamond–Shurman
Def 5.6.1: level-raises **together with** the trivial inclusions `levelInclude_cusp`).

Since `Newform.isNew` places the form in `cuspFormsNewExtended N k = (cuspFormsOldExtended)⊥`,
this is immediate from `cuspFormsOldExtended_disjoint_cuspFormsNewExtended` and `f ≠ 0`. -/
theorem newform_notMem_cuspFormsOldExtended
    (f : Newform N k) (hf0 : f.toCuspForm ≠ 0) :
    f.toCuspForm ∉ cuspFormsOldExtended N k := fun hf_old =>
  hf0 (Submodule.disjoint_def.mp cuspFormsOldExtended_disjoint_cuspFormsNewExtended
    f.toCuspForm hf_old f.isNew)

/-- Package a classical `T(n)`-eigenform in a Nebentypus space `S_k(Γ₁(M), ψ)` as a bundled
`Eigenform M k` (with character `ψ`).  Bridges the predicate `IsEigenform` to the ring
eigen-condition via `isRingEigenvector_of_isEigenform`. -/
private noncomputable def eigenformOfIsEigenform {M : ℕ} [NeZero M] {k : ℤ}
    (ψ : (ZMod M)ˣ →* ℂˣ) (h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hψ : h ∈ cuspFormCharSpace k ψ) (hev : IsEigenform h) : Eigenform M k where
  toCuspForm := h
  χ := ψ
  mem_charSpace := Unified.cuspFormCharSpace_toModularForm'_mem (χ := ψ) hψ
  ringEigenvalue := (Unified.isRingEigenvector_of_isEigenform (χ := ψ) hψ hev).choose
  isRingEigen := (Unified.isRingEigenvector_of_isEigenform (χ := ψ) hψ hev).choose_spec

/-- The classical eigenvalue of `eigenformOfIsEigenform ψ h _ ⟨λ, hλ⟩` agrees with the
chosen `IsEigenform` witness `λ` at coprime indices (both give `T_n h = c • h` with `h ≠ 0`). -/
private theorem eigenformOfIsEigenform_eigenvalue {M : ℕ} [NeZero M] {k : ℤ}
    (ψ : (ZMod M)ˣ →* ℂˣ) (h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (hψ : h ∈ cuspFormCharSpace k ψ) (lam : ℕ+ → ℂ)
    (hlam : ∀ n : ℕ+, Nat.Coprime n.val M →
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      heckeT_n_cusp k n.val h = lam n • h)
    (hh_ne : h ≠ 0) (n : ℕ+) (hn : Nat.Coprime n.val M) :
    (eigenformOfIsEigenform ψ h hψ ⟨lam, hlam⟩).eigenvalue n = lam n := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  set ev := (eigenformOfIsEigenform ψ h hψ ⟨lam, hlam⟩).eigenvalue n with hev_def
  have hEig : heckeT_n_cusp k n.val h = ev • h :=
    (eigenformOfIsEigenform ψ h hψ ⟨lam, hlam⟩).isEigen n hn
  have h3 : ev • h = lam n • h := by rw [← hEig, hlam n hn]
  have h4 : (ev - lam n) • h = 0 := by rw [sub_smul, h3, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right hh_ne)

/-- `petN` distributes over a finite sum in its second argument. -/
private theorem petN_sum_right {ι : Type*} (s : Finset ι)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (x : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN f (∑ i ∈ s, x i) = ∑ i ∈ s, petN f (x i) := by
  induction s using Finset.cons_induction with
  | empty => simp [petN_zero_right]
  | cons a s has ih => rw [Finset.sum_cons, petN_add_right, ih, Finset.sum_cons]

/-- **Step (i) of Miyake 4.6.12** (the eigenvalue-matching extraction).  A nonzero `g_old`
in the χ-refined old space `S_k^♭(N,χ) ∩ S_k(Γ₁(N),χ)` that is a `T(n)`-eigenform with `f`'s
eigenvalues off `S` (for `(n,N)=1`) descends to a **nonzero new eigenform** `h` at a proper
divisor level `M` (`m_χ ∣ M`, `M ≠ N`), carrying a Nebentypus `ψ` with `ψ∘unitsMap = χ`, whose
classical eigenvalues `λ` satisfy `λ n = f.eigenvalue n` for every `(n,N)=1` off `S`.

Proof (Miyake p.164(i)): T008 writes `g_old = ∑ᵢ Vₗᵢ(hᵢ)` with each `hᵢ` a new eigenform at
level `Mᵢ`; the `χ`-isotypic collapse (`charSpace_finset_sum_filter_eq`) drops the summands
with `Ψ i ≠ χ`.  By Lemma 4.6.2 each `Vₗᵢ(hᵢ)` is a `T(n)`-eigenform with `hᵢ`'s eigenvalue.
If **no** surviving summand were nonzero and eigenvalue-matching, then pairing `g_old` against
each summand via `petN_eq_zero_of_ne_eigenvalues` would give `petN g_old g_old = 0`, forcing
`g_old = 0` by `petN_definite` — contradiction.  So a matching nonzero summand `h := hᵢ` exists. -/
private theorem exists_matching_summand
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    (g_old : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_old : g_old ∈ cuspFormsOldChar N k χ m_χ)
    (hg_old_char : g_old ∈ cuspFormCharSpace k χ)
    (hg_old_ne : g_old ≠ 0)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      heckeT_n_cusp k n.val g_old = f.eigenvalue n • g_old) :
    ∃ (M : ℕ) (_ : NeZero M) (_hcond : m_χ ∣ M) (_hMne : M ≠ N) (hMN : M ∣ N)
      (ψ : (ZMod M)ˣ →* ℂˣ) (h : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (lam : ℕ+ → ℂ),
      h ∈ cuspFormsNew M k ∧ h ∈ cuspFormCharSpace k ψ ∧
        ψ.comp (ZMod.unitsMap hMN) = χ ∧ h ≠ 0 ∧
        (∀ n : ℕ+, Nat.Coprime n.val M →
          haveI : NeZero n.val := ⟨n.pos.ne'⟩
          heckeT_n_cusp k n.val h = lam n • h) ∧
        (∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S → lam n = f.eigenvalue n) := by
  classical
  obtain ⟨ι, hι, M, l, hM, hl, hcond, hMne, heq, h, χM, hh_new, hh_eig, hh_char, hsum⟩ :=
    exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar χ m_χ g_old hg_old
  -- `M i ∣ N` and the level-`N` pullback character of each summand.
  have hMdvd : ∀ i, M i ∣ N := fun i ↦ ⟨l i, by rw [← heq i, Nat.mul_comm]⟩
  set Ψ : ι → ((ZMod N)ˣ →* ℂˣ) :=
    fun i ↦ (χM i).comp (ZMod.unitsMap (heq i ▸ Nat.dvd_mul_left (M i) (l i))) with hΨ_def
  -- The summand functions and the χ-isotypic filter.
  set V : ι → CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    fun i ↦ heq i ▸ levelRaise (M i) (l i) k (h i) with hV_def
  -- Each summand lies in its level-`N` pullback character space (Atkin–Lehner, T010-A's `V_l`).
  have hVΨ : ∀ i, V i ∈ cuspFormCharSpace k (Ψ i) := fun i ↦
    levelRaise_mem_cuspFormCharSpace_comp (heq i) (χM i) (hh_char i)
  set s' : Finset ι := Finset.univ.filter (fun i ↦ Ψ i = χ) with hs'_def
  -- Isotypic collapse: only the `Ψ i = χ` summands survive.
  have hcollapse : g_old = ∑ i ∈ s', V i :=
    charSpace_finset_sum_filter_eq Finset.univ V Ψ χ (fun i _ ↦ hVΨ i)
      (by rw [hsum]) hg_old_char
  -- The eigenvalue witness of each `h i` (and hence of `V i`, by Lemma 4.6.2).
  choose lam hlam_spec using hh_eig
  -- `V i` is a `T(n)`-eigenform with eigenvalue `lam i n` for all `(n,N)=1` (Lemma 4.6.2).
  have hV_eig : ∀ (i : ι) (n : ℕ+) (hn : Nat.Coprime n.val N),
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      heckeT_n_cusp k n.val (V i) = lam i n • V i := fun i n hn ↦ by
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    have hnMi : Nat.Coprime n.val (M i) :=
      Nat.Coprime.coprime_dvd_right (hMdvd i) hn
    exact heckeT_n_levelRaise_eigen (heq i) n.val hn (h i) (lam i n) (hlam_spec i n hnMi)
  -- Extract a surviving summand that is nonzero AND matches `f`'s eigenvalues off `S`.
  by_contra hcon
  push_neg at hcon
  -- Under the negation, every surviving summand is `petN`-orthogonal to `g_old`.
  have horth : ∀ i ∈ s', petN g_old (V i) = 0 := by
    intro i hi
    by_cases hVi0 : V i = 0
    · rw [hVi0, petN_zero_right]
    · -- `V i ≠ 0`: it must differ from `f`'s eigenvalues at some `(n,N)=1`, `n ∉ S`.
      have hΨχ : Ψ i = χ := (Finset.mem_filter.mp hi).2
      -- `h i ≠ 0` (else `V i = 0`).
      have hhi0 : h i ≠ 0 := fun he ↦ hVi0 (by
        show (heq i ▸ levelRaise (M i) (l i) k (h i)) = 0
        rw [he, map_zero]
        generalize heq i = e; subst e; rfl)
      obtain ⟨n, hn, hnS, hne⟩ := hcon (M i) (hM i) (hcond i) (hMne i) (hMdvd i)
        (χM i) (h i) (lam i) (hh_new i) (hh_char i) hΨχ hhi0 (hlam_spec i)
      -- `g_old` has eigenvalue `f.eigenvalue n`; `V i` has eigenvalue `lam i n ≠ f.eigenvalue n`.
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      exact petN_eq_zero_of_ne_eigenvalues χ hg_old_char
        ((hΨχ ▸ hVΨ i : V i ∈ cuspFormCharSpace k χ)) hg_old_ne hVi0 hn
        (h_eig n hn hnS) (hV_eig i n hn) (fun he ↦ hne he.symm)
  -- Then `petN g_old g_old = ∑ petN g_old (V i) = 0`, contradicting `petN_definite`.
  have hpet0 : petN g_old g_old = 0 := by
    calc petN g_old g_old
        = petN g_old (∑ i ∈ s', V i) := by rw [← hcollapse]
      _ = ∑ i ∈ s', petN g_old (V i) := petN_sum_right s' g_old V
      _ = 0 := Finset.sum_eq_zero horth
  exact hg_old_ne (petN_definite g_old hpet0)

/-- **Old-part vanishing** (Miyake 4.6.12, steps (i)+(ii), p. 164).  If `f` is a
nonzero newform at level `N` and `g_old` is a common `T(n)`-**eigenform** in the χ-refined
old space sharing `f`'s eigenvalues off `S`, then `g_old = 0`.

The `h_eig` hypothesis is the faithful Miyake-4.6.10 form: `g_old` is *asserted* to be a
`T(n)`-eigenform with `f`'s eigenvalues for every `(n,N)=1`, `n ∉ S` (Theorem 4.6.12 supplies
this for `oldPart g` via the Hecke-stability of the old subspace, `oldPart_isEigen_of_eigenform`).

Proof (reduces to `newform_notMem_cuspFormsOldExtended`): if `g_old ≠ 0`, descend it
(`4.6.9(3)`/T008 = `exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar`, `4.6.2`,
linear independence of distinct-eigenvalue eigenforms) to a nonzero **new** eigenform `h` at a
proper divisor `M` sharing `f`'s eigenvalues; normalise (`4.6.11`, `c₁' = a₁(h) ≠ 0`); then
`ι(h) - c₁'•f` has vanishing coprime `q`-coefficients (`4.5.15(1)`), so
`ι(h) - c₁'•f ∈ cuspFormsOld ⊆ cuspFormsOldExtended` (`4.6.8` + `cuspFormsOld_le_cuspFormsOldExtended`),
while `ι(h) ∈ cuspFormsOldExtended` (`levelInclude_cusp_mem_cuspFormsOldExtended`, the trivial
inclusion `4.6.9(2)`); hence `f = c₁'⁻¹•ι(h) - c₁'⁻¹•(ι(h) - c₁'•f) ∈ cuspFormsOldExtended`,
contradicting `newform_notMem_cuspFormsOldExtended`.

**Status (2026-05-28).**  COMPLETE — **unconditional**.  Step (i) is `exists_matching_summand`
(above): a nonzero new eigenform `h` at a proper divisor level `M` (char `ψ`, `ψ∘unitsMap = χ`)
sharing `f`'s eigenvalues off `S`, via the `petN`-orthogonality engine + the `χ`-isotypic
collapse.  Step (ii) is discharged here: `c₁' = a₁(h) ≠ 0` by the **per-character
unconditional** Lemma 4.6.11 (`coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen_unconditional`,
Deliverable 2, which relies on the unconditional Main Lemma
`mainLemma_charSpace_routeB_unconditional`, Deliverable 1 — the dichotomy-based 4.6.8 with no
`h_chi_factor`).  The eigenvalue agreement off `S` is upgraded to all coprime indices across
the level gap by `eigenvalues_eq_all_coprime_cross_level`, so `ι(h) - c₁'•f` has vanishing
coprime `q`-coeffs, hence lies in `cuspFormsOld N k` (route-B Main Lemma at level `N`,
**unconditional** form) ⊆ `cuspFormsOldExtended`; with `ι(h) ∈ cuspFormsOldExtended`
(`levelInclude_cusp_mem_cuspFormsOldExtended`), this forces `f ∈ cuspFormsOldExtended`,
contradicting `newform_notMem_cuspFormsOldExtended`. -/
theorem oldPart_eq_zero_of_shared_eigenvalues
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (g_old : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_old : g_old ∈ cuspFormsOldChar N k χ m_χ)
    (hg_old_char : g_old ∈ cuspFormCharSpace k χ)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      heckeT_n_cusp k n.val g_old = f.eigenvalue n • g_old) :
    g_old = 0 := by
  -- Suppose `g_old ≠ 0`.  Step (i): extract the matching summand.
  by_contra hg0
  obtain ⟨M, hM_NeZero, _hcond, hMne, hMN, ψ, h, lam, hh_new, hh_char, hψχ, hh_ne,
    hh_eig, hh_lam⟩ :=
    exists_matching_summand f χ m_χ g_old hg_old hg_old_char hg0 S h_eig
  -- Bundle `h` as an `Eigenform M k` with classical eigenvalues `lam` (at coprime indices).
  have hh_char_cusp : h ∈ cuspFormCharSpace k ψ := hh_char
  have hψ_mod : h.toModularForm' ∈ modFormCharSpace k ψ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) ψ h).mpr
      hh_char
  set h_eig_b : Eigenform M k := eigenformOfIsEigenform ψ h hh_char_cusp ⟨lam, hh_eig⟩
    with hh_eig_b
  have hh_eig_b_cusp : h_eig_b.toCuspForm = h := rfl
  have hψ_mod' : h_eig_b.toCuspForm.toModularForm' ∈ modFormCharSpace k ψ := by
    rw [hh_eig_b_cusp]; exact hψ_mod
  -- `c₁' = a₁(h) ≠ 0` by the unconditional Lemma 4.6.11 (Deliverable 2).
  set c₁' := (ModularFormClass.qExpansion (1 : ℝ) h).coeff 1 with hc₁'_def
  have hc₁'_ne : c₁' ≠ 0 :=
    coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen_unconditional h_eig_b ψ hψ_mod' hh_new hh_ne
  have hc₁'_ne' : (ModularFormClass.qExpansion (1 : ℝ) h_eig_b.toCuspForm).coeff 1 ≠ 0 := by
    rw [hh_eig_b_cusp]; exact hc₁'_ne
  -- `M < N`.
  have hMltN : M < N := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hMN) hMne
  -- The trivial inclusion `ι(h)` at level `N`, lying in `cuspFormCharSpace k χ`.
  set ιh : CuspForm ((Gamma1 N).map (mapGL ℝ)) k := levelInclude_cusp hMN k h with hιh_def
  have hιh_char : ιh ∈ cuspFormCharSpace k χ := by
    have := levelInclude_cusp_mem_cuspFormCharSpace_comp hMN ψ hh_char_cusp
    rwa [hψχ] at this
  -- Eigenvalue agreement at ALL coprime indices (cross-level upgrade of the off-`S` data).
  have h_lam_eq : ∀ n : ℕ+, Nat.Coprime n.val N → lam n = f.eigenvalue n := by
    have h_off : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
        f.eigenvalue n = h_eig_b.eigenvalue n := fun n hn hnS ↦ by
      rw [eigenformOfIsEigenform_eigenvalue ψ h hh_char_cusp lam hh_eig hh_ne n
          (hn.coprime_dvd_right hMN)]
      exact (hh_lam n hn hnS).symm
    intro n hn
    have := (eigenvalues_eq_all_coprime_cross_level f h_eig_b χ hfχ ψ hψ_mod'
      hc₁'_ne' hMN hψχ S h_off n hn).symm
    rwa [eigenformOfIsEigenform_eigenvalue ψ h hh_char_cusp lam hh_eig hh_ne n
      (hn.coprime_dvd_right hMN)] at this
  -- `ι(h) - c₁'•f` vanishes at every index coprime to `N`.
  have h_diff_char : ιh - c₁' • f.toCuspForm ∈ cuspFormCharSpace k χ :=
    (cuspFormCharSpace k χ).sub_mem hιh_char ((cuspFormCharSpace k χ).smul_mem c₁'
      ((cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
        f.toCuspForm).mp (by convert hfχ using 1)))
  have h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) (ιh - c₁' • f.toCuspForm)).coeff n = 0 := by
    intro n hn
    show (ModularFormClass.qExpansion (1 : ℝ)
        (⇑ιh.toModularForm' - ⇑(c₁' • f.toCuspForm).toModularForm')).coeff n = 0
    rw [qExpansion_sub one_pos one_mem_strictPeriods_Gamma1_map_local, map_sub, sub_eq_zero]
    by_cases hn0 : n = 0
    · subst hn0
      rw [ModularFormClass.qExpansion_coeff_zero _ one_pos one_mem_strictPeriods_Gamma1_map_local,
          ModularFormClass.qExpansion_coeff_zero _ one_pos one_mem_strictPeriods_Gamma1_map_local,
          show (⇑ιh.toModularForm' : UpperHalfPlane → ℂ) = ⇑ιh from rfl,
          show (⇑(c₁' • f.toCuspForm).toModularForm' : UpperHalfPlane → ℂ) =
            ⇑(c₁' • f.toCuspForm) from rfl,
          (CuspFormClass.zero_at_infty ιh).valueAtInfty_eq_zero,
          (CuspFormClass.zero_at_infty (c₁' • f.toCuspForm)).valueAtInfty_eq_zero]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      set np : ℕ+ := ⟨n, hn_pos⟩ with hnp
      have hnp_val : (np : ℕ) = n := rfl
      have hnM : Nat.Coprime np.val M := hn.coprime_dvd_right hMN
      -- the two underlying functions of `ιh.toModularForm'` and `h.toModularForm'` agree.
      have hfun : (⇑ιh.toModularForm' : UpperHalfPlane → ℂ) =
          ⇑h_eig_b.toCuspForm.toModularForm' := by
        rw [show (⇑ιh.toModularForm' : UpperHalfPlane → ℂ) = ⇑ιh from rfl,
          show (⇑h_eig_b.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑h_eig_b.toCuspForm
            from rfl, hh_eig_b_cusp, hιh_def, levelInclude_cusp_coe]
      -- LHS coefficient: `a_n(ι h) = a_n(h) = c₁' · λ_n(h_eig_b) = c₁' · f.eigenvalue n`.
      have hL : (ModularFormClass.qExpansion (1 : ℝ) (⇑ιh.toModularForm')).coeff n =
          c₁' * f.eigenvalue np := by
        rw [qExpansion_ext2 ιh.toModularForm' h_eig_b.toCuspForm.toModularForm' hfun, ← hnp_val,
          show (⇑h_eig_b.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) =
            ⇑h_eig_b.toCuspForm from rfl,
          Eigenform.coeff_eq_coeff_one_mul_eigenvalue h_eig_b ψ hψ_mod' np hnM,
          eigenformOfIsEigenform_eigenvalue ψ h hh_char_cusp lam hh_eig hh_ne np hnM,
          h_lam_eq np hn, hh_eig_b_cusp]
      -- RHS coefficient: `a_n(c₁' • f) = c₁' · a_n(f) = c₁' · f.eigenvalue n`.
      have hR : (ModularFormClass.qExpansion (1 : ℝ)
          (⇑(c₁' • f.toCuspForm).toModularForm')).coeff n = c₁' * f.eigenvalue np := by
        rw [show (⇑(c₁' • f.toCuspForm).toModularForm' : UpperHalfPlane → ℂ) =
              c₁' • ⇑f.toCuspForm.toModularForm' from rfl,
          qExpansion_smul one_pos one_mem_strictPeriods_Gamma1_map_local, PowerSeries.coeff_smul,
          smul_eq_mul, ← hnp_val, Newform.eigenvalue_eq_coeff f np hn χ hfχ]
        congr 1
      rw [hL, hR]
  -- Route B at level `N` (unconditional form): the difference is old.
  have h_diff_old : ιh - c₁' • f.toCuspForm ∈ cuspFormsOld N k :=
    mainLemma_charSpace_routeB_unconditional χ (ιh - c₁' • f.toCuspForm) h_diff_char h_vanish
  -- Upcast: difference ∈ cuspFormsOldExtended; `ι(h)` ∈ cuspFormsOldExtended.
  have h_diff_ext : ιh - c₁' • f.toCuspForm ∈ cuspFormsOldExtended N k :=
    cuspFormsOld_le_cuspFormsOldExtended h_diff_old
  have hιh_ext : ιh ∈ cuspFormsOldExtended N k :=
    levelInclude_cusp_mem_cuspFormsOldExtended hMN hMltN h
  -- Hence `c₁' • f = ι(h) - (ι(h) - c₁'•f) ∈ cuspFormsOldExtended`, so `f ∈ cuspFormsOldExtended`.
  have hcf_ext : c₁' • f.toCuspForm ∈ cuspFormsOldExtended N k := by
    have := (cuspFormsOldExtended N k).sub_mem hιh_ext h_diff_ext
    simpa using this
  have hf_ext : f.toCuspForm ∈ cuspFormsOldExtended N k := by
    have := (cuspFormsOldExtended N k).smul_mem c₁'⁻¹ hcf_ext
    rwa [smul_smul, inv_mul_cancel₀ hc₁'_ne, one_smul] at this
  -- Contradiction: a nonzero newform (`a₁(f) = 1`) is not in the extended old space.
  have hf_ne : f.toCuspForm ≠ 0 := by
    intro hf0
    have h1 : (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff 1 = 1 := f.isNorm
    rw [hf0, show (⇑(0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) =
        (0 : UpperHalfPlane → ℂ) from rfl, qExpansion_zero] at h1
    simp at h1
  exact newform_notMem_cuspFormsOldExtended f hf_ne hf_ext

/-! ## Theorem 4.6.12: assembly -/

/-- **Miyake Theorem 4.6.12 (Strong Multiplicity One, full constant-multiple form).**

Let `f` be a (normalised) `Newform` at level `N` with Nebentypus `χ`, and let `g` be a
common `T(n)`-eigenfunction in the full χ-space `S_k(Γ₁(N), χ)` (encoded as an
`Eigenform`), sharing `f`'s eigenvalues at all `n` coprime to `N` outside a finite set
`S`.  Then `g = c • f` for some `c ∈ ℂ` (in fact `c = a₁(g)`).

**Unconditional.**  The previous `h_chi_factor` hypothesis (the per-prime character
factorisation through `ZMod (N/p)`) is supplied internally via the dichotomy-based
`mainLemma_charSpace_routeB_unconditional` (Deliverable 1) and
`coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen_unconditional` (Deliverable 2), threaded
through the new-part (T004) and old-part (T010) sub-results.  This does not modify the
frozen `strongMultiplicityOne_axiom_clean` — the present proof takes the direct-disjointness
route through T004/T010 rather than through the axiom-clean variant. -/
theorem strongMultiplicityOne_constMul
    (f : Newform N k) (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    ∃ c : ℂ, g.toCuspForm = c • f.toCuspForm := by
  -- Decompose `g = oldPart g + newPart g`.  The old part is a `T(n)`-eigenform with `f`'s
  -- eigenvalues lying in `χ`-refined old space, so it vanishes (corrected T010); hence `g` is
  -- new and the new-part identity (T004) gives `g = a₁(g) • f`.
  have hgχ_cusp : g.toCuspForm ∈ cuspFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ
      g.toCuspForm).mp (by convert hgχ using 1)
  -- Lift `χ` to a Dirichlet character to access the reverse old-space inclusion (T012).
  set χ_dir : DirichletCharacter ℂ N := Newform.dirichletLift χ with hχ_dir_def
  have h_round : χ_dir.toUnitHom = χ := MulChar.equivToUnitHom.apply_symm_apply χ
  -- `oldPart g` is a `T(n)`-eigenform sharing `f`'s eigenvalues (Hecke-stability, 4.6.10).
  have h_old_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      haveI : NeZero n.val := ⟨n.pos.ne'⟩
      heckeT_n_cusp k n.val (oldPart g.toCuspForm) =
        f.eigenvalue n • oldPart g.toCuspForm := fun n hn hnS ↦ by
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    rw [oldPart_isEigen_of_eigenform g n hn, h_eig n hn hnS]
  -- `oldPart g ∈ cuspFormsOld ⊓ S_k(Γ₁(N),χ) ≤ cuspFormsOldChar` (T012).
  have h_old_char : oldPart g.toCuspForm ∈ cuspFormsOldChar N k χ χ_dir.conductor := by
    have h_inf : oldPart g.toCuspForm ∈
        cuspFormsOld N k ⊓ cuspFormCharSpace k χ_dir.toUnitHom := by
      rw [h_round]
      exact ⟨oldPart_mem_cuspFormsOld g.toCuspForm,
        oldPart_mem_cuspFormCharSpace χ hgχ_cusp⟩
    have := cuspFormsOld_inf_charSpace_le_cuspFormsOldChar (k := k) χ_dir h_inf
    rwa [h_round] at this
  have h_old_charSpace : oldPart g.toCuspForm ∈ cuspFormCharSpace k χ :=
    oldPart_mem_cuspFormCharSpace χ hgχ_cusp
  -- Corrected T010 (unconditional): the old part vanishes.
  have h_old_zero : oldPart g.toCuspForm = 0 :=
    oldPart_eq_zero_of_shared_eigenvalues f χ χ_dir.conductor hfχ
      (oldPart g.toCuspForm) h_old_char h_old_charSpace S h_old_eig
  -- Hence `g` is new.
  have hg_new : g.toCuspForm ∈ cuspFormsNew N k :=
    (mem_cuspFormsNew_iff_oldPart_eq_zero g.toCuspForm).mpr h_old_zero
  -- New-part identity (T004, unconditional), applied to `g` itself.
  refine ⟨(ModularFormClass.qExpansion (1 : ℝ) g.toCuspForm).coeff 1, ?_⟩
  exact newPart_eq_smul_of_shared_eigenvalues f g χ hfχ hgχ hg_new S h_eig

end HeckeRing.GL2
