/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.SMOObligations

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

/-- **Miyake Lemma 4.6.9(3) (generation)**: every element of the χ-refined old space is a
finite sum of `V_l`-images of **eigenforms** in new spaces at proper divisor levels that
are multiples of `m_χ`.  This is the descent normal form used in step (i) of 4.6.12. -/
theorem exists_levelRaise_eigen_decomposition_of_mem_cuspFormsOldChar
    (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsOldChar N k χ m_χ) :
    ∃ (ι : Type) (_ : Fintype ι) (M : ι → ℕ) (l : ι → ℕ)
      (_ : ∀ i, NeZero (M i)) (_ : ∀ i, NeZero (l i))
      (_ : ∀ i, m_χ ∣ M i) (_ : ∀ i, M i ≠ N) (heq : ∀ i, l i * M i = N)
      (h : ∀ i, CuspForm ((Gamma1 (M i)).map (mapGL ℝ)) k),
      (∀ i, h i ∈ cuspFormsNew (M i) k) ∧
      (∀ i, IsEigenform (h i)) ∧
      f = ∑ i, (heq i ▸ levelRaise (M i) (l i) k (h i)) := by
  sorry

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
      (∀ i, h i ∈ cuspFormsNew N k) ∧ (∀ i, IsEigenform (h i)) ∧ g = ∑ i, h i := by
  have hg_char : g ∈ cuspFormCharSpace k χ :=
    (cuspFormToModularForm_mem_modFormCharSpace_iff_mem_cuspFormCharSpace (k := k) χ g).mp
      (by convert hgχ using 1)
  obtain ⟨ι, hι, h, h_new, h_char, h_eigen, h_sum⟩ :=
    exists_eigenform_decomposition_of_invariant χ (cuspFormsNew N k)
      (fun n _ hn f hf ↦ heckeT_n_preserves_cuspFormsNew n hn f hf) g hg_char hg_new
  exact ⟨ι, hι, h, h_new, fun i ↦ (isEigenform_iff (h i)).mpr (h_eigen i), h_sum⟩

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

/-! ## Step: the new part equals `b₁ • f`

Close to the existing same-level uniqueness; reuses `strongMultiplicityOne_axiom_clean`
shape (Main Lemma + new∩old=0) but for an un-normalised new eigenform `g_new`. -/

/-- The renormalised eigenform `c • g_new` carries the same Hecke ring eigenvalues as
`g_new` (scalar multiplication commutes with the linear ring action).  Packaged as a
`Newform` whenever `c • g_new` lies in the new subspace and is normalised at period 1;
its classical eigenvalues coincide with `g_new`'s. -/
private def newformOfSmulEigenform
    (g_new : Eigenform N k) (c : ℂ)
    (hnew : c • g_new.toCuspForm ∈ cuspFormsNew N k)
    (hnorm : (ModularFormClass.qExpansion (1 : ℝ) (c • g_new.toCuspForm)).coeff 1 = 1) :
    Newform N k where
  toCuspForm := c • g_new.toCuspForm
  χ := g_new.χ
  mem_charSpace := (modFormCharSpace k g_new.χ).smul_mem c g_new.mem_charSpace
  ringEigenvalue := g_new.ringEigenvalue
  isRingEigen n hn := by
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    have hsmul :
        (⟨(c • g_new.toCuspForm).toModularForm',
            (modFormCharSpace k g_new.χ).smul_mem c g_new.mem_charSpace⟩ :
          modFormCharSpace k g_new.χ) =
          c • (⟨g_new.toCuspForm.toModularForm', g_new.mem_charSpace⟩ :
            modFormCharSpace k g_new.χ) := by
      apply Subtype.ext
      rfl
    rw [hsmul, map_smul, g_new.isRingEigen n hn, smul_comm]
  isNew := hnew
  isNorm := hnorm

private theorem newformOfSmulEigenform_eigenvalue
    (g_new : Eigenform N k) (c : ℂ)
    (hnew : c • g_new.toCuspForm ∈ cuspFormsNew N k)
    (hnorm : (ModularFormClass.qExpansion (1 : ℝ) (c • g_new.toCuspForm)).coeff 1 = 1)
    (n : ℕ+) :
    (newformOfSmulEigenform g_new c hnew hnorm).eigenvalue n = g_new.eigenvalue n := rfl

/-- **New-part identity** (Miyake 4.6.12, new part, p. 163).  If `f` is a normalised
newform and `g_new` is a common eigenfunction in the new subspace sharing `f`'s
eigenvalues off `S`, then `g_new = b₁ • f` where `b₁ = a₁(g_new)`. -/
theorem newPart_eq_smul_of_shared_eigenvalues
    (f : Newform N k) (g_new : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g_new.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hg_new : g_new.toCuspForm ∈ cuspFormsNew N k)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g_new.eigenvalue n)
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
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
  · -- `b₁ ≠ 0` by Lemma 4.6.11; renormalise `g_new` to a `Newform` and apply same-level SMO.
    have hb₁_ne : b₁ ≠ 0 :=
      coeff_one_ne_zero_of_mem_cuspFormsNew_of_eigen g_new χ hgχ hg_new hg0 N dvd_rfl h_chi_factor
    have hnew : b₁⁻¹ • g_new.toCuspForm ∈ cuspFormsNew N k :=
      (cuspFormsNew N k).smul_mem b₁⁻¹ hg_new
    have hnorm :
        (ModularFormClass.qExpansion (1 : ℝ) (b₁⁻¹ • g_new.toCuspForm)).coeff 1 = 1 := by
      rw [qExpansion_one_coeff_one_smul_local g_new.toCuspForm b₁⁻¹, ← hb₁_def,
        inv_mul_cancel₀ hb₁_ne]
    set f_g : Newform N k := newformOfSmulEigenform g_new b₁⁻¹ hnew hnorm with hf_g_def
    have hf_g_χ : f_g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ :=
      (modFormCharSpace k χ).smul_mem b₁⁻¹ hgχ
    have h_eig' : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
        f.eigenvalue n = f_g.eigenvalue n := fun n hn hnS ↦ by
      rw [newformOfSmulEigenform_eigenvalue]
      exact h_eig n hn hnS
    have hfg : f.toCuspForm = f_g.toCuspForm :=
      strongMultiplicityOne_axiom_clean f f_g χ hfχ hf_g_χ S h_eig' h_chi_factor
    have hkey : b₁⁻¹ • g_new.toCuspForm = f.toCuspForm := hfg.symm
    rw [← hkey, smul_smul, mul_inv_cancel₀ hb₁_ne, one_smul]

/-! ## Step: the old part is zero (the descent argument, steps (i)+(ii))

This is where gap #4 (4.6.9) and gap #3 (4.6.2) are consumed. -/

/-- **Old-part vanishing** (Miyake 4.6.12, steps (i)+(ii), p. 164).  If `f` is a
nonzero newform at level `N` and `g_old` is a common eigenfunction in the χ-refined old
space sharing `f`'s eigenvalues off `S`, then `g_old = 0`.

Proof: descend `g_old` to a nonzero new eigenform `h` at a proper divisor (`4.6.9(3)`,
`4.6.2`, linear independence); normalise `h` (`4.6.11`); then `h - c₁' • f ∈ old(N)`
(`4.6.8`) and `h ∈ old(N)` (`4.6.9(2)`) give `f ∈ old(N)`, contradicting `f` new. -/
theorem oldPart_eq_zero_of_shared_eigenvalues
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) (m_χ : ℕ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (g_old : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hg_old : g_old ∈ cuspFormsOldChar N k χ m_χ)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      ∀ lam : ℂ, (haveI : NeZero n.val := ⟨n.pos.ne'⟩
        heckeT_n_cusp k n.val g_old = lam • g_old) → f.eigenvalue n = lam)
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    g_old = 0 := by
  sorry

/-! ## Theorem 4.6.12: assembly -/

/-- **Miyake Theorem 4.6.12 (Strong Multiplicity One, full constant-multiple form).**

Let `f` be a (normalised) `Newform` at level `N` with Nebentypus `χ`, and let `g` be a
common `T(n)`-eigenfunction in the full χ-space `S_k(Γ₁(N), χ)` (encoded as an
`Eigenform`), sharing `f`'s eigenvalues at all `n` coprime to `N` outside a finite set
`S`.  Then `g = c • f` for some `c ∈ ℂ` (in fact `c = a₁(g)`).

Depends on `strongMultiplicityOne_axiom_clean` (via the new-part argument) and never
modifies it.  The `h_chi_factor` hypothesis is inherited from the route-B Main Lemma. -/
theorem strongMultiplicityOne_constMul
    (f : Newform N k) (g : Eigenform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_eig : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n)
    (h_chi_factor : ∀ (p : ℕ) (hp_in : p ∈ N.primeFactors),
      haveI : NeZero (N / p) := ⟨by
        have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp_in
        have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp_in
        have hN_pos : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
        exact (Nat.div_pos (Nat.le_of_dvd hN_pos hpN) hp_prime.pos).ne'⟩
      ∃ (χ' : (ZMod (N / p))ˣ →* ℂˣ),
        χ = χ'.comp (ZMod.unitsMap
          (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp_in)))) :
    ∃ c : ℂ, g.toCuspForm = c • f.toCuspForm := by
  sorry

end HeckeRing.GL2
