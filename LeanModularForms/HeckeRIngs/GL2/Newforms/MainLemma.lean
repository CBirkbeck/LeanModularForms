/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import LeanModularForms.Eigenforms.ConductorTheorem
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: character decomposition, the `Newform` structure, and the Main Lemma

Character-space decomposition of the old/new subspaces, the `Newform` structure (DS Def 5.8.1),
primitive forms, the eigenvalue-as-Fourier-coefficient identity, and the Atkin-Lehner Main Lemma
(DS Thm 5.7.1) with its uniqueness corollary.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

section CharSpaceDecomposition

/-- **`diamondOpCuspHom`-invariance of `cuspFormsOld N k`.** -/
lemma diamondOpCuspHom_preserves_cuspFormsOld
    (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsOld N k) :
    diamondOpCuspHom k d f ∈ cuspFormsOld N k :=
  diamondOp_preserves_cuspFormsOld d f hf

/-- **`diamondOpCuspHom`-invariance of `cuspFormsNew N k`.** -/
lemma diamondOpCuspHom_preserves_cuspFormsNew
    (d : (ZMod N)ˣ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsNew N k) :
    diamondOpCuspHom k d f ∈ cuspFormsNew N k :=
  diamondOp_preserves_cuspFormsNew d f hf

/-- **Finsupp-indexed character decomposition of a newform subspace element.**
Every `f ∈ cuspFormsNew N k` is a finitely-supported sum of Nebentypus
components, each simultaneously in `cuspFormsNew N k` and in its character
subspace. -/
theorem exists_finsupp_charSpace_of_cuspFormsNew (k : ℤ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ) ∧
      (g.sum fun _ y ↦ y) = f :=
  exists_finsupp_charSpace_of_diamondOpCuspHom_invariant k (cuspFormsNew N k)
    diamondOpCuspHom_preserves_cuspFormsNew hf

end CharSpaceDecomposition

/-- A **newform** of level Γ₁(N) and weight k: a cusp form that is
1. an eigenform (common eigenfunction of all T_n with (n,N)=1)
2. in the new subspace
3. normalised: a_1(f) = 1

By Atkin-Lehner uniqueness (DS Theorem 5.8.2), newforms are uniquely determined
by their Hecke eigenvalues away from the level. -/
@[ext]
structure Newform (N : ℕ) [NeZero N] (k : ℤ)
    extends Eigenform N k where
  /-- The form is in the new subspace. -/
  isNew : toCuspForm ∈ cuspFormsNewExtended N k
  /-- Normalisation at the **canonical Fourier period** (`h = 1`): the first
  Fourier coefficient is `1`, i.e. `a₁ = 1` (the Diamond–Shurman / Miyake
  normalisation). -/
  isNorm : (ModularFormClass.qExpansion (1 : ℝ) toCuspForm).coeff 1 = 1

/-- Predicate version: f is a newform if it's an eigenform in the new subspace
with `a_1 = 1` (at period 1). -/
structure IsNewform (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop where
  isEigen : IsEigenform f
  isNew : f ∈ cuspFormsNewExtended N k
  isNorm : (ModularFormClass.qExpansion (1 : ℝ) f).coeff 1 = 1

/-- A `Newform` satisfies `IsNewform`. -/
theorem Newform.isNewform (f : Newform N k) : IsNewform f.toCuspForm where
  isEigen := f.toEigenform.isEigenform
  isNew := f.isNew
  isNorm := f.isNorm

/-- A `Newform` is **primitive** at its level if its underlying cusp form
lies in the new subspace. -/
def Newform.IsPrimitive (f : Newform N k) : Prop :=
  f.toCuspForm ∈ cuspFormsNewExtended N k

/-- Every `Newform` is primitive at its own level. -/
theorem Newform.isPrimitive (f : Newform N k) : f.IsPrimitive := f.isNew

/-- The **conductor** of a `Newform N k` is the smallest level at which `f`
arises as a `Newform`; for a bundled `Newform N k` this is `N` itself. -/
noncomputable def Newform.conductor (_f : Newform N k) : ℕ := N

private lemma qExpansion_one_coeff_one_smul_of_norm
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_norm : (ModularFormClass.qExpansion (1 : ℝ) f.toModularForm').coeff 1 = 1)
    (c : ℂ) :
    (ModularFormClass.qExpansion (1 : ℝ) (c • f)).coeff 1 = c := by
  change (ModularFormClass.qExpansion (1 : ℝ) (⇑(c • f : CuspForm _ k))).coeff 1 = c
  rw [show (⇑(c • f : CuspForm _ k) : UpperHalfPlane → ℂ) = c • ⇑f from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl,
    qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map N),
    PowerSeries.coeff_smul, smul_eq_mul, h_norm, mul_one]

lemma qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N) (χ : (ZMod N)ˣ →* ℂˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_char : f.toModularForm' ∈ modFormCharSpace k χ) :
    (ModularFormClass.qExpansion (1 : ℝ) (heckeT_n_cusp k n f)).coeff 1 =
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n := by
  rw [show (⇑(heckeT_n_cusp k n f) : UpperHalfPlane → ℂ) =
        ⇑(heckeT_n_cusp k n f).toModularForm' from rfl,
    show (⇑f : UpperHalfPlane → ℂ) = ⇑f.toModularForm' from rfl, heckeT_n_cusp_toModularForm']
  have h := fourierCoeff_heckeT_n_period_one (N := N) k n hn χ hf_char 1
  simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton] at h
  have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
    ext; simp [ZMod.coe_unitOfCoprime]
  simpa only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
    h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] using h

/-- For a `Newform` f lying in a character eigenspace `modFormCharSpace k χ`,
the eigenvalue at `n` (coprime to `N`) equals the `n`-th **canonical
Fourier coefficient** of `f` (period `h = 1`).  The character hypothesis
`hf_char` is required because `fourierCoeff_heckeT_n_period_one` is stated for
forms living in a single Nebentypus eigenspace. -/
theorem Newform.eigenvalue_eq_coeff (f : Newform N k) (n : ℕ+)
    (hn : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.eigenvalue n =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  rw [← qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff n.val hn χ f.toCuspForm hf_char,
    f.isEigen n hn]
  exact (qExpansion_one_coeff_one_smul_of_norm f.toCuspForm f.isNorm _).symm

/-- **Un-normalised analogue of `Newform.eigenvalue_eq_coeff`.**  For an
`Eigenform` `f` lying in `modFormCharSpace k χ` and *assumed normalised at
period 1* (`a₁ = 1`), the classical eigenvalue at `n` (coprime to `N`) equals
the `n`-th canonical Fourier coefficient.  Identical proof to
`Newform.eigenvalue_eq_coeff`, but the normalisation is taken as a hypothesis
rather than read off the `Newform.isNorm` field. -/
theorem Eigenform.eigenvalue_eq_coeff_of_norm (f : Eigenform N k) (n : ℕ+)
    (hn : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h_norm₁ : (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff 1 = 1) :
    f.eigenvalue n =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  rw [← qExpansion_one_coeff_one_heckeT_n_cusp_eq_coeff n.val hn χ f.toCuspForm hf_char,
    f.isEigen n hn]
  exact (qExpansion_one_coeff_one_smul_of_norm f.toCuspForm h_norm₁ (f.eigenvalue n)).symm

private lemma qExpansion_one_levelRaise_coeff_eq_zero_of_not_dvd
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d]
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (n : ℕ) (hn : ¬ d ∣ n) :
    (ModularFormClass.qExpansion (1 : ℝ) (levelRaise M d k g)).coeff n = 0 := by
  let g_mf : ModularForm ((Gamma1 M).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := g.toSlashInvariantForm
      holo' := g.holo'
      bdd_at_cusps' := fun {c} hc γ hγ ↦
        (g.zero_at_cusps' hc γ hγ).isBoundedAtImInfty }
  have h_fun_eq : (⇑(levelRaise M d k g) : UpperHalfPlane → ℂ) =
      ⇑(modularFormLevelRaise M d k g_mf) := by rw [coe_modularFormLevelRaise]; rfl
  rw [show ModularFormClass.qExpansion (1 : ℝ) (levelRaise M d k g) =
      ModularFormClass.qExpansion (1 : ℝ) (modularFormLevelRaise M d k g_mf) from
        qExpansion_ext2 _ _ h_fun_eq,
    qExpansion_one_modularFormLevelRaise_coeff, if_neg hn]

/-- **Oldforms have zero Fourier coefficients at indices coprime to the level.**
This is the **reverse (easy) direction** of
`Newforms.mainLemma` (DS Theorem 5.7.1): every `f ∈ S_k(Γ₁(N))^old`
satisfies `a_n(f) = 0` whenever `(n, N) = 1`.

Together with `Newforms.mainLemma` (the hard converse), this
characterises oldforms by their Fourier support at coprime-to-`N`
indices. -/
theorem cuspFormsOld_coeff_eq_zero_of_coprime
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf : f ∈ cuspFormsOld N k)
    (n : ℕ) (hn : Nat.Coprime n N) :
    (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0 := by
  refine Submodule.span_induction
    (p := fun (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ ↦
      (ModularFormClass.qExpansion (1 : ℝ) x).coeff n = 0)
    ?_ ?_ ?_ ?_ hf
  · rintro f₀ ⟨M, d, _, _, hd_lt, heq, g, rfl⟩
    subst heq
    have h_coprime_d : Nat.Coprime n d := hn.coprime_dvd_right ⟨M, rfl⟩
    refine qExpansion_one_levelRaise_coeff_eq_zero_of_not_dvd g n fun h_dvd ↦ ?_
    rw [Nat.Coprime, Nat.gcd_eq_right h_dvd] at h_coprime_d; lia
  · simp [qExpansion_zero]
  · intro x y _ _ ihx ihy
    have h_eq : ModularFormClass.qExpansion (1 : ℝ)
        (⇑(x + y) : UpperHalfPlane → ℂ) =
        ModularFormClass.qExpansion (1 : ℝ) ⇑x +
          ModularFormClass.qExpansion (1 : ℝ) ⇑y := by
      have := qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ)) (h := 1) (a := k) (b := k)
        one_pos (one_mem_strictPeriods_Gamma1_map N) x y
      convert this using 2
    change (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 ⇑(x + y)) = 0
    rw [h_eq, map_add, ihx, ihy, zero_add]
  · intro c x _ ihx
    have h_eq : ModularFormClass.qExpansion (1 : ℝ)
        (⇑(c • x) : UpperHalfPlane → ℂ) =
        c • ModularFormClass.qExpansion (1 : ℝ) ⇑x := by
      have := qExpansion_smul (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (h := 1) one_pos
        (one_mem_strictPeriods_Gamma1_map N) c x
      convert this using 2
    change (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 ⇑(c • x)) = 0
    rw [h_eq, show (PowerSeries.coeff n)
      (c • ModularFormClass.qExpansion (1 : ℝ) ⇑x) =
      c * (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑x) from
        by simp [smul_eq_mul], ihx, mul_zero]

/-- **The Main Lemma** (DS Theorem 5.7.1, Atkin-Lehner [AL70]):
If `f ∈ S_k(Γ₁(N))` has Fourier expansion `f(τ) = Σ aₙ qⁿ` with `aₙ = 0`
whenever `(n, N) = 1`, then `f` is an oldform.

This is the technical heart of the newform theory; the full proof requires the
spectral theorem for Hecke operators and the Petersson adjoint formula. -/
theorem mainLemma
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k := by
  -- Decompose `f = f_old + f_new`; for each eigenform `g ∈ cuspFormsNew` with
  -- eigenvalue `λ_n ≠ 0`, the adjoint relation gives `⟨f, g⟩ = λ_n⁻¹ ⟨T_n f, g⟩`,
  -- which vanishes since `a_n(f) = 0` for coprime `n`, forcing `f_new = 0`.  The
  -- inputs (`exists_simultaneous_eigenform_basis`, `heckeT_n_adjoint`) are not yet
  -- available, so the conclusion is left unproved.
  sorry

private lemma newform_diff_coprime_coeff_eq_zero
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n)
    (n : ℕ) (hn : Nat.Coprime n N) :
    (ModularFormClass.qExpansion (1 : ℝ) (f.toCuspForm - g.toCuspForm)).coeff n = 0 := by
  have h1_period := one_mem_strictPeriods_Gamma1_map N
  conv_lhs =>
    rw [show (⇑f.toCuspForm - ⇑g.toCuspForm) =
        (⇑f.toCuspForm.toModularForm' - ⇑g.toCuspForm.toModularForm') from rfl]
  rw [qExpansion_sub one_pos h1_period, map_sub, sub_eq_zero]
  by_cases hn0 : n = 0
  · subst hn0
    simp [Nat.Coprime, Nat.gcd_zero_left] at hn
    subst hn
    have h_zero_f := (CuspFormClass.zero_at_infty f.toCuspForm).valueAtInfty_eq_zero
    have h_zero_g := (CuspFormClass.zero_at_infty g.toCuspForm).valueAtInfty_eq_zero
    rw [ModularFormClass.qExpansion_coeff_zero _ one_pos h1_period,
      ModularFormClass.qExpansion_coeff_zero _ one_pos h1_period,
      show (⇑f.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl,
      show (⇑g.toModularForm' : UpperHalfPlane → ℂ) = ⇑g.toCuspForm from rfl, h_zero_f, h_zero_g]
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  have h_eq := h ⟨n, hn_pos⟩ hn
  rwa [Newform.eigenvalue_eq_coeff f ⟨n, hn_pos⟩ hn χ hfχ,
    Newform.eigenvalue_eq_coeff g ⟨n, hn_pos⟩ hn χ hgχ] at h_eq

private lemma newform_diff_mem_cuspFormsNew (f g : Newform N k) :
    f.toCuspForm - g.toCuspForm ∈ cuspFormsNew N k :=
  (cuspFormsNew N k).sub_mem (cuspFormsNewExtended_le_cuspFormsNew f.isNew)
    (cuspFormsNewExtended_le_cuspFormsNew g.isNew)

/-- **Atkin-Lehner uniqueness** (DS Theorem 5.8.2 part 1): two newforms in
`S_k(Γ₁(N), χ)` with the same eigenvalues at all primes `(p, N) = 1` are equal.
Both newforms must lie in the same Nebentypus eigenspace `modFormCharSpace k χ`,
as required by `Newform.eigenvalue_eq_coeff` to bridge `λ_n → a_n`. -/
theorem newform_unique
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine sub_eq_zero.mp <|
    Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _ ?_
      (newform_diff_mem_cuspFormsNew f g)
  exact mainLemma _ (newform_diff_coprime_coeff_eq_zero f g χ hfχ hgχ h)

end HeckeRing.GL2
