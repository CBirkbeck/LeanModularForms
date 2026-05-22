/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.SlashActionAuxil
import LeanModularForms.Eigenforms.ConductorTheorem
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import LeanModularForms.HeckeRIngs.GL2.Newforms.LevelRaiseComm

/-!
# Newforms: character decomposition, the `Newform` structure, and the Main Lemma

Character-space decomposition of the old/new subspaces, the `Newform` structure (DS Def 5.8.1), primitive forms, the eigenvalue-as-Fourier-coefficient identity, and the Atkin-Lehner Main Lemma (DS Thm 5.7.1) with its uniqueness corollary.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### Character decomposition of the oldform / newform subspaces

Both `cuspFormsOld N k` and `cuspFormsNew N k` are stable under every diamond
operator `⟨d⟩` (`diamondOp_preserves_cuspFormsOld` resp.
`_cuspFormsNew`), so they inherit the Nebentypus character decomposition
supplied by `CharacterDecomp.lean`.

These specialisations turn the generic invariant-submodule API into direct
downstream tools: every oldform / newform splits uniquely as a finite sum of
Nebentypus pieces, each simultaneously an oldform / newform **and** a pure
`χ`-eigenform for the diamond operators. This is the structural input for the
composite-`N` `mainLemma`: it reduces the `S_k(Γ₁(N))^old` and
`S_k(Γ₁(N))^new` statements to the per-character-space form consumed by
`AtkinLehner.mainLemma_charSpace_primePower` (T118) and
`AtkinLehner.mainLemma_charSpace_of_primeFactors_decomposition` (T125). -/

section CharSpaceDecomposition

/-- **`diamondOpCuspHom`-invariance of `cuspFormsOld N k`.**  Rephrases
`diamondOp_preserves_cuspFormsOld` in the form expected by the generic
invariant-submodule API (`cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant`).
The underlying function `diamondOpCuspHom k d f` reduces definitionally to
`diamondOp_cusp k d f`. -/
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

/-- **Character decomposition of `cuspFormsOld N k`**: the oldform subspace
equals the supremum of its intersections with the Nebentypus character
subspaces.  Direct specialisation of
`cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant`. -/
theorem cuspFormsOld_iSup_inf_charSpace (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormsOld N k ⊓ cuspFormCharSpace k χ) =
      cuspFormsOld N k :=
  cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant k (cuspFormsOld N k)
    (fun d f hf => diamondOpCuspHom_preserves_cuspFormsOld d f hf)

/-- **Character decomposition of `cuspFormsNew N k`**.  Direct specialisation of
the generic invariant-submodule theorem. -/
theorem cuspFormsNew_iSup_inf_charSpace (k : ℤ) :
    (⨆ χ : (ZMod N)ˣ →* ℂˣ, cuspFormsNew N k ⊓ cuspFormCharSpace k χ) =
      cuspFormsNew N k :=
  cuspFormCharSpace_iSup_inf_of_diamondOpCuspHom_invariant k (cuspFormsNew N k)
    (fun d f hf => diamondOpCuspHom_preserves_cuspFormsNew d f hf)

/-- **Independence of the character-wise pieces of `cuspFormsOld N k`.** -/
theorem cuspFormsOld_iSupIndep_inf_charSpace (k : ℤ) :
    iSupIndep
      (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormsOld N k ⊓ cuspFormCharSpace k χ) :=
  cuspFormCharSpace_iSupIndep_inf k (cuspFormsOld N k)

/-- **Independence of the character-wise pieces of `cuspFormsNew N k`.** -/
theorem cuspFormsNew_iSupIndep_inf_charSpace (k : ℤ) :
    iSupIndep
      (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormsNew N k ⊓ cuspFormCharSpace k χ) :=
  cuspFormCharSpace_iSupIndep_inf k (cuspFormsNew N k)

/-- **Finsupp-indexed character decomposition of an oldform.**  Every
`f ∈ cuspFormsOld N k` is a finitely-supported sum of Nebentypus components,
each landing simultaneously in `cuspFormsOld N k` and in its character
subspace. -/
theorem exists_finsupp_charSpace_of_cuspFormsOld (k : ℤ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOld N k) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ cuspFormsOld N k ⊓ cuspFormCharSpace k χ) ∧
      (g.sum fun _ y => y) = f :=
  exists_finsupp_charSpace_of_diamondOpCuspHom_invariant k (cuspFormsOld N k)
    (fun d f hf => diamondOpCuspHom_preserves_cuspFormsOld d f hf) hf

/-- **Finsupp-indexed character decomposition of a newform subspace element.**
Every `f ∈ cuspFormsNew N k` is a finitely-supported sum of Nebentypus
components, each simultaneously in `cuspFormsNew N k` and in its character
subspace. -/
theorem exists_finsupp_charSpace_of_cuspFormsNew (k : ℤ)
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    ∃ g : ((ZMod N)ˣ →* ℂˣ) →₀ CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      (∀ χ : (ZMod N)ˣ →* ℂˣ, g χ ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ) ∧
      (g.sum fun _ y => y) = f :=
  exists_finsupp_charSpace_of_diamondOpCuspHom_invariant k (cuspFormsNew N k)
    (fun d f hf => diamondOpCuspHom_preserves_cuspFormsNew d f hf) hf

/-- **Range of the χ-component direct-sum map onto `cuspFormsOld N k`.**  The
natural linear map
`⨁ χ, (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) →ₗ[ℂ] CuspForm (Γ₁(N)) k`
has image equal to `cuspFormsOld N k`: every oldform is in the image of the
direct-sum assembly, and every image lies in `cuspFormsOld N k`.  Packages the
existing `cuspFormsOld_iSup_inf_charSpace` through `DirectSum.range_coeLinearMap`.
-/
theorem range_cuspFormsOld_charSpace_coeLinearMap
    [DecidableEq ((ZMod N)ˣ →* ℂˣ)] (k : ℤ) :
    LinearMap.range
      (DirectSum.coeLinearMap
        (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormsOld N k ⊓ cuspFormCharSpace k χ)) =
      cuspFormsOld N k :=
  DirectSum.range_coeLinearMap.trans (cuspFormsOld_iSup_inf_charSpace k)

/-- **Range of the χ-component direct-sum map onto `cuspFormsNew N k`.** -/
theorem range_cuspFormsNew_charSpace_coeLinearMap
    [DecidableEq ((ZMod N)ˣ →* ℂˣ)] (k : ℤ) :
    LinearMap.range
      (DirectSum.coeLinearMap
        (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormsNew N k ⊓ cuspFormCharSpace k χ)) =
      cuspFormsNew N k :=
  DirectSum.range_coeLinearMap.trans (cuspFormsNew_iSup_inf_charSpace k)

/-- **Injectivity of the χ-component direct-sum map at `cuspFormsOld N k`.**  The
natural linear map
`⨁ χ, (cuspFormsOld N k ⊓ cuspFormCharSpace k χ) →ₗ[ℂ] CuspForm (Γ₁(N)) k` is
injective; consequently each oldform has at most one Nebentypus decomposition. -/
theorem injective_cuspFormsOld_charSpace_coeLinearMap
    [DecidableEq ((ZMod N)ˣ →* ℂˣ)] (k : ℤ) :
    Function.Injective
      (DirectSum.coeLinearMap
        (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormsOld N k ⊓ cuspFormCharSpace k χ)) :=
  (cuspFormsOld_iSupIndep_inf_charSpace k).dfinsupp_lsum_injective

/-- **Injectivity of the χ-component direct-sum map at `cuspFormsNew N k`.** -/
theorem injective_cuspFormsNew_charSpace_coeLinearMap
    [DecidableEq ((ZMod N)ˣ →* ℂˣ)] (k : ℤ) :
    Function.Injective
      (DirectSum.coeLinearMap
        (fun χ : (ZMod N)ˣ →* ℂˣ => cuspFormsNew N k ⊓ cuspFormCharSpace k χ)) :=
  (cuspFormsNew_iSupIndep_inf_charSpace k).dfinsupp_lsum_injective

end CharSpaceDecomposition

/-! ### Newforms (DS Definition 5.8.1) -/

/-- A **newform** of level Γ₁(N) and weight k: a cusp form that is
1. an eigenform (common eigenfunction of all T_n with (n,N)=1)
2. in the new subspace
3. normalised: a_1(f) = 1

By Atkin-Lehner uniqueness (DS Theorem 5.8.2), newforms are uniquely determined
by their Hecke eigenvalues away from the level. -/
structure Newform (N : ℕ) [NeZero N] (k : ℤ)
    extends Eigenform N k where
  /-- The form is in the new subspace. -/
  isNew : toCuspForm ∈ cuspFormsNew N k
  /-- Normalisation at the **canonical Fourier period** (`h = 1`):
  the first Fourier coefficient is `1`, i.e. `a₁ = 1`.  This is the
  standard Diamond–Shurman / Miyake normalisation; the earlier
  period-`N` condition `(qExpansion N toCuspForm).coeff 1 = 1` is
  vacuous for `N > 1` because a period-1 form has zero period-`N`
  coefficient at every non-multiple of `N`. -/
  isNorm : (ModularFormClass.qExpansion (1 : ℝ) toCuspForm).coeff 1 = 1

/-- Predicate version: f is a newform if it's an eigenform in the new subspace
with `a_1 = 1` (at period 1). -/
structure IsNewform (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop where
  isEigen : IsEigenform f
  isNew : f ∈ cuspFormsNew N k
  isNorm : (ModularFormClass.qExpansion (1 : ℝ) f).coeff 1 = 1

/-- A `Newform` satisfies `IsNewform`. -/
theorem Newform.isNewform (f : Newform N k) : IsNewform f.toCuspForm where
  isEigen := f.toEigenform.isEigenform
  isNew := f.isNew
  isNorm := f.isNorm

/-! ### Primitive forms and conductor (Phase 6 / T007)

A **primitive form** at level `N` (Miyake §4.6.6, DS Definition 5.8.4) is a
newform that does not arise as a level-raise from any proper divisor of `N`.
By the existing `Newform`/`cuspFormsNew` framework, every `Newform N k`
satisfies `f.toCuspForm ∈ cuspFormsNew N k` (its `isNew` field), so
primitivity at the level is automatic.

The **conductor** of a `Newform N k` is the smallest level at which `f`
arises as a `Newform`; for a bundled `Newform N k` this is `N` itself by
the disjointness `cuspFormsOld_disjoint_cuspFormsNew` together with the
`1 < d` clause built into `IsOldformGenerator`. -/

/-- A `Newform` is **primitive** at its level if its underlying cusp form
lies in the new subspace. Every `Newform N k` is primitive at level `N`
by construction; this predicate is exposed for downstream API symmetry
(SMO, L-functions) so consumers can reach for `IsPrimitive` rather than
the structure projection `f.isNew`. -/
def Newform.IsPrimitive (f : Newform N k) : Prop :=
  f.toCuspForm ∈ cuspFormsNew N k

/-- Every `Newform` is primitive at its own level. -/
theorem Newform.isPrimitive (f : Newform N k) : f.IsPrimitive := f.isNew

/-- The **conductor** of a `Newform N k` is the smallest level at which `f`
arises as a `Newform`. For a bundled `Newform N k`, this is `N` itself,
because `cuspFormsOld_disjoint_cuspFormsNew` together with the `1 < d`
clause in `IsOldformGenerator` forbid a `Newform` from coinciding with
any level-raise from a strictly lower level. -/
noncomputable def Newform.conductor (_f : Newform N k) : ℕ := N

/-- The conductor of a bundled `Newform N k` equals `N`. -/
@[simp] theorem Newform.conductor_eq_level (f : Newform N k) : f.conductor = N := rfl

/-- The Mathlib conductor of a Dirichlet character `χ` carrying a
`Newform`'s Nebentypus divides the newform's conductor (which equals `N`).

Direct from `DirichletCharacter.conductor_dvd_level` and
`Newform.conductor_eq_level`; provided as a named handle so SMO and
L-function consumers can cite a single conductor-divisibility lemma
instead of inlining the Mathlib `conductor_dvd_level` plus the
`Newform.conductor` unfolding. -/
theorem dirichletCharacter_conductor_dvd_newform_conductor
    (f : Newform N k) (χ : DirichletCharacter ℂ N)
    (_hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ.toUnitHom) :
    χ.conductor ∣ f.conductor := by
  rw [Newform.conductor_eq_level]
  exact χ.conductor_dvd_level

/-! ### Eigenvalue = canonical Fourier coefficient for Newforms

For a normalised eigenform, the eigenvalue of `T_n` equals the `n`-th
**canonical Fourier coefficient** `a_n = (qExpansion (1 : ℝ) f).coeff n`.
This is the CuspForm-level version of the period-1 bridge
`HeckeRing.GL2.eigenvalue_eq_fourierCoeff_one` (FourierHecke.lean,
T082), consumed via the period-1 Fourier formula
`HeckeRing.GL2.fourierCoeff_heckeT_n_period_one`. -/

/-- For a `Newform` f lying in a character eigenspace `modFormCharSpace k χ`,
the eigenvalue at `n` (coprime to `N`) equals the `n`-th **canonical
Fourier coefficient** of `f` (period `h = 1`).

**Proof sketch**: `T_n f = λ_n f` implies `a_1(T_n f) = λ_n a_1(f) = λ_n`
(by normalisation `a_1 = 1` at period 1).  The period-1 Fourier formula
at `m = 1` (`fourierCoeff_heckeT_n_period_one`) gives `a_1(T_n f) =
a_n(f)` (the divisor sum collapses to a single `d = 1` term since
`gcd(1, n) = 1` and `χ(1) = 1`).

The character hypothesis `hf_char` is required because
`fourierCoeff_heckeT_n_period_one` is stated at the level of forms
living in a Nebentypus eigenspace.  A Newform is defined as an
eigenfunction of all `T_n` (coprime `n`) in the new subspace, but is
not automatically in a single character eigenspace; this must be
supplied by the caller (for classical newforms, this follows from
multiplicity one, but that is the very theorem being proved downstream). -/
theorem Newform.eigenvalue_eq_coeff (f : Newform N k) (n : ℕ+)
    (hn : Nat.Coprime n.val N) (χ : (ZMod N)ˣ →* ℂˣ)
    (hf_char : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ) :
    f.eigenvalue n =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  have h1_pos : (0 : ℝ) < 1 := one_pos
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  have h_eigen := f.isEigen n hn
  -- a_1(f) = 1 at the function level (CuspForm and ModularForm coerce identically)
  have h_norm :
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm.toModularForm').coeff 1 = 1 := by
    change (ModularFormClass.qExpansion (1 : ℝ)
        (⇑f.toCuspForm.toModularForm')).coeff 1 = 1
    rw [show (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl]
    exact f.isNorm
  -- coeff 1 of (c • f) = c, using normalisation a_1(f) = 1
  have h_smul_coeff : ∀ (c : ℂ),
      (ModularFormClass.qExpansion (1 : ℝ) (c • f.toCuspForm)).coeff 1 = c := by
    intro c
    show (ModularFormClass.qExpansion (1 : ℝ)
        (⇑(c • f.toCuspForm : CuspForm _ k))).coeff 1 = c
    rw [show (⇑(c • f.toCuspForm : CuspForm _ k) : UpperHalfPlane → ℂ) =
        c • ⇑f.toCuspForm from rfl,
      show (⇑f.toCuspForm : UpperHalfPlane → ℂ) =
        ⇑f.toCuspForm.toModularForm' from rfl,
      qExpansion_smul h1_pos h1_period, PowerSeries.coeff_smul, smul_eq_mul, h_norm,
      mul_one]
  -- T_n f = λ f, so coeff 1 of T_n f = λ
  have h_lhs :
      (ModularFormClass.qExpansion (1 : ℝ)
        (heckeT_n_cusp k n.val f.toCuspForm)).coeff 1 = f.eigenvalue n := by
    rw [h_eigen]; exact h_smul_coeff _
  -- coeff 1 of T_n f = coeff n of f via `fourierCoeff_heckeT_n_period_one` at m=1.
  -- Bridge: heckeT_n_cusp on CuspForm → heckeT_n on ModularForm via
  -- `heckeT_n_cusp_toModularForm'`, then apply the period-1 Fourier formula.
  have h_bridge :
      (ModularFormClass.qExpansion (1 : ℝ)
        (heckeT_n_cusp k n.val f.toCuspForm)).coeff 1 =
      (ModularFormClass.qExpansion (1 : ℝ) f.toCuspForm).coeff n.val := by
    -- Replace CuspForm coercions with ModularForm coercions and apply the
    -- ModularForm-level period-1 Fourier formula via heckeT_n_cusp_toModularForm'.
    change (ModularFormClass.qExpansion (1 : ℝ)
        (⇑(heckeT_n_cusp k n.val f.toCuspForm))).coeff 1 =
      (ModularFormClass.qExpansion (1 : ℝ) (⇑f.toCuspForm)).coeff n.val
    rw [show (⇑(heckeT_n_cusp k n.val f.toCuspForm) : UpperHalfPlane → ℂ) =
        ⇑(heckeT_n_cusp k n.val f.toCuspForm).toModularForm' from rfl,
      show (⇑f.toCuspForm : UpperHalfPlane → ℂ) =
        ⇑f.toCuspForm.toModularForm' from rfl,
      heckeT_n_cusp_toModularForm']
    -- Apply fourierCoeff_heckeT_n_period_one at m=1; collapse the divisor sum.
    have h := fourierCoeff_heckeT_n_period_one (N := N) k n.val hn χ hf_char 1
    simp only [Nat.gcd_one_left, Nat.divisors_one, Finset.sum_singleton] at h
    have h_unit_one : ZMod.unitOfCoprime 1 (Nat.coprime_one_left N) = 1 := by
      ext; simp [ZMod.coe_unitOfCoprime]
    simp only [Nat.Coprime, Nat.gcd_one_left, dite_true, Nat.cast_one, one_zpow,
      h_unit_one, map_one, Units.val_one, one_mul, Nat.div_one] at h
    exact h
  rw [← h_bridge, h_lhs]

/-! ### Reverse/consumer direction of the Main Lemma (T125)

The **easy direction** of `Newforms.mainLemma`: every oldform has
Fourier coefficients that vanish at indices coprime to `N`.  This is
dual to the `mainLemma` statement (which is the hard direction,
requiring the spectral theorem for Hecke operators).

The proof is a direct `Submodule.span_induction` on `cuspFormsOld N k`:

* **Generator step.** Each `IsOldformGenerator f` decomposes as
  `f = heq ▸ levelRaise M d k g` with `d * M = N` and `1 < d`.  The
  period-1 `q`-expansion of `levelRaise M d k g` is supported on
  multiples of `d` (via `qExpansion_one_modularFormLevelRaise_coeff`),
  and `Coprime n N` together with `d ∣ N` and `1 < d` force `¬ d ∣ n`.
* **Linearity.** `Submodule.span_induction` extends vanishing from
  generators to arbitrary elements via `qExpansion_add` / `_smul`. -/

omit [NeZero N] in
/-- The period-1 strict-period hypothesis for `Γ₁(N)`, packaged for
reuse in the oldform vanishing proof below. -/
private lemma h1_period_Gamma1_local :
    (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
  rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
    strictPeriods_Gamma1]
  exact ⟨1, by simp⟩

/-- The period-1 `q`-expansion of `levelRaise M d k g` vanishes at every
index `n` with `¬ d ∣ n`.  The proof transports the underlying function
to the `modularFormLevelRaise` version (which shares the same coercion
via `coe_modularFormLevelRaise`) and applies the Mathlib coefficient
formula `qExpansion_one_modularFormLevelRaise_coeff`. -/
private lemma qExpansion_one_levelRaise_coeff_eq_zero_of_not_dvd
    {M : ℕ} [NeZero M] {d : ℕ} [NeZero d]
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (n : ℕ) (hn : ¬ d ∣ n) :
    (ModularFormClass.qExpansion (1 : ℝ) (levelRaise M d k g)).coeff n = 0 := by
  let g_mf : ModularForm ((Gamma1 M).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := g.toSlashInvariantForm
      holo' := g.holo'
      bdd_at_cusps' := fun {c} hc γ hγ =>
        (g.zero_at_cusps' hc γ hγ).isBoundedAtImInfty }
  have h_fun_eq :
      (⇑(levelRaise M d k g) : UpperHalfPlane → ℂ) =
        ⇑(modularFormLevelRaise M d k g_mf) := by
    rw [coe_modularFormLevelRaise]; rfl
  rw [show ModularFormClass.qExpansion (1 : ℝ) (levelRaise M d k g) =
        ModularFormClass.qExpansion (1 : ℝ) (modularFormLevelRaise M d k g_mf) from
      qExpansion_ext2 _ _ h_fun_eq,
    qExpansion_one_modularFormLevelRaise_coeff, if_neg hn]

/-- **Oldforms have zero Fourier coefficients at indices coprime to the
level.**  This is the **reverse (easy) direction** of
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
    (p := fun (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) _ =>
      (ModularFormClass.qExpansion (1 : ℝ) x).coeff n = 0)
    ?_ ?_ ?_ ?_ hf
  · -- Generator case: f₀ = heq ▸ levelRaise M d k g with d * M = N and 1 < d.
    rintro f₀ ⟨M, d, _, _, hd_lt, heq, g, rfl⟩
    subst heq
    -- Goal: (qExpansion 1 (levelRaise M d k g)).coeff n = 0.
    have hd_dvd : d ∣ d * M := ⟨M, rfl⟩
    have h_coprime_d : Nat.Coprime n d := hn.coprime_dvd_right hd_dvd
    have h_not_dvd : ¬ d ∣ n := by
      intro h_dvd
      have h_gcd : n.gcd d = d := Nat.gcd_eq_right h_dvd
      rw [Nat.Coprime, h_gcd] at h_coprime_d
      omega
    exact qExpansion_one_levelRaise_coeff_eq_zero_of_not_dvd g n h_not_dvd
  · -- Zero case.
    show (ModularFormClass.qExpansion (1 : ℝ)
        ⇑(0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n = 0
    rw [show (⇑(0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : UpperHalfPlane → ℂ) =
        (0 : UpperHalfPlane → ℂ) from rfl, qExpansion_zero]
    simp
  · -- Addition case.
    intro x y _ _ ihx ihy
    have h_eq : ModularFormClass.qExpansion (1 : ℝ)
        (⇑(x + y) : UpperHalfPlane → ℂ) =
        ModularFormClass.qExpansion (1 : ℝ) ⇑x +
          ModularFormClass.qExpansion (1 : ℝ) ⇑y := by
      have := qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ)) (h := 1) (a := k) (b := k)
        one_pos h1_period_Gamma1_local x y
      convert this using 2
    show (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 ⇑(x + y)) = 0
    rw [h_eq, map_add, ihx, ihy, zero_add]
  · -- Scalar multiplication case.
    intro c x _ ihx
    have h_eq : ModularFormClass.qExpansion (1 : ℝ)
        (⇑(c • x) : UpperHalfPlane → ℂ) =
        c • ModularFormClass.qExpansion (1 : ℝ) ⇑x := by
      have := qExpansion_smul (Γ := (Gamma1 N).map (mapGL ℝ)) (k := k) (h := 1) one_pos
        h1_period_Gamma1_local c x
      convert this using 2
    show (PowerSeries.coeff n) (ModularFormClass.qExpansion 1 ⇑(c • x)) = 0
    rw [h_eq, show (PowerSeries.coeff n)
        (c • ModularFormClass.qExpansion (1 : ℝ) ⇑x) =
        c * (PowerSeries.coeff n) (ModularFormClass.qExpansion (1 : ℝ) ⇑x) from
      by simp [smul_eq_mul],
      ihx, mul_zero]

/-! ### T136 — Coefficient-vanishing transfer to the new part

Building on the T135 `oldPart` / `newPart` projection API plus
`cuspFormsOld_coeff_eq_zero_of_coprime`, we show that the mainLemma's
coprime-to-`N` Fourier vanishing hypothesis transfers from `f` to
`newPart f`.  This consumes the hitherto-unused `h_vanish` hypothesis of
`mainLemma_of_newPart_eq_zero` and yields the sharper reduction

```
Newforms.mainLemma
  ⇐  ∀ g ∈ cuspFormsNew N k,
       (∀ n coprime to N, coeff n g = 0) → g = 0
```

a zero-criterion on `cuspFormsNew N k` that the classical Atkin–Lehner
argument supplies through the Hecke-adjoint eigenbasis route. -/

/-- **Coprime coefficient vanishing for the oldform part.**  For any cusp
form `f` and any `n` coprime to `N`, the `n`th period-1 Fourier
coefficient of `oldPart f` is zero.  Direct consequence of
`oldPart_mem_cuspFormsOld` plus `cuspFormsOld_coeff_eq_zero_of_coprime`. -/
theorem oldPart_coeff_eq_zero_of_coprime
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (n : ℕ) (hn : Nat.Coprime n N) :
    (ModularFormClass.qExpansion (1 : ℝ) (oldPart f)).coeff n = 0 :=
  cuspFormsOld_coeff_eq_zero_of_coprime (oldPart f) (oldPart_mem_cuspFormsOld f) n hn

/-- **Coprime coefficient vanishing transfers from `f` to `newPart f`.**
If `f` has vanishing period-1 Fourier coefficients at all indices
coprime to `N`, then so does `newPart f`.

**Proof**: from `oldPart f + newPart f = f` (T135 reconstruction) plus
Mathlib's `qExpansion_add` linearity, extracting the `n`th coefficient
gives `coeff n f = coeff n (oldPart f) + coeff n (newPart f)`.  Under the
hypothesis, `coeff n f = 0`, and by
`oldPart_coeff_eq_zero_of_coprime`, `coeff n (oldPart f) = 0`; hence
`coeff n (newPart f) = 0`. -/
theorem newPart_coeff_eq_zero_of_coprime_of_vanish
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    (n : ℕ) (hn : Nat.Coprime n N) :
    (ModularFormClass.qExpansion (1 : ℝ) (newPart f)).coeff n = 0 := by
  -- Step 1: qExpansion is additive on `oldPart f + newPart f`.
  have h_eq : ModularFormClass.qExpansion (1 : ℝ)
        (⇑(oldPart f + newPart f) : UpperHalfPlane → ℂ) =
      ModularFormClass.qExpansion (1 : ℝ) ⇑(oldPart f) +
        ModularFormClass.qExpansion (1 : ℝ) ⇑(newPart f) := by
    have := qExpansion_add (Γ := (Gamma1 N).map (mapGL ℝ)) (h := 1) (a := k) (b := k)
      one_pos h1_period_Gamma1_local (oldPart f) (newPart f)
    convert this using 2
  -- Step 2: rewrite LHS using reconstruction `oldPart f + newPart f = f`.
  rw [oldPart_add_newPart f] at h_eq
  -- Step 3: extract the nth coefficient.
  have h_coeff : (ModularFormClass.qExpansion (1 : ℝ) f).coeff n =
      (ModularFormClass.qExpansion (1 : ℝ) (oldPart f)).coeff n +
      (ModularFormClass.qExpansion (1 : ℝ) (newPart f)).coeff n := by
    have h := congrArg (fun ps : PowerSeries ℂ => ps.coeff n) h_eq
    simpa using h
  -- Step 4: plug in the two zero-coefficient facts to isolate the new-part coefficient.
  rw [h_vanish n hn, oldPart_coeff_eq_zero_of_coprime f n hn, zero_add] at h_coeff
  exact h_coeff.symm

/-- **T136 sharper main-lemma consumer: `mainLemma` from a zero-criterion
on `cuspFormsNew N k`.**  If every cusp form in `cuspFormsNew N k` whose
period-1 Fourier coefficients vanish on all indices coprime to `N` is
zero, then `Newforms.mainLemma` follows immediately: any `f` with the
coprime-vanishing hypothesis is an oldform.

**Proof chain**:
1. `newPart f ∈ cuspFormsNew N k` (`newPart_mem_cuspFormsNew`).
2. `newPart f` inherits the coprime-vanishing hypothesis from `f`
   (`newPart_coeff_eq_zero_of_coprime_of_vanish`).
3. The zero-criterion hypothesis forces `newPart f = 0`.
4. `mainLemma_of_newPart_eq_zero` concludes `f ∈ cuspFormsOld N k`.

This is the genuine content of the classical Atkin–Lehner `mainLemma`
reduction: all that remains is the zero-criterion on `cuspFormsNew`,
owned by the Primary adjoint/eigenbasis lane (`AdjointTheory.lean`).  In
the classical proof, the zero-criterion is established by combining the
Hecke adjoint formula with the simultaneous eigenform basis of
`cuspFormsNew`: a newform's non-trivial Hecke eigenvalue at each prime
`p ∤ N` plus the coprime-vanishing hypothesis kills all pairings `⟨f, g⟩`
with `g` a newform, forcing the new component to vanish by non-degeneracy
of the Petersson inner product. -/
theorem mainLemma_of_newSubspace_coprime_vanishing_zero
    (h_new_zero : ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      g ∈ cuspFormsNew N k →
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) g).coeff n = 0) →
      g = 0)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k := by
  have h_newPart_zero : newPart f = 0 :=
    h_new_zero (newPart f) (newPart_mem_cuspFormsNew f)
      (newPart_coeff_eq_zero_of_coprime_of_vanish f h_vanish)
  exact mainLemma_of_newPart_eq_zero f h_vanish h_newPart_zero

/-! ### Main Lemma (DS Theorem 5.7.1, Atkin-Lehner) -/

/-- **The Main Lemma** (DS Theorem 5.7.1, Atkin-Lehner [AL70]):
If `f ∈ S_k(Γ₁(N))` has Fourier expansion `f(τ) = Σ aₙ qⁿ` with `aₙ = 0`
whenever `(n, N) = 1`, then `f` is an oldform.

This is the technical heart of the newform theory. The proof uses representation
theory (Carlton's elegant proof [Car99,Car01]).

The full proof requires the spectral theorem for Hecke operators
(`exists_simultaneous_eigenform_basis` from `AdjointTheory.lean`) together with
the Petersson inner product and adjoint formula. We decompose `f = f_old + f_new`
via `cuspFormsOld_isCompl_cuspFormsNew`. For each eigenform `gᵢ` in a basis of
`cuspFormsNew`, the adjoint relation forces `⟨f_new, gᵢ⟩ = 0`, which by
non-degeneracy gives `f_new = 0`.

**Dependencies**: `exists_simultaneous_eigenform_basis` (sorry'd in AdjointTheory.lean),
`heckeT_n_adjoint` (sorry'd in AdjointTheory.lean). -/
theorem mainLemma
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0) :
    f ∈ cuspFormsOld N k := by
  -- Decompose f = f_old + f_new via the direct sum.
  -- Show f_new = 0 by showing ⟨f_new, g⟩ = 0 for all g ∈ cuspFormsNew.
  -- For any eigenform g ∈ cuspFormsNew with eigenvalue λ_n ≠ 0:
  --   ⟨f, g⟩ = λ_n⁻¹ ⟨T_n f, g⟩   (by adjoint + eigen)
  --   and a_n(f) = 0 for coprime n, so the pairing vanishes.
  -- Since eigenforms span cuspFormsNew, f_new = 0 and f = f_old.
  sorry

/-! ### Atkin-Lehner uniqueness -/

/-- **Atkin-Lehner uniqueness** (DS Theorem 5.8.2 part 1): two newforms in
`S_k(Γ₁(N), χ)` with the same eigenvalues at all primes `(p, N) = 1` are equal.

This is the key uniqueness theorem for newforms — they are determined by
their L-functions (away from the level).

The character hypothesis `hχ` is required by `Newform.eigenvalue_eq_coeff`
to bridge `λ_n → a_n` via the ModularForm-level Fourier formula; both newforms
must lie in the same Nebentypus eigenspace `modFormCharSpace k χ`. -/
theorem newform_unique
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  -- Show f - g = 0 by proving it lies in both cuspFormsOld and cuspFormsNew,
  -- which are disjoint (cuspFormsOld_isCompl_cuspFormsNew).
  suffices hfg : f.toCuspForm - g.toCuspForm = 0 by
    exact sub_eq_zero.mp hfg
  -- Step 1: f - g ∈ cuspFormsNew (both f, g are newforms)
  have h_new : f.toCuspForm - g.toCuspForm ∈ cuspFormsNew N k :=
    (cuspFormsNew N k).sub_mem f.isNew g.isNew
  -- Step 2: f - g ∈ cuspFormsOld via mainLemma
  -- Need: a_n(f - g) = 0 for all n coprime to N (at the canonical period 1).
  have h_old : f.toCuspForm - g.toCuspForm ∈ cuspFormsOld N k := by
    apply mainLemma
    intro n hn
    -- a_n(f - g) = a_n(f) - a_n(g) at period 1.
    have h1_pos : (0 : ℝ) < 1 := one_pos
    have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    -- Decompose the q-expansion of the subtraction at period 1.
    simp only [CuspForm.coe_sub]
    conv_lhs =>
      rw [show (⇑f.toCuspForm - ⇑g.toCuspForm) =
          (⇑f.toCuspForm.toModularForm' - ⇑g.toCuspForm.toModularForm') from rfl]
    rw [qExpansion_sub h1_pos h1_period, map_sub, sub_eq_zero]
    -- Now need: a_n(f) = a_n(g) at period 1.
    -- For n = 0: coprime 0 N implies N = 1 (since gcd(0,N) = N)
    by_cases hn0 : n = 0
    · -- n = 0: Coprime 0 N means N = 1; cusp forms have a_0 = 0
      subst hn0
      simp [Nat.Coprime, Nat.gcd_zero_left] at hn
      subst hn
      have h_zero_f := (CuspFormClass.zero_at_infty f.toCuspForm).valueAtInfty_eq_zero
      have h_zero_g := (CuspFormClass.zero_at_infty g.toCuspForm).valueAtInfty_eq_zero
      rw [ModularFormClass.qExpansion_coeff_zero _ h1_pos h1_period,
          ModularFormClass.qExpansion_coeff_zero _ h1_pos h1_period,
          show (⇑f.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl,
          show (⇑g.toModularForm' : UpperHalfPlane → ℂ) = ⇑g.toCuspForm from rfl,
          h_zero_f, h_zero_g]
    · -- n > 0 coprime to N: use eigenvalue_eq_coeff (period 1)
      have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have h_eq := h ⟨n, hn_pos⟩ hn
      rw [Newform.eigenvalue_eq_coeff f ⟨n, hn_pos⟩ hn χ hfχ,
          Newform.eigenvalue_eq_coeff g ⟨n, hn_pos⟩ hn χ hgχ] at h_eq
      exact h_eq
  -- Step 3: By disjointness, f - g = 0
  exact Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _ h_old h_new

/-- **Conditional Atkin–Lehner uniqueness via the explicit `cuspFormsNew`
zero criterion.**

This is the `sorry`-free conditional twin of `newform_unique`: the call to
`mainLemma` (currently `sorry`-backed) is replaced by a call to the already
proven bridge `mainLemma_of_newSubspace_coprime_vanishing_zero`.  The
genuinely upstream spectral/adjoint zero criterion — "any `g ∈ cuspFormsNew N k`
whose period-1 Fourier coefficients vanish on indices coprime to `N` is
zero" — is taken as an explicit hypothesis `h_zero`, owned by the
Petersson/adjoint/eigenbasis lane (`AdjointTheory.lean`).

The proof mirrors `newform_unique` line-for-line; only the `mainLemma`
call is swapped for the bridge.  Suitable as a downstream `h_unique`
endpoint for T132's Strong Multiplicity One consumer. -/
theorem newform_unique_of_newSubspace_coprime_vanishing_zero
    (h_zero : ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k,
      g ∈ cuspFormsNew N k →
      (∀ n : ℕ, Nat.Coprime n N →
        (ModularFormClass.qExpansion (1 : ℝ) g).coeff n = 0) →
      g = 0)
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  suffices hfg : f.toCuspForm - g.toCuspForm = 0 by
    exact sub_eq_zero.mp hfg
  -- Step 1: f - g ∈ cuspFormsNew (both f, g are newforms)
  have h_new : f.toCuspForm - g.toCuspForm ∈ cuspFormsNew N k :=
    (cuspFormsNew N k).sub_mem f.isNew g.isNew
  -- Step 2: f - g ∈ cuspFormsOld via the bridge consumer
  have h_old : f.toCuspForm - g.toCuspForm ∈ cuspFormsOld N k := by
    apply mainLemma_of_newSubspace_coprime_vanishing_zero h_zero
    intro n hn
    have h1_pos : (0 : ℝ) < 1 := one_pos
    have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
      rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
        strictPeriods_Gamma1]
      exact ⟨1, by simp⟩
    simp only [CuspForm.coe_sub]
    conv_lhs =>
      rw [show (⇑f.toCuspForm - ⇑g.toCuspForm) =
          (⇑f.toCuspForm.toModularForm' - ⇑g.toCuspForm.toModularForm') from rfl]
    rw [qExpansion_sub h1_pos h1_period, map_sub, sub_eq_zero]
    by_cases hn0 : n = 0
    · subst hn0
      simp [Nat.Coprime, Nat.gcd_zero_left] at hn
      subst hn
      have h_zero_f := (CuspFormClass.zero_at_infty f.toCuspForm).valueAtInfty_eq_zero
      have h_zero_g := (CuspFormClass.zero_at_infty g.toCuspForm).valueAtInfty_eq_zero
      rw [ModularFormClass.qExpansion_coeff_zero _ h1_pos h1_period,
          ModularFormClass.qExpansion_coeff_zero _ h1_pos h1_period,
          show (⇑f.toModularForm' : UpperHalfPlane → ℂ) = ⇑f.toCuspForm from rfl,
          show (⇑g.toModularForm' : UpperHalfPlane → ℂ) = ⇑g.toCuspForm from rfl,
          h_zero_f, h_zero_g]
    · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
      have h_eq := h ⟨n, hn_pos⟩ hn
      rw [Newform.eigenvalue_eq_coeff f ⟨n, hn_pos⟩ hn χ hfχ,
          Newform.eigenvalue_eq_coeff g ⟨n, hn_pos⟩ hn χ hgχ] at h_eq
      exact h_eq
  -- Step 3: By disjointness, f - g = 0
  exact Submodule.disjoint_def.mp cuspFormsOld_disjoint_cuspFormsNew _ h_old h_new


end HeckeRing.GL2
