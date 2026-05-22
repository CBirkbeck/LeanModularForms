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

/-!
# Newforms: eigenforms, oldforms, the new subspace, and Hecke stability

Core definitions for the newform theory: the `Eigenform` structure and its eigenvalue API, the oldform/new-subspace submodules, `petN` left-linearity, the `CuspForm → ModularForm` embedding, the old/new projection API, and `heckeT_n` stability (DS Prop 5.6.2).

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### Eigenforms

An **eigenform** of level Γ₁(N) and weight k is a cusp form that is a common
eigenfunction of all Hecke operators `T_n` for `(n, N) = 1`.

We package this as a structure extending `CuspForm`, with the eigenvalues
recorded as data. -/

/-- An **eigenform** of level Γ₁(N) and weight k: a cusp form `f` carrying a Nebentypus
character `χ` (so `↑f ∈ modFormCharSpace k χ`) that is a simultaneous eigenvector of the
canonical `Γ₀(N)` Hecke **ring** action `heckeRingHomCharSpace`.

The eigen-condition is recorded directly in terms of the ring map (`isRingEigen`): for every
`n` coprime to `N`, the explicit ring element `heckeRingD_n n` acts on `↑f` by the scalar
`ringEigenvalue n`.  The classical eigenvalue `T_n f = (eigenvalue n) • f` is then a
*derived* fact (`Eigenform.eigenvalue`, `Eigenform.isEigen`), where the classical and ring
eigenvalues differ by the diamond normalisation `χ(n)`
(`heckeT_n_cusp_eq_heckeRingHom`).

DS Definition 5.5.4 / Miyake §4.5. -/
structure Eigenform (N : ℕ) [NeZero N] (k : ℤ)
    extends CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  /-- The Nebentypus character of the eigenform. -/
  χ : (ZMod N)ˣ →* ℂˣ
  /-- The coercion of the cusp form lies in the `χ`-eigenspace `modFormCharSpace k χ`. -/
  mem_charSpace : toCuspForm.toModularForm' ∈ modFormCharSpace k χ
  /-- The eigenvalues for the canonical `Γ₀(N)` Hecke **ring** action. -/
  ringEigenvalue : ℕ+ → ℂ
  /-- For `n` coprime to `N`, the explicit ring element `heckeRingD_n n` acts on the
  coercion `↑f ∈ modFormCharSpace k χ` by the scalar `ringEigenvalue n`. -/
  isRingEigen : ∀ n : ℕ+, Nat.Coprime n.val N →
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeRingHomCharSpace (k := k) (χ := χ) (heckeRingD_n n.val)
        ⟨toCuspForm.toModularForm', mem_charSpace⟩ =
      ringEigenvalue n • (⟨toCuspForm.toModularForm', mem_charSpace⟩ : modFormCharSpace k χ)

/-- The classical Hecke eigenvalue of an eigenform: the ring eigenvalue rescaled by the
diamond factor `χ(n)`, so that `T_n f = (eigenvalue n) • f` (`Eigenform.isEigen`).  For
`n` not coprime to `N` the value is `0` (the classical `T_n` is not packaged here). -/
noncomputable def Eigenform.eigenvalue (f : Eigenform N k) (n : ℕ+) : ℂ :=
  if h : Nat.Coprime n.val N then
    (↑(f.χ (ZMod.unitOfCoprime n.val h)) : ℂ) * f.ringEigenvalue n
  else 0

/-- For `n` coprime to `N`, the concrete cusp Hecke operator `T_n` acts on an eigenform by
its classical eigenvalue `eigenvalue n = χ(n) • ringEigenvalue n`.  This recovers the
classical eigenform equation from the ring eigen-condition `isRingEigen`, via the
ring-image identity `heckeT_n_cusp_eq_heckeRingHom`. -/
theorem Eigenform.isEigen (f : Eigenform N k) (n : ℕ+) (hn : Nat.Coprime n.val N) :
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp k n.val f.toCuspForm = f.eigenvalue n • f.toCuspForm := by
  haveI : NeZero n.val := ⟨n.pos.ne'⟩
  -- The coercion of `f` lies in the cusp-form character space (reverse bridge).
  have hf_mem : f.toCuspForm ∈ cuspFormCharSpace k f.χ :=
    cuspFormCharSpace_of_toModularForm'_mem f.mem_charSpace
  -- Prove the equation after coercing to modular forms (coercions agree pointwise).
  have key : (heckeT_n_cusp k n.val f.toCuspForm).toModularForm' =
      (f.eigenvalue n • f.toCuspForm).toModularForm' := by
    -- LHS: rewrite the cusp operator as the ring image (up to the diamond factor `χ(n)`),
    -- then replace the ring image by the eigen-scalar using `isRingEigen` (the membership
    -- witness is irrelevant: subtype membership is a `Prop`, so the witnesses are defeq).
    rw [heckeT_n_cusp_eq_heckeRingHom n.val hn hf_mem, f.isRingEigen n hn]
    -- Normalise the nested smuls on the modular-form side.
    simp only [SetLike.val_smul, smul_smul]
    -- RHS: unfold `eigenvalue` and push the scalar through `toModularForm'`.
    rw [Eigenform.eigenvalue, dif_pos hn]
    rfl
  -- Transfer the modular-form equality back to the cusp-form function level.
  apply DFunLike.ext
  intro τ
  have := DFunLike.congr_fun key τ
  simpa using this

/-- A predicate version: a cusp form is an eigenform if it has eigenvalues. -/
def IsEigenform (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ a : ℕ+ → ℂ, ∀ n : ℕ+, Nat.Coprime n.val N →
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp k n.val f = a n • f

/-- An eigenform is in particular an eigenform (predicate version). -/
theorem Eigenform.isEigenform (f : Eigenform N k) : IsEigenform f.toCuspForm :=
  ⟨f.eigenvalue, f.isEigen⟩

/-- The eigenform predicate matches `IsCommonEigenfunctionCusp` from AdjointTheory. -/
theorem isEigenform_iff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IsEigenform f ↔ IsCommonEigenfunctionCusp k f := by
  constructor
  · rintro ⟨a, ha⟩ n hn
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    exact ⟨a n, ha n hn⟩
  · intro h
    -- Use choice to extract the eigenvalue function
    refine ⟨fun n => if hn : Nat.Coprime n.val N then
      (haveI : NeZero n.val := ⟨n.pos.ne'⟩; h n hn).choose else 0, ?_⟩
    intro n hn
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    simp only [dif_pos hn]
    exact (h n hn).choose_spec

/-! ### Oldforms

An **oldform** at level N is a cusp form coming from a proper divisor M of N
via the level-raising map `ι_d : S_k(Γ₁(M)) → S_k(Γ₁(N))` with `d * M = N`.

The level-raising operator `levelRaise` and its matrix infrastructure live in
`LeanModularForms/HeckeRIngs/GL2/LevelRaise.lean`. -/

/-- A cusp form is an **oldform** generator at level N if it is the image of some
`levelRaise` from a **proper** divisor of N (`1 < d`).

The `1 < d` clause excludes the trivial level-raise `d = 1`, which is the
identity inclusion `S_k(Γ₁(N)) ↪ S_k(Γ₁(N))` and would make every cusp form
an "oldform generator" — collapsing `cuspFormsOld N k = ⊤` (T113 bug).

This is the underlying set of generators for `cuspFormsOld`. -/
def IsOldformGenerator (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ (M : ℕ) (d : ℕ) (_ : NeZero M) (_ : NeZero d) (_ : 1 < d) (heq : d * M = N)
      (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    heq ▸ levelRaise M d k g = f

/-- The **oldform subspace** `S_k(Γ₁(N))^old`: the submodule generated by all
`levelRaise` images from proper divisors of N.

DS (5.18): `S_k^old = ⊕_{M | N, M ≠ N} ι_{N/M}(S_k(Γ₁(M))^2)` (sum over divisors). -/
def cuspFormsOld (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ {f | IsOldformGenerator f}

/-- A cusp form is an **oldform** at level N if it is in the oldform submodule. -/
def IsOldform (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  f ∈ cuspFormsOld N k

/-! ### `petN` left-additivity and left-scalar (derived from existing helpers)

The Phase 4 worker has proved `petN_zero_right/left`, `petN_neg_right/left`,
`petN_add_right`. We derive `petN_add_left` and `petN_smul_left` via the
Hermitian symmetry `petN_conj_symm`. -/

/-- Additivity in the first argument, derived from `petN_add_right` + Hermitian symmetry. -/
theorem petN_add_left
    (f₁ f₂ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (f₁ + f₂) g = petN f₁ g + petN f₂ g := by
  have h := petN_add_right g f₁ f₂
  have e := congr_arg (starRingEnd ℂ) h
  rw [petN_conj_symm, map_add, petN_conj_symm, petN_conj_symm] at e
  exact e

/-- Conjugate-scalar multiplication in the first argument.

Uses `peterssonInner_conj_smul_left` together with `ModularForm.SL_smul_slash`
which says that slashing by `SL(2,ℤ)` commutes with scalar multiplication
(since the σ-conjugation factor is trivial when `det > 0`). -/
theorem petN_conj_smul_left
    (c : ℂ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (c • f) g = starRingEnd ℂ c * petN f g := by
  simp only [petN, Finset.mul_sum]
  congr 1; ext q
  have hcoe : ⇑(c • f) = c • ⇑f := rfl
  have h1 : ⇑(c • f) ∣[k] (q.out : SL(2, ℤ))⁻¹ = c • (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹) := by
    rw [hcoe]
    exact ModularForm.SL_smul_slash k _ ⇑f c
  rw [h1]
  exact UpperHalfPlane.peterssonInner_conj_smul_left k ModularGroup.fd c _ _

/-- Linear scalar multiplication in the second argument.

Derived from `petN_conj_smul_left` and Hermitian symmetry: applying `starRingEnd` to
both sides of `petN (c • g) f = starRingEnd c * petN g f` and using
`petN g (c • f) = conj(petN (c • f) g)` gives `petN g (c • f) = c * petN g f`. -/
theorem petN_smul_right
    (c : ℂ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN g (c • f) = c * petN g f := by
  have h1 : petN (c • f) g = starRingEnd ℂ c * petN f g := petN_conj_smul_left c f g
  have h2 := congr_arg (starRingEnd ℂ) h1
  rw [petN_conj_symm, map_mul, petN_conj_symm] at h2
  simp at h2
  exact h2

/-! ### Newform subspace (orthogonal complement) -/

/-- A cusp form is in the **new subspace** if it is orthogonal (w.r.t. `petN`)
to every oldform. -/
def IsInNewSubspace (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∀ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k, IsOldform g → petN f g = 0

/-- The **new subspace** `S_k(Γ₁(N))^new`: orthogonal complement of oldforms.

DS (5.19): `S_k^new = (S_k^old)⊥`. -/
def cuspFormsNew (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  carrier := {f | IsInNewSubspace f}
  add_mem' {f₁ f₂} h₁ h₂ g hg := by
    show petN (f₁ + f₂) g = 0
    rw [petN_add_left, h₁ g hg, h₂ g hg, add_zero]
  zero_mem' g _ := by
    show petN 0 g = 0
    exact petN_zero_left g
  smul_mem' c f hf g hg := by
    show petN (c • f) g = 0
    rw [petN_conj_smul_left, hf g hg, mul_zero]

/-! ### Direct sum decomposition (DS 5.20) -/

/-- The intersection of `cuspFormsOld` and `cuspFormsNew` is trivial.

If `f ∈ cuspFormsOld ∩ cuspFormsNew`, then `f ∈ cuspFormsNew` means `petN f g = 0`
for all `g ∈ cuspFormsOld`. Taking `g = f` (which is in `cuspFormsOld`), we get
`petN f f = 0`, hence `f = 0` by `petN_definite`. -/
theorem cuspFormsOld_disjoint_cuspFormsNew :
    Disjoint (cuspFormsOld N k) (cuspFormsNew N k) := by
  rw [Submodule.disjoint_def]
  intro f hf_old hf_new
  -- f ∈ cuspFormsNew means petN f g = 0 for all g ∈ cuspFormsOld
  -- Apply this with g = f (which is in cuspFormsOld)
  have h0 : petN f f = 0 := hf_new f hf_old
  -- Then petN_definite gives f = 0
  exact petN_definite f h0

/-! ### Linear embedding `CuspForm → ModularForm`

For finite-dimensionality of `CuspForm`, we use the natural embedding into `ModularForm`
(`CuspForm.toModularForm'` from `AdjointTheory.lean`) as a linear map. This together
with `dim_gen_cong_levels` (ported from the gauss PR — see `DimensionFormulas.lean`)
gives finite-dimensionality of `CuspForm`. -/

/-- The natural embedding `CuspForm → ModularForm` as a `ℂ`-linear map. -/
def cuspFormToModularFormLin :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f := f.toModularForm'
  map_add' f g := by ext z; rfl
  map_smul' c f := by ext z; rfl

omit [NeZero N] in
lemma cuspFormToModularFormLin_injective :
    Function.Injective (cuspFormToModularFormLin (N := N) (k := k)) := by
  intro f g hfg
  ext z
  exact congr_arg (fun h : ModularForm _ _ => h.toFun z) hfg

/-- Finite-dimensionality of `CuspForm Γ₁(N) k`. Derived from finite-dimensionality of
`ModularForm Γ₁(N) k` (`dim_gen_cong_levels` in `DimensionFormulas.lean`, ported from the
gauss PR) via the linear injection `cuspFormToModularFormLin`. -/
theorem cuspForm_finiteDimensional :
    FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  haveI : FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    have hidx : (Gamma1 N).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have := dim_gen_cong_levels k (Gamma1 N) hidx
    -- The coercion `(Gamma1 N : Subgroup (GL (Fin 2) ℝ))` equals `(Gamma1 N).map (mapGL ℝ)`.
    show FiniteDimensional ℂ (ModularForm ((Gamma1 N : Subgroup (GL (Fin 2) ℝ))) k)
    exact this
  exact FiniteDimensional.of_injective
    (cuspFormToModularFormLin (N := N) (k := k))
    cuspFormToModularFormLin_injective

/-- The real-valued bilinear form `B_ℝ(f, g) := Re(petN f g)` on cusp forms,
viewed as an ℝ-vector space. This is symmetric (Hermitian symmetry) and
non-degenerate (`petN_definite`), so we can apply Mathlib's
`BilinForm.isCompl_orthogonal_iff_disjoint` to conclude the codisjoint of
`cuspFormsOld` and `cuspFormsNew`. -/
noncomputable def petN_realBilin :
    LinearMap.BilinForm ℝ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun f :=
    { toFun := fun g => (petN f g).re
      map_add' := fun g₁ g₂ => by
        show (petN f (g₁ + g₂)).re = (petN f g₁).re + (petN f g₂).re
        rw [petN_add_right, Complex.add_re]
      map_smul' := fun (c : ℝ) g => by
        show (petN f (c • g)).re = c * (petN f g).re
        rw [show (c • g : CuspForm _ _) = (c : ℂ) • g from rfl, petN_smul_right,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] }
  map_add' f₁ f₂ := by
    ext g
    show (petN (f₁ + f₂) g).re = (petN f₁ g).re + (petN f₂ g).re
    rw [petN_add_left, Complex.add_re]
  map_smul' (c : ℝ) f := by
    ext g
    show (petN ((c : ℂ) • f) g).re = c * (petN f g).re
    rw [petN_conj_smul_left, Complex.mul_re, Complex.conj_re, Complex.ofReal_re,
      Complex.conj_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]

lemma petN_realBilin_apply (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN_realBilin f g = (petN f g).re := rfl

lemma petN_realBilin_isRefl : (petN_realBilin (N := N) (k := k)).IsRefl := by
  intro f g hfg
  rw [petN_realBilin_apply] at hfg ⊢
  -- petN g f = conj(petN f g), so (petN g f).re = (petN f g).re
  have h := petN_conj_symm f g
  have : (petN g f).re = (petN f g).re := by
    rw [← h, Complex.conj_re]
  linarith

/-- The orthogonal complement of `(cuspFormsOld).restrictScalars ℝ` w.r.t. `petN_realBilin`
equals `(cuspFormsNew).restrictScalars ℝ` as ℝ-submodules. The proof uses Hermitian
symmetry and `cuspFormsOld` being closed under multiplication by `i`. -/
lemma petN_realBilin_orthogonal_cuspFormsOld_eq :
    (petN_realBilin (N := N) (k := k)).orthogonal
        ((cuspFormsOld N k).restrictScalars ℝ) =
      (cuspFormsNew N k).restrictScalars ℝ := by
  ext f
  refine ⟨?_, ?_⟩
  · intro hf
    -- hf : ∀ g ∈ cuspFormsOld (as ℝ-submodule), petN_realBilin g f = 0
    -- (Note: Mathlib's BilinForm orthogonal uses `B g f = 0`, with f in second arg)
    -- We want: f ∈ cuspFormsNew, i.e., for all g ∈ cuspFormsOld, petN f g = 0
    show f ∈ cuspFormsNew N k
    intro g hg
    -- petN_realBilin g f = (petN g f).re = 0 by hf
    have hg_mem : g ∈ Submodule.restrictScalars ℝ (cuspFormsOld N k) := hg
    have hgf_re : (petN g f).re = 0 := by
      have := hf g hg_mem
      simp only [LinearMap.BilinForm.IsOrtho] at this
      rw [petN_realBilin_apply] at this
      exact this
    -- Apply also for (i • g) which is in cuspFormsOld
    have hig : (Complex.I • g) ∈ Submodule.restrictScalars ℝ (cuspFormsOld N k) :=
      (cuspFormsOld N k).smul_mem Complex.I hg
    have higf_re : (petN (Complex.I • g) f).re = 0 := by
      have := hf (Complex.I • g) hig
      simp only [LinearMap.BilinForm.IsOrtho] at this
      rw [petN_realBilin_apply] at this
      exact this
    -- petN (i • g) f = (conj i) * petN g f = -i * petN g f (conj-linear in first arg)
    have h_eq : petN (Complex.I • g) f = starRingEnd ℂ Complex.I * petN g f :=
      petN_conj_smul_left _ _ _
    rw [h_eq] at higf_re
    -- Re(-i * z) = Im(z), so Im(petN g f) = 0
    have h_im : (petN g f).im = 0 := by
      have := higf_re
      simp [Complex.mul_re, Complex.I_re, Complex.I_im] at this
      linarith
    -- Combined: petN g f = 0
    have hgf : petN g f = 0 := by
      apply Complex.ext
      · simpa using hgf_re
      · simpa using h_im
    -- By Hermitian symmetry: petN f g = conj(petN g f) = 0
    have : starRingEnd ℂ (petN g f) = petN f g := petN_conj_symm f g
    rw [hgf] at this
    simp at this
    exact this.symm
  · intro hf g hg
    -- Need: petN_realBilin g f = 0, i.e., (petN g f).re = 0
    show (petN_realBilin g) f = 0
    rw [petN_realBilin_apply]
    -- f ∈ cuspFormsNew means petN f g = 0 for all g ∈ cuspFormsOld
    have hg_mem : g ∈ cuspFormsOld N k := hg
    have hpetN : petN f g = 0 := hf g hg_mem
    -- petN g f = conj(petN f g) by Hermitian symmetry
    have : starRingEnd ℂ (petN g f) = petN f g := petN_conj_symm f g
    rw [hpetN] at this
    have hgf : petN g f = 0 := by
      have h2 := congr_arg (starRingEnd ℂ) this
      simp at h2
      exact h2
    rw [hgf, Complex.zero_re]

/-- DS (5.20): `S_k(Γ₁(N)) = S_k^old ⊕ S_k^new` as inner product spaces.

The `Disjoint` part follows from `petN_definite` (cuspFormsOld_disjoint_cuspFormsNew).
The `Codisjoint` part uses:
1. `cuspForm_finiteDimensional` (ported from gauss PR via `dim_gen_cong_levels`).
2. The real-valued bilinear form `petN_realBilin` (Re of petN), which is reflexive
   by Hermitian symmetry (`petN_realBilin_isRefl`).
3. Mathlib's `BilinForm.isCompl_orthogonal_iff_disjoint` over ℝ.
4. The identification `cuspFormsNew = (cuspFormsOld)^⊥` w.r.t. `petN_realBilin`
   (`petN_realBilin_orthogonal_cuspFormsOld_eq`). -/
theorem cuspFormsOld_isCompl_cuspFormsNew :
    IsCompl (cuspFormsOld N k) (cuspFormsNew N k) := by
  refine ⟨cuspFormsOld_disjoint_cuspFormsNew, ?_⟩
  haveI : FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    cuspForm_finiteDimensional
  haveI : FiniteDimensional ℝ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    Module.Finite.trans ℂ _
  -- Apply BilinForm.isCompl_orthogonal_iff_disjoint over ℝ to get IsCompl over ℝ.
  -- The disjoint condition over ℝ follows from disjoint over ℂ (carriers are the same).
  have hdisj_R : Disjoint
      ((cuspFormsOld N k).restrictScalars ℝ)
      ((petN_realBilin (N := N) (k := k)).orthogonal
        ((cuspFormsOld N k).restrictScalars ℝ)) := by
    rw [petN_realBilin_orthogonal_cuspFormsOld_eq]
    -- Now both submodules have the same carriers as their ℂ versions, so disjoint transfers
    have hdisj_C := cuspFormsOld_disjoint_cuspFormsNew (N := N) (k := k)
    rw [Submodule.disjoint_def] at hdisj_C ⊢
    intro f hf₁ hf₂
    exact hdisj_C f hf₁ hf₂
  have h_iscompl_R := (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    petN_realBilin_isRefl (W := (cuspFormsOld N k).restrictScalars ℝ)).mpr hdisj_R
  rw [petN_realBilin_orthogonal_cuspFormsOld_eq] at h_iscompl_R
  -- Translate IsCompl over ℝ to Codisjoint over ℂ.
  -- Both Submodules have the same carrier as their ℝ versions, so codisjoint transfers.
  rw [codisjoint_iff]
  have : ((cuspFormsOld N k).restrictScalars ℝ) ⊔
      ((cuspFormsNew N k).restrictScalars ℝ) = ⊤ :=
    h_iscompl_R.sup_eq_top
  -- Convert ⊔ from ℝ-Submodule to ℂ-Submodule level via the carrier set.
  apply Submodule.eq_top_iff'.mpr
  intro f
  have hf : f ∈ ((cuspFormsOld N k).restrictScalars ℝ) ⊔
      ((cuspFormsNew N k).restrictScalars ℝ) := by
    rw [this]; exact Submodule.mem_top
  -- Decompose using the join in ℝ-Submodule
  rw [Submodule.mem_sup] at hf
  obtain ⟨x, hx, y, hy, hxy⟩ := hf
  -- x ∈ cuspFormsOld (as ℂ-Submodule, since restrictScalars preserves carrier)
  -- y ∈ cuspFormsNew (similarly)
  rw [Submodule.mem_sup]
  exact ⟨x, hx, y, hy, hxy⟩

/-! ### T135 — Old/new projection decomposition API

Building on `cuspFormsOld_isCompl_cuspFormsNew`, every cusp form at level
`Γ₁(N)` decomposes uniquely as the sum of its **oldform part** and
**newform part**.  We package this decomposition as two `ℂ`-linear
projection maps

* `cuspFormsOldProjection N k`: onto `cuspFormsOld N k` along `cuspFormsNew N k`.
* `cuspFormsNewProjection N k`: onto `cuspFormsNew N k` along `cuspFormsOld N k`.

and the convenient applied forms `oldPart`, `newPart`, with the full
reconstruction, membership, and uniqueness API derived from Mathlib's
`IsCompl.projection` infrastructure.

This is the exact linear-algebra layer called out in the
`Newforms.mainLemma` docstring: the classical Atkin–Lehner–Li /
Diamond–Shurman §5.7 proof reduces `mainLemma` to showing that, under
the coprime-to-`N` Fourier vanishing hypothesis, the newform part of
`f` is zero — a Hecke-adjoint / eigenbasis / analytic-nonvanishing
argument that is owned by the Primary lane (`AdjointTheory.lean`).
The present API provides the reusable consumer
`mainLemma_of_newPart_eq_zero` that closes `Newforms.mainLemma` the
moment the Primary lane can produce `newPart f = 0`. -/

/-- **Oldform linear projection.**  The `ℂ`-linear endomorphism of
`CuspForm Γ₁(N) k` that projects onto `cuspFormsOld N k` along
`cuspFormsNew N k`.  Defined as the composition of Mathlib's
`Submodule.linearProjOfIsCompl` (which lands in the subtype
`cuspFormsOld N k`) with the subtype inclusion back into
`CuspForm Γ₁(N) k`. -/
noncomputable def cuspFormsOldProjection (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (cuspFormsOld N k).subtype ∘ₗ
    Submodule.linearProjOfIsCompl (cuspFormsOld N k) (cuspFormsNew N k)
      cuspFormsOld_isCompl_cuspFormsNew

/-- **Newform linear projection.**  The `ℂ`-linear endomorphism of
`CuspForm Γ₁(N) k` that projects onto `cuspFormsNew N k` along
`cuspFormsOld N k`. -/
noncomputable def cuspFormsNewProjection (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  (cuspFormsNew N k).subtype ∘ₗ
    Submodule.linearProjOfIsCompl (cuspFormsNew N k) (cuspFormsOld N k)
      cuspFormsOld_isCompl_cuspFormsNew.symm

/-- **Oldform part.**  The image of `f` under the oldform projection.
Equivalent to `cuspFormsOldProjection N k f`. -/
noncomputable def oldPart (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  cuspFormsOldProjection N k f

/-- **Newform part.** -/
noncomputable def newPart (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  cuspFormsNewProjection N k f

/-- The oldform part of `f` lies in `cuspFormsOld N k`. -/
theorem oldPart_mem_cuspFormsOld (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    oldPart f ∈ cuspFormsOld N k :=
  SetLike.coe_mem _

/-- The newform part of `f` lies in `cuspFormsNew N k`. -/
theorem newPart_mem_cuspFormsNew (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    newPart f ∈ cuspFormsNew N k :=
  SetLike.coe_mem _

/-- **Reconstruction: `f = oldPart f + newPart f`.**  Derived from
`Submodule.prodEquivOfIsCompl.apply_symm_apply` composed with
`Submodule.prodEquivOfIsCompl_symm_apply` and
`Submodule.coe_prodEquivOfIsCompl'`. -/
theorem oldPart_add_newPart (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    oldPart f + newPart f = f := by
  have h := (Submodule.prodEquivOfIsCompl (cuspFormsOld N k) (cuspFormsNew N k)
    cuspFormsOld_isCompl_cuspFormsNew).apply_symm_apply f
  rw [Submodule.prodEquivOfIsCompl_symm_apply,
    Submodule.coe_prodEquivOfIsCompl'] at h
  exact h

/-- Alternative reconstruction form: `newPart f = f - oldPart f`. -/
theorem newPart_eq_sub_oldPart (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    newPart f = f - oldPart f := by
  rw [eq_sub_iff_add_eq, add_comm, oldPart_add_newPart]

/-- If `f ∈ cuspFormsOld N k`, then `oldPart f = f`. -/
@[simp] theorem oldPart_of_mem_cuspFormsOld
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOld N k) :
    oldPart f = f := by
  show ((cuspFormsOld N k).subtype
    (Submodule.linearProjOfIsCompl _ _ cuspFormsOld_isCompl_cuspFormsNew f) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f
  have := Submodule.linearProjOfIsCompl_apply_left
    cuspFormsOld_isCompl_cuspFormsNew ⟨f, hf⟩
  simp [this]

/-- If `f ∈ cuspFormsNew N k`, then `oldPart f = 0`. -/
@[simp] theorem oldPart_of_mem_cuspFormsNew
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    oldPart f = 0 := by
  show ((cuspFormsOld N k).subtype
    (Submodule.linearProjOfIsCompl _ _ cuspFormsOld_isCompl_cuspFormsNew f) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0
  have hproj : Submodule.linearProjOfIsCompl (cuspFormsOld N k) (cuspFormsNew N k)
      cuspFormsOld_isCompl_cuspFormsNew f = 0 :=
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff
      cuspFormsOld_isCompl_cuspFormsNew).mpr hf
  rw [hproj]
  simp

/-- If `f ∈ cuspFormsNew N k`, then `newPart f = f`. -/
@[simp] theorem newPart_of_mem_cuspFormsNew
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsNew N k) :
    newPart f = f := by
  show ((cuspFormsNew N k).subtype
    (Submodule.linearProjOfIsCompl _ _
      cuspFormsOld_isCompl_cuspFormsNew.symm f) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f
  have := Submodule.linearProjOfIsCompl_apply_left
    cuspFormsOld_isCompl_cuspFormsNew.symm ⟨f, hf⟩
  simp [this]

/-- If `f ∈ cuspFormsOld N k`, then `newPart f = 0`. -/
@[simp] theorem newPart_of_mem_cuspFormsOld
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormsOld N k) :
    newPart f = 0 := by
  show ((cuspFormsNew N k).subtype
    (Submodule.linearProjOfIsCompl _ _
      cuspFormsOld_isCompl_cuspFormsNew.symm f) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0
  have hproj : Submodule.linearProjOfIsCompl (cuspFormsNew N k) (cuspFormsOld N k)
      cuspFormsOld_isCompl_cuspFormsNew.symm f = 0 :=
    (Submodule.linearProjOfIsCompl_apply_eq_zero_iff
      cuspFormsOld_isCompl_cuspFormsNew.symm).mpr hf
  rw [hproj]
  simp

/-- **Characterisation of `cuspFormsOld` by vanishing newform part.**
`f ∈ cuspFormsOld N k ↔ newPart f = 0`.  This is the bridging equivalence
used by the classical `mainLemma` argument: the mainLemma hypothesis
(coprime-to-`N` Fourier vanishing) is intended to imply `newPart f = 0`
via a Hecke-adjoint / eigenbasis analytic-nonvanishing argument, and
this iff then concludes `f ∈ cuspFormsOld N k`. -/
theorem mem_cuspFormsOld_iff_newPart_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormsOld N k ↔ newPart f = 0 :=
  ⟨newPart_of_mem_cuspFormsOld,
    fun h => by rw [← oldPart_add_newPart f, h, add_zero]; exact oldPart_mem_cuspFormsOld f⟩

/-- **Characterisation of `cuspFormsNew` by vanishing oldform part.** -/
theorem mem_cuspFormsNew_iff_oldPart_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormsNew N k ↔ oldPart f = 0 :=
  ⟨oldPart_of_mem_cuspFormsNew,
    fun h => by
      rw [show f = oldPart f + newPart f from (oldPart_add_newPart f).symm, h, zero_add]
      exact newPart_mem_cuspFormsNew f⟩

/-- **Uniqueness of the old/new decomposition.**  If `f = fo + fn` with
`fo ∈ cuspFormsOld N k` and `fn ∈ cuspFormsNew N k`, then `fo = oldPart f`
and `fn = newPart f`. -/
theorem oldPart_newPart_unique
    {f fo fn : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hfo : fo ∈ cuspFormsOld N k) (hfn : fn ∈ cuspFormsNew N k)
    (heq : f = fo + fn) :
    oldPart f = fo ∧ newPart f = fn := by
  refine ⟨?_, ?_⟩
  · rw [heq]
    have h_lin : oldPart (fo + fn) = oldPart fo + oldPart fn := map_add _ _ _
    rw [h_lin, oldPart_of_mem_cuspFormsOld hfo, oldPart_of_mem_cuspFormsNew hfn, add_zero]
  · rw [heq]
    have h_lin : newPart (fo + fn) = newPart fo + newPart fn := map_add _ _ _
    rw [h_lin, newPart_of_mem_cuspFormsOld hfo, newPart_of_mem_cuspFormsNew hfn, zero_add]

/-- **T135 conditional `mainLemma` consumer: newform-part vanishing ⇒
`cuspFormsOld` membership.**  Under the coprime-to-`N` Fourier vanishing
hypothesis (standing assumption of `Newforms.mainLemma`), if additionally
`newPart f = 0`, then `f ∈ cuspFormsOld N k`.

This is the **exact local bridge** the `Newforms.mainLemma` proof wants:
once the Primary lane (`AdjointTheory.lean`) lands the Hecke-adjoint
eigenbasis argument that derives `newPart f = 0` from coprime-vanishing,
`mainLemma` closes by this consumer.

The `h_vanish` hypothesis is present for interface completeness (it
mirrors the `Newforms.mainLemma` signature) and is not used in the
present proof; it is consumed by the future `newPart_eq_zero_of_...`
theorem from `AdjointTheory.lean` that produces the `h_newPart_zero`
hypothesis of this consumer. -/
theorem mainLemma_of_newPart_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (_h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    (h_newPart_zero : newPart f = 0) :
    f ∈ cuspFormsOld N k :=
  (mem_cuspFormsOld_iff_newPart_eq_zero f).mpr h_newPart_zero

/-! ### Hecke stability (DS Proposition 5.6.2)

The oldform subspace is stable under all Hecke operators `T_n` (and diamond
operators `⟨d⟩`) for `(n, N) = 1`. The proof has two ingredients:

1. **Linearity of `heckeT_n_cusp` and `diamondOp_cusp`** (proved here as
   `heckeT_n_cusp_add`, `heckeT_n_cusp_smul`, `diamondOp_cusp_add`,
   `diamondOp_cusp_smul`).
2. **The commutation `T_n ∘ levelRaise = levelRaise ∘ T_n`** for `(n, N) = 1`
   (DS Theorem 5.6.2). This is the *generator step* for `Submodule.span_induction`
   and is encapsulated in `heckeT_n_levelRaise_mem` / `diamondOp_levelRaise_mem`.

Once those generator-step lemmas are filled, the high-level stability theorems
follow from `Submodule.span_induction`. -/

/-- `T_n` commutes with addition on cusp forms. -/
lemma heckeT_n_cusp_add (n : ℕ) [NeZero n] (f₁ f₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (f₁ + f₂) = heckeT_n_cusp k n f₁ + heckeT_n_cusp k n f₂ := by
  ext z
  show (heckeT_n k n (f₁ + f₂).toModularForm').toFun z =
    (heckeT_n k n f₁.toModularForm').toFun z + (heckeT_n k n f₂.toModularForm').toFun z
  rw [show (f₁ + f₂).toModularForm' = f₁.toModularForm' + f₂.toModularForm' from rfl, map_add]
  rfl

/-- `T_n` commutes with scalar multiplication on cusp forms. -/
lemma heckeT_n_cusp_smul (n : ℕ) [NeZero n] (c : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (c • f) = c • heckeT_n_cusp k n f := by
  ext z
  show (heckeT_n k n (c • f).toModularForm').toFun z = c • (heckeT_n k n f.toModularForm').toFun z
  rw [show (c • f).toModularForm' = c • f.toModularForm' from rfl, map_smul]
  rfl

/-- `T_n` of zero is zero. -/
lemma heckeT_n_cusp_zero (n : ℕ) [NeZero n] :
    heckeT_n_cusp k n (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 := by
  ext z
  show (heckeT_n k n (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).toModularForm').toFun z = 0
  rw [show ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).toModularForm') =
      (0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) from rfl, map_zero]
  rfl

/-- `⟨d⟩` commutes with addition (`diamondOp_cusp = diamondOpCusp` is already linear). -/
lemma diamondOp_cusp_add (d : (ZMod N)ˣ) (f₁ f₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d (f₁ + f₂) = diamondOp_cusp k d f₁ + diamondOp_cusp k d f₂ :=
  (diamondOpCusp k d).map_add f₁ f₂

/-- `⟨d⟩` commutes with scalar multiplication. -/
lemma diamondOp_cusp_smul (d : (ZMod N)ˣ) (c : ℂ) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    diamondOp_cusp k d (c • f) = c • diamondOp_cusp k d f :=
  (diamondOpCusp k d).map_smul c f

/-- `⟨d⟩` of zero is zero. -/
lemma diamondOp_cusp_zero (d : (ZMod N)ˣ) :
    diamondOp_cusp k d (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = 0 :=
  (diamondOpCusp k d).map_zero


end HeckeRing.GL2
