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

Core definitions for the newform theory: the `Eigenform` structure and its eigenvalue API, the
oldform/new-subspace submodules, `petN` left-linearity, the `CuspForm → ModularForm` embedding,
the old/new projection API, and `heckeT_n` stability (DS Prop 5.6.2).
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- An **eigenform** of level Γ₁(N) and weight k: a cusp form `f` carrying a Nebentypus
character `χ` (so `↑f ∈ modFormCharSpace k χ`) that is a simultaneous eigenvector of the
canonical `Γ₀(N)` Hecke **ring** action `heckeRingHomCharSpace`.  The classical eigenvalue
`T_n f = (eigenvalue n) • f` is a *derived* fact (`Eigenform.eigenvalue`, `Eigenform.isEigen`),
differing from the ring eigenvalue by the diamond normalisation `χ(n)`.
DS Definition 5.5.4 / Miyake §4.5. -/
@[ext]
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
  have hf_mem : f.toCuspForm ∈ cuspFormCharSpace k f.χ :=
    cuspFormCharSpace_of_toModularForm'_mem f.mem_charSpace
  have key : (heckeT_n_cusp k n.val f.toCuspForm).toModularForm' =
      (f.eigenvalue n • f.toCuspForm).toModularForm' := by
    rw [heckeT_n_cusp_eq_heckeRingHom n.val hn hf_mem, f.isRingEigen n hn]
    simp only [SetLike.val_smul, smul_smul]
    rw [Eigenform.eigenvalue, dif_pos hn]
    rfl
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

/-- **DS Definition 5.8.1 (formal eigenform notion)**: `f` is a `T_n`-eigenform for **all**
`n ∈ ℕ⁺` (not just `(n,N) = 1`).  This is strictly stronger than `IsEigenform`, which only
requires eigen-behaviour at the good primes — the working notion used by both Miyake §4.5 /
Theorem 4.5.4(3) and DS §5.5–§5.7 / Corollary 5.6.3 throughout the development.

The diamond-operator condition of DS Def 5.8.1 is automatic at bad primes (`⟨n⟩ = 0` for
`(n,N) > 1`, so any modular form is trivially an `⟨n⟩`-eigenform with eigenvalue 0 there);
so the only non-trivial content beyond `IsEigenform` is bad-prime `T_n`-eigen-behaviour.

For `Newform`s, the upgrade `IsEigenform → IsFullEigenform` is the **Atkin–Lehner–Li**
bad-prime extension theorem (DS Theorem 5.8.6 / Atkin–Lehner 1970): on a newform of
conductor `N`, the bad-prime eigenvalues are explicit Atkin–Lehner signs (`±p^{(k−2)/2}`
when `p ∥ N`, `0` when `p² ∣ N`).  That upgrade is a separate development not currently
formalised here; this predicate gives downstream API a clean way to *assume* it. -/
def IsFullEigenform (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∃ a : ℕ+ → ℂ, ∀ n : ℕ+,
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    heckeT_n_cusp k n.val f = a n • f

/-- The DS Def 5.8.1 eigenform notion implies the project's working `IsEigenform`. -/
theorem IsFullEigenform.isEigenform
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (h : IsFullEigenform f) :
    IsEigenform f := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, fun n _ ↦ ha n⟩

/-- The eigenform predicate matches `IsCommonEigenfunctionCusp` from AdjointTheory. -/
theorem isEigenform_iff (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IsEigenform f ↔ IsCommonEigenfunctionCusp k f := by
  constructor
  · rintro ⟨a, ha⟩ n hn
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    exact ⟨a n, ha n hn⟩
  · intro h
    refine ⟨fun n ↦ if hn : Nat.Coprime n.val N then
      (haveI : NeZero n.val := ⟨n.pos.ne'⟩; h n hn).choose else 0, ?_⟩
    intro n hn
    haveI : NeZero n.val := ⟨n.pos.ne'⟩
    simp only [dif_pos hn]
    exact (h n hn).choose_spec

/-- A cusp form is an **oldform** generator at level N if it is the image of some
`levelRaise` from a **proper** divisor of N (`1 < d`).  The `1 < d` clause excludes the
trivial level-raise `d = 1` (the identity inclusion), which would otherwise collapse
`cuspFormsOld N k = ⊤`.  This is the underlying set of generators for `cuspFormsOld`. -/
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

/-- Additivity in the first argument, derived from `petN_add_right` + Hermitian symmetry. -/
theorem petN_add_left
    (f₁ f₂ g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (f₁ + f₂) g = petN f₁ g + petN f₂ g := by
  have h := petN_add_right g f₁ f₂
  have e := congr_arg (starRingEnd ℂ) h
  rw [petN_conj_symm, map_add, petN_conj_symm, petN_conj_symm] at e
  exact e

/-- Conjugate-scalar multiplication in the first argument: `petN (c • f) g = conj c * petN f g`. -/
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

/-- Linear scalar multiplication in the second argument: `petN g (c • f) = c * petN g f`.
Derived from `petN_conj_smul_left` and Hermitian symmetry. -/
theorem petN_smul_right
    (c : ℂ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN g (c • f) = c * petN g f := by
  have h1 : petN (c • f) g = starRingEnd ℂ c * petN f g := petN_conj_smul_left c f g
  have h2 := congr_arg (starRingEnd ℂ) h1
  rw [petN_conj_symm, map_mul, petN_conj_symm] at h2
  simp at h2
  exact h2

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

/-- The intersection of `cuspFormsOld` and `cuspFormsNew` is trivial: applying orthogonality
of `f ∈ cuspFormsNew` to `g = f ∈ cuspFormsOld` gives `petN f f = 0`, so `f = 0` by
`petN_definite`. -/
theorem cuspFormsOld_disjoint_cuspFormsNew :
    Disjoint (cuspFormsOld N k) (cuspFormsNew N k) := by
  rw [Submodule.disjoint_def]
  intro f hf_old hf_new
  have h0 : petN f f = 0 := hf_new f hf_old
  exact petN_definite f h0

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
  exact congr_arg (fun h : ModularForm _ _ ↦ h.toFun z) hfg

/-- Finite-dimensionality of `CuspForm Γ₁(N) k`, derived from finite-dimensionality of
`ModularForm Γ₁(N) k` (`dim_gen_cong_levels`) via the linear injection
`cuspFormToModularFormLin`. -/
theorem cuspForm_finiteDimensional :
    FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := by
  haveI : FiniteDimensional ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k) := by
    have hidx : (Gamma1 N).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
    have := dim_gen_cong_levels k (Gamma1 N) hidx
    show FiniteDimensional ℂ (ModularForm ((Gamma1 N : Subgroup (GL (Fin 2) ℝ))) k)
    exact this
  exact FiniteDimensional.of_injective
    (cuspFormToModularFormLin (N := N) (k := k))
    cuspFormToModularFormLin_injective

/-- The real-valued bilinear form `B_ℝ(f, g) := Re(petN f g)` on cusp forms, viewed as an
ℝ-vector space.  Reflexive by Hermitian symmetry and non-degenerate by `petN_definite`. -/
noncomputable def petN_realBilin :
    LinearMap.BilinForm ℝ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) where
  toFun f :=
    { toFun := fun g ↦ (petN f g).re
      map_add' := fun g₁ g₂ ↦ by
        show (petN f (g₁ + g₂)).re = (petN f g₁).re + (petN f g₂).re
        rw [petN_add_right, Complex.add_re]
      map_smul' := fun (c : ℝ) g ↦ by
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
  have h := petN_conj_symm f g
  have : (petN g f).re = (petN f g).re := by
    rw [← h, Complex.conj_re]
  linarith

private lemma petN_swap_eq_zero
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (h : petN f g = 0) :
    petN g f = 0 := by
  have hc := petN_conj_symm f g
  rw [h] at hc
  simpa using congr_arg (starRingEnd ℂ) hc

private lemma petN_eq_zero_of_re_eq_zero_of_I_smul_re_eq_zero
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hre : (petN g f).re = 0) (hIre : (petN (Complex.I • g) f).re = 0) :
    petN g f = 0 := by
  rw [petN_conj_smul_left] at hIre
  have h_im : (petN g f).im = 0 := by
    simp [Complex.mul_re, Complex.I_re, Complex.I_im] at hIre
    linarith
  exact Complex.ext (by simpa using hre) (by simpa using h_im)

/-- The orthogonal complement of `(cuspFormsOld).restrictScalars ℝ` w.r.t. `petN_realBilin`
equals `(cuspFormsNew).restrictScalars ℝ` as ℝ-submodules. The proof uses Hermitian
symmetry and `cuspFormsOld` being closed under multiplication by `i`. -/
lemma petN_realBilin_orthogonal_cuspFormsOld_eq :
    (petN_realBilin (N := N) (k := k)).orthogonal
        ((cuspFormsOld N k).restrictScalars ℝ) =
      (cuspFormsNew N k).restrictScalars ℝ := by
  ext f
  refine ⟨fun hf ↦ ?_, fun hf g hg ↦ ?_⟩
  · show f ∈ cuspFormsNew N k
    intro g hg
    have re_eq_zero : ∀ h ∈ Submodule.restrictScalars ℝ (cuspFormsOld N k),
        (petN h f).re = 0 := fun h hh ↦ by
      have := hf h hh
      simpa only [LinearMap.BilinForm.IsOrtho, petN_realBilin_apply] using this
    have hgf : petN g f = 0 :=
      petN_eq_zero_of_re_eq_zero_of_I_smul_re_eq_zero f g (re_eq_zero g hg)
        (re_eq_zero (Complex.I • g) ((cuspFormsOld N k).smul_mem Complex.I hg))
    exact petN_swap_eq_zero g f hgf
  · show (petN_realBilin g) f = 0
    rw [petN_realBilin_apply, petN_swap_eq_zero f g (hf g hg), Complex.zero_re]

/-- DS (5.20): `S_k(Γ₁(N)) = S_k^old ⊕ S_k^new` as inner product spaces.  `Disjoint` is
`cuspFormsOld_disjoint_cuspFormsNew`; `Codisjoint` comes from applying Mathlib's
`BilinForm.isCompl_orthogonal_iff_disjoint` to the reflexive form `petN_realBilin` over the
finite-dimensional ℝ-space, using `cuspFormsNew = (cuspFormsOld)^⊥`. -/
theorem cuspFormsOld_isCompl_cuspFormsNew :
    IsCompl (cuspFormsOld N k) (cuspFormsNew N k) := by
  refine ⟨cuspFormsOld_disjoint_cuspFormsNew, ?_⟩
  haveI : FiniteDimensional ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    cuspForm_finiteDimensional
  haveI : FiniteDimensional ℝ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    Module.Finite.trans ℂ _
  have hdisj_R : Disjoint
      ((cuspFormsOld N k).restrictScalars ℝ)
      ((petN_realBilin (N := N) (k := k)).orthogonal
        ((cuspFormsOld N k).restrictScalars ℝ)) := by
    rw [petN_realBilin_orthogonal_cuspFormsOld_eq]
    have hdisj_C := cuspFormsOld_disjoint_cuspFormsNew (N := N) (k := k)
    rw [Submodule.disjoint_def] at hdisj_C ⊢
    intro f hf₁ hf₂
    exact hdisj_C f hf₁ hf₂
  have h_iscompl_R := (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    petN_realBilin_isRefl (W := (cuspFormsOld N k).restrictScalars ℝ)).mpr hdisj_R
  rw [petN_realBilin_orthogonal_cuspFormsOld_eq] at h_iscompl_R
  rw [codisjoint_iff]
  have : ((cuspFormsOld N k).restrictScalars ℝ) ⊔
      ((cuspFormsNew N k).restrictScalars ℝ) = ⊤ :=
    h_iscompl_R.sup_eq_top
  apply Submodule.eq_top_iff'.mpr
  intro f
  have hf : f ∈ ((cuspFormsOld N k).restrictScalars ℝ) ⊔
      ((cuspFormsNew N k).restrictScalars ℝ) := by
    rw [this]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hf
  obtain ⟨x, hx, y, hy, hxy⟩ := hf
  rw [Submodule.mem_sup]
  exact ⟨x, hx, y, hy, hxy⟩

/-- **Oldform linear projection.**  The `ℂ`-linear endomorphism of `CuspForm Γ₁(N) k` that
projects onto `cuspFormsOld N k` along `cuspFormsNew N k`. -/
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

/-- **Reconstruction: `f = oldPart f + newPart f`.** -/
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

/-- **Characterisation of `cuspFormsOld` by vanishing newform part:**
`f ∈ cuspFormsOld N k ↔ newPart f = 0`. -/
theorem mem_cuspFormsOld_iff_newPart_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormsOld N k ↔ newPart f = 0 :=
  ⟨newPart_of_mem_cuspFormsOld,
    fun h ↦ by rw [← oldPart_add_newPart f, h, add_zero]; exact oldPart_mem_cuspFormsOld f⟩

/-- **Characterisation of `cuspFormsNew` by vanishing oldform part.** -/
theorem mem_cuspFormsNew_iff_oldPart_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    f ∈ cuspFormsNew N k ↔ oldPart f = 0 :=
  ⟨oldPart_of_mem_cuspFormsNew,
    fun h ↦ by
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

/-- Conditional `mainLemma` consumer: under the coprime-to-`N` Fourier vanishing hypothesis,
if additionally `newPart f = 0` then `f ∈ cuspFormsOld N k`.  The `_h_vanish` hypothesis
mirrors the `Newforms.mainLemma` signature and is unused in the present proof. -/
theorem mainLemma_of_newPart_eq_zero
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (_h_vanish : ∀ n : ℕ, Nat.Coprime n N →
      (ModularFormClass.qExpansion (1 : ℝ) f).coeff n = 0)
    (h_newPart_zero : newPart f = 0) :
    f ∈ cuspFormsOld N k :=
  (mem_cuspFormsOld_iff_newPart_eq_zero f).mpr h_newPart_zero

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
