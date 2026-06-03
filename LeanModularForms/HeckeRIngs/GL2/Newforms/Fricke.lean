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
import LeanModularForms.HeckeRIngs.GL2.Newforms.CoeffSeq
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.SlashActionAuxil

/-!
# Newforms: analytic interface and the Fricke operator

The T132 conditional analytic interface for prime non-vanishing, the structured `AnalyticContradiction` decomposition (`HeckeFEData`, `MellinPairData`, `ImAxisMellinData`), the Fricke matrix and its slash formula, the Fricke square/involution-up-to-scalar, and the Petersson adjoint identity for `W_N` (including the PSL(2,ℝ) FD-transport bridge).

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- The conditional analytic input packaging the missing content of
`Newform.exists_nonzero_prime_eigenvalue`: for every newform `f` in every
Nebentypus eigenspace and every finite exceptional set `S`, vanishing of
`f.lCoeff q` at all primes `q.Coprime N` with `q ∉ S` entails `False`. -/
def Newform.AnalyticContradiction : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
    f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
    ∀ (S : Finset ℕ),
      (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
        q ∉ S → f.lCoeff q = 0) → False


/-- Hecke's analytic continuation hypothesis: for every newform `f`, the
Dirichlet series `LSeries f.lCoeff_stripped` admits an entire extension to `ℂ`
(Hecke 1936; Diamond–Shurman §5.9, Miyake §4.3.5 / Theorem 4.5.16). -/
def Newform.HeckeEntireExtension : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
    LSeries.HasEntireExtension f.lCoeff_stripped

/-- Per-newform Hecke continuation data bridging Mathlib's `StrongFEPair` to
`LSeries.HasEntireExtension f.lCoeff_stripped` via a bridge equation on the
absolute-convergence half-plane (Miyake §4.3.5 / Theorem 4.5.16;
Diamond–Shurman §5.9). -/
@[ext]
structure Newform.HeckeFEData {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) where
  /-- Mathlib `StrongFEPair` capturing the cusp form's Mellin-transform pair. -/
  pair : StrongFEPair ℂ
  /-- The pair's `Λ` coincides with `LSeries f.lCoeff_stripped` on the
  absolute-convergence half-plane (so `Λ` is the entire extension). -/
  bridge : ∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    pair.Λ s = LSeries f.lCoeff_stripped s

/-- `HeckeEntireExtension` from per-newform `HeckeFEData`: each
`f.lCoeff_stripped` admits the entire extension `pair.Λ`. -/
theorem Newform.HeckeEntireExtension_of_HeckeFEData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f) :
    Newform.HeckeEntireExtension := by
  intro N _ k f
  obtain ⟨pair, bridge⟩ := h f
  exact ⟨pair.Λ, pair.differentiable_Λ, bridge⟩

/-- Build `Newform.HeckeFEData f` from explicit Mellin-pair-side data
(functions `F, G`, weight `kReal`, root number `ε`, the `WeakFEPair`
integrability/decay/functional-equation conditions) plus the bridge equation
`mellin F s = LSeries f.lCoeff_stripped s` on the absolute-convergence
half-plane. -/
noncomputable def Newform.HeckeFEData.ofMellinPairData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (F G : ℝ → ℂ) (kReal : ℝ) (ε : ℂ)
    (hF_int : MeasureTheory.LocallyIntegrableOn F (Set.Ioi 0))
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hkReal_pos : 0 < kReal) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      F (1 / x) = (ε * ((x ^ kReal : ℝ) : ℂ)) • G x)
    (hF_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ F x - 0) (fun x : ℝ ↦ x ^ r))
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ G x - 0) (fun x : ℝ ↦ x ^ r))
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin F s = LSeries f.lCoeff_stripped s) :
    Newform.HeckeFEData f where
  pair :=
    { f := F, g := G, k := kReal, ε := ε
      f₀ := 0, g₀ := 0
      hf_int := hF_int, hg_int := hG_int
      hk := hkReal_pos, hε := hε_ne
      h_feq := h_feq
      hf_top := hF_top, hg_top := hG_top
      hf₀ := rfl, hg₀ := rfl }
  bridge := h_bridge

/-- Bundles the Mellin-pair-side data needed to construct
`Newform.HeckeFEData f`, capturing the analytic obligations of the Hecke 1936
entire-continuation theorem (Diamond–Shurman §5.9 / Miyake §4.3.5). -/
@[ext]
structure Newform.MellinPairData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) where
  /-- Mellin-side function for the cusp form (e.g. `t ↦ f(it)`
  in classical theory). -/
  F : ℝ → ℂ
  /-- Mellin-side function for the Atkin-Lehner / Fricke twist
  (e.g. `t ↦ (f|W_N)(it)`). -/
  G : ℝ → ℂ
  /-- Root number `ε` of the functional equation. -/
  ε : ℂ
  /-- `F` is locally integrable on `Ioi 0`. -/
  hF_int : MeasureTheory.LocallyIntegrableOn F (Set.Ioi 0)
  /-- `G` is locally integrable on `Ioi 0`. -/
  hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0)
  /-- Cusp-form weight is positive (cast to ℝ from `(k : ℤ)`). -/
  hk_pos : 0 < (k : ℝ)
  /-- Root number is nonzero. -/
  hε_ne : ε ≠ 0
  /-- Functional equation `F (1/x) = ε · x^k · G x` on `Ioi 0`. -/
  h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
    F (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x
  /-- `F` has rapid polynomial decay at `∞`. -/
  hF_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ F x - 0) (fun x : ℝ ↦ x ^ r)
  /-- `G` has rapid polynomial decay at `∞`. -/
  hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ G x - 0) (fun x : ℝ ↦ x ^ r)
  /-- Mellin–Dirichlet bridge: `mellin F s = LSeries f.lCoeff_stripped s`
  on the absolute-convergence half-plane. -/
  h_bridge : ∀ {s : ℂ},
    LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    mellin F s = LSeries f.lCoeff_stripped s

/-- Specialisation of `Newform.HeckeFEData.ofMellinPairData` to the cusp-form
weight `(k : ℝ)`, consuming a bundled `Newform.MellinPairData f`. -/
noncomputable def Newform.HeckeFEData.ofMellinData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.MellinPairData f) : Newform.HeckeFEData f :=
  Newform.HeckeFEData.ofMellinPairData data.F data.G (k : ℝ) data.ε
    data.hF_int data.hG_int data.hk_pos data.hε_ne
    data.h_feq data.hF_top data.hG_top data.h_bridge

/-- The canonical newform Mellin-side function `t ↦ f(it)` for `t > 0`
(and `0` for `t ≤ 0`), specialising `ModularForms.imAxis` to `f.toCuspForm`. -/
noncomputable def Newform.imAxis {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) :
    ℝ → ℂ :=
  _root_.ModularForms.imAxis f.toCuspForm

/-- Continuity of `Newform.imAxis f` on `Ioi 0`. -/
lemma Newform.continuousOn_imAxis {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) :
    ContinuousOn (Newform.imAxis f) (Set.Ioi (0 : ℝ)) :=
  _root_.ModularForms.continuousOn_imAxis f.toCuspForm

/-- Local integrability of `Newform.imAxis f` on `Ioi 0`. -/
lemma Newform.locallyIntegrableOn_imAxis {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) :
    MeasureTheory.LocallyIntegrableOn (Newform.imAxis f) (Set.Ioi (0 : ℝ)) :=
  _root_.ModularForms.locallyIntegrableOn_imAxis f.toCuspForm

/-- `Newform.MellinPairData` constructor with the canonical Mellin-side
function `F := Newform.imAxis f`, discharging the `hF_int` field via
`Newform.locallyIntegrableOn_imAxis`. -/
noncomputable def Newform.MellinPairData.ofImAxis
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (G : ℝ → ℂ) (ε : ℂ)
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hk_pos : 0 < (k : ℝ)) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      Newform.imAxis f (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x)
    (hF_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ Newform.imAxis f x - 0) (fun x : ℝ ↦ x ^ r))
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ G x - 0) (fun x : ℝ ↦ x ^ r))
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s) :
    Newform.MellinPairData f where
  F := Newform.imAxis f
  G := G
  ε := ε
  hF_int := Newform.locallyIntegrableOn_imAxis f
  hG_int := hG_int
  hk_pos := hk_pos
  hε_ne := hε_ne
  h_feq := h_feq
  hF_top := hF_top
  hG_top := hG_top
  h_bridge := h_bridge

/-- Specialisation of `Newform.MellinPairData` to the canonical
`F := Newform.imAxis f`, dropping the auto-discharged `hF_int` field. The
remaining fields are the analytic Mellin-pair obligations of the Hecke 1936
entire-continuation theorem (Diamond–Shurman §5.9 / Miyake §4.3.5). -/
@[ext]
structure Newform.ImAxisMellinData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) where
  /-- Atkin-Lehner / Fricke-twist Mellin-side function. -/
  G : ℝ → ℂ
  /-- Root number `ε` of the functional equation. -/
  ε : ℂ
  /-- `G` is locally integrable on `Ioi 0`. -/
  hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0)
  /-- Cusp-form weight is positive (cast to ℝ from `(k : ℤ)`). -/
  hk_pos : 0 < (k : ℝ)
  /-- Root number is nonzero. -/
  hε_ne : ε ≠ 0
  /-- Functional equation: `(imAxis f) (1/x) = ε · x^k · G x` on `Ioi 0`. -/
  h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
    (Newform.imAxis f) (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x
  /-- `Newform.imAxis f` has rapid polynomial decay at `∞`. -/
  hF_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ Newform.imAxis f x - 0) (fun x : ℝ ↦ x ^ r)
  /-- `G` has rapid polynomial decay at `∞`. -/
  hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ ↦ G x - 0) (fun x : ℝ ↦ x ^ r)
  /-- Mellin–Dirichlet bridge. -/
  h_bridge : ∀ {s : ℂ},
    LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s

/-- Construct `Newform.MellinPairData f` from `Newform.ImAxisMellinData f`. -/
noncomputable def Newform.MellinPairData.ofImAxisData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.ImAxisMellinData f) : Newform.MellinPairData f :=
  Newform.MellinPairData.ofImAxis f data.G data.ε data.hG_int data.hk_pos
    data.hε_ne data.h_feq data.hF_top data.hG_top data.h_bridge

/-- Construct `Newform.HeckeFEData f` from `Newform.ImAxisMellinData f`. -/
noncomputable def Newform.HeckeFEData.ofImAxisData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.ImAxisMellinData f) : Newform.HeckeFEData f :=
  Newform.HeckeFEData.ofMellinData (Newform.MellinPairData.ofImAxisData data)


/-- Exponential decay of `Newform.imAxis f` at `∞`: the cusp-form-decay
statement specialised to a newform (Diamond–Shurman §5.9 / Miyake §4.3.5). -/
def Newform.HasImAxisExponentialDecay {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Prop :=
  _root_.ModularForms.HasImAxisExponentialDecay f.toCuspForm

/-- Rapid polynomial decay of `Newform.imAxis f` follows from the
exponential-decay hypothesis. -/
theorem Newform.imAxis_rapidDecay_of_exponentialDecay
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (h : Newform.HasImAxisExponentialDecay f) :
    ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ Newform.imAxis f x - 0) (fun x : ℝ ↦ x ^ r) :=
  _root_.ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay
    f.toCuspForm h

/-- `Γ₁(N)`-cusp-form-side `HasImAxisExponentialDecay` for any cusp form on
`(Gamma1 N).map (mapGL ℝ)` (strict period `1`). -/
theorem Newform.cuspForm_Gamma1_hasImAxisExponentialDecay {N : ℕ} [NeZero N]
    {k : ℤ} (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.ModularForms.HasImAxisExponentialDecay g := by
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  exact _root_.ModularForms.hasImAxisExponentialDecay_of_strictPeriod
    g (h := 1) one_pos h1_period

/-- For every `Γ₁(N)` newform `f`, `Newform.HasImAxisExponentialDecay f` holds
unconditionally (via `CuspFormClass.exp_decay_atImInfty` and the strict-period-1
fact for `Γ₁(N)`). -/
theorem Newform.hasImAxisExponentialDecay {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Newform.HasImAxisExponentialDecay f :=
  Newform.cuspForm_Gamma1_hasImAxisExponentialDecay f.toCuspForm





/-- The Atkin-Lehner / Fricke matrix `W_N := !![0, -1; N, 0]` for level `N`,
as an element of `GL (Fin 2) ℝ` with determinant `N > 0`. -/
noncomputable def Newform.frickeMatrix (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℝ), 0]
    (by simp [Matrix.det_fin_two, Nat.cast_ne_zero.mpr (NeZero.ne N)])

/-- Coercion of the Fricke matrix to a `Matrix`. -/
@[simp]
lemma Newform.frickeMatrix_coe (N : ℕ) [NeZero N] :
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; (N : ℝ), 0] := by
  simp [Newform.frickeMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- Determinant of the Fricke matrix is `N`. -/
lemma Newform.frickeMatrix_det (N : ℕ) [NeZero N] :
    (Newform.frickeMatrix N).det.val = (N : ℝ) := by
  change ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det = (N : ℝ)
  simp [Newform.frickeMatrix_coe, Matrix.det_fin_two_of]

/-- Determinant of the Fricke matrix is positive. -/
lemma Newform.frickeMatrix_det_pos (N : ℕ) [NeZero N] :
    0 < (Newform.frickeMatrix N).det.val := by
  rw [Newform.frickeMatrix_det]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

/-- `σ` of the Fricke matrix is the identity (since det > 0). -/
lemma Newform.frickeMatrix_σ (N : ℕ) [NeZero N] :
    UpperHalfPlane.σ (Newform.frickeMatrix N) = RingHom.id ℂ := by
  unfold UpperHalfPlane.σ
  rw [if_pos (Newform.frickeMatrix_det_pos N)]

/-- Numerator of the Fricke matrix at `τ`: `num W_N τ = -1`. -/
@[simp]
lemma Newform.frickeMatrix_num (N : ℕ) [NeZero N] (τ : ℂ) :
    UpperHalfPlane.num (Newform.frickeMatrix N) τ = -1 := by
  change ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 *
      τ + ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -1
  simp [Newform.frickeMatrix_coe]

/-- Denominator of the Fricke matrix at `τ`: `denom W_N τ = N · τ`. -/
@[simp]
lemma Newform.frickeMatrix_denom (N : ℕ) [NeZero N] (τ : ℂ) :
    UpperHalfPlane.denom (Newform.frickeMatrix N) τ = (N : ℂ) * τ := by
  change ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 *
      τ + ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (N : ℂ) * τ
  simp [Newform.frickeMatrix_coe]

/-- Möbius action of the Fricke matrix on `ℍ`: `W_N • τ = -1/(N · τ)`. -/
lemma Newform.frickeMatrix_smul (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    ((Newform.frickeMatrix N • τ : UpperHalfPlane) : ℂ) =
      -1 / ((N : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (Newform.frickeMatrix_det_pos N),
    Newform.frickeMatrix_num, Newform.frickeMatrix_denom]

/-- The integer Fricke conjugate matrix `δ = !![d, -(c/N); -N·b, a]` of
`γ = !![a, b; c, d] ∈ Γ₁(N)` (integer-valued since `N ∣ c`), satisfying
`W_N · γ = δ · W_N` at the matrix level. -/
def Newform.frickeConjMat (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 1 1, -(γ 1 0 / (N : ℤ)); -(N : ℤ) * γ 0 1, γ 0 0]

/-- Determinant of `Newform.frickeConjMat N γ` is `1` when `γ ∈ Γ₁(N)`. -/
lemma Newform.frickeConjMat_det (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) : (Newform.frickeConjMat N γ).det = 1 := by
  have h_div : γ 1 0 / (N : ℤ) * (N : ℤ) = γ 1 0 :=
    Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma1_mem N γ).mp hγN).2.2)
  have h_det_γ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hγ_det : γ.val.det = 1 := γ.2
    rwa [Matrix.det_fin_two] at hγ_det
  rw [Newform.frickeConjMat, Matrix.det_fin_two_of]
  linear_combination h_det_γ - (γ 0 1 : ℤ) * h_div

/-- The Fricke conjugate `Newform.frickeConjMat N γ` as an `SL(2, ℤ)` element,
when `γ ∈ Γ₁(N)`. -/
noncomputable def Newform.frickeConj (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) : SL(2, ℤ) :=
  ⟨Newform.frickeConjMat N γ, Newform.frickeConjMat_det N γ hγN⟩

/-- `Newform.frickeConj N γ ∈ Γ₁(N)` when `γ ∈ Γ₁(N)`. -/
lemma Newform.frickeConj_mem_Gamma1 (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) :
    Newform.frickeConj N γ hγN ∈ Gamma1 N := by
  have hγ := (Gamma1_mem N γ).mp hγN
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · show ((Newform.frickeConjMat N γ) 0 0 : ZMod N) = 1
    simp only [Newform.frickeConjMat, Matrix.cons_val_zero, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    exact hγ.2.1
  · show ((Newform.frickeConjMat N γ) 1 1 : ZMod N) = 1
    simp only [Newform.frickeConjMat, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    exact hγ.1
  · show ((Newform.frickeConjMat N γ) 1 0 : ZMod N) = 0
    simp only [Newform.frickeConjMat, Matrix.cons_val_zero, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
    push_cast
    simp

/-- Fricke conjugation/normalisation identity at the integer-matrix level:
`W_N · γ = δ · W_N` with `δ := frickeConjMat N γ`, showing `W_N` normalises
`Γ₁(N)` (Diamond–Shurman §5.5 / Miyake §4.6.5). -/
lemma Newform.frickeMat_int_mul_eq_frickeConjMat_mul_frickeMat_int
    (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hγN : γ ∈ Gamma1 N) :
    (!![0, -1; (N : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
      Newform.frickeConjMat N γ * !![0, -1; (N : ℤ), 0] := by
  have h_div : γ 1 0 / (N : ℤ) * (N : ℤ) = γ 1 0 :=
    Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      ((Gamma1_mem N γ).mp hγN).2.2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Newform.frickeConjMat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first | exact h_div.symm | ring

/-- The integer Fricke matrix, mapped through `algebraMap ℤ ℝ`, equals the real
Fricke matrix `!![0, -1; (N : ℝ), 0]`. -/
lemma Newform.frickeMatInt_map_algebraMap (N : ℕ) :
    (!![0, -1; (N : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) =
      !![0, -1; (N : ℝ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Fricke matrix conjugation/normalisation at the `GL (Fin 2) ℝ` level:
`W_N * mapGL ℝ γ = mapGL ℝ δ * W_N` for `γ ∈ Γ₁(N)` and `δ := frickeConj N γ`. -/
theorem Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix
    {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγN : γ ∈ Gamma1 N) :
    Newform.frickeMatrix N * mapGL ℝ γ =
      mapGL ℝ (Newform.frickeConj N γ hγN) * Newform.frickeMatrix N := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Newform.frickeMatrix_coe, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  have h_real :
      (!![0, -1; (N : ℤ), 0] * γ.val).map (algebraMap ℤ ℝ) =
        (Newform.frickeConjMat N γ * !![0, -1; (N : ℤ), 0]).map (algebraMap ℤ ℝ) :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ ↦ M.map (algebraMap ℤ ℝ))
      (Newform.frickeMat_int_mul_eq_frickeConjMat_mul_frickeMat_int N γ hγN)
  rw [Matrix.map_mul, Matrix.map_mul, Newform.frickeMatInt_map_algebraMap] at h_real
  exact h_real

/-- Fricke slash normalises the `Γ₁(N)` action: for any `Γ₁(N)`-slash-invariant
`F` and `γ ∈ Γ₁(N)`, `(F ∣[k] W_N) ∣[k] (mapGL ℝ γ) = F ∣[k] W_N`. -/
theorem Newform.slash_frickeMatrix_slash_mapGL_of_mem_Gamma1
    {N : ℕ} [NeZero N] {k : ℤ}
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [SlashInvariantFormClass F ((Gamma1 N).map (mapGL ℝ)) k]
    (f : F) (γ : SL(2, ℤ)) (hγN : γ ∈ Gamma1 N) :
    ((f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N) ∣[k]
        (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N := by
  rw [← SlashAction.slash_mul,
      Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix γ hγN,
      SlashAction.slash_mul]
  congr 1
  exact SlashInvariantForm.slash_action_eqn f _
    ⟨Newform.frickeConj N γ hγN, Newform.frickeConj_mem_Gamma1 N γ hγN, rfl⟩

/-- The Fricke slash operator `f ↦ f ∣[k] W_N` on slash-invariant forms, with
result slash invariance via `slash_frickeMatrix_slash_mapGL_of_mem_Gamma1`. -/
noncomputable def Newform.frickeSlashSIF
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k) :
    SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    exact Newform.slash_frickeMatrix_slash_mapGL_of_mem_Gamma1 f γ hγ

/-- The rational Fricke matrix `!![0, -1; (N : ℚ), 0]` as an element of
`GL (Fin 2) ℚ`. -/
noncomputable def Newform.frickeMatrixRat (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℚ), 0]
    (by simp [Matrix.det_fin_two, Nat.cast_ne_zero.mpr (NeZero.ne N)])

/-- `Newform.frickeMatrix N` is the `glMap`-image of `Newform.frickeMatrixRat N`. -/
lemma Newform.glMap_frickeMatrixRat (N : ℕ) [NeZero N] :
    glMap (Newform.frickeMatrixRat N) = Newform.frickeMatrix N := by
  apply Units.ext
  change (glMap (Newform.frickeMatrixRat N) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Newform.frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Newform.frickeMatrix_coe]
  change (Newform.frickeMatrixRat N : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
    !![0, -1; (N : ℝ), 0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Newform.frickeMatrixRat, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The Fricke matrix `W_N` maps cusps of `(Gamma1 N).map (mapGL ℝ)` to cusps of
the same group. -/
lemma Newform.frickeMatrix_smul_isCusp_Gamma1
    {N : ℕ} [NeZero N] {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (Newform.frickeMatrix N • c) ((Gamma1 N).map (mapGL ℝ)) := by
  rw [← Newform.glMap_frickeMatrixRat]
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  rw [show glMap (Newform.frickeMatrixRat N) • OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (Newform.frickeMatrixRat N • q) from
      (OnePoint.map_smul (algebraMap ℚ ℝ) (Newform.frickeMatrixRat N) q).symm]
  exact ⟨_, rfl⟩

/-- Slash by `W_N` as a `ℂ`-linear endomorphism of
`CuspForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
noncomputable def Newform.frickeSlashCuspForm
    {N : ℕ} [NeZero N] {k : ℤ} :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
        Newform.frickeSlashSIF f.toSlashInvariantForm
      holo' := f.holo'.slash k (Newform.frickeMatrix N)
      zero_at_cusps' := fun {c} hc ↦
        OnePoint.IsZeroAt.smul_iff.mp
          (f.zero_at_cusps' (Newform.frickeMatrix_smul_isCusp_Gamma1 hc)) }
  map_add' f g := by
    apply DFunLike.coe_injective
    change ((f : UpperHalfPlane → ℂ) + (g : UpperHalfPlane → ℂ)) ∣[k]
        Newform.frickeMatrix N =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N +
        (g : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N
    exact SlashAction.add_slash _ _ _ _
  map_smul' c f := by
    apply DFunLike.coe_injective
    change (c • (f : UpperHalfPlane → ℂ)) ∣[k] Newform.frickeMatrix N =
      c • ((f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N)
    rw [ModularForm.smul_slash, Newform.frickeMatrix_σ, RingHom.id_apply]

/-- Underlying function of the CuspForm Fricke operator. -/
@[simp]
lemma Newform.frickeSlashCuspForm_coe
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSlashCuspForm f : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N :=
  rfl

/-- Slash formula for the Fricke matrix:
`(f ∣[k] W_N) τ = f (W_N • τ) · N^{k-1} · (N · τ)^{-k}`. -/
theorem Newform.frickeMatrix_slash_apply
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    (f ∣[k] Newform.frickeMatrix N) τ =
      f (Newform.frickeMatrix N • τ) *
        ((N : ℝ) : ℂ) ^ (k - 1) *
        ((N : ℂ) * (τ : ℂ)) ^ (-k) := by
  rw [show (f ∣[k] Newform.frickeMatrix N) τ =
      UpperHalfPlane.σ (Newform.frickeMatrix N)
        (f (Newform.frickeMatrix N • τ)) *
        |((Newform.frickeMatrix N).det.val)| ^ (k - 1) *
        UpperHalfPlane.denom (Newform.frickeMatrix N) τ ^ (-k) from rfl,
    Newform.frickeMatrix_σ, RingHom.id_apply,
    Newform.frickeMatrix_denom]
  congr 2
  rw [Newform.frickeMatrix_det, abs_of_pos]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

private lemma frickeMatrix_sq_smul {N : ℕ} [NeZero N] (τ : UpperHalfPlane) :
    (Newform.frickeMatrix N * Newform.frickeMatrix N) • τ = τ := by
  apply UpperHalfPlane.ext
  rw [mul_smul, Newform.frickeMatrix_smul, Newform.frickeMatrix_smul]
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N), UpperHalfPlane.ne_zero τ]

/-- The scalar `(-1)^k · N^{k-2}` appearing when slashing twice by the Fricke
matrix `W_N` (the involution-up-to-scalar coefficient). -/
def Newform.frickeSquareScalar (N : ℕ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k * (N : ℂ) ^ (k - 2)

/-- Function-level Fricke double-slash identity: slashing twice by `W_N` scales
`f` by `Newform.frickeSquareScalar N k`. -/
lemma Newform.slash_frickeMatrix_frickeMatrix
    {N : ℕ} [NeZero N] {k : ℤ} (f : UpperHalfPlane → ℂ) :
    ((f ∣[k] Newform.frickeMatrix N) ∣[k] Newform.frickeMatrix N) =
      Newform.frickeSquareScalar N k • f := by
  funext τ
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  rw [Newform.frickeMatrix_slash_apply (f ∣[k] Newform.frickeMatrix N) τ,
    Newform.frickeMatrix_slash_apply f (Newform.frickeMatrix N • τ),
    show Newform.frickeMatrix N • Newform.frickeMatrix N • τ = τ by
      rw [← mul_smul]; exact frickeMatrix_sq_smul τ]
  rw [Newform.frickeMatrix_smul,
    show ((N : ℂ) * (-1 / ((N : ℂ) * (τ : ℂ)))) = -1 / (τ : ℂ) by field_simp,
    show ((N : ℝ) : ℂ) = (N : ℂ) by push_cast; rfl]
  rw [show f τ * (N : ℂ) ^ (k - 1) * (-1 / (τ : ℂ)) ^ (-k) *
        (N : ℂ) ^ (k - 1) * ((N : ℂ) * (τ : ℂ)) ^ (-k) =
      f τ * ((N : ℂ) ^ (k - 1) * (N : ℂ) ^ (k - 1)) *
        ((-1 / (τ : ℂ)) ^ (-k) * ((N : ℂ) * (τ : ℂ)) ^ (-k)) by ring]
  rw [show (-1 / (τ : ℂ)) ^ (-k) * ((N : ℂ) * (τ : ℂ)) ^ (-k) =
      (-(N : ℂ)) ^ (-k) by
    rw [← mul_zpow]
    congr 1
    field_simp]
  rw [show (N : ℂ) ^ (k - 1) * (N : ℂ) ^ (k - 1) = (N : ℂ) ^ (2 * (k - 1)) by
    rw [← zpow_add₀ hN_ne]; congr 1; ring]
  rw [show (-(N : ℂ)) ^ (-k) = (-1 : ℂ) ^ k * (N : ℂ) ^ (-k) by
    rw [show (-(N : ℂ)) = (-1 : ℂ) * (N : ℂ) by ring, mul_zpow]
    rw [show (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k by
      rw [zpow_neg, show ((-1 : ℂ) ^ k)⁻¹ = ((-1 : ℂ)⁻¹) ^ k from (inv_zpow _ _).symm,
          show ((-1 : ℂ)⁻¹ : ℂ) = -1 by norm_num]]]
  rw [Pi.smul_apply, smul_eq_mul, Newform.frickeSquareScalar]
  rw [show f τ * (N : ℂ) ^ (2 * (k - 1)) * ((-1 : ℂ) ^ k * (N : ℂ) ^ (-k)) =
      (-1 : ℂ) ^ k * ((N : ℂ) ^ (2 * (k - 1)) * (N : ℂ) ^ (-k)) * f τ by ring]
  rw [show (N : ℂ) ^ (2 * (k - 1)) * (N : ℂ) ^ (-k) = (N : ℂ) ^ (k - 2) by
    rw [← zpow_add₀ hN_ne]; congr 1; ring]

section FrickeAdjoint
open UpperHalfPlane MeasureTheory
open scoped UpperHalfPlane


private lemma peterssonAdj_frickeMatrix_det_val (N : ℕ) [NeZero N] :
    (peterssonAdj (Newform.frickeMatrix N)).det.val = (N : ℝ) :=
  (congr_arg Units.val (peterssonAdj_det _)).trans (Newform.frickeMatrix_det N)

private lemma peterssonAdj_frickeMatrix_det_pos (N : ℕ) [NeZero N] :
    0 < (peterssonAdj (Newform.frickeMatrix N)).det.val := by
  rw [peterssonAdj_frickeMatrix_det_val]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)



end FrickeAdjoint

private lemma frickeRootNumber_scalar_collapse {k : ℤ} {n x I fv : ℂ}
    (hn : n ≠ 0) (hx : x ≠ 0) (hI : I ≠ 0) :
    n ^ (1 - k) * I ^ k * x ^ k *
      (fv * n ^ (k - 1) * (x ^ (-k) * I ^ (-k))) = fv := by
  simp only [zpow_sub₀ hn, zpow_neg]
  field_simp

private lemma im_I_mul_ofReal_pos {r : ℝ} (hr : 0 < r) :
    0 < (Complex.I * ((r : ℝ) : ℂ)).im := by
  rw [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re, Complex.ofReal_im]
  simpa using hr

private lemma frickeMatrix_smul_imAxis_coe {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x) :
    (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ))) =
      Complex.I * ((1 / x : ℝ) : ℂ) := by
  have : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]
  rw [Complex.I_sq]

/-- Imaginary-axis functional equation derived from the Fricke slash formula:
`Newform.imAxis f (1/x) = (N^{1-k} · I^k · x^k) · (f ∣[k] W_N) ⟨I · (x/N), _⟩`. -/
theorem Newform.imAxis_eq_frickeSlash
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) {x : ℝ} (hx : 0 < x) :
    Newform.imAxis f (1 / x) =
      ((N : ℂ) ^ (1 - k) * Complex.I ^ k * ((x : ℝ) : ℂ) ^ k) *
      (⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N)
        ⟨Complex.I * ((x / (N : ℝ) : ℝ) : ℂ), im_I_mul_ofReal_pos
          (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))⟩ := by
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set τ_inner : UpperHalfPlane :=
    ⟨Complex.I * ((x / (N : ℝ) : ℝ) : ℂ), im_I_mul_ofReal_pos (div_pos hx
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))⟩
  set τ_outer : UpperHalfPlane :=
    ⟨Complex.I * ((1 / x : ℝ) : ℂ), im_I_mul_ofReal_pos (one_div_pos.mpr hx)⟩
  have h_smul_eq : (Newform.frickeMatrix N • τ_inner : UpperHalfPlane) = τ_outer := by
    apply UpperHalfPlane.ext
    rw [show ((Newform.frickeMatrix N • τ_inner : UpperHalfPlane) : ℂ) =
        (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ))) from
        Newform.frickeMatrix_smul _ _]
    exact frickeMatrix_smul_imAxis_coe hx
  have h_imAxis_eq :
      Newform.imAxis f (1 / x) =
        (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_outer := by
    change ModularForms.imAxis f.toCuspForm (1 / x) = _
    rw [ModularForms.imAxis_apply_of_pos f.toCuspForm (one_div_pos.mpr hx)]
    rfl
  rw [h_imAxis_eq, Newform.frickeMatrix_slash_apply (N := N) (k := k)
    (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_inner, h_smul_eq]
  have h_τ_inner_coe : (N : ℂ) * (τ_inner : ℂ) = Complex.I * ((x : ℝ) : ℂ) := by
    change (N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ)) = Complex.I * (x : ℂ)
    push_cast
    field_simp
  rw [h_τ_inner_coe, show ((N : ℝ) : ℂ) = (N : ℂ) by push_cast; rfl,
    show Complex.I * ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) * Complex.I by ring, mul_zpow]
  exact (frickeRootNumber_scalar_collapse hN_ne hx_ne Complex.I_ne_zero).symm

/-- Imaginary-axis functional equation for a CuspForm `twist` whose underlying
function equals the Fricke slash `⇑f.toCuspForm.toModularForm' ∣[k] W_N`:
`Newform.imAxis f (1/x) = (N^{1-k} · I^k · x^k) · ModularForms.imAxis twist (x/N)`. -/
theorem Newform.imAxis_feq_of_slashEq
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N)
    {x : ℝ} (hx : 0 < x) :
    Newform.imAxis f (1 / x) =
      ((N : ℂ) ^ (1 - k) * Complex.I ^ k * ((x : ℝ) : ℂ) ^ k) *
      _root_.ModularForms.imAxis twist (x / (N : ℝ)) := by
  rw [Newform.imAxis_eq_frickeSlash f hx]
  congr 1
  rw [_root_.ModularForms.imAxis_apply_of_pos twist
    (div_pos hx (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))), ← slash_eq]

end HeckeRing.GL2
