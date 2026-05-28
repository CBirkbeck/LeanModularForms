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
import LeanModularForms.HeckeRIngs.GL2.Newforms.CoeffSeq

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

/-- Under `Newform.AnalyticContradiction`, the conclusion of
`Newform.exists_nonzero_prime_eigenvalue` holds. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    (h_ana : Newform.AnalyticContradiction)
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 := by
  by_contra h_none
  push Not at h_none
  apply h_ana f χ hfχ S
  intro q hq hqN hqS
  have h_eq : f.eigenvalue ⟨q, hq.pos⟩ = f.lCoeff q := by
    rw [Newform.eigenvalue_eq_coeff f ⟨q, hq.pos⟩ hqN χ hfχ]
    rfl
  exact h_eq.symm.trans (h_none q hq hqN hqS)

/-- Under `Newform.AnalyticContradiction`, Strong Multiplicity One holds: a
newform is uniquely determined by its Hecke eigenvalues on any cofinite set
of primes coprime to `N`. -/
theorem strongMultiplicityOne_of_analyticContradiction
    (h_ana : Newform.AnalyticContradiction)
    (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine newform_unique f g χ hfχ hgχ ?_
  intro n hn
  by_cases hn_S : n.val ∈ S
  · have hn_pos : 0 < n.val := n.pos
    let bad : Finset ℕ := S ∪ S.image (· / n.val) ∪ n.val.primeFactors
    obtain ⟨q, hq_prime, hq_N, hq_notin, hq_ne⟩ :=
      Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
        h_ana f χ hfχ bad
    have hq_pos : 0 < q := hq_prime.pos
    have hq_notin_S : q ∉ S := fun hqS ↦ hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inl hqS))
    have hq_notin_img : q ∉ S.image (· / n.val) := fun h' ↦ hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inr h'))
    have hq_nd_n : ¬ q ∣ n.val := fun hqn ↦ hq_notin (by
      simp only [bad, Finset.mem_union, Nat.mem_primeFactors]
      exact Or.inr ⟨hq_prime, hqn, hn_pos.ne'⟩)
    have hn_coprime_q : Nat.Coprime n.val q :=
      ((hq_prime.coprime_iff_not_dvd).mpr hq_nd_n).symm
    have hnq_notin_S : n.val * q ∉ S := fun hnqS ↦ hq_notin_img <| by
      refine Finset.mem_image.mpr ⟨n.val * q, hnqS, ?_⟩
      exact Nat.mul_div_cancel_left _ hn_pos
    let q_pnat : ℕ+ := ⟨q, hq_pos⟩
    let nq_pnat : ℕ+ := ⟨n.val * q, Nat.mul_pos hn_pos hq_pos⟩
    have hmul_f : f.eigenvalue nq_pnat = f.eigenvalue n * f.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul f n q_pnat hn hq_N hn_coprime_q χ hfχ
    have hmul_g : g.eigenvalue nq_pnat = g.eigenvalue n * g.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul g n q_pnat hn hq_N hn_coprime_q χ hgχ
    have hcomb :
        f.eigenvalue n * f.eigenvalue q_pnat = g.eigenvalue n * f.eigenvalue q_pnat := by
      rw [← hmul_f, h nq_pnat (hn.mul_left hq_N) hnq_notin_S, hmul_g,
        h q_pnat hq_N hq_notin_S]
    exact mul_right_cancel₀ hq_ne hcomb
  · exact h n hn hn_S

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

/-- Global `Newform.HeckeEntireExtension` from per-newform
`Newform.ImAxisMellinData`. -/
theorem Newform.HeckeEntireExtension_of_ImAxisMellinData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.ImAxisMellinData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_HeckeFEData
    (fun _N _ _k f ↦ Newform.HeckeFEData.ofImAxisData (h f))

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

/-- For every `Γ₁(N)` newform `f`, `Newform.HasImAxisExponentialDecay f` holds
unconditionally (via `CuspFormClass.exp_decay_atImInfty` and the strict-period-1
fact for `Γ₁(N)`). -/
theorem Newform.hasImAxisExponentialDecay {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Newform.HasImAxisExponentialDecay f := by
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  exact _root_.ModularForms.hasImAxisExponentialDecay_of_strictPeriod
    f.toCuspForm (h := 1) one_pos h1_period

/-- Rapid polynomial decay of `Newform.imAxis f`, unconditional for any
`Γ₁(N)` newform. -/
theorem Newform.imAxis_rapidDecay {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) :
    ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ Newform.imAxis f x - 0) (fun x : ℝ ↦ x ^ r) :=
  Newform.imAxis_rapidDecay_of_exponentialDecay f
    (Newform.hasImAxisExponentialDecay f)

/-- `Newform.ImAxisMellinData` constructor taking the exponential-decay
hypothesis `hF_exp` in place of the `hF_top` rapid-decay field (discharged via
`Newform.imAxis_rapidDecay_of_exponentialDecay`). -/
noncomputable def Newform.ImAxisMellinData.ofExponentialDecay
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (G : ℝ → ℂ) (ε : ℂ)
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hk_pos : 0 < (k : ℝ)) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      (Newform.imAxis f) (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x)
    (hF_exp : Newform.HasImAxisExponentialDecay f)
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ G x - 0) (fun x : ℝ ↦ x ^ r))
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s) :
    Newform.ImAxisMellinData f where
  G := G
  ε := ε
  hG_int := hG_int
  hk_pos := hk_pos
  hε_ne := hε_ne
  h_feq := h_feq
  hF_top := Newform.imAxis_rapidDecay_of_exponentialDecay f hF_exp
  hG_top := hG_top
  h_bridge := h_bridge

/-- `Newform.ImAxisMellinData` constructor for any `Γ₁(N)` newform that
discharges both the `hF_exp` exponential-decay and `hF_top` rapid-decay
obligations via `Newform.hasImAxisExponentialDecay`. -/
noncomputable def Newform.ImAxisMellinData.ofData_auto
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (G : ℝ → ℂ) (ε : ℂ)
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hk_pos : 0 < (k : ℝ)) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      (Newform.imAxis f) (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x)
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ ↦ G x - 0) (fun x : ℝ ↦ x ^ r))
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s) :
    Newform.ImAxisMellinData f :=
  Newform.ImAxisMellinData.ofExponentialDecay f G ε hG_int hk_pos hε_ne
    h_feq (Newform.hasImAxisExponentialDecay f) hG_top h_bridge

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

/-- `Newform.ImAxisMellinData` constructor taking the Atkin-Lehner / Fricke
twist as a CuspForm `g`, discharging the entire twist (`G`-) side
(`hG_int`, `hG_top`) and the `F`-side decay fields automatically. -/
noncomputable def Newform.ImAxisMellinData.ofData_withTwist
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (ε : ℂ)
    (hk_pos : 0 < (k : ℝ)) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      (Newform.imAxis f) (1 / x) =
        (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • _root_.ModularForms.imAxis g x)
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s) :
    Newform.ImAxisMellinData f :=
  Newform.ImAxisMellinData.ofData_auto f
    (_root_.ModularForms.imAxis g) ε
    (_root_.ModularForms.locallyIntegrableOn_imAxis g)
    hk_pos hε_ne h_feq
    (_root_.ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay g
      (Newform.cuspForm_Gamma1_hasImAxisExponentialDecay g))
    h_bridge

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
  show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
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
  show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 *
      τ + ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -1
  simp [Newform.frickeMatrix_coe]

/-- Denominator of the Fricke matrix at `τ`: `denom W_N τ = N · τ`. -/
@[simp]
lemma Newform.frickeMatrix_denom (N : ℕ) [NeZero N] (τ : ℂ) :
    UpperHalfPlane.denom (Newform.frickeMatrix N) τ = (N : ℂ) * τ := by
  show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 *
      τ + ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (N : ℂ) * τ
  simp [Newform.frickeMatrix_coe]

/-- Möbius action of the Fricke matrix on `ℍ`: `W_N • τ = -1/(N · τ)`. -/
lemma Newform.frickeMatrix_smul (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    ((Newform.frickeMatrix N • τ : UpperHalfPlane) : ℂ) =
      -1 / ((N : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (Newform.frickeMatrix_det_pos N),
    Newform.frickeMatrix_num, Newform.frickeMatrix_denom]

/-- Fricke matrix involution identity at the matrix level:
`W_N · W_N = -N · I`. -/
lemma Newform.frickeMatrix_sq_matrix (N : ℕ) [NeZero N] :
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (-(N : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Newform.frickeMatrix_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- Fricke matrix involution at the GL level: the underlying matrix of
`W_N * W_N` is `(-N) • 1`. -/
lemma Newform.frickeMatrix_mul_self_val (N : ℕ) [NeZero N] :
    ((Newform.frickeMatrix N * Newform.frickeMatrix N : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) =
      (-(N : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [show ((Newform.frickeMatrix N * Newform.frickeMatrix N : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from rfl]
  exact Newform.frickeMatrix_sq_matrix N

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
    rw [Matrix.det_fin_two] at hγ_det
    show γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1
    convert hγ_det using 1
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

/-- Involution property of `Newform.frickeConj` on `Γ₁(N)`: applying it twice
returns `γ`. -/
lemma Newform.frickeConj_frickeConj (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) :
    Newform.frickeConj N (Newform.frickeConj N γ hγN)
        (Newform.frickeConj_mem_Gamma1 N γ hγN) = γ := by
  apply Subtype.ext
  show Newform.frickeConjMat N (Newform.frickeConj N γ hγN) = γ.val
  have h_div : γ.val 1 0 / (N : ℤ) * (N : ℤ) = γ.val 1 0 :=
    Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      ((Gamma1_mem N γ).mp hγN).2.2)
  ext i j
  simp only [Newform.frickeConjMat, Newform.frickeConj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  fin_cases i
  · fin_cases j
    · rfl
    · show -(-(N : ℤ) * γ.val 0 1 / (N : ℤ)) = γ.val 0 1
      rw [Int.neg_mul, Int.neg_ediv_of_dvd ⟨γ.val 0 1, rfl⟩,
          Int.mul_ediv_cancel_left _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
      ring
  · fin_cases j
    · show -(N : ℤ) * -(γ.val 1 0 / (N : ℤ)) = γ.val 1 0
      linear_combination h_div
    · rfl

/-- The involution on `{γ : SL(2, ℤ) // γ ∈ Gamma1 N}` induced by `frickeConj`,
bundled as an `Equiv` (self-inverse via `frickeConj_frickeConj`). -/
noncomputable def Newform.frickeConjEquivGamma1 (N : ℕ) [NeZero N] :
    {γ : SL(2, ℤ) // γ ∈ Gamma1 N} ≃ {γ : SL(2, ℤ) // γ ∈ Gamma1 N} where
  toFun γ := ⟨Newform.frickeConj N γ.val γ.property,
              Newform.frickeConj_mem_Gamma1 N γ.val γ.property⟩
  invFun γ := ⟨Newform.frickeConj N γ.val γ.property,
               Newform.frickeConj_mem_Gamma1 N γ.val γ.property⟩
  left_inv γ := by
    apply Subtype.ext
    exact Newform.frickeConj_frickeConj N γ.val γ.property
  right_inv γ := by
    apply Subtype.ext
    exact Newform.frickeConj_frickeConj N γ.val γ.property

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

/-- Underlying function of `Newform.frickeSlashSIF`. -/
@[simp]
lemma Newform.frickeSlashSIF_coe
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSlashSIF f : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N :=
  rfl

/-- `Newform.frickeSlashSIF` as a `ℂ`-linear endomorphism on slash-invariant
forms. -/
noncomputable def Newform.frickeSlashSIFLin
    {N : ℕ} [NeZero N] {k : ℤ} :
    SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := Newform.frickeSlashSIF
  map_add' f g := by
    apply DFunLike.coe_injective
    show ((f : UpperHalfPlane → ℂ) + (g : UpperHalfPlane → ℂ)) ∣[k]
        Newform.frickeMatrix N =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N +
        (g : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N
    exact SlashAction.add_slash _ _ _ _
  map_smul' c f := by
    apply DFunLike.coe_injective
    show (c • (f : UpperHalfPlane → ℂ)) ∣[k] Newform.frickeMatrix N =
      c • ((f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N)
    rw [ModularForm.smul_slash, Newform.frickeMatrix_σ, RingHom.id_apply]

/-- The rational Fricke matrix `!![0, -1; (N : ℚ), 0]` as an element of
`GL (Fin 2) ℚ`. -/
noncomputable def Newform.frickeMatrixRat (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℚ), 0]
    (by simp [Matrix.det_fin_two, Nat.cast_ne_zero.mpr (NeZero.ne N)])

/-- `Newform.frickeMatrix N` is the `glMap`-image of `Newform.frickeMatrixRat N`. -/
lemma Newform.glMap_frickeMatrixRat (N : ℕ) [NeZero N] :
    glMap (Newform.frickeMatrixRat N) = Newform.frickeMatrix N := by
  apply Units.ext
  show (glMap (Newform.frickeMatrixRat N) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Newform.frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Newform.frickeMatrix_coe]
  show (Newform.frickeMatrixRat N : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
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
  rw [show glMap (Newform.frickeMatrixRat N) •
        OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (Newform.frickeMatrixRat N • q)
      from (OnePoint.map_smul (algebraMap ℚ ℝ) (Newform.frickeMatrixRat N) q).symm]
  exact ⟨_, rfl⟩

/-- Slash by `W_N` as a `ℂ`-linear endomorphism of
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k`. -/
noncomputable def Newform.frickeSlashModularForm
    {N : ℕ} [NeZero N] {k : ℤ} :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
        Newform.frickeSlashSIF f.toSlashInvariantForm
      holo' := f.holo'.slash k (Newform.frickeMatrix N)
      bdd_at_cusps' := fun {c} hc ↦
        OnePoint.IsBoundedAt.smul_iff.mp
          (f.bdd_at_cusps' (Newform.frickeMatrix_smul_isCusp_Gamma1 hc)) }
  map_add' f g := by
    apply DFunLike.coe_injective
    show ((f : UpperHalfPlane → ℂ) + (g : UpperHalfPlane → ℂ)) ∣[k]
        Newform.frickeMatrix N =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N +
        (g : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N
    exact SlashAction.add_slash _ _ _ _
  map_smul' c f := by
    apply DFunLike.coe_injective
    show (c • (f : UpperHalfPlane → ℂ)) ∣[k] Newform.frickeMatrix N =
      c • ((f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N)
    rw [ModularForm.smul_slash, Newform.frickeMatrix_σ, RingHom.id_apply]

/-- Underlying function of the ModularForm Fricke operator. -/
@[simp]
lemma Newform.frickeSlashModularForm_coe
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSlashModularForm f : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N :=
  rfl

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
    show ((f : UpperHalfPlane → ℂ) + (g : UpperHalfPlane → ℂ)) ∣[k]
        Newform.frickeMatrix N =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N +
        (g : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N
    exact SlashAction.add_slash _ _ _ _
  map_smul' c f := by
    apply DFunLike.coe_injective
    show (c • (f : UpperHalfPlane → ℂ)) ∣[k] Newform.frickeMatrix N =
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
  rw [show ((f ∣[k] Newform.frickeMatrix N) ∣[k] Newform.frickeMatrix N) τ =
      ((f ∣[k] Newform.frickeMatrix N) (Newform.frickeMatrix N • τ)) *
        ((N : ℝ) : ℂ) ^ (k - 1) * ((N : ℂ) * (τ : ℂ)) ^ (-k) from
      Newform.frickeMatrix_slash_apply (f ∣[k] Newform.frickeMatrix N) τ]
  rw [Newform.frickeMatrix_slash_apply f (Newform.frickeMatrix N • τ)]
  rw [show Newform.frickeMatrix N • Newform.frickeMatrix N • τ = τ by
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

/-- Operator-level Fricke square (CuspForm version):
`frickeSlashCuspForm ∘ frickeSlashCuspForm` is scalar multiplication by
`Newform.frickeSquareScalar N k`. -/
lemma Newform.frickeSlashCuspForm_apply_apply
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Newform.frickeSlashCuspForm (Newform.frickeSlashCuspForm f) =
      Newform.frickeSquareScalar N k • f := by
  apply DFunLike.coe_injective
  show ((f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N) ∣[k]
      Newform.frickeMatrix N =
    Newform.frickeSquareScalar N k • (f : UpperHalfPlane → ℂ)
  exact Newform.slash_frickeMatrix_frickeMatrix _

/-- Operator-level Fricke square (ModularForm version). -/
lemma Newform.frickeSlashModularForm_apply_apply
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Newform.frickeSlashModularForm (Newform.frickeSlashModularForm f) =
      Newform.frickeSquareScalar N k • f := by
  apply DFunLike.coe_injective
  show ((f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N) ∣[k]
      Newform.frickeMatrix N =
    Newform.frickeSquareScalar N k • (f : UpperHalfPlane → ℂ)
  exact Newform.slash_frickeMatrix_frickeMatrix _

/-- `LinearMap`-level Fricke square (CuspForm version). -/
lemma Newform.frickeSlashCuspForm_comp_self {N : ℕ} [NeZero N] {k : ℤ} :
    (Newform.frickeSlashCuspForm (N := N) (k := k)).comp
        Newform.frickeSlashCuspForm =
      Newform.frickeSquareScalar N k • LinearMap.id :=
  LinearMap.ext fun f ↦ by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact Newform.frickeSlashCuspForm_apply_apply f

/-- `LinearMap`-level Fricke square (ModularForm version). -/
lemma Newform.frickeSlashModularForm_comp_self {N : ℕ} [NeZero N] {k : ℤ} :
    (Newform.frickeSlashModularForm (N := N) (k := k)).comp
        Newform.frickeSlashModularForm =
      Newform.frickeSquareScalar N k • LinearMap.id :=
  LinearMap.ext fun f ↦ by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact Newform.frickeSlashModularForm_apply_apply f

section FrickeAdjoint
open UpperHalfPlane MeasureTheory
open scoped UpperHalfPlane

/-- Petersson adjoint of `W_N` at the matrix level: underlying matrix
`!![0, 1; -N, 0]`. -/
lemma Newform.peterssonAdj_frickeMatrix_coe (N : ℕ) [NeZero N] :
    (peterssonAdj (Newform.frickeMatrix N) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1; -(N : ℝ), 0] := by
  rw [peterssonAdj_coe, Newform.frickeMatrix_coe, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private lemma peterssonAdj_frickeMatrix_det_val (N : ℕ) [NeZero N] :
    (peterssonAdj (Newform.frickeMatrix N)).det.val = (N : ℝ) := by
  rw [show (peterssonAdj (Newform.frickeMatrix N)).det.val =
      (Newform.frickeMatrix N).det.val from congr_arg Units.val (peterssonAdj_det _)]
  exact Newform.frickeMatrix_det N

private lemma peterssonAdj_frickeMatrix_det_pos (N : ℕ) [NeZero N] :
    0 < (peterssonAdj (Newform.frickeMatrix N)).det.val := by
  rw [peterssonAdj_frickeMatrix_det_val]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

/-- The Möbius action of `peterssonAdj W_N` agrees with that of `W_N` (the
overall sign cancels in the quotient). -/
lemma Newform.peterssonAdj_frickeMatrix_smul (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    (peterssonAdj (Newform.frickeMatrix N)) • τ = Newform.frickeMatrix N • τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_smul_of_det_pos (peterssonAdj_frickeMatrix_det_pos N),
      UpperHalfPlane.coe_smul_of_det_pos (Newform.frickeMatrix_det_pos N)]
  show
      ((peterssonAdj (Newform.frickeMatrix N) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 *
            (τ : ℂ) +
          (peterssonAdj (Newform.frickeMatrix N) :
              Matrix (Fin 2) (Fin 2) ℝ) 0 1) /
        ((peterssonAdj (Newform.frickeMatrix N) :
              Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (τ : ℂ) +
          (peterssonAdj (Newform.frickeMatrix N) :
              Matrix (Fin 2) (Fin 2) ℝ) 1 1) =
      ((Newform.frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (τ : ℂ) +
          (Newform.frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ) 0 1) /
        ((Newform.frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (τ : ℂ) +
          (Newform.frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ) 1 1)
  rw [Newform.peterssonAdj_frickeMatrix_coe, Newform.frickeMatrix_coe]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N), UpperHalfPlane.ne_zero τ]
  ring

/-- Slash by `peterssonAdj W_N` equals `(-1)^k` times slash by `W_N`. -/
lemma Newform.slash_peterssonAdj_frickeMatrix
    {N : ℕ} [NeZero N] {k : ℤ} (g : UpperHalfPlane → ℂ) :
    g ∣[k] peterssonAdj (Newform.frickeMatrix N) =
      ((-1 : ℂ) ^ k) • (g ∣[k] Newform.frickeMatrix N) := by
  funext τ
  have hadj_σ : UpperHalfPlane.σ (peterssonAdj (Newform.frickeMatrix N)) =
      RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos (peterssonAdj_frickeMatrix_det_pos N)]
  have hadj_denom : UpperHalfPlane.denom (peterssonAdj (Newform.frickeMatrix N)) τ =
      -((N : ℂ) * (τ : ℂ)) := by
    show (peterssonAdj (Newform.frickeMatrix N) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 *
          (τ : ℂ) +
        (peterssonAdj (Newform.frickeMatrix N) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 =
        -((N : ℂ) * (τ : ℂ))
    rw [Newform.peterssonAdj_frickeMatrix_coe]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    push_cast
    ring
  rw [Pi.smul_apply, smul_eq_mul, Newform.frickeMatrix_slash_apply]
  rw [show (g ∣[k] peterssonAdj (Newform.frickeMatrix N)) τ =
      UpperHalfPlane.σ (peterssonAdj (Newform.frickeMatrix N))
        (g ((peterssonAdj (Newform.frickeMatrix N)) • τ)) *
        |((peterssonAdj (Newform.frickeMatrix N)).det.val)| ^ (k - 1) *
        UpperHalfPlane.denom (peterssonAdj (Newform.frickeMatrix N)) τ ^ (-k) from rfl]
  rw [hadj_σ, RingHom.id_apply, peterssonAdj_frickeMatrix_det_val, hadj_denom,
      Newform.peterssonAdj_frickeMatrix_smul]
  rw [show |(N : ℝ)| = (N : ℝ) from
    abs_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))]
  rw [show (-((N : ℂ) * (τ : ℂ))) ^ (-k) =
      (-1 : ℂ) ^ k * ((N : ℂ) * (τ : ℂ)) ^ (-k) by
    rw [show (-((N : ℂ) * (τ : ℂ))) = (-1 : ℂ) * ((N : ℂ) * (τ : ℂ)) by ring,
        mul_zpow]
    rw [show (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k by
      rw [zpow_neg, show ((-1 : ℂ) ^ k)⁻¹ = ((-1 : ℂ)⁻¹) ^ k from
            (inv_zpow _ _).symm,
          show ((-1 : ℂ)⁻¹ : ℂ) = -1 by norm_num]]]
  ring

/-- Petersson adjoint identity for the Fricke slash on cusp forms:
`petN (frickeSlashCuspForm f) g = (-1)^k * petN f (frickeSlashCuspForm g)`. The
fundamental-domain and integrability hypotheses are passed as parameters. -/
theorem Newform.frickeSlashCuspForm_petN_adjoint
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hα_norm : ∀ (γ : SL(2, ℤ)), γ ∈ Gamma1 N →
      ∀ τ : UpperHalfPlane,
        petersson k (⇑f) (⇑((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))
          (Newform.frickeMatrix N • ((γ : SL(2, ℤ)) • τ)) =
        petersson k (⇑f) (⇑((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))
          (Newform.frickeMatrix N • τ))
    (hα_fd : MeasureTheory.IsFundamentalDomain (imageGamma1_PSL N)
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
        (Gamma1_fundDomain_PSL N : Set UpperHalfPlane)) μ_hyp)
    (h_int : MeasureTheory.IntegrableOn
      (petersson k (⇑f) (⇑((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g)))
      (Gamma1_fundDomain_PSL N) μ_hyp)
    (h_α_int : MeasureTheory.IntegrableOn
      (fun τ ↦ petersson k (⇑f) (⇑((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp) :
    petN (Newform.frickeSlashCuspForm f) g =
      (-1 : ℂ) ^ k * petN f (Newform.frickeSlashCuspForm g) := by
  have hg_adj : ⇑((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g) =
      ⇑g ∣[k] peterssonAdj (Newform.frickeMatrix N) := by
    show ((-1 : ℂ) ^ k) • ⇑(Newform.frickeSlashCuspForm g) =
      ⇑g ∣[k] peterssonAdj (Newform.frickeMatrix N)
    rw [Newform.frickeSlashCuspForm_coe]
    exact (Newform.slash_peterssonAdj_frickeMatrix _).symm
  rw [petN_slash_adjoint_GL2 (k := k) (Newform.frickeMatrix N)
    (Newform.frickeMatrix_det_pos N) f g (Newform.frickeSlashCuspForm f)
    (Newform.frickeSlashCuspForm_coe f) ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g)
    hg_adj hα_norm hα_fd h_int h_α_int, petN_smul_right]

/-- Petersson invariance under `W_N`-shifted `Γ₁(N)` translation:
`petersson k ⇑f ⇑g₂ (W_N • γ • τ) = petersson k ⇑f ⇑g₂ (W_N • τ)` for `γ ∈ Γ₁(N)`.
Discharges the `hα_norm` hypothesis of `petN_slash_adjoint_GL2` for `α := W_N`. -/
lemma Newform.frickeMatrix_smul_petersson_invariant
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) (τ : UpperHalfPlane) :
    petersson k (⇑f) (⇑g₂)
        (Newform.frickeMatrix N • ((γ : SL(2, ℤ)) • τ)) =
      petersson k (⇑f) (⇑g₂) (Newform.frickeMatrix N • τ) := by
  rw [show ((γ : SL(2, ℤ)) • τ : UpperHalfPlane) = (mapGL ℝ γ : GL (Fin 2) ℝ) • τ from rfl]
  rw [show (Newform.frickeMatrix N • ((mapGL ℝ γ : GL (Fin 2) ℝ) • τ) : UpperHalfPlane) =
      (Newform.frickeMatrix N * (mapGL ℝ γ : GL (Fin 2) ℝ)) • τ from
      (mul_smul _ _ τ).symm]
  rw [Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix γ hγ]
  rw [show (mapGL ℝ (Newform.frickeConj N γ hγ) * Newform.frickeMatrix N) • τ =
      (mapGL ℝ (Newform.frickeConj N γ hγ) : GL (Fin 2) ℝ) •
        (Newform.frickeMatrix N • τ) from mul_smul _ _ _]
  rw [show (mapGL ℝ (Newform.frickeConj N γ hγ) : GL (Fin 2) ℝ) •
        (Newform.frickeMatrix N • τ) =
      ((Newform.frickeConj N γ hγ : SL(2, ℤ)) : SL(2, ℤ)) •
        (Newform.frickeMatrix N • τ) from rfl]
  exact petersson_Gamma1_invariant f g₂ (Newform.frickeConj N γ hγ)
    (Newform.frickeConj_mem_Gamma1 N γ hγ) _

/-- Integrability of `τ ↦ petersson k f g₂ (W_N • τ)` on `Gamma1_fundDomain_PSL N`.
Discharges the `h_α_int` hypothesis of `petN_slash_adjoint_GL2`. -/
lemma Newform.integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MeasureTheory.IntegrableOn
      (fun τ ↦ petersson k (⇑f) (⇑g₂) (Newform.frickeMatrix N • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f g₂
  exact MeasureTheory.IntegrableOn.of_bound
    hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top
    (((petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g₂)).comp
      (continuous_const_smul (Newform.frickeMatrix N : GL (Fin 2) ℝ)))
        |>.aestronglyMeasurable.restrict) C
    (Filter.Eventually.of_forall fun τ ↦ hC _)

/-- The Fricke `W_N`-shifted `Γ₁(N)` fundamental-domain claim:
`W_N • Gamma1_fundDomain_PSL N` is a fundamental domain for `imageGamma1_PSL N`.
This holds because `W_N` normalises `Γ₁(N)` (see
`Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL`). -/
def Newform.HasFrickeFundDomainTransport (N : ℕ) [NeZero N] : Prop :=
  MeasureTheory.IsFundamentalDomain (imageGamma1_PSL N)
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
      (Gamma1_fundDomain_PSL N : Set UpperHalfPlane)) μ_hyp

/-- Fricke Petersson-adjoint identity conditional only on the single FD-transport
hypothesis `Newform.HasFrickeFundDomainTransport N`; the remaining invariance and
integrability hypotheses are discharged internally. -/
theorem Newform.frickeSlashCuspForm_petN_adjoint_of_isFundDomain
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_FD : Newform.HasFrickeFundDomainTransport N) :
    petN (Newform.frickeSlashCuspForm f) g =
      (-1 : ℂ) ^ k * petN f (Newform.frickeSlashCuspForm g) := by
  refine Newform.frickeSlashCuspForm_petN_adjoint f g
    (fun γ hγ τ ↦ Newform.frickeMatrix_smul_petersson_invariant f
      ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g) γ hγ τ)
    h_FD
    (integrableOn_petersson_Gamma1_fundDomain_PSL f
      ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))
    (Newform.integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL f
      ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))

/-- The Fricke matrix `W_N` as a `GL(2, ℝ)⁺` element, via its positive
determinant. -/
noncomputable def Newform.frickeMatrix_GLPos (N : ℕ) [NeZero N] : GL(2, ℝ)⁺ :=
  ⟨Newform.frickeMatrix N, Newform.frickeMatrix_det_pos N⟩

/-- The `PSL(2, ℝ)`-representative of the Fricke matrix `W_N`, via
`GLPos_to_PSL_R_term`. -/
noncomputable def Newform.frickeMatrix_PSL_R (N : ℕ) [NeZero N] : PSL(2, ℝ) :=
  GLPos_to_PSL_R_term (Newform.frickeMatrix_GLPos N)

/-- `frickeMatrix_PSL_R N` acts on `ℍ` exactly as `frickeMatrix N` does. -/
@[simp]
lemma Newform.frickeMatrix_PSL_R_smul (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    Newform.frickeMatrix_PSL_R N • τ =
      (Newform.frickeMatrix N : GL (Fin 2) ℝ) • τ := by
  show GLPos_to_PSL_R_term (Newform.frickeMatrix_GLPos N) • τ =
    (Newform.frickeMatrix N : GL (Fin 2) ℝ) • τ
  rw [GLPos_to_PSL_R_term_smul]
  rfl

/-- Set-level analogue of `Newform.frickeMatrix_PSL_R_smul`. -/
@[simp]
lemma Newform.frickeMatrix_PSL_R_smul_set (N : ℕ) [NeZero N]
    (S : Set UpperHalfPlane) :
    (Newform.frickeMatrix_PSL_R N • S : Set UpperHalfPlane) =
      (Newform.frickeMatrix N : GL (Fin 2) ℝ) • S := by
  ext τ
  simp only [Set.mem_smul_set, Newform.frickeMatrix_PSL_R_smul]

/-- The underlying matrix of `GLPos_to_SLR (frickeMatrix_GLPos N)` (via the GL
coercion) equals `(sqrt N)⁻¹ • W_N.val`. -/
lemma Newform.GLPos_to_SLR_frickeMatrix_GLPos_toGL_matrix (N : ℕ) [NeZero N] :
    (((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt (N : ℝ))⁻¹ •
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  unfold GLPos_to_SLR
  show (Real.sqrt ((Newform.frickeMatrix_GLPos N : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((Newform.frickeMatrix_GLPos N : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (Real.sqrt (N : ℝ))⁻¹ •
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ)
  rw [show (Newform.frickeMatrix_GLPos N : GL (Fin 2) ℝ).det.val =
      (N : ℝ) from Newform.frickeMatrix_det N]
  rfl

/-- GL-level Fricke conjugation identity for the SL_R representative
`W_SL := GLPos_to_SLR (frickeMatrix_GLPos N)`:
`(W_SL : GL) * mapGL ℝ γ = mapGL ℝ (frickeConj N γ) * (W_SL : GL)` for
`γ ∈ Γ₁(N)`. -/
lemma Newform.frickeMatrix_SLR_toGL_mul_mapGL_eq
    {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
        GL (Fin 2) ℝ) *
        (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ (Newform.frickeConj N γ hγ) : GL (Fin 2) ℝ) *
        ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
          GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Newform.GLPos_to_SLR_frickeMatrix_GLPos_toGL_matrix, Matrix.smul_mul,
    Matrix.mul_smul]
  congr 1
  rw [← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
    Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix γ hγ]

/-- SL(2, ℝ)-level Fricke conjugation identity:
`W_SL * map_SL γ = map_SL (frickeConj N γ) * W_SL` for `γ ∈ Γ₁(N)`, with
`W_SL := GLPos_to_SLR (frickeMatrix_GLPos N)` and
`map_SL := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)`. -/
lemma Newform.frickeMatrix_SL_R_mul_SLmap_eq
    {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    GLPos_to_SLR (Newform.frickeMatrix_GLPos N) *
        Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
          (Newform.frickeConj N γ hγ) *
        GLPos_to_SLR (Newform.frickeMatrix_GLPos N) := by
  refine (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ℝ)) ?_
  rw [map_mul, map_mul]
  show (((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) :
          SL(2, ℝ)) : GL (Fin 2) ℝ)) *
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ :
            SL(2, ℝ)) : GL (Fin 2) ℝ) =
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
            (Newform.frickeConj N γ hγ) :
            SL(2, ℝ)) : GL (Fin 2) ℝ) *
        ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) :
            SL(2, ℝ)) : GL (Fin 2) ℝ)
  rw [show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ : SL(2, ℝ)) :
        GL (Fin 2) ℝ) = (mapGL ℝ γ : GL (Fin 2) ℝ) from rfl,
    show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
            (Newform.frickeConj N γ hγ) : SL(2, ℝ)) :
        GL (Fin 2) ℝ) = (mapGL ℝ (Newform.frickeConj N γ hγ) :
        GL (Fin 2) ℝ) from rfl]
  exact Newform.frickeMatrix_SLR_toGL_mul_mapGL_eq γ hγ

/-- PSL(2, ℝ) Fricke conjugation identity:
`frickeMatrix_PSL_R N * SL2Z_to_PSL2R γ = SL2Z_to_PSL2R (frickeConj N γ) * frickeMatrix_PSL_R N`
for `γ ∈ Γ₁(N)`. -/
lemma Newform.frickeMatrix_PSL_R_mul_SL2Z_to_PSL2R_eq
    {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    Newform.frickeMatrix_PSL_R N * SL2Z_to_PSL2R γ =
      SL2Z_to_PSL2R (Newform.frickeConj N γ hγ) *
        Newform.frickeMatrix_PSL_R N := by
  show (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ)) *
        SL2Z_to_PSL2R γ =
      SL2Z_to_PSL2R (Newform.frickeConj N γ hγ) *
        (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ))
  rw [SL2Z_to_PSL2R_apply, SL2Z_to_PSL2R_apply]
  rw [show (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ)) *
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ :
            SL(2, ℝ)) : PSL(2, ℝ)) =
      ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) *
          Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ :
            SL(2, ℝ)) : PSL(2, ℝ)) from
      (QuotientGroup.mk_mul _ _ _).symm,
    show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
              (Newform.frickeConj N γ hγ) : SL(2, ℝ)) : PSL(2, ℝ)) *
          (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ)) =
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
              (Newform.frickeConj N γ hγ) *
            GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
          PSL(2, ℝ)) from
      (QuotientGroup.mk_mul _ _ _).symm,
    Newform.frickeMatrix_SL_R_mul_SLmap_eq γ hγ]

private lemma GLPos_to_SLR_frickeMatrix_GLPos_sq_eq_neg_scalar (N : ℕ) [NeZero N] :
    ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) *
      ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.scalar (Fin 2) (-1) := by
  rw [show ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
          GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) from
      (Matrix.SpecialLinearGroup.coe_GL_coe_matrix _).symm]
  rw [Newform.GLPos_to_SLR_frickeMatrix_GLPos_toGL_matrix]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [show ((Real.sqrt ((N : ℝ)))⁻¹ * (Real.sqrt (N : ℝ))⁻¹ : ℝ) = ((N : ℝ))⁻¹ by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]]
  rw [show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Newform.frickeMatrix N * Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from (Matrix.GeneralLinearGroup.coe_mul _ _).symm]
  rw [Newform.frickeMatrix_mul_self_val, smul_smul]
  rw [show ((N : ℝ))⁻¹ * (-(N : ℝ)) = -1 by
    field_simp [Nat.cast_ne_zero.mpr (NeZero.ne N)]]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.scalar]

/-- `frickeMatrix_PSL_R N` is self-inverse in `PSL(2, ℝ)`:
`frickeMatrix_PSL_R N * frickeMatrix_PSL_R N = 1` (since `W_N²` is the central
element `-1 : SL(2, ℝ)`). -/
lemma Newform.frickeMatrix_PSL_R_mul_self (N : ℕ) [NeZero N] :
    Newform.frickeMatrix_PSL_R N * Newform.frickeMatrix_PSL_R N = 1 := by
  show (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ)) *
        (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ)) = 1
  rw [show (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ)) *
        (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : PSL(2, ℝ)) =
      (((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) *
          GLPos_to_SLR (Newform.frickeMatrix_GLPos N) :
          SL(2, ℝ))) : PSL(2, ℝ)) from
      (QuotientGroup.mk_mul _ _ _).symm]
  rw [QuotientGroup.eq_one_iff]
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, ?_, ?_⟩
  · simp [Fintype.card_fin]
  · show Matrix.scalar (Fin 2) (-1) =
      ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) *
        GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ)
    symm
    show (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) :
          Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.scalar (Fin 2) (-1)
    exact GLPos_to_SLR_frickeMatrix_GLPos_sq_eq_neg_scalar N

/-- Inverse of `frickeMatrix_PSL_R N` is itself. -/
lemma Newform.frickeMatrix_PSL_R_inv (N : ℕ) [NeZero N] :
    (Newform.frickeMatrix_PSL_R N)⁻¹ = Newform.frickeMatrix_PSL_R N := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv]
  exact Newform.frickeMatrix_PSL_R_mul_self N

/-- Conjugating any `h ∈ imageGamma1_PSL_R N` by `frickeMatrix_PSL_R N` keeps the
result in `imageGamma1_PSL_R N`. -/
lemma Newform.frickeMatrix_PSL_R_conj_mem_imageGamma1_PSL_R
    {N : ℕ} [NeZero N] {h : PSL(2, ℝ)}
    (hh : h ∈ imageGamma1_PSL_R N) :
    Newform.frickeMatrix_PSL_R N * h * (Newform.frickeMatrix_PSL_R N)⁻¹ ∈
      imageGamma1_PSL_R N := by
  rw [← map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R] at hh
  obtain ⟨γ, hγ, hγeq⟩ := hh
  rw [← hγeq]
  rw [show Newform.frickeMatrix_PSL_R N * SL2Z_to_PSL2R γ *
        (Newform.frickeMatrix_PSL_R N)⁻¹ =
      SL2Z_to_PSL2R (Newform.frickeConj N γ hγ) by
    rw [Newform.frickeMatrix_PSL_R_mul_SL2Z_to_PSL2R_eq γ hγ,
        mul_assoc, mul_inv_cancel, mul_one]]
  rw [← map_SL2Z_to_PSL2R_eq_imageGamma1_PSL_R]
  exact ⟨_, Newform.frickeConj_mem_Gamma1 N γ hγ, rfl⟩

/-- `frickeMatrix_PSL_R N` lies in the normalizer of `imageGamma1_PSL_R N`. -/
lemma Newform.frickeMatrix_PSL_R_mem_normalizer (N : ℕ) [NeZero N] :
    Newform.frickeMatrix_PSL_R N ∈ (imageGamma1_PSL_R N).normalizer := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨Newform.frickeMatrix_PSL_R_conj_mem_imageGamma1_PSL_R, ?_⟩
  intro h_conj_mem
  have h_simplify :
      Newform.frickeMatrix_PSL_R N *
          (Newform.frickeMatrix_PSL_R N * h *
            (Newform.frickeMatrix_PSL_R N)⁻¹) *
          (Newform.frickeMatrix_PSL_R N)⁻¹ = h := by
    rw [Newform.frickeMatrix_PSL_R_inv N]
    have : Newform.frickeMatrix_PSL_R N *
            (Newform.frickeMatrix_PSL_R N * h * Newform.frickeMatrix_PSL_R N) *
            Newform.frickeMatrix_PSL_R N =
        (Newform.frickeMatrix_PSL_R N * Newform.frickeMatrix_PSL_R N) * h *
          (Newform.frickeMatrix_PSL_R N * Newform.frickeMatrix_PSL_R N) := by
      group
    rw [this, Newform.frickeMatrix_PSL_R_mul_self N, one_mul, mul_one]
  rw [← h_simplify]
  exact Newform.frickeMatrix_PSL_R_conj_mem_imageGamma1_PSL_R h_conj_mem

/-- The Fricke FD-transport claim `HasFrickeFundDomainTransport N` holds, via the
PSL(2, ℝ) normalizer fact and the canonical PSL_R fundamental domain. -/
lemma Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL
    (N : ℕ) [NeZero N] :
    Newform.HasFrickeFundDomainTransport N := by
  unfold Newform.HasFrickeFundDomainTransport
  rw [← Newform.frickeMatrix_PSL_R_smul_set]
  exact isFundamentalDomain_imageGamma1_PSL_of_PSL_R
    (isFundamentalDomain_Gamma1_PSL_R.smul_of_mem_normalizer
      (Newform.frickeMatrix_PSL_R_mem_normalizer N))

/-- Unconditional Fricke Petersson-adjoint identity:
`petN (frickeSlashCuspForm f) g = (-1)^k * petN f (frickeSlashCuspForm g)` for any
cusp forms `f, g` of level `Γ₁(N)` and weight `k`. -/
theorem Newform.frickeSlashCuspForm_petN_adjoint_unconditional
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (Newform.frickeSlashCuspForm f) g =
      (-1 : ℂ) ^ k * petN f (Newform.frickeSlashCuspForm g) :=
  Newform.frickeSlashCuspForm_petN_adjoint_of_isFundDomain f g
    (Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL N)

open UpperHalfPlane MeasureTheory ModularGroup in
/-- `W_N`-shifted `Σ_q` FD-tiling for `petN`: summing `peterssonInner` over
`W_N`-shifted SL-coset tiles equals `petN f g`, because `W_N` normalises `Γ₁(N)`
and `petersson k ⇑f ⇑g` is `Γ₁(N)`-invariant. -/
theorem Newform.sum_peterssonInner_frickeMatrix_smul_q_out_inv_fd_eq_petN
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
        ⇑f ⇑g =
    petN f g := by
  have h_petN_eq : (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
        petersson k ⇑f ⇑g τ ∂μ_hyp) = petN f g := by
    refine Finset.sum_congr rfl (fun q _ ↦ ?_)
    show ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹)
    rw [peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd ⇑f ⇑g (q.out)]
  exact (sum_setIntegral_GL2_shift (N := N)
    (α := Newform.frickeMatrix_GLPos N) (h := petersson k ⇑f ⇑g)
    (h_inv := fun γ hγ τ ↦ petersson_Gamma1_invariant f g γ hγ τ)
    (hα_h_inv := fun γ hγ τ ↦
      Newform.frickeMatrix_smul_petersson_invariant f g γ hγ τ)
    (hα_fd := Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL N)
    (h_int := integrableOn_petersson_Gamma1_fundDomain_PSL f g)
    (h_α_int :=
      Newform.integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL f g)).trans
    h_petN_eq

end FrickeAdjoint

private lemma frickeRootNumber_scalar_collapse {k : ℤ} {n x I fv : ℂ}
    (hn : n ≠ 0) (hx : x ≠ 0) (hI : I ≠ 0) :
    n ^ (1 - k) * I ^ k * x ^ k *
      (fv * n ^ (k - 1) * (x ^ (-k) * I ^ (-k))) = fv := by
  simp only [zpow_sub₀ hn, zpow_neg]
  field_simp

private lemma im_I_mul_ofReal_pos {r : ℝ} (hr : 0 < r) :
    0 < (Complex.I * ((r : ℝ) : ℂ)).im := by
  rw [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
    Complex.ofReal_im]
  simpa using hr

private lemma frickeMatrix_smul_imAxis_coe {N : ℕ} [NeZero N] {x : ℝ}
    (hx : 0 < x) :
    (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ))) =
      Complex.I * ((1 / x : ℝ) : ℂ) := by
  have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
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
        ⟨Complex.I * ((x / (N : ℝ) : ℝ) : ℂ), by
          have hN_pos : (0 : ℝ) < (N : ℝ) :=
            Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
          show 0 < (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ)).im
          rw [Complex.mul_im, Complex.I_im, Complex.I_re,
            Complex.ofReal_re, Complex.ofReal_im]
          have h_div_pos : 0 < x / (N : ℝ) := div_pos hx hN_pos
          simpa using h_div_pos⟩ := by
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set τ_inner : UpperHalfPlane :=
    ⟨Complex.I * ((x / (N : ℝ) : ℝ) : ℂ), im_I_mul_ofReal_pos (div_pos hx
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))⟩ with hτ_inner
  set τ_outer : UpperHalfPlane :=
    ⟨Complex.I * ((1 / x : ℝ) : ℂ), im_I_mul_ofReal_pos (one_div_pos.mpr hx)⟩
    with hτ_outer
  have h_smul_eq : (Newform.frickeMatrix N • τ_inner : UpperHalfPlane) = τ_outer := by
    apply UpperHalfPlane.ext
    rw [show ((Newform.frickeMatrix N • τ_inner : UpperHalfPlane) : ℂ) =
        (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ))) from
        Newform.frickeMatrix_smul _ _]
    exact frickeMatrix_smul_imAxis_coe hx
  have h_imAxis_eq :
      Newform.imAxis f (1 / x) =
        (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_outer := by
    rw [show Newform.imAxis f = ModularForms.imAxis f.toCuspForm from rfl,
      ModularForms.imAxis_apply_of_pos f.toCuspForm (one_div_pos.mpr hx)]
    rfl
  rw [h_imAxis_eq, Newform.frickeMatrix_slash_apply (N := N) (k := k)
    (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_inner, h_smul_eq]
  have h_τ_inner_coe : (N : ℂ) * (τ_inner : ℂ) = Complex.I * ((x : ℝ) : ℂ) := by
    show (N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ)) = Complex.I * (x : ℂ)
    push_cast
    field_simp
  rw [h_τ_inner_coe]
  set fv : ℂ := (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_outer
  have h_N_cast : ((N : ℝ) : ℂ) = (N : ℂ) := by push_cast; rfl
  rw [h_N_cast, show Complex.I * ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) * Complex.I by ring,
    mul_zpow]
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
