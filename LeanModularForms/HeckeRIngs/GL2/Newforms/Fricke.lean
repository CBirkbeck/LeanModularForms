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
/-! ### T132 — Conditional analytic interface for prime-nonvanishing / SMO

`Newform.exists_nonzero_prime_eigenvalue` remains `sorry` pending
genuine analytic input (Hecke's analytic continuation / functional
equation for cusp-form L-series, not yet in Mathlib).  This section
isolates that missing content as a single named proposition
`Newform.AnalyticContradiction`, and re-expresses the
prime-nonvanishing conclusion and the downstream Strong Multiplicity
One theorem as conditional statements taking that proposition as an
explicit hypothesis.

A single future discharge of `Newform.AnalyticContradiction` (once
Mathlib gains the required analytic machinery) closes the entire
conditional chain without further plumbing.  The conditional interface
adds **no new `axiom`, `opaque`, or `sorry`** — the obligation is
localised to the named `Prop`. -/

/-- **Named analytic-contradiction hypothesis (T132).**

The conditional input packaging the missing analytic content of
`Newform.exists_nonzero_prime_eigenvalue`.  States that for every
newform `f : Newform N k` in every Nebentypus character eigenspace
`modFormCharSpace k χ` and every finite exceptional set `S : Finset ℕ`,
the bad-prime-zero assumption
`∀ q prime, q.Coprime N → q ∉ S → f.lCoeff q = 0`
entails `False`.

**Mathematical route.**  Under the bad-prime-zero assumption, T111
(`Newform.lSeries_stripped_eq_dirichlet_quotient_value`) and its T129
special-point specialisation identify
`LSeries f.lCoeff_stripped` with an explicit ratio of Dirichlet
L-functions modulo finite local corrections, on the absolute-
convergence half-plane `Re s > k/2 + 1`.  Hecke's analytic continuation
extends the LHS to an entire function of `s`; the RHS extends
meromorphically with **poles** at the zeros of its denominator
(`LSeries χ̃ s'` etc.), contradicting entirety.  Formalising Hecke's
analytic continuation for cusp-form L-series (or the equivalent
functional equation `Λ(s) = ± Λ(k − s)`) is the precise remaining
obligation.

**Why a `Prop` and not an `axiom`.**  Packaging the missing content as
a named `Prop` keeps the proof obligation explicit, localised, and
free of harness-breaking `axiom`/`opaque` declarations.  Downstream
consumers take an `h_ana : Newform.AnalyticContradiction` argument
rather than silently depending on an unfinished sorry. -/
def Newform.AnalyticContradiction : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
    f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
    ∀ (S : Finset ℕ),
      (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
        q ∉ S → f.lCoeff q = 0) → False

/-- **Conditional prime-nonvanishing (T132).**  Under
`Newform.AnalyticContradiction`, the conclusion of
`Newform.exists_nonzero_prime_eigenvalue` holds.

Proof: contrapositive.  If every prime `q.Coprime N` with `q ∉ S`
satisfied `f.eigenvalue ⟨q, _⟩ = 0`, then by
`Newform.eigenvalue_eq_coeff` also `f.lCoeff q = 0`, which is the
bad-prime-zero setup contradicting `AnalyticContradiction`. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    (h_ana : Newform.AnalyticContradiction)
    (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 := by
  by_contra h_none
  push_neg at h_none
  apply h_ana f χ hfχ S
  intro q hq hqN hqS
  have h_eig : f.eigenvalue ⟨q, hq.pos⟩ = 0 := h_none q hq hqN hqS
  have h_eq : f.eigenvalue ⟨q, hq.pos⟩ = f.lCoeff q := by
    rw [Newform.eigenvalue_eq_coeff f ⟨q, hq.pos⟩ hqN χ hfχ]
    rfl
  rw [h_eq] at h_eig
  exact h_eig

/-- **Conditional Strong Multiplicity One (T132).**  Under
`Newform.AnalyticContradiction`, the Strong Multiplicity One theorem
holds: a newform is uniquely determined by its Hecke eigenvalues on
any cofinite set of primes coprime to `N`.

Mirrors the body of `strongMultiplicityOne` with
`Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction` in
place of the sorry'd `Newform.exists_nonzero_prime_eigenvalue`. -/
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
    have hq_notin_S : q ∉ S := fun hqS => hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inl hqS))
    have hq_notin_img : q ∉ S.image (· / n.val) := fun h' => hq_notin (by
      simp only [bad, Finset.mem_union]; exact Or.inl (Or.inr h'))
    have hq_nd_n : ¬ q ∣ n.val := fun hqn => hq_notin (by
      simp only [bad, Finset.mem_union, Nat.mem_primeFactors]
      exact Or.inr ⟨hq_prime, hqn, hn_pos.ne'⟩)
    have hn_coprime_q : Nat.Coprime n.val q :=
      ((hq_prime.coprime_iff_not_dvd).mpr hq_nd_n).symm
    have hnq_notin_S : n.val * q ∉ S := fun hnqS => hq_notin_img <| by
      refine Finset.mem_image.mpr ⟨n.val * q, hnqS, ?_⟩
      exact Nat.mul_div_cancel_left _ hn_pos
    let q_pnat : ℕ+ := ⟨q, hq_pos⟩
    let nq_pnat : ℕ+ := ⟨n.val * q, Nat.mul_pos hn_pos hq_pos⟩
    have hnq_N : Nat.Coprime (n.val * q) N := hn.mul_left hq_N
    have hq_eq : f.eigenvalue q_pnat = g.eigenvalue q_pnat := h q_pnat hq_N hq_notin_S
    have hnq_eq : f.eigenvalue nq_pnat = g.eigenvalue nq_pnat := h nq_pnat hnq_N hnq_notin_S
    have hmul_f : f.eigenvalue nq_pnat = f.eigenvalue n * f.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul f n q_pnat hn hq_N hn_coprime_q χ hfχ
    have hmul_g : g.eigenvalue nq_pnat = g.eigenvalue n * g.eigenvalue q_pnat :=
      Newform.eigenvalue_coprime_mul g n q_pnat hn hq_N hn_coprime_q χ hgχ
    have hcomb :
        f.eigenvalue n * f.eigenvalue q_pnat = g.eigenvalue n * f.eigenvalue q_pnat := by
      rw [← hmul_f, hnq_eq, hmul_g, hq_eq]
    exact mul_right_cancel₀ hq_ne hcomb
  · exact h n hn hn_S

/-! ### T132 — Structured analytic decomposition of `AnalyticContradiction`

The raw `Newform.AnalyticContradiction` packages the entire analytic
obligation behind `Newform.exists_nonzero_prime_eigenvalue` as a single
black-box `Prop`.  The classical Diamond–Shurman §5.9 / Miyake §4.5.16
proof actually splits cleanly into **two independent analytic
obligations**:

1. **Hecke entire continuation**: every newform's stripped LSeries
   admits an entire extension to `ℂ`.  This is Hecke 1936; the Mathlib
   analogue for Dirichlet L-functions is
   `differentiable_completedLFunction`.

2. **Analytic incompatibility under bad-prime**: under the bad-prime-
   zero hypothesis, the explicit Dirichlet-quotient identification
   from T111 forces the stripped LSeries to inherit a pole, hence to
   *not* admit an entire extension.

These two propositions are independently formalisable (the first via
Mellin / `WeakFEPair` infrastructure, the second via T111 + identity
theorem + Dirichlet pole tracking), and they are **jointly
contradictory**: the bridge theorem
`analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime`
trivially combines them into the original raw `AnalyticContradiction`.

This is a strict analytic-API improvement:  the next worker now has
two clean named obligations to discharge, each with a precise
classical proof, instead of one opaque `False`-producing `Prop`. -/

/-- **Hecke's analytic continuation hypothesis (T132).**
For every newform `f : Newform N k`, the stripped Fourier coefficient
sequence `f.lCoeff_stripped` admits an entire extension of its
Dirichlet series `LSeries f.lCoeff_stripped` to `ℂ`.

Classically this is Hecke 1936 (Diamond–Shurman §5.9 / Miyake
§4.3.5 / Theorem 4.5.16): every cusp-form L-series extends to an
entire function on `ℂ`, satisfying the functional equation
`Λ(s, f) = ε · Λ(k - s, f)` for the completed L-series.  The stripped
variant is the part of the Fourier sequence supported on indices
coprime to the level `N`; its Dirichlet series differs from the full
one by a finite Euler-factor adjustment (a polynomial), preserving
entirety.

**Status.**  Not yet formalised in Mathlib for cusp forms; the
analogue for Dirichlet character L-functions is provided by
`differentiable_completedLFunction`
(`Mathlib.NumberTheory.LSeries.DirichletContinuation`).  Once the
cusp-form analogue is in place, this proposition is automatic. -/
def Newform.HeckeEntireExtension : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
    LSeries.HasEntireExtension f.lCoeff_stripped

/-- **Per-newform Hecke continuation data via `StrongFEPair` (T132 H1
reduction).**

A structured Hecke continuation hypothesis bridging Mathlib's Mellin /
functional-equation API (`StrongFEPair`) to
`LSeries.HasEntireExtension f.lCoeff_stripped`.  The data:

* `pair : StrongFEPair ℂ` — Mathlib's strong functional-equation pair
  (a Mellin-transform pair `(f, g)` of rapidly-decaying functions
  satisfying the cusp-form-style functional equation
  `f (1/x) = ε · x^k · g(x)`).
* `bridge` — equation `pair.Λ s = LSeries f.lCoeff_stripped s` on the
  absolute-convergence half-plane.

In Hecke 1936's classical proof, the input pair is built from the
modular form `f` and its Atkin-Lehner / Fricke twist `f | W_N`; the
Mellin transform of `f - f₀` (the cusp form's exponential decay
trick) gives the completed L-series `Λ(s, f)`.  Mathlib's
`StrongFEPair.differentiable_Λ` then gives entirety of `pair.Λ`,
and via `bridge` the entire extension of
`LSeries f.lCoeff_stripped` follows.

**Status as a reduction.**  Replacing the global black-box
`HeckeEntireExtension` Prop with the per-newform `HeckeFEData`
structure makes the analytic obligation strictly less opaque:
downstream callers no longer need to assume entirety abstractly,
they instead provide a typed `StrongFEPair` plus a per-newform
bridge equation.  The `pair` field can in principle be constructed
from the modular form using Mathlib's existing Mellin infrastructure
(`Mathlib.Analysis.MellinTransform`,
`Mathlib.NumberTheory.LSeries.AbstractFuncEq`), reducing the
Hecke 1936 obligation to the bridge equation alone.

References: Miyake §4.3.5 / Theorem 4.5.16; Diamond-Shurman §5.9. -/
structure Newform.HeckeFEData {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) where
  /-- Mathlib `StrongFEPair` capturing the cusp form's Mellin-transform pair. -/
  pair : StrongFEPair ℂ
  /-- The pair's `Λ` coincides with `LSeries f.lCoeff_stripped` on the
  absolute-convergence half-plane (so `Λ` is the entire extension). -/
  bridge : ∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    pair.Λ s = LSeries f.lCoeff_stripped s

/-- **`HeckeEntireExtension` from per-newform `HeckeFEData` (T132 H1 step).**

If for every newform `f` we are given `Newform.HeckeFEData f` (a
`StrongFEPair` plus a bridge equation), then `Newform.HeckeEntireExtension`
holds: each `f.lCoeff_stripped` admits an entire extension via
`pair.Λ`.

This is the strictly reducing constructor for the H1 hypothesis: the
Hecke 1936 entire-continuation theorem is now packaged as data
(`StrongFEPair` + bridge), each field independently formalisable
via Mathlib's Mellin infrastructure. -/
theorem Newform.HeckeEntireExtension_of_HeckeFEData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f) :
    Newform.HeckeEntireExtension := by
  intro N _ k f
  obtain ⟨pair, bridge⟩ := h f
  exact ⟨pair.Λ, pair.differentiable_Λ, bridge⟩

/-- **Reusable explicit-fields constructor for `Newform.HeckeFEData`
(T132 H1 bridge).**

Build `Newform.HeckeFEData f` from explicit Mellin-pair-side data
(two real-variable functions `F, G : ℝ → ℂ`, real weight `kReal`,
root number `ε`, all `WeakFEPair` integrability / decay / functional-
equation conditions with zero constant terms) plus the **bridge
equation** identifying `mellin F s` with `LSeries f.lCoeff_stripped s`
on the absolute-convergence half-plane.

This isolates the missing analytic input — the Hecke 1936 construction
of the cusp-form Mellin pair — as **explicit named fields**, with no
`sorry` and no opaque hypothesis.  Downstream callers can plug in
concrete Mellin-side data once the corresponding Mellin infrastructure
for cusp forms is formalised.

Mathematical content (Diamond–Shurman §5.9, Miyake §4.3.5 / Theorem
4.5.16):

* `F` corresponds to `t ↦ f(it)` (the Mellin-side function on `Ioi 0`);
* `G` corresponds to `t ↦ (f|W_N)(it)` (Atkin–Lehner / Fricke twist);
* `kReal = (k : ℝ)` is the weight;
* `ε` is the global root number;
* The functional equation `F (1/x) = ε · x^k · G x` is Hecke's classical
  involution under `t ↦ 1 / (Nt)` simplified to the level-`1` form;
* The bridge identifies the completed L-series `Λ_f s = mellin F s` with
  the Dirichlet series `LSeries f.lCoeff_stripped s` on the half-plane,
  reflecting the standard Mellin–Dirichlet correspondence
  `Λ_f s = (2π)^(-s) · Γ(s) · L(f, s)` (modulo the strip-vs-stripped
  Dirichlet-quotient normalisation captured by `lCoeff_stripped`).

The output has the same shape as `Newform.HeckeFEData.mk`, but exposes
each `StrongFEPair` field as a separate explicit hypothesis, making the
analytic obligations strictly more transparent to formalise. -/
noncomputable def Newform.HeckeFEData.ofMellinPairData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (F G : ℝ → ℂ) (kReal : ℝ) (ε : ℂ)
    (hF_int : MeasureTheory.LocallyIntegrableOn F (Set.Ioi 0))
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hkReal_pos : 0 < kReal) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      F (1 / x) = (ε * ((x ^ kReal : ℝ) : ℂ)) • G x)
    (hF_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => F x - 0) (fun x : ℝ => x ^ r))
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r))
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

/-- **Cusp-form-side Mellin-pair data structure (T132 H1).**

Bundles the Mellin-pair-side data needed to construct
`Newform.HeckeFEData f` from local cusp-form / L-function infrastructure
into a single named structure.  Each field is a narrow named hypothesis
with explicit type, capturing **exactly** the analytic obligations of
the Hecke 1936 entire-continuation theorem (Diamond–Shurman §5.9 /
Miyake §4.3.5 / Theorem 4.5.16):

* `F, G : ℝ → ℂ` — the Mellin-side functions for the cusp form `f` and
  its Atkin-Lehner / Fricke twist;
* `ε : ℂ` — the global root number;
* `hF_int, hG_int` — local integrability on `Ioi 0`;
* `hk_pos` — cusp-form weight positive (cast to ℝ);
* `hε_ne` — root number nonzero;
* `h_feq` — the functional involution `F (1/x) = ε · x^k · G x`;
* `hF_top, hG_top` — polynomial decay at `∞`;
* `h_bridge` — the **Mellin–Dirichlet bridge**: `mellin F s` equals
  `LSeries f.lCoeff_stripped s` on the absolute-convergence half-plane.

The bridge is the most substantive obligation: it ties the analytic
Mellin-side construction to the local `LSeries.lCoeff_stripped` API
(reflecting `Λ_f s = (2π)^(-s) · Γ(s) · L(f, s)` modulo bad-prime
stripping). -/
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
    (fun x : ℝ => F x - 0) (fun x : ℝ => x ^ r)
  /-- `G` has rapid polynomial decay at `∞`. -/
  hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r)
  /-- Mellin–Dirichlet bridge: `mellin F s = LSeries f.lCoeff_stripped s`
  on the absolute-convergence half-plane. -/
  h_bridge : ∀ {s : ℂ},
    LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    mellin F s = LSeries f.lCoeff_stripped s

/-- **Theorem-level bridge: cusp-form Mellin-pair data ⇒ `HeckeFEData f`
(T132 H1).**

One-line specialization of `Newform.HeckeFEData.ofMellinPairData` to
the cusp-form weight (`kReal := (k : ℝ)`).  Consumes the bundled
`Newform.MellinPairData f` structure and produces `Newform.HeckeFEData f`
suitable for the SMO consumer chain
(`strongMultiplicityOne_of_HeckeFEData_of_PerNewformFullDirichletData_of_newformUnique`). -/
noncomputable def Newform.HeckeFEData.ofMellinData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.MellinPairData f) : Newform.HeckeFEData f :=
  Newform.HeckeFEData.ofMellinPairData data.F data.G (k : ℝ) data.ε
    data.hF_int data.hG_int data.hk_pos data.hε_ne
    data.h_feq data.hF_top data.hG_top data.h_bridge

/-- **Canonical newform Mellin-side function: `t ↦ f(it)` (T132 H1).**

Specialises the generic `ModularForms.imAxis` to a newform's underlying
cusp form `f.toCuspForm` (viewed via `toModularForm'` as a modular form
on `(Gamma1 N).map (mapGL ℝ)`).  The resulting `ℝ → ℂ` function maps
`t > 0` to `f` evaluated at `i · t ∈ ℍ`, and `t ≤ 0` to `0`.

This is the canonical choice of `F` in `Newform.MellinPairData` and the
classical input to the Mellin–Dirichlet correspondence
(Diamond–Shurman §5.9, Miyake §4.3.5). -/
noncomputable def Newform.imAxis {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) :
    ℝ → ℂ :=
  _root_.ModularForms.imAxis f.toCuspForm

/-- **Continuity of `Newform.imAxis f` on `Ioi 0` (T132 H1).** -/
lemma Newform.continuousOn_imAxis {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) :
    ContinuousOn (Newform.imAxis f) (Set.Ioi (0 : ℝ)) :=
  _root_.ModularForms.continuousOn_imAxis f.toCuspForm

/-- **Local integrability of `Newform.imAxis f` on `Ioi 0` (T132 H1).**

Direct `Newform.MellinPairData.hF_int` field candidate when
`F := Newform.imAxis f` is chosen as the canonical Mellin-side function. -/
lemma Newform.locallyIntegrableOn_imAxis {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) :
    MeasureTheory.LocallyIntegrableOn (Newform.imAxis f) (Set.Ioi (0 : ℝ)) :=
  _root_.ModularForms.locallyIntegrableOn_imAxis f.toCuspForm

/-- **Newform.MellinPairData constructor with `F := Newform.imAxis f` (T132 H1).**

Specialises `Newform.MellinPairData` to the **canonical** Mellin-side
function `F = Newform.imAxis f` (i.e., `t ↦ f(it)` for `t > 0` and `0`
otherwise), automatically discharging the `hF_int` (local integrability
on `Ioi 0`) field via `Newform.locallyIntegrableOn_imAxis`.

The remaining genuinely-analytic fields stay explicit:

* `G : ℝ → ℂ` — Atkin-Lehner / Fricke-twist Mellin-side function.
* `ε : ℂ` — root number.
* `hG_int` — Atkin-Lehner-side local integrability.
* `hk_pos` — weight positivity `0 < (k : ℝ)`.
* `hε_ne` — root-number non-vanishing.
* `h_feq` — functional involution `F (1/x) = ε · x^k · G x`.
* `hF_top`, `hG_top` — polynomial decay at `∞` (the cusp-form rapid-
  decay statement; classical Hecke 1936 input).
* `h_bridge` — Mellin–Dirichlet bridge
  `mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s`. -/
noncomputable def Newform.MellinPairData.ofImAxis
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (G : ℝ → ℂ) (ε : ℂ)
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hk_pos : 0 < (k : ℝ)) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      Newform.imAxis f (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x)
    (hF_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => Newform.imAxis f x - 0) (fun x : ℝ => x ^ r))
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r))
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

/-- **Newform.imAxis-side Mellin-pair data structure (T132 H1).**

Specialises `Newform.MellinPairData` to the canonical
`F := Newform.imAxis f`, dropping the auto-discharged `hF_int` field
(provided by `Newform.locallyIntegrableOn_imAxis`).

The remaining fields are exactly the genuinely-analytic Mellin-pair
obligations of the Hecke 1936 entire-continuation theorem
(Diamond–Shurman §5.9 / Miyake §4.3.5):

* `G : ℝ → ℂ`, `ε : ℂ` — Atkin-Lehner / Fricke-twist Mellin-side
  function and root number.
* `hG_int` — Atkin-Lehner-side local integrability.
* `hk_pos` — weight positivity `0 < (k : ℝ)`.
* `hε_ne` — root-number non-vanishing.
* `h_feq` — functional involution
  `(Newform.imAxis f) (1/x) = ε · x^k · G x`.
* `hF_top` — polynomial decay at `∞` of `Newform.imAxis f`
  (cusp-form-decay; the classical Hecke 1936 input).
* `hG_top` — polynomial decay at `∞` of `G`.
* `h_bridge` — Mellin–Dirichlet bridge
  `mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s`.

Each field of `ImAxisMellinData` is a named, individually-formalisable
analytic statement.  Consumers chain through
`Newform.MellinPairData.ofImAxisData →
Newform.HeckeFEData.ofImAxisData →
Newform.HeckeEntireExtension_of_ImAxisMellinData →
Newform.AnalyticContradiction`. -/
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
    (fun x : ℝ => Newform.imAxis f x - 0) (fun x : ℝ => x ^ r)
  /-- `G` has rapid polynomial decay at `∞`. -/
  hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
    (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r)
  /-- Mellin–Dirichlet bridge. -/
  h_bridge : ∀ {s : ℂ},
    LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s

/-- **Construct `Newform.MellinPairData f` from `Newform.ImAxisMellinData f`
(T132 H1).**

One-line bridge through `Newform.MellinPairData.ofImAxis`. -/
noncomputable def Newform.MellinPairData.ofImAxisData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.ImAxisMellinData f) : Newform.MellinPairData f :=
  Newform.MellinPairData.ofImAxis f data.G data.ε data.hG_int data.hk_pos
    data.hε_ne data.h_feq data.hF_top data.hG_top data.h_bridge

/-- **Construct `Newform.HeckeFEData f` from `Newform.ImAxisMellinData f`
(T132 H1).**

Chains through `Newform.MellinPairData.ofImAxisData` and
`Newform.HeckeFEData.ofMellinData`. -/
noncomputable def Newform.HeckeFEData.ofImAxisData
    {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k}
    (data : Newform.ImAxisMellinData f) : Newform.HeckeFEData f :=
  Newform.HeckeFEData.ofMellinData (Newform.MellinPairData.ofImAxisData data)

/-- **Global `HeckeEntireExtension` from per-newform `ImAxisMellinData`
(T132 H1).**

Reduces `Newform.HeckeEntireExtension` to per-newform structured
imAxis-side Mellin data.  This is the deepest H1 reduction in the
imAxis API: each newform's H1 obligation is now a named structure of
classical analytic fields, bottoming out at the genuinely-missing
Hecke 1936 fields (`hF_top`, `hG_top`, `h_feq`, `h_bridge`). -/
theorem Newform.HeckeEntireExtension_of_ImAxisMellinData
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k),
      Newform.ImAxisMellinData f) :
    Newform.HeckeEntireExtension :=
  Newform.HeckeEntireExtension_of_HeckeFEData
    (fun _N _ _k f => Newform.HeckeFEData.ofImAxisData (h f))

/-- **Newform-side exponential decay of the imAxis function (T132 H1
named hypothesis).**

The classical cusp-form-decay statement specialised to `Newform.imAxis f`:
there exists a positive rate `a` such that `Newform.imAxis f` decays at
rate `exp (-a · t)` as `t → ∞`.

For a Newform with q-expansion `f(τ) = ∑_{n≥1} aₙ q^n` (with `q = e^{2πiτ}`,
period `1`), the leading-term bound at `n = 1` gives exponential decay
with rate `2π`.  Formally, this is the `2π` decay-rate side of the
`hF_top` field of `Newform.ImAxisMellinData`.

We expose it as a **named predicate** isolating the genuine analytic
input of Hecke 1936 (Diamond–Shurman §5.9 / Miyake §4.3.5). -/
def Newform.HasImAxisExponentialDecay {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Prop :=
  _root_.ModularForms.HasImAxisExponentialDecay f.toCuspForm

/-- **Rapid polynomial decay of `Newform.imAxis f` from exponential decay
(T132 H1 reduction).**

Specialises `ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay`
to a `Newform`: the per-newform `hF_top` field of `ImAxisMellinData`
follows directly from the strictly-stronger but more elementary
exponential-decay hypothesis.

This is the substantive theorem-level reduction of the rapid-decay
obligation to the q-expansion-side exponential bound at the cusp `∞`. -/
theorem Newform.imAxis_rapidDecay_of_exponentialDecay
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (h : Newform.HasImAxisExponentialDecay f) :
    ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => Newform.imAxis f x - 0) (fun x : ℝ => x ^ r) :=
  _root_.ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay
    f.toCuspForm h

/-- **Newform-side `HasImAxisExponentialDecay` is automatic (T132 H1
substantive theorem).**

For every `Γ₁(N)` newform `f`, the imAxis-side exponential decay
hypothesis `Newform.HasImAxisExponentialDecay f` holds **unconditionally**.

The proof:

1. `(Gamma1 N).map (mapGL ℝ)` has strict period `1` (via
   `CongruenceSubgroup.strictPeriods_Gamma1`).
2. Mathlib's `CuspFormClass.exp_decay_atImInfty` gives `f.toCuspForm =O[atImInfty] (fun τ => exp (-2π · τ.im))` (rate `c = 2π / 1 = 2π`).
3. The bridge `ModularForms.hasImAxisExponentialDecay_of_strictPeriod`
   transports this to the imaginary-axis-side `HasImAxisExponentialDecay`
   predicate.

Composed with `Newform.imAxis_rapidDecay_of_exponentialDecay`, this
closes the cusp-form-decay obligation of `Newform.MellinPairData.hF_top`
for any newform on `Γ₁(N)`. -/
theorem Newform.hasImAxisExponentialDecay {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) : Newform.HasImAxisExponentialDecay f := by
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  exact _root_.ModularForms.hasImAxisExponentialDecay_of_strictPeriod
    f.toCuspForm (h := 1) one_pos h1_period

/-- **Newform.imAxis rapid polynomial decay (T132 H1 endpoint, automatic).**

Combines `Newform.hasImAxisExponentialDecay` with
`Newform.imAxis_rapidDecay_of_exponentialDecay` to give the
`hF_top`-shape rapid-decay statement unconditionally for any newform
on `Γ₁(N)`.  This **closes** the cusp-form-decay obligation of the
`Newform.MellinPairData.hF_top` field. -/
theorem Newform.imAxis_rapidDecay {N : ℕ} [NeZero N] {k : ℤ}
    (f : Newform N k) :
    ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => Newform.imAxis f x - 0) (fun x : ℝ => x ^ r) :=
  Newform.imAxis_rapidDecay_of_exponentialDecay f
    (Newform.hasImAxisExponentialDecay f)

/-- **Newform.ImAxisMellinData constructor from exponential-decay
hypothesis (T132 H1).**

Specialises `Newform.ImAxisMellinData` so that the `hF_top` rapid-decay
field is **automatically discharged** from the strictly-stronger
exponential-decay hypothesis `Newform.HasImAxisExponentialDecay f`
(via `Newform.imAxis_rapidDecay_of_exponentialDecay`).

Constructor inputs (matching `ImAxisMellinData` minus `hF_top`):

* `G : ℝ → ℂ`, `ε : ℂ`
* `hG_int`, `hk_pos`, `hε_ne`
* `h_feq` (functional equation)
* `hF_exp` — Newform.imAxis f exponential decay (the q-expansion input)
* `hG_top` (twist rapid decay — kept explicit since the twist is
  caller-provided)
* `h_bridge` (Mellin–Dirichlet)

The remaining `hF_top` polynomial-decay field is filled by
`Newform.imAxis_rapidDecay_of_exponentialDecay`. -/
noncomputable def Newform.ImAxisMellinData.ofExponentialDecay
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (G : ℝ → ℂ) (ε : ℂ)
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hk_pos : 0 < (k : ℝ)) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      (Newform.imAxis f) (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x)
    (hF_exp : Newform.HasImAxisExponentialDecay f)
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r))
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

/-- **Newform.ImAxisMellinData constructor with automatic exponential
decay (T132 H1 endpoint).**

Strongest H1 constructor: builds `Newform.ImAxisMellinData f` for any
newform `f : Newform N k` on `Γ₁(N)`, **automatically discharging both
the `hF_exp` exponential-decay AND the `hF_top` rapid-decay obligations**
via `Newform.hasImAxisExponentialDecay` (which uses Mathlib's
`CuspFormClass.exp_decay_atImInfty` + the strict-period-1 fact for
`(Gamma1 N).map (mapGL ℝ)`).

The remaining caller-supplied fields capture the genuinely-classical
analytic obligations not yet in the local repo:

* `G : ℝ → ℂ`, `ε : ℂ` — Atkin-Lehner / Fricke-twist Mellin function
  and root number.
* `hG_int`, `hk_pos`, `hε_ne` — local integrability, weight positivity,
  root-number non-vanishing.
* `h_feq` — functional involution `(Newform.imAxis f) (1/x) = ε · x^k · G x`.
* `hG_top` — rapid decay of the twist (caller-supplied because the twist
  is caller-determined).
* `h_bridge` — Mellin–Dirichlet bridge.

The `hF_top` field is **closed** for any `Γ₁(N)` newform: the
cusp-form-side rapid-decay obligation no longer requires a caller-
supplied hypothesis. -/
noncomputable def Newform.ImAxisMellinData.ofData_auto
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (G : ℝ → ℂ) (ε : ℂ)
    (hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi 0))
    (hk_pos : 0 < (k : ℝ)) (hε_ne : ε ≠ 0)
    (h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      (Newform.imAxis f) (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x)
    (hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r))
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s) :
    Newform.ImAxisMellinData f :=
  Newform.ImAxisMellinData.ofExponentialDecay f G ε hG_int hk_pos hε_ne
    h_feq (Newform.hasImAxisExponentialDecay f) hG_top h_bridge

/-- **`Γ₁(N)`-cusp-form-side `HasImAxisExponentialDecay` (T132 H1 helper).**

Specialises `ModularForms.hasImAxisExponentialDecay_of_strictPeriod` to
`Γ₁(N)` (strict period `1`) for any cusp form `g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k`.

Used to discharge the Atkin-Lehner / Fricke twist exponential-decay
obligation when the twist is supplied as a CuspForm-valued object on
the same level. -/
theorem Newform.cuspForm_Gamma1_hasImAxisExponentialDecay {N : ℕ} [NeZero N]
    {k : ℤ} (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    _root_.ModularForms.HasImAxisExponentialDecay g := by
  have h1_period : (1 : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    rw [show (Gamma1 N).map (mapGL ℝ) = (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) from rfl,
      CongruenceSubgroup.strictPeriods_Gamma1]
    exact ⟨1, by simp⟩
  exact _root_.ModularForms.hasImAxisExponentialDecay_of_strictPeriod
    g (h := 1) one_pos h1_period

/-- **Newform.ImAxisMellinData constructor with CuspForm-supplied twist
(T132 H1 endpoint with twist).**

Strongest H1 constructor that ALSO automatically discharges both the
`hG_int` (twist local integrability) and `hG_top` (twist rapid decay)
fields: takes the Atkin-Lehner / Fricke twist as a **CuspForm-valued
object** `g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k` and uses the
generic imAxis pipeline (continuity ⇒ local integrability;
strictPeriod₁ ⇒ exponential decay ⇒ rapid decay) to fill the entire
Atkin-Lehner side of `ImAxisMellinData`.

Caller-supplied fields collapse to the **genuinely-classical**
analytic content of the Atkin-Lehner functional equation:

* `ε : ℂ` — root number.
* `hk_pos`, `hε_ne` — weight positivity, root-number non-vanishing
  (mechanical for any `k > 0` and unimodular `ε`).
* `h_feq` — functional involution
  `(Newform.imAxis f) (1/x) = ε · x^k · (ModularForms.imAxis g) x`.
  This is the classical Atkin-Lehner / Fricke functional equation,
  the genuinely-missing analytic input.
* `h_bridge` — Mellin–Dirichlet bridge.

The `F`-side fields (`hF_int`, `hF_top`, `hF_exp`) and the entire
`G`-side (`hG_int`, `hG_top`) are now mechanically discharged for
`Γ₁(N)` newforms with CuspForm-supplied twists. -/
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

/-! ### Fricke matrix and slash formula (T132 H1)

The Atkin-Lehner / Fricke matrix `W_N := !![0,-1;N,0]` (as an element
of `GL (Fin 2) ℝ` with determinant `N > 0`).  Computes the imaginary-
axis slash formula directly via Mathlib's `slash_def`. -/

/-- **Fricke matrix `W_N := !![0, -1; N, 0]` for level `N` (T132 H1).** -/
noncomputable def Newform.frickeMatrix (N : ℕ) [NeZero N] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℝ), 0]
    (by
      have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      simp [Matrix.det_fin_two, hN])

/-- **Coercion of the Fricke matrix to a `Matrix`.** -/
@[simp]
lemma Newform.frickeMatrix_coe (N : ℕ) [NeZero N] :
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1; (N : ℝ), 0] := by
  simp [Newform.frickeMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- **Determinant of the Fricke matrix is `N`.** -/
lemma Newform.frickeMatrix_det (N : ℕ) [NeZero N] :
    (Newform.frickeMatrix N).det.val = (N : ℝ) := by
  show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det = (N : ℝ)
  simp [Newform.frickeMatrix_coe, Matrix.det_fin_two_of]

/-- **Determinant of the Fricke matrix is positive.** -/
lemma Newform.frickeMatrix_det_pos (N : ℕ) [NeZero N] :
    0 < (Newform.frickeMatrix N).det.val := by
  rw [Newform.frickeMatrix_det]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

/-- **`σ` of the Fricke matrix is the identity (since det > 0).** -/
lemma Newform.frickeMatrix_σ (N : ℕ) [NeZero N] :
    UpperHalfPlane.σ (Newform.frickeMatrix N) = RingHom.id ℂ := by
  unfold UpperHalfPlane.σ
  rw [if_pos (Newform.frickeMatrix_det_pos N)]

/-- **Numerator of the Fricke matrix at `τ`: `num W_N τ = -1`.** -/
@[simp]
lemma Newform.frickeMatrix_num (N : ℕ) [NeZero N] (τ : ℂ) :
    UpperHalfPlane.num (Newform.frickeMatrix N) τ = -1 := by
  show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 *
      τ + ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) 0 1 = -1
  simp [Newform.frickeMatrix_coe]

/-- **Denominator of the Fricke matrix at `τ`: `denom W_N τ = N · τ`.** -/
@[simp]
lemma Newform.frickeMatrix_denom (N : ℕ) [NeZero N] (τ : ℂ) :
    UpperHalfPlane.denom (Newform.frickeMatrix N) τ = (N : ℂ) * τ := by
  show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 *
      τ + ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) 1 1 = (N : ℂ) * τ
  simp [Newform.frickeMatrix_coe]

/-- **Möbius action of the Fricke matrix on `ℍ`: `W_N • τ = -1/(N · τ)`.** -/
lemma Newform.frickeMatrix_smul (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    ((Newform.frickeMatrix N • τ : UpperHalfPlane) : ℂ) =
      -1 / ((N : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (Newform.frickeMatrix_det_pos N),
    Newform.frickeMatrix_num, Newform.frickeMatrix_denom]

/-- **Fricke matrix involution identity: `W_N · W_N = -N · I` at the
matrix level (T141 concrete Atkin-Lehner leg).**

The Atkin-Lehner / Fricke matrix `W_N := [[0, -1], [N, 0]]` satisfies the
involution identity `W_N · W_N = -N · I` at the underlying matrix level.
Direct matrix computation:
```
W_N · W_N = [[0,-1],[N,0]] · [[0,-1],[N,0]]
          = [[0·0 + (-1)·N,  0·(-1) + (-1)·0],
             [N·0 + 0·N,     N·(-1) + 0·0    ]]
          = [[-N, 0], [0, -N]]
          = (-N) · I
```

This is the **core arithmetic identity** underlying the Atkin-Lehner
involution structure: dividing by `-N` (well-defined since `N > 0`) makes
`W_N / N` an order-2 element of `GL₂(ℝ)`, equivalently `(W_N)² = -N · I` says
`W_N` itself is an order-2-up-to-scalar element. The downstream cusp-form
operator `f ↦ f ∣[k] W_N` therefore satisfies an involution identity modulo
the explicit Fricke scalar `(-N)^{1-k}` (or `N^{k}`-style, depending on
slash-action normalisation).

**Use case (T141 / SMO).**  Combined with the period-1 Fricke slash formula
`Newform.frickeMatrix_slash_apply`, this identity lets the Atkin-Lehner
involution structure on cusp forms unfold cleanly: `(f ∣[k] W_N) ∣[k] W_N
= |det W_N|^{k-1} · σ ∘ σ · (denom · ...)^{−2k} · f`, which after using
`σ(W_N) = id` and `det W_N = N` reduces to a pure scalar multiple of `f`.
This in turn supplies the **inverse/involution property** of the
Fricke/Atkin-Lehner cusp-form operator, the second leg of the bad-prime
Petersson-adjoint package. -/
lemma Newform.frickeMatrix_sq_matrix (N : ℕ) [NeZero N] :
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (-(N : ℝ)) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rw [Newform.frickeMatrix_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Fricke matrix involution at the GL level: `W_N * W_N = (-N) • 1`.**

Lifts `Newform.frickeMatrix_sq_matrix` from underlying matrices to the
`GL (Fin 2) ℝ` group level, where the right-hand side is the GL element
corresponding to scalar multiplication by `(-N : ℝ)` (well-defined since
`N > 0` makes `-N ≠ 0`).

The product `W_N * W_N` in `GL (Fin 2) ℝ` has underlying matrix
`-N · I`, which is the identity element of `GL (Fin 2) ℝ` scaled by `-N`.
At the slash-action level, `(f ∣[k] W_N) ∣[k] W_N = (-N)^{?} · f` with the
exponent dictated by the slash convention; this is the route to the
inverse/involution property of the Fricke cusp-form operator. -/
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

/-- **Integer Fricke conjugate of a `Γ₁(N)` element (T141 conjugation leg).**

For `γ = !![a, b; c, d] : SL(2, ℤ)` belonging to `Γ₁(N)` (so `N ∣ c`), the
**Fricke conjugate matrix** is
```
δ = !![d, -(c / N); -(N : ℤ) * b, a]
```
(integer-valued thanks to `N ∣ c`). At the matrix level it satisfies
`W_N · γ = δ · W_N`, the **conjugation/normalisation identity** for the
Atkin-Lehner / Fricke matrix on `Γ₁(N)`. The downstream consequences
(`δ ∈ SL(2, ℤ)` via `det δ = 1`; `δ ∈ Γ₁(N)`; the GL-level matrix identity)
are landed below. -/
def Newform.frickeConjMat (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  !![γ 1 1, -(γ 1 0 / (N : ℤ)); -(N : ℤ) * γ 0 1, γ 0 0]

/-- **Det of `Newform.frickeConjMat N γ` is `1` when `γ ∈ Γ₁(N)`.**

Computation: `det δ = γ 1 1 · γ 0 0 - (-(γ 1 0 / N)) · (-(N · γ 0 1))
= γ 0 0 · γ 1 1 - (γ 1 0 / N · N) · γ 0 1 = γ 0 0 · γ 1 1 - γ 1 0 · γ 0 1
= det γ = 1`, using `(γ 1 0 / N) · N = γ 1 0` (which holds because
`N ∣ γ 1 0` from `γ ∈ Γ₁(N)`). -/
lemma Newform.frickeConjMat_det (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) : (Newform.frickeConjMat N γ).det = 1 := by
  have hN_dvd : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma1_mem N γ).mp hγN).2.2
  have h_div : γ 1 0 / (N : ℤ) * (N : ℤ) = γ 1 0 := Int.ediv_mul_cancel hN_dvd
  have h_det_γ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hγ_det : γ.val.det = 1 := γ.2
    rw [Matrix.det_fin_two] at hγ_det
    show γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1
    convert hγ_det using 1
  rw [Newform.frickeConjMat, Matrix.det_fin_two_of]
  linear_combination h_det_γ - (γ 0 1 : ℤ) * h_div

/-- **Fricke conjugate as an `SL(2, ℤ)` element (T141 conjugation leg).**

Lifts `Newform.frickeConjMat N γ` to `SL(2, ℤ)` via the `det = 1` proof,
when `γ ∈ Γ₁(N)`. -/
noncomputable def Newform.frickeConj (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) : SL(2, ℤ) :=
  ⟨Newform.frickeConjMat N γ, Newform.frickeConjMat_det N γ hγN⟩

/-- **`Newform.frickeConj N γ ∈ Γ₁(N)` when `γ ∈ Γ₁(N)`.**

Direct case-by-case verification of the three `Gamma1_mem` conditions:
* `(δ 0 0 : ZMod N) = (γ 1 1 : ZMod N) = 1` from `γ ∈ Γ₁(N)`.
* `(δ 1 1 : ZMod N) = (γ 0 0 : ZMod N) = 1` from `γ ∈ Γ₁(N)`.
* `(δ 1 0 : ZMod N) = (-(N : ℤ) * γ 0 1 : ZMod N) = 0` since `N ≡ 0` mod `N`. -/
lemma Newform.frickeConj_mem_Gamma1 (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) :
    Newform.frickeConj N γ hγN ∈ Gamma1 N := by
  have hγ := (Gamma1_mem N γ).mp hγN
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · -- δ 0 0 = γ 1 1, mod N = 1.
    show ((Newform.frickeConjMat N γ) 0 0 : ZMod N) = 1
    simp only [Newform.frickeConjMat, Matrix.cons_val_zero, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    exact hγ.2.1
  · -- δ 1 1 = γ 0 0, mod N = 1.
    show ((Newform.frickeConjMat N γ) 1 1 : ZMod N) = 1
    simp only [Newform.frickeConjMat, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
    exact hγ.1
  · -- δ 1 0 = -(N : ℤ) * γ 0 1, mod N = 0.
    show ((Newform.frickeConjMat N γ) 1 0 : ZMod N) = 0
    simp only [Newform.frickeConjMat, Matrix.cons_val_zero, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.of_apply]
    push_cast
    simp

/-- **T182 involution property of `Newform.frickeConj` on `Γ₁(N)`.**

For any `γ ∈ Γ₁(N)`, applying `Newform.frickeConj` twice (using
`frickeConj_mem_Gamma1` to lift the second application) returns `γ`.

Direct matrix computation:
* If `γ = !![a, b; c, d]` with `c = N · k`, then `frickeConjMat N γ =
  !![d, -k; -N·b, a]` and applying `frickeConjMat` again gives back
  `!![a, b; N·k, d] = γ`.

This is the **first ingredient** for the joint `(q, b)`-bijection witnessing
the bad-prime Atkin-Lehner reindex (T181 residual `qBBijection`). -/
lemma Newform.frickeConj_frickeConj (N : ℕ) [NeZero N] (γ : SL(2, ℤ))
    (hγN : γ ∈ Gamma1 N) :
    Newform.frickeConj N (Newform.frickeConj N γ hγN)
        (Newform.frickeConj_mem_Gamma1 N γ hγN) = γ := by
  apply Subtype.ext
  show Newform.frickeConjMat N (Newform.frickeConj N γ hγN) = γ.val
  have hN_pos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast (NeZero.pos N)
  have hN_ne : (N : ℤ) ≠ 0 := hN_pos.ne'
  have hN_dvd : (N : ℤ) ∣ γ.val 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma1_mem N γ).mp hγN).2.2
  have h_div : γ.val 1 0 / (N : ℤ) * (N : ℤ) = γ.val 1 0 :=
    Int.ediv_mul_cancel hN_dvd
  ext i j
  simp only [Newform.frickeConjMat, Newform.frickeConj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  fin_cases i
  · fin_cases j
    · -- (0, 0): output of inner is γ 1 1, frickeConjMat takes its 1 1 → γ 0 0
      show γ.val 0 0 = γ.val 0 0
      rfl
    · -- (0, 1): -((-N·γ 0 1) / N) = γ 0 1
      show -(-(N : ℤ) * γ.val 0 1 / (N : ℤ)) = γ.val 0 1
      rw [Int.neg_mul, Int.neg_ediv_of_dvd ⟨γ.val 0 1, rfl⟩,
          Int.mul_ediv_cancel_left _ hN_ne]
      ring
  · fin_cases j
    · -- (1, 0): -N·-(γ 1 0 / N) = γ 1 0
      show -(N : ℤ) * -(γ.val 1 0 / (N : ℤ)) = γ.val 1 0
      have : (N : ℤ) * (γ.val 1 0 / (N : ℤ)) = γ.val 1 0 := by
        rw [mul_comm]; exact h_div
      linarith
    · -- (1, 1): output is γ 0 0, frickeConjMat takes its 0 0 → γ 1 1
      show γ.val 1 1 = γ.val 1 1
      rfl

/-- **T182 `Equiv` on `Gamma1 N` induced by `frickeConj`.**

The map `γ ↦ Newform.frickeConj N γ.val γ.property` defines an involution
on the subtype `{γ : SL(2, ℤ) // γ ∈ Gamma1 N}`. Bundled as `Equiv`
(self-inverse via `frickeConj_frickeConj`).

Used in the joint `(q, b)`-bijection construction for T182's qBBijection
target. -/
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

/-- **Fricke conjugation/normalisation identity at the integer-matrix level
(T141 main conjugation theorem).**

For `γ = !![a, b; c, d] ∈ Γ₁(N)` and the Fricke conjugate matrix
`δ = Newform.frickeConjMat N γ = !![d, -(c/N); -N·b, a]`, the matrix
identity
```
W_N_int · γ.val = δ · W_N_int
```
holds at the level of integer matrices, where `W_N_int := !![0, -1; (N : ℤ), 0]`
is the Fricke matrix at the integer level.

Direct matrix calculation:
```
W_N · γ = !![0, -1; N, 0] · !![a, b; c, d] = !![-c, -d; N·a, N·b]
δ · W_N = !![d, -(c/N); -N·b, a] · !![0, -1; N, 0]
       = !![-(c/N)·N, -d; a·N, N·b] = !![-c, -d; N·a, N·b]   (using N ∣ c).
```

This is the **group-theoretic input** showing `W_N` normalises `Γ₁(N)`
up to the explicit reindexing `γ ↦ δ` (Diamond–Shurman §5.5 / Miyake §4.6.5).
The GL ℝ-level matrix identity follows by applying `Matrix.map (algebraMap ℤ ℝ)`
to both sides; landed separately when the cusp-form Fricke operator track
needs the ℝ-level identity. -/
lemma Newform.frickeMat_int_mul_eq_frickeConjMat_mul_frickeMat_int
    (N : ℕ) [NeZero N] (γ : SL(2, ℤ)) (hγN : γ ∈ Gamma1 N) :
    (!![0, -1; (N : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
      Newform.frickeConjMat N γ * !![0, -1; (N : ℤ), 0] := by
  have hN_dvd : (N : ℤ) ∣ γ 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma1_mem N γ).mp hγN).2.2
  have h_div : γ 1 0 / (N : ℤ) * (N : ℤ) = γ 1 0 := Int.ediv_mul_cancel hN_dvd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Newform.frickeConjMat, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals try ring
  all_goals exact h_div.symm

/-- **Coercion of `!![0, -1; (N : ℤ), 0]` to `Matrix _ ℝ` via `Matrix.map`.**

The integer Fricke matrix `!![0, -1; (N : ℤ), 0]`, mapped through `algebraMap ℤ ℝ`,
equals the real Fricke matrix `!![0, -1; (N : ℝ), 0]` (the underlying matrix of
`Newform.frickeMatrix N`). -/
lemma Newform.frickeMatInt_map_algebraMap (N : ℕ) :
    (!![0, -1; (N : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) =
      !![0, -1; (N : ℝ), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Fricke matrix conjugation/normalisation at the GL ℝ level (T142 main theorem).**

Lifts T141's integer-matrix bridge `Newform.frickeMat_int_mul_eq_frickeConjMat_mul_frickeMat_int`
through `Matrix.map (algebraMap ℤ ℝ)` / `mapGL ℝ` to obtain the conjugation identity in
`GL (Fin 2) ℝ`:
```
W_N * mapGL ℝ γ = mapGL ℝ δ * W_N
```
where `W_N := Newform.frickeMatrix N`, `γ ∈ Γ₁(N)`, and
`δ := Newform.frickeConj N γ hγN ∈ Γ₁(N)` is the integer Fricke conjugate of T141.

This is the **slash-action input** for showing that `(F ∣[k] W_N)` is `Γ₁(N)`-invariant
whenever `F` is `Γ₁(N)`-invariant; see `Newform.slash_frickeMatrix_slash_mapGL`. -/
theorem Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix
    {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγN : γ ∈ Gamma1 N) :
    Newform.frickeMatrix N * mapGL ℝ γ =
      mapGL ℝ (Newform.frickeConj N γ hγN) * Newform.frickeMatrix N := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
    Newform.frickeMatrix_coe, Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  -- Goal: !![0, -1; (N : ℝ), 0] * (γ.val).map (algebraMap ℤ ℝ) =
  --   (Newform.frickeConj N γ hγN).val.map (algebraMap ℤ ℝ) * !![0, -1; (N : ℝ), 0]
  have h_int : (!![0, -1; (N : ℤ), 0] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
      Newform.frickeConjMat N γ * !![0, -1; (N : ℤ), 0] :=
    Newform.frickeMat_int_mul_eq_frickeConjMat_mul_frickeMat_int N γ hγN
  have h_real :
      (!![0, -1; (N : ℤ), 0] * γ.val).map (algebraMap ℤ ℝ) =
        (Newform.frickeConjMat N γ * !![0, -1; (N : ℤ), 0]).map (algebraMap ℤ ℝ) :=
    congrArg (fun M : Matrix (Fin 2) (Fin 2) ℤ => M.map (algebraMap ℤ ℝ)) h_int
  rw [Matrix.map_mul, Matrix.map_mul, Newform.frickeMatInt_map_algebraMap] at h_real
  -- (Newform.frickeConj N γ hγN).val = Newform.frickeConjMat N γ holds definitionally.
  exact h_real

/-- **Fricke slash normalises the `Γ₁(N)` action (T142 slash leg).**

For any `Γ₁(N)`-slash-invariant function `F : UpperHalfPlane → ℂ` (e.g. modular or cusp form
of level `(Gamma1 N).map (mapGL ℝ)`), and any `γ ∈ Γ₁(N)`:
```
(F ∣[k] W_N) ∣[k] (mapGL ℝ γ) = F ∣[k] W_N
```
i.e. slashing `F ∣[k] W_N` by another element of `Γ₁(N)` gives back `F ∣[k] W_N`.
This is the **slash-level normalisation** that follows from the GL ℝ identity
`Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix` together with
the `Γ₁(N)`-invariance of `F`.

Proof outline:
```
(F ∣[k] W_N) ∣[k] (mapGL γ) = F ∣[k] (W_N * mapGL γ)              -- slash_mul
                            = F ∣[k] (mapGL δ * W_N)              -- T142 GL identity
                            = (F ∣[k] mapGL δ) ∣[k] W_N            -- slash_mul
                            = F ∣[k] W_N                           -- slash invariance, δ ∈ Γ₁(N)
```
where `δ := Newform.frickeConj N γ hγN ∈ Γ₁(N)`.

Consequence: when packaged via the modular/cusp form Fricke operator, `F ∣[k] W_N`
itself is `Γ₁(N)`-invariant — i.e. `W_N` normalises the `Γ₁(N)` slash action. -/
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

/-- **Fricke slash operator on slash-invariant forms (T142 first operator).**

Given a `Γ₁(N)`-slash-invariant form `f`, define `frickeSlashSIF f := f ∣[k] W_N`,
packaged again as a `Γ₁(N)`-slash-invariant form. The slash invariance of the result
follows from `Newform.slash_frickeMatrix_slash_mapGL_of_mem_Gamma1`.

This is the **slash-action level** Fricke operator. Promoting to a `ModularForm`
or `CuspForm`-level operator additionally requires holomorphy / boundedness-at-cusps
preservation under slashing by `W_N`, which is left as a downstream API gap. -/
noncomputable def Newform.frickeSlashSIF
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k) :
    SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N
  slash_action_eq' g hg := by
    obtain ⟨γ, hγ, rfl⟩ := hg
    exact Newform.slash_frickeMatrix_slash_mapGL_of_mem_Gamma1 f γ hγ

/-- **Underlying function of `Newform.frickeSlashSIF`.** -/
@[simp]
lemma Newform.frickeSlashSIF_coe
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : SlashInvariantForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSlashSIF f : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N :=
  rfl

/-- **Fricke slash as a `ℂ`-linear endomorphism on slash-invariant forms (T142
linear-operator leg).**

Packages `Newform.frickeSlashSIF` as a `→ₗ[ℂ]` map. Linearity over `ℂ` follows
from `SlashAction.add_slash` (additivity) and `ModularForm.smul_slash` together
with `Newform.frickeMatrix_σ` (so that `σ W_N c = c` and the scalar action passes
through cleanly). -/
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

/-- **Rational Fricke matrix `W_N` over ℚ (T143 cusp-transport bridge).**

The Atkin-Lehner / Fricke matrix `!![0, -1; (N : ℚ), 0]` viewed as an element of
`GL (Fin 2) ℚ`. Determinant is `N ≠ 0` since `[NeZero N]`. Used to express
`Newform.frickeMatrix N : GL (Fin 2) ℝ` as `glMap` of a rational matrix, which
in turn supplies the rational cusp-transport lemma. -/
noncomputable def Newform.frickeMatrixRat (N : ℕ) [NeZero N] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, -1; (N : ℚ), 0]
    (by
      have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      simp [Matrix.det_fin_two, hN])

/-- **`Newform.frickeMatrix N` is the `glMap`-image of `Newform.frickeMatrixRat N`.** -/
lemma Newform.glMap_frickeMatrixRat (N : ℕ) [NeZero N] :
    glMap (Newform.frickeMatrixRat N) = Newform.frickeMatrix N := by
  apply Units.ext
  show (glMap (Newform.frickeMatrixRat N) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Newform.frickeMatrix N : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Newform.frickeMatrix_coe]
  show (Newform.frickeMatrixRat N : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
    !![0, -1; (N : ℝ), 0]
  simp [Newform.frickeMatrixRat, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Fricke cusp transport for `Γ₁(N)` (T143 cusp-transport leg).**

The Fricke matrix `W_N := Newform.frickeMatrix N : GL (Fin 2) ℝ` maps cusps of
`(Gamma1 N).map (mapGL ℝ)` to cusps of the same group. Reduces to SL(2, ℤ)-cusps
via arithmeticity (`Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z`); the SL(2, ℤ)-cusp
characterization (`isCusp_SL2Z_iff`) reduces further to ℙ¹(ℚ); finally the
rational Fricke matrix `Newform.frickeMatrixRat N : GL (Fin 2) ℚ` permutes ℙ¹(ℚ)
since GL₂(ℚ) acts on `OnePoint ℚ`, and `OnePoint.map_smul` transports this action
through `algebraMap ℚ ℝ`. -/
lemma Newform.frickeMatrix_smul_isCusp_Gamma1
    {N : ℕ} [NeZero N] {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (Newform.frickeMatrix N • c) ((Gamma1 N).map (mapGL ℝ)) := by
  rw [← Newform.glMap_frickeMatrixRat]
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨q, rfl⟩ := hc
  rw [show glMap (Newform.frickeMatrixRat N) •
        OnePoint.map (Rat.cast : ℚ → ℝ) q =
      OnePoint.map (Rat.cast : ℚ → ℝ) (Newform.frickeMatrixRat N • q)
      from (OnePoint.map_smul (algebraMap ℚ ℝ) (Newform.frickeMatrixRat N) q).symm]
  exact ⟨_, rfl⟩

/-- **Fricke slash on `ModularForm` (T143 ModularForm operator).**

Slash by `W_N := Newform.frickeMatrix N` lifts to a `ℂ`-linear endomorphism of
`ModularForm ((Gamma1 N).map (mapGL ℝ)) k`:
* The `SlashInvariantForm` part comes from `Newform.frickeSlashSIFLin` (T142).
* Holomorphy is preserved by `MDifferentiable.slash` (Mathlib).
* Boundedness at cusps is preserved by `OnePoint.IsBoundedAt.smul_iff`
  combined with the cusp-transport lemma `Newform.frickeMatrix_smul_isCusp_Gamma1`.

This is the **bona-fide ModularForm-level Fricke operator** at level `Γ₁(N)`. -/
noncomputable def Newform.frickeSlashModularForm
    {N : ℕ} [NeZero N] {k : ℤ} :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
        Newform.frickeSlashSIF f.toSlashInvariantForm
      holo' := f.holo'.slash k (Newform.frickeMatrix N)
      bdd_at_cusps' := fun {c} hc =>
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

/-- **Underlying function of the ModularForm Fricke operator.** -/
@[simp]
lemma Newform.frickeSlashModularForm_coe
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSlashModularForm f : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N :=
  rfl

/-- **Fricke slash on `CuspForm` (T143 CuspForm operator).**

Same construction as `Newform.frickeSlashModularForm` but for cusp forms,
using `OnePoint.IsZeroAt.smul_iff` and the same cusp transport lemma. -/
noncomputable def Newform.frickeSlashCuspForm
    {N : ℕ} [NeZero N] {k : ℤ} :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k →ₗ[ℂ]
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f :=
    { toSlashInvariantForm :=
        Newform.frickeSlashSIF f.toSlashInvariantForm
      holo' := f.holo'.slash k (Newform.frickeMatrix N)
      zero_at_cusps' := fun {c} hc =>
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

/-- **Underlying function of the CuspForm Fricke operator.** -/
@[simp]
lemma Newform.frickeSlashCuspForm_coe
    {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSlashCuspForm f : UpperHalfPlane → ℂ) =
      (f : UpperHalfPlane → ℂ) ∣[k] Newform.frickeMatrix N :=
  rfl

/-- **Imaginary-axis slash formula for the Fricke matrix (T132 H1).**

Exact Lean-checked formula derived from `slash_def`:
`(f ∣[k] W_N) τ = f (W_N • τ) · |N|^{k-1} · (N · τ)^{-k}`
(using `σ = id` and `denom W_N τ = N · τ`).  The `|N|` resolves to `N`
since `N > 0`. -/
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
  -- |det W_N| = N (since N > 0).
  rw [Newform.frickeMatrix_det, abs_of_pos]
  exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

/-! ### Square / involution-up-to-scalar of the Fricke operator (T144) -/

/-- **Möbius action of `W_N · W_N` on `ℍ` is trivial (T144 helper).**

`(W_N * W_N) • τ = τ` because the underlying matrix `(-N) • 1` is a (nonzero) scalar
matrix and scalar matrices act trivially via Möbius transformation. -/
private lemma frickeMatrix_sq_smul {N : ℕ} [NeZero N] (τ : UpperHalfPlane) :
    (Newform.frickeMatrix N * Newform.frickeMatrix N) • τ = τ := by
  apply UpperHalfPlane.ext
  rw [mul_smul, Newform.frickeMatrix_smul, Newform.frickeMatrix_smul]
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  field_simp

/-- **Scalar appearing when slashing twice by the Fricke matrix `W_N` (T144).**

In the slash convention used throughout (Mathlib's GL₂(ℝ) slash with
`σ`, `|det|^{k-1}`, and `denom^{-k}`), slashing by `W_N` twice equals slashing by
the scalar matrix `W_N · W_N = (-N) • 1`, which produces this overall scalar:
```
frickeSquareScalar N k := (-1 : ℂ)^k * (N : ℂ)^(k - 2)
```
This is the involution-up-to-scalar coefficient for the Fricke operator. -/
def Newform.frickeSquareScalar (N : ℕ) (k : ℤ) : ℂ :=
  (-1 : ℂ) ^ k * (N : ℂ) ^ (k - 2)

/-- **Function-level Fricke double-slash identity (T144 main theorem).**

For any `f : UpperHalfPlane → ℂ`, slashing twice by `W_N := Newform.frickeMatrix N` gives back
`f` scaled by `Newform.frickeSquareScalar N k`. Proof: two applications of
`Newform.frickeMatrix_slash_apply`, using `Newform.frickeMatrix_smul` (so that
`W_N • τ` is `-1/(Nτ)`) and the trivial-Möbius helper `frickeMatrix_sq_smul`
(so that `W_N • W_N • τ = τ`). The τ-dependent factors collapse via `mul_zpow`. -/
lemma Newform.slash_frickeMatrix_frickeMatrix
    {N : ℕ} [NeZero N] {k : ℤ} (f : UpperHalfPlane → ℂ) :
    ((f ∣[k] Newform.frickeMatrix N) ∣[k] Newform.frickeMatrix N) =
      Newform.frickeSquareScalar N k • f := by
  funext τ
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hNτ_ne : (N : ℂ) * (τ : ℂ) ≠ 0 := mul_ne_zero hN_ne hτ_ne
  rw [show ((f ∣[k] Newform.frickeMatrix N) ∣[k] Newform.frickeMatrix N) τ =
      ((f ∣[k] Newform.frickeMatrix N) (Newform.frickeMatrix N • τ)) *
        ((N : ℝ) : ℂ) ^ (k - 1) * ((N : ℂ) * (τ : ℂ)) ^ (-k) from
      Newform.frickeMatrix_slash_apply (f ∣[k] Newform.frickeMatrix N) τ]
  rw [Newform.frickeMatrix_slash_apply f (Newform.frickeMatrix N • τ)]
  rw [show Newform.frickeMatrix N • Newform.frickeMatrix N • τ = τ by
      rw [← mul_smul]; exact frickeMatrix_sq_smul τ]
  rw [Newform.frickeMatrix_smul]
  rw [show ((N : ℂ) * (-1 / ((N : ℂ) * (τ : ℂ)))) = -1 / (τ : ℂ) by field_simp]
  rw [show ((N : ℝ) : ℂ) = (N : ℂ) by push_cast; rfl]
  -- Goal: f τ * (N:ℂ)^(k-1) * (-1/τ)^(-k) * (N:ℂ)^(k-1) * (Nτ)^(-k) = scalar • f τ
  -- Reorder via ring to group the two zpow pairs:
  rw [show f τ * (N : ℂ) ^ (k - 1) * (-1 / (τ : ℂ)) ^ (-k) *
        (N : ℂ) ^ (k - 1) * ((N : ℂ) * (τ : ℂ)) ^ (-k) =
      f τ * ((N : ℂ) ^ (k - 1) * (N : ℂ) ^ (k - 1)) *
        ((-1 / (τ : ℂ)) ^ (-k) * ((N : ℂ) * (τ : ℂ)) ^ (-k)) by ring]
  -- Combine the τ-factors via mul_zpow.
  rw [show (-1 / (τ : ℂ)) ^ (-k) * ((N : ℂ) * (τ : ℂ)) ^ (-k) =
      (-(N : ℂ)) ^ (-k) by
    rw [← mul_zpow]
    congr 1
    field_simp]
  -- Combine the N-factors via zpow_add.
  rw [show (N : ℂ) ^ (k - 1) * (N : ℂ) ^ (k - 1) = (N : ℂ) ^ (2 * (k - 1)) by
    rw [← zpow_add₀ hN_ne]; ring_nf]
  -- Expand (-N)^(-k) = (-1)^k * N^(-k).
  rw [show (-(N : ℂ)) ^ (-k) = (-1 : ℂ) ^ k * (N : ℂ) ^ (-k) by
    rw [show (-(N : ℂ)) = (-1 : ℂ) * (N : ℂ) by ring, mul_zpow]
    rw [show (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k by
      rw [zpow_neg, show ((-1 : ℂ) ^ k)⁻¹ = ((-1 : ℂ)⁻¹) ^ k from (inv_zpow _ _).symm,
          show ((-1 : ℂ)⁻¹ : ℂ) = -1 by norm_num]]]
  -- Combine N^(2(k-1)) * N^(-k) = N^(k-2).
  rw [Pi.smul_apply, smul_eq_mul, Newform.frickeSquareScalar]
  rw [show f τ * (N : ℂ) ^ (2 * (k - 1)) * ((-1 : ℂ) ^ k * (N : ℂ) ^ (-k)) =
      (-1 : ℂ) ^ k * ((N : ℂ) ^ (2 * (k - 1)) * (N : ℂ) ^ (-k)) * f τ by ring]
  rw [show (N : ℂ) ^ (2 * (k - 1)) * (N : ℂ) ^ (-k) = (N : ℂ) ^ (k - 2) by
    rw [← zpow_add₀ hN_ne]; ring_nf]

/-- **Operator-level Fricke square (CuspForm version, T144 main operator).**

`Newform.frickeSlashCuspForm` composed with itself acts as scalar multiplication by
`Newform.frickeSquareScalar N k` on every cusp form. Pointwise/`apply` form. -/
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

/-- **Operator-level Fricke square (ModularForm version, T144).** -/
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

/-- **`LinearMap`-level Fricke square (CuspForm version).** -/
lemma Newform.frickeSlashCuspForm_comp_self {N : ℕ} [NeZero N] {k : ℤ} :
    (Newform.frickeSlashCuspForm (N := N) (k := k)).comp
        Newform.frickeSlashCuspForm =
      Newform.frickeSquareScalar N k • LinearMap.id :=
  LinearMap.ext fun f => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact Newform.frickeSlashCuspForm_apply_apply f

/-- **`LinearMap`-level Fricke square (ModularForm version).** -/
lemma Newform.frickeSlashModularForm_comp_self {N : ℕ} [NeZero N] {k : ℤ} :
    (Newform.frickeSlashModularForm (N := N) (k := k)).comp
        Newform.frickeSlashModularForm =
      Newform.frickeSquareScalar N k • LinearMap.id :=
  LinearMap.ext fun f => by
    rw [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact Newform.frickeSlashModularForm_apply_apply f

/-! ### Petersson adjoint identity for the Fricke operator (T145) -/

section FrickeAdjoint
open UpperHalfPlane MeasureTheory
open scoped UpperHalfPlane

/-- **Petersson adjoint of `W_N` at the matrix level (T145 helper).**

`peterssonAdj (Newform.frickeMatrix N)` has underlying matrix `!![0, 1; -N, 0]`,
which is the negation of `Newform.frickeMatrix N`'s matrix entries. Computed
directly via `peterssonAdj_coe` + `Newform.frickeMatrix_coe` +
`Matrix.adjugate_fin_two`. -/
lemma Newform.peterssonAdj_frickeMatrix_coe (N : ℕ) [NeZero N] :
    (peterssonAdj (Newform.frickeMatrix N) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1; -(N : ℝ), 0] := by
  rw [peterssonAdj_coe, Newform.frickeMatrix_coe, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Möbius action of `peterssonAdj W_N` agrees with that of `W_N` (T145 helper).**

Both matrices have the same Möbius image because `peterssonAdj W_N`'s underlying
matrix `!![0, 1; -N, 0]` differs from `W_N`'s underlying matrix `!![0, -1; N, 0]`
only by an overall sign, which cancels in the Möbius quotient `(num)/(denom)`. -/
lemma Newform.peterssonAdj_frickeMatrix_smul (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    (peterssonAdj (Newform.frickeMatrix N)) • τ = Newform.frickeMatrix N • τ := by
  apply UpperHalfPlane.ext
  have hadj_det_pos : 0 < (peterssonAdj (Newform.frickeMatrix N)).det.val := by
    rw [show (peterssonAdj (Newform.frickeMatrix N)).det.val =
        (Newform.frickeMatrix N).det.val from
        congr_arg Units.val (peterssonAdj_det _)]
    exact Newform.frickeMatrix_det_pos N
  rw [UpperHalfPlane.coe_smul_of_det_pos hadj_det_pos,
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
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hτ_ne : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  push_cast
  field_simp
  ring

/-- **Slash by `peterssonAdj W_N` equals `(-1)^k` times slash by `W_N` (T145 key).**

For any `g : UpperHalfPlane → ℂ`, slashing by the Petersson adjoint of `Newform.frickeMatrix N`
equals slashing by `W_N` itself, scaled by `(-1)^k`. Proof: direct slash-formula
computation using the matrix-level identity `peterssonAdj_frickeMatrix_coe`, the
Möbius identification (`peterssonAdj_frickeMatrix_smul`), and the `(-Nτ)^(-k) =
(-1)^(-k) · (Nτ)^(-k) = (-1)^k · (Nτ)^(-k)` zpow identity. -/
lemma Newform.slash_peterssonAdj_frickeMatrix
    {N : ℕ} [NeZero N] {k : ℤ} (g : UpperHalfPlane → ℂ) :
    g ∣[k] peterssonAdj (Newform.frickeMatrix N) =
      ((-1 : ℂ) ^ k) • (g ∣[k] Newform.frickeMatrix N) := by
  funext τ
  -- Compute LHS via slash_def using the matrix-level identity.
  have hadj_det_pos : 0 < (peterssonAdj (Newform.frickeMatrix N)).det.val := by
    rw [show (peterssonAdj (Newform.frickeMatrix N)).det.val =
        (Newform.frickeMatrix N).det.val from
        congr_arg Units.val (peterssonAdj_det _)]
    exact Newform.frickeMatrix_det_pos N
  have hadj_σ : UpperHalfPlane.σ (peterssonAdj (Newform.frickeMatrix N)) =
      RingHom.id ℂ := by
    unfold UpperHalfPlane.σ
    rw [if_pos hadj_det_pos]
  have hadj_det : (peterssonAdj (Newform.frickeMatrix N)).det.val = (N : ℝ) := by
    rw [show (peterssonAdj (Newform.frickeMatrix N)).det.val =
        (Newform.frickeMatrix N).det.val from
        congr_arg Units.val (peterssonAdj_det _)]
    exact Newform.frickeMatrix_det N
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
  -- Apply the slash formula on the RHS via frickeMatrix_slash_apply.
  rw [Pi.smul_apply, smul_eq_mul, Newform.frickeMatrix_slash_apply]
  -- LHS slash output via slash_def:
  rw [show (g ∣[k] peterssonAdj (Newform.frickeMatrix N)) τ =
      UpperHalfPlane.σ (peterssonAdj (Newform.frickeMatrix N))
        (g ((peterssonAdj (Newform.frickeMatrix N)) • τ)) *
        |((peterssonAdj (Newform.frickeMatrix N)).det.val)| ^ (k - 1) *
        UpperHalfPlane.denom (peterssonAdj (Newform.frickeMatrix N)) τ ^ (-k) from rfl]
  rw [hadj_σ, RingHom.id_apply, hadj_det, hadj_denom,
      Newform.peterssonAdj_frickeMatrix_smul]
  rw [show |(N : ℝ)| = (N : ℝ) from
    abs_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N)))]
  -- Now the (-1)^k factor needs to be extracted from (-(Nτ))^(-k)
  rw [show (-((N : ℂ) * (τ : ℂ))) ^ (-k) =
      (-1 : ℂ) ^ k * ((N : ℂ) * (τ : ℂ)) ^ (-k) by
    rw [show (-((N : ℂ) * (τ : ℂ))) = (-1 : ℂ) * ((N : ℂ) * (τ : ℂ)) by ring,
        mul_zpow]
    rw [show (-1 : ℂ) ^ (-k) = (-1 : ℂ) ^ k by
      rw [zpow_neg, show ((-1 : ℂ) ^ k)⁻¹ = ((-1 : ℂ)⁻¹) ^ k from
            (inv_zpow _ _).symm,
          show ((-1 : ℂ)⁻¹ : ℂ) = -1 by norm_num]]]
  ring

/-- **Petersson adjoint identity for the Fricke slash on cusp forms (T145 main).**

`petN (frickeSlashCuspForm f) g = (-1)^k * petN f (frickeSlashCuspForm g)`.

This is the **Fricke / Petersson adjoint bridge** for the bad-prime adjoint package.
Proof: combine the generic `petN_slash_adjoint_GL2` with the slash identification
`Newform.slash_peterssonAdj_frickeMatrix` and `petN_smul_right` linearity, taking
`α := Newform.frickeMatrix N` (det > 0) and `f_α := frickeSlashCuspForm f`.

The technical hypotheses (Γ₁(N)-tile fundamental-domain claim for `W_N • F` and
related integrability) are passed through as parameters so that the consumer can
discharge them via the existing T141/T143 normalisation infrastructure.

The discharge of these technical hypotheses—the Γ₁(N)-fundamental-domain claim
for `W_N • Gamma1_fundDomain_PSL N` plus integrability of the petersson form on
the shifted tile—is left as a separate downstream task. The blocker is the
fundamental-domain transport theorem for `W_N`-conjugation on Γ₁(N) at the PSL
level (the SL-level normalisation is supplied by T141 via
`Newform.frickeMat_int_mul_eq_frickeConjMat_mul_frickeMat_int`). -/
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
      (fun τ => petersson k (⇑f) (⇑((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp) :
    petN (Newform.frickeSlashCuspForm f) g =
      (-1 : ℂ) ^ k * petN f (Newform.frickeSlashCuspForm g) := by
  -- Discharge: ⇑(frickeSlashCuspForm f) = ⇑f ∣[k] W_N
  have hf_α : ⇑(Newform.frickeSlashCuspForm f) = ⇑f ∣[k] Newform.frickeMatrix N :=
    Newform.frickeSlashCuspForm_coe f
  -- Discharge: ⇑((-1)^k • frickeSlashCuspForm g) = ⇑g ∣[k] peterssonAdj W_N
  have hg_adj : ⇑((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g) =
      ⇑g ∣[k] peterssonAdj (Newform.frickeMatrix N) := by
    show ((-1 : ℂ) ^ k) • ⇑(Newform.frickeSlashCuspForm g) =
      ⇑g ∣[k] peterssonAdj (Newform.frickeMatrix N)
    rw [Newform.frickeSlashCuspForm_coe]
    exact (Newform.slash_peterssonAdj_frickeMatrix _).symm
  -- Apply the generic petN slash adjoint with α := W_N.
  have h := petN_slash_adjoint_GL2 (k := k) (Newform.frickeMatrix N)
    (Newform.frickeMatrix_det_pos N) f g
    (Newform.frickeSlashCuspForm f) hf_α
    ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g) hg_adj
    hα_norm hα_fd h_int h_α_int
  rw [h, petN_smul_right]

/-- **Petersson invariance under W_N-shifted Γ₁(N) translation (T146 helper).**

Discharges the `hα_norm` hypothesis of `petN_slash_adjoint_GL2` for the Fricke
matrix `α := W_N`. For any γ ∈ Γ₁(N) and τ ∈ ℍ:
```
petersson k ⇑f ⇑g₂ (W_N • γ • τ) = petersson k ⇑f ⇑g₂ (W_N • τ)
```
Proof: T141/T142 give `W_N · mapGL γ = mapGL δ · W_N` with δ := frickeConj γ ∈ Γ₁(N).
Hence `W_N • γ • τ = W_N • (mapGL γ • τ) = (W_N · mapGL γ) • τ = (mapGL δ · W_N) • τ
= mapGL δ • (W_N • τ) = δ • (W_N • τ)`, and `petersson_Gamma1_invariant` for δ
absorbs the δ-shift on the second slot. -/
lemma Newform.frickeMatrix_smul_petersson_invariant
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) (τ : UpperHalfPlane) :
    petersson k (⇑f) (⇑g₂)
        (Newform.frickeMatrix N • ((γ : SL(2, ℤ)) • τ)) =
      petersson k (⇑f) (⇑g₂) (Newform.frickeMatrix N • τ) := by
  -- Step 1: rewrite γ-action via mapGL embedding (SL action factors through mapGL).
  rw [show ((γ : SL(2, ℤ)) • τ : UpperHalfPlane) = (mapGL ℝ γ : GL (Fin 2) ℝ) • τ from rfl]
  -- Step 2: combine W_N and mapGL γ via mul_smul, then T142.
  rw [show (Newform.frickeMatrix N • ((mapGL ℝ γ : GL (Fin 2) ℝ) • τ) : UpperHalfPlane) =
      (Newform.frickeMatrix N * (mapGL ℝ γ : GL (Fin 2) ℝ)) • τ from
      (mul_smul _ _ τ).symm]
  rw [Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix γ hγ]
  rw [show (mapGL ℝ (Newform.frickeConj N γ hγ) * Newform.frickeMatrix N) • τ =
      (mapGL ℝ (Newform.frickeConj N γ hγ) : GL (Fin 2) ℝ) •
        (Newform.frickeMatrix N • τ) from mul_smul _ _ _]
  -- Step 3: identify (mapGL δ • τ' : UpperHalfPlane) with (δ • τ' : SL action).
  rw [show (mapGL ℝ (Newform.frickeConj N γ hγ) : GL (Fin 2) ℝ) •
        (Newform.frickeMatrix N • τ) =
      ((Newform.frickeConj N γ hγ : SL(2, ℤ)) : SL(2, ℤ)) •
        (Newform.frickeMatrix N • τ) from rfl]
  -- Step 4: petersson_Gamma1_invariant on the δ-shifted second slot.
  exact petersson_Gamma1_invariant f g₂ (Newform.frickeConj N γ hγ)
    (Newform.frickeConj_mem_Gamma1 N γ hγ) _

/-- **Integrability of W_N-shifted petersson on the canonical FD (T146 helper).**

Discharges the `h_α_int` hypothesis of `petN_slash_adjoint_GL2` for the Fricke
matrix. The function `τ ↦ petersson k f g₂ (W_N • τ)` is bounded (because petersson
is globally bounded for cusp forms via `CuspFormClass.petersson_bounded_left`) and
`Gamma1_fundDomain_PSL N` has finite hyperbolic measure. Combined with continuity
(for AEStronglyMeasurable), `IntegrableOn.of_bound` closes it. -/
lemma Newform.integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    MeasureTheory.IntegrableOn
      (fun τ => petersson k (⇑f) (⇑g₂) (Newform.frickeMatrix N • τ))
      (Gamma1_fundDomain_PSL N) μ_hyp := by
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    ((Gamma1 N).map (mapGL ℝ)) f g₂
  have h_cont : Continuous fun τ : UpperHalfPlane =>
      petersson k (⇑f) (⇑g₂) (Newform.frickeMatrix N • τ) :=
    (petersson_continuous k (ModularFormClass.continuous f)
      (ModularFormClass.continuous g₂)).comp
      (continuous_const_smul (Newform.frickeMatrix N : GL (Fin 2) ℝ))
  exact MeasureTheory.IntegrableOn.of_bound
    hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top
    h_cont.aestronglyMeasurable.restrict C
    (Filter.Eventually.of_forall fun τ => hC _)

/-- **Fricke `W_N`-shifted Γ₁(N) fundamental domain claim (T146 named blocker).**

Statement of the FD-transport claim that, after discharge, removes the last
caller-supplied hypothesis from `Newform.frickeSlashCuspForm_petN_adjoint`:
```
IsFundamentalDomain (imageGamma1_PSL N)
  (Newform.frickeMatrix N • Gamma1_fundDomain_PSL N) μ_hyp
```

**Mathematical content**: `W_N` (det = N > 0) normalises `Γ₁(N)` (T141 supplies
`W_N · γ = (frickeConj γ) · W_N` at the integer-matrix level, both factors in
`Γ₁(N)`). Hence the conjugation `g ↦ W_N · g · W_N⁻¹` permutes `Γ₁(N)`, and
`W_N • F` is again a `Γ₁(N)`-fundamental domain.

**Proof route (T147)**: lift to `PSL(2, ℝ)` via `GLPos_to_PSL_R_term`, apply
`isFundamentalDomain_PSL_R_smul_conjAct` + the normalizer fact, then bridge from
`imageGamma1_PSL_R N` (PSL_R subgroup) back to `imageGamma1_PSL N` (PSL_Z
subgroup) via `IsFundamentalDomain.image_of_equiv` with the subgroup
equivalence `Subgroup.equivMapOfInjective ... PSL2Z_to_PSL2R_injective` (the
same bridge used by `isFundamentalDomain_Gamma1_PSL_R` in the forward
direction).

This is left as the named target for T147; the alternative is direct
verification of `IsFundamentalDomain.mk'`-style ae-cover and ae-disjointness
conditions using the W_N-conjugation. -/
def Newform.HasFrickeFundDomainTransport (N : ℕ) [NeZero N] : Prop :=
  MeasureTheory.IsFundamentalDomain (imageGamma1_PSL N)
    ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
      (Gamma1_fundDomain_PSL N : Set UpperHalfPlane)) μ_hyp

/-- **Fricke Petersson-adjoint identity, conditional only on FD-transport (T146 main).**

Stronger version of `Newform.frickeSlashCuspForm_petN_adjoint`: takes only the
single FD-transport hypothesis `Newform.HasFrickeFundDomainTransport N`. The
other technical hypotheses (Γ₁(N)-invariance under W_N shift, integrability of
the petersson form on the canonical and W_N-shifted tile) are discharged in
Lean via:
* `Newform.frickeMatrix_smul_petersson_invariant` (T141/T142 + petersson_Gamma1_invariant)
* `integrableOn_petersson_Gamma1_fundDomain_PSL` (canonical-tile integrability)
* `Newform.integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL` (W_N-shifted-tile
  integrability via global boundedness of petersson for cusp forms)

After T147 discharges `HasFrickeFundDomainTransport N` (proof of the FD claim),
the unconditional `frickeSlashCuspForm_petN_adjoint_unconditional` follows by
specialisation. -/
theorem Newform.frickeSlashCuspForm_petN_adjoint_of_isFundDomain
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_FD : Newform.HasFrickeFundDomainTransport N) :
    petN (Newform.frickeSlashCuspForm f) g =
      (-1 : ℂ) ^ k * petN f (Newform.frickeSlashCuspForm g) := by
  refine Newform.frickeSlashCuspForm_petN_adjoint f g
    (fun γ hγ τ => Newform.frickeMatrix_smul_petersson_invariant f
      ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g) γ hγ τ)
    h_FD
    (integrableOn_petersson_Gamma1_fundDomain_PSL f
      ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))
    (Newform.integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL f
      ((-1 : ℂ) ^ k • Newform.frickeSlashCuspForm g))

/-! #### PSL(2, ℝ) bridge for the Fricke FD-transport claim (T146 step) -/

/-- **Fricke matrix as a `GL(2, ℝ)⁺` element (T146 helper).**

Packages `Newform.frickeMatrix N : GL (Fin 2) ℝ` together with its positive
determinant proof `Newform.frickeMatrix_det_pos N` to view it as an element of
`GL(2, ℝ)⁺` (the positive-determinant subgroup). Used to consume the
`GLPos_to_PSL_R_term` API which requires positive determinant. -/
noncomputable def Newform.frickeMatrix_GLPos (N : ℕ) [NeZero N] : GL(2, ℝ)⁺ :=
  ⟨Newform.frickeMatrix N, Newform.frickeMatrix_det_pos N⟩

/-- **`PSL(2, ℝ)`-representative of the Fricke matrix `W_N` (T146 main bridge).**

The projective-real representative of `W_N := Newform.frickeMatrix N`, defined
via `GLPos_to_PSL_R_term` applied to `Newform.frickeMatrix_GLPos N`. By
non-triviality of the action of `PSL(2, ℝ)` on `ℍ` (modulo center), this is the
canonical lift of `W_N`'s Möbius action to a `PSL(2, ℝ)` element, even though
`GLPos_to_PSL_R_term` is not a group homomorphism on the nose. -/
noncomputable def Newform.frickeMatrix_PSL_R (N : ℕ) [NeZero N] : PSL(2, ℝ) :=
  GLPos_to_PSL_R_term (Newform.frickeMatrix_GLPos N)

/-- **Action equality `frickeMatrix_PSL_R N • τ = frickeMatrix N • τ` (T146 bridge).**

Direct corollary of `GLPos_to_PSL_R_term_smul`: the projective-real
representative `frickeMatrix_PSL_R N` acts on `ℍ` exactly as the
`GL(2, ℝ)`-element `frickeMatrix N` does. This bridges the `PSL(2, ℝ)`
fundamental-domain machinery (which requires a `PSL(2, ℝ)` shift) to the
GL(2, ℝ)-shifted fundamental domain `frickeMatrix N • F` that the Petersson
adjoint package needs. -/
@[simp]
lemma Newform.frickeMatrix_PSL_R_smul (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    Newform.frickeMatrix_PSL_R N • τ =
      (Newform.frickeMatrix N : GL (Fin 2) ℝ) • τ := by
  show GLPos_to_PSL_R_term (Newform.frickeMatrix_GLPos N) • τ =
    (Newform.frickeMatrix N : GL (Fin 2) ℝ) • τ
  rw [GLPos_to_PSL_R_term_smul]
  rfl

/-- **Set-level action equality for `frickeMatrix_PSL_R N` (T146 bridge).**

Set-level analogue of `Newform.frickeMatrix_PSL_R_smul`. Identifies the
`PSL(2, ℝ)`-shifted set with the `GL(2, ℝ)`-shifted set, allowing the FD claim
at `PSL(2, ℝ)` ambient to translate directly into the GL-shifted form needed
by the Petersson adjoint. -/
@[simp]
lemma Newform.frickeMatrix_PSL_R_smul_set (N : ℕ) [NeZero N]
    (S : Set UpperHalfPlane) :
    (Newform.frickeMatrix_PSL_R N • S : Set UpperHalfPlane) =
      (Newform.frickeMatrix N : GL (Fin 2) ℝ) • S := by
  ext τ
  simp only [Set.mem_smul_set, Newform.frickeMatrix_PSL_R_smul]

/-- **`GLPos_to_SLR (frickeMatrix_GLPos N)` underlying matrix via GL (T147 helper).**

The SL(2, ℝ)-element `GLPos_to_SLR (frickeMatrix_GLPos N)`, viewed first as a
`GL (Fin 2) ℝ` element (via `Matrix.SpecialLinearGroup.toGL`), then as a 2×2
real matrix, equals `(sqrt N)⁻¹ • W_N.val`. Routed through the GL coercion to
match T142's GL-level state, avoiding direct `SL → Matrix` coercion. -/
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

/-- **GL-level Fricke conjugation identity for the SL_R representative
(T147 helper).**

For γ ∈ Γ₁(N), the SL(2, ℝ) representative `W_SL := GLPos_to_SLR (frickeMatrix_GLPos N)`
satisfies the Fricke conjugation identity at the GL (Fin 2) ℝ level:
```
((W_SL : GL) * mapGL ℝ γ = mapGL ℝ (frickeConj N γ) * (W_SL : GL))
```
in `GL (Fin 2) ℝ`. Proof: reduce to matrix equality via `Units.ext`, expand
both sides via `coe_mul`, use `GLPos_to_SLR_frickeMatrix_GLPos_toGL_matrix`
to expose the `(sqrt N)⁻¹ • W_N` shape, pull the scalar through
`Matrix.smul_mul`/`mul_smul`, then close with T142's matrix form. -/
lemma Newform.frickeMatrix_SLR_toGL_mul_mapGL_eq
    {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
        GL (Fin 2) ℝ) *
        (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ (Newform.frickeConj N γ hγ) : GL (Fin 2) ℝ) *
        ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
          GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul]
  rw [Newform.GLPos_to_SLR_frickeMatrix_GLPos_toGL_matrix]
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  have h_T142 := Newform.frickeMatrix_mul_mapGL_eq_mapGL_frickeConj_mul_frickeMatrix γ hγ
  have h_matrix :
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        ((mapGL ℝ γ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) =
      ((mapGL ℝ (Newform.frickeConj N γ hγ) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [← Matrix.GeneralLinearGroup.coe_mul,
        ← Matrix.GeneralLinearGroup.coe_mul, h_T142]
  exact h_matrix

/-- **SL(2, ℝ)-level Fricke conjugation identity (T147 main).**

For γ ∈ Γ₁(N), the SL(2, ℝ) representative
`W_SL := GLPos_to_SLR (frickeMatrix_GLPos N)` satisfies the Fricke conjugation:
```
W_SL * map_SL γ = map_SL (frickeConj N γ) * W_SL
```
in `SL(2, ℝ)`, where `map_SL := Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)`.
Lift of the GL-level identity `frickeMatrix_SLR_toGL_mul_mapGL_eq` via
`Matrix.SpecialLinearGroup.toGL_injective`. -/
lemma Newform.frickeMatrix_SL_R_mul_SLmap_eq
    {N : ℕ} [NeZero N] (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    GLPos_to_SLR (Newform.frickeMatrix_GLPos N) *
        Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ =
      Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
          (Newform.frickeConj N γ hγ) *
        GLPos_to_SLR (Newform.frickeMatrix_GLPos N) := by
  refine (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := ℝ)) ?_
  -- The lifted GL equation is exactly frickeMatrix_SLR_toGL_mul_mapGL_eq.
  -- Recall: mapGL ℝ γ = toGL (map (Int.castRingHom ℝ) γ).
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
  -- mapGL ℝ γ = toGL (map (Int.castRingHom ℝ) γ) — definitional.
  rw [show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) γ : SL(2, ℝ)) :
        GL (Fin 2) ℝ) = (mapGL ℝ γ : GL (Fin 2) ℝ) from rfl,
    show ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)
            (Newform.frickeConj N γ hγ) : SL(2, ℝ)) :
        GL (Fin 2) ℝ) = (mapGL ℝ (Newform.frickeConj N γ hγ) :
        GL (Fin 2) ℝ) from rfl]
  exact Newform.frickeMatrix_SLR_toGL_mul_mapGL_eq γ hγ

/-- **PSL(2, ℝ) Fricke conjugation identity (T147 main).**

PSL-projection of `Newform.frickeMatrix_SL_R_mul_SLmap_eq` via
`QuotientGroup.mk_mul`. For γ ∈ Γ₁(N):
```
frickeMatrix_PSL_R N * SL2Z_to_PSL2R γ =
  SL2Z_to_PSL2R (frickeConj N γ) * frickeMatrix_PSL_R N
```
in `PSL(2, ℝ)`. -/
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

/-- The `SL(2, ℝ)` Fricke matrix squares to `-1` at the matrix level:
`((√N)⁻¹ • W_N)² = N⁻¹ • (W_N · W_N) = N⁻¹ • (-N • 1) = scalar (-1)`. Combines
`GLPos_to_SLR_frickeMatrix_GLPos_toGL_matrix` with `frickeMatrix_mul_self_val`;
feeds the `mem_center` reduction in `Newform.frickeMatrix_PSL_R_mul_self`. -/
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
  -- `(√N)⁻¹ * (√N)⁻¹ = N⁻¹` via `√N · √N = N`.
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have h_sqrt_sq : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hN_pos)
  rw [show ((Real.sqrt ((N : ℝ)))⁻¹ * (Real.sqrt (N : ℝ))⁻¹ : ℝ) = ((N : ℝ))⁻¹ by
    rw [← mul_inv, h_sqrt_sq]]
  rw [show ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Newform.frickeMatrix N * Newform.frickeMatrix N : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from (Matrix.GeneralLinearGroup.coe_mul _ _).symm]
  rw [Newform.frickeMatrix_mul_self_val, smul_smul]
  rw [show ((N : ℝ))⁻¹ * (-(N : ℝ)) = -1 by field_simp]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.smul_apply, Matrix.scalar]

/-- **Self-inverseness of `frickeMatrix_PSL_R N` in `PSL(2, ℝ)` (T147 helper).**

`W_N² = -N • 1` at the matrix level (T141 + frickeMatrix_mul_self_val) means
that after `(sqrt N)⁻¹`-normalization to SL(2, ℝ), the square is `-1 : SL(2, ℝ)`,
which is in the center and hence trivial in `PSL(2, ℝ)`.

Equivalently: `frickeMatrix_PSL_R N * frickeMatrix_PSL_R N = 1` in `PSL(2, ℝ)`,
i.e., `frickeMatrix_PSL_R N` is its own inverse. This avoids the full SL(2, ℝ)
involution proof (which would require `(sqrt N)⁻¹ • W_N` squaring to `-1`)
by reducing to the well-known fact that `±I` is the kernel of `SL → PSL`. -/
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
  -- Reduce to: GLPos_to_SLR ... * GLPos_to_SLR ... ∈ center SL(2, ℝ).
  rw [QuotientGroup.eq_one_iff]
  -- center SL(2, ℝ) = {±I}; show the square equals -1 (or 1).
  -- Actually: W_SL * W_SL has matrix ((sqrt N)⁻¹)² • (W_N * W_N) =
  --   (1/N) • (-N • 1) = -1 • 1 = -I_2.
  -- So W_SL * W_SL = -1 ∈ SL(2, ℝ), which is in center.
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, ?_, ?_⟩
  · -- (-1)^Fintype.card (Fin 2) = (-1)² = 1.
    simp [Fintype.card_fin]
  · -- scalar (Fin 2) (-1) = -I_2 = (W_SL * W_SL).val.
    show Matrix.scalar (Fin 2) (-1) =
      ((GLPos_to_SLR (Newform.frickeMatrix_GLPos N) *
        GLPos_to_SLR (Newform.frickeMatrix_GLPos N) : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ)
    symm
    -- (a * b).val = a.val * b.val for SL; then the matrix square is `scalar (-1)`.
    show (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        (GLPos_to_SLR (Newform.frickeMatrix_GLPos N) :
          Matrix (Fin 2) (Fin 2) ℝ) =
      Matrix.scalar (Fin 2) (-1)
    exact GLPos_to_SLR_frickeMatrix_GLPos_sq_eq_neg_scalar N

/-- **Inverse of `frickeMatrix_PSL_R N` is itself (T147 corollary).** -/
lemma Newform.frickeMatrix_PSL_R_inv (N : ℕ) [NeZero N] :
    (Newform.frickeMatrix_PSL_R N)⁻¹ = Newform.frickeMatrix_PSL_R N := by
  rw [eq_comm, ← mul_eq_one_iff_eq_inv]
  exact Newform.frickeMatrix_PSL_R_mul_self N

/-- **One-way Fricke conjugation preservation in `imageGamma1_PSL_R N` (T147 helper).**

For h ∈ imageGamma1_PSL_R N, conjugating by `frickeMatrix_PSL_R N` (left-mult,
right-inv) keeps the result in `imageGamma1_PSL_R N`. Combined with the
self-inverse fact `Newform.frickeMatrix_PSL_R_mul_self`, this gives the full
normalizer condition. -/
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

/-- **`frickeMatrix_PSL_R N` lies in the normalizer of `imageGamma1_PSL_R N` (T147).**

Combined the one-way preservation with `Newform.frickeMatrix_PSL_R_inv` (the
self-inverseness): if `W * h * W⁻¹ ∈ H`, then applying conjugation by W (= W⁻¹)
again recovers `h ∈ H`. -/
lemma Newform.frickeMatrix_PSL_R_mem_normalizer (N : ℕ) [NeZero N] :
    Newform.frickeMatrix_PSL_R N ∈ (imageGamma1_PSL_R N).normalizer := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨Newform.frickeMatrix_PSL_R_conj_mem_imageGamma1_PSL_R, ?_⟩
  intro h_conj_mem
  -- Apply one-way to the conjugate to recover h.
  have h_inv_eq : (Newform.frickeMatrix_PSL_R N)⁻¹ = Newform.frickeMatrix_PSL_R N :=
    Newform.frickeMatrix_PSL_R_inv N
  have h_back := Newform.frickeMatrix_PSL_R_conj_mem_imageGamma1_PSL_R h_conj_mem
  -- h_back: W * (W * h * W⁻¹) * W⁻¹ ∈ imageGamma1_PSL_R N.
  -- Using W⁻¹ = W: h_back simplifies to h ∈ imageGamma1_PSL_R N.
  have h_simplify :
      Newform.frickeMatrix_PSL_R N *
          (Newform.frickeMatrix_PSL_R N * h *
            (Newform.frickeMatrix_PSL_R N)⁻¹) *
          (Newform.frickeMatrix_PSL_R N)⁻¹ = h := by
    rw [h_inv_eq]
    have h_sq := Newform.frickeMatrix_PSL_R_mul_self N
    -- Reorganize: W * (W * h * W) * W = W² * h * W² = 1 * h * 1 = h.
    have : Newform.frickeMatrix_PSL_R N *
            (Newform.frickeMatrix_PSL_R N * h * Newform.frickeMatrix_PSL_R N) *
            Newform.frickeMatrix_PSL_R N =
        (Newform.frickeMatrix_PSL_R N * Newform.frickeMatrix_PSL_R N) * h *
          (Newform.frickeMatrix_PSL_R N * Newform.frickeMatrix_PSL_R N) := by
      group
    rw [this, h_sq, one_mul, mul_one]
  rw [← h_simplify]
  exact h_back

/-- **Fricke FD-transport (T147 main).**

`HasFrickeFundDomainTransport N` is now provable, completing T146's named
blocker: composition of bridge 1 (`frickeMatrix_PSL_R_smul_set`), bridge 2
(`isFundamentalDomain_imageGamma1_PSL_of_PSL_R`), the canonical PSL_R FD
(`isFundamentalDomain_Gamma1_PSL_R`), and `IsFundamentalDomain.smul_of_mem_normalizer`
applied to `Newform.frickeMatrix_PSL_R_mem_normalizer`. -/
lemma Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL
    (N : ℕ) [NeZero N] :
    Newform.HasFrickeFundDomainTransport N := by
  unfold Newform.HasFrickeFundDomainTransport
  rw [← Newform.frickeMatrix_PSL_R_smul_set]
  exact isFundamentalDomain_imageGamma1_PSL_of_PSL_R
    (isFundamentalDomain_Gamma1_PSL_R.smul_of_mem_normalizer
      (Newform.frickeMatrix_PSL_R_mem_normalizer N))

/-- **Unconditional Fricke Petersson-adjoint identity (T147 main theorem).**

The unconditional version of the Fricke / petN adjoint relation:
```
petN (frickeSlashCuspForm f) g = (-1)^k * petN f (frickeSlashCuspForm g)
```
for any cusp forms `f, g` of level `Γ₁(N)` and weight `k`. No caller-supplied
hypotheses; the FD-transport claim is discharged in
`Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL`. -/
theorem Newform.frickeSlashCuspForm_petN_adjoint_unconditional
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (Newform.frickeSlashCuspForm f) g =
      (-1 : ℂ) ^ k * petN f (Newform.frickeSlashCuspForm g) :=
  Newform.frickeSlashCuspForm_petN_adjoint_of_isFundDomain f g
    (Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL N)

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **W_N-shifted Σ_q FD-tiling for petN (T170 deliverable).**

For any `Γ₁(N)`-cusp forms `f, g` of weight `k`, summing `peterssonInner` over
`W_N`-shifted SL-coset tiles equals `petN`:
```
∑_q peterssonInner k (W_N • q.out⁻¹ • fd) ⇑f ⇑g = petN f g.
```

Mathematical content: `W_N` (the Fricke matrix) normalises `Γ₁(N)`, so
`W_N • Γ₁(N)_FD` is also a `Γ₁(N)` fundamental domain, and the SL coset
sum on either side counts each tile of the canonical `Γ₁(N)`-fundamental
domain exactly once (modulo `slToPslQuot_fiberCard`). Combined with
`Γ₁(N)`-invariance of `petersson k ⇑f ⇑g` (cusp form invariance), the two
SL coset sums coincide.

**Proof.** Apply `sum_setIntegral_GL2_shift` with `α := frickeMatrix_GLPos N`
and `h := petersson k ⇑f ⇑g`. Discharge the hypotheses:
* `Γ₁(N)`-invariance via `petersson_Gamma1_invariant`.
* `W_N`-shifted invariance via `frickeMatrix_smul_petersson_invariant`.
* FD claim via `frickeMatrix_smul_isFundDomain_imageGamma1_PSL`.
* Integrability via `integrableOn_petersson_Gamma1_fundDomain_PSL` and
  `integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL`.

This closes the W_N FD-tiling content underneath `qBSimplified`'s RHS
unfolding (T166/T167) at the petN level. The original
`HasBadPrimeFrickePerCosetT152ShiftedFD` (T155) stated a per-q identity
which the T159 audit found mathematically too strong: the integrands
`petersson k (T_p f) g` and `petersson k f (T_p^σ g)` are *not* equal
AE on individual `q.out⁻¹ • fd` tiles; only the `q`-sum coincides. The
W_N FD-tiling above captures the correct `q`-summed transport content. -/
theorem Newform.sum_peterssonInner_frickeMatrix_smul_q_out_inv_fd_eq_petN
    {N : ℕ} [NeZero N] {k : ℤ}
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
        ⇑f ⇑g =
    petN f g := by
  -- Apply sum_setIntegral_GL2_shift with α := frickeMatrix_GLPos N and
  -- h := petersson k ⇑f ⇑g. The shift identity gives
  --   Σ_q ∫_{α • q.out⁻¹•fd} h dμ = Σ_q ∫_{q.out⁻¹•fd} h dμ.
  have h_shift := sum_setIntegral_GL2_shift (N := N)
    (α := Newform.frickeMatrix_GLPos N) (h := petersson k ⇑f ⇑g)
    (h_inv := fun γ hγ τ => petersson_Gamma1_invariant f g γ hγ τ)
    (hα_h_inv := fun γ hγ τ =>
      Newform.frickeMatrix_smul_petersson_invariant f g γ hγ τ)
    (hα_fd := Newform.frickeMatrix_smul_isFundDomain_imageGamma1_PSL N)
    (h_int := integrableOn_petersson_Gamma1_fundDomain_PSL f g)
    (h_α_int := Newform.integrableOn_petersson_smul_frickeMatrix_fundDomain_PSL f g)
  -- LHS of h_shift: Σ_q ∫_{W_N • q.out⁻¹•fd} h dμ = Σ_q peterssonInner k (W_N • ...) ⇑f ⇑g.
  -- RHS of h_shift: Σ_q ∫_{q.out⁻¹•fd} h dμ = petN f g via SL transfer reverse.
  -- The unfolded `↑(frickeMatrix_GLPos N) : GL (Fin 2) ℝ` is definitionally equal to
  -- `frickeMatrix N : GL (Fin 2) ℝ` (Subtype.val), and `peterssonInner k S F G` unfolds
  -- definitionally to `∫ τ in S, petersson k F G τ ∂μ_hyp`. So `exact h_shift.trans _`
  -- closes the goal once the petN-side rewrite is prepared.
  have h_petN_eq : (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
        petersson k ⇑f ⇑g τ ∂μ_hyp) = petN f g := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    show ∫ τ in (q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane),
        petersson k ⇑f ⇑g τ ∂μ_hyp =
      peterssonInner k fd (⇑f ∣[k] (q.out)⁻¹) (⇑g ∣[k] (q.out)⁻¹)
    rw [peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd ⇑f ⇑g (q.out)]
  exact h_shift.trans h_petN_eq

end FrickeAdjoint

/-- The Fricke root-number scalar collapses to `1`: the three `zpow` pairs
`n^{1-k}·n^{k-1}`, `I^k·I^{-k}`, `x^k·x^{-k}` each cancel, so the bracketed
product reduces to `fv`. Pure complex `zpow` arithmetic with all bases nonzero;
used to close `Newform.imAxis_eq_frickeSlash`. -/
private lemma frickeRootNumber_scalar_collapse {k : ℤ} {n x I fv : ℂ}
    (hn : n ≠ 0) (hx : x ≠ 0) (hI : I ≠ 0) :
    n ^ (1 - k) * I ^ k * x ^ k *
      (fv * n ^ (k - 1) * (x ^ (-k) * I ^ (-k))) = fv := by
  simp only [zpow_sub₀ hn, zpow_neg]
  field_simp

/-- Imaginary-axis points lie in the upper half plane: `I · r` has positive
imaginary part for `0 < r`. Discharges the membership witnesses for the
`τ_inner`/`τ_outer` points in `Newform.imAxis_eq_frickeSlash`. -/
private lemma im_I_mul_ofReal_pos {r : ℝ} (hr : 0 < r) :
    0 < (Complex.I * ((r : ℝ) : ℂ)).im := by
  rw [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
    Complex.ofReal_im]
  simpa using hr

/-- The Fricke involution `W_N • z = -1/(N z)` sends the imaginary-axis point
`I · (x/N)` to `I · (1/x)` (coordinate form). The `Complex.I_sq` reduction of
`-1 = I²` is the algebraic heart of the involution at imaginary arguments. -/
private lemma frickeMatrix_smul_imAxis_coe {N : ℕ} [NeZero N] {x : ℝ}
    (hx : 0 < x) :
    (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ))) =
      Complex.I * ((1 / x : ℝ) : ℂ) := by
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hx_ne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  push_cast
  field_simp
  rw [Complex.I_sq]

/-- **Im-axis FE derived from the Fricke slash formula (T132 H1
substantive theorem).**

Specialising `Newform.frickeMatrix_slash_apply` at the imaginary-axis
point `τ_inner := ⟨I · x/N, _⟩` and identifying
`W_N • τ_inner = ⟨I · (1/x), _⟩` (via `Newform.frickeMatrix_smul` +
`UpperHalfPlane.ext`), we derive the imaginary-axis functional equation:

`Newform.imAxis f (1/x) =
   ((N : ℂ)^{1-k} · I^k · x^k) ·
   (⇑f.toCuspForm.toModularForm' ∣[k] frickeMatrix N) ⟨I · (x/N), _⟩`

**Every scalar is derived** from the slash formula, not asserted by
hand.  The `(N)^{1-k} · I^k` factor matches the classical Atkin-Lehner
root-number normalization modulo a `N^{?}` factor inherited from
Mathlib's `|det|^{k-1}` convention. -/
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
  have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  -- Setup the inner/outer imaginary-axis points and apply the slash formula.
  set τ_inner : UpperHalfPlane :=
    ⟨Complex.I * ((x / (N : ℝ) : ℝ) : ℂ), im_I_mul_ofReal_pos (div_pos hx
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))))⟩ with hτ_inner
  have h_slash := Newform.frickeMatrix_slash_apply (N := N) (k := k)
    (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_inner
  set τ_outer : UpperHalfPlane :=
    ⟨Complex.I * ((1 / x : ℝ) : ℂ), im_I_mul_ofReal_pos (one_div_pos.mpr hx)⟩
    with hτ_outer
  -- W_N sends τ_inner to τ_outer (Fricke involution at imaginary arguments).
  have h_smul_eq : (Newform.frickeMatrix N • τ_inner : UpperHalfPlane) = τ_outer := by
    apply UpperHalfPlane.ext
    rw [show ((Newform.frickeMatrix N • τ_inner : UpperHalfPlane) : ℂ) =
        (-1 : ℂ) / ((N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ))) from
        Newform.frickeMatrix_smul _ _]
    exact frickeMatrix_smul_imAxis_coe hx
  -- Identify Newform.imAxis f (1/x) with f.toCuspForm.toModularForm' τ_outer.
  have h_imAxis_eq :
      Newform.imAxis f (1 / x) =
        (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_outer := by
    rw [show Newform.imAxis f = ModularForms.imAxis f.toCuspForm from rfl,
      ModularForms.imAxis_apply_of_pos f.toCuspForm (one_div_pos.mpr hx)]
    rfl
  -- Now solve.
  rw [h_imAxis_eq, h_slash, h_smul_eq]
  -- Simplify ((N : ℂ) · τ_inner)^{-k} via h_τ_inner_coe.
  have h_τ_inner_coe : (N : ℂ) * (τ_inner : ℂ) = Complex.I * ((x : ℝ) : ℂ) := by
    show (N : ℂ) * (Complex.I * ((x / (N : ℝ) : ℝ) : ℂ)) = Complex.I * (x : ℂ)
    push_cast
    field_simp
  rw [h_τ_inner_coe]
  -- Goal: f τ_outer = (N^{1-k} · I^k · x^k) · (f τ_outer · N^{k-1} · (I · x)^{-k})
  -- Need: scalar coefficient = 1.
  set fv : ℂ := (⇑f.toCuspForm.toModularForm' : UpperHalfPlane → ℂ) τ_outer
  have h_N_cast : ((N : ℝ) : ℂ) = (N : ℂ) := by push_cast; rfl
  rw [h_N_cast]
  -- Goal: fv = ((N : ℂ)^{1-k} · I^k · x^k) · (fv · (N : ℂ)^{k-1} · (I · x)^{-k})
  rw [show Complex.I * ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) * Complex.I by ring,
      mul_zpow]
  -- Goal: fv = ((N : ℂ)^{1-k} · I^k · x^k) · (fv · (N : ℂ)^{k-1} · (x^{-k} · I^{-k}))
  -- The three `zpow` pairs cancel: `frickeRootNumber_scalar_collapse`.
  exact (frickeRootNumber_scalar_collapse hN_ne hx_ne hI_ne).symm

/-- **Im-axis FE from a CuspForm slash equality (T132 H1 compatibility
layer).**

Given a CuspForm `twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k` whose
underlying `ℍ → ℂ` function equals the Fricke slash
`⇑f.toCuspForm.toModularForm' ∣[k] frickeMatrix N`, the imaginary-axis
FE follows from `Newform.imAxis_eq_frickeSlash`:

`Newform.imAxis f (1/x) =
   ((N : ℂ)^{1-k} · I^k · x^k) · ModularForms.imAxis twist (x / N)`

Note the `x/N` argument of `ModularForms.imAxis twist` — this is the
honest slash-derived shape; the classical Atkin-Lehner formulation uses
a normalised matrix that absorbs the `1/N` into the imAxis argument. -/
theorem Newform.imAxis_feq_of_slashEq
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N)
    {x : ℝ} (hx : 0 < x) :
    Newform.imAxis f (1 / x) =
      ((N : ℂ) ^ (1 - k) * Complex.I ^ k * ((x : ℝ) : ℂ) ^ k) *
      _root_.ModularForms.imAxis twist (x / (N : ℝ)) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have h_x_div_N_pos : (0 : ℝ) < x / (N : ℝ) := div_pos hx hN_pos
  rw [Newform.imAxis_eq_frickeSlash f hx]
  congr 1
  -- Goal: (slash) τ_inner = ModularForms.imAxis twist (x / N)
  rw [_root_.ModularForms.imAxis_apply_of_pos twist h_x_div_N_pos]
  -- Goal: (slash) ⟨I · x/N, _⟩ = ⇑twist ⟨I · x/N, _⟩
  -- By slash_eq, (slash) = ⇑twist as functions UpperHalfPlane → ℂ.
  rw [← slash_eq]


end HeckeRing.GL2
