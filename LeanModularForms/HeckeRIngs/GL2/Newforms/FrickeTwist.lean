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
import LeanModularForms.HeckeRIngs.GL2.Newforms.Fricke

/-!
# Newforms: Atkin-Lehner / Fricke twist as a structured hypothesis

The Atkin-Lehner / Fricke twist packaged as the structured hypothesis `FrickeTwistData` (T132 H1) and its downstream consumers up to the per-newform full Dirichlet-zero data.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### Atkin-Lehner / Fricke twist as a structured hypothesis (T132 H1)

The classical Atkin-Lehner involution `f ↦ f|W_N` sends a `Γ₁(N)`-
newform `f` to another `Γ₁(N)`-cusp form (the Atkin-Lehner image),
modulo a complex root-number scalar.  Mathlib does not yet provide
the Fricke involution as a CuspForm-valued operator.

We expose the Fricke twist as a **structured hypothesis** bundling
the CuspForm-valued image, the root number, the functional involution
on the imaginary axis, and the Mellin-Dirichlet bridge.  Consumers
plug the bundle into `Newform.ImAxisMellinData.ofFrickeTwistData` to
get a fully-discharged `Newform.ImAxisMellinData f`. -/

/-- **Atkin-Lehner / Fricke twist data for a Newform (T132 H1).**

Bundle of the classical Atkin-Lehner / Fricke twist data needed to
discharge the `h_feq` (functional equation) and `h_bridge`
(Mellin–Dirichlet) fields of `Newform.ImAxisMellinData`.

The genuinely-classical content of Hecke 1936 (Diamond–Shurman §5.9 /
Miyake §4.5.16) lives entirely in the four fields below; the
`ImAxisMellinData` constructor `ofFrickeTwistData` then mechanically
fills the remaining `hF_int`, `hF_top`, `hG_int`, `hG_top`, `hk_pos`
fields. -/
structure Newform.FrickeTwistData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) where
  /-- Atkin-Lehner / Fricke image of `f` as a CuspForm on `Γ₁(N)`. -/
  twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k
  /-- Root number (eigenvalue of the Atkin-Lehner involution). -/
  ε : ℂ
  /-- Cusp-form weight is positive (cast to ℝ from `(k : ℤ)`).  Mechanical
  but kept explicit to avoid weight-positivity assumptions in the
  ambient `Newform` type. -/
  hk_pos : 0 < (k : ℝ)
  /-- Root number is nonzero. -/
  hε_ne : ε ≠ 0
  /-- **Functional equation on the imaginary axis.**  The classical
  Atkin-Lehner FE relates `f(i/x)` and the twist evaluated on the
  imaginary axis modulo a root-number/weight scalar. -/
  h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
    (Newform.imAxis f) (1 / x) =
      (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • _root_.ModularForms.imAxis twist x
  /-- **Mellin–Dirichlet bridge.** -/
  h_bridge : ∀ {s : ℂ},
    LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
    mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s

/-- **`Newform.ImAxisMellinData` constructor from `FrickeTwistData` (T132
H1 strongest endpoint).**

Strongest H1 reduction: builds `Newform.ImAxisMellinData f` from the
structured Atkin-Lehner / Fricke twist hypothesis.  All
`hF_int`/`hF_top`/`hG_int`/`hG_top` fields are mechanically discharged
via the imAxis pipeline (continuity ⇒ local integrability;
strict-period-1 ⇒ exponential ⇒ rapid decay).

The H1 obligation is now reduced to providing `Newform.FrickeTwistData f`
— a single named structure capturing the Hecke 1936 analytic input
(twist construction, root number, FE, Mellin–Dirichlet bridge). -/
noncomputable def Newform.ImAxisMellinData.ofFrickeTwistData
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (data : Newform.FrickeTwistData f) :
    Newform.ImAxisMellinData f :=
  Newform.ImAxisMellinData.ofData_withTwist f data.twist data.ε
    data.hk_pos data.hε_ne data.h_feq data.h_bridge

/-- **`Newform.ImAxisMellinData` from a CuspForm slash-equality
hypothesis (T132 H1 strongest endpoint).**

The strongest reduction toward `h_feq`: from a CuspForm-valued twist
`g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k` whose underlying `ℍ → ℂ`
function equals the Fricke slash
`⇑f.toCuspForm.toModularForm' ∣[k] frickeMatrix N`, this constructor
mechanically derives the imaginary-axis FE via
`Newform.imAxis_feq_of_slashEq`.

The `G` field is set to the scaled `t ↦ ModularForms.imAxis g (t / N)`
(matching the slash-derived shape, not the unscaled `imAxis g`); the
`hG_int` and `hG_top` fields are derived via composition with the
positive scaling `t → t/N`.

Caller-supplied fields collapse to:

* `twist`, `slash_eq` — the CuspForm twist + Fricke slash equality.
* `hk_pos` — weight positivity.
* `h_bridge` — Mellin–Dirichlet bridge.

The `hF_int`, `hF_top`, `h_feq`, `hG_int`, `hG_top`, `hε_ne` fields
are now mechanically discharged. -/
noncomputable def Newform.ImAxisMellinData.ofSlashEq
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k)
    (twist : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (slash_eq : (⇑twist : UpperHalfPlane → ℂ) =
      ⇑f.toCuspForm.toModularForm' ∣[k] Newform.frickeMatrix N)
    (hk_pos : 0 < (k : ℝ))
    (h_bridge : ∀ {s : ℂ},
      LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      mellin (Newform.imAxis f) s = LSeries f.lCoeff_stripped s) :
    Newform.ImAxisMellinData f := by
  have hN_pos : (0 : ℝ) < (N : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hN_ne : (N : ℂ) ≠ 0 := by
    have : (N : ℝ) ≠ 0 := hN_pos.ne'
    exact_mod_cast this
  have hI_ne : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  -- Define the scaled G function.
  let G : ℝ → ℂ := fun t => _root_.ModularForms.imAxis twist (t / (N : ℝ))
  -- ε := (N : ℂ)^{1-k} · I^k.
  let ε : ℂ := (N : ℂ) ^ (1 - k) * Complex.I ^ k
  have hε_ne : ε ≠ 0 := by
    refine mul_ne_zero (zpow_ne_zero _ hN_ne) (zpow_ne_zero _ hI_ne)
  -- Local integrability of G on Ioi 0 via ContinuousOn composition.
  have hG_continuousOn : ContinuousOn G (Set.Ioi (0 : ℝ)) := by
    have h_div_cts : ContinuousOn
        (fun t : ℝ => t / (N : ℝ)) (Set.Ioi (0 : ℝ)) :=
      Continuous.continuousOn (by fun_prop)
    have h_maps : Set.MapsTo (fun t : ℝ => t / (N : ℝ))
        (Set.Ioi 0) (Set.Ioi 0) := fun t ht => div_pos ht hN_pos
    exact (_root_.ModularForms.continuousOn_imAxis twist).comp h_div_cts h_maps
  have hG_int : MeasureTheory.LocallyIntegrableOn G (Set.Ioi (0 : ℝ)) :=
    hG_continuousOn.locallyIntegrableOn measurableSet_Ioi
  -- Rapid decay of G via composition with `t / N`.
  have hG_top : ∀ r : ℝ, Asymptotics.IsBigO Filter.atTop
      (fun x : ℝ => G x - 0) (fun x : ℝ => x ^ r) := by
    intro r
    -- imAxis twist has rapid polynomial decay.
    have h_twist_decay :=
      (_root_.ModularForms.HasImAxisRapidDecay_of_HasImAxisExponentialDecay
        twist (Newform.cuspForm_Gamma1_hasImAxisExponentialDecay twist)) r
    -- Pull back via `t → t/N`.
    have h_tendsto : Filter.Tendsto (fun t : ℝ => t / (N : ℝ))
        Filter.atTop Filter.atTop :=
      Filter.tendsto_id.atTop_div_const hN_pos
    -- Build the bound directly.
    refine (h_twist_decay.comp_tendsto h_tendsto).trans ?_
    -- After comp_tendsto, the bound function is `((fun s => s^r) ∘ (fun t => t/N))`.
    -- Show this `=O[atTop] (fun t => t^r)`.
    refine Asymptotics.IsBigO.of_bound (((N : ℝ) ^ (-r))) ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
    -- After Function.comp simp, the LHS norm is `‖(t/N)^r‖`.
    simp only [Function.comp_apply]
    -- Goal: ‖(t/N)^r‖ ≤ N^(-r) · ‖t^r‖.
    have h_div_rpow : (t / (N : ℝ)) ^ r = (N : ℝ) ^ (-r) * t ^ r := by
      rw [Real.div_rpow ht.le hN_pos.le, Real.rpow_neg hN_pos.le, div_eq_mul_inv]
      ring
    rw [h_div_rpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hN_pos (-r))]
  -- h_feq : derived from imAxis_feq_of_slashEq.
  have h_feq : ∀ x ∈ Set.Ioi (0 : ℝ),
      Newform.imAxis f (1 / x) = (ε * ((x ^ (k : ℝ) : ℝ) : ℂ)) • G x := by
    intro x hx
    have h := Newform.imAxis_feq_of_slashEq f twist slash_eq hx
    -- Cast: ((x ^ (k : ℝ) : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ (k : ℤ).
    have h_cast : ((x ^ (k : ℝ) : ℝ) : ℂ) = ((x : ℝ) : ℂ) ^ k := by
      rw [Real.rpow_intCast x k, Complex.ofReal_zpow]
    show Newform.imAxis f (1 / x) =
      (((N : ℂ) ^ (1 - k) * Complex.I ^ k) * ((x ^ (k : ℝ) : ℝ) : ℂ)) •
        _root_.ModularForms.imAxis twist (x / (N : ℝ))
    rw [h, h_cast, smul_eq_mul]
  exact {
    G := G
    ε := ε
    hG_int := hG_int
    hk_pos := hk_pos
    hε_ne := hε_ne
    h_feq := h_feq
    hF_top := Newform.imAxis_rapidDecay f
    hG_top := hG_top
    h_bridge := h_bridge
  }

/-- **Analytic incompatibility under bad-prime hypothesis (T132).**
For every newform `f : Newform N k` in a Nebentypus character
eigenspace `modFormCharSpace k χ` and every finite exceptional set
`S : Finset ℕ`, the bad-prime-zero hypothesis
`∀ q prime, q.Coprime N → q ∉ S → f.lCoeff q = 0`
forces the stripped Dirichlet series `LSeries f.lCoeff_stripped` to
*not* admit an entire extension to `ℂ`.

This is the analytic content extracted by combining T111
(`Newform.lSeries_stripped_eq_dirichlet_quotient_value`) with the
identity theorem for analytic functions: under bad-prime-zero, the
stripped LSeries equals an explicit Dirichlet quotient on the
half-plane `Re s > k/2 + 1`; the Dirichlet quotient extends
meromorphically to `ℂ` (via Mathlib's `completedLFunction`) but has
known poles (from zeros of `LSeries χ̃` in the denominator), so any
entire extension of the stripped LSeries would force the Dirichlet
quotient to be entire — a contradiction.

**Status.**  This proposition encapsulates the Diamond–Shurman §5.9 /
Miyake §4.5.16 contradiction step in clean named-Prop form.  Its
formal proof requires (a) the meromorphic continuation of the
Dirichlet quotient (already in Mathlib) and (b) explicit Dirichlet
L-zero / pole tracking, both of which are independently approachable. -/
def Newform.NoEntireExtensionUnderBadPrime : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
    f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
    ∀ (S : Finset ℕ),
      (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
        q ∉ S → f.lCoeff q = 0) →
      ¬ LSeries.HasEntireExtension f.lCoeff_stripped

/-- **Bridge: structured analytic decomposition implies AnalyticContradiction (T132).**

Combining `Newform.HeckeEntireExtension` (every newform's stripped
LSeries extends entirely) and `Newform.NoEntireExtensionUnderBadPrime`
(under bad-prime, the stripped LSeries cannot extend entirely)
trivially produces `Newform.AnalyticContradiction`.

**Decomposition rationale.**  This bridge re-expresses the original
raw `AnalyticContradiction` as **two independently formalisable
analytic obligations**:

1. `HeckeEntireExtension`: prove via Mellin transform / `WeakFEPair`
   machinery in `Mathlib.NumberTheory.LSeries.AbstractFuncEq`.
2. `NoEntireExtensionUnderBadPrime`: prove via T111 + identity theorem
   `LSeries.HasEntireExtension.unique` + Dirichlet pole tracking.

Each obligation is independently approachable; the bridge proof is a
3-line case-split. -/
theorem Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    (h_hecke : Newform.HeckeEntireExtension)
    (h_no : Newform.NoEntireExtensionUnderBadPrime) :
    Newform.AnalyticContradiction := by
  intro N _ k f χ hfχ S h_bad
  exact h_no f χ hfχ S h_bad (h_hecke f)

/-- **Bridge: per-newform Dirichlet meromorphic-pole obligation reduces to
`NoEntireExtensionUnderBadPrime` (T132 next step).**

If, for every newform-character pair `(f, χ)` and finite exceptional set `S`
satisfying the bad-prime-zero hypothesis, the stripped Dirichlet series
`LSeries f.lCoeff_stripped` admits a meromorphic extension with a pole
(`LSeries.HasMeromorphicExtensionWithPole`), then
`Newform.NoEntireExtensionUnderBadPrime` follows.

**Decomposition rationale.**  This bridge replaces the abstract
"no entire extension" obligation by the concrete and reusable
`LSeries.HasMeromorphicExtensionWithPole` predicate, which packages the
analytic obligation as three named clauses:

* a meromorphic-extension witness `g : ℂ → ℂ` (the explicit T111
  Dirichlet quotient),
* a pole point `s₀ : ℂ` with `meromorphicOrderAt g s₀ < 0` (a Dirichlet
  zero in the appropriate strip), and
* the analytic-continuation hypothesis "any entire `F` agreeing with
  `LSeries f.lCoeff_stripped` on the half-plane coincides with `g` on
  a punctured nbhd of `s₀`" — automatic from T111 + entire-extension
  uniqueness (`LSeries.HasEntireExtension.unique`).

The proof is a 3-line forwarder via
`LSeries.HasMeromorphicExtensionWithPole.not_hasEntireExtension`. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_meromorphicPole
    (h : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        LSeries.HasMeromorphicExtensionWithPole f.lCoeff_stripped) :
    Newform.NoEntireExtensionUnderBadPrime := by
  intro N _ k f χ hfχ S h_bad
  exact LSeries.HasMeromorphicExtensionWithPole.not_hasEntireExtension
    (h f χ hfχ S h_bad)

/-- **Per-newform Dirichlet-quotient pole obligation under bad-prime
(T132 next-step).**

A clean structured analytic obligation that, for every newform-character
pair `(f, χ)` and finite exceptional set `S` satisfying the bad-prime
hypothesis, exhibits the T111 Dirichlet-quotient `num/den` as a
meromorphic-extension witness for `LSeries f.lCoeff_stripped`, with
explicit fields:

* `num : ℂ → ℂ` — the T111 numerator (concretely
  `LSeries χ̃² (2*(2s-k+1)) * (∏ T finite-correction)`), meromorphic
  at the pole point `s₀`, with **finite** order at `s₀`.
* `den : ℂ → ℂ` — the T111 denominator (concretely
  `LSeries χ̃ (2s-k+1) * (∏ T finite-correction)`), meromorphic
  at `s₀`, with **finite** order at `s₀`.
* `s₀ : ℂ` — the pole location (concretely a zero of
  `LSeries χ̃ (2s₀-k+1)`).
* `meromorphicOrderAt num s₀ < meromorphicOrderAt den s₀` — the strict
  order inequality forcing the quotient to have a pole at `s₀`.
* The analytic-continuation clause: any entire extension `F` of
  `LSeries f.lCoeff_stripped` coincides with `num/den` on a punctured
  neighbourhood of `s₀` (automatic from T111 + entire-extension
  uniqueness, in the T132 application).

This Prop is the precise reusable Dirichlet input that, combined with
`meromorphicOrderAt_div_neg_of_orderAt_lt` from `LFunction.lean`,
discharges `Newform.NoEntireExtensionUnderBadPrime` via the existing
forwarder `Newform.noEntireExtensionUnderBadPrime_of_meromorphicPole`.

**Status.**  The remaining external analytic input is now narrowed
to one explicit per-newform construction: produce `num`, `den` from
T111's `Newform.lSeries_stripped_eq_dirichlet_quotient_value`, the
analytic-continuation clause from T111 + uniqueness, the local
meromorphy from `differentiable_completedLFunction`, and the strict
order inequality from a single Dirichlet zero
`LSeries χ̃ (2 s₀ - k + 1) = 0` (the only genuinely missing classical
input, blocked from `Re ≥ 1` by `LFunction_ne_zero_of_one_le_re`). -/
def Newform.DirichletQuotientHasPoleUnderBadPrime : Prop :=
  ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
    f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
    ∀ (S : Finset ℕ),
      (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
        q ∉ S → f.lCoeff q = 0) →
      ∃ (num den : ℂ → ℂ) (s₀ : ℂ),
        MeromorphicAt num s₀ ∧
        MeromorphicAt den s₀ ∧
        meromorphicOrderAt num s₀ ≠ ⊤ ∧
        meromorphicOrderAt den s₀ ≠ ⊤ ∧
        meromorphicOrderAt num s₀ < meromorphicOrderAt den s₀ ∧
        ∀ F : ℂ → ℂ, Differentiable ℂ F →
          (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
            F s = LSeries f.lCoeff_stripped s) →
          F =ᶠ[nhdsWithin s₀ {s₀}ᶜ] (num / den)

/-- **Bridge: per-newform Dirichlet-quotient pole obligation forwards to
`Newform.NoEntireExtensionUnderBadPrime` (T132 next-step).**

Combines the per-newform Dirichlet-quotient pole input (numerator,
denominator, pole point, order strict inequality, analytic-continuation
clause) with the T132 helper
`meromorphicOrderAt_div_neg_of_orderAt_lt` (from `LFunction.lean`) to
produce the pole-side meromorphic-extension witness `g := num / den`,
then forwards through
`Newform.noEntireExtensionUnderBadPrime_of_meromorphicPole`.

**Decomposition rationale.**  This bridge narrows the structured
analytic obligation to **one** explicit per-newform construction:
exhibit the T111 Dirichlet-quotient numerator, denominator, pole
point, and the strict order inequality `order num s₀ < order den s₀`.
The remaining classical input is the existence of a Dirichlet zero
in the appropriate strip — well-known but not yet in Mathlib as a
single named lemma. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole
    (h : Newform.DirichletQuotientHasPoleUnderBadPrime) :
    Newform.NoEntireExtensionUnderBadPrime := by
  apply Newform.noEntireExtensionUnderBadPrime_of_meromorphicPole
  intro N _ k f χ hfχ S h_bad
  obtain ⟨num, den, s₀, h_num_mero, h_den_mero, h_num_finite, h_den_finite,
          h_lt, h_punc⟩ := h f χ hfχ S h_bad
  refine ⟨num / den, s₀, h_num_mero.div h_den_mero, ?_, h_punc⟩
  exact meromorphicOrderAt_div_neg_of_orderAt_lt h_num_mero h_den_mero
    h_num_finite h_den_finite h_lt

/-- **Per-newform pole witness from one explicit Dirichlet zero (T132 step).**

Given a newform-character pair `(f, χ)`, an explicit pole point
`s₀ : ℂ`, plus the **minimal classical analytic input**:

* `h_χ_ne_one` — non-triviality `χ̃ = dirichletLift χ ≠ 1`
  (so `LFunction χ̃` is entire, no Riemann ζ pole at `s' = 1`).
* `h_chi_sq_ne_one` — non-triviality `χ̃² ≠ 1` (so `LFunction χ̃²` is entire).
* `h_den_zero` — the explicit Dirichlet L-function zero
  `LFunction χ̃ (2 s₀ - k + 1) = 0`.  This is the **single irreducible
  classical input**: the existence of a Dirichlet zero on the
  appropriate strip `Re < 1` (mathlib already rules out zeros at
  `Re ≥ 1` via `LFunction_ne_zero_of_one_le_re`).
* `h_num_ne_zero` — the non-cancellation
  `LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0`.
* `h_univ_F` — the analytic-continuation universal-F clause connecting
  any entire extension of `LSeries f.lCoeff_stripped` to the
  meromorphic Dirichlet quotient on a punctured neighbourhood of `s₀`
  (automatic from T111 `Newform.lSeries_stripped_eq_dirichlet_quotient_value`
  + `LSeries.HasEntireExtension.unique`).

We exhibit the existential witness `(num, den, s₀)` for the inner ∃
of `Newform.DirichletQuotientHasPoleUnderBadPrime`.  All six fields
are filled mechanically from existing Mathlib API:

* `num`, `den` — the Dirichlet `LFunction` quotient at the shifted
  argument `s ↦ 2 s - k + 1`.
* `MeromorphicAt num/den s₀` — from `differentiable_LFunction`
  (Mathlib) + composition with the affine map + `Differentiable →
  AnalyticAt → MeromorphicAt`.
* `meromorphicOrderAt num/den s₀ ≠ ⊤` — from
  `analyticOrderAt_ne_top_of_isPreconnected` (Mathlib) on connected
  `ℂ`, with non-vanishing witnessed at `Re > 1` via
  `LFunction_eq_LSeries` + `LSeries_ne_zero_of_one_lt_re`.
* `meromorphicOrderAt num s₀ < meromorphicOrderAt den s₀` — from
  `AnalyticAt.analyticOrderAt_eq_zero` (`= 0` from `num_ne_zero`) and
  `AnalyticAt.analyticOrderAt_ne_zero` (`≠ 0` from `den_zero`),
  comparing in `WithTop ℤ`.
* `univ_F` — directly from `h_univ_F`. -/
theorem Newform.dirichletQuotient_pole_witness_of_dirichletZero
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_den_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_ne_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
      (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_univ_F : ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
        F s = LSeries f.lCoeff_stripped s) →
      F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
        ((fun s => DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
          (2 * (2 * s - k + 1))) /
        (fun s => DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))) :
    ∃ (num den : ℂ → ℂ) (s₀' : ℂ),
      MeromorphicAt num s₀' ∧
      MeromorphicAt den s₀' ∧
      meromorphicOrderAt num s₀' ≠ ⊤ ∧
      meromorphicOrderAt den s₀' ≠ ⊤ ∧
      meromorphicOrderAt num s₀' < meromorphicOrderAt den s₀' ∧
      ∀ F : ℂ → ℂ, Differentiable ℂ F →
        (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
          F s = LSeries f.lCoeff_stripped s) →
        F =ᶠ[nhdsWithin s₀' {s₀'}ᶜ] (num / den) := by
  set num : ℂ → ℂ := fun s => DirichletCharacter.LFunction
    (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
    (2 * (2 * s - k + 1)) with hnum
  set den : ℂ → ℂ := fun s => DirichletCharacter.LFunction
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) with hden
  -- Differentiability (entirety) of num and den via differentiable_LFunction +
  -- composition with the affine map.
  have h_num_diff : Differentiable ℂ num :=
    (DirichletCharacter.differentiable_LFunction h_chi_sq_ne_one).comp (by fun_prop)
  have h_den_diff : Differentiable ℂ den :=
    (DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop)
  -- Analyticity at s₀.
  have h_num_an : AnalyticAt ℂ num s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_num_diff s₀ (Set.mem_univ _)
  have h_den_an : AnalyticAt ℂ den s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_den_diff s₀ (Set.mem_univ _)
  -- Pick a witness point with `Re > k/2 + 1` to land in the convergence half-plane.
  set s' : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ) with hs'_def
  -- Auxiliary: Re(2 s' - k + 1) = 5 > 1.
  have h_re_arg : (2 * s' - (k : ℂ) + 1).re = 5 := by
    simp [s', Complex.add_re, Complex.sub_re, Complex.mul_re,
      Complex.intCast_re, Complex.intCast_im]
    ring
  have h_re_gt_one : (1 : ℝ) < (2 * s' - (k : ℂ) + 1).re := by rw [h_re_arg]; norm_num
  -- Re(2 (2 s' - k + 1)) = 10 > 1.
  have h_re_arg_sq : (2 * (2 * s' - (k : ℂ) + 1)).re = 10 := by
    rw [Complex.mul_re, h_re_arg]
    simp [Complex.add_im, Complex.sub_im, Complex.mul_im, s', Complex.intCast_re,
      Complex.intCast_im]
    ring
  have h_re_sq_gt_one : (1 : ℝ) < (2 * (2 * s' - (k : ℂ) + 1)).re := by
    rw [h_re_arg_sq]; norm_num
  -- num and den are non-zero at s'.
  have h_num_ne_at_s' : num s' ≠ 0 := by
    show DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
      (2 * (2 * s' - k + 1)) ≠ 0
    rw [DirichletCharacter.LFunction_eq_LSeries _ h_re_sq_gt_one]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ h_re_sq_gt_one
  have h_den_ne_at_s' : den s' ≠ 0 := by
    show DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s' - k + 1) ≠ 0
    rw [DirichletCharacter.LFunction_eq_LSeries _ h_re_gt_one]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ h_re_gt_one
  -- Analyticity at s' for the order-non-top argument.
  have h_num_an_s' : AnalyticAt ℂ num s' :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_num_diff s' (Set.mem_univ _)
  have h_den_an_s' : AnalyticAt ℂ den s' :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_den_diff s' (Set.mem_univ _)
  -- Order-zero at s'.
  have h_num_order_s' : analyticOrderAt num s' = 0 :=
    h_num_an_s'.analyticOrderAt_eq_zero.mpr h_num_ne_at_s'
  have h_den_order_s' : analyticOrderAt den s' = 0 :=
    h_den_an_s'.analyticOrderAt_eq_zero.mpr h_den_ne_at_s'
  -- Order ≠ ⊤ at s' (since order = 0).
  have h_num_order_s'_ne_top : analyticOrderAt num s' ≠ ⊤ := h_num_order_s'.symm ▸ by simp
  have h_den_order_s'_ne_top : analyticOrderAt den s' ≠ ⊤ := h_den_order_s'.symm ▸ by simp
  -- Propagate finite order from s' to s₀ via the connected ℂ.
  have h_num_an_univ : AnalyticOnNhd ℂ num Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_num_diff
  have h_den_an_univ : AnalyticOnNhd ℂ den Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_den_diff
  have h_num_order_s₀_ne_top : analyticOrderAt num s₀ ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected h_num_an_univ isPreconnected_univ
      (Set.mem_univ _) (Set.mem_univ _) h_num_order_s'_ne_top
  have h_den_order_s₀_ne_top : analyticOrderAt den s₀ ≠ ⊤ :=
    AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected h_den_an_univ isPreconnected_univ
      (Set.mem_univ _) (Set.mem_univ _) h_den_order_s'_ne_top
  -- Order at s₀: num = 0, den ≠ 0 (and finite).
  have h_num_order_s₀ : analyticOrderAt num s₀ = 0 :=
    h_num_an.analyticOrderAt_eq_zero.mpr h_num_ne_zero
  have h_den_order_s₀_ne_zero : analyticOrderAt den s₀ ≠ 0 :=
    h_den_an.analyticOrderAt_ne_zero.mpr h_den_zero
  -- Now produce the existential witness.
  refine ⟨num, den, s₀, h_num_an.meromorphicAt, h_den_an.meromorphicAt,
    ?_, ?_, ?_, h_univ_F⟩
  · -- meromorphicOrderAt num s₀ ≠ ⊤
    rw [h_num_an.meromorphicOrderAt_eq, h_num_order_s₀]
    simp
  · -- meromorphicOrderAt den s₀ ≠ ⊤
    rw [h_den_an.meromorphicOrderAt_eq]
    intro h
    -- analyticOrderAt den s₀ ≠ ⊤, hence its WithTop ℤ image ≠ ⊤.
    rcases ENat.ne_top_iff_exists.mp h_den_order_s₀_ne_top with ⟨n, hn⟩
    rw [← hn] at h
    -- (n : ℕ∞).map (↑) = ((n : ℤ) : WithTop ℤ), which ≠ ⊤.
    simp at h
  · -- meromorphicOrderAt num s₀ < meromorphicOrderAt den s₀
    rw [h_num_an.meromorphicOrderAt_eq, h_den_an.meromorphicOrderAt_eq, h_num_order_s₀]
    -- Goal: ((0 : ℕ∞).map (↑)) < ((analyticOrderAt den s₀).map (↑))
    -- = (0 : WithTop ℤ) < ((analyticOrderAt den s₀).map (↑))
    rcases ENat.ne_top_iff_exists.mp h_den_order_s₀_ne_top with ⟨m, hm⟩
    rw [← hm]
    -- Goal: (0 : WithTop ℤ) < ((m : ℕ∞).map (↑))
    -- m ≥ 1 since order ≠ 0 and m corresponds to that order.
    have h_m_ge_one : 1 ≤ m := by
      rcases m with _ | m'
      · exfalso
        have : analyticOrderAt den s₀ = 0 := by rw [← hm]; rfl
        exact h_den_order_s₀_ne_zero this
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
    -- Now show 0 < ((m : ℕ∞).map (↑) : WithTop ℤ).
    show (((0 : ℕ∞)).map (↑) : WithTop ℤ) < ((m : ℕ∞).map (↑) : WithTop ℤ)
    simp only [ENat.map_zero, ENat.map_coe]
    show ((0 : ℤ) : WithTop ℤ) < ((m : ℕ) : WithTop ℤ)
    rw [show ((m : ℕ) : WithTop ℤ) = (((m : ℕ) : ℤ) : WithTop ℤ) from by push_cast; rfl,
        WithTop.coe_lt_coe]
    exact_mod_cast h_m_ge_one

/-- **Universal pole certificate ⇒ NoEntireExtensionUnderBadPrime
(T132 final reduction).**

Given, for every newform-character pair `(f, χ)` and finite exceptional
set `S` satisfying the bad-prime-zero hypothesis, the per-newform
**pole-certificate** data — pointwise:

* `s₀ : ℂ` — the explicit pole point;
* nontriviality `χ̃ ≠ 1`, `χ̃² ≠ 1`;
* the Dirichlet zero `LFunction χ̃ (2 s₀ - k + 1) = 0`;
* the non-cancellation `LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0`;
* the analytic-continuation universal-F clause from T111 + uniqueness;

we conclude `Newform.NoEntireExtensionUnderBadPrime`.

**Decomposition rationale.**  This forwarder closes the four-step
T132 reduction chain:

  certificate (5 fields per `(f, χ, S)`)
    ↓ via `Newform.dirichletQuotient_pole_witness_of_dirichletZero`
  inner ∃-witness for `DirichletQuotientHasPoleUnderBadPrime`
    ↓ via `Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole`
  `Newform.NoEntireExtensionUnderBadPrime`

The remaining genuinely-classical input is **one** named theorem per
newform: existence of a Dirichlet zero `LFunction χ̃ s₀' = 0` in the
strip `Re s₀' < 1`.  Mathlib's `LFunction_ne_zero_of_one_le_re` already
rules out `Re ≥ 1`; only the strip case is missing as a single named
classical lemma. -/
theorem Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (s₀ : ℂ),
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) ≠ 1 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)
            (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          ∀ F : ℂ → ℂ, Differentiable ℂ F →
            (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
              F s = LSeries f.lCoeff_stripped s) →
            F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
              ((fun s => DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N)
                (2 * (2 * s - k + 1))) /
              (fun s => DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1)))) :
    Newform.NoEntireExtensionUnderBadPrime := by
  apply Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole
  intro N _ k f χ hfχ S h_bad
  obtain ⟨s₀, h_χ_ne, h_χ_sq_ne, h_den_zero, h_num_ne, h_univ⟩ :=
    h_cert f χ hfχ S h_bad
  exact Newform.dirichletQuotient_pole_witness_of_dirichletZero f χ s₀
    h_χ_ne h_χ_sq_ne h_den_zero h_num_ne h_univ

/-- **Conditional Strong Multiplicity One via T132 analytic decomposition
(final T132 consumer).**

Combines the two T132 named analytic obligations into the original SMO
conclusion, with **only two hypotheses** that the next worker must
discharge classically:

1. `h_hecke : Newform.HeckeEntireExtension` — Hecke 1936 entire
   continuation of every newform's stripped Dirichlet series.
2. `h_cert` — pointwise Dirichlet-zero certificate family: for every
   newform-character pair `(f, χ)` with bad-prime-zero hypothesis,
   exhibit `s₀`, the non-trivialities `χ̃ ≠ 1`, `χ̃² ≠ 1`, the explicit
   Dirichlet zero `LFunction χ̃ (2 s₀ - k + 1) = 0`, the non-cancellation
   `LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0`, and the analytic-continuation
   universal-F clause from T111 + entire-extension uniqueness.

Both hypotheses are **strictly named, pointwise, and classically
formalisable** — no broad black-box `Prop` wrappers remain.  Mathlib's
`differentiable_LFunction`, `LFunction_eq_LSeries`,
`LSeries_ne_zero_of_one_lt_re`, `LFunction_ne_zero_of_one_le_re`, and
`AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected` discharge all
the auxiliary order-arithmetic and meromorphic-continuity facts inside
the per-newform pole witness.

**Chain:**

  `h_cert` (pointwise) → `Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate`
                       → `Newform.NoEntireExtensionUnderBadPrime`
  `h_hecke` ∧ above → `Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime`
                    → `Newform.AnalyticContradiction`
  → `strongMultiplicityOne_of_analyticContradiction` → SMO. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate
    (h_hecke : Newform.HeckeEntireExtension)
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (s₀ : ℂ),
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) ≠ 1 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)
            (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          ∀ F : ℂ → ℂ, Differentiable ℂ F →
            (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
              F s = LSeries f.lCoeff_stripped s) →
            F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
              ((fun s => DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N)
                (2 * (2 * s - k + 1))) /
              (fun s => DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1))))
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  have h_no_ext : Newform.NoEntireExtensionUnderBadPrime :=
    Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate h_cert
  have h_ana : Newform.AnalyticContradiction :=
    Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
      h_hecke h_no_ext
  exact strongMultiplicityOne_of_analyticContradiction h_ana f g χ hfχ hgχ S h

/-- **Conditional Strong Multiplicity One via T132 + explicit `newform_unique`
hypothesis (axiom-clean variant).**

Mirrors `strongMultiplicityOne_of_analyticContradiction` but takes
`newform_unique`'s usable content as an explicit hypothesis `h_unique`,
isolating T132's analytic chain from the upstream `newform_unique`
(currently `sorryAx`-dependent through the Atkin-Lehner / mainLemma
uniqueness lane, separate from T132's analytic obligation).

The proof body is a copy of `strongMultiplicityOne_of_analyticContradiction`
with the call to `newform_unique` replaced by `h_unique`; the analytic
nonvanishing step still uses
`Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction` (clean
axioms) — so this conditional variant has only standard axioms plus the
explicit `h_unique` and `h_ana` hypotheses. -/
theorem strongMultiplicityOne_of_analyticContradiction_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_ana : Newform.AnalyticContradiction)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  refine h_unique f g χ hfχ hgχ ?_
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

/-- **Final T132 conditional consumer (axiom-clean variant).**

Combines the two T132 named analytic obligations
(`HeckeEntireExtension`, pointwise Dirichlet-zero certificate family)
with the explicit `newform_unique` hypothesis to produce the
Strong Multiplicity One conclusion.  All three hypotheses are **strictly
named, pointwise, and classically formalisable**:

* `h_unique` — the standard Atkin-Lehner-style uniqueness statement
  (currently provable in the repo modulo upstream `mainLemma` /
  oldform-newform structure, but factored out here so T132's analytic
  bridge is independently axiom-clean).
* `h_hecke : Newform.HeckeEntireExtension` — Hecke 1936's entire
  continuation of every newform's stripped Dirichlet series.
* `h_cert` — pointwise per-newform Dirichlet-zero certificate family
  (one explicit `s₀`, character non-trivialities, `LFunction χ̃` zero,
  `LFunction χ̃²` non-cancellation, T111-derived universal-F clause).

This conditional theorem has axiom set `[propext, Classical.choice,
Quot.sound]` plus the explicit hypotheses — no `sorryAx`. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_hecke : Newform.HeckeEntireExtension)
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (s₀ : ℂ),
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) ≠ 1 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)
            (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
          ∀ F : ℂ → ℂ, Differentiable ℂ F →
            (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
              F s = LSeries f.lCoeff_stripped s) →
            F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
              ((fun s => DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N)
                (2 * (2 * s - k + 1))) /
              (fun s => DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1))))
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  have h_no_ext : Newform.NoEntireExtensionUnderBadPrime :=
    Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate h_cert
  have h_ana : Newform.AnalyticContradiction :=
    Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
      h_hecke h_no_ext
  exact strongMultiplicityOne_of_analyticContradiction_of_newformUnique
    h_unique h_ana f g χ hfχ hgχ S h

/-- **Named Dirichlet-zero certificate (T132 reusable public API).**

The per-newform analytic certificate consumed by the T132 chain:

1. an explicit pole point `s₀ : ℂ`;
2. non-triviality of the lifted Dirichlet character `χ̃ ≠ 1`;
3. non-triviality of the squared lift `χ̃² ≠ 1`;
4. the explicit Dirichlet L-function zero
   `LFunction χ̃ (2 s₀ - k + 1) = 0` — the **single** classical analytic
   obligation the next worker must discharge (Mathlib's
   `LFunction_ne_zero_of_one_le_re` already handles `Re ≥ 1`);
5. the non-cancellation `LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0`;
6. the analytic-continuation universal-F clause connecting any entire
   extension of `LSeries f.lCoeff_stripped` to the meromorphic
   Dirichlet quotient on a punctured nbhd of `s₀`.

Wraps the previous inline existential into a single named `Prop`, so
public T132 API consumers can refer to "the per-newform pole certificate"
as a first-class predicate instead of repeating the 6-clause body.

The downstream public consumers
`Newform.noEntireExtensionUnderBadPrime_of_HasDirichletZeroCertificate`
and the SMO chain
`strongMultiplicityOne_of_HeckeEntireExtension_of_HasDirichletZeroCertificate_of_newformUnique`
take a single hypothesis `∀ ⦃N⦄ ⦃k⦄ f χ hfχ S, bad-prime →
HasDirichletZeroCertificate f χ` rather than the open-form 6-clause
existential. -/
def Newform.HasDirichletZeroCertificate
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ) :
    Prop :=
  ∃ (s₀ : ℂ),
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1 ∧
    (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1 ∧
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0 ∧
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)
      (2 * (2 * s₀ - k + 1)) ≠ 0 ∧
    ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
        F s = LSeries f.lCoeff_stripped s) →
      F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
        ((fun s => DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)
          (2 * (2 * s - k + 1))) /
        (fun s => DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))

/-- **Public consumer: certificate ⇒ NoEntireExtensionUnderBadPrime
(T132 named-API variant).**

Same content as
`Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate`
but with the per-newform certificate hypothesis written as
`Newform.HasDirichletZeroCertificate` (the named Prop). -/
theorem Newform.noEntireExtensionUnderBadPrime_of_HasDirichletZeroCertificate
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.HasDirichletZeroCertificate f χ) :
    Newform.NoEntireExtensionUnderBadPrime :=
  Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate h_cert

/-- **Public consumer: HeckeEntireExtension + certificate + newform_unique
⇒ Strong Multiplicity One (T132 named-API final variant).**

Same content as
`strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate_of_newformUnique`
but with the per-newform certificate hypothesis written as
`Newform.HasDirichletZeroCertificate`. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_HasDirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_hecke : Newform.HeckeEntireExtension)
    (h_cert : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        Newform.HasDirichletZeroCertificate f χ)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm :=
  strongMultiplicityOne_of_HeckeEntireExtension_of_dirichletZeroCertificate_of_newformUnique
    h_unique h_hecke h_cert f g χ hfχ hgχ S h

/-- **Strictly reducing constructor for the named Dirichlet-zero
certificate (T132 step).**

Builds `Newform.HasDirichletZeroCertificate f χ` directly from the
minimal classical Dirichlet inputs:

* `s₀ : ℂ` — the explicit pole point (typically a Dirichlet zero in the
  strip `Re < 1`);
* `h_χ_ne_one` — non-triviality of the lifted character `χ̃ ≠ 1`
  (rules out the Riemann-ζ pole at `s' = 1`);
* `h_chi_sq_ne_one` — non-triviality of the squared lift `χ̃² ≠ 1`;
* `h_den_zero` — the explicit Dirichlet L-function zero
  `LFunction χ̃ (2 s₀ - k + 1) = 0`.  This is the **single irreducible
  classical input**: existence of a Dirichlet zero in `Re s' < 1`.
  Mathlib's `LFunction_ne_zero_of_one_le_re` already rules out
  `Re s' ≥ 1`; only the strip case is missing as a single named lemma;
* `h_num_ne_zero` — the non-cancellation
  `LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0`;
* `h_univ_F` — the analytic-continuation universal-F clause.

The universal-F clause `h_univ_F` is **kept explicit** as the minimal
analytic-continuation hypothesis: deriving it from T111
(`Newform.lSeries_stripped_eq_dirichlet_quotient_value`) plus
`LSeries.HasEntireExtension.unique` would require the identity theorem
on the connected open set `ℂ \ {poles of LFunction χ̃ (2s - k + 1)}`,
plus a non-cancellation argument for the finite Euler-factor
corrections in T111's full quotient.  Both are formalisable but not
yet packaged as reusable lemmas in this repo.

**Use.**  Downstream consumers no longer pattern-match on the bulky
6-clause inline existential — they instead provide the 6 named
parameters to this constructor and obtain `HasDirichletZeroCertificate`
in a single step. -/
theorem Newform.HasDirichletZeroCertificate_of_dirichletZero
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_den_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_ne_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
      (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_univ_F : ∀ F : ℂ → ℂ, Differentiable ℂ F →
      (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
        F s = LSeries f.lCoeff_stripped s) →
      F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
        ((fun s => DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)
          (2 * (2 * s - k + 1))) /
        (fun s => DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))) :
    Newform.HasDirichletZeroCertificate f χ :=
  ⟨s₀, h_χ_ne_one, h_chi_sq_ne_one, h_den_zero, h_num_ne_zero, h_univ_F⟩

/-- **Named universal-F clause: simplified Dirichlet quotient (T132 step).**

The analytic-continuation hypothesis with the **simplified** Dirichlet
quotient `LFunction χ̃² (2(2s-k+1)) / LFunction χ̃ (2s-k+1)` (no finite
Euler-factor corrections).  Used inside `Newform.HasDirichletZeroCertificate`.

**Mathematical correctness note.**  T111
(`Newform.lSeries_stripped_eq_dirichlet_quotient_value`) does **not**
directly produce this simplified clause: T111 gives equality with the
**full** Dirichlet quotient
`(LFunction χ̃² · ∏_T num-correction) / (LFunction χ̃ · ∏_T den-correction)`,
where the finite Euler-factor correction products depend on `S`, the
finite exceptional prime set, and `T`, the primes in `S` coprime to `N`.

The simplified form coincides with T111's full RHS exactly in the
specialisation `T = ∅` (i.e. when the exceptional set `S` contains no
primes coprime to `N`); this is captured by
`Newform.simplified_eq_full_DirichletQuotientUniversalFClause_T_empty`
below.

In general, downstream callers wanting a T111-derived analytic
obligation should refer to the full-quotient clause
`Newform.FullDirichletQuotientUniversalFClause`; the simplified form
remains available as a convenience for `T = ∅` workflows. -/
def Newform.DirichletQuotientUniversalFClause
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ) : Prop :=
  ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      F s = LSeries f.lCoeff_stripped s) →
    F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
      ((fun s => DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)
        (2 * (2 * s - k + 1))) /
      (fun s => DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)))

/-- **Strictly reducing constructor (T132 step, named-clause variant).**

Same as `Newform.HasDirichletZeroCertificate_of_dirichletZero` but
takes the universal-F clause via the named Prop
`Newform.DirichletQuotientUniversalFClause f χ s₀` instead of the raw
`∀ F` quantified hypothesis.  Downstream code can refer to the analytic-
continuation obligation by name, keeping certificate construction
sites compact. -/
theorem Newform.HasDirichletZeroCertificate_of_dirichletZero_of_clause
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_den_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_ne_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
      (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_clause : Newform.DirichletQuotientUniversalFClause f χ s₀) :
    Newform.HasDirichletZeroCertificate f χ :=
  Newform.HasDirichletZeroCertificate_of_dirichletZero f χ s₀
    h_χ_ne_one h_chi_sq_ne_one h_den_zero h_num_ne_zero h_clause

/-- **Trivial unfolding lemma: named clause ↔ raw `∀ F` clause.**

The named `Newform.DirichletQuotientUniversalFClause` is *definitionally*
the raw `∀ F` clause used inline by
`Newform.dirichletQuotient_pole_witness_of_dirichletZero`.  This lemma
provides the explicit unfolding for callers chaining named-clause
hypotheses through the per-newform pole witness. -/
theorem Newform.DirichletQuotientUniversalFClause_iff
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ) :
    Newform.DirichletQuotientUniversalFClause f χ s₀ ↔
      ∀ F : ℂ → ℂ, Differentiable ℂ F →
        (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
          F s = LSeries f.lCoeff_stripped s) →
        F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
          ((fun s => DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)
            (2 * (2 * s - k + 1))) /
          (fun s => DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1))) :=
  Iff.rfl

/-- **Named universal-F clause: FULL T111 Dirichlet quotient (T132 step).**

The analytic-continuation hypothesis matching T111's RHS
**exactly** — including the finite Euler-factor correction products
parameterised by the exceptional set `S` and its `T` of primes coprime
to `N`.

Numerator: `LFunction χ̃² (2(2s-k+1)) · ∏ p ∈ T, eulerFactor_stripped f χ S s p
            · (1 - χ̃(p) · p^{-(2s-k+1)})⁻¹`

Denominator: `LFunction χ̃ (2s-k+1) · ∏ p ∈ T, (1 - χ̃²(p) · p^{-(2(2s-k+1))})⁻¹`

This is the clause that
`Newform.lSeries_stripped_eq_dirichlet_quotient_value` (T111) actually
produces (modulo the `LSeries`-vs-`LFunction` identification on the
right half-plane via `LFunction_eq_LSeries`); naming it here gives
downstream callers a stable T111-aligned API.

**Use.**  Pole-witness constructors should consume this full clause
when the exceptional set `T` is potentially non-empty; the simplified
clause `Newform.DirichletQuotientUniversalFClause` is the `T = ∅`
specialisation, captured by
`Newform.simplified_eq_full_DirichletQuotientUniversalFClause_T_empty`. -/
def Newform.FullDirichletQuotientUniversalFClause
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ) : Prop :=
  ∀ F : ℂ → ℂ, Differentiable ℂ F →
    (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
      F s = LSeries f.lCoeff_stripped s) →
    F =ᶠ[nhdsWithin s₀ {s₀}ᶜ]
      ((fun s =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) /
      (fun s =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          (2 * s - k + 1) *
        ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹))

/-- **The simplified universal-F clause is the `T = ∅` specialisation
of the full T111 universal-F clause (T132 step).**

When the exceptional finset of primes `T` is empty, the finite
Euler-factor products in `Newform.FullDirichletQuotientUniversalFClause`
collapse to `1`, and the full clause reduces to the simplified
clause `Newform.DirichletQuotientUniversalFClause`.

This explicitly shows the simplified clause is **not** a free
T111-derived consequence in the general case: it requires the
exceptional set `T` to be empty (i.e., `S` contains no primes coprime
to `N` — a condition that can always be arranged at the cost of
restricting `S`). -/
theorem Newform.simplified_eq_full_DirichletQuotientUniversalFClause_T_empty
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (s₀ : ℂ) :
    Newform.FullDirichletQuotientUniversalFClause f χ S ∅ s₀ ↔
      Newform.DirichletQuotientUniversalFClause f χ s₀ := by
  unfold Newform.FullDirichletQuotientUniversalFClause
    Newform.DirichletQuotientUniversalFClause
  simp only [Finset.prod_empty, mul_one]

/-- **Universal-F clause from a half-plane T111 identity (T132 H2 reduction).**

Reduces `Newform.DirichletQuotientUniversalFClause f χ s₀` (the
simplified `T = ∅` universal-F clause) to a **half-plane multiplicative
identity hypothesis**: if for some `σ : ℝ` strictly above the
absolute-convergence abscissa, the multiplicative form

`LSeries f.lCoeff_stripped s · (LFunction χ̃ (2s-k+1)) =
   LFunction χ̃² (2(2s-k+1))`

holds for every `s` with `Re s > σ`, then the universal-F clause holds
at any point `s₀ : ℂ`.

**Mathematical content** (Diamond–Shurman §5.9 / Miyake §4.5.15–4.5.16).

The half-plane identity is the multiplicative reformulation of the
T111 Dirichlet-quotient identity
(`Newform.lSeries_stripped_eq_dirichlet_quotient_value`) at `T = ∅`,
where the finite Euler-factor product collapses to `1`.  In this form
no division appears, sidestepping the bookkeeping of pointwise
non-vanishing of `LFunction χ̃` on the half-plane.

**Proof structure.**

1. Take any differentiable `F` extending `LSeries f.lCoeff_stripped`
   on its abscissa half-plane.
2. On the open half-plane `{Re s > σ}`, both `F = LSeries` (from the
   abscissa hypothesis, since `σ > abscissa`) and the half-plane
   identity hold, so `F · den - num = 0` there.
3. Both `num`, `den` are entire (via
   `DirichletCharacter.differentiable_LFunction` for nontrivial χ̃, χ̃²),
   so `F · den - num` is entire.
4. By the **identity theorem**
   (`AnalyticOnNhd.eq_of_eventuallyEq` on the connected `ℂ`),
   `F · den - num ≡ 0` on all of `ℂ`.
5. `den` is non-trivially nonzero (witness: `den (k/2 + 2 : ℝ) ≠ 0`
   via `LFunction_eq_LSeries` + `LSeries_ne_zero_of_one_lt_re`), hence
   not eventually zero at any point.  So `den ≠ 0` on a punctured
   neighbourhood of `s₀`.
6. From `F · den = num` and `den ≠ 0` on the punctured nbhd,
   `F = num / den` there.

The hypothesis `h_halfPlane_id` is exactly the **classical T111
identity** (multiplicative form, `T = ∅`), which is the genuinely
missing analytic input not yet proven uniformly on a half-plane in
the local repo.  Keeping it as a named hypothesis isolates the
remaining gap precisely. -/
theorem Newform.DirichletQuotientUniversalFClause_of_halfPlane_identity
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (σ : ℝ)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped < (σ : EReal))
    (h_halfPlane_id : ∀ s : ℂ, σ < s.re →
      LSeries f.lCoeff_stripped s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) =
        DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s - k + 1))) :
    Newform.DirichletQuotientUniversalFClause f χ s₀ := by
  intro F hF h_F_eq
  set num : ℂ → ℂ := fun s => DirichletCharacter.LFunction
    (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
    (2 * (2 * s - k + 1)) with hnum_def
  set den : ℂ → ℂ := fun s => DirichletCharacter.LFunction
    (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) with hden_def
  have h_num_diff : Differentiable ℂ num :=
    (DirichletCharacter.differentiable_LFunction h_chi_sq_ne_one).comp (by fun_prop)
  have h_den_diff : Differentiable ℂ den :=
    (DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop)
  have h_eq_halfPlane : ∀ s : ℂ, σ < s.re → F s * den s = num s := by
    intro s hs
    have hs_abscissa : LSeries.abscissaOfAbsConv f.lCoeff_stripped < (s.re : EReal) :=
      lt_of_lt_of_le h_abscissa_lt (by exact_mod_cast hs.le)
    rw [h_F_eq hs_abscissa]
    exact h_halfPlane_id s hs
  have h_g_diff : Differentiable ℂ (fun s => F s * den s - num s) :=
    (hF.mul h_den_diff).sub h_num_diff
  let z₀ : ℂ := ((σ + 1 : ℝ) : ℂ)
  have hz₀_re : σ < z₀.re := by
    show σ < ((σ + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]; linarith
  have h_open : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h_g_eventually_zero :
      (fun s : ℂ => F s * den s - num s) =ᶠ[nhds z₀] (fun _ : ℂ => 0) :=
    (h_open.eventually_mem hz₀_re).mono (fun s hs => by
      show F s * den s - num s = 0
      rw [sub_eq_zero]
      exact h_eq_halfPlane s hs)
  have h_g_an : AnalyticOnNhd ℂ (fun s => F s * den s - num s) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_g_diff
  have h_zero_an : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ :=
    fun _ _ => analyticAt_const
  have h_g_eq_zero : (fun s => F s * den s - num s) = fun _ : ℂ => 0 :=
    h_g_an.eq_of_eventuallyEq h_zero_an h_g_eventually_zero
  have h_F_den_eq_num : ∀ s : ℂ, F s * den s = num s := fun s => by
    have h_g_s : F s * den s - num s = 0 := congrFun h_g_eq_zero s
    exact sub_eq_zero.mp h_g_s
  set s' : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ) with hs'_def
  have h_re_gt_one : (1 : ℝ) < (2 * s' - (k : ℂ) + 1).re := by
    have h_re : (2 * s' - (k : ℂ) + 1).re = 5 := by
      simp [s', Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.intCast_re, Complex.intCast_im]
      ring
    rw [h_re]; norm_num
  have h_den_s' : den s' ≠ 0 := by
    show DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s' - k + 1) ≠ 0
    rw [DirichletCharacter.LFunction_eq_LSeries _ h_re_gt_one]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ h_re_gt_one
  have h_den_an_s₀ : AnalyticAt ℂ den s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_den_diff s₀ (Set.mem_univ _)
  have h_den_not_eventually_zero : ¬ ∀ᶠ s in nhds s₀, den s = 0 := by
    intro h_ev
    have h_den_an : AnalyticOnNhd ℂ den Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr h_den_diff
    have h_zero_an' : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ :=
      fun _ _ => analyticAt_const
    have h_den_eq_zero : den = (fun _ : ℂ => (0 : ℂ)) :=
      h_den_an.eq_of_eventuallyEq h_zero_an' (h_ev.mono (fun _ h => h))
    exact h_den_s' (congrFun h_den_eq_zero s')
  have h_den_punctured : ∀ᶠ s in nhdsWithin s₀ {s₀}ᶜ, den s ≠ 0 :=
    h_den_an_s₀.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      h_den_not_eventually_zero
  refine h_den_punctured.mono (fun s h_den_s_ne => ?_)
  show F s = num s / den s
  rw [eq_div_iff h_den_s_ne]
  exact h_F_den_eq_num s

/-- **Universal-F clause from T111 pointwise identity (T132 H2 reduction,
T = ∅).**

Discharges the half-plane multiplicative T111 identity hypothesis
`h_halfPlane_id` of
`Newform.DirichletQuotientUniversalFClause_of_halfPlane_identity`
**from the existing pointwise T111 theorem**
`Newform.lSeries_stripped_eq_dirichlet_quotient_value` instantiated
at `T = ∅`.

The geometric / pole side conditions of T111 (`hs, hs', hs''`,
`h_geom`, `h_pos_neg`) are derived **uniformly** for every `s` with
`(k : ℝ) / 2 + 1 < s.re` from the local helpers
`Newform.norm_eulerFactor_argument_lt_one`,
`Newform.norm_chi_q_cpow_neg_lt_one_of_re_pos`,
`Newform.one_add_ne_zero_of_norm_lt_one`,
`Newform.one_sub_ne_zero_of_norm_lt_one`.  Conversion of T111's RHS
from `LSeries (fun n => χ̃ n)` to `DirichletCharacter.LFunction χ̃`
uses `DirichletCharacter.LFunction_eq_LSeries` (valid because
`Re(2s - k + 1) > 3 > 1` and `Re(2(2s - k + 1)) > 6 > 1` on this
half-plane).

**Hypotheses kept explicit** (genuinely classical):

* `h_χ_ne_one`, `h_chi_sq_ne_one` — Dirichlet character non-triviality.
* `h_bad` — bad-prime-zero hypothesis (the per-newform input).
* `h_T_empty` — the **`T = ∅` selector**: `S` contains no primes
  coprime to `N`, so the T111 finset `T` characterised by
  `p ∈ T ↔ p ∈ S ∧ Coprime p N` is empty (cf. T111's `hT_iff`).
* `h_abscissa_lt` — abscissa of absolute convergence is strictly below
  `k/2 + 1` (the convergence half-plane).
* `hfχ` — character eigenspace membership (T111 input).

References: Diamond–Shurman §5.9, Miyake §4.5.15–4.5.16. -/
theorem Newform.DirichletQuotientUniversalFClause_of_T111_T_empty
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    (h_T_empty : ∀ p : Nat.Primes, ¬ ((p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N))
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped <
      (((k : ℝ) / 2 + 1 : ℝ) : EReal)) :
    Newform.DirichletQuotientUniversalFClause f χ s₀ := by
  refine Newform.DirichletQuotientUniversalFClause_of_halfPlane_identity f χ s₀
    h_χ_ne_one h_chi_sq_ne_one ((k : ℝ) / 2 + 1) h_abscissa_lt ?_
  intro s hs_re
  -- Real-part side conditions of T111.
  have h_re_eq : (2 * s - (k : ℂ) + 1).re = 2 * s.re - k + 1 := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re]
  have hs' : 1 < (2 * s - k + 1).re := by rw [h_re_eq]; linarith
  have h_re_eq_sq : (2 * (2 * s - (k : ℂ) + 1)).re = 4 * s.re - 2 * k + 2 := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re]
    ring
  have hs'' : 1 < (2 * (2 * s - k + 1)).re := by rw [h_re_eq_sq]; linarith
  -- Geometric / sign side conditions of T111, uniform on `Re s > k/2 + 1`.
  have h_geom : ∀ q : ℕ, ∀ (hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-s)) ^ 2‖ < 1 := by
    intro q hq hqN _
    have hs_ge : ((k : ℝ) - 1) / 2 < s.re := by linarith
    exact Newform.norm_eulerFactor_argument_lt_one χ k hq.two_le hqN _ hs_ge
  have h_pos_neg : ∀ q : ℕ, ∀ (hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 ∧
      (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 := by
    intro q hq hqN _
    have h_re_pos : (0 : ℝ) < (2 * s - (k : ℂ) + 1).re := by linarith
    have h_norm_lt :
        ‖(χ (ZMod.unitOfCoprime q hqN) : ℂ) *
          (q : ℂ) ^ (-(2 * s - k + 1))‖ < 1 :=
      Newform.norm_chi_q_cpow_neg_lt_one_of_re_pos χ hq.two_le hqN h_re_pos
    exact ⟨Newform.one_add_ne_zero_of_norm_lt_one h_norm_lt,
           Newform.one_sub_ne_zero_of_norm_lt_one h_norm_lt⟩
  -- The T111 finset `T = ∅` selector via `h_T_empty`.
  have hT_iff : ∀ p : Nat.Primes, p ∈ (∅ : Finset Nat.Primes) ↔
      (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N := by
    intro p
    refine iff_of_false (Finset.notMem_empty p) ?_
    exact h_T_empty p
  -- Apply T111 with T = ∅ and simplify the empty product.
  have h_T111 := f.lSeries_stripped_eq_dirichlet_quotient_value χ hfχ S h_bad
    hs_re hs' hs'' h_geom ∅ hT_iff h_pos_neg
  simp only [Finset.prod_empty, mul_one] at h_T111
  -- Convert LSeries χ̃ → LFunction χ̃ on `Re > 1` half-planes.
  have h_LF_eq : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) =
        LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1) :=
    DirichletCharacter.LFunction_eq_LSeries _ hs'
  have h_LF_sq_eq : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) =
        LSeries (fun n => (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) n) (2 * (2 * s - k + 1)) :=
    DirichletCharacter.LFunction_eq_LSeries _ hs''
  rw [h_LF_eq, h_LF_sq_eq]
  -- Multiplicative form: convert `LSeries = num/den` to `LSeries · den = num`.
  have h_den_ne :
      LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1) ≠ 0 :=
    DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ hs'
  rw [eq_div_iff h_den_ne] at h_T111
  exact h_T111

/-- **Full universal-F clause from the half-plane multiplicative entire
identity (T132 H2 reduction, general T).**

Reduces `Newform.FullDirichletQuotientUniversalFClause f χ S T s₀`
(the general-`T` universal-F clause, including the finite Euler-factor
correction products over `T`) to a **half-plane multiplicative entire
identity** between two polynomial-multiplied entire functions.

Specifically, after clearing the inverses `(...)⁻¹` from T111's RHS by
cross-multiplication, the resulting identity reads (on the half-plane
`Re s > σ`):

`LSeries f.lCoeff_stripped s · LFunction χ̃ (2s-k+1) ·
   ∏ p ∈ T, (1 - χ̃(p) · p^{-(2s-k+1)})
 = LFunction χ̃² (2(2s-k+1)) · (∏ p ∈ T, eulerFactor_stripped f χ S s p) ·
   ∏ p ∈ T, (1 - χ̃²(p) · p^{-(2(2s-k+1))})`

(both sides are entire products of entire functions, no inverses).

The bridge then closes the gap from the half-plane to a punctured
neighbourhood of `s₀` via the **identity theorem**, and converts back
to the meromorphic universal-F-clause RHS form using `Finset.prod_inv_distrib`
and pointwise non-vanishing of the linear factors at `s₀` (which by
continuity gives non-vanishing on a nbhd of `s₀`).

**Hypotheses kept explicit.**

* `h_χ_ne_one`, `h_chi_sq_ne_one` — Dirichlet character non-triviality.
* `σ : ℝ`, `h_abscissa_lt` — half-plane abscissa bound.
* `h_EFP_diff` — entirety of the per-prime Euler-factor product (the
  genuinely non-trivial analytic input for `p ∈ T`).
* `h_halfPlane_id` — the half-plane multiplicative entire identity
  (cleared of inverses), strictly closer to T111 than the raw
  arbitrary universal-F clause.
* `h_LinFP1_factor_ne_s₀`, `h_LinFP2_factor_ne_s₀` — pointwise
  non-vanishing at `s₀` of each linear factor in the two finite
  products (so by continuity each product is nonzero on a nbhd
  of `s₀`, giving a punctured nbhd where the inverses are well-defined).

References: Diamond–Shurman §5.9, Miyake §4.5.15–4.5.16. -/
theorem Newform.FullDirichletQuotientUniversalFClause_of_halfPlane_multIdentity
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (σ : ℝ)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped < (σ : EReal))
    (h_EFP_diff : Differentiable ℂ
      (fun s : ℂ => ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p))
    (h_halfPlane_id : ∀ s : ℂ, σ < s.re →
      LSeries f.lCoeff_stripped s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) *
        (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) =
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))))
    (h_LinFP1_factor_ne_s₀ : ∀ p ∈ T,
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_LinFP2_factor_ne_s₀ : ∀ p ∈ T,
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) :
    Newform.FullDirichletQuotientUniversalFClause f χ S T s₀ := by
  intro F hF h_F_eq
  -- Differentiability of the LFunction-based entire factors.
  have h_LF_chi_diff : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * s - k + 1)) :=
    (DirichletCharacter.differentiable_LFunction h_χ_ne_one).comp (by fun_prop)
  have h_LF_chi_sq_diff : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1))) :=
    (DirichletCharacter.differentiable_LFunction h_chi_sq_ne_one).comp (by fun_prop)
  -- Differentiability of the linear-factor finite products via `AnalyticAt.cpow`.
  have h_LinFP1_diff : Differentiable ℂ (fun s : ℂ =>
      ∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) := by
    refine Differentiable.fun_finset_prod (fun p _ => ?_)
    have h_p_slit : ((p : ℕ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.natCast_mem_slitPlane]
      exact (p.prop.pos).ne'
    have h_pow : Differentiable ℂ
        (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))) := fun s =>
      (AnalyticAt.cpow analyticAt_const (by fun_prop) h_p_slit).differentiableAt
    exact (differentiable_const _).sub ((h_pow).const_mul _)
  have h_LinFP2_diff : Differentiable ℂ (fun s : ℂ =>
      ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))) := by
    refine Differentiable.fun_finset_prod (fun p _ => ?_)
    have h_p_slit : ((p : ℕ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.natCast_mem_slitPlane]
      exact (p.prop.pos).ne'
    have h_pow : Differentiable ℂ
        (fun s : ℂ => ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))) := fun s =>
      (AnalyticAt.cpow analyticAt_const (by fun_prop) h_p_slit).differentiableAt
    exact (differentiable_const _).sub ((h_pow).const_mul _)
  -- Half-plane entire-form identity for F.
  have h_eq_halfPlane : ∀ s : ℂ, σ < s.re →
      F s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) *
        (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) =
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))) := by
    intro s hs
    have hs_abscissa : LSeries.abscissaOfAbsConv f.lCoeff_stripped < (s.re : EReal) :=
      lt_of_lt_of_le h_abscissa_lt (by exact_mod_cast hs.le)
    rw [h_F_eq hs_abscissa]
    exact h_halfPlane_id s hs
  -- LHS, RHS as entire functions.
  have h_LHS_diff : Differentiable ℂ (fun s : ℂ =>
      F s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) *
        (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))))) :=
    (hF.mul h_LF_chi_diff).mul h_LinFP1_diff
  have h_RHS_diff : Differentiable ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))))) :=
    (h_LF_chi_sq_diff.mul h_EFP_diff).mul h_LinFP2_diff
  -- Witness in half-plane.
  let z₀ : ℂ := ((σ + 1 : ℝ) : ℂ)
  have hz₀_re : σ < z₀.re := by
    show σ < ((σ + 1 : ℝ) : ℂ).re
    rw [Complex.ofReal_re]; linarith
  have h_open : IsOpen {s : ℂ | σ < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  -- Identity theorem on connected ℂ.
  have h_LHS_an : AnalyticOnNhd ℂ (fun s : ℂ =>
      F s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) *
        (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))))) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_LHS_diff
  have h_RHS_an : AnalyticOnNhd ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))))) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_RHS_diff
  have h_LHS_eq_RHS_eventually :
      (fun s : ℂ =>
        F s *
          DirichletCharacter.LFunction (Newform.dirichletLift χ
            : DirichletCharacter ℂ N) (2 * s - k + 1) *
          (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))))) =ᶠ[nhds z₀]
      (fun s : ℂ =>
        DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
          (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
          (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))))) :=
    (h_open.eventually_mem hz₀_re).mono (fun s hs => h_eq_halfPlane s hs)
  have h_global_eq := h_LHS_an.eq_of_eventuallyEq h_RHS_an h_LHS_eq_RHS_eventually
  -- Pointwise: LHS s = RHS s for every s.
  have h_pointwise : ∀ s : ℂ,
      F s *
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1) *
        (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) =
      DirichletCharacter.LFunction (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))) :=
    fun s => congrFun h_global_eq s
  -- LinFP1 nonzero at s₀.
  have h_LinFP1_ne_s₀ : (∏ p ∈ T, (1 - (Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr h_LinFP1_factor_ne_s₀
  have h_LinFP2_ne_s₀ : (∏ p ∈ T, (1 - ((Newform.dirichletLift χ *
      Newform.dirichletLift χ : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr h_LinFP2_factor_ne_s₀
  -- LinFP1 and LinFP2 nonzero on a nbhd of s₀ via continuity.
  have h_LinFP1_ev_ne : ∀ᶠ (s : ℂ) in nhds s₀,
      (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) ≠ 0 :=
    (h_LinFP1_diff.continuous).continuousAt.eventually_ne h_LinFP1_ne_s₀
  have h_LinFP2_ev_ne : ∀ᶠ (s : ℂ) in nhds s₀,
      (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))) ≠ 0 :=
    (h_LinFP2_diff.continuous).continuousAt.eventually_ne h_LinFP2_ne_s₀
  -- LF_chi (= LFunction χ̃ ∘ affine) nonzero on punctured nbhd of s₀ via isolated zeros.
  -- Witness: at s' = ((k:ℝ)/2 + 2), LFunction χ̃ (2s'-k+1) = LSeries χ̃ (5) ≠ 0.
  set s' : ℂ := (((k : ℝ) / 2 + 2 : ℝ) : ℂ) with hs'_def
  have h_re_gt_one : (1 : ℝ) < (2 * s' - (k : ℂ) + 1).re := by
    have h_re : (2 * s' - (k : ℂ) + 1).re = 5 := by
      simp [s', Complex.add_re, Complex.sub_re, Complex.mul_re,
        Complex.intCast_re, Complex.intCast_im]
      ring
    rw [h_re]; norm_num
  have h_LF_chi_at_s' : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s' - k + 1) ≠ 0 := by
    rw [DirichletCharacter.LFunction_eq_LSeries _ h_re_gt_one]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re _ h_re_gt_one
  have h_LF_chi_an_s₀ : AnalyticAt ℂ (fun s : ℂ =>
      DirichletCharacter.LFunction (Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * s - k + 1)) s₀ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr h_LF_chi_diff s₀ (Set.mem_univ _)
  have h_LF_chi_not_eventually_zero : ¬ ∀ᶠ s in nhds s₀,
      DirichletCharacter.LFunction (Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * s - k + 1) = 0 := by
    intro h_ev
    have h_LF_chi_an : AnalyticOnNhd ℂ (fun s : ℂ =>
        DirichletCharacter.LFunction (Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * s - k + 1)) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr h_LF_chi_diff
    have h_zero_an' : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ)) Set.univ :=
      fun _ _ => analyticAt_const
    have h_eq : (fun s : ℂ => DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1)) =
        (fun _ : ℂ => (0 : ℂ)) :=
      h_LF_chi_an.eq_of_eventuallyEq h_zero_an' (h_ev.mono (fun _ h => h))
    exact h_LF_chi_at_s' (congrFun h_eq s')
  have h_LF_chi_punctured_ne : ∀ᶠ s in nhdsWithin s₀ {s₀}ᶜ,
      DirichletCharacter.LFunction (Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * s - k + 1) ≠ 0 :=
    h_LF_chi_an_s₀.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      h_LF_chi_not_eventually_zero
  -- Combine.
  have h_LinFP1_punctured_ne :
      ∀ᶠ (s : ℂ) in nhdsWithin s₀ {s₀}ᶜ,
        (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) ≠ 0 :=
    h_LinFP1_ev_ne.filter_mono nhdsWithin_le_nhds
  have h_LinFP2_punctured_ne :
      ∀ᶠ (s : ℂ) in nhdsWithin s₀ {s₀}ᶜ,
        (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))) ≠ 0 :=
    h_LinFP2_ev_ne.filter_mono nhdsWithin_le_nhds
  -- The conjunction filter still has the punctured-nbhd structure.
  filter_upwards [h_LinFP1_punctured_ne, h_LinFP2_punctured_ne, h_LF_chi_punctured_ne]
    with s h_LP1_ne h_LP2_ne h_LF_ne
  -- Now we want: F s = (top_fn s) / (bot_fn s) where:
  --   top_fn s = LF_chi_sq s · ∏(eulerFactor s p · (1 - χ̃(p) p^...)⁻¹)
  --   bot_fn s = LF_chi s · ∏(1 - χ̃²(p) p^...)⁻¹
  -- From h_pointwise: F · LF_chi · LinFP1 = LF_chi_sq · EFP · LinFP2.
  show F s = _
  have h_LP1_inv : (∏ p ∈ T, (1 - (Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))))⁻¹ =
      ∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹ :=
    (Finset.prod_inv_distrib (s := T) (f := fun p =>
      1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))).symm
  have h_LP2_inv : (∏ p ∈ T, (1 - ((Newform.dirichletLift χ *
      Newform.dirichletLift χ : DirichletCharacter ℂ N))
      ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))))⁻¹ =
      ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ :=
    (Finset.prod_inv_distrib (s := T) (f := fun p =>
      1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))).symm
  -- Rewrite the goal RHS to expose LinFP1, LinFP2.
  have h_top_factored : (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) =
      (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p) *
      (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) :=
    Finset.prod_mul_distrib
  -- Goal:
  --   F s = (LF_chi_sq · ∏ (eulerFactor · (1-...)⁻¹)) / (LF_chi · ∏ (1-...)⁻¹)
  -- Rewrite numerator and denominator using the two factored/inverted identities.
  rw [Pi.div_apply]
  rw [h_top_factored, ← h_LP1_inv, ← h_LP2_inv]
  -- Goal:
  -- F s = (LF_chi_sq · EFP · LinFP1⁻¹) / (LF_chi · LinFP2⁻¹)
  -- = (LF_chi_sq · EFP · LinFP2) / (LF_chi · LinFP1)
  -- = LHS / (LF_chi · LinFP1) = F · LF_chi · LinFP1 / (LF_chi · LinFP1) = F
  have h_LF_LP1_ne : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) *
      (∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) ≠ 0 :=
    mul_ne_zero h_LF_ne h_LP1_ne
  have h_eq_at_s := h_pointwise s
  field_simp at h_eq_at_s ⊢
  linear_combination h_eq_at_s

/-- **Full universal-F clause from the pointwise T111 theorem (T132 H2
reduction, general T).**

Discharges the half-plane multiplicative entire identity
(`h_halfPlane_id` of
`Newform.FullDirichletQuotientUniversalFClause_of_halfPlane_multIdentity`)
**directly from the existing pointwise T111 theorem**
`Newform.lSeries_stripped_value_identity`, by

(a) deriving T111's geometric / sign side conditions uniformly on
`(k : ℝ) / 2 + 1 < s.re` (same techniques as
`Newform.DirichletQuotientUniversalFClause_of_T111_T_empty`);
(b) clearing the inverses `(1 - χ̃(p) ...)⁻¹` and `(1 - χ̃²(p) ...)⁻¹`
from T111's RHS by multiplying through with the corresponding linear
factors (using `Finset.prod_mul_distrib` and pointwise non-vanishing
from `h_pos_neg`); and
(c) converting `LSeries (fun n => χ̃ n) → LFunction χ̃` and
`LSeries (fun n => χ̃² n) → LFunction χ̃²` via
`DirichletCharacter.LFunction_eq_LSeries`.

The remaining inputs match those of the half-plane bridge:
`h_EFP_diff` (entirety of the per-prime Euler-factor product) and the
pointwise non-vanishing of the linear factors at `s₀`.

References: Diamond–Shurman §5.9, Miyake §4.5.15–4.5.16. -/
theorem Newform.FullDirichletQuotientUniversalFClause_of_T111
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h_bad : ∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
      q ∉ S → f.lCoeff q = 0)
    (T : Finset Nat.Primes)
    (hT_iff : ∀ p : Nat.Primes, p ∈ T ↔
      (p : ℕ) ∈ S ∧ Nat.Coprime (p : ℕ) N)
    (s₀ : ℂ)
    (h_χ_ne_one : (Newform.dirichletLift χ : DirichletCharacter ℂ N) ≠ 1)
    (h_chi_sq_ne_one : (Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ≠ 1)
    (h_abscissa_lt : LSeries.abscissaOfAbsConv f.lCoeff_stripped <
      (((k : ℝ) / 2 + 1 : ℝ) : EReal))
    (h_EFP_diff : Differentiable ℂ
      (fun s : ℂ => ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p))
    (h_LinFP1_factor_ne_s₀ : ∀ p ∈ T,
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_LinFP2_factor_ne_s₀ : ∀ p ∈ T,
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1)))) ≠ 0) :
    Newform.FullDirichletQuotientUniversalFClause f χ S T s₀ := by
  refine Newform.FullDirichletQuotientUniversalFClause_of_halfPlane_multIdentity
    f χ S T s₀ h_χ_ne_one h_chi_sq_ne_one ((k : ℝ) / 2 + 1)
    h_abscissa_lt h_EFP_diff ?_ h_LinFP1_factor_ne_s₀ h_LinFP2_factor_ne_s₀
  intro s hs_re
  -- Real-part side conditions of T111 (same approach as T_empty case).
  have h_re_eq : (2 * s - (k : ℂ) + 1).re = 2 * s.re - k + 1 := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re]
  have hs' : 1 < (2 * s - k + 1).re := by rw [h_re_eq]; linarith
  have h_re_eq_sq : (2 * (2 * s - (k : ℂ) + 1)).re = 4 * s.re - 2 * k + 2 := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.intCast_re]
    ring
  have hs'' : 1 < (2 * (2 * s - k + 1)).re := by rw [h_re_eq_sq]; linarith
  -- Geometric / sign side conditions.
  have h_geom : ∀ q : ℕ, ∀ (hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      ‖((χ (ZMod.unitOfCoprime q hqN) : ℂ) * (q : ℂ) ^ (k - 1)) *
        ((q : ℂ) ^ (-s)) ^ 2‖ < 1 := by
    intro q hq hqN _
    have hs_ge : ((k : ℝ) - 1) / 2 < s.re := by linarith
    exact Newform.norm_eulerFactor_argument_lt_one χ k hq.two_le hqN _ hs_ge
  have h_pos_neg : ∀ q : ℕ, ∀ (hq : Nat.Prime q) (hqN : Nat.Coprime q N),
      q ∉ S →
      (1 : ℂ) + (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 ∧
      (1 : ℂ) - (χ (ZMod.unitOfCoprime q hqN) : ℂ) *
        (q : ℂ) ^ (-(2 * s - k + 1)) ≠ 0 := by
    intro q hq hqN _
    have h_re_pos : (0 : ℝ) < (2 * s - (k : ℂ) + 1).re := by linarith
    have h_norm_lt :
        ‖(χ (ZMod.unitOfCoprime q hqN) : ℂ) *
          (q : ℂ) ^ (-(2 * s - k + 1))‖ < 1 :=
      Newform.norm_chi_q_cpow_neg_lt_one_of_re_pos χ hq.two_le hqN h_re_pos
    exact ⟨Newform.one_add_ne_zero_of_norm_lt_one h_norm_lt,
           Newform.one_sub_ne_zero_of_norm_lt_one h_norm_lt⟩
  -- Apply T111 multiplicative form.
  have h_T111_mult := f.lSeries_stripped_value_identity χ hfχ S h_bad
    hs_re hs' hs'' h_geom T hT_iff h_pos_neg
  -- Convert LSeries (fun n => ...) → LFunction.
  have h_LF_eq : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) =
        LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
          (2 * s - k + 1) :=
    DirichletCharacter.LFunction_eq_LSeries _ hs'
  have h_LF_sq_eq : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) =
        LSeries (fun n => (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) n) (2 * (2 * s - k + 1)) :=
    DirichletCharacter.LFunction_eq_LSeries _ hs''
  rw [h_LF_eq, h_LF_sq_eq]
  -- Establish nonzero conditions for clearing inverses.
  -- Each `(1 - dirichletLift χ ((p:ℕ):ZMod N) · p^...) ≠ 0` for p ∈ T.
  have h_LinFP1_ne : ∀ p ∈ T,
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))) ≠ 0 := by
    intro p _
    have h_inv :=
      Newform.dirichletLift_eulerFactor_ne_zero
        (Newform.dirichletLift χ : DirichletCharacter ℂ N) p.prop hs'
    intro h_zero
    apply h_inv
    rw [h_zero, inv_zero]
  have h_LinFP2_ne : ∀ p ∈ T,
      (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))) ≠ 0 := by
    intro p _
    have h_inv :=
      Newform.dirichletLift_eulerFactor_ne_zero
        (Newform.dirichletLift χ * Newform.dirichletLift χ : DirichletCharacter ℂ N)
        p.prop hs''
    intro h_zero
    apply h_inv
    rw [h_zero, inv_zero]
  have h_prod_LinFP1_ne : (∏ p ∈ T, (1 - (Newform.dirichletLift χ
      : DirichletCharacter ℂ N) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr h_LinFP1_ne
  have h_prod_LinFP2_ne : (∏ p ∈ T, (1 - ((Newform.dirichletLift χ *
      Newform.dirichletLift χ : DirichletCharacter ℂ N))
      ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr h_LinFP2_ne
  -- Algebra: clear inverses by multiplying T111 multiplicative through.
  -- h_T111_mult (raw) : LSeries f · LSχ̃ · ∏(1-χ̃²)⁻¹ = LSχ̃² · ∏(eulerFactor · (1-χ̃)⁻¹)
  -- Goal              : LSeries f · LSχ̃ · ∏(1-χ̃)   = LSχ̃² · ∏ eulerFactor · ∏(1-χ̃²)
  -- Step: factorise the RHS product, then clear both inverses uniformly.
  rw [Finset.prod_mul_distrib] at h_T111_mult
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib] at h_T111_mult
  -- Now h_T111_mult: LSeries f · LSχ̃ · (∏(1-χ̃²))⁻¹ =
  --                  LSχ̃² · ((∏ eulerFactor) · (∏(1-χ̃))⁻¹)
  -- Abbreviate to keep the algebra readable.
  set A : ℂ := LSeries f.lCoeff_stripped s with hA
  set B : ℂ := LSeries (fun n => (Newform.dirichletLift χ : DirichletCharacter ℂ N) n)
    (2 * s - k + 1) with hB
  set D : ℂ := LSeries (fun n => (Newform.dirichletLift χ * Newform.dirichletLift χ
    : DirichletCharacter ℂ N) n) (2 * (2 * s - k + 1)) with hD
  set E : ℂ := ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p with hE
  set F : ℂ := ∏ p ∈ T, (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
      ((p : ℕ) : ZMod N) *
    ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1))) with hF
  set C : ℂ := ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
    : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
    ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1)))) with hC
  -- After `set`, h_T111_mult : A * B * C⁻¹ = D * (E * F⁻¹).
  -- Goal: A * B * F = D * E * C.
  have h_C_ne : C ≠ 0 := h_prod_LinFP2_ne
  have h_F_ne : F ≠ 0 := h_prod_LinFP1_ne
  -- Step 1: cancel C⁻¹ on LHS by multiplying by C.
  have h_step1 : A * B = D * (E * F⁻¹) * C := by
    have h_mul := congrArg (· * C) h_T111_mult
    simp only at h_mul
    rw [show A * B * C⁻¹ * C = A * B * (C⁻¹ * C) from by ring,
      inv_mul_cancel₀ h_C_ne, mul_one] at h_mul
    exact h_mul
  -- Step 2: multiply by F to cancel F⁻¹ on RHS.
  have h_step2 : A * B * F = D * E * C := by
    have h_mul := congrArg (· * F) h_step1
    simp only at h_mul
    rw [show D * (E * F⁻¹) * C * F = D * E * C * (F⁻¹ * F) from by ring,
      inv_mul_cancel₀ h_F_ne, mul_one] at h_mul
    exact h_mul
  exact h_step2

/-- **Per-newform pole witness from the full T111 Dirichlet quotient
(T132 step).**

The full-clause analogue of `Newform.dirichletQuotient_pole_witness_of_dirichletZero`,
consuming the **full** T111 quotient (numerator + denominator each
including the finite Euler-factor correction product over `T`) plus
explicit analyticity / nonzero / zero / non-trivial-order hypotheses
at the pole point `s₀`.

**Hypotheses.**

* `h_num_an`, `h_den_an` — analyticity at `s₀` of the full T111
  numerator/denominator (caller-supplied; in practice combines
  `differentiable_LFunction` with the elementary analyticity of the
  finite Euler-factor correction product).
* `h_num_ne_zero` — full numerator is nonzero at `s₀` (the
  non-cancellation condition: the LFunction χ̃² value AND each finite
  correction factor is nonzero).
* `h_den_zero` — full denominator vanishes at `s₀` (the Dirichlet zero
  hypothesis: `LFunction χ̃ (2 s₀ - k + 1) = 0` propagated through the
  product).
* `h_den_finite` — the full denominator's meromorphic order at `s₀`
  is finite (⇔ den is not eventually zero in a punctured nbhd of
  `s₀`, automatic from `LFunction χ̃` being non-trivial entire).
* `h_full_clause` — the full universal-F clause
  `Newform.FullDirichletQuotientUniversalFClause f χ S T s₀`.

**Conclusion.**  Produces the inner `∃ num den s₀, ...`-shape witness
required by `Newform.DirichletQuotientHasPoleUnderBadPrime`'s inner
existential, with `num`, `den` being the full T111 numerator and
denominator as functions of `s`.

**Proof outline.**  Set `num`, `den` to the full T111 functions.  Both
are analytic at `s₀` (so meromorphic with finite order).  num(s₀) ≠ 0
gives `analyticOrderAt num s₀ = 0`; den(s₀) = 0 with non-trivial den
gives `1 ≤ analyticOrderAt den s₀`.  The strict order inequality
`0 < 1 ≤ analyticOrderAt den s₀` propagates through
`AnalyticAt.meromorphicOrderAt_eq` to the WithTop ℤ comparison
required by `meromorphicOrderAt_div_neg_of_orderAt_lt`.  Universal-F
clause is forwarded directly. -/
theorem Newform.dirichletQuotient_pole_witness_of_dirichletZero_full
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_num_an : AnalyticAt ℂ
      (fun s =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_an : AnalyticAt ℂ
      (fun s =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          (2 * s - k + 1) *
        ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀)
    (h_num_ne_zero :
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
      (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
        (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹) ≠ 0)
    (h_den_zero :
      DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s₀ - k + 1) *
      (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹) = 0)
    (h_den_finite :
      meromorphicOrderAt
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤)
    (h_full_clause : Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    ∃ (num den : ℂ → ℂ) (s₀' : ℂ),
      MeromorphicAt num s₀' ∧
      MeromorphicAt den s₀' ∧
      meromorphicOrderAt num s₀' ≠ ⊤ ∧
      meromorphicOrderAt den s₀' ≠ ⊤ ∧
      meromorphicOrderAt num s₀' < meromorphicOrderAt den s₀' ∧
      ∀ F : ℂ → ℂ, Differentiable ℂ F →
        (∀ {s : ℂ}, LSeries.abscissaOfAbsConv f.lCoeff_stripped < s.re →
          F s = LSeries f.lCoeff_stripped s) →
        F =ᶠ[nhdsWithin s₀' {s₀'}ᶜ] (num / den) := by
  set num : ℂ → ℂ := fun s =>
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
    ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹ with hnum
  set den : ℂ → ℂ := fun s =>
    DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s - k + 1) *
    ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
      : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
      ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹ with hden
  refine ⟨num, den, s₀, h_num_an.meromorphicAt, h_den_an.meromorphicAt,
    ?_, h_den_finite, ?_, h_full_clause⟩
  · -- meromorphicOrderAt num s₀ ≠ ⊤
    rw [h_num_an.meromorphicOrderAt_eq]
    have h_num_order : analyticOrderAt num s₀ = 0 :=
      h_num_an.analyticOrderAt_eq_zero.mpr h_num_ne_zero
    rw [h_num_order]
    simp
  · -- meromorphicOrderAt num s₀ < meromorphicOrderAt den s₀
    rw [h_num_an.meromorphicOrderAt_eq, h_den_an.meromorphicOrderAt_eq]
    have h_num_order : analyticOrderAt num s₀ = 0 :=
      h_num_an.analyticOrderAt_eq_zero.mpr h_num_ne_zero
    have h_den_order_ne_zero : analyticOrderAt den s₀ ≠ 0 :=
      h_den_an.analyticOrderAt_ne_zero.mpr h_den_zero
    have h_den_order_ne_top : analyticOrderAt den s₀ ≠ ⊤ := by
      intro h
      apply h_den_finite
      rw [h_den_an.meromorphicOrderAt_eq, h]
      rfl
    rw [h_num_order]
    rcases ENat.ne_top_iff_exists.mp h_den_order_ne_top with ⟨m, hm⟩
    rw [← hm]
    have h_m_ge_one : 1 ≤ m := by
      rcases m with _ | m'
      · exfalso
        have : analyticOrderAt den s₀ = 0 := by rw [← hm]; rfl
        exact h_den_order_ne_zero this
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero _)
    show (((0 : ℕ∞)).map (↑) : WithTop ℤ) < ((m : ℕ∞).map (↑) : WithTop ℤ)
    simp only [ENat.map_zero, ENat.map_coe]
    show ((0 : ℤ) : WithTop ℤ) < ((m : ℕ) : WithTop ℤ)
    rw [show ((m : ℕ) : WithTop ℤ) = (((m : ℕ) : ℤ) : WithTop ℤ) from by push_cast; rfl,
        WithTop.coe_lt_coe]
    exact_mod_cast h_m_ge_one

/-- **Full-quotient bridge: per-newform full T111 data ⇒
`NoEntireExtensionUnderBadPrime` (T132 step).**

If, for every newform-character pair `(f, χ)` and finite exceptional
set `S` satisfying the bad-prime-zero hypothesis, there exists per-
newform data `(T, s₀)` plus the full T111 numerator/denominator
analyticity / nonzero / zero / non-trivial-order conditions plus the
full universal-F clause, then `Newform.NoEntireExtensionUnderBadPrime`
follows.

This is the SMO-facing analogue of
`Newform.noEntireExtensionUnderBadPrime_of_dirichletZeroCertificate`
using the **full** T111 quotient (with finite Euler-factor correction
products) instead of the simplified `T = ∅` quotient.

The proof chains
`Newform.dirichletQuotient_pole_witness_of_dirichletZero_full` (per
newform) through
`Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole`
(the existing universal forwarder consumes any inner ∃-witness for
`DirichletQuotientHasPoleUnderBadPrime`, simplified or full). -/
theorem Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    Newform.NoEntireExtensionUnderBadPrime := by
  apply Newform.noEntireExtensionUnderBadPrime_of_dirichletQuotientHasPole
  intro N _ k f χ hfχ S h_bad
  obtain ⟨T, s₀, h_num_an, h_den_an, h_num_ne, h_den_zero, h_den_finite, h_clause⟩ :=
    h_data f χ hfχ S h_bad
  exact Newform.dirichletQuotient_pole_witness_of_dirichletZero_full
    f χ S T s₀ h_num_an h_den_an h_num_ne h_den_zero h_den_finite h_clause

/-- **Final T132 SMO consumer with full T111 quotient (T132 step).**

The full-quotient analogue of
`strongMultiplicityOne_of_HeckeEntireExtension_of_HasDirichletZeroCertificate_of_newformUnique`.
Combines the three named obligations:

1. `h_unique` — the standard Atkin-Lehner-style uniqueness statement;
2. `h_hecke : Newform.HeckeEntireExtension` — Hecke's entire continuation;
3. `h_data` — pointwise per-newform full T111 data with FULL universal-F clause;

into the Strong Multiplicity One conclusion `f.toCuspForm = g.toCuspForm`,
**without** assuming the simplified `T = ∅` specialization of the
universal-F clause — i.e. the chain works for arbitrary exceptional
prime sets `S`. -/
theorem strongMultiplicityOne_of_HeckeEntireExtension_of_full_dirichletZeroCertificate_of_newformUnique
    (h_unique : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      (∀ n : ℕ+, Nat.Coprime n.val N → f.eigenvalue n = g.eigenvalue n) →
      f.toCuspForm = g.toCuspForm)
    (h_hecke : Newform.HeckeEntireExtension)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f g : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (hgχ : g.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ)
    (h : ∀ n : ℕ+, Nat.Coprime n.val N → n.val ∉ S →
      f.eigenvalue n = g.eigenvalue n) :
    f.toCuspForm = g.toCuspForm := by
  have h_no_ext : Newform.NoEntireExtensionUnderBadPrime :=
    Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate h_data
  have h_ana : Newform.AnalyticContradiction :=
    Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
      h_hecke h_no_ext
  exact strongMultiplicityOne_of_analyticContradiction_of_newformUnique
    h_unique h_ana f g χ hfχ hgχ S h

/-- **Direct full-quotient bridge to `Newform.AnalyticContradiction` (T132 step).**

Composes the full T111 chain into a direct
`HeckeEntireExtension + full-data ⇒ AnalyticContradiction` consumer,
sparing callers the intermediate `NoEntireExtensionUnderBadPrime` step. -/
theorem Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (h_hecke : Newform.HeckeEntireExtension)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    Newform.AnalyticContradiction := by
  have h_no_ext : Newform.NoEntireExtensionUnderBadPrime :=
    Newform.noEntireExtensionUnderBadPrime_of_full_dirichletZeroCertificate h_data
  exact Newform.analyticContradiction_of_HeckeEntireExtension_of_NoEntireExtensionUnderBadPrime
    h_hecke h_no_ext

/-- **Direct full-quotient bridge to `exists_nonzero_prime_eigenvalue` (T132 step).**

Composes the full T111 chain through `AnalyticContradiction` into a direct
`HeckeEntireExtension + full-data ⇒ ∃ nonzero-prime-eigenvalue` consumer
for callers needing the prime-nonvanishing conclusion (rather than full SMO). -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (h_hecke : Newform.HeckeEntireExtension)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 := by
  have h_ana : Newform.AnalyticContradiction :=
    Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
      h_hecke h_data
  exact Newform.exists_nonzero_prime_eigenvalue_of_analyticContradiction
    h_ana f χ hfχ S

/-- **Direct full-quotient bridge: `HeckeFEData` + full data ⇒
`Newform.AnalyticContradiction` (T132 H1 consumer).**

The `HeckeFEData` analogue of
`Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`,
taking a per-newform `Newform.HeckeFEData` (Mathlib `StrongFEPair` +
bridge equation) instead of the global `HeckeEntireExtension` Prop. -/
theorem Newform.analyticContradiction_of_HeckeFEData_of_full_dirichletZeroCertificate
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    Newform.AnalyticContradiction :=
  Newform.analyticContradiction_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_HeckeFEData h_FE) h_data

/-- **Direct full-quotient bridge: `HeckeFEData` + full data ⇒
`exists_nonzero_prime_eigenvalue` (T132 H1 consumer).**

The `HeckeFEData` analogue of
`Newform.exists_nonzero_prime_eigenvalue_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`,
taking a per-newform `Newform.HeckeFEData` instead of the global
`HeckeEntireExtension` Prop. -/
theorem Newform.exists_nonzero_prime_eigenvalue_of_HeckeFEData_of_full_dirichletZeroCertificate
    (h_FE : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k), Newform.HeckeFEData f)
    (h_data : ∀ ⦃N : ℕ⦄ [NeZero N] ⦃k : ℤ⦄ (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ),
      f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ →
      ∀ (S : Finset ℕ),
        (∀ q : ℕ, ∀ (_hq : Nat.Prime q) (_hqN : Nat.Coprime q N),
          q ∉ S → f.lCoeff q = 0) →
        ∃ (T : Finset Nat.Primes) (s₀ : ℂ),
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ * Newform.dirichletLift χ
                  : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
              ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
                (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                    ((p : ℕ) : ZMod N) *
                  ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀ ∧
          AnalyticAt ℂ
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) *
            (∏ p ∈ T, Newform.eulerFactor_stripped f χ S s₀ p *
              (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                  ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1)))⁻¹)) ≠ 0 ∧
          (DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s₀ - k + 1) *
            (∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀ - k + 1))))⁻¹)) = 0 ∧
          meromorphicOrderAt
            (fun s =>
              DirichletCharacter.LFunction
                (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                (2 * s - k + 1) *
              ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
                : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
                ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤ ∧
          Newform.FullDirichletQuotientUniversalFClause f χ S T s₀)
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (hfχ : f.toCuspForm.toModularForm' ∈ modFormCharSpace k χ)
    (S : Finset ℕ) :
    ∃ q : ℕ, ∃ hq : Nat.Prime q, Nat.Coprime q N ∧ q ∉ S ∧
      f.eigenvalue ⟨q, hq.pos⟩ ≠ 0 :=
  Newform.exists_nonzero_prime_eigenvalue_of_HeckeEntireExtension_of_full_dirichletZeroCertificate
    (Newform.HeckeEntireExtension_of_HeckeFEData h_FE) h_data f χ hfχ S

/-- **Per-newform full T111 pole-data from named Dirichlet-zero inputs
(T132 step).**

Reduces the giant per-newform `h_data` hypothesis appearing inside
`Newform.exists_nonzero_prime_eigenvalue_of_HeckeEntireExtension_of_full_dirichletZeroCertificate`
(and the SMO consumer) to a **named cluster of classical Dirichlet-zero
ingredients** at one explicit pole point `s₀ : ℂ` for the given
newform-character pair `(f, χ)` and finite exceptional set `(S, T)`.

The named ingredients are:

* `h_zero : LFunction χ̃ (2 s₀ - k + 1) = 0` — the **single classical
  Dirichlet-L-zero input** in the strip `Re < 1` (Mathlib's
  `LFunction_ne_zero_of_one_le_re` rules out `Re ≥ 1`; the strip
  case is the genuinely missing classical theorem from
  Diamond-Shurman §5.9 / Miyake §4.5.15).

* `h_num_LF_ne` — non-cancellation of the squared-character
  L-function `LFunction χ̃² (2 (2 s₀ - k + 1)) ≠ 0` (also
  classical: the squared character at the doubled image point).

* `h_num_factors_ne`, `h_den_factors_ne` — local non-vanishing of the
  finite Euler-factor correction denominators at `s₀`, plus
  non-vanishing of `eulerFactor_stripped` at numerator entries.

* `h_num_an`, `h_den_an` — analyticity of the full T111 numerator and
  denominator at `s₀` (typically derivable from
  `differentiable_LFunction` + `AnalyticAt.inv` for finite
  Euler-factor inverses + `AnalyticAt.prod`; left explicit here so
  callers can choose the cleanest derivation).

* `h_den_finite` — finite analytic order of the full T111 denominator
  at `s₀` (automatic when the underlying L-function is non-trivial
  entire, via `analyticOrderAt_ne_top_of_isPreconnected`).

* `h_clause` — `Newform.FullDirichletQuotientUniversalFClause f χ S T s₀`
  (the analytic-continuation universal-F clause derived from T111 +
  extension uniqueness).

**Output.**  Produces the ∃-witness expected by the per-newform
component of `h_data` in the consumer chain (Newform.AnalyticContradiction
and onward).  The classical Dirichlet-zero existence remains the only
unproven mathematical input; all other fields are mechanical
combinations that can be discharged with existing Mathlib API. -/
theorem Newform.full_pole_witness_data_of_dirichletZero
    {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (χ : (ZMod N)ˣ →* ℂˣ)
    (S : Finset ℕ) (T : Finset Nat.Primes) (s₀ : ℂ)
    (h_zero : DirichletCharacter.LFunction
      (Newform.dirichletLift χ : DirichletCharacter ℂ N) (2 * s₀ - k + 1) = 0)
    (h_num_LF_ne : DirichletCharacter.LFunction
      (Newform.dirichletLift χ * Newform.dirichletLift χ
        : DirichletCharacter ℂ N) (2 * (2 * s₀ - k + 1)) ≠ 0)
    (h_num_factors_ne : ∀ p ∈ T,
      Newform.eulerFactor_stripped f χ S s₀ p ≠ 0 ∧
      (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          ((p : ℕ) : ZMod N) *
        ((p : ℕ) : ℂ) ^ (-(2 * s₀ - k + 1))) ≠ 0)
    (h_num_an : AnalyticAt ℂ
      (fun s =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
        ∏ p ∈ T, Newform.eulerFactor_stripped f χ S s p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀)
    (h_den_an : AnalyticAt ℂ
      (fun s =>
        DirichletCharacter.LFunction
          (Newform.dirichletLift χ : DirichletCharacter ℂ N)
          (2 * s - k + 1) *
        ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀)
    (h_den_finite :
      meromorphicOrderAt
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T, (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀ ≠ ⊤)
    (h_clause : Newform.FullDirichletQuotientUniversalFClause f χ S T s₀) :
    ∃ (T' : Finset Nat.Primes) (s₀' : ℂ),
      AnalyticAt ℂ
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ * Newform.dirichletLift χ
              : DirichletCharacter ℂ N) (2 * (2 * s - k + 1)) *
          ∏ p ∈ T', Newform.eulerFactor_stripped f χ S s p *
            (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
                ((p : ℕ) : ZMod N) *
              ((p : ℕ) : ℂ) ^ (-(2 * s - k + 1)))⁻¹) s₀' ∧
      AnalyticAt ℂ
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T', (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀' ∧
      (DirichletCharacter.LFunction
        (Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N) (2 * (2 * s₀' - k + 1)) *
        (∏ p ∈ T', Newform.eulerFactor_stripped f χ S s₀' p *
          (1 - (Newform.dirichletLift χ : DirichletCharacter ℂ N)
              ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * s₀' - k + 1)))⁻¹)) ≠ 0 ∧
      (DirichletCharacter.LFunction
        (Newform.dirichletLift χ : DirichletCharacter ℂ N)
        (2 * s₀' - k + 1) *
        (∏ p ∈ T', (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
          : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
          ((p : ℕ) : ℂ) ^ (-(2 * (2 * s₀' - k + 1))))⁻¹)) = 0 ∧
      meromorphicOrderAt
        (fun s =>
          DirichletCharacter.LFunction
            (Newform.dirichletLift χ : DirichletCharacter ℂ N)
            (2 * s - k + 1) *
          ∏ p ∈ T', (1 - ((Newform.dirichletLift χ * Newform.dirichletLift χ
            : DirichletCharacter ℂ N)) ((p : ℕ) : ZMod N) *
            ((p : ℕ) : ℂ) ^ (-(2 * (2 * s - k + 1))))⁻¹) s₀' ≠ ⊤ ∧
      Newform.FullDirichletQuotientUniversalFClause f χ S T' s₀' := by
  refine ⟨T, s₀, h_num_an, h_den_an, ?_, ?_, h_den_finite, h_clause⟩
  · -- full numerator at s₀ ≠ 0
    refine mul_ne_zero h_num_LF_ne ?_
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    refine mul_ne_zero (h_num_factors_ne p hp).1 ?_
    exact inv_ne_zero (h_num_factors_ne p hp).2
  · -- full denominator at s₀ = 0
    rw [h_zero, zero_mul]


end HeckeRing.GL2
