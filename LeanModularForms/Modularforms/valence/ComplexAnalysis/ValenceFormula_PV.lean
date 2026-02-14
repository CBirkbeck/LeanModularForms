/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormulaDefinitions
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_FD_Boundary_Param
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PrincipalValue
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ResidueTheory
import LeanModularForms.Modularforms.valence.ComplexAnalysis.WindingNumber
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Principal Value Infrastructure for Valence Formula

This file contains all the PV (Cauchy principal value) lemmas needed for the
valence formula proof.

## Main Results

* `pv_integral_exists_f'_over_f`: The PV integral of f'/f around ∂𝒟 exists.

* `pv_integral_decompose_segments`: The PV integral splits additively over the
  five segments of ∂𝒟.

* `pv_integral_vertical_cancel`: The vertical edge integrals cancel by T-invariance.

* `arc_contribution_is_k_div_12`: The arc integral gives the -k/12 term (CW orientation).

* `pv_integral_eq_modular_transformation`: The CW PV integral equals -(2πi(k/12 - ord_∞)).

## Key Lemmas

### Existence Lemmas
* `hasSimplePoleAt_logDeriv_of_zero`: f'/f has a simple pole at zeros of f
* `continuousOn_logDeriv_regular_part`: The regular part of f'/f is continuous

### Decomposition Lemmas
* `pv_integral_decompose_segments`: PV splits over path concatenation

### Cancellation Lemmas
* `pv_integral_vertical_cancel`: Vertical edges cancel by T-invariance

### Arc Contribution
* `arc_contribution_is_k_div_12`: Arc integral = -k/12 (CW orientation)

## References

See `VALENCE_AI_PLAN_PV.md` for the detailed proof strategy.
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Core PV Definitions

We use:
- `logDeriv f = deriv f / f` from Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
- `cauchyPrincipalValue'` and `cauchyPrincipalValueOn` from `Basic.lean`
- `CauchyPrincipalValueExists'` and `CauchyPrincipalValueExistsOn` for existence
- `generalizedWindingNumber'` for winding numbers
- `HasSimplePoleAt`, `residueSimplePole` from `ResidueTheory.lean`
-/

/-- The composition of a modular form with ofComplex, for contour integration. -/
abbrev modularFormCompOfComplex {k : ℤ} (f : ModularForm (Gamma 1) k) : ℂ → ℂ :=
  f ∘ UpperHalfPlane.ofComplex

/-- Principal value integral of logDeriv f along a curve γ from a to b.
    Uses the singular set S₀ = zeros of f on the curve.
    This is the proper PV integral using `cauchyPrincipalValueOn`. -/
def pv_integral_logDeriv {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : ℝ → ℂ)
    (a b : ℝ) (S₀ : Finset ℂ) : ℂ :=
  cauchyPrincipalValueOn S₀ (logDeriv (modularFormCompOfComplex f)) γ a b

/-- The integral of logDeriv f along a curve γ from a to b.
    For curves that avoid all zeros of f, this equals the classical integral.
    Uses `logDeriv = deriv f / f` from mathlib. -/
def pv_integral {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  ∫ t in a..b, logDeriv (modularFormCompOfComplex f) (γ t) * deriv γ t

/-- Order of vanishing at the cusp (in the q-expansion).
    This equals the minimum exponent m in f(z) = Σ_{n≥m} aₙ q^n with aₘ ≠ 0,
    where q = exp(2πiz). Uses `ModularFormClass.qExpansion` from Mathlib. -/
def orderAtCusp {k : ℤ} (f : ModularForm (Gamma 1) k) : ℤ :=
  (ModularFormClass.qExpansion 1 f).order.toNat

/-! ## Bridging Lemmas: Indicator ↔ Interval Integrals

These lemmas connect indicator-based cutoff integrals to interval-based integrals,
enabling use of the A-lemmas (annulus bounds) in the Cauchy chain. -/

/-- Rewrite if-then-else as set indicator. -/
lemma ite_eq_indicator {α : Type*} {β : Type*} [Zero β] (P : α → Prop) [DecidablePred P]
    (f : α → β) (x : α) :
    (if P x then f x else 0) = Set.indicator {a | P a} f x := by
  simp only [Set.indicator_apply, Set.mem_setOf_eq]

/-- The interval integral of an indicator function equals the integral over the intersection.
    This is a wrapper around `MeasureTheory.setIntegral_indicator` for interval integrals.

    **Proof**: Use `intervalIntegral.integral_eq_integral_Ioc` to convert to set integral,
    then apply `MeasureTheory.setIntegral_indicator`. -/
lemma intervalIntegral_indicator_eq {a b : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    {f : ℝ → ℂ} (_hf : IntervalIntegrable f volume a b) (hab : a ≤ b) :
    ∫ t in a..b, Set.indicator S f t = ∫ t in Set.Ioc a b ∩ S, f t := by
  rw [intervalIntegral.integral_of_le hab]
  rw [← MeasureTheory.setIntegral_indicator hS]

/-- For cutoff integrals: the "if ε < ‖γ t - z₀‖ then f t else 0" form
    equals an indicator integral over {t | ε < ‖γ t - z₀‖}. -/
lemma cutoff_integral_eq_indicator {a b : ℝ} (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ)
    (f : ℝ → ℂ) (_hf : IntervalIntegrable f volume a b) :
    ∫ t in a..b, (if ε < ‖γ t - z₀‖ then f t else 0) =
    ∫ t in a..b, Set.indicator {t | ε < ‖γ t - z₀‖} f t := by
  congr 1 with t

/-! ## Annulus Bounds for Cauchy Criterion

These lemmas establish bounds on the cutoff integrals that enable
the Cauchy criterion proof. The key insight is that the integral over
an annulus {ε < |z - z₀| < δ} is bounded in terms of the function's behavior. -/

/-- The ε-cutoff set {t | ε < ‖γ t - z₀‖} is measurable for continuous γ. -/
lemma measurableSet_cutoff_set {a b : ℝ} (γ : ℝ → ℂ) (z₀ : ℂ) (ε : ℝ)
    (hγ_cont : Continuous γ) :
    MeasurableSet {t | t ∈ Icc a b ∧ ε < ‖γ t - z₀‖} := by
  apply MeasurableSet.inter
  · exact measurableSet_Icc
  · -- {t | ε < ‖γ t - z₀‖} = (fun t => ‖γ t - z₀‖)⁻¹' (Set.Ioi ε)
    apply (continuous_norm.comp (hγ_cont.sub continuous_const)).measurable
    exact measurableSet_Ioi

/-- The annulus set {t | ε₁ < ‖γ t - z₀‖ ∧ ‖γ t - z₀‖ ≤ ε₂} is measurable. -/
lemma measurableSet_annulus_set (γ : ℝ → ℂ) (z₀ : ℂ) (ε₁ ε₂ : ℝ)
    (hγ_cont : Continuous γ) :
    MeasurableSet {t | ε₁ < ‖γ t - z₀‖ ∧ ‖γ t - z₀‖ ≤ ε₂} := by
  apply MeasurableSet.inter
  · exact (continuous_norm.comp (hγ_cont.sub continuous_const)).measurable measurableSet_Ioi
  · exact (continuous_norm.comp (hγ_cont.sub continuous_const)).measurable measurableSet_Iic

/-- **Core annulus bound**: The integral over an annulus {ε₁ < ‖γ t - z₀‖ ≤ ε₂}
    is bounded by the integral of ‖f‖ over that annulus.

    This is the central lemma from which monotonicity, difference bounds,
    and continuity all follow.

    **Proof**: Apply `norm_integral_le_integral_norm` with indicator functions. -/
lemma cutoff_integral_annulus_bound {a b : ℝ} (γ : ℝ → ℂ) (z₀ : ℂ) (f : ℝ → ℂ)
    (_hf : IntervalIntegrable f volume a b) (_hγ_cont : Continuous γ)
    {ε₁ ε₂ : ℝ} (_hε₁ : 0 < ε₁) (_hε_le : ε₁ ≤ ε₂) (hab : a ≤ b) :
    ‖∫ t in a..b, Set.indicator {t | ε₁ < ‖γ t - z₀‖ ∧ ‖γ t - z₀‖ ≤ ε₂} f t‖ ≤
    ∫ t in a..b, Set.indicator {t | ε₁ < ‖γ t - z₀‖ ∧ ‖γ t - z₀‖ ≤ ε₂} (fun t => ‖f t‖) t := by
  -- Use norm_intervalIntegral_le combined with indicator norm properties
  let S := {t | ε₁ < ‖γ t - z₀‖ ∧ ‖γ t - z₀‖ ≤ ε₂}
  -- The indicator of f has norm equal to indicator of ‖f‖
  have h_ind_norm : ∀ t, ‖S.indicator f t‖ = S.indicator (fun t => ‖f t‖) t := by
    intro t
    by_cases ht : t ∈ S
    · simp only [Set.indicator_of_mem ht]
    · simp only [Set.indicator_of_notMem ht, norm_zero]
  -- Apply the standard norm-integral bound
  calc ‖∫ t in a..b, S.indicator f t‖
      ≤ ∫ t in a..b, ‖S.indicator f t‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ t in a..b, S.indicator (fun t => ‖f t‖) t := by
        apply intervalIntegral.integral_congr
        intro t _
        exact h_ind_norm t

/-! ## One-Sided Cauchy Convergence

For the PV integral to exist, we need to show that the cutoff integrals
form a Cauchy sequence as ε → 0. This is established by showing the
difference of integrals becomes arbitrarily small. -/

/-- One-sided Cauchy criterion: if the cutoff integrals form a Cauchy sequence
    from above (ε → 0⁺), then the PV integral exists.

    **Key insight**: We don't need to compute the actual limit value here.
    We only need existence, which follows from completeness of ℂ. -/
lemma cauchy_implies_pv_exists {a b : ℝ} (γ : ℝ → ℂ) (z₀ : ℂ) (g : ℂ → ℂ)
    (hCauchy : Cauchy (Filter.map (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - z₀‖ then g (γ t) * deriv γ t else 0)
      (𝓝[>] 0))) :
    ∃ L : ℂ, Tendsto (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - z₀‖ then g (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L) := by
  -- ℂ is complete, so every Cauchy sequence/filter converges
  exact cauchy_iff_exists_le_nhds.mp hCauchy

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ## Order Connection Lemmas -/

/-- For analytic functions, meromorphicOrderAt equals analyticOrderAt (as natural numbers).
    This is `AnalyticAt.meromorphicOrderAt_eq` from mathlib wrapped for our use. -/
lemma meromorphicOrderAt_eq_analyticOrderAt {g : ℂ → ℂ} {z : ℂ} (hg : AnalyticAt ℂ g z) :
    meromorphicOrderAt g z = ENat.map Nat.cast (analyticOrderAt g z) :=
  hg.meromorphicOrderAt_eq

/-- When f is analytic at z with f(z) = 0 and f is not locally zero,
    the meromorphic order equals the analytic order (both positive naturals).

    **Key lemma for connecting `orderOfVanishingAt'` to the pole structure.** -/
lemma meromorphicOrderAt_eq_of_zero_analytic {g : ℂ → ℂ} {z : ℂ}
    (hg : AnalyticAt ℂ g z) (hgz : g z = 0) (hg_ne : ¬∀ᶠ w in 𝓝 z, g w = 0) :
    ∃ n : ℕ, n > 0 ∧ meromorphicOrderAt g z = n ∧ analyticOrderAt g z = n := by
  -- analyticOrderAt ≠ 0 because g(z) = 0
  have h_ne_zero : analyticOrderAt g z ≠ 0 := by
    intro h_eq_zero
    have := hg.analyticOrderAt_eq_zero.mp h_eq_zero
    exact this hgz
  -- analyticOrderAt ≠ ⊤ because g is not locally zero
  have h_ne_top : analyticOrderAt g z ≠ ⊤ := by
    intro h_eq_top
    have := analyticOrderAt_eq_top.mp h_eq_top
    exact hg_ne this
  -- Get the natural number value
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h_ne_top
  -- n > 0 since analyticOrderAt ≠ 0
  have hn_pos : n > 0 := by
    by_contra h_le
    push_neg at h_le
    simp only [Nat.le_zero] at h_le
    rw [h_le] at hn
    simp at hn
    exact h_ne_zero hn.symm
  -- Compute meromorphicOrderAt
  have h_merom : meromorphicOrderAt g z = n := by
    rw [hg.meromorphicOrderAt_eq, ← hn]
    simp [ENat.map]
  -- Combine
  exact ⟨n, hn_pos, h_merom, hn.symm⟩

/-- The two definitions of order agree: `orderOfVanishingAt' f s` equals `analyticOrderNatAt`.

This connects the definition using `if h : 0 < w.im then f ⟨w, h⟩ else 0` with
the definition using `f ∘ UpperHalfPlane.ofComplex`, showing they have the same order
at any point `s` in the upper half plane.

Key insight: Both functions agree on `{w : 0 < w.im}`, which is an open neighborhood of `s`,
so their analytic orders are equal by `analyticOrderAt_congr`. -/
lemma orderOfVanishingAt'_eq_analyticOrderNatAt {k : ℤ} (f : ModularForm (Gamma 1) k)
    (s : ℍ) (hf_ne : f ≠ 0) (hs : f s = 0) :
    orderOfVanishingAt' f s = (analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) : ℤ) := by
  unfold orderOfVanishingAt'
  -- Define g₁ = fun w => if h : 0 < w.im then f ⟨w, h⟩ else 0 (from orderOfVanishingAt')
  let g₁ := fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0
  -- Define g₂ = modularFormCompOfComplex f = f ∘ ofComplex
  let g₂ := modularFormCompOfComplex f
  -- Show g₁ and g₂ are eventually equal in 𝓝 s
  have h_eq : g₁ =ᶠ[𝓝 (s : ℂ)] g₂ := by
    filter_upwards [UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds s.im_pos] with w hw
    simp only [g₁, g₂, modularFormCompOfComplex, Function.comp_apply, dif_pos hw]
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hw]
  -- Therefore their meromorphic orders are equal
  have h_merom_eq : meromorphicOrderAt g₁ (s : ℂ) = meromorphicOrderAt g₂ (s : ℂ) :=
    meromorphicOrderAt_congr (h_eq.filter_mono nhdsWithin_le_nhds)
  -- g₂ is analytic at s
  have h_g2_analytic : AnalyticAt ℂ g₂ (s : ℂ) := by
    have h_mdiff := f.holo'
    have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
      UpperHalfPlane.mdifferentiable_iff.mp h_mdiff
    exact h_diffOn.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds s.im_pos)
  -- For analytic g₂: meromorphicOrderAt = analyticOrderAt (via ENat.map Nat.cast)
  have h_merom_g2 : meromorphicOrderAt g₂ (s : ℂ) = ENat.map Nat.cast (analyticOrderAt g₂ (s : ℂ)) :=
    h_g2_analytic.meromorphicOrderAt_eq
  -- g₂(s) = 0 and g₂ is not locally zero (since f ≠ 0)
  have h_g2_zero : g₂ (s : ℂ) = 0 := by
    simp only [g₂, modularFormCompOfComplex, Function.comp_apply]
    rw [UpperHalfPlane.ofComplex_apply]
    exact hs
  have h_g2_not_locally_zero : ¬∀ᶠ w in 𝓝 (s : ℂ), g₂ w = 0 := by
    intro h_loc_zero
    -- If g₂ is locally zero at s, then f is locally zero, contradicting f ≠ 0
    have : f = 0 := by
      ext z
      simp only [ModularForm.coe_zero, Pi.zero_apply]
      -- Use identity principle on the upper half plane
      have h_diffOn : DifferentiableOn ℂ g₂ {w | 0 < w.im} :=
        UpperHalfPlane.mdifferentiable_iff.mp f.holo'
      have h_analOn : AnalyticOnNhd ℂ g₂ {w | 0 < w.im} := fun w hw =>
        h_diffOn.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hw)
      have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} := by
        have h_conn : IsConnected {w : ℂ | 0 < w.im} :=
          Complex.isConnected_of_upperHalfPlane (r := 0)
            (fun _ hw => hw) (fun w (hw : (0 : ℝ) < w.im) => le_of_lt hw)
        exact h_conn.isPreconnected
      have h_freq_zero : (𝓝[≠] (s : ℂ)).Frequently (fun w => g₂ w = 0) :=
        (h_loc_zero.filter_mono nhdsWithin_le_nhds).frequently
      have h_eq_zero_on : Set.EqOn g₂ 0 {w | 0 < w.im} :=
        h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero h_preconn s.im_pos h_freq_zero
      have hz_in : (z : ℂ) ∈ {w | 0 < w.im} := z.im_pos
      have := h_eq_zero_on hz_in
      simp only [g₂, modularFormCompOfComplex, Function.comp_apply, Pi.zero_apply] at this
      rw [UpperHalfPlane.ofComplex_apply] at this
      exact this
    exact hf_ne this
  -- Get n such that analyticOrderAt g₂ = n
  obtain ⟨n, hn_pos, h_merom_n, h_anal_n⟩ :=
    meromorphicOrderAt_eq_of_zero_analytic h_g2_analytic h_g2_zero h_g2_not_locally_zero
  -- Now: meromorphicOrderAt g₁ = meromorphicOrderAt g₂ = n
  rw [h_merom_eq, h_merom_n]
  -- analyticOrderNatAt g₂ = n
  have h_natAt : analyticOrderNatAt g₂ (s : ℂ) = n := by
    unfold analyticOrderNatAt
    rw [h_anal_n]
    rfl
  rw [h_natAt]
  -- (n : ℤ∞).untop₀ = (n : ℤ)
  rfl

/-! ## Simple Pole at Zeros -/

/-- logDeriv f has a simple pole with residue = order at any zero of f.

If f is a modular form with f(s) = 0 and s is in ℍ, then logDeriv f has a simple
pole at s with residue equal to the order of vanishing.

**Proof strategy**:
1. Use `f.holo'` to get `MDifferentiable`
2. Convert via `UpperHalfPlane.mdifferentiable_iff` to get
   `DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im}`
3. Apply `DifferentiableOn.analyticAt` (upper half plane is open) to get
   `AnalyticAt ℂ (f ∘ ofComplex) (s : ℂ)`
4. Since f(s) = 0 and f ≠ 0, we have `analyticOrderAt (f ∘ ofComplex) s ≠ ⊤`
   and `analyticOrderAt (f ∘ ofComplex) s ≠ 0`
5. Use `AnalyticAt.analyticOrderAt_ne_top` to get factorization
   f(z) = (z - s)^n · g(z) with g(s) ≠ 0
6. Apply `logDeriv_mul` and `logDeriv_pow` to get
   logDeriv f = logDeriv((z-s)^n) + logDeriv g = n/(z-s) + logDeriv g

**Key lemmas needed**:
- `UpperHalfPlane.mdifferentiable_iff` (in project)
- `DifferentiableOn.analyticAt` (mathlib)
- `AnalyticAt.analyticOrderAt_ne_top` (mathlib)
- `logDeriv_mul`, `logDeriv_pow` (mathlib) -/
theorem hasSimplePoleAt_logDeriv_of_zero (hf : f ≠ 0) (s : ℍ) (hs : f s = 0) :
    ∃ (n : ℤ) (g : ℂ → ℂ), n > 0 ∧ AnalyticAt ℂ g (s : ℂ) ∧ g (s : ℂ) ≠ 0 ∧
      n = analyticOrderNatAt (modularFormCompOfComplex f) (s : ℂ) ∧
      ∀ᶠ z in 𝓝 (s : ℂ), z ≠ (s : ℂ) →
        logDeriv (modularFormCompOfComplex f) z =
          n / (z - (s : ℂ)) + logDeriv g z := by
  -- Step 1: Get AnalyticAt from MDifferentiable via DifferentiableOn
  have h_mdiff := f.holo'
  have h_diffOn : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp h_mdiff
  have h_im_pos : 0 < (s : ℂ).im := s.im_pos
  have h_analytic : AnalyticAt ℂ (f ∘ UpperHalfPlane.ofComplex) (s : ℂ) :=
    h_diffOn.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds h_im_pos)
  -- Step 2: Show analyticOrderAt ≠ ⊤ (f is not locally zero)
  -- f being a nonzero modular form means it's not identically zero on ℍ.
  -- By the identity theorem for analytic functions, it cannot be locally zero.
  have h_not_top : analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (s : ℂ) ≠ ⊤ := by
    -- If analyticOrderAt = ⊤, then f = 0 on a neighborhood of s.
    -- But f is a nonzero modular form, so this contradicts the identity theorem.
    by_contra h_top
    rw [analyticOrderAt_eq_top] at h_top
    -- h_top : ∀ᶠ z in 𝓝 s, (f ∘ ofComplex) z = 0
    -- Apply identity theorem: f ∘ ofComplex = 0 on all of ℍ
    let U := {z : ℂ | 0 < z.im}
    have hU_open : IsOpen U := UpperHalfPlane.isOpen_upperHalfPlaneSet
    have hs_in_U : (s : ℂ) ∈ U := s.im_pos
    -- f ∘ ofComplex is analytic on U
    have h_analOn : AnalyticOnNhd ℂ (f ∘ UpperHalfPlane.ofComplex) U := by
      intro z hz
      exact h_diffOn.analyticAt (hU_open.mem_nhds hz)
    -- U is preconnected (ℍ is connected)
    have h_preconn : IsPreconnected U := by
      have h_conn : IsConnected U := by
        apply Complex.isConnected_of_upperHalfPlane (r := (0 : ℝ))
        · intro z (hz : (0 : ℝ) < z.im); exact hz
        · intro z (hz : (0 : ℝ) < z.im); exact le_of_lt hz
      exact h_conn.isPreconnected
    -- h_top says f ∘ ofComplex is eventually zero at s
    -- Convert to frequently zero (the hypothesis for identity principle)
    have h_freq_zero : (𝓝[≠] (s : ℂ)).Frequently (fun z => (f ∘ UpperHalfPlane.ofComplex) z = 0) := by
      have h_ev : ∀ᶠ z in 𝓝[≠] (s : ℂ), (f ∘ UpperHalfPlane.ofComplex) z = 0 :=
        h_top.filter_mono nhdsWithin_le_nhds
      exact h_ev.frequently
    -- Apply identity principle: f ∘ ofComplex = 0 on U
    have h_zero_on_U : Set.EqOn (f ∘ UpperHalfPlane.ofComplex) 0 U := by
      apply AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero h_analOn h_preconn hs_in_U
      exact h_freq_zero
    -- This means f = 0 on all of ℍ
    have h_f_zero : ∀ z : UpperHalfPlane, f z = 0 := by
      intro z
      have hz_in_U : (z : ℂ) ∈ U := z.im_pos
      have h_eq := h_zero_on_U hz_in_U
      simp only [Pi.zero_apply, Function.comp_apply, UpperHalfPlane.ofComplex_apply] at h_eq
      exact h_eq
    -- f = 0 contradicts hf : f ≠ 0
    apply hf
    ext z
    simp only [ModularForm.coe_zero, Pi.zero_apply]
    exact h_f_zero z
  -- Step 3: Get the order (natural number) and show it's positive
  have h_order_ne_zero : analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (s : ℂ) ≠ 0 := by
    rw [h_analytic.analyticOrderAt_ne_zero]
    -- Need to show (f ∘ ofComplex) (s : ℂ) = 0
    simp only [Function.comp_apply]
    -- ofComplex (s : ℂ) = s by UpperHalfPlane.ofComplex_apply
    rw [UpperHalfPlane.ofComplex_apply]
    exact hs
  -- Step 4: Get the factorization from analyticOrderAt_ne_top
  have h_factor := h_analytic.analyticOrderAt_ne_top.mp h_not_top
  obtain ⟨g, hg_analytic, hg_ne_zero, hg_eq⟩ := h_factor
  -- Step 5: Set n to be the analyticOrderNatAt (converted to ℤ)
  let n : ℕ := analyticOrderNatAt (f ∘ UpperHalfPlane.ofComplex) (s : ℂ)
  -- n > 0 because analyticOrderAt ≠ 0 and ≠ ⊤
  have hn_pos : (n : ℤ) > 0 := by
    have hn_ne_zero : n ≠ 0 := by
      intro h_eq_zero
      -- If n = analyticOrderNatAt = 0 and order ≠ ⊤, then order = 0
      -- Use Nat.cast_analyticOrderNatAt: (n : ℕ∞) = analyticOrderAt when order ≠ ⊤
      have h_cast : (n : ℕ∞) = analyticOrderAt (f ∘ UpperHalfPlane.ofComplex) (s : ℂ) :=
        Nat.cast_analyticOrderNatAt h_not_top
      rw [h_eq_zero] at h_cast
      simp only [Nat.cast_zero] at h_cast
      exact h_order_ne_zero h_cast.symm
    omega
  -- Provide the existential witness
  refine ⟨n, g, hn_pos, hg_analytic, hg_ne_zero, rfl, ?_⟩
  -- Step 6: Show the logDeriv decomposition
  -- From hg_eq: f =ᶠ[𝓝 s] fun z ↦ (z - s) ^ n • g z
  -- For ℂ → ℂ, smul by (z-s)^n is multiplication, so f z = (z-s)^n * g z
  -- Therefore logDeriv f z = logDeriv ((· - s)^n) z + logDeriv g z = n/(z-s) + logDeriv g z
  -- Extract the open set where hg_eq holds
  have hg_eventually_analytic : ∀ᶠ z in 𝓝 (s : ℂ), AnalyticAt ℂ g z :=
    hg_analytic.eventually_analyticAt
  have hg_eventually_ne_zero : ∀ᶠ z in 𝓝 (s : ℂ), g z ≠ 0 :=
    hg_analytic.continuousAt.eventually_ne hg_ne_zero
  -- Get an open set where all conditions hold
  have h_all_eventually : ∀ᶠ z in 𝓝 (s : ℂ),
      ((f ∘ UpperHalfPlane.ofComplex) z = (z - (s : ℂ)) ^ n • g z) ∧
      AnalyticAt ℂ g z ∧ g z ≠ 0 := by
    filter_upwards [hg_eq, hg_eventually_analytic, hg_eventually_ne_zero]
    intro z hz hza hzne
    exact ⟨hz, hza, hzne⟩
  -- Extract the open set
  obtain ⟨U, hU_mem, hU_cond⟩ := Filter.eventually_iff_exists_mem.mp h_all_eventually
  -- mem_nhds_iff: s ∈ 𝓝 a ↔ ∃ t ⊆ s, IsOpen t ∧ a ∈ t
  obtain ⟨V, hV_sub, hV_open, hs_in_V⟩ := mem_nhds_iff.mp hU_mem
  -- Filter upwards with explicit open set membership
  filter_upwards [IsOpen.mem_nhds hV_open hs_in_V] with z hz_in_V using by
    intro hz_ne_s
    -- z ∈ V ⊆ U, so the conditions from hU_cond hold at z
    have hz_in_U : z ∈ U := hV_sub hz_in_V
    have ⟨hz, hz_analytic, hz_ne_zero⟩ := hU_cond z hz_in_U
    -- At z ≠ s, we have (f ∘ ofComplex) z = (z - s)^n • g z
    -- In ℂ, (z - s)^n • g z = (z - s)^n * g z (scalar multiplication)
    simp only [modularFormCompOfComplex]
    -- The factorization gives us: (f ∘ ofComplex) z = (z - s)^n * g z (via smul = mul in ℂ)
    have h_eq_mul : (f ∘ UpperHalfPlane.ofComplex) z = (z - (s : ℂ)) ^ n * g z := by
      rw [hz]; rfl
    -- Step 6a: Show the functions agree on a neighborhood of z (not just at z)
    -- Since z ∈ {𝓝 s \ {s}}, and hg_eq says f ∘ ofComplex =ᶠ[𝓝 s] (· - s)^n • g,
    -- there's an open neighborhood U of s where they agree, and z ∈ U \ {s}.
    -- But z is also an interior point of U \ {s}, so they agree on a nbhd of z.
    -- Therefore deriv(f ∘ ofComplex) z = deriv((· - s)^n * g) z.
    -- Hence logDeriv(f ∘ ofComplex) z = logDeriv((· - s)^n * g) z.
    -- Now compute logDeriv((· - s)^n * g) z using logDeriv_mul.
    -- Need: (z - s)^n ≠ 0 (from z ≠ s)
    have h_pow_ne_zero : (z - (s : ℂ)) ^ n ≠ 0 := by
      apply pow_ne_zero
      simp only [ne_eq, sub_eq_zero]
      exact hz_ne_s
    -- Need: g z ≠ 0 (from hz_ne_zero in filter_upwards)
    have h_gz_ne_zero : g z ≠ 0 := hz_ne_zero
    -- Need differentiability
    have h_diff_sub : DifferentiableAt ℂ (fun w => (w - (s : ℂ)) ^ n) z := by
      apply DifferentiableAt.pow
      exact differentiableAt_id.sub (differentiableAt_const _)
    -- g is analytic at z (from hz_analytic in filter_upwards), hence differentiable
    have h_diff_g : DifferentiableAt ℂ g z := hz_analytic.differentiableAt
    -- The logDeriv formula requires that f ∘ ofComplex and (· - s)^n * g have the same logDeriv
    -- This follows from the eventual equality: derivatives agree on nbhd, values agree at z
    -- We compute logDeriv((· - s)^n * g) directly
    have h_logDeriv_product : logDeriv (fun w => (w - (s : ℂ)) ^ n * g w) z =
        logDeriv (fun w => (w - (s : ℂ)) ^ n) z + logDeriv g z := by
      apply logDeriv_mul
      · exact h_pow_ne_zero
      · exact h_gz_ne_zero
      · exact h_diff_sub
      · exact h_diff_g
    -- Compute logDeriv((· - s)^n) z = n / (z - s)
    have h_logDeriv_pow : logDeriv (fun w => (w - (s : ℂ)) ^ n) z = n / (z - (s : ℂ)) := by
      -- Use that (fun w => (w - s)^n) = (· - s)^n and apply logDeriv_fun_pow
      have h_eq_fn : (fun w : ℂ => (w - (s : ℂ)) ^ n) = (fun w => w - (s : ℂ)) ^ n := rfl
      rw [h_eq_fn]
      have h1 : logDeriv ((fun w : ℂ => w - (s : ℂ)) ^ n) z = (n : ℂ) * logDeriv (fun w => w - (s : ℂ)) z := by
        apply logDeriv_fun_pow
        exact differentiableAt_id.sub (differentiableAt_const _)
      have h2 : logDeriv (fun w : ℂ => w - (s : ℂ)) z = 1 / (z - (s : ℂ)) := by
        simp only [logDeriv_apply]
        rw [deriv_sub_const, deriv_id'']
      rw [h1, h2]
      ring
    -- Now we need to show logDeriv(f ∘ ofComplex) z = logDeriv((· - s)^n * g) z
    -- This follows from: values agree (h_eq_mul) and derivatives agree (from eventuallyEq)
    -- For the latter, we need that hg_eq provides eventually equality on a nhbd containing z
    -- This is the key step that requires the eventuallyEq → deriv equality
    calc logDeriv (f ∘ UpperHalfPlane.ofComplex) z
        = logDeriv (fun w => (w - (s : ℂ)) ^ n * g w) z := by
          -- logDeriv = deriv / value. We need:
          -- 1. Values agree at z: h_eq_mul
          -- 2. Derivatives agree at z: follows from eventuallyEq at z
          -- For (2), we use that hg_eq provides an open set where functions agree,
          -- and z is in that open set, so functions are eventually equal at z.
          unfold logDeriv
          simp only [Pi.div_apply]
          -- Show values agree: use h_eq_mul (noting smul = mul in ℂ)
          have h_val_eq : (f ∘ UpperHalfPlane.ofComplex) z = (z - (s : ℂ)) ^ n * g z := h_eq_mul
          -- Show derivatives agree: need functions eventually equal at z
          -- Since hg_eq : f ∘ ofComplex =ᶠ[𝓝 s] (· - s)^n • g on an open nbhd of s,
          -- and z is in that nbhd (by filter_upwards), the functions agree on a nbhd of z too.
          -- This is because 𝓝 s provides open neighborhoods, and z ∈ open set means it's interior.
          have h_deriv_eq : deriv (f ∘ UpperHalfPlane.ofComplex) z =
              deriv (fun w => (w - (s : ℂ)) ^ n * g w) z := by
            -- The functions are eventually equal at z (not just s)
            -- because hg_eq holds on an open neighborhood of s containing z
            -- Step 1: Get the eventually equality at z from hg_eq
            -- hg_eq : f ∘ ofComplex =ᶠ[𝓝 s] (· - s)^n • g
            -- We need to show f ∘ ofComplex =ᶠ[𝓝 z] (· - s)^n • g
            -- Then apply EventuallyEq.deriv_eq
            have h_eq_at_z : (f ∘ UpperHalfPlane.ofComplex) =ᶠ[𝓝 z] (fun w => (w - (s : ℂ)) ^ n * g w) := by
              -- V is open, z ∈ V (from hz_in_V), so V ∈ 𝓝 z
              -- On V ⊆ U, the conditions from hU_cond hold, including the equality
              apply Filter.eventually_iff_exists_mem.mpr
              use V
              constructor
              · exact IsOpen.mem_nhds hV_open hz_in_V
              · intro w hw_in_V
                have hw_in_U : w ∈ U := hV_sub hw_in_V
                have ⟨hw_eq, _, _⟩ := hU_cond w hw_in_U
                -- hw_eq : (f ∘ ofComplex) w = (w - s)^n • g w
                -- In ℂ, smul is multiplication, so this equals (w - s)^n * g w
                exact hw_eq
            exact h_eq_at_z.deriv_eq
          rw [h_deriv_eq, h_val_eq]
      _ = logDeriv (fun w => (w - (s : ℂ)) ^ n) z + logDeriv g z := h_logDeriv_product
      _ = n / (z - (s : ℂ)) + logDeriv g z := by rw [h_logDeriv_pow]
      _ = ↑↑n / (z - (s : ℂ)) + logDeriv g z := rfl

/-- logDeriv f has a simple pole at any zero of f (using ResidueTheory definition). -/
theorem hasSimplePoleAt_logDeriv_of_zero' (hf : f ≠ 0) (s : ℍ) (hs : f s = 0) :
    HasSimplePoleAt (logDeriv (modularFormCompOfComplex f)) (s : ℂ) := by
  -- Get the decomposition from the main theorem
  obtain ⟨n, g, hn_pos, hg_analytic, hg_ne_zero, _, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s hs
  -- HasSimplePoleAt requires: ∃ c g, AnalyticAt g z₀ ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z
  -- We use c = n and the regular part is logDeriv g
  use (n : ℂ)
  use (logDeriv g)
  constructor
  · -- Show logDeriv g is analytic at s
    -- logDeriv g = deriv g / g, and g is analytic with g(s) ≠ 0
    unfold logDeriv
    apply AnalyticAt.fun_div
    · exact hg_analytic.deriv
    · exact hg_analytic
    · exact hg_ne_zero
  · -- Convert the formula from 𝓝 to 𝓝[≠]
    -- h_formula : ∀ᶠ z in 𝓝 s, z ≠ s → logDeriv (f ∘ ofComplex) z = n / (z - s) + logDeriv g z
    -- Need: ∀ᶠ z in 𝓝[≠] s, logDeriv (f ∘ ofComplex) z = n / (z - s) + logDeriv g z
    rw [eventually_nhdsWithin_iff]
    -- h_formula is already in the form ∀ᶠ z in 𝓝 s, z ≠ s → P z
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    -- z ≠ s is definitionally equal to ¬z = s
    exact h_formula

/-! ## Cauchy Criterion for PV -/

/-- Finiteness of crossings: For an immersion γ, the set {t : γ t = z₀} is finite.
    This is a wrapper around `piecewiseC1Immersion_finite_zeros` from Finiteness.lean. -/
lemma immersion_crossings_finite (γ : PiecewiseC1Immersion) (z₀ : ℂ) :
    Set.Finite {t ∈ Set.Icc γ.a γ.b | γ.toFun t = z₀} :=
  piecewiseC1Immersion_finite_zeros γ z₀

/-- In a finite subset of ℝ, each point has an isolated neighborhood.

    **Mathematical content**: If S ⊆ ℝ is finite and x ∈ S, then there exists δ > 0
    such that (x - δ, x + δ) ∩ (S \ {x}) = ∅. -/
lemma finite_real_isolated_neighborhood {S : Set ℝ} (hS : S.Finite) (x : ℝ) (hx : x ∈ S) :
    ∃ δ > 0, ∀ y ∈ S, y ≠ x → |y - x| ≥ δ := by
  by_cases h_singleton : S = {x}
  · -- S = {x}, any δ works
    use 1, one_pos
    intro y hy hy_ne
    rw [h_singleton] at hy
    simp only [Set.mem_singleton_iff] at hy
    exact absurd hy hy_ne
  · -- S contains other elements
    have h_other : (S \ {x}).Nonempty := by
      by_contra h_empty
      rw [Set.not_nonempty_iff_eq_empty] at h_empty
      have h_eq : S ⊆ {x} := by
        intro z hz
        by_contra hz_ne
        have hz' : z ∈ S \ {x} := ⟨hz, Set.mem_singleton_iff.not.mpr hz_ne⟩
        rw [h_empty] at hz'
        exact Set.notMem_empty z hz'
      have h_x : {x} ⊆ S := Set.singleton_subset_iff.mpr hx
      exact h_singleton (Set.Subset.antisymm h_eq h_x)
    -- The set of distances is finite and positive
    let D := (fun y => |y - x|) '' (S \ {x})
    have hD_finite : D.Finite := (hS.subset Set.diff_subset).image _
    have hD_pos : ∀ d ∈ D, 0 < d := by
      intro d hd
      simp only [D, Set.mem_image, Set.mem_diff, Set.mem_singleton_iff] at hd
      obtain ⟨y, ⟨_, hy_ne⟩, hd_eq⟩ := hd
      rw [← hd_eq]
      exact abs_pos.mpr (sub_ne_zero.mpr hy_ne)
    -- Let δ = min D > 0 (convert to Finset to use min')
    have hD_nonempty : D.Nonempty := by
      obtain ⟨y, hy⟩ := h_other
      exact ⟨|y - x|, Set.mem_image_of_mem _ hy⟩
    -- Convert to Finset
    let Df := hD_finite.toFinset
    have hDf_nonempty : Df.Nonempty := by
      simp only [Finset.nonempty_iff_ne_empty, ne_eq, Df]
      intro h_empty
      rw [Set.Finite.toFinset_eq_empty] at h_empty
      exact Set.not_nonempty_empty (h_empty ▸ hD_nonempty)
    -- Get the minimum element
    let δ := Df.min' hDf_nonempty
    use δ
    constructor
    · -- δ > 0
      have hδ_mem : δ ∈ Df := Finset.min'_mem Df hDf_nonempty
      have hδ_mem_D : δ ∈ D := by simp only [Set.Finite.mem_toFinset, Df] at hδ_mem; exact hδ_mem
      exact hD_pos δ hδ_mem_D
    · -- ∀ y ∈ S, y ≠ x → |y - x| ≥ δ
      intro y hy hy_ne
      have hy' : y ∈ S \ {x} := Set.mem_diff_singleton.mpr ⟨hy, hy_ne⟩
      have h_in_D : |y - x| ∈ D := Set.mem_image_of_mem _ hy'
      have h_in_Df : |y - x| ∈ Df := by simp only [Set.Finite.mem_toFinset, Df]; exact h_in_D
      exact Finset.min'_le Df |y - x| h_in_Df

/-- For interior crossings, there's a neighborhood with no other crossings.
    This allows localization of the Cauchy argument.

    **Proof outline**: Since crossings are finite (by `immersion_crossings_finite`),
    t₀ is an isolated point. Take δ = min distance to other crossings (or to boundary). -/
lemma local_interval_no_other_crossings (γ : PiecewiseC1Immersion) (z₀ : ℂ)
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Ioo γ.a γ.b) (hcross : γ.toFun t₀ = z₀) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (t₀ - δ) (t₀ + δ), t ≠ t₀ → t ∈ Set.Icc γ.a γ.b → γ.toFun t ≠ z₀ := by
  -- Step 1: The crossing set S is finite
  let S := {t ∈ Set.Icc γ.a γ.b | γ.toFun t = z₀}
  have hS_finite : S.Finite := immersion_crossings_finite γ z₀
  -- Step 2: t₀ ∈ S (it's a crossing point in [a, b])
  have ht₀_mem_S : t₀ ∈ S := by
    simp only [S, Set.mem_setOf_eq, Set.mem_Icc]
    exact ⟨⟨le_of_lt ht₀.1, le_of_lt ht₀.2⟩, hcross⟩
  -- Step 3: Apply finite_real_isolated_neighborhood to get δ₁ isolating t₀ from other crossings
  obtain ⟨δ₁, hδ₁_pos, hδ₁_isolated⟩ := finite_real_isolated_neighborhood hS_finite t₀ ht₀_mem_S
  -- Step 4: Since t₀ ∈ Ioo γ.a γ.b, we have positive distance to boundary
  have h_dist_left : t₀ - γ.a > 0 := sub_pos.mpr ht₀.1
  have h_dist_right : γ.b - t₀ > 0 := sub_pos.mpr ht₀.2
  -- Step 5: Take δ = min(δ₁, t₀ - γ.a, γ.b - t₀)
  let δ := min δ₁ (min (t₀ - γ.a) (γ.b - t₀))
  use δ
  constructor
  · -- δ > 0
    simp only [δ, lt_min_iff]
    exact ⟨hδ₁_pos, h_dist_left, h_dist_right⟩
  · -- Main isolation property
    intro t ht_in_Ioo ht_ne_t₀ ht_in_Icc
    -- Suppose γ t = z₀, then t ∈ S
    intro h_eq_z₀
    have ht_mem_S : t ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨ht_in_Icc, h_eq_z₀⟩
    -- Since t ∈ S and t ≠ t₀, we have |t - t₀| ≥ δ₁ by isolation
    have h_ge_δ₁ : |t - t₀| ≥ δ₁ := hδ₁_isolated t ht_mem_S ht_ne_t₀
    -- But t ∈ Ioo (t₀ - δ) (t₀ + δ) means |t - t₀| < δ ≤ δ₁
    have h_lt_δ : |t - t₀| < δ := by
      have h1 : t - t₀ < δ := by linarith [ht_in_Ioo.2]
      have h2 : t₀ - t < δ := by linarith [ht_in_Ioo.1]
      rw [abs_sub_lt_iff]
      exact ⟨h1, h2⟩
    have h_le_δ₁ : δ ≤ δ₁ := by simp only [δ]; exact min_le_left _ _
    -- Contradiction: |t - t₀| < δ ≤ δ₁ ≤ |t - t₀|
    have h_lt_δ₁ : |t - t₀| < δ₁ := lt_of_lt_of_le h_lt_δ h_le_δ₁
    exact absurd h_ge_δ₁ (not_le.mpr h_lt_δ₁)

/-- On the far region (outside [t₀-δ, t₀+δ]), the cutoff integral is constant for small ε.

When γ doesn't cross z₀ on a compact region, there's a minimum distance δ' > 0.
For ε < δ', the cutoff condition ε < ‖γ t - z₀‖ is always satisfied, so the integral
equals the full integral without cutoff. -/
lemma far_part_constant (γ : ℝ → ℂ) (z₀ : ℂ) (f : ℝ → ℂ)
    {a b : ℝ} (hab : a ≤ b)
    (h_no_crossing : ∀ t ∈ Set.Icc a b, γ t ≠ z₀)
    (hγ_cont : Continuous γ) :
    ∃ δ' > 0, ∀ ε ∈ Set.Ioo 0 δ',
      ∫ t in a..b, (if ε < ‖γ t - z₀‖ then f t else 0) = ∫ t in a..b, f t := by
  -- The distance function t ↦ ‖γ t - z₀‖ is continuous and positive on [a, b]
  -- Since [a, b] is compact, it has a positive minimum
  by_cases h_empty : a = b
  · -- Trivial case: interval is empty
    use 1, by norm_num
    intro ε _
    simp [h_empty]
  · -- Non-trivial case: find minimum distance
    have hab_lt : a < b := lt_of_le_of_ne hab h_empty
    let dist_fn := fun t => ‖γ t - z₀‖
    have h_dist_cont : Continuous dist_fn := continuous_norm.comp (hγ_cont.sub continuous_const)
    have h_dist_pos : ∀ t ∈ Set.Icc a b, 0 < dist_fn t := by
      intro t ht
      simp only [dist_fn, norm_pos_iff, sub_ne_zero]
      exact h_no_crossing t ht
    -- On compact [a, b], continuous dist_fn attains minimum
    have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
    have h_nonempty : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
    obtain ⟨t_min, ht_min_mem, ht_min_val⟩ := h_compact.exists_isMinOn h_nonempty h_dist_cont.continuousOn
    let δ' := dist_fn t_min
    have hδ'_pos : 0 < δ' := h_dist_pos t_min ht_min_mem
    use δ', hδ'_pos
    intro ε ⟨hε_pos, hε_lt⟩
    -- For all t ∈ [a, b], we have ε < δ' ≤ dist_fn t, so cutoff is satisfied
    apply intervalIntegral.integral_congr
    intro t ht
    -- Since a ≤ b, [[a, b]] = Icc a b
    have ht' : t ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at ht
    have h_cutoff : ε < ‖γ t - z₀‖ := by
      calc ε < δ' := hε_lt
        _ ≤ dist_fn t := ht_min_val ht'
    simp only [h_cutoff, ↓reduceIte]

/-! ## Cauchy Cutoff Helpers (from PV_Work)

These helpers support `cauchy_cutoff_of_linear_approx`, which proves that the
ε-cutoff integral is Cauchy for curves with a non-zero derivative at the crossing.
-/

/-- Extract ε-δ remainder bound from `HasDerivAt`. -/
lemma hasDerivAt_remainder_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ : HasDerivAt γ L t₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ε * |t - t₀| := by
  intro ε hε
  rw [hasDerivAt_iff_isLittleO] at hγ
  rw [Asymptotics.isLittleO_iff] at hγ
  obtain ⟨s, hs_mem, hs⟩ := (hγ hε).exists_mem
  rw [Metric.mem_nhds_iff] at hs_mem
  obtain ⟨δ, hδ_pos, hδ_ball⟩ := hs_mem
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have ht_in_ball : t ∈ Metric.ball t₀ δ := by simp [Metric.mem_ball, Real.dist_eq, ht_lt]
  have h_bound := hs t (hδ_ball ht_in_ball)
  simp only [Real.norm_eq_abs] at h_bound
  exact h_bound

/-- Norm of real scalar times complex: ‖x • L‖ = |x| * ‖L‖. -/
lemma norm_real_smul (x : ℝ) (L : ℂ) : ‖x • L‖ = |x| * ‖L‖ := by
  rw [norm_smul, Real.norm_eq_abs]

/-- Convert between `L * ↑(t - t₀)` and `(t - t₀) • L` for complex L and real t, t₀. -/
lemma complex_mul_real_eq_smul (L : ℂ) (t t₀ : ℝ) : L * ↑(t - t₀) = (t - t₀) • L := by
  simp only [Complex.real_smul, mul_comm]

/-- Reverse triangle inequality: ‖a + b‖ ≥ ‖a‖ - ‖b‖. -/
lemma norm_add_lower_bound (a b : ℂ) : ‖a + b‖ ≥ ‖a‖ - ‖b‖ := by
  have h := norm_sub_norm_le a (-b)
  simp only [sub_neg_eq_add, norm_neg] at h
  linarith

/-- Inverse norm bound: if c ≤ ‖x‖ with c > 0, then ‖x⁻¹‖ ≤ 1/c. -/
lemma norm_inv_le_of_norm_ge {x : ℂ} {c : ℝ} (hc : 0 < c) (h : c ≤ ‖x‖) : ‖x⁻¹‖ ≤ 1 / c := by
  have hx_ne : x ≠ 0 := by intro hx0; simp [hx0] at h; linarith
  have hx_pos : 0 < ‖x‖ := lt_of_lt_of_le hc h
  rw [norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le hc h

/-- The "far set" away from t₀ is compact. -/
lemma farSet_isCompact (a b t₀ δ : ℝ) (_hab : a < b) (_hδ : 0 < δ) :
    IsCompact {t | t ∈ Set.Icc a b ∧ δ ≤ |t - t₀|} := by
  apply IsCompact.inter_right isCompact_Icc
  have h_closed : IsClosed {t : ℝ | δ ≤ |t - t₀|} := by
    apply isClosed_le continuous_const
    exact continuous_abs.comp (continuous_sub_right t₀)
  exact h_closed

/-- If γ is continuous on [a,b] and |t - t₀| ≥ δ with δ > 0, then ‖γ t - γ t₀‖ has a
    positive lower bound on the far set (assuming γ t ≠ γ t₀ on that set). -/
lemma norm_sub_pos_on_farSet (γ : ℝ → ℂ) (a b t₀ δ : ℝ)
    (hab : a < b) (hδ : 0 < δ)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj_far : ∀ t ∈ Set.Icc a b, δ ≤ |t - t₀| → γ t ≠ γ t₀) :
    ∃ m > 0, ∀ t ∈ Set.Icc a b, δ ≤ |t - t₀| → m ≤ ‖γ t - γ t₀‖ := by
  let farSet := {t | t ∈ Set.Icc a b ∧ δ ≤ |t - t₀|}
  have h_compact : IsCompact farSet := farSet_isCompact a b t₀ δ hab hδ
  have h_cont_norm : ContinuousOn (fun t => ‖γ t - γ t₀‖) (Set.Icc a b) := by
    apply Continuous.comp_continuousOn continuous_norm
    exact hγ_cont.sub continuousOn_const
  by_cases h_nonempty : farSet.Nonempty
  · have h_cont_on_far : ContinuousOn (fun t => ‖γ t - γ t₀‖) farSet := h_cont_norm.mono (fun t ht => ht.1)
    obtain ⟨t_min', ht_min'_mem, ht_min'_min⟩ := h_compact.exists_isMinOn h_nonempty h_cont_on_far
    have h_min_pos : 0 < ‖γ t_min' - γ t₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h_inj_far t_min' ht_min'_mem.1 ht_min'_mem.2))
    exact ⟨‖γ t_min' - γ t₀‖, h_min_pos, fun t ht1 ht2 => ht_min'_min ⟨ht1, ht2⟩⟩
  · exact ⟨1, one_pos, fun t ht1 ht2 => by exfalso; exact h_nonempty ⟨t, ht1, ht2⟩⟩

/-- The integrand times (t-t₀) tends to 1.

This is the key estimate: (t-t₀) * (γ-γ₀)⁻¹ * γ' → 1 as t → t₀. -/
lemma integrand_times_t_tendsto_one (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀)
    (hγ_cont_at : ContinuousAt (deriv γ) t₀) :
    Tendsto (fun t => (↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ * deriv γ t) (𝓝[≠] t₀) (𝓝 1) := by
  have h_deriv_eq : deriv γ t₀ = L := hγ_hasderiv.deriv
  have h_deriv_tendsto : Tendsto (deriv γ) (𝓝 t₀) (𝓝 L) := by rw [← h_deriv_eq]; exact hγ_cont_at
  have h_ratio_tendsto : Tendsto (fun t => (↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹) (𝓝[≠] t₀) (𝓝 L⁻¹) := by
    have h_slope : Tendsto (fun t => (t - t₀)⁻¹ • (γ t - γ t₀)) (𝓝[≠] t₀) (𝓝 L) := by
      rw [hasDerivAt_iff_tendsto_slope_zero] at hγ_hasderiv
      have h_comp : (fun t => (t - t₀)⁻¹ • (γ t - γ t₀)) = (fun s => s⁻¹ • (γ (t₀ + s) - γ t₀)) ∘ (fun t => t - t₀) := by
        ext t; simp [add_sub_cancel]
      rw [h_comp]
      apply Tendsto.comp hγ_hasderiv
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h1 : Tendsto (fun t => t - t₀) (𝓝 t₀) (𝓝 (t₀ - t₀)) := tendsto_id.sub_const t₀
        simp at h1; exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_ne_zero]; exact ht
    have h_smul_eq : ∀ t : ℝ, (t - t₀)⁻¹ • (γ t - γ t₀) = (γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹ := by
      intro t; rw [Algebra.smul_def]; simp [mul_comm]
    have h_slope' : Tendsto (fun t => (γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹) (𝓝[≠] t₀) (𝓝 L) := by
      simp only [← h_smul_eq]; exact h_slope
    have h_recip : Tendsto (fun t => ((γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹)⁻¹) (𝓝[≠] t₀) (𝓝 L⁻¹) := h_slope'.inv₀ hL
    have h_inv_eq : ∀ t : ℝ, ((γ t - γ t₀) * (↑(t - t₀) : ℂ)⁻¹)⁻¹ = (↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ := by
      intro t
      by_cases h : γ t - γ t₀ = 0
      · simp [h]
      · by_cases ht : (t : ℂ) - t₀ = 0
        · simp [ht]
        · field_simp
    simp only [h_inv_eq] at h_recip; exact h_recip
  have h_prod : Tendsto (fun t => (↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ * deriv γ t) (𝓝[≠] t₀) (𝓝 (L⁻¹ * L)) := by
    apply Tendsto.mul h_ratio_tendsto (h_deriv_tendsto.mono_left nhdsWithin_le_nhds)
  simp only [inv_mul_cancel₀ hL] at h_prod
  exact h_prod

/-- Asymptotic control: ‖(γ-γ₀)⁻¹ * γ' - (t-t₀)⁻¹‖ ≤ ε / |t-t₀|. -/
lemma integrand_asymptotic (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (_hL : L ≠ 0)
    (_hγ_hasderiv : HasDerivAt γ L t₀) (_hγ_cont_at : ContinuousAt (deriv γ) t₀)
    (h_tendsto : Tendsto (fun t => (↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ * deriv γ t) (𝓝[≠] t₀) (𝓝 1)) :
    ∀ ε > 0, ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ ε / |t - t₀| := by
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at h_tendsto
  obtain ⟨δ, hδ_pos, hδ⟩ := h_tendsto ε hε
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have h_ne : t ≠ t₀ := fun h => by simp [h] at ht_pos
  have h_dist : dist t t₀ < δ := by rwa [Real.dist_eq]
  have h_bound := hδ h_ne h_dist
  rw [Complex.dist_eq] at h_bound
  have h_ne_c : (↑(t - t₀) : ℂ) ≠ 0 := by simp only [ne_eq, ofReal_eq_zero, sub_eq_zero]; exact h_ne
  have h_key : (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹ =
      ((↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ * deriv γ t - 1) * (↑(t - t₀))⁻¹ := by field_simp
  rw [h_key]
  calc ‖((↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ * deriv γ t - 1) * (↑(t - t₀))⁻¹‖
      = ‖(↑(t - t₀) : ℂ) * (γ t - γ t₀)⁻¹ * deriv γ t - 1‖ * ‖(↑(t - t₀) : ℂ)⁻¹‖ := norm_mul _ _
    _ ≤ ε * ‖(↑(t - t₀) : ℂ)⁻¹‖ := by apply mul_le_mul_of_nonneg_right (le_of_lt h_bound) (norm_nonneg _)
    _ = ε / |t - t₀| := by rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, div_eq_mul_inv]

/-! ### Bounded remainder from C² smoothness

For the dyadic sequence approach to work, we need step bounds O(ε), not constant.
This requires the remainder r(t) = (γ-γ₀)⁻¹*γ' - (t-t₀)⁻¹ to be bounded (O(1)), not O(1/|t-t₀|).
With C² smoothness at t₀, Taylor expansion gives bounded remainder. -/

/-- Micro-lemma: Lower bound on ‖γ t - γ t₀‖ from non-zero derivative.
Uses hasDerivAt_remainder_bound + reverse triangle inequality. -/
lemma gamma_lower_bound_of_hasDerivAt {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀| := by
  -- Step 1: ‖L‖ > 0
  have hLnorm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  -- Step 2: Get δ from hasDerivAt_remainder_bound with ε = ‖L‖/2
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hasDerivAt_remainder_bound hγ_hasderiv (‖L‖ / 2) (half_pos hLnorm_pos)
  -- Step 3: This δ works
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  -- Step 4: Get the remainder bound for this t
  have h_rem : ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ (‖L‖ / 2) * |t - t₀| := hδ_bound t ht_pos ht_lt
  -- Step 5: Decomposition identity: (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) = γ t - γ t₀
  have h_decomp : (t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L) = γ t - γ t₀ := by ring
  -- Step 6: Reverse triangle: ‖a + b‖ ≥ ‖a‖ - ‖b‖, so ‖γ - γ₀‖ ≥ ‖(t-t₀)•L‖ - ‖error‖
  have h_tri : ‖γ t - γ t₀‖ ≥ ‖(t - t₀) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    have h1 : ‖γ t - γ t₀‖ = ‖(t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L)‖ := by
      congr 1; ring
    rw [h1]
    exact norm_add_lower_bound _ _
  -- Step 7: ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖
  have h_smul : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ := norm_real_smul (t - t₀) L
  -- Step 8: Combine: ‖γ - γ₀‖ ≥ |t-t₀|*‖L‖ - (‖L‖/2)*|t-t₀| = (‖L‖/2)*|t-t₀|
  calc ‖γ t - γ t₀‖ ≥ ‖(t - t₀) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
    _ ≥ |t - t₀| * ‖L‖ - (‖L‖ / 2) * |t - t₀| := by rw [h_smul]; linarith
    _ = (‖L‖ / 2) * |t - t₀| := by ring

/-- Micro-lemma: Upper bound on ‖γ t - γ t₀‖ from non-zero derivative.
Uses hasDerivAt_remainder_bound + triangle inequality. -/
lemma gamma_upper_bound_of_hasDerivAt {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ → ‖γ t - γ t₀‖ ≤ 2 * ‖L‖ * |t - t₀| := by
  -- Step 1: ‖L‖ > 0
  have hLnorm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  -- Step 2: Get δ from hasDerivAt_remainder_bound with ε = ‖L‖
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hasDerivAt_remainder_bound hγ_hasderiv ‖L‖ hLnorm_pos
  -- Step 3: This δ works
  refine ⟨δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  -- Step 4: Get the remainder bound for this t
  have h_rem : ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ ‖L‖ * |t - t₀| := hδ_bound t ht_pos ht_lt
  -- Step 5: Triangle inequality: ‖γ - γ₀‖ ≤ ‖(t-t₀)•L‖ + ‖error‖
  have h_tri : ‖γ t - γ t₀‖ ≤ ‖(t - t₀) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := by
    have h1 : ‖γ t - γ t₀‖ = ‖(t - t₀) • L + (γ t - γ t₀ - (t - t₀) • L)‖ := by
      congr 1; ring
    rw [h1]
    exact norm_add_le _ _
  -- Step 6: ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖
  have h_smul : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ := norm_real_smul (t - t₀) L
  -- Step 7: Combine: ‖γ - γ₀‖ ≤ |t-t₀|*‖L‖ + ‖L‖*|t-t₀| = 2*‖L‖*|t-t₀|
  calc ‖γ t - γ t₀‖ ≤ ‖(t - t₀) • L‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := h_tri
    _ ≤ |t - t₀| * ‖L‖ + ‖L‖ * |t - t₀| := by rw [h_smul]; linarith
    _ = 2 * ‖L‖ * |t - t₀| := by ring

/-- **No-return from injectivity + continuity**: If γ is continuous on [a,b] and injective
    at γ(t₀) (i.e., γ t = γ t₀ implies t = t₀), then γ stays bounded away from γ(t₀)
    outside any neighborhood of t₀. Uses compactness + IsCompact.exists_forall_le'. -/
lemma no_return_of_inj_continuous {γ : ℝ → ℂ} {a b t₀ : ℝ} {c : ℝ}
    (hc_pos : 0 < c)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ ρ > 0, ∀ t ∈ Set.Icc a b, c ≤ |t - t₀| → ρ ≤ ‖γ t - γ t₀‖ := by
  let S := Set.Icc a b ∩ {t | c ≤ |t - t₀|}
  have hS_compact : IsCompact S :=
    isCompact_Icc.inter_right (isClosed_le continuous_const
      (continuous_abs.comp (continuous_id.sub continuous_const)))
  have hf_cont : ContinuousOn (fun t => ‖γ t - γ t₀‖) S :=
    ((hγ_cont.mono Set.inter_subset_left).sub continuousOn_const).norm
  have hf_pos : ∀ t ∈ S, (0 : ℝ) < ‖γ t - γ t₀‖ := by
    intro t ⟨ht_Icc, ht_dist⟩
    rw [norm_pos_iff, sub_ne_zero]
    intro h_eq
    have h_t_eq := h_inj t ht_Icc h_eq
    subst h_t_eq; simp at ht_dist; linarith
  obtain ⟨ρ, hρ_pos, hρ_le⟩ := hS_compact.exists_forall_le' hf_cont hf_pos
  exact ⟨ρ, hρ_pos, fun t ht h_dist => hρ_le t ⟨ht, h_dist⟩⟩

/-! ### Annulus Translation: γ-space ↔ t-space

These lemmas translate between cutoffs in ‖γ - γ₀‖ and cutoffs in |t - t₀|.
Key facts used:
- Lower bound: ‖γ - γ₀‖ ≥ (‖L‖/2) * |t - t₀|
- Upper bound: ‖γ - γ₀‖ ≤ 2 * ‖L‖ * |t - t₀|
-/

/-- From γ-space upper bound to t-space upper bound:
If ‖γ t - γ t₀‖ ≤ εC and we have the lower bound, then |t - t₀| ≤ 2*εC/‖L‖. -/
lemma t_bound_from_gamma_bound {γ : ℝ → ℂ} {t₀ t : ℝ} {L : ℂ} {εC δ : ℝ}
    (hL : L ≠ 0) (hδ_pos : 0 < δ) (ht_pos : 0 < |t - t₀|) (ht_lt : |t - t₀| < δ)
    (h_lower : ∀ s, 0 < |s - t₀| → |s - t₀| < δ → ‖γ s - γ t₀‖ ≥ (‖L‖ / 2) * |s - t₀|)
    (h_gamma_bound : ‖γ t - γ t₀‖ ≤ εC) :
    |t - t₀| ≤ 2 * εC / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_lower_t := h_lower t ht_pos ht_lt
  -- From ‖γ - γ₀‖ ≥ (‖L‖/2)*|t-t₀| and ‖γ - γ₀‖ ≤ εC:
  -- (‖L‖/2)*|t-t₀| ≤ εC, so |t-t₀| ≤ 2*εC/‖L‖
  have h1 : (‖L‖ / 2) * |t - t₀| ≤ εC := le_trans h_lower_t h_gamma_bound
  have h_half_pos : 0 < ‖L‖ / 2 := half_pos hL_norm_pos
  -- (‖L‖/2) * |t-t₀| ≤ εC implies |t-t₀| ≤ 2*εC/‖L‖
  -- Multiply both sides by 2/‖L‖
  have h2 : |t - t₀| ≤ 2 * εC / ‖L‖ := by
    have key : ‖L‖ / 2 * |t - t₀| ≤ εC := h1
    have h_ne : ‖L‖ ≠ 0 := ne_of_gt hL_norm_pos
    calc |t - t₀| = (‖L‖ / 2 * |t - t₀|) / (‖L‖ / 2) := by field_simp
      _ ≤ εC / (‖L‖ / 2) := by apply div_le_div_of_nonneg_right key (le_of_lt h_half_pos)
      _ = 2 * εC / ‖L‖ := by field_simp
  exact h2

/-- From γ-space lower bound to t-space lower bound:
If ‖γ t - γ t₀‖ > εC and we have the upper bound, then |t - t₀| > εC/(2*‖L‖). -/
lemma t_lower_from_gamma_lower {γ : ℝ → ℂ} {t₀ t : ℝ} {L : ℂ} {εC δ : ℝ}
    (hL : L ≠ 0) (hδ_pos : 0 < δ) (ht_pos : 0 < |t - t₀|) (ht_lt : |t - t₀| < δ)
    (h_upper : ∀ s, 0 < |s - t₀| → |s - t₀| < δ → ‖γ s - γ t₀‖ ≤ 2 * ‖L‖ * |s - t₀|)
    (h_gamma_lower : εC < ‖γ t - γ t₀‖) :
    εC / (2 * ‖L‖) < |t - t₀| := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_upper_t := h_upper t ht_pos ht_lt
  -- From ‖γ - γ₀‖ ≤ 2*‖L‖*|t-t₀| and εC < ‖γ - γ₀‖:
  -- εC < 2*‖L‖*|t-t₀|, so εC/(2*‖L‖) < |t-t₀|
  have h1 : εC < 2 * ‖L‖ * |t - t₀| := lt_of_lt_of_le h_gamma_lower h_upper_t
  have h_two_norm_pos : 0 < 2 * ‖L‖ := by linarith
  have h2 : εC / (2 * ‖L‖) < |t - t₀| := by
    have key : εC < 2 * ‖L‖ * |t - t₀| := h1
    calc εC / (2 * ‖L‖) < (2 * ‖L‖ * |t - t₀|) / (2 * ‖L‖) :=
        div_lt_div_of_pos_right key h_two_norm_pos
      _ = |t - t₀| := by field_simp
  exact h2

/-- **Micro-lemma 2A: Continuity of deriv from C²**. If γ is C² at t₀, then deriv γ is continuous at t₀. -/
lemma contAt_deriv_of_contDiffAt_two {γ : ℝ → ℂ} {t₀ : ℝ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) : ContinuousAt (deriv γ) t₀ := by
  -- Get ContDiffOn on some neighborhood
  obtain ⟨u, hu_mem, hγ_on⟩ := hγ_C2.contDiffOn (m := 2) le_rfl (by simp)
  -- Extract an open ball from the neighborhood
  obtain ⟨ε, hε_pos, hball_sub⟩ := Metric.mem_nhds_iff.mp hu_mem
  -- On the open ball, γ is C²
  have hγ_ball : ContDiffOn ℝ 2 γ (Metric.ball t₀ ε) := hγ_on.mono hball_sub
  -- Get continuity of fderiv on the ball
  have h_fderiv_cont : ContinuousOn (fderiv ℝ γ) (Metric.ball t₀ ε) :=
    hγ_ball.continuousOn_fderiv_of_isOpen Metric.isOpen_ball (by norm_cast)
  -- ContinuousOn at a point in the interior gives ContinuousAt
  have h_mem_ball : t₀ ∈ Metric.ball t₀ ε := Metric.mem_ball_self hε_pos
  have h_cont_at_fderiv : ContinuousAt (fderiv ℝ γ) t₀ :=
    h_fderiv_cont.continuousAt (Metric.isOpen_ball.mem_nhds h_mem_ball)
  -- deriv γ t = fderiv ℝ γ t 1 (for functions ℝ → ℂ)
  have h_deriv_eq : deriv γ = (fun t => fderiv ℝ γ t 1) := by
    ext t
    by_cases h : DifferentiableAt ℝ γ t
    · rw [fderiv_deriv]
    · simp [deriv_zero_of_not_differentiableAt h, fderiv_zero_of_not_differentiableAt h]
  rw [h_deriv_eq]
  exact h_cont_at_fderiv.clm_apply continuousAt_const

/-- **Micro-lemma: taylorWithinEval for n=1 gives linear approximation**.
taylorWithinEval f 1 s a x = f(a) + (x - a) • derivWithin f s a -/
lemma taylor_one_eq_linear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (s : Set ℝ) (a x : ℝ) :
    taylorWithinEval f 1 s a x = f a + (x - a) • derivWithin f s a := by
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton]
  simp [iteratedDerivWithin_zero, iteratedDerivWithin_one, Nat.factorial]

/-- **Micro-lemma: ContDiffOn on Icc from ContDiffAt**.
From ContDiffAt ℝ n γ t₀, get ContDiffOn ℝ n γ on some interval Icc (t₀ - δ) (t₀ + δ). -/
lemma contDiffOn_Icc_of_contDiffAt {γ : ℝ → ℂ} {t₀ : ℝ} {n : ℕ}
    (hγ : ContDiffAt ℝ n γ t₀) :
    ∃ δ > 0, ContDiffOn ℝ n γ (Set.Icc (t₀ - δ) (t₀ + δ)) := by
  obtain ⟨u, hu_mem, hγ_on⟩ := hγ.contDiffOn (m := n) le_rfl (by simp)
  obtain ⟨r, hr_pos, hball_sub⟩ := Metric.mem_nhds_iff.mp hu_mem
  use r / 2, by linarith
  apply hγ_on.mono
  intro x hx
  apply hball_sub
  simp only [Metric.mem_ball, Real.dist_eq]
  have h1 : t₀ - r / 2 ≤ x := hx.1
  have h2 : x ≤ t₀ + r / 2 := hx.2
  rw [abs_sub_lt_iff]; constructor <;> linarith

/-- **Micro-lemma: Bound on 2nd derivative on compact interval**.
If γ is C² on Icc a b with a < b, then iteratedDerivWithin 2 γ is bounded on Icc a b. -/
lemma bound_iteratedDerivWithin_two_on_Icc {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 2 γ (Set.Icc a b)) :
    ∃ C ≥ 0, ∀ y ∈ Set.Icc a b, ‖iteratedDerivWithin 2 γ (Set.Icc a b) y‖ ≤ C := by
  -- iteratedDerivWithin 2 is continuous on Icc (from ContDiffOn 2)
  have h_cont : ContinuousOn (iteratedDerivWithin 2 γ (Set.Icc a b)) (Set.Icc a b) :=
    hγ.continuousOn_iteratedDerivWithin (by norm_cast) (uniqueDiffOn_Icc hab)
  -- Continuous on compact implies bounded
  have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
  obtain ⟨M, hM⟩ := h_compact.exists_bound_of_continuousOn h_cont
  by_cases hM_neg : M < 0
  · -- If M < 0, use 0 as the bound (all norms are ≥ 0)
    use 0, le_refl 0
    intro y hy
    have := hM y hy
    linarith [norm_nonneg (iteratedDerivWithin 2 γ (Set.Icc a b) y)]
  · exact ⟨M, le_of_not_gt hM_neg, hM⟩

/-- **Micro-lemma: deriv γ deviation bound from C²**.
From C² at t₀, for points near t₀: ‖γ'(t) - L‖ ≤ K * |t - t₀| for some K. -/
-- **Helper: deriv γ is C¹ at t₀ when γ is C² at t₀**
lemma contDiffAt_one_deriv_of_contDiffAt_two {γ : ℝ → ℂ} {t₀ : ℝ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) : ContDiffAt ℝ 1 (deriv γ) t₀ := by
  -- Step 1: From C² at t₀, get C¹ for fderiv ℝ γ at t₀
  have h_fderiv_C1 : ContDiffAt ℝ 1 (fderiv ℝ γ) t₀ := by
    have h : ContDiffAt ℝ (1 + 1) γ t₀ := hγ_C2
    exact h.fderiv_right_succ
  -- Step 2: deriv γ t = (fderiv ℝ γ t) 1, use CLM application
  have h_const : ContDiffAt ℝ 1 (fun _ : ℝ => (1 : ℝ)) t₀ := contDiffAt_const
  have h_apply := h_fderiv_C1.clm_apply h_const
  -- Step 3: (fun t => (fderiv ℝ γ t) 1) = deriv γ pointwise
  have h_eq : (fun t => (fderiv ℝ γ t) 1) = deriv γ := by ext t; exact fderiv_deriv.symm
  rw [← h_eq]; exact h_apply

lemma deriv_deviation_bound_of_C2 {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ ∀ t, |t - t₀| < δ → ‖deriv γ t - L‖ ≤ K * |t - t₀| := by
  -- Step 1: deriv γ is C¹ at t₀, hence Lipschitz nearby
  have h_deriv_C1 : ContDiffAt ℝ 1 (deriv γ) t₀ := contDiffAt_one_deriv_of_contDiffAt_two hγ_C2
  -- Step 2: Apply exists_lipschitzOnWith
  obtain ⟨K, s, hs_nhds, h_lip⟩ := h_deriv_C1.exists_lipschitzOnWith
  -- Step 3: Extract δ from s ∈ 𝓝 t₀
  obtain ⟨δ, hδ_pos, hball_sub⟩ := Metric.mem_nhds_iff.mp hs_nhds
  use K, δ, hδ_pos
  intro t ht
  -- Step 4: t and t₀ are in s
  have ht_in_s : t ∈ s := hball_sub (Metric.mem_ball.mpr (by rwa [Real.dist_eq]))
  have ht₀_in_s : t₀ ∈ s := hball_sub (Metric.mem_ball.mpr (by simp [hδ_pos]))
  -- Step 5: Apply Lipschitz bound
  have h := h_lip.dist_le_mul t ht_in_s t₀ ht₀_in_s
  rw [dist_eq_norm, hγ_deriv, Real.dist_eq] at h
  exact h

/-- **Micro-lemma 2B1: Quadratic approximation from C²**. For C² function γ at t₀,
γ(t) - γ(t₀) - (t-t₀)*L is O(|t-t₀|²) near t₀.

**Proof sketch**:
1. From ContDiffAt ℝ 2 γ t₀, get ContDiffOn ℝ 2 γ on a ball B(t₀, r)
2. On the ball, γ is C², so deriv γ is C¹, hence Lipschitz with some constant M
3. The Lipschitz bound: ‖(deriv γ)(s) - L‖ ≤ M * |s - t₀| for s in the ball
4. By Mean Value inequality: ‖γ(t) - γ(t₀) - (t-t₀)•L‖ ≤ (M * |t-t₀|) * |t-t₀| = M|t-t₀|²

The technical details involve:
- Getting DifferentiableOn (deriv γ) from ContDiffOn 2
- Bounding ‖deriv(deriv γ)‖ on a compact subset to get the Lipschitz constant M
- Applying Convex.norm_image_sub_le_of_norm_deriv_le (twice conceptually) -/
lemma quadratic_approx_of_contDiffAt_two {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ 0 < K ∧ ∀ t, |t - t₀| < δ →
      ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K * |t - t₀|^2 := by
  -- Step 1: Get deriv deviation bound from C²
  obtain ⟨M, δ₁, hδ₁_pos, h_deriv_dev⟩ := deriv_deviation_bound_of_C2 hγ_C2 hγ_deriv
  -- Step 2: Get a neighborhood where γ is differentiable
  -- From C¹ at t₀, γ is differentiable at t₀, and differentiability is an open condition
  have h_C1_at : ContDiffAt ℝ 1 γ t₀ := hγ_C2.of_le one_le_two
  have h_diff_at : DifferentiableAt ℝ γ t₀ := h_C1_at.differentiableAt le_rfl
  -- Get a ball where γ is differentiable
  -- Use ContDiffAt.eventually for n=1 which gives eventually ContDiffAt 1
  -- Type is WithTop ℕ∞, need (1 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞)
  have h1_ne_top : (1 : WithTop ℕ∞) ≠ ↑(⊤ : ℕ∞) := by
    intro heq
    have : (1 : ℕ∞) = ⊤ := WithTop.coe_injective heq
    exact ENat.one_ne_top this
  have h_evt_C1 : ∀ᶠ s in 𝓝 t₀, ContDiffAt ℝ 1 γ s := h_C1_at.eventually h1_ne_top
  have h_evt_diff : ∀ᶠ s in 𝓝 t₀, DifferentiableAt ℝ γ s :=
    h_evt_C1.mono (fun s hs => hs.differentiableAt le_rfl)
  obtain ⟨δ₂, hδ₂_pos, h_diff_ball⟩ := Metric.eventually_nhds_iff.mp h_evt_diff
  -- Step 3: Use δ = min(δ₁, δ₂) and K = M + 1 to ensure K > 0
  let δ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  let K := M + 1
  -- Prove M ≥ 0 from h_deriv_dev (if M < 0 and |t-t₀| > 0, then M*|t-t₀| < 0, contradiction)
  have hM_nonneg : 0 ≤ M := by
    by_contra hM_neg
    push_neg at hM_neg
    -- Pick t with 0 < |t - t₀| < δ₁
    have ⟨t, ht_pos, ht_lt⟩ : ∃ t, 0 < |t - t₀| ∧ |t - t₀| < δ₁ := by
      use t₀ + δ₁ / 2
      simp only [add_sub_cancel_left, abs_of_pos (half_pos hδ₁_pos)]
      exact ⟨half_pos hδ₁_pos, half_lt_self hδ₁_pos⟩
    have h := h_deriv_dev t ht_lt
    have h_neg : M * |t - t₀| < 0 := mul_neg_of_neg_of_pos hM_neg ht_pos
    linarith [norm_nonneg (deriv γ t - L)]
  have hK_pos : 0 < K := by linarith
  use K, δ, hδ_pos, hK_pos
  intro t ht
  -- Step 4: Handle t = t₀ case
  by_cases ht_eq : t = t₀
  · simp [ht_eq]
  -- Step 5: For t ≠ t₀, use MVT on h(s) = γ(s) - γ(t₀) - (s - t₀) • L
  -- Define helper functions
  let f₁ : ℝ → ℂ := γ
  let f₂ : ℝ → ℂ := fun _ => γ t₀
  let f₃ : ℝ → ℂ := fun s => (s - t₀) • L
  let h := fun s => f₁ s - f₂ s - f₃ s
  have ht_lt_δ₁ : |t - t₀| < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht_lt_δ₂ : |t - t₀| < δ₂ := lt_of_lt_of_le ht (min_le_right _ _)
  -- Step 5a: Show uIcc t₀ t ⊆ ball(t₀, δ₂)
  have h_uIcc_sub_ball : Set.uIcc t₀ t ⊆ Metric.ball t₀ δ₂ := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq]
    exact lt_of_le_of_lt (Set.abs_sub_left_of_mem_uIcc hs) ht_lt_δ₂
  -- Step 5b: γ is differentiable on uIcc
  have h_γ_diff_on : ∀ s ∈ Set.uIcc t₀ t, DifferentiableAt ℝ γ s := by
    intro s hs
    exact h_diff_ball (h_uIcc_sub_ball hs)
  -- Step 5c: Differentiability of components
  have h_f₂_diff : ∀ s, DifferentiableAt ℝ f₂ s := fun _ => differentiableAt_const _
  have h_f₃_diff : ∀ s, DifferentiableAt ℝ f₃ s := fun _ =>
    (differentiableAt_id.sub (differentiableAt_const _)).smul_const _
  -- Step 5d: h is differentiable on uIcc
  have h_diff : ∀ s ∈ Set.uIcc t₀ t, DifferentiableAt ℝ h s := by
    intro s hs
    exact ((h_γ_diff_on s hs).sub (h_f₂_diff s)).sub (h_f₃_diff s)
  -- Step 5e: Compute derivatives
  have h_deriv_f₂ : ∀ s, deriv f₂ s = 0 := fun s => deriv_const s (γ t₀)
  have h_deriv_f₃ : ∀ s, deriv f₃ s = L := fun s => by
    simp only [f₃]
    have hid : deriv (fun x : ℝ => x) s = 1 := deriv_id s
    have hsub : deriv (fun x => x - t₀) s = 1 := by rw [deriv_sub_const, hid]
    rw [deriv_smul_const (differentiableAt_id.sub (differentiableAt_const _)), hsub, one_smul]
  have h_deriv : ∀ s ∈ Set.uIcc t₀ t, deriv h s = deriv γ s - L := by
    intro s hs
    have hs_diff : DifferentiableAt ℝ γ s := h_γ_diff_on s hs
    -- h = f₁ - f₂ - f₃, compute deriv step by step
    have h_eq_sub : h = fun s => (f₁ s - f₂ s) - f₃ s := by ext; simp [h, f₁, f₂, f₃]
    have h_diff_f1f2 : DifferentiableAt ℝ (fun s => f₁ s - f₂ s) s := hs_diff.sub (h_f₂_diff s)
    -- Deriv of subtraction uses standard lemmas
    have step1 : deriv h s = deriv (fun s => (f₁ s - f₂ s) - f₃ s) s := by rw [← h_eq_sub]
    have step2 : deriv (fun s => (f₁ s - f₂ s) - f₃ s) s =
        deriv (fun s => f₁ s - f₂ s) s - deriv f₃ s := deriv_sub h_diff_f1f2 (h_f₃_diff s)
    have step3 : deriv (fun s => f₁ s - f₂ s) s = deriv f₁ s - deriv f₂ s :=
      deriv_sub hs_diff (h_f₂_diff s)
    simp only [step1, step2, step3, h_deriv_f₂, h_deriv_f₃, sub_zero, f₁]
  have h_at_t₀ : h t₀ = 0 := by simp only [h, f₁, f₂, f₃, sub_self, zero_smul]
  -- Step 5f: Bound ‖h'(s)‖ on uIcc
  have h_deriv_bound : ∀ s ∈ Set.uIcc t₀ t, ‖deriv h s‖ ≤ M * |t - t₀| := by
    intro s hs
    rw [h_deriv s hs]
    have hs_bound : |s - t₀| ≤ |t - t₀| := Set.abs_sub_left_of_mem_uIcc hs
    have hs_lt : |s - t₀| < δ₁ := lt_of_le_of_lt hs_bound ht_lt_δ₁
    calc ‖deriv γ s - L‖ ≤ M * |s - t₀| := h_deriv_dev s hs_lt
      _ ≤ M * |t - t₀| := mul_le_mul_of_nonneg_left hs_bound hM_nonneg
  -- Step 5g: Apply MVT
  have h_bound := Convex.norm_image_sub_le_of_norm_deriv_le h_diff
    h_deriv_bound (convex_uIcc t₀ t) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [h_at_t₀, sub_zero, Real.norm_eq_abs] at h_bound
  -- Step 5h: Final calculation
  have h_eq : h t = γ t - γ t₀ - (t - t₀) • L := by simp only [h, f₁, f₂, f₃]
  calc ‖γ t - γ t₀ - (t - t₀) • L‖ = ‖h t‖ := by rw [h_eq]
    _ ≤ M * |t - t₀| * |t - t₀| := h_bound
    _ = M * |t - t₀|^2 := by ring
    _ ≤ K * |t - t₀|^2 := by nlinarith [sq_nonneg |t - t₀|]

/-- **Micro-lemma 2B2: Bounded slope deviation**. For C² function γ at t₀ with γ'(t₀) = L,
the slope (γ(t) - γ(t₀))/(t - t₀) satisfies ‖slope - L‖ ≤ K * |t - t₀| near t₀. -/
lemma bounded_slope_deviation_of_contDiffAt_two {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ 0 < K ∧ ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖(γ t - γ t₀) / (↑(t - t₀)) - L‖ ≤ K * |t - t₀| := by
  -- From quadratic_approx_of_contDiffAt_two:
  -- ‖γ(t) - γ(t₀) - (t-t₀)*L‖ ≤ K₁ * |t-t₀|²
  -- Divide by |t - t₀|:
  -- ‖(γ(t) - γ(t₀))/(t-t₀) - L‖ ≤ K₁ * |t-t₀|
  obtain ⟨K₁, δ₁, hδ₁_pos, hK₁_pos, h_quad⟩ := quadratic_approx_of_contDiffAt_two hγ_C2 hγ_deriv
  refine ⟨K₁, δ₁, hδ₁_pos, hK₁_pos, fun t ht_pos ht_lt => ?_⟩
  have h := h_quad t ht_lt
  -- ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₁ * |t - t₀|²
  -- Need: ‖(γ t - γ t₀) / (t - t₀) - L‖ ≤ K₁ * |t - t₀|
  have ht_ne_real : t - t₀ ≠ 0 := abs_pos.mp ht_pos
  have ht_ne : (↑(t - t₀) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_ne_real
  -- The key algebraic identity:
  -- (γ - γ₀)/(t-t₀) - L = (γ - γ₀ - (t-t₀)*L) / (t-t₀)
  have h_smul_eq : (t - t₀) • L = (↑(t - t₀) : ℂ) * L := Complex.real_smul
  have h_eq : (γ t - γ t₀) / (↑(t - t₀)) - L = (γ t - γ t₀ - (t - t₀) • L) / (↑(t - t₀)) := by
    rw [h_smul_eq]; field_simp [ht_ne]
  rw [h_eq, norm_div]
  -- Now: ‖...‖ / ‖(t-t₀ : ℂ)‖ ≤ K₁ * |t-t₀|² / |t-t₀| = K₁ * |t-t₀|
  have h_norm_eq : ‖(↑(t - t₀) : ℂ)‖ = |t - t₀| := Complex.norm_real _
  rw [h_norm_eq]
  have h_abs_pos : 0 < |t - t₀| := ht_pos
  have h_calc : K₁ * |t - t₀|^2 / |t - t₀| = K₁ * |t - t₀| := by field_simp
  calc ‖γ t - γ t₀ - (t - t₀) • L‖ / |t - t₀|
      ≤ K₁ * |t - t₀|^2 / |t - t₀| := div_le_div_of_nonneg_right h (le_of_lt h_abs_pos)
    _ = K₁ * |t - t₀| := h_calc

/-- **Micro-lemma: Numerator quadratic bound**.
The expression (t - t₀) * γ'(t) - (γ t - γ t₀) is O(|t - t₀|²) for C² functions.

Key computation:
(t - t₀) * γ'(t) - Δγ = (t - t₀) * (γ'(t) - L) - (Δγ - (t - t₀) * L)

where the first term is O(|t-t₀|²) from deriv deviation, and second is O(|t-t₀|²) from quadratic approx. -/
lemma numerator_quadratic_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ}
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) :
    ∃ K δ, 0 < δ ∧ ∀ t, |t - t₀| < δ →
      ‖(↑(t - t₀) : ℂ) * deriv γ t - (γ t - γ t₀)‖ ≤ K * |t - t₀|^2 := by
  -- Get quadratic approx bound
  obtain ⟨K₁, δ₁, hδ₁_pos, _, h_quad⟩ := quadratic_approx_of_contDiffAt_two hγ_C2 hγ_deriv
  -- Get deriv deviation bound
  obtain ⟨K₂, δ₂, hδ₂_pos, h_deriv⟩ := deriv_deviation_bound_of_C2 hγ_C2 hγ_deriv
  let δ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  use K₁ + K₂ + 1, δ, hδ_pos
  intro t ht
  have ht₁ : |t - t₀| < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
  have ht₂ : |t - t₀| < δ₂ := lt_of_lt_of_le ht (min_le_right _ _)
  -- Key algebraic identity: (t-t₀)*γ'(t) - Δγ = (t-t₀)*(γ'(t)-L) - (Δγ - (t-t₀)*L)
  have h_identity : (↑(t - t₀) : ℂ) * deriv γ t - (γ t - γ t₀) =
      (↑(t - t₀) : ℂ) * (deriv γ t - L) - (γ t - γ t₀ - (t - t₀) • L) := by
    rw [Complex.real_smul]; ring
  rw [h_identity]
  -- Bound each term
  have h1 : ‖(↑(t - t₀) : ℂ) * (deriv γ t - L)‖ ≤ |t - t₀| * (K₂ * |t - t₀|) := by
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_left (h_deriv t ht₂) (abs_nonneg _)
  have h2 : ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₁ * |t - t₀|^2 := h_quad t ht₁
  calc ‖(↑(t - t₀) : ℂ) * (deriv γ t - L) - (γ t - γ t₀ - (t - t₀) • L)‖
      ≤ ‖(↑(t - t₀) : ℂ) * (deriv γ t - L)‖ + ‖γ t - γ t₀ - (t - t₀) • L‖ := norm_sub_le _ _
    _ ≤ |t - t₀| * (K₂ * |t - t₀|) + K₁ * |t - t₀|^2 := add_le_add h1 h2
    _ = (K₁ + K₂) * |t - t₀|^2 := by ring
    _ ≤ (K₁ + K₂ + 1) * |t - t₀|^2 := by nlinarith [sq_nonneg |t - t₀|]

/-- **Bounded remainder from C² smoothness**. If γ is C² at t₀ with γ'(t₀) = L ≠ 0,
then the remainder r(t) = (γ-γ₀)⁻¹*γ' - (t-t₀)⁻¹ is bounded near t₀.

Key identity: r(t) = [(t-t₀)*γ'(t) - Δγ] / [Δγ * (t-t₀)]
The numerator is O(|t-t₀|²) and the denominator is ≥ (|L|/2)|t-t₀|², so the ratio is O(1). -/
lemma remainder_bounded_of_C2 {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) :
    ∃ C δ, 0 < δ ∧ ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  -- Step 1: Get HasDerivAt from C²
  have hγ_diff : DifferentiableAt ℝ γ t₀ := hγ_C2.differentiableAt one_le_two
  have hγ_hasderiv : HasDerivAt γ L t₀ := by rw [← hγ_deriv]; exact hγ_diff.hasDerivAt
  -- Step 2: Get lower bound on ‖γ t - γ t₀‖
  obtain ⟨δ₁, hδ₁_pos, h_lower⟩ := gamma_lower_bound_of_hasDerivAt hL hγ_hasderiv
  -- Step 3: Get numerator quadratic bound
  obtain ⟨K, δ₂, hδ₂_pos, h_numer⟩ := numerator_quadratic_bound hγ_C2 hγ_deriv
  -- Step 4: Combine bounds
  let δ := min δ₁ δ₂
  have hδ_pos : 0 < δ := lt_min hδ₁_pos hδ₂_pos
  -- The bound C = 2K/‖L‖
  refine ⟨2 * K / ‖L‖, δ, hδ_pos, fun t ht_pos ht_lt => ?_⟩
  have ht₁ : |t - t₀| < δ₁ := lt_of_lt_of_le ht_lt (min_le_left _ _)
  have ht₂ : |t - t₀| < δ₂ := lt_of_lt_of_le ht_lt (min_le_right _ _)
  -- Key identity: r(t) = numerator / (Δγ * (t - t₀))
  have h_Δγ_ne : γ t - γ t₀ ≠ 0 := by
    have h := h_lower t ht_pos ht₁
    intro heq; rw [heq, norm_zero] at h; linarith [mul_pos (half_pos hL_norm_pos) ht_pos]
  have ht_ne : (↑(t - t₀) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_pos.mp ht_pos)
  have h_identity : (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹ =
      ((↑(t - t₀) : ℂ) * deriv γ t - (γ t - γ t₀)) / ((γ t - γ t₀) * (↑(t - t₀))) := by
    field_simp [h_Δγ_ne, ht_ne]
  rw [h_identity, norm_div]
  -- Bound numerator: ‖(t-t₀)*γ'(t) - Δγ‖ ≤ K * |t - t₀|²
  have h_numer_bound : ‖(↑(t - t₀) : ℂ) * deriv γ t - (γ t - γ t₀)‖ ≤ K * |t - t₀|^2 :=
    h_numer t ht₂
  -- Bound denominator: ‖Δγ * (t - t₀)‖ ≥ (‖L‖/2) * |t - t₀|²
  have h_denom_lower : (‖L‖ / 2) * |t - t₀|^2 ≤ ‖(γ t - γ t₀) * (↑(t - t₀))‖ := by
    rw [norm_mul, Complex.norm_real]
    have h := h_lower t ht_pos ht₁
    calc (‖L‖ / 2) * |t - t₀|^2 = (‖L‖ / 2 * |t - t₀|) * |t - t₀| := by ring
      _ ≤ ‖γ t - γ t₀‖ * |t - t₀| := mul_le_mul_of_nonneg_right h (abs_nonneg _)
  have h_denom_pos : 0 < ‖(γ t - γ t₀) * (↑(t - t₀))‖ := by
    rw [norm_mul, Complex.norm_real]
    exact mul_pos (norm_pos_iff.mpr h_Δγ_ne) ht_pos
  -- Combine: ‖r(t)‖ ≤ K|t-t₀|² / ((‖L‖/2)|t-t₀|²) = 2K/‖L‖
  have h_sq_pos : 0 < |t - t₀|^2 := sq_pos_of_pos ht_pos
  have h_K_nonneg : 0 ≤ K * |t - t₀|^2 :=
    le_trans (norm_nonneg _) h_numer_bound
  have h_d_pos : 0 < (‖L‖ / 2) * |t - t₀|^2 := mul_pos (half_pos hL_norm_pos) h_sq_pos
  calc ‖(↑(t - t₀) : ℂ) * deriv γ t - (γ t - γ t₀)‖ / ‖(γ t - γ t₀) * (↑(t - t₀))‖
      ≤ (K * |t - t₀|^2) / ((‖L‖ / 2) * |t - t₀|^2) :=
        div_le_div₀ h_K_nonneg h_numer_bound h_d_pos h_denom_lower
    _ = 2 * K / ‖L‖ := by field_simp [ne_of_gt h_sq_pos, ne_of_gt hL_norm_pos]

/-- **O(ε) step bound from bounded remainder**. If the remainder is bounded by C,
then the integral over an interval of length ε is bounded by C*ε. -/
lemma remainder_integral_O_eps {r : ℝ → ℂ} {t₀ ε C : ℝ}
    (hε_pos : 0 < ε) (_hC_pos : 0 < C)
    (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ 2*ε → ‖r t‖ ≤ C) :
    ‖∫ t in (t₀ - 2*ε)..(t₀ - ε), r t‖ + ‖∫ t in (t₀ + ε)..(t₀ + 2*ε), r t‖ ≤ 2 * C * ε := by
  have h_left : ‖∫ t in (t₀ - 2*ε)..(t₀ - ε), r t‖ ≤ C * ε := by
    have hb : ∀ t ∈ Set.uIoc (t₀ - 2*ε) (t₀ - ε), ‖r t‖ ≤ C := fun t ht => by
      have ⟨h1, h2⟩ := (Set.uIoc_of_le (by linarith : t₀ - 2*ε ≤ t₀ - ε) ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bound t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_neg (by linarith : t - t₀ < 0)]; linarith
    calc ‖∫ t in (t₀ - 2*ε)..(t₀ - ε), r t‖
        ≤ C * |(t₀ - ε) - (t₀ - 2*ε)| := intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * ε := by rw [show (t₀ - ε) - (t₀ - 2*ε) = ε by ring, abs_of_pos hε_pos]
  have h_right : ‖∫ t in (t₀ + ε)..(t₀ + 2*ε), r t‖ ≤ C * ε := by
    have hb : ∀ t ∈ Set.uIoc (t₀ + ε) (t₀ + 2*ε), ‖r t‖ ≤ C := fun t ht => by
      have ⟨h1, h2⟩ := (Set.uIoc_of_le (by linarith : t₀ + ε ≤ t₀ + 2*ε) ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bound t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_pos (by linarith : t - t₀ > 0)]; linarith
    calc ‖∫ t in (t₀ + ε)..(t₀ + 2*ε), r t‖
        ≤ C * |(t₀ + 2*ε) - (t₀ + ε)| := intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * ε := by rw [show (t₀ + 2*ε) - (t₀ + ε) = ε by ring, abs_of_pos hε_pos]
  linarith

/-- **Symmetric cancellation of 1/(t-t₀)**.

The integral of the odd function 1/(t-t₀) over symmetric intervals cancels:
∫_{t₀-ε₂}^{t₀-ε₁} (t-t₀)⁻¹ + ∫_{t₀+ε₁}^{t₀+ε₂} (t-t₀)⁻¹ = 0 -/
lemma integral_inv_symm (t₀ ε₁ ε₂ : ℝ) (_hε₁ : 0 < ε₁) (_hε₂ : 0 < ε₂) (_hε₁₂ : ε₁ ≤ ε₂) :
    (∫ t in (t₀ - ε₂)..(t₀ - ε₁), (↑(t - t₀) : ℂ)⁻¹) +
    (∫ t in (t₀ + ε₁)..(t₀ + ε₂), (↑(t - t₀) : ℂ)⁻¹) = 0 := by
  have h_odd : ∀ u : ℝ, (↑(-u) : ℂ)⁻¹ = -((↑u : ℂ)⁻¹) := by
    intro u; simp only [ofReal_neg, neg_inv]
  have h_reflect : ∫ t in (t₀ - ε₂)..(t₀ - ε₁), (↑(t - t₀) : ℂ)⁻¹ =
      -(∫ t in (t₀ + ε₁)..(t₀ + ε₂), (↑(t - t₀) : ℂ)⁻¹) := by
    have h1 := intervalIntegral.integral_comp_sub_left
      (f := fun x => (↑(x - t₀) : ℂ)⁻¹) (d := 2 * t₀) (a := t₀ + ε₁) (b := t₀ + ε₂)
    have h_b1 : 2 * t₀ - (t₀ + ε₂) = t₀ - ε₂ := by ring
    have h_b2 : 2 * t₀ - (t₀ + ε₁) = t₀ - ε₁ := by ring
    have h_i : ∀ x, 2 * t₀ - x - t₀ = -(x - t₀) := by intro x; ring
    simp only [h_b1, h_b2, h_i, h_odd] at h1
    rw [intervalIntegral.integral_neg] at h1
    exact h1.symm
  rw [h_reflect, neg_add_cancel]

/-- **Remainder annulus bound**: The integral of remainder terms over an annulus is O(log ratio).

    If ‖r t‖ ≤ η / |t - t₀| on the annulus c₁ < |t - t₀| < c₂, then:
    ‖∫ left piece‖ + ‖∫ right piece‖ ≤ 2 * η * log(c₂/c₁)

    This is the key bound: the remainder integral is controlled by the log ratio. -/
lemma remainder_annulus_bound {r : ℝ → ℂ} {t₀ c₁ c₂ η : ℝ}
    (hc₁_pos : 0 < c₁) (hc₂_pos : 0 < c₂) (hc₁₂ : c₁ < c₂) (hη_pos : 0 < η)
    (hr_bound : ∀ t, c₁ < |t - t₀| → |t - t₀| < c₂ → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - c₂)..(t₀ - c₁), r t‖ + ‖∫ t in (t₀ + c₁)..(t₀ + c₂), r t‖ ≤
      2 * η * Real.log (c₂ / c₁) := by
  have h_log_pos : 0 < Real.log (c₂ / c₁) := Real.log_pos (one_lt_div hc₁_pos |>.mpr hc₁₂)
  -- Bound left piece
  have h_left : ‖∫ t in (t₀ - c₂)..(t₀ - c₁), r t‖ ≤ η * Real.log (c₂ / c₁) := by
    have hab : t₀ - c₂ ≤ t₀ - c₁ := by linarith
    let g : ℝ → ℝ := fun t => η / (t₀ - t)
    have h_norm_le : ∀ t ∈ Set.Ioo (t₀ - c₂) (t₀ - c₁), ‖r t‖ ≤ g t := by
      intro t ⟨ht_lo, ht_hi⟩
      have h_t_minus : t - t₀ < 0 := by linarith
      have h_abs : |t - t₀| = t₀ - t := by rw [abs_of_neg h_t_minus]; ring
      have h_abs_lo : c₁ < |t - t₀| := by rw [h_abs]; linarith
      have h_abs_hi : |t - t₀| < c₂ := by rw [h_abs]; linarith
      have h_bound := hr_bound t h_abs_lo h_abs_hi
      simp only [g]; rw [h_abs] at h_bound; exact h_bound
    have h_norm_le_ae : ∀ᵐ t, t ∈ Set.Ioc (t₀ - c₂) (t₀ - c₁) → ‖r t‖ ≤ g t := by
      have h_meas_zero : MeasureTheory.volume {t₀ - c₁} = 0 := Real.volume_singleton
      have h_compl : ∀ᵐ t, t ∉ ({t₀ - c₁} : Set ℝ) := by
        rw [MeasureTheory.ae_iff]; convert h_meas_zero using 2
        ext t; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, not_not]
      filter_upwards [h_compl] with t ht_ne ht_mem
      have h_in_open : t ∈ Set.Ioo (t₀ - c₂) (t₀ - c₁) := by
        simp only [Set.mem_Ioo, Set.mem_Ioc] at ht_mem ⊢
        refine ⟨ht_mem.1, ?_⟩; simp only [Set.mem_singleton_iff] at ht_ne
        exact lt_of_le_of_ne ht_mem.2 ht_ne
      exact h_norm_le t h_in_open
    have h_g_integrable : IntervalIntegrable g MeasureTheory.volume (t₀ - c₂) (t₀ - c₁) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_const.sub continuousOn_id
      · intro t ht; simp only [Set.uIcc_of_le hab, Set.mem_Icc] at ht; linarith
    have h_bound := intervalIntegral.norm_integral_le_of_norm_le hab h_norm_le_ae h_g_integrable
    have h_g_eq : ∫ t in (t₀ - c₂)..(t₀ - c₁), g t = η * Real.log (c₂ / c₁) := by
      simp only [g]
      have h_subst : ∫ t in (t₀ - c₂)..(t₀ - c₁), η / (t₀ - t) = ∫ u in c₁..c₂, η / u := by
        have h := intervalIntegral.integral_comp_sub_left (fun u => η / u) t₀
          (a := t₀ - c₂) (b := t₀ - c₁)
        simp only [sub_sub_cancel] at h; exact h
      rw [h_subst]
      have h_inv : ∫ u in c₁..c₂, u⁻¹ = Real.log (c₂ / c₁) := integral_inv_of_pos hc₁_pos hc₂_pos
      have h_factor : ∫ u in c₁..c₂, η / u = η * ∫ u in c₁..c₂, u⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]; simp only [div_eq_mul_inv]
      rw [h_factor, h_inv]
    rw [h_g_eq] at h_bound; exact h_bound
  -- Bound right piece
  have h_right : ‖∫ t in (t₀ + c₁)..(t₀ + c₂), r t‖ ≤ η * Real.log (c₂ / c₁) := by
    have hab : t₀ + c₁ ≤ t₀ + c₂ := by linarith
    let g : ℝ → ℝ := fun t => η / (t - t₀)
    have h_norm_le : ∀ t ∈ Set.Ioo (t₀ + c₁) (t₀ + c₂), ‖r t‖ ≤ g t := by
      intro t ⟨ht_lo, ht_hi⟩
      have h_t_minus : t - t₀ > 0 := by linarith
      have h_abs : |t - t₀| = t - t₀ := abs_of_pos h_t_minus
      have h_abs_lo : c₁ < |t - t₀| := by rw [h_abs]; linarith
      have h_abs_hi : |t - t₀| < c₂ := by rw [h_abs]; linarith
      have h_bound := hr_bound t h_abs_lo h_abs_hi
      simp only [g]; rw [h_abs] at h_bound; exact h_bound
    have h_norm_le_ae : ∀ᵐ t, t ∈ Set.Ioc (t₀ + c₁) (t₀ + c₂) → ‖r t‖ ≤ g t := by
      have h_meas_zero : MeasureTheory.volume {t₀ + c₂} = 0 := Real.volume_singleton
      have h_compl : ∀ᵐ t, t ∉ ({t₀ + c₂} : Set ℝ) := by
        rw [MeasureTheory.ae_iff]; convert h_meas_zero using 2
        ext t; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, not_not]
      filter_upwards [h_compl] with t ht_ne ht_mem
      have h_in_open : t ∈ Set.Ioo (t₀ + c₁) (t₀ + c₂) := by
        simp only [Set.mem_Ioo, Set.mem_Ioc] at ht_mem ⊢
        refine ⟨ht_mem.1, ?_⟩; simp only [Set.mem_singleton_iff] at ht_ne
        exact lt_of_le_of_ne ht_mem.2 ht_ne
      exact h_norm_le t h_in_open
    have h_g_integrable : IntervalIntegrable g MeasureTheory.volume (t₀ + c₁) (t₀ + c₂) := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.div continuousOn_const
      · exact continuousOn_id.sub continuousOn_const
      · intro t ht; simp only [Set.uIcc_of_le hab, Set.mem_Icc] at ht; linarith
    have h_bound := intervalIntegral.norm_integral_le_of_norm_le hab h_norm_le_ae h_g_integrable
    have h_g_eq : ∫ t in (t₀ + c₁)..(t₀ + c₂), g t = η * Real.log (c₂ / c₁) := by
      simp only [g]
      have h_subst : ∫ t in (t₀ + c₁)..(t₀ + c₂), η / (t - t₀) = ∫ u in c₁..c₂, η / u := by
        have h := intervalIntegral.integral_comp_sub_right (fun u => η / u) t₀
          (a := t₀ + c₁) (b := t₀ + c₂)
        simp only [add_sub_cancel_left] at h; exact h
      rw [h_subst]
      have h_inv : ∫ u in c₁..c₂, u⁻¹ = Real.log (c₂ / c₁) := integral_inv_of_pos hc₁_pos hc₂_pos
      have h_factor : ∫ u in c₁..c₂, η / u = η * ∫ u in c₁..c₂, u⁻¹ := by
        rw [← intervalIntegral.integral_const_mul]; simp only [div_eq_mul_inv]
      rw [h_factor, h_inv]
    rw [h_g_eq] at h_bound; exact h_bound
  -- Combine
  calc ‖∫ t in (t₀ - c₂)..(t₀ - c₁), r t‖ + ‖∫ t in (t₀ + c₁)..(t₀ + c₂), r t‖
      ≤ η * Real.log (c₂ / c₁) + η * Real.log (c₂ / c₁) := add_le_add h_left h_right
    _ = 2 * η * Real.log (c₂ / c₁) := by ring

/-! ### P1-P4: Scale-dependent smallness and summable step bounds

The key to PV convergence: use `integrand_asymptotic` with shrinking η.
For each target error η' > 0, we get a scale δ where the remainder bound holds.
As η' → 0, the step bounds become summable. -/

/-- **P1: Scale-dependent η**. For any target η > 0, we get δ > 0 where remainder ≤ η/|t-t₀|. -/
lemma exists_eta_delta {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ > 0, ∀ t, 0 < |t - t₀| → |t - t₀| < δ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ η / |t - t₀| := by
  have h_tendsto := integrand_times_t_tendsto_one γ t₀ L hL hγ_hasderiv hγ_cont_deriv
  exact integrand_asymptotic γ t₀ L hL hγ_hasderiv hγ_cont_deriv h_tendsto η hη

/-- **P2: Step bound with scale-dependent η**. At scale ε with remainder bound η/|t-t₀|,
the dyadic step [ε/2, ε] contributes at most 2η*log(2). -/
lemma step_bound_with_eta {r : ℝ → ℂ} {t₀ ε η : ℝ}
    (hε_pos : 0 < ε) (hη_pos : 0 < η)
    (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε)..(t₀ - ε/2), r t‖ + ‖∫ t in (t₀ + ε/2)..(t₀ + ε), r t‖ ≤
      2 * η * Real.log 2 := by
  have h_half_pos : 0 < ε / 2 := by linarith
  have h_half_lt : ε / 2 < ε := by linarith
  have hr_restricted : ∀ t, ε / 2 < |t - t₀| → |t - t₀| < ε → ‖r t‖ ≤ η / |t - t₀| := by
    intro t ht_lo ht_hi; exact hr_bound t (lt_trans h_half_pos ht_lo) (le_of_lt ht_hi)
  have h_ratio_eq : ε / (ε / 2) = 2 := by field_simp
  calc ‖∫ t in (t₀ - ε)..(t₀ - ε/2), r t‖ + ‖∫ t in (t₀ + ε/2)..(t₀ + ε), r t‖
      ≤ 2 * η * Real.log (ε / (ε / 2)) :=
        remainder_annulus_bound h_half_pos hε_pos h_half_lt hη_pos hr_restricted
    _ = 2 * η * Real.log 2 := by rw [h_ratio_eq]

/-- **P3: Error bound extends to smaller scales**. If remainder bound holds at scale δ,
it holds at any smaller scale ε < δ. -/
lemma error_at_smaller_scale {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀) :
    ∀ η' > 0, ∃ δ > 0, ∀ ε, 0 < ε → ε < δ →
      (∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ η' / |t - t₀|) := by
  intro η' hη'
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := exists_eta_delta hL hγ_hasderiv hγ_cont_deriv η' hη'
  refine ⟨δ, hδ_pos, fun ε _hε_pos hε_lt t ht_pos ht_le => ?_⟩
  exact hδ_bound t ht_pos (lt_of_le_of_lt ht_le hε_lt)

/-! ### P0: Define cutoff integral I(ε) -/

/-- **P0: Cutoff integral** I(ε) = ∫_{ε < ‖γ-γ₀‖} (γ-γ₀)⁻¹ * γ'. -/
abbrev cutoffIntegral (γ : ℝ → ℂ) (a b t₀ ε : ℝ) : ℂ :=
  ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0

/-! ### P3: Subsequence selection with summable step bounds

We construct a sequence ε_n → 0 such that at scale ε_n, the error bound η_n = 2^{-n} holds.
This gives step bounds Σ 2^{1-n}*log(2) = 4*log(2) < ∞.

The construction:
- For each n, use `error_at_smaller_scale` with η' = 2^{-n} to get δ_n
- Set ε_n = min(δ_n, ε_{n-1}/2)
- Then ε_n < δ_n, so the bound holds at scale ε_n -/

/-- Helper: The δ function that gives δ_n such that error bound (1/2)^n holds for ε < δ_n. -/
lemma exists_delta_for_error_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀) (n : ℕ) :
    ∃ δ > 0, ∀ ε, 0 < ε → ε < δ →
      (∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1/2)^n / |t - t₀|) :=
  error_at_smaller_scale hL hγ_hasderiv hγ_cont_deriv ((1/2)^n) (by positivity)

/-- Define ε_n recursively: ε_0 = min(δ₀, δ(0))/2, ε_{n+1} = min(ε_n/2, δ(n+1))/2.
    This ensures ε_n < δ_n for all n, allowing the error bound to hold. -/
def summableSubseqAux {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) : ℕ → ℝ :=
  let δ := fun n => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv n).choose
  fun n => Nat.rec
    (min δ₀ (δ 0) / 2)  -- ε_0
    (fun m ε_m => min (ε_m / 2) (δ (m + 1)) / 2)  -- ε_{m+1} given ε_m
    n

/-- ε_0 formula -/
lemma summableSubseqAux_zero {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) :
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ 0 =
      min δ₀ ((exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv 0).choose) / 2 := rfl

/-- ε_{n+1} formula -/
lemma summableSubseqAux_succ {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (n : ℕ) :
    let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
    let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
    ε (n + 1) = min (ε n / 2) (δ (n + 1)) / 2 := rfl

/-- Property (i): ε_n > 0 for all n -/
lemma summableSubseqAux_pos {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    0 < summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
  have hδ_pos : ∀ m, 0 < δ m := fun m =>
    (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose_spec.1
  induction n with
  | zero =>
    simp only [summableSubseqAux_zero]
    have h_min_pos : 0 < min δ₀ (δ 0) := lt_min hδ₀_pos (hδ_pos 0)
    linarith
  | succ m ih =>
    simp only [summableSubseqAux_succ]
    have h_min_pos : 0 < min (ε m / 2) (δ (m + 1)) := lt_min (by linarith) (hδ_pos (m + 1))
    linarith

/-- Property (ii): ε_{n+1} ≤ ε_n / 2 -/
lemma summableSubseqAux_halving {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ (n + 1) ≤
      summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n / 2 := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
  simp only [summableSubseqAux_succ]
  -- ε (n+1) = min (ε n / 2) (δ (n+1)) / 2 ≤ (ε n / 2) / 2 = ε n / 4 < ε n / 2
  have h_min_le : min (ε n / 2) (δ (n + 1)) / 2 ≤ (ε n / 2) / 2 := by
    apply div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num : (0 : ℝ) ≤ 2)
  have h_eq : (ε n / 2) / 2 = ε n / 4 := by ring
  rw [h_eq] at h_min_le
  have hε_pos := summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  linarith

/-- Property (iii): ε_n < δ_n -/
lemma summableSubseqAux_lt_delta {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n < δ n := by
  intro δ
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  have hδ_pos : ∀ m, 0 < δ m := fun m =>
    (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose_spec.1
  induction n with
  | zero =>
    simp only [summableSubseqAux_zero]
    have h_min_le : min δ₀ (δ 0) ≤ δ 0 := min_le_right _ _
    have h_min_pos : 0 < min δ₀ (δ 0) := lt_min hδ₀_pos (hδ_pos 0)
    linarith
  | succ m _ =>
    simp only [summableSubseqAux_succ]
    have h_min_le : min (ε m / 2) (δ (m + 1)) ≤ δ (m + 1) := min_le_right _ _
    have h_min_pos : 0 < min (ε m / 2) (δ (m + 1)) := by
      refine lt_min ?_ (hδ_pos (m + 1))
      have := summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos m
      linarith
    linarith

/-- Property (iv): Error bound holds at scale ε_n with η_n = (1/2)^n -/
lemma summableSubseqAux_error_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    let ε_n := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n
    ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε_n →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1/2)^n / |t - t₀| := by
  intro ε_n t ht_pos ht_le
  let δ := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose
  have hδ_bound := fun m => (exists_delta_for_error_bound hL hγ_hasderiv hγ_cont_deriv m).choose_spec.2
  have hε_pos := summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  have hε_lt_δ := summableSubseqAux_lt_delta hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  exact hδ_bound n ε_n hε_pos hε_lt_δ t ht_pos ht_le

lemma exists_summable_subseq {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 < ε n) ∧ (∀ n, ε (n + 1) ≤ ε n / 2) ∧
      (∀ n, ∀ t, 0 < |t - t₀| → |t - t₀| ≤ ε n →
        ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ (1/2)^n / |t - t₀|) := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  refine ⟨ε, ?_, ?_, ?_⟩
  · exact fun n => summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  · exact fun n => summableSubseqAux_halving hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
  · exact fun n => summableSubseqAux_error_bound hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n

/-! ### P4: Cauchy on basis and PV limit -/

/-- ε_n ≤ ε_0 / 2^n for the summable subsequence -/
lemma summableSubseqAux_le_geometric {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (n : ℕ) :
    summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ n ≤
      summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀ 0 / 2^n := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  induction n with
  | zero => simp
  | succ m ih =>
    have h_halving := summableSubseqAux_halving hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos m
    have hε_m_pos := summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos m
    calc ε (m + 1) ≤ ε m / 2 := h_halving
      _ ≤ (ε 0 / 2^m) / 2 := by apply div_le_div_of_nonneg_right ih (by norm_num : (0 : ℝ) ≤ 2)
      _ = ε 0 / 2^(m + 1) := by rw [pow_succ]; ring

/-- The summable subsequence tends to 0 -/
lemma summableSubseqAux_tendsto_zero {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0)
    (hγ_hasderiv : HasDerivAt γ L t₀) (hγ_cont_deriv : ContinuousAt (deriv γ) t₀)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) :
    Tendsto (summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀) atTop (𝓝 0) := by
  let ε := summableSubseqAux hL hγ_hasderiv hγ_cont_deriv δ₀
  have hε_0_pos := summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos 0
  -- ε n ≤ ε 0 / 2^n → 0
  have h_squeeze : ∀ n, ε n ≤ ε 0 * (1/2)^n := fun n => by
    calc ε n ≤ ε 0 / 2^n := summableSubseqAux_le_geometric hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n
      _ = ε 0 * (1/2)^n := by rw [one_div, inv_pow, ← div_eq_mul_inv]
  have h_geom_tendsto : Tendsto (fun n => ε 0 * (1/2 : ℝ)^n) atTop (𝓝 0) := by
    have h := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)
    have h' := Tendsto.const_mul (ε 0) h
    simp only [mul_zero] at h'
    exact h'
  have h_pos : ∀ n, 0 ≤ ε n := fun n => le_of_lt (summableSubseqAux_pos hL hγ_hasderiv hγ_cont_deriv δ₀ hδ₀_pos n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_geom_tendsto h_pos h_squeeze



/-- The cutoff integrand `t ↦ if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0`
    is interval integrable on [a,b], since it is bounded by M/ε where M bounds ‖deriv γ‖. -/
lemma cutoff_integrand_intervalIntegrable {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hat₀ : t₀ ∈ Set.Ioo a b) (hL : L ≠ 0)
    (hγ_meas : Measurable γ)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b))
    (ε : ℝ) (hε_pos : 0 < ε) :
    IntervalIntegrable
      (fun t => if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)
      MeasureTheory.volume a b := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_deriv_bdd : ∃ M > 0, ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ ≤ M := by
    have h_compact : IsCompact (Set.Icc a b) := isCompact_Icc
    have h_cont : ContinuousOn (fun t => ‖deriv γ t‖) (Set.Icc a b) :=
      continuous_norm.comp_continuousOn hγ_cont_deriv
    have h_nonempty : (Set.Icc a b).Nonempty := ⟨t₀, Set.Ioo_subset_Icc_self hat₀⟩
    obtain ⟨x_max, hx_mem, hx_max⟩ := h_compact.exists_isMaxOn h_nonempty h_cont
    exact ⟨max (‖deriv γ x_max‖) 1, lt_max_of_lt_right one_pos,
      fun t ht => le_max_of_le_left (hx_max ht)⟩
  obtain ⟨M_deriv, hM_pos, hM_deriv⟩ := h_deriv_bdd
  have hM_bound_pos : 0 < M_deriv / ε := div_pos hM_pos hε_pos
  have h_norm_bound_ae : ∀ t ∈ Set.uIoc a b,
      ‖(if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)‖ ≤ M_deriv / ε := by
    intro t ht_uIoc
    have hab : a < b := hat₀.1.trans hat₀.2
    have ht : t ∈ Set.Icc a b := by
      rw [Set.uIoc_of_le (le_of_lt hab)] at ht_uIoc
      exact Set.Ioc_subset_Icc_self ht_uIoc
    by_cases h_in : ε < ‖γ t - γ t₀‖
    · simp only [h_in, ↓reduceIte]
      have h_bound : ‖(γ t - γ t₀)⁻¹‖ ≤ 1 / ε := by
        rw [norm_inv, one_div]
        exact inv_anti₀ hε_pos (le_of_lt h_in)
      have h_deriv_bound : ‖deriv γ t‖ ≤ M_deriv := hM_deriv t ht
      calc ‖(γ t - γ t₀)⁻¹ * deriv γ t‖
          = ‖(γ t - γ t₀)⁻¹‖ * ‖deriv γ t‖ := norm_mul _ _
        _ ≤ (1 / ε) * M_deriv := by
            apply mul_le_mul h_bound h_deriv_bound (norm_nonneg _)
            exact le_of_lt (one_div_pos.mpr hε_pos)
        _ = M_deriv / ε := by ring
    · simp only [h_in, ↓reduceIte, norm_zero, hM_bound_pos.le]
  rw [intervalIntegrable_iff]
  apply MeasureTheory.IntegrableOn.of_bound
  · exact measure_Ioc_lt_top
  · apply AEStronglyMeasurable.indicator
    · apply Measurable.aestronglyMeasurable
      exact ((hγ_meas.sub_const (γ t₀)).inv.mul (measurable_deriv γ))
    · exact (measurable_norm.comp (hγ_meas.sub_const (γ t₀))) measurableSet_Ioi
  · rw [MeasureTheory.ae_restrict_iff']
    · filter_upwards with t ht using h_norm_bound_ae t ht
    · exact measurableSet_uIoc

/-- **Cutoff difference as annulus integral**: When ε₁ ≤ ε₂, the difference of cutoff integrals
    equals the integral over the annulus {ε₁ < ‖γ-γ₀‖ ≤ ε₂}. -/
lemma cutoff_diff_eq_annulus_integral {f : ℝ → ℂ} {γ : ℝ → ℂ} {a b t₀ : ℝ}
    {ε₁ ε₂ : ℝ} (h_le : ε₁ ≤ ε₂)
    (h_int₁ : IntervalIntegrable (fun t => if ε₁ < ‖γ t - γ t₀‖ then f t else 0) MeasureTheory.volume a b)
    (h_int₂ : IntervalIntegrable (fun t => if ε₂ < ‖γ t - γ t₀‖ then f t else 0) MeasureTheory.volume a b) :
    (∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ then f t else 0) -
    (∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ then f t else 0) =
    ∫ t in a..b, if ε₁ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₂ then f t else 0 := by
  rw [← intervalIntegral.integral_sub h_int₁ h_int₂]
  congr 1; ext t
  by_cases h1 : ε₁ < ‖γ t - γ t₀‖
  · by_cases h2 : ε₂ < ‖γ t - γ t₀‖
    · -- Both indicators are 1: diff = 0, annulus condition false
      simp only [h1, h2, ↓reduceIte, sub_self, not_le.mpr h2, and_false]
    · -- First is 1, second is 0: diff = f, annulus condition true
      simp only [h1, h2, ↓reduceIte, sub_zero, not_lt.mp h2, and_self]
  · by_cases h2 : ε₂ < ‖γ t - γ t₀‖
    · -- First is 0, second is 1: impossible since ε₁ ≤ ε₂ < ‖γ‖ but ‖γ‖ ≤ ε₁
      have h1' : ‖γ t - γ t₀‖ ≤ ε₁ := not_lt.mp h1
      exact absurd (lt_of_le_of_lt h1' (lt_of_le_of_lt h_le h2)) (lt_irrefl _)
    · -- Both indicators are 0: diff = 0, annulus condition false
      simp only [h1, h2, ↓reduceIte, sub_self, false_and]

/-! ### Micro-lemmas for pv_limit_exists -/

/-- **Micro-lemma 1: Singular part cancellation**. For any symmetric ε-cutoff around t₀,
the integral of (t - t₀)⁻¹ is zero by the odd function cancellation. -/
lemma pv_singular_cancels (t₀ ε δ : ℝ) (hε_pos : 0 < ε) (hδ_pos : 0 < δ) (hεδ : ε < δ) :
    (∫ t in (t₀ - δ)..(t₀ - ε), (↑(t - t₀) : ℂ)⁻¹) +
    (∫ t in (t₀ + ε)..(t₀ + δ), (↑(t - t₀) : ℂ)⁻¹) = 0 := by
  exact integral_inv_symm t₀ ε δ hε_pos hδ_pos (le_of_lt hεδ)

/-- **Micro-lemma 2: Remainder step bound**. The remainder integral over a dyadic step
[ε/2, ε] is bounded by 2η * log(2). -/
lemma remainder_step_bound {r : ℝ → ℂ} {t₀ ε η : ℝ}
    (hε_pos : 0 < ε) (_hη_pos : 0 < η)
    (hr_bound : ∀ t, ε / 2 < |t - t₀| → |t - t₀| < ε → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε)..(t₀ - ε/2), r t‖ + ‖∫ t in (t₀ + ε/2)..(t₀ + ε), r t‖ ≤
      2 * η * Real.log 2 := by
  have h_half_pos : 0 < ε / 2 := by linarith
  have h_half_lt : ε / 2 < ε := by linarith
  have h_ratio_eq : ε / (ε / 2) = 2 := by field_simp
  have h_log_eq : Real.log (ε / (ε / 2)) = Real.log 2 := by rw [h_ratio_eq]
  calc ‖∫ t in (t₀ - ε)..(t₀ - ε/2), r t‖ + ‖∫ t in (t₀ + ε/2)..(t₀ + ε), r t‖
      ≤ 2 * η * Real.log (ε / (ε / 2)) :=
        remainder_annulus_bound h_half_pos hε_pos h_half_lt (by linarith) hr_bound
    _ = 2 * η * Real.log 2 := by rw [h_log_eq]

/-- **Micro-lemma 3: Remainder bounded ratio**. For a fixed ratio bound K,
the remainder integral over annuli with ratio ≤ K is bounded by 2η * log(K). -/
lemma remainder_bounded_ratio {r : ℝ → ℂ} {t₀ ε₁ ε₂ η K : ℝ}
    (hε₁_pos : 0 < ε₁) (hε₁₂ : ε₁ < ε₂) (hη_pos : 0 < η)
    (hK : 1 < K) (h_ratio : ε₂ / ε₁ ≤ K)
    (hr_bound : ∀ t, ε₁ < |t - t₀| → |t - t₀| < ε₂ → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε₂)..(t₀ - ε₁), r t‖ + ‖∫ t in (t₀ + ε₁)..(t₀ + ε₂), r t‖ ≤
      2 * η * Real.log K := by
  have h_base := remainder_annulus_bound hε₁_pos (lt_trans hε₁_pos hε₁₂) hε₁₂ hη_pos hr_bound
  have h_ratio_pos : 0 < ε₂ / ε₁ := div_pos (lt_trans hε₁_pos hε₁₂) hε₁_pos
  have h_log_le : Real.log (ε₂ / ε₁) ≤ Real.log K := Real.log_le_log h_ratio_pos h_ratio
  calc ‖∫ t in (t₀ - ε₂)..(t₀ - ε₁), r t‖ + ‖∫ t in (t₀ + ε₁)..(t₀ + ε₂), r t‖
      ≤ 2 * η * Real.log (ε₂ / ε₁) := h_base
    _ ≤ 2 * η * Real.log K := by nlinarith [Real.log_pos hK]

/-- **Micro-lemma 4: Dyadic sequence Cauchy**. Along the dyadic sequence ε_n = ε₀/2^n,
the remainder integrals form a Cauchy sequence. -/
lemma remainder_dyadic_step {r : ℝ → ℂ} {t₀ ε₀ η : ℝ} (n : ℕ)
    (hε₀_pos : 0 < ε₀) (hη_pos : 0 < η)
    (hr_bound : ∀ t, 0 < |t - t₀| → |t - t₀| < ε₀ → ‖r t‖ ≤ η / |t - t₀|) :
    ‖∫ t in (t₀ - ε₀/2^n)..(t₀ - ε₀/2^(n+1)), r t‖ +
    ‖∫ t in (t₀ + ε₀/2^(n+1))..(t₀ + ε₀/2^n), r t‖ ≤ 2 * η * Real.log 2 := by
  have h_pow_pos : (0 : ℝ) < 2^n := by positivity
  have h_pow1_pos : (0 : ℝ) < 2^(n+1) := by positivity
  have hε_n_pos : 0 < ε₀ / 2^n := div_pos hε₀_pos h_pow_pos
  have hε_n1_pos : 0 < ε₀ / 2^(n+1) := div_pos hε₀_pos h_pow1_pos
  have h_lt : ε₀ / 2^(n+1) < ε₀ / 2^n := by
    have h_pow_lt : (2 : ℝ)^n < 2^(n+1) := by
      have h : (2 : ℝ)^(n+1) = 2^n * 2 := by ring
      rw [h]; linarith
    exact div_lt_div_of_pos_left hε₀_pos h_pow_pos h_pow_lt
  have h_ratio : (ε₀ / 2^n) / (ε₀ / 2^(n+1)) = 2 := by field_simp; ring
  have hr_restricted : ∀ t, ε₀ / 2^(n+1) < |t - t₀| → |t - t₀| < ε₀ / 2^n →
      ‖r t‖ ≤ η / |t - t₀| := by
    intro t ht_lo ht_hi
    have ht_pos : 0 < |t - t₀| := lt_trans hε_n1_pos ht_lo
    have ht_lt : |t - t₀| < ε₀ := by
      have h1 : ε₀ / 2^n ≤ ε₀ := div_le_self hε₀_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      exact lt_of_lt_of_le ht_hi h1
    exact hr_bound t ht_pos ht_lt
  have h_bound := remainder_bounded_ratio hε_n1_pos h_lt hη_pos (by norm_num : (1 : ℝ) < 2)
    (by rw [h_ratio]) hr_restricted
  convert h_bound using 2

/-! ### Dyadic sequence approach for PV convergence

The key insight: with **bounded** remainder (from C² smoothness), the step bounds are O(ε),
and the dyadic sum Σ C*ε_n = Σ C*δ₀/2^n converges geometrically. -/

/-- **Dyadic step bound with bounded remainder**. If the remainder r is bounded by C,
then the cutoff integral difference over a dyadic step is O(ε_n). -/
lemma pv_dyadic_step_O_eps {r : ℝ → ℂ} {t₀ δ₀ C : ℝ} (n : ℕ)
    (hδ₀_pos : 0 < δ₀) (_hC_pos : 0 < C)
    (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| ≤ δ₀ → ‖r t‖ ≤ C) :
    let ε_n := δ₀ / 2^n
    ‖∫ t in (t₀ - ε_n)..(t₀ - ε_n/2), r t‖ + ‖∫ t in (t₀ + ε_n/2)..(t₀ + ε_n), r t‖ ≤
      C * ε_n := by
  intro ε_n
  have h_pow_pos : (0 : ℝ) < 2^n := by positivity
  have hε_n_pos : 0 < ε_n := div_pos hδ₀_pos h_pow_pos
  have hε_n_half_pos : 0 < ε_n / 2 := by positivity
  have hε_n_le_δ₀ : ε_n ≤ δ₀ := div_le_self hδ₀_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have h_left : ‖∫ t in (t₀ - ε_n)..(t₀ - ε_n/2), r t‖ ≤ C * (ε_n / 2) := by
    have hb : ∀ t ∈ Set.uIoc (t₀ - ε_n) (t₀ - ε_n/2), ‖r t‖ ≤ C := fun t ht => by
      have hle : t₀ - ε_n ≤ t₀ - ε_n/2 := by linarith
      have ⟨h1, h2⟩ := (Set.uIoc_of_le hle ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bounded t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_neg (by linarith : t - t₀ < 0)]; linarith
    calc ‖∫ t in (t₀ - ε_n)..(t₀ - ε_n/2), r t‖
        ≤ C * |(t₀ - ε_n/2) - (t₀ - ε_n)| := intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * (ε_n / 2) := by rw [show (t₀ - ε_n/2) - (t₀ - ε_n) = ε_n/2 by ring, abs_of_pos hε_n_half_pos]
  have h_right : ‖∫ t in (t₀ + ε_n/2)..(t₀ + ε_n), r t‖ ≤ C * (ε_n / 2) := by
    have hb : ∀ t ∈ Set.uIoc (t₀ + ε_n/2) (t₀ + ε_n), ‖r t‖ ≤ C := fun t ht => by
      have hle : t₀ + ε_n/2 ≤ t₀ + ε_n := by linarith
      have ⟨h1, h2⟩ := (Set.uIoc_of_le hle ▸ ht : t ∈ Set.Ioc _ _)
      refine hr_bounded t (abs_pos.mpr (by linarith)) ?_
      rw [abs_of_pos (by linarith : t - t₀ > 0)]; linarith
    calc ‖∫ t in (t₀ + ε_n/2)..(t₀ + ε_n), r t‖
        ≤ C * |(t₀ + ε_n) - (t₀ + ε_n/2)| := intervalIntegral.norm_integral_le_of_norm_le_const hb
      _ = C * (ε_n / 2) := by rw [show (t₀ + ε_n) - (t₀ + ε_n/2) = ε_n/2 by ring, abs_of_pos hε_n_half_pos]
  linarith

/-- **Dyadic sequence is Cauchy**. With bounded remainder, the cutoff integral
along the dyadic sequence ε_n = δ₀/2^n is Cauchy. -/
lemma cauchySeq_pv_dyadic {I : ℝ → ℂ} {δ₀ C : ℝ}
    (_hδ₀_pos : 0 < δ₀) (_hC_pos : 0 < C)
    (h_step : ∀ n, ‖I (δ₀ / 2^(n+1)) - I (δ₀ / 2^n)‖ ≤ C * δ₀ / 2^n) :
    CauchySeq (fun n => I (δ₀ / 2^n)) := by
  -- Use cauchySeq_of_le_geometric: dist (f n) (f (n+1)) ≤ C * r^n with r < 1
  refine cauchySeq_of_le_geometric (1/2) (C * δ₀) (by norm_num) (fun n => ?_)
  rw [dist_comm]
  calc dist (I (δ₀ / 2 ^ (n + 1))) (I (δ₀ / 2 ^ n))
      = ‖I (δ₀ / 2 ^ (n + 1)) - I (δ₀ / 2 ^ n)‖ := dist_eq_norm _ _
    _ ≤ C * δ₀ / 2 ^ n := h_step n
    _ = C * δ₀ * (1 / 2) ^ n := by rw [one_div, inv_pow, ← div_eq_mul_inv]

/-- **t-space bound from γ-space**: On the γ-annulus {‖γ - γ₀‖ ≤ ε}, we have |t - t₀| ≤ 2ε/‖L‖.
    This inverts the lower bound h_lower. -/
lemma t_bound_from_gamma_annulus {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {δ₁ ε : ℝ}
    (hL : L ≠ 0) (hε_pos : 0 < ε)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (t : ℝ) (ht_pos : 0 < |t - t₀|) (ht_lt : |t - t₀| < δ₁) (hγ_bound : ‖γ t - γ t₀‖ ≤ ε) :
    |t - t₀| ≤ 2 * ε / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have h_low := h_lower t ht_pos ht_lt
  calc |t - t₀| = 2 * ((‖L‖ / 2) * |t - t₀|) / ‖L‖ := by field_simp
    _ ≤ 2 * ‖γ t - γ t₀‖ / ‖L‖ := by apply div_le_div_of_nonneg_right; linarith; exact hL_norm_pos.le
    _ ≤ 2 * ε / ‖L‖ := by apply div_le_div_of_nonneg_right; linarith; exact hL_norm_pos.le

/-- **Integrand bound on γ-annulus**: When ε₂ < ‖γ - γ₀‖, the integrand satisfies
    ‖(γ-γ₀)⁻¹ * deriv γ‖ ≤ |(t-t₀)⁻¹| + C on the domain of hr_bounded. -/
lemma integrand_bound_on_annulus {γ : ℝ → ℂ} {t₀ : ℝ} {C δ₀ : ℝ}
    (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C)
    (t : ℝ) (ht_pos : 0 < |t - t₀|) (ht_lt : |t - t₀| < δ₀) :
    ‖(γ t - γ t₀)⁻¹ * deriv γ t‖ ≤ |t - t₀|⁻¹ + C := by
  have hr := hr_bounded t ht_pos ht_lt
  have h_tri := norm_sub_norm_le ((γ t - γ t₀)⁻¹ * deriv γ t) (↑(t - t₀))⁻¹
  have h_inv_norm : ‖(↑(t - t₀) : ℂ)⁻¹‖ = |t - t₀|⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc ‖(γ t - γ t₀)⁻¹ * deriv γ t‖
      ≤ ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ + ‖(↑(t - t₀) : ℂ)⁻¹‖ := by linarith [h_tri]
    _ ≤ C + |t - t₀|⁻¹ := by rw [h_inv_norm]; linarith
    _ = |t - t₀|⁻¹ + C := by ring

/-- **Micro-lemma (B): Annulus localization**. Points in the γ-annulus lie in the local zone. -/
lemma annulus_implies_t_local {γ : ℝ → ℂ} {a b t₀ : ℝ} {ε₁ δ₀ δ₁ : ℝ}
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁)
    (t : ℝ) (ht_ab : t ∈ Set.Icc a b) (hγ_bound : ‖γ t - γ t₀‖ ≤ ε₁) :
    |t - t₀| < δ₀ ∧ |t - t₀| < δ₁ := by
  have h := h_localize t ht_ab hγ_bound
  exact ⟨lt_of_lt_of_le h (min_le_left _ _), lt_of_lt_of_le h (min_le_right _ _)⟩

/-- **Micro-lemma (C): Measure bound**. The t-region where ε₂ < ‖γ‖ ≤ ε₁ has measure ≤ 4ε₁/‖L‖.
    More precisely, on the annulus we have |t-t₀| ≤ 2ε₁/‖L‖, so the full t-region
    has width ≤ 4ε₁/‖L‖ (both sides of t₀). -/
lemma annulus_t_measure_bound {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ} {ε₁ ε₂ δ₁ : ℝ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁)
    (h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁)
    (t : ℝ) (ht_ab : t ∈ Set.Icc a b) (_ht_ne : t ≠ t₀)
    (hγ_lower : ε₂ < ‖γ t - γ t₀‖) (hγ_upper : ‖γ t - γ t₀‖ ≤ ε₁) :
    |t - t₀| ≤ 2 * ε₁ / ‖L‖ := by
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  have ht_local := h_localize t ht_ab hγ_upper
  have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr _ht_ne)
  have ht_lt_δ₁ : |t - t₀| < δ₁ := lt_of_lt_of_le ht_local (min_le_right _ _)
  exact t_bound_from_gamma_annulus hL hε₁_pos h_lower t ht_pos ht_lt_δ₁ hγ_upper

/-- **Micro-lemma (E): Remainder integral bound**. The integral of the remainder term
    over the annulus is bounded by C times the measure. -/
lemma remainder_integral_bound_on_annulus {γ : ℝ → ℂ} {a b t₀ : ℝ} {C δ₀ δ₁ ε₁ ε₂ : ℝ} {L : ℂ}
    (hL : L ≠ 0) (hε₁_pos : 0 < ε₁) (hε₂_pos : 0 < ε₂)
    (hr_bounded : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₀ →
      ‖(γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹‖ ≤ C)
    (_h_lower : ∀ t, 0 < |t - t₀| → |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ (‖L‖ / 2) * |t - t₀|)
    (h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁)
    (_hat₀ : t₀ ∈ Set.Ioo a b) :
    let r := fun t => (γ t - γ t₀)⁻¹ * deriv γ t - (↑(t - t₀))⁻¹
    ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ ≤
      max 0 C * (4 * ε₁ / ‖L‖) := by
  intro r
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  -- From _hat₀ : t₀ ∈ Ioo a b, we get a < b
  have hab : a < b := (Set.mem_Ioo.mp _hat₀).1.trans_le (le_of_lt (Set.mem_Ioo.mp _hat₀).2)
  -- Step 1: Pointwise bound on integrand
  have h_pw_bound : ∀ t ∈ Set.uIoc a b,
      ‖if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ ≤ max 0 C := by
    intro t ht
    by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · simp only [hcond, ↓reduceIte]
      -- On annulus, use hr_bounded
      -- Since a < b, we have uIoc a b = Ioc a b ⊆ Icc a b
      have ht_in_Icc : t ∈ Set.Icc a b := by
        rw [Set.uIoc_eq_union] at ht
        rcases ht with ht_ab | ht_ba
        · exact Set.Ioc_subset_Icc_self ht_ab
        · -- ht_ba : t ∈ Ioc b a, but a < b, so Ioc b a = ∅
          rw [Set.Ioc_eq_empty_of_le hab.le] at ht_ba
          exact absurd ht_ba (Set.not_mem_empty t)
      have ht_loc := h_localize t ht_in_Icc hcond.2
      by_cases ht_eq : t = t₀
      · simp only [ht_eq, sub_self, norm_zero] at hcond
        exact absurd hcond.1 (not_lt.mpr hε₂_pos.le)
      have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_eq)
      have ht_lt_δ₀ : |t - t₀| < δ₀ := lt_of_lt_of_le ht_loc (min_le_left _ _)
      have hr_t := hr_bounded t ht_pos ht_lt_δ₀
      simp only [r] at hr_t ⊢
      exact le_trans hr_t (le_max_right 0 C)
    · simp only [hcond, ↓reduceIte, norm_zero, le_max_iff, le_refl, true_or]
  -- Step 2: Define the support set S = {t ∈ [a,b] | ε₂ < ‖γ‖ ≤ ε₁}
  -- The integrand is S.indicator r, so ∫ = ∫_S r
  -- Use: ‖∫_S r‖ ≤ (max 0 C) * measure(S) ≤ (max 0 C) * (4ε₁/‖L‖)
  -- where measure(S) ≤ 4ε₁/‖L‖ because S ⊆ {t | |t-t₀| ≤ 2ε₁/‖L‖}
  let S := {t ∈ Set.Icc a b | ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
  -- Step 3: Support measure bound - S is contained in an interval of width 4ε₁/‖L‖
  have hS_subset : S ⊆ Set.Icc (t₀ - 2 * ε₁ / ‖L‖) (t₀ + 2 * ε₁ / ‖L‖) := by
    intro t ht
    obtain ⟨ht_ab, hε_lower, hε_upper⟩ := ht
    -- Use annulus_t_measure_bound: on annulus, |t - t₀| ≤ 2ε₁/‖L‖
    have h_loc_adapted : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₁ δ₁ := by
      intro s hs hγs
      simp only [min_self]
      exact lt_of_lt_of_le (h_localize s hs hγs) (min_le_right _ _)
    by_cases ht_eq : t = t₀
    · -- t = t₀ is trivially in the interval around t₀
      rw [ht_eq, Set.mem_Icc]
      have h_term_pos : 0 < 2 * ε₁ / ‖L‖ := by positivity
      constructor
      · linarith [h_term_pos]
      · linarith [h_term_pos]
    have ht_bound := annulus_t_measure_bound hL hε₁_pos _h_lower h_loc_adapted t ht_ab ht_eq
      hε_lower hε_upper
    rw [abs_le] at ht_bound
    exact Set.mem_Icc.mpr ⟨by linarith [ht_bound.1], by linarith [ht_bound.2]⟩
  -- Step 4: Measure of S is at most 4ε₁/‖L‖
  have hS_measure : MeasureTheory.volume S ≤ ENNReal.ofReal (4 * ε₁ / ‖L‖) := by
    have h_width : (t₀ + 2 * ε₁ / ‖L‖) - (t₀ - 2 * ε₁ / ‖L‖) = 4 * ε₁ / ‖L‖ := by ring
    calc MeasureTheory.volume S
        ≤ MeasureTheory.volume (Set.Icc (t₀ - 2 * ε₁ / ‖L‖) (t₀ + 2 * ε₁ / ‖L‖)) :=
          MeasureTheory.measure_mono hS_subset
      _ = ENNReal.ofReal ((t₀ + 2 * ε₁ / ‖L‖) - (t₀ - 2 * ε₁ / ‖L‖)) := Real.volume_Icc
      _ = ENNReal.ofReal (4 * ε₁ / ‖L‖) := by rw [h_width]
  -- Step 5: Pointwise bound on r over S
  have hr_bound_on_S : ∀ t ∈ S, ‖r t‖ ≤ max 0 C := by
    intro t ⟨ht_ab, hε_lower, hε_upper⟩
    by_cases ht_eq : t = t₀
    · -- If t = t₀, then ‖γ t - γ t₀‖ = 0, but hε_lower says ε₂ < 0, contradiction
      simp only [ht_eq, sub_self, norm_zero] at hε_lower
      exact absurd hε_lower (not_lt.mpr hε₂_pos.le)
    have ht_loc := h_localize t ht_ab hε_upper
    have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_eq)
    have ht_lt_δ₀ : |t - t₀| < δ₀ := lt_of_lt_of_le ht_loc (min_le_left _ _)
    have hr_t := hr_bounded t ht_pos ht_lt_δ₀
    simp only [r] at hr_t ⊢
    exact le_trans hr_t (le_max_right 0 C)
  -- Step 6: Route A - Use h_zero_of_far to restrict integral to small interval
  -- R2: Integrand is 0 when |t - t₀| > 2ε₁/‖L‖ (contrapositive of annulus_t_measure_bound)
  have h_zero_of_far : ∀ t ∈ Set.uIoc a b, 2 * ε₁ / ‖L‖ < |t - t₀| →
      (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) = 0 := by
    intro t ht h_far
    by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · exfalso
      have ht_in_Icc : t ∈ Set.Icc a b := by
        rw [Set.uIoc_eq_union] at ht
        rcases ht with ht_ab | ht_ba
        · exact Set.Ioc_subset_Icc_self ht_ab
        · rw [Set.Ioc_eq_empty_of_le hab.le] at ht_ba
          exact absurd ht_ba (Set.notMem_empty t)
      by_cases ht_eq : t = t₀
      · simp only [ht_eq, sub_self, norm_zero] at hcond
        exact absurd hcond.1 (not_lt.mpr hε₂_pos.le)
      have h_loc_adapted : ∀ s ∈ Set.Icc a b, ‖γ s - γ t₀‖ ≤ ε₁ → |s - t₀| < min δ₁ δ₁ := by
        intro s hs hγs; simp only [min_self]
        exact lt_of_lt_of_le (h_localize s hs hγs) (min_le_right _ _)
      have ht_bound := annulus_t_measure_bound hL hε₁_pos _h_lower h_loc_adapted t ht_in_Icc ht_eq
        hcond.1 hcond.2
      exact not_lt.mpr ht_bound h_far
    · simp only [hcond, ↓reduceIte]
  -- R4: Apply norm_integral_le_of_norm_le_const with pointwise bound
  -- Key: integrand is bounded by max 0 C, and is 0 outside a small interval
  -- Use direct bound: ‖∫ f‖ ≤ (sup ‖f‖) * |b - a| with the additional fact that f = 0 outside S
  -- Since the integrand vanishes outside |t - t₀| ≤ 2ε₁/‖L‖, and S has measure ≤ 4ε₁/‖L‖,
  -- the effective integration region has measure ≤ 4ε₁/‖L‖
  -- This requires measure-theory conversion; use sorry for now with clear documentation
  -- Use comparison function approach with norm_integral_le_of_norm_le
  -- The integrand is bounded by max 0 C and supported in [t₀-R, t₀+R] where R = 2ε₁/‖L‖
  set R := 2 * ε₁ / ‖L‖ with hR_def
  have hR_pos : 0 < R := by positivity
  set Icontain := Set.Icc (t₀ - R) (t₀ + R) with hI_def
  -- Comparison function: max 0 C on Icontain, 0 elsewhere
  set g_comp : ℝ → ℝ := Icontain.indicator (fun _ => max 0 C) with hg_comp_def
  -- Step 1: g_comp is interval integrable (bounded + measurable indicator)
  have hg_int : IntervalIntegrable g_comp volume a b := by
    constructor <;>
      exact (MeasureTheory.integrableOn_const (hs := measure_Ioc_lt_top.ne)).indicator
        measurableSet_Icc
  -- Step 2: Pointwise bound on Ioc a b (not just a.e.!)
  -- For t ∈ Icontain: use h_pw_bound. For t ∉ Icontain: h_zero_of_far gives 0.
  have h_pw_le : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b →
      ‖if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ ≤ g_comp t := by
    apply Filter.Eventually.of_forall
    intro t ht
    simp only [g_comp, Set.indicator]
    by_cases ht_in : t ∈ Icontain
    · simp only [ht_in, ↓reduceIte]
      have ht_uIoc : t ∈ Ι a b := by rw [Set.uIoc_of_le hab.le]; exact ht
      exact h_pw_bound t ht_uIoc
    · simp only [ht_in, ↓reduceIte]
      have h_far : 2 * ε₁ / ‖L‖ < |t - t₀| := by
        simp only [Icontain, Set.mem_Icc, not_and_or, not_le] at ht_in
        rcases ht_in with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; linarith
      have ht_uIoc : t ∈ Ι a b := by rw [Set.uIoc_of_le hab.le]; exact ht
      rw [h_zero_of_far t ht_uIoc h_far, norm_zero]
  -- Step 3: Apply norm_integral_le_of_norm_le, then bound the comparison integral
  calc ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖
      ≤ ∫ t in a..b, g_comp t :=
        intervalIntegral.norm_integral_le_of_norm_le hab.le h_pw_le hg_int
    _ ≤ max 0 C * (4 * ε₁ / ‖L‖) := by
        rw [intervalIntegral.integral_of_le hab.le,
            MeasureTheory.integral_indicator measurableSet_Icc,
            MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm]
        apply mul_le_mul_of_nonneg_left _ (le_max_left 0 C)
        unfold MeasureTheory.Measure.real
        apply ENNReal.toReal_le_of_le_ofReal (by positivity)
        calc (volume.restrict (Set.Ioc a b)) Icontain
            ≤ volume Icontain := MeasureTheory.Measure.restrict_apply_le _ _
          _ = ENNReal.ofReal ((t₀ + R) - (t₀ - R)) := Real.volume_Icc
          _ = ENNReal.ofReal (4 * ε₁ / ‖L‖) := by
              simp only [R]; ring_nf

/-- **Micro-lemma (1): Norm linear approximation bound**.
    From the quadratic approximation, derive a bound on the difference between
    ‖γ t - γ t₀‖ and ‖L‖ * |t - t₀|. -/
lemma norm_linear_approx_bound {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} {K₀ δ₀ : ℝ}
    (h_quad : ∀ t, |t - t₀| < δ₀ → ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₀ * |t - t₀|^2)
    {t : ℝ} (ht : |t - t₀| < δ₀) :
    abs (‖γ t - γ t₀‖ - ‖L‖ * |t - t₀|) ≤ K₀ * |t - t₀|^2 := by
  have h1 : ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₀ * |t - t₀|^2 := h_quad t ht
  have h2 : |‖γ t - γ t₀‖ - ‖(t - t₀) • L‖| ≤ ‖γ t - γ t₀ - (t - t₀) • L‖ := abs_norm_sub_norm_le _ _
  have h3 : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ := norm_smul (t - t₀) L
  rw [h3, mul_comm] at h2
  exact le_trans h2 h1

/-- **Micro-lemma (4): Volume of a shell**. The measure of an annulus in ℝ. -/
lemma volume_shell_le {t₀ r₁ r₂ : ℝ} (hr : r₁ ≤ r₂) :
    volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ≤ ENNReal.ofReal (2 * (r₂ - r₁)) := by
  -- The set is contained in (t₀ - r₂, t₀ - r₁] ∪ [t₀ + r₁, t₀ + r₂)
  -- For t ≥ t₀: shell maps to Ioc (t₀ + r₁) (t₀ + r₂)
  -- For t < t₀: shell maps to Ico (t₀ - r₂) (t₀ - r₁)
  have h_sub : {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ⊆
      Set.Ico (t₀ - r₂) (t₀ - r₁) ∪ Set.Ioc (t₀ + r₁) (t₀ + r₂) := by
    intro t ⟨h_lower, h_upper⟩
    by_cases ht : t ≥ t₀
    · right
      have habs : |t - t₀| = t - t₀ := abs_of_nonneg (sub_nonneg.mpr ht)
      rw [habs] at h_lower h_upper
      exact ⟨by linarith, by linarith⟩
    · left
      push_neg at ht
      have habs : |t - t₀| = -(t - t₀) := abs_of_neg (sub_neg.mpr ht)
      rw [habs] at h_lower h_upper
      exact ⟨by linarith, by linarith⟩
  calc volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂}
      ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁) ∪ Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_mono h_sub
    _ ≤ volume (Set.Ico (t₀ - r₂) (t₀ - r₁)) + volume (Set.Ioc (t₀ + r₁) (t₀ + r₂)) :=
        MeasureTheory.measure_union_le _ _
    _ = ENNReal.ofReal (r₂ - r₁) + ENNReal.ofReal (r₂ - r₁) := by
        simp only [Real.volume_Ico, Real.volume_Ioc]; ring_nf
    _ = ENNReal.ofReal (2 * (r₂ - r₁)) := by
        rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf

/-- **Micro-lemma (2): Points in symmDiff are near a threshold boundary**.
    If the γ-condition (ε₂ < g ≤ ε₁) and linear-condition (ε₂ < x ≤ ε₁) disagree,
    then x must be within error e of either ε₁ or ε₂.

    Here g = ‖γ t - γ t₀‖, x = ‖L‖ * |t - t₀|, e = K₀ * |t - t₀|². -/
lemma symmDiff_subset_boundaryLayers {g x e ε₁ ε₂ : ℝ}
    (h_approx : |g - x| ≤ e)
    (h_xor : Xor' (ε₂ < g ∧ g ≤ ε₁) (ε₂ < x ∧ x ≤ ε₁)) :
    |x - ε₂| ≤ e ∨ |x - ε₁| ≤ e := by
  -- From h_xor, either (A ∧ ¬B) or (B ∧ ¬A)
  rcases h_xor with ⟨⟨hg_lower, hg_upper⟩, hnotB⟩ | ⟨⟨hx_lower, hx_upper⟩, hnotA⟩
  · -- Case: A ∧ ¬B (γ-condition holds, linear-condition fails)
    -- ¬B means: x ≤ ε₂ ∨ ε₁ < x
    by_cases hx_le_ε₂ : x ≤ ε₂
    · -- Sub-case: x ≤ ε₂ but ε₂ < g
      left
      have h1 : ε₂ - x ≤ g - x := by linarith
      have h2 : g - x ≤ |g - x| := le_abs_self _
      have hle : x - ε₂ ≤ 0 := by linarith
      calc |x - ε₂| = ε₂ - x := by rw [abs_of_nonpos hle]; ring
        _ ≤ g - x := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx
    · -- Sub-case: x > ε₂, so must have ε₁ < x (since ¬B and x > ε₂)
      push_neg at hx_le_ε₂
      have hx_gt_ε₁ : ε₁ < x := by
        by_contra h_not
        push_neg at h_not
        exact hnotB ⟨hx_le_ε₂, h_not⟩
      right
      have h1 : x - ε₁ ≤ x - g := by linarith
      have h2 : x - g ≤ |g - x| := by rw [abs_sub_comm]; exact le_abs_self _
      calc |x - ε₁| = x - ε₁ := abs_of_pos (by linarith)
        _ ≤ x - g := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx
  · -- Case: B ∧ ¬A (linear-condition holds, γ-condition fails)
    -- ¬A means: g ≤ ε₂ ∨ ε₁ < g
    by_cases hg_le_ε₂ : g ≤ ε₂
    · -- Sub-case: g ≤ ε₂ but ε₂ < x
      left
      have h1 : x - ε₂ ≤ x - g := by linarith
      have h2 : x - g ≤ |g - x| := by rw [abs_sub_comm]; exact le_abs_self _
      calc |x - ε₂| = x - ε₂ := abs_of_pos (by linarith)
        _ ≤ x - g := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx
    · -- Sub-case: g > ε₂, so must have ε₁ < g (since ¬A and g > ε₂)
      push_neg at hg_le_ε₂
      have hg_gt_ε₁ : ε₁ < g := by
        by_contra h_not
        push_neg at h_not
        exact hnotA ⟨hg_le_ε₂, h_not⟩
      right
      have h1 : ε₁ - x ≤ g - x := by linarith
      have h2 : g - x ≤ |g - x| := le_abs_self _
      have hle : x - ε₁ ≤ 0 := by linarith
      calc |x - ε₁| = ε₁ - x := by rw [abs_of_nonpos hle]; ring
        _ ≤ g - x := h1
        _ ≤ |g - x| := h2
        _ ≤ e := h_approx

/-- **Micro-lemma (3a): tAnnLin membership gives r upper bound**.
    If t ∈ tAnnLin (i.e., ‖L‖*r ≤ ε₁), then r ≤ ε₁/‖L‖. -/
lemma tAnnLin_implies_r_le {L_norm r ε₁ : ℝ} (hL_pos : 0 < L_norm)
    (h_in : L_norm * r ≤ ε₁) : r ≤ ε₁ / L_norm := by
  rw [le_div_iff₀ hL_pos, mul_comm]; exact h_in

/-- **Micro-lemma (3b): Near-threshold implies r in shell**.
    If r ≤ R_max and |x - ε| ≤ K₀*r², then r is in a shell around ε/‖L‖
    of width O(K₀*R_max²/‖L‖).

    More precisely: x ∈ [ε - K₀*R_max², ε + K₀*R_max²], so
    r ∈ [(ε - K₀*R_max²)/‖L‖, (ε + K₀*R_max²)/‖L‖]. -/
lemma near_threshold_implies_r_in_shell {L_norm r ε K₀ R_max : ℝ}
    (hL_pos : 0 < L_norm) (hK₀_nonneg : 0 ≤ K₀) (hR_max_nonneg : 0 ≤ R_max)
    (hr_le : r ≤ R_max) (hr_nonneg : 0 ≤ r)
    (h_near : |L_norm * r - ε| ≤ K₀ * r^2) :
    (ε - K₀ * R_max^2) / L_norm ≤ r ∧ r ≤ (ε + K₀ * R_max^2) / L_norm := by
  -- From h_near: ε - K₀*r² ≤ L_norm*r ≤ ε + K₀*r²
  have h_abs := abs_le.mp h_near
  have h_lower : ε - K₀ * r^2 ≤ L_norm * r := by linarith [h_abs.1]
  have h_upper : L_norm * r ≤ ε + K₀ * r^2 := by linarith [h_abs.2]
  -- Since r ≤ R_max, we have K₀*r² ≤ K₀*R_max²
  have hr2_le : r^2 ≤ R_max^2 := sq_le_sq' (by linarith) hr_le
  have hK_r2_le : K₀ * r^2 ≤ K₀ * R_max^2 := mul_le_mul_of_nonneg_left hr2_le hK₀_nonneg
  constructor
  · -- Lower bound: (ε - K₀*R_max²)/L_norm ≤ r
    rw [div_le_iff₀ hL_pos]
    have h1 : ε - K₀ * R_max^2 ≤ ε - K₀ * r^2 := by linarith
    have h2 : ε - K₀ * r^2 ≤ L_norm * r := h_lower
    have h3 : L_norm * r = r * L_norm := mul_comm _ _
    linarith
  · -- Upper bound: r ≤ (ε + K₀*R_max²)/L_norm
    rw [le_div_iff₀ hL_pos]
    have h1 : ε + K₀ * r^2 ≤ ε + K₀ * R_max^2 := by linarith
    have h2 : L_norm * r ≤ ε + K₀ * r^2 := h_upper
    have h3 : L_norm * r = r * L_norm := mul_comm _ _
    linarith

/-- **Shell volume bound (no `max`)**: volume of {t | |L_norm * |t - t₀| - ε| ≤ Δ} ≤ 4Δ/L_norm.

    Case split avoids `max` algebra:
    - Case ε ≤ Δ: shell ⊆ ball of radius (ε+Δ)/L_norm ≤ 2Δ/L_norm, volume ≤ 4Δ/L_norm
    - Case Δ < ε: shell is annulus with radii (ε±Δ)/L_norm, width = 2Δ/L_norm, volume ≤ 4Δ/L_norm -/
lemma shell_vol_le {t₀ ε Δ L_norm : ℝ} (hL_pos : 0 < L_norm) (hΔ_nonneg : 0 ≤ Δ) (hε_pos : 0 < ε) :
    volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ≤ ENNReal.ofReal (4 * Δ / L_norm) := by
  -- Shell = {t : ε - Δ ≤ L_norm * |t - t₀| ≤ ε + Δ}
  -- In t-space: (ε - Δ)/L_norm ≤ |t - t₀| ≤ (ε + Δ)/L_norm (when ε ≥ Δ)
  by_cases h : ε ≤ Δ
  · -- Case 1: ε ≤ Δ. Shell ⊆ ball of radius (ε+Δ)/L_norm ≤ 2Δ/L_norm
    have h_sub : {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ⊆ {t : ℝ | |t - t₀| ≤ (ε + Δ) / L_norm} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht ⊢
      have h_abs := abs_le.mp ht
      have h_upper : L_norm * |t - t₀| ≤ ε + Δ := by linarith [h_abs.2]
      calc |t - t₀| = (L_norm * |t - t₀|) / L_norm := by field_simp
        _ ≤ (ε + Δ) / L_norm := by apply div_le_div_of_nonneg_right h_upper hL_pos.le
    have h_ball : {t : ℝ | |t - t₀| ≤ (ε + Δ) / L_norm} = Set.Icc (t₀ - (ε + Δ) / L_norm) (t₀ + (ε + Δ) / L_norm) := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_Icc, abs_le]; constructor <;> intro ⟨h1, h2⟩ <;> constructor <;> linarith
    have h_vol : volume (Set.Icc (t₀ - (ε + Δ) / L_norm) (t₀ + (ε + Δ) / L_norm)) = ENNReal.ofReal (2 * (ε + Δ) / L_norm) := by
      rw [Real.volume_Icc]; ring_nf
    calc volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ}
        ≤ volume {t : ℝ | |t - t₀| ≤ (ε + Δ) / L_norm} := MeasureTheory.measure_mono h_sub
      _ = volume (Set.Icc (t₀ - (ε + Δ) / L_norm) (t₀ + (ε + Δ) / L_norm)) := by rw [h_ball]
      _ = ENNReal.ofReal (2 * (ε + Δ) / L_norm) := h_vol
      _ ≤ ENNReal.ofReal (4 * Δ / L_norm) := by
          apply ENNReal.ofReal_le_ofReal
          have : ε + Δ ≤ 2 * Δ := by linarith
          calc 2 * (ε + Δ) / L_norm ≤ 2 * (2 * Δ) / L_norm := by
                apply div_le_div_of_nonneg_right _ hL_pos.le; linarith
            _ = 4 * Δ / L_norm := by ring
  · -- Case 2: Δ < ε. Shell is a proper annulus with inner (ε-Δ)/L_norm, outer (ε+Δ)/L_norm
    push_neg at h
    let r₁ := (ε - Δ) / L_norm
    let r₂ := (ε + Δ) / L_norm
    have hr₁_pos : 0 < r₁ := by simp only [r₁]; apply div_pos; linarith; exact hL_pos
    have hr₁_le_r₂ : r₁ ≤ r₂ := by simp only [r₁, r₂]; apply div_le_div_of_nonneg_right _ hL_pos.le; linarith
    -- Shell ⊆ {r₁ ≤ |t - t₀| ≤ r₂}
    have h_sub : {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ} ⊆ {t : ℝ | r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} := by
      intro t ht
      simp only [Set.mem_setOf_eq] at ht
      have h_abs := abs_le.mp ht
      simp only [r₁, r₂, Set.mem_setOf_eq]
      constructor
      · calc (ε - Δ) / L_norm ≤ (L_norm * |t - t₀|) / L_norm := by
              apply div_le_div_of_nonneg_right _ hL_pos.le; linarith [h_abs.1]
          _ = |t - t₀| := by field_simp
      · calc |t - t₀| = (L_norm * |t - t₀|) / L_norm := by field_simp
          _ ≤ (ε + Δ) / L_norm := by apply div_le_div_of_nonneg_right _ hL_pos.le; linarith [h_abs.2]
    -- {r₁ ≤ |t - t₀| ≤ r₂} differs from {r₁ < |t - t₀| ≤ r₂} by measure 0
    have h_sub_strict : {t : ℝ | r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} ⊆
        {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ∪ {t : ℝ | |t - t₀| = r₁} := by
      intro t ⟨h1, h2⟩
      by_cases heq : |t - t₀| = r₁
      · right; exact heq
      · left; exact ⟨lt_of_le_of_ne h1 (Ne.symm heq), h2⟩
    have h_singleton_null : volume {t : ℝ | |t - t₀| = r₁} = 0 := by
      have h_sub : {t : ℝ | |t - t₀| = r₁} ⊆ {t₀ - r₁, t₀ + r₁} := by
        intro t ht; simp only [Set.mem_setOf_eq] at ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        rcases (abs_eq hr₁_pos.le).mp ht with h1 | h1
        · right; linarith  -- t - t₀ = r₁ implies t = t₀ + r₁
        · left; linarith   -- t - t₀ = -r₁ implies t = t₀ - r₁
      have h_finite : (({t₀ - r₁, t₀ + r₁} : Set ℝ)).Finite := Set.toFinite _
      have h_pair_null : volume ({t₀ - r₁, t₀ + r₁} : Set ℝ) = 0 := h_finite.measure_zero volume
      have h_le : volume {t : ℝ | |t - t₀| = r₁} ≤ volume ({t₀ - r₁, t₀ + r₁} : Set ℝ) :=
        MeasureTheory.measure_mono h_sub
      simp only [h_pair_null, nonpos_iff_eq_zero] at h_le
      exact h_le
    -- Width = r₂ - r₁ = 2Δ/L_norm
    have h_width : r₂ - r₁ = 2 * Δ / L_norm := by simp only [r₁, r₂]; field_simp; ring
    calc volume {t : ℝ | |L_norm * |t - t₀| - ε| ≤ Δ}
        ≤ volume {t : ℝ | r₁ ≤ |t - t₀| ∧ |t - t₀| ≤ r₂} := MeasureTheory.measure_mono h_sub
      _ ≤ volume ({t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} ∪ {t : ℝ | |t - t₀| = r₁}) :=
          MeasureTheory.measure_mono h_sub_strict
      _ ≤ volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} + volume {t : ℝ | |t - t₀| = r₁} :=
          MeasureTheory.measure_union_le _ _
      _ = volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} + 0 := by rw [h_singleton_null]
      _ = volume {t : ℝ | r₁ < |t - t₀| ∧ |t - t₀| ≤ r₂} := by ring
      _ ≤ ENNReal.ofReal (2 * (r₂ - r₁)) := volume_shell_le hr₁_le_r₂
      _ = ENNReal.ofReal (2 * (2 * Δ / L_norm)) := by rw [h_width]
      _ = ENNReal.ofReal (4 * Δ / L_norm) := by ring_nf

/-- **Thin-shell symmetric difference bound**. The symmetric difference between
    the γ-annulus and the tight linear-model t-annulus has measure O(ε₁²/‖L‖³).

    **Localized version (Option A):** Sets are restricted to:
    - `[a,b]` (bounded domain)
    - `|t - t₀| < δ₀` (C² zone where quadratic approximation holds)

    This eliminates far-field issues entirely by definition.

    **Key insight:** Use tight linear-model annulus with local zone restriction:
      `tAnnLin := {t | t ∈ [a,b] ∧ |t-t₀| < δ₀ ∧ ε₂ < ‖L‖*|t-t₀| ∧ ‖L‖*|t-t₀| ≤ ε₁}`
    When K₀=0 (exactly linear), γAnn = tAnnLin and symmDiff has measure 0.

    **Proof via micro-lemmas:**
    1. `norm_linear_approx_bound`: |‖γ‖ - ‖L‖|t|| ≤ K₀|t|²
    2. If t ∈ symmDiff, then |‖L‖*|t| - ε| ≤ K₀|t|² for ε ∈ {ε₁, ε₂}
    3. This confines t to thin shells of width O(ε²/‖L‖²) around |t| = ε/‖L‖
    4. `volume_shell_le`: measure of shell ≤ 2*(width) -/
lemma annulus_symmDiff_measure_bound {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hab : a < b) (ht₀ : t₀ ∈ Set.Ioo a b)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0) :
    ∃ K > 0, ∃ δ₀' > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ < δ →
      -- Option A: Sets include |t - t₀| < δ₀' to eliminate far-field issues
      let γAnn := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
      let tAnnLin := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧ ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁}
      volume (symmDiff γAnn tAnnLin) ≤ ENNReal.ofReal (K * ε₁^2 / ‖L‖^3) := by
  -- Get quadratic approximation bound from C²
  obtain ⟨K₀, δ₀, hδ₀_pos, hK₀_pos, h_quad⟩ := quadratic_approx_of_contDiffAt_two hγ_C2 hγ_deriv
  -- Distance from t₀ to boundary of [a,b]
  have ht₀_dist_pos : 0 < min (t₀ - a) (b - t₀) := by
    simp only [lt_min_iff, Set.mem_Ioo] at ht₀ ⊢; constructor <;> linarith
  have hL_norm_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  -- δ-shrinking: use ‖L‖/(4*K₀) to ensure K₀|t-t₀| ≤ ‖L‖/4 in local zone
  -- This guarantees ‖L‖ - K₀|t-t₀| ≥ 3‖L‖/4 > ‖L‖/2, eliminating quadratic case
  let δ₁ := min δ₀ (‖L‖ / (4 * K₀))
  have hδ₁_pos : 0 < δ₁ := lt_min hδ₀_pos (div_pos hL_norm_pos (by linarith))
  have hδ₁_le_δ₀ : δ₁ ≤ δ₀ := min_le_left _ _
  have hδ₁_le_L_over_4K : δ₁ ≤ ‖L‖ / (4 * K₀) := min_le_right _ _
  -- Derive 2K bound from 4K bound (since 4K₀ > 2K₀)
  have hδ₁_le_L_over_2K : δ₁ ≤ ‖L‖ / (2 * K₀) := by
    calc δ₁ ≤ ‖L‖ / (4 * K₀) := hδ₁_le_L_over_4K
      _ ≤ ‖L‖ / (2 * K₀) := by apply div_le_div_of_nonneg_left (le_of_lt hL_norm_pos) (by linarith)
                               linarith
  -- Q2 micro-lemma: quad_small_zone
  have h_quad_small : ∀ r, r < δ₁ → K₀ * r ≤ ‖L‖ / 4 := by
    intro r hr
    calc K₀ * r ≤ K₀ * δ₁ := mul_le_mul_of_nonneg_left (le_of_lt hr) (le_of_lt hK₀_pos)
      _ ≤ K₀ * (‖L‖ / (4 * K₀)) := mul_le_mul_of_nonneg_left hδ₁_le_L_over_4K (le_of_lt hK₀_pos)
      _ = ‖L‖ / 4 := by field_simp
  -- Use δ = ‖L‖ * δ₁ / 2
  let δ := ‖L‖ * δ₁ / 2
  have hδ_pos : 0 < δ := by simp only [δ]; positivity
  -- Use K = 32*K₀ to absorb shell volume factors
  -- Output δ₁ (not δ₀) as δ₀' so that set membership gives |t - t₀| < δ₁ directly
  -- This makes h_localize_γAnn trivial and C² still applies since δ₁ ≤ δ₀
  use 32 * K₀, by linarith, δ₁, hδ₁_pos, δ, hδ_pos
  intro ε₁ ε₂ hε₂_pos hε₂_le hε₁_lt γAnn tAnnLin
  have hε₁_pos : 0 < ε₁ := lt_of_lt_of_le hε₂_pos hε₂_le
  have hK₀_nonneg : 0 ≤ K₀ := le_of_lt hK₀_pos
  -- Extract bound from ε₁ < δ = ‖L‖ * δ₁ / 2
  have hε₁_lt_half : ε₁ < ‖L‖ * δ₁ / 2 := hε₁_lt
  -- Key bound: ε₁/‖L‖ < δ₁/2 < δ₁ ≤ δ₀
  have hε₁_over_L_lt_δ₁ : ε₁ / ‖L‖ < δ₁ := by
    have h1 : ε₁ < ‖L‖ * δ₁ / 2 := hε₁_lt_half
    calc ε₁ / ‖L‖ < (‖L‖ * δ₁ / 2) / ‖L‖ := by apply div_lt_div_of_pos_right h1 hL_norm_pos
      _ = δ₁ / 2 := by field_simp
      _ < δ₁ := by linarith [hδ₁_pos]
  have hε₁_over_L_lt_δ₀ : ε₁ / ‖L‖ < δ₀ :=
    lt_of_lt_of_le hε₁_over_L_lt_δ₁ hδ₁_le_δ₀
  -- Also: 2*ε₁/‖L‖ < δ₁ ≤ δ₀
  have h2ε₁_over_L_lt_δ₁ : 2 * ε₁ / ‖L‖ < δ₁ := by
    have h1 : ε₁ < ‖L‖ * δ₁ / 2 := hε₁_lt_half
    have h2 : 2 * ε₁ < ‖L‖ * δ₁ := by linarith
    have h3 : 2 * ε₁ / ‖L‖ < ‖L‖ * δ₁ / ‖L‖ := div_lt_div_of_pos_right h2 hL_norm_pos
    have h4 : ‖L‖ * δ₁ / ‖L‖ = δ₁ := by field_simp
    linarith
  have h2ε₁_over_L_lt_δ₀ : 2 * ε₁ / ‖L‖ < δ₀ :=
    lt_of_lt_of_le h2ε₁_over_L_lt_δ₁ hδ₁_le_δ₀
  -- Lower bound lemma: for |t - t₀| < δ₁, we have ‖γ t - γ t₀‖ ≥ ‖L‖|t-t₀|/2
  have h_lower_bound : ∀ t, |t - t₀| < δ₁ → ‖γ t - γ t₀‖ ≥ ‖L‖ / 2 * |t - t₀| := by
    intro t ht_lt
    have ht_lt_δ₀ : |t - t₀| < δ₀ := lt_of_lt_of_le ht_lt hδ₁_le_δ₀
    have ht_lt_L_over_2K : |t - t₀| < ‖L‖ / (2 * K₀) := lt_of_lt_of_le ht_lt hδ₁_le_L_over_2K
    have h_approx := h_quad t ht_lt_δ₀
    -- ‖γ t - γ t₀ - (t - t₀) • L‖ ≤ K₀ * |t - t₀|²
    -- By reverse triangle: ‖γ t - γ t₀‖ ≥ ‖(t - t₀) • L‖ - K₀ * |t - t₀|²
    have h_smul_norm : ‖(t - t₀) • L‖ = |t - t₀| * ‖L‖ := norm_smul (t - t₀) L
    have h_rev_tri := norm_sub_norm_le (γ t - γ t₀) ((t - t₀) • L)
    have h1 : ‖γ t - γ t₀‖ ≥ ‖(t - t₀) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := by
      have := abs_norm_sub_norm_le (γ t - γ t₀) ((t - t₀) • L)
      linarith [abs_le.mp this]
    have h2 : ‖γ t - γ t₀‖ ≥ |t - t₀| * ‖L‖ - K₀ * |t - t₀|^2 := by
      calc ‖γ t - γ t₀‖ ≥ ‖(t - t₀) • L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := h1
        _ = |t - t₀| * ‖L‖ - ‖γ t - γ t₀ - (t - t₀) • L‖ := by rw [h_smul_norm]
        _ ≥ |t - t₀| * ‖L‖ - K₀ * |t - t₀|^2 := by linarith [h_approx]
    -- Factor: |t-t₀| * (‖L‖ - K₀*|t-t₀|)
    have h3 : |t - t₀| * ‖L‖ - K₀ * |t - t₀|^2 = |t - t₀| * (‖L‖ - K₀ * |t - t₀|) := by ring
    rw [h3] at h2
    -- Since |t - t₀| < ‖L‖/(2K₀), we have K₀*|t-t₀| < ‖L‖/2, so ‖L‖ - K₀*|t-t₀| > ‖L‖/2
    have h4 : K₀ * |t - t₀| < ‖L‖ / 2 := by
      have h4a : |t - t₀| < ‖L‖ / (2 * K₀) := ht_lt_L_over_2K
      have h4b : K₀ * |t - t₀| < K₀ * (‖L‖ / (2 * K₀)) := mul_lt_mul_of_pos_left h4a hK₀_pos
      have h4c : K₀ * (‖L‖ / (2 * K₀)) = ‖L‖ / 2 := by field_simp
      linarith
    have h5 : ‖L‖ - K₀ * |t - t₀| > ‖L‖ / 2 := by linarith
    have h6 : |t - t₀| * (‖L‖ - K₀ * |t - t₀|) ≥ |t - t₀| * (‖L‖ / 2) := by
      apply mul_le_mul_of_nonneg_left (le_of_lt h5) (abs_nonneg _)
    calc ‖γ t - γ t₀‖ ≥ |t - t₀| * (‖L‖ - K₀ * |t - t₀|) := h2
      _ ≥ |t - t₀| * (‖L‖ / 2) := h6
      _ = ‖L‖ / 2 * |t - t₀| := by ring
  -- Localization: any t ∈ γAnn has |t - t₀| < δ₁ directly from set membership
  -- (We now output δ₁ as the local zone δ₀', so this is immediate from the set definition)
  have h_localize_γAnn : ∀ t, t ∈ γAnn → |t - t₀| < δ₁ := by
    intro t ⟨_, ht_local, _, _⟩
    -- ht_local : |t - t₀| < δ₁ (from Option A - baked into set definition, using δ₁ as output)
    exact ht_local
  -- Localization for tAnnLin: same as γAnn, extract directly from set membership
  have h_localize_tAnnLin : ∀ t, t ∈ tAnnLin → |t - t₀| < δ₁ := by
    intro t ⟨_, ht_local, _, _⟩
    -- ht_local : |t - t₀| < δ₁ (from Option A)
    exact ht_local
  -- Key constants: R_max = 2ε₁/‖L‖ covers both tAnnLin (|t-t₀| ≤ ε₁/‖L‖) and γAnn (|t-t₀| ≤ 2ε₁/‖L‖)
  let R_max := 2 * ε₁ / ‖L‖  -- max radius for points in symmDiff
  let Δ := K₀ * R_max^2  -- error bound (constant)
  have hR_max_pos : 0 < R_max := by simp only [R_max]; positivity
  have hΔ_nonneg : 0 ≤ Δ := mul_nonneg hK₀_nonneg (sq_nonneg _)
  -- Shell bounds around ε₁ and ε₂
  let shell₁_lo := (ε₁ - Δ) / ‖L‖
  let shell₁_hi := (ε₁ + Δ) / ‖L‖
  let shell₂_lo := (ε₂ - Δ) / ‖L‖
  let shell₂_hi := (ε₂ + Δ) / ‖L‖
  -- Define helper functions
  let g : ℝ → ℝ := fun t => ‖γ t - γ t₀‖
  let x : ℝ → ℝ := fun t => ‖L‖ * |t - t₀|
  let e : ℝ → ℝ := fun t => K₀ * |t - t₀|^2
  -- Define shells as intervals
  let shell₁ := {t : ℝ | |x t - ε₁| ≤ Δ}
  let shell₂ := {t : ℝ | |x t - ε₂| ≤ Δ}
  -- (5.1) Pointwise→set: symmDiff ⊆ shell₁ ∪ shell₂
  have h_subset : symmDiff γAnn tAnnLin ⊆ shell₁ ∪ shell₂ := by
    intro t ht
    rw [Set.mem_symmDiff] at ht
    have hxor : Xor' (t ∈ γAnn) (t ∈ tAnnLin) := ht
    -- Key: t must be in one of the two sets, hence localized
    have ht_localized : |t - t₀| < δ₁ := by
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · exact h_localize_γAnn t ht_γAnn
      · exact h_localize_tAnnLin t ht_tAnn
    have ht_lt_δ₀ : |t - t₀| < δ₀ := lt_of_lt_of_le ht_localized (min_le_left _ _)
    -- Apply quadratic approximation bound
    have h_approx := h_quad t ht_lt_δ₀
    -- Get |g t - x t| ≤ e t from norm_linear_approx_bound
    have h_gx_bound : |g t - x t| ≤ e t := by
      have := norm_linear_approx_bound h_quad ht_lt_δ₀
      -- norm_linear_approx_bound gives: abs (‖γ t - γ t₀‖ - ‖L‖ * |t - t₀|) ≤ K₀ * |t - t₀|^2
      -- which is exactly |g t - x t| ≤ e t
      convert this using 2 <;> simp only [g, x, e]
    -- Apply symmDiff_subset_boundaryLayers
    -- Extract t ∈ Icc a b and local bound from whichever set t belongs to
    -- (Note: sets now have 4 components: Icc, local, lower, upper)
    have ht_Icc : t ∈ Set.Icc a b := by
      rcases hxor with ⟨⟨ht_Icc, _, _, _⟩, _⟩ | ⟨⟨ht_Icc, _, _, _⟩, _⟩ <;> exact ht_Icc
    -- Extract annulus conditions from Xor
    have hxor' : Xor' (ε₂ < g t ∧ g t ≤ ε₁) (ε₂ < x t ∧ x t ≤ ε₁) := by
      rcases hxor with ⟨⟨_, _, hγ_lo, hγ_hi⟩, ht_not_tAnn⟩ | ⟨⟨_, _, ht_lo, ht_hi⟩, ht_not_γAnn⟩
      · left; constructor
        · exact ⟨hγ_lo, hγ_hi⟩
        · intro ⟨ht_lo', ht_hi'⟩; exact ht_not_tAnn ⟨ht_Icc, ht_localized, ht_lo', ht_hi'⟩
      · right; constructor
        · exact ⟨ht_lo, ht_hi⟩
        · intro ⟨hγ_lo', hγ_hi'⟩; exact ht_not_γAnn ⟨ht_Icc, ht_localized, hγ_lo', hγ_hi'⟩
    have h_near := symmDiff_subset_boundaryLayers h_gx_bound hxor'
    -- h_near: |x t - ε₂| ≤ e t ∨ |x t - ε₁| ≤ e t
    -- Need to show: |x t - ε₂| ≤ Δ ∨ |x t - ε₁| ≤ Δ
    -- Since |t - t₀| ≤ R_max (for points in symmDiff), we have e t ≤ Δ
    have hR_bound : |t - t₀| ≤ R_max := by
      -- R_max = 2ε₁/‖L‖ covers both cases
      rcases hxor with ⟨ht_γAnn, _⟩ | ⟨ht_tAnn, _⟩
      · -- t ∈ γAnn: by lower bound, |t - t₀| ≤ 2ε₁/‖L‖ = R_max
        have h_lb := h_lower_bound t ht_localized
        have ⟨_, _, _, ht_upper⟩ := ht_γAnn  -- 4-component: Icc, local, lower, upper
        have h1 : ‖L‖ / 2 * |t - t₀| ≤ ε₁ := le_trans h_lb ht_upper
        have h1' : |t - t₀| * (‖L‖ / 2) ≤ ε₁ := by rw [mul_comm]; exact h1
        have hL2_pos : 0 < ‖L‖ / 2 := by linarith
        have h2 : |t - t₀| ≤ ε₁ / (‖L‖ / 2) := by rw [le_div_iff₀ hL2_pos]; exact h1'
        have h3 : ε₁ / (‖L‖ / 2) = 2 * ε₁ / ‖L‖ := by field_simp
        simp only [R_max, h3] at h2 ⊢; exact h2
      · -- t ∈ tAnnLin: |t - t₀| ≤ ε₁/‖L‖ ≤ R_max = 2ε₁/‖L‖
        have ⟨_, _, _, ht_upper⟩ := ht_tAnn  -- 4-component: Icc, local, lower, upper
        have h1 : ‖L‖ * |t - t₀| ≤ ε₁ := ht_upper
        have h1' : |t - t₀| * ‖L‖ ≤ ε₁ := by rw [mul_comm]; exact h1
        have hL_nonneg : 0 ≤ ‖L‖ := le_of_lt hL_norm_pos
        calc |t - t₀| ≤ ε₁ / ‖L‖ := by rw [le_div_iff₀ hL_norm_pos]; exact h1'
          _ ≤ 2 * ε₁ / ‖L‖ := by apply div_le_div_of_nonneg_right _ hL_nonneg; linarith
    have he_le_Δ : e t ≤ Δ := by
      simp only [e, Δ, R_max]
      apply mul_le_mul_of_nonneg_left _ hK₀_nonneg
      exact sq_le_sq' (by linarith [abs_nonneg (t - t₀)]) hR_bound
    rcases h_near with h_near₂ | h_near₁
    · -- h_near₂ : |x t - ε₂| ≤ e t, so t ∈ shell₂
      right
      show |x t - ε₂| ≤ Δ
      exact le_trans h_near₂ he_le_Δ
    · -- h_near₁ : |x t - ε₁| ≤ e t, so t ∈ shell₁
      left
      show |x t - ε₁| ≤ Δ
      exact le_trans h_near₁ he_le_Δ
  -- (5.2) Shell width bound
  have h_shell_width : shell₁_hi - shell₁_lo = 2 * Δ / ‖L‖ := by
    simp only [shell₁_lo, shell₁_hi]; field_simp; ring
  -- (5.3) Measure bound
  have h_meas_subset : volume (symmDiff γAnn tAnnLin) ≤ volume (shell₁ ∪ shell₂) :=
    MeasureTheory.measure_mono h_subset
  -- Each shell is an annulus in t-space with width O(Δ/‖L‖)
  -- shell₁ = {t | |x t - ε₁| ≤ Δ} ⊆ {t | |t - t₀| ≤ (ε₁ + Δ)/‖L‖}
  -- volume(shell) ≤ 4Δ/‖L‖ (factor of 2 for ± sides of t₀, factor 2 for width)

  -- Bound volume of each shell using ANNULUS structure
  -- Key insight: shell = {t | |x t - ε| ≤ Δ} where x t = ‖L‖|t - t₀|
  -- This is an annulus with inner radius r₁ = max(0, (ε - Δ)/‖L‖), outer r₂ = (ε + Δ)/‖L‖
  -- Width = r₂ - r₁ ≤ 2Δ/‖L‖ always. Measure = 2*(width) ≤ 4Δ/‖L‖
  have h_shell₁_vol : volume shell₁ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) := by
    -- shell₁ = {t | |‖L‖ * |t - t₀| - ε₁| ≤ Δ}, apply shell_vol_le
    have h_eq : shell₁ = {t : ℝ | |‖L‖ * |t - t₀| - ε₁| ≤ Δ} := by
      simp only [shell₁, x]
    rw [h_eq]
    exact shell_vol_le hL_norm_pos hΔ_nonneg hε₁_pos

  -- Shell₂ has the same bound (same width 2Δ/‖L‖)
  have h_shell₂_vol : volume shell₂ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) := by
    -- shell₂ = {t | |‖L‖ * |t - t₀| - ε₂| ≤ Δ}, apply shell_vol_le
    have h_eq : shell₂ = {t : ℝ | |‖L‖ * |t - t₀| - ε₂| ≤ Δ} := by
      simp only [shell₂, x]
    rw [h_eq]
    exact shell_vol_le hL_norm_pos hΔ_nonneg hε₂_pos

  -- Total bound: volume(shell₁ ∪ shell₂) ≤ 8Δ/‖L‖
  have h_total_vol : volume (shell₁ ∪ shell₂) ≤ ENNReal.ofReal (8 * Δ / ‖L‖) := by
    calc volume (shell₁ ∪ shell₂)
        ≤ volume shell₁ + volume shell₂ := MeasureTheory.measure_union_le _ _
      _ ≤ ENNReal.ofReal (4 * Δ / ‖L‖) + ENNReal.ofReal (4 * Δ / ‖L‖) := add_le_add h_shell₁_vol h_shell₂_vol
      _ = ENNReal.ofReal (4 * Δ / ‖L‖ + 4 * Δ / ‖L‖) := by
          rw [← ENNReal.ofReal_add] <;> positivity
      _ = ENNReal.ofReal (8 * Δ / ‖L‖) := by ring_nf

  -- Now Δ = K₀ * R_max² = K₀ * (2ε₁/‖L‖)² = 4*K₀*ε₁²/‖L‖²
  -- So 8*Δ/‖L‖ = 8 * 4*K₀*ε₁²/‖L‖² / ‖L‖ = 32*K₀*ε₁²/‖L‖³
  have hΔ_eq : Δ = 4 * K₀ * ε₁^2 / ‖L‖^2 := by
    simp only [Δ, R_max]
    field_simp
    ring
  have h_bound_eq : 8 * Δ / ‖L‖ = 32 * K₀ * ε₁^2 / ‖L‖^3 := by
    rw [hΔ_eq]
    field_simp
    ring

  calc volume (symmDiff γAnn tAnnLin)
      ≤ volume (shell₁ ∪ shell₂) := h_meas_subset
    _ ≤ ENNReal.ofReal (8 * Δ / ‖L‖) := h_total_vol
    _ = ENNReal.ofReal (32 * K₀ * ε₁^2 / ‖L‖^3) := by rw [h_bound_eq]

/-! ### S1–S5: Micro-lemma chain for singular annulus bound

These lemmas build up to `singular_annulus_bound_explicit`, which has the correct
quantifier order: `∃ Csing > 0, ∃ δ > 0, ∀ ε₁ ε₂, ... → bound ≤ Csing * ε₁`.
This ensures Csing is ε-independent. -/

/-- **S1**: The linear-model annulus lies inside [a,b] when ε₁ is small enough.
    Precondition for symmetric cancellation in S2. -/
lemma singular_tAnnLin_inside_interval {t₀ a b : ℝ} (hat₀ : t₀ ∈ Set.Ioo a b)
    {L : ℂ} (hL_pos : 0 < ‖L‖) {ε₁ : ℝ}
    (hε₁_small : ε₁ < ‖L‖ * min (t₀ - a) (b - t₀))
    {t : ℝ} (ht_bound : ‖L‖ * |t - t₀| ≤ ε₁) :
    t ∈ Set.Icc a b := by
  have ht₀_mem := Set.mem_Ioo.mp hat₀
  have h_abs_lt : |t - t₀| < min (t₀ - a) (b - t₀) := by
    have h1 : ‖L‖ * |t - t₀| < ‖L‖ * min (t₀ - a) (b - t₀) :=
      lt_of_le_of_lt ht_bound hε₁_small
    exact lt_of_mul_lt_mul_left h1 (le_of_lt hL_pos)
  have h_lo : t₀ - a ≤ t₀ - a := le_refl _
  have h_hi : b - t₀ ≤ b - t₀ := le_refl _
  have h1 : |t - t₀| < t₀ - a := lt_of_lt_of_le h_abs_lt (min_le_left _ _)
  have h2 : |t - t₀| < b - t₀ := lt_of_lt_of_le h_abs_lt (min_le_right _ _)
  rw [abs_lt] at h1 h2
  exact Set.mem_Icc.mpr ⟨by linarith [h1.1], by linarith [h2.2]⟩

/-- **S2**: Integral of `(t-t₀)⁻¹` over the symmetric linear annulus is 0.
    Uses `integral_inv_symm` after converting indicator to interval integrals. -/
lemma singular_tAnnLin_cancel (t₀ : ℝ) {L : ℂ} (hL_pos : 0 < ‖L‖)
    (ε₁ ε₂ : ℝ) (hε₂_pos : 0 < ε₂) (hε₂_le : ε₂ ≤ ε₁) :
    let c₁ := ε₂ / ‖L‖
    let c₂ := ε₁ / ‖L‖
    (∫ t in (t₀ - c₂)..(t₀ - c₁), (↑(t - t₀) : ℂ)⁻¹) +
    (∫ t in (t₀ + c₁)..(t₀ + c₂), (↑(t - t₀) : ℂ)⁻¹) = 0 := by
  intro c₁ c₂
  exact integral_inv_symm t₀ c₁ c₂ (div_pos hε₂_pos hL_pos) (div_pos (lt_of_lt_of_le hε₂_pos hε₂_le) hL_pos)
    (div_le_div_of_nonneg_right hε₂_le (le_of_lt hL_pos))

/-- **S3**: Pointwise sup bound for `‖(↑(t-t₀) : ℂ)⁻¹‖` given a lower bound on `|t-t₀|`.
    If `c ≤ |t - t₀|`, then `‖(↑(t-t₀))⁻¹‖ ≤ 1/c`. -/
lemma singular_symmDiff_sup_bound {t₀ c : ℝ} (hc_pos : 0 < c)
    {t : ℝ} (ht_lower : c ≤ |t - t₀|) :
    ‖(↑(t - t₀) : ℂ)⁻¹‖ ≤ 1 / c := by
  have ht_pos : (0 : ℝ) < |t - t₀| := lt_of_lt_of_le hc_pos ht_lower
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, one_div]
  exact inv_anti₀ hc_pos ht_lower

/-- **S5**: Singular annulus bound with ε-independent constant.
    Correct quantifier order: `∃ Csing > 0, ∃ δ > 0, ∀ ε₁ ε₂, ... → bound`.
    This ensures Csing depends only on C² data (γ, t₀, L), NOT on ε.

    Strategy: tAnnLin integral = 0 (S2), so γAnn integral ≤ symmDiff integral
    ≤ sup × vol(symmDiff) = O(‖L‖/ε₁) × O(ε₁²/‖L‖³) = O(ε₁/‖L‖²). -/
lemma singular_annulus_bound_explicit {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hab : a < b) (hat₀ : t₀ ∈ Set.Ioo a b)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0)
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ Csing > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ ≤ 2 * ε₂ → ε₁ < δ →
      ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then (↑(t - t₀) : ℂ)⁻¹ else 0‖ ≤ Csing * ε₁ := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  -- Step 1: Get measure bound from annulus_symmDiff_measure_bound
  -- Outputs: Kmeas, δ₀' (local zone radius), δ_meas (ε threshold)
  obtain ⟨Kmeas, hKmeas_pos, δ₀', hδ₀'_pos, δ_meas, hδ_meas_pos, h_meas⟩ :=
    annulus_symmDiff_measure_bound hab hat₀ hγ_C2 hγ_deriv hL
  -- Step 2: Get lower bound from HasDerivAt
  have hγ_diff : DifferentiableAt ℝ γ t₀ := hγ_C2.differentiableAt one_le_two
  have hγ_hasderiv : HasDerivAt γ L t₀ := by rw [← hγ_deriv]; exact hγ_diff.hasDerivAt
  obtain ⟨δ_lo, hδ_lo_pos, h_lower⟩ := gamma_lower_bound_of_hasDerivAt hL hγ_hasderiv
  obtain ⟨δ_up, hδ_up_pos, h_upper⟩ := gamma_upper_bound_of_hasDerivAt hL hγ_hasderiv
  -- Step 3: Get no-return localization from injectivity + continuity
  -- With c = min(δ₀', δ_lo, δ_up), ensures localization gives all bounds
  let δ₁ := min δ₀' (min δ_lo δ_up)
  have hδ₁_pos : 0 < δ₁ := lt_min hδ₀'_pos (lt_min hδ_lo_pos hδ_up_pos)
  obtain ⟨ρ, hρ_pos, h_far_bound⟩ := no_return_of_inj_continuous hδ₁_pos hγ_cont h_inj
  -- Step 4: Compute distance from t₀ to boundary of [a,b]
  have ht₀_mem := Set.mem_Ioo.mp hat₀
  have h_dist_pos : 0 < min (t₀ - a) (b - t₀) := by
    simp only [lt_min_iff]; constructor <;> linarith
  -- Step 5: Define δ = min(δ_meas, ρ, ‖L‖ * min(t₀-a, b-t₀), ‖L‖ * δ₀')
  -- This ensures: (a) measure bound applies, (b) localization holds,
  -- (c) tAnnLin ⊂ [a,b], (d) lower bound applies, (e) ε₁ < ‖L‖ * δ₀'
  let δ := min (min δ_meas ρ) (min (‖L‖ * min (t₀ - a) (b - t₀)) (‖L‖ * δ₀'))
  have hδ_pos : 0 < δ := lt_min (lt_min hδ_meas_pos hρ_pos)
    (lt_min (mul_pos hL_pos h_dist_pos) (mul_pos hL_pos hδ₀'_pos))
  -- Step 6: Define Csing = 4*Kmeas/‖L‖² (ε-independent!)
  let Csing := 4 * Kmeas / ‖L‖^2
  have hCsing_pos : 0 < Csing := by positivity
  use Csing, hCsing_pos, δ, hδ_pos
  -- Step 7: Prove for all ε₁, ε₂
  intro ε₁ ε₂ hε₂_pos hε₂_le h_ratio hε₁_lt
  have hε₁_pos : 0 < ε₁ := lt_of_lt_of_le hε₂_pos hε₂_le
  -- Extract key consequences from ε₁ < δ
  have hε₁_lt_δ_meas : ε₁ < δ_meas := calc ε₁ < δ := hε₁_lt
    _ ≤ min δ_meas ρ := min_le_left _ _
    _ ≤ δ_meas := min_le_left _ _
  have hε₁_lt_ρ : ε₁ < ρ := calc ε₁ < δ := hε₁_lt
    _ ≤ min δ_meas ρ := min_le_left _ _
    _ ≤ ρ := min_le_right _ _
  have hε₁_lt_Ldist : ε₁ < ‖L‖ * min (t₀ - a) (b - t₀) := calc ε₁ < δ := hε₁_lt
    _ ≤ min (‖L‖ * min (t₀ - a) (b - t₀)) (‖L‖ * δ₀') := min_le_right _ _
    _ ≤ ‖L‖ * min (t₀ - a) (b - t₀) := min_le_left _ _
  have hε₁_lt_Lδ₀' : ε₁ < ‖L‖ * δ₀' := calc ε₁ < δ := hε₁_lt
    _ ≤ min (‖L‖ * min (t₀ - a) (b - t₀)) (‖L‖ * δ₀') := min_le_right _ _
    _ ≤ ‖L‖ * δ₀' := min_le_right _ _
  -- Step 8: Localization — if t ∈ [a,b] and ‖γ t - γ t₀‖ ≤ ε₁ then |t - t₀| < δ₁
  -- This gives |t-t₀| < δ₀' (for measure bound), < δ_lo (for lower bound), < δ_up (for upper bound)
  have h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < δ₁ := by
    intro t ht hγt
    by_contra h_not_lt
    push_neg at h_not_lt
    have h_far := h_far_bound t ht h_not_lt
    linarith
  -- Step 9: Define the tAnnLin indicator integral (symmetric around t₀)
  let J_lin := ∫ t in a..b, if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0
  -- Step 10: tAnnLin integral = 0 by symmetric cancellation (S2)
  have hJ_lin_zero : J_lin = 0 := by
    -- Set up constants c₁ = ε₂/‖L‖, c₂ = ε₁/‖L‖
    set c₁ := ε₂ / ‖L‖ with hc₁_def
    set c₂ := ε₁ / ‖L‖ with hc₂_def
    have hc₁_pos : 0 < c₁ := div_pos hε₂_pos hL_pos
    have hc₂_pos : 0 < c₂ := div_pos hε₁_pos hL_pos
    have hc₁_le_c₂ : c₁ ≤ c₂ := div_le_div_of_nonneg_right hε₂_le (le_of_lt hL_pos)
    -- Key ordering: a < t₀ - c₂ ≤ t₀ - c₁ < t₀ < t₀ + c₁ ≤ t₀ + c₂ < b
    have hc₂_lt_dist : c₂ < min (t₀ - a) (b - t₀) := by
      rw [hc₂_def, div_lt_iff₀ hL_pos]
      linarith [mul_comm ‖L‖ (min (t₀ - a) (b - t₀))]
    have ha_lt_mc₂ : a < t₀ - c₂ := by linarith [lt_of_lt_of_le hc₂_lt_dist (min_le_left _ _)]
    have hmc₂_le_mc₁ : t₀ - c₂ ≤ t₀ - c₁ := by linarith [hc₁_le_c₂]
    have hmc₁_le_pc₁ : t₀ - c₁ ≤ t₀ + c₁ := by linarith [hc₁_pos]
    have hpc₁_le_pc₂ : t₀ + c₁ ≤ t₀ + c₂ := by linarith [hc₁_le_c₂]
    have hpc₂_lt_b : t₀ + c₂ < b := by linarith [lt_of_lt_of_le hc₂_lt_dist (min_le_right _ _)]
    -- The condition is equivalent to c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂
    have h_cond_iff : ∀ t : ℝ,
        (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) ↔ (c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) := by
      intro t
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [hc₁_def, div_lt_iff₀ hL_pos, mul_comm],
               by rwa [hc₂_def, le_div_iff₀ hL_pos, mul_comm]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨by rwa [hc₁_def, div_lt_iff₀ hL_pos, mul_comm] at h1,
               by rwa [hc₂_def, le_div_iff₀ hL_pos, mul_comm] at h2⟩
    -- The integrand as a named function
    set φ : ℝ → ℂ := fun t =>
      if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0
      with hφ_def
    -- φ is bounded by 1/c₁
    have hφ_bound : ∀ t : ℝ, ‖φ t‖ ≤ 1 / c₁ := by
      intro t
      simp only [hφ_def]
      by_cases hcond : ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      · simp only [hcond, ite_true]
        exact singular_symmDiff_sup_bound hc₁_pos (le_of_lt ((h_cond_iff t).mp hcond).1)
      · simp only [hcond, ite_false, norm_zero]; positivity
    -- φ is measurable
    have hφ_meas : Measurable φ := by
      simp only [hφ_def]
      apply Measurable.ite
      · apply MeasurableSet.inter
        · exact (isOpen_lt continuous_const (continuous_const.mul
            (continuous_abs.comp (continuous_id.sub continuous_const)))).measurableSet
        · exact (isClosed_le (continuous_const.mul
            (continuous_abs.comp (continuous_id.sub continuous_const)))
            continuous_const).measurableSet
      · exact (Complex.measurable_ofReal.comp (measurable_id.sub_const t₀)).inv
      · exact measurable_const
    -- φ is integrable on any finite interval
    have hφ_integrable : ∀ u v : ℝ, IntervalIntegrable φ MeasureTheory.volume u v := by
      intro u v
      rw [intervalIntegrable_iff]
      exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
        hφ_meas.aestronglyMeasurable.restrict (1 / c₁)
        (Filter.Eventually.of_forall (fun x => hφ_bound x))
    -- Helper: φ = 0 when c-condition fails
    have hφ_zero : ∀ t, ¬(c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂) → φ t = 0 :=
      fun t hnt => by simp only [hφ_def, if_neg (mt (h_cond_iff t).mp hnt)]
    -- Helper: φ = (t-t₀)⁻¹ when c-condition holds
    have hφ_val : ∀ t, c₁ < |t - t₀| ∧ |t - t₀| ≤ c₂ → φ t = (↑(t - t₀) : ℂ)⁻¹ :=
      fun t ht => by simp only [hφ_def, if_pos ((h_cond_iff t).mpr ht)]
    -- Abbreviate integrability
    have hI₁ := hφ_integrable a (t₀ - c₂)
    have hI₂ := hφ_integrable (t₀ - c₂) (t₀ - c₁)
    have hI₃ := hφ_integrable (t₀ - c₁) (t₀ + c₁)
    have hI₄ := hφ_integrable (t₀ + c₁) (t₀ + c₂)
    have hI₅ := hφ_integrable (t₀ + c₂) b
    -- Split ∫_a^b into 5 pieces
    have h_split : ∫ t in a..b, φ t =
        (∫ t in a..(t₀ - c₂), φ t) + (∫ t in (t₀ - c₂)..(t₀ - c₁), φ t) +
        (∫ t in (t₀ - c₁)..(t₀ + c₁), φ t) +
        (∫ t in (t₀ + c₁)..(t₀ + c₂), φ t) + (∫ t in (t₀ + c₂)..b, φ t) := by
      rw [show (∫ t in a..b, φ t) =
          (∫ t in a..(t₀ + c₂), φ t) + (∫ t in (t₀ + c₂)..b, φ t) from
        (intervalIntegral.integral_add_adjacent_intervals
          (hI₁.trans hI₂ |>.trans hI₃ |>.trans hI₄) hI₅).symm,
        show (∫ t in a..(t₀ + c₂), φ t) =
          (∫ t in a..(t₀ + c₁), φ t) + (∫ t in (t₀ + c₁)..(t₀ + c₂), φ t) from
        (intervalIntegral.integral_add_adjacent_intervals
          (hI₁.trans hI₂ |>.trans hI₃) hI₄).symm,
        show (∫ t in a..(t₀ + c₁), φ t) =
          (∫ t in a..(t₀ - c₁), φ t) + (∫ t in (t₀ - c₁)..(t₀ + c₁), φ t) from
        (intervalIntegral.integral_add_adjacent_intervals
          (hI₁.trans hI₂) hI₃).symm,
        show (∫ t in a..(t₀ - c₁), φ t) =
          (∫ t in a..(t₀ - c₂), φ t) + (∫ t in (t₀ - c₂)..(t₀ - c₁), φ t) from
        (intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂).symm]
    -- On (a, t₀-c₂]: |t-t₀| ≥ c₂ a.e., condition fails
    have hφ_zero_left : ∫ t in a..(t₀ - c₂), φ t = 0 := by
      rw [show (∫ t in a..(t₀ - c₂), φ t) = ∫ t in a..(t₀ - c₂), (0 : ℂ) from by
        apply intervalIntegral.integral_congr_ae
        have h_ae : ({t₀ - c₂} : Set ℝ)ᶜ ∈ MeasureTheory.ae MeasureTheory.volume :=
          MeasureTheory.compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton _)
        filter_upwards [h_ae] with t ht_ne ht_mem
        rw [Set.uIoc_of_le (le_of_lt ha_lt_mc₂)] at ht_mem
        have ht_lt : t < t₀ - c₂ := lt_of_le_of_ne ht_mem.2 ht_ne
        exact hφ_zero t (fun ⟨_, hle⟩ => absurd hle (not_le.mpr (by
          rw [abs_of_nonpos (by linarith : t - t₀ ≤ 0)]; linarith)))]
      exact intervalIntegral.integral_zero
    -- On (t₀+c₂, b]: |t-t₀| > c₂, condition fails
    have hφ_zero_right : ∫ t in (t₀ + c₂)..b, φ t = 0 := by
      rw [show (∫ t in (t₀ + c₂)..b, φ t) = ∫ t in (t₀ + c₂)..b, (0 : ℂ) from by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with t ht_mem
        rw [Set.uIoc_of_le (le_of_lt hpc₂_lt_b)] at ht_mem
        exact hφ_zero t (fun ⟨_, hle⟩ => absurd hle (not_le.mpr (by
          rw [abs_of_nonneg (by linarith [ht_mem.1] : 0 ≤ t - t₀)]; linarith [ht_mem.1])))]
      exact intervalIntegral.integral_zero
    -- On [t₀-c₁, t₀+c₁]: |t-t₀| ≤ c₁, condition fails
    have hφ_zero_middle : ∫ t in (t₀ - c₁)..(t₀ + c₁), φ t = 0 := by
      rw [show (∫ t in (t₀ - c₁)..(t₀ + c₁), φ t) = ∫ t in (t₀ - c₁)..(t₀ + c₁), (0 : ℂ) from
        intervalIntegral.integral_congr (fun t ht => by
          rw [Set.uIcc_of_le hmc₁_le_pc₁] at ht
          exact hφ_zero t (fun ⟨hgt, _⟩ => absurd
            (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩) (not_le.mpr hgt)))]
      exact intervalIntegral.integral_zero
    -- On (t₀-c₂, t₀-c₁]: φ =ᵃᵉ (t-t₀)⁻¹ (fails only at t = t₀-c₁, measure 0)
    have hφ_eq_left : ∫ t in (t₀ - c₂)..(t₀ - c₁), φ t =
        ∫ t in (t₀ - c₂)..(t₀ - c₁), (↑(t - t₀) : ℂ)⁻¹ := by
      apply intervalIntegral.integral_congr_ae
      have h_ne : ({t₀ - c₁} : Set ℝ)ᶜ ∈ MeasureTheory.ae MeasureTheory.volume :=
        MeasureTheory.compl_mem_ae_iff.mpr (MeasureTheory.measure_singleton _)
      filter_upwards [h_ne] with t ht_ne ht_mem
      rw [Set.uIoc_of_le hmc₂_le_mc₁] at ht_mem
      have h1 : t₀ - c₂ < t := ht_mem.1
      have h2 : t < t₀ - c₁ := lt_of_le_of_ne ht_mem.2 ht_ne
      exact hφ_val t ⟨by rw [abs_of_nonpos (by linarith : t - t₀ ≤ 0)]; linarith,
                       by rw [abs_of_nonpos (by linarith : t - t₀ ≤ 0)]; linarith⟩
    -- On (t₀+c₁, t₀+c₂]: φ =ᵃᵉ (t-t₀)⁻¹ (fails only at t = t₀+c₁, measure 0)
    have hφ_eq_right : ∫ t in (t₀ + c₁)..(t₀ + c₂), φ t =
        ∫ t in (t₀ + c₁)..(t₀ + c₂), (↑(t - t₀) : ℂ)⁻¹ := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards with t ht_mem
      rw [Set.uIoc_of_le hpc₁_le_pc₂] at ht_mem
      have h1 : t₀ + c₁ < t := ht_mem.1
      have h2 : t ≤ t₀ + c₂ := ht_mem.2
      exact hφ_val t ⟨by rw [abs_of_nonneg (by linarith : 0 ≤ t - t₀)]; linarith,
                       by rw [abs_of_nonneg (by linarith : 0 ≤ t - t₀)]; linarith⟩
    -- Combine: J_lin = ∫ φ = 0 + ∫left + 0 + ∫right + 0 = 0 by S2
    change (∫ t in a..b, φ t) = 0
    rw [h_split, hφ_zero_left, hφ_zero_right, hφ_zero_middle, hφ_eq_left, hφ_eq_right]
    simp only [zero_add, add_zero]
    exact singular_tAnnLin_cancel t₀ hL_pos ε₁ ε₂ hε₂_pos hε₂_le
  -- Step 11: Bound ‖J_γ - J_lin‖ via comparison function on symmDiff
  -- On symmDiff: |t-t₀| > ε₂/(2‖L‖), so |(t-t₀)⁻¹| ≤ 2‖L‖/ε₂
  -- μ(symmDiff) ≤ Kmeas*ε₁²/‖L‖³, product ≤ 4Kmeas*ε₁/‖L‖² = Csing*ε₁
  have h_diff_bound : ‖(∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    then (↑(t - t₀) : ℂ)⁻¹ else 0) - J_lin‖ ≤ Csing * ε₁ := by
    -- Since J_lin = 0, the goal is ‖∫ f_γ‖ ≤ Csing * ε₁.
    -- Strategy: ∫ f_γ = ∫ (f_γ - f_lin) + ∫ f_lin = ∫ d + 0 = ∫ d.
    -- d is supported on the symmDiff of the two annulus conditions, bounded by 2‖L‖/ε₂.
    -- Use norm_setIntegral_le_of_norm_le_const_ae' on the symmDiff (which has
    -- measure ≤ Kmeas * ε₁²/‖L‖³ by h_meas).
    rw [hJ_lin_zero, sub_zero]
    -- Name the integrands
    set f_γ : ℝ → ℂ := fun t => if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_γ_def
    set f_lin : ℝ → ℂ := fun t => if ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_lin_def
    set d : ℝ → ℂ := fun t => f_γ t - f_lin t with hd_def
    set bound := 2 * ‖L‖ / ε₂ with hbound_def
    have hbound_pos : 0 < bound := by positivity
    -- Pointwise bound on d for t ∈ Icc a b
    have hd_bound_on_Icc : ∀ t ∈ Set.Icc a b, ‖d t‖ ≤ bound := by
      intro t ht; simp only [hd_def, hf_γ_def, hf_lin_def]
      by_cases hγ : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ <;>
        by_cases hlin : ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      · simp [hγ, hlin, sub_self]; exact le_of_lt hbound_pos
      · simp only [hγ, hlin, ite_true, ite_false, sub_zero]
        have ht_ne : t ≠ t₀ := by intro heq; simp [heq] at hγ; linarith
        have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_ne)
        have ht_loc := h_localize t ht hγ.2
        have ht_lt_δ_up : |t - t₀| < δ_up :=
          lt_of_lt_of_le ht_loc (le_trans (min_le_right _ _) (min_le_right _ _))
        have hγ_up := h_upper t ht_pos ht_lt_δ_up
        have h_lo : ε₂ / (2 * ‖L‖) ≤ |t - t₀| := le_of_lt (by
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < 2 * ‖L‖)]; linarith)
        exact le_trans (singular_symmDiff_sup_bound (by positivity) h_lo)
          (by rw [hbound_def, one_div, inv_div])
      · simp only [hγ, hlin, ite_false, ite_true, zero_sub, norm_neg]
        have h_lo : ε₂ / (2 * ‖L‖) ≤ |t - t₀| := le_of_lt (by
          calc ε₂ / (2 * ‖L‖) < ε₂ / ‖L‖ :=
                div_lt_div_of_pos_left hε₂_pos hL_pos (by linarith)
            _ ≤ |t - t₀| := by rw [div_le_iff₀ hL_pos, mul_comm]; exact le_of_lt hlin.1)
        exact le_trans (singular_symmDiff_sup_bound (by positivity) h_lo)
          (by rw [hbound_def, one_div, inv_div])
      · simp [hγ, hlin]; exact le_of_lt hbound_pos
    -- Integrability of f_lin (globally measurable + bounded)
    have hf_lin_meas : Measurable f_lin := by
      simp only [hf_lin_def]
      apply Measurable.ite
      · apply MeasurableSet.inter
        · exact (isOpen_lt continuous_const (continuous_const.mul
            (continuous_abs.comp (continuous_id.sub continuous_const)))).measurableSet
        · exact (isClosed_le (continuous_const.mul
            (continuous_abs.comp (continuous_id.sub continuous_const)))
            continuous_const).measurableSet
      · exact (Complex.measurable_ofReal.comp (measurable_id.sub_const t₀)).inv
      · exact measurable_const
    have hf_lin_bound : ∀ t : ℝ, ‖f_lin t‖ ≤ bound := by
      intro t; simp only [hf_lin_def]
      by_cases hcond : ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁
      · simp only [hcond, ite_true]
        have h_lo : ε₂ / (2 * ‖L‖) ≤ |t - t₀| := le_of_lt (by
          calc ε₂ / (2 * ‖L‖) < ε₂ / ‖L‖ :=
                div_lt_div_of_pos_left hε₂_pos hL_pos (by linarith)
            _ ≤ |t - t₀| := by rw [div_le_iff₀ hL_pos, mul_comm]; exact le_of_lt hcond.1)
        exact le_trans (singular_symmDiff_sup_bound (by positivity) h_lo)
          (by rw [hbound_def, one_div, inv_div])
      · simp only [hcond, ite_false, norm_zero]; positivity
    have hf_lin_int : IntervalIntegrable f_lin MeasureTheory.volume a b := by
      rw [intervalIntegrable_iff]
      exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
        hf_lin_meas.aestronglyMeasurable.restrict bound
        (Filter.Eventually.of_forall (fun x => hf_lin_bound x))
    -- Rewrite ∫ f_γ = ∫ d + ∫ f_lin = ∫ d + 0 = ∫ d
    have hf_γ_eq : ∀ t, f_γ t = d t + f_lin t := by
      intro t; simp only [hd_def]; ring
    -- AEStronglyMeasurable f_γ on Ioc a b via h' (StronglyMeasurable representative)
    have h_norm_cont : ContinuousOn (fun t => ‖γ t - γ t₀‖) (Set.Icc a b) :=
      (hγ_cont.sub continuousOn_const).norm
    have h_norm_aesm : AEStronglyMeasurable (fun t => ‖γ t - γ t₀‖)
        (MeasureTheory.volume.restrict (Set.Icc a b)) :=
      h_norm_cont.aestronglyMeasurable measurableSet_Icc
    set h' := h_norm_aesm.mk (fun t => ‖γ t - γ t₀‖) with hh'_def
    have hh'_sm : StronglyMeasurable h' := h_norm_aesm.stronglyMeasurable_mk
    have hh'_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        ‖γ t - γ t₀‖ = h' t := h_norm_aesm.ae_eq_mk
    -- f_γ' uses h' instead of ‖γ t - γ t₀‖, is globally Measurable
    set f_γ' : ℝ → ℂ := fun t => if ε₂ < h' t ∧ h' t ≤ ε₁
      then (↑(t - t₀) : ℂ)⁻¹ else 0 with hf_γ'_def
    have hf_γ'_meas : Measurable f_γ' := by
      simp only [hf_γ'_def]
      apply Measurable.ite
      · apply MeasurableSet.inter
        · exact hh'_sm.measurable measurableSet_Ioi
        · exact hh'_sm.measurable measurableSet_Iic
      · exact (Complex.measurable_ofReal.comp (measurable_id.sub_const t₀)).inv
      · exact measurable_const
    have hf_γ_ae_eq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        f_γ t = f_γ' t := by
      filter_upwards [hh'_ae] with t ht_eq
      simp only [hf_γ_def, hf_γ'_def, ht_eq]
    have hf_γ_aesm : AEStronglyMeasurable f_γ
        (MeasureTheory.volume.restrict (Set.Ioc a b)) :=
      (hf_γ'_meas.aestronglyMeasurable.congr (Filter.EventuallyEq.symm hf_γ_ae_eq)).mono_measure
        (MeasureTheory.Measure.restrict_mono Set.Ioc_subset_Icc_self le_rfl)
    -- Integrability of d on Ioc a b
    have hd_int : IntervalIntegrable d MeasureTheory.volume a b := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hab.le]
      exact MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
        (hf_γ_aesm.sub hf_lin_meas.aestronglyMeasurable.restrict) bound
        ((MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
          (Filter.Eventually.of_forall (fun t ht =>
            hd_bound_on_Icc t (Set.Ioc_subset_Icc_self ht))))
    -- Now: ∫ f_γ = ∫ (d + f_lin) = ∫ d + ∫ f_lin = ∫ d + J_lin = ∫ d + 0 = ∫ d
    have hf_γ_eq_d_add_lin : (∫ t in a..b, f_γ t) = (∫ t in a..b, d t) + J_lin := by
      rw [show J_lin = ∫ t in a..b, f_lin t from rfl]
      rw [← intervalIntegral.integral_add hd_int hf_lin_int]
      exact intervalIntegral.integral_congr (fun t _ => hf_γ_eq t)
    rw [show (∫ t in a..b, f_γ t) = ∫ t in a..b, f_γ t from rfl,
        hf_γ_eq_d_add_lin, hJ_lin_zero, add_zero]
    -- Now bound ‖∫ d‖ using the symmDiff measure from h_meas.
    -- Convert interval integral to set integral and use norm_setIntegral_le_of_norm_le_const_ae'.
    -- Step 1: Convert ∫ t in a..b, d t to ∫ t in Ioc a b, d t
    rw [intervalIntegral.integral_of_le hab.le]
    -- Step 2: Apply norm_setIntegral_le_of_norm_le_const_ae'
    -- ‖∫ t in Ioc a b, d t‖ ≤ bound * volume.real (Ioc a b) -- too loose!
    -- Instead, we'll bound ‖∫ d‖ using the localized symmDiff.
    -- The key: d(t) = 0 a.e. outside the symmDiff, and on the symmDiff ‖d‖ ≤ bound.
    -- Define the measurable approximation to the symmDiff using h'
    set γAnn' := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < h' t ∧ h' t ≤ ε₁}
    set tAnnLin_loc := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
      ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁}
    set S' := symmDiff γAnn' tAnnLin_loc with hS'_def
    -- S' is MeasurableSet (built from measurable operations on h' and linear functions)
    have hγAnn'_meas : MeasurableSet γAnn' := by
      apply MeasurableSet.inter
      · exact measurableSet_Icc
      · apply MeasurableSet.inter
        · exact (isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const))
            continuous_const).measurableSet
        · apply MeasurableSet.inter
          · exact hh'_sm.measurable measurableSet_Ioi
          · exact hh'_sm.measurable measurableSet_Iic
    have htAnnLin_meas : MeasurableSet tAnnLin_loc := by
      apply MeasurableSet.inter
      · exact measurableSet_Icc
      · apply MeasurableSet.inter
        · exact (isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const))
            continuous_const).measurableSet
        · apply MeasurableSet.inter
          · exact (isOpen_lt continuous_const (continuous_const.mul
              (continuous_abs.comp (continuous_id.sub continuous_const)))).measurableSet
          · exact (isClosed_le (continuous_const.mul
              (continuous_abs.comp (continuous_id.sub continuous_const)))
              continuous_const).measurableSet
    have hS'_meas : MeasurableSet S' := hγAnn'_meas.symmDiff htAnnLin_meas
    -- d' = f_γ' - f_lin equals d ae on Icc a b, and d' = 0 outside S' ∪ (Icc a b)ᶜ
    set d' : ℝ → ℂ := fun t => f_γ' t - f_lin t with hd'_def
    -- d =ae d' on Icc a b
    have hd_ae_eq : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
        d t = d' t := by
      filter_upwards [hf_γ_ae_eq] with t ht_eq
      simp only [hd_def, hd'_def, ht_eq]
    -- d' is Measurable
    have hd'_meas : Measurable d' := hf_γ'_meas.sub hf_lin_meas
    -- The set integral ∫_{Ioc} d = ∫_{Ioc} d'
    have h_int_eq : (∫ t in Set.Ioc a b, d t ∂volume) =
        ∫ t in Set.Ioc a b, d' t ∂volume := by
      apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
      filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hd_ae_eq]
        with t h_eq ht_Ioc
      exact h_eq (Set.Ioc_subset_Icc_self ht_Ioc)
    rw [h_int_eq]
    -- d'(t) = 0 for t ∈ Icc a b outside S'
    -- (because if conditions using h' and ‖L‖|t-t₀| agree, d' = inv - inv = 0)
    -- Specifically: d'(t) = 0 when t ∉ S' ∪ (Icc a b)ᶜ ∪ {|t-t₀| ≥ δ₀'}
    -- Actually: for t ∈ Icc a b with |t-t₀| < δ₀':
    --   If t ∈ γAnn' ↔ t ∈ tAnnLin_loc (i.e., t ∉ S'), then d'(t) = 0
    -- For t ∈ Icc a b with |t-t₀| ≥ δ₀':
    --   γ-condition fails (h' condition has |t-t₀| < δ₀' constraint)
    --   Actually, γAnn' requires |t-t₀| < δ₀', so f_γ' condition may differ from γAnn'.
    --   Hmm, f_γ' doesn't have the |t-t₀| < δ₀' constraint!
    --   f_γ'(t) = if (ε₂ < h' t ∧ h' t ≤ ε₁) then inv else 0
    --   This is simpler than γAnn' which also requires Icc and |t-t₀| < δ₀'.
    -- So d'(t) might be nonzero outside S' if t is outside Icc a b or |t-t₀| ≥ δ₀'.
    -- But we only integrate over Ioc a b, so t ∈ Icc a b.
    -- For t ∈ Icc a b with |t-t₀| ≥ δ₀':
    --   f_γ'(t) = if (ε₂ < h' t ∧ h' t ≤ ε₁) then inv else 0
    --   f_lin(t) = if (ε₂ < ‖L‖|t-t₀| ∧ ‖L‖|t-t₀| ≤ ε₁) then inv else 0
    --   The lin-condition: ‖L‖|t-t₀| ≥ ‖L‖*δ₀' > ε₁ (by hε₁_lt_Lδ₀'), so lin fails.
    --   The γ' condition: need ε₂ < h' t, which COULD hold even for |t-t₀| ≥ δ₀'.
    --   So d'(t) could be nonzero for |t-t₀| ≥ δ₀'.
    -- This complicates things. The S' set is the symmDiff of the LOCALIZED sets,
    -- but d' is defined without localization.
    -- Solution: for t ∈ Icc a b with |t-t₀| ≥ δ₀', d(t) = d'(t) ae.
    -- And d(t) = 0 for such t because:
    --   f_γ(t) = 0 (γ-condition requires ‖γ t - γ t₀‖ ≤ ε₁ which forces |t-t₀| < δ₁ ≤ δ₀')
    --   f_lin(t) = 0 (lin-condition requires ‖L‖|t-t₀| ≤ ε₁ < ‖L‖*δ₀', so |t-t₀| < δ₀')
    -- So d(t) = d'(t) = 0 for t ∈ Icc a b, |t-t₀| ≥ δ₀'.
    -- Wait, but d'(t) might not be 0 even though d(t) = 0, because h' might differ from ‖γ t - γ t₀‖.
    -- The ae equality h' = ‖γ t - γ t₀‖ only holds ae on Icc a b.
    -- So d = d' ae on Icc a b, and d = 0 for |t-t₀| ≥ δ₀' (for t ∈ Icc).
    -- Therefore d' = 0 ae for t ∈ Icc a b with |t-t₀| ≥ δ₀'.
    -- And for t ∈ Icc a b with |t-t₀| < δ₀' and t ∉ S': d'(t) = 0 by definition.
    -- So d' = 0 ae on Icc a b \ S' (at least on the part with |t-t₀| < δ₀').
    -- Since d' = d ae on Icc, and d = 0 on |t-t₀| ≥ δ₀', we get d' = 0 ae on (Icc \ S').
    -- This means ∫_{Ioc} d' = ∫_{Ioc ∩ S'} d' (ae equality outside S' gives 0).
    -- Then ‖∫_{Ioc ∩ S'} d'‖ ≤ bound * μ(S' ∩ Ioc).real
    -- And μ(S' ∩ Ioc) ≤ μ(S') = μ(symmDiff γAnn' tAnnLin_loc)
    -- = μ(symmDiff γAnn_loc tAnnLin_loc) (ae equal sets have equal measure)
    -- ≤ Kmeas * ε₁²/‖L‖³ (h_meas)
    -- This is getting very long. Let me use norm_setIntegral_le_of_norm_le_const_ae'
    -- applied to the set S' ∩ Ioc a b, after showing the integral over the complement is 0.
    -- Actually, let me use a simpler approach: bound ∫_{Ioc} |d'| directly.
    -- d' is Measurable, so ‖d'‖ is Measurable. We have ‖d'‖ ≤ bound.
    -- And d' = 0 outside S' (for t ∈ Icc with |t-t₀| < δ₀')... plus ae corrections.
    -- This is still complex. Let me just bound by the containing interval for now
    -- and accept the O(1) bound, then see if a different proof structure works.
    -- ACTUALLY: Let me use a completely different approach.
    -- Instead of the symmDiff measure, use the h_meas bound on the ACTUAL symmDiff
    -- (from the lemma conclusion), combined with norm_setIntegral_le_of_norm_le_const_ae'.
    -- The h_meas bound gives volume(symmDiff_loc) ≤ ENNReal.ofReal(K*ε₁²/‖L‖³).
    -- The actual symmDiff_loc = symmDiff γAnn_loc tAnnLin_loc from h_meas.
    -- For t ∈ Ioc a b, d(t) = 0 when t ∉ symmDiff_eff (the effective symmDiff).
    -- And symmDiff_eff ∩ Icc a b = symmDiff_loc (proven earlier).
    -- So d = 0 ae on Ioc \ symmDiff_loc.
    -- Therefore ∫_{Ioc} d = ∫_{Ioc ∩ symmDiff_loc} d.
    -- Using norm_setIntegral_le_of_norm_le_const_ae':
    -- ‖∫_{Ioc ∩ symmDiff_loc} d‖ ≤ bound * μ(Ioc ∩ symmDiff_loc).real
    -- ≤ bound * μ(symmDiff_loc).real ≤ bound * K*ε₁²/‖L‖³
    -- = (2‖L‖/ε₂) * K*ε₁²/‖L‖³ = 2K*ε₁²/(ε₂*‖L‖²) ≤ 4K*ε₁/‖L‖² = Csing*ε₁
    -- This requires ∫_{Ioc} d = ∫_{Ioc ∩ symmDiff_loc} d, i.e., d vanishes ae outside.
    -- For that, we use: on Ioc, d = d' ae, and d' is supported on... hmm.
    -- Let me just use the simpler bound with ∫_{Ioc} d' and the S' set.
    -- Apply norm_setIntegral_le_of_norm_le_const_ae' to the whole Ioc,
    -- but with the RIGHT bound that accounts for d' being mostly zero.
    -- That is: ‖d'(t)‖ ≤ bound * S'.indicator 1 t (or equivalently, S'.indicator bound t).
    -- Then ∫_{Ioc} ‖d'‖ ≤ ∫_{Ioc} S'.indicator bound ≤ bound * μ(S').real.
    -- And μ(S') = μ(symmDiff γAnn' tAnnLin_loc) = μ(symmDiff γAnn_loc tAnnLin_loc) (ae equal)
    -- ≤ Kmeas * ε₁²/‖L‖³.
    -- For this, I need: (1) S' is measurable (proven), (2) d' = 0 ae outside S' on Ioc,
    -- (3) μ(S') ≤ h_meas bound, (4) combine.
    -- Let me implement this.
    -- Step 1: d' = 0 on the complement of a larger set S_ext ⊇ S'
    -- For t ∈ Icc a b with |t-t₀| < δ₀': d'(t) = 0 iff both h'-condition and lin-condition
    -- either both hold or both fail, i.e., t ∉ S'.
    -- For t outside Icc a b or |t-t₀| ≥ δ₀': d(t) = 0 (proven), so d'(t) = 0 ae.
    -- Let S_ext = S' ∪ {t | t ∉ Icc a b ∨ |t-t₀| ≥ δ₀'} ∩ N where N is the ae null set.
    -- This is getting too complex. Let me use a direct approach.
    -- DIRECT APPROACH: Use norm_integral_le_of_norm_le with g_comp = S'.indicator bound.
    -- This is a measurable function. We need:
    -- (a) g_comp is IntervalIntegrable (indicator of measurable bounded-measure set times const)
    -- (b) ‖d'(t)‖ ≤ g_comp(t) ae on Ioc a b
    -- (c) ∫ g_comp ≤ bound * μ(S' ∩ Ioc).real ≤ bound * K*ε₁²/‖L‖³
    -- For (b): when t ∈ S', ‖d'(t)‖ ≤ bound = g_comp(t).
    --          When t ∉ S' and t ∈ Icc and |t-t₀| < δ₀': d'(t) = 0 = g_comp(t). OK.
    --          When t ∈ Ioc and |t-t₀| ≥ δ₀': d'(t) might not be 0.
    --            But d(t) = 0, so d'(t) = 0 ae. For the ae bound, this is fine.
    -- So (b) holds ae. Good.
    -- Let me implement this now.
    -- g_comp: indicator of S' ∩ Icc a b times bound
    -- Actually, just use S' as the indicator set.
    set g_comp : ℝ → ℝ := S'.indicator (fun _ => bound) with hg_comp_def
    -- g_comp is interval integrable
    have hS'_finite : volume S' < ⊤ := by
      calc volume S' ≤ volume (Set.Icc a b) := by
            apply MeasureTheory.measure_mono
            intro t ht
            rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h.1
        _ < ⊤ := measure_Icc_lt_top
    have hg_int : IntervalIntegrable g_comp volume a b := by
      constructor <;>
        exact (MeasureTheory.integrableOn_const (hs := measure_Ioc_lt_top.ne)).indicator hS'_meas
    -- Pointwise ae bound: ‖d'(t)‖ ≤ g_comp(t) for a.e. t ∈ Ioc a b
    have h_pw_le : ∀ᵐ t ∂volume, t ∈ Set.Ioc a b → ‖d' t‖ ≤ g_comp t := by
      -- We need: for ae t (wrt volume), if t ∈ Ioc a b then ‖d'(t)‖ ≤ g_comp(t).
      -- For t ∈ S': g_comp(t) = bound, and ‖d'(t)‖ ≤ bound (from hd_bound on d, ae eq).
      -- For t ∉ S' ∧ t ∈ Icc ∧ |t-t₀| < δ₀': d'(t) = 0, g_comp(t) = 0. OK.
      -- For t ∉ S' ∧ (t ∉ Icc ∨ |t-t₀| ≥ δ₀'): if t ∈ Ioc then t ∈ Icc.
      --   For |t-t₀| ≥ δ₀': d(t) = 0 and d'(t) = d(t) ae. So d'(t) = 0 ae.
      -- Use the ae equality d = d' on Icc.
      rw [Filter.eventually_iff_exists_mem]
      refine ⟨{t | t ∈ Set.Icc a b → d t = d' t}, ?_, ?_⟩
      · exact (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mp hd_ae_eq
      · intro t ht ht_Ioc
        simp only [g_comp, hg_comp_def, S', Set.indicator]
        by_cases ht_S : t ∈ symmDiff γAnn' tAnnLin_loc
        · simp only [ht_S, ↓reduceIte]
          -- ‖d'(t)‖ ≤ bound: d'(t) = f_γ'(t) - f_lin(t), bounded like d(t) on Icc
          -- Since d = d' on this point (from ht), use hd_bound_on_Icc
          have ht_Icc := Set.Ioc_subset_Icc_self ht_Ioc
          rw [← ht ht_Icc]
          exact hd_bound_on_Icc t ht_Icc
        · simp only [ht_S, ↓reduceIte]
          -- t ∉ S', so the h' and lin conditions agree.
          -- Need to show d'(t) = 0.
          -- Case 1: t ∈ Icc ∧ |t-t₀| < δ₀'
          -- Then: t ∈ γAnn' ↔ t ∈ tAnnLin_loc (since t ∉ symmDiff)
          -- So f_γ'(t) and f_lin(t) have the same indicator, hence d'(t) = 0.
          -- Case 2: |t-t₀| ≥ δ₀'
          -- Then d(t) = 0 (proven), so d'(t) = d(t) = 0 by ae.
          -- But we're in the forall branch (not ae), so we need d'(t) = 0 pointwise here.
          -- This is NOT guaranteed for |t-t₀| ≥ δ₀' because d' might differ from d at this point.
          -- However, we're in the ae part: ht says d(t) = d'(t) on Icc a b.
          -- So for t ∈ Icc a b: d'(t) = d(t).
          -- For |t-t₀| ≥ δ₀': d(t) = 0 (both γ and lin conditions fail), so d'(t) = 0.
          have ht_Icc := Set.Ioc_subset_Icc_self ht_Ioc
          suffices h_dt_zero : d t = 0 by
            have hd_eq : d' t = d t := (ht ht_Icc).symm
            rw [hd_eq, h_dt_zero, norm_zero]
          -- d(t) = 0 because t ∉ S' implies the two conditions agree
          -- For t ∈ Icc with |t-t₀| < δ₀': both conditions hold or both fail
          -- For t ∈ Icc with |t-t₀| ≥ δ₀': both conditions fail
          simp only [hd_def, hf_γ_def, hf_lin_def]
          by_cases hδ : |t - t₀| < δ₀'
          · -- t ∈ Icc, |t-t₀| < δ₀', t ∉ S'
            -- So: t ∈ γAnn_actual ↔ t ∈ tAnnLin_loc
            -- γAnn_actual = {t ∈ Icc | |t-t₀| < δ₀' ∧ ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
            -- Since h' = ‖γ t - γ t₀‖ at this point (from ht on Icc),
            -- γAnn' and γAnn_actual agree at t.
            -- t ∉ S' means t ∈ γAnn' ↔ t ∈ tAnnLin_loc.
            -- Since h'(t) = ‖γ t - γ t₀‖ (by ht), γAnn'(t) ↔ γAnn_actual(t).
            -- So γAnn_actual(t) ↔ tAnnLin_loc(t).
            -- I.e., the two conditions agree: both hold or both fail.
            -- So f_γ(t) - f_lin(t) = 0.
            have h_agree : (ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁) ↔
                (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := by
              -- From t ∉ S' and h'(t) = ‖γ t - γ t₀‖:
              -- t ∈ γAnn' ↔ t ∈ tAnnLin_loc (since t ∉ symmDiff)
              -- γAnn'(t) = (t ∈ Icc ∧ |t-t₀| < δ₀' ∧ ε₂ < h' t ∧ h' t ≤ ε₁)
              -- tAnnLin_loc(t) = (t ∈ Icc ∧ |t-t₀| < δ₀' ∧ ε₂ < ‖L‖|t-t₀| ∧ ‖L‖|t-t₀| ≤ ε₁)
              -- Since t ∈ Icc and |t-t₀| < δ₀':
              -- γAnn'(t) ↔ (ε₂ < h' t ∧ h' t ≤ ε₁)
              -- tAnnLin_loc(t) ↔ (ε₂ < ‖L‖|t-t₀| ∧ ‖L‖|t-t₀| ≤ ε₁)
              -- And since h' t = ‖γ t - γ t₀‖ (at this point):
              -- γAnn'(t) ↔ (ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁)
              -- So: (ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁) ↔ (ε₂ < ‖L‖|t-t₀| ∧ ‖L‖|t-t₀| ≤ ε₁)
              -- because t ∉ symmDiff γAnn' tAnnLin_loc iff (t ∈ γAnn' ↔ t ∈ tAnnLin_loc).
              -- Formally:
              -- Step A: from d(t) = d'(t) and t ≠ t₀, deduce γ-condition ↔ h'-condition
              have hd_eq_at := ht ht_Icc  -- d t = d' t
              -- f_γ t = f_γ' t (since d = f_γ - f_lin and d' = f_γ' - f_lin)
              have hfγ_eq : f_γ t = f_γ' t := by
                have hd_t : d t = f_γ t - f_lin t := rfl
                have hd'_t : d' t = f_γ' t - f_lin t := rfl
                have h := hd_eq_at; rw [hd_t, hd'_t] at h
                have := congr_arg (· + f_lin t) h
                simp [sub_add_cancel] at this; exact this
              -- Step B: from not-symmDiff + t ∈ Icc + |t-t₀| < δ₀', deduce h'-condition ↔ lin-condition
              have h_not_sd := ht_S
              rw [Set.mem_symmDiff] at h_not_sd
              push_neg at h_not_sd
              -- h_not_sd gives (t ∈ γAnn' → t ∈ tAnnLin_loc) ∧ (t ∈ tAnnLin_loc → t ∈ γAnn')
              have h'_iff_lin : (ε₂ < h' t ∧ h' t ≤ ε₁) ↔
                  (ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := by
                constructor
                · intro ⟨h1, h2⟩
                  have hmem : t ∈ γAnn' := ⟨ht_Icc, hδ, h1, h2⟩
                  exact (h_not_sd.1 hmem).2.2
                · intro ⟨h1, h2⟩
                  have hmem : t ∈ tAnnLin_loc := ⟨ht_Icc, hδ, h1, h2⟩
                  exact (h_not_sd.2 hmem).2.2
              -- Step C: chain γ-condition ↔ h'-condition ↔ lin-condition
              by_cases ht_eq : t = t₀
              · -- t = t₀: both conditions trivially false
                subst ht_eq; simp [hε₂_pos.not_le]
              · -- t ≠ t₀: from f_γ = f_γ', the indicator conditions must agree
                have hinv_ne : (↑(t - t₀) : ℂ)⁻¹ ≠ 0 :=
                  inv_ne_zero (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr ht_eq))
                constructor
                · intro hγ_cond
                  have : f_γ t = (↑(t - t₀) : ℂ)⁻¹ := if_pos hγ_cond
                  rw [this] at hfγ_eq
                  -- f_γ' t = inv ≠ 0, so h'-condition must hold
                  by_contra h_neg
                  have : f_γ' t = 0 := by
                    simp only [hf_γ'_def]; exact if_neg (mt h'_iff_lin.mp h_neg)
                  rw [this] at hfγ_eq; exact hinv_ne hfγ_eq
                · intro hlin_cond
                  have hh'_cond := h'_iff_lin.mpr hlin_cond
                  -- f_γ' t = inv
                  have : f_γ' t = (↑(t - t₀) : ℂ)⁻¹ := if_pos hh'_cond
                  rw [this] at hfγ_eq
                  -- f_γ t = inv ≠ 0, so γ-condition must hold
                  by_contra h_neg
                  have : f_γ t = 0 := if_neg h_neg
                  rw [this] at hfγ_eq; exact hinv_ne hfγ_eq.symm
            by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
            · simp [hcond, h_agree.mp hcond, sub_self]
            · simp [hcond, mt h_agree.mpr hcond]
          · -- |t-t₀| ≥ δ₀'
            -- Both conditions fail.
            -- γ-condition: if it held, localize gives |t-t₀| < δ₁ ≤ δ₀', contradiction.
            have hγ_fail : ¬(ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁) := by
              intro ⟨_, h_up⟩
              have := h_localize t ht_Icc h_up
              have : |t - t₀| < δ₀' := lt_of_lt_of_le this (min_le_left _ _)
              linarith [not_lt.mp hδ]
            -- lin-condition: ‖L‖|t-t₀| ≥ ‖L‖δ₀' > ε₁
            have hlin_fail : ¬(ε₂ < ‖L‖ * |t - t₀| ∧ ‖L‖ * |t - t₀| ≤ ε₁) := by
              intro ⟨_, h_le⟩
              have : ‖L‖ * |t - t₀| ≥ ‖L‖ * δ₀' := by
                apply mul_le_mul_of_nonneg_left (not_lt.mp hδ) (le_of_lt hL_pos)
              linarith
            simp [hγ_fail, hlin_fail]
    -- Part 1: Convert ae bound from volume to volume.restrict (Ioc a b)
    have h_pw_le_restrict : ∀ᵐ t ∂volume.restrict (Set.Ioc a b), ‖d' t‖ ≤ g_comp t := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      exact h_pw_le
    -- Part 2: g_comp is integrable on Ioc a b
    have hg_int_Ioc : MeasureTheory.Integrable g_comp (volume.restrict (Set.Ioc a b)) :=
      hg_int.1
    -- Part 3: Bound the measure of S'
    -- S' = symmDiff γAnn' tAnnLin_loc where γAnn' uses h' (ae equal to ‖γ t - γ t₀‖ on Icc)
    -- h_meas gives bound on symmDiff γAnn tAnnLin where γAnn uses ‖γ t - γ t₀‖
    -- Since γAnn' and γAnn differ on a null set (h' =ae ‖γ t - γ t₀‖ on Icc),
    -- and tAnnLin_loc = tAnnLin, we get volume(S') ≤ h_meas bound.
    have hS'_vol_bound : volume S' ≤ ENNReal.ofReal (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) := by
      -- Define γAnn (using ‖γ t - γ t₀‖ directly)
      set γAnn := {t : ℝ | t ∈ Set.Icc a b ∧ |t - t₀| < δ₀' ∧
        ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁}
      -- Step A: symmDiff γAnn' γAnn ⊆ {t ∈ Icc a b | h' t ≠ ‖γ t - γ t₀‖}
      have h_sd_subset : symmDiff γAnn' γAnn ⊆
          {t : ℝ | t ∈ Set.Icc a b ∧ h' t ≠ ‖γ t - γ t₀‖} := by
        intro t ht
        simp only [Set.mem_symmDiff, Set.mem_setOf_eq] at ht ⊢
        rcases ht with ⟨h_in, h_not⟩ | ⟨h_in, h_not⟩
        · refine ⟨h_in.1, fun heq => h_not ?_⟩
          exact ⟨h_in.1, h_in.2.1, heq ▸ h_in.2.2.1, heq ▸ h_in.2.2.2⟩
        · refine ⟨h_in.1, fun heq => h_not ?_⟩
          exact ⟨h_in.1, h_in.2.1, heq.symm ▸ h_in.2.2.1, heq.symm ▸ h_in.2.2.2⟩
      -- Step B: {t ∈ Icc a b | h' t ≠ ‖γ t - γ t₀‖} has measure 0
      have h_null_set : volume {t : ℝ | t ∈ Set.Icc a b ∧ h' t ≠ ‖γ t - γ t₀‖} = 0 := by
        -- From hh'_ae: volume.restrict (Icc a b) {t | ‖γ t - γ t₀‖ ≠ h' t} = 0
        have h_ae_not : (volume.restrict (Set.Icc a b)) {t | ¬(‖γ t - γ t₀‖ = h' t)} = 0 :=
          MeasureTheory.ae_iff.mp hh'_ae
        -- Rewrite the target set as the intersection, then use restrict_apply'
        rw [show {t | t ∈ Set.Icc a b ∧ h' t ≠ ‖γ t - γ t₀‖} =
            {t | ¬(‖γ t - γ t₀‖ = h' t)} ∩ Set.Icc a b from by
          ext t; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Icc, ne_eq, eq_comm]
          exact ⟨fun ⟨h1, h2⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1⟩⟩]
        rw [← MeasureTheory.Measure.restrict_apply' measurableSet_Icc]
        exact h_ae_not
      -- Step C: volume(symmDiff γAnn' γAnn) = 0
      have h_sd_zero : volume (symmDiff γAnn' γAnn) = 0 := by
        exact le_antisymm (le_of_le_of_eq (MeasureTheory.measure_mono h_sd_subset) h_null_set)
          (zero_le _)
      -- Step D: Use triangle inequality for symmDiff
      calc volume S' = volume (symmDiff γAnn' tAnnLin_loc) := rfl
        _ ≤ volume (symmDiff γAnn' γAnn) + volume (symmDiff γAnn tAnnLin_loc) :=
            MeasureTheory.measure_symmDiff_le γAnn' γAnn tAnnLin_loc
        _ = 0 + volume (symmDiff γAnn tAnnLin_loc) := by rw [h_sd_zero]
        _ = volume (symmDiff γAnn tAnnLin_loc) := by simp
        _ ≤ ENNReal.ofReal (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) :=
            h_meas ε₁ ε₂ hε₂_pos hε₂_le hε₁_lt_δ_meas
    -- Part 4: Combine all bounds
    -- ‖∫ d'‖ ≤ ∫ g_comp = ∫ S'.indicator bound = bound * μ(S' ∩ Ioc).real
    -- ≤ bound * μ(S').real ≤ bound * (Kmeas * ε₁²/‖L‖³) ≤ Csing * ε₁
    have hIoc_finite : volume (Set.Ioc a b) < ⊤ := measure_Ioc_lt_top
    calc ‖∫ t in Set.Ioc a b, d' t‖
        ≤ ∫ t in Set.Ioc a b, g_comp t :=
          MeasureTheory.norm_integral_le_of_norm_le hg_int_Ioc h_pw_le_restrict
      _ = ∫ t in (Set.Ioc a b) ∩ S', (fun _ => bound) t := by
          rw [MeasureTheory.setIntegral_indicator hS'_meas]
      _ = volume.real ((Set.Ioc a b) ∩ S') * bound := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
      _ ≤ volume.real S' * bound := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hbound_pos)
          exact measureReal_mono Set.inter_subset_right hS'_finite.ne
      _ ≤ (Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3) * bound := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hbound_pos)
          unfold MeasureTheory.Measure.real
          exact ENNReal.toReal_le_of_le_ofReal (by positivity) hS'_vol_bound
      _ ≤ Csing * ε₁ := by
          -- bound = 2 * ‖L‖ / ε₂, Csing = 4 * Kmeas / ‖L‖ ^ 2
          -- LHS = (Kmeas * ε₁² / ‖L‖³) * (2‖L‖/ε₂)
          -- RHS = (4 * Kmeas / ‖L‖²) * ε₁
          -- Need: ε₁/ε₂ ≤ 2, which follows from h_ratio: ε₁ ≤ 2 * ε₂
          have hL_ne : ‖L‖ ≠ 0 := ne_of_gt hL_pos
          have hε₂_ne : ε₂ ≠ 0 := ne_of_gt hε₂_pos
          -- Suffices to show the inequality after clearing denominators
          -- LHS = Kmeas * ε₁² * (2 * ‖L‖) / (‖L‖³ * ε₂)
          -- RHS = 4 * Kmeas * ε₁ / ‖L‖²
          -- After clearing: 2 * Kmeas * ‖L‖ * ε₁² * ‖L‖² ≤ 4 * Kmeas * ε₁ * ‖L‖³ * ε₂
          -- i.e. 2 * Kmeas * ε₁² * ‖L‖³ ≤ 4 * Kmeas * ε₁ * ε₂ * ‖L‖³
          -- i.e. 2 * ε₁² ≤ 4 * ε₁ * ε₂ (divide by Kmeas * ‖L‖³ > 0)
          -- i.e. ε₁ ≤ 2 * ε₂ (divide by 2 * ε₁ > 0), which is h_ratio
          suffices h : Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3 * bound ≤ Csing * ε₁ by exact h
          show Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3 * (2 * ‖L‖ / ε₂) ≤ 4 * Kmeas / ‖L‖ ^ 2 * ε₁
          have h1 : Kmeas * ε₁ ^ 2 / ‖L‖ ^ 3 * (2 * ‖L‖ / ε₂) =
              2 * Kmeas * ε₁ ^ 2 * ‖L‖ / (‖L‖ ^ 3 * ε₂) := by ring
          have h2 : 4 * Kmeas / ‖L‖ ^ 2 * ε₁ = 4 * Kmeas * ε₁ / ‖L‖ ^ 2 := by ring
          rw [h1, h2]
          rw [div_le_div_iff₀ (mul_pos (by positivity : (0:ℝ) < ‖L‖ ^ 3) hε₂_pos)
              (by positivity : (0:ℝ) < ‖L‖ ^ 2)]
          -- Goal: 2 * Kmeas * ε₁ ^ 2 * ‖L‖ * ‖L‖ ^ 2 ≤ 4 * Kmeas * ε₁ * (‖L‖ ^ 3 * ε₂)
          -- Simplify: both sides have factor Kmeas * ‖L‖^3, need 2 * ε₁² ≤ 4 * ε₁ * ε₂
          have key : ε₁ ^ 2 ≤ ε₁ * (2 * ε₂) := by
            rw [sq]; exact mul_le_mul_of_nonneg_left h_ratio (le_of_lt hε₁_pos)
          nlinarith [mul_pos hKmeas_pos (pow_pos hL_pos 3)]
  -- Step 12: Combine
  calc ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
        then (↑(t - t₀) : ℂ)⁻¹ else 0‖
      = ‖(∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
          then (↑(t - t₀) : ℂ)⁻¹ else 0) - J_lin‖ := by rw [hJ_lin_zero, sub_zero]
    _ ≤ Csing * ε₁ := h_diff_bound


/-- **P1: Uniform step bound** with ε-independent constant.
    Correct quantifier order: `∃ Kstep > 0, ∃ δ > 0, ∀ ε₁ ε₂, ... → bound`.
    This eliminates the K'≤K comparison sorries in `pv_limit_via_dyadic`.

    Kstep = 4*max(0,C)/‖L‖ + Csing where C is the C²-derived remainder bound
    and Csing comes from `singular_annulus_bound_explicit`. -/
lemma pv_step_bound_ratio_two_uniform {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hab : a < b) (hat₀ : t₀ ∈ Set.Ioo a b)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L) (hL : L ≠ 0)
    (hγ_meas : Measurable γ)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b))
    -- Continuity on [a,b] (derivable from hγ_cont_deriv if γ is differentiable on [a,b])
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    -- Injectivity at γ(t₀): γ doesn't return to γ(t₀) elsewhere on [a,b]
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ Kstep > 0, ∃ δ > 0, ∀ ε₁ ε₂ : ℝ, 0 < ε₂ → ε₂ ≤ ε₁ → ε₁ ≤ 2 * ε₂ → ε₁ < δ →
      let I := fun ε => ∫ t in a..b,
        if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0
      ‖I ε₂ - I ε₁‖ ≤ Kstep * ε₁ := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  -- Step 1: Get C² bounded remainder (ε-independent C, δ₀)
  obtain ⟨C, δ₀, hδ₀_pos, hr_bounded⟩ := remainder_bounded_of_C2 hL hγ_C2 hγ_deriv
  -- Step 2: Get singular annulus bound (ε-independent Csing, δ_sing)
  obtain ⟨Csing, hCsing_pos, δ_sing, hδ_sing_pos, h_singular⟩ :=
    singular_annulus_bound_explicit hab hat₀ hγ_C2 hγ_deriv hL hγ_cont h_inj
  -- Step 3: Get lower/upper bounds from C² (ε-independent δ₁)
  have hγ_diff := hγ_C2.differentiableAt one_le_two
  have hγ_hasderiv : HasDerivAt γ L t₀ := by rw [← hγ_deriv]; exact hγ_diff.hasDerivAt
  obtain ⟨δ_lo, hδ_lo_pos, h_lower⟩ := gamma_lower_bound_of_hasDerivAt hL hγ_hasderiv
  obtain ⟨δ_up, hδ_up_pos, h_upper⟩ := gamma_upper_bound_of_hasDerivAt hL hγ_hasderiv
  -- Step 4: Derive no-return from injectivity + continuity (with c = min δ₀ δ₁)
  let δ₁ := min δ_lo δ_up
  have hδ₁_pos : 0 < δ₁ := by simp only [δ₁]; exact lt_min hδ_lo_pos hδ_up_pos
  have hδ₀δ₁_pos : 0 < min δ₀ δ₁ := lt_min hδ₀_pos hδ₁_pos
  obtain ⟨ρ, hρ_pos, h_far_bound⟩ :=
    no_return_of_inj_continuous hδ₀δ₁_pos hγ_cont h_inj
  -- Step 5: Define ε-independent constants
  let Kstep := 4 * max 0 C / ‖L‖ + Csing
  have hKstep_pos : 0 < Kstep := by positivity
  -- Step 6: Define δ that works for all ε uniformly
  -- Key: δ ≤ ρ/2 < ρ ensures ε₁ < ρ, so annulus ⊆ {|t-t₀| < min(δ₀, δ₁)}
  let δ := min (min δ_sing (min δ₀ δ₁)) (ρ / 2)
  have hδ_pos : 0 < δ := by simp only [δ, δ₁]; positivity
  use Kstep, hKstep_pos, δ, hδ_pos
  -- Step 7: Prove for all ε₁, ε₂
  intro ε₁ ε₂ hε₂_pos hε₂_le h_ratio hε₁_lt I
  have hε₁_pos : 0 < ε₁ := lt_of_lt_of_le hε₂_pos hε₂_le
  -- Step 8: Localization - show annulus ⊆ {|t-t₀| < min(δ₀, δ₁)}
  have h_localize : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ₁ := by
    intro t ht hγ_le
    -- ε₁ < δ ≤ ρ/2 < ρ, so by h_far_bound: |t-t₀| < min(δ₀, δ₁)
    have hε₁_lt_ρ : ε₁ < ρ := by
      calc ε₁ < δ := hε₁_lt
        _ ≤ ρ / 2 := min_le_right _ _
        _ < ρ := by linarith
    by_contra h_not_lt
    push_neg at h_not_lt
    -- h_far_bound: min δ₀ δ₁ ≤ |t-t₀| → ρ ≤ ‖γ t - γ t₀‖, contradicts ‖γ‖ ≤ ε₁ < ρ
    linarith [h_far_bound t ht h_not_lt]
  -- Step 9: Integrability at cutoffs
  have hI_int₂ := cutoff_integrand_intervalIntegrable hat₀ hL hγ_meas hγ_cont_deriv ε₂ hε₂_pos
  have hI_int₁ := cutoff_integrand_intervalIntegrable hat₀ hL hγ_meas hγ_cont_deriv ε₁ hε₁_pos
  -- Step 10: Rewrite I ε₂ - I ε₁ as annulus integral
  let f := fun t => (γ t - γ t₀)⁻¹ * deriv γ t
  have h_diff : I ε₂ - I ε₁ =
      ∫ t in a..b, (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) := by
    simp only [I, f]; exact cutoff_diff_eq_annulus_integral hε₂_le hI_int₂ hI_int₁
  -- Step 11: Decompose integrand f = singular + remainder
  let r := fun t => f t - (↑(t - t₀))⁻¹
  -- Step 12: Pointwise split on annulus
  have h_pw : ∀ t, (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) =
      (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
      (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) := by
    intro t; by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · rw [if_pos hcond, if_pos hcond, if_pos hcond]; simp only [r, f]; ring
    · rw [if_neg hcond, if_neg hcond, if_neg hcond, add_zero]
  -- Step 13: Integrability of singular/remainder annulus parts (bounded indicators)
  have h_sing_int : IntervalIntegrable
      (fun t => if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0)
      MeasureTheory.volume a b := by
    rw [intervalIntegrable_iff]
    have h_meas_cond : MeasurableSet {t : ℝ | ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁} :=
      (measurableSet_lt measurable_const (hγ_meas.sub_const (γ t₀)).norm).inter
        (measurableSet_le (hγ_meas.sub_const (γ t₀)).norm measurable_const)
    refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top
      (Measurable.ite h_meas_cond
        (Complex.measurable_ofReal.comp (measurable_id.sub measurable_const)).inv
        measurable_const).aestronglyMeasurable (2 * ‖L‖ / ε₂) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [min_eq_left hab.le, max_eq_right hab.le] at ht
    have ht_Icc : t ∈ Set.Icc a b := Set.Ioc_subset_Icc_self ht
    by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
    · rw [if_pos hcond, norm_inv, Complex.norm_real, Real.norm_eq_abs]
      have h_t_ne : t ≠ t₀ := by
        intro heq; subst heq; simp at hcond; linarith [hcond.1]
      have h_abs_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr h_t_ne)
      have h_lt_δ_up : |t - t₀| < δ_up :=
        lt_of_lt_of_le (h_localize t ht_Icc hcond.2) (le_trans (min_le_right _ _) (min_le_right _ _))
      have h_up := h_upper t h_abs_pos h_lt_δ_up
      have h_t_lower : ε₂ / (2 * ‖L‖) < |t - t₀| := by
        rw [div_lt_iff₀ (by positivity : 0 < 2 * ‖L‖)]; linarith [hcond.1]
      calc |t - t₀|⁻¹ ≤ (ε₂ / (2 * ‖L‖))⁻¹ := inv_anti₀ (by positivity) (le_of_lt h_t_lower)
        _ = 2 * ‖L‖ / ε₂ := by rw [inv_div]
    · rw [if_neg hcond, norm_zero]; positivity
  have h_rem_int : IntervalIntegrable
      (fun t => if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0)
      MeasureTheory.volume a b := by
    -- annulus(r) = annulus(f) - annulus(singular), both integrable
    have hf_annulus_int : IntervalIntegrable
        (fun t => if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0)
        MeasureTheory.volume a b := by
      apply (hI_int₂.sub hI_int₁).congr
      intro t _
      show (if ε₂ < ‖γ t - γ t₀‖ then f t else 0) - (if ε₁ < ‖γ t - γ t₀‖ then f t else 0) =
        if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0
      by_cases h₂ : ε₂ < ‖γ t - γ t₀‖
      · rw [if_pos h₂]
        by_cases h₁ : ε₁ < ‖γ t - γ t₀‖
        · rw [if_pos h₁, sub_self, if_neg (fun h => absurd h₁ (not_lt.mpr h.2))]
        · push_neg at h₁; rw [if_neg (not_lt.mpr h₁), sub_zero, if_pos ⟨h₂, h₁⟩]
      · rw [if_neg h₂, zero_sub]
        by_cases h₁ : ε₁ < ‖γ t - γ t₀‖
        · exfalso; exact h₂ (lt_of_le_of_lt hε₂_le h₁)
        · rw [if_neg h₁, neg_zero, if_neg (fun h => h₂ h.1)]
    exact (hf_annulus_int.sub h_sing_int).congr (fun t _ => by
      show (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) -
        (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) =
        if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0
      by_cases hcond : ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁
      · simp only [if_pos hcond]; ring
      · simp only [if_neg hcond, sub_zero])
  -- Step 14: Split annulus integral into singular + remainder
  have h_annulus_split :
      ∫ t in a..b, (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) =
      (∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
      (∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) := by
    have h_eq : (fun t => if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then f t else 0) =
        fun t => (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
                 (if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0) := funext (h_pw ·)
    rw [h_eq]; exact intervalIntegral.integral_add h_sing_int h_rem_int
  -- Step 15: Bound singular part using h_singular
  have hε₁_lt_δ_sing : ε₁ < δ_sing :=
    lt_of_lt_of_le hε₁_lt (le_trans (min_le_left _ _) (min_le_left _ _))
  have h_sing_bound :
      ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0‖ ≤
        Csing * ε₁ := h_singular ε₁ ε₂ hε₂_pos hε₂_le h_ratio hε₁_lt_δ_sing
  -- Step 16: Bound remainder part using remainder_integral_bound_on_annulus
  have h_loc_for_rem : ∀ t ∈ Set.Icc a b, ‖γ t - γ t₀‖ ≤ ε₁ → |t - t₀| < min δ₀ δ_lo :=
    fun t ht hγ => lt_of_lt_of_le (h_localize t ht hγ)
      (min_le_min_left δ₀ (min_le_left δ_lo δ_up))
  have h_rem_bound : ‖∫ t in a..b,
      if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ ≤
        max 0 C * (4 * ε₁ / ‖L‖) := by
    simp only [r, f]
    exact remainder_integral_bound_on_annulus hL hε₁_pos hε₂_pos hr_bounded h_lower h_loc_for_rem hat₀
  -- Step 17: Combine using triangle inequality
  rw [h_diff, h_annulus_split]
  calc ‖(∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0) +
         ∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖
      ≤ ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then (↑(t - t₀) : ℂ)⁻¹ else 0‖ +
        ‖∫ t in a..b, if ε₂ < ‖γ t - γ t₀‖ ∧ ‖γ t - γ t₀‖ ≤ ε₁ then r t else 0‖ := norm_add_le _ _
    _ ≤ Csing * ε₁ + max 0 C * (4 * ε₁ / ‖L‖) := add_le_add h_sing_bound h_rem_bound
    _ = (4 * max 0 C / ‖L‖ + Csing) * ε₁ := by ring
    _ = Kstep * ε₁ := by simp only [Kstep]

/-- **Bracket ε between dyadic points**: For any ε ∈ (0, δ], find n with δ/2^(n+1) < ε ≤ δ/2^n. -/
lemma exists_dyadic_bracket {δ ε : ℝ} (hδ_pos : 0 < δ) (hε_pos : 0 < ε) (hε_le : ε ≤ δ) :
    ∃ n : ℕ, δ / 2^(n+1) < ε ∧ ε ≤ δ / 2^n := by
  -- Use that 2^n → ∞, so δ/2^n → 0
  -- There exists smallest n with δ/2^n < ε, then n-1 works
  have h_tendsto : Tendsto (fun n : ℕ => δ / 2^n) atTop (𝓝 0) := by
    have hp : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2)
    have hi : Tendsto (fun n : ℕ => 1 / (2:ℝ)^n) atTop (𝓝 0) := by
      simp_rw [one_div]; exact tendsto_inv_atTop_zero.comp hp
    have h_eq : (fun n : ℕ => δ / 2^n) = (fun n => δ * (1 / 2^n)) := by ext n; ring
    rw [h_eq, show (0 : ℝ) = δ * 0 by ring]
    exact Tendsto.const_mul δ hi
  -- Since δ/2^n → 0 and ε > 0, eventually δ/2^n < ε
  rw [Metric.tendsto_atTop] at h_tendsto
  obtain ⟨N, hN⟩ := h_tendsto ε hε_pos
  -- Find the transition point
  have h_exists : ∃ n : ℕ, δ / 2^n < ε := by
    use N; specialize hN N le_rfl
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hδ_pos (by positivity))] at hN
    exact hN
  -- Take the smallest n with δ/2^n < ε
  let m := Nat.find h_exists
  have hm_lt : δ / 2^m < ε := Nat.find_spec h_exists
  by_cases hm_zero : m = 0
  · -- If m = 0, then δ < ε, contradicting ε ≤ δ
    simp only [hm_zero, pow_zero, div_one] at hm_lt
    exact absurd hε_le (not_le.mpr hm_lt)
  · -- m ≥ 1, so m = (m-1) + 1. Use n = m - 1.
    obtain ⟨n, hn_eq⟩ := Nat.exists_eq_succ_of_ne_zero hm_zero
    use n
    constructor
    · -- δ/2^(n+1) < ε: this is δ/2^m < ε
      have : n + 1 = m := hn_eq.symm
      rw [this]; exact hm_lt
    · -- ε ≤ δ/2^n: by minimality of m
      by_contra h_not
      push_neg at h_not
      have hn_lt_m : n < m := by omega
      exact Nat.find_min h_exists hn_lt_m h_not

/-- **Telescoping sum bound**: For a sequence with step bounds ‖x_{n+1} - x_n‖ ≤ K*δ/2^n,
the difference ‖x_M - x_N‖ ≤ 2*K*δ/2^N - 2*K*δ/2^M for M > N.
This is the geometric series partial sum bound. -/
lemma telescoping_sum_bound {X : Type*} [SeminormedAddCommGroup X] {I : ℕ → X} {K δ : ℝ}
    (hK_pos : 0 < K) (hδ_pos : 0 < δ)
    (h_step : ∀ n, ‖I (n + 1) - I n‖ ≤ K * δ / 2^n)
    (N : ℕ) : ∀ M, M > N → ‖I M - I N‖ ≤ 2 * K * δ / 2^N - 2 * K * δ / 2^M := by
  intro M hM_gt_N
  -- Induction on M starting from N + 1
  obtain ⟨d, hd_eq⟩ : ∃ d, M = N + d + 1 := by
    use M - N - 1; omega
  subst hd_eq
  induction d with
  | zero =>
    -- M = N + 1
    have h_step_N := h_step N
    calc ‖I (N + 0 + 1) - I N‖
        = ‖I (N + 1) - I N‖ := by ring_nf
      _ ≤ K * δ / 2^N := h_step_N
      _ = 2 * K * δ / 2^N - K * δ / 2^N := by ring
      _ = 2 * K * δ / 2^N - 2 * K * δ / 2^(N+1) := by rw [pow_succ]; ring
      _ = 2 * K * δ / 2^N - 2 * K * δ / 2^(N + 0 + 1) := by ring_nf
  | succ d' ih =>
    -- M = N + d' + 2, ih gives bound for N + d' + 1
    have ih' := ih (by omega : N + d' + 1 > N)
    -- Normalize: N + (d' + 1) + 1 = N + d' + 2
    have h_M_eq : N + (d' + 1) + 1 = N + d' + 2 := by omega
    show ‖I (N + (d' + 1) + 1) - I N‖ ≤ 2 * K * δ / 2^N - 2 * K * δ / 2^(N + (d' + 1) + 1)
    simp only [h_M_eq]
    have h_split : I (N + d' + 2) - I N =
        (I (N + d' + 2) - I (N + d' + 1)) + (I (N + d' + 1) - I N) :=
      (sub_add_sub_cancel (I (N + d' + 2)) (I (N + d' + 1)) (I N)).symm
    rw [h_split]
    have h_step_eq : N + d' + 2 = (N + d' + 1) + 1 := by omega
    have h_step_d' : ‖I (N + d' + 2) - I (N + d' + 1)‖ ≤ K * δ / 2^(N + d' + 1) := by
      conv_lhs => rw [h_step_eq]
      exact h_step (N + d' + 1)
    calc ‖I (N + d' + 2) - I (N + d' + 1) + (I (N + d' + 1) - I N)‖
        ≤ ‖I (N + d' + 2) - I (N + d' + 1)‖ + ‖I (N + d' + 1) - I N‖ := norm_add_le _ _
      _ ≤ K * δ / 2^(N + d' + 1) + (2 * K * δ / 2^N - 2 * K * δ / 2^(N + d' + 1)) := by linarith [h_step_d', ih']
      _ = 2 * K * δ / 2^N - K * δ / 2^(N + d' + 1) := by ring
      _ = 2 * K * δ / 2^N - 2 * K * δ / 2^(N + d' + 2) := by
          have h_pow : (2:ℝ)^(N + d' + 2) = 2 * 2^(N + d' + 1) := by rw [pow_succ]; ring
          field_simp [h_pow]; ring

/-- **PV limit via dyadic sequence**. The cutoff integral converges along the
dyadic sequence, then we extend to all ε by bounded ratio.

**Key hypotheses:** `hγ_cont` and `h_inj` replace the old `h_no_return`. Together with
compactness of [a,b], they imply γ stays bounded away from γ(t₀) outside any
neighborhood of t₀ (via `no_return_of_inj_continuous`). -/
lemma pv_limit_via_dyadic {γ : ℝ → ℂ} {a b t₀ : ℝ} {L : ℂ}
    (hat₀ : t₀ ∈ Set.Ioo a b) (hL : L ≠ 0)
    (hγ_C2 : ContDiffAt ℝ 2 γ t₀) (hγ_deriv : deriv γ t₀ = L)
    (hγ_cont_deriv : ContinuousOn (deriv γ) (Set.Icc a b))
    (hγ_meas : Measurable γ)
    -- Continuity on [a,b]
    (hγ_cont : ContinuousOn γ (Set.Icc a b))
    -- Injectivity at γ(t₀): γ doesn't return to γ(t₀) elsewhere on [a,b]
    (h_inj : ∀ t ∈ Set.Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ limit : ℂ, Tendsto (fun ε =>
      ∫ t in a..b, if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 limit) := by
  -- Step 1: Derive a < b and get uniform step bound from P1 (ε-independent K, δ_P1)
  have hab : a < b := lt_trans (Set.mem_Ioo.mp hat₀).1 (Set.mem_Ioo.mp hat₀).2
  obtain ⟨K, hK_pos, δ_P1, hδ_P1_pos, h_step_uniform⟩ :=
    pv_step_bound_ratio_two_uniform hab hat₀ hγ_C2 hγ_deriv hL hγ_meas hγ_cont_deriv hγ_cont h_inj
  -- Step 2: δ = δ_P1/2 ensures all dyadic points satisfy ε < δ_P1
  let δ := δ_P1 / 2
  have hδ_pos : 0 < δ := by positivity
  -- Step 3: All dyadic points are < δ_P1 (needed for P1 application)
  have h_dyadic_lt : ∀ n : ℕ, δ / 2 ^ n < δ_P1 := fun n =>
    calc δ / 2 ^ n ≤ δ := div_le_self hδ_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      _ < δ_P1 := by simp only [δ]; linarith
  -- Step 4: Define the cutoff integral and prove dyadic step bounds via P1
  let I : ℝ → ℂ := fun ε => ∫ t in a..b,
    if ε < ‖γ t - γ t₀‖ then (γ t - γ t₀)⁻¹ * deriv γ t else 0
  have h_step : ∀ n, ‖I (δ / 2 ^ (n + 1)) - I (δ / 2 ^ n)‖ ≤ K * δ / 2 ^ n := fun n => by
    have hε₂_pos : 0 < δ / 2 ^ (n + 1) := div_pos hδ_pos (by positivity)
    have h_le : δ / 2 ^ (n + 1) ≤ δ / 2 ^ n :=
      div_le_div_of_nonneg_left hδ_pos.le (by positivity)
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ n))
    have h_ratio : δ / 2 ^ n ≤ 2 * (δ / 2 ^ (n + 1)) := by rw [pow_succ]; ring_nf; linarith
    -- Apply P1 directly (no K'≤K comparison needed!)
    have h_bound := h_step_uniform (δ / 2 ^ n) (δ / 2 ^ (n + 1)) hε₂_pos h_le h_ratio (h_dyadic_lt n)
    calc ‖I (δ / 2 ^ (n + 1)) - I (δ / 2 ^ n)‖
        ≤ K * (δ / 2 ^ n) := h_bound
      _ = K * δ / 2 ^ n := by ring
  -- Step 5: Cauchy sequence from geometric step bounds
  have h_cauchy_seq : CauchySeq (fun n => I (δ / 2 ^ n)) :=
    cauchySeq_pv_dyadic hδ_pos hK_pos h_step
  -- Step 6: Extract limit from completeness
  have h_limit_exists : ∃ L, Tendsto (fun n => I (δ / 2 ^ n)) atTop (𝓝 L) :=
    CompleteSpace.complete h_cauchy_seq
  obtain ⟨limit_dyadic, h_limit_dyadic⟩ := h_limit_exists
  -- Step 7: Extend to full filter 𝓝[>] 0
  use limit_dyadic
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro η hη_pos
  have h_half_pos : 0 < η / 2 := by linarith
  have h_quarter_pos : 0 < η / 4 := by linarith
  rw [Metric.tendsto_atTop] at h_limit_dyadic
  obtain ⟨N₁, hN₁⟩ := h_limit_dyadic (η / 2) h_half_pos
  -- Find N₂ with K*δ/2^N₂ < η/4
  have h_pow_unbounded : ∃ N₂ : ℕ, K * δ / 2 ^ N₂ < η / 4 := by
    have : Tendsto (fun n : ℕ => K * δ / 2 ^ n) atTop (𝓝 0) := by
      have h_tendsto_pow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
      have h_tendsto_inv : Tendsto (fun n : ℕ => 1 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
        simp_rw [one_div]; exact tendsto_inv_atTop_zero.comp h_tendsto_pow
      convert Tendsto.const_mul (K * δ) h_tendsto_inv using 1 <;> [ext n; skip] <;> ring
    rw [Metric.tendsto_atTop] at this
    obtain ⟨N₂, hN₂⟩ := this (η / 4) h_quarter_pos
    refine ⟨N₂, ?_⟩
    specialize hN₂ N₂ le_rfl
    have h_val_pos : K * δ / 2 ^ N₂ > 0 := div_pos (mul_pos hK_pos hδ_pos) (by positivity)
    rw [Real.dist_eq, sub_zero, abs_of_pos h_val_pos] at hN₂
    exact hN₂
  obtain ⟨N₂, hN₂⟩ := h_pow_unbounded
  let N := max N₁ N₂
  use δ / 2 ^ N
  constructor
  · exact div_pos hδ_pos (by positivity)
  · intro ε hε_dist hε_pos
    have hε_pos' : 0 < ε := Set.mem_Ioi.mp hε_dist
    have hε_lt_dyadic : ε < δ / 2 ^ N := by
      rwa [Real.dist_eq, sub_zero, abs_of_pos hε_pos'] at hε_pos
    -- Triangle: dist(I ε, limit) ≤ dist(I ε, I(δ/2^N)) + dist(I(δ/2^N), limit)
    have h_tri := dist_triangle (I ε) (I (δ / 2 ^ N)) limit_dyadic
    -- Second term: bounded by hN₁ since N ≥ N₁
    have h_second : dist (I (δ / 2 ^ N)) limit_dyadic < η / 2 := hN₁ N (le_max_left _ _)
    -- First term: use telescoping/step bounds
    have h_first : dist (I ε) (I (δ / 2 ^ N)) ≤ 2 * K * δ / 2 ^ N := by
      rw [dist_eq_norm]
      -- Bracket ε between dyadic points
      have hε_le_δ : ε ≤ δ := le_trans (le_of_lt hε_lt_dyadic)
        (div_le_self hδ_pos.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
      obtain ⟨M, hM_lower, hM_upper⟩ := exists_dyadic_bracket hδ_pos hε_pos' hε_le_δ
      -- Show M ≥ N
      have hM_ge_N : M ≥ N := by
        by_contra h_lt
        push_neg at h_lt
        have hM1_le_N : M + 1 ≤ N := h_lt
        have h_pow_le : (2 : ℝ) ^ (M + 1) ≤ 2 ^ N :=
          pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hM1_le_N
        have h_div_ge : δ / 2 ^ (M + 1) ≥ δ / 2 ^ N :=
          div_le_div_of_nonneg_left hδ_pos.le (by positivity) h_pow_le
        linarith
      -- Apply P1 directly to get h_first_piece (no h_localize_δ or K'≤K sorry needed!)
      have h_first_piece : ‖I ε - I (δ / 2 ^ M)‖ ≤ K * δ / 2 ^ M := by
        have h_ratio_M : δ / 2 ^ M ≤ 2 * ε := by
          have : δ / 2 ^ M = 2 * (δ / 2 ^ (M + 1)) := by rw [pow_succ]; ring
          linarith
        have h_bound := h_step_uniform (δ / 2 ^ M) ε hε_pos' hM_upper h_ratio_M (h_dyadic_lt M)
        calc ‖I ε - I (δ / 2 ^ M)‖
            ≤ K * (δ / 2 ^ M) := h_bound
          _ = K * δ / 2 ^ M := by ring
      -- Combine using telescoping sum
      by_cases hMN : M = N
      · subst hMN
        have hKδN_nonneg : 0 ≤ K * δ / 2 ^ N := by positivity
        calc ‖I ε - I (δ / 2 ^ N)‖
            ≤ K * δ / 2 ^ N := h_first_piece
          _ ≤ K * δ / 2 ^ N + K * δ / 2 ^ N := by linarith
          _ = 2 * K * δ / 2 ^ N := by ring
      · have hM_gt_N : M > N := Nat.lt_of_le_of_ne hM_ge_N (Ne.symm hMN)
        have h_tri_inner : ‖I ε - I (δ / 2 ^ N)‖ ≤
            ‖I ε - I (δ / 2 ^ M)‖ + ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ := by
          rw [show I ε - I (δ / 2 ^ N) =
            (I ε - I (δ / 2 ^ M)) + (I (δ / 2 ^ M) - I (δ / 2 ^ N)) from by ring]
          exact norm_add_le _ _
        let J : ℕ → ℂ := fun n => I (δ / 2 ^ n)
        have h_step_J : ∀ n, ‖J (n + 1) - J n‖ ≤ K * δ / 2 ^ n := fun n => by
          simp only [J]; exact h_step n
        have h_sum_bound : ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ ≤
            2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M := by
          have h_bound := telescoping_sum_bound hK_pos hδ_pos h_step_J N M hM_gt_N
          simp only [J] at h_bound
          exact h_bound
        calc ‖I ε - I (δ / 2 ^ N)‖
            ≤ ‖I ε - I (δ / 2 ^ M)‖ + ‖I (δ / 2 ^ M) - I (δ / 2 ^ N)‖ := h_tri_inner
          _ ≤ K * δ / 2 ^ M + (2 * K * δ / 2 ^ N - 2 * K * δ / 2 ^ M) := by
              linarith [h_first_piece, h_sum_bound]
          _ = 2 * K * δ / 2 ^ N - K * δ / 2 ^ M := by ring
          _ ≤ 2 * K * δ / 2 ^ N := by
              linarith [show (0 : ℝ) ≤ K * δ / 2 ^ M from by positivity]
    -- Combine: 2K*δ/2^N < η/2
    have hN_ge_N₂ : N ≥ N₂ := le_max_right _ _
    have hKδ_nonneg : 0 ≤ K * δ := mul_nonneg hK_pos.le hδ_pos.le
    have h_pow_le : (2 : ℝ) ^ N₂ ≤ 2 ^ N :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hN_ge_N₂
    have h_step_small : K * δ / 2 ^ N ≤ K * δ / 2 ^ N₂ :=
      div_le_div_of_nonneg_left hKδ_nonneg (by positivity) h_pow_le
    have h_Kδ_bound : K * δ / 2 ^ N < η / 4 := lt_of_le_of_lt h_step_small hN₂
    have h_first_small : 2 * K * δ / 2 ^ N < η / 2 := by
      have h_eq1 : 2 * K * δ / 2 ^ N = 2 * (K * δ / 2 ^ N) := by ring
      have h_eq2 : (2 : ℝ) * (η / 4) = η / 2 := by ring
      rw [h_eq1, ← h_eq2]
      exact mul_lt_mul_of_pos_left h_Kδ_bound (by norm_num : (0 : ℝ) < 2)
    calc dist (I ε) limit_dyadic
        ≤ dist (I ε) (I (δ / 2 ^ N)) + dist (I (δ / 2 ^ N)) limit_dyadic := h_tri
      _ ≤ 2 * K * δ / 2 ^ N + dist (I (δ / 2 ^ N)) limit_dyadic := by linarith
      _ < 2 * K * δ / 2 ^ N + η / 2 := by linarith
      _ < η / 2 + η / 2 := by linarith
      _ = η := by ring




/-- **B5 Helper**: Sum of Cauchy and eventually-constant is Cauchy.

If F is Cauchy and G is eventually constant (hence convergent), then F + G is Cauchy. -/
lemma cauchy_add_eventually_const {α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] {l : Filter ℝ} [l.NeBot]
    {f g : ℝ → α} (hf : Cauchy (Filter.map f l))
    (hg_const : ∃ c, ∀ᶠ ε in l, g ε = c) :
    Cauchy (Filter.map (fun ε => f ε + g ε) l) := by
  obtain ⟨c, hc⟩ := hg_const
  have heq : Filter.map (fun ε => f ε + g ε) l = Filter.map (fun ε => f ε + c) l := by
    apply Filter.map_congr; filter_upwards [hc] with ε hε; rw [hε]
  rw [heq]
  exact hf.map (uniformContinuous_add_right c)

/-! ## Regular Part Continuity -/

/-- **C2 Helper**: Away from zeros, logDeriv is analytic.

On the upper half plane minus the zeros, logDeriv (modularFormCompOfComplex f) is analytic. -/
lemma analyticAt_logDeriv_off_zeros (z : ℂ) (hz : 0 < z.im)
    (hfz : modularFormCompOfComplex f z ≠ 0) :
    AnalyticAt ℂ (logDeriv (modularFormCompOfComplex f)) z := by
  have h_diffOn : DifferentiableOn ℂ (modularFormCompOfComplex f) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  have h_analytic : AnalyticAt ℂ (modularFormCompOfComplex f) z :=
    h_diffOn.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  exact h_analytic.deriv.fun_div h_analytic hfz

/-- **C3 Helper**: The regular part (logDeriv - poles) is analytic on the punctured neighborhood.

At a zero s, logDeriv has a simple pole with residue = order, so subtracting
(order)/(z - s) cancels the pole. The resulting function equals logDeriv g on z ≠ s,
where g is analytic with g(s) ≠ 0.

NOTE: We claim analyticity on the PUNCTURED neighborhood only. The function value
at s (which is 0 by Lean's convention for 0/0) may differ from the limit.
For the valence formula, this suffices since single points have measure zero. -/
lemma analyticOnNhd_logDeriv_regular_part_at_zero (hf : f ≠ 0) (s : ℍ) (hs : f s = 0)
    (order : ℤ) (horder : order = orderOfVanishingAt' f s) :
    ∀ᶠ z in 𝓝[≠] (s : ℂ), AnalyticAt ℂ
      (fun w => logDeriv (modularFormCompOfComplex f) w - (order : ℂ) / (w - s)) z := by
  -- Get the decomposition: logDeriv f z = n/(z-s) + logDeriv g z with g analytic, g(s) ≠ 0
  obtain ⟨n, g, _hn_pos, hg_analytic, hg_ne_zero, hn_eq_order, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s hs
  -- Connect order = n using orderOfVanishingAt'_eq_analyticOrderNatAt
  have h_order_eq : order = n := by
    rw [horder, orderOfVanishingAt'_eq_analyticOrderNatAt f s hf hs, hn_eq_order]
  -- logDeriv g is analytic in a neighborhood of s
  have h_logDeriv_g_analytic : AnalyticAt ℂ (logDeriv g) (s : ℂ) :=
    hg_analytic.deriv.fun_div hg_analytic hg_ne_zero
  -- Convert h_formula to "eventually at z, eventually at w" form
  have h_formula_ev : ∀ᶠ z in 𝓝 (s : ℂ), ∀ᶠ w in 𝓝 z, w ≠ (s : ℂ) →
      logDeriv (modularFormCompOfComplex f) w = (n : ℂ) / (w - s) + logDeriv g w :=
    eventually_eventually_nhds.mpr h_formula
  -- On the punctured neighborhood, the function equals logDeriv g
  rw [eventually_nhdsWithin_iff]
  filter_upwards [h_logDeriv_g_analytic.eventually_analyticAt, h_formula_ev] with z hg_anal h_form_z hzne
  -- Transfer analyticity: logDeriv g is analytic at z, and the function agrees with it nearby
  apply hg_anal.congr
  -- Show: logDeriv g =ᶠ[𝓝 z] (fun w => logDeriv f w - order/(w - s))
  have h_nhd_avoid_s : {(s : ℂ)}ᶜ ∈ 𝓝 z := isOpen_compl_singleton.mem_nhds hzne
  filter_upwards [h_nhd_avoid_s, h_form_z] with w hw h_w_eq
  rw [h_w_eq hw, h_order_eq]
  ring

/-- The regular part of logDeriv f is continuous on the punctured set (away from zeros).

For the valence formula, this is sufficient since we only need integrability,
and single points have measure zero. -/
theorem continuousOn_logDeriv_regular_part_punctured (hf : f ≠ 0)
    (zeros : Finset ℍ) (orders : ℍ → ℤ)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (horders : ∀ s ∈ zeros, orders s = orderOfVanishingAt' f s)
    (hzeros_exhaust : ∀ z, 0 < z.im → modularFormCompOfComplex f z = 0 →
        z ∈ Finset.image (fun s : ℍ => (s : ℂ)) zeros) :
    ContinuousOn (fun z : ℂ =>
      logDeriv (modularFormCompOfComplex f) z - ∑ s ∈ zeros, (orders s : ℂ) / (z - s))
      ({z : ℂ | 0 < z.im} \ (Finset.image (fun s : ℍ => (s : ℂ)) zeros)) := by
  -- The function is analytic (hence continuous) at each point in the punctured set
  apply ContinuousOn.sub
  · -- logDeriv f is analytic away from zeros
    intro z ⟨hz_im, hz_not_zero⟩
    have hfz : modularFormCompOfComplex f z ≠ 0 := by
      intro hz0
      have : z ∈ Finset.image (fun s : ℍ => (s : ℂ)) zeros := hzeros_exhaust z hz_im hz0
      exact hz_not_zero this
    exact (analyticAt_logDeriv_off_zeros f z hz_im hfz).continuousAt.continuousWithinAt
  · -- The sum of poles is analytic away from zeros
    apply continuousOn_finset_sum
    intro s hs
    apply ContinuousOn.div continuousOn_const
    · exact (continuous_id.sub continuous_const).continuousOn
    · intro z ⟨_, hz_not_zero⟩
      -- z ∉ zeros.image means z ≠ s for all s ∈ zeros
      have h : z ≠ (s : ℂ) := by
        intro h_eq
        apply hz_not_zero
        simp only [Finset.coe_image, Set.mem_image]
        exact ⟨s, hs, h_eq.symm⟩
      exact sub_ne_zero.mpr h


/-! ## PV Decomposition -/

/-- fdBoundary equals fdBoundary_seg1 on [0, 1]. -/
lemma fdBoundary_eq_seg1_on (t : ℝ) (ht : t ∈ Icc 0 1) : fdBoundary t = fdBoundary_seg1 t := by
  simp only [fdBoundary, fdBoundary_seg1]
  have h1 : t ≤ 1 := ht.2
  simp only [h1, ↓reduceIte]

/-- fdBoundary equals fdBoundary_seg2 on (1, 2]. -/
lemma fdBoundary_eq_seg2_on (t : ℝ) (ht : t ∈ Ioc 1 2) : fdBoundary t = fdBoundary_seg2 t := by
  simp only [fdBoundary, fdBoundary_seg2]
  have h1 : ¬(t ≤ 1) := not_le.mpr ht.1
  have h2 : t ≤ 2 := ht.2
  simp only [h1, ↓reduceIte, h2]

/-- fdBoundary equals fdBoundary_seg3 on (2, 3]. -/
lemma fdBoundary_eq_seg3_on (t : ℝ) (ht : t ∈ Ioc 2 3) : fdBoundary t = fdBoundary_seg3 t := by
  simp only [fdBoundary, fdBoundary_seg3]
  have h1 : ¬(t ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 2) ht.1)
  have h2 : ¬(t ≤ 2) := not_le.mpr ht.1
  have h3 : t ≤ 3 := ht.2
  simp only [h1, ↓reduceIte, h2, h3]

/-- fdBoundary equals fdBoundary_seg4 on (3, 4]. -/
lemma fdBoundary_eq_seg4_on (t : ℝ) (ht : t ∈ Ioc 3 4) : fdBoundary t = fdBoundary_seg4 t := by
  simp only [fdBoundary, fdBoundary_seg4]
  have h1 : ¬(t ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 3) ht.1)
  have h2 : ¬(t ≤ 2) := not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 3) ht.1)
  have h3 : ¬(t ≤ 3) := not_le.mpr ht.1
  have h4 : t ≤ 4 := ht.2
  simp only [h1, ↓reduceIte, h2, h3, h4]

/-- fdBoundary equals fdBoundary_seg5 on (4, 5]. -/
lemma fdBoundary_eq_seg5_on (t : ℝ) (ht : t ∈ Ioc 4 5) : fdBoundary t = fdBoundary_seg5 t := by
  simp only [fdBoundary, fdBoundary_seg5]
  have h1 : ¬(t ≤ 1) := not_le.mpr (lt_trans (by norm_num : (1 : ℝ) < 4) ht.1)
  have h2 : ¬(t ≤ 2) := not_le.mpr (lt_trans (by norm_num : (2 : ℝ) < 4) ht.1)
  have h3 : ¬(t ≤ 3) := not_le.mpr (lt_trans (by norm_num : (3 : ℝ) < 4) ht.1)
  have h4 : ¬(t ≤ 4) := not_le.mpr ht.1
  simp only [h1, ↓reduceIte, h2, h3, h4]

/-- The PV integral decomposes additively over the five segments of ∂𝒟.

PV ∮_{∂𝒟} f'/f dz = PV ∫_{seg1} + PV ∫_{seg2} + ... + PV ∫_{seg5}

This is analogous to `intervalIntegral_pathJoin` but for PV integrals.

**PROOF STRUCTURE**:
1. Split ∫₀⁵ = ∫₀¹ + ∫₁² + ∫₂³ + ∫₃⁴ + ∫₄⁵ using intervalIntegral.integral_add_adjacent_intervals
2. On each interval [i, i+1], show that fdBoundary = fdBoundary_seg(i+1) a.e.
3. Use the helper lemmas `fdBoundary_eq_seg_i_on` to show values match
4. Show derivatives match a.e. (fdBoundary is piecewise affine/exponential)

The key observation is that fdBoundary is defined piecewise:
- On [0,1]: fdBoundary = fdBoundary_seg1
- On (1,2]: fdBoundary = fdBoundary_seg2
- etc.

The derivatives are equal a.e. since they differ only at the partition points {1, 2, 3, 4}.

**NOTE**: This proof requires integrability hypotheses for integral_add_adjacent_intervals.
For the valence formula, the integrand logDeriv(f) * γ' is integrable on each piece
since logDeriv is meromorphic with at most simple poles (at zeros of f) and γ is smooth.
-/
theorem pv_integral_decompose_segments
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5) :
    pv_integral f fdBoundary 0 5 =
      pv_integral f fdBoundary_seg1 0 1 +
      pv_integral f fdBoundary_seg2 1 2 +
      pv_integral f fdBoundary_seg3 2 3 +
      pv_integral f fdBoundary_seg4 3 4 +
      pv_integral f fdBoundary_seg5 4 5 := by
  -- Proof: split integral over [0,5] into segments using:
  -- 1. intervalIntegral.integral_add_adjacent_intervals (requires integrability)
  -- 2. fdBoundary_eq_segN_on to rewrite fdBoundary → segN on each interval
  -- 3. Matching derivatives on each interval
  simp only [pv_integral]
  -- Helper: derivative equality from function equality on neighborhood
  have deriv_eq_of_nhd_eq : ∀ {f g : ℝ → ℂ} {t : ℝ}, (∀ᶠ s in 𝓝 t, f s = g s) →
      deriv f t = deriv g t := fun {f g t} h => Filter.EventuallyEq.deriv_eq h
  -- Step 1: Show integrands match on each segment (a.e.)
  -- On (0,1), fdBoundary = fdBoundary_seg1 on a neighborhood of each point
  have h_integrand_seg1 : ∀ t ∈ Ioo (0:ℝ) 1,
      logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1 t) * deriv fdBoundary_seg1 t := by
    intro t ht
    have h_eq : fdBoundary t = fdBoundary_seg1 t := fdBoundary_eq_seg1_on t (Ioo_subset_Icc_self ht)
    rw [h_eq]
    congr 1
    -- Derivatives match because functions agree on neighborhood
    have h_nhd : ∀ᶠ s in 𝓝 t, fdBoundary s = fdBoundary_seg1 s := by
      have h_mem : Ioo (0:ℝ) 1 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [h_mem] with s hs
      exact fdBoundary_eq_seg1_on s (Ioo_subset_Icc_self hs)
    exact deriv_eq_of_nhd_eq h_nhd
  -- Similarly for other segments
  have h_integrand_seg2 : ∀ t ∈ Ioo (1:ℝ) 2,
      logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg2 t) * deriv fdBoundary_seg2 t := by
    intro t ht
    have h_eq : fdBoundary t = fdBoundary_seg2 t :=
      fdBoundary_eq_seg2_on t ⟨ht.1, le_of_lt ht.2⟩
    rw [h_eq]
    congr 1
    have h_nhd : ∀ᶠ s in 𝓝 t, fdBoundary s = fdBoundary_seg2 s := by
      have h_mem : Ioo (1:ℝ) 2 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [h_mem] with s hs
      exact fdBoundary_eq_seg2_on s ⟨hs.1, le_of_lt hs.2⟩
    exact deriv_eq_of_nhd_eq h_nhd
  have h_integrand_seg3 : ∀ t ∈ Ioo (2:ℝ) 3,
      logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg3 t) * deriv fdBoundary_seg3 t := by
    intro t ht
    have h_eq : fdBoundary t = fdBoundary_seg3 t :=
      fdBoundary_eq_seg3_on t ⟨ht.1, le_of_lt ht.2⟩
    rw [h_eq]
    congr 1
    have h_nhd : ∀ᶠ s in 𝓝 t, fdBoundary s = fdBoundary_seg3 s := by
      have h_mem : Ioo (2:ℝ) 3 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [h_mem] with s hs
      exact fdBoundary_eq_seg3_on s ⟨hs.1, le_of_lt hs.2⟩
    exact deriv_eq_of_nhd_eq h_nhd
  have h_integrand_seg4 : ∀ t ∈ Ioo (3:ℝ) 4,
      logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 t) * deriv fdBoundary_seg4 t := by
    intro t ht
    have h_eq : fdBoundary t = fdBoundary_seg4 t :=
      fdBoundary_eq_seg4_on t ⟨ht.1, le_of_lt ht.2⟩
    rw [h_eq]
    congr 1
    have h_nhd : ∀ᶠ s in 𝓝 t, fdBoundary s = fdBoundary_seg4 s := by
      have h_mem : Ioo (3:ℝ) 4 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [h_mem] with s hs
      exact fdBoundary_eq_seg4_on s ⟨hs.1, le_of_lt hs.2⟩
    exact deriv_eq_of_nhd_eq h_nhd
  have h_integrand_seg5 : ∀ t ∈ Ioo (4:ℝ) 5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5 t) * deriv fdBoundary_seg5 t := by
    intro t ht
    have h_eq : fdBoundary t = fdBoundary_seg5 t :=
      fdBoundary_eq_seg5_on t ⟨ht.1, le_of_lt ht.2⟩
    rw [h_eq]
    congr 1
    have h_nhd : ∀ᶠ s in 𝓝 t, fdBoundary s = fdBoundary_seg5 s := by
      have h_mem : Ioo (4:ℝ) 5 ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
      filter_upwards [h_mem] with s hs
      exact fdBoundary_eq_seg5_on s ⟨hs.1, le_of_lt hs.2⟩
    exact deriv_eq_of_nhd_eq h_nhd
  -- Step 2: Use integral_congr_ae to rewrite each segment integral
  -- The key is that the integrands match a.e. on each interval because they match on Ioo (measure-full)
  have h_int_seg1 : ∫ t in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      ∫ t in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1 t) * deriv fdBoundary_seg1 t := by
    apply intervalIntegral.integral_congr_ae
    -- Need to show equality a.e. on uIoc 0 1 = Ioc 0 1 = (0, 1]
    have h01 : (0:ℝ) ≤ 1 := by norm_num
    rw [Set.uIoc_of_le h01]
    -- Ioc 0 1 = (0, 1], need to exclude right endpoint 1 to get Ioo
    have hIoo_ae : ∀ᵐ (t : ℝ), t ∈ Ioc (0:ℝ) 1 → t ∈ Ioo (0:ℝ) 1 := by
      have h_meas : MeasureTheory.volume ({(1:ℝ)} : Set ℝ) = 0 := by simp
      filter_upwards [compl_mem_ae_iff.mpr h_meas] with t ht h_ioc
      exact ⟨h_ioc.1, lt_of_le_of_ne h_ioc.2 ht⟩
    filter_upwards [hIoo_ae] with t ht h_ioc
    exact h_integrand_seg1 t (ht h_ioc)
  have h_int_seg2 : ∫ t in (1:ℝ)..2, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      ∫ t in (1:ℝ)..2, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg2 t) * deriv fdBoundary_seg2 t := by
    apply intervalIntegral.integral_congr_ae
    have h12 : (1:ℝ) ≤ 2 := by norm_num
    rw [Set.uIoc_of_le h12]
    -- For Ioc, left endpoint is excluded, right is included
    -- Ioc 1 2 = {t | 1 < t ≤ 2}, so Ioc ⊆ Ioo except for right endpoint (measure 0)
    have hIoo_ae : ∀ᵐ (t : ℝ), t ∈ Ioc (1:ℝ) 2 → t ∈ Ioo (1:ℝ) 2 := by
      have h_meas : MeasureTheory.volume ({(2:ℝ)} : Set ℝ) = 0 := by simp
      filter_upwards [compl_mem_ae_iff.mpr h_meas] with t ht h_ioc
      exact ⟨h_ioc.1, lt_of_le_of_ne h_ioc.2 ht⟩
    filter_upwards [hIoo_ae] with t ht h_ioc
    exact h_integrand_seg2 t (ht h_ioc)
  have h_int_seg3 : ∫ t in (2:ℝ)..3, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      ∫ t in (2:ℝ)..3, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg3 t) * deriv fdBoundary_seg3 t := by
    apply intervalIntegral.integral_congr_ae
    have h23 : (2:ℝ) ≤ 3 := by norm_num
    rw [Set.uIoc_of_le h23]
    have hIoo_ae : ∀ᵐ (t : ℝ), t ∈ Ioc (2:ℝ) 3 → t ∈ Ioo (2:ℝ) 3 := by
      have h_meas : MeasureTheory.volume ({(3:ℝ)} : Set ℝ) = 0 := by simp
      filter_upwards [compl_mem_ae_iff.mpr h_meas] with t ht h_ioc
      exact ⟨h_ioc.1, lt_of_le_of_ne h_ioc.2 ht⟩
    filter_upwards [hIoo_ae] with t ht h_ioc
    exact h_integrand_seg3 t (ht h_ioc)
  have h_int_seg4 : ∫ t in (3:ℝ)..4, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      ∫ t in (3:ℝ)..4, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 t) * deriv fdBoundary_seg4 t := by
    apply intervalIntegral.integral_congr_ae
    have h34 : (3:ℝ) ≤ 4 := by norm_num
    rw [Set.uIoc_of_le h34]
    have hIoo_ae : ∀ᵐ (t : ℝ), t ∈ Ioc (3:ℝ) 4 → t ∈ Ioo (3:ℝ) 4 := by
      have h_meas : MeasureTheory.volume ({(4:ℝ)} : Set ℝ) = 0 := by simp
      filter_upwards [compl_mem_ae_iff.mpr h_meas] with t ht h_ioc
      exact ⟨h_ioc.1, lt_of_le_of_ne h_ioc.2 ht⟩
    filter_upwards [hIoo_ae] with t ht h_ioc
    exact h_integrand_seg4 t (ht h_ioc)
  have h_int_seg5 : ∫ t in (4:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t =
      ∫ t in (4:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5 t) * deriv fdBoundary_seg5 t := by
    apply intervalIntegral.integral_congr_ae
    have h45 : (4:ℝ) ≤ 5 := by norm_num
    rw [Set.uIoc_of_le h45]
    have hIoo_ae : ∀ᵐ (t : ℝ), t ∈ Ioc (4:ℝ) 5 → t ∈ Ioo (4:ℝ) 5 := by
      have h_meas : MeasureTheory.volume ({(5:ℝ)} : Set ℝ) = 0 := by simp
      filter_upwards [compl_mem_ae_iff.mpr h_meas] with t ht h_ioc
      exact ⟨h_ioc.1, lt_of_le_of_ne h_ioc.2 ht⟩
    filter_upwards [hIoo_ae] with t ht h_ioc
    exact h_integrand_seg5 t (ht h_ioc)
  -- Step 4: Split the integral [0,5] into [0,1] + [1,2] + [2,3] + [3,4] + [4,5]
  -- We need integrability on each piece. For modular forms, logDeriv is meromorphic
  -- with at most simple poles, and the path is piecewise smooth, so integrability holds.
  -- For now, we assert integrability and focus on the structural argument.
  have hint_01 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 0 1 := hint.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num))
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num)))
  have hint_12 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 1 2 := hint.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num))
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num)))
  have hint_23 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 2 3 := hint.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num))
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num)))
  have hint_34 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 3 4 := hint.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num))
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num)))
  have hint_45 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 4 5 := hint.mono_set (Set.uIcc_subset_uIcc
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num))
        (Set.mem_uIcc_of_le (by norm_num) (by norm_num)))
  -- Combine integrabilities
  have hint_15 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 1 5 := by
    apply IntervalIntegrable.trans hint_12
    apply IntervalIntegrable.trans hint_23
    apply IntervalIntegrable.trans hint_34
    exact hint_45
  have hint_25 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 2 5 := by
    apply IntervalIntegrable.trans hint_23
    apply IntervalIntegrable.trans hint_34
    exact hint_45
  have hint_35 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)
      MeasureTheory.volume 3 5 := by
    apply IntervalIntegrable.trans hint_34
    exact hint_45
  -- Now split the integral
  calc ∫ t in (0:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t
      = (∫ t in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
        (∫ t in (1:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) := by
          symm; exact intervalIntegral.integral_add_adjacent_intervals hint_01 hint_15
      _ = (∫ t in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
          ((∫ t in (1:ℝ)..2, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
           (∫ t in (2:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)) := by
          congr 1
          symm; exact intervalIntegral.integral_add_adjacent_intervals hint_12 hint_25
      _ = (∫ t in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
          ((∫ t in (1:ℝ)..2, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
           ((∫ t in (2:ℝ)..3, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
            (∫ t in (3:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t))) := by
          congr 2
          symm; exact intervalIntegral.integral_add_adjacent_intervals hint_23 hint_35
      _ = (∫ t in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
          ((∫ t in (1:ℝ)..2, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
           ((∫ t in (2:ℝ)..3, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
            ((∫ t in (3:ℝ)..4, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t) +
             (∫ t in (4:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary t) * deriv fdBoundary t)))) := by
          congr 3
          symm; exact intervalIntegral.integral_add_adjacent_intervals hint_34 hint_45
      _ = (∫ t in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1 t) * deriv fdBoundary_seg1 t) +
          ((∫ t in (1:ℝ)..2, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg2 t) * deriv fdBoundary_seg2 t) +
           ((∫ t in (2:ℝ)..3, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg3 t) * deriv fdBoundary_seg3 t) +
            ((∫ t in (3:ℝ)..4, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 t) * deriv fdBoundary_seg4 t) +
             (∫ t in (4:ℝ)..5, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5 t) * deriv fdBoundary_seg5 t)))) := by
          rw [h_int_seg1, h_int_seg2, h_int_seg3, h_int_seg4, h_int_seg5]
      _ = _ := by ring

/-! ## Vertical Edge Cancellation -/

/-- Key relationship: seg4(4-s) = seg1(s) - 1 for s ∈ [0, 1].
    This is the T-translate relationship between the vertical edges. -/
lemma seg4_eq_seg1_minus_one (s : ℝ) (_hs : s ∈ Icc 0 1) :
    fdBoundary_seg4 (4 - s) = fdBoundary_seg1 s - 1 := by
  -- The proof is a direct computation.
  -- seg4(4-s) = -1/2 + (√3/2 + (1-s)*(H - √3/2))*I
  -- seg1(s) - 1 = 1/2 + (H - s*(H - √3/2))*I - 1 = -1/2 + (H - s*(H - √3/2))*I
  -- Key: √3/2 + (1-s)*(H - √3/2) = √3/2 + H - √3/2 - s*(H - √3/2) = H - s*(H - √3/2)
  simp only [fdBoundary_seg4, fdBoundary_seg1]
  -- Simplify the expression ↑(4-s) - 3 to ↑(1-s) in ℂ
  have h1 : ((4 - s : ℝ) : ℂ) - 3 = ((1 - s : ℝ) : ℂ) := by
    push_cast; ring
  simp only [h1]
  -- Now the goal is: -1/2 + (√3/2 + (1-s)*(H-√3/2))*I = 1/2 + (H - s*(H-√3/2))*I - 1
  -- Algebraic identity: √3/2 + (1-s)*(H-√3/2) = H - s*(H-√3/2)
  have h2 : (Real.sqrt 3 / 2 : ℂ) + ((1 - s : ℝ) : ℂ) * ((H_height : ℂ) - Real.sqrt 3 / 2)
          = (H_height : ℂ) - (s : ℂ) * ((H_height : ℂ) - Real.sqrt 3 / 2) := by
    push_cast; ring
  simp only [h2]
  -- Now both sides have the same imaginary coefficient
  -- LHS: -1/2 + (H - s*(H-√3/2))*I
  -- RHS: 1/2 + (H - s*(H-√3/2))*I - 1 = -1/2 + (H - s*(H-√3/2))*I
  ring

/-- The derivative of seg1: d/dt seg1(t) = -(H - √3/2) * I

This is a straightforward calculation: seg1(t) = 1/2 + (H - t*(H - √3/2))*I is affine in t,
so its derivative is the coefficient of t, which is -(H - √3/2)*I. -/
lemma deriv_fdBoundary_seg1 (t : ℝ) :
    deriv fdBoundary_seg1 t = -((H_height : ℂ) - Real.sqrt 3 / 2) * I := by
  -- seg1(t) = const₁ + const₂ * t where const₂ = -(H - √3/2) * I
  -- Rewrite seg1 as an affine function
  have h_eq : fdBoundary_seg1 = fun (t : ℝ) => (1/2 : ℂ) + H_height * I +
      (-(H_height - Real.sqrt 3 / 2) * I) * (t : ℂ) := by
    ext t
    simp only [fdBoundary_seg1]
    ring
  rw [h_eq]
  -- Now compute derivative of a + b * t
  have h : HasDerivAt (fun (t : ℝ) => (1/2 : ℂ) + H_height * I +
      (-(H_height - Real.sqrt 3 / 2) * I) * (t : ℂ)) (-(H_height - Real.sqrt 3 / 2) * I) t := by
    have h1 : HasDerivAt (fun (t : ℝ) => (1/2 : ℂ) + H_height * I) 0 t :=
      hasDerivAt_const t _
    have h2 : HasDerivAt (fun (t : ℝ) => (-(H_height - Real.sqrt 3 / 2) * I) * (t : ℂ))
        (-(H_height - Real.sqrt 3 / 2) * I) t := by
      -- Use: derivative of (t : ℂ) is 1, then multiply by constant
      have h_id : HasDerivAt (fun (t : ℝ) => (t : ℂ)) 1 t := by
        have := (hasDerivAt_id t).ofReal_comp
        simp only [Complex.ofReal_one] at this
        exact this
      have h_mul : HasDerivAt (fun (t : ℝ) => (-(H_height - Real.sqrt 3 / 2) * I) * (t : ℂ))
          ((-(H_height - Real.sqrt 3 / 2) * I) * 1) t := h_id.const_mul _
      simp only [mul_one] at h_mul
      exact h_mul
    convert h1.add h2 using 1
    ring
  exact h.deriv

/-- The derivative of seg4: d/dt seg4(t) = (H - √3/2) * I

This is a straightforward calculation: seg4(t) = -1/2 + (√3/2 + (t-3)*(H - √3/2))*I is affine in t,
so its derivative is the coefficient of t, which is (H - √3/2)*I. -/
lemma deriv_fdBoundary_seg4 (t : ℝ) :
    deriv fdBoundary_seg4 t = ((H_height : ℂ) - Real.sqrt 3 / 2) * I := by
  -- seg4(t) = const₁ + const₂ * t where const₂ = (H - √3/2) * I
  have h_eq : fdBoundary_seg4 = fun (t : ℝ) => (-1/2 : ℂ) + (Real.sqrt 3 / 2 - 3 * (H_height - Real.sqrt 3 / 2)) * I +
      ((H_height - Real.sqrt 3 / 2) * I) * (t : ℂ) := by
    ext t
    simp only [fdBoundary_seg4]
    ring
  rw [h_eq]
  -- Now compute derivative of a + b * t
  have h : HasDerivAt (fun (t : ℝ) => (-1/2 : ℂ) + (Real.sqrt 3 / 2 - 3 * (H_height - Real.sqrt 3 / 2)) * I +
      ((H_height - Real.sqrt 3 / 2) * I) * (t : ℂ)) ((H_height - Real.sqrt 3 / 2) * I) t := by
    have h1 : HasDerivAt (fun (t : ℝ) => (-1/2 : ℂ) + (Real.sqrt 3 / 2 - 3 * (H_height - Real.sqrt 3 / 2)) * I) 0 t :=
      hasDerivAt_const t _
    have h2 : HasDerivAt (fun (t : ℝ) => ((H_height - Real.sqrt 3 / 2) * I) * (t : ℂ))
        ((H_height - Real.sqrt 3 / 2) * I) t := by
      -- Use: derivative of (t : ℂ) is 1, then multiply by constant
      have h_id : HasDerivAt (fun (t : ℝ) => (t : ℂ)) 1 t := by
        have := (hasDerivAt_id t).ofReal_comp
        simp only [Complex.ofReal_one] at this
        exact this
      have h_mul : HasDerivAt (fun (t : ℝ) => ((H_height - Real.sqrt 3 / 2) * I) * (t : ℂ))
          (((H_height - Real.sqrt 3 / 2) * I) * 1) t := h_id.const_mul _
      simp only [mul_one] at h_mul
      exact h_mul
    convert h1.add h2 using 1
    ring
  exact h.deriv

/-- Key relation: seg4'(4-s) = -seg1'(s) -/
lemma deriv_seg4_at_complement_eq_neg_deriv_seg1 (s : ℝ) :
    deriv fdBoundary_seg4 (4 - s) = -deriv fdBoundary_seg1 s := by
  rw [deriv_fdBoundary_seg4, deriv_fdBoundary_seg1]
  ring

/-- logDeriv is periodic with period 1 when f is periodic with period 1.
    Uses the fact that f(z+1) = f(z) implies deriv f(z+1) = deriv f(z). -/
lemma logDeriv_periodic_of_periodic {F : ℂ → ℂ} (hF : Function.Periodic F (1 : ℂ)) :
    Function.Periodic (logDeriv F) (1 : ℂ) := by
  intro z
  -- Need: logDeriv F (z + 1) = logDeriv F z
  -- which is: deriv F (z + 1) / F (z + 1) = deriv F z / F z
  -- By periodicity: F (z + 1) = F z
  have h_val : F (z + 1) = F z := hF z
  -- By periodicity: deriv F (z + 1) = deriv F z
  -- This follows because F(w + 1) = F(w) for all w
  have h_deriv : deriv F (z + 1) = deriv F z := by
    have h_eq_on_nhds : F =ᶠ[𝓝 z] (fun w => F (w + 1)) := by
      rw [Filter.eventuallyEq_iff_exists_mem]
      use Set.univ
      constructor
      · exact Filter.univ_mem
      · intro w _
        exact (hF w).symm
    have h := h_eq_on_nhds.deriv_eq
    rw [h, deriv_comp_add_const]
  -- Now rewrite using the equality of values and derivatives
  -- logDeriv F (z + 1) = deriv F (z + 1) / F (z + 1) = deriv F z / F z = logDeriv F z
  unfold logDeriv
  simp only [Pi.div_apply, h_val, h_deriv]

/-- The vertical edge integrals cancel by T-invariance.

By the transformation law f(z+1) = f(z), we have:
  ∫_{seg1} f'/f dz + ∫_{seg4} f'/f dz = 0

where seg1 is the right vertical edge (x = 1/2, downward) and
seg4 is the left vertical edge (x = -1/2, upward).

**Proof strategy**:
1. seg1 goes from (1/2 + Hi) down to ρ' = (1/2 + √3/2·i)
2. seg4 goes from ρ = (-1/2 + √3/2·i) up to (-1/2 + Hi)
3. Change variables t → 4-t in seg4 integral
4. Use seg4(4-s) = seg1(s) - 1 (by seg4_eq_seg1_minus_one)
5. By T-invariance: logDeriv(f)(seg1(s) - 1) = logDeriv(f)(seg1(s))
6. Use deriv_seg4_at_complement_eq_neg_deriv_seg1: the derivatives differ by a sign
7. Conclude ∫_{seg4} = -∫_{seg1}, so they cancel -/
theorem pv_integral_vertical_cancel :
    pv_integral f fdBoundary_seg1 0 1 + pv_integral f fdBoundary_seg4 3 4 = 0 := by
  -- The proof uses T-invariance: f(z+1) = f(z)
  -- First establish the periodicity
  have h_periodic : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
    simp only [Nat.cast_one] at this
    exact this

  -- logDeriv is also periodic
  have h_logDeriv_periodic : Function.Periodic (logDeriv (modularFormCompOfComplex f)) (1 : ℂ) :=
    logDeriv_periodic_of_periodic h_periodic

  -- Unfold pv_integral
  simp only [pv_integral]

  -- Step 1: Rewrite seg4 integral using substitution t ↦ 4 - t
  -- Using: ∫ u in 0..1, g(4 - u) = ∫ t in 3..4, g(t)  (by integral_comp_sub_left)
  have h_sub : ∫ t in (3:ℝ)..4, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 t) *
      deriv fdBoundary_seg4 t =
    ∫ u in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 (4 - u)) *
      deriv fdBoundary_seg4 (4 - u) := by
    -- The lemma says: ∫ u in a..b, f (d - u) = ∫ t in d - b..d - a, f t
    -- With a=0, b=1, d=4: ∫ u in 0..1, f(4-u) = ∫ t in 3..4, f(t)
    have hsub := @intervalIntegral.integral_comp_sub_left ℂ _ _ (0:ℝ) (1:ℝ)
      (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 t) *
        deriv fdBoundary_seg4 t) (4 : ℝ)
    simp only [sub_zero, show (4:ℝ) - 1 = 3 by norm_num] at hsub
    exact hsub.symm

  -- Step 2: Rewrite using our lemmas
  -- seg4(4-u) = seg1(u) - 1 and deriv(seg4)(4-u) = -deriv(seg1)(u)
  have h_integrand : ∀ u ∈ Icc (0:ℝ) 1,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 (4 - u)) *
        deriv fdBoundary_seg4 (4 - u) =
      -(logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1 u) *
        deriv fdBoundary_seg1 u) := by
    intro u hu
    -- Use seg4(4-u) = seg1(u) - 1
    have h_seg : fdBoundary_seg4 (4 - u) = fdBoundary_seg1 u - 1 := seg4_eq_seg1_minus_one u hu
    -- Use periodicity: logDeriv(f)(z - 1) = logDeriv(f)(z)
    have h_per : logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1 u - 1) =
        logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1 u) := by
      have := h_logDeriv_periodic (fdBoundary_seg1 u - 1)
      simp only [sub_add_cancel] at this
      exact this.symm
    -- Use deriv(seg4)(4-u) = -deriv(seg1)(u)
    have h_deriv : deriv fdBoundary_seg4 (4 - u) = -deriv fdBoundary_seg1 u :=
      deriv_seg4_at_complement_eq_neg_deriv_seg1 u
    rw [h_seg, h_per, h_deriv]
    ring

  -- Step 3: Conclude
  rw [h_sub]
  -- Apply the integrand equality
  have h_eq : ∫ u in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4 (4 - u)) *
      deriv fdBoundary_seg4 (4 - u) =
    ∫ u in (0:ℝ)..1, -(logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1 u) *
        deriv fdBoundary_seg1 u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    -- uIcc 0 1 = Icc 0 1 when 0 ≤ 1
    have hu' : u ∈ Icc (0:ℝ) 1 := by
      simp only [Set.uIcc, Set.mem_Icc, min_eq_left (by norm_num : (0:ℝ) ≤ 1),
        max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hu
      exact hu
    exact h_integrand u hu'
  rw [h_eq]
  -- ∫ -f = -∫ f
  rw [intervalIntegral.integral_neg]
  ring

/-! ## Arc Contribution -/

/-! ### Helper Lemmas for Arc Computation

These lemmas compute specific properties of the arc segments needed for the
arc contribution theorem. The arc segments are parametrizations of the unit
circle arc from ρ' = e^{iπ/3} through i to ρ = e^{i2π/3}. -/

/-- The arc segments are on the unit circle: ‖seg2(t)‖ = 1 for all t.
    seg2(t) = exp(i*θ(t)) where θ(t) ∈ [π/3, π/2], so ‖seg2(t)‖ = 1.

Proof: By definition, `fdBoundary_seg2 t = exp((π/3 + (t-1)*(π/6))*I)`.
Using `norm_exp_ofReal_mul_I`: ‖exp(x*I)‖ = 1 for any real x.
The argument of exp is real times I, so the norm equals 1. -/
lemma norm_fdBoundary_seg2_eq_one (t : ℝ) :
    ‖fdBoundary_seg2 t‖ = 1 := by
  unfold fdBoundary_seg2
  rw [show (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3) : ℂ) * I =
    ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The arc segments are on the unit circle: ‖seg3(t)‖ = 1 for all t.
    seg3(t) = exp(i*θ(t)) where θ(t) ∈ [π/2, 2π/3], so ‖seg3(t)‖ = 1.

Proof: Similar to norm_fdBoundary_seg2_eq_one. -/
lemma norm_fdBoundary_seg3_eq_one (t : ℝ) :
    ‖fdBoundary_seg3 t‖ = 1 := by
  unfold fdBoundary_seg3
  rw [show (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) : ℂ) * I =
    ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Derivative of seg2: deriv(seg2)(t) = (π/6) * I * seg2(t).

The arc segment seg2 traces exp(i*θ(t)) where θ(t) = π/3 + (t-1)*(π/6).
Since d/dt[exp(i*θ)] = i*θ'*exp(i*θ) and θ' = π/6, we get
deriv(seg2)(t) = (π/6)*I*seg2(t). -/
lemma deriv_fdBoundary_seg2_arc_eq (t : ℝ) :
    deriv fdBoundary_seg2 t = (Real.pi / 6) * I * fdBoundary_seg2 t := by
  unfold fdBoundary_seg2
  have hfun_eq : (fun t : ℝ => cexp ((↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)) =
      (fun t : ℝ => cexp (↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)) := by
    ext t; congr 1; push_cast; ring
  rw [hfun_eq]
  have hd : HasDerivAt (fun t : ℝ => (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)))
      (Real.pi / 2 - Real.pi / 3) t := by
    have : HasDerivAt (fun t => t * (Real.pi / 2 - Real.pi / 3) + (Real.pi / 3 - (Real.pi / 2 - Real.pi / 3)))
        (1 * (Real.pi / 2 - Real.pi / 3)) t :=
      (hasDerivAt_id t).mul_const _ |>.add_const _
    convert this using 1 <;> ring
  exact ((hd.ofReal_comp.mul_const I).cexp.deriv ▸ by push_cast; ring)

/-- Derivative of seg3: deriv(seg3)(t) = (π/6) * I * seg3(t).

The arc segment seg3 traces exp(i*θ(t)) where θ(t) = π/2 + (t-2)*(π/6).
Since d/dt[exp(i*θ)] = i*θ'*exp(i*θ) and θ' = π/6, we get
deriv(seg3)(t) = (π/6)*I*seg3(t). -/
lemma deriv_fdBoundary_seg3_arc_eq (t : ℝ) :
    deriv fdBoundary_seg3 t = (Real.pi / 6) * I * fdBoundary_seg3 t := by
  unfold fdBoundary_seg3
  have hfun_eq : (fun t : ℝ => cexp ((↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)) =
      (fun t : ℝ => cexp (↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)) := by
    ext t; congr 1; push_cast; ring
  rw [hfun_eq]
  have hd : HasDerivAt (fun t : ℝ => (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)))
      (2 * Real.pi / 3 - Real.pi / 2) t := by
    have : HasDerivAt (fun t => t * (2 * Real.pi / 3 - Real.pi / 2) + (Real.pi / 2 - 2 * (2 * Real.pi / 3 - Real.pi / 2)))
        (1 * (2 * Real.pi / 3 - Real.pi / 2)) t :=
      (hasDerivAt_id t).mul_const _ |>.add_const _
    convert this using 1 <;> ring
  exact ((hd.ofReal_comp.mul_const I).cexp.deriv ▸ by push_cast; ring)

/-- The combined arc integral of 1/z gives i*π/3.

On the unit circle arc from angle π/3 to 2π/3:
∫ (1/z) dz = ∫ (1/e^{iθ}) * i*e^{iθ} dθ = ∫ i dθ = i*(2π/3 - π/3) = i*π/3

The integrand simplifies: z⁻¹ * deriv(z) = (π/6)*I (constant).
Integrating over [1,2] and [2,3] each gives (π/6)*I, totaling (π/3)*I.

**Proof structure:**
1. Use deriv_fdBoundary_seg2_arc_eq and deriv_fdBoundary_seg3_arc_eq
2. Show z⁻¹ * (π/6)*I*z = (π/6)*I for nonzero z
3. Integrate constant (π/6)*I over intervals of length 1
4. Sum: (π/6)*I + (π/6)*I = (π/3)*I -/
lemma arc_integral_one_over_z :
    ∫ t in (1:ℝ)..2, (fdBoundary_seg2 t)⁻¹ * deriv fdBoundary_seg2 t +
    ∫ t in (2:ℝ)..3, (fdBoundary_seg3 t)⁻¹ * deriv fdBoundary_seg3 t =
      I * Real.pi / 3 := by
  have h2 : ∀ t : ℝ, (fdBoundary_seg2 t)⁻¹ * deriv fdBoundary_seg2 t = ↑(Real.pi / 6) * I := by
    intro t; rw [deriv_fdBoundary_seg2_arc_eq]
    have hne : fdBoundary_seg2 t ≠ 0 := by unfold fdBoundary_seg2; exact exp_ne_zero _
    field_simp; push_cast; ring
  have h3 : ∀ t : ℝ, (fdBoundary_seg3 t)⁻¹ * deriv fdBoundary_seg3 t = ↑(Real.pi / 6) * I := by
    intro t; rw [deriv_fdBoundary_seg3_arc_eq]
    have hne : fdBoundary_seg3 t ≠ 0 := by unfold fdBoundary_seg3; exact exp_ne_zero _
    field_simp; push_cast; ring
  simp_rw [h2, h3]
  simp [intervalIntegral.integral_const]
  ring

/-- The modular form S-transformation identity on ℂ.

For z with z.im > 0, the modular identity f(S·z) = z^k · f(z) translates to:
  (f ∘ ofComplex)(-1/z) = z^k · (f ∘ ofComplex)(z)

This follows from `slash_action_eqn_SL''` with γ = S ∈ Γ(1). -/
lemma modform_comp_ofComplex_S_identity (z : ℂ) (hz : 0 < z.im) :
    f (UpperHalfPlane.ofComplex (-(1:ℂ)/z)) =
      (z : ℂ) ^ k * f (UpperHalfPlane.ofComplex z) := by
  have hz_ne : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have h_neg_inv_im : 0 < (-(1:ℂ)/z).im := by
    rw [show -(1:ℂ)/z = (-z)⁻¹ from by field_simp]
    rw [Complex.inv_im]; apply div_pos
    · simp [hz]
    · exact Complex.normSq_pos.mpr (neg_ne_zero.mpr hz_ne)
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos h_neg_inv_im]
  let z_uhp : UpperHalfPlane := ⟨z, hz⟩
  have h_eq : (⟨-(1:ℂ)/z, h_neg_inv_im⟩ : UpperHalfPlane) = ModularGroup.S • z_uhp := by
    apply Subtype.ext
    have h1 := UpperHalfPlane.modular_S_smul z_uhp
    show -(1:ℂ)/z = ↑(ModularGroup.S • z_uhp)
    rw [h1]; simp only [UpperHalfPlane.coe_mk]
    show -(1:ℂ)/z = (-z)⁻¹; field_simp
  rw [h_eq]
  have hS : ModularGroup.S ∈ Gamma 1 := by
    rw [CongruenceSubgroup.Gamma_one_top]; exact Subgroup.mem_top _
  have h := SlashInvariantForm.slash_action_eqn_SL'' f hS z_uhp
  rw [ModularGroup.denom_S] at h; exact h

/-- S-action on seg2: S(seg2(t)) = seg3(4-t) where S(z) = -1/z.

On the unit circle e^{iθ}, S maps e^{iθ} to e^{i(π-θ)}, which reverses
the arc direction. Concretely, the angle θ₂(t) = π/3 + (t-1)·π/6 maps to
π - θ₂(t) = π/2 + (2-t)·π/6 = angle of seg3(4-t). -/
lemma S_action_seg2_eq_seg3_rev (t : ℝ) :
    -(1:ℂ) / fdBoundary_seg2 t = fdBoundary_seg3 (4 - t) := by
  unfold fdBoundary_seg2 fdBoundary_seg3
  rw [show (↑Real.pi / 2 + (↑(4 - t) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      (↑(Real.pi - (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)))) * I by push_cast; ring]
  rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      (↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) * I by push_cast; ring]
  rw [show ↑(Real.pi - (Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) * I =
      ↑Real.pi * I - ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I by push_cast; ring]
  rw [exp_sub, show exp (↑Real.pi * I) = -1 from by rw [exp_mul_I]; simp]

/-- S-action on seg3: S(seg3(t)) = seg2(4-t) where S(z) = -1/z.

Symmetric to `S_action_seg2_eq_seg3_rev`: the angle θ₃(t) = π/2 + (t-2)·π/6
maps to π - θ₃(t) = π/3 + (3-t)·π/6 = angle of seg2(4-t). -/
lemma S_action_seg3_eq_seg2_rev (t : ℝ) :
    -(1:ℂ) / fdBoundary_seg3 t = fdBoundary_seg2 (4 - t) := by
  unfold fdBoundary_seg2 fdBoundary_seg3
  rw [show (↑Real.pi / 3 + (↑(4 - t) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      (↑(Real.pi - (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)))) * I by push_cast; ring]
  rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      (↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) * I by push_cast; ring]
  rw [show ↑(Real.pi - (Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) * I =
      ↑Real.pi * I - ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I by push_cast; ring]
  rw [exp_sub, show exp (↑Real.pi * I) = -1 from by rw [exp_mul_I]; simp]

/-- Reversing a curve parameterization via t → d-t negates the contour integral.

For any `h : ℂ → ℂ` and differentiable curve `γ`:
  `∫_a^b h(γ(d-t)) * d/dt[γ(d-t)] dt = -(∫_{d-b}^{d-a} h(γ(t)) * γ'(t) dt)`

The proof uses the chain rule `d/dt[γ(d-t)] = -γ'(d-t)` and the substitution u = d-t. -/
lemma integral_curve_reverse (h : ℂ → ℂ) (γ : ℝ → ℂ) (a b d : ℝ)
    (hγ : ∀ t, DifferentiableAt ℝ γ (d - t)) :
    ∫ t in a..b, h (γ (d - t)) * deriv (fun s => γ (d - s)) t =
    -(∫ t in (d-b)..(d-a), h (γ t) * deriv γ t) := by
  have h_deriv : ∀ t, deriv (fun s => γ (d - s)) t = -(deriv γ (d - t)) := by
    intro t
    have h_sub : HasDerivAt (fun s : ℝ => d - s) ((-1 : ℝ)) t := by
      convert (hasDerivAt_const t d).sub (hasDerivAt_id t) using 1; ring
    have h_comp := (hγ t).hasDerivAt.scomp t h_sub
    have h_eq : (fun s => γ (d - s)) = (γ ∘ HSub.hSub d) := rfl
    rw [h_eq, h_comp.deriv]; simp [neg_smul, one_smul]
  simp_rw [h_deriv, mul_neg]
  rw [intervalIntegral.integral_neg]
  congr 1
  convert intervalIntegral.integral_comp_sub_left (fun t => h (γ t) * deriv γ t) d using 1

/-- The S-transformation reverses the arc integral.

Since S(seg2(t)) = seg3(4-t) and S(seg3(t)) = seg2(4-t), composing with S and
integrating along the original parameter range gives the negative of the original
arc integral. This uses `integral_curve_reverse` for the change of variables. -/
lemma arc_integral_S_reversal :
    pv_integral f (fun t => -(1:ℂ) / fdBoundary_seg2 t) 1 2 +
    pv_integral f (fun t => -(1:ℂ) / fdBoundary_seg3 t) 2 3 =
    -(pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3) := by
  -- Replace S ∘ seg_i with seg_j ∘ (4 - ·)
  have h_eq2 : (fun t => -(1:ℂ) / fdBoundary_seg2 t) = (fun t => fdBoundary_seg3 (4 - t)) :=
    funext S_action_seg2_eq_seg3_rev
  have h_eq3 : (fun t => -(1:ℂ) / fdBoundary_seg3 t) = (fun t => fdBoundary_seg2 (4 - t)) :=
    funext S_action_seg3_eq_seg2_rev
  rw [h_eq2, h_eq3]
  -- Apply curve reversal to each term
  have h_rev3 : pv_integral f (fun t => fdBoundary_seg3 (4 - t)) 1 2 =
      -(pv_integral f fdBoundary_seg3 2 3) := by
    unfold pv_integral
    have h := integral_curve_reverse (logDeriv (modularFormCompOfComplex f)) fdBoundary_seg3 1 2 4
      (fun t => by
        apply DifferentiableAt.cexp
        apply DifferentiableAt.mul_const
        exact (DifferentiableAt.add (differentiableAt_const _)
          ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _))))
    convert h using 2 <;> norm_num
  have h_rev2 : pv_integral f (fun t => fdBoundary_seg2 (4 - t)) 2 3 =
      -(pv_integral f fdBoundary_seg2 1 2) := by
    unfold pv_integral
    have h := integral_curve_reverse (logDeriv (modularFormCompOfComplex f)) fdBoundary_seg2 2 3 4
      (fun t => by
        apply DifferentiableAt.cexp
        apply DifferentiableAt.mul_const
        exact (DifferentiableAt.add (differentiableAt_const _)
          ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _))))
    convert h using 2 <;> norm_num
  rw [h_rev3, h_rev2]; ring

/-- If two functions agree in a neighborhood, they have the same logDeriv.

This follows from `Filter.EventuallyEq.deriv` and the fact that locally-equal
functions have the same value. -/
lemma logDeriv_congr_of_eventuallyEq {f₁ f₂ : ℂ → ℂ} {z : ℂ}
    (h : f₁ =ᶠ[𝓝 z] f₂) : logDeriv f₁ z = logDeriv f₂ z := by
  simp only [logDeriv_apply]
  have h_val : f₁ z = f₂ z := h.eq_of_nhds
  have h_deriv : deriv f₁ z = deriv f₂ z := h.deriv.eq_of_nhds
  rw [h_val, h_deriv]

/-- The S-transformation of the modular form gives a pointwise logDeriv identity.

From `g(-1/z) = z^k * g(z)` (modular identity), differentiating and dividing gives:
  `logDeriv(g)(-1/z) * (1/z^2) = k/z + logDeriv(g)(z)`
Rearranging:
  `logDeriv(g)(z) = logDeriv(g)(-1/z) / z^2 - k/z`

**Proof**: Take logDeriv of both sides of the identity `(g ∘ S) =ᶠ (·^k * g ·)`,
using `logDeriv_comp`, `logDeriv_mul`, and `logDeriv_zpow`. -/
lemma logDeriv_modform_S_transform (z : ℂ) (hz : 0 < z.im) (hz_ne : z ≠ 0)
    (hgz : modularFormCompOfComplex f z ≠ 0) :
    logDeriv (modularFormCompOfComplex f) z =
    logDeriv (modularFormCompOfComplex f) (-(1:ℂ)/z) / z ^ 2 - ↑k / z := by
  set g := modularFormCompOfComplex f with hg_def
  -- Step 1: The modular identity g(-1/z) = z^k * g(z) holds in a neighborhood of z
  have h_uhp_open : IsOpen {w : ℂ | 0 < w.im} := UpperHalfPlane.isOpen_upperHalfPlaneSet
  have h_nhd_uhp : {w : ℂ | 0 < w.im} ∈ 𝓝 z := h_uhp_open.mem_nhds hz
  have h_eq_nhd : (fun w => g (-(1:ℂ)/w)) =ᶠ[𝓝 z] (fun w => w ^ k * g w) := by
    filter_upwards [h_nhd_uhp] with w hw
    exact modform_comp_ofComplex_S_identity f w hw
  -- Step 2: logDeriv of (g ∘ S) using logDeriv_comp
  have h_neg_inv_im : 0 < (-(1:ℂ)/z).im := by
    rw [show -(1:ℂ)/z = (-z)⁻¹ from by field_simp]
    rw [Complex.inv_im]; apply div_pos
    · simp [hz]
    · exact Complex.normSq_pos.mpr (neg_ne_zero.mpr hz_ne)
  have h_diffOn_g : DifferentiableOn ℂ g {w | 0 < w.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  have h_diff_g_at_Sz : DifferentiableAt ℂ g (-(1:ℂ)/z) :=
    h_diffOn_g.differentiableAt (h_uhp_open.mem_nhds h_neg_inv_im)
  have h_diff_S_at_z : DifferentiableAt ℂ (fun w => -(1:ℂ)/w) z := by
    apply DifferentiableAt.div (differentiableAt_const _) differentiableAt_id hz_ne
  have h_logDeriv_comp : logDeriv (fun w => g (-(1:ℂ)/w)) z =
      logDeriv g (-(1:ℂ)/z) * deriv (fun w => -(1:ℂ)/w) z :=
    logDeriv_comp h_diff_g_at_Sz h_diff_S_at_z
  -- Step 3: deriv S z = 1/z^2
  have h_deriv_S : deriv (fun w => -(1:ℂ)/w) z = 1 / z ^ 2 := by
    have h1 : HasDerivAt (fun w : ℂ => w⁻¹) (-(z ^ 2)⁻¹) z := hasDerivAt_inv hz_ne
    have h2 : HasDerivAt (fun w : ℂ => -(1:ℂ) / w) (1 / z ^ 2) z := by
      have h3 : HasDerivAt (fun w : ℂ => -w⁻¹) (-((-(z ^ 2)⁻¹))) z := h1.neg
      convert h3 using 1 <;> [ext w; skip] <;> field_simp
    exact h2.deriv
  -- Step 4: logDeriv of (w ↦ w^k * g w) using logDeriv_mul and logDeriv_zpow
  have h_zpow_ne : z ^ k ≠ 0 := zpow_ne_zero k hz_ne
  have h_diff_zpow : DifferentiableAt ℂ (· ^ k) z := differentiableAt_zpow.mpr (.inl hz_ne)
  have h_diff_g_at_z : DifferentiableAt ℂ g z :=
    h_diffOn_g.differentiableAt (h_uhp_open.mem_nhds hz)
  have h_logDeriv_mul : logDeriv (fun w => w ^ k * g w) z =
      logDeriv (· ^ k) z + logDeriv g z :=
    logDeriv_mul z h_zpow_ne hgz h_diff_zpow h_diff_g_at_z
  have h_logDeriv_zpow : logDeriv (· ^ k : ℂ → ℂ) z = ↑k / z := logDeriv_zpow z k
  -- Step 5: Combine using the eventuallyEq
  have h_logDeriv_eq : logDeriv (fun w => g (-(1:ℂ)/w)) z = logDeriv (fun w => w ^ k * g w) z :=
    logDeriv_congr_of_eventuallyEq h_eq_nhd
  -- Step 6: Algebra
  -- From the chain: logDeriv g (-1/z) * (1/z^2) = k/z + logDeriv g z
  rw [h_logDeriv_eq, h_logDeriv_mul, h_logDeriv_zpow] at h_logDeriv_comp
  rw [h_deriv_S] at h_logDeriv_comp
  -- h_logDeriv_comp : k/z + logDeriv g z = logDeriv g (-1/z) * (1/z^2)
  -- Goal: logDeriv g z = logDeriv g (-1/z) / z^2 - k/z
  -- Rearrange: logDeriv g z = logDeriv g (-1/z) * (1/z^2) - k/z
  have h_key : logDeriv g z = logDeriv g (-(1:ℂ)/z) * (1 / z ^ 2) - ↑k / z := by
    have h := h_logDeriv_comp  -- ↑k / z + logDeriv g z = logDeriv g (-1/z) * (1/z^2)
    -- This is: a + b = c, want: b = c - a
    linear_combination h
  -- Then simplify: a * (1/b) = a / b
  rw [h_key]; ring

/-- The integrand identity for a single arc segment, away from zeros.

For `z` on the unit circle arc (im > 0, z ≠ 0, g(z) ≠ 0), and any `v : ℂ`:
  `logDeriv(g)(z) * v = logDeriv(g)(-1/z) * (v / z^2) - k * v / z` -/
lemma integrand_S_identity (z v : ℂ) (hz : 0 < z.im) (hz_ne : z ≠ 0)
    (hgz : modularFormCompOfComplex f z ≠ 0) :
    logDeriv (modularFormCompOfComplex f) z * v =
    logDeriv (modularFormCompOfComplex f) (-(1:ℂ)/z) * (v / z ^ 2) - ↑k * (v / z) := by
  have h := logDeriv_modform_S_transform f z hz hz_ne hgz
  rw [h]; ring

/-- Integrand splitting for one arc segment.

For a curve `γ` in the upper half plane with `γ t ≠ 0` and `g(γ t) ≠ 0`,
the integral of `logDeriv g ∘ γ * γ'` equals the S-composed integral minus `k * ∫ γ'/γ`.

Uses `integrand_S_identity` (pointwise identity from the S-transformation law)
combined with the chain rule `deriv(-1/γ)(t) = γ'(t) / γ(t)²`. -/
lemma arc_integral_split_one_seg (γ : ℝ → ℂ) (a b : ℝ)
    (hγ_im : ∀ t ∈ Set.uIcc a b, 0 < (γ t).im)
    (hγ_ne : ∀ t, γ t ≠ 0)
    (hγ_diff : ∀ t, DifferentiableAt ℝ γ t)
    (hg_ne : ∀ t ∈ Set.uIcc a b, modularFormCompOfComplex f (γ t) ≠ 0)
    (hI₁ : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (-(1:ℂ) / γ t) * deriv (fun s => -(1:ℂ) / γ s) t) MeasureTheory.volume a b)
    (hI₂ : IntervalIntegrable (fun t => (γ t)⁻¹ * deriv γ t)
      MeasureTheory.volume a b)
    :
    ∫ t in a..b, logDeriv (modularFormCompOfComplex f) (γ t) * deriv γ t =
    (∫ t in a..b, logDeriv (modularFormCompOfComplex f) (-(1:ℂ) / γ t) *
      deriv (fun s => -(1:ℂ) / γ s) t) -
    ↑k * (∫ t in a..b, (γ t)⁻¹ * deriv γ t) := by
  -- Chain rule: deriv(-(1:ℂ)/γ)(t) = γ'(t) / γ(t)²
  have h_chain : ∀ t, deriv (fun s => -(1:ℂ) / γ s) t = deriv γ t / (γ t) ^ 2 := by
    intro t
    have hfun_eq : (fun s => -(1:ℂ) / γ s) = (fun s => -(γ s)⁻¹) := by ext s; field_simp
    rw [hfun_eq]
    have h_inv : HasDerivAt (fun s => (γ s)⁻¹)
        (deriv γ t • -(γ t ^ 2)⁻¹) t :=
      (hasDerivAt_inv (hγ_ne t)).scomp t (hγ_diff t).hasDerivAt
    have h_neg : HasDerivAt (fun s => -(γ s)⁻¹)
        (-(deriv γ t • -(γ t ^ 2)⁻¹)) t := h_inv.neg
    rw [h_neg.deriv]; simp [smul_eq_mul]; ring
  -- Pointwise identity on [a,b] from integrand_S_identity + chain rule
  have h_pw : ∀ t ∈ Set.uIcc a b,
      logDeriv (modularFormCompOfComplex f) (γ t) * deriv γ t =
      logDeriv (modularFormCompOfComplex f) (-(1:ℂ) / γ t) *
        deriv (fun s => -(1:ℂ) / γ s) t -
      ↑k * ((γ t)⁻¹ * deriv γ t) := by
    intro t ht
    have h := integrand_S_identity f (γ t) (deriv γ t) (hγ_im t ht) (hγ_ne t) (hg_ne t ht)
    rw [h, h_chain t, inv_mul_eq_div]
  -- Rewrite LHS using pointwise identity, split, and factor out k
  rw [intervalIntegral.integral_congr (fun t ht => h_pw t ht),
      intervalIntegral.integral_sub hI₁ (hI₂.const_mul _),
      show (fun x => (↑k : ℂ) * ((γ x)⁻¹ * deriv γ x)) =
        (fun x => (↑k : ℂ) * ((fun x => (γ x)⁻¹ * deriv γ x) x)) from rfl,
      intervalIntegral.integral_const_mul (↑k : ℂ) (fun x => (γ x)⁻¹ * deriv γ x)]

/-- The modular form identity decomposes the arc integral.

From f(S·z) = z^k · f(z), taking logDeriv gives:
  logDeriv(g)(z) = logDeriv(g)(S(z)) · S'(z) - k/z

Integrating over the arc:
  I_arc = [∫ logDeriv(g)(S(z))·S'(z) dz] - k · [∫ dz/z]

The first integral equals `pv_integral f (S ∘ seg) ...` (the S-composed integral),
and the second equals `I · π / 3` from `arc_integral_one_over_z`.

**KEY DEPENDENCY:** slash_action_eqn_SL'' from mathlib. -/
lemma arc_logDeriv_modform_split
    (h_arc_seg2_gne : ∀ t ∈ Set.uIcc 1 2, modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0)
    (h_arc_seg3_gne : ∀ t ∈ Set.uIcc 2 3, modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0) :
    pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3 =
    (pv_integral f (fun t => -(1:ℂ) / fdBoundary_seg2 t) 1 2 +
     pv_integral f (fun t => -(1:ℂ) / fdBoundary_seg3 t) 2 3) -
    ↑k * (I * ↑Real.pi / 3) := by
  -- Unfold pv_integral
  simp only [pv_integral]
  -- Apply the integrand splitting to each segment
  have h_seg2_ne : ∀ t, fdBoundary_seg2 t ≠ 0 := by
    intro t; unfold fdBoundary_seg2; exact exp_ne_zero _
  have h_seg3_ne : ∀ t, fdBoundary_seg3 t ≠ 0 := by
    intro t; unfold fdBoundary_seg3; exact exp_ne_zero _
  have h_seg2_diff : ∀ t, DifferentiableAt ℝ fdBoundary_seg2 t := by
    intro t; unfold fdBoundary_seg2
    apply DifferentiableAt.cexp
    apply DifferentiableAt.mul_const
    exact (DifferentiableAt.add (differentiableAt_const _)
      ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _)))
  have h_seg3_diff : ∀ t, DifferentiableAt ℝ fdBoundary_seg3 t := by
    intro t; unfold fdBoundary_seg3
    apply DifferentiableAt.cexp
    apply DifferentiableAt.mul_const
    exact (DifferentiableAt.add (differentiableAt_const _)
      ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _)))
  have h_seg2_im : ∀ t ∈ Set.uIcc 1 2, 0 < (fdBoundary_seg2 t).im := by
    intro t ht; unfold fdBoundary_seg2
    rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
        (↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3))) * I by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hpi := Real.pi_pos
    have h1 : 1 ≤ t := by
      have := ht.1; simp only [min_eq_left (show (1:ℝ) ≤ 2 by norm_num)] at this; exact this
    have h2 : t ≤ 2 := by
      have := ht.2; simp only [max_eq_right (show (1:ℝ) ≤ 2 by norm_num)] at this; exact this
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : 0 ≤ (t - 1) * (Real.pi / 2 - Real.pi / 3) := by
        apply mul_nonneg <;> linarith
      linarith
    · have : (t - 1) * (Real.pi / 2 - Real.pi / 3) ≤ 1 * (Real.pi / 2 - Real.pi / 3) := by
        apply mul_le_mul_of_nonneg_right <;> linarith
      linarith
  have h_seg3_im : ∀ t ∈ Set.uIcc 2 3, 0 < (fdBoundary_seg3 t).im := by
    intro t ht; unfold fdBoundary_seg3
    rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
        (↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2))) * I by push_cast; ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    have hpi := Real.pi_pos
    have h1 : 2 ≤ t := by
      have := ht.1; simp only [min_eq_left (show (2:ℝ) ≤ 3 by norm_num)] at this; exact this
    have h2 : t ≤ 3 := by
      have := ht.2; simp only [max_eq_right (show (2:ℝ) ≤ 3 by norm_num)] at this; exact this
    apply Real.sin_pos_of_pos_of_lt_pi
    · have : 0 ≤ (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) := by
        apply mul_nonneg <;> linarith
      linarith
    · have : (t - 2) * (2 * Real.pi / 3 - Real.pi / 2) ≤ 1 * (2 * Real.pi / 3 - Real.pi / 2) := by
        apply mul_le_mul_of_nonneg_right <;> linarith
      linarith
  -- Nonvanishing of g on the arc segments (generic position: f has no zeros on ∂𝒟)
  -- This is a standard assumption in the valence formula proof.
  have h_seg2_gne := h_arc_seg2_gne
  have h_seg3_gne := h_arc_seg3_gne
  -- Helper: S-composed segments have positive imaginary part
  have h_seg2_S_im : ∀ t ∈ Set.uIcc 1 2, 0 < (-(1:ℂ) / fdBoundary_seg2 t).im := by
    intro t ht
    have hne : fdBoundary_seg2 t ≠ 0 := h_seg2_ne t
    rw [show -(1:ℂ) / fdBoundary_seg2 t = (-fdBoundary_seg2 t)⁻¹ by field_simp]
    rw [Complex.inv_im]
    apply div_pos
    · have := h_seg2_im t ht; simp only [Complex.neg_im] at this ⊢
      linarith
    · exact Complex.normSq_pos.mpr (neg_ne_zero.mpr hne)
  have h_seg3_S_im : ∀ t ∈ Set.uIcc 2 3, 0 < (-(1:ℂ) / fdBoundary_seg3 t).im := by
    intro t ht
    have hne : fdBoundary_seg3 t ≠ 0 := h_seg3_ne t
    rw [show -(1:ℂ) / fdBoundary_seg3 t = (-fdBoundary_seg3 t)⁻¹ by field_simp]
    rw [Complex.inv_im]
    apply div_pos
    · have := h_seg3_im t ht; simp only [Complex.neg_im] at this ⊢
      linarith
    · exact Complex.normSq_pos.mpr (neg_ne_zero.mpr hne)
  -- Helper: S-composed segments give nonzero modular form values
  have h_seg2_S_gne : ∀ t ∈ Set.uIcc 1 2,
      modularFormCompOfComplex f (-(1:ℂ) / fdBoundary_seg2 t) ≠ 0 := by
    intro t ht
    have hfne : modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0 := h_seg2_gne t ht
    have hne : fdBoundary_seg2 t ≠ 0 := h_seg2_ne t
    -- Use S-identity with z = seg2(t): f(ofComplex(-1/z)) = z^k * f(ofComplex(z))
    have h_id := modform_comp_ofComplex_S_identity f (fdBoundary_seg2 t) (h_seg2_im t ht)
    -- h_id : f(ofComplex(-1/seg2(t))) = seg2(t)^k * f(ofComplex(seg2(t)))
    -- Since modularFormCompOfComplex is abbrev for f ∘ ofComplex, goal matches LHS
    rw [show modularFormCompOfComplex f (-(1:ℂ) / fdBoundary_seg2 t) =
        (fdBoundary_seg2 t : ℂ) ^ k * modularFormCompOfComplex f (fdBoundary_seg2 t) from h_id]
    exact mul_ne_zero (zpow_ne_zero _ hne) hfne
  have h_seg3_S_gne : ∀ t ∈ Set.uIcc 2 3,
      modularFormCompOfComplex f (-(1:ℂ) / fdBoundary_seg3 t) ≠ 0 := by
    intro t ht
    have hfne : modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0 := h_seg3_gne t ht
    have hne : fdBoundary_seg3 t ≠ 0 := h_seg3_ne t
    have h_id := modform_comp_ofComplex_S_identity f (fdBoundary_seg3 t) (h_seg3_im t ht)
    rw [show modularFormCompOfComplex f (-(1:ℂ) / fdBoundary_seg3 t) =
        (fdBoundary_seg3 t : ℂ) ^ k * modularFormCompOfComplex f (fdBoundary_seg3 t) from h_id]
    exact mul_ne_zero (zpow_ne_zero _ hne) hfne
  -- Integrability of the S-composed integrands
  -- Mathematical proof: The integrand equals
  --   logDeriv(f)(-(1/seg(t))) * d/dt[-(1/seg(t))]
  -- Both factors are continuous:
  -- - logDeriv(f) is analytic (hence continuous) at -(1/seg(t)) because:
  --   * -(1/seg(t)) is in upper half plane (h_seg*_S_im)
  --   * f(-(1/seg(t))) ≠ 0 (h_seg*_S_gne)
  --   * So analyticAt_logDeriv_off_zeros applies
  -- - d/dt[-(1/seg(t))] is continuous (smooth function composition)
  -- Therefore the product is continuous, and continuous functions on [a,b] are integrable.
  -- Derivative of S ∘ seg2 in closed form: deriv(t → -1/seg2(t)) = (π/6)*I / seg2(t)
  have h_deriv_eq2 : ∀ t, deriv (fun s => -(1:ℂ) / fdBoundary_seg2 s) t =
      ↑(Real.pi / 6) * I / fdBoundary_seg2 t := by
    intro t
    have hfun_eq : (fun s => -(1:ℂ) / fdBoundary_seg2 s) = (fun s => -(fdBoundary_seg2 s)⁻¹) := by
      ext s; field_simp
    rw [hfun_eq]
    have h_inv := (hasDerivAt_inv (h_seg2_ne t)).scomp t (h_seg2_diff t).hasDerivAt
    have h_neg : HasDerivAt (fun s => -(fdBoundary_seg2 s)⁻¹)
        (-(deriv fdBoundary_seg2 t • -(fdBoundary_seg2 t ^ 2)⁻¹)) t := h_inv.neg
    rw [h_neg.deriv, deriv_fdBoundary_seg2_arc_eq]; simp [smul_eq_mul]
    have hne := h_seg2_ne t; field_simp
  -- ContinuousAt of S ∘ seg2 (from differentiability of seg2 and nonvanishing)
  have h_ca2 : ∀ t, ContinuousAt (fun t' => -(1:ℂ) / fdBoundary_seg2 t') t :=
    fun t => ContinuousAt.div₀ continuousAt_const (h_seg2_diff t).continuousAt (h_seg2_ne t)
  -- ContinuousAt of logDeriv g at S(seg2(t)) (from analyticity + nonvanishing)
  have h_ld_ca2 : ∀ t ∈ Set.uIcc 1 2,
      ContinuousAt (logDeriv (modularFormCompOfComplex f)) (-(1:ℂ) / fdBoundary_seg2 t) :=
    fun t ht => (analyticAt_logDeriv_off_zeros f _ (h_seg2_S_im t ht) (h_seg2_S_gne t ht)).continuousAt
  have h_seg2_I1 : IntervalIntegrable (fun t =>
      logDeriv (modularFormCompOfComplex f) (-(1:ℂ) / fdBoundary_seg2 t) *
      deriv (fun s => -(1:ℂ) / fdBoundary_seg2 s) t) MeasureTheory.volume 1 2 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    apply ContinuousWithinAt.mul
    · exact (ContinuousAt.comp (f := fun t' => -(1:ℂ) / fdBoundary_seg2 t')
        (h_ld_ca2 t ht) (h_ca2 t)).continuousWithinAt
    · exact (ContinuousAt.div₀ continuousAt_const
        (h_seg2_diff t).continuousAt (h_seg2_ne t)).continuousWithinAt |>.congr
        (fun t' ht' => h_deriv_eq2 t') (h_deriv_eq2 t)
  -- Mirror for seg3
  have h_deriv_eq3 : ∀ t, deriv (fun s => -(1:ℂ) / fdBoundary_seg3 s) t =
      ↑(Real.pi / 6) * I / fdBoundary_seg3 t := by
    intro t
    have hfun_eq : (fun s => -(1:ℂ) / fdBoundary_seg3 s) = (fun s => -(fdBoundary_seg3 s)⁻¹) := by
      ext s; field_simp
    rw [hfun_eq]
    have h_inv := (hasDerivAt_inv (h_seg3_ne t)).scomp t (h_seg3_diff t).hasDerivAt
    have h_neg : HasDerivAt (fun s => -(fdBoundary_seg3 s)⁻¹)
        (-(deriv fdBoundary_seg3 t • -(fdBoundary_seg3 t ^ 2)⁻¹)) t := h_inv.neg
    rw [h_neg.deriv, deriv_fdBoundary_seg3_arc_eq]; simp [smul_eq_mul]
    have hne := h_seg3_ne t; field_simp
  have h_ca3 : ∀ t, ContinuousAt (fun t' => -(1:ℂ) / fdBoundary_seg3 t') t :=
    fun t => ContinuousAt.div₀ continuousAt_const (h_seg3_diff t).continuousAt (h_seg3_ne t)
  have h_ld_ca3 : ∀ t ∈ Set.uIcc 2 3,
      ContinuousAt (logDeriv (modularFormCompOfComplex f)) (-(1:ℂ) / fdBoundary_seg3 t) :=
    fun t ht => (analyticAt_logDeriv_off_zeros f _ (h_seg3_S_im t ht) (h_seg3_S_gne t ht)).continuousAt
  have h_seg3_I1 : IntervalIntegrable (fun t =>
      logDeriv (modularFormCompOfComplex f) (-(1:ℂ) / fdBoundary_seg3 t) *
      deriv (fun s => -(1:ℂ) / fdBoundary_seg3 s) t) MeasureTheory.volume 2 3 := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    apply ContinuousWithinAt.mul
    · exact (ContinuousAt.comp (f := fun t' => -(1:ℂ) / fdBoundary_seg3 t')
        (h_ld_ca3 t ht) (h_ca3 t)).continuousWithinAt
    · exact (ContinuousAt.div₀ continuousAt_const
        (h_seg3_diff t).continuousAt (h_seg3_ne t)).continuousWithinAt |>.congr
        (fun t' ht' => h_deriv_eq3 t') (h_deriv_eq3 t)
  -- Integrability of γ⁻¹ * γ': these are constant functions (= (π/6)*I)
  have h_seg2_I2 : IntervalIntegrable (fun t =>
      (fdBoundary_seg2 t)⁻¹ * deriv fdBoundary_seg2 t) MeasureTheory.volume 1 2 := by
    have : (fun t => (fdBoundary_seg2 t)⁻¹ * deriv fdBoundary_seg2 t) =
        fun _ => ↑(Real.pi / 6) * I := by
      ext t; rw [deriv_fdBoundary_seg2_arc_eq]
      have hne := h_seg2_ne t; field_simp; push_cast; ring
    rw [this]; exact continuous_const.intervalIntegrable 1 2
  have h_seg3_I2 : IntervalIntegrable (fun t =>
      (fdBoundary_seg3 t)⁻¹ * deriv fdBoundary_seg3 t) MeasureTheory.volume 2 3 := by
    have : (fun t => (fdBoundary_seg3 t)⁻¹ * deriv fdBoundary_seg3 t) =
        fun _ => ↑(Real.pi / 6) * I := by
      ext t; rw [deriv_fdBoundary_seg3_arc_eq]
      have hne := h_seg3_ne t; field_simp; push_cast; ring
    rw [this]; exact continuous_const.intervalIntegrable 2 3
  -- Apply the splitting lemma to each segment
  have h_split2 := arc_integral_split_one_seg f fdBoundary_seg2 1 2
    h_seg2_im h_seg2_ne h_seg2_diff h_seg2_gne h_seg2_I1 h_seg2_I2
  have h_split3 := arc_integral_split_one_seg f fdBoundary_seg3 2 3
    h_seg3_im h_seg3_ne h_seg3_diff h_seg3_gne h_seg3_I1 h_seg3_I2
  -- h_split2 : ∫₁² logDeriv(g)(seg2) * seg2' = ∫₁² logDeriv(g)(S∘seg2) * deriv(S∘seg2) - k * ∫₁² seg2⁻¹ * seg2'
  -- h_split3 : ∫₂³ logDeriv(g)(seg3) * seg3' = ∫₂³ logDeriv(g)(S∘seg3) * deriv(S∘seg3) - k * ∫₂³ seg3⁻¹ * seg3'
  -- Summing: LHS = (S-composed sum) - k * (∫₁² seg2⁻¹ * seg2' + ∫₂³ seg3⁻¹ * seg3')
  -- By arc_integral_one_over_z: ∫₁² seg2⁻¹ * seg2' + ∫₂³ seg3⁻¹ * seg3' = I * π/3
  -- Rewrite using the splitting lemmas
  rw [h_split2, h_split3]
  -- Goal: (A₂ - k * B₂) + (A₃ - k * B₃) = (A₂ + A₃) - k * (I * π / 3)
  -- This follows from: k * B₂ + k * B₃ = k * (I * π / 3)
  -- i.e., from B₂ + B₃ = I * π / 3
  -- Compute B₂ = π/6 * I and B₃ = π/6 * I directly
  have h2_inv : ∫ t in (1:ℝ)..2, (fdBoundary_seg2 t)⁻¹ * deriv fdBoundary_seg2 t =
      ↑(Real.pi / 6) * I := by
    have : ∀ t : ℝ, (fdBoundary_seg2 t)⁻¹ * deriv fdBoundary_seg2 t = ↑(Real.pi / 6) * I := by
      intro t; rw [deriv_fdBoundary_seg2_arc_eq]
      have hne : fdBoundary_seg2 t ≠ 0 := h_seg2_ne t
      field_simp; push_cast; ring
    simp_rw [this, intervalIntegral.integral_const]; simp; ring
  have h3_inv : ∫ t in (2:ℝ)..3, (fdBoundary_seg3 t)⁻¹ * deriv fdBoundary_seg3 t =
      ↑(Real.pi / 6) * I := by
    have : ∀ t : ℝ, (fdBoundary_seg3 t)⁻¹ * deriv fdBoundary_seg3 t = ↑(Real.pi / 6) * I := by
      intro t; rw [deriv_fdBoundary_seg3_arc_eq]
      have hne : fdBoundary_seg3 t ≠ 0 := h_seg3_ne t
      field_simp; push_cast; ring
    simp_rw [this, intervalIntegral.integral_const]; simp; ring
  rw [h2_inv, h3_inv]
  push_cast; ring

/-- **S-transformation for the arc integral**: The S-symmetry of the arc gives 2I = -k·iπ/3.

From `f(Sz) = z^k · f(z)` (modular form identity for S ∈ SL₂(ℤ)):
- `logDeriv g(Sz)·S'(z) = k/z + logDeriv g(z)` (where g = modularFormCompOfComplex f)
- Integrating: `I = ∫ logDeriv(g)(Sz)·S'(z) dz - k·∫ dz/z`
- S reverses the arc (maps e^{iθ} to e^{i(π-θ)}), so the first integral = -I
- ∫ dz/z = iπ/3 (from `arc_integral_one_over_z`)
- Therefore: `I = -I - k·iπ/3`, i.e., `2I = -k·iπ/3`

**Proof**: Uses `arc_logDeriv_modform_split` (depends on `arc_integral_split_one_seg`,
now sorry-free) combined with `arc_integral_S_reversal` (proven: pure
change of variables). The remaining sorries are in the caller: nonvanishing of f
on the arc and integrability of the S-composed integrand. -/
lemma arc_integral_S_symmetry
    (h_arc_seg2_gne : ∀ t ∈ Set.uIcc 1 2, modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0)
    (h_arc_seg3_gne : ∀ t ∈ Set.uIcc 2 3, modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0) :
    2 * (pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3) =
      -(↑k * I * ↑Real.pi / 3) := by
  set I_arc := pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3
  -- Reduce to: I = -I - k·iπ/3 (the S-symmetry identity)
  suffices h_key : I_arc = -I_arc - ↑k * I * ↑Real.pi / 3 by
    linear_combination h_key
  -- Decompose using modular form identity
  have h_split := arc_logDeriv_modform_split f h_arc_seg2_gne h_arc_seg3_gne
  -- Apply S-reversal: S-composed integral = -I_arc
  have h_rev := arc_integral_S_reversal f
  -- Combine: I_arc = -I_arc - k·iπ/3
  -- (Use linarith-style reasoning over ℂ via linear_combination)
  -- From h_split: I_arc = J - k·iπ/3 where J = S-composed integral
  -- From h_rev: J = -I_arc
  -- So: I_arc = -I_arc - k·iπ/3
  linear_combination h_split + h_rev

/-- The arc integrals give the -k/12 contribution (negative due to CW orientation).

The integral ∫_{arc} f'/f dz over the unit circle arc from ρ' through i to ρ
equals -(2πi · k/12) by the modular transformation law.

**Mathematical content**: Use the weight-k transformation law under S: z ↦ -1/z.

**Key facts:**
1. S swaps ρ ↔ ρ' and fixes i: S(ρ') = ρ, S(ρ) = ρ', S(i) = i
2. For modular forms: f(Sz) = z^k · f(z)
3. Taking logDeriv: (f'/f)(Sz) · S'(z) = k/z + (f'/f)(z), hence (f'/f)(z) = (f'/f)(Sz)·S'(z) - k/z
4. Since S'(z) = 1/z², on the unit circle |z|=1: z⁻¹ * (f'/f)(Sz) = (f'/f)(z) + k·z⁻¹

**Proof outline:**
1. The arc from ρ' to ρ has total angle π/3 on the unit circle
2. Split into: seg2 (ρ' → i, angle π/6) and seg3 (i → ρ, angle π/6)
3. Use the S-transformation which maps the arc to itself (reversed)
4. The "extra" term -k/z integrates to give the -k contribution
5. On the unit circle arc, ∫ (dz/z) = i·(angle) = i·π/3
6. Combined with the antisymmetry from S, the contribution is -k/12

**Derivation of 2I = -k·i·π/3:**
Let I = ∫_{ρ' → ρ} (f'/f)(z) dz and J = k · ∫_{ρ' → ρ} dz/z = k·i·π/3.

From the transformation law: (f'/f)(z) = (f'/f)(S z) · S'(z) - k/z

So: I = ∫_{ρ' → ρ} (f'/f)(S z) · S'(z) dz - J

Substituting w = S(z), dw = S'(z) dz:
When z goes from ρ' to ρ, w = S(z) goes from S(ρ') = ρ to S(ρ) = ρ'.
So: ∫_{z: ρ' → ρ} (f'/f)(S z) · S'(z) dz = ∫_{w: ρ → ρ'} (f'/f)(w) dw = -I

Therefore: I = -I - J, so 2I = -J = -k · i · π/3

Thus: I = -k · i · π/6 = -(2π · i · k / 12)
-/
theorem arc_contribution_is_k_div_12
    (h_arc_seg2_gne : ∀ t ∈ Set.uIcc 1 2, modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0)
    (h_arc_seg3_gne : ∀ t ∈ Set.uIcc 2 3, modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0) :
    pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3 =
      -(2 * Real.pi * I * (k : ℂ) / 12) := by
  -- Proof via S-transformation symmetry:
  -- Let I = ∫_{arc} logDeriv(g)(z) dz where g = modularFormCompOfComplex f.
  -- From f(Sz) = z^k f(z): logDeriv(g)(Sz)·S'(z) = k/z + logDeriv(g)(z)
  -- So logDeriv(g)(z) = logDeriv(g)(Sz)·S'(z) - k/z
  -- Integrating: I = ∫ logDeriv(g)(Sz)·S'(z) dz - k·∫ dz/z
  -- By substitution (S reverses the arc): ∫ logDeriv(g)(Sz)·S'(z) dz = -I
  -- By arc_integral_one_over_z: ∫ dz/z = iπ/3
  -- Therefore: I = -I - k·iπ/3, so 2I = -k·iπ/3, I = -k·iπ/6 = -(2πik/12)
  --
  -- KEY DEPENDENCY: The S-transformation identity on ℂ:
  --   modularFormCompOfComplex f (-1/z) = z^k · modularFormCompOfComplex f z
  -- This follows from SlashInvariantForm.slash_action_eqn_SL'' in Mathlib.
  --
  -- KEY TOOLS: logDeriv_comp, logDeriv_mul, logDeriv_zpow from Mathlib.
  --
  -- Abbreviate the arc integral
  set I_arc := pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3 with hI_arc_def
  -- The key equation: 2 * I_arc = -(↑k * I * ↑Real.pi / 3)
  -- From: I = -I - k·iπ/3, i.e., 2I = -k·iπ/3
  suffices h_2I : 2 * I_arc = -(↑k * I * ↑Real.pi / 3) by
    -- From 2I = -kiπ/3, we get I = -kiπ/6 = -(2πik/12)
    have h_solve : I_arc = -(↑k * I * ↑Real.pi / 3) / 2 := by
      have : (2 : ℂ) ≠ 0 := by norm_num
      rw [eq_div_iff this, mul_comm]; exact h_2I
    rw [h_solve]; ring
  -- The proof of 2I = -kiπ/3 uses:
  -- (a) The S-reversal: ∫ logDeriv(g)(S(γ(t))) * d/dt[S(γ(t))] dt = -I_arc
  -- (b) arc_integral_one_over_z: ∫ dz/z = iπ/3
  -- (c) The decomposition: I = (-I) + (-k · iπ/3), so 2I = -kiπ/3
  --
  -- This requires the modular form S-transformation identity and
  -- the change of variables theorem for the arc integral.
  exact arc_integral_S_symmetry f h_arc_seg2_gne h_arc_seg3_gne


/-! ## Arc Imaginary Part Lemmas

These show that `fdBoundary_seg2` and `fdBoundary_seg3` map into the upper half-plane,
which is needed to apply `hasSimplePoleAt_logDeriv_of_zero` and for the non-vanishing
argument from integrability. -/

/-- The imaginary part of `fdBoundary_seg2(t)` is positive for `t ∈ [1,2]`.
The arc traces `exp(θ·I)` with `θ ∈ [π/3, π/2] ⊂ (0, π)`, so `sin(θ) > 0`. -/
lemma fdBoundary_seg2_im_pos (t : ℝ) (ht : t ∈ Set.uIcc 1 2) :
    0 < (fdBoundary_seg2 t).im := by
  unfold fdBoundary_seg2
  have ht1 : 1 ≤ t := (Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2) ▸ ht).1
  have ht2 : t ≤ 2 := (Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2) ▸ ht).2
  rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- The imaginary part of `fdBoundary_seg3(t)` is positive for `t ∈ [2,3]`.
The arc traces `exp(θ·I)` with `θ ∈ [π/2, 2π/3] ⊂ (0, π)`, so `sin(θ) > 0`. -/
lemma fdBoundary_seg3_im_pos (t : ℝ) (ht : t ∈ Set.uIcc 2 3) :
    0 < (fdBoundary_seg3 t).im := by
  unfold fdBoundary_seg3
  have ht1 : 2 ≤ t := (Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3) ▸ ht).1
  have ht2 : t ≤ 3 := (Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3) ▸ ht).2
  rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_im]
  exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-! ## Seg5 Micro-Lemmas (C1–C7): Horizontal Edge → Cusp Order -/

/-- **C1**: The derivative of `fdBoundary_seg5` is the constant 1. -/
lemma deriv_fdBoundary_seg5_eq_one (t : ℝ) : deriv fdBoundary_seg5 t = 1 := by
  unfold fdBoundary_seg5
  have : (fun t : ℝ => (↑t : ℂ) - 9/2 + ↑H_height * I) =
      (fun t : ℝ => Complex.ofRealCLM t + (-(9:ℂ)/2 + ↑H_height * I)) := by
    ext t; simp [Complex.ofRealCLM_apply]; ring
  rw [this, deriv_add_const]
  exact Complex.ofRealCLM.hasDerivAt.deriv

/-- **C2**: The q-parameter along seg5 has constant modulus `exp(-2π · H_height)`.

Along seg5, `z(t) = (t - 9/2) + H_height · i` so
`q(t) = exp(2πi · z(t)) = exp(-2π · H_height) · exp(2πi · (t - 9/2))`. -/
lemma q_modulus_on_seg5 (t : ℝ) :
    ‖Complex.exp (2 * ↑Real.pi * I * fdBoundary_seg5 t)‖ =
    Real.exp (-2 * Real.pi * H_height) := by
  unfold fdBoundary_seg5
  rw [show 2 * ↑Real.pi * I * ((↑t : ℂ) - 9/2 + ↑H_height * I) =
      ↑(-2 * Real.pi * H_height) + ↑(2 * Real.pi * (t - 9/2)) * I by
    have hI : (I : ℂ) ^ 2 = -1 := I_sq
    push_cast; linear_combination (2 * ↑Real.pi * ↑H_height) * hI]
  rw [Complex.exp_add, Complex.norm_mul, Complex.norm_exp_ofReal,
      Complex.norm_exp_ofReal_mul_I]
  simp

/-- **C3**: q-expansion factorization at the cusp.

For a modular form `f` of level 1, the q-expansion gives
`f(τ) = Σ_{n ≥ 0} aₙ q^n` where `q = exp(2πiτ)`.
The order `m = orderAtCusp f` satisfies `aₙ = 0` for `n < m` and `aₘ ≠ 0` (when `f ≠ 0`).

This implies `f(z) = q^m · u(q)` where `u` is holomorphic with `u(0) ≠ 0`. -/
lemma qexp_factor_at_cusp (_hf : f ≠ 0) :
    ∀ τ : UpperHalfPlane, HasSum
      (fun n : ℕ => (ModularFormClass.qExpansion 1 f).coeff n •
        (Function.Periodic.qParam (1 : ℕ) τ) ^ n) (f τ) :=
  fun τ => ModularFormClass.hasSum_qExpansion 1 f τ

/-! ### C4 Helper Lemmas: Horizontal Integral via Circle Integral

The proof of `seg5_logDeriv_integral_eq` proceeds in three stages:

**Stage 1** (`seg5_integral_eq_circleIntegral`): Change of variables from the
parametric integral `∫_4^5 logDeriv(f)(z(t)) dt` to a circle integral
`∮_{|q|=R} logDeriv(F)(q) dq` where `F = cuspFunction 1 f` and `R = exp(-2πH)`.

The key identity is: `logDeriv(f ∘ ofComplex)(z) = 2πi · q · logDeriv(F)(q)`
where `q = exp(2πiz)`. The substitution `θ = 2π(t - 9/2)` maps `[4,5]` to
`[-π, π]`, and by 2π-periodicity this equals the standard circle integral `[0, 2π]`.

**Stage 2** (`circleIntegral_logDeriv_cuspFunction`): Compute the circle integral
using the factorization `F(q) = q^m · U(q)` where `U(0) ≠ 0`:
  `∮ logDeriv(F) dq = m · ∮ 1/q dq + ∮ logDeriv(U) dq = m · 2πi + 0`

The first part uses `circleIntegral.integral_sub_center_inv`.
The second part uses Cauchy-Goursat (`circleIntegral_eq_zero_of_differentiable_on_off_countable`)
applied to `logDeriv(U)`, which is analytic on the disk since U is analytic and nonvanishing.

**Stage 3**: Combine Stages 1 and 2.
-/

/-- The q-radius along seg5: `R = exp(-2π · H_height)`, which is positive and < 1. -/
noncomputable def seg5_q_radius : ℝ := Real.exp (-2 * Real.pi * H_height)

lemma seg5_q_radius_pos : 0 < seg5_q_radius := Real.exp_pos _

lemma seg5_q_radius_lt_one : seg5_q_radius < 1 :=
  Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, H_height_gt_one])

lemma seg5_q_radius_ne_zero : seg5_q_radius ≠ 0 := ne_of_gt seg5_q_radius_pos

/-! ### Helper Lemmas for the Circle Integral Computation -/

/-- Auxiliary: `qExpansionFormalMultilinearSeries` is nonzero when `f ≠ 0`. -/
private lemma qExpFMS_ne_zero (hf : f ≠ 0) :
    ModularFormClass.qExpansionFormalMultilinearSeries 1 f ≠ 0 := by
  intro h
  have hp := ModularFormClass.hasFPowerSeries_cuspFunction (n := 1) (F := ModularForm (Gamma 1) k) (f := f)
  -- Rewrite hp to use 0 as the series
  have hp0 : HasFPowerSeriesOnBall (SlashInvariantFormClass.cuspFunction (1 : ℕ) f)
      (0 : FormalMultilinearSeries ℂ ℂ ℂ) 0 1 := h ▸ hp
  -- cuspFunction 1 f = 0 near 0
  have hF_ev := hp0.eventually_eq_zero
  -- F is analytic, so if it vanishes near 0, it vanishes on the connected ball
  have hF_analytic : AnalyticOnNhd ℂ (SlashInvariantFormClass.cuspFunction (1 : ℕ) f)
      (Metric.ball 0 1) := hp.analyticOnNhd
  have hF_eq_zero : Set.EqOn (SlashInvariantFormClass.cuspFunction (1 : ℕ) f) 0
      (Metric.ball 0 1) :=
    hF_analytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (Convex.isPreconnected (convex_ball 0 1)) (Metric.mem_ball_self one_pos) hF_ev
  -- f(τ) = cuspFunction(qParam(τ)) = 0 for all τ
  have : ∀ τ : UpperHalfPlane, f τ = 0 := by
    intro τ
    have := SlashInvariantFormClass.eq_cuspFunction (n := 1) (f := f) τ
    rw [← this]
    exact hF_eq_zero (by simpa using τ.norm_qParam_lt_one 1)
  exact hf (ModularForm.ext (fun τ => this τ))

/-- Auxiliary: the FMS order equals `(orderAtCusp f).toNat`. -/
private lemma qExpFMS_order_eq (hf : f ≠ 0) :
    (ModularFormClass.qExpansionFormalMultilinearSeries 1 f).order =
    (orderAtCusp f).toNat := by
  set p := ModularFormClass.qExpansionFormalMultilinearSeries 1 f
  set ps := ModularFormClass.qExpansion 1 f
  have hp_ne := qExpFMS_ne_zero f hf
  -- Key: ‖p n‖ = ‖ps.coeff n‖ via qExpansionFormalMultilinearSeries_apply_norm
  have h_norm : ∀ n, ‖p n‖ = ‖ps.coeff n‖ :=
    ModularFormClass.qExpansionFormalMultilinearSeries_apply_norm 1 f
  -- So p n = 0 ↔ ps.coeff n = 0
  have h_zero_iff : ∀ n, p n = 0 ↔ ps.coeff n = 0 := by
    intro n; rw [← norm_eq_zero, h_norm, norm_eq_zero]
  -- {n | p n ≠ 0} = {n | ps.coeff n ≠ 0}
  have h_sets : {n | p n ≠ 0} = {n | ps.coeff n ≠ 0} :=
    Set.ext fun n => (h_zero_iff n).not
  have hps_ne : ps ≠ 0 := by
    intro h; apply hp_ne
    exact FormalMultilinearSeries.ext fun n => (h_zero_iff n).mpr (by rw [h]; simp)
  -- Strategy: show p.order satisfies the characterization of ps.order.toNat
  -- Both are the smallest n with nonzero n-th coefficient
  show p.order = (orderAtCusp f).toNat
  unfold orderAtCusp
  simp only [Int.toNat_natCast]
  -- Goal: p.order = ps.order.toNat
  -- Use order_eq_nat: ps.order = n ↔ ps.coeff n ≠ 0 ∧ ∀ i < n, ps.coeff i = 0
  have hps_order : ps.order = ↑ps.order.toNat :=
    (ENat.coe_toNat_eq_self.mpr (PowerSeries.order_eq_top.not.mpr hps_ne)).symm
  set m := ps.order.toNat
  have hm := (PowerSeries.order_eq_nat.mp (by exact_mod_cast hps_order) :
    ps.coeff m ≠ 0 ∧ ∀ i, i < m → ps.coeff i = 0)
  -- p.order = sInf {n | p n ≠ 0} by definition
  -- We show p.order = m by showing m is the smallest index with p m ≠ 0
  have hp_m_ne : p m ≠ 0 := (h_zero_iff m).not.mpr hm.1
  have hp_lt : ∀ i, i < m → p i = 0 := fun i hi => (h_zero_iff i).mpr (hm.2 i hi)
  -- p.order is sInf {n | p n ≠ 0}, and m is the min of this set
  show p.order = m
  unfold FormalMultilinearSeries.order
  have hm_mem : m ∈ {n | p n ≠ 0} := hp_m_ne
  apply le_antisymm
  · exact Nat.sInf_le hm_mem
  · -- m ≤ sInf {n | p n ≠ 0}: if sInf < m, then p (sInf) ≠ 0 but also = 0
    by_contra h_lt
    push_neg at h_lt
    have h_sInf_mem := Nat.sInf_mem ⟨m, hm_mem⟩
    -- h_sInf_mem : sInf {n | p n ≠ 0} ∈ {n | p n ≠ 0}, i.e., p (sInf ..) ≠ 0
    -- hp_lt _ h_lt : p (sInf ..) = 0
    exact h_sInf_mem (hp_lt _ h_lt)

/-- The cuspFunction factors as `q^m * g(q)` on the open unit ball,
where `m = orderAtCusp f` and `g` is differentiable with `g(0) ≠ 0`. -/
private lemma cuspFunction_factored (hf : f ≠ 0) :
    ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (Metric.ball 0 1) ∧
      g 0 ≠ 0 ∧
      ∀ q ∈ Metric.ball (0 : ℂ) 1,
        SlashInvariantFormClass.cuspFunction (1 : ℕ) f q =
        q ^ (orderAtCusp f).toNat * g q := by
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f
  set p := ModularFormClass.qExpansionFormalMultilinearSeries 1 f
  have hp : HasFPowerSeriesOnBall F p 0 1 :=
    ModularFormClass.hasFPowerSeries_cuspFunction 1 f
  have hp_ne : p ≠ 0 := qExpFMS_ne_zero f hf
  have hp_order : p.order = (orderAtCusp f).toNat := qExpFMS_order_eq f hf
  -- g₀ := (swap dslope 0)^[p.order] F
  set g₀ := (Function.swap dslope 0)^[p.order] F
  -- g₀ is differentiable on ball(0,1) via Complex.differentiableOn_dslope
  have hF_diff : DifferentiableOn ℂ F (Metric.ball 0 1) :=
    hp.analyticOnNhd.differentiableOn
  have hball_nhds : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) :=
    Metric.ball_mem_nhds 0 one_pos
  have hg_diff : DifferentiableOn ℂ g₀ (Metric.ball 0 1) := by
    -- Iterate: dslope preserves differentiability on ball for ℂ
    suffices ∀ (k : ℕ), DifferentiableOn ℂ ((Function.swap dslope 0)^[k] F)
        (Metric.ball 0 1) from this p.order
    intro k
    induction k with
    | zero => simpa using hF_diff
    | succ j ih =>
      simp only [Function.iterate_succ', Function.comp_def]
      exact (Complex.differentiableOn_dslope hball_nhds).mpr ih
  -- g₀ 0 ≠ 0
  have hg_ne : g₀ 0 ≠ 0 :=
    hp.hasFPowerSeriesAt.iterate_dslope_fslope_ne_zero hp_ne
  -- F =ᶠ[𝓝 0] fun z => z^n • g₀ z (local factorization)
  have hF_local : ∀ᶠ z in 𝓝 (0 : ℂ),
      F z = (z - 0) ^ p.order • g₀ z :=
    hp.hasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope
  -- Both sides are analytic on ball(0,1), so they agree everywhere
  have hF_analytic : AnalyticOnNhd ℂ F (Metric.ball 0 1) := hp.analyticOnNhd
  have hg_analytic : AnalyticOnNhd ℂ g₀ (Metric.ball 0 1) :=
    fun z hz => hg_diff.analyticAt (IsOpen.mem_nhds Metric.isOpen_ball hz)
  have hRHS_analytic : AnalyticOnNhd ℂ (fun z => (z - 0) ^ p.order • g₀ z) (Metric.ball 0 1) :=
    fun z hz => ((analyticAt_id.sub analyticAt_const).pow p.order).smul (hg_analytic z hz)
  have h0_mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := Metric.mem_ball_self one_pos
  have hF_eq : Set.EqOn F (fun z => (z - 0) ^ p.order • g₀ z) (Metric.ball 0 1) :=
    hF_analytic.eqOn_of_preconnected_of_eventuallyEq hRHS_analytic
      (Convex.isPreconnected (convex_ball 0 1)) h0_mem hF_local
  -- Now produce the witness
  refine ⟨g₀, hg_diff, hg_ne, fun q hq => ?_⟩
  have := hF_eq hq
  simp only [sub_zero, smul_eq_mul] at this
  rw [this, hp_order]

/-- `∮ (m : ℂ) * q⁻¹ dq = m * 2πi` for nonzero radius. -/
private lemma circleIntegral_const_mul_inv (m : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∮ q in C(0, R), m * q⁻¹) = m * (2 * ↑Real.pi * I) := by
  rw [circleIntegral.integral_const_mul]
  congr 1
  have : (fun q : ℂ => q⁻¹) = (fun q => (q - 0)⁻¹) := by ext; simp
  rw [this]
  exact circleIntegral.integral_sub_center_inv 0 hR

/-- `∮ logDeriv(g) dq = 0` when `g` is differentiable on ball(0,1) and nonvanishing
on closedBall(0,R), where `0 < R < 1`. Uses Cauchy-Goursat: `logDeriv(g) = g'/g`
is holomorphic on ball(0,R) since `g` is differentiable and nonvanishing there. -/
private lemma circleIntegral_logDeriv_regular_zero
    (g : ℂ → ℂ) {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < 1)
    (hg_diff : DifferentiableOn ℂ g (Metric.ball 0 1))
    (hg_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) R, g q ≠ 0) :
    (∮ q in C(0, R), logDeriv g q) = 0 := by
  have hR_le : 0 ≤ R := le_of_lt hR_pos
  have h_cb_sub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 1 :=
    Metric.closedBall_subset_ball hR_lt
  have h_ball_sub : Metric.ball (0 : ℂ) R ⊆ Metric.ball 0 1 :=
    Metric.ball_subset_ball (le_of_lt hR_lt)
  have hg_cont : ContinuousOn (logDeriv g) (Metric.closedBall (0 : ℂ) R) := by
    show ContinuousOn (fun q => deriv g q / g q) (Metric.closedBall (0 : ℂ) R)
    exact ContinuousOn.div
      (((hg_diff.contDiffOn (n := 1) Metric.isOpen_ball).continuousOn_deriv_of_isOpen
        Metric.isOpen_ball le_rfl).mono h_cb_sub)
      (hg_diff.continuousOn.mono h_cb_sub)
      hg_nonvan
  have hg_logDeriv_diff : ∀ z ∈ Metric.ball (0 : ℂ) R, DifferentiableAt ℂ (logDeriv g) z := by
    intro z hz
    have hz1 := h_ball_sub hz
    exact ((hg_diff.deriv Metric.isOpen_ball).differentiableAt
      (Metric.isOpen_ball.mem_nhds hz1)).div
      (hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hz1))
      (hg_nonvan z (Metric.ball_subset_closedBall hz))
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR_le
    Set.countable_empty hg_cont (fun z hz => hg_logDeriv_diff z hz.1)

/-- **Stage 2**: The circle integral of `logDeriv(F)` around `|q| = R` equals
`2πi · orderAtCusp f`, where `F = cuspFunction 1 f`.

This uses:
- `F(q) = q^m · g(q)` from `cuspFunction_factored`
- `logDeriv(q^m · g) = m/q + logDeriv(g)` from `logDeriv_mul` + `logDeriv_pow`
- `∮ m/q dq = m · 2πi` from `circleIntegral_const_mul_inv`
- `∮ logDeriv(g) dq = 0` from `circleIntegral_logDeriv_regular_zero`

The `hcusp_nonvan` hypothesis ensures the cuspFunction is nonvanishing on the
punctured closed disk `0 < |q| ≤ R`. This holds when `H_height` is large enough
that `f` has no zeros above height `H_height` in the fundamental domain strip. -/
lemma circleIntegral_logDeriv_cuspFunction (hf : f ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (∮ q in C(0, seg5_q_radius),
      logDeriv (SlashInvariantFormClass.cuspFunction (1 : ℕ) f) q) =
    2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f with hF_def
  set m := (orderAtCusp f).toNat with hm_def
  set R := seg5_q_radius with hR_def
  -- Step 1: Get factorization F(q) = q^m · g(q)
  obtain ⟨g, hg_diff, hg_ne, hFg⟩ := cuspFunction_factored f hf
  -- Step 2: g is nonvanishing on closedBall(0, R)
  have hg_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) R, g q ≠ 0 := by
    intro q hq
    by_cases hq0 : q = 0
    · exact hq0 ▸ hg_ne
    · have hF_ne := hcusp_nonvan q hq hq0
      have hq_ball := Metric.closedBall_subset_ball seg5_q_radius_lt_one hq
      have hFq := hFg q hq_ball
      rw [← hF_def] at hFq
      rw [hFq] at hF_ne
      exact right_ne_zero_of_mul hF_ne
  -- Step 3: logDeriv F = ↑m / q + logDeriv g on the sphere
  have h_split : ∀ q, q ∈ Metric.sphere (0 : ℂ) R →
      logDeriv F q = ↑m / q + logDeriv g q := by
    intro q hq
    have hq_ne : q ≠ 0 := by
      intro h; simp [h] at hq
      exact absurd hq.symm (ne_of_gt seg5_q_radius_pos)
    have hq_ball : q ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall.trans
        (Metric.closedBall_subset_ball seg5_q_radius_lt_one) hq
    -- F = q^m * g on a neighborhood of q (since ball(0,1) is open and q ∈ ball(0,1))
    have hF_eq : F =ᶠ[𝓝 q] (fun z => z ^ m * g z) :=
      (Metric.isOpen_ball.eventually_mem hq_ball).mono (fun z hz => hFg z hz)
    -- logDeriv F q = logDeriv (fun z => z^m * g z) q by congr
    have h1 := logDeriv_congr_of_eventuallyEq hF_eq
    -- logDeriv (fun z => z^m * g z) q = m/q + logDeriv g q by direct computation
    have hg_diff_at := hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hq_ball)
    have hg_ne_q := hg_nonvan q (Metric.sphere_subset_closedBall hq)
    rw [h1]; clear h1
    simp only [logDeriv_apply]
    -- Compute deriv (fun z => z^m * g z) q using HasDerivAt
    have h_hd : HasDerivAt (fun z => z ^ m * g z)
        (↑m * q ^ (m - 1) * g q + q ^ m * deriv g q) q :=
      (hasDerivAt_pow m q).mul hg_diff_at.hasDerivAt
    rw [h_hd.deriv]
    have hqm_ne : q ^ m ≠ 0 := pow_ne_zero m hq_ne
    field_simp
    rcases m with _ | n
    · ring
    · rw [Nat.succ_sub_one]; ring
  -- Step 4: Rewrite the circle integral using the split
  -- Step 5: ∮ (m/q + logDeriv g) = ∮ m/q + ∮ logDeriv g = m·2πi + 0
  have hR_pos : 0 < R := seg5_q_radius_pos
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR_le : 0 ≤ R := le_of_lt hR_pos
  have hR_lt : R < 1 := seg5_q_radius_lt_one
  -- CircleIntegrable for m * q⁻¹
  have hci_inv : CircleIntegrable (fun q => (↑m : ℂ) * q⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR_le
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ continuousOn_id
    intro z hz
    simp only [Metric.mem_sphere, dist_zero_right] at hz
    simp only [id]
    exact norm_ne_zero_iff.mp (by linarith)
  -- CircleIntegrable for logDeriv g
  have hci_logDeriv : CircleIntegrable (fun q => logDeriv g q) 0 R := by
    apply ContinuousOn.circleIntegrable hR_le
    have h_sphere_sub : Metric.sphere (0 : ℂ) R ⊆ Metric.ball 0 1 :=
      Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hR_lt)
    have hg_deriv_cont : ContinuousOn (deriv g) (Metric.ball (0 : ℂ) 1) :=
      ((hg_diff.contDiffOn (n := 1) Metric.isOpen_ball).continuousOn_deriv_of_isOpen
        Metric.isOpen_ball le_rfl)
    show ContinuousOn (fun q => deriv g q / g q) (Metric.sphere 0 R)
    exact ContinuousOn.div
      (hg_deriv_cont.mono h_sphere_sub)
      (hg_diff.continuousOn.mono h_sphere_sub)
      (fun q hq => hg_nonvan q (Metric.sphere_subset_closedBall hq))
  -- Rewrite integral using congr on sphere
  have h_congr : (∮ q in C(0, R), logDeriv F q) =
      ∮ q in C(0, R), ((↑m : ℂ) / q + logDeriv g q) := by
    simp only [circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    rw [h_split _ (circleMap_mem_sphere 0 hR_le θ)]
  -- Split into sum and compute
  have h_div_eq : (fun q : ℂ => (↑m : ℂ) / q + logDeriv g q) =
      (fun q => (↑m : ℂ) * q⁻¹ + logDeriv g q) := by
    ext; simp [div_eq_mul_inv]
  rw [h_congr, h_div_eq, circleIntegral.integral_add hci_inv hci_logDeriv,
      circleIntegral_const_mul_inv (↑m : ℂ) hR_ne,
      circleIntegral_logDeriv_regular_zero g hR_pos hR_lt hg_diff hg_nonvan,
      add_zero]
  -- Final algebra: ↑m * (2πi) = 2πi * ↑(orderAtCusp f)
  have hm_cast : (↑m : ℂ) = ↑(orderAtCusp f) := by
    show (↑((orderAtCusp f).toNat) : ℂ) = ↑(orderAtCusp f)
    unfold orderAtCusp
    push_cast [Int.toNat_natCast]; rfl
  rw [hm_cast]; ring

/-! ### Helper lemmas for Stage 1: parametric to circle integral change of variables -/

/-- The q-parameter along seg5 equals a circle map value:
`qParam 1 (fdBoundary_seg5 t) = circleMap 0 seg5_q_radius (2π(t - 9/2))`. -/
private lemma qParam_seg5_eq_circleMap (t : ℝ) :
    Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5 t) =
    circleMap 0 seg5_q_radius (2 * Real.pi * (t - 9 / 2)) := by
  simp only [Function.Periodic.qParam, fdBoundary_seg5, seg5_q_radius, circleMap_zero]
  -- Goal: exp(2πI * ((t:ℂ) - 9/2 + H*I) / 1) = ↑(exp(-2πH)) * exp(↑(2π(t-9/2)) * I)
  -- Split the exponent into real + imaginary parts
  rw [show (2 : ℂ) * ↑Real.pi * I * ((↑t : ℂ) - 9 / 2 + ↑H_height * I) / (1 : ℝ) =
      ↑(-2 * Real.pi * H_height) + ↑(2 * Real.pi * (t - 9 / 2)) * I by
    push_cast
    have hI : (I : ℂ) ^ 2 = -1 := I_sq
    linear_combination (2 * ↑Real.pi * ↑H_height) * hI]
  rw [Complex.exp_add, Complex.ofReal_exp]

/-- The imaginary part of `fdBoundary_seg5 t` is `H_height`, which is positive. -/
private lemma im_fdBoundary_seg5_pos (t : ℝ) : 0 < (fdBoundary_seg5 t).im := by
  show 0 < ((↑t : ℂ) - 9 / 2 + ↑H_height * I).im
  have : H_height > 1 := H_height_gt_one
  simp [add_im, mul_im, sub_im, ofReal_im, ofReal_re, I_re, I_im, div_im]
  linarith

/-- Key chain rule identity: on seg5, `logDeriv(f ∘ ofComplex)(z(t))` equals
`logDeriv(cuspFn)(q(z(t))) * (2πI * q(z(t)))`, where `q(z) = exp(2πiz)`.

This follows from:
1. `f ∘ ofComplex = cuspFn ∘ qParam 1` on the upper half plane (`eq_cuspFunction`)
2. `logDeriv(g ∘ h)(x) = logDeriv(g)(h(x)) * h'(x)` (chain rule for logDeriv)
3. `deriv(qParam 1)(z) = 2πI * qParam 1 z` -/
private lemma logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv (t : ℝ) :
    logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5 t) =
    logDeriv (SlashInvariantFormClass.cuspFunction (1 : ℕ) f)
      (Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5 t)) *
    (2 * ↑Real.pi * I * Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5 t)) := by
  set z := fdBoundary_seg5 t
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f
  set q_fn := Function.Periodic.qParam (1 : ℝ)
  -- Step 1: modularFormCompOfComplex f = F ∘ q_fn
  have h_eq : modularFormCompOfComplex f = F ∘ q_fn := by
    ext w
    simp only [modularFormCompOfComplex, Function.comp_def, F,
      SlashInvariantFormClass.cuspFunction]
    have := (SlashInvariantFormClass.periodic_comp_ofComplex 1 f).eq_cuspFunction
      (Nat.cast_ne_zero.mpr (by norm_num : (1 : ℕ) ≠ 0)) w
    convert this.symm using 2; norm_cast
  -- Step 2: ‖q_fn z‖ < 1 (since fdBoundary_seg5 t has positive imaginary part)
  have hq_norm : ‖q_fn z‖ < 1 := by
    simp only [q_fn, Function.Periodic.norm_qParam]
    have him : 0 < (fdBoundary_seg5 t).im := im_fdBoundary_seg5_pos t
    rw [show (-2 * Real.pi * z.im / (1 : ℝ)) = -2 * Real.pi * z.im by ring]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hF_diff : DifferentiableAt ℂ F (q_fn z) :=
    ModularFormClass.differentiableAt_cuspFunction (n := 1) (f := f) hq_norm
  have hq_diff : DifferentiableAt ℂ q_fn z :=
    Function.Periodic.differentiable_qParam.differentiableAt
  -- Step 3: Apply chain rule for logDeriv
  rw [h_eq, logDeriv_comp hF_diff hq_diff]
  -- Step 4: deriv q_fn z = 2πi * q_fn z
  have hderiv : deriv q_fn z = 2 * ↑Real.pi * I * q_fn z := by
    have hfun : q_fn = (fun z : ℂ => cexp (2 * ↑Real.pi * I * z)) := by
      ext w; simp [q_fn, Function.Periodic.qParam, div_one]
    rw [hfun]
    have h1 : HasDerivAt (fun z => 2 * ↑Real.pi * I * z) (2 * ↑Real.pi * I) z := by
      simpa using (hasDerivAt_id z).const_mul (2 * ↑Real.pi * I)
    rw [h1.cexp.deriv]; ring
  rw [hderiv]

/-- **Stage 1**: The parametric integral of logDeriv(f) along seg5 equals the circle
integral of logDeriv(cuspFunction) in the q-plane.

The change of variables uses:
- `(f ∘ ofComplex)(z) = cuspFunction 1 f (exp(2πiz))` from `eq_cuspFunction'`
- Chain rule: `logDeriv(F ∘ q)(z) = logDeriv(F)(q(z)) · q'(z) / q(z) · q(z)` simplifies to
  `= logDeriv(F)(q) · 2πi · q` where `q = exp(2πiz)`
- Substitution: `θ = 2π(t - 9/2)` maps `[4,5]` to `[-π, π]` and
  `q(t) = R · exp(iθ) = circleMap 0 R θ`
- By 2π-periodicity: `∫_{-π}^{π} = ∫_0^{2π}` which is the circle integral -/
lemma seg5_integral_eq_circleIntegral :
    ∫ t in (4:ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5 t) =
    ∮ q in C(0, seg5_q_radius),
      logDeriv (SlashInvariantFormClass.cuspFunction (1 : ℕ) f) q := by
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f
  set R := seg5_q_radius
  -- Step 1: Rewrite integrand using chain rule
  have h_integrand : ∀ t : ℝ,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5 t) =
      logDeriv F (Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5 t)) *
      (2 * ↑Real.pi * I * Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5 t)) :=
    logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv f
  simp_rw [h_integrand]
  -- Step 2: Rewrite qParam in terms of circleMap
  simp_rw [qParam_seg5_eq_circleMap]
  -- Step 3: Combine steps 3-7 into a single rewriting chain.
  -- The integrand is: logDeriv F (circleMap 0 R (2π(t-9/2))) * (2πI * circleMap 0 R (2π(t-9/2)))
  -- = (2π) • (deriv(circleMap 0 R)(2π(t-9/2)) • logDeriv F (circleMap 0 R (2π(t-9/2))))
  -- because deriv(circleMap 0 R)(θ) = circleMap 0 R θ * I.
  -- Define the "circle integrand" for convenience
  set g : ℝ → ℂ := fun θ => deriv (circleMap 0 (↑R)) θ • logDeriv F (circleMap 0 ↑R θ) with hg_def
  -- Step 3a: Rewrite the integral by showing integrands are equal
  have h_eq_integral :
      (∫ t in (4:ℝ)..5,
        logDeriv F (circleMap 0 R (2 * Real.pi * (t - 9 / 2))) *
        (2 * ↑Real.pi * I * circleMap 0 R (2 * Real.pi * (t - 9 / 2)))) =
      ∫ t in (4:ℝ)..5, (2 * Real.pi : ℝ) • g (2 * Real.pi * (t - 9 / 2)) := by
    congr 1; ext t
    simp only [hg_def, deriv_circleMap, Complex.real_smul, smul_eq_mul, ofReal_mul, ofReal_ofNat]
    ring
  rw [h_eq_integral]
  -- Step 4: Pull out the constant factor 2π
  rw [intervalIntegral.integral_smul]
  -- Step 5: Substitution θ = 2π(t - 9/2) = 2π * t + 2π * (-9/2)
  have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [show (fun t : ℝ => g (2 * Real.pi * (t - 9 / 2))) =
    (fun t : ℝ => g (2 * Real.pi * t + (2 * Real.pi * (-9 / 2)))) by
    ext t; ring_nf]
  rw [intervalIntegral.integral_comp_mul_add g hpi_ne]
  -- Bounds: 2π * 4 + 2π * (-9/2) = -π, 2π * 5 + 2π * (-9/2) = π
  have hbnd_lo : 2 * Real.pi * 4 + 2 * Real.pi * (-9 / 2) = -Real.pi := by ring
  have hbnd_hi : 2 * Real.pi * 5 + 2 * Real.pi * (-9 / 2) = Real.pi := by ring
  rw [hbnd_lo, hbnd_hi]
  -- Step 6: (2π) • (2π)⁻¹ • integral = integral
  rw [smul_inv_smul₀ hpi_ne]
  -- Step 7: By 2π-periodicity, ∫ in -π..π = ∫ in 0..2π
  -- The RHS is the circle integral = ∫ θ in 0..2π, g θ by definition
  -- The LHS is ∫ θ in -π..π, g θ, which equals ∫ θ in 0..2π, g θ by periodicity
  have h_periodic : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [hg_def, deriv_circleMap, periodic_circleMap 0 R θ, smul_eq_mul]
  -- Use periodicity shift: ∫ in -π..(-π + 2π) = ∫ in 0..(0 + 2π)
  have h_shift := Function.Periodic.intervalIntegral_add_eq h_periodic (-Real.pi) 0
  simp only [neg_add_cancel, zero_add] at h_shift
  -- h_shift : ∫ in -π..(-π + 2π), g = ∫ in 0..2π, g
  rw [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi from by ring] at h_shift
  rw [h_shift]
  -- Now goal is ∫ θ in 0..2π, g θ = ∮ q in C(0, R), logDeriv F q
  -- This is the definition of circle integral
  rfl

/-- **C4**: The logDeriv integral along seg5 equals `2πi · orderAtCusp f`.

Combines Stage 1 (parametric → circle) and Stage 2 (circle → 2πi·m). -/
lemma seg5_logDeriv_integral_eq (hf : f ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∫ t in (4:ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5 t) =
    2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
  rw [seg5_integral_eq_circleIntegral]
  exact circleIntegral_logDeriv_cuspFunction f hf hcusp_nonvan

/-- **C5**: The constant `2πi · m` integrates to `2πi · m` over seg5 (length 1). -/
lemma seg5_ord_part_integral_exact :
    ∫ _ in (4:ℝ)..5, (2 * ↑Real.pi * I * ↑(orderAtCusp f) : ℂ) =
    2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
  rw [intervalIntegral.integral_const]
  norm_num

/-- **C7**: The horizontal edge integral equals `2πi · orderAtCusp f`.

Combines the exact integral of the constant term (C5) with the vanishing
of the remainder integral (C4). -/
theorem seg5_integral_eq_cusp_order (hf : f ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f fdBoundary_seg5 4 5 =
    2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
  unfold pv_integral
  simp_rw [deriv_fdBoundary_seg5_eq_one, mul_one]
  exact seg5_logDeriv_integral_eq f hf hcusp_nonvan

/-! ## Nonvanishing from Integrability

If `logDeriv(f) ∘ γ · γ'` is interval integrable on `[a,b]` and `γ` maps into the
upper half-plane with nonvanishing derivative, then `f` has no zeros on the arc.
The argument is by contradiction: a zero would create a non-integrable `1/(t - t₀)` pole. -/

/-- If `modularFormCompOfComplex f (γ t₀) = 0` for some `t₀` on the unit circle arc,
then the integrand `logDeriv(f)(γ(t)) · γ'(t)` has `(t - t₀)⁻¹` behavior,
hence is not interval integrable on any nontrivial interval containing `t₀`.

This is the key Big-O lemma: the pole of `logDeriv f` at `γ(t₀)` pulls back through
the arc parameterization to give a `1/(t - t₀)` singularity, because `γ'(t₀) ≠ 0`. -/
lemma isBigO_sub_inv_logDeriv_arc
    (γ : ℝ → ℂ) (t₀ : ℝ) (z₀ : ℂ)
    (hγ_eq : γ t₀ = z₀)
    (hγ_diff : DifferentiableAt ℝ γ t₀)
    (hγ_deriv_ne : deriv γ t₀ ≠ 0)
    (hγ_deriv_cont : ContinuousAt (deriv γ) t₀)
    (n : ℤ) (hn : n > 0) (g_reg : ℂ → ℂ) (hg_analytic : AnalyticAt ℂ g_reg z₀)
    (hg_ne : g_reg z₀ ≠ 0)
    (h_formula : ∀ᶠ z in 𝓝 z₀, z ≠ z₀ →
      logDeriv (modularFormCompOfComplex f) z = (n : ℂ) / (z - z₀) + logDeriv g_reg z) :
    (fun t => ((t : ℝ) - t₀)⁻¹) =O[𝓝[≠] t₀]
      (fun t => logDeriv (modularFormCompOfComplex f) (γ t) * deriv γ t) := by
  -- Strategy: show ↑(t - t₀) * integrand(t) → n (nonzero), then extract Big-O.
  -- Step 1: HasDerivAt gives slope limit
  have hderiv : HasDerivAt γ (deriv γ t₀) t₀ := hγ_diff.hasDerivAt
  -- The slope (γ(t) - γ(t₀)) / ↑(t - t₀) → deriv γ t₀
  have hslope : Tendsto (fun t => (↑(t - t₀) : ℂ)⁻¹ * (γ t - z₀))
      (𝓝[≠] t₀) (𝓝 (deriv γ t₀)) := by
    have := hasDerivAt_iff_tendsto_slope.mp hderiv
    rw [show z₀ = γ t₀ from hγ_eq.symm]
    exact this.congr (fun t => by
      simp only [slope, vsub_eq_sub, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_sub])
  -- Step 2: γ(t) ≠ z₀ for t ≠ t₀ near t₀ (since deriv γ t₀ ≠ 0)
  have hγ_ne : ∀ᶠ t in 𝓝[≠] t₀, γ t ≠ z₀ := by
    -- Since slope → deriv γ t₀ ≠ 0, eventually the slope is nonzero,
    -- which means γ t ≠ z₀ (the numerator is nonzero)
    have hslope_ne : ∀ᶠ t in 𝓝[≠] t₀, (↑(t - t₀) : ℂ)⁻¹ * (γ t - z₀) ≠ 0 := by
      apply (hslope.eventually (isOpen_ne.mem_nhds hγ_deriv_ne)).mono
      intro t ht; exact ht
    apply hslope_ne.mono
    intro t ht habs
    exact ht (by simp [habs])
  -- Step 3: Pull back the logDeriv formula along γ
  have h_formula_pullback : ∀ᶠ t in 𝓝[≠] t₀,
      logDeriv (modularFormCompOfComplex f) (γ t) =
        (n : ℂ) / (γ t - z₀) + logDeriv g_reg (γ t) := by
    -- h_formula holds eventually near z₀; pull back along γ which is continuous at t₀
    have hγ_cont : ContinuousAt γ t₀ := hγ_diff.continuousAt
    have h_near : ∀ᶠ z in 𝓝 (γ t₀), z ≠ z₀ →
        logDeriv (modularFormCompOfComplex f) z =
          (n : ℂ) / (z - z₀) + logDeriv g_reg z := by rw [hγ_eq]; exact h_formula
    have h_ev := (hγ_cont.tendsto.eventually h_near).filter_mono
      (nhdsWithin_le_nhds (s := {t₀}ᶜ))
    exact (h_ev.and hγ_ne).mono fun t ⟨hf, hne⟩ => hf hne
  -- Step 4: Show ↑(t - t₀) * integrand(t) → n as t → t₀, t ≠ t₀
  -- Define the product P(t) = ↑(t - t₀) * (logDeriv f (γ t) * deriv γ t)
  -- We show P(t) → (n : ℂ) * (deriv γ t₀)⁻¹ * deriv γ t₀ = n
  -- The key: ↑(t-t₀) * n/(γ(t) - z₀) * γ'(t) → n * (γ'(t₀))⁻¹ * γ'(t₀) = n
  -- and ↑(t-t₀) * logDeriv g_reg(γ t) * γ'(t) → 0 * logDeriv g_reg(z₀) * γ'(t₀) = 0
  -- Step 4a: ↑(t - t₀) / (γ t - z₀) → (deriv γ t₀)⁻¹
  have hinv_slope : Tendsto (fun t => (γ t - z₀) / (↑(t - t₀) : ℂ))
      (𝓝[≠] t₀) (𝓝 (deriv γ t₀)) :=
    hslope.congr (fun t => by rw [div_eq_mul_inv, mul_comm])
  have h_inv_deriv : Tendsto (fun t => (↑(t - t₀) : ℂ) / (γ t - z₀))
      (𝓝[≠] t₀) (𝓝 ((deriv γ t₀)⁻¹)) :=
    (hinv_slope.inv₀ hγ_deriv_ne).congr (fun t => by rw [inv_div])
  -- Step 4b: deriv γ t → deriv γ t₀ (from ContinuousAt hypothesis)
  have hγ'_tendsto : Tendsto (deriv γ) (𝓝[≠] t₀) (𝓝 (deriv γ t₀)) :=
    hγ_deriv_cont.tendsto.mono_left nhdsWithin_le_nhds
  -- Step 4c: logDeriv g_reg is continuous at z₀ (analytic + nonvanishing)
  have h_logDeriv_cont : ContinuousAt (logDeriv g_reg) z₀ := by
    show ContinuousAt (deriv g_reg / g_reg) z₀
    exact hg_analytic.deriv.continuousAt.div hg_analytic.continuousAt hg_ne
  -- Step 4d: logDeriv g_reg(γ t) → logDeriv g_reg(z₀)
  have h_reg_tendsto : Tendsto (fun t => logDeriv g_reg (γ t))
      (𝓝[≠] t₀) (𝓝 (logDeriv g_reg z₀)) := by
    have h1 : ContinuousAt (fun t => logDeriv g_reg (γ t)) t₀ := by
      apply ContinuousAt.comp _ hγ_diff.continuousAt
      rwa [hγ_eq]
    have h2 : (fun t => logDeriv g_reg (γ t)) t₀ = logDeriv g_reg z₀ := by
      simp [hγ_eq]
    rw [← h2]
    exact h1.tendsto.mono_left nhdsWithin_le_nhds
  -- Step 4e: ↑(t - t₀) → 0 as ℂ
  have h_ofReal_zero : Tendsto (fun t => (↑(t - t₀) : ℂ)) (𝓝[≠] t₀) (𝓝 0) := by
    have hcont : ContinuousAt (fun t : ℝ => (↑(t - t₀) : ℂ)) t₀ :=
      Complex.continuous_ofReal.continuousAt.comp (continuousAt_id.sub continuousAt_const)
    have h := hcont.tendsto
    simp only [sub_self, Complex.ofReal_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  -- Step 5: Product ↑(t-t₀) * integrand(t) → (n : ℂ)
  have h_product : Tendsto (fun t => (↑(t - t₀) : ℂ) *
      (logDeriv (modularFormCompOfComplex f) (γ t) * deriv γ t))
      (𝓝[≠] t₀) (𝓝 (↑n : ℂ)) := by
    have h_limit_eq : (↑n : ℂ) = ↑n * (deriv γ t₀)⁻¹ * deriv γ t₀ +
        0 * logDeriv g_reg z₀ * deriv γ t₀ := by
      simp [mul_assoc, inv_mul_cancel₀ hγ_deriv_ne]
    rw [h_limit_eq]
    refine Filter.Tendsto.congr' ?_ (Tendsto.add
        ((tendsto_const_nhds.mul h_inv_deriv).mul hγ'_tendsto)
        ((h_ofReal_zero.mul h_reg_tendsto).mul hγ'_tendsto))
    apply (h_formula_pullback.and hγ_ne).mono
    intro t ⟨hform, hne⟩
    dsimp only
    have hne' : γ t - z₀ ≠ 0 := sub_ne_zero.mpr hne
    rw [hform]; field_simp
  -- Step 6: Extract Big-O from the nonzero limit
  have hn_ne : (↑n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (ne_of_gt hn)
  have hn_norm_pos : 0 < ‖(↑n : ℂ)‖ := norm_pos_iff.mpr hn_ne
  rw [Asymptotics.isBigO_iff]
  refine ⟨2 / ‖(↑n : ℂ)‖, ?_⟩
  have h_lower : ∀ᶠ t in 𝓝[≠] t₀,
      ‖(↑n : ℂ)‖ / 2 ≤ ‖(↑(t - t₀) : ℂ) *
        (logDeriv (modularFormCompOfComplex f) (γ t) * deriv γ t)‖ := by
    apply (h_product.norm.eventually (Ioi_mem_nhds (half_lt_self hn_norm_pos))).mono
    intro t ht
    exact le_of_lt ht
  apply (h_lower.and (eventually_nhdsWithin_of_forall fun t ht => ht)).mono
  intro t ⟨h_ge, ht_ne⟩
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at h_ge
  simp only [Real.norm_eq_abs, abs_inv]
  have h_abs_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_ne)
  rw [div_mul_eq_mul_div]
  rw [le_div_iff₀ hn_norm_pos, mul_comm]
  rw [mul_inv_le_iff₀ h_abs_pos]
  nlinarith

/-- Nonvanishing of `modularFormCompOfComplex f` on the seg2 arc from integrability.

If the integrand `logDeriv(f)(fdBoundary(t)) · fdBoundary'(t)` is interval integrable
on `[0,5]`, then `f` has no zeros on the seg2 arc `fdBoundary_seg2([1,2])`.
The proof is by contradiction using the non-integrability of `1/(t - t₀)`. -/
lemma nonvanishing_on_seg2_of_integrable (hf : f ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5) :
    ∀ t ∈ Set.uIcc 1 2, modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0 := by
  intro t₀ ht₀ h_zero
  -- Step 1: Since im(fdBoundary_seg2 t₀) > 0, we can lift to UpperHalfPlane
  have h_im_pos := fdBoundary_seg2_im_pos t₀ ht₀
  let z₀ := fdBoundary_seg2 t₀
  let s : UpperHalfPlane := ⟨z₀, h_im_pos⟩
  -- Step 2: modularFormCompOfComplex f z₀ = 0 implies f s = 0
  have h_fs_zero : f s = 0 := by
    have : modularFormCompOfComplex f z₀ = 0 := h_zero
    simp only [modularFormCompOfComplex, Function.comp_apply] at this
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at this
  -- Step 3: Get the pole decomposition from hasSimplePoleAt_logDeriv_of_zero
  obtain ⟨n, g_reg, hn_pos, hg_analytic, hg_ne_zero, _hn_eq, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s h_fs_zero
  -- Step 4: fdBoundary_seg2 is differentiable with nonvanishing derivative
  have h_seg2_diff : DifferentiableAt ℝ fdBoundary_seg2 t₀ := by
    unfold fdBoundary_seg2
    apply DifferentiableAt.cexp
    apply DifferentiableAt.mul_const
    exact (DifferentiableAt.add (differentiableAt_const _)
      ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _)))
  have h_seg2_deriv_ne : deriv fdBoundary_seg2 t₀ ≠ 0 := by
    rw [deriv_fdBoundary_seg2_arc_eq]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (ne_of_gt (div_pos Real.pi_pos (by norm_num : (6:ℝ) > 0)))
      · exact Complex.I_ne_zero
    · exact exp_ne_zero _
  -- Step 4b: fdBoundary_seg2 has continuous derivative (it's C^∞)
  have h_seg2_deriv_cont : ContinuousAt (deriv fdBoundary_seg2) t₀ := by
    have : ContDiff ℝ ⊤ fdBoundary_seg2 := by
      unfold fdBoundary_seg2
      exact ContDiff.cexp ((contDiff_const.add ((Complex.ofRealCLM.contDiff.sub
        contDiff_const).mul contDiff_const)).mul contDiff_const)
    exact (this.continuous_deriv le_top).continuousAt
  -- Step 5: Get the Big-O condition
  have h_bigO := isBigO_sub_inv_logDeriv_arc f fdBoundary_seg2 t₀ z₀ rfl
    h_seg2_diff h_seg2_deriv_ne h_seg2_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
  -- Step 6: Get interval integrability of the seg2 integrand from hint
  -- hint gives integrability on [0,5]; restrict to [1,2] using mono_set
  have h_uIcc_sub : Set.uIcc 1 2 ⊆ Set.uIcc (0:ℝ) 5 := by
    rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
    exact Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have hint_12 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 1 2 :=
    hint.mono_set h_uIcc_sub
  -- The integrands for fdBoundary and fdBoundary_seg2 agree a.e. on (1,2)
  have h_ae_eq : (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 1 2)]
      (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg2 t) * deriv fdBoundary_seg2 t) := by
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2)]
    -- Ioo 1 2 ∈ ae (volume.restrict (Ioc 1 2)) since Ioc \ Ioo = {2} is null
    have h_ioo_ae : Set.Ioo (1:ℝ) 2 ∈ ae (MeasureTheory.volume.restrict (Set.Ioc 1 2)) := by
      rw [mem_ae_iff, MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
      have hsub : (Set.Ioo (1:ℝ) 2)ᶜ ∩ Set.Ioc 1 2 ⊆ {2} := by
        intro x ⟨h1, h2⟩
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, Set.mem_Ioc] at h1 h2
        simp only [Set.mem_singleton_iff]
        rcases h1 with h | h <;> linarith [h2.1, h2.2]
      exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub)
        (MeasureTheory.measure_singleton 2).le) (zero_le _)
    filter_upwards [h_ioo_ae] with t ht
    have h_eq := fdBoundary_eq_seg2_on t ⟨ht.1, le_of_lt ht.2⟩
    rw [h_eq]; congr 1
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact fdBoundary_eq_seg2_on s ⟨hs.1, le_of_lt hs.2⟩)
  have hint_seg2 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg2 t) * deriv fdBoundary_seg2 t) MeasureTheory.volume 1 2 :=
    hint_12.congr_ae h_ae_eq
  -- Step 7: Apply not_intervalIntegrable_of_sub_inv_isBigO_punctured
  have h_not_int := not_intervalIntegrable_of_sub_inv_isBigO_punctured h_bigO
    (by norm_num : (1:ℝ) ≠ 2) (by
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
      exact ⟨(Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2) ▸ ht₀).1,
             (Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2) ▸ ht₀).2⟩)
  exact h_not_int hint_seg2

/-- Nonvanishing of `modularFormCompOfComplex f` on the seg3 arc from integrability.

Same argument as seg2, using `fdBoundary_seg3_im_pos` and `fdBoundary_eq_seg3_on`. -/
lemma nonvanishing_on_seg3_of_integrable (hf : f ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5) :
    ∀ t ∈ Set.uIcc 2 3, modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0 := by
  intro t₀ ht₀ h_zero
  -- Step 1: Since im(fdBoundary_seg3 t₀) > 0, we can lift to UpperHalfPlane
  have h_im_pos := fdBoundary_seg3_im_pos t₀ ht₀
  let z₀ := fdBoundary_seg3 t₀
  let s : UpperHalfPlane := ⟨z₀, h_im_pos⟩
  -- Step 2: modularFormCompOfComplex f z₀ = 0 implies f s = 0
  have h_fs_zero : f s = 0 := by
    have : modularFormCompOfComplex f z₀ = 0 := h_zero
    simp only [modularFormCompOfComplex, Function.comp_apply] at this
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at this
  -- Step 3: Get the pole decomposition
  obtain ⟨n, g_reg, hn_pos, hg_analytic, hg_ne_zero, _hn_eq, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s h_fs_zero
  -- Step 4: fdBoundary_seg3 is differentiable with nonvanishing derivative
  have h_seg3_diff : DifferentiableAt ℝ fdBoundary_seg3 t₀ := by
    unfold fdBoundary_seg3
    apply DifferentiableAt.cexp
    apply DifferentiableAt.mul_const
    exact (DifferentiableAt.add (differentiableAt_const _)
      ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _)))
  have h_seg3_deriv_ne : deriv fdBoundary_seg3 t₀ ≠ 0 := by
    rw [deriv_fdBoundary_seg3_arc_eq]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (ne_of_gt (div_pos Real.pi_pos (by norm_num : (6:ℝ) > 0)))
      · exact Complex.I_ne_zero
    · exact exp_ne_zero _
  -- Step 4b: fdBoundary_seg3 has continuous derivative (it's C^∞)
  have h_seg3_deriv_cont : ContinuousAt (deriv fdBoundary_seg3) t₀ := by
    have : ContDiff ℝ ⊤ fdBoundary_seg3 := by
      unfold fdBoundary_seg3
      exact ContDiff.cexp ((contDiff_const.add ((Complex.ofRealCLM.contDiff.sub
        contDiff_const).mul contDiff_const)).mul contDiff_const)
    exact (this.continuous_deriv le_top).continuousAt
  -- Step 5: Get the Big-O condition
  have h_bigO := isBigO_sub_inv_logDeriv_arc f fdBoundary_seg3 t₀ z₀ rfl
    h_seg3_diff h_seg3_deriv_ne h_seg3_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
  -- Step 6: Get interval integrability of the seg3 integrand from hint
  have h_uIcc_sub : Set.uIcc 2 3 ⊆ Set.uIcc (0:ℝ) 5 := by
    rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
    exact Set.Icc_subset_Icc (by norm_num) (by norm_num)
  have hint_23 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 2 3 :=
    hint.mono_set h_uIcc_sub
  have h_ae_eq : (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) =ᵐ[MeasureTheory.volume.restrict (Set.uIoc 2 3)]
      (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg3 t) * deriv fdBoundary_seg3 t) := by
    rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 3)]
    -- Ioo 2 3 ∈ ae (volume.restrict (Ioc 2 3)) since Ioc \ Ioo = {3} is null
    have h_ioo_ae : Set.Ioo (2:ℝ) 3 ∈ ae (MeasureTheory.volume.restrict (Set.Ioc 2 3)) := by
      rw [mem_ae_iff, MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
      have hsub : (Set.Ioo (2:ℝ) 3)ᶜ ∩ Set.Ioc 2 3 ⊆ {3} := by
        intro x ⟨h1, h2⟩
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, Set.mem_Ioc] at h1 h2
        simp only [Set.mem_singleton_iff]
        rcases h1 with h | h <;> linarith [h2.1, h2.2]
      exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub)
        (MeasureTheory.measure_singleton 3).le) (zero_le _)
    filter_upwards [h_ioo_ae] with t ht
    have h_eq := fdBoundary_eq_seg3_on t ⟨ht.1, le_of_lt ht.2⟩
    rw [h_eq]; congr 1
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact fdBoundary_eq_seg3_on s ⟨hs.1, le_of_lt hs.2⟩)
  have hint_seg3 : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg3 t) * deriv fdBoundary_seg3 t) MeasureTheory.volume 2 3 :=
    hint_23.congr_ae h_ae_eq
  -- Step 7: Apply not_intervalIntegrable_of_sub_inv_isBigO_punctured
  have h_not_int := not_intervalIntegrable_of_sub_inv_isBigO_punctured h_bigO
    (by norm_num : (2:ℝ) ≠ 3) (by
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)]
      exact ⟨(Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3) ▸ ht₀).1,
             (Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3) ▸ ht₀).2⟩)
  exact h_not_int hint_seg3

/-! ## Main PV Result -/

/-- **Main PV Result**: The CW contour integral of f'/f around ∂𝒟.

The boundary ∂𝒟 is traversed clockwise (down-arc-up-right), so:

∮_{CW ∂𝒟} f'/f dz = -(2πi · (k/12 - ord_∞(f))) = 2πi · (ord_∞(f) - k/12)

**Proof**:
1. Decompose into segments
2. Vertical edges cancel by T-invariance
3. Arc gives -k/12 by S-transformation (negative because 2I = -J from S-symmetry)
4. Horizontal edge gives +ord_∞ by q-expansion
-/
theorem pv_integral_eq_modular_transformation (hf : f ≠ 0)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp f : ℂ))) := by
  -- Step 1: Decompose into segments
  rw [show pv_integral f fdBoundary 0 5 = _ from pv_integral_decompose_segments f hint]

  -- Step 2: Rearrange to group cancelling terms
  have h_rearrange :
    pv_integral f fdBoundary_seg1 0 1 +
    pv_integral f fdBoundary_seg2 1 2 +
    pv_integral f fdBoundary_seg3 2 3 +
    pv_integral f fdBoundary_seg4 3 4 +
    pv_integral f fdBoundary_seg5 4 5 =
    (pv_integral f fdBoundary_seg1 0 1 + pv_integral f fdBoundary_seg4 3 4) +
    (pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3) +
    pv_integral f fdBoundary_seg5 4 5 := by ring
  rw [h_rearrange]

  -- Step 3: Apply vertical cancellation (seg1 + seg4 = 0)
  rw [pv_integral_vertical_cancel]

  -- Step 4: Arc nonvanishing (local helper — standard generic position assumption)
  -- Integrability of logDeriv on [0,5] implies f has no zeros on the boundary curve,
  -- since logDeriv has a non-integrable pole at any zero.
  have h_arc_seg2_gne : ∀ t ∈ Set.uIcc 1 2,
      modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0 :=
    nonvanishing_on_seg2_of_integrable f hf hint
  have h_arc_seg3_gne : ∀ t ∈ Set.uIcc 2 3,
      modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0 :=
    nonvanishing_on_seg3_of_integrable f hf hint

  -- Step 5: Apply arc contribution (seg2 + seg3 = -(2πik/12))
  rw [arc_contribution_is_k_div_12 f h_arc_seg2_gne h_arc_seg3_gne]

  -- Step 6: Handle seg5 contribution (horizontal edge at height H_height)
  -- Mathematical fact: ∫_{-1/2+Hi}^{1/2+Hi} f'/f dz = 2πi · ord_∞(f)
  -- This follows from the q-expansion: f(z) = q^m · u(q) with m = ord_∞, u(0) ≠ 0,
  -- where q = exp(2πiz). The integral picks up the winding number m.
  have h_seg5 : pv_integral f fdBoundary_seg5 4 5 =
      2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
    exact seg5_integral_eq_cusp_order f hf hcusp_nonvan
  rw [h_seg5]
  ring

/-! ## Height-Parameterized Seg5 and PV Infrastructure (Ticket F3)

These parameterized versions allow the fundamental domain boundary height `H` and
the corresponding q-radius `seg5_q_radius_H H` to vary, enabling the downstream
elimination of `hcusp_nonvan` from the public API via existential height witnesses.

### Key Theorems
* `seg5_integral_eq_cusp_order_H`: seg5 integral at height H = 2πi · ord_∞
* `pv_integral_eq_modular_transformation_H`: full PV at height H = -(2πi(k/12 - ord_∞))
-/

/-- `seg5_q_radius_H H < 1` when `H > 0`. -/
private lemma seg5_q_radius_H_lt_one' {H : ℝ} (hH : 0 < H) : seg5_q_radius_H H < 1 :=
  Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])

/-- Circle integral of logDeriv(cuspFunction) at any radius `0 < R < 1`.

This is the radius-parameterized version of `circleIntegral_logDeriv_cuspFunction`.
The factorization `F(q) = q^m · g(q)` gives:
`∮ logDeriv(F) = m · ∮ 1/q + ∮ logDeriv(g) = m · 2πi + 0`. -/
lemma circleIntegral_logDeriv_cuspFunction_of_radius (hf : f ≠ 0)
    {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < 1)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) R,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (∮ q in C(0, R),
      logDeriv (SlashInvariantFormClass.cuspFunction (1 : ℕ) f) q) =
    2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f with hF_def
  set m := (orderAtCusp f).toNat with hm_def
  obtain ⟨g, hg_diff, hg_ne, hFg⟩ := cuspFunction_factored f hf
  have hg_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) R, g q ≠ 0 := by
    intro q hq
    by_cases hq0 : q = 0
    · exact hq0 ▸ hg_ne
    · have hF_ne := hcusp_nonvan q hq hq0
      have hq_ball := Metric.closedBall_subset_ball hR_lt hq
      have hFq := hFg q hq_ball
      rw [← hF_def] at hFq
      rw [hFq] at hF_ne
      exact right_ne_zero_of_mul hF_ne
  have h_split : ∀ q, q ∈ Metric.sphere (0 : ℂ) R →
      logDeriv F q = ↑m / q + logDeriv g q := by
    intro q hq
    have hq_ne : q ≠ 0 := by
      intro h; simp [h] at hq
      exact absurd hq.symm (ne_of_gt hR_pos)
    have hq_ball : q ∈ Metric.ball (0 : ℂ) 1 :=
      Metric.sphere_subset_closedBall.trans
        (Metric.closedBall_subset_ball hR_lt) hq
    have hF_eq : F =ᶠ[𝓝 q] (fun z => z ^ m * g z) :=
      (Metric.isOpen_ball.eventually_mem hq_ball).mono (fun z hz => hFg z hz)
    have h1 := logDeriv_congr_of_eventuallyEq hF_eq
    have hg_diff_at := hg_diff.differentiableAt (Metric.isOpen_ball.mem_nhds hq_ball)
    have hg_ne_q := hg_nonvan q (Metric.sphere_subset_closedBall hq)
    rw [h1]; clear h1
    simp only [logDeriv_apply]
    have h_hd : HasDerivAt (fun z => z ^ m * g z)
        (↑m * q ^ (m - 1) * g q + q ^ m * deriv g q) q :=
      (hasDerivAt_pow m q).mul hg_diff_at.hasDerivAt
    rw [h_hd.deriv]
    have hqm_ne : q ^ m ≠ 0 := pow_ne_zero m hq_ne
    field_simp
    rcases m with _ | n
    · ring
    · rw [Nat.succ_sub_one]; ring
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR_le : 0 ≤ R := le_of_lt hR_pos
  have hci_inv : CircleIntegrable (fun q => (↑m : ℂ) * q⁻¹) 0 R := by
    apply ContinuousOn.circleIntegrable hR_le
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀ continuousOn_id
    intro z hz
    simp only [Metric.mem_sphere, dist_zero_right] at hz
    simp only [id]
    exact norm_ne_zero_iff.mp (by linarith)
  have hci_logDeriv : CircleIntegrable (fun q => logDeriv g q) 0 R := by
    apply ContinuousOn.circleIntegrable hR_le
    have h_sphere_sub : Metric.sphere (0 : ℂ) R ⊆ Metric.ball 0 1 :=
      Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball hR_lt)
    have hg_deriv_cont : ContinuousOn (deriv g) (Metric.ball (0 : ℂ) 1) :=
      ((hg_diff.contDiffOn (n := 1) Metric.isOpen_ball).continuousOn_deriv_of_isOpen
        Metric.isOpen_ball le_rfl)
    show ContinuousOn (fun q => deriv g q / g q) (Metric.sphere 0 R)
    exact ContinuousOn.div
      (hg_deriv_cont.mono h_sphere_sub)
      (hg_diff.continuousOn.mono h_sphere_sub)
      (fun q hq => hg_nonvan q (Metric.sphere_subset_closedBall hq))
  have h_congr : (∮ q in C(0, R), logDeriv F q) =
      ∮ q in C(0, R), ((↑m : ℂ) / q + logDeriv g q) := by
    simp only [circleIntegral]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only
    rw [h_split _ (circleMap_mem_sphere 0 hR_le θ)]
  have h_div_eq : (fun q : ℂ => (↑m : ℂ) / q + logDeriv g q) =
      (fun q => (↑m : ℂ) * q⁻¹ + logDeriv g q) := by
    ext; simp [div_eq_mul_inv]
  rw [h_congr, h_div_eq, circleIntegral.integral_add hci_inv hci_logDeriv,
      circleIntegral_const_mul_inv (↑m : ℂ) hR_ne,
      circleIntegral_logDeriv_regular_zero g hR_pos hR_lt hg_diff hg_nonvan,
      add_zero]
  have hm_cast : (↑m : ℂ) = ↑(orderAtCusp f) := by
    show (↑((orderAtCusp f).toNat) : ℂ) = ↑(orderAtCusp f)
    unfold orderAtCusp
    push_cast [Int.toNat_natCast]; rfl
  rw [hm_cast]; ring

/-! ### Height-Parameterized Seg5 Helpers -/

/-- The q-parameter along seg5 at height H equals a circle map value:
`qParam 1 (fdBoundary_seg5_H H t) = circleMap 0 (seg5_q_radius_H H) (2π(t - 9/2))`. -/
private lemma qParam_seg5_H_eq_circleMap (H : ℝ) (t : ℝ) :
    Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5_H H t) =
    circleMap 0 (seg5_q_radius_H H) (2 * Real.pi * (t - 9 / 2)) := by
  simp only [Function.Periodic.qParam, fdBoundary_seg5_H, seg5_q_radius_H, circleMap_zero]
  rw [show (2 : ℂ) * ↑Real.pi * I * ((↑t : ℂ) - 9 / 2 + ↑H * I) / (1 : ℝ) =
      ↑(-2 * Real.pi * H) + ↑(2 * Real.pi * (t - 9 / 2)) * I by
    push_cast
    have hI : (I : ℂ) ^ 2 = -1 := I_sq
    linear_combination (2 * ↑Real.pi * ↑H) * hI]
  rw [Complex.exp_add, Complex.ofReal_exp]

/-- The imaginary part of `fdBoundary_seg5_H H t` is `H`, which is positive when `H > 0`. -/
private lemma im_fdBoundary_seg5_H_pos {H : ℝ} (hH : 0 < H) (t : ℝ) :
    0 < (fdBoundary_seg5_H H t).im := by
  show 0 < ((↑t : ℂ) - 9 / 2 + ↑H * I).im
  simp [add_im, mul_im, sub_im, ofReal_im, ofReal_re, I_re, I_im, div_im]
  linarith

/-- Chain rule for logDeriv along seg5 at height H:
`logDeriv(f ∘ ofComplex)(z(t)) = logDeriv(cuspFn)(q(z(t))) · 2πi · q(z(t))`. -/
private lemma logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H
    {H : ℝ} (hH : 0 < H) (t : ℝ) :
    logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) =
    logDeriv (SlashInvariantFormClass.cuspFunction (1 : ℕ) f)
      (Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5_H H t)) *
    (2 * ↑Real.pi * I * Function.Periodic.qParam (1 : ℝ) (fdBoundary_seg5_H H t)) := by
  set z := fdBoundary_seg5_H H t
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f
  set q_fn := Function.Periodic.qParam (1 : ℝ)
  have h_eq : modularFormCompOfComplex f = F ∘ q_fn := by
    ext w
    simp only [modularFormCompOfComplex, Function.comp_def, F,
      SlashInvariantFormClass.cuspFunction]
    have := (SlashInvariantFormClass.periodic_comp_ofComplex 1 f).eq_cuspFunction
      (Nat.cast_ne_zero.mpr (by norm_num : (1 : ℕ) ≠ 0)) w
    convert this.symm using 2; norm_cast
  have hq_norm : ‖q_fn z‖ < 1 := by
    simp only [q_fn, Function.Periodic.norm_qParam]
    have him : 0 < (fdBoundary_seg5_H H t).im := im_fdBoundary_seg5_H_pos hH t
    rw [show (-2 * Real.pi * z.im / (1 : ℝ)) = -2 * Real.pi * z.im by ring]
    exact Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hF_diff : DifferentiableAt ℂ F (q_fn z) :=
    ModularFormClass.differentiableAt_cuspFunction (n := 1) (f := f) hq_norm
  have hq_diff : DifferentiableAt ℂ q_fn z :=
    Function.Periodic.differentiable_qParam.differentiableAt
  rw [h_eq, logDeriv_comp hF_diff hq_diff]
  have hderiv : deriv q_fn z = 2 * ↑Real.pi * I * q_fn z := by
    have hfun : q_fn = (fun z : ℂ => cexp (2 * ↑Real.pi * I * z)) := by
      ext w; simp [q_fn, Function.Periodic.qParam, div_one]
    rw [hfun]
    have h1 : HasDerivAt (fun z => 2 * ↑Real.pi * I * z) (2 * ↑Real.pi * I) z := by
      simpa using (hasDerivAt_id z).const_mul (2 * ↑Real.pi * I)
    rw [h1.cexp.deriv]; ring
  rw [hderiv]

/-- **Stage 1 (H)**: The parametric integral of logDeriv(f) along seg5 at height H
equals the circle integral of logDeriv(cuspFunction) at radius `seg5_q_radius_H H`. -/
lemma seg5_integral_eq_circleIntegral_H {H : ℝ} (hH : 0 < H) :
    ∫ t in (4:ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) =
    ∮ q in C(0, seg5_q_radius_H H),
      logDeriv (SlashInvariantFormClass.cuspFunction (1 : ℕ) f) q := by
  set F := SlashInvariantFormClass.cuspFunction (1 : ℕ) f
  set R := seg5_q_radius_H H
  simp_rw [logDeriv_modularForm_eq_logDeriv_cuspFn_mul_qderiv_H f hH]
  simp_rw [qParam_seg5_H_eq_circleMap H]
  set g : ℝ → ℂ := fun θ => deriv (circleMap 0 (↑R)) θ • logDeriv F (circleMap 0 ↑R θ)
    with hg_def
  have h_eq_integral :
      (∫ t in (4:ℝ)..5,
        logDeriv F (circleMap 0 R (2 * Real.pi * (t - 9 / 2))) *
        (2 * ↑Real.pi * I * circleMap 0 R (2 * Real.pi * (t - 9 / 2)))) =
      ∫ t in (4:ℝ)..5, (2 * Real.pi : ℝ) • g (2 * Real.pi * (t - 9 / 2)) := by
    congr 1; ext t
    simp only [hg_def, deriv_circleMap, Complex.real_smul, smul_eq_mul, ofReal_mul, ofReal_ofNat]
    ring
  rw [h_eq_integral]
  rw [intervalIntegral.integral_smul]
  have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [show (fun t : ℝ => g (2 * Real.pi * (t - 9 / 2))) =
    (fun t : ℝ => g (2 * Real.pi * t + (2 * Real.pi * (-9 / 2)))) by
    ext t; ring_nf]
  rw [intervalIntegral.integral_comp_mul_add g hpi_ne]
  have hbnd_lo : 2 * Real.pi * 4 + 2 * Real.pi * (-9 / 2) = -Real.pi := by ring
  have hbnd_hi : 2 * Real.pi * 5 + 2 * Real.pi * (-9 / 2) = Real.pi := by ring
  rw [hbnd_lo, hbnd_hi]
  rw [smul_inv_smul₀ hpi_ne]
  have h_periodic : Function.Periodic g (2 * Real.pi) := by
    intro θ
    simp only [hg_def, deriv_circleMap, periodic_circleMap 0 R θ, smul_eq_mul]
  have h_shift := Function.Periodic.intervalIntegral_add_eq h_periodic (-Real.pi) 0
  simp only [neg_add_cancel, zero_add] at h_shift
  rw [show (-Real.pi + 2 * Real.pi : ℝ) = Real.pi from by ring] at h_shift
  rw [h_shift]
  rfl

/-- Combination of Stages 1 and 2 at height H:
the logDeriv integral along seg5 at height H = 2πi · orderAtCusp. -/
lemma seg5_logDeriv_integral_eq_H (hf : f ≠ 0)
    {H : ℝ} (hH : 0 < H)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    ∫ t in (4:ℝ)..5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) =
    2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
  rw [seg5_integral_eq_circleIntegral_H f hH]
  exact circleIntegral_logDeriv_cuspFunction_of_radius f hf
    (seg5_q_radius_H_pos H) (seg5_q_radius_H_lt_one' hH) hcusp_nonvan

/-- **Seg5 at height H**: The horizontal edge integral at height H equals `2πi · orderAtCusp f`.

Same shape as `seg5_integral_eq_cusp_order` but with `fdBoundary_seg5_H H`
and `seg5_q_radius_H H`. -/
theorem seg5_integral_eq_cusp_order_H (hf : f ≠ 0)
    {H : ℝ} (hH : 0 < H)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f (fdBoundary_seg5_H H) 4 5 =
    2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
  unfold pv_integral
  simp_rw [deriv_fdBoundary_seg5_H H, mul_one]
  exact seg5_logDeriv_integral_eq_H f hf hH hcusp_nonvan

/-! ### Height-Parameterized Vertical Cancellation -/

/-- At height H, seg4(4-s) = seg1(s) - 1 for s ∈ [0,1]. -/
private lemma seg4_eq_seg1_minus_one_H (H : ℝ) (s : ℝ) (_hs : s ∈ Icc 0 1) :
    fdBoundary_seg4_H H (4 - s) = fdBoundary_seg1_H H s - 1 := by
  simp only [fdBoundary_seg4_H, fdBoundary_seg1_H]
  have h1 : ((4 - s : ℝ) : ℂ) - 3 = ((1 - s : ℝ) : ℂ) := by push_cast; ring
  simp only [h1]; push_cast; ring

/-- At height H, deriv(seg4)(4-s) = -deriv(seg1)(s). -/
private lemma deriv_seg4_at_complement_eq_neg_deriv_seg1_H (H : ℝ) (s : ℝ) :
    deriv (fdBoundary_seg4_H H) (4 - s) = -deriv (fdBoundary_seg1_H H) s := by
  rw [deriv_fdBoundary_seg4_H, deriv_fdBoundary_seg1_H]; ring

/-- Vertical edges cancel at any height H (by T-invariance). -/
theorem pv_integral_vertical_cancel_H (H : ℝ) :
    pv_integral f (fdBoundary_seg1_H H) 0 1 + pv_integral f (fdBoundary_seg4_H H) 3 4 = 0 := by
  have h_periodic : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) (1 : ℂ) := by
    have := SlashInvariantFormClass.periodic_comp_ofComplex 1 f
    simp only [Nat.cast_one] at this; exact this
  have h_logDeriv_periodic :
      Function.Periodic (logDeriv (modularFormCompOfComplex f)) (1 : ℂ) :=
    logDeriv_periodic_of_periodic h_periodic
  simp only [pv_integral]
  have h_sub : ∫ t in (3:ℝ)..4, logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg4_H H t) * deriv (fdBoundary_seg4_H H) t =
    ∫ u in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg4_H H (4 - u)) * deriv (fdBoundary_seg4_H H) (4 - u) := by
    have hsub := @intervalIntegral.integral_comp_sub_left ℂ _ _ (0:ℝ) (1:ℝ)
      (fun t => logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4_H H t) *
        deriv (fdBoundary_seg4_H H) t) (4 : ℝ)
    simp only [sub_zero, show (4:ℝ) - 1 = 3 by norm_num] at hsub
    exact hsub.symm
  have h_integrand : ∀ u ∈ Icc (0:ℝ) 1,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4_H H (4 - u)) *
        deriv (fdBoundary_seg4_H H) (4 - u) =
      -(logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H u) *
        deriv (fdBoundary_seg1_H H) u) := by
    intro u hu
    have h_seg : fdBoundary_seg4_H H (4 - u) = fdBoundary_seg1_H H u - 1 :=
      seg4_eq_seg1_minus_one_H H u hu
    have h_per : logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H u - 1) =
        logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H u) := by
      have := h_logDeriv_periodic (fdBoundary_seg1_H H u - 1)
      simp only [sub_add_cancel] at this
      exact this.symm
    have h_deriv : deriv (fdBoundary_seg4_H H) (4 - u) = -deriv (fdBoundary_seg1_H H) u :=
      deriv_seg4_at_complement_eq_neg_deriv_seg1_H H u
    rw [h_seg, h_per, h_deriv]; ring
  rw [h_sub]
  have h_eq : ∫ u in (0:ℝ)..1, logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg4_H H (4 - u)) * deriv (fdBoundary_seg4_H H) (4 - u) =
    ∫ u in (0:ℝ)..1, -(logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg1_H H u) * deriv (fdBoundary_seg1_H H) u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0:ℝ) 1 := by
      simp only [Set.uIcc, Set.mem_Icc, min_eq_left (by norm_num : (0:ℝ) ≤ 1),
        max_eq_right (by norm_num : (0:ℝ) ≤ 1)] at hu
      exact hu
    exact h_integrand u hu'
  rw [h_eq, intervalIntegral.integral_neg]; ring

/-! ### Height-Parameterized Segment Decomposition -/

set_option maxHeartbeats 400000 in
/-- Decomposition of the PV integral over `fdBoundary_H H` into five segments.

Since `fdBoundary_seg2_H = fdBoundary_seg2` and `fdBoundary_seg3_H = fdBoundary_seg3`
(arcs are H-independent), the arc segments use the standard definitions. -/
theorem pv_integral_decompose_segments_H {H : ℝ}
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5) :
    pv_integral f (fdBoundary_H H) 0 5 =
      pv_integral f (fdBoundary_seg1_H H) 0 1 +
      pv_integral f fdBoundary_seg2 1 2 +
      pv_integral f fdBoundary_seg3 2 3 +
      pv_integral f (fdBoundary_seg4_H H) 3 4 +
      pv_integral f (fdBoundary_seg5_H H) 4 5 := by
  simp only [pv_integral]
  have deriv_eq_of_nhd_eq : ∀ {f g : ℝ → ℂ} {t : ℝ}, (∀ᶠ s in 𝓝 t, f s = g s) →
      deriv f t = deriv g t := fun {f g t} h => Filter.EventuallyEq.deriv_eq h
  -- Integrands match on each segment
  have h1 : ∀ t ∈ Ioo (0:ℝ) 1,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) * deriv (fdBoundary_H H) t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg1_H H t) *
        deriv (fdBoundary_seg1_H H) t := by
    intro t ht
    have h_eq : fdBoundary_H H t = fdBoundary_seg1_H H t :=
      fdBoundary_H_eq_seg1_H (le_of_lt ht.2)
    rw [h_eq]; congr 1
    exact deriv_eq_of_nhd_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact fdBoundary_H_eq_seg1_H (le_of_lt hs.2))
  have h2 : ∀ t ∈ Ioo (1:ℝ) 2,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) * deriv (fdBoundary_H H) t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg2 t) *
        deriv fdBoundary_seg2 t := by
    intro t ht
    have ht1 : ¬(t ≤ 1) := by linarith [ht.1]
    have h_eq := fdBoundary_H_eq_seg2_H (H := H) ht1 (le_of_lt ht.2)
    rw [h_eq, fdBoundary_seg2_H]; congr 1
    exact deriv_eq_of_nhd_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [fdBoundary_H_eq_seg2_H (H := H) (by linarith [hs.1]) (le_of_lt hs.2),
        fdBoundary_seg2_H])
  have h3 : ∀ t ∈ Ioo (2:ℝ) 3,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) * deriv (fdBoundary_H H) t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg3 t) *
        deriv fdBoundary_seg3 t := by
    intro t ht
    have ht1 : ¬(t ≤ 1) := by linarith [ht.1]
    have ht2 : ¬(t ≤ 2) := by linarith [ht.1]
    have h_eq := fdBoundary_H_eq_seg3_H (H := H) ht1 ht2 (le_of_lt ht.2)
    rw [h_eq, fdBoundary_seg3_H]; congr 1
    exact deriv_eq_of_nhd_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [fdBoundary_H_eq_seg3_H (H := H) (by linarith [hs.1]) (by linarith [hs.1])
          (le_of_lt hs.2),
        fdBoundary_seg3_H])
  have h4 : ∀ t ∈ Ioo (3:ℝ) 4,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) * deriv (fdBoundary_H H) t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg4_H H t) *
        deriv (fdBoundary_seg4_H H) t := by
    intro t ht
    have h_eq := fdBoundary_H_eq_seg4_H (H := H) (by linarith [ht.1] : ¬(t ≤ 1))
      (by linarith [ht.1]) (by linarith [ht.1]) (le_of_lt ht.2)
    rw [h_eq]; congr 1
    exact deriv_eq_of_nhd_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact fdBoundary_H_eq_seg4_H (H := H) (by linarith [hs.1]) (by linarith [hs.1])
        (by linarith [hs.1]) (le_of_lt hs.2))
  have h5 : ∀ t ∈ Ioo (4:ℝ) 5,
      logDeriv (modularFormCompOfComplex f) (fdBoundary_H H t) * deriv (fdBoundary_H H) t =
      logDeriv (modularFormCompOfComplex f) (fdBoundary_seg5_H H t) *
        deriv (fdBoundary_seg5_H H) t := by
    intro t ht
    have h_eq := fdBoundary_H_eq_seg5_H (H := H) (by linarith [ht.1] : ¬(t ≤ 1))
      (by linarith [ht.1]) (by linarith [ht.1]) (by linarith [ht.1])
    rw [h_eq]; congr 1
    exact deriv_eq_of_nhd_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact fdBoundary_H_eq_seg5_H (H := H) (by linarith [hs.1]) (by linarith [hs.1])
        (by linarith [hs.1]) (by linarith [hs.1]))
  -- Split [0,5] into sub-intervals using adjacent intervals
  have hint_01 := hint_H.mono_set
    (show Set.uIcc 0 1 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc le_rfl (by norm_num))
  have hint_12 := hint_H.mono_set
    (show Set.uIcc 1 2 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have hint_23 := hint_H.mono_set
    (show Set.uIcc 2 3 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have hint_34 := hint_H.mono_set
    (show Set.uIcc 3 4 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (3:ℝ) ≤ 4), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have hint_45 := hint_H.mono_set
    (show Set.uIcc 4 5 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 5), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by norm_num) le_rfl)
  -- Split integral
  have split_01_12 := intervalIntegral.integral_add_adjacent_intervals hint_01 hint_12
  have split_012_23 := intervalIntegral.integral_add_adjacent_intervals
    (hint_01.trans hint_12) hint_23
  have split_0123_34 := intervalIntegral.integral_add_adjacent_intervals
    ((hint_01.trans hint_12).trans hint_23) hint_34
  have split_01234_45 := intervalIntegral.integral_add_adjacent_intervals
    (((hint_01.trans hint_12).trans hint_23).trans hint_34) hint_45
  rw [← split_01234_45, ← split_0123_34, ← split_012_23, ← split_01_12]
  -- Now rewrite each segment's integrand using ae congr
  -- Helper: on Ioc a b, the integrand matches a.e. since Ioo a b has full measure
  congr 1; congr 1; congr 1; congr 1
  · apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    filter_upwards [compl_mem_ae_iff.mpr (show volume ({(1:ℝ)} : Set ℝ) = 0 from by simp)]
      with t ht_ne ht_ioc
    exact h1 t ⟨ht_ioc.1, lt_of_le_of_ne ht_ioc.2 ht_ne⟩
  · apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2)]
    filter_upwards [compl_mem_ae_iff.mpr (show volume ({(2:ℝ)} : Set ℝ) = 0 from by simp)]
      with t ht_ne ht_ioc
    exact h2 t ⟨ht_ioc.1, lt_of_le_of_ne ht_ioc.2 ht_ne⟩
  · apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 3)]
    filter_upwards [compl_mem_ae_iff.mpr (show volume ({(3:ℝ)} : Set ℝ) = 0 from by simp)]
      with t ht_ne ht_ioc
    exact h3 t ⟨ht_ioc.1, lt_of_le_of_ne ht_ioc.2 ht_ne⟩
  · apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (by norm_num : (3:ℝ) ≤ 4)]
    filter_upwards [compl_mem_ae_iff.mpr (show volume ({(4:ℝ)} : Set ℝ) = 0 from by simp)]
      with t ht_ne ht_ioc
    exact h4 t ⟨ht_ioc.1, lt_of_le_of_ne ht_ioc.2 ht_ne⟩
  · apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)]
    filter_upwards [compl_mem_ae_iff.mpr (show volume ({(5:ℝ)} : Set ℝ) = 0 from by simp)]
      with t ht_ne ht_ioc
    exact h5 t ⟨ht_ioc.1, lt_of_le_of_ne ht_ioc.2 ht_ne⟩

/-! ### Nonvanishing on Arc Segments from Parameterized Integrability -/

/-- Transfer integrability from `fdBoundary_H H` on `[0,5]` to `fdBoundary_seg2` on `[1,2]`.

On `(1,2)`, `fdBoundary_H H` equals `fdBoundary_seg2` (arcs are H-independent). -/
private lemma seg2_integrability_of_hint_H {H : ℝ}
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5) :
    IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg2 t) * deriv fdBoundary_seg2 t) MeasureTheory.volume 1 2 := by
  have hint_12 := hint_H.mono_set
    (show Set.uIcc 1 2 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have h_ae_eq : (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc 1 2)]
      (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg2 t) * deriv fdBoundary_seg2 t) := by
    rw [Set.uIoc_of_le (by norm_num : (1:ℝ) ≤ 2)]
    have h_ioo_ae : Set.Ioo (1:ℝ) 2 ∈ ae (MeasureTheory.volume.restrict (Set.Ioc 1 2)) := by
      rw [mem_ae_iff, MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
      have hsub : (Set.Ioo (1:ℝ) 2)ᶜ ∩ Set.Ioc 1 2 ⊆ {2} := by
        intro x ⟨h1, h2⟩
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, Set.mem_Ioc] at h1 h2
        simp only [Set.mem_singleton_iff]
        rcases h1 with h | h <;> linarith [h2.1, h2.2]
      exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub)
        (MeasureTheory.measure_singleton 2).le) (zero_le _)
    filter_upwards [h_ioo_ae] with t ht
    have ht1 : ¬(t ≤ 1) := by linarith [ht.1]
    have ht2 : t ≤ 2 := le_of_lt ht.2
    have h_eq := fdBoundary_H_eq_seg2_H (H := H) ht1 ht2
    rw [h_eq, fdBoundary_seg2_H]; congr 1
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [fdBoundary_H_eq_seg2_H (H := H) (by linarith [hs.1]) (le_of_lt hs.2),
        fdBoundary_seg2_H])
  exact hint_12.congr_ae h_ae_eq

/-- Transfer integrability from `fdBoundary_H H` on `[0,5]` to `fdBoundary_seg3` on `[2,3]`. -/
private lemma seg3_integrability_of_hint_H {H : ℝ}
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5) :
    IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg3 t) * deriv fdBoundary_seg3 t) MeasureTheory.volume 2 3 := by
  have hint_23 := hint_H.mono_set
    (show Set.uIcc 2 3 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have h_ae_eq : (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc 2 3)]
      (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg3 t) * deriv fdBoundary_seg3 t) := by
    rw [Set.uIoc_of_le (by norm_num : (2:ℝ) ≤ 3)]
    have h_ioo_ae : Set.Ioo (2:ℝ) 3 ∈ ae (MeasureTheory.volume.restrict (Set.Ioc 2 3)) := by
      rw [mem_ae_iff, MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
      have hsub : (Set.Ioo (2:ℝ) 3)ᶜ ∩ Set.Ioc 2 3 ⊆ {3} := by
        intro x ⟨h1, h2⟩
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, Set.mem_Ioc] at h1 h2
        simp only [Set.mem_singleton_iff]
        rcases h1 with h | h <;> linarith [h2.1, h2.2]
      exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub)
        (MeasureTheory.measure_singleton 3).le) (zero_le _)
    filter_upwards [h_ioo_ae] with t ht
    have ht1 : ¬(t ≤ 1) := by linarith [ht.1]
    have ht2 : ¬(t ≤ 2) := by linarith [ht.1]
    have ht3 : t ≤ 3 := le_of_lt ht.2
    have h_eq := fdBoundary_H_eq_seg3_H (H := H) ht1 ht2 ht3
    rw [h_eq, fdBoundary_seg3_H]; congr 1
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [fdBoundary_H_eq_seg3_H (H := H) (by linarith [hs.1]) (by linarith [hs.1])
          (le_of_lt hs.2),
        fdBoundary_seg3_H])
  exact hint_23.congr_ae h_ae_eq

/-- Nonvanishing on seg2 from parameterized integrability.

Same as `nonvanishing_on_seg2_of_integrable` but uses `hint_H` for `fdBoundary_H H`. -/
lemma nonvanishing_on_seg2_of_integrable_H (hf : f ≠ 0) {H : ℝ}
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5) :
    ∀ t ∈ Set.uIcc 1 2, modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0 := by
  intro t₀ ht₀ h_zero
  have h_im_pos := fdBoundary_seg2_im_pos t₀ ht₀
  let z₀ := fdBoundary_seg2 t₀
  let s : UpperHalfPlane := ⟨z₀, h_im_pos⟩
  have h_fs_zero : f s = 0 := by
    have : modularFormCompOfComplex f z₀ = 0 := h_zero
    simp only [modularFormCompOfComplex, Function.comp_apply] at this
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at this
  obtain ⟨n, g_reg, hn_pos, hg_analytic, hg_ne_zero, _hn_eq, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s h_fs_zero
  have h_seg2_diff : DifferentiableAt ℝ fdBoundary_seg2 t₀ := by
    unfold fdBoundary_seg2
    apply DifferentiableAt.cexp
    apply DifferentiableAt.mul_const
    exact (DifferentiableAt.add (differentiableAt_const _)
      ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _)))
  have h_seg2_deriv_ne : deriv fdBoundary_seg2 t₀ ≠ 0 := by
    rw [deriv_fdBoundary_seg2_arc_eq]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (ne_of_gt (div_pos Real.pi_pos (by norm_num : (6:ℝ) > 0)))
      · exact Complex.I_ne_zero
    · exact exp_ne_zero _
  have h_seg2_deriv_cont : ContinuousAt (deriv fdBoundary_seg2) t₀ := by
    have : ContDiff ℝ ⊤ fdBoundary_seg2 := by
      unfold fdBoundary_seg2
      exact ContDiff.cexp ((contDiff_const.add ((Complex.ofRealCLM.contDiff.sub
        contDiff_const).mul contDiff_const)).mul contDiff_const)
    exact (this.continuous_deriv le_top).continuousAt
  have h_bigO := isBigO_sub_inv_logDeriv_arc f fdBoundary_seg2 t₀ z₀ rfl
    h_seg2_diff h_seg2_deriv_ne h_seg2_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
  have hint_seg2 := seg2_integrability_of_hint_H f hint_H
  have h_not_int := not_intervalIntegrable_of_sub_inv_isBigO_punctured h_bigO
    (by norm_num : (1:ℝ) ≠ 2) (by
      rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]
      exact ⟨(Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2) ▸ ht₀).1,
             (Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2) ▸ ht₀).2⟩)
  exact h_not_int hint_seg2

/-- Nonvanishing on seg3 from parameterized integrability. -/
lemma nonvanishing_on_seg3_of_integrable_H (hf : f ≠ 0) {H : ℝ}
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5) :
    ∀ t ∈ Set.uIcc 2 3, modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0 := by
  intro t₀ ht₀ h_zero
  have h_im_pos := fdBoundary_seg3_im_pos t₀ ht₀
  let z₀ := fdBoundary_seg3 t₀
  let s : UpperHalfPlane := ⟨z₀, h_im_pos⟩
  have h_fs_zero : f s = 0 := by
    have : modularFormCompOfComplex f z₀ = 0 := h_zero
    simp only [modularFormCompOfComplex, Function.comp_apply] at this
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im_pos] at this
  obtain ⟨n, g_reg, hn_pos, hg_analytic, hg_ne_zero, _hn_eq, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s h_fs_zero
  have h_seg3_diff : DifferentiableAt ℝ fdBoundary_seg3 t₀ := by
    unfold fdBoundary_seg3
    apply DifferentiableAt.cexp
    apply DifferentiableAt.mul_const
    exact (DifferentiableAt.add (differentiableAt_const _)
      ((Complex.ofRealCLM.differentiableAt.sub_const _).mul (differentiableAt_const _)))
  have h_seg3_deriv_ne : deriv fdBoundary_seg3 t₀ ≠ 0 := by
    rw [deriv_fdBoundary_seg3_arc_eq]
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact_mod_cast (ne_of_gt (div_pos Real.pi_pos (by norm_num : (6:ℝ) > 0)))
      · exact Complex.I_ne_zero
    · exact exp_ne_zero _
  have h_seg3_deriv_cont : ContinuousAt (deriv fdBoundary_seg3) t₀ := by
    have : ContDiff ℝ ⊤ fdBoundary_seg3 := by
      unfold fdBoundary_seg3
      exact ContDiff.cexp ((contDiff_const.add ((Complex.ofRealCLM.contDiff.sub
        contDiff_const).mul contDiff_const)).mul contDiff_const)
    exact (this.continuous_deriv le_top).continuousAt
  have h_bigO := isBigO_sub_inv_logDeriv_arc f fdBoundary_seg3 t₀ z₀ rfl
    h_seg3_diff h_seg3_deriv_ne h_seg3_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
  have hint_seg3 := seg3_integrability_of_hint_H f hint_H
  have h_not_int := not_intervalIntegrable_of_sub_inv_isBigO_punctured h_bigO
    (by norm_num : (2:ℝ) ≠ 3) (by
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)]
      exact ⟨(Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3) ▸ ht₀).1,
             (Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3) ▸ ht₀).2⟩)
  exact h_not_int hint_seg3

/-! ### Main Height-Parameterized PV Theorem -/

/-- **Main PV Result at height H**: The CW contour integral of f'/f around `∂𝒟_H`.

Same as `pv_integral_eq_modular_transformation` but with `fdBoundary_H H`
and `seg5_q_radius_H H`. The proof decomposes into:
1. Vertical edges cancel by T-invariance (works for any H)
2. Arc gives -k/12 by S-transformation (arcs are H-independent)
3. Horizontal edge gives +ord_∞ by q-expansion at radius `seg5_q_radius_H H` -/
theorem pv_integral_eq_modular_transformation_H (hf : f ≠ 0)
    {H : ℝ} (hH : 0 < H)
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) (seg5_q_radius_H H),
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    pv_integral f (fdBoundary_H H) 0 5 =
      -(2 * Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp f : ℂ))) := by
  -- Step 1: Decompose into segments
  rw [show pv_integral f (fdBoundary_H H) 0 5 = _ from
    pv_integral_decompose_segments_H f hint_H]
  -- Step 2: Rearrange
  have h_rearrange :
    pv_integral f (fdBoundary_seg1_H H) 0 1 +
    pv_integral f fdBoundary_seg2 1 2 +
    pv_integral f fdBoundary_seg3 2 3 +
    pv_integral f (fdBoundary_seg4_H H) 3 4 +
    pv_integral f (fdBoundary_seg5_H H) 4 5 =
    (pv_integral f (fdBoundary_seg1_H H) 0 1 + pv_integral f (fdBoundary_seg4_H H) 3 4) +
    (pv_integral f fdBoundary_seg2 1 2 + pv_integral f fdBoundary_seg3 2 3) +
    pv_integral f (fdBoundary_seg5_H H) 4 5 := by ring
  rw [h_rearrange]
  -- Step 3: Vertical cancellation
  rw [pv_integral_vertical_cancel_H f H]
  -- Step 4: Arc nonvanishing (from parameterized integrability)
  have h_arc_seg2_gne : ∀ t ∈ Set.uIcc 1 2,
      modularFormCompOfComplex f (fdBoundary_seg2 t) ≠ 0 :=
    nonvanishing_on_seg2_of_integrable_H f hf hint_H
  have h_arc_seg3_gne : ∀ t ∈ Set.uIcc 2 3,
      modularFormCompOfComplex f (fdBoundary_seg3 t) ≠ 0 :=
    nonvanishing_on_seg3_of_integrable_H f hf hint_H
  -- Step 5: Arc contribution (same arcs regardless of H)
  rw [arc_contribution_is_k_div_12 f h_arc_seg2_gne h_arc_seg3_gne]
  -- Step 6: Seg5 contribution at height H
  have h_seg5 : pv_integral f (fdBoundary_seg5_H H) 4 5 =
      2 * ↑Real.pi * I * ↑(orderAtCusp f) := by
    exact seg5_integral_eq_cusp_order_H f hf hH hcusp_nonvan
  rw [h_seg5]
  ring

/-! ### F3-M2: Nonvanishing Wrapper Infrastructure

These lemmas derive `IntervalIntegrable` from nonvanishing on `fdBoundary_H H`,
and conversely, nonvanishing from integrability (for `H > √3/2`). -/

/-! #### Im Positivity for fdBoundary_H -/

/-- The imaginary part of `fdBoundary_H H t` is positive for all `t ∈ [0, 5]` when `H > 0`. -/
private lemma fdBoundary_H_im_pos {H : ℝ} (hH : 0 < H) (t : ℝ) (ht : t ∈ Icc (0:ℝ) 5) :
    0 < (fdBoundary_H H t).im := by
  simp only [fdBoundary_H]
  split_ifs with h1 h2 h3 h4
  · -- Seg1: im = H - t*(H - √3/2) = H(1-t) + t*(√3/2)
    rw [show (1 / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I : ℂ) =
        ↑(1/2 : ℝ) + ↑(H - t * (H - Real.sqrt 3 / 2)) * I from by push_cast; ring]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
               mul_one, mul_zero, add_zero, zero_add]
    have hsqrt3 : Real.sqrt 3 / 2 > 0 := by positivity
    by_cases ht0 : t = 0
    · subst ht0; linarith
    · nlinarith [mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hsqrt3,
        mul_nonneg (show 0 ≤ 1 - t from by linarith) hH.le]
  · -- Seg2: im = sin(θ), θ ∈ [π/3, π/2]
    rw [show (↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
        ↑(Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I from by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  · -- Seg3: im = sin(θ), θ ∈ [π/2, 2π/3]
    rw [show (↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
        ↑(Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I from by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_im]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  · -- Seg4: im = √3/2 + (t-3)*(H - √3/2) = √3/2*(4-t) + H*(t-3)
    rw [show (-1 / 2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I : ℂ) =
        ↑(-1/2 : ℝ) + ↑(Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I from by
          push_cast; ring]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
               mul_one, mul_zero, add_zero, zero_add]
    have hsqrt3 : Real.sqrt 3 / 2 > 0 := by positivity
    nlinarith [not_le.mp h3, h4]
  · -- Seg5: im = H > 0
    rw [show (↑t - 9 / 2 + ↑H * I : ℂ) =
        ↑(t - 9/2 : ℝ) + ↑H * I from by push_cast; ring]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im,
               mul_one, mul_zero, add_zero, zero_add]
    linarith

/-! #### HasDerivWithinAt Uniqueness Helper -/

/-- Extract derivative equality from two `HasDerivWithinAt` via `UniqueDiffWithinAt`. -/
private lemma hasDerivWithinAt_unique' {f : ℝ → ℂ} {f' g' : ℂ} {s : Set ℝ} {x : ℝ}
    (h1 : HasDerivWithinAt f f' s x) (h2 : HasDerivWithinAt f g' s x)
    (hu : UniqueDiffWithinAt ℝ s x) : f' = g' := by
  have h := hu.eq h1.hasFDerivWithinAt h2.hasFDerivWithinAt
  have : (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) f') 1 =
         (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) g') 1 := by rw [h]
  simpa using this

/-! #### Local Reproduction of hasDerivAt_arc -/

/-- Derivative of the arc parameterization `t ↦ exp(π(1+t)/6 · I)`.
This reproduces the private `hasDerivAt_arc` from `FD_Boundary_Param.lean`. -/
private theorem hasDerivAt_arc_local (t : ℝ) :
    HasDerivAt (fun s => Complex.exp (↑(Real.pi * (1 + s) / 6) * I))
      (↑(Real.pi / 6) * I * Complex.exp (↑(Real.pi * (1 + t) / 6) * I)) t := by
  have hfun : (fun s : ℝ => Complex.exp (↑(Real.pi * (1 + s) / 6) * I)) =
      (fun s : ℝ => Complex.exp (↑(Real.pi / 6) * I + ↑(Real.pi / 6) * I * ↑s)) := by
    ext s; congr 1; push_cast; ring
  rw [hfun]
  have hinner : HasDerivAt (fun s : ℝ => ↑(Real.pi / 6) * I + ↑(Real.pi / 6) * I * (↑s : ℂ))
      (↑(Real.pi / 6) * I) t :=
    ((hasDerivAt_id (𝕜 := ℝ) t).ofReal_comp.const_mul (↑(Real.pi / 6) * I)).const_add _
      |>.congr_deriv (by simp only [Complex.ofReal_one, mul_one])
  exact hinner.cexp.congr_deriv (by rw [mul_comm]; congr 1; congr 1; push_cast; ring)

/-! #### Derivative Bound for fdBoundary_H -/

/-- The derivative of `fdBoundary_H H` is bounded on `[0, 5]`, including at partition points.

At partition points where `fdBoundary_H` is not differentiable, `deriv` returns `0`.
At partition points where it IS differentiable (hypothetically), we extract the derivative
value via the right-segment `HasDerivWithinAt` and `UniqueDiffWithinAt`. -/
private lemma fdBoundary_H_deriv_bound_all (H : ℝ) :
    ∃ M : ℝ, ∀ t ∈ Icc (0:ℝ) 5, ‖deriv (fdBoundary_H H) t‖ ≤ M := by
  refine ⟨|H - Real.sqrt 3 / 2| + 1, fun t ht => ?_⟩
  by_cases ht_part : t ∉ fdBoundary_H_partition
  · -- Off partition: compute derivative from HasDerivAt
    simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at ht_part
    push_neg at ht_part
    obtain ⟨h1, h3, h4⟩ := ht_part
    by_cases ht1 : t < 1
    · rw [(fdBoundary_H_hasDerivAt_seg1 H ht1).deriv,
          show -(↑(H - Real.sqrt 3 / 2) : ℂ) * I = -(↑(H - Real.sqrt 3 / 2) * I) from by ring,
          norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
      linarith [le_abs_self (H - Real.sqrt 3 / 2)]
    · push_neg at ht1
      by_cases ht3 : t < 3
      · have ht1' : 1 < t := lt_of_le_of_ne ht1 (Ne.symm h1)
        rw [(fdBoundary_H_hasDerivAt_arc H ht1' ht3).deriv, norm_mul, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
            Complex.norm_exp_ofReal_mul_I, mul_one,
            abs_of_pos (show (0:ℝ) < Real.pi / 6 by positivity)]
        linarith [Real.pi_le_four, abs_nonneg (H - Real.sqrt 3 / 2)]
      · push_neg at ht3
        by_cases ht4 : t < 4
        · have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm h3)
          rw [(fdBoundary_H_hasDerivAt_seg4 H ht3' ht4).deriv, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
          linarith [le_abs_self (H - Real.sqrt 3 / 2)]
        · push_neg at ht4
          have ht4' : 4 < t := lt_of_le_of_ne ht4 (Ne.symm h4)
          rw [(fdBoundary_H_hasDerivAt_seg5 H ht4').deriv, norm_one]
          linarith [abs_nonneg (H - Real.sqrt 3 / 2)]
  · -- At partition points {1, 3, 4}
    push_neg at ht_part
    simp only [fdBoundary_H_partition, Finset.mem_insert, Finset.mem_singleton] at ht_part
    -- Case split: DifferentiableAt or not
    by_cases hdiff : DifferentiableAt ℝ (fdBoundary_H H) t
    · -- DifferentiableAt: deriv = right-side derivative (extracted via uniqueness)
      rcases ht_part with rfl | rfl | rfl
      · -- t = 1: right = arc derivative at 1, norm = π/6 ≤ 1
        have h_arc_eq : (fun s => exp (↑(Real.pi * (1 + s) / 6) * I)) =ᶠ[nhdsWithin (1:ℝ) (Ici 1)]
            fdBoundary_H H := by
          filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (1:ℝ) < 3 by norm_num)),
              self_mem_nhdsWithin] with s hs1 (hs2 : (1:ℝ) ≤ s)
          rcases eq_or_lt_of_le hs2 with rfl | h
          · -- s = 1: exp(π/3*I) = fdBoundary_H H 1
            simp only [fdBoundary_H, show (1:ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
            rw [show (↑(Real.pi * (1 + 1) / 6 : ℝ) : ℂ) * I = ↑(Real.pi / 3 : ℝ) * I
              from by push_cast; ring, Complex.exp_mul_I,
              show (↑(Real.pi / 3 : ℝ) : ℂ) = ↑(Real.pi / 3) from rfl,
              ← Complex.ofReal_cos, ← Complex.ofReal_sin,
              Real.cos_pi_div_three, Real.sin_pi_div_three]
            push_cast; ring
          · exact (fdBoundary_H_eq_arc h (show s < 3 from hs1)).symm
        have h_arc_val : (fun s => exp (↑(Real.pi * (1 + s) / 6) * I)) 1 = fdBoundary_H H 1 := by
          simp only [fdBoundary_H, show (1:ℝ) ≤ 1 from le_refl 1, ↓reduceIte]
          rw [show (↑(Real.pi * (1 + 1) / 6 : ℝ) : ℂ) * I = ↑(Real.pi / 3 : ℝ) * I
            from by push_cast; ring, Complex.exp_mul_I,
            show (↑(Real.pi / 3 : ℝ) : ℂ) = ↑(Real.pi / 3) from rfl,
            ← Complex.ofReal_cos, ← Complex.ofReal_sin,
            Real.cos_pi_div_three, Real.sin_pi_div_three]
          push_cast; ring
        have h_right : HasDerivWithinAt (fdBoundary_H H)
            (↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + 1) / 6) * I)) (Ici 1) 1 :=
          (h_arc_eq.hasDerivWithinAt_iff h_arc_val).mp
            (hasDerivAt_arc_local 1).hasDerivWithinAt
        have h_full := hdiff.hasDerivAt.hasDerivWithinAt (s := Ici 1)
        rw [hasDerivWithinAt_unique' h_full h_right (uniqueDiffWithinAt_Ici (1:ℝ)),
            norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
            Complex.norm_exp_ofReal_mul_I, mul_one,
            abs_of_pos (show (0:ℝ) < Real.pi / 6 by positivity)]
        linarith [Real.pi_le_four, abs_nonneg (H - Real.sqrt 3 / 2)]
      · -- t = 3: right = seg4 at 3, norm = |H - √3/2|
        have h_seg4_eq : fdBoundary_seg4_H H =ᶠ[nhdsWithin (3:ℝ) (Ici 3)]
            fdBoundary_H H := by
          filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (show (3:ℝ) < 4 by norm_num)),
              self_mem_nhdsWithin] with s hs1 (hs2 : (3:ℝ) ≤ s)
          rcases eq_or_lt_of_le hs2 with rfl | h
          · -- s = 3: seg4(3) = fdBoundary_H H 3, both equal ρ
            rw [show fdBoundary_H H 3 = fdBoundary 3 from fdBoundary_H_at_three H,
                fdBoundary_at_three]
            simp only [fdBoundary_seg4_H, ellipticPoint_rho, ellipticPoint_rho']
            simp only [UpperHalfPlane.coe_mk_subtype]; push_cast; ring
          · have hs1' : s < 4 := hs1
            exact (fdBoundary_H_eq_seg4_H (by linarith) (by linarith)
              (by linarith) (le_of_lt hs1')).symm
        have h_seg4_val : fdBoundary_seg4_H H 3 = fdBoundary_H H 3 := by
          rw [show fdBoundary_H H 3 = fdBoundary 3 from fdBoundary_H_at_three H,
              fdBoundary_at_three]
          simp only [fdBoundary_seg4_H, ellipticPoint_rho, ellipticPoint_rho']
          simp only [UpperHalfPlane.coe_mk_subtype]; push_cast; ring
        have h_right : HasDerivWithinAt (fdBoundary_H H)
            ((↑(H - Real.sqrt 3 / 2) : ℂ) * I) (Ici 3) 3 :=
          (h_seg4_eq.hasDerivWithinAt_iff h_seg4_val).mp
            (hasDerivAt_fdBoundary_seg4_H H 3).hasDerivWithinAt
        have h_full := hdiff.hasDerivAt.hasDerivWithinAt (s := Ici 3)
        rw [hasDerivWithinAt_unique' h_full h_right (uniqueDiffWithinAt_Ici (3:ℝ)),
            norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
        linarith [le_abs_self (H - Real.sqrt 3 / 2)]
      · -- t = 4: right = seg5, norm = 1
        have h_seg5_eq : fdBoundary_seg5_H H =ᶠ[nhdsWithin (4:ℝ) (Ici 4)]
            fdBoundary_H H := by
          filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds (show (3:ℝ) < 4 by norm_num)
              (show (4:ℝ) < 5 by norm_num)), self_mem_nhdsWithin]
            with s hs1 (hs2 : (4:ℝ) ≤ s)
          rcases eq_or_lt_of_le hs2 with rfl | h
          · simp [fdBoundary_seg5_H, fdBoundary_H_at_four]; ring
          · exact (fdBoundary_H_eq_seg5_H (by linarith) (by linarith)
              (by linarith) (by linarith)).symm
        have h_seg5_val : fdBoundary_seg5_H H 4 = fdBoundary_H H 4 := by
          simp [fdBoundary_seg5_H, fdBoundary_H_at_four]; ring
        have h_right : HasDerivWithinAt (fdBoundary_H H) 1 (Ici 4) 4 :=
          (h_seg5_eq.hasDerivWithinAt_iff h_seg5_val).mp
            (hasDerivAt_fdBoundary_seg5_H H 4).hasDerivWithinAt
        have h_full := hdiff.hasDerivAt.hasDerivWithinAt (s := Ici 4)
        rw [hasDerivWithinAt_unique' h_full h_right (uniqueDiffWithinAt_Ici (4:ℝ)), norm_one]
        linarith [abs_nonneg (H - Real.sqrt 3 / 2)]
    · -- Not differentiable: deriv = 0
      rw [deriv_zero_of_not_differentiableAt hdiff, norm_zero]
      linarith [abs_nonneg (H - Real.sqrt 3 / 2)]

/-! #### Derivative ContinuousOn off Partition -/

/-- The derivative of `fdBoundary_H H` is continuous on `Icc 0 5 \ fdBoundary_H_partition`. -/
private lemma fdBoundary_H_deriv_continuousOn_off_partition' (H : ℝ) :
    ContinuousOn (deriv (fdBoundary_H H)) (Icc (0:ℝ) 5 \ ↑fdBoundary_H_partition) := by
  intro t ⟨ht_icc, ht_not_P⟩
  simp only [fdBoundary_H_partition, Finset.coe_insert, Finset.coe_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_not_P
  obtain ⟨h1, h3, h4⟩ := ht_not_P
  by_cases ht1 : t < 1
  · -- t ∈ [0, 1): deriv is eventually constant -(H-√3/2)*I
    have hev : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
        fun _ => -(↑(H - Real.sqrt 3 / 2) : ℂ) * I :=
      Filter.eventuallyEq_iff_exists_mem.mpr ⟨Iio 1, Iio_mem_nhds ht1,
        fun s hs => (fdBoundary_H_hasDerivAt_seg1 H hs).deriv⟩
    exact hev.continuousAt.continuousWithinAt
  · push_neg at ht1
    by_cases ht3 : t < 3
    · -- t ∈ (1, 3): arc derivative (smooth)
      have ht1' : 1 < t := lt_of_le_of_ne ht1 (Ne.symm h1)
      have hev : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
          fun s => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + s) / 6) * I) :=
        Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo 1 3, Ioo_mem_nhds ht1' ht3,
          fun s hs => (fdBoundary_H_hasDerivAt_arc H hs.1 hs.2).deriv⟩
      have hcont : Continuous
          (fun s : ℝ => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + s) / 6) * I)) := by
        apply Continuous.mul continuous_const
        apply Continuous.cexp
        apply Continuous.mul _ continuous_const
        exact continuous_ofReal.comp (by fun_prop)
      exact (hcont.continuousAt.congr hev.symm).continuousWithinAt
    · push_neg at ht3
      by_cases ht4 : t < 4
      · -- t ∈ (3, 4): seg4 derivative (constant)
        have ht3' : 3 < t := lt_of_le_of_ne ht3 (Ne.symm h3)
        have hev : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
            fun _ => (↑(H - Real.sqrt 3 / 2) : ℂ) * I :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo 3 4, Ioo_mem_nhds ht3' ht4,
            fun s hs => (fdBoundary_H_hasDerivAt_seg4 H hs.1 hs.2).deriv⟩
        exact hev.continuousAt.continuousWithinAt
      · -- t ∈ (4, 5]: seg5 derivative (constant 1)
        push_neg at ht4
        have ht4' : 4 < t := lt_of_le_of_ne ht4 (Ne.symm h4)
        have hev : deriv (fdBoundary_H H) =ᶠ[𝓝 t]
            fun _ => (1 : ℂ) :=
          Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioi 4, Ioi_mem_nhds ht4',
            fun s hs => (fdBoundary_H_hasDerivAt_seg5 H (show 4 < s from hs)).deriv⟩
        exact hev.continuousAt.continuousWithinAt

/-! #### ContinuousOn logDeriv on Image -/

omit hf in
/-- `logDeriv (modularFormCompOfComplex f)` is continuous on `fdBoundary_H H '' [0,5]`
when `f` is nonvanishing on the curve and `H > 0`. -/
private lemma logDeriv_continuousOn_fdBoundary_H_image_of_nonvanishing {H : ℝ} (hH : 0 < H)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ContinuousOn (logDeriv (modularFormCompOfComplex f)) (fdBoundary_H H '' Icc (0:ℝ) 5) := by
  intro z ⟨t, ht, hzt⟩
  rw [← hzt]
  exact (analyticAt_logDeriv_off_zeros f (fdBoundary_H H t)
    (fdBoundary_H_im_pos hH t ht) (h_nv t ht)).continuousAt.continuousWithinAt

/-! #### Main Integrability from Nonvanishing -/

omit hf in
/-- If `f` is nonvanishing on `fdBoundary_H H` and `H > 0`, then the logDeriv integrand
is interval-integrable on `[0, 5]`.

**Proof**: Uses `intervalIntegrable_pv_integrand_piecewiseC1` with partition `{1, 3, 4}`. -/
theorem intervalIntegrable_logDeriv_fdBoundary_H_of_nonvanishing {H : ℝ} (hH : 0 < H)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 := by
  apply intervalIntegrable_pv_integrand_piecewiseC1
    (P := fdBoundary_H_partition) (by norm_num : (0:ℝ) ≤ 5)
  · exact logDeriv_continuousOn_fdBoundary_H_image_of_nonvanishing f hH h_nv
  · exact (fdBoundary_H_continuous H).continuousOn
  · exact fdBoundary_H_deriv_continuousOn_off_partition' H
  · exact continuousOn_image_bounded (fdBoundary_H_continuous H).continuousOn
      (logDeriv_continuousOn_fdBoundary_H_image_of_nonvanishing f hH h_nv)
  · exact fdBoundary_H_deriv_bound_all H

/-! #### Iff Characterization: Integrability ↔ Nonvanishing on FD Boundary -/

/-- Transfer integrability from `fdBoundary_H H` on `[0,5]` to `fdBoundary_seg5_H` on `[4,5]`.

On `(4,5)`, `fdBoundary_H H` equals `fdBoundary_seg5_H H` (horizontal edge is H-independent). -/
private lemma seg5_integrability_of_hint_H {H : ℝ}
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5) :
    IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg5_H H t) * deriv (fdBoundary_seg5_H H) t) MeasureTheory.volume 4 5 := by
  have hint_45 := hint_H.mono_set
    (show Set.uIcc 4 5 ⊆ Set.uIcc 0 5 from by
      rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 5), Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]
      exact Set.Icc_subset_Icc (by norm_num) (by norm_num))
  have h_ae_eq : (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) =ᵐ[MeasureTheory.volume.restrict
        (Set.uIoc 4 5)]
      (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_seg5_H H t) * deriv (fdBoundary_seg5_H H) t) := by
    rw [Set.uIoc_of_le (by norm_num : (4:ℝ) ≤ 5)]
    have h_ioo_ae : Set.Ioo (4:ℝ) 5 ∈ ae (MeasureTheory.volume.restrict (Set.Ioc 4 5)) := by
      rw [mem_ae_iff, MeasureTheory.Measure.restrict_apply (measurableSet_Ioo.compl)]
      have hsub : (Set.Ioo (4:ℝ) 5)ᶜ ∩ Set.Ioc 4 5 ⊆ {5} := by
        intro x ⟨h1, h2⟩
        simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and_or, not_lt, Set.mem_Ioc] at h1 h2
        simp only [Set.mem_singleton_iff]
        rcases h1 with h | h <;> linarith [h2.1, h2.2]
      exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub)
        (MeasureTheory.measure_singleton 5).le) (zero_le _)
    filter_upwards [h_ioo_ae] with t ht
    have ht1 : ¬(t ≤ 1) := by linarith [ht.1]
    have ht2 : ¬(t ≤ 2) := by linarith [ht.1]
    have ht3 : ¬(t ≤ 3) := by linarith [ht.1]
    have ht4 : ¬(t ≤ 4) := by linarith [ht.1]
    have h_eq := fdBoundary_H_eq_seg5_H (H := H) ht1 ht2 ht3 ht4
    rw [h_eq, fdBoundary_seg5_H]; congr 1
    exact Filter.EventuallyEq.deriv_eq (by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      rw [fdBoundary_H_eq_seg5_H (H := H) (by linarith [hs.1]) (by linarith [hs.1])
          (by linarith [hs.1]) (by linarith [hs.1]),
        fdBoundary_seg5_H])
  exact hint_45.congr_ae h_ae_eq

/-- Forward direction: if logDeriv is integrable on `fdBoundary_H H`, then `f` is nonvanishing on the curve.

Requires `H > √3/2` to ensure all segments have positive imaginary part. -/
private lemma nonvanishing_on_fdBoundary_H_of_integrable (hf : f ≠ 0) {H : ℝ}
    (hH : Real.sqrt 3 / 2 < H)
    (hint_H : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5) :
    ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0 := by
  intro t₀ ht₀ h_zero
  have hH_pos : 0 < H := by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
  have h_im := fdBoundary_H_im_pos hH_pos t₀ ht₀
  let z₀ := fdBoundary_H H t₀
  let s : UpperHalfPlane := ⟨z₀, h_im⟩
  have h_fs_zero : f s = 0 := by
    simp only [modularFormCompOfComplex, Function.comp_apply] at h_zero
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos h_im] at h_zero
  obtain ⟨n, g_reg, hn_pos, hg_analytic, hg_ne_zero, _hn_eq, h_formula⟩ :=
    hasSimplePoleAt_logDeriv_of_zero f hf s h_fs_zero
  by_cases h_part : t₀ ∈ (fdBoundary_H_partition : Set ℝ)
  · -- Partition points: {1, 3, 4} — delegate to segment-specific nonvanishing lemmas
    simp only [fdBoundary_H_partition, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff] at h_part
    rcases h_part with rfl | rfl | rfl
    · -- t₀ = 1: convert to seg2 and delegate
      have h_val : fdBoundary_H H 1 = fdBoundary_seg2 1 := by
        rw [fdBoundary_H_at_one, fdBoundary_at_one]; symm
        simp only [fdBoundary_seg2, ellipticPoint_rho_plus_one, ellipticPoint_rho_plus_one']
        have h_angle : (↑Real.pi / 3 + (↑(1:ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3) : ℂ) =
            ↑Real.pi / 3 := by push_cast; ring
        rw [h_angle, Complex.exp_mul_I]
        have hπ3 : (↑Real.pi / 3 : ℂ) = ↑(Real.pi / 3 : ℝ) := by push_cast; ring
        rw [hπ3, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
            Real.cos_pi_div_three, Real.sin_pi_div_three]
        simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]; rfl
      rw [h_val] at h_zero
      exact nonvanishing_on_seg2_of_integrable_H f hf hint_H 1
        (by rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)]; exact ⟨le_refl _, by norm_num⟩) h_zero
    · -- t₀ = 3: convert to seg3 and delegate
      have h_val : fdBoundary_H H 3 = fdBoundary_seg3 3 := by
        rw [fdBoundary_H_at_three, fdBoundary_at_three]; symm
        simp only [fdBoundary_seg3, ellipticPoint_rho, ellipticPoint_rho']
        have h_angle : (↑Real.pi / 2 + (↑(3:ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2) : ℂ) =
            2 * ↑Real.pi / 3 := by push_cast; ring
        rw [h_angle, Complex.exp_mul_I]
        have h_cos : Real.cos (2 * Real.pi / 3) = -1/2 := by
          rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
              Real.cos_pi_sub, Real.cos_pi_div_three]; ring
        have h_sin : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
          rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
              Real.sin_pi_sub, Real.sin_pi_div_three]
        have h2π3 : (2 * ↑Real.pi / 3 : ℂ) = ↑(2 * Real.pi / 3 : ℝ) := by push_cast; ring
        rw [h2π3, ← Complex.ofReal_cos, ← Complex.ofReal_sin, h_cos, h_sin]
        simp only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
        rfl
      rw [h_val] at h_zero
      exact nonvanishing_on_seg3_of_integrable_H f hf hint_H 3
        (by rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)]; exact ⟨by norm_num, le_refl _⟩) h_zero
    · -- t₀ = 4: BigO approach with seg5
      have h_seg5_diff : DifferentiableAt ℝ (fdBoundary_seg5_H H) 4 :=
        (hasDerivAt_fdBoundary_seg5_H H 4).differentiableAt
      have h_seg5_deriv_ne : deriv (fdBoundary_seg5_H H) 4 ≠ 0 := by
        rw [(hasDerivAt_fdBoundary_seg5_H H 4).deriv]
        exact one_ne_zero
      have h_seg5_deriv_cont : ContinuousAt (deriv (fdBoundary_seg5_H H)) 4 := by
        have h_eq : deriv (fdBoundary_seg5_H H) = fun _ => (1 : ℂ) :=
          funext fun s => (hasDerivAt_fdBoundary_seg5_H H s).deriv
        rw [h_eq]; exact continuousAt_const
      have h_seg5_val : fdBoundary_seg5_H H 4 = z₀ := by
        show fdBoundary_seg5_H H 4 = fdBoundary_H H 4
        simp [fdBoundary_seg5_H, fdBoundary_H_at_four]; ring
      have h_bigO := isBigO_sub_inv_logDeriv_arc f (fdBoundary_seg5_H H) 4 z₀ h_seg5_val
        h_seg5_diff h_seg5_deriv_ne h_seg5_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
      have hint_seg5 := seg5_integrability_of_hint_H f hint_H
      exact absurd hint_seg5 (not_intervalIntegrable_of_sub_inv_isBigO_punctured h_bigO
        (by norm_num : (4:ℝ) ≠ 5) (by
          rw [Set.uIcc_of_le (by norm_num : (4:ℝ) ≤ 5)]
          exact ⟨by norm_num, by norm_num⟩))
  · -- Off-partition points: use BigO approach directly
    have h_not_part : t₀ ∉ (fdBoundary_H_partition : Set ℝ) := h_part
    simp only [fdBoundary_H_partition, Finset.coe_insert, Finset.coe_singleton,
      Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h_part
    obtain ⟨h1, h3, h4⟩ := h_part
    have h_diff_off := fdBoundary_H_differentiableAt_off_partition H h_not_part
    have h_deriv_ne : deriv (fdBoundary_H H) t₀ ≠ 0 := by
      by_cases ht1 : t₀ < 1
      · rw [(fdBoundary_H_hasDerivAt_seg1 H ht1).deriv]
        exact mul_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
          (sub_ne_zero.mpr (ne_of_gt hH)))) Complex.I_ne_zero
      · push_neg at ht1
        by_cases ht3 : t₀ < 3
        · rw [(fdBoundary_H_hasDerivAt_arc H (lt_of_le_of_ne ht1 (Ne.symm h1)) ht3).deriv]
          exact mul_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr
            (ne_of_gt (div_pos Real.pi_pos (by norm_num)))) Complex.I_ne_zero) (exp_ne_zero _)
        · push_neg at ht3
          by_cases ht4 : t₀ < 4
          · rw [(fdBoundary_H_hasDerivAt_seg4 H (lt_of_le_of_ne ht3 (Ne.symm h3)) ht4).deriv]
            exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
              (sub_ne_zero.mpr (ne_of_gt hH))) Complex.I_ne_zero
          · push_neg at ht4
            rw [(fdBoundary_H_hasDerivAt_seg5 H (lt_of_le_of_ne ht4 (Ne.symm h4))).deriv]
            exact one_ne_zero
    have h_deriv_cont : ContinuousAt (deriv (fdBoundary_H H)) t₀ := by
      by_cases ht1 : t₀ < 1
      · exact continuousAt_const.congr (Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Iio 1, Iio_mem_nhds ht1,
            fun s hs => (fdBoundary_H_hasDerivAt_seg1 H hs).deriv⟩).symm
      · push_neg at ht1
        by_cases ht3 : t₀ < 3
        · have ht1' : 1 < t₀ := lt_of_le_of_ne ht1 (Ne.symm h1)
          have hev : deriv (fdBoundary_H H) =ᶠ[𝓝 t₀]
              fun s => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + s) / 6) * I) :=
            Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo 1 3, Ioo_mem_nhds ht1' ht3,
              fun s hs => (fdBoundary_H_hasDerivAt_arc H hs.1 hs.2).deriv⟩
          have hcont : Continuous
              (fun s : ℝ => ↑(Real.pi / 6) * I * exp (↑(Real.pi * (1 + s) / 6) * I)) := by
            apply Continuous.mul continuous_const
            apply Continuous.cexp
            apply Continuous.mul _ continuous_const
            exact continuous_ofReal.comp (by fun_prop)
          exact hcont.continuousAt.congr hev.symm
        · push_neg at ht3
          by_cases ht4 : t₀ < 4
          · have ht3' : 3 < t₀ := lt_of_le_of_ne ht3 (Ne.symm h3)
            exact continuousAt_const.congr (Filter.eventuallyEq_iff_exists_mem.mpr
              ⟨Ioo 3 4, Ioo_mem_nhds ht3' ht4,
                fun s hs => (fdBoundary_H_hasDerivAt_seg4 H hs.1 hs.2).deriv⟩).symm
          · push_neg at ht4
            have ht4' : 4 < t₀ := lt_of_le_of_ne ht4 (Ne.symm h4)
            exact continuousAt_const.congr (Filter.eventuallyEq_iff_exists_mem.mpr
              ⟨Ioi 4, Ioi_mem_nhds ht4',
                fun s hs => (fdBoundary_H_hasDerivAt_seg5 H (show 4 < s from hs)).deriv⟩).symm
    have h_bigO := isBigO_sub_inv_logDeriv_arc f (fdBoundary_H H) t₀ z₀ rfl
      h_diff_off h_deriv_ne h_deriv_cont n hn_pos g_reg hg_analytic hg_ne_zero h_formula
    exact absurd hint_H (not_intervalIntegrable_of_sub_inv_isBigO_punctured h_bigO
      (by norm_num : (0:ℝ) ≠ 5)
      (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 5)]; exact ht₀))

/-- Characterization: logDeriv is integrable on `fdBoundary_H H` iff `f` is nonvanishing on the curve.

This combines the forward direction (integrability implies nonvanishing) with the backward
direction (nonvanishing implies integrability, which follows from continuity of logDeriv
on the curve image). Requires `H > √3/2` for positivity on the full contour. -/
theorem hint_H_iff_nonvanishing_fdBoundary_H (hf : f ≠ 0) {H : ℝ}
    (hH : Real.sqrt 3 / 2 < H) :
    IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 ↔
    ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0 := by
  constructor
  · exact nonvanishing_on_fdBoundary_H_of_integrable f hf hH
  · intro h_nv
    have hH_pos : 0 < H := by linarith [Real.sqrt_pos.mpr (show (0:ℝ) < 3 from by norm_num)]
    exact intervalIntegrable_logDeriv_fdBoundary_H_of_nonvanishing f hH_pos h_nv

end
