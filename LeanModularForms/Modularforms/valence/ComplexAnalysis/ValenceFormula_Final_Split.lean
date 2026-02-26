/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.ValenceFormula_Final_Discharge
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# The Valence Formula — Axiom-Clean Public API (Split-Chain Route)

This file provides axiom-clean public theorems of the valence formula for
modular forms of level 1. Unlike `ValenceFormula_Final.lean` (which forwards
to the monolithic `ValenceFormula.lean` and inherits `sorryAx`), these theorems
forward to the split-chain discharge lemmas and use only standard axioms:
`[propext, Classical.choice, Quot.sound]`.

They require explicit data hypotheses (`zeros`, `hint`, `hcusp_nonvan`) that
expose internal constants. A future Track E2 will derive these from `hf : f ≠ 0`.

**Note**: The legacy `ValenceFormula_Final.lean` remains for backward compatibility only;
it carries `sorryAx` from the monolithic proof. Prefer these split-chain theorems for
any new downstream work.

## Main Theorems

### Exact-zeros forms (caller provides `zeros/hzeros/...`)
* `valenceFormula_split` — Orbifold form via `effectiveWinding`
* `valenceFormula_classical_split` — Classical form

### Superset forms (caller provides `S ⊇ {zeros in 𝒟'}`)
* `valenceFormula_split_from_S` — Orbifold superset form
* `valenceFormula_classical_split_from_S` — Classical superset form

### Larger-radius superset forms (accept `closedBall(0, r)` with `r ≥ seg5_q_radius`)
* `valenceFormula_split_from_S_of_larger_radius` — Orbifold, variable radius
* `valenceFormula_classical_split_from_S_of_larger_radius` — Classical, variable radius

## References

* [Serre, *A Course in Arithmetic*], Chapter VII
* [Miyake, *Modular Forms*], Section 2.4
* [Diamond-Shurman, *A First Course in Modular Forms*], Section 3.5
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup UpperHalfPlane
open scoped Real Interval UpperHalfPlane ModularForm

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Split-Chain Public Theorems (axiom-clean, no `sorryAx`)

These forward to the split-chain discharge lemmas in `ValenceFormula_Final_Discharge.lean`.
They require explicit data hypotheses (`zeros`, `hint`, `hcusp_nonvan`) but are
fully axiom-clean: `[propext, Classical.choice, Quot.sound]` only. -/

/-- **The Valence Formula** (split-chain, orbifold form via `effectiveWinding`).

Axiom-clean version: forwards to the split-chain proof via
`valence_formula_rearranged_rat`. Requires explicit zero data and integrability.

  `ord_∞(f) + Σ_{p ∈ zeros} effectiveWinding(p) · ord_p(f) = k/12` -/
theorem valenceFormula_split {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ s ∈ zeros, effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valence_formula_rearranged_rat f hf zeros hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-- **The Classical Valence Formula** (split-chain, axiom-clean).

Axiom-clean version: forwards to the split-chain proof via
`valence_formula_classical_form_rat`. Requires explicit zero data and integrability.

The sum over interior points uses `zeros.filter isInteriorPoint`.
Elliptic contributions appear as `if`-guarded terms for `i` and `ρ` membership. -/
theorem valenceFormula_classical_split {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (zeros : Finset UpperHalfPlane)
    (hzeros : ∀ s ∈ zeros, f s = 0)
    (hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟')
    (hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ zeros
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ zeros.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valence_formula_classical_form_rat f hf zeros hzeros hzeros_fd hzeros_complete hint hcusp_nonvan

/-! ## Order↔Zero Bridge Lemmas

These micro-lemmas bridge between `f p = 0` and `orderOfVanishingAt' f p ≠ 0`,
enabling the superset-form theorems to filter S down to the exact zero locus. -/

private lemma G_analyticAt {k : ℤ} (f : ModularForm (Gamma 1) k) (p : ℍ) :
    AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) := by
  have h_diffOn : DifferentiableOn ℂ (f ∘ ofComplex) {w | 0 < w.im} :=
    mdifferentiable_iff.mp f.holo'
  apply analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds p.im_pos] with w hw
  have h_eq : ∀ᶠ u in 𝓝 w, (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) u =
      (f ∘ ofComplex) u := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hw] with u hu
    simp only [Function.comp_apply, dif_pos hu, ofComplex_apply_of_im_pos hu]
  exact ((h_diffOn w hw).differentiableAt
    (isOpen_upperHalfPlaneSet.mem_nhds hw)).congr_of_eventuallyEq h_eq

private lemma G_eq_f {k : ℤ} (f : ModularForm (Gamma 1) k) (p : ℍ) :
    (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p := by
  have him : 0 < (↑p : ℂ).im := p.im_pos
  simp only [him, ↓reduceDIte]; congr 1

private lemma orderOfVanishingAt'_eq_zero_of_ne_zero {k : ℤ}
    (f : ModularForm (Gamma 1) k) (p : ℍ) (hp : f p ≠ 0) :
    orderOfVanishingAt' f p = 0 := by
  unfold orderOfVanishingAt'
  have h_nf := (G_analyticAt f p).meromorphicNFAt
  have hGp : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) ≠ 0 := by
    rw [G_eq_f]; exact hp
  rw [h_nf.meromorphicOrderAt_eq_zero_iff.mpr hGp]; rfl

private lemma orderOfVanishingAt'_ne_zero_of_eq_zero {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0) (p : ℍ) (hp : f p = 0) :
    orderOfVanishingAt' (⇑f) p ≠ 0 := by
  unfold orderOfVanishingAt'
  intro h_untop_eq
  have him : 0 < (↑p : ℂ).im := p.im_pos
  have h_nf := (G_analyticAt f p).meromorphicNFAt
  have h_ord_ne : meromorphicOrderAt
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑p) ≠ (0 : WithTop ℤ) := by
    intro h0; apply h_nf.meromorphicOrderAt_eq_zero_iff.mp h0
    simp only [him, ↓reduceDIte]; exact_mod_cast hp
  have h_top : meromorphicOrderAt
      (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑p) = ⊤ :=
    (WithTop.untop₀_eq_zero.mp h_untop_eq).resolve_left h_ord_ne
  rw [meromorphicOrderAt_eq_top_iff] at h_top
  have h_analOn : AnalyticOnNhd ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0)
      {w | 0 < w.im} := fun w hw => G_analyticAt f ⟨w, hw⟩
  have h_preconn : IsPreconnected {w : ℂ | 0 < w.im} :=
    ((convex_halfSpace_im_gt 0).isConnected
      ⟨Complex.I, by simp [Complex.I_im]⟩).isPreconnected
  have h_zero_on := h_analOn.eqOn_zero_of_preconnected_of_frequently_eq_zero
    h_preconn p.im_pos h_top.frequently
  apply hf; ext z
  have hG_eq : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (↑z) = f z := G_eq_f f z
  simp only [ModularForm.coe_zero, Pi.zero_apply, ← hG_eq, h_zero_on z.im_pos]

/-! ## Sum Rewriting Lemmas

These convert sums/guards indexed by `zeros := S.filter (f = 0)` to sums/guards
indexed by `S` directly, using that `orderOfVanishingAt' f p = 0` when `f p ≠ 0`. -/

private lemma if_mem_zeros_eq_if_mem_S {k : ℤ} (f : ModularForm (Gamma 1) k)
    (S : Finset UpperHalfPlane) (p : ℍ) :
    (if p ∈ S.filter (fun q => f q = 0)
      then (orderOfVanishingAt' f p : ℚ) else 0) =
    (if p ∈ S then (orderOfVanishingAt' f p : ℚ) else 0) := by
  by_cases hpS : p ∈ S
  · by_cases hfp : f p = 0
    · have : p ∈ S.filter (fun q => f q = 0) := Finset.mem_filter.mpr ⟨hpS, hfp⟩
      simp [this, hpS]
    · have : p ∉ S.filter (fun q => f q = 0) :=
        fun hmem => hfp (Finset.mem_filter.mp hmem).2
      simp [this, hpS, orderOfVanishingAt'_eq_zero_of_ne_zero f p hfp]
  · have : p ∉ S.filter (fun q => f q = 0) :=
      fun hmem => hpS (Finset.mem_filter.mp hmem).1
    simp [this, hpS]

private lemma sum_interior_zeros_eq_sum_interior_S {k : ℤ} (f : ModularForm (Gamma 1) k)
    (S : Finset UpperHalfPlane) :
    ∑ s ∈ (S.filter (fun p => f p = 0)).filter (fun s => isInteriorPoint s),
        (orderOfVanishingAt' f s : ℚ) =
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
        (orderOfVanishingAt' f s : ℚ) := by
  rw [Finset.filter_filter, Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl; intro p _
  by_cases hfp : f p = 0
  · simp [hfp]
  · simp [hfp, orderOfVanishingAt'_eq_zero_of_ne_zero f p hfp]

private lemma sum_ew_S_eq_sum_ew_zeros {k : ℤ} (f : ModularForm (Gamma 1) k)
    (S : Finset UpperHalfPlane) :
    ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      ∑ p ∈ S.filter (fun p => f p = 0),
        effectiveWinding p * (orderOfVanishingAt' f p : ℚ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro p _
  split_ifs with h
  · rfl
  · simp [orderOfVanishingAt'_eq_zero_of_ne_zero f p h]

/-! ## Superset-Form Theorems (Larger Radius)

These are the most general public theorems. They accept:
- A superset `S ⊇ {zeros in 𝒟'}` (via `hS_complete`)
- A cusp nonvanishing ball of any radius `r ≥ seg5_q_radius` (via `hr`)

The fixed-radius variants (`_from_S`) specialize these with `r := seg5_q_radius`. -/

/-- **The Valence Formula** (superset form, larger radius).

Most general orbifold form: accepts `S ⊇ {zeros in 𝒟'}` and
`closedBall(0, r)` with `r ≥ seg5_q_radius`.

  `ord_∞(f) + Σ_{p ∈ S} effectiveWinding(p) · ord_p(f) = k/12` -/
theorem valenceFormula_split_from_S_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 := by
  set zeros := S.filter (fun p => f p = 0)
  have hzeros : ∀ s ∈ zeros, f s = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟' :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros := by
    intro s hs_fd hs_zero; rw [Finset.mem_filter]
    exact ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf s hs_zero), hs_zero⟩
  rw [sum_ew_S_eq_sum_ew_zeros f S]
  have h := valence_formula_base_identity_of_larger_radius_rat f hf zeros hzeros hzeros_fd
    hzeros_complete hint hr hcusp_nonvan
  linarith

/-- **The Classical Valence Formula** (superset form, larger radius).

Most general classical form: accepts `S ⊇ {zeros in 𝒟'}` and
`closedBall(0, r)` with `r ≥ seg5_q_radius`.

  `ord_∞(f) + (1/2)·(if i ∈ S then ord_i else 0) + (1/3)·(if ρ ∈ S then ord_ρ else 0)
     + Σ_{interior p ∈ S} ord_p = k/12` -/
theorem valenceFormula_classical_split_from_S_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  set zeros := S.filter (fun p => f p = 0)
  have hzeros : ∀ s ∈ zeros, f s = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟' :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros := by
    intro s hs_fd hs_zero; rw [Finset.mem_filter]
    exact ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf s hs_zero), hs_zero⟩
  have h := valence_formula_classical_form_of_larger_radius_rat f hf zeros hzeros hzeros_fd
    hzeros_complete hint hr hcusp_nonvan
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_i'] at h
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_rho'] at h
  rw [sum_interior_zeros_eq_sum_interior_S f S] at h
  exact h

/-! ## Fixed-Radius Superset Forms (Specializations)

These specialize the larger-radius forms with `r := seg5_q_radius`, providing
backward-compatible API with the original fixed-radius signatures. -/

/-- **The Valence Formula** (superset form, fixed radius).

Specialization of `valenceFormula_split_from_S_of_larger_radius` with
`r := seg5_q_radius`. -/
theorem valenceFormula_split_from_S {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_larger_radius f hf S hS hS_complete hint le_rfl hcusp_nonvan

/-- **The Classical Valence Formula** (superset form, fixed radius).

Specialization of `valenceFormula_classical_split_from_S_of_larger_radius` with
`r := seg5_q_radius`. -/
theorem valenceFormula_classical_split_from_S {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_larger_radius f hf S hS hS_complete hint
    le_rfl hcusp_nonvan

/-! ## Nonvanishing Forms (replace `hint` with `h_nv`)

These accept a boundary nonvanishing hypothesis `h_nv` instead of `hint`.
Integrability is derived internally via `intervalIntegrable_logDeriv_fdBoundary_of_nonvanishing`.

The larger-radius variants additionally accept `closedBall(0, r)` with `r ≥ seg5_q_radius`.
The fixed-radius variants specialize with `r := seg5_q_radius`. -/

/-- **The Valence Formula** (superset form, nonvanishing boundary, larger radius).

Most general nonvanishing orbifold form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_nv` (boundary nonvanishing), and `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_split_from_S_of_nonvanishing_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 := by
  set zeros := S.filter (fun p => f p = 0)
  have hzeros : ∀ s ∈ zeros, f s = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟' :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros := by
    intro s hs_fd hs_zero; rw [Finset.mem_filter]
    exact ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf s hs_zero), hs_zero⟩
  rw [sum_ew_S_eq_sum_ew_zeros f S]
  have h := valence_formula_base_identity_of_nonvanishing_rat f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
  linarith

/-- **The Classical Valence Formula** (superset form, nonvanishing boundary, larger radius).

Most general nonvanishing classical form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_nv` (boundary nonvanishing), and `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_classical_split_from_S_of_nonvanishing_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  set zeros := S.filter (fun p => f p = 0)
  have hzeros : ∀ s ∈ zeros, f s = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟' :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros := by
    intro s hs_fd hs_zero; rw [Finset.mem_filter]
    exact ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf s hs_zero), hs_zero⟩
  have h := valence_formula_classical_form_of_nonvanishing_rat f hf zeros hzeros hzeros_fd
    hzeros_complete h_nv
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_i'] at h
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_rho'] at h
  rw [sum_interior_zeros_eq_sum_interior_S f S] at h
  exact h

/-- **The Valence Formula** (superset form, nonvanishing boundary, fixed radius).

Specialization of `valenceFormula_split_from_S_of_nonvanishing_of_larger_radius`
with `r := seg5_q_radius`. -/
theorem valenceFormula_split_from_S_of_nonvanishing {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_nonvanishing_of_larger_radius f hf S hS hS_complete
    h_nv le_rfl hcusp_nonvan

/-- **The Classical Valence Formula** (superset form, nonvanishing boundary, fixed radius).

Specialization of `valenceFormula_classical_split_from_S_of_nonvanishing_of_larger_radius`
with `r := seg5_q_radius`. -/
theorem valenceFormula_classical_split_from_S_of_nonvanishing {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_nv : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary t) ≠ 0)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_nonvanishing_of_larger_radius f hf S hS hS_complete
    h_nv le_rfl hcusp_nonvan

/-! ## Superset Crossing-Cauchy Forms (Larger Radius)

These accept `S ⊇ {zeros in 𝒟'}`, `hint`, `h_pv_eq_residue` (the pre-composed
residue-side result), and `closedBall(0, r)` with `r ≥ seg5_q_radius`.

The `h_pv_eq_residue` references the sum over `S.filter (fun p => f p = 0)` (the zero
locus within `S`). Non-zero points contribute 0 to the `S`-indexed sum. -/

/-- **The Valence Formula** (superset form, crossing-Cauchy, larger radius).

Most general crossing-Cauchy orbifold form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_pv_eq_residue`, and `closedBall(0, r)` with `r ≥ seg5_q_radius`.

  `ord_∞(f) + Σ_{p ∈ S} effectiveWinding(p) · ord_p(f) = k/12` -/
theorem valenceFormula_split_from_S_of_crossingCauchy_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 := by
  rw [sum_ew_S_eq_sum_ew_zeros f S]
  have h := valence_formula_base_identity_of_crossingCauchy_rat f hf
    (S.filter (fun p => f p = 0)) hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
    h_pv_eq_residue
  linarith

/-- **The Classical Valence Formula** (superset form, crossing-Cauchy, larger radius).

Most general crossing-Cauchy classical form: accepts `S ⊇ {zeros in 𝒟'}`,
`h_pv_eq_residue`, and `closedBall(0, r)` with `r ≥ seg5_q_radius`. -/
theorem valenceFormula_classical_split_from_S_of_crossingCauchy_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  have h := valence_formula_classical_form_of_crossingCauchy_rat f hf
    (S.filter (fun p => f p = 0)) hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
    h_pv_eq_residue
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_i'] at h
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_rho'] at h
  rw [sum_interior_zeros_eq_sum_interior_S f S] at h
  exact h

/-! ## Fixed-Radius Superset Crossing-Cauchy Forms (Specializations)

These specialize the larger-radius crossing-Cauchy forms with
`r := seg5_q_radius`, providing backward-compatible API. -/

/-- **The Valence Formula** (superset form, crossing-Cauchy, fixed radius).

Specialization of `valenceFormula_split_from_S_of_crossingCauchy_of_larger_radius` with
`r := seg5_q_radius`. -/
theorem valenceFormula_split_from_S_of_crossingCauchy {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_crossingCauchy_of_larger_radius f hf S hS hS_complete hint
    le_rfl hcusp_nonvan h_pv_eq_residue

/-- **The Classical Valence Formula** (superset form, crossing-Cauchy, fixed radius).

Specialization of `valenceFormula_classical_split_from_S_of_crossingCauchy_of_larger_radius`
with `r := seg5_q_radius`. -/
theorem valenceFormula_classical_split_from_S_of_crossingCauchy {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0)
    (h_pv_eq_residue : pv_integral f fdBoundary 0 5 =
      -(2 * Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
        (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_crossingCauchy_of_larger_radius f hf S hS hS_complete
    hint le_rfl hcusp_nonvan h_pv_eq_residue

/-! ## Superset Crossing-Cauchy Auto Forms (No h_cc, No h_pv_eq_residue)

These accept `S ⊇ {zeros in 𝒟'}`, `hint`, `hcusp_nonvan`, and derive everything
internally. When `hint` holds, the boundary avoids all zeros, so the crossing-Cauchy
condition is vacuously satisfied. No `h_cc` or `h_pv_eq_residue` needed.

The larger-radius variants additionally accept `closedBall(0, r)` with `r ≥ seg5_q_radius`.
The fixed-radius variants specialize with `r := seg5_q_radius`. -/

/-- **The Valence Formula** (superset form, auto integrability, larger radius, no `h_cc`).

Most general auto orbifold form: derives PV residue identity from `hint` internally. -/
theorem valenceFormula_split_from_S_of_crossingCauchy_auto_of_integrable_of_larger_radius {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 := by
  set zeros := S.filter (fun p => f p = 0)
  have hzeros : ∀ s ∈ zeros, f s = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟' :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros := by
    intro s hs_fd hs_zero; rw [Finset.mem_filter]
    exact ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf s hs_zero), hs_zero⟩
  rw [sum_ew_S_eq_sum_ew_zeros f S]
  have h := valence_formula_base_identity_of_crossingCauchy_auto_of_integrable_rat f hf zeros
    hzeros hzeros_fd hzeros_complete hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
  linarith

/-- **The Classical Valence Formula** (superset form, auto integrability, larger radius, no `h_cc`). -/
theorem valenceFormula_classical_split_from_S_of_crossingCauchy_auto_of_integrable_of_larger_radius
    {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    {r : ℝ} (hr : seg5_q_radius ≤ r)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) r,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
  set zeros := S.filter (fun p => f p = 0)
  have hzeros : ∀ s ∈ zeros, f s = 0 := fun s hs => (Finset.mem_filter.mp hs).2
  have hzeros_fd : ∀ s ∈ zeros, s ∈ 𝒟' :=
    fun s hs => hS s (Finset.mem_filter.mp hs).1
  have hzeros_complete : ∀ s, s ∈ 𝒟' → f s = 0 → s ∈ zeros := by
    intro s hs_fd hs_zero; rw [Finset.mem_filter]
    exact ⟨hS_complete s hs_fd (orderOfVanishingAt'_ne_zero_of_eq_zero f hf s hs_zero), hs_zero⟩
  have h := valence_formula_classical_form_of_crossingCauchy_auto_of_integrable_rat f hf zeros
    hzeros hzeros_fd hzeros_complete hint
    (fun q hq hq0 => hcusp_nonvan q (Metric.closedBall_subset_closedBall hr hq) hq0)
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_i'] at h
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_rho'] at h
  rw [sum_interior_zeros_eq_sum_interior_S f S] at h
  exact h

/-- **The Valence Formula** (superset form, auto integrability, fixed radius, no `h_cc`). -/
theorem valenceFormula_split_from_S_of_crossingCauchy_auto_of_integrable {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_split_from_S_of_crossingCauchy_auto_of_integrable_of_larger_radius f hf S hS
    hS_complete hint le_rfl hcusp_nonvan

/-- **The Classical Valence Formula** (superset form, auto integrability, fixed radius, no `h_cc`). -/
theorem valenceFormula_classical_split_from_S_of_crossingCauchy_auto_of_integrable {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hint : IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
      (fdBoundary t) * deriv fdBoundary t) MeasureTheory.volume 0 5)
    (hcusp_nonvan : ∀ q ∈ Metric.closedBall (0 : ℂ) seg5_q_radius,
        q ≠ 0 → SlashInvariantFormClass.cuspFunction (1 : ℕ) f q ≠ 0) :
    (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ S.filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 :=
  valenceFormula_classical_split_from_S_of_crossingCauchy_auto_of_integrable_of_larger_radius f hf
    S hS hS_complete hint le_rfl hcusp_nonvan

/-! ## Auto-Cusp Superset Forms (No `hcusp_nonvan`)

These derive cusp nonvanishing from `hf : f ≠ 0` via `modular_side_auto_cusp_of_integrable`.
The result is existential: `∃ H₀ > √3/2`, for `H ≥ H₀`, given integrability and the
residue-side result at height H, the valence formula identity holds in ℚ.

Unlike the variants above which require `hcusp_nonvan`, these operate on the parameterized
boundary curve `fdBoundary_H H` (not the fixed `fdBoundary`). The algebraic conclusion
(`ord_∞ + Σ ew·ord = k/12`) is curve-independent. -/

/-- **The Valence Formula** (superset form, auto-cusp, no `hcusp_nonvan`).

From `hf : f ≠ 0`, cusp nonvanishing is derived automatically for heights `H ≥ H₀`.
The caller provides integrability at height H and the residue-side result
`h_pv_eq_residue` (at height H, over `S.filter (f = 0)`). -/
theorem valenceFormula_split_from_S_auto_cusp {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
          (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := valence_formula_base_identity_auto_cusp f hf
    (S.filter (fun p => f p = 0))
  refine ⟨H₀, hH₀_gt, fun {H} hH hint_H h_pv => ?_⟩
  rw [sum_ew_S_eq_sum_ew_zeros f S]
  have h_base := h_auto hH hint_H h_pv
  have h_rat : ∑ s ∈ S.filter (fun p => f p = 0),
      effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by exact_mod_cast h_base
  linarith

/-- **The Classical Valence Formula** (superset form, auto-cusp, no `hcusp_nonvan`).

From `hf : f ≠ 0`, cusp nonvanishing is derived automatically for heights `H ≥ H₀`.
The caller provides integrability at height H and the residue-side result. -/
theorem valenceFormula_classical_split_from_S_auto_cusp {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        IntervalIntegrable (fun t => logDeriv (modularFormCompOfComplex f)
          (fdBoundary_H H t) * deriv (fdBoundary_H H) t) MeasureTheory.volume 0 5 →
        pv_integral f (fdBoundary_H H) 0 5 =
          -(2 * Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ S.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := valence_formula_classical_form_auto_cusp f hf
    (S.filter (fun p => f p = 0))
  refine ⟨H₀, hH₀_gt, fun {H} hH hint_H h_pv => ?_⟩
  have h_C := h_auto hH hint_H h_pv
  have h : (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S.filter (fun p => f p = 0)
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S.filter (fun p => f p = 0)
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ (S.filter (fun p => f p = 0)).filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
    apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
    push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
    exact h_C
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_i'] at h
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_rho'] at h
  rw [sum_interior_zeros_eq_sum_interior_S f S] at h
  exact h

/-! ## Auto-Cusp Generalized PV Superset Forms (via CPV modular side)

These use `pv_integral_logDeriv` with `fdBoundaryArcSingularSet` instead of `pv_integral`,
replacing `IntervalIntegrable` with local nonvanishing hypotheses. -/

/-- **The Valence Formula** (superset form, auto-cusp, generalized PV).

From `hf : f ≠ 0`, cusp nonvanishing is derived automatically for heights `H ≥ H₀`.
The caller provides arc nonvanishing, vertical nonvanishing, and the CPV residue-side
result `h_cpv` (at height H, over `S.filter (f = 0)`). -/
theorem valenceFormula_split_from_S_auto_cusp_generalizedPV {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := valence_formula_base_identity_auto_cusp_generalizedPV f hf
    (S.filter (fun p => f p = 0)) h_arc_nv
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv h_cpv => ?_⟩
  rw [sum_ew_S_eq_sum_ew_zeros f S]
  have h_base := h_auto hH h_vert_nv h_cpv
  have h_rat : ∑ s ∈ S.filter (fun p => f p = 0),
      effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by exact_mod_cast h_base
  linarith

/-- **The Classical Valence Formula** (superset form, auto-cusp, generalized PV).

From `hf : f ≠ 0`, cusp nonvanishing is derived automatically for heights `H ≥ H₀`.
Uses `pv_integral_logDeriv` with `fdBoundaryArcSingularSet`. -/
theorem valenceFormula_classical_split_from_S_auto_cusp_generalizedPV {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ)) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ S.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ := valence_formula_classical_form_auto_cusp_generalizedPV f hf
    (S.filter (fun p => f p = 0)) h_arc_nv
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv h_cpv => ?_⟩
  have h_C := h_auto hH h_vert_nv h_cpv
  have h : (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S.filter (fun p => f p = 0)
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S.filter (fun p => f p = 0)
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ (S.filter (fun p => f p = 0)).filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
    apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
    push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
    exact h_C
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_i'] at h
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_rho'] at h
  rw [sum_interior_zeros_eq_sum_interior_S f S] at h
  exact h

/-! ## Auto-Cusp Generalized PV + Residue-Auto Superset Forms

These compose the modular-side with a residue-auto provider, removing
`h_cpv_eq_residue` from the per-height API. Only `h_vert_nv` remains per height. -/

/-- **The Valence Formula** (superset form, auto-cusp, generalizedPV, residue-auto).

No `h_cpv_eq_residue` at each height — the residue-auto provider is consumed once. -/
theorem valenceFormula_split_from_S_auto_cusp_generalizedPV_of_residue_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          ∑ p ∈ S, effectiveWinding p * (orderOfVanishingAt' f p : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_base_identity_auto_cusp_generalizedPV_of_residue_auto f hf
      (S.filter (fun p => f p = 0)) h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  rw [sum_ew_S_eq_sum_ew_zeros f S]
  have h_base := h_auto hH h_vert_nv
  have h_rat : ∑ s ∈ S.filter (fun p => f p = 0),
      effectiveWinding s * (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 - (orderAtCusp' f : ℚ) := by exact_mod_cast h_base
  linarith

/-- **The Classical Valence Formula** (superset form, auto-cusp, generalizedPV, residue-auto).

No `h_cpv_eq_residue` at each height. -/
theorem valenceFormula_classical_split_from_S_auto_cusp_generalizedPV_of_residue_auto {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (_hS : ∀ p ∈ S, p ∈ 𝒟')
    (_hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_arc_nv : ∀ t ∈ Set.Ioo (1:ℝ) 3, t ≠ 2 →
        modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0)
    (h_residue_auto : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 fdBoundaryArcSingularSet =
          -(2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            (effectiveWinding s : ℂ) * (orderOfVanishingAt' f s : ℂ))) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        (∀ t ∈ Set.Ioo (0:ℝ) 1,
            modularFormCompOfComplex f (fdBoundary_H H t) ≠ 0) →
        (orderAtCusp' f : ℚ) +
          (1/2 : ℚ) * (if ellipticPoint_i' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
          (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S
            then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
          ∑ s ∈ S.filter (fun s => isInteriorPoint s),
              (orderOfVanishingAt' f s : ℚ) =
          (k : ℚ) / 12 := by
  obtain ⟨H₀, hH₀_gt, h_auto⟩ :=
    valence_formula_classical_form_auto_cusp_generalizedPV_of_residue_auto f hf
      (S.filter (fun p => f p = 0)) h_arc_nv h_residue_auto
  refine ⟨H₀, hH₀_gt, fun {H} hH h_vert_nv => ?_⟩
  have h_C := h_auto hH h_vert_nv
  have h : (orderAtCusp' f : ℚ) +
      (1/2 : ℚ) * (if ellipticPoint_i' ∈ S.filter (fun p => f p = 0)
        then (orderOfVanishingAt' f ellipticPoint_i' : ℚ) else 0) +
      (1/3 : ℚ) * (if ellipticPoint_rho' ∈ S.filter (fun p => f p = 0)
        then (orderOfVanishingAt' f ellipticPoint_rho' : ℚ) else 0) +
      ∑ s ∈ (S.filter (fun p => f p = 0)).filter (fun s => isInteriorPoint s),
          (orderOfVanishingAt' f s : ℚ) =
      (k : ℚ) / 12 := by
    apply_fun (Rat.cast : ℚ → ℂ) using Rat.cast_injective
    push_cast [apply_ite (Rat.cast : ℚ → ℂ)]
    exact h_C
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_i'] at h
  rw [if_mem_zeros_eq_if_mem_S f S ellipticPoint_rho'] at h
  rw [sum_interior_zeros_eq_sum_interior_S f S] at h
  exact h

/-! ## Generalized Winding Number Valence Formula via CPV (Superset Form)

These are the gWN variants from the F7-B assembly chain. The sum is over `S`
(not `S.filter (f = 0)`), using the fact that `orderOfVanishingAt' f p = 0`
when `f p ≠ 0`. -/

private lemma sum_gWN_S_eq_sum_gWN_zeros {k : ℤ} (f : ModularForm (Gamma 1) k)
    (S : Finset UpperHalfPlane) (H : ℝ) :
    ∑ p ∈ S,
      generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑p : ℂ) *
        (orderOfVanishingAt' f p : ℂ) =
    ∑ p ∈ S.filter (fun p => f p = 0),
      generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑p : ℂ) *
        (orderOfVanishingAt' f p : ℂ) := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl; intro p _
  split_ifs with h
  · rfl
  · simp [orderOfVanishingAt'_eq_zero_of_ne_zero f p h]

/-- **Generalized Winding Number Valence Formula via CPV** (superset form).

Same as `valence_formula_gWN_cpv_from_S` but sums over `S` instead of
`S.filter (f = 0)`. For non-zero points the term vanishes because
`orderOfVanishingAt' f p = 0`. -/
theorem valenceFormula_split_gWN_cpv_from_S {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_oncurve_arc : ∀ t ∈ Set.Ioo (1:ℝ) 3,
        modularFormCompOfComplex f (fdBoundary_H 1 t) = 0 →
        fdBoundary_H 1 t ∈ (↑(S_arc_of_S S) : Set ℂ))
    (h_oncurve_vert : ∀ (H' : ℝ), Real.sqrt 3 / 2 < H' → ∀ t ∈ Set.Ioo (0:ℝ) 1,
        modularFormCompOfComplex f (fdBoundary_H H' t) = 0 →
        (fdBoundary_H H' t : ℂ) ∈ (↑(S_vert_of_S S) : Set ℂ))
    (h_residue_provider : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc_of_S S ∪ S_vert_of_S S) =
          2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
              (orderOfVanishingAt' f s : ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S,
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  obtain ⟨H₀, hH₀, h⟩ := valence_formula_gWN_cpv_from_S f hf S hS hS_complete
    h_oncurve_arc h_oncurve_vert h_residue_provider
  exact ⟨H₀, hH₀, fun hH => by rw [sum_gWN_S_eq_sum_gWN_zeros]; exact h hH⟩

/-- **Generalized Winding Number Valence Formula via CPV — Auto Capture** (superset form).

Same as `valenceFormula_split_gWN_cpv_from_S` but without `h_oncurve_arc` or `h_oncurve_vert`.
These are derived automatically from `hS_complete` and the geometry of the fundamental domain.

Sums over `S` instead of `S.filter (f = 0)`. -/
theorem valenceFormula_split_gWN_cpv_from_S_auto_capture {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (h_residue_provider : ∃ H₁ : ℝ, Real.sqrt 3 / 2 < H₁ ∧
      ∀ {H : ℝ}, H₁ ≤ H →
        pv_integral_logDeriv f (fdBoundary_H H) 0 5 (S_arc_of_S S ∪ S_vert_of_S S) =
          2 * ↑Real.pi * Complex.I * ∑ s ∈ S.filter (fun p => f p = 0),
            generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
              (orderOfVanishingAt' f s : ℂ)) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S,
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  obtain ⟨H₀, hH₀, h⟩ := valence_formula_gWN_cpv_from_S_auto_capture f hf S hS hS_complete
    h_residue_provider
  exact ⟨H₀, hH₀, fun hH => by rw [sum_gWN_S_eq_sum_gWN_zeros]; exact h hH⟩

/-- **Generalized Winding Number Valence Formula — OnCurvePVProvider** (superset form).

Same as `valenceFormula_split_gWN_cpv_from_S_auto_capture` but takes `OnCurvePVProvider`
instead of `h_residue_provider`. The residue identity is derived internally from
the CPV existence hypotheses. Sums over `S` instead of `S.filter (f = 0)`. -/
theorem valenceFormula_split_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider {k : ℤ}
    (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)
    (S : Finset UpperHalfPlane)
    (hS : ∀ p ∈ S, p ∈ 𝒟')
    (hS_complete : ∀ p, p ∈ 𝒟' → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (hPV : OnCurvePVProvider f S) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧
      ∀ {H : ℝ}, H₀ ≤ H →
        ∑ s ∈ S,
          generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) *
            (orderOfVanishingAt' f s : ℂ) =
          -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  obtain ⟨H₀, hH₀, h⟩ := valence_formula_gWN_cpv_from_S_auto_capture_of_OnCurvePVProvider
    f hf S hS hS_complete hPV
  exact ⟨H₀, hH₀, fun hH => by rw [sum_gWN_S_eq_sum_gWN_zeros]; exact h hH⟩

end
