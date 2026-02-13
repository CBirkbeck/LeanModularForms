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

end
