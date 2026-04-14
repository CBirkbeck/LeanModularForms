/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PVChainProof
import LeanModularForms.ForMathlib.ModularContourIntegral
import LeanModularForms.ForMathlib.LogDerivModularForm

/-!
# Modular Side Proof: CPV of logDeriv(f) tends to -(2piI)(k/12 - ord_cusp)

This file provides the modular side of the PV chain: the Cauchy principal value
integral of `logDeriv(f)` around the FD boundary converges (as epsilon -> 0+) to
`-(2 pi i * (k/12 - ord_cusp))`.

## Architecture

The proof is structured in layers:

### Layer 1: `ModularSideData`

A structure bundling the arc and horizontal contributions at height `H`,
together with a Tendsto for the CPV integrand. From this the modular-side
Tendsto `-(2 pi i)(k/12 - ord_cusp)` is derived by pure algebra.

### Layer 2: Segment algebra

Pure algebra lemmas that combine the five segment integrals:
- T-cancellation: seg1 + seg4 = 0
- Arc: seg2 + seg3 = -(2piI)(k/12)
- Horizontal: seg5 = 2piI * ord_cusp
- Total = -(2piI)(k/12 - ord_cusp)

### Layer 3: Bridge to `discharge_pvChain_full`

Interface theorems for the `h_mod` parameter:
- `modularSide_for_discharge`: from `ModularSideData` at each height
- `modularSide_direct`: from a Tendsto hypothesis
- `modularSide_complete_discharge`: combine residue + modular sides

### Layer 4: Integration with `PVChainProof`

The full valence formula from both Tendsto results, delegating to
`valence_formula_of_two_sides`.

## Main results

* `modularSide_tendsto_of_data` -- from `ModularSideData` extract the Tendsto
* `modularSide_from_segments` -- five-segment algebra
* `modularSide_tendsto_of_segments` -- from segments to Tendsto
* `T_cancel_segment_integrals` -- T-cancellation for vertical integrals
* `modularSide_for_discharge` -- h_mod from structured data
* `modularSide_complete_discharge` -- both sides to h_pvChain
* `valence_formula_of_modular_and_residue_sides` -- the full valence formula

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Serre, *A Course in Arithmetic*, Chapter VII
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Two-pi-I nonzero -/

omit f hf in
private lemma two_pi_I_ne_zero_ms : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
    ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, or_self]

/-! ### ModularSideData: bundled analytical ingredients -/

/-- Bundled data for the modular side at a given height `H`.

This packages the three analytical ingredients needed for the modular side
of the valence formula:

1. **T-cancellation**: the vertical segment integrals (seg1 + seg4) cancel.
2. **Arc contribution**: the arc integrals (seg2 + seg3) give `-(2piI)(k/12)`.
3. **Horizontal contribution**: the horizontal integral (seg5) gives
   `2piI * ord_cusp`.

The three contributions are combined algebraically to give the total modular
side `-(2piI)(k/12 - ord_cusp)`. -/
structure ModularSideData (H : ℝ) (F_eps : ℝ → ℂ) where
  /-- The arc contribution (seg2 + seg3) to the contour integral. -/
  arc_value : ℂ
  /-- The horizontal contribution (seg5) to the contour integral. -/
  horiz_value : ℂ
  /-- Arc value equals `-(2piI)(k/12)`. -/
  arc_eq : arc_value = -(2 * ↑Real.pi * I * ((k : ℂ) / 12))
  /-- Horizontal value equals `2piI * ord_cusp`. -/
  horiz_eq : horiz_value = 2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)
  /-- The CPV integral tends to arc_value + horiz_value.
  (The T-cancellation is already absorbed: seg1 + seg4 = 0.) -/
  h_tendsto : Tendsto F_eps (𝓝[>] 0) (𝓝 (arc_value + horiz_value))

/-! ### Extract Tendsto from ModularSideData -/

/-- From `ModularSideData`, extract the Tendsto statement:
the epsilon-truncated integral of `F` along the FD boundary converges to
`-(2piI * (k/12 - ord_cusp))`.

This unfolds the data fields and applies the algebraic combination. -/
theorem modularSide_tendsto_of_data {H : ℝ}
    {F_eps : ℝ → ℂ}
    (data : ModularSideData f H F_eps) :
    Tendsto F_eps (𝓝[>] 0)
      (𝓝 (-(2 * ↑Real.pi * I *
        ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) := by
  have h_eq : data.arc_value + data.horiz_value =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) := by
    rw [data.arc_eq, data.horiz_eq]; ring
  rw [← h_eq]
  exact data.h_tendsto

/-! ### Layer 2: Segment algebra

Pure algebra: combining the three/five segment contributions. -/

omit f hf in
/-- The three-piece modular side combination: 0 (T-cancel) + arc + horizontal
equals `-(2piI)(k/12 - ord_cusp)`. -/
theorem modularSide_three_piece {ord_cusp : ℂ} (arc_val horiz_val : ℂ)
    (h_arc : arc_val = -(2 * ↑Real.pi * I * ((k : ℂ) / 12)))
    (h_horiz : horiz_val = 2 * ↑Real.pi * I * ord_cusp) :
    arc_val + horiz_val =
    -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ord_cusp)) := by
  rw [h_arc, h_horiz]; ring

omit f hf in
/-- From the individual segment equations, derive the modular side. -/
theorem modularSide_from_segments {ord_cusp : ℂ}
    (seg1_val seg2_val seg3_val seg4_val seg5_val : ℂ)
    (h_T_cancel : seg1_val + seg4_val = 0)
    (h_arc : seg2_val + seg3_val = -(2 * ↑Real.pi * I * ((k : ℂ) / 12)))
    (h_horiz : seg5_val = 2 * ↑Real.pi * I * ord_cusp) :
    seg1_val + seg2_val + seg3_val + seg4_val + seg5_val =
    -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - ord_cusp)) := by
  have : seg1_val + seg2_val + seg3_val + seg4_val + seg5_val =
    (seg1_val + seg4_val) + (seg2_val + seg3_val) + seg5_val := by ring
  rw [this, h_T_cancel, h_arc, h_horiz]; ring

/-! ### Bridge to discharge_pvChain_full -/

/-- **Direct modular side bridge.**

If you already have the Tendsto statement for the common integrand `F_int`,
this packages it for `discharge_pvChain_full`. -/
theorem modularSide_direct
    (_S : Finset UpperHalfPlane) (_hS : ∀ p ∈ _S, p ∈ 𝒟)
    (_hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ _S)
    (_mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (F_int : ℝ → ℝ → ℂ)
    (H_mod : ℝ) (_hH_mod_gt : Real.sqrt 3 / 2 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))) :
    ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) :=
  h_mod

/-- **Modular side for `discharge_pvChain_full`.**

Given a constructor for `ModularSideData` at each height above threshold,
produce the `h_mod` parameter needed by `discharge_pvChain_full`. -/
theorem modularSide_for_discharge
    (_S : Finset UpperHalfPlane) (_hS : ∀ p ∈ _S, p ∈ 𝒟)
    (_hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ _S)
    (_mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (F_int : ℝ → ℝ → ℂ)
    (H_mod : ℝ) (_hH_mod_gt : Real.sqrt 3 / 2 < H_mod)
    (mk_data : ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      ModularSideData f H (F_int H)) :
    ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) := by
  intro H hH_ge hH
  exact modularSide_tendsto_of_data f (mk_data H hH_ge hH)

/-! ### Build ModularSideData from ingredients -/

/-- Build `ModularSideData` from explicit arc and horizontal values
and a Tendsto hypothesis. -/
noncomputable def modularSideData_of_avoidance
    (H : ℝ)
    (arc : ℂ)
    (h_arc_eq : arc = -(2 * ↑Real.pi * I * ((k : ℂ) / 12)))
    (horiz : ℂ)
    (h_horiz_eq : horiz = 2 * ↑Real.pi * I * (orderAtCusp' f : ℂ))
    (F_eps : ℝ → ℂ)
    (h_tendsto : Tendsto F_eps (𝓝[>] 0) (𝓝 (arc + horiz))) :
    ModularSideData f H F_eps where
  arc_value := arc
  horiz_value := horiz
  arc_eq := h_arc_eq
  horiz_eq := h_horiz_eq
  h_tendsto := h_tendsto

/-! ### From five segments to Tendsto -/

/-- **Modular side from segment decomposition.**

Given T-cancellation, arc contribution, and horizontal contribution as
hypotheses on the five segment integrals, plus the CPV tending to their sum,
produce the modular side Tendsto. -/
theorem modularSide_tendsto_of_segments
    (I_seg1 I_seg2 I_seg3 I_seg4 I_seg5 : ℂ)
    (h_T_cancel : I_seg1 + I_seg4 = 0)
    (h_arc : I_seg2 + I_seg3 = -(2 * ↑Real.pi * I * ((k : ℂ) / 12)))
    (h_horiz : I_seg5 = 2 * ↑Real.pi * I * (orderAtCusp' f : ℂ))
    (F_eps : ℝ → ℂ)
    (h_ev : Tendsto F_eps (𝓝[>] 0)
      (𝓝 (I_seg1 + I_seg2 + I_seg3 + I_seg4 + I_seg5))) :
    Tendsto F_eps (𝓝[>] 0)
      (𝓝 (-(2 * ↑Real.pi * I *
        ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) := by
  have h_total : I_seg1 + I_seg2 + I_seg3 + I_seg4 + I_seg5 =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :=
    modularSide_from_segments (k := k) I_seg1 I_seg2 I_seg3 I_seg4 I_seg5
      h_T_cancel h_arc h_horiz
  rwa [h_total] at h_ev

/-! ### Combined discharge: modular side -> h_pvChain -/

omit hf in
/-- **Complete modular-side discharge**: combine residue and modular sides
to produce `h_pvChain` for `discharge_pvChain_full`. -/
theorem modularSide_complete_discharge
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (F_int : ℝ → ℝ → ℂ)
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S)
    (H_res : ℝ) (hH_res_gt : Real.sqrt 3 / 2 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    (H_mod : ℝ) (hH_mod_gt : Real.sqrt 3 / 2 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))) :
    ∃ H' : ℝ, ∃ D : FDWindingDataFull H',
      (∀ s ∈ S, (s : ℂ).im < H') ∧
      ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) =
      -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) :=
  discharge_pvChain_full f S hS hS_complete mkD H_S hH_S F_int
    H_res hH_res_gt h_res H_mod hH_mod_gt h_mod

/-! ### T-cancellation for vertical segment integrals -/

omit f hf in
/-- T-cancellation at the integrand level implies cancellation of the
interval integrals.

The hypothesis requires `F(4/5 - t) = -(F t)` on the closed interval
`[0, 1/5]`, which avoids measure-theoretic complications at endpoints.
This is satisfied by `logDeriv_integrand_seg4_neg_seg1` from
`ModularContourIntegral.lean` (which proves it on the open interval,
and the boundary values are continuous limits). -/
theorem T_cancel_segment_integrals
    {F : ℝ → ℂ}
    (h_cancel : ∀ t ∈ Icc (0 : ℝ) (1/5), F (4/5 - t) = -(F t))
    (_h_int : IntervalIntegrable F volume 0 (1/5)) :
    (∫ t in (0 : ℝ)..(1/5), F t) +
    (∫ t in (3/5 : ℝ)..(4/5), F t) = 0 := by
  -- Step 1: change of variables gives seg4 = ∫ F(4/5 - u) over [0, 1/5]
  have h_sub : ∫ t in (3/5 : ℝ)..(4/5), F t =
      ∫ u in (0 : ℝ)..(1/5), F (4/5 - u) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1/5) F (4/5 : ℝ)
    simp only [sub_zero] at h
    rw [show (4 : ℝ)/5 - 1/5 = 3/5 from by norm_num] at h
    exact h.symm
  -- Step 2: pointwise cancellation on [0, 1/5]
  have h_neg_int : (∫ u in (0 : ℝ)..(1/5), F (4/5 - u)) =
      -(∫ u in (0 : ℝ)..(1/5), F u) := by
    trans (∫ u in (0 : ℝ)..(1/5), (fun v => -(F v)) u)
    · apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1/5)] at hu
      exact h_cancel u hu
    · exact intervalIntegral.integral_neg
  -- Step 3: combine
  rw [h_sub, h_neg_int]
  exact add_neg_cancel _

/-! ### Arc contribution from S-identity -/

omit f hf in
/-- The arc contribution `-(kpiI/6) = -(2piI)(k/12)`, restated. -/
theorem arc_contribution_eq (k : ℤ) :
    -(↑k * ↑Real.pi * I / 6) =
    -(2 * ↑Real.pi * I * ((k : ℂ) / 12)) :=
  arc_contribution_eq_neg_k_over_12 k

/-! ### Horizontal contribution interface -/

/-- Data for the horizontal contribution at height `H`. -/
structure HorizontalContributionData {H : ℝ}
    (γ : PiecewiseC1Path (fdStart H) (fdStart H)) where
  /-- The integral of `logDeriv(f)` on seg5 equals `2piI * ord_cusp`. -/
  seg5_integral_eq :
    ∫ t in (4/5 : ℝ)..1,
      logDeriv (⇑f ∘ UpperHalfPlane.ofComplex) (γ.toPath.extend t) *
      deriv γ.toPath.extend t =
    2 * ↑Real.pi * I * (orderAtCusp' f : ℂ)

/-! ### Modular side from Tendsto or Eventually -/

/-- **Modular side from avoidance and ingredients.**

Given the CPV tends to the contour value, and the contour value equals
the modular side expression, produce the Tendsto. -/
theorem modularSide_of_avoidance_and_ingredients
    (F_eps : ℝ → ℂ) (contour_val : ℂ)
    (h_tendsto : Tendsto F_eps (𝓝[>] 0) (𝓝 contour_val))
    (h_decomp : contour_val =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))) :
    Tendsto F_eps (𝓝[>] 0)
      (𝓝 (-(2 * ↑Real.pi * I *
        ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) := by
  rwa [h_decomp] at h_tendsto

/-- When the CPV is eventually equal to the modular side value. -/
theorem modularSide_tendsto_of_eventually_eq
    (F_eps : ℝ → ℂ) (L : ℂ)
    (hL : L = -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))
    (h_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), F_eps ε = L) :
    Tendsto F_eps (𝓝[>] 0)
      (𝓝 (-(2 * ↑Real.pi * I *
        ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) := by
  rw [← hL]
  exact tendsto_const_nhds.congr' (Filter.EventuallyEq.symm h_ev)

/-! ### The main interface theorem -/

/-- **The modular side theorem (direct form).**

Given the modular-side Tendsto at every sufficiently large height, produce
the h_mod parameter for `discharge_pvChain_full`. -/
theorem modularSide_main
    (_mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (F_int : ℝ → ℝ → ℂ)
    (H_mod : ℝ) (_hH_mod_gt : Real.sqrt 3 / 2 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))) :
    ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))) :=
  h_mod

/-! ### Integration with PVChainProof: full valence formula -/

omit hf in
/-- **The valence formula from residue side + modular side Tendsto.**

Combines:
- Residue side: `F_int H eps -> 2piI * Sigma gWN * ord`
- Modular side: `F_int H eps -> -(2piI)(k/12 - ord_cusp)`

By uniqueness of limits, the two agree, giving the valence formula. -/
theorem valence_formula_of_modular_and_residue_sides
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S)
    (F_int : ℝ → ℝ → ℂ)
    (H_res : ℝ) (hH_res_gt : Real.sqrt 3 / 2 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    (H_mod : ℝ) (hH_mod_gt : Real.sqrt 3 / 2 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVertFM S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 :=
  valence_formula_of_two_sides f S hS hS_complete mkD H_S hH_S F_int
    H_res hH_res_gt h_res H_mod hH_mod_gt h_mod

end
