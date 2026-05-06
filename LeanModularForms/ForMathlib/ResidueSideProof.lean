/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PVChainProof
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.LogDerivModularForm

/-!
# Residue Side Proof — CPV of logDeriv(f) tends to 2πi · Σ gWN · ord

This file provides the residue side of the PV chain: the Cauchy principal value
integral of `logDeriv(f)` around the FD boundary converges (as ε → 0⁺) to
`2πi · Σ generalizedWindingNumber(γ, s) · orderOfVanishingAt'(f, s)`.

## Architecture

The proof is structured in layers:

### Layer 1: `ResidueSideData`

A structure bundling all analytical ingredients at a given height `H`:
- The `HasCauchyPVOn` for `logDeriv(f)` along the boundary
- The identification of the limit with the winding-weighted order sum

### Layer 2: Sum conversion

The generalized residue theorem gives the CPV in terms of residues:
  `CPV(logDeriv f) = Σ 2πi · gWN(γ, s) · residue(logDeriv f, s)`

The residue of `logDeriv(f)` at a zero of order `n` equals `n`
(`logDeriv_residue_eq_order` from LogDerivModularForm), so:
  `CPV(logDeriv f) = 2πi · Σ gWN(γ, s) · ord(f, s)`

### Layer 3: Bridge to `discharge_pvChain_full`

Format the Tendsto for the `h_res` parameter of `discharge_pvChain_full`
in PVChainProof.lean.

## Strategy for filling `ResidueSideData`

The `ResidueSideData` structure is designed so that each field can be
independently verified:

1. **Simple poles**: `logDeriv(f)` has simple poles at each zero/pole of `f`
   in the upper half-plane (from `logDeriv_hasSimplePoleAt_of_order`).

2. **CPV existence**: Apply the generalized residue theorem
   (`hasCauchyPVOn_simplePoles_convex_auto`) to `logDeriv(f)` on the fdBox.

3. **Sum conversion**: Convert from residues to orders using
   `logDeriv_residue_eq_order`.

## Main results

* `residueSide_tendsto_of_hasCauchyPVOn` — from `HasCauchyPVOn` for
  `logDeriv(f)` plus residue-to-order conversion, extract the Tendsto.

* `residueSide_for_discharge` — the full interface for `discharge_pvChain_full`:
  given structured hypotheses, produce the `h_res` parameter.

## Imports

Only `LeanModularForms.ForMathlib.*` and `Mathlib.*`.

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Theorem 3.1.1
* Hungerbühler--Wasem, *A generalized residue theorem*, arXiv:1808.00997v2
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0)

/-! ### Two-pi-I nonzero -/

omit f hf in
private lemma two_pi_I_ne_zero_rs : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
    ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, or_self]

/-! ### ResidueSideData: bundled analytical ingredients -/

/-- Bundled data for the residue side at a given height `H`.

This packages the result of applying the generalized residue theorem to
`logDeriv(f)` along the FD boundary at height `H`:

1. A singular set `S_sing` of complex points where `logDeriv(f)` has simple poles
   (the zeros and poles of `f` in the fundamental domain).
2. `HasCauchyPVOn` for `logDeriv(f)` along the boundary, with singular set `S_sing`.
3. The winding-weighted residue sum equals the winding-weighted order sum.

The CPV integrand `cpvIntegrandOn S_sing (logDeriv f) γ.toPath.extend ε t`
is zero when `γ(t)` is within `ε` of some `s ∈ S_sing`, and
`(logDeriv f)(γ(t)) · γ'(t)` otherwise. -/
structure ResidueSideData {H : ℝ} (D : FDWindingDataFull H)
    (S : Finset UpperHalfPlane) where
  /-- The singular set for the CPV. -/
  S_sing : Finset ℂ
  /-- The function whose CPV we compute. -/
  F : ℂ → ℂ
  /-- `F` agrees with `logDeriv f` off the singular set. -/
  F_eq_logDeriv : ∀ z, z ∉ (↑S_sing : Set ℂ) → F z = logDeriv (⇑f ∘ UpperHalfPlane.ofComplex) z
  /-- The CPV of `F` along the boundary exists and equals the winding-weighted residue sum. -/
  h_cpv : HasCauchyPVOn S_sing F D.boundary
    (∑ s ∈ S_sing, 2 * ↑Real.pi * I *
      generalizedWindingNumber D.boundary (s : ℂ) * residue F s)
  /-- The winding-weighted residue sum converts to the winding-weighted order sum.
  This captures: (a) residue(logDeriv f, s) = ord(f, s) at each zero, (b) off-S
  points contribute zero, and (c) the image of S in ℂ covers the relevant S_sing. -/
  sum_convert :
    ∑ s ∈ S_sing, 2 * ↑Real.pi * I *
      generalizedWindingNumber D.boundary s * residue F s =
    2 * ↑Real.pi * I *
      ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ)

/-! ### Extract Tendsto from ResidueSideData -/

/-- From `ResidueSideData`, extract the Tendsto statement:
the ε-truncated integral of `F` along the FD boundary converges to
`2πi · Σ gWN(γ, s) · ord(f, s)`.

This unfolds `HasCauchyPVOn` and applies the sum conversion. -/
theorem residueSide_tendsto_of_data {H : ℝ} {D : FDWindingDataFull H}
    {S : Finset UpperHalfPlane}
    (data : ResidueSideData f S (D := D)) :
    Tendsto (fun ε =>
      ∫ t in (0 : ℝ)..1, cpvIntegrandOn data.S_sing data.F
        D.boundary.toPath.extend ε t)
      (𝓝[>] 0)
      (𝓝 (2 * ↑Real.pi * I *
        ∑ s ∈ S,
          generalizedWindingNumber D.boundary (↑s : ℂ) *
            (orderOfVanishingAt' (⇑f) s : ℂ))) := by
  rw [← data.sum_convert]
  exact data.h_cpv

/-! ### Layer 2: Sum conversion helpers

These lemmas help construct the `sum_convert` field of `ResidueSideData`. -/

/-- The winding-weighted residue sum for `logDeriv(f)` can be converted to a
winding-weighted order sum, given:
- Residue equals order at each point of `S` (covering both zero and nonzero cases)
- Winding times residue = 0 at singular points not in the image of `S`
- `S.image ⊆ S_sing`
- Injectivity of the coercion on `S` -/
theorem residueSide_sum_convert_of_residue_eq_order
    {γ : PiecewiseC1Path (fdStart H) (fdStart H)}
    {S : Finset UpperHalfPlane} {S_sing : Finset ℂ} {F : ℂ → ℂ}
    -- Residue = order at every point of S
    (h_res_eq : ∀ s ∈ S,
      residue F (↑s : ℂ) = ↑(orderOfVanishingAt' (⇑f) s))
    -- Winding × residue = 0 at non-S points
    (h_non_S_zero : ∀ s ∈ S_sing,
      s ∉ (S.image (↑· : UpperHalfPlane → ℂ) : Finset ℂ) →
      generalizedWindingNumber γ s * residue F s = 0)
    -- S_sing contains the image of S
    (h_S_sub : S.image (↑· : UpperHalfPlane → ℂ) ⊆ S_sing)
    -- Injectivity of the coercion on S
    (h_inj : ∀ p₁ ∈ S, ∀ p₂ ∈ S, (↑p₁ : ℂ) = (↑p₂ : ℂ) → p₁ = p₂) :
    ∑ s ∈ S_sing, 2 * ↑Real.pi * I *
      generalizedWindingNumber γ s * residue F s =
    2 * ↑Real.pi * I *
      ∑ s ∈ S,
        generalizedWindingNumber γ (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) := by
  -- Step 1: Restrict sum to S.image since other terms are zero
  have h_restrict :
      ∑ s ∈ S_sing, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue F s =
      ∑ s ∈ S.image (↑· : UpperHalfPlane → ℂ),
        2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue F s := by
    symm
    apply Finset.sum_subset h_S_sub
    intro s hs hs_ni
    have := h_non_S_zero s hs hs_ni
    rw [show 2 * ↑Real.pi * I * generalizedWindingNumber γ s * residue F s =
      2 * ↑Real.pi * I * (generalizedWindingNumber γ s * residue F s) from by ring]
    rw [this, mul_zero]
  rw [h_restrict]
  -- Step 2: Rewrite image sum as S sum
  rw [Finset.sum_image (fun p₁ hp₁ p₂ hp₂ h => h_inj p₁ hp₁ p₂ hp₂ h)]
  -- Step 3: Factor out 2πi and match each term
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [h_res_eq p hp]
  ring

/-! ### Layer 3: Bridge to `discharge_pvChain_full`

The main interface theorem. -/

/-- **Residue side for `discharge_pvChain_full`.**

Given:
1. A constructor `mkD` for `FDWindingDataFull` at any height above `√3/2`
2. For each height `H ≥ H_res`, a `ResidueSideData f S (D := mkD H hH)`
3. An integrand `F_int H ε` that agrees with the CPV integral of `data.F`

Produce the `h_res` parameter needed by `discharge_pvChain_full`. -/
theorem residueSide_for_discharge
    (S : Finset UpperHalfPlane) (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (_hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    -- Common integrand
    (F_int : ℝ → ℝ → ℂ)
    -- Height threshold
    (H_res : ℝ) (_hH_res_gt : Real.sqrt 3 / 2 < H_res)
    -- For each valid height, we have ResidueSideData
    (mk_data : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      ResidueSideData f S (D := mkD H hH))
    -- The common integrand eventually equals the CPV integral from the data
    (h_F_eq : ∀ (H : ℝ) (hH_ge : H_res ≤ H) (hH : Real.sqrt 3 / 2 < H),
      (fun ε => ∫ t in (0 : ℝ)..1,
            cpvIntegrandOn (mk_data H hH_ge hH).S_sing (mk_data H hH_ge hH).F
              (mkD H hH).boundary.toPath.extend ε t) =ᶠ[𝓝[>] (0 : ℝ)]
        F_int H) :
    ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))) := by
  intro H hH_ge hH
  have h_tendsto := residueSide_tendsto_of_data f (mk_data H hH_ge hH)
  exact h_tendsto.congr' (h_F_eq H hH_ge hH)

/-! ### Simpler interface: direct Tendsto hypothesis

For cases where the ResidueSideData construction is overkill, we provide
a direct bridge from a Tendsto hypothesis. -/

/-- **Direct residue side bridge.**

If you already have the Tendsto statement for the common integrand `F_int`,
this packages it for `discharge_pvChain_full`. This is the simplest interface:
it just verifies the types match. -/
theorem residueSide_direct
    (S : Finset UpperHalfPlane) (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (_hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (F_int : ℝ → ℝ → ℂ)
    (H_res : ℝ) (_hH_res_gt : Real.sqrt 3 / 2 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ)))) :
    ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))) :=
  h_res

/-! ### Connecting to the existing ForMathlib chain

These theorems show how to combine the residue side with the modular side
to get the valence formula. -/

/-- **Complete residue-side discharge**: from `ResidueSideData` at each height,
produce the full `h_pvChain` existential.

This combines `residueSide_for_discharge` with `discharge_pvChain_full`. -/
theorem valence_formula_of_residueSideData
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (F_int : ℝ → ℝ → ℂ)
    -- Height bound on S
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S)
    -- Residue side
    (H_res : ℝ) (hH_res_gt : Real.sqrt 3 / 2 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    -- Modular side
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

/-! ### Residue = order bridge

Lemmas connecting the generalized residue theorem output (residues)
to the valence formula input (orders of vanishing). -/

/-- At a zero of a nonzero modular form, the residue of `logDeriv(f)` equals
the order of vanishing.

This is the bridge between the generalized residue theorem (which gives
`Σ gWN · residue`) and the valence formula (which needs `Σ gWN · ord`). -/
theorem logDeriv_residue_eq_orderOfVanishing
    (p : UpperHalfPlane)
    (hMero : MeromorphicAt (⇑f ∘ UpperHalfPlane.ofComplex) (↑p : ℂ))
    (hord : meromorphicOrderAt (⇑f ∘ UpperHalfPlane.ofComplex) (↑p : ℂ) ≠ ⊤) :
    residue (logDeriv (⇑f ∘ UpperHalfPlane.ofComplex)) (↑p : ℂ) =
      ↑(meromorphicOrderAt (⇑f ∘ UpperHalfPlane.ofComplex) (↑p : ℂ)).untop₀ :=
  logDeriv_residue_eq_order hMero hord

/-! ### Height utilities -/

omit f hf in
/-- For a finite set `S` of upper half-plane points, there exists a height
above all points and above `√3/2`. -/
theorem exists_height_above_S_and_sqrt3 (S : Finset UpperHalfPlane) :
    ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ s ∈ S, (s : ℂ).im < H₀ := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · refine ⟨1, ?_, fun s hs => absurd hs (Finset.notMem_empty s)⟩
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)]
  · set M := S.sup' hne (fun s : UpperHalfPlane => (s : ℂ).im) with hM_def
    refine ⟨max (Real.sqrt 3 / 2) M + 1, ?_, ?_⟩
    · linarith [le_max_left (Real.sqrt 3 / 2) M]
    · intro s hs
      have : (s : ℂ).im ≤ M :=
        Finset.le_sup' (fun s : UpperHalfPlane => (s : ℂ).im) hs
      linarith [le_max_right (Real.sqrt 3 / 2) M]

/-! ### Avoidance case: when the boundary avoids all singular points

This is the simpler case, used when all zeros of `f` lie strictly inside
the fundamental domain (away from the boundary). -/

/-- In the avoidance case, `hasCauchyPVOn_simplePoles_convex_auto` directly
gives the CPV, and the sum is over the same singular set.

This lemma converts the `HasCauchyPVOn` output from the generalized residue
theorem into the Tendsto format needed by `discharge_pvChain_full`. -/
theorem residueSide_of_avoidance_case
    {x₀ : ℂ}
    {U : Set ℂ} (hU_convex : Convex ℝ U) (hU_open : IsOpen U) (hU_ne : U.Nonempty)
    (S_sing : Finset ℂ) (hS_in_U : ↑S_sing ⊆ U)
    (F : ℂ → ℂ) (hF_diff : DifferentiableOn ℂ F (U \ ↑S_sing))
    (γ : PiecewiseC1Path x₀ x₀)
    (hSimplePoles : ∀ s ∈ S_sing, HasSimplePoleAt F s)
    (hγ_in_U : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U)
    (hγ_avoids : ∀ s ∈ S_sing, ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (hδ : ∃ δ > 0, ∀ s ∈ S_sing, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_rem_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (fun z => F z - principalPartSum S_sing (fun s => residue F s) z) γ)
      volume 0 1)
    (h_pp_int : IntervalIntegrable
      (PiecewiseC1Path.contourIntegrand
        (principalPartSum S_sing (fun s => residue F s)) γ) volume 0 1)
    (hI : ∀ s ∈ S_sing, IntervalIntegrable
      (fun t => (residue F s / (γ.toPath.extend t - s)) *
        deriv γ.toPath.extend t) volume 0 1) :
    HasCauchyPVOn S_sing F γ
      (∑ s ∈ S_sing, 2 * ↑Real.pi * I *
        generalizedWindingNumber γ s * residue F s) :=
  hasCauchyPVOn_simplePoles_convex_auto hU_convex hU_open hU_ne S_sing hS_in_U F
    hF_diff γ hSimplePoles hγ_in_U hγ_avoids hδ h_rem_int h_pp_int hI

/-! ### Winding number sum algebra

Pure algebra lemmas for manipulating the winding-weighted sums. -/

omit f hf in
/-- Factor `2πi` out of the winding-weighted residue sum. -/
theorem factor_two_pi_I_from_sum {γ : PiecewiseC1Path x₀ x₀}
    {S : Finset ℂ} {c : ℂ → ℂ} :
    ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c s =
    2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber γ s * c s := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

omit f hf in
/-- Cancel `2πi` from both sides of a sum equation. -/
theorem cancel_two_pi_I_sum {γ : PiecewiseC1Path x₀ x₀}
    {S : Finset ℂ} {c₁ c₂ : ℂ → ℂ}
    (h : ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c₁ s =
         ∑ s ∈ S, 2 * ↑Real.pi * I * generalizedWindingNumber γ s * c₂ s) :
    ∑ s ∈ S, generalizedWindingNumber γ s * c₁ s =
    ∑ s ∈ S, generalizedWindingNumber γ s * c₂ s := by
  rw [factor_two_pi_I_from_sum, factor_two_pi_I_from_sum] at h
  exact mul_left_cancel₀ two_pi_I_ne_zero_rs h

/-! ### Combined discharge: residue + modular → valence formula

This is the culmination: combine the residue and modular sides. -/

omit hf in
/-- **The valence formula from Tendsto hypotheses.**

A thin wrapper around `valence_formula_of_two_sides` that makes the
type signature explicit. Given both Tendsto results (residue and modular),
plus the `FDWindingDataFull` construction, produces the orbit-sum form of
the valence formula. -/
theorem valence_formula_of_two_tendsto_sides
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S)
    (F_int : ℝ → ℝ → ℂ)
    -- Residue side
    (H_res : ℝ) (hH_res_gt : Real.sqrt 3 / 2 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F_int H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    -- Modular side
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
