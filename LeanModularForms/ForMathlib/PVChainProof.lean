/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.CoreIdentityProof

/-!
# PV Chain Proof: Discharging h_pvChain

This file discharges the `h_pvChain` hypothesis from `CoreIdentityProof.lean`,
which bundles:
1. `FDWindingDataFull H` for some large `H`
2. Height bound: all S points below H
3. PV chain identity: `Sigma gWN(boundary, s) * ord(f,s) = -(k/12 - ord_cusp)`

## Strategy

Both sides of the PV chain identity are limits of the *same* epsilon-truncated
integral of `logDeriv(f)` around the FD boundary:

- **Residue side**: the CPV integral tends to `2 pi i * Sigma gWN * ord`,
  by the generalized residue theorem applied to `logDeriv(f)` (which has
  simple poles with residue = order of vanishing).

- **Modular side**: the same CPV integral tends to `-(2 pi i)(k/12 - ord_inf)`,
  via T-cancellation of verticals, S-arc contribution, and horizontal winding.

By `tendsto_nhds_unique` the two limits agree, and cancelling `2 pi i` gives
the PV chain identity.

## Architecture

### `PVChainData`

Bundles the two `Tendsto` hypotheses for a common integrand `F_eps` at a
given height `H`, together with the `FDWindingDataFull` at that height.

### `pvChainIdentity`

The core theorem: from `PVChainData` extract the identity
  `Sigma gWN * ord = -(k/12 - ord_cusp)`
via uniqueness of limits and algebraic manipulation.

### `discharge_pvChain`

Assembles `h_pvChain` from `PVChainData` by packaging the identity with
the height bound.

## Imports

Only from `LeanModularForms.ForMathlib.*` and `Mathlib.*`.

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
private lemma pvChain_two_pi_I_ne_zero : (2 : ℂ) * ↑Real.pi * I ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
    ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero, or_self]

/-! ### PVChainData: the bundled Tendsto hypotheses -/

/-- Data for the PV chain identity at height `H`.

This bundles:
1. `FDWindingDataFull H` -- winding weights at all FD boundary points
2. A common integrand function `F_eps : R -> C` (the epsilon-truncated
   integral of `logDeriv(f)` around the FD boundary)
3. The residue-side limit: `F_eps` tends to the winding-weighted ord sum
4. The modular-side limit: `F_eps` tends to the modular-side expression
5. Height bound: all points in `S` lie below `H`

The two Tendsto hypotheses share the same integrand, so
`tendsto_nhds_unique` applies. -/
structure PVChainData
    (S : Finset UpperHalfPlane) (H : ℝ) where
  /-- The full winding data at height `H`. -/
  D : FDWindingDataFull H
  /-- All points in `S` lie below the horizontal segment. -/
  hH_above : ∀ s ∈ S, (s : ℂ).im < H
  /-- The common epsilon-dependent integrand. -/
  F_eps : ℝ → ℂ
  /-- The residue-side limit: `F_eps` converges (as `epsilon -> 0+`) to
  `2 pi i * Sigma gWN * ord`. -/
  h_res : Tendsto F_eps (𝓝[>] 0)
    (𝓝 (2 * ↑Real.pi * I *
      ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ)))
  /-- The modular-side limit: `F_eps` converges (as `epsilon -> 0+`) to
  `-(2 pi i * (k/12 - ord_cusp))`. -/
  h_mod : Tendsto F_eps (𝓝[>] 0)
    (𝓝 (-(2 * ↑Real.pi * I *
      ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))

/-! ### Core identity from PVChainData -/

/-- **The PV chain identity**: from `PVChainData`, extract

  `Sigma gWN(gamma, s) * ord(f, s) = -(k/12 - ord_cusp)`

by uniqueness of limits (both the residue and modular sides are limits
of the same epsilon-truncated integral) and cancellation of `2 pi i`.

This is the heart of the valence formula proof: the analytical content
is in constructing the two `Tendsto` hypotheses; the algebraic content
is this uniqueness + cancellation argument. -/
theorem pvChainIdentity
    (S : Finset UpperHalfPlane)
    {H : ℝ} (data : PVChainData f S H) :
    ∑ s ∈ S,
      generalizedWindingNumber data.D.boundary (↑s : ℂ) *
        (orderOfVanishingAt' (⇑f) s : ℂ) =
    -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  -- Both sides are limits of the same F_eps as eps -> 0+
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  -- By uniqueness of limits in a Hausdorff space:
  have h_eq :
      2 * ↑Real.pi * I *
        ∑ s ∈ S, generalizedWindingNumber data.D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) =
      -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) :=
    tendsto_nhds_unique data.h_res data.h_mod
  -- Cancel 2 pi i from both sides
  have hpi : (2 : ℂ) * ↑Real.pi * I ≠ 0 := pvChain_two_pi_I_ne_zero
  rw [show -(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) =
    2 * ↑Real.pi * I * (-((k : ℂ) / 12 - (orderAtCusp' f : ℂ))) from by ring] at h_eq
  exact mul_left_cancel₀ hpi h_eq

/-! ### Discharge h_pvChain -/

/-- **Discharge `h_pvChain`**: given `PVChainData` for some `H`, produce
the existential hypothesis needed by `valence_formula_orbit_sum_of_pvChain`
in `CoreIdentityProof.lean`.

This wraps `pvChainIdentity` with the height and `FDWindingDataFull`
existentials. -/
theorem discharge_pvChain
    (S : Finset UpperHalfPlane) (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (_hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (data : PVChainData f S H) :
    ∃ H' : ℝ, ∃ D : FDWindingDataFull H',
      (∀ s ∈ S, (s : ℂ).im < H') ∧
      ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) =
      -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) :=
  ⟨H, data.D, data.hH_above, pvChainIdentity f S data⟩

/-! ### Full discharge: from residue + modular sides to h_pvChain -/

/-- **Full discharge of `h_pvChain`** from residue and modular side existentials.

Given:
1. A constructor for `FDWindingDataFull H` at any height `H > sqrt(3)/2`
2. Height bounds on S
3. Residue side: for `H >= H_res`, the CPV integral tends to the winding sum
4. Modular side: for `H >= H_mod`, the CPV integral tends to the modular expression

Produces the `h_pvChain` existential needed by
`valence_formula_orbit_sum_of_pvChain`.

The proof picks `H = max(max(H_res, H_mod), H_S) + 1`, constructs
`PVChainData` at that height, and applies `pvChainIdentity`. -/
theorem discharge_pvChain_full
    (S : Finset UpperHalfPlane) (_hS : ∀ p ∈ S, p ∈ 𝒟)
    (_hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    -- FDWindingDataFull construction
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    -- Height bound on S
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S)
    -- Common integrand
    (F : ℝ → ℝ → ℂ)
    -- Residue side
    (H_res : ℝ) (hH_res_gt : Real.sqrt 3 / 2 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    -- Modular side
    (H_mod : ℝ) (_hH_mod_gt : Real.sqrt 3 / 2 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))) :
    ∃ H' : ℝ, ∃ D : FDWindingDataFull H',
      (∀ s ∈ S, (s : ℂ).im < H') ∧
      ∑ s ∈ S,
        generalizedWindingNumber D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ) =
      -((k : ℂ) / 12 - (orderAtCusp' f : ℂ)) := by
  set H := max (max H_res H_mod) H_S + 1
  have hH_ge_res : H_res ≤ H := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))
  have hH_ge_mod : H_mod ≤ H := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))
  have hH_gt_sqrt3 : Real.sqrt 3 / 2 < H :=
    lt_of_lt_of_le hH_res_gt hH_ge_res
  have hH_above : ∀ s ∈ S, (s : ℂ).im < H := fun s hs =>
    lt_of_lt_of_le (hH_S s hs)
      (le_trans (le_max_right _ _) (le_of_lt (lt_add_one _)))
  refine ⟨H, mkD H hH_gt_sqrt3, hH_above, ?_⟩
  exact pvChainIdentity f S
    { D := mkD H hH_gt_sqrt3
      hH_above := hH_above
      F_eps := F H
      h_res := h_res H hH_ge_res hH_gt_sqrt3
      h_mod := h_mod H hH_ge_mod hH_gt_sqrt3 }

/-! ### Winding sum rearrangement -/

/-- From the PV chain identity, rearrange to the form used downstream:
  `ord_cusp + (- weighted_sum) = k / 12`. -/
theorem pvChain_rearranged
    (S : Finset UpperHalfPlane)
    {H : ℝ} (data : PVChainData f S H) :
    (orderAtCusp' f : ℂ) +
    (-(∑ s ∈ S,
        generalizedWindingNumber data.D.boundary (↑s : ℂ) *
          (orderOfVanishingAt' (⇑f) s : ℂ))) =
    (k : ℂ) / 12 := by
  have h := pvChainIdentity f S data
  linear_combination -h

/-! ### FDWindingDataFull construction from FDWindingData + boundary winding -/

/-- Extend `FDWindingData` to `FDWindingDataFull` by providing the smooth
boundary winding number hypothesis.

The boundary winding (`gWN = -1/2` at non-elliptic on-curve points) comes
from `BoundaryWinding.lean`: at any such point the FD boundary passes through
as a smooth curve with crossing angle `pi`, so the generalized winding number
is `-(pi * i) / (2 * pi * i) = -1/2`. -/
def FDWindingDataFull.ofWindingData {H : ℝ}
    (D : FDWindingData H)
    (h_bdry : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      Complex.normSq z ≥ 1 → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber D.boundary z (-1/2)) :
    FDWindingDataFull H :=
  { toFDWindingData := D
    boundary_winding := h_bdry }

/-! ### Uniqueness of limits: algebraic alternatives -/

omit f hf in
/-- If two complex numbers agree after multiplying by `2 pi i`, they are equal.
A variant of the cancellation lemma. -/
theorem eq_of_two_pi_I_mul_eq {a b : ℂ}
    (h : 2 * ↑Real.pi * I * a = 2 * ↑Real.pi * I * b) :
    a = b :=
  mul_left_cancel₀ pvChain_two_pi_I_ne_zero h

omit f hf in
/-- If `2 pi i * a = -(2 pi i * b)` then `a = -b`. -/
theorem eq_neg_of_two_pi_I_mul_eq_neg {a b : ℂ}
    (h : 2 * ↑Real.pi * I * a = -(2 * ↑Real.pi * I * b)) :
    a = -b := by
  have : 2 * ↑Real.pi * I * a = 2 * ↑Real.pi * I * (-b) := by
    rw [mul_neg]; exact h
  exact mul_left_cancel₀ pvChain_two_pi_I_ne_zero this

/-! ### Height bound utilities -/

omit f hf in
/-- For a finite set `S` of upper half plane points, there exists `H_S`
above the imaginary parts of all points. -/
theorem exists_height_above_finset (S : Finset UpperHalfPlane) :
    ∃ H_S : ℝ, ∀ s ∈ S, (s : ℂ).im < H_S := by
  by_cases hne : S.Nonempty
  · set M := S.sup' hne (fun s : UpperHalfPlane => (s : ℂ).im) with hM_def
    refine ⟨M + 1, fun s hs => ?_⟩
    have : (s : ℂ).im ≤ M := by
      exact Finset.le_sup' (fun s : UpperHalfPlane => (s : ℂ).im) hs
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨1, fun s hs => by simp [hne] at hs⟩

omit f hf in
/-- Combine height bound with sqrt(3)/2 lower bound. -/
theorem exists_height_above_finset_and_sqrt3
    (S : Finset UpperHalfPlane) :
    ∃ H_S : ℝ, Real.sqrt 3 / 2 < H_S ∧ ∀ s ∈ S, (s : ℂ).im < H_S := by
  obtain ⟨H₁, hH₁⟩ := exists_height_above_finset S
  exact ⟨max H₁ (Real.sqrt 3 / 2) + 1,
    by linarith [le_max_right H₁ (Real.sqrt 3 / 2)],
    fun s hs => lt_of_lt_of_le (hH₁ s hs)
      (le_trans (le_max_left _ _) (le_of_lt (lt_add_one _)))⟩

/-! ### Integration of PVChainData with CoreIdentityProof -/

omit hf in
/-- The orbit-sum valence formula, given `PVChainData`.

Combines `discharge_pvChain` with `valence_formula_orbit_sum_of_pvChain`
from `CoreIdentityProof.lean`, yielding the textbook formula:

  `ord_inf + (1/2) * ord_i + (1/3) * ord_rho + non-ell sum = k / 12` -/
theorem valence_formula_of_pvChainData
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    {H : ℝ} (data : PVChainData f S H) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 :=
  valence_formula_orbit_sum_of_pvChain f S hS hS_complete
    (discharge_pvChain f S hS hS_complete data)

/-! ### Summary theorem: the complete discharge interface -/

omit hf in
/-- **Complete interface for discharging `h_pvChain`**.

Given:
- `mkD`: constructor for `FDWindingDataFull` at any height above sqrt(3)/2
- `F`: the common epsilon-truncated integrand (indexed by height `H` and cutoff `eps`)
- Residue-side and modular-side `Tendsto` results with existential height bounds

Produces the full orbit-sum valence formula. No sorry. -/
theorem valence_formula_of_two_sides
    (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S)
    -- FDWindingDataFull construction
    (mkD : ∀ H : ℝ, Real.sqrt 3 / 2 < H → FDWindingDataFull H)
    -- Height bound on S
    (H_S : ℝ) (hH_S : ∀ s ∈ S, (s : ℂ).im < H_S)
    -- Common integrand
    (F : ℝ → ℝ → ℂ)
    -- Residue side
    (H_res : ℝ) (hH_res_gt : Real.sqrt 3 / 2 < H_res)
    (h_res : ∀ (H : ℝ), H_res ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F H) (𝓝[>] 0)
        (𝓝 (2 * ↑Real.pi * I *
          ∑ s ∈ S,
            generalizedWindingNumber (mkD H hH).boundary (↑s : ℂ) *
              (orderOfVanishingAt' (⇑f) s : ℂ))))
    -- Modular side
    (H_mod : ℝ) (hH_mod_gt : Real.sqrt 3 / 2 < H_mod)
    (h_mod : ∀ (H : ℝ), H_mod ≤ H → (hH : Real.sqrt 3 / 2 < H) →
      Tendsto (F H) (𝓝[>] 0)
        (𝓝 (-(2 * ↑Real.pi * I *
          ((k : ℂ) / 12 - (orderAtCusp' f : ℂ)))))) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
        ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2),
      ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ sLeftVert S, ↑(orderOfVanishingAt' (⇑f) s) +
    ∑ s ∈ S.filter (fun p =>
        p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0),
      ↑(orderOfVanishingAt' (⇑f) s) =
    (k : ℂ) / 12 := by
  have h_pvChain := discharge_pvChain_full f S hS hS_complete mkD H_S hH_S
    F H_res hH_res_gt h_res H_mod hH_mod_gt h_mod
  exact valence_formula_orbit_sum_of_pvChain f S hS hS_complete h_pvChain

end
