/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.GeneralizedResidueTheorem
import LeanModularForms.ForMathlib.InteriorWinding
import LeanModularForms.ForMathlib.EllipticWeights
import LeanModularForms.ForMathlib.OrbitPairing

/-!
# Valence Formula Core

Assembly of the valence formula for modular forms from the residue theorem,
contour integration, and modular symmetry.

## Overview

The valence formula states that for a nonzero modular form `f` of weight `k`
for `SL₂(ℤ)`:

`ord_∞(f) + (1/2) · ord_i(f) + (1/3) · ord_ρ(f) + Σ_{z ∈ F°} ord_z(f) = k/12`

The proof strategy assembles this from three ingredients:
1. **Residue theorem** (`GeneralizedResidueTheorem.lean`): relates `∮ f'/f dz`
   to a sum of residues (= orders) times winding numbers.
2. **Modular symmetry** (`OrbitPairing.lean`): T-periodicity cancels the vertical
   edges; S-invariance pairs the arc segments; the horizontal segment gives `ord_∞`.
3. **Winding numbers** (`InteriorWinding.lean`, `EllipticWeights.lean`): interior
   points have winding number `-1`; elliptic points have fractional winding numbers.

## Main definitions

* `ValenceFormulaData` -- bundled data for the valence formula: orders at
  special points and interior, plus the identity `k/12 = weighted sum`.
* `ModularSymmetryData` -- bundled hypothesis recording the T-periodicity and
  S-transformation properties needed for contour cancellation.

## Main results

* `ValenceFormulaData.weight_nonneg` -- `k ≥ 0` when all orders
  are nonneg (i.e., `f` is holomorphic).
* `ValenceFormulaData.ord_inf_le` -- `ord_∞(f) ≤ k/12`.
* `ValenceFormulaData.half_ord_i_le` -- `(1/2) · ord_i(f) ≤ k/12`.
* `ValenceFormulaData.third_ord_rho_le` -- `(1/3) · ord_ρ(f) ≤ k/12`.
* `ValenceFormulaData.interior_sum_le` -- interior zero count ≤ `k/12`.
* `ValenceFormulaData.all_zero_of_weight_zero` -- weight 0 forces all orders to 0.
* `residueSide_with_fd_winding_numbers` -- algebraic decomposition of the residue
  side with the FD winding number values substituted.
* `residueSide_collapse_rho` -- T-periodicity collapse of `ρ` and `ρ+1` terms.
* `assembly_identity` -- the algebraic core: residue side = modular side implies
  the valence formula.

## Design notes

The full analytic proof (applying the residue theorem to the logarithmic derivative
along the FD boundary, then computing each segment) requires hundreds of lines of
integration estimates. This file provides:

1. The **algebraic framework**: `ValenceFormulaData` captures the formula statement
   and allows deriving corollaries purely algebraically.
2. **Assembly lemmas**: provable algebraic identities that would appear in the full
   proof (residue decomposition, symmetry cancellations).
3. **Clean API**: downstream files (`ValenceFormulaTextbook.lean`) consume only
   the `ValenceFormulaData` structure, insulating them from analytic details.

## References

* T. Apostol, *Modular Functions and Dirichlet Series in Number Theory*, Chapter 2
* J.-P. Serre, *A Course in Arithmetic*, Chapter VII
* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

/-! ### The Valence Formula Data Structure

This structure captures the *conclusion* of the valence formula: the relationship
between the weight `k`, the orders at special points, and the sum of orders at
interior zeros. All downstream corollaries (weight nonnegativity, finiteness of
zeros, dimension formulas) follow algebraically from this data. -/

/-- Bundled data for the valence formula.

For a nonzero modular form `f` of weight `k` for `SL₂(ℤ)`, the orders at
the cusp, at `i`, at `ρ`, and at interior points of the fundamental domain
satisfy the identity:

`ord_∞(f) + (1/2) · ord_i(f) + (1/3) · ord_ρ(f) + Σ interior = k / 12`

The field `all_nonneg` records that all orders are nonneg (the holomorphic case). -/
structure ValenceFormulaData (k : ℤ) where
  /-- The order of `f` at the cusp `∞` (via the `q`-expansion). -/
  ord_inf : ℤ
  /-- The order of `f` at `i` (the order-2 elliptic point). -/
  ord_i : ℤ
  /-- The order of `f` at `ρ = e^{2πi/3}` (the order-3 elliptic point). -/
  ord_rho : ℤ
  /-- The sum of orders at all interior zeros in the fundamental domain. -/
  interior_sum : ℤ
  /-- All orders are nonneg (holomorphic modular form). -/
  all_nonneg : 0 ≤ ord_inf ∧ 0 ≤ ord_i ∧ 0 ≤ ord_rho ∧ 0 ≤ interior_sum
  /-- The valence formula identity. -/
  formula : (ord_inf : ℚ) + 1 / 2 * ord_i + 1 / 3 * ord_rho + interior_sum = k / 12

namespace ValenceFormulaData

variable {k : ℤ} (vf : ValenceFormulaData k)

/-! ### Basic accessors and reformulations -/

/-- The weighted order sum as a rational number. -/
def weightedSum : ℚ :=
  (vf.ord_inf : ℚ) + 1 / 2 * vf.ord_i + 1 / 3 * vf.ord_rho + vf.interior_sum

/-- The weighted sum equals `k/12`. -/
theorem weightedSum_eq : vf.weightedSum = (k : ℚ) / 12 := vf.formula

/-! ### Weight nonnegativity -/

include vf in
/-- **Weight nonnegativity**: if `f` is a nonzero holomorphic modular form of weight `k`,
then `k ≥ 0`. This follows from the valence formula because all orders are nonneg,
so `k/12 ≥ 0`, hence `k ≥ 0`. -/
theorem weight_nonneg : 0 ≤ k := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  have h_inf : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_half : (0 : ℚ) ≤ 1 / 2 * (vf.ord_i : ℚ) := by
    apply mul_nonneg (by norm_num)
    exact_mod_cast h2
  have h_third : (0 : ℚ) ≤ 1 / 3 * (vf.ord_rho : ℚ) := by
    apply mul_nonneg (by norm_num)
    exact_mod_cast h3
  have h_int : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  have hk12 : (0 : ℚ) ≤ (k : ℚ) / 12 := by linarith
  have hk : (0 : ℚ) ≤ (k : ℚ) := by linarith
  exact_mod_cast hk

/-- The weighted sum is nonneg. -/
theorem weightedSum_nonneg : 0 ≤ vf.weightedSum := by
  rw [vf.weightedSum_eq]
  exact div_nonneg (by exact_mod_cast vf.weight_nonneg) (by norm_num)

/-! ### Individual order bounds -/

/-- `ord_∞(f) ≤ k/12` (the cusp order is bounded by the weight). -/
theorem ord_inf_le : (vf.ord_inf : ℚ) ≤ k / 12 := by
  have ⟨_, h2, h3, h4⟩ := vf.all_nonneg
  have h_half : (0 : ℚ) ≤ 1 / 2 * (vf.ord_i : ℚ) := by
    apply mul_nonneg (by norm_num); exact_mod_cast h2
  have h_third : (0 : ℚ) ≤ 1 / 3 * (vf.ord_rho : ℚ) := by
    apply mul_nonneg (by norm_num); exact_mod_cast h3
  have h_int : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  linarith [vf.formula]

/-- `(1/2) · ord_i(f) ≤ k/12` (the weighted i-order is bounded by the weight). -/
theorem half_ord_i_le : 1 / 2 * (vf.ord_i : ℚ) ≤ k / 12 := by
  have ⟨h1, _, h3, h4⟩ := vf.all_nonneg
  have h_inf : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_third : (0 : ℚ) ≤ 1 / 3 * (vf.ord_rho : ℚ) := by
    apply mul_nonneg (by norm_num); exact_mod_cast h3
  have h_int : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  linarith [vf.formula]

/-- `(1/3) · ord_ρ(f) ≤ k/12` (the weighted ρ-order is bounded by the weight). -/
theorem third_ord_rho_le : 1 / 3 * (vf.ord_rho : ℚ) ≤ k / 12 := by
  have ⟨h1, h2, _, h4⟩ := vf.all_nonneg
  have h_inf : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_half : (0 : ℚ) ≤ 1 / 2 * (vf.ord_i : ℚ) := by
    apply mul_nonneg (by norm_num); exact_mod_cast h2
  have h_int : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  linarith [vf.formula]

/-- The interior zero count (sum of orders) is bounded by `k/12`. -/
theorem interior_sum_le : (vf.interior_sum : ℚ) ≤ k / 12 := by
  have ⟨h1, h2, h3, _⟩ := vf.all_nonneg
  have h_inf : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_half : (0 : ℚ) ≤ 1 / 2 * (vf.ord_i : ℚ) := by
    apply mul_nonneg (by norm_num); exact_mod_cast h2
  have h_third : (0 : ℚ) ≤ 1 / 3 * (vf.ord_rho : ℚ) := by
    apply mul_nonneg (by norm_num); exact_mod_cast h3
  linarith [vf.formula]

/-- `ord_i(f) ≤ k/6` (integral bound on the i-order). -/
theorem ord_i_le : (vf.ord_i : ℚ) ≤ k / 6 := by
  have h := vf.half_ord_i_le
  linarith

/-- `ord_ρ(f) ≤ k/4` (integral bound on the ρ-order). -/
theorem ord_rho_le : (vf.ord_rho : ℚ) ≤ k / 4 := by
  have h := vf.third_ord_rho_le
  linarith

end ValenceFormulaData

/-! ### Modular Symmetry Data

This structure bundles the properties of a modular form needed for the contour
cancellation argument. -/

/-- Bundled hypothesis for the modular symmetry properties used in the valence formula. -/
structure ModularSymmetryData (f : ℂ → ℂ) (k : ℤ) where
  /-- T-periodicity: `f(z + 1) = f(z)`. -/
  hperiodic : IsPeriodic f
  /-- The logarithmic derivative `f'/f` is T-periodic. -/
  hlogDeriv_periodic : IsPeriodic (fun z => deriv f z / f z)

namespace ModularSymmetryData

variable {f : ℂ → ℂ} {k : ℤ}

/-- T-periodic functions have the same value at `ρ` and `ρ + 1`. -/
theorem eq_at_rho (msd : ModularSymmetryData f k) : f rhoPlusOne = f rho :=
  periodic_eq_at_rho msd.hperiodic

/-- T-periodic functions have the same logarithmic derivative at `ρ` and `ρ + 1`. -/
theorem logDeriv_eq_at_rho (msd : ModularSymmetryData f k) :
    deriv f rhoPlusOne / f rhoPlusOne = deriv f rho / f rho :=
  periodic_eq_at_rho msd.hlogDeriv_periodic

end ModularSymmetryData

/-! ### Residue Side Decomposition

When the residue theorem is applied to `f'/f` along the FD boundary, the result
is a sum over singular points of `ord_z(f) · windingNumber(γ, z)`.

For the fundamental domain:
- Interior points: winding number = `-1`
- `i`: winding number = `-1/2`
- `ρ`: winding number = `-1/6` (and similarly for `ρ + 1`)

The following lemmas record the algebraic decomposition. -/

/-- When `w_i = -1/2`, `w_ρ = w_{ρ+1} = -1/6`, and `w_int = -1`, the
residue sum equals `-(1/2 · n_i + 1/6 · n_ρ + 1/6 · n_{ρ+1} + n_int)`. -/
theorem residueSide_with_fd_winding_numbers
    {n_i n_rho n_rhoP n_int : ℤ} :
    (n_i : ℚ) * (-1 / 2) + n_rho * (-1 / 6) + n_rhoP * (-1 / 6) + n_int * (-1) =
    -(1 / 2 * n_i + 1 / 6 * n_rho + 1 / 6 * n_rhoP + n_int) := by
  ring

/-- When `n_rho = n_rhoP` (T-periodicity), the `ρ` and `ρ+1` contributions
collapse to `1/3 · n_ρ`. -/
theorem residueSide_collapse_rho {n_i n_rho n_int : ℤ} :
    (1 : ℚ) / 2 * n_i + 1 / 6 * n_rho + 1 / 6 * n_rho + n_int =
    1 / 2 * n_i + 1 / 3 * n_rho + n_int := by
  ring

/-- After collapsing `ρ` and `ρ+1`, negating gives the standard valence formula form. -/
theorem residueSide_to_valence_formula
    {n_inf n_i n_rho n_int : ℤ} {k : ℤ}
    (h_modular : (n_inf : ℚ) = k / 12 +
      (1 / 2 * n_i + 1 / 3 * n_rho + n_int)) :
    (n_inf : ℚ) + (-(1 / 2 * n_i + 1 / 3 * n_rho + n_int)) = k / 12 := by
  linarith

/-! ### Vertical Edge Cancellation

T-periodicity implies that the integrals along segments 1 and 4 cancel.
This is recorded in `OrbitPairing.lean` as `seg4_integrand_eq_neg_seg1`.
Here we provide the algebraic consequence. -/

/-- If two terms are negatives of each other, their sum is zero. -/
theorem vertical_cancel {a b : ℂ} (h : b = -a) : a + b = 0 := by
  rw [h]; ring

/-- The vertical edge cancellation: segments 1 and 4 contribute nothing. -/
theorem vertical_edges_vanish {I₁ I₄ : ℂ} (h : I₄ = -I₁) :
    I₁ + I₄ = 0 :=
  vertical_cancel h

/-! ### Arc Segment Pairing

The S-transformation pairs segments 2 and 3 via `γ(t) · γ(4/5 - t) = -1`.
For `f'/f` of a weight-`k` modular form, this gives the `-k/6` contribution. -/

/-- The arc integral identity: after dividing by `2πi`, the arc contribution
is `-k/6`. -/
theorem arc_contribution_eq {k : ℤ} :
    (k : ℚ) * (-(1 : ℚ) / 6) = -(k / 6) := by ring

/-- The arc contribution `-k/6` splits as `-k/12 + (-k/12)` for the
two sub-arcs (segment 2 and segment 3). -/
theorem arc_split_halves {k : ℤ} :
    -(k : ℚ) / 6 = -(k / 12) + -(k / 12) := by ring

/-! ### Horizontal Segment (Cusp Contribution)

The horizontal segment at height `H` gives `ord_∞(f)` via the `q`-expansion
winding number. After dividing by `-2πi` (clockwise orientation), this
contributes `+ord_∞(f)` to the sum. -/

/-- The horizontal segment contribution: `ord_∞` appears with coefficient `+1`
in the valence formula (from the `q`-expansion winding number). -/
theorem horizontal_contribution {n_inf : ℤ} :
    (n_inf : ℚ) * 1 = n_inf := by ring

/-! ### Complete Assembly Identity

The full assembly combines all pieces:
- Residue side: `-Σ ord_z · windingNumber(γ, z)`
- Modular side: `ord_∞ - k/12` (from vertical cancellation + arc pairing + horizontal)

Setting them equal gives the valence formula. -/

/-- **Assembly identity**: the algebraic core of the valence formula.

If the residue side is `-(1/2 · n_i + 1/3 · n_ρ + n_int)` and
the modular side is `n_inf - k/12`, then equating them gives
`n_inf + 1/2 · n_i + 1/3 · n_ρ + n_int = k/12`. -/
theorem assembly_identity {n_inf n_i n_rho n_int : ℤ} {k : ℤ}
    (h : (n_inf : ℚ) - k / 12 = -(1 / 2 * n_i + 1 / 3 * n_rho + n_int)) :
    (n_inf : ℚ) + 1 / 2 * n_i + 1 / 3 * n_rho + n_int = k / 12 := by
  linarith

/-- **Assembly identity (alternate form)**: if the formula is already known and
all orders are nonneg, produce `ValenceFormulaData`. -/
noncomputable def assembleValenceData {k : ℤ}
    (n_inf n_i n_rho n_int : ℤ)
    (h_inf : 0 ≤ n_inf) (h_i : 0 ≤ n_i) (h_rho : 0 ≤ n_rho) (h_int : 0 ≤ n_int)
    (h : (n_inf : ℚ) + 1 / 2 * n_i + 1 / 3 * n_rho + n_int = k / 12) :
    ValenceFormulaData k where
  ord_inf := n_inf
  ord_i := n_i
  ord_rho := n_rho
  interior_sum := n_int
  all_nonneg := ⟨h_inf, h_i, h_rho, h_int⟩
  formula := h

/-! ### Uniqueness of the valence formula decomposition

The decomposition is NOT unique in general (there could be many ways to distribute
orders). But given a FIXED modular form, the orders are determined. This section
records the algebraic fact that if two ValenceFormulaData agree on k, they must
satisfy the same identity. -/

/-- Two valence formula data with the same `k` have the same weighted sum. -/
theorem ValenceFormulaData.weightedSum_eq_weightedSum
    {k : ℤ} (vf₁ vf₂ : ValenceFormulaData k) :
    vf₁.weightedSum = vf₂.weightedSum := by
  rw [vf₁.weightedSum_eq, vf₂.weightedSum_eq]

/-! ### Algebraic consequences for specific weights -/

/-- For weight 0, the valence formula forces all orders to be 0. -/
theorem ValenceFormulaData.all_zero_of_weight_zero
    (vf : ValenceFormulaData 0) :
    vf.ord_inf = 0 ∧ vf.ord_i = 0 ∧ vf.ord_rho = 0 ∧ vf.interior_sum = 0 := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hf := vf.formula
  simp only [Int.cast_zero, zero_div] at hf
  have h_inf_q : (0 : ℚ) ≤ (vf.ord_inf : ℚ) := by exact_mod_cast h1
  have h_i_q : (0 : ℚ) ≤ (vf.ord_i : ℚ) := by exact_mod_cast h2
  have h_rho_q : (0 : ℚ) ≤ (vf.ord_rho : ℚ) := by exact_mod_cast h3
  have h_int_q : (0 : ℚ) ≤ (vf.interior_sum : ℚ) := by exact_mod_cast h4
  have h_half : (0 : ℚ) ≤ 1 / 2 * (vf.ord_i : ℚ) := by linarith
  have h_third : (0 : ℚ) ≤ 1 / 3 * (vf.ord_rho : ℚ) := by linarith
  have h_inf_zero : (vf.ord_inf : ℚ) = 0 := by linarith
  have h_int_zero : (vf.interior_sum : ℚ) = 0 := by linarith
  have h_i_half_zero : 1 / 2 * (vf.ord_i : ℚ) = 0 := by linarith
  have h_i_zero : (vf.ord_i : ℚ) = 0 := by linarith
  have h_rho_zero : (vf.ord_rho : ℚ) = 0 := by linarith
  exact ⟨by exact_mod_cast h_inf_zero, by exact_mod_cast h_i_zero,
    by exact_mod_cast h_rho_zero, by exact_mod_cast h_int_zero⟩

/-- For weight 0, if the valence formula holds, then `f` has no zeros at all
in the fundamental domain (including at the cusp and elliptic points). -/
theorem ValenceFormulaData.total_zero_count_of_weight_zero
    (vf : ValenceFormulaData 0) :
    (vf.ord_inf : ℚ) + vf.ord_i + vf.ord_rho + vf.interior_sum = 0 := by
  have ⟨h1, h2, h3, h4⟩ := vf.all_zero_of_weight_zero
  simp [h1, h2, h3, h4]

/-- For weight `k > 0`, at least one of the orders is positive
(equivalently, `f` has at least one zero). -/
theorem ValenceFormulaData.exists_positive_order
    (vf : ValenceFormulaData k) (hk : 0 < k) :
    0 < vf.ord_inf ∨ 0 < vf.ord_i ∨ 0 < vf.ord_rho ∨ 0 < vf.interior_sum := by
  by_contra h
  push_neg at h
  have ⟨h1, h2, h3, h4⟩ := vf.all_nonneg
  have hi := le_antisymm (h.1) h1
  have hj := le_antisymm (h.2.1) h2
  have hr := le_antisymm (h.2.2.1) h3
  have hs := le_antisymm (h.2.2.2) h4
  have hf := vf.formula
  simp only [hi, hj, hr, hs, Int.cast_zero, mul_zero, add_zero] at hf
  have : (0 : ℚ) < (k : ℚ) / 12 := by positivity
  linarith

/-! ### Weight 12 analysis -/

/-- For weight 12 (`k = 12`), the formula becomes
`ord_∞ + 1/2 · ord_i + 1/3 · ord_ρ + interior = 1`.
The only solutions with nonneg integer entries are:
- `ord_∞ = 1, rest = 0` (the discriminant `Δ`)
- `ord_i = 0, ord_ρ = 3, rest = 0`
- `ord_i = 2, ord_ρ = 0, rest = 0`
and a few more. This lemma just records the sum-equals-1 fact. -/
theorem ValenceFormulaData.formula_weight_12
    (vf : ValenceFormulaData 12) :
    (vf.ord_inf : ℚ) + 1 / 2 * vf.ord_i + 1 / 3 * vf.ord_rho +
      vf.interior_sum = 1 := by
  have hf := vf.formula
  norm_num at hf ⊢
  linarith

end
