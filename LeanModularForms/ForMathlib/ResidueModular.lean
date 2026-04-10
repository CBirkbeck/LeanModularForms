/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ValenceFormulaFinal
import LeanModularForms.ForMathlib.ModularInvariance

/-!
# Residue-Modular Identity -- Construction of `ResidueModularHyp`

This file provides the infrastructure for constructing `ResidueModularHyp`, which bundles
the result of applying the generalized residue theorem to `logDeriv(f)` along the
fundamental domain boundary.

## Strategy

The valence formula identity `cusp_order + Sigma winding * ord = k/12` follows from:

1. **T-periodicity**: `f(z+1) = f(z)` implies `logDeriv(f)` is 1-periodic, so the
   integrals along the left and right vertical edges cancel.
2. **S-transformation on arcs**: `f(-1/z) = z^k * f(z)` gives
   `logDeriv(f(-1/z)) * (-z^{-2}) = logDeriv(f(z)) - k/z`, so the two arc integrals
   contribute `-k/6` after change of variables.
3. **Horizontal segment**: At height `H`, the integral of `logDeriv(f)` along the
   horizontal relates to the cusp order via the q-expansion.

## What is proved vs hypothesized

### Proved unconditionally

* `modularFormCompOfComplex_periodic` -- T-periodicity: `f(z+1) = f(z)` on the UHP.
* `modularFormCompOfComplex_periodic_neg` -- backward shift: `f(z-1) = f(z)`.
* `modularForm_S_identity` -- S-identity: `f(-1/z) = z^k * f(z)`.
* `fd_points_below_of_finset` -- any finite set of UHP points has a uniform height bound.
* `winding_sum_term_zero_of_ord_zero` -- zero-order terms contribute nothing.
* `winding_sum_eq_filter_nonzero` -- the winding sum depends only on nonzero-order points.
* `ord_sum_eq_filter_nonzero` -- order sums are unchanged when restricting to nonzero terms.
* `residueModularData_identity_extends` -- the identity for the zero set extends to
  any superset, enabling the `forall S` quantification in `ResidueModularHyp`.
* `valence_formula_from_residueModularData` -- the full textbook valence formula from
  `ResidueModularData`, bypassing the unsatisfiable `h_above` in `ResidueModularHyp`.

### Taken as hypothesis (`ResidueModularData`)

* `h_above_zeros` -- all FD zeros have imaginary part below `H`.
* `h_identity_for_zeros` -- the combined residue-modular identity for zero sets.
* `wd` -- winding weight data at height `H`.

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Chapter 3
* Miyake, *Modular Forms*, Theorem 2.5.2
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ### T-periodicity of modular forms on C -/

/-- T-periodicity: a modular form for `Gamma(1)` satisfies `f(z + 1) = f(z)` for all `z`
in the upper half-plane. This is the composition with `ofComplex` version. -/
theorem modularFormCompOfComplex_periodic (z : ℂ) (hz : 0 < z.im) :
    modularFormCompOfComplex f (z + 1) = modularFormCompOfComplex f z := by
  have hz1 : 0 < (z + 1).im := by simp [add_im, hz]
  simp only [modularFormCompOfComplex, Function.comp_apply,
    UpperHalfPlane.ofComplex_apply_of_im_pos hz1,
    UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  set z_uhp : UpperHalfPlane := ⟨z, hz⟩
  have h_vadd : ((1 : ℝ) +ᵥ z_uhp : ℍ) = ⟨z + 1, hz1⟩ := by
    ext; simp [UpperHalfPlane.coe_vadd]; ring
  have := SlashInvariantForm.vAdd_width_periodic 1 k 1 f.toSlashInvariantForm z_uhp
  simp only [Nat.cast_one, mul_one, Int.cast_one, ModularForm.toSlashInvariantForm_coe] at this
  rw [h_vadd] at this; exact this

/-- Backward T-periodicity: `f(z - 1) = f(z)` for `z` in the upper half-plane. -/
theorem modularFormCompOfComplex_periodic_neg (z : ℂ) (hz : 0 < z.im) :
    modularFormCompOfComplex f (z - 1) = modularFormCompOfComplex f z := by
  have hz1 : 0 < (z - 1).im := by simp [sub_im, hz]
  have h := modularFormCompOfComplex_periodic f (z - 1) hz1
  rw [show z - 1 + 1 = z from by ring] at h; exact h.symm

/-! ### S-identity for modular forms on C -/

/-- S-identity: `(f circ ofComplex)(-1/z) = z^k * (f circ ofComplex)(z)` for `z` in the
upper half-plane. This is a re-export of `modform_comp_ofComplex_S_identity`. -/
theorem modularForm_S_identity (z : ℂ) (hz : 0 < z.im) :
    modularFormCompOfComplex f (-(1 : ℂ) / z) =
    z ^ k * modularFormCompOfComplex f z := by
  simp only [modularFormCompOfComplex, Function.comp_apply]
  exact modform_comp_ofComplex_S_identity f z hz

/-! ### Height bounds for finite sets -/

/-- Any finite subset of the upper half-plane has a uniform upper bound on imaginary
parts, with the bound strictly above 1. -/
theorem fd_points_below_of_finset (S : Finset ℍ) :
    ∃ H : ℝ, 1 < H ∧ ∀ s ∈ S, (s : ℂ).im < H := by
  by_cases hS : S.Nonempty
  · obtain ⟨s₀, _, h_max⟩ := S.exists_max_image (fun s : ℍ => (s : ℂ).im) hS
    refine ⟨max ((s₀ : ℂ).im + 1) 2, ?_, fun s hs => ?_⟩
    · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    · linarith [h_max s hs, le_max_left ((s₀ : ℂ).im + 1) 2]
  · rw [Finset.not_nonempty_iff_eq_empty] at hS; subst hS
    exact ⟨2, by norm_num, fun _ hs => absurd hs (by simp)⟩

/-! ### Winding sum reduction -/

/-- If a point has `orderOfVanishingAt' = 0`, its contribution to the winding-weighted
sum is zero, since the term is `winding(s) * 0 = 0`. -/
theorem winding_sum_term_zero_of_ord_zero {x y : ℂ} (γ : PiecewiseC1Path x y) (s : ℍ)
    (h_ord : orderOfVanishingAt' (⇑f) s = 0) :
    (-generalizedWindingNumber γ (↑s : ℂ)) * ↑(orderOfVanishingAt' (⇑f) s) = 0 := by
  rw [h_ord, Int.cast_zero, mul_zero]

/-- The winding-weighted sum over `S` equals the sum restricted to elements with nonzero
order. Points with `orderOfVanishingAt' = 0` contribute zero and can be dropped. -/
theorem winding_sum_eq_filter_nonzero {x y : ℂ} (γ : PiecewiseC1Path x y)
    (S : Finset ℍ) :
    ∑ s ∈ S, (-generalizedWindingNumber γ (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) =
    ∑ s ∈ S.filter (fun s => orderOfVanishingAt' (⇑f) s ≠ 0),
      (-generalizedWindingNumber γ (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) := by
  symm; apply Finset.sum_filter_of_ne
  intro s _ h_ne; contrapose! h_ne
  rw [h_ne, Int.cast_zero, mul_zero]

/-- A sum of `orderOfVanishingAt' f` values over `S.filter P` equals the same sum
restricted to points with nonzero order. -/
theorem ord_sum_eq_filter_nonzero (S : Finset ℍ) (P : ℍ → Prop) [DecidablePred P] :
    ∑ s ∈ S.filter P, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ (S.filter (fun s => orderOfVanishingAt' (⇑f) s ≠ 0)).filter P,
      (orderOfVanishingAt' (⇑f) s : ℂ) := by
  -- LHS = Σ_{(S.filter P).filter(ord≠0)} (drop zero terms)
  have h1 : ∑ s ∈ S.filter P, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ (S.filter P).filter (fun s => orderOfVanishingAt' (⇑f) s ≠ 0),
      (orderOfVanishingAt' (⇑f) s : ℂ) := by
    symm; apply Finset.sum_filter_of_ne; intro s _ h; contrapose! h; simp [h]
  -- RHS filter = (S.filter P).filter(ord≠0) by commutativity of filter
  have h2 : (S.filter (fun s => orderOfVanishingAt' (⇑f) s ≠ 0)).filter P =
    (S.filter P).filter (fun s => orderOfVanishingAt' (⇑f) s ≠ 0) := by
    ext s; simp only [Finset.mem_filter]; tauto
  rw [h1, h2]

/-! ### The residue-modular data hypothesis -/

/-- The analytical data needed for the residue-modular identity. This bundles the
output of applying the generalized residue theorem to `logDeriv(f)` along the FD
boundary, together with the modular side computation and the winding weight data.

Unlike `ResidueModularHyp`, this structure only requires `h_above_zeros` (zeros have
bounded imaginary part), not the unsatisfiable `h_above` (all FD points bounded).

The identity is stated for sets `S_0` that capture exactly the zeros:
all elements lie in `D`, all have nonzero order, and all FD zeros are included.
-/
structure ResidueModularData {k : ℤ} (f : ModularForm (Gamma 1) k) where
  /-- The height above all zeros in the fundamental domain. -/
  H : ℝ
  /-- The height is above 1. -/
  hH : 1 < H
  /-- The winding weight data at height `H`. -/
  wd : FDWindingDataFull H
  /-- All fundamental-domain zeros have imaginary part below `H`.
  This follows from the q-expansion: for large `im(z)`, the modular form is
  asymptotic to `a_N * q^N` and hence nonvanishing. -/
  h_above_zeros : ∀ p : ℍ, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → (p : ℂ).im < H
  /-- The combined residue-modular identity, stated for any zero set.
  This is the output of:
  1. Generalized residue theorem: contour integral of `logDeriv(f)` equals
     winding-weighted sum of orders.
  2. T-periodicity: vertical integrals cancel.
  3. S-transformation: arc integrals contribute `-k/6`.
  4. q-expansion: horizontal integral gives cusp order. -/
  h_identity_for_zeros : ∀ (S₀ : Finset ℍ), (∀ p ∈ S₀, p ∈ 𝒟) →
    (∀ s ∈ S₀, orderOfVanishingAt' (⇑f) s ≠ 0) →
    (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S₀) →
    (orderAtCusp' f : ℂ) +
    ∑ s ∈ S₀, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12

/-! ### Extending the identity to arbitrary S -/

/-- The identity from `ResidueModularData` extends to any set `S` satisfying the
standard hypotheses `hS : forall p in S, p in D` and
`hS_complete : forall p in D, ord(p) ne 0 -> p in S`.

Points in `S` with `orderOfVanishingAt' = 0` contribute nothing to the
winding-weighted sum. Therefore the sum over `S` equals the sum over
`S.filter (ord ne 0)`, and the latter is exactly the zero set for which
`h_identity_for_zeros` provides the identity. -/
theorem residueModularData_identity_extends (data : ResidueModularData f)
    (S : Finset ℍ) (hS : ∀ p ∈ S, p ∈ 𝒟)
    (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) :
    (orderAtCusp' f : ℂ) +
    ∑ s ∈ S, (-generalizedWindingNumber data.wd.boundary (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12 := by
  set S₀ := S.filter (fun s => orderOfVanishingAt' (⇑f) s ≠ 0) with hS₀_def
  have h_sum_eq : ∑ s ∈ S, (-generalizedWindingNumber data.wd.boundary (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) =
    ∑ s ∈ S₀, (-generalizedWindingNumber data.wd.boundary (↑s : ℂ)) *
      ↑(orderOfVanishingAt' (⇑f) s) := by
    symm; apply Finset.sum_filter_of_ne
    intro s _ h_ne; contrapose! h_ne
    rw [h_ne, Int.cast_zero, mul_zero]
  rw [h_sum_eq]
  apply data.h_identity_for_zeros S₀
  · intro p hp; exact hS p (Finset.mem_filter.mp hp).1
  · intro s hs; exact (Finset.mem_filter.mp hs).2
  · intro p hp_fd hp_ord
    exact Finset.mem_filter.mpr ⟨hS_complete p hp_fd hp_ord, hp_ord⟩

/-! ### Construction of ResidueModularHyp -/

/-- Construct `ResidueModularHyp` from `ResidueModularData` plus the condition that
all FD points lie below height `H`.

**Note:** The `h_all_above` condition is unsatisfiable for the standard fundamental
domain, which is unbounded upward. See `valence_formula_from_residueModularData` for
the recommended route that avoids this condition entirely. -/
theorem mkResidueModularHyp_from_data
    (data : ResidueModularData f)
    (h_all_above : ∀ p : ℍ, p ∈ 𝒟 → (p : ℂ).im < data.H) :
    ResidueModularHyp f data.H data.wd.boundary where
  h_above := h_all_above
  h_identity S hS hS_complete :=
    residueModularData_identity_extends f data S hS hS_complete

/-! ### Direct route to the valence formula -/

variable (hf : f ≠ 0)

include hf in
/-- **The Valence Formula** from `ResidueModularData`.

This is the main theorem of the file: it produces the textbook valence formula directly
from the residue-modular analytical data, bypassing the unsatisfiable `h_above`
condition of `ResidueModularHyp`.

The proof filters each `S` to `S₀ = S.filter(ord ne 0)` (the actual zeros), applies
`valence_formula_core_of_windingDataFull` with `S₀` (which satisfies `hS_below` from
`h_above_zeros`), then shows the expanded sums over `S` equal those over `S₀` because
zero-order terms contribute nothing. -/
theorem valence_formula_from_residueModularData
    (data : ResidueModularData f) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 := by
  apply valence_formula_textbook_orbit_finsum f hf
  intro S hS hS_complete
  -- Filter to zeros only
  set S₀ := S.filter (fun s => orderOfVanishingAt' (⇑f) s ≠ 0)
  have hS₀_fd : ∀ p ∈ S₀, p ∈ 𝒟 := fun p hp => hS p (Finset.mem_filter.mp hp).1
  have hS₀_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S₀ :=
    fun p hp_fd hp_ord => Finset.mem_filter.mpr ⟨hS_complete p hp_fd hp_ord, hp_ord⟩
  have hS₀_below : ∀ s ∈ S₀, (s : ℂ).im < data.H :=
    fun s hs => data.h_above_zeros s (hS₀_fd s hs) (Finset.mem_filter.mp hs).2
  -- The identity for S₀
  have h_id_S₀ := data.h_identity_for_zeros S₀ hS₀_fd
    (fun s hs => (Finset.mem_filter.mp hs).2) hS₀_complete
  -- The core formula with S₀ (only needs hS₀_below, not h_above for all FD)
  have h_core := valence_formula_core_of_windingDataFull f hf data.wd S₀
    hS₀_fd hS₀_complete hS₀_below h_id_S₀
  -- Reduce S-based filter sums to S₀-based (zero-order terms vanish)
  have h_int := ord_sum_eq_filter_nonzero f S (fun p =>
    p ≠ ellipticPointI' ∧ p ≠ ellipticPointRho' ∧ p ≠ ellipticPointRhoPlusOne' ∧
    ‖(p : ℂ)‖ > 1 ∧ |(p : ℂ).re| < 1/2)
  have h_lv : ∑ s ∈ sLeftVert S, (orderOfVanishingAt' (⇑f) s : ℂ) =
    ∑ s ∈ sLeftVert S₀, (orderOfVanishingAt' (⇑f) s : ℂ) := by
    simp only [sLeftVert]; exact ord_sum_eq_filter_nonzero f S _
  have h_la := ord_sum_eq_filter_nonzero f S (fun p =>
    p ≠ ellipticPointRho' ∧ ‖(p : ℂ)‖ = 1 ∧ (p : ℂ).re < 0)
  linear_combination h_core + h_int + h_lv + h_la

end
