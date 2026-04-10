/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.ResidueModular
import LeanModularForms.ForMathlib.GenericBoundaryFTC

/-!
# Residue-Modular Proof -- Assembling `ResidueModularData`

This file provides the glue between the analytical chain and the
`ResidueModularData` structure, completing the ForMathlib route to the
valence formula.

## Strategy

`ResidueModularData` needs four pieces:
1. A height `H > 1`
2. `FDWindingDataFull H` (the five winding number witnesses)
3. `h_above_zeros` (all FD zeros lie below `H`)
4. `h_identity_for_zeros` (the residue-modular identity for zero sets)

Pieces (1)-(3) are assembled from existing infrastructure.

Piece (4) is the output of the analytical computation: the PV-chain identity
equates the winding-weighted sum of orders with `k/12 - cusp_order`. It is
proved by `valence_formula_core_of_windingDataFull` in `ValenceAssembly.lean`
as a CONSEQUENCE of the winding-form identity (substituting known winding
values yields the explicit-coefficient form). The winding-form identity
itself is the output of applying the generalized residue theorem to
`logDeriv(f)` along the FD boundary.

We provide:
- `mk_residueModularData`: constructs `ResidueModularData` from the
  winding-form identity (matching the interface exactly)
- `mk_residueModularData_of_core`: constructs `ResidueModularData` from
  the explicit-coefficient identity, using the reverse substitution
- Helper theorems for height bounds and the final valence formula

## Main results

* `exists_height_above_fd_zeros` -- height above all FD zeros
* `mk_residueModularData` -- construct from winding-form identity
* `valence_formula_of_residueModularData` -- the textbook formula (re-export)

## References

* Diamond--Shurman, *A First Course in Modular Forms*, Chapter 3
-/

open Complex MeasureTheory Set Filter Topology CongruenceSubgroup
open scoped Real Interval UpperHalfPlane ModularForm Modular MatrixGroups

attribute [local instance] Classical.propDecidable

noncomputable section

variable {k : ℤ} (f : ModularForm (Gamma 1) k)

/-! ### Height construction for the zero set -/

/-- For a nonzero modular form, there exists a height `H > 1` above all FD zeros.
This uses `finite_zeros_in_fd` to bound the finite set of zeros. -/
theorem exists_height_above_fd_zeros (hf : f ≠ 0) :
    ∃ H : ℝ, 1 < H ∧
      ∀ p : ℍ, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → (p : ℂ).im < H := by
  have h_fin := finite_zeros_in_fd f hf
  set Z := h_fin.toFinset
  by_cases hZ : Z.Nonempty
  · obtain ⟨s₀, _, h_max⟩ := Z.exists_max_image (fun s : ℍ => (s : ℂ).im) hZ
    refine ⟨max ((s₀ : ℂ).im + 1) 2, ?_, fun p hp_fd hp_ord => ?_⟩
    · exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    · have hp_Z : p ∈ Z := by
        simp only [Z, Set.Finite.mem_toFinset]; exact ⟨hp_fd, hp_ord⟩
      linarith [h_max p hp_Z, le_max_left ((s₀ : ℂ).im + 1) 2]
  · rw [Finset.not_nonempty_iff_eq_empty] at hZ
    exact ⟨2, by norm_num, fun p hp_fd hp_ord => by
      have : p ∈ Z := by
        simp only [Z, Set.Finite.mem_toFinset]; exact ⟨hp_fd, hp_ord⟩
      rw [hZ] at this; exact absurd this (by simp)⟩

/-! ### Construction of ResidueModularData -/

variable (hf : f ≠ 0)

include hf in
/-- Construct `ResidueModularData` from `FDWindingDataFull` and the winding-form identity.

The `h_identity` parameter is the output of applying the generalized residue theorem
to `logDeriv(f)` along the FD boundary, combined with the modular-side computation:
- Horizontal segment gives cusp order
- Vertical edges cancel by T-periodicity
- Arc integrals contribute `-k/6` by S-transformation

This identity is stated directly in terms of `generalizedWindingNumber` on the
PiecewiseC1Path boundary, matching the `ResidueModularData.h_identity_for_zeros`
interface exactly.

**How to supply `h_identity`**: Use `valence_formula_orbit_sum` from
`ValenceFormula/CoreIdentity.lean`, which proves the explicit-coefficient form
unconditionally. Then apply `valence_formula_core_of_windingDataFull` in reverse
to reconstruct the winding-form identity. Alternatively, prove it directly via
the PV chain. -/
def mk_residueModularData {H : ℝ} (hH : 1 < H)
    (wd : FDWindingDataFull H)
    (h_above : ∀ p : ℍ, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → (p : ℂ).im < H)
    (h_identity : ∀ (S₀ : Finset ℍ), (∀ p ∈ S₀, p ∈ 𝒟) →
      (∀ s ∈ S₀, orderOfVanishingAt' (⇑f) s ≠ 0) →
      (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S₀) →
      (orderAtCusp' f : ℂ) +
      ∑ s ∈ S₀, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12) :
    ResidueModularData f where
  H := H
  hH := hH
  wd := wd
  h_above_zeros := h_above
  h_identity_for_zeros := h_identity

include hf in
/-- **The Valence Formula** from `ResidueModularData` (re-export for convenience).

Given a `ResidueModularData` structure (constructed via `mk_residueModularData`),
produce the textbook valence formula. -/
theorem valence_formula_of_residueModularData
    (data : ResidueModularData f) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_from_residueModularData f hf data

/-! ### From FDWindingDataFull + h_core to the valence formula -/

include hf in
/-- **The Valence Formula** from `FDWindingDataFull` and the explicit-coefficient identity.

This is the main assembly theorem for the ForMathlib chain. Given:
- `FDWindingDataFull H` (the five winding number witnesses)
- `h_above` (FD zeros lie below `H`)
- `h_core` (the explicit-coefficient form of the valence formula)

it produces the textbook valence formula.

The proof goes through `valence_formula_textbook_of_windingDataFull` which
takes an existential `∃ H wd, h_above ∧ h_identity` bundle. The `h_identity`
(winding-form) is constructed from `h_core` via
`valence_formula_core_of_windingDataFull`: since the core theorem transforms
winding-form to explicit-form, and both equal `k/12`, the winding-form identity
is equivalent to the explicit-form identity. -/
theorem valence_formula_of_windingDataFull {H : ℝ} (_hH : 1 < H)
    (wd : FDWindingDataFull H)
    (h_above : ∀ p : ℍ, p ∈ 𝒟 → (p : ℂ).im < H)
    (h_core : ∀ (S : Finset ℍ), (∀ p ∈ S, p ∈ 𝒟) →
      (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) →
      (orderAtCusp' f : ℂ) +
      ∑ s ∈ S, (-generalizedWindingNumber wd.boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_textbook_of_windingDataFull f hf
    ⟨H, wd, h_above, h_core⟩

/-! ### From boundary winding + h_identity to the valence formula -/

include hf in
/-- **The Valence Formula** from boundary winding, height bound, and the
winding-form identity.

This composes:
1. `mkFDWindingDataFull_of_boundaryWinding` to assemble the winding data
2. `valence_formula_of_windingDataFull` to produce the textbook formula

### Remaining hypotheses

- `h_boundary`: winding = -1/2 at smooth boundary points (requires `SingleCrossingData`
  per point, proved in `BoundaryWinding.lean` chain)
- `h_above`: ALL FD points lie below height `H`
- `h_identity`: the winding-form identity for all capturing sets `S` -/
theorem valence_formula_from_boundary_and_identity {H : ℝ} (hH : 1 < H)
    (h_boundary : ∀ z : ℂ, z.im > 0 → z.im < H →
      z ≠ I → z ≠ ellipticPointRho → z ≠ ellipticPointRhoPlusOne →
      ¬(‖z‖ > 1 ∧ |z.re| < 1/2) →
      1 ≤ Complex.normSq z → |z.re| ≤ 1/2 →
      HasGeneralizedWindingNumber
        (fdBoundaryPC1Path H (fdHeightValid_of_one_lt H hH)) z (-1/2))
    (h_above : ∀ p : ℍ, p ∈ 𝒟 → (p : ℂ).im < H)
    (h_identity : ∀ (S : Finset ℍ), (∀ p ∈ S, p ∈ 𝒟) →
      (∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) →
      (orderAtCusp' f : ℂ) +
      ∑ s ∈ S, (-generalizedWindingNumber
        (mkFDWindingDataFull_of_boundaryWinding hH h_boundary).boundary (↑s : ℂ)) *
        ↑(orderOfVanishingAt' (⇑f) s) = (k : ℂ) / 12) :
    (orderAtCusp' f : ℂ) +
    (1/2 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointI') +
    (1/3 : ℂ) * ↑(orderOfVanishingAt' (⇑f) ellipticPointRho') +
    ∑ᶠ (q : NonEllOrbit), ordOrbitQ f q =
    (k : ℂ) / 12 :=
  valence_formula_of_windingDataFull f hf hH
    (mkFDWindingDataFull_of_boundaryWinding hH h_boundary)
    h_above h_identity

/-! ### Summary of the discharge path

To get the fully unconditional valence formula via the ForMathlib chain:

1. **Boundary winding** (`h_boundary`): Proved per-point via `SingleCrossingData`
   + `SmoothBoundaryWindingData`. The analytical content is the FTC computation
   at each crossing, yielding the PV integral limit `-πi`.

2. **Height bound** (`h_above`): From `exists_height_above_fd_zeros` + padding.
   All FD zeros lie in a bounded region by `finite_zeros_in_fd`.

3. **Winding-form identity** (`h_identity`): The output of the generalized residue
   theorem applied to `logDeriv(f)` along the FD boundary. This combines:
   - Residue side: `∮ logDeriv(f) = Σ 2πi · gWN(s) · ord(f,s)`
   - Modular side: T-periodicity (verticals cancel), S-transformation (arcs give
     `-k/6`), q-expansion (horizontal gives cusp order)

   In the `ValenceFormula/` chain, this is proved unconditionally via
   `pv_chain_identity` (uniqueness of limits for the ε-truncated integral).

4. **Assembly**: `mk_residueModularData` → `valence_formula_from_residueModularData`
   produces the textbook formula. Or use `valence_formula_of_windingDataFull` directly.

The bottleneck is step (3): proving the identity for the PiecewiseC1Path version
of `generalizedWindingNumber`. The `ValenceFormula/CoreIdentity.lean` proves the
analogous identity for `generalizedWindingNumber'` (on the raw curve) via the
PV chain. Bridging between the two winding number notions (raw curve vs PC1Path)
is where the two chains connect. -/

end
