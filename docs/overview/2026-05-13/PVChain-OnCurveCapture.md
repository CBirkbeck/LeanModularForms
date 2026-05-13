# OnCurveCapture.lean Inventory

### `theorem oncurve_arc_capture`
- **Type**: `(S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 5) (h_norm : ‖fdBoundary_H H t‖ = 1) (h_zero : modularFormCompOfComplex f (fdBoundary_H H t) = 0) : fdBoundary_H H t ∈ (↑(sArcOfS S) : Set ℂ)`
- **What**: A zero of `f` on the arc segment (`‖·‖ = 1`) of the height-`H` fundamental domain boundary is captured by `sArcOfS S`.
- **How**: 35-line proof. Uses `fdBoundary_H_im_ge_sqrt3_div_2` to ensure `im > 0`; from `‖z‖ = 1` derives `re² + im² = 1` then `im² ≥ 3/4` (via `mul_self_le_mul_self` and `Real.sq_sqrt`); deduces `|re| ≤ 1/2` by `nlinarith` on `sq_nonneg (re ± 1/2)`. Lifts `z` to `ℍ` via the positive im, shows `p ∈ 𝒟` (Complex.normSq ≥ 1 and `|re| ≤ 1/2`), uses `UpperHalfPlane.ofComplex_apply_of_im_pos` to identify `f p = 0`. Applies `hS_complete` with `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`. Finally unfolds `sArcOfS` and selects the filter image. Specific lemma: `UpperHalfPlane.ofComplex_apply_of_im_pos`.
- **Hypotheses**: `S` finite; completeness; `√3/2 < H`; `t ∈ [0,5]`; `‖fdBoundary_H H t‖ = 1`; `f` vanishes at that point.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_im_ge_sqrt3_div_2`, `modularFormCompOfComplex`, `sArcOfS`, `orderOfVanishingAt'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`, `𝒟`
- **Used by**: `oncurve_full_capture`
- **Visibility**: public
- **Lines**: 36-72
- **Notes**: >30 lines proof; depends on `attribute [local instance] Classical.propDecidable`.

### `theorem oncurve_vert_capture`
- **Type**: `(S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H' : ℝ} (hH' : Real.sqrt 3 / 2 < H') {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) (h_zero : modularFormCompOfComplex f (fdBoundary_H H' t) = 0) : (fdBoundary_H H' t : ℂ) ∈ (↑(sVertOfS S) : Set ℂ)`
- **What**: A zero on segment 1 (right vertical, `Re = 1/2`, `Im > √3/2`) is captured by `sVertOfS S`.
- **How**: 55-line proof. Rewrites `z = fdBoundary_seg1_H` via `fdBoundary_H_eq_seg1_H`; extracts `re = 1/2`, `im = H' - t(H' - √3/2)`; deduces `im > √3/2` (via `nlinarith` on `ht.2`). Computes `‖z‖² = re² + im² > 1` by `mul_self_lt_mul_self` and `Real.sq_sqrt`, then `Real.sqrt_lt_sqrt`. Lifts to ℍ, shows `p ∈ 𝒟`, applies `hS_complete` and `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`, then unfolds `sVertOfS` four levels deep to land in the right `Finset.image` branch. Specific lemma: `fdBoundary_H_eq_seg1_H`.
- **Hypotheses**: completeness; `H' > √3/2`; `t ∈ (0,1)`; `f` vanishes.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_seg1_H`, `modularFormCompOfComplex`, `sVertOfS`, `orderOfVanishingAt'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`, `𝒟`
- **Used by**: `oncurve_full_capture`
- **Visibility**: public
- **Lines**: 75-127
- **Notes**: >30 lines proof.

### `theorem height_contradiction`
- **Type**: `(S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H : ℝ} (hH_ge1 : 1 ≤ H) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) {z : ℂ} (h_im : z.im = H) (h_re : |z.re| ≤ 1/2) (h_zero : modularFormCompOfComplex f z = 0) : False`
- **What**: If `f` vanishes at a height-`H` point with `|re| ≤ 1/2` and all elements of `S` have imaginary part strictly less than `H`, contradiction.
- **How**: From `im = H ≥ 1 > 0` lift to ℍ; show `p ∈ 𝒟` (Complex.normSq z ≥ 1 + sq_nonneg; `|re| ≤ 1/2` direct), use `hS_complete` and `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`; `linarith` against `hH_bound p hp_in_S`.
- **Hypotheses**: `1 ≤ H`; bound on S; `z.im = H`, `|z.re| ≤ 1/2`; `f z = 0`.
- **Uses from project**: `modularFormCompOfComplex`, `orderOfVanishingAt'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`, `𝒟`
- **Used by**: `oncurve_full_capture`
- **Visibility**: public
- **Lines**: 130-148
- **Notes**: none

### `lemma seg4_eq_seg1_minus_one_H`
- **Type**: `(H : ℝ) (s : ℝ) (_hs : s ∈ Icc 0 1) : fdBoundary_seg4_H H (4 - s) = fdBoundary_seg1_H H s - 1`
- **What**: T-translation correspondence: seg4 at parameter `4 - s` equals seg1 at `s` translated by `-1`.
- **How**: Unfold both definitions; use `push_cast` and `ring` after rewriting `(4 - s) - 3 = 1 - s`.
- **Hypotheses**: `s ∈ [0,1]`.
- **Uses from project**: `fdBoundary_seg4_H`, `fdBoundary_seg1_H`
- **Used by**: `oncurve_seg4_capture`
- **Visibility**: public
- **Lines**: 151-159
- **Notes**: uses `omit hf in` to drop the `hf` hypothesis for this lemma.

### `theorem oncurve_seg4_capture`
- **Type**: `(S : Finset ℍ) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H : ℝ} (hH : Real.sqrt 3 / 2 < H) {t : ℝ} (ht : t ∈ Set.Ioo (3:ℝ) 4) (h_zero : modularFormCompOfComplex f (fdBoundary_H H t) = 0) : fdBoundary_H H t ∈ (↑(sVertOfS S) : Set ℂ)`
- **What**: A zero on segment 4 (left vertical, `t ∈ (3,4)`) is captured by `sVertOfS S` via T-periodicity (translating by +1 sends seg4 to seg1).
- **How**: 70-line proof. Use `fdBoundary_H_eq_seg4_H` to convert `z` to seg4; set `s = 4 - t ∈ (0,1)`; show `z = fdBoundary_seg1_H H s - 1` via `seg4_eq_seg1_minus_one_H`. Get T-periodicity of `modularFormCompOfComplex f` with period 1 from `SlashInvariantFormClass.periodic_comp_ofComplex f ModularFormClass.one_mem_strictPeriods_SL2Z`, then `z + 1 = fdBoundary_seg1_H H s` ⇒ `f vanishes at the seg1 lift`. Same machinery as `oncurve_vert_capture` afterward (re = 1/2, im > √3/2, `‖·‖ > 1`, lift to ℍ, `hp_fd`, `hS_complete`, image extraction). Selects the seg4 (right) subset of `sVertOfS` (whereas vert_capture selects left). Specific lemma: `SlashInvariantFormClass.periodic_comp_ofComplex`.
- **Hypotheses**: completeness; `H > √3/2`; `t ∈ (3,4)`; `f` vanishes.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_eq_seg4_H`, `seg4_eq_seg1_minus_one_H`, `fdBoundary_seg1_H`, `modularFormCompOfComplex`, `sVertOfS`, `orderOfVanishingAt'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`, `𝒟`, `SlashInvariantFormClass.periodic_comp_ofComplex`, `ModularFormClass.one_mem_strictPeriods_SL2Z`
- **Used by**: `oncurve_full_capture`
- **Visibility**: public
- **Lines**: 162-232
- **Notes**: >30 lines proof.

### `theorem oncurve_full_capture`
- **Type**: `(S : Finset ℍ) (_hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) {H : ℝ} (hH_ge1 : 1 ≤ H) (hH_sqrt3 : Real.sqrt 3 / 2 < H) (hH_bound : ∀ s ∈ S, (s : ℂ).im < H) : ∀ t ∈ Icc (0:ℝ) 5, modularFormCompOfComplex f (fdBoundary_H H t) = 0 → fdBoundary_H H t ∈ (↑(sArcOfS S ∪ sVertOfS S) : Set ℂ)`
- **What**: Full on-curve capture: every zero of `f` on the height-`H` fundamental-domain boundary is in `sArcOfS S ∪ sVertOfS S`.
- **How**: 55-line proof. Case-split `t ≤ 1`: subcase `t = 0` (seg1 corner) — uses `height_contradiction` (im = H, |re| = 1/2). Subcase `t = 1` — corner `ρ + 1`, falls into `sArcOfS` via `fdBoundary_H_at_one_eq_rho_plus_one` and `sArcOfS_rho_plus_one_in`. Otherwise `t ∈ (0,1)` ⇒ `oncurve_vert_capture`. Else `t ≤ 3`: subcase `t = 3` — corner ρ via `fdBoundary_H_at_three_eq_rho` + `sArcOfS_rho_in`. Otherwise `t ∈ (1,3)` ⇒ arc, `‖·‖ = 1` from `fdBoundary_H_eq_arc` + `Complex.norm_exp_ofReal_mul_I`, then `oncurve_arc_capture`. Else `t ≤ 4`: subcase `t = 4` — seg5 corner, `height_contradiction`. Otherwise `t ∈ (3,4)` ⇒ `oncurve_seg4_capture`. Else `t ∈ (4,5]` ⇒ seg5 top, `height_contradiction` (im = H). Specific lemmas: `fdBoundary_H_at_one_eq_rho_plus_one`, `fdBoundary_H_at_three_eq_rho`, `fdBoundary_H_eq_arc`, `oncurve_vert_capture`, `oncurve_arc_capture`, `oncurve_seg4_capture`, `height_contradiction`.
- **Hypotheses**: `S ⊆ 𝒟`; completeness; `1 ≤ H`; `H > √3/2`; `S` bounded above by `H`.
- **Uses from project**: `fdBoundary_H`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_seg1_H`, `fdBoundary_H_eq_seg4_H`, `fdBoundary_seg4_H`, `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`, `fdBoundary_H_eq_arc`, `fdBoundary_H_at_one_eq_rho_plus_one`, `fdBoundary_H_at_three_eq_rho`, `sArcOfS`, `sVertOfS`, `sArcOfS_rho_in`, `sArcOfS_rho_plus_one_in`, `oncurve_arc_capture`, `oncurve_vert_capture`, `oncurve_seg4_capture`, `height_contradiction`, `modularFormCompOfComplex`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 235-296
- **Notes**: >30 lines proof.

## File Summary

**File**: `LeanModularForms/ForMathlib/ValenceFormula/PVChain/OnCurveCapture.lean` (298 lines)

Establishes that any zero of a nonzero modular form `f : ModularForm (Gamma 1) k` lying on the height-`H` fundamental-domain boundary curve (the piecewise contour with arc + four straight segments) is "captured" — i.e. belongs to the singular set `sArcOfS S ∪ sVertOfS S` for the user-provided complete zero list `S`. This is the on-curve half of the singular-set-completeness argument used by the principal-value/valence-formula chain. Imports `PVChain.Helpers` and `Orbits`. Layout:
- `oncurve_arc_capture` handles arc points (`‖·‖ = 1`, `t ∈ [1,3]`).
- `oncurve_vert_capture` handles right vertical (seg1, `t ∈ (0,1)`, `Re = 1/2`).
- `height_contradiction` rules out zeros at the top (`Im = H`).
- `seg4_eq_seg1_minus_one_H` (omit `hf`) gives the T-translation identity.
- `oncurve_seg4_capture` handles left vertical (seg4, `t ∈ (3,4)`) via T-periodicity.
- `oncurve_full_capture` assembles the full case analysis for `t ∈ [0,5]`.

Three of the six proofs are >30 lines. No `sorry`, no axioms, no `set_option`. Uses `attribute [local instance] Classical.propDecidable`. Pattern: lift `ℂ`-points to `ℍ`, check `𝒟` membership, apply user-supplied completeness, then extract membership in the Finset.image-defined singular set.
