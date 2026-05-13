# ValenceFormula/PVChain.lean

## theorem/pv_chain_identity
- **Type**: `{k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0) (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) → ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H → ∑ s ∈ S, generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ) = -((k : ℂ) / 12 - (orderAtCusp' f : ℂ))`
- **What**: PV chain identity equating residue-side gWN-weighted order sum to negated modular side (`-(k/12 - ord_∞)`).
- **How**: Obtain `cpv_residue_side_tendsto` and `cpv_modular_side_tendsto`; take `max H₁ H₂`; apply `tendsto_nhds_unique` to get `2πi · Σ ... = -(2πi · (k/12 - ord_∞))`; conclude by `mul_left_cancel₀` against nonzero `2πi`.
- **Hypotheses**: `hf : f ≠ 0`; finset `S` containing all zeros in fundamental domain.
- **Uses-from-project**: `ValenceFormula.PVChain.Assembly`, `ValenceFormula.PVChain.Assembly.ResidueSide`, `cpv_residue_side_tendsto`, `cpv_modular_side_tendsto`, `generalizedWindingNumber'`, `fdBoundary_H`, `orderOfVanishingAt'`, `orderAtCusp'`.
- **Used by**: Downstream chain combining residue and modular sides into the valence formula.
- **Visibility**: public.
- **Lines**: ~31-49.
- **Notes**: Uses `tendsto_nhds_unique` to equate two limits of the same ε-truncated integral, then cancels `2πi` via `mul_left_cancel₀`.

### File Summary
Single bridge theorem combining residue-side and modular-side Tendsto results into a clean PV chain identity via limit uniqueness and `2πi` cancellation. Top-level wrapper for the `ValenceFormula.PVChain` directory.
