# ResidueSide.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ResidueSide.lean
**Lines**: 153
**Imports**: `LeanModularForms.ForMathlib.ValenceFormula.PVChain`

## Entries

### theorem `cpv_residue_side_forMathlib`
- **Type**: theorem (with `include hf in`)
- **What**: Residue side of the valence formula: there exists `H₀ > √3/2` such that for all `H ≥ H₀`, the ε-truncated PV integrand of `logDeriv(f)` over `[0,5]` along `fdBoundary_H H` tends, as ε → 0⁺, to `2πi · ∑ s ∈ S, gWN'(γ, 0, 5, s) · ord(f, s)`.
- **How**: One-liner: `cpv_residue_side_tendsto f hf S hS hS_complete`.
- **Hypotheses**: `hf : f ≠ 0` (via `include`); `S : Finset UpperHalfPlane`, `hS : ∀ p ∈ S, p ∈ 𝒟`, `hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S`.
- **Uses-from-project**: `cpv_residue_side_tendsto` (from `ValenceFormula.PVChain.Assembly.ResidueSide`), `pvIntegrand`, `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `generalizedWindingNumber'`, `orderOfVanishingAt'`.
- **Used by**: `pv_chain_identity_forMathlib` (indirectly via `pv_chain_identity`); ForMathlib-native valence-formula chain assembly (`ResidueSideBridge.lean` and downstream).
- **Visibility**: public
- **Lines**: 78–86
- **Notes**: One-line wrapper of the legacy-chain `cpv_residue_side_tendsto`. The mathematical content (residue theorem applied to `logDeriv f`, CPV existence at on-curve singularities, integrand eventually agrees with on-curve restriction) lives in `ValenceFormula.PVChain.Assembly.ResidueSide`.

### theorem `cpv_modular_side_forMathlib`
- **Type**: theorem (with `include hf in`)
- **What**: Modular side: there exists `H₀ > √3/2` such that for all `H ≥ H₀`, the same ε-truncated PV integrand tends to `-(2πi · (k/12 - ord_∞(f)))`.
- **How**: One-liner: `cpv_modular_side_tendsto f hf S hS hS_complete`.
- **Hypotheses**: Same as `cpv_residue_side_forMathlib` (`hf : f ≠ 0`, `S : Finset UpperHalfPlane`, `hS`, `hS_complete`).
- **Uses-from-project**: `cpv_modular_side_tendsto`, `pvIntegrand`, `fdBoundary_H`, `sArcOfS`, `sVertOfS`, `orderAtCusp'`.
- **Used by**: `pv_chain_identity_forMathlib` (indirectly via `pv_chain_identity`); ForMathlib chain.
- **Visibility**: public
- **Lines**: 101–108
- **Notes**: One-line wrapper. Mathematical content: T-cancellation of vertical segments + S-arc `-(2πi)(k/12)` from modular identity `f(Sz) = z^k f(z)` + horizontal contribution `2πi · ord_∞` from q-expansion winding number — all lives in the assembled `cpv_modular_side_tendsto`.

### theorem `pv_chain_identity_forMathlib`
- **Type**: theorem (with `include hf in`)
- **What**: PV chain identity equating residue and modular sides: `Σ gWN'(γ, 0, 5, s) · ord(f, s) = -((k:ℂ)/12 - ord_∞(f))` for all sufficiently large `H`.
- **How**: One-liner: `pv_chain_identity f hf S hS hS_complete`.
- **Hypotheses**: Same as the two side theorems (`hf : f ≠ 0`, `S : Finset UpperHalfPlane`, `hS`, `hS_complete`).
- **Uses-from-project**: `pv_chain_identity` (uniqueness-of-limits + `2πi` cancellation already done inside).
- **Used by**: Final valence-formula assembly in `ResidueSideBridge.lean` and `ValenceFormulaBridged.lean`.
- **Visibility**: public
- **Lines**: 124–129
- **Notes**: One-line wrapper. The fundamental identity before substituting explicit winding weights.

### theorem `residue_side_rearrange`
- **Type**: theorem
- **What**: Pure algebra: from `weighted_sum = -((k:ℂ)/12 - ord_inf)` derive `ord_inf + (-weighted_sum) = (k:ℂ)/12`.
- **How**: `rw [h]; ring`.
- **Hypotheses**: `ord_inf weighted_sum : ℂ`, `h : weighted_sum = -((k : ℂ) / 12 - ord_inf)`.
- **Uses-from-project**: None (pure ℂ ring algebra).
- **Used by**: Algebraic rearrangement steps in downstream valence-formula assemblies.
- **Visibility**: public
- **Lines**: 136–139
- **Notes**: Sign-flipping helper.

### theorem `cancel_two_pi_I`
- **Type**: theorem
- **What**: If `2πi · L = -(2πi · R)`, then `L = -R`.
- **How**: Show `hpi : (2 : ℂ) * Real.pi * I ≠ 0` via `norm_num [Real.pi_ne_zero, I_ne_zero]`. Build `h' : 2 * Real.pi * I * L = 2 * Real.pi * I * (-R)` by `rw [h]; ring`. Conclude `mul_left_cancel₀ hpi h'`.
- **Hypotheses**: `L R : ℂ`, `h : 2 * ↑Real.pi * I * L = -(2 * ↑Real.pi * I * R)`.
- **Uses-from-project**: None (pure ℂ algebra; `Real.pi_ne_zero`, `I_ne_zero` from Mathlib).
- **Used by**: Final cancellation step in valence-formula assemblies.
- **Visibility**: public
- **Lines**: 143–151
- **Notes**: Standard `2πi`-cancellation algebra lemma.

## File Summary

Five public theorems (three with `include hf in`). The first three are one-line ForMathlib-native wrappers exposing the three core results assembled in `ValenceFormula.PVChain.Assembly`: residue-side tendsto, modular-side tendsto, and the equated PV chain identity for the residue/modular sides of the valence formula applied to `logDeriv(f)` along the FD boundary. The last two (`residue_side_rearrange`, `cancel_two_pi_I`) are pure-algebra helpers used downstream. The file's role is purely as a ForMathlib-namespaced thin re-exporter: all real mathematical work is delegated to `cpv_residue_side_tendsto`, `cpv_modular_side_tendsto`, and `pv_chain_identity` in the deeper `ValenceFormula.PVChain` modules.
