# ResidueSideBridge.lean

## theorem/cpv_residue_side_HasCauchyPVOn
- **Type**: `{k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0) (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) → ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H → ∀ (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (_hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t), HasCauchyPVOn (sArcOfS S ∪ sVertOfS S) (logDeriv (modularFormCompOfComplex f)) γ (2 * ↑Real.pi * I * ∑ s ∈ S, generalizedWindingNumber' (fdBoundary_H H) 0 5 (↑s : ℂ) * (orderOfVanishingAt' (⇑f) s : ℂ))`
- **What**: Residue side in ForMathlib form — the ε-truncated integral of `logDeriv(f)` around any `PiecewiseC1Path` agreeing with `fdBoundaryFun H` converges to `2πi · Σ gWN(γ, s) · ord(f, s)`.
- **How**: Obtains old-chain `cpv_residue_side_forMathlib` data, then applies `hasCauchyPVOn_of_cauchyPVOn'_tendsto` to each H.
- **Hypotheses**: `hf : f ≠ 0`; finset `S` of zeros in fundamental domain, complete.
- **Uses-from-project**: `FDBoundaryReparametrization`, `ResidueSide`, `cpv_residue_side_forMathlib`, `hasCauchyPVOn_of_cauchyPVOn'_tendsto`, `PiecewiseC1Path`, `fdStart`, `fdBoundaryFun`, `HasCauchyPVOn`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`, `generalizedWindingNumber'`, `fdBoundary_H`, `orderOfVanishingAt'`.
- **Used by**: Bridges old-chain residue side to new-chain `HasCauchyPVOn`; consumed downstream by combiners with `valence_formula_unconditional_mkD`.
- **Visibility**: public.
- **Lines**: ~41-51.
- **Notes**: Bridge file converting old-chain results into new-chain HasCauchyPVOn shape.

## theorem/cpv_modular_side_HasCauchyPVOn
- **Type**: `{k : ℤ} (f : ModularForm (Gamma 1) k) (hf : f ≠ 0) (S : Finset UpperHalfPlane) (hS : ∀ p ∈ S, p ∈ 𝒟) (hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S) → ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ {H : ℝ}, H₀ ≤ H → ∀ (γ : PiecewiseC1Path (fdStart H) (fdStart H)) (_hγ : ∀ t ∈ Icc (0 : ℝ) 1, γ.toPath.extend t = fdBoundaryFun H t), HasCauchyPVOn (sArcOfS S ∪ sVertOfS S) (logDeriv (modularFormCompOfComplex f)) γ (-(2 * ↑Real.pi * I * ((k : ℂ) / 12 - (orderAtCusp' f : ℂ))))`
- **What**: Modular side in ForMathlib form — the ε-truncated integral of `logDeriv(f)` around any matching `PiecewiseC1Path` converges to `-(2πi)(k/12 - ord_∞)`.
- **How**: Obtains old-chain `cpv_modular_side_forMathlib` data, then applies `hasCauchyPVOn_of_cauchyPVOn'_tendsto`.
- **Hypotheses**: `hf : f ≠ 0`; finset `S` of zeros in fundamental domain, complete.
- **Uses-from-project**: `cpv_modular_side_forMathlib`, `hasCauchyPVOn_of_cauchyPVOn'_tendsto`, `PiecewiseC1Path`, `HasCauchyPVOn`, `fdBoundaryFun`, `modularFormCompOfComplex`, `orderAtCusp'`, `sArcOfS`, `sVertOfS`.
- **Used by**: Bridges old-chain modular side to new-chain HasCauchyPVOn; consumed downstream.
- **Visibility**: public.
- **Lines**: ~57-65.
- **Notes**: Mirror of residue-side bridge, with the modular limit value.

### File Summary
Two bridging theorems that convert old-chain `cpv_*_side_forMathlib` results into the new-chain `HasCauchyPVOn` shape suitable for combining with `valence_formula_unconditional_mkD`. Both wrap existing infrastructure via `hasCauchyPVOn_of_cauchyPVOn'_tendsto`.
