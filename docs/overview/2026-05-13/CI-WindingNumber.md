# ContourIntegral/WindingNumber.lean

## theorem/ContourIntegral.gWN_eq_of_pv_tendsto
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) (L : ℂ) (h : Tendsto (fun ε => ∫ t in a..b, if ε < ‖(γ t - s : ℂ) - 0‖ then (γ t - s)⁻¹ * deriv (fun t => γ t - s) t else 0) (𝓝[Ioi 0] 0) (𝓝 L)) → generalizedWindingNumber' γ a b s = L / (2 * Real.pi * I)`
- **What**: General PV→gWN conversion: if the PV integral of `(γ - s)⁻¹·(γ - s)'` tends to `L`, then `gWN' γ a b s = L / (2πi)`.
- **How**: `h.limUnder_eq` gives `cauchyPrincipalValue' = L`; then `simp` unfolds `generalizedWindingNumber'`.
- **Hypotheses**: tendsto hypothesis on truncated PV integrand.
- **Uses-from-project**: `ClassicalCPV`, `generalizedWindingNumber'`, `cauchyPrincipalValue'`.
- **Used by**: `gWN_eq_neg_half_of_pv_tendsto`, `gWN_eq_neg_sixth_of_pv_tendsto`; downstream winding number computations.
- **Visibility**: public; in namespace `ContourIntegral`.
- **Lines**: ~22-30.
- **Notes**: Shared final step for converting PV-integral limits into gWN values.

## theorem/ContourIntegral.gWN_eq_neg_half_of_pv_tendsto
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) (h : Tendsto (fun ε => ...) (𝓝[Ioi 0] 0) (𝓝 (-(Real.pi * I)))) → generalizedWindingNumber' γ a b s = -1/2`
- **What**: Specialization with `L = -πi` giving `gWN = -1/2`.
- **How**: `h.limUnder_eq`; `simp` unfolds gWN'; `field_simp [Real.pi_ne_zero, I_ne_zero]`.
- **Hypotheses**: tendsto to `-(π * I)`.
- **Uses-from-project**: `generalizedWindingNumber'`, `cauchyPrincipalValue'`.
- **Used by**: Half-residue winding-number computations (boundary edges of FD).
- **Visibility**: public.
- **Lines**: ~33-42.
- **Notes**: Used for edge contributions on FD boundary.

## theorem/ContourIntegral.gWN_eq_neg_sixth_of_pv_tendsto
- **Type**: `(γ : ℝ → ℂ) (a b : ℝ) (s : ℂ) (h : Tendsto (fun ε => ...) (𝓝[Ioi 0] 0) (𝓝 (-(Real.pi / 3 * I)))) → generalizedWindingNumber' γ a b s = -1/6`
- **What**: Specialization with `L = -πi/3` giving `gWN = -1/6` (60°-corner contribution).
- **How**: `h.limUnder_eq`; `simp`; `field_simp`; `norm_num`.
- **Hypotheses**: tendsto to `-(π/3 * I)`.
- **Uses-from-project**: `generalizedWindingNumber'`, `cauchyPrincipalValue'`.
- **Used by**: Sixth-residue computations (ρ corner contribution on FD boundary).
- **Visibility**: public.
- **Lines**: ~45-55.
- **Notes**: Used for ρ-corner contribution where 60° angle gives -1/6.

### File Summary
Three theorems in `ContourIntegral` namespace converting PV-integral Tendsto data into generalized winding number values. General version plus two specialized constants `-1/2` (edge) and `-1/6` (60° corner).
