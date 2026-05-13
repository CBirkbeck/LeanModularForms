# TrigLemmas.lean

## theorem/exp_real_angle_I
- **Type**: `(θ : ℝ) → Complex.exp (↑θ * I) = ↑(Real.cos θ) + ↑(Real.sin θ) * I`
- **What**: Euler's formula for `exp(θ·i)` with real `θ`, in `ℂ`-coerced form.
- **How**: `rw [Complex.exp_mul_I]; simp [Complex.ofReal_cos, Complex.ofReal_sin]`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: `WindingWeights/Common.lean`, `RectHomotopy/HomotopyDef.lean`.
- **Visibility**: public.
- **Lines**: ~17-20.
- **Notes**: Euler-formula expansion.

## theorem/cos_two_pi_div_three
- **Type**: `Real.cos (2 * Real.pi / 3) = -1 / 2`
- **What**: Exact value `cos(2π/3) = -1/2`.
- **How**: Rewrite `2π/3 = π - π/3`; `Real.cos_pi_sub`, `Real.cos_pi_div_three`; `ring`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: `WindingWeights/Common.lean`, `RectHomotopy/HomotopyDef.lean` (ρ vertex computations).
- **Visibility**: public.
- **Lines**: ~22-25.
- **Notes**: Used at the elliptic point ρ.

## theorem/sin_two_pi_div_three
- **Type**: `Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2`
- **What**: Exact value `sin(2π/3) = √3/2`.
- **How**: Rewrite `2π/3 = π - π/3`; `Real.sin_pi_sub`; `Real.sin_pi_div_three`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: `WindingWeights/Common.lean`, `RectHomotopy/HomotopyDef.lean`.
- **Visibility**: public.
- **Lines**: ~27-30.
- **Notes**: Imaginary part of ρ.

### File Summary
Three shared trig lemmas: Euler-formula expansion `exp(θI)` and exact values `cos(2π/3) = -1/2`, `sin(2π/3) = √3/2`. Used by both `WindingWeights/Common` and `RectHomotopy/HomotopyDef`. No project deps.
