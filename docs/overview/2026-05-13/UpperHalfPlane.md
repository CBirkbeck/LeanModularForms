# UpperHalfPlane.lean

## theorem/ModularGroup.modular_S_sq
- **Type**: `S * S = -1`
- **What**: Square of the modular `S` matrix equals `-1`.
- **How**: `ext i j; simp [S]; fin_cases i <;> fin_cases j <;> simp`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: Modular group element-level computations; downstream identities using `S² = -I`.
- **Visibility**: public; in `ModularGroup` namespace.
- **Lines**: ~9-12.
- **Notes**: From Sphere Pack project; candidate for mathlib `LinearAlgebra/Matrix/SpecialLinearGroup.lean`.

### File Summary
Single identity `S * S = -1` for the modular `S` matrix. Candidate for mathlib upstream. No project deps.
