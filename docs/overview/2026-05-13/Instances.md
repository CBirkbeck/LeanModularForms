# Instances.lean

## instance/instNormSMulClassRealComplex
- **Type**: `NormSMulClass ℝ ℂ` (noncomputable instance)
- **What**: Provides the `NormSMulClass ℝ ℂ` instance.
- **How**: `NormedSpace.toNormSMulClass`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: All ForMathlib files needing the `ℝ`-scalar-on-`ℂ` chain (since mathlib 4.29 removed the auto-instance).
- **Visibility**: public.
- **Lines**: ~22-23.
- **Notes**: Restores chain broken in mathlib 4.29.

## instance/instIsBoundedSMulRealComplex
- **Type**: `IsBoundedSMul ℝ ℂ` (noncomputable instance)
- **What**: Provides `IsBoundedSMul ℝ ℂ`.
- **How**: `NormSMulClass.toIsBoundedSMul`.
- **Hypotheses**: none.
- **Uses-from-project**: `instNormSMulClassRealComplex`.
- **Used by**: Downstream files needing bounded smul.
- **Visibility**: public.
- **Lines**: ~25-26.
- **Notes**: Part of restored chain.

## instance/instContinuousSMulRealComplex
- **Type**: `ContinuousSMul ℝ ℂ` (noncomputable instance)
- **What**: Provides `ContinuousSMul ℝ ℂ`.
- **How**: `IsBoundedSMul.continuousSMul`.
- **Hypotheses**: none.
- **Uses-from-project**: `instIsBoundedSMulRealComplex`.
- **Used by**: Downstream files needing continuous smul of `ℝ` on `ℂ`.
- **Visibility**: public.
- **Lines**: ~28-29.
- **Notes**: Final link in restored chain.

## instance/instIsScalarTowerRealComplexComplex
- **Type**: `IsScalarTower ℝ ℂ ℂ`
- **What**: Provides the scalar tower instance.
- **How**: `inferInstance`.
- **Hypotheses**: none.
- **Uses-from-project**: [].
- **Used by**: Downstream files using scalar-tower coercions.
- **Visibility**: public.
- **Lines**: ~31.
- **Notes**: Consolidation point for previously-duplicated proofs.

### File Summary
Project-wide instance restoration file: four typeclass instances (`NormSMulClass`, `IsBoundedSMul`, `ContinuousSMul`, `IsScalarTower`) for `ℝ` acting on `ℂ`, restoring chain broken by mathlib 4.29 removal of auto-instance. Consolidated home so any file can `import LeanModularForms.ForMathlib.Instances` instead of redeclaring.
