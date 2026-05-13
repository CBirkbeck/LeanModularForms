# EllipticPoints.lean — Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/EllipticPoints.lean`
Lines: 117

## def/`ellipticPointI'`
- **Type**: `UpperHalfPlane`
- **What**: The elliptic point `i` as an `UpperHalfPlane` element.
- **How**: Bundled subtype literal `⟨I, by simp [Complex.I_im]⟩`.
- **Hypotheses**: None.
- **Uses-from-project**: None (mathlib `UpperHalfPlane`, `Complex.I`).
- **Used by**: `ellipticPointI` (this file); valence formula consumers.
- **Visibility**: public
- **Lines**: 29

## abbrev/`ellipticPointI`
- **Type**: `ℂ`
- **What**: The elliptic point `i` as a complex number.
- **How**: Coercion `(ellipticPointI' : ℂ)`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointI'`.
- **Used by**: `ellipticPointI_mem_fd` (this file); winding/valence consumers.
- **Visibility**: public
- **Lines**: 32

## def/`ellipticPointRho'`
- **Type**: `UpperHalfPlane`
- **What**: The elliptic point `ρ = e^{2πi/3} = -1/2 + (√3/2)i` as an `UpperHalfPlane` element.
- **How**: Subtype literal `⟨-1/2 + (Real.sqrt 3 / 2) * I, by simp …; norm_num⟩` (im positive via `Real.sqrt 3 / 2 > 0`).
- **Hypotheses**: None.
- **Uses-from-project**: None (mathlib).
- **Used by**: `ellipticPointRho`, `rho_normSq_eq_one`, `ellipticPointRho_norm`, `ellipticPointRho_mem_fd`, `ellipticPointI_ne_rho`, `ellipticPointRho_add_one_eq` (this file).
- **Visibility**: public
- **Lines**: 35–38

## abbrev/`ellipticPointRho`
- **Type**: `ℂ`
- **What**: `ρ` as a complex number.
- **How**: Coercion `(ellipticPointRho' : ℂ)`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRho'`.
- **Used by**: `ellipticPointRho_add_one_eq`, `rho_normSq_eq_one`, `ellipticPointRho_norm` (this file); downstream `WindingWeightsUnconditional.lean`, valence formula.
- **Visibility**: public
- **Lines**: 41

## def/`ellipticPointRhoPlusOne'`
- **Type**: `UpperHalfPlane`
- **What**: The T-translate `ρ + 1 = e^{πi/3} = 1/2 + (√3/2)i`.
- **How**: Subtype literal analogous to `ellipticPointRho'`.
- **Hypotheses**: None.
- **Uses-from-project**: None.
- **Used by**: `ellipticPointRhoPlusOne`, `rho_plus_one_normSq_eq_one`, `ellipticPointRhoPlusOne_norm` (this file); downstream consumers.
- **Visibility**: public
- **Lines**: 44–47

## abbrev/`ellipticPointRhoPlusOne`
- **Type**: `ℂ`
- **What**: `ρ + 1` as a complex number.
- **How**: Coercion `(ellipticPointRhoPlusOne' : ℂ)`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRhoPlusOne'`.
- **Used by**: `ellipticPointRho_add_one_eq`, `rho_plus_one_normSq_eq_one`, `ellipticPointRhoPlusOne_norm` (this file); downstream consumers.
- **Visibility**: public
- **Lines**: 50

## theorem/`ellipticPointRho_add_one_eq`
- **Type**: `ellipticPointRho + 1 = ellipticPointRhoPlusOne`
- **What**: `ρ + 1` agrees with the explicit `1/2 + (√3/2)i`.
- **How**: `change ... ; ring`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRho`, `ellipticPointRhoPlusOne`.
- **Used by**: Identifies `ρ` and `ρ+1` orbifold contributions in valence formula.
- **Visibility**: public
- **Lines**: 52–55

## lemma/`rho_normSq_eq_one` (private)
- **Type**: `Complex.normSq (ellipticPointRho' : ℂ) = 1`
- **What**: `|ρ|² = 1`.
- **How**: Rewrite as `(-1/2) + (√3/2)·I`, apply `Complex.normSq_add_mul_I`, then `(√3/2)² = 3/4` via `Real.sq_sqrt` and `ring`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRho'`.
- **Used by**: `ellipticPointRho_norm`, `ellipticPointRho_mem_fd` (this file).
- **Visibility**: private
- **Lines**: 57–68

## lemma/`rho_plus_one_normSq_eq_one` (private)
- **Type**: `Complex.normSq (ellipticPointRhoPlusOne' : ℂ) = 1`
- **What**: `|ρ+1|² = 1`.
- **How**: Same structure as `rho_normSq_eq_one`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRhoPlusOne'`.
- **Used by**: `ellipticPointRhoPlusOne_norm` (this file).
- **Visibility**: private
- **Lines**: 70–82

## theorem/`ellipticPointRhoPlusOne_norm`
- **Type**: `‖ellipticPointRhoPlusOne‖ = 1`
- **What**: `ρ+1` lies on the unit circle.
- **How**: `change Real.sqrt _ = 1`; use `rho_plus_one_normSq_eq_one` and `Real.sqrt_one`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRhoPlusOne`, `rho_plus_one_normSq_eq_one`.
- **Used by**: Winding-weight machinery for the `ρ+1` crossing.
- **Visibility**: public
- **Lines**: 84–86

## theorem/`ellipticPointRho_norm`
- **Type**: `‖ellipticPointRho‖ = 1`
- **What**: `ρ` lies on the unit circle.
- **How**: As above with `rho_normSq_eq_one`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRho`, `rho_normSq_eq_one`.
- **Used by**: Winding-weight machinery for the `ρ` crossing.
- **Visibility**: public
- **Lines**: 88–90

## theorem/`ellipticPointI_mem_fd`
- **Type**: `ellipticPointI' ∈ 𝒟`
- **What**: `i` is in the canonical fundamental domain `𝒟 := ModularGroup.fd`.
- **How**: Refine the two conjuncts: `normSq_I = 1` (via `simp`), and re-component `re = 0` is in `[-1/2, 1/2]` (via `norm_num`).
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointI'`.
- **Used by**: Valence-formula assembly.
- **Visibility**: public
- **Lines**: 92–96

## theorem/`ellipticPointRho_mem_fd`
- **Type**: `ellipticPointRho' ∈ 𝒟`
- **What**: `ρ` is in `𝒟`.
- **How**: `refine ⟨rho_normSq_eq_one.ge, ?_⟩`; close `re = -1/2` ∈ `[-1/2, 1/2]` via `norm_num`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointRho'`, `rho_normSq_eq_one`.
- **Used by**: Valence-formula assembly.
- **Visibility**: public
- **Lines**: 98–101

## lemma/`ellipticPointI_ne_rho`
- **Type**: `ellipticPointI' ≠ ellipticPointRho'`
- **What**: `i` and `ρ` are distinct elliptic points.
- **How**: Real-part contradiction — `(i).re = 0`, `(ρ).re = -1/2`; `norm_num` closes after `rw [h]`.
- **Hypotheses**: None.
- **Uses-from-project**: `ellipticPointI'`, `ellipticPointRho'`.
- **Used by**: Distinguishing summands in the valence formula.
- **Visibility**: public
- **Lines**: 103–107

## def/`orderOfVanishingAt'`
- **Type**: `(UpperHalfPlane → ℂ) → UpperHalfPlane → ℤ`
- **What**: Order of vanishing of `f` at `z ∈ ℍ`, extracted from the meromorphic-order of the lifted function on a neighborhood of `(z : ℂ)`.
- **How**: `(meromorphicOrderAt (fun w ↦ if h : 0 < w.im then f ⟨w,h⟩ else 0) (z : ℂ)).untop₀` — convert the `WithTop ℤ` to `ℤ` via `untop₀` (top maps to `0`).
- **Hypotheses**: None (totalised by `untop₀`).
- **Uses-from-project**: None.
- **Used by**: `FDWindingDataFullSeg1Seg4.lean` (`valence_formula_unconditional_mkD`); all valence-formula consumers.
- **Visibility**: public
- **Lines**: 110–111

## def/`orderAtCusp'`
- **Type**: For `f : ModularForm (Gamma 1) k`, returns `ℤ`.
- **What**: Order of vanishing at the cusp via the `q`-expansion.
- **How**: `(ModularFormClass.qExpansion 1 f).order.toNat` cast to `ℤ`.
- **Hypotheses**: implicit `k : ℤ`.
- **Uses-from-project**: None directly (uses mathlib `ModularFormClass.qExpansion`).
- **Used by**: `HorizontalContribution.lean` (`horizontalContribution_eq`); `FDWindingDataFullSeg1Seg4.lean` (`valence_formula_unconditional_mkD`); valence formula consumers.
- **Visibility**: public
- **Lines**: 114–115

## File Summary
Foundational definitions for the valence-formula chain: the three elliptic points (`i`, `ρ`, `ρ+1`) as `UpperHalfPlane` and `ℂ` values, basic lemmas on their norms (`= 1` for `ρ`, `ρ+1`) and fundamental-domain membership, the `T`-translation identity `ρ + 1 = ρ+1`, distinctness `i ≠ ρ`, and the order-of-vanishing definitions `orderOfVanishingAt'` (interior, via `meromorphicOrderAt`) and `orderAtCusp'` (q-expansion order). All proofs are elementary (`simp`, `norm_num`, `ring`, one `Real.sq_sqrt` computation). Pure mathlib-style definition file with no project dependencies.
