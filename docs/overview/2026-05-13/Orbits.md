# Inventory: Orbits.lean

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/Orbits.lean` (315 lines)

Purpose: SL(2,ℤ)-orbits on the upper half-plane and the order-of-vanishing for full-modular-group modular forms. Establishes:
1. SL(2,ℤ)-invariance of `orderOfVanishingAt'`.
2. The orbit quotient `OrbitFM`, its `i` and `ρ` orbits, and non-elliptic orbits.
3. Finiteness of zeros in the fundamental domain `𝒟` and finite support of `ordOrbitFM`.
4. The canonical zero set `s₀FM` and the T-equivalence of `ρ+1`'s orbit with `ρ`'s.

Imports: `LeanModularForms.ForMathlib.ModularInvariance`, `Mathlib.Analysis.Meromorphic.NormalForm`, `Mathlib.LinearAlgebra.Matrix.FixedDetMatrices`, `Mathlib.NumberTheory.ModularForms.LevelOne`.

Top-level context: `noncomputable section` with `variable {k : ℤ} (f : ModularForm (Gamma 1) k)`.

---

### `theorem ord_smul_eqFM`
- **Type**: `(g : SL(2, ℤ)) (p : ℍ) : orderOfVanishingAt' (⇑f) (g • p) = orderOfVanishingAt' (⇑f) p`
- **What**: Order of vanishing is invariant under the full modular group action.
- **How**: `g ∈ closure {S, T}` by `SpecialLinearGroup.SL2Z_generators`; induct on `Subgroup.closure_induction`; base case for S uses `ord_S_eq`, for T uses `UpperHalfPlane.modular_T_smul` + `ord_add_one_eq`; product/inverse closure cases use `mul_smul` and `smul_inv_smul`.
- **Hypotheses**: none beyond signature.
- **Uses from project**: `ord_S_eq`, `ord_add_one_eq`.
- **Used by**: `ordOrbitFM`.
- **Visibility**: public
- **Lines**: 45–71
- **Notes**: >20 lines.

### `abbrev OrbitFM`
- **Type**: `OrbitFM := MulAction.orbitRel.Quotient SL(2, ℤ) ℍ`
- **What**: The quotient of ℍ by the SL(2,ℤ)-action.
- **How**: Defined as a Mathlib quotient abbreviation.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `orbFM`, `ordOrbitFM`, `oiFM`, `orhoFM`, `NonEllOrbitFM`, `orbit_has_fd_repFM`, all downstream lemmas.
- **Visibility**: public
- **Lines**: 76

### `def orbFM`
- **Type**: `(p : ℍ) : OrbitFM := Quotient.mk'' p`
- **What**: Canonical map ℍ → OrbitFM.
- **How**: Quotient constructor.
- **Hypotheses**: none.
- **Uses from project**: `OrbitFM`.
- **Used by**: `ordOrbit_mkFM`, `oiFM`, `orhoFM`, `orbit_has_fd_repFM`, `finite_support_ordOrbitFM`, `orb_rho_plus_one_eq_orb_rhoFM`.
- **Visibility**: public
- **Lines**: 79

### `def ordOrbitFM`
- **Type**: `(q : OrbitFM) : ℤ := Quotient.liftOn' q (fun p => orderOfVanishingAt' (⇑f) p) (fun a b hab => …)`
- **What**: Order of vanishing lifted to orbits.
- **How**: Well-defined by `ord_smul_eqFM` discharging the orbit-relation condition `MulAction.orbitRel_apply`.
- **Hypotheses**: none beyond `f`.
- **Uses from project**: `OrbitFM`, `ord_smul_eqFM`.
- **Used by**: `ordOrbit_mkFM`, `NonEllOrbitFM` (indirectly via downstream), `finite_support_ordOrbitFM`, `finite_support_ordOrbit_nonEllFM`.
- **Visibility**: public
- **Lines**: 82–87

### `@[simp] theorem ordOrbit_mkFM`
- **Type**: `(p : ℍ) : ordOrbitFM f (orbFM p) = orderOfVanishingAt' (⇑f) p`
- **What**: Computing `ordOrbitFM` on a representative.
- **How**: `rfl` (definitional unfolding).
- **Hypotheses**: none.
- **Uses from project**: `ordOrbitFM`, `orbFM`.
- **Used by**: `finite_support_ordOrbitFM`.
- **Visibility**: public, `@[simp]`
- **Lines**: 89–90

### `def oiFM`
- **Type**: `oiFM : OrbitFM := orbFM ellipticPointI'`
- **What**: The orbit of the elliptic point `i`.
- **How**: Apply `orbFM` to `ellipticPointI'`.
- **Hypotheses**: none.
- **Uses from project**: `OrbitFM`, `orbFM`, `ellipticPointI'`.
- **Used by**: `NonEllOrbitFM`.
- **Visibility**: public
- **Lines**: 93

### `def orhoFM`
- **Type**: `orhoFM : OrbitFM := orbFM ellipticPointRho'`
- **What**: The orbit of the elliptic point `ρ`.
- **How**: Apply `orbFM` to `ellipticPointRho'`.
- **Hypotheses**: none.
- **Uses from project**: `OrbitFM`, `orbFM`, `ellipticPointRho'`.
- **Used by**: `NonEllOrbitFM`, `orb_rho_plus_one_eq_orb_rhoFM`.
- **Visibility**: public
- **Lines**: 96

### `def NonEllOrbitFM`
- **Type**: `NonEllOrbitFM := {q : OrbitFM // q ≠ oiFM ∧ q ≠ orhoFM}`
- **What**: A non-elliptic orbit is one distinct from both `oiFM` and `orhoFM`.
- **How**: Subtype of `OrbitFM`.
- **Hypotheses**: none.
- **Uses from project**: `OrbitFM`, `oiFM`, `orhoFM`.
- **Used by**: `finite_support_ordOrbit_nonEllFM`.
- **Visibility**: public
- **Lines**: 99

### `theorem orbit_has_fd_repFM`
- **Type**: `(q : OrbitFM) : ∃ p : ℍ, orbFM p = q ∧ p ∈ 𝒟`
- **What**: Every orbit has a representative in the fundamental domain `𝒟`.
- **How**: `Quotient.inductionOn'`; lift to a representative `z`; `ModularGroup.exists_smul_mem_fd` provides `g` with `g • z ∈ 𝒟`; conclude via `Quotient.sound'`.
- **Hypotheses**: none beyond `q : OrbitFM`.
- **Uses from project**: `OrbitFM`, `orbFM`, `ModularGroup.exists_smul_mem_fd`, `𝒟`.
- **Used by**: `finite_support_ordOrbitFM` (via `choose`).
- **Visibility**: public
- **Lines**: 104–109

### `private theorem G_analyticAtFM`
- **Type**: `(p : ℍ) : AnalyticAt ℂ (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ)`
- **What**: The complex extension of `f` (by 0 on lower-half plane) is analytic at every ℍ-point.
- **How**: `UpperHalfPlane.mdifferentiable_iff.mp f.holo'` gives `DifferentiableOn` on the upper-half-plane set; `analyticAt_iff_eventually_differentiableAt` + `congr_of_eventuallyEq` (eventually equals `f ∘ ofComplex`).
- **Hypotheses**: none beyond `f` and `p`.
- **Uses from project**: `UpperHalfPlane.mdifferentiable_iff`, `UpperHalfPlane.isOpen_upperHalfPlaneSet`, `UpperHalfPlane.ofComplex_apply_of_im_pos`.
- **Used by**: `G_eval_eq_fFM`, `orderOfVanishingAt'_eq_zero_of_ne_zero'`, `eq_zero_of_orderOfVanishingAt'_ne_zero'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`.
- **Visibility**: private
- **Lines**: 113–124
- **Notes**: >10 lines.

### `private theorem G_eval_eq_fFM`
- **Type**: `(p : ℍ) : (fun w : ℂ => if h : 0 < w.im then f ⟨w, h⟩ else 0) (p : ℂ) = f p`
- **What**: The extension evaluates to `f p` at any `p : ℍ`.
- **How**: `beta_reduce`; split on `dif_pos` (positive imaginary part holds by `p.im_pos`); `congr` handles the upper-half-plane case.
- **Hypotheses**: none.
- **Uses from project**: [].
- **Used by**: `orderOfVanishingAt'_eq_zero_of_ne_zero'`, `orderOfVanishingAt'_ne_zero_of_eq_zeroFM`.
- **Visibility**: private
- **Lines**: 126–131

### `theorem orderOfVanishingAt'_eq_zero_of_ne_zero'`
- **Type**: `(p : ℍ) (hp : f p ≠ 0) : orderOfVanishingAt' f p = 0`
- **What**: If `f p ≠ 0` then the order of vanishing at p is zero.
- **How**: Unfold `orderOfVanishingAt'`; use `MeromorphicNFAt.meromorphicOrderAt_eq_zero_iff` applied to the analytic extension via `G_analyticAtFM`; rewrite by `G_eval_eq_fFM`.
- **Hypotheses**: `f p ≠ 0`.
- **Uses from project**: `orderOfVanishingAt'`, `G_analyticAtFM`, `G_eval_eq_fFM`.
- **Used by**: `eq_zero_of_orderOfVanishingAt'_ne_zero'`.
- **Visibility**: public
- **Lines**: 136–144

### `theorem eq_zero_of_orderOfVanishingAt'_ne_zero'`
- **Type**: `(p : ℍ) (hp : orderOfVanishingAt' (⇑f) p ≠ 0) : f p = 0`
- **What**: Contrapositive: if the order of vanishing is nonzero, then `f p = 0`.
- **How**: `by_contra` then apply `orderOfVanishingAt'_eq_zero_of_ne_zero'`.
- **Hypotheses**: `orderOfVanishingAt' f p ≠ 0`.
- **Uses from project**: `orderOfVanishingAt'_eq_zero_of_ne_zero'`.
- **Used by**: `finite_zeros_in_fdFM`.
- **Visibility**: public
- **Lines**: 147–150

### `theorem orderOfVanishingAt'_ne_zero_of_eq_zeroFM`
- **Type**: `(hf : f ≠ 0) (p : ℍ) (hp : f p = 0) : orderOfVanishingAt' (⇑f) p ≠ 0`
- **What**: For a nonzero modular form, a zero of `f` has nonzero order of vanishing.
- **How**: Unfold `orderOfVanishingAt'`; show that `untop₀ = 0` would force `meromorphicOrderAt G p = ⊤`, hence (via `meromorphicOrderAt_eq_top_iff` + `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero` over the connected upper-half-plane) `f` identically zero, contradicting `hf`. Uses `WithTop.untop₀_eq_zero.mp` and `convex_halfSpace_im_gt 0`.
- **Hypotheses**: `f ≠ 0`, `f p = 0`.
- **Uses from project**: `orderOfVanishingAt'`, `G_analyticAtFM`, `G_eval_eq_fFM`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 153–180
- **Notes**: >25 lines.

### `private theorem modularFormCompOfComplexFM_eq'`
- **Type**: `(p : ℍ) : modularFormCompOfComplex f (p : ℂ) = f p`
- **What**: The complex-domain composition of `f` evaluates to `f p` at `(p : ℂ)`.
- **How**: Unfold `modularFormCompOfComplex`; congr; `UpperHalfPlane.ofComplex_apply_of_im_pos p.im_pos`.
- **Hypotheses**: none.
- **Uses from project**: `modularFormCompOfComplex`, `UpperHalfPlane.ofComplex_apply_of_im_pos`.
- **Used by**: `finite_zeros_in_fdFM`.
- **Visibility**: private
- **Lines**: 184–188

### `theorem fd_im_gt_halfFM`
- **Type**: `(p : ℍ) (hp : p ∈ 𝒟) : (1:ℝ)/2 < (p : ℂ).im`
- **What**: Every point of the fundamental domain has imaginary part > 1/2.
- **How**: By contradiction: from `normSq_apply` get `re² + im² ≥ 1`; from `|re| ≤ 1/2` get `re² ≤ 1/4`; combined with `im ≤ 1/2` get `im² ≤ 1/4`, contradicting the lower bound. `linarith`/`nlinarith` orchestration.
- **Hypotheses**: `p ∈ 𝒟`.
- **Uses from project**: `𝒟`.
- **Used by**: `finite_zeros_in_fdFM`.
- **Visibility**: public
- **Lines**: 190–204
- **Notes**: >10 lines.

### `private theorem no_zeros_above_height'`
- **Type**: `(hf : f ≠ 0) : ∃ H₀ : ℝ, Real.sqrt 3 / 2 < H₀ ∧ ∀ (p : ℍ), H₀ ≤ (p : ℂ).im → f p ≠ 0`
- **What**: For a nonzero modular form, there is a height `H₀ > √3/2` above which `f` has no zeros.
- **How**: From `exists_height_cusp_nonvanishing` get `H₀` and nonvanishing of the q-expansion on a closed disk; use `SlashInvariantFormClass.eq_cuspFunction` (with `ModularFormClass.one_mem_strictPeriods_SL2Z`) to identify `f p` with the q-expansion evaluated at `qParam`; `Periodic.norm_qParam` and `Real.exp_le_exp` bound `qParam ∈ closedBall`; nonvanishing of `qParam` via `exp_ne_zero`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `exists_height_cusp_nonvanishing`, `SlashInvariantFormClass.eq_cuspFunction`, `ModularFormClass.one_mem_strictPeriods_SL2Z`.
- **Used by**: `finite_zeros_in_fdFM`.
- **Visibility**: private
- **Lines**: 206–221
- **Notes**: >10 lines.

### `theorem finite_zeros_in_fdFM`
- **Type**: `(hf : f ≠ 0) : Set.Finite {p : ℍ | p ∈ 𝒟 ∧ orderOfVanishingAt' (⇑f) p ≠ 0}`
- **What**: The set of zeros (with nonzero order) of `f` in the fundamental domain is finite.
- **How**: Reduce to `{p ∈ 𝒟 | f p = 0}` via `eq_zero_of_orderOfVanishingAt'_ne_zero'`; pick height `H₀` via `no_zeros_above_height'`; show this set is the preimage (under `UpperHalfPlane.coe`) of `{z ∈ fdBox (H₀+1) | modularFormCompOfComplex f z = 0}`, which is finite via `modularForm_finitely_many_zeros_in_fdBox`. Bridges via `fd_im_gt_halfFM`, `modularFormCompOfComplexFM_eq'`, `fdBox`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `𝒟`, `eq_zero_of_orderOfVanishingAt'_ne_zero'`, `no_zeros_above_height'`, `modularForm_finitely_many_zeros_in_fdBox`, `fdBox`, `modularFormCompOfComplex`, `modularFormCompOfComplexFM_eq'`, `fd_im_gt_halfFM`.
- **Used by**: `finite_support_ordOrbitFM`, `s₀FM`.
- **Visibility**: public
- **Lines**: 224–250
- **Notes**: >25 lines.

### `theorem finite_support_ordOrbitFM`
- **Type**: `(hf : f ≠ 0) : Set.Finite {q : OrbitFM | ordOrbitFM f q ≠ 0}`
- **What**: Finitely many orbits have nonzero `ordOrbitFM`.
- **How**: `choose` a representative for each orbit using `orbit_has_fd_repFM`; the image of the orbit-support under `rep` is a subset of the (finite) zero set in `𝒟` via `finite_zeros_in_fdFM`; `rep` is injective on the support by orbit-equality; conclude via `Set.Finite.subset` + `Set.Finite.of_finite_image`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `OrbitFM`, `ordOrbitFM`, `orbFM`, `ordOrbit_mkFM`, `orbit_has_fd_repFM`, `finite_zeros_in_fdFM`.
- **Used by**: `finite_support_ordOrbit_nonEllFM`.
- **Visibility**: public
- **Lines**: 255–270
- **Notes**: >10 lines.

### `theorem finite_support_ordOrbit_nonEllFM`
- **Type**: `(hf : f ≠ 0) : Set.Finite {q : NonEllOrbitFM | ordOrbitFM f q.val ≠ 0}`
- **What**: Finitely many non-elliptic orbits have nonzero `ordOrbitFM`.
- **How**: Preimage of the finite full support under `Subtype.val`, which is injective; `Set.Finite.preimage`.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `NonEllOrbitFM`, `ordOrbitFM`, `finite_support_ordOrbitFM`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 273–280

### `noncomputable def s₀FM`
- **Type**: `(hf : f ≠ 0) : Finset ℍ := (finite_zeros_in_fdFM f hf).toFinset`
- **What**: The canonical finite set of zeros (with nonzero order) of `f` in `𝒟`.
- **How**: `Set.Finite.toFinset` of the finite-zeros set.
- **Hypotheses**: `f ≠ 0`.
- **Uses from project**: `finite_zeros_in_fdFM`.
- **Used by**: `s₀FM_mem_fd`, `s₀FM_complete`.
- **Visibility**: public
- **Lines**: 285

### `theorem s₀FM_mem_fd`
- **Type**: `(hf : f ≠ 0) : ∀ p ∈ s₀FM f hf, p ∈ 𝒟`
- **What**: Every point of `s₀FM` lies in `𝒟`.
- **How**: Unfold `s₀FM`; `Set.Finite.mem_toFinset`; take the left conjunct.
- **Hypotheses**: `f ≠ 0`, `p ∈ s₀FM`.
- **Uses from project**: `s₀FM`, `𝒟`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 288–291

### `theorem s₀FM_complete`
- **Type**: `(hf : f ≠ 0) : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ s₀FM f hf`
- **What**: `s₀FM` captures every point of `𝒟` with nonzero order.
- **How**: Unfold `s₀FM`; `Set.Finite.mem_toFinset`; pack the two assumptions.
- **Hypotheses**: `f ≠ 0`, `p ∈ 𝒟`, `orderOfVanishingAt' f p ≠ 0`.
- **Uses from project**: `s₀FM`, `𝒟`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 294–298

### `theorem orb_rho_plus_one_eq_orb_rhoFM`
- **Type**: `orbFM ellipticPointRhoPlusOne' = (orhoFM : OrbitFM)`
- **What**: The orbit of `ρ+1` equals the orbit of `ρ` (T-equivalence).
- **How**: Change to `Quotient.mk''` equality, then `Quotient.eq''`; reduce to `MulAction.orbitRel_apply`/`mem_orbit_iff`; exhibit `T ∈ SL(2,ℤ)` with `T • ρ = ρ+1` via `UpperHalfPlane.modular_T_smul` and `push_cast; ring` on the coordinates.
- **Hypotheses**: none.
- **Uses from project**: `orbFM`, `orhoFM`, `OrbitFM`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`.
- **Used by**: unused in file.
- **Visibility**: public
- **Lines**: 303–313

---

## File Summary

- **Declarations**: 18 named declarations: 1 abbrev (`OrbitFM`), 3 defs (`orbFM`, `oiFM`, `orhoFM`), 1 def (`NonEllOrbitFM`), 1 `ordOrbitFM`, 1 `s₀FM`, 11 theorems (3 private), 1 simp lemma. No axioms, no sorries.
- **Theme**: Lifts the order-of-vanishing function from ℍ to the SL(2,ℤ)-orbit quotient `OrbitFM`, defines special orbits (`oiFM`, `orhoFM`, `NonEllOrbitFM`), and proves finiteness of zeros in the fundamental domain `𝒟` and finite support of the orbit-level order function. Closes with the T-equivalence `orb(ρ+1) = orb(ρ)`.
- **Internal call graph**: `ord_smul_eqFM` makes `ordOrbitFM` well-defined; `orbit_has_fd_repFM` plus `finite_zeros_in_fdFM` drive `finite_support_ordOrbitFM`. The finiteness of zeros is a transfer along `modularFormCompOfComplex` from the complex-disk finite-zeros result `modularForm_finitely_many_zeros_in_fdBox`. Helpers `G_analyticAtFM`/`G_eval_eq_fFM` are private bridges between `f : ModularForm` and its complex extension; they underpin the order-characterisation lemmas.
- **Imports**: `LeanModularForms.ForMathlib.ModularInvariance` (provides `ord_S_eq`, `ord_add_one_eq`, `modularFormCompOfComplex`, `fdBox`, `modularForm_finitely_many_zeros_in_fdBox`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `𝒟`, `exists_height_cusp_nonvanishing`); plus Mathlib analytic/normal-form and `ModularForms.LevelOne`.
- **Notes**: No `set_option`, no `sorry`, no `axiom`, no `TODO`. The file uses `Subgroup.closure_induction`, `Quotient.inductionOn'`, `MulAction.orbitRel`, and the modular `T`/`S` generators.
