# ValenceFormulaBridged.lean Inventory

**Path**: /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormulaBridged.lean
**Lines**: 170
**Imports**: `LeanModularForms.ForMathlib.FDWindingDataFullSeg1Seg4`, `LeanModularForms.ForMathlib.ResidueSideBridge`

## Entries

### private noncomputable def `F_int_FM`
- **Type**: def (private noncomputable)
- **What**: Integrand combining residue and modular sides; for `1 < H`, returns `∫_0^1 cpvIntegrandOn (sArcOfS S ∪ sVertOfS S) (logDeriv (modularFormCompOfComplex f)) γ.extend ε t` with `γ = (fdWindingDataFull_unconditional hH).boundary`; otherwise 0.
- **How**: Definitional `if hH : 1 < H then ... else 0` over the boundary path of `fdWindingDataFull_unconditional hH`.
- **Hypotheses**: `S : Finset UpperHalfPlane`, `H ε : ℝ`; `f` and `k` from outer variables.
- **Uses-from-project**: `cpvIntegrandOn`, `sArcOfS`, `sVertOfS`, `modularFormCompOfComplex`, `fdWindingDataFull_unconditional`, `FDWindingDataFull.boundary`.
- **Used by**: `valence_formula_textbook_unconditional_FM` (passed to `valence_formula_unconditional_mkD`).
- **Visibility**: private
- **Lines**: 39–45
- **Notes**: Internal common integrand that lets both bridges quantify over the same epsilon-family.

### private lemma `gwnPrime_eq_gwn_of_mem_fd`
- **Type**: lemma (private)
- **What**: For `s ∈ 𝒟` below height `H`, `generalizedWindingNumber' (fdBoundary_H H) 0 5 s = generalizedWindingNumber γ s` where `γ` is the boundary path of `fdWindingDataFull_unconditional hH`.
- **How**: Sets `D, γ`; gets `hγ : ∀ t ∈ Icc 0 1, γ.extend t = fdBoundaryFun H t` via `D.boundary_eq`. Reduces to producing `∃ w, HasGeneralizedWindingNumber γ s w` via `generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber γ hγ h_gwn` and `.eq.symm`. Five `by_cases` arms: `s = I` → `D.winding_at_i`; `s = ρ` → `D.winding_at_rho`; `s = ρ+1` → `D.winding_at_rho_plus_one`; strict interior (`‖s‖>1 ∧ |re|<1/2`) → `D.toFDWindingData.interior_winding`; else → `D.boundary_winding`.
- **Hypotheses**: `hH : 1 < H`, `hs_fd : s ∈ 𝒟`, `hs_im_lt : (s : ℂ).im < H`.
- **Uses-from-project**: `fdWindingDataFull_unconditional`, `FDWindingDataFull.boundary*` (`boundary_eq`, `winding_at_i`, `winding_at_rho`, `winding_at_rho_plus_one`, `boundary_winding`), `FDWindingData.interior_winding`, `ellipticPointRho`, `ellipticPointRhoPlusOne`, `generalizedWindingNumberPrime_eq_of_hasGeneralizedWindingNumber`, `fdBoundary_H`, `fdBoundaryFun`.
- **Used by**: `valence_formula_textbook_unconditional_FM`.
- **Visibility**: private
- **Lines**: 50–71
- **Notes**: Bridge from old-chain `gWN'` to new-chain `gWN` via 5-way case split on the fundamental-domain stratification.

### theorem `valence_formula_textbook_unconditional_FM`
- **Type**: theorem
- **What**: Final unconditional valence formula stating `ord_∞(f) + (1/2)·ord_i + (1/3)·ord_ρ + Σ ord (over strict interior, left vert, and lower arc strata) = k/12` for the input `Finset S` of fundamental-domain points containing all zeros below height `H_S`.
- **How**: Obtain `(H₀_res, h_res_bridge)` from `cpv_residue_side_HasCauchyPVOn` and `(H₀_mod, h_mod_bridge)` from `cpv_modular_side_HasCauchyPVOn`. Set `M := max(max(max H₀_res H₀_mod) H_S) 1` and `H_res := M + 1`; obtain bounds `hH_res_gt, hH₀_res_le, hH₀_mod_le, hH_S_le` via `simp` and `linarith`. Apply `valence_formula_unconditional_mkD f S hS hS_complete H_S hH_S (F_int_FM f S) H_res hH_res_gt`. Residue side: for each `H ≥ H_res`, set `γ := boundary`, sum-bridge via `gwnPrime_eq_gwn_of_mem_fd` and `Finset.sum_congr`, then `(h_res_bridge ...).congr'` with `filter_upwards`. Modular side: analogous using `h_mod_bridge`.
- **Hypotheses**: `hf : f ≠ 0` (via `include`); `S : Finset UpperHalfPlane`, `hS : ∀ p ∈ S, p ∈ 𝒟`, `hS_complete : ∀ p, p ∈ 𝒟 → orderOfVanishingAt' (⇑f) p ≠ 0 → p ∈ S`, `H_S : ℝ`, `hH_S : ∀ s ∈ S, (s : ℂ).im < H_S`.
- **Uses-from-project**: `cpv_residue_side_HasCauchyPVOn`, `cpv_modular_side_HasCauchyPVOn`, `valence_formula_unconditional_mkD`, `fdWindingDataFull_unconditional`, `FDWindingDataFull.boundary_eq`, `gwnPrime_eq_gwn_of_mem_fd`, `F_int_FM`, `sLeftVertFM`, `orderAtCusp'`, `orderOfVanishingAt'`, `ellipticPointI'`, `ellipticPointRho'`, `ellipticPointRhoPlusOne'`, `fdBoundaryFun`.
- **Used by**: `valence_formula_textbook_orbit_finsum_FM`.
- **Visibility**: public
- **Lines**: 77–140 (with `include hf in`)
- **Notes**: ForMathlib-native chain assembly; ~63-line proof orchestrates residue/modular bridges, the height-choosing trick, and the gWN'→gWN reparametrization sum.

### theorem `valence_formula_textbook_orbit_finsum_FM`
- **Type**: theorem
- **What**: The Valence Formula in textbook finsum-over-orbits form: `ord_∞ + (1/2)·ord_i + (1/3)·ord_ρ + Σᶠ over non-elliptic SL₂(ℤ)-orbits = k/12`.
- **How**: `refine valence_formula_textbook_orbit_finsum f hf fun S hS hS_complete => ?_`; choose height bound `H_S := S.sum (fun s => (s : ℂ).im) + 1`; prove `hH_S` per `s ∈ S` using `Finset.single_le_sum` plus `linarith`; conclude via `valence_formula_textbook_unconditional_FM`.
- **Hypotheses**: `hf : f ≠ 0` (via `include`).
- **Uses-from-project**: `valence_formula_textbook_orbit_finsum`, `valence_formula_textbook_unconditional_FM`, `NonEllOrbitFM`, `ordOrbitQ`, `orderAtCusp'`, `ellipticPointI'`, `ellipticPointRho'`.
- **Used by**: Top-level statement; final public theorem of the chain.
- **Visibility**: public
- **Lines**: 154–168 (with `include hf in`)
- **Notes**: Top-level final form of the valence formula; the Finset-sum height bound trick (`s.im ≤ S.sum im` for `s ∈ S`) is the only nontrivial step.

## File Summary

Two public theorems and two private helpers that complete the ForMathlib-native valence formula chain. `F_int_FM` packages the common integrand. `gwnPrime_eq_gwn_of_mem_fd` bridges old-chain `generalizedWindingNumber'` to new-chain `generalizedWindingNumber` via a 5-way fundamental-domain case split. `valence_formula_textbook_unconditional_FM` is the headline: combining the residue-side and modular-side bridges from `ResidueSideBridge` with the master assembly `valence_formula_unconditional_mkD`, requiring only `hf : f ≠ 0`. `valence_formula_textbook_orbit_finsum_FM` packages the result in finsum-over-orbits form. Together these are the fully unconditional ForMathlib endpoints of the valence-formula development.
