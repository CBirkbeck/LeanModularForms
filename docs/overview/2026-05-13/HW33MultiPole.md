# HW33MultiPole.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HW33MultiPole.lean`

---

### theorem `LeanModularForms.hasCauchyPVOn_extend_of_avoid`
- Type: `(S T : Finset ℂ) (hST : S ⊆ T) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x) {L : ℂ} {δ : ℝ} (hδ_pos : 0 < δ) (h_avoid : ∀ s ∈ T \ S, ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s‖) (h_S : HasCauchyPVOn S f γ L) → HasCauchyPVOn T f γ L`
- What: Pole-set extension under avoidance margin — if γ stays ≥ δ from `T \ S`, then `HasCauchyPVOn` for `S` and `T` coincide.
- How: Applies `h_S.congr'` and shows `cpvIntegrandOn S _ ε = cpvIntegrandOn T _ ε` eventually for `ε ∈ Ioo 0 δ`; via `intervalIntegral.integral_congr` rewrites `uIcc_of_le`; `simp only [cpvIntegrandOn]`; matches existential characterisation via `propext` of the cutoff condition (forward via `hST`, backward by case-splitting on `s ∈ S`, contradicting with `h_avoid` and `PiecewiseC1Path.extendedPath_eq` via `linarith [hε.2]`).
- Hypotheses: subset inclusion `S ⊆ T`; positive separation margin between γ and `T \ S`.
- Uses-from-project: `HasCauchyPVOn`, `HasCauchyPVOn.congr'`, `cpvIntegrandOn`, `PiecewiseC1Path.extendedPath_eq`.
- Used by: `hasCauchyPVOn_multipole_pow_inv_of_singleton`.
- Visibility: public.
- Lines: 44-67.

### theorem `LeanModularForms.hasCauchyPVOn_multipole_pow_inv_of_singleton`
- Type: `(S : Finset ℂ) {s : ℂ} (hs : s ∈ S) {k : ℕ} (γ) {δ} (hδ_pos) (h_avoid : ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s'‖) (h_singleton : HasCauchyPVOn {s} (fun z => 1/(z-s)^k) γ 0) → HasCauchyPVOn S (fun z => 1/(z-s)^k) γ 0`
- What: Multi-pole extension for a single `1/(z-s)^k` term — promotes singleton CPV cancellation to full set `S`.
- How: Applies `hasCauchyPVOn_extend_of_avoid` with `{s}` and `S`, using `Finset.singleton_subset_iff.mpr hs`; rewrites `s' ∈ S \ {s}` via `Finset.mem_sdiff, Finset.mem_singleton` and discharges via `h_avoid`.
- Hypotheses: `s ∈ S`; γ avoids `S \ {s}` with margin `δ`; singleton CPV result.
- Uses-from-project: `hasCauchyPVOn_extend_of_avoid`, `HasCauchyPVOn`.
- Used by: `hasCauchyPVOn_multipole_sum_pow_inv`.
- Visibility: public.
- Lines: 77-88.

### theorem `LeanModularForms.hasCauchyPVOn_multipole_sum_pow_inv`
- Type: `(S : Finset ℂ) {k : ℕ} (c : ℂ → ℂ) (γ) {δ} (hδ_pos) (h_avoid : ∀ s ∈ S, ∀ s' ∈ S, s' ≠ s → ∀ t ∈ Icc 0 1, δ ≤ ‖γ t - s'‖) (h_singletons) (_h_int_sum) (h_int_each) → HasCauchyPVOn S (fun z => ∑ s ∈ S, c s / (z-s)^k) γ 0`
- What: Multi-pole assembly — sum of singleton transverse cancellations yields the multi-pole sum CPV cancellation.
- How: Builds `h_each_scaled : ∀ s ∈ S, HasCauchyPVOn S (fun z => c s/(z-s)^k) γ 0` by applying `.smul (c s)` to `hasCauchyPVOn_multipole_pow_inv_of_singleton`, rewriting `c s · (1/(z-s)^k) = c s/(z-s)^k` via `funext` + `ring` and `mul_zero`; closes with `HasCauchyPVOn.finset_sum S h_each_scaled h_int_each` and a final `simpa only [Finset.sum_const_zero]` to convert `∑ s ∈ S, 0 = 0`.
- Hypotheses: pairwise margin avoidance; per-pole singleton CPV; per-pole and total integrand integrability.
- Uses-from-project: `hasCauchyPVOn_multipole_pow_inv_of_singleton`, `HasCauchyPVOn.smul`, `HasCauchyPVOn.finset_sum`.
- Used by: `hasCauchyPVOn_multipole_transverse_assembled`, `hasCauchyPVOn_multipole_pow_of_conditionB_assembled`.
- Visibility: public.
- Lines: 94-121.

### theorem `LeanModularForms.hasCauchyPVOn_multipole_transverse_assembled`
- Type: `(S : Finset ℂ) {k : ℕ} (c : ℂ → ℂ) (γ) {δ} (hδ_pos) (h_avoid_pairs) (h_singletons) (h_int_each) (h_int_sum) → HasCauchyPVOn S (fun z => ∑ s ∈ S, c s/(z-s)^k) γ 0`
- What: High-level multi-pole transverse closure of HW Theorem 3.3 in `HasCauchyPVOn` form.
- How: Direct delegation to `hasCauchyPVOn_multipole_sum_pow_inv` with reordered arguments `h_avoid_pairs h_singletons h_int_each h_int_sum`.
- Hypotheses: same as `hasCauchyPVOn_multipole_sum_pow_inv` (positive margin between pairs, per-pole singleton CPV, integrability of cutout integrands per-pole and overall).
- Uses-from-project: `hasCauchyPVOn_multipole_sum_pow_inv`.
- Used by: `hasCauchyPVOn_multipole_pow_of_conditionB_assembled`.
- Visibility: public.
- Lines: 138-154.

### theorem `LeanModularForms.hasCauchyPVOn_multipole_pow_of_conditionB_assembled`
- Type: identical to `hasCauchyPVOn_multipole_transverse_assembled` (discoverability alias).
- What: Multi-pole condition-(B) closure of HW Theorem 3.3.
- How: Direct delegation to `hasCauchyPVOn_multipole_transverse_assembled`.
- Hypotheses: identical to the transverse version.
- Uses-from-project: `hasCauchyPVOn_multipole_transverse_assembled`.
- Used by: external (downstream condition-(B) consumers).
- Visibility: public.
- Lines: 163-179.

---

## File Summary
- Total declarations: 5 theorems.
- Key API: `hasCauchyPVOn_extend_of_avoid` (the key technical lemma); `hasCauchyPVOn_multipole_sum_pow_inv` (assembly); the two top-level "assembled" forms (transverse + condition-(B) discoverability alias).
- Unused declarations within file: none — all theorems are public, and the latter two are entry-points for external consumers (HW 3.3 multi-pole closure callers).
- Sorries: none.
- `set_option`: none.
- Long proofs (>10 lines): `hasCauchyPVOn_extend_of_avoid` (~24 lines): uses `Filter.eventuallyEq_iff_exists_mem` with `Ioo 0 δ ∈ 𝓝[>] 0`, `intervalIntegral.integral_congr`, and an explicit `propext` to identify the cutoff existential; `hasCauchyPVOn_multipole_sum_pow_inv` (~28 lines): builds `h_each_scaled` via `.smul (c s)` then assembles with `HasCauchyPVOn.finset_sum`.
- Purpose: Extends the single-pole transverse closure (HW 3.3 from `HW33Final.hasCauchyPVOn_singleton_pow_of_transverse_assembled`) to the multi-pole case. The key step is `hasCauchyPVOn_extend_of_avoid` — when the curve stays ≥ δ from poles not in the active subset, the cutoff integrands agree pointwise — enabling extension from `{s}` to `S`, then summing via `HasCauchyPVOn.finset_sum`. Provides two end-user "assembled" theorems (transverse-only and condition-(B) discoverability alias) that compose the singleton input shape into the full multi-pole sum cancellation result.
