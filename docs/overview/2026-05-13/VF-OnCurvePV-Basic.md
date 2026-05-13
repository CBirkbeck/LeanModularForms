# ValenceFormula/OnCurvePV/Basic.lean Inventory

Path: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/ValenceFormula/OnCurvePV/Basic.lean`

---

### theorem `cpv_exists_at_rho`
- Type: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) → CauchyPrincipalValueExists' (fun z => (z - ellipticPointRho)⁻¹) (fdBoundary_H H) 0 5 ellipticPointRho`
- What: CPV of `(z - ρ)⁻¹` exists along the height-`H` FD boundary on `[0,5]`.
- How: Direct application of `cpv_exists_from_shifted_tendsto` with the project's `pv_integral_at_rho_tendsto H hH`.
- Hypotheses: `H > √3/2`.
- Uses-from-project: `CauchyPrincipalValueExists'`, `fdBoundary_H`, `ellipticPointRho`, `cpv_exists_from_shifted_tendsto`, `pv_integral_at_rho_tendsto`.
- Used by: downstream WindingWeights/Rho assembly.
- Visibility: public.
- Lines: 28-31.

### theorem `cpv_exists_at_rho_plus_one`
- Type: `(H : ℝ) (hH : Real.sqrt 3 / 2 < H) → CauchyPrincipalValueExists' (fun z => (z - ellipticPointRhoPlusOne)⁻¹) (fdBoundary_H H) 0 5 ellipticPointRhoPlusOne`
- What: CPV of `(z - ρ')⁻¹` exists along height-`H` FD boundary.
- How: Direct application of `cpv_exists_from_shifted_tendsto` with `pv_integral_at_rho_plus_one_tendsto`.
- Hypotheses: `H > √3/2`.
- Uses-from-project: `cpv_exists_from_shifted_tendsto`, `pv_integral_at_rho_plus_one_tendsto`, `ellipticPointRhoPlusOne`, `fdBoundary_H`.
- Used by: WindingWeights/RhoPlusOne consumers.
- Visibility: public.
- Lines: 34-38.

### theorem `cpv_exists_at_i`
- Type: `(H : ℝ) (hH : 1 < H) → CauchyPrincipalValueExists' (fun z => (z - I)⁻¹) (fdBoundary_H H) 0 5 I`
- What: CPV of `(z - I)⁻¹` exists along height-`H` FD boundary for `H > 1`.
- How: Direct application of `cpv_exists_from_shifted_tendsto` with `pv_integral_at_i_tendsto`.
- Hypotheses: `H > 1`.
- Uses-from-project: `cpv_exists_from_shifted_tendsto`, `pv_integral_at_i_tendsto`, `fdBoundary_H`.
- Used by: WindingWeights/I.
- Visibility: public.
- Lines: 41-43.

### lemma `fdBoundary_H_seg1_re'`
- Type: `(H : ℝ) {t : ℝ} (_ht0 : 0 ≤ t) (ht1 : t ≤ 1) → (fdBoundary_H H t).re = 1/2`
- What: On segment 1 (the right vertical edge), the curve has real part `1/2`.
- How: Rewrites by `fdBoundary_H_eq_seg1_H`, then `simp` with the segment formula and `Complex.add_re/mul_re/ofReal_re/I_re/I_im`.
- Hypotheses: `t ∈ [0,1]`.
- Uses-from-project: `fdBoundary_H`, `fdBoundary_H_eq_seg1_H`, `fdBoundary_seg1_H`.
- Used by: smooth boundary classifications (downstream).
- Visibility: public.
- Lines: 45-49.

### lemma `fdBoundary_H_seg4_re'`
- Type: `(H : ℝ) {t : ℝ} (ht3 : 3 < t) (ht4 : t ≤ 4) → (fdBoundary_H H t).re = -1/2`
- What: On segment 4 (left vertical edge), real part is `-1/2`.
- How: `rw [fdBoundary_H_eq_seg4_H]; simp [fdBoundary_seg4_H, ...]`.
- Hypotheses: `t ∈ (3,4]`.
- Uses-from-project: `fdBoundary_H_eq_seg4_H`, `fdBoundary_seg4_H`.
- Used by: smooth boundary classifications.
- Visibility: public.
- Lines: 51-55.

### lemma `fdBoundary_H_seg5_re'`
- Type: `(H : ℝ) {t : ℝ} (ht4 : 4 < t) (_ht5 : t ≤ 5) → (fdBoundary_H H t).re = t - 9/2`
- What: On segment 5 (top horizontal), real part is `t - 9/2`.
- How: `rw [fdBoundary_H_eq_seg5_H]; simp [...]`.
- Hypotheses: `t ∈ (4,5]`.
- Uses-from-project: `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`.
- Used by: smooth boundary characterisations.
- Visibility: public.
- Lines: 57-61.

### lemma `fdBoundary_H_seg5_im'`
- Type: `(H : ℝ) {t : ℝ} (ht4 : 4 < t) (_ht5 : t ≤ 5) → (fdBoundary_H H t).im = H`
- What: On segment 5, imaginary part is `H`.
- How: `rw [fdBoundary_H_eq_seg5_H]; simp [...]`.
- Hypotheses: `t ∈ (4,5]`.
- Uses-from-project: `fdBoundary_H_eq_seg5_H`, `fdBoundary_seg5_H`.
- Used by: cusp / boundary downstream.
- Visibility: public.
- Lines: 63-67.

### lemma `fdBoundary_H_arc_re'`
- Type: `(H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) → (fdBoundary_H H t).re = Real.cos (Real.pi*(1+t)/6)`
- What: On the bottom arc, real part is `cos(π(1+t)/6)`.
- How: `rw [fdBoundary_H_eq_arc, Complex.exp_ofReal_mul_I_re]`.
- Hypotheses: `t ∈ (1,3)`.
- Uses-from-project: `fdBoundary_H_eq_arc`.
- Used by: arc analysis.
- Visibility: public.
- Lines: 69-71.

### lemma `fdBoundary_H_arc_im'`
- Type: `(H : ℝ) {t : ℝ} (ht1 : 1 < t) (ht3 : t < 3) → (fdBoundary_H H t).im = Real.sin (Real.pi*(1+t)/6)`
- What: On the bottom arc, imaginary part is `sin(π(1+t)/6)`.
- How: `rw [fdBoundary_H_eq_arc, Complex.exp_ofReal_mul_I_im]`.
- Hypotheses: `t ∈ (1,3)`.
- Uses-from-project: `fdBoundary_H_eq_arc`.
- Used by: arc analysis.
- Visibility: public.
- Lines: 73-75.

### lemma `cpv_exists_on_smooth_subinterval`
- Type: `(H : ℝ) (_hH : Real.sqrt 3 / 2 < H) {t₀ a' b' : ℝ} (s : ℂ) (hat₀ : t₀ ∈ Ioo a' b') (hs : fdBoundary_H H t₀ = s) (hγ_C2 : ContDiffAt ℝ 2 (fdBoundary_H H) t₀) (hL_ne : deriv (fdBoundary_H H) t₀ ≠ 0) (hγ_cont_deriv : ContinuousOn (deriv (fdBoundary_H H)) (Icc a' b')) (h_inj : ∀ t ∈ Icc a' b', fdBoundary_H H t = fdBoundary_H H t₀ → t = t₀) → CauchyPrincipalValueExists' (fun z => (z-s)⁻¹) (fdBoundary_H H) a' b' s`
- What: CPV exists on a smooth sub-interval where the curve crosses `s` exactly once with nonzero derivative.
- How: Uses curve continuity `(fdBoundary_H_continuous H).continuousOn` and measurability; calls `pv_limit_via_dyadic` with all C2/derivative/injectivity hypotheses; lifts via `intervalIntegral.integral_congr` over `t ↦ rw [hs]`.
- Hypotheses: smoothness, nonzero derivative, continuous-derivative on the closed sub-interval, injectivity at the crossing.
- Uses-from-project: `fdBoundary_H_continuous`, `pv_limit_via_dyadic`, `CauchyPrincipalValueExists'`.
- Used by: ellipticPoint / single-crossing CPV constructions.
- Visibility: public.
- Lines: 77-91.

### private lemma `fdBoundary_H_cutout_cont_inv`
- Type: `(s : ℂ) (H : ℝ) (ε : ℝ) (hε : 0 < ε) → ContinuousOn (fun z => (z-s)⁻¹) ((fdBoundary_H H) '' Icc 0 5 \ Metric.ball s ε)`
- What: The function `z ↦ (z-s)⁻¹` is continuous on the curve image minus a ε-ball around `s`.
- How: `ContinuousOn.inv₀` with `continuousOn_id.sub continuousOn_const`; `sub_ne_zero.mpr` after a `Metric.mem_ball, not_lt` simp + `dist_self`+ `linarith`.
- Hypotheses: `ε > 0`.
- Uses-from-project: `fdBoundary_H`.
- Used by: `fdBoundary_H_cutout_meas`.
- Visibility: private.
- Lines: 93-102.

### private lemma `fdBoundary_H_cutout_bound`
- Type: `(H : ℝ) (hH : Real.sqrt 3/2 < H) (s : ℂ) (ε : ℝ) (hε : 0 < ε) → ∃ C, ∀ t ∈ Icc 0 5, ‖if-cutout integrand‖ ≤ C`
- What: Uniform bound on the cutout integrand `(γ-s)⁻¹·γ'` over `[0,5]` outside the ε-ball.
- How: Pulls `M`-bound on derivative from `fdBoundary_H_deriv_bound_ex`; returns `ε⁻¹·M`; splits on the `if` branch and on `t ∈ fdBoundary_H_partition`; on partition points (with `rcases`) uses `fdBoundary_H_not_differentiableAt_{1,3,4}` and `deriv_zero_of_not_differentiableAt`; off-partition uses `hM_bound`.
- Hypotheses: `H > √3/2`, `ε > 0`.
- Uses-from-project: `fdBoundary_H_deriv_bound_ex`, `fdBoundary_H_partition`, `fdBoundary_H_not_differentiableAt_1/3/4`.
- Used by: `fdBoundary_H_cutout_ii`.
- Visibility: private.
- Lines: 104-132.

### private lemma `fdBoundary_H_cutout_meas`
- Type: `(H : ℝ) (s : ℂ) (ε : ℝ) (hε : 0 < ε) → AEStronglyMeasurable (cutout integrand) (volume.restrict (Icc 0 5))`
- What: AE-strong measurability of the cutout integrand.
- How: Direct application of `aEStronglyMeasurable_pv_integrand_piecewiseC1` with `fdBoundary_H_cutout_cont_inv`, `(fdBoundary_H_continuous H).continuousOn`, `fdBoundary_H_deriv_continuousOn_off_partition`, partition `fdBoundary_H_partition`.
- Hypotheses: `ε > 0`.
- Uses-from-project: `aEStronglyMeasurable_pv_integrand_piecewiseC1`, `fdBoundary_H_continuous`, `fdBoundary_H_deriv_continuousOn_off_partition`, `fdBoundary_H_partition`.
- Used by: `fdBoundary_H_cutout_ii`.
- Visibility: private.
- Lines: 134-141.

### lemma `fdBoundary_H_cutout_ii`
- Type: `(H : ℝ) (hH : Real.sqrt 3/2 < H) (s : ℂ) (ε : ℝ) (hε : 0 < ε) → IntervalIntegrable (cutout integrand) volume 0 5`
- What: Interval integrability of the ε-cutout integrand on `[0,5]`.
- How: Rewrites via `intervalIntegrable_iff_integrableOn_Ioc_of_le`; uses `IntegrableOn.mono_set` with `HasFiniteIntegral.of_bounded` and the cutout bound (from `fdBoundary_H_cutout_bound`); restricts to `Ioc ⊆ Icc`.
- Hypotheses: `H > √3/2`, `ε > 0`.
- Uses-from-project: `fdBoundary_H_cutout_meas`, `fdBoundary_H_cutout_bound`.
- Used by: `cpv_extend_to_full_interval`.
- Visibility: public.
- Lines: 145-157.

### lemma `cpv_extend_to_full_interval`
- Type: `(H : ℝ) (hH : Real.sqrt 3/2 < H) (s : ℂ) (a' b' : ℝ) (ha' : 0 ≤ a') (hb' : b' ≤ 5) (hab' : a' < b') (h_sub : CauchyPrincipalValueExists' ... a' b' s) (h_avoid_left ... ) (h_avoid_right ...) → CauchyPrincipalValueExists' (fun z => (z-s)⁻¹) (fdBoundary_H H) 0 5 s`
- What: Glue a sub-interval CPV with avoidance segments to produce CPV on full `[0,5]`.
- How: Builds CPV on `[0,a']` and `[b',5]` via `cpv_avoidance` (using restriction of `fdBoundary_H_continuous`); chains with `cpv_concat` twice (`[0,a']∪[a',b']` then `[0,b']∪[b',5]`); each gluing supplies cutout integrability via `fdBoundary_H_cutout_ii` plus `Set.Icc_subset_Icc_right`/`Set.uIcc_of_le`.
- Hypotheses: positivity & ordering on `[a',b']`; CPV on the central sub-interval; curve avoids `s` outside it.
- Uses-from-project: `fdBoundary_H_continuous`, `cpv_avoidance`, `cpv_concat`, `fdBoundary_H_cutout_ii`.
- Used by: full-curve CPV construction in WindingWeights downstream.
- Visibility: public.
- Lines: 162-189.

---

## File Summary
- Total declarations: 13 (3 CPV existence theorems, 6 segment-coordinate lemmas, 1 sub-interval CPV lemma, 3 cutout-integrand helpers, 1 extension lemma).
- Key API: `cpv_exists_at_i`, `cpv_exists_at_rho`, `cpv_exists_at_rho_plus_one` (elliptic-point CPV); `cpv_exists_on_smooth_subinterval`, `cpv_extend_to_full_interval` (general crossing); segment coordinate identities.
- Unused declarations within file: none (segment lemmas are exported public API; cutout helpers are private and used internally).
- Sorries: none.
- `set_option`: none. Has `attribute [local instance] Classical.propDecidable` at line 23.
- Long proofs (>10 lines): `fdBoundary_H_cutout_bound` (29 lines) splits on partition point with `fdBoundary_H_not_differentiableAt_{1,3,4}` and uses `calc` + `mul_le_mul`; `cpv_extend_to_full_interval` (28 lines) chains `cpv_concat` twice; `fdBoundary_H_cutout_ii` (13 lines) uses `IntegrableOn.mono_set` + `HasFiniteIntegral.of_bounded`.
- Purpose: Builds the infrastructure needed for "on-curve" CPV existence at the three elliptic boundary points (`i`, `ρ`, `ρ+1`) of the fundamental domain, supplies segment-coordinate identities for the four boundary segments + arc of `fdBoundary_H H`, and packages two generic helpers (`cpv_exists_on_smooth_subinterval`, `cpv_extend_to_full_interval`) that turn local sub-interval CPV with avoidance into full-interval CPV by gluing via `cpv_concat`.
