# CrossingHigherOrder.lean Inventory

File: `/Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/HungerbuhlerWasem/CrossingHigherOrder.lean`
Total lines: 1225
Namespace: `HungerbuhlerWasem`

### `theorem closed_immersion_extend_zero_eq_one`
- **Type**: `(γ : ClosedPwC1Immersion x) → γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 0 = γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend 1`
- **What**: For a closed piecewise-C¹ immersion, the extended path takes the same value at parameters 0 and 1 (both equal to the basepoint x).
- **How**: Direct application of `Path.extend_zero` and `Path.extend_one` (both equal `x`).
- **Hypotheses**: γ is a closed piecewise-C¹ immersion with common endpoint x.
- **Uses from project**: `ClosedPwC1Immersion`
- **Used by**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`, `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`
- **Visibility**: public
- **Lines**: 71-74
- **Notes**: trivial

### `private theorem neg_pow_eq_self_of_even_sub_one`
- **Type**: `{k : ℕ} (z : ℂ) (m : ℤ) (hm : ((k - 1 : ℕ) : ℝ) = 2 * (m : ℝ)) → (-z) ^ (k - 1) = z ^ (k - 1)`
- **What**: If `k - 1 = 2m` (an even number, witnessed via a real-valued equation with an integer m), then `(-z)^(k-1) = z^(k-1)`.
- **How**: Extracts a natural witness `m'` of evenness via `Int.toNat_of_nonneg`, then `pow_mul` + `neg_pow` + `(-1)^2 = 1`.
- **Hypotheses**: k natural, m integer, the equation `(k-1) = 2m` over reals.
- **Uses from project**: []
- **Used by**: `h_B_of_angle_compat_smooth`
- **Visibility**: private
- **Lines**: 85-101
- **Notes**: none

### `theorem deriv_limit_eq_at_off_partition`
- **Type**: `(γ : ClosedPwC1Immersion x) {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) (h_off : t₀ ∉ γ.toPwC1Immersion.toPiecewiseC1Path.partition) → deriv f t₀ ≠ 0 ∧ Tendsto (deriv f) (𝓝[>] t₀) (𝓝 (deriv f t₀)) ∧ Tendsto (deriv f) (𝓝[<] t₀) (𝓝 (deriv f t₀))`
- **What**: At an interior point off the legacy partition, the derivative of the extended path is continuous (left and right derivative limits both equal `deriv f t₀`) and nonzero.
- **How**: Uses `deriv_continuous_off` and `deriv_ne_zero` from `PiecewiseC1Path`, then specializes to one-sided filters via `mono_left nhdsWithin_le_nhds`.
- **Hypotheses**: γ closed piecewise-C¹ immersion; t₀ interior; t₀ off the partition.
- **Uses from project**: `ClosedPwC1Immersion`, `PiecewiseC1Path.deriv_continuous_off`, `PwC1Immersion.deriv_ne_zero`
- **Used by**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`
- **Visibility**: public
- **Lines**: 110-124
- **Notes**: none

### `theorem h_B_of_angle_compat_smooth`
- **Type**: `(L : ℂ) (hL : L ≠ 0) (k : ℕ) (_hk : 2 ≤ k) (h_angle : ∃ m : ℤ, ((k - 1 : ℕ) : ℝ) * Real.pi = (m : ℝ) * (2 * Real.pi)) → (L / (↑‖L‖ : ℂ)) ^ (k - 1) = ((-L) / (↑‖L‖ : ℂ)) ^ (k - 1)`
- **What**: In the smooth crossing case, condition (B) `(k-1)·π ∈ 2π·ℤ` reduces to `k-1` even, hence the unit-circle (k-1)-power agrees for L and -L.
- **How**: Cancels π using `Real.pi_ne_zero` to extract `k-1 = 2m`, then applies `neg_pow_eq_self_of_even_sub_one` on the division `L/‖L‖`.
- **Hypotheses**: L ≠ 0; k ≥ 2; angle equation `(k-1)·π = m · 2π`.
- **Uses from project**: `neg_pow_eq_self_of_even_sub_one`
- **Used by**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`
- **Visibility**: public
- **Lines**: 131-146
- **Notes**: none

### `theorem hasDerivWithinAt_Ioi_of_tendsto`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hγ_cont : ContinuousAt γ t₀) (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L)) → HasDerivWithinAt γ L (Ioi t₀) t₀`
- **What**: Given continuity at t₀, eventual differentiability to the right of t₀, and a right-tendsto for `deriv γ`, the function has right derivative L at t₀.
- **How**: Uses `hasDerivWithinAt_Ioi_iff_Ici` to reduce to closed-right derivative, then `hasDerivWithinAt_Ici_of_tendsto_deriv` from mathlib.
- **Hypotheses**: γ continuous at t₀; eventually differentiable to the right; one-sided derivative tendsto.
- **Uses from project**: []
- **Used by**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`, `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`
- **Visibility**: public
- **Lines**: 154-164
- **Notes**: none

### `theorem hasDerivWithinAt_Iio_of_tendsto`
- **Type**: `{γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hγ_cont : ContinuousAt γ t₀) (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L)) → HasDerivWithinAt γ L (Iio t₀) t₀`
- **What**: Left-derivative version of `hasDerivWithinAt_Ioi_of_tendsto`.
- **How**: Uses `hasDerivWithinAt_Iio_iff_Iic` then `hasDerivWithinAt_Iic_of_tendsto_deriv`.
- **Hypotheses**: γ continuous at t₀; eventually differentiable to the left; one-sided derivative tendsto.
- **Uses from project**: []
- **Used by**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`, `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`
- **Visibility**: public
- **Lines**: 166-176
- **Notes**: none

### `theorem cpvIntegrandOn_singleMonomial_intervalIntegrable`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {S : Finset ℂ} (hs : s ∈ S) (c : ℂ) (k : ℕ) {ε : ℝ} (hε : 0 < ε) → IntervalIntegrable (fun t => cpvIntegrandOn S (fun z => c / (z - s) ^ k) γ.toPiecewiseC1Path.toPath.extend ε t) volume 0 1`
- **What**: Cutoff CPV-integrand for a single Laurent monomial `c/(z-s)^k` is interval-integrable on [0,1].
- **How**: Step-by-step: split into bad/good sets via indicator, bound on good set by `‖c‖/ε^k · K` (K = Lipschitz constant of extended path), use measurability of γ and badSet via `Finset.countable_toSet`, then `MeasureTheory.IntegrableOn.of_bound`. Key lemmas: `ClosedPwC1Immersion.lipschitzWith_extend`, `cpvIntegrandOn_of_exists_le`, `cpvIntegrandOn_of_forall_gt`, `pow_le_pow_left₀`, `norm_deriv_le_of_lipschitz`.
- **Hypotheses**: γ closed piecewise-C¹ immersion; s in S; cutoff radius ε > 0.
- **Uses from project**: `ClosedPwC1Immersion`, `ClosedPwC1Immersion.lipschitzWith_extend`, `cpvIntegrandOn`, `cpvIntegrandOn_of_exists_le`, `cpvIntegrandOn_of_forall_gt`, `norm_deriv_le_of_lipschitz`
- **Used by**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`, `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`
- **Visibility**: public
- **Lines**: 184-284
- **Notes**: proof >30 lines (≈100 lines), uses `classical`

### `private theorem integral_pow_inv_eq_FTC_of_le`
- **Type**: `{γ γ' : ℝ → ℂ} {s : ℂ} {k : ℕ} {a b : ℝ} {exc : Set ℝ} (hexc : exc.Countable) (hk : 2 ≤ k) (hab : a ≤ b) (hγ_cont : ContinuousOn γ (Icc a b)) (hγ_diff : ∀ t ∈ Ioo a b \ exc, HasDerivAt γ (γ' t) t) (h_avoids : ∀ t ∈ Icc a b, γ t ≠ s) (h_int : IntervalIntegrable ...) → ∫ t in a..b, γ' t / (γ t - s) ^ k = ...`
- **What**: Countable-exception FTC for `∫ γ'/(γ-s)^k`: equals `F(γ b) - F(γ a)` where `F(z) = -1/((k-1)(z-s)^{k-1})`.
- **How**: Defines `F`, shows `F ∘ γ` differentiates correctly off the countable exception set via `hasDerivAt_antiderivative_pow_inv_complex` and the chain rule, continuity by `ContinuousAt.comp_continuousWithinAt`, then applies `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`.
- **Hypotheses**: countable exception set; k ≥ 2; a ≤ b; γ continuous on [a,b], HasDerivAt off the exception set; γ avoids s; integrability.
- **Uses from project**: `hasDerivAt_antiderivative_pow_inv_complex`
- **Used by**: `closed_excised_integral_eq_antideriv_diff_of_continuous`
- **Visibility**: private
- **Lines**: 296-329
- **Notes**: proof >30 lines

### `private theorem closed_excised_integral_eq_antideriv_diff_of_continuous`
- **Type**: `{γ γ' : ℝ → ℂ} {s : ℂ} {k : ℕ} {a t_minus t_plus b : ℝ} {exc : Set ℝ} ... → (∫ t in a..t_minus, ...) + (∫ t in t_plus..b, ...) = ...`
- **What**: Closed-curve excised integral identity: for a closed curve (γ a = γ b), the two side integrals telescope to a single antiderivative difference, with a countable exception set for partition points.
- **How**: Applies `integral_pow_inv_eq_FTC_of_le` to each side, then uses `h_close` to cancel the endpoint terms.
- **Hypotheses**: countable exception; k ≥ 2; ordering a ≤ t_minus, t_plus ≤ b; closure γ a = γ b; continuity/diff/avoidance/integrability on both pieces.
- **Uses from project**: `integral_pow_inv_eq_FTC_of_le`
- **Used by**: `hw_theorem_3_3_parametric_relaxed`
- **Visibility**: private
- **Lines**: 335-356
- **Notes**: none

### `private theorem hw_theorem_3_3_parametric_relaxed`
- **Type**: Parametric tendsto result with ~30 hypotheses asserting that the two-sided excision integral of `γ'/(γ-s)^k` tends to zero as ε → 0⁺.
- **What**: The relaxed parametric Hungerbühler-Wasem 3.3: combines the antiderivative difference of two side integrals (over [a, t_eps_minus ε] ∪ [t_eps_plus ε, b]) and shows it tends to zero, using a countable exception set for partition points.
- **How**: Combines `F_curve_diff_tendsto_zero_under_conditionB` (from SectorCancellation) with `closed_excised_integral_eq_antideriv_diff_of_continuous` via `Tendsto.congr'`, using `tendsto_zero_iff_norm_tendsto_zero`.
- **Hypotheses**: 30+ hypotheses including: flatness of order n at t₀; nonzero left/right derivative limits; condition (B) angle equation `h_B`; closed curve; exit-time tendsto/radius hypotheses; eventual continuity/HasDerivAt/avoidance/integrability on shrinking subintervals.
- **Uses from project**: `F_curve_diff_tendsto_zero_under_conditionB`, `closed_excised_integral_eq_antideriv_diff_of_continuous`, `IsFlatOfOrder`
- **Used by**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`, `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`
- **Visibility**: private
- **Lines**: 363-417
- **Notes**: heavy hypothesis list, abbreviated type signature

### `theorem hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`
- **Type**: `(γ : ClosedPwC1Immersion x) {s : ℂ} {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo 0 1) (h_at : ... = s) (h_unique : ...) (h_t₀_off_partition : ...) {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) (h_flat : IsFlatOfOrder ... t₀ n) (h_angle : ∃ m : ℤ, (k-1)·π = m·2π) (c : ℂ) → HasCauchyPVOn {s} (fun z => c / (z - s) ^ k) γ.toPiecewiseC1Path 0`
- **What**: Headline wrapper (smooth crossing): higher-order CPV of `c/(z-s)^k` along a closed piecewise-C¹ immersion vanishes if the curve crosses s only at an off-partition interior point t₀, with flatness of order n ≥ k and condition (B) `(k-1)·π ∈ 2π·ℤ`.
- **How**: Massive orchestration: derive ~30 sub-hypotheses (derivative limits via `deriv_limit_eq_at_off_partition`; mono/anti radii via `norm_sub_strictMonoOn_right`/`Left`; far-bound via `exists_far_bound_compact`; exit times via `firstExitTimeRight/Left` family; eventual integrability/avoidance on shrinking intervals; cpv-integrand cutoff integrability via `cpvIntegrandOn_singleMonomial_intervalIntegrable`); then call `hw_theorem_3_3_parametric_relaxed` to get the existence of the limit, and finally `hasCauchyPVOn_singleton_of_exitTime_excision` to package and scale by c.
- **Hypotheses**: ClosedPwC1Immersion γ; interior t₀; unique crossing; off-partition; flat of order n ≥ k ≥ 2; angle-compatibility (smooth-case form).
- **Uses from project**: `ClosedPwC1Immersion`, `deriv_limit_eq_at_off_partition`, `norm_sub_strictMonoOn_right`, `norm_sub_strictAntiOn_left`, `exists_far_bound_compact`, `hasDerivWithinAt_Ioi_of_tendsto`, `hasDerivWithinAt_Iio_of_tendsto`, `h_B_of_angle_compat_smooth`, `LeanModularForms.firstExitTimeRight`, `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeRight_tendsto_t₀`, `LeanModularForms.firstExitTimeLeft_tendsto_t₀`, `LeanModularForms.firstExitTimeRight_radius_eventually`, `LeanModularForms.firstExitTimeLeft_radius_eventually`, `eventually_differentiable_right`, `eventually_differentiable_left`, `PiecewiseC1Path.differentiable_off`, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`, `shape_eventually_of_strict_mono`, `cpvIntegrandOn_singleMonomial_intervalIntegrable`, `hw_theorem_3_3_parametric_relaxed`, `hasCauchyPVOn_singleton_of_exitTime_excision`, `closed_immersion_extend_zero_eq_one`, `IsFlatOfOrder`, `cpvIntegrandOn`, `HasCauchyPVOn`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 434-779
- **Notes**: proof >30 lines (~345 lines), key headline theorem T-BR-Y2; uses `classical`

### `private theorem div_norm_eq_exp_arg`
- **Type**: `{z : ℂ} (hz : z ≠ 0) → z / (↑‖z‖ : ℂ) = Complex.exp (↑(Complex.arg z) * Complex.I)`
- **What**: For nonzero z ∈ ℂ, `z/‖z‖ = exp(i·arg z)`.
- **How**: Uses `Complex.norm_mul_exp_arg_mul_I` to express z = ‖z‖·exp(i·arg z), then divides.
- **Hypotheses**: z ≠ 0.
- **Uses from project**: []
- **Used by**: `h_B_of_angle_compat_corner`
- **Visibility**: private
- **Lines**: 793-801
- **Notes**: none

### `theorem h_B_of_angle_compat_corner`
- **Type**: `{L_minus L_plus : ℂ} (hL_minus : L_minus ≠ 0) (hL_plus : L_plus ≠ 0) {k : ℕ} (_hk : 2 ≤ k) (h_angle : ∃ m : ℤ, ((k-1):ℝ) * (Complex.arg L_plus - Complex.arg (-L_minus)) = m · 2π) → (L_plus/‖L_plus‖)^(k-1) = ((-L_minus)/‖L_minus‖)^(k-1)`
- **What**: Corner-case angle bridge: from the integer angle equation `(k-1)·(arg L_+ - arg(-L_-)) = m·2π`, the unit-circle (k-1)-powers of `L_+/‖L_+‖` and `(-L_-)/‖L_-‖` agree.
- **How**: Rewrites both sides as `exp(i·(k-1)·arg L)` via `div_norm_eq_exp_arg`, applies `Complex.exp_eq_exp_iff_exists_int`, and uses the cast of the real-valued angle equation to discharge the integer winding.
- **Hypotheses**: L_minus, L_plus nonzero; k ≥ 2; integer winding equation.
- **Uses from project**: `div_norm_eq_exp_arg`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 811-854
- **Notes**: T-BR-Y10 bridge

### `theorem hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`
- **Type**: Same as smooth-case wrapper but with explicit `L_minus, L_plus` derivatives, their tendsto hypotheses, and a directly-given `h_B` of the corner form.
- **What**: Corner-friendly variant of the headline CPV vanishing theorem (T-BR-Y10): generalizes the smooth-case theorem to allow t₀ to be a corner (`t₀ ∈ partition`), accepting separate `L_-, L_+` derivative limits.
- **How**: Structurally identical to the smooth-case proof but uses `L_minus, L_plus` separately and skips the off-partition smoothness step. Same ~300-line orchestration of: mono/anti radii, exit times, eventual integrability/avoidance, `hw_theorem_3_3_parametric_relaxed`, `hasCauchyPVOn_singleton_of_exitTime_excision`. Key dependency: `norm_sub_strictMonoOn_right`/`Left`, `firstExitTimeRight/Left` family.
- **Hypotheses**: ClosedPwC1Immersion γ; interior t₀; unique crossing; nonzero one-sided limits L_minus, L_plus (no off-partition required); flat of order n ≥ k ≥ 2; corner-form `h_B`.
- **Uses from project**: `ClosedPwC1Immersion`, `norm_sub_strictMonoOn_right`, `norm_sub_strictAntiOn_left`, `exists_far_bound_compact`, `hasDerivWithinAt_Ioi_of_tendsto`, `hasDerivWithinAt_Iio_of_tendsto`, `LeanModularForms.firstExitTimeRight`, `LeanModularForms.firstExitTimeLeft`, `LeanModularForms.firstExitTimeRight_tendsto_t₀`, `LeanModularForms.firstExitTimeLeft_tendsto_t₀`, `LeanModularForms.firstExitTimeRight_radius_eventually`, `LeanModularForms.firstExitTimeLeft_radius_eventually`, `eventually_differentiable_right`, `eventually_differentiable_left`, `PiecewiseC1Path.differentiable_off`, `ClosedPwC1Curve.deriv_extend_intervalIntegrable`, `shape_eventually_of_strict_mono`, `cpvIntegrandOn_singleMonomial_intervalIntegrable`, `hw_theorem_3_3_parametric_relaxed`, `hasCauchyPVOn_singleton_of_exitTime_excision`, `closed_immersion_extend_zero_eq_one`, `IsFlatOfOrder`, `cpvIntegrandOn`, `HasCauchyPVOn`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 889-1221
- **Notes**: proof >30 lines (~330 lines), corner-friendly headline T-BR-Y10; uses `classical`

## File Summary

- **Total declarations**: 14 (3 private + 11 non-private, 1 of which is a sub-theorem)
- **Key API (used by 3+ in file)**: none in-file (the file is a leaf wrapper). External users consume the two headline theorems (smooth and corner variants).
- **Unused in file**: `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB`, `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner`, `h_B_of_angle_compat_corner` (these are the headline public API consumed downstream).
- **Sorries**: 0
- **set_option**: none
- **Proofs >30 lines**: `cpvIntegrandOn_singleMonomial_intervalIntegrable` (≈100), `integral_pow_inv_eq_FTC_of_le` (≈33), `hw_theorem_3_3_parametric_relaxed` (≈55), `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB` (≈345), `hasCauchyPVOn_higherOrder_polar_at_crossing_under_conditionB_corner` (≈330).
- **One-paragraph purpose**: Wraps the heavy `hasCauchyPVOn_singleton_pow_of_conditionB_assembled` machinery (~30 hypotheses) into two paper-faithful wrapper theorems: one for SMOOTH crossings (where the crossing point t₀ is off the legacy partition, so `L_- = L_+`) and one for CORNER crossings (where left and right derivative limits may differ). Each wrapper takes ≈5 conceptual inputs — a closed piecewise-C¹ immersion γ, an interior crossing time t₀ with uniqueness, flatness of order n ≥ k at t₀, and the condition (B) angle compatibility — and discharges every internal hypothesis (derivative limits, monotonicity radii, exit times, far bounds, eventual differentiability/integrability/avoidance) before invoking the relaxed FTC (`hw_theorem_3_3_parametric_relaxed`) which uses `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le` to bypass partition points. The corner variant adds a `div_norm_eq_exp_arg` + `Complex.exp_eq_exp_iff_exists_int` bridge from the general-angle equation `(k-1)·α ∈ 2π·ℤ` to the algebraic form of `h_B`. The result conclusion is `HasCauchyPVOn {s} (c/(z-s)^k) γ.toPiecewiseC1Path 0`, i.e. the Cauchy principal value of a single Laurent monomial vanishes along the immersion.
