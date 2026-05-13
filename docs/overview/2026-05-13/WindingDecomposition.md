# WindingDecomposition.lean Inventory

### `def angleAtCrossing`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (_ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : ℝ`
- **What**: Signed angle at a crossing point where the piecewise C¹ immersion passes through z₀: at a smooth point not in the partition the angle is π; at a corner point in the partition it is `arg(L_right) - arg(-L_left)` from one-sided derivative limits.
- **How**: Definition by `if h : t₀ ∈ partition` branch — uses `Classical.choose` on `γ.left_deriv_limit` and `γ.right_deriv_limit` to extract one-sided derivative vectors; else returns `Real.pi`.
- **Hypotheses**: `t₀` in the open interval `(0,1)` (used only to scope the position).
- **Uses from project**: `PwC1Immersion`, `PwC1Immersion.left_deriv_limit`, `PwC1Immersion.right_deriv_limit`, `PiecewiseC1Path.partition`, `PwC1Immersion.toPiecewiseC1Path`
- **Used by**: `angleAtCrossing_smooth`, `angleAtCrossing_smooth_pos`, `angleAtCrossing_smooth_div_two_pi`, `externalWindingContribution`, `generalizedWindingNumber_eq_external_sub_angle`, and all downstream theorems.
- **Visibility**: public
- **Lines**: 59-64
- **Notes**: none

### `theorem angleAtCrossing_smooth`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) : angleAtCrossing γ t₀ ht₀ = Real.pi`
- **What**: At a smooth point (outside the partition), the crossing angle equals π.
- **How**: `simp` unfolds the `dite` using `hsmooth` to take the else branch.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`; `t₀ ∉ γ.toPiecewiseC1Path.partition`.
- **Uses from project**: `angleAtCrossing`, `PwC1Immersion.toPiecewiseC1Path`, `PiecewiseC1Path.partition`
- **Used by**: `angleAtCrossing_smooth_pos`, `angleAtCrossing_smooth_div_two_pi`, `generalizedWindingNumber_eq_neg_half_smooth_crossing`, `externalWindingContribution_zero_of_neg_half`, `generalizedWindingNumber_eq_half_of_external_one_smooth`, `generalizedWindingNumber_eq_neg_three_halves_of_external_neg_one_smooth`, `windingContributionAt_smooth`
- **Visibility**: public
- **Lines**: 69-72
- **Notes**: none

### `theorem angleAtCrossing_smooth_pos`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) : 0 < angleAtCrossing γ t₀ ht₀`
- **What**: At smooth points the crossing angle π is positive.
- **How**: Rewrites with `angleAtCrossing_smooth` then `Real.pi_pos`.
- **Hypotheses**: smoothness at `t₀`.
- **Uses from project**: `angleAtCrossing`, `angleAtCrossing_smooth`, `PwC1Immersion.toPiecewiseC1Path`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 75-79
- **Notes**: none

### `theorem angleAtCrossing_smooth_div_two_pi`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) : (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi) = 1 / 2`
- **What**: Smooth crossings contribute exactly 1/2 to the angle-sum (π divided by 2π).
- **How**: Rewrite with `angleAtCrossing_smooth`, observe `(Real.pi : ℂ) ≠ 0`, finish with `field_simp`.
- **Hypotheses**: smoothness at `t₀`.
- **Uses from project**: `angleAtCrossing`, `angleAtCrossing_smooth`, `PwC1Immersion.toPiecewiseC1Path`
- **Used by**: `windingContributionAt_smooth`
- **Visibility**: public
- **Lines**: 82-87
- **Notes**: none

### `def externalWindingContribution`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : ℂ`
- **What**: External winding contribution at a crossing: `generalizedWindingNumber γ z₀ + angleAtCrossing γ t₀ / (2π)`; the "integer part" of the H-W decomposition.
- **How**: Sum of generalized winding number plus the normalized angle.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `generalizedWindingNumber`, `angleAtCrossing`, `PwC1Immersion.toPiecewiseC1Path`
- **Used by**: `generalizedWindingNumber_eq_external_sub_angle`, `externalWindingContribution_eq`, `generalizedWindingNumber_eq_neg_angleContribution_single`, `externalWindingContribution_zero_of_windingNumber_eq`, `externalWindingContribution_zero_of_neg_half`, `generalizedWindingNumber_of_external_eq`, `HasIntegerExternalWinding`, `HasIntegerExternalWinding.of_zero`
- **Visibility**: public
- **Lines**: 97-100
- **Notes**: none

### `theorem generalizedWindingNumber_eq_external_sub_angle`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = externalWindingContribution γ z₀ t₀ ht₀ - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)`
- **What**: H-W Proposition 2.3 decomposition: `n_{z₀}(γ) = N - α/(2π)`.
- **How**: Unfold `externalWindingContribution`, simplify via `add_sub_cancel_right`.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `generalizedWindingNumber`, `externalWindingContribution`, `angleAtCrossing`
- **Used by**: `generalizedWindingNumber_eq_neg_angleContribution_single`, `generalizedWindingNumber_of_external_eq`, `generalizedWindingNumber_eq_external_sub_contribution`
- **Visibility**: public
- **Lines**: 112-117
- **Notes**: none

### `theorem externalWindingContribution_eq`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : externalWindingContribution γ z₀ t₀ ht₀ = generalizedWindingNumber γ.toPiecewiseC1Path z₀ + (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)`
- **What**: Restates the definition of `externalWindingContribution`.
- **How**: `rfl`.
- **Hypotheses**: none beyond setup.
- **Uses from project**: `externalWindingContribution`, `generalizedWindingNumber`, `angleAtCrossing`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 121-125
- **Notes**: none

### `theorem generalizedWindingNumber_eq_neg_angleContribution_single`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -((angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi))`
- **What**: When external winding vanishes, gWN equals minus the normalized crossing angle.
- **How**: Apply `generalizedWindingNumber_eq_external_sub_angle`, substitute `h_external = 0`, simplify `zero_sub`.
- **Hypotheses**: `externalWindingContribution = 0`.
- **Uses from project**: `generalizedWindingNumber`, `externalWindingContribution`, `angleAtCrossing`, `generalizedWindingNumber_eq_external_sub_angle`
- **Used by**: `generalizedWindingNumber_eq_neg_half_smooth_crossing`, `generalizedWindingNumber_eq_neg_corner_contribution`
- **Visibility**: public
- **Lines**: 131-138
- **Notes**: none

### `theorem generalizedWindingNumber_eq_neg_half_smooth_crossing`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(1 / 2)`
- **What**: At a smooth crossing with zero external winding the gWN is exactly -1/2.
- **How**: Substitute via `generalizedWindingNumber_eq_neg_angleContribution_single` and `angleAtCrossing_smooth`, finish with `field_simp` after `Real.pi ≠ 0`.
- **Hypotheses**: smoothness at `t₀`; external winding zero.
- **Uses from project**: `generalizedWindingNumber_eq_neg_angleContribution_single`, `angleAtCrossing_smooth`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 143-150
- **Notes**: none

### `theorem generalizedWindingNumber_eq_neg_corner_contribution`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hangle : angleAtCrossing γ t₀ ht₀ = α) (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 0) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(↑α / (2 * ↑Real.pi))`
- **What**: At a corner crossing of angle α with zero external winding, gWN = -α/(2π).
- **How**: Rewrite with `generalizedWindingNumber_eq_neg_angleContribution_single`, then substitute `hangle`.
- **Hypotheses**: corner angle equals α; external winding zero.
- **Uses from project**: `generalizedWindingNumber_eq_neg_angleContribution_single`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 154-158
- **Notes**: none

### `theorem externalWindingContribution_zero_of_windingNumber_eq`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (h_eq : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -((angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi))) : externalWindingContribution γ z₀ t₀ ht₀ = 0`
- **What**: Converse: gWN equal to `-α/(2π)` forces external winding = 0.
- **How**: Unfold `externalWindingContribution`, substitute `h_eq`, simplify via `neg_add_cancel`.
- **Hypotheses**: gWN identity holds.
- **Uses from project**: `externalWindingContribution`, `generalizedWindingNumber`, `angleAtCrossing`
- **Used by**: `externalWindingContribution_zero_of_neg_half`
- **Visibility**: public
- **Lines**: 165-170
- **Notes**: none

### `theorem externalWindingContribution_zero_of_neg_half`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) (h_eq : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(1 / 2)) : externalWindingContribution γ z₀ t₀ ht₀ = 0`
- **What**: At a smooth crossing where gWN = -1/2, external winding vanishes.
- **How**: Apply `externalWindingContribution_zero_of_windingNumber_eq` with the rewrite via `angleAtCrossing_smooth`, plus `field_simp`.
- **Hypotheses**: smooth at `t₀`; gWN = -1/2.
- **Uses from project**: `externalWindingContribution_zero_of_windingNumber_eq`, `angleAtCrossing_smooth`
- **Used by**: `HasIntegerExternalWinding.of_neg_half_smooth`
- **Visibility**: public
- **Lines**: 174-181
- **Notes**: none

### `theorem generalizedWindingNumber_of_external_eq`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (N : ℂ) (hN : externalWindingContribution γ z₀ t₀ ht₀ = N) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = N - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)`
- **What**: Generalizes decomposition: with external winding equal to N (any complex), gWN = N - α/(2π).
- **How**: Substitute `hN` into `generalizedWindingNumber_eq_external_sub_angle`.
- **Hypotheses**: external winding equals `N`.
- **Uses from project**: `generalizedWindingNumber_eq_external_sub_angle`
- **Used by**: `generalizedWindingNumber_of_external_int`, `generalizedWindingNumber_eq_half_of_external_one_smooth`, `generalizedWindingNumber_eq_neg_three_halves_of_external_neg_one_smooth`
- **Visibility**: public
- **Lines**: 187-191
- **Notes**: none

### `theorem generalizedWindingNumber_of_external_int`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (n : ℤ) (hn : externalWindingContribution γ z₀ t₀ ht₀ = (n : ℂ)) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = (n : ℂ) - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)`
- **What**: Integer specialization of `generalizedWindingNumber_of_external_eq`.
- **How**: Direct application.
- **Hypotheses**: external winding equals integer `n`.
- **Uses from project**: `generalizedWindingNumber_of_external_eq`
- **Used by**: `generalizedWindingNumber_eq_int_sub_angle_of_hasInt`
- **Visibility**: public
- **Lines**: 195-199
- **Notes**: none

### `theorem generalizedWindingNumber_eq_half_of_external_one_smooth`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) (h_external : externalWindingContribution γ z₀ t₀ ht₀ = 1) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = 1 / 2`
- **What**: External winding = 1 at a smooth crossing yields gWN = 1/2.
- **How**: Apply `generalizedWindingNumber_of_external_eq` then `angleAtCrossing_smooth`, simplify with `field_simp` and `ring`.
- **Hypotheses**: smooth; external winding = 1.
- **Uses from project**: `generalizedWindingNumber_of_external_eq`, `angleAtCrossing_smooth`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 203-211
- **Notes**: none

### `theorem generalizedWindingNumber_eq_neg_three_halves_of_external_neg_one_smooth`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) (h_external : externalWindingContribution γ z₀ t₀ ht₀ = -1) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(3 / 2)`
- **What**: External winding = -1 at a smooth crossing yields gWN = -3/2.
- **How**: Apply `generalizedWindingNumber_of_external_eq` then `angleAtCrossing_smooth`, simplify with `field_simp` and `ring`.
- **Hypotheses**: smooth; external winding = -1.
- **Uses from project**: `generalizedWindingNumber_of_external_eq`, `angleAtCrossing_smooth`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 215-224
- **Notes**: none

### `def HasIntegerExternalWinding`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : Prop`
- **What**: Predicate asserting the external winding contribution is integer-valued — the content of H-W Proposition 2.3.
- **How**: `∃ n : ℤ, externalWindingContribution γ z₀ t₀ ht₀ = (n : ℂ)`.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `externalWindingContribution`
- **Used by**: `HasIntegerExternalWinding.of_zero`, `HasIntegerExternalWinding.of_neg_half_smooth`, `generalizedWindingNumber_eq_int_sub_angle_of_hasInt`
- **Visibility**: public
- **Lines**: 240-242
- **Notes**: none

### `theorem HasIntegerExternalWinding.of_zero`
- **Type**: `{γ : PwC1Immersion x y} {z₀ : ℂ} {t₀ : ℝ} {ht₀ : t₀ ∈ Ioo (0 : ℝ) 1} (h : externalWindingContribution γ z₀ t₀ ht₀ = 0) : HasIntegerExternalWinding γ z₀ t₀ ht₀`
- **What**: Zero external winding gives integer predicate with witness 0.
- **How**: `⟨0, by simp [h]⟩`.
- **Hypotheses**: external winding = 0.
- **Uses from project**: `HasIntegerExternalWinding`, `externalWindingContribution`
- **Used by**: `HasIntegerExternalWinding.of_neg_half_smooth`
- **Visibility**: public
- **Lines**: 245-248
- **Notes**: none

### `theorem HasIntegerExternalWinding.of_neg_half_smooth`
- **Type**: `{γ : PwC1Immersion x y} {z₀ : ℂ} {t₀ : ℝ} {ht₀ : t₀ ∈ Ioo (0 : ℝ) 1} (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) (h_gWN : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = -(1 / 2)) : HasIntegerExternalWinding γ z₀ t₀ ht₀`
- **What**: gWN = -1/2 at a smooth crossing implies integer external winding.
- **How**: Combine `externalWindingContribution_zero_of_neg_half` with `HasIntegerExternalWinding.of_zero`.
- **Hypotheses**: smooth; gWN = -1/2.
- **Uses from project**: `externalWindingContribution_zero_of_neg_half`, `HasIntegerExternalWinding.of_zero`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 252-256
- **Notes**: none

### `theorem generalizedWindingNumber_eq_int_sub_angle_of_hasInt`
- **Type**: `{γ : PwC1Immersion x y} {z₀ : ℂ} {t₀ : ℝ} {ht₀ : t₀ ∈ Ioo (0 : ℝ) 1} (h : HasIntegerExternalWinding γ z₀ t₀ ht₀) : ∃ n : ℤ, (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = (n : ℂ) - (angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)`
- **What**: Complete form of HW Proposition 2.3 — gWN = n - α/(2π) for some integer n given `HasIntegerExternalWinding`.
- **How**: Destruct the existential, supply `generalizedWindingNumber_of_external_int`.
- **Hypotheses**: `HasIntegerExternalWinding`.
- **Uses from project**: `HasIntegerExternalWinding`, `generalizedWindingNumber_of_external_int`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 261-266
- **Notes**: none

### `def windingContributionAt`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : ℂ`
- **What**: Single-crossing winding contribution: `angleAtCrossing/(2π)`.
- **How**: `(angleAtCrossing γ t₀ ht₀ : ℂ) / (2 * ↑Real.pi)`.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `angleAtCrossing`
- **Used by**: `windingContributionAt_smooth`, `windingContributionAt_corner`, `generalizedWindingNumber_eq_external_sub_contribution`
- **Visibility**: public
- **Lines**: 272-273
- **Notes**: none

### `theorem windingContributionAt_smooth`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hsmooth : t₀ ∉ γ.toPiecewiseC1Path.partition) : windingContributionAt γ t₀ ht₀ = 1 / 2`
- **What**: Smooth crossings give angle-based winding 1/2.
- **How**: Direct from `angleAtCrossing_smooth_div_two_pi`.
- **Hypotheses**: smooth at `t₀`.
- **Uses from project**: `windingContributionAt`, `angleAtCrossing_smooth_div_two_pi`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 276-279
- **Notes**: none

### `theorem windingContributionAt_corner`
- **Type**: `(γ : PwC1Immersion x y) (t₀ : ℝ) (α : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (hangle : angleAtCrossing γ t₀ ht₀ = α) : windingContributionAt γ t₀ ht₀ = ↑α / (2 * ↑Real.pi)`
- **What**: Corner with angle α gives angle-based winding α/(2π).
- **How**: `simp` with `hangle` after unfolding `windingContributionAt`.
- **Hypotheses**: `angleAtCrossing = α`.
- **Uses from project**: `windingContributionAt`, `angleAtCrossing`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 282-285
- **Notes**: none

### `theorem generalizedWindingNumber_eq_external_sub_contribution`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) : (generalizedWindingNumber γ.toPiecewiseC1Path z₀ : ℂ) = externalWindingContribution γ z₀ t₀ ht₀ - windingContributionAt γ t₀ ht₀`
- **What**: HW decomposition phrased with `windingContributionAt` instead of raw angle.
- **How**: Refers to `generalizedWindingNumber_eq_external_sub_angle` (definitionally equal modulo unfolding `windingContributionAt`).
- **Hypotheses**: `t₀ ∈ Ioo 0 1`.
- **Uses from project**: `generalizedWindingNumber`, `externalWindingContribution`, `windingContributionAt`, `generalizedWindingNumber_eq_external_sub_angle`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 289-293
- **Notes**: none

### `theorem endpoint_avoidance_of_unique_interior_crossing`
- **Type**: `(γ : PwC1Immersion x y) (z₀ : ℂ) (t₀ : ℝ) (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) (_hcross : (γ : ℝ → ℂ) t₀ = z₀) (honly : ∀ t ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t = z₀ → t = t₀) : (γ : ℝ → ℂ) 0 ≠ z₀ ∧ (γ : ℝ → ℂ) 1 ≠ z₀`
- **What**: If `t₀ ∈ (0,1)` is the unique solution of γ(t) = z₀ on `[0,1]`, both endpoints avoid `z₀`.
- **How**: Case-split each endpoint: if γ(0) = z₀ then `honly` gives 0 = t₀ contradicting `ht₀.1`; analogously for 1.
- **Hypotheses**: `t₀ ∈ Ioo 0 1`; unique crossing.
- **Uses from project**: `PwC1Immersion`
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 299-307
- **Notes**: none

## File Summary

**File**: `LeanModularForms/ForMathlib/WindingDecomposition.lean` (309 lines)

Formalizes **Hungerbühler–Wasem Proposition 2.3** decomposing the generalized winding number `n_{z₀}(γ) = N - α/(2π)` for a piecewise C¹ immersion passing through `z₀`. Imports `CrossingAnalysis` and `GeneralizedWindingNumber`. Provides:
- `angleAtCrossing` (signed angle, π at smooth points, corner formula otherwise) and `externalWindingContribution` (the integer-valued `N`).
- The decomposition theorem `generalizedWindingNumber_eq_external_sub_angle` and many specializations: gWN = -1/2 at smooth zero-external crossings; corner contribution `-α/(2π)`; integer-shift consequences for ±1 external winding.
- Converse helpers (`externalWindingContribution_zero_of_neg_half`, etc.) and the integer predicate `HasIntegerExternalWinding` (with builder lemmas `of_zero`, `of_neg_half_smooth`).
- A convenient `windingContributionAt` alias and the endpoint avoidance lemma `endpoint_avoidance_of_unique_interior_crossing`.

No `sorry`, no axioms, no `set_option`. All proofs are short (mostly algebraic after `field_simp`).
