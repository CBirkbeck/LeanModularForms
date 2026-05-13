# /Users/mcu22seu/Documents/GitHub/LeanModularForms/LeanModularForms/ForMathlib/FDWindingDataFullAssembly.lean

## theorem `arg_mem_arc_range`
- **Type**: `{z : ℂ} (hz_norm : ‖z‖ = 1) (hz_im : 0 < z.im) (hz_re : |z.re| < 1/2)
  → π/3 < z.arg ∧ z.arg < 2π/3`.
- **What**: A point on the upper unit circle with `|re| < 1/2` has argument
  strictly in `(π/3, 2π/3)` — the open arc of the standard fundamental
  domain's bottom circle.
- **How**: Uses `Complex.cos_arg`, `Complex.sin_arg` (on the unit circle these
  give `re` and `im`), `Complex.arg_nonneg_iff` and `Complex.arg_le_pi` to
  pin `arg z ∈ (0, π)`, then case-splits with `Real.cos_le_cos_of_nonneg_of_le_pi`
  against `cos(π/3) = 1/2` and `cos(2π/3) = -1/2` (derived from
  `Real.cos_pi_sub` + `Real.cos_pi_div_three`); contradicts each via `linarith`
  on the constraint `|re| < 1/2`.
- **Hypotheses**: norm 1, positive imaginary part, real part bounded by 1/2.
- **Uses-from-project**: none directly (uses mathlib for arg/cos/sin lemmas);
  the file imports `BoundaryWindingSeg1Proof`, `BoundaryWindingSeg4Proof`,
  `BoundaryWindingArcProof` for the downstream assembler.
- **Used by**: `mkFDWindingDataFull_of_ftcProviders` (case for the arc).
- **Visibility**: public (`theorem`); root namespace (no enclosing namespace).
- **Lines**: 33-59.
- **Notes**: 27-line proof; named intermediate steps `h_cos`, `h_sin`,
  `h_arg_pos`, `h_arg_lt_pi`, `h_cos_2pi3`.

## theorem `eq_exp_arg_mul_I`
- **Type**: `{z : ℂ} (hz_norm : ‖z‖ = 1) → z = exp (↑z.arg * I)`.
- **What**: On the unit circle, a complex number equals `exp(i·arg z)`.
- **How**: Rewrites via `Complex.norm_mul_exp_arg_mul_I z` then plugs
  `hz_norm : ‖z‖ = 1` with `ofReal_one` and `one_mul`. One-line proof using
  `conv_lhs`.
- **Hypotheses**: `‖z‖ = 1`.
- **Uses-from-project**: mathlib only (`norm_mul_exp_arg_mul_I`).
- **Used by**: `mkFDWindingDataFull_of_ftcProviders` (arc case rewrites
  `z = exp(i z.arg)` to apply the arc FTC provider).
- **Visibility**: public (`theorem`); root namespace.
- **Lines**: 62-64.

## def `mkFDWindingDataFull_of_ftcProviders`
- **Type**: For `1 < H`, `D : FDWindingData H`, and three FTC providers
  (seg1: right vertical edge `re = 1/2`; seg4: left vertical edge
  `re = -1/2`; arc: argument in `(π/3, 2π/3)`), produce `FDWindingDataFull H`.
- **What**: Promotes a base `FDWindingData H` (interior winding + three
  elliptic-corner data) to the full assembly by classifying every smooth
  boundary point and discharging its winding number via the matching FTC
  provider.
- **How**: Establishes `√3/2 < H` via `nlinarith` using `Real.sq_sqrt`. Then
  calls `mkFDWindingDataFull` and feeds the boundary classifier
  `smooth_boundary_classification`, splitting into the vertical-edge case
  (`|re| = 1/2`, `‖z‖ > 1`) and the arc case (`‖z‖ = 1`, `|re| < 1/2`). In
  the edge case, derives `√3/2 < z.im` from `re² = 1/4` and `‖z‖ > 1`
  (`nlinarith` with `Complex.normSq_apply`, `Complex.normSq_eq_norm_sq`,
  `Real.sq_sqrt 3`), then `abs_eq` splits `|re| = 1/2` into `re = 1/2` or
  `re = -1/2`, dispatching to `smoothBoundaryData_seg1_of_ftcHyp` /
  `smoothBoundaryData_seg4_of_ftcHyp` whose `.hasWindingNumber` projection
  yields the goal. In the arc case, calls `arg_mem_arc_range`, rewrites
  `z = exp(i arg z)` via `eq_exp_arg_mul_I`, and applies
  `smoothBoundaryData_arc_of_ftcHyp`.
- **Hypotheses**: `1 < H`; base data `D`; three FTC providers indexed by
  the corresponding boundary parametrisation parameters
  (`seg1T₀`/`seg4T₀`/`arcT₀`, `linDelta`/`arcsinDelta`,
  `seg1Threshold`/`seg4Threshold`/`arcThreshold`, expected winding
  `-(π·I)`).
- **Uses-from-project**:
  - `FDWindingData`, `FDWindingDataFull`, `mkFDWindingDataFull`, the field
    `D.boundary`, `D.boundary_eq` (from the base data module re-exported
    by the seg/arc proof imports).
  - `ArcFTCHyp`, `seg1T₀`, `seg4T₀`, `arcT₀`, `linDelta`, `arcsinDelta`,
    `seg1Speed`, `seg1Threshold`, `seg4Threshold`, `arcThreshold` from
    the boundary-winding modules.
  - `smoothBoundaryData_seg1_of_ftcHyp`, `smoothBoundaryData_seg4_of_ftcHyp`,
    `smoothBoundaryData_arc_of_ftcHyp` (provided by the three imports).
  - `smooth_boundary_classification` (boundary point trichotomy).
  - Local helpers `arg_mem_arc_range`, `eq_exp_arg_mul_I`.
- **Used by**: Top-level fundamental-domain winding-number assembly that
  needs the full `FDWindingDataFull H` to feed into the valence-formula
  pipeline.
- **Visibility**: public `def`; root namespace; `noncomputable section`.
- **Lines**: 70-107.
- **Notes**: ~38-line proof; the key dispatch is `smooth_boundary_classification`
  splitting into two cases plus `abs_eq` for `|re| = 1/2`.

## File Summary
Three public declarations in the root namespace, all under
`noncomputable section`: two helpers (`arg_mem_arc_range`, `eq_exp_arg_mul_I`)
that convert between arc parameter and complex point on the unit circle,
plus the main assembler `mkFDWindingDataFull_of_ftcProviders` that combines
a base `FDWindingData H` with three per-segment FTC providers (seg1, seg4,
arc) into a `FDWindingDataFull H`. The assembler uses
`smooth_boundary_classification` to split smooth boundary points into the
two regimes (vertical edges with `|re| = 1/2`, or arc with `‖z‖ = 1`).
No `sorry`. Depends on the three boundary-winding proof modules and the
base FD winding-data infrastructure.
