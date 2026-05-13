# WindingInteger.lean Inventory

### `theorem exists_uniform_modulus_avoiding`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc (0:ℝ) 1)) (h_avoid : ∀ t ∈ Icc (0:ℝ) 1, γ t ≠ w) : ∃ δ' > 0, ∃ ρ > 0, (∀ t ∈ Icc (0:ℝ) 1, ρ ≤ ‖γ t − w‖) ∧ ∀ t s, t ∈ Icc 0 1 → s ∈ Icc 0 1 → |t−s| < δ' → ‖γ t − γ s‖ < ρ/2`
- **What**: For `γ` continuous on `[0,1]` avoiding `w`, there exists a uniform mesh `δ'` and lower bound `ρ` such that on any sub-interval of length `<δ'`, `γ` varies by less than `ρ/2`.
- **How**: Two-step proof (>10 lines): compactness gives `ρ := Metric.infDist w (γ''[0,1]) > 0` via `IsClosed.notMem_iff_infDist_pos`; uniform continuity of `γ` on compact via `IsCompact.uniformContinuousOn_of_continuous` gives `δ'` for variation `< ρ/2`.
- **Hypotheses**: `γ` continuous on `[0,1]`, avoids point `w`.
- **Uses from project**: []
- **Used by**: `exists_continuous_arg_lift_of_avoids`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: public
- **Lines**: 47–77
- **Notes**: >10 lines (~30 line proof body).

### `theorem mem_slitPlane_of_ball_one`
- **Type**: `(z : ℂ) (hz : ‖z − 1‖ < 1/2) : z ∈ Complex.slitPlane`
- **What**: Open ball of radius `1/2` centered at `1` lies inside `Complex.slitPlane` (avoids the negative real axis).
- **How**: Uses `Complex.abs_re_le_norm` + `abs_sub_lt_iff` to get `z.re > 1/2 > 0`, so `z` is in the right half-plane, hence in `slitPlane`.
- **Hypotheses**: `‖z − 1‖ < 1/2`.
- **Uses from project**: []
- **Used by**: `segRatio_mem_slitPlane`
- **Visibility**: public
- **Lines**: 82–91

### `def segClamp`
- **Type**: `(s_j s_jp1 t : ℝ) : ℝ := max s_j (min t s_jp1)`
- **What**: Clamps `t` to the interval `[s_j, s_{j+1}]`.
- **How**: Composition of `max` and `min`.
- **Hypotheses**: none.
- **Uses from project**: []
- **Used by**: `segClamp_continuous`, `segClamp_mem_Icc`, `segClamp_eq_left`, `segClamp_eq_self`, `segClamp_eq_right`, `segRatio`, `segRatio_mem_ball_one`, `continuousOn_segRatio`
- **Visibility**: public
- **Lines**: 103

### `theorem segClamp_continuous`
- **Type**: `(s_j s_jp1 : ℝ) : Continuous (segClamp s_j s_jp1)`
- **What**: `segClamp s_j s_jp1` is continuous in `t`.
- **How**: `continuous_const.max (continuous_id.min continuous_const)`.
- **Hypotheses**: none.
- **Uses from project**: [`segClamp`]
- **Used by**: `continuousOn_segRatio`
- **Visibility**: public
- **Lines**: 105–107

### `theorem segClamp_mem_Icc`
- **Type**: `(s_j s_jp1 t : ℝ) (h : s_j ≤ s_jp1) : segClamp s_j s_jp1 t ∈ Icc s_j s_jp1`
- **What**: `segClamp s_j s_jp1 t` lies in `[s_j, s_{j+1}]`.
- **How**: Case split on `t ≤ s_jp1` versus its negation; simp with `min_eq_left/right`.
- **Hypotheses**: `s_j ≤ s_jp1`.
- **Uses from project**: [`segClamp`]
- **Used by**: `segRatio_mem_ball_one`, `continuousOn_segRatio`
- **Visibility**: public
- **Lines**: 109–117

### `theorem segClamp_eq_left`
- **Type**: `{s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : t ≤ s_j) : segClamp s_j s_jp1 t = s_j`
- **What**: When `t ≤ s_j`, the clamp is `s_j`.
- **How**: Unfold and apply `min_eq_left (ht.trans h)`, `max_eq_left ht`.
- **Hypotheses**: `s_j ≤ s_jp1`, `t ≤ s_j`.
- **Uses from project**: [`segClamp`]
- **Used by**: `segRatio_eq_one_of_le`
- **Visibility**: public
- **Lines**: 119–122

### `theorem segClamp_eq_self`
- **Type**: `{s_j s_jp1 t : ℝ} (ht_lo : s_j ≤ t) (ht_hi : t ≤ s_jp1) : segClamp s_j s_jp1 t = t`
- **What**: When `t ∈ [s_j, s_{j+1}]`, the clamp equals `t`.
- **How**: Unfold and apply `min_eq_left ht_hi`, `max_eq_right ht_lo`.
- **Hypotheses**: `s_j ≤ t ≤ s_jp1`.
- **Uses from project**: [`segClamp`]
- **Used by**: `segRatio_eq_self_div`
- **Visibility**: public
- **Lines**: 124–127

### `theorem segClamp_eq_right`
- **Type**: `{s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) : segClamp s_j s_jp1 t = s_jp1`
- **What**: When `t ≥ s_{j+1}`, the clamp is `s_{j+1}`.
- **How**: Unfold and apply `min_eq_right ht`, `max_eq_right h`.
- **Hypotheses**: `s_j ≤ s_jp1`, `s_jp1 ≤ t`.
- **Uses from project**: [`segClamp`]
- **Used by**: `segRatio_eq_full`
- **Visibility**: public
- **Lines**: 129–132

### `def segRatio`
- **Type**: `(γ : ℝ → ℂ) (w : ℂ) (s_j s_jp1 t : ℝ) : ℂ := (γ (segClamp s_j s_jp1 t) − w) / (γ s_j − w)`
- **What**: Segment ratio `(γ(clamp t) − w) / (γ s_j − w)` used in telescoping product.
- **How**: noncomputable definition.
- **Hypotheses**: none.
- **Uses from project**: [`segClamp`]
- **Used by**: `segRatio_eq_one_of_le`, `segRatio_eq_self_div`, `segRatio_eq_full`, `segRatio_mem_ball_one`, `continuousOn_segRatio`, `segRatio_mem_slitPlane`, `prod_segRatio_telescope`, `continuousOn_im_log_segRatio`, `exists_continuous_arg_lift_of_avoids`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: public
- **Lines**: 135–136

### `theorem segRatio_eq_one_of_le`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : t ≤ s_j) (h_ne : γ s_j − w ≠ 0) : segRatio γ w s_j s_jp1 t = 1`
- **What**: When `t ≤ s_j`, `segRatio` equals `1`.
- **How**: Unfold + `segClamp_eq_left` + `div_self h_ne`.
- **Hypotheses**: `s_j ≤ s_jp1`, `t ≤ s_j`, `γ s_j ≠ w`.
- **Uses from project**: [`segRatio`, `segClamp_eq_left`]
- **Used by**: `prod_segRatio_telescope`
- **Visibility**: public
- **Lines**: 138–142

### `theorem segRatio_eq_self_div`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ} (ht_lo : s_j ≤ t) (ht_hi : t ≤ s_jp1) : segRatio γ w s_j s_jp1 t = (γ t − w) / (γ s_j − w)`
- **What**: On the segment, `segRatio` is `(γ t − w)/(γ s_j − w)`.
- **How**: Unfold + `segClamp_eq_self ht_lo ht_hi`.
- **Hypotheses**: `s_j ≤ t ≤ s_jp1`.
- **Uses from project**: [`segRatio`, `segClamp_eq_self`]
- **Used by**: `prod_segRatio_telescope`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: public
- **Lines**: 144–148

### `theorem segRatio_eq_full`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} {s_j s_jp1 t : ℝ} (h : s_j ≤ s_jp1) (ht : s_jp1 ≤ t) : segRatio γ w s_j s_jp1 t = (γ s_jp1 − w) / (γ s_j − w)`
- **What**: When `t ≥ s_{j+1}`, `segRatio` equals the full-segment ratio.
- **How**: Unfold + `segClamp_eq_right h ht`.
- **Hypotheses**: `s_j ≤ s_jp1 ≤ t`.
- **Uses from project**: [`segRatio`, `segClamp_eq_right`]
- **Used by**: `prod_segRatio_telescope`
- **Visibility**: public
- **Lines**: 150–154

### `theorem segRatio_mem_ball_one`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ) (h_dist_lb : ∀ t ∈ Icc 0 1, ρ ≤ ‖γ t − w‖) (h_unif : ∀ t s, … |t−s| < δ' → ‖γ t − γ s‖ < ρ/2) {s_j s_jp1} (hsj : s_j ∈ Icc 0 1) (hsjp1 : s_jp1 ∈ Icc 0 1) (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 − s_j < δ') (t : ℝ) : ‖segRatio γ w s_j s_jp1 t − 1‖ < 1/2`
- **What**: For partition with mesh `<δ'`, each `segRatio` lies in `ball(1, 1/2)`.
- **How**: Reduces `segRatio − 1` to `(γ(clamp t) − γ s_j)/(γ s_j − w)`; uses `h_dist_lb` and `h_unif` (via `segClamp_mem_Icc`) to bound numerator by `ρ/2` and denominator from below by `ρ`; calc chain.
- **Hypotheses**: positive `ρ`, lower bound on `‖γ − w‖`, uniform modulus.
- **Uses from project**: [`segRatio`, `segClamp_mem_Icc`]
- **Used by**: `segRatio_mem_slitPlane`
- **Visibility**: public
- **Lines**: 158–187
- **Notes**: >10 lines proof.

### `theorem continuousOn_segRatio`
- **Type**: `{γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) {w : ℂ} {s_j s_jp1 : ℝ} (hsj : s_j ∈ Icc 0 1) (hsjp1 : s_jp1 ∈ Icc 0 1) (h_le : s_j ≤ s_jp1) : ContinuousOn (fun t => segRatio γ w s_j s_jp1 t) (Icc 0 1)`
- **What**: `t ↦ segRatio γ w s_j s_jp1 t` is continuous on `[0,1]`.
- **How**: `ContinuousOn.div_const` of `γ ∘ segClamp − w`; uses `segClamp_continuous` and `segClamp_mem_Icc`.
- **Hypotheses**: `γ` continuous on `[0,1]`, endpoints in `[0,1]`, `s_j ≤ s_jp1`.
- **Uses from project**: [`segRatio`, `segClamp_continuous`, `segClamp_mem_Icc`]
- **Used by**: `continuousOn_im_log_segRatio`
- **Visibility**: public
- **Lines**: 190–200

### `theorem segRatio_mem_slitPlane`
- **Type**: same hypothesis list as `segRatio_mem_ball_one`, conclusion: `segRatio γ w s_j s_jp1 t ∈ Complex.slitPlane`
- **What**: With small mesh, the segment ratio lies in the slit plane.
- **How**: `mem_slitPlane_of_ball_one` applied to `segRatio_mem_ball_one`.
- **Hypotheses**: same as `segRatio_mem_ball_one`.
- **Uses from project**: [`mem_slitPlane_of_ball_one`, `segRatio_mem_ball_one`, `segRatio`]
- **Used by**: `continuousOn_im_log_segRatio`, `exists_continuous_arg_lift_of_avoids`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: public
- **Lines**: 203–212

### `lemma prod_range_div_complex`
- **Type**: `(a : ℕ → ℂ) (k : ℕ) (ha : ∀ j ≤ k, a j ≠ 0) : ∏ j ∈ Finset.range k, (a (j+1)/a j) = a k / a 0`
- **What**: Standard telescoping product in `ℂ`.
- **How**: Induction on `k`; base by `div_self`; step uses `Finset.prod_range_succ`, `div_mul_div_comm`, `mul_div_mul_right`.
- **Hypotheses**: `a j ≠ 0` for `j ≤ k`.
- **Uses from project**: []
- **Used by**: `prod_segRatio_telescope`
- **Visibility**: private
- **Lines**: 218–226

### `theorem prod_segRatio_telescope`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} {N : ℕ} {s : ℕ → ℝ} (hs_zero : s 0 = 0) (hs_mono : Monotone s) (h_avoid : ∀ j ≤ N, γ (s j) − w ≠ 0) {t : ℝ} {k : ℕ} (hk : k < N) (hk_lo : s k ≤ t) (hk_hi : t ≤ s (k+1)) : ∏ j ∈ Finset.range N, segRatio γ w (s j) (s (j+1)) t = (γ t − w) / (γ 0 − w)`
- **What**: Telescoping product of `segRatio` over the partition collapses to `(γ t − w)/(γ 0 − w)`.
- **How**: Split `range N` into `range (k+1) ∪ Ico (k+1) N` via `Finset.prod_Ico_consecutive`; tail equals `1` by `segRatio_eq_one_of_le`; range `k` uses `segRatio_eq_full` to get full ratios; the middle index `k` uses `segRatio_eq_self_div`; finally apply `prod_range_div_complex`. Multi-step `rw` chain (>10 lines).
- **Hypotheses**: monotone partition starting at `0`, avoidance at partition nodes, segment containing `t`.
- **Uses from project**: [`segRatio`, `segRatio_eq_one_of_le`, `segRatio_eq_full`, `segRatio_eq_self_div`, `prod_range_div_complex`]
- **Used by**: `exists_continuous_arg_lift_of_avoids`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: public
- **Lines**: 235–269
- **Notes**: >30 lines.

### `theorem continuousOn_im_log_segRatio`
- **Type**: `{γ : ℝ → ℂ} (hγ : ContinuousOn γ (Icc 0 1)) {w : ℂ} {δ' ρ : ℝ} (hρ_pos : 0 < ρ) (h_dist_lb : ∀ t ∈ Icc 0 1, ρ ≤ ‖γ t − w‖) (h_unif …) {s_j s_jp1} (hsj : s_j ∈ Icc 0 1) (hsjp1 : s_jp1 ∈ Icc 0 1) (h_le : s_j ≤ s_jp1) (h_mesh : s_jp1 − s_j < δ') : ContinuousOn (fun t => (Complex.log (segRatio γ w s_j s_jp1 t)).im) (Icc 0 1)`
- **What**: Each telescoping summand `Im(log(segRatio))` is continuous on `[0,1]`.
- **How**: `Complex.continuous_im.comp_continuousOn` of `continuousOn_segRatio … .clog` (using `segRatio_mem_slitPlane`).
- **Hypotheses**: as in `segRatio_mem_slitPlane`.
- **Uses from project**: [`segRatio`, `continuousOn_segRatio`, `segRatio_mem_slitPlane`]
- **Used by**: `exists_continuous_arg_lift_of_avoids`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: public
- **Lines**: 274–285

### `lemma exp_I_log_im_eq_div_norm`
- **Type**: `{z : ℂ} (hz : z ≠ 0) : Complex.exp (Complex.I * (Complex.log z).im) = z / ↑‖z‖`
- **What**: For nonzero `z`, `exp(i·Im(log z)) = z / ‖z‖` (the unit-norm phase).
- **How**: Split `i·Im(log z) = log z − Re(log z)`; apply `Complex.exp_sub`, `Complex.exp_log hz`, `Complex.log_re`, `Real.exp_log` (on `‖z‖ > 0`).
- **Hypotheses**: `z ≠ 0`.
- **Uses from project**: []
- **Used by**: `exists_continuous_arg_lift_of_avoids`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: private
- **Lines**: 290–298

### `lemma partition_segment_exists`
- **Type**: `{N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Icc 0 1) : ∃ k : ℕ, k < N ∧ (k:ℝ)/N ≤ t ∧ t ≤ ((k+1:ℕ):ℝ)/N`
- **What**: For the uniform partition `s_j = j/N`, every `t ∈ [0,1]` lies in some segment `[s_k, s_{k+1}]`.
- **How**: Case split on `t < 1` vs `t = 1`; use `⌊t·N⌋₊` in the first case (`Nat.floor_le`, `Nat.lt_floor_add_one`) and `N − 1` in the second.
- **Hypotheses**: positive `N`, `t ∈ [0,1]`.
- **Uses from project**: []
- **Used by**: `exists_continuous_arg_lift_of_avoids`, `exists_continuous_arg_lift_with_partition`
- **Visibility**: private
- **Lines**: 304–330
- **Notes**: >10 lines.

### `theorem exists_continuous_arg_lift_of_avoids`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (h_avoid : ∀ t ∈ Icc 0 1, γ t ≠ w) : ∃ θ : ℝ → ℝ, ContinuousOn θ (Icc 0 1) ∧ ∀ t ∈ Icc 0 1, γ t − w = (‖γ t − w‖ : ℂ) * Complex.exp (Complex.I * θ t)`
- **What**: Existence of a continuous argument lift `θ` for a curve `γ` avoiding `w`.
- **How**: (>30 lines) Step 1 `exists_uniform_modulus_avoiding`; Step 2 pick `N` with `1/N < δ'` (`exists_nat_gt`); Step 3 uniform partition `s_j = j/N`; Step 4 define `θ t = arg(γ 0 − w) + ∑_j Im(log segRatio_j t)`. Continuity from `continuousOn_im_log_segRatio`. Lift property via `prod_segRatio_telescope` plus splitting `exp(I·θ)` as a product, using `exp_I_log_im_eq_div_norm` and `partition_segment_exists`.
- **Hypotheses**: `γ` continuous on `[0,1]`, never `= w`.
- **Uses from project**: [`exists_uniform_modulus_avoiding`, `segRatio`, `segRatio_mem_slitPlane`, `continuousOn_im_log_segRatio`, `prod_segRatio_telescope`, `partition_segment_exists`, `exp_I_log_im_eq_div_norm`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 337–453
- **Notes**: >100 lines.

### `theorem exists_continuous_arg_lift_with_partition`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} (hγ : ContinuousOn γ (Icc 0 1)) (h_avoid : ∀ t ∈ Icc 0 1, γ t ≠ w) : ∃ (N : ℕ) (s : ℕ → ℝ), 0 < N ∧ s 0 = 0 ∧ s N = 1 ∧ Monotone s ∧ (∀ j ≤ N, s j ∈ Icc 0 1) ∧ (∀ j ≤ N, γ (s j) − w ≠ 0) ∧ (∀ j < N, ∀ t ∈ Icc (s j) (s (j+1)), (γ t − w)/(γ (s j) − w) ∈ slitPlane) ∧ ContinuousOn (arg-lift formula) (Icc 0 1) ∧ (lift property)`
- **What**: Strengthened W-1: continuous argument lift packaged with the underlying partition `s : ℕ → ℝ` and per-segment slit-plane condition; needed for FTC-based winding number.
- **How**: Same scaffolding as `exists_continuous_arg_lift_of_avoids` but additionally returns `N, s` and the per-segment slit-plane claim `h_slit` via `segRatio_mem_slitPlane` rewritten with `segRatio_eq_self_div`. Uses `exists_uniform_modulus_avoiding`, `exists_nat_gt`, `prod_segRatio_telescope`, `partition_segment_exists`, `exp_I_log_im_eq_div_norm`.
- **Hypotheses**: same as the simpler version.
- **Uses from project**: [`exists_uniform_modulus_avoiding`, `segRatio`, `segRatio_eq_self_div`, `segRatio_mem_slitPlane`, `continuousOn_im_log_segRatio`, `prod_segRatio_telescope`, `partition_segment_exists`, `exp_I_log_im_eq_div_norm`]
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 461–590
- **Notes**: >100 lines.

### `theorem segment_log_FTC`
- **Type**: `{γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} (hab : a ≤ b) {P : Set ℝ} (hP_count : P.Countable) (hγ_cont : ContinuousOn γ (Icc a b)) (hγ_diff : ∀ t ∈ Ioo a b \ P, HasDerivAt γ (deriv γ t) t) (h_a_ne : γ a − w ≠ 0) (h_slit : ∀ t ∈ Icc a b, (γ t − w)/(γ a − w) ∈ slitPlane) (h_int : IntervalIntegrable (deriv γ / (γ − w)) volume a b) : ∫ t in a..b, deriv γ t / (γ t − w) = Complex.log ((γ b − w)/(γ a − w))`
- **What**: Per-segment FTC: integral of `γ'/(γ − w)` equals `log((γ b − w)/(γ a − w))` when ratios lie in the slit plane.
- **How**: Define `F t := Complex.log ((γ t − w)/(γ a − w))`. `F` is continuous via `ContinuousOn.clog`; derivative `F' t = γ'(t)/(γ t − w)` via `HasDerivAt.div_const … |>.clog_real`. Apply `MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le`. Final `log 1 = 0` cancels the `F(a)` term.
- **Hypotheses**: continuity of `γ`, differentiability off countable set, slit-plane ratio condition, integrability of `γ'/(γ − w)`, `γ a ≠ w`.
- **Uses from project**: []
- **Used by**: unused in file
- **Visibility**: public
- **Lines**: 598–631
- **Notes**: >10 lines.

## File Summary
WindingInteger.lean develops a continuous argument lift `θ` for a curve `γ : [0,1] → ℂ` avoiding `w`, plus an FTC integral formula for `γ'/(γ − w)`. The structure is: (i) uniform modulus `exists_uniform_modulus_avoiding`, (ii) `segClamp`/`segRatio` helpers landing in `ball(1, 1/2) ⊆ slitPlane`, (iii) `prod_segRatio_telescope` collapsing the telescoping product, (iv) the two main theorems `exists_continuous_arg_lift_of_avoids` and `exists_continuous_arg_lift_with_partition`, and (v) `segment_log_FTC` evaluating the log-derivative integral. The file is self-contained (no project imports — only mathlib). 23 declarations total. 2 private lemmas. No `sorry`, `axiom`, or `set_option`.

## N1 = 23
