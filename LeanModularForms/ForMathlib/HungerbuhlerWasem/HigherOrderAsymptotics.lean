/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanModularForms.ForMathlib.FlatChordBound
public import LeanModularForms.ForMathlib.FlatnessConditions

/-!
# F-diff asymptotic chain (T-SC-00a)

For a curve `γ` flat of order `n` at `t₀` with `γ(t₀) = s`, the antiderivative
`F(z) = -1/[(k-1)(z-s)^{k-1}]` of the higher-order pole integrand satisfies
`F(γ(t)) - F(tangent target) → 0` as `t → t₀` from either side, provided
`n ≥ k ≥ 2`. Combined with FTC on each smooth piece, this gives the
parameter-excised CPV `→ 0` result needed by the sector cancellation argument
of T-SC-01.

This file restores the F-diff asymptotic subset of the deleted
`HigherOrderCancel.lean` (git ref `79bcaa5^`, lines 477-1300+) into
`namespace HungerbuhlerWasem`. Only the asymptotic / FTC chain leading to the
five headline theorems is restored; the upstream `HasCauchyPVOn`-based
cancellation API (which depended on the also-deleted `HigherOrderAssembly.lean`)
is intentionally omitted as it isn't needed for T-SC-01.

## Headline theorems

* `chord_to_tangent_isLittleO` — chord-to-tangent-target o-bound, parametrised
  over the filter and the tangent direction `T` (`T = L` on the right,
  `T = -L` on the left).
* `F_diff_at_tangent_target_tendsto_zero` — parametrised core: F-diff vs
  tangent target → 0 under the chord o-bound and `n ≥ k ≥ 2`.
* `F_diff_at_tangent_target_tendsto_zero_right` / `_left` — the one-sided
  instantiations consumed by the sector cancellation argument.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Classical Real Interval

@[expose] public section

noncomputable section

namespace HungerbuhlerWasem

/-- Antiderivative of `1/(z-s)^k` as a function `ℂ → ℂ` (`k ≥ 2`): the function
`F(z) = -1/[(k-1)(z-s)^{k-1}]` has complex derivative `1/(z-s)^k` at any `z ≠ s`. -/
theorem hasDerivAt_antiderivative_pow_inv_complex
    {s : ℂ} {k : ℕ} (hk : 2 ≤ k) {z : ℂ} (hz : z ≠ s) :
    HasDerivAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
      (1 / (z - s) ^ k) z := by
  have h_pow : HasDerivAt (fun w : ℂ => (w - s) ^ (k - 1))
      (↑(k - 1) * (z - s) ^ (k - 1 - 1) * 1) z :=
    ((hasDerivAt_id z).sub_const s).pow (k - 1)
  rw [show k - 1 - 1 = k - 2 from by lia] at h_pow
  have h_const := (h_pow.inv (pow_ne_zero _ (sub_ne_zero.mpr hz))).const_mul
    (-(↑(k - 1) : ℂ)⁻¹)
  convert h_const using 1
  have hk1 : (↑(k - 1) : ℂ) ≠ 0 := by exact_mod_cast (by lia : 0 < k - 1).ne'
  have h_pow_k2_ne : (z - s) ^ (k - 2) ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hz)
  have h_pow2 : ((z - s) ^ (k - 1)) ^ 2 = (z - s) ^ k * (z - s) ^ (k - 2) := by
    rw [← pow_mul, ← pow_add]; congr 1; lia
  rw [h_pow2]
  field_simp

/-- When the line segment from `z₁` to `z₂` stays at distance `≥ ε` from `s`, the
antiderivative difference satisfies `‖F(z₂) − F(z₁)‖ ≤ ‖z₂ − z₁‖ / ε^k`, where
`F(z) = -1/[(k-1)(z-s)^{k-1}]`. -/
theorem norm_F_diff_le_segment_bound
    {z₁ z₂ s : ℂ} {k : ℕ} {ε : ℝ} (hk : 2 ≤ k) (hε : 0 < ε)
    (h_seg_avoids : ∀ z ∈ segment ℝ z₁ z₂, ε ≤ ‖z - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((z₂ - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((z₁ - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / ε ^ k) * ‖z₂ - z₁‖ := by
  have h_deriv : ∀ z ∈ segment ℝ z₁ z₂,
      HasDerivWithinAt (fun w => -(↑(k - 1) : ℂ)⁻¹ * ((w - s) ^ (k - 1))⁻¹)
        (1 / (z - s) ^ k) (segment ℝ z₁ z₂) z := by
    intro z hz
    have h_ne : z ≠ s := fun heq => by
      have := h_seg_avoids z hz; rw [heq, sub_self, norm_zero] at this; linarith
    exact (hasDerivAt_antiderivative_pow_inv_complex hk h_ne).hasDerivWithinAt
  have h_bound : ∀ z ∈ segment ℝ z₁ z₂, ‖1 / (z - s) ^ k‖ ≤ 1 / ε ^ k := by
    intro z hz
    rw [norm_div, norm_one, norm_pow]
    exact div_le_div_of_nonneg_left zero_le_one (pow_pos hε k)
      (pow_le_pow_left₀ hε.le (h_seg_avoids z hz) k)
  exact (convex_segment z₁ z₂).norm_image_sub_le_of_norm_hasDerivWithin_le h_deriv h_bound
    (left_mem_segment _ _ _) (right_mem_segment _ _ _)

/-- **Eventual hemisphere condition.** If `T` is the outgoing tangent direction
on `u` — i.e. `(t - t₀) • L = |t - t₀| • T` for `t ∈ u` and `‖T‖ = ‖L‖` — then
for `t` close to `t₀` within `u`, the chord `γ(t) − s` lies in the `+T`
hemisphere (`Re((γ(t) − s) · conj T) ≥ 0`). On `Ioi t₀` this holds with
`T = L`, on `Iio t₀` with `T = -L`. -/
theorem eventually_re_smul_conj_nonneg
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {u : Set ℝ} {T : ℂ} (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_s : γ t₀ = s)
    (hT : ∀ t ∈ u, (t - t₀) • L = |t - t₀| • T) (hTL : ‖T‖ = ‖L‖) :
    ∀ᶠ t in 𝓝[u] t₀, 0 ≤ ((γ t - s) * starRingEnd ℂ T).re := by
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  filter_upwards [h_deriv.isLittleO.bound (by linarith : (0 : ℝ) < ‖L‖ / 2),
    self_mem_nhdsWithin] with t h_b ht
  rw [Real.norm_eq_abs] at h_b
  rw [show (γ t - s) = |t - t₀| • T + (γ t - γ t₀ - (t - t₀) • L) by
      rw [← hT t ht, h_s]; ring,
    add_mul, Complex.add_re]
  have h1 : ((|t - t₀| : ℝ) • T * starRingEnd ℂ T).re = |t - t₀| * ‖T‖ ^ 2 := by
    rw [Complex.real_smul, mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [h1, hTL]
  have h2 : -(‖L‖ / 2 * |t - t₀|) * ‖L‖ ≤
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ T).re := by
    have habs := Complex.abs_re_le_norm
      ((γ t - γ t₀ - (t - t₀) • L) * starRingEnd ℂ T)
    rw [norm_mul, Complex.norm_conj, hTL] at habs
    nlinarith [abs_le.mp (habs.trans (mul_le_mul_of_nonneg_right h_b (norm_nonneg L)))]
  nlinarith [abs_nonneg (t - t₀), sq_nonneg ‖L‖]

/-- With one-sided derivative `L ≠ 0` at `t₀` within `u ∌ t₀`, the curve cannot
stay at `s = γ(t₀)` near `t₀` within `u`. -/
theorem eventually_ne
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {u : Set ℝ} (hu : t₀ ∉ u) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L u t₀) (h_s : γ t₀ = s) :
    ∀ᶠ t in 𝓝[u] t₀, γ t ≠ s := by
  filter_upwards [((hasDerivWithinAt_iff_tendsto_slope' hu).mp h_deriv).eventually_ne hL]
    with t ht h_eq
  exact ht (by rw [slope_def_module, h_eq, h_s, sub_self, smul_zero])

/-- **Chord-to-tangent o-bound (parametrised core).** Combining the eventual
hemisphere/non-vanishing conditions with the deviation o-bound, the chord
`‖γ(t) − s − (‖γ(t)−s‖/‖T‖)·T‖` is `o(‖γ(t)−s‖^n)` along `l`. The right side
instantiates `T = L`, `l = 𝓝[>] t₀`; the left side `T = -L`, `l = 𝓝[<] t₀`. -/
theorem chord_to_tangent_isLittleO
    {γ : ℝ → ℂ} {s : ℂ} {l : Filter ℝ} {T : ℂ} {n : ℕ} (hT : T ≠ 0)
    (h_re : ∀ᶠ t in l, 0 ≤ ((γ t - s) * starRingEnd ℂ T).re)
    (h_ne : ∀ᶠ t in l, γ t ≠ s)
    (h_dev : (fun t => ‖tangentDeviation (γ t - s) T‖) =o[l]
      fun t => ‖γ t - s‖ ^ n) :
    (fun t => ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖) =o[l]
      (fun t => ‖γ t - s‖ ^ n) := by
  have h_eventually_bound : ∀ᶠ t in l,
      ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ ≤ 3 * ‖tangentDeviation (γ t - s) T‖ := by
    filter_upwards [h_re, h_ne] with t h_pos h_ne
    have hw_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h_ne)
    have h_chord := LeanModularForms.norm_chord_to_tangent_target_le hT hw_pos h_pos
    have h_dev_le : ‖tangentDeviation (γ t - s) T‖ ≤ 2 * ‖γ t - s‖ :=
      norm_tangentDeviation_le _ _ hT
    have h_div_bound : ‖tangentDeviation (γ t - s) T‖ ^ 2 / ‖γ t - s‖ ≤
        2 * ‖tangentDeviation (γ t - s) T‖ := by
      rw [pow_two, mul_div_assoc]
      have hd_div : ‖tangentDeviation (γ t - s) T‖ / ‖γ t - s‖ ≤ 2 := by
        rw [div_le_iff₀ hw_pos]; linarith
      nlinarith [norm_nonneg (tangentDeviation (γ t - s) T)]
    linarith [h_chord]
  refine Asymptotics.IsBigO.trans_isLittleO ?_ h_dev
  refine Asymptotics.IsBigO.of_bound 3 ?_
  filter_upwards [h_eventually_bound] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _)]
  exact ht

/-- If `z₁, z₂` are equidistant from `s` (distance `d`), then any point `z` on the
segment from `z₁` to `z₂` satisfies `‖z − s‖² ≥ d² − ‖z₁ − z₂‖²/4`. -/
theorem norm_sq_segment_to_pole_lower_bound
    {z₁ z₂ s : ℂ} {d : ℝ}
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d ^ 2 - ‖z₁ - z₂‖ ^ 2 / 4 ≤ ‖z - s‖ ^ 2 := by
  obtain ⟨α, β, hα, hβ, h_sum, rfl⟩ := hz
  rw [show α • z₁ + β • z₂ - s = α • (z₁ - s) + β • (z₂ - s) by
    rw [show β = 1 - α by linarith]; module]
  have h_expand : ‖α • (z₁ - s) + β • (z₂ - s)‖ ^ 2 =
      α ^ 2 * ‖z₁ - s‖ ^ 2 +
        2 * α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re +
        β ^ 2 * ‖z₂ - s‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.real_smul]
    rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal,
      show (((α : ℂ) * (z₁ - s)) * starRingEnd ℂ ((β : ℂ) * (z₂ - s))) =
          ((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s)) by
        rw [map_mul, Complex.conj_ofReal]; push_cast; ring,
      show (((α * β : ℝ) : ℂ) * ((z₁ - s) * starRingEnd ℂ (z₂ - s))).re =
          α * β * ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re by
        rw [Complex.mul_re]; simp]
    ring
  have h_cross : ((z₁ - s) * starRingEnd ℂ (z₂ - s)).re =
      (‖z₁ - s‖ ^ 2 + ‖z₂ - s‖ ^ 2 - ‖z₁ - z₂‖ ^ 2) / 2 := by
    have h_ns := Complex.normSq_sub (z₁ - s) (z₂ - s)
    rw [← Complex.sq_norm, ← Complex.sq_norm, ← Complex.sq_norm,
      show (z₁ - s) - (z₂ - s) = z₁ - z₂ by ring] at h_ns
    linarith
  rw [h_expand, h_cross, h₁, h₂]
  have h_ab_le : α * β ≤ 1 / 4 := by nlinarith [sq_nonneg (α - β)]
  have h_quad : α ^ 2 + 2 * α * β + β ^ 2 = 1 := by nlinarith [h_sum]
  nlinarith [h_quad, h_ab_le, sq_nonneg (‖z₁ - z₂‖)]

/-- When the chord between two equidistant points is at most `d`, the segment from
`z₁` to `z₂` stays at distance `≥ d/2` from `s`. -/
theorem norm_segment_to_pole_lower_bound_half
    {z₁ z₂ s : ℂ} {d : ℝ} (_hd_pos : 0 < d)
    (h₁ : ‖z₁ - s‖ = d) (h₂ : ‖z₂ - s‖ = d) (h_chord : ‖z₁ - z₂‖ ≤ d)
    {z : ℂ} (hz : z ∈ segment ℝ z₁ z₂) :
    d / 2 ≤ ‖z - s‖ := by
  have h_le_sq : (d / 2) ^ 2 ≤ ‖z - s‖ ^ 2 := by
    nlinarith [norm_sq_segment_to_pole_lower_bound h₁ h₂ hz,
      mul_self_le_mul_self (norm_nonneg _) h_chord]
  have := abs_le_of_sq_le_sq' h_le_sq (norm_nonneg _)
  linarith [this.2, abs_of_pos (by linarith : 0 < d / 2)]

/-- For `γ(t) ≠ s` and chord-to-target bounded by `‖γ(t) - s‖`, the antiderivative
difference between `γ(t)` and the tangent target `s + (‖γ(t)-s‖/‖L‖)·L` is bounded by
`(1/(‖γ(t)−s‖/2)^k) · chord(t)`. -/
theorem norm_F_diff_at_tangent_target_le
    {γ : ℝ → ℂ} {t : ℝ} {s L : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hL : L ≠ 0) (hw_ne : γ t ≠ s)
    (h_chord_le : ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ ≤ ‖γ t - s‖) :
    ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖ ≤
      (1 / (‖γ t - s‖ / 2) ^ k) * ‖γ t - (s + (‖γ t - s‖ / ‖L‖ : ℝ) • L)‖ := by
  have hd_pos : 0 < ‖γ t - s‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hw_ne)
  have hL_pos : 0 < ‖L‖ := norm_pos_iff.mpr hL
  set d := ‖γ t - s‖
  set tgt := s + (d / ‖L‖ : ℝ) • L with htgt_def
  have h_tgt : ‖tgt - s‖ = d := by
    rw [show tgt - s = (d / ‖L‖ : ℝ) • L by simp [htgt_def], norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    field_simp
  have h_F_diff := norm_F_diff_le_segment_bound (z₁ := γ t) (z₂ := tgt) (s := s) hk
    (by linarith : 0 < d / 2)
    (fun z hz => norm_segment_to_pole_lower_bound_half hd_pos rfl h_tgt h_chord_le hz)
  rw [show (-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
      (-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) =
      -((-(↑(k - 1) : ℂ)⁻¹ * ((tgt - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹)) by ring,
    norm_neg, show ‖γ t - tgt‖ = ‖tgt - γ t‖ from norm_sub_rev _ _]
  exact h_F_diff

/-- If `chord = o(d^n)`, `d → 0`, `d > 0` eventually, and `k ≤ n`, then
`chord/d^k → 0`. -/
theorem tendsto_div_pow_zero_of_isLittleO
    {chord d : ℝ → ℝ} {l : Filter ℝ} {n k : ℕ}
    (h_chord : chord =o[l] (fun t => d t ^ n)) (h_d : Tendsto d l (𝓝 0))
    (h_d_pos : ∀ᶠ t in l, 0 < d t) (hkn : k ≤ n) :
    Tendsto (fun t => chord t / d t ^ k) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h_chord.bound (by linarith : 0 < ε / 2),
    h_d.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)), h_d_pos] with t hb hd hdp
  have hd_n_pos : 0 < d t ^ n := pow_pos hdp n
  have hd_k_pos : 0 < d t ^ k := pow_pos hdp k
  rw [Real.dist_eq, sub_zero]
  have h_pow : d t ^ n = d t ^ k * d t ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [Real.norm_eq_abs] at hb
  rw [Real.norm_eq_abs, abs_of_nonneg hd_n_pos.le] at hb
  rw [abs_div, abs_of_pos hd_k_pos]
  have h_pow_le : d t ^ (n - k) ≤ 1 := by
    rcases Nat.eq_zero_or_pos (n - k) with h_eq | h_pos
    · simp [h_eq]
    · exact pow_le_one₀ hdp.le hd.le |>.trans_eq (by simp)
  calc |chord t| / d t ^ k
      ≤ ε / 2 * d t ^ (n - k) := by
        rw [div_le_iff₀ hd_k_pos]
        nlinarith [hb, h_pow]
    _ ≤ ε / 2 * 1 := by gcongr
    _ < ε := by linarith

/-- **F-diff tends to zero along a tangent ray (parametrised core).** If the
chord to the `+T` tangent target is `o(‖γ(t) − s‖^n)` along `l`, `γ → s` and
`γ ≠ s` eventually along `l`, and `2 ≤ k ≤ n`, then the antiderivative
difference between `γ(t)` and the target `s + (‖γ(t)−s‖/‖T‖)·T` tends to `0`
along `l`. The right side instantiates `T = L`, `l = 𝓝[>] t₀`; the left side
`T = -L`, `l = 𝓝[<] t₀`. -/
theorem F_diff_at_tangent_target_tendsto_zero
    {γ : ℝ → ℂ} {s : ℂ} {l : Filter ℝ} {T : ℂ} {n k : ℕ}
    (hT : T ≠ 0) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (h_chord : (fun t => ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖) =o[l]
      fun t => ‖γ t - s‖ ^ n)
    (h_ne : ∀ᶠ t in l, γ t ≠ s) (h_to : Tendsto γ l (𝓝 s)) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖T‖ : ℝ) • T) - s) ^ (k - 1))⁻¹)‖)
      l (𝓝 0) := by
  have h_d_to_zero : Tendsto (fun t => ‖γ t - s‖) l (𝓝 0) := by
    simpa using (h_to.sub_const s).norm
  have h_d_pos : ∀ᶠ t in l, 0 < ‖γ t - s‖ := by
    filter_upwards [h_ne] with t h
    exact norm_pos_iff.mpr (sub_ne_zero.mpr h)
  have h_const_ratio : Tendsto
      (fun t => 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ / ‖γ t - s‖ ^ k))
      l (𝓝 0) := by
    simpa using
      (tendsto_div_pow_zero_of_isLittleO h_chord h_d_to_zero h_d_pos hkn).const_mul (2 ^ k : ℝ)
  have h_chord_le_d : ∀ᶠ t in l,
      ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ ≤ ‖γ t - s‖ := by
    filter_upwards [h_chord.bound one_pos,
      h_d_to_zero.eventually (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      h_d_pos] with t hb hd hdp
    calc ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖
        ≤ ‖γ t - s‖ ^ n := by simpa using hb
      _ ≤ ‖γ t - s‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg _) hd hn1
      _ = ‖γ t - s‖ := pow_one _
  have h_F_diff_le : ∀ᶠ t in l,
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖T‖ : ℝ) • T) - s) ^ (k - 1))⁻¹)‖ ≤
      2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ / ‖γ t - s‖ ^ k) := by
    filter_upwards [h_ne, h_chord_le_d] with t h_ne hcd
    have hcd' : ‖γ t - (s + (‖γ t - s‖ / ‖T‖ : ℝ) • T)‖ ≤ ‖γ t - s‖ := by
      rwa [show γ t - (s + (‖γ t - s‖ / ‖T‖ : ℝ) • T) =
            γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T by ring]
    have h_bound := norm_F_diff_at_tangent_target_le hk hT h_ne hcd'
    rw [show ‖γ t - (s + (‖γ t - s‖ / ‖T‖ : ℝ) • T)‖ =
          ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ by congr 1; ring] at h_bound
    calc ‖_‖
        ≤ (1 : ℝ) / (‖γ t - s‖ / 2) ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ := h_bound
      _ = 2 ^ k / ‖γ t - s‖ ^ k *
            ‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ := by
          congr 1; rw [div_pow]; field_simp
      _ = 2 ^ k * (‖γ t - s - (‖γ t - s‖ / ‖T‖ : ℝ) • T‖ / ‖γ t - s‖ ^ k) := by ring
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_const_ratio
    (Eventually.of_forall fun _ => norm_nonneg _) h_F_diff_le

/-- Under HW's flatness condition `n ≥ k` (with `k ≥ 2`), the antiderivative
difference between `γ(t)` and the tangent target on the +L ray tends to 0 as
`t → t₀⁺`. -/
theorem F_diff_at_tangent_target_tendsto_zero_right
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] t₀) (𝓝 0) := by
  have h_ne := eventually_ne self_notMem_Ioi hL h_deriv h_s
  have h_re := eventually_re_smul_conj_nonneg hL h_deriv h_s
    (fun t ht => by rw [abs_of_pos (sub_pos.mpr ht)]) rfl
  exact F_diff_at_tangent_target_tendsto_zero hL hk hkn hn1
    (chord_to_tangent_isLittleO hL h_re h_ne
      (LeanModularForms.orthogonal_deviation_at_radius_right h_flat hL hL_right h_s))
    h_ne (h_s ▸ h_deriv.continuousWithinAt)

/-- Left-side counterpart of `F_diff_at_tangent_target_tendsto_zero_right`,
with the tangent target on the `-L` ray. -/
theorem F_diff_at_tangent_target_tendsto_zero_left
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hkn : k ≤ n) (hn1 : 1 ≤ n) :
    Tendsto (fun t =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ t - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ *
          (((s + (‖γ t - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[<] t₀) (𝓝 0) := by
  have h_ne := eventually_ne self_notMem_Iio hL h_deriv h_s
  have h_re := eventually_re_smul_conj_nonneg hL h_deriv h_s
    (fun t ht => by rw [abs_of_neg (sub_neg.mpr ht), neg_smul, smul_neg, neg_neg])
    (norm_neg L)
  have h_dev : (fun t => ‖tangentDeviation (γ t - s) (-L)‖) =o[𝓝[<] t₀]
      fun t => ‖γ t - s‖ ^ n := by
    refine (LeanModularForms.orthogonal_deviation_at_radius_left h_flat hL hL_left
      h_s).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    show ‖tangentDeviation (γ t - s) L‖ = ‖tangentDeviation (γ t - s) (-L)‖
    congr 1
    unfold tangentDeviation orthogonalProjectionComplex
    rw [Complex.normSq_neg L,
      show ((γ t - s) * starRingEnd ℂ (-L)).re = -((γ t - s) * starRingEnd ℂ L).re by
        rw [map_neg, mul_neg]; exact Complex.neg_re _]
    module
  exact F_diff_at_tangent_target_tendsto_zero (neg_ne_zero.mpr hL) hk hkn hn1
    (chord_to_tangent_isLittleO (neg_ne_zero.mpr hL) h_re h_ne h_dev) h_ne
    (h_s ▸ h_deriv.continuousWithinAt)

end HungerbuhlerWasem

end

end
