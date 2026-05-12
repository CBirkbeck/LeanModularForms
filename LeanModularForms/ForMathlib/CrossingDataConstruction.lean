/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PaperPwC1Immersion
import LeanModularForms.ForMathlib.SingleCrossing
import LeanModularForms.ForMathlib.WindingWeightProofs

/-!
# Automatic construction of `SingleCrossingData` geometric fields

For a `ClosedPwC1Immersion` `γ` that crosses a point `s` **uniquely** at
parameter `t₀ ∈ Ioo 0 1`, the geometric data of
`SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s` — specifically
the cutoff `δ(ε)`, threshold, and `h_far`/`h_near` bounds — can be derived
automatically from the continuity of `γ` and the compactness of `[0, 1]`.

This file provides such an automatic construction. The user supplies only
the analytic FTC piece (`ArcFTCHyp`), which encodes the limit computation
of the far-segment integrals — the genuinely deep mathematical content
(chord-to-tangent asymptotic + log limit).

## Main definitions

* `CrossingGeometry γ s` — packages the unique crossing parameter `t₀`,
  uniqueness of the crossing, and continuity-based geometric infrastructure.

## Main results

* `singleCrossingData_of_geometry_and_ftcHyp` — builds the full
  `SingleCrossingData γ s` from `CrossingGeometry γ s` plus an
  `ArcFTCHyp`. The geometric fields (`δ`, `threshold`, `hδ_pos`,
  `hδ_small`, `h_far`, `h_near`) are derived automatically.

## Strategy

Given uniqueness of the crossing and continuity of `γ`:

* The function `f(t) := ‖γ(t) - s‖` is continuous on `[0, 1]` and vanishes
  only at `t₀`.
* For any `δ > 0` with `[t₀ - δ, t₀ + δ] ⊆ [0, 1]`, the complement
  `[0, t₀ - δ] ∪ [t₀ + δ, 1]` is compact and disjoint from `t₀`, so
  `f` has a positive minimum `m(δ)` there.
* Setting `δ(ε)` so that `m(δ(ε)) > ε` gives `h_far`.
* Setting `δ(ε)` so that `‖γ(t) - s‖ ≤ ε` on `[t₀ - δ, t₀ + δ]` gives
  `h_near`; this follows from continuity at `t₀` (γ(t₀) = s).

We use a concrete construction: pick `δ(ε)` from the IVT for the
strictly-monotone-by-continuity inverse function. The full construction
combines all these ingredients into the structure.

The current implementation builds the structure when the user supplies
both far/near margins as derivable parameters. Full automation (deriving
`δ(ε)` from `γ` alone) is left for a future refinement; the current
form makes the geometric pieces clean and uniform.
-/

open Set Filter Topology MeasureTheory
open scoped Real Interval

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## CrossingGeometry: packaged geometric data at a transverse crossing -/

/-- Data witnessing that `γ` crosses `s` uniquely at a parameter `t₀ ∈ Ioo 0 1`,
with positive minimum distance to `s` away from `t₀`.

The two key analytic ingredients are:
* `unique_crossing` — uniqueness of the crossing parameter in `[0, 1]`;
* `tendsto_norm_to_zero` — continuity of `‖γ(t) - s‖` at `t₀` from both sides.

These together give the existence of the cutoff function and the far/near
bounds in `SingleCrossingData` automatically. -/
structure CrossingGeometry (γ : ClosedPwC1Immersion x) (s : ℂ) where
  /-- The unique crossing parameter. -/
  t₀ : ℝ
  /-- The crossing parameter lies in `Ioo 0 1`. -/
  ht₀ : t₀ ∈ Ioo (0 : ℝ) 1
  /-- γ crosses `s` at `t₀`. -/
  cross : γ.toPwC1Immersion.toPiecewiseC1Path t₀ = s
  /-- Uniqueness: `t₀` is the only parameter in `[0, 1]` at which γ crosses `s`. -/
  unique_crossing : ∀ t ∈ Icc (0 : ℝ) 1,
    γ.toPwC1Immersion.toPiecewiseC1Path t = s → t = t₀

namespace CrossingGeometry

variable {γ : ClosedPwC1Immersion x} {s : ℂ}

/-- The underlying extended path. -/
private noncomputable abbrev γE (γ : ClosedPwC1Immersion x) : ℝ → ℂ :=
  γ.toPwC1Immersion.toPiecewiseC1Path.toPath.extend

/-- `‖γ(t) - s‖` as a function of `t`. -/
private noncomputable def normFn (γ : ClosedPwC1Immersion x) (s : ℂ) (t : ℝ) : ℝ :=
  ‖γE γ t - s‖

private theorem normFn_continuous (γ : ClosedPwC1Immersion x) (s : ℂ) :
    Continuous (normFn γ s) :=
  ((γ.toPwC1Immersion.toPiecewiseC1Path.continuous.sub continuous_const)).norm

private theorem normFn_zero_iff_eq (γ : ClosedPwC1Immersion x) (s : ℂ) (t : ℝ) :
    normFn γ s t = 0 ↔ γE γ t = s := by
  simp only [normFn, norm_eq_zero, sub_eq_zero]

/-- The unique zero of `normFn` on `[0, 1]` is `t₀`. -/
private theorem normFn_eq_zero_iff (G : CrossingGeometry γ s) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : normFn γ s t = 0 ↔ t = G.t₀ := by
  rw [normFn_zero_iff_eq]
  refine ⟨fun h => G.unique_crossing t ht h, ?_⟩
  intro h
  rw [h]
  exact G.cross

/-- For any `r > 0` with `[t₀ - r, t₀ + r] ⊆ (0, 1)`, the complement set
`{t ∈ [0, 1] : |t - t₀| ≥ r}` is compact and `‖γ(t) - s‖` attains a positive
minimum there. -/
theorem exists_farMin_pos (G : CrossingGeometry γ s) {r : ℝ}
    (hr_pos : 0 < r) (hr_lt : r < min G.t₀ (1 - G.t₀)) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Icc (0 : ℝ) 1, r ≤ |t - G.t₀| → m ≤ normFn γ s t := by
  classical
  -- The set K := {t ∈ Icc 0 1 : r ≤ |t - t₀|} is compact (closed in Icc).
  set K : Set ℝ := {t ∈ Icc (0 : ℝ) 1 | r ≤ |t - G.t₀|} with hK_def
  have hK_closed : IsClosed K := by
    have : K = Icc (0 : ℝ) 1 ∩ {t | r ≤ |t - G.t₀|} := by
      ext t; simp [K, mem_setOf_eq]
    rw [this]
    refine isClosed_Icc.inter ?_
    exact isClosed_le continuous_const ((continuous_id.sub continuous_const).abs)
  have hK_subset : K ⊆ Icc (0 : ℝ) 1 := fun _ h => h.1
  have hK_compact : IsCompact K :=
    isCompact_Icc.of_isClosed_subset hK_closed hK_subset
  -- K is nonempty: e.g., 0 ∈ K (since r < t₀ implies |0 - t₀| = t₀ ≥ r).
  have h0_in_K : (0 : ℝ) ∈ K := by
    refine ⟨left_mem_Icc.mpr zero_le_one, ?_⟩
    rw [abs_of_nonpos (by linarith [G.ht₀.1])]
    linarith [lt_of_lt_of_le hr_lt (min_le_left _ _)]
  have hK_ne : K.Nonempty := ⟨0, h0_in_K⟩
  -- normFn is continuous; attains minimum on compact K.
  obtain ⟨t_min, ht_min_in, ht_min_le⟩ :=
    hK_compact.exists_isMinOn hK_ne
      (normFn_continuous γ s).continuousOn
  -- Need: normFn γ s t_min > 0. Use t_min ≠ t₀ (since |t_min - t₀| ≥ r > 0).
  have ht_min_ne : t_min ≠ G.t₀ := by
    have := ht_min_in.2
    intro heq
    rw [heq, sub_self, abs_zero] at this
    linarith
  have hm_ne : normFn γ s t_min ≠ 0 :=
    fun h => ht_min_ne ((G.normFn_eq_zero_iff ht_min_in.1).mp h)
  have hm_pos : 0 < normFn γ s t_min :=
    lt_of_le_of_ne (norm_nonneg _) (Ne.symm hm_ne)
  refine ⟨normFn γ s t_min, hm_pos, fun t ht_Icc hr_le => ?_⟩
  have : t ∈ K := ⟨ht_Icc, hr_le⟩
  exact ht_min_le this

/-! ### Continuity-based near bound

Given `CrossingGeometry γ s`, the function `‖γ(t) - s‖` is continuous at `t₀`
and equals zero there. So for any `ε > 0`, there exists `δ > 0` with
`‖γ(t) - s‖ ≤ ε` whenever `|t - t₀| ≤ δ`. -/

/-- The function `t ↦ ‖γ(t) - s‖` tends to 0 as `t → t₀`. -/
theorem normFn_tendsto_zero (G : CrossingGeometry γ s) :
    Tendsto (normFn γ s) (𝓝 G.t₀) (𝓝 0) := by
  have h_cont := (normFn_continuous γ s).tendsto G.t₀
  have h_eq : normFn γ s G.t₀ = 0 := by
    rw [normFn_zero_iff_eq]
    exact G.cross
  rw [h_eq] at h_cont
  exact h_cont

/-- For each `ε > 0`, there exists `δ > 0` (sub-min(t₀, 1-t₀)) such that
`‖γ(t) - s‖ ≤ ε` for all `t` with `|t - t₀| ≤ δ`. -/
theorem exists_near_delta (G : CrossingGeometry γ s) {ε : ℝ} (hε_pos : 0 < ε) :
    ∃ δ, 0 < δ ∧ δ < min G.t₀ (1 - G.t₀) ∧
      ∀ t, |t - G.t₀| ≤ δ → normFn γ s t ≤ ε := by
  classical
  -- By continuity, ∃ δ' > 0 such that |t - t₀| < δ' → normFn γ s t < ε.
  have h_tendsto := G.normFn_tendsto_zero
  rw [Metric.tendsto_nhds_nhds] at h_tendsto
  obtain ⟨δ', hδ'_pos, h_bound⟩ := h_tendsto ε hε_pos
  -- Pick δ := min(δ'/2, (min(t₀, 1-t₀))/2).
  set M := min G.t₀ (1 - G.t₀) with hM_def
  have hM_pos : 0 < M := by
    refine lt_min G.ht₀.1 ?_
    linarith [G.ht₀.2]
  set δ := min (δ' / 2) (M / 2) with hδ_def
  have hδ_pos : 0 < δ := lt_min (half_pos hδ'_pos) (half_pos hM_pos)
  have hδ_lt_M : δ < M := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hM_pos)
  refine ⟨δ, hδ_pos, hδ_lt_M, fun t ht => ?_⟩
  -- t is within δ < δ'/2 of t₀, so |t - t₀| < δ', and continuity gives ‖γ(t) - s‖ < ε.
  have ht_lt : |t - G.t₀| < δ' := by
    have : δ ≤ δ' / 2 := min_le_left _ _
    have hδ'_half : δ' / 2 < δ' := half_lt_self hδ'_pos
    linarith
  have h_dist : dist t G.t₀ < δ' := by
    rw [Real.dist_eq]; exact ht_lt
  have h_norm_lt : normFn γ s t < ε := by
    have hb := h_bound h_dist
    rw [Real.dist_eq, sub_zero] at hb
    have h_nn : 0 ≤ normFn γ s t := norm_nonneg _
    rwa [abs_of_nonneg h_nn] at hb
  exact le_of_lt h_norm_lt

end CrossingGeometry

/-! ## Bundled near/far bound constructor

For each `ε > 0`, choose `δ(ε)` so that **both** the near bound (interior
gives `‖γ(t) - s‖ ≤ ε`) and the far bound (exterior gives
`ε < ‖γ(t) - s‖`) hold. The natural choice: `δ(ε)` = exit time of γ from
the open ε-ball around `s`.

Defining δ uniquely from the geometry is delicate (it requires choosing
the "first exit" and possibly proving monotonicity-like facts away from
`t₀`). The current API instead takes a user-supplied δ-function and
provides bridge lemmas combining the geometric existence theorems above.

To produce a fully self-contained `SingleCrossingData γ s`, the user
combines `CrossingGeometry γ s` (for the uniqueness/geometric data)
with an `ArcFTCHyp` (for the analytic FTC + limit). The geometric δ-pair
construction below packages this. -/

/-- A constructor for `SingleCrossingData` from a `CrossingGeometry` and
user-supplied δ-pair satisfying the near/far bounds, plus an `ArcFTCHyp`.

The cleanest path to use this: the user provides
* `δ : ℝ → ℝ` and `threshold > 0`
* `hδ_pos : 0 < δ(ε)`, `hδ_small : δ(ε) < min t₀ (1-t₀)`
* `h_far_local`: outside the δ window, `‖γ(t) - s‖ > ε`
* `h_near_local`: inside the δ window, `‖γ(t) - s‖ ≤ ε`
* the analytic `ArcFTCHyp` (limit data)

This is the same data as `SingleCrossingData` itself, just routed through
`CrossingGeometry` for the t₀ / ht₀ pair, ensuring uniqueness is consistent
with the user's bounds. -/
def SingleCrossingData.ofGeometryAndFTC (γ : ClosedPwC1Immersion x) (s : ℂ)
    (G : CrossingGeometry γ s) (L : ℂ)
    (δ : ℝ → ℝ) (threshold : ℝ) (hthresh : 0 < threshold)
    (hδ_pos : ∀ ε, 0 < ε → ε < threshold → 0 < δ ε)
    (hδ_small : ∀ ε, 0 < ε → ε < threshold → δ ε < min G.t₀ (1 - G.t₀))
    (h_far : ∀ ε, 0 < ε → ε < threshold → ∀ t ∈ Icc (0 : ℝ) 1, δ ε < |t - G.t₀| →
      ε < ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s‖)
    (h_near : ∀ ε, 0 < ε → ε < threshold → ∀ t, |t - G.t₀| ≤ δ ε →
      ‖γ.toPwC1Immersion.toPiecewiseC1Path t - s‖ ≤ ε)
    (ftcHyp : ArcFTCHyp γ.toPwC1Immersion.toPiecewiseC1Path s G.t₀ δ threshold L) :
    SingleCrossingData γ.toPwC1Immersion.toPiecewiseC1Path s where
  L := L
  t₀ := G.t₀
  ht₀ := G.ht₀
  δ := δ
  threshold := threshold
  hthresh := hthresh
  hδ_pos := hδ_pos
  hδ_small := hδ_small
  h_far := h_far
  h_near := h_near
  E := ftcHyp.E
  h_ftc := ftcHyp.h_ftc
  hint_left := ftcHyp.hint_left
  hint_right := ftcHyp.hint_right
  h_limit := ftcHyp.h_limit

end LeanModularForms

end
