/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Path
import LeanModularForms.ForMathlib.PiecewiseC1Path

/-!
# Paper-faithful piecewise C¹ immersions (Hungerbühler–Wasem)

The legacy `PiecewiseC1Path` / `PwC1Immersion` in `PiecewiseC1Path.lean` keep the
partition in the *open* interval `(0, 1)` and only require `C¹` regularity on the
*open* sub-intervals between consecutive breakpoints. That is strictly weaker than
the definition used by Hungerbühler–Wasem (arXiv:1808.00997v2, page 3):

> "A closed piecewise `C¹` immersion `Λ : [a,b] → ℂ` is a closed curve such that
> there is a partition `a = a₀ < a₁ < … < aₙ = b` such that `Λ|_{[aₖ,aₖ₊₁]}` is
> of class `C¹` and such that `Λ̇|_{[aₖ,aₖ₊₁]} ≠ 0` for all `k = 0, …, n−1`."

This file mirrors that definition exactly:

* the partition `Finset ℝ` includes both endpoints `0` and `1`;
* on every closed sub-interval `Icc a b` whose endpoints are consecutive
  partition members, the path is `ContDiffOn ℝ 1`;
* for the immersion variant, the derivative is non-vanishing on each closed
  piece.

Because each piece is `C¹` on a *closed* bounded interval, the derivative is
automatically interval-integrable on each piece, and so on `[0, 1]` by gluing.

## Main definitions

* `Finset.IsConsecutive S a b` — `(a, b)` are consecutive members of `S`
  (both lie in `S`, `a < b`, no element of `S` strictly between them).
* `ClosedPwC1Curve x` — a closed path at `x` that is paper-`C¹`-piecewise.
* `ClosedPwC1Immersion x` — extends with non-vanishing derivative on each piece.

## Main results

* `ClosedPwC1Curve.deriv_intervalIntegrable_piece` — derivative is integrable on
  each closed piece between consecutive partition members.

## References

* K. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized
  Residue Theorem*, arXiv:1808.00997v2, page 3.
-/

open Set Filter Topology MeasureTheory

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pair `(a, b)` are *consecutive* members of `S : Finset ℝ` when both lie
in `S`, `a < b`, and no element of `S` lies strictly between them. -/
def Finset.IsConsecutive (S : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ c ∈ S, c ∉ Set.Ioo a b

/-- A **closed piecewise `C¹` curve** in the sense of Hungerbühler–Wasem
(arXiv:1808.00997v2, page 3): a path `[0, 1] → E` returning to its starting point,
together with a partition `0 = a₀ < a₁ < … < aₙ = 1` whose endpoints are included,
such that the path is `C¹` on each *closed* sub-interval `[aₖ, aₖ₊₁]`. -/
structure ClosedPwC1Curve (x : E) extends Path x x where
  /-- The partition. Includes both `0` and `1`. -/
  partition : Finset ℝ
  /-- `0` is a partition point. -/
  zero_mem_partition : (0 : ℝ) ∈ partition
  /-- `1` is a partition point. -/
  one_mem_partition : (1 : ℝ) ∈ partition
  /-- Every partition point lies in `[0, 1]`. -/
  partition_subset : (partition : Set ℝ) ⊆ Icc 0 1
  /-- On every closed sub-interval `[a, b]` whose endpoints are consecutive
  partition members, the extended path is `C¹`. -/
  contDiffOn_pieces : ∀ a b, partition.IsConsecutive a b →
    ContDiffOn ℝ 1 toPath.extend (Icc a b)

/-- A **closed piecewise `C¹` immersion** in the sense of Hungerbühler–Wasem
(arXiv:1808.00997v2, page 3): a closed piecewise `C¹` curve whose derivative
is non-vanishing on every closed sub-interval between consecutive partition
points. -/
structure ClosedPwC1Immersion (x : E) extends ClosedPwC1Curve x where
  /-- On every closed sub-interval between consecutive partition members, the
  *within*-derivative of the extended path is non-zero — i.e. `Λ̇|_{[aₖ,aₖ₊₁]} ≠ 0`
  in the paper. We use `derivWithin _ (Icc a b)` rather than the global `deriv`
  because at corner partition points the global `deriv` is `0` by mathlib
  convention (the function is not differentiable there), which would falsely
  contradict non-vanishing. -/
  derivWithin_ne_zero_pieces : ∀ a b, partition.IsConsecutive a b →
    ∀ t ∈ Icc a b, derivWithin toPath.extend (Icc a b) t ≠ 0

namespace ClosedPwC1Curve

variable {x : E}

/-- The underlying extended path is continuous. -/
theorem continuous (γ : ClosedPwC1Curve x) : Continuous γ.toPath.extend :=
  γ.toPath.continuous_extend

/-! ## Interval integrability of the derivative on each piece

The key payoff of the closed-piece formulation: on each closed sub-interval
between consecutive partition members, the derivative is interval-integrable.
This follows from `ContDiffOn ℝ 1` on the closed piece, which gives a continuous
`derivWithin`, agreeing with `deriv` on the open interior (i.e. almost
everywhere on the piece). -/

/-- On the open interior `Ioo a b`, the within-`Icc a b` derivative agrees with
the global derivative. -/
private lemma derivWithin_eq_deriv_on_Ioo (f : ℝ → E) {a b t : ℝ}
    (ht : t ∈ Ioo a b) :
    derivWithin f (Icc a b) t = deriv f t :=
  derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)

/-- **Piece-wise integrability of the derivative.** On each closed sub-interval
`[a, b]` between consecutive partition members, `deriv γ.toPath.extend` is
interval-integrable. This is `TIGHT-6` for one piece. -/
theorem deriv_intervalIntegrable_piece (γ : ClosedPwC1Curve x) {a b : ℝ}
    (h : γ.partition.IsConsecutive a b) :
    IntervalIntegrable (deriv γ.toPath.extend) volume a b := by
  have hab : a ≤ b := h.2.2.1.le
  -- Continuous `derivWithin` on the closed piece.
  have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b h
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    ContDiffOn.continuousOn_derivWithin hcd (uniqueDiffOn_Icc h.2.2.1) le_rfl
  -- That gives integrability of `derivWithin`.
  have h_dw_int :
      IntervalIntegrable (derivWithin γ.toPath.extend (Icc a b)) volume a b :=
    h_dw_cont.intervalIntegrable_of_Icc hab
  -- `derivWithin = deriv` on the open interior, hence a.e. on the integration set.
  refine h_dw_int.congr_ae ?_
  -- Goal: derivWithin _ (Icc a b) =ᵐ[volume.restrict (Ι a b)] deriv γ.toPath.extend
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo a b, ?_, ?_⟩
  · rw [MeasureTheory.mem_ae_iff,
        MeasureTheory.Measure.restrict_apply' measurableSet_uIoc]
    refine MeasureTheory.measure_mono_null (t := ({b} : Set ℝ)) ?_ Real.volume_singleton
    intro t ⟨ht_compl, ht_in⟩
    rw [uIoc_of_le hab] at ht_in
    by_contra hne
    exact ht_compl ⟨ht_in.1, lt_of_le_of_ne ht_in.2 hne⟩
  · intro t ht
    exact derivWithin_eq_deriv_on_Ioo _ ht

end ClosedPwC1Curve

/-! ## Helper: gluing piece-wise interval-integrability over a finite partition -/

/-- If `f` is interval-integrable on every consecutive pair of a finite partition
of `[a, b]` containing both endpoints, then `f` is interval-integrable on `[a, b]`. -/
private theorem intervalIntegrable_of_consecutive_pieces
    {α : Type*} [TopologicalSpace α] [ENormedAddMonoid α]
    [TopologicalSpace.PseudoMetrizableSpace α]
    {f : ℝ → α} {μ : MeasureTheory.Measure ℝ} :
    ∀ s : Finset ℝ, ∀ a b : ℝ, a ∈ s → b ∈ s → a ≤ b →
      (∀ c ∈ s, a ≤ c ∧ c ≤ b) →
      (∀ p q, s.IsConsecutive p q → IntervalIntegrable f μ p q) →
      IntervalIntegrable f μ a b := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro a b ha hb hab hbds hpc
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · subst hab_eq
      exact IntervalIntegrable.refl
    -- Pick the smallest partition member strictly above `a`.
    set t : Finset ℝ := s.filter (a < ·) with ht_def
    have hb_in_t : b ∈ t := Finset.mem_filter.mpr ⟨hb, hab_lt⟩
    have ht_ne : t.Nonempty := ⟨b, hb_in_t⟩
    set a' := t.min' ht_ne with ha'_def
    have ha'_in_t : a' ∈ t := t.min'_mem ht_ne
    have ha'_in_s : a' ∈ s := (Finset.mem_filter.mp ha'_in_t).1
    have ha_lt_a' : a < a' := (Finset.mem_filter.mp ha'_in_t).2
    -- `(a, a')` is consecutive in `s`.
    have hcons : s.IsConsecutive a a' := by
      refine ⟨ha, ha'_in_s, ha_lt_a', ?_⟩
      intro c hc hc_Ioo
      have hc_in_t : c ∈ t :=
        Finset.mem_filter.mpr ⟨hc, hc_Ioo.1⟩
      have : a' ≤ c := t.min'_le _ hc_in_t
      linarith [hc_Ioo.2]
    have hint_aa' : IntervalIntegrable f μ a a' := hpc _ _ hcons
    -- Recurse on `s.erase a`, which is strictly smaller and still contains `a'` and `b`.
    set s' : Finset ℝ := s.erase a with hs'_def
    have hs'_ssub : s' ⊂ s := Finset.erase_ssubset ha
    have ha'_in_s' : a' ∈ s' :=
      Finset.mem_erase.mpr ⟨ne_of_gt ha_lt_a', ha'_in_s⟩
    have hb_in_s' : b ∈ s' := Finset.mem_erase.mpr ⟨ne_of_gt hab_lt, hb⟩
    have hbds' : ∀ c ∈ s', a' ≤ c ∧ c ≤ b := by
      intro c hc
      have hc_in : c ∈ s := (Finset.mem_erase.mp hc).2
      have hc_ne : c ≠ a := (Finset.mem_erase.mp hc).1
      refine ⟨?_, (hbds c hc_in).2⟩
      -- c ≠ a and a ≤ c ⇒ a < c, then c ∈ t, so a' ≤ c.
      have hac : a < c := lt_of_le_of_ne (hbds c hc_in).1 (Ne.symm hc_ne)
      exact t.min'_le _ (Finset.mem_filter.mpr ⟨hc_in, hac⟩)
    have hpc' : ∀ p q, s'.IsConsecutive p q → IntervalIntegrable f μ p q := by
      intro p q hcons'
      -- Consecutive in `s.erase a` is consecutive in `s` (provided neither equals `a`,
      -- which is automatic since both are in `s.erase a`).
      refine hpc p q ⟨?_, ?_, hcons'.2.2.1, ?_⟩
      · exact (Finset.mem_erase.mp hcons'.1).2
      · exact (Finset.mem_erase.mp hcons'.2.1).2
      · intro c hc hc_Ioo
        -- If c ∈ s, c ∉ Ioo p q. We use hcons'.2.2.2 with c ∈ s.erase a.
        -- Need: c ∈ s.erase a, i.e., c ≠ a.
        -- We have a ≤ c (from hbds c hc) and a < p (since p ≥ a' > a, see below).
        -- So c ≥ p > a, hence c ≠ a.
        have hp_ge_a' : a' ≤ p := (hbds' p hcons'.1).1
        have hp_gt_a : a < p := lt_of_lt_of_le ha_lt_a' hp_ge_a'
        have hc_gt_a : a < c := lt_of_lt_of_le hp_gt_a hc_Ioo.1.le
        exact hcons'.2.2.2 c
          (Finset.mem_erase.mpr ⟨ne_of_gt hc_gt_a, hc⟩) hc_Ioo
    have hint_a'b : IntervalIntegrable f μ a' b :=
      ih s' hs'_ssub a' b ha'_in_s' hb_in_s' (hbds' b hb_in_s').1 hbds' hpc'
    exact hint_aa'.trans hint_a'b

/-! ## Global interval-integrability of the derivative -/

namespace ClosedPwC1Curve

variable {x : E}

/-- **TIGHT-6 (global form).** For a paper-faithful closed piecewise `C¹` curve
`γ`, the derivative `deriv γ.toPath.extend` is interval-integrable on `[0, 1]`. -/
theorem deriv_extend_intervalIntegrable (γ : ClosedPwC1Curve x) :
    IntervalIntegrable (deriv γ.toPath.extend) volume 0 1 :=
  intervalIntegrable_of_consecutive_pieces γ.partition 0 1
    γ.zero_mem_partition γ.one_mem_partition zero_le_one
    (fun _ hc => ⟨(γ.partition_subset hc).1, (γ.partition_subset hc).2⟩)
    (fun _ _ h => γ.deriv_intervalIntegrable_piece h)

/-! ## Bridge to legacy `PiecewiseC1Path`

A paper-faithful curve produces a legacy curve by erasing the global endpoints
`0` and `1` from the partition (the legacy structure keeps the partition in
the open interior `(0, 1)` by convention). -/

/-- For `t` strictly inside `(0, 1)` not in the paper partition, find the
consecutive partition pair containing `t`. -/
private lemma exists_consecutive_pair_containing (γ : ClosedPwC1Curve x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htn : t ∉ γ.partition) :
    ∃ a b, γ.partition.IsConsecutive a b ∧ t ∈ Ioo a b := by
  set pred := γ.partition.filter (· < t) with hpred_def
  set succ := γ.partition.filter (t < ·) with hsucc_def
  have h0_pred : (0 : ℝ) ∈ pred := Finset.mem_filter.mpr ⟨γ.zero_mem_partition, ht.1⟩
  have h1_succ : (1 : ℝ) ∈ succ := Finset.mem_filter.mpr ⟨γ.one_mem_partition, ht.2⟩
  set a := pred.max' ⟨0, h0_pred⟩
  set b := succ.min' ⟨1, h1_succ⟩
  have ha_mem : a ∈ pred := pred.max'_mem _
  have hb_mem : b ∈ succ := succ.min'_mem _
  have ha_in : a ∈ γ.partition := (Finset.mem_filter.mp ha_mem).1
  have ha_lt : a < t := (Finset.mem_filter.mp ha_mem).2
  have hb_in : b ∈ γ.partition := (Finset.mem_filter.mp hb_mem).1
  have ht_lt_b : t < b := (Finset.mem_filter.mp hb_mem).2
  refine ⟨a, b, ⟨ha_in, hb_in, lt_trans ha_lt ht_lt_b, ?_⟩, ⟨ha_lt, ht_lt_b⟩⟩
  intro c hc hc_Ioo
  rcases lt_trichotomy c t with hct | hct | hct
  · exact absurd (pred.le_max' c (Finset.mem_filter.mpr ⟨hc, hct⟩))
      (by linarith [hc_Ioo.1])
  · exact htn (hct ▸ hc)
  · exact absurd (succ.min'_le c (Finset.mem_filter.mpr ⟨hc, hct⟩))
      (by linarith [hc_Ioo.2])

/-- The legacy partition `(γ.partition.erase 0).erase 1` lies strictly inside
`(0, 1)`. -/
private lemma legacy_partition_subset_Ioo (γ : ClosedPwC1Curve x) :
    (((γ.partition.erase 0).erase 1 : Finset ℝ) : Set ℝ) ⊆ Ioo (0 : ℝ) 1 := by
  intro t ht
  have h_ne_1 : t ≠ 1 := (Finset.mem_erase.mp ht).1
  have h_in_e0 : t ∈ γ.partition.erase 0 := (Finset.mem_erase.mp ht).2
  have h_ne_0 : t ≠ 0 := (Finset.mem_erase.mp h_in_e0).1
  have h_in : t ∈ γ.partition := (Finset.mem_erase.mp h_in_e0).2
  have h_in_Icc := γ.partition_subset h_in
  exact ⟨lt_of_le_of_ne h_in_Icc.1 (Ne.symm h_ne_0),
         lt_of_le_of_ne h_in_Icc.2 h_ne_1⟩

/-- If `t ∈ Ioo 0 1` and `t ∉ (γ.partition.erase 0).erase 1`, then `t ∉ γ.partition`. -/
private lemma not_mem_partition_of_not_mem_legacy (γ : ClosedPwC1Curve x) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) (htn : t ∉ (γ.partition.erase 0).erase 1) :
    t ∉ γ.partition := fun h_in => htn <| by
  refine Finset.mem_erase.mpr ⟨ne_of_lt ht.2, Finset.mem_erase.mpr ⟨?_, h_in⟩⟩
  exact (ne_of_lt ht.1).symm

/-- Unpack a legacy interior partition point: it lies strictly inside `(0, 1)`
and belongs to the original paper partition. -/
private lemma legacy_mem_unpack (γ : ClosedPwC1Curve x) {p : ℝ}
    (hp : p ∈ (γ.partition.erase 0).erase 1) :
    0 < p ∧ p < 1 ∧ p ∈ γ.partition := by
  have hp_ne_1 : p ≠ 1 := (Finset.mem_erase.mp hp).1
  have hp_in_e0 := (Finset.mem_erase.mp hp).2
  have hp_ne_0 : p ≠ 0 := (Finset.mem_erase.mp hp_in_e0).1
  have hp_in : p ∈ γ.partition := (Finset.mem_erase.mp hp_in_e0).2
  have hp_in_Icc := γ.partition_subset hp_in
  exact ⟨lt_of_le_of_ne hp_in_Icc.1 (Ne.symm hp_ne_0),
         lt_of_le_of_ne hp_in_Icc.2 hp_ne_1, hp_in⟩

/-- A `ClosedPwC1Curve` produces a legacy `PiecewiseC1Path`. -/
def toPiecewiseC1Path (γ : ClosedPwC1Curve x) : PiecewiseC1Path x x where
  toPath := γ.toPath
  partition := (γ.partition.erase 0).erase 1
  partition_subset := γ.legacy_partition_subset_Ioo
  differentiable_off := by
    intro t ht htn
    have htn' : t ∉ γ.partition := γ.not_mem_partition_of_not_mem_legacy ht htn
    obtain ⟨a, b, hcons, ht_Ioo⟩ := γ.exists_consecutive_pair_containing ht htn'
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b hcons
    exact (hcd.differentiableOn_one t (Ioo_subset_Icc_self ht_Ioo)).differentiableAt
      (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2)
  deriv_continuous_off := by
    intro t ht htn
    have htn' : t ∉ γ.partition := γ.not_mem_partition_of_not_mem_legacy ht htn
    obtain ⟨a, b, hcons, ht_Ioo⟩ := γ.exists_consecutive_pair_containing ht htn'
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b hcons
    have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
      ContDiffOn.continuousOn_derivWithin hcd (uniqueDiffOn_Icc hcons.2.2.1) le_rfl
    have h_dw_at : ContinuousAt (derivWithin γ.toPath.extend (Icc a b)) t :=
      (h_dw_cont t (Ioo_subset_Icc_self ht_Ioo)).continuousAt
        (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2)
    -- `derivWithin _ (Icc a b) =ᶠ[𝓝 t] deriv _` since they agree on `Ioo a b ∈ 𝓝 t`.
    refine h_dw_at.congr (Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds ht_Ioo.1 ht_Ioo.2) ?_)
    intro u hu
    exact derivWithin_eq_deriv_on_Ioo _ hu

end ClosedPwC1Curve

namespace ClosedPwC1Immersion

variable {x : E}

/-- Helper for the immersion bridge: at an interior partition point `p`, the
predecessor `a := max{c ∈ partition : c < p}` is well-defined and `(a, p)` is
consecutive. -/
private lemma exists_predecessor (γ : ClosedPwC1Immersion x) {p : ℝ}
    (hp_in : p ∈ γ.partition) (hp_pos : 0 < p) :
    ∃ a, γ.partition.IsConsecutive a p := by
  set pred := γ.partition.filter (· < p)
  have h0_pred : (0 : ℝ) ∈ pred :=
    Finset.mem_filter.mpr ⟨γ.zero_mem_partition, hp_pos⟩
  set a := pred.max' ⟨0, h0_pred⟩
  have ha_mem : a ∈ pred := pred.max'_mem _
  have ha_in : a ∈ γ.partition := (Finset.mem_filter.mp ha_mem).1
  have ha_lt : a < p := (Finset.mem_filter.mp ha_mem).2
  refine ⟨a, ha_in, hp_in, ha_lt, ?_⟩
  intro c hc hc_Ioo
  exact absurd (pred.le_max' c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.2⟩))
    (by linarith [hc_Ioo.1])

/-- Helper for the immersion bridge: at an interior partition point `p`, the
successor `b := min{c ∈ partition : p < c}` is well-defined and `(p, b)` is
consecutive. -/
private lemma exists_successor (γ : ClosedPwC1Immersion x) {p : ℝ}
    (hp_in : p ∈ γ.partition) (hp_lt_one : p < 1) :
    ∃ b, γ.partition.IsConsecutive p b := by
  set succ := γ.partition.filter (p < ·)
  have h1_succ : (1 : ℝ) ∈ succ :=
    Finset.mem_filter.mpr ⟨γ.one_mem_partition, hp_lt_one⟩
  set b := succ.min' ⟨1, h1_succ⟩
  have hb_mem : b ∈ succ := succ.min'_mem _
  have hb_in : b ∈ γ.partition := (Finset.mem_filter.mp hb_mem).1
  have hp_lt_b : p < b := (Finset.mem_filter.mp hb_mem).2
  refine ⟨b, hp_in, hb_in, hp_lt_b, ?_⟩
  intro c hc hc_Ioo
  exact absurd (succ.min'_le c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.1⟩))
    (by linarith [hc_Ioo.2])

/-- A `ClosedPwC1Immersion` produces a legacy `PwC1Immersion`. -/
def toPwC1Immersion (γ : ClosedPwC1Immersion x) : PwC1Immersion x x where
  toPiecewiseC1Path := γ.toClosedPwC1Curve.toPiecewiseC1Path
  deriv_ne_zero := by
    intro t ht htn
    have htn' : t ∉ γ.partition :=
      γ.toClosedPwC1Curve.not_mem_partition_of_not_mem_legacy ht htn
    obtain ⟨a, b, hcons, ht_Ioo⟩ :=
      γ.toClosedPwC1Curve.exists_consecutive_pair_containing ht htn'
    have h_dw_ne :=
      γ.derivWithin_ne_zero_pieces a b hcons t (Ioo_subset_Icc_self ht_Ioo)
    -- `Path.extend` is a coercion-overloaded `toPath.extend`; both forms agree.
    change deriv γ.toPath.extend t ≠ 0
    rwa [ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo _ ht_Ioo] at h_dw_ne
  left_deriv_limit := by
    intro p hp
    obtain ⟨hp_pos, _, hp_in⟩ := γ.toClosedPwC1Curve.legacy_mem_unpack hp
    obtain ⟨a, hcons⟩ := γ.exists_predecessor hp_in hp_pos
    have ha_lt : a < p := hcons.2.2.1
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a p) := γ.contDiffOn_pieces a p hcons
    have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a p)) (Icc a p) :=
      ContDiffOn.continuousOn_derivWithin hcd (uniqueDiffOn_Icc ha_lt) le_rfl
    set L := derivWithin γ.toPath.extend (Icc a p) p
    have hL_ne : L ≠ 0 :=
      γ.derivWithin_ne_zero_pieces a p hcons p (right_mem_Icc.mpr ha_lt.le)
    refine ⟨L, hL_ne, ?_⟩
    -- 𝓝[<] p localizes to 𝓝[Ioo a p] p (intersect with Ioi a, which is a nhd of p).
    have h_eq : 𝓝[<] p = 𝓝[Ioo a p] p := by
      rw [← Set.Iio_inter_Ioi (a := p) (b := a),
        nhdsWithin_inter_of_mem'
          (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ha_lt))]
    have h_at_p : Tendsto (derivWithin γ.toPath.extend (Icc a p))
        (𝓝[Icc a p] p) (𝓝 L) := h_dw_cont p (right_mem_Icc.mpr ha_lt.le)
    have h_dw_iio : Tendsto (derivWithin γ.toPath.extend (Icc a p))
        (𝓝[<] p) (𝓝 L) := by
      rw [h_eq]
      exact h_at_p.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
    refine h_dw_iio.congr' ?_
    rw [h_eq]
    refine Filter.eventuallyEq_of_mem (s := Ioo a p) self_mem_nhdsWithin ?_
    intro u hu
    exact ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo _ hu
  right_deriv_limit := by
    intro p hp
    obtain ⟨_, hp_lt_1, hp_in⟩ := γ.toClosedPwC1Curve.legacy_mem_unpack hp
    obtain ⟨b, hcons⟩ := γ.exists_successor hp_in hp_lt_1
    have hp_lt_b : p < b := hcons.2.2.1
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc p b) := γ.contDiffOn_pieces p b hcons
    have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc p b)) (Icc p b) :=
      ContDiffOn.continuousOn_derivWithin hcd (uniqueDiffOn_Icc hp_lt_b) le_rfl
    set L := derivWithin γ.toPath.extend (Icc p b) p
    have hL_ne : L ≠ 0 :=
      γ.derivWithin_ne_zero_pieces p b hcons p (left_mem_Icc.mpr hp_lt_b.le)
    refine ⟨L, hL_ne, ?_⟩
    have h_eq : 𝓝[>] p = 𝓝[Ioo p b] p := by
      rw [← Set.Ioi_inter_Iio (a := p) (b := b),
        nhdsWithin_inter_of_mem'
          (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hp_lt_b))]
    have h_at_p : Tendsto (derivWithin γ.toPath.extend (Icc p b))
        (𝓝[Icc p b] p) (𝓝 L) := h_dw_cont p (left_mem_Icc.mpr hp_lt_b.le)
    have h_dw_ioi : Tendsto (derivWithin γ.toPath.extend (Icc p b))
        (𝓝[>] p) (𝓝 L) := by
      rw [h_eq]
      exact h_at_p.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
    refine h_dw_ioi.congr' ?_
    rw [h_eq]
    refine Filter.eventuallyEq_of_mem (s := Ioo p b) self_mem_nhdsWithin ?_
    intro u hu
    exact ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo _ hu

end ClosedPwC1Immersion

/-! ## Phase 1 — Lipschitz constant from `ClosedPwC1Curve`

A paper-faithful piecewise-C¹ curve has bounded derivative on each closed
piece (continuity on compact), and by gluing across pieces we obtain a
global Lipschitz constant for `γ.toPath.extend : ℝ → E`. -/

/-- Glue two `LipschitzOnWith` results across a shared midpoint. -/
private lemma lipschitzOnWith_Icc_trans {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b c : ℝ} {C : NNReal}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hf₁ : LipschitzOnWith C f (Icc a b))
    (hf₂ : LipschitzOnWith C f (Icc b c)) :
    LipschitzOnWith C f (Icc a c) := by
  rw [lipschitzOnWith_iff_norm_sub_le] at hf₁ hf₂ ⊢
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · rcases le_total y b with hyb | hby
    · exact hf₁ ⟨hx.1, hxy.trans hyb⟩ ⟨hx.1.trans hxy, hyb⟩
    · rcases le_total x b with hxb | hbx
      · -- x ≤ b ≤ y: split
        have hb_in_left : b ∈ Icc a b := ⟨hab, le_refl b⟩
        have hb_in_right : b ∈ Icc b c := ⟨le_refl b, hbc⟩
        have h1 := hf₁ ⟨hx.1, hxb⟩ hb_in_left
        have h2 := hf₂ hb_in_right ⟨hby, hy.2⟩
        have h_norm : ‖f x - f y‖ ≤ ‖f x - f b‖ + ‖f b - f y‖ := by
          have heq : f x - f y = (f x - f b) + (f b - f y) := by abel
          calc ‖f x - f y‖ = ‖(f x - f b) + (f b - f y)‖ := by rw [heq]
            _ ≤ ‖f x - f b‖ + ‖f b - f y‖ := norm_add_le _ _
        have h_dist : ‖x - y‖ = ‖x - b‖ + ‖b - y‖ := by
          have hxy_neg : x - y ≤ 0 := by linarith
          have hxb_neg : x - b ≤ 0 := by linarith
          have hby_neg : b - y ≤ 0 := by linarith
          rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonpos hxy_neg, abs_of_nonpos hxb_neg, abs_of_nonpos hby_neg]
          ring
        calc ‖f x - f y‖
            ≤ ‖f x - f b‖ + ‖f b - f y‖ := h_norm
          _ ≤ (C : ℝ) * ‖x - b‖ + (C : ℝ) * ‖b - y‖ := by gcongr
          _ = (C : ℝ) * (‖x - b‖ + ‖b - y‖) := by ring
          _ = (C : ℝ) * ‖x - y‖ := by rw [← h_dist]
      · exact hf₂ ⟨hbx, hx.2⟩ ⟨hbx.trans hxy, hy.2⟩
  · -- y ≤ x: by symmetry
    rw [show ‖f x - f y‖ = ‖f y - f x‖ from by rw [norm_sub_rev],
        show ‖x - y‖ = ‖y - x‖ from by rw [norm_sub_rev]]
    rcases le_total x b with hxb | hbx
    · exact hf₁ ⟨hy.1, hxy.trans hxb⟩ ⟨hy.1.trans hxy, hxb⟩
    · rcases le_total y b with hyb | hby
      · -- y ≤ b ≤ x: split (symmetric to above)
        have hb_in_left : b ∈ Icc a b := ⟨hab, le_refl b⟩
        have hb_in_right : b ∈ Icc b c := ⟨le_refl b, hbc⟩
        have h1 := hf₁ ⟨hy.1, hyb⟩ hb_in_left
        have h2 := hf₂ hb_in_right ⟨hbx, hx.2⟩
        have h_norm : ‖f y - f x‖ ≤ ‖f y - f b‖ + ‖f b - f x‖ := by
          have heq : f y - f x = (f y - f b) + (f b - f x) := by abel
          calc ‖f y - f x‖ = ‖(f y - f b) + (f b - f x)‖ := by rw [heq]
            _ ≤ ‖f y - f b‖ + ‖f b - f x‖ := norm_add_le _ _
        have h_dist : ‖y - x‖ = ‖y - b‖ + ‖b - x‖ := by
          have hyx_neg : y - x ≤ 0 := by linarith
          have hyb_neg : y - b ≤ 0 := by linarith
          have hbx_neg : b - x ≤ 0 := by linarith
          rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonpos hyx_neg, abs_of_nonpos hyb_neg, abs_of_nonpos hbx_neg]
          ring
        calc ‖f y - f x‖
            ≤ ‖f y - f b‖ + ‖f b - f x‖ := h_norm
          _ ≤ (C : ℝ) * ‖y - b‖ + (C : ℝ) * ‖b - x‖ := by gcongr
          _ = (C : ℝ) * (‖y - b‖ + ‖b - x‖) := by ring
          _ = (C : ℝ) * ‖y - x‖ := by rw [← h_dist]
      · exact hf₂ ⟨hby, hy.2⟩ ⟨hby.trans hxy, hx.2⟩

/-- Inductive gluing: piecewise-`LipschitzOnWith` on consecutive pieces yields
global `LipschitzOnWith` on `Icc a b` containing all pieces. -/
private lemma lipschitzOnWith_of_consecutive_pieces {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {C : NNReal} :
    ∀ s : Finset ℝ, ∀ a b : ℝ, a ∈ s → b ∈ s → a ≤ b →
      (∀ c ∈ s, a ≤ c ∧ c ≤ b) →
      (∀ p q, s.IsConsecutive p q → LipschitzOnWith C f (Icc p q)) →
      LipschitzOnWith C f (Icc a b) := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro a b ha hb hab hbds hpc
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · subst hab_eq
      rw [lipschitzOnWith_iff_norm_sub_le]
      intro x hx y hy
      have hx_eq : x = a := le_antisymm hx.2 hx.1
      have hy_eq : y = a := le_antisymm hy.2 hy.1
      simp [hx_eq, hy_eq]
    set t : Finset ℝ := s.filter (a < ·) with ht_def
    have hb_in_t : b ∈ t := Finset.mem_filter.mpr ⟨hb, hab_lt⟩
    set a' := t.min' ⟨b, hb_in_t⟩
    have ha'_in_t : a' ∈ t := t.min'_mem _
    have ha'_in_s : a' ∈ s := (Finset.mem_filter.mp ha'_in_t).1
    have ha_lt_a' : a < a' := (Finset.mem_filter.mp ha'_in_t).2
    have hcons : s.IsConsecutive a a' := by
      refine ⟨ha, ha'_in_s, ha_lt_a', ?_⟩
      intro c hc hc_Ioo
      exact absurd (t.min'_le c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.1⟩))
        (by linarith [hc_Ioo.2])
    have hL_aa' : LipschitzOnWith C f (Icc a a') := hpc _ _ hcons
    set s' : Finset ℝ := s.erase a with hs'_def
    have hs'_ssub : s' ⊂ s := Finset.erase_ssubset ha
    have ha'_in_s' : a' ∈ s' :=
      Finset.mem_erase.mpr ⟨ne_of_gt ha_lt_a', ha'_in_s⟩
    have hb_in_s' : b ∈ s' := Finset.mem_erase.mpr ⟨ne_of_gt hab_lt, hb⟩
    have ha'_le_b : a' ≤ b := t.min'_le b hb_in_t
    have hbds' : ∀ c ∈ s', a' ≤ c ∧ c ≤ b := by
      intro c hc
      have hc_in : c ∈ s := (Finset.mem_erase.mp hc).2
      have hc_ne : c ≠ a := (Finset.mem_erase.mp hc).1
      refine ⟨?_, (hbds c hc_in).2⟩
      have hac : a < c := lt_of_le_of_ne (hbds c hc_in).1 (Ne.symm hc_ne)
      exact t.min'_le _ (Finset.mem_filter.mpr ⟨hc_in, hac⟩)
    have hpc' : ∀ p q, s'.IsConsecutive p q → LipschitzOnWith C f (Icc p q) := by
      intro p q hcons'
      refine hpc p q ⟨?_, ?_, hcons'.2.2.1, ?_⟩
      · exact (Finset.mem_erase.mp hcons'.1).2
      · exact (Finset.mem_erase.mp hcons'.2.1).2
      · intro c hc hc_Ioo
        have hp_ge_a' : a' ≤ p := (hbds' p hcons'.1).1
        have hp_gt_a : a < p := lt_of_lt_of_le ha_lt_a' hp_ge_a'
        have hc_gt_a : a < c := lt_of_lt_of_le hp_gt_a hc_Ioo.1.le
        exact hcons'.2.2.2 c
          (Finset.mem_erase.mpr ⟨ne_of_gt hc_gt_a, hc⟩) hc_Ioo
    have hL_a'b : LipschitzOnWith C f (Icc a' b) :=
      ih s' hs'_ssub a' b ha'_in_s' hb_in_s' ha'_le_b hbds' hpc'
    exact lipschitzOnWith_Icc_trans ha_lt_a'.le ha'_le_b hL_aa' hL_a'b

namespace ClosedPwC1Curve

variable {x : E}

/-- On each closed piece between consecutive partition members, `γ.toPath.extend`
is Lipschitz with the maximum of `‖derivWithin γ.toPath.extend (Icc a b) t‖`
on the piece. -/
theorem lipschitzOnWith_piece (γ : ClosedPwC1Curve x) {a b : ℝ}
    (h : γ.partition.IsConsecutive a b) :
    ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc a b) := by
  have hab : a ≤ b := h.2.2.1.le
  have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b h
  have h_uniq : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc h.2.2.1
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    ContDiffOn.continuousOn_derivWithin hcd h_uniq le_rfl
  have h_diff : DifferentiableOn ℝ γ.toPath.extend (Icc a b) :=
    hcd.differentiableOn_one
  -- Compact + continuous norm has a max
  have h_norm_cont : ContinuousOn (fun t => ‖derivWithin γ.toPath.extend (Icc a b) t‖)
      (Icc a b) := h_dw_cont.norm
  obtain ⟨t₀, ht₀_in, ht₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨a, left_mem_Icc.mpr hab⟩ h_norm_cont
  set M := ‖derivWithin γ.toPath.extend (Icc a b) t₀‖
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  set K : NNReal := ⟨M, hM_nonneg⟩
  refine ⟨K, ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_derivWithin_le (convex_Icc _ _) h_diff
  intro u hu
  exact ht₀_max hu

/-- Existence of a global Lipschitz constant on `Icc 0 1`, by gluing the
piece-wise constants. -/
theorem lipschitzOnWith_Icc01 (γ : ClosedPwC1Curve x) :
    ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc (0 : ℝ) 1) := by
  classical
  set pairs : Finset (ℝ × ℝ) := (γ.partition.product γ.partition).filter
    (fun p => γ.partition.IsConsecutive p.1 p.2)
  -- For each consecutive pair, pick a Lipschitz constant via `lipschitzOnWith_piece`.
  have h_each : ∀ p ∈ pairs, ∃ K : NNReal,
      LipschitzOnWith K γ.toPath.extend (Icc p.1 p.2) := fun p hp =>
    γ.lipschitzOnWith_piece (Finset.mem_filter.mp hp).2
  choose K hK using h_each
  -- Take the supremum
  set Kmax : NNReal := pairs.attach.sup (fun p => K p.1 p.2)
  refine ⟨Kmax, ?_⟩
  have hpieces : ∀ p q, γ.partition.IsConsecutive p q →
      LipschitzOnWith Kmax γ.toPath.extend (Icc p q) := by
    intro p q hcons
    have hp_in : p ∈ γ.partition := hcons.1
    have hq_in : q ∈ γ.partition := hcons.2.1
    have hpq_in : (p, q) ∈ pairs := Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp_in, hq_in⟩, hcons⟩
    have hK_le : K (p, q) hpq_in ≤ Kmax :=
      Finset.le_sup (s := pairs.attach) (f := fun p => K p.1 p.2)
        (Finset.mem_attach pairs ⟨(p, q), hpq_in⟩)
    exact (hK (p, q) hpq_in).weaken hK_le
  exact lipschitzOnWith_of_consecutive_pieces γ.partition 0 1
    γ.zero_mem_partition γ.one_mem_partition zero_le_one
    (fun _ hc => ⟨(γ.partition_subset hc).1, (γ.partition_subset hc).2⟩)
    hpieces

/-- A `ClosedPwC1Curve` extends to a globally Lipschitz function `ℝ → E`.
Outside `[0, 1]`, the extended path is constant. -/
theorem lipschitzWith_extend (γ : ClosedPwC1Curve x) :
    ∃ K : NNReal, LipschitzWith K γ.toPath.extend := by
  obtain ⟨K, hK⟩ := γ.lipschitzOnWith_Icc01
  rw [lipschitzOnWith_iff_norm_sub_le] at hK
  refine ⟨K, ?_⟩
  rw [lipschitzWith_iff_norm_sub_le]
  intro s t
  -- The clamp s' := projIcc 0 1 _ s ∈ Icc 0 1, similarly t'.
  -- γ.extend s = γ.toPath.toFun s' = γ.extend s' for s' ∈ Icc 0 1.
  -- |s' - t'| ≤ |s - t| since projIcc is 1-Lipschitz.
  -- ‖γ.extend s - γ.extend t‖ = ‖γ.extend s' - γ.extend t'‖ ≤ K |s' - t'| ≤ K |s - t|.
  set s' : ℝ := max 0 (min s 1)
  set t' : ℝ := max 0 (min t 1)
  have hs'_in : s' ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have ht'_in : t' ∈ Icc (0 : ℝ) 1 :=
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  -- γ.extend s = γ.extend s'
  have hs_eq : γ.toPath.extend s = γ.toPath.extend s' := by
    rcases le_total s 0 with hs0 | hs0
    · -- s ≤ 0: extend s = x, s' = max 0 (min s 1) = 0 (since s ≤ 0 ≤ 1, min = s, max = 0).
      have hs'_eq : s' = 0 := by simp [s', min_eq_left (hs0.trans zero_le_one), max_eq_left hs0]
      rw [γ.toPath.extend_of_le_zero hs0, hs'_eq, γ.toPath.extend_zero]
    · rcases le_total s 1 with hs1 | hs1
      · -- 0 ≤ s ≤ 1: s' = s
        have hs'_eq : s' = s := by simp [s', min_eq_left hs1, max_eq_right hs0]
        rw [hs'_eq]
      · -- s ≥ 1: extend s = γ 1 = x (closed); s' = 1.
        have hs'_eq : s' = 1 := by
          simp [s', min_eq_right hs1]
        rw [γ.toPath.extend_of_one_le hs1, hs'_eq, γ.toPath.extend_one]
  -- γ.extend t = γ.extend t' (same argument)
  have ht_eq : γ.toPath.extend t = γ.toPath.extend t' := by
    rcases le_total t 0 with ht0 | ht0
    · have ht'_eq : t' = 0 := by simp [t', min_eq_left (ht0.trans zero_le_one), max_eq_left ht0]
      rw [γ.toPath.extend_of_le_zero ht0, ht'_eq, γ.toPath.extend_zero]
    · rcases le_total t 1 with ht1 | ht1
      · have ht'_eq : t' = t := by simp [t', min_eq_left ht1, max_eq_right ht0]
        rw [ht'_eq]
      · have ht'_eq : t' = 1 := by
          simp [t', min_eq_right ht1]
        rw [γ.toPath.extend_of_one_le ht1, ht'_eq, γ.toPath.extend_one]
  -- Bound |s' - t'| by |s - t|: clamping is 1-Lipschitz
  have h_proj_lip : ‖s' - t'‖ ≤ ‖s - t‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    -- |max 0 (min s 1) - max 0 (min t 1)| ≤ max |0 - 0| |min s 1 - min t 1|
    --                                      = |min s 1 - min t 1|
    --                                      ≤ max |s - t| |1 - 1| = |s - t|
    calc |s' - t'|
        = |max 0 (min s 1) - max 0 (min t 1)| := rfl
      _ ≤ max |(0 : ℝ) - 0| |min s 1 - min t 1| := abs_max_sub_max_le_max _ _ _ _
      _ = |min s 1 - min t 1| := by simp
      _ ≤ max |s - t| |(1 : ℝ) - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = |s - t| := by simp
  -- Combine
  rw [hs_eq, ht_eq]
  calc ‖γ.toPath.extend s' - γ.toPath.extend t'‖
      ≤ (K : ℝ) * ‖s' - t'‖ := hK hs'_in ht'_in
    _ ≤ (K : ℝ) * ‖s - t‖ :=
        mul_le_mul_of_nonneg_left h_proj_lip (NNReal.coe_nonneg _)

end ClosedPwC1Curve

namespace ClosedPwC1Immersion

variable {x : E}

/-- A `ClosedPwC1Immersion` extends to a globally Lipschitz function `ℝ → E`. -/
theorem lipschitzWith_extend (γ : ClosedPwC1Immersion x) :
    ∃ K : NNReal, LipschitzWith K γ.toPath.extend :=
  γ.toClosedPwC1Curve.lipschitzWith_extend

end ClosedPwC1Immersion

/-! ## Phase 2 — Cyclic shift of a closed piecewise-`C¹` immersion (T-BR-Y8c)

For a closed piecewise-`C¹` immersion `γ : ClosedPwC1Immersion x` and a parameter
`τ ∈ Ioo 0 1`, the **cyclic shift** is a reparametrization that starts the contour
at `γ(τ)` instead of `γ(0) = x`. The shifted curve `γ'(t)` is defined by:

  γ'(t) = γ(t + τ)      for `t ∈ [0, 1 - τ]`
  γ'(t) = γ(t + τ - 1)  for `t ∈ [1 - τ, 1]`

At `t = 1 - τ`, both pieces give `γ(1) = γ(0) = x` (closedness), so the path is
continuous. The point `1 - τ` becomes a new partition corner.

This file ships:
* `cyclicShiftFun γ τ` — the raw piecewise function `ℝ → E`
* `cyclicShiftFun_zero`, `cyclicShiftFun_one` — endpoint values
* `Continuous.cyclicShiftFun` — continuity

The full `ClosedPwC1Immersion.cyclicShift` constructor and the invariance lemmas
for `HasCauchyPVOn` and `generalizedWindingNumber` are built on top of this. -/

/-- The cyclic-shift function on `ℝ`: for a closed loop `f` based at `x` (i.e.
`f(0) = f(1) = x`) and a shift parameter `τ`, `cyclicShiftFun f τ t` is:
- `f(t + τ)` when `t + τ ≤ 1` (i.e. `t ≤ 1 - τ`)
- `f(t + τ - 1)` when `t + τ ≥ 1` (i.e. `t ≥ 1 - τ`)

Outside `[0, 1]`, the function naturally extends as a constant via the underlying
`f = γ.toPath.extend` being constant on `(-∞, 0]` and `[1, ∞)`. -/
noncomputable def cyclicShiftFun (f : ℝ → E) (τ : ℝ) : ℝ → E :=
  fun t => if t + τ ≤ 1 then f (t + τ) else f (t + τ - 1)

variable {x : E}

omit [NormedSpace ℝ E] in
/-- Value of `cyclicShiftFun` at `0` (in `Ioo 0 1`): equals `f τ`. -/
@[simp]
theorem cyclicShiftFun_zero (f : ℝ → E) {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    cyclicShiftFun f τ 0 = f τ := by
  simp only [cyclicShiftFun, zero_add, if_pos hτ.2.le]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Value of `cyclicShiftFun` at `1`: equals `f τ` whenever `τ ∈ (0, 1)` and
`f(0) = f(1)` (i.e. for closed loops). -/
theorem cyclicShiftFun_one (f : ℝ → E) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) (_hclosed : f 0 = f 1) :
    cyclicShiftFun f τ 1 = f τ := by
  unfold cyclicShiftFun
  -- `1 + τ ≤ 1` is false when `τ > 0`. So we take the else branch.
  have h_not : ¬ (1 + τ ≤ 1) := by linarith [hτ.1]
  rw [if_neg h_not]
  -- The result is `f (1 + τ - 1) = f τ`.
  congr 1; ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Value of `cyclicShiftFun` at `t = 1 - τ`: both pieces agree and equal `f(1)`. -/
theorem cyclicShiftFun_at_breakpoint (f : ℝ → E) (τ : ℝ) :
    cyclicShiftFun f τ (1 - τ) = f 1 := by
  unfold cyclicShiftFun
  -- `(1 - τ) + τ = 1`, so the condition is `1 ≤ 1` which is true.
  rw [if_pos (by linarith : (1 - τ) + τ ≤ 1)]
  congr 1; ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The `else`-branch limit at `1 - τ`: gives `f 0`. -/
theorem cyclicShiftFun_at_breakpoint_else (f : ℝ → E) (τ : ℝ) :
    f ((1 - τ) + τ - 1) = f 0 := by
  congr 1; ring

omit [NormedSpace ℝ E] in
/-- Continuity of `cyclicShiftFun` for a continuous closed loop. -/
theorem Continuous.cyclicShiftFun {f : ℝ → E} (hf : Continuous f) {τ : ℝ}
    (hclosed : f 0 = f 1) : Continuous (cyclicShiftFun f τ) := by
  -- Decompose: g(t) = if t + τ ≤ 1 then f (t + τ) else f (t + τ - 1).
  -- At the gluing point t + τ = 1: f(t+τ) = f(1) = f(0) = f(t+τ-1). ✓
  show Continuous (fun t => if t + τ ≤ 1 then f (t + τ) else f (t + τ - 1))
  -- Apply `Continuous.if_le` with `f := (· + τ)`, `g := const 1`,
  -- `f' := fun t => f (t + τ)`, `g' := fun t => f (t + τ - 1)`.
  apply Continuous.if_le (f' := fun t => f (t + τ)) (g' := fun t => f (t + τ - 1))
    (f := fun t => t + τ) (g := fun _ => (1 : ℝ))
  · exact hf.comp (by fun_prop)
  · exact hf.comp (by fun_prop)
  · fun_prop
  · exact continuous_const
  -- Matching condition at `t + τ = 1`.
  intro t ht_eq
  rw [ht_eq, show (1 : ℝ) - 1 = 0 from by ring]
  exact hclosed.symm

/-- The cyclic-shift function preserves "closedness": `g(0) = g(1) = f(τ)`. -/
theorem cyclicShiftFun_closed (f : ℝ → E) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) (hclosed : f 0 = f 1) :
    cyclicShiftFun f τ 0 = cyclicShiftFun f τ 1 := by
  rw [cyclicShiftFun_zero f hτ, cyclicShiftFun_one f hτ hclosed]

/-! ### `cyclicShiftPath` — building a `Path` -/

/-- The cyclic-shift `Path` from `γ(τ)` to `γ(τ)`. -/
noncomputable def Path.cyclicShift {x : E} (γ : Path x x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) : Path (γ.extend τ) (γ.extend τ) where
  toFun := fun t => cyclicShiftFun γ.extend τ (t : ℝ)
  continuous_toFun := by
    have h_outer : Continuous (cyclicShiftFun γ.extend τ) :=
      Continuous.cyclicShiftFun γ.continuous_extend
        (by rw [γ.extend_zero, γ.extend_one])
    exact h_outer.comp continuous_subtype_val
  source' := by
    simp only [Set.Icc.coe_zero]
    exact cyclicShiftFun_zero γ.extend hτ
  target' := by
    simp only [Set.Icc.coe_one]
    exact cyclicShiftFun_one γ.extend hτ
      (by rw [γ.extend_zero, γ.extend_one])

/-- Endpoints of `Path.cyclicShift`. -/
theorem Path.cyclicShift_apply {x : E} (γ : Path x x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) (t : ↑(Set.Icc (0 : ℝ) 1)) :
    γ.cyclicShift hτ t = cyclicShiftFun γ.extend τ (t : ℝ) := rfl

/-- The extend of `Path.cyclicShift` agrees with `cyclicShiftFun` on `[0, 1]`. -/
theorem Path.cyclicShift_extend_on_Icc {x : E} (γ : Path x x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (γ.cyclicShift hτ).extend t = cyclicShiftFun γ.extend τ t := by
  rw [Path.extend_apply _ ht, Path.cyclicShift_apply]

/-! ### `cyclicShiftPath` — partition of the shifted curve

The partition of the shifted curve `γ'` consists of:
* `0`, `1`, and `1 - τ` (the new corner partition point);
* shifted-back partition points of `γ` itself.

Concretely, if `γ.partition = {0, p₁, p₂, …, pₙ, 1}` with `p₁ < … < pₙ`, and we
let `j` be the unique index where `p_{j-1} ≤ τ < p_j` (or `0 ≤ τ < p₁`, or
`pₙ ≤ τ ≤ 1`), then the partition of `γ'` is:

  `{0} ∪ {p_j - τ, p_{j+1} - τ, …, pₙ - τ} ∪ {1 - τ}`
  `   ∪ {1 - τ + p_1, 1 - τ + p_2, …, 1 - τ + p_{j-1}} ∪ {1}`

That is, partition points after `τ` get shifted to `p - τ`, and partition points
before `τ` get shifted to `p + (1 - τ)`, with `1 - τ` always added as a corner.

We construct this set via a simple translate+filter+union. -/

/-- The partition for the cyclic-shifted curve at shift `τ`. -/
noncomputable def cyclicShiftPartition (P : Finset ℝ) (τ : ℝ) : Finset ℝ :=
  ((P.image (fun p => p - τ)) ∪ (P.image (fun p => p - τ + 1)))
    |>.filter (fun t => t ∈ Set.Icc (0 : ℝ) 1)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A point `t ∈ Icc 0 1` lies in the cyclic-shift partition iff its "shifted-back"
representative `t + τ` or `t + τ - 1` is in the original partition. -/
theorem mem_cyclicShiftPartition_iff (P : Finset ℝ) (τ : ℝ) (t : ℝ) :
    t ∈ cyclicShiftPartition P τ ↔
      t ∈ Set.Icc (0 : ℝ) 1 ∧ ((t + τ ∈ P) ∨ (t + τ - 1 ∈ P)) := by
  unfold cyclicShiftPartition
  simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨h_or, ht_in⟩
    refine ⟨ht_in, ?_⟩
    rcases h_or with ⟨p, hp_in, hp_eq⟩ | ⟨p, hp_in, hp_eq⟩
    · left; rw [← hp_eq]; convert hp_in using 1; ring
    · right; rw [← hp_eq]; convert hp_in using 1; ring
  · rintro ⟨ht_in, ht_or⟩
    refine ⟨?_, ht_in⟩
    rcases ht_or with hp | hp
    · left; refine ⟨t + τ, hp, by ring⟩
    · right; refine ⟨t + τ - 1, hp, by ring⟩

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The cyclic-shift partition lies inside `Icc 0 1`. -/
theorem cyclicShiftPartition_subset_Icc (P : Finset ℝ) (τ : ℝ) :
    ((cyclicShiftPartition P τ : Finset ℝ) : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  have : t ∈ cyclicShiftPartition P τ := ht
  exact ((mem_cyclicShiftPartition_iff P τ t).mp this).1

/-! ### Consecutive-pair lifting under cyclic shift (T-BR-Y8d Step 1)

For a cyclic shift by `τ ∈ Ioo 0 1`, the *new* partition is
`cyclicShiftPartition γ.partition τ ∪ {0, 1, 1 - τ}`. For each consecutive pair
`(a, b)` in the new partition, either:

* `b ≤ 1 - τ`, in which case `[a + τ, b + τ] ⊆ Icc c d` for some consecutive
  pair `(c, d)` in `γ.partition ∪ {τ}`, hence `[a + τ, b + τ]` is contained in a
  single original γ-piece (possibly subdivided by `τ`); OR
* `a ≥ 1 - τ`, in which case `[a + τ - 1, b + τ - 1] ⊆ Icc c d` for some
  consecutive pair in `γ.partition ∪ {τ}`.

The straddle case `a < 1 - τ < b` is impossible because `1 - τ` is added to the
new partition explicitly. -/

/-- The cyclic-shift augmented partition: includes `0`, `1`, and the cyclic-shift
breakpoint `1 - τ`. This is the actual partition we use for the shifted curve. -/
noncomputable def cyclicShiftPartitionExt (P : Finset ℝ) (τ : ℝ) : Finset ℝ :=
  insert 0 (insert 1 (insert (1 - τ) (cyclicShiftPartition P τ)))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem mem_cyclicShiftPartitionExt_iff (P : Finset ℝ) (τ : ℝ) (t : ℝ) :
    t ∈ cyclicShiftPartitionExt P τ ↔
      t = 0 ∨ t = 1 ∨ t = 1 - τ ∨ t ∈ cyclicShiftPartition P τ := by
  unfold cyclicShiftPartitionExt
  simp [Finset.mem_insert]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cyclicShiftPartitionExt_subset_Icc (P : Finset ℝ) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ((cyclicShiftPartitionExt P τ : Finset ℝ) : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1 := by
  intro t ht
  rcases (mem_cyclicShiftPartitionExt_iff P τ t).mp ht with rfl | rfl | rfl | h
  · exact ⟨le_refl _, zero_le_one⟩
  · exact ⟨zero_le_one, le_refl _⟩
  · exact ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  · exact cyclicShiftPartition_subset_Icc P τ h

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem zero_mem_cyclicShiftPartitionExt (P : Finset ℝ) (τ : ℝ) :
    (0 : ℝ) ∈ cyclicShiftPartitionExt P τ := by
  rw [mem_cyclicShiftPartitionExt_iff]; tauto

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem one_mem_cyclicShiftPartitionExt (P : Finset ℝ) (τ : ℝ) :
    (1 : ℝ) ∈ cyclicShiftPartitionExt P τ := by
  rw [mem_cyclicShiftPartitionExt_iff]; tauto

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp]
theorem oneSubTau_mem_cyclicShiftPartitionExt (P : Finset ℝ) (τ : ℝ) :
    (1 - τ : ℝ) ∈ cyclicShiftPartitionExt P τ := by
  rw [mem_cyclicShiftPartitionExt_iff]; tauto

/-- Given a consecutive pair `(a, b)` in `cyclicShiftPartitionExt`, the new
partition does not straddle `1 - τ` (since `1 - τ` itself is in the partition). -/
private theorem not_straddle_oneSubTau (P : Finset ℝ) {τ : ℝ}
    {a b : ℝ} (h_cons : (cyclicShiftPartitionExt P τ).IsConsecutive a b) :
    b ≤ 1 - τ ∨ a ≥ 1 - τ := by
  by_contra h
  push_neg at h
  obtain ⟨h_lt_b, h_a_lt⟩ := h
  exact h_cons.2.2.2 (1 - τ) (oneSubTau_mem_cyclicShiftPartitionExt P τ) ⟨h_a_lt, h_lt_b⟩

namespace ClosedPwC1Curve

variable {x : E}

/-- **Step 1: cyclicShift consecutive lift (case 1, no wraparound).** For a
consecutive pair `(a, b)` in the cyclic-shift partition with `b ≤ 1 - τ`, the
interval `[a + τ, b + τ]` lies inside a γ-piece of the original partition. -/
theorem cyclicShift_consecutive_lift_no_wrap (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b)
    (h_b_le : b ≤ 1 - τ) :
    ∃ c d, γ.partition.IsConsecutive c d ∧ Icc (a + τ) (b + τ) ⊆ Icc c d := by
  classical
  obtain ⟨ha_in, hb_in, h_ab_lt, h_no_between⟩ := h_cons
  -- a ∈ Icc 0 1 and b ∈ Icc 0 1.
  have ha_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ ha_in
  have hb_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ hb_in
  have ha_ge : 0 ≤ a := ha_Icc.1
  -- a + τ ∈ [τ, 1], b + τ ∈ (τ, 1].
  have h_aT_ge : τ ≤ a + τ := by linarith
  have h_bT_le : b + τ ≤ 1 := by linarith
  -- Define c := max {p ∈ γ.partition : p ≤ a + τ}.
  set Pl : Finset ℝ := γ.partition.filter (· ≤ a + τ) with hPl_def
  -- If a + τ ≥ τ ≥ 0, and 0 ∈ γ.partition, then 0 ∈ Pl.
  have h0_in_Pl : (0 : ℝ) ∈ Pl := by
    refine Finset.mem_filter.mpr ⟨γ.zero_mem_partition, ?_⟩
    linarith [hτ.1]
  set c : ℝ := Pl.max' ⟨0, h0_in_Pl⟩ with hc_def
  have hc_mem : c ∈ Pl := Pl.max'_mem _
  have hc_in_P : c ∈ γ.partition := (Finset.mem_filter.mp hc_mem).1
  have hc_le : c ≤ a + τ := (Finset.mem_filter.mp hc_mem).2
  -- Define d := min {p ∈ γ.partition : p ≥ b + τ}.
  set Pr : Finset ℝ := γ.partition.filter (b + τ ≤ ·) with hPr_def
  have h1_in_Pr : (1 : ℝ) ∈ Pr := Finset.mem_filter.mpr ⟨γ.one_mem_partition, h_bT_le⟩
  set d : ℝ := Pr.min' ⟨1, h1_in_Pr⟩ with hd_def
  have hd_mem : d ∈ Pr := Pr.min'_mem _
  have hd_in_P : d ∈ γ.partition := (Finset.mem_filter.mp hd_mem).1
  have hd_ge : b + τ ≤ d := (Finset.mem_filter.mp hd_mem).2
  -- c ≤ a + τ < b + τ ≤ d, so c < d.
  have hcd_lt : c < d := lt_of_le_of_lt hc_le (lt_of_lt_of_le (by linarith : a + τ < b + τ) hd_ge)
  -- Show (c, d) consecutive in γ.partition.
  refine ⟨c, d, ⟨hc_in_P, hd_in_P, hcd_lt, ?_⟩, ?_⟩
  · -- No γ-partition element strictly between c and d.
    intro e he_in he_Ioo
    -- If e ≤ a + τ: then e ∈ Pl, so e ≤ c. But e > c, contradiction.
    rcases le_or_gt e (a + τ) with he_le | he_gt
    · have he_in_Pl : e ∈ Pl := Finset.mem_filter.mpr ⟨he_in, he_le⟩
      exact absurd (Pl.le_max' e he_in_Pl) (not_le_of_gt he_Ioo.1)
    -- If e ≥ b + τ: then e ∈ Pr, so d ≤ e. But e < d, contradiction.
    rcases le_or_gt (b + τ) e with he_ge | he_lt
    · have he_in_Pr : e ∈ Pr := Finset.mem_filter.mpr ⟨he_in, he_ge⟩
      exact absurd (Pr.min'_le e he_in_Pr) (not_le_of_gt he_Ioo.2)
    -- Otherwise a + τ < e < b + τ, hence a < e - τ < b.
    -- And e - τ ∈ Icc 0 1 (since τ ≤ a + τ < e < b + τ ≤ 1, so 0 < e - τ < 1 - τ ≤ 1).
    have h_e_in_Icc : e - τ ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [hτ.1, ha_ge]
      · linarith [hτ.1, h_b_le]
    have h_e_minus_tau_in_csp : e - τ ∈ cyclicShiftPartition γ.partition τ := by
      rw [mem_cyclicShiftPartition_iff]
      refine ⟨h_e_in_Icc, Or.inl ?_⟩
      convert he_in using 1
      ring
    have h_e_minus_tau_in_Q : e - τ ∈ cyclicShiftPartitionExt γ.partition τ := by
      rw [mem_cyclicShiftPartitionExt_iff]
      tauto
    have h_in_Ioo : e - τ ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
    exact h_no_between (e - τ) h_e_minus_tau_in_Q h_in_Ioo
  · -- Subset claim: Icc (a + τ) (b + τ) ⊆ Icc c d.
    intro t ht
    exact ⟨hc_le.trans ht.1, ht.2.trans hd_ge⟩

/-- **Step 1: cyclicShift consecutive lift (case 2, with wraparound).** For a
consecutive pair `(a, b)` in the cyclic-shift partition with `a ≥ 1 - τ`, the
interval `[a + τ - 1, b + τ - 1]` lies inside a γ-piece of the original
partition. -/
theorem cyclicShift_consecutive_lift_wrap (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b)
    (h_a_ge : a ≥ 1 - τ) :
    ∃ c d, γ.partition.IsConsecutive c d ∧ Icc (a + τ - 1) (b + τ - 1) ⊆ Icc c d := by
  classical
  obtain ⟨ha_in, hb_in, h_ab_lt, h_no_between⟩ := h_cons
  have ha_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ ha_in
  have hb_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ hb_in
  have hb_le_1 : b ≤ 1 := hb_Icc.2
  -- a + τ - 1 ∈ [0, τ), b + τ - 1 ∈ (0, τ].
  have h_aT_ge : 0 ≤ a + τ - 1 := by linarith
  have h_bT_le : b + τ - 1 ≤ τ := by linarith
  -- c := max {p ∈ γ.partition : p ≤ a + τ - 1}, 0 ∈ since a + τ - 1 ≥ 0.
  set Pl : Finset ℝ := γ.partition.filter (· ≤ a + τ - 1) with hPl_def
  have h0_in_Pl : (0 : ℝ) ∈ Pl :=
    Finset.mem_filter.mpr ⟨γ.zero_mem_partition, h_aT_ge⟩
  set c : ℝ := Pl.max' ⟨0, h0_in_Pl⟩ with hc_def
  have hc_mem : c ∈ Pl := Pl.max'_mem _
  have hc_in_P : c ∈ γ.partition := (Finset.mem_filter.mp hc_mem).1
  have hc_le : c ≤ a + τ - 1 := (Finset.mem_filter.mp hc_mem).2
  -- d := min {p ∈ γ.partition : p ≥ b + τ - 1}, 1 ∈ since b + τ - 1 ≤ τ ≤ 1.
  set Pr : Finset ℝ := γ.partition.filter (b + τ - 1 ≤ ·) with hPr_def
  have h1_in_Pr : (1 : ℝ) ∈ Pr := by
    refine Finset.mem_filter.mpr ⟨γ.one_mem_partition, ?_⟩
    linarith [hτ.2]
  set d : ℝ := Pr.min' ⟨1, h1_in_Pr⟩ with hd_def
  have hd_mem : d ∈ Pr := Pr.min'_mem _
  have hd_in_P : d ∈ γ.partition := (Finset.mem_filter.mp hd_mem).1
  have hd_ge : b + τ - 1 ≤ d := (Finset.mem_filter.mp hd_mem).2
  have hcd_lt : c < d := lt_of_le_of_lt hc_le
    (lt_of_lt_of_le (by linarith : a + τ - 1 < b + τ - 1) hd_ge)
  refine ⟨c, d, ⟨hc_in_P, hd_in_P, hcd_lt, ?_⟩, ?_⟩
  · intro e he_in he_Ioo
    rcases le_or_gt e (a + τ - 1) with he_le | he_gt
    · have he_in_Pl : e ∈ Pl := Finset.mem_filter.mpr ⟨he_in, he_le⟩
      exact absurd (Pl.le_max' e he_in_Pl) (not_le_of_gt he_Ioo.1)
    rcases le_or_gt (b + τ - 1) e with he_ge | he_lt
    · have he_in_Pr : e ∈ Pr := Finset.mem_filter.mpr ⟨he_in, he_ge⟩
      exact absurd (Pr.min'_le e he_in_Pr) (not_le_of_gt he_Ioo.2)
    -- Otherwise a + τ - 1 < e < b + τ - 1. Then a < e + 1 - τ < b.
    -- And e + 1 - τ ∈ Icc 0 1.
    have h_shift_in_Icc : e + 1 - τ ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [hτ.2, h_a_ge]
      · linarith [hτ.1, hb_le_1]
    -- e + 1 - τ ∈ cyclicShiftPartition since (e + 1 - τ) + τ - 1 = e ∈ γ.partition.
    have h_csp : e + 1 - τ ∈ cyclicShiftPartition γ.partition τ := by
      rw [mem_cyclicShiftPartition_iff]
      refine ⟨h_shift_in_Icc, Or.inr ?_⟩
      convert he_in using 1
      ring
    have h_in_Q : e + 1 - τ ∈ cyclicShiftPartitionExt γ.partition τ := by
      rw [mem_cyclicShiftPartitionExt_iff]
      tauto
    have h_in_Ioo : e + 1 - τ ∈ Set.Ioo a b :=
      ⟨by linarith, by linarith⟩
    exact h_no_between (e + 1 - τ) h_in_Q h_in_Ioo
  · intro t ht
    exact ⟨hc_le.trans ht.1, ht.2.trans hd_ge⟩

/-- **Step 1 (combined): cyclicShift consecutive lift.** For a consecutive pair
`(a, b)` in the cyclic-shift partition, either there's no wraparound (`b ≤ 1-τ`)
and `[a + τ, b + τ]` lies in a γ-piece, or there is wraparound (`a ≥ 1-τ`) and
`[a + τ - 1, b + τ - 1]` lies in a γ-piece. -/
theorem cyclicShift_consecutive_lift (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b) :
    (b ≤ 1 - τ ∧
        ∃ c d, γ.partition.IsConsecutive c d ∧ Icc (a + τ) (b + τ) ⊆ Icc c d) ∨
    (a ≥ 1 - τ ∧
        ∃ c d, γ.partition.IsConsecutive c d ∧
          Icc (a + τ - 1) (b + τ - 1) ⊆ Icc c d) := by
  rcases not_straddle_oneSubTau γ.partition h_cons with h_b_le | h_a_ge
  · left
    refine ⟨h_b_le, ?_⟩
    exact γ.cyclicShift_consecutive_lift_no_wrap hτ h_cons h_b_le
  · right
    refine ⟨h_a_ge, ?_⟩
    exact γ.cyclicShift_consecutive_lift_wrap hτ h_cons h_a_ge

end ClosedPwC1Curve

/-! ### Step 2: `ClosedPwC1Curve.cyclicShift` constructor

We build the shifted curve as a paper-faithful `ClosedPwC1Curve`. The partition
is `cyclicShiftPartitionExt γ.partition τ` and the underlying path is
`γ.toPath.cyclicShift hτ`. The `ContDiffOn` field on each piece is established
by the consecutive-pair lift (Step 1). -/

/-- The cyclic-shifted curve agrees on `Icc 0 (1 - τ)` with the original curve
shifted by `+τ`. -/
private lemma cyclicShiftFun_eq_on_no_wrap (f : ℝ → E) {τ : ℝ}
    (_hτ : τ ∈ Ioo (0 : ℝ) 1) :
    Set.EqOn (cyclicShiftFun f τ) (fun t => f (t + τ)) (Icc (0 : ℝ) (1 - τ)) := by
  intro t ht
  simp only [cyclicShiftFun]
  rw [if_pos (by linarith [ht.2] : t + τ ≤ 1)]

/-- The cyclic-shifted curve agrees on `Icc (1 - τ) 1` with the original curve
shifted by `+τ - 1`, provided the curve is *closed* (`f 0 = f 1`). -/
private lemma cyclicShiftFun_eq_on_wrap (f : ℝ → E) {τ : ℝ}
    (_hτ : τ ∈ Ioo (0 : ℝ) 1) (hclosed : f 0 = f 1) :
    Set.EqOn (cyclicShiftFun f τ) (fun t => f (t + τ - 1))
      (Icc (1 - τ) 1) := by
  intro t ht
  simp only [cyclicShiftFun]
  rcases eq_or_lt_of_le ht.1 with h_eq | h_lt
  · -- t = 1 - τ: cyclicShiftFun gives f 1 (via if_pos with t + τ = 1)
    rw [if_pos (by linarith : t + τ ≤ 1)]
    -- f (t + τ) = f 1, and f (t + τ - 1) = f 0 = f 1
    have h1 : t + τ = 1 := by linarith
    have h2 : t + τ - 1 = 0 := by linarith
    rw [h1]; rw [show (1 : ℝ) - 1 = 0 from by ring]; exact hclosed.symm
  · -- t > 1 - τ: cyclicShiftFun gives f (t + τ - 1) via if_neg
    rw [if_neg (by linarith : ¬ (t + τ ≤ 1))]

namespace ClosedPwC1Curve

variable {x : E}

/-- The shifted curve is `ContDiffOn ℝ 1` on each consecutive piece (Step 2). -/
private theorem cyclicShift_extend_contDiffOn_piece (γ : ClosedPwC1Curve x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b) :
    ContDiffOn ℝ 1 (γ.toPath.cyclicShift hτ).extend (Icc a b) := by
  have ha_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ h_cons.1
  have hb_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ h_cons.2.1
  have hab_Icc : Icc a b ⊆ Icc (0:ℝ) 1 := fun t ht => ⟨ha_Icc.1.trans ht.1, ht.2.trans hb_Icc.2⟩
  have hclosed : γ.toPath.extend 0 = γ.toPath.extend 1 := by
    rw [γ.toPath.extend_zero, γ.toPath.extend_one]
  -- First, the shifted curve `(γ.toPath.cyclicShift hτ).extend` agrees with
  -- `cyclicShiftFun γ.toPath.extend τ` on `Icc 0 1`, hence on `Icc a b`.
  have h_eq_csf : Set.EqOn (γ.toPath.cyclicShift hτ).extend
      (cyclicShiftFun γ.toPath.extend τ) (Icc a b) := by
    intro t ht
    exact Path.cyclicShift_extend_on_Icc γ.toPath hτ (hab_Icc ht)
  -- Use the consecutive-pair lift to find a γ-piece containing the shifted interval.
  rcases γ.cyclicShift_consecutive_lift hτ h_cons with
    ⟨h_b_le, c, d, h_cons_cd, h_sub⟩ | ⟨h_a_ge, c, d, h_cons_cd, h_sub⟩
  · -- No wraparound: cyclicShiftFun = γ.extend ∘ (· + τ) on Icc a b ⊆ Icc 0 (1 - τ).
    have hab_sub : Icc a b ⊆ Icc (0:ℝ) (1 - τ) :=
      fun t ht => ⟨ha_Icc.1.trans ht.1, ht.2.trans h_b_le⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun t => γ.toPath.extend (t + τ)) (Icc a b) := by
      intro t ht
      rw [h_eq_csf ht]
      exact cyclicShiftFun_eq_on_no_wrap γ.toPath.extend hτ (hab_sub ht)
    -- ContDiffOn for γ.toPath.extend on Icc c d, pulled back via (· + τ).
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc c d) := γ.contDiffOn_pieces c d h_cons_cd
    have h_shift_contDiff : ContDiffOn ℝ 1 (fun t => γ.toPath.extend (t + τ)) (Icc a b) := by
      have h_shift_smooth : ContDiff ℝ 1 (fun t : ℝ => t + τ) :=
        contDiff_id.add contDiff_const
      have h_maps_to : MapsTo (fun t : ℝ => t + τ) (Icc a b) (Icc c d) := by
        intro t ht
        refine h_sub ⟨?_, ?_⟩
        · show a + τ ≤ t + τ; linarith [ht.1]
        · show t + τ ≤ b + τ; linarith [ht.2]
      exact hcd.comp h_shift_smooth.contDiffOn h_maps_to
    -- Transfer ContDiffOn back to (γ.toPath.cyclicShift hτ).extend via EqOn.
    exact h_shift_contDiff.congr (fun t ht => h_eq_shifted ht)
  · -- Wraparound: cyclicShiftFun = γ.extend ∘ (· + τ - 1) on Icc a b ⊆ Icc (1 - τ) 1.
    have hab_sub : Icc a b ⊆ Icc (1 - τ) 1 :=
      fun t ht => ⟨h_a_ge.trans ht.1, ht.2.trans hb_Icc.2⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun t => γ.toPath.extend (t + τ - 1)) (Icc a b) := by
      intro t ht
      rw [h_eq_csf ht]
      exact cyclicShiftFun_eq_on_wrap γ.toPath.extend hτ hclosed (hab_sub ht)
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc c d) := γ.contDiffOn_pieces c d h_cons_cd
    have h_shift_contDiff :
        ContDiffOn ℝ 1 (fun t => γ.toPath.extend (t + τ - 1)) (Icc a b) := by
      have h_shift_smooth : ContDiff ℝ 1 (fun t : ℝ => t + τ - 1) :=
        (contDiff_id.add contDiff_const).sub contDiff_const
      have h_maps_to : MapsTo (fun t : ℝ => t + τ - 1) (Icc a b) (Icc c d) := by
        intro t ht
        refine h_sub ⟨?_, ?_⟩
        · show a + τ - 1 ≤ t + τ - 1; linarith [ht.1]
        · show t + τ - 1 ≤ b + τ - 1; linarith [ht.2]
      exact hcd.comp h_shift_smooth.contDiffOn h_maps_to
    exact h_shift_contDiff.congr (fun t ht => h_eq_shifted ht)

/-- **Step 2: Cyclic shift of a `ClosedPwC1Curve`.** -/
noncomputable def cyclicShift (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ClosedPwC1Curve (γ.toPath.extend τ) where
  toPath := γ.toPath.cyclicShift hτ
  partition := cyclicShiftPartitionExt γ.partition τ
  zero_mem_partition := zero_mem_cyclicShiftPartitionExt γ.partition τ
  one_mem_partition := one_mem_cyclicShiftPartitionExt γ.partition τ
  partition_subset := cyclicShiftPartitionExt_subset_Icc γ.partition hτ
  contDiffOn_pieces := fun _ _ h_cons => γ.cyclicShift_extend_contDiffOn_piece hτ h_cons

end ClosedPwC1Curve

/-! ### Step 3: `ClosedPwC1Immersion.cyclicShift`

For an immersion, additionally we need `derivWithin _ (Icc a b) t ≠ 0` on each
piece. We obtain this from the original immersion's `derivWithin_ne_zero_pieces`
property by chain rule. -/

namespace ClosedPwC1Immersion

variable {x : E}

/-- On each piece of the cyclic shift, the (within-`Icc a b`) derivative is
nonzero. -/
private theorem cyclicShift_derivWithin_ne_zero_piece (γ : ClosedPwC1Immersion x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.partition τ).IsConsecutive a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    derivWithin (γ.toPath.cyclicShift hτ).extend (Icc a b) t ≠ 0 := by
  have ha_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ h_cons.1
  have hb_Icc := cyclicShiftPartitionExt_subset_Icc γ.partition hτ h_cons.2.1
  have hab_Icc : Icc a b ⊆ Icc (0:ℝ) 1 :=
    fun u hu => ⟨ha_Icc.1.trans hu.1, hu.2.trans hb_Icc.2⟩
  have hab_lt : a < b := h_cons.2.2.1
  have hclosed : γ.toPath.extend 0 = γ.toPath.extend 1 := by
    rw [γ.toPath.extend_zero, γ.toPath.extend_one]
  -- The shifted curve agrees with `cyclicShiftFun γ.toPath.extend τ` on `Icc 0 1`.
  have h_eq_csf : Set.EqOn (γ.toPath.cyclicShift hτ).extend
      (cyclicShiftFun γ.toPath.extend τ) (Icc a b) := by
    intro u hu
    exact Path.cyclicShift_extend_on_Icc γ.toPath hτ (hab_Icc hu)
  rcases γ.toClosedPwC1Curve.cyclicShift_consecutive_lift hτ h_cons with
    ⟨h_b_le, c, d, h_cons_cd, h_sub⟩ | ⟨h_a_ge, c, d, h_cons_cd, h_sub⟩
  · -- Case A: no wraparound; shift by τ.
    have hab_sub : Icc a b ⊆ Icc (0:ℝ) (1 - τ) :=
      fun u hu => ⟨ha_Icc.1.trans hu.1, hu.2.trans h_b_le⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun u => γ.toPath.extend (u + τ)) (Icc a b) := by
      intro u hu
      rw [h_eq_csf hu]
      exact cyclicShiftFun_eq_on_no_wrap γ.toPath.extend hτ (hab_sub hu)
    -- t + τ ∈ Icc c d
    have ht_shift : t + τ ∈ Icc c d := h_sub ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- γ.toPath.extend has nonzero derivWithin on Icc c d at t + τ.
    set L : E := derivWithin γ.toPath.extend (Icc c d) (t + τ)
    have hL_ne : L ≠ 0 := γ.derivWithin_ne_zero_pieces c d h_cons_cd (t + τ) ht_shift
    -- HasDerivWithinAt for γ on Icc c d.
    have hγ_diff : DifferentiableWithinAt ℝ γ.toPath.extend (Icc c d) (t + τ) := by
      have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc c d) := γ.contDiffOn_pieces c d h_cons_cd
      exact hcd.differentiableOn_one (t + τ) ht_shift
    have h_HDwa_γ : HasDerivWithinAt γ.toPath.extend L (Icc c d) (t + τ) :=
      hγ_diff.hasDerivWithinAt
    -- HasDerivWithinAt for (· + τ) at t with derivative 1.
    have h_HDwa_shift : HasDerivWithinAt (fun u : ℝ => u + τ) 1 (Icc a b) t :=
      (((hasDerivAt_id t).add_const τ) : HasDerivAt (fun u : ℝ => u + τ) 1 t).hasDerivWithinAt
    -- MapsTo
    have h_maps_to : MapsTo (fun u : ℝ => u + τ) (Icc a b) (Icc c d) := by
      intro u hu
      refine h_sub ⟨?_, ?_⟩
      · show a + τ ≤ u + τ; linarith [hu.1]
      · show u + τ ≤ b + τ; linarith [hu.2]
    -- Composition: g ∘ h has derivative h' • g' = 1 • L = L.
    have h_comp : HasDerivWithinAt (γ.toPath.extend ∘ (fun u : ℝ => u + τ))
        ((1 : ℝ) • L) (Icc a b) t :=
      h_HDwa_γ.scomp t h_HDwa_shift h_maps_to
    have h_comp' : HasDerivWithinAt (fun u : ℝ => γ.toPath.extend (u + τ))
        L (Icc a b) t := by
      simpa [Function.comp_def, one_smul] using h_comp
    -- Transfer to (γ.toPath.cyclicShift hτ).extend via EqOn.
    have h_HDwa_csf : HasDerivWithinAt (γ.toPath.cyclicShift hτ).extend L (Icc a b) t :=
      h_comp'.congr (fun u hu => h_eq_shifted hu) (h_eq_shifted ht)
    -- Derive derivWithin equality.
    have h_unique : UniqueDiffWithinAt ℝ (Icc a b) t := uniqueDiffOn_Icc hab_lt t ht
    rw [h_HDwa_csf.derivWithin h_unique]
    exact hL_ne
  · -- Case B: wraparound; shift by τ - 1.
    have hab_sub : Icc a b ⊆ Icc (1 - τ) 1 :=
      fun u hu => ⟨h_a_ge.trans hu.1, hu.2.trans hb_Icc.2⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun u => γ.toPath.extend (u + τ - 1)) (Icc a b) := by
      intro u hu
      rw [h_eq_csf hu]
      exact cyclicShiftFun_eq_on_wrap γ.toPath.extend hτ hclosed (hab_sub hu)
    have ht_shift : t + τ - 1 ∈ Icc c d := by
      refine h_sub ⟨?_, ?_⟩
      · show a + τ - 1 ≤ t + τ - 1; linarith [ht.1]
      · show t + τ - 1 ≤ b + τ - 1; linarith [ht.2]
    set L : E := derivWithin γ.toPath.extend (Icc c d) (t + τ - 1)
    have hL_ne : L ≠ 0 := γ.derivWithin_ne_zero_pieces c d h_cons_cd (t + τ - 1) ht_shift
    have hγ_diff : DifferentiableWithinAt ℝ γ.toPath.extend (Icc c d) (t + τ - 1) := by
      have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc c d) := γ.contDiffOn_pieces c d h_cons_cd
      exact hcd.differentiableOn_one (t + τ - 1) ht_shift
    have h_HDwa_γ : HasDerivWithinAt γ.toPath.extend L (Icc c d) (t + τ - 1) :=
      hγ_diff.hasDerivWithinAt
    have h_HDwa_shift : HasDerivWithinAt (fun u : ℝ => u + τ - 1) 1 (Icc a b) t :=
      ((((hasDerivAt_id t).add_const τ).sub_const 1) :
        HasDerivAt (fun u : ℝ => u + τ - 1) 1 t).hasDerivWithinAt
    have h_maps_to : MapsTo (fun u : ℝ => u + τ - 1) (Icc a b) (Icc c d) := by
      intro u hu
      refine h_sub ⟨?_, ?_⟩
      · show a + τ - 1 ≤ u + τ - 1; linarith [hu.1]
      · show u + τ - 1 ≤ b + τ - 1; linarith [hu.2]
    have h_comp : HasDerivWithinAt (γ.toPath.extend ∘ (fun u : ℝ => u + τ - 1))
        ((1 : ℝ) • L) (Icc a b) t :=
      h_HDwa_γ.scomp t h_HDwa_shift h_maps_to
    have h_comp' : HasDerivWithinAt (fun u : ℝ => γ.toPath.extend (u + τ - 1))
        L (Icc a b) t := by
      simpa [Function.comp_def, one_smul] using h_comp
    have h_HDwa_csf : HasDerivWithinAt (γ.toPath.cyclicShift hτ).extend L (Icc a b) t :=
      h_comp'.congr (fun u hu => h_eq_shifted hu) (h_eq_shifted ht)
    have h_unique : UniqueDiffWithinAt ℝ (Icc a b) t := uniqueDiffOn_Icc hab_lt t ht
    rw [h_HDwa_csf.derivWithin h_unique]
    exact hL_ne

/-- **Step 3: Cyclic shift of a `ClosedPwC1Immersion`.** -/
noncomputable def cyclicShift (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ClosedPwC1Immersion (γ.toPath.extend τ) where
  toClosedPwC1Curve := γ.toClosedPwC1Curve.cyclicShift hτ
  derivWithin_ne_zero_pieces := fun _ _ h_cons _ ht =>
    γ.cyclicShift_derivWithin_ne_zero_piece hτ h_cons ht

/-! ### Step 4: Cyclic-shift equation-on lemmas (parameter-level)

These lemmas relate the cyclic-shifted curve `γ.cyclicShift hτ` to `γ` at the
parameter level. The shifted curve equals `γ ∘ (· + τ)` on `Icc 0 (1 - τ)` and
`γ ∘ (· + τ - 1)` on `Icc (1 - τ) 1`. -/

/-- The shifted curve agrees with `γ ∘ (· + τ)` on `Icc 0 (1 - τ)`. -/
theorem cyclicShift_extend_eq_no_wrap (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 - τ)) :
    (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ) := by
  have ht_Icc01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨ht.1, by linarith [ht.2, hτ.1]⟩
  rw [show (γ.cyclicShift hτ).toPath.extend = (γ.toPath.cyclicShift hτ).extend from rfl,
      Path.cyclicShift_extend_on_Icc γ.toPath hτ ht_Icc01]
  exact cyclicShiftFun_eq_on_no_wrap γ.toPath.extend hτ ht

/-- The shifted curve agrees with `γ ∘ (· + τ - 1)` on `Icc (1 - τ) 1`. -/
theorem cyclicShift_extend_eq_wrap (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (1 - τ) 1) :
    (γ.cyclicShift hτ).toPath.extend t = γ.toPath.extend (t + τ - 1) := by
  have ht_Icc01 : t ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [ht.1, hτ.2], ht.2⟩
  have hclosed : γ.toPath.extend 0 = γ.toPath.extend 1 := by
    rw [γ.toPath.extend_zero, γ.toPath.extend_one]
  rw [show (γ.cyclicShift hτ).toPath.extend = (γ.toPath.cyclicShift hτ).extend from rfl,
      Path.cyclicShift_extend_on_Icc γ.toPath hτ ht_Icc01]
  exact cyclicShiftFun_eq_on_wrap γ.toPath.extend hτ hclosed ht

/-- The cyclic-shifted path is differentiable on `Ioo 0 (1 - τ)` (off partition),
with derivative `deriv γ.toPath.extend (· + τ)`.

We package the no-wrap derivative behavior as a `HasDerivAt` statement on an open
set `Ioo 0 (1 - τ)`, which suffices for almost-everywhere arguments. The full
statement at every interior point requires a partition lookup. -/
theorem cyclicShift_hasDerivAt_no_wrap (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1 - τ))
    (htn : t ∉ (γ.cyclicShift hτ).partition) :
    HasDerivAt (γ.cyclicShift hτ).toPath.extend
      (deriv γ.toPath.extend (t + τ)) t := by
  -- t lies in the open interior of some piece `(a, b)` of the shifted partition.
  have ht_Ioo01 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨ht.1, by linarith [ht.2, hτ.1]⟩
  obtain ⟨a, b, hcons, ht_in_Ioo⟩ :=
    (γ.cyclicShift hτ).toClosedPwC1Curve.exists_consecutive_pair_containing
      ht_Ioo01 htn
  -- The shifted curve is C¹ on Icc a b, so derivWithin = derivW.
  have h_eq_csf : Set.EqOn (γ.toPath.cyclicShift hτ).extend
      (cyclicShiftFun γ.toPath.extend τ) (Icc a b) := by
    intro u hu
    -- a, b ∈ Icc 0 1
    have ha_Icc : a ∈ Icc (0:ℝ) 1 := by
      have := cyclicShiftPartitionExt_subset_Icc γ.partition hτ hcons.1
      exact this
    have hb_Icc : b ∈ Icc (0:ℝ) 1 := by
      have := cyclicShiftPartitionExt_subset_Icc γ.partition hτ hcons.2.1
      exact this
    have hu_Icc : u ∈ Icc (0:ℝ) 1 :=
      ⟨ha_Icc.1.trans hu.1, hu.2.trans hb_Icc.2⟩
    exact Path.cyclicShift_extend_on_Icc γ.toPath hτ hu_Icc
  have hab_lt : a < b := hcons.2.2.1
  -- Use the consecutive-pair lift to find a γ-piece containing the shifted interval.
  rcases γ.toClosedPwC1Curve.cyclicShift_consecutive_lift hτ hcons with
    ⟨h_b_le, c, d, h_cons_cd, h_sub⟩ | ⟨h_a_ge, _c, _d, _h_cons_cd, _h_sub⟩
  · -- No wraparound case: the piece is on Icc a b ⊆ Icc 0 (1 - τ).
    have hab_sub : Icc a b ⊆ Icc (0:ℝ) (1 - τ) := by
      have ha_nn : 0 ≤ a :=
        (cyclicShiftPartitionExt_subset_Icc γ.partition hτ hcons.1).1
      exact fun u hu => ⟨ha_nn.trans hu.1, hu.2.trans h_b_le⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun u => γ.toPath.extend (u + τ)) (Icc a b) := by
      intro u hu
      rw [h_eq_csf hu]
      exact cyclicShiftFun_eq_on_no_wrap γ.toPath.extend hτ (hab_sub hu)
    -- t + τ ∈ Ioo c d (open interior).
    have ht_shift : t + τ ∈ Ioo c d := by
      have ha_eq : a + τ ≥ c := by
        have hin : (a + τ : ℝ) ∈ Icc (a + τ) (b + τ) :=
          ⟨le_refl _, by linarith [hab_lt]⟩
        exact (h_sub hin).1
      have hb_eq : b + τ ≤ d := by
        have hin : (b + τ : ℝ) ∈ Icc (a + τ) (b + τ) :=
          ⟨by linarith [hab_lt], le_refl _⟩
        exact (h_sub hin).2
      exact ⟨by linarith [ht_in_Ioo.1], by linarith [ht_in_Ioo.2]⟩
    -- DifferentiableAt γ.extend (t + τ) (interior of piece).
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc c d) := γ.contDiffOn_pieces c d h_cons_cd
    have ht_shift_Icc : t + τ ∈ Icc c d := Ioo_subset_Icc_self ht_shift
    have h_diff_within : DifferentiableWithinAt ℝ γ.toPath.extend (Icc c d) (t + τ) :=
      hcd.differentiableOn_one (t + τ) ht_shift_Icc
    have h_diff_at : DifferentiableAt ℝ γ.toPath.extend (t + τ) := by
      have : Icc c d ∈ 𝓝 (t + τ) := Icc_mem_nhds ht_shift.1 ht_shift.2
      exact h_diff_within.differentiableAt this
    -- HasDerivAt γ.extend at (t + τ).
    have h_γHDA : HasDerivAt γ.toPath.extend (deriv γ.toPath.extend (t + τ)) (t + τ) :=
      h_diff_at.hasDerivAt
    -- HasDerivAt (· + τ) 1 t.
    have h_shift_HDA : HasDerivAt (fun u : ℝ => u + τ) 1 t :=
      (hasDerivAt_id t).add_const τ
    -- Composition: scomp gives (1 : ℝ) • L = L.
    have h_comp : HasDerivAt (γ.toPath.extend ∘ (fun u : ℝ => u + τ))
        ((1 : ℝ) • deriv γ.toPath.extend (t + τ)) t :=
      h_γHDA.scomp t h_shift_HDA
    have h_comp' : HasDerivAt (fun u : ℝ => γ.toPath.extend (u + τ))
        (deriv γ.toPath.extend (t + τ)) t := by
      simpa [Function.comp_def, one_smul] using h_comp
    -- Transfer to (γ.cyclicShift hτ).extend via EqOn on a nhd of t.
    have h_eqOn_nhd : (γ.cyclicShift hτ).toPath.extend =ᶠ[𝓝 t]
        (fun u => γ.toPath.extend (u + τ)) := by
      -- Icc a b is a nhd of t (interior)
      have h_Icc_nhd : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht_in_Ioo.1 ht_in_Ioo.2
      filter_upwards [h_Icc_nhd] with u hu
      show (γ.toPath.cyclicShift hτ).extend u = γ.toPath.extend (u + τ)
      exact h_eq_shifted hu
    -- congr_of_eventuallyEq: h : HasDerivAt f f' x, h₁ : f₁ =ᶠ f → HasDerivAt f₁
    -- So we need the shifted-form-eq-fun-form, then conclude the LHS form has the deriv.
    exact h_comp'.congr_of_eventuallyEq h_eqOn_nhd
  · -- Wraparound case: but we're in Icc 0 (1 - τ), so a ≥ 1 - τ contradicts t < 1 - τ.
    exfalso
    have h_t_lt : t < 1 - τ := ht.2
    have h_a_le_t : a ≤ t := ht_in_Ioo.1.le
    linarith

/-- Symmetric: derivative on the wrap region. -/
theorem cyclicShift_hasDerivAt_wrap (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Ioo (1 - τ) 1)
    (htn : t ∉ (γ.cyclicShift hτ).partition) :
    HasDerivAt (γ.cyclicShift hτ).toPath.extend
      (deriv γ.toPath.extend (t + τ - 1)) t := by
  have ht_Ioo01 : t ∈ Ioo (0 : ℝ) 1 :=
    ⟨by linarith [ht.1, hτ.2], ht.2⟩
  obtain ⟨a, b, hcons, ht_in_Ioo⟩ :=
    (γ.cyclicShift hτ).toClosedPwC1Curve.exists_consecutive_pair_containing
      ht_Ioo01 htn
  have hclosed : γ.toPath.extend 0 = γ.toPath.extend 1 := by
    rw [γ.toPath.extend_zero, γ.toPath.extend_one]
  have h_eq_csf : Set.EqOn (γ.toPath.cyclicShift hτ).extend
      (cyclicShiftFun γ.toPath.extend τ) (Icc a b) := by
    intro u hu
    have ha_Icc : a ∈ Icc (0:ℝ) 1 :=
      cyclicShiftPartitionExt_subset_Icc γ.partition hτ hcons.1
    have hb_Icc : b ∈ Icc (0:ℝ) 1 :=
      cyclicShiftPartitionExt_subset_Icc γ.partition hτ hcons.2.1
    have hu_Icc : u ∈ Icc (0:ℝ) 1 :=
      ⟨ha_Icc.1.trans hu.1, hu.2.trans hb_Icc.2⟩
    exact Path.cyclicShift_extend_on_Icc γ.toPath hτ hu_Icc
  have hab_lt : a < b := hcons.2.2.1
  rcases γ.toClosedPwC1Curve.cyclicShift_consecutive_lift hτ hcons with
    ⟨h_b_le, _c, _d, _h_cons_cd, _h_sub⟩ | ⟨h_a_ge, c, d, h_cons_cd, h_sub⟩
  · -- No wrap case: b ≤ 1 - τ contradicts t > 1 - τ and a ≤ t.
    exfalso
    have h_t_gt : t > 1 - τ := ht.1
    have h_t_le_b : t ≤ b := ht_in_Ioo.2.le
    linarith
  · -- Wraparound case.
    have hb_le_1 : b ≤ 1 :=
      (cyclicShiftPartitionExt_subset_Icc γ.partition hτ hcons.2.1).2
    have hab_sub : Icc a b ⊆ Icc (1 - τ) 1 :=
      fun u hu => ⟨h_a_ge.trans hu.1, hu.2.trans hb_le_1⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun u => γ.toPath.extend (u + τ - 1)) (Icc a b) := by
      intro u hu
      rw [h_eq_csf hu]
      exact cyclicShiftFun_eq_on_wrap γ.toPath.extend hτ hclosed (hab_sub hu)
    -- t + τ - 1 ∈ Ioo c d.
    have ht_shift : t + τ - 1 ∈ Ioo c d := by
      have ha_eq : a + τ - 1 ≥ c := by
        have hin : (a + τ - 1 : ℝ) ∈ Icc (a + τ - 1) (b + τ - 1) :=
          ⟨le_refl _, by linarith [hab_lt]⟩
        exact (h_sub hin).1
      have hb_eq : b + τ - 1 ≤ d := by
        have hin : (b + τ - 1 : ℝ) ∈ Icc (a + τ - 1) (b + τ - 1) :=
          ⟨by linarith [hab_lt], le_refl _⟩
        exact (h_sub hin).2
      exact ⟨by linarith [ht_in_Ioo.1], by linarith [ht_in_Ioo.2]⟩
    have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc c d) := γ.contDiffOn_pieces c d h_cons_cd
    have ht_shift_Icc : t + τ - 1 ∈ Icc c d := Ioo_subset_Icc_self ht_shift
    have h_diff_within : DifferentiableWithinAt ℝ γ.toPath.extend (Icc c d) (t + τ - 1) :=
      hcd.differentiableOn_one (t + τ - 1) ht_shift_Icc
    have h_diff_at : DifferentiableAt ℝ γ.toPath.extend (t + τ - 1) := by
      have : Icc c d ∈ 𝓝 (t + τ - 1) := Icc_mem_nhds ht_shift.1 ht_shift.2
      exact h_diff_within.differentiableAt this
    have h_γHDA : HasDerivAt γ.toPath.extend (deriv γ.toPath.extend (t + τ - 1)) (t + τ - 1) :=
      h_diff_at.hasDerivAt
    have h_shift_HDA : HasDerivAt (fun u : ℝ => u + τ - 1) 1 t :=
      ((hasDerivAt_id t).add_const τ).sub_const 1
    have h_comp : HasDerivAt (γ.toPath.extend ∘ (fun u : ℝ => u + τ - 1))
        ((1 : ℝ) • deriv γ.toPath.extend (t + τ - 1)) t :=
      h_γHDA.scomp t h_shift_HDA
    have h_comp' : HasDerivAt (fun u : ℝ => γ.toPath.extend (u + τ - 1))
        (deriv γ.toPath.extend (t + τ - 1)) t := by
      simpa [Function.comp_def, one_smul] using h_comp
    have h_eqOn_nhd : (γ.cyclicShift hτ).toPath.extend =ᶠ[𝓝 t]
        (fun u => γ.toPath.extend (u + τ - 1)) := by
      have h_Icc_nhd : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht_in_Ioo.1 ht_in_Ioo.2
      filter_upwards [h_Icc_nhd] with u hu
      show (γ.toPath.cyclicShift hτ).extend u = γ.toPath.extend (u + τ - 1)
      exact h_eq_shifted hu
    exact h_comp'.congr_of_eventuallyEq h_eqOn_nhd

/-- Equality of derivatives on the open no-wrap interior, off the shifted partition. -/
theorem cyclicShift_deriv_eq_no_wrap (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1 - τ))
    (htn : t ∉ (γ.cyclicShift hτ).partition) :
    deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ) :=
  (γ.cyclicShift_hasDerivAt_no_wrap hτ ht htn).deriv

/-- Equality of derivatives on the open wrap interior, off the shifted partition. -/
theorem cyclicShift_deriv_eq_wrap (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ}
    (ht : t ∈ Ioo (1 - τ) 1)
    (htn : t ∉ (γ.cyclicShift hτ).partition) :
    deriv (γ.cyclicShift hτ).toPath.extend t =
      deriv γ.toPath.extend (t + τ - 1) :=
  (γ.cyclicShift_hasDerivAt_wrap hτ ht htn).deriv

end ClosedPwC1Immersion

/-! ## Finite preimage of a finite set under a `ClosedPwC1Immersion`

For a `ClosedPwC1Immersion γ` and finite `S : Finset E`, the parameter
preimage `{t ∈ [0,1] | γ t ∈ S}` is finite. The proof uses
`HasDerivWithinAt.eventually_ne` (isolated zeros from non-vanishing
derivative) + `IsCompact + discrete ⇒ finite`.

Eliminates the `h_preimage : Set.Countable …` hypothesis in
`h_holo_cancel_of_conditionB` and related downstream theorems. -/

namespace ClosedPwC1Immersion

variable {x : E} {γ : ClosedPwC1Immersion x}


/-- **Per-piece finite preimage at a single value.** On a closed piece `Icc a b`
between consecutive partition members, the preimage of a single point `s ∈ E`
under the extended path is finite.

The proof uses `HasDerivWithinAt.eventually_ne`: non-vanishing `derivWithin`
forces each preimage point to be isolated within `Icc a b`. The preimage is a
closed subset of compact `Icc a b`, and discreteness + compactness gives
finiteness via `IsCompact.finite_of_discrete`. -/
private theorem preimage_finite_piece (γ : ClosedPwC1Immersion x) {a b : ℝ}
    (h : γ.partition.IsConsecutive a b) (s : E) :
    Set.Finite {t ∈ Icc a b | γ.toPath.extend t = s} := by
  classical
  let f : ℝ → E := γ.toPath.extend
  let T : Set ℝ := {t ∈ Icc a b | f t = s}
  show T.Finite
  -- Differentiability + ContDiffOn ℝ 1 on Icc a b gives HasDerivWithinAt.
  have hcd : ContDiffOn ℝ 1 f (Icc a b) := γ.contDiffOn_pieces a b h
  have h_diff : DifferentiableOn ℝ f (Icc a b) := hcd.differentiableOn_one
  -- T is closed in ℝ (continuous preimage of {s} ∩ closed Icc a b).
  have hT_closed : IsClosed T := by
    have h_eq : T = (Icc a b) ∩ (f ⁻¹' {s}) := by
      ext t; simp [T, Set.mem_setOf_eq]
    rw [h_eq]
    exact isClosed_Icc.inter (isClosed_singleton.preimage γ.toPath.continuous_extend)
  -- T is compact (closed in compact Icc a b).
  have hT_compact : IsCompact T :=
    isCompact_Icc.of_isClosed_subset hT_closed (fun t ht => ht.1)
  -- T as a subtype is discrete. We use the noAccPts criterion: each point
  -- t₀ ∈ T is not an accumulation point of T.
  have hT_discrete : DiscreteTopology T := by
    refine discreteTopology_of_noAccPts ?_
    intro t₀ ht₀
    have ht₀_Icc : t₀ ∈ Icc a b := ht₀.1
    -- Get HasDerivWithinAt with nonzero derivative.
    have h_diffAt : DifferentiableWithinAt ℝ f (Icc a b) t₀ :=
      h_diff t₀ ht₀_Icc
    let f'₀ : E := derivWithin f (Icc a b) t₀
    have h_HD : HasDerivWithinAt f f'₀ (Icc a b) t₀ :=
      h_diffAt.hasDerivWithinAt
    have h_f'₀_ne : f'₀ ≠ 0 :=
      γ.derivWithin_ne_zero_pieces a b h t₀ ht₀_Icc
    -- Eventually `f z ≠ s` in `𝓝[Icc a b \ {t₀}] t₀`.
    have h_eventually : ∀ᶠ z in 𝓝[(Icc a b) \ {t₀}] t₀, f z ≠ s :=
      HasDerivWithinAt.eventually_ne h_HD h_f'₀_ne
    -- Translate via accPt_principal_iff_nhdsWithin to filter language.
    rw [accPt_principal_iff_nhdsWithin]
    -- Goal: ¬(𝓝[T \ {t₀}] t₀).NeBot
    intro h_neBot
    -- T \ {t₀} ⊆ (Icc a b) \ {t₀}.
    have hTsub : T \ {t₀} ⊆ (Icc a b) \ {t₀} :=
      fun u hu => ⟨hu.1.1, hu.2⟩
    have h_ev_T : ∀ᶠ z in 𝓝[T \ {t₀}] t₀, f z ≠ s :=
      h_eventually.filter_mono (nhdsWithin_mono _ hTsub)
    have h_ev_in_T : ∀ᶠ z in 𝓝[T \ {t₀}] t₀, z ∈ T \ {t₀} :=
      self_mem_nhdsWithin
    have h_combo : ∀ᶠ z in 𝓝[T \ {t₀}] t₀, False := by
      filter_upwards [h_ev_T, h_ev_in_T] with z hz_ne hz_in
      exact hz_ne hz_in.1.2
    exact h_neBot.ne (Filter.eventually_false_iff_eq_bot.mp h_combo)
  -- Compact + Discrete ⇒ Finite (via `Finite (T : Type)` and `Set.finite_coe_iff`).
  have : CompactSpace T := isCompact_iff_compactSpace.mp hT_compact
  have hT_finite_coe : Finite T := finite_of_compact_of_discrete
  exact Set.finite_coe_iff.mp hT_finite_coe

/-- **Per-piece finite preimage of a finite set.** On a closed piece `Icc a b`
between consecutive partition members, the preimage of any finite set `S ⊆ E`
under the extended path is finite. -/
private theorem preimage_finite_piece_of_finset (γ : ClosedPwC1Immersion x) {a b : ℝ}
    (h : γ.partition.IsConsecutive a b) (S : Finset E) :
    Set.Finite {t ∈ Icc a b | γ.toPath.extend t ∈ (↑S : Set E)} := by
  classical
  have h_union :
      {t ∈ Icc a b | γ.toPath.extend t ∈ (↑S : Set E)} =
        ⋃ s ∈ S, {t ∈ Icc a b | γ.toPath.extend t = s} := by
    ext t
    constructor
    · rintro ⟨htI, hts⟩
      simp only [Finset.mem_coe] at hts
      exact Set.mem_iUnion₂.mpr ⟨γ.toPath.extend t, hts, htI, rfl⟩
    · intro ht
      obtain ⟨s, hs, htI, hts⟩ := Set.mem_iUnion₂.mp ht
      exact ⟨htI, by simp only [hts, Finset.mem_coe]; exact hs⟩
  rw [h_union]
  exact S.finite_toSet.biUnion fun s _ => γ.preimage_finite_piece h s

/-- **Finite preimage of a finite set under a closed paper-piecewise `C¹` immersion.**
The set of parameters `t ∈ [0, 1]` at which `γ t ∈ S` is finite, for any finite
target `S ⊆ E`.

The proof decomposes `[0, 1]` along the partition into closed pieces, applies
`preimage_finite_piece_of_finset` on each piece, and takes the finite union. -/
theorem preimage_finite (γ : ClosedPwC1Immersion x) (S : Finset E) :
    Set.Finite {t ∈ Icc (0 : ℝ) 1 |
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set E)} := by
  classical
  -- Set of consecutive pairs in γ.partition.
  set pairs : Finset (ℝ × ℝ) := (γ.partition.product γ.partition).filter
    (fun p => γ.partition.IsConsecutive p.1 p.2) with hpairs_def
  -- The image of `γ.toPwC1Immersion.toPiecewiseC1Path` is `γ.toPath.extend`.
  -- Every `t ∈ Icc 0 1` belongs to some piece `Icc a b` with `(a, b)` consecutive.
  set f := γ.toPath.extend with hf_def
  have h_eq : ∀ t, γ.toPwC1Immersion.toPiecewiseC1Path t = f t := fun _ => rfl
  -- The target set is a subset of the union over consecutive pieces.
  have h_subset :
      {t ∈ Icc (0 : ℝ) 1 |
          γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set E)} ⊆
        ⋃ p ∈ pairs, {t ∈ Icc p.1 p.2 | f t ∈ (↑S : Set E)} := by
    intro t ht
    obtain ⟨ht_Icc, ht_S⟩ := ht
    rw [h_eq] at ht_S
    -- Find a consecutive pair (a, b) containing t.
    by_cases htn : t ∈ γ.partition
    · -- t is a partition point. Pick the piece [t, succ(t)] if t < 1, otherwise [pred(t), t].
      by_cases ht1 : t = 1
      · -- t = 1: use the predecessor piece.
        have h0_lt : (0 : ℝ) < 1 := zero_lt_one
        have h1_in : (1 : ℝ) ∈ γ.partition := γ.one_mem_partition
        obtain ⟨a, hcons⟩ := γ.exists_predecessor h1_in h0_lt
        refine Set.mem_iUnion₂.mpr ⟨(a, 1), ?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hcons.1, hcons.2.1⟩, hcons⟩
        · refine ⟨⟨?_, ?_⟩, ?_⟩
          · rw [ht1]; exact hcons.2.2.1.le
          · rw [ht1]
          · exact ht_S
      · -- t < 1: use the successor piece.
        have ht_lt_1 : t < 1 := lt_of_le_of_ne ht_Icc.2 ht1
        obtain ⟨b, hcons⟩ := γ.exists_successor htn ht_lt_1
        refine Set.mem_iUnion₂.mpr ⟨(t, b), ?_, ?_⟩
        · exact Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hcons.1, hcons.2.1⟩, hcons⟩
        · refine ⟨⟨le_refl t, hcons.2.2.1.le⟩, ht_S⟩
    · -- t not in partition: t ∈ (0, 1) (since 0, 1 ∈ partition, t ≠ 0 and t ≠ 1).
      have ht_ne_0 : t ≠ 0 := fun h => htn (h ▸ γ.zero_mem_partition)
      have ht_ne_1 : t ≠ 1 := fun h => htn (h ▸ γ.one_mem_partition)
      have ht_Ioo : t ∈ Ioo (0 : ℝ) 1 :=
        ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_ne_0), lt_of_le_of_ne ht_Icc.2 ht_ne_1⟩
      obtain ⟨a, b, hcons, ht_Ioo'⟩ :=
        γ.toClosedPwC1Curve.exists_consecutive_pair_containing ht_Ioo htn
      refine Set.mem_iUnion₂.mpr ⟨(a, b), ?_, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨hcons.1, hcons.2.1⟩, hcons⟩
      · refine ⟨Ioo_subset_Icc_self ht_Ioo', ht_S⟩
  refine Set.Finite.subset ?_ h_subset
  refine pairs.finite_toSet.biUnion ?_
  intro p hp
  have hcons : γ.partition.IsConsecutive p.1 p.2 := (Finset.mem_filter.mp hp).2
  exact γ.preimage_finite_piece_of_finset hcons S

/-- Corollary: the preimage of a finite set is countable. -/
theorem preimage_countable (γ : ClosedPwC1Immersion x) (S : Finset E) :
    Set.Countable {t ∈ Icc (0 : ℝ) 1 |
      γ.toPwC1Immersion.toPiecewiseC1Path t ∈ (↑S : Set E)} :=
  (γ.preimage_finite S).countable

end ClosedPwC1Immersion


end
