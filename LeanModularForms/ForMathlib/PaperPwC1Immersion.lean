/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
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

end
