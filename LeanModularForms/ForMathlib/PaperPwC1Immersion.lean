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
import LeanModularForms.ForMathlib.PiecewiseC1PathOn

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
such that the path is `C¹` on each *closed* sub-interval `[aₖ, aₖ₊₁]`.

This extends `PiecewiseC1Path x x`. The inherited `partition` field is the
*Ioo-style* (open-interior) partition, while `closedPartition` is the Icc-style
partition with endpoints included. The two are related by
`closedPartition_eq : closedPartition = insert 0 (insert 1 partition)`. -/
structure ClosedPwC1Curve (x : E) extends PiecewiseC1Path x x where
  /-- Closed partition WITH endpoints. Required because the inherited `partition`
  is Ioo-style (interior only). -/
  closedPartition : Finset ℝ
  /-- `0` is a closed-partition point. -/
  zero_mem_closedPartition : (0 : ℝ) ∈ closedPartition
  /-- `1` is a closed-partition point. -/
  one_mem_closedPartition : (1 : ℝ) ∈ closedPartition
  /-- Every closed-partition point lies in `[0, 1]`. -/
  closedPartition_subset : (closedPartition : Set ℝ) ⊆ Icc 0 1
  /-- The closed partition is the Ioo-style `partition` with `0` and `1` adjoined. -/
  closedPartition_eq : closedPartition = insert 0 (insert 1 partition)
  /-- On every closed sub-interval `[a, b]` whose endpoints are consecutive
  closed-partition members, the extended path is `C¹`. -/
  contDiffOn_pieces : ∀ a b, closedPartition.IsConsecutive a b →
    ContDiffOn ℝ 1 toPath.extend (Icc a b)

/-- A **closed piecewise `C¹` immersion** in the sense of Hungerbühler–Wasem
(arXiv:1808.00997v2, page 3): a closed piecewise `C¹` curve whose derivative
is non-vanishing on every closed sub-interval between consecutive partition
points. -/
structure ClosedPwC1Immersion (x : E) extends ClosedPwC1Curve x where
  /-- On every closed sub-interval between consecutive closed-partition members, the
  *within*-derivative of the extended path is non-zero — i.e. `Λ̇|_{[aₖ,aₖ₊₁]} ≠ 0`
  in the paper. We use `derivWithin _ (Icc a b)` rather than the global `deriv`
  because at corner partition points the global `deriv` is `0` by mathlib
  convention (the function is not differentiable there), which would falsely
  contradict non-vanishing. -/
  derivWithin_ne_zero_pieces : ∀ a b, closedPartition.IsConsecutive a b →
    ∀ t ∈ Icc a b, derivWithin toPath.extend (Icc a b) t ≠ 0

namespace ClosedPwC1Curve

variable {x : E}

/-- The underlying extended path is continuous. -/
theorem continuous (γ : ClosedPwC1Curve x) : Continuous γ.toPath.extend :=
  γ.toPath.continuous_extend

/-- Membership in the inherited Ioo-style `partition` is equivalent to lying in
`closedPartition` while not being an endpoint. -/
theorem mem_partition_iff (γ : ClosedPwC1Curve x) {t : ℝ} :
    t ∈ γ.partition ↔ t ∈ γ.closedPartition ∧ t ≠ 0 ∧ t ≠ 1 := by
  refine ⟨fun ht => ?_, fun ⟨h_in, h_ne0, h_ne1⟩ => ?_⟩
  · have h_in_Ioo : t ∈ Ioo (0 : ℝ) 1 := γ.partition_subset ht
    exact ⟨γ.closedPartition_eq ▸ by simp [Finset.mem_insert, ht],
      ne_of_gt h_in_Ioo.1, ne_of_lt h_in_Ioo.2⟩
  · rw [γ.closedPartition_eq, Finset.mem_insert, Finset.mem_insert] at h_in
    exact h_in.resolve_left h_ne0 |>.resolve_left h_ne1

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
    (h : γ.closedPartition.IsConsecutive a b) :
    IntervalIntegrable (deriv γ.toPath.extend) volume a b := by
  have hab : a ≤ b := h.2.2.1.le
  have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b h
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    hcd.continuousOn_derivWithin (uniqueDiffOn_Icc h.2.2.1) le_rfl
  refine (h_dw_cont.intervalIntegrable_of_Icc hab).congr_ae ?_
  refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioo a b, ?_, fun _ ht => derivWithin_eq_deriv_on_Ioo _ ht⟩
  rw [MeasureTheory.mem_ae_iff, MeasureTheory.Measure.restrict_apply' measurableSet_uIoc]
  refine MeasureTheory.measure_mono_null (t := ({b} : Set ℝ)) ?_ Real.volume_singleton
  intro t ⟨ht_compl, ht_in⟩
  rw [uIoc_of_le hab] at ht_in
  by_contra hne
  exact ht_compl ⟨ht_in.1, lt_of_le_of_ne ht_in.2 hne⟩

end ClosedPwC1Curve

/-! ## Helper: gluing piece-wise predicates over a finite partition -/

/-- Generic "glue piece-wise predicates" induction over a finite partition:
if `P` is reflexive (in the `a = b` sense) and transitive across a shared midpoint
on consecutive pieces, then `P` holds on `[a, b]` once it holds on every consecutive
pair of the partition. The two callers (`IntervalIntegrable` and `LipschitzOnWith`)
fix `P` accordingly. -/
private lemma consecutive_piece_induction {P : ℝ → ℝ → Prop}
    (P_refl : ∀ x, P x x) (P_trans : ∀ {p q r : ℝ}, P p q → P q r → P p r) :
    ∀ s : Finset ℝ, ∀ a b : ℝ, a ∈ s → b ∈ s → a ≤ b →
      (∀ c ∈ s, a ≤ c ∧ c ≤ b) →
      (∀ p q, s.IsConsecutive p q → P p q) → P a b := by
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro a b ha hb hab hbds hpc
    rcases eq_or_lt_of_le hab with hab_eq | hab_lt
    · subst hab_eq; exact P_refl a
    set t : Finset ℝ := s.filter (a < ·)
    have hb_in_t : b ∈ t := Finset.mem_filter.mpr ⟨hb, hab_lt⟩
    have ha'_in_t : t.min' ⟨b, hb_in_t⟩ ∈ t := t.min'_mem _
    set a' := t.min' ⟨b, hb_in_t⟩
    have ha'_in_s : a' ∈ s := (Finset.mem_filter.mp ha'_in_t).1
    have ha_lt_a' : a < a' := (Finset.mem_filter.mp ha'_in_t).2
    have hcons : s.IsConsecutive a a' :=
      ⟨ha, ha'_in_s, ha_lt_a', fun c hc hc_Ioo =>
        absurd (t.min'_le c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.1⟩)) (by linarith [hc_Ioo.2])⟩
    set s' : Finset ℝ := s.erase a
    have ha'_in_s' : a' ∈ s' := Finset.mem_erase.mpr ⟨ne_of_gt ha_lt_a', ha'_in_s⟩
    have hb_in_s' : b ∈ s' := Finset.mem_erase.mpr ⟨ne_of_gt hab_lt, hb⟩
    have hbds' : ∀ c ∈ s', a' ≤ c ∧ c ≤ b := fun c hc => by
      have hc_in : c ∈ s := (Finset.mem_erase.mp hc).2
      refine ⟨t.min'_le _ (Finset.mem_filter.mpr ⟨hc_in, ?_⟩), (hbds c hc_in).2⟩
      exact lt_of_le_of_ne (hbds c hc_in).1 (Ne.symm (Finset.mem_erase.mp hc).1)
    have hpc' : ∀ p q, s'.IsConsecutive p q → P p q := fun p q hcons' =>
      hpc p q ⟨(Finset.mem_erase.mp hcons'.1).2, (Finset.mem_erase.mp hcons'.2.1).2,
        hcons'.2.2.1, fun c hc hc_Ioo => by
          have hp_gt_a : a < p := lt_of_lt_of_le ha_lt_a' (hbds' p hcons'.1).1
          exact hcons'.2.2.2 c (Finset.mem_erase.mpr
            ⟨ne_of_gt (lt_of_lt_of_le hp_gt_a hc_Ioo.1.le), hc⟩) hc_Ioo⟩
    exact P_trans (hpc _ _ hcons)
      (ih s' (Finset.erase_ssubset ha) a' b ha'_in_s' hb_in_s' (hbds' b hb_in_s').1 hbds' hpc')

/-- If `f` is interval-integrable on every consecutive pair of a finite partition
of `[a, b]` containing both endpoints, then `f` is interval-integrable on `[a, b]`. -/
private theorem intervalIntegrable_of_consecutive_pieces
    {α : Type*} [TopologicalSpace α] [ENormedAddMonoid α]
    [TopologicalSpace.PseudoMetrizableSpace α]
    {f : ℝ → α} {μ : MeasureTheory.Measure ℝ} (s : Finset ℝ) (a b : ℝ)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b)
    (hbds : ∀ c ∈ s, a ≤ c ∧ c ≤ b)
    (hpc : ∀ p q, s.IsConsecutive p q → IntervalIntegrable f μ p q) :
    IntervalIntegrable f μ a b :=
  consecutive_piece_induction (P := IntervalIntegrable f μ)
    (fun _ => IntervalIntegrable.refl) (fun h1 h2 => h1.trans h2) s a b ha hb hab hbds hpc

/-! ## Global interval-integrability of the derivative -/

namespace ClosedPwC1Curve

variable {x : E}

/-- **TIGHT-6 (global form).** For a paper-faithful closed piecewise `C¹` curve
`γ`, the derivative `deriv γ.toPath.extend` is interval-integrable on `[0, 1]`. -/
theorem deriv_extend_intervalIntegrable (γ : ClosedPwC1Curve x) :
    IntervalIntegrable (deriv γ.toPath.extend) volume 0 1 :=
  intervalIntegrable_of_consecutive_pieces γ.closedPartition 0 1
    γ.zero_mem_closedPartition γ.one_mem_closedPartition zero_le_one
    (fun _ hc => ⟨(γ.closedPartition_subset hc).1, (γ.closedPartition_subset hc).2⟩)
    (fun _ _ h => γ.deriv_intervalIntegrable_piece h)

/-! ## Bridge to legacy `PiecewiseC1Path`

A paper-faithful curve produces a legacy curve by erasing the global endpoints
`0` and `1` from the partition (the legacy structure keeps the partition in
the open interior `(0, 1)` by convention). -/

/-- For `t` strictly inside `(0, 1)` not in a closed-partition that contains
both endpoints, find the consecutive closed-partition pair containing `t`. -/
private lemma exists_consecutive_pair_aux {closedPartition : Finset ℝ}
    (zero_mem : (0 : ℝ) ∈ closedPartition) (one_mem : (1 : ℝ) ∈ closedPartition)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htn : t ∉ closedPartition) :
    ∃ a b, closedPartition.IsConsecutive a b ∧ t ∈ Ioo a b := by
  set pred := closedPartition.filter (· < t)
  set succ := closedPartition.filter (t < ·)
  have h0_pred : (0 : ℝ) ∈ pred := Finset.mem_filter.mpr ⟨zero_mem, ht.1⟩
  have h1_succ : (1 : ℝ) ∈ succ := Finset.mem_filter.mpr ⟨one_mem, ht.2⟩
  set a := pred.max' ⟨0, h0_pred⟩
  set b := succ.min' ⟨1, h1_succ⟩
  have ha_mem : a ∈ pred := pred.max'_mem _
  have hb_mem : b ∈ succ := succ.min'_mem _
  have ha_lt : a < t := (Finset.mem_filter.mp ha_mem).2
  have ht_lt_b : t < b := (Finset.mem_filter.mp hb_mem).2
  refine ⟨a, b, ⟨(Finset.mem_filter.mp ha_mem).1, (Finset.mem_filter.mp hb_mem).1,
    ha_lt.trans ht_lt_b, fun c hc hc_Ioo => ?_⟩, ha_lt, ht_lt_b⟩
  rcases lt_trichotomy c t with hct | hct | hct
  · exact absurd (pred.le_max' c (Finset.mem_filter.mpr ⟨hc, hct⟩))
      (by linarith [hc_Ioo.1])
  · exact htn (hct ▸ hc)
  · exact absurd (succ.min'_le c (Finset.mem_filter.mpr ⟨hc, hct⟩))
      (by linarith [hc_Ioo.2])

/-- Method version: find the consecutive closed-partition pair containing `t`. -/
private lemma exists_consecutive_pair_containing (γ : ClosedPwC1Curve x)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (htn : t ∉ γ.closedPartition) :
    ∃ a b, γ.closedPartition.IsConsecutive a b ∧ t ∈ Ioo a b :=
  exists_consecutive_pair_aux γ.zero_mem_closedPartition γ.one_mem_closedPartition ht htn

/-- Smart constructor for `ClosedPwC1Curve`: builds the structure from a `Path x x`
together with the closed-partition data, deriving the inherited `PiecewiseC1Path`
fields (Ioo-style `partition`, differentiability, derivative continuity) from
`contDiffOn_pieces`. -/
def ofClosedPartition (toPath : Path x x) (closedPartition : Finset ℝ)
    (zero_mem : (0 : ℝ) ∈ closedPartition) (one_mem : (1 : ℝ) ∈ closedPartition)
    (subset : (closedPartition : Set ℝ) ⊆ Icc 0 1)
    (contDiffOn_pieces : ∀ a b, closedPartition.IsConsecutive a b →
      ContDiffOn ℝ 1 toPath.extend (Icc a b)) :
    ClosedPwC1Curve x := by
  classical
  set partition : Finset ℝ := (closedPartition.erase 0).erase 1
  have h_eq_closed : closedPartition = insert 0 (insert 1 partition) := by
    ext s
    by_cases h0 : s = 0
    · simp [h0, zero_mem]
    by_cases h1 : s = 1
    · simp [h1, one_mem]
    simp [partition, Finset.mem_insert, Finset.mem_erase, h0, h1]
  have partition_subset_Ioo : (partition : Set ℝ) ⊆ Ioo (0 : ℝ) 1 := fun t ht => by
    obtain ⟨h_ne_1, ht'⟩ := Finset.mem_erase.mp ht
    obtain ⟨h_ne_0, h_in⟩ := Finset.mem_erase.mp ht'
    have h_in_Icc := subset h_in
    exact ⟨lt_of_le_of_ne h_in_Icc.1 (Ne.symm h_ne_0),
           lt_of_le_of_ne h_in_Icc.2 h_ne_1⟩
  have not_in_closed_of_not_in_part : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 → t ∉ partition →
      t ∉ closedPartition := fun {t} ht htn h_in => htn <|
    Finset.mem_erase.mpr ⟨ne_of_lt ht.2,
      Finset.mem_erase.mpr ⟨(ne_of_lt ht.1).symm, h_in⟩⟩
  refine
    { toFun := toPath.extend
      source := toPath.extend_zero
      target := toPath.extend_one
      continuous_toFun := toPath.continuous_extend.continuousOn
      toPath := toPath
      toPath_extend_eq_toFun := fun _ _ => rfl
      partition := partition
      partition_subset := partition_subset_Ioo
      differentiable_off := ?_
      deriv_continuous_off := ?_
      closedPartition := closedPartition
      zero_mem_closedPartition := zero_mem
      one_mem_closedPartition := one_mem
      closedPartition_subset := subset
      closedPartition_eq := h_eq_closed
      contDiffOn_pieces := contDiffOn_pieces }
  · intro t ht htn
    obtain ⟨a, b, hcons, ht_Ioo⟩ :=
      exists_consecutive_pair_aux zero_mem one_mem ht (not_in_closed_of_not_in_part ht htn)
    exact ((contDiffOn_pieces a b hcons).differentiableOn_one t
      (Ioo_subset_Icc_self ht_Ioo)).differentiableAt (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2)
  · intro t ht htn
    obtain ⟨a, b, hcons, ht_Ioo⟩ :=
      exists_consecutive_pair_aux zero_mem one_mem ht (not_in_closed_of_not_in_part ht htn)
    have h_dw_cont : ContinuousOn (derivWithin toPath.extend (Icc a b)) (Icc a b) :=
      (contDiffOn_pieces a b hcons).continuousOn_derivWithin
        (uniqueDiffOn_Icc hcons.2.2.1) le_rfl
    refine ((h_dw_cont t (Ioo_subset_Icc_self ht_Ioo)).continuousAt
      (Icc_mem_nhds ht_Ioo.1 ht_Ioo.2)).congr (Filter.eventuallyEq_of_mem
        (Ioo_mem_nhds ht_Ioo.1 ht_Ioo.2) fun _ hu => derivWithin_eq_deriv_on_Ioo _ hu)

end ClosedPwC1Curve

namespace ClosedPwC1Immersion

variable {x : E}

/-- Helper for the immersion bridge: at an interior closed-partition point `p`, the
predecessor `a := max{c ∈ closedPartition : c < p}` is well-defined and `(a, p)` is
consecutive. -/
private lemma exists_predecessor (γ : ClosedPwC1Immersion x) {p : ℝ}
    (hp_in : p ∈ γ.closedPartition) (hp_pos : 0 < p) :
    ∃ a, γ.closedPartition.IsConsecutive a p := by
  set pred := γ.closedPartition.filter (· < p)
  have h0_pred : (0 : ℝ) ∈ pred :=
    Finset.mem_filter.mpr ⟨γ.zero_mem_closedPartition, hp_pos⟩
  have ha_mem : pred.max' ⟨0, h0_pred⟩ ∈ pred := pred.max'_mem _
  exact ⟨_, (Finset.mem_filter.mp ha_mem).1, hp_in, (Finset.mem_filter.mp ha_mem).2,
    fun c hc hc_Ioo => absurd (pred.le_max' c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.2⟩))
      (by linarith [hc_Ioo.1])⟩

/-- Helper for the immersion bridge: at an interior closed-partition point `p`, the
successor `b := min{c ∈ closedPartition : p < c}` is well-defined and `(p, b)` is
consecutive. -/
private lemma exists_successor (γ : ClosedPwC1Immersion x) {p : ℝ}
    (hp_in : p ∈ γ.closedPartition) (hp_lt_one : p < 1) :
    ∃ b, γ.closedPartition.IsConsecutive p b := by
  set succ := γ.closedPartition.filter (p < ·)
  have h1_succ : (1 : ℝ) ∈ succ :=
    Finset.mem_filter.mpr ⟨γ.one_mem_closedPartition, hp_lt_one⟩
  have hb_mem : succ.min' ⟨1, h1_succ⟩ ∈ succ := succ.min'_mem _
  exact ⟨_, hp_in, (Finset.mem_filter.mp hb_mem).1, (Finset.mem_filter.mp hb_mem).2,
    fun c hc hc_Ioo => absurd (succ.min'_le c (Finset.mem_filter.mpr ⟨hc, hc_Ioo.1⟩))
      (by linarith [hc_Ioo.2])⟩

/-- Shared inner computation for `left_deriv_limit` / `right_deriv_limit` in
`toPwC1Immersion`. Given a piece `Icc a b` with `a < b` and a designated endpoint
`p ∈ {a, b}`, produces the one-sided derivative limit `Tendsto (deriv γ̃) (𝓝[hSide] p)`
where `hSide` is the one-sided neighborhood toward the *interior* of `Icc a b`. -/
private lemma toPwC1Immersion_deriv_limit_aux (γ : ClosedPwC1Immersion x) {a b : ℝ}
    (hcons : γ.closedPartition.IsConsecutive a b) {p : ℝ} (hp : p ∈ Icc a b)
    (S : Set ℝ) (hSeq : 𝓝[S] p = 𝓝[Ioo a b] p) :
    ∃ L : E, L ≠ 0 ∧ Tendsto (deriv γ.toPath.extend) (𝓝[S] p) (𝓝 L) := by
  have hab : a < b := hcons.2.2.1
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    (γ.contDiffOn_pieces a b hcons).continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl
  refine ⟨derivWithin γ.toPath.extend (Icc a b) p,
    γ.derivWithin_ne_zero_pieces a b hcons p hp, ?_⟩
  refine (hSeq ▸ (h_dw_cont p hp).mono_left
    (nhdsWithin_mono _ Ioo_subset_Icc_self)).congr' ?_
  rw [hSeq]
  exact Filter.eventuallyEq_of_mem (s := Ioo a b) self_mem_nhdsWithin
    fun _ hu => ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo _ hu

/-- A `ClosedPwC1Immersion` produces a legacy `PwC1Immersion`. -/
def toPwC1Immersion (γ : ClosedPwC1Immersion x) : PwC1Immersion x x where
  toPiecewiseC1Path := γ.toPiecewiseC1Path
  deriv_ne_zero := by
    intro t ht htn
    have htn_closed : t ∉ γ.closedPartition := fun h_in => htn
      (γ.toClosedPwC1Curve.mem_partition_iff.mpr ⟨h_in, ne_of_gt ht.1, ne_of_lt ht.2⟩)
    obtain ⟨a, b, hcons, ht_Ioo⟩ :=
      γ.toClosedPwC1Curve.exists_consecutive_pair_containing ht htn_closed
    have h_dw_ne :=
      γ.derivWithin_ne_zero_pieces a b hcons t (Ioo_subset_Icc_self ht_Ioo)
    change deriv γ.toPath.extend t ≠ 0
    rwa [ClosedPwC1Curve.derivWithin_eq_deriv_on_Ioo _ ht_Ioo] at h_dw_ne
  left_deriv_limit := by
    intro p hp
    have hp_in : p ∈ γ.closedPartition := (γ.toClosedPwC1Curve.mem_partition_iff.mp hp).1
    obtain ⟨a, hcons⟩ := γ.exists_predecessor hp_in (γ.partition_subset hp).1
    refine γ.toPwC1Immersion_deriv_limit_aux hcons (right_mem_Icc.mpr hcons.2.2.1.le) _ ?_
    rw [← Set.Iio_inter_Ioi (a := p) (b := a),
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcons.2.2.1))]
  right_deriv_limit := by
    intro p hp
    have hp_in : p ∈ γ.closedPartition := (γ.toClosedPwC1Curve.mem_partition_iff.mp hp).1
    obtain ⟨b, hcons⟩ := γ.exists_successor hp_in (γ.partition_subset hp).2
    refine γ.toPwC1Immersion_deriv_limit_aux hcons (left_mem_Icc.mpr hcons.2.2.1.le) _ ?_
    rw [← Set.Ioi_inter_Iio (a := p) (b := b),
      nhdsWithin_inter_of_mem' (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hcons.2.2.1))]

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
  -- Ordered-pair version: prove the bound for x ≤ b ≤ y.
  have split : ∀ {x y : ℝ}, x ∈ Icc a c → y ∈ Icc a c → x ≤ b → b ≤ y →
      ‖f x - f y‖ ≤ C * ‖x - y‖ := by
    intro x y hx hy hxb hby
    have h1 := hf₁ ⟨hx.1, hxb⟩ ⟨hab, le_refl b⟩
    have h2 := hf₂ ⟨le_refl b, hbc⟩ ⟨hby, hy.2⟩
    have h_dist : ‖x - y‖ = ‖x - b‖ + ‖b - y‖ := by
      simp only [Real.norm_eq_abs, abs_of_nonpos (by linarith : x - y ≤ 0),
        abs_of_nonpos (by linarith : x - b ≤ 0), abs_of_nonpos (by linarith : b - y ≤ 0)]
      ring
    calc ‖f x - f y‖
        = ‖(f x - f b) + (f b - f y)‖ := by congr 1; abel
      _ ≤ ‖f x - f b‖ + ‖f b - f y‖ := norm_add_le _ _
      _ ≤ (C : ℝ) * ‖x - b‖ + (C : ℝ) * ‖b - y‖ := by gcongr
      _ = (C : ℝ) * ‖x - y‖ := by rw [← mul_add, ← h_dist]
  intro x hx y hy
  rcases le_total x y with hxy | hxy
  · rcases le_total y b with hyb | hby
    · exact hf₁ ⟨hx.1, hxy.trans hyb⟩ ⟨hx.1.trans hxy, hyb⟩
    · rcases le_total x b with hxb | hbx
      · exact split hx hy hxb hby
      · exact hf₂ ⟨hbx, hx.2⟩ ⟨hbx.trans hxy, hy.2⟩
  · rw [norm_sub_rev (f x) (f y), norm_sub_rev x y]
    rcases le_total x b with hxb | hbx
    · exact hf₁ ⟨hy.1, hxy.trans hxb⟩ ⟨hy.1.trans hxy, hxb⟩
    · rcases le_total y b with hyb | hby
      · exact split hy hx hyb hbx
      · exact hf₂ ⟨hby, hy.2⟩ ⟨hby.trans hxy, hx.2⟩

/-- Inductive gluing: piecewise-`LipschitzOnWith` on consecutive pieces yields
global `LipschitzOnWith` on `Icc a b` containing all pieces. -/
private lemma lipschitzOnWith_of_consecutive_pieces {E : Type*}
    [NormedAddCommGroup E] {f : ℝ → E} {C : NNReal} (s : Finset ℝ) (a b : ℝ)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≤ b)
    (hbds : ∀ c ∈ s, a ≤ c ∧ c ≤ b)
    (hpc : ∀ p q, s.IsConsecutive p q → LipschitzOnWith C f (Icc p q)) :
    LipschitzOnWith C f (Icc a b) := by
  refine consecutive_piece_induction (P := fun p q => p ≤ q ∧ LipschitzOnWith C f (Icc p q))
    (fun x => ⟨le_refl x, ?_⟩) (fun {p q r} h1 h2 => ⟨h1.1.trans h2.1,
      lipschitzOnWith_Icc_trans h1.1 h2.1 h1.2 h2.2⟩) s a b ha hb hab hbds
    (fun p q hcons => ⟨hcons.2.2.1.le, hpc p q hcons⟩) |>.2
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro y hy z hz
  simp [le_antisymm hy.2 hy.1, le_antisymm hz.2 hz.1]

namespace ClosedPwC1Curve

variable {x : E}

/-- On each closed piece between consecutive partition members, `γ.toPath.extend`
is Lipschitz with the maximum of `‖derivWithin γ.toPath.extend (Icc a b) t‖`
on the piece. -/
theorem lipschitzOnWith_piece (γ : ClosedPwC1Curve x) {a b : ℝ}
    (h : γ.closedPartition.IsConsecutive a b) :
    ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc a b) := by
  have hab : a ≤ b := h.2.2.1.le
  have hcd : ContDiffOn ℝ 1 γ.toPath.extend (Icc a b) := γ.contDiffOn_pieces a b h
  have h_dw_cont : ContinuousOn (derivWithin γ.toPath.extend (Icc a b)) (Icc a b) :=
    hcd.continuousOn_derivWithin (uniqueDiffOn_Icc h.2.2.1) le_rfl
  obtain ⟨t₀, _, ht₀_max⟩ :=
    isCompact_Icc.exists_isMaxOn ⟨a, left_mem_Icc.mpr hab⟩ h_dw_cont.norm
  refine ⟨⟨_, norm_nonneg (derivWithin γ.toPath.extend (Icc a b) t₀)⟩, ?_⟩
  exact Convex.lipschitzOnWith_of_nnnorm_derivWithin_le (convex_Icc _ _)
    hcd.differentiableOn_one fun u hu => ht₀_max hu

/-- Existence of a global Lipschitz constant on `Icc 0 1`, by gluing the
piece-wise constants. -/
theorem lipschitzOnWith_Icc01 (γ : ClosedPwC1Curve x) :
    ∃ K : NNReal, LipschitzOnWith K γ.toPath.extend (Icc (0 : ℝ) 1) := by
  classical
  set pairs : Finset (ℝ × ℝ) := (γ.closedPartition.product γ.closedPartition).filter
    (fun p => γ.closedPartition.IsConsecutive p.1 p.2)
  have h_each : ∀ p ∈ pairs, ∃ K : NNReal,
      LipschitzOnWith K γ.toPath.extend (Icc p.1 p.2) := fun p hp =>
    γ.lipschitzOnWith_piece (Finset.mem_filter.mp hp).2
  choose K hK using h_each
  set Kmax : NNReal := pairs.attach.sup (fun p => K p.1 p.2)
  refine ⟨Kmax, lipschitzOnWith_of_consecutive_pieces γ.closedPartition 0 1
    γ.zero_mem_closedPartition γ.one_mem_closedPartition zero_le_one
    (fun _ hc => ⟨(γ.closedPartition_subset hc).1, (γ.closedPartition_subset hc).2⟩) ?_⟩
  intro p q hcons
  have hpq_in : (p, q) ∈ pairs := Finset.mem_filter.mpr
    ⟨Finset.mem_product.mpr ⟨hcons.1, hcons.2.1⟩, hcons⟩
  exact (hK (p, q) hpq_in).weaken <| Finset.le_sup (s := pairs.attach)
    (f := fun p => K p.1 p.2) (Finset.mem_attach pairs ⟨(p, q), hpq_in⟩)

/-- A `ClosedPwC1Curve` extends to a globally Lipschitz function `ℝ → E`.
Outside `[0, 1]`, the extended path is constant. -/
theorem lipschitzWith_extend (γ : ClosedPwC1Curve x) :
    ∃ K : NNReal, LipschitzWith K γ.toPath.extend := by
  obtain ⟨K, hK⟩ := γ.lipschitzOnWith_Icc01
  rw [lipschitzOnWith_iff_norm_sub_le] at hK
  refine ⟨K, ?_⟩
  rw [lipschitzWith_iff_norm_sub_le]
  intro s t
  set s' : ℝ := max 0 (min s 1)
  set t' : ℝ := max 0 (min t 1)
  have clamp_mem : ∀ u : ℝ, max 0 (min u 1) ∈ Icc (0 : ℝ) 1 := fun _ =>
    ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hclamp : ∀ u : ℝ, γ.toPath.extend u = γ.toPath.extend (max 0 (min u 1)) := by
    intro u
    rcases le_total u 0 with hu0 | hu0
    · rw [γ.toPath.extend_of_le_zero hu0,
        show max 0 (min u 1) = 0 from by
          simp [min_eq_left (hu0.trans zero_le_one), max_eq_left hu0],
        γ.toPath.extend_zero]
    · rcases le_total u 1 with hu1 | hu1
      · simp [min_eq_left hu1, max_eq_right hu0]
      · rw [γ.toPath.extend_of_one_le hu1,
          show max 0 (min u 1) = 1 from by simp [min_eq_right hu1], γ.toPath.extend_one]
  have h_proj_lip : ‖s' - t'‖ ≤ ‖s - t‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |s' - t'|
        ≤ max |(0 : ℝ) - 0| |min s 1 - min t 1| := abs_max_sub_max_le_max _ _ _ _
      _ = |min s 1 - min t 1| := by simp
      _ ≤ max |s - t| |(1 : ℝ) - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = |s - t| := by simp
  rw [hclamp s, hclamp t]
  exact (hK (clamp_mem s) (clamp_mem t)).trans
    (mul_le_mul_of_nonneg_left h_proj_lip (NNReal.coe_nonneg _))

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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
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
  rw [if_neg (by linarith [hτ.1] : ¬ (1 + τ ≤ 1))]
  congr 1; ring

omit [NormedSpace ℝ E] in
/-- Continuity of `cyclicShiftFun` for a continuous closed loop. -/
theorem Continuous.cyclicShiftFun {f : ℝ → E} (hf : Continuous f) {τ : ℝ}
    (hclosed : f 0 = f 1) : Continuous (cyclicShiftFun f τ) := by
  show Continuous (fun t => if t + τ ≤ 1 then f (t + τ) else f (t + τ - 1))
  apply Continuous.if_le (f' := fun t => f (t + τ)) (g' := fun t => f (t + τ - 1))
    (f := fun t => t + τ) (g := fun _ => (1 : ℝ))
    (hf.comp (by fun_prop)) (hf.comp (by fun_prop)) (by fun_prop) continuous_const
  intro t ht_eq
  rw [ht_eq, show (1 : ℝ) - 1 = 0 by ring]
  exact hclosed.symm

/-! ### `cyclicShiftPath` — building a `Path` -/

/-- The cyclic-shift `Path` from `γ(τ)` to `γ(τ)`. -/
noncomputable def Path.cyclicShift {x : E} (γ : Path x x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) : Path (γ.extend τ) (γ.extend τ) where
  toFun := fun t => cyclicShiftFun γ.extend τ (t : ℝ)
  continuous_toFun := (Continuous.cyclicShiftFun γ.continuous_extend
    (by rw [γ.extend_zero, γ.extend_one])).comp continuous_subtype_val
  source' := by
    simp only [Set.Icc.coe_zero]
    exact cyclicShiftFun_zero γ.extend hτ
  target' := by
    simp only [Set.Icc.coe_one]
    exact cyclicShiftFun_one γ.extend hτ (by rw [γ.extend_zero, γ.extend_one])

omit [NormedSpace ℝ E] in
/-- Endpoints of `Path.cyclicShift`. -/
theorem Path.cyclicShift_apply {x : E} (γ : Path x x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) (t : ↑(Set.Icc (0 : ℝ) 1)) :
    γ.cyclicShift hτ t = cyclicShiftFun γ.extend τ (t : ℝ) := rfl

omit [NormedSpace ℝ E] in
/-- The extend of `Path.cyclicShift` agrees with `cyclicShiftFun` on `[0, 1]`. -/
theorem Path.cyclicShift_extend_on_Icc {x : E} (γ : Path x x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (γ.cyclicShift hτ).extend t = cyclicShiftFun γ.extend τ t := by
  rw [Path.extend_apply _ ht, Path.cyclicShift_apply]

/-! ### `cyclicShiftPath` — partition of the shifted curve

The partition of the shifted curve `γ'` consists of:
* `0`, `1`, and `1 - τ` (the new corner partition point);
* shifted-back partition points of `γ` itself.

Concretely, if `γ.closedPartition = {0, p₁, p₂, …, pₙ, 1}` with `p₁ < … < pₙ`, and we
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
    ((cyclicShiftPartition P τ : Finset ℝ) : Set ℝ) ⊆ Set.Icc (0 : ℝ) 1 :=
  fun _ ht => ((mem_cyclicShiftPartition_iff P τ _).mp ht).1

/-! ### Consecutive-pair lifting under cyclic shift (T-BR-Y8d Step 1)

For a cyclic shift by `τ ∈ Ioo 0 1`, the *new* partition is
`cyclicShiftPartition γ.closedPartition τ ∪ {0, 1, 1 - τ}`. For each consecutive pair
`(a, b)` in the new partition, either:

* `b ≤ 1 - τ`, in which case `[a + τ, b + τ] ⊆ Icc c d` for some consecutive
  pair `(c, d)` in `γ.closedPartition ∪ {τ}`, hence `[a + τ, b + τ]` is contained in a
  single original γ-piece (possibly subdivided by `τ`); OR
* `a ≥ 1 - τ`, in which case `[a + τ - 1, b + τ - 1] ⊆ Icc c d` for some
  consecutive pair in `γ.closedPartition ∪ {τ}`.

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
  by_contra! h
  obtain ⟨h_lt_b, h_a_lt⟩ := h
  exact h_cons.2.2.2 (1 - τ) (oneSubTau_mem_cyclicShiftPartitionExt P τ) ⟨h_a_lt, h_lt_b⟩

namespace ClosedPwC1Curve

variable {x : E}

/-- Auxiliary helper for `cyclicShift_consecutive_lift_*`: given an interval
`[a', b'] ⊆ [0, 1]` with `a' < b'`, find consecutive partition members `(c, d)`
containing it, using a hypothesis that every interior partition member would
contradict `(a, b)` being consecutive in the shifted partition. -/
private lemma cyclicShift_consecutive_lift_aux (γ : ClosedPwC1Curve x)
    {a' b' : ℝ} (h0_le_a' : 0 ≤ a') (h_b'_le : b' ≤ 1) (h_a'b' : a' < b')
    (h_no_interior : ∀ e ∈ γ.closedPartition, e ∈ Ioo a' b' → False) :
    ∃ c d, γ.closedPartition.IsConsecutive c d ∧ Icc a' b' ⊆ Icc c d := by
  classical
  set Pl : Finset ℝ := γ.closedPartition.filter (· ≤ a')
  have h0_in_Pl : (0 : ℝ) ∈ Pl :=
    Finset.mem_filter.mpr ⟨γ.zero_mem_closedPartition, h0_le_a'⟩
  have hc_mem : Pl.max' ⟨0, h0_in_Pl⟩ ∈ Pl := Pl.max'_mem _
  have hc_le : Pl.max' ⟨0, h0_in_Pl⟩ ≤ a' := (Finset.mem_filter.mp hc_mem).2
  set Pr : Finset ℝ := γ.closedPartition.filter (b' ≤ ·)
  have h1_in_Pr : (1 : ℝ) ∈ Pr := Finset.mem_filter.mpr ⟨γ.one_mem_closedPartition, h_b'_le⟩
  have hd_mem : Pr.min' ⟨1, h1_in_Pr⟩ ∈ Pr := Pr.min'_mem _
  have hd_ge : b' ≤ Pr.min' ⟨1, h1_in_Pr⟩ := (Finset.mem_filter.mp hd_mem).2
  refine ⟨_, _, ⟨(Finset.mem_filter.mp hc_mem).1, (Finset.mem_filter.mp hd_mem).1,
    hc_le.trans_lt (h_a'b'.trans_le hd_ge), fun e he_in he_Ioo => ?_⟩,
    fun _ ht => ⟨hc_le.trans ht.1, ht.2.trans hd_ge⟩⟩
  rcases le_or_gt e a' with he_le | he_gt
  · exact absurd (Pl.le_max' e (Finset.mem_filter.mpr ⟨he_in, he_le⟩))
      (not_le_of_gt he_Ioo.1)
  rcases le_or_gt b' e with he_ge | he_lt
  · exact absurd (Pr.min'_le e (Finset.mem_filter.mpr ⟨he_in, he_ge⟩))
      (not_le_of_gt he_Ioo.2)
  exact h_no_interior e he_in ⟨he_gt, he_lt⟩

/-- **Step 1: cyclicShift consecutive lift (case 1, no wraparound).** For a
consecutive pair `(a, b)` in the cyclic-shift partition with `b ≤ 1 - τ`, the
interval `[a + τ, b + τ]` lies inside a γ-piece of the original partition. -/
theorem cyclicShift_consecutive_lift_no_wrap (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.closedPartition τ).IsConsecutive a b)
    (h_b_le : b ≤ 1 - τ) :
    ∃ c d, γ.closedPartition.IsConsecutive c d ∧ Icc (a + τ) (b + τ) ⊆ Icc c d := by
  obtain ⟨ha_in, _, h_ab_lt, h_no_between⟩ := h_cons
  have ha_ge : 0 ≤ a := (cyclicShiftPartitionExt_subset_Icc γ.closedPartition hτ ha_in).1
  refine γ.cyclicShift_consecutive_lift_aux (by linarith [hτ.1]) (by linarith)
    (by linarith) fun e he_in he_Ioo => ?_
  have h_e_in_Icc : e - τ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hτ.1, ha_ge, he_Ioo.1], by linarith [hτ.1, h_b_le, he_Ioo.2]⟩
  have h_csp : e - τ ∈ cyclicShiftPartition γ.closedPartition τ :=
    (mem_cyclicShiftPartition_iff _ _ _).mpr
      ⟨h_e_in_Icc, Or.inl (by convert he_in using 1; ring)⟩
  exact h_no_between (e - τ) ((mem_cyclicShiftPartitionExt_iff _ _ _).mpr
    (Or.inr (Or.inr (Or.inr h_csp))))
    ⟨by linarith [he_Ioo.1], by linarith [he_Ioo.2]⟩

/-- **Step 1: cyclicShift consecutive lift (case 2, with wraparound).** For a
consecutive pair `(a, b)` in the cyclic-shift partition with `a ≥ 1 - τ`, the
interval `[a + τ - 1, b + τ - 1]` lies inside a γ-piece of the original
partition. -/
theorem cyclicShift_consecutive_lift_wrap (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.closedPartition τ).IsConsecutive a b)
    (h_a_ge : a ≥ 1 - τ) :
    ∃ c d, γ.closedPartition.IsConsecutive c d ∧ Icc (a + τ - 1) (b + τ - 1) ⊆ Icc c d := by
  obtain ⟨_, hb_in, h_ab_lt, h_no_between⟩ := h_cons
  have hb_le_1 : b ≤ 1 := (cyclicShiftPartitionExt_subset_Icc γ.closedPartition hτ hb_in).2
  refine γ.cyclicShift_consecutive_lift_aux (by linarith) (by linarith [hτ.2])
    (by linarith) fun e he_in he_Ioo => ?_
  have h_shift_in_Icc : e + 1 - τ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by linarith [hτ.2, h_a_ge, he_Ioo.1], by linarith [hτ.1, hb_le_1, he_Ioo.2]⟩
  have h_csp : e + 1 - τ ∈ cyclicShiftPartition γ.closedPartition τ :=
    (mem_cyclicShiftPartition_iff _ _ _).mpr
      ⟨h_shift_in_Icc, Or.inr (by convert he_in using 1; ring)⟩
  exact h_no_between (e + 1 - τ) ((mem_cyclicShiftPartitionExt_iff _ _ _).mpr
    (Or.inr (Or.inr (Or.inr h_csp))))
    ⟨by linarith [he_Ioo.1], by linarith [he_Ioo.2]⟩

/-- **Step 1 (combined): cyclicShift consecutive lift.** For a consecutive pair
`(a, b)` in the cyclic-shift partition, either there's no wraparound (`b ≤ 1-τ`)
and `[a + τ, b + τ]` lies in a γ-piece, or there is wraparound (`a ≥ 1-τ`) and
`[a + τ - 1, b + τ - 1]` lies in a γ-piece. -/
theorem cyclicShift_consecutive_lift (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0:ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.closedPartition τ).IsConsecutive a b) :
    (b ≤ 1 - τ ∧
        ∃ c d, γ.closedPartition.IsConsecutive c d ∧ Icc (a + τ) (b + τ) ⊆ Icc c d) ∨
    (a ≥ 1 - τ ∧
        ∃ c d, γ.closedPartition.IsConsecutive c d ∧
          Icc (a + τ - 1) (b + τ - 1) ⊆ Icc c d) := by
  rcases not_straddle_oneSubTau γ.closedPartition h_cons with h_b_le | h_a_ge
  · exact Or.inl ⟨h_b_le, γ.cyclicShift_consecutive_lift_no_wrap hτ h_cons h_b_le⟩
  · exact Or.inr ⟨h_a_ge, γ.cyclicShift_consecutive_lift_wrap hτ h_cons h_a_ge⟩

end ClosedPwC1Curve

/-! ### Step 2: `ClosedPwC1Curve.cyclicShift` constructor

We build the shifted curve as a paper-faithful `ClosedPwC1Curve`. The closed
partition is `cyclicShiftPartitionExt γ.closedPartition τ` and the underlying
path is `γ.toPath.cyclicShift hτ`. The `ContDiffOn` field on each piece is
established by the consecutive-pair lift (Step 1). -/

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The cyclic-shifted curve agrees on `Icc 0 (1 - τ)` with the original curve
shifted by `+τ`. -/
private lemma cyclicShiftFun_eq_on_no_wrap (f : ℝ → E) {τ : ℝ}
    (_hτ : τ ∈ Ioo (0 : ℝ) 1) :
    Set.EqOn (cyclicShiftFun f τ) (fun t => f (t + τ)) (Icc (0 : ℝ) (1 - τ)) := by
  intro t ht
  simp only [cyclicShiftFun]
  rw [if_pos (by linarith [ht.2] : t + τ ≤ 1)]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
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
    rw [h1, show (1 : ℝ) - 1 = 0 by ring]
    exact hclosed.symm
  · -- t > 1 - τ: cyclicShiftFun gives f (t + τ - 1) via if_neg
    rw [if_neg (by linarith : ¬ (t + τ ≤ 1))]

namespace ClosedPwC1Curve

variable {x : E}

/-- The shifted curve is `ContDiffOn ℝ 1` on each consecutive piece (Step 2). -/
private theorem cyclicShift_extend_contDiffOn_piece (γ : ClosedPwC1Curve x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.closedPartition τ).IsConsecutive a b) :
    ContDiffOn ℝ 1 (γ.toPath.cyclicShift hτ).extend (Icc a b) := by
  have ha_Icc := cyclicShiftPartitionExt_subset_Icc γ.closedPartition hτ h_cons.1
  have hb_Icc := cyclicShiftPartitionExt_subset_Icc γ.closedPartition hτ h_cons.2.1
  have hab_Icc : Icc a b ⊆ Icc (0:ℝ) 1 := fun t ht => ⟨ha_Icc.1.trans ht.1, ht.2.trans hb_Icc.2⟩
  have hclosed : γ.toPath.extend 0 = γ.toPath.extend 1 := by
    rw [γ.toPath.extend_zero, γ.toPath.extend_one]
  have h_eq_csf : Set.EqOn (γ.toPath.cyclicShift hτ).extend
      (cyclicShiftFun γ.toPath.extend τ) (Icc a b) := fun _ ht =>
    Path.cyclicShift_extend_on_Icc γ.toPath hτ (hab_Icc ht)
  rcases γ.cyclicShift_consecutive_lift hτ h_cons with
    ⟨h_b_le, c, d, h_cons_cd, h_sub⟩ | ⟨h_a_ge, c, d, h_cons_cd, h_sub⟩
  · have hab_sub : Icc a b ⊆ Icc (0:ℝ) (1 - τ) :=
      fun _ ht => ⟨ha_Icc.1.trans ht.1, ht.2.trans h_b_le⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun t => γ.toPath.extend (t + τ)) (Icc a b) := fun t ht => by
      rw [h_eq_csf ht]
      exact cyclicShiftFun_eq_on_no_wrap γ.toPath.extend hτ (hab_sub ht)
    have h_maps_to : MapsTo (fun t : ℝ => t + τ) (Icc a b) (Icc c d) :=
      fun _ ht => h_sub ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((γ.contDiffOn_pieces c d h_cons_cd).comp
      (contDiff_id.add contDiff_const).contDiffOn h_maps_to).congr h_eq_shifted
  · have hab_sub : Icc a b ⊆ Icc (1 - τ) 1 :=
      fun _ ht => ⟨h_a_ge.trans ht.1, ht.2.trans hb_Icc.2⟩
    have h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
        (fun t => γ.toPath.extend (t + τ - 1)) (Icc a b) := fun t ht => by
      rw [h_eq_csf ht]
      exact cyclicShiftFun_eq_on_wrap γ.toPath.extend hτ hclosed (hab_sub ht)
    have h_maps_to : MapsTo (fun t : ℝ => t + τ - 1) (Icc a b) (Icc c d) :=
      fun _ ht => h_sub ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact ((γ.contDiffOn_pieces c d h_cons_cd).comp
      ((contDiff_id.add contDiff_const).sub contDiff_const).contDiffOn h_maps_to).congr h_eq_shifted

/-- **Step 2: Cyclic shift of a `ClosedPwC1Curve`.** -/
noncomputable def cyclicShift (γ : ClosedPwC1Curve x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ClosedPwC1Curve (γ.toPath.extend τ) :=
  ofClosedPartition (γ.toPath.cyclicShift hτ) (cyclicShiftPartitionExt γ.closedPartition τ)
    (zero_mem_cyclicShiftPartitionExt γ.closedPartition τ)
    (one_mem_cyclicShiftPartitionExt γ.closedPartition τ)
    (cyclicShiftPartitionExt_subset_Icc γ.closedPartition hτ)
    (fun _ _ h_cons => γ.cyclicShift_extend_contDiffOn_piece hτ h_cons)

end ClosedPwC1Curve

/-! ### Step 3: `ClosedPwC1Immersion.cyclicShift`

For an immersion, additionally we need `derivWithin _ (Icc a b) t ≠ 0` on each
piece. We obtain this from the original immersion's `derivWithin_ne_zero_pieces`
property by chain rule. -/

namespace ClosedPwC1Immersion

variable {x : E}

/-- On each piece of the cyclic shift, the (within-`Icc a b`) derivative is
nonzero — branch helper for a fixed shift `φ : ℝ → ℝ` with constant derivative `1`. -/
private theorem cyclicShift_derivWithin_ne_zero_branch (γ : ClosedPwC1Immersion x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.closedPartition τ).IsConsecutive a b)
    {t : ℝ} (ht : t ∈ Icc a b)
    {c d : ℝ} (h_cons_cd : γ.closedPartition.IsConsecutive c d)
    (φ : ℝ → ℝ) (hφ_deriv : HasDerivWithinAt φ 1 (Icc a b) t)
    (h_eq_shifted : Set.EqOn (γ.toPath.cyclicShift hτ).extend
      (fun u => γ.toPath.extend (φ u)) (Icc a b))
    (h_maps_to : MapsTo φ (Icc a b) (Icc c d)) :
    derivWithin (γ.toPath.cyclicShift hτ).extend (Icc a b) t ≠ 0 := by
  have h_unique : UniqueDiffWithinAt ℝ (Icc a b) t :=
    uniqueDiffOn_Icc h_cons.2.2.1 t ht
  set L : E := derivWithin γ.toPath.extend (Icc c d) (φ t)
  have h_HDwa_γ : HasDerivWithinAt γ.toPath.extend L (Icc c d) (φ t) :=
    ((γ.contDiffOn_pieces c d h_cons_cd).differentiableOn_one
      (φ t) (h_maps_to ht)).hasDerivWithinAt
  have h_comp' : HasDerivWithinAt (fun u : ℝ => γ.toPath.extend (φ u)) L (Icc a b) t := by
    simpa [Function.comp_def, one_smul] using h_HDwa_γ.scomp t hφ_deriv h_maps_to
  rw [(h_comp'.congr h_eq_shifted (h_eq_shifted ht)).derivWithin h_unique]
  exact γ.derivWithin_ne_zero_pieces c d h_cons_cd _ (h_maps_to ht)

/-- On each piece of the cyclic shift, the (within-`Icc a b`) derivative is
nonzero. -/
private theorem cyclicShift_derivWithin_ne_zero_piece (γ : ClosedPwC1Immersion x)
    {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) {a b : ℝ}
    (h_cons : (cyclicShiftPartitionExt γ.closedPartition τ).IsConsecutive a b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    derivWithin (γ.toPath.cyclicShift hτ).extend (Icc a b) t ≠ 0 := by
  have ha_Icc := cyclicShiftPartitionExt_subset_Icc γ.closedPartition hτ h_cons.1
  have hb_Icc := cyclicShiftPartitionExt_subset_Icc γ.closedPartition hτ h_cons.2.1
  have hab_Icc : Icc a b ⊆ Icc (0:ℝ) 1 :=
    fun u hu => ⟨ha_Icc.1.trans hu.1, hu.2.trans hb_Icc.2⟩
  have hclosed : γ.toPath.extend 0 = γ.toPath.extend 1 := by
    rw [γ.toPath.extend_zero, γ.toPath.extend_one]
  have h_eq_csf : Set.EqOn (γ.toPath.cyclicShift hτ).extend
      (cyclicShiftFun γ.toPath.extend τ) (Icc a b) := fun _ hu =>
    Path.cyclicShift_extend_on_Icc γ.toPath hτ (hab_Icc hu)
  rcases γ.toClosedPwC1Curve.cyclicShift_consecutive_lift hτ h_cons with
    ⟨h_b_le, c, d, h_cons_cd, h_sub⟩ | ⟨h_a_ge, c, d, h_cons_cd, h_sub⟩
  · refine γ.cyclicShift_derivWithin_ne_zero_branch hτ h_cons ht h_cons_cd
      (fun u => u + τ) ((hasDerivAt_id t).add_const τ).hasDerivWithinAt
      (fun u hu => ?_) (fun _ hu => h_sub ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    rw [h_eq_csf hu]
    exact cyclicShiftFun_eq_on_no_wrap γ.toPath.extend hτ
      ⟨ha_Icc.1.trans hu.1, hu.2.trans h_b_le⟩
  · refine γ.cyclicShift_derivWithin_ne_zero_branch hτ h_cons ht h_cons_cd
      (fun u => u + τ - 1) (((hasDerivAt_id t).add_const τ).sub_const 1).hasDerivWithinAt
      (fun u hu => ?_) (fun _ hu => h_sub ⟨by linarith [hu.1], by linarith [hu.2]⟩)
    rw [h_eq_csf hu]
    exact cyclicShiftFun_eq_on_wrap γ.toPath.extend hτ hclosed
      ⟨h_a_ge.trans hu.1, hu.2.trans hb_Icc.2⟩

/-- **Step 3: Cyclic shift of a `ClosedPwC1Immersion`.** -/
noncomputable def cyclicShift (γ : ClosedPwC1Immersion x) {τ : ℝ}
    (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ClosedPwC1Immersion (γ.toPath.extend τ) where
  toClosedPwC1Curve := γ.toClosedPwC1Curve.cyclicShift hτ
  derivWithin_ne_zero_pieces := fun _ _ h_cons _ ht =>
    γ.cyclicShift_derivWithin_ne_zero_piece hτ h_cons ht

end ClosedPwC1Immersion

end
