/-
Copyright (c) 2025 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.NormedSpace.FunctionSeries
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib

/-!
# Continuity of series of functions

We prove some HasSumUniformlyOn versions of theorems from
`Mathlib.Analysis.NormedSpace.FunctionSeries`.

Alongside this we prove `derivWithin_tsum` which states that the derivative of a series of functions
is the sum of the derivatives, under suitable conditions.

-/

open Set Metric TopologicalSpace Function Filter

open scoped Topology NNReal

variable {α β F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {u : α → ℝ}

theorem HasSumUniformlyOn_of_bounded {f : α → β → F} (hu : Summable u) {s : Set β}
    (hfu : ∀ n x, x ∈ s → ‖f n x‖ ≤ u n) : HasSumUniformlyOn f (fun x => ∑' n, f n x) {s} :=  by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn, tendstoUniformlyOn_tsum hu hfu]

theorem HasSumUniformlyOn_of_cofinite_eventually {ι : Type*} {f : ι → β → F} {u : ι → ℝ}
    (hu : Summable u) {s : Set β} (hfu : ∀ᶠ n in cofinite, ∀ x ∈ s, ‖f n x‖ ≤ u n) :
    HasSumUniformlyOn f (fun x => ∑' n, f n x) {s} := by
  simp [hasSumUniformlyOn_iff_tendstoUniformlyOn,
    tendstoUniformlyOn_tsum_of_cofinite_eventually hu hfu]

lemma SummableLocallyUniformlyOn_of_locally_bounded [TopologicalSpace β] [LocallyCompactSpace β]
    (f : α → β → F) {s : Set β} (hs : IsOpen s)
    (hu : ∀ K ⊆ s, IsCompact K → ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖f n k‖ ≤ u n) :
    SummableLocallyUniformlyOn f s := by
  apply HasSumLocallyUniformlyOn.summableLocallyUniformlyOn (g := (fun x => ∑' i, f i x))
  rw [hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn,
    tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
  intro K hK hKc
  obtain ⟨u, hu1, hu2⟩ := hu K hK hKc
  apply tendstoUniformlyOn_tsum hu1 fun n x hx ↦ hu2 n ⟨x, hx⟩

/-- The `derivWithin` of a absolutely and uniformly converget sum on an open set `s` is the sum
of the derivatives of squence of functions on the open set `s` -/
theorem derivWithin_tsum {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] (f : α → E → F) {s : Set E}
    (hs : IsOpen s) {x : E} (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n ↦ f n y)
    (h : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r) :
    derivWithin (fun z ↦ ∑' n , f n z) s x = ∑' n, derivWithin (f n) s x := by
  apply HasDerivWithinAt.derivWithin ?_ (IsOpen.uniqueDiffWithinAt hs hx)
  apply HasDerivAt.hasDerivWithinAt
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ (fun y hy ↦ Summable.hasSum (hf y hy)) hx
  · use fun n : Finset α ↦ fun a ↦ ∑ i ∈ n, derivWithin (fun z ↦ f i z) s a
  · obtain ⟨g, hg⟩ := h
    apply (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hg).congr_right
    exact fun _ hb ↦ Eq.symm (HasSumLocallyUniformlyOn.tsum_eqOn hg hb)
  · filter_upwards with t r hr
    apply HasDerivAt.fun_sum
    intro q hq
    apply HasDerivWithinAt.hasDerivAt
    · exact DifferentiableWithinAt.hasDerivWithinAt (hf2 q r hr).differentiableWithinAt
    · exact IsOpen.mem_nhds hs hr


lemma tsum_eq_summable {ι α : Type*} [AddCommMonoid α] [ TopologicalSpace α]
    (g : ι → α) (h : ∑' n, g n ≠ 0) :
    Summable g := by
  by_contra hg
  rw [tsum_eq_zero_of_not_summable hg] at h
  aesop


variable {α β ι : Type*} [CommMonoid α] {f : ι → β → α} {g : β → α} {𝔖 : Set (Set β)}
  {x : β} {s : Set β} {I : Finset ι} [UniformSpace α] [TopologicalSpace β] [T2Space α] [DecidableEq ι]

@[to_additive]
lemma MultipliableLocallyUniformlyOn_congr (f f' : ι → β → α) (h : ∀ i,  s.EqOn (f i)  (f' i))
    (h2 : MultipliableLocallyUniformlyOn f s):
    MultipliableLocallyUniformlyOn f' s := by
  apply HasProdLocallyUniformlyOn.multipliableLocallyUniformlyOn
  have H := h2.hasProdLocallyUniformlyOn
  apply H.congr
  intro v
  induction' v using Finset.induction_on with i S hi hs
  simp
  intro t ht
  simp
  intro x hx
  simp
  have H := hs hx
  simp at *
  congr
  ext i
  exact h i hx


theorem iteratedDerivWithin_tsum {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] (f : ι → E → F) {s : Set E} (m : ℕ)
    (hs : IsOpen s) {x : E} (hx : x ∈ s)
    (h : ∀ k, SummableLocallyUniformlyOn (fun n ↦ (iteratedDerivWithin k (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, r ∈ s → DifferentiableAt E (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n , f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction' m with m hm generalizing x
  · simp
  · simp_rw [iteratedDerivWithin_succ]
    rw [← derivWithin_tsum _ hs hx]
    · apply derivWithin_congr (fun _ ht ↦ hm ht) (hm hx)
    · intro y hy
      apply ((h m).summable hy).congr
      intro b
      simp
    · apply SummableLocallyUniformlyOn_congr _ _ _ (h (m+1))
      intro i t ht
      rw [iteratedDerivWithin_succ]
    · intro n r hr
      exact hf2 n m _ hr

theorem iteratedDerivWithin_tsum2 {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] (f : ι → E → F) {s : Set E} (m : ℕ)
    (hs : IsOpen s) {x : E} (hx : x ∈ s)
    (h : SummableLocallyUniformlyOn (fun n ↦ (iteratedDerivWithin m (fun z ↦ f n z) s)) s)
    (hf2 : ∀ n k r, r ∈ s → DifferentiableAt E (iteratedDerivWithin k (fun z ↦ f n z) s) r) :
    iteratedDerivWithin m (fun z ↦ ∑' n , f n z) s x = ∑' n, iteratedDerivWithin m (f n) s x := by
  induction' m using Nat.case_strong_induction_on  with m hm generalizing x
  simp
  simp_rw [iteratedDerivWithin_succ]
  rw [← derivWithin_tsum _ hs hx]
  · apply derivWithin_congr
    intro t ht
    have HM := hm m ?_ ht
    sorry
    sorry


  sorry

lemma derivWithin_SummableUniformlyOn_eq {F E : Type*} [NontriviallyNormedField E] [IsRCLikeNormedField E]
    [NormedField F] [NormedSpace E F] {f g : α → E → F} {s : Set E}
    (hs : IsOpen s) (hf0 : ∀ y ∈ s, Summable fun n ↦ f n y)
    (hg0 :  ∀ y ∈ s, Summable fun n ↦ g n y)
    (hf : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ f n z) s)) s)
    (hg : SummableLocallyUniformlyOn (fun n ↦ (derivWithin (fun z ↦ g n z) s)) s)
    (hfg :s.EqOn (∑' n, f n) (∑' n, g n))
    (hf2 : ∀ n r, r ∈ s → DifferentiableAt E (f n) r)
    (hg2 : ∀ n r, r ∈ s → DifferentiableAt E (g n) r)  :
    s.EqOn (∑' n,  (derivWithin (f n) s))  (∑' n,  (derivWithin (g n) s)) := by
  intro z hz
  have := derivWithin_tsum f hs hz hf0 hf hf2
  rw [tsum_apply, ← this]
  have := derivWithin_tsum g hs hz hg0 hg hg2
  rw [tsum_apply, ← this]
  apply derivWithin_congr
  intro t ht
  have H := hfg ht
  simp
  rw [tsum_apply, tsum_apply] at H
  exact H
  all_goals {sorry}
