/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33MultiPole
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.ResidueLinearity

/-!
# Laurent polar part extraction from condition (B)

For HW Theorem 3.3 in tight (paper-style) form we extract a Laurent decomposition
`f = polarPart + holomorphicRemainder` at each pole. Condition (B)
(`SatisfiesConditionB.laurent_compatible`) already carries this data via `∃ N a g, ...`;
this file extracts it into named functions via `Classical.choose` (no new axioms beyond
`Classical.choice`) and proves the key compatibility lemmas.

## Main definitions

* `crossingParam γ s` — the unique parameter `t₀ ∈ (0,1)` with `γ(t₀) = s`.
* `laurentPolarPartAt hCondB s` — the local polar part `∑ k, a_k / (z - s)^(k+1)`.
* `laurentAnalyticPartAt hCondB s` — the analytic remainder `g_s` near `s`.
* `laurentHigherOrderPolar hCondB` / `laurentHolomorphicRemainder hCondB` — the global
  decomposition `f - principalPartSum = higherOrderPolar + holomorphicRemainder`.
-/

open Filter Topology Set Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-- Predicate: pole `s` is crossed by γ in the open interval. -/
def IsCrossed (γ : PwC1Immersion x x) (s : ℂ) : Prop :=
  ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s

/-- The crossing parameter `t₀ ∈ (0, 1)` with `γ(t₀) = s`, or `0` if no such `t₀` exists. -/
noncomputable def crossingParam (γ : PwC1Immersion x x) (s : ℂ) : ℝ :=
  open Classical in if h : IsCrossed γ s then Classical.choose h else 0

theorem crossingParam_mem_Ioo {γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) :
    crossingParam γ s ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [crossingParam, h, ↓reduceDIte]; exact (Classical.choose_spec h).1

theorem γ_at_crossingParam {γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) :
    (γ : ℝ → ℂ) (crossingParam γ s) = s := by
  simp only [crossingParam, h, ↓reduceDIte]; exact (Classical.choose_spec h).2

variable {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}

private theorem laurent_data_exists (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      (∀ᶠ z in 𝓝[≠] s, f z = g z +
        ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧
      (∀ k : Fin N, a k ≠ 0 → k.val ≥ 1 →
        ∃ m : ℤ, (↑k.val : ℝ) * angleAtCrossing γ (crossingParam γ s)
          (crossingParam_mem_Ioo h_cross) =
          ↑m * (2 * Real.pi)) := by
  exact hCondB.laurent_compatible s hs (crossingParam γ s)
    (Set.Ioo_subset_Icc_self (crossingParam_mem_Ioo h_cross))
    (γ_at_crossingParam h_cross) (crossingParam_mem_Ioo h_cross)

/-- Local polar part `∑ k ∈ Fin N, a_k / (z - s)^(k+1)` at pole `s`, with `N` and `a_k` from
condition (B)'s Laurent data at the crossing parameter. Zero for uncrossed `s`. -/
noncomputable def laurentPolarPartAt (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S)
    (z : ℂ) : ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    ∑ k : Fin (laurent_data_exists hCondB hs h).choose,
      (laurent_data_exists hCondB hs h).choose_spec.choose k /
        (z - s) ^ (k.val + 1)
  else 0

/-- The analytic remainder `g` from condition (B)'s Laurent data at a crossed pole `s ∈ S`,
so that `f z = g z + ∑ a_k / (z-s)^(k+1)` holds eventually near `s`. Zero for uncrossed `s`. -/
noncomputable def laurentAnalyticPartAt (hCondB : SatisfiesConditionB γ f S) (s : ℂ)
    (hs : s ∈ S) : ℂ → ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    (laurent_data_exists hCondB hs h).choose_spec.choose_spec.choose
  else 0

/-- The analytic part is `AnalyticAt ℂ` at `s` (for crossed `s`). -/
theorem laurentAnalyticPartAt_analyticAt (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    AnalyticAt ℂ (laurentAnalyticPartAt hCondB s hs) s := by
  unfold laurentAnalyticPartAt; rw [dif_pos h_cross]
  exact (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose_spec.1

private lemma laurentAnalyticPartAt_eq_data (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    laurentAnalyticPartAt hCondB s hs =
      (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose := by
  unfold laurentAnalyticPartAt; simp only [dif_pos h_cross]

private lemma laurentPolarPartAt_eq_data (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) (h_cross : IsCrossed γ s) (z : ℂ) :
    laurentPolarPartAt hCondB s hs z =
      ∑ k : Fin (laurent_data_exists hCondB hs h_cross).choose,
        (laurent_data_exists hCondB hs h_cross).choose_spec.choose k /
          (z - s) ^ (k.val + 1) := by
  unfold laurentPolarPartAt; simp only [dif_pos h_cross]

/-- Near a crossed pole `s`, `f =ᶠ[𝓝[≠] s] analyticPartAt s + polarPartAt s` — the core
consequence of condition (B)'s `laurent_compatible` field on our extracted parts. -/
theorem f_eq_analyticPart_plus_polarPart_eventually (hCondB : SatisfiesConditionB γ f S)
    {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    ∀ᶠ z in 𝓝[≠] s, f z =
      laurentAnalyticPartAt hCondB s hs z +
        laurentPolarPartAt hCondB s hs z := by
  filter_upwards [(laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose_spec.2.1]
    with z hz
  rw [hz, laurentPolarPartAt_eq_data hCondB hs h_cross z,
      ← congrArg (· z) (laurentAnalyticPartAt_eq_data hCondB hs h_cross)]

/-- `laurentPolarPartAt s` is differentiable at any point `z ≠ s`. -/
theorem laurentPolarPartAt_differentiableAt (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) {z : ℂ} (hz : z ≠ s) :
    DifferentiableAt ℂ (laurentPolarPartAt hCondB s hs) z := by
  unfold laurentPolarPartAt
  by_cases h : IsCrossed γ s
  · simp only [dif_pos h]
    refine DifferentiableAt.fun_sum fun k _ => ?_
    exact (differentiableAt_const _).div
      ((differentiableAt_id.sub (differentiableAt_const _)).pow _)
      (pow_ne_zero _ (sub_ne_zero.mpr hz))
  · simp only [dif_neg h]; exact differentiableAt_const _

/-- The per-pole higher-order polar part, guarded on `IsCrossed γ s`. At crossed poles, this
is `laurentPolarPartAt s - residue/(z-s)` (the Laurent terms `k ≥ 1` from condition (B), which
CPV-cancel under (B)); at uncrossed poles, it is `0`. -/
noncomputable def laurentHigherOrderPolarAt (hCondB : SatisfiesConditionB γ f S) (s : ℂ)
    (hs : s ∈ S) (z : ℂ) : ℂ :=
  open Classical in
  if IsCrossed γ s then
    laurentPolarPartAt hCondB s hs z - residue f s / (z - s)
  else 0

/-- The total higher-order polar part: sum over `s ∈ S` of the per-pole guarded parts. Only
crossed poles contribute. -/
noncomputable def laurentHigherOrderPolar (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, laurentHigherOrderPolarAt hCondB s.1 s.2 z

/-- The holomorphic remainder `f - principalPartSum - laurentHigherOrderPolar`. At crossed
`s`, this collapses to the analytic part `g_s` from condition (B)'s Laurent compatibility. At
uncrossed `s`, the higher-order terms `1/(z-s)^k` for `k ≥ 2` survive but are single-valued
along closed curves, so they don't affect the residue formula. -/
noncomputable def laurentHolomorphicRemainder (hCondB : SatisfiesConditionB γ f S) (z : ℂ) :
    ℂ :=
  f z - principalPartSum S (fun s => residue f s) z -
    laurentHigherOrderPolar hCondB z

/-- `f - principalPartSum = laurentHigherOrderPolar + laurentHolomorphicRemainder`. Holds by
construction. -/
theorem f_minus_pp_eq_higherOrder_plus_holo (hCondB : SatisfiesConditionB γ f S) (z : ℂ) :
    f z - principalPartSum S (fun s => residue f s) z =
      laurentHigherOrderPolar hCondB z +
        laurentHolomorphicRemainder hCondB z := by
  simp only [laurentHolomorphicRemainder]; ring

/-- `laurentHigherOrderPolarAt s` is differentiable at any point `z ≠ s`. -/
theorem laurentHigherOrderPolarAt_differentiableAt (hCondB : SatisfiesConditionB γ f S) {s : ℂ}
    (hs : s ∈ S) {z : ℂ} (hz : z ≠ s) :
    DifferentiableAt ℂ (laurentHigherOrderPolarAt hCondB s hs) z := by
  unfold laurentHigherOrderPolarAt
  by_cases h : IsCrossed γ s
  · simp only [if_pos h]
    exact (laurentPolarPartAt_differentiableAt hCondB hs hz).fun_sub
      ((differentiableAt_const _).div
        (differentiableAt_id.sub (differentiableAt_const _)) (sub_ne_zero.mpr hz))
  · simp only [if_neg h]; exact differentiableAt_const _

/-- `laurentHigherOrderPolar` is differentiable at any point `z ∉ S`. -/
theorem laurentHigherOrderPolar_differentiableAt (hCondB : SatisfiesConditionB γ f S) {z : ℂ}
    (hz : z ∉ (↑S : Set ℂ)) :
    DifferentiableAt ℂ (laurentHigherOrderPolar hCondB) z := by
  refine DifferentiableAt.fun_sum fun s _ =>
    laurentHigherOrderPolarAt_differentiableAt hCondB s.2 ?_
  exact fun h_eq => hz (h_eq ▸ Finset.mem_coe.mpr s.2)

/-- `laurentHolomorphicRemainder` is differentiable on `U \ S`. -/
theorem laurentHolomorphicRemainder_differentiableOn (hCondB : SatisfiesConditionB γ f S)
    {U : Set ℂ} (hU : IsOpen U) (hf : DifferentiableOn ℂ f (U \ ↑S)) :
    DifferentiableOn ℂ (laurentHolomorphicRemainder hCondB) (U \ ↑S) := by
  intro z hz
  have hf_at : DifferentiableAt ℂ f z :=
    (hf z hz).differentiableAt ((hU.sdiff S.finite_toSet.isClosed).mem_nhds hz)
  exact ((hf_at.sub (_root_.principalPartSum_differentiableAt (hz := hz.2))).sub
    (laurentHigherOrderPolar_differentiableAt hCondB hz.2)).differentiableWithinAt

private theorem laurentHigherOrderPolarAt_analyticAt_of_ne
    (hCondB : SatisfiesConditionB γ f S) {s t : ℂ} (ht : t ∈ S) (h_ne : t ≠ s) :
    AnalyticAt ℂ (laurentHigherOrderPolarAt hCondB t ht) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_compl_singleton.mem_nhds (mem_compl_singleton_iff.mpr h_ne.symm)]
    with z hz
  exact laurentHigherOrderPolarAt_differentiableAt hCondB ht (mem_compl_singleton_iff.mp hz)

private noncomputable def laurentHigherOrderPolar_rest (hCondB : SatisfiesConditionB γ f S)
    (s : ℂ) (_hs : s ∈ S) (z : ℂ) : ℂ :=
  ∑ t ∈ S.attach.filter (fun t => t.1 ≠ s),
    laurentHigherOrderPolarAt hCondB t.1 t.2 z

private theorem laurentHigherOrderPolar_rest_analyticAt (hCondB : SatisfiesConditionB γ f S)
    {s : ℂ} (hs : s ∈ S) :
    AnalyticAt ℂ (laurentHigherOrderPolar_rest hCondB s hs) s :=
  Finset.analyticAt_fun_sum _ fun t ht =>
    laurentHigherOrderPolarAt_analyticAt_of_ne hCondB t.2 (Finset.mem_filter.mp ht).2

private theorem laurentHigherOrderPolar_eq_term_add_rest (hCondB : SatisfiesConditionB γ f S)
    {s : ℂ} (hs : s ∈ S) (z : ℂ) :
    laurentHigherOrderPolar hCondB z =
      laurentHigherOrderPolarAt hCondB s hs z +
        laurentHigherOrderPolar_rest hCondB s hs z := by
  unfold laurentHigherOrderPolar laurentHigherOrderPolar_rest
  rw [← Finset.sum_filter_add_sum_filter_not S.attach (·.1 = s),
      show S.attach.filter (·.1 = s) = {⟨s, hs⟩} by ext t; simp [Subtype.ext_iff],
      Finset.sum_singleton]

private theorem principalPartSum_rest_analyticAt_at_s {c : ℂ → ℂ} {s : ℂ} (_hs : s ∈ S) :
    AnalyticAt ℂ (fun z => ∑ t ∈ S.erase s, c t / (z - t)) s :=
  Finset.analyticAt_fun_sum _ fun _ ht => analyticAt_const.div
    (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr (Finset.ne_of_mem_erase ht).symm)

/-- `laurentHolomorphicRemainder` is eventually equal (in the punctured neighborhood of each
`s ∈ S`) to a function that is analytic at `s`. Together with the off-`S` differentiability
from `laurentHolomorphicRemainder_differentiableOn`, this feeds a Riemann-removable-singularity
argument that builds a global analytic extension on `U`. -/
theorem laurentHolomorphicRemainder_eventuallyEq_analyticAt
    (hCondB : SatisfiesConditionB γ f S) (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    {s : ℂ} (hs : s ∈ S) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s ∧
      (laurentHolomorphicRemainder hCondB) =ᶠ[𝓝[≠] s] g := by
  classical
  set h_pole := hSimple s hs
  set rest_pp : ℂ → ℂ := fun z => ∑ t ∈ S.erase s, residue f t / (z - t)
  have rest_pp_an : AnalyticAt ℂ rest_pp s := principalPartSum_rest_analyticAt_at_s hs
  have pp_decomp : ∀ z, principalPartSum S (fun s => residue f s) z =
      residue f s / (z - s) + rest_pp z :=
    principalPartSum_eq_term_add_rest hs _
  set rest_holo : ℂ → ℂ := laurentHigherOrderPolar_rest hCondB s hs
  have rest_holo_an : AnalyticAt ℂ rest_holo s :=
    laurentHigherOrderPolar_rest_analyticAt hCondB hs
  have holo_decomp : ∀ z, laurentHigherOrderPolar hCondB z =
      laurentHigherOrderPolarAt hCondB s hs z + rest_holo z :=
    laurentHigherOrderPolar_eq_term_add_rest hCondB hs
  by_cases h_cross : IsCrossed γ s
  · set g : ℂ → ℂ :=
      fun z => laurentAnalyticPartAt hCondB s hs z - rest_pp z - rest_holo z with g_def
    refine ⟨g, ((laurentAnalyticPartAt_analyticAt hCondB hs h_cross).sub rest_pp_an).sub
      rest_holo_an, ?_⟩
    filter_upwards [h_pole.eventually_eq,
      f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross] with z hz_pole hz_laurent
    have h_higher_eq : laurentHigherOrderPolarAt hCondB s hs z =
        laurentPolarPartAt hCondB s hs z - residue f s / (z - s) := by
      unfold laurentHigherOrderPolarAt; rw [if_pos h_cross]
    simp only [laurentHolomorphicRemainder, pp_decomp z, holo_decomp z, h_higher_eq,
      hz_laurent, g_def]
    ring
  · have h_term_zero : ∀ z, laurentHigherOrderPolarAt hCondB s hs z = 0 := fun z => by
      unfold laurentHigherOrderPolarAt; rw [if_neg h_cross]
    set g : ℂ → ℂ := fun z => h_pole.regularPart z - rest_pp z - rest_holo z with g_def
    refine ⟨g, (h_pole.regularPart_analyticAt.sub rest_pp_an).sub rest_holo_an, ?_⟩
    have h_coeff_eq : h_pole.coeff = residue f s := (residue_eq_coeff h_pole).symm
    filter_upwards [h_pole.eventually_eq] with z hz_pole
    simp only [laurentHolomorphicRemainder, pp_decomp z, holo_decomp z, h_term_zero z,
      hz_pole, g_def, h_coeff_eq, zero_add]
    ring

/-- Under the simple-pole hypothesis on `f` at every `s ∈ S`, the holomorphic remainder
`laurentHolomorphicRemainder` has zero residue at every `s ∈ S`. -/
theorem laurentHolomorphicRemainder_residue_zero (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s) {s : ℂ} (hs : s ∈ S) :
    residue (laurentHolomorphicRemainder hCondB) s = 0 := by
  obtain ⟨g, g_an, h_evEq⟩ :=
    laurentHolomorphicRemainder_eventuallyEq_analyticAt hCondB hSimple hs
  rw [residue_congr h_evEq]; exact residue_eq_zero_of_analyticAt g_an

end LeanModularForms

end
