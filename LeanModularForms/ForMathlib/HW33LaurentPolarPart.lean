/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33SectorEven
import LeanModularForms.ForMathlib.HW33MultiPole
import LeanModularForms.ForMathlib.FlatnessConditions
import LeanModularForms.ForMathlib.ResidueLinearity

/-!
# Laurent polar part extraction from condition (B)

For HW Theorem 3.3 in tight (paper-style) form, we need to extract a Laurent
decomposition `f = polarPart + holomorphicRemainder` at each pole. Condition
(B) (`SatisfiesConditionB.laurent_compatible`) already carries this data via
`∃ N a g, ...`. This file extracts that data into named functions and proves
the key compatibility lemmas.

## Main definitions

* `crossingParam γ S s` — the unique parameter `t₀ ∈ (0,1)` with `γ(t₀) = s`,
  via `Classical.choose` from the uniqueness assumption.

* `laurentPolarOrderAt γ f S hCondB s hs` — the pole order `N s : ℕ` extracted
  from `hCondB.laurent_compatible` at the crossing of pole `s`.

* `laurentPolarCoeffAt γ f S hCondB s hs k` — the coefficient `a_k` for
  `k = 0, ..., N - 1` (so the Laurent term is `a_k / (z - s)^(k+1)`).

* `laurentPolarPartAt γ f S hCondB s` — the local polar part
  `∑ k ∈ Fin N, a_k / (z - s)^(k+1)` at pole `s`.

## Strategy

We use `Classical.choose` to extract data from `hCondB.laurent_compatible`.
This adds no axioms beyond the existing `Classical.choice`.
-/

open Filter Topology Set Complex MeasureTheory

noncomputable section

namespace LeanModularForms

variable {x : ℂ}

/-! ## Crossing parameter extraction -/

/-- Predicate: pole `s` is crossed by γ in the open interval. -/
def IsCrossed (γ : PwC1Immersion x x) (s : ℂ) : Prop :=
  ∃ t₀ ∈ Set.Ioo (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s

/-- Selector for the crossing parameter `t₀` of pole `s`. Under the uniqueness
hypothesis, this is the unique `t₀ ∈ (0, 1)` with `γ(t₀) = s` if any exists,
or `0` (default) otherwise. -/
noncomputable def crossingParam (γ : PwC1Immersion x x) (s : ℂ) : ℝ :=
  open Classical in if h : IsCrossed γ s then Classical.choose h else 0

theorem crossingParam_mem_Ioo {γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) :
    crossingParam γ s ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [crossingParam, h, ↓reduceDIte]
  exact (Classical.choose_spec h).1

theorem γ_at_crossingParam {γ : PwC1Immersion x x} {s : ℂ} (h : IsCrossed γ s) :
    (γ : ℝ → ℂ) (crossingParam γ s) = s := by
  simp only [crossingParam, h, ↓reduceDIte]
  exact (Classical.choose_spec h).2

/-! ## Laurent decomposition extraction from condition (B) -/

/-- Helper: when `s ∈ S`, `γ` crosses `s`, and `hCondB.laurent_compatible`
holds, extract the existential at `s`. Returns the existential statement
to be unpacked by `Classical.choose`. -/
private theorem laurent_data_exists {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      (∀ᶠ z in 𝓝[≠] s, f z = g z +
        ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧
      (∀ k : Fin N, a k ≠ 0 → k.val ≥ 1 →
        ∃ m : ℤ, (↑k.val : ℝ) * angleAtCrossing γ (crossingParam γ s)
          (crossingParam_mem_Ioo h_cross) =
          ↑m * (2 * Real.pi)) := by
  have ht_mem : crossingParam γ s ∈ Set.Icc (0 : ℝ) 1 :=
    Set.Ioo_subset_Icc_self (crossingParam_mem_Ioo h_cross)
  exact hCondB.laurent_compatible s hs (crossingParam γ s) ht_mem
    (γ_at_crossingParam h_cross) (crossingParam_mem_Ioo h_cross)

/-- Local polar part at pole `s`: `∑ k ∈ Fin N, a_k / (z - s)^(k+1)`, where
`N` and `a_k` come from condition (B)'s Laurent compatibility data at the
crossing parameter. Zero for uncrossed `s`.

The single `if-then-else` (rather than separate `laurentPolarOrderAt` /
`laurentPolarCoeffAt` definitions) avoids dependent-type clashes when
unfolding: the `Fin` index, the coefficients, and the sum all live inside
the same conditional, so `dif_pos` reduces the whole expression cleanly. -/
noncomputable def laurentPolarPartAt {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) (z : ℂ) : ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    ∑ k : Fin (laurent_data_exists hCondB hs h).choose,
      (laurent_data_exists hCondB hs h).choose_spec.choose k /
        (z - s) ^ (k.val + 1)
  else 0

/-- Total polar part: sum over all poles in `S`. -/
noncomputable def laurentPolarPartTotal {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, laurentPolarPartAt hCondB s.1 s.2 z

/-! ## Analytic part of the Laurent decomposition

The analytic remainder `g` from condition (B)'s `laurent_compatible` data is
the holomorphic part of the local decomposition `f = g + ∑ aₖ / (z-s)^(k+1)`
near a crossed pole `s ∈ S`. Extracting this `g` as a separate function
provides the building block for proving global analyticity of
`laurentHolomorphicRemainder` (TIGHT-4). -/

/-- The analytic remainder `g` from condition (B)'s Laurent compatibility data
at a crossed pole `s ∈ S`. By definition, `f z = g z + ∑ a_k / (z-s)^(k+1)`
holds eventually near `s`. For uncrossed `s`, this is the zero function. -/
noncomputable def laurentAnalyticPartAt {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) : ℂ → ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    (laurent_data_exists hCondB hs h).choose_spec.choose_spec.choose
  else 0

/-- The analytic part is `AnalyticAt ℂ` at `s` (for crossed `s`). -/
theorem laurentAnalyticPartAt_analyticAt {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    AnalyticAt ℂ (laurentAnalyticPartAt hCondB s hs) s := by
  classical
  unfold laurentAnalyticPartAt
  rw [dif_pos h_cross]
  exact (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose_spec.1

/-- Helper: `laurentAnalyticPartAt` unfolds to the data-defined `g`. -/
private lemma laurentAnalyticPartAt_eq_data {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) :
    laurentAnalyticPartAt hCondB s hs =
      (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose := by
  classical
  unfold laurentAnalyticPartAt
  simp only [dif_pos h_cross]

/-- Helper: `laurentPolarPartAt` unfolds to the data-defined sum (for crossed `s`). -/
private lemma laurentPolarPartAt_eq_data {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s)
    (z : ℂ) :
    laurentPolarPartAt hCondB s hs z =
      ∑ k : Fin (laurent_data_exists hCondB hs h_cross).choose,
        (laurent_data_exists hCondB hs h_cross).choose_spec.choose k /
          (z - s) ^ (k.val + 1) := by
  classical
  unfold laurentPolarPartAt
  simp only [dif_pos h_cross]

/-- **Local Laurent decomposition**: near a crossed pole `s`, `f` decomposes
as `analyticPartAt s + polarPartAt s` (eventually equal in the punctured
neighborhood). This is the core consequence of condition (B)'s
`laurent_compatible` field, repackaged as a working theorem on our extracted
`laurentAnalyticPartAt` and `laurentPolarPartAt`. -/
theorem f_eq_analyticPart_plus_polarPart_eventually {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    ∀ᶠ z in 𝓝[≠] s, f z =
      laurentAnalyticPartAt hCondB s hs z +
        laurentPolarPartAt hCondB s hs z := by
  have h_data :=
    (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose_spec.2.1
  filter_upwards [h_data] with z hz
  rw [hz, laurentPolarPartAt_eq_data hCondB hs h_cross z]
  congr 1
  exact congrArg (· z) (laurentAnalyticPartAt_eq_data hCondB hs h_cross).symm

/-- **Corollary**: `f - laurentPolarPartAt s = laurentAnalyticPartAt s`
eventually in the punctured neighborhood of a crossed pole `s`. -/
theorem f_minus_polarPartAt_eventuallyEq_analyticPartAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    (fun z => f z - laurentPolarPartAt hCondB s hs z) =ᶠ[𝓝[≠] s]
      laurentAnalyticPartAt hCondB s hs := by
  filter_upwards [f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross]
    with z hz
  rw [hz]
  ring

/-- `laurentPolarPartAt s` is differentiable at any point `z ≠ s`. The terms
`a_k / (z - s)^(k+1)` are differentiable when `z ≠ s`, and a finite sum of
differentiable functions is differentiable. -/
theorem laurentPolarPartAt_differentiableAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) {z : ℂ}
    (hz : z ≠ s) :
    DifferentiableAt ℂ (laurentPolarPartAt hCondB s hs) z := by
  classical
  unfold laurentPolarPartAt
  by_cases h : IsCrossed γ s
  · simp only [dif_pos h]
    apply DifferentiableAt.fun_sum
    intro k _
    have h_pow_ne : (z - s) ^ (k.val + 1) ≠ 0 :=
      pow_ne_zero _ (sub_ne_zero.mpr hz)
    exact ((differentiableAt_const _).div
      ((differentiableAt_id.sub (differentiableAt_const _)).pow _) h_pow_ne)
  · simp only [dif_neg h]
    exact differentiableAt_const _

/-! ## Decomposition relative to simple-pole `principalPartSum`

**Crossed-vs-uncrossed split.** The decomposition
`f - principalPartSum = laurentHigherOrderPolar + laurentHolomorphicRemainder`
must work uniformly whether or not `γ` crosses each `s ∈ S`. We achieve this by
defining the higher-order polar part *per pole* with a guard:

* **Crossed `s`**: `laurentHigherOrderPolarAt s z = laurentPolarPartAt s z -
  residue f s / (z - s)` — the Laurent terms `aₖ / (z-s)^(k+1)` for `k ≥ 1`,
  which (B)'s angle-compatibility cancels under CPV.
* **Uncrossed `s`**: `laurentHigherOrderPolarAt s z = 0`. Higher-order Laurent
  terms `1/(z-s)^k` for `k ≥ 2` integrate to zero along *any* closed curve
  (the antiderivative `-1/((k-1)(z-s)^{k-1})` is single-valued), so they need
  no separate cancellation; they live in `laurentHolomorphicRemainder` and
  vanish via the path-of-residues structure.

With this split, both `h_polar_cancel` and `h_holo_cancel` are individually
zero under just `hCondB` + null-homology, with no "all crossed" assumption. -/

/-- The per-pole higher-order polar part, guarded on `IsCrossed γ s`.
At crossed poles, this is `laurentPolarPartAt s - residue/(z-s)` — the Laurent
terms `k ≥ 1` from condition (B), which CPV-cancel under (B). At uncrossed
poles, this is `0` — there's no on-curve singularity to cancel. -/
noncomputable def laurentHigherOrderPolarAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) (z : ℂ) : ℂ :=
  open Classical in
  if IsCrossed γ s then
    laurentPolarPartAt hCondB s hs z - residue f s / (z - s)
  else 0

/-- The total higher-order polar part: sum over `s ∈ S` of the per-pole
guarded higher-order parts. Only crossed poles contribute. -/
noncomputable def laurentHigherOrderPolar {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, laurentHigherOrderPolarAt hCondB s.1 s.2 z

/-- The **holomorphic remainder** in the refactored decomposition:
`f - principalPartSum - laurentHigherOrderPolar`.

Per-pole contributions:
* **At crossed `s`**: `f - residue/(z-s) - (polarPartAt - residue/(z-s)) =
  f - polarPartAt`, which is the analytic part `g_s` from condition (B)'s
  Laurent compatibility — analytic at `s`.
* **At uncrossed `s`**: `f - residue/(z-s) - 0`, which has the higher-order
  Laurent terms `1/(z-s)^k` for `k ≥ 2`. These are *not* analytic at `s`,
  but they integrate to zero along any closed curve (single-valued
  antiderivative), so they don't affect the residue formula. -/
noncomputable def laurentHolomorphicRemainder {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  f z - principalPartSum S (fun s => residue f s) z -
    laurentHigherOrderPolar hCondB z

/-- **Decomposition for `hCancel` discharge**:
`f - principalPartSum = laurentHigherOrderPolar + laurentHolomorphicRemainder`.

Holds by construction (the new `laurentHolomorphicRemainder` is defined as the
remainder after subtracting `principalPartSum + laurentHigherOrderPolar`). -/
theorem f_minus_pp_eq_higherOrder_plus_holo {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) (z : ℂ) :
    f z - principalPartSum S (fun s => residue f s) z =
      laurentHigherOrderPolar hCondB z +
        laurentHolomorphicRemainder hCondB z := by
  simp only [laurentHolomorphicRemainder]
  ring

/-! ## Differentiability of the decomposition pieces -/

/-- `laurentHigherOrderPolarAt s` is differentiable at any point `z ≠ s`. -/
theorem laurentHigherOrderPolarAt_differentiableAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) {z : ℂ}
    (hz : z ≠ s) :
    DifferentiableAt ℂ (laurentHigherOrderPolarAt hCondB s hs) z := by
  classical
  unfold laurentHigherOrderPolarAt
  by_cases h : IsCrossed γ s
  · simp only [if_pos h]
    refine (laurentPolarPartAt_differentiableAt hCondB hs hz).fun_sub ?_
    have h_sub_ne : z - s ≠ 0 := sub_ne_zero.mpr hz
    exact ((differentiableAt_const _).div
      (differentiableAt_id.sub (differentiableAt_const _)) h_sub_ne)
  · simp only [if_neg h]
    exact differentiableAt_const _

/-- `laurentHigherOrderPolar` is differentiable at any point `z ∉ S`. -/
theorem laurentHigherOrderPolar_differentiableAt {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {z : ℂ} (hz : z ∉ (↑S : Set ℂ)) :
    DifferentiableAt ℂ (laurentHigherOrderPolar hCondB) z := by
  unfold laurentHigherOrderPolar
  apply DifferentiableAt.fun_sum
  intro s _
  refine laurentHigherOrderPolarAt_differentiableAt hCondB s.2 ?_
  intro h_eq
  exact hz (h_eq ▸ Finset.mem_coe.mpr s.2)

/-- `principalPartSum S c` is differentiable at any point `z ∉ S`. -/
theorem principalPartSum_differentiableAt (S : Finset ℂ) (c : ℂ → ℂ) {z : ℂ}
    (hz : z ∉ (↑S : Set ℂ)) :
    DifferentiableAt ℂ (principalPartSum S c) z := by
  unfold principalPartSum
  apply DifferentiableAt.fun_sum
  intro s hs
  have h_sub_ne : z - s ≠ 0 := sub_ne_zero.mpr (fun h_eq =>
    hz (h_eq ▸ Finset.mem_coe.mpr hs))
  exact (differentiableAt_const _).div
    (differentiableAt_id.sub (differentiableAt_const _)) h_sub_ne

/-- `laurentHolomorphicRemainder` is differentiable on `U \ S`. -/
theorem laurentHolomorphicRemainder_differentiableOn {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S) {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f (U \ ↑S)) :
    DifferentiableOn ℂ (laurentHolomorphicRemainder hCondB) (U \ ↑S) := by
  intro z hz
  have hU_open_diff : IsOpen (U \ ↑S) :=
    hU.sdiff (Set.Finite.isClosed (Set.toFinite (↑S : Set ℂ)))
  have hf_at : DifferentiableAt ℂ f z :=
    (hf z hz).differentiableAt (hU_open_diff.mem_nhds hz)
  unfold laurentHolomorphicRemainder
  exact ((hf_at.sub (principalPartSum_differentiableAt S _ hz.2)).sub
    (laurentHigherOrderPolar_differentiableAt hCondB hz.2)).differentiableWithinAt

/-! ## Phase 3.3: residue of `laurentHolomorphicRemainder` at each `s ∈ S` is zero

The decomposition `f = principalPartSum + laurentHigherOrderPolar + laurentHolomorphicRemainder`
is designed so that the holomorphic remainder has zero residue at every pole `s ∈ S`. This is
the key fact for TIGHT-4 (holo cancel): once we know the remainder integrates to zero along the
curve, the residue formula reduces purely to the `principalPartSum` contribution.

The proof routes through `residue_congr` to identify `laurentHolomorphicRemainder` near `s`
with an explicit analytic function. -/

/-- At a crossed pole `s ∈ S` and under the simple-pole hypothesis on `f` at `s`, the
higher-order polar term `laurentHigherOrderPolarAt s` is eventually equal (in the punctured
neighborhood of `s`) to the analytic difference `regularPart(f) - analyticPart(f)`. -/
private theorem laurentHigherOrderPolarAt_eventuallyEq_analytic_of_crossed
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) (h_pole : HasSimplePoleAt f s) :
    (fun z => laurentHigherOrderPolarAt hCondB s hs z) =ᶠ[𝓝[≠] s]
      (fun z => h_pole.regularPart z - laurentAnalyticPartAt hCondB s hs z) := by
  classical
  have h_pole_eq := h_pole.eventually_eq
  have h_coeff_eq : h_pole.coeff = residue f s := (residue_eq_coeff h_pole).symm
  have h_laurent_eq := f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross
  filter_upwards [h_pole_eq, h_laurent_eq] with z hpole hlaurent
  -- From `hpole`: f z = coeff/(z-s) + regularPart z
  -- From `hlaurent`: f z = analyticPart z + polarPartAt z
  -- Hence: polarPartAt z - coeff/(z-s) = regularPart z - analyticPart z.
  -- And `laurentHigherOrderPolarAt s = polarPartAt - residue f s/(z-s)` (crossed).
  have h_higher_eq : laurentHigherOrderPolarAt hCondB s hs z =
      laurentPolarPartAt hCondB s hs z - residue f s / (z - s) := by
    unfold laurentHigherOrderPolarAt
    rw [if_pos h_cross]
  rw [h_higher_eq, ← h_coeff_eq]
  -- coeff/(z-s) + regularPart = analyticPart + polarPartAt ⟹ polarPart - coeff/(z-s) = regular - analytic
  linear_combination hpole - hlaurent

/-- At any pole `t ≠ s` (both in `S`), the per-pole higher-order polar contribution
`laurentHigherOrderPolarAt t` is analytic at `s` (it is differentiable at `s` because
its only singularity is at `t ≠ s`). -/
private theorem laurentHigherOrderPolarAt_analyticAt_of_ne
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s t : ℂ} (ht : t ∈ S) (h_ne : t ≠ s) :
    AnalyticAt ℂ (laurentHigherOrderPolarAt hCondB t ht) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have h_open : IsOpen ({t}ᶜ : Set ℂ) := isOpen_compl_singleton
  have h_mem : s ∈ ({t}ᶜ : Set ℂ) := mem_compl_singleton_iff.mpr h_ne.symm
  filter_upwards [h_open.mem_nhds h_mem] with z hz
  exact laurentHigherOrderPolarAt_differentiableAt hCondB ht (mem_compl_singleton_iff.mp hz)

/-- The "rest" of `laurentHigherOrderPolar` excluding the `s`-term — a finite sum over
`t ∈ S \ {s}` of analytic-at-`s` contributions. -/
private noncomputable def laurentHigherOrderPolar_rest
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (_hs : s ∈ S) (z : ℂ) : ℂ :=
  ∑ t ∈ S.attach.filter (fun t => t.1 ≠ s),
    laurentHigherOrderPolarAt hCondB t.1 t.2 z

/-- The "rest" sum is analytic at `s` — it is a finite sum of differentiable-at-`s` terms. -/
private theorem laurentHigherOrderPolar_rest_analyticAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) :
    AnalyticAt ℂ (laurentHigherOrderPolar_rest hCondB s hs) s := by
  classical
  unfold laurentHigherOrderPolar_rest
  apply Finset.analyticAt_fun_sum
  intro t ht
  have h_ne : t.1 ≠ s := (Finset.mem_filter.mp ht).2
  exact laurentHigherOrderPolarAt_analyticAt_of_ne hCondB t.2 h_ne

/-- Decomposition of `laurentHigherOrderPolar` at a pole `s ∈ S`:
the `s`-term plus the rest sum. -/
private theorem laurentHigherOrderPolar_eq_term_add_rest
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S) (z : ℂ) :
    laurentHigherOrderPolar hCondB z =
      laurentHigherOrderPolarAt hCondB s hs z +
        laurentHigherOrderPolar_rest hCondB s hs z := by
  classical
  unfold laurentHigherOrderPolar laurentHigherOrderPolar_rest
  have h_mem : (⟨s, hs⟩ : {x // x ∈ S}) ∈ S.attach := Finset.mem_attach _ _
  rw [← Finset.sum_filter_add_sum_filter_not S.attach (fun t => t.1 = s)
        (fun t => laurentHigherOrderPolarAt hCondB t.1 t.2 z)]
  -- The "= s" filter sums to a single element (s, hs)
  have h_eq_singleton :
      S.attach.filter (fun t : {x // x ∈ S} => t.1 = s) = {⟨s, hs⟩} := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_attach, true_and, Finset.mem_singleton]
    exact ⟨fun h => Subtype.ext h, fun h => h ▸ rfl⟩
  rw [h_eq_singleton, Finset.sum_singleton]

/-- The `principalPartSum`-rest excluding the `s`-term is analytic at `s`. This is the
standard sum-of-other-terms analytic lemma, exposed for `principalPartSum`'s decomp. -/
private theorem principalPartSum_rest_analyticAt_at_s
    {S : Finset ℂ} {c : ℂ → ℂ} {s : ℂ} (_hs : s ∈ S) :
    AnalyticAt ℂ (fun z => ∑ t ∈ S.erase s, c t / (z - t)) s := by
  apply Finset.analyticAt_fun_sum
  intro t ht
  have hts : t ≠ s := Finset.ne_of_mem_erase ht
  exact analyticAt_const.div (analyticAt_id.sub analyticAt_const)
    (sub_ne_zero.mpr hts.symm)

/-- **Phase 3.3 main theorem**: `laurentHolomorphicRemainder` has zero residue at every
pole `s ∈ S`, under the assumption that `f` has a simple pole at every `s ∈ S`.

**Proof structure**.

We identify `laurentHolomorphicRemainder` near `s` (in a punctured neighborhood) with an
explicit *analytic function* and apply `residue_congr` + `residue_eq_zero_of_analyticAt`.

* **Crossed `s`**: Condition (B) gives `f =ᶠ analyticPart + polarPartAt`. Together with
  `HasSimplePoleAt f s` (giving `f =ᶠ residue f s/(z-s) + regularPart`), one obtains
  `polarPartAt - residue f s/(z-s) =ᶠ regularPart - analyticPart`. Thus
  `laurentHigherOrderPolarAt s =ᶠ regularPart - analyticPart`, and the whole remainder
  becomes `regularPart - rest_pp - rest_holo - (regularPart - analyticPart) =
  analyticPart - rest_pp - rest_holo`, an analytic combination.

* **Uncrossed `s`**: `laurentHigherOrderPolarAt s = 0`. From `HasSimplePoleAt`,
  `f =ᶠ residue f s/(z-s) + regularPart`, so the remainder reduces to
  `regularPart - rest_pp - rest_holo`, which is analytic at `s`.

In both cases the local form is analytic, so the residue is zero. -/
theorem laurentHolomorphicRemainder_residue_zero {γ : PwC1Immersion x x} {f : ℂ → ℂ}
    {S : Finset ℂ} (hCondB : SatisfiesConditionB γ f S)
    (hSimple : ∀ s ∈ S, HasSimplePoleAt f s)
    {s : ℂ} (hs : s ∈ S) :
    residue (laurentHolomorphicRemainder hCondB) s = 0 := by
  classical
  set h_pole := hSimple s hs with h_pole_def
  -- Decompose principalPartSum as `c s/(z-s) + rest_pp`.
  set rest_pp : ℂ → ℂ := fun z => ∑ t ∈ S.erase s, residue f t / (z - t) with rest_pp_def
  have rest_pp_an : AnalyticAt ℂ rest_pp s := principalPartSum_rest_analyticAt_at_s hs
  have pp_decomp : ∀ z, principalPartSum S (fun s => residue f s) z =
      residue f s / (z - s) + rest_pp z :=
    fun z => principalPartSum_eq_term_add_rest hs (fun s => residue f s) z
  -- Decompose laurentHigherOrderPolar as `term + rest_holo`.
  set rest_holo : ℂ → ℂ := laurentHigherOrderPolar_rest hCondB s hs with rest_holo_def
  have rest_holo_an : AnalyticAt ℂ rest_holo s :=
    laurentHigherOrderPolar_rest_analyticAt hCondB hs
  have holo_decomp : ∀ z, laurentHigherOrderPolar hCondB z =
      laurentHigherOrderPolarAt hCondB s hs z + rest_holo z :=
    fun z => laurentHigherOrderPolar_eq_term_add_rest hCondB hs z
  -- Build the candidate analytic function. We'll case on crossed vs uncrossed.
  by_cases h_cross : IsCrossed γ s
  · -- Crossed case: laurentHigherOrderPolarAt s = polarPartAt - residue f s/(z-s).
    -- And f =ᶠ analyticPart + polarPartAt.
    -- Local form: `analyticPart - rest_pp - rest_holo`, analytic at `s`.
    set g : ℂ → ℂ :=
      fun z => laurentAnalyticPartAt hCondB s hs z - rest_pp z - rest_holo z with g_def
    have g_an : AnalyticAt ℂ g s := by
      have h_analyticPart_an := laurentAnalyticPartAt_analyticAt hCondB hs h_cross
      exact (h_analyticPart_an.sub rest_pp_an).sub rest_holo_an
    have h_evEq : (laurentHolomorphicRemainder hCondB) =ᶠ[𝓝[≠] s] g := by
      have h_pole_eq := h_pole.eventually_eq
      have h_coeff_eq : h_pole.coeff = residue f s := (residue_eq_coeff h_pole).symm
      have h_laurent := f_eq_analyticPart_plus_polarPart_eventually hCondB hs h_cross
      filter_upwards [h_pole_eq, h_laurent] with z hz_pole hz_laurent
      -- laurentHigherOrderPolarAt s = polarPartAt - residue f s/(z-s) (crossed case).
      have h_higher_eq : laurentHigherOrderPolarAt hCondB s hs z =
          laurentPolarPartAt hCondB s hs z - residue f s / (z - s) := by
        unfold laurentHigherOrderPolarAt
        rw [if_pos h_cross]
      simp only [laurentHolomorphicRemainder, pp_decomp z, holo_decomp z, h_higher_eq,
        hz_laurent, g_def]
      -- Now: (analyticPart + polarPart) - (c/(z-s) + rest_pp)
      --      - ((polarPart - c/(z-s)) + rest_holo)
      --    = analyticPart - rest_pp - rest_holo. Use h_pole eq: c/(z-s) = f - regularPart.
      -- Actually no simpler: just ring it out — the polarPart cancels naturally.
      ring
    rw [residue_congr h_evEq]
    exact residue_eq_zero_of_analyticAt g_an
  · -- Uncrossed case: laurentHigherOrderPolarAt s = 0.
    -- Local form: `regularPart - rest_pp - rest_holo`, analytic at `s`.
    have h_term_zero : ∀ z, laurentHigherOrderPolarAt hCondB s hs z = 0 := by
      intro z
      unfold laurentHigherOrderPolarAt
      rw [if_neg h_cross]
    set g : ℂ → ℂ :=
      fun z => h_pole.regularPart z - rest_pp z - rest_holo z with g_def
    have g_an : AnalyticAt ℂ g s :=
      (h_pole.regularPart_analyticAt.sub rest_pp_an).sub rest_holo_an
    have h_evEq : (laurentHolomorphicRemainder hCondB) =ᶠ[𝓝[≠] s] g := by
      have h_pole_eq := h_pole.eventually_eq
      have h_coeff_eq : h_pole.coeff = residue f s := (residue_eq_coeff h_pole).symm
      filter_upwards [h_pole_eq] with z hz_pole
      simp only [laurentHolomorphicRemainder, pp_decomp z, holo_decomp z, h_term_zero z,
        hz_pole, g_def, h_coeff_eq, zero_add]
      ring
    rw [residue_congr h_evEq]
    exact residue_eq_zero_of_analyticAt g_an

end LeanModularForms

end
