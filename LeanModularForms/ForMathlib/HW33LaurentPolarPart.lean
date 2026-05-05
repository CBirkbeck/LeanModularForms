/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.HW33SectorEven
import LeanModularForms.ForMathlib.HW33MultiPole
import LeanModularForms.ForMathlib.FlatnessConditions

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
noncomputable def crossingParam
    (γ : PwC1Immersion x x) (s : ℂ) : ℝ :=
  open Classical in if h : IsCrossed γ s then Classical.choose h else 0

theorem crossingParam_mem_Ioo
    {γ : PwC1Immersion x x} {s : ℂ}
    (h : IsCrossed γ s) :
    crossingParam γ s ∈ Set.Ioo (0 : ℝ) 1 := by
  simp only [crossingParam, h, ↓reduceDIte]
  exact (Classical.choose_spec h).1

theorem γ_at_crossingParam
    {γ : PwC1Immersion x x} {s : ℂ}
    (h : IsCrossed γ s) :
    (γ : ℝ → ℂ) (crossingParam γ s) = s := by
  simp only [crossingParam, h, ↓reduceDIte]
  exact (Classical.choose_spec h).2

/-! ## Laurent decomposition extraction from condition (B) -/

/-- Helper: when `s ∈ S`, `γ` crosses `s`, and `hCondB.laurent_compatible`
holds, extract the existential at `s`. Returns the existential statement
to be unpacked by `Classical.choose`. -/
private theorem laurent_data_exists
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S)
    {s : ℂ} (hs : s ∈ S) (h_cross : IsCrossed γ s) :
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

/-- Extracted pole order at a crossed pole `s ∈ S` from condition (B).
Returns `0` if `s` is not crossed (vacuous case). -/
noncomputable def laurentPolarOrderAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) : ℕ :=
  open Classical in
  if h : IsCrossed γ s then
    (laurent_data_exists hCondB hs h).choose
  else 0

/-- Extracted Laurent coefficients at a crossed pole. -/
noncomputable def laurentPolarCoeffAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) :
    Fin (laurentPolarOrderAt hCondB s hs) → ℂ :=
  open Classical in
  if h : IsCrossed γ s then by
    have h_data := (laurent_data_exists hCondB hs h).choose_spec
    have h_eq : laurentPolarOrderAt hCondB s hs =
        (laurent_data_exists hCondB hs h).choose := by
      simp only [laurentPolarOrderAt, h, ↓reduceDIte]
    rw [h_eq]
    exact h_data.choose
  else by
    -- When not crossed, laurentPolarOrderAt = 0, so Fin 0 is empty
    have h_zero : laurentPolarOrderAt hCondB s hs = 0 := by
      simp only [laurentPolarOrderAt, h, ↓reduceDIte]
    rw [h_zero]
    exact Fin.elim0

/-- Local polar part at pole `s`: `∑ k ∈ Fin N, a_k / (z - s)^(k+1)`. -/
noncomputable def laurentPolarPartAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) (z : ℂ) : ℂ :=
  ∑ k : Fin (laurentPolarOrderAt hCondB s hs),
    laurentPolarCoeffAt hCondB s hs k / (z - s) ^ (k.val + 1)

/-- Total polar part: sum over all poles in `S`. -/
noncomputable def laurentPolarPartTotal
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  ∑ s ∈ S.attach, laurentPolarPartAt hCondB s.1 s.2 z

/-- Holomorphic remainder: `f - laurentPolarPartTotal`. By condition (B)'s
Laurent compatibility, this is analytic at each pole `s ∈ S`. -/
noncomputable def laurentHolomorphicRemainder
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  f z - laurentPolarPartTotal hCondB z

/-! ## Decomposition identity (TIGHT-2 building block) -/

/-- **Fundamental identity**: by definition,
`f z = laurentPolarPartTotal hCondB z + laurentHolomorphicRemainder hCondB z`. -/
theorem f_eq_polar_plus_holo
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) :
    f z =
      laurentPolarPartTotal hCondB z + laurentHolomorphicRemainder hCondB z := by
  simp [laurentHolomorphicRemainder]

/-! ## Analytic part of the Laurent decomposition

The analytic remainder `g` from condition (B)'s `laurent_compatible` data is
the holomorphic part of the local decomposition `f = g + ∑ aₖ / (z-s)^(k+1)`
near a crossed pole `s ∈ S`. Extracting this `g` as a separate function
provides the building block for proving global analyticity of
`laurentHolomorphicRemainder` (TIGHT-4). -/

/-- The analytic remainder `g` from condition (B)'s Laurent compatibility data
at a crossed pole `s ∈ S`. By definition, `f z = g z + ∑ a_k / (z-s)^(k+1)`
holds eventually near `s`. For uncrossed `s`, this is the zero function. -/
noncomputable def laurentAnalyticPartAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (s : ℂ) (hs : s ∈ S) : ℂ → ℂ :=
  open Classical in
  if h : IsCrossed γ s then
    (laurent_data_exists hCondB hs h).choose_spec.choose_spec.choose
  else 0

/-- The analytic part is `AnalyticAt ℂ` at `s` (for crossed `s`). -/
theorem laurentAnalyticPartAt_analyticAt
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) {s : ℂ} (hs : s ∈ S)
    (h_cross : IsCrossed γ s) :
    AnalyticAt ℂ (laurentAnalyticPartAt hCondB s hs) s := by
  unfold laurentAnalyticPartAt
  classical
  rw [dif_pos h_cross]
  exact (laurent_data_exists hCondB hs h_cross).choose_spec.choose_spec.choose_spec.1

/-! ## Decomposition relative to simple-pole `principalPartSum` -/

/-- The **higher-order polar part**: `laurentPolarPartTotal` with the
simple-pole `principalPartSum` subtracted. This is the input to the
(B)-closure machinery for the higher-order Laurent terms. -/
noncomputable def laurentHigherOrderPolar
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) : ℂ :=
  laurentPolarPartTotal hCondB z -
    principalPartSum S (fun s => residue f s) z

/-- **Decomposition for `hCancel` discharge**:
`f - principalPartSum = laurentHigherOrderPolar + laurentHolomorphicRemainder`. -/
theorem f_minus_pp_eq_higherOrder_plus_holo
    {γ : PwC1Immersion x x} {f : ℂ → ℂ} {S : Finset ℂ}
    (hCondB : SatisfiesConditionB γ f S) (z : ℂ) :
    f z - principalPartSum S (fun s => residue f s) z =
      laurentHigherOrderPolar hCondB z +
        laurentHolomorphicRemainder hCondB z := by
  simp only [laurentHigherOrderPolar, laurentHolomorphicRemainder]; ring

end LeanModularForms

end
