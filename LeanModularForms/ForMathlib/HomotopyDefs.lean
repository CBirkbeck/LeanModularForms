/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Homotopy Definitions on [0,1]

Definitions and basic properties for piecewise C¹ and smooth homotopies between
closed curves on the unit interval `[0, 1]`, avoiding a given point `z₀`.

## Main definitions

* `PiecewiseCurvesHomotopicAvoiding` — piecewise C¹ homotopy between closed curves
  on `[0, 1]` avoiding `z₀`, with a finite partition `P` of breakpoints.
* `ClosedCurvesHomotopicAvoiding` — smooth homotopy between closed curves on `[0, 1]`
  avoiding `z₀` (no partition needed).

## Main results

* `ClosedCurvesHomotopicAvoiding.toPiecewise` — a smooth homotopy is a piecewise
  homotopy with empty partition.
* `PiecewiseCurvesHomotopicAvoiding.refl` — reflexivity: every curve is homotopic
  to itself.
* `PiecewiseCurvesHomotopicAvoiding.symm` — symmetry: reverse the homotopy parameter.
* `homotopy_uniform_avoidance` — compactness gives a uniform positive distance from `z₀`.

## Design notes

Both `t` (curve parameter) and `s` (homotopy parameter) range over `[0, 1]`.
The previous definitions in `Homotopy/Integrality.lean` used a general interval
`[a, b]` for the curve parameter; these are the `[0, 1]`-specialised versions.
-/

open Set Filter Topology Complex
open scoped Real

noncomputable section

/-! ### Definitions -/

/-- Piecewise C¹ homotopy between **closed** curves on `[0, 1]` avoiding `z₀`.

The homotopy `H : ℝ × ℝ → ℂ` satisfies:
* continuity,
* boundary conditions (`H(·, 0) = γ₀`, `H(·, 1) = γ₁`),
* closure (`H(0, s) = H(1, s)`),
* avoidance (`H(t, s) ≠ z₀`),
* differentiability in `t` away from `P`,
* piecewise continuity of the `t`-derivative,
* a uniform derivative bound. -/
def PiecewiseCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) (P : Finset ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc (0 : ℝ) 1, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (0, s) = H (1, s)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, t ∉ P →
      ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    (∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo (0 : ℝ) 1 →
        ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
          (Ioo p₁ p₂ ×ˢ Icc 0 1)) ∧
    (∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M)

/-- Smooth homotopy between **closed** curves on `[0, 1]` avoiding `z₀`.

This is strictly stronger than `PiecewiseCurvesHomotopicAvoiding`: the `t`-derivative
of `H` is continuous on the full product `(0, 1) × [0, 1]` (no partition needed),
and a uniform derivative bound is required. -/
def ClosedCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc (0 : ℝ) 1, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (0, s) = H (1, s)) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀) ∧
    (∀ t ∈ Ioo (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
      (Ioo 0 1 ×ˢ Icc 0 1) ∧
    (∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M)

/-! ### Conversion: smooth implies piecewise -/

/-- A smooth closed homotopy is a piecewise homotopy with empty partition.

Differentiability holds everywhere in `(0, 1)` (the partition condition is vacuous),
and the global continuity of the derivative restricts to every sub-interval. -/
theorem ClosedCurvesHomotopicAvoiding.toPiecewise
    {γ₀ γ₁ : ℝ → ℂ} {z₀ : ℂ}
    (h : ClosedCurvesHomotopicAvoiding γ₀ γ₁ z₀) :
    PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ ∅ := by
  obtain ⟨H, hcont, hH0, hH1, hclosed, havoid, hdiff, hderiv_cont, hbound⟩ := h
  refine ⟨H, hcont, hH0, hH1, hclosed, havoid, ?_, ?_, hbound⟩
  · intro t ht _ s hs
    exact hdiff t ht s hs
  · intro p₁ p₂ _ _ hI
    exact hderiv_cont.mono (prod_mono hI Subset.rfl)

/-! ### Reflexivity -/

/-- Reflexivity: every piecewise C¹ closed curve avoiding `z₀` is homotopic to itself.

The constant homotopy `H(t, s) = γ(t)` satisfies all conditions trivially. -/
theorem PiecewiseCurvesHomotopicAvoiding.refl
    {γ : ℝ → ℂ} {z₀ : ℂ} {P : Finset ℝ}
    (hγ_cont : Continuous γ)
    (hγ_closed : γ 0 = γ 1)
    (hγ_avoid : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z₀)
    (hγ_diff : ∀ t ∈ Ioo (0 : ℝ) 1, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo (0 : ℝ) 1 →
        ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_bound : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv γ t‖ ≤ M) :
    PiecewiseCurvesHomotopicAvoiding γ γ z₀ P := by
  refine ⟨fun p => γ p.1, hγ_cont.comp continuous_fst, fun _ _ => rfl,
    fun _ _ => rfl, fun _ _ => hγ_closed, fun t ht _ _ => hγ_avoid t ht,
    fun t ht htp _ _ => hγ_diff t ht htp, ?_, ?_⟩
  · intro p₁ p₂ hp hvac hI
    have h_eq : ∀ (q : ℝ × ℝ), q ∈ Ioo p₁ p₂ ×ˢ Icc (0 : ℝ) 1 →
        deriv (fun t' => (fun p : ℝ × ℝ => γ p.1) (t', q.2)) q.1 = deriv γ q.1 :=
      fun _ _ => rfl
    exact ContinuousOn.congr
      ((hγ_deriv_cont p₁ p₂ hp hvac hI).comp continuousOn_fst
        (fun q hq => hq.1)) h_eq
  · obtain ⟨M, hM⟩ := hγ_bound
    exact ⟨M, fun t ht _ _ => hM t ht⟩

/-! ### Symmetry -/

private lemma one_sub_mem_Icc {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 1 - s ∈ Icc (0 : ℝ) 1 :=
  ⟨by linarith [hs.2], by linarith [hs.1]⟩

/-- Symmetry: if `γ₀` is homotopic to `γ₁` avoiding `z₀`, then `γ₁` is homotopic
to `γ₀`. The reversed homotopy is `H'(t, s) = H(t, 1 - s)`. -/
theorem PiecewiseCurvesHomotopicAvoiding.symm
    {γ₀ γ₁ : ℝ → ℂ} {z₀ : ℂ} {P : Finset ℝ}
    (h : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ P) :
    PiecewiseCurvesHomotopicAvoiding γ₁ γ₀ z₀ P := by
  obtain ⟨H, hcont, hH0, hH1, hclosed, havoid, hdiff, hderiv_cont, ⟨M, hbound⟩⟩ := h
  refine ⟨fun p => H (p.1, 1 - p.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hcont.comp (continuous_fst.prodMk (continuous_const.sub continuous_snd))
  · intro t ht
    simp only [sub_zero]
    exact hH1 t ht
  · intro t ht
    simp only [sub_self]
    exact hH0 t ht
  · intro s hs
    exact hclosed (1 - s) (one_sub_mem_Icc hs)
  · intro t ht s hs
    exact havoid t ht (1 - s) (one_sub_mem_Icc hs)
  · intro t ht htp s hs
    exact hdiff t ht htp (1 - s) (one_sub_mem_Icc hs)
  · intro p₁ p₂ hp hvac hI
    let φ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1, 1 - q.2)
    have hφ_cont : Continuous φ :=
      continuous_fst.prodMk (continuous_const.sub continuous_snd)
    have hφ_maps : ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0 : ℝ) 1,
        φ q ∈ Ioo p₁ p₂ ×ˢ Icc (0 : ℝ) 1 :=
      fun ⟨_, _⟩ ⟨ht, hs⟩ => ⟨ht, one_sub_mem_Icc hs⟩
    have h_eq : ∀ q ∈ Ioo p₁ p₂ ×ˢ Icc (0 : ℝ) 1,
        deriv (fun t' => H (t', 1 - q.2)) q.1 =
        (fun q => deriv (fun t' => H (t', q.2)) q.1) (φ q) :=
      fun _ _ => rfl
    exact ContinuousOn.congr
      ((hderiv_cont p₁ p₂ hp hvac hI).comp hφ_cont.continuousOn hφ_maps)
      (fun q hq => (h_eq q hq).symm)
  · exact ⟨M, fun t ht s hs => hbound t ht (1 - s) (one_sub_mem_Icc hs)⟩

/-! ### Uniform avoidance from compactness -/

/-- Compactness gives a uniform positive distance from `z₀`.

If `H` is continuous on `[0, 1] × [0, 1]` and avoids `z₀` everywhere, then there
exists `δ > 0` such that `‖H(t, s) - z₀‖ ≥ δ` for all `(t, s) ∈ [0, 1] × [0, 1]`.
This is the key compactness argument used in homotopy invariance proofs. -/
theorem homotopy_uniform_avoidance
    (H : ℝ × ℝ → ℂ) (z₀ : ℂ)
    (hH_cont : Continuous H)
    (hH_avoid : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, δ ≤ ‖H (t, s) - z₀‖ := by
  have hcompact : IsCompact (H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image hH_cont
  have hnonempty : (H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).Nonempty :=
    ⟨H (0, 0), (0, 0),
      ⟨left_mem_Icc.mpr zero_le_one, left_mem_Icc.mpr zero_le_one⟩, rfl⟩
  have hz_notin : z₀ ∉ H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    fun ⟨⟨t, s⟩, ⟨ht, hs⟩, heq⟩ => hH_avoid t ht s hs heq
  have hδ := (hcompact.isClosed.notMem_iff_infDist_pos hnonempty).mp hz_notin
  refine ⟨_, hδ, fun t ht s hs => ?_⟩
  have hmem : H (t, s) ∈ H '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    ⟨(t, s), ⟨ht, hs⟩, rfl⟩
  calc Metric.infDist z₀ _ ≤ dist z₀ (H (t, s)) := Metric.infDist_le_dist_of_mem hmem
    _ = ‖H (t, s) - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]

end
