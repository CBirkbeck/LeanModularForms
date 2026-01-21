/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: 8c887cb6-d214-43db-903b-73c8e51a2b38

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- lemma hasDerivAt_segmentIntegral {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hS_convex : Convex ℝ S) (hS_open : IsOpen S)
    (hc : c ∈ S) (hz : z ∈ S)
    (hf : DifferentiableOn ℂ f S) :
    HasDerivAt (fun w => ∫ t in (0:ℝ)..1, f (c + t • (w - c)) * (w - c)) (f z) z

- theorem modelSector_windingNumber (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 2 * Real.pi) :
    ∃ (γ : ℝ → ℂ) (a b : ℝ), a < b ∧ γ a = 0 ∧ γ b = 0 ∧
      Tendsto (fun ε => (1 / (2 * Real.pi * I)) *
        ∫ t in a..b, if ε < ‖γ t‖ then (γ t)⁻¹ * deriv γ t else 0)
        (𝓝[>] 0) (𝓝 (α / (2 * Real.pi)))

The following was negated by Aristotle:

- theorem cauchyTheorem_homotopic {f : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ₀_in : ∀ t ∈ Icc a b, γ₀ t ∈ U)
    (hγ₁_in : ∀ t ∈ Icc a b, γ₁ t ∈ U)
    (hγ₀_closed : γ₀ a = γ₀ b)
    (hγ₁_closed : γ₁ a = γ₁ b)
    (H : ℝ × ℝ → ℂ) (hH_cont : Continuous H)
    (hH_in : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ∈ U)
    (hH₀ : ∀ t ∈ Icc a b, H (t, 0) = γ₀ t)
    (hH₁ : ∀ t ∈ Icc a b, H (t, 1) = γ₁ t)
    (hf : DifferentiableOn ℂ f U)
    (hγ₀_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ₀ t)
    (hγ₁_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ₁ t) :
    ∫ t in a..b, f (γ₀ t) * deriv γ₀ t = ∫ t in a..b, f (γ₁ t) * deriv γ₁ t

- theorem residueTheorem_classical
    {f : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (poles : Finset ℂ)
    (hpoles_in : ∀ z ∈ poles, z ∈ U)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ U)
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ∉ poles)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ t)
    (hf : DifferentiableOn ℂ f (U \ poles))
    (hf_simple : ∀ z ∈ poles, ∃ c g, DifferentiableOn ℂ g (Metric.ball z 1) ∧
      ∀ w ∈ Metric.ball z 1 \ {z}, f w = c / (w - z) + g w) :
    ∫ t in a..b, f (γ t) * deriv γ t =
      2 * Real.pi * I * ∑ z ∈ poles,
        (residue_contour f z) * (1 / (2 * Real.pi * I) *
          ∫ t in a..b, (γ t - z)⁻¹ * deriv γ t)

Here is the code for the `negate_state` tactic, used within these negations:

```lean
import Mathlib
open Lean Meta Elab Tactic in
elab "revert_all" : tactic => do
  let goals ← getGoals
  let mut newGoals : List MVarId := []
  for mvarId in goals do
    newGoals := newGoals.append [(← mvarId.revertAll)]
  setGoals newGoals

open Lean.Elab.Tactic in
macro "negate_state" : tactic => `(tactic|
  (
    guard_goal_nums 1
    revert_all
    refine @(((by admit) : ∀ {p : Prop}, ¬p → p) ?_)
    try (push_neg; guard_goal_nums 1)
  )
)
```
-/

/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral


/-!
# Cauchy's Theorem for Piecewise C¹ Curves

This file extends Cauchy's integral theorem from smooth curves to piecewise C¹ curves,
which is needed for the generalized residue theorem.

## Strategy

We break down Cauchy's theorem into small lemmas that use mathlib directly:

1. **FTC approach**: For a function with a primitive, the integral along any curve
   from p to q equals F(q) - F(p). For a closed curve, this is 0.

2. **Key mathlib results used**:
   - `DifferentiableOn.isExactOn_ball`: Holomorphic functions on balls have primitives
   - `intervalIntegral.integral_eq_sub_of_hasDerivAt`: FTC for interval integrals
   - `circleIntegral.integral_sub_center_inv`: ∮ (z-c)⁻¹ dz = 2πi
   - `circleIntegral_eq_zero_of_differentiable_on_off_countable`: Cauchy for circle integrals
-/

open Complex MeasureTheory Set Filter Topology

open scoped Real Interval

noncomputable section

/-! ## Part 1: Fundamental Theorem of Calculus for Complex Line Integrals -/

/-- If F is a primitive of f along γ (i.e., F'(γ(t)) = f(γ(t)) for all t), then the
    line integral of f along γ equals F(γ(b)) - F(γ(a)). -/
theorem lineIntegral_eq_sub_of_hasPrimitive {F f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hF : ∀ z, HasDerivAt F (f z) z)
    (hf_cont : ContinuousOn f (γ '' Icc a b)) :
    ∫ t in a..b, f (γ t) * deriv γ t = F (γ b) - F (γ a) := by
  -- The integrand is (F ∘ γ)'(t) by chain rule
  have h_comp : ∀ t ∈ Ioo a b, HasDerivAt (F ∘ γ) (f (γ t) * deriv γ t) t := by
    intro t ht
    have hγ_at : DifferentiableAt ℝ γ t := hγ_diff t ht
    have h := (hF (γ t)).comp_of_eq t (hγ_at.hasDerivAt) rfl
    convert h using 1
  -- Apply FTC
  have h_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.mul
    · exact hf_cont.comp hγ_cont (mapsTo_image γ _)
    · exact hγ'_cont
  have h_cont : ContinuousOn (F ∘ γ) (Icc a b) := by
    apply ContinuousOn.comp _ hγ_cont (mapsTo_image γ _)
    have hF_diff : Differentiable ℂ F := fun z => (hF z).differentiableAt
    exact hF_diff.continuous.continuousOn
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab h_cont h_comp h_int

/-- For a closed curve (γ(a) = γ(b)) and a function with a primitive, the line integral is 0. -/
theorem lineIntegral_eq_zero_of_hasPrimitive_closed {F f : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ}
    (hab : a ≤ b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hF : ∀ z, HasDerivAt F (f z) z)
    (hf_cont : ContinuousOn f (γ '' Icc a b)) :
    ∫ t in a..b, f (γ t) * deriv γ t = 0 := by
  rw [lineIntegral_eq_sub_of_hasPrimitive hab hγ_cont hγ_diff hγ'_cont hF hf_cont, hγ_closed, sub_self]

/-! ## Part 2: Holomorphic Functions on Balls Have Primitives -/

/-- A holomorphic function on a ball has a primitive on that ball.
    This uses that holomorphic functions on convex open sets have primitives. -/
theorem hasPrimitive_on_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (_hr : 0 < r)
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∃ F : ℂ → ℂ, ∀ z ∈ Metric.ball c r, HasDerivAt F (f z) z := by
  -- Use mathlib's DifferentiableOn.isExactOn_ball (Morera's theorem)
  exact hf.isExactOn_ball

/-- Cauchy's theorem for curves contained in a ball where f is holomorphic. -/
theorem cauchyTheorem_ball {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ Metric.ball c r)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) :
    ∫ t in a..b, f (γ t) * deriv γ t = 0 := by
  -- Use that f has a primitive on the ball
  obtain ⟨F₀, hF₀⟩ := hasPrimitive_on_ball hr hf
  -- Apply FTC via chain rule: (F₀ ∘ γ)'(t) = f(γ(t)) * γ'(t)
  have h_comp : ∀ t ∈ Ioo a b, HasDerivAt (F₀ ∘ γ) (f (γ t) * deriv γ t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hγt : γ t ∈ Metric.ball c r := hγ_in t ht'
    have hγ_at : DifferentiableAt ℝ γ t := hγ_diff t ht
    have h := (hF₀ (γ t) hγt).comp_of_eq t (hγ_at.hasDerivAt) rfl
    convert h using 1
  -- Continuity of f on curve image
  have hf_cont : ContinuousOn f (γ '' Icc a b) := by
    apply hf.continuousOn.mono
    intro z ⟨t, ht, htz⟩
    exact htz ▸ hγ_in t ht
  -- Continuity of F₀ ∘ γ
  have h_cont : ContinuousOn (F₀ ∘ γ) (Icc a b) := by
    apply ContinuousOn.comp _ hγ_cont (fun t ht => hγ_in t ht)
    intro z hz
    exact (hF₀ z hz).continuousAt.continuousWithinAt
  -- Integrability
  have h_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.mul
    · exact hf_cont.comp hγ_cont (mapsTo_image γ _)
    · exact hγ'_cont
  -- Apply FTC
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab h_cont h_comp h_int
  rw [this]
  simp only [Function.comp_apply, hγ_closed, sub_self]

/-! ## Part 3: Cauchy's Theorem for Convex Regions

The Isabelle approach (HOL-Complex_Analysis):
1. `holomorphic_convex_primitive`: Holomorphic on convex open ⇒ has primitive on that set
2. Primitive defined as: F(z) = ∫_{c→z along segment} f for some fixed c ∈ S
3. Works because S is convex, so all line segments stay in S
4. Then use FTC to conclude ∮_γ f = 0 for closed curves

The key insight: we do NOT need to fit the curve into a single ball.
Instead, we work directly with the primitive on the entire convex set.
-/

/-! ### Helper lemmas for primitive construction -/

/-- The segment from c to z stays in a convex set S when c, z ∈ S. -/
lemma segment_subset_convex {S : Set ℂ} (hS : Convex ℝ S) {c z : ℂ} (hc : c ∈ S) (hz : z ∈ S) :
    ∀ t ∈ Icc (0:ℝ) 1, c + t • (z - c) ∈ S := by
  intro t ht
  have heq : c + t • (z - c) = (1 - t) • c + t • z := by
    simp only [smul_sub, sub_smul, one_smul]; ring
  rw [heq]
  have h1 : 0 ≤ 1 - t := by linarith [ht.2]
  have h2 : 0 ≤ t := ht.1
  have h3 : 1 - t + t = 1 := by ring
  exact hS hc hz h1 h2 h3

/-- The integrand f(c + t(z-c)) · (z-c) is continuous in t on [0,1] when f is continuous. -/
lemma segmentIntegrand_continuousOn {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hf : ContinuousOn f S) (h_seg : ∀ t ∈ Icc (0:ℝ) 1, c + t • (z - c) ∈ S) :
    ContinuousOn (fun t : ℝ => f (c + t • (z - c)) * (z - c)) (Icc 0 1) := by
  apply ContinuousOn.mul _ continuousOn_const
  apply ContinuousOn.comp hf _ (fun t ht => h_seg t ht)
  apply Continuous.continuousOn
  continuity

/-- The segment integral is integrable. -/
lemma segmentIntegral_integrable {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hf : ContinuousOn f S) (h_seg : ∀ t ∈ Icc (0:ℝ) 1, c + t • (z - c) ∈ S) :
    IntervalIntegrable (fun t => f (c + t • (z - c)) * (z - c)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact segmentIntegrand_continuousOn hf h_seg

/-- Key computation: integration by parts for ∫₀¹ t · φ'(t) dt = φ(1) - ∫₀¹ φ(t) dt.
    Here φ(t) = f(c + t(z-c)) where f is holomorphic on S containing the segment. -/
lemma integral_t_mul_deriv_eq {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hS_open : IsOpen S) (hf : DifferentiableOn ℂ f S)
    (h_seg : ∀ t ∈ Icc (0:ℝ) 1, c + t • (z - c) ∈ S) :
    ∫ t in (0:ℝ)..1, t * (deriv f (c + t • (z - c)) * (z - c)) =
      f z - ∫ t in (0:ℝ)..1, f (c + t • (z - c)) := by
  -- Let φ(t) = f(c + t(z-c)), then φ'(t) = f'(c + t(z-c)) · (z-c)
  -- We have ∫₀¹ t · φ'(t) dt = [t·φ(t)]₀¹ - ∫₀¹ φ(t) dt = φ(1) - ∫₀¹ φ(t) dt = f(z) - ∫₀¹ φ dt
  -- Define u(t) = t and v(t) = f(c + t(z-c))
  let u : ℝ → ℂ := fun t => t
  let v : ℝ → ℂ := fun t => f (c + t • (z - c))
  let u' : ℝ → ℂ := fun _ => 1
  let v' : ℝ → ℂ := fun t => deriv f (c + t • (z - c)) * (z - c)
  -- The inner function γ(t) = c + t(z-c)
  let γ : ℝ → ℂ := fun t => c + t • (z - c)
  have hγ_cont : Continuous γ := continuous_const.add (continuous_ofReal.smul continuous_const)
  -- Establish continuity of u
  have hu_cont : ContinuousOn u (Set.uIcc 0 1) := continuous_ofReal.continuousOn
  -- Establish continuity of v
  have hv_cont : ContinuousOn v (Set.uIcc 0 1) := by
    have : v = f ∘ γ := rfl
    rw [this]
    apply ContinuousOn.comp hf.continuousOn hγ_cont.continuousOn
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    exact h_seg t ht
  -- Establish derivative of u
  have hu_deriv : ∀ x ∈ Set.Ioo (min 0 1) (max 0 1), HasDerivAt u (u' x) x := by
    intro x _
    simp only [u, u']
    exact ofRealCLM.hasDerivAt
  -- Derivative of inner function γ
  have hγ_deriv : ∀ t : ℝ, HasDerivAt γ (z - c) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := ofRealCLM.hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) • (z - c)) ((1 : ℂ) • (z - c)) t :=
      h1.smul_const (z - c)
    simp only [one_smul] at h2
    have h3 : HasDerivAt (fun _ : ℝ => c) 0 t := hasDerivAt_const t c
    convert h3.add h2 using 1
    ring
  -- Establish derivative of v (chain rule)
  have hv_deriv : ∀ x ∈ Set.Ioo (min 0 1) (max 0 1), HasDerivAt v (v' x) x := by
    intro t ht
    simp only [v, v']
    simp only [min_eq_left, max_eq_right, (by norm_num : (0:ℝ) ≤ 1)] at ht
    have ht' : t ∈ Icc (0:ℝ) 1 := Ioo_subset_Icc_self ht
    have h_in_S : γ t ∈ S := h_seg t ht'
    have h_diff_at : DifferentiableAt ℂ f (γ t) := hf.differentiableAt (hS_open.mem_nhds h_in_S)
    -- Chain rule: (f ∘ γ)'(t) = γ'(t) • f'(γ(t))
    have h_chain : HasDerivAt (f ∘ γ) ((z - c) • deriv f (γ t)) t := by
      have hγ' := hγ_deriv t
      exact h_diff_at.hasDerivAt.scomp t hγ'
    -- smul and mul are the same for ℂ, just reorder
    simp only [smul_eq_mul] at h_chain
    convert h_chain using 1
    ring
  -- Integrability of u'
  have hu'_int : IntervalIntegrable u' MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable continuousOn_const
  -- Integrability of v'
  have hv'_int : IntervalIntegrable v' MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply ContinuousOn.mul _ continuousOn_const
    -- For holomorphic functions on open sets, the derivative is continuous
    have hContDiff : ContDiffOn ℂ 1 f S := hf.contDiffOn hS_open
    have hderiv_cont : ContinuousOn (deriv f) S :=
      hContDiff.continuousOn_deriv_of_isOpen hS_open le_rfl
    exact hderiv_cont.comp hγ_cont.continuousOn (fun t ht => h_seg t ht)
  -- Apply integration by parts: ∫ u * v' = u(1)*v(1) - u(0)*v(0) - ∫ u' * v
  have h_parts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu_cont hv_cont hu_deriv hv_deriv hu'_int hv'_int
  -- Simplify: u(1) = 1, u(0) = 0, u' = 1, so ∫ u * v' = v(1) - ∫ v
  simp only [u, v, u', v'] at h_parts
  simp only [ofReal_one, ofReal_zero, one_mul, zero_mul, sub_zero] at h_parts
  -- v(1) = f(c + 1 • (z - c)) = f(z)
  have hv1 : f (c + (1 : ℝ) • (z - c)) = f z := by
    simp only [one_smul]
    ring_nf
  rw [hv1] at h_parts
  -- Match forms: They already match after simplification
  exact h_parts

/- The derivative of the segment integral F(z) = ∫₀¹ f(c + t(z-c)) · (z-c) dt equals f(z).

    This is the core computation for holomorphic_convex_primitive.
    The proof uses differentiation under the integral and integration by parts:
    1. F'(z) = ∫₀¹ f(c + t(z-c)) dt + (z-c) · ∫₀¹ t · f'(c + t(z-c)) dt  (product rule)
    2. ∫₀¹ t · f'(c + t(z-c)) · (z-c) dt = f(z) - ∫₀¹ f(c + t(z-c)) dt   (by parts)
    3. F'(z) = ∫₀¹ f dt + f(z) - ∫₀¹ f dt = f(z)
-/
noncomputable section AristotleLemmas

/-
Differentiation under the integral sign for the auxiliary function H(w).
-/
lemma hasDerivAt_integral_subst {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hS_convex : Convex ℝ S) (hS_open : IsOpen S)
    (hc : c ∈ S) (hz : z ∈ S)
    (hf : DifferentiableOn ℂ f S) :
    HasDerivAt (fun w => ∫ t in (0:ℝ)..1, f (c + t • (w - c)))
      (∫ t in (0:ℝ)..1, t * deriv f (c + t • (z - c))) z := by
        -- Since $S$ is open, there exists $\epsilon > 0$ such that $\overline{B(z, \epsilon)} \subseteq S$.
        obtain ⟨ε, hε_pos, hε_ball⟩ : ∃ ε > 0, Metric.closedBall z ε ⊆ S := by
          exact Metric.nhds_basis_closedBall.mem_iff.mp ( hS_open.mem_nhds hz );
        -- Let $K$ be the image of $[0, 1] \times \overline{B(z, \epsilon)}$ under the map $(t, w) \mapsto c + t(w - c)$.
        set K := {u : ℂ | ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ w ∈ Metric.closedBall z ε, u = c + t • (w - c)} with hK_def;
        -- Since $K$ is compact and $f'$ is continuous on $S$, $f'$ is bounded on $K$. Let $M = \sup_{u \in K} \|f'(u)\|$.
        obtain ⟨M, hM⟩ : ∃ M > 0, ∀ u ∈ K, ‖deriv f u‖ ≤ M := by
          have hK_compact : IsCompact K := by
            have hK_compact : IsCompact (Set.image (fun p : ℝ × ℂ => c + p.1 • (p.2 - c)) (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall z ε)) := by
              exact IsCompact.image ( isCompact_Icc.prod ( ProperSpace.isCompact_closedBall _ _ ) ) ( by continuity );
            convert hK_compact using 1 ; ext ; aesop;
          have hK_subset_S : K ⊆ S := by
            rintro u ⟨ t, ht, w, hw, rfl ⟩ ; convert hS_convex hc ( hε_ball hw ) ( show 0 ≤ 1 - t by linarith [ ht.1, ht.2 ] ) ( show 0 ≤ t by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) using 1 ; simp +decide ; ring;
          have hK_bounded : ContinuousOn (deriv f) K := by
            have hK_bounded : DifferentiableOn ℂ (deriv f) S := by
              exact?;
            exact hK_bounded.continuousOn.mono hK_subset_S;
          obtain ⟨ M, hM ⟩ := hK_compact.exists_bound_of_continuousOn hK_bounded; use Max.max M 1; aesop;
        have := @intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le;
        contrapose! this;
        refine' ⟨ ℂ, inferInstance, MeasureTheory.MeasureSpace.volume, ℂ, inferInstance, inferInstance, inferInstance, 0, 1, ε, fun _ => M, fun w t => f ( c + t • ( w - c ) ), fun w t => t • deriv f ( c + t • ( w - c ) ), z, hε_pos, _, _, _, _, _ ⟩ <;> norm_num;
        · refine' Filter.eventually_of_mem ( Metric.ball_mem_nhds z hε_pos ) fun w hw => ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc;
          refine' ContinuousOn.comp hf.continuousOn _ _;
          · fun_prop;
          · intro t ht;
            have := hS_convex hc ( hε_ball <| Metric.mem_closedBall.mpr <| le_of_lt hw );
            convert this ( show 0 ≤ 1 - t by linarith [ ht.1, ht.2 ] ) ( show 0 ≤ t by linarith [ ht.1, ht.2 ] ) ( by linarith [ ht.1, ht.2 ] ) using 1 ; norm_num ; ring;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.comp hf.continuousOn _ _;
          · exact Continuous.continuousOn ( by continuity );
          · intro t ht;
            norm_num +zetaDelta at *;
            exact hS_convex.add_smul_sub_mem hc hz ( by constructor <;> linarith );
        · fun_prop;
        · filter_upwards [ ] with t ht₁ ht₂ x hx using le_trans ( mul_le_of_le_one_left ( norm_nonneg _ ) ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ) ( hM.2 _ ⟨ t, ⟨ by linarith, by linarith ⟩, x, by simpa using hx.le, rfl ⟩ );
        · refine' ⟨ _, _ ⟩;
          · refine' Filter.Eventually.of_forall fun t ht₁ ht₂ x hx => _;
            convert HasDerivAt.comp x ( hf.hasDerivAt <| ?_ ) ( HasDerivAt.const_add _ <| HasDerivAt.const_mul _ <| hasDerivAt_id x |> HasDerivAt.sub <| hasDerivAt_const _ _ ) using 1;
            · norm_num [ mul_comm ];
            · refine' IsOpen.mem_nhds hS_open _;
              convert hS_convex hc ( hε_ball <| Metric.mem_closedBall.mpr <| le_of_lt hx ) ( show 0 ≤ 1 - t by linarith ) ( show 0 ≤ t by linarith ) ( by linarith ) using 1 ; norm_num ; ring;
          · exact?

end AristotleLemmas

lemma hasDerivAt_segmentIntegral {f : ℂ → ℂ} {S : Set ℂ} {c z : ℂ}
    (hS_convex : Convex ℝ S) (hS_open : IsOpen S)
    (hc : c ∈ S) (hz : z ∈ S)
    (hf : DifferentiableOn ℂ f S) :
    HasDerivAt (fun w => ∫ t in (0:ℝ)..1, f (c + t • (w - c)) * (w - c)) (f z) z := by
  -- The segment from c to any point w ∈ S stays in S by convexity
  have h_seg : ∀ w ∈ S, ∀ t ∈ Icc (0:ℝ) 1, c + t • (w - c) ∈ S := fun w hw t ht =>
    segment_subset_convex hS_convex hc hw t ht
  have h_seg_z : ∀ t ∈ Icc (0:ℝ) 1, c + t • (z - c) ∈ S := h_seg z hz

  -- Strategy: Use that z ∈ S (open) so there's a ball B(z, ε) ⊆ S
  -- On this ball, f has a primitive G by DifferentiableOn.isExactOn_ball
  -- Then the segment integral from c to w equals G(w) - G(c) for w near z
  -- So F'(z) = G'(z) = f(z)

  -- Get a ball around z contained in S
  obtain ⟨ε, hε_pos, hε_ball⟩ := Metric.isOpen_iff.mp hS_open z hz

  -- f is holomorphic on this ball, so has a primitive
  have hf_ball : DifferentiableOn ℂ f (Metric.ball z ε) := hf.mono hε_ball
  obtain ⟨G, hG⟩ := hf_ball.isExactOn_ball

  -- The segment integral from c to w equals G(w) - G(c) when the segment stays in S
  -- This uses FTC along the segment

  -- For w in the ball, the segment from c to w stays in S (by convexity)
  -- The line integral ∫_c^w f = G(w) - some constant

  -- Actually, we need to be more careful. The segment integral equals
  -- F(w) = ∫₀¹ f(c + t(w-c)) * (w-c) dt
  -- This is NOT the same as G(w) - G(c) in general (G is only defined on the ball)

  -- Better approach: Differentiate directly
  -- F(w) = (w - c) * ∫₀¹ f(c + t(w-c)) dt = (w - c) * H(w)
  -- where H(w) = ∫₀¹ f(c + t(w-c)) dt
  -- By product rule: F'(z) = H(z) + (z - c) * H'(z)

  -- Alternative: Use the parametric differentiation directly
  -- The formula F'(z) = f(z) follows from:
  -- 1. Leibniz rule for ∂/∂w ∫₀¹ f(c + t(w-c)) * (w-c) dt
  -- 2. The integral_t_mul_deriv_eq identity

  -- Product rule approach:
  -- Let H(w) = ∫₀¹ f(c + t(w-c)) dt
  -- Then F(w) = H(w) * (w - c)
  -- F'(z) = H(z) * 1 + H'(z) * (z - c) = H(z) + H'(z) * (z - c)

  -- We need to show this equals f(z).

  -- Claim: H'(z) * (z - c) = f(z) - H(z)
  -- This would give F'(z) = H(z) + f(z) - H(z) = f(z) ✓

  -- Proof of claim: H'(z) = ∫₀¹ t * f'(c + t(z-c)) dt (by differentiation under integral)
  -- So H'(z) * (z - c) = ∫₀¹ t * f'(c + t(z-c)) * (z-c) dt
  -- By integral_t_mul_deriv_eq, this equals f(z) - H(z) ✓

  -- Let's implement this:
  let H : ℂ → ℂ := fun w => ∫ t in (0:ℝ)..1, f (c + t • (w - c))

  -- Our function F(w) = H(w) * (w - c)
  have hF_eq : ∀ w, (∫ t in (0:ℝ)..1, f (c + t • (w - c)) * (w - c)) = H w * (w - c) := by
    intro w
    simp only [H]
    rw [← intervalIntegral.integral_mul_const]

  -- Show goal is equivalent to HasDerivAt for the rewritten form
  suffices HasDerivAt (fun w => H w * (w - c)) (f z) z by
    convert this using 1
    ext w
    exact hF_eq w

  -- Now we need HasDerivAt (fun w => H w * (w - c)) (f z) z
  -- By product rule: we need HasDerivAt H (H'(z)) z and combine

  -- H(z) = ∫₀¹ f(c + t(z-c)) dt
  -- H'(z) = ∫₀¹ t * f'(c + t(z-c)) dt (by differentiation under integral)

  -- For H'(z) * (z - c) + H(z) = f(z):
  -- H'(z) * (z - c) = ∫₀¹ t * f'(c + t(z-c)) * (z-c) dt = f(z) - H(z)
  -- by integral_t_mul_deriv_eq

  -- Product rule
  have h1 : HasDerivAt (fun w => w - c) 1 z := by
    convert (hasDerivAt_id z).sub (hasDerivAt_const z c) using 1
    ring

  -- For H, we use that H is differentiable with a specific derivative
  -- This requires parametric differentiation, which is complex.
  -- We use the following approach:

  -- The derivative H'(z) satisfies: H'(z) * (z - c) = f(z) - H(z)
  -- So (H(z) + H'(z) * (z - c)) = f(z)

  -- Therefore, if HasDerivAt H (H'(z)) z, then
  -- HasDerivAt (H * (· - c)) (H(z) * 1 + H'(z) * (z - c)) z = f(z)

  -- We prove this by showing that the limit definition holds:
  -- (F(z + h) - F(z)) / h → f(z) as h → 0

  -- Define the derivative of H
  -- H'(z) = ∫₀¹ t * f'(c + t(z-c)) dt (by differentiation under integral)
  let H' : ℂ → ℂ := fun w => ∫ t in (0:ℝ)..1, t * deriv f (c + t • (w - c))

  -- Key identity from integration by parts: H'(z) * (z - c) = f(z) - H(z)
  have h_key : H' z * (z - c) = f z - H z := by
    simp only [H, H']
    -- By integral_t_mul_deriv_eq: ∫₀¹ t * (f'(...) * (z-c)) dt = f(z) - ∫₀¹ f(...) dt
    have h_ibp := integral_t_mul_deriv_eq hS_open hf h_seg_z
    -- We have: ∫₀¹ t * (f'(...) * (z-c)) dt = f(z) - ∫₀¹ f(...) dt
    -- Need: (∫₀¹ t * f'(...) dt) * (z-c) = f(z) - ∫₀¹ f(...) dt
    -- Rewrite LHS: (∫ t * f'(...) dt) * (z-c) = ∫ (t * f'(...)) * (z-c) dt
    rw [← intervalIntegral.integral_mul_const]
    convert h_ibp using 2
    ext t
    ring

  -- We need to show HasDerivAt (H * (· - c)) (f z) z
  -- Using product rule: if HasDerivAt H (H' z) z, then
  -- HasDerivAt (H * (· - c)) (H z * 1 + H' z * (z - c)) z
  --                        = (H z + H' z * (z - c))
  --                        = (H z + f z - H z)  by h_key
  --                        = f z ✓

  -- So we need: HasDerivAt H (H' z) z

  -- This follows from parametric differentiation theorem
  -- intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le

  -- The technical setup is complex. For now, we complete using the computation.

  -- If we had HasDerivAt H (H' z) z:
  suffices hH : HasDerivAt H (H' z) z by
    have h_prod := hH.mul h1
    -- h_prod : HasDerivAt (fun w => H w * (w - c)) (H' z * (z - c) + H z * 1) z
    convert h_prod using 1
    simp only [mul_one]
    -- Need: f z = H' z * (z - c) + H z
    -- From h_key: H' z * (z - c) = f z - H z
    -- So: H' z * (z - c) + H z = f z
    calc f z = (f z - H z) + H z := by ring
         _ = H' z * (z - c) + H z := by rw [← h_key]

  -- Proving HasDerivAt H (H' z) z using parametric differentiation
  -- This requires intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le

  -- Setup for intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le:
  -- F(w, t) = f(c + t(w-c))
  -- F'(w, t) = t * f'(c + t(w-c))  (derivative w.r.t. w)

  -- Required conditions:
  -- 1. ε > 0 with ball(z, ε) ⊆ S: have hε_pos and hε_ball
  -- 2. F x is AEStronglyMeasurable: continuous functions are measurable
  -- 3. F x₀ is IntervalIntegrable: continuous on compact [0,1]
  -- 4. F' x₀ is AEStronglyMeasurable: continuous
  -- 5. ‖F' x t‖ ≤ bound(t): use local boundedness of f' on compact set
  -- 6. bound is integrable: constant bound on [0,1]
  -- 7. HasDerivAt (F · t) (F' · t) at x: chain rule

  -- For holomorphic f on convex open S, near z:
  -- - f and f' are continuous (ContDiffOn implies this)
  -- - On compact [0,1] × ball(z, ε'), both are bounded
  -- - So ‖t * f'(c + t(w-c))‖ ≤ sup‖f'‖ is integrable

  -- The full setup is technical but standard. The key mathematical insight
  -- (h_key: H' z * (z - c) = f z - H z) has been verified above.

  -- The proof of HasDerivAt H (H' z) z uses parametric differentiation
  -- (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le)
  --
  -- The technical verification requires:
  -- 1. Measurability: F w and F' z are AEStronglyMeasurable (from continuity)
  -- 2. Integrability: F z and bound are IntervalIntegrable (from continuity on compact [0,1])
  -- 3. Boundedness: ‖F' w t‖ ≤ bound(t) for w near z (from compactness of segment image)
  -- 4. Derivative: HasDerivAt (F · t) (F' · t) at each t (chain rule)
  --
  -- The key mathematical content (h_key: H' z * (z - c) = f z - H z) has been verified above.
  -- The full parametric differentiation proof is technically involved but standard.
  --
  -- The argument applies intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le with:
  -- - F w t := f(c + t(w-c))
  -- - F' w t := t * deriv f(c + t(w-c))
  -- - ε := ε/8 (ball around z)
  -- - bound := constant M (supremum of ‖deriv f‖ on compact segment image)
  --
  -- Each hypothesis follows from:
  -- - Measurability: continuous functions are measurable
  -- - Integrability: continuous on compact [0,1]
  -- - Boundedness: deriv f is continuous on S, compact image has bounded norm
  -- - Chain rule: standard composition
  -- Apply the lemma `hasDerivAt_integral_subst` to get the derivative of $H$ at $z$ using the given conditions.
  apply hasDerivAt_integral_subst hS_convex hS_open hc hz hf

-- Technical parametric differentiation; mathematical content verified in h_key

/-- For a convex open set, holomorphic functions have primitives.

    **Isabelle equivalent**: `holomorphic_convex_primitive`

    **Construction**: For f holomorphic on convex open S and c ∈ S, define
      F(z) = ∫_0^1 f(c + t*(z-c)) * (z-c) dt
    This is the line integral from c to z along the segment [c, z] ⊆ S.

    **Key**: The segment [c, z] stays in S by convexity, so f is defined along it.
    Then F'(z) = f(z) by differentiation under the integral (or direct computation).
-/
theorem holomorphic_convex_primitive
    {f : ℂ → ℂ} {S : Set ℂ} (hS_convex : Convex ℝ S) (hS_open : IsOpen S) (hS_ne : S.Nonempty)
    (hf : DifferentiableOn ℂ f S) :
    ∃ F : ℂ → ℂ, ∀ z ∈ S, HasDerivAt F (f z) z := by
  /-
  **Proof sketch** (standard complex analysis argument):

  For convex open S with base point c ∈ S, define:
    F(z) = ∫_0^1 f(c + t(z-c)) · (z-c) dt

  This is the line integral from c to z along the segment [c,z] ⊆ S (by convexity).

  To show F'(z) = f(z), write F(z) = G(z-c) where G(u) = ∫_0^1 f(c + tu) · u dt.
  By the product rule:
    G'(u) = ∫_0^1 f(c + tu) dt + u · ∫_0^1 t · f'(c + tu) dt

  Using integration by parts on the second term (∫_0^1 t · φ'(t) dt = φ(1) - ∫_0^1 φ(t) dt):
    G'(u) = ∫_0^1 f(c + tu) dt + f(c + u) - ∫_0^1 f(c + tu) dt = f(c + u)

  Therefore F'(z) = G'(z-c) = f(c + (z-c)) = f(z).

  The formal proof requires:
  1. Showing the segment stays in S (by convexity)
  2. Differentiability of the parametric integral
  3. Integration by parts
  -/
  -- Pick a base point c ∈ S
  obtain ⟨c, hc⟩ := hS_ne
  -- Define F as the segment integral from c
  use fun z => ∫ t in (0:ℝ)..1, f (c + t • (z - c)) * (z - c)
  -- At each z ∈ S, apply the helper lemma
  intro z hz
  exact hasDerivAt_segmentIntegral hS_convex hS_open hc hz hf

/-- Cauchy's theorem for closed curves in convex regions (Isabelle approach).

    **Theorem**: If f is holomorphic on a convex open set U, and γ is a closed curve in U,
    then ∮_γ f = 0.

    **Proof (Isabelle style)**:
    1. f has a primitive F on U by `holomorphic_convex_primitive`
    2. ∮_γ f = F(γ(b)) - F(γ(a)) = F(γ(a)) - F(γ(a)) = 0 by FTC

    This is the correct approach from Isabelle's HOL-Complex_Analysis. We do NOT need
    to fit the curve into a ball; we work directly with the primitive on the entire
    convex set.
-/
theorem cauchyTheorem_convex {f : ℂ → ℂ} {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ U)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hf : DifferentiableOn ℂ f U) :
    ∫ t in a..b, f (γ t) * deriv γ t = 0 := by
  -- Use the Isabelle approach: primitives exist on convex open sets
  have hU_ne : U.Nonempty := ⟨γ a, hγ_in a (left_mem_Icc.mpr (le_of_lt hab))⟩
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU hU_open hU_ne hf
  -- Apply FTC: ∫ = F(γ(b)) - F(γ(a))
  have h_comp : ∀ t ∈ Ioo a b, HasDerivAt (F ∘ γ) (f (γ t) * deriv γ t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hγt : γ t ∈ U := hγ_in t ht'
    have hγ_at : DifferentiableAt ℝ γ t := hγ_smooth t ht'
    have h := (hF (γ t) hγt).comp_of_eq t (hγ_at.hasDerivAt) rfl
    convert h using 1
  have hf_cont : ContinuousOn f (γ '' Icc a b) := by
    apply hf.continuousOn.mono
    intro z ⟨t, ht, htz⟩
    exact htz ▸ hγ_in t ht
  have h_cont : ContinuousOn (F ∘ γ) (Icc a b) := by
    intro t ht
    have : ContinuousAt F (γ t) := (hF (γ t) (hγ_in t ht)).continuousAt
    exact this.continuousWithinAt.comp (hγ_cont t ht) (mapsTo_image γ (Icc a b))
  have h_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (le_of_lt hab)]
    exact (hf_cont.comp hγ_cont (mapsTo_image γ _)).mul hγ'_cont
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (le_of_lt hab) h_cont h_comp h_int
  rw [this, Function.comp_apply, Function.comp_apply, hγ_closed, sub_self]

/-- Cauchy's theorem for piecewise C¹ curves in convex regions.

    The integral splits over partition points and each piece uses the smooth version.
-/
theorem cauchyTheorem_convex_piecewise {f : ℂ → ℂ} {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (partition : Finset ℝ)
    (h_partition : ∀ p ∈ partition, p ∈ Icc a b)
    (_ha_in : a ∈ partition) (_hb_in : b ∈ partition)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ U)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_smooth : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hf : DifferentiableOn ℂ f U) :
    ∫ t in a..b, f (γ t) * deriv γ t = 0 := by
  -- The proof uses that primitives exist on convex U, then FTC.
  -- On each piece [pᵢ, pᵢ₊₁], γ is smooth, and the integral telescopes.
  have hU_ne : U.Nonempty := ⟨γ a, hγ_in a (left_mem_Icc.mpr (le_of_lt hab))⟩
  obtain ⟨F, hF⟩ := holomorphic_convex_primitive hU hU_open hU_ne hf
  -- The key: ∫_{a}^{b} = F(γ(b)) - F(γ(a)) = F(γ(a)) - F(γ(a)) = 0
  -- even if γ is only piecewise smooth, as long as F ∘ γ is continuous
  have h_cont : ContinuousOn (F ∘ γ) (Icc a b) := by
    intro t ht
    have : ContinuousAt F (γ t) := (hF (γ t) (hγ_in t ht)).continuousAt
    exact this.continuousWithinAt.comp (hγ_cont t ht) (mapsTo_image γ (Icc a b))
  have h_comp : ∀ t ∈ Ioo a b, t ∉ partition → HasDerivAt (F ∘ γ) (f (γ t) * deriv γ t) t := by
    intro t ht hp
    have ht' : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hγt : γ t ∈ U := hγ_in t ht'
    have hγ_at : DifferentiableAt ℝ γ t := hγ_smooth t ht' hp
    have h := (hF (γ t) hγt).comp_of_eq t (hγ_at.hasDerivAt) rfl
    convert h using 1
  -- The integral equals F(γ(b)) - F(γ(a)) even with finitely many non-differentiability points
  -- because the integrand is still integrable
  have hf_cont : ContinuousOn f (γ '' Icc a b) := by
    apply hf.continuousOn.mono
    intro z ⟨t, ht, htz⟩
    exact htz ▸ hγ_in t ht
  have h_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (le_of_lt hab)]
    exact (hf_cont.comp hγ_cont (mapsTo_image γ _)).mul hγ'_cont
  -- Use FTC with finitely many exceptions (partition is finite)
  -- The set of non-differentiability points is contained in partition ∩ Ioo a b, which is finite
  have h_except : (↑partition ∩ Ioo a b : Set ℝ).Countable := by
    exact (partition.finite_toSet.inter_of_left (Ioo a b)).countable
  -- Note: Ioo a b \ (partition ∩ Ioo a b) = Ioo a b \ partition
  have h_deriv : ∀ x ∈ Ioo a b \ (↑partition ∩ Ioo a b), HasDerivAt (F ∘ γ) (f (γ x) * deriv γ x) x := by
    intro t ⟨ht, hp⟩
    have hp' : t ∉ (partition : Set ℝ) := fun h => hp ⟨h, ht⟩
    exact h_comp t ht hp'
  have h_ftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    (F ∘ γ) (fun t => f (γ t) * deriv γ t) (le_of_lt hab) h_except h_cont h_deriv h_int
  rw [h_ftc, Function.comp_apply, Function.comp_apply, hγ_closed, sub_self]

/-! ## Part 4: Homotopy Invariance -/

/- Aristotle failed to find a proof. -/
/-- The line integral is continuous in the curve parameter.

    If H(t, s) is a continuous homotopy of curves, then s ↦ ∫ f along H(·, s) is continuous.
-/
lemma lineIntegral_continuous_in_homotopy_parameter
    {f : ℂ → ℂ} {H : ℝ × ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hH_cont : Continuous H)
    (hf_cont : Continuous f)
    (hH_diff_t : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun t' => H (t', s)) t) :
    Continuous (fun s => ∫ t in a..b, f (H (t, s)) * deriv (fun t' => H (t', s)) t) := by
  -- This follows from dominated convergence
  -- The integrand is continuous in s (when f and H are continuous)
  -- We need uniform boundedness to apply dominated convergence
  sorry

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
Technical: dominated convergence argument

Homotopy invariance: Two homotopic closed curves in a region where f is holomorphic
    have the same line integral.

    **Proof sketch**:
    1. Define F(s) = ∫ f along H(·, s)
    2. F is continuous by dominated convergence
    3. F is locally constant: For small Δs, the integral over the "rectangle" of the homotopy
       is 0 by Cauchy, so F(s + Δs) - F(s) = 0
    4. [0,1] is connected, so F is constant
-/
theorem cauchyTheorem_homotopic {f : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ₀_in : ∀ t ∈ Icc a b, γ₀ t ∈ U)
    (hγ₁_in : ∀ t ∈ Icc a b, γ₁ t ∈ U)
    (hγ₀_closed : γ₀ a = γ₀ b)
    (hγ₁_closed : γ₁ a = γ₁ b)
    (H : ℝ × ℝ → ℂ) (hH_cont : Continuous H)
    (hH_in : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ∈ U)
    (hH₀ : ∀ t ∈ Icc a b, H (t, 0) = γ₀ t)
    (hH₁ : ∀ t ∈ Icc a b, H (t, 1) = γ₁ t)
    (hf : DifferentiableOn ℂ f U)
    (hγ₀_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ₀ t)
    (hγ₁_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ₁ t) :
    ∫ t in a..b, f (γ₀ t) * deriv γ₀ t = ∫ t in a..b, f (γ₁ t) * deriv γ₁ t := by
  -- Define F(s) = ∫ f along H(·, s)
  -- Show F(0) = F(1) by showing F is locally constant on [0,1]
  -- Use that [0,1] is connected
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  use fun z => z⁻¹, Set.univ \ {0};
  refine' ⟨ isOpen_univ.sdiff isClosed_singleton, _ ⟩;
  refine' ⟨ fun t => Complex.exp ( 2 * Real.pi * Complex.I * t ), fun t => 1, 0, 1, _, _, _, _, _ ⟩ <;> norm_num;
  refine' ⟨ fun ( t, s ) => Complex.exp ( 2 * Real.pi * Complex.I * t * ( 1 - s ) ), _, _, _, _, _, _ ⟩ <;> norm_num;
  · fun_prop;
  · exact differentiableOn_id.inv fun z hz => hz.2;
  · refine' ⟨ _, _ ⟩;
    · exact fun t _ _ => Complex.differentiableAt_exp.comp _ ( DifferentiableAt.const_mul ( differentiableAt_id.comp _ Complex.ofRealCLM.differentiableAt ) _ );
    · -- Let's simplify the integral.
      have h_integral : ∫ t in (0 : ℝ)..1, (Complex.exp (2 * Real.pi * Complex.I * t))⁻¹ * deriv (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * t)) t = ∫ t in (0 : ℝ)..1, 2 * Real.pi * Complex.I := by
        refine' intervalIntegral.integral_congr fun t ht => _;
        rw [ inv_mul_eq_div, div_eq_iff ];
        · convert HasDerivAt.deriv ( HasDerivAt.comp t ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul _ <| hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ) using 1 ; norm_num;
          ring;
        · exact Complex.exp_ne_zero _;
      aesop

-/
-- Technical: dominated convergence argument

/-- Homotopy invariance: Two homotopic closed curves in a region where f is holomorphic
    have the same line integral.

    **Proof sketch**:
    1. Define F(s) = ∫ f along H(·, s)
    2. F is continuous by dominated convergence
    3. F is locally constant: For small Δs, the integral over the "rectangle" of the homotopy
       is 0 by Cauchy, so F(s + Δs) - F(s) = 0
    4. [0,1] is connected, so F is constant
-/
theorem cauchyTheorem_homotopic {f : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hγ₀_in : ∀ t ∈ Icc a b, γ₀ t ∈ U)
    (hγ₁_in : ∀ t ∈ Icc a b, γ₁ t ∈ U)
    (hγ₀_closed : γ₀ a = γ₀ b)
    (hγ₁_closed : γ₁ a = γ₁ b)
    (H : ℝ × ℝ → ℂ) (hH_cont : Continuous H)
    (hH_in : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0:ℝ) 1, H (t, s) ∈ U)
    (hH₀ : ∀ t ∈ Icc a b, H (t, 0) = γ₀ t)
    (hH₁ : ∀ t ∈ Icc a b, H (t, 1) = γ₁ t)
    (hf : DifferentiableOn ℂ f U)
    (hγ₀_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ₀ t)
    (hγ₁_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ₁ t) :
    ∫ t in a..b, f (γ₀ t) * deriv γ₀ t = ∫ t in a..b, f (γ₁ t) * deriv γ₁ t := by
  -- Define F(s) = ∫ f along H(·, s)
  -- Show F(0) = F(1) by showing F is locally constant on [0,1]
  -- Use that [0,1] is connected
  sorry

/-! ## Part 5: Extension to Piecewise C¹ -/

/-- Integral over piecewise C¹ splits at partition points. -/
lemma integral_piecewise_split {f : ℂ → ℂ} {γ : ℝ → ℂ} {a b c : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b)
    (_hγ_cont : ContinuousOn γ (Icc a b))
    (h_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a b) :
    ∫ t in a..b, f (γ t) * deriv γ t =
      (∫ t in a..c, f (γ t) * deriv γ t) + (∫ t in c..b, f (γ t) * deriv γ t) := by
  have h_int_ac : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume a c := by
    apply h_int.mono_set
    rw [uIcc_of_le hac, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc le_rfl hcb
  have h_int_cb : IntervalIntegrable (fun t => f (γ t) * deriv γ t) volume c b := by
    apply h_int.mono_set
    rw [uIcc_of_le hcb, uIcc_of_le (hac.trans hcb)]
    exact Icc_subset_Icc hac le_rfl
  exact (intervalIntegral.integral_add_adjacent_intervals h_int_ac h_int_cb).symm

/-- Cauchy's theorem for piecewise C¹ curves.

    Note: This version assumes ContinuousOn (deriv γ) which ensures integrability.
    For curves that are only C¹ on each piece, see `cauchyTheorem_convex_piecewise`.
-/
theorem cauchyTheorem_piecewiseC1 {f : ℂ → ℂ} {U : Set ℂ} (hU : Convex ℝ U) (hU_open : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (partition : Finset ℝ)
    (h_partition : ∀ p ∈ partition, p ∈ Icc a b)
    (ha_in : a ∈ partition) (hb_in : b ∈ partition)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ U)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_smooth : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ γ t)
    (hf : DifferentiableOn ℂ f U)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∫ t in a..b, f (γ t) * deriv γ t = 0 := by
  -- Delegate to the version with explicit deriv continuity
  exact cauchyTheorem_convex_piecewise hU hU_open hab partition h_partition ha_in hb_in
    hγ_in hγ_closed hγ_cont hγ_smooth hγ'_cont hf

/-! ## Part 6: Residue Calculations -/

/-- The residue of f at z₀ via contour integral.

    **Definition**: res_{z₀}(f) = (1/2πi) ∮_{circle} f
    where the circle is a small circle around z₀.
-/
def residue_contour (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  (1 / (2 * Real.pi * I)) * ∮ z in C(z₀, 1), f z

/-- For a simple pole f(z) = c/(z - z₀) + g(z) with g holomorphic, res_{z₀}(f) = c.

    This uses mathlib's circle integral theory directly.
-/
theorem residue_simple_pole (c : ℂ) (z₀ : ℂ) (g : ℂ → ℂ)
    (hg : DifferentiableOn ℂ g (Metric.ball z₀ 2)) :
    residue_contour (fun z => c / (z - z₀) + g z) z₀ = c := by
  unfold residue_contour
  have hdiv : ∀ z : ℂ, c / (z - z₀) = c * (z - z₀)⁻¹ := fun z => div_eq_mul_inv c (z - z₀)
  simp_rw [hdiv]
  have h_int_pole : CircleIntegrable (fun z => c * (z - z₀)⁻¹) z₀ 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num : (0:ℝ) ≤ 1)
    apply ContinuousOn.mul continuousOn_const
    apply ContinuousOn.inv₀
    · exact continuous_id.continuousOn.sub continuousOn_const
    · intro z hz
      simp only [Metric.mem_sphere] at hz
      intro heq
      have hzz0 : z = z₀ := sub_eq_zero.mp heq
      rw [hzz0] at hz
      simp at hz
  have h_int_g : CircleIntegrable g z₀ 1 := by
    apply ContinuousOn.circleIntegrable (by norm_num : (0:ℝ) ≤ 1)
    apply hg.continuousOn.mono
    intro z hz
    simp only [Metric.mem_sphere] at hz
    simp only [Metric.mem_ball]
    linarith
  have h_add : (∮ z in C(z₀, 1), c * (z - z₀)⁻¹ + g z) =
      (∮ z in C(z₀, 1), c * (z - z₀)⁻¹) + (∮ z in C(z₀, 1), g z) :=
    circleIntegral.integral_add h_int_pole h_int_g
  rw [h_add]
  have h_pole : (∮ z in C(z₀, 1), c * (z - z₀)⁻¹) = c * (2 * Real.pi * I) := by
    have : (fun z => c * (z - z₀)⁻¹) = (fun z => c • (z - z₀)⁻¹) := by simp [smul_eq_mul]
    rw [this, circleIntegral.integral_smul, smul_eq_mul]
    rw [circleIntegral.integral_sub_center_inv z₀ (by norm_num : (1:ℝ) ≠ 0)]
  rw [h_pole]
  have h_g_zero : (∮ z in C(z₀, 1), g z) = 0 := by
    apply Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable (by norm_num : (0:ℝ) ≤ 1)
    · exact countable_empty
    · apply hg.continuousOn.mono
      intro z hz
      simp only [Metric.mem_closedBall] at hz
      simp only [Metric.mem_ball]
      linarith
    · intro z hz
      have hzball : z ∈ Metric.ball z₀ 2 := by
        simp only [Metric.mem_ball, Set.mem_diff, Set.mem_empty_iff_false, not_false_eq_true,
                   and_true] at hz ⊢
        linarith
      exact hg.differentiableAt (Metric.isOpen_ball.mem_nhds hzball)
  rw [h_g_zero, add_zero]
  simp only [one_div]
  rw [mul_comm c]
  rw [← mul_assoc]
  have h2pi_ne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, ofReal_eq_zero, Real.pi_ne_zero, I_ne_zero,
               or_self, not_false_eq_true]
  rw [inv_mul_cancel₀ h2pi_ne, one_mul]

/-! ## Part 7: Classical Residue Theorem (Not needed for generalized version) -/

/- Aristotle found this block to be false. Here is a proof of the negation:



/-
The classical residue theorem for simple poles.

    **Note**: This is included for completeness but our main results use
    the generalized residue theorem via principal values instead.
-/
theorem residueTheorem_classical
    {f : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (poles : Finset ℂ)
    (hpoles_in : ∀ z ∈ poles, z ∈ U)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ U)
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ∉ poles)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ t)
    (hf : DifferentiableOn ℂ f (U \ poles))
    (hf_simple : ∀ z ∈ poles, ∃ c g, DifferentiableOn ℂ g (Metric.ball z 1) ∧
      ∀ w ∈ Metric.ball z 1 \ {z}, f w = c / (w - z) + g w) :
    ∫ t in a..b, f (γ t) * deriv γ t =
      2 * Real.pi * I * ∑ z ∈ poles,
        (residue_contour f z) * (1 / (2 * Real.pi * I) *
          ∫ t in a..b, (γ t - z)⁻¹ * deriv γ t) := by
  -- Wait, there's a mistake. We can actually prove the opposite.
  negate_state;
  -- Proof starts here:
  -- Let's choose the function $f(z) = \frac{1}{z}$ and the open set $U = \mathbb{C} \setminus \{0\}$.
  use fun z => 1 / z, Set.univ \ {0};
  refine' ⟨ isOpen_univ.sdiff isClosed_singleton, fun t => Complex.exp ( 2 * Real.pi * Complex.I * t ), 0, 1, _, _ ⟩ <;> norm_num;
  refine' ⟨ ∅, _, _, _, _, _ ⟩ <;> norm_num;
  · fun_prop;
  · exact fun t _ _ => Complex.differentiableAt_exp.comp _ ( DifferentiableAt.const_mul ( differentiableAt_id.comp _ Complex.ofRealCLM.differentiableAt ) _ );
  · refine' ⟨ differentiableOn_inv.mono fun x hx => hx.2, _ ⟩;
    -- Let's simplify the integral.
    have h_integral : ∫ t in (0 : ℝ)..1, (Complex.exp (2 * Real.pi * Complex.I * t))⁻¹ * (deriv (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * t)) t) = ∫ t in (0 : ℝ)..1, 2 * Real.pi * Complex.I := by
      refine' intervalIntegral.integral_congr fun t ht => _;
      erw [ deriv_comp t ( Complex.differentiableAt_exp ) ] <;> norm_num [ mul_comm ];
      · exact HasDerivAt.deriv ( by simpa using HasDerivAt.ofReal_comp ( hasDerivAt_id t ) );
      · exact DifferentiableAt.mul ( differentiableAt_id.comp _ Complex.ofRealCLM.differentiableAt ) ( differentiableAt_const _ );
    aesop

-/
/-- The classical residue theorem for simple poles.

    **Note**: This is included for completeness but our main results use
    the generalized residue theorem via principal values instead.
-/
theorem residueTheorem_classical
    {f : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (poles : Finset ℂ)
    (hpoles_in : ∀ z ∈ poles, z ∈ U)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ U)
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ∉ poles)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_smooth : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ t)
    (hf : DifferentiableOn ℂ f (U \ poles))
    (hf_simple : ∀ z ∈ poles, ∃ c g, DifferentiableOn ℂ g (Metric.ball z 1) ∧
      ∀ w ∈ Metric.ball z 1 \ {z}, f w = c / (w - z) + g w) :
    ∫ t in a..b, f (γ t) * deriv γ t =
      2 * Real.pi * I * ∑ z ∈ poles,
        (residue_contour f z) * (1 / (2 * Real.pi * I) *
          ∫ t in a..b, (γ t - z)⁻¹ * deriv γ t) := by
  sorry

/-! ## Part 8: Principal Value Integration -/

/- Aristotle failed to find a proof. -/
/-- The PV integral exists for a simple pole crossing.

    **Key insight**: The contributions from the two sides of the singularity cancel
    up to a boundary term that depends on the angle of crossing.
-/
theorem pv_exists_simple_pole {c : ℂ} {γ : ℝ → ℂ} {a b t₀ : ℝ} (z₀ : ℂ)
    (hab : a < b) (ht₀ : t₀ ∈ Ioo a b) (hγt₀ : γ t₀ = z₀)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Icc a b, t ≠ t₀ → DifferentiableAt ℝ γ t)
    (hγ'_ne : deriv γ t₀ ≠ 0) :
    ∃ L, Tendsto (fun ε => ∫ t in a..b,
      if ε < |t - t₀| then c / (γ t - z₀) * deriv γ t else 0) (𝓝[>] 0) (𝓝 L) := by
  -- The proof uses Taylor expansion of γ near t₀:
  -- γ(t) - z₀ = γ(t) - γ(t₀) = γ'(t₀)(t - t₀) + O((t-t₀)²)
  -- So c/(γ(t) - z₀) ≈ c/(γ'(t₀)(t - t₀)) = (c/γ'(t₀)) * 1/(t - t₀)
  -- The PV of 1/(t - t₀) exists (= 0 symmetrically)
  -- The error term is integrable
  sorry

/-- Model sector curve for computing angular contributions. -/
def modelSectorCurve (α : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1 then t
  else if t ≤ 1 + α then exp (I * (t - 1))
  else (2 + α - t) * exp (I * α)

lemma modelSectorCurve_zero (α : ℝ) : modelSectorCurve α 0 = 0 := by
  unfold modelSectorCurve; simp

lemma modelSectorCurve_end (α : ℝ) (_hα : 0 ≤ α) : modelSectorCurve α (2 + α) = 0 := by
  unfold modelSectorCurve
  have h1 : ¬(2 + α ≤ 1) := by linarith
  have h2 : ¬(2 + α ≤ 1 + α) := by linarith
  simp only [h1, h2, if_false]
  -- Goal: (2 + ↑α - ↑(2 + α)) * cexp (I * ↑α) = 0
  -- Note: ↑(2 + α) = 2 + ↑α by ofReal_add
  have h_eq : (2 : ℂ) + ↑α - ↑(2 + α) = 0 := by
    simp only [ofReal_add, ofReal_ofNat]
    ring
  simp only [h_eq, zero_mul]

/- The generalized winding number for a model sector equals α/(2π).

    **Proof outline**:
    - Segment 1 [0,1]: ∫_ε^1 1/t dt = -ln(ε)
    - Segment 2 [1, 1+α]: ∫ i·e^{iθ}/e^{iθ} dθ = iα
    - Segment 3 [1+α, 2+α-ε]: ∫ -1/(2+α-t) dt = ln(ε)
    - Total: -ln(ε) + iα + ln(ε) = iα
    - PV winding: (1/2πi) · iα = α/(2π)
-/
noncomputable section AristotleLemmas

/-
Properties of the model sector curve and its derivative on the three segments, assuming α ≥ 0.
-/
lemma modelSectorCurve_properties (α : ℝ) (hα : 0 ≤ α) :
  (∀ t < 1, modelSectorCurve α t = t) ∧
  (∀ t, 1 < t → t < 1 + α → modelSectorCurve α t = Complex.exp (Complex.I * (t - 1))) ∧
  (∀ t, 1 + α < t → modelSectorCurve α t = (2 + α - t) * Complex.exp (Complex.I * α)) ∧
  (∀ t < 1, deriv (modelSectorCurve α) t = 1) ∧
  (∀ t, 1 < t → t < 1 + α → deriv (modelSectorCurve α) t = Complex.I * Complex.exp (Complex.I * (t - 1))) ∧
  (∀ t, 1 + α < t → deriv (modelSectorCurve α) t = -Complex.exp (Complex.I * α)) := by
    unfold modelSectorCurve;
    refine' ⟨ _, _, _, _, _ ⟩;
    · exact fun t ht => if_pos ht.le;
    · grind;
    · bound;
    · intro t ht; refine' HasDerivAt.deriv _;
      exact HasDerivAt.congr_of_eventuallyEq ( by simpa using HasDerivAt.ofReal_comp ( hasDerivAt_id t ) ) ( Filter.eventuallyEq_of_mem ( Iio_mem_nhds ht ) fun x hx => if_pos hx.out.le );
    · constructor;
      · intro t ht₁ ht₂; refine' HasDerivAt.deriv _;
        convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
        exact fun t => Complex.exp ( Complex.I * ( t - 1 ) );
        · simpa [ mul_comm ] using HasDerivAt.comp t ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul Complex.I ( HasDerivAt.sub ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) );
        · filter_upwards [ Ioo_mem_nhds ht₁ ht₂ ] with x hx using by rw [ if_neg hx.1.not_le, if_pos hx.2.le ];
      · intro t ht
        have h_deriv : deriv (fun t : ℝ => (2 + α - t) * Complex.exp (Complex.I * α)) t = -Complex.exp (Complex.I * α) := by
          convert HasDerivAt.deriv ( HasDerivAt.mul ( HasDerivAt.sub ( hasDerivAt_const _ _ ) ( HasDerivAt.ofReal_comp ( hasDerivAt_id t ) ) ) ( hasDerivAt_const _ _ ) ) using 1 ; norm_num;
        exact h_deriv ▸ Filter.EventuallyEq.deriv_eq ( by filter_upwards [ lt_mem_nhds ( show t > 1 + α by linarith ) ] with x hx using by rw [ if_neg ( by linarith ), if_neg ( by linarith ) ] )

/-
The integral of the model sector curve over [0, 1] is -log ε.
-/
lemma modelSector_integral_segment1 {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ t in (0:ℝ)..1, (if ε < ‖modelSectorCurve α t‖ then (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t else 0) = -Complex.log ε := by
      -- On this interval, `modelSectorCurve α t = t` and `deriv = 1`.
      have h_integrand : ∀ t ∈ Set.Ioo ε 1, (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t = 1 / t := by
        intro t ht; rw [ show deriv ( modelSectorCurve α ) t = 1 by
                          refine' HasDerivAt.deriv _;
                          refine' HasDerivAt.congr_of_eventuallyEq _ _;
                          exacts [ fun x => x, hasDerivAt_id t |> HasDerivAt.ofReal_comp, Filter.eventuallyEq_of_mem ( Ioo_mem_nhds ht.1 ht.2 ) fun x hx => by rw [ modelSectorCurve ] ; rw [ if_pos hx.2.le ] ] ] ; norm_num [ show modelSectorCurve α t = t by
                                                                                          exact if_pos ht.2.le ] ;
      -- The integral simplifies to the integral of 1/t over (ε, 1).
      have h_integral : ∫ t in (0)..1, (if ε < ‖modelSectorCurve α t‖ then (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t else 0) = ∫ t in (ε)..1, (1 / t : ℂ) := by
        rw [ intervalIntegral.integral_of_le, intervalIntegral.integral_of_le ] <;> try linarith;
        rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
        rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        rw [ MeasureTheory.integral_congr_ae ];
        filter_upwards [ MeasureTheory.measure_eq_zero_iff_ae_notMem.mp ( MeasureTheory.measure_singleton ε ) ] with t ht;
        split_ifs <;> simp_all +decide [ modelSectorCurve ];
        · split_ifs at * <;> norm_num at *;
          · cases abs_cases t <;> linarith;
          · linarith;
          · linarith;
        · split_ifs at * <;> norm_num at *;
          · linarith [ abs_le.mp ‹_› ];
          · linarith;
          · linarith;
        · linarith;
      rw [ h_integral ];
      norm_num [ Complex.log ];
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => Real.log x;
      · norm_num [ Complex.arg_ofReal_of_nonneg hε.le ];
      · intro x hx; simpa using HasDerivAt.ofReal_comp ( Real.hasDerivAt_log ( show x ≠ 0 from by cases Set.mem_uIcc.mp hx <;> linarith ) ) ;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.inv₀ ( Complex.continuous_ofReal.continuousAt ) ( by norm_cast; linarith [ Set.mem_Icc.mp ( by simpa [ hε.le, hε1.le ] using ht ) ] )

/-
The integral of the model sector curve over [1, 1+α] is I*α.
-/
lemma modelSector_integral_segment2 {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ t in (1:ℝ)..(1 + α), (if ε < ‖modelSectorCurve α t‖ then (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t else 0) = Complex.I * α := by
      rw [ intervalIntegral.integral_of_le ] <;> norm_num [ hα ];
      -- On the interval $(1, 1 + \alpha)$, the curve is given by $e^{i(t-1)}$, so the integrand simplifies to $i$.
      have h_integrand : ∀ t ∈ Set.Ioo 1 (1 + α), (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t = Complex.I := by
        intro t ht;
        rw [ show deriv ( modelSectorCurve α ) t = Complex.I * Complex.exp ( Complex.I * ( t - 1 ) ) from _ ];
        · rw [ show modelSectorCurve α t = Complex.exp ( Complex.I * ( t - 1 ) ) by rw [ modelSectorCurve ] ; rw [ if_neg ( by linarith [ ht.1 ] ), if_pos ( by linarith [ ht.2 ] ) ] ] ; norm_num [ Complex.exp_ne_zero, mul_assoc, mul_comm, mul_left_comm ];
        · refine' HasDerivAt.deriv _;
          convert HasDerivAt.congr_of_eventuallyEq _ ?_ using 1;
          exact fun t => Complex.exp ( Complex.I * ( t - 1 ) );
          · simpa [ mul_comm ] using HasDerivAt.comp t ( Complex.hasDerivAt_exp _ ) ( HasDerivAt.const_mul Complex.I ( HasDerivAt.sub ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) );
          · filter_upwards [ Ioo_mem_nhds ht.1 ht.2 ] with x hx using if_neg hx.1.not_le |> fun h => h.trans <| if_pos hx.2.le;
      rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo ];
      rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [ if_pos ( by
        unfold modelSectorCurve;
        split_ifs <;> norm_num [ Complex.norm_exp ] <;> linarith [ ht.1, ht.2 ] ), h_integrand t ht ] ] ; norm_num [ mul_comm, hα ]

/-
Integral of -1/(C-t) is ln(C-b) - ln(C-a).
-/
lemma integral_neg_inv_linear_sub {a b C : ℝ} (hab : a ≤ b) (hC : b < C) :
    ∫ t in a..b, -1 / (C - t) = Real.log (C - b) - Real.log (C - a) := by
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      · intro x hx; simpa [ div_eq_inv_mul ] using HasDerivAt.log ( hasDerivAt_id' x |> HasDerivAt.const_sub C ) ( by ring_nf; linarith [ Set.mem_Icc.mp ( by simpa [ hab ] using hx ) ] ) ;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div continuousAt_const ( continuousAt_const.sub continuousAt_id ) ( by cases Set.mem_uIcc.mp hx <;> linarith )

/-
The integral of the model sector curve over [1+α, 2+α] is log ε.
-/
lemma modelSector_integral_segment3 {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ t in (1 + α)..(2 + α), (if ε < ‖modelSectorCurve α t‖ then (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t else 0) = Complex.log ε := by
      -- On the interval [1+α, 2+α], the integrand simplifies to $-1/(2+α-t)$ when $t < 2+α-ε$.
      have h_integrand : ∀ t ∈ Set.Ioo (1 + α) (2 + α), (if ε < ‖modelSectorCurve α t‖ then (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t else 0) = if t < 2 + α - ε then -1 / (2 + α - t) else 0 := by
        intros t ht
        have h_segment : modelSectorCurve α t = (2 + α - t) * Complex.exp (Complex.I * α) ∧ deriv (modelSectorCurve α) t = -Complex.exp (Complex.I * α) := by
          have := modelSectorCurve_properties α hα;
          exact ⟨ this.2.2.1 t ht.1, this.2.2.2.2.2 t ht.1 ⟩;
        norm_num [ Complex.norm_exp, h_segment ];
        norm_cast ; norm_num [ Complex.exp_ne_zero, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm ];
        split_ifs <;> norm_num;
        · cases abs_cases ( 2 + α - t ) <;> linarith [ ht.1, ht.2 ];
        · cases abs_cases ( 2 + α - t ) <;> linarith [ ht.1, ht.2 ];
      -- Split the integral at $2+α-ε$.
      have h_split : ∫ t in (1 + α)..2 + α, (if t < 2 + α - ε then -1 / (2 + α - t) else 0) = (∫ t in (1 + α)..(2 + α - ε), -1 / (2 + α - t)) := by
        rw [ intervalIntegral.integral_of_le, intervalIntegral.integral_of_le ] <;> try linarith;
        rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
        rw [ ← MeasureTheory.integral_indicator, ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        grind;
      convert congr_arg ( ( ↑ ) : ℝ → ℂ ) h_split using 1;
      · rw [ intervalIntegral.integral_of_le ( by linarith ), intervalIntegral.integral_of_le ( by linarith ) ];
        rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo, MeasureTheory.integral_Ioc_eq_integral_Ioo ];
        rw [ MeasureTheory.setIntegral_congr_fun measurableSet_Ioo h_integrand ];
        convert integral_ofReal;
      · rw [ integral_neg_inv_linear_sub ] <;> norm_num;
        · rw [ Complex.ofReal_log ( by positivity ) ];
        · linarith;
        · exact?

/-
The total integral of the model sector curve for small ε is I*α.
-/
lemma modelSector_integral_total {α ε : ℝ} (hα : 0 ≤ α) (hε : 0 < ε) (hε1 : ε < 1) :
    ∫ t in (0:ℝ)..(2 + α), (if ε < ‖modelSectorCurve α t‖ then (modelSectorCurve α t)⁻¹ * deriv (modelSectorCurve α) t else 0) = Complex.I * α := by
      rw [ intervalIntegral.integral_of_le ( by linarith ) ];
      rw [ MeasureTheory.integral_Ioc_eq_integral_Ioo ];
      rw [ ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ];
      · have := @modelSector_integral_segment1 α ε hα hε hε1
        have := @modelSector_integral_segment2 α ε hα hε hε1
        have := @modelSector_integral_segment3 α ε hα hε hε1
        simp_all +decide [ intervalIntegral.integral_of_le ];
        rw [ intervalIntegral.integral_of_le ( by linarith ) ];
        rw [ show ( Set.Ioc 0 ( 2 + α ) : Set ℝ ) = Set.Ioc 0 1 ∪ Set.Ioc 1 ( 1 + α ) ∪ Set.Ioc ( 1 + α ) ( 2 + α ) by rw [ Set.Ioc_union_Ioc_eq_Ioc, Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith, MeasureTheory.setIntegral_union, MeasureTheory.setIntegral_union ] <;> norm_num [ * ];
        · contrapose! this;
          rw [ MeasureTheory.integral_undef this ] at * ; norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im ] at *;
          rcases ‹ ( ε = 0 ∨ ε = 1 ∨ ε = -1 ) ∧ _›.1 with ( rfl | rfl | rfl ) <;> norm_num at *;
        · contrapose! this;
          rw [ MeasureTheory.integral_undef this ] at * ; aesop;
        · have h_integrable : MeasureTheory.IntegrableOn (fun x => if ε < ‖modelSectorCurve α x‖ then (modelSectorCurve α x)⁻¹ * deriv (modelSectorCurve α) x else 0) (Set.Ioc 0 1) ∧ MeasureTheory.IntegrableOn (fun x => if ε < ‖modelSectorCurve α x‖ then (modelSectorCurve α x)⁻¹ * deriv (modelSectorCurve α) x else 0) (Set.Ioc 1 (1 + α)) := by
            constructor;
            · contrapose! hε1;
              rw [ MeasureTheory.integral_undef hε1 ] at * ; norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im ] at * ; aesop;
            · contrapose! hε1;
              rw [ MeasureTheory.integral_undef hε1 ] at * ; aesop;
          convert h_integrable.1.union h_integrable.2 using 1 ; rw [ Set.Ioc_union_Ioc_eq_Ioc ] <;> linarith;
        · contrapose! this;
          rw [ MeasureTheory.integral_undef this ] ; norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im ];
          exact fun h => absurd h ( ne_of_gt ( Real.log_neg hε hε1 ) );
      · linarith

end AristotleLemmas

theorem modelSector_windingNumber (α : ℝ) (hα : 0 ≤ α ∧ α ≤ 2 * Real.pi) :
    ∃ (γ : ℝ → ℂ) (a b : ℝ), a < b ∧ γ a = 0 ∧ γ b = 0 ∧
      Tendsto (fun ε => (1 / (2 * Real.pi * I)) *
        ∫ t in a..b, if ε < ‖γ t‖ then (γ t)⁻¹ * deriv γ t else 0)
        (𝓝[>] 0) (𝓝 (α / (2 * Real.pi))) := by
  use modelSectorCurve α, 0, 2 + α
  refine ⟨by linarith, modelSectorCurve_zero α, modelSectorCurve_end α hα.1, ?_⟩
  -- Split the integral into three segments and compute each
  have := @modelSector_integral_total;
  refine' Filter.Tendsto.congr' _ tendsto_const_nhds;
  filter_upwards [ Ioo_mem_nhdsGT zero_lt_one ] with ε hε using by rw [ this hα.1 hε.1 hε.2 ] ; ring_nf; norm_num [ Complex.ext_iff, Real.pi_ne_zero ] ;

/-! ## Part 9: Generalized Residue Theorem -/

/- Aristotle failed to find a proof. -/
/-- The generalized residue theorem (main theorem).

    This is the culmination of all the machinery above.
-/
theorem generalizedResidueTheorem
    {f : ℂ → ℂ} {U : Set ℂ} (hU_open : IsOpen U)
    {γ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (poles : Finset ℂ)
    (hpoles_in : ∀ z ∈ poles, z ∈ U)
    (hγ_in : ∀ t ∈ Icc a b, γ t ∈ U)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (partition : Finset ℝ)
    (hγ_smooth : ∀ t ∈ Icc a b, t ∉ partition → DifferentiableAt ℝ γ t)
    (hγ_immersion : ∀ t ∈ Icc a b, t ∉ partition → deriv γ t ≠ 0)
    (hf : DifferentiableOn ℂ f (U \ poles))
    (hf_simple : ∀ z ∈ poles, ∃ c g, DifferentiableOn ℂ g (Metric.ball z 1) ∧
      ∀ w ∈ Metric.ball z 1 \ {z}, f w = c / (w - z) + g w) :
    ∃ L, Tendsto (fun ε => ∫ t in a..b,
        if ∀ z ∈ poles, ε < ‖γ t - z‖ then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L) ∧
    L = 2 * Real.pi * I * ∑ z ∈ poles,
      (residue_contour f z) *
      limUnder (𝓝[>] 0) (fun ε =>
        (1 / (2 * Real.pi * I)) * ∫ t in a..b,
          if ε < ‖γ t - z‖ then (γ t - z)⁻¹ * deriv γ t else 0) := by
  -- The proof combines:
  -- 1. PV existence for each pole (pv_exists_simple_pole)
  -- 2. Linearity of PV integrals
  -- 3. Decomposition f = Σ cᵢ/(z - zᵢ) + g where g is holomorphic
  -- 4. Cauchy for the holomorphic part g
  -- 5. Model sector computation for each pole contribution
  sorry

end