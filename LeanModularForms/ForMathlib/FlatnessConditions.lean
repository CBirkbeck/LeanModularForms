/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.FDeriv.Extend
import LeanModularForms.ForMathlib.Instances
import LeanModularForms.ForMathlib.PrincipalPart
import LeanModularForms.ForMathlib.WindingDecomposition

/-!
# Flatness Conditions for CPV Convergence (Definition 3.2)

Flatness of curves at crossing points and conditions (A')/(B) from
Hungerbuhler-Wasem ensuring Cauchy principal value convergence at higher-order poles.

## Main definitions

* `orthogonalProjectionComplex` -- projection of `w` onto direction `L` in `ℂ` as `ℝ²`
* `tangentDeviation` -- component of `w` orthogonal to direction `L`
* `IsFlatOfOrder` -- curve flatness of order `n` at a crossing (Definition 3.2)
* `SatisfiesConditionA'` -- variable-order flatness at each pole crossing
* `SatisfiesConditionB` -- angle/Laurent compatibility condition

## Main results

* `isFlatOfOrder_one` -- every piecewise C¹ immersion is flat of order 1
* `satisfiesConditionA'_of_simplePoles` -- condition A' automatic for simple poles
* `satisfiesConditionB_of_simplePoles` -- condition B automatic for simple poles
* `conditions_automatic_simple_poles` -- both conditions automatic for simple poles

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2, Definition 3.2 and Theorem 3.3
-/

open Complex Set Filter Topology Asymptotics
open scoped Real Interval

noncomputable section

variable {x y : ℂ}

/-- The orthogonal projection of `w` onto the real line spanned by `L` in `ℂ`,
where `ℂ` is viewed as `ℝ²`. Computes `(Re(w * conj L) / ‖L‖²) • L`. -/
def orthogonalProjectionComplex (w L : ℂ) : ℂ :=
  ((w * starRingEnd ℂ L).re / Complex.normSq L) • L

/-- The tangent deviation: the component of `w` orthogonal to direction `L`. -/
def tangentDeviation (w L : ℂ) : ℂ :=
  w - orthogonalProjectionComplex w L





/-- Projection of a real scalar multiple of `L` onto `L` is itself. -/
theorem orthogonalProjectionComplex_real_smul_self (c : ℝ) (L : ℂ) (hL : L ≠ 0) :
    orthogonalProjectionComplex (c • L) L = c • L := by
  have hns : Complex.normSq L ≠ 0 := (Complex.normSq_pos.mpr hL).ne'
  simp only [orthogonalProjectionComplex]
  have h_coeff : (c • L * starRingEnd ℂ L).re / Complex.normSq L = c := by
    rw [Complex.real_smul, mul_assoc, starRingEnd_apply]
    simp only [Complex.star_def, Complex.mul_conj, ← Complex.ofReal_mul, Complex.ofReal_re]
    exact mul_div_cancel_of_imp fun h => absurd h hns
  rw [h_coeff]

/-- Tangent deviation of a real scalar multiple of `L` vanishes. -/
theorem tangentDeviation_real_smul_self (c : ℝ) (L : ℂ) (hL : L ≠ 0) :
    tangentDeviation (c • L) L = 0 := by
  rw [tangentDeviation, orthogonalProjectionComplex_real_smul_self c L hL, sub_self]

/-- Tangent deviation is additive in the first argument. -/
theorem tangentDeviation_add (w₁ w₂ L : ℂ) :
    tangentDeviation (w₁ + w₂) L = tangentDeviation w₁ L + tangentDeviation w₂ L := by
  simp only [tangentDeviation, orthogonalProjectionComplex, add_mul, Complex.add_re, add_div]
  module

/-- Norm bound: `‖tangentDeviation w L‖ ≤ 2 * ‖w‖` for `L ≠ 0`. -/
theorem norm_tangentDeviation_le (w L : ℂ) (hL : L ≠ 0) :
    ‖tangentDeviation w L‖ ≤ 2 * ‖w‖ := by
  have hns : 0 < Complex.normSq L := Complex.normSq_pos.mpr hL
  unfold tangentDeviation orthogonalProjectionComplex
  suffices h : ‖((w * starRingEnd ℂ L).re / Complex.normSq L) • L‖ ≤ ‖w‖ by
    calc ‖w - _‖
        ≤ ‖w‖ + ‖((w * starRingEnd ℂ L).re / Complex.normSq L) • L‖ := norm_sub_le _ _
      _ ≤ ‖w‖ + ‖w‖ := by gcongr
      _ = 2 * ‖w‖ := by ring
  rw [norm_smul, Real.norm_eq_abs]
  calc |(w * starRingEnd ℂ L).re / Complex.normSq L| * ‖L‖
      ≤ (‖w‖ * ‖L‖ / Complex.normSq L) * ‖L‖ := by
        gcongr
        rw [abs_div, abs_of_pos hns]
        gcongr
        exact (Complex.abs_re_le_norm _).trans
          (by rw [norm_mul, starRingEnd_apply, norm_star])
    _ = ‖w‖ * (‖L‖ * ‖L‖ / Complex.normSq L) := by ring
    _ = ‖w‖ := by rw [Complex.norm_mul_self_eq_normSq L, div_self hns.ne', mul_one]

/-- A curve `γ` is **flat of order `n`** at parameter `t₀` if:
- From the right: the deviation from the right tangent is `o(‖γ(t) - γ(t₀)‖ⁿ)`.
- From the left: the deviation from the left tangent is `o(‖γ(t) - γ(t₀)‖ⁿ)`.

This captures Definition 3.2 from Hungerbuhler-Wasem. -/
structure IsFlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop where
  right_flat : ∀ L : ℂ, L ≠ 0 →
    Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L) →
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ n)
  left_flat : ∀ L : ℂ, L ≠ 0 →
    Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L) →
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ n)

/-- Flatness of order `m` implies flatness of order `n` for `n ≤ m`,
provided `γ` is continuous at `t₀` (so `‖γ(t) - γ(t₀)‖ → 0`). -/
theorem IsFlatOfOrder.of_le {γ : ℝ → ℂ} {t₀ : ℝ} {m n : ℕ}
    (h : IsFlatOfOrder γ t₀ m) (hmn : n ≤ m)
    (hγ_cont : ContinuousAt γ t₀) :
    IsFlatOfOrder γ t₀ n := by
  have h_le_one : ∀ᶠ t in 𝓝 t₀, ‖γ t - γ t₀‖ ≤ 1 := by
    have h_tend : Tendsto (fun t => ‖γ t - γ t₀‖) (𝓝 t₀) (𝓝 0) := by
      rw [← norm_zero (E := ℂ), ← sub_self (γ t₀)]
      exact (hγ_cont.sub continuousAt_const).norm
    exact h_tend (Iic_mem_nhds one_pos)
  have h_big_O : ∀ l : Filter ℝ, l ≤ 𝓝 t₀ →
      (fun t => ‖γ t - γ t₀‖ ^ m) =O[l] (fun t => ‖γ t - γ t₀‖ ^ n) := fun l hl => by
    refine .of_bound 1 ?_
    filter_upwards [hl h_le_one] with t ht
    simp only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _), one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) ht hmn
  exact ⟨fun L hL hR => (h.right_flat L hL hR).trans_isBigO (h_big_O _ nhdsWithin_le_nhds),
    fun L hL hL' => (h.left_flat L hL hL').trans_isBigO (h_big_O _ nhdsWithin_le_nhds)⟩

private theorem tangentDeviation_isLittleO_one_of_continuousAt
    {γ : ℝ → ℂ} {t₀ : ℝ} (hγ_cont : ContinuousAt γ t₀)
    {l : Filter ℝ} (hl : l ≤ 𝓝 t₀) (L : ℂ) (hL : L ≠ 0) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[l] (fun _ => (1 : ℝ)) := by
  rw [Asymptotics.isLittleO_one_iff]
  have h_tend : Tendsto (fun t => ‖γ t - γ t₀‖) l (𝓝 0) := by
    rw [← norm_zero (E := ℂ), ← sub_self (γ t₀)]
    exact ((hγ_cont.sub continuousAt_const).mono_left hl).norm
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h_ev : ∀ᶠ t in l, ‖γ t - γ t₀‖ < ε / 2 := h_tend (Iio_mem_nhds (half_pos hε))
  filter_upwards [h_ev] with t ht
  simp only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  calc ‖tangentDeviation (γ t - γ t₀) L‖
      ≤ 2 * ‖γ t - γ t₀‖ := norm_tangentDeviation_le _ _ hL
    _ < 2 * (ε / 2) := by linarith
    _ = ε := by ring


/-- Flatness of order 1 from a derivative limit on either side, packaged as a
common helper for the left and right variants. The set `u` is the open ray
`Ioi t₀` or `Iio t₀`. -/
private theorem tangentDeviation_isLittleO_of_hasDerivWithinAt
    {γ : ℝ → ℂ} {t₀ : ℝ} {L : ℂ} (hL : L ≠ 0) {u : Set ℝ}
    (hderiv : HasDerivWithinAt γ L u t₀) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[u] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  simp only [pow_one]
  rw [Asymptotics.isLittleO_norm_norm]
  set r := fun t => γ t - γ t₀ - (t - t₀) • L with hr_def
  have hr := hasDerivWithinAt_iff_isLittleO.mp hderiv
  have h_eq : ∀ t, tangentDeviation (γ t - γ t₀) L = tangentDeviation (r t) L := fun t => by
    rw [show γ t - γ t₀ = (t - t₀) • L + r t from by simp [hr_def],
      tangentDeviation_add, tangentDeviation_real_smul_self _ _ hL, zero_add]
  have hO : (fun t => tangentDeviation (r t) L) =O[𝓝[u] t₀] r :=
    Asymptotics.isBigO_iff.mpr
      ⟨2, Eventually.of_forall fun _ => norm_tangentDeviation_le _ _ hL⟩
  have hO2 : (fun t => t - t₀) =O[𝓝[u] t₀] (fun t => γ t - γ t₀) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨2 / ‖L‖, ?_⟩
    filter_upwards [hr.def (by positivity : (0 : ℝ) < ‖L‖ / 2)] with t ht
    have h_smul : (t - t₀) • L = (γ t - γ t₀) - r t := by simp [hr_def]
    have h2 : ‖(t - t₀) • L‖ ≤ ‖γ t - γ t₀‖ + ‖r t‖ := h_smul ▸ norm_sub_le _ _
    have hr_eq : ‖r t‖ ≤ ‖L‖ / 2 * ‖t - t₀‖ := ht
    rw [div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr hL)]
    nlinarith [norm_nonneg (γ t - γ t₀), (norm_smul (t - t₀) L).symm]
  exact ((hO.trans_isLittleO hr).trans_isBigO hO2).congr_left fun t => (h_eq t).symm

/-- Right-sided flatness of order 1 from a right derivative limit. -/
private theorem tangentDeviation_isLittleO_right
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hγ_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[>] t₀, DifferentiableAt ℝ γ t) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact tangentDeviation_isLittleO_of_hasDerivWithinAt hL <|
    hasDerivWithinAt_Ioi_iff_Ici.mpr <| hasDerivWithinAt_Ici_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hγ_right

/-- Left-sided flatness of order 1 from a left derivative limit. -/
private theorem tangentDeviation_isLittleO_left
    (γ : ℝ → ℂ) (t₀ : ℝ) (L : ℂ) (hL : L ≠ 0)
    (hγ_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (hγ_cont : ContinuousAt γ t₀)
    (hγ_diff : ∀ᶠ t in 𝓝[<] t₀, DifferentiableAt ℝ γ t) :
    (fun t => ‖tangentDeviation (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ 1) := by
  obtain ⟨s, hs_mem, hs_diff⟩ := hγ_diff.exists_mem
  exact tangentDeviation_isLittleO_of_hasDerivWithinAt hL <|
    hasDerivWithinAt_Iio_iff_Iic.mpr <| hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hs_diff t ht).differentiableWithinAt)
      hγ_cont.continuousWithinAt hs_mem hγ_left

/-- Every piecewise C¹ immersion is flat of order 1 at any interior point.
The derivative approximation `γ(t) - γ(t₀) ∼ L(t - t₀)` lies exactly on the
tangent line, so the deviation is the remainder `o(t - t₀) = o(‖γ(t) - γ(t₀)‖)`. -/
theorem isFlatOfOrder_one (γ : PwC1Immersion x y) (t₀ : ℝ)
    (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    IsFlatOfOrder (γ : ℝ → ℂ) t₀ 1 := by
  have hcont : ContinuousAt (γ : ℝ → ℂ) t₀ := γ.continuous.continuousAt
  have hcl : IsClosed ((↑γ.toPiecewiseC1Path.partition : Set ℝ) \ {t₀}) :=
    (γ.toPiecewiseC1Path.partition.finite_toSet.subset diff_subset).isClosed
  have hmem : (↑γ.toPiecewiseC1Path.partition \ {t₀} : Set ℝ)ᶜ ∈ 𝓝 t₀ :=
    hcl.isOpen_compl.mem_nhds (mem_compl (fun h => h.2 rfl))
  have hIoo : Ioo (0 : ℝ) 1 ∈ 𝓝 t₀ := Ioo_mem_nhds ht₀.1 ht₀.2
  have hdiff_aux : ∀ {u : Set ℝ} (_ : ∀ t ∈ u, t ≠ t₀),
      ∀ᶠ t in 𝓝[u] t₀, DifferentiableAt ℝ (γ : ℝ → ℂ) t := fun {u} hne => by
    filter_upwards [nhdsWithin_le_nhds hmem, nhdsWithin_le_nhds hIoo,
      self_mem_nhdsWithin] with t ht₁ ht₂ ht₃
    exact γ.toPiecewiseC1Path.differentiable_off_extend t ht₂ fun hm => ht₁ ⟨hm, hne t ht₃⟩
  refine ⟨fun L hL hL_right => ?_, fun L hL hL_left => ?_⟩
  · exact tangentDeviation_isLittleO_right (γ : ℝ → ℂ) t₀ L hL hL_right hcont
      (hdiff_aux fun _ ht => ne_of_gt (mem_Ioi.mp ht))
  · exact tangentDeviation_isLittleO_left (γ : ℝ → ℂ) t₀ L hL hL_left hcont
      (hdiff_aux fun _ ht => ne_of_lt (mem_Iio.mp ht))

/-- **Condition (A')** from Hungerbuhler-Wasem: for each singular point `s` in `S₀`
and each parameter `t₀` where `γ(t₀) = s`, the curve must be flat of order
`poleOrder s` at `t₀`. -/
def SatisfiesConditionA' (γ : PwC1Immersion x y) (_f : ℂ → ℂ)
    (S0 : Finset ℂ) (poleOrder : ℂ → ℕ) : Prop :=
  ∀ s ∈ S0, ∀ t₀ ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s →
    t₀ ∈ Ioo (0 : ℝ) 1 →
    IsFlatOfOrder (γ : ℝ → ℂ) t₀ (poleOrder s)

/-- **Condition (B)** from Hungerbuhler-Wasem (Theorem 3.3): at each crossing point,
the angle `α` is a rational multiple of `π`, and the Laurent coefficients of `f` satisfy
angle compatibility.

For simple poles, this is vacuously satisfied for the Laurent part. -/
structure SatisfiesConditionB (γ : PwC1Immersion x y) (f : ℂ → ℂ)
    (S0 : Finset ℂ) : Prop where
  /-- The angle at each crossing is a rational multiple of `π`. -/
  angle_rational : ∀ s ∈ S0, ∀ t₀ ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s →
    ∀ ht₀ : t₀ ∈ Ioo (0 : ℝ) 1,
      ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
        angleAtCrossing γ t₀ ht₀ = ↑p * Real.pi / ↑q
  /-- Laurent coefficient compatibility: there is a Laurent decomposition
      `f(z) = g(z) + Σ_k a_k / (z - s)^(k+1)` where `g` is analytic, and each
      nonzero coefficient `a_k` with `k ≥ 1` satisfies `k · α ∈ 2πℤ`. -/
  laurent_compatible : ∀ s ∈ S0, ∀ t₀ ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s →
    ∀ ht₀ : t₀ ∈ Ioo (0 : ℝ) 1,
      ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
        AnalyticAt ℂ g s ∧
        (∀ᶠ z in 𝓝[≠] s, f z = g z +
          ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧
        (∀ k : Fin N, a k ≠ 0 → k.val ≥ 1 →
          ∃ m : ℤ, (↑k.val : ℝ) * angleAtCrossing γ t₀ ht₀ =
            ↑m * (2 * Real.pi))

/-- Condition (A') is automatically satisfied when all poles are simple and the
pole order function assigns order 1 to each pole. Flatness of order 1 is automatic
for any piecewise C¹ immersion. -/
theorem satisfiesConditionA'_of_simplePoles
    (γ : PwC1Immersion x y) (f : ℂ → ℂ) (S0 : Finset ℂ)
    (_hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s) :
    SatisfiesConditionA' γ f S0 (fun _ => 1) :=
  fun _ _ t₀ _ _ ht => isFlatOfOrder_one γ t₀ ht

/-- Condition (B) for simple poles requires angle rationality at corner crossings
as an explicit hypothesis. The Laurent coefficient condition is vacuously true
(the only singular term has `k = 0`, so `k ≥ 1` is never satisfied).

At smooth crossings the angle is `π = 1 · π / 1`, so this is automatic.
At corner crossings, the angle depends on the curve geometry. -/
theorem satisfiesConditionB_of_simplePoles
    (γ : PwC1Immersion x y) (f : ℂ → ℂ) (S0 : Finset ℂ)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hAngles : ∀ s ∈ S0, ∀ t₀ ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s →
      ∀ ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1,
        t₀ ∈ γ.toPiecewiseC1Path.partition →
          ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
            angleAtCrossing γ t₀ ht₀_Ioo = ↑p * Real.pi / ↑q) :
    SatisfiesConditionB γ f S0 := by
  refine ⟨fun s hs t₀ ht₀ hcross ht₀_Ioo => ?_, fun s hs t₀ _ _ _ => ?_⟩
  · by_cases hp : t₀ ∈ γ.toPiecewiseC1Path.partition
    · exact hAngles s hs t₀ ht₀ hcross ht₀_Ioo hp
    · exact ⟨1, 1, one_ne_zero, Nat.coprime_one_left 1, by
        simp [angleAtCrossing_smooth γ t₀ ht₀_Ioo hp]⟩
  · obtain ⟨c, g, hg, hf_eq⟩ := hSimplePoles s hs
    refine ⟨1, ![c], g, hg, ?_, ?_⟩
    · filter_upwards [hf_eq] with z hz
      simp [hz, pow_one, add_comm]
    · exact fun ⟨_, hk⟩ _ hk1 => absurd hk1 (by lia)

/-- Both conditions (A') and (B) are satisfied for simple poles, provided
corner crossing angles are rational multiples of `π`. Condition (A') is fully
automatic; condition (B) requires the angle hypothesis only at corners. -/
theorem conditions_automatic_simple_poles
    (γ : PwC1Immersion x y) (f : ℂ → ℂ) (S0 : Finset ℂ)
    (hSimplePoles : ∀ s ∈ S0, HasSimplePoleAt f s)
    (hAngles : ∀ s ∈ S0, ∀ t₀ ∈ Icc (0 : ℝ) 1, (γ : ℝ → ℂ) t₀ = s →
      ∀ ht₀_Ioo : t₀ ∈ Ioo (0 : ℝ) 1,
        t₀ ∈ γ.toPiecewiseC1Path.partition →
          ∃ p q : ℕ, q ≠ 0 ∧ Nat.Coprime p q ∧
            angleAtCrossing γ t₀ ht₀_Ioo = ↑p * Real.pi / ↑q) :
    SatisfiesConditionA' γ f S0 (fun _ => 1) ∧ SatisfiesConditionB γ f S0 :=
  ⟨satisfiesConditionA'_of_simplePoles γ f S0 hSimplePoles,
   satisfiesConditionB_of_simplePoles γ f S0 hSimplePoles hAngles⟩


end
