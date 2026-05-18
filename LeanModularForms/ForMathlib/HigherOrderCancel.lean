/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanModularForms.ForMathlib.FlatChordBound
import LeanModularForms.ForMathlib.HigherOrderAssembly
import LeanModularForms.ForMathlib.HungerbuhlerWasem.HigherOrderAsymptotics
import LeanModularForms.ForMathlib.SectorCurve

/-!
# Higher-Order Cancellation from Conditions (A') + (B)

This file proves that under conditions (A') and (B) from Hungerbuhler-Wasem,
the CPV of the remainder `f - principalPartSum` tends to 0. This discharges
the `hCancel` hypothesis in `generalizedResidueTheorem`.

## Main results

* `hCancel_of_contourIntegral_zero` -- if the contour integral vanishes and
  `gamma` avoids `S`, then the CPV is zero.
* `hCancel_of_decomposition` -- structural decomposition for cancellation.
* `hasCauchyPVOn_pow_inv_of_avoids` -- CPV of `1/(z-s)^k` for `k ≥ 2` along
  a closed curve avoiding `s`.
* `hw_theorem_3_3_odd_transverse_parametric` -- HW Theorem 3.3 for the
  k-odd transverse case (curve-side conclusion).

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2, Theorem 3.3
-/

open Complex Set Filter Topology MeasureTheory Finset HungerbuhlerWasem
open scoped Classical Real Interval

noncomputable section

variable {x : ℂ}

/-- When `gamma` avoids all points of `S`, the CPV of any function `f` equals
its ordinary contour integral. In particular, if the contour integral is `L`,
then `HasCauchyPVOn S f gamma L`.

This is a direct restatement of `hasCauchyPVOn_of_avoids` specialized to the
remainder setting: the CPV of the remainder equals its contour integral. -/
theorem hCancel_of_contourIntegral_zero
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (hδ : ∃ δ > 0, ∀ s ∈ S, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_zero : γ.contourIntegral f = 0) :
    HasCauchyPVOn S f γ 0 :=
  h_zero ▸ hasCauchyPVOn_of_avoids hδ

/-- **Structural decomposition for cancellation.** If the remainder `f - pp`
decomposes as a sum of two functions `h₁ + h₂` where each individually has
vanishing CPV, then the full remainder has vanishing CPV.

This allows reducing the higher-order cancellation to proving it for each
component separately: typically `h₁` is the holomorphic part and `h₂`
collects the higher-order polar terms. -/
theorem hCancel_of_decomposition
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : PiecewiseC1Path x x)
    (h₁ h₂ : ℂ → ℂ)
    (h_decomp : ∀ z, f z - principalPartSum S (fun s => residue f s) z = h₁ z + h₂ z)
    (hh₁ : HasCauchyPVOn S h₁ γ 0)
    (hh₂ : HasCauchyPVOn S h₂ γ 0)
    (hI₁ : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h₁ γ.toPath.extend ε t) volume 0 1)
    (hI₂ : ∀ ε > 0, IntervalIntegrable
      (fun t => cpvIntegrandOn S h₂ γ.toPath.extend ε t) volume 0 1) :
    HasCauchyPVOn S
      (fun z => f z - principalPartSum S (fun s => residue f s) z) γ 0 := by
  have h_add := hh₁.add hh₂ hI₁ hI₂
  simp only [add_zero] at h_add
  have h_congr : (fun ε => ∫ t in (0 : ℝ)..1,
      cpvIntegrandOn S (fun z => f z -
        principalPartSum S (fun s => residue f s) z) γ.toPath.extend ε t) =
      (fun ε => ∫ t in (0 : ℝ)..1,
        cpvIntegrandOn S (fun z => h₁ z + h₂ z) γ.toPath.extend ε t) := by
    ext ε
    congr 1
    ext t
    simp only [cpvIntegrandOn]
    split_ifs with h
    · rfl
    · congr 1
      exact h_decomp _
  simp only [HasCauchyPVOn] at h_add ⊢
  rwa [h_congr]

/-- **Higher-order avoidance: contour integral vanishes.** For `k ≥ 2`, the contour
integral of `1/(z-s)^k` along a closed `γ` avoiding `s` is zero. Follows from FTC
applied to the antiderivative `-1/[(k-1)(z-s)^{k-1}]`, which is single-valued on
`ℂ \ {s}`. -/
theorem PiecewiseC1Path.contourIntegral_pow_inv_eq_zero
    {x : ℂ} (γ : PiecewiseC1Path x x) {s : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s)
    (h_int : IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1) :
    γ.contourIntegral (fun z => 1 / (z - s) ^ k) = 0 :=
  γ.contourIntegral_eq_zero_of_hasDerivAt_of_closed rfl
    (U := {z : ℂ | z ≠ s})
    (fun t ht => h_avoids t ht)
    (fun _ hz => hasDerivAt_antiderivative_pow_inv_complex hk hz)
    h_int

/-- **Higher-order avoidance: CPV is zero.** For `k ≥ 2`, the CPV of `1/(z-s)^k`
along a closed `γ` avoiding `s` (with positive margin) is zero. Combines
`hasCauchyPVOn_of_avoids` with the contour-integral-vanishing result. -/
theorem hasCauchyPVOn_pow_inv_of_avoids
    {x : ℂ} (γ : PiecewiseC1Path x x) {s : ℂ} {k : ℕ} (hk : 2 ≤ k)
    (hδ : ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s‖)
    (h_int : IntervalIntegrable
      (fun t => (1 / (γ.toPath.extend t - s) ^ k) * deriv γ.toPath.extend t)
      volume 0 1) :
    HasCauchyPVOn {s} (fun z => 1 / (z - s) ^ k) γ 0 := by
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := hδ
  have h_avoids : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ s := by
    intro t ht hγt
    have hδ_norm : δ ≤ ‖γ t - s‖ := hδ_bd t ht
    rw [hγt, sub_self, norm_zero] at hδ_norm
    linarith
  have hδ' : ∃ δ > 0, ∀ s' ∈ ({s} : Finset ℂ), ∀ t ∈ Icc (0 : ℝ) 1, δ ≤ ‖γ t - s'‖ :=
    ⟨δ, hδ_pos, fun s' hs' t ht => Finset.mem_singleton.mp hs' ▸ hδ_bd t ht⟩
  exact (γ.contourIntegral_pow_inv_eq_zero hk h_avoids h_int) ▸ hasCauchyPVOn_of_avoids hδ'

/-- **Line-model F-difference vanishing for k odd.** For `k` odd ≥ 2, the
antiderivative of `1/(z-s)^k` at the two symmetric line-exit-points
`s ± (ε/‖L‖)·L` are equal. This is the source of the line PV = 0 for
odd-order poles in the transverse case. -/
theorem F_line_diff_eq_zero_of_odd
    (s L : ℂ) (k : ℕ) (hk : 2 ≤ k) (hk_odd : Odd k) (ε : ℝ) :
    -(↑(k - 1) : ℂ)⁻¹ * (((s - (ε / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ * (((s + (ε / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹ := by
  have h_even : Even (k - 1) := by
    obtain ⟨m, hm⟩ := hk_odd
    exact ⟨m, by omega⟩
  congr 1
  congr 1
  have h1 : (s - (ε / ‖L‖ : ℝ) • L) - s = -((ε / ‖L‖ : ℝ) • L) := by ring
  have h2 : (s + (ε / ‖L‖ : ℝ) • L) - s = ((ε / ‖L‖ : ℝ) • L) := by ring
  rw [h1, h2, neg_pow, h_even.neg_one_pow, one_mul]

/-- **Combined curve F-difference → 0 for k odd.** Given exit-time functions
`t_eps_plus`, `t_eps_minus` parametrizing γ at radius ε on the right and left
of t₀ respectively (each with `‖γ(t_eps_±(ε)) - s‖ = ε` eventually), the
curve antiderivative difference tends to 0 as ε → 0⁺.

This is the **PHASE 3 ENDPOINT**: combining both F-diff asymptotics with
the k-odd line-model symmetric vanishing gives the curve-side
"F(γ(t_-)) - F(γ(t_+)) → 0" needed for the closed-curve PV result. -/
theorem F_curve_diff_tendsto_zero_odd
    {γ : ℝ → ℂ} {t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (t_eps_plus t_eps_minus : ℝ → ℝ)
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] 0) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] 0) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_minus ε) - s‖ = ε) :
    Tendsto (fun ε =>
      ‖(-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹) -
        (-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹)‖)
      (𝓝[>] 0) (𝓝 0) := by
  have h_right_comp := (F_diff_at_tangent_target_tendsto_zero_right
    h_flat hL h_deriv_right hL_right h_s hk hkn hn1).comp h_plus_to
  have h_left_comp := (F_diff_at_tangent_target_tendsto_zero_left
    h_flat hL h_deriv_left hL_left h_s hk hkn hn1).comp h_minus_to
  have h_sum_raw := h_right_comp.add h_left_comp
  have h_sum : Tendsto (fun ε =>
      ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹‖ +
        ‖-(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹ -
          -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹‖)
      (𝓝[>] 0) (𝓝 0) := by
    convert h_sum_raw using 2
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h_sum
      (Eventually.of_forall fun _ => norm_nonneg _) ?_
  filter_upwards [h_plus_radius, h_minus_radius] with ε hpr hmr
  have h_targets_eq :
      -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_minus ε) - s‖ / ‖(-L)‖ : ℝ) • (-L)) - s) ^ (k - 1))⁻¹ =
      -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹ := by
    rw [hmr, norm_neg, hpr]
    have heq : (s + (ε / ‖L‖ : ℝ) • (-L) : ℂ) - s = (s - (ε / ‖L‖ : ℝ) • L) - s := by simp
    rw [heq]
    exact F_line_diff_eq_zero_of_odd s L k hk hk_odd ε
  set TR := -(↑(k - 1) : ℂ)⁻¹ * (((s + (‖γ (t_eps_plus ε) - s‖ / ‖L‖ : ℝ) • L) - s) ^ (k - 1))⁻¹
  set A := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_minus ε) - s) ^ (k - 1))⁻¹
  set B := -(↑(k - 1) : ℂ)⁻¹ * ((γ (t_eps_plus ε) - s) ^ (k - 1))⁻¹
  have h_triangle : ‖A - B‖ ≤ ‖B - TR‖ + ‖A - TR‖ := by
    calc ‖A - B‖ = ‖(A - TR) - (B - TR)‖ := by ring_nf
      _ ≤ ‖A - TR‖ + ‖B - TR‖ := norm_sub_le _ _
      _ = ‖B - TR‖ + ‖A - TR‖ := add_comm _ _
  change ‖A - B‖ ≤ ‖B - TR‖ + ‖A - _‖
  rw [h_targets_eq]
  exact h_triangle

/-- **HW Theorem 3.3 — k-odd transverse case.** For closed γ (γ a = γ b) with
single transverse crossing at t₀ and `γ(t₀) = s`, k odd ≥ 3, flatness order
n ≥ k:

  ∫_{[a, t_eps_minus(ε)] ∪ [t_eps_plus(ε), b]} γ'/(γ-s)^k → 0  as ε → 0⁺

This is the **curve-side conclusion of HW Theorem 3.3 higher-order** for the
k-odd transverse case, fully proven from:
- Phase 3 analytical kernel (chord bound, F-diff segment bound, asymptotics)
- Phase 3.7 (line F-diff = 0 for k odd, symmetric cancellation)
- Phase 3.8 (combined curve F-diff → 0)
- Phase 3.5a (FTC excision)

Combines `F_curve_diff_tendsto_zero_odd` with
`cpv_excised_tendsto_zero_of_F_diff_zero` to give the final PV statement.

This is the **Lean formalization of HW eq. (3.4)** for k odd transverse with
flatness order matching the pole order. -/
theorem hw_theorem_3_3_odd_transverse_parametric
    {γ : ℝ → ℂ} {γ' : ℝ → ℂ} {a b t₀ : ℝ} {s L : ℂ} {n k : ℕ}
    (h_close : γ a = γ b)
    (h_flat : IsFlatOfOrder γ t₀ n) (hL : L ≠ 0)
    (h_deriv_right : HasDerivWithinAt γ L (Ioi t₀) t₀)
    (h_deriv_left : HasDerivWithinAt γ L (Iio t₀) t₀)
    (hL_right : Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L))
    (hL_left : Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L))
    (h_s : γ t₀ = s) (hk : 2 ≤ k) (hk_odd : Odd k) (hkn : k ≤ n) (hn1 : 1 ≤ n)
    (t_eps_plus t_eps_minus : ℝ → ℝ)
    (h_plus_to : Tendsto t_eps_plus (𝓝[>] 0) (𝓝[>] t₀))
    (h_plus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_plus ε) - s‖ = ε)
    (h_minus_to : Tendsto t_eps_minus (𝓝[>] 0) (𝓝[<] t₀))
    (h_minus_radius : ∀ᶠ ε in 𝓝[>] 0, ‖γ (t_eps_minus ε) - s‖ = ε)
    (h_minus_smooth : ∀ ε > 0, ∀ t ∈ uIcc a (t_eps_minus ε), HasDerivAt γ (γ' t) t)
    (h_minus_avoids : ∀ ε > 0, ∀ t ∈ uIcc a (t_eps_minus ε), γ t ≠ s)
    (h_minus_int : ∀ ε > 0,
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume a (t_eps_minus ε))
    (h_plus_smooth : ∀ ε > 0, ∀ t ∈ uIcc (t_eps_plus ε) b, HasDerivAt γ (γ' t) t)
    (h_plus_avoids : ∀ ε > 0, ∀ t ∈ uIcc (t_eps_plus ε) b, γ t ≠ s)
    (h_plus_int : ∀ ε > 0,
      IntervalIntegrable (fun t => γ' t / (γ t - s) ^ k) volume (t_eps_plus ε) b) :
    Tendsto (fun ε =>
      (∫ t in a..(t_eps_minus ε), γ' t / (γ t - s) ^ k) +
        (∫ t in (t_eps_plus ε)..b, γ' t / (γ t - s) ^ k))
      (𝓝[>] 0) (𝓝 0) :=
  cpv_excised_tendsto_zero_of_F_diff_zero h_close hk
    t_eps_plus t_eps_minus
    h_minus_smooth h_minus_avoids h_minus_int
    h_plus_smooth h_plus_avoids h_plus_int
    (F_curve_diff_tendsto_zero_odd h_flat hL h_deriv_right h_deriv_left
      hL_right hL_left h_s hk hk_odd hkn hn1
      t_eps_plus t_eps_minus h_plus_to h_plus_radius h_minus_to h_minus_radius)

end
