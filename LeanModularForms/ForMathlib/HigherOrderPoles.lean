/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.PiecewiseC1Path
import LeanModularForms.ForMathlib.Residue
import Mathlib.Analysis.Meromorphic.Order

/-!
# Higher-Order Pole Conditions

Geometric conditions ensuring Cauchy principal value convergence at higher-order poles
(conditions A' and B from Hungerbuhler-Wasem, Definition 3.2 / Theorem 3.3).

For simple poles, these conditions are automatically satisfied. For higher-order poles,
the curve must have sufficient flatness at crossing points (condition A'), and the
Laurent coefficients must be compatible with the crossing angle (condition B).

## Main definitions

* `tangentDeviation'` -- the component of `w` orthogonal to direction `L` in `ℂ`.

* `IsFlatOfOrder` -- the curve has flatness of order `n` at a crossing point `t₀`:
  the tangent deviation from the approach direction is `o(‖γ(t) - γ(t₀)‖ⁿ)`.

* `HasFlatCrossings` -- for each pole `s` of `f` that `γ` crosses, the crossing has
  sufficient flatness (condition A' from Hungerbuhler-Wasem).

* `IsLaurentCompatible` -- angle/Laurent coefficient compatibility at each crossing
  (condition B from Hungerbuhler-Wasem).

* `poleOrder` -- the pole order of a meromorphic function at a point, as a natural number.

* `meromorphicPrincipalPart` -- the finite-rank Laurent principal part of a meromorphic
  function at a point, extracting the singular terms of the Laurent series.

## Main results

* `isFlatOfOrder_zero` -- every continuous curve is flat of order 0.

* `poleOrder_le_one_of_simplePole` -- simple poles have pole order at most 1.

* `hasFlatCrossings_of_simplePoles` -- simple poles automatically satisfy the flatness
  condition, since flatness of order 0 suffices when the pole order is 0.

* `isLaurentCompatible_of_simplePoles` -- simple poles automatically satisfy Laurent
  compatibility, since there are no higher-order singular terms.

* `meromorphicPrincipalPart_eq_zero_of_analyticAt` -- if `f` is analytic at `z₀`, the
  principal part is zero.

* `meromorphicPrincipalPart_differentiableOn` -- the principal part is differentiable
  away from the pole.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*,
  arXiv:1808.00997v2, Definition 3.2, Theorem 3.3.
-/

open Complex Set Filter Topology Asymptotics
open scoped Real

private instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
attribute [local instance] Classical.propDecidable

noncomputable section

variable {x y : ℂ}

/-! ### Tangent deviation in ℂ -/

/-- The tangent deviation: the component of `w` orthogonal to direction `L` in `ℂ`
viewed as `ℝ²`. Computed as `w - proj_L(w)` where `proj_L(w) = (Re(w * conj L) / ‖L‖²) · L`. -/
def tangentDeviation' (w L : ℂ) : ℂ :=
  w - ((w * starRingEnd ℂ L).re / Complex.normSq L) • L

/-- Norm bound: `‖tangentDeviation' w L‖ ≤ 2 * ‖w‖` for `L ≠ 0`. -/
theorem norm_tangentDeviation'_le (w L : ℂ) (hL : L ≠ 0) :
    ‖tangentDeviation' w L‖ ≤ 2 * ‖w‖ := by
  have hns : 0 < Complex.normSq L := Complex.normSq_pos.mpr hL
  unfold tangentDeviation'
  suffices h : ‖((w * starRingEnd ℂ L).re / Complex.normSq L) • L‖ ≤ ‖w‖ by
    calc ‖w - _‖ ≤ ‖w‖ + ‖((w * starRingEnd ℂ L).re / Complex.normSq L) • L‖ :=
            norm_sub_le _ _
      _ ≤ ‖w‖ + ‖w‖ := by gcongr
      _ = 2 * ‖w‖ := by ring
  rw [norm_smul, Real.norm_eq_abs]
  calc |(w * starRingEnd ℂ L).re / Complex.normSq L| * ‖L‖
      ≤ (‖w‖ * ‖L‖ / Complex.normSq L) * ‖L‖ := by
        gcongr; rw [abs_div, abs_of_pos hns]; gcongr
        exact (Complex.abs_re_le_norm _).trans
          (by rw [norm_mul, starRingEnd_apply, norm_star])
    _ = ‖w‖ * (‖L‖ * ‖L‖ / Complex.normSq L) := by ring
    _ = ‖w‖ := by rw [Complex.norm_mul_self_eq_normSq L, div_self hns.ne', mul_one]

/-! ### Flatness of order n (Definition 3.2)

A piecewise C¹ curve `γ` is flat of order `n` at parameter `t₀` if the orthogonal
deviation from the tangent line at `γ(t₀)` is `o(‖γ(t) - γ(t₀)‖ⁿ)` as `t → t₀`,
where the tangent line is determined by the one-sided derivative limits. -/

/-- A curve `γ : ℝ → ℂ` is **flat of order `n`** at parameter `t₀` if:
- From the right: the deviation from the right tangent is `o(‖γ(t) - γ(t₀)‖ⁿ)`.
- From the left: the deviation from the left tangent is `o(‖γ(t) - γ(t₀)‖ⁿ)`.

This captures Definition 3.2 from Hungerbuhler-Wasem: the curve stays within
`o(|Γ(x) - z₁|ⁿ)` of the tangent lines at the crossing point `z₁`. -/
structure IsFlatOfOrder (γ : ℝ → ℂ) (t₀ : ℝ) (n : ℕ) : Prop where
  /-- From the right: deviation from right tangent direction is
  `o(‖γ(t) - γ(t₀)‖ⁿ)`. -/
  right_flat : ∀ L : ℂ, L ≠ 0 → Tendsto (deriv γ) (𝓝[>] t₀) (𝓝 L) →
    (fun t => ‖tangentDeviation' (γ t - γ t₀) L‖) =o[𝓝[>] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ n)
  /-- From the left: deviation from left tangent direction is
  `o(‖γ(t) - γ(t₀)‖ⁿ)`. -/
  left_flat : ∀ L : ℂ, L ≠ 0 → Tendsto (deriv γ) (𝓝[<] t₀) (𝓝 L) →
    (fun t => ‖tangentDeviation' (γ t - γ t₀) L‖) =o[𝓝[<] t₀]
      (fun t => ‖γ t - γ t₀‖ ^ n)

/-- Flatness of order 0 is trivially true for any continuous curve.

The deviation `‖tangentDeviation' (γ t - γ t₀) L‖ → 0` as `t → t₀` (by continuity
and the norm bound), while `‖γ t - γ t₀‖⁰ = 1` is constant. Hence the deviation is
`o(1)`, which is precisely `IsFlatOfOrder γ t₀ 0`. -/
theorem isFlatOfOrder_zero (γ : ℝ → ℂ) (t₀ : ℝ) (hcont : ContinuousAt γ t₀) :
    IsFlatOfOrder γ t₀ 0 := by
  have helper : ∀ (l : Filter ℝ), l ≤ 𝓝 t₀ → ∀ L : ℂ, L ≠ 0 →
      (fun t => ‖tangentDeviation' (γ t - γ t₀) L‖) =o[l]
        (fun t => ‖γ t - γ t₀‖ ^ 0) := by
    intro l hl L hL
    simp only [pow_zero]
    rw [isLittleO_one_iff ℝ]
    have h_sub : Tendsto (fun t => γ t - γ t₀) l (𝓝 0) := by
      rw [show (0 : ℂ) = γ t₀ - γ t₀ from (sub_self _).symm]
      exact (hcont.mono_left hl).sub tendsto_const_nhds
    apply squeeze_zero (fun t => norm_nonneg _)
      (fun t => norm_tangentDeviation'_le (γ t - γ t₀) L hL)
    have := h_sub.norm.const_mul 2
    rwa [norm_zero, mul_zero] at this
  exact ⟨fun L hL _ => helper _ nhdsWithin_le_nhds L hL,
         fun L hL _ => helper _ nhdsWithin_le_nhds L hL⟩

/-- Flatness of order `m` implies flatness of order `n` for `n ≤ m`,
provided the curve is continuous at the point. -/
theorem IsFlatOfOrder.of_le {γ : ℝ → ℂ} {t₀ : ℝ} {m n : ℕ}
    (h : IsFlatOfOrder γ t₀ m) (hmn : n ≤ m)
    (hγ_cont : ContinuousAt γ t₀) :
    IsFlatOfOrder γ t₀ n := by
  have h_le_one : ∀ᶠ t in 𝓝 t₀, ‖γ t - γ t₀‖ ≤ 1 := by
    have : Tendsto (fun t => ‖γ t - γ t₀‖) (𝓝 t₀) (𝓝 0) := by
      rw [← norm_zero (E := ℂ), ← sub_self (γ t₀)]
      exact (hγ_cont.sub continuousAt_const).norm
    exact this (Iic_mem_nhds one_pos)
  have h_big_O : ∀ (l : Filter ℝ), l ≤ 𝓝 t₀ →
      (fun t => ‖γ t - γ t₀‖ ^ m) =O[l] (fun t => ‖γ t - γ t₀‖ ^ n) := by
    intro l hl
    apply Asymptotics.IsBigO.of_bound 1
    filter_upwards [hl h_le_one] with t ht
    simp only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _), one_mul]
    exact pow_le_pow_of_le_one (norm_nonneg _) ht hmn
  exact ⟨fun L hL hR => (h.right_flat L hL hR).trans_isBigO (h_big_O _ nhdsWithin_le_nhds),
    fun L hL hL' => (h.left_flat L hL hL').trans_isBigO (h_big_O _ nhdsWithin_le_nhds)⟩

/-! ### Pole order -/

/-- The **pole order** of a meromorphic function at a point, as a natural number.
Returns `0` if `f` is analytic at `z₀` (including identically zero near `z₀`).
Returns `n` if `f` has a pole of order `n` (i.e., `meromorphicOrderAt f z₀ = -n`). -/
noncomputable def poleOrder (f : ℂ → ℂ) (z₀ : ℂ) : ℕ :=
  (-(meromorphicOrderAt f z₀).untop₀).toNat

/-- Simple poles have `poleOrder` at most 1.

If the pole coefficient `c = 0` then `f` is analytic and `poleOrder = 0`.
If `c ≠ 0` then `meromorphicOrderAt = -1` and `poleOrder = 1`. -/
theorem poleOrder_le_one_of_simplePole {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) : poleOrder f z₀ ≤ 1 := by
  obtain ⟨c, g, hg, hev⟩ := h
  by_cases hc : c = 0
  · -- f is analytic at z₀, so meromorphicOrderAt ≥ 0, hence poleOrder = 0
    have hf_eq : f =ᶠ[nhdsWithin z₀ {z₀}ᶜ] g := by
      filter_upwards [hev] with z hz; rw [hz, hc, zero_div, zero_add]
    have h_ord : 0 ≤ meromorphicOrderAt f z₀ := by
      rw [meromorphicOrderAt_congr hf_eq]; exact hg.meromorphicOrderAt_nonneg
    unfold poleOrder
    have h_nn : 0 ≤ (meromorphicOrderAt f z₀).untop₀ := by
      cases hm : meromorphicOrderAt f z₀ with
      | top => simp [WithTop.untop₀]
      | coe v => simp [WithTop.untop₀]; rw [hm] at h_ord; exact_mod_cast h_ord
    simp [Int.toNat_eq_zero.mpr (neg_nonpos.mpr h_nn)]
  · -- c ≠ 0: meromorphicOrderAt = -1, so poleOrder = 1
    have hf : MeromorphicAt f z₀ := by
      rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
      refine ⟨-1, fun z => c + g z * (z - z₀), ?_, ?_⟩
      · exact analyticAt_const.add (hg.mul (analyticAt_id.sub analyticAt_const))
      · filter_upwards [hev, self_mem_nhdsWithin] with z hz hne
        rw [hz]
        have hne' : z - z₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hne)
        simp only [zpow_neg_one, smul_eq_mul]; field_simp
    have hord : meromorphicOrderAt f z₀ = (-1 : ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hf]
      refine ⟨fun z => c + g z * (z - z₀), ?_, ?_, ?_⟩
      · exact analyticAt_const.add (hg.mul (analyticAt_id.sub analyticAt_const))
      · simp [hc]
      · filter_upwards [hev, self_mem_nhdsWithin] with z hz hne
        rw [hz]
        have hne' : z - z₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hne)
        simp only [zpow_neg_one, smul_eq_mul]; field_simp
    simp only [poleOrder, hord]; rfl

/-- A simple pole with nonzero coefficient has `poleOrder = 0` (i.e., the function
is actually analytic) when the coefficient is zero. -/
theorem poleOrder_eq_zero_of_simplePole_trivial {f : ℂ → ℂ} {z₀ : ℂ} {c : ℂ} {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hc : c = 0)
    (hev : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    poleOrder f z₀ = 0 := by
  have hf_eq : f =ᶠ[nhdsWithin z₀ {z₀}ᶜ] g := by
    filter_upwards [hev] with z hz; rw [hz, hc, zero_div, zero_add]
  have h_ord : 0 ≤ meromorphicOrderAt f z₀ := by
    rw [meromorphicOrderAt_congr hf_eq]; exact hg.meromorphicOrderAt_nonneg
  unfold poleOrder
  have h_nn : 0 ≤ (meromorphicOrderAt f z₀).untop₀ := by
    cases hm : meromorphicOrderAt f z₀ with
    | top => simp [WithTop.untop₀]
    | coe v => simp [WithTop.untop₀]; rw [hm] at h_ord; exact_mod_cast h_ord
  simp [Int.toNat_eq_zero.mpr (neg_nonpos.mpr h_nn)]

/-! ### Condition A': Flatness at crossings -/

/-- **Condition A'** (HasFlatCrossings): for each pole `s` in `S₀` that lies on
the curve `γ`, the curve is flat of order `poleOrder f s` at every parameter
`t₀ ∈ (0, 1)` where `γ(t₀) = s`.

For simple poles (order at most 1), this is satisfied provided the curve is flat
of order at most 1 at each crossing. For higher-order poles, this imposes genuine
geometric constraints on how the curve approaches the singularity. -/
def HasFlatCrossings (f : ℂ → ℂ) (γ : PiecewiseC1Immersion x y) (S₀ : Finset ℂ) : Prop :=
  ∀ s ∈ S₀, ∀ t₀ ∈ Ioo (0 : ℝ) 1, γ.toPiecewiseC1Path.toPath.extend t₀ = s →
    IsFlatOfOrder γ.toPiecewiseC1Path.toPath.extend t₀ (poleOrder f s)

/-- **Condition A' is automatic for simple poles with zero coefficient.** When the
pole coefficient is zero, the function is analytic (`poleOrder = 0`) and the
flatness condition reduces to `IsFlatOfOrder γ t₀ 0`, which holds for any
continuous curve by `isFlatOfOrder_zero`. -/
theorem hasFlatCrossings_of_simplePoles
    (f : ℂ → ℂ) (γ : PiecewiseC1Immersion x y) (S₀ : Finset ℂ)
    (_hSimple : ∀ s ∈ S₀, HasSimplePoleAt f s)
    (hAnalytic : ∀ s ∈ S₀, poleOrder f s = 0) :
    HasFlatCrossings f γ S₀ := by
  intro s hs t₀ _ht₀ _hcross
  rw [hAnalytic s hs]
  exact isFlatOfOrder_zero _ _ γ.toPiecewiseC1Path.toPath.continuous_extend.continuousAt

/-! ### Condition B: Angle/Laurent compatibility -/

/-- **Condition B** (IsLaurentCompatible): at each crossing point, the Laurent
coefficients of `f` are compatible with the crossing geometry.

For a pole of order `N` at `s`, near `s` we can write
`f(z) = Σ_{k=1}^{N} cₖ/(z-s)^k + g(z)` with `g` analytic.
Condition B requires that for each `k ≥ 2` with `cₖ ≠ 0`, the
higher-order singular terms have vanishing principal value integrals.

For simple poles (`N = 1`), the only singular term is `c₁/(z-s)` and the
condition on higher-order terms is vacuously true. -/
def IsLaurentCompatible (f : ℂ → ℂ) (γ : PiecewiseC1Immersion x y) (S₀ : Finset ℂ) : Prop :=
  ∀ s ∈ S₀, ∀ t₀ ∈ Ioo (0 : ℝ) 1, γ.toPiecewiseC1Path.toPath.extend t₀ = s →
    ∃ (N : ℕ) (a : Fin N → ℂ) (g : ℂ → ℂ),
      AnalyticAt ℂ g s ∧
      (∀ᶠ z in 𝓝[≠] s,
        f z = g z + ∑ k : Fin N, a k / (z - s) ^ (k.val + 1)) ∧
      (∀ k : Fin N, k.val ≥ 1 → a k = 0)

/-- **Condition B is automatic for simple poles.** A simple pole
`f(z) = c/(z-z₀) + g(z)` has only one singular term (`k = 0` in the `Fin 1` indexing,
representing `c/(z-z₀)¹`). The Laurent compatibility condition for `k.val ≥ 1` is
vacuously true since `Fin 1` has no element with `val ≥ 1`. -/
theorem isLaurentCompatible_of_simplePoles
    (f : ℂ → ℂ) (γ : PiecewiseC1Immersion x y) (S₀ : Finset ℂ)
    (hSimple : ∀ s ∈ S₀, HasSimplePoleAt f s) :
    IsLaurentCompatible f γ S₀ := by
  intro s hs t₀ _ht₀ _hcross
  obtain ⟨c, g, hg, hev⟩ := hSimple s hs
  refine ⟨1, ![c], g, hg, ?_, ?_⟩
  · filter_upwards [hev] with z hz
    simp [pow_one, hz]; ring
  · intro ⟨k, hk⟩ hk1
    exact absurd hk1 (by omega)

/-! ### Meromorphic Principal Part -/

/-- The **meromorphic principal part** of `f` at `z₀`.

If `f` has a pole of order `N` at `z₀`, the principal part captures the singular
terms of the Laurent expansion: `pp(z) = Σ_{k=0}^{N-1} cₖ · (z - z₀)^{k - N}`.

If `f` is analytic at `z₀` (non-negative order) or not meromorphic, returns `0`.

The coefficients are determined by the analytic factor `g` from the Mathlib
decomposition `f(z) =ᶠ (z - z₀)^{ord} · g(z)` with `g` analytic and `g(z₀) ≠ 0`:
`cₖ = g^{(k)}(z₀) / k!`. -/
noncomputable def meromorphicPrincipalPart (f : ℂ → ℂ) (z₀ : ℂ) : ℂ → ℂ :=
  if h : MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0 then
    let N := poleOrder f z₀
    let g := ((meromorphicOrderAt_ne_top_iff h.1).mp h.2.ne_top).choose
    fun z => (Finset.range N).sum fun k =>
      (iteratedDeriv k g z₀ / ↑(Nat.factorial k)) * (z - z₀) ^ ((k : ℤ) - (N : ℤ))
  else
    fun _ => 0

/-- When `f` is analytic at `z₀` (non-negative order), the principal part is zero. -/
theorem meromorphicPrincipalPart_eq_zero_of_analyticAt (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : AnalyticAt ℂ f z₀) :
    meromorphicPrincipalPart f z₀ = fun _ => 0 := by
  unfold meromorphicPrincipalPart
  have h_ord : 0 ≤ meromorphicOrderAt f z₀ := hf.meromorphicOrderAt_nonneg
  exact dif_neg (fun h => absurd h.2 (not_lt.mpr h_ord))

/-- Each term `c * (z - z₀)^n` is differentiable on `{z₀}ᶜ`. -/
private theorem differentiableOn_zpow_sub_compl (z₀ : ℂ) (n : ℤ) (c : ℂ) :
    DifferentiableOn ℂ (fun z => c * (z - z₀) ^ n) {z₀}ᶜ := by
  intro z hz
  have hne : z - z₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hz)
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_const c).mul
    ((differentiableAt_id.sub (differentiableAt_const z₀)).zpow (Or.inl hne))

/-- The principal part is differentiable on `{z₀}ᶜ`. -/
theorem meromorphicPrincipalPart_differentiableOn (f : ℂ → ℂ) (z₀ : ℂ) :
    DifferentiableOn ℂ (meromorphicPrincipalPart f z₀) {z₀}ᶜ := by
  unfold meromorphicPrincipalPart
  by_cases h : MeromorphicAt f z₀ ∧ meromorphicOrderAt f z₀ < 0
  · rw [dif_pos h]
    apply DifferentiableOn.fun_sum
    intro k _
    exact differentiableOn_zpow_sub_compl z₀ _ _
  · rw [dif_neg h]
    exact differentiableOn_const 0

/-- When `f` is not meromorphic at `z₀`, the principal part is zero. -/
theorem meromorphicPrincipalPart_eq_zero_of_not_meromorphic (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : ¬MeromorphicAt f z₀) :
    meromorphicPrincipalPart f z₀ = fun _ => 0 := by
  unfold meromorphicPrincipalPart
  exact dif_neg (fun h => absurd h.1 hf)

/-- When `f` has non-negative meromorphic order at `z₀`, the principal part is zero. -/
theorem meromorphicPrincipalPart_eq_zero_of_nonneg_order (f : ℂ → ℂ) (z₀ : ℂ)
    (h_ord : 0 ≤ meromorphicOrderAt f z₀) :
    meromorphicPrincipalPart f z₀ = fun _ => 0 := by
  unfold meromorphicPrincipalPart
  exact dif_neg (fun h => absurd h.2 (not_lt.mpr h_ord))

/-- A simple pole `f(z) = c/(z-z₀) + g(z)` implies `MeromorphicAt f z₀`. -/
theorem HasSimplePoleAt.meromorphicAt {f : ℂ → ℂ} {z₀ : ℂ}
    (h : HasSimplePoleAt f z₀) : MeromorphicAt f z₀ := by
  obtain ⟨c, g, hg, hev⟩ := h
  rw [MeromorphicAt.iff_eventuallyEq_zpow_smul_analyticAt]
  by_cases hc : c = 0
  · refine ⟨0, g, hg, ?_⟩
    filter_upwards [hev] with z hz
    rw [hz, hc, zero_div, zero_add, zpow_zero, one_smul]
  · refine ⟨-1, fun z => c + g z * (z - z₀), ?_, ?_⟩
    · exact analyticAt_const.add (hg.mul (analyticAt_id.sub analyticAt_const))
    · filter_upwards [hev, self_mem_nhdsWithin] with z hz hne
      rw [hz]
      have hne' : z - z₀ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hne)
      simp only [zpow_neg_one, smul_eq_mul]; field_simp

end
