/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.ForMathlib.HomotopyDefs
import LeanModularForms.ForMathlib.PiecewiseContourIntegral
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Complex.Norm

/-!
# Winding Number Homotopy Invariance

The generalized winding number is invariant under piecewise C^1
homotopy avoiding the base point `z_0`.

## Main results

* `continuous_integer_valued_constant` -- a continuous function from `[0, 1]` to
  `Complex` that takes only integer values satisfies `f 0 = f 1`.

* `generalizedWindingNumber01_eq_of_eq_on` -- the winding number on `[0, 1]`
  depends only on the values and derivatives of the curve a.e.

* `windingNumber_eq_of_piecewise_homotopic` -- winding number invariance under
  piecewise C^1 homotopy, given parametric continuity and integrality hypotheses.

## Proof strategy

The proof of homotopy invariance follows three steps:
1. **Continuity**: `s -> n(H(., s), z_0)` is continuous on `[0, 1]`.
2. **Integrality**: each `n(H(., s), z_0)` is an integer (winding number of a closed
   curve avoiding `z_0`).
3. **Constant**: a continuous integer-valued function on a connected set is constant.

Steps 1 and 2 are substantial results in their own right (parametric dominated
convergence for step 1, the exponential trick for step 2). They are provided as
hypotheses to the main theorem via `WindingNumberHomotopyData`.

## Design notes

The winding number `generalizedWindingNumber01` is defined locally as the `[0, 1]`
specialization of the Cauchy principal value formula. This avoids an import conflict
between `ForMathlib.PiecewiseC1Path` (imported by `HomotopyDefs`) and
`GeneralizedResidueTheory.Basic`, which both define `PwC1Immersion`.

## References

* K. Hungerbuhler, J. Wasem, *A generalized notion of winding numbers*
-/

open Set Filter Topology Complex MeasureTheory
open scoped Real Interval

noncomputable section

/-! ### Generalized winding number on [0, 1] -/

/-- The generalized winding number of `gamma` around `z_0` on `[0, 1]`, defined via
the Cauchy principal value of the log-derivative integral.

This is the `[0, 1]`-specialization of `generalizedWindingNumber'` from
`GeneralizedResidueTheory.Basic`, reproduced here to avoid an import conflict. -/
def generalizedWindingNumber01 (γ : ℝ → ℂ) (z₀ : ℂ) : ℂ :=
  (2 * ↑Real.pi * I)⁻¹ * limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in (0 : ℝ)..1, if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0

/-! ### Auxiliary: limUnder of an eventually constant function -/

private theorem limUnder_eventually_eq_const {f : ℝ → ℂ} {l : Filter ℝ} {c : ℂ} [l.NeBot]
    (h : ∀ᶠ x in l, f x = c) : l.limUnder f = c := by
  have htend : Tendsto f l (nhds c) := by
    rw [Filter.tendsto_congr' (h.mono (fun _ hx => by rw [hx]))]
    exact tendsto_const_nhds
  exact htend.limUnder_eq

/-! ### Continuous integer-valued functions are constant on [0, 1] -/

/-- A continuous function from `[0, 1]` to `Complex` that takes only integer values
satisfies `f 0 = f 1`. The proof uses the fact that `Z` inside `Complex` is discrete
(distinct integers have distance at least 1), so a continuous preimage of a singleton
equals the preimage of an open ball, making `f` locally constant. Since `[0, 1]` is
connected, a locally constant function is constant. -/
theorem continuous_integer_valued_constant (f : ℝ → ℂ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (hf_int : ∀ s ∈ Icc (0 : ℝ) 1, ∃ n : ℤ, f s = n) :
    f 0 = f 1 := by
  let g : Icc (0 : ℝ) 1 → ℂ := fun x => f x.val
  have hg_loc : IsLocallyConstant g := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro y
    by_cases hy : ∃ n : ℤ, y = n
    · obtain ⟨n, rfl⟩ := hy
      have heq : g ⁻¹' {↑n} = g ⁻¹' (Metric.ball (n : ℂ) 1) := by
        ext ⟨x, hx⟩
        simp only [g, mem_preimage, mem_singleton_iff, Metric.mem_ball]
        constructor
        · intro heq
          rw [heq]
          simp only [dist_self, zero_lt_one]
        · intro hdist
          obtain ⟨m, hm⟩ := hf_int x hx
          rw [hm] at hdist ⊢
          have h1 : dist (m : ℂ) (n : ℂ) < 1 := hdist
          have hsub : (m : ℂ) - (n : ℂ) = ((m - n : ℤ) : ℂ) := by
            push_cast
            ring
          rw [Complex.dist_eq, hsub, Complex.norm_intCast, ← Int.cast_abs] at h1
          have h2 : |m - n| < 1 := by exact_mod_cast h1
          have h3 : m - n = 0 := Int.abs_lt_one_iff.mp h2
          exact_mod_cast sub_eq_zero.mp h3
      rw [heq]
      exact hf_cont.restrict.isOpen_preimage _ Metric.isOpen_ball
    · convert isOpen_empty
      ext ⟨x, hx⟩
      simp only [g, mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      intro heq
      obtain ⟨n, hn⟩ := hf_int x hx
      exact hy ⟨n, heq.symm.trans hn⟩
  have h0 : (⟨0, left_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩ :
      Icc (0 : ℝ) 1) ∈ (Set.univ : Set (Icc (0 : ℝ) 1)) := trivial
  have h1 : (⟨1, right_mem_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)⟩ :
      Icc (0 : ℝ) 1) ∈ (Set.univ : Set (Icc (0 : ℝ) 1)) := trivial
  exact hg_loc.apply_eq_of_isPreconnected isPreconnected_univ h0 h1

/-! ### Winding number depends only on values and derivatives a.e. -/

/-- The generalized winding number on `[0, 1]` depends only on pointwise values on
`[0, 1]` and derivatives a.e. on `(0, 1]`. -/
theorem generalizedWindingNumber01_eq_of_eq_on
    (f g : ℝ → ℂ) (z₀ : ℂ)
    (heq_val : ∀ t ∈ Icc (0 : ℝ) 1, f t = g t)
    (heq_deriv : ∀ᵐ t ∂volume.restrict (Set.uIoc 0 1), deriv f t = deriv g t) :
    generalizedWindingNumber01 f z₀ = generalizedWindingNumber01 g z₀ := by
  unfold generalizedWindingNumber01
  congr 1
  congr 1
  funext ε
  apply intervalIntegral.integral_congr_ae
  have h_uIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := Set.uIoc_of_le zero_le_one
  simp only [h_uIoc] at heq_deriv ⊢
  rw [ae_restrict_iff' measurableSet_Ioc] at heq_deriv
  filter_upwards [heq_deriv] with t ht ht_mem
  have ht_Icc : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht_mem
  rw [heq_val t ht_Icc, ht ht_mem]

/-! ### Homotopy invariance hypotheses -/

/-- Data bundle for the two substantial hypotheses needed for winding number
homotopy invariance: parametric continuity and integrality.

* **Parametric continuity** follows from dominated convergence and piecewise
  continuity of the integrand (uniform derivative bounds).
* **Integrality** follows from the exponential trick: `exp(integral of gamma'/
  (gamma - z_0))` has constant ratio with `gamma - z_0`, so the integral over a
  closed curve is `2 pi i` times an integer. -/
structure WindingNumberHomotopyData (z₀ : ℂ) (P : Finset ℝ) where
  /-- Parametric continuity: for any homotopy `H` satisfying the regularity conditions,
  the map `s -> gWN(H(., s), z_0)` is continuous on `[0, 1]`. -/
  parametric_continuity :
    ∀ H : ℝ × ℝ → ℂ,
      Continuous H →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀) →
      (∀ t ∈ Ioo (0 : ℝ) 1, t ∉ P →
        ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t) →
      (∀ p₁ p₂ : ℝ, p₁ < p₂ →
        (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo (0 : ℝ) 1 →
        ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
          (Ioo p₁ p₂ ×ˢ Icc 0 1)) →
      (∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖deriv (fun t' => H (t', s)) t‖ ≤ M) →
      ContinuousOn
        (fun s => generalizedWindingNumber01 (fun t => H (t, s)) z₀)
        (Icc 0 1)
  /-- Integrality: the winding number of any closed continuous curve avoiding `z_0`
  is an integer. -/
  integrality :
    ∀ (γ : ℝ → ℂ),
      (γ 0 = γ 1) →
      Continuous γ →
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z₀) →
      ∃ m : ℤ, generalizedWindingNumber01 γ z₀ = m

/-! ### Main theorem: homotopy invariance -/

/-- If a homotopy `H(t, s)` agrees with `γ` on `[0, 1]`, their winding numbers coincide. -/
private theorem gWN01_eq_of_homotopy_slice (H : ℝ × ℝ → ℂ) (γ : ℝ → ℂ)
    (z₀ : ℂ) (s : ℝ) (heq : ∀ t ∈ Icc (0 : ℝ) 1, H (t, s) = γ t) :
    generalizedWindingNumber01 (fun t => H (t, s)) z₀ =
    generalizedWindingNumber01 γ z₀ := by
  apply generalizedWindingNumber01_eq_of_eq_on (fun t => H (t, s)) γ z₀ heq
  rw [Set.uIoc_of_le zero_le_one]
  have h_eq_on_Ioo : EqOn (fun t => H (t, s)) γ (Ioo 0 1) :=
    fun t' ht' => heq t' (Ioo_subset_Icc_self ht')
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [Ioo_ae_eq_Ioc.mem_iff] with t ht ht_Ioc
  exact h_eq_on_Ioo.deriv isOpen_Ioo (ht.mpr ht_Ioc)

/-- **Winding number homotopy invariance** (with explicit hypotheses).

Given a piecewise C^1 homotopy `H` from `gamma_0` to `gamma_1` avoiding `z_0`,
together with parametric continuity and integrality of the winding number,
we conclude `n(gamma_0, z_0) = n(gamma_1, z_0)`.

The proof implements the standard three-step argument:
1. Define `n(s) = winding number of H(., s) around z_0`.
2. Show `n` is continuous (hypothesis) and integer-valued (hypothesis).
3. Apply `continuous_integer_valued_constant` to conclude `n(0) = n(1)`.
4. Use `generalizedWindingNumber01_eq_of_eq_on` to identify `n(0) = n(gamma_0, z_0)`
   and `n(1) = n(gamma_1, z_0)`. -/
theorem windingNumber_eq_of_piecewise_homotopic_of_hyps
    (γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) (P : Finset ℝ)
    (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ P)
    (hn_cont : ∀ H : ℝ × ℝ → ℂ,
      Continuous H →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, H (t, s) ≠ z₀) →
      (∀ t ∈ Ioo (0 : ℝ) 1, t ∉ P →
        ∀ s ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (fun t' => H (t', s)) t) →
      (∀ p₁ p₂ : ℝ, p₁ < p₂ →
        (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo (0 : ℝ) 1 →
        ContinuousOn (fun (p : ℝ × ℝ) => deriv (fun t' => H (t', p.2)) p.1)
          (Ioo p₁ p₂ ×ˢ Icc 0 1)) →
      (∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖deriv (fun t' => H (t', s)) t‖ ≤ M) →
      ContinuousOn
        (fun s => generalizedWindingNumber01 (fun t => H (t, s)) z₀)
        (Icc 0 1))
    (hn_int : ∀ (γ : ℝ → ℂ),
      (γ 0 = γ 1) →
      Continuous γ →
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ z₀) →
      ∃ m : ℤ, generalizedWindingNumber01 γ z₀ = m) :
    generalizedWindingNumber01 γ₀ z₀ =
    generalizedWindingNumber01 γ₁ z₀ := by
  obtain ⟨H, hH_cont, hH0, hH1, hH_closed, hH_avoid, hH_diff, hH_deriv_cont,
    M, hM_bound⟩ := hhom
  let n : ℝ → ℂ := fun s => generalizedWindingNumber01 (fun t => H (t, s)) z₀
  have h_n_cont : ContinuousOn n (Icc 0 1) :=
    hn_cont H hH_cont hH_avoid hH_diff hH_deriv_cont ⟨M, hM_bound⟩
  have h_n_int : ∀ s ∈ Icc (0 : ℝ) 1, ∃ m : ℤ, n s = m := fun s hs =>
    hn_int (fun t => H (t, s))
      (hH_closed s hs)
      (hH_cont.comp (continuous_id.prodMk continuous_const))
      (fun t ht => hH_avoid t ht s hs)
  have h_n_const : n 0 = n 1 :=
    continuous_integer_valued_constant n h_n_cont h_n_int
  have hn0 := gWN01_eq_of_homotopy_slice H γ₀ z₀ 0 hH0
  have hn1 := gWN01_eq_of_homotopy_slice H γ₁ z₀ 1 hH1
  rw [← hn0, ← hn1]
  exact h_n_const

/-- **Winding number homotopy invariance** -- the main theorem, bundled.

If `gamma_0` and `gamma_1` are piecewise-homotopic avoiding `z_0` and the winding number
satisfies parametric continuity and integrality (bundled in `WindingNumberHomotopyData`),
then the winding numbers agree. -/
theorem windingNumber_eq_of_piecewise_homotopic
    (γ₀ γ₁ : ℝ → ℂ) (z₀ : ℂ) (P : Finset ℝ)
    (hhom : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ z₀ P)
    (hdata : WindingNumberHomotopyData z₀ P) :
    generalizedWindingNumber01 γ₀ z₀ =
    generalizedWindingNumber01 γ₁ z₀ :=
  windingNumber_eq_of_piecewise_homotopic_of_hyps γ₀ γ₁ z₀ P hhom
    hdata.parametric_continuity hdata.integrality

end
