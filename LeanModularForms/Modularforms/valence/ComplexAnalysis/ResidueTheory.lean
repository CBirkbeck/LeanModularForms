/-
Copyright (c) 2024. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import LeanModularForms.Modularforms.valence.ComplexAnalysis.Basic
import LeanModularForms.Modularforms.valence.ComplexAnalysis.PrincipalValue
import LeanModularForms.Modularforms.valence.ComplexAnalysis.WindingNumber

/-!
# Residue Theory and the Generalized Residue Theorem

This file develops the residue theorem using our principal value approach.
The key advantage is that contours can pass through singularities, giving
a more general statement than the classical theorem.

## Main Results

* `residue_simple_pole` - Residue computation for simple poles
* `residue_eq_contour_integral` - Residue via small circle integral
* `pv_integral_singular_part` - PV integral of singular part
* `generalizedResidueTheorem` - The main theorem

## References

* Isabelle: `Complex_Residues.thy` - `residue`, `residue_simple_pole`
* Isabelle: `Residue_Theorem.thy` - `Residue_theorem`
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped Real Interval

noncomputable section

/-! ## Multi-point Principal Value -/

/-- PV integrand excluding ε-neighborhoods of a finite set of points. -/
def cauchyPrincipalValueIntegrandOn
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (ε : ℝ) (t : ℝ) : ℂ :=
  if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then 0 else f (γ t) * deriv γ t

/-- The multi-point Cauchy principal value (exclude all s ∈ S). -/
def cauchyPrincipalValueOn
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε =>
    ∫ t in a..b, cauchyPrincipalValueIntegrandOn S f γ ε t

/-- Existence of the multi-point PV. -/
def CauchyPrincipalValueExistsOn
    (S : Finset ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∃ L : ℂ, Tendsto (fun ε =>
    ∫ t in a..b, cauchyPrincipalValueIntegrandOn S f γ ε t) (𝓝[>] 0) (𝓝 L)

/-! ## Helper Lemmas -/

lemma finite_of_discrete_inter_compact
    {S K : Set ℂ}
    (hS : ∀ s ∈ S, ∃ ε > 0, Metric.ball s ε ∩ S = {s})
    (hS_closed : IsClosed S)
    (hK : IsCompact K) :
    Set.Finite (S ∩ K) := by
  -- Step 1: Show S ∩ K is compact (closed subset of compact set)
  have h_inter_compact : IsCompact (S ∩ K) := hK.inter_left hS_closed
  -- Step 2: Show S ∩ K has discrete subspace topology (each point is isolated)
  have h_discrete : DiscreteTopology (S ∩ K).Elem := by
    rw [discreteTopology_subtype_iff]
    intro x hx
    obtain ⟨hx_S, _⟩ := hx
    obtain ⟨ε, hε_pos, hε_ball⟩ := hS x hx_S
    rw [Filter.inf_eq_bot_iff]
    refine ⟨Metric.ball x ε \ {x}, ?_, S ∩ K, Filter.mem_principal_self _, ?_⟩
    · rw [mem_nhdsWithin]
      exact ⟨Metric.ball x ε, Metric.isOpen_ball, Metric.mem_ball_self hε_pos,
             fun y ⟨hy_ball, hy_ne⟩ => ⟨hy_ball, hy_ne⟩⟩
    · ext z
      simp only [mem_inter_iff, mem_diff, mem_singleton_iff, mem_empty_iff_false, iff_false,
                 not_and, and_imp]
      intro hz_ball hz_ne hz_S hz_K
      have hz_in : z ∈ Metric.ball x ε ∩ S := ⟨hz_ball, hz_S⟩
      rw [hε_ball] at hz_in
      simp only [mem_singleton_iff] at hz_in
      exact hz_ne hz_in
  -- Step 3: Compact + discrete = finite
  exact h_inter_compact.finite h_discrete

lemma finite_singularities_on_curve
    (S : Set ℂ) (γ : PiecewiseC1Curve)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S) :
    Set.Finite (S ∩ γ.toFun '' Icc γ.a γ.b) := by
  -- Use finite_of_discrete_inter_compact after converting the discreteness condition
  have h_image_compact : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  -- Convert discreteness condition to ball form
  have hS_ball : ∀ s ∈ S, ∃ ε > 0, Metric.ball s ε ∩ S = {s} := by
    intro s hs
    obtain ⟨ε, hε_pos, hε_sep⟩ := hS_discrete s hs
    refine ⟨ε, hε_pos, ?_⟩
    ext z
    simp only [Metric.mem_ball, mem_inter_iff, mem_singleton_iff]
    constructor
    · intro ⟨hz_ball, hz_S⟩
      by_contra hz_ne
      have := hε_sep z hz_S hz_ne
      rw [dist_eq_norm] at hz_ball
      linarith
    · intro hz_eq
      rw [hz_eq]
      exact ⟨Metric.mem_ball_self hε_pos, hs⟩
  exact finite_of_discrete_inter_compact hS_ball hS_closed h_image_compact

lemma pv_eq_classical_when_avoids
    (f : ℂ → ℂ) (γ : PiecewiseC1Curve) (z₀ : ℂ)
    (havoid : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ z₀) :
    cauchyPrincipalValue' f γ.toFun γ.a γ.b z₀ =
      ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t := by
  unfold cauchyPrincipalValue'
  -- The curve γ avoids z₀, so there's a positive lower bound on distance
  have h_image_compact : IsCompact (γ.toFun '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn γ.continuous_toFun
  have h_z₀_not_in : z₀ ∉ γ.toFun '' Icc γ.a γ.b := by
    intro ⟨t, ht, htz₀⟩
    exact havoid t ht htz₀
  have h_closed : IsClosed (γ.toFun '' Icc γ.a γ.b) := h_image_compact.isClosed
  have h_ne : (γ.toFun '' Icc γ.a γ.b).Nonempty := by
    use γ.toFun γ.a
    exact ⟨γ.a, left_mem_Icc.mpr (le_of_lt γ.hab), rfl⟩
  have h_pos_dist : 0 < infDist z₀ (γ.toFun '' Icc γ.a γ.b) :=
    h_closed.notMem_iff_infDist_pos h_ne |>.mp h_z₀_not_in
  set δ := infDist z₀ (γ.toFun '' Icc γ.a γ.b) with hδ_def
  have h_dist_bound : ∀ t ∈ Icc γ.a γ.b, δ ≤ ‖γ.toFun t - z₀‖ := by
    intro t ht
    have h_in : γ.toFun t ∈ γ.toFun '' Icc γ.a γ.b := ⟨t, ht, rfl⟩
    calc δ = infDist z₀ (γ.toFun '' Icc γ.a γ.b) := rfl
      _ ≤ dist z₀ (γ.toFun t) := infDist_le_dist_of_mem h_in
      _ = ‖z₀ - γ.toFun t‖ := dist_eq_norm z₀ (γ.toFun t)
      _ = ‖γ.toFun t - z₀‖ := norm_sub_rev _ _
  -- For ε in (0, δ), the integral is the classical one
  have h_eq_eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∫ t in γ.a..γ.b, if ‖γ.toFun t - z₀‖ > ε then f (γ.toFun t) * deriv γ.toFun t else 0) =
      ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t := by
    rw [Filter.eventually_iff_exists_mem]
    use Ioo 0 δ
    constructor
    · rw [mem_nhdsWithin]
      refine ⟨Iio δ, isOpen_Iio, ?_, ?_⟩
      · simp only [mem_Iio]; exact h_pos_dist
      · intro x ⟨hx_lt_δ, hx_in_Ioi⟩
        simp only [mem_Ioi] at hx_in_Ioi
        exact ⟨hx_in_Ioi, hx_lt_δ⟩
    · intro ε ⟨hε_pos, hε_lt_δ⟩
      apply intervalIntegral.integral_congr
      intro t ht
      have ht' : t ∈ Icc γ.a γ.b := by
        simp only [uIcc, min_eq_left (le_of_lt γ.hab), max_eq_right (le_of_lt γ.hab)] at ht
        exact ht
      have hδ_le := h_dist_bound t ht'
      simp only [gt_iff_lt]
      rw [if_pos]
      linarith
  -- Tendsto of eventually constant function
  have h_tendsto : Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ‖γ.toFun t - z₀‖ > ε then f (γ.toFun t) * deriv γ.toFun t else 0)
      (𝓝[>] 0) (𝓝 (∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t)) := by
    apply Filter.Tendsto.congr'
    swap
    · exact tendsto_const_nhds
    · exact h_eq_eventually.mono fun _ h => h.symm
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact h_tendsto.limUnder_eq

lemma generalizedWindingNumber_comp
    (f : ℂ → ℂ) (γ : PiecewiseC1Curve)
    (hf : DifferentiableOn ℂ f (γ.toFun '' Icc γ.a γ.b))
    (hf_ne_zero : ∀ t ∈ Icc γ.a γ.b, f (γ.toFun t) ≠ 0) :
    generalizedWindingNumber' (fun t => f (γ.toFun t)) γ.a γ.b 0 =
      (2 * Real.pi * I)⁻¹ *
        ∫ t in γ.a..γ.b, deriv (fun t => f (γ.toFun t)) t / f (γ.toFun t) := by
  -- The composed curve f o gamma avoids 0 (by hf_ne_zero), so we can use the
  -- classical winding number formula.
  --
  -- Key insight: When a curve avoids a point, the generalized winding number
  -- equals the classical contour integral.
  --
  -- Define the composed curve
  set φ : ℝ → ℂ := fun t => f (γ.toFun t) with hφ_def
  -- Step 1: The image of the composed curve is compact and avoids 0
  have hφ_cont : ContinuousOn φ (Icc γ.a γ.b) := by
    apply ContinuousOn.comp hf.continuousOn γ.continuous_toFun
    intro t ht; exact mem_image_of_mem γ.toFun ht
  have h_image_compact : IsCompact (φ '' Icc γ.a γ.b) :=
    isCompact_Icc.image_of_continuousOn hφ_cont
  have h_nonempty : (φ '' Icc γ.a γ.b).Nonempty :=
    Set.image_nonempty.mpr (Set.nonempty_Icc.mpr (le_of_lt γ.hab))
  have h_ne_zero : ∀ w ∈ φ '' Icc γ.a γ.b, w ≠ 0 := by
    intro w ⟨t, ht, htw⟩
    rw [← htw, hφ_def]
    exact hf_ne_zero t ht
  -- Step 2: Find minimum distance from the curve to 0
  have hδ : ∃ δ > 0, ∀ t ∈ Icc γ.a γ.b, δ ≤ ‖φ t‖ := by
    have hclosed : IsClosed (φ '' Icc γ.a γ.b) := h_image_compact.isClosed
    have hz₀_notin : (0 : ℂ) ∉ φ '' Icc γ.a γ.b := fun hz₀ => h_ne_zero 0 hz₀ rfl
    have hdist_pos : 0 < Metric.infDist 0 (φ '' Icc γ.a γ.b) :=
      (hclosed.notMem_iff_infDist_pos h_nonempty).mp hz₀_notin
    refine ⟨Metric.infDist 0 (φ '' Icc γ.a γ.b), hdist_pos, fun t ht => ?_⟩
    have hmem : φ t ∈ φ '' Icc γ.a γ.b := mem_image_of_mem _ ht
    calc Metric.infDist 0 (φ '' Icc γ.a γ.b)
        ≤ dist 0 (φ t) := Metric.infDist_le_dist_of_mem hmem
      _ = ‖φ t‖ := by rw [Complex.dist_eq]; simp only [zero_sub, norm_neg]
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hδ
  -- Step 3: Use the definition and show the limit is the classical integral
  unfold generalizedWindingNumber' cauchyPrincipalValue'
  congr 1
  -- Simplify: φ t - 0 = φ t
  have h_sub_zero : ∀ t, (φ t - 0) = φ t := fun t => sub_zero (φ t)
  have h_sub_zero' : (fun t => φ t - 0) = φ := funext h_sub_zero
  -- The PV cutoff is eventually trivial
  have h_cutoff_trivial : ∀ᶠ ε in 𝓝[>] (0:ℝ), ∀ t ∈ Icc γ.a γ.b, ε < ‖φ t - 0‖ := by
    filter_upwards [Ioo_mem_nhdsGT hδ_pos] with ε hε t ht
    simp only [sub_zero]
    calc ε < δ := (mem_Ioo.mp hε).2
      _ ≤ ‖φ t‖ := hδ_bound t ht
  -- For small ε, the integrand equals (φ t)⁻¹ * deriv φ t
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  apply limUnder_eventually_eq_const
  simp only [sub_zero, gt_iff_lt]
  filter_upwards [h_cutoff_trivial] with ε hε
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Icc γ.a γ.b := by
    simp only [Set.uIcc_of_le (le_of_lt γ.hab)] at ht
    exact ht
  simp only [sub_zero] at hε ⊢
  rw [if_pos (hε t ht')]
  simp only [hφ_def, div_eq_mul_inv, mul_comm]

/-! ## Residue Definition and Basic Properties -/

/-- The residue of f at z₀, defined as the limit formula for simple poles.
    For a simple pole: res_{z₀}(f) = lim_{z→z₀} (z - z₀) · f(z)

    **Isabelle parallel**: `residue` in `Complex_Residues.thy` uses a similar
    characterization via contour integrals.
-/
def residueSimplePole (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[≠] z₀) fun z => (z - z₀) * f z

/-- The residue via Laurent series coefficient.
    res_{z₀}(f) = coefficient of (z - z₀)⁻¹ in the Laurent expansion.

    Note: For a full implementation, this would extract the (-1) coefficient
    from the Laurent series expansion of f at z₀. For simple poles,
    this coincides with `residueSimplePole`.
-/
def residueLaurent (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  -- For simple poles, use the limit definition which equals the Laurent coefficient
  residueSimplePole f z₀

/-- For simple poles, both definitions agree.

    **Isabelle parallel**: `residue_simple_pole` in `Complex_Residues.thy`
-/
theorem residue_simple_pole_eq_laurent
    (f : ℂ → ℂ) (z₀ : ℂ) (c : ℂ) (g : ℂ → ℂ)
    (hg : AnalyticAt ℂ g z₀)
    (hf : ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z) :
    residueSimplePole f z₀ = c := by
  unfold residueSimplePole
  -- lim_{z→z₀} (z - z₀) · (c/(z-z₀) + g(z)) = lim (c + (z-z₀)·g(z)) = c
  -- Step 1: Show (z - z₀) * f z = c + (z - z₀) * g z eventually
  have h_eq : (fun z => c + (z - z₀) * g z) =ᶠ[𝓝[≠] z₀] fun z => (z - z₀) * f z := by
    -- First get the membership in the punctured neighborhood
    have h_mem : ∀ᶠ z in 𝓝[≠] z₀, z ≠ z₀ := by
      rw [eventually_nhdsWithin_iff]
      filter_upwards with z hz
      simp only [mem_compl_iff, mem_singleton_iff] at hz
      exact hz
    filter_upwards [hf, h_mem] with z hz hz_ne
    rw [hz]
    have h_ne : z - z₀ ≠ 0 := sub_ne_zero.mpr hz_ne
    field_simp [h_ne]
  -- Step 2: Show lim (c + (z-z₀)·g(z)) = c
  have h_tendsto : Tendsto (fun z => c + (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 c) := by
    have h_sub : Tendsto (fun z => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
      have : Tendsto (fun z => z - z₀) (𝓝 z₀) (𝓝 0) := by
        have h_eq' : (0 : ℂ) = z₀ - z₀ := by ring
        rw [h_eq']
        exact tendsto_id.sub tendsto_const_nhds
      exact this.mono_left nhdsWithin_le_nhds
    have h_g : Tendsto g (𝓝[≠] z₀) (𝓝 (g z₀)) :=
      hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h_prod : Tendsto (fun z => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 0) := by
      have := h_sub.mul h_g
      simp only [zero_mul] at this
      exact this
    have h_const : Tendsto (fun _ : ℂ => c) (𝓝[≠] z₀) (𝓝 c) := tendsto_const_nhds
    convert h_const.add h_prod using 1
    simp only [add_zero]
  -- Step 3: The limUnder equals c
  have h_tendsto' : Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 c) :=
    h_tendsto.congr' h_eq
  exact h_tendsto'.limUnder_eq

/-- Residue via contour integral around a small circle.
    res_{z₀}(f) = (1/2πi) ∮_{|z-z₀|=ε} f(z) dz  for small ε

    **Isabelle parallel**: This is the definition in `Complex_Residues.thy`

    Note: This requires:
    - g(z) = (z - z₀) * f(z) is continuous on the punctured closed ball
    - g is differentiable on the punctured open ball
    - The limit L = lim_{z → z₀} g(z) exists

    These hold when f has a simple pole at z₀.
-/
theorem residue_eq_contour_integral
    (f : ℂ → ℂ) (z₀ : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hg_cont : ContinuousOn (fun z => (z - z₀) * f z) (Metric.closedBall z₀ ε \ {z₀}))
    (hg_diff : DifferentiableOn ℂ (fun z => (z - z₀) * f z) (Metric.ball z₀ ε \ {z₀}))
    (hL : ∃ L, Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 L)) :
    residueSimplePole f z₀ = (2 * Real.pi * I)⁻¹ * ∮ z in C(z₀, ε), f z := by
  /-
  Proof using mathlib's `circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto`:
  If g is continuous on closedBall c R \ {c}, differentiable on ball c R \ {c}, and
  has limit y at c, then ∮ (z - c)⁻¹ • g(z) dz = 2πi • y.

  Since (z - z₀)⁻¹ * g(z) = f(z) for z ≠ z₀, we get ∮ f = 2πi * L where L is the limit.
  -/
  obtain ⟨L, hL⟩ := hL
  -- The residue is L by definition
  have hres : residueSimplePole f z₀ = L := hL.limUnder_eq
  rw [hres]
  -- Helper: points in ball \ {z₀} have the punctured ball as a neighborhood
  have h_diff_at : ∀ z ∈ Metric.ball z₀ ε \ {z₀}, DifferentiableAt ℂ (fun z => (z - z₀) * f z) z := by
    intro z hz
    have hz_ball : z ∈ Metric.ball z₀ ε := hz.1
    have hz_ne : z ≠ z₀ := hz.2
    -- The set ball z₀ ε \ {z₀} is open (as difference of open and closed)
    have h_open : IsOpen (Metric.ball z₀ ε \ {z₀}) :=
      Metric.isOpen_ball.sdiff isClosed_singleton
    exact (hg_diff z hz).differentiableAt (h_open.mem_nhds hz)
  -- Apply mathlib's theorem
  -- hz : z ∈ (ball z₀ ε \ {z₀}) \ ∅, so hz.1 : z ∈ ball z₀ ε \ {z₀}
  -- and hz.1.1 : z ∈ ball z₀ ε, hz.1.2 : z ∉ {z₀}
  have h_key := circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto
    (c := z₀) (R := ε) (f := fun z => (z - z₀) * f z) (y := L) (s := ∅)
    hε (by simp) hg_cont (fun z hz => h_diff_at z ⟨hz.1.1, hz.1.2⟩) hL
  -- h_key : ∮ z in C(z₀, ε), (z - z₀)⁻¹ • ((z - z₀) * f z) = (2 * π * I) • L
  -- Show that (z - z₀)⁻¹ • ((z - z₀) * f z) = f z for z on the circle
  have h_integrand : Set.EqOn (fun z => (z - z₀)⁻¹ • ((z - z₀) * f z)) f (Metric.sphere z₀ ε) := by
    intro z hz
    have hz_ne : z ≠ z₀ := by
      intro heq
      rw [heq, Metric.mem_sphere, dist_self] at hz
      exact hε.ne hz
    simp only [smul_eq_mul]
    field_simp [sub_ne_zero.mpr hz_ne]
  -- The circle integral only depends on values on the sphere
  have h_eq : (∮ z in C(z₀, ε), (z - z₀)⁻¹ * ((z - z₀) * f z) : ℂ) = ∮ z in C(z₀, ε), f z := by
    have h_integrand' : Set.EqOn (fun z => (z - z₀)⁻¹ * ((z - z₀) * f z)) f (Metric.sphere z₀ ε) := by
      intro z hz
      have hz_ne : z ≠ z₀ := by
        intro heq
        rw [heq, Metric.mem_sphere, dist_self] at hz
        exact hε.ne hz
      field_simp [sub_ne_zero.mpr hz_ne]
    exact circleIntegral.integral_congr hε.le h_integrand'
  -- Convert smul to mul in h_key
  simp only [smul_eq_mul] at h_key
  rw [h_eq] at h_key
  -- h_key : ∮ z in C(z₀, ε), f z = (2 * π * I) * L
  -- L = (2πi)⁻¹ * ∮ f
  have h_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨by norm_num, by exact_mod_cast Real.pi_ne_zero⟩, Complex.I_ne_zero⟩
  field_simp [h_ne]
  -- h_key : ∮ f = 2 * π * I * L
  -- Goal: L * 2 * π * I = ∮ f (since multiplication is commutative in ℂ)
  calc L * 2 * Real.pi * I = 2 * Real.pi * I * L := by ring
    _ = ∮ z in C(z₀, ε), f z := h_key.symm

/-! ## Linearity of Residues -/

/-- Residue is additive.

    **Isabelle parallel**: Follows from `residue_add` in `Complex_Residues.thy`
-/
theorem residue_add (f g : ℂ → ℂ) (z₀ : ℂ)
    (hf : ∃ L, Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 L))
    (hg : ∃ L, Tendsto (fun z => (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 L)) :
    residueSimplePole (f + g) z₀ = residueSimplePole f z₀ + residueSimplePole g z₀ := by
  unfold residueSimplePole
  -- lim (z-z₀)·(f+g) = lim ((z-z₀)·f + (z-z₀)·g) = lim (z-z₀)·f + lim (z-z₀)·g
  -- First, rewrite the function pointwise
  have h_eq : (fun z => (z - z₀) * (f + g) z) =
              (fun z => (z - z₀) * f z + (z - z₀) * g z) := by
    ext z
    simp only [Pi.add_apply]
    ring
  simp only [h_eq]
  -- Now use that limUnder of sum equals sum of limits when both limits exist
  obtain ⟨Lf, hLf⟩ := hf
  obtain ⟨Lg, hLg⟩ := hg
  have h_sum : Tendsto (fun z => (z - z₀) * f z + (z - z₀) * g z) (𝓝[≠] z₀) (𝓝 (Lf + Lg)) :=
    hLf.add hLg
  rw [h_sum.limUnder_eq, hLf.limUnder_eq, hLg.limUnder_eq]

/-- Residue is homogeneous (when the limit exists).

    **Isabelle parallel**: `residue_cmult` in `Complex_Residues.thy`

    Note: This requires the limit defining the residue to exist.
    For simple poles, this is always satisfied.
-/
theorem residue_smul (c : ℂ) (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : ∃ L, Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 L)) :
    residueSimplePole (fun z => c * f z) z₀ = c * residueSimplePole f z₀ := by
  unfold residueSimplePole
  -- The key observation: (z - z₀) * (c * f z) = c * ((z - z₀) * f z)
  have h_eq : (fun z => (z - z₀) * (c * f z)) = (fun z => c * ((z - z₀) * f z)) := by
    ext z; ring
  simp only [h_eq]
  -- limUnder of (c * g) = c * limUnder of g when the limit exists
  obtain ⟨L, hL⟩ := hf
  -- limUnder (fun z => c * ((z - z₀) * f z)) = c * L
  have h_tendsto : Tendsto (fun z => c * ((z - z₀) * f z)) (𝓝[≠] z₀) (𝓝 (c * L)) :=
    hL.const_mul c
  rw [h_tendsto.limUnder_eq, hL.limUnder_eq]

/-- Residue is homogeneous for scalar 0. -/
theorem residue_smul_zero (f : ℂ → ℂ) (z₀ : ℂ) :
    residueSimplePole (fun z => (0 : ℂ) * f z) z₀ = 0 * residueSimplePole f z₀ := by
  simp only [zero_mul]
  unfold residueSimplePole
  have h_eq : (fun z => (z - z₀) * (fun z => (0 : ℂ)) z) = (fun _ => (0 : ℂ)) := by
    ext z; simp only [mul_zero]
  simp only [h_eq]
  have h_zero : Tendsto (fun _ : ℂ => (0 : ℂ)) (𝓝[≠] z₀) (𝓝 0) := tendsto_const_nhds
  exact h_zero.limUnder_eq

/-- Residue of a holomorphic function is zero.

    **Isabelle parallel**: `residue_holomorphic` in `Complex_Residues.thy`
-/
theorem residue_holomorphic (f : ℂ → ℂ) (z₀ : ℂ)
    (hf : AnalyticAt ℂ f z₀) :
    residueSimplePole f z₀ = 0 := by
  unfold residueSimplePole
  -- (z - z₀) · f(z) → 0 as z → z₀ for holomorphic f (since f is bounded near z₀)
  -- The limit exists and equals 0 because (z - z₀) → 0 and f(z) → f(z₀)
  have h_tendsto : Tendsto (fun z => (z - z₀) * f z) (𝓝[≠] z₀) (𝓝 0) := by
    -- Use that f is continuous at z₀ (from analyticity) and (z - z₀) → 0
    have hf_cont : ContinuousAt f z₀ := hf.continuousAt
    have h_sub : Tendsto (fun z => z - z₀) (𝓝[≠] z₀) (𝓝 0) := by
      have : Tendsto (fun z => z - z₀) (𝓝 z₀) (𝓝 0) := by
        have h_eq : (0 : ℂ) = z₀ - z₀ := by ring
        rw [h_eq]
        exact tendsto_id.sub tendsto_const_nhds
      exact this.mono_left nhdsWithin_le_nhds
    have h_f : Tendsto f (𝓝[≠] z₀) (𝓝 (f z₀)) :=
      hf_cont.tendsto.mono_left nhdsWithin_le_nhds
    -- (z - z₀) * f(z) → 0 * f(z₀) = 0
    have := h_sub.mul h_f
    simp only [zero_mul] at this
    exact this
  -- The limUnder equals the limit value when the limit exists
  exact h_tendsto.limUnder_eq

/-! ## PV Integral of Singular Part -/

/-- The PV integral of 1/(z - z₀) equals 2πi times the winding number.

    This is the key calculation connecting residues to winding numbers.
-/
theorem pv_integral_inverse
    (γ : PiecewiseC1Curve) (z₀ : ℂ) :
    cauchyPrincipalValue' (·⁻¹) (fun t => γ.toFun t - z₀) γ.a γ.b 0 =
    2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b z₀ := by
  -- Follows directly from the definition of generalizedWindingNumber'
  -- generalizedWindingNumber' γ a b z₀ = (2πi)⁻¹ * PV ∮_{γ-z₀} (·)⁻¹
  -- So PV ∮_{γ-z₀} (·)⁻¹ = 2πi * generalizedWindingNumber'
  unfold generalizedWindingNumber'
  -- Now the goal is: PV = 2πi * ((2πi)⁻¹ * PV) = PV
  have h_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    constructor
    constructor
    · norm_num
    · exact_mod_cast Real.pi_ne_zero
    · exact Complex.I_ne_zero
  field_simp [h_ne]

/-- The PV integral of c/(z - z₀) for simple poles.

    PV ∮_γ c/(z - z₀) dz = 2πi · n_{z₀}(γ) · c = 2πi · n_{z₀}(γ) · res_{z₀}(c/(z-z₀))

    Note: This requires the PV limit of the base integral (·)⁻¹ to exist, which holds
    for piecewise C¹ curves that intersect {z₀} transversally.
-/
theorem pv_integral_simple_pole
    (γ : PiecewiseC1Curve) (z₀ c : ℂ)
    (hPV : ∃ L, Tendsto (fun ε => ∫ t in γ.a..γ.b,
      if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
      then (·⁻¹) ((fun s => γ.toFun s - z₀) t) * deriv (fun s => γ.toFun s - z₀) t else 0)
      (𝓝[>] 0) (𝓝 L)) :
    cauchyPrincipalValue' (fun z => c / (z - z₀)) γ.toFun γ.a γ.b z₀ =
    2 * Real.pi * I * generalizedWindingNumber' γ.toFun γ.a γ.b z₀ * c := by
  -- Key: 2πi ≠ 0
  have h_ne : (2 * Real.pi * I : ℂ) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, not_or]
    exact ⟨⟨by norm_num, by exact_mod_cast Real.pi_ne_zero⟩, Complex.I_ne_zero⟩
  -- Use pv_integral_inverse which says:
  -- cauchyPrincipalValue' (·⁻¹) (fun t => γ.toFun t - z₀) γ.a γ.b 0 = 2πi * n_{z₀}(γ)
  have h_inv := pv_integral_inverse γ z₀
  -- Rewrite RHS using h_inv
  rw [← h_inv]
  -- Goal now: PV(c/(z-z₀)) γ z₀ = PV(·⁻¹) (γ - z₀) 0 * c
  -- Both sides are equal by showing the integrands match
  unfold cauchyPrincipalValue'
  -- The derivative fact: d/dt(γ(t) - z₀) = d/dt γ(t)
  have h_deriv_eq : ∀ t, deriv (fun s => γ.toFun s - z₀) t = deriv γ.toFun t := by
    intro t; exact deriv_sub_const (x := t) (c := z₀)
  -- Show the integrands are equal up to factor c
  have h_integrand' : ∀ ε t,
      (if ‖γ.toFun t - z₀‖ > ε then (fun z => c / (z - z₀)) (γ.toFun t) * deriv γ.toFun t else 0) =
      (if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
        then (·⁻¹) ((fun s => γ.toFun s - z₀) t) * deriv (fun s => γ.toFun s - z₀) t else 0) * c := by
    intro ε t
    simp only [sub_zero]
    rw [h_deriv_eq]
    split_ifs with h
    · rw [div_eq_mul_inv]; ring
    · ring
  have h_integral' : ∀ ε,
      (∫ t in γ.a..γ.b, if ‖γ.toFun t - z₀‖ > ε then (fun z => c / (z - z₀)) (γ.toFun t) * deriv γ.toFun t else 0) =
      (∫ t in γ.a..γ.b, if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
        then (·⁻¹) ((fun s => γ.toFun s - z₀) t) * deriv (fun s => γ.toFun s - z₀) t else 0) * c := by
    intro ε
    rw [← intervalIntegral.integral_mul_const]
    apply intervalIntegral.integral_congr
    intro t _
    exact h_integrand' ε t
  simp_rw [h_integral']
  -- Now goal is: limUnder (f * c) = limUnder f * c where limit of f exists by hPV
  obtain ⟨L, hL⟩ := hPV
  -- The limit of (f * c) is L * c by continuity of multiplication
  have h_mul : Tendsto (fun ε => (∫ t in γ.a..γ.b,
      if ‖(fun s => γ.toFun s - z₀) t - 0‖ > ε
      then (·⁻¹) ((fun s => γ.toFun s - z₀) t) * deriv (fun s => γ.toFun s - z₀) t else 0) * c)
      (𝓝[>] 0) (𝓝 (L * c)) := hL.mul_const c
  rw [h_mul.limUnder_eq, hL.limUnder_eq]

/-! ## The Generalized Residue Theorem -/

/-- A function has a simple pole at z₀ if it can be written as c/(z-z₀) + g(z)
    where g is holomorphic near z₀. -/
def HasSimplePoleAt (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ c : ℂ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z₀ ∧
    ∀ᶠ z in 𝓝[≠] z₀, f z = c / (z - z₀) + g z

/-- The coefficient in a simple pole decomposition is unique.
    This follows because the residue is uniquely determined by the limit formula. -/
theorem simple_pole_coeff_unique (f : ℂ → ℂ) (z₀ : ℂ)
    (c₁ c₂ : ℂ) (g₁ g₂ : ℂ → ℂ)
    (hg₁ : AnalyticAt ℂ g₁ z₀) (hg₂ : AnalyticAt ℂ g₂ z₀)
    (hf₁ : ∀ᶠ z in 𝓝[≠] z₀, f z = c₁ / (z - z₀) + g₁ z)
    (hf₂ : ∀ᶠ z in 𝓝[≠] z₀, f z = c₂ / (z - z₀) + g₂ z) :
    c₁ = c₂ := by
  have h₁ := residue_simple_pole_eq_laurent f z₀ c₁ g₁ hg₁ hf₁
  have h₂ := residue_simple_pole_eq_laurent f z₀ c₂ g₂ hg₂ hf₂
  -- h₁ : residueSimplePole f z₀ = c₁
  -- h₂ : residueSimplePole f z₀ = c₂
  rw [← h₁, h₂]

/-- Extract the residue from a simple pole decomposition. -/
theorem residue_of_simple_pole (f : ℂ → ℂ) (z₀ : ℂ) (hf : HasSimplePoleAt f z₀) :
    residueSimplePole f z₀ = Classical.choose hf := by
  -- Get the decomposition from Classical.choose_spec
  have hspec := Classical.choose_spec hf
  obtain ⟨g, hg, hf_eq⟩ := hspec
  -- Apply residue_simple_pole_eq_laurent
  exact residue_simple_pole_eq_laurent f z₀ (Classical.choose hf) g hg hf_eq

/-- The Generalized Residue Theorem.

    **Theorem**: Let f be meromorphic on U with isolated singularities S.
    For a closed piecewise C¹ curve γ in U (possibly passing through singularities),
    if all singularities on γ are simple poles, then:

    PV ∮_γ f = 2πi · Σ_{s ∈ S} n_s(γ) · res_s(f)

    **Isabelle parallel**: `Residue_theorem` in `Residue_Theorem.thy`

    The key difference: Isabelle requires γ to avoid all singularities.
    Our PV approach allows γ to pass through simple poles.

    **Proof Strategy**:
    1. Decompose f = Σ_s (singular part at s) + (holomorphic part)
    2. PV ∮ (holomorphic) = ∮ (holomorphic) = 0 by Cauchy
    3. PV ∮ (c_s/(z-s)) = 2πi · n_s(γ) · c_s by pv_integral_simple_pole
    4. Sum over all singularities
-/
-- NOTE: Previous version used `cauchyPrincipalValue' f γ a b 0`, which only cuts out
-- a neighborhood of 0 and is wrong when the contour meets multiple singularities.
-- The corrected statement uses a finite set `S0` of singularities on the contour.
theorem generalizedResidueTheorem'
    (U : Set ℂ) (hU : IsOpen U)
    (S : Set ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (hS_discrete : ∀ s ∈ S, ∃ ε > 0, ∀ s' ∈ S, s' ≠ s → ε ≤ ‖s' - s‖)
    (hS_closed : IsClosed S)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S))
    (γ : PiecewiseC1Curve) (hγ_closed : γ.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (S0 : Finset ℂ)
    (hS0_subset : ∀ s ∈ S0, s ∈ S)
    (hS_on_curve : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ S → γ.toFun t ∈ S0)
    (hSimplePoles : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t = s → HasSimplePoleAt f s) :
    CauchyPrincipalValueExistsOn S0 f γ.toFun γ.a γ.b ∧
    cauchyPrincipalValueOn S0 f γ.toFun γ.a γ.b =
      2 * Real.pi * I * ∑ s ∈ S0, generalizedWindingNumber' γ.toFun γ.a γ.b s *
        residueSimplePole f s := by
  constructor
  · -- PV exists: decompose into singular and regular parts
    --
    -- PROOF OUTLINE (requires substantial infrastructure not yet in mathlib):
    --
    -- The curve γ intersects S at finitely many points (by finite_singularities_on_curve).
    -- At each singularity s ∈ S0, f has a simple pole: f(z) = c_s/(z-s) + g_s(z)
    -- where g_s is holomorphic near s.
    --
    -- The multi-point PV integral exists because:
    -- 1. Away from S0, f is holomorphic, so the integrand f(γ(t)) * γ'(t) is continuous
    -- 2. Near each singularity s ∈ S0:
    --    - The singular part c_s/(z-s) contributes a log-type integral
    --    - The symmetric ε-excision ensures log divergences cancel
    --    - The model sector calculation (generalizedWindingNumber_modelSector') shows
    --      the PV contribution is finite
    -- 3. The regular parts g_s are continuous, contributing finite integrals
    -- 4. By linearity, the sum of finitely many existing limits exists
    --
    -- REQUIRED INFRASTRUCTURE:
    -- - Decomposition of meromorphic functions at simple poles
    -- - Local Taylor expansion of γ near crossing points
    -- - Dominated convergence for multi-point PV
    -- - Extension of pv_integral_simple_pole to multi-point case
    sorry
  · -- The formula
    --
    -- PROOF OUTLINE:
    --
    -- Step 1: The set S ∩ γ([a,b]) is finite (discrete singularities meet compact curve)
    have h_image_compact : IsCompact (γ.toFun '' Icc γ.a γ.b) := by
      exact isCompact_Icc.image_of_continuousOn γ.continuous_toFun
    have h_finite_intersection : Set.Finite (S ∩ γ.toFun '' Icc γ.a γ.b) :=
      finite_singularities_on_curve S γ hS_discrete hS_closed
    --
    -- Step 2: Decompose f near each singularity s ∈ S0:
    --         f(z) = c_s/(z-s) + g_s(z) where c_s = res_s(f) and g_s is holomorphic
    --
    -- Step 3: Split the multi-point PV integral:
    --         PV ∮_γ f = Σ_{s ∈ S0} PV ∮_γ (c_s/(z-s)) + PV ∮_γ (Σ_s g_s)
    --
    -- Step 4: For each singular part, apply the model sector result:
    --         PV ∮_γ (c_s/(z-s)) = 2πi · n_s(γ) · c_s
    --         This follows from pv_integral_simple_pole
    --
    -- Step 5: The holomorphic remainder Σ_s g_s contributes 0 by Cauchy's theorem
    --         (the curve is closed and the function is holomorphic on U \ S)
    --
    -- Step 6: Sum the contributions:
    --         PV ∮_γ f = Σ_{s ∈ S0} 2πi · n_s(γ) · res_s(f)
    --
    -- REQUIRED INFRASTRUCTURE:
    -- - Cauchy's theorem for closed curves (from HomotopyBridge or mathlib)
    -- - Linearity of multi-point PV integrals
    -- - Connection between HasSimplePoleAt decomposition and residueSimplePole
    sorry

/-! ## Corollaries -/

/-- Classical residue theorem: when γ avoids all singularities.

    This is the special case where all winding numbers are integers.
-/
theorem classicalResidueTheorem
    (U : Set ℂ) (hU : IsOpen U)
    (S : Finset ℂ) (hS_in_U : ∀ s ∈ S, s ∈ U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (U \ S))
    (γ : PiecewiseC1Curve) (hγ_closed : γ.IsClosed)
    (hγ_in_U : ∀ t ∈ Icc γ.a γ.b, γ.toFun t ∈ U)
    (hγ_avoids_S : ∀ s ∈ S, ∀ t ∈ Icc γ.a γ.b, γ.toFun t ≠ s) :
    ∫ t in γ.a..γ.b, f (γ.toFun t) * deriv γ.toFun t =
      2 * Real.pi * I * ∑ s ∈ S, generalizedWindingNumber' γ.toFun γ.a γ.b s *
        residueSimplePole f s := by
  -- PROOF OUTLINE:
  --
  -- This is the classical residue theorem for curves that avoid all singularities.
  -- When γ avoids S, the generalized winding numbers are all integers (by
  -- generalizedWindingNumber_eq_classical'), so this reduces to the standard
  -- residue theorem.
  --
  -- Key steps:
  -- 1. For each s ∈ S, since γ avoids s, we can apply pv_eq_classical_when_avoids
  --    to show PV integrals equal classical integrals
  --
  -- 2. The classical residue theorem states:
  --    ∮_γ f(z) dz = 2πi · Σ_{s ∈ S} n_s(γ) · res_s(f)
  --    where n_s(γ) is the classical (integer) winding number
  --
  -- 3. By generalizedWindingNumber_eq_classical_away, the generalized winding number
  --    equals the classical one when γ avoids s
  --
  -- REQUIRED INFRASTRUCTURE (not yet in mathlib):
  -- - Classical residue theorem connecting contour integrals to residues
  -- - Mathlib's complex analysis library has Cauchy's integral formula
  --   (circleIntegral_sub_center_inv_smul_of_differentiable_on_off_countable_of_tendsto)
  --   but the full residue theorem for general closed curves requires more
  -- - Connection between residueSimplePole and the coefficient in pole decomposition
  --
  -- Note: pv_eq_classical_when_avoids shows that when γ avoids z₀:
  --   cauchyPrincipalValue' f γ.toFun γ.a γ.b z₀ = ∫ f(γ(t)) * γ'(t) dt
  -- This would be used to reduce the multi-point case to single-point PV integrals.
  sorry

/-- Argument principle: the winding number of f ∘ γ around 0 counts zeros minus poles.

    **Isabelle parallel**: Part of `Residue_Theorem.thy`
-/
-- NOTE: Previous version incorrectly claimed `winding(f ∘ γ) = winding(γ)`.
-- The corrected statement expresses the winding of `f ∘ γ` as the integral of `f'/f`.
theorem argumentPrinciple
    (f : ℂ → ℂ) (γ : PiecewiseC1Curve) (hγ_closed : γ.IsClosed)
    (hf : DifferentiableOn ℂ f (γ.toFun '' Icc γ.a γ.b))
    (hf_ne_zero : ∀ t ∈ Icc γ.a γ.b, f (γ.toFun t) ≠ 0) :
    generalizedWindingNumber' (fun t => f (γ.toFun t)) γ.a γ.b 0 =
      (2 * Real.pi * I)⁻¹ *
        ∫ t in γ.a..γ.b, deriv (fun t => f (γ.toFun t)) t / f (γ.toFun t) := by
  -- This follows directly from the generalizedWindingNumber_comp lemma
  exact generalizedWindingNumber_comp f γ hf hf_ne_zero

end
