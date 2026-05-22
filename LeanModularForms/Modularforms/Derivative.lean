module

public import LeanModularForms.Modularforms.MDifferentiableFunProp

public import LeanModularForms.Modularforms.Eisenstein
public import Mathlib.Analysis.Calculus.DiffContOnCl

@[expose] public section

open UpperHalfPlane hiding I
open Real Complex CongruenceSubgroup SlashAction SlashInvariantForm ContinuousMap
open Metric Filter Function

open scoped ModularForm MatrixGroups Manifold Topology BigOperators

-- In mathlib 4.29, NormSMulClass.toIsBoundedSMul is not an instance (to avoid loops),
-- which breaks the chain NormedSpace ℝ ℂ → ContinuousSMul ℝ ℂ. Provide it locally.
noncomputable instance : NormSMulClass ℝ ℂ := NormedSpace.toNormSMulClass
noncomputable instance : IsBoundedSMul ℝ ℂ := NormSMulClass.toIsBoundedSMul

/-- Constant Pi functions (numeric literals) are MDifferentiable. -/
@[fun_prop]
lemma MDifferentiable.pi_ofNat (n : ℕ) [n.AtLeastTwo] :
    MDiff (@OfNat.ofNat (ℍ → ℂ) n _) := mdifferentiable_const

/-- Inverse of a constant Pi function (e.g. `6⁻¹ : ℍ → ℂ`) is MDifferentiable. -/
@[fun_prop]
lemma MDifferentiable.pi_inv_ofNat (n : ℕ) [n.AtLeastTwo] :
    MDiff (@OfNat.ofNat (ℍ → ℂ) n _)⁻¹ := by
  change MDiff (fun (_ : ℍ) => (OfNat.ofNat n : ℂ)⁻¹); exact mdifferentiable_const

/-!
Definition of (Serre) derivative of modular forms.
Prove Ramanujan's formulas on derivatives of Eisenstein series.
-/
noncomputable def D (F : ℍ → ℂ) : ℍ → ℂ :=
  fun (z : ℍ) => (2 * π * I)⁻¹ * ((deriv (F ∘ ofComplex)) z)

/-- `MDifferentiableAt` for `F : ℍ → ℂ` gives `DifferentiableAt` for
`F ∘ ofComplex : ℂ → ℂ` at the same point. -/
lemma MDifferentiableAt_DifferentiableAt {F : ℍ → ℂ} {z : ℍ}
    (h : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) F z) :
    DifferentiableAt ℂ (F ∘ ofComplex) ↑z :=
  differentiableWithinAt_univ.1 <| by
    simpa [writtenInExtChartAt, extChartAt, Set.range_id] using
      MDifferentiableWithinAt.differentiableWithinAt_writtenInExtChartAt h

/--
The converse direction: `DifferentiableAt` on ℂ implies `MDifferentiableAt` on ℍ.
-/
lemma DifferentiableAt_MDifferentiableAt {G : ℂ → ℂ} {z : ℍ}
    (h : DifferentiableAt ℂ G ↑z) : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ (↑) : ℍ → ℂ) z := by
  rw [mdifferentiableAt_iff]
  -- Goal: DifferentiableAt ℂ ((G ∘ (↑)) ∘ ofComplex) ↑z
  -- The functions ((G ∘ (↑)) ∘ ofComplex) and G agree on the upper half-plane
  -- which is a neighborhood of ↑z
  apply DifferentiableAt.congr_of_eventuallyEq h
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp [Function.comp_apply, ofComplex_apply_of_im_pos hw]

/--
The derivative operator `D` preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `D F` is also MDifferentiable.
-/
@[fun_prop]
theorem D_differentiable {F : ℍ → ℂ} (hF : MDiff F) : MDiff (D F) := fun z =>
  have hDiffOn : DifferentiableOn ℂ (F ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    fun w hw => (MDifferentiableAt_DifferentiableAt (hF ⟨w, hw⟩)).differentiableWithinAt
  mdifferentiableAt_const.mul <| DifferentiableAt_MDifferentiableAt <|
    (hDiffOn.deriv isOpen_upperHalfPlaneSet).differentiableAt
      (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

/-- The Eisenstein series `E₂` is `MDifferentiable` on `ℍ`. -/
@[fun_prop]
theorem E₂_holo' : MDiff E₂ := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hη : DifferentiableOn ℂ η {z : ℂ | 0 < z.im} := fun z hz => by
    simpa [ModularForm.eta] using
      (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (z := z) hz).differentiableWithinAt
  have hlog : DifferentiableOn ℂ (logDeriv η) {z | 0 < z.im} :=
    (hη.deriv isOpen_upperHalfPlaneSet).div hη fun z hz => by
      simpa [ModularForm.eta] using (ModularForm.eta_ne_zero (z := z) hz)
  exact (hlog.const_mul ((↑π * I / 12)⁻¹)).congr fun z hz => by
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hz,
      show logDeriv η z = (↑π * I / 12) * E₂ ⟨z, hz⟩ by
        simpa [ModularForm.eta, E₂] using (ModularForm.logDeriv_eta_eq_E2 ⟨z, hz⟩)]
    field_simp [Real.pi_ne_zero]

/--
Basic properties of derivatives: linearity, Leibniz rule, etc.
-/
@[simp]
theorem D_add (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F + G) = D F + D G := by
  ext z
  show (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) + (G ∘ ofComplex)) z = D F z + D G z
  rw [deriv_add (MDifferentiableAt_DifferentiableAt (hF z))
    (MDifferentiableAt_DifferentiableAt (hG z))]
  simp [D, mul_add]

@[simp]
theorem D_sub (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F - G) = D F - D G := by
  ext z
  show (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) - (G ∘ ofComplex)) z = D F z - D G z
  rw [deriv_sub (MDifferentiableAt_DifferentiableAt (hF z))
    (MDifferentiableAt_DifferentiableAt (hG z))]
  simp [D, mul_sub]

@[simp]
theorem D_smul (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) :
    D (c • F) = c • D F := by
  ext z
  show (2 * π * I)⁻¹ * deriv (c • (F ∘ ofComplex)) z = c * D F z
  rw [show (c • (F ∘ ofComplex)) = (fun w => c * (F ∘ ofComplex) w) from rfl,
    deriv_const_mul c (MDifferentiableAt_DifferentiableAt (hF z))]
  simp [D]; ring

@[simp]
theorem D_neg (F : ℍ → ℂ) (hF : MDiff F) :
    D (-F) = -D F := by
  rw [show (-F) = (-1 : ℂ) • F from by ext; simp, D_smul _ _ hF]; ext; simp

@[simp]
theorem D_mul (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    D (F * G) = D F * G + F * D G := by
  ext z
  show (2 * π * I)⁻¹ * deriv ((F ∘ ofComplex) * (G ∘ ofComplex)) z = _
  rw [deriv_mul (MDifferentiableAt_DifferentiableAt (hF z))
    (MDifferentiableAt_DifferentiableAt (hG z))]
  simp [D, Function.comp_apply, ofComplex_apply, mul_add]; ring

@[simp]
theorem D_sq (F : ℍ → ℂ) (hF : MDiff F) :
    D (F ^ 2) = 2 * F * D F := by
  rw [pow_two, D_mul F F hF hF]; ring

@[simp]
theorem D_cube (F : ℍ → ℂ) (hF : MDiff F) :
    D (F ^ 3) = 3 * F ^ 2 * D F := by
  have hF2 : MDiff (F ^ 2) := by rw [pow_two]; exact hF.mul hF
  rw [show (F ^ 3) = F * F ^ 2 from by ring, D_mul F (F ^ 2) hF hF2, D_sq F hF]; ring

/-- Division of MDifferentiable functions on ℍ is MDifferentiable, when the denominator
is everywhere nonzero. -/
lemma MDifferentiable_div {F G : ℍ → ℂ} (hF : MDiff F) (hG : MDiff G)
    (hG_ne : ∀ z : ℍ, G z ≠ 0) : MDiff (fun z => F z / G z) := fun τ => by
  suffices h : DifferentiableAt ℂ ((fun z => F z / G z) ∘ ofComplex) ↑τ by
    have h_eq : ((fun z => F z / G z) ∘ ofComplex) ∘ UpperHalfPlane.coe = fun z => F z / G z := by
      ext x; simp [Function.comp, ofComplex_apply]
    rw [← h_eq]; exact DifferentiableAt_MDifferentiableAt h
  have h_eq : (fun z => F z / G z) ∘ ofComplex =ᶠ[nhds ↑τ]
      (F ∘ ofComplex) / (G ∘ ofComplex) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with w hw
    simp [Function.comp, Pi.div_apply, ofComplex_apply_of_im_pos hw]
  exact ((MDifferentiableAt_DifferentiableAt (hF τ)).div
    (MDifferentiableAt_DifferentiableAt (hG τ))
    (by simp [Function.comp]; exact hG_ne _)).congr_of_eventuallyEq h_eq.symm

@[simp]
theorem D_const (c : ℂ) : D (Function.const ℍ c) = 0 := by
  ext z
  show (2 * π * I)⁻¹ * deriv (Function.const _ c ∘ ofComplex) z = 0
  rw [show (Function.const _ c ∘ ofComplex) = fun _ : ℂ => c from rfl, deriv_const]; ring

/-- Normalize a numeric literal `(n : ℍ → ℂ)` to `Function.const ℍ n` so `D_const` fires. -/
@[simp]
lemma pi_ofNat_eq_const (n : ℕ) [n.AtLeastTwo] :
    (@OfNat.ofNat (ℍ → ℂ) n _) = Function.const ℍ (OfNat.ofNat n) := rfl

/-- Normalize `(Function.const ℍ c)⁻¹` to `Function.const ℍ c⁻¹` so `D_const` fires. -/
@[simp]
lemma pi_inv_const_eq_const (c : ℂ) :
    (Function.const ℍ c)⁻¹ = Function.const ℍ c⁻¹ := rfl

/-! ### Termwise differentiation of q-series (Lemma 6.45) -/

/-- Helper: HasDerivAt for a·exp(2πicw) with chain rule. -/
private lemma hasDerivAt_qexp (a c w : ℂ) :
    HasDerivAt (fun z => a * cexp (2 * π * I * c * z))
      (a * (2 * π * I * c) * cexp (2 * π * I * c * w)) w := by
  have h := (hasDerivAt_id w).const_mul (2 * π * I * c)
  simp only [mul_one, id] at h
  have := ((Complex.hasDerivAt_exp _).scomp w h).const_mul a
  simp only [smul_eq_mul] at this ⊢
  convert this using 1; ring

/-- Helper: derivWithin for qexp term on upper half-plane. -/
private lemma derivWithin_qexp (a c : ℂ) (w : ℂ) (hw : 0 < w.im) :
    derivWithin (fun z => a * cexp (2 * π * I * c * z))
      {z : ℂ | 0 < z.im} w = a * (2 * π * I * c) * cexp (2 * π * I * c * w) :=
  ((hasDerivAt_qexp a c w).hasDerivWithinAt).derivWithin
    (isOpen_upperHalfPlaneSet.uniqueDiffWithinAt hw)

/--
**Lemma 6.45 (Blueprint)**: $D$ commutes with tsum for $q$-series.
If F(z) = Σ a(n)·qⁿ where q = exp(2πiz), then D F(z) = Σ n·a(n)·qⁿ.

More precisely, this lemma shows that for a ℕ-indexed q-series with summable coefficients
satisfying appropriate derivative bounds, D acts termwise by multiplying coefficients by n.
-/
theorem D_qexp_tsum (a : ℕ → ℂ) (z : ℍ)
    (_hsum : Summable (fun n => a n * cexp (2 * π * I * n * z)))
    (hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K), ‖a n * (2 * π * I * n) *
          cexp (2 * π * I * n * k.1)‖ ≤ u n) :
    D (fun w => ∑' n, a n * cexp (2 * π * I * n * w)) z =
      ∑' n : ℕ, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
  simp only [D]
  -- Each term is differentiable
  have hf_diff : ∀ n (r : {w : ℂ | 0 < w.im}), DifferentiableAt ℂ
      (fun w => a n * cexp (2 * π * I * n * w)) r := fun n r =>
    ((differentiableAt_id.const_mul (2 * π * I * n)).cexp).const_mul (a n)
  -- Summability at each point (bound holds for n ≥ 1, exception set ⊆ {0})
  have hf_sum : ∀ y : ℂ, y ∈ {w : ℂ | 0 < w.im} →
      Summable (fun n => a n * cexp (2 * π * I * n * y)) := by
    intro y hy
    obtain ⟨u, hu_sum, hu_bound⟩ :=
      hsum_deriv {y} (Set.singleton_subset_iff.mpr hy) isCompact_singleton
    apply Summable.of_norm_bounded_eventually (g := fun n => u n / (2 * π)) (hu_sum.div_const _)
    rw [Filter.eventually_cofinite]
    refine Set.Finite.subset (Set.finite_singleton 0) fun n hn => ?_
    simp only [Set.mem_setOf_eq, not_le] at hn
    by_contra h_ne
    have h_deriv_bound := hu_bound n ⟨y, Set.mem_singleton y⟩
    have h_n_ge_1 : (1 : ℝ) ≤ n := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr h_ne)
    have h_norm_2pin : ‖(2 : ℂ) * π * I * n‖ = 2 * π * n := by
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
          Complex.norm_I, mul_one, Complex.norm_natCast, Real.norm_of_nonneg pi_pos.le]
    have h_bound : ‖a n * cexp (2 * π * I * n * y)‖ ≤ u n / (2 * π) := by
      have h_pos : (0 : ℝ) < 2 * π * n := by positivity
      have h_key : ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) =
          ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ := by
        simp only [norm_mul, h_norm_2pin]; ring
      calc ‖a n * cexp (2 * π * I * n * y)‖
          = ‖a n * cexp (2 * π * I * n * y)‖ * (2 * π * n) / (2 * π * n) := by field_simp
        _ = ‖a n * (2 * π * I * n) * cexp (2 * π * I * n * y)‖ / (2 * π * n) := by rw [h_key]
        _ ≤ u n / (2 * π * n) := div_le_div_of_nonneg_right h_deriv_bound h_pos.le
        _ ≤ u n / (2 * π) := by
            apply div_le_div_of_nonneg_left (le_trans (norm_nonneg _) h_deriv_bound)
              (by positivity); nlinarith
    exact hn.not_ge h_bound
  -- Derivative bound for uniform convergence
  have hu : ∀ K ⊆ {w : ℂ | 0 < w.im}, IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K),
        ‖derivWithin (fun w => a n * cexp (2 * π * I * n * w)) {w : ℂ | 0 < w.im} k‖ ≤ u n := by
    intro K hK1 hK2
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK1 hK2
    exact ⟨u, hu_sum, fun n k => by rw [derivWithin_qexp _ _ _ (hK1 k.2)]; exact hu_bound n k⟩
  -- Apply termwise differentiation
  have h_tsum_deriv := hasDerivAt_tsum_fun (fun n w => a n * cexp (2 * π * I * n * w))
    isOpen_upperHalfPlaneSet (z : ℂ) z.2 hf_sum hu hf_diff
  -- The composed function agrees with ℂ → ℂ in a neighborhood
  have h_agree : ((fun w : ℍ => ∑' n, a n * cexp (2 * π * I * n * w)) ∘ ofComplex) =ᶠ[nhds (z : ℂ)]
      (fun w => ∑' n, a n * cexp (2 * π * I * n * w)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.2] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw, UpperHalfPlane.coe_mk]
  rw [h_agree.deriv_eq, h_tsum_deriv.deriv]
  -- Simplify derivWithin using helper
  have h_deriv_simp : ∀ n, derivWithin (fun w => a n * cexp (2 * π * I * n * w))
      {w : ℂ | 0 < w.im} z = a n * (2 * π * I * n) * cexp (2 * π * I * n * z) :=
    fun n => derivWithin_qexp _ _ _ z.2
  simp_rw [h_deriv_simp, ← tsum_mul_left]
  congr 1; funext n; field_simp [two_pi_I_ne_zero]

/--
Simplified version of `D_qexp_tsum` for ℕ+-indexed series (starting from n=1).
This is the form most commonly used for Eisenstein series q-expansions.

**Thin layer implementation:** Extends `a : ℕ+ → ℂ` to `ℕ → ℂ` with `a' 0 = 0`,
uses `tsum_pNat` and `nat_pos_tsum2` to convert between sums,
then applies `D_qexp_tsum`.
-/
theorem D_qexp_tsum_pnat (a : ℕ+ → ℂ) (z : ℍ)
    (hsum : Summable (fun n : ℕ+ => a n * cexp (2 * π * I * n * z)))
    (hsum_deriv : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
        ∃ u : ℕ+ → ℝ, Summable u ∧ ∀ n (k : K), ‖a n * (2 * π * I * n) *
          cexp (2 * π * I * n * k.1)‖ ≤ u n) :
    D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z =
      ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
  -- Extend a to ℕ with a' 0 = 0
  let a' : ℕ → ℂ := fun n => if h : 0 < n then a ⟨n, h⟩ else 0
  have ha' : ∀ n : ℕ+, a' n = a n := fun n => dif_pos n.pos
  -- Derivative bounds: extend u using nat_pos_tsum2
  have hsum_deriv' : ∀ K : Set ℂ, K ⊆ {w : ℂ | 0 < w.im} → IsCompact K →
      ∃ u : ℕ → ℝ, Summable u ∧ ∀ n (k : K), ‖a' n * (2 * π * I * n) *
        cexp (2 * π * I * n * k.1)‖ ≤ u n := fun K hK hKc => by
    obtain ⟨u, hu_sum, hu_bound⟩ := hsum_deriv K hK hKc
    let u' : ℕ → ℝ := fun n => if h : 0 < n then u ⟨n, h⟩ else 0
    have hu' : ∀ n : ℕ+, u' n = u n := fun n => dif_pos n.pos
    refine ⟨u', (nat_pos_tsum2 u' (by simp [u'])).mp (hu_sum.congr fun n => by rw [hu']),
      fun n k => ?_⟩
    by_cases hn : 0 < n
    · simp only [a', u', dif_pos hn]; exact hu_bound _ k
    · simp only [Nat.not_lt, Nat.le_zero] at hn; simp [a', u', hn]
  -- Apply D_qexp_tsum and convert sums via tsum_pNat
  have hD := D_qexp_tsum a' z ((nat_pos_tsum2 _ (by simp [a'])).mp
    (hsum.congr fun n => by rw [ha'])) hsum_deriv'
  calc D (fun w => ∑' n : ℕ+, a n * cexp (2 * π * I * n * w)) z
      = D (fun w : ℍ => ∑' n : ℕ, a' n * cexp (2 * π * I * n * (w : ℂ))) z := by
          congr 1; ext w; rw [← tsum_pNat _ (by simp [a'])]; exact tsum_congr fun n => by rw [ha']
    _ = ∑' n : ℕ, (n : ℂ) * a' n * cexp (2 * π * I * n * (z : ℂ)) := hD
    _ = ∑' n : ℕ+, (n : ℂ) * a n * cexp (2 * π * I * n * z) := by
          rw [← tsum_pNat _ (by simp [a'])]; exact tsum_congr fun n => by rw [ha']

/--
Serre derivative of weight $k$.
Note that the definition makes sense for any analytic function $F : \mathbb{H} \to \mathbb{C}$.
-/
noncomputable def serre_D (k : ℂ) : (ℍ → ℂ) → (ℍ → ℂ) :=
  fun (F : ℍ → ℂ) => (fun z => D F z - k * 12⁻¹ * E₂ z * F z)

@[simp]
lemma serre_D_apply (k : ℂ) (F : ℍ → ℂ) (z : ℍ) :
    serre_D k F z = D F z - k * 12⁻¹ * E₂ z * F z := rfl

lemma serre_D_eq (k : ℂ) (F : ℍ → ℂ) :
    serre_D k F = fun z => D F z - k * 12⁻¹ * E₂ z * F z := rfl

/--
Basic properties of Serre derivative: linearity, Leibniz rule, etc.
-/
theorem serre_D_add (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F + G) = serre_D k F + serre_D k G := by
  ext z; simp only [serre_D, Pi.add_apply, D_add F G hF hG]; ring_nf

theorem serre_D_sub (k : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D k (F - G) = serre_D k F - serre_D k G := by
  ext z; simp only [serre_D, Pi.sub_apply, D_sub F G hF hG]; ring_nf

theorem serre_D_smul (k : ℤ) (c : ℂ) (F : ℍ → ℂ) (hF : MDiff F) :
    serre_D k (c • F) = c • (serre_D k F) := by
  ext z; show D (c • F) z - _ = c * (D F z - _)
  rw [D_smul c F hF]; simp; ring

theorem serre_D_mul (k₁ k₂ : ℤ) (F G : ℍ → ℂ) (hF : MDiff F) (hG : MDiff G) :
    serre_D (k₁ + k₂) (F * G) = (serre_D k₁ F) * G + F * (serre_D k₂ G) := by
  ext z
  show D (F * G) z - _ = (D F z - _) * G z + F z * (D G z - _)
  rw [D_mul F G hF hG]; simp only [Pi.add_apply, Pi.mul_apply]; ring

/--
The Serre derivative preserves MDifferentiability.
If `F : ℍ → ℂ` is MDifferentiable, then `serre_D k F` is also MDifferentiable.
-/
@[fun_prop]
theorem serre_D_differentiable {F : ℍ → ℂ} {k : ℂ} (hF : MDiff F) :
    MDiff (serre_D k F) := by
  have h_term : MDiff (fun z => k * 12⁻¹ * E₂ z * F z) := by
    have h1 : MDiff (fun z => (k * 12⁻¹) * (E₂ z * F z)) :=
      mdifferentiable_const.mul (E₂_holo'.mul hF)
    convert h1 using 1; ext z; simp only [mul_assoc]
  exact (D_differentiable hF).sub h_term

/-! ### Helper lemmas for D_slash

These micro-lemmas compute derivatives of the components in the slash action formula.
-/

section DSlashHelpers

open ModularGroup

variable (γ : SL(2, ℤ))

/-- Derivative of the denominator function: d/dz[cz + d] = c. -/
lemma deriv_denom (z : ℂ) :
    deriv (fun w => denom γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) := by
  simp only [denom]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Derivative of the numerator function: d/dz[az + b] = a. -/
lemma deriv_num (z : ℂ) :
    deriv (fun w => num γ w) z = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) := by
  simp only [num]
  rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'', mul_one]; simp

/-- Differentiability of denom. -/
lemma differentiableAt_denom (z : ℂ) : DifferentiableAt ℂ (fun w => denom γ w) z := by
  simp only [denom]; fun_prop

/-- Differentiability of num. -/
lemma differentiableAt_num (z : ℂ) : DifferentiableAt ℂ (fun w => num γ w) z := by
  simp only [num]; fun_prop

/-- Derivative of the Möbius transformation: d/dz[(az+b)/(cz+d)] = 1/(cz+d)².
Uses det(γ) = 1: a(cz+d) - c(az+b) = ad - bc = 1. -/
lemma deriv_moebius (z : ℍ) :
    deriv (fun w => num γ w / denom γ w) z = 1 / (denom γ z) ^ 2 := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet : ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℂ) * (γ 1 1) -
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 : ℂ) * (γ 1 0) = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    simp only [Matrix.det_fin_two, ← Int.cast_mul, ← Int.cast_sub] at this ⊢
    exact_mod_cast this
  rw [deriv_fun_div (differentiableAt_num γ z) (differentiableAt_denom γ z) hz,
      deriv_num, deriv_denom]
  simp only [denom_apply, num, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.map_apply, ofReal_intCast] at *
  have hnum_eq : ((γ 0 0 : ℤ) : ℂ) * ((γ 1 0 : ℤ) * z + (γ 1 1 : ℤ)) -
      ((γ 0 0 : ℤ) * z + (γ 0 1 : ℤ)) * (γ 1 0 : ℤ) = 1 := by linear_combination hdet
  simp only [hnum_eq, one_div]

/-- Derivative of denom^(-k): d/dz[(cz+d)^(-k)] = -k * c * (cz+d)^(-k-1). -/
lemma deriv_denom_zpow (k : ℤ) (z : ℍ) :
    deriv (fun w => (denom γ w) ^ (-k)) z =
        (-k : ℂ) * ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) * (denom γ z) ^ (-k - 1) := by
  have hz : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdiff := differentiableAt_denom γ (z : ℂ)
  have hderiv_zpow := hasDerivAt_zpow (-k) (denom γ z) (Or.inl hz)
  have hderiv_denom : HasDerivAt (fun w => denom γ w)
      ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℂ) (z : ℂ) := by
    rw [← deriv_denom]; exact hdiff.hasDerivAt
  have hcomp := hderiv_zpow.comp (z : ℂ) hderiv_denom
  have heq : (fun w => w ^ (-k)) ∘ (fun w => denom γ w) = (fun w => (denom γ w) ^ (-k)) := rfl
  rw [← heq, hcomp.deriv]; simp only [Int.cast_neg]; ring

end DSlashHelpers

/--
The derivative anomaly: how D interacts with the slash action.
This is the key computation for proving Serre derivative equivariance.
-/
lemma D_slash (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) (γ : SL(2, ℤ)) :
    D (F ∣[k] γ) = (D F ∣[k + 2] γ) -
        (fun z : ℍ => (k : ℂ) * (2 * π * I)⁻¹ * (γ 1 0 / denom γ z) * (F ∣[k] γ) z) := by
  ext z
  unfold D
  simp only [Pi.sub_apply]
  have hz_denom_ne : denom γ z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  have hdet_pos : (0 : ℝ) < ((γ : GL (Fin 2) ℝ).det).val := by simp
  -- `(F ∣[k] γ) ∘ ofComplex` agrees with `F(num/denom) * denom^(-k)` on ℍ.
  have hcomp : deriv (((F ∣[k] γ)) ∘ ofComplex) z =
      deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) z := by
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
    simp only [Function.comp_apply, ofComplex_apply_of_im_pos hw]
    rw [ModularForm.SL_slash_apply (f := F) (k := k) γ ⟨w, hw⟩]
    congr 1
    · let gz : ℍ := γ • ⟨w, hw⟩
      have hsmul_coe : (gz : ℂ) = num γ w / denom γ w :=
        UpperHalfPlane.coe_smul_of_det_pos hdet_pos ⟨w, hw⟩
      have hmob_im : (num γ w / denom γ w).im > 0 := by rw [← hsmul_coe]; exact gz.im_pos
      congr 1
      apply UpperHalfPlane.ext
      rw [ofComplex_apply_of_im_pos hmob_im]; exact hsmul_coe
  rw [hcomp]
  have hdenom_ne : ∀ w : ℂ, w.im > 0 → denom γ w ≠ 0 := fun w hw =>
    UpperHalfPlane.denom_ne_zero γ ⟨w, hw⟩
  have hdiff_denom_zpow : DifferentiableAt ℂ (fun w => (denom γ w) ^ (-k)) z :=
    DifferentiableAt.zpow (differentiableAt_denom γ z) (Or.inl (hdenom_ne z z.im_pos))
  have hdiff_mobius : DifferentiableAt ℂ (fun w => num γ w / denom γ w) z :=
    (differentiableAt_num γ z).div (differentiableAt_denom γ z) (hdenom_ne z z.im_pos)
  have hmobius_in_H : (num γ z / denom γ z).im > 0 := by
    rw [← UpperHalfPlane.coe_smul_of_det_pos hdet_pos z]; exact (γ • z).im_pos
  have hdiff_F_comp : DifferentiableAt ℂ (F ∘ ofComplex) (num γ z / denom γ z) :=
    MDifferentiableAt_DifferentiableAt (hF ⟨num γ z / denom γ z, hmobius_in_H⟩)
  have hcomp_eq : (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) =
      (F ∘ ofComplex) ∘ (fun w => num γ w / denom γ w) := rfl
  have hdiff_F_mobius : DifferentiableAt ℂ (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z := by
    rw [hcomp_eq]; exact DifferentiableAt.comp (z : ℂ) hdiff_F_comp hdiff_mobius
  rw [show (fun w => (F ∘ ofComplex) (num γ w / denom γ w) * (denom γ w) ^ (-k)) =
    ((fun w => (F ∘ ofComplex) (num γ w / denom γ w)) * fun w => (denom γ w) ^ (-k)) from rfl,
    deriv_mul hdiff_F_mobius hdiff_denom_zpow]
  have hchain : deriv (fun w => (F ∘ ofComplex) (num γ w / denom γ w)) z =
      deriv (F ∘ ofComplex) (num γ z / denom γ z) * deriv (fun w => num γ w / denom γ w) z := by
    rw [hcomp_eq, (hdiff_F_comp.hasDerivAt.comp (z : ℂ) hdiff_mobius.hasDerivAt).deriv]
  rw [hchain, deriv_moebius γ z, deriv_denom_zpow γ k z]
  have hmob_eq : ↑(γ • z) = num γ z / denom γ z :=
    UpperHalfPlane.coe_smul_of_det_pos hdet_pos z
  have hF_mob : (F ∘ ofComplex) (num γ z / denom γ z) = F (γ • z) := by
    simp only [Function.comp_apply, ← hmob_eq, ofComplex_apply]
  simp only [ModularForm.SL_slash_apply, hF_mob, hmob_eq]
  have hpow_combine : 1 / (denom γ z) ^ 2 * (denom γ z) ^ (-k) = (denom γ z) ^ (-(k + 2)) := by
    rw [one_div, ← zpow_natCast (denom γ z) 2, ← zpow_neg, ← zpow_add₀ hz_denom_ne]
    congr 1; ring
  have hpow_m1 : (denom γ z) ^ (-k - 1) = (denom γ z) ^ (-1 : ℤ) * (denom γ z) ^ (-k) := by
    rw [← zpow_add₀ hz_denom_ne]; congr 1; ring
  conv_lhs =>
    rw [mul_assoc (deriv (F ∘ ofComplex) (num γ z / denom γ z)) (1 / denom γ z ^ 2) _,
      hpow_combine, hpow_m1]
  simp only [zpow_neg_one]; ring

/--
Serre derivative is equivariant under the slash action. More precisely, if `F` is invariant
under the slash action of weight `k`, then `serre_D k F` is invariant under the slash action
of weight `k + 2`.
-/
theorem serre_D_slash_equivariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F) :
    ∀ γ : SL(2, ℤ), serre_D k F ∣[k + 2] γ = serre_D k (F ∣[k] γ) := fun γ => by
  have hD := D_slash k F hF γ
  have hE₂ := E₂_slash_transform γ
  have hmul := ModularForm.mul_slash_SL2 (2 : ℤ) k γ E₂ F
  ext z
  simp only [serre_D_apply]
  have hLHS : (serre_D (↑k) F ∣[k + 2] γ) z =
      (D F ∣[k + 2] γ) z - ↑k * 12⁻¹ * ((E₂ ∣[(2 : ℤ)] γ) z * (F ∣[k] γ) z) := by
    have h := congrFun hmul z
    simp only [Pi.mul_apply, show (2 : ℤ) + k = k + 2 from by omega] at h
    simp only [ModularForm.SL_slash_apply, serre_D_apply, Pi.mul_apply] at h ⊢
    rw [← h]; ring
  rw [hLHS]
  have hE₂z := congrFun hE₂ z
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hE₂z
  have hDz := congrFun hD z
  simp only [Pi.sub_apply] at hDz
  rw [hE₂z, hDz]
  simp only [show D₂ γ z = (2 * ↑π * I * ↑↑(γ 1 0)) / denom γ ↑z from rfl, riemannZeta_two]
  have hpi_ne : (↑π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdenom_ne : denom γ ↑z ≠ 0 := UpperHalfPlane.denom_ne_zero γ z
  field_simp [hdenom_ne, hpi_ne]
  ring_nf; simp only [I_sq]; ring

theorem serre_D_slash_invariant (k : ℤ) (F : ℍ → ℂ) (hF : MDiff F)
    (γ : SL(2, ℤ)) (h : F ∣[k] γ = F) :
    serre_D k F ∣[k + 2] γ = serre_D k F := by
  rw [serre_D_slash_equivariant _ _ hF, h]

/-
Interaction between (Serre) derivative and restriction to the imaginary axis.
-/
lemma StrictAntiOn.eventuallyPos_Ioi {g : ℝ → ℝ} (hAnti : StrictAntiOn g (Set.Ioi (0 : ℝ)))
    {t₀ : ℝ} (ht₀_pos : 0 < t₀) (hEv : ∀ t : ℝ, t₀ ≤ t → 0 < g t) :
    ∀ t : ℝ, 0 < t → 0 < g t := fun t ht => by
  by_cases hcase : t₀ ≤ t
  · exact hEv t hcase
  · exact (hEv t₀ le_rfl).trans (hAnti ht ht₀_pos (lt_of_not_ge hcase))

/--
Chain rule for restriction to imaginary axis: `d/dt F(it) = -2π * (D F)(it)`.

This connects the real derivative along the imaginary axis to the normalized derivative D.
The key computation is:
- The imaginary axis is parametrized by g(t) = I * t
- By chain rule: d/dt F(it) = (dF/dz)(it) · (d/dt)(it) = F'(it) · I
- Since D = (2πi)⁻¹ · d/dz, we have F' = 2πi · D F
- So d/dt F(it) = 2πi · D F(it) · I = -2π · D F(it)
-/
theorem deriv_resToImagAxis_eq (F : ℍ → ℂ) (hF : MDiff F) {t : ℝ} (ht : 0 < t) :
    deriv F.resToImagAxis t = -2 * π * (D F).resToImagAxis t := by
  let z : ℍ := ⟨I * t, by simp [ht]⟩
  let g : ℝ → ℂ := (I * ·)
  have h_eq : F.resToImagAxis =ᶠ[nhds t] ((F ∘ ofComplex) ∘ g) := by
    filter_upwards [lt_mem_nhds ht] with s hs
    have him : 0 < (g s).im := by simp [g, hs]
    simp [Function.resToImagAxis_apply, ResToImagAxis, hs, Function.comp_apply, g,
      ofComplex_apply_of_im_pos him]
  suffices h : deriv ((F ∘ ofComplex) ∘ g) t = -2 * ↑π * (D F).resToImagAxis t by
    exact h_eq.deriv_eq (x := t) ▸ h
  have hg : HasDerivAt g I t := by
    show HasDerivAt (fun x : ℝ => I * (x : ℂ)) I t
    have h := ofRealCLM.hasDerivAt (x := t) |>.const_mul I
    simp only [ofRealCLM_apply, ofReal_one, mul_one] at h; exact h
  have hF' := (MDifferentiableAt_DifferentiableAt (hF z)).hasDerivAt
  have hcomp := (hF'.comp t hg).deriv
  -- hcomp : deriv ((F ∘ ofComplex) ∘ g) t = deriv (F ∘ ofComplex) (g t) * I
  rw [show deriv ((F ∘ ↑ofComplex) ∘ g) t = deriv (F ∘ ↑ofComplex) (↑z) * I from hcomp]
  have hD : deriv (F ∘ ofComplex) z = 2 * π * I * D F z := by simp only [D]; field_simp
  simp only [hD, Function.resToImagAxis_apply, ResToImagAxis, dif_pos ht, z]
  ring_nf; simp only [I_sq]; ring

/-- The derivative of a function with zero imaginary part also has zero imaginary part. -/
lemma im_deriv_eq_zero_of_im_eq_zero {f : ℝ → ℂ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (him : ∀ s, (f s).im = 0) :
    (deriv f t).im = 0 := by
  simpa [funext him] using ((hasDerivAt_const t Complex.imCLM).clm_apply hf.hasDerivAt).deriv.symm

/-- If F is real on the imaginary axis and MDifferentiable, then D F is also real
on the imaginary axis. -/
theorem D_real_of_real {F : ℍ → ℂ} (hF_real : ResToImagAxis.Real F)
    (hF_diff : MDiff F) : ResToImagAxis.Real (D F) := fun t ht => by
  have him : ∀ s, (F.resToImagAxis s).im = 0 := fun s => by
    by_cases hs : 0 < s
    · exact hF_real s hs
    · simp [ResToImagAxis, hs]
  have h_im_deriv :=
    im_deriv_eq_zero_of_im_eq_zero (ResToImagAxis.Differentiable F hF_diff t ht) him
  have h_im_eq : (deriv F.resToImagAxis t).im = -2 * π * ((D F).resToImagAxis t).im := by
    simpa [mul_assoc, ofReal_mul] using congrArg Complex.im (deriv_resToImagAxis_eq F hF_diff ht)
  exact (mul_eq_zero.mp (h_im_deriv ▸ h_im_eq).symm).resolve_left
    (by positivity)

/-- The real part of F.resToImagAxis has derivative -2π * ((D F).resToImagAxis t).re at t. -/
lemma hasDerivAt_resToImagAxis_re {F : ℍ → ℂ} (hdiff : MDiff F) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => (F.resToImagAxis s).re) (-2 * π * ((D F).resToImagAxis t).re) t := by
  have hderivC := (ResToImagAxis.Differentiable F hdiff t ht).hasDerivAt.congr_deriv
    (deriv_resToImagAxis_eq F hdiff ht)
  simpa using (hasDerivAt_const t (Complex.reCLM : ℂ →L[ℝ] ℝ)).clm_apply hderivC

/--
Let $F : \mathbb{H} \to \mathbb{C}$ be a holomorphic function where $F(it)$ is real for all $t > 0$.
Assume that Serre derivative $\partial_k F$ is positive on the imaginary axis.
If $F(it)$ is positive for sufficiently large $t$, then $F(it)$ is positive for all $t > 0$.
-/
theorem antiSerreDerPos {F : ℍ → ℂ} {k : ℤ} (hSDF : ResToImagAxis.Pos (serre_D k F))
    (hF : ResToImagAxis.EventuallyPos F) : ResToImagAxis.Pos F := by
  sorry

/-! ## Cauchy Estimates for D-derivative

Infrastructure for bounding derivatives using Cauchy estimates on disks in the upper half plane.
-/

/-- If `f : ℍ → ℂ` is `MDifferentiable` and a closed disk in `ℂ` lies in the upper
half-plane, then `f ∘ ofComplex` is `DiffContOnCl` on the corresponding open disk. -/
lemma diffContOnCl_comp_ofComplex_of_mdifferentiable {f : ℍ → ℂ}
    (hf : MDiff f) {c : ℂ} {R : ℝ}
    (hclosed : Metric.closedBall c R ⊆ {z : ℂ | 0 < z.im}) :
    DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball c R) :=
  ⟨fun z hz => (MDifferentiableAt_DifferentiableAt
      (hf ⟨z, hclosed (Metric.ball_subset_closedBall hz)⟩)).differentiableWithinAt,
   fun z hz => (MDifferentiableAt_DifferentiableAt
      (hf ⟨z, hclosed (Metric.closure_ball_subset_closedBall hz)⟩)).continuousAt.continuousWithinAt⟩

/-- For any `w` and complex `c`, `|w.im - c.im| ≤ dist w c`. -/
private lemma abs_im_sub_le_dist (w c : ℂ) : |w.im - c.im| ≤ dist w c := calc |w.im - c.im|
  _ = |(w - c).im| := by simp [Complex.sub_im]
  _ ≤ ‖w - c‖ := abs_im_le_norm _
  _ = dist w c := (dist_eq_norm _ _).symm

/-- Closed ball centered at z with radius z.im/2 is contained in the upper half plane. -/
lemma closedBall_center_subset_upperHalfPlane (z : ℍ) :
    Metric.closedBall (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := fun w hw => by
  have habs := (abs_im_sub_le_dist w z).trans (Metric.mem_closedBall.mp hw)
  have := (abs_le.mp habs).1
  show 0 < w.im; linarith [z.im_pos, UpperHalfPlane.coe_im z]

/-- Cauchy estimate for the D-derivative: if `f ∘ ofComplex` is holomorphic on a disk
of radius `r` around `z` and bounded by `M` on the boundary sphere,
then `‖D f z‖ ≤ M / (2πr)`. -/
lemma norm_D_le_of_sphere_bound {f : ℍ → ℂ} {z : ℍ} {r M : ℝ}
    (hr : 0 < r) (hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) r))
    (hbdd : ∀ w ∈ Metric.sphere (z : ℂ) r, ‖(f ∘ ofComplex) w‖ ≤ M) :
    ‖D f z‖ ≤ M / (2 * π * r) := calc ‖D f z‖
  _ = ‖(2 * π * I)⁻¹‖ * ‖deriv (f ∘ ofComplex) z‖ := by simp [D]
  _ = (2 * π)⁻¹ * ‖deriv (f ∘ ofComplex) z‖ := by simp [abs_of_pos Real.pi_pos]
  _ ≤ (2 * π)⁻¹ * (M / r) := by
        gcongr; exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hDiff hbdd
  _ = M / (2 * π * r) := by ring

/-- The D-derivative is bounded at infinity for bounded holomorphic functions.

For y large (y ≥ 2·max(A,0) + 1), we use a ball of radius z.im/2 around z.
The ball lies in the upper half plane, f is bounded by M on it, and
`norm_D_le_of_sphere_bound` gives ‖D f z‖ ≤ M/(π·z.im) ≤ M/π. -/
lemma D_isBoundedAtImInfty_of_bounded {f : ℍ → ℂ}
    (hf : MDiff f)
    (hbdd : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (D f) := by
  rw [isBoundedAtImInfty_iff] at hbdd ⊢
  obtain ⟨M, A, hMA⟩ := hbdd
  use M / π, 2 * max A 0 + 1
  intro z hz
  have hR_pos : 0 < z.im / 2 := by linarith [z.im_pos]
  have hclosed := closedBall_center_subset_upperHalfPlane z
  have hDiff : DiffContOnCl ℂ (f ∘ ofComplex) (Metric.ball (z : ℂ) (z.im / 2)) :=
    diffContOnCl_comp_ofComplex_of_mdifferentiable hf hclosed
  have hf_bdd_sphere : ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro w hw
    have hw_im_pos : 0 < w.im := hclosed (Metric.sphere_subset_closedBall hw)
    have habs := (abs_im_sub_le_dist w z).trans_eq (Metric.mem_sphere.mp hw)
    have hw_im_ge_A : A ≤ w.im := by
      linarith [(abs_le.mp habs).1, le_max_left A 0, UpperHalfPlane.coe_im z]
    simpa [ofComplex_apply_of_im_pos hw_im_pos] using hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  have hz_im_ge_1 : 1 ≤ z.im := by linarith [le_max_right A 0]
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) (hMA z (by linarith [le_max_left A 0]))
  calc ‖D f z‖ ≤ M / (2 * π * (z.im / 2)) := norm_D_le_of_sphere_bound hR_pos hDiff hf_bdd_sphere
    _ = M / (π * z.im) := by ring
    _ ≤ M / (π * 1) := by gcongr
    _ = M / π := by ring

/-- The D-derivative of a bounded holomorphic function tends to zero at infinity.

For z with im(z) = y, a Cauchy estimate on a ball of radius y/2 gives
‖D f z‖ ≤ M / (π · y), which tends to zero as y → ∞. -/
theorem D_tendsto_zero_of_isBoundedAtImInfty {f : ℍ → ℂ}
    (hf : MDiff f)
    (hbdd : IsBoundedAtImInfty f) :
    Filter.Tendsto (D f) atImInfty (nhds 0) := by
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.mp hbdd
  -- ‖D f z‖ ≤ M / (π · z.im) by Cauchy estimate; the bound → 0 since z.im → ∞.
  suffices h : ∀ᶠ z : ℍ in atImInfty, ‖D f z‖ ≤ M / (π * z.im) by
    apply squeeze_zero_norm' h
    have := Filter.tendsto_im_atImInfty.inv_tendsto_atTop.const_mul (M / π)
    simp only [Pi.inv_apply, mul_zero] at this
    exact this.congr fun z => by field_simp
  have h_sphere_bdd : ∀ z : ℍ, 2 * max A 0 + 1 ≤ z.im →
      ∀ w ∈ Metric.sphere (z : ℂ) (z.im / 2), ‖(f ∘ ofComplex) w‖ ≤ M := by
    intro z hz_ge w hw
    have hw_im_pos : 0 < w.im :=
      closedBall_center_subset_upperHalfPlane z (Metric.sphere_subset_closedBall hw)
    have habs := (abs_im_sub_le_dist w z).trans_eq (Metric.mem_sphere.mp hw)
    have hw_im_ge_A : A ≤ w.im := by
      linarith [(abs_le.mp habs).1, le_max_left A 0, UpperHalfPlane.coe_im z]
    simpa [ofComplex_apply_of_im_pos hw_im_pos] using hMA ⟨w, hw_im_pos⟩ hw_im_ge_A
  rw [Filter.eventually_iff_exists_mem]
  refine ⟨{z : ℍ | 2 * max A 0 + 1 ≤ z.im},
    (atImInfty_mem _).mpr ⟨_, fun _ h => h⟩, fun z hz => ?_⟩
  calc ‖D f z‖
      ≤ M / (2 * π * (z.im / 2)) := norm_D_le_of_sphere_bound (by linarith [z.im_pos])
          (diffContOnCl_comp_ofComplex_of_mdifferentiable hf
            (closedBall_center_subset_upperHalfPlane z)) (h_sphere_bdd z hz)
    _ = M / (π * z.im) := by ring

/-- The Serre derivative of a bounded holomorphic function is bounded at infinity.

serre_D k f = D f - (k/12)·E₂·f. Both terms are bounded:
- D f is bounded by `D_isBoundedAtImInfty_of_bounded`
- (k/12)·E₂·f is bounded since E₂ and f are bounded -/
theorem serre_D_isBoundedAtImInfty_of_bounded {f : ℍ → ℂ} (k : ℂ) (hf : MDiff f)
    (hbdd : IsBoundedAtImInfty f) : IsBoundedAtImInfty (serre_D k f) := by
  simp only [serre_D_eq]
  have hE₂f : IsBoundedAtImInfty (fun z => k * 12⁻¹ * E₂ z * f z) := by
    convert (Filter.const_boundedAtFilter (atImInfty) (k * 12⁻¹)).mul
      (E₂_isBoundedAtImInfty.mul hbdd) using 1
    ext z; simp only [Pi.mul_apply, Function.const_apply]; ring
  exact (D_isBoundedAtImInfty_of_bounded hf hbdd).sub hE₂f

/-- A level-1 modular form is invariant under slash action by any element of SL(2,ℤ). -/
@[simp]
lemma ModularForm.slash_eq_self {k : ℤ} (f : ModularForm (Gamma 1) k) (γ : SL(2, ℤ)) :
    (f : ℍ → ℂ) ∣[k] γ = f := by
  simpa using f.slash_action_eq' _ ⟨γ, mem_Gamma_one γ, rfl⟩

/-- The Serre derivative of a weight-k level-1 modular form is a weight-(k+2) modular form. -/
noncomputable def serre_D_ModularForm (k : ℤ) (f : ModularForm (Gamma 1) k) :
    ModularForm (Gamma 1) (k + 2) where
  toSlashInvariantForm := {
    toFun := serre_D k f
    slash_action_eq' := fun _ hγ => by
      obtain ⟨γ', -, rfl⟩ := Subgroup.mem_map.mp hγ
      simpa using serre_D_slash_invariant k f f.holo' γ' (f.slash_eq_self γ')
  }
  holo' := serre_D_differentiable f.holo'
  bdd_at_cusps' := fun hc => bounded_at_cusps_of_bounded_at_infty hc fun _ hA => by
    obtain ⟨A', rfl⟩ := MonoidHom.mem_range.mp hA
    exact (serre_D_slash_invariant k f f.holo' A' (f.slash_eq_self A')).symm ▸
      serre_D_isBoundedAtImInfty_of_bounded k f.holo' (ModularFormClass.bdd_at_infty f)
