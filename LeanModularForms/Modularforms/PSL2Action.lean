/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Mathlib.NumberTheory.Modular
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.NumberTheory.NumberField.Norm
import LeanModularForms.Modularforms.PeterssonInnerProduct

/-!
# PSL₂(ℤ) action on the upper half-plane

The **projective special linear group** `PSL(2, ℤ) = SL(2, ℤ) / {±I}` acts
faithfully on the upper half-plane `ℍ`. The center `{±I}` of `SL(2, ℤ)` acts
trivially (since `(-I) • τ = τ` for all `τ ∈ ℍ`), so the action descends to
the quotient.

## Main results

* `center_SL2Z_smul_eq` — the center of `SL(2, ℤ)` acts trivially on `ℍ`.
* `instMulActionPSL` — `MulAction PSL(2, ℤ) ℍ`.
* `isFundamentalDomain_fdo_PSL` — `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)`.

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.4
* [Shi] Shimura, *Arithmetic Theory of Automorphic Functions*, §1.5
-/

noncomputable section

open scoped MatrixGroups ModularForm Pointwise
open ModularGroup UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory

/-! ### Center of SL₂(ℤ) acts trivially -/

/-- The center of `SL(2, ℤ)` consists of `{I, -I}`. Every center element
acts trivially on `ℍ` because it is a scalar matrix `ζI` with `ζ = ±1`,
and `(ζτ + 0)/(0τ + ζ) = τ`. -/
theorem center_SL2Z_smul_eq (c : SL(2, ℤ))
    (hc : c ∈ Subgroup.center SL(2, ℤ)) (τ : ℍ) : c • τ = τ := by
  rw [mem_center_iff] at hc
  obtain ⟨ζ, hζ, hζ_eq⟩ := hc
  -- ζ ∈ ℤ with ζ² = 1 (roots of unity for 2×2 matrices), so ζ = ±1
  have hζ_cases : ζ = 1 ∨ ζ = -1 := by
    have : (ζ - 1) * (ζ + 1) = 0 := by
      simp only [Fintype.card_fin] at hζ; nlinarith [hζ]
    rcases mul_eq_zero.mp this with h | h <;> omega
  rcases hζ_cases with rfl | rfl
  · -- ζ = 1: c = I
    have : c = 1 := by
      ext i j; simpa [Matrix.scalar] using (congr_fun (congr_fun hζ_eq i) j).symm
    rw [this, one_smul]
  · -- ζ = -1: c = -I, which acts trivially
    have : c = -1 := by
      ext i j; have := congr_fun (congr_fun hζ_eq i) j
      simp [Matrix.scalar, coe_neg] at this ⊢; linarith
    rw [this]; simp

/-! ### PSL₂(ℤ) action on ℍ -/

/-- Auxiliary: the PSL₂(ℤ) action as a function. -/
private def pslSmul : PSL(2, ℤ) → ℍ → ℍ :=
  Quotient.lift (fun (a : SL(2, ℤ)) (τ : ℍ) => a • τ) (by
    intro a b hab; funext τ; show a • τ = b • τ
    have h := QuotientGroup.leftRel_apply.mp hab
    rw [show b = a * (a⁻¹ * b) from by group, mul_smul, center_SL2Z_smul_eq _ h])

@[simp] private theorem pslSmul_coe (a : SL(2, ℤ)) (τ : ℍ) :
    pslSmul (↑a) τ = a • τ := rfl

/-- The action of `PSL(2, ℤ) = SL(2, ℤ)/{±I}` on `ℍ`, descending from the
`SL(2, ℤ)` action since the center acts trivially. -/
instance instMulActionPSL : MulAction PSL(2, ℤ) ℍ where
  smul g τ := pslSmul g τ
  one_smul τ := by
    change pslSmul (↑(1 : SL(2, ℤ))) τ = τ; rw [pslSmul_coe, one_smul]
  mul_smul g₁ g₂ τ := by
    induction g₁ using Quotient.inductionOn with | h a => ?_
    induction g₂ using Quotient.inductionOn with | h b => ?_
    show pslSmul ((↑a : PSL(2, ℤ)) * ↑b) τ = pslSmul ↑a (pslSmul ↑b τ)
    rw [show (↑a : PSL(2, ℤ)) * ↑b = (↑(a * b) : PSL(2, ℤ)) from
      (QuotientGroup.mk_mul _ a b).symm, pslSmul_coe, pslSmul_coe, pslSmul_coe, mul_smul]

/-- The `PSL(2, ℤ)` action is compatible with the `SL(2, ℤ)` action:
`(↑g) • τ = g • τ` for `g : SL(2, ℤ)`. -/
@[simp]
theorem PSL_smul_coe (g : SL(2, ℤ)) (τ : ℍ) :
    (↑g : PSL(2, ℤ)) • τ = g • τ := rfl

/-! ### IsFundamentalDomain for PSL₂(ℤ)

The open modular fundamental domain `𝒟ᵒ = {τ : |τ| > 1, |Re τ| < 1/2}` is a
fundamental domain for `PSL(2, ℤ)` acting on `ℍ` with respect to `μ_hyp`.

The three conditions from `eq_smul_self_of_mem_fdo_mem_fdo` and `exists_smul_mem_fd`:

1. **NullMeasurableSet**: `fdo` is open, hence Borel measurable.
2. **ae_covers**: Every `τ ∈ ℍ` has an `SL(2, ℤ)`-translate in `fd` (by
   `exists_smul_mem_fd`), hence a `PSL(2, ℤ)`-translate in `fd`. Since
   `fd \ fdo` has measure zero (`hyperbolicMeasure_fd_boundary`), a.e. every
   `τ` has a translate in `fdo`.
3. **aedisjoint**: For `g₁ ≠ g₂` in `PSL(2, ℤ)`, `g₁ • fdo ∩ g₂ • fdo = ∅`.
   This follows from `eq_smul_self_of_mem_fdo_mem_fdo`: if `τ ∈ fdo` and
   `g • τ ∈ fdo`, then `g • τ = τ`, so `g = ±I` in `SL(2, ℤ)`, hence `g = 1`
   in `PSL(2, ℤ)`. -/

instance : Countable PSL(2, ℤ) := Quotient.countable

-- MeasurableConstSMul inherited from SL₂(ℤ)
instance : MeasurableSpace UpperHalfPlane := borel UpperHalfPlane
instance : BorelSpace UpperHalfPlane := ⟨rfl⟩

instance : MeasurableConstSMul PSL(2, ℤ) ℍ where
  measurable_const_smul g := by
    induction g using Quotient.inductionOn with | h a => ?_
    show Measurable (fun τ => (↑a : PSL(2, ℤ)) • τ)
    simp only [PSL_smul_coe]
    exact (continuous_const_smul (mapGL ℝ a)).measurable

-- SMulInvariantMeasure for μ_hyp: the hyperbolic measure is SL₂(ℝ)-invariant,
-- hence SL₂(ℤ)- and PSL₂(ℤ)-invariant ([Miy] §1.4, [DS] Ex. 5.4.1(a)).
--
-- Proof outline (Miyake (1.4.3) + (1.1.7)):
--   dv(αz) = |d(αz)/dz|² · dxdy / Im(αz)²
--          = |j(α,z)|⁻⁴ · dxdy / (Im(z)/|j(α,z)|²)²
--          = |j|⁻⁴ · |j|⁴ · dxdy/y²  =  dxdy/y²  =  dv(z).
--
-- Formalized ingredients:
--   • HasDerivAt for Möbius: d(αz)/dz = (ad-bc)/(cz+d)² (tested above)
--   • det of ℂ-multiplication as ℝ-linear map = normSq (proved via Algebra.norm)
--   • Im(αz) = det(α)·Im(z)/normSq(denom) (mathlib: im_smul_eq_div_normSq)
--
-- Missing formalization: the change-of-variables step connecting the Jacobian
-- |det fderiv| to the measure transformation. This requires
-- `lintegral_image_eq_lintegral_abs_det_fderiv_mul` applied to the Möbius
-- transform on ℍ ⊂ ℂ ≅ ℝ², which needs HasFDerivAt for the Möbius map.
private lemma mapGL_det_abs_eq_one (g : SL(2, ℤ)) :
    |(Matrix.GeneralLinearGroup.det (mapGL ℝ g)).val| = 1 := by
  have h1 : ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g).1).det = (1 : ℝ) := by
    rw [show (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g).1 =
        (Int.castRingHom ℝ).mapMatrix (↑g : Matrix (Fin 2) (Fin 2) ℤ) from by
      ext i j; simp [Matrix.SpecialLinearGroup.map],
      ← RingHom.map_det, g.det_coe, map_one]
  rw [show (Matrix.GeneralLinearGroup.det (mapGL ℝ g)).val =
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g).1).det from by
    simp [mapGL, Matrix.SpecialLinearGroup.toGL, Matrix.GeneralLinearGroup.det],
    h1, abs_one]

/-- The density identity from [Miyake] (1.4.3)+(1.1.7): for `g ∈ SL₂(ℤ)` and `τ ∈ ℍ`,
`Im(τ)⁻² = Im(gτ)⁻² · normSq(denom g τ)⁻²`.

This is the key cancellation: the `normSq` from `Im(gτ)⁻²` (which picks up a factor
`normSq(denom)²`) exactly cancels the Jacobian `normSq(denom)⁻²` of the Möbius transform.
-/
theorem density_jacobian_identity (g : SL(2, ℤ)) (τ : ℍ) :
    τ.im ^ (-2 : ℤ) = (g • τ).im ^ (-2 : ℤ) *
      Complex.normSq (UpperHalfPlane.denom (mapGL ℝ g) τ) ^ (-2 : ℤ) := by
  set g' := mapGL ℝ g
  have hns : (0 : ℝ) < Complex.normSq (UpperHalfPlane.denom g' τ) :=
    Complex.normSq_pos.mpr (UpperHalfPlane.denom_ne_zero g' τ)
  suffices him : (g • τ).im = τ.im / Complex.normSq (UpperHalfPlane.denom g' τ) by
    rw [him, div_zpow]; exact (div_mul_cancel₀ _ (zpow_ne_zero _ (ne_of_gt hns))).symm
  have h := UpperHalfPlane.im_smul_eq_div_normSq g' τ
  rwa [show g' • τ = g • τ from rfl, mapGL_det_abs_eq_one, one_mul] at h

/-! ### Möbius transform derivative and change of variables -/

/-- The Möbius transform `z ↦ (az+b)/(cz+d)` as a function on `ℂ`. -/
private def moeb (g : SL(2, ℤ)) (z : ℂ) : ℂ :=
  (((g.1 0 0 : ℤ) : ℂ) * z + (g.1 0 1 : ℤ)) / ((g.1 1 0 : ℤ) * z + (g.1 1 1 : ℤ))

/-- The denominator of the Möbius transform is nonzero on `ℍ`. -/
private lemma moeb_denom_ne_zero (g : SL(2, ℤ)) (z : ℂ) (hz : 0 < z.im) :
    ((g.1 1 0 : ℤ) : ℂ) * z + (g.1 1 1 : ℤ) ≠ 0 := by
  convert UpperHalfPlane.denom_ne_zero (mapGL ℝ g) (⟨z, hz⟩ : ℍ) using 1

/-- `HasDerivAt` for the Möbius transform: `d(moeb g z)/dz = 1/(cz+d)²`. -/
private lemma moeb_hasDerivAt (g : SL(2, ℤ)) (z : ℂ) (hz : 0 < z.im) :
    HasDerivAt (moeb g) (1 / ((g.1 1 0 : ℤ) * z + (g.1 1 1 : ℤ) : ℂ) ^ 2) z := by
  set a := ((g.1 0 0 : ℤ) : ℂ); set b := ((g.1 0 1 : ℤ) : ℂ)
  set c := ((g.1 1 0 : ℤ) : ℂ); set d := ((g.1 1 1 : ℤ) : ℂ)
  have hd := moeb_denom_ne_zero g z hz
  change HasDerivAt (fun w => (a * w + b) / (c * w + d)) (1 / (c * z + d) ^ 2) z
  have hn : DifferentiableAt ℂ (fun w => a * w + b) z :=
    (differentiableAt_id.const_mul a).add (differentiableAt_const b)
  have hdn : DifferentiableAt ℂ (fun w => c * w + d) z :=
    (differentiableAt_id.const_mul c).add (differentiableAt_const d)
  suffices h : deriv (fun w => (a * w + b) / (c * w + d)) z = 1 / (c * z + d) ^ 2 by
    rw [← h]; exact (hn.div hdn hd).hasDerivAt
  rw [show (fun w => (a * w + b) / (c * w + d)) =
      ((fun w => a * w + b) / (fun w => c * w + d)) from funext fun _ => rfl,
    deriv_div hn hdn hd, deriv_add_const, deriv_const_mul_field,
    deriv_add_const, deriv_const_mul_field]
  simp only [show deriv (fun y : ℂ => y) z = 1 from by simp, mul_one]
  have hdet : a * d - b * c = 1 := by
    simp only [a, b, c, d]; push_cast
    have h := g.det_coe; rw [Matrix.det_fin_two] at h; exact_mod_cast h
  congr 1; linear_combination hdet

/-- The determinant of the ℝ-Fréchet derivative of "multiply by `w`" on `ℂ` is `normSq w`. -/
private lemma det_complexSmul (w : ℂ) : (w • (1 : ℂ →L[ℝ] ℂ)).det = Complex.normSq w := by
  rw [show w • (1 : ℂ →L[ℝ] ℂ) =
      (ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ from by
    ext z; simp [ContinuousLinearMap.toSpanSingleton, mul_comm]]
  show ((ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ).toLinearMap.det = _
  rw [show ((ContinuousLinearMap.toSpanSingleton ℂ w).restrictScalars ℝ).toLinearMap =
      (Algebra.lmul ℝ ℂ) w from by ext z; simp [ContinuousLinearMap.toSpanSingleton, mul_comm],
    ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.basisOneI]
  -- The matrix entries after det_fin_two are expressed via repr.
  -- Use simp to evaluate the basis/repr applications.
  -- Simplify: the basis at 0 is 1, at 1 is I.
  -- lmul w 1 = w, lmul w I = w*I. repr gives [re, im].
  simp only [Complex.basisOneI, Module.Basis.ofEquivFun_repr_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Complex.normSq_apply, mul_comm, mul_one]
  -- Now (Algebra.lmul ℝ ℂ) w applied to basis elements:
  -- Need to evaluate Algebra.lmul ℝ ℂ w (basisOneI 0) and (basisOneI 1)
  -- basisOneI 0 = 1, basisOneI 1 = I
  -- (Algebra.lmul ℝ ℂ) w x = w * x
  simp only [Algebra.lmul, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    LinearMap.mul_apply']
  simp [Complex.ext_iff, Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]

/-- `moeb g` agrees with the SL₂(ℤ) action on ℍ. -/
private lemma moeb_coe (g : SL(2, ℤ)) (τ : ℍ) : moeb g (↑τ) = ↑(g • τ) := by
  simp only [moeb, UpperHalfPlane.coe_specialLinearGroup_apply, algebraMap_int_eq,
    Int.coe_castRingHom]; push_cast; rfl

/-- The Möbius image of `coe((g•·)⁻¹' s)` is `coe(s)`. -/
private lemma moeb_image_eq (g : SL(2, ℤ)) (s : Set ℍ) :
    moeb g '' (UpperHalfPlane.coe '' ((g • ·) ⁻¹' s)) = UpperHalfPlane.coe '' s := by
  ext z; constructor
  · rintro ⟨w, ⟨τ, hτ, rfl⟩, rfl⟩; exact ⟨g • τ, hτ, (moeb_coe g τ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩; refine ⟨↑(g⁻¹ • σ), ⟨g⁻¹ • σ, by simpa, rfl⟩, ?_⟩
    rw [moeb_coe, smul_inv_smul]

/-- Transfer: `∫ on ℍ` against `comap coe vol` equals `∫ on ℂ` against `vol`. -/
private lemma setLIntegral_comap_coe (t : Set ℍ) (ht : MeasurableSet t) (f : ℂ → ENNReal) :
    ∫⁻ τ in t, f (UpperHalfPlane.coe τ) ∂(Measure.comap UpperHalfPlane.coe (volume : Measure ℂ)) =
    ∫⁻ z in UpperHalfPlane.coe '' t, f z ∂(volume : Measure ℂ) := by
  have me := isOpenEmbedding_coe.measurableEmbedding
  rw [(⟨me.measurable, me.map_comap volume⟩ :
      MeasurePreserving UpperHalfPlane.coe _ _).setLIntegral_comp_emb me f t,
    Measure.restrict_restrict (me.measurableSet_image.mpr ht),
    show UpperHalfPlane.coe '' t ∩ Set.range UpperHalfPlane.coe = UpperHalfPlane.coe '' t from
      Set.inter_eq_left.mpr (Set.image_subset_range _ _)]

instance instSMulInvMeasure_SL : SMulInvariantMeasure SL(2, ℤ) ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    -- Transfer to ambient ℂ using setLIntegral_comap_coe, apply change of vars,
    -- use density_jacobian_identity.
    have hs' : MeasurableSet ((g • ·) ⁻¹' s) := (measurable_const_smul g) hs
    -- Rewrite τ.im as (↑τ).im so the transfer lemma pattern matches.
    simp_rw [hyperbolicMeasure, show ∀ (τ : ℍ), τ.im = (↑τ : ℂ).im from coe_im]
    rw [withDensity_apply _ hs', withDensity_apply _ hs,
      setLIntegral_comap_coe _ hs' (fun z => ENNReal.ofReal (z.im ^ (-2 : ℤ))),
      setLIntegral_comap_coe _ hs (fun z => ENNReal.ofReal (z.im ^ (-2 : ℤ)))]
    -- Apply lintegral_image backwards: moeb g '' A = B where
    -- A = coe((g•·)⁻¹'s), B = coe(s). Then ∫_B ρ = ∫_A |det J| · ρ(moeb g ·).
    -- By density_jacobian_identity: |det J(z)| · ρ(moeb g z) = ρ(z). QED.
    set A := UpperHalfPlane.coe '' ((g • ·) ⁻¹' s)
    set B := UpperHalfPlane.coe '' s
    set ρ : ℂ → ENNReal := fun z => ENNReal.ofReal (z.im ^ (-2 : ℤ))
    set J : ℂ → ℂ →L[ℝ] ℂ :=
      fun z => (1 / (((g.1 1 0 : ℤ) : ℂ) * z + (g.1 1 1 : ℤ)) ^ 2) • (1 : ℂ →L[ℝ] ℂ)
    change ∫⁻ z in A, ρ z = ∫⁻ z in B, ρ z
    -- B = moeb g '' A (moeb_image_eq). Apply lintegral_image backwards.
    rw [show B = moeb g '' A from (moeb_image_eq g s).symm,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs')
        (fun z hz => (moeb_hasDerivAt g z (by obtain ⟨τ, _, rfl⟩ := hz; exact τ.coe_im_pos
          )).complexToReal_fderiv.hasFDerivWithinAt)
        (fun z₁ hz₁ z₂ hz₂ h => by
          obtain ⟨τ₁, _, rfl⟩ := hz₁; obtain ⟨τ₂, _, rfl⟩ := hz₂
          rw [moeb_coe, moeb_coe] at h
          exact congrArg _ (MulAction.injective g (UpperHalfPlane.ext h)))]
    -- Goal: ∫_A |det J(z)| * ρ(moeb g z) = ∫_A ρ z.
    -- Pointwise: |det J(z)| * ρ(moeb g z) = ρ(z) by density_jacobian_identity + det_complexSmul.
    refine setLIntegral_congr_fun (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs') fun z hz => ?_
    obtain ⟨τ, _, rfl⟩ := hz
    -- ρ(↑τ) = ofReal |det(J(↑τ))| * ρ(moeb g ↑τ)
    simp only [ρ, J, det_complexSmul]
    rw [abs_of_nonneg (Complex.normSq_nonneg _),
      ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
      moeb_coe, UpperHalfPlane.coe_im]
    congr 1
    -- τ.im⁻² = normSq(1/(cτ+d)²) * (g•τ).im⁻²
    -- normSq(1/(cτ+d)²) = normSq(denom g τ)⁻² (they're the same denominator).
    have hdenom : Complex.normSq (1 / ((↑(g.1 1 0 : ℤ) : ℂ) * ↑τ + ↑(g.1 1 1 : ℤ)) ^ 2) =
        Complex.normSq (UpperHalfPlane.denom (mapGL ℝ g) ↑τ) ^ (-2 : ℤ) := by
      simp only [UpperHalfPlane.denom, mapGL, MonoidHom.comp_apply,
        Matrix.SpecialLinearGroup.map_apply_coe, Complex.normSq_div,
        Complex.normSq_one, one_div, Complex.normSq_inv, zpow_neg, zpow_natCast, inv_pow]
      congr 3
      all_goals (first | rfl | simp [Matrix.SpecialLinearGroup.map, algebraMap_int_eq,
        Int.coe_castRingHom, Matrix.SpecialLinearGroup.toGL])
      all_goals exact Eq.refl _
    rw [hdenom, ← UpperHalfPlane.coe_im, mul_comm]
    exact density_jacobian_identity g τ

instance instSMulInvMeasure_PSL : SMulInvariantMeasure PSL(2, ℤ) ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    induction g using Quotient.inductionOn with | h a => ?_
    change μ_hyp ((fun τ => (↑a : PSL(2, ℤ)) • τ) ⁻¹' s) = μ_hyp s
    simp only [PSL_smul_coe]
    exact (measurePreserving_smul a μ_hyp).measure_preimage hs.nullMeasurableSet

set_option maxHeartbeats 800000 in
/-- If `g ∈ SL₂(ℤ)` acts trivially on `ℍ` and has `c`-entry zero, then `g ∈ center`.

From `c = 0` and `det = 1`: `g = [[a,b],[0,d]]` with `ad = 1`, so `a = d = ±1`.
From `∀ z, g • z = z`: `(az+b)/a = z` forces `b = 0`. So `g = ±I ∈ center`. -/
private theorem center_SL2Z_smul_eq_of_forall (g : SL(2, ℤ))
    (htriv : ∀ z : ℍ, g • z = z)
    (hc : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0) :
    g ∈ Subgroup.center SL(2, ℤ) := by
  have hdet : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 *
      (↑g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 := by
    have := g.det_coe; rwa [Matrix.det_fin_two, hc, mul_zero, sub_zero] at this
  set z₀ : ℍ := ⟨⟨0, 2⟩, by norm_num⟩
  have z₀_fdo : z₀ ∈ fdo := by
    exact ⟨by norm_num [Complex.normSq_apply],
      by show |z₀.re| < 1 / 2; simp only [UpperHalfPlane.re, z₀]; norm_num⟩
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hdet with ⟨ha, hd⟩ | ⟨ha, hd⟩
  · -- Case a = d = 1: g = T^b, T^b • z₀ = z₀ → b = 0, g = I = 1 ∈ center.
    have hg : g = T ^ ((↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1) := by
      apply Subtype.ext; apply Matrix.ext; intro i j
      simp only [coe_T_zpow]; fin_cases i <;> fin_cases j <;> simp_all
    have hb := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo z₀_fdo (hg ▸ htriv z₀ ▸ z₀_fdo)
    rw [hg, hb, zpow_zero]; exact one_mem _
  · -- Case a = d = -1: -g = T^(-b), then b = 0, g = -I = -1 ∈ center.
    have hng : -g = T ^ (-((↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1)) := by
      apply Subtype.ext; apply Matrix.ext; intro i j
      simp only [coe_T_zpow, coe_neg]; fin_cases i <;> fin_cases j <;> simp_all
    have hb : (↑g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0 := by
      have h2 : (-g) • z₀ = z₀ := by rw [SL_neg_smul]; exact htriv z₀
      rw [hng] at h2
      have := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo z₀_fdo (h2 ▸ z₀_fdo); omega
    have : g = -1 := neg_eq_iff_eq_neg.mp (by rw [hng, hb, neg_zero, zpow_zero])
    rw [this]
    exact Subgroup.mem_center_iff.mpr fun x => by
      apply Subtype.ext; apply Matrix.ext; intro i j; simp [coe_neg, neg_mul, mul_neg]

/-- **Pairwise disjointness**: distinct `PSL(2, ℤ)`-translates of `𝒟ᵒ` are
**exactly** disjoint (not just a.e.). From `eq_smul_self_of_mem_fdo_mem_fdo`:
if `τ ∈ 𝒟ᵒ` and `g • τ ∈ 𝒟ᵒ` then `g • τ = τ`, so `g = ±I` in `SL₂(ℤ)`,
hence `g = 1` in `PSL₂(ℤ)`. -/
private theorem fdo_PSL_pairwise_disjoint :
    Pairwise fun (g₁ g₂ : PSL(2, ℤ)) => Disjoint (g₁ • (fdo : Set ℍ)) (g₂ • fdo) := by
  intro g₁ g₂ hne
  rw [Set.disjoint_left]
  intro τ h1 h2
  obtain ⟨σ₁, hσ₁, rfl⟩ := h1
  obtain ⟨σ₂, hσ₂, h_eq⟩ := h2
  induction g₁ using Quotient.inductionOn with | h a => ?_
  induction g₂ using Quotient.inductionOn with | h b => ?_
  simp only [PSL_smul_coe] at h_eq
  have hba : (b⁻¹ * a) • σ₁ = σ₂ := by rw [mul_smul, ← h_eq, inv_smul_smul]
  -- σ₁ ∈ fdo and (b⁻¹a) • σ₁ = σ₂ ∈ fdo → σ₁ = (b⁻¹a) • σ₁
  have h_fix := eq_smul_self_of_mem_fdo_mem_fdo hσ₁ (hba ▸ hσ₂)
  -- b⁻¹a fixes σ₁ ∈ fdo → b⁻¹a ∈ center (from the uniqueness theorem)
  -- Then ↑a = ↑b in PSL, contradicting g₁ ≠ g₂.
  exfalso; apply hne
  -- Show b⁻¹a ∈ center, hence ⟦a⟧ = ⟦b⟧ in PSL.
  -- From h_fix: σ₁ = (b⁻¹*a) • σ₁ with σ₁ ∈ fdo, (b⁻¹*a)•σ₁ ∈ fdo.
  -- Mathlib chain: c_eq_zero → exists_eq_T_zpow → eq_zero_of_mem_fdo → acts trivially.
  -- Then: matrix analysis shows b⁻¹*a = ±I ∈ center.
  have hc := c_eq_zero hσ₁ (hba ▸ hσ₂)
  obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
  have hn0 := eq_zero_of_mem_fdo_of_T_zpow_mem_fdo hσ₁ (hn σ₁ ▸ (hba ▸ hσ₂))
  -- b⁻¹*a acts trivially on all of ℍ
  have htriv : ∀ z : ℍ, (b⁻¹ * a) • z = z := by
    intro z; rw [hn z, hn0, zpow_zero, one_smul]
  -- Therefore b⁻¹*a ∈ center (since it's a scalar matrix ±I).
  -- Proof: c=0, det=1 gives diagonal entries ±1 with a₀₀=a₁₁.
  -- Acting trivially forces the off-diagonal entry to be 0.
  have hmem : b⁻¹ * a ∈ Subgroup.center SL(2, ℤ) :=
    center_SL2Z_smul_eq_of_forall _ htriv hc
  -- ⟦a⟧ = ⟦b⟧ in PSL follows from b⁻¹*a ∈ center.
  -- ⟦b⁻¹*a⟧ = 1 in PSL, so ⟦a⟧ = ⟦b⟧.
  -- ⟦b⁻¹*a⟧ = 1 in PSL → ⟦a⟧ = ⟦b⟧.
  rw [Quotient.eq, QuotientGroup.leftRel_apply]
  rw [show a⁻¹ * b = (b⁻¹ * a)⁻¹ from by group]
  exact (Subgroup.center _).inv_mem hmem

private lemma measurableSet_fd_diff_fdo : MeasurableSet (fd \ fdo : Set ℍ) :=
  MeasurableSet.diff
    ((isClosed_le continuous_const (Complex.continuous_normSq.comp continuous_coe)).inter
      (isClosed_le (continuous_abs.comp continuous_re) continuous_const)).measurableSet
    isOpen_fdo.measurableSet

/-- The open fundamental domain `𝒟ᵒ` is a fundamental domain for `PSL(2, ℤ)`
acting on `ℍ` with respect to the hyperbolic measure `μ_hyp`. -/
theorem isFundamentalDomain_fdo_PSL :
    IsFundamentalDomain PSL(2, ℤ) (fdo : Set ℍ) μ_hyp where
  nullMeasurableSet := isOpen_fdo.measurableSet.nullMeasurableSet
  ae_covers := by
    rw [ae_iff]
    apply measure_mono_null (show {x | ¬∃ g : PSL(2, ℤ), g • x ∈ fdo} ⊆
        ⋃ g : SL(2, ℤ), (g • ·) ⁻¹' (fd \ fdo) from by
      intro τ hτ; push_neg at hτ
      obtain ⟨g, hg⟩ := exists_smul_mem_fd τ
      exact Set.mem_iUnion.mpr ⟨g, Set.mem_preimage.mpr ⟨hg, hτ ↑g⟩⟩)
    exact measure_iUnion_null fun g =>
      (measurePreserving_smul g μ_hyp).measure_preimage
        (measurableSet_fd_diff_fdo.nullMeasurableSet) ▸ hyperbolicMeasure_fd_boundary
  aedisjoint := fun _ _ hne =>
    (fdo_PSL_pairwise_disjoint hne).aedisjoint

end

/-! ### GL₂⁺(ℝ) invariance of the hyperbolic measure

The hyperbolic measure `μ_hyp = y⁻² dx dy` is invariant under the full group `GL(2,ℝ)⁺`
of real 2×2 matrices with positive determinant.

For `g ∈ GL(2,ℝ)⁺` with `det g > 0`, the Möbius transform `z ↦ (az+b)/(cz+d)` has
complex derivative `det(g)/(cz+d)²`. The real Jacobian is therefore
`|det(g)|²/|cz+d|⁴`. Meanwhile, `Im(gz) = det(g)·Im(z)/|cz+d|²`, so
`Im(gz)⁻² = |cz+d|⁴/(det(g)²·Im(z)²)`. The product
`Jacobian · density = |det|²/|cz+d|⁴ · |cz+d|⁴/(|det|²·Im(z)²) = Im(z)⁻²`,
giving exact cancellation regardless of the value of `det(g)`.

References: [Miy] Miyake (1.4.3), [Shi] Shimura §1.5.
-/

noncomputable section GLPos_invariance

open scoped MatrixGroups ModularForm
open UpperHalfPlane MeasureTheory

-- GL(2,ℝ)⁺ already acts on ℍ via the Subgroup.instMulAction derived from glAction.

-- Notation for convenience (local to this section).
local notation "GL₂⁺" => GL(2, ℝ)⁺

/-- The Möbius transform `z ↦ (az+b)/(cz+d)` as a function on `ℂ`, for `g : GL(2,ℝ)⁺`. -/
private def moebGL (g : GL₂⁺) (z : ℂ) : ℂ :=
  let M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  (↑(M 0 0) * z + ↑(M 0 1)) / (↑(M 1 0) * z + ↑(M 1 1))

/-- The denominator of the GL₂⁺ Möbius transform is nonzero on ℍ. -/
private lemma moebGL_denom_ne_zero (g : GL₂⁺) (z : ℂ) (hz : 0 < z.im) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    (↑(M 1 0) * z + ↑(M 1 1) : ℂ) ≠ 0 := by
  exact denom_ne_zero_of_im (g : GL (Fin 2) ℝ) (ne_of_gt hz)

/-- `HasDerivAt` for the GL₂⁺ Möbius transform:
`d/dz((az+b)/(cz+d)) = det(g)/(cz+d)²`.

For general `g` with `det g ≠ 0`, the derivative is `det(g)/(cz+d)²`
(not `1/(cz+d)²` as in the SL₂ case). -/
private lemma moebGL_hasDerivAt (g : GL₂⁺) (z : ℂ) (hz : 0 < z.im) :
    let M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
    HasDerivAt (moebGL g)
      ((↑(M.det : ℝ) : ℂ) / (↑(M 1 0) * z + ↑(M 1 1)) ^ 2) z := by
  set M : Matrix (Fin 2) (Fin 2) ℝ := ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  set a : ℂ := ↑(M 0 0 : ℝ); set b : ℂ := ↑(M 0 1 : ℝ)
  set c : ℂ := ↑(M 1 0 : ℝ); set d : ℂ := ↑(M 1 1 : ℝ)
  have hd := moebGL_denom_ne_zero g z hz
  change HasDerivAt (fun w => (a * w + b) / (c * w + d)) (↑(M.det : ℝ) / (c * z + d) ^ 2) z
  have hn : DifferentiableAt ℂ (fun w => a * w + b) z :=
    (differentiableAt_id.const_mul a).add (differentiableAt_const b)
  have hdn : DifferentiableAt ℂ (fun w => c * w + d) z :=
    (differentiableAt_id.const_mul c).add (differentiableAt_const d)
  suffices h : deriv (fun w => (a * w + b) / (c * w + d)) z =
      ↑(M.det : ℝ) / (c * z + d) ^ 2 by
    rw [← h]; exact (hn.div hdn hd).hasDerivAt
  rw [show (fun w => (a * w + b) / (c * w + d)) =
      ((fun w => a * w + b) / (fun w => c * w + d)) from funext fun _ => rfl,
    deriv_div hn hdn hd, deriv_add_const, deriv_const_mul_field,
    deriv_add_const, deriv_const_mul_field]
  simp only [show deriv (fun y : ℂ => y) z = 1 from by simp, mul_one]
  have hdet : a * d - b * c = ↑(M.det : ℝ) := by
    simp only [a, b, c, d, Matrix.det_fin_two]; push_cast; ring
  congr 1; linear_combination hdet

/-- `moebGL g` agrees with the `GL(2,ℝ)⁺` action on ℍ (using `coe_smul_of_det_pos`). -/
private lemma moebGL_coe (g : GL₂⁺) (τ : ℍ) : moebGL g (↑τ) = ↑((g : GL (Fin 2) ℝ) • τ) := by
  have hdet : 0 < ((g : GL (Fin 2) ℝ)).det.val := g.2
  rw [coe_smul_of_det_pos hdet]
  rfl

/-- The Möbius image of `coe((g•·)⁻¹' s)` is `coe(s)`, for `g : GL(2,ℝ)⁺`. -/
private lemma moebGL_image_eq (g : GL₂⁺) (s : Set ℍ) :
    moebGL g '' (UpperHalfPlane.coe '' (((g : GL (Fin 2) ℝ) • ·) ⁻¹' s)) =
      UpperHalfPlane.coe '' s := by
  ext z; constructor
  · rintro ⟨w, ⟨τ, hτ, rfl⟩, rfl⟩
    exact ⟨(g : GL (Fin 2) ℝ) • τ, hτ, (moebGL_coe g τ).symm⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨↑((g : GL (Fin 2) ℝ)⁻¹ • σ), ⟨(g : GL (Fin 2) ℝ)⁻¹ • σ, by simpa, rfl⟩, ?_⟩
    rw [moebGL_coe, smul_inv_smul]

/-- The density-Jacobian identity for GL₂⁺(ℝ):

`Im(τ)⁻² = normSq(det(g)/(denom g τ)²) · Im(g•τ)⁻²`

This captures the exact cancellation: the `|det|²` from the Jacobian cancels
the `|det|²` in `Im(g•τ)⁻²`, leaving `Im(τ)⁻²`. -/
theorem density_jacobian_identity_GLpos (g : GL₂⁺) (τ : ℍ) :
    τ.im ^ (-2 : ℤ) =
      Complex.normSq ((↑((↑g : GL (Fin 2) ℝ).det : ℝ) : ℂ) /
        (denom (↑g : GL (Fin 2) ℝ) ↑τ) ^ 2) *
      ((↑g : GL (Fin 2) ℝ) • τ).im ^ (-2 : ℤ) := by
  set g' := (g : GL (Fin 2) ℝ)
  set D := denom g' (↑τ : ℂ)
  have hD : D ≠ 0 := denom_ne_zero g' τ
  have hnsD : (0 : ℝ) < Complex.normSq D := Complex.normSq_pos.mpr hD
  have hdet_pos : (0 : ℝ) < g'.det.val := g.2
  have hdet_ne : g'.det.val ≠ (0 : ℝ) := ne_of_gt hdet_pos
  -- Im(g•τ) = |det g| · Im(τ) / normSq(D)
  have him := im_smul_eq_div_normSq g' τ
  -- Since det > 0, |det| = det
  rw [abs_of_pos hdet_pos] at him
  -- Compute normSq(det/(denom)²)
  have hns_frac : Complex.normSq ((↑(g'.det.val : ℝ) : ℂ) / D ^ 2) =
      g'.det.val ^ 2 / Complex.normSq D ^ 2 := by
    rw [Complex.normSq_div, map_pow, Complex.normSq_ofReal]
    ring
  rw [hns_frac, him, div_zpow, mul_comm, mul_zpow]
  have hnsD_ne : Complex.normSq D ≠ 0 := ne_of_gt hnsD
  have him_ne : τ.im ≠ 0 := ne_of_gt τ.im_pos
  field_simp
  ring

/-- `MeasurableConstSMul` for `GL(2,ℝ)⁺` acting on `ℍ`, inherited from `GL(Fin 2, ℝ)`. -/
instance : MeasurableConstSMul GL(2, ℝ)⁺ ℍ where
  measurable_const_smul g := (continuous_const_smul (g : GL (Fin 2) ℝ)).measurable

/-- The hyperbolic measure `μ_hyp` is invariant under the action of `GL(2,ℝ)⁺` on `ℍ`.

This generalizes `instSMulInvMeasure_SL` from `SL(2,ℤ)` to the full group `GL(2,ℝ)⁺`.
The proof follows the same change-of-variables strategy, but now the Möbius derivative
is `det(g)/(cz+d)²` instead of `1/(cz+d)²`. The `|det|²` factor from the Jacobian
exactly cancels the `|det|²` in `Im(g•τ)⁻²`, giving the same invariance. -/
instance instSMulInvMeasure_GLpos : SMulInvariantMeasure GL(2, ℝ)⁺ ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    -- The GL₂⁺ action on ℍ factors through the GL action.
    set g' := (g : GL (Fin 2) ℝ)
    have hs' : MeasurableSet ((g' • ·) ⁻¹' s) := (measurable_const_smul g') hs
    simp_rw [hyperbolicMeasure, show ∀ (τ : ℍ), τ.im = (↑τ : ℂ).im from coe_im]
    -- The preimage under the subgroup action equals the preimage under the GL action.
    have hpre : (fun τ => (g : GL₂⁺) • τ) ⁻¹' s = (g' • ·) ⁻¹' s := by
      ext τ; simp only [Set.mem_preimage]; rfl
    rw [hpre, withDensity_apply _ hs', withDensity_apply _ hs,
      setLIntegral_comap_coe _ hs' (fun z => ENNReal.ofReal (z.im ^ (-2 : ℤ))),
      setLIntegral_comap_coe _ hs (fun z => ENNReal.ofReal (z.im ^ (-2 : ℤ)))]
    set A := UpperHalfPlane.coe '' ((g' • ·) ⁻¹' s)
    set B := UpperHalfPlane.coe '' s
    set ρ : ℂ → ENNReal := fun z => ENNReal.ofReal (z.im ^ (-2 : ℤ))
    set M : Matrix (Fin 2) (Fin 2) ℝ := (g' : Matrix (Fin 2) (Fin 2) ℝ)
    change ∫⁻ z in A, ρ z = ∫⁻ z in B, ρ z
    rw [show B = moebGL g '' A from (moebGL_image_eq g s).symm,
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs')
        (fun z hz => (moebGL_hasDerivAt g z (by obtain ⟨τ, _, rfl⟩ := hz; exact τ.coe_im_pos
          )).complexToReal_fderiv.hasFDerivWithinAt)
        (fun z₁ hz₁ z₂ hz₂ h => by
          obtain ⟨τ₁, _, rfl⟩ := hz₁; obtain ⟨τ₂, _, rfl⟩ := hz₂
          rw [moebGL_coe, moebGL_coe] at h
          exact congrArg _ (MulAction.injective g' (UpperHalfPlane.ext h)))]
    refine setLIntegral_congr_fun
      (isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hs') fun z hz => ?_
    obtain ⟨τ, _, rfl⟩ := hz
    -- Need to show: |det fderiv| * ρ(moebGL g ↑τ) = ρ(↑τ)
    -- fderiv is w • 1 where w = det(M)/(cz+d)², so |det fderiv| = normSq(w).
    -- ρ(moebGL g ↑τ) = ρ(↑(g'•τ)) = (g'•τ).im⁻².
    -- By density_jacobian_identity_GLpos: normSq(w) * (g'•τ).im⁻² = τ.im⁻².
    simp only [ρ, det_complexSmul]
    rw [abs_of_nonneg (Complex.normSq_nonneg _),
      ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
      moebGL_coe]
    -- Now goal is: ofReal((↑τ).im⁻²) = ofReal(normSq(w) * (↑(g'•τ)).im⁻²)
    -- where w = det(M)/(c*z+d)². Apply congr then density_jacobian_identity_GLpos.
    congr 1
    -- Goal: (↑τ).im⁻² = normSq(w) * (↑(g'•τ)).im⁻²
    -- After moebGL_coe, the goal involves coe_im on both sides.
    -- density_jacobian_identity_GLpos gives the equality up to mul_comm and
    -- definitional equality of det/denom coercions.
    -- Goal: (↑τ).im⁻² = normSq(↑(↑↑g).det / (c*τ+d)²) * (↑(↑g•τ)).im⁻²
    -- Convert im terms using coe_im.
    rw [show (↑τ : ℂ).im = τ.im from coe_im τ,
      show (↑((↑g : GL (Fin 2) ℝ) • τ) : ℂ).im = ((↑g : GL (Fin 2) ℝ) • τ).im from
        coe_im ((↑g : GL (Fin 2) ℝ) • τ)]
    -- Goal: τ.im⁻² = normSq(↑(↑↑g).det / (c*τ+d)²) * (↑g•τ).im⁻²
    -- The normSq term is definitionally equal to the one in density_jacobian_identity_GLpos.
    exact density_jacobian_identity_GLpos g τ

end GLPos_invariance

/-! ### PSL(2, ℝ) action on the upper half-plane (T090 Phase A)

We mirror the `PSL(2, ℤ)` block above for the real projective ambient
`PSL(2, ℝ) = SL(2, ℝ) / {±I}`.  Each step is a direct port of the integer
treatment with the entry ring changed from ℤ to ℝ; the underlying
`SL(2, ℝ)`-action on `ℍ` is `Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction.SLAction`,
which factors through `SpecialLinearGroup.mapGL ℝ : SL(2, ℝ) →* GL (Fin 2) ℝ`.

Outputs: `MulAction PSL(2, ℝ) ℍ`, `MeasurableConstSMul PSL(2, ℝ) ℍ`,
`SMulInvariantMeasure PSL(2, ℝ) ℍ μ_hyp`, plus the
`SL(2, ℤ) →* PSL(2, ℝ)` lift that downstream Γ₁(N)-side code consumes. -/

noncomputable section PSL_R_action

open scoped MatrixGroups ModularForm Pointwise
open UpperHalfPlane Matrix.SpecialLinearGroup MeasureTheory

/-- The center of `SL(2, ℝ)` consists of `{I, -I}`.  Every central element
acts trivially on `ℍ` because it is a scalar matrix `ζI` with `ζ² = 1`,
and the Möbius formula `(ζτ + 0)/(0τ + ζ) = τ` is invariant under the
sign of `ζ`.  We handle both cases simultaneously via the explicit
Möbius formula `coe_specialLinearGroup_apply`. -/
theorem center_SL2R_smul_eq (c : SL(2, ℝ))
    (hc : c ∈ Subgroup.center SL(2, ℝ)) (τ : ℍ) : c • τ = τ := by
  rw [mem_center_iff] at hc
  obtain ⟨ζ, hζ, hζ_eq⟩ := hc
  -- ζ : ℝ with ζ² = 1, so ζ = ±1, hence ζ ≠ 0.
  have hζ_cases : ζ = 1 ∨ ζ = -1 := by
    have h_diff : (ζ - 1) * (ζ + 1) = 0 := by
      simp only [Fintype.card_fin] at hζ; nlinarith [hζ]
    rcases mul_eq_zero.mp h_diff with h | h
    · left; linarith
    · right; linarith
  have hζ_ne : ζ ≠ 0 := by rcases hζ_cases with rfl | rfl <;> norm_num
  -- The matrix entries of `c` are `c 0 0 = ζ`, `c 1 1 = ζ`, off-diagonal = 0.
  have h00 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 0 0 = ζ := by
    have h := congr_fun (congr_fun hζ_eq 0) 0
    simpa [Matrix.scalar_apply, Matrix.diagonal] using h.symm
  have h11 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 1 1 = ζ := by
    have h := congr_fun (congr_fun hζ_eq 1) 1
    simpa [Matrix.scalar_apply, Matrix.diagonal] using h.symm
  have h01 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 0 1 = 0 := by
    have h := congr_fun (congr_fun hζ_eq 0) 1
    simpa [Matrix.scalar_apply, Matrix.diagonal] using h.symm
  have h10 : ((c : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 = 0 := by
    have h := congr_fun (congr_fun hζ_eq 1) 0
    simpa [Matrix.scalar_apply, Matrix.diagonal] using h.symm
  -- Now compute via `coe_specialLinearGroup_apply`: `(ζ·τ + 0)/(0·τ + ζ) = τ`.
  have hζ_ne_C : (ζ : ℂ) ≠ 0 := by exact_mod_cast hζ_ne
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply, h00, h11, h01, h10]
  simp only [Algebra.algebraMap_self_apply, Complex.ofReal_zero,
    zero_mul, zero_add, add_zero]
  field_simp

/-- Auxiliary: the `PSL(2, ℝ)` action as a function on `ℍ`. -/
private def pslSmul_R : PSL(2, ℝ) → ℍ → ℍ :=
  Quotient.lift (fun (a : SL(2, ℝ)) (τ : ℍ) => a • τ) (by
    intro a b hab; funext τ; show a • τ = b • τ
    have h := QuotientGroup.leftRel_apply.mp hab
    rw [show b = a * (a⁻¹ * b) from by group, mul_smul, center_SL2R_smul_eq _ h])

@[simp] private theorem pslSmul_R_coe (a : SL(2, ℝ)) (τ : ℍ) :
    pslSmul_R (↑a) τ = a • τ := rfl

/-- The action of `PSL(2, ℝ) = SL(2, ℝ)/{±I}` on `ℍ`, descending from the
`SL(2, ℝ)` action since the center acts trivially. -/
instance instMulActionPSL_R : MulAction PSL(2, ℝ) ℍ where
  smul g τ := pslSmul_R g τ
  one_smul τ := by
    change pslSmul_R (↑(1 : SL(2, ℝ))) τ = τ
    rw [pslSmul_R_coe, one_smul]
  mul_smul g₁ g₂ τ := by
    induction g₁ using Quotient.inductionOn with | h a => ?_
    induction g₂ using Quotient.inductionOn with | h b => ?_
    show pslSmul_R ((↑a : PSL(2, ℝ)) * ↑b) τ =
      pslSmul_R ↑a (pslSmul_R ↑b τ)
    rw [show (↑a : PSL(2, ℝ)) * ↑b = (↑(a * b) : PSL(2, ℝ)) from
        (QuotientGroup.mk_mul _ a b).symm,
      pslSmul_R_coe, pslSmul_R_coe, pslSmul_R_coe, mul_smul]

/-- Compatibility: the `PSL(2, ℝ)` action of a representative coincides with
the underlying `SL(2, ℝ)` action.  Mirror of `PSL_smul_coe` for `PSL(2, ℤ)`. -/
@[simp]
theorem PSL_R_smul_coe (g : SL(2, ℝ)) (τ : ℍ) :
    (↑g : PSL(2, ℝ)) • τ = g • τ := rfl

instance : MeasurableConstSMul PSL(2, ℝ) ℍ where
  measurable_const_smul g := by
    induction g using Quotient.inductionOn with | h a => ?_
    show Measurable (fun τ => (↑a : PSL(2, ℝ)) • τ)
    simp only [PSL_R_smul_coe]
    -- (a : SL(2, ℝ)) • τ = (mapGL ℝ a : GL (Fin 2) ℝ) • τ definitionally,
    -- and `MulAction (GL (Fin 2) ℝ) ℍ` has `ContinuousConstSMul`.
    exact (continuous_const_smul (mapGL ℝ a)).measurable

instance instSMulInvMeasure_PSL_R : SMulInvariantMeasure PSL(2, ℝ) ℍ μ_hyp where
  measure_preimage_smul g s hs := by
    induction g using Quotient.inductionOn with | h a => ?_
    -- Reduce to the SL(2, ℝ)-action via `mapGL ℝ a`, which factors through
    -- `GL(2, ℝ)⁺`-invariance (`instSMulInvMeasure_GLpos`).
    change μ_hyp ((fun τ => (↑a : PSL(2, ℝ)) • τ) ⁻¹' s) = μ_hyp s
    simp only [PSL_R_smul_coe]
    -- (a : SL(2, ℝ)) • τ via SLAction = compHom mapGL = mapGL a • τ in GL.
    -- `mapGL ℝ a : GL (Fin 2) ℝ` has positive determinant 1; lift to `GL(2, ℝ)⁺`.
    set g_GL : GL (Fin 2) ℝ := mapGL ℝ a with hg_GL_def
    have h_det : (Matrix.GeneralLinearGroup.det g_GL).val = (1 : ℝ) := by
      show (Matrix.GeneralLinearGroup.det (mapGL ℝ a)).val = (1 : ℝ)
      -- `mapGL ℝ a` is the GL-image of an SL element (after the trivial
      -- `algebraMap ℝ ℝ = RingHom.id`), so its determinant is `1` as a unit.
      have h_unit : Matrix.GeneralLinearGroup.det (mapGL ℝ a) = 1 := by
        rw [show (mapGL ℝ a : GL (Fin 2) ℝ) =
            ((Matrix.SpecialLinearGroup.map (algebraMap ℝ ℝ) a) : GL (Fin 2) ℝ) from rfl]
        exact Matrix.SpecialLinearGroup.coeToGL_det _
      rw [h_unit]; rfl
    have hg_pos : 0 < (Matrix.GeneralLinearGroup.det g_GL).val := by
      rw [h_det]; exact one_pos
    set g_GLPos : GL(2, ℝ)⁺ := ⟨g_GL, hg_pos⟩
    have h_action : ∀ τ : ℍ, (↑a : SL(2, ℝ)) • τ = (g_GLPos : GL(2, ℝ)⁺) • τ := fun τ => rfl
    simp_rw [h_action]
    exact (measurePreserving_smul g_GLPos μ_hyp).measure_preimage hs.nullMeasurableSet

/-- The lift `SL(2, ℤ) →* PSL(2, ℝ)`: cast SL(2, ℤ) entries to ℝ via
`SpecialLinearGroup.map (Int.castRingHom ℝ)`, then project to the
`±I`-quotient.  This is the canonical map appearing whenever the existing
PSL(2, ℤ) infrastructure (e.g. `imageGamma1_PSL N`) needs to be reconciled
with the projective real ambient. -/
def SL2Z_to_PSL2R : SL(2, ℤ) →* PSL(2, ℝ) :=
  (QuotientGroup.mk' (Subgroup.center SL(2, ℝ))).comp
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

@[simp] theorem SL2Z_to_PSL2R_apply (g : SL(2, ℤ)) :
    SL2Z_to_PSL2R g =
      (↑(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) : PSL(2, ℝ)) := rfl

/-- Representative-action compatibility: the `PSL(2, ℝ)`-image of an
integer SL element acts on `ℍ` exactly as the underlying `SL(2, ℤ)`-element
does (under the SL(2, ℤ) → SL(2, ℝ) embedding via `Int.castRingHom`).

Together with the existing `PSL_smul_coe`, this is the bridge that lets
the existing `imageGamma1_PSL N` story (PSL(2, ℤ) ambient) match the
PSL(2, ℝ) ambient required by the FD-shift adapter. -/
@[simp]
theorem SL2Z_to_PSL2R_smul (g : SL(2, ℤ)) (τ : ℍ) :
    SL2Z_to_PSL2R g • τ =
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) • τ :=
  rfl

/-- **Kernel of `SL2Z_to_PSL2R` is the center of `SL(2, ℤ)`**.

For `g : SL(2, ℤ)`, the cast `g.map (Int.castRingHom ℝ) : SL(2, ℝ)` is
a scalar matrix (member of `center SL(2, ℝ)`) iff `g` is itself a scalar
matrix in `SL(2, ℤ)`, by `Matrix.SpecialLinearGroup.map_intCast_injective`
on the entries. -/
theorem ker_SL2Z_to_PSL2R : SL2Z_to_PSL2R.ker = Subgroup.center SL(2, ℤ) := by
  -- Per-entry transfer: `((map ℝ g) : Matrix _) i j = ((g : Matrix _) i j : ℝ)`.
  have h_map_entry : ∀ (g : SL(2, ℤ)) (i j : Fin 2),
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g : SL(2, ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) i j =
      (((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℝ) := fun _ _ _ => rfl
  ext g
  simp only [MonoidHom.mem_ker, SL2Z_to_PSL2R_apply, QuotientGroup.eq_one_iff,
    Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · -- (g.map ℝ ∈ center SL(2, ℝ)) → g ∈ center SL(2, ℤ).
    rintro ⟨r, hr_pow, hr_scalar⟩
    -- Per-entry: `((g : Matrix _) i j : ℝ) = (scalar r) i j`.
    have h_entry_R : ∀ i j, ((g : Matrix (Fin 2) (Fin 2) ℤ) i j : ℝ) =
        (Matrix.scalar (Fin 2) r) i j := fun i j => by
      have h_ij := congr_fun (congr_fun hr_scalar i) j
      rw [h_map_entry] at h_ij
      exact h_ij.symm
    -- Set z := g.val 0 0.  Diagonal entries of g all equal z; off-diagonals are 0.
    set z : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with hz_def
    have hr_z : (z : ℝ) = r := by
      have := h_entry_R 0 0
      rwa [show (Matrix.scalar (Fin 2) r) 0 0 = r from by
        simp [Matrix.scalar_apply, Matrix.diagonal_apply]] at this
    have h_diag : ∀ i, (g : Matrix (Fin 2) (Fin 2) ℤ) i i = z := fun i => by
      have h_iR : (((g : Matrix _ _ ℤ) i i : ℤ) : ℝ) = (z : ℝ) := by
        have := h_entry_R i i
        rw [show (Matrix.scalar (Fin 2) r) i i = r from by
          simp [Matrix.scalar_apply, Matrix.diagonal_apply]] at this
        rw [this, ← hr_z]
      exact_mod_cast h_iR
    have h_off : ∀ i j, i ≠ j → (g : Matrix (Fin 2) (Fin 2) ℤ) i j = 0 := fun i j hij => by
      have h_R : (((g : Matrix _ _ ℤ) i j : ℤ) : ℝ) = 0 := by
        have := h_entry_R i j
        rw [show (Matrix.scalar (Fin 2) r) i j = 0 from by
          simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij]] at this
        exact this
      exact_mod_cast h_R
    -- z² = 1 (from r² = 1 and r = (z : ℝ)).
    have hz_sq : z ^ 2 = 1 := by
      have hr_pow' : r ^ 2 = 1 := by simpa [Fintype.card_fin] using hr_pow
      have hz_sq_R : (z : ℝ) ^ 2 = 1 := by rw [hr_z]; exact hr_pow'
      exact_mod_cast hz_sq_R
    refine ⟨z, ?_, ?_⟩
    · simpa [Fintype.card_fin] using hz_sq
    · -- scalar z = g.val (matrix-wise).
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq, h_diag]
      · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij, h_off i j hij]
  · -- (g ∈ center SL(2, ℤ)) → (g.map ℝ ∈ center SL(2, ℝ)).
    rintro ⟨z, hz_pow, hz_scalar⟩
    refine ⟨(z : ℝ), ?_, ?_⟩
    · have h : ((z ^ Fintype.card (Fin 2) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by rw [hz_pow]
      push_cast at h
      exact h
    · ext i j
      have h_ij := congr_fun (congr_fun hz_scalar i) j
      rw [h_map_entry]
      by_cases hij : i = j
      · subst hij
        rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at h_ij ⊢
        exact_mod_cast h_ij
      · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij] at h_ij ⊢
        exact_mod_cast h_ij

/-- **Phase C — descended hom `PSL(2, ℤ) →* PSL(2, ℝ)`**.

The hom `SL2Z_to_PSL2R` factors through `PSL(2, ℤ) = SL(2, ℤ) ⧸
center SL(2, ℤ)` because integer scalar matrices map to real scalar
matrices (in `center SL(2, ℝ)`).  This is the descent. -/
def PSL2Z_to_PSL2R : PSL(2, ℤ) →* PSL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) SL2Z_to_PSL2R fun x hx => by
    show SL2Z_to_PSL2R x = 1
    rw [← MonoidHom.mem_ker, ker_SL2Z_to_PSL2R]
    exact hx

@[simp] theorem PSL2Z_to_PSL2R_mk (g : SL(2, ℤ)) :
    PSL2Z_to_PSL2R (↑g : PSL(2, ℤ)) = SL2Z_to_PSL2R g :=
  QuotientGroup.lift_mk' _ _ g

/-- **Action compatibility for `PSL2Z_to_PSL2R` (representative form)**:
the descended hom sends `[g] : PSL(2, ℤ)` to a `PSL(2, ℝ)`-element acting
on `ℍ` exactly as the underlying `SL(2, ℤ)`-action does.

Mirror of `PSL_R_smul_coe`/`SL2Z_to_PSL2R_smul` at the descended-hom
level.  Used by the projective Γ₁(N)-FD bridge in `PeterssonLevelN.lean`
to identify `imageGamma1_PSL N`-action with `imageGamma1_PSL_R N`-action. -/
@[simp]
theorem PSL2Z_to_PSL2R_smul (g : SL(2, ℤ)) (τ : ℍ) :
    PSL2Z_to_PSL2R (↑g : PSL(2, ℤ)) • τ = g • τ := by
  rw [PSL2Z_to_PSL2R_mk, SL2Z_to_PSL2R_smul]
  -- (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ) g) • τ = g • τ at SL level.
  rfl

/-- **Action compatibility for `PSL2Z_to_PSL2R` (generic form)**: for any
`p : PSL(2, ℤ)`, the descended hom's image acts on `ℍ` exactly as `p`
does (with `p`'s action on the LHS via the `PSL(2, ℝ)`-action of
`PSL2Z_to_PSL2R p`, and on the RHS via the `PSL(2, ℤ)`-action of `p`). -/
@[simp]
theorem PSL2Z_to_PSL2R_smul_eq (p : PSL(2, ℤ)) (τ : ℍ) :
    PSL2Z_to_PSL2R p • τ = p • τ := by
  induction p using Quotient.inductionOn with | h g => ?_
  exact (PSL2Z_to_PSL2R_smul g τ).trans (PSL_smul_coe g τ).symm

/-- **`PSL2Z_to_PSL2R` is injective.**

Direct from `ker_SL2Z_to_PSL2R` and `QuotientGroup.ker_lift`: the
descended hom's kernel is the image of `SL2Z_to_PSL2R.ker = center
SL(2, ℤ)` under the `PSL(2, ℤ)`-projection, which is `⊥`. -/
theorem PSL2Z_to_PSL2R_injective : Function.Injective PSL2Z_to_PSL2R := by
  rw [← MonoidHom.ker_eq_bot_iff]
  show (QuotientGroup.lift (Subgroup.center SL(2, ℤ)) SL2Z_to_PSL2R _).ker = ⊥
  rw [QuotientGroup.ker_lift, ker_SL2Z_to_PSL2R, QuotientGroup.map_mk'_self]

/-! ### Phase B: term-level GL(2, ℝ)⁺ → PSL(2, ℝ) projection

We define a function (NOT a group hom) sending `g : GL(2, ℝ)⁺` to its
projective representative in `PSL(2, ℝ)`, obtained by determinant-
normalizing `g` to land in `SL(2, ℝ)` and then quotienting by `{±I}`.
The defining property is action-equivariance:
`GLPos_to_PSL_R_term g • τ = g • τ` for all `τ : ℍ`.

The argument splits into two reusable steps:
* `GL_smul_pos_eq` (positive-scalar action invariance): the Möbius
  action of `GL (Fin 2) ℝ` on `ℍ` is unchanged when every matrix entry
  is multiplied by a fixed positive scalar.  Direct numerator/denominator
  cancellation from `coe_smul_of_det_pos`.
* `GLPos_to_SLR` (det-normalization): for `g : GL(2, ℝ)⁺`, the matrix
  `(Real.sqrt g.det.val)⁻¹ • g.val.val : Matrix (Fin 2) (Fin 2) ℝ` has
  determinant `1` (`Real.sq_sqrt` + det-of-scalar-multiple), so it is
  the underlying matrix of an `SL(2, ℝ)` element. -/

/-- **Phase B step 1 — positive-scalar action invariance for `GL (Fin 2) ℝ`.**

If `h : GL (Fin 2) ℝ` has matrix obtained by scaling `g`'s matrix by a
positive scalar `c`, and `g` has positive determinant, then `h` and `g`
act identically on `ℍ`. -/
lemma GL_smul_pos_eq
    {g h : GL (Fin 2) ℝ} {c : ℝ} (hc : 0 < c)
    (hg_det : 0 < g.det.val)
    (h_eq : ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      c • ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ))
    (τ : ℍ) :
    h • τ = g • τ := by
  have hc_C : (c : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  -- Show h has positive determinant via det of scalar multiple.
  have hh_det : 0 < h.det.val := by
    have h_det_eq : h.det.val = c ^ 2 * g.det.val := by
      show ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
        c ^ 2 * ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
      rw [h_eq, Matrix.det_smul]
      simp [Fintype.card_fin]
    rw [h_det_eq]; positivity
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos hh_det, coe_smul_of_det_pos hg_det]
  -- Per-entry: (h : Matrix) i j = c * (g : Matrix) i j.
  have h_entry : ∀ i j,
      ((h : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j =
        c * ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j
    rw [h_eq]
    simp [Matrix.smul_apply, smul_eq_mul]
  -- Numerator and denominator both pick up factor c, which cancels.
  have h_num : num h τ = (c : ℂ) * num g τ := by
    show ((h 0 0 : ℝ) : ℂ) * τ + ((h 0 1 : ℝ) : ℂ) =
      (c : ℂ) * (((g 0 0 : ℝ) : ℂ) * τ + ((g 0 1 : ℝ) : ℂ))
    have h00 := h_entry 0 0
    have h01 := h_entry 0 1
    push_cast [h00, h01]
    ring
  have h_denom : denom h τ = (c : ℂ) * denom g τ := by
    show ((h 1 0 : ℝ) : ℂ) * τ + ((h 1 1 : ℝ) : ℂ) =
      (c : ℂ) * (((g 1 0 : ℝ) : ℂ) * τ + ((g 1 1 : ℝ) : ℂ))
    have h10 := h_entry 1 0
    have h11 := h_entry 1 1
    push_cast [h10, h11]
    ring
  rw [h_num, h_denom, mul_div_mul_left _ _ hc_C]

/-- **Phase B step 2 — det-normalized `SL(2, ℝ)` representative of a
`GL(2, ℝ)⁺` element.**

For `g : GL(2, ℝ)⁺`, the matrix `(Real.sqrt g.det.val)⁻¹ • g.val.val`
has determinant `1` (over ℝ), hence packages as an element of
`SL(2, ℝ)`.  Used to define the projective representative. -/
noncomputable def GLPos_to_SLR (g : GL(2, ℝ)⁺) : SL(2, ℝ) :=
  ⟨(Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ),
    by
      -- Show det = 1.
      have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
      have h_sq : Real.sqrt ((g : GL (Fin 2) ℝ).det.val) ^ 2 =
          (g : GL (Fin 2) ℝ).det.val :=
        Real.sq_sqrt (le_of_lt hg_pos)
      have h_det_g : ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det =
          (g : GL (Fin 2) ℝ).det.val := rfl
      show ((Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
          ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)).det = 1
      rw [Matrix.det_smul, h_det_g]
      simp only [Fintype.card_fin]
      rw [inv_pow, h_sq]
      exact inv_mul_cancel₀ (ne_of_gt hg_pos)⟩

/-- **Phase B step 3 — projective representative of a `GL(2, ℝ)⁺` element**.

The `PSL(2, ℝ)`-image of `GLPos_to_SLR g`.  This is a function (not a
group hom; the determinant normalization does not commute with matrix
multiplication on the nose). -/
noncomputable def GLPos_to_PSL_R_term (g : GL(2, ℝ)⁺) : PSL(2, ℝ) :=
  (GLPos_to_SLR g : PSL(2, ℝ))

/-- **Phase B step 4 — action equivariance**: the projective
representative `GLPos_to_PSL_R_term g` acts on `ℍ` exactly as `g` does.

This is the central fact that makes the projective ambient usable for
α-shifts: each `α : GL(2, ℝ)⁺` (e.g. a Hecke matrix `glMap (T_p_lower
p)`) descends to a well-defined `α_PSL : PSL(2, ℝ)` whose action on
`ℍ` agrees with the GL(2, ℝ)⁺ action of `α`, even though the
determinant of `α` is not necessarily `1`. -/
theorem GLPos_to_PSL_R_term_smul (g : GL(2, ℝ)⁺) (τ : ℍ) :
    GLPos_to_PSL_R_term g • τ = g • τ := by
  have hg_pos : 0 < ((g : GL (Fin 2) ℝ).det.val : ℝ) := g.property
  have h_sqrt_pos : 0 < (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ := by
    rw [inv_pos]; exact Real.sqrt_pos.mpr hg_pos
  -- Step A: unfold PSL action to underlying SL action.
  show ((GLPos_to_SLR g : SL(2, ℝ)) : PSL(2, ℝ)) • τ = g • τ
  rw [PSL_R_smul_coe]
  -- Step B: SL action factors through `GL (Fin 2) ℝ` via `mapGL ℝ`.
  -- The `(g : GL(2, ℝ)⁺) • τ` is the underlying `(g : GL (Fin 2) ℝ) • τ`.
  show (mapGL ℝ (GLPos_to_SLR g) : GL (Fin 2) ℝ) • τ = (g : GL (Fin 2) ℝ) • τ
  -- Step C: apply `GL_smul_pos_eq` with c := (sqrt det g)⁻¹.
  refine GL_smul_pos_eq h_sqrt_pos hg_pos ?_ τ
  -- Show matrix-level equality: mapGL ℝ (GLPos_to_SLR g) = c • g (matrix form).
  -- (mapGL ℝ s : Matrix _) = s.val.map (algebraMap ℝ ℝ) = s.val (id-map).
  -- (GLPos_to_SLR g).val = c • g.val.val.
  show ((mapGL ℝ (GLPos_to_SLR g) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    (Real.sqrt ((g : GL (Fin 2) ℝ).det.val))⁻¹ •
      ((g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix]
  -- Goal: (GLPos_to_SLR g : SL(2, ℝ).val).map (algebraMap ℝ ℝ) = c • g.val.val.
  -- The .map (algebraMap ℝ ℝ) is the identity on entries.
  ext i j
  simp [GLPos_to_SLR, Matrix.map_apply, Matrix.smul_apply, Algebra.algebraMap_self_apply]

/-- **Set-level action compatibility (T090 Phase D step 5).**

The set-level analogue of `GLPos_to_PSL_R_term_smul`: pointwise action-equality
on `ℍ` lifts to set-image equality.  Used by the projective FD-shift adapter
to identify the α-shifted Γ_p(α)-FD with the corresponding `GL(2, ℝ)⁺`-shift
at set level, so callers can pass between the two without per-point rewriting.
-/
@[simp]
theorem GLPos_to_PSL_R_term_smul_set (α' : GL(2, ℝ)⁺) (S : Set ℍ) :
    (GLPos_to_PSL_R_term α' • S : Set ℍ) = ((α' : GL(2, ℝ)⁺) • S : Set ℍ) := by
  ext τ
  simp only [Set.mem_smul_set, GLPos_to_PSL_R_term_smul]

end PSL_R_action

