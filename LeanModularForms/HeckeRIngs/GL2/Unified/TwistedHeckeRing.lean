 /-
 Copyright (c) 2026. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 Authors: LeanModularForms contributors
 -/
import LeanModularForms.HeckeRIngs.GL2.Unified.TwistedSlash
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke

/-!
# Twisted `Γ₀(N)` Hecke-ring action on Nebentypus spaces

This file begins the direct construction of the general-`χ` action of the
existing Hecke ring `𝕋 (Gamma0_pair N) ℤ` on the experimental `Γ₀(N), χ` spaces.

The first step is the semigroup character on `Δ₀(N)` coming from the upper-left
entry modulo `N`, as in the classical Nebentypus formalism.
-/

open Matrix Matrix.SpecialLinearGroup CongruenceSubgroup HeckeRing.GLn
open HeckeRing

open scoped Pointwise MatrixGroups ModularForm UpperHalfPlane

namespace HeckeRing.GL2.Unified

open HeckeRing.GL2

variable {N : ℕ} [NeZero N]

/-- A concrete integer matrix witness for an element of `Δ₀(N)`. -/
noncomputable def delta0IntegralMatrix (g : (Gamma0_pair N).Δ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  Classical.choose g.2.2.2

/-- The chosen integer matrix witness really represents `g`. -/
lemma delta0IntegralMatrix_spec (g : (Gamma0_pair N).Δ) :
    ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (delta0IntegralMatrix (N := N) g).map (Int.cast : ℤ → ℚ) :=
  (Classical.choose_spec g.2.2.2).1

/-- The lower-left entry of the chosen witness is divisible by `N`. -/
lemma delta0IntegralMatrix_lower_left_dvd (g : (Gamma0_pair N).Δ) :
    (N : ℤ) ∣ delta0IntegralMatrix (N := N) g 1 0 :=
  (Classical.choose_spec g.2.2.2).2.1

/-- The upper-left entry of the chosen witness is coprime to `N`. -/
lemma delta0IntegralMatrix_upper_left_coprime (g : (Gamma0_pair N).Δ) :
    Int.gcd (delta0IntegralMatrix (N := N) g 0 0) N = 1 :=
  (Classical.choose_spec g.2.2.2).2.2

/-- Any two integer witnesses for the same element of `Δ₀(N)` agree entrywise. -/
lemma delta0IntegralMatrix_witness_unique (g : (Gamma0_pair N).Δ)
    (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = A.map (Int.cast : ℤ → ℚ)) :
    delta0IntegralMatrix (N := N) g = A := by
  ext i j
  have h_entry :
      (((delta0IntegralMatrix (N := N) g).map (Int.cast : ℤ → ℚ)) i j) =
        ((A.map (Int.cast : ℤ → ℚ)) i j) := by
    rw [← delta0IntegralMatrix_spec (N := N) g, hA]
  simp only [Matrix.map_apply] at h_entry
  exact Int.cast_injective h_entry

/-- The upper-left entry of a `Δ₀(N)` witness is a unit modulo `N`. -/
lemma delta0UpperEntry_isUnit (g : (Gamma0_pair N).Δ) :
    IsUnit ((delta0IntegralMatrix (N := N) g 0 0 : ℤ) : ZMod N) := by
  have hco_nat : Nat.Coprime (delta0IntegralMatrix (N := N) g 0 0).natAbs N := by
    simpa using Int.isCoprime_iff_nat_coprime.mp
      (Int.isCoprime_iff_gcd_eq_one.mpr (delta0IntegralMatrix_upper_left_coprime (N := N) g))
  rcases Int.natAbs_eq (delta0IntegralMatrix (N := N) g 0 0) with hnonneg | hneg
  · rw [hnonneg]
    simpa [ZMod.coe_unitOfCoprime] using (ZMod.unitOfCoprime _ hco_nat).isUnit
  · rw [hneg]
    simpa [ZMod.coe_unitOfCoprime] using IsUnit.neg (ZMod.unitOfCoprime _ hco_nat).isUnit

/-- The unit in `(ZMod N)ˣ` attached to the upper-left entry of a `Δ₀(N)` matrix. -/
noncomputable def Delta0UpperUnit (g : (Gamma0_pair N).Δ) : (ZMod N)ˣ :=
  (delta0UpperEntry_isUnit (N := N) g).unit

/-- The value of `Delta0UpperUnit` as a `ZMod N`. -/
lemma Delta0UpperUnit_val (g : (Gamma0_pair N).Δ) :
    ((Delta0UpperUnit (N := N) g : (ZMod N)ˣ) : ZMod N) =
      (delta0IntegralMatrix (N := N) g 0 0 : ZMod N) :=
  IsUnit.unit_spec (delta0UpperEntry_isUnit (N := N) g)

/-- The chosen witness for a product in `Δ₀(N)` is the product of the chosen
integer witnesses. -/
lemma delta0IntegralMatrix_mul (g h : (Gamma0_pair N).Δ) :
    delta0IntegralMatrix (N := N) (g * h) =
      delta0IntegralMatrix (N := N) g * delta0IntegralMatrix (N := N) h := by
  apply delta0IntegralMatrix_witness_unique (N := N) (g := g * h)
  calc
    (((g * h : (Gamma0_pair N).Δ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = (((g : (Gamma0_pair N).Δ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
          (((h : (Gamma0_pair N).Δ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) := rfl
    _ = (delta0IntegralMatrix (N := N) g).map (Int.cast : ℤ → ℚ) *
          (delta0IntegralMatrix (N := N) h).map (Int.cast : ℤ → ℚ) := by
            rw [delta0IntegralMatrix_spec (N := N) g, delta0IntegralMatrix_spec (N := N) h]
    _ = (delta0IntegralMatrix (N := N) g * delta0IntegralMatrix (N := N) h).map
          (Int.cast : ℤ → ℚ) := by
            ext i j
            simp [Matrix.mul_apply]

/-- The upper-left units multiply on `Δ₀(N)`. -/
lemma Delta0UpperUnit_mul (g h : (Gamma0_pair N).Δ) :
    Delta0UpperUnit (N := N) (g * h) =
      Delta0UpperUnit (N := N) g * Delta0UpperUnit (N := N) h := by
  ext
  rw [Units.val_mul, Delta0UpperUnit_val, Delta0UpperUnit_val, Delta0UpperUnit_val,
    delta0IntegralMatrix_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hz :
      ((delta0IntegralMatrix (N := N) g 0 1 * delta0IntegralMatrix (N := N) h 1 0 : ℤ) :
        ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_of_dvd_right (delta0IntegralMatrix_lower_left_dvd (N := N) h) _
  simp [hz, add_comm]

/-- The semigroup character on `Δ₀(N)` obtained from the upper-left unit. -/
noncomputable def delta0NebentypusDeltaChar (χ : (ZMod N)ˣ →* ℂˣ) :
    (Gamma0_pair N).Δ →* ℂˣ where
  toFun g := χ (Delta0UpperUnit (N := N) g)
  map_one' := by
    have hmat : delta0IntegralMatrix (N := N) (1 : (Gamma0_pair N).Δ) = 1 := by
      apply delta0IntegralMatrix_witness_unique (N := N) (g := 1)
      simp
    have h_unit_one : Delta0UpperUnit (N := N) (1 : (Gamma0_pair N).Δ) = 1 := by
      ext
      rw [Delta0UpperUnit_val]
      simp [hmat]
    simp [h_unit_one]
  map_mul' g h := by
    rw [Delta0UpperUnit_mul (N := N) g h, map_mul]

private lemma units_coe_mul_inv_mul_right_cancel (a b : ℂˣ) :
    ((↑(a * b) : ℂ)⁻¹ * (↑b : ℂ)) = (↑a : ℂ)⁻¹ := by
  rw [Units.val_mul, _root_.mul_inv_rev, mul_assoc, mul_comm (↑a : ℂ)⁻¹ (↑b : ℂ),
    ← mul_assoc, inv_mul_cancel₀ b.ne_zero, one_mul]

/-- The restriction of the `Δ₀(N)` upper-left character to `Γ₀(N) = H`. It is
evaluated on `adj(h)` to match the adjugated representatives of the generalized
Hecke action; for `h ∈ Γ₀(N)` this is the usual lower-right Nebentypus entry. -/
noncomputable def delta0NebentypusHChar (χ : (ZMod N)ˣ →* ℂˣ) (h : GL (Fin 2) ℚ)
    (hh : h ∈ (Gamma0_pair N).H) : ℂˣ :=
  delta0NebentypusDeltaChar (N := N) χ ⟨h, (Gamma0_pair N).h₀ hh⟩

/-- The concrete `Δ₀(N)` representative `σᵢ · rep(D)` attached to an index in the
right-coset decomposition of a `Γ₀(N)` Hecke coset. -/
noncomputable def deltaRep_gen (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) : (Gamma0_pair N).Δ := by
  refine ⟨(i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ), ?_⟩
  exact (Gamma0_pair N).Δ.mul_mem
    ((Gamma0_pair N).h₀ (show (i.out : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).H from SetLike.coe_mem _))
    (show (HeckeCoset.rep D : GL (Fin 2) ℚ) ∈ (Gamma0_pair N).Δ from SetLike.coe_mem _)

/-- The nebentypus weight attached to a `Γ₀(N)` Hecke-coset summand. -/
noncomputable def delta0NebentypusWeight (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) : ℂˣ :=
  delta0NebentypusDeltaChar (N := N) χ (deltaRep_gen (N := N) D i)

/-- The twisted Hecke slash action attached to the existing `Γ₀(N)` Hecke coset.
Since the slash uses the adjugated representatives `tRep_gen = adj(σᵢ · rep(D))`,
each summand carries the inverse of the upper-left Nebentypus character, matching
the twisted fixed-space law `f ∣ h = η(h)⁻¹ f` for `h ∈ Γ₀(N)`. -/
noncomputable def twistedHeckeSlash_gen (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
    (↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹ •
      (f ∣[k] tRep_gen (Gamma0_pair N) D i)

/-- Positivity of the real determinant of an adjugated `Γ₀(N)` Hecke
representative. -/
lemma tRep_gen_Gamma0_det_pos (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    0 < (glMap (tRep_gen (Gamma0_pair N) D i)).det.val := by
  have hRat : 0 < (tRep_gen (Gamma0_pair N) D i).det.val := by
    have hdelta :
        0 <
          (((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ) :
              GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := by
      simpa [deltaRep_gen] using (deltaRep_gen (N := N) D i).prop.2.1
    change 0 < (GL_adjugate
      ((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ))).det.val
    rw [GeneralLinearGroup.val_det_apply, GL_adjugate_val, Matrix.det_adjugate,
      Fintype.card_fin]
    simpa using hdelta
  exact glMap_det_pos_of_rat_det_pos _ hRat

private lemma tRep_gen_sigma_eq_id
    (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    UpperHalfPlane.σ (glMap (tRep_gen (Gamma0_pair N) D i)) =
      ContinuousAlgEquiv.refl ℝ ℂ := by
  unfold UpperHalfPlane.σ
  simp only [tRep_gen_Gamma0_det_pos (N := N) D i, ↓reduceIte]

private lemma glMap_sigma_eq_id_of_mem_H (h : GL (Fin 2) ℚ) (hh : h ∈ (Gamma0_pair N).H) :
    UpperHalfPlane.σ (glMap h) = ContinuousAlgEquiv.refl ℝ ℂ := by
  unfold UpperHalfPlane.σ
  simp only [show 0 < (glMap h).det.val from by
    simpa using Gamma0_pair_det_pos N ⟨h, (Gamma0_pair N).h₀ hh⟩, ↓reduceIte]

private lemma smul_slash_tRep_gen (k : ℤ) (D : HeckeCoset (Gamma0_pair N))
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (c : ℂ) (f : ℍ → ℂ) :
    (c • f) ∣[k] tRep_gen (Gamma0_pair N) D i =
      c • (f ∣[k] tRep_gen (Gamma0_pair N) D i) := by
  change (c • f) ∣[k] glMap (tRep_gen (Gamma0_pair N) D i) =
    c • (f ∣[k] glMap (tRep_gen (Gamma0_pair N) D i))
  ext z
  rw [ModularForm.smul_slash, tRep_gen_sigma_eq_id (N := N) D i]
  rfl

@[simp] lemma twistedHeckeSlash_gen_add (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f g : ℍ → ℂ) :
    twistedHeckeSlash_gen (N := N) k χ D (f + g) =
      twistedHeckeSlash_gen (N := N) k χ D f +
        twistedHeckeSlash_gen (N := N) k χ D g := by
  ext z
  simp [twistedHeckeSlash_gen, Finset.sum_add_distrib]

@[simp] lemma twistedHeckeSlash_gen_smul (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (c : ℂ) (f : ℍ → ℂ) :
    twistedHeckeSlash_gen (N := N) k χ D (c • f) =
      c • twistedHeckeSlash_gen (N := N) k χ D f := by
  simp only [twistedHeckeSlash_gen, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ext z
  change
    (↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹ *
        (((c • f) ∣[k] tRep_gen (Gamma0_pair N) D i) z) =
      c * ((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹ *
        ((f ∣[k] tRep_gen (Gamma0_pair N) D i) z))
  rw [smul_slash_tRep_gen (N := N) k D i c f]
  simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- The weighted Hecke slash action extended by `ℤ`-linearity to the existing
Hecke ring `𝕋 (Gamma0_pair N) ℤ`. -/
noncomputable def twistedHeckeSlashExt_gen (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ) (f : ℍ → ℂ) : ℍ → ℂ :=
  T.sum (fun D c ↦ c • twistedHeckeSlash_gen (N := N) k χ D f)

lemma twistedHeckeSlashExt_gen_add (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) (f : ℍ → ℂ) :
    twistedHeckeSlashExt_gen (N := N) k χ (T₁ + T₂) f =
      twistedHeckeSlashExt_gen (N := N) k χ T₁ f +
        twistedHeckeSlashExt_gen (N := N) k χ T₂ f := by
  dsimp [twistedHeckeSlashExt_gen]
  exact Finsupp.sum_add_index'
    (h := fun D c ↦ c • twistedHeckeSlash_gen (N := N) k χ D f)
    (fun _ ↦ by simp) (fun _ _ _ ↦ by ext z; simp [add_smul])

/-- The raw function-space `Γ₀(N),χ` condition for the existing Hecke pair. -/
def IsGamma0TwistedInvariant (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : ℍ → ℂ) : Prop :=
  ∀ h : GL (Fin 2) ℚ, ∀ hh : h ∈ (Gamma0_pair N).H,
    f ∣[k] glMap h =
      (↑(delta0NebentypusHChar (N := N) χ (GL_adjugate h)
        (HeckePairAction.adjugate_mem_H h hh)) : ℂ) • f

/-- The abstract `Γ₀(N),χ` fixed submodule of functions. -/
noncomputable def gamma0TwistedInvariantFunctionSubmodule (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule ℂ (ℍ → ℂ) where
  carrier := {f | IsGamma0TwistedInvariant (N := N) k χ f}
  zero_mem' := by
    intro h hh
    simp [SlashAction.zero_slash]
  add_mem' := by
    intro f g hf hg h hh
    rw [SlashAction.add_slash, hf h hh, hg h hh]
    ext z
    simp [Pi.add_apply, mul_add]
  smul_mem' := by
    intro c f hf h hh
    rw [ModularForm.smul_slash, glMap_sigma_eq_id_of_mem_H (N := N) h hh, hf h hh]
    ext z
    simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- The `H`-correction element attached to replacing `h₁` by its quotient
representative in a right-coset decomposition. -/
noncomputable def gamma0Correction (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ) : GL (Fin 2) ℚ :=
  (HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
    (HeckeCoset.rep D : GL _ ℚ) * h₂

/-- The correction element lies in `Γ₀(N)`. -/
lemma gamma0Correction_mem_H (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (hq : (⟦q.out⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) = ⟦⟨h₁, hh₁⟩⟧) :
    gamma0Correction (N := N) D q h₁ h₂ ∈ (Gamma0_pair N).H := by
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact hq)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at h_K
  simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
  exact (Gamma0_pair N).H.mul_mem (by
    convert h_K using 1) hh₂

/-- The adjugate decomposition of a corrected representative. -/
lemma gamma0_adjugate_decomp_eq (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (h₁ h₂ : GL (Fin 2) ℚ) :
    GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) =
    GL_adjugate (gamma0Correction (N := N) D q h₁ h₂) *
      tRep_gen (Gamma0_pair N) D q := by
  simp only [tRep_gen, gamma0Correction]
  rw [← GL_adjugate_mul]
  congr 1
  simp only [mul_assoc, mul_inv_cancel_left]

/-- The `Δ₀(N)` element `h₁ · rep(D) · h₂`. -/
noncomputable def gamma0TripleDelta (D : HeckeCoset (Gamma0_pair N))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H) : (Gamma0_pair N).Δ :=
  ⟨h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂,
    (Gamma0_pair N).Δ.mul_mem
      ((Gamma0_pair N).Δ.mul_mem ((Gamma0_pair N).h₀ hh₁)
        (show (HeckeCoset.rep D : GL _ ℚ) ∈ (Gamma0_pair N).Δ from SetLike.coe_mem _))
      ((Gamma0_pair N).h₀ hh₂)⟩

/-- The correction term as a `Δ₀(N)` element via `H ⊆ Δ`. -/
noncomputable def gamma0CorrectionDelta (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) (h₁ h₂ : GL (Fin 2) ℚ)
    (hκ : gamma0Correction (N := N) D q h₁ h₂ ∈ (Gamma0_pair N).H) : (Gamma0_pair N).Δ :=
  ⟨gamma0Correction (N := N) D q h₁ h₂, (Gamma0_pair N).h₀ hκ⟩

/-- The corrected representative factorization inside `Δ₀(N)`. -/
lemma gamma0TripleDelta_eq_deltaRep_mul_correction (D : HeckeCoset (Gamma0_pair N))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (hκ : gamma0Correction (N := N) D q h₁ h₂ ∈ (Gamma0_pair N).H) :
    gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂ =
      deltaRep_gen (N := N) D q * gamma0CorrectionDelta (N := N) D q h₁ h₂ hκ := by
  apply Subtype.ext
  change h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂ =
    ((q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)) *
      gamma0Correction (N := N) D q h₁ h₂
  simp only [gamma0Correction]
  group

private lemma slash_GL_adjugate_triple_eq_correction_slash (k : ℤ)
    (D : HeckeCoset (Gamma0_pair N)) (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ) (f : ℍ → ℂ) :
    f ∣[k] GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) =
      (f ∣[k] glMap (GL_adjugate (gamma0Correction (N := N) D q h₁ h₂))) ∣[k]
        glMap (tRep_gen (Gamma0_pair N) D q) := by
  rw [gamma0_adjugate_decomp_eq (N := N) D q h₁ h₂]
  change f ∣[k] glMap (GL_adjugate (gamma0Correction (N := N) D q h₁ h₂) *
      tRep_gen (Gamma0_pair N) D q) = _
  rw [map_mul, SlashAction.slash_mul]

private lemma delta0NebentypusHChar_adjugate_adjugate_correction (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h₁ h₂ : GL (Fin 2) ℚ)
    (hκ : gamma0Correction (N := N) D q h₁ h₂ ∈ (Gamma0_pair N).H)
    (hκadj : GL_adjugate (gamma0Correction (N := N) D q h₁ h₂) ∈ (Gamma0_pair N).H) :
    delta0NebentypusHChar (N := N) χ
        (GL_adjugate (GL_adjugate (gamma0Correction (N := N) D q h₁ h₂)))
        (HeckePairAction.adjugate_mem_H
          (GL_adjugate (gamma0Correction (N := N) D q h₁ h₂)) hκadj) =
      delta0NebentypusDeltaChar (N := N) χ
        (gamma0CorrectionDelta (N := N) D q h₁ h₂ hκ) := by
  unfold delta0NebentypusHChar gamma0CorrectionDelta
  apply congrArg (delta0NebentypusDeltaChar (N := N) χ)
  apply Subtype.ext
  exact GL_adjugate_involutive _

/-- Twisted replacement for `slash_tRep_gen_of_mem`: the `H` correction is
absorbed by the inverse character coefficient. -/
lemma twisted_weighted_slash_tRep_gen_of_mem (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant (N := N) k χ f) :
    let q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
    ((↑(delta0NebentypusDeltaChar (N := N) χ
      (gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂)) : ℂ)⁻¹) •
        (f ∣[k] GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)) =
      ((↑(delta0NebentypusDeltaChar (N := N) χ
        (deltaRep_gen (N := N) D q)) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D q) := by
  intro q
  have hκ : gamma0Correction (N := N) D q h₁ h₂ ∈ (Gamma0_pair N).H :=
    gamma0Correction_mem_H (N := N) D q h₁ hh₁ h₂ hh₂ (Quotient.out_eq q)
  have hη :
      delta0NebentypusDeltaChar (N := N) χ
          (gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂) =
        delta0NebentypusDeltaChar (N := N) χ (deltaRep_gen (N := N) D q) *
          delta0NebentypusDeltaChar (N := N) χ
            (gamma0CorrectionDelta (N := N) D q h₁ h₂ hκ) := by
    rw [gamma0TripleDelta_eq_deltaRep_mul_correction (N := N) D q h₁ hh₁ h₂ hh₂ hκ]
    exact map_mul _ _ _
  rw [slash_GL_adjugate_triple_eq_correction_slash (N := N) k D q h₁ h₂ f]
  have hκadj : GL_adjugate (gamma0Correction (N := N) D q h₁ h₂) ∈
      (Gamma0_pair N).H :=
    HeckePairAction.adjugate_mem_H _ hκ
  rw [hf (GL_adjugate (gamma0Correction (N := N) D q h₁ h₂)) hκadj,
    ModularForm.smul_slash]
  · rw [tRep_gen_sigma_eq_id (N := N) D q,
      delta0NebentypusHChar_adjugate_adjugate_correction (N := N) χ D q h₁ h₂ hκ hκadj]
    have hscalar :
        ((↑(delta0NebentypusDeltaChar (N := N) χ
          (gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂)) : ℂ)⁻¹ *
          (↑(delta0NebentypusDeltaChar (N := N) χ
            (gamma0CorrectionDelta (N := N) D q h₁ h₂ hκ)) : ℂ)) =
        (↑(delta0NebentypusDeltaChar (N := N) χ
          (deltaRep_gen (N := N) D q)) : ℂ)⁻¹ := by
      rw [hη]
      exact units_coe_mul_inv_mul_right_cancel
        (delta0NebentypusDeltaChar (N := N) χ (deltaRep_gen (N := N) D q))
        (delta0NebentypusDeltaChar (N := N) χ
          (gamma0CorrectionDelta (N := N) D q h₁ h₂ hκ))
    ext z
    simp only [Pi.smul_apply, smul_eq_mul, ContinuousAlgEquiv.refl_apply, RingHom.id_apply]
    rw [← mul_assoc, hscalar]
    rfl

private lemma units_coe_inv_right_eq_mul_inv_mul (a b : ℂˣ) (x : ℂ) :
    (↑b : ℂ)⁻¹ * x = (↑a : ℂ) * (((↑(a * b) : ℂ)⁻¹) * x) := by
  simp [Units.val_mul, _root_.mul_inv_rev, mul_assoc, mul_left_comm, a.ne_zero]

private lemma units_coe_inv_right_smul_eq_mul_smul_inv_mul (a b : ℂˣ) (g : ℍ → ℂ) :
    (↑b : ℂ)⁻¹ • g = (↑a : ℂ) • ((↑(a * b) : ℂ)⁻¹ • g) := by
  ext z
  simp only [Pi.smul_apply, smul_eq_mul]
  exact units_coe_inv_right_eq_mul_inv_mul a b (g z)

private lemma units_inv_smul_inv_smul_eq_mul_inv_smul (a b : ℂˣ) (g : ℍ → ℂ) :
    (↑a : ℂ)⁻¹ • ((↑b : ℂ)⁻¹ • g) = (↑(a * b) : ℂ)⁻¹ • g := by
  ext z
  simp [Pi.smul_apply, smul_eq_mul, Units.val_mul, _root_.mul_inv_rev,
    mul_left_comm, mul_comm]

private noncomputable def gamma0LeftMulQuot (D : HeckeCoset (Gamma0_pair N))
    (σ : (Gamma0_pair N).H) :
    decompQuot (Gamma0_pair N) (HeckeCoset.rep D) →
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D) :=
  fun i ↦ ⟦⟨σ * i.out, (Gamma0_pair N).H.mul_mem σ.prop (SetLike.coe_mem _)⟩⟧

private lemma gamma0LeftMulQuot_injective (D : HeckeCoset (Gamma0_pair N))
    (σ : (Gamma0_pair N).H) :
    Function.Injective (gamma0LeftMulQuot (N := N) D σ) := by
  intro i₁ i₂ h
  simp only [gamma0LeftMulQuot] at h
  by_contra hne
  have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact h)
  simp only [Subgroup.mem_subgroupOf] at h_K
  have h_mem : (HeckeCoset.rep D : GL _ ℚ)⁻¹ *
      ((i₁.out : GL _ ℚ)⁻¹ * (i₂.out : GL _ ℚ)) *
      (HeckeCoset.rep D : GL _ ℚ) ∈ (Gamma0_pair N).H := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at h_K
    simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
    convert h_K using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  exact decompQuot_coset_diff (Gamma0_pair N) (HeckeCoset.rep D) i₁ i₂ hne
    (leftCoset_eq_of_not_disjoint (Gamma0_pair N).H _ _ (by
      rw [Set.not_disjoint_iff]
      refine ⟨(i₂.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ), ?_, ?_⟩
      · rw [smul_eq_singleton_mul]
        exact ⟨_, rfl, _, h_mem, by group⟩
      · rw [smul_eq_singleton_mul]
        exact ⟨_, rfl, 1, (Gamma0_pair N).H.one_mem, by group⟩))

private noncomputable def gamma0LeftMulEquiv (D : HeckeCoset (Gamma0_pair N))
    (σ : (Gamma0_pair N).H) :
    decompQuot (Gamma0_pair N) (HeckeCoset.rep D) ≃
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D) :=
  Equiv.ofBijective _ ⟨gamma0LeftMulQuot_injective (N := N) D σ,
    Finite.surjective_of_injective (gamma0LeftMulQuot_injective (N := N) D σ)⟩

private lemma gamma0TripleDelta_left_eq_h_mul_deltaRep (D : HeckeCoset (Gamma0_pair N))
    (σ : GL (Fin 2) ℚ) (hσ : σ ∈ (Gamma0_pair N).H)
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    gamma0TripleDelta (N := N) D (σ * (i.out : GL (Fin 2) ℚ))
        ((Gamma0_pair N).H.mul_mem hσ (SetLike.coe_mem _))
        1 (Gamma0_pair N).H.one_mem =
      (⟨σ, (Gamma0_pair N).h₀ hσ⟩ : (Gamma0_pair N).Δ) *
        deltaRep_gen (N := N) D i := by
  apply Subtype.ext
  change (σ * (i.out : GL _ ℚ)) * (HeckeCoset.rep D : GL _ ℚ) * 1 =
    σ * ((i.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ))
  group

private lemma delta0Nebentypus_left_weight (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N))
    (σ : GL (Fin 2) ℚ) (hσ : σ ∈ (Gamma0_pair N).H)
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    delta0NebentypusDeltaChar (N := N) χ
      (gamma0TripleDelta (N := N) D (σ * (i.out : GL (Fin 2) ℚ))
        ((Gamma0_pair N).H.mul_mem hσ (SetLike.coe_mem _))
        1 (Gamma0_pair N).H.one_mem) =
    delta0NebentypusHChar (N := N) χ σ hσ *
      delta0NebentypusWeight (N := N) χ D i := by
  rw [gamma0TripleDelta_left_eq_h_mul_deltaRep (N := N) D σ hσ i]
  exact map_mul _ _ _

private lemma twistedHeckeSlash_gen_slash_distrib (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) (g : GL (Fin 2) ℚ) :
    (twistedHeckeSlash_gen (N := N) k χ D f) ∣[k] g =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D i)) ∣[k] g := by
  simp only [twistedHeckeSlash_gen]
  induction Finset.univ (α := decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
      using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp [Finset.sum_cons, SlashAction.add_slash, ih]

private lemma tRep_gen_mul_eq_adjugate_leftMul (D : HeckeCoset (Gamma0_pair N))
    (σ_Q : GL (Fin 2) ℚ) (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    tRep_gen (Gamma0_pair N) D i * σ_Q =
      GL_adjugate (GL_adjugate σ_Q * (i.out : GL (Fin 2) ℚ) *
        (HeckeCoset.rep D : GL (Fin 2) ℚ)) := by
  change GL_adjugate _ * σ_Q = _
  conv_lhs =>
    rw [show σ_Q = GL_adjugate (GL_adjugate σ_Q) from
      (GL_adjugate_involutive σ_Q).symm,
      ← GL_adjugate_mul]
  rw [show GL_adjugate σ_Q * (i.out : GL (Fin 2) ℚ) *
      (HeckeCoset.rep D : GL (Fin 2) ℚ) =
      GL_adjugate σ_Q *
      ((i.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D : GL (Fin 2) ℚ)) from by
        group]

private lemma twistedHeckeSlash_gen_perm_summand (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N))
    (σ_Q : GL (Fin 2) ℚ) (hσ : σ_Q ∈ (Gamma0_pair N).H)
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant (N := N) k χ f)
    (i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    (((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D i)) ∣[k] glMap σ_Q =
      (↑(delta0NebentypusHChar (N := N) χ (GL_adjugate σ_Q)
          (HeckePairAction.adjugate_mem_H σ_Q hσ)) : ℂ) •
        (((↑(delta0NebentypusWeight (N := N) χ D
            (gamma0LeftMulEquiv (N := N) D
              ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩ i)) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D
            (gamma0LeftMulEquiv (N := N) D
              ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩ i))) := by
  set σA : (Gamma0_pair N).H :=
    ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩
  set π := gamma0LeftMulEquiv (N := N) D σA
  rw [ModularForm.smul_slash, glMap_sigma_eq_id_of_mem_H (N := N) σ_Q hσ]
  have hslash :
      (f ∣[k] tRep_gen (Gamma0_pair N) D i) ∣[k] glMap σ_Q =
        f ∣[k] (tRep_gen (Gamma0_pair N) D i * σ_Q) := by
    change (f ∣[k] glMap (tRep_gen (Gamma0_pair N) D i)) ∣[k] glMap σ_Q =
      f ∣[k] glMap (tRep_gen (Gamma0_pair N) D i * σ_Q)
    rw [map_mul, ← SlashAction.slash_mul]
  rw [hslash, tRep_gen_mul_eq_adjugate_leftMul (N := N) D σ_Q i]
  have htw' :
      ((↑(delta0NebentypusDeltaChar (N := N) χ
        (gamma0TripleDelta (N := N) D (σA.val * (i.out : GL (Fin 2) ℚ))
          ((Gamma0_pair N).H.mul_mem σA.prop (SetLike.coe_mem _))
          1 (Gamma0_pair N).H.one_mem)) : ℂ)⁻¹) •
        (f ∣[k] GL_adjugate ((σA.val * (i.out : GL (Fin 2) ℚ)) *
          (HeckeCoset.rep D : GL (Fin 2) ℚ) * 1)) =
      ((↑(delta0NebentypusWeight (N := N) χ D (π i)) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D (π i)) := by
    simpa [π, gamma0LeftMulEquiv, gamma0LeftMulQuot, delta0NebentypusWeight]
      using twisted_weighted_slash_tRep_gen_of_mem (N := N) k χ D
        (σA.val * (i.out : GL (Fin 2) ℚ))
        ((Gamma0_pair N).H.mul_mem σA.prop (SetLike.coe_mem _))
        1 (Gamma0_pair N).H.one_mem f hf
  rw [show GL_adjugate (σA.val * (i.out : GL (Fin 2) ℚ) *
        (HeckeCoset.rep D : GL (Fin 2) ℚ)) =
      GL_adjugate ((σA.val * (i.out : GL (Fin 2) ℚ)) *
        (HeckeCoset.rep D : GL (Fin 2) ℚ) * 1) by group]
  rw [← htw', delta0Nebentypus_left_weight (N := N) χ D σA.val σA.prop i]
  exact units_coe_inv_right_smul_eq_mul_smul_inv_mul
    (delta0NebentypusHChar (N := N) χ (GL_adjugate σ_Q)
      (HeckePairAction.adjugate_mem_H σ_Q hσ))
    (delta0NebentypusWeight (N := N) χ D i)
    (f ∣[k] GL_adjugate ((σA.val * (i.out : GL (Fin 2) ℚ)) *
      (HeckeCoset.rep D : GL (Fin 2) ℚ) * 1))

/-- A single twisted Hecke-coset operator preserves the `Γ₀(N),χ` fixed space. -/
lemma twistedHeckeSlash_gen_preserves_invariant (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ)
    (hf : IsGamma0TwistedInvariant (N := N) k χ f) :
    IsGamma0TwistedInvariant (N := N) k χ
      (twistedHeckeSlash_gen (N := N) k χ D f) := by
  intro σ_Q hσ
  let σA : (Gamma0_pair N).H :=
    ⟨GL_adjugate σ_Q, HeckePairAction.adjugate_mem_H σ_Q hσ⟩
  let π := gamma0LeftMulEquiv (N := N) D σA
  have h_perm :
      ∀ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹) •
            (f ∣[k] tRep_gen (Gamma0_pair N) D i)) ∣[k] glMap σ_Q =
          (↑(delta0NebentypusHChar (N := N) χ (GL_adjugate σ_Q)
              (HeckePairAction.adjugate_mem_H σ_Q hσ)) : ℂ) •
            (((↑(delta0NebentypusWeight (N := N) χ D (π i)) : ℂ)⁻¹) •
              (f ∣[k] tRep_gen (Gamma0_pair N) D (π i))) :=
    fun i ↦ twistedHeckeSlash_gen_perm_summand (N := N) k χ D σ_Q hσ f hf i
  rw [show (twistedHeckeSlash_gen (N := N) k χ D f) ∣[k] glMap σ_Q =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        (((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D i)) ∣[k] glMap σ_Q from by
    simpa using (twistedHeckeSlash_gen_slash_distrib (N := N) k χ D f σ_Q)]
  rw [Finset.sum_congr rfl (fun i _ ↦ h_perm i), ← Finset.smul_sum,
    Fintype.sum_equiv π _ (fun i ↦
      ((↑(delta0NebentypusWeight (N := N) χ D i) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D i)) (fun _ ↦ rfl)]
  rfl

private lemma delta0NebentypusWeight_mul_eq_tripleDelta (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (heq : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
        ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) =
      h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    delta0NebentypusWeight (N := N) χ D₁ p.1 *
        delta0NebentypusWeight (N := N) χ D₂ p.2 =
      delta0NebentypusDeltaChar (N := N) χ
        (gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂) := by
  have hdelta_prod :
      deltaRep_gen (N := N) D₁ p.1 * deltaRep_gen (N := N) D₂ p.2 =
        gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂ := by
    apply Subtype.ext
    change (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
        ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) =
      h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂
    exact heq
  change delta0NebentypusDeltaChar (N := N) χ
        (deltaRep_gen (N := N) D₁ p.1) *
      delta0NebentypusDeltaChar (N := N) χ
        (deltaRep_gen (N := N) D₂ p.2) =
    delta0NebentypusDeltaChar (N := N) χ
      (gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂)
  rw [← map_mul, hdelta_prod]

private lemma twisted_weighted_slash_product_eq (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (h₁ : GL (Fin 2) ℚ) (hh₁ : h₁ ∈ (Gamma0_pair N).H)
    (h₂ : GL (Fin 2) ℚ) (hh₂ : h₂ ∈ (Gamma0_pair N).H)
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant (N := N) k χ f)
    (heq : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
        ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) =
      h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂) :
    ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1) =
      ((↑(delta0NebentypusWeight (N := N) χ D
          (⟦⟨h₁, hh₁⟩⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D
          (⟦⟨h₁, hh₁⟩⟧ : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))) := by
  set q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  calc
    ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1)
        = ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
            (((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
              ((f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2) ∣[k]
                tRep_gen (Gamma0_pair N) D₁ p.1)) := by
          rw [smul_slash_tRep_gen (N := N) k D₁ p.1]
    _ = ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1 *
            delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
          ((f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1) :=
          units_inv_smul_inv_smul_eq_mul_inv_smul
            (delta0NebentypusWeight (N := N) χ D₁ p.1)
            (delta0NebentypusWeight (N := N) χ D₂ p.2)
            ((f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2) ∣[k]
              tRep_gen (Gamma0_pair N) D₁ p.1)
    _ = ((↑(delta0NebentypusDeltaChar (N := N) χ
            (gamma0TripleDelta (N := N) D h₁ hh₁ h₂ hh₂)) : ℂ)⁻¹) •
          (f ∣[k] GL_adjugate (h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂)) := by
          rw [delta0NebentypusWeight_mul_eq_tripleDelta (N := N) χ D₁ D₂ D p
            h₁ hh₁ h₂ hh₂ heq]
          have hslash : (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2) ∣[k]
              tRep_gen (Gamma0_pair N) D₁ p.1 =
              f ∣[k] (tRep_gen (Gamma0_pair N) D₂ p.2 *
                tRep_gen (Gamma0_pair N) D₁ p.1) := by
            change (f ∣[k] glMap (tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
                glMap (tRep_gen (Gamma0_pair N) D₁ p.1) =
              f ∣[k] glMap (tRep_gen (Gamma0_pair N) D₂ p.2 *
                tRep_gen (Gamma0_pair N) D₁ p.1)
            rw [map_mul, ← SlashAction.slash_mul]
          rw [hslash, tRep_gen_mul_anti D₁ D₂ p.1 p.2, heq]
    _ = ((↑(delta0NebentypusWeight (N := N) χ D q) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D q) := by
          simpa [q, delta0NebentypusWeight] using
            twisted_weighted_slash_tRep_gen_of_mem (N := N) k χ D h₁ hh₁ h₂ hh₂ f hf

private lemma twisted_slash_and_coset_of_mulMap_eq (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant (N := N) k χ f)
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (hp : mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D) :
    ∃ q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
      (((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1) =
        ((↑(delta0NebentypusWeight (N := N) χ D q) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D q)) ∧
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) := by
  have hmem : (p.1.out : GL (Fin 2) ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet D := by
    have : HeckeCoset.toSet (mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) = HeckeCoset.toSet D := by
      rw [hp]
    rw [← this]
    show _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (Gamma0_pair N))
    simp only [HeckeCoset.toSet_mk]
    exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hmem
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hmem
  let q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := ⟦⟨h₁, hh₁⟩⟧
  refine ⟨q, ?_, ?_⟩
  · exact twisted_weighted_slash_product_eq (N := N) k χ D₁ D₂ D p h₁ hh₁ h₂ hh₂ f hf heq
  · have h_K := QuotientGroup.leftRel_apply.mp (Quotient.exact (Quotient.out_eq q))
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at h_K
    simp only [ConjAct.ofConjAct_toConjAct, map_inv, inv_inv] at h_K
    set κ := (HeckeCoset.rep D : GL _ ℚ)⁻¹ * ((q.out : GL _ ℚ)⁻¹ * h₁) *
        (HeckeCoset.rep D : GL _ ℚ)
    rw [Set.singleton_mul_singleton, heq]
    apply leftCoset_eq_of_not_disjoint
    rw [Set.not_disjoint_iff]
    exact ⟨h₁ * (HeckeCoset.rep D : GL _ ℚ) * h₂,
      ⟨1, (Gamma0_pair N).H.one_mem, by simp [smul_eq_mul]⟩,
      ⟨κ * h₂, (Gamma0_pair N).H.mul_mem h_K hh₂, by
        simp only [smul_eq_mul, κ]
        group⟩⟩

private lemma gamma0_prod_mem_D_of_rightCoset (D : HeckeCoset (Gamma0_pair N))
    (g : GL (Fin 2) ℚ) (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h : GL (Fin 2) ℚ) (hh : h ∈ ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)))
    (hprod : g = (q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ) * h) :
    g ∈ HeckeCoset.toSet D := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  exact ⟨(q.out : GL (Fin 2) ℚ), SetLike.coe_mem q.out, h, hh, hprod⟩

private lemma gamma0_prod_mem_mulMap (D₁ D₂ : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂)) :
    (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      HeckeCoset.toSet (mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2)) := by
  show _ ∈ HeckeCoset.toSet (⟦⟨_, _⟩⟧ : HeckeCoset (Gamma0_pair N))
  simp only [HeckeCoset.toSet_mk]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

private lemma gamma0_mulMap_eq_of_rightCoset (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (hp_rc : ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))) :
    mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2) = D := by
  have h_in_rc : (p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ) *
      ((p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)) ∈
      ({(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} : Set _) *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) := by
    rw [← hp_rc, Set.singleton_mul_singleton]
    exact ⟨_, rfl, 1, (Gamma0_pair N).H.one_mem, by simp only [mul_one]⟩
  obtain ⟨_, hd_eq, h, hh, hprod⟩ := h_in_rc
  rw [Set.mem_singleton_iff] at hd_eq
  subst hd_eq
  set M := mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2)
  exact HeckeCoset_ext_toSet (P := Gamma0_pair N) (by
    rw [HeckeCoset.toSet_eq_rep, HeckeCoset.toSet_eq_rep]
    exact DoubleCoset.eq_of_not_disjoint (by
      rw [Set.not_disjoint_iff]
      have hm := gamma0_prod_mem_mulMap (N := N) D₁ D₂ p
      rw [HeckeCoset.toSet_eq_rep] at hm
      have hd := gamma0_prod_mem_D_of_rightCoset (N := N) D _ q h hh hprod.symm
      rw [HeckeCoset.toSet_eq_rep] at hd
      exact ⟨_, hm, hd⟩))

open Classical in
private lemma twisted_fiber_filter_card_eq (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (q_of : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) →
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (h_coset_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)))
    (q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D)) :
    ((Finset.univ.filter
        (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
            decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) ↦
          mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
            (p.1, p.2) = D)).filter (fun p ↦ q_of p = q)).card =
      Nat.card
        {p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
             decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) |
          ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
          {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
          {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))} := by
  rw [← Nat.card_eq_finsetCard]
  apply Nat.card_congr
  exact {
    toFun := fun ⟨p, hp⟩ ↦ ⟨p, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rw [← hp.2]
      exact h_coset_eq p hp.1⟩
    invFun := fun ⟨p, hp_rc⟩ ↦ ⟨p, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hmap := gamma0_mulMap_eq_of_rightCoset (N := N) D₁ D₂ D p q hp_rc
      refine ⟨hmap, ?_⟩
      by_contra hne
      exact decompQuot_coset_diff (Gamma0_pair N) (HeckeCoset.rep D) (q_of p) q hne
        ((h_coset_eq p hmap).symm.trans hp_rc)⟩
    left_inv := fun ⟨_, _⟩ ↦ rfl
    right_inv := fun ⟨_, _⟩ ↦ rfl }

private lemma twisted_filtered_sum_collapse_of_qOf {M : Type*} [AddCommGroup M]
    [DecidableEq (HeckeCoset (Gamma0_pair N))] (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (q_of : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) →
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D))
    (F : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) → M)
    (G : decompQuot (Gamma0_pair N) (HeckeCoset.rep D) → M)
    (h_term_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2) = D → F p = G (q_of p))
    (h_coset_eq : ∀ p, mulMap (Gamma0_pair N) (HeckeCoset.rep D₁)
        (HeckeCoset.rep D₂) (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
        {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
        ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
                 decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) =>
          mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
            (p.1, p.2) = D), F p) =
      (m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D • ∑ q, G q := by
  classical
  set S := Finset.univ.filter
    (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
        decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) ↦
      mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
        (p.1, p.2) = D)
  rw [Finset.sum_congr rfl (fun p hp ↦ by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    exact h_term_eq p hp)]
  rw [← Finset.sum_fiberwise (s := S) (g := q_of)]
  conv_lhs =>
    arg 2
    ext q
    rw [Finset.sum_congr rfl (fun p hp ↦ by
      simp only [Finset.mem_filter] at hp
      rw [hp.2])]
    rw [Finset.sum_const]
  have h_fiber_eq : ∀ q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
      (S.filter (fun p ↦ q_of p = q)).card = Nat.card
        {p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
             decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) |
          ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
          {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
          {(q.out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
          ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))} := by
    intro q
    convert twisted_fiber_filter_card_eq (N := N) D₁ D₂ D q_of h_coset_eq q using 2
    ext p
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [h_fiber_eq,
    heckeMultiplicity_uniform (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D]
  set n := Nat.card
    {p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
         decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) |
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {(HeckeCoset.rep D : GL _ ℚ)} * ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ))}
  rw [Finset.sum_nsmul]
  simp only [m, Finsupp.coe_mk, heckeMultiplicity, n, Nat.cast_smul_eq_nsmul ℤ]

private lemma twistedHeckeSlash_gen_fiber_sum
    [DecidableEq (HeckeCoset (Gamma0_pair N))]
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ D : HeckeCoset (Gamma0_pair N))
    (_hD : D ∈ mulSupport (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂))
    (f : ℍ → ℂ) (hf : IsGamma0TwistedInvariant (N := N) k χ f) :
    (∑ p ∈ Finset.univ.filter
        (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
                 decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) =>
          mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
            (p.1, p.2) = D),
      ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1)) =
    (m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)) D •
      ∑ q : decompQuot (Gamma0_pair N) (HeckeCoset.rep D),
        ((↑(delta0NebentypusWeight (N := N) χ D q) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D q) := by
  classical
  have h_main := twisted_slash_and_coset_of_mulMap_eq (N := N) k χ D₁ D₂ D f hf
  set q_of : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) →
      decompQuot (Gamma0_pair N) (HeckeCoset.rep D) := fun p ↦
    if h : mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
        (p.1, p.2) = D
    then (h_main p h).choose else ⟦1⟧
  have h_term_eq : ∀ p,
      mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
        (p.1, p.2) = D →
      ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
        ((((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
          (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ p.1) =
      ((↑(delta0NebentypusWeight (N := N) χ D (q_of p)) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D (q_of p)) := by
    intro p hp
    simp only [q_of, hp, dif_pos]
    exact (h_main p hp).choose_spec.1
  have h_coset_eq : ∀ p,
      mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
        (p.1, p.2) = D →
      ({(p.1.out : GL _ ℚ) * (HeckeCoset.rep D₁ : GL _ ℚ)} : Set _) *
      {(p.2.out : GL _ ℚ) * (HeckeCoset.rep D₂ : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) =
      {((q_of p).out : GL _ ℚ) * (HeckeCoset.rep D : GL _ ℚ)} *
      ((Gamma0_pair N).H : Set (GL (Fin 2) ℚ)) := by
    intro p hp
    simp only [q_of, hp, dif_pos]
    exact (h_main p hp).choose_spec.2
  exact twisted_filtered_sum_collapse_of_qOf (N := N) D₁ D₂ D q_of
    (fun p ↦ ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
      ((((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
        (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
          tRep_gen (Gamma0_pair N) D₁ p.1))
    (fun q ↦ ((↑(delta0NebentypusWeight (N := N) χ D q) : ℂ)⁻¹) •
      (f ∣[k] tRep_gen (Gamma0_pair N) D q))
    h_term_eq h_coset_eq

private lemma twistedHeckeSlash_gen_comp_eq_prod_sum (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ) :
    twistedHeckeSlash_gen (N := N) k χ D₁
        (twistedHeckeSlash_gen (N := N) k χ D₂ f) =
      ∑ p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
          decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂),
        ((↑(delta0NebentypusWeight (N := N) χ D₁ p.1) : ℂ)⁻¹) •
          ((((↑(delta0NebentypusWeight (N := N) χ D₂ p.2) : ℂ)⁻¹) •
            (f ∣[k] tRep_gen (Gamma0_pair N) D₂ p.2)) ∣[k]
              tRep_gen (Gamma0_pair N) D₁ p.1) := by
  rw [show twistedHeckeSlash_gen (N := N) k χ D₁
      (twistedHeckeSlash_gen (N := N) k χ D₂ f) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁),
        ((↑(delta0NebentypusWeight (N := N) χ D₁ i) : ℂ)⁻¹) •
          ((twistedHeckeSlash_gen (N := N) k χ D₂ f) ∣[k]
            tRep_gen (Gamma0_pair N) D₁ i) from rfl]
  rw [show (∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁),
      ((↑(delta0NebentypusWeight (N := N) χ D₁ i) : ℂ)⁻¹) •
        ((twistedHeckeSlash_gen (N := N) k χ D₂ f) ∣[k]
          tRep_gen (Gamma0_pair N) D₁ i)) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁),
        ((↑(delta0NebentypusWeight (N := N) χ D₁ i) : ℂ)⁻¹) •
          (∑ j : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂),
            (((↑(delta0NebentypusWeight (N := N) χ D₂ j) : ℂ)⁻¹) •
              (f ∣[k] tRep_gen (Gamma0_pair N) D₂ j)) ∣[k]
                tRep_gen (Gamma0_pair N) D₁ i) from by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact twistedHeckeSlash_gen_slash_distrib (N := N) k χ D₂ f
      (tRep_gen (Gamma0_pair N) D₁ i)]
  rw [show (∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁),
      ((↑(delta0NebentypusWeight (N := N) χ D₁ i) : ℂ)⁻¹) •
        (∑ j : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂),
          (((↑(delta0NebentypusWeight (N := N) χ D₂ j) : ℂ)⁻¹) •
            (f ∣[k] tRep_gen (Gamma0_pair N) D₂ j)) ∣[k]
              tRep_gen (Gamma0_pair N) D₁ i)) =
      ∑ i : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁),
        ∑ j : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂),
          ((↑(delta0NebentypusWeight (N := N) χ D₁ i) : ℂ)⁻¹) •
            ((((↑(delta0NebentypusWeight (N := N) χ D₂ j) : ℂ)⁻¹) •
              (f ∣[k] tRep_gen (Gamma0_pair N) D₂ j)) ∣[k]
                tRep_gen (Gamma0_pair N) D₁ i) from by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.smul_sum]]
  rw [← Fintype.sum_prod_type']

/-- Multiplicativity of the twisted slash action on `Γ₀(N),χ`-invariant
functions, using the existing `Γ₀(N)` Hecke-ring multiplication. -/
theorem twistedHeckeSlash_gen_comp (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (f : ℍ → ℂ)
    (hf : IsGamma0TwistedInvariant (N := N) k χ f)
    (hcomm : T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1 =
      T_single (Gamma0_pair N) ℤ D₁ 1 * T_single (Gamma0_pair N) ℤ D₂ 1) :
    twistedHeckeSlash_gen (N := N) k χ D₁
        (twistedHeckeSlash_gen (N := N) k χ D₂ f) =
      twistedHeckeSlashExt_gen (N := N) k χ
        (T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1) f := by
  rw [show twistedHeckeSlashExt_gen (N := N) k χ
      (T_single (Gamma0_pair N) ℤ D₂ 1 * T_single (Gamma0_pair N) ℤ D₁ 1) f =
      (m (Gamma0_pair N) (HeckeCoset.rep D₂) (HeckeCoset.rep D₁)).sum
        (fun D c ↦ c • twistedHeckeSlash_gen (N := N) k χ D f) from by
    unfold twistedHeckeSlashExt_gen
    rw [mul_singleton_𝕋]
    simp]
  have h_comm : m (Gamma0_pair N) (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) =
      m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
    simpa only [T_single_one_mul_T_single_one] using hcomm
  rw [h_comm, twistedHeckeSlash_gen_comp_eq_prod_sum (N := N) k χ D₁ D₂ f]
  letI : DecidableEq (HeckeCoset (Gamma0_pair N)) := Classical.decEq _
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p ↦ mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
      (p.1, p.2))
    (fun p _ ↦ Finset.mem_image_of_mem _ (Finset.mem_univ _)),
    show Finset.image
      (fun p : decompQuot (Gamma0_pair N) (HeckeCoset.rep D₁) ×
          decompQuot (Gamma0_pair N) (HeckeCoset.rep D₂) ↦
        mulMap (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (p.1, p.2))
        Finset.univ =
      mulSupport (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl,
    Finsupp.sum,
    show (m (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)).support =
      mulSupport (Gamma0_pair N) (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) from rfl]
  exact Finset.sum_congr rfl fun D hD ↦
    twistedHeckeSlash_gen_fiber_sum (N := N) k χ D₁ D₂ D hD f hf

private lemma twistedHeckeSlashExt_gen_zsmul (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (n : ℤ)
    (T : 𝕋 (Gamma0_pair N) ℤ) (f : ℍ → ℂ) :
    twistedHeckeSlashExt_gen (N := N) k χ (n • T) f =
      n • twistedHeckeSlashExt_gen (N := N) k χ T f := by
  unfold twistedHeckeSlashExt_gen
  have hsmi := Finsupp.sum_smul_index (g := T) (b := n)
    (h := fun D c ↦ c • twistedHeckeSlash_gen (N := N) k χ D f) (by simp)
  rw [show ((n • T : 𝕋 (Gamma0_pair N) ℤ).sum
      fun D c ↦ c • twistedHeckeSlash_gen (N := N) k χ D f) =
    T.sum (fun D a ↦ (n * a) • twistedHeckeSlash_gen (N := N) k χ D f) from hsmi]
  rw [Finsupp.smul_sum]
  exact Finsupp.sum_congr fun D _ ↦ SemigroupAction.mul_smul _ _ _

/-- The endomorphism of the abstract `Γ₀(N),χ` function submodule attached to one
existing `Γ₀(N)` Hecke double coset. -/
noncomputable def twistedHeckeOperatorFunction (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) :
    Module.End ℂ (gamma0TwistedInvariantFunctionSubmodule (N := N) k χ) where
  toFun f := ⟨twistedHeckeSlash_gen (N := N) k χ D f,
    twistedHeckeSlash_gen_preserves_invariant (N := N) k χ D f f.property⟩
  map_add' f g := by
    ext z
    exact congrFun (twistedHeckeSlash_gen_add (N := N) k χ D f g) z
  map_smul' c f := by
    ext z
    exact congrFun (twistedHeckeSlash_gen_smul (N := N) k χ D c f) z

/-- The `ℤ`-linear extension of the twisted coset operators over the existing
Hecke ring source `𝕋 (Gamma0_pair N) ℤ`. -/
noncomputable def twistedHeckeSumFunction (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ) :
    Module.End ℂ (gamma0TwistedInvariantFunctionSubmodule (N := N) k χ) :=
  T.sum (fun D c ↦ (c : ℂ) • twistedHeckeOperatorFunction (N := N) k χ D)

@[simp] lemma twistedHeckeSumFunction_zero (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    twistedHeckeSumFunction (N := N) k χ (0 : 𝕋 (Gamma0_pair N) ℤ) = 0 := by
  unfold twistedHeckeSumFunction; exact Finsupp.sum_zero_index

@[simp] lemma twistedHeckeSumFunction_T_single (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D : HeckeCoset (Gamma0_pair N)) (c : ℤ) :
    twistedHeckeSumFunction (N := N) k χ (T_single (Gamma0_pair N) ℤ D c) =
      (c : ℂ) • twistedHeckeOperatorFunction (N := N) k χ D := by
  simp [twistedHeckeSumFunction, T_single]

lemma twistedHeckeSumFunction_add (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    twistedHeckeSumFunction (N := N) k χ (T₁ + T₂) =
      twistedHeckeSumFunction (N := N) k χ T₁ +
        twistedHeckeSumFunction (N := N) k χ T₂ := by
  unfold twistedHeckeSumFunction
  refine Finsupp.sum_add_index' (f := T₁) (g := T₂)
    (h := fun D c ↦ (c : ℂ) • twistedHeckeOperatorFunction (N := N) k χ D) ?_ ?_
  · intro D; simp
  · intro D c₁ c₂; ext f z
    simp [add_smul]

/-- Applying the endomorphism-valued extension agrees with the function-valued
weighted extension. -/
lemma twistedHeckeSumFunction_apply_coe
    (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (T : 𝕋 (Gamma0_pair N) ℤ)
    (f : gamma0TwistedInvariantFunctionSubmodule (N := N) k χ) :
    (twistedHeckeSumFunction (N := N) k χ T f : ℍ → ℂ) =
      twistedHeckeSlashExt_gen (N := N) k χ T f := by
  induction T using HeckeRing.induction_linear_𝕋 with
  | h_zero =>
      show (((0 : Module.End ℂ _) f : _) : ℍ → ℂ) = twistedHeckeSlashExt_gen (N := N) k χ 0 f
      simp [twistedHeckeSlashExt_gen]; rfl
  | h_add T₁ T₂ h₁ h₂ =>
      rw [twistedHeckeSumFunction_add, twistedHeckeSlashExt_gen_add]
      ext z
      simp [h₁, h₂]
  | h_single D c =>
      rw [twistedHeckeSumFunction_T_single]
      ext z
      unfold twistedHeckeSlashExt_gen
      rw [Finsupp.sum_single_index (by simp :
        (0 : ℤ) • twistedHeckeSlash_gen (N := N) k χ D (f : ℍ → ℂ) = 0)]
      change ((c : ℂ) • (twistedHeckeSlash_gen (N := N) k χ D (f : ℍ → ℂ))) z =
        (c : ℤ) • (twistedHeckeSlash_gen (N := N) k χ D (f : ℍ → ℂ)) z
      simp [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul]

private lemma twistedHeckeSumFunction_mul_T_single (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)
    (D₁ D₂ : HeckeCoset (Gamma0_pair N)) (a b : ℤ) :
    twistedHeckeSumFunction (N := N) k χ
        (T_single (Gamma0_pair N) ℤ D₁ a * T_single (Gamma0_pair N) ℤ D₂ b) =
      twistedHeckeSumFunction (N := N) k χ (T_single (Gamma0_pair N) ℤ D₁ a) *
        twistedHeckeSumFunction (N := N) k χ (T_single (Gamma0_pair N) ℤ D₂ b) := by
  rw [Gamma0_pair_HeckeAlgebra_mul_comm N
    (T_single (Gamma0_pair N) ℤ D₁ a) (T_single (Gamma0_pair N) ℤ D₂ b)]
  ext f z
  rw [twistedHeckeSumFunction_apply_coe]
  have h_prod : T_single (Gamma0_pair N) ℤ D₂ b *
      T_single (Gamma0_pair N) ℤ D₁ a =
      (b * a) • (T_single (Gamma0_pair N) ℤ D₂ 1 *
        T_single (Gamma0_pair N) ℤ D₁ 1) := by
    rw [HeckeRing.T_single_mul_T_single, HeckeRing.T_single_mul_T_single,
      one_smul, one_smul, ← SemigroupAction.mul_smul]; rfl
  rw [h_prod, twistedHeckeSlashExt_gen_zsmul]
  rw [← twistedHeckeSlash_gen_comp (N := N) k χ D₁ D₂ (f : ℍ → ℂ)
    f.property (Gamma0_pair_HeckeAlgebra_mul_comm N
      (T_single (Gamma0_pair N) ℤ D₂ 1) (T_single (Gamma0_pair N) ℤ D₁ 1))]
  simp only [Module.End.mul_apply]
  rw [twistedHeckeSumFunction_T_single, twistedHeckeSumFunction_T_single]
  simp only [LinearMap.smul_apply]
  rw [(twistedHeckeOperatorFunction (N := N) k χ D₁).map_smul]
  change ((b * a : ℤ) •
      twistedHeckeSlash_gen (N := N) k χ D₁
        (twistedHeckeSlash_gen (N := N) k χ D₂ (f : ℍ → ℂ))) z =
    ((a : ℂ) • ((b : ℂ) •
      twistedHeckeSlash_gen (N := N) k χ D₁
        (twistedHeckeSlash_gen (N := N) k χ D₂ (f : ℍ → ℂ)))) z
  simp [Pi.smul_apply, smul_eq_mul, zsmul_eq_mul, Int.cast_mul, mul_assoc, mul_comm]

/-- Multiplicativity of the endomorphism-valued twisted action for all elements
of the existing Hecke ring `𝕋 (Gamma0_pair N) ℤ`. -/
lemma twistedHeckeSumFunction_mul (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (T₁ T₂ : 𝕋 (Gamma0_pair N) ℤ) :
    twistedHeckeSumFunction (N := N) k χ (T₁ * T₂) =
      twistedHeckeSumFunction (N := N) k χ T₁ *
        twistedHeckeSumFunction (N := N) k χ T₂ := by
  induction T₁ using HeckeRing.induction_linear_𝕋 with
  | h_zero => rw [zero_mul, twistedHeckeSumFunction_zero, zero_mul]
  | h_single D₁ a =>
      induction T₂ using HeckeRing.induction_linear_𝕋 with
      | h_zero => rw [mul_zero, twistedHeckeSumFunction_zero, mul_zero]
      | h_single D₂ b =>
          exact twistedHeckeSumFunction_mul_T_single (N := N) k χ D₁ D₂ a b
      | h_add T₂ T₂' h h' =>
          rw [mul_add, twistedHeckeSumFunction_add, twistedHeckeSumFunction_add,
            h, h', mul_add]
  | h_add T₁ T₁' h h' =>
      rw [add_mul, twistedHeckeSumFunction_add, twistedHeckeSumFunction_add,
        h, h', add_mul]

private lemma twistedHeckeSlash_gen_identity_coset (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) (f : ℍ → ℂ)
    (hf : IsGamma0TwistedInvariant (N := N) k χ f) :
    twistedHeckeSlash_gen (N := N) k χ (HeckeCoset.one (Gamma0_pair N)) f = f := by
  haveI : Subsingleton (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) :=
    subsingleton_decompQuot_T_one (Gamma0_pair N)
  haveI : Nonempty (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) :=
    one_in_decompQuot_T_one (Gamma0_pair N)
  haveI : Unique (decompQuot (Gamma0_pair N)
      (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)))) := uniqueOfSubsingleton default
  unfold twistedHeckeSlash_gen
  rw [show (Finset.univ : Finset (decompQuot (Gamma0_pair N)
        (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N))))) = {default} from by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, fun i _ ↦ Subsingleton.elim _ _⟩,
    Finset.sum_singleton]
  set q : decompQuot (Gamma0_pair N)
    (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N))) := default
  have h_adj_mem :
      tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q ∈
        (Gamma0_pair N).H := by
    change GL_adjugate
      ((q.out : GL (Fin 2) ℚ) *
        (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)) : GL (Fin 2) ℚ)) ∈
        (Gamma0_pair N).H
    exact HeckePairAction.adjugate_mem_H _ <|
      (Gamma0_pair N).H.mul_mem (SetLike.coe_mem _) (HeckeCoset.one_rep_mem_H _)
  have hchar :
      delta0NebentypusHChar (N := N) χ
        (GL_adjugate (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q))
        (HeckePairAction.adjugate_mem_H
          (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q) h_adj_mem) =
      delta0NebentypusWeight (N := N) χ (HeckeCoset.one (Gamma0_pair N)) q := by
    unfold delta0NebentypusHChar delta0NebentypusWeight deltaRep_gen
    apply congrArg (delta0NebentypusDeltaChar (N := N) χ)
    apply Subtype.ext
    change GL_adjugate
        (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q) =
      (q.out : GL (Fin 2) ℚ) *
        (HeckeCoset.rep (HeckeCoset.one (Gamma0_pair N)) : GL (Fin 2) ℚ)
    simp [tRep_gen, GL_adjugate_involutive]
  change
    ((↑(delta0NebentypusWeight (N := N) χ (HeckeCoset.one (Gamma0_pair N)) q) :
        ℂ)⁻¹) •
      (f ∣[k] glMap
        (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q)) = f
  rw [hf (tRep_gen (Gamma0_pair N) (HeckeCoset.one (Gamma0_pair N)) q) h_adj_mem, hchar]
  ext z
  simp [Pi.smul_apply, smul_eq_mul]

@[simp] lemma twistedHeckeOperatorFunction_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    twistedHeckeOperatorFunction (N := N) k χ (HeckeCoset.one (Gamma0_pair N)) = 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change twistedHeckeSlash_gen (N := N) k χ (HeckeCoset.one (Gamma0_pair N))
      (f : ℍ → ℂ) = (f : ℍ → ℂ)
  exact twistedHeckeSlash_gen_identity_coset (N := N) k χ (f : ℍ → ℂ) f.property

@[simp] lemma twistedHeckeSumFunction_one (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    twistedHeckeSumFunction (N := N) k χ (1 : 𝕋 (Gamma0_pair N) ℤ) = 1 := by
  rw [show (1 : 𝕋 (Gamma0_pair N) ℤ) =
      T_single (Gamma0_pair N) ℤ (HeckeCoset.one (Gamma0_pair N)) 1 from
      HeckeRing.one_def _ _,
    twistedHeckeSumFunction_T_single, twistedHeckeOperatorFunction_one]
  simp

/-- The existing `Γ₀(N)` Hecke ring acts on the abstract twisted
`Γ₀(N),χ` function space by a genuine ring homomorphism. -/
noncomputable def twistedHeckeRingHomFunction (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ) :
    𝕋 (Gamma0_pair N) ℤ →+*
      Module.End ℂ (gamma0TwistedInvariantFunctionSubmodule (N := N) k χ) where
  toFun := twistedHeckeSumFunction (N := N) k χ
  map_zero' := twistedHeckeSumFunction_zero (N := N) k χ
  map_one' := twistedHeckeSumFunction_one (N := N) k χ
  map_add' := twistedHeckeSumFunction_add (N := N) k χ
  map_mul' := twistedHeckeSumFunction_mul (N := N) k χ

end HeckeRing.GL2.Unified
