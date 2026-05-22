/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import Mathlib.Analysis.Complex.Periodic
import Mathlib.NumberTheory.ModularForms.QExpansion
import LeanModularForms.HeckeRIngs.GL2.HeckeAction
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GLn.CongruenceHecke
import LeanModularForms.Modularforms.Matrix.SL2SmithDecomp
import LeanModularForms.Modularforms.QExpansionSlash

/-!
# Hecke Lemma — low-dependency API scaffold (POST-6a, T045)

Low-dependency scaffold for Miyake Lemma 4.6.3 ("Hecke's Lemma"): the
integer-lift / integer-determinant / primitivity API on `Delta0_submonoid`,
plus a rational pushforward of the 2×2 matrix Smith decomposition
`Matrix.smith_decomp_of_primitive_posDet` (T040).

The full statement of Miyake 4.6.3 is **not** landed here — it requires the
modular-form slash action / Nebentypus / `Newforms.lean` chain.  See T033
for the full scaffold packet.

This file deliberately avoids `Newforms`/`AdjointTheory`/`LevelRaise`/
`PeterssonLevelN` to keep the import closure small.

## Main definitions

* `HeckeRing.GLn.Delta0_submonoid.intLift` — the unique integer lift of
  `α ∈ Δ₀(N)` as a 2×2 integer matrix.
* `HeckeRing.GLn.Delta0_submonoid.intDet` — the integer determinant of
  `α ∈ Δ₀(N)`.
* `HeckeRing.GLn.IsPrimitiveDelta0` — primitivity of `α ∈ Δ₀(N)` (nested
  `Nat.gcd` of the four entries of `intLift` equals 1).

## Main results

* `Delta0_submonoid.intLift_unique` — uniqueness of the integer lift.
* `Delta0_submonoid.coe_intLift` — `↑α = (intLift α).map (Int.cast : ℤ → ℚ)`.
* `Delta0_submonoid.coe_intDet` — the rational determinant of `α` equals
  `(intDet α : ℚ)`.
* `Delta0_submonoid.intDet_pos` — `0 < intDet α`.
* `Delta0_submonoid.intLift_c_dvd` — `N ∣ (intLift α) 1 0`.
* `Delta0_submonoid.intLift_a_coprime` — `gcd((intLift α) 0 0, N) = 1`.
* `IsPrimitiveDelta0.smith_decomp_rat` — pushforward of the T040 Smith
  decomposition for a primitive `α ∈ Δ₀(N)` with positive determinant,
  living as a ℚ-matrix equality via `Matrix.map` along `Int.cast`.

Reference: Miyake, *Modular Forms*, Lemma 4.6.3.
-/

open Matrix HeckeRing.GL2 CongruenceSubgroup ModularFormClass
open Matrix.SpecialLinearGroup (mapGL)

open scoped ModularForm UpperHalfPlane HeckeRing.GL2 MatrixGroups

namespace HeckeRing.GLn

/-- **Uniqueness of the integer lift.**
If two integer matrices both cast to the same rational matrix, they are
equal.  Follows from `Matrix.map_injective` and `Int.cast_injective`
(which requires `CharZero ℚ`). -/
lemma Delta0_submonoid.intLift_unique
    {A B : Matrix (Fin 2) (Fin 2) ℤ}
    (h : A.map (Int.cast : ℤ → ℚ) = B.map (Int.cast : ℤ → ℚ)) :
    A = B :=
  Matrix.map_injective (Int.cast_injective : Function.Injective ((↑) : ℤ → ℚ)) h

/-- The **integer lift** of `α ∈ Δ₀(N)`.  Picks the witness integer matrix
from the existential in `α.property`; unique by
`Delta0_submonoid.intLift_unique`. -/
noncomputable def Delta0_submonoid.intLift {N : ℕ} (α : Delta0_submonoid N) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  α.property.2.2.choose

/-- The rational matrix of `α ∈ Δ₀(N)` agrees with its integer lift under
`Int.cast : ℤ → ℚ`. -/
lemma Delta0_submonoid.coe_intLift {N : ℕ} (α : Delta0_submonoid N) :
    ((α : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      (Delta0_submonoid.intLift α).map (Int.cast : ℤ → ℚ) :=
  α.property.2.2.choose_spec.1

/-- The integer lift of `α ∈ Δ₀(N)` satisfies `N ∣ (intLift α) 1 0`. -/
lemma Delta0_submonoid.intLift_c_dvd {N : ℕ} (α : Delta0_submonoid N) :
    (N : ℤ) ∣ Delta0_submonoid.intLift α 1 0 :=
  α.property.2.2.choose_spec.2.1

/-- The integer lift of `α ∈ Δ₀(N)` satisfies `gcd((intLift α) 0 0, N) = 1`. -/
lemma Delta0_submonoid.intLift_a_coprime {N : ℕ} (α : Delta0_submonoid N) :
    Int.gcd (Delta0_submonoid.intLift α 0 0) N = 1 :=
  α.property.2.2.choose_spec.2.2

/-- **Integer determinant** of `α ∈ Δ₀(N)`: the determinant of its integer lift. -/
noncomputable def Delta0_submonoid.intDet {N : ℕ} (α : Delta0_submonoid N) : ℤ :=
  (Delta0_submonoid.intLift α).det

/-- The rational determinant of `α ∈ Δ₀(N)` equals the integer determinant
cast along `Int.cast : ℤ → ℚ`. -/
lemma Delta0_submonoid.coe_intDet {N : ℕ} (α : Delta0_submonoid N) :
    ((α : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det =
      (Delta0_submonoid.intDet α : ℚ) := by
  simp [Delta0_submonoid.coe_intLift α, det_intMat_cast, Delta0_submonoid.intDet]

/-- The integer determinant of `α ∈ Δ₀(N)` is strictly positive. -/
lemma Delta0_submonoid.intDet_pos {N : ℕ} (α : Delta0_submonoid N) :
    0 < Delta0_submonoid.intDet α := by
  have h := α.property.2.1
  rw [Delta0_submonoid.coe_intDet α] at h
  exact_mod_cast h

/-- A member `α ∈ Δ₀(N)` is **primitive** if the four integer entries of
its integer lift have gcd 1.  Equivalently, `α` does not factor as `d · β`
for any integer `d ≥ 2` and integer matrix `β` (Miyake §4.6.3). -/
def IsPrimitiveDelta0 {N : ℕ} (α : Delta0_submonoid N) : Prop :=
  Nat.gcd
    (Nat.gcd (Delta0_submonoid.intLift α 0 0).natAbs
             (Delta0_submonoid.intLift α 0 1).natAbs)
    (Nat.gcd (Delta0_submonoid.intLift α 1 0).natAbs
             (Delta0_submonoid.intLift α 1 1).natAbs) = 1

/-- Unfolding lemma: `IsPrimitiveDelta0 α` by definition holds iff the
nested `Nat.gcd` of the four entries of `α.intLift` equals `1`. -/
lemma isPrimitiveDelta0_iff {N : ℕ} (α : Delta0_submonoid N) :
    IsPrimitiveDelta0 α ↔
      Nat.gcd
        (Nat.gcd (Delta0_submonoid.intLift α 0 0).natAbs
                 (Delta0_submonoid.intLift α 0 1).natAbs)
        (Nat.gcd (Delta0_submonoid.intLift α 1 0).natAbs
                 (Delta0_submonoid.intLift α 1 1).natAbs) = 1 :=
  Iff.rfl

/-- **Rational pushforward of the Smith decomposition (T040).**
Given a primitive `α ∈ Δ₀(N)` with integer lift `A := Delta0_submonoid.intLift α`,
there exist `U V ∈ SL(2, ℤ)` such that, cast entrywise to `ℚ`,

`U.map (Int.cast) * (↑α : Matrix ℚ) * V.map (Int.cast) = !![1, 0; 0, (intDet α : ℚ)]`.

Immediate corollary of `Matrix.smith_decomp_of_primitive_posDet` applied
to the integer lift (primitive by `hα_prim`, positive determinant by
`Delta0_submonoid.intDet_pos`), pushed through `Int.cast` using
`Matrix.map_mul`. -/
theorem IsPrimitiveDelta0.smith_decomp_rat {N : ℕ} {α : Delta0_submonoid N}
    (hα_prim : IsPrimitiveDelta0 α) :
    ∃ U V : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ((U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) *
          ((α : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) *
          ((V : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
        !![(1 : ℚ), 0; 0, (Delta0_submonoid.intDet α : ℚ)] := by
  obtain ⟨U, V, hUV⟩ :=
    Matrix.smith_decomp_of_primitive_posDet
      (A := Delta0_submonoid.intLift α) hα_prim
      (Delta0_submonoid.intDet_pos α)
  refine ⟨U, V, ?_⟩
  have h : (Int.castRingHom ℚ).mapMatrix
            ((U : Matrix (Fin 2) (Fin 2) ℤ) * Delta0_submonoid.intLift α *
              (V : Matrix (Fin 2) (Fin 2) ℤ)) =
        (Int.castRingHom ℚ).mapMatrix
            (!![(1 : ℤ), 0; 0, (Delta0_submonoid.intLift α).det]) := by
    rw [hUV]
  rw [map_mul, map_mul] at h
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at h
  rw [← Delta0_submonoid.coe_intLift α] at h
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.map_apply, Delta0_submonoid.intDet]

/-- **Inverted Smith pushforward (GL ℚ matrix form).**
For a primitive `α ∈ Δ₀(N)`, there exist `U V ∈ SL(2, ℤ)` (obtained as
the inverses of the Smith factors from `smith_decomp_rat`) such that

`(↑α : Matrix ℚ) = (U : Matrix ℤ).map cast * !![1, 0; 0, (intDet α : ℚ)] * (V : Matrix ℤ).map cast`.

Equivalently, `α = U · diag(1, m) · V` in `GL(2, ℚ)` at the matrix level,
reflecting the 2×2 Smith normal form over `ℤ`.  This is the form used in
Miyake 4.6.3 for the slash-level reduction. -/
theorem IsPrimitiveDelta0.smith_decomp_Q {N : ℕ} {α : Delta0_submonoid N}
    (hα_prim : IsPrimitiveDelta0 α) :
    ∃ U V : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      ((α : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
        (U : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) *
        !![(1 : ℚ), 0; 0, (Delta0_submonoid.intDet α : ℚ)] *
        (V : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ) := by
  obtain ⟨U₀, V₀, hUV⟩ :=
    Matrix.smith_decomp_of_primitive_posDet (A := Delta0_submonoid.intLift α)
      hα_prim (Delta0_submonoid.intDet_pos α)
  refine ⟨U₀⁻¹, V₀⁻¹, ?_⟩
  have hUU : (U₀⁻¹).val * U₀.val = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]; rfl
  have hVV : V₀.val * (V₀⁻¹).val = (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]; rfl
  have hIntLift_eq : Delta0_submonoid.intLift α =
      (U₀⁻¹).val *
      !![(1 : ℤ), 0; 0, (Delta0_submonoid.intLift α).det] *
      (V₀⁻¹).val := by
    calc Delta0_submonoid.intLift α
        = 1 * Delta0_submonoid.intLift α * 1 := by rw [one_mul, mul_one]
      _ = ((U₀⁻¹).val * U₀.val) * Delta0_submonoid.intLift α *
            (V₀.val * (V₀⁻¹).val) := by rw [hUU, hVV]
      _ = (U₀⁻¹).val *
            (U₀.val * Delta0_submonoid.intLift α * V₀.val) *
            (V₀⁻¹).val := by simp only [mul_assoc]
      _ = (U₀⁻¹).val *
            !![(1 : ℤ), 0; 0, (Delta0_submonoid.intLift α).det] *
            (V₀⁻¹).val := by rw [hUV]
  calc ((α : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ)
      = (Delta0_submonoid.intLift α).map (Int.cast : ℤ → ℚ) :=
          Delta0_submonoid.coe_intLift α
    _ = ((U₀⁻¹).val *
          !![(1 : ℤ), 0; 0, (Delta0_submonoid.intLift α).det] *
          (V₀⁻¹).val).map (Int.cast : ℤ → ℚ) := by
          conv_lhs => rw [hIntLift_eq]
    _ = ((U₀⁻¹).val).map (Int.cast : ℤ → ℚ) *
        (!![(1 : ℤ), 0; 0, (Delta0_submonoid.intLift α).det] : Matrix (Fin 2) (Fin 2) ℤ).map
          (Int.cast : ℤ → ℚ) *
        ((V₀⁻¹).val).map (Int.cast : ℤ → ℚ) := by
          have := (Int.castRingHom ℚ).mapMatrix.map_mul
              ((U₀⁻¹).val * !![(1 : ℤ), 0; 0, (Delta0_submonoid.intLift α).det])
              (V₀⁻¹).val
          simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this
          rw [this]
          have := (Int.castRingHom ℚ).mapMatrix.map_mul (U₀⁻¹).val
              !![(1 : ℤ), 0; 0, (Delta0_submonoid.intLift α).det]
          simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at this
          rw [this]
    _ = ((U₀⁻¹).val).map (Int.cast : ℤ → ℚ) *
        !![(1 : ℚ), 0; 0, (Delta0_submonoid.intDet α : ℚ)] *
        ((V₀⁻¹).val).map (Int.cast : ℤ → ℚ) := by
          congr 1
          congr 1
          ext i j
          fin_cases i <;> fin_cases j <;>
            simp [Matrix.map_apply, Delta0_submonoid.intDet]

/-- The `GL(2, ℚ)` diagonal matrix `diag(1, m)` for positive integer `m`.
Used as the middle Smith factor for a primitive `α ∈ Δ₀(N)`. -/
noncomputable def diagGL_Q (m : ℤ) (hm : 0 < m) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(1 : ℚ), 0; 0, (m : ℚ)]
    (by
      rw [Matrix.det_fin_two_of]
      simp only [one_mul, mul_zero, sub_zero]
      exact_mod_cast hm.ne')

@[simp] lemma diagGL_Q_coe_matrix (m : ℤ) (hm : 0 < m) :
    ((diagGL_Q m hm : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![(1 : ℚ), 0; 0, (m : ℚ)] :=
  rfl

/-- **GL-level Smith decomposition.**
For primitive `α ∈ Δ₀(N)`, there exist `U V ∈ SL(2, ℤ)` such that, as
elements of `GL(2, ℚ)`,
`α = mapGL ℚ U * diagGL_Q (intDet α) _ * mapGL ℚ V`.

Obtained from `smith_decomp_Q` by extensionality in `Units`. -/
theorem IsPrimitiveDelta0.smith_decomp_GL_Q {N : ℕ} {α : Delta0_submonoid N}
    (hα_prim : IsPrimitiveDelta0 α) :
    ∃ U V : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      (α : GL (Fin 2) ℚ) =
        Matrix.SpecialLinearGroup.mapGL ℚ U *
          diagGL_Q (Delta0_submonoid.intDet α) (Delta0_submonoid.intDet_pos α) *
          Matrix.SpecialLinearGroup.mapGL ℚ V := by
  obtain ⟨U, V, hmat⟩ := hα_prim.smith_decomp_Q
  refine ⟨U, V, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, diagGL_Q_coe_matrix,
             Matrix.SpecialLinearGroup.mapGL_coe_matrix,
             Matrix.SpecialLinearGroup.map_apply_coe,
             RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom]
  exact hmat

/-- **Slash-level Smith reduction for a primitive `α ∈ Δ₀(N)`.**
For a function `f : ℍ → ℂ`, the slash by the `GL(2, ℚ)` element `↑α`
decomposes through the Smith factors: there exist `U V ∈ SL(2, ℤ)` such
that
`f ∣[k] (↑α : GL (Fin 2) ℚ) = f ∣[k] mapGL ℚ U ∣[k] diagGL_Q m _ ∣[k] mapGL ℚ V`,
where `m = intDet α`.  Immediate from `smith_decomp_GL_Q` and
`SlashAction.slash_mul`. -/
theorem IsPrimitiveDelta0.slash_decomp {N : ℕ} {α : Delta0_submonoid N}
    (hα_prim : IsPrimitiveDelta0 α) (k : ℤ) (f : UpperHalfPlane → ℂ) :
    ∃ U V : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      f ∣[k] ((α : GL (Fin 2) ℚ)) =
        ((f ∣[k] Matrix.SpecialLinearGroup.mapGL ℚ U) ∣[k]
            diagGL_Q (Delta0_submonoid.intDet α)
              (Delta0_submonoid.intDet_pos α)) ∣[k]
          Matrix.SpecialLinearGroup.mapGL ℚ V := by
  obtain ⟨U, V, hGL⟩ := hα_prim.smith_decomp_GL_Q
  exact ⟨U, V, by rw [hGL, SlashAction.slash_mul, SlashAction.slash_mul]⟩

/-- **Real-valued slash bridge.**
Same decomposition pushed to `GL(2, ℝ)` via `glMap`: the first and third
factors become `mapGL ℝ U` and `mapGL ℝ V` respectively.  This is the
form needed by Miyake 4.6.3, where the `SL(2, ℤ)` factors can be absorbed
into the `Γ₀(N)`-character via Prop 3.34 and the modular-form slash
invariance. -/
theorem IsPrimitiveDelta0.slash_decomp_R {N : ℕ} {α : Delta0_submonoid N}
    (hα_prim : IsPrimitiveDelta0 α) (k : ℤ) (f : UpperHalfPlane → ℂ) :
    ∃ U V : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      f ∣[k] ((α : GL (Fin 2) ℚ)) =
        ((f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ U : GL (Fin 2) ℝ)) ∣[k]
            glMap (diagGL_Q (Delta0_submonoid.intDet α)
              (Delta0_submonoid.intDet_pos α))) ∣[k]
          (Matrix.SpecialLinearGroup.mapGL ℝ V : GL (Fin 2) ℝ) := by
  obtain ⟨U, V, hfn⟩ := hα_prim.slash_decomp k f
  refine ⟨U, V, ?_⟩
  rw [hfn]
  show ((f ∣[k] glMap (Matrix.SpecialLinearGroup.mapGL ℚ U)) ∣[k]
         glMap (diagGL_Q (Delta0_submonoid.intDet α)
           (Delta0_submonoid.intDet_pos α))) ∣[k]
         glMap (Matrix.SpecialLinearGroup.mapGL ℚ V) = _
  rw [glMap_mapGL_eq, glMap_mapGL_eq]

/-- **Pointwise slash formula** for the rational diagonal `diag(1, m)` with
`0 < m`.  Unfolded via the Mathlib `slash_apply` formula `f ∣[k] γ = σ γ (f
(γ • τ)) * |det γ|^(k-1) * denom γ τ^(-k)`.  For `γ = diag(1, m)` with
positive determinant `m`, `σ = id`, `|det γ| = m`, `denom γ τ = m`, so

`(f ∣[k] glMap (diagGL_Q m hm)) τ = m⁻¹ · f (glMap (diagGL_Q m hm) • τ)`.

Template: `HeckeRIngs.GL2.QExpansionSlash.slash_T_p_upper_eval`. -/
lemma slash_diagGL_Q_apply (k : ℤ) (m : ℤ) (hm : 0 < m)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    (f ∣[k] (diagGL_Q m hm : GL (Fin 2) ℚ)) τ =
      (m : ℂ)⁻¹ * f (glMap (diagGL_Q m hm) • τ) := by
  show ((f ∣[k] glMap (diagGL_Q m hm)) τ) = _
  rw [ModularForm.slash_apply]
  have hdet_val : (glMap (diagGL_Q m hm)).det.val = (m : ℝ) := by
    rw [show (glMap (diagGL_Q m hm)).det.val =
      algebraMap ℚ ℝ (diagGL_Q m hm).det.val from
      congr_arg Units.val (Matrix.GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      Matrix.GeneralLinearGroup.val_det_apply]
    simp [diagGL_Q, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]
  have hdet_pos : 0 < (glMap (diagGL_Q m hm)).det.val := by
    rw [hdet_val]; exact_mod_cast hm
  have hσ : UpperHalfPlane.σ (glMap (diagGL_Q m hm)) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; simp only [hdet_pos, ↓reduceIte]
  have hdenom : UpperHalfPlane.denom (glMap (diagGL_Q m hm)) ↑τ = (m : ℂ) := by
    simp [UpperHalfPlane.denom, glMap, diagGL_Q,
          Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.cons_val_one]
  rw [hσ, RingHom.id_apply, hdet_val,
    abs_of_pos (show (0 : ℝ) < (m : ℝ) by exact_mod_cast hm), hdenom]
  have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have halg (x : ℂ) : x * (m : ℂ) ^ (k - 1) * (m : ℂ) ^ (-k) = (m : ℂ)⁻¹ * x := by
    rw [mul_assoc, ← zpow_add₀ hm_ne]
    simp [show (k - 1 + -k : ℤ) = -1 by lia]
    ring
  exact halg _

/-- Möbius action of `glMap (diagGL_Q m hm)` on `τ ∈ ℍ`: `diag(1, m) • τ` has
complex coordinate `τ / m`.  Useful companion to `slash_diagGL_Q_apply`. -/
lemma coe_diagGL_Q_smul (m : ℤ) (hm : 0 < m) (τ : UpperHalfPlane) :
    (↑(glMap (diagGL_Q m hm) • τ) : ℂ) = (τ : ℂ) / (m : ℂ) := by
  have hdet_val : (glMap (diagGL_Q m hm)).det.val = (m : ℝ) := by
    rw [show (glMap (diagGL_Q m hm)).det.val =
      algebraMap ℚ ℝ (diagGL_Q m hm).det.val from
      congr_arg Units.val (Matrix.GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      Matrix.GeneralLinearGroup.val_det_apply]
    simp [diagGL_Q, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two_of]
  have hdet_pos : 0 < (glMap (diagGL_Q m hm)).det.val := by
    rw [hdet_val]; exact_mod_cast hm
  simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
    UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
  set M := (↑(glMap (diagGL_Q m hm)) : Matrix (Fin 2) (Fin 2) ℝ)
  have h00 : M 0 0 = 1 := by
    simp [M, glMap, diagGL_Q, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h01 : M 0 1 = 0 := by
    simp [M, glMap, diagGL_Q, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h10 : M 1 0 = 0 := by
    simp [M, glMap, diagGL_Q, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : M 1 1 = (m : ℝ) := by
    simp [M, glMap, diagGL_Q, Matrix.GeneralLinearGroup.mkOfDetNeZero,
          Matrix.cons_val_one]
  simp only [h00, h01, h10, h11]
  push_cast
  ring

/-- **Sparse-index `HasSum` reindexing through a multiplication.**
For `0 < m`, if `HasSum (fun j => a j • (q ^ m) ^ j) S`, then the reindexed
sum through `j ↦ m · j` — with zeros filled in at non-multiples of `m` —
still sums to `S`:

`HasSum (fun n => if m ∣ n then a (n / m) • q ^ n else 0) S`.

Immediate from `Function.Injective.hasSum_iff` applied to `j ↦ m · j`
(injective for `m > 0`), using that the sparse function vanishes outside
its range. -/
lemma hasSum_pow_mul_reindex {m : ℕ} (hm : 0 < m) {a : ℕ → ℂ} {q : ℂ}
    {S : ℂ} (h : HasSum (fun j : ℕ => a j • (q ^ m) ^ j) S) :
    HasSum (fun n : ℕ => if m ∣ n then a (n / m) • q ^ n else 0) S := by
  have hm_ne : m ≠ 0 := hm.ne'
  have hinj : Function.Injective (fun j : ℕ => m * j) := by
    intro x y hxy
    exact Nat.mul_left_cancel hm hxy
  have h_zero : ∀ n : ℕ, n ∉ Set.range (fun j : ℕ => m * j) →
      (fun n : ℕ => if m ∣ n then a (n / m) • q ^ n else 0) n = 0 := by
    intro n hn
    simp only
    rw [if_neg]
    intro hdvd
    obtain ⟨j, rfl⟩ := hdvd
    exact hn ⟨j, rfl⟩
  have h_eq : ((fun n : ℕ => if m ∣ n then a (n / m) • q ^ n else 0) ∘
      (fun j : ℕ => m * j)) = fun j : ℕ => a j • (q ^ m) ^ j := by
    funext j
    simp only [Function.comp_apply]
    rw [if_pos ⟨j, rfl⟩]
    congr 1
    · exact congrArg a (Nat.mul_div_cancel_left j hm)
    · rw [← pow_mul]
  rw [← Function.Injective.hasSum_iff hinj h_zero, h_eq]
  exact h

/-- **qParam rescaling under argument scaling.**
For positive real `h`, positive `m : ℤ`, and complex `z`,
`Function.Periodic.qParam h (z / m) = Function.Periodic.qParam (h * m) z`.

This is the core identity behind the change-of-period reindexing:
`qParam N (τ/m) = qParam (N·m) τ`. -/
lemma qParam_div_eq_qParam_mul (h : ℝ) (m : ℤ) (hm : 0 < m) (z : ℂ) :
    Function.Periodic.qParam h (z / (m : ℂ)) =
      Function.Periodic.qParam (h * m) z := by
  have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Function.Periodic.qParam]
  congr 1
  push_cast
  field_simp

/-- **qParam scaling identity**, dual to `qParam_div_eq_qParam_mul`.
For positive real `h` and positive integer `m`,
`Function.Periodic.qParam h z = (Function.Periodic.qParam (h * m) z) ^ m`.

This is the reciprocal direction: at the finer period `h · m`, the level-`h`
q-parameter is the `m`-th power. -/
lemma qParam_eq_qParam_mul_pow (h : ℝ) (m : ℕ) (hm : 0 < m) (z : ℂ) :
    Function.Periodic.qParam h z =
      (Function.Periodic.qParam (h * m) z) ^ m := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  have hm_ne : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- **q-expansion support theorem for the diagonal slash.**
Let `f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k`, and assume that
slashing `f` by the rational diagonal `diag(1, m)` produces `g` as
functions `ℍ → ℂ`.  Then the Fourier coefficients of `f` at level `N` are
**supported on multiples of `m`**: for every `n : ℕ` not divisible by
`m`, `(qExpansion N f).coeff n = 0`.

Proof combines:
* `slash_diagGL_Q_apply` (slash collapses to `m⁻¹ · f(τ/m)`),
* `coe_diagGL_Q_smul` (`(γ • τ : ℂ) = τ / m`),
* `hasSum_qExpansion` at levels `N` and `N·m`,
* `qParam_div_eq_qParam_mul` + `qParam_eq_qParam_mul_pow` to relate
  `qParam N` and `qParam (N·m)` arguments,
* `hasSum_pow_mul_reindex` (sparse-index reindexing of `g`'s `N`-level
  expansion to the `N·m`-level expansion with zeros at non-multiples of
  `m`),
* `qExpansion_coeff_unique` at level `N·m` to equate the two
  representations of `g τ` and read off the coefficient.

This is the q-expansion half of Miyake Lemma 4.6.3. -/
theorem qExpansion_support_of_diagGL_Q_slash {N : ℕ} [NeZero N] {k : ℤ}
    {m : ℕ} (hm : 0 < m)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (m : ℤ) (by exact_mod_cast hm) : GL (Fin 2) ℚ)) :
    ∀ n : ℕ, ¬ m ∣ n → (qExpansion (N : ℝ) f).coeff n = 0 := by
  have hm_int : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hm_ne_C : ((m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hm_ne_C_int : ((m : ℤ) : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hN_pos_R : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have hm_pos_R : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hNm_pos_R : (0 : ℝ) < (N : ℝ) * (m : ℝ) := mul_pos hN_pos_R hm_pos_R
  have hNm_period :
      ((N : ℝ) * (m : ℝ)) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods := by
    have hsmul_eq : (m : ℕ) • (N : ℝ) = (N : ℝ) * (m : ℝ) := by
      rw [nsmul_eq_mul]; ring
    rw [← hsmul_eq]
    exact AddSubgroup.nsmul_mem _ hN_period m
  set γ : GL (Fin 2) ℚ := diagGL_Q (m : ℤ) hm_int with hγ_def
  have h_dense : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ =>
        ((m : ℂ)⁻¹ * (qExpansion (N : ℝ) f).coeff n) •
          Function.Periodic.qParam ((N : ℝ) * (m : ℝ)) (τ : ℂ) ^ n) (g τ) := by
    intro τ
    have hfsum :=
      hasSum_qExpansion f hN_pos_R hN_period (glMap γ • τ : UpperHalfPlane)
    have hqeq :
        Function.Periodic.qParam (N : ℝ) ((glMap γ • τ : UpperHalfPlane) : ℂ) =
          Function.Periodic.qParam ((N : ℝ) * (m : ℝ)) (τ : ℂ) := by
      rw [coe_diagGL_Q_smul (m : ℤ) hm_int τ]
      exact qParam_div_eq_qParam_mul (N : ℝ) (m : ℤ) hm_int (τ : ℂ)
    rw [hqeq] at hfsum
    have hslash_eq : g τ = (m : ℂ)⁻¹ * f (glMap γ • τ) := by
      rw [h_eq]
      exact slash_diagGL_Q_apply k (m : ℤ) hm_int (⇑f) τ
    rw [hslash_eq]
    have := hfsum.mul_left ((m : ℂ)⁻¹)
    convert this using 1
    funext n
    simp only [smul_eq_mul]
    ring
  have h_sparse : ∀ τ : UpperHalfPlane,
      HasSum (fun n : ℕ =>
        (if m ∣ n then (qExpansion (N : ℝ) g).coeff (n / m) else 0) •
          Function.Periodic.qParam ((N : ℝ) * (m : ℝ)) (τ : ℂ) ^ n) (g τ) := by
    intro τ
    have hgsum := hasSum_qExpansion g hN_pos_R hN_period τ
    have hq_pow : Function.Periodic.qParam (N : ℝ) (τ : ℂ) =
        (Function.Periodic.qParam ((N : ℝ) * (m : ℝ)) (τ : ℂ)) ^ m :=
      qParam_eq_qParam_mul_pow (N : ℝ) m hm (τ : ℂ)
    rw [hq_pow] at hgsum
    have hreidx := hasSum_pow_mul_reindex hm hgsum
    convert hreidx using 1
    funext n
    split_ifs with hdvd
    · rfl
    · simp
  intro n hmn_ne
  have h_dense_eq :
      ((m : ℂ)⁻¹ * (qExpansion (N : ℝ) f).coeff n) =
        (qExpansion ((N : ℝ) * (m : ℝ)) g).coeff n :=
    qExpansion_coeff_unique hNm_pos_R hNm_period h_dense n
  have h_sparse_eq :
      (if m ∣ n then (qExpansion (N : ℝ) g).coeff (n / m) else 0 : ℂ) =
        (qExpansion ((N : ℝ) * (m : ℝ)) g).coeff n :=
    qExpansion_coeff_unique hNm_pos_R hNm_period h_sparse n
  have h_comb :
      (m : ℂ)⁻¹ * (qExpansion (N : ℝ) f).coeff n =
        (if m ∣ n then (qExpansion (N : ℝ) g).coeff (n / m) else 0 : ℂ) := by
    rw [h_dense_eq, ← h_sparse_eq]
  rw [if_neg hmn_ne] at h_comb
  rcases mul_eq_zero.mp h_comb with h | h
  · exact absurd h (inv_ne_zero hm_ne_C)
  · exact h

/-- Positive determinant of the rational diagonal `diagGL_Q m`. -/
lemma diagGL_Q_det_pos (m : ℤ) (hm : 0 < m) :
    0 < ((diagGL_Q m hm : GL (Fin 2) ℚ).det.val) := by
  simp only [diagGL_Q, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  simpa using (show (0 : ℚ) < (m : ℚ) by exact_mod_cast hm)

/-- **Nebentypus slash bridge via `mapGL ℚ`.**
For `f ∈ modFormCharSpace k χ` and `γ ∈ Γ₀(N)`, slashing the underlying
function by the `GL(2, ℚ)` image of `γ` multiplies by `χ(Gamma0MapUnits γ)`:

`⇑f ∣[k] (mapGL ℚ γ : GL (Fin 2) ℚ) = χ(Gamma0MapUnits γ) • ⇑f`.

Obtained from `glMap_mapGL_eq` composed with `modFormCharSpace_iff_nebentypus`. -/
lemma slash_mapGL_Q_Gamma0_charSpace {N : ℕ} [NeZero N] {k : ℤ}
    {χ : (ZMod N)ˣ →* ℂˣ}
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (γ : ↥(Gamma0 N)) :
    (⇑f : UpperHalfPlane → ℂ) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) =
      (↑(χ (Gamma0MapUnits γ)) : ℂ) • ⇑f := by
  show (⇑f) ∣[k] glMap (Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ))) = _
  rw [glMap_mapGL_eq]
  exact ((modFormCharSpace_iff_nebentypus k χ f).mp hf) γ

/-- **Γ₀-normalized character transport + q-expansion support.**
Assume a primitive `α ∈ Δ₀(N)` factors as `α = mapGL ℚ γ · diagGL_Q m _`
with `γ ∈ Γ₀(N)`, and a level-`N` modular form `g ∈ modFormCharSpace k χ`
whose underlying function equals `⇑f ∣[k] (↑α : GL ℚ)` exists.  Then `f`'s
Fourier coefficients at level `N` are supported on multiples of `m`: for
every `n : ℕ` with `¬ m ∣ n`, `(qExpansion N f).coeff n = 0`.

Combines:
* `slash_mapGL_Q_Gamma0_charSpace` (Γ₀ character identity),
* `smul_slash_pos_det` (scalar-slash commutation for positive det),
* `qExpansion_support_of_diagGL_Q_slash` (T049).

**Hypothesis discussion**.  Generic primitive `α ∈ Δ₀(N)` with
`gcd(det α, N) = 1` does **not** factor as `γ · D` with a single `γ ∈
Γ₀(N)` on the left: the Smith factor lies in `SL(2, ℤ)` but may be
outside `Γ₀(N)`.  However, Shimura 3.29 gives a double-coset
decomposition `Γ₀(N) · α · Γ₀(N) = ⊔ᵢ Γ₀(N) · αᵢ`; for specific coset
representatives `αᵢ` the `γ · D` factorization is available, and this
theorem is the transport-to-support bridge used once that decomposition
lands. -/
theorem IsPrimitiveDelta0.qExpansion_support_of_Gamma0_factored
    {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {m : ℕ} (hm : 0 < m)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ modFormCharSpace k χ)
    {α : Delta0_submonoid N}
    (γ : ↥(Gamma0 N))
    (hα_factor : ((α : GL (Fin 2) ℚ)) =
      Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ)) *
      diagGL_Q (m : ℤ) (by exact_mod_cast hm))
    {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] ((α : GL (Fin 2) ℚ))) :
    ∀ n : ℕ, ¬ m ∣ n → (qExpansion (N : ℝ) f).coeff n = 0 := by
  set χγ : ℂˣ := χ (Gamma0MapUnits γ) with hχγ_def
  have hχγ_ne : (↑χγ : ℂ) ≠ 0 := χγ.ne_zero
  have h_diag_pos : 0 < (diagGL_Q (m : ℤ) (by exact_mod_cast hm)).det.val :=
    diagGL_Q_det_pos _ _
  have h_key : (⇑f : UpperHalfPlane → ℂ) ∣[k] (α : GL (Fin 2) ℚ) =
      (↑χγ : ℂ) • (⇑f ∣[k]
        (diagGL_Q (m : ℤ) (by exact_mod_cast hm) : GL (Fin 2) ℚ)) := by
    rw [hα_factor, SlashAction.slash_mul, slash_mapGL_Q_Gamma0_charSpace hf_char γ,
        smul_slash_pos_det k _ _ _ h_diag_pos]
  let g' : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := (↑χγ : ℂ)⁻¹ • g
  have hg'_eq : (⇑g' : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (m : ℤ) (by exact_mod_cast hm) : GL (Fin 2) ℚ) := by
    show (↑χγ : ℂ)⁻¹ • ⇑g = _
    rw [hg_eq, h_key, smul_smul, inv_mul_cancel₀ hχγ_ne, one_smul]
  exact qExpansion_support_of_diagGL_Q_slash hm hN_period f g' hg'_eq

/-- The upper-triangular integer matrix `!![1, b; 0, 1]` as an element of
`Γ₀(N)`.  The (1,0) entry is `0`, so `Γ₀(N)`'s congruence condition
`N ∣ c` is trivially satisfied.

Used as the Γ₀-normalising factor for the standard upper-triangular
Hecke coset representative `!![1, b; 0, p] = diag(1, p) · !![1, b; 0, 1]`. -/
def Gamma0_upperTri (N : ℕ) (b : ℤ) : ↥(Gamma0 N) :=
  ⟨⟨!![1, b; 0, 1], by rw [Matrix.det_fin_two_of]; ring⟩, by
    rw [Gamma0_mem]
    show ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ZMod N) = 0
    simp⟩

@[simp] lemma Gamma0_upperTri_coe (N : ℕ) (b : ℤ) :
    ((Gamma0_upperTri N b : ↥(Gamma0 N)) : SL(2, ℤ)).val =
      !![1, b; 0, 1] := rfl

/-- **Γ₀-normalized `D · γ` character transport + q-expansion support.**
Companion to `qExpansion_support_of_Gamma0_factored` for factorizations
with `γ` on the **right** of the diagonal:

if `α = diagGL_Q m · mapGL ℚ γ` for `γ ∈ Γ₀(N)`, and `f ∣[k] α` equals
the underlying function of a level-`N` modular form `g ∈ modFormCharSpace
k χ`, then `f`'s Fourier coefficients at level `N` are supported on
multiples of `m`.

The proof slashes both sides of `⇑g = (⇑f ∣[k] D) ∣[k] mapGL ℚ γ` on
the right by `(mapGL ℚ γ)⁻¹ = mapGL ℚ γ⁻¹`, applies the Nebentypus
bridge at `γ⁻¹` to extract the scalar `χ(γ⁻¹) = χ(γ)⁻¹`, then delegates
to `qExpansion_support_of_diagGL_Q_slash`.

This form fits the standard upper-triangular Hecke coset representative
`T_p_upper b = diag(1, p) · !![1, b; 0, 1]` (see `T_p_upper_factor_Gamma0`
below). -/
theorem IsPrimitiveDelta0.qExpansion_support_of_Gamma0_factored_right
    {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ} {m : ℕ} (hm : 0 < m)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {α : Delta0_submonoid N}
    (γ : ↥(Gamma0 N))
    (hα_factor : ((α : GL (Fin 2) ℚ)) =
      diagGL_Q (m : ℤ) (by exact_mod_cast hm) *
      Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ)))
    {g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hg_char : g ∈ modFormCharSpace k χ)
    (hg_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] ((α : GL (Fin 2) ℚ))) :
    ∀ n : ℕ, ¬ m ∣ n → (qExpansion (N : ℝ) f).coeff n = 0 := by
  set χγ : ℂˣ := χ (Gamma0MapUnits γ) with hχγ_def
  have hχγ_ne : (↑χγ : ℂ) ≠ 0 := χγ.ne_zero
  have hγinv_coe :
      ((γ⁻¹ : ↥(Gamma0 N)) : SL(2, ℤ)) = ((γ : ↥(Gamma0 N)) : SL(2, ℤ))⁻¹ :=
    InvMemClass.coe_inv γ
  have hγγinv_one :
      (Matrix.SpecialLinearGroup.mapGL ℚ (γ : SL(2, ℤ)) : GL (Fin 2) ℚ) *
      (Matrix.SpecialLinearGroup.mapGL ℚ ((γ⁻¹ : ↥(Gamma0 N)) : SL(2, ℤ)) :
        GL (Fin 2) ℚ) = 1 := by
    rw [hγinv_coe, ← map_mul, mul_inv_cancel, map_one]
  have h_slash_gγinv : (⇑g : UpperHalfPlane → ℂ) ∣[k]
      (Matrix.SpecialLinearGroup.mapGL ℚ ((γ⁻¹ : ↥(Gamma0 N)) : SL(2, ℤ)) :
        GL (Fin 2) ℚ) =
      ⇑f ∣[k] (diagGL_Q (m : ℤ) (by exact_mod_cast hm) : GL (Fin 2) ℚ) := by
    rw [hg_eq, hα_factor, SlashAction.slash_mul, ← SlashAction.slash_mul,
        hγγinv_one, SlashAction.slash_one]
  have h_slash_gγinv_char : (⇑g : UpperHalfPlane → ℂ) ∣[k]
      (Matrix.SpecialLinearGroup.mapGL ℚ ((γ⁻¹ : ↥(Gamma0 N)) : SL(2, ℤ)) :
        GL (Fin 2) ℚ) =
      (↑χγ : ℂ)⁻¹ • ⇑g := by
    rw [slash_mapGL_Q_Gamma0_charSpace hg_char γ⁻¹]
    simp [hχγ_def, map_inv]
  have h_fD_eq : (⇑f : UpperHalfPlane → ℂ) ∣[k]
      (diagGL_Q (m : ℤ) (by exact_mod_cast hm) : GL (Fin 2) ℚ) =
      (↑χγ : ℂ)⁻¹ • ⇑g := h_slash_gγinv.symm.trans h_slash_gγinv_char
  let g' : ModularForm ((Gamma1 N).map (mapGL ℝ)) k := (↑χγ : ℂ)⁻¹ • g
  have hg'_eq : (⇑g' : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (m : ℤ) (by exact_mod_cast hm) : GL (Fin 2) ℚ) := by
    show (↑χγ : ℂ)⁻¹ • ⇑g = _
    rw [h_fD_eq]
  exact qExpansion_support_of_diagGL_Q_slash hm hN_period f g' hg'_eq

/-- **Explicit Γ₀-normalised factorisation of the upper-triangular Hecke
coset representative.**

For `p > 0` and `b : ℕ`, the standard Hecke coset representative
`T_p_upper b = !![1, b; 0, p] : GL(2, ℚ)` factors as

`T_p_upper b = diagGL_Q p _ · mapGL ℚ (Gamma0_upperTri N b)`.

This gives the exact `α = diagGL_Q m · mapGL ℚ γ` shape demanded by
`qExpansion_support_of_Gamma0_factored_right`, enabling the Hecke-lemma
reduction on each of the `p` upper-triangular coset representatives of
`Γ₀(N) · diag(1, p) · Γ₀(N)`. -/
lemma T_p_upper_factor_Gamma0 {N : ℕ} [NeZero N] (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (T_p_upper p hp b : GL (Fin 2) ℚ) =
      diagGL_Q (p : ℤ) (by exact_mod_cast hp) *
      Matrix.SpecialLinearGroup.mapGL ℚ
        ((Gamma0_upperTri N (b : ℤ) : ↥(Gamma0 N)) : SL(2, ℤ)) := by
  apply Units.ext
  rw [Units.val_mul]
  simp only [T_p_upper_coe, diagGL_Q_coe_matrix,
    Matrix.SpecialLinearGroup.mapGL_coe_matrix,
    Matrix.SpecialLinearGroup.map_apply_coe, Gamma0_upperTri_coe,
    RingHom.mapMatrix_apply, algebraMap_int_eq, Int.coe_castRingHom]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]

/-- The `GL(2, ℚ)` diagonal `diag(m, 1)` for a positive integer `m`.
Companion to `diagGL_Q` (= `diag(1, m)`); the **lower** diagonal whose
slash action scales `τ ↦ m · τ` rather than `τ ↦ τ / m`. -/
noncomputable def diagGL_Q_lower (m : ℤ) (hm : 0 < m) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![(m : ℚ), 0; 0, 1]
    (by
      rw [Matrix.det_fin_two_of]
      simpa using hm.ne')

@[simp] lemma diagGL_Q_lower_coe_matrix (m : ℤ) (hm : 0 < m) :
    ((diagGL_Q_lower m hm : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      !![(m : ℚ), 0; 0, 1] :=
  rfl

/-- `qParam h (m · z) = (qParam h z) ^ m` for `m : ℕ`.  Inline helper
mirroring `QExpansionSlash.qParam_mul_nat` without pulling in that file's
heavy transitive imports. -/
lemma qParam_mul_nat (h : ℝ) (m : ℕ) (z : ℂ) :
    Function.Periodic.qParam h ((m : ℂ) * z) =
      (Function.Periodic.qParam h z) ^ m := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Pointwise slash formula** for `diagGL_Q_lower m`.
For any `f : ℍ → ℂ`, `k : ℤ`, `m : ℤ` with `0 < m`, and `τ : ℍ`,

`(f ∣[k] diagGL_Q_lower m hm) τ = m ^ (k-1) · f (glMap (diagGL_Q_lower m hm) • τ)`.

Mathlib normalisation: `|det|^(k-1) · denom^(-k) = m^(k-1) · 1^(-k) =
m^(k-1)` for `γ = diag(m, 1)` with det `m` and denom `= 1`. -/
lemma slash_diagGL_Q_lower_apply (k : ℤ) (m : ℤ) (hm : 0 < m)
    (f : UpperHalfPlane → ℂ) (τ : UpperHalfPlane) :
    (f ∣[k] (diagGL_Q_lower m hm : GL (Fin 2) ℚ)) τ =
      (m : ℂ) ^ (k - 1) * f (glMap (diagGL_Q_lower m hm) • τ) := by
  show ((f ∣[k] glMap (diagGL_Q_lower m hm)) τ) = _
  rw [ModularForm.slash_apply]
  have hdet_val : (glMap (diagGL_Q_lower m hm)).det.val = (m : ℝ) := by
    rw [show (glMap (diagGL_Q_lower m hm)).det.val =
      algebraMap ℚ ℝ (diagGL_Q_lower m hm).det.val from
      congr_arg Units.val (Matrix.GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      Matrix.GeneralLinearGroup.val_det_apply]
    simp [diagGL_Q_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two_of]
  have hdet_pos : 0 < (glMap (diagGL_Q_lower m hm)).det.val := by
    rw [hdet_val]; exact_mod_cast hm
  have hσ : UpperHalfPlane.σ (glMap (diagGL_Q_lower m hm)) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; simp only [hdet_pos, ↓reduceIte]
  have hdenom : UpperHalfPlane.denom (glMap (diagGL_Q_lower m hm)) ↑τ = 1 := by
    simp [UpperHalfPlane.denom, glMap, diagGL_Q_lower,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.cons_val_one]
  rw [hσ, RingHom.id_apply, hdet_val,
    abs_of_pos (show (0 : ℝ) < (m : ℝ) by exact_mod_cast hm), hdenom]
  simp [one_zpow]
  ring

/-- Möbius action of `glMap (diagGL_Q_lower m hm)`: sends `τ ↦ m · τ`. -/
lemma coe_diagGL_Q_lower_smul (m : ℤ) (hm : 0 < m) (τ : UpperHalfPlane) :
    (↑(glMap (diagGL_Q_lower m hm) • τ) : ℂ) = (m : ℂ) * (τ : ℂ) := by
  have hdet_val : (glMap (diagGL_Q_lower m hm)).det.val = (m : ℝ) := by
    rw [show (glMap (diagGL_Q_lower m hm)).det.val =
      algebraMap ℚ ℝ (diagGL_Q_lower m hm).det.val from
      congr_arg Units.val (Matrix.GeneralLinearGroup.map_det (algebraMap ℚ ℝ) _),
      Matrix.GeneralLinearGroup.val_det_apply]
    simp [diagGL_Q_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.det_fin_two_of]
  have hdet_pos : 0 < (glMap (diagGL_Q_lower m hm)).det.val := by
    rw [hdet_val]; exact_mod_cast hm
  simp only [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
    UpperHalfPlane.σ, hdet_pos, ↓reduceIte, RingHom.id_apply]
  set M := (↑(glMap (diagGL_Q_lower m hm)) : Matrix (Fin 2) (Fin 2) ℝ)
  have h00 : M 0 0 = (m : ℝ) := by
    simp [M, glMap, diagGL_Q_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h01 : M 0 1 = 0 := by
    simp [M, glMap, diagGL_Q_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h10 : M 1 0 = 0 := by
    simp [M, glMap, diagGL_Q_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : M 1 1 = 1 := by
    simp [M, glMap, diagGL_Q_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
      Matrix.cons_val_one]
  simp only [h00, h01, h10, h11]
  push_cast
  ring

/-- **q-expansion coefficient formula for the lower-diagonal slash.**

For `f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k` with `⇑g = ⇑f ∣[k]
diagGL_Q_lower m` as functions `ℍ → ℂ`, the `N`-level Fourier
coefficients of `g` are given by
`(qExpansion N g).coeff n = m^(k-1) · (qExpansion N f).coeff (n / m)` when
`m ∣ n` and `= 0` otherwise.

This is **not** a support constraint on `f` itself (`f`'s coefficients
can be arbitrary); rather it is a bijective determination: `g`'s
coefficients are determined by `f`'s, rescaled and reindexed by
multiplication by `m`.  It is the T_p_lower / lower-diagonal companion
to `qExpansion_support_of_diagGL_Q_slash` (T049, which constrains `f` by
the upper-diagonal slash).

**Miyake-lemma role**.  In Miyake §4.6.3, this formula feeds the
support-combining step: if for a fixed prime `p` coprime to `N` both
the upper-triangular slash by `diag(1, p)` **and** the lower-diagonal
slash by `diag(p, 1)` land in the character space, the two q-expansion
identities (support on multiples of `p` from T049 / coefficient
determination from this theorem) combine with the Hecke-operator
`T(p) f = f|T_p_upper_0 + ⋯ + f|T_p_upper_{p-1} + diamond · f|T_p_lower`
to force vanishing.  The **formal reduction** so obtained — given the
q-expansion formulas — is pure Dirichlet arithmetic combining support on
arithmetic progressions modulo `p`. -/
theorem qExpansion_of_diagGL_Q_lower_slash
    {N : ℕ} [NeZero N] {k : ℤ} {m : ℕ} (hm : 0 < m)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q_lower (m : ℤ) (by exact_mod_cast hm) : GL (Fin 2) ℚ)) :
    ∀ n : ℕ, (qExpansion (N : ℝ) g).coeff n =
      (if m ∣ n then (m : ℂ) ^ (k - 1) * (qExpansion (N : ℝ) f).coeff (n / m)
        else 0) := by
  have hm_int : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have hN_pos_R : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have h_sum_g : ∀ τ : UpperHalfPlane,
      HasSum (fun j : ℕ =>
        (if m ∣ j then (m : ℂ) ^ (k - 1) * (qExpansion (N : ℝ) f).coeff (j / m)
          else 0) •
          Function.Periodic.qParam (N : ℝ) (τ : ℂ) ^ j) (g τ) := by
    intro τ
    set γ : GL (Fin 2) ℚ := diagGL_Q_lower (m : ℤ) hm_int with hγ_def
    have hfsum := hasSum_qExpansion f hN_pos_R hN_period (glMap γ • τ : UpperHalfPlane)
    have hqeq :
        Function.Periodic.qParam (N : ℝ) ((glMap γ • τ : UpperHalfPlane) : ℂ) =
          (Function.Periodic.qParam (N : ℝ) (τ : ℂ)) ^ m := by
      rw [coe_diagGL_Q_lower_smul (m : ℤ) hm_int τ]
      exact qParam_mul_nat (N : ℝ) m (τ : ℂ)
    rw [hqeq] at hfsum
    have hslash : g τ = (m : ℂ) ^ (k - 1) * f (glMap γ • τ) := by
      show (⇑g : UpperHalfPlane → ℂ) τ = _
      rw [h_eq, hγ_def]
      exact slash_diagGL_Q_lower_apply k (m : ℤ) hm_int (⇑f) τ
    rw [hslash]
    have hscaled : HasSum (fun n : ℕ =>
          ((m : ℂ) ^ (k - 1) * (qExpansion (N : ℝ) f).coeff n) •
            ((Function.Periodic.qParam (N : ℝ) (τ : ℂ)) ^ m) ^ n)
          ((m : ℂ) ^ (k - 1) * f (glMap γ • τ)) := by
      convert hfsum.mul_left ((m : ℂ) ^ (k - 1)) using 1
      funext n
      simp [smul_eq_mul]
      ring
    have hreidx := hasSum_pow_mul_reindex hm hscaled
    convert hreidx using 1
    funext n
    split_ifs with hdvd
    · rfl
    · simp
  intro n
  exact (qExpansion_coeff_unique hN_pos_R hN_period h_sum_g n).symm

/-- **Combined prime-case coefficient formula.**
Package the T049 upper-diagonal support constraint with the T052
lower-diagonal coefficient formula into a single reduction theorem.

Hypotheses (for a fixed positive integer `p` — typically a prime):
* `f, g_u, g_l : ModularForm ((Gamma1 N).map (mapGL ℝ)) k`;
* `⇑g_u = ⇑f ∣[k] diag(1, p)` (upper slash is a level-`N` modular form);
* `⇑g_l = ⇑f ∣[k] diag(p, 1)` (lower slash is a level-`N` modular form).

Conclusions:
1. **Upper support (from T049)**: `(qExpansion N f).coeff n = 0` for
   every `n` not divisible by `p`.
2. **Lower formula (from T052)**: `(qExpansion N g_l).coeff n =
   p^(k-1) · (qExpansion N f).coeff (n / p)` when `p ∣ n`, else `0`.

Immediate consequence (not stated separately but visible from
conclusion 1 applied to conclusion 2's right-hand side): `g_l`'s
Fourier support at level `N` is on **multiples of `p²`**, since
`(qExpansion N f).coeff (n / p) = 0` unless `p ∣ (n / p)`, i.e.,
`p² ∣ n`.

**Role in Miyake 4.6.3**: this is the prime-case **coefficient-combining
reduction**.  Together with the `T(p) f ∈ charSpace` Hecke-operator
identity `T(p) f = Σ_b f ∣[k] T_p_upper(b) + χ(p) · f ∣[k] T_p_lower`
(existing in `HeckeT_p_Gamma0_Bridge.lean`), and a Dirichlet arithmetic
argument combining the `p²`-support on `g_l` with the `p`-support on
`f`, one obtains vanishing of all positive-index Fourier coefficients
of `f`.  The `a_0 = valueAtInfty f` term requires a separate classical
argument.

**Hypothesis discussion**: the hypotheses `h_u_eq`/`h_l_eq` are exactly
the level-`N`-modular-form wrapping of the raw slash actions, which is
the strong "f ∣[k] α lies in `M_k(Γ₀(N), χ)`" hypothesis of Miyake §4.6.3
specialised to `α ∈ {diag(1, p), diag(p, 1)}`.  No charSpace membership
of `g_u`/`g_l` is required. -/
theorem qExpansion_support_of_prime_upper_and_lower
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f g_u g_l : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_u_eq : (⇑g_u : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (p : ℤ) (by exact_mod_cast hp) : GL (Fin 2) ℚ))
    (h_l_eq : (⇑g_l : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q_lower (p : ℤ) (by exact_mod_cast hp) : GL (Fin 2) ℚ)) :
    (∀ n : ℕ, ¬ p ∣ n → (qExpansion (N : ℝ) f).coeff n = 0) ∧
    (∀ n : ℕ, (qExpansion (N : ℝ) g_l).coeff n =
      if p ∣ n then (p : ℂ) ^ (k - 1) * (qExpansion (N : ℝ) f).coeff (n / p)
      else 0) :=
  ⟨qExpansion_support_of_diagGL_Q_slash hp hN_period f g_u h_u_eq,
   qExpansion_of_diagGL_Q_lower_slash hp hN_period f g_l h_l_eq⟩

/-- **Refined combined support**: `g_l`'s Fourier coefficients are
supported on multiples of `p²`.  Immediate from
`qExpansion_support_of_prime_upper_and_lower` by composing the lower
formula with the upper support. -/
theorem qExpansion_support_of_prime_gl_p_sq
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f g_u g_l : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_u_eq : (⇑g_u : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (p : ℤ) (by exact_mod_cast hp) : GL (Fin 2) ℚ))
    (h_l_eq : (⇑g_l : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q_lower (p : ℤ) (by exact_mod_cast hp) : GL (Fin 2) ℚ)) :
    ∀ n : ℕ, ¬ (p * p) ∣ n → (qExpansion (N : ℝ) g_l).coeff n = 0 := by
  obtain ⟨hf_supp, hgl_fmla⟩ :=
    qExpansion_support_of_prime_upper_and_lower hp hN_period f g_u g_l h_u_eq h_l_eq
  intro n hnot
  rw [hgl_fmla]
  split_ifs with hdvd
  · have h_npdiv : ¬ p ∣ (n / p) := by
      intro hpdvd
      obtain ⟨q, hq⟩ := hpdvd
      apply hnot
      obtain ⟨r, hr⟩ := hdvd
      refine ⟨q, ?_⟩
      rw [show n = p * r from hr, Nat.mul_div_cancel_left r hp] at hq
      rw [hr, hq]; ring
    rw [hf_supp _ h_npdiv, mul_zero]
  · rfl

/-- **Conditional iteration reduction: positive-coefficient vanishing
under `h_iter`.**

Given the hypothesis `h_iter` — for each `r ≥ 1`, the slash
`⇑f ∣[k] diag(1, p^r)` is the underlying function of some level-`N`
modular form — every positive-index Fourier coefficient of `f` at
level `N` vanishes.

Proof: instantiate `h_iter` at `r := n` and apply T049's
`qExpansion_support_of_diagGL_Q_slash` with `m = p^n`; since
`n < p^n` (`Nat.lt_pow_self` for `1 < p`), the divisibility condition
`p^n ∣ n` fails and the support conclusion gives `(qExp N f).coeff n = 0`.

**Status of `h_iter`.**  `h_iter` is **strictly stronger** than
Miyake §4.6.3's single-slash hypothesis `f ∣[k] diag(1, p) ∈ M_k(N, χ)`
and is **not** derivable from it by `SlashAction.slash_mul` induction:
the inductive step would need every level-`N` modular form to be closed
under slash by `diag(1, p)`, which is false (applying this theorem
would then force every level-`N` form's positive Fourier coefficients
to vanish, contradicting Eisenstein series and Hecke eigenforms).  This
theorem is therefore a *conditional* reduction; closing the prime case
of Miyake 4.6.3 requires establishing `h_iter` from substantially
stronger infrastructure than the base slash hypothesis. -/
theorem qExpansion_f_vanish_positive_of_iterated_prime_diag
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 1 < p)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_iter : ∀ r : ℕ, 0 < r → ∃ g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k,
      (⇑g : UpperHalfPlane → ℂ) =
        ⇑f ∣[k] (diagGL_Q ((p ^ r : ℕ) : ℤ)
          (by exact_mod_cast Nat.pow_pos (show 0 < p by lia)) :
          GL (Fin 2) ℚ)) :
    ∀ n : ℕ, 0 < n → (qExpansion (N : ℝ) f).coeff n = 0 := by
  intro n hn
  have hp_pos : 0 < p := by lia
  have hpn_pos : 0 < p ^ n := Nat.pow_pos hp_pos
  obtain ⟨g, hg_eq⟩ := h_iter n hn
  refine qExpansion_support_of_diagGL_Q_slash hpn_pos hN_period f g hg_eq n ?_
  intro hdvd
  have h1 : p ^ n ≤ n := Nat.le_of_dvd hn hdvd
  have h2 : n < p ^ n := Nat.lt_pow_self hp
  lia

/-- Miyake §4.6.3-setting restatement of `qExpansion_support_of_diagGL_Q_slash`
(T049): if the single slash `f ∣[k] diag(1, p)` equals the underlying
function of a level-`N` modular form `g`, then `f`'s Fourier coefficients
at level `N` vanish on indices not divisible by `p`.

One-step support consequence of T049; does not itself imply full Miyake
vanishing. -/
theorem miyake_4_6_3_prime_slash_support
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (p : ℤ) (by exact_mod_cast hp) : GL (Fin 2) ℚ)) :
    ∀ n : ℕ, ¬ p ∣ n → (qExpansion (N : ℝ) f).coeff n = 0 :=
  qExpansion_support_of_diagGL_Q_slash hp hN_period f g h_eq

/-- **Prime-case Hecke eigenform closure: positive-coefficient vanishing.**

Combines T049's one-step support consequence with an explicit Hecke
eigenform Fourier recurrence to derive full positive-coefficient
vanishing of `f` at level `N`.

Hypotheses:
* `1 < p` (prime-style, only `p ≥ 2` used);
* `hN_period` strict-period witness;
* `h_eq : ⇑g = ⇑f ∣[k] diag(1, p)` — Miyake's single-slash hypothesis,
  i.e. the upper-diagonal slash of `f` is the underlying function of a
  level-`N` modular form `g`;
* `h_hecke` — the `T_p`-Hecke-eigenform Fourier recurrence
  `lam · a_n = a_{pn} + p^(k-1) · χp · [p ∣ n] · a_{n/p}` for all `n ≥ 1`,
  with eigenvalue `lam` and Nebentypus value `χp`.  This is the standard
  Hecke-eigenform identity on Fourier coefficients (Diamond–Shurman
  §5.2, matching `fourierCoeff_heckeT_p`) and packages the extra
  structure required to close the prime case.

Conclusion: `(qExpansion N f).coeff n = 0` for every `n ≥ 1`.

**How it avoids the false global-closure problem.**  The hypothesis
`h_hecke` is an *explicit* Fourier-level property of `f` — concretely,
that `f` is a `T_p`-Hecke eigenform.  It is **not** derived from a
generic closure statement like "every level-`N` modular form is closed
under slash by `diag(1, p)`".  That false closure was audited in T055
and shown to be false by reductio.  Here we take the eigenform identity
as an explicit assumption on `f` (justified in applications by
decomposing `f` into its Hecke eigen-component, or by taking `f`
directly to be an eigenform); the theorem does not import any global
closure.

**Proof**: strong induction on `n`.  For `p ∤ n` use T049 via
`miyake_4_6_3_prime_slash_support`.  For `p ∣ n`, write `n = p · m`
with `m < n` and apply the IH to `a_m` (and to `a_{m / p}` if `p ∣ m`);
the `h_hecke` identity at index `m` then expresses `a_{pm}` in terms of
these smaller-index coefficients, forcing `a_{pm} = 0`. -/
theorem miyake_4_6_3_prime_eigenform_case
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 1 < p)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    (f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (p : ℤ) (by exact_mod_cast (show 0 < p by lia))
        : GL (Fin 2) ℚ))
    (lam χp : ℂ)
    (h_hecke : ∀ n : ℕ, 0 < n →
      lam * (qExpansion (N : ℝ) f).coeff n =
        (qExpansion (N : ℝ) f).coeff (p * n) +
        (p : ℂ) ^ (k - 1) * χp *
          (if p ∣ n then (qExpansion (N : ℝ) f).coeff (n / p) else 0)) :
    ∀ n : ℕ, 0 < n → (qExpansion (N : ℝ) f).coeff n = 0 := by
  have hp_pos : 0 < p := by lia
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    by_cases hdvd : p ∣ n
    · obtain ⟨m, rfl⟩ := hdvd
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with hm0 | hm0
        · exfalso; subst hm0; simp at hn
        · exact hm0
      have hm_lt : m < p * m := by
        have h1 : 1 * m < p * m := (Nat.mul_lt_mul_right hm_pos).mpr hp
        simpa using h1
      have ham : (qExpansion (N : ℝ) f).coeff m = 0 := IH m hm_lt hm_pos
      have h_rel := h_hecke m hm_pos
      rw [ham, mul_zero] at h_rel
      by_cases hdvdm : p ∣ m
      · rw [if_pos hdvdm] at h_rel
        have hm_div_pos : 0 < m / p :=
          Nat.div_pos (Nat.le_of_dvd hm_pos hdvdm) hp_pos
        have hm_div_lt : m / p < p * m :=
          lt_of_le_of_lt (Nat.div_le_self _ _) hm_lt
        have ham_p : (qExpansion (N : ℝ) f).coeff (m / p) = 0 :=
          IH (m / p) hm_div_lt hm_div_pos
        rw [ham_p, mul_zero, add_zero] at h_rel
        exact h_rel.symm
      · rw [if_neg hdvdm, mul_zero, add_zero] at h_rel
        exact h_rel.symm
    · exact miyake_4_6_3_prime_slash_support hp_pos hN_period f g h_eq n hdvd

/-- **Derivation of T056's Hecke recurrence from a `T_p`-eigenform hypothesis.**

Given `f ∈ modFormCharSpace k χ` that is a `T_p`-Hecke eigenform with
eigenvalue `lam` (i.e. `heckeT_p k p hp hpN f = lam • f` as modular
forms), the Fourier coefficients of `f` at level `N` satisfy exactly
the T056 recurrence:

`lam * a_n = a_{pn} + p^(k-1) * χ(ZMod.unitOfCoprime p hpN) * [p ∣ n] * a_{n/p}`

for every `n ≥ 1`, with `χp := χ(ZMod.unitOfCoprime p hpN)`.

Combines `fourierCoeff_heckeT_p` (T_p's Fourier coefficient formula,
from `QExpansionSlash.lean`) with Mathlib's `qExpansion_smul` at the
scalar `lam`. -/
lemma hecke_recurrence_of_T_p_eigenform {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    {χ : (ZMod N)ˣ →* ℂˣ}
    {f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf_char : f ∈ modFormCharSpace k χ)
    (lam : ℂ) (h_eigen : heckeT_p k p hp hpN f = lam • f) :
    ∀ n : ℕ, 0 < n →
      lam * (qExpansion (N : ℝ) f).coeff n =
        (qExpansion (N : ℝ) f).coeff (p * n) +
        (p : ℂ) ^ (k - 1) *
          (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) *
          (if p ∣ n then (qExpansion (N : ℝ) f).coeff (n / p) else 0) := by
  have hN_pos_R : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  intro n _
  have h_lhs : (qExpansion (N : ℝ) (heckeT_p k p hp hpN f)).coeff n =
      (qExpansion (N : ℝ) f).coeff (p * n) +
        (p : ℂ) ^ (k - 1) *
          (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ) *
          (if p ∣ n then (qExpansion (N : ℝ) f).coeff (n / p) else 0) :=
    fourierCoeff_heckeT_p k hp hpN χ hf_char n
  have h_rhs : (qExpansion (N : ℝ) (heckeT_p k p hp hpN f)).coeff n =
      lam * (qExpansion (N : ℝ) f).coeff n := by
    have h_eq : qExpansion (N : ℝ) (heckeT_p k p hp hpN f) =
        lam • qExpansion (N : ℝ) f := by
      rw [h_eigen]
      exact qExpansion_smul hN_pos_R hN_period lam f
    rw [h_eq, PowerSeries.coeff_smul, smul_eq_mul]
  rw [h_rhs] at h_lhs
  exact h_lhs

/-- **Prime-case Hecke lemma for `T_p`-eigenforms (full corollary).**

Combines T056 with `hecke_recurrence_of_T_p_eigenform` to conclude
positive-coefficient vanishing of `f` directly from:

* `1 < p` (prime-style; we also assume `Nat.Prime p` for the `T_p`
  machinery and `Nat.Coprime p N` for the Hecke operator on character
  spaces);
* the strict-period witness for `N`;
* `f ∈ modFormCharSpace k χ` (character-space membership for some
  Nebentypus `χ`);
* `h_eq : ⇑g = ⇑f ∣[k] diag(1, p)` — Miyake's single-slash hypothesis
  packaged as `g` being a level-`N` modular form whose function equals
  the slash;
* `heckeT_p k p hp hpN f = lam • f` — `f` is a `T_p`-eigenform with
  eigenvalue `lam`.

Conclusion: `(qExpansion N f).coeff n = 0` for every `n ≥ 1`.

Replaces T056's abstract `h_hecke` hypothesis with the concrete
`T_p`-eigenform hypothesis from the Hecke operator API. -/
theorem miyake_4_6_3_prime_T_p_eigenform_case
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (hp_gt : 1 < p)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    {χ : (ZMod N)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hf_char : f ∈ modFormCharSpace k χ)
    (g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_eq : (⇑g : UpperHalfPlane → ℂ) =
      ⇑f ∣[k] (diagGL_Q (p : ℤ)
        (by exact_mod_cast (show 0 < p by lia)) : GL (Fin 2) ℚ))
    (lam : ℂ) (h_eigen : heckeT_p k p hp hpN f = lam • f) :
    ∀ n : ℕ, 0 < n → (qExpansion (N : ℝ) f).coeff n = 0 :=
  miyake_4_6_3_prime_eigenform_case hp_gt hN_period f g h_eq
    lam (↑(χ (ZMod.unitOfCoprime p hpN)) : ℂ)
    (hecke_recurrence_of_T_p_eigenform hp hpN hN_period hf_char lam h_eigen)

/-- **Prime Miyake 4.6.3 under an explicit Hecke-eigenform decomposition.**

Given a `modFormCharSpace k χ`-element `f` that decomposes as a finite
sum `f = ∑ i ∈ s, f_i` of `T_p`-eigenforms `f_i ∈ modFormCharSpace k χ`
(with eigenvalues `lam_i` and matching single-slash data `g_i`), the
positive-index Fourier coefficients of `f` vanish.

Proof strategy:
* Per-component: apply T060's `miyake_4_6_3_prime_T_p_eigenform_case` to
  each `f_i` to conclude `(qExpansion N (f_i i)).coeff n = 0`.
* Assembly: `qExpansion N (∑ i, f_i i) = ∑ i, qExpansion N (f_i i)` via
  the additive-monoid homomorphism `qExpansionAddHom`, and
  `PowerSeries.coeff` is linear, so the coefficient of the sum is the
  sum of coefficients — each zero.

**Limitation**: this theorem does **not** derive the decomposition
hypothesis `h_decomp` from the single slash hypothesis; it consumes an
explicit finite decomposition.  Removing that hypothesis requires the
full spectral/eigenbasis decomposition of `modFormCharSpace k χ` under
the commuting Hecke operators — an infrastructure obligation beyond
the current local API. -/
theorem miyake_4_6_3_prime_charspace_case
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : Nat.Prime p)
    (hpN : Nat.Coprime p N) (hp_gt : 1 < p)
    (hN_period : (N : ℝ) ∈ ((Gamma1 N).map (mapGL ℝ)).strictPeriods)
    {χ : (ZMod N)ˣ →* ℂˣ}
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    {ι : Type*} (s : Finset ι)
    (f_i : ι → ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (g_i : ι → ModularForm ((Gamma1 N).map (mapGL ℝ)) k)
    (lam_i : ι → ℂ)
    (h_char_i : ∀ i ∈ s, f_i i ∈ modFormCharSpace k χ)
    (h_eq_i : ∀ i ∈ s, (⇑(g_i i) : UpperHalfPlane → ℂ) =
      ⇑(f_i i) ∣[k] (diagGL_Q (p : ℤ)
        (by exact_mod_cast hp.pos) : GL (Fin 2) ℚ))
    (h_eigen_i : ∀ i ∈ s, heckeT_p k p hp hpN (f_i i) = lam_i i • (f_i i))
    (h_decomp : f = ∑ i ∈ s, f_i i) :
    ∀ n : ℕ, 0 < n → (qExpansion (N : ℝ) f).coeff n = 0 := by
  intro n hn
  have hN_pos_R : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_neZero N)
  have h_per : ∀ i ∈ s, (qExpansion (N : ℝ) (f_i i)).coeff n = 0 := fun i hi =>
    miyake_4_6_3_prime_T_p_eigenform_case hp hpN hp_gt hN_period
      (f_i i) (h_char_i i hi) (g_i i) (h_eq_i i hi) (lam_i i) (h_eigen_i i hi) n hn
  have h_coeff_sum : (qExpansion (N : ℝ) f).coeff n =
      ∑ i ∈ s, (qExpansion (N : ℝ) (f_i i)).coeff n := by
    rw [h_decomp]
    change (qExpansionAddHom hN_pos_R hN_period k (∑ i ∈ s, f_i i)).coeff n = _
    rw [map_sum, map_sum (PowerSeries.coeff (R := ℂ) n) _ s]
    rfl
  rw [h_coeff_sum]
  exact Finset.sum_eq_zero h_per

end HeckeRing.GLn
