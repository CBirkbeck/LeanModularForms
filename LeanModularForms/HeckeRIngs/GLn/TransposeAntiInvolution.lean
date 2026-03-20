/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.DiagonalCosets
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Commutativity

/-!
# GL_n Hecke Algebra Commutativity via Transpose

The transpose `ξ ↦ ᵗξ` is an anti-automorphism of `GL_n(ℚ)` that preserves `SL_n(ℤ)`
and the positive-determinant integer matrices `Δ`. Since every double coset has a
diagonal representative (which is fixed by transpose), Shimura's Proposition 3.8
gives commutativity of the Hecke ring.

## Main results

* `GL_pair_antiInvolution` -- the transpose as an `AntiInvolution` for `GL_pair n`
* `instCommRing_HeckeAlgebra` -- `CommRing (HeckeAlgebra n)`
-/

open Matrix HeckeRing HeckeRing.GLn

namespace HeckeRing.GLn

variable (n : ℕ) [NeZero n]

noncomputable def GL_transposeEquiv :
    GL (Fin n) ℚ ≃* (GL (Fin n) ℚ)ᵐᵒᵖ :=
  (Units.mapEquiv (transposeRingEquiv (Fin n) ℚ).toMulEquiv).trans Units.opEquiv

lemma GL_transposeEquiv_val (g : GL (Fin n) ℚ) :
    ((GL_transposeEquiv n g).unop : Matrix (Fin n) (Fin n) ℚ) =
    (↑g : Matrix (Fin n) (Fin n) ℚ)ᵀ := by
  simp [GL_transposeEquiv, Units.opEquiv, Units.mapEquiv, transposeRingEquiv]

lemma GL_transposeEquiv_involutive (g : GL (Fin n) ℚ) :
    (GL_transposeEquiv n (GL_transposeEquiv n g).unop).unop = g := by
  apply Units.ext; ext i j
  simp [GL_transposeEquiv_val]

lemma SLnZ_to_GLnQ_transpose (σ : SpecialLinearGroup (Fin n) ℤ) :
    (GL_transposeEquiv n (σ : GL (Fin n) ℚ)).unop = (σ.transpose : GL (Fin n) ℚ) := by
  apply Units.ext; ext i j
  rw [GL_transposeEquiv_val, SLnZ_to_GLnQ_val, SLnZ_to_GLnQ_val]
  simp [SpecialLinearGroup.coe_transpose]

lemma GL_transpose_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ_subgroup n) :
    (GL_transposeEquiv n g).unop ∈ SLnZ_subgroup n := by
  rw [mem_SLnZ_subgroup_iff] at hg ⊢
  obtain ⟨σ, rfl⟩ := hg
  exact ⟨σ.transpose, (SLnZ_to_GLnQ_transpose n σ).symm⟩

lemma HasIntEntries.transpose {g : GL (Fin n) ℚ} (hg : HasIntEntries n g) :
    HasIntEntries n (GL_transposeEquiv n g).unop := by
  obtain ⟨A, hA⟩ := hg
  refine ⟨Aᵀ, ?_⟩
  rw [GL_transposeEquiv_val, hA, Matrix.transpose_map]

lemma GL_transpose_mem_posDetInt {g : GL (Fin n) ℚ} (hg : g ∈ posDetInt_submonoid n) :
    (GL_transposeEquiv n g).unop ∈ posDetInt_submonoid n := by
  refine ⟨hg.1.transpose, ?_⟩
  rw [GL_transposeEquiv_val, Matrix.det_transpose]
  exact hg.2

lemma diagMat_GL_transpose_eq (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    (GL_transposeEquiv n (diagMat n a ha)).unop = diagMat n a ha := by
  apply Units.ext
  change (diagMat n a ha).val.transpose = (diagMat n a ha).val
  rw [diagMat_val, Matrix.diagonal_transpose]

/-- The transpose as an `AntiInvolution` for `GL_pair n`. -/
noncomputable def GL_pair_antiInvolution : AntiInvolution (GL_pair n) where
  toFun := (GL_transposeEquiv n).toMonoidHom
  involutive := GL_transposeEquiv_involutive n
  map_H := fun _g hg => GL_transpose_mem_SLnZ n hg
  map_Δ := fun _g hg => GL_transpose_mem_posDetInt n hg

/-- Transpose fixes every double coset of `GL_pair n`. -/
lemma GL_pair_onT'_eq (D : T' (GL_pair n)) :
    (GL_pair_antiInvolution n).onT' D = D := by
  apply T'_ext (GL_pair n)
  set g := (D.eql.choose : GL (Fin n) ℚ)
  obtain ⟨a, ha, hdiv, hrep⟩ := exists_diagonal_representative n D.eql.choose
  have hD_set : D.set = DoubleCoset.doubleCoset (diagMat n a ha : GL (Fin n) ℚ)
      (GL_pair n).H (GL_pair n).H := by
    have h1 := D.eql.choose_spec
    have h2 := congr_arg T'.set hrep
    simp only [T_mk, T_diag, diagMat_delta] at h2
    rw [h1, h2]
  have hg_mem : g ∈ DoubleCoset.doubleCoset (diagMat n a ha : GL (Fin n) ℚ)
      (GL_pair n).H (GL_pair n).H := by
    rw [← hD_set]; rw [D.eql.choose_spec]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hg_mem
  obtain ⟨L, hL, R, hR, hg_eq⟩ := hg_mem
  have hbar_mem : (GL_pair_antiInvolution n).bar g ∈
      DoubleCoset.doubleCoset (diagMat n a ha : GL (Fin n) ℚ) (GL_pair n).H (GL_pair n).H := by
    show (GL_transposeEquiv n g).unop ∈ _
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨(GL_transposeEquiv n R).unop, GL_transpose_mem_SLnZ n hR,
           (GL_transposeEquiv n L).unop, GL_transpose_mem_SLnZ n hL, ?_⟩
    apply Units.ext
    simp only [GL_transposeEquiv_val, Units.val_mul, hg_eq, Matrix.transpose_mul,
      diagMat_val, Matrix.diagonal_transpose, Matrix.mul_assoc]
  conv_lhs => rw [AntiInvolution.onT'_set]
  conv_rhs => rw [hD_set]
  exact DoubleCoset.doubleCoset_eq_of_mem hbar_mem

/-- **Shimura Proposition 3.8 for GL_n**: the Hecke algebra is commutative. -/
noncomputable instance instCommRing_HeckeAlgebra : CommRing (HeckeAlgebra n) :=
  instCommRing_of_antiInvolution (GL_pair_antiInvolution n) (GL_pair_onT'_eq n)

end HeckeRing.GLn
