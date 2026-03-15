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

* `GL_pair_antiInvolution` — the transpose as an `AntiInvolution` for `GL_pair n`
* `instCommRing_HeckeAlgebra` — `CommRing (HeckeAlgebra n)`
-/

open Matrix HeckeRing HeckeRing.GLn

namespace HeckeRing.GLn

variable (n : ℕ) [NeZero n]

/-! ### Transpose on GL_n(ℚ) -/

/-- Transpose as a `MulEquiv` from `GL_n(ℚ)` to `GL_n(ℚ)ᵐᵒᵖ`.
    Constructed by composing `transposeRingEquiv` (matrix level) with
    `Units.mapEquiv` (lifting to units) and `Units.opEquiv` (moving `ᵐᵒᵖ` outside). -/
noncomputable def GL_transposeEquiv :
    GL (Fin n) ℚ ≃* (GL (Fin n) ℚ)ᵐᵒᵖ :=
  (Units.mapEquiv (transposeRingEquiv (Fin n) ℚ).toMulEquiv).trans Units.opEquiv

/-- The underlying matrix of `GL_transposeEquiv g` is `gᵀ`. -/
lemma GL_transposeEquiv_val (g : GL (Fin n) ℚ) :
    ((GL_transposeEquiv n g).unop : Matrix (Fin n) (Fin n) ℚ) =
    (↑g : Matrix (Fin n) (Fin n) ℚ)ᵀ := by
  simp [GL_transposeEquiv, Units.opEquiv, Units.mapEquiv, transposeRingEquiv]

/-- `GL_transposeEquiv` is involutive: `(gᵀ)ᵀ = g`. -/
lemma GL_transposeEquiv_involutive (g : GL (Fin n) ℚ) :
    (GL_transposeEquiv n (GL_transposeEquiv n g).unop).unop = g := by
  apply Units.ext; ext i j
  simp [GL_transposeEquiv_val]

/-! ### Transpose preserves SL_n(ℤ) -/

/-- `SLnZ_to_GLnQ` commutes with transpose:
    `(SLnZ_to_GLnQ σ)ᵀ = SLnZ_to_GLnQ (σᵀ)`. -/
lemma SLnZ_to_GLnQ_transpose (σ : SpecialLinearGroup (Fin n) ℤ) :
    (GL_transposeEquiv n (SLnZ_to_GLnQ n σ)).unop = SLnZ_to_GLnQ n σ.transpose := by
  apply Units.ext; ext i j
  rw [GL_transposeEquiv_val, SLnZ_to_GLnQ_val, SLnZ_to_GLnQ_val]
  simp [SpecialLinearGroup.coe_transpose, Matrix.transpose_map]

/-- Transpose preserves `SLnZ_subgroup`: if `g ∈ SL_n(ℤ)`, then `gᵀ ∈ SL_n(ℤ)`. -/
lemma GL_transpose_mem_SLnZ {g : GL (Fin n) ℚ} (hg : g ∈ SLnZ_subgroup n) :
    (GL_transposeEquiv n g).unop ∈ SLnZ_subgroup n := by
  rw [SLnZ_subgroup, MonoidHom.mem_range] at hg ⊢
  obtain ⟨σ, rfl⟩ := hg
  exact ⟨σ.transpose, (SLnZ_to_GLnQ_transpose n σ).symm⟩

/-! ### Transpose preserves Δ (positive-determinant integer matrices) -/

/-- Transpose preserves integer entries. -/
lemma HasIntEntries.transpose {g : GL (Fin n) ℚ} (hg : HasIntEntries n g) :
    HasIntEntries n (GL_transposeEquiv n g).unop := by
  obtain ⟨A, hA⟩ := hg
  refine ⟨Aᵀ, ?_⟩
  rw [GL_transposeEquiv_val, hA, Matrix.transpose_map]

/-- Transpose preserves `posDetInt_submonoid`: if `g ∈ Δ`, then `gᵀ ∈ Δ`. -/
lemma GL_transpose_mem_posDetInt {g : GL (Fin n) ℚ} (hg : g ∈ posDetInt_submonoid n) :
    (GL_transposeEquiv n g).unop ∈ posDetInt_submonoid n := by
  refine ⟨hg.1.transpose, ?_⟩
  rw [GL_transposeEquiv_val, Matrix.det_transpose]
  exact hg.2

/-! ### Transpose fixes diagonal matrices -/

/-- The GL-level transpose of a diagonal matrix is itself. -/
lemma diagMat_GL_transpose_eq (a : Fin n → ℕ+) :
    (GL_transposeEquiv n (diagMat n a)).unop = diagMat n a := by
  apply Units.ext
  change (diagMat n a).val.transpose = (diagMat n a).val
  rw [diagMat_val, Matrix.diagonal_transpose]

/-! ### Assembly: the AntiInvolution and CommRing instance -/

/-- The transpose as an `AntiInvolution` for `GL_pair n`. -/
noncomputable def GL_pair_antiInvolution : AntiInvolution (GL_pair n) where
  toFun := (GL_transposeEquiv n).toMonoidHom
  involutive := GL_transposeEquiv_involutive n
  map_H := fun g hg => GL_transpose_mem_SLnZ n hg
  map_Δ := fun g hg => GL_transpose_mem_posDetInt n hg

/-- Transpose fixes every double coset of `GL_pair n`.
    Proof: every double coset has a diagonal representative (SNF), and diagonal
    matrices are fixed by transpose. -/
lemma GL_pair_onT'_eq (D : T' (GL_pair n)) :
    (GL_pair_antiInvolution n).onT' D = D := by
  -- Use the abstract bar_mem_doubleCoset machinery.
  -- It suffices to show bar(g) ∈ D.set for g = D.eql.choose.
  -- By exists_diagonal_representative, D has a diagonal rep: D.set = DC(diagMat a).
  -- g ∈ DC(diagMat a), so g = L * diagMat(a) * R with L, R ∈ H.
  -- bar(g) = gᵀ = Rᵀ * diagMat(a) * Lᵀ ∈ DC(diagMat a) = D.set.
  apply T'_ext (GL_pair n)
  set g := (D.eql.choose : GL (Fin n) ℚ)
  -- Get diagonal representative
  obtain ⟨a, hdiv, hrep⟩ := exists_diagonal_representative n D.eql.choose
  have hD_set : D.set = DoubleCoset.doubleCoset (diagMat n a : GL (Fin n) ℚ)
      (GL_pair n).H (GL_pair n).H := by
    have h1 := D.eql.choose_spec  -- D.set = DC(D.eql.choose)
    have h2 := congr_arg T'.set hrep  -- (T_mk D.eql.choose).set = (T_diag a hdiv).set
    simp only [T_mk, T_diag, diagMat_delta] at h2
    rw [h1, h2]
  -- g ∈ DC(diagMat a)
  have hg_mem : g ∈ DoubleCoset.doubleCoset (diagMat n a : GL (Fin n) ℚ)
      (GL_pair n).H (GL_pair n).H := by
    rw [← hD_set]; rw [D.eql.choose_spec]; exact DoubleCoset.mem_doubleCoset_self _ _ _
  rw [DoubleCoset.mem_doubleCoset] at hg_mem
  obtain ⟨L, hL, R, hR, hg_eq⟩ := hg_mem
  -- Show gᵀ ∈ DC(diagMat a)
  have hbar_mem : (GL_pair_antiInvolution n).bar g ∈
      DoubleCoset.doubleCoset (diagMat n a : GL (Fin n) ℚ) (GL_pair n).H (GL_pair n).H := by
    show (GL_transposeEquiv n g).unop ∈ _
    rw [DoubleCoset.mem_doubleCoset]
    refine ⟨(GL_transposeEquiv n R).unop, GL_transpose_mem_SLnZ n hR,
           (GL_transposeEquiv n L).unop, GL_transpose_mem_SLnZ n hL, ?_⟩
    -- gᵀ = Rᵀ * diagMat(a) * Lᵀ
    -- Prove at the raw matrix level, then lift
    have h_mat : g.val.transpose =
        R.val.transpose * (diagMat n a).val * L.val.transpose := by
      rw [hg_eq]; simp only [Units.val_mul, Matrix.transpose_mul]
      rw [show (diagMat n a).val.transpose = (diagMat n a).val from by
            rw [diagMat_val]; exact Matrix.diagonal_transpose _]
      rw [Matrix.mul_assoc]
    -- Now lift to GL equality
    have h1 : (GL_transposeEquiv n g).unop.val = g.val.transpose :=
      GL_transposeEquiv_val n g
    have h2 : ((GL_transposeEquiv n R).unop).val = R.val.transpose :=
      GL_transposeEquiv_val n R
    have h3 : ((GL_transposeEquiv n L).unop).val = L.val.transpose :=
      GL_transposeEquiv_val n L
    apply Units.ext; show (GL_transposeEquiv n g).unop.val = _
    rw [h1, h_mat, Units.val_mul, Units.val_mul, h2, h3]
  -- DC(gᵀ) = DC(diagMat a) = D.set
  -- We need (onT' D).set = D.set
  -- (onT' D).set = DC(bar g) = DC(gᵀ)  [by definition of onT']
  -- DC(gᵀ) = DC(diagMat a)              [since gᵀ ∈ DC(diagMat a)]
  -- DC(diagMat a) = D.set               [by hD_set]
  conv_lhs => rw [AntiInvolution.onT'_set]
  conv_rhs => rw [hD_set]
  exact DoubleCoset.doubleCoset_eq_of_mem hbar_mem

/-- **Shimura Proposition 3.8 for GL_n**: the Hecke algebra is commutative. -/
noncomputable instance instCommRing_HeckeAlgebra : CommRing (HeckeAlgebra n) :=
  instCommRing_of_antiInvolution (GL_pair_antiInvolution n) (GL_pair_onT'_eq n)

end HeckeRing.GLn
