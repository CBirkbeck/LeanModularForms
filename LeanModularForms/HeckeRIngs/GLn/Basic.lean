/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Commensurable
import LeanModularForms.HeckeRIngs.AbstractHeckeRing.Basic

/-!
# GL_n ArithmeticGroupPair

Constructs the canonical `ArithmeticGroupPair (GL (Fin n) ℚ)` with:
- `H = SL_n(ℤ)` (embedded in GL_n(ℚ))
- `Δ = {α ∈ M_n(ℤ) ∩ GL_n(ℚ) | det(α) > 0}` (integer matrices with positive determinant)

This is the foundation for the Hecke ring of GL_n following Shimura §3.2.

## Main definitions

* `SLnZ_to_GLnQ` — embedding `SL_n(ℤ) →* GL_n(ℚ)`
* `SLnZ_subgroup` — `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)`
* `posDetInt_submonoid` — positive-determinant integer matrices as a submonoid of `GL_n(ℚ)`
* `GL_pair` — the standard `ArithmeticGroupPair`

## Main results

* `SLnZ_le_posDetInt` — `SL_n(ℤ) ⊆ Δ`
* `posDetInt_le_commensurator` — `Δ ⊆ commensurator(SL_n(ℤ))`
-/

open Matrix Subgroup.Commensurable Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

section Embedding

/-- Embed `SL_n(ℤ)` into `GL_n(ℚ)` via `ℤ ↪ ℚ` and the inclusion `SL → GL`. -/
noncomputable def SLnZ_to_GLnQ :
    SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ :=
  (SpecialLinearGroup.toGL).comp (SpecialLinearGroup.map (Int.castRingHom ℚ))

/-- `SL_n(ℤ)` as a subgroup of `GL_n(ℚ)`. -/
noncomputable def SLnZ_subgroup : Subgroup (GL (Fin n) ℚ) :=
  (SLnZ_to_GLnQ n).range

/-- The matrix underlying `SLnZ_to_GLnQ A` is `A.val.map Int.cast`. -/
lemma SLnZ_to_GLnQ_val (A : SpecialLinearGroup (Fin n) ℤ) :
    ↑(SLnZ_to_GLnQ n A) = (↑A : Matrix (Fin n) (Fin n) ℤ).map (Int.cast : ℤ → ℚ) := by
  ext i j
  simp [SLnZ_to_GLnQ, SpecialLinearGroup.toGL, SpecialLinearGroup.map,
    RingHom.mapMatrix_apply, Matrix.map_apply]

/-- The determinant of `SLnZ_to_GLnQ A` is 1. -/
lemma SLnZ_to_GLnQ_det (A : SpecialLinearGroup (Fin n) ℤ) :
    (↑(SLnZ_to_GLnQ n A) : Matrix (Fin n) (Fin n) ℚ).det = 1 := by
  have h1 : (↑(SLnZ_to_GLnQ n A) : Matrix (Fin n) (Fin n) ℚ) =
      (Int.castRingHom ℚ).mapMatrix ↑A := by
    rw [SLnZ_to_GLnQ_val]; ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [h1, ← RingHom.map_det, Int.coe_castRingHom]
  simp [A.prop]

end Embedding

section PosDetInt

/-- An element of `GL_n(ℚ)` has integer matrix entries if its underlying matrix
    is the image of an integer matrix under `ℤ → ℚ`. -/
def HasIntEntries (g : GL (Fin n) ℚ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℤ,
    (↑g : Matrix (Fin n) (Fin n) ℚ) = A.map (Int.cast : ℤ → ℚ)

/-- The identity matrix has integer entries. -/
lemma hasIntEntries_one : HasIntEntries n (1 : GL (Fin n) ℚ) :=
  ⟨1, by ext i j; simp [Matrix.map_apply, Matrix.one_apply]⟩

/-- Product of integer-entry matrices has integer entries. -/
lemma HasIntEntries.mul {a b : GL (Fin n) ℚ}
    (ha : HasIntEntries n a) (hb : HasIntEntries n b) :
    HasIntEntries n (a * b) := by
  obtain ⟨A, hA⟩ := ha
  obtain ⟨B, hB⟩ := hb
  exact ⟨A * B, by ext i j; simp [hA, hB, Matrix.mul_apply, Matrix.map_apply]⟩

/-- `det (A.map Int.cast) = ↑(det A)` for integer matrices cast to `ℚ`. -/
private lemma det_intMat_cast (A : Matrix (Fin n) (Fin n) ℤ) :
    (A.map (Int.cast : ℤ → ℚ)).det = (A.det : ℚ) := by
  have h : A.map (Int.cast : ℤ → ℚ) = (Int.castRingHom ℚ).mapMatrix A := by
    ext i j; simp [RingHom.mapMatrix_apply, Matrix.map_apply]
  rw [h, ← RingHom.map_det, Int.coe_castRingHom]

/-- The submonoid of `GL_n(ℚ)` consisting of invertible matrices with integer entries
    and positive determinant. This is Shimura's `Δ`. -/
noncomputable def posDetInt_submonoid : Submonoid (GL (Fin n) ℚ) where
  carrier := {g | HasIntEntries n g ∧ 0 < (↑g : Matrix (Fin n) (Fin n) ℚ).det}
  one_mem' := ⟨hasIntEntries_one n, by simp⟩
  mul_mem' := by
    intro a b ⟨ha, hda⟩ ⟨hb, hdb⟩
    exact ⟨HasIntEntries.mul (n := n) ha hb, by
      simp only [GeneralLinearGroup.coe_mul, Matrix.det_mul]; exact mul_pos hda hdb⟩

end PosDetInt

section Pair

variable [NeZero n]

omit [NeZero n] in
/-- `SL_n(ℤ) ⊆ Δ`: elements of `SL_n(ℤ)` have integer entries and det = 1 > 0. -/
lemma SLnZ_le_posDetInt :
    (SLnZ_subgroup n).toSubmonoid ≤ posDetInt_submonoid n := by
  intro g hg
  rw [SLnZ_subgroup, Subgroup.mem_toSubmonoid, MonoidHom.mem_range] at hg
  obtain ⟨A, rfl⟩ := hg
  refine ⟨⟨A.val, SLnZ_to_GLnQ_val n A⟩, ?_⟩
  rw [SLnZ_to_GLnQ_det]
  exact one_pos

/-! ### Helper lemmas for the commensurator proof (Shimura Lemma 3.10) -/

omit [NeZero n] in
/-- `SLnZ_to_GLnQ` is injective. -/
private lemma SLnZ_to_GLnQ_injective : Function.Injective (SLnZ_to_GLnQ n) := by
  intro x y hxy; ext i j
  have h := congr_arg (fun (g : GL (Fin n) ℚ) => (g : Matrix (Fin n) (Fin n) ℚ) i j) hxy
  simp only [SLnZ_to_GLnQ_val, Matrix.map_apply] at h; exact_mod_cast h

omit [NeZero n] in
/-- Kernel element of `SL_n(ℤ) → SL_n(ℤ/dℤ)` has entries congruent to identity mod d. -/
private lemma ker_entry_dvd (d : ℕ) [NeZero d]
    (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod d))).ker)
    (i j : Fin n) :
    (d : ℤ) ∣ (γ.val i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j) := by
  rw [MonoidHom.mem_ker] at hγ
  have h := congr_fun₂ (congr_arg Subtype.val hγ) i j
  simp [SpecialLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply] at h
  rw [Matrix.one_apply] at h ⊢
  split_ifs at h ⊢
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by push_cast; simp [h])
  · rw [sub_zero]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

omit [NeZero n] in
/-- If `d | (γ - I)` entry-wise, then `d | (adj(A) * γ * A)` entry-wise.
    Key: `adj(A) * (I + dM) * A = d·I + d·(adj(A)·M·A)`. -/
private lemma adjugate_conj_dvd
    (A gamma : Matrix (Fin n) (Fin n) ℤ)
    (hgamma : ∀ i j : Fin n, A.det ∣ (gamma i j - (1 : Matrix (Fin n) (Fin n) ℤ) i j))
    (i j : Fin n) :
    A.det ∣ (A.adjugate * gamma * A) i j := by
  set M := Matrix.of fun i j => (gamma i j - (1 : Matrix _ _ ℤ) i j) / A.det
  have hgamma_eq : gamma = 1 + A.det • M := by
    ext i j; simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.of_apply, M]; simp only [Matrix.one_apply] at hgamma
    nlinarith [mul_comm ((gamma i j - if i = j then 1 else 0) / A.det) A.det,
               Int.ediv_mul_cancel (hgamma i j)]
  have : A.adjugate * gamma * A = A.adjugate * A + A.det • (A.adjugate * M * A) := by
    rw [hgamma_eq]; conv_lhs => rw [mul_add, Matrix.mul_one, mul_smul_comm]
    rw [add_mul, smul_mul_assoc]
  rw [this, adjugate_mul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)

/-- The integer matrix `(adj(A) * γ * A) / det(A)` has determinant 1
    when `det(γ) = 1`. -/
private lemma conj_mat_det_one
    (A gamma : Matrix (Fin n) (Fin n) ℤ) (hgamma_det : gamma.det = 1)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A.adjugate * gamma * A) i j)
    (hAdet : A.det ≠ 0) :
    (Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det).det = 1 := by
  suffices h : ((Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det).det : ℚ) = 1 by
    exact_mod_cast h
  have h_mat_eq : (Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det).map
      (Int.cast : ℤ → ℚ) =
      (A.det : ℚ)⁻¹ • ((A.adjugate * gamma * A).map (Int.cast : ℤ → ℚ)) := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    rw [Int.cast_div (hdvd i j) (Int.cast_ne_zero.mpr hAdet)]; ring
  have hAQ : (A.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hAdet
  rw [← det_intMat_cast, h_mat_eq, det_smul, Fintype.card_fin, det_intMat_cast]
  simp only [Matrix.det_mul, det_adjugate, hgamma_det, Fintype.card_fin]
  push_cast; rw [mul_one, inv_pow, ← pow_succ, Nat.sub_one_add_one_eq_of_pos (NeZero.pos n)]
  simp only [det_intMat_cast]
  exact inv_mul_cancel₀ (pow_ne_zero n hAQ)

omit [NeZero n] in
/-- If `A * δ = γ * A` at the integer level, then `g * δ_GL = γ_GL * g` at the GL level,
    so `δ_GL = g⁻¹ * γ_GL * g`. -/
private lemma int_mul_eq
    (A gamma : Matrix (Fin n) (Fin n) ℤ) (hAdet : A.det ≠ 0)
    (hdvd : ∀ i j : Fin n, A.det ∣ (A.adjugate * gamma * A) i j) :
    A * (Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det) = gamma * A := by
  set delta := Matrix.of fun i j => (A.adjugate * gamma * A) i j / A.det
  have ha : A.det • delta = A.adjugate * gamma * A := by
    ext i j; simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, delta]
    exact Int.mul_ediv_cancel' (hdvd i j)
  suffices h : A.det • (A * delta) = A.det • (gamma * A) by
    ext i j; exact mul_left_cancel₀ hAdet
      (by simpa [Matrix.smul_apply, smul_eq_mul] using congr_fun₂ h i j)
  rw [← mul_smul_comm, ha, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    mul_adjugate, smul_mul_assoc, one_mul, smul_mul_assoc]

/-- Main step: for `g` with integer matrix `A` and `det(A) > 0`,
    kernel elements of `SL_n(ℤ) → SL_n(ℤ/dℤ)` conjugated by `g⁻¹` remain in `SL_n(ℤ)`.
    This is the mathematical heart of Shimura's Lemma 3.10. -/
private lemma conj_ker_mem_SLnZ
    (g : GL (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : (↑g : Matrix _ _ ℚ) = A.map (Int.cast : ℤ → ℚ))
    (hAdet : A.det ≠ 0)
    (γ : SpecialLinearGroup (Fin n) ℤ)
    (hγ : γ ∈ (SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs))).ker) :
    g⁻¹ * SLnZ_to_GLnQ n γ * g ∈ SLnZ_subgroup n := by
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet⟩
  have h_entry : ∀ i j, A.det ∣ (γ.val i j - (1 : Matrix _ _ ℤ) i j) := by
    intro i j; exact Int.natAbs_dvd.mp (ker_entry_dvd n A.det.natAbs γ hγ i j)
  have hdvd := adjugate_conj_dvd n A γ.val h_entry
  set delta_mat := Matrix.of fun i j => (A.adjugate * γ.val * A) i j / A.det with hdelta_def
  have hdelta_det : delta_mat.det = 1 := conj_mat_det_one n A γ.val γ.prop hdvd hAdet
  set delta : SpecialLinearGroup (Fin n) ℤ := ⟨delta_mat, hdelta_det⟩
  rw [SLnZ_subgroup, MonoidHom.mem_range]
  refine ⟨delta, ?_⟩
  have h_int_eq : A * delta_mat = γ.val * A := int_mul_eq n A γ.val hAdet hdvd
  have h_mat_eq : (g * SLnZ_to_GLnQ n delta).val =
      (SLnZ_to_GLnQ n γ * g).val := by
    show (g.val * (SLnZ_to_GLnQ n delta).val : Matrix _ _ ℚ) =
         ((SLnZ_to_GLnQ n γ).val * g.val : Matrix _ _ ℚ)
    rw [SLnZ_to_GLnQ_val, SLnZ_to_GLnQ_val, hA]
    rw [show (A.map (Int.cast : ℤ → ℚ)) * (delta_mat.map _) =
        (A * delta_mat).map (Int.cast : ℤ → ℚ) from by
      ext i j; simp [Matrix.mul_apply, Matrix.map_apply]]
    rw [show (γ.val.map (Int.cast : ℤ → ℚ)) * (A.map _) =
        (γ.val * A).map (Int.cast : ℤ → ℚ) from by
      ext i j; simp [Matrix.mul_apply, Matrix.map_apply]]
    rw [h_int_eq]
  have h_unit_eq : g * SLnZ_to_GLnQ n delta = SLnZ_to_GLnQ n γ * g := Units.ext h_mat_eq
  calc SLnZ_to_GLnQ n delta
      = g⁻¹ * (g * SLnZ_to_GLnQ n delta) := by rw [inv_mul_cancel_left]
    _ = g⁻¹ * (SLnZ_to_GLnQ n γ * g) := by rw [h_unit_eq]
    _ = g⁻¹ * SLnZ_to_GLnQ n γ * g := by rw [mul_assoc]

/-- `Δ ⊆ commensurator(SL_n(ℤ))`: for any integer matrix `α` with positive determinant,
    `SL_n(ℤ)` and `α · SL_n(ℤ) · α⁻¹` are commensurable.

    The key idea (Shimura Lemma 3.10): if `α` has integer entries with `det(α) = d > 0`,
    then the congruence subgroup `Γ(d) = ker(SL_n(ℤ) → SL_n(ℤ/dℤ))` has finite index
    in `SL_n(ℤ)` and is contained in both `SL_n(ℤ) ∩ α·SL_n(ℤ)·α⁻¹` and
    `SL_n(ℤ) ∩ α⁻¹·SL_n(ℤ)·α`, establishing commensurability. -/
lemma posDetInt_le_commensurator :
    posDetInt_submonoid n ≤ (commensurator (SLnZ_subgroup n)).toSubmonoid := by
  intro g ⟨⟨A, hA⟩, hdet⟩
  rw [Subgroup.mem_toSubmonoid, commensurator_mem_iff]
  set H := SLnZ_subgroup n
  have hAdet_pos : 0 < A.det := by
    have h1 : (0 : ℚ) < (A.det : ℚ) := by
      have h2 : (A.det : ℚ) = (A.map (Int.cast : ℤ → ℚ)).det := (det_intMat_cast n A).symm
      rw [h2, ← hA]; exact hdet
    exact Int.cast_pos.mp h1
  have hAdet_ne : A.det ≠ 0 := ne_of_gt hAdet_pos
  have hnatAbs_ne : NeZero A.det.natAbs := ⟨Int.natAbs_ne_zero.mpr hAdet_ne⟩
  set phi : SpecialLinearGroup (Fin n) ℤ →* SpecialLinearGroup (Fin n) (ZMod A.det.natAbs) :=
    SpecialLinearGroup.map (Int.castRingHom (ZMod A.det.natAbs)) with hphi_def
  set K := phi.ker.map (SLnZ_to_GLnQ n) with hK_def
  have hK_le_H : K ≤ H := by
    intro x hx; simp only [K, Subgroup.mem_map] at hx
    obtain ⟨γ, _, rfl⟩ := hx; exact ⟨γ, rfl⟩
  have hK_relIndex : K.relIndex H ≠ 0 := by
    have h1 : H = Subgroup.map (SLnZ_to_GLnQ n) ⊤ := by
      simp [H, SLnZ_subgroup, MonoidHom.range_eq_map]
    rw [hK_def, h1, Subgroup.relIndex_map_map_of_injective _ _ (SLnZ_to_GLnQ_injective n),
      Subgroup.relIndex_top_right]
    exact (Subgroup.finiteIndex_ker phi).index_ne_zero
  have hK_le_gH : K ≤ ConjAct.toConjAct g • H := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [K, Subgroup.mem_map] at hx
    obtain ⟨γ, hγ_ker, rfl⟩ := hx
    show (ConjAct.toConjAct g)⁻¹ • SLnZ_to_GLnQ n γ ∈ H
    rw [ConjAct.smul_def, ConjAct.ofConjAct_inv, ConjAct.ofConjAct_toConjAct]
    exact conj_ker_mem_SLnZ n g A hA hAdet_ne γ hγ_ker
  have hK_le_ginvH : K ≤ ConjAct.toConjAct g⁻¹ • H := by
    intro x hx
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.toConjAct_inv, inv_inv]
    simp only [K, Subgroup.mem_map] at hx
    obtain ⟨γ, hγ_ker, rfl⟩ := hx
    show ConjAct.toConjAct g • SLnZ_to_GLnQ n γ ∈ H
    rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    have h_entry : ∀ i j, A.det ∣ (γ.val i j - (1 : Matrix _ _ ℤ) i j) := by
      intro i j; exact Int.natAbs_dvd.mp (ker_entry_dvd n A.det.natAbs γ hγ_ker i j)
    have hdvd' : ∀ i j : Fin n, A.det ∣ (A * γ.val * A.adjugate) i j := by
      intro i j
      set M := Matrix.of fun i j => (γ.val i j - (1 : Matrix _ _ ℤ) i j) / A.det
      have hgamma_eq : γ.val = 1 + A.det • M := by
        ext i j; simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
          Matrix.of_apply, M]; simp only [Matrix.one_apply] at h_entry
        nlinarith [mul_comm ((γ.val i j - if i = j then 1 else 0) / A.det) A.det,
                   Int.ediv_mul_cancel (h_entry i j)]
      have : A * γ.val * A.adjugate = A * A.adjugate + A.det • (A * M * A.adjugate) := by
        rw [hgamma_eq]; conv_lhs => rw [mul_add, Matrix.mul_one, mul_smul_comm]
        rw [add_mul, smul_mul_assoc]
      rw [this, mul_adjugate]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact dvd_add (dvd_mul_right _ _) (dvd_mul_right _ _)
    set delta'_mat := Matrix.of fun i j => (A * γ.val * A.adjugate) i j / A.det
    have hdelta'_det : delta'_mat.det = 1 := by
      suffices h : (delta'_mat.det : ℚ) = 1 by exact_mod_cast h
      have h_mat_eq : delta'_mat.map (Int.cast : ℤ → ℚ) =
          (A.det : ℚ)⁻¹ • ((A * γ.val * A.adjugate).map (Int.cast : ℤ → ℚ)) := by
        ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,
          delta'_mat]
        rw [Int.cast_div (hdvd' i j) (Int.cast_ne_zero.mpr hAdet_ne)]; ring
      have hAQ : (A.det : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hAdet_ne
      rw [← det_intMat_cast, h_mat_eq, det_smul, Fintype.card_fin, det_intMat_cast]
      simp only [Matrix.det_mul, det_adjugate, γ.prop, Fintype.card_fin]
      push_cast; simp only [det_intMat_cast]; rw [mul_one, inv_pow]
      rw [show (A.det : ℚ) * (A.det : ℚ) ^ (n - 1) = (A.det : ℚ) ^ n from by
        rw [← pow_succ']; congr 1; exact Nat.succ_pred_eq_of_pos (NeZero.pos n)]
      exact inv_mul_cancel₀ (pow_ne_zero n hAQ)
    set delta' : SpecialLinearGroup (Fin n) ℤ := ⟨delta'_mat, hdelta'_det⟩
    have h_int_eq' : delta'_mat * A = A * γ.val := by
      have ha : A.det • delta'_mat = A * γ.val * A.adjugate := by
        ext i j; simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, delta'_mat]
        exact Int.mul_ediv_cancel' (hdvd' i j)
      suffices h : A.det • (delta'_mat * A) = A.det • (A * γ.val) by
        ext i j; exact mul_left_cancel₀ hAdet_ne
          (by simpa [Matrix.smul_apply, smul_eq_mul] using congr_fun₂ h i j)
      rw [← smul_mul_assoc, ha, Matrix.mul_assoc, adjugate_mul, mul_smul_comm, Matrix.mul_one]
    have h_mat_eq' : (SLnZ_to_GLnQ n delta' * g).val =
        (g * SLnZ_to_GLnQ n γ).val := by
      show ((SLnZ_to_GLnQ n delta').val * g.val : Matrix _ _ ℚ) =
           (g.val * (SLnZ_to_GLnQ n γ).val : Matrix _ _ ℚ)
      rw [SLnZ_to_GLnQ_val, SLnZ_to_GLnQ_val, hA]
      rw [show (delta'_mat.map (Int.cast : ℤ → ℚ)) * (A.map _) =
          (delta'_mat * A).map (Int.cast : ℤ → ℚ) from by
        ext i j; simp [Matrix.mul_apply, Matrix.map_apply]]
      rw [show (A.map (Int.cast : ℤ → ℚ)) * (γ.val.map _) =
          (A * γ.val).map (Int.cast : ℤ → ℚ) from by
        ext i j; simp [Matrix.mul_apply, Matrix.map_apply]]
      rw [h_int_eq']
    have h_unit_eq' : SLnZ_to_GLnQ n delta' * g = g * SLnZ_to_GLnQ n γ :=
      Units.ext h_mat_eq'
    show g * SLnZ_to_GLnQ n γ * g⁻¹ ∈ (SLnZ_to_GLnQ n).range
    rw [MonoidHom.mem_range]
    exact ⟨delta', by
      have : SLnZ_to_GLnQ n delta' = g * SLnZ_to_GLnQ n γ * g⁻¹ := by
        rw [← h_unit_eq']; group
      rw [this, mul_assoc]⟩
  constructor
  · exact ne_zero_of_dvd_ne_zero hK_relIndex
      (Subgroup.relIndex_dvd_of_le_left H hK_le_gH)
  · rw [show H.relIndex (ConjAct.toConjAct g • H) =
        (ConjAct.toConjAct g⁻¹ • H).relIndex H from by
      have h1 : ConjAct.toConjAct g⁻¹ • (ConjAct.toConjAct g • H) = H := by
        rw [← MulAction.mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      have := Subgroup.relIndex_pointwise_smul (ConjAct.toConjAct g⁻¹) H
        (ConjAct.toConjAct g • H)
      rw [h1] at this; exact this.symm]
    exact ne_zero_of_dvd_ne_zero hK_relIndex
      (Subgroup.relIndex_dvd_of_le_left H hK_le_ginvH)

/-- The standard arithmetic group pair for number theory:
    `SL_n(ℤ) ≤ Δ ≤ commensurator(SL_n(ℤ))` in `GL_n(ℚ)`. -/
noncomputable def GL_pair : ArithmeticGroupPair (GL (Fin n) ℚ) where
  H := SLnZ_subgroup n
  Δ := posDetInt_submonoid n
  h₀ := SLnZ_le_posDetInt n
  h₁ := posDetInt_le_commensurator n

end Pair

section API

variable [NeZero n]

/-- The Hecke algebra for `GL_n`. -/
abbrev HeckeAlgebra := 𝕋 (GL_pair n) ℤ

scoped notation "Γₙ" => SLnZ_subgroup
scoped notation "Δₙ" => posDetInt_submonoid

/-- Embed an integer matrix with positive determinant into `Δ`. -/
noncomputable def intMat_to_delta (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    (GL_pair n).Δ := by
  have hne : (A.map (Int.cast : ℤ → ℚ)).det ≠ 0 := by
    rw [det_intMat_cast]; exact_mod_cast hdet.ne'
  have hval : (↑(GeneralLinearGroup.mkOfDetNeZero _ hne) : Matrix (Fin n) (Fin n) ℚ) =
      A.map (Int.cast : ℤ → ℚ) := rfl
  exact ⟨GeneralLinearGroup.mkOfDetNeZero _ hne,
    ⟨A, hval⟩,
    by rw [hval, det_intMat_cast]; exact_mod_cast hdet⟩

/-- Embed an integer matrix with positive determinant into a double coset. -/
noncomputable def intMat_to_T' (A : Matrix (Fin n) (Fin n) ℤ) (hdet : 0 < A.det) :
    HeckeRing.T' (GL_pair n) :=
  HeckeRing.T_mk _ (intMat_to_delta n A hdet)

end API

end HeckeRing.GLn
