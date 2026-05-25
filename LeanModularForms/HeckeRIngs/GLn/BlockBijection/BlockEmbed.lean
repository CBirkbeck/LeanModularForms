/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GLn.BlockBijection.AbstractHeckePair

/-!
# Block Embedding Bijection: `slSuccEmbed`/`blockEmbedGL` and dimension reduction

The block embeddings `slSuccEmbed`/`slSuccEmbed_H`/`blockEmbedGL`/`slPredEmbed`,
their homomorphism/stabilizer properties, dimension reduction, and the
`decompQuot_rep_to_diagMat` bridge (Shimura §3.2, Proposition 3.15).
-/

open Matrix Subgroup.Commensurable Pointwise HeckeRing DoubleCoset
open Matrix.SpecialLinearGroup

open scoped Pointwise

namespace HeckeRing.GLn

variable {m : ℕ} [NeZero m]

/-! ### Block embedding helpers for `slSuccEmbed` -/

section SlSuccEmbedHelpers

/-- Block embedding `SL_{k+1}(ℤ) → SL_{k+2}(ℤ)` via `M ↦ 1 ⊕ M`. -/
noncomputable def slSuccEmbed {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    SpecialLinearGroup (Fin (k + 2)) ℤ := by
  let e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  refine ⟨(fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0
    (M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)).submatrix e e, ?_⟩
  rw [det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, one_mul, M.prop]

private lemma slSuccEmbed_val_eq {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    (slSuccEmbed M).1 = (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0
      (M : Matrix _ _ ℤ)).submatrix
      (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
        |>.toEquiv.trans finSumFinEquiv.symm)
      (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
        |>.toEquiv.trans finSumFinEquiv.symm) := rfl

private lemma slSuccEmbed_mul {k : ℕ} (A B : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    slSuccEmbed (A * B) = slSuccEmbed A * slSuccEmbed B := by
  apply Subtype.ext
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
      |>.toEquiv.trans finSumFinEquiv.symm)
  have lhs : (slSuccEmbed (A * B)).1 =
    (fromBlocks 1 0 0 ((A : Matrix _ _ ℤ) * (B : Matrix _ _ ℤ))).submatrix e e := by
    rw [slSuccEmbed_val_eq]; ext i j
    simp only [SpecialLinearGroup.coe_mul, submatrix_apply]; rfl
  have rhs : (slSuccEmbed A * slSuccEmbed B).1 =
    (fromBlocks 1 0 0 (A : Matrix _ _ ℤ)).submatrix e e *
    (fromBlocks 1 0 0 (B : Matrix _ _ ℤ)).submatrix e e := by
    simp only [SpecialLinearGroup.coe_mul]; rw [slSuccEmbed_val_eq, slSuccEmbed_val_eq]
  rw [lhs, rhs,
    show fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 ((A.1) * (B.1)) =
      fromBlocks 1 0 0 A.1 * fromBlocks 1 0 0 B.1 from by
      rw [fromBlocks_multiply]; simp]
  exact (submatrix_mul_equiv _ _ e e e).symm

private lemma slSuccEmbed_one {k : ℕ} :
    slSuccEmbed (1 : SpecialLinearGroup (Fin (k + 1)) ℤ) = 1 := by
  apply Subtype.ext
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
      |>.toEquiv.trans finSumFinEquiv.symm)
  rw [slSuccEmbed_val_eq]; simp only [SpecialLinearGroup.coe_one, fromBlocks_one]
  ext i j; simp only [submatrix_apply, one_apply, Equiv.apply_eq_iff_eq]

private lemma slSuccEmbed_inv {k : ℕ} (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    slSuccEmbed M⁻¹ = (slSuccEmbed M)⁻¹ := by
  apply mul_left_cancel (a := slSuccEmbed M)
  rw [mul_inv_cancel, ← slSuccEmbed_mul, mul_inv_cancel, slSuccEmbed_one]

/-- Extract the SL preimage of an element of `(GL_pair n).H = SLnZ_subgroup n`. -/
noncomputable def toSL {n : ℕ} [NeZero n] (σ : (GL_pair n).H) :
    SpecialLinearGroup (Fin n) ℤ :=
  (Classical.indefiniteDescription _ σ.2).val

lemma toSL_spec {n : ℕ} [NeZero n] (σ : (GL_pair n).H) :
    mapGL ℚ (toSL σ) = (σ : GL (Fin n) ℚ) :=
  (Classical.indefiniteDescription _ σ.2).prop

private lemma mapGL_injective (n : ℕ) :
    Function.Injective
      (mapGL ℚ : SpecialLinearGroup (Fin n) ℤ →* GL (Fin n) ℚ) := by
  intro a b h
  have h_mat : (a : Matrix (Fin n) (Fin n) ℤ) = (b : Matrix (Fin n) (Fin n) ℤ) := by
    ext i j
    have hij := congr_arg (fun g ↦ (g : Matrix (Fin n) (Fin n) ℚ) i j)
      (show (mapGL ℚ a : Matrix _ _ ℚ) = (mapGL ℚ b : Matrix _ _ ℚ) from
        congr_arg Units.val h)
    simp only [mapGL_coe_matrix, algebraMap_int_eq] at hij
    exact Int.cast_injective hij
  exact Subtype.ext h_mat

/-! ### H-level block embedding -/

/-- Lift `slSuccEmbed` to the Hecke pair subgroup: `(GL_pair (k+1)).H → (GL_pair (k+2)).H`. -/
noncomputable def slSuccEmbed_H {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    (GL_pair (k + 2)).H := by
  refine ⟨mapGL ℚ (slSuccEmbed (toSL σ)), ?_⟩
  show (mapGL ℚ (slSuccEmbed (toSL σ)) : GL (Fin (k + 2)) ℚ) ∈ SLnZ_subgroup (k + 2)
  rw [MonoidHom.mem_range]
  exact ⟨slSuccEmbed (toSL σ), rfl⟩

private lemma slSuccEmbed_H_val {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) = mapGL ℚ (slSuccEmbed (toSL σ)) := rfl

private lemma slSuccEmbed_H_mul {k : ℕ} (σ₁ σ₂ : (GL_pair (k + 1)).H) :
    slSuccEmbed_H (σ₁ * σ₂) = slSuccEmbed_H σ₁ * slSuccEmbed_H σ₂ := by
  apply Subtype.ext
  show (mapGL ℚ (slSuccEmbed (toSL (σ₁ * σ₂))) : GL _ ℚ) =
    (mapGL ℚ (slSuccEmbed (toSL σ₁)) : GL _ ℚ) * mapGL ℚ (slSuccEmbed (toSL σ₂))
  have htoSL : toSL (σ₁ * σ₂) = toSL σ₁ * toSL σ₂ := by
    apply mapGL_injective (k + 1)
    rw [map_mul, toSL_spec, toSL_spec, toSL_spec]
    exact Subgroup.coe_mul _ _ _
  rw [htoSL, slSuccEmbed_mul, map_mul]

private lemma slSuccEmbed_H_one {k : ℕ} :
    slSuccEmbed_H (1 : (GL_pair (k + 1)).H) = 1 := by
  apply Subtype.ext
  show (mapGL ℚ (slSuccEmbed (toSL 1)) : GL _ ℚ) = 1
  have htoSL : toSL (1 : (GL_pair (k + 1)).H) = 1 :=
    mapGL_injective (k + 1) (by rw [toSL_spec]; simp [map_one])
  rw [htoSL, slSuccEmbed_one, map_one]

private lemma slSuccEmbed_injective {k : ℕ} :
    Function.Injective (slSuccEmbed : SpecialLinearGroup (Fin (k + 1)) ℤ →
      SpecialLinearGroup (Fin (k + 2)) ℤ) := by
  intro A B h
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)
      |>.toEquiv.trans finSumFinEquiv.symm)
  have hSub : (slSuccEmbed A).1 = (slSuccEmbed B).1 := congr_arg Subtype.val h
  rw [slSuccEmbed_val_eq, slSuccEmbed_val_eq] at hSub
  have hFromBlocks :
      (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 A.1) = fromBlocks 1 0 0 B.1 := by
    have hSub' := congr_arg (fun M : Matrix (Fin (k + 2)) (Fin (k + 2)) ℤ ↦
      M.submatrix e.symm e.symm) hSub
    simp only at hSub'
    have h1 : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 A.1) =
        ((fromBlocks 1 0 0 A.1).submatrix e e).submatrix e.symm e.symm := by
      simp [submatrix_submatrix, Equiv.self_comp_symm]
    have h2 : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℤ) 0 0 B.1) =
        ((fromBlocks 1 0 0 B.1).submatrix e e).submatrix e.symm e.symm := by
      simp [submatrix_submatrix, Equiv.self_comp_symm]
    rw [h1, h2, hSub']
  have hAB : A.1 = B.1 := by
    have := congr_arg Matrix.toBlocks₂₂ hFromBlocks
    simpa [toBlocks_fromBlocks₂₂] using this
  exact Subtype.ext hAB

private lemma slSuccEmbed_H_inv {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    slSuccEmbed_H σ⁻¹ = (slSuccEmbed_H σ)⁻¹ := by
  apply mul_left_cancel (a := slSuccEmbed_H σ)
  rw [mul_inv_cancel, ← slSuccEmbed_H_mul, mul_inv_cancel, slSuccEmbed_H_one]

private lemma slSuccEmbed_H_injective {k : ℕ} :
    Function.Injective (slSuccEmbed_H : (GL_pair (k + 1)).H → (GL_pair (k + 2)).H) := by
  intro σ₁ σ₂ h
  have hval : (slSuccEmbed_H σ₁ : GL (Fin (k + 2)) ℚ) =
      (slSuccEmbed_H σ₂ : GL (Fin (k + 2)) ℚ) :=
    congr_arg (fun x : (GL_pair (k + 2)).H ↦ (x : GL (Fin (k + 2)) ℚ)) h
  rw [slSuccEmbed_H_val, slSuccEmbed_H_val] at hval
  have hSL : slSuccEmbed (toSL σ₁) = slSuccEmbed (toSL σ₂) :=
    mapGL_injective (k + 2) hval
  have htoSL : toSL σ₁ = toSL σ₂ := slSuccEmbed_injective hSL
  apply Subtype.ext
  rw [← toSL_spec σ₁, ← toSL_spec σ₂, htoSL]

end SlSuccEmbedHelpers

/-! ### Dimension reduction: `decompQuot(m+1, rep(T(1,d))) ≃ decompQuot(m, rep(T(d)))` -/

omit [NeZero m] in
private lemma block_conj_identity {k : ℕ}
    (d : Fin (k + 1) → ℕ) (hd : ∀ i, 0 < d i)
    (M N : SpecialLinearGroup (Fin (k + 1)) ℤ)
    (hMN : (diagMat (k + 1) d)⁻¹ * mapGL ℚ M * diagMat (k + 1) d = mapGL ℚ N) :
    (diagMat (k + 2) (Fin.cons 1 d))⁻¹ * mapGL ℚ (slSuccEmbed M) *
      diagMat (k + 2) (Fin.cons 1 d) = mapGL ℚ (slSuccEmbed N) := by
  have hcons_pos : ∀ i : Fin (k + 2), 0 < (Fin.cons 1 d : Fin (k + 2) → ℕ) i := by
    intro i; refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [Fin.cons_zero]
    · rw [Fin.cons_succ]; exact hd j
  set D' := diagMat (k + 2) (Fin.cons 1 d) with hD'_def
  set D := diagMat (k + 1) d with hD_def
  have hMN_mul : mapGL ℚ M * D = D * mapGL ℚ N := by
    have h1 := congr_arg (D * ·) hMN
    simp only [← mul_assoc, mul_inv_cancel, one_mul] at h1
    exact h1
  suffices hmul : mapGL ℚ (slSuccEmbed M) * D' = D' * mapGL ℚ (slSuccEmbed N) by
    have h1 := congr_arg (D'⁻¹ * ·) hmul
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h1
    exact h1
  apply Units.ext; ext i j
  simp only [Units.val_mul, mul_apply, hD'_def, diagMat_val _ _ hcons_pos, diagonal_apply,
    mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j
  all_goals simp only [mapGL_coe_matrix, algebraMap_int_eq, Fin.cons_zero, Fin.cons_succ,
    Nat.cast_one]
  · simp [SpecialLinearGroup.map, RingHom.mapMatrix_apply, slSuccEmbed_val_eq,
      submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv,
      Fin.addCases]
  · simp [SpecialLinearGroup.map, RingHom.mapMatrix_apply, slSuccEmbed_val_eq,
      submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv,
      Fin.addCases]
  · simp [SpecialLinearGroup.map, RingHom.mapMatrix_apply, slSuccEmbed_val_eq,
      submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv,
      Fin.addCases]
  · have h4 := congr_arg Units.val hMN_mul
    simp only [Units.val_mul] at h4
    have h4_entry := congr_fun (congr_fun h4 i') j'
    simp only [hD_def, diagMat_val _ _ hd, mul_apply, diagonal_apply, mul_ite, mul_zero,
      ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      ite_true] at h4_entry
    convert h4_entry using 2 <;>
      simp [mapGL_coe_matrix, algebraMap_int_eq, SpecialLinearGroup.map,
        RingHom.mapMatrix_apply, Matrix.map_apply, slSuccEmbed_val_eq,
        submatrix_apply, fromBlocks, Matrix.of_apply, Fin.castOrderIso,
        finSumFinEquiv, Fin.addCases, Fin.subNat]

/-- Stabilizer preservation for `slSuccEmbed_H` at the `diagMat` level: if `σ ∈ H_{k+1}`
stabilizes `diagMat(a)` under conjugation, then `slSuccEmbed_H σ ∈ H_{k+2}` stabilizes
`diagMat(cons 1 a)`. -/
lemma slSuccEmbed_H_stab_diagMat {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (hσ : (diagMat (k + 1) a)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a ∈
        (GL_pair (k + 1)).H) :
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ * (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨ν, hν⟩ := hσ
  have h_hyp : (diagMat (k + 1) a)⁻¹ * mapGL ℚ (toSL σ) * diagMat (k + 1) a =
      mapGL ℚ ν := by
    rw [toSL_spec σ]; exact hν.symm
  have h_block := block_conj_identity a ha (toSL σ) ν h_hyp
  rw [slSuccEmbed_H_val]
  exact ⟨slSuccEmbed ν, h_block.symm⟩


/-- Positivity lifts through `Fin.cons 1`: if every `a i` is positive, so is every
`(Fin.cons 1 a) i`. -/
lemma cons_one_pos {k : ℕ} {a : Fin (k + 1) → ℕ} (ha : ∀ i, 0 < a i) :
    ∀ i : Fin (k + 2), 0 < (Fin.cons 1 a : Fin (k + 2) → ℕ) i := by
  intro i; refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp [Fin.cons_zero]
  · rw [Fin.cons_succ]; exact ha j

private def diagConjWitnessMat {n : ℕ} (c : Fin n → ℕ)
    (N : SpecialLinearGroup (Fin n) ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j ↦ (N.1 i j * (c j : ℤ)) / (c i : ℤ)

private lemma diagConjWitnessMat_entry_cast {n : ℕ} (c : Fin n → ℕ)
    (N : SpecialLinearGroup (Fin n) ℤ)
    (h_dvd : ∀ i j, (c i : ℤ) ∣ N.1 i j * (c j : ℤ)) (i j : Fin n) :
    (diagConjWitnessMat c N i j : ℚ) * (c i : ℤ) = (N.1 i j : ℚ) * (c j : ℤ) := by
  have hmul : diagConjWitnessMat c N i j * (c i : ℤ) = N.1 i j * (c j : ℤ) :=
    Int.ediv_mul_cancel (h_dvd i j)
  exact_mod_cast congr_arg (fun z : ℤ ↦ (z : ℚ)) hmul

private lemma diagConjWitnessMat_mat_eq {n : ℕ} (c : Fin n → ℕ) (hc : ∀ i, 0 < c i)
    (N : SpecialLinearGroup (Fin n) ℤ)
    (h_dvd : ∀ i j, (c i : ℤ) ∣ N.1 i j * (c j : ℤ)) :
    (mapGL ℚ N : Matrix _ _ ℚ) * (diagMat n c : Matrix _ _ ℚ) =
      (diagMat n c : Matrix _ _ ℚ) *
        ((diagConjWitnessMat c N).map (Int.cast : ℤ → ℚ)) := by
  ext i j
  simp only [diagMat_val _ _ hc, mul_apply, diagonal_apply, mul_ite, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    mapGL_coe_matrix, algebraMap_int_eq]
  show ((N.1 i j : ℤ) : ℚ) * (c j : ℚ) = (c i : ℚ) * ((diagConjWitnessMat c N i j : ℤ) : ℚ)
  have he := diagConjWitnessMat_entry_cast c N h_dvd i j
  push_cast at he ⊢
  linarith [he]

private lemma diagConjWitnessMat_det_one {n : ℕ} (c : Fin n → ℕ) (hc : ∀ i, 0 < c i)
    (N : SpecialLinearGroup (Fin n) ℤ)
    (h_dvd : ∀ i j, (c i : ℤ) ∣ N.1 i j * (c j : ℤ)) :
    (diagConjWitnessMat c N).det = 1 := by
  set D : GL (Fin n) ℚ := diagMat n c with hD_def
  have hD_det_ne : (D.val).det ≠ 0 := by
    rw [hD_def, diagMat_det _ _ hc]
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ by exact_mod_cast (hc i).ne'
  have hdet := congr_arg Matrix.det (diagConjWitnessMat_mat_eq c hc N h_dvd)
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hN1 : ((mapGL ℚ N).val).det = 1 := by
    rw [show ((mapGL ℚ N).val).det = (N.val.map (Int.cast : ℤ → ℚ)).det by
      rw [mapGL_coe_matrix]; simp [algebraMap_int_eq], ← Int.cast_det, N.2]; simp
  rw [hN1, one_mul] at hdet
  have hcast : (((diagConjWitnessMat c N).det : ℤ) : ℚ) =
      ((diagConjWitnessMat c N).map (Int.cast : ℤ → ℚ)).det := Int.cast_det _
  have : (((diagConjWitnessMat c N).det : ℤ) : ℚ) = (1 : ℚ) := by
    rw [hcast]; exact mul_left_cancel₀ hD_det_ne (by rw [mul_one]; linarith [hdet])
  exact_mod_cast this

/-- Sufficient direction for diag-conjugation membership: if `N ∈ SL(k+2, ℤ)` satisfies the
entry-wise divisibility `(Fin.cons 1 a) i ∣ N i j * (Fin.cons 1 a) j`, then the conjugate
`D⁻¹ * mapGL ℚ N * D` lies in `(GL_pair (k+2)).H`, where `D := diagMat (Fin.cons 1 a)`. -/
lemma diagMat_cons_one_conj_mapGL_mem_H_of_entry_dvd
    {k : ℕ} (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (N : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_dvd : ∀ i j : Fin (k + 2),
      ((Fin.cons 1 a : Fin (k + 2) → ℕ) i : ℤ) ∣
        N.1 i j * ((Fin.cons 1 a : Fin (k + 2) → ℕ) j : ℤ)) :
    (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
      (mapGL ℚ N : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H := by
  set c : Fin (k + 2) → ℕ := Fin.cons 1 a with hc_def
  have hc_pos : ∀ i, 0 < c i := cons_one_pos ha
  set D : GL (Fin (k + 2)) ℚ := diagMat (k + 2) c with hD_def
  set M : SpecialLinearGroup (Fin (k + 2)) ℤ :=
    ⟨diagConjWitnessMat c N, diagConjWitnessMat_det_one c hc_pos N h_dvd⟩ with hM_def
  refine ⟨M, ?_⟩
  have h_units : (mapGL ℚ N : GL (Fin (k + 2)) ℚ) * D = D * mapGL ℚ M := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, show (mapGL ℚ M).val =
      (diagConjWitnessMat c N).map (Int.cast : ℤ → ℚ) by rw [mapGL_coe_matrix]; rfl]
    exact diagConjWitnessMat_mat_eq c hc_pos N h_dvd
  have h1 := congr_arg (D⁻¹ * ·) h_units
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at h1
  exact h1.symm



/-- The block-embedding map on `decompQuot` at the `diagMat_delta` level: `slSuccEmbed_H`
descends to a map `decompQuot (GL_pair (k+1)) (diagMat_delta (k+1) a) →
decompQuot (GL_pair (k+2)) (diagMat_delta (k+2) (Fin.cons 1 a))`. -/
noncomputable def decompQuot_slSuccEmbed_diagMat {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) :
    decompQuot (GL_pair (k + 1)) (diagMat_delta (k + 1) a) →
    decompQuot (GL_pair (k + 2)) (diagMat_delta (k + 2) (Fin.cons 1 a)) := by
  refine Quotient.map' slSuccEmbed_H ?_
  intro σ₁ σ₂ h_rel
  rw [QuotientGroup.leftRel_apply] at h_rel ⊢
  have h_mul : (slSuccEmbed_H σ₁)⁻¹ * slSuccEmbed_H σ₂ =
      slSuccEmbed_H (σ₁⁻¹ * σ₂) := by
    rw [← slSuccEmbed_H_inv, ← slSuccEmbed_H_mul]
  rw [h_mul]
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at h_rel ⊢
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h_rel ⊢
  rw [show ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) : GL (Fin (k + 1)) ℚ) =
        diagMat (k + 1) a from diagMat_delta_val (k + 1) a ha] at h_rel
  rw [show ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
        GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) from
      diagMat_delta_val (k + 2) (Fin.cons 1 a) (cons_one_pos ha)]
  exact slSuccEmbed_H_stab_diagMat a ha (σ₁⁻¹ * σ₂) h_rel

/-! ### Block entry extraction lemmas for `slSuccEmbed` -/

lemma slSuccEmbed_val_zero_zero {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    (slSuccEmbed τ).val 0 0 = 1 := by
  rw [slSuccEmbed_val_eq]
  simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]

lemma slSuccEmbed_val_zero_succ {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) (j : Fin (k + 1)) :
    (slSuccEmbed τ).val 0 j.succ = 0 := by
  rw [slSuccEmbed_val_eq]
  simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]

lemma slSuccEmbed_val_succ_zero {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) (i : Fin (k + 1)) :
    (slSuccEmbed τ).val i.succ 0 = 0 := by
  rw [slSuccEmbed_val_eq]
  simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]

lemma slSuccEmbed_val_succ_succ {k : ℕ}
    (τ : SpecialLinearGroup (Fin (k + 1)) ℤ) (i j : Fin (k + 1)) :
    (slSuccEmbed τ).val i.succ j.succ = τ.val i j := by
  rw [slSuccEmbed_val_eq]
  simp only [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
        Fin.castOrderIso, finSumFinEquiv, Fin.addCases]
  simp [Fin.subNat]

private lemma slSuccEmbed_conj_flip {k : ℕ}
    (a : Fin (k + 1) → ℕ)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hν : mapGL ℚ ν = (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a)) :
    (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν := by
  rw [hν]; group

private lemma slSuccEmbed_conj_entry {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (i j : Fin (k + 2)) :
    ((slSuccEmbed (toSL σ)).val i j : ℚ) * ((Fin.cons 1 a : Fin (k + 2) → ℕ) j : ℚ) =
      ((Fin.cons 1 a : Fin (k + 2) → ℕ) i : ℚ) * (ν.val i j : ℚ) := by
  have hcons_pos := cons_one_pos ha
  have h := congr_arg (fun (x : GL (Fin (k + 2)) ℚ) ↦ (x : Matrix _ _ ℚ) i j) hflip
  simp only [Units.val_mul, Matrix.mul_apply, slSuccEmbed_H_val,
             mapGL_coe_matrix, algebraMap_int_eq, diagMat_val _ _ hcons_pos,
             Matrix.diagonal_apply, mul_ite, mul_zero, ite_mul, zero_mul,
             Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
             SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
             Matrix.map_apply] at h
  exact h

private lemma slSuccEmbed_conj_ν_zero_zero {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    ν.val 0 0 = 1 := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip 0 0
  rw [slSuccEmbed_val_zero_zero] at h
  simp only [Fin.cons_zero, Nat.cast_one, mul_one, one_mul] at h
  exact_mod_cast h.symm

private lemma slSuccEmbed_conj_ν_zero_succ {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (j : Fin (k + 1)) :
    ν.val 0 j.succ = 0 := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip 0 j.succ
  rw [slSuccEmbed_val_zero_succ] at h
  simp only [Int.cast_zero, zero_mul, Fin.cons_zero, Nat.cast_one, one_mul] at h
  exact_mod_cast h.symm

private lemma slSuccEmbed_conj_ν_succ_zero {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (i : Fin (k + 1)) :
    ν.val i.succ 0 = 0 := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip i.succ 0
  rw [slSuccEmbed_val_succ_zero] at h
  simp only [Int.cast_zero, Fin.cons_zero, Nat.cast_one, mul_one, Fin.cons_succ] at h
  have hai : (0 : ℚ) < (a i : ℚ) := by exact_mod_cast ha i
  have hν_zero : (ν.val i.succ 0 : ℚ) = 0 := by
    have h' : (a i : ℚ) * (ν.val i.succ 0 : ℚ) = 0 := h.symm
    exact (mul_eq_zero.mp h').resolve_left hai.ne'
  exact_mod_cast hν_zero

private lemma slSuccEmbed_conj_ν_succ_succ {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) (i j : Fin (k + 1)) :
    ((toSL σ).val i j : ℚ) * (a j : ℚ) = (a i : ℚ) * (ν.val i.succ j.succ : ℚ) := by
  have h := slSuccEmbed_conj_entry a ha σ ν hflip i.succ j.succ
  rw [slSuccEmbed_val_succ_succ] at h
  simp only [Fin.cons_succ] at h
  exact h

private lemma ν_bottomBlock_det {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    Matrix.det (M := (fun i j : Fin (k + 1) ↦ ν.val i.succ j.succ :
      Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ)) = 1 := by
  set ν'_mat : Matrix (Fin (k + 1)) (Fin (k + 1)) ℤ :=
    fun i j ↦ ν.val i.succ j.succ with hν'_mat_def
  have h00 := slSuccEmbed_conj_ν_zero_zero a ha σ ν hflip
  have h_col : ∀ i : Fin (k + 1), ν.val i.succ 0 = 0 :=
    fun i ↦ slSuccEmbed_conj_ν_succ_zero a ha σ ν hflip i
  have h_expand := Matrix.det_succ_column ν.val 0
  rw [Fin.sum_univ_succ] at h_expand
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, h00] at h_expand
  have h_zero_sum :
      (∑ x : Fin (k + 1), (-1 : ℤ) ^ (x.succ : Fin (k + 2)).val * ν.val x.succ 0 *
        (ν.val.submatrix x.succ.succAbove (Fin.succAbove 0)).det) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [h_col]; ring
  rw [h_zero_sum, add_zero] at h_expand
  rw [ν.prop] at h_expand
  have h_sub : ν'_mat = ν.val.submatrix (Fin.succAbove 0) (Fin.succAbove 0) := by
    ext i j; simp only [hν'_mat_def, Matrix.submatrix_apply, Fin.succAbove_zero]
  show ν'_mat.det = 1
  rw [h_sub]
  exact h_expand.symm

private noncomputable def ν_bottomBlock {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    SpecialLinearGroup (Fin (k + 1)) ℤ :=
  ⟨fun i j ↦ ν.val i.succ j.succ, ν_bottomBlock_det a ha σ ν hflip⟩

private lemma ν_bottomBlock_mapGL_eq {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (ν : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (hflip : (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) =
      diagMat (k + 2) (Fin.cons 1 a) * mapGL ℚ ν) :
    (diagMat (k + 1) a)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a =
      mapGL ℚ (ν_bottomBlock a ha σ ν hflip) := by
  have h_flip_k1 : (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a =
      diagMat (k + 1) a * mapGL ℚ (ν_bottomBlock a ha σ ν hflip) := by
    apply Units.ext
    ext i j
    simp only [Units.val_mul, Matrix.mul_apply, diagMat_val _ _ ha,
               Matrix.diagonal_apply, mul_ite, ite_mul, zero_mul, mul_zero,
               Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true,
               mapGL_coe_matrix, algebraMap_int_eq,
               SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
               Matrix.map_apply]
    have h_σ : (σ : GL (Fin (k + 1)) ℚ).val i j = ((toSL σ).val i j : ℚ) := by
      have : mapGL ℚ (toSL σ) = σ := toSL_spec σ
      have h' := congr_arg (fun (x : GL _ ℚ) ↦ x.val i j) this
      simp only [mapGL_coe_matrix, algebraMap_int_eq,
                 SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
                 Matrix.map_apply] at h'
      exact h'.symm
    rw [h_σ]
    exact slSuccEmbed_conj_ν_succ_succ a ha σ ν hflip i j
  have : (diagMat (k + 1) a)⁻¹ * ((σ : GL _ ℚ) * diagMat (k + 1) a) =
      (diagMat (k + 1) a)⁻¹ * (diagMat (k + 1) a * mapGL ℚ (ν_bottomBlock a ha σ ν hflip)) :=
    congr_arg ((diagMat (k + 1) a)⁻¹ * ·) h_flip_k1
  rw [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul] at this
  exact this

private lemma slSuccEmbed_H_stab_diagMat_converse {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 1)).H)
    (hσ' : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ *
        (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) * diagMat (k + 2) (Fin.cons 1 a) ∈
      (GL_pair (k + 2)).H) :
    (diagMat (k + 1) a)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a ∈
      (GL_pair (k + 1)).H := by
  obtain ⟨ν, hν⟩ := hσ'
  have hflip := slSuccEmbed_conj_flip a σ ν hν
  exact ⟨ν_bottomBlock a ha σ ν hflip,
    (ν_bottomBlock_mapGL_eq a ha σ ν hflip).symm⟩

/-- The block-embedding map `decompQuot_slSuccEmbed_diagMat` is injective. -/
lemma decompQuot_slSuccEmbed_diagMat_injective {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) :
    Function.Injective (decompQuot_slSuccEmbed_diagMat a ha) := by
  refine Quotient.ind₂ ?_
  intro σ₁ σ₂ h
  change (⟦slSuccEmbed_H σ₁⟧ : decompQuot _ _) = ⟦slSuccEmbed_H σ₂⟧ at h
  rw [Quotient.eq] at h
  change QuotientGroup.leftRel _ (slSuccEmbed_H σ₁) (slSuccEmbed_H σ₂) at h
  rw [QuotientGroup.leftRel_apply] at h
  have h_mul : (slSuccEmbed_H σ₁)⁻¹ * slSuccEmbed_H σ₂ =
      slSuccEmbed_H (σ₁⁻¹ * σ₂) := by
    rw [← slSuccEmbed_H_inv, ← slSuccEmbed_H_mul]
  rw [h_mul] at h
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def] at h
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv] at h
  rw [show ((diagMat_delta (k + 2) (Fin.cons 1 a) : (GL_pair (k + 2)).Δ) :
        GL (Fin (k + 2)) ℚ) = diagMat (k + 2) (Fin.cons 1 a) from
      diagMat_delta_val (k + 2) (Fin.cons 1 a) (cons_one_pos ha)] at h
  have h_stab := slSuccEmbed_H_stab_diagMat_converse a ha (σ₁⁻¹ * σ₂) h
  apply Quotient.sound
  change QuotientGroup.leftRel _ σ₁ σ₂
  rw [QuotientGroup.leftRel_apply,
      Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  rw [show ((diagMat_delta (k + 1) a : (GL_pair (k + 1)).Δ) : GL (Fin (k + 1)) ℚ) =
        diagMat (k + 1) a from diagMat_delta_val (k + 1) a ha]
  exact h_stab

/-! ### GL-level block embedding -/

private noncomputable def blockEmbedGL {k : ℕ} (X : GL (Fin (k + 1)) ℚ) :
    GL (Fin (k + 2)) ℚ := by
  refine GeneralLinearGroup.mkOfDetNeZero
    ((Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val).submatrix
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm)
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm)) ?_
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  have h_det_prod : X.val.det * (X⁻¹ : GL (Fin (k + 1)) ℚ).val.det = 1 := by
    rw [← Matrix.det_mul]
    have h_mul : X.val * (X⁻¹ : GL _ ℚ).val = 1 := by exact_mod_cast X.mul_inv
    rw [h_mul]; exact Matrix.det_one
  intro h; rw [h, zero_mul] at h_det_prod; exact one_ne_zero h_det_prod.symm

private lemma blockEmbedGL_val_eq {k : ℕ} (X : GL (Fin (k + 1)) ℚ) :
    (blockEmbedGL X).val = (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val).submatrix
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm)
      ((Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans
        finSumFinEquiv.symm) := rfl

private lemma blockEmbedGL_mul {k : ℕ} (X Y : GL (Fin (k + 1)) ℚ) :
    blockEmbedGL (X * Y) = blockEmbedGL X * blockEmbedGL Y := by
  apply Units.ext
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  have lhs : (blockEmbedGL (X * Y)).val =
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 (X.val * Y.val)).submatrix e e := by
    rw [blockEmbedGL_val_eq, Units.val_mul]
  have rhs : (blockEmbedGL X * blockEmbedGL Y).val =
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val).submatrix e e *
      (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 Y.val).submatrix e e := by
    rw [Units.val_mul, blockEmbedGL_val_eq, blockEmbedGL_val_eq]
  rw [lhs, rhs,
    show Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 (X.val * Y.val) =
        Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 X.val *
        Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0 Y.val from by
      rw [Matrix.fromBlocks_multiply]; simp]
  exact (Matrix.submatrix_mul_equiv _ _ e e e).symm

private lemma blockEmbedGL_one {k : ℕ} :
    blockEmbedGL (1 : GL (Fin (k + 1)) ℚ) = 1 := by
  apply Units.ext
  rw [blockEmbedGL_val_eq]
  set e : Fin (k + 2) ≃ Fin 1 ⊕ Fin (k + 1) :=
    (Fin.castOrderIso (show k + 1 + 1 = 1 + (k + 1) by omega)).toEquiv.trans finSumFinEquiv.symm
  show (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℚ) 0 0
        ((1 : GL (Fin (k + 1)) ℚ).val)).submatrix e e = (1 : GL (Fin (k + 2)) ℚ).val
  rw [show ((1 : GL (Fin (k + 1)) ℚ).val) = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℚ) from rfl,
      Matrix.fromBlocks_one]
  ext i j
  simp [Matrix.submatrix_apply, Matrix.one_apply]

private lemma blockEmbedGL_inv {k : ℕ} (X : GL (Fin (k + 1)) ℚ) :
    blockEmbedGL X⁻¹ = (blockEmbedGL X)⁻¹ := by
  apply mul_left_cancel (a := blockEmbedGL X)
  rw [mul_inv_cancel, ← blockEmbedGL_mul, mul_inv_cancel, blockEmbedGL_one]

private lemma blockEmbedGL_diagMat {k : ℕ} (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) :
    blockEmbedGL (diagMat (k + 1) a) = diagMat (k + 2) (Fin.cons 1 a) := by
  apply Units.ext
  rw [blockEmbedGL_val_eq]
  rw [diagMat_val _ _ ha, diagMat_val _ _ (cons_one_pos ha)]
  ext i j
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j <;>
    simp [Matrix.submatrix_apply, Matrix.diagonal_apply, Matrix.fromBlocks,
          Matrix.of_apply, Fin.castOrderIso, finSumFinEquiv, Fin.addCases,
          Fin.subNat, Fin.succ_inj, Fin.cons_succ,
          (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]

private lemma blockEmbedGL_mapGL_eq {k : ℕ} (ν : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    blockEmbedGL (mapGL ℚ ν) = mapGL ℚ (slSuccEmbed ν) := by
  apply Units.ext
  rw [blockEmbedGL_val_eq]
  ext i j
  simp only [Matrix.submatrix_apply, mapGL_coe_matrix, algebraMap_int_eq,
             SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j
  · rw [slSuccEmbed_val_zero_zero]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply]
  · rw [slSuccEmbed_val_zero_succ]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply]
  · rw [slSuccEmbed_val_succ_zero]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply]
  · rw [slSuccEmbed_val_succ_succ]
    simp [Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Matrix.fromBlocks,
          Matrix.of_apply, Fin.subNat]

private lemma blockEmbedGL_slSuccEmbed_H_eq {k : ℕ} (σ : (GL_pair (k + 1)).H) :
    blockEmbedGL (σ : GL (Fin (k + 1)) ℚ) = (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) := by
  rw [show (σ : GL (Fin (k + 1)) ℚ) = mapGL ℚ (toSL σ) from (toSL_spec σ).symm,
    blockEmbedGL_mapGL_eq, slSuccEmbed_H_val]

/-! ### Block-form predecessor `slPredEmbed` -/

private noncomputable def slPredEmbed {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0) :
    SpecialLinearGroup (Fin (k + 1)) ℤ :=
  ⟨M.1.submatrix Fin.succ Fin.succ, by
    have h_det_M : M.1.det = 1 := M.2
    have h_laplace := Matrix.det_succ_column_zero M.1
    rw [Fin.sum_univ_succ] at h_laplace
    simp only [Fin.val_zero, pow_zero, h_diag, one_mul, Fin.succAbove_zero] at h_laplace
    have h_tail : (∑ i : Fin (k + 1),
        (-1 : ℤ) ^ ((i.succ : Fin (k + 2)) : ℕ) * M.1 i.succ 0 *
          (M.1.submatrix (i.succ).succAbove Fin.succ).det) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [h_col i]; ring
    rw [h_tail, add_zero] at h_laplace
    rw [h_det_M] at h_laplace
    exact h_laplace.symm⟩

private lemma slPredEmbed_val_eq {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0) :
    (slPredEmbed M h_diag h_col).1 = M.1.submatrix Fin.succ Fin.succ := rfl

private lemma slPredEmbed_val_apply {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0)
    (i j : Fin (k + 1)) :
    (slPredEmbed M h_diag h_col).1 i j = M.1 i.succ j.succ := rfl

private lemma slPredEmbed_slSuccEmbed_eq {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 1)) ℤ) :
    slPredEmbed (slSuccEmbed M) (slSuccEmbed_val_zero_zero M)
      (fun i ↦ slSuccEmbed_val_succ_zero M i) = M := by
  apply Subtype.ext
  ext i j
  rw [slPredEmbed_val_apply]
  exact slSuccEmbed_val_succ_succ M i j

private lemma slSuccEmbed_slPredEmbed_eq {k : ℕ}
    (M : SpecialLinearGroup (Fin (k + 2)) ℤ)
    (h_diag : M.1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), M.1 i.succ 0 = 0)
    (h_row : ∀ j : Fin (k + 1), M.1 0 j.succ = 0) :
    slSuccEmbed (slPredEmbed M h_diag h_col) = M := by
  apply Subtype.ext
  ext i j
  refine Fin.cases ?_ (fun i' ↦ ?_) i <;> refine Fin.cases ?_ (fun j' ↦ ?_) j
  · rw [slSuccEmbed_val_zero_zero, h_diag]
  · rw [slSuccEmbed_val_zero_succ, h_row j']
  · rw [slSuccEmbed_val_succ_zero, h_col i']
  · rw [slSuccEmbed_val_succ_succ]; rfl

private noncomputable def slPredEmbed_H {k : ℕ}
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0) :
    (GL_pair (k + 1)).H := by
  refine ⟨mapGL ℚ (slPredEmbed (toSL σ) h_diag h_col), ?_⟩
  show (mapGL ℚ (slPredEmbed (toSL σ) h_diag h_col) : GL (Fin (k + 1)) ℚ) ∈
    SLnZ_subgroup (k + 1)
  exact ⟨slPredEmbed (toSL σ) h_diag h_col, rfl⟩

private lemma slPredEmbed_H_val {k : ℕ}
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0) :
    (slPredEmbed_H σ h_diag h_col : GL (Fin (k + 1)) ℚ) =
      mapGL ℚ (slPredEmbed (toSL σ) h_diag h_col) := rfl

private lemma slSuccEmbed_H_slPredEmbed_H_eq {k : ℕ}
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0)
    (h_row : ∀ j : Fin (k + 1), (toSL σ).1 0 j.succ = 0) :
    slSuccEmbed_H (slPredEmbed_H σ h_diag h_col) = σ := by
  apply Subtype.ext
  show (mapGL ℚ (slSuccEmbed (toSL (slPredEmbed_H σ h_diag h_col))) :
      GL (Fin (k + 2)) ℚ) = (σ : GL (Fin (k + 2)) ℚ)
  have h_toSL_eq : toSL (slPredEmbed_H σ h_diag h_col) =
      slPredEmbed (toSL σ) h_diag h_col := by
    apply mapGL_injective (k + 1)
    rw [toSL_spec (slPredEmbed_H σ h_diag h_col), slPredEmbed_H_val]
  rw [h_toSL_eq, slSuccEmbed_slPredEmbed_eq _ h_diag h_col h_row]
  exact toSL_spec σ

private lemma slPredEmbed_H_stab_diagMat {k : ℕ}
    (a : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i)
    (σ : (GL_pair (k + 2)).H)
    (h_diag : (toSL σ).1 0 0 = 1)
    (h_col : ∀ i : Fin (k + 1), (toSL σ).1 i.succ 0 = 0)
    (h_row : ∀ j : Fin (k + 1), (toSL σ).1 0 j.succ = 0)
    (hσ : (diagMat (k + 2) (Fin.cons 1 a))⁻¹ * (σ : GL (Fin (k + 2)) ℚ) *
        diagMat (k + 2) (Fin.cons 1 a) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 1) a)⁻¹ *
        (slPredEmbed_H σ h_diag h_col : GL (Fin (k + 1)) ℚ) *
        diagMat (k + 1) a ∈ (GL_pair (k + 1)).H := by
  have h_eq : (σ : GL (Fin (k + 2)) ℚ) =
      (slSuccEmbed_H (slPredEmbed_H σ h_diag h_col) : GL (Fin (k + 2)) ℚ) := by
    rw [slSuccEmbed_H_slPredEmbed_H_eq σ h_diag h_col h_row]
  rw [h_eq] at hσ
  exact slSuccEmbed_H_stab_diagMat_converse a ha (slPredEmbed_H σ h_diag h_col) hσ

private lemma blockEmbedGL_injective {k : ℕ} :
    Function.Injective (blockEmbedGL : GL (Fin (k + 1)) ℚ → GL (Fin (k + 2)) ℚ) := by
  intro X Y h
  apply Units.ext
  ext i j
  have h_val : (blockEmbedGL X).val i.succ j.succ = (blockEmbedGL Y).val i.succ j.succ :=
    congr_arg (fun (u : GL (Fin (k + 2)) ℚ) ↦ u.val i.succ j.succ) h
  have h_X_unfold : (blockEmbedGL X).val i.succ j.succ = X.val i j := by
    rw [blockEmbedGL_val_eq]
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
          Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat]
  have h_Y_unfold : (blockEmbedGL Y).val i.succ j.succ = Y.val i j := by
    rw [blockEmbedGL_val_eq]
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
          Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat]
  rw [h_X_unfold, h_Y_unfold] at h_val
  exact h_val

private lemma blockEmbedGL_mem_H_imp {k : ℕ} (h : GL (Fin (k + 1)) ℚ)
    (hh : blockEmbedGL h ∈ (GL_pair (k + 2)).H) :
    h ∈ (GL_pair (k + 1)).H := by
  obtain ⟨ν, hν⟩ := hh
  have hν_val : ∀ p q : Fin (k + 2),
      ((ν.1 p q : ℤ) : ℚ) = (blockEmbedGL h).val p q := by
    intro p q
    have := congr_arg (fun (u : GL (Fin (k + 2)) ℚ) ↦ u.val p q) hν
    simpa [mapGL_coe_matrix, algebraMap_int_eq, Matrix.map_apply] using this
  have h_ν_diag : ν.1 0 0 = 1 := by
    have h0 := hν_val 0 0
    rw [blockEmbedGL_val_eq] at h0
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
      Fin.castOrderIso, finSumFinEquiv, Fin.addCases] at h0
    exact_mod_cast h0
  have h_ν_col : ∀ i : Fin (k + 1), ν.1 i.succ 0 = 0 := by
    intro i
    have hi := hν_val i.succ 0
    rw [blockEmbedGL_val_eq] at hi
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
      Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat] at hi
    exact_mod_cast hi
  have h_ν_row : ∀ j : Fin (k + 1), ν.1 0 j.succ = 0 := by
    intro j
    have hj := hν_val 0 j.succ
    rw [blockEmbedGL_val_eq] at hj
    simp [Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.of_apply,
      Fin.castOrderIso, finSumFinEquiv, Fin.addCases, Fin.subNat] at hj
    exact_mod_cast hj
  set ν_m := slPredEmbed ν h_ν_diag h_ν_col with hν_m_def
  refine ⟨ν_m, ?_⟩
  apply blockEmbedGL_injective
  have h_section : slSuccEmbed ν_m = ν :=
    slSuccEmbed_slPredEmbed_eq ν h_ν_diag h_ν_col h_ν_row
  rw [blockEmbedGL_mapGL_eq, h_section, hν]

/-- Block-form fiber descent (converse of `slSuccEmbed_H_fiber_transfer`): if the lifted
dim-`k+2` H-membership condition holds for the `slSuccEmbed_H` images of `σ_m, τ_m`, then
the corresponding dim-`k+1` condition holds for `σ_m, τ_m`. -/
lemma slSuccEmbed_H_fiber_transfer_converse {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (σ_m τ_m : (GL_pair (k + 1)).H)
    (h : (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
         (slSuccEmbed_H σ_m : GL (Fin (k + 2)) ℚ) *
         diagMat (k + 2) (Fin.cons 1 a) *
         (slSuccEmbed_H τ_m : GL (Fin (k + 2)) ℚ) *
         diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H) :
    (diagMat (k + 1) c)⁻¹ * (σ_m : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a *
      (τ_m : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b ∈ (GL_pair (k + 1)).H := by
  have h_eq : (diagMat (k + 2) (Fin.cons 1 c))⁻¹ *
      (slSuccEmbed_H σ_m : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) *
      (slSuccEmbed_H τ_m : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) =
    blockEmbedGL ((diagMat (k + 1) c)⁻¹ * (σ_m : GL (Fin (k + 1)) ℚ) *
      diagMat (k + 1) a * (τ_m : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b) := by
    rw [blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul,
      blockEmbedGL_inv, blockEmbedGL_diagMat _ hc, blockEmbedGL_diagMat _ ha,
      blockEmbedGL_diagMat _ hb, ← blockEmbedGL_slSuccEmbed_H_eq σ_m,
      ← blockEmbedGL_slSuccEmbed_H_eq τ_m]
  rw [h_eq] at h
  exact blockEmbedGL_mem_H_imp _ h

/-- Fiber-condition block transfer (the five-factor key lemma for the ≥ direction): if the
dim-`k+1` expression `(diagMat c)⁻¹ · σ · diagMat a · τ · diagMat b` lies in `H_{k+1}`, then
the analogous dim-`k+2` expression with `Fin.cons 1` diagonals and `slSuccEmbed_H` lifts of
`σ, τ` lies in `H_{k+2}`. -/
lemma slSuccEmbed_H_fiber_transfer {k : ℕ}
    (a b c : Fin (k + 1) → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i)
    (σ τ : (GL_pair (k + 1)).H)
    (h : (diagMat (k + 1) c)⁻¹ * (σ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) a *
         (τ : GL (Fin (k + 1)) ℚ) * diagMat (k + 1) b ∈ (GL_pair (k + 1)).H) :
    (diagMat (k + 2) (Fin.cons 1 c))⁻¹ * (slSuccEmbed_H σ : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 a) * (slSuccEmbed_H τ : GL (Fin (k + 2)) ℚ) *
      diagMat (k + 2) (Fin.cons 1 b) ∈ (GL_pair (k + 2)).H := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨slSuccEmbed ν, ?_⟩
  have h_img := congr_arg (blockEmbedGL (k := k)) hν
  rw [blockEmbedGL_mapGL_eq] at h_img
  rw [blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul, blockEmbedGL_mul,
      blockEmbedGL_inv, blockEmbedGL_diagMat _ hc, blockEmbedGL_diagMat _ ha,
      blockEmbedGL_diagMat _ hb, blockEmbedGL_slSuccEmbed_H_eq σ,
      blockEmbedGL_slSuccEmbed_H_eq τ] at h_img
  exact h_img

/-- Right-coset / H-membership pivot for the `diagMat` fiber: the fiber-pair right-coset
condition `{σ · diagMat a} · {τ · diagMat b} · H = {diagMat c} · H` is equivalent to the
H-membership condition `(diagMat c)⁻¹ · σ · diagMat a · τ · diagMat b ∈ H`. -/
lemma fiber_diagMat_iff_mem_H {n : ℕ} [NeZero n]
    (a b c : Fin n → ℕ) (_ : ∀ i, 0 < a i) (_ : ∀ i, 0 < b i) (_ : ∀ i, 0 < c i)
    (σ τ : (GL_pair n).H) :
    (({(σ : GL (Fin n) ℚ) * diagMat n a} : Set _) *
        {(τ : GL (Fin n) ℚ) * diagMat n b} *
        ((GL_pair n).H : Set (GL (Fin n) ℚ)) =
        {(diagMat n c : GL (Fin n) ℚ)} * ((GL_pair n).H : Set (GL (Fin n) ℚ))) ↔
    (diagMat n c)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a *
        (τ : GL (Fin n) ℚ) * diagMat n b ∈ (GL_pair n).H := by
  rw [Set.singleton_mul_singleton]
  constructor
  · intro h_eq
    have hmem : (σ : GL (Fin n) ℚ) * diagMat n a *
        ((τ : GL (Fin n) ℚ) * diagMat n b) ∈
        ({(diagMat n c : GL (Fin n) ℚ)} : Set _) *
          ((GL_pair n).H : Set (GL (Fin n) ℚ)) := by
      rw [← h_eq]; exact ⟨_, rfl, 1, (GL_pair n).H.one_mem, by simp⟩
    obtain ⟨_, hd_eq, h, hh, hprod⟩ := hmem
    rw [Set.mem_singleton_iff] at hd_eq
    subst hd_eq
    simp only at hprod
    have h_eq_factor : (diagMat n c)⁻¹ *
        ((σ : GL (Fin n) ℚ) * diagMat n a *
          ((τ : GL (Fin n) ℚ) * diagMat n b)) = h := by
      rw [← hprod]; group
    rw [show (diagMat n c)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a *
          (τ : GL (Fin n) ℚ) * diagMat n b =
        (diagMat n c)⁻¹ * ((σ : GL (Fin n) ℚ) * diagMat n a *
          ((τ : GL (Fin n) ℚ) * diagMat n b)) by group, h_eq_factor]
    exact hh
  · intro h_mem
    set h_elt := (diagMat n c)⁻¹ * (σ : GL (Fin n) ℚ) * diagMat n a *
        (τ : GL (Fin n) ℚ) * diagMat n b
    ext y
    constructor
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt * k, (GL_pair n).H.mul_mem h_mem hk, ?_⟩
      simp only [h_elt]; group
    · rintro ⟨_, rfl, k, hk, rfl⟩
      refine ⟨_, rfl, h_elt⁻¹ * k, (GL_pair n).H.mul_mem ((GL_pair n).H.inv_mem h_mem) hk, ?_⟩
      simp only [h_elt]; group

/-- `decompQuot` is invariant under changing the Δ-element when the underlying GL-values
agree (the stabilizer depends only on the GL-value, not on the Δ-membership proof). -/
noncomputable def decompQuot_val_equiv {n : ℕ} [NeZero n]
    (g₁ g₂ : (GL_pair n).Δ) (h : (g₁ : GL (Fin n) ℚ) = g₂) :
    decompQuot (GL_pair n) g₁ ≃ decompQuot (GL_pair n) g₂ :=
  Equiv.cast (congrArg _ (Subtype.ext h))

/-- Strip H-factors from `rep(T_diag a)` to get `decompQuot(rep) ≃ decompQuot(diagMat_delta)`. -/
noncomputable def decompQuot_rep_to_diagMat {n : ℕ} [NeZero n]
    (a : Fin n → ℕ) (ha : ∀ i, 0 < a i) :
    decompQuot (GL_pair n) (HeckeCoset.rep (T_diag a)) ≃
    decompQuot (GL_pair n) (diagMat_delta n a) := by
  let L_data := Classical.indefiniteDescription _ (T_diag_rep_decompose a ha)
  let L : (GL_pair n).H := ⟨L_data.val, L_data.prop.1⟩
  let R_data := Classical.indefiniteDescription _ L_data.prop.2
  let R : (GL_pair n).H := ⟨R_data.val, R_data.prop.1⟩
  have hLR : (HeckeCoset.rep (T_diag a) : GL (Fin n) ℚ) =
    ↑L * diagMat n a * ↑R := R_data.prop.2
  have hmem : (↑L * diagMat n a * ↑R : GL (Fin n) ℚ) ∈ (GL_pair n).Δ :=
    hLR ▸ (T_diag a).rep.2
  have hD_eq : diagMat_delta n a =
      ⟨diagMat n a, diagMat_mem_posDetInt n a ha⟩ :=
    Subtype.ext (diagMat_delta_val n a ha)
  exact (decompQuot_val_equiv _ ⟨_, hmem⟩ hLR).trans
    (hD_eq ▸ decompQuot_double_H_equiv (GL_pair n)
      ⟨diagMat n a, diagMat_mem_posDetInt n a ha⟩ L R hmem)


end HeckeRing.GLn
