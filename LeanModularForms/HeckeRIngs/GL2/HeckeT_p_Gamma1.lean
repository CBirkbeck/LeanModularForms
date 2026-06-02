/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanModularForms.HeckeRIngs.GL2.HeckeActionGeneral
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_GLpair

/-!
# Connection between `heckeT_p_fun` and `heckeSlash_gen (Gamma1_pair N)`

This file relates the explicit Hecke operator `T_p` defined via coset representatives in
`HeckeT_p.lean` to the abstract Hecke slash action `heckeSlash_gen (Gamma1_pair N)` from
`HeckeActionGeneral.lean`, at level `N` (not requiring SL₂(ℤ)-invariance), via the double
coset `D_p_Gamma1` and the diamond identity `slash_M_infty_eq_diamond_slash_T_p_lower`.

## References

* Diamond–Shurman, *A First Course in Modular Forms*, §5.2, Proposition 5.2.1
* Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions*, §3.4
-/

open Matrix Matrix.SpecialLinearGroup HeckeRing.GLn CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2

/-- The double coset `Γ₁(N) · diag(1,p) · Γ₁(N)` in `Gamma1_pair N`,
representing the Hecke operator `T_p` at level `N`. -/
noncomputable def D_p_Gamma1 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    HeckeRing.HeckeCoset (Gamma1_pair N) :=
  ⟦⟨diagMat 2 ![1, p], diag_1p_mem_Delta1 N p hp⟩⟧

/-- `diag(1,p)` as an element of `(Gamma1_pair N).Δ`. -/
noncomputable def diag_1p_delta_Gamma1 (N p : ℕ) [NeZero N] (hp : 0 < p) :
    (Gamma1_pair N).Δ :=
  ⟨diagMat 2 ![1, p], diag_1p_mem_Delta1 N p hp⟩

private lemma diag_1p_mul_mapGL_val (p : ℕ) (hp : 0 < p) (s : SL(2, ℤ)) :
    ((diagMat 2 ![1, p] : GL (Fin 2) ℚ) * (mapGL ℚ s)).val =
    !![((s.val 0 0 : ℤ) : ℚ), ((s.val 0 1 : ℤ) : ℚ);
       (p : ℚ) * (s.val 1 0 : ℤ), (p : ℚ) * (s.val 1 1 : ℤ)] := by
  have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) k := fun k ↦ by
    fin_cases k <;> simp [hp]
  rw [Units.val_mul, diagMat_val _ _ hpos]
  ext i j
  simp only [mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.diagonal_apply, algebraMap_int_eq]
  fin_cases i <;> fin_cases j <;> simp

/-- The natural number `a ∈ [0, N)` with `a ≡ p⁻¹ (mod N)`. -/
noncomputable def aInvOfCoprime (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) : ℕ :=
  (((ZMod.unitOfCoprime p hpN)⁻¹ : (ZMod N)ˣ) : ZMod N).val

/-- `aInvOfCoprime · p ≡ 1 (mod N)`. -/
lemma aInvOfCoprime_mul_eq_one (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    ((aInvOfCoprime N p hpN : ZMod N)) * (p : ZMod N) = 1 := by
  unfold aInvOfCoprime
  rw [ZMod.natCast_val, ZMod.cast_id, ← ZMod.coe_unitOfCoprime p hpN, ← Units.val_mul,
    inv_mul_cancel, Units.val_one]

/-- `N` divides `aInvOfCoprime · p - 1`. -/
lemma N_dvd_aInv_mul_p_sub_one (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (N : ℤ) ∣ ((aInvOfCoprime N p hpN : ℤ) * p - 1) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [aInvOfCoprime_mul_eq_one]; ring

/-- The integer `m` such that `aInvOfCoprime · p - 1 = N · m`. -/
noncomputable def mIdxOfCoprime (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) : ℤ :=
  ((aInvOfCoprime N p hpN : ℤ) * p - 1) / (N : ℤ)

/-- Bezout identity: `N · mIdxOfCoprime = aInvOfCoprime · p - 1`. -/
lemma N_mul_mIdx_eq (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (N : ℤ) * mIdxOfCoprime N p hpN = (aInvOfCoprime N p hpN : ℤ) * p - 1 := by
  unfold mIdxOfCoprime; rw [mul_comm (N : ℤ)]
  exact Int.ediv_mul_cancel (N_dvd_aInv_mul_p_sub_one N p hpN)

/-- `σ_p_specific = [[a, 1], [N·m, p]]` where `a · p − N · m = 1`, so the determinant
is `1` and the lower-right entry is exactly `p`. -/
noncomputable def sigma_p_specific (N p : ℕ) [NeZero N] (_hp : 0 < p)
    (hpN : Nat.Coprime p N) : SL(2, ℤ) :=
  ⟨!![(aInvOfCoprime N p hpN : ℤ), 1; (N : ℤ) * mIdxOfCoprime N p hpN, (p : ℤ)], by
    simp [det_fin_two]; linarith [N_mul_mIdx_eq N p hpN]⟩

@[simp] lemma sigma_p_specific_val (N p : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    (sigma_p_specific N p hp hpN : Matrix (Fin 2) (Fin 2) ℤ) =
    !![(aInvOfCoprime N p hpN : ℤ), 1; (N : ℤ) * mIdxOfCoprime N p hpN, (p : ℤ)] := rfl

/-- `σ_p_specific` lies in `Gamma0 N`: lower-left entry `N · m ≡ 0 mod N`. -/
lemma sigma_p_specific_mem_Gamma0 (N p : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) : sigma_p_specific N p hp hpN ∈ Gamma0 N := by
  simp [Gamma0_mem, sigma_p_specific]

/-- The `Gamma0MapUnits` of `σ_p_specific` is `(p : ZMod N)ˣ`. -/
lemma Gamma0MapUnits_sigma_p_specific (N p : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    Gamma0MapUnits ⟨sigma_p_specific N p hp hpN,
      sigma_p_specific_mem_Gamma0 N p hp hpN⟩ = ZMod.unitOfCoprime p hpN := by
  ext
  simp [Gamma0MapUnits_val, Gamma0Map, sigma_p_specific]

private lemma M_infty_det_pos (N p : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    (!![((aInvOfCoprime N p hpN : ℤ) : ℚ) * p, 1;
        ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) * p, p] :
        Matrix (Fin 2) (Fin 2) ℚ).det ≠ 0 := by
  rw [Matrix.det_fin_two_of]
  have hp_ne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h_det : ((aInvOfCoprime N p hpN : ℤ) : ℚ) * p * p -
      1 * (((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) * p) = p := by
    have h_q : ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) =
        (aInvOfCoprime N p hpN : ℤ) * p - 1 := by exact_mod_cast N_mul_mIdx_eq N p hpN
    rw [h_q]; ring
  rw [h_det]; exact hp_ne

/-- The `(p+1)`-th coset representative for the double coset `D_p_Gamma1`, defined
directly as the matrix `[[ap, 1], [Nmp, p]]` where `ap − Nm = 1`. It equals
`mapGL ℚ σ_p_specific · T_p_lower` (see `M_infty_eq_sigma_mul_T_p_lower`). -/
noncomputable def M_infty (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero
    !![((aInvOfCoprime N p hpN : ℤ) : ℚ) * p, 1;
       ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) * p, p]
    (M_infty_det_pos N p hp hpN)

@[simp] lemma M_infty_val (N p : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (M_infty N p hp hpN : Matrix (Fin 2) (Fin 2) ℚ) =
    !![((aInvOfCoprime N p hpN : ℤ) : ℚ) * p, 1;
       ((N : ℤ) * mIdxOfCoprime N p hpN : ℚ) * p, p] := rfl

private lemma gamma_prime_det (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (!![((aInvOfCoprime N p hpN : ℤ) * p), 1;
        ((N : ℤ) * mIdxOfCoprime N p hpN), 1] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  simp [det_fin_two]; linarith [N_mul_mIdx_eq N p hpN]

private lemma gamma_prime_mem_Gamma1 (N p : ℕ) [NeZero N] (hpN : Nat.Coprime p N) :
    (⟨!![((aInvOfCoprime N p hpN : ℤ) * p), 1;
         ((N : ℤ) * mIdxOfCoprime N p hpN), 1], gamma_prime_det N p hpN⟩ :
      SL(2, ℤ)) ∈ Gamma1 N := by
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · change (((aInvOfCoprime N p hpN : ℤ) * p : ℤ) : ZMod N) = 1
    push_cast; exact aInvOfCoprime_mul_eq_one N p hpN
  · change ((1 : ℤ) : ZMod N) = 1; simp
  · change (((N : ℤ) * mIdxOfCoprime N p hpN : ℤ) : ZMod N) = 0
    push_cast; rw [ZMod.natCast_self, zero_mul]

private lemma M_infty_eq_diag_mul_gamma_prime (N p : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    M_infty N p hp hpN = diagMat 2 ![1, p] *
      (mapGL ℚ (⟨!![((aInvOfCoprime N p hpN : ℤ) * p), 1;
           ((N : ℤ) * mIdxOfCoprime N p hpN), 1], gamma_prime_det N p hpN⟩ :
        SL(2, ℤ))) := by
  apply Units.ext
  rw [diag_1p_mul_mapGL_val p hp, M_infty_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

/-- `M_∞` equals the product `(mapGL ℚ σ_p_specific) · T_p_lower` in `GL₂(ℚ)`.
This is the form that gives the diamond-twisted slash identity. -/
lemma M_infty_eq_sigma_mul_T_p_lower (N p : ℕ) [NeZero N] (hp : 0 < p)
    (hpN : Nat.Coprime p N) :
    M_infty N p hp hpN =
    (mapGL ℚ (sigma_p_specific N p hp hpN)) * (T_p_lower p hp) := by
  apply Units.ext
  change (M_infty N p hp hpN : Matrix _ _ ℚ) =
    (mapGL ℚ (sigma_p_specific N p hp hpN) * T_p_lower p hp : GL _ ℚ).val
  rw [M_infty_val, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, mapGL_coe_matrix,
      T_p_lower, GeneralLinearGroup.mkOfDetNeZero, sigma_p_specific_val]

/-- The diamond identity: for any modular form `f`, slashing `f` by `M_∞` equals
slashing `(⟨p⟩ f)` by `T_p_lower`. This ties the abstract sum (which uses `M_∞`)
to the explicit `T_p` formula (which uses `(⟨p⟩ f) ∣ T_p_lower`). -/
lemma slash_M_infty_eq_diamond_slash_T_p_lower {N : ℕ} [NeZero N] (k : ℤ) (p : ℕ)
    (hp : 0 < p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑f) ∣[k] (M_infty N p hp hpN : GL (Fin 2) ℚ) =
    ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
      (T_p_lower p hp : GL (Fin 2) ℚ) := by
  rw [M_infty_eq_sigma_mul_T_p_lower]
  set σ_p_pkg : ↥(Gamma0 N) := ⟨sigma_p_specific N p hp hpN,
    sigma_p_specific_mem_Gamma0 N p hp hpN⟩
  have hdia : diamondOp k (ZMod.unitOfCoprime p hpN) =
      diamondOpAux k σ_p_pkg :=
    diamondOp_eq_diamondOpAux k _ σ_p_pkg (Gamma0MapUnits_sigma_p_specific N p hp hpN)
  rw [hdia]
  have hgl : glMap (mapGL ℚ (sigma_p_specific N p hp hpN)) =
      mapGL ℝ (σ_p_pkg : SL(2, ℤ)) := by
    apply Units.ext; ext i j
    simp only [glMap, GeneralLinearGroup.map]
    exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ
      ((σ_p_pkg : SL(2, ℤ)) i j)).symm
  change ⇑f ∣[k] glMap ((mapGL ℚ (sigma_p_specific N p hp hpN)) * T_p_lower p hp) =
    (⇑f ∣[k] mapGL ℝ (σ_p_pkg : SL(2, ℤ))) ∣[k] glMap (T_p_lower p hp)
  rw [map_mul, hgl, ← SlashAction.slash_mul]

/-- **Bridge lemma**: the explicit Γ₁(N)-level `heckeT_p_fun` sum coincides with the
naive double-coset sum (upper-triangular reps plus `M_∞`), for any modular form. The
diamond twist inside `heckeT_p_fun` is exactly absorbed by the diamond identity at `M_∞`. -/
lemma heckeT_p_fun_eq_coset_sum {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ}
    (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : ModularForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_p_fun k p hp hpN f =
    heckeT_p_ut k p hp.pos (⇑f) + (⇑f) ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) := by
  unfold heckeT_p_fun
  congr 1
  rw [slash_M_infty_eq_diamond_slash_T_p_lower k p hp.pos hpN f]

private lemma Gamma1_pair_H_entry_is_int {N : ℕ} [NeZero N] (g : GL (Fin 2) ℚ)
    (hg : g ∈ (Gamma1_pair N).H) (i j : Fin 2) : ∃ n : ℤ, g.val i j = (n : ℚ) :=
  let ⟨s, _, hs⟩ := Subgroup.mem_map.mp hg
  ⟨s.val i j, by rw [← hs]; simp [mapGL_coe_matrix, algebraMap_int_eq]⟩

private lemma adj_T_p_upper_val (p : ℕ) (hp : 0 < p) (b : ℕ) :
    (GL_adjugate (T_p_upper p hp b : GL (Fin 2) ℚ)).val =
    !![(p : ℚ), -(b : ℚ); 0, 1] := by
  rw [GL_adjugate_val, T_p_upper_coe, Matrix.adjugate_fin_two_of, neg_zero]

private lemma adj_T_p_upper_inv_val (p : ℕ) (hp : 0 < p) (b : ℕ) :
    ((GL_adjugate (T_p_upper p hp b : GL (Fin 2) ℚ))⁻¹).val =
    !![1 / (p : ℚ), (b : ℚ) / (p : ℚ); 0, 1] := by
  have : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [Matrix.coe_units_inv, adj_T_p_upper_val p hp b,
    Matrix.inv_def, Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.det_fin_two_of] <;> field_simp

private lemma adj_upper_inv_mul_upper_val (p : ℕ) (hp : 0 < p) (b₁ b₂ : ℕ) :
    ((GL_adjugate (T_p_upper p hp b₁ : GL (Fin 2) ℚ))⁻¹ *
      GL_adjugate (T_p_upper p hp b₂ : GL (Fin 2) ℚ)).val =
    !![(1 : ℚ), ((b₁ : ℤ) - (b₂ : ℤ) : ℤ) / (p : ℚ); 0, 1] := by
  have : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [Units.val_mul, adj_T_p_upper_inv_val p hp b₁, adj_T_p_upper_val p hp b₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, sub_div] <;> field_simp <;> ring

/-- `(Gamma1_pair N).H ≤ (GL_pair 2).H` (i.e., Γ₁(N) image is in SL₂(ℤ) image). -/
lemma Gamma1_pair_H_le_GL_pair_H (N : ℕ) [NeZero N] :
    (Gamma1_pair N).H ≤ (GL_pair 2).H := fun _ hg ↦
  let ⟨s, _, hs⟩ := Subgroup.mem_map.mp hg; ⟨s, hs⟩

private lemma diagMat_1p_val (p : ℕ) (hp : 0 < p) :
    (diagMat 2 ![1, p] : GL (Fin 2) ℚ).val =
    !![(1 : ℚ), 0; 0, (p : ℚ)] := by
  have hpos : ∀ k : Fin 2, 0 < (![1, p] : Fin 2 → ℕ) k := fun k ↦ by
    fin_cases k <;> simp [hp]
  rw [diagMat_val _ _ hpos]
  ext k l
  fin_cases k <;> fin_cases l <;> simp

private lemma diagMat_1p_inv_val (p : ℕ) (hp : 0 < p) :
    ((diagMat 2 ![1, p] : GL (Fin 2) ℚ)⁻¹).val =
    !![(1 : ℚ), 0; 0, (1 : ℚ) / p] := by
  have : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [Matrix.coe_units_inv, diagMat_1p_val p hp, Matrix.inv_def, Matrix.adjugate_fin_two,
    Ring.inverse_eq_inv']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.det_fin_two_of] <;> field_simp

private lemma conj_diag_val_entry (p : ℕ) (hp : 0 < p) (s : SL(2, ℤ)) (i j : Fin 2) :
    (((diagMat 2 ![1, p] : GL (Fin 2) ℚ))⁻¹ *
      (mapGL ℚ s) * (diagMat 2 ![1, p])).val i j =
    (![![((s.val 0 0 : ℤ) : ℚ), (p : ℚ) * (s.val 0 1 : ℤ)],
       ![((s.val 1 0 : ℤ) : ℚ) / (p : ℚ), ((s.val 1 1 : ℤ) : ℚ)]]) i j := by
  have : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  rw [Units.val_mul, Units.val_mul, diagMat_1p_inv_val p hp, diagMat_1p_val p hp]
  simp only [mapGL_coe_matrix, Matrix.mul_apply, Fin.sum_univ_two,
    algebraMap_int_eq]
  fin_cases i <;> fin_cases j <;> simp <;> field_simp

private lemma h_quot_imp_adj_mem_Gamma1 (N p : ℕ) [NeZero N] (hp : 0 < p)
    (a₁ : GL (Fin 2) ℚ) (ha₁ : a₁ ∈ (Gamma1_pair N).H)
    (c₁ : GL (Fin 2) ℚ) (hc₁ : c₁ ∈ (Gamma1_pair N).H)
    (a₂ : GL (Fin 2) ℚ) (ha₂ : a₂ ∈ (Gamma1_pair N).H)
    (c₂ : GL (Fin 2) ℚ) (hc₂ : c₂ ∈ (Gamma1_pair N).H)
    (g₁ g₂ : GL (Fin 2) ℚ)
    (heq₁ : GL_adjugate g₁ = a₁ * (HeckeCoset.rep (D_p_Gamma1 N p hp) : GL _ ℚ) * c₁)
    (heq₂ : GL_adjugate g₂ = a₂ * (HeckeCoset.rep (D_p_Gamma1 N p hp) : GL _ ℚ) * c₂)
    (hquot : (⟦(⟨a₁, ha₁⟩ : (Gamma1_pair N).H)⟧ :
        decompQuot (Gamma1_pair N) (HeckeCoset.rep (D_p_Gamma1 N p hp))) =
      ⟦⟨a₂, ha₂⟩⟧) :
    (GL_adjugate g₁)⁻¹ * GL_adjugate g₂ ∈ (Gamma1_pair N).H := by
  rw [heq₁, heq₂]
  have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact hquot)
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hrel
  simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, map_inv, inv_inv,
    Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have h_prod : (a₁ * ↑(HeckeCoset.rep (D_p_Gamma1 N p hp)) * c₁)⁻¹ *
      (a₂ * ↑(HeckeCoset.rep (D_p_Gamma1 N p hp)) * c₂) =
      c₁⁻¹ * ((↑(HeckeCoset.rep (D_p_Gamma1 N p hp)))⁻¹ * (a₁⁻¹ * a₂) *
        ↑(HeckeCoset.rep (D_p_Gamma1 N p hp))) * c₂ := by group
  rw [h_prod]
  exact (Gamma1_pair N).H.mul_mem
    ((Gamma1_pair N).H.mul_mem ((Gamma1_pair N).H.inv_mem hc₁) hrel) hc₂

end HeckeRing.GL2
