/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheory.TileBridge

/-!
# Hecke adjoint theory: concrete `Option (Fin p)` projective T_p tile family.

Fifth module of the split of `AdjointTheoryPetersson`. Covers the Phase E3
concrete `Option (Fin p)` projective T_p tile family and the resulting
symmetric-form adjoint identity for `petN`.
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

/-! ### Phase E3 — concrete `Option (Fin p)` projective T_p tile family -/

/-- **Phase E3 — rational `Option (Fin p)` T_p tile family.** -/
noncomputable def α_T_p_Q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    Option (Fin p) → GL (Fin 2) ℚ
  | none => M_infty N p hp.pos hpN
  | some b => T_p_upper p hp.pos b.val

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E3 — concrete `Option (Fin p)` T_p tile family in `GL(2, ℝ)⁺`.** -/
noncomputable def α_T_p_GLPos
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    Option (Fin p) → GL(2, ℝ)⁺
  | none => ⟨glMap (M_infty N p hp.pos hpN), glMap_M_infty_det_pos N p hp.pos hpN⟩
  | some b => ⟨glMap (T_p_upper p hp.pos b.val), glMap_T_p_upper_det_pos p hp.pos b.val⟩

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E3 — concrete `Option (Fin p)` T_p tile family in `PSL(2, ℝ)`.** -/
noncomputable def α_T_p_PSL_R
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    Option (Fin p) → PSL(2, ℝ) :=
  fun i ↦ GLPos_to_PSL_R_term (α_T_p_GLPos p hp hpN i)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — set-level transfer from `α_T_p_PSL_R` to `α_T_p_GLPos`.** -/
theorem α_T_p_PSL_R_smul_set
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) (S : Set ℍ) :
    (α_T_p_PSL_R p hp hpN i • S : Set ℍ) =
      ((α_T_p_GLPos p hp hpN i : GL(2, ℝ)⁺) • S : Set ℍ) :=
  GLPos_to_PSL_R_term_smul_set _ _

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — set-level transfer from `α_T_p_GLPos` to underlying matrix.** -/
theorem α_T_p_GLPos_smul_set_val
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) (S : Set ℍ) :
    ((α_T_p_GLPos p hp hpN i : GL(2, ℝ)⁺) • S : Set ℍ) =
      (((α_T_p_GLPos p hp hpN i : GL(2, ℝ)⁺) : GL (Fin 2) ℝ) • S : Set ℍ) :=
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — set-level match form for `α_T_p_PSL_R i • S`.** -/
theorem α_T_p_PSL_R_smul_set_eq_match_GL
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) (S : Set ℍ) :
    (α_T_p_PSL_R p hp hpN i • S : Set ℍ) =
      ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
            S : Set ℍ) := by
  rw [α_T_p_PSL_R_smul_set, α_T_p_GLPos_smul_set_val]
  cases i <;> rfl

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — pairwise AE-disjointness for the projective T_p family.** -/
theorem aedisjoint_pairwise_T_p_family_PSL_R
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    (↑(Finset.univ : Finset (Option (Fin p))) : Set (Option (Fin p))).Pairwise
      (fun i j ↦ AEDisjoint μ_hyp
          (α_T_p_PSL_R p hp hpN i • (Gamma1_fundDomain_PSL N : Set ℍ))
          (α_T_p_PSL_R p hp hpN j • (Gamma1_fundDomain_PSL N : Set ℍ))) := by
  intro i hi j hj hij
  rw [α_T_p_PSL_R_smul_set_eq_match_GL,
      α_T_p_PSL_R_smul_set_eq_match_GL]
  exact aedisjoint_pairwise_T_p_family p hp hpN hi hj hij

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Phase E4 — biUnion bridge: projective T_p tiles ↔ GL-tile match form.** -/
theorem α_T_p_PSL_R_biUnion_eq_match_GL_biUnion
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (S : Set ℍ) :
    (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
      α_T_p_PSL_R p hp hpN i • S) =
    (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
      ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
            S : Set ℍ)) := by
  refine Set.iUnion_congr ?_
  intro i
  refine Set.iUnion_congr ?_
  intro _
  rw [α_T_p_PSL_R_smul_set, α_T_p_GLPos_smul_set_val]
  cases i <;> rfl

/-- The determinant of the real `GL₂` image of `T_p_lower` is positive. -/
private theorem glMap_T_p_lower_det_pos (p : ℕ) (hp : Nat.Prime p) :
    0 < (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ).det.val :=
  glMap_det_pos_of_rat_det_pos _ (T_p_lower_det_pos p hp.pos)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD
    {N : ℕ} [NeZero N] (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : ∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      NullMeasurableSet ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (h_int_per : ∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp)
    (hfi : IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) ⇑g =
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  let α : Option (Fin p) → GL (Fin 2) ℝ := fun i ↦ match i with
    | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
    | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)
  have hset_eq : (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α i • (Gamma1_fundDomain_PSL N : Set ℍ)) =
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) := by
    refine Set.iUnion_congr ?_
    intro i
    refine Set.iUnion_congr ?_
    intro _
    cases i <;> rfl
  have hfi_compact : IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
    rw [hset_eq]; exact hfi
  have hmain : peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ i ∈ (Finset.univ : Finset (Option (Fin p))), ⇑f ∣[k] α i) ⇑g =
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α i • (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
    apply peterssonInner_T_p_family_sum_slashes_eq_aggregate_of_integrable
      (s := Finset.univ) (α := α) (f := f) (g := g)
      (g' := ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
    · intro i _
      cases i with
      | none => exact glMap_M_infty_det_pos N p hp.pos hpN
      | some b => exact glMap_T_p_upper_det_pos p hp.pos b.val
    · intro i _
      cases i with
      | none => exact slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower p hp hpN g
      | some b => exact slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower p hp.pos b.val g
    · exact hm
    · exact aedisjoint_pairwise_T_p_family p hp hpN
    · exact h_int_per
    · exact hfi_compact
  rw [← hset_eq]
  exact hmain

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD_PSL_R
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : ∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      NullMeasurableSet
        (α_T_p_PSL_R p hp hpN i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (h_int_per : ∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp)
    (hfi : IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α_T_p_PSL_R p hp hpN i • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) :
    peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) ⇑g =
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        α_T_p_PSL_R p hp hpN i • (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  have h_biUnion := α_T_p_PSL_R_biUnion_eq_match_GL_biUnion (N := N) p hp hpN
    (Gamma1_fundDomain_PSL N : Set ℍ)
  have hm_GL : ∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      NullMeasurableSet ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
    intro i hi
    have h_per := α_T_p_PSL_R_smul_set_eq_match_GL p hp hpN i
      (Gamma1_fundDomain_PSL N : Set ℍ)
    rw [← h_per]
    exact hm i hi
  have hfi_GL : IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ((match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))) μ_hyp := by
    rw [← h_biUnion]; exact hfi
  rw [h_biUnion]
  exact peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD
    p hp hpN f g hm_GL h_int_per hfi_GL

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane MeasureTheory in
/-- **Phase G specialized — projective shifted FD-decomposition for the
T_p Hecke family.** -/
theorem T_p_PSL_R_FD_finite_index_decomp_shifted
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) :
    IsFundamentalDomain
      ((ConjAct.toConjAct (α_T_p_PSL_R p hp hpN i) •
        ((Gamma_p_α (N := N) (α_T_p_Q p hp hpN i)).map SL2Z_to_PSL2R)) :
          Subgroup PSL(2, ℝ))
      (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) (α_T_p_Q p hp hpN i)).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
        (α_T_p_PSL_R p hp hpN i *
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp :=
  Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted (α_T_p_Q p hp hpN i)
    (α_T_p_GLPos p hp hpN i)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase H — T_p specialized: shifted FD set as `α_T_p_PSL_R i • Γ_p(α_i)-FD`.** -/
theorem T_p_PSL_R_FD_finite_index_decomp_shifted_eq_smul
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) :
    (⋃ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
            (((Gamma_p_α (N := N) (α_T_p_Q p hp hpN i)).map SL2Z_to_PSL2R).subgroupOf
              ((Gamma1 N).map SL2Z_to_PSL2R)),
      (α_T_p_PSL_R p hp hpN i *
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) =
    α_T_p_PSL_R p hp hpN i •
      Gamma_p_α_fundDomain_PSL (N := N) (α_T_p_Q p hp hpN i) :=
  Gamma_p_α_PSL_R_FD_finite_index_decomp_shifted_eq_smul
    (α_T_p_Q p hp hpN i) (α_T_p_GLPos p hp hpN i)

open CongruenceSubgroup Pointwise UpperHalfPlane MeasureTheory in
/-- **Phase I — per-`i` aggregate Petersson identity over the projective
shifted Γ_p(α_i)-FD.** -/
theorem peterssonInner_T_p_PSL_R_shifted_eq_sum_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (i : Option (Fin p)) (f g : ℍ → ℂ)
    (hm : ∀ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) (α_T_p_Q p hp hpN i)).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
      NullMeasurableSet ((α_T_p_PSL_R p hp hpN i *
        ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp)
    (hd : Pairwise (fun q₁ q₂ : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) (α_T_p_Q p hp hpN i)).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)) =>
      AEDisjoint μ_hyp
        ((α_T_p_PSL_R p hp hpN i *
          ((q₁.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ))
        ((α_T_p_PSL_R p hp hpN i *
          ((q₂.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ))))
    (hint : IntegrableOn (fun τ ↦ petersson k f g τ)
      (α_T_p_PSL_R p hp hpN i •
        Gamma_p_α_fundDomain_PSL (N := N) (α_T_p_Q p hp hpN i)) μ_hyp) :
    peterssonInner k
      (α_T_p_PSL_R p hp hpN i •
        Gamma_p_α_fundDomain_PSL (N := N) (α_T_p_Q p hp hpN i))
      f g =
    ∑ q : ((Gamma1 N).map SL2Z_to_PSL2R) ⧸
              (((Gamma_p_α (N := N) (α_T_p_Q p hp hpN i)).map SL2Z_to_PSL2R).subgroupOf
                ((Gamma1 N).map SL2Z_to_PSL2R)),
      peterssonInner k
        ((α_T_p_PSL_R p hp hpN i *
          ((q.out : ((Gamma1 N).map SL2Z_to_PSL2R)) : PSL(2, ℝ))⁻¹) •
            (Gamma1_fundDomain_PSL N : Set ℍ))
        f g := by
  rw [← T_p_PSL_R_FD_finite_index_decomp_shifted_eq_smul] at hint ⊢
  exact peterssonInner_iUnion_finite_aedisjoint _ hm hd f g hint

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_upper_tile_shift_to_prefactored_from_SL_tile_balance_family
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (hm : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (hint_LHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableLHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (hint_RHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableRHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (h_SL_tile_balance : ∀ b ∈ Finset.range p,
      TpUpperBSLTileBalance p hp hpN b f g) :
    TpUpperTileShiftPrefactored p hp hpN f g := by
  apply h_upper_tile_shift_to_prefactored_of_FD_slash_exchange p hp hpN f g
  show _ = _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  exact h_α_FD_slash_exchange_T_p_lower_form_of_canonical p hp hpN
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
    (gamma0_T_p_upper_Gamma1_factor N p hpN b)
    (mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp.pos hpN b)
    f g
    (h_α_canonical_form_of_balanced p hp hpN
      (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) f g
      (balanced_α_of_aggregate_FD_balance p hp hpN
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
        (glMap_T_p_upper_det_pos p hp.pos b) f g
        (hd b hb) (hm b hb) (hint_LHS b hb) (hint_RHS b hb)
        (h_FD_balance_of_post_swap_balance p hp hpN
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
          (glMap_T_p_upper_det_pos p hp.pos b) f g
          (h_post_swap_balance_of_SL_tile_balance p hp hpN
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
            (glMap_T_p_upper_det_pos p hp.pos b) f g
            (h_SL_tile_balance b hb)))))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_upper_FD_slash_exchange_from_SL_tile_balance_family
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (hm : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (hint_LHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableLHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (hint_RHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableRHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (h_SL_tile_balance : ∀ b ∈ Finset.range p,
      TpUpperBSLTileBalance p hp hpN b f g) :
    TpUpperFDSlashExchange p hp hpN f g := by
  show _ = _
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb ↦ ?_
  exact h_α_FD_slash_exchange_T_p_lower_form_of_canonical p hp hpN
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
    (gamma0_T_p_upper_Gamma1_factor N p hpN b)
    (mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp.pos hpN b)
    f g
    (h_α_canonical_form_of_balanced p hp hpN
      (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) f g
      (balanced_α_of_aggregate_FD_balance p hp hpN
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
        (glMap_T_p_upper_det_pos p hp.pos b) f g
        (hd b hb) (hm b hb) (hint_LHS b hb) (hint_RHS b hb)
        (h_FD_balance_of_post_swap_balance p hp hpN
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
          (glMap_T_p_upper_det_pos p hp.pos b) f g
          (h_post_swap_balance_of_SL_tile_balance p hp hpN
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
            (glMap_T_p_upper_det_pos p hp.pos b) f g
            (h_SL_tile_balance b hb)))))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_upper_tile_shift_to_prefactored_from_blocker_family
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (hm : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (hint_LHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableLHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (hint_RHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableRHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (h_blockers : ∀ b ∈ Finset.range p,
      TpUpperBranchDiamondFormBlocker p hp hpN b f g) :
    TpUpperTileShiftPrefactored p hp hpN f g :=
  h_upper_tile_shift_to_prefactored_from_SL_tile_balance_family p hp hpN f g
    hd hm hint_LHS hint_RHS
    (fun b hb ↦ h_T_p_upper_SL_tile_balance_from_blocker p hp hpN b f g
      (h_blockers b hb))

open UpperHalfPlane ModularGroup MeasureTheory in
private def TpUpperZeroShiftedFormBlocker_v2
    (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑f ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p _hpN)⁻¹ g)) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p _hpN) f))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p _hpN) g) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem TpUpperZeroShiftedFormBlocker_of_v2
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_v2 : TpUpperZeroShiftedFormBlocker_v2 p hp hpN f g) :
    TpUpperZeroShiftedFormBlocker p hp hpN f g := by
  have h_det_pos := glMap_T_p_lower_det_pos p hp
  unfold TpUpperZeroShiftedFormBlocker_v2 at h_v2
  unfold TpUpperZeroShiftedFormBlocker
  rw [peterssonInner_slash_adjoint (k := k) _ _ h_det_pos ⇑f
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g),
    slash_peterssonAdj_T_p_lower_eq_T_p_upper_0 p hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g),
    peterssonInner_slash_adjoint_right (k := k) _ _ h_det_pos
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g),
    slash_peterssonAdj_T_p_lower_eq_T_p_upper_0 p hp hpN
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)] at h_v2
  exact h_v2

open UpperHalfPlane ModularGroup MeasureTheory in
private def TpHeckeFamilyMeasureHypotheses
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  (Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd))) ∧
  (∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp) ∧
  (IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp) ∧
  (IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp) ∧
  (∀ b ∈ Finset.range p, Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd))) ∧
  (∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp) ∧
  (∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp) ∧
  (∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)

private def TpHeckeFamilyBlocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  TpUpperZeroShiftedFormBlocker p hp hpN f g ∧
  ∀ b ∈ Finset.range p, TpUpperBranchDiamondFormBlocker p hp hpN b f g

open UpperHalfPlane ModularGroup MeasureTheory in
private def TpUniformSigmaPermBlocker
    (p : ℕ) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : GL (Fin 2) ℝ) : Prop :=
  peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑f ∣[k] M)
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k] M)

open UpperHalfPlane ModularGroup MeasureTheory in
private def TpPerQSigmaAlignedBlocker
    (p : ℕ) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : GL (Fin 2) ℝ) (q : SL(2, ℤ) ⧸ Gamma1 N) : Prop :=
  peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
        GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑f ∣[k] M)
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    peterssonInner k
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out :
            SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k] M)

open UpperHalfPlane ModularGroup MeasureTheory in
private def TpPerQSigmaAlignedBlocker_fd
    (p : ℕ) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : GL (Fin 2) ℝ) (q : SL(2, ℤ) ⧸ Gamma1 N) : Prop :=
  peterssonInner k (fd : Set ℍ)
      (⇑f ∣[k] (M *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ)))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out :
            SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) =
    peterssonInner k (fd : Set ℍ)
      (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
        (M * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem TpPerQSigmaAlignedBlocker_fd_of_kernel_eq
    (p : ℕ) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : GL (Fin 2) ℝ) (q : SL(2, ℤ) ⧸ Gamma1 N)
    (h_kernel_eq : ∀ τ : ℍ,
      petersson k
        (⇑f ∣[k] (M * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹))
        τ =
      petersson k
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          (M * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((Gamma1QuotEquivOfGamma0
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
              (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        τ) :
    TpPerQSigmaAlignedBlocker_fd (k := k) p hpN f g M q := by
  unfold TpPerQSigmaAlignedBlocker_fd
  simp only [peterssonInner]
  exact integral_congr_ae (Filter.Eventually.of_forall h_kernel_eq)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Slash of the inverse-diamond shift of `g` by `q.out⁻¹` agrees with the plain slash
of `g` by the `Γ₀`-corrected coset representative `(Equiv q).out⁻¹`. -/
private lemma slash_diamond_inv_out_inv_eq_slash_Gamma1QuotEquiv_out_inv
    (p : ℕ) (hpN : Nat.Coprime p N) (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹) := by
  have hT126_g := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv
    (k := k) (adjointGamma0Rep p N hpN) g q
  rw [adjointGamma0Rep_units p N hpN] at hT126_g
  rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) = (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
            GL (Fin 2) ℝ) from rfl,
    ← ModularForm.SL_slash,
    show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹) =
        ((((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹ :
            SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl,
    ← ModularForm.SL_slash]
  exact hT126_g.symm

open UpperHalfPlane ModularGroup MeasureTheory in
/-- Slash of the diamond shift of `f` by the `Γ₀`-corrected coset representative
`(Equiv q).out⁻¹` agrees with the plain slash of `f` by `q.out⁻¹`. -/
private lemma slash_diamond_out_Gamma1QuotEquiv_eq_slash_out_inv
    (p : ℕ) (hpN : Nat.Coprime p N) (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) =
      ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) := by
  have hT126_uf := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv
    (k := k) (adjointGamma0Rep p N hpN)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) q
  rw [adjointGamma0Rep_units p N hpN] at hT126_uf
  have h_cancel : diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) = f := by
    show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f) = f
    rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f) =
        ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹).comp
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN))) f from rfl,
      ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one]
    rfl
  rw [h_cancel] at hT126_uf
  rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) =
        ((((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹ :
            SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl,
    ← ModularForm.SL_slash,
    show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) = (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) :
            GL (Fin 2) ℝ) from rfl,
    ← ModularForm.SL_slash]
  exact hT126_uf

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem TpPerQSigmaAlignedBlocker_of_fd
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : GL (Fin 2) ℝ) (q : SL(2, ℤ) ⧸ Gamma1 N)
    (h_fd : TpPerQSigmaAlignedBlocker_fd (k := k) p hpN f g M q) :
    TpPerQSigmaAlignedBlocker (k := k) p hpN f g M q := by
  unfold TpPerQSigmaAlignedBlocker_fd at h_fd
  unfold TpPerQSigmaAlignedBlocker
  rw [peterssonInner_mapGL_smul_eq_slash fd (q.out : SL(2, ℤ))⁻¹,
      peterssonInner_mapGL_smul_eq_slash fd
        ((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹]
  simp only [← SlashAction.slash_mul]
  rw [slash_diamond_inv_out_inv_eq_slash_Gamma1QuotEquiv_out_inv p hpN g q,
    slash_diamond_out_Gamma1QuotEquiv_eq_slash_out_inv p hpN f q]
  exact h_fd

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem TpUniformSigmaPermBlocker_of_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : GL (Fin 2) ℝ)
    (hd_LHS : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • fd)))
    (hm_LHS : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : IntegrableOn
      (fun τ ↦ petersson k (⇑f ∣[k] M)
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : IntegrableOn
      (fun τ ↦ petersson k ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k] M) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (h_per_q : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      TpPerQSigmaAlignedBlocker (k := k) p hpN f g M q) :
    TpUniformSigmaPermBlocker (k := k) p hpN f g M := by
  unfold TpUniformSigmaPermBlocker
  rw [peterssonInner_iUnion_finite_aedisjoint _ hm_LHS hd_LHS _ _ hint_LHS,
      peterssonInner_iUnion_finite_aedisjoint _ hm_LHS hd_LHS _ _ hint_RHS]
  rw [← Equiv.sum_comp (Gamma1QuotEquivOfGamma0
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
    (adjointGamma0Rep p N hpN).property)
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ peterssonInner k
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k] M))]
  exact Finset.sum_congr rfl fun q _ ↦ h_per_q q

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma TpUniformSigmaPermBlocker_iff_slash_adj_form
    (p : ℕ) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (M : GL (Fin 2) ℝ) (hM : 0 < M.det.val) :
    TpUniformSigmaPermBlocker (k := k) p hpN f g M ↔
    peterssonInner k (M •
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ)))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          peterssonAdj M) =
      peterssonInner k (M •
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ) • (fd : Set ℍ)))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          peterssonAdj M)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)) := by
  unfold TpUniformSigmaPermBlocker
  constructor
  · intro h
    rw [← peterssonInner_slash_adjoint (k := k) _ _ hM ⇑f _,
        ← peterssonInner_slash_adjoint_right (k := k) _ _ hM _ _]
    exact h
  · intro h
    rw [peterssonInner_slash_adjoint (k := k) _ _ hM ⇑f _,
        peterssonInner_slash_adjoint_right (k := k) _ _ hM _ _]
    exact h

private lemma TpUpperZeroShiftedFormBlocker_v2_eq_uniform
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    TpUpperZeroShiftedFormBlocker_v2 p hp hpN f g ↔
    TpUniformSigmaPermBlocker (k := k) p hpN f g
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma h_M_infty_SL_tile_balance_iff_uniform
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))) ↔
    TpUniformSigmaPermBlocker (k := k) p hpN f g
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :=
  h_M_infty_SL_tile_balance_iff_T_p_lower_diamond_form p hp hpN f g

private lemma TpUpperBranchDiamondFormBlocker_eq_uniform
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    TpUpperBranchDiamondFormBlocker p hp hpN b f g ↔
    TpUniformSigmaPermBlocker (k := k) p hpN f g
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))) := by
  rfl

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma h_T_p_upper_SL_tile_balance_iff_uniform
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) ↔
    TpUniformSigmaPermBlocker (k := k) p hpN f g
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))) :=
  h_T_p_upper_SL_tile_balance_iff_T_p_lower_diamond_form p hp hpN b f g

private def TpHeckeFamilyBlocker_v2
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  TpUpperZeroShiftedFormBlocker_v2 p hp hpN f g ∧
  ∀ b ∈ Finset.range p, TpUpperBranchDiamondFormBlocker p hp hpN b f g

private theorem TpHeckeFamilyBlocker_of_v2
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_v2 : TpHeckeFamilyBlocker_v2 p hp hpN f g) :
    TpHeckeFamilyBlocker p hp hpN f g :=
  ⟨TpUpperZeroShiftedFormBlocker_of_v2 p hp hpN f g h_v2.1, h_v2.2⟩

private theorem TpHeckeFamilyBlocker_v2_of_uniform
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M : TpUniformSigmaPermBlocker (k := k) p hpN f g
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
    (h_U : ∀ b ∈ Finset.range p,
      TpUniformSigmaPermBlocker (k := k) p hpN f g
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)))) :
    TpHeckeFamilyBlocker_v2 p hp hpN f g :=
  ⟨(TpUpperZeroShiftedFormBlocker_v2_eq_uniform p hp hpN f g).mpr h_M,
    fun b hb ↦ (TpUpperBranchDiamondFormBlocker_eq_uniform p hp hpN b f g).mpr
      (h_U b hb)⟩

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem TpHeckeFamilyBlocker_v2_of_SL_tile_balances
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M : peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)))
    (h_U : ∀ b ∈ Finset.range p, peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
    TpHeckeFamilyBlocker_v2 p hp hpN f g :=
  TpHeckeFamilyBlocker_v2_of_uniform p hp hpN f g
    ((h_M_infty_SL_tile_balance_iff_uniform p hp hpN f g).mp h_M)
    (fun b hb ↦ (h_T_p_upper_SL_tile_balance_iff_uniform p hp hpN b f g).mp (h_U b hb))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_LHS_dist_eq_RHS_absorbed_from_two_residuals
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_tile_shift_to_prefactored : MInftyTileShiftPrefactored p hp hpN f g)
    (h_upper_tile_shift_to_prefactored : TpUpperTileShiftPrefactored p hp hpN f g) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k]
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k]
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :=
  petN_LHS_dist_eq_RHS_absorbed_from_branches p hp hpN f g
    (M_infty_branch_hypothesis_via_sum_chain p hp hpN f g
      h_M_infty_tile_shift_to_prefactored)
    (T_p_upper_branch_hypothesis_via_sum_chain p hp hpN f g
      h_upper_tile_shift_to_prefactored)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The "**LHS distribution = RHS absorbed**" equation: the sum-over-`q` of per-`q`
`fd`-Petersson on `(T_p_lower·γ₀·q.out⁻¹) f` vs `(γ_adj·q.out⁻¹) g` equals the
σ-reindexed sum where `g` carries the diamond. Used as the irreducible algebraic
hypothesis of `petN_heckeT_p_LHS_eq_diamond_T_p_g_via_sum_chain`,
`petN_heckeT_p_adjoint_standard_form_via_sum_chain`, and
`DSDoubleCosetTileBridge_of_LHS_dist_eq_RHS_absorbed`. -/
def LHSDistEqRHSAbsorbed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    (peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k]
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) =
  ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    (peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_LHS_dist_eq_RHS_absorbed_from_TpHeckeFamilyBlocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd_M : MInftyTilePairwiseAEDisjoint p hp hpN)
    (hm_M : MInftyTileNullMeasurable p hp hpN)
    (hint_LHS_M : MInftyIntegrableLHS p hp hpN f g)
    (hint_RHS_M : MInftyIntegrableRHS p hp hpN f g)
    (hd_U : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (hm_U : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (hint_LHS_U : ∀ b ∈ Finset.range p,
      AlphaIntegrableLHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (hint_RHS_U : ∀ b ∈ Finset.range p,
      AlphaIntegrableRHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (h_family : TpHeckeFamilyBlocker p hp hpN f g) :
    LHSDistEqRHSAbsorbed p hp hpN f g := by
  obtain ⟨h_M, h_U⟩ := h_family
  exact petN_LHS_dist_eq_RHS_absorbed_from_two_residuals p hp hpN f g
    (h_M_infty_tile_shift_to_prefactored_from_blocker p hp hpN f g
      hd_M hm_M hint_LHS_M hint_RHS_M h_M)
    (h_upper_tile_shift_to_prefactored_from_blocker_family p hp hpN f g
      hd_U hm_U hint_LHS_U hint_RHS_U h_U)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_LHS_dist_eq_RHS_absorbed_from_petN_symmetric_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sym : petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)) :
    LHSDistEqRHSAbsorbed p hp hpN f g := by
  show _ = _
  rw [← petN_T_p_heckeT_p_LHS_sum_diamond_distributed p hp hpN f g, h_sym,
      petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g,
      petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex p hp hpN f g,
      petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex_absorbed p hp hpN
        f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_LHS_eq_diamond_T_p_g_via_sum_chain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_LHS_dist_eq_RHS_absorbed : LHSDistEqRHSAbsorbed p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
  unfold LHSDistEqRHSAbsorbed at h_LHS_dist_eq_RHS_absorbed
  rw [petN_T_p_heckeT_p_LHS_sum_diamond_distributed p hp hpN f g,
    h_LHS_dist_eq_RHS_absorbed,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex_absorbed p hp hpN
      f g,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex p hp hpN f g,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_TpHeckeFamilyBlocker
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd_M : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS_M : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS_M : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hd_U : ∀ b ∈ Finset.range p, Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm_U : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS_U : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS_U : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_family : TpHeckeFamilyBlocker p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_LHS_eq_diamond_T_p_g_via_sum_chain p hp hpN f g
    (petN_LHS_dist_eq_RHS_absorbed_from_TpHeckeFamilyBlocker p hp hpN f g
      hd_M hm_M hint_LHS_M hint_RHS_M
      hd_U hm_U hint_LHS_U hint_RHS_U h_family)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_TpHeckeFamilyBlocker_v2
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd_M : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS_M : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS_M : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hd_U : ∀ b ∈ Finset.range p, Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm_U : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS_U : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS_U : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_family_v2 : TpHeckeFamilyBlocker_v2 p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_symmetric_form_from_TpHeckeFamilyBlocker p hp hpN f g
    hd_M hm_M hint_LHS_M hint_RHS_M
    hd_U hm_U hint_LHS_U hint_RHS_U
    (TpHeckeFamilyBlocker_of_v2 p hp hpN f g h_family_v2)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_v2_bundled
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_measure : TpHeckeFamilyMeasureHypotheses p hp hpN f g)
    (h_family_v2 : TpHeckeFamilyBlocker_v2 p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
  obtain ⟨hd_M, hm_M, hint_LHS_M, hint_RHS_M,
    hd_U, hm_U, hint_LHS_U, hint_RHS_U⟩ := h_measure
  exact petN_heckeT_p_symmetric_form_from_TpHeckeFamilyBlocker_v2 p hp hpN f g
    hd_M hm_M hint_LHS_M hint_RHS_M
    hd_U hm_U hint_LHS_U hint_RHS_U
    h_family_v2

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_uniform
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_measure : TpHeckeFamilyMeasureHypotheses p hp hpN f g)
    (h_M : TpUniformSigmaPermBlocker (k := k) p hpN f g
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
    (h_U : ∀ b ∈ Finset.range p,
      TpUniformSigmaPermBlocker (k := k) p hpN f g
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_symmetric_form_from_v2_bundled p hp hpN f g h_measure
    (TpHeckeFamilyBlocker_v2_of_uniform p hp hpN f g h_M h_U)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_SL_tile_balances
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_measure : TpHeckeFamilyMeasureHypotheses p hp hpN f g)
    (h_M : peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)))
    (h_U : ∀ b ∈ Finset.range p, peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_symmetric_form_from_v2_bundled p hp hpN f g h_measure
    (TpHeckeFamilyBlocker_v2_of_SL_tile_balances p hp hpN f g h_M h_U)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_measure : TpHeckeFamilyMeasureHypotheses p hp hpN f g)
    (h_per_q_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      TpPerQSigmaAlignedBlocker (k := k) p hpN f g
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) q)
    (h_per_q_U : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      TpPerQSigmaAlignedBlocker (k := k) p hpN f g
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b))) q)
    (hd_iUnion : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • fd)))
    (hm_iUnion : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_LHS : IntegrableOn
      (fun τ ↦ petersson k (⇑f ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_RHS : IntegrableOn
      (fun τ ↦ petersson k ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_U_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_U_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)))) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_symmetric_form_from_uniform p hp hpN f g h_measure
    (TpUniformSigmaPermBlocker_of_per_q p hp hpN f g
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)
      hd_iUnion hm_iUnion hint_M_LHS hint_M_RHS h_per_q_M)
    (fun b hb ↦ TpUniformSigmaPermBlocker_of_per_q p hp hpN f g
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)))
        hd_iUnion hm_iUnion (hint_U_LHS b hb) (hint_U_RHS b hb)
        (h_per_q_U b hb))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_per_q_fd
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_measure : TpHeckeFamilyMeasureHypotheses p hp hpN f g)
    (h_per_q_fd_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      TpPerQSigmaAlignedBlocker_fd (k := k) p hpN f g
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) q)
    (h_per_q_fd_U : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      TpPerQSigmaAlignedBlocker_fd (k := k) p hpN f g
        ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b))) q)
    (hd_iUnion : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • fd)))
    (hm_iUnion : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_LHS : IntegrableOn
      (fun τ ↦ petersson k (⇑f ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_RHS : IntegrableOn
      (fun τ ↦ petersson k ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_U_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
        ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_U_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)))) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_symmetric_form_from_per_q p hp hpN f g h_measure
    (fun q ↦ TpPerQSigmaAlignedBlocker_of_fd p hp hpN f g
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) q (h_per_q_fd_M q))
    (fun b hb q ↦ TpPerQSigmaAlignedBlocker_of_fd p hp hpN f g
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))) q (h_per_q_fd_U b hb q))
    hd_iUnion hm_iUnion hint_M_LHS hint_M_RHS hint_U_LHS hint_U_RHS

open UpperHalfPlane ModularGroup MeasureTheory in
theorem petN_heckeT_p_adjoint_standard_form_via_sum_chain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_LHS_dist_eq_RHS_absorbed : LHSDistEqRHSAbsorbed p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_of_LHS_bridge p hp hpN f g
    (petN_heckeT_p_LHS_eq_diamond_T_p_g_via_sum_chain p hp hpN f g
      h_LHS_dist_eq_RHS_absorbed)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_sym : petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_via_sum_chain p hp hpN f g
    (h_LHS_dist_eq_RHS_absorbed_from_petN_symmetric_form p hp hpN f g h_sym)

private def heckeT_p_petN_symmetric_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  petN (heckeT_p_cusp k p hp hpN f) g =
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
      (heckeT_p_cusp k p hp hpN g)

private theorem petN_heckeT_p_adjoint_standard_form_from_combined_hecke_sum_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_combined : heckeT_p_petN_symmetric_residual p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form p hp hpN f g h_combined

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_diamond_shift_core_from_HeckeFD_swap
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_LHS_aggregate :
      petN (heckeT_p_cusp k p hp hpN f) g =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)))
    (h_RHS_aggregate :
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
          (heckeT_p_cusp k p hp hpN g) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g)
    (h_HeckeFD_swap :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  h_LHS_aggregate.trans (h_HeckeFD_swap.trans h_RHS_aggregate.symm)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_HeckeFD_swap
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_LHS_aggregate :
      petN (heckeT_p_cusp k p hp hpN f) g =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)))
    (h_RHS_aggregate :
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
          (heckeT_p_cusp k p hp hpN g) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g)
    (h_HeckeFD_swap :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form p hp hpN f g
    (petN_heckeT_p_diamond_shift_core_from_HeckeFD_swap p hp hpN f g
      h_LHS_aggregate h_RHS_aggregate h_HeckeFD_swap)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_aggregate_hypotheses
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_disj : AlphaTilePairwiseAEDisjoint (N := N) (glMap (M_infty N p hp.pos hpN)))
    (h_M_infty_meas : AlphaTileNullMeasurable (N := N) (glMap (M_infty N p hp.pos hpN)))
    (h_upper_disj : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (h_upper_meas : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (h_upper_per_q_disj : TpUpperPerQTilePairwiseAEDisjoint (N := N) p hp)
    (h_upper_per_q_meas : TpUpperPerQTileNullMeasurable (N := N) p hp)
    (h_LHS_M_infty_int : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_LHS_upper_int : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k ⇑f
          (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_LHS_upper_per_q_int : TpUpperPerQIntegrableBUnion (N := N) p hp
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_M_infty_int : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_upper_int : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k ⇑g
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_upper_per_q_int : TpUpperPerQIntegrableBUnion (N := N) p hp
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_HeckeFD_swap :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_HeckeFD_swap p hp hpN f g
    (petN_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN f g
      h_M_infty_disj h_M_infty_meas h_LHS_M_infty_int
      h_upper_disj h_upper_meas h_LHS_upper_int
      h_upper_per_q_disj h_upper_per_q_meas h_LHS_upper_per_q_int)
    (petN_diamond_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN f g
      h_M_infty_disj h_M_infty_meas h_RHS_M_infty_int
      h_upper_disj h_upper_meas h_RHS_upper_int
      h_upper_per_q_disj h_upper_per_q_meas h_RHS_upper_per_q_int)
    h_HeckeFD_swap

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeT_p_petN_symmetric_residual_from_aggregate_HeckeFD_swap
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_disj : AlphaTilePairwiseAEDisjoint (N := N) (glMap (M_infty N p hp.pos hpN)))
    (h_M_infty_meas : AlphaTileNullMeasurable (N := N) (glMap (M_infty N p hp.pos hpN)))
    (h_upper_disj : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (h_upper_meas : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (h_upper_per_q_disj : TpUpperPerQTilePairwiseAEDisjoint (N := N) p hp)
    (h_upper_per_q_meas : TpUpperPerQTileNullMeasurable (N := N) p hp)
    (h_LHS_M_infty_int : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_LHS_upper_int : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k ⇑f
          (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_LHS_upper_per_q_int : TpUpperPerQIntegrableBUnion (N := N) p hp
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_M_infty_int : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_upper_int : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k ⇑g
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_upper_per_q_int : TpUpperPerQIntegrableBUnion (N := N) p hp
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_HeckeFD_swap :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
                GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g) :
    heckeT_p_petN_symmetric_residual p hp hpN f g :=
  petN_heckeT_p_diamond_shift_core_from_HeckeFD_swap p hp hpN f g
    (petN_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN f g
      h_M_infty_disj h_M_infty_meas h_LHS_M_infty_int
      h_upper_disj h_upper_meas h_LHS_upper_int
      h_upper_per_q_disj h_upper_per_q_meas h_LHS_upper_per_q_int)
    (petN_diamond_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN f g
      h_M_infty_disj h_M_infty_meas h_RHS_M_infty_int
      h_upper_disj h_upper_meas h_RHS_upper_int
      h_upper_per_q_disj h_upper_per_q_meas h_RHS_upper_per_q_int)
    h_HeckeFD_swap

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_HeckeFD_swap_from_petN_symm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_disj : AlphaTilePairwiseAEDisjoint (N := N) (glMap (M_infty N p hp.pos hpN)))
    (h_M_infty_meas : AlphaTileNullMeasurable (N := N) (glMap (M_infty N p hp.pos hpN)))
    (h_upper_disj : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (h_upper_meas : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (h_upper_per_q_disj : TpUpperPerQTilePairwiseAEDisjoint (N := N) p hp)
    (h_upper_per_q_meas : TpUpperPerQTileNullMeasurable (N := N) p hp)
    (h_LHS_M_infty_int : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_LHS_upper_int : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k ⇑f
          (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_LHS_upper_per_q_int : TpUpperPerQIntegrableBUnion (N := N) p hp
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_M_infty_int : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_upper_int : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k ⇑g
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_RHS_upper_per_q_int : TpUpperPerQIntegrableBUnion (N := N) p hp
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ))
    (h_sym : petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g)) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) +
    ∑ b ∈ Finset.range p,
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g +
    ∑ b ∈ Finset.range p,
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ⇑g := by
  rw [(petN_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN f g
        h_M_infty_disj h_M_infty_meas h_LHS_M_infty_int
        h_upper_disj h_upper_meas h_LHS_upper_int
        h_upper_per_q_disj h_upper_per_q_meas h_LHS_upper_per_q_int).symm]
  rw [h_sym]
  rw [petN_diamond_heckeT_p_eq_per_alpha_HeckeFD_form p hp hpN f g
        h_M_infty_disj h_M_infty_meas h_RHS_M_infty_int
        h_upper_disj h_upper_meas h_RHS_upper_int
        h_upper_per_q_disj h_upper_per_q_meas h_RHS_upper_per_q_int]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_h_sym_from_DSDoubleCosetTileBridge
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_bridge : DSDoubleCosetTileBridge p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
  have h_std :=
    petN_heckeT_p_adjoint_standard_form_of_doubleCosetTileBridge
      p hp hpN f g h_bridge
  rw [h_std, ← petN_diamond_heckeT_p_eq_unsymm_RHS p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem DSDoubleCosetTileBridge_of_LHS_dist_eq_RHS_absorbed
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_LHS_dist_eq_RHS_absorbed : LHSDistEqRHSAbsorbed p hp hpN f g) :
    DSDoubleCosetTileBridge p hp hpN f g := by
  unfold DSDoubleCosetTileBridge
  unfold LHSDistEqRHSAbsorbed at h_LHS_dist_eq_RHS_absorbed
  rw [h_LHS_dist_eq_RHS_absorbed,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex_absorbed p hp hpN f g,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_T_p_lower_gamma_M_tile_to_iUnion
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : AlphaTileNullMeasurable (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hd : AlphaTilePairwiseAEDisjoint (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hint : AlphaIntegrableUnion (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) :=
  (peterssonInner_iUnion_finite_aedisjoint
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
        (ModularGroup.fd : Set UpperHalfPlane))) hm hd ⇑f
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) hint).symm

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Shared tile identity** for a generic `Γ₁(N)` factor `γ`: pushing the slash
of the adjoint `T_p`-tile `T_p_lower · γ · q⁻¹` over the standard fundamental
domain through the adjoint–coset exchange. Both the `M_∞` and per-`b` upper tile
identities are instances of this. -/
private lemma peterssonInner_T_p_lower_gamma_tile_per_q_eq_fd_LHS_dist
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) := by
  have h_T_p_lower_det_pos := glMap_T_p_lower_det_pos p hp
  have h_gamma_det_one : (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = ((Int.castRingHom ℝ).mapMatrix γ.val) by
      rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, γ.property]; simp
  have h_β_det : 0 <
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ)).det.val := by
    show 0 < ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ) : GL (Fin 2) ℝ).val.det
    rw [Units.val_mul, Matrix.det_mul, h_gamma_det_one, mul_one]
    exact h_T_p_lower_det_pos
  have h_g_slash : (⇑g ∣[k]
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) := by
    rw [SlashAction.slash_mul]
    congr 1
    show ⇑g ∣[k] _ = ⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
    rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
      (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
    rfl
  have h_pa_simp : (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        peterssonAdj ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ))) := by
    rw [peterssonAdj_mul, peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero,
      peterssonAdj_mapGL_SL_eq_inv, ← map_inv, SlashAction.slash_mul]
    congr 1
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ⁻¹ : GL (Fin 2) ℝ) =
        ((γ⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl, ← ModularForm.SL_slash]
    exact (slash_Gamma1_eq (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
      γ⁻¹ (Subgroup.inv_mem _ hγ)).symm
  rw [h_g_slash, h_pa_simp, mul_smul, ← peterssonInner_slash_adjoint_coset
    ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ))
    h_β_det q ⇑f ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_T_p_lower_gamma_M_tile_per_q_eq_fd_LHS_dist
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) :=
  peterssonInner_T_p_lower_gamma_tile_per_q_eq_fd_LHS_dist p hp hpN
    (gamma0_T_p_upper_Gamma1_factor N p hpN 0 * M_infty_Gamma1_factor N p hpN 0)
    (gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
      N p hpN) q f g

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_iUnion_T_p_lower_gamma_M_to_RHS_prefactored
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : AlphaTileNullMeasurable (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hd : AlphaTilePairwiseAEDisjoint (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hint : AlphaIntegrableUnion (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (h_tile_shift_to_prefactored :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
            ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
            ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)))
      ⇑f
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [← peterssonInner_sum_T_p_lower_gamma_M_tile_to_iUnion p hp hpN f g hm hd hint]
  rw [Finset.sum_congr rfl (fun q _ ↦ peterssonInner_T_p_lower_gamma_M_tile_per_q_eq_fd_LHS_dist p hp hpN
      (q.out : SL(2, ℤ)) f g)]
  exact M_infty_branch_sum_slash_adjoint_reindex_prefactored p hp hpN f g
    h_tile_shift_to_prefactored

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma peterssonInner_T_p_lower_gamma_b_tile_per_q_eq_fd_LHS_dist_upper
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ)) (b : ℕ) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) :=
  peterssonInner_T_p_lower_gamma_tile_per_q_eq_fd_LHS_dist p hp hpN
    (gamma0_T_p_upper_Gamma1_factor N p hpN b)
    (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b) q f g

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_iUnion_T_p_lower_gamma_b_to_RHS_prefactored_upper
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : AlphaFamilyPerQTileNullMeasurable (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hd : AlphaFamilyPerQTilePairwiseAEDisjoint (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hint : AlphaFamilyPerQIntegrableBUnion (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (h_upper_tile_shift_to_prefactored :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
                (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
                  (ModularGroup.fd : Set UpperHalfPlane)))
              ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)
              ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
                (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
              (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹))
              (⇑g ∣[k]
                ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                  ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                    ((Gamma1QuotEquivOfGamma0
                      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                      (adjointGamma0Rep p N hpN).property q).out :
                      SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N, peterssonInner k
        (⋃ b ∈ Finset.range p,
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [Finset.sum_congr rfl (fun q _ ↦ peterssonInner_biUnion_finset_ae (Finset.range p) (hm q) (hd q) ⇑f
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
      (hint q))]
  rw [Finset.sum_congr rfl (fun q _ ↦ Finset.sum_congr rfl (fun b _ ↦ peterssonInner_T_p_lower_gamma_b_tile_per_q_eq_fd_LHS_dist_upper p hp hpN
        (q.out : SL(2, ℤ)) b f g))]
  exact T_p_upper_branch_sum_slash_adjoint_reindex_prefactored p hp hpN f g
    h_upper_tile_shift_to_prefactored

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **`M_∞` branch** of `h_LHS_dist_eq_RHS_absorbed_of_M_infty_iUnion`: rewrite the
per-`q` `T_p_lower · γ_M · q⁻¹` distribution sum into the diamond-shifted prefactored
form, using the per-`q` tile identity, the AE-disjoint `iUnion` collapse, and the
supplied `M_∞`-`iUnion` prefactorization. -/
private theorem h_LHS_dist_eq_RHS_absorbed_M_branch
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm_M : AlphaTileNullMeasurable (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hd_M : AlphaTilePairwiseAEDisjoint (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hint_M : AlphaIntegrableUnion (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (h_M_infty_iUnion_eq_RHS_prefactored :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑f ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k]
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                    M_infty_Gamma1_factor N p hpN 0)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [Finset.sum_congr rfl (fun q _ ↦ (peterssonInner_T_p_lower_gamma_M_tile_per_q_eq_fd_LHS_dist p hp hpN
      (q.out : SL(2, ℤ)) f g).symm)]
  rw [peterssonInner_sum_T_p_lower_gamma_M_tile_to_iUnion p hp hpN f g
    hm_M hd_M hint_M]
  rw [h_M_infty_iUnion_eq_RHS_prefactored]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  congr 1
  exact slash_M_infty_eq_diamond_slash_T_p_lower_factor p hp hpN g
    (Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **Upper branch** of `h_LHS_dist_eq_RHS_absorbed_of_M_infty_iUnion`: rewrite the
per-`q`, per-`b` `T_p_lower · γ_b · q⁻¹` distribution double-sum into the
diamond-shifted prefactored form, using the per-`q`/`b` tile identity, the AE-disjoint
`biUnion` collapse, and the supplied upper-`iUnion` prefactorization. -/
private theorem h_LHS_dist_eq_RHS_absorbed_upper_branch
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm_T : AlphaFamilyPerQTileNullMeasurable (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hd_T : AlphaFamilyPerQTilePairwiseAEDisjoint (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hint_T : AlphaFamilyPerQIntegrableBUnion (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (h_upper_iUnion_eq_RHS_prefactored :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N, peterssonInner k
          (⋃ b ∈ Finset.range p,
            (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k]
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  rw [Finset.sum_congr rfl (fun q _ ↦ Finset.sum_congr rfl (fun b _ ↦ (peterssonInner_T_p_lower_gamma_b_tile_per_q_eq_fd_LHS_dist_upper p hp hpN
        (q.out : SL(2, ℤ)) b f g).symm))]
  rw [Finset.sum_congr rfl (fun q _ ↦ (peterssonInner_biUnion_finset_ae (Finset.range p) (hm_T q) (hd_T q) ⇑f
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))
      (hint_T q)).symm)]
  rw [h_upper_iUnion_eq_RHS_prefactored]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  congr 1
  exact slash_T_p_upper_eq_diamond_slash_T_p_lower_factor p hp hpN b g
    (Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem h_LHS_dist_eq_RHS_absorbed_of_M_infty_iUnion
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm_M : AlphaTileNullMeasurable (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hd_M : AlphaTilePairwiseAEDisjoint (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hint_M : AlphaIntegrableUnion (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (hm_T : AlphaFamilyPerQTileNullMeasurable (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hd_T : AlphaFamilyPerQTilePairwiseAEDisjoint (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hint_T : AlphaFamilyPerQIntegrableBUnion (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (h_M_infty_iUnion_eq_RHS_prefactored :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))
    (h_upper_iUnion_eq_RHS_prefactored :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N, peterssonInner k
          (⋃ b ∈ Finset.range p,
            (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
          (⇑g ∣[k]
            (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
            (⇑g ∣[k]
              (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      (peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                  M_infty_Gamma1_factor N p hpN 0)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) +
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
              ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    h_LHS_dist_eq_RHS_absorbed_M_branch p hp hpN f g hm_M hd_M hint_M
      h_M_infty_iUnion_eq_RHS_prefactored,
    h_LHS_dist_eq_RHS_absorbed_upper_branch p hp hpN f g hm_T hd_T hint_T
      h_upper_iUnion_eq_RHS_prefactored]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_via_iUnion_residuals
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm_M : AlphaTileNullMeasurable (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hd_M : AlphaTilePairwiseAEDisjoint (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))))
    (hint_M : AlphaIntegrableUnion (N := N)
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (hm_T : AlphaFamilyPerQTileNullMeasurable (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hd_T : AlphaFamilyPerQTilePairwiseAEDisjoint (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))))
    (hint_T : AlphaFamilyPerQIntegrableBUnion (N := N) p
      (fun b ↦ (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)))
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ))
    (h_M_infty_iUnion_eq_RHS_prefactored :
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))
    (h_upper_iUnion_eq_RHS_prefactored :
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N, peterssonInner k
          (⋃ b ∈ Finset.range p,
            (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          ⇑f
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ))) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k ModularGroup.fd
            (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹))
            (⇑g ∣[k]
              ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_via_sum_chain p hp hpN f g
    (h_LHS_dist_eq_RHS_absorbed_of_M_infty_iUnion p hp hpN f g
      hm_M hd_M hint_M hm_T hd_T hint_T
      h_M_infty_iUnion_eq_RHS_prefactored
      h_upper_iUnion_eq_RHS_prefactored)

open UpperHalfPlane ModularGroup MeasureTheory in
private noncomputable def Gamma1QuotEquivOfGamma0_out_correction
    (γ : ↥(Gamma0 N)) (q : SL(2, ℤ) ⧸ Gamma1 N) : SL(2, ℤ) :=
  ((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out : SL(2, ℤ))⁻¹ *
    ((q.out : SL(2, ℤ)) * ((γ : SL(2, ℤ))⁻¹))

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma Gamma1QuotEquivOfGamma0_out_correction_mem_Gamma1
    (γ : ↥(Gamma0 N)) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    Gamma1QuotEquivOfGamma0_out_correction γ q ∈ Gamma1 N := by
  show ((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out : SL(2, ℤ))⁻¹ *
      ((q.out : SL(2, ℤ)) * ((γ : SL(2, ℤ))⁻¹)) ∈ Gamma1 N
  set σ := Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property
  have h_coset_eq : (σ q) = ⟦(q.out : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹⟧ := by
    conv_lhs => rw [show q = ⟦q.out⟧ from q.out_eq.symm]
    rfl
  have h_out_eq_mk : ⟦((σ q).out : SL(2, ℤ))⟧ =
      (⟦(q.out : SL(2, ℤ)) * (γ : SL(2, ℤ))⁻¹⟧ : SL(2, ℤ) ⧸ Gamma1 N) := by
    rw [← h_coset_eq, (σ q).out_eq]
  have h_left_rel := Quotient.exact h_out_eq_mk
  change (QuotientGroup.leftRel _).r _ _ at h_left_rel
  rwa [QuotientGroup.leftRel_apply] at h_left_rel

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma Gamma1QuotEquivOfGamma0_out_inv_eq_correction_mul
    (γ : ↥(Gamma0 N)) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out : SL(2, ℤ))⁻¹ =
      Gamma1QuotEquivOfGamma0_out_correction γ q * (γ : SL(2, ℤ)) *
        ((q.out : SL(2, ℤ)))⁻¹ := by
  show ((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out)⁻¹ =
    (((Gamma1QuotEquivOfGamma0 (γ : SL(2, ℤ)) γ.property q).out)⁻¹ *
      ((q.out : SL(2, ℤ)) * ((γ : SL(2, ℤ))⁻¹))) * (γ : SL(2, ℤ)) *
        ((q.out : SL(2, ℤ)))⁻¹
  group

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma mapGL_gamma0_mul_T_p_upper_mul_Gamma1QuotEquiv_out_inv_factorization
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) : GL (Fin 2) ℝ) *
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹)) =
    (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((gamma0_T_p_upper_Gamma1_factor N p hpN b) *
          (Gamma1QuotEquivOfGamma0_out_correction
            (adjointGamma0Rep p N hpN) q) *
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹) := by
  rw [Gamma1QuotEquivOfGamma0_out_inv_eq_correction_mul (adjointGamma0Rep p N hpN) q]
  simp only [map_mul]
  rw [← mul_assoc, ← mul_assoc,
    mapGL_gamma0_mul_T_p_upper_eq_T_p_lower_mul_mapGL_delta N p hp.pos hpN b]
  simp only [mul_assoc]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_diamond_T_p_upper_Gamma1QuotEquiv_out_inv_eq_T_p_lower_via_correction
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹)) =
    ⇑g ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (Gamma1QuotEquivOfGamma0_out_correction (adjointGamma0Rep p N hpN) q *
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
            ((q.out : SL(2, ℤ)))⁻¹))) := by
  rw [slash_diamond_inv_T_p_upper_eq_T_p_lower_delta p hp hpN b
    ((Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ)) g,
    Gamma1QuotEquivOfGamma0_out_inv_eq_correction_mul
      (adjointGamma0Rep p N hpN) q]

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_T_p_upper_Gamma1QuotEquiv_out_inv_eq_diamond_T_p_lower_via_correction
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k]
      ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹)) =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (Gamma1QuotEquivOfGamma0_out_correction (adjointGamma0Rep p N hpN) q *
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
            ((q.out : SL(2, ℤ)))⁻¹))) := by
  have h := slash_diamond_T_p_upper_Gamma1QuotEquiv_out_inv_eq_T_p_lower_via_correction
    p hp hpN b q (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)
  rw [show (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) :
      CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = g by
    show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN) g) = g
    rw [show diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (diamondOpCusp k (ZMod.unitOfCoprime p hpN) g) =
        ((diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹).comp
          (diamondOpCusp k (ZMod.unitOfCoprime p hpN))) g from rfl,
      ← diamondOpCusp_mul, inv_mul_cancel, diamondOpCusp_one]
    rfl] at h
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_T_p_upper_Gamma1QuotEquiv_out_inv_slot2_rewrite
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∑ b ∈ Finset.range p,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹)))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∑ b ∈ Finset.range p,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (Gamma1QuotEquivOfGamma0_out_correction
                (adjointGamma0Rep p N hpN) q *
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
                ((q.out : SL(2, ℤ)))⁻¹)))) := by
  refine Finset.sum_congr rfl (fun q _ ↦ ?_)
  refine Finset.sum_congr rfl (fun b _ ↦ ?_)
  congr 1
  exact slash_T_p_upper_Gamma1QuotEquiv_out_inv_eq_diamond_T_p_lower_via_correction
    p hp hpN b q g

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem T_p_upper_branch_via_sum_chain_correction_factorized
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_upper_tile_shift_to_prefactored :
      TpUpperTileShiftPrefactored p hp hpN f g) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∑ b ∈ Finset.range p,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∑ b ∈ Finset.range p,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (Gamma1QuotEquivOfGamma0_out_correction
                (adjointGamma0Rep p N hpN) q *
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
                ((q.out : SL(2, ℤ)))⁻¹)))) := by
  rw [T_p_upper_branch_sum_slash_adjoint_reindex_prefactored p hp hpN f g
    h_upper_tile_shift_to_prefactored]
  exact peterssonInner_sum_T_p_upper_Gamma1QuotEquiv_out_inv_slot2_rewrite
    p hp hpN f g

open UpperHalfPlane ModularGroup MeasureTheory in
private lemma slash_M_infty_Gamma1QuotEquiv_out_inv_eq_diamond_T_p_lower_via_correction
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ⇑g ∣[k]
      ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹)) =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0)) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (Gamma1QuotEquivOfGamma0_out_correction (adjointGamma0Rep p N hpN) q *
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
            ((q.out : SL(2, ℤ)))⁻¹))) := by
  rw [slash_M_infty_eq_diamond_slash_T_p_lower_factor p hp hpN g
    ((Gamma1QuotEquivOfGamma0
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
      (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ)),
    Gamma1QuotEquivOfGamma0_out_inv_eq_correction_mul
      (adjointGamma0Rep p N hpN) q]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_M_infty_Gamma1QuotEquiv_out_inv_slot2_rewrite
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k]
          ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹)))) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (Gamma1QuotEquivOfGamma0_out_correction
                (adjointGamma0Rep p N hpN) q *
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
                ((q.out : SL(2, ℤ)))⁻¹)))) := by
  refine Finset.sum_congr rfl (fun q _ ↦ ?_)
  congr 1
  exact slash_M_infty_Gamma1QuotEquiv_out_inv_eq_diamond_T_p_lower_via_correction
    p hp hpN q g

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_two_tile_shift_residuals
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_tile_shift_to_prefactored : MInftyTileShiftPrefactored p hp hpN f g)
    (h_upper_tile_shift_to_prefactored : TpUpperTileShiftPrefactored p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_via_sum_chain p hp hpN f g
    (petN_LHS_dist_eq_RHS_absorbed_from_two_residuals p hp hpN f g
      h_M_infty_tile_shift_to_prefactored h_upper_tile_shift_to_prefactored)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_two_FD_slash_exchanges
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_M_infty_FD_slash_exchange : MInftyFDSlashExchange p hp hpN f g)
    (h_upper_FD_slash_exchange : TpUpperFDSlashExchange p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_two_tile_shift_residuals p hp hpN f g
    (h_M_infty_tile_shift_to_prefactored_of_FD_slash_exchange p hp hpN f g
      h_M_infty_FD_slash_exchange)
    (h_upper_tile_shift_to_prefactored_of_FD_slash_exchange p hp hpN f g
      h_upper_FD_slash_exchange)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_SL_tile_balances
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd_M : MInftyTilePairwiseAEDisjoint p hp hpN)
    (hm_M : MInftyTileNullMeasurable p hp hpN)
    (hint_M_LHS : MInftyIntegrableLHS p hp hpN f g)
    (hint_M_RHS : MInftyIntegrableRHS p hp hpN f g)
    (h_M_SL_tile_balance : MInftySLTileBalance p hp hpN f g)
    (hd_T : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (hm_T : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (hint_T_LHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableLHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (hint_T_RHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableRHS p hpN (glMap (T_p_upper p hp.pos b)) f g)
    (h_T_SL_tile_balance : ∀ b ∈ Finset.range p,
      TpUpperBSLTileBalance p hp hpN b f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_two_FD_slash_exchanges p hp hpN f g
    (h_M_infty_FD_slash_exchange_from_SL_tile_balance p hp hpN f g
      hd_M hm_M hint_M_LHS hint_M_RHS h_M_SL_tile_balance)
    (h_upper_FD_slash_exchange_from_SL_tile_balance_family p hp hpN f g
      hd_T hm_T hint_T_LHS hint_T_RHS h_T_SL_tile_balance)

open UpperHalfPlane ModularGroup MeasureTheory in
private def heckeFD_canonical_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  (peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
    peterssonInner k
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
      (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
      (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))) ∧
  (∀ b ∈ Finset.range p,
    peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem TpHeckeFamilyBlocker_v2_of_heckeFD_canonical_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_canon : heckeFD_canonical_SL_tile_balance p hp hpN f g) :
    TpHeckeFamilyBlocker_v2 p hp hpN f g :=
  TpHeckeFamilyBlocker_v2_of_SL_tile_balances p hp hpN f g h_canon.1 h_canon.2

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_symmetric_form_from_heckeFD_canonical_SL_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_measure : TpHeckeFamilyMeasureHypotheses p hp hpN f g)
    (h_canon : heckeFD_canonical_SL_tile_balance p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_symmetric_form_from_v2_bundled p hp hpN f g h_measure
    (TpHeckeFamilyBlocker_v2_of_heckeFD_canonical_SL_tile_balance
      p hp hpN f g h_canon)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_canonical_SL_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd_M : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_M_LHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_M_RHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hd_T : ∀ b ∈ Finset.range p, Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm_T : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_T_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_T_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_canon : heckeFD_canonical_SL_tile_balance p hp hpN f g) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_SL_tile_balances p hp hpN f g
    hd_M hm_M hint_M_LHS hint_M_RHS h_canon.1
    hd_T hm_T hint_T_LHS hint_T_RHS h_canon.2

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeFD_canonical_SL_tile_balance_M_infty_from_per_tile_balance
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : SLTilePairwiseAEDisjoint (N := N))
    (hm : SLTileNullMeasurable (N := N))
    (hint_LHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ))
    (hint_RHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ))
    (h_per_tile : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))) :
    peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) := by
  rw [peterssonInner_iUnion_finite_aedisjoint _ hm hd _ _ hint_LHS,
      peterssonInner_iUnion_finite_aedisjoint _ hm hd _ _ hint_RHS]
  exact Finset.sum_congr rfl fun q _ ↦ h_per_tile q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeFD_canonical_SL_tile_balance_α_branch_from_per_tile_balance
    (α : GL (Fin 2) ℝ)
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : SLTilePairwiseAEDisjoint (N := N))
    (hm : SLTileNullMeasurable (N := N))
    (hint_LHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ))
    (hint_RHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] α) τ))
    (h_per_tile : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] α)) :
    peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g ∣[k] α) := by
  rw [peterssonInner_iUnion_finite_aedisjoint _ hm hd _ _ hint_LHS,
      peterssonInner_iUnion_finite_aedisjoint _ hm hd _ _ hint_RHS]
  exact Finset.sum_congr rfl fun q _ ↦ h_per_tile q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeFD_canonical_SL_tile_balance_α_branch_per_tile_from_per_q_fd_balance
    (α : GL (Fin 2) ℝ)
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_per_q_fd : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) =
        peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ))
          ((⇑g) ∣[k]
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))) :
    ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] α) := by
  intro q
  rw [peterssonInner_mapGL_smul_eq_slash fd ((q.out : SL(2, ℤ))⁻¹) _ _,
      peterssonInner_mapGL_smul_eq_slash fd ((q.out : SL(2, ℤ))⁻¹) _ _]
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
  exact h_per_q_fd q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeFD_canonical_SL_tile_balance_upper_per_tile_from_per_q_fd_balance_family
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_per_q_fd : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) =
        peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ))
          ((⇑g) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))) :
    ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) := by
  intro b hb
  exact heckeFD_canonical_SL_tile_balance_α_branch_per_tile_from_per_q_fd_balance
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) p hp hpN f g
    (h_per_q_fd b hb)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeFD_canonical_SL_tile_balance_α_branch_per_q_fd_from_shifted_tile_diamond_swap
    (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_shifted : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (α • (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) • (fd : Set ℍ)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            peterssonAdj α) =
      peterssonInner k
          (α • (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) • (fd : Set ℍ)))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            peterssonAdj α)
          ⇑g) :
    ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) =
        peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ))
          ((⇑g) ∣[k]
            (α * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ))) := by
  intro q
  rw [peterssonInner_slash_adjoint_coset (k := k) α hα ((q.out : SL(2, ℤ)))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g))]
  rw [peterssonInner_slash_adjoint_coset_right (k := k) α hα ((q.out : SL(2, ℤ)))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        (⇑g)]
  exact h_shifted q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeFD_canonical_SL_tile_balance_upper_from_per_tile_balance_family
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : SLTilePairwiseAEDisjoint (N := N))
    (hm : SLTileNullMeasurable (N := N))
    (hint_LHS : ∀ b ∈ Finset.range p, SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ))
    (hint_RHS : ∀ b ∈ Finset.range p, SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ))
    (h_per_tile : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
    ∀ b ∈ Finset.range p,
      peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) := by
  intro b hb
  exact heckeFD_canonical_SL_tile_balance_α_branch_from_per_tile_balance
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) p hp hpN f g
    hd hm (hint_LHS b hb) (hint_RHS b hb) (h_per_tile b hb)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem heckeFD_canonical_SL_tile_balance_from_per_tile_balances
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_LHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_RHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (h_per_tile_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)))
    (hint_T_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_T_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (h_per_tile_T : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
    heckeFD_canonical_SL_tile_balance p hp hpN f g :=
  ⟨heckeFD_canonical_SL_tile_balance_M_infty_from_per_tile_balance
      p hp hpN f g hd hm hint_M_LHS hint_M_RHS h_per_tile_M,
    heckeFD_canonical_SL_tile_balance_upper_from_per_tile_balance_family
      p hp hpN f g hd hm hint_T_LHS hint_T_RHS h_per_tile_T⟩

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_per_tile_balances
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : SLTilePairwiseAEDisjoint (N := N))
    (hm : SLTileNullMeasurable (N := N))
    (hd_M : AlphaTilePairwiseAEDisjoint (N := N) (glMap (M_infty N p hp.pos hpN)))
    (hm_M : AlphaTileNullMeasurable (N := N) (glMap (M_infty N p hp.pos hpN)))
    (hint_M_LHS : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ))
    (hint_M_RHS : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ))
    (hd_T : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (hm_T : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (hint_T_LHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ))
    (hint_T_RHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
          ⇑g τ))
    (hint_M_balance_LHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ))
    (hint_M_balance_RHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ))
    (h_per_tile_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)))
    (hint_T_balance_LHS : ∀ b ∈ Finset.range p, SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ))
    (hint_T_balance_RHS : ∀ b ∈ Finset.range p, SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ))
    (h_per_tile_T : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) =
        peterssonInner k
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
          ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_canonical_SL_balance p hp hpN f g
    hd_M hm_M hint_M_LHS hint_M_RHS
    hd_T hm_T hint_T_LHS hint_T_RHS
    (heckeFD_canonical_SL_tile_balance_from_per_tile_balances p hp hpN f g
      hd hm hint_M_balance_LHS hint_M_balance_RHS h_per_tile_M
      hint_T_balance_LHS hint_T_balance_RHS h_per_tile_T)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_per_q_fd_balances
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hd : SLTilePairwiseAEDisjoint (N := N))
    (hm : SLTileNullMeasurable (N := N))
    (hd_M : AlphaTilePairwiseAEDisjoint (N := N) (glMap (M_infty N p hp.pos hpN)))
    (hm_M : AlphaTileNullMeasurable (N := N) (glMap (M_infty N p hp.pos hpN)))
    (hint_M_LHS : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ))
    (hint_M_RHS : AlphaIntegrableUnion (N := N) (glMap (M_infty N p hp.pos hpN))
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        ⇑g τ))
    (hd_T : ∀ b ∈ Finset.range p,
      AlphaTilePairwiseAEDisjoint (N := N) (glMap (T_p_upper p hp.pos b)))
    (hm_T : ∀ b ∈ Finset.range p,
      AlphaTileNullMeasurable (N := N) (glMap (T_p_upper p hp.pos b)))
    (hint_T_LHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ))
    (hint_T_RHS : ∀ b ∈ Finset.range p,
      AlphaIntegrableUnion (N := N) (glMap (T_p_upper p hp.pos b))
        (fun τ ↦ petersson k
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
          ⇑g τ))
    (hint_M_balance_LHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ))
    (hint_M_balance_RHS : SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ))
    (h_per_q_fd_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) =
        peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ))
          ((⇑g) ∣[k]
            ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ))))
    (hint_T_balance_LHS : ∀ b ∈ Finset.range p, SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ))
    (hint_T_balance_RHS : ∀ b ∈ Finset.range p, SLTileIntegrableUnion (N := N)
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ))
    (h_per_q_fd_T : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) =
        peterssonInner k ModularGroup.fd
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ))
          ((⇑g) ∣[k]
            ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_standard_form_from_per_tile_balances p hp hpN f g
    hd hm hd_M hm_M hint_M_LHS hint_M_RHS hd_T hm_T hint_T_LHS hint_T_RHS
    hint_M_balance_LHS hint_M_balance_RHS
    (heckeFD_canonical_SL_tile_balance_α_branch_per_tile_from_per_q_fd_balance
      (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) p hp hpN f g h_per_q_fd_M)
    hint_T_balance_LHS hint_T_balance_RHS
    (heckeFD_canonical_SL_tile_balance_upper_per_tile_from_per_q_fd_balance_family
      p hp hpN f g h_per_q_fd_T)

open UpperHalfPlane ModularGroup MeasureTheory in
private def SigmaQPermResidual_M_infty
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
  ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
                M_infty_Gamma1_factor N p hpN 0)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
private def SigmaQPermResidual_upper
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    ∑ b ∈ Finset.range p,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k]
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
  ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
    ∑ b ∈ Finset.range p,
      peterssonInner k ModularGroup.fd
        (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
          ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((Gamma1QuotEquivOfGamma0
                ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                (adjointGamma0Rep p N hpN).property q).out :
                SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))

open UpperHalfPlane ModularGroup MeasureTheory in
private def TileFormIntegralResidual_M_infty
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
  peterssonInner k
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    (⇑g)

open UpperHalfPlane ModularGroup MeasureTheory in
private def TileFormIntegralResidual_upper
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) (b : ℕ)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
  peterssonInner k
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set UpperHalfPlane)))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    (⇑g)

open UpperHalfPlane ModularGroup MeasureTheory in
private def TileFormIntegralResidual_M_infty_sigma_p_reduced
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) : Prop :=
  peterssonInner k
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ)))
    ⇑f
    (((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp.pos hpN) : GL (Fin 2) ℝ)) =
  peterssonInner k
    (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) •
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ)))
    (((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp.pos hpN) : GL (Fin 2) ℝ))
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem TileFormIntegralResidual_M_infty_of_sigma_p_reduced
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : TileFormIntegralResidual_M_infty_sigma_p_reduced p hp hpN f g) :
    TileFormIntegralResidual_M_infty p hp hpN f g := by
  unfold TileFormIntegralResidual_M_infty
  rw [peterssonInner_LHS_M_infty_residual_after_sigma_p p hp.pos hpN f,
    peterssonInner_RHS_M_infty_residual_after_sigma_p p hp.pos hpN _ g]
  exact h

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem SigmaQPermResidual_M_infty_of_TileFormIntegralResidual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q₁.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q₂.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))))
    (h_LHS_int : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_RHS_int : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_tile : TileFormIntegralResidual_M_infty p hp hpN f g) :
    SigmaQPermResidual_M_infty p hp hpN f g := by
  unfold SigmaQPermResidual_M_infty
  rw [sum_peterssonInner_LHS_M_infty_to_tile_form p hp hpN f g,
    sum_peterssonInner_M_infty_tile_form_collapse p hp hpN f g h_meas h_disj h_LHS_int]
  rw [sum_peterssonInner_RHS_M_infty_to_tile_form_via_sigma p hp hpN f g]
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g)) =
      peterssonInner k
        (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g) from
    (peterssonInner_iUnion_finite_aedisjoint
      (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
      h_meas h_disj
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
      (⇑g) h_RHS_int).symm]
  exact h_tile

open UpperHalfPlane ModularGroup MeasureTheory in
private def TileFormIntegralResidual_M_infty_per_q
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ)) : Prop :=
  peterssonInner k
    ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
        (ModularGroup.fd : Set ℍ)))
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) =
  peterssonInner k
    ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ) •
        (ModularGroup.fd : Set ℍ)))
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    (⇑g)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem SigmaQPermResidual_M_infty_of_per_q_tile_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_per_q : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      TileFormIntegralResidual_M_infty_per_q p hp hpN f g (q.out : SL(2, ℤ))) :
    SigmaQPermResidual_M_infty p hp hpN f g := by
  unfold SigmaQPermResidual_M_infty
  rw [sum_peterssonInner_LHS_M_infty_to_tile_form p hp hpN f g]
  rw [sum_peterssonInner_RHS_M_infty_to_tile_form_via_sigma p hp hpN f g]
  exact Finset.sum_congr rfl fun q _ ↦ h_per_q q

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem SigmaQPermResidual_M_infty_of_sigma_p_reduced
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q₁.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q₂.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ)))))
    (h_LHS_int : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_RHS_int : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_reduced : TileFormIntegralResidual_M_infty_sigma_p_reduced p hp hpN f g) :
    SigmaQPermResidual_M_infty p hp hpN f g :=
  SigmaQPermResidual_M_infty_of_TileFormIntegralResidual p hp hpN f g
    h_meas h_disj h_LHS_int h_RHS_int
    (TileFormIntegralResidual_M_infty_of_sigma_p_reduced p hp hpN f g h_reduced)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **LHS per-`b` tile collapse** for `SigmaQPermResidual_upper`: each inner per-`q`
sum over the upper tiles collapses to the integral over the AE-disjoint `iUnion`. -/
private theorem sum_peterssonInner_LHS_upper_per_b_tiles_to_iUnion
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q₁.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set ℍ)))
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q₂.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set ℍ)))))
    (h_LHS_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp) :
    (∑ b ∈ Finset.range p,
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))) =
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
              ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) :=
  Finset.sum_congr rfl (fun b hb ↦ sum_peterssonInner_upper_tile_form_per_b_collapse p hp hpN b hb f g
      (fun q ↦ h_meas b hb q) (h_disj b hb) (h_LHS_int b hb))

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **RHS per-`b` tile collapse** for `SigmaQPermResidual_upper`: the prefactored
double-sum (after `sum_comm`) collapses per `b` to the integral over the AE-disjoint
`iUnion`. -/
private theorem sum_peterssonInner_RHS_upper_prefactored_to_iUnion
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q₁.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set ℍ)))
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q₂.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set ℍ)))))
    (h_RHS_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k ModularGroup.fd
          (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹))
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) g) ∣[k]
            ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))) =
      ∑ b ∈ Finset.range p,
        peterssonInner k
          (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
              ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
                (ModularGroup.fd : Set UpperHalfPlane)))
          ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
              (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
          (⇑g) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b hb ↦ ?_)
  rw [sum_peterssonInner_RHS_upper_to_tile_form_via_sigma_per_b p hp hpN b f g]
  exact (peterssonInner_iUnion_finite_aedisjoint
    (fun q : SL(2, ℤ) ⧸ Gamma1 N ↦ (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (ModularGroup.fd : Set ℍ)))
    (fun q ↦ h_meas b hb q) (h_disj b hb)
    ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
    (⇑g) (h_RHS_int b hb)).symm

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem SigmaQPermResidual_upper_of_TileFormIntegralResidual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q₁.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set ℍ)))
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q₂.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (ModularGroup.fd : Set ℍ)))))
    (h_LHS_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_RHS_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))))
        (⇑g) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set ℍ))) μ_hyp)
    (h_tile : ∀ b ∈ Finset.range p,
      TileFormIntegralResidual_upper p hp hpN b f g) :
    SigmaQPermResidual_upper p hp hpN f g := by
  unfold SigmaQPermResidual_upper
  rw [sum_peterssonInner_LHS_upper_to_tile_form p hp hpN f g,
    sum_peterssonInner_upper_tile_form_swap p hp hpN f g,
    sum_peterssonInner_LHS_upper_per_b_tiles_to_iUnion p hp hpN f g
      h_meas h_disj h_LHS_int,
    sum_peterssonInner_RHS_upper_prefactored_to_iUnion p hp hpN f g
      h_meas h_disj h_RHS_int]
  exact Finset.sum_congr rfl (fun b hb ↦ h_tile b hb)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **CORRECTED leaf 1** — LHS to the proven global aggregate's LHS.
`petN(T_p f, g) = c_N • ⟨Γ₁-FD⟩ (Σᵢ f∣β_i) g`, where `β_i` ranges over the full Hecke
family `{M_∞} ⊔ {T_p_upper b}` (DS: `Σᵢ f∣β_i = f[ΓαΓ]_k = T_p f`), and
`c_N = slToPslQuot_fiberCard N`. The fiber-count factor is forced because `petN` is the
integral over the *SL*-coset fundamental domain (`[SL:Γ₁(N)]` tiles), while
`peterssonInner k (Gamma1_fundDomain_PSL N)` is the integral over the *PSL*-coset
fundamental domain (`[PSL:imageΓ₁(N)]` tiles), the two differing by the uniform fiber
count `c_N = [SL/Γ₁ : PSL/imageΓ₁]` (`= 1` iff `-I ∈ Γ₁(N)`). The aggregate identity at
line 202 is at the PSL level (fiber-count-free) on both sides, so the `c_N •` carried here
cancels the matching `c_N •` of leaf 2.
Route (BUILD, bounded): `petN_eq_setIntegral_Gamma1_fundDomain_PSL` (the `c_N • ∫_{D₁}`
form of `petN`) + `heckeT_p_fun_eq_coset_sum` (the family-sum form of `T_p`). -/
private theorem petN_heckeT_p_LHS_eq_aggregate
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
    slToPslQuot_fiberCard N • peterssonInner k (Gamma1_fundDomain_PSL N)
      (∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) ⇑g := by
  have h_fun : (⇑(heckeT_p_cusp k p hp hpN f) : ℍ → ℂ) =
      ∑ i ∈ (Finset.univ : Finset (Option (Fin p))),
        ⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) := by
    have h_Tpf : (⇑(heckeT_p_cusp k p hp hpN f) : ℍ → ℂ) =
        heckeT_p_ut k p hp.pos ⇑f.toModularForm' +
          ⇑f.toModularForm' ∣[k] (M_infty N p hp.pos hpN : GL (Fin 2) ℚ) :=
      heckeT_p_fun_eq_coset_sum k hp hpN f.toModularForm'
    rw [Fintype.sum_option, h_Tpf, add_comm]
    refine congr_arg₂ (· + ·) rfl ?_
    rw [show heckeT_p_ut k p hp.pos ⇑f.toModularForm' =
        ∑ b ∈ Finset.range p,
          ⇑f.toModularForm' ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) from rfl,
      ← Fin.sum_univ_eq_sum_range
        (fun b ↦ ⇑f.toModularForm' ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ))]
    rfl
  rw [petN_eq_setIntegral_Gamma1_fundDomain_PSL, peterssonInner, h_fun]

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `β • Γ₁`-PSL-FD set is null-measurable whenever `β` has positive `GL(2,ℝ)`
determinant, via the `β⁻¹`-pullback of the `Γ₁(N)` FD (a measure-preserving map). -/
private lemma nullMeasurableSet_glPos_smul_Gamma1_fundDomain_PSL
    {β : GL (Fin 2) ℝ} (hβ : 0 < β.det.val) :
    NullMeasurableSet (β • (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
  have hinv : 0 < (β⁻¹).det.val := by
    rw [map_inv, Units.val_inv_eq_inv_val]; exact inv_pos.mpr hβ
  have h_eq : (β • (Gamma1_fundDomain_PSL N : Set ℍ)) =
      ((β⁻¹ • ·) : ℍ → ℍ) ⁻¹' (Gamma1_fundDomain_PSL N : Set ℍ) := by
    ext τ; simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [h_eq]
  exact isFundamentalDomain_Gamma1_PSL.nullMeasurableSet.preimage
    (measurePreserving_glPos_smul _ hinv).quasiMeasurePreserving

open UpperHalfPlane ModularGroup MeasureTheory in
/-- The `α_T_p` family aggregate has finite hyperbolic measure: each tile
`β_i • Γ₁-FD` has finite measure (via `measure_glPos_smul_Gamma1_fundDomain_lt_top`)
and the family is finite. -/
private lemma measure_α_T_p_family_aggregate_lt_top
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    μ_hyp (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
      (match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) < ⊤ := by
  simp only [Finset.mem_univ, Set.iUnion_true]
  refine (measure_iUnion_le _).trans_lt ?_
  rw [tsum_fintype]
  refine ENNReal.sum_lt_top.mpr fun i _ ↦ ?_
  cases i with
  | none =>
    exact measure_glPos_smul_Gamma1_fundDomain_lt_top _
      (glMap_M_infty_det_pos N p hp.pos hpN)
  | some b =>
    exact measure_glPos_smul_Gamma1_fundDomain_lt_top _
      (glMap_T_p_upper_det_pos p hp.pos b.val)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **CORRECTED leaf 3** — the family-aggregate measure hypotheses for invoking the proven
`peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD_PSL_R` (line 202): per-`i`
`NullMeasurableSet` of each `β_i•Γ₁-FD`, per-`i` `IntegrableOn` of the swapped kernel on
`Γ₁-FD`, and `IntegrableOn` of the forward kernel on the family `iUnion`.
Route (BUILD, bounded): `nullMeasurableSet`/`integrableOn` engines already used at
DeltaBSystem:1666–1736 and the `Γ_p(α)`/PSL fundamental-domain measurability of FDTransport. -/
private theorem aggregate_HeckeFD_measure_hyps
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      NullMeasurableSet ((match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp) ∧
    (∀ i ∈ (Finset.univ : Finset (Option (Fin p))),
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑f ∣[k] (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ))) τ)
        (Gamma1_fundDomain_PSL N) μ_hyp) ∧
    IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) μ_hyp := by
  refine ⟨?_, ?_, ?_⟩
  · intro i _
    cases i with
    | none =>
      exact nullMeasurableSet_glPos_smul_Gamma1_fundDomain_PSL
        (glMap_M_infty_det_pos N p hp.pos hpN)
    | some b =>
      exact nullMeasurableSet_glPos_smul_Gamma1_fundDomain_PSL
        (glMap_T_p_upper_det_pos p hp.pos b.val)
  · intro i _
    cases i with
    | none =>
      exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure g f
        (M_infty N p hp.pos hpN)
        (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N))
    | some b =>
      exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure g f
        (T_p_upper p hp.pos b.val)
        (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N))
  · exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g
      (T_p_lower p hp.pos) (measure_α_T_p_family_aggregate_lt_top p hp hpN)

open UpperHalfPlane ModularGroup MeasureTheory in
/-- **RHS aggregate expansion (Hermitian mirror of leaf 1).** Expands the *right*-hand
side `petN(⟨p⟩f, T_p g)` of the symmetric form onto the SAME single-tile aggregate domain
`⋃_i β_i • Γ₁-FD` as the proven LHS aggregate, with the slots arranged as
`((⟨p⟩f)∣T_p_lower)` against `g`.

Route (PROVEN wiring, NO double-coset content): conjugate-Hermitian symmetry
`petN_conj_symm` turns `petN(⟨p⟩f, T_p g)` into `conj(petN(T_p g, ⟨p⟩f))`; the proven
leaf 1 (`petN_heckeT_p_LHS_eq_aggregate`) + the proven aggregate
(`peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD`, fed
`aggregate_HeckeFD_measure_hyps`), applied with `f := g`, `g := ⟨p⟩f`, rewrites this to
`conj(c_N • ⟨⋃_i β_i•Γ₁-FD⟩ g ((⟨p⟩f)∣T_p_lower))`; finally `conj` distributes over the
ℕ-scalar (`map_nsmul`) and swaps the two `peterssonInner` slots (`peterssonInner_conj_symm`).
This is purely the Hermitian-symmetric mirror of leaf 1. -/
private theorem petN_heckeT_p_RHS_eq_aggregate
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) (heckeT_p_cusp k p hp hpN g) =
    slToPslQuot_fiberCard N • peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
        (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ))
      ⇑g := by
  set Df := diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f with hDf
  obtain ⟨hm, h_int_per, hfi⟩ := aggregate_HeckeFD_measure_hyps p hp hpN g Df
  have h_LHS_swapped :
      petN (heckeT_p_cusp k p hp hpN g) Df =
      slToPslQuot_fiberCard N • peterssonInner k
        (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
          (match i with
            | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
            | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
            (Gamma1_fundDomain_PSL N : Set ℍ))
        ⇑g (⇑Df ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
    rw [petN_heckeT_p_LHS_eq_aggregate p hp hpN g Df,
      peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD p hp hpN g Df hm h_int_per hfi]
  rw [← petN_conj_symm Df (heckeT_p_cusp k p hp hpN g), h_LHS_swapped, map_nsmul,
    peterssonInner_conj_symm]

/-- `glMap (T_p_lower p hp) = (T_p_lower p hp).map (Rat.castHom ℝ)` (the `glMap`/`.map`
identification connecting the residual's slash matrix `A = diag(p,1)` to the `Γ_p(α)` API,
which is phrased over `α.map (Rat.castHom ℝ)`). -/
private lemma glMap_T_p_lower_eq_map_castHom (p : ℕ) (hp : 0 < p) :
    (glMap (T_p_lower p hp) : GL (Fin 2) ℝ) =
      ((T_p_lower p hp).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) := rfl

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane ModularGroup MeasureTheory in
/-- **Γ_p(A)-invariance of the W5b integrand.** For `A = diag(p,1)`, the kernel
`pet f (g∣A)` is invariant under the (SL-level) action of `Γ_p(A) = A⁻¹Γ₁A ∩ Γ₁`: `f` is
`Γ₁`-invariant hence `Γ_p(A)`-invariant, and `g∣A` is `Γ_p(A)`-invariant
(`slash_α_Gamma_p_α_invariant_cuspForm`, FDT:152). -/
private lemma petersson_f_slash_T_p_lower_Gamma_p_invariant
    (p : ℕ) (hp : Nat.Prime p) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos)) (τ : ℍ) :
    petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) (γ • τ) =
      petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ := by
  rw [← petersson_slash_SL]
  congr 1
  · exact slash_Gamma1_eq f γ ((Gamma_p_α_le_Gamma1 _) hγ)
  · rw [ModularForm.SL_slash, glMap_T_p_lower_eq_map_castHom]
    exact slash_α_Gamma_p_α_invariant_cuspForm (T_p_lower p hp.pos) g hγ

open CongruenceSubgroup Pointwise ConjAct UpperHalfPlane ModularGroup MeasureTheory in
/-- **W5b — the FD transfer (the consumable for W5c).** GIVEN the fundamental-domain
property of the Hecke aggregate domain `D = ⋃_i β_i • Γ₁-FD` for `Γ_p(A) = A⁻¹Γ₁A ∩ Γ₁`
(`A = diag(p,1)`), the Petersson integral over `D` transfers to the integral over the
canonical `Γ_p(A)` fundamental domain `Gamma_p_α_fundDomain_PSL A`:
```
⟨D⟩ f (g∣A) = ∫_{Γ_p(A)-FD} pet f (g∣A).
```
Both are FDs for the **same** group `(Γ_p(A)).map SL2Z_to_PSL2R` (the latter via FDT:860),
and the integrand `pet f (g∣A)` is `Γ_p(A)`-invariant
(`petersson_f_slash_T_p_lower_Gamma_p_invariant`), so the two integrals coincide by
`IsFundamentalDomain.setIntegral_eq`. This is the exact form the trace engine FDT:1612
consumes: it puts `⟨D⟩ f (g∣A)` into `∫_{Γ_p(A)-FD}` shape, where the engine fires.

The hypothesis `hFD` is the residual **W5a-2 crux** — that the `p+1` det-`p` Hecke tiles
`β_i • Γ₁-FD` tile `Γ_p(A)\ℍ` (the covering/transversal half; the AE-disjoint half is
`aedisjoint_pairwise_T_p_family`, SA:1431, and the index is `p+1` via
`slGamma_p_αToGamma1_fiberCard_T_p_lower`). See the HARD-STOP note on
`heckeT_p_aggregate_peeled_diagonal_balance`. -/
theorem aggregate_D_petersson_eq_Gamma_p_A_fundDomain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hFD : IsFundamentalDomain
      (((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R))
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp) :
    peterssonInner k
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) =
    ∫ τ in Gamma_p_α_fundDomain_PSL (N := N) (T_p_lower p hp.pos),
      petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ ∂μ_hyp := by
  rw [peterssonInner]
  refine hFD.setIntegral_eq
    (isFundamentalDomain_Gamma_p_α_fundDomain_PSL_at_PSL_R (N := N) (T_p_lower p hp.pos))
    (fun gp τ ↦ ?_)
  exact inv_under_Gamma_p_α_PSL_R_of_inv_under_Gamma_p_α (N := N) (T_p_lower p hp.pos)
    (fun γ hγ τ ↦ petersson_f_slash_T_p_lower_Gamma_p_invariant p hp f g hγ τ) gp τ

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **`hFD` discharged.** The fundamental-domain hypothesis of
`aggregate_D_petersson_eq_Gamma_p_A_fundDomain` is exactly the W5a-2 Hecke-tile FD
identification `isFundamentalDomain_Hecke_tiles_Gamma_p_α` (DeltaBSystem), modulo the
`⋃ i ∈ univ ↔ ⋃ i` biUnion/iUnion reshape. -/
theorem isFundamentalDomain_Hecke_tiles_biUnion_Gamma_p_α
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    IsFundamentalDomain
      (((Gamma_p_α (N := N) (T_p_lower p hp.pos)).map SL2Z_to_PSL2R))
      (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ))
      μ_hyp := by
  have hset : (⋃ i ∈ (Finset.univ : Finset (Option (Fin p))),
      (match i with
        | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
        | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
        (Gamma1_fundDomain_PSL N : Set ℍ)) =
      (⋃ i : Option (Fin p),
        (match i with
          | none => (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)
          | some b => (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
          (Gamma1_fundDomain_PSL N : Set ℍ)) := by
    refine Set.iUnion_congr fun i ↦ ?_
    cases i <;> simp
  rw [hset]
  exact isFundamentalDomain_Hecke_tiles_Gamma_p_α p hp hpN

/-! ### DIRECT (non-circular) DS 5.5.3 route via the `Γ_p(A)` trace engine

The chain below proves `petN(T_p f, g) = petN(f, ⟨p⟩⁻¹ T_p g)` ONE-DIRECTIONALLY, without
assuming the symmetric form `petN_heckeT_p_symmetric_form_doubleCoset` (the residual at
`heckeT_p_aggregate_peeled_diagonal_balance`). It chains:
* leaf 1 (`petN_heckeT_p_LHS_eq_aggregate`),
* the proven aggregate (`peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD`),
* the Hecke-tile FD identification (`aggregate_D_petersson_eq_Gamma_p_A_fundDomain` +
  `isFundamentalDomain_Hecke_tiles_biUnion_Gamma_p_α`),
* the degree-`(p+1)` **trace engine**
  (`setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain`,
  FDTransport),
* the **trace leaf** `traceSlash_T_p_lower_eq_diamond_inv_heckeT_p` (form-level, the genuine
  DS 5.5.3 content), and
* `petN_eq_setIntegral_Gamma1_fundDomain_PSL`. -/

/-- Center elements of `SL(2,ℤ)` have lower-left entry `0`, so `Γ_p(A)`- and `Γ₁`-membership
agree on the center (used for the fiber-count reconciliation). -/
private theorem center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2, ℤ)) :
    z ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) ↔ z ∈ Gamma1 N := by
  rw [mem_Gamma_p_α_T_p_lower p hp.pos hpN]
  refine ⟨fun h ↦ h.1, fun h ↦ ⟨h, ?_⟩⟩
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hz
  obtain ⟨c, _, hc⟩ := hz
  have : (z : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    rw [← hc, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ (by decide)]
  rw [this]; exact dvd_zero _

/-- Fiber-membership characterization at `[1]` (uniform across any congruence subgroup
`H ≤ SL(2,ℤ)`): the double PSL-quotient lands at the identity iff there is a central
representative `z` with `g * z ∈ H`. -/
private theorem pslQuot_eq_one_iff_exists_center_mem
    (H : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    (QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ (H.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))) =
      QuotientGroup.mk 1 ↔
    ∃ z ∈ Subgroup.center SL(2, ℤ), g * z ∈ H := by
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhe⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hhe
    refine ⟨g⁻¹ * h, ?_, by group; exact hh⟩
    have := (Subgroup.center SL(2, ℤ)).inv_mem hhe
    rwa [mul_inv_rev, inv_inv] at this
  · rintro ⟨z, hz, hgz⟩
    exact ⟨g * z, hgz, by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff _).mpr hz, mul_one]⟩

/-- Center crux: for `g₁, g₂` whose `Γ_p(A)`-fiber membership holds
(`gᵢ·zᵢ ∈ Γ_p(A)`, `zᵢ ∈ center`), the `Γ₁`- and `Γ_p(A)`-cosets of `g₁⁻¹g₂` coincide
(the discrepancy lies in the center, where the two memberships agree by
`center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1`). -/
private theorem Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g₁ g₂ z₁ z₂ : SL(2, ℤ))
    (hz₁ : z₁ ∈ Subgroup.center SL(2, ℤ))
    (hz₂ : z₂ ∈ Subgroup.center SL(2, ℤ))
    (hg₁ : g₁ * z₁ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos))
    (hg₂ : g₂ * z₂ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos)) :
    g₁⁻¹ * g₂ ∈ Gamma1 N ↔ g₁⁻¹ * g₂ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) := by
  have hzc : z₁ * z₂⁻¹ ∈ Subgroup.center SL(2, ℤ) :=
    (Subgroup.center SL(2, ℤ)).mul_mem hz₁ ((Subgroup.center SL(2, ℤ)).inv_mem hz₂)
  have hz₁i : z₁⁻¹ ∈ Subgroup.center SL(2, ℤ) := (Subgroup.center SL(2, ℤ)).inv_mem hz₁
  have hz₂i : z₂⁻¹ ∈ Subgroup.center SL(2, ℤ) := (Subgroup.center SL(2, ℤ)).inv_mem hz₂
  have hcz₁ : ∀ x : SL(2, ℤ), z₁⁻¹ * x = x * z₁⁻¹ :=
    fun x ↦ (Subgroup.mem_center_iff.mp hz₁i x).symm
  have hcz₂ : ∀ x : SL(2, ℤ), z₂⁻¹ * x = x * z₂⁻¹ :=
    fun x ↦ (Subgroup.mem_center_iff.mp hz₂i x).symm
  have hsplit : g₁⁻¹ * g₂ = (g₁ * z₁)⁻¹ * ((z₁ * z₂⁻¹) * (g₂ * z₂)) := by
    rw [mul_inv_rev]
    symm
    calc (z₁⁻¹ * g₁⁻¹) * ((z₁ * z₂⁻¹) * (g₂ * z₂))
        = g₁⁻¹ * z₁⁻¹ * (z₁ * (z₂⁻¹ * (g₂ * z₂))) := by rw [hcz₁ g₁⁻¹]; group
      _ = g₁⁻¹ * (z₂⁻¹ * (g₂ * z₂)) := by rw [← mul_assoc, mul_assoc _ z₁⁻¹ z₁,
          inv_mul_cancel, mul_one]
      _ = g₁⁻¹ * (g₂ * (z₂⁻¹ * z₂)) := by rw [hcz₂ (g₂ * z₂)]; group
      _ = g₁⁻¹ * g₂ := by rw [inv_mul_cancel, mul_one]
  rw [hsplit]
  have hL₁ : (g₁ * z₁)⁻¹ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) :=
    (Gamma_p_α (N := N) (T_p_lower p hp.pos)).inv_mem hg₁
  refine ⟨fun h ↦ ?_, fun h ↦ (Gamma_p_α_le_Gamma1 _) h⟩
  have hmid : (z₁ * z₂⁻¹) * (g₂ * z₂) ∈ Gamma1 N := by
    have h2 := (Gamma1 N).mul_mem ((Gamma_p_α_le_Gamma1 _) hg₁) h
    rwa [← mul_assoc, mul_inv_cancel, one_mul] at h2
  have hz_mem : z₁ * z₂⁻¹ ∈ Gamma1 N := by
    have h2 := (Gamma1 N).mul_mem hmid ((Gamma1 N).inv_mem ((Gamma_p_α_le_Gamma1 _) hg₂))
    rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
  have hz_memP : z₁ * z₂⁻¹ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos) :=
    (center_mem_Gamma_p_α_T_p_lower_iff_mem_Gamma1 p hp hpN hzc).mpr hz_mem
  exact (Gamma_p_α (N := N) (T_p_lower p hp.pos)).mul_mem hL₁
    ((Gamma_p_α (N := N) (T_p_lower p hp.pos)).mul_mem hz_memP hg₂)

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- The map `slGamma_p_αToGamma1 (T_p_lower)` sends the `Γ_p(A)`-fiber of `[1]` into the
`Γ₁`-fiber of `[1]`: a `Γ_p(A)`-fiber witness `z ∈ center, g·z ∈ Γ_p(A)` maps to the same
`z` with `g·z ∈ Γ₁(N)` via `Gamma_p_α_le_Gamma1`. -/
private theorem slGamma_p_αToGamma1_maps_into_Gamma1_fiber
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos))
    (hq : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos))) :
    slToPslQuot (N := N) (slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q) =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ imageGamma1_PSL N) := by
  induction q using QuotientGroup.induction_on with | _ g => ?_
  rw [slToPslQuot_Gamma_p_α_mk] at hq
  rw [slGamma_p_αToGamma1_mk, slToPslQuot_mk]
  obtain ⟨z, hz, hgz⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g).mp hq
  exact (pslQuot_eq_one_iff_exists_center_mem _ g).mpr
    ⟨z, hz, (Gamma_p_α_le_Gamma1 _) hgz⟩

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- The map `slGamma_p_αToGamma1 (T_p_lower)` is injective on the `Γ_p(A)`-fiber of `[1]`,
via `Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber`. -/
private theorem slGamma_p_αToGamma1_injective_on_Gamma_p_α_fiber
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q₁ q₂ : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos))
    (hq₁ : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) q₁ =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos)))
    (hq₂ : slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) q₂ =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos)))
    (heq : slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q₁ =
      slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q₂) :
    q₁ = q₂ := by
  induction q₁ using QuotientGroup.induction_on with | _ g₁ => ?_
  induction q₂ using QuotientGroup.induction_on with | _ g₂ => ?_
  rw [slToPslQuot_Gamma_p_α_mk] at hq₁ hq₂
  rw [slGamma_p_αToGamma1_mk, slGamma_p_αToGamma1_mk, QuotientGroup.eq] at heq
  obtain ⟨z₁, hz₁, hgz₁⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g₁).mp hq₁
  obtain ⟨z₂, hz₂, hgz₂⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g₂).mp hq₂
  rw [QuotientGroup.eq]
  exact (Gamma1_coset_iff_Gamma_p_α_coset_of_center_fiber p hp hpN g₁ g₂ z₁ z₂
    hz₁ hz₂ hgz₁ hgz₂).mp heq

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- The map `slGamma_p_αToGamma1 (T_p_lower)` is surjective onto the `Γ₁`-fiber of `[1]`:
the center part `z⁻¹` of any `Γ₁`-fiber rep `g` gives the corresponding `Γ_p(A)`-fiber rep
(since `z * g = g * z` by centrality, and `(z⁻¹)⁻¹·g = g·z ∈ Γ₁(N)`). -/
private theorem slGamma_p_αToGamma1_surjective_onto_Gamma1_fiber
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (hq : slToPslQuot (N := N) q =
      (QuotientGroup.mk (1 : PSL(2, ℤ)) :
        PSL(2, ℤ) ⧸ imageGamma1_PSL N)) :
    ∃ a : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      slToPslQuot_Gamma_p_α (N := N) (T_p_lower p hp.pos) a =
        (QuotientGroup.mk (1 : PSL(2, ℤ)) :
          PSL(2, ℤ) ⧸ image_Gamma_p_α_PSL (N := N) (T_p_lower p hp.pos)) ∧
      slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) a = q := by
  induction q using QuotientGroup.induction_on with | _ g => ?_
  rw [slToPslQuot_mk] at hq
  obtain ⟨z, hz, hgz⟩ := (pslQuot_eq_one_iff_exists_center_mem _ g).mp hq
  refine ⟨QuotientGroup.mk z⁻¹, ?_, ?_⟩
  · rw [slToPslQuot_Gamma_p_α_mk]
    refine (pslQuot_eq_one_iff_exists_center_mem _ z⁻¹).mpr ⟨z, hz, ?_⟩
    rw [inv_mul_cancel]
    exact (Gamma_p_α (N := N) (T_p_lower p hp.pos)).one_mem
  · rw [slGamma_p_αToGamma1_mk, QuotientGroup.eq]
    have hcomm : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
    rw [inv_inv, hcomm]; exact hgz

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **Fiber-count reconciliation.** The `SL → PSL` fiber count at `Γ_p(diag(p,1))` equals the
one at `Γ₁(N)`. Both count `[H·{±I} : H]` over the respective `H`, which is `1` or `2`
according to whether `-I ∈ H`; and `-I ∈ Γ_p(A) ↔ -I ∈ Γ₁(N)` (the `(1,0)`-entry of `-I` is
`0`, divisible by `p`). This is the `c_p`-vs-`c_N` bridge that lets leaf 1's `c_N`-weighted
`Γ_p(A)`-FD integral feed the trace engine (which carries `c_p`). -/
theorem slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N) :
    slToPslQuot_fiberCard_Gamma_p_α (N := N) (T_p_lower p hp.pos) =
      slToPslQuot_fiberCard N := by
  classical
  rw [slToPslQuot_fiberCard_Gamma_p_α, slToPslQuot_fiberCard]
  refine Finset.card_bij
    (fun q _ ↦ slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q) ?_ ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact slGamma_p_αToGamma1_maps_into_Gamma1_fiber p hp hpN q hq
  · intro q₁ hq₁ q₂ hq₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
    exact slGamma_p_αToGamma1_injective_on_Gamma_p_α_fiber p hp hpN q₁ q₂ hq₁ hq₂ heq
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨a, ha₁, ha₂⟩ := slGamma_p_αToGamma1_surjective_onto_Gamma1_fiber p hp hpN q hq
    exact ⟨a, by simp [ha₁], ha₂⟩

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **TRACE LEAF (DS 5.5.3, form-level) — the single genuine remaining gap.** Summing `g ∣ A`
over a transversal of `Γ_p(A)\Γ₁(N)` (`A = diag(p,1)`, `[Γ₁ : Γ_p(A)] = p+1`) yields the
*adjoint* Hecke operator `⟨p⟩⁻¹ T_p g`. Precisely, the partial trace
`traceSlash_Gamma_p_α A (g∣A) q₀` equals `⇑(⟨p⟩⁻¹ T_p g)` as a function `ℍ → ℂ` (independent
of the base coset `q₀`).

NON-CIRCULAR: this is a pure slash/coset identity — `traceSlash_Gamma_p_α`, `glMap`,
`diamondOp_cusp`, `heckeT_p_cusp` are all defined strictly *before* `heckeT_p_adjoint`
(in `FDTransport`/`Gamma1Pair`/`AdjointTheory`), and the statement mentions neither
`petersson`, `petN`, nor `heckeT_p_adjoint`. So `heckeT_p_adjoint`'s proof (which uses this
leaf) does not loop through itself.

MATH: the double coset `Γ₁ A Γ₁` with `A = diag(p,1)` is the *adjoint* of the standard `T_p`
coset `Γ₁ diag(1,p) Γ₁` (`diag(p,1) = det(diag(1,p))·diag(1,p)⁻¹`), and DS Thm 5.5.3 gives
`g[Γ₁ A Γ₁]_k = ⟨p⟩⁻¹ T_p g`.

PROOF SKELETON (the precise residual gap; two ordered sub-lemmas):
1. `traceSlash_Gamma_p_α A (g∣A) q₀ = ∑_{j} (g∣A) ∣[k] δ_j` over a CONCRETE transversal
   `{δ_j}` (`p+1` elements) of `Γ_p(A)\Γ₁` — where `Γ_p(A) = {γ∈Γ₁ : p ∣ γ₁₀}`
   (`mem_Gamma_p_α_T_p_lower`, the `Γ₀(p)`-type lower-left condition). A correct transversal is
   the `Γ₀(p)\Γ₁`-style lower reps (e.g. `[[1,0],[j,1]]·(level corrector)` for `j=0..p-1`
   plus an `S`-type rep). NB: `T_p_lower_tile_family` (DeltaB:687) is NOT this transversal —
   it is the transversal of the *conjugate* group `Γ₁ ∩ AΓ₁A⁻¹` (the `A•D` decomposition),
   a different coset space; building the `Γ_p(A)\Γ₁` transversal is part of this gap. The
   bridge is a `Finset.sum_bij` from the abstract fiber `{q : slGamma_p_αToGamma1 A q = q₀}`
   to `{δ_j}`, with the `Γ_p(A)`-slash-invariance of `g∣A`
   (`slash_α_Gamma_p_α_invariant_cuspForm`) absorbing the per-coset discrepancy; base-coset
   independence is `traceSlash_Gamma_p_α_indep`.
2. `∑_j (g∣A) ∣[k] δ_j = ∑_j g ∣[k] (A·δ_j) = ⇑(⟨p⟩⁻¹ T_p g)`. The matrices `{A·δ_j}` (det-`p`)
   are left-coset reps of `Γ₁\Γ₁ A Γ₁`, the *adjoint* of the standard `T_p` double coset
   `Γ₁ diag(1,p) Γ₁` (`diag(p,1) = det(diag(1,p))·diag(1,p)⁻¹`); recombine into the adjoint
   family via `heckeT_p_fun_eq_coset_sum` (HeckeT_p_Gamma1:307), `heckeT_p_comm_diamondOp`
   (HeckeT_p:1013), `glMap_M_infty_eq_mapGL_sigma_p_mul_glMap_T_p_lower` (SA:303), and the
   diamond/slash commutation. This is the genuine DS 5.5.3 / Miyake 4.5.4 content. -/
theorem traceSlash_T_p_lower_eq_diamond_inv_heckeT_p
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀ =
    ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ (heckeT_p_cusp k p hp hpN g)) :=
  ds_traceSlash_Gamma_p_α_T_p_lower_eq_diamond_inv_heckeT_p p hp hpN g q₀

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- Integrability of `pet f ((g∣A)∣γ)` (`γ : SL(2,ℤ)`) over any finite-measure set: the
slash-by-`A`-then-`γ` collapses to `g ∣ glMap(A · γ)`. -/
private theorem integrableOn_petersson_slash_T_p_lower_slash_SL
    (p : ℕ) (hp : Nat.Prime p)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (γ : SL(2, ℤ))
    {S : Set ℍ} (hS : μ_hyp S < ⊤) :
    IntegrableOn (fun τ ↦ petersson k ⇑f
      ((⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ))) τ)
      S μ_hyp := by
  have hσ : (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ)) =
      ⇑g ∣[k] (glMap (T_p_lower p hp.pos * mapGL ℚ γ) : GL (Fin 2) ℝ) := by
    rw [ModularForm.SL_slash, map_mul, ← SlashAction.slash_mul]; rfl
  rw [hσ]
  exact integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g
    (T_p_lower p hp.pos * mapGL ℚ γ) hS

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- Integrability of `pet f (g∣A)` on the canonical `Γ_p(A)`-FD (engine hyp `h_int`). -/
private theorem h_int_FD (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (Gamma_p_α_fundDomain_PSL_canonical (N := N) (T_p_lower p hp.pos)) μ_hyp :=
  integrableOn_petersson_cuspform_slash_glMap_of_finiteMeasure f g (T_p_lower p hp.pos)
    (hyperbolicMeasure_Gamma_p_α_fundDomain_PSL_canonical_lt_top (N := N) (T_p_lower p hp.pos))

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Per-fiber integrability of the slashed trace summand (engine hyp `h_int_trace`). -/
private theorem h_int_trace_FD (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (_q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    TraceFiberIntegrable (N := N) (k := k) (T_p_lower p hp.pos) ⇑f
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) := by
  intro q' q _
  refine integrableOn_petersson_slash_T_p_lower_slash_SL p hp f g
    ((q.out : SL(2, ℤ))⁻¹ * q'.out) ?_
  rw [← Set.preimage_smul (q'.out : SL(2, ℤ)) (fd : Set ℍ), measure_preimage_smul]
  exact hyperbolicMeasure_fd_lt_top

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory Classical in
/-- Integrability of `pet f (tr_{q₀}(g∣A))` on the `Γ₁`-FD (engine hyp `h_int_tr`). -/
private theorem h_int_tr_FD (p : ℕ) (hp : Nat.Prime p) (_hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q₀ : SL(2, ℤ) ⧸ Gamma1 N) :
    IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
          (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀) τ)
      (Gamma1_fundDomain_PSL N) μ_hyp := by
  have h_fun : (fun τ ↦ petersson k ⇑f
      (traceSlash_Gamma_p_α (N := N) (k := k) (T_p_lower p hp.pos)
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀) τ) =
      fun τ ↦ ∑ q ∈ Finset.univ.filter
        (fun q : SL(2, ℤ) ⧸ Gamma_p_α (N := N) (T_p_lower p hp.pos) =>
          slGamma_p_αToGamma1 (N := N) (T_p_lower p hp.pos) q = q₀),
        petersson k ⇑f
          ((⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹ * q₀.out)) τ := by
    funext τ
    rw [traceSlash_Gamma_p_α, petersson_sum_right]
  rw [h_fun]
  refine MeasureTheory.integrable_finset_sum _ fun q _ ↦ ?_
  exact integrableOn_petersson_slash_T_p_lower_slash_SL p hp f g
    ((q.out : SL(2, ℤ))⁻¹ * q₀.out)
    (hyperbolicMeasure_Gamma1_fundDomain_PSL_lt_top (N := N))

open CongruenceSubgroup Pointwise UpperHalfPlane ModularGroup MeasureTheory in
/-- **DIRECT chain assembler (non-circular).** `petN(T_p f, g) = petN(f, ⟨p⟩⁻¹ T_p g)` via the
trace engine, assuming `heckeT_p_adjoint`/`symmetric_form` NOWHERE. -/
private theorem petN_heckeT_p_adjoint_via_trace
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  -- Base coset for the (coset-independent) trace.
  set q₀ : SL(2, ℤ) ⧸ Gamma1 N := QuotientGroup.mk 1 with hq₀
  obtain ⟨hm, h_int_per, hfi⟩ := aggregate_HeckeFD_measure_hyps p hp hpN f g
  -- F is `Γ₁`-slash-invariant; G = g∣A is `Γ_p(A)`-slash-invariant.
  have hF_slash : ∀ γ ∈ Gamma1 N, (⇑f : ℍ → ℂ) ∣[k] (γ : SL(2, ℤ)) = ⇑f :=
    fun γ hγ ↦ slash_Gamma1_eq f γ hγ
  have hG_slash : ∀ γ ∈ Gamma_p_α (N := N) (T_p_lower p hp.pos),
      (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) ∣[k] (γ : SL(2, ℤ)) =
        ⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) := by
    intro γ hγ
    rw [ModularForm.SL_slash, glMap_T_p_lower_eq_map_castHom]
    exact slash_α_Gamma_p_α_invariant_cuspForm (T_p_lower p hp.pos) g hγ
  -- LHS: leaf 1 + aggregate + Hecke-tile FD identification, then `c_N → c_p`.
  rw [petN_heckeT_p_LHS_eq_aggregate p hp hpN f g,
    peterssonInner_T_p_reps_sum_slashes_eq_aggregate_HeckeFD p hp hpN f g hm h_int_per hfi,
    aggregate_D_petersson_eq_Gamma_p_A_fundDomain p hp hpN f g
      (isFundamentalDomain_Hecke_tiles_biUnion_Gamma_p_α p hp hpN),
    ← slToPslQuot_fiberCard_Gamma_p_α_T_p_lower_eq_fiberCard p hp hpN]
  -- Trace engine: `c_p • ∫_{Γ_p(A)-FD} pet f (g∣A) = c_N • ∫_{Γ₁-FD} pet f (tr_{q₀}(g∣A))`.
  rw [setIntegral_Gamma_p_α_fundDomain_PSL_petersson_eq_traceSlash_Gamma1_fundDomain
    (N := N) (k := k) (T_p_lower p hp.pos) ⇑f
    (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) q₀ hF_slash hG_slash
    (h_int_FD p hp hpN f g) (h_int_trace_FD p hp hpN f g q₀) (h_int_tr_FD p hp hpN f g q₀)]
  -- Trace leaf: `tr_{q₀}(g∣A) = ⟨p⟩⁻¹ T_p g`; then re-fold into `petN`.
  rw [traceSlash_T_p_lower_eq_diamond_inv_heckeT_p p hp hpN g q₀,
    ← petN_eq_setIntegral_Gamma1_fundDomain_PSL]

/-- **DS Theorem 5.5.3**: `T_p* = ⟨p⟩⁻¹ T_p` w.r.t. the level-N Petersson product
`petN`, i.e. `⟨T_p f, g⟩_N = ⟨f, ⟨p⟩⁻¹ T_p g⟩_N`. -/
theorem heckeT_p_adjoint
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  petN_heckeT_p_adjoint_via_trace p hp hpN f g
end HeckeRing.GL2
