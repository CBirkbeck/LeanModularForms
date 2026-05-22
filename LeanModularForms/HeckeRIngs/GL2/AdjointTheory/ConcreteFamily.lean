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
    ·
      intro i _
      cases i with
      | none => exact glMap_M_infty_det_pos N p hp.pos hpN
      | some b => exact glMap_T_p_upper_det_pos p hp.pos b.val
    ·
      intro i _
      cases i with
      | none => exact slash_peterssonAdj_glMap_M_infty_eq_slash_T_p_lower p hp hpN g
      | some b => exact slash_peterssonAdj_glMap_T_p_upper_eq_slash_T_p_lower p hp.pos b.val g
    ·
      exact hm
    ·
      exact aedisjoint_pairwise_T_p_family p hp hpN
    ·
      exact h_int_per
    ·
      exact hfi_compact
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
    (hd : ∀ b ∈ Finset.range p, Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_SL_tile_balance : ∀ b ∈ Finset.range p,
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
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
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
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) := by
  apply h_upper_tile_shift_to_prefactored_of_FD_slash_exchange p hp hpN f g
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
    (hd : ∀ b ∈ Finset.range p, Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_SL_tile_balance : ∀ b ∈ Finset.range p,
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
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
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
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
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
    (hd : ∀ b ∈ Finset.range p, Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ))
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • fd)))
    (hm : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f))
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)) ∣[k]
          peterssonAdj (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        ⇑g τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) • (fd : Set ℍ)) μ_hyp)
    (h_blockers : ∀ b ∈ Finset.range p,
      TpUpperBranchDiamondFormBlocker p hp hpN b f g) :
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
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) :=
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
  have h_det_pos : 0 < (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).map
        (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
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
  have h_units : Gamma0MapUnits (adjointGamma0Rep p N hpN) =
      (ZMod.unitOfCoprime p hpN)⁻¹ := adjointGamma0Rep_units p N hpN
  have hT126_g := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv
    (k := k) (adjointGamma0Rep p N hpN) g q
  rw [h_units] at hT126_g
  have hT126_uf := slash_Gamma1QuotEquiv_out_inv_eq_diamond_slash_out_inv
    (k := k) (adjointGamma0Rep p N hpN)
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) q
  rw [h_units] at hT126_uf
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
  have hgoal_rw1 :
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) =
      ⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((Gamma1QuotEquivOfGamma0
          ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
          (adjointGamma0Rep p N hpN).property q).out : SL(2, ℤ))⁻¹) := by
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
  have hgoal_rw2 :
      ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((Gamma1QuotEquivOfGamma0
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
            (adjointGamma0Rep p N hpN).property q).out :
              SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) =
      ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) := by
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
  rw [hgoal_rw1, hgoal_rw2]
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
    (h_M_infty_tile_shift_to_prefactored :
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
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))
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
private theorem petN_LHS_dist_eq_RHS_absorbed_from_TpHeckeFamilyBlocker
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
  rw [← petN_T_p_heckeT_p_LHS_sum_diamond_distributed p hp hpN f g, h_sym,
      petN_diamond_heckeT_p_symm_RHS_sum_distributed p hp hpN f g,
      petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex p hp hpN f g,
      petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex_absorbed p hp hpN
        f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_LHS_eq_diamond_T_p_g_via_sum_chain
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_LHS_dist_eq_RHS_absorbed :
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
                      SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
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
    (h_LHS_dist_eq_RHS_absorbed :
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
                      SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) :
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
    (h_M_infty_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_M_infty_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_disj : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((Finset.range p : Finset ℕ) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b₁) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b₂) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_per_q_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
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
    (h_M_infty_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_M_infty_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_disj : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((Finset.range p : Finset ℕ) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b₁) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b₂) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_per_q_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
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
    (h_M_infty_disj : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_M_infty_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_disj : ∀ b ∈ Finset.range p,
      Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₁.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q₂.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_meas : ∀ b ∈ Finset.range p, ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_upper_per_q_disj : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      ((Finset.range p : Finset ℕ) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_upper p hp.pos b₁) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))
          (((glMap (T_p_upper p hp.pos b₂) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ))))
    (h_upper_per_q_meas : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_LHS_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑f
        (⇑g ∣[k] (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_M_infty_int : IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_upper_int : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
    (h_RHS_upper_per_q_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn (fun τ ↦ petersson k ⇑g
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) ∣[k]
          (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ)) τ)
      (⋃ b ∈ Finset.range p,
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
            GL (Fin 2) ℝ)) • (ModularGroup.fd : Set ℍ)) μ_hyp)
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
    (h_LHS_dist_eq_RHS_absorbed :
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
                      SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))) :
    DSDoubleCosetTileBridge p hp hpN f g := by
  unfold DSDoubleCosetTileBridge
  rw [h_LHS_dist_eq_RHS_absorbed,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex_absorbed p hp hpN f g,
    ← petN_diamond_heckeT_p_symm_RHS_sum_distributed_reindex p hp hpN f g]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_sum_T_p_lower_gamma_M_tile_to_iUnion
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))))
    (hint : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))) μ_hyp) :
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
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) := by
  have h_T_p_lower_det_pos : 0 <
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).map
        (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
  have h_gamma_M_det_one : (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0).val) by
      rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det,
      (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0).property]
    simp
  have h_β_det : 0 <
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
            M_infty_Gamma1_factor N p hpN 0))).det.val := by
    show 0 < ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0)) : GL (Fin 2) ℝ).val.det
    rw [Units.val_mul, Matrix.det_mul, h_gamma_M_det_one, mul_one]
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
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)))) := by
    rw [peterssonAdj_mul, peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero,
      peterssonAdj_mapGL_SL_eq_inv, ← map_inv,
      SlashAction.slash_mul]
    congr 1
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)⁻¹) : GL (Fin 2) ℝ) =
        ((((gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)⁻¹) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) from rfl,
      ← ModularForm.SL_slash]
    exact (slash_Gamma1_eq (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
      (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
        M_infty_Gamma1_factor N p hpN 0)⁻¹
      (Subgroup.inv_mem _
        (gamma0_T_p_upper_Gamma1_factor_zero_mul_M_infty_Gamma1_factor_zero_mem_Gamma1
          N p hpN))).symm
  rw [h_g_slash, h_pa_simp, mul_smul, ← peterssonInner_slash_adjoint_coset
    ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
          M_infty_Gamma1_factor N p hpN 0)))
    h_β_det q ⇑f ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_iUnion_T_p_lower_gamma_M_to_RHS_prefactored
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp)
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))))
    (hint : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))) μ_hyp)
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
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) q⁻¹ : GL (Fin 2) ℝ))) := by
  have h_T_p_lower_det_pos : 0 <
      (glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).map (algebraMap ℚ ℝ) from rfl]
    rw [show (((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).map
        (algebraMap ℚ ℝ)).det =
        (algebraMap ℚ ℝ) (((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).det) from
          (RingHom.map_det _ _).symm]
    rw [show ((T_p_lower p hp.pos : GL (Fin 2) ℚ).val).det = (p : ℚ) by
      simp [T_p_lower, Matrix.GeneralLinearGroup.mkOfDetNeZero,
        Matrix.det_fin_two, Matrix.of_apply]]
    show 0 < (algebraMap ℚ ℝ) ((p : ℚ))
    rw [show (algebraMap ℚ ℝ) ((p : ℚ)) = ((p : ℚ) : ℝ) from rfl]
    exact_mod_cast hp.pos
  have h_gamma_b_det_one : (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
      (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [show (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix
          (gamma0_T_p_upper_Gamma1_factor N p hpN b).val) by
      rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det,
      (gamma0_T_p_upper_Gamma1_factor N p hpN b).property]
    simp
  have h_β_det : 0 <
      ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (gamma0_T_p_upper_Gamma1_factor N p hpN b))).det.val := by
    show 0 < ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b)) : GL (Fin 2) ℝ).val.det
    rw [Units.val_mul, Matrix.det_mul, h_gamma_b_det_one, mul_one]
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
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)))) := by
    rw [peterssonAdj_mul, peterssonAdj_glMap_T_p_lower_eq_glMap_T_p_upper_zero,
      peterssonAdj_mapGL_SL_eq_inv, ← map_inv,
      SlashAction.slash_mul]
    congr 1
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          ((gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹) : GL (Fin 2) ℝ) =
        ((((gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) from rfl,
      ← ModularForm.SL_slash]
    exact (slash_Gamma1_eq (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)
      (gamma0_T_p_upper_Gamma1_factor N p hpN b)⁻¹
      (Subgroup.inv_mem _
        (gamma0_T_p_upper_Gamma1_factor_mem_Gamma1 N p hpN b))).symm
  rw [h_g_slash, h_pa_simp, mul_smul, ← peterssonInner_slash_adjoint_coset
    ((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (gamma0_T_p_upper_Gamma1_factor N p hpN b)))
    h_β_det q ⇑f ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem peterssonInner_iUnion_T_p_lower_gamma_b_to_RHS_prefactored_upper
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp)
    (hd : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      (↑(Finset.range p) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b₁)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b₂)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))))
    (hint : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn
        (fun τ ↦ petersson k ⇑f
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)
        (⋃ b ∈ Finset.range p,
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))) μ_hyp)
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
private theorem h_LHS_dist_eq_RHS_absorbed_of_M_infty_iUnion
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp)
    (hd_M : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))))
    (hint_M : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))) μ_hyp)
    (hm_T : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp)
    (hd_T : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      (↑(Finset.range p) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b₁)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b₂)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))))
    (hint_T : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn
        (fun τ ↦ petersson k ⇑f
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)
        (⋃ b ∈ Finset.range p,
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))) μ_hyp)
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
  have h_M_branch :
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
  have h_upper_branch :
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
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h_M_branch, h_upper_branch]

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_via_iUnion_residuals
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (hm_M : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp)
    (hd_M : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))))
    (hint_M : IntegrableOn
      (fun τ ↦ petersson k ⇑f
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
          (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN 0 *
              M_infty_Gamma1_factor N p hpN 0)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane))) μ_hyp)
    (hm_T : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      NullMeasurableSet
        (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
          (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp)
    (hd_T : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      (↑(Finset.range p) : Set ℕ).Pairwise (fun b₁ b₂ ↦ AEDisjoint μ_hyp
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b₁)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b₂)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))))
    (hint_T : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      IntegrableOn
        (fun τ ↦ petersson k ⇑f
          (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) ∣[k]
            (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) τ)
        (⋃ b ∈ Finset.range p,
          (((glMap (T_p_lower p hp.pos) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (gamma0_T_p_upper_Gamma1_factor N p hpN b)) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
              (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))) μ_hyp)
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
    (h_M_infty_tile_shift_to_prefactored :
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
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))))
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
    (h_M_infty_FD_slash_exchange :
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
              ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                ((Gamma1QuotEquivOfGamma0
                  ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                  (adjointGamma0Rep p N hpN).property q).out :
                  SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
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
    (h_upper_FD_slash_exchange :
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
                ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
                  ((Gamma1QuotEquivOfGamma0
                    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))
                    (adjointGamma0Rep p N hpN).property q).out :
                    SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ))) =
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
  petN_heckeT_p_adjoint_standard_form_from_two_tile_shift_residuals p hp hpN f g
    (h_M_infty_tile_shift_to_prefactored_of_FD_slash_exchange p hp hpN f g
      h_M_infty_FD_slash_exchange)
    (h_upper_tile_shift_to_prefactored_of_FD_slash_exchange p hp hpN f g
      h_upper_FD_slash_exchange)

open UpperHalfPlane ModularGroup MeasureTheory in
private theorem petN_heckeT_p_adjoint_standard_form_from_SL_tile_balances
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
    (h_M_SL_tile_balance :
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
        (⇑g ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)))
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
    (h_T_SL_tile_balance : ∀ b ∈ Finset.range p,
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
        (⇑g ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))) :
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
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
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
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k] α)
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] α) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
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
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
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
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
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
    (hint_M_balance_LHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_balance_RHS : IntegrableOn
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
    (hint_T_balance_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_T_balance_RHS : ∀ b ∈ Finset.range p, IntegrableOn
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
    (hd : Pairwise (fun (q₁ q₂ : SL(2, ℤ) ⧸ Gamma1 N) ↦ AEDisjoint μ_hyp
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₁.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ))
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q₂.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • fd)))
    (hm : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      NullMeasurableSet
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
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
    (hint_M_balance_LHS : IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_M_balance_RHS : IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
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
    (hint_T_balance_LHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        ((⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ))
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
    (hint_T_balance_RHS : ∀ b ∈ Finset.range p, IntegrableOn
      (fun τ ↦ petersson k
        (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f))
        ((⇑g) ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) τ)
      (⋃ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) • (fd : Set ℍ)) μ_hyp)
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
    sum_peterssonInner_upper_tile_form_swap p hp hpN f g]
  rw [show (∑ b ∈ Finset.range p,
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
              ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) from
    Finset.sum_congr rfl (fun b hb ↦ sum_peterssonInner_upper_tile_form_per_b_collapse p hp hpN b hb f g
        (fun q ↦ h_meas b hb q) (h_disj b hb) (h_LHS_int b hb))]
  rw [show (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
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
          (⇑g) by
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
      (⇑g) (h_RHS_int b hb)).symm]
  exact Finset.sum_congr rfl (fun b hb ↦ h_tile b hb)

private theorem petN_heckeT_p_symmetric_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
  refine petN_heckeT_p_symmetric_form_of_doubleCosetTileBridge p hp hpN f g ?_
  unfold DSDoubleCosetTileBridge
  refine DSDoubleCosetTileBridge_of_LHS_dist_eq_RHS_absorbed p hp hpN f g ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  refine congr_arg₂ (· + ·) ?_ ?_
  ·
    show SigmaQPermResidual_M_infty p hp hpN f g
    sorry
  ·
    show SigmaQPermResidual_upper p hp hpN f g
    sorry

private lemma petN_heckeT_p_adjoint_standard_form
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      UpperHalfPlane.peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) = _
  have h_per_q : ∀ q : SL(2, ℤ) ⧸ Gamma1 N,
      UpperHalfPlane.peterssonInner k ModularGroup.fd
        (⇑(heckeT_p_cusp k p hp hpN f) ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) =
      UpperHalfPlane.peterssonInner k
        ((glMap (M_infty N p hp.pos hpN) : GL (Fin 2) ℝ) •
          (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ) •
            (ModularGroup.fd : Set UpperHalfPlane)))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) +
      UpperHalfPlane.peterssonInner k
        (⋃ b ∈ Finset.range p,
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) *
            ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
              GL (Fin 2) ℝ)) •
            (ModularGroup.fd : Set UpperHalfPlane))
        ⇑f
        ((⇑g ∣[k] (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) ∣[k]
          ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
            ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)))) := fun q ↦ by
    change UpperHalfPlane.peterssonInner k ModularGroup.fd
      (⇑(heckeT_p_cusp k p hp hpN f) ∣[k]
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ))
      (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) = _
    exact peterssonInner_heckeT_p_LHS_per_q_to_union_tiles p hp hpN
      (q.out : SL(2, ℤ)) f g
  exact petN_heckeT_p_adjoint_standard_form_from_petN_symmetric_form p hp hpN f g
    (petN_heckeT_p_symmetric_form p hp hpN f g)

private theorem petN_heckeT_p_canonical_adjoint_residual
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g)) := by
  rw [show (heckeT_p_cusp k p hp hpN
        (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ g) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
      diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g) by
    apply CuspForm.ext; intro τ
    show ((heckeT_p k p hp hpN)
        (diamondOp k (ZMod.unitOfCoprime p hpN)⁻¹ g.toModularForm')).toFun τ =
      ((diamondOp k (ZMod.unitOfCoprime p hpN)⁻¹)
        (heckeT_p k p hp hpN g.toModularForm')).toFun τ
    have h := LinearMap.congr_fun
      (heckeT_p_comm_diamondOp k p hp hpN (ZMod.unitOfCoprime p hpN)⁻¹)
      g.toModularForm'
    exact congr_arg (fun m : ModularForm ((Gamma1 N).map (mapGL ℝ)) k ↦ m.toFun τ)
      h.symm]
  exact petN_heckeT_p_adjoint_standard_form p hp hpN f g

private theorem petN_heckeT_p_diamond_shift_core_of_unsymm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_unsymm : petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g))) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) := by
  set u := ZMod.unitOfCoprime p hpN
  have h_cancel : diamondOp_cusp k u (diamondOp_cusp k u⁻¹
      (heckeT_p_cusp k p hp hpN g)) = heckeT_p_cusp k p hp hpN g := by
    show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
      heckeT_p_cusp k p hp hpN g
    rw [show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
        ((diamondOpCusp k u).comp (diamondOpCusp k u⁻¹))
          (heckeT_p_cusp k p hp hpN g) from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl
  have h2 := diamondOp_petersson_unitary u f
    (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))
  calc petN (heckeT_p_cusp k p hp hpN f) g
      = petN f (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) := h_unsymm
    _ = petN (diamondOp_cusp k u f)
          (diamondOp_cusp k u
            (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))) := h2.symm
    _ = petN (diamondOp_cusp k u f) (heckeT_p_cusp k p hp hpN g) := by
        rw [h_cancel]

private theorem petN_heckeT_p_diamond_shift_core
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_diamond_shift_core_of_unsymm p hp hpN f g
    (petN_heckeT_p_adjoint_standard_form p hp hpN f g)

private theorem petN_heckeT_p_adjoint_unsymm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  set u := ZMod.unitOfCoprime p hpN
  have h1 := petN_heckeT_p_diamond_shift_core p hp hpN f g
  have h_cancel : diamondOp_cusp k u (diamondOp_cusp k u⁻¹
      (heckeT_p_cusp k p hp hpN g)) = heckeT_p_cusp k p hp hpN g := by
    show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
      heckeT_p_cusp k p hp hpN g
    rw [show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
        ((diamondOpCusp k u).comp (diamondOpCusp k u⁻¹)) (heckeT_p_cusp k p hp hpN g) from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl
  have h2 := diamondOp_petersson_unitary u f
    (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))
  calc petN (heckeT_p_cusp k p hp hpN f) g
      = petN (diamondOp_cusp k u f) (heckeT_p_cusp k p hp hpN g) := h1
    _ = petN (diamondOp_cusp k u f) (diamondOp_cusp k u
          (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))) := by
        rw [h_cancel]
    _ = petN f (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) := h2

private theorem petN_heckeT_p_diamond_shift
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN (diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f)
        (heckeT_p_cusp k p hp hpN g) :=
  petN_heckeT_p_diamond_shift_core p hp hpN f g

private theorem heckeT_p_adjoint_of_diamond_shift
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) := by
  set u := ZMod.unitOfCoprime p hpN
  have h1 := petN_heckeT_p_diamond_shift p hp hpN f g
  have h_cancel : diamondOp_cusp k u (diamondOp_cusp k u⁻¹
      (heckeT_p_cusp k p hp hpN g)) = heckeT_p_cusp k p hp hpN g := by
    show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
      heckeT_p_cusp k p hp hpN g
    rw [show diamondOpCusp k u (diamondOpCusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) =
        ((diamondOpCusp k u).comp (diamondOpCusp k u⁻¹)) (heckeT_p_cusp k p hp hpN g) from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl
  have h2 := diamondOp_petersson_unitary u f
    (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))
  calc petN (heckeT_p_cusp k p hp hpN f) g
      = petN (diamondOp_cusp k u f) (heckeT_p_cusp k p hp hpN g) := h1
    _ = petN (diamondOp_cusp k u f) (diamondOp_cusp k u
          (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g))) := by
        rw [h_cancel]
    _ = petN f (diamondOp_cusp k u⁻¹ (heckeT_p_cusp k p hp hpN g)) := h2

/-- **DS Theorem 5.5.3**: `T_p* = ⟨p⟩⁻¹ T_p` w.r.t. the level-N Petersson product
`petN`, i.e. `⟨T_p f, g⟩_N = ⟨f, ⟨p⟩⁻¹ T_p g⟩_N`. -/
theorem heckeT_p_adjoint
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    petN (heckeT_p_cusp k p hp hpN f) g =
      petN f (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹
        (heckeT_p_cusp k p hp hpN g)) :=
  heckeT_p_adjoint_of_diamond_shift p hp hpN f g

end HeckeRing.GL2
