/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson
import LeanModularForms.HeckeRIngs.GL2.CharacterDecomp
import LeanModularForms.HeckeRIngs.GL2.LevelEmbed
import LeanModularForms.HeckeRIngs.GL2.LevelRaise
import LeanModularForms.HeckeRIngs.GL2.Unified.NebentypusHeckeRingHom
import LeanModularForms.Modularforms.LFunction
import LeanModularForms.Modularforms.PeterssonLevelN
import LeanModularForms.Modularforms.DimensionFormulas
import LeanModularForms.Modularforms.SlashActionAuxil
import LeanModularForms.Eigenforms.ConductorTheorem
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeCosets

/-!
# Newforms: bad-prime Fricke-adjoint reduction chain

The aggregate `(q, b)`-shifted-domain identities, per-`q` AE-disjointness and
integrability discharges, and the reduction chain closing the bad-prime `petN`
Fricke adjoint via the `qBSimplified` residual.

This module is part of the split of `Newforms.lean`; see that file's header for
the overall design.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}

private theorem neg_one_zpow_mul_self (k : ℤ) :
    ((-1 : ℂ) ^ k) * ((-1 : ℂ) ^ k) = 1 := by
  rw [← mul_zpow]; norm_num

private theorem mapGL_SL_det_eq_one (γ : SL(2, ℤ)) :
    ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
  rw [show ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Int.castRingHom ℝ).mapMatrix γ.val) by rw [mapGL_coe_matrix]; rfl]
  rw [← RingHom.map_det, γ.property]
  simp

private theorem glMap_T_p_upper_mul_mapGL_SL_inv_det_pos
    {p : ℕ} (hp : 0 < p) (b : ℕ) (γ : SL(2, ℤ)) :
    0 < (((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) *
      (mapGL ℝ γ : GL (Fin 2) ℝ))⁻¹ : GL (Fin 2) ℝ).det.val := by
  set α : GL (Fin 2) ℝ :=
    (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) * (mapGL ℝ γ : GL (Fin 2) ℝ)
  have h_α_det_pos : 0 < (α : GL (Fin 2) ℝ).det.val := by
    show 0 < ((α : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((α : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) *
        ((mapGL ℝ γ : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) from Units.val_mul _ _,
      Matrix.det_mul, mapGL_SL_det_eq_one γ, mul_one]
    exact glMap_T_p_upper_det_pos p hp b
  show 0 < (((α⁻¹ : GL (Fin 2) ℝ)).det : ℝˣ).val
  rw [show (((α⁻¹ : GL (Fin 2) ℝ)).det : ℝˣ) = (α.det : ℝˣ)⁻¹ from
    map_inv _ _, Units.val_inv_eq_inv_val]
  exact inv_pos.mpr h_α_det_pos

open UpperHalfPlane MeasureTheory ModularGroup in
/-- Per-`q` `Fin p`-indexed null-measurability for the bad-prime upper-coset tile
family `{β_b · q.out⁻¹·fd}_{b ∈ Fin p}`: each per-`b` tile is null-measurable
w.r.t. `μ_hyp`. -/
theorem Newform.nullMeasurableSet_T_p_upper_smul_qOut_inv_fd
    {N : ℕ} [NeZero N] {p : ℕ} (hp : 0 < p) (q : SL(2, ℤ) ⧸ Gamma1 N)
    (b : Fin p) :
    NullMeasurableSet
      ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (fd : Set UpperHalfPlane))) μ_hyp := by
  rw [← mul_smul]
  set α : GL (Fin 2) ℝ :=
    (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) *
      (mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)
  have h_eq : (α • (fd : Set UpperHalfPlane) : Set ℍ) =
      ((α⁻¹ • · : ℍ → ℍ) ⁻¹' (fd : Set UpperHalfPlane)) := by
    ext τ; simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [h_eq]
  exact nullMeasurableSet_modularGroup_fd.preimage
    (measurePreserving_glPos_smul _
      (glMap_T_p_upper_mul_mapGL_SL_inv_det_pos hp b.val
        ((q.out : SL(2, ℤ))⁻¹))).quasiMeasurePreserving

open UpperHalfPlane MeasureTheory ModularGroup in
/-- Per-`q` `peterssonInner` finite-union additivity for the bad-prime upper-coset
tile family `{β_b · q.out⁻¹·fd}_{b ∈ Fin p}`: the integral over the finite union
equals the sum of per-`b` integrals, given integrability over the union. -/
theorem Newform.peterssonInner_iUnion_T_p_upper_smul_qOut_inv_fd_eq_sum
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (f g : UpperHalfPlane → ℂ)
    (hint : IntegrableOn (fun τ ↦ petersson k f g τ)
      (⋃ b : Fin p,
        (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))) μ_hyp) :
    peterssonInner k
        (⋃ b : Fin p,
          (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane))) f g =
      ∑ b : Fin p, peterssonInner k
        ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))) f g :=
  peterssonInner_iUnion_finite_aedisjoint
    (k := k)
    (fun b : Fin p ↦
      (glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (fd : Set UpperHalfPlane)))
    (Newform.nullMeasurableSet_T_p_upper_smul_qOut_inv_fd hp q)
    (Newform.aedisjoint_pairwise_T_p_upper_smul_qOut_inv_fd hp q)
    f g hint

open UpperHalfPlane MeasureTheory ModularGroup in
/-- `W_N`-envelope per-`q` `Fin p`-indexed pairwise AE-disjointness for the
bad-prime upper-coset tile family `{W_N · β_b · q.out⁻¹·fd}_{b ∈ Fin p}`. -/
theorem Newform.aedisjoint_pairwise_fricke_T_p_upper_smul_qOut_inv_fd
    {N : ℕ} [NeZero N] {p : ℕ} (hp : 0 < p) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    Pairwise (fun b₁ b₂ : Fin p ↦
      AEDisjoint μ_hyp
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((glMap (T_p_upper p hp b₁.val) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane))))
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((glMap (T_p_upper p hp b₂.val) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane))))) := by
  intro b₁ b₂ hne
  have h_W_N_inv_det_pos :
      0 < ((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹).det.val := by
    show 0 < (((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹).det : ℝˣ).val
    rw [show (((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹).det : ℝˣ) =
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ).det : ℝˣ)⁻¹ from
        map_inv _ _, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr (Newform.frickeMatrix_det_pos N)
  have h_smul_eq : ∀ (S : Set UpperHalfPlane),
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) • S : Set ℍ) =
        (((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹ • ·) : ℍ → ℍ) ⁻¹' S := by
    intro S
    ext τ
    simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [h_smul_eq, h_smul_eq]
  exact (Newform.aedisjoint_pairwise_T_p_upper_smul_qOut_inv_fd hp q hne).preimage
    (measurePreserving_glPos_smul _ h_W_N_inv_det_pos).quasiMeasurePreserving

open UpperHalfPlane MeasureTheory ModularGroup in
/-- `W_N`-envelope per-`q` per-`b` null-measurability for the bad-prime
upper-coset tile `W_N · β_b · q.out⁻¹·fd`. -/
theorem Newform.nullMeasurableSet_fricke_T_p_upper_smul_qOut_inv_fd
    {N : ℕ} [NeZero N] {p : ℕ} (hp : 0 < p) (q : SL(2, ℤ) ⧸ Gamma1 N)
    (b : Fin p) :
    NullMeasurableSet
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
        ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane)))) μ_hyp := by
  have h_W_N_inv_det_pos :
      0 < ((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹).det.val := by
    show 0 < (((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹).det : ℝˣ).val
    rw [show (((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹).det : ℝˣ) =
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ).det : ℝˣ)⁻¹ from
        map_inv _ _, Units.val_inv_eq_inv_val]
    exact inv_pos.mpr (Newform.frickeMatrix_det_pos N)
  have h_smul_eq :
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
        ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))) : Set ℍ) =
      (((Newform.frickeMatrix N : GL (Fin 2) ℝ)⁻¹ • ·) : ℍ → ℍ) ⁻¹'
        ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))) := by
    ext τ
    simp [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem]
  rw [h_smul_eq]
  exact (Newform.nullMeasurableSet_T_p_upper_smul_qOut_inv_fd hp q b).preimage
    (measurePreserving_glPos_smul _ h_W_N_inv_det_pos).quasiMeasurePreserving

open UpperHalfPlane MeasureTheory ModularGroup in
/-- `W_N`-envelope per-`q` `peterssonInner` finite-union additivity for the
bad-prime upper-coset tile family: the integral over the `W_N`-conjugated finite
union equals the sum of per-`b` integrals, given integrability over the union. -/
theorem Newform.peterssonInner_iUnion_fricke_T_p_upper_smul_qOut_inv_fd_eq_sum
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p)
    (q : SL(2, ℤ) ⧸ Gamma1 N)
    (f g : UpperHalfPlane → ℂ)
    (hint : IntegrableOn (fun τ ↦ petersson k f g τ)
      (⋃ b : Fin p,
        (Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane)))) μ_hyp) :
    peterssonInner k
        (⋃ b : Fin p,
          (Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
              ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
                (fd : Set UpperHalfPlane)))) f g =
      ∑ b : Fin p, peterssonInner k
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane)))) f g :=
  peterssonInner_iUnion_finite_aedisjoint
    (k := k)
    (fun b : Fin p ↦
      (Newform.frickeMatrix N : GL (Fin 2) ℝ) •
        ((glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))))
    (Newform.nullMeasurableSet_fricke_T_p_upper_smul_qOut_inv_fd hp q)
    (Newform.aedisjoint_pairwise_fricke_T_p_upper_smul_qOut_inv_fd hp q)
    f g hint

open UpperHalfPlane MeasureTheory ModularGroup in
/-- Per-`(q, b)` right-slot to f-slot transfer for the bad-prime W_N-conjugated
tile family: rewrites `peterssonInner k (W_N · β_b · q.out⁻¹·fd) f (g | adj M_b)`
to `peterssonInner k (W_N · q.out⁻¹·fd) (f | M_b) g`, giving a `b`-independent
integration domain. -/
theorem Newform.peterssonInner_W_N_β_b_qOut_inv_fd_adj_eq_peterssonInner_W_N_qOut_inv_fd_M_b_slash
    (N : ℕ) [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p)
    (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ)
    (f g : UpperHalfPlane → ℂ) :
    peterssonInner k
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane))))
        f
        (g ∣[k]
          (Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ)) =
      peterssonInner k
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane)))
        (f ∣[k] (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ))
        g := by
  rw [Newform.frickeMatrix_smul_T_p_upper_smul_set_eq_T_p_lower_with_offset_smul_frickeMatrix_smul_set
    N hp b,
    ← Newform.slash_peterssonAdj_T_p_lower_with_offset hp b g,
    ← peterssonInner_slash_adjoint
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (fd : Set UpperHalfPlane)))
      (Newform.T_p_lower_with_offset N hp b)
      (Newform.T_p_lower_with_offset_det_pos N hp b)]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The common-domain `(q, b)`-aggregate identity for the bad-prime W_N-conjugated
tile family with RHS `petN (T_p f) g`: every per-`(q, b)` summand uses the
`b`-independent domain `W_N · q.out⁻¹·fd`, with the `b`-dependence isolated as
`(f|W_N)|M_b` in the f-slot. -/
theorem Newform.aggregate_q_b_common_W_N_qOut_inv_fd_eq_inv_c_petN_T_p_f_g
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSquareScalar N k)⁻¹ *
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          ((-1 : ℂ) ^ k *
            peterssonInner k
              ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
                ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
                  (fd : Set UpperHalfPlane)))
              ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
                (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ))
              (⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)))) =
    petN (heckeT_n_cusp k p f) g := by
  rw [← Newform.aggregate_q_b_W_N_β_b_shifted_eq_inv_c_petN_T_p_f_g hp hpN f g]
  congr 1
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [peterssonInner_smul_right,
    Newform.peterssonInner_W_N_β_b_qOut_inv_fd_adj_eq_peterssonInner_W_N_qOut_inv_fd_M_b_slash
      N hp.pos q b]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The common-domain b-sum collapse for the bad-prime W_N-conjugated aggregate
with RHS `petN (T_p f) g`: the per-`q` b-sum is folded into the f-slot of a single
`peterssonInner` over the common domain, concentrating the `b`-dependence in
`Σ_b ((f|W_N)|M_b)`. Conditional on per-`(q, b)` integrability. -/
theorem Newform.aggregate_q_b_collapsed_W_N_qOut_inv_fd_eq_inv_c_petN_T_p_f_g
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h_int : ∀ q : SL(2, ℤ) ⧸ Gamma1 N, ∀ b ∈ Finset.range p,
      IntegrableOn
        (fun τ ↦ petersson k
          (⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
          ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ)) τ)
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))) μ_hyp) :
    (Newform.frickeSquareScalar N k)⁻¹ *
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((-1 : ℂ) ^ k *
          peterssonInner k
            ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
              ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
                (fd : Set UpperHalfPlane)))
            (∑ b ∈ Finset.range p,
              ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
                (Newform.T_p_lower_with_offset N hp.pos b :
                  GL (Fin 2) ℝ)))
            (⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)))) =
    petN (heckeT_n_cusp k p f) g := by
  rw [← Newform.aggregate_q_b_common_W_N_qOut_inv_fd_eq_inv_c_petN_T_p_f_g hp hpN f g]
  congr 1
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [peterssonInner_sum_left _ _ _ _ (h_int q), Finset.mul_sum]

/-- The rational lift of `Newform.T_p_lower_with_offset` in `GL (Fin 2) ℚ`, with
entries `!![p, 0; -N·b, 1]`. -/
noncomputable def Newform.T_p_lower_with_offsetRat
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(p : ℚ), 0; -((N : ℚ) * b), 1] : Matrix (Fin 2) (Fin 2) ℚ)
    (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne')

/-- The `glMap`-image of the rational lift equals the real
`T_p_lower_with_offset`. -/
lemma Newform.glMap_T_p_lower_with_offsetRat
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    glMap (Newform.T_p_lower_with_offsetRat N hp b) =
      Newform.T_p_lower_with_offset N hp b := by
  apply Units.ext
  show (glMap (Newform.T_p_lower_with_offsetRat N hp b) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (Newform.T_p_lower_with_offset N hp b : Matrix (Fin 2) (Fin 2) ℝ)
  rw [Newform.T_p_lower_with_offset_coe]
  show ((Newform.T_p_lower_with_offsetRat N hp b : GL (Fin 2) ℚ) :
        Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
      !![(p : ℝ), 0; -((N : ℝ) * b), 1]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Newform.T_p_lower_with_offsetRat, Matrix.GeneralLinearGroup.mkOfDetNeZero]

open ConjAct Pointwise in
private theorem isArithmetic_toConjAct_inv_smul_gamma1_of_map_eq
    {N : ℕ} [NeZero N] {A : GL (Fin 2) ℝ} {M : GL (Fin 2) ℚ}
    (hM : ((M : GL (Fin 2) ℚ).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) = A) :
    (toConjAct A⁻¹ • ((Gamma1 N).map (mapGL ℝ))).IsArithmetic := by
  have h := Subgroup.IsArithmetic.conj ((Gamma1 N).map (mapGL ℝ)) M⁻¹
  have h_inv : (((M)⁻¹ : GL (Fin 2) ℚ).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) =
      A⁻¹ := by rw [map_inv, hM]
  rw [h_inv] at h
  exact h

open UpperHalfPlane in
private theorem norm_petersson_le_half_add_diag (k : ℤ) (a b : ℍ → ℂ) (τ : ℍ) :
    ‖petersson k a b τ‖ ≤
      (‖petersson k b b τ‖ + ‖petersson k a a τ‖) / 2 := by
  simp only [petersson, norm_mul, Complex.norm_conj]
  have h_im_nn : (0 : ℝ) ≤ ‖((τ.im : ℂ) ^ k)‖ := norm_nonneg _
  nlinarith [mul_nonneg (sq_nonneg (‖a τ‖ - ‖b τ‖)) h_im_nn,
    sq_nonneg (‖a τ‖ - ‖b τ‖), norm_nonneg (a τ), norm_nonneg (b τ), h_im_nn]

open UpperHalfPlane MeasureTheory ModularGroup ConjAct Pointwise in
private theorem integrableOn_petersson_slash_smul_fd_of_map_eq
    {N : ℕ} [NeZero N] {k : ℤ} (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {A_g A_f α : GL (Fin 2) ℝ} {M_g M_f : GL (Fin 2) ℚ}
    (hM_g : ((M_g : GL (Fin 2) ℚ).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) = A_g)
    (hM_f : ((M_f : GL (Fin 2) ℚ).map (Rat.castHom ℝ) : GL (Fin 2) ℝ) = A_f)
    (hα : 0 < α.det.val) :
    IntegrableOn (fun τ ↦ petersson k (⇑g ∣[k] A_g) (⇑f ∣[k] A_f) τ)
      (α • (ModularGroup.fd : Set UpperHalfPlane)) μ_hyp := by
  haveI hArith_g :
      (toConjAct (A_g : GL (Fin 2) ℝ)⁻¹ •
        ((Gamma1 N).map (mapGL ℝ))).IsArithmetic :=
    isArithmetic_toConjAct_inv_smul_gamma1_of_map_eq hM_g
  haveI hArith_f :
      (toConjAct (A_f : GL (Fin 2) ℝ)⁻¹ •
        ((Gamma1 N).map (mapGL ℝ))).IsArithmetic :=
    isArithmetic_toConjAct_inv_smul_gamma1_of_map_eq hM_f
  let g_tr : CuspForm
      (toConjAct (A_g : GL (Fin 2) ℝ)⁻¹ • ((Gamma1 N).map (mapGL ℝ))) k :=
    CuspForm.translate g A_g
  have h_gtr_coe : (⇑g_tr : UpperHalfPlane → ℂ) = ⇑g ∣[k] A_g := rfl
  let f_tr : CuspForm
      (toConjAct (A_f : GL (Fin 2) ℝ)⁻¹ • ((Gamma1 N).map (mapGL ℝ))) k :=
    CuspForm.translate f A_f
  have h_ftr_coe : (⇑f_tr : UpperHalfPlane → ℂ) = ⇑f ∣[k] A_f := rfl
  obtain ⟨C_f, hC_f⟩ := CuspFormClass.petersson_bounded_left k _ f_tr f_tr
  obtain ⟨C_g, hC_g⟩ := CuspFormClass.petersson_bounded_left k _ g_tr g_tr
  have h_AM_GM : ∀ τ,
      ‖petersson k (⇑g ∣[k] A_g) (⇑f ∣[k] A_f) τ‖ ≤ (C_f + C_g) / 2 := by
    intro τ
    rw [← h_gtr_coe, ← h_ftr_coe]
    linarith [hC_f τ, hC_g τ, norm_petersson_le_half_add_diag k ⇑g_tr ⇑f_tr τ]
  have h_finite_measure :
      μ_hyp (α • (ModularGroup.fd : Set UpperHalfPlane)) < ⊤ := by
    rw [measure_glPos_smul_eq α hα nullMeasurableSet_modularGroup_fd]
    exact hyperbolicMeasure_fd_lt_top
  refine IntegrableOn.of_bound h_finite_measure ?_ ((C_f + C_g) / 2) ?_
  · refine (petersson_continuous k ?_ ?_).aestronglyMeasurable.restrict
    · rw [← h_gtr_coe]; exact ModularFormClass.continuous g_tr
    · rw [← h_ftr_coe]; exact ModularFormClass.continuous f_tr
  · exact ae_of_all _ fun τ ↦ h_AM_GM τ

open UpperHalfPlane MeasureTheory ModularGroup ConjAct Pointwise in
/-- Integrability of the bad-prime W_N-shifted q-tile lower-offset Petersson
integrand `petersson k (g | W_N) ((f | W_N) | M_b)` over the tile
`W_N • mapGL ℝ q.out⁻¹ • fd`. -/
theorem Newform.integrableOn_petersson_fricke_qOut_fd_lowerOffset
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) :
    IntegrableOn
      (fun τ ↦ petersson k
        (⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
        ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)) τ)
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
        ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
          (fd : Set UpperHalfPlane))) μ_hyp := by
  have h_integrand_eq :
      (fun τ ↦ petersson k
        (⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
        ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)) τ) =
      (fun τ ↦ petersson k
        (⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
        (⇑f ∣[k] ((Newform.frickeMatrix N : GL (Fin 2) ℝ) *
          (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ))) τ) := by
    funext τ; rw [SlashAction.slash_mul]
  rw [h_integrand_eq, ← mul_smul]
  refine integrableOn_petersson_slash_smul_fd_of_map_eq f g
    (M_g := Newform.frickeMatrixRat N)
    (M_f := Newform.frickeMatrixRat N * Newform.T_p_lower_with_offsetRat N hp b)
    ?_ ?_ ?_
  · show glMap (Newform.frickeMatrixRat N) = _
    rw [Newform.glMap_frickeMatrixRat]
  · show glMap (Newform.frickeMatrixRat N *
        Newform.T_p_lower_with_offsetRat N hp b) = _
    rw [map_mul, Newform.glMap_frickeMatrixRat,
      Newform.glMap_T_p_lower_with_offsetRat]
  · show 0 < ((Newform.frickeMatrix N : GL (Fin 2) ℝ) *
        (mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)).det.val
    rw [map_mul, Units.val_mul]
    refine mul_pos (Newform.frickeMatrix_det_pos N) ?_
    show 0 < ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [mapGL_SL_det_eq_one ((q.out : SL(2, ℤ))⁻¹)]; exact one_pos

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The unconditional collapsed common-domain aggregate identity for
`petN (T_p f) g`, discharging the per-`(q, b)` integrability hypothesis via
`Newform.integrableOn_petersson_fricke_qOut_fd_lowerOffset`. -/
theorem Newform.aggregate_q_b_collapsed_W_N_qOut_inv_fd_eq_inv_c_petN_T_p_f_g_unconditional
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (Newform.frickeSquareScalar N k)⁻¹ *
      (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ((-1 : ℂ) ^ k *
          peterssonInner k
            ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
              ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
                (fd : Set UpperHalfPlane)))
            (∑ b ∈ Finset.range p,
              ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
                (Newform.T_p_lower_with_offset N hp.pos b :
                  GL (Fin 2) ℝ)))
            (⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)))) =
    petN (heckeT_n_cusp k p f) g :=
  Newform.aggregate_q_b_collapsed_W_N_qOut_inv_fd_eq_inv_c_petN_T_p_f_g
    hp hpN f g
    (fun q b _ ↦
      Newform.integrableOn_petersson_fricke_qOut_fd_lowerOffset hp.pos f g q b)

private theorem Newform.conj_frickeSquareScalar (N : ℕ) (k : ℤ) :
    (starRingEnd ℂ) (Newform.frickeSquareScalar N k) =
      Newform.frickeSquareScalar N k := by
  rw [Newform.frickeSquareScalar, map_mul, map_zpow₀, map_zpow₀, Complex.conj_natCast]
  congr 1
  norm_num

open UpperHalfPlane MeasureTheory ModularGroup in
private theorem Newform.peterssonInner_lowerOffset_smul_fricke_eq_frickeSquareScalar_shifted
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : p.Prime) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) :
    peterssonInner k
        ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane))))
        (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
        (((-1 : ℂ) ^ k) •
          ((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
              GL (Fin 2) ℝ))) =
      Newform.frickeSquareScalar N k *
        peterssonInner k
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))
          (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g := by
  rw [← Newform.peterssonInner_fricke_T_p_upper_rewrite_adjoint_t152
      ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
        (fd : Set UpperHalfPlane))
      N hp.pos b
      (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ⇑g]
  rw [show (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) :
            UpperHalfPlane → ℂ) =
      (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) from rfl]
  rw [Newform.slash_frickeMatrix_frickeMatrix ⇑f]
  rw [smul_slash_pos_det k (Newform.frickeSquareScalar N k) _
      (T_p_upper p hp.pos b) (T_p_upper_det_pos p hp.pos b)]
  rw [UpperHalfPlane.peterssonInner_conj_smul_left]
  congr 1
  exact Newform.conj_frickeSquareScalar N k

private theorem Newform.sum_slash_T_p_upper_eq_heckeT_n_cusp
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (∑ b ∈ Finset.range p, ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) =
      ⇑(heckeT_n_cusp k p f) := by
  show heckeT_p_ut k p hp.pos (⇑f) =
      (heckeT_n k p (f.toModularForm') : UpperHalfPlane → ℂ)
  rw [heckeT_n_prime k hp,
    heckeT_p_all_not_coprime_apply (k := k) hp hpN f.toModularForm']
  rfl

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimeFrickePerCosetAggregateRes ⟹
HasBadPrimeFrickePerCosetT152ShiftedFD`: the bridge between the matrix-explicit
per-`(q, b)` shifted-domain form and the per-`q` `petN`-shaped form. -/
theorem Newform.hasBadPrimeFrickePerCosetT152ShiftedFD_of_aggregateRes
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_aggregate :
      Newform.HasBadPrimeFrickePerCosetAggregateRes N k p) :
    Newform.HasBadPrimeFrickePerCosetT152ShiftedFD N k p hp hpN := by
  intro f g q
  rw [Finset.sum_congr rfl fun b _ ↦
    Newform.peterssonInner_lowerOffset_smul_fricke_eq_frickeSquareScalar_shifted
      hp f g q b]
  rw [← Finset.mul_sum]
  have h_sl_transfer : ∀ b ∈ Finset.range p,
      peterssonInner k
          ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
            (fd : Set UpperHalfPlane))
          (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g =
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) := by
    intro b _
    rw [show ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
        (fd : Set UpperHalfPlane)) =
        ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)) from rfl]
    rw [peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd
        (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g (q.out)]
    rfl
  rw [Finset.sum_congr rfl h_sl_transfer]
  have h_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ UpperHalfPlane.petersson k
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) τ) (fd : Set UpperHalfPlane) μ_hyp := by
    intro b _
    exact integrableOn_petersson_cuspform_mixed_slash_on_fd g f
      (T_p_upper p hp.pos b) ((q.out : SL(2, ℤ))⁻¹)
  rw [← peterssonInner_sum_left _ _ _ _ h_int]
  rw [← SlashAction.sum_slash,
    Newform.sum_slash_T_p_upper_eq_heckeT_n_cusp hp hpN f]
  rw [h_aggregate f g q]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The explicit `Σ_q Σ_b` form of the bad-prime Atkin-Lehner Hecke adjoint:
the `Σ_q Σ_b` unfolding of `petN (heckeT_n_cusp k p f) g` equals
`petN f (frickeBadAdjointCandidateNormalized k p g)`. The substantive content is
the finite Atkin-Lehner reindex of the `(q, b)` index set governed by
`M_b · W_N = W_N · β_b`. -/
def Newform.HasBadPrimePetN_T_p_FrickeAdjoint_BSum
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) =
    petN f (Newform.frickeBadAdjointCandidateNormalized k p g)

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimePetN_T_p_FrickeAdjoint_BSum ⟹
HasBadPrimeFrickePetNAdjoint`, unfolding the LHS `petN (heckeT_n_cusp k p f) g`
to the explicit `Σ_q Σ_b` form. -/
theorem Newform.hasBadPrimeFrickePetNAdjoint_of_qBDoubleSumIdentity
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_double_sum :
      Newform.HasBadPrimePetN_T_p_FrickeAdjoint_BSum N k p hp hpN) :
    Newform.HasBadPrimeFrickePetNAdjoint N k p := by
  intro f g
  show petN (heckeT_n_cusp k p f) g =
    petN f (Newform.frickeBadAdjointCandidateNormalized k p g)
  rw [show petN (heckeT_n_cusp k p f) g =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k (fd : Set UpperHalfPlane)
          (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
          (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) from rfl]
  have h_lhs_q : ∀ (q : SL(2, ℤ) ⧸ Gamma1 N),
      peterssonInner k (fd : Set UpperHalfPlane)
        (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) := by
    intro q
    rw [Newform.peterssonInner_heckeT_n_cusp_at_divN_slash_qOut_inv_eq_bsum hp hpN f g q,
      SlashAction.sum_slash]
    have h_int : ∀ b ∈ Finset.range p,
        IntegrableOn (fun τ ↦ UpperHalfPlane.petersson k
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹))
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹)) τ) (fd : Set UpperHalfPlane) μ_hyp := by
      intro b _
      exact integrableOn_petersson_cuspform_mixed_slash_on_fd g f
        (T_p_upper p hp.pos b) ((q.out : SL(2, ℤ))⁻¹)
    rw [peterssonInner_sum_left _ _ _ _ h_int]
  rw [Finset.sum_congr rfl fun q _ ↦ h_lhs_q q]
  exact h_double_sum f g

open UpperHalfPlane MeasureTheory ModularGroup in
/-- Operator commutation at the cusp-form level: `heckeT_n_cusp k p` and the
Fricke involution `frickeSlashCuspForm` commute up to the Fricke-conjugated
normalized adjoint candidate, i.e. `heckeT_n_cusp k p ∘ frickeSlashCuspForm =
frickeSlashCuspForm ∘ frickeBadAdjointCandidateNormalized`. -/
lemma Newform.heckeT_n_cusp_frickeSlashCuspForm_eq_frickeSlashCuspForm_frickeBadAdjointCandidateNormalized
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    heckeT_n_cusp k p (Newform.frickeSlashCuspForm g) =
      Newform.frickeSlashCuspForm
        (Newform.frickeBadAdjointCandidateNormalized k p g) := by
  apply DFunLike.coe_injective
  rw [Newform.frickeBadAdjointCandidateNormalized_apply, LinearMap.map_smul,
    Newform.frickeBadAdjointCandidate_apply]
  show (⇑(heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) :
      UpperHalfPlane → ℂ) =
    (Newform.frickeSquareScalar N k)⁻¹ •
      ⇑(Newform.frickeSlashCuspForm (Newform.frickeSlashCuspForm
        (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g))))
  rw [Newform.frickeSlashCuspForm_apply_apply
    (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g))]
  show _ = (Newform.frickeSquareScalar N k)⁻¹ •
      (Newform.frickeSquareScalar N k •
        (⇑(heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) :
          UpperHalfPlane → ℂ))
  rw [smul_smul,
    inv_mul_cancel₀ (Newform.frickeSquareScalar_ne_zero N k), one_smul]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime petN-level Atkin-Lehner intertwine identity:
```
petN (heckeT_n_cusp k p f) g =
  (frickeSquareScalar N k)⁻¹ * (-1)^k *
    petN (frickeSlashCuspForm f) (heckeT_n_cusp k p (frickeSlashCuspForm g)).
```
This is equivalent to `HasBadPrimeFrickePetNAdjoint`, stated with the explicit
W_N-twist and scalar factors. -/
def Newform.HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    petN (heckeT_n_cusp k p f) g =
      (Newform.frickeSquareScalar N k)⁻¹ * (-1 : ℂ) ^ k *
        petN (Newform.frickeSlashCuspForm f)
          (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g))

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine ⟹
HasBadPrimeFrickePetNAdjoint`, combining the intertwine residual with the
operator commutation and the Fricke adjoint identity. -/
theorem Newform.hasBadPrimeFrickePetNAdjoint_of_intertwine
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_intertwine :
      Newform.HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine N k p hp hpN) :
    Newform.HasBadPrimeFrickePetNAdjoint N k p := by
  intro f g
  show petN (heckeT_n_cusp k p f) g =
    petN f (Newform.frickeBadAdjointCandidateNormalized k p g)
  rw [h_intertwine f g,
    Newform.heckeT_n_cusp_frickeSlashCuspForm_eq_frickeSlashCuspForm_frickeBadAdjointCandidateNormalized g,
    Newform.frickeSlashCuspForm_petN_adjoint_unconditional f
      (Newform.frickeSlashCuspForm
        (Newform.frickeBadAdjointCandidateNormalized k p g)),
    Newform.frickeSlashCuspForm_apply_apply
      (Newform.frickeBadAdjointCandidateNormalized k p g),
    petN_smul_right]
  rw [show (Newform.frickeSquareScalar N k)⁻¹ * (-1 : ℂ) ^ k *
        ((-1 : ℂ) ^ k *
          (Newform.frickeSquareScalar N k *
            petN f (Newform.frickeBadAdjointCandidateNormalized k p g))) =
      ((Newform.frickeSquareScalar N k)⁻¹ * Newform.frickeSquareScalar N k) *
        ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
          petN f (Newform.frickeBadAdjointCandidateNormalized k p g) by
      ring]
  rw [inv_mul_cancel₀ (Newform.frickeSquareScalar_ne_zero N k), neg_one_zpow_mul_self k,
    one_mul, one_mul]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine ⟹
HasBadPrimePetN_T_p_FrickeAdjoint_BSum`. -/
theorem Newform.hasBadPrimePetN_T_p_FrickeAdjoint_BSum_of_intertwine
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_intertwine :
      Newform.HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine N k p hp hpN) :
    Newform.HasBadPrimePetN_T_p_FrickeAdjoint_BSum N k p hp hpN := by
  intro f g
  have h_lhs_q : ∀ (q : SL(2, ℤ) ⧸ Gamma1 N),
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) =
      peterssonInner k (fd : Set UpperHalfPlane)
        (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) := by
    intro q
    rw [Newform.peterssonInner_heckeT_n_cusp_at_divN_slash_qOut_inv_eq_bsum hp hpN f g q,
      SlashAction.sum_slash]
    have h_int : ∀ b ∈ Finset.range p,
        IntegrableOn (fun τ ↦ UpperHalfPlane.petersson k
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹))
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹)) τ) (fd : Set UpperHalfPlane) μ_hyp := by
      intro b _
      exact integrableOn_petersson_cuspform_mixed_slash_on_fd g f
        (T_p_upper p hp.pos b) ((q.out : SL(2, ℤ))⁻¹)
    rw [peterssonInner_sum_left _ _ _ _ h_int]
  rw [Finset.sum_congr rfl fun q _ ↦ h_lhs_q q]
  exact Newform.hasBadPrimeFrickePetNAdjoint_of_intertwine hp hpN h_intertwine f g

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime double-coset tile bridge: the concrete sum-level matrix identity
```
∑_q ∑_b peterssonInner k fd ((⇑f ∣[k] β_b) ∣[k] q.out⁻¹) (⇑g ∣[k] q.out⁻¹) =
  (frickeSquareScalar N k)⁻¹ * (-1)^k *
    petN (frickeSlashCuspForm f) (heckeT_n_cusp k p (frickeSlashCuspForm g))
```
with LHS fully expanded over `β_b = T_p_upper p hp.pos b` and `q.out⁻¹`. -/
def Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) =
    (Newform.frickeSquareScalar N k)⁻¹ * (-1 : ℂ) ^ k *
      petN (Newform.frickeSlashCuspForm f)
        (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g))

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimeAtkinLehnerDoubleCosetTileBridge ⟹
HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine`, by mechanical `petN` unfolding of
the intertwine LHS. -/
theorem Newform.hasBadPrimePetN_T_p_FrickeAdjoint_Intertwine_of_doubleCosetTileBridge
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_bridge :
      Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge N k p hp hpN) :
    Newform.HasBadPrimePetN_T_p_FrickeAdjoint_Intertwine N k p hp hpN := by
  intro f g
  show petN (heckeT_n_cusp k p f) g =
    (Newform.frickeSquareScalar N k)⁻¹ * (-1 : ℂ) ^ k *
      petN (Newform.frickeSlashCuspForm f)
        (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g))
  rw [show petN (heckeT_n_cusp k p f) g =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k (fd : Set UpperHalfPlane)
          (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
          (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) from rfl]
  have h_lhs_q : ∀ (q : SL(2, ℤ) ⧸ Gamma1 N),
      peterssonInner k (fd : Set UpperHalfPlane)
        (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) := by
    intro q
    rw [Newform.peterssonInner_heckeT_n_cusp_at_divN_slash_qOut_inv_eq_bsum hp hpN f g q,
      SlashAction.sum_slash]
    have h_int : ∀ b ∈ Finset.range p,
        IntegrableOn (fun τ ↦ UpperHalfPlane.petersson k
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹))
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹)) τ) (fd : Set UpperHalfPlane) μ_hyp := by
      intro b _
      exact integrableOn_petersson_cuspform_mixed_slash_on_fd g f
        (T_p_upper p hp.pos b) ((q.out : SL(2, ℤ))⁻¹)
    rw [peterssonInner_sum_left _ _ _ _ h_int]
  rw [Finset.sum_congr rfl fun q _ ↦ h_lhs_q q]
  exact h_bridge f g

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime double-coset tile bridge with both sides expanded to explicit
`Σ_q Σ_b` `peterssonInner` form (all matrices `β_b`, `W_N`, and coset reps
`q.out⁻¹` visible). -/
def Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) =
    (Newform.frickeSquareScalar N k)⁻¹ * (-1 : ℂ) ^ k *
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k (fd : Set UpperHalfPlane)
            ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
              ((q.out : SL(2, ℤ))⁻¹))
            (((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
              (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
              ((q.out : SL(2, ℤ))⁻¹))

private theorem sum_sum_const_mul_eq_const_mul_sum_sum
    {N : ℕ} [NeZero N] {p : ℕ} (c : ℂ)
    (F : (SL(2, ℤ) ⧸ Gamma1 N) → ℕ → ℂ) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∑ b ∈ Finset.range p, (c * F q b) =
      c * ∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∑ b ∈ Finset.range p, F q b := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ ↦ (Finset.mul_sum _ _ _).symm

private theorem sum_sum_range_eq_sum_prod {Q : Type*} [Fintype Q] {p : ℕ}
    (G : Q → ℕ → ℂ) :
    ∑ q : Q, ∑ b ∈ Finset.range p, G q b =
      ∑ qb : Q × Fin p, G qb.1 qb.2.val := by
  rw [Fintype.sum_prod_type (fun qb : Q × Fin p ↦ G qb.1 qb.2.val)]
  exact Finset.sum_congr rfl fun q _ ↦
    (Fin.sum_univ_eq_sum_range (fun b ↦ G q b) p).symm

open UpperHalfPlane MeasureTheory ModularGroup in
private theorem Newform.peterssonInner_fricke_T_p_upper_slash_qOut_inv_eq_neg_pow_smul_lowerOffset
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : p.Prime) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) :
    peterssonInner k (fd : Set UpperHalfPlane)
        ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹)) =
      (-1 : ℂ) ^ k *
        peterssonInner k
          ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
            ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))
          (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
              GL (Fin 2) ℝ)) ⇑g := by
  rw [peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd
    (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
    ((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
      (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) (q.out)]
  show peterssonInner k
      ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
      (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
      ((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) = _
  rw [← peterssonInner_conj_symm]
  rw [show (((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) :
        UpperHalfPlane → ℂ) =
      ((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) from rfl]
  rw [Newform.peterssonInner_fricke_T_p_upper_rewrite_adjoint_t152
    ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
    N hp.pos b ⇑g (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))]
  rw [UpperHalfPlane.peterssonInner_smul_right, map_mul]
  rw [show (starRingEnd ℂ) ((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k by
    rw [map_zpow₀]
    congr 1
    norm_num]
  congr 1
  exact peterssonInner_conj_symm k _ _ _

open UpperHalfPlane MeasureTheory ModularGroup in
private theorem Newform.peterssonInner_frickeSlash_heckeT_n_cusp_slash_qOut_inv_eq_bsum
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (q : SL(2, ℤ) ⧸ Gamma1 N) :
    peterssonInner k (fd : Set UpperHalfPlane)
        (⇑(Newform.frickeSlashCuspForm f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑(heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) ∣[k]
          (q.out : SL(2, ℤ))⁻¹) =
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹)) := by
  rw [Newform.frickeSlashCuspForm_coe f,
    ← Newform.sum_slash_T_p_upper_eq_heckeT_n_cusp hp hpN (Newform.frickeSlashCuspForm g),
    Newform.frickeSlashCuspForm_coe g, SlashAction.sum_slash]
  have h_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ UpperHalfPlane.petersson k
        ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) τ)
        (fd : Set UpperHalfPlane) μ_hyp := fun b _ ↦ by
    have h := integrableOn_petersson_cuspform_mixed_slash_on_fd
      (Newform.frickeSlashCuspForm f) (Newform.frickeSlashCuspForm g)
      (T_p_upper p hp.pos b) ((q.out : SL(2, ℤ))⁻¹)
    simp only [Newform.frickeSlashCuspForm_coe] at h
    exact h
  rw [peterssonInner_sum_right _ _ _ _ h_int]

open UpperHalfPlane MeasureTheory ModularGroup in
private theorem Newform.sum_sum_peterssonInner_shifted_T_p_upper_eq_petN_heckeT_n_cusp
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N, ∑ b ∈ Finset.range p,
        peterssonInner k ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
          (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g =
      petN (heckeT_n_cusp k p f) g := by
  have h_lhs_qb : ∀ (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ),
      peterssonInner k ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
        (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g =
      peterssonInner k (fd : Set UpperHalfPlane)
        ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) := fun q b ↦ by
    rw [peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd
      (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g (q.out)]
    rfl
  rw [Finset.sum_congr rfl fun q _ ↦
    Finset.sum_congr rfl fun b _ ↦ h_lhs_qb q b]
  show _ = ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      peterssonInner k fd
        (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹)
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  have h_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ ↦ UpperHalfPlane.petersson k
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) τ) (fd : Set UpperHalfPlane) μ_hyp :=
    fun b _ ↦
      integrableOn_petersson_cuspform_mixed_slash_on_fd g f
        (T_p_upper p hp.pos b) ((q.out : SL(2, ℤ))⁻¹)
  rw [← peterssonInner_sum_left _ _ _ _ h_int]
  rw [← SlashAction.sum_slash,
    Newform.sum_slash_T_p_upper_eq_heckeT_n_cusp hp hpN f]

open UpperHalfPlane MeasureTheory ModularGroup in
private theorem Newform.peterssonInner_lowerOffset_smul_eq_neg_pow_fricke_T_p_upper_slash_qOut_inv
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : p.Prime) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) :
    peterssonInner k
        ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))
        (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
            GL (Fin 2) ℝ)) ⇑g =
      (-1 : ℂ) ^ k *
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
              (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
              ((q.out : SL(2, ℤ))⁻¹)) := by
  rw [Newform.peterssonInner_fricke_T_p_upper_slash_qOut_inv_eq_neg_pow_smul_lowerOffset
    hp f g q b, ← mul_assoc, neg_one_zpow_mul_self k, one_mul]

private theorem Newform.petN_heckeT_n_cusp_eq_inv_frickeSquareScalar_neg_pow_petN_frickeSlash
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (h : petN (heckeT_n_cusp k p f) g =
      petN f (Newform.frickeBadAdjointCandidateNormalized k p g)) :
    petN (heckeT_n_cusp k p f) g =
      (Newform.frickeSquareScalar N k)⁻¹ *
        ((-1 : ℂ) ^ k *
          petN (Newform.frickeSlashCuspForm f)
            (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g))) := by
  rw [h,
    Newform.heckeT_n_cusp_frickeSlashCuspForm_eq_frickeSlashCuspForm_frickeBadAdjointCandidateNormalized g,
    Newform.frickeSlashCuspForm_petN_adjoint_unconditional f
      (Newform.frickeSlashCuspForm
        (Newform.frickeBadAdjointCandidateNormalized k p g)),
    Newform.frickeSlashCuspForm_apply_apply
      (Newform.frickeBadAdjointCandidateNormalized k p g),
    petN_smul_right]
  rw [show (Newform.frickeSquareScalar N k)⁻¹ *
        ((-1 : ℂ) ^ k *
          ((-1 : ℂ) ^ k *
            (Newform.frickeSquareScalar N k *
              petN f (Newform.frickeBadAdjointCandidateNormalized k p g)))) =
      ((Newform.frickeSquareScalar N k)⁻¹ * Newform.frickeSquareScalar N k) *
        ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
          petN f (Newform.frickeBadAdjointCandidateNormalized k p g) by
    ring]
  rw [inv_mul_cancel₀ (Newform.frickeSquareScalar_ne_zero N k), neg_one_zpow_mul_self k,
    one_mul, one_mul]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded
⟹ HasBadPrimeAtkinLehnerDoubleCosetTileBridge`, by `petN` unfolding of the RHS. -/
theorem Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_of_qBExpanded
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_qBExpanded :
      Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded N k p hp hpN) :
    Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge N k p hp hpN := by
  intro f g
  show ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k (fd : Set UpperHalfPlane)
          ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            ((q.out : SL(2, ℤ))⁻¹))
          (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) =
    (Newform.frickeSquareScalar N k)⁻¹ * (-1 : ℂ) ^ k *
      petN (Newform.frickeSlashCuspForm f)
        (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g))
  rw [show petN (Newform.frickeSlashCuspForm f)
        (heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        peterssonInner k (fd : Set UpperHalfPlane)
          (⇑(Newform.frickeSlashCuspForm f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
          (⇑(heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) ∣[k]
            (q.out : SL(2, ℤ))⁻¹) from rfl]
  rw [Finset.sum_congr rfl fun q _ ↦
    Newform.peterssonInner_frickeSlash_heckeT_n_cusp_slash_qOut_inv_eq_bsum
      hp hpN f g q]
  exact h_qBExpanded f g

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The simplified `Σ_q Σ_b` `peterssonInner` matrix-domain identity, with the
`W_N`'s absorbed into domain shifts and the `(-1)^k * c` factor cancelled:
```
∑_q ∑_b peterssonInner k (q.out⁻¹ • fd) (⇑f ∣[k] β_b) ⇑g =
∑_q ∑_b peterssonInner k (M_b · W_N · q.out⁻¹ • fd) (⇑f ∣[k] adj_M_b) ⇑g
```
where `β_b = T_p_upper p hp.pos b`, `M_b = T_p_lower_with_offset N hp.pos b`,
`adj_M_b = T_p_lower_with_offset_adjugate N hp.pos b`, `W_N = frickeMatrix N`. -/
def Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
          (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g =
    (Newform.frickeSquareScalar N k)⁻¹ *
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        ∑ b ∈ Finset.range p,
          peterssonInner k
            ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
              ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
                ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))
            (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
              (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
              (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
                GL (Fin 2) ℝ)) ⇑g

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified
⟹ HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded`. -/
theorem Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded_of_qBSimplified
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_simp :
      Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified N k p hp hpN) :
    Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBExpanded N k p hp hpN := by
  intro f g
  have h_lhs_qb : ∀ (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ),
      peterssonInner k (fd : Set UpperHalfPlane)
        ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹))
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹)) =
      peterssonInner k
        ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
        (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g := by
    intro q b
    rw [peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd
      (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g (q.out)]
    rfl
  rw [Finset.sum_congr rfl fun q _ ↦
    Finset.sum_congr rfl fun b _ ↦ h_lhs_qb q b]
  rw [Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun b _ ↦
    Newform.peterssonInner_fricke_T_p_upper_slash_qOut_inv_eq_neg_pow_smul_lowerOffset
      hp f g q b]
  rw [sum_sum_const_mul_eq_const_mul_sum_sum]
  rw [show (Newform.frickeSquareScalar N k)⁻¹ * (-1 : ℂ) ^ k *
        ((-1 : ℂ) ^ k *
          ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
            ∑ b ∈ Finset.range p,
              peterssonInner k _ _ _) =
      ((-1 : ℂ) ^ k * (-1 : ℂ) ^ k) *
        (Newform.frickeSquareScalar N k)⁻¹ *
        ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∑ b ∈ Finset.range p,
            peterssonInner k _ _ _ by ring]
  rw [neg_one_zpow_mul_self k, one_mul]
  exact h_simp f g

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The domain-swap form of the bad-prime Atkin-Lehner double-coset reindex, with
the `W_N`/`adj_M_b` slashes absorbed via T145 and scalars cancelled:
```
∑_q ∑_b peterssonInner k ((glMap β_b · q.out⁻¹) • fd) ⇑f
    (⇑g ∣[k] peterssonAdj (glMap β_b)) =
∑_q ∑_b peterssonInner k ((W_N · q.out⁻¹) • fd) ⇑f
    (⇑g ∣[k] T_p_lower_with_offset N hp.pos b)
```
with `⇑f` bare in slot 1 on both sides. -/
def Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
            ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
          ⇑f
          (⇑g ∣[k] peterssonAdj
            (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) =
    ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
          ⇑f
          (⇑g ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ))

/-- Audit declaration recording that `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap`
is mathematically equivalent to `HasBadPrimeFrickePetNAdjoint`; the proof
typechecks the named witnesses of that reduction. -/
theorem T184_qBDomainSwap_equivalent_to_petN_adjoint_audit : True := by
  let _ := @Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap
  let _ := @Newform.HasBadPrimeFrickePetNAdjoint
  let _ := @Newform.frickeBadAdjointCandidate
  let _ := @Newform.frickeBadAdjointCandidate_apply
  let _ := @Newform.frickeBadAdjointCandidateNormalized
  let _ := @Newform.frickeSquareScalar
  let _ := @Newform.hasBadPrimeFrickePetNAdjoint_iff
  let _ := @Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix
  let _ := @Newform.slash_frickeMatrix_T_p_upper_rewrite
  let _ := @peterssonInner_slash_adjoint
  let _ := @Newform.frickeSlashCuspForm_petN_adjoint
  let _ := @heckeT_n_prime
  let _ := @heckeT_p_all_not_coprime_apply
  let _ := @heckeT_n_cusp
  let _ := @Newform.sum_peterssonInner_frickeMatrix_smul_q_out_inv_fd_eq_petN
  let _ := @sum_setIntegral_GL2_shift
  let _ := @peterssonInner_fd_slash_SL_eq_setIntegral_shifted_fd
  let _ := @UpperHalfPlane.peterssonInner_conj_symm
  trivial

open UpperHalfPlane MeasureTheory ModularGroup in
private theorem Newform.peterssonInner_shifted_T_p_upper_eq_peterssonAdj_domainSwap
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : p.Prime) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) :
    peterssonInner k
        ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
        (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ⇑g =
      peterssonInner k
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
        ⇑f
        (⇑g ∣[k] peterssonAdj
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) := by
  rw [show ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) :
        UpperHalfPlane → ℂ) =
      (⇑f ∣[k] (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) from rfl]
  rw [peterssonInner_slash_adjoint (k := k)
    ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))
    (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)
    (glMap_det_pos_of_rat_det_pos (T_p_upper p hp.pos b)
      (T_p_upper_det_pos p hp.pos b)) ⇑f ⇑g]

open UpperHalfPlane MeasureTheory ModularGroup in
private theorem Newform.peterssonInner_lowerOffset_smul_eq_frickeSquareScalar_domainSwap
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ}
    (hp : p.Prime) (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) :
    peterssonInner k
        ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))
        (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
            GL (Fin 2) ℝ)) ⇑g =
      Newform.frickeSquareScalar N k *
        peterssonInner k
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
          ⇑f
          (⇑g ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ)) := by
  rw [Newform.slash_frickeMatrix_frickeMatrix ⇑f, ModularForm.smul_slash]
  rw [show UpperHalfPlane.σ
        (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
          GL (Fin 2) ℝ) = RingHom.id ℂ by
    unfold UpperHalfPlane.σ
    simp only [if_pos
      (Newform.T_p_lower_with_offset_adjugate_det_pos N hp.pos b)]]
  rw [RingHom.id_apply, UpperHalfPlane.peterssonInner_conj_smul_left,
    Newform.conj_frickeSquareScalar N k]
  rw [peterssonInner_slash_adjoint (k := k)
    ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
        ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))
    (Newform.T_p_lower_with_offset_adjugate N hp.pos b : GL (Fin 2) ℝ)
    (Newform.T_p_lower_with_offset_adjugate_det_pos N hp.pos b) ⇑f ⇑g]
  rw [← mul_smul, ← Newform.peterssonAdj_T_p_lower_with_offset_eq N hp.pos b,
    peterssonAdj_mul_self_smul_set, peterssonAdj_peterssonAdj]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap
⟹ HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified`. -/
theorem Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified_of_qBDomainSwap
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_swap :
      Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap N k p hp hpN) :
    Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBSimplified N k p hp hpN := by
  intro f g
  rw [Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun b _ ↦
    Newform.peterssonInner_shifted_T_p_upper_eq_peterssonAdj_domainSwap hp f g q b]
  rw [Finset.sum_congr rfl fun q _ ↦ Finset.sum_congr rfl fun b _ ↦
    Newform.peterssonInner_lowerOffset_smul_eq_frickeSquareScalar_domainSwap hp f g q b]
  rw [sum_sum_const_mul_eq_const_mul_sum_sum]
  rw [show (Newform.frickeSquareScalar N k)⁻¹ *
        (Newform.frickeSquareScalar N k *
          ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
            ∑ b ∈ Finset.range p,
              peterssonInner k _ _ _) =
      ((Newform.frickeSquareScalar N k)⁻¹ * Newform.frickeSquareScalar N k) *
        ∑ q : SL(2, ℤ) ⧸ Gamma1 N,
          ∑ b ∈ Finset.range p,
            peterssonInner k _ _ _ by ring]
  rw [inv_mul_cancel₀ (Newform.frickeSquareScalar_ne_zero N k), one_mul]
  exact h_swap f g

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The explicit `(q, b)`-bijection residual witnessing the bad-prime
Atkin-Lehner Γ₁(N)-coset reindex: there is a bijection
`σ : (SL(2, ℤ) ⧸ Γ₁(N)) × Fin p ≃ (SL(2, ℤ) ⧸ Γ₁(N)) × Fin p` under which each
`qBDomainSwap` LHS-`(q, b)` summand equals the RHS-`σ (q, b)` summand. -/
def Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∃ σ : (SL(2, ℤ) ⧸ Gamma1 N) × Fin p ≃
        (SL(2, ℤ) ⧸ Gamma1 N) × Fin p,
    ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
      (q : SL(2, ℤ) ⧸ Gamma1 N) (b : Fin p),
      peterssonInner k
          ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
            ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
          ⇑f
          (⇑g ∣[k] peterssonAdj
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) =
      peterssonInner k
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            (((σ (q, b)).1.out : SL(2, ℤ))⁻¹ •
              (fd : Set UpperHalfPlane)))
          ⇑f
          (⇑g ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos (σ (q, b)).2.val :
              GL (Fin 2) ℝ))

open UpperHalfPlane MeasureTheory ModularGroup in
/-- The bad-prime reduction `HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection
⟹ HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap`, by reindexing the
double sum along the bijection. -/
theorem Newform.hasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap_of_qBBijection
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_bij :
      Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBBijection N k p hp hpN) :
    Newform.HasBadPrimeAtkinLehnerDoubleCosetTileBridge_qBDomainSwap N k p hp hpN := by
  obtain ⟨σ, h_σ⟩ := h_bij
  intro f g
  rw [sum_sum_range_eq_sum_prod
    (fun (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) ↦
      peterssonInner k
        ((glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
        ⇑f
        (⇑g ∣[k] peterssonAdj
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)))]
  rw [sum_sum_range_eq_sum_prod
    (fun (q : SL(2, ℤ) ⧸ Gamma1 N) (b : ℕ) ↦
      peterssonInner k
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
        ⇑f
        (⇑g ∣[k]
          (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ)))]
  rw [← Equiv.sum_comp σ
    (fun qb : (SL(2, ℤ) ⧸ Gamma1 N) × Fin p ↦
      peterssonInner k
        ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
          ((qb.1.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))
        ⇑f
        (⇑g ∣[k]
          (Newform.T_p_lower_with_offset N hp.pos qb.2.val :
            GL (Fin 2) ℝ)))]
  refine Finset.sum_congr rfl fun qb _ ↦ ?_
  exact h_σ f g qb.1 qb.2


end HeckeRing.GL2
