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
