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
import LeanModularForms.HeckeRIngs.GL2.Newforms.BadPrimeAdjoint

/-!
# Newforms: bad-prime coset combinatorics and per-coset Petersson adjoints

The lower-triangular GL coset rep with offset (T150), the bad-prime lower-offset b-sum identity (T185), upper-family left-coset injectivity (T186), per-coset Petersson adjoints at the bad-prime upper coset (T151), right-slot factor identification (T152), and the aggregation steps T153-T156.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### Lower-triangular GL coset rep with offset (T150) -/

/-- **Lower-triangular `GL (Fin 2) ℝ` coset representative `!![p, 0; -N·b, 1]`
(T150 helper).**

The GL element with underlying matrix `!![(p : ℝ), 0; -((N : ℝ) * b), 1]`. Determinant
is `p · 1 - 0 · (-N·b) = p`, so this lives in `GL (Fin 2) ℝ` whenever `p ≠ 0`.

Used downstream to express the Fricke-conjugated bad-prime upper coset
`W_N · T_p_upper · W_N⁻¹` as an explicit GL element (T150 main lemma below). -/
noncomputable def Newform.T_p_lower_with_offset
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(p : ℝ), 0; -((N : ℝ) * b), 1] : Matrix (Fin 2) (Fin 2) ℝ)
    (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne')

/-- **`T_p_lower_with_offset N hp b` underlying matrix (T150 helper).** -/
@[simp]
lemma Newform.T_p_lower_with_offset_coe
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(p : ℝ), 0; -((N : ℝ) * b), 1] := by
  simp [Newform.T_p_lower_with_offset, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- **GL-level Fricke / bad-prime upper coset rewrite (T150 main).**

Lift of T149's matrix-level inverse-conjugation identity to `GL (Fin 2) ℝ`:
```
W_N * glMap (T_p_upper p hp b) =
  T_p_lower_with_offset N hp b * W_N
```
Direct corollary of the matrix identity
`Newform.frickeMatrix_mul_glMap_T_p_upper_mul_frickeMatrix_inv_val` after
multiplying by `W_N` on the right (and using `(W_N⁻¹) * W_N = 1`). The
`GL`-level form is exactly what the slash-action `SlashAction.slash_mul`
consumes for the Fricke-conjugated bad-prime petN-adjoint argument. -/
lemma Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (Newform.frickeMatrix N : GL (Fin 2) ℝ) * (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) *
        (Newform.frickeMatrix N : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_mul,
      Newform.T_p_lower_with_offset_coe]
  rw [Newform.frickeMatrix_coe]
  rw [show ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)] by
    show (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
        !![(1 : ℝ), (b : ℝ); 0, (p : ℝ)]
    rw [T_p_upper_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]

/-- **Slash-action Fricke / bad-prime upper coset rewrite (T150 slash form).**

Function-level slash-action analog of the GL-level rewrite. For any function
`f : UpperHalfPlane → ℂ`:
```
(f ∣[k] W_N) ∣[k] glMap (T_p_upper p hp b) =
  (f ∣[k] T_p_lower_with_offset N hp b) ∣[k] W_N.
```
Direct application of `SlashAction.slash_mul` (right action convention
`(f ∣[k] A) ∣[k] B = f ∣[k] (A * B)`) on both sides, then the GL-level rewrite
`Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix`. -/
lemma Newform.slash_frickeMatrix_T_p_upper_rewrite
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p) (b : ℕ)
    (f : UpperHalfPlane → ℂ) :
    (f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      (f ∣[k] (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)) ∣[k]
        (Newform.frickeMatrix N : GL (Fin 2) ℝ) := by
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
  rw [Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix]

/-! ### T185 — Bad-prime lower-offset b-sum function-level identity and Γ₁(N)-invariance -/

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T185 helper: per-`b` slash factorization
`((⇑g ∣ W_N) ∣ β_b) ∣ W_N = c • (⇑g ∣ M_b)`.**

Function-level identity at the per-`b` level: the `(W_N · β_b · W_N)`-slash of
any function `g` collapses to a `frickeSquareScalar`-scaled `M_b`-slash via:
1. `slash_mul × 2` to combine `((⇑g ∣ W_N) ∣ β_b) ∣ W_N = ⇑g ∣ ((W_N · β_b) · W_N)`.
2. The matrix relation `W_N · glMap β_b = M_b · W_N`
   (`Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix`)
   plus `mul_assoc` to rewrite to `M_b · (W_N · W_N)`.
3. `slash_mul × 2` to redistribute and apply `slash_frickeMatrix_frickeMatrix`
   (`(f ∣ W_N) ∣ W_N = c • f`) to the result. -/
private lemma Newform.slash_W_N_T_p_upper_W_N_eq_smul_T_p_lower_with_offset
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p) (b : ℕ)
    (g : UpperHalfPlane → ℂ) :
    ((g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ) =
      Newform.frickeSquareScalar N k •
        (g ∣[k] (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)) := by
  rw [← SlashAction.slash_mul, ← SlashAction.slash_mul]
  -- Goal: g ∣ (W_N * (β_b * W_N)) = c • (g ∣ M_b)
  rw [show (Newform.frickeMatrix N : GL (Fin 2) ℝ) *
          ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) *
            (Newform.frickeMatrix N : GL (Fin 2) ℝ)) =
        (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) *
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) *
            (Newform.frickeMatrix N : GL (Fin 2) ℝ)) from by
    rw [← mul_assoc,
        Newform.frickeMatrix_mul_glMap_T_p_upper_eq_lower_offset_mul_frickeMatrix,
        mul_assoc]]
  rw [SlashAction.slash_mul, SlashAction.slash_mul]
  rw [Newform.slash_frickeMatrix_frickeMatrix]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T185 main helper (function identity): `⇑(frickeBadAdjointCandidateNormalized k p g)
= Σ_b ⇑g ∣ T_p_lower_with_offset N hp.pos b`.**

The function representation of the bad-prime Fricke adjoint candidate
(normalized) coincides exactly with the b-sum of `M_b`-slashed `⇑g`. Proof:
unfold the candidate to `c⁻¹ • W_N(T_p(W_N g))`, expand `T_p` at the bad
prime via `heckeT_n_prime` + `heckeT_p_all_not_coprime_apply` to a b-sum of
`(⇑g ∣ W_N) ∣ β_b`, distribute the outer `W_N`-slash via
`SlashAction.sum_slash`, then apply the per-`b` collapse
`slash_W_N_T_p_upper_W_N_eq_smul_T_p_lower_with_offset` to obtain
`c • (⇑g ∣ M_b)` per summand; the outer `c⁻¹`-scalar cancels the inner `c`
via `inv_mul_cancel₀ frickeSquareScalar_ne_zero`. -/
lemma Newform.frickeBadAdjointCandidateNormalized_coe_eq_bsum_lower
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(Newform.frickeBadAdjointCandidateNormalized k p g) : UpperHalfPlane → ℂ) =
      ∑ b ∈ Finset.range p,
        (⇑g : UpperHalfPlane → ℂ) ∣[k]
          (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) := by
  rw [Newform.frickeBadAdjointCandidateNormalized_apply]
  show ((Newform.frickeSquareScalar N k)⁻¹ •
      (⇑(Newform.frickeBadAdjointCandidate k p g) : UpperHalfPlane → ℂ)) = _
  rw [Newform.frickeBadAdjointCandidate_apply]
  rw [Newform.frickeSlashCuspForm_coe]
  rw [show (⇑(heckeT_n_cusp k p (Newform.frickeSlashCuspForm g)) :
        UpperHalfPlane → ℂ) =
      ∑ b ∈ Finset.range p,
        (⇑(Newform.frickeSlashCuspForm g) ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) from by
    show (heckeT_n k p ((Newform.frickeSlashCuspForm g).toModularForm') :
          UpperHalfPlane → ℂ) =
        heckeT_p_ut k p hp.pos ⇑(Newform.frickeSlashCuspForm g)
    rw [heckeT_n_prime k hp,
      heckeT_p_all_not_coprime_apply (k := k) hp hpN
        (Newform.frickeSlashCuspForm g).toModularForm']
    rfl]
  -- Rewrite each summand: ⇑(W_N g) = ⇑g ∣ W_N, and use the per-b collapse.
  have h_term : ∀ b ∈ Finset.range p,
      ((⇑(Newform.frickeSlashCuspForm g) ∣[k]
          (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) =
        Newform.frickeSquareScalar N k •
          ((⇑g : UpperHalfPlane → ℂ) ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ)) := by
    intro b _
    rw [Newform.frickeSlashCuspForm_coe]
    show ((((⇑g : UpperHalfPlane → ℂ) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) =
        Newform.frickeSquareScalar N k •
          ((⇑g : UpperHalfPlane → ℂ) ∣[k]
            (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ))
    exact Newform.slash_W_N_T_p_upper_W_N_eq_smul_T_p_lower_with_offset hp.pos b ⇑g
  rw [SlashAction.sum_slash]
  rw [Finset.sum_congr rfl h_term]
  rw [← Finset.smul_sum, smul_smul]
  have h_c_ne : Newform.frickeSquareScalar N k ≠ 0 := by
    unfold Newform.frickeSquareScalar
    exact mul_ne_zero (zpow_ne_zero _ (by norm_num))
      (zpow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N)))
  rw [inv_mul_cancel₀ h_c_ne, one_smul]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T185 b-sum invariance lemma (manager-requested target).** For the
bad-prime lower-offset family `M_b := T_p_lower_with_offset N hp.pos b`,
slashing the b-sum by any `mapGL γ` for `γ ∈ Γ₁(N)` is invariant:
```
Σ_b ⇑g ∣[k] (M_b * mapGL γ) = Σ_b ⇑g ∣[k] M_b.
```
Proof via the function-level identity
`frickeBadAdjointCandidateNormalized_coe_eq_bsum_lower`: the b-sum equals
`⇑(frickeBadAdjointCandidateNormalized k p g)` which is a `Γ₁(N)`-slash-invariant
CuspForm, hence its slash by `mapGL γ` is itself; the per-summand
`SlashAction.slash_mul` factorization then yields the b-sum identity. -/
lemma Newform.badPrime_lowerOffset_bsum_slash_Gamma1_right
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    (∑ b ∈ Finset.range p,
      (⇑g : UpperHalfPlane → ℂ) ∣[k]
        ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) *
          (mapGL ℝ γ : GL (Fin 2) ℝ)))
    =
    (∑ b ∈ Finset.range p,
      (⇑g : UpperHalfPlane → ℂ) ∣[k]
        (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ)) := by
  -- Step 1: distribute the outer mapGL γ-slash via slash_mul + sum_slash.
  rw [show (∑ b ∈ Finset.range p,
        (⇑g : UpperHalfPlane → ℂ) ∣[k]
          ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) *
            (mapGL ℝ γ : GL (Fin 2) ℝ))) =
      (∑ b ∈ Finset.range p,
        (⇑g : UpperHalfPlane → ℂ) ∣[k]
          (Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ)) ∣[k]
      (mapGL ℝ γ : GL (Fin 2) ℝ) from by
    rw [SlashAction.sum_slash]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [SlashAction.slash_mul]]
  -- Step 2: rewrite the b-sum to ⇑(frickeBadAdjointCandidateNormalized k p g).
  rw [← Newform.frickeBadAdjointCandidateNormalized_coe_eq_bsum_lower hp hpN g]
  -- Step 3: apply the CuspForm Γ₁(N)-slash-invariance of frickeBadAdjointCandidateNormalized.
  exact (Newform.frickeBadAdjointCandidateNormalized k p g).slash_action_eq'
    (mapGL ℝ γ : GL (Fin 2) ℝ) (Subgroup.mem_map.mpr ⟨γ, hγ, rfl⟩)

/-! ### T186 — Bad-prime upper-family left-coset injectivity / pairwise disjointness -/

/-- **Real-matrix entries of the bad-prime upper coset rep `β_b` (T186 helper).**

The underlying `Matrix (Fin 2) (Fin 2) ℝ` of `glMap (T_p_upper p hp b)` is the
integer matrix `!![1, b; 0, p]` cast to `ℝ` via `algebraMap ℤ ℝ`. Used to
identify the `(0, *)` row entries in the left-coset injectivity argument and to
combine the integer-level double-coset identity through `Matrix.map_mul`. -/
private lemma Newform.glMap_T_p_upper_coe_real_intMap
    {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (!![(1 : ℤ), (b : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ) := by
  show (T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
      (!![(1 : ℤ), (b : ℤ); 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).map
        (algebraMap ℤ ℝ)
  rw [T_p_upper_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]

/-- **Coset-index rigidity from a `mod p` shear (T186 helper).**

If `m * p = b₂ - b₁` for two indices `b₁ b₂ : Fin p` and some integer `m`, then
`b₁ = b₂`. The shear coefficient `m` must vanish: `|m * p| = |b₂ - b₁| < p` and
`p > 0` force `m = 0`, hence `b₂ - b₁ = 0`. This is the arithmetic core of the
left-coset injectivity for the bad-prime upper family. -/
private lemma Newform.fin_eq_of_mul_eq_sub
    {p : ℕ} (hp : 0 < p) (b1 b2 : Fin p) (m : ℤ)
    (h : m * (p : ℤ) = (b2.val : ℤ) - (b1.val : ℤ)) : b1 = b2 := by
  have hb1_lt : (b1.val : ℤ) < (p : ℤ) := by exact_mod_cast b1.isLt
  have hb2_lt : (b2.val : ℤ) < (p : ℤ) := by exact_mod_cast b2.isLt
  have hb1_nn : (0 : ℤ) ≤ (b1.val : ℤ) := Int.natCast_nonneg _
  have hb2_nn : (0 : ℤ) ≤ (b2.val : ℤ) := Int.natCast_nonneg _
  have hp_pos_int : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have h_abs2 : |m * (p : ℤ)| < (p : ℤ) := by
    rw [h, abs_lt]; constructor <;> linarith
  have hm : m = 0 := by
    by_contra h_ne
    have h_abs_m : 1 ≤ |m| := Int.one_le_abs h_ne
    rw [abs_mul, abs_of_pos hp_pos_int] at h_abs2
    have : (p : ℤ) ≤ |m| * (p : ℤ) := by nlinarith
    linarith
  rw [hm, zero_mul] at h
  exact Fin.ext (by exact_mod_cast (by linarith : (b1.val : ℤ) = (b2.val : ℤ)))

/-- **T186 left-coset injectivity for the bad-prime upper family at level `Γ₁(N)`.**

For p > 0 and any `γ ∈ Γ₁(N)` (in fact any `γ ∈ SL(2, ℤ)`), if
```
mapGL ℝ γ * glMap (T_p_upper p hp b₁.val) = glMap (T_p_upper p hp b₂.val)
```
in `GL (Fin 2) ℝ` (i.e. `γ · β_{b₁} = β_{b₂}` at the integer-matrix level),
then `b₁ = b₂` in `Fin p`.

**Proof.** Compare the `(0, 0)` and `(0, 1)` entries of the matrix product
`γ · !![1, b₁; 0, p]` against `!![1, b₂; 0, p]`:
* `(0, 0)`: `γ.val 0 0 = 1` (over ℝ ⇒ over ℤ).
* `(0, 1)`: `γ.val 0 0 * b₁ + γ.val 0 1 * p = b₂` (over ℝ ⇒ over ℤ).
Substituting `γ.val 0 0 = 1` gives `γ.val 0 1 * p = b₂ - b₁`. Since
`b₁, b₂ ∈ Fin p` (both in `[0, p)`), `|b₂ - b₁| < p`. Combined with
`p · |γ.val 0 1| = |b₂ - b₁| < p`, conclude `γ.val 0 1 = 0` and hence
`b₂ - b₁ = 0`, i.e. `b₁.val = b₂.val`, i.e. `b₁ = b₂` by `Fin.ext`.

**Consequence.** The left `Γ₁(N)`-cosets `Γ₁(N) · β_b` are pairwise disjoint
for `b : Fin p`. The hypothesis `γ ∈ Γ₁(N)` is included for the public coset
API; the underlying integer-matrix injectivity does not strictly require it. -/
theorem Newform.T_p_upper_left_coset_injective_Gamma1
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p)
    (b1 b2 : Fin p) (γ : SL(2, ℤ)) (_hγ : γ ∈ Gamma1 N)
    (h : (mapGL ℝ γ : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp b1.val) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp b2.val) : GL (Fin 2) ℝ)) :
    b1 = b2 := by
  have hmat : (((mapGL ℝ γ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)) *
      (((glMap (T_p_upper p hp b1.val) : GL (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (((glMap (T_p_upper p hp b2.val) : GL (Fin 2) ℝ)) :
        Matrix (Fin 2) (Fin 2) ℝ) := by
    have := congrArg Units.val h
    simpa [Matrix.GeneralLinearGroup.coe_mul] using this
  have hβ1 : ((glMap (T_p_upper p hp b1.val) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b1.val : ℝ); 0, (p : ℝ)] := by
    show (T_p_upper p hp b1.val : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
        !![(1 : ℝ), (b1.val : ℝ); 0, (p : ℝ)]
    rw [T_p_upper_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  have hβ2 : ((glMap (T_p_upper p hp b2.val) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), (b2.val : ℝ); 0, (p : ℝ)] := by
    show (T_p_upper p hp b2.val : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
        !![(1 : ℝ), (b2.val : ℝ); 0, (p : ℝ)]
    rw [T_p_upper_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.map_apply]
  have hγ_mat : ((mapGL ℝ γ : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      γ.val.map (algebraMap ℤ ℝ) := mapGL_coe_matrix γ
  rw [hβ1, hβ2, hγ_mat] at hmat
  have h00 := congr_fun (congr_fun hmat 0) 0
  have h01 := congr_fun (congr_fun hmat 0) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, algebraMap_int_eq,
    Int.coe_castRingHom, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    mul_one, mul_zero, add_zero] at h00 h01
  have h00_int : γ.val 0 0 = 1 := by exact_mod_cast h00
  rw [h00_int] at h01
  push_cast at h01
  have h_real : (γ.val 0 1 : ℝ) * (p : ℝ) = (b2.val : ℝ) - (b1.val : ℝ) := by linarith
  have h_diff : γ.val 0 1 * (p : ℤ) = (b2.val : ℤ) - (b1.val : ℤ) := by exact_mod_cast h_real
  exact Newform.fin_eq_of_mul_eq_sub hp b1 b2 _ h_diff

open scoped Pointwise in
/-- **T186 left-coset pairwise disjointness for the bad-prime upper family.**

The left `Γ₁(N)`-cosets `Γ₁(N).map (mapGL ℝ) · {β_b} ⊆ GL(2, ℝ)` for
`b ∈ Fin p` are pairwise disjoint. Direct consumer of
`Newform.T_p_upper_left_coset_injective_Gamma1`: any element `x` lying in
both `Γ₁(N) · β_{b₁}` and `Γ₁(N) · β_{b₂}` for `b₁ ≠ b₂` would force a
witness `γ ∈ Γ₁(N)` with `γ · β_{b₁} = β_{b₂}`, contradicting injectivity. -/
theorem Newform.T_p_upper_left_cosets_pairwiseDisjoint_Gamma1
    (N : ℕ) [NeZero N] {p : ℕ} (hp : 0 < p) :
    (Set.univ : Set (Fin p)).PairwiseDisjoint
      (fun b => (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) := by
  intro b1 _ b2 _ hb_ne
  rw [Function.onFun, Set.disjoint_left]
  rintro x ⟨g1, hg1, β1, hβ1_in, hx_eq1⟩ ⟨g2, hg2, β2, hβ2_in, hx_eq2⟩
  rw [Set.mem_singleton_iff] at hβ1_in hβ2_in
  subst hβ1_in
  subst hβ2_in
  dsimp only at hx_eq1 hx_eq2
  rw [← hx_eq2] at hx_eq1
  obtain ⟨γ1, hγ1, rfl⟩ := Subgroup.mem_map.mp hg1
  obtain ⟨γ2, hγ2, rfl⟩ := Subgroup.mem_map.mp hg2
  apply hb_ne
  apply Newform.T_p_upper_left_coset_injective_Gamma1 N hp b1 b2 (γ2⁻¹ * γ1)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hγ2) hγ1)
  rw [map_mul, map_inv, mul_assoc, hx_eq1, ← mul_assoc, inv_mul_cancel, one_mul]

/-- **Integer double-coset matrix identity for the bad-prime upper family
(T186 helper).**

The explicit `M₂(ℤ)` factorization underlying DS Lemma 5.5.2(a): with the shear
relation `B · p = b' - a · bb`,
```
!![1, 0; 0, p] · !![a, b'; c, d] = !![a, B; p·c, d - c·bb] · !![1, bb; 0, p].
```
Entry-by-entry: `(0,0) a=a`, `(0,1) b' = a·bb + B·p`, `(1,0) p·c = p·c`,
`(1,1) p·d = (p·c)·bb + (d - c·bb)·p`. -/
private lemma Newform.alpha_p_mul_eq_M_mul_T_p_upper_int
    (p a b' c d B bb : ℤ) (hB : B * p = b' - a * bb) :
    (!![(1 : ℤ), 0; 0, p] : Matrix (Fin 2) (Fin 2) ℤ) * !![a, b'; c, d] =
      !![a, B; p * c, d - c * bb] * !![(1 : ℤ), bb; 0, p] := by
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- **Mod-`p` reduction of a `mod N` unit congruence (T186 helper).**

If `a ≡ 1 (mod N)` and `p ∣ N`, then `a ≡ 1 (mod p)`. Used to descend the
`Γ₁(N)` diagonal congruence `a ≡ 1 (mod N)` to the residue ring `ZMod p` so the
bad-prime shear coefficient `B := (b' - a·b)/p` is integral. -/
private lemma Newform.intCast_eq_one_of_dvd_of_eq_one
    {N p : ℕ} (hpN : p ∣ N) {a : ℤ} (ha : (a : ZMod N) = 1) :
    (a : ZMod p) = 1 := by
  have hN_int_dvd : (N : ℤ) ∣ (a - 1) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [ha]; ring
  have hp_dvd : (p : ℤ) ∣ (a - 1) :=
    dvd_trans (Int.natCast_dvd_natCast.mpr hpN) hN_int_dvd
  rw [show (a : ZMod p) = ((a - 1 : ℤ) : ZMod p) + 1 by push_cast; ring]
  rw [(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hp_dvd, zero_add]

/-- **Determinant of the bad-prime upper factor `M` is 1 (T186 helper).**

The constructed `M := !![a, B; p·c, d - c·bb]` has determinant `1`: expand via
`det_fin_two_of`, substitute the shear relation `B·p = b' - a·bb`, and reduce to
`a·d - b'·c = det γ = 1`. This is what places `γ' := ⟨M, _⟩` in `SL(2, ℤ)`. -/
private lemma Newform.det_alpha_p_factor_eq_one
    (p a b' c d B bb : ℤ) (hBp : B * p = b' - a * bb) (h_det : a * d - b' * c = 1) :
    (!![a, B; p * c, d - c * bb] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
  rw [Matrix.det_fin_two_of]
  have step1 : a * (d - c * bb) - B * (p * c) = a * d - c * (a * bb + B * p) := by ring
  rw [step1, hBp]
  linarith [h_det]

/-- **GL-lift of the integer double-coset identity (T186 helper).**

Promote the `M₂(ℤ)`-level factorization `!![1,0;0,p] · γ = γ' · !![1,b;0,p]` to the
`GL (Fin 2) ℝ`-level identity `α_p · γ = γ' · β_b`, where
`α_p := glMap (T_p_upper p hp 0)` and `β_b := glMap (T_p_upper p hp b)`. All four
real matrices are `algebraMap ℤ ℝ`-images of integer matrices
(`glMap_T_p_upper_coe_real_intMap`, `mapGL_coe_matrix`), so the identity follows
from the integer one through `Matrix.map_mul`. -/
private lemma Newform.glMap_T_p_upper_zero_mul_mapGL_eq_of_int
    {p : ℕ} (hp : 0 < p) (γ γ' : SL(2, ℤ)) (b : ℕ)
    (h_int : (!![(1 : ℤ), 0; 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
      γ'.val * !![(1 : ℤ), (b : ℤ); 0, (p : ℤ)]) :
    (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * (mapGL ℝ γ : GL (Fin 2) ℝ) =
      (mapGL ℝ γ' : GL (Fin 2) ℝ) * (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) := by
  apply Units.ext
  show ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((mapGL ℝ γ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) *
        ((glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
  have hα := Newform.glMap_T_p_upper_coe_real_intMap hp 0
  rw [Nat.cast_zero] at hα
  have hβ := Newform.glMap_T_p_upper_coe_real_intMap hp b
  have hγ_mat : ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      γ.val.map (algebraMap ℤ ℝ) := mapGL_coe_matrix γ
  have hγ'_mat : ((mapGL ℝ γ' : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      γ'.val.map (algebraMap ℤ ℝ) := mapGL_coe_matrix γ'
  rw [hα, hβ, hγ_mat, hγ'_mat, ← Matrix.map_mul, ← Matrix.map_mul, h_int]

/-- **Integer-level bad-prime double-coset decomposition (T186 core).**

For a prime `p ∣ N` and `γ ∈ Γ₁(N)`, there are `γ' ∈ Γ₁(N)` and `b ∈ Fin p` with
the explicit `M₂(ℤ)` factorization
`!![1,0;0,p] · γ.val = γ'.val · !![1, b; 0, p]`.

**Construction.** Write `γ.val = !![a, b'; c, d]`. As `p ∣ N` forces `a ≡ 1 (mod p)`
(`intCast_eq_one_of_dvd_of_eq_one`), the residue `b := (b' : ZMod p).val` satisfies
`a·b ≡ b' (mod p)`, so `B := (b' - a·b)/p ∈ ℤ`. Then
`γ' := ⟨!![a, B; p·c, d - c·b], _⟩` has determinant `1`
(`det_alpha_p_factor_eq_one`) and lies in `Γ₁(N)` (entry congruences mod `N`); the
matrix identity is `alpha_p_mul_eq_M_mul_T_p_upper_int`. -/
private lemma Newform.exists_Gamma1_mul_T_p_upper_int
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ∃ (γ' : SL(2, ℤ)) (b : Fin p), γ' ∈ Gamma1 N ∧
      (!![(1 : ℤ), 0; 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
        γ'.val * !![(1 : ℤ), (b.val : ℤ); 0, (p : ℤ)] := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp_dvd_N : (p : ℕ) ∣ N := by
    by_contra h_ndvd
    exact hpN (hp.coprime_iff_not_dvd.mpr h_ndvd)
  -- Integer entries and Γ₁(N) congruences; `p ∣ N` descends `a ≡ 1` to `mod p`.
  set a : ℤ := γ.val 0 0 with ha_def
  set b' : ℤ := γ.val 0 1 with hb'_def
  set c : ℤ := γ.val 1 0 with hc_def
  set d : ℤ := γ.val 1 1 with hd_def
  have hg := (Gamma1_mem N γ).mp hγ
  have ha_mod_N : (a : ZMod N) = 1 := by exact_mod_cast hg.1
  have hd_mod_N : (d : ZMod N) = 1 := by exact_mod_cast hg.2.1
  have hc_mod_N : (c : ZMod N) = 0 := by exact_mod_cast hg.2.2
  have ha_mod_p : (a : ZMod p) = 1 :=
    Newform.intCast_eq_one_of_dvd_of_eq_one hp_dvd_N ha_mod_N
  have h_det_γ : a * d - b' * c = 1 := by
    have := γ.property
    show γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = 1
    rw [Matrix.det_fin_two] at this; exact this
  -- Choose `b` as the canonical residue of `b'` mod `p`; then `p ∣ b' - a·b`.
  set b : Fin p := ⟨((b' : ZMod p)).val, ZMod.val_lt _⟩ with hb_def
  have hbval_zmod : ((b.val : ℕ) : ZMod p) = (b' : ZMod p) := by
    show (((b' : ZMod p).val : ℕ) : ZMod p) = (b' : ZMod p)
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hp_dvd_diff : (p : ℤ) ∣ (b' - a * (b.val : ℤ)) := by
    refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ?_
    push_cast
    rw [ha_mod_p, hbval_zmod]
    ring
  obtain ⟨B, hB_eq⟩ := hp_dvd_diff
  have hBp_int : B * (p : ℤ) = b' - a * (b.val : ℤ) := by linarith
  have hM_det : (!![a, B; (p : ℤ) * c, d - c * (b.val : ℤ)] :
      Matrix (Fin 2) (Fin 2) ℤ).det = 1 :=
    Newform.det_alpha_p_factor_eq_one (p : ℤ) a b' c d B (b.val : ℤ) hBp_int h_det_γ
  refine ⟨⟨_, hM_det⟩, b, ?_, ?_⟩
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((a : ℤ) : ZMod N) = 1
      exact_mod_cast ha_mod_N
    · show ((d - c * (b.val : ℤ) : ℤ) : ZMod N) = 1
      push_cast; rw [hd_mod_N, hc_mod_N]; ring
    · show (((p : ℤ) * c : ℤ) : ZMod N) = 0
      push_cast; rw [hc_mod_N]; ring
  · -- Integer matrix identity: η-expand `γ.val`, then the explicit factorization.
    show (!![(1 : ℤ), 0; 0, (p : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) * γ.val =
        !![a, B; (p : ℤ) * c, d - c * (b.val : ℤ)] *
          !![(1 : ℤ), (b.val : ℤ); 0, (p : ℤ)]
    rw [Matrix.eta_fin_two γ.val, ← ha_def, ← hb'_def, ← hc_def, ← hd_def]
    exact Newform.alpha_p_mul_eq_M_mul_T_p_upper_int (p : ℤ) a b' c d B (b.val : ℤ) hBp_int

/-- **T186 per-γ Hecke double-coset decomposition at level Γ₁(N) for bad primes
(DS Lemma 5.5.2(a) variant).**

For a prime `p` with `p ∣ N` and any `γ ∈ Γ₁(N)`, there exist `γ' ∈ Γ₁(N)`
and `b ∈ Fin p` such that the matrix product `α_p · γ` factors as `γ' · β_b`
in `GL(2, ℝ)`, where `α_p := T_p_upper p hp.pos 0` and
`β_b := T_p_upper p hp.pos b.val`.

**Construction.** Write `γ.val = !![a, b'; c, d]` with `a ≡ d ≡ 1 (mod N)`,
`c ≡ 0 (mod N)`, `ad - b'c = 1`. Choose `b ∈ Fin p` as the canonical residue
of `b'` modulo `p` (`b := (b' : ZMod p).val`). Since `p ∣ N` forces
`a ≡ 1 (mod p)`, we have `a · b ≡ b' (mod p)`, so `B := (b' - a · b) / p ∈ ℤ`.
Define
```
γ' := !![a, B; p · c, d - c · b]   ∈ M₂(ℤ)
```
with determinant `a (d - c b) - B (p c) = ad - b' c = 1`, hence in `SL(2, ℤ)`.

**Γ₁(N) membership of γ'.**
* `(0, 0)`: `a ≡ 1 (mod N)` directly.
* `(1, 0)`: `p · c ≡ 0 (mod N)` since `c ≡ 0 (mod N)`.
* `(1, 1)`: `d - c · b ≡ 1 - 0 = 1 (mod N)` since `c ≡ 0 (mod N)`.

**Matrix-equality verification.** Direct entry-by-entry check of
`!![1, 0; 0, p] · !![a, b'; c, d] = !![a, B; p c, d - c b] · !![1, b; 0, p]`:
* `(0, 0)`: `a = a`.
* `(0, 1)`: `b' = a b + B p` (using `B p = b' - a b`).
* `(1, 0)`: `p c = p c`.
* `(1, 1)`: `p d = (p c) b + (d - c b) p` (after simplification). -/
theorem Newform.alpha_p_mul_Gamma1_eq_Gamma1_mul_T_p_upper_b
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    ∃ (γ' : SL(2, ℤ)) (b : Fin p), γ' ∈ Gamma1 N ∧
      (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ) *
          (mapGL ℝ γ : GL (Fin 2) ℝ) =
        (mapGL ℝ γ' : GL (Fin 2) ℝ) *
          (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) := by
  obtain ⟨γ', b, hγ'_mem, h_int⟩ :=
    Newform.exists_Gamma1_mul_T_p_upper_int hp hpN γ hγ
  exact ⟨γ', b, hγ'_mem,
    Newform.glMap_T_p_upper_zero_mul_mapGL_eq_of_int hp.pos γ γ' b.val h_int⟩

/-- **Bad-prime upper coset rep as `α_p` times a unipotent shear (T186 helper).**

`β_b = α_p · mapGL ℝ (shiftSL b)`, i.e.
`glMap (T_p_upper p hp b) = glMap (T_p_upper p hp 0) · mapGL ℝ (shiftSL b)`. Used
for the reverse inclusion of the double-coset decomposition, embedding each
`β_b`-left-coset into `Γ₁(N) · α_p · Γ₁(N)` via `shiftSL b ∈ Γ₁(N)`. -/
private lemma Newform.glMap_T_p_upper_eq_glMap_zero_mul_shiftSL
    {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ) =
      (glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        (mapGL ℝ (shiftSL (b : ℤ)) : GL (Fin 2) ℝ) := by
  apply Units.ext
  ext i j
  show ((T_p_upper p hp b : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ)) i j =
      ((((T_p_upper p hp 0 : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ)) *
        ((shiftSL (b : ℤ) : SL(2, ℤ)).val.map (algebraMap ℤ ℝ))) i j)
  simp only [T_p_upper_coe, shiftSL, Matrix.map_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply,
    Matrix.SpecialLinearGroup.coe_mk]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

open scoped Pointwise in
/-- **T186 Γ₁(N) double-coset decomposition for the bad-prime upper family.**

The double coset `Γ₁(N) · α_p · Γ₁(N) ⊆ GL(2, ℝ)` (where
`α_p := glMap (T_p_upper p hp.pos 0)`) decomposes as the union over `b : Fin p`
of the left cosets `Γ₁(N) · β_b`, where `β_b := glMap (T_p_upper p hp.pos b.val)`.

**Forward.** Use `Newform.alpha_p_mul_Gamma1_eq_Gamma1_mul_T_p_upper_b` to push
the right-Γ₁(N) witness through `α_p`.

**Reverse.** Use the unipotent `shiftSL (b.val : ℤ) ∈ Γ₁(N)` and the matrix
identity `α_p · mapGL ℝ (shiftSL b.val) = β_b` to embed each `β_b` into
`Γ₁(N) · α_p · Γ₁(N)`. Combined with
`Newform.T_p_upper_left_cosets_pairwiseDisjoint_Gamma1`, this gives a partition
of the double coset into `p` disjoint left `Γ₁(N)`-cosets. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_eq_iUnion_T_p_upper_left_cosets
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) =
    (⋃ b : Fin p,
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) := by
  ext x
  constructor
  · -- Forward: x ∈ Γ * {α_p} * Γ ⟹ x ∈ ⋃ b, Γ * {β_b}.
    rintro ⟨y, hy, g2, hg2, rfl⟩
    obtain ⟨g1, hg1, α', hα', rfl⟩ := hy
    rw [Set.mem_singleton_iff] at hα'
    subst hα'
    obtain ⟨γ2_int, hγ2_int, rfl⟩ := Subgroup.mem_map.mp hg2
    obtain ⟨γ2', b, hγ2'_mem, h_eq⟩ :=
      Newform.alpha_p_mul_Gamma1_eq_Gamma1_mul_T_p_upper_b hp hpN γ2_int hγ2_int
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    refine ⟨g1 * (mapGL ℝ γ2' : GL (Fin 2) ℝ), ?_,
      (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ), rfl, ?_⟩
    · exact Subgroup.mul_mem _ hg1
        (Subgroup.mem_map.mpr ⟨γ2', hγ2'_mem, rfl⟩)
    · -- Goal (post-beta): (g1 * mapGL ℝ γ2') * β_b = (g1 * α_p) * mapGL ℝ γ2_int.
      -- Set.image2 wraps the multiplications as `(fun x1 x2 => x1 * x2)` which
      -- blocks `rw [mul_assoc]` pattern matching; expose the literal `*` via `show`.
      show (g1 * (mapGL ℝ γ2' : GL (Fin 2) ℝ)) *
          (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) =
        (g1 * (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) *
          (mapGL ℝ γ2_int : GL (Fin 2) ℝ)
      rw [mul_assoc, ← h_eq, ← mul_assoc]
  · -- Reverse: x ∈ ⋃ b, Γ * {β_b} ⟹ x ∈ Γ * {α_p} * Γ.
    intro hx
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
    obtain ⟨g, hg, β', hβ', rfl⟩ := hb
    rw [Set.mem_singleton_iff] at hβ'
    subst hβ'
    -- Construct membership directly without pre-rewriting the goal
    -- (a `rw [h_shift_unfold]` here would target the singleton's `α_p` rather
    -- than the LHS's `β_b`, since the LHS multiplication is hidden behind
    -- a `Set.image2` lambda).
    refine ⟨g * (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ), ?_,
      (mapGL ℝ (shiftSL (b.val : ℤ)) : GL (Fin 2) ℝ), ?_, ?_⟩
    · exact ⟨g, hg, glMap (T_p_upper p hp.pos 0), rfl, rfl⟩
    · exact Subgroup.mem_map.mpr ⟨shiftSL (b.val : ℤ), shiftSL_mem_Gamma1 N _, rfl⟩
    · -- Goal (post-beta): (g * α_p) * mapGL ℝ shiftSL_b = g * β_b.
      show (g * (glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)) *
          (mapGL ℝ (shiftSL (b.val : ℤ)) : GL (Fin 2) ℝ) =
        g * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)
      rw [mul_assoc, ← Newform.glMap_T_p_upper_eq_glMap_zero_mul_shiftSL hp.pos b.val]

open scoped Pointwise in
/-- **T186 Γ₁(N) double-coset partition for the bad-prime upper family.**

Bundles the set-level decomposition
`Newform.alpha_p_Gamma1_doubleCoset_eq_iUnion_T_p_upper_left_cosets` with the
left-coset pairwise-disjointness
`Newform.T_p_upper_left_cosets_pairwiseDisjoint_Gamma1`, packaging the
double coset `Γ₁(N) · α_p · Γ₁(N)` as a disjoint union of `p` left
`Γ₁(N)`-cosets indexed by `Fin p`. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) =
    (⋃ b : Fin p,
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) ∧
    (Set.univ : Set (Fin p)).PairwiseDisjoint
      (fun b => (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} :
          Set (GL (Fin 2) ℝ))) :=
  ⟨Newform.alpha_p_Gamma1_doubleCoset_eq_iUnion_T_p_upper_left_cosets N (p := p) hp hpN,
    Newform.T_p_upper_left_cosets_pairwiseDisjoint_Gamma1 N (p := p) hp.pos⟩

open scoped Pointwise in
/-- **T185 selector: existence and uniqueness of the `b`-index of a
double-coset element (T186 partition consumer).**

Combines `Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets`
in two ways:
* The equality `Γ₁(N) · α_p · Γ₁(N) = ⋃ b, Γ₁(N) · β_b` gives existence (any
  element of the double coset lies in some `Γ₁(N)`-left-coset of `β_b`).
* The pairwise-disjointness of those left cosets gives uniqueness (no element
  lies in two different `Γ₁(N) · β_b`-cosets).

This is the combinatorial selector input for the BSum proof: each element of
the bad-prime double coset selects a unique `b ∈ Fin p`. -/
theorem Newform.existsUnique_T_p_upper_left_coset_index_of_mem_alpha_p_doubleCoset
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    {x : GL (Fin 2) ℝ}
    (hx : x ∈
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)))) :
    ∃! b : Fin p,
      x ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) := by
  have hpart := Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets
    N (p := p) hp hpN
  rw [hpart.1] at hx
  obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hx
  refine ⟨b, hb, ?_⟩
  intro c hc
  by_contra hne
  -- hne : ¬ (c = b). Recover `b ≠ c` for the disjointness.
  have hbc : b ≠ c := fun h => hne h.symm
  exact Set.disjoint_left.mp
    (hpart.2 (Set.mem_univ b) (Set.mem_univ c) hbc) hb hc

open scoped Pointwise in
/-- **T185 left-factor selector: existence and uniqueness of the
`b`-index together with a `Γ₁(N)`-left-factor witness.**

Promotes
`Newform.existsUnique_T_p_upper_left_coset_index_of_mem_alpha_p_doubleCoset`
from a coset-membership statement to an explicit left-factorization
`x = γ · β_b` with `γ ∈ Γ₁(N).map (mapGL ℝ)` and `b : Fin p` uniquely
determined. The witness `γ` exists by unfolding the `Set.mul`-membership
witness for `x ∈ Γ₁(N) · {β_b}`; uniqueness of `b` is inherited from the
underlying selector. -/
theorem Newform.existsUnique_T_p_upper_left_factor_of_mem_alpha_p_doubleCoset
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    {x : GL (Fin 2) ℝ}
    (hx : x ∈
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)))) :
    ∃! b : Fin p,
      ∃ γ : GL (Fin 2) ℝ,
        γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) ∧
          γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) = x := by
  obtain ⟨b, hb, huniq⟩ :=
    Newform.existsUnique_T_p_upper_left_coset_index_of_mem_alpha_p_doubleCoset
      N (p := p) hp hpN hx
  refine ⟨b, ?_, ?_⟩
  · -- Existence: unpack `hb : x ∈ Γ * {β_b}` to get `γ ∈ Γ` with `γ * β_b = x`.
    obtain ⟨γ, hγ, y, hy, hmul⟩ := hb
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨γ, hγ, hmul⟩
  · -- Uniqueness: convert any factor witness for `c` back to `x ∈ Γ * {β_c}`,
    -- then apply `huniq`.
    intro c hc
    obtain ⟨γ', hγ', hmul'⟩ := hc
    apply huniq
    exact ⟨γ', hγ', glMap (T_p_upper p hp.pos c.val), rfl, hmul'⟩

open scoped Pointwise in
/-- **T185 membership characterization (non-unique iff form).**

Plain biconditional `x ∈ Γ₁(N)·α_p·Γ₁(N) ↔ ∃ b ∃ γ ∈ Γ₁(N), γ · β_b = x`.

Forward direction strips uniqueness from
`Newform.existsUnique_T_p_upper_left_factor_of_mem_alpha_p_doubleCoset`.
Reverse direction repackages a `(b, γ)` factorization into the partition's
left-coset union via
`Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets.1`. -/
theorem Newform.mem_alpha_p_Gamma1_doubleCoset_iff_exists_T_p_upper_left_factor
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    {x : GL (Fin 2) ℝ} :
    x ∈
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) ↔
      ∃ b : Fin p,
        ∃ γ : GL (Fin 2) ℝ,
          γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) ∧
            γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) = x := by
  refine ⟨?_, ?_⟩
  · -- Forward: drop uniqueness from the factor theorem.
    intro hx
    obtain ⟨b, hb, _⟩ :=
      Newform.existsUnique_T_p_upper_left_factor_of_mem_alpha_p_doubleCoset
        N (p := p) hp hpN hx
    exact ⟨b, hb⟩
  · -- Reverse: repackage via the partition equality.
    rintro ⟨b, γ, hγ, hmul⟩
    have hpart := Newform.alpha_p_Gamma1_doubleCoset_partition_T_p_upper_left_cosets
      N (p := p) hp hpN
    rw [hpart.1]
    exact Set.mem_iUnion.mpr
      ⟨b, ⟨γ, hγ, glMap (T_p_upper p hp.pos b.val), rfl, hmul⟩⟩

open scoped Pointwise in
/-- **T185 tile membership: `Γ₁(N)·α_p·Γ₁(N) • D` characterized by an
explicit upper-family left-factor `Γ₁(N)`-translate.**

Lifts `Newform.mem_alpha_p_Gamma1_doubleCoset_iff_exists_T_p_upper_left_factor`
from `GL(2, ℝ)` to its action on `Set UpperHalfPlane`. The resulting
biconditional is the per-tile shape required for the BSum / DS aggregate
tile transport: every `z` in the double-coset-translated tile equals
`(γ · β_b) • w` for some `b : Fin p`, `γ ∈ Γ₁(N)`, `w ∈ D`. -/
theorem Newform.mem_alpha_p_Gamma1_doubleCoset_smul_set_iff_exists_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) {z : UpperHalfPlane} :
    z ∈
      (((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D) ↔
      ∃ b : Fin p,
        ∃ γ : GL (Fin 2) ℝ,
          γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) ∧
            ∃ w ∈ D,
              (γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) • w = z := by
  refine ⟨?_, ?_⟩
  · -- Forward: unpack `z ∈ S • D`, apply mem-iff to extract `(b, γ)` factor.
    rintro ⟨x, hx, w, hw, hsmul⟩
    rw [Newform.mem_alpha_p_Gamma1_doubleCoset_iff_exists_T_p_upper_left_factor
      N (p := p) hp hpN] at hx
    obtain ⟨b, γ, hγ, hmul⟩ := hx
    subst hmul
    exact ⟨b, γ, hγ, w, hw, hsmul⟩
  · -- Reverse: use mem-iff.mpr on the `γ * β_b` element, then pack `Set.smul`.
    rintro ⟨b, γ, hγ, w, hw, hsmul⟩
    refine ⟨γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ), ?_, w, hw, hsmul⟩
    rw [Newform.mem_alpha_p_Gamma1_doubleCoset_iff_exists_T_p_upper_left_factor
      N (p := p) hp hpN]
    exact ⟨b, γ, hγ, rfl⟩

open scoped Pointwise in
/-- **T185 tile-set equality: nested `iUnion` form of the
double-coset-translated tile.**

Set-level packaging of
`Newform.mem_alpha_p_Gamma1_doubleCoset_smul_set_iff_exists_T_p_upper_left_factor_smul`
as the equality
```
(Γ₁(N) · α_p · Γ₁(N)) • D = ⋃ b ⋃ γ ⋃ (_ : γ ∈ Γ₁(N)), (γ · β_b) • D.
```
This is the cleaner form for aggregate tile/integral transport (each
right-hand-side tile `(γ · β_b) • D` is a single `Γ₁(N)`-translate of the
upper-family `β_b • D`). -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D =
      Set.iUnion (fun b : Fin p =>
        Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
            γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
              Set (GL (Fin 2) ℝ))} =>
          (((γ : GL (Fin 2) ℝ) *
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) • D))) := by
  ext z
  rw [Newform.mem_alpha_p_Gamma1_doubleCoset_smul_set_iff_exists_T_p_upper_left_factor_smul
    N (p := p) hp hpN D]
  simp only [Set.mem_iUnion, Set.mem_smul_set]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, γ, hγ, w, hw, hsmul⟩
    exact ⟨b, ⟨γ, hγ⟩, w, hw, hsmul⟩
  · rintro ⟨b, ⟨γ, hγ⟩, w, hw, hsmul⟩
    exact ⟨b, γ, hγ, w, hw, hsmul⟩

open scoped Pointwise in
/-- **T185 q-tile specialization of the bad-prime double-coset tile equality.** -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_qOut_inv_fd_eq_iUnion_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
        ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)) =
      Set.iUnion (fun b : Fin p =>
        Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
            γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
              Set (GL (Fin 2) ℝ))} =>
          (((γ : GL (Fin 2) ℝ) *
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))) := by
  simpa using
    Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_T_p_upper_left_factor_smul
      N (p := p) hp hpN ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))

open scoped Pointwise in
/-- **T185 q-aggregate tile-set equality for the bad-prime double coset.** -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_iUnion_qOut_inv_fd_eq_iUnion_q_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
      ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))) =
      Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
        Set.iUnion (fun b : Fin p =>
          Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
              γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
                Set (GL (Fin 2) ℝ))} =>
            (((γ : GL (Fin 2) ℝ) *
              (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
                ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))))) := by
  refine Set.iUnion_congr fun q => ?_
  exact Newform.alpha_p_Gamma1_doubleCoset_smul_qOut_inv_fd_eq_iUnion_T_p_upper_left_factor_smul
    N (p := p) hp hpN q

open scoped Pointwise in
/-- **T185 whole-q-domain tile-set equality for the bad-prime double coset.** -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_iUnion_q_T_p_upper_left_factor_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
        (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))) =
      Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
        Set.iUnion (fun b : Fin p =>
          Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
              γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
                Set (GL (Fin 2) ℝ))} =>
            (((γ : GL (Fin 2) ℝ) *
              (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) •
                ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))))) := by
  rw [Set.smul_iUnion]
  exact Newform.alpha_p_Gamma1_doubleCoset_smul_iUnion_qOut_inv_fd_eq_iUnion_q_T_p_upper_left_factor_smul
    N (p := p) hp hpN

open scoped Pointwise in
/-- **T185 Γ₁-action regrouping for one bad-prime upper representative.** -/
theorem Newform.iUnion_Gamma1_T_p_upper_left_factor_smul_eq_Gamma1_smul_T_p_upper_left_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (b : Fin p)
    (D : Set UpperHalfPlane) :
    Set.iUnion (fun γ : {γ : GL (Fin 2) ℝ //
        γ ∈ (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ))} =>
      (((γ : GL (Fin 2) ℝ) *
        (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) • D)) =
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
        Set (GL (Fin 2) ℝ)) •
        ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • D) := by
  ext z
  simp only [Set.mem_iUnion, Set.mem_smul_set]
  constructor
  · rintro ⟨γ, w, hw, hzw⟩
    refine ⟨(γ : GL (Fin 2) ℝ), γ.property,
      (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • w, ?_, ?_⟩
    · exact ⟨w, hw, rfl⟩
    · simpa [mul_smul] using hzw
  · rintro ⟨γ, hγ, y, hy, hzy⟩
    rcases hy with ⟨w, hw, hyw⟩
    refine ⟨⟨γ, hγ⟩, w, hw, ?_⟩
    -- `rcases`/`simp` left `hyw` and `hzy` as beta-redexes; reduce to literal `•`.
    have hyw' : (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • w = y := hyw
    have hzy' : γ • y = z := hzy
    calc
      ((γ * (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ)) : GL (Fin 2) ℝ) • w =
          γ • ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • w) := by
            rw [mul_smul]
      _ = γ • y := by rw [hyw']
      _ = z := hzy'

open scoped Pointwise in
/-- **T185 cleaner Γ₁-action form of the bad-prime double-coset tile equality.** -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_Gamma1_smul_T_p_upper_left_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D =
      Set.iUnion (fun b : Fin p =>
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
          Set (GL (Fin 2) ℝ)) •
          ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • D)) := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_T_p_upper_left_factor_smul
    N (p := p) hp hpN D]
  refine Set.iUnion_congr fun b => ?_
  exact Newform.iUnion_Gamma1_T_p_upper_left_factor_smul_eq_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp b D

open scoped Pointwise in
/-- **T185 whole-q-domain Γ₁-action form of the bad-prime double-coset tile equality.** -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_iUnion_q_Gamma1_smul_T_p_upper_left_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
        (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))) =
      Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
        Set.iUnion (fun b : Fin p =>
          (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) :
            Set (GL (Fin 2) ℝ)) •
            ((glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))) := by
  rw [Set.smul_iUnion]
  refine Set.iUnion_congr fun q => ?_
  exact Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp hpN ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))

open scoped Pointwise in
/-- **T190 set-action regrouping: pull `Γ₁(N)` out of the `b`-iUnion in the
double-coset tile equality.**

Refines
`Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_Gamma1_smul_T_p_upper_left_smul`
by extracting the `Γ₁(N)`-action factor outside the `Fin p` iUnion. The
resulting `Γ₁(N) • (⋃_b β_b • D)` shape is the precise form of the LHS that
downstream measure/integral consumers naturally match: a `Γ₁(N)`-invariant
integrand pulls inside, leaving `⋃_b β_b • D` as the single Γ₁(N)-orbit
representative tile. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_Gamma1_smul_iUnion_T_p_upper_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D =
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
        Set.iUnion (fun b : Fin p =>
          (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • D) := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_iUnion_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp hpN D, Set.smul_iUnion]

open scoped Pointwise in
/-- **T190 set-action regrouping (whole-q form): pull `Γ₁(N)` out of the
`(q, b)`-iUnion in the double-coset tile equality on the union of all
q-tiles.**

Whole-q-domain analogue of
`Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_Gamma1_smul_iUnion_T_p_upper_smul`.
The LHS is the action of the bad-prime double coset on the SL(2,ℤ)-fundamental
cover `⋃_q q.out⁻¹ • fd` of `ℍ` (modulo `Γ₁(N)`). The RHS expresses this as a
single `Γ₁(N)`-orbit of the per-`(q, b)` upper-coset-shifted tile family,
which is the natural shape for downstream measure/integral consumers. -/
theorem Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
        ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
        (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
          ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))) =
      (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
        Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
          Set.iUnion (fun b : Fin p =>
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane)))) := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_iUnion_q_Gamma1_smul_T_p_upper_left_smul
    N (p := p) hp hpN, Set.smul_iUnion]
  refine Set.iUnion_congr fun q => ?_
  rw [Set.smul_iUnion]

open UpperHalfPlane MeasureTheory in
/-- **T194 set-integral consumer of T190 per-tile regrouping.**

Lifts the T190 set-equality
`Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_Gamma1_smul_iUnion_T_p_upper_smul`
from sets in `ℍ` to the `setIntegral` context: for any integrable
`h : ℍ → ℂ`, the integral of `h` over `(Γ₁(N) · α_p · Γ₁(N)) • D` rewrites
as the integral over `Γ₁(N) • ⋃_b β_b · D`. This is the natural domain
rewrite at the integral level, applicable to any integrand `h` (in
particular the Petersson integrand `petersson k f g`). -/
theorem Newform.setIntegral_alpha_p_doubleCoset_smul_set_eq_setIntegral_Gamma1_smul_iUnion_T_p_upper_smul
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (D : Set UpperHalfPlane) (h : UpperHalfPlane → ℂ) :
    ∫ τ in
      (((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
            ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
          (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) • D),
        h τ ∂μ_hyp =
      ∫ τ in
        ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
          Set.iUnion (fun b : Fin p =>
            (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) • D)),
        h τ ∂μ_hyp := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_set_eq_Gamma1_smul_iUnion_T_p_upper_smul
    N (p := p) hp hpN D]

open UpperHalfPlane MeasureTheory in
/-- **T194 set-integral consumer of T190 whole-q regrouping.**

Whole-q-domain analogue of
`Newform.setIntegral_alpha_p_doubleCoset_smul_set_eq_setIntegral_Gamma1_smul_iUnion_T_p_upper_smul`.
Lifts the T190 whole-q set-equality
`Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_Gamma1_smul_iUnion_q_b_T_p_upper_smul`
from sets in `ℍ` to the `setIntegral` context. The bad-prime aggregate
Petersson integral over `(Γ₁(N) · α_p · Γ₁(N)) • ⋃_q q.out⁻¹ • fd` (the
double-coset image of the SL(2,ℤ)-fundamental cover) rewrites as the
integral over the clean iUnion form
`Γ₁(N) • ⋃_q ⋃_b β_b · q.out⁻¹ • fd`. -/
theorem Newform.setIntegral_alpha_p_doubleCoset_smul_whole_qOut_inv_fd_eq_setIntegral_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h : UpperHalfPlane → ℂ) :
    ∫ τ in
      (((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
            ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
          (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
            (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
              ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))),
        h τ ∂μ_hyp =
      ∫ τ in
        ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
          Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
            Set.iUnion (fun b : Fin p =>
              (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
                ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))),
        h τ ∂μ_hyp := by
  rw [Newform.alpha_p_Gamma1_doubleCoset_smul_whole_qOut_inv_fd_eq_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    N (p := p) hp hpN]

open UpperHalfPlane MeasureTheory in
/-- **T194 `peterssonInner` consumer of T190 whole-q regrouping.**

Specialization of
`Newform.setIntegral_alpha_p_doubleCoset_smul_whole_qOut_inv_fd_eq_setIntegral_Gamma1_smul_iUnion_q_b_T_p_upper_smul`
to the Petersson integrand `petersson k f g`. Provides the bad-prime
double-coset image rewrite directly at the `peterssonInner` level. -/
theorem Newform.peterssonInner_alpha_p_doubleCoset_smul_whole_qOut_inv_fd_eq_peterssonInner_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    {N : ℕ} [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (k : ℤ) (f g : UpperHalfPlane → ℂ) :
    peterssonInner k
      (((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) *
          ({(glMap (T_p_upper p hp.pos 0) : GL (Fin 2) ℝ)} : Set (GL (Fin 2) ℝ)) *
        (((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ))) •
          (Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
            ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))) f g =
      peterssonInner k
        ((((Gamma1 N).map (mapGL ℝ) : Subgroup (GL (Fin 2) ℝ)) : Set (GL (Fin 2) ℝ)) •
          Set.iUnion (fun q : SL(2, ℤ) ⧸ Gamma1 N =>
            Set.iUnion (fun b : Fin p =>
              (glMap (T_p_upper p hp.pos b.val) : GL (Fin 2) ℝ) •
                ((q.out : SL(2, ℤ))⁻¹ • (fd : Set UpperHalfPlane))))) f g := by
  unfold peterssonInner
  exact Newform.setIntegral_alpha_p_doubleCoset_smul_whole_qOut_inv_fd_eq_setIntegral_Gamma1_smul_iUnion_q_b_T_p_upper_smul
    hp hpN _

/-! ### Per-coset Petersson adjoint at the bad-prime upper coset (T151) -/

/-- **Determinant of `T_p_lower_with_offset` (T151 helper).** -/
lemma Newform.T_p_lower_with_offset_det
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (Newform.T_p_lower_with_offset N hp b).det.val = (p : ℝ) := by
  show ((Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ)
  rw [Newform.T_p_lower_with_offset_coe]
  simp [Matrix.det_fin_two]

/-- **Positive determinant for `T_p_lower_with_offset` (T151 helper).** -/
lemma Newform.T_p_lower_with_offset_det_pos
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    0 < (Newform.T_p_lower_with_offset N hp b).det.val := by
  rw [Newform.T_p_lower_with_offset_det]
  exact_mod_cast hp

open UpperHalfPlane MeasureTheory in
/-- **Per-coset Petersson adjoint identity at the bad-prime upper coset
(T151 main).**

For the bad-prime upper-triangular coset rep `β_b := glMap (T_p_upper p hp b)`
and any `f, g : UpperHalfPlane → ℂ`:
```
peterssonInner k D ((f ∣[k] W_N) ∣[k] β_b) g =
  peterssonInner k (M • W_N • D) f
    ((g ∣[k] peterssonAdj W_N) ∣[k] peterssonAdj M)
```
where `M := T_p_lower_with_offset N hp b`. Proof: combine T150's slash
rewrite `(f ∣[k] W_N) ∣[k] β_b = (f ∣[k] M) ∣[k] W_N` with two applications
of T145's `peterssonInner_slash_adjoint`, first at `α := W_N` (det N > 0)
and then at `α := M` (det p > 0).

This is the per-coset analytic input to the bad-prime Fricke petN-adjoint
proof: each `b ∈ Finset.range p` summand of the Hecke operator
`T_p_divN = Σ_b f ∣[k] β_b` gets converted into a peterssonInner with a
Fricke-shifted domain and a Fricke-conjugated `g`-side. The petN aggregate
then proceeds by Γ₁(N)-coset reindex (separate ticket). -/
lemma Newform.peterssonInner_fricke_T_p_upper_rewrite_adjoint
    (D : Set UpperHalfPlane) (N : ℕ) [NeZero N] {k : ℤ}
    {p : ℕ} (hp : 0 < p) (b : ℕ) (f g : UpperHalfPlane → ℂ) :
    peterssonInner k D
        ((f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) g =
      peterssonInner k
        ((Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) •
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) • D))
        f
        ((g ∣[k] peterssonAdj (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          peterssonAdj (Newform.T_p_lower_with_offset N hp b :
            GL (Fin 2) ℝ)) := by
  rw [Newform.slash_frickeMatrix_T_p_upper_rewrite hp b f]
  rw [peterssonInner_slash_adjoint (k := k) D
      (Newform.frickeMatrix N : GL (Fin 2) ℝ)
      (Newform.frickeMatrix_det_pos N)
      (f ∣[k] (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)) g]
  rw [peterssonInner_slash_adjoint (k := k)
      ((Newform.frickeMatrix N : GL (Fin 2) ℝ) • D)
      (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ)
      (Newform.T_p_lower_with_offset_det_pos N hp b) f
      (g ∣[k] peterssonAdj (Newform.frickeMatrix N : GL (Fin 2) ℝ))]

/-! ### Identification of the right-slot adjoint factors (T152) -/

/-- **Adjugate of `T_p_lower_with_offset` as an explicit `GL (Fin 2) ℝ`
element (T152 helper).**

The 2×2 adjugate of `!![p, 0; -N·b, 1]` is `!![1, 0; N·b, p]`, also with
determinant `p`. This is the matrix shape of `peterssonAdj
(T_p_lower_with_offset N hp b)`; packaging it as a GL element via
`mkOfDetNeZero` lets downstream slash rewrites bypass the
`peterssonAdj` machinery. -/
noncomputable def Newform.T_p_lower_with_offset_adjugate
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (!![(1 : ℝ), 0; ((N : ℝ) * b), (p : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ)
    (by simp [Matrix.det_fin_two]; exact_mod_cast hp.ne')

/-- **Underlying matrix of `T_p_lower_with_offset_adjugate` (T152 helper).** -/
@[simp]
lemma Newform.T_p_lower_with_offset_adjugate_coe
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    ((Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      !![(1 : ℝ), 0; ((N : ℝ) * b), (p : ℝ)] := by
  simp [Newform.T_p_lower_with_offset_adjugate,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- **Determinant of `T_p_lower_with_offset_adjugate` (T152 helper).** -/
lemma Newform.T_p_lower_with_offset_adjugate_det
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    (Newform.T_p_lower_with_offset_adjugate N hp b).det.val = (p : ℝ) := by
  show ((Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det = (p : ℝ)
  rw [Newform.T_p_lower_with_offset_adjugate_coe]
  simp [Matrix.det_fin_two]

/-- **Positive determinant for `T_p_lower_with_offset_adjugate` (T152 helper).** -/
lemma Newform.T_p_lower_with_offset_adjugate_det_pos
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    0 < (Newform.T_p_lower_with_offset_adjugate N hp b).det.val := by
  rw [Newform.T_p_lower_with_offset_adjugate_det]
  exact_mod_cast hp

/-- **`peterssonAdj (T_p_lower_with_offset N hp b) = T_p_lower_with_offset_adjugate
N hp b` as `GL (Fin 2) ℝ` elements (T152 main matrix-level identity).**

The adjugate of `!![p, 0; -N·b, 1]` is `!![1, 0; N·b, p]`, established by
`Matrix.adjugate_fin_two` (the 2×2 adjugate formula) plus a 4-entry case
analysis. -/
lemma Newform.peterssonAdj_T_p_lower_with_offset_eq
    (N : ℕ) {p : ℕ} (hp : 0 < p) (b : ℕ) :
    peterssonAdj (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) =
      Newform.T_p_lower_with_offset_adjugate N hp b := by
  apply Units.ext
  show (peterssonAdj (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      ((Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ)
  rw [peterssonAdj_coe, Newform.T_p_lower_with_offset_coe,
      Newform.T_p_lower_with_offset_adjugate_coe, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **Slash by `peterssonAdj (T_p_lower_with_offset N hp b)` reduces to slash
by the explicit adjugate `T_p_lower_with_offset_adjugate N hp b` (T152 main
slash form).**

Direct corollary of `peterssonAdj_T_p_lower_with_offset_eq` (slash respects
GL equality). Together with T145's `Newform.slash_peterssonAdj_frickeMatrix`
gives the two slash identifications needed for the T151 right-slot rewrite. -/
@[simp]
lemma Newform.slash_peterssonAdj_T_p_lower_with_offset
    {N : ℕ} {k : ℤ} {p : ℕ} (hp : 0 < p) (b : ℕ)
    (g : UpperHalfPlane → ℂ) :
    g ∣[k] peterssonAdj (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) =
      g ∣[k] (Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) := by
  rw [Newform.peterssonAdj_T_p_lower_with_offset_eq]

/-- **Combined T151 right-slot Petersson-adjoint rewrite (T152 main combined).**

The exact T151 right-slot expression
`(g ∣[k] peterssonAdj W_N) ∣[k] peterssonAdj M_{N,p,b}`
collapses to a `(-1)^k`-scaled slash by W_N followed by slash by the explicit
adjugate `M_{N,p,b}^*`:
```
(g ∣[k] peterssonAdj W_N) ∣[k] peterssonAdj M_{N,p,b} =
  (-1)^k • ((g ∣[k] W_N) ∣[k] T_p_lower_with_offset_adjugate N hp b)
```
Proof: `slash_peterssonAdj_frickeMatrix` (T145) gives the `(-1)^k` scalar on
the inner `peterssonAdj W_N` slash; `slash_peterssonAdj_T_p_lower_with_offset`
(T152 above) replaces the outer `peterssonAdj M`-slash by an `M^*`-slash;
then `ModularForm.smul_slash` + `frickeMatrix_*_σ` lift the scalar through
the outer slash without picking up an extra factor. -/
lemma Newform.peterssonInner_fricke_T_p_upper_right_slot_rewrite
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} (hp : 0 < p) (b : ℕ)
    (g : UpperHalfPlane → ℂ) :
    (g ∣[k] peterssonAdj (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        peterssonAdj (Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) =
      ((-1 : ℂ) ^ k) •
        ((g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.T_p_lower_with_offset_adjugate N hp b :
            GL (Fin 2) ℝ)) := by
  rw [Newform.slash_peterssonAdj_frickeMatrix g,
      Newform.slash_peterssonAdj_T_p_lower_with_offset hp b]
  -- Goal: ((-1)^k • (g ∣ W_N)) ∣ adj_M = (-1)^k • ((g ∣ W_N) ∣ adj_M)
  -- Use ModularForm.smul_slash; need σ(adj_M) c = c, i.e., σ adj_M = id (det adj_M > 0).
  rw [ModularForm.smul_slash]
  have hadj_M_pos : 0 <
      (Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ).det.val :=
    Newform.T_p_lower_with_offset_adjugate_det_pos N hp b
  rw [show UpperHalfPlane.σ
        (Newform.T_p_lower_with_offset_adjugate N hp b : GL (Fin 2) ℝ) =
      RingHom.id ℂ from by
    unfold UpperHalfPlane.σ
    rw [if_pos hadj_M_pos]]
  rfl

/-! ### Aggregation to bad-prime Fricke petN adjoint (T153) -/

/-- **`frickeSquareScalar N k` is non-zero (T153 helper).**

`frickeSquareScalar N k = (-1 : ℂ)^k * (N : ℂ)^(k - 2)`. The first factor
is non-zero (the unit `-1`), the second is non-zero because `(N : ℂ) ≠ 0`
from `[NeZero N]`. -/
lemma Newform.frickeSquareScalar_ne_zero (N : ℕ) [NeZero N] (k : ℤ) :
    Newform.frickeSquareScalar N k ≠ 0 := by
  unfold Newform.frickeSquareScalar
  have h_neg_one_ne : ((-1 : ℂ) ^ k) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hN_pow_ne : (N : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ hN_ne
  exact mul_ne_zero h_neg_one_ne hN_pow_ne

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **Per-Γ₁(N)-coset aggregation residual for the bad-prime Fricke petN
adjoint (T153 named residual).**

The exact remaining content of `Newform.HasBadPrimeFrickePetNAdjoint N k p`
after unfolding `petN` to its `q : SL(2, ℤ) ⧸ Γ₁(N)`-summands: for each
`q`, the per-summand equality
```
peterssonInner k fd
    (⇑(heckeT_n_cusp k p f) ∣[k] q.out⁻¹)
    (⇑g ∣[k] q.out⁻¹) =
  peterssonInner k fd
    (⇑f ∣[k] q.out⁻¹)
    (⇑(frickeBadAdjointCandidateNormalized k p g) ∣[k] q.out⁻¹).
```
This is the precise remaining sum/coset equality the T150-T152 per-coset
chain must aggregate over the `b ∈ Finset.range p` Hecke index plus the
shifted-FD reindex for each `q`. -/
def Newform.HasBadPrimeFrickePerCosetAggregateRes
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p] : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N),
    peterssonInner k fd
      (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
      (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    peterssonInner k fd
      (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
      (⇑(Newform.frickeBadAdjointCandidateNormalized k p g) ∣[k]
        (q.out : SL(2, ℤ))⁻¹)

/-- **`Newform.HasBadPrimeFrickePetNAdjoint` from per-coset aggregation
residual (T153 main reduction).**

Direct petN-summation reduction: if every `q : SL(2, ℤ) ⧸ Γ₁(N)`-coset
peterssonInner summand satisfies the per-coset equality
`Newform.HasBadPrimeFrickePerCosetAggregateRes`, then the petN-level Fricke
bad-prime adjoint Prop `HasBadPrimeFrickePetNAdjoint` holds.

Proof: unfold `petN` to its `q`-sum, apply the per-coset hypothesis pointwise
in `q`, repackage. The `Finset.sum_congr` plumbing handles the reassembly. -/
theorem Newform.hasBadPrimeFrickePetNAdjoint_of_perCosetAggregate
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (h_perCoset : Newform.HasBadPrimeFrickePerCosetAggregateRes N k p) :
    Newform.HasBadPrimeFrickePetNAdjoint N k p := by
  intro f g
  show petN (heckeT_n_cusp k p f) g =
    petN f (Newform.frickeBadAdjointCandidateNormalized k p g)
  unfold petN
  exact Finset.sum_congr rfl (fun q _ => h_perCoset f g q)

/-- **The aggregate target Prop: `Newform.hasBadPrimeFrickePetNAdjoint_of_fricke_upper_aggregate`
(T153 named reduction, full-aggregate form).**

States the bad-prime Fricke petN adjoint as the unscaled scaled identity
(via `frickeSquareScalar`-multiplication on both sides) — equivalent to
`HasBadPrimeFrickePetNAdjoint` via `hasBadPrimeFrickePetNAdjoint_iff`
(T149) under `frickeSquareScalar_ne_zero`. Enables the consumer to work
with whichever scalar form is convenient. -/
theorem Newform.hasBadPrimeFrickePetNAdjoint_of_fricke_upper_aggregate
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (_hp : p.Prime) (_hpN : ¬ Nat.Coprime p N)
    (h_aggregate : ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k),
      Newform.frickeSquareScalar N k * petN (heckeT_n_cusp k p f) g =
        petN f (Newform.frickeBadAdjointCandidate k p g)) :
    Newform.HasBadPrimeFrickePetNAdjoint N k p :=
  (Newform.hasBadPrimeFrickePetNAdjoint_iff
    (Newform.frickeSquareScalar_ne_zero N k)).mpr h_aggregate

/-! ### Per-q b-sum exposure of the bad-prime aggregation residual (T154) -/

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **Bad-prime `heckeT_n_cusp k p` LHS-summand expansion to upper b-sum
(T154 helper).**

For prime `p` with `p ∣ N` and `q : SL(2, ℤ) ⧸ Γ₁(N)`, the LHS summand of
T153's `HasBadPrimeFrickePerCosetAggregateRes` rewrites to a peterssonInner
whose first slot is the *finite Hecke b-sum* `∑ b ∈ Finset.range p, (⇑f ∣[k]
β_b)` further slashed by `q.out⁻¹`. This rewrite uses the bad-prime
`heckeT_p_all_not_coprime_apply` and `heckeT_p_ut` definitions; the b-sum
distribution to a sum-of-peterssonInners is left for the consumer (it
requires per-b integrability hypotheses). -/
lemma Newform.peterssonInner_heckeT_n_cusp_at_divN_slash_qOut_inv_eq_bsum
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N) :
    peterssonInner k fd
        (⇑(heckeT_n_cusp k p f) ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
      peterssonInner k fd
        ((∑ b ∈ Finset.range p,
            ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) := by
  have h_unfold : (⇑(heckeT_n_cusp k p f) : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos (⇑f) := by
    show (heckeT_n k p (f.toModularForm') : UpperHalfPlane → ℂ) =
      heckeT_p_ut k p hp.pos (⇑f)
    rw [heckeT_n_prime k hp,
        heckeT_p_all_not_coprime_apply (k := k) hp hpN f.toModularForm']
    rfl
  rw [h_unfold]
  rfl

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **Per-(q, b) bad-prime Fricke aggregation residual (T154 named residual).**

The exact remaining content of `Newform.HasBadPrimeFrickePerCosetAggregateRes
N k p` after the b-sum exposure (above) is per-(q, b) summand equality
between the upper-triangular peterssonInner and the corresponding
expansion of `frickeBadAdjointCandidateNormalized k p g`-slot summand.

States, for each `q : SL(2, ℤ) ⧸ Γ₁(N)` and each `b ∈ Finset.range p`,
the equality between
* the LHS upper-triangular per-(q, b) summand
  `peterssonInner k fd ((⇑f ∣[k] β_b) ∣[k] q.out⁻¹) (⇑g ∣[k] q.out⁻¹)`,
and
* the per-(q, b) component of the RHS, namely
  `peterssonInner k fd (⇑f ∣[k] q.out⁻¹) (((⇑g ∣[k] W_N ∣[k] β_b ∣[k] W_N)
    ∣[k] q.out⁻¹) summand of frickeBadAdjointCandidateNormalized)`,
properly normalized by `(frickeSquareScalar)⁻¹`.

This is the precise per-coset residual that the T151/T152 chain is
intended to discharge through the `peterssonInner_slash_adjoint` machinery
applied at α = β_b · q.out⁻¹, followed by adjugate identification and the
shifted-FD reindex. The full discharge is the substantive content of T155+. -/
def Newform.HasBadPrimeFrickePerCosetBsumShiftedFD
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N),
    peterssonInner k fd
        ((∑ b ∈ Finset.range p,
            ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    peterssonInner k fd
      (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
      (⇑(Newform.frickeBadAdjointCandidateNormalized k p g) ∣[k]
        (q.out : SL(2, ℤ))⁻¹)

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **From T154 b-sum residual to T153 per-coset residual (T154 main reduction).**

Direct one-line composition: T154's b-sum-LHS expansion lemma
(`peterssonInner_heckeT_n_cusp_at_divN_slash_qOut_inv_eq_bsum`) plus the
named residual `HasBadPrimeFrickePerCosetBsumShiftedFD`. -/
theorem Newform.hasBadPrimeFrickePerCosetAggregateRes_of_bsum_shiftedFD
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_bsum_shifted :
      Newform.HasBadPrimeFrickePerCosetBsumShiftedFD N k p hp hpN) :
    Newform.HasBadPrimeFrickePerCosetAggregateRes N k p := by
  intro f g q
  rw [Newform.peterssonInner_heckeT_n_cusp_at_divN_slash_qOut_inv_eq_bsum hp hpN f g q]
  exact h_bsum_shifted f g q

/-! ### Combined T151+T152 + Fricke-square insertion (T155) -/

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **Combined T151+T152: per-(b, D) Fricke bad-prime peterssonInner identity
(T155 main combined lemma).**

Composition of `Newform.peterssonInner_fricke_T_p_upper_rewrite_adjoint` (T151)
and `Newform.peterssonInner_fricke_T_p_upper_right_slot_rewrite` (T152), giving
the full per-coset Petersson identity in scalar-correct form:
```
peterssonInner k D ((f|W_N)|β_b) g =
  peterssonInner k (M_{N,p,b} • W_N • D) f
    ((-1)^k • ((g|W_N)|T_p_lower_with_offset_adjugate N hp b)).
```
-/
lemma Newform.peterssonInner_fricke_T_p_upper_rewrite_adjoint_t152
    (D : Set UpperHalfPlane) (N : ℕ) [NeZero N] {k : ℤ}
    {p : ℕ} (hp : 0 < p) (b : ℕ) (f g : UpperHalfPlane → ℂ) :
    peterssonInner k D
        ((f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (glMap (T_p_upper p hp b) : GL (Fin 2) ℝ)) g =
      peterssonInner k
        ((Newform.T_p_lower_with_offset N hp b : GL (Fin 2) ℝ) •
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) • D))
        f
        (((-1 : ℂ) ^ k) •
          ((g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (Newform.T_p_lower_with_offset_adjugate N hp b :
              GL (Fin 2) ℝ))) := by
  rw [Newform.peterssonInner_fricke_T_p_upper_rewrite_adjoint D N hp b f g]
  rw [Newform.peterssonInner_fricke_T_p_upper_right_slot_rewrite hp b g]

/-- **Fricke-square scalar insertion at the function level (T155 helper).**

T144's `slash_frickeMatrix_frickeMatrix` says `(f|W_N)|W_N = frickeSquareScalar N k • f`.
This lemma gives the *inverse* form needed by T155: `f` rewritten as
`(frickeSquareScalar N k)⁻¹ • ((f|W_N)|W_N)`. Used to insert the W_N · W_N
factor into a function before applying T151+T152 (which expect
`(h|W_N)|β_b`-shaped slashes). -/
lemma Newform.fricke_square_inv_smul
    {N : ℕ} [NeZero N] {k : ℤ} (f : UpperHalfPlane → ℂ) :
    (Newform.frickeSquareScalar N k)⁻¹ •
        ((f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
          (Newform.frickeMatrix N : GL (Fin 2) ℝ)) = f := by
  rw [Newform.slash_frickeMatrix_frickeMatrix, smul_smul]
  rw [show (Newform.frickeSquareScalar N k)⁻¹ * Newform.frickeSquareScalar N k = 1 from
    inv_mul_cancel₀ (Newform.frickeSquareScalar_ne_zero N k)]
  rw [one_smul]

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **Per-q Fricke-squared b-sum residual after T151+T152 application
(T155 named residual).**

The exact remaining content of `Newform.HasBadPrimeFrickePerCosetBsumShiftedFD`
after applying:
1. **Fricke-square insertion**: rewrite `f := (frickeSquareScalar)⁻¹ •
   ((f|W_N)|W_N)` (T155 `fricke_square_inv_smul`).
2. **Distribute the b-sum** over `peterssonInner` (T154-style; consumer's
   responsibility).
3. **Per-b combined T151+T152**: each summand `peterssonInner k fd
   (((f|W_N)|W_N)|β_b)|q.out⁻¹) (g|q.out⁻¹)` rewrites via the combined
   identity (T155 `peterssonInner_fricke_T_p_upper_rewrite_adjoint_t152`)
   plus a per-q domain shift through `q.out⁻¹` to reduce to
   `peterssonInner k (M_b • W_N • q.out⁻¹ • fd) (f|W_N)
     ((-1)^k • ((g|W_N)|adj_M_b))`.

The residual states the resulting per-q b-sum equals the corresponding b-sum
of `frickeBadAdjointCandidateNormalized`-evaluated peterssonInner summands.
The substantive remaining step is the **shifted-FD reindex** transporting
`M_b • W_N • q.out⁻¹ • fd` integrals back to `fd` integrals (the
Atkin-Lehner / Γ₀(N) coset reindex), plus the Fricke-square scalar matching. -/
def Newform.HasBadPrimeFrickePerCosetT152ShiftedFD
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N),
    ∑ b ∈ Finset.range p,
      peterssonInner k
        ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
          ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
            ((mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
              (fd : Set UpperHalfPlane))))
        (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
        (((-1 : ℂ) ^ k) •
          ((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
            (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
              GL (Fin 2) ℝ))) =
    Newform.frickeSquareScalar N k *
      peterssonInner k fd
        (⇑f ∣[k] (q.out : SL(2, ℤ))⁻¹)
        (⇑(Newform.frickeBadAdjointCandidateNormalized k p g) ∣[k]
          (q.out : SL(2, ℤ))⁻¹)

/-! ### T156 bridge: T155 shifted residual ⟹ T154 b-sum residual -/

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T156 sub-residual: T154 LHS rewrites as scalar-times Σ_b through Fricke
insertion + b-sum distribution + per-b T145 + combined T151+T152.**

The substantive bridge content of T156. Captures the four mechanical steps
that transport T154's LHS expression
`peterssonInner k fd ((Σ_b ⇑f ∣[k] β_b) ∣[k] q.out⁻¹) (⇑g ∣[k] q.out⁻¹)`
to T155's LHS form
`(frickeSquareScalar)⁻¹ • Σ_b peterssonInner k (M_b • W_N • q.out⁻¹ • fd)
   (⇑f ∣[k] W_N) ((-1)^k • ((⇑g ∣[k] W_N) ∣[k] adj_M_b))`:

1. **Fricke-square insertion** via `Newform.fricke_square_inv_smul`:
   `⇑f = (frickeSquareScalar)⁻¹ • ((⇑f ∣[k] W_N) ∣[k] W_N)`.
2. **Distribute the b-sum** over `peterssonInner` (per-b integrability via
   `peterssonInner_sum_left`).
3. **Per-b application of `peterssonInner_slash_adjoint`** at α = q.out⁻¹
   (det 1 > 0), absorbing `q.out⁻¹` into the domain on the left.
4. **Per-b combined T151+T152** via
   `peterssonInner_fricke_T_p_upper_rewrite_adjoint_t152`, producing the
   M_b • W_N • domain shift and the `(-1)^k • adj_M_b` right-slot factor.

Isolates the technical b-sum/integrability/per-b transformation work, which
is mechanical but requires per-b CuspForm integrability bookkeeping. -/
def Newform.HasBadPrimeFrickePerCosetSumTransport
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (hp : p.Prime) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (q : SL(2, ℤ) ⧸ Gamma1 N),
    peterssonInner k fd
        ((∑ b ∈ Finset.range p,
            ⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
            (q.out : SL(2, ℤ))⁻¹)
        (⇑g ∣[k] (q.out : SL(2, ℤ))⁻¹) =
    (Newform.frickeSquareScalar N k)⁻¹ *
      ∑ b ∈ Finset.range p,
        peterssonInner k
          ((Newform.T_p_lower_with_offset N hp.pos b : GL (Fin 2) ℝ) •
            ((Newform.frickeMatrix N : GL (Fin 2) ℝ) •
              ((mapGL ℝ (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ) •
                (fd : Set UpperHalfPlane))))
          (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ))
          (((-1 : ℂ) ^ k) •
            ((⇑g ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
              (Newform.T_p_lower_with_offset_adjugate N hp.pos b :
                GL (Fin 2) ℝ)))

/-- **Positive determinant of an `SL(2, ℤ)` element under `mapGL ℝ` (T157 helper).**

`0 < (mapGL ℝ σ).det.val` for any `σ : SL(2, ℤ)`: the underlying real matrix is
the `algebraMap ℤ ℝ`-image of `σ.val`, whose determinant is `1` (as `σ ∈ SL`).
Supplies the positive-determinant hypothesis of `peterssonInner_slash_adjoint`. -/
private lemma Newform.mapGL_SL_det_val_pos (σ : SL(2, ℤ)) :
    (0 : ℝ) < ((mapGL ℝ σ : GL (Fin 2) ℝ)).det.val := by
  show 0 < (((mapGL ℝ σ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det
  rw [show ((mapGL ℝ σ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((Int.castRingHom ℝ).mapMatrix (σ.val)) from by rw [mapGL_coe_matrix]; rfl]
  rw [← RingHom.map_det, σ.property]
  norm_num

/-- **Realness of `frickeSquareScalar⁻¹` (T157 helper).**

`conj ((frickeSquareScalar N k)⁻¹) = (frickeSquareScalar N k)⁻¹`: the Fricke-square
scalar `(-1)^k · N^(-k)` is real, so it is fixed by complex conjugation. Used to
drop the outer `conj` after pulling the scalar out of `peterssonInner`'s left slot. -/
private lemma Newform.conj_frickeSquareScalar_inv (N : ℕ) [NeZero N] (k : ℤ) :
    (starRingEnd ℂ) ((Newform.frickeSquareScalar N k)⁻¹) =
      (Newform.frickeSquareScalar N k)⁻¹ := by
  rw [map_inv₀, Newform.frickeSquareScalar, map_mul, map_zpow₀, map_zpow₀,
    Complex.conj_natCast]
  congr 1
  norm_num

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T157: bad-prime SumTransport bridge residual proven directly.**

Closes the T156 sub-residual `HasBadPrimeFrickePerCosetSumTransport`
without external hypotheses. Bridges T154's b-sum LHS to T155's shifted
peterssonInner b-sum.

**Proof outline (per fixed `f, g, q`).**
1. Distribute the outer `q.out⁻¹`-slash over the b-sum
   (`SlashAction.sum_slash`).
2. Distribute `peterssonInner` over the b-sum (`peterssonInner_sum_left`);
   per-b integrability via `integrableOn_petersson_cuspform_mixed_slash_on_fd`.
3. Pull `(frickeSquareScalar)⁻¹` out of the RHS sum (`Finset.mul_sum`).
4. Reduce to per-b equality via `Finset.sum_congr`.
5. **Per-b** apply `peterssonInner_slash_adjoint` (T145) at
   `α := mapGL ℝ q.out⁻¹` (det 1 > 0) to absorb `q.out⁻¹` into the
   domain; simplify the right slot via `peterssonAdj_mapGL_SL_eq_inv`
   + `SlashAction.slash_mul` + `mul_inv_cancel` + `slash_one` to recover `⇑g`.
6. Insert the Fricke-square via `Newform.fricke_square_inv_smul`,
   rewriting `⇑f` as `(frickeSquareScalar)⁻¹ • ((⇑f|W_N)|W_N)`.
7. Pull the scalar through `β_b`-slash (`smul_slash_pos_det`,
   `T_p_upper_det_pos`).
8. Pull the scalar out of `peterssonInner`'s left slot
   (`peterssonInner_conj_smul_left`); use realness of
   `frickeSquareScalar` to drop the outer `conj`.
9. Apply combined T151+T152 via
   `peterssonInner_fricke_T_p_upper_rewrite_adjoint_t152`. -/
theorem Newform.hasBadPrimeFrickePerCosetSumTransport
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasBadPrimeFrickePerCosetSumTransport N k p hp hpN := by
  intro f g q
  -- Steps 1+2: distribute outer slash + `peterssonInner` over the b-sum.
  have h_int : ∀ b ∈ Finset.range p,
      IntegrableOn (fun τ => UpperHalfPlane.petersson k
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹))
        ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
          ((q.out : SL(2, ℤ))⁻¹)) τ) (fd : Set UpperHalfPlane) μ_hyp :=
    fun b _ => integrableOn_petersson_cuspform_mixed_slash_on_fd g f
      (T_p_upper p hp.pos b) ((q.out : SL(2, ℤ))⁻¹)
  rw [SlashAction.sum_slash, peterssonInner_sum_left _ _ _ _ h_int]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have h_det_pos := Newform.mapGL_SL_det_val_pos ((q.out : SL(2, ℤ))⁻¹)
  -- Step 5: T145 absorbs `q.out⁻¹` into the domain; recover ⇑g in the right slot.
  rw [show ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        ((q.out : SL(2, ℤ))⁻¹) : UpperHalfPlane → ℂ) =
      ((⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k]
        (mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) from rfl,
    peterssonInner_slash_adjoint (k := k) (fd : Set UpperHalfPlane)
      (mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) h_det_pos
      (⇑f ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ))
      (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹))]
  rw [peterssonAdj_mapGL_SL_eq_inv,
    show ((⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹) : UpperHalfPlane → ℂ)) =
      (⇑g ∣[k] (mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ)) from rfl,
    ← SlashAction.slash_mul,
    mul_inv_cancel (mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ),
    SlashAction.slash_one]
  -- Step 6: insert the Fricke-square in the f-slot (`fricke_square_inv_smul`).
  conv_lhs => rw [show (⇑f : UpperHalfPlane → ℂ) =
    (Newform.frickeSquareScalar N k)⁻¹ •
      ((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (Newform.frickeMatrix N : GL (Fin 2) ℝ)) from
      (Newform.fricke_square_inv_smul ⇑f).symm]
  rw [smul_slash_pos_det k (Newform.frickeSquareScalar N k)⁻¹ _
      (T_p_upper p hp.pos b) (T_p_upper_det_pos p hp.pos b)]
  rw [UpperHalfPlane.peterssonInner_conj_smul_left]
  -- Step 9 (bridge): T151+T152 combined (GL ℚ → GL ℝ via glMap; def-eq).
  rw [show (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (T_p_upper p hp.pos b : GL (Fin 2) ℚ) : UpperHalfPlane → ℂ) =
      (((⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ∣[k]
        (glMap (T_p_upper p hp.pos b) : GL (Fin 2) ℝ)) from rfl,
    Newform.peterssonInner_fricke_T_p_upper_rewrite_adjoint_t152
      ((mapGL ℝ ((q.out : SL(2, ℤ))⁻¹) : GL (Fin 2) ℝ) •
        (fd : Set UpperHalfPlane))
      N hp.pos b (⇑f ∣[k] (Newform.frickeMatrix N : GL (Fin 2) ℝ)) ⇑g]
  congr 1
  exact Newform.conj_frickeSquareScalar_inv N k

open UpperHalfPlane MeasureTheory ModularGroup in
/-- **T156 bridge: T155 shifted residual ⟹ T154 b-sum residual.**

Direct bridge from `HasBadPrimeFrickePerCosetT152ShiftedFD` (T155 named
residual) back to `HasBadPrimeFrickePerCosetBsumShiftedFD` (T154 named
residual), via T157's now-proven `HasBadPrimeFrickePerCosetSumTransport`
(`hasBadPrimeFrickePerCosetSumTransport`). Closes the chain via scalar
arithmetic `(c⁻¹) * (c * X) = X` using `frickeSquareScalar_ne_zero`. -/
theorem Newform.hasBadPrimeFrickePerCosetBsumShiftedFD_of_t152ShiftedFD
    {N : ℕ} [NeZero N] {k : ℤ} {p : ℕ} [NeZero p]
    (hp : p.Prime) (hpN : ¬ Nat.Coprime p N)
    (h_shifted :
      Newform.HasBadPrimeFrickePerCosetT152ShiftedFD N k p hp hpN) :
    Newform.HasBadPrimeFrickePerCosetBsumShiftedFD N k p hp hpN := by
  intro f g q
  rw [Newform.hasBadPrimeFrickePerCosetSumTransport hp hpN f g q,
    h_shifted f g q, ← mul_assoc,
    inv_mul_cancel₀ (Newform.frickeSquareScalar_ne_zero N k), one_mul]


end HeckeRing.GL2
