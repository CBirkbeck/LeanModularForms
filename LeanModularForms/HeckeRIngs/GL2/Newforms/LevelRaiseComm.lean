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
import LeanModularForms.HeckeRIngs.GL2.Newforms.Basic

/-!
# Newforms: level-raise / `T_p` commutation machinery

Matrix helpers for level raising and the commutation `heckeT_n_levelRaise_comm` (DS Thm 5.6.2), together with the T171 trivial-inclusion oldform API for the bad-prime (`p ∣ d`) case.

This module is part of the split of `Newforms.lean`; see that file's header
for the overall design.  Declarations are kept in their original order.
-/

noncomputable section

namespace HeckeRing.GL2

open CongruenceSubgroup Matrix.SpecialLinearGroup CuspForm
open HeckeRing.GL2.Unified
open scoped MatrixGroups ModularForm Pointwise DirectSum

variable {N : ℕ} [NeZero N] {k : ℤ}
/-! ### Matrix helpers for level-raise / T_p commutation -/

open Matrix in
/-- The shift matrix `[[1, q], [0, 1]]` as an `SL(2, ℤ)` element. -/
def shiftSL (q : ℤ) : SL(2, ℤ) :=
  ⟨!![1, q; 0, 1], by simp [Matrix.det_fin_two]⟩

/-- `shiftSL q ∈ Γ₁(M)` for any level `M`. -/
lemma shiftSL_mem_Gamma1 (M : ℕ) (q : ℤ) : shiftSL q ∈ Gamma1 M := by
  rw [Gamma1_mem]; refine ⟨?_, ?_, ?_⟩ <;> simp [shiftSL]

/-- `glMap ∘ mapGL ℚ = mapGL ℝ` on `SL(2, ℤ)`:
the two embeddings `SL₂(ℤ) → GL₂(ℝ)` via ℚ and directly agree. -/
private lemma glMap_mapGL_eq_R (s : SL(2, ℤ)) :
    glMap (mapGL ℚ s) = (mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) s := by
  apply Units.ext; ext i j
  simp only [glMap, Matrix.GeneralLinearGroup.map]
  exact (IsScalarTower.algebraMap_apply ℤ ℚ ℝ (s.1 i j)).symm

/-- Slash by `mapGL ℚ S` for `S ∈ Γ₁(M)` preserves `Γ₁(M)`-invariant functions. -/
private lemma slash_mapGL_Q_Gamma1 (M : ℕ) [NeZero M] (k : ℤ) (S : SL(2, ℤ))
    (hS : S ∈ Gamma1 M) (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑g ∣[k] (mapGL ℚ S : GL (Fin 2) ℚ) = ⇑g := by
  show ⇑g ∣[k] glMap (mapGL ℚ S) = ⇑g
  rw [glMap_mapGL_eq_R]
  exact g.slash_action_eq' (mapGL ℝ S) (Subgroup.mem_map.mpr ⟨S, hS, rfl⟩)

open Matrix in
/-- `T_p_upper(a) = mapGL ℚ (shiftSL (a/p)) * T_p_upper(a % p)` in `GL(2, ℚ)`.
Here `a/p` is natural number division, used as an integer for `shiftSL`. -/
private lemma T_p_upper_mod (p : ℕ) (hp : 0 < p) (a : ℕ) :
    T_p_upper p hp a = mapGL ℚ (shiftSL (↑(a / p : ℕ) : ℤ)) * T_p_upper p hp (a % p) := by
  apply Units.ext
  ext i j
  simp only [T_p_upper, shiftSL, mapGL_coe_matrix, Matrix.GeneralLinearGroup.mkOfDetNeZero,
    Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul]
  fin_cases i <;> fin_cases j <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- Remaining: (0,1) entry, goal ↑a = ↑(a%p) + ↑(↑a/↑p) * ↑p in ℚ
  rw [← Int.natCast_ediv]
  simp only [Int.cast_natCast]
  exact_mod_cast show (a : ℤ) = (a % p : ℤ) + (a / p : ℤ) * (p : ℤ) from by
    have := Int.emod_add_mul_ediv (a : ℤ) (p : ℤ); linarith

/-- Γ₁-periodicity: `g ∣[k] T_p_upper(a) = g ∣[k] T_p_upper(a % p)` for level-`M` forms. -/
private lemma slash_T_p_upper_mod (M : ℕ) [NeZero M] (k : ℤ) (p : ℕ) (hp : 0 < p) (a : ℕ)
    (g : ModularForm ((Gamma1 M).map (mapGL ℝ)) k) :
    ⇑g ∣[k] (T_p_upper p hp a : GL (Fin 2) ℚ) =
      ⇑g ∣[k] (T_p_upper p hp (a % p) : GL (Fin 2) ℚ) := by
  rw [T_p_upper_mod p hp a, SlashAction.slash_mul]
  congr 1
  exact slash_mapGL_Q_Gamma1 M k (shiftSL (↑(a / p : ℕ))) (shiftSL_mem_Gamma1 M _) g

open Matrix in
/-- `α_d * glMap(β_b) = glMap(β_{d*b}) * α_d` in `GL(2, ℝ)`. -/
private lemma levelRaise_mul_T_p_upper (d : ℕ) [NeZero d] (p : ℕ) (hp : 0 < p) (b : ℕ) :
    levelRaiseMatrix d * glMap (T_p_upper p hp b) =
      glMap (T_p_upper p hp (d * b)) * levelRaiseMatrix d := by
  apply Matrix.GeneralLinearGroup.ext; intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    levelRaiseMatrix, glMap, Matrix.GeneralLinearGroup.map,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one]

open Matrix in
/-- Diagonal matrices commute: `α_d * glMap(β_∞) = glMap(β_∞) * α_d` in `GL(2, ℝ)`. -/
private lemma levelRaise_mul_T_p_lower (d : ℕ) [NeZero d] (p : ℕ) (hp : 0 < p) :
    levelRaiseMatrix d * glMap (T_p_lower p hp) =
      glMap (T_p_lower p hp) * levelRaiseMatrix d := by
  apply Matrix.GeneralLinearGroup.ext; intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    levelRaiseMatrix, glMap, Matrix.GeneralLinearGroup.map,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.cons_val_zero, Matrix.cons_val_one]; try ring)

/-- Reindexing: `Σ_{b < p} f(d*b % p) = Σ_{b < p} f(b)` when `gcd(d, p) = 1`.
The map `b ↦ d*b mod p` is a bijection on `{0,...,p-1}` since `d` is a unit mod `p`. -/
private lemma sum_reindex_mul_mod {α : Type*} [AddCommMonoid α] (d p : ℕ)
    (hp : Nat.Prime p) (hd : Nat.Coprime d p) (f : ℕ → α) :
    ∑ b ∈ Finset.range p, f (d * b % p) = ∑ b ∈ Finset.range p, f b := by
  -- Use that multiplication by d is a permutation on ZMod p
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- Convert to ZMod p indexing
  have h_val_range : ∀ b ∈ Finset.range p, d * b % p < p :=
    fun b _ => Nat.mod_lt _ hp.pos
  -- Injectivity: d*b₁ ≡ d*b₂ (mod p) → b₁ ≡ b₂ (mod p) → b₁ = b₂ (both < p)
  have h_inj : Set.InjOn (fun b => d * b % p) (↑(Finset.range p)) := by
    intro b₁ hb₁ b₂ hb₂ heq
    simp only [Finset.coe_range, Set.mem_Iio] at hb₁ hb₂
    have h₁ : (d * b₁) % p = (d * b₂) % p := heq
    have h₂ : b₁ % p = b₂ % p := by
      have : (d : ZMod p) ≠ 0 := by
        intro h; rw [ZMod.natCast_eq_zero_iff] at h
        exact (hp.coprime_iff_not_dvd.mp hd.symm) h
      have h₃ : ((d * b₁ : ℕ) : ZMod p) = ((d * b₂ : ℕ) : ZMod p) :=
        (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h₁
      simp only [Nat.cast_mul] at h₃
      have h₄ : (b₁ : ZMod p) = (b₂ : ZMod p) := mul_left_cancel₀ this h₃
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h₄
    rwa [Nat.mod_eq_of_lt hb₁, Nat.mod_eq_of_lt hb₂] at h₂
  refine Finset.sum_nbij (fun b => d * b % p)
    (fun b _ => Finset.mem_range.mpr (Nat.mod_lt _ hp.pos))
    h_inj ?_ (fun b _ => rfl)
  -- Surjectivity: injective map on finite set of same card is surjective
  intro b hb
  have h_img : Finset.image (fun b => d * b % p) (Finset.range p) = Finset.range p := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.image_subset_iff.mpr (fun b _ => Finset.mem_range.mpr (Nat.mod_lt _ hp.pos))
    · rw [Finset.card_image_of_injOn h_inj]
  have : b ∈ Finset.image (fun b => d * b % p) (Finset.range p) := by
    rw [h_img]; exact hb
  exact Finset.mem_image.mp this

/-- `(c • f) ∣[k] α_d = c • (f ∣[k] α_d)` for `levelRaiseMatrix d` (det > 0). -/
private lemma smul_slash_levelRaise (k : ℤ) (d : ℕ) [NeZero d] (c : ℂ)
    (f : UpperHalfPlane → ℂ) :
    (c • f) ∣[k] levelRaiseMatrix d = c • (f ∣[k] levelRaiseMatrix d) := by
  have hσ : UpperHalfPlane.σ (levelRaiseMatrix d) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; rw [if_pos]
    show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (levelRaiseMatrix d) : ℝ)
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    simp [levelRaiseMatrix, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.det_fin_two,
      Nat.cast_pos.mpr (Nat.pos_of_neZero d)]
  ext z; rw [ModularForm.smul_slash, hσ, RingHom.id_apply]

/-- Slash distributes over finset sums (for `GL(2, ℝ)` elements). -/
private lemma sum_slash_R (k : ℤ) {ι : Type*} (s : Finset ι)
    (φ : ι → (UpperHalfPlane → ℂ)) (g : GL (Fin 2) ℝ) :
    (∑ b ∈ s, φ b) ∣[k] g = ∑ b ∈ s, (φ b ∣[k] g) := by
  induction s using Finset.cons_induction with
  | empty => simp [SlashAction.zero_slash]
  | cons a s has ih => simp only [Finset.sum_cons, SlashAction.add_slash, ih]

/-- **Diamond/level-raise commutation equality**: `⟨a⟩_N (ι_d g) = ι_d (⟨a'⟩_M g)`
where `a' = unitsMap a` (the cast of `a` from `(ZMod N)ˣ` to `(ZMod M)ˣ`).

This is the EQUALITY version (not just membership). Used in the Hecke/level-raise
commutation via the prime-power recurrence. -/
lemma diamondOp_levelRaise_eq (a : (ZMod N)ˣ)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    diamondOp_cusp k a (heq ▸ levelRaise M d k g) =
      heq ▸ levelRaise M d k (diamondOpCusp k (ZMod.unitsMap (heq ▸ Nat.dvd_mul_left M d) a) g) := by
  subst heq
  obtain ⟨g₀, hg₀⟩ := Gamma0MapUnits_surjective (N := d * M) a
  set g₀'_sl : SL(2, ℤ) := levelRaiseConjOfDvd d (g₀ : SL(2, ℤ))
    (Gamma0_dmul_lower_left_dvd d M (g₀ : SL(2, ℤ)) g₀.property) with hg₀'_def
  have hg₀'_mem : g₀'_sl ∈ Gamma0 M :=
    levelRaiseConjOfDvd_mem_Gamma0 d M (g₀ : SL(2, ℤ)) g₀.property
  let g₀' : ↥(Gamma0 M) := ⟨g₀'_sl, hg₀'_mem⟩
  have h_lower_right : (g₀'_sl : SL(2, ℤ)).val 1 1 = (g₀ : SL(2, ℤ)).val 1 1 :=
    levelRaiseConjOfDvd_lower_right d (g₀ : SL(2, ℤ))
      (Gamma0_dmul_lower_left_dvd d M (g₀ : SL(2, ℤ)) g₀.property)
  have h_units : Gamma0MapUnits g₀' =
      ZMod.unitsMap (Nat.dvd_mul_left M d) a := by
    apply Units.ext
    rw [Gamma0MapUnits_val, ZMod.unitsMap_val, ← hg₀, Gamma0MapUnits_val]
    show ((((g₀'_sl : SL(2, ℤ)).val 1 1 : ℤ) : ZMod M)) = _
    rw [h_lower_right]
    exact (ZMod.cast_intCast (Nat.dvd_mul_left M d) ((g₀ : SL(2, ℤ)).val 1 1)).symm
  apply CuspForm.ext; intro z
  have hL : ⇑(diamondOp_cusp k a (levelRaise M d k g)) =
      ⇑(levelRaise M d k g) ∣[k] mapGL ℝ (g₀ : SL(2, ℤ)) := by
    show ⇑(diamondOpCusp k a (levelRaise M d k g)) =
      ⇑(levelRaise M d k g) ∣[k] mapGL ℝ (g₀ : SL(2, ℤ))
    rw [diamondOpCusp_eq k a g₀ hg₀]; rfl
  have hh : ⇑(diamondOpCusp k (ZMod.unitsMap (Nat.dvd_mul_left M d) a) g) =
      ⇑g ∣[k] mapGL ℝ (g₀'_sl : SL(2, ℤ)) := by
    rw [diamondOpCusp_eq k (ZMod.unitsMap (Nat.dvd_mul_left M d) a) g₀' h_units]; rfl
  rw [hL]
  have hLR : ⇑(levelRaise M d k g) =
      ((d : ℂ) ^ (1 - k)) • (⇑g ∣[k] levelRaiseMatrix d) := rfl
  rw [hLR]
  have hσ_g₀ : UpperHalfPlane.σ (mapGL ℝ (g₀ : SL(2, ℤ))) = RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; rw [if_pos]
    show (0 : ℝ) < (Matrix.GeneralLinearGroup.det (mapGL ℝ (g₀ : SL(2, ℤ)))).val
    rw [Matrix.SpecialLinearGroup.det_mapGL]; norm_num
  show ((((d : ℂ) ^ (1 - k)) • (⇑g ∣[k] levelRaiseMatrix d)) ∣[k]
      mapGL ℝ (g₀ : SL(2, ℤ))) z =
    (((d : ℂ) ^ (1 - k)) • (⇑(diamondOpCusp k (ZMod.unitsMap (Nat.dvd_mul_left M d) a) g)
      ∣[k] levelRaiseMatrix d)) z
  rw [ModularForm.smul_slash k _ _ ((d : ℂ) ^ (1 - k)), hσ_g₀, RingHom.id_apply]
  rw [show ((⇑g ∣[k] levelRaiseMatrix d) ∣[k] mapGL ℝ (g₀ : SL(2, ℤ))) =
      (⇑g ∣[k] (levelRaiseMatrix d * mapGL ℝ (g₀ : SL(2, ℤ)))) from
      (SlashAction.slash_mul k _ _ _).symm]
  rw [show (levelRaiseMatrix d * mapGL ℝ (g₀ : SL(2, ℤ))) =
      mapGL ℝ g₀'_sl * levelRaiseMatrix d from
    (levelRaiseMatrix_mul_mapGL d (g₀ : SL(2, ℤ))
      (Gamma0_dmul_lower_left_dvd d M (g₀ : SL(2, ℤ)) g₀.property)).symm]
  rw [SlashAction.slash_mul, ← hh]

/-- **Upper-triangular part of `T_p` under level raising.**

The shared computation behind all three prime-`T_p` level-raise lemmas: pushing
`heckeT_p_ut` through the level-raise `LR_d` rewrites the sum over `b` into a
sum of slashed-and-reindexed translates,
`Σ_b d^{1-k} • (g ∣ [[1, d·b mod p],[0,p]]) ∣ α_d`.
Combines `smul_slash_pos_det`, the matrix commutation `levelRaise_mul_T_p_upper`,
slash associativity, and `Γ₁`-periodicity `slash_T_p_upper_mod`. -/
private lemma heckeT_p_ut_levelRaise
    (p : ℕ) (hp : Nat.Prime p) (M d : ℕ) [NeZero M] [NeZero d]
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_p_ut k p hp.pos (⇑((levelRaise M d k g).toModularForm')) =
      ∑ b ∈ Finset.range p, ((d : ℂ) ^ (1 - k)) •
        (⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * b % p) : GL (Fin 2) ℚ)) ∣[k]
          levelRaiseMatrix d := by
  simp only [heckeT_p_ut]
  have hLR : (⇑((levelRaise M d k g).toModularForm') : UpperHalfPlane → ℂ) =
    ((d : ℂ) ^ (1 - k)) • (⇑g ∣[k] levelRaiseMatrix d) := rfl
  simp_rw [hLR, smul_slash_pos_det k _ _ _ (T_p_upper_det_pos p hp.pos _)]
  simp_rw [show ∀ b, (⇑g ∣[k] levelRaiseMatrix d) ∣[k] (T_p_upper p hp.pos b : GL (Fin 2) ℚ) =
    ⇑g ∣[k] (levelRaiseMatrix d * glMap (T_p_upper p hp.pos b)) from
    fun b => show (⇑g ∣[k] levelRaiseMatrix d) ∣[k] glMap (T_p_upper p hp.pos b) = _ from
      (SlashAction.slash_mul k _ _ _).symm]
  simp_rw [levelRaise_mul_T_p_upper d p hp.pos]
  simp_rw [show ∀ b, ⇑g ∣[k] (glMap (T_p_upper p hp.pos (d * b)) * levelRaiseMatrix d) =
    (⇑g ∣[k] (T_p_upper p hp.pos (d * b) : GL (Fin 2) ℚ)) ∣[k] levelRaiseMatrix d from
    fun b => show ⇑g ∣[k] (glMap (T_p_upper p hp.pos (d * b)) * levelRaiseMatrix d) =
      (⇑g ∣[k] glMap (T_p_upper p hp.pos (d * b))) ∣[k] levelRaiseMatrix d from
      SlashAction.slash_mul k _ _ _]
  simp_rw [show ∀ b, ⇑g ∣[k] (T_p_upper p hp.pos (d * b) : GL (Fin 2) ℚ) =
    ⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * b % p) : GL (Fin 2) ℚ) from
    fun b => slash_T_p_upper_mod M k p hp.pos (d * b) g.toModularForm']

/-- **Reindexing the level-raised upper-triangular sum.**

When `(d, p) = 1`, the bijection `b ↦ d·b mod p` (`sum_reindex_mul_mod`) folds the
sum produced by `heckeT_p_ut_levelRaise` back into `heckeT_p_ut g`, slashed:
`Σ_b d^{1-k} • (g ∣ [[1, d·b mod p],[0,p]]) ∣ α_d = d^{1-k} • (heckeT_p_ut g) ∣ α_d`. -/
private lemma heckeT_p_ut_levelRaise_reindex
    (p : ℕ) (hp : Nat.Prime p) (M d : ℕ) [NeZero M] [NeZero d]
    (hdp : Nat.Coprime d p) (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (∑ b ∈ Finset.range p, ((d : ℂ) ^ (1 - k)) •
        (⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * b % p) : GL (Fin 2) ℚ)) ∣[k]
          levelRaiseMatrix d) =
      ((d : ℂ) ^ (1 - k)) •
        (heckeT_p_ut k p hp.pos (⇑g.toModularForm') ∣[k] levelRaiseMatrix d) := by
  rw [sum_reindex_mul_mod d p hp hdp
    (fun b => ((d : ℂ) ^ (1 - k)) • (⇑g.toModularForm' ∣[k]
      (T_p_upper p hp.pos b : GL (Fin 2) ℚ)) ∣[k] levelRaiseMatrix d),
    heckeT_p_ut, sum_slash_R, ← Finset.smul_sum]

/-- **Lower/diamond part of `T_p` under level raising.**

The `⟨p⟩`-twisted lower-triangular term of `T_p` commutes with `LR_d`:
`(⟨p⟩_{dM} (LR_d g)) ∣ [[p,0],[0,1]] = d^{1-k} • ((⟨p⟩_M g) ∣ [[p,0],[0,1]]) ∣ α_d`.
Combines `diamondOp_levelRaise_eq` (diamond/level-raise), `smul_slash_pos_det`,
and the diagonal commutation `levelRaise_mul_T_p_lower`. -/
private lemma diamondOp_T_p_lower_levelRaise
    (p : ℕ) (hp : Nat.Prime p) (M d : ℕ) [NeZero M] [NeZero d]
    (hpdM : Nat.Coprime p (d * M)) (hpM : Nat.Coprime p M)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(diamondOp k (ZMod.unitOfCoprime p hpdM) ((levelRaise M d k g).toModularForm')) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ)) =
      ((d : ℂ) ^ (1 - k)) •
        (⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g.toModularForm') ∣[k]
          (T_p_lower p hp.pos : GL (Fin 2) ℚ)) ∣[k] levelRaiseMatrix d := by
  have hdia := diamondOp_levelRaise_eq (ZMod.unitOfCoprime p hpdM) M d rfl g
  have hdia_fun : (⇑((diamondOp k (ZMod.unitOfCoprime p hpdM))
      ((levelRaise M d k g).toModularForm') : ModularForm _ k) : UpperHalfPlane → ℂ) =
    ((d : ℂ) ^ (1 - k)) • (⇑(diamondOpCusp k
      (ZMod.unitsMap (Nat.dvd_mul_left M d) (ZMod.unitOfCoprime p hpdM)) g) ∣[k]
      levelRaiseMatrix d) :=
    congr_arg (fun f : CuspForm _ k => (⇑f : UpperHalfPlane → ℂ)) hdia
  rw [hdia_fun, smul_slash_pos_det k _ _ _ (T_p_lower_det_pos p hp.pos)]
  have h_units_eq : ZMod.unitsMap (Nat.dvd_mul_left M d) (ZMod.unitOfCoprime p hpdM) =
      ZMod.unitOfCoprime p hpM := by
    ext; simp [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  rw [h_units_eq]
  have h_coe : (⇑(diamondOpCusp k (ZMod.unitOfCoprime p hpM) g) : UpperHalfPlane → ℂ) =
    ⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') := rfl
  rw [h_coe,
    show (⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') ∣[k]
        levelRaiseMatrix d) ∣[k] (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
      ⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') ∣[k]
        (levelRaiseMatrix d * glMap (T_p_lower p hp.pos)) from
      show (⇑((diamondOp k (ZMod.unitOfCoprime p hpM)) g.toModularForm') ∣[k]
          levelRaiseMatrix d) ∣[k] glMap (T_p_lower p hp.pos) = _ from
        (SlashAction.slash_mul k _ _ _).symm]
  rw [levelRaise_mul_T_p_lower d p hp.pos, SlashAction.slash_mul k _ _ _]
  rfl

/-- **Level-raise commutation for prime T_p** (the hard case):
`T_p (ι_d g) = ι_d (T_p^{(M)} g)` at the function level.

The proof uses the explicit formula `T_p f = Σ_b f|[[1,b],[0,p]] + (⟨p⟩f)|[[p,0],[0,1]]`:
- Upper-triangular part: `α_d * [[1,b],[0,p]] = [[1,db],[0,p]] * α_d` (matrix identity),
  then `b ↦ db mod p` is a bijection on `{0,...,p-1}` since `(d,p) = 1`.
- Lower part: uses `diamondOp_levelRaise_mem` (already proved) + level-raising
  composition `α_d * [[p,0],[0,1]] = [[dp,0],[0,1]]`.

Since the slash actions compose associatively, the function-level equality follows. -/
private lemma heckeT_p_all_levelRaise_comm
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeT_n_cusp k p (heq ▸ levelRaise M d k g) =
      heq ▸ levelRaise M d k (heckeT_n_cusp k p g) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  subst heq
  have hpM : Nat.Coprime p M := hpN.coprime_dvd_right ⟨d, mul_comm d M⟩
  have hd_coprime_p : Nat.Coprime d p := by
    have : Nat.Coprime (d * M) p := hpN.symm
    exact this.coprime_dvd_left (dvd_mul_right d M)
  apply CuspForm.ext; intro z
  -- Both sides unfold through heckeT_n → heckeT_p_all → heckeT_p_fun (coprime).
  show (heckeT_n (N := d * M) k p (levelRaise M d k g).toModularForm').toFun z =
    (((d : ℂ) ^ (1 - k)) • ((heckeT_n_cusp (N := M) k p g : CuspForm _ k).toFun
      ∣[k] levelRaiseMatrix d)) z
  rw [heckeT_n_prime k hp]
  change ((heckeT_p_all k p hp) ((levelRaise M d k) g).toModularForm').toFun z =
    (((d : ℂ) ^ (1 - k)) • ((heckeT_n (N := M) k p g.toModularForm').toFun
      ∣[k] levelRaiseMatrix d)) z
  rw [heckeT_n_prime k hp, heckeT_p_all_coprime k hp hpN, heckeT_p_all_coprime k hp hpM]
  -- LHS = heckeT_p_fun at d*M, RHS = d^{1-k} • (heckeT_p_fun at M) ∣[k] α_d; unfold
  -- `heckeT_p_fun` into ut + lower parts and rewrite the ut part by `heckeT_p_ut_levelRaise`
  -- (the lower `⟨p⟩`-part is handled below via the diamond + diagonal commutations).
  show heckeT_p_fun k p hp hpN ((levelRaise M d k g).toModularForm') z = _
  rw [show heckeT_p_fun k p hp hpN ((levelRaise M d k g).toModularForm') =
      heckeT_p_ut k p hp.pos (⇑((levelRaise M d k g).toModularForm')) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) ((levelRaise M d k g).toModularForm')) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) from rfl,
    heckeT_p_ut_levelRaise p hp M d g]
  simp only [Pi.add_apply]
  suffices h :
    (∑ x ∈ Finset.range p, ((d : ℂ) ^ (1 - k)) •
      (⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos (d * x % p) : GL (Fin 2) ℚ)) ∣[k]
        levelRaiseMatrix d) +
    (⇑((diamondOp k (ZMod.unitOfCoprime p hpN)) ((levelRaise M d k) g).toModularForm') ∣[k]
      (T_p_lower p hp.pos : GL (Fin 2) ℚ)) =
    ((d : ℂ) ^ (1 - k)) • (((heckeT_p k p hp hpM) g.toModularForm').toFun ∣[k]
      levelRaiseMatrix d) from congr_fun h z
  -- Reindex the upper sum, unfold the RHS `heckeT_p_fun` into ut + lower, and split.
  rw [heckeT_p_ut_levelRaise_reindex p hp M d hd_coprime_p g]
  show ((d : ℂ) ^ (1 - k)) • (heckeT_p_ut k p hp.pos ⇑g.toModularForm' ∣[k] levelRaiseMatrix d) +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpN) ((levelRaise M d k g).toModularForm')) ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) =
    ((d : ℂ) ^ (1 - k)) • (heckeT_p_fun k p hp hpM g.toModularForm' ∣[k] levelRaiseMatrix d)
  rw [show heckeT_p_fun k p hp hpM g.toModularForm' = heckeT_p_ut k p hp.pos ⇑g.toModularForm' +
      ⇑(diamondOp k (ZMod.unitOfCoprime p hpM) g.toModularForm') ∣[k]
        (T_p_lower p hp.pos : GL (Fin 2) ℚ) from rfl,
    SlashAction.add_slash, smul_add]
  -- Upper sums agree; the lower `⟨p⟩`-part is `diamondOp_T_p_lower_levelRaise`.
  congr 1
  exact diamondOp_T_p_lower_levelRaise p hp M d hpN hpM g

/-- **Bad-prime version of `heckeT_p_all_levelRaise_comm` (T168 partial).**

For `p ∣ N` (bad prime) AND `p ∤ d` (level-raise factor coprime to `p`), the
Hecke operator `heckeT_p_all = heckeT_p_divN` commutes with the level-raise
`LR_d` from `S_k(Γ₁(M)) → S_k(Γ₁(d·M))` (where `d · M = N`):
```
T_p (ι_d g) = ι_d (T_p g)   (at level d·M = N)
```

**Why `p ∤ d`.**  When `p ∣ d`, the standard reindex `b ↦ d·b mod p` collapses
to `0` for all `b ∈ {0, ..., p-1}`, breaking the upper-triangular reindex
argument.  In that case `T_p (ι_d g)` is NOT generally `ι_d (T_p g)`; instead,
it relates to a level-raise from a smaller level (the "p-stabilization"
phenomenon).  This lemma covers the `p ∤ d` case which IS provable by the
same template as the coprime case.

**Companion to `heckeT_p_all_levelRaise_comm`.**  The coprime version requires
`Coprime p N` (hence both `Coprime p d` and `Coprime p M`).  This lemma
relaxes to bad prime `¬ Coprime p N` while keeping `Coprime p d` (forcing
`¬ Coprime p M` since `p ∣ N = d·M` and `p ∤ d`).

**Proof structure.** Mirrors `heckeT_p_all_levelRaise_comm` but simpler — only
the upper-triangular sum, no lower-triangular `⟨p⟩`-twist part (since
`heckeT_p_divN` has only the upper-triangular sum).  Steps:
1. `CuspForm.ext` to function-level.
2. `heckeT_n_prime` + `heckeT_p_all_not_coprime_apply` (both `N` and `M`
   sides).
3. Per-`b` use `levelRaise_mul_T_p_upper` + `slash_T_p_upper_mod`.
4. `sum_reindex_mul_mod` with `Coprime d p` to reindex `d·b mod p ↦ b`. -/
lemma heckeT_p_all_levelRaise_comm_divN
    (p : ℕ) (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N)
    (hpd : Nat.Coprime p d)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    heckeT_n_cusp k p (heq ▸ levelRaise M d k g) =
      heq ▸ levelRaise M d k (heckeT_n_cusp k p g) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  subst heq
  -- p ∤ d ∧ p ∣ d·M ⟹ p ∣ M, so heckeT_p_all at M is also bad-prime case.
  have hpM : ¬ Nat.Coprime p M := fun h => hpN (hpd.mul_right h)
  have hd_coprime_p : Nat.Coprime d p := hpd.symm
  apply CuspForm.ext; intro z
  -- Both sides unfold via heckeT_n_prime → heckeT_p_all → heckeT_p_divN.
  show (heckeT_n (N := d * M) k p (levelRaise M d k g).toModularForm').toFun z =
    (((d : ℂ) ^ (1 - k)) • ((heckeT_n_cusp (N := M) k p g : CuspForm _ k).toFun
      ∣[k] levelRaiseMatrix d)) z
  rw [heckeT_n_prime k hp]
  change ⇑((heckeT_p_all k p hp) ((levelRaise M d k) g).toModularForm') z =
    (((d : ℂ) ^ (1 - k)) • (⇑(heckeT_n (N := M) k p g.toModularForm')
      ∣[k] levelRaiseMatrix d)) z
  rw [heckeT_n_prime k hp]
  -- Convert each `heckeT_p_all` to `heckeT_p_ut` via `heckeT_p_all_not_coprime_apply`.
  rw [show ⇑((heckeT_p_all k p hp) ((levelRaise M d k) g).toModularForm') =
        heckeT_p_ut k p hp.pos (⇑((levelRaise M d k) g).toModularForm') from
      heckeT_p_all_not_coprime_apply k hp hpN _]
  rw [show ⇑((heckeT_p_all k p hp) g.toModularForm') =
        heckeT_p_ut k p hp.pos (⇑g.toModularForm') from
      heckeT_p_all_not_coprime_apply k hp hpM _]
  -- LHS is heckeT_p_ut at level d*M of LR_d g, RHS is d^{1-k} • (heckeT_p_ut at M of g) ∣ α_d;
  -- rewrite the level-raised sum (`heckeT_p_ut_levelRaise`) then reindex (`..._reindex`).
  show heckeT_p_ut k p hp.pos (⇑((levelRaise M d k) g).toModularForm') z =
    (((d : ℂ) ^ (1 - k)) • (heckeT_p_ut k p hp.pos (⇑g.toModularForm') ∣[k]
      levelRaiseMatrix d)) z
  rw [heckeT_p_ut_levelRaise p hp M d g, heckeT_p_ut_levelRaise_reindex p hp M d hd_coprime_p g]

/-! ### T171 trivial-inclusion oldform API (`p ∣ d` bad-prime case) -/

/-- **`Γ₁(N) ≤ Γ₁(M)` for `M ∣ N`.**

The standard nesting of principal congruence subgroups: if `M ∣ N`, then any
matrix congruent to the identity modulo `N` is also congruent modulo `M`.
Direct from the membership characterization `Gamma1_mem`. -/
lemma Gamma1_le_Gamma1_of_dvd {M N : ℕ} (hMN : M ∣ N) :
    CongruenceSubgroup.Gamma1 N ≤ CongruenceSubgroup.Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h00, h11, h10⟩ := hA
  have h_cast : ∀ (k : ℤ), ((k : ℤ) : ZMod M) =
      (ZMod.castHom hMN (ZMod M)) ((k : ℤ) : ZMod N) := fun k => by
    rw [ZMod.castHom_apply]; exact (ZMod.cast_intCast hMN _).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [h_cast, h00, map_one]
  · rw [h_cast, h11, map_one]
  · rw [h_cast, h10, map_zero]

/-- **`(Γ₁(N)).map (mapGL ℝ) ≤ (Γ₁(M)).map (mapGL ℝ)` for `M ∣ N`.**

GL-image version of `Gamma1_le_Gamma1_of_dvd`, used to transfer cusp forms
between levels via `restrictSubgroup`. -/
lemma Gamma1_map_le_Gamma1_map_of_dvd {M N : ℕ} (hMN : M ∣ N) :
    (CongruenceSubgroup.Gamma1 N).map (mapGL ℝ) ≤
      (CongruenceSubgroup.Gamma1 M).map (mapGL ℝ) :=
  Subgroup.map_mono (Gamma1_le_Gamma1_of_dvd hMN)

/-- **Trivial-inclusion CuspForm map (level descent into deeper level).**

For `M ∣ N`, a CuspForm at level `Γ₁(M)` is automatically `Γ₁(N)`-invariant
(since `Γ₁(N) ⊆ Γ₁(M)`).  This map lifts a `CuspForm ((Gamma1 M).map (mapGL ℝ)) k`
to a `CuspForm ((Gamma1 N).map (mapGL ℝ)) k` with the SAME underlying function.

This is the **trivial-inclusion oldform API** missing from `IsOldformGenerator`:
classically, `S_k^old(N) = ⊕_{M ∣ N, M < N} (S_k(Γ₁(M)) ⊕ LR_{N/M}(S_k(Γ₁(M))))`,
the first summand being `levelInclude_cusp` and the second being `levelRaise`. -/
def levelInclude_cusp {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N) (k : ℤ) :
    CuspForm ((Gamma1 M).map (mapGL ℝ)) k →ₗ[ℂ]
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun f := CuspForm.restrictSubgroup (Gamma1_map_le_Gamma1_map_of_dvd hMN) f
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- **Coercion-level identity for `levelInclude_cusp`.** -/
@[simp]
lemma levelInclude_cusp_coe {M N : ℕ} [NeZero M] [NeZero N]
    (hMN : M ∣ N) (k : ℤ)
    (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    (⇑(levelInclude_cusp hMN k f) : UpperHalfPlane → ℂ) = ⇑f := rfl

/-- **`IsLevelInclusionOldformGenerator` (T171 trivial-inclusion oldform predicate).**

A cusp form `f : CuspForm Γ₁(N) k` is a *trivial-inclusion oldform generator*
if there exists a strictly smaller divisor `M ∣ N, M < N` and a cusp form
`g : CuspForm Γ₁(M) k` such that `f = levelInclude_cusp g` (i.e., `g` viewed
as a Γ₁(N)-form via `restrictSubgroup` since `Γ₁(N) ⊆ Γ₁(M)`).

**Companion to `IsOldformGenerator`.**  Classically `S_k^old(N) =
span(IsOldformGenerator ∪ IsLevelInclusionOldformGenerator)`.  The Lean
`cuspFormsOld` defined as `span IsOldformGenerator` is **strictly narrower**
than classical `S_k^old`; this predicate captures the missing piece. -/
def IsLevelInclusionOldformGenerator (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    Prop :=
  ∃ (M : ℕ) (_ : NeZero M) (hMN : M ∣ N) (_ : M < N)
      (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    levelInclude_cusp hMN k g = f

/-- **`cuspFormsOldExtended` (T171): classical `S_k^old(N)`.**

`cuspFormsOld N k` extended with the trivial-inclusion oldform generators
to match the classical Diamond-Shurman / Miyake `S_k^old(N) = ⊕_{M ∣ N, M < N}
(S_k(Γ₁(M)) ⊕ LR_{N/M}(S_k(Γ₁(M))))`.

The current Lean `cuspFormsOld N k` (defined via `IsOldformGenerator` only)
contains only the level-raise summands `LR_{N/M}(S_k(Γ₁(M)))`; this extended
version adds the trivial-inclusion summands `S_k(Γ₁(M)) ↪ S_k(Γ₁(N))` for
`M ∣ N, M < N`, recovering classical S_k^old.

The relation `cuspFormsOld N k ≤ cuspFormsOldExtended N k` is immediate
(left summand of the disjunction).  The reverse inclusion fails in general
(e.g., for `N = p²`, `S_k(Γ₁(p))` includes into `S_k(Γ₁(p²))` but is not
in the level-raise span). -/
def cuspFormsOldExtended (N : ℕ) [NeZero N] (k : ℤ) :
    Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ
    {f | IsOldformGenerator f ∨ IsLevelInclusionOldformGenerator f}

/-- **`cuspFormsOld ≤ cuspFormsOldExtended`.** -/
lemma cuspFormsOld_le_cuspFormsOldExtended :
    cuspFormsOld N k ≤ cuspFormsOldExtended N k :=
  Submodule.span_mono (fun _ hf => Or.inl hf)

/-- **`levelInclude_cusp g ∈ cuspFormsOldExtended`** (membership of a trivial
inclusion generator). -/
lemma levelInclude_cusp_mem_cuspFormsOldExtended
    {M : ℕ} [NeZero M] (hMN : M ∣ N) (hMltN : M < N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    levelInclude_cusp hMN k g ∈ cuspFormsOldExtended N k := by
  refine Submodule.subset_span (Or.inr ?_)
  exact ⟨M, inferInstance, hMN, hMltN, g, rfl⟩

/-- **`HasCuspFormsOldEqualsExtended` (T171 named blocker)**.

The named hypothesis that the Lean `cuspFormsOld N k` equals the classical
`cuspFormsOldExtended N k`.  Equivalently, every trivial-inclusion oldform
generator `levelInclude_cusp g` (for `M ∣ N, M < N, g ∈ S_k(Γ₁(M))`) lies
in the level-raise span `cuspFormsOld N k`.

**Status.** This is **false in general** for the current Lean `cuspFormsOld`
def: at `N = p²`, the trivial inclusion `S_k(Γ₁(p)) ↪ S_k(Γ₁(p²))` is NOT
in the span of `LR_p` images (different functions).  The classical
`S_k^old` definition includes both, so this hypothesis really requires
**either** extending the Lean `cuspFormsOld` def to span both kinds of
generators, **or** restricting the bad-prime preservation theorem to
`cuspFormsOldExtended`.  This Prop names the gap precisely. -/
def Newform.HasCuspFormsOldEqualsExtended (N : ℕ) [NeZero N] (k : ℤ) : Prop :=
  cuspFormsOld N k = cuspFormsOldExtended N k

/-- **T171 case analysis: `heckeT_p_divN(LR_d g_0)` for `p ∣ d` lies in
`cuspFormsOldExtended N k` (named blocker version).**

Stated as a Prop named `Newform.HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended`
so downstream consumers can compose with `Newform.HasCuspFormsOldEqualsExtended`
to obtain the full bad-prime preservation theorem.

**Mathematical content.** For the `p ∣ d` case, function-level computation
shows `heckeT_p_divN(LR_d g_0)(τ) = (LR_{d/p} g_0)(τ)` (after the
upper-triangular sum collapses via Γ₁-invariance translation).  The output
is a Γ₁(N/p)-form viewed as Γ₁(N)-form via `levelInclude_cusp` (when
`d/p = 1`) or as a `LR_{d/p}`-image of a `levelInclude_cusp` form (when
`d/p > 1`).  Either case lies in `cuspFormsOldExtended N k`. -/
def Newform.HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : Nat.Prime p) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (M d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N) (_hd : 1 < d) (_hpd : p ∣ d)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
    haveI : NeZero p := ⟨_hp.ne_zero⟩
    heckeT_n_cusp k p (heq ▸ levelRaise M d k g) ∈ cuspFormsOldExtended N k

/-- **T171 — `p ∣ d` collapse identity (named blocker Prop).**

The **function-level collapse identity** for the `p ∣ d` bad-prime case:
for `p ∣ d` with `d = p · d'` (`d' = d/p ≥ 1`), the upper-triangular
sum collapses to a level-raise from `M` by the quotient `d' = d/p`:
```
heckeT_p_divN(LR_d g)(τ) = g(d' · τ).
```

Mathematical justification (sketch): each summand is `p^{-1} · g(d' · (τ+b))`,
and Γ₁(M)-period-1 invariance of `g` makes `g(σ + d'·b) = g(σ)` for `d'·b ∈ ℤ`,
collapsing the sum to `p · g(d'·τ) · p^{-1} = g(d'·τ)`.

**The proof of this identity** mirrors T168's `heckeT_p_all_levelRaise_comm_divN`
template (matrix manipulation + `slash_T_p_upper_mod` + reindex), with the
key difference that `d·b mod p = 0` for all `b` (since `p ∣ d`), so the
reindex collapses rather than permuting.  Landing the full proof requires
extensive matrix/slash manipulation beyond this Phase; this Prop names the
identity precisely so downstream consumers can package it. -/
def Newform.HasHeckeT_p_divN_LR_d_collapse_identity
    (N : ℕ) [NeZero N] (k : ℤ) (p : ℕ) [NeZero p]
    (_hp : Nat.Prime p) (_hpN : ¬ Nat.Coprime p N) : Prop :=
  ∀ (M d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N) (_hd : 1 < d) (_hpd : p ∣ d)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) (z : UpperHalfPlane),
    haveI : NeZero p := ⟨_hp.ne_zero⟩
    haveI : NeZero (d / p) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) _hpd) _hp.pos).ne'⟩
    (heckeT_n_cusp k p (heq ▸ levelRaise M d k g) :
        CuspForm ((Gamma1 N).map (mapGL ℝ)) k).toFun z =
      levelRaiseFun (d / p) k ⇑g z

/-- **T171 — `p ∣ d` upper-sum collapse helper.**

For `p ∣ d`, the index `d * b mod p = 0` for all `b : ℕ`, since `p ∣ d * b`.
This is the **combinatorial collapse** step underlying the function-level
collapse identity of `HasHeckeT_p_divN_LR_d_collapse_identity`. -/
private lemma mul_mod_eq_zero_of_dvd {p d b : ℕ} (_hp : 0 < p) (hpd : p ∣ d) :
    d * b % p = 0 :=
  Nat.mod_eq_zero_of_dvd (hpd.mul_right b)

/-- **T171 matrix-value helper for `glMap (T_p_upper p hp 0)`.**

The underlying matrix of `glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ` is
`!![1, 0; 0, p]` over `ℝ` (cast from ℚ via `T_p_upper_coe + Matrix.map`). -/
private lemma glMap_T_p_upper_zero_val (p : ℕ) (hp : 0 < p) :
    ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; 0, (p : ℝ)] := by
  show (T_p_upper p hp 0 : Matrix (Fin 2) (Fin 2) ℚ).map (algebraMap ℚ ℝ) =
      !![(1 : ℝ), 0; 0, (p : ℝ)]
  rw [T_p_upper_coe]
  ext i j
  fin_cases i
  · fin_cases j
    · show ((1 : ℚ) : ℝ) = (1 : ℝ); norm_num
    · show ((0 : ℚ) : ℝ) = 0; norm_num
  · fin_cases j
    · show ((0 : ℚ) : ℝ) = 0; norm_num
    · show ((p : ℚ) : ℝ) = (p : ℝ); norm_num

/-- **T171 matrix-value helper for `levelRaiseMatrix d`.**

The underlying matrix of `levelRaiseMatrix d : GL (Fin 2) ℝ` is `!![d, 0; 0, 1]`
over `ℝ`, by `mkOfDetNeZero` definitional unfolding. -/
private lemma levelRaiseMatrix_val (d : ℕ) [NeZero d] :
    ((levelRaiseMatrix d : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ) = !![(d : ℝ), 0; 0, 1] := rfl

/-- **T171 matrix product helper for `T_p_upper(0) · levelRaiseMatrix d`.**

The matrix product `glMap (T_p_upper p hp 0) * levelRaiseMatrix d` (as a `GL`
element) has underlying matrix `!![d, 0; 0, p]` over `ℝ`.  This is the
matrix-level content of the `p ∣ d` collapsed-product step in the function-level
collapse identity for `HasHeckeT_p_divN_LR_d_collapse_identity`. -/
private lemma T_p_upper_zero_mul_levelRaise_matrix
    (p d : ℕ) (hp : 0 < p) [NeZero d] :
    (((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d :
      GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![(d : ℝ), 0; 0, (p : ℝ)] := by
  rw [show (((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d :
        GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) *
      ((levelRaiseMatrix d : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) from
    Units.val_mul _ _]
  rw [glMap_T_p_upper_zero_val p hp, levelRaiseMatrix_val d]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i
  · fin_cases j
    · show (1 : ℝ) * (d : ℝ) + 0 * 0 = (d : ℝ); ring
    · show (1 : ℝ) * 0 + 0 * 1 = 0; ring
  · fin_cases j
    · show (0 : ℝ) * (d : ℝ) + (p : ℝ) * 0 = 0; ring
    · show (0 : ℝ) * 0 + (p : ℝ) * 1 = (p : ℝ); ring

/-- **T171 — det of the `T_p_upper(0) · levelRaiseMatrix d` product.**

`(glMap (T_p_upper p hp 0) * levelRaiseMatrix d).det.val = p · d` over `ℝ`. -/
private lemma T_p_upper_zero_mul_levelRaise_det
    (p d : ℕ) (hp : 0 < p) [NeZero d] :
    ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d).det.val =
    (p : ℝ) * (d : ℝ) := by
  show ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d :
      GL (Fin 2) ℝ).val.det = (p : ℝ) * (d : ℝ)
  rw [T_p_upper_zero_mul_levelRaise_matrix p d hp]
  rw [Matrix.det_fin_two_of]
  ring

/-- **T171 — `T_p_upper(0) · levelRaiseMatrix d` has positive det (`p · d`).** -/
private lemma T_p_upper_zero_mul_levelRaise_det_pos
    (p d : ℕ) (hp : 0 < p) [NeZero d] :
    0 < ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d).det.val := by
  rw [T_p_upper_zero_mul_levelRaise_det p d hp]
  exact mul_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr (NeZero.pos d))

/-- **T171 — denom of `T_p_upper(0) · levelRaiseMatrix d` at `z`**: equals `p`. -/
private lemma T_p_upper_zero_mul_levelRaise_denom
    (p d : ℕ) (hp : 0 < p) [NeZero d] (z : UpperHalfPlane) :
    UpperHalfPlane.denom
      ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d)
      (z : ℂ) = (p : ℂ) := by
  show ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        levelRaiseMatrix d : GL (Fin 2) ℝ).val 1 0 * (z : ℂ) +
      ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        levelRaiseMatrix d : GL (Fin 2) ℝ).val 1 1 = (p : ℂ)
  rw [T_p_upper_zero_mul_levelRaise_matrix p d hp]
  simp

/-- **T171 — num of `T_p_upper(0) · levelRaiseMatrix d` at `z`**: equals `d · z`. -/
private lemma T_p_upper_zero_mul_levelRaise_num
    (p d : ℕ) (hp : 0 < p) [NeZero d] (z : UpperHalfPlane) :
    UpperHalfPlane.num
      ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d)
      (z : ℂ) = (d : ℂ) * (z : ℂ) := by
  show ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        levelRaiseMatrix d : GL (Fin 2) ℝ).val 0 0 * (z : ℂ) +
      ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
        levelRaiseMatrix d : GL (Fin 2) ℝ).val 0 1 = (d : ℂ) * (z : ℂ)
  rw [T_p_upper_zero_mul_levelRaise_matrix p d hp]
  simp

/-- **T171 — Möbius action coercion of `T_p_upper(0) · levelRaiseMatrix d` at `z`.**

For `p ∣ d`, the action `(glMap T_p_upper(0) * levelRaiseMatrix d) • z` (as a
complex number) equals `((d/p : ℕ) : ℂ) * (z : ℂ)`.  This matches the action
`(d/p) · z` of `levelRaiseMatrix(d/p)` on `z`. -/
private lemma T_p_upper_zero_mul_levelRaise_smul_coe
    {p d : ℕ} (hp : 0 < p) (hpd : p ∣ d) [NeZero d] (z : UpperHalfPlane) :
    ((((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d :
        GL (Fin 2) ℝ) • z : UpperHalfPlane) : ℂ) =
      ((d / p : ℕ) : ℂ) * (z : ℂ) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos
      (T_p_upper_zero_mul_levelRaise_det_pos p d hp)]
  rw [T_p_upper_zero_mul_levelRaise_num p d hp z,
      T_p_upper_zero_mul_levelRaise_denom p d hp z]
  -- Goal: (d : ℂ) * (z : ℂ) / (p : ℂ) = ((d / p : ℕ) : ℂ) * (z : ℂ).
  have hp_cast_ne : ((p : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hp)
  have h_d_eq : ((d : ℕ) : ℂ) = ((p : ℕ) : ℂ) * ((d / p : ℕ) : ℂ) := by
    rw [show ((p : ℕ) : ℂ) * ((d / p : ℕ) : ℂ) = (((p * (d / p) : ℕ) : ℂ)) from by
      push_cast; ring,
      Nat.mul_div_cancel' hpd]
  rw [h_d_eq]
  field_simp

/-- **T171 — Möbius action equality at the `ℍ` level.**

For `p ∣ d`, the actions of `glMap T_p_upper(0) * levelRaiseMatrix d` and
`levelRaiseMatrix (d/p)` on `z : ℍ` agree as elements of `ℍ` (both equal
`(d/p) · z`).  Used to identify `f (M • z)` with `f (levelRaiseMatrix (d/p) • z)`
in the slash-level proof. -/
private lemma T_p_upper_zero_mul_levelRaise_smul_eq
    {p d : ℕ} (hp : 0 < p) (hpd : p ∣ d) [NeZero d] (z : UpperHalfPlane) :
    haveI : NeZero (d / p) :=
      ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) hpd) hp).ne'⟩
    (((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d :
        GL (Fin 2) ℝ) • z : UpperHalfPlane) =
      ((levelRaiseMatrix (d / p) : GL (Fin 2) ℝ) • z : UpperHalfPlane) := by
  haveI : NeZero (d / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) hpd) hp).ne'⟩
  have hd_quot_pos : 0 < d / p :=
    Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) hpd) hp
  apply UpperHalfPlane.ext
  rw [T_p_upper_zero_mul_levelRaise_smul_coe hp hpd z]
  -- Show: ((levelRaiseMatrix (d/p) • z : ℍ) : ℂ) = ((d/p : ℕ) : ℂ) * (z : ℂ).
  have h_LR_det_pos : 0 < (levelRaiseMatrix (d / p) : GL (Fin 2) ℝ).det.val := by
    show 0 < ((levelRaiseMatrix (d / p) : GL (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ).det
    rw [levelRaiseMatrix_val (d / p), Matrix.det_fin_two_of]
    have h1 : (0 : ℝ) < ((d / p : ℕ) : ℝ) := by exact_mod_cast hd_quot_pos
    linarith
  rw [UpperHalfPlane.coe_smul_of_det_pos h_LR_det_pos]
  have h_num : UpperHalfPlane.num (levelRaiseMatrix (d / p)) (z : ℂ) =
      ((d / p : ℕ) : ℂ) * (z : ℂ) := by
    show ((levelRaiseMatrix (d / p) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (z : ℂ) +
      ((levelRaiseMatrix (d / p) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 0 1 = _
    rw [levelRaiseMatrix_val (d / p)]
    simp
  have h_denom : UpperHalfPlane.denom (levelRaiseMatrix (d / p)) (z : ℂ) = 1 := by
    show ((levelRaiseMatrix (d / p) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 1 0 * (z : ℂ) +
      ((levelRaiseMatrix (d / p) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1
    rw [levelRaiseMatrix_val (d / p)]
    simp
  rw [h_num, h_denom, div_one]

/-- **T171 — scalar collapse for the `p ∣ d` slash product.**

The pure ℂ-arithmetic identity behind the `p ∣ d` slash collapse: with `p ∣ d`
(so `d = p · (d/p)`) and `p ≠ 0`, the determinant/denominator scalars combine as
`x · (p·d)^{k-1} · p^{-k} = p^{k-2} · (x · (d/p)^{k-1})`.  Pulls `2(k-1) - k = k-2`
out of the prime powers via `zpow_add₀`. -/
private lemma T_p_zero_levelRaise_scalar_collapse
    {p d : ℕ} (hp : 0 < p) (hpd : p ∣ d) (x : ℂ) :
    x * (((p : ℝ) * (d : ℝ) : ℝ) : ℂ) ^ (k - 1) * (p : ℂ) ^ (-k) =
      (p : ℂ) ^ (k - 2) * (x * (((d / p : ℕ) : ℝ) : ℂ) ^ (k - 1)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdetC : (((p : ℝ) * (d : ℝ) : ℝ) : ℂ) = ((p : ℂ) * (p : ℂ)) * ((d / p : ℕ) : ℂ) := by
    rw [show (((p : ℝ) * (d : ℝ) : ℝ) : ℂ) = (p : ℂ) * (d : ℂ) by push_cast; ring,
      show (d : ℂ) = ((p * (d / p) : ℕ) : ℂ) by rw [Nat.mul_div_cancel' hpd]]
    push_cast; ring
  rw [hdetC, show (((d / p : ℕ) : ℝ) : ℂ) = ((d / p : ℕ) : ℂ) by push_cast; ring,
    mul_zpow, mul_zpow,
    show x * (((p : ℂ) ^ (k - 1) * (p : ℂ) ^ (k - 1)) *
        ((d / p : ℕ) : ℂ) ^ (k - 1)) * (p : ℂ) ^ (-k) =
        (((p : ℂ) ^ (k - 1) * (p : ℂ) ^ (k - 1)) * (p : ℂ) ^ (-k)) *
        (x * ((d / p : ℕ) : ℂ) ^ (k - 1)) by ring,
    show (p : ℂ) ^ (k - 1) * (p : ℂ) ^ (k - 1) = (p : ℂ) ^ (2 * k - 2) by
      rw [← zpow_add₀ hpC]; congr 1; ring,
    ← zpow_add₀ hpC, show (2 * k - 2 + -k : ℤ) = k - 2 by ring]

/-- **T171 — slash-level helper for the `p ∣ d` collapsed product.**

For `p ∣ d` with `[NeZero (d / p)]` as an explicit instance binder, the
composed slash `f ∣[k] (glMap T_p_upper(0) * levelRaiseMatrix d)` equals
`(p : ℂ)^(k-2) * f ∣[k] levelRaiseMatrix(d/p)` pointwise on `ℍ`.

Uses `ModularForm.slash_apply` + σ-id (positive det) + matrix value/det/denom
helpers + Möbius equality to reduce to scalar arithmetic in ℂ. -/
private lemma slash_T_p_upper_zero_mul_levelRaise_apply
    {p d : ℕ} (hp : 0 < p) (hpd : p ∣ d) [NeZero d] [NeZero (d / p)]
    (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) :
    ((f ∣[k] ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d)) z) =
      (p : ℂ) ^ (k - 2) *
        ((f ∣[k] (levelRaiseMatrix (d / p) : GL (Fin 2) ℝ)) z) := by
  rw [ModularForm.slash_apply, ModularForm.slash_apply]
  -- σ on positive-det matrices = id.
  have h_M_det_pos := T_p_upper_zero_mul_levelRaise_det_pos p d hp
  have hσ_M : UpperHalfPlane.σ
      ((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) * levelRaiseMatrix d) =
        RingHom.id ℂ := by
    unfold UpperHalfPlane.σ; rw [if_pos h_M_det_pos]
  rw [hσ_M, σ_levelRaiseMatrix (d / p)]
  simp only [RingHom.id_apply]
  -- Möbius equality M • z = LR (d/p) • z.
  rw [T_p_upper_zero_mul_levelRaise_smul_eq hp hpd z]
  -- det/denom rewriting via existing helpers.
  have hdetM_abs : |(((glMap (T_p_upper p hp 0) : GL (Fin 2) ℝ) *
      levelRaiseMatrix d).det.val)| = (p : ℝ) * (d : ℝ) := by
    rw [T_p_upper_zero_mul_levelRaise_det p d hp]
    exact abs_of_pos
      (mul_pos (Nat.cast_pos.mpr hp) (Nat.cast_pos.mpr (NeZero.pos d)))
  rw [hdetM_abs, T_p_upper_zero_mul_levelRaise_denom p d hp z,
      abs_levelRaiseMatrix_det_val (d / p),
      denom_levelRaiseMatrix (d / p) z]
  -- After rewrites, both sides are at the same `f (LR (d/p) • z)` factor, with
  -- scalar factors:
  --   LHS: f(...) * ((p:ℝ)*(d:ℝ) : ℂ)^(k-1) * (p:ℂ)^(-k)
  --   RHS: (p:ℂ)^(k-2) * (f(...) * ((d/p:ℕ:ℝ) : ℂ)^(k-1) * 1^(-k))
  -- Simplify 1^(-k) = 1.
  rw [one_zpow, mul_one]
  -- The remaining scalar arithmetic is `T_p_zero_levelRaise_scalar_collapse`.
  exact T_p_zero_levelRaise_scalar_collapse hp hpd _

/-- **T171 — final scalar identity for the `p ∣ d` collapse.**

The closing ℂ-arithmetic step of the collapse identity: with `p ∣ d` and `p ≠ 0`
(so `d = p · (d/p)`), the accumulated `p · (d^{1-k} · (p^{k-2} · h))` reduces to
`(d/p)^{1-k} · h`, because `p · p^{1-k} · p^{k-2} = p^0 = 1`. -/
private lemma T_p_divN_collapse_final_scalar
    {p d : ℕ} (hp : 0 < p) (hpd : p ∣ d) (h : ℂ) :
    (p : ℂ) * ((d : ℂ) ^ (1 - k) * ((p : ℂ) ^ (k - 2) * h)) =
      ((d / p : ℕ) : ℂ) ^ (1 - k) * h := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hdC : (d : ℂ) = (p : ℂ) * ((d / p : ℕ) : ℂ) := by
    rw [show (d : ℂ) = ((p * (d / p) : ℕ) : ℂ) by rw [Nat.mul_div_cancel' hpd]]
    push_cast; ring
  have hp_exp : (p : ℂ) * (p : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 2) = 1 := by
    rw [mul_assoc, ← zpow_add₀ hpC, show ((1 - k) + (k - 2) : ℤ) = -1 from by ring,
      zpow_neg_one]
    exact mul_inv_cancel₀ hpC
  rw [hdC, mul_zpow,
    show (p : ℂ) * (((p : ℂ) ^ (1 - k) * ((d / p : ℕ) : ℂ) ^ (1 - k)) *
        ((p : ℂ) ^ (k - 2) * h)) =
      ((p : ℂ) * (p : ℂ) ^ (1 - k) * (p : ℂ) ^ (k - 2)) *
        (((d / p : ℕ) : ℂ) ^ (1 - k) * h) from by ring,
    hp_exp, one_mul]

/-- **T171 — `p ∣ d` collapse identity (proof of `HasHeckeT_p_divN_LR_d_collapse_identity`).**

For `p` prime with `p ∣ N` (bad prime), `d * M = N`, and `p ∣ d`, the function-level
identity holds:
```
heckeT_n_cusp k p (LR_d g) τ = levelRaiseFun (d/p) k g τ.
```

**Proof structure** (mirrors `heckeT_p_all_levelRaise_comm_divN` template):
1. Unfold `heckeT_n_cusp` via `heckeT_n_prime` → `heckeT_p_all_not_coprime_apply` → `heckeT_p_ut`.
2. Per-summand: `(g ∣[k] α_d) ∣[k] T_p_upper b = (g ∣[k] T_p_upper(d·b)) ∣[k] α_d` via
   `levelRaise_mul_T_p_upper`.
3. `slash_T_p_upper_mod` → `g ∣[k] T_p_upper(d·b mod p) = g ∣[k] T_p_upper(0)` (since `p ∣ d`).
4. `slash_T_p_upper_zero_mul_levelRaise_apply` collapses the matrix product to
   `(p:ℂ)^(k-2) · (g ∣[k] α_(d/p))`.
5. Sum of `p` constant terms times scalar arithmetic recombines to `((d/p):ℂ)^(1-k)`.
-/
private theorem Newform.HasHeckeT_p_divN_LR_d_collapse_identity_proof
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_p_divN_LR_d_collapse_identity N k p hp hpN := by
  intro M d _ _ heq _hd hpd g z
  haveI : NeZero (d / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) hpd) hp.pos).ne'⟩
  subst heq
  have hpdM : ¬ Nat.Coprime p (d * M) := fun h =>
    hp.coprime_iff_not_dvd.mp h (dvd_mul_of_dvd_left hpd M)
  show (heckeT_n_cusp k p (levelRaise M d k g)).toFun z = levelRaiseFun (d / p) k ⇑g z
  show ((heckeT_n k p) (levelRaise M d k g).toModularForm').toFun z = _
  rw [heckeT_n_prime k hp]
  change ⇑((heckeT_p_all k p hp) ((levelRaise M d k) g).toModularForm') z = _
  rw [show ⇑((heckeT_p_all k p hp) ((levelRaise M d k) g).toModularForm') =
        heckeT_p_ut k p hp.pos (⇑((levelRaise M d k) g).toModularForm') from
      heckeT_p_all_not_coprime_apply k hp hpdM _]
  show heckeT_p_ut k p hp.pos (⇑((levelRaise M d k) g).toModularForm') z = _
  -- Rewrite the level-raised upper-triangular sum via `heckeT_p_ut_levelRaise`,
  -- then collapse the index since `p ∣ d` forces `d * b % p = 0`.
  rw [heckeT_p_ut_levelRaise p hp M d g]
  simp only [Finset.sum_apply]
  simp_rw [mul_mod_eq_zero_of_dvd hp.pos hpd]
  simp_rw [show (⇑g.toModularForm' ∣[k] (T_p_upper p hp.pos 0 : GL (Fin 2) ℚ))
      ∣[k] levelRaiseMatrix d =
    ⇑g.toModularForm' ∣[k]
      (glMap (T_p_upper p hp.pos 0) * levelRaiseMatrix d) from
    show (⇑g.toModularForm' ∣[k] glMap (T_p_upper p hp.pos 0))
      ∣[k] levelRaiseMatrix d = _ from (SlashAction.slash_mul k _ _ _).symm]
  simp_rw [Pi.smul_apply, smul_eq_mul]
  simp_rw [slash_T_p_upper_zero_mul_levelRaise_apply (k := k) hp.pos hpd
    ⇑g.toModularForm']
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- Final ℂ-arithmetic via `T_p_divN_collapse_final_scalar`.  The `show` performs the
  -- rfl-defeq conversions: `levelRaiseFun` unfold, `Pi.smul_apply`, `⇑g.toModularForm' = ⇑g`.
  show ((p : ℕ) : ℂ) * ((d : ℂ) ^ (1 - k) *
      ((p : ℂ) ^ (k - 2) *
        (⇑g ∣[k] (levelRaiseMatrix (d / p) : GL (Fin 2) ℝ)) z)) =
    ((d / p : ℕ) : ℂ) ^ (1 - k) *
      (⇑g ∣[k] levelRaiseMatrix (d / p)) z
  exact T_p_divN_collapse_final_scalar hp.pos hpd _

/-- **T171 — `p ∣ d` extended-oldspace preservation theorem (proof of
`HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended`).**

Composes the function-level collapse identity
`HasHeckeT_p_divN_LR_d_collapse_identity_proof` with the trivial-inclusion
membership lemma `levelInclude_cusp_mem_cuspFormsOldExtended`.

For `p ∣ d` with `1 < d, d * M = N`, the bad-prime Hecke operator on
`LR_d g` lands as `levelInclude_cusp ((d/p)*M ∣ d*M) (LR_{d/p} g)`,
which is in the extended oldspace via the trivial-inclusion summand. -/
theorem Newform.HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended_proof
    {p : ℕ} [NeZero p] (hp : Nat.Prime p) (hpN : ¬ Nat.Coprime p N) :
    Newform.HasHeckeT_p_divN_LRpd_in_cuspFormsOldExtended N k p hp hpN := by
  intro M d _ _ heq _hd hpd g
  haveI : NeZero (d / p) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos d) hpd) hp.pos).ne'⟩
  subst heq
  have hQM_dvd : (d / p) * M ∣ d * M := ⟨p, by
    rw [mul_assoc, mul_comm M p, ← mul_assoc, Nat.div_mul_cancel hpd]⟩
  have hQM_lt : (d / p) * M < d * M := by
    have hd_lt : d / p < d := Nat.div_lt_self (NeZero.pos d) hp.one_lt
    exact Nat.mul_lt_mul_of_pos_right hd_lt (NeZero.pos M)
  -- heckeT_n_cusp k p (LR_d g) = levelInclude_cusp ((d/p)*M ∣ d*M) (LR_{d/p} g)
  -- via CuspForm.ext + collapse identity.
  have h_eq : heckeT_n_cusp k p (levelRaise M d k g) =
      levelInclude_cusp hQM_dvd k (levelRaise M (d / p) k g) := by
    apply CuspForm.ext
    intro z
    -- Convert FunLike `f z` to explicit `f.toFun z` for collapse identity rw.
    show (heckeT_n_cusp k p (levelRaise M d k g)).toFun z = _
    rw [Newform.HasHeckeT_p_divN_LR_d_collapse_identity_proof hp hpN
      M d rfl _hd hpd g z]
    rfl
  rw [h_eq]
  exact levelInclude_cusp_mem_cuspFormsOldExtended hQM_dvd hQM_lt _

/-- **CuspForm-level multiplicative decomposition.**  A `Module.End`-level
factorisation `T_m = T_a ∘ T_b` of the Hecke operator transfers to the
function level: `T_m f = T_a (T_b f)` for every cusp form `f`. -/
private lemma heckeT_n_cusp_decomp_of_mul
    {L : ℕ} [NeZero L] (k : ℤ) (a b m : ℕ) [NeZero a] [NeZero b] [NeZero m]
    (h_mul : heckeT_n (N := L) k m = heckeT_n k a * heckeT_n k b)
    (f : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) :
    heckeT_n_cusp k m f = heckeT_n_cusp k a (heckeT_n_cusp k b f) := by
  apply CuspForm.ext; intro z
  show ((heckeT_n (N := L) k m) f.toModularForm').toFun z =
    ((heckeT_n k a) ((heckeT_n k b) f.toModularForm')).toFun z
  simp only [ModularForm.toFun_eq_coe]; rw [h_mul]; rfl

/-- **CuspForm-level prime-power recurrence `T_{p^{r+2}}`.**  The Hecke
recurrence `T_{p^{r+2}} = T_p T_{p^{r+1}} - p^{k-1} ⟨p⟩ T_{p^r}` (from
`heckeT_ppow_succ_succ`) at the function level, with the diamond identified
via `diamondOp_ext_coprime`. -/
private lemma heckeT_n_cusp_ppow_succ_succ
    {L : ℕ} [NeZero L] (k : ℤ) {p : ℕ} (hp : Nat.Prime p) (hpL : Nat.Coprime p L)
    (r : ℕ) (f : CuspForm ((Gamma1 L).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
    haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp k (p ^ (r + 2)) f =
      heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) f) -
        ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpL)
          (heckeT_n_cusp k (p ^ r) f) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  apply CuspForm.ext; intro z
  show ((heckeT_n (N := L) k (p ^ (r + 2))) f.toModularForm').toFun z = _
  rw [heckeT_n_prime_pow k hp (r + 2) (by omega), heckeT_ppow_succ_succ k p hp r]
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    ModularForm.toFun_eq_coe, ModularForm.coe_sub, Pi.sub_apply]
  congr 1
  · show (heckeT_p_all (N := L) k p hp
      (heckeT_ppow k p hp (r + 1) f.toModularForm')).toFun z =
      ((heckeT_n k p) ((heckeT_n k (p ^ (r + 1))) f.toModularForm')).toFun z
    rw [← heckeT_n_prime k hp, ← heckeT_n_prime_pow k hp (r + 1) (by omega)]
  · have key : (diamondOp_ext k p) ((heckeT_ppow k p hp r) f.toModularForm') =
        (diamondOp k (ZMod.unitOfCoprime p hpL))
          ((heckeT_n (N := L) k (p ^ r)) f.toModularForm') := by
      rw [diamondOp_ext_coprime k hpL]
      cases r with
      | zero => simp [heckeT_ppow_zero, heckeT_n_one]
      | succ r => rw [← heckeT_n_prime_pow k hp (r + 1) (by omega)]
    rw [show diamondOp_ext k p * heckeT_ppow k p hp r =
      (diamondOp_ext k p).comp (heckeT_ppow k p hp r) from rfl] at *
    simp only [LinearMap.comp_apply] at *
    rw [key]; rfl

/-- **Prime-power inductive step for level-raise commutation.**  Assuming the
commutation `T_q (LR g) = LR (T_q g)` already holds for `q ∈ {p, p^{r+1}, p^r}`,
the recurrence (`heckeT_n_cusp_ppow_succ_succ`) plus the diamond/level-raise
commutation (`diamondOp_levelRaise_eq`) gives it for `q = p^{r+2}`. -/
private lemma heckeT_ppow_levelRaise_comm_step
    (M d : ℕ) [NeZero M] [NeZero d] {p : ℕ} (hp : Nat.Prime p)
    (hpM : Nat.Coprime p M) (hpdM : Nat.Coprime p (d * M)) (r : ℕ)
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k)
    (ih_p : haveI : NeZero p := ⟨hp.ne_zero⟩
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      heckeT_n_cusp k p (levelRaise M d k f) = levelRaise M d k (heckeT_n_cusp k p f))
    (ih_pv1 : haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      heckeT_n_cusp k (p ^ (r + 1)) (levelRaise M d k f) =
        levelRaise M d k (heckeT_n_cusp k (p ^ (r + 1)) f))
    (ih_pr : haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
      ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
      heckeT_n_cusp k (p ^ r) (levelRaise M d k f) =
        levelRaise M d k (heckeT_n_cusp k (p ^ r) f)) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp (N := d * M) k (p ^ (r + 2)) (levelRaise M d k g') =
      levelRaise M d k (heckeT_n_cusp (N := M) k (p ^ (r + 2)) g') := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ (r + 1)) := ⟨(pow_pos hp.pos _).ne'⟩
  haveI : NeZero (p ^ r) := ⟨(pow_pos hp.pos _).ne'⟩
  have h_units_eq : ZMod.unitsMap (Nat.dvd_mul_left M d)
      (ZMod.unitOfCoprime p hpdM) = ZMod.unitOfCoprime p hpM := by
    ext; simp [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime]
  have ih_dia : ∀ f, diamondOp_cusp k (ZMod.unitOfCoprime p hpdM) (levelRaise M d k f) =
      levelRaise M d k (diamondOp_cusp k (ZMod.unitOfCoprime p hpM) f) := by
    intro f
    have h := diamondOp_levelRaise_eq (ZMod.unitOfCoprime p hpdM) M d rfl f
    rw [h, h_units_eq]; rfl
  calc heckeT_n_cusp k (p ^ (r + 2)) (levelRaise M d k g')
      = heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) (levelRaise M d k g')) -
          ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpdM)
            (heckeT_n_cusp k (p ^ r) (levelRaise M d k g')) :=
        heckeT_n_cusp_ppow_succ_succ k hp hpdM r (levelRaise M d k g')
    _ = heckeT_n_cusp k p (levelRaise M d k (heckeT_n_cusp k (p ^ (r + 1)) g')) -
          ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpdM)
            (levelRaise M d k (heckeT_n_cusp k (p ^ r) g')) := by
        rw [ih_pv1 g', ih_pr g']
    _ = levelRaise M d k (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g')) -
          ((↑p : ℂ) ^ (k - 1)) • levelRaise M d k (diamondOp_cusp k
            (ZMod.unitOfCoprime p hpM) (heckeT_n_cusp k (p ^ r) g')) := by
        rw [ih_p (heckeT_n_cusp k (p ^ (r + 1)) g'), ih_dia (heckeT_n_cusp k (p ^ r) g')]
    _ = levelRaise M d k (heckeT_n_cusp k p (heckeT_n_cusp k (p ^ (r + 1)) g') -
          ((↑p : ℂ) ^ (k - 1)) • diamondOp_cusp k (ZMod.unitOfCoprime p hpM)
            (heckeT_n_cusp k (p ^ r) g')) := by
        rw [← (levelRaise M d k).map_smul, ← (levelRaise M d k).map_sub]
    _ = levelRaise M d k (heckeT_n_cusp k (p ^ (r + 2)) g') := by
        rw [heckeT_n_cusp_ppow_succ_succ k hp hpM r g']

/-- **Prime-power case `m = p^{r+2}` of the level-raise commutation step.**
Discharges the IH size bounds (`p, p^{r+1}, p^r < p^{r+2}`) and feeds the three
resulting commutations to `heckeT_ppow_levelRaise_comm_step`. -/
private lemma heckeT_n_levelRaise_comm_ppow_case
    (M d : ℕ) [NeZero M] [NeZero d] {p : ℕ} (hp : Nat.Prime p) (r : ℕ)
    (hpcop : Nat.Coprime p (d * M))
    (ih : haveI : NeZero p := ⟨hp.ne_zero⟩
        ∀ m' < p ^ (r + 2), ∀ (_ : 0 < m'), Nat.Coprime m' (d * M) →
        ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
          haveI : NeZero m' := ⟨‹0 < m'›.ne'⟩
          heckeT_n_cusp k m' (levelRaise M d k f) =
            levelRaise M d k (heckeT_n_cusp k m' f))
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero p := ⟨hp.ne_zero⟩
    haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hp.pos _).ne'⟩
    heckeT_n_cusp k (p ^ (r + 2)) (levelRaise M d k g') =
      levelRaise M d k (heckeT_n_cusp k (p ^ (r + 2)) g') := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hp_lt : p < p ^ (r + 2) := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpv1_lt : p ^ (r + 1) < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hpr_lt : p ^ r < p ^ (r + 2) := Nat.pow_lt_pow_right hp.one_lt (by omega)
  exact heckeT_ppow_levelRaise_comm_step M d hp
    (hpcop.coprime_dvd_right (dvd_mul_left M d)) hpcop r g'
    (fun f => ih p hp_lt hp.pos hpcop f)
    (fun f => ih (p ^ (r + 1)) hpv1_lt (pow_pos hp.pos _) (hpcop.pow_left _) f)
    (fun f => ih (p ^ r) hpr_lt (pow_pos hp.pos _) (hpcop.pow_left _) f)

/-- **`m > 1` inductive step for `heckeT_n_levelRaise_comm`.**  Splits `m` by
its largest prime-power factor `p^v ‖ m`.  If `p^v < m`, `T_m = T_{p^v} T_{m/p^v}`
factors and the IH applies to both; if `p^v = m`, the prime case
(`heckeT_p_all_levelRaise_comm`, `v = 1`) or the recurrence step
(`heckeT_n_levelRaise_comm_ppow_case`, `v ≥ 2`) closes the goal. -/
private lemma heckeT_n_levelRaise_comm_step
    (M d : ℕ) [NeZero M] [NeZero d] (m : ℕ) (hle : 1 < m)
    (hcop : Nat.Coprime m (d * M))
    (ih : ∀ m' < m, ∀ (_ : 0 < m'), Nat.Coprime m' (d * M) →
        ∀ f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
          haveI : NeZero m' := ⟨‹0 < m'›.ne'⟩
          heckeT_n_cusp k m' (levelRaise M d k f) =
            levelRaise M d k (heckeT_n_cusp k m' f))
    (g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    haveI : NeZero m := ⟨(by omega : 0 < m).ne'⟩
    heckeT_n_cusp k m (levelRaise M d k g') =
      levelRaise M d k (heckeT_n_cusp k m g') := by
  haveI : NeZero m := ⟨(by omega : 0 < m).ne'⟩
  set p := m.minFac with hp_def
  have hpp : p.Prime := Nat.minFac_prime (by omega : m ≠ 1)
  set v := m.factorization p with hv_def
  have hv_pos : 0 < v := hpp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
  have hdiv_pos : 0 < m / p ^ v :=
    Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (pow_pos hpp.pos v)
  have hdiv_lt : m / p ^ v < m := heckeT_n_unfold_lt m hle
  have hpcop : Nat.Coprime p (d * M) := Nat.Coprime.coprime_dvd_left (Nat.minFac_dvd m) hcop
  have hdiv_cop : Nat.Coprime (m / p ^ v) (d * M) :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.ordProj_dvd m p)) hcop
  have hpv_cop : Nat.Coprime (p ^ v) (d * M) := Nat.Coprime.pow_left v hpcop
  have hpv_pos : 0 < p ^ v := pow_pos hpp.pos v
  haveI : NeZero (p ^ v) := ⟨hpv_pos.ne'⟩
  haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
  by_cases hpv_lt : p ^ v < m
  · -- Case 1: m not a prime power. T_m = T_{p^v} ∘ T_{m/p^v}, IH on both factors.
    have hDecomp : ∀ {L : ℕ} [NeZero L] (f : CuspForm ((Gamma1 L).map (mapGL ℝ)) k),
        heckeT_n_cusp k m f = heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) f) :=
      fun {L} _ f => heckeT_n_cusp_decomp_of_mul k (p ^ v) (m / p ^ v) m
        (heckeT_n_mul_ppow_quot (N := L) (k := k) m hle p hpp rfl v rfl hv_pos hdiv_pos) f
    rw [hDecomp, ih (m / p ^ v) hdiv_lt hdiv_pos hdiv_cop g',
      ih (p ^ v) hpv_lt hpv_pos hpv_cop (heckeT_n_cusp k (m / p ^ v) g')]
    congr 1; exact (hDecomp g').symm
  · have hpv_eq : p ^ v = m := le_antisymm
      (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m p)) (not_lt.mp hpv_lt)
    by_cases hv1 : v = 1
    · -- Case 2a: m = p prime.
      have hpp_m : Nat.Prime m := by
        have := hpv_eq; rw [hv1, pow_one] at this; rwa [← this]
      exact heckeT_p_all_levelRaise_comm m hpp_m hcop M d rfl g'
    · -- Case 2b: m = p^v with v ≥ 2; reduce to `heckeT_n_levelRaise_comm_ppow_case`.
      obtain ⟨r, hr⟩ : ∃ r, v = r + 2 := ⟨v - 2, by omega⟩
      haveI : NeZero p := ⟨hpp.ne_zero⟩
      haveI : NeZero (p ^ (r + 2)) := ⟨(pow_pos hpp.pos _).ne'⟩
      have hm_eq : m = p ^ (r + 2) := by rw [← hpv_eq, hr]
      calc heckeT_n_cusp k m (levelRaise M d k g')
          = heckeT_n_cusp k (p ^ (r + 2)) (levelRaise M d k g') := by simp only [hm_eq]
        _ = levelRaise M d k (heckeT_n_cusp k (p ^ (r + 2)) g') :=
            heckeT_n_levelRaise_comm_ppow_case M d hpp r hpcop (hm_eq ▸ ih) g'
        _ = levelRaise M d k (heckeT_n_cusp k m g') := by simp only [hm_eq]

/-- The commutation `T_n (LR g) = LR (T_n g)` for general coprime n.
Proved by strong induction on `n` (`heckeT_n_levelRaise_comm_step` is the
`n > 1` step); the prime case uses `heckeT_p_all_levelRaise_comm`, prime
powers the recurrence, and composite `n` the multiplicative factorisation. -/
lemma heckeT_n_levelRaise_comm
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (heq ▸ levelRaise M d k g) =
      heq ▸ levelRaise M d k (heckeT_n_cusp k n g) := by
  subst heq
  -- Strong induction on `n`, strengthened over all cusp forms `g'`; the
  -- `m > 1` step is `heckeT_n_levelRaise_comm_step`.
  suffices h : ∀ m : ℕ, (hm : 0 < m) → Nat.Coprime m (d * M) →
      ∀ g' : CuspForm ((Gamma1 M).map (mapGL ℝ)) k,
        haveI : NeZero m := ⟨hm.ne'⟩
        heckeT_n_cusp k m (levelRaise M d k g') =
          levelRaise M d k (heckeT_n_cusp k m g') from
    h n (NeZero.pos n) hn g
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hcop g'
    haveI : NeZero m := ⟨hm.ne'⟩
    by_cases hle : 1 < m
    · exact heckeT_n_levelRaise_comm_step M d m hle hcop ih g'
    · -- m = 1: T_1 = id, so both sides are `LR g'`.
      obtain rfl : m = 1 := by omega
      have hid : ∀ (f : CuspForm ((Gamma1 (d * M)).map (mapGL ℝ)) k),
          heckeT_n_cusp k 1 f = f := fun f => by
        apply CuspForm.ext; intro w
        show (heckeT_n k 1 f.toModularForm').toFun w = f w
        rw [heckeT_n_one]; rfl
      have hid_M : ∀ (f : CuspForm ((Gamma1 M).map (mapGL ℝ)) k),
          heckeT_n_cusp k 1 f = f := fun f => by
        apply CuspForm.ext; intro w
        show (heckeT_n k 1 f.toModularForm').toFun w = f w
        rw [heckeT_n_one]; rfl
      rw [hid, hid_M]

/-- **Generator step for `T_n` stability**: `T_n(ι_d g) ∈ cuspFormsOld`.
Follows immediately from `heckeT_n_levelRaise_comm`. -/
private lemma heckeT_n_levelRaise_mem (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (hd : 1 < d) (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    heckeT_n_cusp k n (heq ▸ levelRaise M d k g) ∈ cuspFormsOld N k := by
  rw [heckeT_n_levelRaise_comm n hn M d heq g]
  exact Submodule.subset_span ⟨M, d, _, _, hd, heq, _, rfl⟩

/-- **Generator step for `⟨d⟩` stability**: Diamond operators preserve oldform
generators. Follows immediately from `diamondOp_levelRaise_eq`. -/
private lemma diamondOp_levelRaise_mem (a : (ZMod N)ˣ)
    (M : ℕ) (d : ℕ) [NeZero M] [NeZero d] (hd : 1 < d) (heq : d * M = N)
    (g : CuspForm ((Gamma1 M).map (mapGL ℝ)) k) :
    diamondOp_cusp k a (heq ▸ levelRaise M d k g) ∈ cuspFormsOld N k := by
  subst heq
  rw [diamondOp_levelRaise_eq a M d rfl g]
  exact Submodule.subset_span ⟨M, d, _, _, hd, rfl, _, rfl⟩

/-- The oldform subspace is stable under all Hecke operators `T_n` for `(n, N) = 1`. -/
theorem heckeT_n_preserves_cuspFormsOld
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsOld N k) :
    heckeT_n_cusp k n f ∈ cuspFormsOld N k := by
  refine Submodule.span_induction
    (p := fun x _ => heckeT_n_cusp k n x ∈ cuspFormsOld N k)
    ?_ ?_ ?_ ?_ hf
  · -- generator case
    rintro f₀ ⟨M, d, _, _, hd, heq, g, rfl⟩
    exact heckeT_n_levelRaise_mem n hn M d hd heq g
  · -- zero
    show heckeT_n_cusp k n (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k
    rw [heckeT_n_cusp_zero]
    exact (cuspFormsOld N k).zero_mem
  · -- add
    intros f₁ f₂ _ _ ih₁ ih₂
    show heckeT_n_cusp k n (f₁ + f₂) ∈ cuspFormsOld N k
    rw [heckeT_n_cusp_add]
    exact (cuspFormsOld N k).add_mem ih₁ ih₂
  · -- smul
    intros c f₁ _ ih
    show heckeT_n_cusp k n (c • f₁) ∈ cuspFormsOld N k
    rw [heckeT_n_cusp_smul]
    exact (cuspFormsOld N k).smul_mem c ih

/-- Diamond operators preserve the oldform subspace. -/
theorem diamondOp_preserves_cuspFormsOld
    (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsOld N k) :
    diamondOp_cusp k d f ∈ cuspFormsOld N k := by
  refine Submodule.span_induction
    (p := fun x _ => diamondOp_cusp k d x ∈ cuspFormsOld N k)
    ?_ ?_ ?_ ?_ hf
  · -- generator case
    rintro f₀ ⟨M, d', _, _, hd', heq, g, rfl⟩
    exact diamondOp_levelRaise_mem d M d' hd' heq g
  · -- zero
    show diamondOp_cusp k d (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k
    rw [diamondOp_cusp_zero]
    exact (cuspFormsOld N k).zero_mem
  · -- add
    intros f₁ f₂ _ _ ih₁ ih₂
    show diamondOp_cusp k d (f₁ + f₂) ∈ cuspFormsOld N k
    rw [diamondOp_cusp_add]
    exact (cuspFormsOld N k).add_mem ih₁ ih₂
  · -- smul
    intros c f₁ _ ih
    show diamondOp_cusp k d (c • f₁) ∈ cuspFormsOld N k
    rw [diamondOp_cusp_smul]
    exact (cuspFormsOld N k).smul_mem c ih

/-- The newform subspace is stable under all Hecke operators `T_n` for `(n, N) = 1`.

Proof: For `f ∈ S_k^new` and `g ∈ S_k^old`, by the adjoint formula
`heckeT_n_adjoint`, `petN (T_n f) g = petN f (⟨n⟩⁻¹ T_n g)`. Since `T_n` and
`⟨n⟩⁻¹` both preserve `S_k^old`, we have `⟨n⟩⁻¹ (T_n g) ∈ S_k^old`, hence
`petN f (⟨n⟩⁻¹ T_n g) = 0`. -/
theorem heckeT_n_preserves_cuspFormsNew
    (n : ℕ) [NeZero n] (hn : Nat.Coprime n N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    heckeT_n_cusp k n f ∈ cuspFormsNew N k := by
  intro g hg
  -- petN (T_n f) g = petN f (⟨n⟩⁻¹ (T_n g))  by heckeT_n_adjoint
  rw [heckeT_n_adjoint n hn f g]
  -- ⟨n⟩⁻¹ (T_n g) ∈ cuspFormsOld since both T_n and ⟨n⟩⁻¹ preserve cuspFormsOld
  exact hf _ (diamondOp_preserves_cuspFormsOld _ _
    (heckeT_n_preserves_cuspFormsOld n hn g hg))

/-- Diamond operators preserve the newform subspace.

Proof: Diamond operators are unitary (`diamondOp_petersson_unitary`), so they
preserve the orthogonal complement of any stable subspace. Equivalently, the
inverse of a diamond operator is again a diamond operator (which preserves
oldforms), so by the unitarity argument the original preserves newforms. -/
theorem diamondOp_preserves_cuspFormsNew
    (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (hf : f ∈ cuspFormsNew N k) :
    diamondOp_cusp k d f ∈ cuspFormsNew N k := by
  intro g hg
  -- petN (⟨d⟩f) g = ?  Use that ⟨d⟩ is unitary: petN (⟨d⟩f) (⟨d⟩(⟨d⟩⁻¹ g)) = petN f (⟨d⟩⁻¹ g)
  -- Then ⟨d⟩⁻¹ g ∈ cuspFormsOld (since diamond preserves old), so petN f (⟨d⟩⁻¹ g) = 0
  have hgg : diamondOp_cusp k d (diamondOp_cusp k d⁻¹ g) = g := by
    -- ⟨d⟩ (⟨d⁻¹⟩ g) = (⟨d⟩ ∘ ⟨d⁻¹⟩) g = ⟨d * d⁻¹⟩ g = ⟨1⟩ g = g
    show diamondOpCusp k d (diamondOpCusp k d⁻¹ g) = g
    rw [show (diamondOpCusp k d (diamondOpCusp k d⁻¹ g)) =
        ((diamondOpCusp k d).comp (diamondOpCusp k d⁻¹)) g from rfl,
      ← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
    rfl
  have hg' : diamondOp_cusp k d⁻¹ g ∈ cuspFormsOld N k :=
    diamondOp_preserves_cuspFormsOld _ _ hg
  rw [← hgg, diamondOp_petersson_unitary]
  exact hf _ hg'


end HeckeRing.GL2
