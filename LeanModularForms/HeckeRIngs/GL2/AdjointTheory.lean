/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanModularForms contributors
-/
import LeanModularForms.HeckeRIngs.GL2.FourierHecke
import LeanModularForms.HeckeRIngs.GL2.HeckeT_p_Gamma1
import LeanModularForms.Modularforms.PeterssonInner
import LeanModularForms.Modularforms.PeterssonLevelN
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.Semisimple

/-!
# Hecke adjoint theory: core cusp/Hecke infrastructure

This file provides the foundational infrastructure for the adjoint theory of
Hecke operators with respect to the Petersson inner product: the cusp-form
Hecke operators, the cuspidality-preservation API, the algebraic double-coset
identity, and the GL₂⁺ change-of-variables lemma `peterssonInner_slash_adjoint`.

The long Petersson development (the T090/T024/T128/T205 double-coset tile
calculation) and the eigenform diagonalization built on top of it live in the
downstream module `LeanModularForms.HeckeRIngs.GL2.AdjointTheoryPetersson`,
including `heckeT_p_adjoint`, `diamondOp_petersson_unitary`, `heckeT_n_normal`
and `exists_simultaneous_eigenform_basis`.

## Main results

* `heckeT_n_cusp` — the Hecke operator `T_n` on cusp forms
* `PreservesCusps` — the cuspidality-preservation predicate and its API
* `adjointGamma0Rep` / `peterssonAdj` — adjoint representatives for the change of
  variables
* `peterssonInner_slash_adjoint` — DS Proposition 5.5.2, GL₂⁺ change of variables

## References

* [DS] Diamond–Shurman, *A First Course in Modular Forms*, §5.5
* [Miy] Miyake, *Modular Forms*, §4.5 (Thm 4.5.4–4.5.5)
-/

noncomputable section

open CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped Pointwise MatrixGroups ModularForm

variable {k : ℤ}

/-! ### CuspForm ↪ ModularForm coercion

In Mathlib, `CuspForm` and `ModularForm` are parallel structures over
`SlashInvariantForm`. A cusp form is also a modular form since
`IsZeroAt → IsBoundedAt`. -/

namespace CuspForm

/-- Every cusp form is a modular form (zero at cusps implies bounded at cusps). -/
def toModularForm' {Γ : Subgroup (GL (Fin 2) ℝ)}
    (f : CuspForm Γ k) : ModularForm Γ k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc g hg := (f.zero_at_cusps' hc g hg).boundedAtFilter

end CuspForm

namespace HeckeRing.GL2

open CuspForm

variable {N : ℕ} [NeZero N]

/-! ### Hecke operators on cusp forms

The Hecke operators preserve cuspidality — `IsZeroAt` is preserved by
the coset-sum construction. -/

private lemma Gamma1_isCusp_glMap_smul' (A : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    IsCusp (glMap A • c) ((Gamma1 N).map (mapGL ℝ)) := by
  have hc_SL : IsCusp c ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) :=
    hc.mono (Subgroup.map_mono le_top)
  rw [← MonoidHom.range_eq_map] at hc_SL
  have hsmul_SL : IsCusp (glMap A • c) (mapGL ℝ : SL(2, ℤ) →* _).range := by
    rw [isCusp_SL2Z_iff] at hc_SL ⊢
    obtain ⟨q, rfl⟩ := hc_SL
    refine ⟨A • q, ?_⟩
    show OnePoint.map (algebraMap ℚ ℝ) (A • q) =
      glMap A • OnePoint.map (algebraMap ℚ ℝ) q
    simp [OnePoint.map_smul, glMap]
  rw [MonoidHom.range_eq_map] at hsmul_SL
  haveI : ((Gamma1 N).map (mapGL ℝ)).IsFiniteRelIndex
      ((⊤ : Subgroup SL(2, ℤ)).map (mapGL ℝ)) := ⟨by
    rw [Subgroup.relIndex_map_map_of_injective _ _ mapGL_injective,
        Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero⟩
  exact hsmul_SL.of_isFiniteRelIndex

/-- `T_p` preserves cuspidality. -/
theorem heckeT_p_zero_at_cusps (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsZeroAt (heckeT_p k p hp hpN f.toModularForm').toFun k := by
  show c.IsZeroAt (heckeT_p_fun k p hp hpN f.toModularForm') k
  simp only [heckeT_p_fun, heckeT_p_ut]
  apply OnePoint.IsZeroAt.add
  · apply Finset.sum_induction _ (fun g ↦ c.IsZeroAt g k)
      (fun _ _ ha hb ↦ ha.add hb)
      ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc)
    intro b _
    exact OnePoint.IsZeroAt.smul_iff.mp
      (f.zero_at_cusps' (Gamma1_isCusp_glMap_smul' _ hc))
  ·
    intro γ hγ
    show UpperHalfPlane.IsZeroAtImInfty
      ((⇑((diamondOp k (ZMod.unitOfCoprime p hpN)) f.toModularForm') ∣[k]
        glMap (T_p_lower p hp.pos)) ∣[k] γ)
    rw [← SlashAction.slash_mul]
    set g := (Gamma0MapUnits_surjective (ZMod.unitOfCoprime p hpN)).choose
    change UpperHalfPlane.IsZeroAtImInfty
      ((⇑f.toModularForm' ∣[k] mapGL ℝ (g : SL(2, ℤ))) ∣[k]
        (glMap (T_p_lower p hp.pos) * γ))
    rw [← SlashAction.slash_mul]
    have hc_lower : IsCusp (glMap (T_p_lower p hp.pos) • c)
        ((Gamma1 N).map (mapGL ℝ)) := Gamma1_isCusp_glMap_smul' _ hc
    have hconj : ConjAct.toConjAct (mapGL ℝ (g : SL(2, ℤ))) •
        (Gamma1 N).map (mapGL ℝ) = (Gamma1 N).map (mapGL ℝ) := by
      have := Gamma1_map_conjAct_eq ⟨(g : SL(2, ℤ))⁻¹, (Gamma0 N).inv_mem g.property⟩
      simpa [map_inv, ConjAct.toConjAct_inv, inv_inv, inv_smul_eq_iff] using this
    have hcusp : IsCusp (mapGL ℝ (g : SL(2, ℤ)) • glMap (T_p_lower p hp.pos) • c)
        ((Gamma1 N).map (mapGL ℝ)) :=
      hconj ▸ hc_lower.smul (mapGL ℝ (g : SL(2, ℤ)))
    apply f.zero_at_cusps' hcusp
    have hmul : (mapGL ℝ (g : SL(2, ℤ)) * (glMap (T_p_lower p hp.pos) * γ)) •
        (OnePoint.infty : OnePoint ℝ) =
      mapGL ℝ (g : SL(2, ℤ)) • glMap (T_p_lower p hp.pos) • c := by
      simp [SemigroupAction.mul_smul, hγ]
    exact hmul

/-- `T_p` restricted to cusp forms. -/
def heckeT_p_cusp (k : ℤ) (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toSlashInvariantForm := (heckeT_p k p hp hpN f.toModularForm').toSlashInvariantForm
  holo' := (heckeT_p k p hp hpN f.toModularForm').holo'
  zero_at_cusps' := heckeT_p_zero_at_cusps p hp hpN f

/-- `⟨d⟩` restricted to cusp forms. -/
def diamondOp_cusp (k : ℤ) (d : (ZMod N)ˣ)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  diamondOpCusp k d f

private theorem heckeT_p_all_zero_at_cusps (p : ℕ) (hp : Nat.Prime p)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    {c : OnePoint ℝ} (hc : IsCusp c ((Gamma1 N).map (mapGL ℝ))) :
    c.IsZeroAt ((heckeT_p_all k p hp) f.toModularForm').toFun k := by
  unfold heckeT_p_all
  split
  · exact heckeT_p_zero_at_cusps p hp ‹_› f hc
  · rename_i hpN
    show c.IsZeroAt (heckeT_p_ut k p hp.pos (⇑f.toModularForm')) k
    simp only [heckeT_p_ut]
    apply Finset.sum_induction _ (fun g ↦ c.IsZeroAt g k)
      (fun _ _ ha hb ↦ ha.add hb)
      ((0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc)
    intro b _
    exact OnePoint.IsZeroAt.smul_iff.mp
      (f.zero_at_cusps' (Gamma1_isCusp_glMap_smul' _ hc))

private def PreservesCusps (T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)) :
    Prop :=
  ∀ (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) {c : OnePoint ℝ},
    IsCusp c ((Gamma1 N).map (mapGL ℝ)) → c.IsZeroAt (T f.toModularForm').toFun k

omit [NeZero N] in
private theorem preservesCusps_one :
    PreservesCusps (N := N) (k := k) 1 :=
  fun f _ hc ↦ by simp; exact f.zero_at_cusps' hc

private theorem preservesCusps_heckeT_p_all (p : ℕ) (hp : Nat.Prime p) :
    PreservesCusps (N := N) (heckeT_p_all k p hp) :=
  fun f _ hc ↦ heckeT_p_all_zero_at_cusps p hp f hc

private theorem preservesCusps_diamondOp_ext (p : ℕ) :
    PreservesCusps (N := N) (diamondOp_ext k p) := by
  intro f c hc
  unfold diamondOp_ext
  split
  · exact (diamondOpCusp k (ZMod.unitOfCoprime p ‹_›) f).zero_at_cusps' hc
  · show c.IsZeroAt ((0 : ModularForm ((Gamma1 N).map (mapGL ℝ)) k).toFun) k
    exact (0 : CuspForm ((Gamma1 N).map (mapGL ℝ)) k).zero_at_cusps' hc

omit [NeZero N] in
private theorem preservesCusps_mul {T₁ T₂ : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (h₁ : PreservesCusps T₁) (h₂ : PreservesCusps T₂) :
    PreservesCusps (T₁ * T₂) := by
  intro f c hc
  show c.IsZeroAt (T₁ (T₂ f.toModularForm')).toFun k
  let g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := (T₂ f.toModularForm').toSlashInvariantForm
      holo' := (T₂ f.toModularForm').holo'
      zero_at_cusps' := h₂ f }
  exact h₁ g hc

omit [NeZero N] in
private theorem preservesCusps_sub {T₁ T₂ : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (h₁ : PreservesCusps T₁) (h₂ : PreservesCusps T₂) :
    PreservesCusps (T₁ - T₂) := by
  intro f c hc
  let g₁ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := (T₁ f.toModularForm').toSlashInvariantForm
      holo' := (T₁ f.toModularForm').holo'
      zero_at_cusps' := h₁ f }
  let g₂ : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
    { toSlashInvariantForm := (T₂ f.toModularForm').toSlashInvariantForm
      holo' := (T₂ f.toModularForm').holo'
      zero_at_cusps' := h₂ f }
  have hfun : ((T₁ - T₂) f.toModularForm').toFun = (g₁ - g₂).toFun := rfl
  rw [hfun]
  exact (g₁ - g₂).zero_at_cusps' hc

omit [NeZero N] in
private theorem preservesCusps_smul (a : ℂ) {T : Module.End ℂ (ModularForm ((Gamma1 N).map (mapGL ℝ)) k)}
    (hT : PreservesCusps T) :
    PreservesCusps (a • T) := by
  intro f c hc
  show c.IsZeroAt ((a • T f.toModularForm').toFun) k
  have hfun : (a • T f.toModularForm').toFun = a • (T f.toModularForm').toFun := by
    ext z; exact ModularForm.IsGLPos.smul_apply (T f.toModularForm') a z
  rw [hfun]
  intro g hg
  rw [ModularForm.smul_slash k g (T f.toModularForm').toFun a]
  exact (hT f hc g hg).smul (UpperHalfPlane.σ g a)

private theorem preservesCusps_heckeT_ppow (p : ℕ) (hp : Nat.Prime p) :
    ∀ r : ℕ, PreservesCusps (N := N) (heckeT_ppow k p hp r) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => exact preservesCusps_one
    | 1 => exact preservesCusps_heckeT_p_all p hp
    | r + 2 =>
      rw [heckeT_ppow_succ_succ]
      exact preservesCusps_sub
        (preservesCusps_mul (preservesCusps_heckeT_p_all p hp) (ih (r + 1) (by omega)))
        (preservesCusps_smul _ (preservesCusps_mul (preservesCusps_diamondOp_ext p)
          (ih r (by omega))))

private theorem preservesCusps_heckeT_n (n : ℕ) [NeZero n] :
    PreservesCusps (N := N) (k := k) (heckeT_n k n) := by
  show PreservesCusps (heckeT_n_aux k n)
  induction n using Nat.strong_induction_on with
  | _ m ih =>
    rw [heckeT_n_aux]
    split_ifs with hle
    · exact preservesCusps_one
    · push_neg at hle
      apply preservesCusps_mul (preservesCusps_heckeT_ppow m.minFac
        (Nat.minFac_prime (by omega)) _)
      exact ih _ (heckeT_n_unfold_lt m hle)

/-- `T_n` restricted to cusp forms. -/
def heckeT_n_cusp (k : ℤ) (n : ℕ) [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    CuspForm ((Gamma1 N).map (mapGL ℝ)) k where
  toSlashInvariantForm := (heckeT_n k n f.toModularForm').toSlashInvariantForm
  holo' := (heckeT_n k n f.toModularForm').holo'
  zero_at_cusps' := fun hc ↦ preservesCusps_heckeT_n n f hc

/-- Function-level decomposition for `heckeT_n_cusp`:
`T_m f = T_{p^v}(T_{m/p^v} f)` at each point. -/
theorem heckeT_n_cusp_unfold (m : ℕ) [NeZero m] (hm : 1 < m)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) (z : UpperHalfPlane) :
    let p := m.minFac
    let hp := Nat.minFac_prime (by omega : m ≠ 1)
    let v := m.factorization p
    have : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    have : NeZero (m / p ^ v) := ⟨(Nat.div_pos (Nat.le_of_dvd (by omega)
      (Nat.ordProj_dvd m p)) (pow_pos hp.pos v)).ne'⟩
    (heckeT_n_cusp k m f) z =
      (heckeT_n_cusp k (p ^ v) (heckeT_n_cusp k (m / p ^ v) f)) z := by
  have hp' := Nat.minFac_prime (show m ≠ 1 by omega)
  have hv_pos := hp'.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd m)
  haveI : NeZero (m.minFac ^ m.factorization m.minFac) := ⟨(pow_pos hp'.pos _).ne'⟩
  haveI : NeZero (m / m.minFac ^ m.factorization m.minFac) :=
    ⟨(Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd m m.minFac))
      (pow_pos hp'.pos _)).ne'⟩
  show (heckeT_n_aux k m f.toModularForm').toFun z =
    (heckeT_n_aux k _ (heckeT_n_aux k _ f.toModularForm')).toFun z
  rw [heckeT_n_aux, dif_neg (not_le.mpr hm), Module.End.mul_apply]
  conv_lhs => rw [show heckeT_ppow (N := N) k m.minFac hp' (m.factorization m.minFac) =
      heckeT_n_aux k (m.minFac ^ m.factorization m.minFac) from
    (heckeT_n_prime_pow k hp' _ hv_pos).symm]

@[simp]
theorem heckeT_n_cusp_toModularForm' (n : ℕ) [NeZero n]
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (heckeT_n_cusp k n f).toModularForm' = heckeT_n k n f.toModularForm' := by
  apply DFunLike.ext; intro τ; rfl

variable (N) in
/-- `heckeT_n` decomposes into prime-power * quotient, with explicit arguments. -/
theorem heckeT_n_mul_ppow_quot [NeZero N] (m : ℕ) [NeZero m] (hm : 1 < m)
    (p : ℕ) (hp : Nat.Prime p)
    (hmp : p = m.minFac) (v : ℕ) (hmv : v = m.factorization p)
    (hv_pos : 0 < v) (hdiv_pos : 0 < m / p ^ v) :
    haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
    haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
    heckeT_n (N := N) k m =
      heckeT_n (N := N) k (p ^ v) *
        heckeT_n (N := N) k (m / p ^ v) := by
  haveI : NeZero (p ^ v) := ⟨(pow_pos hp.pos v).ne'⟩
  haveI : NeZero (m / p ^ v) := ⟨hdiv_pos.ne'⟩
  subst hmp; subst hmv
  have h := heckeT_n_unfold (N := N) k m hm
  simp only [h]
  congr 1
  exact (heckeT_n_prime_pow k (Nat.minFac_prime (by omega : m ≠ 1)) _
    ((Nat.minFac_prime (by omega : m ≠ 1)).factorization_pos_of_dvd (by omega)
      (Nat.minFac_dvd m))).symm

/-- `heckeT_n_cusp` decomposes as composition at each point:
`(T_n f)(z) = (T_{n₁}(T_{n₂} f))(z)` when `heckeT_n k n = heckeT_n k n₁ * heckeT_n k n₂`
at the Module.End level. -/
theorem heckeT_n_cusp_mul_apply (n₁ n₂ : ℕ) [NeZero n₁] [NeZero n₂]
    (h_eq : haveI : NeZero (n₁ * n₂) := ⟨Nat.mul_pos (NeZero.pos n₁) (NeZero.pos n₂) |>.ne'⟩
            heckeT_n (N := N) k (n₁ * n₂) = heckeT_n k n₁ * heckeT_n k n₂)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (z : UpperHalfPlane) :
    haveI : NeZero (n₁ * n₂) := ⟨Nat.mul_pos (NeZero.pos n₁) (NeZero.pos n₂) |>.ne'⟩
    (heckeT_n_cusp k (n₁ * n₂) f) z =
      (heckeT_n_cusp k n₁ (heckeT_n_cusp k n₂ f)) z := by
  haveI : NeZero (n₁ * n₂) := ⟨Nat.mul_pos (NeZero.pos n₁) (NeZero.pos n₂) |>.ne'⟩
  show (heckeT_n k (n₁ * n₂) f.toModularForm').toFun z =
    (heckeT_n k n₁ (heckeT_n k n₂ f.toModularForm')).toFun z
  rw [h_eq]; rfl

/-! ### Double coset identity for the adjoint (DS Theorem 5.5.3, algebraic part)

For `p` coprime to `N`, choose `m, n ∈ ℤ` with `mp - nN = 1` (Bezout).
Then the matrix factorization `[p,0;0,1] = [1,n;N,mp]⁻¹ · [1,0;0,p] · [p,n;N,m]`
(where `[1,n;N,mp] ∈ Γ₁(N)` and `[p,n;N,m] ∈ Γ₀(N)` with `m ≡ p⁻¹ mod N`)
gives the double coset identity:

  `Γ₁(N) [p,0;0,1] Γ₁(N) = Γ₁(N) [1,0;0,p] Γ₁(N) · γ₀`

where `γ₀ = [p,n;N,m]` represents `⟨p⁻¹⟩`. This is the algebraic heart of
`T_p* = ⟨p⟩⁻¹ T_p`. -/

noncomputable def adjointGamma0Rep (p N : ℕ) (hpN : Nat.Coprime p N) :
    ↥(Gamma0 N) :=
  let m := Int.gcdA p N
  let n := -(Int.gcdB p N)
  ⟨⟨!![(p : ℤ), n; (N : ℤ), m], by
      have hbez := Int.gcd_eq_gcd_ab p N
      rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
      simp only [Matrix.det_fin_two_of]
      linarith⟩, by
      rw [Gamma0_mem]; simp⟩

lemma adjointGamma0Rep_units (p N : ℕ) (hpN : Nat.Coprime p N) [NeZero N] :
    Gamma0MapUnits (adjointGamma0Rep p N hpN) =
      (ZMod.unitOfCoprime p hpN)⁻¹ := by
  have hbez := Int.gcd_eq_gcd_ab p N
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
  have hmod : (Int.gcdA (↑p) (↑N) : ZMod N) * (p : ZMod N) = 1 := by
    have h := congr_arg (Int.cast : ℤ → ZMod N) hbez
    simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      ZMod.natCast_self, zero_mul, add_zero] at h
    rw [mul_comm] at h; exact h.symm
  rw [eq_comm, inv_eq_of_mul_eq_one_left]
  ext
  simp only [Units.val_mul, Units.val_one, Gamma0MapUnits_val, ZMod.coe_unitOfCoprime]
  unfold adjointGamma0Rep Gamma0Map
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  exact hmod

lemma coe_diamondOp_cusp_eq_slash_adjointGamma0Rep_inv
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) :
        UpperHalfPlane → ℂ) =
      ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ))⁻¹) :
          GL (Fin 2) ℝ) := by
  have h_units : Gamma0MapUnits ((adjointGamma0Rep p N hpN)⁻¹ : Gamma0 N) =
      ZMod.unitOfCoprime p hpN := by
    rw [map_inv, adjointGamma0Rep_units, inv_inv]
  show (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f : UpperHalfPlane → ℂ) = _
  rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)
    ((adjointGamma0Rep p N hpN)⁻¹ : Gamma0 N) h_units]
  rfl

private lemma coe_diamondOp_inv_cusp_eq_slash_adjointGamma0Rep
    (p : ℕ) (hp : Nat.Prime p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) :
        UpperHalfPlane → ℂ) =
      ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
          GL (Fin 2) ℝ) := by
  show (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ f :
      UpperHalfPlane → ℂ) = _
  rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
    (adjointGamma0Rep p N hpN) (adjointGamma0Rep_units p N hpN)]
  rfl

private lemma coe_diamondOp_inv_cusp_eq_slash_sigma_p_inv
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) :
        UpperHalfPlane → ℂ) =
      ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ) := by
  show (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹ f :
      UpperHalfPlane → ℂ) = _
  have h_units : Gamma0MapUnits
      (⟨sigma_p_specific N p hp hpN, sigma_p_specific_mem_Gamma0 N p hp hpN⟩ :
        Gamma0 N)⁻¹ = (ZMod.unitOfCoprime p hpN)⁻¹ := by
    rw [map_inv, Gamma0MapUnits_sigma_p_specific]
  rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)⁻¹
    (⟨sigma_p_specific N p hp hpN, sigma_p_specific_mem_Gamma0 N p hp hpN⟩ :
      Gamma0 N)⁻¹ h_units]
  rfl

lemma coe_diamondOp_cusp_eq_slash_sigma_p
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) :
        UpperHalfPlane → ℂ) =
      ⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ) := by
  show (diamondOpCusp k (ZMod.unitOfCoprime p hpN) f : UpperHalfPlane → ℂ) = _
  rw [diamondOpCusp_eq k (ZMod.unitOfCoprime p hpN)
    ⟨sigma_p_specific N p hp hpN, sigma_p_specific_mem_Gamma0 N p hp hpN⟩
    (Gamma0MapUnits_sigma_p_specific N p hp hpN)]
  rfl

lemma slash_sigma_p_diamond_inv_cusp_eq
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f) :
        UpperHalfPlane → ℂ) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN) : GL (Fin 2) ℝ) = ⇑f := by
  rw [← coe_diamondOp_cusp_eq_slash_sigma_p p hp hpN
    (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)]
  show ⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN)
      (diamondOp_cusp k (ZMod.unitOfCoprime p hpN)⁻¹ f)) = ⇑f
  show (((diamondOpCusp k (ZMod.unitOfCoprime p hpN)).comp
      (diamondOpCusp k (ZMod.unitOfCoprime p hpN)⁻¹) f) :
        UpperHalfPlane → ℂ) = ⇑f
  rw [← diamondOpCusp_mul, mul_inv_cancel, diamondOpCusp_one]
  rfl

private lemma slash_sigma_p_inv_diamond_cusp_eq
    (p : ℕ) (hp : 0 < p) (hpN : Nat.Coprime p N)
    (f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    (⇑(diamondOp_cusp k (ZMod.unitOfCoprime p hpN) f) :
        UpperHalfPlane → ℂ) ∣[k]
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ) = ⇑f := by
  rw [coe_diamondOp_cusp_eq_slash_sigma_p p hp hpN f]
  rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN)⁻¹ : GL (Fin 2) ℝ) =
      ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
        (sigma_p_specific N p hp hpN))⁻¹ by rw [map_inv]]
  rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]

noncomputable def adjointGamma1Rep (p N : ℕ) (hpN : Nat.Coprime p N) :
    SL(2, ℤ) :=
  let a := Int.gcdA p N
  let b := Int.gcdB p N
  ⟨!![(p : ℤ) * a, b; -(N : ℤ), 1], by
    have hbez := Int.gcd_eq_gcd_ab p N
    rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
    simp only [Matrix.det_fin_two_of]
    linarith⟩

lemma adjointGamma1Rep_mem_Gamma1 (p N : ℕ) [NeZero N]
    (hpN : Nat.Coprime p N) :
    adjointGamma1Rep p N hpN ∈ Gamma1 N := by
  rw [Gamma1_mem]
  have hbez := Int.gcd_eq_gcd_ab p N
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
  refine ⟨?_, ?_, ?_⟩
  ·
    show (((adjointGamma1Rep p N hpN).val 0 0 : ℤ) : ZMod N) = 1
    unfold adjointGamma1Rep
    have h : ((p : ℤ) * Int.gcdA p N + Int.gcdB p N * N : ZMod N) = 1 := by
      have := congr_arg (Int.cast : ℤ → ZMod N) hbez
      simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast] at this
      push_cast; linear_combination -this
    simpa [ZMod.natCast_self] using h
  ·
    show (((adjointGamma1Rep p N hpN).val 1 1 : ℤ) : ZMod N) = 1
    unfold adjointGamma1Rep; simp
  ·
    show (((adjointGamma1Rep p N hpN).val 1 0 : ℤ) : ZMod N) = 0
    unfold adjointGamma1Rep; simp

/-- `γ₀ · σ_p` has reduction `1` in its `(0,0)` entry mod `N`: a quick `Matrix.mul_apply`
expansion plus `aInvOfCoprime · p ≡ 1`. -/
private lemma adjointGamma0Rep_mul_sigma_p_entry_00
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (((((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val 0 0 : ℤ) : ZMod N) = 1 := by
  have h_mul : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val =
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val *
        (sigma_p_specific N p hp hpN).val := rfl
  rw [h_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h_γ₀_00 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 0 0 : ℤ)
      = (p : ℤ) := by simp [adjointGamma0Rep]
  have h_γ₀_01 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 0 1 : ℤ)
      = -(Int.gcdB p N) := by simp [adjointGamma0Rep]
  have h_σp_00 : ((sigma_p_specific N p hp hpN).val 0 0 : ℤ) =
      (aInvOfCoprime N p hpN : ℤ) := by simp [sigma_p_specific]
  have h_σp_10 : ((sigma_p_specific N p hp hpN).val 1 0 : ℤ) =
      (N : ℤ) * mIdxOfCoprime N p hpN := by simp [sigma_p_specific]
  rw [h_γ₀_00, h_γ₀_01, h_σp_00, h_σp_10]
  push_cast
  rw [show (-(Int.gcdB ↑p ↑N : ZMod N)) * ((N : ZMod N) * (mIdxOfCoprime N p hpN : ZMod N))
      = 0 by rw [ZMod.natCast_self]; ring]
  rw [add_zero, mul_comm]
  exact aInvOfCoprime_mul_eq_one N p hpN

/-- `γ₀ · σ_p` has reduction `1` in its `(1,1)` entry mod `N`: the `N`-column drops out and
Bézout gives `(gcdA p N) · p ≡ 1`. -/
private lemma adjointGamma0Rep_mul_sigma_p_entry_11
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (((((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val 1 1 : ℤ) : ZMod N) = 1 := by
  have h_mul : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val =
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val *
        (sigma_p_specific N p hp hpN).val := rfl
  rw [h_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h_γ₀_10 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 0 : ℤ)
      = (N : ℤ) := by simp [adjointGamma0Rep]
  have h_γ₀_11 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 1 : ℤ)
      = Int.gcdA p N := by simp [adjointGamma0Rep]
  have h_σp_01 : ((sigma_p_specific N p hp hpN).val 0 1 : ℤ) = 1 := by simp [sigma_p_specific]
  have h_σp_11 : ((sigma_p_specific N p hp hpN).val 1 1 : ℤ) = (p : ℤ) := by simp [sigma_p_specific]
  rw [h_γ₀_10, h_γ₀_11, h_σp_01, h_σp_11]
  push_cast
  rw [show (((N : ZMod N)) * 1) = 0 by rw [ZMod.natCast_self]; ring, zero_add]
  have hbez := Int.gcd_eq_gcd_ab p N
  rw [show (Int.gcd (↑p) (↑N) : ℤ) = 1 by exact_mod_cast hpN] at hbez
  have := congr_arg (Int.cast : ℤ → ZMod N) hbez
  simp only [Int.cast_one, Int.cast_add, Int.cast_mul, Int.cast_natCast,
    ZMod.natCast_self] at this
  linear_combination -this

/-- `γ₀ · σ_p` has reduction `0` in its `(1,0)` entry mod `N`: every term carries a factor of
`N`, so the entry vanishes mod `N`. -/
private lemma adjointGamma0Rep_mul_sigma_p_entry_10
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (((((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val 1 0 : ℤ) : ZMod N) = 0 := by
  have h_mul : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN).val =
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val *
        (sigma_p_specific N p hp hpN).val := rfl
  rw [h_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h_γ₀_10 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 0 : ℤ)
      = (N : ℤ) := by simp [adjointGamma0Rep]
  have h_γ₀_11 : (((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)).val 1 1 : ℤ)
      = Int.gcdA p N := by simp [adjointGamma0Rep]
  have h_σp_00 : ((sigma_p_specific N p hp hpN).val 0 0 : ℤ) =
      (aInvOfCoprime N p hpN : ℤ) := by simp [sigma_p_specific]
  have h_σp_10 : ((sigma_p_specific N p hp hpN).val 1 0 : ℤ) =
      (N : ℤ) * mIdxOfCoprime N p hpN := by simp [sigma_p_specific]
  rw [h_γ₀_10, h_γ₀_11, h_σp_00, h_σp_10]
  push_cast
  rw [show ((N : ZMod N)) * (aInvOfCoprime N p hpN : ZMod N) = 0 by
    rw [ZMod.natCast_self]; ring]
  rw [show ((Int.gcdA ↑p ↑N : ZMod N)) * ((N : ZMod N) * (mIdxOfCoprime N p hpN : ZMod N)) = 0 by
    rw [ZMod.natCast_self]; ring]
  ring

private lemma adjointGamma0Rep_mul_sigma_p_mem_Gamma1
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
      sigma_p_specific N p hp hpN ∈ Gamma1 N := by
  rw [Gamma1_mem]
  exact ⟨adjointGamma0Rep_mul_sigma_p_entry_00 p N hp hpN,
    adjointGamma0Rep_mul_sigma_p_entry_11 p N hp hpN,
    adjointGamma0Rep_mul_sigma_p_entry_10 p N hp hpN⟩

noncomputable def gamma1_of_gamma0_sigma_p
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ↥(Gamma1 N) :=
  ⟨((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
    sigma_p_specific N p hp hpN,
    adjointGamma0Rep_mul_sigma_p_mem_Gamma1 p N hp hpN⟩

private lemma gamma1_of_gamma0_sigma_p_coe
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ((gamma1_of_gamma0_sigma_p p N hp hpN : Gamma1 N) : SL(2, ℤ)) =
      ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) *
        sigma_p_specific N p hp hpN := rfl

lemma sigma_p_inv_eq_gamma1_inv_mul_gamma0
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    (sigma_p_specific N p hp hpN)⁻¹ =
      ((gamma1_of_gamma0_sigma_p p N hp hpN : Gamma1 N) : SL(2, ℤ))⁻¹ *
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) := by
  rw [gamma1_of_gamma0_sigma_p_coe, mul_inv_rev, inv_mul_cancel_right]

private lemma adjointGamma0Rep_mul_M_infty_eq_gamma1_mul_T_p_lower
    (p N : ℕ) [NeZero N] (hp : 0 < p) (hpN : Nat.Coprime p N) :
    ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ)
        ((adjointGamma0Rep p N hpN : Gamma0 N) : SL(2, ℤ)) :
        GL (Fin 2) ℚ) *
      (M_infty N p hp hpN : GL (Fin 2) ℚ) =
    ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ)
        ((gamma1_of_gamma0_sigma_p p N hp hpN : Gamma1 N) :
          SL(2, ℤ))) *
      (T_p_lower p hp : GL (Fin 2) ℚ) := by
  rw [show (M_infty N p hp hpN : GL (Fin 2) ℚ) =
      ((mapGL ℚ : SL(2, ℤ) →* GL (Fin 2) ℚ)
        (sigma_p_specific N p hp hpN)) *
        (T_p_lower p hp : GL (Fin 2) ℚ) from
    M_infty_eq_sigma_mul_T_p_lower N p hp hpN]
  rw [← mul_assoc, ← map_mul]
  rfl

/-! ### Hermitian adjoint of Hecke operators

The adjoint is defined via the Petersson inner product:
`⟨T f, g⟩ = ⟨f, T* g⟩` for all cusp forms f, g.

Diamond–Shurman Proposition 5.5.2 gives the key identity:
`⟨f|[α], g⟩ = ⟨f, g|[α']⟩` where `α' = det(α) · α⁻¹`.

For T_p, this yields T_p* = ⟨p⟩⁻¹ T_p (Theorem 5.5.3). -/

/-! ### DS Proposition 5.5.2: GL₂⁺ change of variables for Petersson

The key analytic lemma for the Hecke adjoint. For `α ∈ GL₂⁺(ℝ)`:

```
∫_{D} petersson k (f|α) g dμ = ∫_{α⁻¹•D} petersson k f (g|α') dμ
```
where `α' = det(α)·α⁻¹`, using `instSMulInvMeasure_GLpos` for the change of
variables and `petersson_slash` for the integrand transformation.

This is combined with the coset sum structure of `petN` and the algebraic
double coset identity to prove `T_p* = ⟨p⟩⁻¹ T_p` (DS Theorem 5.5.3). -/

section PeterssonAdjoint

open UpperHalfPlane MeasureTheory

-- Proof sketch for peterssonInner_slash_adjoint (DS Lemma 5.5.1 / Prop 5.5.2a):
-- 1. Insert `g = (g∣α)∣α⁻¹` to get both functions slashed by α:
--    `petersson k (f∣α) ((g∣α⁻¹)∣α) τ = |det α|^{k-2} · σ α · petersson k f (g∣α⁻¹) (α•τ)`.
-- 2. Change variables `τ → α⁻¹•τ` using `instSMulInvMeasure_GLpos`:
--    `∫_D h(τ) dμ = ∫_{α⁻¹•D} h(α•τ) dμ`.
-- 3. Simplify: the `|det α|^{k-2}` factor combines with `g∣α⁻¹` to give
--    `g∣(det(α)·α⁻¹) = g∣adjugate(α)` in the `petersson` integrand.

/-- The "Petersson adjoint" of a GL₂(ℝ) element: `α† = det(α) · α⁻¹ = adjugate(α)`.
As a 2x2 matrix, `adjugate [[a,b],[c,d]] = [[d,-b],[-c,a]]`.
Since `det(adjugate α) = det(α)^{n-1} ≠ 0`, the adjugate is in GL₂(ℝ). -/
noncomputable def peterssonAdj (α : GL (Fin 2) ℝ) : GL (Fin 2) ℝ :=
  .mkOfDetNeZero (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate (by
    rw [Matrix.det_adjugate]
    exact pow_ne_zero _ α.det_ne_zero)

-- API for `slash_peterssonAdj_eq`: key facts about adjugate in GL₂.

/-- `det(peterssonAdj α) = det(α)` for 2×2 matrices (since det(adjugate) = det^{n-1}). -/
lemma peterssonAdj_det (α : GL (Fin 2) ℝ) :
    (peterssonAdj α).det = α.det := by
  have hcoe : (peterssonAdj α : Matrix (Fin 2) (Fin 2) ℝ) =
      (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
    simp [peterssonAdj]
  ext
  show (peterssonAdj α : Matrix (Fin 2) (Fin 2) ℝ).det =
      (α : Matrix (Fin 2) (Fin 2) ℝ).det
  rw [hcoe, Matrix.det_adjugate, Fintype.card_fin]
  ring

/-- Coercion: `peterssonAdj α` as a matrix equals the adjugate of `α`. -/
lemma peterssonAdj_coe (α : GL (Fin 2) ℝ) :
    (peterssonAdj α : Matrix (Fin 2) (Fin 2) ℝ) =
      (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate := by
  simp [peterssonAdj]

lemma peterssonAdj_mul (α β : GL (Fin 2) ℝ) :
    peterssonAdj (α * β) = peterssonAdj β * peterssonAdj α := by
  apply Units.ext
  show (peterssonAdj (α * β) : Matrix (Fin 2) (Fin 2) ℝ) =
    (peterssonAdj β * peterssonAdj α : GL (Fin 2) ℝ).val
  rw [Units.val_mul, peterssonAdj_coe, peterssonAdj_coe, peterssonAdj_coe,
    Units.val_mul, Matrix.adjugate_mul_distrib]

private lemma Gamma1Quot_mk_mul_right_inv_eq
    (q γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N) :
    (⟦q * γ⁻¹⟧ : SL(2, ℤ) ⧸ Gamma1 N) = (⟦q⟧ : SL(2, ℤ) ⧸ Gamma1 N) := by
  rw [QuotientGroup.eq]
  show (q * γ⁻¹)⁻¹ * q ∈ Gamma1 N
  rw [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one]
  exact hγ

private lemma sum_Gamma1Quot_mul_right_inv_eq
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N)
    (F : SL(2, ℤ) ⧸ Gamma1 N → ℂ) :
    (∑ q : SL(2, ℤ) ⧸ Gamma1 N,
        F (⟦(q.out : SL(2, ℤ)) * γ⁻¹⟧)) =
      ∑ q : SL(2, ℤ) ⧸ Gamma1 N, F q := by
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [Gamma1Quot_mk_mul_right_inv_eq _ γ hγ]
  exact congrArg F (Quotient.out_eq q)

/-- **Double-adjoint identity**: `peterssonAdj (peterssonAdj α) = α` for
any `α : GL (Fin 2) ℝ`.  Follows from `Matrix.adjugate_adjugate` at
`Fintype.card (Fin 2) = 2`, where `(det α)^(2 - 2) • α = α`. -/
lemma peterssonAdj_peterssonAdj (α : GL (Fin 2) ℝ) :
    peterssonAdj (peterssonAdj α) = α := by
  apply Units.ext
  ext i j
  have hαcoe := peterssonAdj_coe α
  change ((peterssonAdj α : Matrix (Fin 2) (Fin 2) ℝ).adjugate) i j =
      (α : Matrix (Fin 2) (Fin 2) ℝ) i j
  rw [hαcoe, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.of_apply]

/-- For an SL(2, ℤ) element cast to GL(2, ℝ), the `peterssonAdj` equals the group inverse.
Since SL elements have determinant 1, their adjugate equals their inverse. -/
lemma peterssonAdj_mapGL_SL_eq_inv (q : SL(2, ℤ)) :
    peterssonAdj ((mapGL ℝ q : GL (Fin 2) ℝ)) = (mapGL ℝ q : GL (Fin 2) ℝ)⁻¹ := by
  apply Units.ext
  rw [peterssonAdj_coe, Matrix.coe_units_inv]
  have hdet : (mapGL ℝ q : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    have : (mapGL ℝ q : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix q.val) := by
      ext i j; simp [mapGL_coe_matrix, Int.castRingHom]
    rw [this, ← RingHom.map_det, q.property]
    simp
  rw [Matrix.inv_def, Ring.inverse_eq_inv', hdet]
  simp

lemma peterssonAdj_inv_mapGL_SL_eq_self (q : SL(2, ℤ)) :
    (peterssonAdj ((mapGL ℝ q : GL (Fin 2) ℝ)))⁻¹ = (mapGL ℝ q : GL (Fin 2) ℝ) := by
  rw [peterssonAdj_mapGL_SL_eq_inv, inv_inv]

private lemma GL_inv_entry (α : GL (Fin 2) ℝ) (i j : Fin 2) :
    (α⁻¹ : GL (Fin 2) ℝ) i j =
      (α.det.val)⁻¹ * (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j := by
  set A := (α : Matrix (Fin 2) (Fin 2) ℝ)
  have hdet : A.det ≠ 0 := α.det_ne_zero
  have hcoe : (↑α⁻¹ : Matrix (Fin 2) (Fin 2) ℝ) = A⁻¹ := Matrix.coe_units_inv α
  have hinv : A⁻¹ = A.det⁻¹ • A.adjugate := by
    rw [Matrix.inv_def]
    congr 1
    exact Ring.inverse_eq_inv _
  have hdet_eq : A.det = α.det.val := rfl
  show (↑α⁻¹ : Matrix _ _ ℝ) i j = _
  rw [hcoe, hinv, Matrix.smul_apply, smul_eq_mul, hdet_eq]

lemma peterssonAdj_smul_eq (α : GL (Fin 2) ℝ) (τ : ℍ) :
    (peterssonAdj α) • τ = α⁻¹ • τ := by
  have hdet_ne : (α.det.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Units.ne_zero α.det)
  have hadj_entry : ∀ i j, (peterssonAdj α : Matrix _ _ ℝ) i j =
      (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j := by
    intro i j; simp [peterssonAdj]
  have hdet_ne' : α.det.val ≠ 0 := Units.ne_zero α.det
  have hnum : num (peterssonAdj α) (τ : ℂ) = ↑α.det.val * num α⁻¹ (τ : ℂ) := by
    simp only [num, hadj_entry, GL_inv_entry]
    push_cast; field_simp
  have hdenom : denom (peterssonAdj α) (τ : ℂ) = ↑α.det.val * denom α⁻¹ (τ : ℂ) := by
    simp only [denom, hadj_entry, GL_inv_entry]
    push_cast; field_simp
  have hσ_eq : σ (peterssonAdj α) = σ α⁻¹ := by
    have hdet1 : (peterssonAdj α).det.val = α.det.val :=
      congr_arg Units.val (peterssonAdj_det α)
    have hdet2 : (α⁻¹).det.val = (α.det.val)⁻¹ := by
      show (α⁻¹).det.val = _
      rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α]
      exact Units.val_inv_eq_inv_val _
    simp only [σ, hdet1, hdet2, inv_pos]
  ext1
  simp only [coe_smul, hσ_eq]
  congr 1
  rw [hnum, hdenom, mul_div_mul_left _ _ hdet_ne]

private lemma peterssonAdj_denom (α : GL (Fin 2) ℝ) (τ : ℍ) :
    UpperHalfPlane.denom (peterssonAdj α) τ =
      ↑(α.det.val) * UpperHalfPlane.denom α⁻¹ τ := by
  have hadj_entry : ∀ i j, (peterssonAdj α : Matrix _ _ ℝ) i j =
      (α : Matrix (Fin 2) (Fin 2) ℝ).adjugate i j := by
    intro i j; simp [peterssonAdj]
  simp only [denom, hadj_entry, GL_inv_entry]
  push_cast
  have hdet_ne : (α.det.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Units.ne_zero α.det)
  field_simp

/-- Pointwise: `g ∣[k] peterssonAdj α = |det α|^{k-2} • (g ∣[k] α⁻¹)`.

Proof: By `ext τ; simp [slash_apply]`, both sides evaluate to
`g(α⁻¹•τ) * (det-power) * (denom)^{-k}`. Using `peterssonAdj_smul_eq` (same Möbius
action), `peterssonAdj_det` (same det), and `peterssonAdj_denom` (denom scales by det),
the det powers `|det|^{k-1} · det^{-k}` on the LHS vs `|det|^{k-2} · |det⁻¹|^{k-1}`
on the RHS both equal `det^{-1}`, so the ratio is `|det|^{k-2}`. -/
lemma slash_peterssonAdj_eq (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (g : ℍ → ℂ) :
    g ∣[k] peterssonAdj α = (↑(|α.det.val| ^ (k - 2)) : ℂ) • (g ∣[k] α⁻¹) := by
  have habs : |α.det.val| = α.det.val := abs_of_pos hα
  have hdet_ne : (α.det.val : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hα)
  have hdet_eq : (peterssonAdj α).det.val = α.det.val :=
    congr_arg Units.val (peterssonAdj_det α)
  have hσ_adj : σ (peterssonAdj α) = σ α⁻¹ := by
    simp only [σ, hdet_eq]
    simp [inv_pos]
  have hdet_inv_abs : |(α⁻¹).det.val| = (α.det.val)⁻¹ := by
    rw [show (α⁻¹).det = α.det⁻¹ from map_inv (Matrix.GeneralLinearGroup.det) α,
      Units.val_inv_eq_inv_val, abs_inv, habs]
  ext τ
  have hD := denom_ne_zero α⁻¹ τ
  simp only [ModularForm.slash_apply, Pi.smul_apply, smul_eq_mul, peterssonAdj_smul_eq,
    hσ_adj, hdet_eq, peterssonAdj_denom, mul_zpow, hdet_inv_abs, habs]
  set d := α.det.val with hd_def
  rw [show (↑(d ^ (k - 2)) : ℂ) = (↑d : ℂ) ^ (k - 2) by push_cast; rfl]
  rw [show (↑(d⁻¹) : ℂ) = (↑d : ℂ)⁻¹ from Complex.ofReal_inv d]
  have hcd : (↑d : ℂ) ≠ 0 := hdet_ne
  set G := σ α⁻¹ (g (α⁻¹ • τ)) with hG_def
  set D := denom α⁻¹ (↑τ) with hD_def
  suffices h : G * (↑d : ℂ) ^ (k - 1) * ((↑d : ℂ) ^ (-k) * D ^ (-k)) =
      (↑d : ℂ) ^ (k - 2) * (G * (↑d : ℂ)⁻¹ ^ (k - 1) * D ^ (-k)) by exact h
  rw [inv_zpow']
  have h1 : (k - 1 : ℤ) + (-k) = -1 := by omega
  have h2 : (k - 2 : ℤ) + (-(k - 1)) = -1 := by omega
  calc G * (↑d : ℂ) ^ (k - 1) * ((↑d : ℂ) ^ (-k) * D ^ (-k))
      = G * ((↑d : ℂ) ^ (k - 1) * (↑d : ℂ) ^ (-k)) * D ^ (-k) := by ring
    _ = G * (↑d : ℂ) ^ (-1 : ℤ) * D ^ (-k) := by rw [← zpow_add₀ hcd, h1]
    _ = G * ((↑d : ℂ) ^ (k - 2) * (↑d : ℂ) ^ (-(k - 1))) * D ^ (-k) := by
          rw [← zpow_add₀ hcd, h2]
    _ = (↑d : ℂ) ^ (k - 2) * (G * (↑d : ℂ) ^ (-(k - 1)) * D ^ (-k)) := by ring

/-- **GL₂⁺ Petersson adjoint** (DS Proposition 5.5.2a):
For `α ∈ GL(2,ℝ)` with `det(α) > 0`, and any measurable set `D ⊆ ℍ`:
```
peterssonInner k D (f∣[k]α) g = peterssonInner k (α • D) f (g∣[k] adjugate(α))
``` -/
theorem peterssonInner_slash_adjoint
    (D : Set ℍ) (α : GL (Fin 2) ℝ) (hα : 0 < α.det.val)
    (f g : ℍ → ℂ) :
    peterssonInner k D (f ∣[k] α) g =
      peterssonInner k (α • D) f (g ∣[k] peterssonAdj α) := by
  have hg_decomp : g = (g ∣[k] α⁻¹) ∣[k] α := by
    rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
  simp only [peterssonInner]
  set g' := g ∣[k] α⁻¹
  have h_eq : ∀ τ, petersson k (f ∣[k] α) g τ =
      ↑|α.det.val| ^ (k - 2) * petersson k f g' (α • τ) := by
    intro τ
    have : g = g' ∣[k] α := hg_decomp
    rw [this, petersson_slash, show σ α = RingHom.id ℂ from if_pos hα, RingHom.id_apply]
  simp_rw [h_eq]
  symm
  have hpet_adj : ∀ τ, petersson k f (g ∣[k] peterssonAdj α) τ =
      ↑|α.det.val| ^ (k - 2) * petersson k f g' τ := by
    intro τ
    rw [slash_peterssonAdj_eq α hα g]
    simp [petersson, Pi.smul_apply, smul_eq_mul]; ring
  simp_rw [hpet_adj]
  set α' : GL(2, ℝ)⁺ := ⟨α, hα⟩
  rw [show α • D = (fun τ ↦ α' • τ) '' D by rw [Set.image_smul]; rfl]
  exact (measurePreserving_smul α' μ_hyp).setIntegral_image_emb
    (measurableEmbedding_const_smul α') _ D

/-- **Hecke-representative wrapper around `peterssonInner_slash_adjoint`**
(Step 1 of the T205-d-SYMM chain, per expert review 2026-05-11). -/
theorem peterssonInner_slash_adjoint_for_heckeRep
    (D : Set ℍ) (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k D ((⇑f : ℍ → ℂ) ∣[k] β) ⇑g =
      peterssonInner k (β • D) ⇑f ((⇑g : ℍ → ℂ) ∣[k] peterssonAdj β) :=
  peterssonInner_slash_adjoint D β hβ ⇑f ⇑g

/-- **Per-`q`-coset Hecke-rep wrapper** (companion to
`peterssonInner_slash_adjoint_for_heckeRep`, Step 1 of T205-d-SYMM chain). -/
theorem peterssonInner_slash_adjoint_for_heckeRep_per_q
    (q : SL(2, ℤ) ⧸ Gamma1 N) (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k fd
        (((⇑f : ℍ → ℂ) ∣[k] β) ∣[k] ((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)))
        (⇑g ∣[k] ((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ))) =
      peterssonInner k
        (β • (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) • (fd : Set ℍ)))
        ⇑f
        ((⇑g : ℍ → ℂ) ∣[k] peterssonAdj β) := by
  rw [← peterssonInner_smul_set_eq_slash ((q.out : SL(2, ℤ))⁻¹) fd
        ((⇑f : ℍ → ℂ) ∣[k] β) ⇑g]
  exact peterssonInner_slash_adjoint_for_heckeRep _ β hβ f g

/-- **LHS-distributed-summand → tile-form bridge** (consumer of
`peterssonInner_slash_adjoint_for_heckeRep_per_q`, immediate use by
T205-d-ADJ-CORR). -/
theorem peterssonInner_LHS_distributed_summand_to_tile_form
    (q : SL(2, ℤ) ⧸ Gamma1 N) (β : GL (Fin 2) ℝ) (hβ : 0 < β.det.val)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k fd
        ((⇑f : ℍ → ℂ) ∣[k] (β * ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)))
        (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ)
          (q.out : SL(2, ℤ))⁻¹ : GL (Fin 2) ℝ)) =
      peterssonInner k
        (β • (((q.out : SL(2, ℤ))⁻¹ : SL(2, ℤ)) • (fd : Set ℍ)))
        ⇑f
        ((⇑g : ℍ → ℂ) ∣[k] peterssonAdj β) := by
  rw [SlashAction.slash_mul k β
        ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) (q.out : SL(2, ℤ))⁻¹ :
          GL (Fin 2) ℝ) (⇑f : ℍ → ℂ)]
  exact peterssonInner_slash_adjoint_for_heckeRep_per_q q β hβ f g

private lemma peterssonInner_mapGL_smul_eq_of_slash_invariant
    (D : Set ℍ) (γ : SL(2, ℤ)) (F G : ℍ → ℂ)
    (hF : F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) = F)
    (hG : G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) = G) :
    peterssonInner k
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) • D) F G =
      peterssonInner k D F G := by
  have hα : 0 <
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)).det.val := by
    show 0 < (((mapGL ℝ γ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix γ.val) by rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, γ.property]
    norm_num
  have h := peterssonInner_slash_adjoint (k := k) D
    (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)) hα F
    (G ∣[k] (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)))
  rw [peterssonAdj_mapGL_SL_eq_inv γ] at h
  rw [show ((G ∣[k] (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)))
          ∣[k] (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ))⁻¹) =
        G by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]] at h
  rw [hF, hG] at h
  exact h.symm

private lemma peterssonInner_mapGL_smul_eq_of_Gamma1
    (D : Set ℍ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 N)
    (f g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :
    peterssonInner k
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) • D)
        ⇑f ⇑g =
      peterssonInner k D ⇑f ⇑g := by
  have hf : (⇑f ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ :
      GL (Fin 2) ℝ)) = ⇑f := by
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) =
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl, ← ModularForm.SL_slash]
    exact slash_Gamma1_eq f γ hγ
  have hg : (⇑g ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ :
      GL (Fin 2) ℝ)) = ⇑g := by
    rw [show ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) =
          ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) from rfl, ← ModularForm.SL_slash]
    exact slash_Gamma1_eq g γ hγ
  exact peterssonInner_mapGL_smul_eq_of_slash_invariant D γ ⇑f ⇑g hf hg

lemma peterssonInner_mapGL_smul_eq_slash
    (D : Set ℍ) (γ : SL(2, ℤ)) (F G : ℍ → ℂ) :
    peterssonInner k
        (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ) • D) F G =
      peterssonInner k D
        (F ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ))
        (G ∣[k] ((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)) := by
  have hα : 0 <
      (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)).det.val := by
    show 0 < (((mapGL ℝ γ : GL (Fin 2) ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).det
    rw [show ((mapGL ℝ γ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        ((Int.castRingHom ℝ).mapMatrix γ.val) by rw [mapGL_coe_matrix]; rfl]
    rw [← RingHom.map_det, γ.property]
    norm_num
  have h := peterssonInner_slash_adjoint (k := k) D
    (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)) hα F
    (G ∣[k] (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)))
  rw [peterssonAdj_mapGL_SL_eq_inv γ] at h
  rw [show ((G ∣[k] (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ)))
          ∣[k] (((mapGL ℝ : SL(2, ℤ) →* GL (Fin 2) ℝ) γ : GL (Fin 2) ℝ))⁻¹) =
        G by
      rw [← SlashAction.slash_mul, mul_inv_cancel, SlashAction.slash_one]] at h
  exact h.symm

end PeterssonAdjoint

end HeckeRing.GL2
